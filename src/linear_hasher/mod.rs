use std::collections::VecDeque;
use std::mem::MaybeUninit;

use crate::base_structures::log_query::LogQuery;
use crate::base_structures::state_diff_record::StateDiffRecord;
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::keccak256_round_function::keccak256_absorb_and_run_permutation;
use crate::linear_hasher::mmr::create_celestis_commitment;
use crate::linear_hasher::params::{
    DATA_ARRAY_COUNT, DATA_BYTES_LEN, NAMESPACE_ID, NAMESPACE_VERSION, SHARE_VERSION,
};
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::config::*;
use boojum::cs::traits::cs::{ConstraintSystem, DstBuffer};
use boojum::cs::{Place, Variable};
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::keccak256;
use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::{CSAllocatable, CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::castable::WitnessCastable;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use std::sync::{Arc, RwLock};
use zkevm_opcode_defs::system_params::STORAGE_AUX_BYTE;

use super::*;

pub mod input;
mod mmr;
mod nmt;
pub mod params;
use self::input::*;

pub fn linear_hasher_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: LinearHasherCircuitInstanceWitness<F>,
    round_function: &R,
    params: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    let limit = params;

    assert!(limit <= u32::MAX as usize);

    let LinearHasherCircuitInstanceWitness {
        closed_form_input,
        queue_witness,
    } = witness;

    let mut structured_input =
        LinearHasherInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());
    let start_flag = structured_input.start_flag;

    let boolean_true = Boolean::allocated_constant(cs, true);

    // only 1 instance of the circuit here for now
    Boolean::enforce_equal(cs, &start_flag, &boolean_true);

    let queue_state_from_input = structured_input.observable_input.queue_state;

    // it must be trivial
    queue_state_from_input.enforce_trivial_head(cs);

    let mut queue = StorageLogQueue::<F, R>::from_state(cs, queue_state_from_input);
    let queue_witness = CircuitQueueWitness::from_inner_witness(queue_witness);
    queue.witness = Arc::new(queue_witness);

    use crate::base_structures::log_query::L2_TO_L1_MESSAGE_BYTE_LENGTH;
    // we do not serialize length because it's recalculatable in L1

    let empty_hash = {
        use zkevm_opcode_defs::sha3::*;

        let mut result = [0u8; 32];
        let digest = Keccak256::digest(&[]);
        result.copy_from_slice(digest.as_slice());

        result.map(|el| UInt8::allocated_constant(cs, el))
    };

    let mut buffer = vec![];

    let done = queue.is_empty(cs);
    let no_work = done;

    use crate::storage_application::keccak256_conditionally_absorb_and_run_permutation;
    use boojum::gadgets::keccak256::KECCAK_RATE_BYTES;

    for _cycle in 0..limit {
        let queue_is_empty = queue.is_empty(cs);
        let should_pop = queue_is_empty.negated(cs);

        let (storage_log, _) = queue.pop_front(cs, should_pop);

        use crate::base_structures::ByteSerializable;
        let as_bytes = storage_log.into_bytes(cs);

        buffer.extend(as_bytes);
    }

    let completed = queue.is_empty(cs);

    Boolean::enforce_equal(cs, &completed, &boolean_true);

    structured_input.completion_flag = completed.clone();

    let fsm_output = ();
    structured_input.hidden_fsm_output = fsm_output;

    // Padding data
    assert_eq!(buffer.len(), DATA_BYTES_LEN);

    let share_version = UInt8::allocated_constant(cs, SHARE_VERSION);
    let namespace_id = NAMESPACE_ID
        .iter()
        .map(|b| UInt8::allocate(cs, *b))
        .collect::<Vec<_>>();
    let namespace_version = UInt8::allocated_constant(cs, NAMESPACE_VERSION);

    let keccak256_hash =
        create_celestis_commitment(cs, namespace_version, &namespace_id, buffer, share_version);

    let keccak256_hash =
        <[UInt8<F>; 32]>::conditionally_select(cs, no_work, &empty_hash, &keccak256_hash);

    let mut observable_output = LinearHasherOutputData::placeholder(cs);
    observable_output.keccak256_hash = keccak256_hash;
    structured_input.observable_output = observable_output;

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    use crate::fsm_input_output::commit_variable_length_encodable_item;
    use crate::fsm_input_output::ClosedFormInputCompactForm;
    use boojum::cs::gates::PublicInputGate;

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);
    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}
