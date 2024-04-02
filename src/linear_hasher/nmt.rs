use boojum::gadgets::traits::selectable::Selectable;
use boojum::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{
        boolean::Boolean, sha256::SHA256_DIGEST_SIZE, traits::allocatable::CSAllocatable, u8::UInt8,
    },
};
use itertools::Itertools;

use super::params::NMT_ROOT_SIZE;
use crate::recursion::leaf_layer::leaf_layer_recursion_entry_point;
// use crate::linear_hasher::DATA_ARRAY_LEN;
use crate::utils::is_equal_queue_state;

/// Implementation of Namespace Merkle Tree in circuit.
#[derive(Debug, Clone, Default)]
pub struct Nmt<F: SmallField> {
    pub leaves: Vec<Vec<UInt8<F>>>,
    pub min_namespace_id: Vec<UInt8<F>>,
    pub max_namespace_id: Vec<UInt8<F>>,
}

impl<F: SmallField> Nmt<F> {
    pub fn new() -> Self {
        Self {
            leaves: vec![],
            min_namespace_id: vec![],
            max_namespace_id: vec![],
        }
    }

    pub fn push_from_witness<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        namespace_id: &[u8],
        data: &[u8],
    ) {
        let namespace_id = namespace_id
            .iter()
            .map(|b| UInt8::allocate(cs, *b))
            .collect::<Vec<_>>();
        let data = data
            .iter()
            .map(|b| UInt8::allocate(cs, *b))
            .collect::<Vec<_>>();
        self.push(cs, &namespace_id, &data)
    }

    pub fn push<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        namespace_id: &[UInt8<F>],
        data: &[UInt8<F>],
    ) {
        let mut leaf = vec![];
        leaf.extend(namespace_id);
        leaf.extend(data);
        self.leaves.push(leaf);

        if self.min_namespace_id.is_empty()
            || namespace_id_less(cs, namespace_id, &self.min_namespace_id)
        {
            self.min_namespace_id = namespace_id.try_into().unwrap();
        }
        if self.max_namespace_id.is_empty()
            || namespace_id_less(cs, &self.max_namespace_id, namespace_id)
        {
            self.max_namespace_id = namespace_id.try_into().unwrap();
        }
    }

    pub fn root<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> [UInt8<F>; NMT_ROOT_SIZE] {
        self.compute_root(cs, 0, self.leaves.len())
    }

    pub fn compute_root<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        start: usize,
        end: usize,
    ) -> [UInt8<F>; NMT_ROOT_SIZE] {
        assert!(start <= end);
        use hasher::*;

        match end - start {
            0 => empty_root(cs),
            1 => hash_leaf(cs, &self.leaves[start]),
            _ => {
                let k = Self::get_split_point(end - start);
                let left = self.compute_root(cs, start, start + k);
                let right = self.compute_root(cs, start + k, end);
                hash_node(cs, &left, &right)
            }
        }
    }

    fn get_split_point(len: usize) -> usize {
        let bitlen = if len == 0 {
            0
        } else {
            32 - (len as u32).leading_zeros()
        };
        let mut k = 1 << (bitlen - 1);
        if k == len {
            k >>= 1
        }
        k
    }
}

fn namespace_id_less<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &[UInt8<F>],
    b: &[UInt8<F>],
) -> bool {
    assert_eq!(a.len(), b.len());
    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);

    let mut iter = a.iter().zip(b.iter()).skip_while(|(a, b)| {
        let (diff, borrow) = a.overflowing_sub(cs, b);
        // Equal
        diff.is_zero(cs) == boolean_true && borrow == boolean_false
    });

    match iter.next() {
        Some((a, b)) => {
            let (_, borrow) = a.overflowing_sub(cs, b);
            borrow == boolean_true
        }
        None => false,
    }
}

mod hasher {
    use boojum::{
        cs::traits::cs::ConstraintSystem,
        field::SmallField,
        gadgets::{
            boolean::Boolean, sha256::SHA256_DIGEST_SIZE, traits::selectable::Selectable, u8::UInt8,
        },
    };

    use crate::linear_hasher::params::{NAMESPACE_LEN, NMT_ROOT_SIZE};

    pub fn sha256<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input: &[UInt8<F>],
    ) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
        boojum::gadgets::sha256::sha256(cs, input)
    }

    pub fn empty_root<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
    ) -> [UInt8<F>; NMT_ROOT_SIZE] {
        let empty_namespace = vec![UInt8::zero(cs); NAMESPACE_LEN];
        let hash = sha256(cs, &empty_namespace);
        let mut root = vec![];
        root.extend(&empty_namespace);
        root.extend(&empty_namespace);
        root.extend(hash);
        root.try_into().unwrap()
    }

    const LEAF_PREFIX: u8 = 0;
    const NODE_PREFIX: u8 = 1;
    pub fn hash_leaf<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        node: &[UInt8<F>],
    ) -> [UInt8<F>; NMT_ROOT_SIZE] {
        let hash = {
            let mut data = vec![];
            data.push(UInt8::allocated_constant(cs, LEAF_PREFIX));
            data.extend(node);
            sha256(cs, &data)
        };
        let namespace_id = &node[..NAMESPACE_LEN];
        let mut res = vec![];
        res.extend(namespace_id);
        res.extend(namespace_id);
        res.extend(hash);
        res.try_into().unwrap()
    }
    pub fn hash_node<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        left: &[UInt8<F>],
        right: &[UInt8<F>],
    ) -> [UInt8<F>; NMT_ROOT_SIZE] {
        fn get_namespace<F: SmallField>(
            root: &[UInt8<F>],
        ) -> ([UInt8<F>; NAMESPACE_LEN], [UInt8<F>; NAMESPACE_LEN]) {
            (
                root[..NAMESPACE_LEN].try_into().unwrap(),
                root[NAMESPACE_LEN..NAMESPACE_LEN * 2].try_into().unwrap(),
            )
        }
        let (left_min_namespace, left_max_namespace) = get_namespace(left);
        let (right_min_namespace, right_max_namespace) = get_namespace(right);

        // Here ignore_max_namespace is true
        let is_equal_precomputed_max_namespace = {
            let precomputed_max_namespace =
                vec![UInt8::allocated_constant(cs, 0xff); NAMESPACE_LEN];
            assert_eq!(right_max_namespace.len(), precomputed_max_namespace.len());
            let mut is_equal = Boolean::allocated_constant(cs, true);
            precomputed_max_namespace
                .iter()
                .zip(right_min_namespace.iter())
                .for_each(|(a, b)| {
                    let a_b_equal = UInt8::equals(cs, a, b);
                    is_equal = is_equal.and(cs, a_b_equal);
                });
            is_equal
        };

        let max_namespace = Selectable::<F>::conditionally_select(
            cs,
            is_equal_precomputed_max_namespace,
            &left_max_namespace,
            &right_max_namespace,
        );
        let min_namespace = left_min_namespace;

        let hash = {
            let mut data = vec![];
            data.push(UInt8::allocated_constant(cs, NODE_PREFIX));
            data.extend(left);
            data.extend(right);
            sha256(cs, &data)
        };

        let mut res = vec![];
        res.extend(min_namespace);
        res.extend(max_namespace);
        res.extend(hash);
        res.try_into().unwrap()
    }
}

#[cfg(test)]
pub mod tests {
    use crate::linear_hasher::params::NAMESPACE_ID_LEN;
    use crate::linear_hasher::params::NAMESPACE_LEN;

    use super::Nmt;

    use std::alloc::Global;

    use boojum::algebraic_props::poseidon2_parameters::*;
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder::*;
    use boojum::cs::gates::*;
    use boojum::cs::implementations::reference_cs::CSReferenceImplementation;
    use boojum::cs::traits::gate::*;
    use boojum::cs::*;
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::tables::*;
    use boojum::gadgets::traits::witnessable::CSWitnessable;
    use boojum::implementations::poseidon2::Poseidon2Goldilocks;
    use boojum::sha3::digest::typenum::SquareRoot;
    use boojum::worker::Worker;
    use zkevm_opcode_defs::PrecompileCallABI;

    use super::*;

    type F = GoldilocksField;
    type P = GoldilocksField;
    type R = Poseidon2Goldilocks;

    pub fn create_test_cs() -> CSReferenceImplementation<
        GoldilocksField,
        GoldilocksField,
        DevCSConfig,
        impl GateConfigurationHolder<GoldilocksField>,
        impl StaticToolboxHolder,
    > {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 4,
                    num_repetitions: 5,
                    share_table_id: true,
                },
            );

            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            let builder = UIntXAddGate::<8>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
                false,
            );

            let builder = SelectionGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, 1 << 20);

        use boojum::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);
        let builder = configure(builder);
        let mut owned_cs = builder.build(1 << 20);

        // add tables for keccak
        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

        let table = create_ch4_table();
        owned_cs.add_lookup_table::<Ch4Table, 4>(table);

        let table = create_maj4_table();
        owned_cs.add_lookup_table::<Maj4Table, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 1>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<1>, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 2>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<2>, 4>(table);

        owned_cs
    }

    #[test]
    fn test_root() {
        let cs = &mut create_test_cs();
        let mut nmt = Nmt::new();
        nmt.push_from_witness(cs, &[0x00; NAMESPACE_LEN], "leaf_0".as_bytes());
        nmt.push_from_witness(cs, &[0x00; NAMESPACE_LEN], "leaf_1".as_bytes());
        nmt.push_from_witness(cs, &[0x01; NAMESPACE_LEN], "leaf_2".as_bytes());
        nmt.push_from_witness(cs, &[0x01; NAMESPACE_LEN], "leaf_3".as_bytes());

        let root = nmt.root(cs);
        let root = root
            .iter()
            .map(|b| b.get_witness(cs).wait().unwrap())
            .collect::<Vec<_>>();
        let expected_root = hex::decode("000000000000000000000000000000000000000000000000000000000001010101010101010101010101010101010101010101010101010101018cdbbadd52d68c58a7dd9cdd980af24a63f147814d5c5a16faaba077d37fd83d").unwrap();
        assert_eq!(root, expected_root);
    }
}
