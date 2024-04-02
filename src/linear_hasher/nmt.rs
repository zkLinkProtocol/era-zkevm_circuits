use super::hash::*;
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
        &self,
        cs: &mut CS,
    ) -> [UInt8<F>; NMT_ROOT_SIZE] {
        self.compute_root(cs, 0, self.leaves.len())
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

        match end - start {
            0 => empty_root(cs),
            1 => hash_leaf(cs, &self.leaves[start]),
            _ => {
                let k = get_split_point(end - start);
                let left = self.compute_root(cs, start, start + k);
                let right = self.compute_root(cs, start + k, end);
                hash_node(cs, &left, &right)
            }
        }
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
