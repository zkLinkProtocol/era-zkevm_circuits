use boojum::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{
        boolean::Boolean, sha256::SHA256_DIGEST_SIZE, traits::selectable::Selectable, u8::UInt8,
    },
};

use super::params::{NAMESPACE_LEN, NMT_ROOT_SIZE};

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
const INNER_PREFIX: u8 = 1;
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

    let ignore_max_namespace = true;
    let is_equal_precomputed_max_namespace = {
        let precomputed_max_namespace = vec![UInt8::allocated_constant(cs, 0xff); NAMESPACE_LEN];
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

pub fn get_split_point(len: usize) -> usize {
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
