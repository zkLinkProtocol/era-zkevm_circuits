use boojum::gadgets::sha256::SHA256_DIGEST_SIZE;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::{cs::traits::cs::ConstraintSystem, field::SmallField, gadgets::u8::UInt8};

use crate::linear_hasher::params::NS_SIZE;

use super::nmt::Nmt;
use super::params::{NMT_ROOT_SIZE, SHARE_BYTE_LEN};

pub fn create_celestis_commitment<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    namespace_version: u8,
    namespace_id: &[u8],
    data: Vec<UInt8<F>>,
    share_version: u8,
) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
    let shares = create_celestis_shares(cs, namespace_version, namespace_id, data, share_version);
    compute_mmr_root(cs, shares)
}

fn create_celestis_shares<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    namespace_version: u8,
    namespace_id: &[u8],
    mut data: Vec<UInt8<F>>,
    share_version: u8,
) -> Vec<[UInt8<F>; SHARE_BYTE_LEN]> {
    // assert_eq!(namespace_id.len(), NAMESPACE_ID_LEN);
    // assert_eq!(data.len(), DATA_BYTES_LEN);

    let mut normalized_data = vec![];
    // TODO:
    normalized_data.extend(
        (data.len() as u32)
            .to_be_bytes()
            .iter()
            .map(|b| UInt8::allocate(cs, *b))
            .collect::<Vec<_>>(),
    );
    normalized_data.append(&mut data);

    let mut shares = vec![];
    let data_size = 512 - 1 - 28 - 1;
    for (i, data) in normalized_data.chunks(data_size).enumerate() {
        // Build share
        // first share: namespace_version (1-byte) || namespace_id (28-byte) || info_byte (1-byte) || sequence_len (4-byte) || data || padding with 0s until 512 bytes
        // first share: namespace_version (1-byte) || namespace_id (28-byte) || info_byte (1-byte) || data || padding with 0s until 512 bytes
        let mut share = vec![];
        share.push(UInt8::allocate(cs, namespace_version));
        share.extend(
            namespace_id
                .iter()
                .map(|b| UInt8::allocate(cs, *b))
                .collect::<Vec<_>>(),
        );
        share.push(new_info_byte(cs, share_version, i == 0));
        share.extend(data);
        share.resize(SHARE_BYTE_LEN, UInt8::allocate_constant(cs, 0));
        shares.push(share.try_into().unwrap());
    }
    shares
}

fn new_info_byte<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    version: u8,
    is_first_share: bool,
) -> UInt8<F> {
    let prefix = version << 1;
    let byte = if is_first_share { prefix + 1 } else { prefix };
    UInt8::allocate(cs, byte)
}

/// Compute root of merkle mountaint range
fn compute_mmr_root<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    shares: Vec<[UInt8<F>; SHARE_BYTE_LEN]>,
) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
    const SUBTREE_ROOT_THRESHOLD: usize = 64;
    let shares_len = shares.len();
    let subtree_width = subtree_width(shares_len, SUBTREE_ROOT_THRESHOLD);
    let tree_sizes = merkle_mountain_range_sizes(shares_len, subtree_width);

    let mut leaf_sets = vec![];
    let mut cursor = 0;
    for tree_size in tree_sizes.iter() {
        let mut leaf_set = vec![];
        (cursor..cursor + tree_size).for_each(|j| leaf_set.push(shares[j]));
        leaf_sets.push(leaf_set);
        cursor += tree_size;
    }

    let mut subtree_roots = vec![];
    for set in leaf_sets.iter() {
        let mut nmt = Nmt::new();
        for leaf in set.iter() {
            let namespace_id = &leaf[..NS_SIZE];
            let data = leaf;
            nmt.push(cs, namespace_id, data);
        }

        let nmt_root = nmt.root(cs);
        subtree_roots.push(nmt_root);
    }

    let mut subtree_roots_slice = vec![];
    for root in subtree_roots.iter() {
        subtree_roots_slice.push(root.as_slice());
    }
    hash_from_byte_slice(cs, &subtree_roots_slice)
}

// computes a Merkle tree where the leaves are the byte slice,
// in the provided order. It follows RFC-6962.
fn hash_from_byte_slice<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    items: &[&[UInt8<F>]],
) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
    let len = items.len();
    match len {
        0 => hasher::empty_hash(cs),
        1 => hasher::leaf_hash(cs, items[0]),
        _ => {
            let k = get_split_point(len);
            let left = hash_from_byte_slice(cs, &items[..k]);
            let right = hash_from_byte_slice(cs, &items[k..]);
            hasher::inner_hash(cs, &left, &right)
        }
    }
}

mod hasher {
    use boojum::{
        cs::traits::cs::ConstraintSystem,
        field::SmallField,
        gadgets::{sha256::SHA256_DIGEST_SIZE, u8::UInt8},
    };

    pub fn empty_hash<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
    ) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
        boojum::gadgets::sha256::sha256(cs, &[])
    }

    const LEAF_PREFIX: u8 = 0;
    const INNER_PREFIX: u8 = 1;
    // returns tmhash(0x00 || leaf)
    pub fn leaf_hash<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        leaf: &[UInt8<F>],
    ) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
        let mut bytes = vec![];
        bytes.push(UInt8::allocated_constant(cs, LEAF_PREFIX));
        bytes.extend(leaf);
        boojum::gadgets::sha256::sha256(cs, &bytes)
    }

    // returns tmhash(0x01 || left || right)
    pub fn inner_hash<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        left: &[UInt8<F>],
        right: &[UInt8<F>],
    ) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
        let mut bytes = vec![];
        bytes.push(UInt8::allocated_constant(cs, INNER_PREFIX));
        bytes.extend(left);
        bytes.extend(right);
        boojum::gadgets::sha256::sha256(cs, &bytes)
    }
}

fn subtree_width(share_count: usize, subtree_root_threshold: usize) -> usize {
    let mut s = share_count / subtree_root_threshold;

    if share_count % subtree_root_threshold != 0 {
        s += 1;
    }

    let x = round_up_power_of_two(s);
    let y = round_up_power_of_two((share_count as f64).sqrt().ceil() as usize);

    std::cmp::min(x, y)
}

fn round_up_power_of_two(x: usize) -> usize {
    let mut result = 1;
    while result < x {
        result *= 2
    }
    result
}

fn round_down_power_of_two(x: usize) -> usize {
    let round_up = round_up_power_of_two(x);
    if round_up == x {
        round_up
    } else {
        round_up / 2
    }
}

fn merkle_mountain_range_sizes(total_size: usize, max_tree_size: usize) -> Vec<usize> {
    let mut tree_sizes = vec![];
    let mut total_size = total_size;
    while total_size != 0 {
        let tree_size = if total_size >= max_tree_size {
            max_tree_size
        } else {
            round_down_power_of_two(total_size)
        };
        tree_sizes.push(tree_size);
        total_size -= tree_size;
    }
    tree_sizes
}

// returns the largest power of 2 less than length
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
