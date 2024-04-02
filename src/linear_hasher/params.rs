use boojum::gadgets::sha256::SHA256_DIGEST_SIZE;

use crate::base_structures::log_query::L2_TO_L1_MESSAGE_BYTE_LENGTH;

pub const NAMESPACE_ID_LEN: usize = 28;
pub const NAMESPACE_VERSION_LEN: usize = 1;
pub const NAMESPACE_LEN: usize = NAMESPACE_ID_LEN + NAMESPACE_VERSION_LEN;
pub const DATA_ARRAY_LEN: usize = 1139;
pub const DATA_BYTES_LEN: usize = DATA_ARRAY_LEN * L2_TO_L1_MESSAGE_BYTE_LENGTH;

pub const NAMESPACE_VERSION: u8 = 0;
pub const NAMESPACE_ID: [u8; NAMESPACE_ID_LEN] = [0; NAMESPACE_ID_LEN];
pub const SHARE_VERSION: u8 = 0;

pub const NS_SIZE: usize = 29;
pub const SHARE_BYTE_LEN: usize = 512;

pub const NMT_ROOT_SIZE: usize = NAMESPACE_LEN + NAMESPACE_LEN + SHA256_DIGEST_SIZE;
