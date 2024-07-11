////
////
//// This file is generated by the Pulse2Rust tool
////
////

pub static uds_len: super::hacl::hashable_len = 32;
pub enum dice_return_code {
    DICE_SUCCESS,
    DICE_ERROR,
}
pub struct engine_record_t {
    pub l0_image_header_size: super::hacl::signable_len,
    pub l0_image_header: std::vec::Vec<u8>,
    pub l0_image_header_sig: std::vec::Vec<u8>,
    pub l0_binary_size: super::hacl::hashable_len,
    pub l0_binary: std::vec::Vec<u8>,
    pub l0_binary_hash: std::vec::Vec<u8>,
    pub l0_image_auth_pubkey: std::vec::Vec<u8>,
}

