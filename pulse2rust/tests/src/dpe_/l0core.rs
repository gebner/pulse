////
////
//// This file is generated by the Pulse2Rust tool
////
////

pub fn create_deviceIDCRI(
    pub_perm: (),
    pub_seq: (),
    _buf: (),
    deviceID_pub: &mut [u8],
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCSR_ingredients: super::l0types::deviceIDCSR_ingredients_t,
) -> super::l0types::deviceIDCSR_ingredients_t {
    let deviceIDCRI = super::x509::x509_get_deviceIDCRI(
        deviceIDCSR_ingredients,
        deviceID_pub,
        (),
        (),
    );
    super::x509::serialize_deviceIDCRI(
        deviceIDCRI.1,
        deviceIDCRI_len,
        deviceIDCRI_buf,
        (),
    );
    deviceIDCRI.0
}
pub fn sign_and_finalize_deviceIDCSR(
    priv_perm: (),
    priv_seq: (),
    _cri_buf: (),
    _csr_buf: (),
    deviceID_priv: &mut [u8],
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCSR_len: usize,
    deviceIDCSR_buf: &mut [u8],
    deviceIDCSR_ingredients: (),
) -> () {
    let mut deviceIDCRI_sig = vec![0; 64];
    super::hacl::ed25519_sign(
        &mut deviceIDCRI_sig,
        deviceID_priv,
        deviceIDCRI_len,
        deviceIDCRI_buf,
        (),
        (),
        (),
        (),
        (),
    );
    let deviceIDCSR = super::x509::x509_get_deviceIDCSR(
        deviceIDCRI_len,
        deviceIDCRI_buf,
        &mut deviceIDCRI_sig,
        (),
        (),
        (),
        (),
    );
    drop(deviceIDCRI_sig);
    super::x509::serialize_deviceIDCSR(
        deviceIDCRI_len,
        deviceIDCSR,
        deviceIDCSR_len,
        deviceIDCSR_buf,
        (),
    )
}
pub fn create_aliasKeyTBS(
    fwid_perm: (),
    authKey_perm: (),
    device_perm: (),
    aliasKey_perm: (),
    fwid0: (),
    authKeyID0: (),
    deviceID_pub0: (),
    aliasKey_pub0: (),
    _buf: (),
    fwid: &mut [u8],
    authKeyID: &mut [u8],
    deviceID_pub: &mut [u8],
    aliasKey_pub: &mut [u8],
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyCRT_ingredients: super::l0types::aliasKeyCRT_ingredients_t,
) -> super::l0types::aliasKeyCRT_ingredients_t {
    let aliasKeyTBS = super::x509::x509_get_aliasKeyTBS(
        aliasKeyCRT_ingredients,
        fwid,
        deviceID_pub,
        aliasKey_pub,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    super::x509::serialize_aliasKeyTBS(
        aliasKeyTBS.1,
        aliasKeyTBS_len,
        aliasKeyTBS_buf,
        (),
    );
    aliasKeyTBS.0
}
pub fn sign_and_finalize_aliasKeyCRT(
    priv_perm: (),
    priv_seq: (),
    _tbs_buf: (),
    _crt_buf: (),
    deviceID_priv: &mut [u8],
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyCRT_len: usize,
    aliasKeyCRT_buf: &mut [u8],
    aliasKeyCRT_ingredients: (),
) -> () {
    let mut aliasKeyTBS_sig = vec![0; 64];
    super::hacl::ed25519_sign(
        &mut aliasKeyTBS_sig,
        deviceID_priv,
        aliasKeyTBS_len,
        aliasKeyTBS_buf,
        (),
        (),
        (),
        (),
        (),
    );
    let aliasKeyCRT = super::x509::x509_get_aliasKeyCRT(
        aliasKeyTBS_len,
        aliasKeyTBS_buf,
        &mut aliasKeyTBS_sig,
        (),
        (),
        (),
        (),
    );
    drop(aliasKeyTBS_sig);
    super::x509::serialize_aliasKeyCRT(
        aliasKeyTBS_len,
        aliasKeyCRT,
        aliasKeyCRT_len,
        aliasKeyCRT_buf,
        (),
    )
}
pub fn l0_main(
    cdi: &mut [u8],
    deviceID_pub: &mut [u8],
    deviceID_priv: &mut [u8],
    aliasKey_pub: &mut [u8],
    aliasKey_priv: &mut [u8],
    aliasKeyTBS_len: usize,
    aliasKeyCRT_len: usize,
    aliasKeyCRT: &mut [u8],
    deviceIDCRI_len: usize,
    deviceIDCSR_len: usize,
    deviceIDCSR: &mut [u8],
    mut record: super::l0types::l0_record_t,
    repr: (),
    cdi0: (),
    deviceID_pub0: (),
    deviceID_priv0: (),
    aliasKey_pub0: (),
    aliasKey_priv0: (),
    aliasKeyCRT0: (),
    deviceIDCSR0: (),
    cdi_perm: (),
    p: (),
) -> super::l0types::l0_record_t {
    super::l0crypto::derive_DeviceID(
        super::hacl::dice_hash_alg0(()),
        deviceID_pub,
        deviceID_priv,
        cdi,
        record.deviceID_label_len,
        &mut record.deviceID_label,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    super::l0crypto::derive_AliasKey(
        super::hacl::dice_hash_alg0(()),
        aliasKey_pub,
        aliasKey_priv,
        cdi,
        &mut record.fwid,
        record.aliasKey_label_len,
        &mut record.aliasKey_label,
        (),
        (),
        (),
        (),
        (),
        (),
        (),
    );
    let mut authKeyID = vec![0; 32];
    super::l0crypto::derive_AuthKeyID(
        super::hacl::dice_hash_alg0(()),
        &mut authKeyID,
        deviceID_pub,
        (),
        (),
        (),
    );
    let mut deviceIDCRI = vec![0; deviceIDCRI_len];
    let deviceIDCSR_ingredients = super::l0core::create_deviceIDCRI(
        (),
        (),
        (),
        deviceID_pub,
        deviceIDCRI_len,
        &mut deviceIDCRI,
        record.deviceIDCSR_ingredients,
    );
    super::l0core::sign_and_finalize_deviceIDCSR(
        (),
        (),
        (),
        (),
        deviceID_priv,
        deviceIDCRI_len,
        &mut deviceIDCRI,
        deviceIDCSR_len,
        deviceIDCSR,
        (),
    );
    let mut aliasKeyTBS = vec![0; aliasKeyTBS_len];
    let aliasKeyCRT_ingredients = super::l0core::create_aliasKeyTBS(
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        &mut record.fwid,
        &mut authKeyID,
        deviceID_pub,
        aliasKey_pub,
        aliasKeyTBS_len,
        &mut aliasKeyTBS,
        record.aliasKeyCRT_ingredients,
    );
    super::l0core::sign_and_finalize_aliasKeyCRT(
        (),
        (),
        (),
        (),
        deviceID_priv,
        aliasKeyTBS_len,
        &mut aliasKeyTBS,
        aliasKeyCRT_len,
        aliasKeyCRT,
        (),
    );
    drop(authKeyID);
    drop(deviceIDCRI);
    drop(aliasKeyTBS);
    let r1 = super::l0types::l0_record_t {
        fwid: record.fwid,
        deviceID_label_len: record.deviceID_label_len,
        deviceID_label: record.deviceID_label,
        aliasKey_label_len: record.aliasKey_label_len,
        aliasKey_label: record.aliasKey_label,
        deviceIDCSR_ingredients: deviceIDCSR_ingredients,
        aliasKeyCRT_ingredients: aliasKeyCRT_ingredients,
    };
    r1
}

