// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    binary_config::BinaryConfig,
    file_format::{basic_test_module, CompiledModule},
    file_format_common::*,
};
use move_core_types::{metadata::Metadata, vm_status::StatusCode};

fn malformed_simple_versioned_test(version: u32) {
    // bad uleb (more than allowed for table count)
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(150); // table count (high bit 1)
    binary.push(150); // table count (high bit 1)
    binary.push(1);
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected bad uleb").major_status(),
        StatusCode::MALFORMED
    );

    // bad uleb (too big)
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(150); // table count (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(150); // table count again (high bit 1)
    binary.push(0); // table count again
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected bad uleb").major_status(),
        StatusCode::MALFORMED
    );

    // no tables
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(0); // table count
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected no table count").major_status(),
        StatusCode::MALFORMED
    );

    // missing tables
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(10); // table count
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected no table header").major_status(),
        StatusCode::MALFORMED
    );

    // missing table content
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(1); // table count
    binary.push(1); // table type
    binary.push(0); // table offset
    binary.push(10); // table length
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected no table content").major_status(),
        StatusCode::MALFORMED
    );

    // bad table header (bad offset)
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(1); // table count
    binary.push(1); // table type
    binary.push(100); // bad table offset
    binary.push(10); // table length
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected bad table offset").major_status(),
        StatusCode::BAD_HEADER_TABLE
    );

    // bad table header (bad offset)
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(2); // table count
    binary.push(1); // table type
    binary.push(0); // table offset
    binary.push(10); // table length
    binary.push(2); // table type
    binary.push(100); // bad table offset
    binary.push(10); // table length
    binary.resize(binary.len() + 5000, 0);
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected bad table offset").major_status(),
        StatusCode::BAD_HEADER_TABLE
    );

    // incomplete table
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(1); // table count
    binary.push(1); // table type
    binary.push(0); // table offset
    binary.push(10); // table length
    binary.resize(binary.len() + 5, 0);
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected bad table content").major_status(),
        StatusCode::MALFORMED
    );

    // unknown table
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(1); // table count
    binary.push(100); // table type
    binary.push(0); // table offset
    binary.push(10); // table length
    binary.resize(binary.len() + 10, 0);
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected unknown table").major_status(),
        StatusCode::UNKNOWN_TABLE_TYPE
    );

    // duplicate table
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend(version.to_le_bytes()); // version
    binary.push(3); // table count
    binary.push(1); // table type
    binary.push(0); // table offset
    binary.push(10); // table length
    binary.push(2); // table type
    binary.push(10); // table offset
    binary.push(10); // table length
    binary.push(1); // table type
    binary.push(20); // table offset
    binary.push(10); // table length
    binary.resize(binary.len() + 5000, 0);
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected table offset overflow")
            .major_status(),
        StatusCode::DUPLICATE_TABLE
    );
}

#[test]
#[allow(clippy::same_item_push)]
fn malformed_simple() {
    // empty binary
    let binary = vec![];
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected malformed binary").major_status(),
        StatusCode::BAD_MAGIC
    );

    // under-sized binary
    let binary = vec![0u8, 0u8, 0u8];
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected malformed binary").major_status(),
        StatusCode::BAD_MAGIC
    );

    // bad magic
    let binary = vec![0u8; 4];
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected bad magic").major_status(),
        StatusCode::BAD_MAGIC
    );

    // only magic
    let binary = BinaryConstants::MOVE_MAGIC.to_vec();
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected malformed binary").major_status(),
        StatusCode::MALFORMED
    );

    // bad version
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend((VERSION_MAX.checked_add(1).unwrap()).to_le_bytes()); // version
    binary.push(10); // table count
    binary.push(0); // rest of binary
    let res = CompiledModule::deserialize_with_defaults(&binary);
    assert_eq!(
        res.expect_err("Expected unknown version").major_status(),
        StatusCode::UNKNOWN_VERSION
    );

    // versioned tests
    for version in VERSION_1..VERSION_MAX {
        malformed_simple_versioned_test(version);
    }
}

#[test]
fn max_version_lower_than_hardcoded() {
    let mut binary = BinaryConstants::MOVE_MAGIC.to_vec();
    binary.extend((VERSION_MAX).to_le_bytes()); // version
    binary.push(10); // table count
    binary.push(0); // rest of binary

    let res = CompiledModule::deserialize_with_config(
        &binary,
        &BinaryConfig::legacy(VERSION_MAX.checked_sub(1).unwrap(), false),
    );
    assert_eq!(
        res.expect_err("Expected unknown version").major_status(),
        StatusCode::UNKNOWN_VERSION
    );
}

#[test]
fn deserialize_trailing_bytes() {
    let module = basic_test_module();
    let bytes = {
        let mut v = vec![];
        module.serialize(&mut v).unwrap();
        v
    };
    let test = |bytes| {
        // ok with flag false
        CompiledModule::deserialize_with_config(
            bytes,
            &BinaryConfig::with_extraneous_bytes_check(false),
        )
        .unwrap();
        // error with flag true
        let status_code = CompiledModule::deserialize_with_config(
            bytes,
            &BinaryConfig::with_extraneous_bytes_check(true),
        )
        .unwrap_err()
        .major_status();
        assert_eq!(status_code, StatusCode::TRAILING_BYTES);
    };
    // simple trailing byte
    let test1 = {
        let mut v = bytes.clone();
        v.push(0);
        v
    };
    test(&test1);

    // many bytes
    let test2 = {
        let mut v = bytes.clone();
        v.push(3);
        v.push(1);
        v.push(0);
        v.push(10);
        v
    };
    test(&test2);

    // another module
    let test3 = {
        let mut v = bytes.clone();
        v.extend(bytes);
        v
    };
    test(&test3);
}

#[test]
fn no_metadata() {
    let test = |bytes| {
        // ok with flag false
        CompiledModule::deserialize_with_config(
            bytes,
            &BinaryConfig::with_extraneous_bytes_check(false),
        )
        .unwrap();
        // error with flag true
        let status_code = CompiledModule::deserialize_with_config(
            bytes,
            &BinaryConfig::with_extraneous_bytes_check(true),
        )
        .unwrap_err()
        .major_status();
        assert_eq!(status_code, StatusCode::MALFORMED);
    };
    // empty metadata
    let mut module = basic_test_module();
    module.metadata.push(Metadata {
        key: vec![],
        value: vec![],
    });
    let test2 = {
        let mut v = vec![];
        module.serialize(&mut v).unwrap();
        v
    };
    test(&test2);

    // lots of metadata
    let metadata_bytes = {
        let module = basic_test_module();
        let mut v = vec![];
        module.serialize(&mut v).unwrap();
        v
    };
    let mut module = basic_test_module();
    module.metadata.push(Metadata {
        key: metadata_bytes.clone(),
        value: metadata_bytes.clone(),
    });
    module.metadata.push(Metadata {
        key: metadata_bytes.clone(),
        value: metadata_bytes.clone(),
    });
    let test2 = {
        let mut v = vec![];
        module.serialize(&mut v).unwrap();
        v
    };
    test(&test2);
}
