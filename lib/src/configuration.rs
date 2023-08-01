use crate::env::*;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

type File = String; // Represents a file path, ex: examples/foo/bar.rs"
type Context = String; // Represents a context inside a file, ex: "top_level::some_mod"
type Identifier = String; // Represents a identifier inside a context ex: "SomeType"

type Reorder = HashMap<File, HashMap<Context, Vec<Identifier>>>;

#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct Configuration {
    pub(crate) axiomatize: bool,
    /// [reorder] states the order that definitions should
    /// appear in the translation output:
    /// "reorder": {
    ///   "some/path/some_file.rs": {
    ///     "top_level::some_mod": ["bar", "foo"],
    ///      ...
    ///   },
    ///  ...
    /// }
    pub(crate) reorder: Reorder,
}

pub(crate) fn get_configuration(configuration_file_path: &str) -> Configuration {
    match std::fs::read_to_string(configuration_file_path) {
        Ok(configuration_file_content) => match serde_json::from_str(&configuration_file_content) {
            Ok(configuration) => return configuration,
            Err(error) => {
                eprintln!("Warning: Could not parse configuration file: {}", error);
            }
        },
        Err(_) => {
            eprintln!(
                "Warnning: Current working directory: {}",
                std::env::current_dir().unwrap().display()
            );
            eprintln!(
                "  Could not read configuration file: {}",
                configuration_file_path
            );
        }
    }

    Configuration::default()
}

pub(crate) fn config_get_reorder(env: &Env) -> Vec<String> {
    match env.configuration.reorder.get(&env.file) {
        Some(contexts) => match contexts.get(&env.context) {
            Some(identifiers) => identifiers.clone(),
            None => vec![],
        },
        None => vec![],
    }
}
