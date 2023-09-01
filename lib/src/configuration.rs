use crate::env::*;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Used for moving definitions up and down
/// by specifing it in the configuration file
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct DefinitionMove {
    #[serde(rename = "move")]
    /// "up" | "down"
    pub(crate) move_: String,
    pub(crate) after: Option<String>,
    pub(crate) before: Option<String>,
}

// if the destination is not specified it means an item should be removed
// this change was introduced to temporarily remove blocking modules from a file
impl DefinitionMove {
    pub(crate) fn get_ident(&self) -> Option<String> {
        match &self.before {
            Some(x) => Some(x.clone()),
            None => self.after.clone(),
            /*original:
            match &self.after {
                Some(x) => Some(x.clone()),
                None => panic!("Expecting before or after to be present in DefinitionMove"),
            },
            */
        }
    }

    pub(crate) fn is_before(&self) -> bool {
        self.before.is_some()
    }
}

type File = String; // Represents a file path, ex: examples/foo/bar.rs"
type Context = String; // Represents a context inside a file, ex: "top_level::some_mod"
type Identifier = String; // Represents a identifier inside a context ex: "SomeType"

type Reorder = HashMap<File, HashMap<Context, HashMap<Identifier, DefinitionMove>>>;

#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct Configuration {
    pub(crate) axiomatize: bool,
    /// [reorder] states the order that definitions should
    /// appear in the translation output, example:
    /// "reorder": {
    ///   "some/path/some_file.rs": {
    ///     "top_level::some_mod": { "bar": { "move": "down", "after", "foo" }, ... },
    ///      ...
    ///   },
    ///  ...
    /// }
    pub(crate) reorder: Reorder,
    pub(crate) debug_reorder: bool,
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

pub(crate) fn config_get_reorder<'a>(
    env: &'a Env,
    context: &str,
    id: &str,
) -> Option<&'a DefinitionMove> {
    match env.configuration.reorder.get(&env.file) {
        Some(contexts) => match contexts.get(context) {
            Some(identifiers) => identifiers.get(id),
            None => None,
        },
        None => None,
    }
}
