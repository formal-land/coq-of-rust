use serde::{Deserialize, Serialize};

#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct Configuration {
    pub(crate) axiomatize: bool,
}

pub(crate) fn get_configuration(configuration_file_path: &str) -> Configuration {
    match std::fs::read_to_string(configuration_file_path) {
        Ok(configuration_file_content) => match serde_json::from_str(&configuration_file_content) {
            Ok(configuration) => return configuration,
            Err(error) => {
                eprintln!("Could not parse configuration file: {}", error);
            }
        },
        Err(_) => {
            eprintln!(
                "Current working directory: {}",
                std::env::current_dir().unwrap().display()
            );
            eprintln!(
                "Could not read configuration file: {}",
                configuration_file_path
            );
        }
    }

    Configuration::default()
}
