#[macro_use]
extern crate quote;
#[macro_use]
extern crate syn;

extern crate proc_macro;

use proc_macro::TokenStream;
use syn::DeriveInput;

// #[proc_macro]
// pub trait Encode {}

// #[proc_macro]
// pub trait Decode {}

// NOTE: this is a mere stub for #[derive(Encode)]'s implementation to eliminate errors.
#[proc_macro_derive(Encode)]
pub fn encode_macro_derive(input: TokenStream) -> TokenStream { 
  let input = parse_macro_input!(input as DeriveInput);
  let expanded = quote!{};
  proc_macro::TokenStream::from(expanded)
}

#[proc_macro_derive(Decode)]
pub fn decode_macro_derive(input: TokenStream) -> TokenStream { 
  let input = parse_macro_input!(input as DeriveInput);
  let expanded = quote!{};
  proc_macro::TokenStream::from(expanded)
}