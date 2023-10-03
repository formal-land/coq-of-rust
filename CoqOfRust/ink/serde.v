(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

Module de.
  Module Deserializer.
    (* TODO *)
    (*
    pub trait Deserializer<'de>: Sized {
        type Error: Error;

        // Required methods
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_byte_buf<V>(
            self,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_unit_struct<V>(
            self,
            name: &'static str,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_newtype_struct<V>(
            self,
            name: &'static str,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_tuple<V>(
            self,
            len: usize,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_tuple_struct<V>(
            self,
            name: &'static str,
            len: usize,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_struct<V>(
            self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_enum<V>(
            self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_identifier<V>(
            self,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;
        fn deserialize_ignored_any<V>(
            self,
            visitor: V
        ) -> Result<V::Value, Self::Error>
          where V: Visitor<'de>;

        // Provided methods
        fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de> { ... }
        fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Self::Error>
          where V: Visitor<'de> { ... }
        fn is_human_readable(&self) -> bool { ... }
    }
    *)
    Class Trait (Self : Set) : Type := {
      Error : Set;
    }.

    Global Instance Method_Error `(Trait)
      : Notation.DoubleColonType Self "Error" := {
      Notation.double_colon_type := Error;
    }.
  End Deserializer.

  Module Deserialize.
    (*
    
    *)
    Class Trait (Self : Set) : Set := {
      deserialize `{H' : State.Trait} {__D : Set} `{serde.de.Deserializer.Trait __D} :
        __D -> M (H := H') (core.result.Result Self __D::type["Error"]);
    }.
  End Deserialize.
End de.

Module ser.
  Module Serializer.
    (* TODO *)
    (*
    pub trait Serializer: Sized {
        type Ok;
        type Error: Error;
        type SerializeSeq: SerializeSeq<Ok = Self::Ok, Error = Self::Error>;
        type SerializeTuple: SerializeTuple<Ok = Self::Ok, Error = Self::Error>;
        type SerializeTupleStruct: SerializeTupleStruct<Ok = Self::Ok, Error = Self::Error>;
        type SerializeTupleVariant: SerializeTupleVariant<Ok = Self::Ok, Error = Self::Error>;
        type SerializeMap: SerializeMap<Ok = Self::Ok, Error = Self::Error>;
        type SerializeStruct: SerializeStruct<Ok = Self::Ok, Error = Self::Error>;
        type SerializeStructVariant: SerializeStructVariant<Ok = Self::Ok, Error = Self::Error>;

        // Required methods
        fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error>;
        fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error>;
        fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error>;
        fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error>;
        fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error>;
        fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error>;
        fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error>;
        fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error>;
        fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error>;
        fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error>;
        fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error>;
        fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error>;
        fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error>;
        fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error>;
        fn serialize_none(self) -> Result<Self::Ok, Self::Error>;
        fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
          where T: Serialize + ?Sized;
        fn serialize_unit(self) -> Result<Self::Ok, Self::Error>;
        fn serialize_unit_struct(
            self,
            name: &'static str
        ) -> Result<Self::Ok, Self::Error>;
        fn serialize_unit_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str
        ) -> Result<Self::Ok, Self::Error>;
        fn serialize_newtype_struct<T>(
            self,
            name: &'static str,
            value: &T
        ) -> Result<Self::Ok, Self::Error>
          where T: Serialize + ?Sized;
        fn serialize_newtype_variant<T>(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            value: &T
        ) -> Result<Self::Ok, Self::Error>
          where T: Serialize + ?Sized;
        fn serialize_seq(
            self,
            len: Option<usize>
        ) -> Result<Self::SerializeSeq, Self::Error>;
        fn serialize_tuple(
            self,
            len: usize
        ) -> Result<Self::SerializeTuple, Self::Error>;
        fn serialize_tuple_struct(
            self,
            name: &'static str,
            len: usize
        ) -> Result<Self::SerializeTupleStruct, Self::Error>;
        fn serialize_tuple_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize
        ) -> Result<Self::SerializeTupleVariant, Self::Error>;
        fn serialize_map(
            self,
            len: Option<usize>
        ) -> Result<Self::SerializeMap, Self::Error>;
        fn serialize_struct(
            self,
            name: &'static str,
            len: usize
        ) -> Result<Self::SerializeStruct, Self::Error>;
        fn serialize_struct_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize
        ) -> Result<Self::SerializeStructVariant, Self::Error>;

        // Provided methods
        fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> { ... }
        fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> { ... }
        fn collect_seq<I>(self, iter: I) -> Result<Self::Ok, Self::Error>
          where I: IntoIterator,
                <I as IntoIterator>::Item: Serialize { ... }
        fn collect_map<K, V, I>(self, iter: I) -> Result<Self::Ok, Self::Error>
          where K: Serialize,
                V: Serialize,
                I: IntoIterator<Item = (K, V)> { ... }
        fn collect_str<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
          where T: Display + ?Sized { ... }
        fn is_human_readable(&self) -> bool { ... }
    }
    *)
    Class Trait (Self : Set) : Type := {
      Ok : Set;
      Error : Set;
    }.

    Global Instance Method_Ok `(Trait)
      : Notation.DoubleColonType Self "Ok" := {
      Notation.double_colon_type := Ok;
    }.

    Global Instance Method_Error `(Trait)
      : Notation.DoubleColonType Self "Error" := {
      Notation.double_colon_type := Error;
    }.
  End Serializer.

  Module Serialize.
    (*
    pub trait Serialize {
        // Required method
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
          where S: Serializer;
    }
    *)
    Class Trait (Self : Set) : Set := {
      serialize `{H' : State.Trait} {__S : Set} `{serde.ser.Serializer.Trait __S} :
        (ref Self) ->
        __S ->
        M (H := H') (core.result.Result __S::type["Ok"] __S::type["Error"]);
    }.
  End Serialize.
End ser.
