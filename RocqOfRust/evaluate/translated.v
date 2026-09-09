Require Import RocqOfRust.RocqOfRust.

Module Translated.
  Parameter ty_eqb : Ty.t -> Ty.t -> bool.

  Module Execution.
    Inductive t : Set :=
    | Done (output : Value.t + Exception.t)
    | OutOfFuel
    | Unsupported (message : string).
  End Execution.

  Module Runtime.
    Record t : Set := {
      get_function :
        string ->
        list Value.t ->
        list Ty.t ->
        option PolymorphicFunction.t;
      get_associated_function :
        Ty.t ->
        string ->
        list Value.t ->
        list Ty.t ->
        option PolymorphicFunction.t;
      get_trait_method :
        string ->
        Ty.t ->
        list Value.t ->
        list Ty.t ->
        string ->
        list Value.t ->
        list Ty.t ->
        option PolymorphicFunction.t;
    }.

    Definition integer_kind_of_ty (ty : Ty.t) : option IntegerKind.t :=
      if ty_eqb ty (Ty.path "i8") then Some IntegerKind.I8 else
      if ty_eqb ty (Ty.path "i16") then Some IntegerKind.I16 else
      if ty_eqb ty (Ty.path "i32") then Some IntegerKind.I32 else
      if ty_eqb ty (Ty.path "i64") then Some IntegerKind.I64 else
      if ty_eqb ty (Ty.path "i128") then Some IntegerKind.I128 else
      if ty_eqb ty (Ty.path "isize") then Some IntegerKind.Isize else
      if ty_eqb ty (Ty.path "u8") then Some IntegerKind.U8 else
      if ty_eqb ty (Ty.path "u16") then Some IntegerKind.U16 else
      if ty_eqb ty (Ty.path "u32") then Some IntegerKind.U32 else
      if ty_eqb ty (Ty.path "u64") then Some IntegerKind.U64 else
      if ty_eqb ty (Ty.path "u128") then Some IntegerKind.U128 else
      if ty_eqb ty (Ty.path "usize") then Some IntegerKind.Usize else
      None.

    Definition constant_function
        (ty : Ty.t)
        (value : Value.t) :
        PolymorphicFunction.t :=
      fun _ _ args =>
        match args with
        | [] => M.alloc ty value
        | _ => M.impossible "an associated constant takes no arguments"
        end.

    Definition get_primitive_associated_function
        (ty : Ty.t)
        (name : string)
        (_ : list Value.t)
        (_ : list Ty.t) :
        option PolymorphicFunction.t :=
      match PrimString.compare name "MIN" with
      | Eq =>
        match integer_kind_of_ty ty with
        | Some kind => Some (constant_function ty (Value.Integer kind (Integer.min kind)))
        | None => None
        end
      | _ =>
        match PrimString.compare name "MAX" with
        | Eq =>
          match integer_kind_of_ty ty with
          | Some kind => Some (constant_function ty (Value.Integer kind (Integer.max kind)))
          | None => None
          end
        | _ => None
        end
      end.

    Definition empty : t :=
      {|
        get_function := fun _ _ _ => None;
        get_associated_function := get_primitive_associated_function;
        get_trait_method := fun _ _ _ _ _ _ _ => None;
      |}.

    Fixpoint find_trait_method
        (methods :
          list
            (string *
              list Ty.t *
              Ty.t *
              string *
              PolymorphicFunction.t))
        (trait_name : string)
        (trait_tys : list Ty.t)
        (self_ty : Ty.t)
        (method_name : string) :
        option PolymorphicFunction.t :=
      match methods with
      | [] => None
      | (entry_trait_name,
          entry_trait_tys,
          entry_self_ty,
          entry_method_name,
          method) :: methods =>
        match PrimString.compare entry_trait_name trait_name with
        | Eq =>
          match PrimString.compare entry_method_name method_name with
          | Eq =>
            if List.eqb ty_eqb entry_trait_tys trait_tys then
              if ty_eqb entry_self_ty self_ty then
                Some method
              else find_trait_method methods trait_name trait_tys self_ty method_name
            else find_trait_method methods trait_name trait_tys self_ty method_name
          | _ => find_trait_method methods trait_name trait_tys self_ty method_name
          end
        | _ => find_trait_method methods trait_name trait_tys self_ty method_name
        end
      end.

    Fixpoint find_associated_function
        (functions : list (Ty.t * string * PolymorphicFunction.t))
        (ty : Ty.t)
        (name : string) :
        option PolymorphicFunction.t :=
      match functions with
      | [] => None
      | (entry_ty, entry_name, function) :: functions =>
        match PrimString.compare entry_name name with
        | Eq =>
          if ty_eqb entry_ty ty then
            Some function
          else
            find_associated_function functions ty name
        | _ => find_associated_function functions ty name
        end
      end.

    Definition of_all_tables
        (functions : list (string * PolymorphicFunction.t))
        (associated_functions : list (Ty.t * string * PolymorphicFunction.t))
        (trait_methods :
          list
            (string *
              list Ty.t *
              Ty.t *
              string *
              PolymorphicFunction.t)) :
        t :=
      {|
        get_function := fun path _ _ => List.assoc functions path;
        get_associated_function :=
          fun ty name _ _ =>
            match find_associated_function associated_functions ty name with
            | Some function => Some function
            | None => get_primitive_associated_function ty name [] []
            end;
        get_trait_method :=
          fun trait_name self_ty trait_consts trait_tys method_name _ _ =>
            match trait_consts with
            | [] =>
              find_trait_method
                trait_methods
                trait_name
                trait_tys
                self_ty
                method_name
            | _ => None
            end;
      |}.

    Definition of_tables
        (functions : list (string * PolymorphicFunction.t))
        (trait_methods :
          list
            (string *
              list Ty.t *
              Ty.t *
              string *
              PolymorphicFunction.t)) :
        t :=
      of_all_tables functions [] trait_methods.

    Definition of_function_table
        (functions : list (string * PolymorphicFunction.t)) :
        t :=
      of_tables functions [].

    Fixpoint get_function_from
        (runtimes : list t)
        (path : string)
        (generic_consts : list Value.t)
        (generic_tys : list Ty.t) :
        option PolymorphicFunction.t :=
      match runtimes with
      | [] => None
      | runtime :: runtimes =>
        match runtime.(get_function) path generic_consts generic_tys with
        | Some function => Some function
        | None => get_function_from runtimes path generic_consts generic_tys
        end
      end.

    Fixpoint get_associated_function_from
        (runtimes : list t)
        (ty : Ty.t)
        (name : string)
        (generic_consts : list Value.t)
        (generic_tys : list Ty.t) :
        option PolymorphicFunction.t :=
      match runtimes with
      | [] => None
      | runtime :: runtimes =>
        match runtime.(get_associated_function) ty name generic_consts generic_tys with
        | Some function => Some function
        | None =>
          get_associated_function_from runtimes ty name generic_consts generic_tys
        end
      end.

    Fixpoint get_trait_method_from
        (runtimes : list t)
        (trait_name : string)
        (self_ty : Ty.t)
        (trait_consts : list Value.t)
        (trait_tys : list Ty.t)
        (method_name : string)
        (generic_consts : list Value.t)
        (generic_tys : list Ty.t) :
        option PolymorphicFunction.t :=
      match runtimes with
      | [] => None
      | runtime :: runtimes =>
        match runtime.(get_trait_method)
          trait_name
          self_ty
          trait_consts
          trait_tys
          method_name
          generic_consts
          generic_tys with
        | Some method => Some method
        | None =>
          get_trait_method_from
            runtimes
            trait_name
            self_ty
            trait_consts
            trait_tys
            method_name
            generic_consts
            generic_tys
        end
      end.

    Definition combine (runtimes : list t) : t :=
      {|
        get_function := get_function_from runtimes;
        get_associated_function := get_associated_function_from runtimes;
        get_trait_method := get_trait_method_from runtimes;
      |}.
  End Runtime.

  Module Stack.
    Definition t : Set := list Value.t.

    Definition empty : t := [].

    Parameter address_to_nat : forall {Address : Set}, Address -> option nat.

    Definition make_pointer (address : nat) (path : Pointer.Path.t) : Value.t :=
      Value.Pointer {|
        Pointer.kind := Pointer.Kind.Ref;
        Pointer.core := Pointer.Core.Mutable address path;
      |}.

    Fixpoint read_path (value : Value.t) (path : Pointer.Path.t) : option Value.t :=
      match path with
      | [] => Some value
      | index :: path =>
        match Value.read_index value index with
        | Some value => read_path value path
        | None => None
        end
      end.

    Fixpoint write_path
        (value : Value.t)
        (path : Pointer.Path.t)
        (update : Value.t) :
        option Value.t :=
      match path with
      | [] => Some update
      | index :: path =>
        match Value.read_index value index with
        | Some sub_value =>
          match write_path sub_value path update with
          | Some sub_update => Value.write_index value index sub_update
          | None => None
          end
        | None => None
        end
      end.

    Definition alloc (stack : t) (value : Value.t) : Value.t * t :=
      (make_pointer (List.length stack) [], stack ++ [value]).

    Definition read (stack : t) (pointer : Value.t) : option Value.t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate value => value
        | Pointer.Core.Mutable address path =>
          match address_to_nat address with
          | Some address =>
            match List.nth_error stack address with
            | Some value => read_path value path
            | None => None
            end
          | None => None
          end
        end
      | _ => None
      end.

    Definition write
        (stack : t)
        (pointer update : Value.t) :
        option t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate _ => None
        | Pointer.Core.Mutable address path =>
          match address_to_nat address with
          | Some address =>
            match List.nth_error stack address with
            | Some value =>
              match write_path value path update with
              | Some value => Some (List.replace_at stack address value)
              | None => None
              end
            | None => None
            end
          | None => None
          end
        end
      | _ => None
      end.

    Definition get_sub_pointer
        (stack : t)
        (pointer : Value.t)
        (index : Pointer.Index.t) :
        option Value.t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate value =>
          match value with
          | Some value =>
            match Value.read_index value index with
            | Some value =>
              Some (Value.Pointer {|
                Pointer.kind := pointer.(Pointer.kind);
                Pointer.core := Pointer.Core.Immediate (Some value);
              |})
            | None => None
            end
          | None => None
          end
        | Pointer.Core.Mutable address path =>
          match read stack (Value.Pointer pointer) with
          | Some value =>
            match Value.read_index value index with
            | Some _ =>
              Some (Value.Pointer {|
                Pointer.kind := pointer.(Pointer.kind);
                Pointer.core := Pointer.Core.Mutable address (path ++ [index]);
              |})
            | None => None
            end
          | None => None
          end
        end
      | _ => None
      end.
  End Stack.

  Module Evaluate.
    Parameter closure_body : Value.t -> option (list Value.t -> M).

    Module Result.
      Inductive t : Set :=
      | Done (output : Value.t + Exception.t) (stack : Stack.t)
      | OutOfFuel
      | Unsupported (message : string).
    End Result.

    Fixpoint eval_with_stack
        (runtime : Runtime.t)
        (fuel : nat)
        (stack : Stack.t)
        (expression : M) :
        Result.t :=
      match fuel with
      | O => Result.OutOfFuel
      | S fuel =>
        match expression with
        | LowM.Pure output => Result.Done output stack
        | LowM.CallPrimitive primitive k =>
          match primitive with
          | Primitive.StateAlloc _ value =>
            let '(pointer, stack) := Stack.alloc stack value in
            eval_with_stack runtime fuel stack (k pointer)
          | Primitive.StateRead pointer =>
            match Stack.read stack pointer with
            | Some value => eval_with_stack runtime fuel stack (k value)
            | None => Result.Unsupported "unable to read pointer"
            end
          | Primitive.StateWrite pointer update =>
            match Stack.write stack pointer update with
            | Some stack =>
              eval_with_stack runtime fuel stack (k (Value.Tuple []))
            | None => Result.Unsupported "unable to write pointer"
            end
          | Primitive.GetSubPointer pointer index =>
            match Stack.get_sub_pointer stack pointer index with
            | Some pointer => eval_with_stack runtime fuel stack (k pointer)
            | None => Result.Unsupported "unable to get sub-pointer"
            end
          | Primitive.GetFunction path generic_consts generic_tys =>
            match runtime.(Runtime.get_function) path generic_consts generic_tys with
            | Some function =>
              eval_with_stack
                runtime
                fuel
                stack
                (k (M.closure (function generic_consts generic_tys)))
            | None => Result.Unsupported "function not found"
            end
          | Primitive.GetAssociatedFunction ty name generic_consts generic_tys =>
            match runtime.(Runtime.get_associated_function)
              ty name generic_consts generic_tys with
            | Some function =>
              eval_with_stack
                runtime
                fuel
                stack
                (k (M.closure (function generic_consts generic_tys)))
            | None => Result.Unsupported "associated function not found"
            end
          | Primitive.GetTraitMethod
              trait_name self_ty trait_consts trait_tys method_name generic_consts generic_tys =>
            match runtime.(Runtime.get_trait_method)
              trait_name
              self_ty
              trait_consts
              trait_tys
              method_name
              generic_consts
              generic_tys with
            | Some method =>
              eval_with_stack
                runtime
                fuel
                stack
                (k (M.closure (method generic_consts generic_tys)))
            | None => Result.Unsupported "trait method not found"
            end
          end
        | LowM.CallClosure _ closure arguments k =>
          match closure_body closure with
          | Some body =>
            match eval_with_stack runtime fuel stack (body arguments) with
            | Result.Done output stack =>
              eval_with_stack runtime fuel stack (k output)
            | Result.OutOfFuel => Result.OutOfFuel
            | Result.Unsupported message => Result.Unsupported message
            end
          | None => Result.Unsupported "value is not a closure"
          end
        | LowM.CallLogicalOp op lhs rhs k =>
          match lhs with
          | Value.Bool lhs =>
            match op, lhs with
            | LogicalOp.And, false =>
              eval_with_stack runtime fuel stack (k (inl (Value.Bool false)))
            | LogicalOp.Or, true =>
              eval_with_stack runtime fuel stack (k (inl (Value.Bool true)))
            | _, _ =>
              match eval_with_stack runtime fuel stack rhs with
              | Result.Done output stack =>
                eval_with_stack runtime fuel stack (k output)
              | Result.OutOfFuel => Result.OutOfFuel
              | Result.Unsupported message => Result.Unsupported message
              end
            end
          | _ => Result.Unsupported "expected a boolean logical operand"
          end
        | LowM.Let _ expression k =>
          match eval_with_stack runtime fuel stack expression with
          | Result.Done output stack =>
            eval_with_stack runtime fuel stack (k output)
          | Result.OutOfFuel => Result.OutOfFuel
          | Result.Unsupported message => Result.Unsupported message
          end
        | LowM.LetAlloc _ expression k =>
          match eval_with_stack runtime fuel stack expression with
          | Result.Done (inl value) stack =>
            let '(pointer, stack) := Stack.alloc stack value in
            eval_with_stack runtime fuel stack (k (inl pointer))
          | Result.Done (inr exception) stack =>
            eval_with_stack runtime fuel stack (k (inr exception))
          | Result.OutOfFuel => Result.OutOfFuel
          | Result.Unsupported message => Result.Unsupported message
          end
        | LowM.Loop ty body k =>
          match eval_with_stack runtime fuel stack body with
          | Result.Done (inl _) stack =>
            eval_with_stack runtime fuel stack (LowM.Loop ty body k)
          | Result.Done (inr exception) stack =>
            eval_with_stack runtime fuel stack (k (inr exception))
          | Result.OutOfFuel => Result.OutOfFuel
          | Result.Unsupported message => Result.Unsupported message
          end
        | LowM.MatchTuple tuple k =>
          match tuple with
          | Value.Tuple fields => eval_with_stack runtime fuel stack (k fields)
          | _ => Result.Unsupported "expected a tuple"
          end
        | LowM.IfThenElse _ condition then_ else_ k =>
          match condition with
          | Value.Bool true =>
            match eval_with_stack runtime fuel stack then_ with
            | Result.Done output stack =>
              eval_with_stack runtime fuel stack (k output)
            | Result.OutOfFuel => Result.OutOfFuel
            | Result.Unsupported message => Result.Unsupported message
            end
          | Value.Bool false =>
            match eval_with_stack runtime fuel stack else_ with
            | Result.Done output stack =>
              eval_with_stack runtime fuel stack (k output)
            | Result.OutOfFuel => Result.OutOfFuel
            | Result.Unsupported message => Result.Unsupported message
            end
          | _ => Result.Unsupported "expected a boolean condition"
          end
        | LowM.Impossible _ => Result.Unsupported "impossible"
        end
      end.

    Definition eval
        (runtime : Runtime.t)
        (fuel : nat)
        (expression : M) :
        Execution.t :=
      match eval_with_stack runtime fuel Stack.empty expression with
      | Result.Done output _ => Execution.Done output
      | Result.OutOfFuel => Execution.OutOfFuel
      | Result.Unsupported message => Execution.Unsupported message
      end.
  End Evaluate.
End Translated.
