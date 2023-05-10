# Translation

In this doc we specify how the translation works and the details of
the translation together with the target language. It should proceed
by iterating over the Rust features and specifying the translation
together with one or more examples of the translation.

## A note about notation in this document
I use brackets to represent how the translation recurse, together
with an example in Rust, followed by a horizontal rule, followed
by an example in Coq. Here is an example. If there are brackets
ocurring in the expression we may use double brackets for the
translation flow to avoid confusion

```
     [a + 1]
------------------
Pure ([a] [+] [1])
```

## M - The Monad

_See: [PR 58](https://github.com/formal-land/coq-of-rust/pull/58/files#diff-7333cfd320f9b3335b66aa12653cbe8ae17310ff381a1c00d5c101f8ac412c50)_

This is a monad to represent various impure constructs from Rust. It will
be used in the translation.

```Coq
Module M.
  (** Monad for impure Rust code. The parameter [R] is for the type of the
      returned value in a block. *)
  Inductive t (R A : Set) : Set :=
  | Pure : A -> t R A
  | Bind {B : Set} : t R B -> (B -> t R A) -> t R A
  | FunctionCall : t Empty_set A -> t R A
  (** This is the Rust's `return`, not the one of the monad *)
  | Return : R -> t R A
  | Break : t R A
  | Continue : t R A
  | Panic {E : Set} : E -> t R A.
  Arguments Pure {_ _}.
  Arguments Bind {_ _ _}.
  Arguments FunctionCall {_ _}.
  Arguments Return {_ _}.
  Arguments Break {_ _}.
  Arguments Continue {_ _}.
  Arguments Panic {_ _ _}.
End M.
```

## Expressions

### Pure expressions

* TODO: 
  * [] Give an explanation of what is pure expressions, and how function calls
      may not be pure because the can panic
  * [] Get the name of the AST that we work in the translation (there are multiple
       for multiple phases.
  * [] Can we know if an expressions is pure or not from the AST?
  * [] Should we assume that all funcitions are impure (because they can panic)? By
       doing so we don't need to inspect the function body to tell if
       its pure or inpure during the translation.

Pure expressions must be wrapped in `Pure` constructor of [#M](#M)

Examples:


```
  [1]
------
Pure 1
```

```
   [if cond { then_body } else { else_body }]
-------------------------------------------------
Pure (if [cond] then [then_body] else [else_body])
```

## Function calls

```
  [f(a, b)]
-------------
 f(|[a] [b]|)
```

Where `f(| ... |)` is a notation in Coq.
_See [PR 58](https://github.com/formal-land/coq-of-rust/pull/58/files#diff-7333cfd320f9b3335b66aa12653cbe8ae17310ff381a1c00d5c101f8ac412c50R111)_

