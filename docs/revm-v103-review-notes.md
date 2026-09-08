# Revm v103 Upgrade Notes

These notes describe conventions for the Revm v103 upgrade work. They are meant
to keep small compile slices consistent and to avoid repeating review issues.

## Scope and semantics

Do not change semantics only to make a proof compile. If a semantic change is
really needed, make it explicit and keep it separate from routine compile-slice
repairs.

Do not invent translated Rust bodies in links files. Links files should connect
existing translated definitions to Rocq link structures. If a translated function
or method no longer exists, remove the stale link or move it to the new owner
instead of adding a compatibility wrapper.

Do not add local fake `PolymorphicFunction.t` definitions, `LowM.Pure (inl ...)`
bodies, or `M.impossible "wrong number of arguments"` stubs to force compilation.

For new standard-library or link obligations, an `Admitted` can be better than
changing definitions, as long as it does not break proofs that worked before.

## Translated files

Do not edit translated generated Rocq files by hand to make a proof pass. Prefer
fixing the link layer, the simulate layer, or the translation step.

Generated code can expose Rust field names while Rocq records use escaped field
names. For example, a Rust field such as `Range.end` can appear as the field name
`"end"` in generated field access, while the Rocq record field is named `end_`
and generated record construction may use `"end_"`. In this situation, keep the
canonical generated representation coherent and add the required link-side field
access support, or fix regeneration.

When translated Rust code moves, move the corresponding links or simulate file
to the new owning crate path. When translated Rust code is removed, remove the
corresponding links or simulate file instead of keeping a stale wrapper.

## Proof style

Prefer short targeted proof scripts when they work.

For memory link proofs using interpreter halt helpers, destruct
`run_InterpreterTypes_for_WIRE` with `eqn:?`, destruct only the trait records
still needed, run `run_symbolic`, and close exposed halt obligations directly
with `eapply Impl_Interpreter.run_halt_*`.

Avoid copying `run_InterpreterTypes_for_WIRE`, destructing individual method
fields, and pre-posing halt instances when direct `eapply` works.

Avoid broad `repeat (...)` proof scripts when newer short tactics or targeted
steps work.

It is acceptable to keep targeted exposed-call closures after `run_symbolic` when
automation cannot yet infer all calls. Over time, `run_symbolic` should be
improved to handle more of these cases automatically.

Use the project convention of double-space indentation in Rocq proofs.

## Local resource limits

Reuse existing build worktrees and check free disk space and available RAM before
compiling. Run only one compiler job at a time on this laptop. Use a per-process
virtual-memory limit (for example, `ulimit -v 2097152` for 2 GiB) and a timeout
for evaluation tests, and record peak RSS. A timed-out or memory-limited test is
a failure to investigate, not a reason to remove the limit automatically.

Check binary offsets against the input length before applying `Z.to_nat` in
executable simulations. Converting a saturated 64-bit offset directly to a
unary natural can exhaust memory even when the input list has only two bytes.

## PR hygiene

Keep links, simulate, and tests layers separate unless the current change really
requires crossing layers.

If a local check finds a wider test or simulate blocker, mention it separately
instead of silently folding it into a narrow links PR.

Before staging, scan for new `Admitted`, broad `repeat (...)` scripts, and fake
links bodies.

Use `_eq` suffixes for simple helper lemmas that state exact equalities, such as
`take_pad_length_eq` or `slice_length_eq`.
