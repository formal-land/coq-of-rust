# Technical Audit and Strategic Roadmap for rocq-of-rust

**Status:** internal engineering audit<br>
**Audit date:** 2026-07-13<br>
**Repository snapshot:** <code>ebacf73cc0e95e21b422db7d0057f045bac688f5</code><br>
**REVM gitlink:** <code>v102</code>, <code>0d424ba11fd59d2a2a13988d61381e5b5cfccd22</code><br>
**Audience:** rocq-of-rust maintainers, proof engineers, and technical sponsors<br>
**Recommendation bias:** platform correctness and trustworthiness before further breadth

## 1. Executive summary

rocq-of-rust has a technically interesting and potentially valuable architecture: it translates largely unchanged Rust into an inspectable deep embedding in Rocq, recovers native Rocq types and trait structure in a separate link phase, and proves refinements to readable functional simulations. The repository demonstrates that this architecture can process unusually large, macro- and trait-heavy production code. The REVM corpus is meaningful evidence of translation scale.

It is not yet sound to present the project as a general Rust verifier or as an end-to-end verification of REVM. The current implementation contains confirmed semantic mismatches in ordinary safe Rust, silently accepts several unsupported constructs by changing their meaning, has no formal semantic relation or correctness proof connecting Rust/THIR execution to the generated <code>M</code> semantics, and relies on a large unclassified assumption surface. The REVM work is concentrated on instruction functions and contains stale signatures, admitted links, placeholder gas functions, and no proof of the transaction executor or interpreter dispatch loop.

The strongest defensible position is:

> rocq-of-rust is an inspectable Rust-to-Rocq refinement pipeline demonstrated on selected production-scale Rust, including REVM instruction code. It enables interactive proofs against maintainable functional models, but its supported Rust subset, semantic correspondence, and transitive assumptions still need to be made explicit and hardened.

That position is differentiated. Aeneas has a stronger formal translation story and more automatic functionalization; RefinedRust has a stronger foundational account of unsafe memory; Creusot, Verus, and Kani provide much better automated feedback and counterexamples. rocq-of-rust's distinctive asset is the combination of unchanged production source, a large Rocq artifact, source-correlated generated code, and an explicit refinement layer. The engineering strategy should reinforce that asset rather than compete first on general-purpose automation.

### 1.1 Headline findings

| ID | Finding | Severity | Confidence | Immediate consequence |
|---|---|---:|---:|---|
| S-01 | Unsupported syntax can fail open, including range patterns translated as wildcards | Critical | Confirmed | A compiling Rocq artifact can denote different behavior from Rust |
| S-02 | Signed division/remainder and their mandatory panic cases are modeled incorrectly | Critical | Confirmed by differential evaluation | Functional correctness and panic-freedom claims can both be false |
| S-03 | Oversized shifts disagree with both audited checked and unchecked configurations | High | Confirmed by differential evaluation | Integer proofs can establish the wrong result |
| S-04 | Break values and loop labels are discarded | High | Confirmed from source and generated example | Value-returning and labeled loops are mistranslated |
| S-05 | Implicit <code>Drop</code> is absent | High | Confirmed from the repository's own example | RAII, cleanup, guards, and destructor side effects are omitted |
| S-06 | Index and subpointer failure behavior diverges from Rust; some invalid writes silently succeed | High | Confirmed by Rocq evaluation | Bounds/panic and reference proofs can follow impossible paths |
| S-07 | Typed integers are unconstrained mathematical integers; pointer width is fixed at 64 bits | High | Confirmed design limitation | Theorems quantify over non-Rust states unless validity is explicit |
| S-08 | Executable simulation of loops is an unconstrained <code>Parameter</code> | High | Confirmed coverage gap | Loop-containing linked programs cannot be reduced faithfully |
| S-09 | Panic maps to an unconstrained <code>Impossible</code> run rule | High | Confirmed trust risk | A closed simulation proof alone does not establish panic-freedom |
| T-01 | There is no machine-readable assumption or proof-coverage closure | High | Confirmed | <code>Qed</code> is easily overinterpreted |
| R-01 | REVM is broadly translated but narrowly simulated and not verified end to end | Critical | Confirmed scope issue | “REVM verified” is not an accurate current claim |
| R-02 | REVM gas simulations include zero placeholders and stale admitted interfaces | Critical | Confirmed EVM-correctness defect | Gas, OOG, refund, and fork correctness are unsupported |
| E-01 | The checked-in CI calls a deleted <code>jinja</code> target; a documented REVM test target fails | High | Reproduced | The current repository is not green |

### 1.2 Overall maturity scorecard

The scores below are judgment calls, not formal metrics. They summarize the evidence in this audit on a five-point scale.

| Dimension | Score | Assessment |
|---|---:|---|
| Architectural separation | 4/5 | Deep embedding, links, and simulations are cleanly separated and amenable to incremental hardening |
| Generated artifact readability | 4/5 | Source snippets and names are retained; generated code is verbose but inspectable |
| Translation scale | 4/5 | Standard-library, REVM, ruint, Alloy, Sui, Solana, and Bytes artifacts are substantial |
| Semantic faithfulness | 1/5 | Confirmed mismatches affect basic arithmetic, patterns, control flow, drops, and bounds |
| Trusted-computing-base transparency | 1/5 | Parameters, axioms, and admits are numerous and not reported per theorem |
| Rust language coverage | 2/5 | A large practical fragment translates, but unsupported behavior is neither documented nor safely rejected |
| Proof automation | 2/5 | Tactics and the link plugin help, but much linking/simulation work is manual and brittle |
| Rust-side testing | 1/5 | Workspace tests pass because there are zero tests; snapshots are the primary frontend regression mechanism |
| Rocq/REVM testing | 2/5 | There are useful computational smoke goals, but no native differential or Ethereum state-test oracle |
| REVM instruction modeling | 3/5 | Many instruction bodies have useful functional simulations and local equivalence proofs |
| REVM end-to-end verification | 1/5 | No complete gas model, dispatch loop, concrete host/journal closure, handler, or transaction theorem |
| Product usability | 1.5/5 | Nightly coupling, monolithic builds, sparse diagnostics, broken options, and limited documentation impede adoption |

### 1.3 Top-level recommendation

Do not prioritize translating additional ecosystems until the supported subset is fail-closed and the semantic core has a conformance suite. The first milestone should make it impossible to consume a proof artifact without knowing whether translation encountered an unsupported construct and what assumptions remain in the final theorem. The second should repair ordinary safe-Rust semantics and state a precise correspondence theorem target. Only then should the project extend the REVM proof upward from instruction functions.

## 2. Scope, method, and terminology

### 2.1 Snapshot and worktree

The audit uses the tracked parent repository at commit <code>ebacf73cc</code>. Several submodules were dirty before the report was written. Counts therefore use <code>git ls-files</code> in the parent repository and the recorded gitlinks, not untracked generated files inside submodules. Build artifacts such as <code>.vo</code>, <code>.glob</code>, and <code>.aux</code> are excluded from coverage counts.

The checked-in REVM target is the <code>v102</code> gitlink. The document [revm-v103-review-notes.md](revm-v103-review-notes.md) describes upgrade conventions; it does not make the current tree a v103 translation. Current external comparisons were checked on 2026-07-13. Upstream REVM showed v111 / revm 40.0.2 as its latest GitHub Release; the repository can contain newer tags.

### 2.2 Evidence classes

Each important finding is assigned one of these classes:

- **Confirmed defect:** the translator or Rocq model produces behavior different from compiled Rust for a supported-looking input, demonstrated by code inspection and usually a minimal reproducer.
- **Semantic limitation:** behavior is deliberately absent or abstract. It becomes a defect only when a theorem or project claim exceeds the documented preconditions.
- **Trust assumption:** a theorem depends on a <code>Parameter</code>, <code>Axiom</code>, <code>Admitted</code> declaration, compiler assumption, or handwritten specification.
- **Coverage gap:** no relevant link, simulation, proof, or validation exists.
- **Engineering defect:** build, CLI, reproducibility, documentation, or testing behavior is broken independently of semantic correctness.
- **Strategic opportunity:** a feature or positioning change that would materially improve the project but is not required to repair an incorrect claim.

Severity measures the risk of using a result as evidence about the original Rust program. Confidence measures the strength of the audit evidence. An <code>Admitted</code> declaration is not automatically a bug: it can be an honest placeholder. It is a trust gap whose importance depends on whether a final theorem uses it.

### 2.3 What “verified” must mean

The repository contains several distinct achievements that should not be conflated:

1. Rust source was accepted by rustc.
2. rocq-of-rust emitted a Rocq term.
3. the generated term compiled in Rocq.
4. a link proof assigned native Rocq types and resolved calls.
5. a functional simulation was defined.
6. an equivalence theorem was closed with <code>Qed</code>.
7. the theorem's transitive assumptions were audited.
8. the functional simulation was related to an independent specification.
9. an end-to-end entrypoint, rather than a helper function, was covered.

Levels 6–7 establish a local refinement result relative to disclosed assumptions; level 8 connects it to independently intended behavior; level 9 is additionally required for an end-to-end implementation claim. A generated file compiling establishes neither semantic preservation nor correctness of the Rust. A local <code>Qed</code> establishes its proposition relative to every axiom in its dependency closure.

### 2.4 Audit limitations

This was a repository and semantics audit, not a completed formal metaproof of the tool. It combined source inspection, tracked-artifact inventory, selected builds, <code>Print Assumptions</code>, and minimal native-Rust/Rocq reproducers. It did not manually review every generated declaration, execute the full Ethereum test corpus, benchmark proof productivity against every alternative, or validate binary-code correspondence. The full Rocq build was not pursued past the reproduced protected host-target failure. External comparison uses primary project material but cannot substitute for joint benchmark studies.

Accordingly, “no issue found” in an area means only that this audit did not establish one. Confirmed counterexamples are sufficient to refute general semantic-faithfulness claims; their absence elsewhere is not proof of correctness.

## 3. Architecture

### 3.1 Pipeline

The Cargo integration installs <code>rocq-of-rust-rustc</code> as a <code>RUSTC_WRAPPER</code> and runs translation during rustc callbacks ([cargo-rocq-of-rust.rs](../lib/src/bin/cargo-rocq-of-rust.rs#L10-L37), [callbacks.rs](../lib/src/callbacks.rs#L32-L84)). Top-level declarations use HIR and rustc queries; function bodies and typed expressions use THIR. The translator constructs its own Rust-side AST for types, patterns, expressions, and top-level items, then pretty-prints Rocq.

~~~mermaid
flowchart LR
    A[Rust crate] --> B[rustc HIR/THIR and type context]
    B --> C[rocq-of-rust internal AST]
    C --> D[Generated deep embedding: M]
    D --> E[Links: native types and resolved calls]
    E --> F[Functional simulations]
    F --> G[Equivalence and specification proofs]
    H[External Rust/std/dependency models] --> E
    I[Independent application specification] --> G
~~~

Generated functions have a uniform interface over lists of generic constants, generic types, and values and return the monad <code>M</code>. This sacrifices static typing in the generated layer, but gives the frontend a simple target and keeps most rustc-specific complexity outside the proof model.

### 3.2 The deep embedding

[M.v](../RocqOfRust/M.v) defines:

- an abstract <code>Ty.t</code>;
- structural <code>Value.t</code> constructors for booleans, integers, characters, strings, tuples, arrays, structs, pointers, closures, errors, and uninitialized locals;
- pointer paths and primitive operations for allocation, reads, writes, subpointers, functions, associated functions, and trait methods;
- <code>LowM</code>, an effect syntax for calls, lets, loops, matching, conditionals, and impossible states;
- control-flow exceptions for return, continue, break, and failed pattern branches.

This is a useful verification boundary. Effects remain explicit, generated programs remain close to the source control flow, and the semantics can be interpreted relationally without trusting an extracted evaluator. It also makes semantic omissions very consequential: every Rust behavior that does not appear in <code>M</code> must be rejected, separately modeled, or made an explicit theorem precondition.

### 3.3 Links

[links/M.v](../RocqOfRust/links/M.v) introduces a <code>Link</code> class associating a native Rocq type with its abstract Rust type and encoding function. It converts the untyped generated terms into a typed <code>LinkM</code> representation and resolves functions, methods, associated types, primitive operations, and subpointers using proof objects and typeclass search.

The new Rocq link plugin is an important improvement. It removes repetitive record/enum boilerplate while leaving generated declarations kernel-checked. That direction should continue: automate construction of proof obligations, but keep the resulting object inspectable and the obligation status machine-readable.

### 3.4 Simulations and proofs

[simulate/M.v](../RocqOfRust/simulate/M.v) uses a heterogeneous stack and typed reference projections/injections to execute linked terms. Application-specific files define idiomatic functions and prove that evaluating a linked translation produces the same result and state.

This separation supports maintainable specifications. A 300-line generated instruction can refine to a short functional definition. Proof engineers reason mostly about the native representation rather than raw <code>Value.t</code>. It also creates three independent correctness obligations:

1. Rust/THIR to <code>M</code> is faithful.
2. <code>M</code> to linked <code>LinkM</code> is faithful.
3. linked execution refines the handwritten simulation.

The repository works extensively on obligations 2 and 3. It does not yet establish obligation 1, and several findings below show that it currently fails.

### 3.5 Trusted computing base

| Component | Current role | Trust status | Desired status |
|---|---|---|---|
| rustc and pinned nightly | Supplies HIR/THIR, types, resolved definitions | Trusted external compiler internals | Record version/target/options in every artifact; test upgrades differentially |
| Rust translator | Selects and lowers source semantics | Fully trusted; no correctness proof | Fail closed, conformance-tested, then prove an overlapping-subset correspondence |
| <code>M</code> semantics | Defines what generated programs mean | Kernel-checked definitions plus Parameters | Explicit supported subset and documented correspondence to Rust/MiniRust |
| Link layer | Recovers native types/calls | Mix of definitions, proofs, axioms, admits | Generated obligations with per-item status and assumption closure |
| Simulation functions | Human-authored intended behavior | Kernel-checked definitions | Validate independently, not only against the same translation |
| Equivalence proofs | Relate linked code and simulation | Kernel-checked proof terms | CI checks <code>Print Assumptions</code> policy |
| Tactics and link plugin | Build terms/declarations | Tactics are logically untrusted when they only construct checked proof terms; native plugins can also declare assumptions | Audit generated declarations and protected-theorem closure; keep output deterministic; forbid hidden axioms |
| Rocq kernel | Final checker | Trusted | Pin and reproduce; use <code>coqchk</code> for releases |
| Rocq libraries and dependencies | Definitions, proofs, tactics, notation | Kernel-checked artifacts whose transitive logical assumptions remain material | Pin versions and include their assumptions in protected closure |
| Independent Rust/EVM specification | Establishes intended application behavior | Mostly absent | MiniRust/Rust conformance for language; EELS/EEST or formal EVM for REVM |

The most important architectural observation is that Rocq's kernel protects the internal consistency of stated theorems, not the correctness of the encoding. If unsupported Rust becomes an unconditional wildcard, the kernel correctly proves facts about the wrong program.

## 4. Repository inventory and current checks

### 4.1 Tracked inventory

| Item | Files | Lines where applicable |
|---|---:|---:|
| Rust translator and CLI source | 20 | 7,943 |
| Rocq semantic core | 5 | 1,608 |
| Current generated Rocq translations | 1,164 | 3,342,557 |
| Authored links | 224 | 27,931 |
| Authored simulations, including legacy | 190 | 40,872 |
| Authored files under <code>proofs/</code> | 11 | 4,701 |
| All tracked Rocq <code>.v</code> files | 1,885 | 4,894,087 |
| Rust example inputs used for snapshots | 267 | — |
| Active non-comment build-blacklist entries | 19 | — |
| Tracked REVM Rust mirrors | 145 | — |
| Tracked REVM Rocq files | 356 | 443,203 |

These are scale metrics, not verification metrics. In particular, most large generated files contain axiomatized registration instances and are not handwritten proof coverage.

### 4.2 Executed checks

The following commands were executed on the audited snapshot:

| Check | Result | Interpretation |
|---|---|---|
| <code>cargo fmt --all --check</code> | Pass | Rust formatting is clean |
| <code>cargo clippy --workspace --all-targets --all-features -- -D warnings</code> | Pass, with a Cargo profile-location warning | The Rust implementation is warning-clean under Clippy |
| <code>cargo test --workspace --no-fail-fast</code> | Pass, **zero tests** in all four targets | This is not meaningful behavioral coverage |
| <code>make -C RocqOfRust plugin-inline-print-check</code> | Pass | The plugin's checked print fixture is stable |
| <code>make -C RocqOfRust -n jinja</code> | Fail: no rule for <code>jinja</code> | The current CI invokes a deleted target |
| <code>make revm/revm_interpreter/tests/host.vo -j1</code> | Fail at line 123: missing <code>Link aliases.B256.t</code> | The documented REVM test/build surface is not green |
| <code>Print Assumptions add_eq</code> | Reports many axioms | A representative <code>Qed</code> theorem is conditional |

The host failure is reproducible in [tests/host.v](../RocqOfRust/revm/revm_interpreter/tests/host.v#L123). A complete <code>make</code> cannot succeed while that target is in the generated Rocq makefile. This audit did not wait for an otherwise redundant full build after reproducing the blocking target.

### 4.3 Existing strengths

- CI is configured/intended to regenerate examples, core/alloc, ten selected REVM crates, ruint, Alloy primitives, Bytes, Move/Sui, Solana Token, and parts of the Solana SDK, then check the diff and compile Rocq; E-01 prevents the checked-in workflow from completing as written.
- Generated files retain source snippets and stable-enough names, which is valuable when reviewing proof failures.
- The repository has moved repetitive linking into a plugin and has explicit review guidance against fake link bodies.
- REVM computational tests use <code>vm_compute</code>, showing that many functional simulations are executable.
- The project is willing to preserve explicit admits instead of disguising missing proofs. The next step is to classify them automatically.

## 5. Semantic correctness audit

### 5.1 S-01 — unsupported constructs fail open

**Severity:** Critical<br>
**Confidence:** Confirmed<br>
**Affected claims:** all source-to-Rocq correspondence and all downstream theorems using affected items

Unsupported constant, range, never, error, and dereference patterns are converted into <code>Pattern::Wild</code> after only a warning ([thir_pattern.rs](../lib/src/thir_pattern.rs#L113-L192), [thir_pattern.rs](../lib/src/thir_pattern.rs#L225-L254)). A wildcard emits no test. The first such match arm can therefore accept every value.

A minimal source function:

~~~rust
fn classify(x: u8) -> u8 {
    match x {
        0..=5 => 1,
        _ => 2,
    }
}
~~~

was translated successfully. The command emitted “Ranges in patterns are not yet supported,” but the generated match contained two unconditional arms. Native Rust returned 2 for input 10; the Rocq match selects the first arm and returns 1. This is a direct semantic miscompile.

Other paths replace unsupported expressions with comments around unit, including <code>LoopMatch</code>, unexpected THIR <code>Let</code>, and unknown zero-sized/function-parent cases ([thir_expression.rs](../lib/src/thir_expression.rs#L683-L700), [thir_expression.rs](../lib/src/thir_expression.rs#L1271-L1292)). Unsupported literals and inline assembly are global unconstrained parameters in [RocqOfRust.v](../RocqOfRust/RocqOfRust.v#L38-L43).

This policy is unsafe for verification. An ordinary compiler may recover from unsupported syntax for diagnostics; a verifier cannot silently substitute a weaker program.

**Required remediation**

1. Make strict translation the default.
2. Assign every lowered node a status: exact, modeled by explicit contract, unsupported, or intentionally opaque.
3. If any unsupported node is reachable from an emitted item, fail with a structured diagnostic and source span.
4. Provide an explicit <code>--allow-unsupported</code> exploration mode only if every resulting definition is marked tainted and cannot be imported into a release proof without an override.
5. Add negative tests asserting that unsupported constructs fail; never snapshot their weakened output as success.

**Acceptance criterion:** the complete example suite and REVM translation produce a machine-readable manifest with zero unclassified nodes, and injected unsupported range/never/deref cases fail CI.

### 5.2 S-02 — integer division and remainder are not Rust semantics

**Severity:** Critical<br>
**Confidence:** Confirmed with native Rust and Rocq evaluation<br>
**Affected claims:** arithmetic correctness, panic-freedom, indexing/gas helpers using primitive integer division

The translator maps THIR division and remainder to <code>BinOp.Wrap.div</code> and <code>BinOp.Wrap.rem</code> ([thir_expression.rs](../lib/src/thir_expression.rs#L15-L25)). The deep library defines those using <code>Z.div</code> and <code>Z.modulo</code>, normalizing only afterward ([lib.v](../RocqOfRust/lib/lib.v#L224-L257)). The typed simulation library duplicates the same definitions ([simulate/lib.v](../RocqOfRust/lib/simulate/lib.v#L42-L71)).

Differential results:

| Expression | Rust debug | Rust release-like | Rocq model |
|---|---:|---:|---:|
| <code>-5i8 / 2</code> | -2 | -2 | -3 |
| <code>-5i8 % 2</code> | -1 | -1 | 1 |
| <code>1u8 / 0</code> | panic | panic | 0 |
| <code>i8::MIN / -1</code> | panic | panic | -128 |
| <code>i8::MIN % -1</code> | panic | panic | 0 |

Primitive Rust integer division truncates toward zero, while the chosen Rocq operations use Euclidean division. Rust also mandates panic for a zero divisor and for signed minimum divided or remaindered by -1, regardless of overflow-check configuration. Overloaded <code>/</code> and <code>%</code> follow their trait implementation rather than necessarily these primitive rules. The [Rust Reference arithmetic operator table](https://doc.rust-lang.org/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators) documents the primitive cases.

The model's comment that operators represent release mode is insufficient: in the audited/common rustc configuration, disabling overflow checks makes add/sub/mul overflow wrap, but a Cargo release profile may enable checks and the language does not define “release” as one semantic profile. In every profile, division's mandatory panics remain.

**Required remediation**

- Separate ordinary Rust operators from <code>wrapping_*</code>, <code>checked_*</code>, <code>saturating_*</code>, and <code>overflowing_*</code> APIs.
- Use truncation-toward-zero quotient and remainder, for example validated <code>Z.quot</code>/<code>Z.rem</code>-based definitions.
- Route zero and signed-minimum/-1 through an explicit panic result.
- Derive overflow-check behavior from the rustc session and record it in artifact metadata.
- Differentially test every integer kind at minimum, maximum, -1, 0, 1, width boundaries, and random values.

**Acceptance criterion:** an exhaustive test over all <code>u8</code>/<code>i8</code> operand pairs and property tests for wider kinds agree with native Rust for result and panic status in both overflow profiles.

### 5.3 S-03 — shift semantics disagree with both audited configurations

**Severity:** High<br>
**Confidence:** Confirmed with differential evaluation

<code>BinOp.Wrap.shl</code> and <code>shr</code> apply <code>Z.shiftl</code>/<code>Z.shiftr</code> to the full shift count and normalize the result afterward. For <code>1u8 &lt;&lt; 8</code> and <code>1u8 &gt;&gt; 8</code>:

- debug Rust panics because the shift count overflows the type width;
- with the audited x86_64 rustc and <code>-C overflow-checks=off -C opt-level=3</code>, the count was effectively masked and both expressions returned 1; this is an observed compiler/configuration result, not a target-independent Rust-language guarantee;
- the Rocq model computes the mathematical shift and returns 0.

Negative right-hand values are legal source operands when the right-hand type is signed; they are overflow conditions. In the current model they instead make <code>Z.shiftl</code>/<code>Z.shiftr</code> reverse direction. The typed simulation also requires the left and right operands to have the same <code>IntegerKind</code> ([simulate/lib.v](../RocqOfRust/lib/simulate/lib.v#L67-L71)), although Rust permits combinations such as <code>u8 &lt;&lt; u32</code>. The deep model ignores the right-hand kind.

**Required remediation:** parameterize primitive operators by left-hand width, both operand kinds, and the recorded overflow configuration; implement the documented checked/unchecked operation policy rather than assuming a universal release result; require validity of typed integer inputs. Tests must cover every right-hand primitive integer kind, negative signed counts, boundary counts, and exact compiler/target/profile identity.

### 5.4 S-04 — break payloads and labels are discarded

**Severity:** High<br>
**Confidence:** Confirmed from translator source and tracked generated examples

rustc THIR represents <code>Break</code> with both a target label and optional value. The translator matches <code>ExprKind::Break { .. }</code> and emits a payload-free control-flow marker; continue labels are also ignored ([thir_expression.rs](../lib/src/thir_expression.rs#L859-L875)). <code>Exception::Break</code> and <code>Continue</code> carry neither payload nor loop identity, and <code>catch_break</code> always returns unit ([M.v](../RocqOfRust/M.v#L449-L483), [M.v](../RocqOfRust/M.v#L853-L881)).

The tracked example [loop_returning_from_loops.v](../RocqOfRust/examples/default/examples/rust_book/flow_of_control/loop_returning_from_loops.v#L19-L65) translates <code>break counter * 2</code> into <code>M.break</code> without translating <code>counter * 2</code>. The result is then used as an <code>i32</code>. The labeled-loop example similarly turns <code>break 'outer</code> into a break caught by the inner loop.

**Required remediation:** control-flow exceptions must carry a loop identifier and break value. The loop semantics must catch only its own identifier and return the payload at the loop's result type. Add nested labeled break/continue and value-returning loop conformance tests.

### 5.5 S-05 — implicit Drop and cleanup are missing

**Severity:** High<br>
**Confidence:** Confirmed<br>
**Affected code:** any type with observable destructor behavior, guards, locks, reference counts, resource wrappers, or unsafe invariants

The translator strips THIR scope nodes to their body ([thir_expression.rs](../lib/src/thir_expression.rs#L505-L506)). There is no representation of implicit destructor execution or unwind cleanup. The repository's own Rust Drop example declares four values with observable destructors. Its generated translation contains the explicit <code>core::mem::drop(_a)</code> call, but no automatic reverse-order drops for the other values ([drop.rs](../examples/rust_book/traits/drop.rs), [drop.v](../RocqOfRust/examples/default/examples/rust_book/traits/drop.v#L173-L304)).

This is not merely memory deallocation. Safe Rust permits arbitrary observable code in <code>Drop::drop</code>. The [Rust Reference destructor rules](https://doc.rust-lang.org/reference/destructors.html) define drop scopes and reverse declaration order. Omitting them changes valid safe programs.

**Required remediation:** use MIR drop elaboration or supplement THIR with MIR cleanup/drop information while retaining THIR source mapping. Until then, strict mode should reject items whose reachable types have nontrivial drop glue, except where a proved erasure theorem shows the destructor is observationally irrelevant.

### 5.6 S-06 — indexing and pointer-path failure are inconsistent

**Severity:** High<br>
**Confidence:** Confirmed by Rocq evaluation

<code>Value.read_index</code> converts a <code>Z</code> index with <code>Z.to_nat</code> without a nonnegative check ([M.v](../RocqOfRust/M.v#L272-L304)). Therefore -1 aliases element zero. <code>write_index</code> checks array bounds but not tuple or struct-tuple bounds; an out-of-bounds write returns <code>Some</code> of the unchanged value. Record writes return <code>Some</code> even if the field is absent ([M.v](../RocqOfRust/M.v#L306-L344)). This contradicts the function's comment that invalid shapes return <code>None</code>.

Confirmed evaluations include:

- array read at -1 returns element zero;
- tuple write at -1 updates element zero;
- tuple write at index 9 returns <code>Some</code> unchanged;
- absent record field write returns <code>Some</code> unchanged.

Positive safe-Rust array out-of-bounds becomes <code>None</code>, which the simulation maps to <code>BreakMatch</code>, not a Rust bounds panic. That can incorrectly fall through to a later match arm.

**Required remediation**

- Validate <code>0 &lt;= index &lt; length</code> before conversion.
- Make structural projection helpers return a typed failure cause.
- Use <code>PatternMismatch</code> only for enum/pattern selection; safe dynamic array/slice out-of-bounds becomes the modeled panic/abort; impossible tuple/field indices become an internal invariant failure; unsafe invalid pointers become UB/precondition failures.
- Prove read-after-write, disjoint-path noninterference, and failure consistency for pointer paths.

### 5.7 S-07 — integer validity is external to the type

**Severity:** High<br>
**Class:** modeling limitation<br>
**Confidence:** Confirmed

<code>Value.Integer</code> accepts any <code>Z</code>. The typed <code>Integer.t kind</code> is a record containing only <code>value : Z</code>, and every integer value receives an <code>OfValue</code> instance ([M.v](../RocqOfRust/M.v#L232-L255), [links/M.v](../RocqOfRust/links/M.v#L195-L301)). <code>Integer.Valid</code> exists in a proof library but is not embedded in the linked type or ordinary function runner.

Consequently, theorem quantification over <code>u8</code> also includes -1 and 1,000; <code>usize</code> includes negative values. This is a reasonable proof convenience only if every externally reachable theorem adds and preserves validity invariants. Current statements often do not, which activates otherwise “unreachable” negative-index and overflow behavior.

The minimum, maximum, and normalization for <code>usize</code>/<code>isize</code> are also hard-coded to 64 bits ([lib.v](../RocqOfRust/lib/lib.v#L63-L112)). rustc supports other targets.

**Options**

1. Make <code>Integer.t</code> a bounded dependent record and pay the proof overhead once in shared lemmas.
2. Keep an unbounded representation but include validity in <code>Link</code>, runner inputs, outputs, and every primitive preservation theorem.
3. Use a two-level representation: bounded public values and unbounded internal arithmetic with explicit normalization proofs.

The target pointer width, endianness where relevant, overflow-check mode, panic strategy, and rustc version should be extracted from the compilation session and stored in generated metadata.

### 5.8 S-08 — loops have no executable simulation

**Severity:** High<br>
**Class:** coverage gap<br>
**Confidence:** Confirmed

<code>SimulateM.TodoLoop</code> is an unconstrained <code>Parameter</code>; evaluating any linked loop returns it ([simulate/M.v](../RocqOfRust/simulate/M.v#L341-L417)). The link layer has a structural loop rule, but it does not provide iterative operational semantics. Generated REVM code contains loops, so this is not confined to tutorial examples.

An inductive relational semantics is the safest first implementation. A terminating <code>loop</code> executes one body iteration; normal completion or a matching continue recurs, a matching break terminates with its payload, and return/panic/abort propagate. Labels ensure only the targeted loop handles an effect. A coinductive divergence judgment—or absence of a terminating derivation for partial correctness—handles infinite execution. An executable fuelled evaluator can support tests, but out-of-fuel is evaluator metadata rather than successful program behavior.

### 5.9 S-09 — panic is erased into an unconstrained rule

**Severity:** High<br>
**Class:** semantic/trust risk<br>
**Confidence:** Confirmed and documented in source

<code>M.panic</code> is defined as <code>impossible</code>, with a comment that only panic-free programs are considered ([M.v](../RocqOfRust/M.v#L774-L781)). More seriously, <code>Run.Impossible</code> has no unreachability premise and derives the run judgment for any output ([links/M.v](../RocqOfRust/links/M.v#L1014-L1015)). A reachable panic/Impossible branch can therefore close a simulation relation without proving that the branch is unreachable. A successful simulation/equivalence proof alone is not evidence of panic-freedom.

Reserve <code>Impossible</code> for compiler invariants and require an explicit <code>False</code>/unreachability premise at its semantic rule. Represent Rust panic and abort as typed outcomes and prove that protected entrypoints cannot produce them. The semantics must also distinguish abort from unwind and execute supported cleanup. Division and indexing currently omit mandatory panic sources, compounding the issue.

### 5.10 S-10 — unsafe memory and several safe primitives are incomplete

**Severity:** High<br>
**Class:** scope-dependent semantic limitation<br>
**Confidence:** Confirmed limitation

The structural pointer model is productive for borrow-checked safe code, but it does not encode byte-level layout, provenance, alignment, padding/uninitialized data, aliasing validity, volatile access, atomics, or data races. Those are principally unsafe/low-level boundaries.

A separate assumption surface affects ordinary safe Rust: integer casts, record update, unevaluated constants, and slice-rest projections can appear in safe code. Casts, pointer-coercion intrinsics, record update, unevaluated constants, slice-rest projections, and yield remain Parameters ([M.v](../RocqOfRust/M.v#L979-L1060)); integer-cast correctness lemmas are admitted ([links/M.v](../RocqOfRust/links/M.v#L1558-L1575)). A protected theorem using one of these has a semantic trust dependency even if the original Rust contains no <code>unsafe</code> block.

The project should not attempt a full Rust memory model immediately. It should:

- state the safe subset whose borrow-checker guarantees justify the structural model;
- reject or contract every unsafe operation crossing that boundary;
- give external primitives explicit pre/postconditions;
- align the longer-term operational semantics with [MiniRust](https://github.com/minirust/minirust), which focuses on exact evaluation order, representation, UB, and a byte-oriented memory interface, while noting that MiniRust is incomplete and does not define Rust-to-MiniRust lowering.

For foundational unsafe verification, integration or shared models with [RefinedRust](https://plv.mpi-sws.org/refinedrust/) or VeriFast are more credible than inventing a second separation-logic memory model inside the current pipeline.

### 5.11 Other language limitations

| Area | Current behavior | Risk |
|---|---|---|
| Floats | Deep values are strings; typed <code>F64</code> is abstract | No IEEE-754 executable semantics or correctness proofs |
| Dynamic traits | Partial type representation; REVM historically missed tx-info methods | Blocks common production APIs and concrete dispatch reasoning |
| Inline assembly | Unconstrained global value | No behavioral claim is possible |
| Async/generators/yield | Parameterized or incomplete | Control-flow/state-machine semantics absent |
| Associated types | Some concrete cases warn or become unknown | Type resolution can become an admitted bridge |
| Const evaluation | Unevaluated constants are abstract | Compile-time behavior and target-dependent constants may diverge |
| Raw pointers | Reused structural reference model | No provenance/UB contract |
| Concurrency/atomics | No memory/concurrency semantics | Out of supported scope |

These need not all be implemented. A public supported-subset matrix and strict diagnostics are higher value than nominally accepting syntax through axioms.

## 6. Proof status and trusted-assumption audit

### 6.1 Repository-wide syntactic inventory

The following counts use mutually exclusive categories over tracked Rocq files. “Generated” means that the first line is exactly <code>(* Generated by rocq-of-rust *)</code>. “Links,” “simulations,” and “proofs” are authored files under the corresponding path components. Historical files without the current generator header remain in “other.”

| Layer | Files | Lines | <code>Admitted.</code> | <code>Axiom</code> | <code>Parameter</code> |
|---|---:|---:|---:|---:|---:|
| Semantic core | 5 | 1,608 | 0 | 3 | 24 |
| Current generated translations | 1,164 | 3,342,557 | 12,476 | 16,320 | 1,147 |
| Links | 224 | 27,931 | 381 | 3 | 92 |
| Simulations, including legacy | 190 | 40,872 | 149 | 4 | 34 |
| Proofs | 11 | 4,701 | 38 | 10 | 0 |
| Other authored or historical Rocq | 291 | 1,476,418 | 1,061 | 2,658 | 4 |
| **Total** | **1,885** | **4,894,087** | **14,105** | **18,998** | **1,301** |

There are also 227 executable <code>admit.</code> tactic lines: 125 in links, 12 in simulations, and 90 in proofs. Searching only for the terminating declaration <code>Admitted.</code> therefore understates unfinished proof steps.

These figures need careful interpretation:

- they count source lines, not distinct kernel constants;
- they are lexical source counts rather than Rocq-parser output and can include declaration-shaped text inside comments;
- a generated axiom may be registration boilerplate or a material behavioral assumption;
- a <code>Parameter</code> may intentionally define an abstract interface, such as an external host;
- an admitted local helper is much more consequential if every deliverable theorem imports it;
- the 1.47-million-line “other” category is almost entirely the historical <code>legacy/</code> tree;
- a completed proof can depend transitively on assumptions without containing any admit itself.

The counts are therefore an inventory and a warning, not a proof-quality score. They show why a theorem-level closure is necessary.

### 6.2 What a current <code>Qed</code> establishes

A representative query, <code>Print Assumptions add_eq</code>, reported a broad dependency set including wrapping-integer equalities, tuple and path typing, conversion functions, trait registries, associated-type equalities, and <code>SimulateM.TodoLoop</code>. This does not invalidate the theorem. It means the theorem is conditional on those declarations.

The proper unit of reporting is:

~~~text
Rust item
  -> generated definition and diagnostics
  -> link instance and assumptions
  -> simulation theorem and assumptions
  -> application specification theorem and assumptions
~~~

A “green” theorem should have an allowlisted logical closure. Permissible classes may include:

- standard logical axioms explicitly adopted by policy;
- abstract environment interfaces that occur as quantified hypotheses;
- cryptographic primitives with named external specifications;
- a target model with recorded target triple and compiler configuration.

The Rocq kernel, compiler, plugin binaries, and tool versions do not appear in <code>Print Assumptions</code>; record them separately in the build/TCB manifest.

It should not silently include:

- a semantic operation used by the program but left unconstrained;
- an admitted equality between the generated body and the link;
- a placeholder simulation returning zero;
- a theorem about a stale function signature;
- a fail-open translation diagnostic.

### 6.3 Required proof manifest

Every generated crate and every published theorem should receive a machine-readable manifest. A minimal schema is:

~~~yaml
schema_version: 1
source:
  repository: https://github.com/bluealloy/revm
  revision: 0d424ba11fd59d2a2a13988d61381e5b5cfccd22
  crate: revm_interpreter
  rustc: nightly-2025-12-07
  target: x86_64-unknown-linux-gnu
  overflow_checks: true
  panic_strategy: unwind
translation:
  rocq_of_rust_revision: ebacf73cc0e95e21b422db7d0057f045bac688f5
  mode: strict
  warnings: 0
  unsupported_constructs: []
artifact:
  generated_definition: revm_interpreter.instructions.arithmetic.add
  link_instance: Impl_add.run
  simulation_theorem: add_eq
status:
  translated: true
  linked: true
  simulated: true
  proof_closed: true
  independent_specification: false
assumptions:
  allowed: []
  unresolved:
    - name: Impl_Uint.wrapping_add_eq
      class: dependency_contract
      owner: ruint
      issue: 123
~~~

CI should reject:

- an unknown manifest version;
- a diagnostic not explicitly allowlisted;
- a missing source hash or target configuration;
- a new assumption in a protected theorem;
- a claimed status whose named artifact is absent;
- an item manifest that refers to a source signature different from the generated signature.

The implementation can start as a script around Rocq's <code>Print Assumptions</code> output and the translator's item map. It does not need a new proof framework.

### 6.4 Trust-reduction priorities

1. **Stop semantic weakening.** A proof over a rejected input is unavailable; a proof over silently changed input is misleading.
2. **Classify assumptions by role.** Separate logical axiom, environment contract, dependency contract, type-registration bridge, semantic primitive, and unfinished proof.
3. **Protect named deliverables.** Apply zero-new-assumption budgets to a small set of theorems first.
4. **Replace behavioral axioms with hypotheses.** A theorem parameterized by a host contract is clearer than a global axiom implementing that host.
5. **Check releases independently.** Run <code>coqchk</code> over release artifacts and archive the resulting manifest.
6. **Prove preservation lemmas once.** Integer validity, pointer-path laws, and primitive panic behavior should be reusable core lemmas rather than repeated admits.

The goal is not “zero axioms everywhere.” Real systems require abstract environments. The goal is no unidentified or accidentally transitive assumption in a stated deliverable.

## 7. Engineering, CLI, and reproducibility audit

### 7.1 Findings

| ID | Finding | Severity | Evidence | Recommended repair |
|---|---|---:|---|---|
| E-01 | CI invokes a deleted <code>jinja</code> target | High | [workflow](../.github/workflows/rust.yml#L274-L284); <code>make -n jinja</code> fails | Remove the step or restore a declared generator target and test it |
| E-02 | REVM host test does not compile | High | [host.v](../RocqOfRust/revm/revm_interpreter/tests/host.v#L123) lacks a <code>Link B256</code> instance | Make the default Rocq target green; add a fast REVM smoke job |
| E-03 | The Rust workspace has zero tests | High | <code>cargo test</code> runs four empty suites | Add unit, property, and differential tests around translation decisions |
| E-04 | Core regeneration is repaired by <code>sed</code> in CI | High | [workflow](../.github/workflows/rust.yml#L87-L88) comments out a generated module | Represent the limitation in translation policy and fail or generate valid output |
| E-05 | Ink generation is disabled after a compiler panic | High | commented workflow block and submodule drift | Reproduce as a fixture; fail with a diagnostic rather than dropping a corpus |
| E-06 | Standalone directory mode recompiles the directory path for every file | High | [core.rs](../lib/src/core.rs#L64-L90) loops entries but [create_translation_to_rocq](../lib/src/core.rs#L96-L142) always uses <code>opts.path</code> | Pass the current file and add nested-directory tests |
| E-07 | CLI output paths embed source paths and require the output directory to pre-exist | Medium | [main.rs](../cli/src/main.rs#L18-L29), [core.rs](../lib/src/core.rs#L40-L63) | Normalize relative paths under a created output root |
| E-08 | Cargo-wrapper output paths are derived directly from rustc source filenames and are not confined to a declared output root | High | [callbacks.rs](../lib/src/callbacks.rs#L40-L75) | Require an output root; normalize source-relative paths and write atomically using a deterministic crate/file map |
| E-09 | Some output-file errors are logged and ignored | High | [callbacks.rs](../lib/src/callbacks.rs#L57-L65) | Make write failure fatal unless an explicit exclusion policy matches |
| E-10 | Parsed configuration options are dropped | Medium | [options.rs](../lib/src/options.rs#L4-L43) parses configuration and reorder flags but <code>Options</code> retains neither | Implement or remove the flags; add CLI contract tests |
| E-11 | A single nightly and rustc-private API are hard requirements | Medium | [rust-toolchain](../rust-toolchain#L1-L8), [lib.rs](../lib/src/lib.rs#L1-L2) | Document an upgrade policy and automated semantic-diff process |
| E-12 | Documentation links use wrong case and the claim language is too broad | High | [README](../README.md#L3-L7), [README](../README.md#L100-L103) vs <code>builds.md</code>/<code>guide.md</code> | Publish a supported-subset and evidence-level page; repair links |

### 7.2 Snapshot tests are useful but insufficient

The repository tracks 267 Rust snapshot inputs:

| Corpus | Rust inputs |
|---|---:|
| Rust Book | 214 |
| Ink examples | 29 |
| Custom | 18 |
| Monadic transformation | 5 |
| Subtle example | 1 |
| **Total** | **267** |

Each is translated in normal and axiomatized mode, producing 534 current generated <code>.v</code> snapshots. There are 530 tracked <code>.err</code> snapshots; the two sets are not one-to-one. This is good regression coverage for pretty-print stability and rustc API changes. It does not establish that the output denotes the same program.

A snapshot suite can approve a stable bug indefinitely. It needs three companions:

- **decision tests:** small Rust-side unit tests that assert a THIR/HIR form maps to an explicit supported semantic constructor or a hard diagnostic;
- **differential tests:** execute Rust and the Rocq model on the same concrete inputs, including panic outcomes;
- **metamorphic tests:** translate equivalent source variants—such as explicit wrapping operations, desugared matches, and reordered independent declarations—and compare their modeled behavior.

The signed arithmetic, shift, range-pattern, and bounds reproducers from this audit should become the first differential fixtures.

### 7.3 Build shape and developer feedback

The default Rocq makefile discovers every non-blacklisted <code>.v</code> file. With 1,885 files and almost 4.9 million physical lines, that makes global compilation a poor inner loop. Nineteen active blacklist entries also mean “make passed” is not equivalent to “all checked-in proof files passed.”

Create explicit packages:

~~~text
core-semantics
frontend-fixtures
links-library
revm-generated
revm-instruction-proofs
revm-integration-proofs
legacy
~~~

Each package should emit a status and manifest. Pull requests should build affected packages plus a small protected set; nightly CI can build the full graph. A dependency graph generated from <code>Require</code> imports can select reverse dependencies.

Diagnostics should include:

- stable code such as <code>ROR-E-PATTERN-RANGE</code>;
- source span and rustc DefId/path;
- semantic impact: rejected, abstracted, or assumed;
- remediation hint;
- manifest entry;
- strict/permissive disposition.

Warnings printed into a large generation log are not an adequate correctness boundary.

### 7.4 Determinism and artifact identity

Generated artifact identity currently depends on working directories, rustc file-name strings, and unsorted <code>HashMap</code> traversal. Cargo index generation collects map keys without an explicit order, while standalone <code>translation.iter().next()</code> can select an arbitrary translation. Correctness work needs a content-addressed identity:

~~~text
artifact key =
  source repository revision
  + crate/package identity and enabled features
  + rustc version
  + target specification
  + compiler flags
  + rocq-of-rust revision and semantic profile
  + source-relative item path
~~~

Write into a staging directory, validate all expected files, then atomically replace the output. Store the key in a header and JSON manifest. Sorting every declaration and file list must be explicit. Re-running generation with the same key should be byte-identical and should not touch timestamps of unchanged files.

### 7.5 Packaging and contributor experience

The repository uses MIT for Rocq and AGPL-3.0 for the transpiler. Publish explicit guidance—and obtain legal review where appropriate—on generated artifacts, linking, modification, and proprietary verification use. The Rust packages are version 0.1.0 while the opam package is 0.1; there is no release compatibility matrix joining translator, nightly, Rocq, plugin, and proof corpus.

A minimal supported release should include:

- one installation command or container image;
- exact Rust nightly and Rocq/opam lock;
- a five-minute end-to-end example;
- <code>rocq-of-rust doctor</code> to validate tools and versions;
- <code>rocq-of-rust inspect-manifest</code> to explain assumptions;
- a compatibility table for the latest three project releases;
- a migration note for rustc or REVM upgrades.

## 8. REVM technical audit

### 8.1 Why REVM is the right stress test

REVM is a strong flagship target. It combines generics, traits, macro-generated instruction tables, mutable interpreter state, byte arrays, large integers, host callbacks, fork-dependent gas, journals, database effects, nested calls, and security-critical failure behavior. It is also production infrastructure in the Ethereum ecosystem. A successful end-to-end result would be more convincing than a suite of isolated examples.

It is equally important not to let REVM-specific proof stubs define the platform semantics. The Rust frontend should first be validated on small language tests, while REVM supplies integration pressure and application-level priorities.

### 8.2 Version identity and claim drift

| Target | Revision/version | Meaning |
|---|---|---|
| Initial grant report | <code>80099a770…</code> | Fixed historical REVM target covered by the February 2026 report |
| Current checked-in gitlink | <code>0d424ba11…</code>, v102 / revm 33.1.0 | Actual subject of the local proof tree |
| Repository review notes | v103 | Upgrade guidance, not current generated coverage |
| Latest GitHub Release at audit date | v111 / revm 40.0.2 | Public releases have moved beyond the proof target; repository tags may be newer |

The [grant report](https://formal.land/reports/2026-02-15_revm-formal-specification.pdf) reported approximately 94% coverage of instruction bodies for its fixed commit and explicitly described axiomatized dependencies and exclusions. That number must not be reused as “94% of REVM verified,” and it must not be applied automatically to v102. Versioned proof claims are mandatory because instruction signatures and gas behavior change between releases.

### 8.3 Tracked crate coverage

The matrix below counts copied tracked Rust source files and corresponding Rocq files. A file count indicates presence, not proof completion.

| Crate | Rust <code>.rs</code> | Generated <code>.v</code> | Link files | Simulation files | Legacy simulation | Test files |
|---|---:|---:|---:|---:|---:|---:|
| <code>revm</code> | 1 | 0 | 0 | 0 | 0 | 0 |
| <code>revm_bytecode</code> | 13 | 11 | 2 | 0 | 0 | 0 |
| <code>revm_context</code> | 11 | 9 | 0 | 0 | 0 | 0 |
| <code>revm_context_interface</code> | 17 | 16 | 8 | 5 | 0 | 0 |
| <code>revm_database_interface</code> | 5 | 4 | 0 | 0 | 0 | 0 |
| <code>revm_handler</code> | 16 | 15 | 0 | 0 | 0 | 0 |
| <code>revm_interpreter</code> | 37 | 32 | 85 | 98 | 7 | 13 |
| <code>revm_precompile</code> | 31 | 30 | 1 | 0 | 0 | 0 |
| <code>revm_primitives</code> | 11 | 10 | 2 | 2 | 2 | 0 |
| <code>revm_state</code> | 3 | 3 | 1 | 0 | 0 | 0 |
| **Total** | **145** | **130** | **99** | **105** | **9** | **13** |

Of 99 link files, 85 are in <code>revm_interpreter</code>. Of 105 current simulation files, 98 are there. The context, database, handler, state, precompile, and top-level executor layers are mostly translation artifacts without refinement proofs.

This distribution supports a precise claim: the project has deep work on many interpreter instruction functions. It does not support a claim about transaction execution or the complete REVM crate.

### 8.4 REVM assumption inventory

| Layer | Files | Lines | <code>Admitted.</code> | <code>Axiom</code> | <code>Parameter</code> |
|---|---:|---:|---:|---:|---:|
| Generated | 130 | 412,435 | 1,397 | 1,227 | 0 |
| Links | 99 | 10,038 | 43 | 0 | 2 |
| Simulations, including legacy | 114 | 16,996 | 58 | 0 | 12 |
| Tests | 13 | 3,734 | 15 | 0 | 4 |
| **Total** | **356** | **443,203** | **1,513** | **1,227** | **18** |

The table reports active admits; a lexical grep finds one extra <code>Admitted.</code> inside the fully commented interpreter <code>run</code> sketch. There is no current <code>proofs/</code> directory beneath REVM. Proof-like lemmas are located in links, simulations, and tests. A syntax-aware source count finds 212 active <code>Lemma</code>/<code>Theorem</code> declarations under current <code>simulate/</code>, or 215 including legacy, while 24 simulation files contain active admits. None of those numbers is a sound coverage denominator without item and assumption manifests.

Within the 86 direct instruction-simulation files, 72 have no active local admit and 14 do: five contract, six host, one memory, and two system files. “No local admit” still says nothing about transitive assumptions, stale links, gas completeness, dispatch integration, or an independent specification. This is why the older instruction README's hand-maintained 82/5/87 summary should not be reused.

### 8.5 The interpreter boundary is not closed

The current [interpreter link](../RocqOfRust/revm/revm_interpreter/links/interpreter.v#L16-L49) actively links <code>step</code> and closes it with <code>Defined</code>, but [simulate/interpreter.v](../RocqOfRust/revm/revm_interpreter/simulate/interpreter.v#L11-L74) specifies only halt helpers. There is no active interpreter <code>run</code> link: the entire attempted <code>run_run</code> instance, including its <code>Admitted.</code> line, is inside a comment ([interpreter.v](../RocqOfRust/revm/revm_interpreter/links/interpreter.v#L215-L246)). There is no simulation/refinement theorem that dispatching an opcode through the 256-entry instruction table executes the independently specified instruction and reaches the correct next state.

That missing theorem is a central integration boundary. Individual instruction proofs can all be correct while:

- opcode registration points to the wrong function;
- the program counter advances incorrectly;
- memory is not resized before an instruction;
- the host or journal state is threaded incorrectly;
- a halt/action result is lost;
- a feature/fork selects the wrong instruction table.

A credible first end-to-end theorem should cover a bounded straight-line bytecode fragment over a concrete interpreter type and host. It need not immediately support nested calls.

### 8.6 Stale links and interfaces

The copied v102 Rust for <code>origin</code> and <code>blob_hash</code> accepts an <code>InstructionContext</code> ([tx_info.rs](../RocqOfRust/revm/revm_interpreter/instructions/tx_info.rs#L20-L39)). The handwritten link still describes the older separate interpreter/host arguments ([links/tx_info.v](../RocqOfRust/revm/revm_interpreter/instructions/links/tx_info.v#L60-L137)) and is admitted.

Two gas helpers have similar drift:

- generated <code>extcodecopy_cost</code> takes <code>is_cold : bool</code>, while its link/simulation uses <code>Eip7702CodeLoad.t unit</code>;
- generated <code>warm_cold_cost_with_delegation</code> takes <code>StateLoad&lt;AccountLoad&gt;</code>, while the handwritten side also uses <code>Eip7702CodeLoad.t unit</code>.

These are not merely compilation chores. A stale gas signature can preserve an old fork's semantics under a theorem named like the new function. Add a generated signature fingerprint to each link manifest and make mismatch a hard error.

### 8.7 Gas is a critical correctness blocker

[gas/simulate/calc.v](../RocqOfRust/revm/revm_interpreter/gas/simulate/calc.v) contains exactly 23 direct definitions that return zero or <code>Some 0</code> as placeholders. All 23 corresponding <code>_eq</code> equivalence lemmas are actively admitted. Affected families include:

- exponentiation;
- copy, log, and Keccak costs;
- initcode cost;
- SLOAD/SSTORE and refunds;
- SELFDESTRUCT;
- calls and warm/cold/delegation accounting;
- memory expansion.

Transaction-level intrinsic gas helpers are also omitted.

Gas is part of EVM semantics, not an optimization metric. It decides:

- whether state changes commit or revert;
- the exceptional-halt point;
- whether a nested call receives enough gas;
- refunds and transaction settlement;
- fork compatibility;
- denial-of-service safety.

For this reason, an instruction proof that ignores or placeholders gas must be labeled “state/value functional model excluding gas and OOG,” not fully verified instruction semantics.

The gas work should use:

1. exact fork-indexed constants;
2. unbounded arithmetic only where overflow impossibility is proved;
3. explicit memory-word rounding and quadratic expansion;
4. EIP-specific warm/cold and delegation state;
5. independently generated test vectors from Ethereum execution specifications;
6. proofs relating each helper to both its Rust body and the independent formula.

### 8.8 Current tests do not validate the Rust implementation

The 13 REVM test files contain 155 <code>vm_compute</code> goals. These are useful smoke checks for functional definitions. They do not:

- execute the native REVM function on the same input;
- compare post-state, gas, memory, logs, journal, and halt reason;
- use official Ethereum state-test fixtures;
- cover the instruction dispatcher;
- detect that a link is stale if its local functional test still computes.

The reproduced host-test compilation failure at [host.v](../RocqOfRust/revm/revm_interpreter/tests/host.v#L123) further means the checked-in smoke surface is not currently coherent.

### 8.9 A defensible REVM evidence ladder

Use the following labels in dashboards and reports:

| Level | Required evidence | Suitable claim |
|---|---|---|
| R0 Mirrored | Copied Rust source with source revision | “Tracked as a target” |
| R1 Translated | Strict translation, zero unsupported diagnostics | “Translated to Rocq for this configuration” |
| R2 Linked | Typed link closed; assumption manifest published | “Linked to typed Rocq semantics” |
| R3 Simulated | Readable functional model and closed equivalence theorem | “Refined to this functional model” |
| R4 Independently specified | Functional model related to EELS, an EIP formula, or another independent spec | “Conforms to the cited specification for this scope” |
| R5 Integrated | Dispatcher/host/journal or transaction theorem closes composition | “Verified along this end-to-end execution path” |
| R6 Validated | Differential runs over official and adversarial fixtures | “Mechanically cross-validated on this test set” |

No single percentage should aggregate these levels. Publish counts by level, crate, fork, and REVM revision.

## 9. Position relative to other projects

### 9.1 Rust verification landscape

The comparison is capability-oriented. Project status and exact feature sets change; links point to the primary project sources checked at the audit date.

| Project | Input/lowering | Main proof mechanism | Source changes | Unsafe/memory story | Automation/feedback | Relative position |
|---|---|---|---|---|---|---|
| **rocq-of-rust** | rustc HIR/THIR to a Rocq deep embedding, then links/simulations | Interactive Rocq refinement proofs | Usually unchanged production Rust; handwritten links/specs/proofs | Structural safe-code memory; unsafe and layout mostly abstract | Low to medium; source-correlated artifacts, limited counterexamples | Strong production-code inspectability and Rocq integration; weak semantic closure today |
| [Aeneas](https://github.com/AeneasVerif/aeneas) | Charon lowers MIR to LLBC and pure functional code | F*, Lean, Rocq, HOL4 backends | Mostly unchanged safe Rust plus proof-side work | Formal work on borrow-checking soundness; safe subset; unsafe/concurrency are separate future challenges | Strong automatic functionalization; backend maturity varies | Closest architectural comparator; stronger formal translation narrative |
| [Hax](https://github.com/cryspen/hax) | THIR extraction and backend-specific phases | Primarily F*, with Rocq/Lean and other backends | Attributes/refinements often guide extraction | Restricts aliasing patterns; not a foundational unsafe model | Mature F* workflow, partial/active other backends | Similar rustc layer; broader multi-backend extraction, less Rocq-specific refinement depth |
| [RefinedRust](https://plv.mpi-sws.org/refinedrust/) | Annotated Rust into a foundational Coq/Iris model | Separation logic and refinement typing in Coq | Significant verification annotations | Core strength: safe and unsafe Rust, ownership, lifetimes, representation | Research prototype; high proof expertise | Much stronger foundational unsafe story; less frictionless at production-crate scale |
| [Creusot](https://creusot.rs/) | Rust/MIR into Coma and Why3 | SMT-backed deductive verification | Contracts, invariants, ghost code | Logical model with prophecy-style treatment of mutable borrows | High automation and fast failures | Better day-to-day contract proving; less direct interactive operational proof control |
| [Verus](https://github.com/verus-lang/verus) | Extended Rust-like language/annotations | SMT with executable/spec/proof modes | Contracts and ghost/proof code | Supports important low-level patterns including raw-pointer reasoning under its model | High automation and counterexamples/model feedback | Better usability for annotated verification; different trusted stack and proof style |
| [Kani](https://model-checking.github.io/kani/) | Rust to model checking with proof harnesses | Bounded model checking/CBMC | Harnesses, assumptions, contracts | Checks panic, overflow, UB and memory-safety properties within bounds | Excellent concrete counterexamples; bounded/scalability limits | Complementary oracle for frontend semantics and REVM helpers, not a substitute for universal proofs |
| [MiniRust](https://github.com/minirust/minirust) | Research MIR-like core language, not a complete Rust frontend or official Rust semantics | Executable/formal operational semantics | N/A | Exact evaluation order, byte memory interface, layout/UB focus; incomplete | Reference model rather than product verifier | Strong candidate semantic north star for the low-level core |
| [Foundational VeriFast](https://arxiv.org/abs/2601.13727) | Symbolic execution proof scripts replayed in Rocq against axiomatic MIR semantics | Separation logic with Rocq replay | VeriFast annotations/contracts | Explicit unsafe and ownership reasoning | Mature VeriFast workflow; foundational replay is recent research | Important 2026 comparator for kernel-checked Rust verification claims |
| [Prusti](https://github.com/viperproject/prusti-dev) | Rust/MIR to Viper | SMT-backed contracts | Annotations | Ownership-aware logical verification; active scope varies | Automated | Historically important comparator; verify current maintenance status before product comparisons |

### 9.2 Where rocq-of-rust is genuinely differentiated

1. **Readable, source-correlated deep embedding.** The generated object retains recognizable Rust control flow and names rather than immediately erasing them into verification conditions.
2. **A staged trust boundary.** Untyped translation, typed linking, and idiomatic simulation make mismatches reviewable at distinct layers.
3. **Rocq-native extensibility.** Users can state arbitrary mathematical properties, compose libraries, and inspect final proof terms.
4. **Evidence on large real crates.** REVM and dependency corpora exercise traits and macros beyond most tutorial verifiers.
5. **Potential for auditable proof artifacts.** A link plugin can generate repetitive terms while the kernel validates them.

Those advantages are currently weakened by fail-open translation and the lack of a manifest. Once repaired, they form a credible niche: high-assurance, Rocq-native refinement of selected critical paths in production Rust.

### 9.3 Where competitors are ahead

- Aeneas has a clearer formal story around functional translation and borrow checking.
- RefinedRust and VeriFast have substantially stronger low-level and unsafe-memory foundations.
- Creusot and Verus give users contracts, automated solvers, faster proof feedback, and countermodels.
- Kani makes semantic failures concrete and reproducible with minimal proof infrastructure.
- Multi-backend tools reduce dependence on one proof-assistant ecosystem.

rocq-of-rust should not attempt to close every gap simultaneously. Its most useful integrations are:

- differential frontend tests generated with Kani or native Rust;
- alignment of the semantic subset with MiniRust;
- import/export of contracts or pure models from Aeneas/Hax where practical;
- use of RefinedRust/VeriFast for explicitly unsafe components;
- an optional SMT sidecar for arithmetic leaves while retaining Rocq proof terms or checked certificates.

### 9.4 EVM semantics and implementation-verification landscape

| Project/specification | Subject | Strength | Limitation relative to rocq-of-rust's goal |
|---|---|---|---|
| [EELS / Ethereum execution specifications](https://github.com/ethereum/execution-specs) | Readable executable Python execution-layer specification | Canonical protocol-level oracle and fork evolution | It specifies Ethereum behavior, not REVM implementation correctness |
| [EEST / execution-specification tests](https://github.com/ethereum/execution-spec-tests) | Tests and fixtures generated from execution specifications | Broad concrete cross-client validation corpus | Finite tests do not prove REVM refinement |
| [KEVM](https://docs.runtimeverification.com/kevm/overview) | Executable EVM semantics in K | Mature semantics and symbolic reachability tooling | Does not prove current REVM Rust refines the semantics |
| [Verifereum](https://verifereum.org/) | Executable EVM semantics in HOL4 | Mature theorem-prover semantics with broad test validation | Independent semantics, not a Rust implementation proof |
| [Isabelle/EVM](https://drops.dagstuhl.de/entities/document/10.4230/OASIcs.FMBC.2026.3) | EVM semantics and verification in Isabelle/HOL | Authors report current-opcode/cross-contract coverage and extensive official-test execution | Again, implementation-independent |
| **rocq-of-rust + REVM** | Production Rust implementation and handwritten Rocq simulations | Can connect deployed implementation structure to theorem-prover models | Connection is presently instruction-local, assumption-heavy, and not independently specified |

The opportunity is not “another EVM formalization.” It is a checked refinement path:

~~~text
specific REVM revision and configuration
  -> faithful Rust semantics
  -> linked executable interpreter
  -> independent fork-indexed EVM specification
  -> official execution fixtures as differential validation
~~~

No other public project found in this audit clearly supplies that complete REVM-specific chain. This is an inference from the reviewed primary sources, not a claim that no private or unpublished work exists.

### 9.5 Recommended market and research position

Avoid “check 100% of execution cases” as an unqualified headline while the frontend changes basic Rust behavior and the proof closure is unknown. Prefer:

> Kernel-checked refinement proofs for selected critical paths in production Rust, with source-correlated Rocq artifacts and explicit assumptions.

For REVM:

> Versioned refinement of REVM instruction implementations toward an independent EVM model; instruction coverage is in progress and transaction-level verification is a roadmap item.

This wording remains ambitious, makes the unique value legible, and gives measurable criteria for strengthening the claim.

## 10. Prioritized improvement backlog

### 10.1 Prioritization principles

The ordering below follows five rules:

1. prevent unsound success before adding supported syntax;
2. repair the reusable platform before specializing more code for REVM;
3. close vertical slices before increasing translation percentages;
4. make every status and assumption machine-verifiable;
5. keep an independent oracle in each validation loop.

Effort is relative: S is a focused change, M is a multi-file feature with tests and proofs, L is a substantial subsystem, and XL is a research/architecture program. “Acceptance” is deliberately testable.

### 10.2 Platform backlog

| ID | Priority | Improvement | Impact | Effort | Dependencies | Acceptance criterion |
|---|---:|---|---|---:|---|---|
| PF-00 | P0 | Minimal typed normal/panic/abort outcome plus compiler/target metadata | Unblocks faithful primitive failure and profile-sensitive semantics | M | None | Panic/abort is distinct from <code>Impossible</code>; rustc, target, panic strategy, and overflow configuration are recorded |
| PF-01 | P0 | Strict, fail-closed translation mode | Prevents proofs of changed programs | M | None | Every unsupported THIR/HIR case produces a stable error and no consumable artifact |
| PF-02 | P0 | Fix range/constant/never/deref pattern lowering | Removes confirmed critical mismatch | M | PF-01 | Differential tests cover match success/failure and guards across all supported pattern forms |
| PF-03 | P0 | Correct signed division/remainder and mandatory panics | Repairs ordinary integer semantics | M | PF-00 | Exhaustive i8 differential suite agrees with Rust for all non/exceptional operands |
| PF-04 | P0 | Correct shift semantics by operation and build profile | Repairs debug/release mismatch | M | PF-00 | Exhaustive small-width suite covers every RHS kind, negative signed counts, and checked/wrapping/overflowing/ordinary APIs for exact configurations |
| PF-05 | P0 | Repair pointer-path read/write failure consistency | Removes silent invalid state transitions | M/L | PF-00, typed failure policy | Read/write laws proved; valid array/slice OOB yields modeled panic; invalid typed indices are rejected; impossible tuple/field indices are internal failures |
| PF-06 | P0 | Proof and translation manifest | Makes claims auditable | M | Stable item identity | CI emits per-theorem assumptions and blocks new unapproved dependencies |
| PF-07 | P0 | Restore green CI and fast protected target | Restores trustworthy baseline | S/M | None | Workflow has no deleted target; host smoke target and protected theorem set pass from clean checkout |
| PF-08 | P0 | Rust frontend unit/differential suite | Catches local regressions | M | PF-01 | Nonzero Rust tests include every confirmed reproducer and negative diagnostic fixtures |
| PF-09 | P1 | Preserve break values and loop labels | Fixes common control flow | M | Loop representation design | Nested/labeled/value loop differential suite passes |
| PF-10 | P1 | Model loops relationally and execute them with explicit fuel | Enables linked loop programs | L | PF-09 | Soundness lemma relates fuelled successes to inductive semantics; divergence is not reported as success |
| PF-11 | P2 | Represent implicit drop and cleanup control flow | Enables RAII-sensitive code | L/XL | PF-00, PF-16 | Destructor ordering and return cleanup fixtures match Rust; RAII items remain rejected beforehand |
| PF-12 | P2 | Extend panic/abort outcomes with unwind cleanup | Completes supported panic semantics | L/XL | PF-00, PF-11 | Every modeled panic source follows the recorded strategy; panic-freedom theorem excludes all panic/abort outcomes |
| PF-13 | P1 | Target-derived integer widths and validity invariants | Removes non-Rust states | L | PF-00, integer design | <code>usize/isize</code> width follows target; all primitive ops preserve validity |
| PF-14 | P1 | Supported-subset capability matrix | Aligns users and claims | S/M | Strict diagnostics | Generated from handler coverage and linked to semantic/tests status |
| PF-15 | P2 | Semantic correspondence statement for a core subset | Reduces translator TCB | XL | Strict baseline and chosen subset semantics | A defined subset has a machine-checked simulation/refinement theorem or proof-producing lowering |
| PF-16 | P1 | THIR/MIR hybrid architecture experiment | Obtains explicit drop/cleanup/control flow without losing source types | L | PF-00, source identity | Prototype maps MIR control-flow events to source spans and shared THIR item identities; a recorded decision precedes PF-11 |
| PF-17 | P2 | Unsafe operation contracts | Safely broadens useful scope | L/XL | Memory boundary | Every unsafe primitive is rejected or requires an explicit pre/postcondition in the manifest |
| PF-18 | P2 | Floats, atomics, async | Broadens language coverage | XL each | Demand and independent semantics | Only schedule after a named target requires them; never implement as unconstrained globals |

PF-15 does not require proving all of rustc correct. A useful first theorem can cover a typed expression language with integers, tuples, structs, matches, calls, mutable local references, and explicit outcomes. The practical frontend then reports whether an item lies inside that theorem's subset.

### 10.3 Tooling and proof-engineering backlog

| ID | Priority | Feature | Value | Effort | Acceptance criterion |
|---|---:|---|---|---:|---|
| DX-01 | P0 | Deterministic output root and atomic generation | Reproducible builds | M | Same artifact key yields byte-identical tree; inaccessible output is fatal |
| DX-02 | P0 | Stable diagnostic codes and JSON diagnostics | Enables policy and editors | M | Human and JSON output contain code, span, item, semantic disposition, remediation |
| DX-03 | P1 | Item source map | Faster proof maintenance | M | Rocq definitions/theorem failures map to Rust file, span, DefId, and source revision |
| DX-04 | P1 | Coverage/assumption dashboard | Makes progress honest | M | Dashboard is generated, revisioned, drillable by crate/item/evidence level |
| DX-05 | P1 | Incremental dependency graph | Shortens feedback loop | L | A changed item rebuilds its generated file and reverse proof dependencies only |
| DX-06 | P1 | Counterexample/trace runner | Makes semantic failures actionable | L | A concrete Rust input produces aligned Rust and Rocq outcomes plus first differing event |
| DX-07 | P1 | Link generation for records/enums/functions | Reduces repetitive proof labor | M/L | Plugin-generated obligations never add axioms and expose unresolved fields explicitly |
| DX-08 | P2 | Contract syntax and extraction | Lets users state properties near code | L | Contracts lower to named Rocq propositions and preserve source locations |
| DX-09 | P2 | Optional checked arithmetic automation | Speeds leaf proofs | M/L | Solver output is replayed/certified; protected theorem assumption closure is unchanged |
| DX-10 | P2 | Release bundle and <code>doctor</code> command | Improves adoption | M | Clean container completes documented example and verifies compatibility lock |

### 10.4 REVM backlog

| ID | Priority | Improvement | Impact | Effort | Acceptance criterion |
|---|---:|---|---|---:|---|
| RV-01 | P0 | Record and freeze the complete REVM target identity | Stops moving-goal ambiguity | S | Existing gitlink plus features, target, compiler, and forks are manifest-recorded; dashboard never combines identities |
| RV-02 | P0 | Remove stale instruction/gas links | Prevents old behavior under new names | M | Signature fingerprints match; <code>origin</code>, <code>blob_hash</code>, <code>extcodecopy_cost</code>, and <code>warm_cold_cost_with_delegation</code> links use current signatures |
| RV-03 | P0 | Make all current REVM proof targets compile | Establishes baseline | M | Clean protected build includes host tests and has zero unexpected blacklist entries |
| RV-04 | P0/P1 | Complete exact gas helpers used by protected opcodes | Restores EVM-relevant semantics | L | No zero placeholder lies in closure; formula proofs and EEST vectors pass |
| RV-05 | P1 | Retain/repair the active <code>step</code> link and prove table/step simulation | Closes dispatcher gap | L | A refinement theorem shows each protected opcode's fetched table entry invokes the expected instruction and state transition |
| RV-06 | P1 | Concrete interpreter/host/journal slice | Reduces abstract-interface assumptions | XL | Straight-line program theorem covers stack, memory, gas, PC, host reads, halt result |
| RV-07 | P1 | EELS/EEST differential adapter | Supplies independent oracle | L | Same fork/test vector produces matching status, gas, output, logs, and post-state |
| RV-08 | P2 | Nested call/create and journal rollback | Covers critical state semantics | XL | Success, revert, and exceptional halt match oracle through at least two call frames |
| RV-09 | P2 | Handler and transaction pipeline | Moves from interpreter to REVM | XL | One supported transaction class is proved from validated input through settlement |
| RV-10 | P2 | Precompile strategy | Covers external computation honestly | XL | Each precompile is proved, connected to a certified library, or an explicit contract |
| RV-11 | P2 | Fork-delta framework | Makes upgrades reviewable | L | New fork reuses unchanged proofs and generates obligations for semantic deltas only |
| RV-12 | P3 | Upstream-version continuous integration | Limits proof drift | L ongoing | Scheduled job reports signature/semantic deltas without overwriting protected artifacts |

## 11. Feature design recommendations

### 11.1 Semantic profiles

Replace the current binary “axiomatize” behavior with named profiles:

| Profile | Unsupported source | Abstract dependencies | Intended use |
|---|---|---|---|
| <code>strict</code> | Hard error | Only declared contracts | Publishable proofs |
| <code>explore</code> | Emits explicit opaque node and taints dependents | Allowed with manifest | Early porting and coverage discovery |
| <code>snapshot</code> | Preserves diagnostics and output for regression tests | Broadly allowed | Frontend development only |
| <code>legacy</code> | Current compatibility behavior | Current assumptions | Rebuilding historical artifacts; never publish as strict |

An opaque node must not be equal to unit or a wildcard. It should carry an ID and cause any dependent theorem to be marked tainted. The Rocq representation can remain abstract, but it must be impossible to confuse with a successfully modeled computation.

### 11.2 Runtime outcomes and tool-status separation

The runtime/control semantics should distinguish:

~~~text
normal value
return value
continue with optional label
break with optional label and value
panic payload and source
abort
~~~

Separately, the syntax/manifest/evaluator layer should record:

~~~text
unsupported or tainted node
violated compiler invariant / stuck semantics
out-of-fuel evaluator result
~~~

Divergence is a semantic judgment, not a catchable runtime value. Rust code must not be able to observe or catch translation taint or evaluator fuel. Today, “impossible,” failed pattern matching, unsupported operations, panic, and some bounds failures are close enough in representation that proofs can lose the distinction. A typed runtime outcome plus separate meta-status makes panic-freedom and exhaustiveness stateable without relying on comments.

For unwind semantics, cleanup can be modeled as a stack of scopes or taken from MIR cleanup edges. If the initial supported profile is <code>panic=abort</code>, state that restriction in the target manifest and still model the abort outcome.

### 11.3 Valid integers

There are three viable designs:

1. **Dependent bounded values:** store <code>Z</code> plus a proof of range. Strong invariant, heavier rewriting.
2. **Bitvectors:** use a well-supported bitvector library. Natural modular arithmetic and automation, but conversions and signed views need care. Ordinary primitive shifts still need a profile-sensitive overflow wrapper; a library's masked shift is appropriate only for APIs such as <code>wrapping_shl</code>/<code>overflowing_shl</code>.
3. **Unbounded representation with validity predicates:** least disruptive, but every boundary theorem must carry and preserve validity.

For REVM, bitvectors or a bounded <code>Z</code> foundation are preferable because U256 and machine-word operations are central. Use a shared bitvector foundation with distinct wrappers and contracts for primitive Rust integers and the custom generic ruint type; they do not have one undifferentiated source semantics. Signed division must operate on the signed interpretation with truncation toward zero; ordinary division must return a panic outcome on zero and signed minimum divided by minus one. Wrapping/checked/overflowing/saturating operations should remain distinct definitions.

### 11.4 THIR/MIR hybrid rather than a wholesale rewrite

THIR is useful for typed expressions, overloaded operators, and source correlation. MIR makes control flow, drops, moves, storage liveness, cleanup edges, and assertions explicit. A hybrid can preserve the current architecture:

- use HIR/THIR for item structure, resolved types, patterns, and expression/source presentation;
- use MIR to derive the executable control-flow skeleton and implicit effects;
- map MIR basic blocks and statements back to THIR/source spans;
- give each operation a shared stable semantic ID;
- render a source-oriented Rocq form while retaining a machine-checkable MIR-origin table.

Before implementing, compare a corpus of functions under both lowerings. The decision criterion is whether the hybrid eliminates implicit-effect gaps without destroying maintainability of generated proofs.

### 11.5 Contracts and modular verification

Large crates cannot be verified by inlining every dependency. Introduce contracts for:

- pure functions;
- stateful functions over explicit pre/post-state;
- trait methods;
- unsafe primitives;
- FFI and host calls;
- cryptographic or database operations.

Every contract should identify whether it is:

- proved from a translated body;
- assumed for an external dependency;
- validated by tests only;
- connected to another formal development.

Callers should depend on the contract theorem, not a global function axiom. This makes replacement and assumption closure local.

For REVM, contracts are appropriate for database access, Keccak, precompiles, and possibly ruint internals. Gas, interpreter state transitions, and journal commit/revert should not be hidden behind broad contracts because they are central to the target claim.

### 11.6 Aligned execution traces

Add an optional trace semantics whose event vocabulary includes:

~~~text
enter/exit Rust item
read/write local or semantic state field
primitive integer operation
branch/match-arm choice
call/trait-dispatch target
panic/assert
EVM opcode, PC, gas-before/gas-after
stack/memory/journal delta
host request/response
~~~

Native Rust instrumentation and the Rocq evaluator should emit the same stable event IDs. A trace comparator can report the first divergence. Traces do not prove equivalence, but they dramatically reduce the cost of finding a bad lowering, stale link, or wrong simulation. For security, values should be redacted or hashable by policy.

### 11.7 Evidence dashboard

The dashboard should be a generated static artifact, not a hand-maintained percentage. For every item show:

- source revision and signature hash;
- strict-translation status and diagnostics;
- semantic-subset classification;
- link and simulation theorem names;
- assumption closure grouped by class;
- independent-spec status;
- differential-test count and last result;
- last successful compiler/Rocq configuration;
- owner and issue for each gap.

For REVM, add crate, opcode, hard-fork activation, gas completeness, host effects, memory effects, and integrated-dispatch status.

## 12. Platform-first implementation roadmap

### 12.1 Dependency order

~~~mermaid
flowchart TD
    A[Strict diagnostics and manifests] --> B[Semantic differential suite]
    B --> D[Target and outcome model]
    D --> C[Integer, pattern, bounds fixes]
    B --> C
    C --> E[Control flow and loops]
    D --> E
    E --> M[THIR/MIR decision, Drop and cleanup]
    A --> F[Deterministic modular build]
    C --> G[Protected REVM instruction slice]
    F --> G
    G --> H[Exact gas and dispatch]
    E --> H
    H --> I[Concrete host, journal, memory]
    I --> J[EELS/EEST differential closure]
    J --> K[Handler and transaction theorem]
    E --> L[Core semantic correspondence theorem]
~~~

### 12.2 Phase 0 — containment and truthful status

**Objective:** no new proof artifact can silently hide an unsupported construct or unidentified assumption.

Deliverables:

- introduce a minimal typed normal/panic/abort outcome and record compiler/target/panic/overflow configuration;
- implement strict diagnostics for every fallback branch;
- change range and unsupported patterns to hard errors;
- emit source/configuration/proof manifests;
- create a protected CI job containing semantic reproducers, plugin fixture, and a small REVM slice;
- remove the stale <code>jinja</code> step and resolve the host build failure;
- publish the evidence ladder and versioned REVM dashboard;
- revise README claim language and fix documentation links.

Exit criteria:

- all known fail-open paths have a test;
- a strict artifact with warnings cannot be marked publishable;
- protected theorem assumption closures are recorded and diffed;
- clean CI is reproducible from the documented environment;
- no REVM percentage is shown without evidence level and revision.

This phase is the highest return per unit effort. It does not require solving the full semantic model, but it prevents new unsound-looking successes.

### 12.3 Phase 1 — safe-Rust semantic baseline

**Objective:** faithfully model the ordinary safe constructs used by the first REVM vertical slice.

Deliverables:

- signed/unsigned integer families with correct ordinary and explicit overflow modes;
- target-derived pointer widths;
- explicit panic/abort result;
- corrected reads/writes/subpointers with pointer-path laws;
- break values and labels;
- relational loop semantics and tested fuel evaluator;
- THIR/MIR cleanup experiment and recorded architecture decision;
- compiler configuration recorded in artifacts;
- exhaustive small-width arithmetic and control-flow differential suites.

Exit criteria:

- exhaustive i8/u8 operator tests match native Rust;
- no generated value of a typed integer lies outside its Rust range without an explicit invalid-state hypothesis;
- array/slice out-of-bounds follows the selected panic strategy; invalid typed indices are unrepresentable or rejected; compiler-generated tuple/struct projections satisfy static-validity laws;
- labeled/value loops pass native/Rocq tests;
- the first REVM protected slice contains no semantic primitive outside the documented subset.

Implicit Drop may extend into Phase 2 if MIR integration is required, but RAII-dependent items must remain rejected until then.

### 12.4 Phase 2 — proof platform and semantic closure

**Objective:** make the pipeline maintainable and reduce the trusted translator for a meaningful subset.

Deliverables:

- implement the chosen THIR/MIR or MIR-assisted cleanup mapping;
- explicit cleanup/drop modeling for supported types;
- source maps and aligned traces;
- deterministic, incremental generation;
- contract system for external/dependency functions;
- proof-producing or verified lowering for the chosen core subset;
- generated coverage dashboard and release assumption reports;
- optional checked automation for arithmetic/record obligations.

Exit criteria:

- at least one nontrivial crate fragment is classified inside the proved semantic subset;
- source edits rebuild only affected proof packages;
- every external behavior in a protected theorem is a quantified contract or allowlisted axiom;
- release artifacts pass <code>coqchk</code> and reproducibility checks;
- a failing differential test reports the first source-correlated divergence.

### 12.5 Phase 3 — REVM instruction-to-dispatch vertical slice

**Objective:** prove and independently validate a small executable bytecode path, not just isolated instruction bodies.

Choose a deliberate slice:

- arithmetic: ADD, SUB, MUL, DIV/SDIV, MOD/SMOD;
- stack/control: PUSH, DUP, SWAP, POP, STOP;
- memory: MLOAD, MSTORE, MSIZE;
- environment: one host-read instruction such as ORIGIN;
- failure: stack underflow and out-of-gas;
- one fork configuration.

Deliverables:

- exact gas for the slice;
- instruction registration theorem;
- the existing active <code>step</code> link plus a new table/step simulation-refinement theorem;
- concrete interpreter types and minimal deterministic host;
- PC/stack/memory/gas/halt trace;
- differential adapter to native REVM, EELS execution, and EEST vectors;
- straight-line bytecode theorem.

Exit criteria:

- no zero gas placeholder or stale link is in the transitive closure;
- the dispatch theorem chooses the correct instruction for every slice opcode;
- official and adversarial fixtures match on full observed state;
- the theorem's assumption manifest contains only reviewed dependency/environment contracts;
- an unsupported opcode produces an explicit out-of-scope result, not an arbitrary behavior.

### 12.6 Phase 4 — stateful REVM and transaction path

**Objective:** extend the vertical proof through host state, rollback, calls, and one transaction class.

Deliverables:

- concrete journal/database refinement model;
- SLOAD/SSTORE, warm/cold access, refunds, logs;
- CALL/CREATE frame semantics, gas forwarding, success/revert/exception;
- handler/pre-execution and post-execution path;
- transaction intrinsic gas and settlement;
- fork-delta proofs;
- independent state-transition specification.

Exit criteria:

- one signed, validated transaction class is related from input environment to final state root-relevant changes;
- nested success/revert/exception fixtures match independent execution specs;
- state that must roll back is proven unchanged on revert;
- gas conservation/charging invariants are stated and proved for the supported path;
- upgrade deltas are explicit obligations rather than silent regenerated output.

Phase 4 is a long-term application program. It should begin only after Phase 3 proves that the composition strategy works.

## 13. Concrete REVM proof strategy

### 13.1 Freeze the subject before proving it

Create a <code>revm-target.toml</code> equivalent containing:

~~~toml
repository = "https://github.com/bluealloy/revm"
revision = "0d424ba11fd59d2a2a13988d61381e5b5cfccd22"
revm_release_tag = "v102"
revm_crate_version = "33.1.0"
features = ["...exact enabled features..."]
target = "x86_64-unknown-linux-gnu"
rustc = "nightly-2025-12-07"
evm_forks = ["...explicit supported forks..."]
~~~

The current tree should first be made coherent at this version. Do not interleave semantic repairs with an upgrade to latest REVM. After the protected slice closes, run upgrades as explicit delta projects. MLOAD and KECCAK already resize memory in v102; the v103 delta changes their <code>Host</code> dependencies/signatures and routes memory/gas charging through <code>context.host.gas_params()</code>. That is exactly the kind of signature and semantic dependency change a delta report must surface.

### 13.2 Separate three specifications

REVM verification needs three models with different owners:

1. **Rust implementation model:** generated automatically from the pinned source.
2. **Functional REVM model:** readable Rocq definitions that expose interpreter data structures and are convenient for proofs.
3. **Independent EVM model:** fork-indexed semantics derived from EELS/EIPs or connected to an established formal EVM semantics.

Proving 1 refines 2 validates the generated/linked program against the chosen functional model and can expose a discrepancy; it cannot by itself attribute the discrepancy to a Rust implementation bug or establish protocol correctness. Proving 2 refines 3 supplies the independent protocol edge. Running native REVM, the Rocq model, and the EELS executable specification/EEST fixtures on shared cases adds practical validation. Keep these evidence edges separate in manifests.

### 13.3 State relation

Define one explicit relation between concrete REVM state and the independent EVM state:

~~~text
RelState(revm, evm) :=
  PC agrees
  and active bytecode bytes agree
  and stack words agree in order
  and active memory bytes and logical size agree
  and remaining/spent/refunded gas agree
  and call-frame metadata agrees
  and warm accounts/storage agree
  and journaled account/storage/log/transient changes agree
  and action/halt status agrees
~~~

Do not hide fields merely because the current instruction leaves them unchanged; prove their frame condition. For an abstract database, quantify a relation and explicit read contract. For a deterministic minimal host, instantiate it and compute.

### 13.4 Instruction theorem shape

The reusable statement should be close to:

~~~coq
Theorem step_refines_evm
    fork opcode linked_state evm_state :
  supported_opcode fork opcode ->
  RelState linked_state evm_state ->
  manifest_clean opcode ->
  match linked_revm_step fork linked_state with
  | Success linked_state' =>
      exists evm_state',
        evm_step fork opcode evm_state = Success evm_state' /\
        RelState linked_state' evm_state'
  | Exceptional reason linked_state' =>
      exists evm_state',
        evm_step fork opcode evm_state = Exceptional reason evm_state' /\
        RelFailureState linked_state' evm_state'
  end.
~~~

The Rust-facing side is the linked execution theorem rather than a native call inside Rocq. A frontend correspondence theorem—or, until one exists, explicitly scoped conformance evidence—supplies its connection to Rust. The manifest records whether that evidence's preconditions and assumptions hold; the manifest itself proves no correspondence. Separate lemmas should prove gas calculation, stack preconditions, memory expansion, host action, and unchanged fields.

### 13.5 Differential record

For each fixture collect:

~~~json
{
  "revm_revision": "0d424ba11...",
  "rocq_of_rust_revision": "ebacf73cc...",
  "rustc": "nightly-2025-12-07",
  "eels_revision": "...",
  "fork": "explicit-fork",
  "bytecode": "0x...",
  "pre": {
    "pc": 0,
    "gas": 100000,
    "stack": [],
    "memory": "0x",
    "accounts_fixture": "..."
  },
  "observations": {
    "native_revm": {
      "status": "success|revert|exception",
      "pc": 0,
      "gas_remaining": 0,
      "gas_refund": 0,
      "stack": [],
      "memory": "0x",
      "logs": [],
      "state_delta": {},
      "trace_hash": "..."
    },
    "rocq": {"same_normalized_schema": "..."},
    "eels": {"same_normalized_schema": "..."}
  },
  "comparison": {"all_equal": true, "first_divergence": null}
}
~~~

Normalize representation before comparison: word endianness, memory trailing zeros, empty/nonexistent account distinctions, log ordering, refund caps, and fork-dependent halt names.

### 13.6 Gas work decomposition

Implement gas in dependency order:

1. constant costs and fork activation;
2. checked addition/multiplication helpers;
3. memory word rounding and quadratic expansion;
4. copy/Keccak/log exponent sizes;
5. warm/cold account and storage access;
6. SSTORE original/current/new value cases and refunds;
7. call stipend, 63/64 rule, value/new-account cases;
8. SELFDESTRUCT and delegation rules;
9. transaction intrinsic and calldata/access-list/initcode costs;
10. settlement/refund caps.

Each helper needs:

- generated Rust link;
- idiomatic Rocq function;
- equivalence theorem with clean assumptions;
- independent formula citation by fork;
- boundary and overflow tests;
- native REVM, EELS execution, and EEST vectors.

### 13.7 Precompiles and cryptography

The precompile crate has 30 generated files, one interface-only link file, and zero simulation or test files. Treat precompiles as a separate workstream:

- simple identity/hash wrappers can connect to verified or explicitly axiomatized cryptographic primitives;
- elliptic-curve and pairing implementations require specialized libraries and representation proofs;
- external C/assembly acceleration must be covered by contracts or lower-level verification;
- gas and input-validation behavior still belongs in the REVM/EVM proof even if the cryptographic result is assumed.

Do not block the first interpreter slice on precompiles, but ensure encountering one is an explicit unsupported boundary.

## 14. Validation and CI strategy

### 14.1 Frontend conformance matrix

Every supported construct should have tests across these dimensions:

| Dimension | Required variants |
|---|---|
| Build profile | debug checks on, release checks off, explicit overflow-check override |
| Target | at least 32-bit and 64-bit pointer width |
| Runtime outcome | value, return, break, continue, panic/abort |
| Tool/meta status | unsupported/tainted, internal stuck, evaluator out-of-fuel |
| Integers | signed/unsigned; min, max, zero, ±1; all operation families |
| Patterns | literals, ranges, or-patterns, guards, references, slices, structs/enums |
| Control flow | nested/labeled loops, value breaks, early return, <code>?</code>, match guards |
| Memory | array/tuple indexing, mutable borrows, reborrows, disjoint fields, OOB |
| Ownership | moves, copies, partial moves, explicit and implicit drops |
| Generics | trait calls, associated types/constants, dynamic dispatch where supported |
| Constants | evaluated constants, target constants, const generics |

Tests should state their semantic profile. A rejected feature test passes only if the expected stable diagnostic and span match.

### 14.2 Four validation layers

1. **Translator unit tests** inspect internal AST decisions and diagnostics.
2. **Native/Rocq differential tests** compare values, state, and failure outcomes.
3. **Kernel proof checks** validate semantic laws and refinement theorems with assumption policies.
4. **Independent application tests** compare against EELS/EEST or another formal EVM model.

No layer subsumes another. Native differential tests find encoding errors quickly but are finite. Proofs cover all modeled inputs but can prove the wrong encoding. Independent application tests detect a shared implementation/specification misunderstanding.

### 14.3 Property and fuzz testing

Use exhaustive enumeration for i8/u8 and small arrays. Use property-based generation for larger types and AST fragments:

- <code>decode(encode(x)) = x</code> for valid linked values;
- primitive operations preserve validity or return the correct failure;
- successful write then read at the same path returns the value;
- writes to disjoint paths commute;
- strict translation either succeeds without taint or rejects;
- pretty-print/parse and generation are deterministic;
- translated evaluation equals native Rust for terminating generated programs.

For generated Rust programs, restrict the grammar to the declared supported subset and include a step/fuel bound. When a mismatch appears, shrink it to a regression fixture.

### 14.4 Proposed CI lanes

| Lane | Trigger | Budget | Contents |
|---|---|---:|---|
| Fast frontend | Every PR | Minutes | fmt, clippy, Rust unit tests, strict negative fixtures, small differential suite |
| Protected proofs | Every PR | Tens of minutes | semantic core, link plugin, assumption diff, selected REVM slice |
| Affected graph | Every PR | Variable | regenerated items and reverse proof dependencies |
| Full corpus | Nightly | Hours | all snapshots, strict coverage report, all nonlegacy Rocq packages |
| Differential REVM | Nightly | Hours | native REVM/Rocq/EELS execution plus EEST fixtures across supported forks |
| Upgrade monitor | Scheduled | Variable | latest rustc/REVM signature and semantic delta, no artifact overwrite |
| Release | Tag | Long | clean container rebuild, byte reproducibility, <code>coqchk</code>, signed manifests |

The full corpus lane should report blacklisted files by reason. An expiring exception with owner and issue is preferable to a bare path.

### 14.5 Release gates

A release described as suitable for verification should require:

- zero fail-open translator paths;
- zero unexpected translation warning in strict examples;
- a supported-subset document generated from code;
- green clean build;
- nonzero frontend unit and differential tests;
- target/compiler/source identity in every artifact;
- proof manifests and protected assumption budgets;
- reproducible generated output;
- all public claims linked to an evidence level.

A REVM milestone additionally requires:

- one pinned REVM revision and explicit fork list;
- no stale link in protected scope;
- no gas placeholder in theorem closure;
- at least one dispatcher-integrated theorem;
- native and independent-oracle differential results;
- a coverage table by evidence level.

## 15. Risk register

| Risk | Likelihood | Impact | Early indicator | Mitigation |
|---|---:|---:|---|---|
| rustc THIR churn repeatedly breaks frontend | High | High | nightly upgrade produces large snapshot diff | Isolate rustc adapter, pin releases, dual-run upgrades, adopt MIR/Charon interchange where useful |
| semantic fixes invalidate many existing proofs | High | High | core definition change touches broad imports | Version semantic profiles; migrate protected slices first; retain legacy profile temporarily |
| assumption dashboard looks worse before it improves | High | Medium | large initial red inventory | Explain classification; use trend and protected-theorem closure, not vanity totals |
| REVM upstream moves faster than proofs | High | High | signature/body delta grows each release | Freeze supported releases; prove delta modules; avoid claiming latest |
| gas and journal semantics dominate schedule | High | High | instruction count rises while integration stalls | Fund vertical end-to-end slices and set composition milestones |
| MIR integration harms readable output | Medium | High | generated CFG becomes difficult to link | Hybrid source view, stable semantic IDs, prototype before migration |
| proof automation creates opaque failures | Medium | Medium | typeclass search timeouts and nonlocal breakage | Explicit generated obligations, tracing, bounded search, deterministic plugin output |
| independent spec differs in representation/fork detail | High | Medium | differential mismatches cluster at normalization | Define relation/normalization explicitly; version fork data; retain raw traces |
| dual licensing discourages adoption or contribution | Medium | Medium | repeated user uncertainty | Publish generated-output and linking guidance; offer clear contributor licensing FAQ |
| team spreads across language breadth and REVM depth | High | High | many partially translated crates, few closed theorems | Platform-first gates, protected vertical slice, explicit out-of-scope list |

## 16. Recommended decisions

### 16.1 Decisions to take now

1. **Adopt strict translation as the only profile eligible for published proofs.**
2. **Freeze v102 for the first REVM vertical slice.**
3. **Treat gas, dispatch, and full observed state as part of instruction correctness.**
4. **Publish theorem assumption closures and evidence levels instead of a single coverage percentage.**
5. **Make the semantic conformance suite a first-class project alongside the proof corpus.**
6. **Use an independent EVM oracle, preferably EELS execution and EEST fixtures plus a formal-semantics cross-check.**
7. **Defer new ecosystem translation campaigns until Phase 0 and the safe-Rust baseline are green.**

### 16.2 Stop/continue gates

After Phase 0:

- continue if strict mode can classify the current REVM instruction corpus without pervasive opaque fallback;
- reconsider the frontend architecture if unsupported/implicit constructs dominate protected functions.

After Phase 1:

- continue with the current deep embedding if native/Rocq conformance is stable and proof migrations are local;
- prioritize MIR/hybrid lowering if Drop, cleanup, and control-flow reconstruction remain error-prone.

After the Phase 3 vertical slice:

- expand REVM if dispatch + gas + host composition yields manageable theorem and upgrade costs;
- narrow the product to instruction-library verification if transaction integration requires assumptions that erase the desired claim;
- investigate reuse of another Rust semantics if the source-to-model correspondence remains the dominant trusted component.

### 16.3 Success metrics

Prefer metrics tied to reduced uncertainty:

- percentage of frontend handlers that are strict, tested, and inside the proved subset;
- number of protected theorems with zero unapproved assumptions;
- median time from a Rust source change to an aligned proof failure;
- number of REVM opcodes at each evidence level R0–R6;
- percentage of protected gas helpers with independent formula proofs;
- number of EEST fixtures matched on complete observed state;
- time and proof-delta size for a rustc or REVM upgrade;
- reproducibility rate of tagged artifacts.

Avoid:

- raw generated lines;
- raw translated-file percentage;
- raw <code>Qed</code> count;
- one “verified percentage” mixing translation, link, simulation, and integration.

## 17. Conclusion

rocq-of-rust has a coherent high-level product idea but not yet a sound source-semantics boundary. Its architecture—source-correlated deep embedding, typed links, and idiomatic simulations—is worth preserving. It exposes proof layers that are often hidden in monolithic automated verifiers and has already shown that the frontend can process difficult production Rust at substantial scale.

The urgent work is not more surface coverage. It is to make unsupported code impossible to mistake for verified code, repair confirmed semantics bugs, identify every theorem's assumptions, and validate the encoding independently. Those changes turn the current large artifact corpus from a demonstration into evidence.

REVM should remain the flagship application, with a narrower and stronger goal: one pinned revision, one fork configuration, and one end-to-end interpreter slice whose translation, link, simulation, gas, dispatch, state effects, and independent EVM correspondence all close. That result would be more valuable than a much larger count of translated or locally simulated functions.

If the platform-first roadmap is followed, the project can occupy a distinctive position between automatic contract verifiers and foundational Rust semantics: an auditable, kernel-checked refinement workflow for selected critical paths in real Rust systems. If fail-open translation, placeholder gas, and unclassified assumptions remain, additional generated coverage will increase apparent scope without increasing assurance.

---

## Appendix A — Confirmed semantic reproducers

### A.1 Signed arithmetic

Native Rust was evaluated with <code>black_box</code> and <code>catch_unwind</code>.

| Expression | Rust result | Current Rocq model |
|---|---:|---:|
| <code>-5_i8 / 2</code> | -2 | -3 |
| <code>-5_i8 % 2</code> | -1 | 1 |
| <code>1_u8 / 0</code> | panic | 0 |
| <code>i8::MIN / -1</code> | panic | -128 |
| <code>i8::MIN % -1</code> | panic | 0 |

The panic cases are mandatory for ordinary division/remainder; they are not controlled solely by release overflow checks. The Rocq column evaluates <code>Integer.normalize_wrap</code> applied to the <code>Z.div</code>/<code>Z.modulo</code> operations selected by <code>BinOp.Wrap</code>; it does not imply that a full translated-program evaluator was run.

### A.2 Oversized shifts

For a runtime right-hand operand of 8:

| Expression | Audited rustc, overflow checks enabled | Audited x86_64 rustc, <code>-C overflow-checks=off -C opt-level=3</code> | Current Rocq model |
|---|---:|---:|---:|
| <code>1_u8 &lt;&lt; 8</code> | panic | 1 | 0 |
| <code>1_u8 &gt;&gt; 8</code> | panic | 1 | 0 |

The release behavior reflects the platform operation used by this compiled test; a model should follow Rust's specified/operator contract and recorded compilation configuration rather than infer all release behavior from this one machine.

### A.3 Range pattern

~~~rust
fn classify(x: u8) -> u8 {
    match x {
        0..=5 => 1,
        _ => 2,
    }
}
~~~

Native Rust returns 2 for input 10. The translation emits a warning but turns the first range pattern into a wildcard, so the Rocq model returns 1.

### A.4 Pointer/index failures

- Native Rust array index 2 on a length-2 array panics.
- <code>Value.read_index</code> at <code>Pointer.Index.Array 2</code> returns <code>None</code>; applying the typed immediate-subpointer/read simulation turns this into <code>BreakMatch</code>, not the same panic.
- A negative model index can alias element zero.
- An out-of-bounds <code>Value.write_index</code> returns <code>Some</code> of the unchanged tuple.

The minimal reproducers used during this audit were kept under <code>/tmp</code>; this appendix records the durable expected cases for conversion into repository tests.

## Appendix B — Metric definitions

- All repository counts use regular files tracked by the superproject. Gitlink contents and build artifacts are excluded.
- Lines are physical newline counts and include blanks, comments, source snippets, and generated boilerplate.
- “Semantic core” comprises <code>M.v</code>, <code>RecordUpdate.v</code>, <code>RocqOfRust.v</code>, <code>lib/Notations.v</code>, and <code>lib/lib.v</code>.
- “Current generated” requires the exact current generator header on the first line.
- “Links,” “simulations,” and “proofs” use path components and exclude generated-header files.
- REVM Rust counts are copied tracked <code>.rs</code> mirrors under <code>RocqOfRust/revm</code>, not the full upstream submodule.
- Syntactic assumption counts do not replace <code>Print Assumptions</code>.
- Simulation lemma counts identify named source declarations; they do not prove that the theorem is assumption-free or independently specified.

## Appendix C — Selected repository checks

~~~sh
git rev-parse HEAD
git submodule status third-party/revm
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --no-fail-fast
make -C RocqOfRust plugin-inline-print-check
make -C RocqOfRust -n jinja
cd RocqOfRust
make revm/revm_interpreter/tests/host.vo -j1
rocq repl
  Require Import revm.revm_interpreter.instructions.simulate.arithmetic.add.
  Print Assumptions add_eq.
~~~

Inventory commands used <code>git ls-files</code>, <code>rg</code>, <code>wc</code>, and path/header classification. Counts should be regenerated by a checked-in metrics script before external publication.

## Appendix D — Primary external references

Rust verification and semantics:

- [Aeneas repository and documentation](https://github.com/AeneasVerif/aeneas)
- [Hax repository and backend status](https://github.com/cryspen/hax)
- [RefinedRust project](https://plv.mpi-sws.org/refinedrust/)
- [Creusot guide](https://creusot.rs/)
- [Verus repository](https://github.com/verus-lang/verus)
- [Kani documentation](https://model-checking.github.io/kani/)
- [MiniRust repository](https://github.com/minirust/minirust)
- [Foundational VeriFast paper](https://arxiv.org/abs/2601.13727)
- [VeriFast Rust reference](https://verifast.github.io/verifast/rust-reference/)
- [Prusti repository](https://github.com/viperproject/prusti-dev)

REVM and EVM:

- [REVM repository](https://github.com/bluealloy/revm)
- [REVM releases](https://github.com/bluealloy/revm/releases)
- [Formal Land REVM grant report, 2026-02-15](https://formal.land/reports/2026-02-15_revm-formal-specification.pdf)
- [Ethereum execution specifications](https://github.com/ethereum/execution-specs)
- [Ethereum execution-specification tests](https://github.com/ethereum/execution-spec-tests)
- [KEVM overview](https://docs.runtimeverification.com/kevm/overview)
- [Verifereum](https://verifereum.org/)
- [Isabelle/EVM FMBC 2026 paper](https://drops.dagstuhl.de/entities/document/10.4230/OASIcs.FMBC.2026.3)

External status was checked on 2026-07-13. Project capabilities and upstream version numbers should be refreshed before the report is used publicly.
