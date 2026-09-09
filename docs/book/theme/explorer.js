/**
 * EVM Opcode Verification Explorer
 * Interactive visualization of the four-stage verification pipeline
 */

const EVMExplorer = {
    currentOpcode: null,
    currentStage: 'rust',
    opcodeData: null,

    // Stage explanations
    stageExplanations: {
        rust: `<strong>Rust Source</strong>: The original Rust implementation from revm. This code is automatically translated to Rocq by rocq-of-rust. The translation preserves the structure while encoding side effects in a monad.`,
        link: `<strong>Link Instance</strong>: Type-resolved version that adds back concrete types and resolves trait instances. The <code>run_symbolic</code> tactic automates most linking proofs by symbolically executing the translated code.`,
        simulate: `<strong>Simulation</strong>: A hand-written Rocq model optimized for proofs. Uses mathematical types (Z instead of machine integers) and simplified structure. Proven equivalent to the linked code.`,
        test: `<strong>Test Cases</strong>: Concrete test cases that validate the simulation using <code>vm_compute</code>. These catch bugs early and serve as documentation for expected behavior.`
    },

    // Sample code for opcodes (in practice, loaded from opcodes.json)
    sampleCode: {
        lt: {
            rust: `(* Original Rust from revm *)
pub fn lt<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::VERYLOW);
    popn_top!([op1], op2, interpreter);
    *op2 = U256::from(op1 < *op2);
}`,
            link: `(* Link instance for LT opcode *)
Require Import RocqOfRust.RocqOfRust.
Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.instructions.bitwise.

Instance run_lt
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.lt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_lt.`,
            simulate: `(* Simulation for LT opcode *)
Definition op_lt
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if PartialOrd.lt op1 op2 then
        {| Uint.value := 1 |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for LT opcode *)

(** Test that LT correctly computes 25 < 23 = false *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.

(** Test that LT correctly computes 10 < 20 = true *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 20 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.

(** Test that LT correctly computes 5 < 5 = false *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        },
        gt: {
            rust: `(* Original Rust from revm *)
pub fn gt<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::VERYLOW);
    popn_top!([op1], op2, interpreter);
    *op2 = U256::from(op1 > *op2);
}`,
            link: `(* Link instance for GT opcode *)
Instance run_gt
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.gt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.`,
            simulate: `(* Simulation for GT opcode *)
Definition op_gt
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if PartialOrd.gt op1 op2 then
        {| Uint.value := 1 |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for GT opcode *)

(** Test that GT correctly computes 25 > 23 = true *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_gt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        },
        eq: {
            rust: `(* Original Rust from revm *)
pub fn eq<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::VERYLOW);
    popn_top!([op1], op2, interpreter);
    *op2 = U256::from(op1 == *op2);
}`,
            link: `(* Link instance for EQ opcode *)
Instance run_eq
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.eq [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.`,
            simulate: `(* Simulation for EQ opcode *)
Definition op_eq
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if op1 =? op2 then
        {| Uint.value := 1 |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for EQ opcode *)

(** Test that EQ correctly computes 42 = 42 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_eq interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        },
        add: {
            rust: `(* Original Rust from revm *)
pub fn add<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::VERYLOW);
    popn_top!([op1], op2, interpreter);
    *op2 = op1.wrapping_add(*op2);
}`,
            link: `(* Link instance for ADD opcode *)
Instance run_add
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.arithmetic.add [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.`,
            simulate: `(* Simulation for ADD opcode *)
Definition op_add
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result := {| Uint.value := (op1.(Uint.value) + op2.(Uint.value)) mod 2^256 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for ADD opcode *)

(** Test that ADD correctly computes 2 + 3 = 5 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_add interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 5 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        },
        sub: {
            rust: `(* Original Rust from revm *)
pub fn sub<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::VERYLOW);
    popn_top!([op1], op2, interpreter);
    *op2 = op1.wrapping_sub(*op2);
}`,
            link: `(* Link instance for SUB opcode *)
Instance run_sub
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.arithmetic.sub [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.`,
            simulate: `(* Simulation for SUB opcode *)
Definition op_sub
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result := {| Uint.value := (op1.(Uint.value) - op2.(Uint.value)) mod 2^256 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for SUB opcode *)

(** Test that SUB correctly computes 10 - 3 = 7 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sub interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 7 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        },
        mul: {
            rust: `(* Original Rust from revm *)
pub fn mul<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::LOW);
    popn_top!([op1], op2, interpreter);
    *op2 = op1.wrapping_mul(*op2);
}`,
            link: `(* Link instance for MUL opcode *)
Instance run_mul
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.arithmetic.mul [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.`,
            simulate: `(* Simulation for MUL opcode *)
Definition op_mul
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result := {| Uint.value := (op1.(Uint.value) * op2.(Uint.value)) mod 2^256 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for MUL opcode *)

(** Test that MUL correctly computes 6 * 7 = 42 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 6 |};
    {| Uint.value := 7 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_mul interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        },
        div: {
            rust: `(* Original Rust from revm *)
pub fn div<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::LOW);
    popn_top!([op1], op2, interpreter);
    *op2 = op1.checked_div(*op2).unwrap_or_default();
}`,
            link: `(* Link instance for DIV opcode *)
Instance run_div
    {WIRE H : Set} \`{Link WIRE} \`{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.arithmetic.div [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.`,
            simulate: `(* Simulation for DIV opcode *)
Definition op_div
    {WIRE : Set} \`{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    \`{InterpreterTypes.Types.AreLinks WIRE_types}
    \`{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if op2.(Uint.value) =? 0 then
        {| Uint.value := 0 |}
      else
        {| Uint.value := op1.(Uint.value) / op2.(Uint.value) |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).`,
            test: `(* Test cases for DIV opcode *)

(** Test that DIV correctly computes 20 / 4 = 5 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 20 |};
    {| Uint.value := 4 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_div interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 5 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.

(** Test that DIV returns 0 for division by zero *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_div interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof. timeout 1 vm_compute. reflexivity. Qed.`
        }
    },

    // Initialize the explorer
    init: function() {
        this.bindEvents();
        // Default selection
        this.selectOpcode('lt');
        this.selectStage('rust');
    },

    // Bind click events
    bindEvents: function() {
        const self = this;

        // Opcode selection
        document.querySelectorAll('.opcode-item').forEach(function(item) {
            item.addEventListener('click', function() {
                self.selectOpcode(this.dataset.opcode);
            });
        });

        // Tab selection
        document.querySelectorAll('.stage-tabs .tab').forEach(function(tab) {
            tab.addEventListener('click', function() {
                self.selectStage(this.dataset.stage);
            });
        });

        // Pipeline stage selection
        document.querySelectorAll('.pipeline-stage').forEach(function(stage) {
            stage.addEventListener('click', function() {
                self.selectStage(this.dataset.stage);
            });
        });
    },

    // Select an opcode
    selectOpcode: function(opcode) {
        this.currentOpcode = opcode;

        // Update sidebar selection
        document.querySelectorAll('.opcode-item').forEach(function(item) {
            item.classList.remove('active');
        });
        const selected = document.querySelector('.opcode-item[data-opcode="' + opcode + '"]');
        if (selected) {
            selected.classList.add('active');
        }

        // Update code display
        this.updateCodeDisplay();
    },

    // Select a stage
    selectStage: function(stage) {
        this.currentStage = stage;

        // Update tabs
        document.querySelectorAll('.stage-tabs .tab').forEach(function(tab) {
            tab.classList.remove('active');
        });
        const selectedTab = document.querySelector('.tab[data-stage="' + stage + '"]');
        if (selectedTab) {
            selectedTab.classList.add('active');
        }

        // Update pipeline visualization
        document.querySelectorAll('.pipeline-stage').forEach(function(pstage) {
            pstage.classList.remove('active');
        });
        const selectedPipeline = document.querySelector('.pipeline-stage[data-stage="' + stage + '"]');
        if (selectedPipeline) {
            selectedPipeline.classList.add('active');
        }

        // Update explanation
        const explanation = document.getElementById('stage-explanation');
        if (explanation && this.stageExplanations[stage]) {
            explanation.innerHTML = this.stageExplanations[stage];
        }

        // Update code display
        this.updateCodeDisplay();
    },

    // Update the code display
    updateCodeDisplay: function() {
        const codeContent = document.getElementById('code-content');
        const opcodeName = document.querySelector('.opcode-name');
        const filePath = document.querySelector('.file-path');

        if (!codeContent) return;

        const opcodeData = this.sampleCode[this.currentOpcode];
        if (opcodeData && opcodeData[this.currentStage]) {
            codeContent.textContent = opcodeData[this.currentStage];

            // Update header
            if (opcodeName) {
                opcodeName.textContent = this.currentOpcode.toUpperCase();
            }
            if (filePath) {
                // Determine category based on opcode
                const arithmeticOpcodes = ['add', 'sub', 'mul', 'div', 'sdiv', 'mod', 'smod', 'addmod', 'mulmod', 'exp', 'signextend'];
                const category = arithmeticOpcodes.includes(this.currentOpcode) ? 'arithmetic' : 'bitwise';
                const paths = {
                    rust: category + '.v (comment)',
                    link: 'links/' + category + '/' + this.currentOpcode + '.v',
                    simulate: 'simulate/' + category + '/' + this.currentOpcode + '.v',
                    test: 'tests/' + category + '.v'
                };
                filePath.textContent = paths[this.currentStage] || '';
            }

            // Re-apply highlighting
            if (typeof RocqHighlighter !== 'undefined') {
                codeContent.innerHTML = RocqHighlighter.highlight(codeContent.textContent);
            }
        } else {
            codeContent.textContent = '(* Code not available for this opcode/stage combination *)';
        }
    },

    // Load opcode data from JSON (for production use)
    loadOpcodeData: function(url) {
        const self = this;
        fetch(url)
            .then(function(response) {
                return response.json();
            })
            .then(function(data) {
                self.opcodeData = data;
                self.updateCodeDisplay();
            })
            .catch(function(error) {
                console.error('Failed to load opcode data:', error);
            });
    }
};

// Auto-init when DOM is ready
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function() {
        if (document.getElementById('evm-explorer')) {
            EVMExplorer.init();
        }
    });
} else {
    if (document.getElementById('evm-explorer')) {
        EVMExplorer.init();
    }
}
