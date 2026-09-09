/**
 * Rocq (Coq) syntax highlighter for mdbook
 * Provides syntax highlighting for Rocq code blocks
 */

const RocqHighlighter = {
    // Keywords - language constructs
    keywords: [
        'Theorem', 'Lemma', 'Definition', 'Fixpoint', 'Inductive', 'CoInductive',
        'Record', 'Structure', 'Class', 'Instance', 'Proof', 'Qed', 'Admitted',
        'Defined', 'Module', 'Import', 'Export', 'Require', 'From', 'Set', 'Unset',
        'Section', 'End', 'Variable', 'Variables', 'Parameter', 'Parameters',
        'Axiom', 'Hypothesis', 'Context', 'Let', 'Notation', 'Coercion',
        'Arguments', 'Implicit', 'Existing', 'Canonical', 'Coercion', 'Ltac',
        'Ltac2', 'Tactic', 'Declare', 'Program', 'Obligation', 'Next', 'Solve',
        'Global', 'Local', 'Opaque', 'Transparent', 'Goal', 'Example', 'Fact',
        'Remark', 'Corollary', 'Proposition', 'Property', 'Add', 'Remove',
        'Hint', 'Resolve', 'Rewrite', 'Unfold', 'Constructors', 'Extern',
        'with', 'as', 'in', 'return', 'match', 'end', 'if', 'then', 'else',
        'fun', 'fix', 'cofix', 'forall', 'exists', 'let', 'where', 'struct',
        'for', 'using'
    ],

    // Tactics - proof commands
    tactics: [
        'intro', 'intros', 'apply', 'exact', 'assumption', 'auto', 'eauto',
        'trivial', 'simpl', 'cbn', 'cbv', 'compute', 'vm_compute', 'native_compute',
        'rewrite', 'replace', 'subst', 'induction', 'destruct', 'case',
        'split', 'left', 'right', 'exists', 'constructor', 'econstructor',
        'reflexivity', 'symmetry', 'transitivity', 'f_equal', 'congruence',
        'discriminate', 'injection', 'inversion', 'clear', 'generalize',
        'specialize', 'pose', 'set', 'remember', 'assert', 'cut', 'enough',
        'exfalso', 'contradiction', 'absurd', 'elim', 'elimtype',
        'unfold', 'fold', 'change', 'pattern', 'red', 'hnf', 'lazy',
        'repeat', 'try', 'first', 'solve', 'now', 'easy', 'tauto', 'intuition',
        'omega', 'lia', 'nia', 'lra', 'nra', 'field', 'ring', 'fourier',
        'eapply', 'rapply', 'refine', 'shelve', 'unshelve', 'admit',
        'move', 'rename', 'revert', 'have', 'suff', 'wlog',
        'run_symbolic', 'typeclasses', 'eauto'
    ],

    // Built-in types
    types: [
        'Prop', 'Type', 'Set', 'SProp',
        'nat', 'bool', 'list', 'option', 'unit', 'Empty_set',
        'True', 'False', 'and', 'or', 'not', 'iff', 'eq', 'ex',
        'prod', 'sum', 'sig', 'sigT', 'sumbool', 'sumor',
        'Z', 'N', 'positive', 'Q', 'R',
        'string', 'ascii', 'byte',
        'Vector.t', 'Fin.t',
        // rocq-of-rust specific
        'Value.t', 'Ty.t', 'M', 'Run.Trait', 'Link'
    ],

    // Built-in functions and constructors
    builtins: [
        'O', 'S', 'nil', 'cons', 'None', 'Some', 'tt',
        'true', 'false', 'pair', 'fst', 'snd',
        'inl', 'inr', 'exist', 'existT',
        'eq_refl', 'I', 'conj', 'or_introl', 'or_intror',
        'length', 'app', 'rev', 'map', 'filter', 'fold_right', 'fold_left',
        'nth', 'nth_error', 'hd', 'tl', 'last',
        'negb', 'andb', 'orb', 'xorb', 'implb',
        'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.div', 'Nat.modulo',
        'Nat.eqb', 'Nat.ltb', 'Nat.leb',
        'Z.add', 'Z.sub', 'Z.mul', 'Z.div', 'Z.modulo',
        'Z.eqb', 'Z.ltb', 'Z.leb', 'Z.of_nat', 'Z.to_nat'
    ],

    // Escape HTML characters
    escapeHtml: function(text) {
        return text
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;');
    },

    // Create a regex pattern from word list
    makeWordPattern: function(words) {
        return new RegExp('\\b(' + words.join('|') + ')\\b', 'g');
    },

    // Highlight a code string
    highlight: function(code) {
        // First escape HTML
        let result = this.escapeHtml(code);

        // Comments: (* ... *)
        result = result.replace(/\(\*[\s\S]*?\*\)/g, '<span class="rocq-comment">$&</span>');

        // Strings
        result = result.replace(/"(?:[^"\\]|\\.)*"/g, '<span class="rocq-string">$&</span>');

        // Numbers
        result = result.replace(/\b(\d+)\b/g, '<span class="rocq-number">$1</span>');

        // Keywords (must be done before types to handle overlap)
        result = result.replace(this.makeWordPattern(this.keywords),
            '<span class="rocq-keyword">$1</span>');

        // Tactics
        result = result.replace(this.makeWordPattern(this.tactics),
            '<span class="rocq-tactic">$1</span>');

        // Types
        result = result.replace(this.makeWordPattern(this.types),
            '<span class="rocq-type">$1</span>');

        // Builtins
        result = result.replace(this.makeWordPattern(this.builtins),
            '<span class="rocq-builtin">$1</span>');

        // Operators
        result = result.replace(/([-+*/%]=?|[<>=!]=|&lt;[-=]?|[-=]&gt;|:=|::|\.\.|\/\\|\\\/|&lt;&gt;|&amp;&amp;|\|\||~)/g,
            '<span class="rocq-operator">$1</span>');

        // Special symbols
        result = result.replace(/(@|#|\$|%|&amp;|\?|`|')/g,
            '<span class="rocq-symbol">$1</span>');

        return result;
    },

    // Highlight all rocq code blocks on the page
    highlightAll: function() {
        // Find code blocks marked as rocq
        document.querySelectorAll('pre code.language-rocq, pre code.language-coq').forEach(function(block) {
            block.innerHTML = RocqHighlighter.highlight(block.textContent);
        });

        // Also handle code blocks inside .rocq class containers
        document.querySelectorAll('.rocq code, .coq code').forEach(function(block) {
            if (!block.classList.contains('highlighted')) {
                block.innerHTML = RocqHighlighter.highlight(block.textContent);
                block.classList.add('highlighted');
            }
        });
    }
};

// Auto-highlight on page load
document.addEventListener('DOMContentLoaded', function() {
    RocqHighlighter.highlightAll();
});

// Re-highlight when mdbook navigation occurs
if (typeof window.book !== 'undefined') {
    window.book.onNavigation = function() {
        setTimeout(function() {
            RocqHighlighter.highlightAll();
        }, 100);
    };
}
