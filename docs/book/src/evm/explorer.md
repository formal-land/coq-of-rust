# Interactive Explorer

<div id="evm-explorer">
<div class="explorer-header">
<h2>EVM Opcode Verification Explorer</h2>
<p>Explore the four-stage verification pipeline for each opcode</p>
</div>

<div class="explorer-container">
<aside class="opcode-sidebar">
<h3>Opcodes</h3>
<div class="category" data-category="arithmetic">
<h4>Arithmetic</h4>
<ul class="opcode-list">
<li class="opcode-item verified" data-opcode="add">ADD</li>
<li class="opcode-item verified" data-opcode="mul">MUL</li>
<li class="opcode-item verified" data-opcode="sub">SUB</li>
<li class="opcode-item verified" data-opcode="div">DIV</li>
<li class="opcode-item in-progress" data-opcode="sdiv">SDIV</li>
<li class="opcode-item in-progress" data-opcode="mod">MOD</li>
<li class="opcode-item in-progress" data-opcode="smod">SMOD</li>
<li class="opcode-item in-progress" data-opcode="addmod">ADDMOD</li>
<li class="opcode-item in-progress" data-opcode="mulmod">MULMOD</li>
<li class="opcode-item in-progress" data-opcode="exp">EXP</li>
<li class="opcode-item in-progress" data-opcode="signextend">SIGNEXTEND</li>
</ul>
</div>
<div class="category" data-category="bitwise">
<h4>Comparison & Bitwise</h4>
<ul class="opcode-list">
<li class="opcode-item verified" data-opcode="lt">LT</li>
<li class="opcode-item verified" data-opcode="gt">GT</li>
<li class="opcode-item verified" data-opcode="slt">SLT</li>
<li class="opcode-item verified" data-opcode="sgt">SGT</li>
<li class="opcode-item verified" data-opcode="eq">EQ</li>
<li class="opcode-item verified" data-opcode="iszero">ISZERO</li>
<li class="opcode-item verified" data-opcode="bitand">AND</li>
<li class="opcode-item verified" data-opcode="bitor">OR</li>
<li class="opcode-item verified" data-opcode="bitxor">XOR</li>
<li class="opcode-item verified" data-opcode="not">NOT</li>
<li class="opcode-item verified" data-opcode="byte">BYTE</li>
<li class="opcode-item verified" data-opcode="shl">SHL</li>
<li class="opcode-item verified" data-opcode="shr">SHR</li>
<li class="opcode-item verified" data-opcode="sar">SAR</li>
</ul>
</div>
<div class="category" data-category="contract">
<h4>Contract</h4>
<ul class="opcode-list">
<li class="opcode-item verified" data-opcode="call">CALL</li>
<li class="opcode-item verified" data-opcode="call_code">CALLCODE</li>
<li class="opcode-item verified" data-opcode="delegate_call">DELEGATECALL</li>
<li class="opcode-item verified" data-opcode="static_call">STATICCALL</li>
<li class="opcode-item in-progress" data-opcode="create">CREATE</li>
<li class="opcode-item in-progress" data-opcode="create2">CREATE2</li>
<li class="opcode-item in-progress" data-opcode="return">RETURN</li>
<li class="opcode-item in-progress" data-opcode="revert">REVERT</li>
<li class="opcode-item in-progress" data-opcode="selfdestruct">SELFDESTRUCT</li>
</ul>
</div>
<div class="category" data-category="memory">
<h4>Memory</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="mload">MLOAD</li>
<li class="opcode-item in-progress" data-opcode="mstore">MSTORE</li>
<li class="opcode-item in-progress" data-opcode="mstore8">MSTORE8</li>
<li class="opcode-item in-progress" data-opcode="msize">MSIZE</li>
<li class="opcode-item in-progress" data-opcode="mcopy">MCOPY</li>
</ul>
</div>
<div class="category" data-category="stack">
<h4>Stack</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="pop">POP</li>
<li class="opcode-item in-progress" data-opcode="push0">PUSH0</li>
<li class="opcode-item in-progress" data-opcode="push">PUSH</li>
<li class="opcode-item in-progress" data-opcode="dup">DUP</li>
<li class="opcode-item in-progress" data-opcode="swap">SWAP</li>
<li class="opcode-item in-progress" data-opcode="dupn">DUPN</li>
<li class="opcode-item in-progress" data-opcode="swapn">SWAPN</li>
<li class="opcode-item in-progress" data-opcode="exchange">EXCHANGE</li>
</ul>
</div>
<div class="category" data-category="control">
<h4>Control Flow</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="stop">STOP</li>
<li class="opcode-item in-progress" data-opcode="jump">JUMP</li>
<li class="opcode-item in-progress" data-opcode="jumpi">JUMPI</li>
<li class="opcode-item in-progress" data-opcode="rjump">RJUMP</li>
<li class="opcode-item in-progress" data-opcode="rjumpi">RJUMPI</li>
<li class="opcode-item in-progress" data-opcode="pc">PC</li>
<li class="opcode-item in-progress" data-opcode="gas">GAS</li>
<li class="opcode-item in-progress" data-opcode="jumpdest">JUMPDEST</li>
</ul>
</div>
<div class="category" data-category="block_info">
<h4>Block Info</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="chainid">CHAINID</li>
<li class="opcode-item in-progress" data-opcode="coinbase">COINBASE</li>
<li class="opcode-item in-progress" data-opcode="timestamp">TIMESTAMP</li>
<li class="opcode-item in-progress" data-opcode="block_number">NUMBER</li>
<li class="opcode-item in-progress" data-opcode="prevrandao">PREVRANDAO</li>
<li class="opcode-item in-progress" data-opcode="gaslimit">GASLIMIT</li>
<li class="opcode-item in-progress" data-opcode="basefee">BASEFEE</li>
<li class="opcode-item in-progress" data-opcode="blobbasefee">BLOBBASEFEE</li>
</ul>
</div>
<div class="category" data-category="host">
<h4>Host</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="balance">BALANCE</li>
<li class="opcode-item in-progress" data-opcode="selfbalance">SELFBALANCE</li>
<li class="opcode-item in-progress" data-opcode="extcodesize">EXTCODESIZE</li>
<li class="opcode-item in-progress" data-opcode="extcodehash">EXTCODEHASH</li>
<li class="opcode-item in-progress" data-opcode="blockhash">BLOCKHASH</li>
<li class="opcode-item in-progress" data-opcode="sload">SLOAD</li>
<li class="opcode-item in-progress" data-opcode="sstore">SSTORE</li>
<li class="opcode-item in-progress" data-opcode="tload">TLOAD</li>
<li class="opcode-item in-progress" data-opcode="tstore">TSTORE</li>
<li class="opcode-item in-progress" data-opcode="log">LOG</li>
</ul>
</div>
<div class="category" data-category="system">
<h4>System</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="keccak256">KECCAK256</li>
<li class="opcode-item in-progress" data-opcode="address">ADDRESS</li>
<li class="opcode-item in-progress" data-opcode="caller">CALLER</li>
<li class="opcode-item in-progress" data-opcode="callvalue">CALLVALUE</li>
<li class="opcode-item in-progress" data-opcode="calldataload">CALLDATALOAD</li>
<li class="opcode-item in-progress" data-opcode="calldatasize">CALLDATASIZE</li>
<li class="opcode-item in-progress" data-opcode="codesize">CODESIZE</li>
<li class="opcode-item in-progress" data-opcode="returndatasize">RETURNDATASIZE</li>
</ul>
</div>
<div class="category" data-category="data">
<h4>Data (EOF)</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="dataload">DATALOAD</li>
<li class="opcode-item in-progress" data-opcode="dataloadn">DATALOADN</li>
<li class="opcode-item in-progress" data-opcode="datasize">DATASIZE</li>
<li class="opcode-item in-progress" data-opcode="datacopy">DATACOPY</li>
</ul>
</div>
<div class="category" data-category="tx_info">
<h4>TX Info</h4>
<ul class="opcode-list">
<li class="opcode-item in-progress" data-opcode="gasprice">GASPRICE</li>
<li class="opcode-item in-progress" data-opcode="origin">ORIGIN</li>
<li class="opcode-item in-progress" data-opcode="blobhash">BLOBHASH</li>
</ul>
</div>
</aside>

<section class="opcode-detail">
<div class="pipeline-visualization">
<div class="pipeline-stage" data-stage="rust">
<div class="stage-icon">🦀</div>
<div class="stage-label">Rust</div>
<div class="stage-status">Source</div>
</div>
<div class="pipeline-arrow">→</div>
<div class="pipeline-stage" data-stage="link">
<div class="stage-icon">🔗</div>
<div class="stage-label">Link</div>
<div class="stage-status">Types</div>
</div>
<div class="pipeline-arrow">→</div>
<div class="pipeline-stage" data-stage="simulate">
<div class="stage-icon">⚙️</div>
<div class="stage-label">Simulate</div>
<div class="stage-status">Model</div>
</div>
<div class="pipeline-arrow">→</div>
<div class="pipeline-stage" data-stage="test">
<div class="stage-icon">✓</div>
<div class="stage-label">Test</div>
<div class="stage-status">Verify</div>
</div>
</div>

<div class="stage-tabs">
<button class="tab active" data-stage="rust">1. Rust Source</button>
<button class="tab" data-stage="link">2. Link Instance</button>
<button class="tab" data-stage="simulate">3. Simulation</button>
<button class="tab" data-stage="test">4. Test Cases</button>
</div>

<div class="code-display">
<div class="code-header">
<span class="opcode-name">LT</span>
<span class="file-path">bitwise.v</span>
</div>
<pre><code id="code-content" class="language-rocq">Select an opcode from the sidebar to view its verification code.</code></pre>
</div>

<div class="explanation">
<h4>About this stage</h4>
<p id="stage-explanation">
The verification pipeline has four stages. Click on an opcode and tab to explore each stage of the formal verification process.
</p>
</div>
</section>
</div>
</div>

<script>
// Explorer initialization is handled by explorer.js
document.addEventListener('DOMContentLoaded', function() {
    if (typeof EVMExplorer !== 'undefined') {
        EVMExplorer.init();
    }
});
</script>
