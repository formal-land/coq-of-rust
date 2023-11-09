Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.ink.erc20.

(* 
PAPERS that contain interesting results and give ideas:
https://gisellereis.com/papers/oracles-types.pdf <- contains simple goals for initial trying outs
https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=8970279
https://link.springer.com/chapter/10.1007/978-3-030-81685-8_15
https://link.springer.com/chapter/10.1007/978-3-030-32409-4_8
https://ieeexplore.ieee.org/abstract/document/8946210 <- Missing access

Blogposts:
https://medium.com/etherscan-blog/verifying-contracts-on-etherscan-f995ab772327
https://programtheblockchain.com/posts/2018/01/16/verifying-contract-source-code/
More thoughts: it can happen that contracts are written by people and thus these contracts needed
  to be verified. When contracts goe larger, then some basic properties for verifying their 
  correctness in each aspects of translactions that involves them could be important. 
  What I want to see from the paper is common properties that need to be verifies for contracts.
  
TODO:
  IDEAS of properties to be proved:
  - First of all, figure out the correct way to express them in Coq code
  - balance_of(Account) >= allowance(Account)
  - balance_of(Account) = balance_of(Account) for all same accounts
  - if two account has same balance, then they will have same effect to others on any transactions
  - ...
*)