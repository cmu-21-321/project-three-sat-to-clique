# 3SAT to CLIQUE in Lean 4

This project formalizes the reduction from 3SAT to CLIQUE in Lean 4 using Mathlib. It constructs a graph with one vertex per literal occurrence and connects vertices from different clauses when their literals do not contradict each other.

The correctness proof shows that a formula is satisfiable if and only if its reduction graph contains a clique whose size equals the number of clauses. It proves both directions using the project's own `Clique.IsClique` and `Clique.HasClique` definitions.

The Lean files in `ProjectTemplate/` define 3SAT, cliques, the reduction graph, and the correctness proof.

To download the Mathlib cache and check the proofs, run:

```sh
lake exe cache get
lake build
```
