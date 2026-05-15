# Non-Hamiltonian

A Lean 4 formalization of **Claim 2.2** of

> L. Gordeev & E.H. Haeusler (2022). *Proof Compression and NP versus PSPACE II: Addendum.*  Bulletin of the Section of Logic, University of Łódź. [[link]](https://czasopisma.uni.lodz.pl/bulletin/article/view/8755)

## Background

Gordeev & Haeusler 2022 is a paper about the compressibility of natural deduction proofs in the purely implicational fragment of intuitionistic propositional logic (IPL<sub>→</sub>).

Claim 2.2, specifically, concerns the Hamiltonicity of directed graphs.  Recall that:

- A path in a digraph *G* is *Hamiltonian* if it visits every vertex of *G* exactly once.
- Deciding whether such a path exists, `HamiltonianPath G`, is NP-complete.

Claim 2.2 states that:

> For any digraph *G*, `¬ hasHamiltonianPath *G*` if and only if there exists a normal natural deduction proof *π* of `¬ α(*G*)` in IPL<sub>→</sub> with height polynomial in |V(*G*)|.

Here `α(*G*)` is a formula encoding the Hamiltonian path property of *G* in *IPL*<sub>→</sub>.

## Implementation

The formalization builds on [CSLib](https://github.com/leanprover/cslib) and [Mathlib](https://github.com/leanprover-community/mathlib4).

- **`Digraph`** — directed graphs with a `Finset`-based node set and a `LinearOrder` constraint.
- **`Formula`** — propositional formulas over a digraph, defined as
  `Cslib.Logic.PL.Proposition (Atom g)`, where `Atom g` encodes the
  atomic proposition "node *a* is visited at step *i*".
- **`Derivation`** — a sequent calculus for **IPL**<sub>→</sub>, with an `InferenceSystem`
  instance from CSLib so that `⇓s` denotes a derivation of `s.ctx ⊢ s.conc`.

The scoped notation from CSLib is available under `open Cslib.Logic.PL`, e.g.:

```lean
open Cslib.Logic.PL in
#eval ¬ g₁.A 2
```

## Commit Convention

Commit messages follow [Conventional Commits 1.0.0](https://www.conventionalcommits.org/en/v1.0.0/).
