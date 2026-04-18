# Non-Hamiltonian

A Lean 4 formalization of **Claim 2.2** from:

> L. Gordeev & E.H. Haeusler (2022). *Proof Compression and NP versus PSPACE II: Addendum.*
> Bulletin of the Section of Logic, University of Łódź. [[link]](https://czasopisma.uni.lodz.pl/bulletin/article/view/8755)

## Background

The paper argues about the compressibility of natural deduction proofs in the
purely implicational fragment of intuitionistic propositional logic
(**IPC**<sub>→</sub>, in the paper the authors used the notation **M**<sub>imp</sub> and **NM**<sub>imp</sub> for the natural deduction system for this logic, we adopt a more conventional notation).

**Claim 2.2** concerns the Hamiltonicity of directed graphs. Recall:

- A path in a digraph *G* is **Hamiltonian** if it visits every vertex of *G*
  exactly once.
- Deciding whether such a path exists — `HamiltonianPath G` — is NP-complete.

The claim states:

> For any digraph *G*, ¬ `HamiltonianPath G` if and only if there exists a normal
> natural deduction proof *π* of ¬ α(*G*) in **IPC**<sub>→</sub> whose height is
> polynomial in |*V*(*G*)|.

Here α(*G*) is a formula encoding the Hamiltonian path property of *G* in **IPC**<sub>→</sub>.

## Implementation

The formalization builds on [CSLib](https://github.com/leanprover/cslib) and [Mathlib](https://github.com/leanprover-community/mathlib4).

- **`Digraph`** — directed graphs with a `Finset`-based node set and a `LinearOrder` constraint.
- **`Formula`** — propositional formulas over a digraph, defined as
  `Cslib.Logic.PL.Proposition (Atom g)`, where `Atom g` encodes the atomic proposition
  *"node* a *is visited at step* i*"*.
- **`Derivation`** — a sequent calculus for **IPC**<sub>→</sub>, with an `InferenceSystem`
  instance from CSLib so that `⇓s` denotes a derivation of `s.ctx ⊢ s.conc`.

The scoped notation from CSLib is available under `open Cslib.Logic.PL`, e.g.:

```lean
open Cslib.Logic.PL in
#eval ¬ g₁.A 2
```

## Commit Convention

Commit messages follow [Conventional Commits 1.0.0](https://www.conventionalcommits.org/en/v1.0.0/).
