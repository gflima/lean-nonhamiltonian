/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph
public import Mathlib.Data.Finset.Sort
public import Cslib.Logics.Propositional.Defs

@[expose] public section

/-! # Formula -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

/-- Atomic propositions:

 - `vis i a` means that node `a` is visited at step `i`
 - `bot` used to define the negation  -/
inductive Atom {α : Type u} [LinearOrder α] (g : Digraph α) where
  | vis (i : Nat) (a : α) : i < g.nodes.card → a ∈ g.nodes → Atom g
  | bot
  deriving DecidableEq, Repr

instance {α : Type u} [LinearOrder α] {g : Digraph α}
  : Bot (Atom g) := ⟨.bot⟩

/-- Propositional formulas over a digraph, built from `Atom g` via CSLib's
    `Proposition`. -/
abbrev Formula {α : Type u} [LinearOrder α] (g : Digraph α) :=
  Cslib.Logic.PL.Proposition (Atom g)


namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- Builds a formula stating that node `a` is visited at step `i`. -/
def V (g : Digraph α) (i : Nat) (a : α)
    (hi : i < g.nodes.card := by decide)
    (ha : a ∈ g.nodes := by decide) : Formula g :=
  .atom (.vis i a hi ha)

/-- Builds a formula stating that node `a` is visited in some step. -/
def A (g : Digraph α) (a : α) (ha : a ∈ g.nodes := by decide) :
    Formula g :=
  ((g.nodes.sort (· ≤ ·)).mapFinIdx (fun i _ hi => g.V i a
    (by rw [← Finset.length_sort (· ≤ ·)]; exact hi) ha)).foldr
      .or ⊤

end Digraph
