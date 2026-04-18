/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Formula -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

inductive Formula {α : Type u} [LinearOrder α] (g : Digraph α) where
  | vis (i : Nat) (a : α) : i < g.nodes.card → a ∈ g.nodes → Formula g
  | top : Formula g
  | bot : Formula g
  | and : Formula g → Formula g → Formula g
  | or  : Formula g → Formula g → Formula g
  | imp : Formula g → Formula g → Formula g
  deriving Repr, DecidableEq

namespace Formula
variable {α : Type u} [LinearOrder α]
variable {g : Digraph α}

/-- Builds the negation of `p`. -/
abbrev neg (p : Formula g) : Formula g :=
  .imp p .bot

end Formula

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- Builds a formula stating that node `a` is visited at step `i`. -/
def V (g : Digraph α) (i : Nat) (a : α)
    (hi : i < g.nodes.card := by decide)
    (ha : a ∈ g.nodes := by decide) : Formula g :=
  .vis i a hi ha

/-- Builds a formula stating that node `a` is visited in some step. -/
def A (g : Digraph α) (a : α) (ha : a ∈ g.nodes := by decide) :
    Formula g :=
  ((g.nodes.sort (· ≤ ·)).mapFinIdx (fun i _ hi => g.V i a
    (by rw [← Finset.length_sort (· ≤ ·)]; exact hi) ha)).foldr
      Formula.or Formula.top

def g₁ : Digraph Nat := {
  nodeList := {0, 1, 2, 3, 4},
  edges :=
   {(0, 1), (0, 2), (0, 3),
    (2, 1), (3, 2), (3, 4),
    (4, 1), (4, 2), (4, 3)}}

#eval g₁.A 2

end Digraph
