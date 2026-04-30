/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph
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

/-! ## Big operators on `Formula` -/

/-- Big conjunction over a list of formulas: `f₀ ∧ f₁ ∧ … ∧ ⊤`. -/
def Formula.bigAnd {α : Type u} [LinearOrder α] {g : Digraph α}
    (fs : List (Formula g)) : Formula g :=
  fs.foldr .and ⊤

/-- Big disjunction over a list of formulas: `f₀ ∨ f₁ ∨ … ∨ ⊥`. -/
def Formula.bigOr {α : Type u} [LinearOrder α] {g : Digraph α}
    (fs : List (Formula g)) : Formula g :=
  fs.foldr .or ⊥

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- Builds a formula stating that node `a` is visited at step `i`. -/
def V (g : Digraph α) (i : Nat) (a : α)
    (hi : i < g.nodes.card := by decide)
    (ha : a ∈ g.nodes := by decide) : Formula g :=
  .atom (.vis i a hi ha)

-- Membership of a nodeList element in g.nodes.
theorem nodeList_mem {g : Digraph α} (i : Fin g.nodeList.length) :
    g.nodeList[i.val]'i.isLt ∈ g.nodes :=
  g.mem_nodeList_iff.mp (List.getElem_mem i.isLt)

-- Converts a nodeList Fin index to a nodes.card bound.
theorem nodeList_stepLt {g : Digraph α} (i : Fin g.nodeList.length) :
    i.val < g.nodes.card :=
  g.nodeList_length ▸ i.isLt

-- The shared index set for steps and node positions.
def indices (g : Digraph α) : List (Fin g.nodeList.length) :=
  List.finRange g.nodeList.length


/-- Builds a formula stating that node `a` is visited in some step. -/
def A (g : Digraph α) (a : α) (ha : a ∈ g.nodes := by decide) :
    Formula g :=
  .bigOr (g.indices.map fun i => g.V i.val a (nodeList_stepLt i) ha)

/-- `B`: every vertex is visited at most once.
    `⋀_{a ∈ V} ⋀_{i ≠ j} (X_{i,a} → (X_{j,a} → ⊥))` -/
def B (g : Digraph α) : Formula g :=
  .bigAnd (g.indices.map fun i =>
    let a   := g.nodeList[i.val]'i.isLt
    let ha  := nodeList_mem i
    let hi' := nodeList_stepLt i
    .bigAnd (g.indices.map fun j =>
      if i = j then ⊤
      else .impl (g.V i.val a hi' ha) (.neg (g.V j.val a (nodeList_stepLt j) ha))))

/-- `C`: at each step at least one vertex is visited.
    `⋀_{i ∈ [n]} ⋁_{a ∈ V} X_{i,a}` -/
def C (g : Digraph α) : Formula g :=
  .bigAnd (g.indices.map fun i =>
    let hi' := nodeList_stepLt i
    .bigOr (g.indices.map fun k =>
      g.V i.val (g.nodeList[k.val]'k.isLt) hi' (nodeList_mem k)))

/-- `D`: at each step at most one vertex is visited.
    `⋀_{i ∈ [n]} ⋀_{v ≠ w} (X_{i,v} → (X_{i,w} → ⊥))` -/
def D (g : Digraph α) : Formula g :=
  .bigAnd (g.indices.map fun i =>
    let hi' := nodeList_stepLt i
    .bigAnd (g.indices.map fun k =>
      let v  := g.nodeList[k.val]'k.isLt
      let hv := nodeList_mem k
      .bigAnd (g.indices.map fun l =>
        let w  := g.nodeList[l.val]'l.isLt
        let hw := nodeList_mem l
        if v = w then ⊤
        else .impl (g.V i.val v hi' hv) (.neg (g.V i.val w hi' hw)))))

/-- `E`: edges are respected.
    `⋀_{(v,w) ∉ E} ⋀_{i ∈ [n-1]} (X_{i,v} → (X_{i+1,w} → ⊥))` -/
def E (g : Digraph α) : Formula g :=
  .bigAnd (g.indices.map fun k =>
    let v  := g.nodeList[k.val]'k.isLt
    let hv := nodeList_mem k
    .bigAnd (g.indices.map fun l =>
      let w  := g.nodeList[l.val]'l.isLt
      let hw := nodeList_mem l
      if (v, w) ∈ g.edges then ⊤
      else
        .bigAnd (g.indices.map fun i =>
          if h : i.val + 1 < g.nodes.card then
            .impl (g.V i.val v (nodeList_stepLt i) hv)
              (.neg (g.V (i.val + 1) w h hw))
          else ⊤)))

end Digraph
