/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph
public import Cslib.Logics.Propositional.Defs
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-! # Formula -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std Cslib.Logic.PL

/-- Atomic propositions:
 - `vis i a` means that node `a` is visited at step `i`
 - `bot` used to define the negation  -/
inductive Atom {α : Type u} [LinearOrder α] (g : Digraph α) where
  | vis (i : Nat) (a : α) : i < g.nodes.card → a ∈ g.nodes → Atom g
  | bot
  deriving DecidableEq, Repr

instance {α : Type u} [LinearOrder α] {g : Digraph α}
  : Bot (Atom g) := ⟨.bot⟩

instance {α : Type u} [LinearOrder α] [Repr α] {g : Digraph α}
    : Repr (Atom g) where
  reprPrec a _ := match a with
    | .vis i x _ _ => "X[" ++ repr i ++ "," ++ repr x ++ "]"
    | .bot         => "⊥"

instance {α : Type u} [LinearOrder α] [Repr α] {g : Digraph α}
    : Repr (Cslib.Logic.PL.Proposition (Atom g)) where
  reprPrec p prec :=
    let rec go : Cslib.Logic.PL.Proposition (Atom g) → Nat → Lean.Format
      | .atom a,   _  => repr a
      | .and a b,  _  => "(" ++ go a 36 ++ " ∧ " ++ go b 36 ++ ")"
      | .or a b,   _  => "(" ++ go a 35 ++ " ∨ " ++ go b 35 ++ ")"
      | .impl a (.atom .bot), _ => "(¬" ++ go a 40 ++ ")"
      | .impl a b, _  => "(" ++ go a 30 ++ " → " ++ go b 30 ++ ")"
    go p prec

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

scoped macro "⋀ " x:ident " in " l:term ", " r:term : term =>
  `(Formula.bigAnd (List.map (fun $x => $r) $l))
scoped macro "⋁ " x:ident " in " l:term ", " r:term : term =>
  `(Formula.bigOr  (List.map (fun $x => $r) $l))

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- Builds a formula stating that node `a` is visited at step `i`. -/
def V (g : Digraph α) (i : Nat) (a : α)
    (hi : i < g.nodes.card := by decide)
    (ha : a ∈ g.nodes := by decide) : Formula g :=
  .atom (.vis i a hi ha)


/-- Builds a formula stating that node `a` is visited in some step. -/
def A (g : Digraph α) (a : α) (ha : a ∈ g.nodes := by decide) : Formula g :=
  ⋁ i in g.indices, g.V i.val a (nodeList_stepLt i) ha

/-- `B`: every vertex is visited at most once.
    `⋀_{a ∈ V} ⋀_{i ≠ j} (X_{i,a} → ¬ (X_{j,a}))` -/
def B (g : Digraph α) : Formula g :=
  ⋀ i in g.indices,
    ⋀ j in g.indices,
      let a  := g.nodeList[i.val]'i.isLt
      let ha := nodeList_mem i
      if i = j then ⊤
      else g.V i.val a (nodeList_stepLt i) ha → ¬ g.V j.val a (nodeList_stepLt j) ha

/-- `C`: at each step at least one vertex is visited.
    `⋀_{i ∈ [n]} ⋁_{a ∈ V} X_{i,a}` -/
def C (g : Digraph α) : Formula g :=
  ⋀ i in g.indices,
    ⋁ k in g.indices,
      g.V i.val (g.nodeList[k.val]'k.isLt) (nodeList_stepLt i) (nodeList_mem k)

/-- `D`: at each step at most one vertex is visited.
    `⋀_{i ∈ [n]} ⋀_{v ≠ w} (X_{i,v} → (X_{i,w} → ⊥))` -/
def D (g : Digraph α) : Formula g :=
  ⋀ i in g.indices,
    ⋀ k in g.indices,
      ⋀ l in g.indices,
        let v  := g.nodeList[k.val]'k.isLt
        let w  := g.nodeList[l.val]'l.isLt
        if v = w then ⊤
        else g.V i.val v (nodeList_stepLt i) (nodeList_mem k) →
             ¬ g.V i.val w (nodeList_stepLt i) (nodeList_mem l)

/-- `E`: edges are respected.
    `⋀_{(v,w) ∉ E} ⋀_{i ∈ [n-1]} (X_{i,v} → (X_{i+1,w} → ⊥))` -/
def E (g : Digraph α) : Formula g :=
  ⋀ k in g.indices,
    ⋀ l in g.indices,
      let v := g.nodeList[k.val]'k.isLt
      let w := g.nodeList[l.val]'l.isLt
      if (v, w) ∈ g.edges then ⊤
      else
        ⋀ i in g.indices,
          if h : i.val + 1 < g.nodes.card then
            g.V i.val v (nodeList_stepLt i) (nodeList_mem k) →
            ¬ g.V (i.val + 1) w h (nodeList_mem l)
          else ⊤

/-- `E₁`: edges are respected (compact form — iterates only over non-edges).
    `⋀_{(v,w) ∉ E} ⋀_{i ∈ [n-1]} (X_{i,v} → (X_{i+1,w} → ⊥))` -/
def E₁ (g : Digraph α) : Formula g :=
  Formula.bigAnd (g.indices.flatMap fun k =>
    g.indices.filterMap fun l =>
      let v := g.nodeList[k.val]'k.isLt
      let w := g.nodeList[l.val]'l.isLt
      if (v, w) ∈ g.edges then none
      else some (⋀ i in g.indices,
        if h : i.val + 1 < g.nodes.card then
          g.V i.val v (nodeList_stepLt i) (nodeList_mem k) →
          ¬ g.V (i.val + 1) w h (nodeList_mem l)
        else ⊤))


end Digraph
