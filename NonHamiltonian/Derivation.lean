/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph
public import NonHamiltonian.Formula
public import Std.Data.ExtTreeSet

@[expose] public section

/-! # Derivation -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

/-- Derivation context (a set of formulas). -/
abbrev Context {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]
    (g : Digraph α) := ExtTreeSet (Formula g)

/-- Derivation of a formula from a context. -/
inductive Derivation {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]
    {g : Digraph α} : Context g → Formula g → Prop where

  | hypo (p : Formula g) : Derivation {p} p

  | impI {Γ Γ' : Context g} {p q : Formula g} :
      Derivation Γ q → p ∈ Γ → Γ' = Γ.erase p → Derivation Γ' (p.imp q)

  | impE {Γ₁ Γ₂ Γ' : Context g} {p q : Formula g} :
      Derivation Γ₁ p → Derivation Γ₂ (p.imp q) →
      Γ' = Γ₁ ∪ Γ₂ → Derivation Γ' q

infix:21 " ⊢ " => Derivation

macro "app " e:term : tactic =>
  `(tactic| apply ($e : _) <;> try simp [ExtTreeSet.size_insert])

namespace Derivation
variable {α : Type u} [Ord α] [tα : TransOrd α] [LawfulEqOrd α]
variable {g : Digraph α} {p q r : Formula g} {Γ Γ₁ Γ₂ : Context g}

example {p : Formula g} : ∅ ⊢ p.imp p := by
  app Derivation.impI (Derivation.hypo p)

theorem MP (d₁ : Γ₁ ⊢ p) (d₂ : Γ₂ ⊢ p.imp q) : Γ₁ ∪ Γ₂ ⊢ q := by
  app impE d₁ d₂

theorem imp_trans {d₁ : Γ₁ ⊢ p.imp q} {d₂ : Γ₂ ⊢ q.imp r} :
    Γ₁ ∪ Γ₂ ⊢ p.imp r := by
  app impI (MP (MP (hypo p) d₁) d₂)
  sorry

end Derivation
