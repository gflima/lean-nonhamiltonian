/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph
public import NonHamiltonian.Formula
public import Mathlib.Data.Finset.Basic
public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.InferenceSystem

@[expose] public section


/-! # Derivation -/

set_option autoImplicit false

namespace NonHamiltonian
universe u

open Std
open Cslib.Logic
open Cslib.Logic.PL
open Cslib.Logic.InferenceSystem

/-- Derivation context (a set of formulas).
abbrev Context {α : Type u} [LinearOrder α] (g : Digraph α) :=
  Finset (Formula g)

A sequent pairs a context with a conclusion formula.
structure Sequent {α : Type u} [LinearOrder α] (g : Digraph α) where
  ctx  : Context g
  conc : Formula g

Derivation of a formula from a context.
inductive Derivation {α : Type u} [LinearOrder α]
    {g : Digraph α} : Context g → Formula g → Prop where

  | hypo (p : Formula g) : Derivation {p} p

  | impI {Γ Γ' : Context g} {p q : Formula g} :
      Derivation Γ q → p ∈ Γ → Γ' = Γ.erase p → Derivation Γ' (.impl p q)

  | impE {Γ₁ Γ₂ Γ' : Context g} {p q : Formula g} :
      Derivation Γ₁ p → Derivation Γ₂ (.impl p q) →
      Γ' = Γ₁ ∪ Γ₂ → Derivation Γ' q

infix:21 " ⊢ " => Derivation

`s` is derivable if its conclusion follows from its context.
abbrev Sequent.Derivable {α : Type u} [LinearOrder α] {g : Digraph α}
    (s : Sequent g) : Prop :=
  Cslib.Logic.InferenceSystem.Derivable s

instance {α : Type u} [LinearOrder α] {g : Digraph α} :
    InferenceSystem (Formula g) (@Sequent (Atom g)) where
  derivation s := s.ctx ⊢ s.conc

-/


macro "app " e:term : tactic =>
  `(tactic| apply ($e : _) <;> try simp [Finset.card_insert_of_notMem])


variable {α : Type u} [LinearOrder α]
variable {g : Digraph α} {p q r : Formula g} {Γ Γ₁ Γ₂ : Ctx (Atom g)}

def T := Theory (Atom g)

-- example {p : Formula g} : T⇓(p → p) := by sorry
#check (Theory (Atom g))
#check (Proposition (Atom g))
#check InferenceSystem T (Proposition (Atom g))
#check instInferenceSystemElemPropositionSequent


/-
theorem MP (d₁ : Γ₁ ⊢ p) (d₂ : Γ₂ ⊢ .impl p q) : Γ₁ ∪ Γ₂ ⊢ q := by
  app impE d₁ d₂

theorem imp_trans {d₁ : Γ₁ ⊢ .impl p q} {d₂ : Γ₂ ⊢ .impl q r}
    (hp₁ : p ∉ Γ₁) (hp₂ : p ∉ Γ₂) :
    Γ₁ ∪ Γ₂ ⊢ .impl p r := by
  app impI (MP (MP (hypo p) d₁) d₂)
  rw [Finset.erase_eq_of_notMem]
  simp [hp₁, hp₂]
-/

end NonHamiltonian
