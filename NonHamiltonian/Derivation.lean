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



variable {α : Type u} [LinearOrder α]
variable {g : Digraph α} {p q r : Formula g} {Γ Γ₁ Γ₂ : Ctx (Atom g)}

def T (g : Digraph α) : Theory (Atom g) := ∅

-- option 1
example {p : Formula g} : (∅ : Theory (Atom g))⇓(p → p) := by
  exact .implI ∅ (.ass (by grind))

-- option 2
example {p : Formula g} : (T g)⇓(p → p) := by
  -- T g = ∅, então o objetivo é (∅ : Theory (Atom g))⇓(p → p)
  show (∅ : Theory (Atom g))⇓(p → p)
  -- ⇓ expande via instância: Theory.Derivation ∅ (p → p)  (dois ∅ distintos)
  show Theory.Derivation (T := ∅) ∅ (Proposition.impl p p)
  -- implI introduz a implicação: basta derivar p de {p}
  exact .implI ∅ (.ass (Finset.mem_insert_self p ∅))


macro "app " e:term : tactic =>
  `(tactic| apply ($e : _) <;> try simp [Finset.card_insert_of_notMem])


theorem MP {T : Theory (Atom g)}
  (d₁ : DerivableIn T ((Γ₁) ⊢ p))
  (d₂ : DerivableIn T ((Γ₂) ⊢ (p → q)))
  : DerivableIn T ((Γ₁ ∪ Γ₂) ⊢ q) := by
  obtain ⟨D₁⟩ := d₁
  obtain ⟨D₂⟩ := d₂
  exact ⟨.implE (D₂.weak_ctx Finset.subset_union_right)
                (D₁.weak_ctx Finset.subset_union_left)⟩


theorem imp_trans {T : Theory (Atom g)}
  (d₁ : DerivableIn T (Γ₁ ⊢ p → q))
  (d₂ : DerivableIn T (Γ₂ ⊢ q → r))
  : DerivableIn T ((Γ₁ ∪ Γ₂) ⊢ (p → r)) := by
  obtain ⟨D₁⟩ := d₁
  obtain ⟨D₂⟩ := d₂
  exact ⟨
    .implI (Γ₁ ∪ Γ₂)
     (.implE (D₂.weak_ctx (by grind))
       (.implE (D₁.weak_ctx (by grind))
        (.ass (Finset.mem_insert_self p _))))⟩


end NonHamiltonian
