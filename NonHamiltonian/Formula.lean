/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph

/-! # Formula -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

inductive Formula {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]
    (g : Digraph α) where
  | vis (i : Nat) (a : α) : i < g.nodes.size → a ∈ g.nodes → Formula g
  | bot : Formula g
  | and : Formula g → Formula g → Formula g
  | or  : Formula g → Formula g → Formula g
  | imp : Formula g → Formula g → Formula g
  deriving Repr, DecidableEq

namespace Formula
variable {α : Type u} [Ord α] [tα : TransOrd α] [LawfulEqOrd α]
variable {g : Digraph α}

/-- Builds the negation of `p`. -/
abbrev neg (p : Formula g) : Formula g :=
  .imp p .bot

/-- Compares formulas lexicographically. -/
def cmp : Formula g → Formula g → Ordering
  | vis i a .., vis i' a' .. => (compare i i').then (compare a a')
  | bot, bot => .eq
  | and p q, and p' q' => (cmp p p').then (cmp q q')
  | or p q, or p' q' => (cmp p p').then (cmp q q')
  | imp p q, imp p' q' => (cmp p p').then (cmp q q')
  | vis .., _ => .lt
  | _, vis .. => .gt
  | bot, _ => .lt
  | _ , bot => .gt
  | and .., _ => .lt
  | _, and .. => .gt
  | or .., _ => .lt
  | _, or .. => .gt

theorem eq_of_cmp_isEq {p q : Formula g} :
    (cmp p q).isEq → p = q := by
  induction p generalizing q with
  | vis i a _ _ => cases q <;> simp [cmp]
  | bot => cases q <;> simp [cmp]
  | and _ _ ih₁ ih₂ =>
    cases q <;> simp [cmp]; simp only [← Ordering.isEq_iff_eq_eq]
    intro h₁ h₂; exact ⟨ih₁ h₁, ih₂ h₂⟩
  | or _ _ ih₁ ih₂ =>
    cases q <;> simp [cmp]; simp only [← Ordering.isEq_iff_eq_eq]
    intro h₁ h₂; exact ⟨ih₁ h₁, ih₂ h₂⟩
  | imp _ _ ih₁ ih₂ =>
    cases q <;> simp [cmp]; simp only [← Ordering.isEq_iff_eq_eq]
    intro h₁ h₂; exact ⟨ih₁ h₁, ih₂ h₂⟩

theorem cmp_isEq_of_eq {p q : Formula g} :
    p = q → (cmp p q).isEq := by
  intro; subst q; induction p <;> simp_all [cmp]

theorem cmp_isEq_iff_eq {p q : Formula g} :
    (cmp p q).isEq ↔ p = q :=
  ⟨eq_of_cmp_isEq, cmp_isEq_of_eq⟩

@[simp]
theorem cmp_eq_eq_iff_eq {p q : Formula g} :
    cmp p q = .eq ↔ p = q := by
  rw [← Ordering.isEq_iff_eq_eq]; exact cmp_isEq_iff_eq

theorem cmp_swap {p q : Formula g} :
    (cmp p q).swap = cmp q p := by
  induction p generalizing q with
  | vis i a _ _ => cases q <;> simp [cmp, ← i.compare_swap,
      @tα.eq_swap a, Ordering.swap_then]
  | _ => cases q <;> simp_all [cmp, Ordering.swap_then]

theorem cmp_eq_lt_of_lt_lt_isLE {p q r : Formula g}
     (hpq : cmp p q = .lt) (hqr : cmp q r = .lt) :
    (cmp p r).isLE → cmp p r = .lt := by
  intro hpr
  rcases Ordering.isLE_iff_eq_lt_or_eq_eq.mp hpr with (_ | heq)
  · assumption
  · rw [cmp_eq_eq_iff_eq] at heq; subst r
    rw [← cmp_swap] at hpq; simp_all

theorem cmp_eq_lt_of_isLE_lt_isLE {p q r : Formula g}
    (hpq : (cmp p q).isLE) (hqr : cmp q r = .lt) :
    (cmp p r).isLE → cmp p r = .lt := by
  rw [Ordering.isLE_iff_eq_lt_or_eq_eq] at hpq
  rcases hpq with (hpq | hpq)
  · exact cmp_eq_lt_of_lt_lt_isLE hpq hqr
  · rw [cmp_eq_eq_iff_eq] at hpq; subst q; intro; assumption

theorem cmp_eq_lt_of_lt_isLE_isLE {p q r : Formula g}
    (hpq : cmp p q = .lt) (hqr : (cmp q r).isLE) :
    (cmp p r).isLE → cmp p r = .lt := by
  rw [Ordering.isLE_iff_eq_lt_or_eq_eq] at hqr
  rcases hqr with (hqr | hqr)
  · exact cmp_eq_lt_of_lt_lt_isLE hpq hqr
  · rw [cmp_eq_eq_iff_eq] at hqr; subst q; intro; assumption

protected theorem _cmp_isLE_trans_aux {p₁ p₂ q₁ q₂ r₁ r₂ : Formula g}
    (ih₁ : ∀ {p r : Formula g},
      (p.cmp q₁).isLE → (q₁.cmp r).isLE → (p.cmp r).isLE)
    (ih₂ : ∀ {p r : Formula g},
      (p.cmp q₂).isLE → (q₂.cmp r).isLE → (p.cmp r).isLE)
    (le_p₁q₁ : (p₁.cmp q₁).isLE)
    (hpq : p₁.cmp q₁ = Ordering.lt ∨ (p₂.cmp q₂).isLE)
    (le_q₁r₁ : (q₁.cmp r₁).isLE)
    (hqr : q₁.cmp r₁ = Ordering.lt ∨ (q₂.cmp r₂).isLE) :
    (p₁.cmp r₁).isLE ∧ (p₁.cmp r₁ = Ordering.lt ∨ (p₂.cmp r₂).isLE) := by
  rcases hpq with (lt_p₁q₁ | le_p₂q₂) <;>
  rcases hqr with (lt_q₁r₁ | le_q₂r₂) <;>
  constructor <;> try exact ih₁ le_p₁q₁ le_q₁r₁
  · left; exact cmp_eq_lt_of_lt_lt_isLE lt_p₁q₁ lt_q₁r₁
      (ih₁ le_p₁q₁ le_q₁r₁)
  · left; exact cmp_eq_lt_of_lt_isLE_isLE lt_p₁q₁ le_q₁r₁
      (ih₁ le_p₁q₁ le_q₁r₁)
  · left; exact cmp_eq_lt_of_isLE_lt_isLE le_p₁q₁ lt_q₁r₁
      (ih₁ le_p₁q₁ le_q₁r₁)
  · right; exact ih₂ le_p₂q₂ le_q₂r₂

theorem cmp_isLE_trans {p q r : Formula g} :
    (cmp p q).isLE → (cmp q r).isLE → (cmp p r).isLE := by
  induction q generalizing p r with
  | vis _ _ _ _ =>
    cases p with
    | vis _ _ _ _ =>
      cases r with
      | vis _ _ _ _ =>
        simp [cmp, Ordering.isLE_then_iff_and, Nat.isLE_compare,
          Nat.compare_eq_lt]
        rintro le_ij (lt_ij | le_ab) le_jk (lt_jk | le_bc) <;>
        constructor <;> try exact Nat.le_trans le_ij le_jk
        · left; exact Nat.lt_trans lt_ij lt_jk
        · left; exact Nat.lt_of_lt_of_le lt_ij le_jk
        · left; exact Nat.lt_of_le_of_lt le_ij lt_jk
        · right; exact tα.isLE_trans le_ab le_bc
      | _ => simp [cmp]
    | _ => simp [cmp]
  | bot => cases p <;> cases r <;> simp [cmp]
  | and _ _ ih₁ ih₂ =>
    cases p <;> cases r <;> simp [cmp, Ordering.isLE_then_iff_and]
    exact _cmp_isLE_trans_aux ih₁ ih₂
  | or _ _ ih₁ ih₂ =>
    cases p <;> cases r <;> simp [cmp, Ordering.isLE_then_iff_and]
    exact _cmp_isLE_trans_aux ih₁ ih₂
  | imp _ _ ih₁ ih₂ =>
    cases p <;> cases r <;> simp [cmp, Ordering.isLE_then_iff_and]
    exact _cmp_isLE_trans_aux ih₁ ih₂

instance : Ord (Formula g) where
  compare := cmp

instance : LT (Formula g) := ltOfOrd
instance : LE (Formula g) := leOfOrd
instance : Min (Formula g) := minOfLe
instance : Max (Formula g) := maxOfLe

instance : TransOrd (Formula g) where
  eq_swap := cmp_swap.symm
  isLE_trans := cmp_isLE_trans

instance : LawfulEqOrd (Formula g) where
  eq_of_compare := cmp_eq_eq_iff_eq.mp

end Formula

/-- Builds formula stating that node `a` is visited at step `i`. -/
def Digraph.V {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]
    (g : Digraph α) (i : Nat) (a : α)
    (hi : i < g.nodes.size := by decide)
    (ha : a ∈ g.nodes := by decide) : Formula g :=
  .vis i a hi ha

end NonHamiltonian
