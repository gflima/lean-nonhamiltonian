/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Data.List.InsertIdx
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-! # Extra operations on `List` -/

set_option autoImplicit false

namespace List
universe u
variable {α : Type u}

/-! ## connect -/

/-- The list of pairs of consecutive elements in list. -/
def connect : List α → List (α × α)
  | [] => []
  | a :: l =>
    match l with
    | [] => []
    | a' :: _ => (a, a') :: connect l

theorem connect_eq {l : List α} : l.connect = l.zip l.tail := by
  induction l with simp_all [connect]
  | cons _ l _ => cases l with simp

theorem mem_connect_iff {l : List α} {p : α × α} :
    p ∈ l.connect ↔ ∃ (i : Nat) (_ : i < l.length - 1),
    l[i] = p.1 ∧ l[i+1] = p.2 := by
  induction l with simp_all [connect]
  | cons a l ih =>
    constructor
    · cases l with simp
      | cons _ _ =>
        rintro (_ | h)
        · subst p; exists 0; simp_all
        · rcases ih.mp h with ⟨j, hj, _⟩
          simp at hj; exists j.succ; simp_all
    · rintro ⟨i, hi, _, _⟩
      cases l with
      | nil => simp at hi
      | cons _ _ =>
        cases i with simp_all
        | succ j =>
          right; rw [← ih]; simp_all [connect]
          exists j; simp at hi; simp_all

/-! ## perms -/

/-- Computes all permutations of a list. -/
def perms : List α → List (List α)
  | [] => [[]]
  | a :: l =>
    (perms l).flatMap (λ p ↦
      (List.finRange (p.length + 1)).map (p.insertIdx · a))

theorem mem_perms_self {l : List α} : l ∈ l.perms := by
  induction l with simp_all [perms]
  | cons a l ih =>
    exists l; constructor
    · assumption
    · exists 0

theorem perm_of_mem_perms {l l' : List α} : l' ∈ l.perms → l' ~ l := by
  induction l generalizing l' with simp_all [perms]
  | cons a l ih =>
    intro l₁ hl₁ hfin heq; rw [← heq]
    apply Perm.trans _ ((@perm_cons _ a l₁ l).mpr (ih hl₁))
    apply perm_insertIdx
    apply Nat.le_of_lt_add_one hfin.isLt

theorem mem_perms_of_perm [BEq α] [LawfulBEq α] {l l' : List α} :
    l' ~ l → l' ∈ l.perms := by
  induction l generalizing l' with simp_all [perms]
  | cons a l ih =>
    intro hl'; exists (l'.erase a)
    rcases List.cons_perm_iff_perm_erase.mp hl'.symm with ⟨ha, hl⟩
    constructor
    · apply ih; apply hl.symm
    · have hi : ∃ i, l'.finIdxOf? a = some i := by
        simp only [←Option.isSome_iff_exists, List.isSome_finIdxOf?,
          List.contains_iff_mem]; assumption
      rcases hi with ⟨i, hir⟩
      exists i.castLE ?_
      · simp_all; omega
      · simp [l'.erase_eq_eraseIdx]
        cases hidx : idxOf? a l' with
        | none => simp_all
        | some j =>
          simp [idxOf?_eq_map_finIdxOf?_val, hir] at hidx
          simp [hidx]; subst j
          have heq : a = l'[↑i] := by simp_all
          subst heq
          exact insertIdx_eraseIdx_getElem (by simp_all)

theorem perm_iff_mem_perms [BEq α] [LawfulBEq α] {l l' : List α} :
    l' ~ l ↔ l' ∈ l.perms :=
  ⟨@mem_perms_of_perm _ _ _ l l', @perm_of_mem_perms _ l l'⟩

end List
