/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

@[expose] public section

/-! # Extra operations on `List` -/

set_option autoImplicit false

universe u
variable {α : Type u}

namespace List

/-- Computes all permutations of the given list. -/
def perms : List α → List (List α)
  | [] => [[]]
  | a :: l =>
    (perms l).flatMap (λ p ↦
      (List.finRange (p.length + 1)).map (λ i ↦ p.insertIdx i.val a))

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

theorem insertIdx_eraseIdx_self
    {l : List α} {i : Nat} {a : α} {hi: i < l.length} {ha: a = l[i]} :
    (l.eraseIdx i).insertIdx i a = l := by
  induction l generalizing i with
  | nil => revert hi; simp
  | cons => cases i with simp_all

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
          apply insertIdx_eraseIdx_self <;> simp_all

theorem perm_iff_mem_perms [BEq α] [LawfulBEq α] {l l' : List α} :
    l' ~ l ↔ l' ∈ l.perms :=
  ⟨@mem_perms_of_perm _ _ _ l l', @perm_of_mem_perms _ l l'⟩

end List
