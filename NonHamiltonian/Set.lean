/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Std.Data.ExtTreeSet

@[expose] public section

/-! # Set -/

set_option autoImplicit false

universe u

namespace NonHamiltonian
open Std

/-- Finite set of elements of a `LawfulEqOrd` type. -/
abbrev Set (α : Type u) [Ord α] [TransOrd α] [LawfulEqOrd α] := ExtTreeSet α

namespace Set
variable {α: Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]

/-- Builds set from a list `l` of elements. -/
abbrev ofList (l : List α ) : Set α :=
  ExtTreeSet.ofList l

protected def compareLex (a b : Set α) : Ordering :=
  compare a.toList b.toList

instance : Ord (Set α) where
  compare := Set.compareLex

instance : LT (Set α) := ltOfOrd
instance : LE (Set α) := leOfOrd
instance : Min (Set α) := minOfLe
instance : Max (Set α) := maxOfLe

instance : TransOrd (Set α) where
  eq_swap := List.instTransCmpCompareLex.eq_swap
  isLE_trans := List.instTransCmpCompareLex.isLE_trans

protected theorem eq_of_compare {a b : Set α} :
    (compare a b) = .eq → a = b := by
  unfold compare instOrd Set.compareLex; simp
  apply ExtTreeSet.toList_inj.mp

instance : LawfulEqOrd (Set α) where
  eq_of_compare := Set.eq_of_compare

end Set
