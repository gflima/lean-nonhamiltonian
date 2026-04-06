/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.Digraph

/-! # Derivation -/

set_option autoImplicit false

namespace NonHamiltonian

inductive Formula (g : Digraph) where
  | X (i : Nat) (n : Nat) : i < g.nodes.size → n ∈ g.nodes → Formula g
  | bot : Formula g
  | and : Formula g → Formula g → Formula g
  | or  : Formula g → Formula g → Formula g
  | imp : Formula g → Formula g → Formula g
  deriving Repr

namespace Formula

variable {g : Digraph}

def cmp : Formula g → Formula g → Ordering
  | .X i n .., .X i' n' .. => (compare i i').then (compare n n')
  | .X .., _ => .lt
  | .bot, .bot => .eq
  | .bot, _ => .lt
  | .and φ ψ, .and φ' ψ' => (cmp φ φ').then (cmp ψ ψ')
  | .and .., _ => .lt
  | .or φ ψ, .or φ' ψ' => (cmp φ φ').then (cmp ψ ψ')
  | .or .., _ => .lt
  | .imp φ ψ, .imp φ' ψ' => (cmp φ φ').then (cmp ψ ψ')
  | .imp .., _ => .lt

instance : Ord (Formula g) where
  compare := Formula.cmp

instance : LT (Formula g) := ltOfOrd
instance : LE (Formula g) := leOfOrd
instance : Min (Formula g) := minOfLe
instance : Max (Formula g) := maxOfLe

-- theorem eq_swap {φ ψ : Formula g} :
--     compare φ ψ = (compare ψ φ).swap := by
--   simp [compare]
--   induction φ with
--   | X i n _ _ =>
--     cases ψ with
--     | X i' n' _ _ => simp [cmp]; sorry
--     | bot => rw [cmp]
--     | and => sorry
--     | _ => sorry
--   | bot => sorry
--   | and φ₁ φ₂ ih₁ ih₂ => sorry
--   | or φ₁ φ₂ ih₁ ih₂ => sorry
--   | imp φ₁ φ₂ ih₁ ih₂ => sorry

end Formula

def Digraph.X (g : Digraph) (i : Nat) (n : Nat)
    (hi : i < g.nodes.size := by decide)
    (hn : n ∈ g.nodes := by decide) : Formula g :=
  .X i n hi hn

-- abbrev Context (g : Digraph) := Set (Formula g)
-- inductive Derivation (g : Digraph) : Context g → Formula g → Prop where
-- | hypo (φ : Formula g) : Derivation g ({φ} : Context g)

def g : Digraph := {
  nodes := {0, 1, 2, 3, 4},
  edges :=
   {(0, 1), (0, 2), (0, 3),
    (2, 1), (3, 2), (3, 4),
    (4, 1), (4, 2), (4, 3)}}

#eval (g.X 4 4) <  Formula.bot


-- set_option trace.Meta.synthInstance true
-- #check ({g.X 4 4} : Context g)
