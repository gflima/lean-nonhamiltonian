/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.List
public import Std.Data.ExtTreeSet

@[expose] public section

/-! # Digraph -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

/-- Simple directed graph with nodes of a `LawfulEqOrd` type. -/
structure Digraph (α : Type u) [Ord α] [TransOrd α] [LawfulEqOrd α] where
  nodes : ExtTreeSet α
  edges : ExtTreeSet (α × α) lexOrd.compare
  nodes_nonempty : nodes ≠ ∅ := by decide
  edges_endnodes : edges.toList.all (λ (l,r) ↦
    nodes.contains l && nodes.contains r) := by decide
  deriving Repr

namespace Digraph
variable {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]

theorem nodes_size_ne_zero {g : Digraph α} : g.nodes.size ≠ 0 := by
  simp [← g.nodes.eq_empty_iff_size_eq_zero, g.nodes_nonempty]

theorem zero_lt_nodes_size {g : Digraph α} : 0 < g.nodes.size := by
  rw [← Nat.ne_zero_iff_zero_lt]; exact g.nodes_size_ne_zero

theorem edges_endnodes' {g : Digraph α} :
    ∀ e ∈ g.edges, e.1 ∈ g.nodes ∧ e.2 ∈ g.nodes := by
  simp only [← g.edges.mem_toList, ← g.nodes.contains_iff_mem,
    ← Bool.and_eq_true]
  exact List.all_eq_true.mp g.edges_endnodes

end Digraph

/-! ## Hamiltonian Path -/

/-- A Hamiltonian path in a digraph `g` is a list of nodes `path` such that:
(i) `path` is a permutation of the nodes of `g`; and
(ii) there is an edge in `g` for each consecutive pair of nodes in `path`. -/
structure Digraph.HamiltonianPath
    {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α] (g : Digraph α) where
  path : List α
  path_perm : path.Perm g.nodes.toList := by decide
  path_conn : path.connect.all g.edges.contains := by decide
  deriving Repr

namespace Digraph.HamiltonianPath
variable {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]

theorem path_length {g : Digraph α} {p : HamiltonianPath g} :
    p.path.length = g.nodes.size := by
  rw [← g.nodes.length_toList]; exact List.Perm.length_eq p.path_perm

theorem path_nonempty {g : Digraph α} {p : HamiltonianPath g} :
    p.path ≠ [] := by
  apply List.ne_nil_of_length_pos; rw [path_length]
  exact g.zero_lt_nodes_size

theorem path_conn_subset_edges {g : Digraph α} {p :HamiltonianPath g} :
    p.path.connect.Subset g.edges.toList := by
  intro e; rw [g.edges.mem_toList]; exact List.all_eq_true.mp p.path_conn e

end Digraph.HamiltonianPath

/-! ## The Hamiltonian property -/

namespace Digraph
variable {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]

/-- Logical characterization of the Hamiltonian property. -/
def Hamiltonian (g : Digraph α) : Prop :=
  Nonempty (HamiltonianPath g)

/-- Algorithmic characterization of the Hamiltonian property. -/
def isHamiltonian (g : Digraph α) : Bool :=
  g.nodes.toList.perms.any (·.connect.all g.edges.contains)

-- TODO: Relate this to isHamiltonian.
def findHamiltonianPath? (g : Digraph α) : Option (HamiltonianPath g) :=
  Id.run do
    for hperm : p in g.nodes.toList.perms do
      if hconn : p.connect.all g.edges.contains then
        return some ⟨p, List.perm_of_mem_perms hperm, hconn⟩
    return none

theorem isHamiltonian_iff_Hamiltonian [BEq α] [LawfulBEq α] {g : Digraph α} :
    g.isHamiltonian ↔ g.Hamiltonian := by
  rw [isHamiltonian, List.any_eq_true, Hamiltonian]
  constructor <;> rintro ⟨p, hperm, hconn⟩
  · exact Nonempty.intro ⟨p, List.perm_of_mem_perms hperm, hconn⟩
  · exists p; exact ⟨List.mem_perms_of_perm hperm, hconn⟩

instance [BEq α] [LawfulBEq α] (g : Digraph α) : Decidable (g.Hamiltonian) :=
  decidable_of_iff (g.isHamiltonian) isHamiltonian_iff_Hamiltonian

end Digraph
