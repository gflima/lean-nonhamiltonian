/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.List
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! # Digraph -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

/-- Simple directed graph with nodes of a `LinearOrder` type. -/
structure Digraph (α : Type u) [LinearOrder α] where
  nodeList : List α
  edges : Finset (α × α)
  nodes_nodup    : nodeList.Nodup := by decide
  nodes_nonempty : nodeList ≠ [] := by decide
  edges_endnodes : ∀ e ∈ edges, e.1 ∈ nodeList ∧ e.2 ∈ nodeList := by decide

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- The node set as a `Finset`. -/
def nodes (g : Digraph α) : Finset α := g.nodeList.toFinset

theorem mem_nodes_iff {g : Digraph α} {a : α} : a ∈ g.nodes ↔ a ∈ g.nodeList := by
  simp [nodes, List.mem_toFinset]

theorem nodes_size_ne_zero {g : Digraph α} : g.nodes.card ≠ 0 := by
  simp [nodes, List.toFinset_card_of_nodup g.nodes_nodup,
    List.length_eq_zero_iff, g.nodes_nonempty]

theorem zero_lt_nodes_size {g : Digraph α} : 0 < g.nodes.card := by
  rw [← Nat.ne_zero_iff_zero_lt]; exact g.nodes_size_ne_zero

theorem nodeList_length_eq_card {g : Digraph α} : g.nodeList.length = g.nodes.card := by
  simp [nodes, List.toFinset_card_of_nodup g.nodes_nodup]

theorem edges_endnodes' {g : Digraph α} :
    ∀ e ∈ g.edges, e.1 ∈ g.nodes ∧ e.2 ∈ g.nodes := by
  intro e he
  rcases g.edges_endnodes e he with ⟨h1, h2⟩
  exact ⟨mem_nodes_iff.mpr h1, mem_nodes_iff.mpr h2⟩

end Digraph


/-! ## Hamiltonian Path -/

/-- A Hamiltonian path in a digraph `g` is a list of nodes `path` such that:
(i) `path` is a permutation of the nodes of `g`; and
(ii) there is an edge in `g` for each consecutive pair of nodes in `path`. -/
structure Digraph.HamiltonianPath
    {α : Type u} [LinearOrder α] (g : Digraph α) where
  path : List α
  path_perm : path.Perm g.nodeList := by decide
  path_conn : path.connect.all (fun e => decide (e ∈ g.edges)) := by decide

namespace Digraph.HamiltonianPath
variable {α : Type u} [LinearOrder α]

theorem path_length {g : Digraph α} {p : HamiltonianPath g} :
    p.path.length = g.nodes.card := by
  rw [← g.nodeList_length_eq_card]; exact List.Perm.length_eq p.path_perm

theorem path_nonempty {g : Digraph α} {p : HamiltonianPath g} :
    p.path ≠ [] := by
  apply List.ne_nil_of_length_pos; rw [path_length]
  exact g.zero_lt_nodes_size

theorem path_conn_subset_edges {g : Digraph α} {p : HamiltonianPath g} :
    ∀ e ∈ p.path.connect, e ∈ g.edges := by
  intro e he
  have h := List.all_eq_true.mp p.path_conn e he
  simpa [decide_eq_true_eq] using h

end Digraph.HamiltonianPath


/-! ## The Hamiltonian property -/

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- Logical characterization of the Hamiltonian property. -/
def Hamiltonian (g : Digraph α) : Prop :=
  Nonempty (HamiltonianPath g)

/-- Algorithmic characterization of the Hamiltonian property. -/
def isHamiltonian (g : Digraph α) : Bool :=
  g.nodeList.perms.any (fun p => p.connect.all (fun e => decide (e ∈ g.edges)))

def findHamiltonianPath? (g : Digraph α) : Option (HamiltonianPath g) :=
  Id.run do
    for hperm : p in g.nodeList.perms do
      if hconn : p.connect.all (fun e => decide (e ∈ g.edges)) then
        return some ⟨p, List.perm_of_mem_perms hperm, hconn⟩
    return none

theorem isHamiltonian_iff_Hamiltonian {g : Digraph α} :
    g.isHamiltonian ↔ g.Hamiltonian := by
  rw [isHamiltonian, List.any_eq_true, Hamiltonian]
  constructor <;> rintro ⟨p, hperm, hconn⟩
  · exact Nonempty.intro ⟨p, List.perm_of_mem_perms hperm, hconn⟩
  · exact ⟨p, List.mem_perms_of_perm hperm, hconn⟩

instance (g : Digraph α) : Decidable (g.Hamiltonian) :=
  decidable_of_iff (g.isHamiltonian) isHamiltonian_iff_Hamiltonian

end Digraph
