/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import NonHamiltonian.List
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Digraph -/

set_option autoImplicit false

namespace NonHamiltonian
universe u
open Std

/-- Simple directed graph with nodes of a `LinearOrder` type. -/
structure Digraph (α : Type u) [LinearOrder α] where
  nodes : Finset α
  edges : Finset (α × α)
  nodes_nonempty  : nodes.Nonempty := by decide
  edges_endnodes  : ∀ e ∈ edges, e.1 ∈ nodes ∧ e.2 ∈ nodes := by decide

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- The node set is non-empty, so its cardinality is not zero. -/
theorem nodes_card_ne_zero {g : Digraph α} : g.nodes.card ≠ 0 :=
  Finset.card_ne_zero.mpr g.nodes_nonempty

/-- The cardinality of the node set is positive. -/
theorem zero_lt_nodes_card {g : Digraph α} : 0 < g.nodes.card :=
  Finset.card_pos.mpr g.nodes_nonempty

/-- The canonical sorted list of nodes. -/
def nodeList (g : Digraph α) : List α := g.nodes.sort (· ≤ ·)

-- The shared index set for steps and node positions.
def indices (g : Digraph α) : List (Fin g.nodeList.length) :=
  List.finRange g.nodeList.length

theorem nodeList_length {g : Digraph α} : g.nodeList.length = g.nodes.card :=
  Finset.length_sort _

theorem nodeList_nodup {g : Digraph α} : g.nodeList.Nodup :=
  Finset.sort_nodup _ _

theorem nodeList_nonempty {g : Digraph α} : g.nodeList ≠ [] :=
  List.ne_nil_of_length_pos (g.nodeList_length ▸ g.zero_lt_nodes_card)

theorem mem_nodeList_iff {g : Digraph α} {a : α} : a ∈ g.nodeList ↔ a ∈ g.nodes :=
  Finset.mem_sort _

-- Membership of a nodeList element in g.nodes.
theorem nodeList_mem {g : Digraph α} (i : Fin g.nodeList.length) :
    g.nodeList[i]'i.isLt ∈ g.nodes :=
  g.mem_nodeList_iff.mp (List.getElem_mem i.isLt)

-- Converts a nodeList Fin index to a nodes.card bound.
theorem nodeList_stepLt {g : Digraph α} (i : Fin g.nodeList.length) :
    i.val < g.nodes.card :=
  g.nodeList_length ▸ i.isLt

end Digraph


/-! ## Hamiltonian Path -/

/-- A Hamiltonian path in a digraph `g` is a list of nodes `path` such that:
(i) `path` is a permutation of the canonical node list of `g`; and
(ii) there is an edge in `g` for each consecutive pair of nodes in `path`. -/
structure Digraph.HamiltonianPath
    {α : Type u} [LinearOrder α] (g : Digraph α) where
  path : List α
  path_perm : path.Perm g.nodeList := by decide
  path_conn : path.connect.all (fun e => decide (e ∈ g.edges)) := by decide

namespace Digraph.HamiltonianPath
variable {α : Type u} [LinearOrder α]

/-- A Hamiltonian path visits every node exactly once, so its length equals
  `g.nodes.card`. -/
theorem path_length {g : Digraph α} {p : HamiltonianPath g} :
    p.path.length = g.nodes.card := by
  rw [← g.nodeList_length]; exact List.Perm.length_eq p.path_perm

/-- A Hamiltonian path is non-empty because the graph has at least one node. -/
theorem path_nonempty {g : Digraph α} {p : HamiltonianPath g} :
    p.path ≠ [] := by
  apply List.ne_nil_of_length_pos; rw [path_length]
  exact g.zero_lt_nodes_card

/-- Every consecutive pair in a Hamiltonian path is an edge of `g`. -/
theorem path_conn_subset_edges {g : Digraph α} {p : HamiltonianPath g} :
    ∀ e ∈ p.path.connect, e ∈ g.edges := by
  intro e he
  have h := List.all_eq_true.mp p.path_conn e he
  simpa [decide_eq_true_eq] using h

end Digraph.HamiltonianPath

/-! ## The Hamiltonian path property -/

namespace Digraph
variable {α : Type u} [LinearOrder α]

/-- Logical characterization of the Hamiltonian path property. -/
def HasHamiltonianPath (g : Digraph α) : Prop :=
  Nonempty (HamiltonianPath g)

/-- Algorithmic characterization of the Hamiltonian path property. -/
def hasHamiltonianPath (g : Digraph α) : Bool :=
  g.nodeList.perms.any (fun p => p.connect.all (fun e => decide (e ∈ g.edges)))

/-- Searches for a Hamiltonian path in `g` by trying all permutations of its
  nodes. Returns `some p` if one is found, `none` otherwise. -/
def findHamiltonianPath? (g : Digraph α) : Option (HamiltonianPath g) :=
  Id.run do
    for hperm : p in g.nodeList.perms do
      if hconn : p.connect.all (fun e => decide (e ∈ g.edges)) then
        return some ⟨p, List.perm_of_mem_perms hperm, hconn⟩
    return none

/-- `hasHamiltonianPath` decides `HasHamiltonianPath`: the boolean check is
  equivalent to the existence of a Hamiltonian path. -/
theorem hasHamiltonianPath_iff_HasHamiltonianPath {g : Digraph α} :
    g.hasHamiltonianPath ↔ g.HasHamiltonianPath := by
  rw [hasHamiltonianPath, List.any_eq_true, HasHamiltonianPath]
  constructor <;> rintro ⟨p, hperm, hconn⟩
  · exact Nonempty.intro ⟨p, List.perm_of_mem_perms hperm, hconn⟩
  · exact ⟨p, List.mem_perms_of_perm hperm, hconn⟩

instance (g : Digraph α) : Decidable (g.HasHamiltonianPath) :=
  decidable_of_iff (g.hasHamiltonianPath) hasHamiltonianPath_iff_HasHamiltonianPath

end Digraph
