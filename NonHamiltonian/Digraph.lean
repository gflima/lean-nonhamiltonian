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

abbrev Node    := Nat
abbrev Edge    := Nat × Nat
abbrev NodeSet := Std.ExtTreeSet Node
abbrev EdgeSet := Std.ExtTreeSet Edge lexOrd.compare

structure Digraph where
  nodes          : NodeSet
  edges          : EdgeSet
  nodes_nonempty : nodes ≠ ∅ := by decide
  edges_endnodes : edges.toList.all (λ (l,r) ↦
    nodes.contains l && nodes.contains r) := by decide
  deriving Repr

namespace Digraph

theorem nodes_size_ne_zero {g : Digraph} : g.nodes.size ≠ 0 := by
  simp [← g.nodes.eq_empty_iff_size_eq_zero, g.nodes_nonempty]

theorem zero_lt_nodes_size {g : Digraph} : 0 < g.nodes.size := by
  rw [← Nat.ne_zero_iff_zero_lt]; exact g.nodes_size_ne_zero

theorem edges_endnodes' {g : Digraph} :
    ∀ e ∈ g.edges, e.1 ∈ g.nodes ∧ e.2 ∈ g.nodes := by
  simp only [← g.edges.mem_toList, ← g.nodes.contains_iff_mem,
    ← Bool.and_eq_true]; exact List.all_eq_true.mp g.edges_endnodes

/-! ## Hamiltonian Path -/

structure HamiltonianPath (g : Digraph) where
  path      : List Node
  path_perm : path.Perm g.nodes.toList := by decide
  path_conn : path.connect.all g.edges.contains := by decide
  deriving Repr, DecidableEq

namespace HamiltonianPath

theorem path_length {g : Digraph} {p : HamiltonianPath g} :
    p.path.length = g.nodes.size := by
  rw [← g.nodes.length_toList]; exact List.Perm.length_eq p.path_perm

theorem path_nonempty {g : Digraph} {p : HamiltonianPath g} :
    p.path ≠ [] := by
  apply List.ne_nil_of_length_pos; rw [path_length]
  exact g.zero_lt_nodes_size

theorem path_conn_subset_edges {g : Digraph} {p :HamiltonianPath g} :
    p.path.connect.Subset g.edges.toList := by
  intro e; rw [g.edges.mem_toList]; exact List.all_eq_true.mp p.path_conn e

end HamiltonianPath

def Hamiltonian (g : Digraph) : Prop :=
  Nonempty (HamiltonianPath g)

/-- Tests whether digraph is Hamiltonian. -/
def isHamiltonian (g : Digraph) : Bool :=
  g.nodes.toList.perms.any (·.connect.all g.edges.contains)

-- TODO: Relate this to isHamiltonian.
def findHamiltonianPath? (g : Digraph) : Option (HamiltonianPath g) :=
  Id.run do
    for hperm : p in g.nodes.toList.perms do
      if hconn : p.connect.all g.edges.contains then
        return some ⟨p, List.perm_of_mem_perms hperm, hconn⟩
    return none

theorem isHamiltonian_iff_Hamiltonian {g : Digraph} :
    g.isHamiltonian ↔ g.Hamiltonian := by
  rw [isHamiltonian, List.any_eq_true, Hamiltonian]
  constructor <;> rintro ⟨p, hperm, hconn⟩
  · exact Nonempty.intro ⟨p, List.perm_of_mem_perms hperm, hconn⟩
  · exists p; exact ⟨List.mem_perms_of_perm hperm, hconn⟩

instance (g : Digraph) : Decidable (g.Hamiltonian) :=
  decidable_of_iff (g.isHamiltonian) isHamiltonian_iff_Hamiltonian

end Digraph
