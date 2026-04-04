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
  edges_nodes    : edges.toList.all (λ (l,r) ↦
    nodes.contains l && nodes.contains r) := by decide
  deriving Repr

namespace Digraph

theorem nodes_size_ne_zero (g : Digraph) : g.nodes.size ≠ 0 := by
  simp [← g.nodes.eq_empty_iff_size_eq_zero, g.nodes_nonempty]

theorem zero_lt_nodes_size (g : Digraph) : 0 < g.nodes.size := by
  rw [← Nat.ne_zero_iff_zero_lt]; exact g.nodes_size_ne_zero

theorem edges_nodes' (g : Digraph) :
    ∀ e ∈ g.edges, e.1 ∈ g.nodes ∧ e.2 ∈ g.nodes := by
  simp only [← g.edges.mem_toList, ← g.nodes.contains_iff_mem,
    ← Bool.and_eq_true]; exact List.all_eq_true.mp g.edges_nodes

/-! ## Hamiltonian Path -/

structure HamiltonianPath (g : Digraph) where
  path        : List Node
  path_nodes  : path.all g.nodes.contains                 := by decide
  nodes_path  : g.nodes.toList.all path.contains          := by decide
  path_length : path.length = g.nodes.size                := by decide
  path_edges  : (path.zip path.tail).all g.edges.contains := by decide

namespace HamiltonianPath

theorem path_nonempty (g : Digraph) (p : HamiltonianPath g) :
    p.path ≠ [] := by
  apply List.ne_nil_of_length_pos; rw [p.path_length]
  exact g.zero_lt_nodes_size

theorem path_nodes' (g : Digraph) (p : HamiltonianPath g) :
    ∀ n ∈ p.path, n ∈ g.nodes := by
  exact p.path.all_eq_true.mp p.path_nodes

theorem nodes_path' (g : Digraph) (p : HamiltonianPath g) :
    ∀ n ∈ g.nodes, n ∈ p.path := by
  simp only [← g.nodes.mem_toList, ← p.path.contains_iff_mem]
  exact List.all_eq_true.mp p.nodes_path

theorem path_edges' (g : Digraph) (p :HamiltonianPath g) :
    ∀ e ∈ p.path.zip p.path.tail, e ∈ g.edges := by
  intro; apply List.all_eq_true.mp p.path_edges

end HamiltonianPath

def hamiltonian (g : Digraph) : Prop :=
  Nonempty (HamiltonianPath g)

def isHamiltonian (g : Digraph) : Bool :=
  g.nodes.toList.perms.any (λ l ↦ (l.zip l.tail).all g.edges.contains)

theorem isHamiltonian_iff_hamiltonian (g : Digraph) :
    g.isHamiltonian ↔ g.hamiltonian := by
  constructor
  · unfold isHamiltonian hamiltonian
    intro h; simp at h
    rcases h with ⟨hl, hr⟩
    sorry
  · sorry

end Digraph
