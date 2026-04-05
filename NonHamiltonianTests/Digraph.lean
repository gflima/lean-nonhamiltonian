/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NonHamiltonian
open NonHamiltonian

def g₀ : Digraph := {
  nodes := {0},
  edges := ∅,
}

/-- info: 1 -/
#guard_msgs in
#eval g₀.nodes.size

/-- info: 0 -/
#guard_msgs in
#eval g₀.edges.size

def p₀ : Digraph.HamiltonianPath g₀ :=
  {path := [0]}

example : g₀.Hamiltonian := by
  exact Nonempty.intro p₀

/-- info: true -/
#guard_msgs in
#eval g₀.isHamiltonian

/-- info: true -/
#guard_msgs in
#eval decide g₀.Hamiltonian

/-- info: true -/
#guard_msgs in
#eval g₀.findHamiltonianPath?.isSome

def g₁ : Digraph := {
  nodes := {0, 1, 2, 3, 4},
  edges :=
   {(0, 1), (0, 2), (0, 3),
    (2, 1), (3, 2), (3, 4),
    (4, 1), (4, 2), (4, 3)}}

/-- info: 5 -/
#guard_msgs in
#eval g₁.nodes.size

/-- info: 9 -/
#guard_msgs in
#eval g₁.edges.size

def p₁ : Digraph.HamiltonianPath g₁ := {
  path := [0, 3, 4, 2, 1]
}

example : g₁.Hamiltonian := by
  exact Nonempty.intro p₁

/-- info: true -/
#guard_msgs in
#eval g₁.isHamiltonian

/-- info: true -/
#guard_msgs in
#eval decide g₁.Hamiltonian

/-- info: some [0, 3, 4, 2, 1] -/
#guard_msgs in
#eval g₁.findHamiltonianPath?.map (·.path)

def g₂ : Digraph := {
  nodes := {0, 1, 2, 3, 4},
  edges := {(0, 1), (1, 2)}}

/-- info: false -/
#guard_msgs in
#eval g₂.isHamiltonian

/-- info: false -/
#guard_msgs in
#eval decide g₂.isHamiltonian

/-- info: true -/
#guard_msgs in
#eval g₂.findHamiltonianPath?.isNone
