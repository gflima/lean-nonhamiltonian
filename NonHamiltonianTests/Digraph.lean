/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NonHamiltonian
import Mathlib.Data.String.Basic
open NonHamiltonian

def g₀ : Digraph Nat := {
  nodes := {0} ,
  edges := ∅ }

def g₁ : Digraph Nat := {
  nodes := {0, 1, 2, 3, 4},
  edges :=
   {(0, 1), (0, 2), (0, 3),
    (2, 1), (3, 2), (3, 4),
    (4, 1), (4, 2), (4, 3)}}

def g₂ : Digraph Nat := {
  nodes := {0, 1, 2, 3, 4},
  edges := {(0, 1), (1, 2)}}

def g₃ : Digraph String := {
  nodes := {"a", "b", "c"},
  edges := {("a", "a"), ("a", "b"), ("b", "c")} }


-- #eval NonHamiltonian.Digraph.E g₂

/-- info: 1 -/
#guard_msgs in
#eval g₀.nodes.card

/-- info: 0 -/
#guard_msgs in
#eval g₀.edges.card

def p₀ : Digraph.HamiltonianPath g₀ :=
  {path := [0]}

example : g₀.HasHamiltonianPath := by
  exact Nonempty.intro p₀

/-- info: true -/
#guard_msgs in
#eval g₀.hasHamiltonianPath

/-- info: true -/
#guard_msgs in
#eval decide g₀.HasHamiltonianPath

/-- info: true -/
#guard_msgs in
#eval g₀.findHamiltonianPath?.isSome


/-- info: 5 -/
#guard_msgs in
#eval g₁.nodes.card

/-- info: 9 -/
#guard_msgs in
#eval g₁.edges.card

def p₁ : Digraph.HamiltonianPath g₁ := {
  path := [0, 3, 4, 2, 1]
}

example : g₁.HasHamiltonianPath := by
  exact Nonempty.intro p₁

/-- info: true -/
#guard_msgs in
#eval g₁.hasHamiltonianPath

/-- info: true -/
#guard_msgs in
#eval decide g₁.HasHamiltonianPath

/-- info: some [0, 3, 4, 2, 1] -/
#guard_msgs in
#eval g₁.findHamiltonianPath?.map (·.path)

/-- info: false -/
#guard_msgs in
#eval g₂.hasHamiltonianPath

/-- info: false -/
#guard_msgs in
#eval decide g₂.hasHamiltonianPath

/-- info: true -/
#guard_msgs in
#eval g₂.findHamiltonianPath?.isNone

/-- info: true -/
#guard_msgs in
#eval g₃.hasHamiltonianPath

/-- info: some ["a", "b", "c"] -/
#guard_msgs in
#eval g₃.findHamiltonianPath?.map (·.path)
