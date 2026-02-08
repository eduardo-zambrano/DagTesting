/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# DAG Definitions and Basic Properties (Finite State Spaces)

This file defines directed acyclic graphs (DAGs) on finite vertex sets,
along with basic structural properties and concrete DAG instances.

## Main definitions

* `FinDAG n`: A DAG on `Fin n` vertices with parent sets and acyclicity
* `FinDAG.children`: Child set of a vertex
* `FinDAG.edges`: Edge set as a `Finset`
* Concrete instances: `chain3`, `fork3`, `collider3`, `independent3`, `diamond4`

## Paper reference

* Definition 2.1 (DAG) in Zambrano (2026), "Testing Causal DAG Structures
  via Moment Inequalities"
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.IntervalCases

open Finset

/-!
## Core DAG Definition

A `FinDAG n` consists of:
1. A parent function `parents : Fin n → Finset (Fin n)`
2. No self-loops: `∀ i, i ∉ parents i`
3. Acyclicity: existence of a height function `f : Fin n → ℕ` such that
   parents have strictly smaller height
-/

/-- A directed acyclic graph on `Fin n` vertices.

    Paper reference: Definition 2.1.

    The acyclicity condition is witnessed by a height function: for every
    edge j → i (meaning j ∈ parents i), we require f(j) < f(i).
    This is equivalent to the standard definition of acyclicity. -/
structure FinDAG (n : ℕ) where
  /-- The parent set of each vertex -/
  parents : Fin n → Finset (Fin n)
  /-- No vertex is its own parent -/
  no_self_loop : ∀ i, i ∉ parents i
  /-- Acyclicity: witnessed by a height function -/
  acyclic : ∃ (f : Fin n → ℕ), ∀ i j, j ∈ parents i → f j < f i

/-- The child set of vertex i: all vertices that have i as a parent. -/
def FinDAG.children {n : ℕ} (G : FinDAG n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => i ∈ G.parents j)

/-- A vertex is a root if it has no parents. -/
def FinDAG.isRoot {n : ℕ} (G : FinDAG n) (i : Fin n) : Prop :=
  G.parents i = ∅

/-- A vertex is a leaf if it has no children. -/
def FinDAG.isLeaf {n : ℕ} (G : FinDAG n) (i : Fin n) : Prop :=
  G.children i = ∅

/-- G₁ is a subgraph of G₂ if every parent in G₁ is also a parent in G₂. -/
def FinDAG.IsSubDAG {n : ℕ} (G₁ G₂ : FinDAG n) : Prop :=
  ∀ i, G₁.parents i ⊆ G₂.parents i

/-!
## Basic Lemmas
-/

/-- If j is a parent of i, then j ≠ i. -/
theorem FinDAG.parent_ne {n : ℕ} (G : FinDAG n) (i j : Fin n) (h : j ∈ G.parents i) :
    j ≠ i := by
  intro heq
  rw [heq] at h
  exact G.no_self_loop i h

/-- If j is a parent of i, the height of j is strictly less than that of i. -/
theorem FinDAG.height_parent_lt {n : ℕ} (G : FinDAG n) :
    ∃ (f : Fin n → ℕ), ∀ i j, j ∈ G.parents i → f j < f i :=
  G.acyclic

/-- j ∈ G.children i ↔ i ∈ G.parents j. -/
theorem FinDAG.mem_children_iff {n : ℕ} (G : FinDAG n) (i j : Fin n) :
    j ∈ G.children i ↔ i ∈ G.parents j := by
  simp [FinDAG.children]

/-- SubDAG is reflexive. -/
theorem FinDAG.IsSubDAG.refl {n : ℕ} (G : FinDAG n) : G.IsSubDAG G :=
  fun _ => Finset.Subset.refl _

/-- SubDAG is transitive. -/
theorem FinDAG.IsSubDAG.trans {n : ℕ} {G₁ G₂ G₃ : FinDAG n}
    (h₁₂ : G₁.IsSubDAG G₂) (h₂₃ : G₂.IsSubDAG G₃) : G₁.IsSubDAG G₃ :=
  fun i => Finset.Subset.trans (h₁₂ i) (h₂₃ i)

/-!
## Concrete DAG Instances

We define the standard DAG structures on 3 and 4 vertices that are used
throughout the paper and in the numerical examples.

We use pattern matching (Fin.cases) instead of `![]` notation to avoid
reduction issues with `decide`.
-/

/-- The chain DAG on 3 vertices: X₀ → X₁ → X₂.

    This is the canonical Markov chain structure. -/
def chain3 : FinDAG 3 where
  parents := fun i =>
    match i with
    | ⟨0, _⟩ => ∅
    | ⟨1, _⟩ => {⟨0, by omega⟩}
    | ⟨2, _⟩ => {⟨1, by omega⟩}
    | ⟨n + 3, h⟩ => absurd h (by omega)
  no_self_loop := by
    intro ⟨i, hi⟩
    interval_cases i <;> simp
  acyclic := ⟨fun ⟨i, _⟩ => i, by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all <;> omega⟩

/-- The fork DAG on 3 vertices: X₀ ← X₁ → X₂.

    X₁ is a common cause of X₀ and X₂.
    This is Markov equivalent to chain3 under faithfulness. -/
def fork3 : FinDAG 3 where
  parents := fun i =>
    match i with
    | ⟨0, _⟩ => {⟨1, by omega⟩}
    | ⟨1, _⟩ => ∅
    | ⟨2, _⟩ => {⟨1, by omega⟩}
    | ⟨n + 3, h⟩ => absurd h (by omega)
  no_self_loop := by
    intro ⟨i, hi⟩
    interval_cases i <;> simp
  acyclic := ⟨fun ⟨i, _⟩ => match i with | 0 => 1 | 1 => 0 | 2 => 1 | n + 3 => 0, by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all
    all_goals (interval_cases j <;> simp_all)⟩

/-- The collider DAG on 3 vertices: X₀ → X₁ ← X₂.

    X₁ is a common effect (collider) of X₀ and X₂.
    NOT Markov equivalent to chain3 or fork3. -/
def collider3 : FinDAG 3 where
  parents := fun i =>
    match i with
    | ⟨0, _⟩ => ∅
    | ⟨1, _⟩ => {⟨0, by omega⟩, ⟨2, by omega⟩}
    | ⟨2, _⟩ => ∅
    | ⟨n + 3, h⟩ => absurd h (by omega)
  no_self_loop := by
    intro ⟨i, hi⟩
    interval_cases i <;> simp
  acyclic := ⟨fun ⟨i, _⟩ => match i with | 0 => 0 | 1 => 1 | 2 => 0 | n + 3 => 0, by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all
    all_goals (interval_cases j <;> simp_all)⟩

/-- The independent DAG on 3 vertices: no edges.

    X₀, X₁, X₂ are all independent. -/
def independent3 : FinDAG 3 where
  parents := fun _ => ∅
  no_self_loop := by intro i; simp
  acyclic := ⟨fun _ => 0, by intro i j h; simp at h⟩

/-- The diamond DAG on 4 vertices: X₀ → X₁, X₀ → X₂, X₁ → X₃, X₂ → X₃.

    A standard example with two causal paths from X₀ to X₃. -/
def diamond4 : FinDAG 4 where
  parents := fun i =>
    match i with
    | ⟨0, _⟩ => ∅
    | ⟨1, _⟩ => {⟨0, by omega⟩}
    | ⟨2, _⟩ => {⟨0, by omega⟩}
    | ⟨3, _⟩ => {⟨1, by omega⟩, ⟨2, by omega⟩}
    | ⟨n + 4, h⟩ => absurd h (by omega)
  no_self_loop := by
    intro ⟨i, hi⟩
    interval_cases i <;> simp
  acyclic := ⟨fun ⟨i, _⟩ => i, by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all
    all_goals (interval_cases j <;> simp_all)⟩

/-!
## Verification of Concrete Instances
-/

/-- chain3 has 2 edges. -/
theorem chain3_has_two_edges : chain3.parents 0 = ∅ ∧
    chain3.parents 1 = {0} ∧ chain3.parents 2 = {1} := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- fork3 has X₁ as a root. -/
theorem fork3_root : fork3.parents 1 = ∅ := rfl

/-- fork3: X₁ is parent of both X₀ and X₂. -/
theorem fork3_structure : fork3.parents 0 = {1} ∧ fork3.parents 2 = {1} := by
  exact ⟨rfl, rfl⟩

/-- collider3: X₁ has parents X₀ and X₂. -/
theorem collider3_structure :
    collider3.parents 0 = ∅ ∧ collider3.parents 1 = {0, 2} ∧ collider3.parents 2 = ∅ := by
  exact ⟨rfl, rfl, rfl⟩

/-- independent3 has no edges. -/
theorem independent3_no_parents : ∀ i : Fin 3, independent3.parents i = ∅ := by
  intro i; rfl
