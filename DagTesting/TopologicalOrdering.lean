/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Topological Orderings of DAGs

This file defines topological orderings of finite DAGs and proves
that every DAG has at least one topological ordering.

## Main definitions

* `TopologicalOrdering G`: A permutation of `Fin n` that respects DAG edges
* Concrete topological orderings for chain3, fork3, collider3, etc.

## Paper reference

* Definition 3.1 (Topological ordering) in Zambrano (2026)
-/

import DagTesting.DAGBasic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Finset Equiv.Perm

/-!
## Topological Ordering

A topological ordering of a DAG G is a permutation π of Fin n such that
for every edge j → i (i.e., j ∈ parents(i)), we have π⁻¹(j) < π⁻¹(i).
Equivalently, π orders the vertices so that parents come before children.
-/

/-- A topological ordering of a `FinDAG n`.

    A permutation π such that for every edge j → i, the position of j
    in the ordering (π⁻¹ j) precedes the position of i (π⁻¹ i).

    Paper reference: Definition 3.1. -/
structure TopologicalOrdering {n : ℕ} (G : FinDAG n) where
  /-- The permutation giving the ordering -/
  perm : Equiv.Perm (Fin n)
  /-- Parents precede children in the ordering -/
  valid : ∀ i j, j ∈ G.parents i → perm.symm j < perm.symm i

/-!
## Existence of Topological Orderings

Every DAG has at least one topological ordering. The proof uses a ranking
function derived from the height function witnessing acyclicity.
-/

/-- Every DAG has at least one topological ordering.

    The proof constructs a permutation by sorting vertices according to
    the height function witnessing acyclicity. We encode (f i, i.val)
    as a single ℕ via `g i = n * f i + i.val` (a "Cantor-style" encoding
    that is injective and preserves the f-ordering), then define the rank
    of each vertex as the number of vertices with smaller g-value. This
    rank function is an injective map `Fin n → Fin n`, hence a bijection,
    giving the desired permutation. -/
theorem topologicalOrdering_exists {n : ℕ} (G : FinDAG n) :
    Nonempty (TopologicalOrdering G) := by
  obtain ⟨f, hf⟩ := G.acyclic
  -- Encode (f i, i.val) as a single ℕ for a strict total order
  let g : Fin n → ℕ := fun i => n * f i + i.val
  -- g is injective (uniqueness of Euclidean division)
  have hg_inj : Function.Injective g := by
    intro a b heq
    simp only [g] at heq
    have ha := a.isLt; have hb := b.isLt
    suffices hfeq : f a = f b by rw [hfeq] at heq; exact Fin.ext (by omega)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 := Nat.mul_le_mul_left n (show f a + 1 ≤ f b by omega)
      have h2 : n * (f a + 1) = n * f a + n := by ring
      omega
    · have h1 := Nat.mul_le_mul_left n (show f b + 1 ≤ f a by omega)
      have h2 : n * (f b + 1) = n * f b + n := by ring
      omega
  -- f a < f b → g a < g b
  have hg_mono : ∀ a b : Fin n, f a < f b → g a < g b := by
    intro a b hab
    show n * f a + a.val < n * f b + b.val
    have ha := a.isLt
    have h1 := Nat.mul_le_mul_left n (show f a + 1 ≤ f b by omega)
    have h2 : n * (f a + 1) = n * f a + n := by ring
    omega
  -- Rank function: position in sorted order
  let rankSet : Fin n → Finset (Fin n) := fun i => univ.filter (fun j : Fin n => g j < g i)
  have rank_lt : ∀ i : Fin n, (rankSet i).card < n := by
    intro i
    exact lt_of_lt_of_eq
      (Finset.card_lt_card
        (Finset.filter_ssubset.mpr ⟨i, mem_univ i, by simp only [g]; omega⟩))
      (Finset.card_fin n)
  let rank : Fin n → Fin n := fun i => ⟨(rankSet i).card, rank_lt i⟩
  -- Key: rankSet a ⊂ rankSet b when g a < g b
  have h_ssubset : ∀ a b : Fin n, g a < g b → rankSet a ⊂ rankSet b := by
    intro a b hab
    rw [Finset.ssubset_iff_of_subset (fun x hx => by
      simp only [rankSet, mem_filter, mem_univ, true_and] at hx ⊢; omega)]
    exact ⟨a, by simp only [rankSet, mem_filter, mem_univ, true_and]; exact hab,
              by simp only [rankSet, mem_filter, mem_univ, true_and, not_lt]; omega⟩
  -- Strict monotonicity: g a < g b → rank a < rank b
  have h_strict : ∀ a b : Fin n, g a < g b → rank a < rank b := by
    intro a b hab
    exact Finset.card_lt_card (h_ssubset a b hab)
  -- Injectivity of rank
  have h_inj : Function.Injective rank := by
    intro a b hab
    by_contra hne
    have hgne : g a ≠ g b := fun h => hne (hg_inj h)
    rcases lt_or_gt_of_ne hgne with h | h
    · exact absurd hab (ne_of_lt (h_strict a b h))
    · exact absurd hab (ne_of_gt (h_strict b a h))
  -- Construct permutation from the ranking bijection
  let perm_equiv := Equiv.ofBijective rank (Finite.injective_iff_bijective.mp h_inj)
  exact ⟨⟨perm_equiv.symm, fun i j hji => by
    show perm_equiv j < perm_equiv i
    exact h_strict j i (hg_mono j i (hf i j hji))⟩⟩

/-!
## SubDAG Ordering Inheritance
-/

/-- If G₁ is a sub-DAG of G₂ (fewer edges), then any topological ordering
    of G₂ is also valid for G₁. More edges means more ordering constraints,
    so G₁'s valid orderings are a superset of G₂'s.

    Paper reference: Supports Proposition 6.3 (edge density monotonicity). -/
def topologicalOrdering_of_subDAG {n : ℕ} {G₁ G₂ : FinDAG n}
    (h : G₁.IsSubDAG G₂) (π : TopologicalOrdering G₂) :
    TopologicalOrdering G₁ :=
  ⟨π.perm, fun i j hj => π.valid i j (h i hj)⟩

/-!
## Topological Orderings for Concrete DAGs
-/

/-- The identity is a topological ordering for chain3 (0 → 1 → 2). -/
def chain3_ordering : TopologicalOrdering chain3 where
  perm := 1  -- identity permutation
  valid := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    simp [Equiv.Perm.one_symm]
    interval_cases i <;> simp_all [chain3]
    all_goals (interval_cases j <;> simp_all)

/-- A valid topological ordering for fork3 (0 ← 1 → 2):
    the ordering is (1, 0, 2), i.e., X₁ first, then X₀, then X₂. -/
def fork3_ordering : TopologicalOrdering fork3 where
  perm := Equiv.swap (0 : Fin 3) 1
  valid := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all [fork3]
    all_goals (interval_cases j <;> simp_all [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne] <;> decide)

/-- A valid topological ordering for collider3 (0 → 1 ← 2):
    the ordering (0, 2, 1), i.e., swap positions 1 and 2. -/
def collider3_ordering : TopologicalOrdering collider3 where
  perm := Equiv.swap (1 : Fin 3) 2
  valid := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all [collider3]
    all_goals (interval_cases j <;> simp_all [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne] <;> decide)

/-- The identity is a topological ordering for independent3 (no edges). -/
def independent3_ordering : TopologicalOrdering independent3 where
  perm := 1
  valid := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    interval_cases i <;> simp_all [independent3]

/-- The identity is a topological ordering for diamond4. -/
def diamond4_ordering : TopologicalOrdering diamond4 where
  perm := 1
  valid := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hmem
    simp [Equiv.Perm.one_symm]
    interval_cases i <;> simp_all [diamond4]
    all_goals (interval_cases j <;> simp_all)

/-!
## Properties of Topological Orderings
-/

/-- Roots appear before all their children in any topological ordering. -/
theorem TopologicalOrdering.root_early {n : ℕ} {G : FinDAG n}
    (π : TopologicalOrdering G) {i j : Fin n}
    (hj : j ∈ G.parents i) : π.perm.symm j < π.perm.symm i :=
  π.valid i j hj

/-- The permutation of a topological ordering is injective. -/
theorem TopologicalOrdering.perm_injective {n : ℕ} {G : FinDAG n}
    (π : TopologicalOrdering G) : Function.Injective π.perm :=
  π.perm.injective
