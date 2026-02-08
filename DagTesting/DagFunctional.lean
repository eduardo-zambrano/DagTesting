/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# DAG-Specific Carbery Functional

This file defines the DAG-specific Carbery functional Q_n^G and related
concepts, building on the core Carbery functional from CarberyVersionA.

## Main definitions

* `JointPMF.IsMarkovDAG`: Markov factorization property for a DAG
* `JointPMF.bivariateAny`: Bivariate marginal for any pair of variables
* `dagCarberyFunctional`: Q_n^{G,π}(p) — the DAG-specific functional

## Main results

* `dagCarberyFunctional_marginal_sufficiency`: Q_n^G depends only on marginals
* `bivariateAny_eq_bivariateMarginai`: Consecutive pairs match

## Paper reference

* Definition 2.4 (DAG-specific Q_n) in Zambrano (2026)
* Section 3 (Theory) in Zambrano (2026)
-/

import DagTesting.TopologicalOrdering
import CarberyVersionA.Basic

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Markov Factorization for DAGs

A joint PMF `p` is Markov with respect to a DAG `G` if it factorizes as:
  p(x₁, ..., xₙ) = ∏ᵢ p(xᵢ | x_{pa(i)})

In finite state spaces, this is a direct algebraic condition on the PMF.
-/

/-- A joint PMF factorizes according to a DAG (Markov property).

    p(x) = ∏ᵢ p(xᵢ | x_{pa(i)})

    We encode this using local conditional distributions: for each vertex i,
    a function from parent values to a distribution over Ω i.

    Paper reference: Implicit in Section 2 (DAG definition). -/
def JointPMF.IsMarkovDAG (p : JointPMF Ω) (G : FinDAG n) : Prop :=
  ∃ (localCond : ∀ (i : Fin n), (∀ j : G.parents i, Ω j.val) → Ω i → ℝ≥0∞),
    -- Each local conditional sums to 1 over xᵢ
    (∀ i (xpa : ∀ j : G.parents i, Ω j.val),
      ∑ xi : Ω i, localCond i xpa xi = 1) ∧
    -- The joint factorizes as ∏ᵢ localCond_i(x_{pa(i)}, x_i)
    (∀ x : ∀ i, Ω i,
      p.prob x = ∏ i : Fin n, localCond i (fun j => x j.val) (x i))

/-!
## General Bivariate Marginals

For the DAG functional, we need bivariate marginals for arbitrary pairs
of variables, not just consecutive ones.
-/

/-- The bivariate marginal of any two variables (i, j).
    p_{i,j}(s, t) = ∑_{x : xᵢ = s, xⱼ = t} p(x) -/
def JointPMF.bivariateAny (p : JointPMF Ω) (i j : Fin n) (hij : i ≠ j) :
    Ω i → Ω j → ℝ≥0∞ :=
  fun s t => ∑ x : ∀ k, Ω k, if x i = s ∧ x j = t then p.prob x else 0

/-- The bivariate marginal sums correctly over the second variable. -/
theorem JointPMF.bivariateAny_sum_snd (p : JointPMF Ω) (i j : Fin n) (hij : i ≠ j)
    (s : Ω i) :
    ∑ t : Ω j, p.bivariateAny i j hij s t = p.marginal i s := by
  simp only [JointPMF.bivariateAny, JointPMF.marginal]
  -- Swap the order of summation
  rw [Finset.sum_comm]
  -- Now goal: ∑ x, ∑ t, (if x i = s ∧ x j = t then p.prob x else 0) = ∑ x, ...
  congr 1; ext x
  -- For each fixed x, compute ∑ t, (if x i = s ∧ x j = t then p.prob x else 0)
  by_cases hxs : x i = s
  · -- When x i = s: inner sum picks out t = x j, giving p.prob x
    simp [hxs]
  · -- When x i ≠ s: all terms are 0
    simp [hxs]

/-!
## DAG-Specific Carbery Functional

Q_n^{G,π}(p) = ∑_s p_{π(0)}(s₀) · ∏_{k=0}^{n-2} p_{π(k),π(k+1)}(sₖ,sₖ₊₁) · p_{π(n-1)}(sₙ₋₁)

This uses the general bivariate marginals at the ordering-determined pairs.
-/

/-- For a permutation, consecutive positions are always mapped to distinct vertices. -/
theorem perm_consecutive_ne {n : ℕ} (π : Equiv.Perm (Fin n))
    (j : Fin (n - 1)) :
    π ⟨j.val, by omega⟩ ≠ π ⟨j.val + 1, by omega⟩ := by
  intro h
  have h2 := π.injective h
  have h3 : j.val = j.val + 1 := Fin.val_eq_of_eq h2
  omega

/-- The DAG-specific Carbery functional Q_n^{G,π}(p).

    For a DAG G, a joint PMF p, and a topological ordering π of G,
    this is the Carbery functional using bivariate marginals determined
    by the consecutive pairs under ordering π.

    Paper reference: Definition 2.4 (adapted to DAG setting). -/
def dagCarberyFunctional (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) : ℝ≥0∞ :=
  ∑ s : ∀ i, Ω i,
    p.marginal (π.perm ⟨0, by omega⟩)
      (s (π.perm ⟨0, by omega⟩)) *
    (∏ j : Fin (n - 1),
      p.bivariateAny
        (π.perm ⟨j.val, by omega⟩)
        (π.perm ⟨j.val + 1, by omega⟩)
        (perm_consecutive_ne π.perm j)
        (s (π.perm ⟨j.val, by omega⟩))
        (s (π.perm ⟨j.val + 1, by omega⟩))) *
    p.marginal (π.perm ⟨n - 1, by omega⟩)
      (s (π.perm ⟨n - 1, by omega⟩))

/-!
## Consecutive Bivariate Equivalence

For consecutive indices (i, i+1), the general bivariate marginal
equals the consecutive bivariate marginal from CarberyVersionA.
-/

/-- For consecutive indices, `bivariateAny` agrees with `bivariateMarginai`. -/
theorem bivariateAny_eq_bivariateMarginai (p : JointPMF Ω) (i : Fin (n - 1))
    (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) :
    p.bivariateAny
      ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩
      ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩
      (by simp [Fin.ext_iff])
      s t =
    p.bivariateMarginai i s t := by
  simp only [JointPMF.bivariateAny, JointPMF.bivariateMarginai]

/-!
## Marginal Sufficiency for DAG Functional

The DAG functional Q_n^{G,π}(p) depends on p only through:
1. The boundary univariate marginals p_{π(0)} and p_{π(n-1)}
2. The consecutive bivariate marginals p_{π(k),π(k+1)} for k = 0,...,n-2

This extends the marginal sufficiency theorem from CarberyVersionA.
-/

/-- The root form of the DAG Carbery functional:
    Q_n^{G,π}(p) = (dagCarberyFunctional)^{1/(n+1)}.
    This is the analog of `carberyFunctional` from CarberyVersionA.

    The root form is the correct normalization for the test statistic denominator,
    matching the form used in the Carbery inequality axiom. -/
def dagCarberyRoot (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) : ℝ≥0∞ :=
  (dagCarberyFunctional hn G p π) ^ (1 / (n + 1 : ℝ))

/-- Two distributions have the same DAG-relevant marginals if they agree on
    the boundary marginals and the ordering-determined bivariate marginals. -/
def JointPMF.sameDagMarginals (p q : JointPMF Ω) (hn : n ≥ 1)
    {G : FinDAG n} (π : TopologicalOrdering G) : Prop :=
  -- Same boundary marginals under the ordering
  p.marginal (π.perm ⟨0, by omega⟩) = q.marginal (π.perm ⟨0, by omega⟩) ∧
  p.marginal (π.perm ⟨n - 1, by omega⟩) = q.marginal (π.perm ⟨n - 1, by omega⟩) ∧
  -- Same consecutive bivariate marginals under the ordering
  ∀ j : Fin (n - 1),
    p.bivariateAny (π.perm ⟨j.val, by omega⟩) (π.perm ⟨j.val + 1, by omega⟩)
      (perm_consecutive_ne π.perm j) =
    q.bivariateAny (π.perm ⟨j.val, by omega⟩) (π.perm ⟨j.val + 1, by omega⟩)
      (perm_consecutive_ne π.perm j)

/-- **DAG Marginal Sufficiency**: The DAG Carbery functional depends only
    on boundary marginals and ordering-determined bivariate marginals.

    Paper reference: Proposition 6.1 (generalized). -/
theorem dagCarberyFunctional_marginal_sufficiency (hn : n ≥ 1)
    {G : FinDAG n} (π : TopologicalOrdering G) (p q : JointPMF Ω)
    (h : p.sameDagMarginals q hn π) :
    dagCarberyFunctional hn G p π = dagCarberyFunctional hn G q π := by
  simp only [dagCarberyFunctional]
  congr 1
  ext s
  obtain ⟨h1, h2, h3⟩ := h
  -- Rewrite boundary marginals
  have eq1 : p.marginal (π.perm ⟨0, by omega⟩) (s (π.perm ⟨0, by omega⟩)) =
             q.marginal (π.perm ⟨0, by omega⟩) (s (π.perm ⟨0, by omega⟩)) := by
    rw [h1]
  have eq2 : p.marginal (π.perm ⟨n - 1, by omega⟩) (s (π.perm ⟨n - 1, by omega⟩)) =
             q.marginal (π.perm ⟨n - 1, by omega⟩) (s (π.perm ⟨n - 1, by omega⟩)) := by
    rw [h2]
  -- Rewrite bivariate marginals
  have eq3 : ∀ j : Fin (n - 1),
      p.bivariateAny (π.perm ⟨j.val, by omega⟩) (π.perm ⟨j.val + 1, by omega⟩)
        (perm_consecutive_ne π.perm j)
        (s (π.perm ⟨j.val, by omega⟩)) (s (π.perm ⟨j.val + 1, by omega⟩)) =
      q.bivariateAny (π.perm ⟨j.val, by omega⟩) (π.perm ⟨j.val + 1, by omega⟩)
        (perm_consecutive_ne π.perm j)
        (s (π.perm ⟨j.val, by omega⟩)) (s (π.perm ⟨j.val + 1, by omega⟩)) := by
    intro j
    have := h3 j
    rw [this]
  rw [eq1, eq2]
  congr 1
  congr 1
  exact Finset.prod_congr rfl (fun j _ => eq3 j)

end
