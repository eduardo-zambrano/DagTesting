/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# DAG Test Statistic

This file defines the moment-inequality test statistic for testing
DAG structures using the Carbery functional.

## Main definitions

* `AdmissibleTestFunction`: Nonnegativity condition for test functions
* `testStatistic`: T_h^{G,π}(p) — the test statistic for DAG G
* `combinedTestStatistic`: T_max = max_k T_{h^(k)} over test function classes

## Paper reference

* Definition 4.1 (Test statistic) in Zambrano (2026)
* Proposition 4.1 (Admissible test functions) in Zambrano (2026)
* Proposition 4.3 (Combined test) in Zambrano (2026)
-/

import DagTesting.DagFunctional

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Admissible Test Functions

Test functions h = (h₁, ..., hₙ) must be nonnegative to apply Carbery's inequality.
This is the key admissibility condition.
-/

/-- A family of test functions is admissible if each function is nonnegative.

    Paper reference: Proposition 4.1. -/
def AdmissibleTestFunction (h : ∀ i : Fin n, Ω i → ℝ≥0∞) : Prop :=
  ∀ i s, h i s ≥ 0

/-- Every function to ℝ≥0∞ is automatically admissible (nonnegativity is built in). -/
theorem admissible_of_ennreal (h : ∀ i : Fin n, Ω i → ℝ≥0∞) :
    AdmissibleTestFunction h :=
  fun _ _ => zero_le _

/-!
## Test Statistic

The test statistic T_h^{G,π}(p) is defined as:

  T_h^{G,π}(p) = E[∏ᵢ hᵢ(Xᵢ)] / (Q_n^{G,π}(p) · ∏ᵢ ‖hᵢ‖_{n+1})

Under H₀ (p is Markov for G), Carbery's inequality gives T ≤ 1.
Under H₁ (p is NOT Markov for G), T may exceed 1.

Note: We define the test statistic as a ratio in ℝ≥0∞. The division
by zero case (when the denominator is 0) gives ⊤ (infinity) in ℝ≥0∞,
which is fine because if Q_n = 0 the test is trivially valid.
-/

/-- The expectation of a product of functions under a joint PMF.
    E[∏ᵢ hᵢ(Xᵢ)] = ∑_x p(x) · ∏ᵢ hᵢ(xᵢ) -/
def JointPMF.expectationProd (p : JointPMF Ω) (h : ∀ i : Fin n, Ω i → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i, p.prob x * ∏ i, h i (x i)

/-- The denominator of the test statistic:
    Q_n^{G,π}(p) · ∏ᵢ ‖hᵢ‖_{L^{n+1}(counting)} -/
def testDenominator (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) (h : ∀ i : Fin n, Ω i → ℝ≥0∞) : ℝ≥0∞ :=
  dagCarberyRoot hn G p π * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i)

/-- **Test Statistic** T_h^{G,π}(p).

    T = E[∏ᵢ hᵢ(Xᵢ)] / (Q_n^{G,π}(p) · ∏ᵢ ‖hᵢ‖_{n+1})

    Paper reference: Definition 4.1. -/
def testStatistic (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) (h : ∀ i : Fin n, Ω i → ℝ≥0∞) : ℝ≥0∞ :=
  p.expectationProd h / testDenominator hn G p π h

/-!
## Combined Test Statistic

The combined test uses multiple test function families and takes the maximum.
If any single test rejects, the combined test rejects.
-/

/-- The combined test statistic over a finite set of test functions.
    T_max = max_k T_{h^(k)}

    Paper reference: Proposition 4.3. -/
def combinedTestStatistic (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) {K : ℕ}
    (hs : Fin K → (∀ i : Fin n, Ω i → ℝ≥0∞)) : ℝ≥0∞ :=
  Finset.sup Finset.univ (fun k => testStatistic hn G p π (hs k))

/-!
## Properties of the Test Statistic
-/

/-- The test statistic is nonnegative (automatic for ℝ≥0∞). -/
theorem testStatistic_nonneg (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) (h : ∀ i : Fin n, Ω i → ℝ≥0∞) :
    testStatistic hn G p π h ≥ 0 :=
  zero_le _

/-- The test statistic with constant test functions h_i = 1 equals
    1 / (Q_n^{G,π}(p)^{1/(n+1)} · ∏ ‖1‖), since E[∏ 1] = 1. -/
theorem testStatistic_const_one (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) :
    testStatistic hn G p π (fun _ _ => 1) =
    1 / (dagCarberyRoot hn G p π *
         ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (fun (_ : Ω i) => (1 : ℝ≥0∞))) := by
  simp only [testStatistic, JointPMF.expectationProd, testDenominator]
  congr 1
  simp [Finset.prod_const_one, mul_one, p.sum_eq_one]

/-- If T_h ≤ 1 for all h^(k), then T_max ≤ 1. -/
theorem combinedTestStatistic_le_one (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (π : TopologicalOrdering G) {K : ℕ}
    (hs : Fin K → (∀ i : Fin n, Ω i → ℝ≥0∞))
    (h_each : ∀ k, testStatistic hn G p π (hs k) ≤ 1) :
    combinedTestStatistic hn G p π hs ≤ 1 := by
  simp only [combinedTestStatistic]
  apply Finset.sup_le
  intro k _
  exact h_each k

end
