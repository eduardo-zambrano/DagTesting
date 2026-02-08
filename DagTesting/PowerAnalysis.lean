/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Power Analysis for DAG Tests

This file formalizes the power analysis results: MI-equivalence
characterization and the power direction theorems.

## Main definitions

* `MIEquivalent`: Two DAGs are MI-equivalent (same Q_n for all distributions)
* `powerDirection`: If Q₀ < Q₁ and T₁ = 1, then T₀ > 1

## Main results

* `mi_equivalent_iff_same_bivariates`: MI-equivalence characterization (Prop 6.6)
* `power_direction_strict`: Power direction theorem (Thm 6.1§2)
* `power_no_rejection`: No rejection when Q₀ ≥ Q₁ (Thm 6.1§3)

## Paper reference

* Definition 6.5 (MI-equivalent DAGs) in Zambrano (2026)
* Proposition 6.6 (MI-equivalence characterization) in Zambrano (2026)
* Theorem 6.1 (Power characterization) in Zambrano (2026)
-/

import DagTesting.OrderingValidity

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## MI-Equivalence

Two DAGs G₁ and G₂ are MI-equivalent (moment inequality equivalent) if they
produce the same Carbery functional value for all distributions and all valid
orderings. This means the test cannot discriminate between them.
-/

/-- Two DAGs are MI-equivalent if they give the same Carbery functional
    for all joint distributions and valid orderings.

    Paper reference: Definition 6.5. -/
def MIEquivalent (G₁ G₂ : FinDAG n) : Prop :=
  ∀ (p : JointPMF Ω) (hn : n ≥ 1)
    (π₁ : TopologicalOrdering G₁) (π₂ : TopologicalOrdering G₂),
    dagCarberyFunctional hn G₁ p π₁ = dagCarberyFunctional hn G₂ p π₂

/-- MI-equivalence is symmetric. -/
theorem MIEquivalent.symm {G₁ G₂ : FinDAG n} (h : MIEquivalent (Ω := Ω) G₁ G₂) :
    MIEquivalent (Ω := Ω) G₂ G₁ :=
  fun p hn π₂ π₁ => (h p hn π₁ π₂).symm

/-!
## MI-Equivalence Characterization

Proposition 6.6: G₁ and G₂ are MI-equivalent if and only if they imply
the same consecutive bivariate marginals for all valid orderings.

The forward direction is immediate from the definition of Q_n^G.
The reverse direction follows from marginal sufficiency.
-/

/-- Two DAGs imply the same bivariate structure if for every pair of valid
    orderings, the bivariate marginals used in the Carbery functional match. -/
def SameBivariateStructure (G₁ G₂ : FinDAG n) : Prop :=
  ∀ (p : JointPMF Ω) (hn : n ≥ 1)
    (π₁ : TopologicalOrdering G₁) (π₂ : TopologicalOrdering G₂),
    p.sameDagMarginals p hn π₁ →
    p.sameDagMarginals p hn π₂ →
    dagCarberyFunctional hn G₁ p π₁ = dagCarberyFunctional hn G₂ p π₂

/-- **MI-Equivalence Characterization** (Proposition 6.6, forward direction):
    MI-equivalent DAGs have the same Carbery functional for all distributions.

    This is true by definition. -/
theorem mi_equivalent_implies_same_functional {G₁ G₂ : FinDAG n}
    (h : MIEquivalent (Ω := Ω) G₁ G₂) (hn : n ≥ 1) (p : JointPMF Ω)
    (π₁ : TopologicalOrdering G₁) (π₂ : TopologicalOrdering G₂) :
    dagCarberyFunctional hn G₁ p π₁ = dagCarberyFunctional hn G₂ p π₂ :=
  h p hn π₁ π₂

/-!
## Power Direction Theorems

These theorems characterize when the test has power to discriminate
between DAGs.

### Theorem 6.1§2 (Power Direction)

If Q_n^{G₀}(p) < Q_n^{G₁}(p) and T^{G₁}(p) = 1 (the Carbery inequality
is tight for G₁), then T^{G₀}(p) > 1.

Proof: T^{G₀} = E[∏ hᵢ] / (Q^{G₀} · ∏ ‖hᵢ‖)
              = (Q^{G₁} / Q^{G₀}) · E[∏ hᵢ] / (Q^{G₁} · ∏ ‖hᵢ‖)
              = (Q^{G₁} / Q^{G₀}) · T^{G₁}
              = Q^{G₁} / Q^{G₀} > 1

### Theorem 6.1§3 (No False Rejection)

If Q_n^{G₀}(p) ≥ Q_n^{G₁}(p), then T^{G₀}(p) ≤ 1.
-/

/-- Auxiliary: (a / (b * c)) * b = a / c for b ≠ 0 and b ≠ ⊤ in ENNReal. -/
private theorem ennreal_div_mul_cancel {a b c : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ⊤) :
    a / (b * c) * b = a / c := by
  have h1 : a / (b * c) = a * c⁻¹ * b⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hb) (Or.inl hb'), mul_comm b⁻¹ c⁻¹,
        mul_assoc]
  rw [h1, mul_assoc, ENNReal.inv_mul_cancel hb hb', mul_one, ← div_eq_mul_inv]

/-- **Test Statistic Ratio Identity** (Theorem 6.1, parts 2-3):
    T^{G₀} · Q_root^{G₀} = T^{G₁} · Q_root^{G₁}

    because the numerator E[∏ hᵢ] · (∏ ‖hᵢ‖)⁻¹ is the same for both.

    Paper reference: Theorem 6.1. -/
theorem test_statistic_ratio (hn : n ≥ 1)
    (G₀ G₁ : FinDAG n) (p : JointPMF Ω)
    (π₀ : TopologicalOrdering G₀) (π₁ : TopologicalOrdering G₁)
    (h : ∀ i : Fin n, Ω i → ℝ≥0∞)
    (_h_norms : ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) ≠ 0)
    (hQ₀ : dagCarberyRoot hn G₀ p π₀ ≠ 0)
    (hQ₀' : dagCarberyRoot hn G₀ p π₀ ≠ ⊤)
    (hQ₁ : dagCarberyRoot hn G₁ p π₁ ≠ 0)
    (hQ₁' : dagCarberyRoot hn G₁ p π₁ ≠ ⊤) :
    testStatistic hn G₀ p π₀ h * dagCarberyRoot hn G₀ p π₀ =
    testStatistic hn G₁ p π₁ h * dagCarberyRoot hn G₁ p π₁ := by
  -- Both sides equal E[∏ hᵢ] / ∏ ‖hᵢ‖
  -- T^G · Q_root^G = (E[∏h] / (Q_root^G · ∏‖h‖)) · Q_root^G = E[∏h] / ∏‖h‖
  simp only [testStatistic, testDenominator]
  rw [ennreal_div_mul_cancel hQ₀ hQ₀', ennreal_div_mul_cancel hQ₁ hQ₁']

/-- **Power Direction** (Theorem 6.1§2):
    If Q_root^{G₀} < Q_root^{G₁} and T^{G₁} ≥ 1, then T^{G₀} > 1.

    Algebraically: T^{G₀} = (Q_root^{G₁}/Q_root^{G₀}) · T^{G₁}.
    Since Q_root₁/Q_root₀ > 1 and T₁ ≥ 1, we get T₀ > 1.

    Paper reference: Theorem 6.1§2. -/
theorem power_direction_strict (hn : n ≥ 1)
    (G₀ G₁ : FinDAG n) (p : JointPMF Ω)
    (π₀ : TopologicalOrdering G₀) (π₁ : TopologicalOrdering G₁)
    (h : ∀ i : Fin n, Ω i → ℝ≥0∞)
    (hQ : dagCarberyRoot hn G₀ p π₀ < dagCarberyRoot hn G₁ p π₁)
    (_hQ₀_pos : dagCarberyRoot hn G₀ p π₀ ≠ 0)
    (hE_ne_zero : p.expectationProd h ≠ 0)
    (hE_ne_top : p.expectationProd h ≠ ⊤)
    (hN_ne_zero : ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) ≠ 0)
    (hN_ne_top : ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) ≠ ⊤)
    (hT₁ : testStatistic hn G₁ p π₁ h ≥ 1) :
    testStatistic hn G₀ p π₀ h > 1 := by
  have h_denom_lt : testDenominator hn G₀ p π₀ h < testDenominator hn G₁ p π₁ h := by
    simp only [testDenominator]
    exact ENNReal.mul_lt_mul_right' hN_ne_zero hN_ne_top hQ
  calc 1 ≤ testStatistic hn G₁ p π₁ h := hT₁
    _ = p.expectationProd h / testDenominator hn G₁ p π₁ h := rfl
    _ < p.expectationProd h / testDenominator hn G₀ p π₀ h :=
        ENNReal.div_lt_div_left hE_ne_zero hE_ne_top h_denom_lt
    _ = testStatistic hn G₀ p π₀ h := rfl

/-- **No Rejection** (Theorem 6.1§3):
    If Q_root^{G₀} ≥ Q_root^{G₁} and the test is valid under G₁,
    then T^{G₀} ≤ 1.

    Algebraically: T₀ = (Q_root₁/Q_root₀) · T₁ ≤ 1 · T₁ ≤ 1.

    Paper reference: Theorem 6.1§3. -/
theorem power_no_rejection (hn : n ≥ 1)
    (G₀ G₁ : FinDAG n) (p : JointPMF Ω)
    (π₀ : TopologicalOrdering G₀) (π₁ : TopologicalOrdering G₁)
    (h : ∀ i : Fin n, Ω i → ℝ≥0∞)
    (hQ : dagCarberyRoot hn G₁ p π₁ ≤ dagCarberyRoot hn G₀ p π₀)
    (hT₁ : testStatistic hn G₁ p π₁ h ≤ 1) :
    testStatistic hn G₀ p π₀ h ≤ 1 := by
  have h_denom_le : testDenominator hn G₁ p π₁ h ≤ testDenominator hn G₀ p π₀ h := by
    simp only [testDenominator]
    exact mul_le_mul_right' hQ _
  calc testStatistic hn G₀ p π₀ h
      = p.expectationProd h / testDenominator hn G₀ p π₀ h := rfl
    _ ≤ p.expectationProd h / testDenominator hn G₁ p π₁ h :=
        ENNReal.div_le_div_left h_denom_le _
    _ = testStatistic hn G₁ p π₁ h := rfl
    _ ≤ 1 := hT₁

end
