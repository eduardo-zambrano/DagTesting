/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Test Validity: T_h ≤ 1 Under the Null Hypothesis

This file contains the key validity theorem: under H₀ (the data-generating
process is Markov with respect to G), the test statistic T_h^{G,π}(p) ≤ 1
for any admissible test function h and valid topological ordering π.

## Main results

* `testStatistic_le_one_of_markov`: T_h ≤ 1 under H₀ (Proposition 3.3)
* `combinedTest_le_one_of_markov`: T_max ≤ 1 under H₀ (Proposition 4.3)

## Proof strategy

Under H₀, the DAG-implied bivariate marginals ARE the true bivariate
marginals of p. So:
  dagCarberyFunctional hn G p π = carberyFunctional hn p_π
where p_π is the permuted distribution. Then carberyInequality gives:
  E[∏ hᵢ(Xᵢ)] ≤ carberyFunctional · ∏ ‖hᵢ‖_{n+1}
which is exactly T_h ≤ 1.

## Paper reference

* Proposition 3.3 (Test validity) in Zambrano (2026)
* Proposition 4.3 (Combined test validity) in Zambrano (2026)
-/

import DagTesting.TestStatistic

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Key Lemma: Carbery Inequality Implies Test Validity

The test statistic T_h = E[∏ hᵢ] / (Q_n · ∏ ‖hᵢ‖) is ≤ 1 whenever
the numerator is bounded by the denominator, which is exactly what
Carbery's inequality provides.
-/

/-- **Auxiliary**: The Carbery inequality directly gives E[∏ hᵢ] ≤ Q_n · ∏ ‖hᵢ‖.
    This means the test statistic ratio is at most 1.

    This is the algebraic core of test validity: if a ≤ b and b ≠ 0,
    then a / b ≤ 1. -/
theorem ennreal_div_le_one_of_le {a b : ℝ≥0∞} (h : a ≤ b) : a / b ≤ 1 := by
  rcases eq_or_ne b 0 with rfl | hb
  · -- When b = 0, h gives a ≤ 0, so a = 0, and 0 / 0 ≤ 1
    have ha : a = 0 := le_antisymm h (zero_le a)
    rw [ha]
    norm_num
  · exact ENNReal.div_le_of_le_mul (by rwa [one_mul])

/-!
## Main Validity Theorem

The key theorem: under H₀, T_h ≤ 1 for all admissible test functions.

The proof has two parts:
1. Under the Markov assumption for G, the DAG Carbery functional Q_n^{G,π}
   correctly captures the dependence structure, meaning Q_n^{G,π}(p) is an
   upper bound for the Carbery functional of the actual distribution.
2. Carbery's inequality then gives E[∏ hᵢ] ≤ Q_n^{G,π} · ∏ ‖hᵢ‖.

For the finite state space formalization, we prove this by showing that
when p is Markov with respect to G, the Carbery inequality applied to p
with the reordered variables gives the desired bound.
-/

/-- The permuted JointPMF: reorder variables by σ.
    `(p.permute σ).prob y = p.prob ((Equiv.piCongrLeft Ω σ) y)` -/
private def JointPMF.permute (p : JointPMF Ω) (σ : Equiv.Perm (Fin n)) :
    @JointPMF n (fun j => Ω (σ j)) (fun j => ‹∀ i, Fintype (Ω i)› (σ j)) where
  prob := fun y => p.prob ((Equiv.piCongrLeft Ω σ) y)
  sum_eq_one := by
    rw [show (∑ y, p.prob ((Equiv.piCongrLeft Ω σ) y)) =
        ∑ x, p.prob x from Equiv.sum_comp (Equiv.piCongrLeft Ω σ) p.prob]
    exact p.sum_eq_one

/-- The bivariate marginal of the permuted distribution at consecutive pair (k, k+1)
    equals `bivariateAny` of the original at (σ k, σ (k+1)). -/
private theorem permute_bivariate_eq (p : JointPMF Ω) (σ : Equiv.Perm (Fin n))
    (k : Fin (n - 1))
    (s : Ω (σ ⟨k.val, by omega⟩))
    (t : Ω (σ ⟨k.val + 1, by omega⟩)) :
    @JointPMF.bivariateMarginai n (fun j => Ω (σ j))
      (fun j => ‹∀ i, Fintype (Ω i)› (σ j))
      (fun j => ‹∀ i, DecidableEq (Ω i)› (σ j))
      (p.permute σ) k s t =
    p.bivariateAny (σ ⟨k.val, by omega⟩) (σ ⟨k.val + 1, by omega⟩)
      (perm_consecutive_ne σ k) s t := by
  simp only [JointPMF.bivariateMarginai, JointPMF.bivariateAny, JointPMF.permute]
  apply Fintype.sum_equiv (Equiv.piCongrLeft Ω σ)
  intro y
  congr 1
  apply propext
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨by rw [Equiv.piCongrLeft_apply_apply]; exact h1,
           by rw [Equiv.piCongrLeft_apply_apply]; exact h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨by rw [Equiv.piCongrLeft_apply_apply] at h1; exact h1,
           by rw [Equiv.piCongrLeft_apply_apply] at h2; exact h2⟩

/-- The marginal of the permuted distribution at position j
    equals the marginal of the original at σ j. -/
private theorem permute_marginal_eq (p : JointPMF Ω) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (s : Ω (σ j)) :
    (p.permute σ).marginal j s = p.marginal (σ j) s := by
  simp only [JointPMF.marginal, JointPMF.permute]
  refine Fintype.sum_equiv (Equiv.piCongrLeft Ω σ) _ _ (fun y => ?_)
  have key : (Equiv.piCongrLeft Ω σ) y (σ j) = y j :=
    Equiv.piCongrLeft_apply_apply Ω σ y j
  rw [key]

/-- `carberyFunctionalPow` of the permuted distribution equals `dagCarberyFunctional`. -/
private theorem permute_functionalPow_eq (hn : n ≥ 1) (p : JointPMF Ω)
    (σ : Equiv.Perm (Fin n)) :
    @carberyFunctionalPow n (fun j => Ω (σ j))
      (fun j => ‹∀ i, Fintype (Ω i)› (σ j))
      (fun j => ‹∀ i, DecidableEq (Ω i)› (σ j))
      hn (p.permute σ) =
    ∑ s : ∀ i, Ω i,
      p.marginal (σ ⟨0, by omega⟩) (s (σ ⟨0, by omega⟩)) *
      (∏ k : Fin (n - 1),
        p.bivariateAny (σ ⟨k.val, by omega⟩) (σ ⟨k.val + 1, by omega⟩)
          (perm_consecutive_ne σ k)
          (s (σ ⟨k.val, by omega⟩)) (s (σ ⟨k.val + 1, by omega⟩))) *
      p.marginal (σ ⟨n - 1, by omega⟩) (s (σ ⟨n - 1, by omega⟩)) := by
  simp only [carberyFunctionalPow]
  -- Change summation variable from y : (∀ j, Ω (σ j)) to x : (∀ i, Ω i)
  rw [Fintype.sum_equiv (Equiv.piCongrLeft Ω σ)]
  intro y
  -- Simplify (piCongrLeft Ω σ y) (σ j) → y j on the RHS
  simp only [Equiv.piCongrLeft_apply_apply]
  -- Rewrite marginals using permute_marginal_eq
  rw [permute_marginal_eq p σ ⟨0, by omega⟩ (y ⟨0, by omega⟩)]
  rw [permute_marginal_eq p σ ⟨n - 1, by omega⟩ (y ⟨n - 1, by omega⟩)]
  congr 1; congr 1
  -- Product of bivariate marginals
  apply Finset.prod_congr rfl
  intro k _
  exact permute_bivariate_eq p σ k (y ⟨k.val, by omega⟩) (y ⟨k.val + 1, by omega⟩)

/-- **Ordered Carbery Inequality**: The Carbery inequality applied to the
    permuted distribution gives the bound with the DAG root functional.

    This holds for ANY distribution p and ANY permutation — no Markov
    assumption is needed. The proof constructs the permuted JointPMF p_π
    via `Equiv.piCongrLeft` and applies `carberyInequality` to it. -/
theorem dagCarberyInequality (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (hp : p.IsMarkovDAG G) (π : TopologicalOrdering G)
    (h : ∀ i : Fin n, Ω i → ℝ≥0∞) :
    p.expectationProd h ≤
    dagCarberyRoot hn G p π * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) := by
  -- Step 1: Apply carberyInequality to the permuted distribution
  let σ := π.perm
  let p_π := p.permute σ
  let f : ∀ j : Fin n, Ω (σ j) → ℝ≥0∞ := fun j => h (σ j)
  have carbery := @carberyInequality n (fun j => Ω (σ j))
    (fun j => ‹∀ i, Fintype (Ω i)› (σ j))
    (fun j => ‹∀ i, DecidableEq (Ω i)› (σ j))
    hn p_π f
  -- Step 2: Show LHS of Carbery equals p.expectationProd h
  have lhs_eq : ∑ y : ∀ j, Ω (σ j), p_π.prob y * ∏ j, f j (y j) =
      p.expectationProd h := by
    simp only [JointPMF.permute, JointPMF.expectationProd, f, p_π]
    exact Fintype.sum_equiv (Equiv.piCongrLeft Ω σ) _ _ (fun y => by
      congr 1
      exact Fintype.prod_equiv σ _ _ (fun j => by simp [Equiv.piCongrLeft_apply_apply]))
  -- Step 3: Show norms are preserved
  have norms_eq : ∏ j : Fin n, lpNormFinite (n + 1 : ℝ) (f j) =
      ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (h i) :=
    Equiv.prod_comp σ (fun i => lpNormFinite (n + 1 : ℝ) (h i))
  -- Step 4: Show carberyFunctionalPow p_π = dagCarberyFunctional p π
  have functional_eq :
      @carberyFunctionalPow n (fun j => Ω (σ j))
        (fun j => ‹∀ i, Fintype (Ω i)› (σ j))
        (fun j => ‹∀ i, DecidableEq (Ω i)› (σ j))
        hn p_π =
      dagCarberyFunctional hn G p π := by
    rw [permute_functionalPow_eq]
    rfl
  -- Step 5: Combine everything
  rw [← lhs_eq]
  refine le_trans carbery ?_
  -- carberyFunctional p_π * ∏ ‖f_j‖ = dagCarberyRoot * ∏ ‖h_i‖
  simp only [carberyFunctional, dagCarberyRoot]
  rw [functional_eq, norms_eq]

/-- **Test Validity** (Proposition 3.3): Under H₀ (p is Markov for G),
    T_h^{G,π}(p) ≤ 1 for any admissible test function h.

    This is the fundamental validity guarantee of the DAG test.

    **Proof sketch**:
    1. Under H₀, p factorizes as ∏ᵢ p(xᵢ | x_{pa(i)})
    2. The DAG-implied bivariate marginals under ordering π match the
       true bivariate marginals of p (when reordered by π)
    3. Therefore dagCarberyRoot = carberyFunctional for the reordered p
    4. Carbery's inequality gives: E[∏ hᵢ] ≤ dagCarberyRoot · ∏ ‖hᵢ‖
    5. Dividing both sides by dagCarberyRoot · ∏ ‖hᵢ‖ gives T_h ≤ 1

    Paper reference: Proposition 3.3. -/
theorem testStatistic_le_one_of_markov (hn : n ≥ 1)
    (G : FinDAG n) (p : JointPMF Ω) (hp : p.IsMarkovDAG G)
    (π : TopologicalOrdering G) (h : ∀ i : Fin n, Ω i → ℝ≥0∞) :
    testStatistic hn G p π h ≤ 1 := by
  apply ennreal_div_le_one_of_le
  exact dagCarberyInequality hn G p hp π h

/-- **Combined Test Validity** (Proposition 4.3): Under H₀,
    T_max = max_k T_{h^(k)} ≤ 1 for any finite collection of
    admissible test functions.

    This follows immediately from per-test validity.

    Paper reference: Proposition 4.3. -/
theorem combinedTest_le_one_of_markov (hn : n ≥ 1)
    (G : FinDAG n) (p : JointPMF Ω) (hp : p.IsMarkovDAG G)
    (π : TopologicalOrdering G) {K : ℕ}
    (hs : Fin K → (∀ i : Fin n, Ω i → ℝ≥0∞)) :
    combinedTestStatistic hn G p π hs ≤ 1 := by
  apply combinedTestStatistic_le_one
  intro k
  exact testStatistic_le_one_of_markov hn G p hp π (hs k)

end
