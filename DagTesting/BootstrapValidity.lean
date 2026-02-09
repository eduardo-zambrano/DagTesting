/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Bootstrap Validity: Product-of-Conditionals Is Markov

This file formalizes the structural core of bootstrap validity for DAG testing:
any distribution that factorizes as a product of conditional PMFs along a DAG
is Markov with respect to that DAG, and therefore satisfies T ≤ 1.

## Main definitions

* `ConditionalFamily`: A family of conditional distributions indexed by parent configs
* `JointPMF.FactorsAs`: A JointPMF factorizes according to a conditional family

## Main results

* `isMarkovDAG_of_factorsAs`: If a JointPMF factors as a product of conditionals, it is Markov
* `bootstrap_validity`: For any DAG-constrained distribution, T ≤ 1
* `bootstrap_combined_validity`: Combined test also satisfies T_max ≤ 1

## Referee concern addressed

The referee noted that the bootstrap consistency proof (Theorem 5.3) was too informal.
This formalization proves the structural core: any DAG-constrained distribution satisfies
T ≤ 1, regardless of whether it arises from a bootstrap procedure or any other source.
This is the key invariant that makes the constrained bootstrap valid.

## Paper reference

* Theorem 5.3 (Bootstrap consistency) in Zambrano (2026)
* The structural argument: constrained bootstrap → Markov w.r.t. G → T ≤ 1
-/

import DagTesting.OrderingValidity

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Conditional Family

A conditional family for a DAG G consists of, for each vertex i, a
conditional distribution p(xᵢ | x_{pa(i)}) — i.e., a function from
parent configurations to distributions over Ω i.

This is exactly the data needed to specify a Bayesian network.
-/

/-- A family of conditional distributions for a DAG.

    For each vertex i, we have a conditional distribution:
    given values for the parents of i, we get a probability distribution over Ω i.

    The normalization condition ensures each conditional sums to 1. -/
structure ConditionalFamily (G : FinDAG n) (Ω : Fin n → Type*)
    [∀ i, Fintype (Ω i)] where
  /-- The conditional distribution for vertex i given parent values -/
  cond : ∀ (i : Fin n), (∀ j : G.parents i, Ω j.val) → Ω i → ℝ≥0∞
  /-- Each conditional sums to 1 over the child variable -/
  sum_eq_one : ∀ (i : Fin n) (xpa : ∀ j : G.parents i, Ω j.val),
    ∑ xi : Ω i, cond i xpa xi = 1

/-!
## Factorization Property

A JointPMF `p` factorizes according to a conditional family if
  p(x) = ∏ᵢ cond_i(x_{pa(i)}, xᵢ)
for all x. This is the standard Bayesian network factorization.
-/

/-- A JointPMF factorizes according to a conditional family for DAG G.

    This states that p(x) = ∏ᵢ cond_i(x_{pa(i)}, xᵢ) for all x.
    This is the defining property of a Bayesian network distribution. -/
def JointPMF.FactorsAs (p : JointPMF Ω) (G : FinDAG n)
    (cf : ConditionalFamily G Ω) : Prop :=
  ∀ x : ∀ i, Ω i,
    p.prob x = ∏ i : Fin n, cf.cond i (fun j => x j.val) (x i)

/-!
## Core Result: Factorization Implies Markov Property

This is the structural core of bootstrap validity.
-/

/-- **Factorization implies Markov property**.

    If a JointPMF factorizes according to a conditional family for DAG G,
    then it is Markov with respect to G.

    This is immediate by construction: the conditional family IS the
    local conditional distributions witnessing the Markov factorization.
    The `IsMarkovDAG` definition asks for exactly what `FactorsAs` provides:
    local conditionals that (1) sum to 1, and (2) give the joint as a product.

    Paper reference: This is the structural core of Theorem 5.3. -/
theorem isMarkovDAG_of_factorsAs (G : FinDAG n) (p : JointPMF Ω)
    (cf : ConditionalFamily G Ω) (hf : p.FactorsAs G cf) :
    p.IsMarkovDAG G :=
  ⟨cf.cond, cf.sum_eq_one, hf⟩

/-- **Bootstrap Validity**: For any distribution that factorizes according to
    a conditional family for DAG G (i.e., any constrained bootstrap distribution),
    the test statistic T_h ≤ 1.

    This is the key structural result for bootstrap inference:
    - The constrained bootstrap generates distributions that factor as products
      of conditional PMFs along G
    - By `isMarkovDAG_of_factorsAs`, these are Markov w.r.t. G
    - By `testStatistic_le_one_of_markov`, they satisfy T ≤ 1
    - Therefore the bootstrap null distribution is stochastically dominated by 1

    Paper reference: Theorem 5.3 (structural core). -/
theorem bootstrap_validity (hn : n ≥ 1) (G : FinDAG n) (p : JointPMF Ω)
    (cf : ConditionalFamily G Ω) (hf : p.FactorsAs G cf)
    (π : TopologicalOrdering G) (h : ∀ i : Fin n, Ω i → ℝ≥0∞) :
    testStatistic hn G p π h ≤ 1 :=
  testStatistic_le_one_of_markov hn G p (isMarkovDAG_of_factorsAs G p cf hf) π h

/-- **Combined Bootstrap Validity**: The combined test also satisfies T_max ≤ 1
    for any constrained bootstrap distribution.

    Paper reference: Follows from Theorem 5.3 + Proposition 4.7. -/
theorem bootstrap_combined_validity (hn : n ≥ 1) (G : FinDAG n)
    (p : JointPMF Ω) (cf : ConditionalFamily G Ω) (hf : p.FactorsAs G cf)
    (π : TopologicalOrdering G) {K : ℕ}
    (hs : Fin K → (∀ i : Fin n, Ω i → ℝ≥0∞)) :
    combinedTestStatistic hn G p π hs ≤ 1 :=
  combinedTest_le_one_of_markov hn G p (isMarkovDAG_of_factorsAs G p cf hf) π hs

/-!
## Direct Markov property construction

Alternative formulation: any JointPMF for which there exist conditional
distributions (summing to 1) that give the factorization is Markov.
This doesn't require the `ConditionalFamily` structure.
-/

/-- Any JointPMF that admits a product-of-conditionals factorization is Markov.

    This is a convenience version that doesn't require bundling the conditionals
    into a `ConditionalFamily` structure. -/
theorem isMarkovDAG_of_product_factorization (G : FinDAG n) (p : JointPMF Ω)
    (localCond : ∀ (i : Fin n), (∀ j : G.parents i, Ω j.val) → Ω i → ℝ≥0∞)
    (h_sum : ∀ i (xpa : ∀ j : G.parents i, Ω j.val),
      ∑ xi : Ω i, localCond i xpa xi = 1)
    (h_factor : ∀ x : ∀ i, Ω i,
      p.prob x = ∏ i : Fin n, localCond i (fun j => x j.val) (x i)) :
    p.IsMarkovDAG G :=
  ⟨localCond, h_sum, h_factor⟩

/-!
## Converse: Markov Property Yields Conditional Family

For completeness, we show the converse: any Markov distribution yields
a conditional family.
-/

/-- The Markov property yields a conditional family.

    If p is Markov w.r.t. G, then there exists a conditional family
    such that p factorizes according to it.

    This is just unpacking the definition of `IsMarkovDAG`. -/
theorem exists_conditionalFamily_of_isMarkovDAG (G : FinDAG n) (p : JointPMF Ω)
    (hp : p.IsMarkovDAG G) :
    ∃ cf : ConditionalFamily G Ω, p.FactorsAs G cf := by
  obtain ⟨localCond, h_sum, h_factor⟩ := hp
  exact ⟨⟨localCond, h_sum⟩, h_factor⟩

/-- **Equivalence**: A JointPMF is Markov w.r.t. G if and only if it factors
    according to some conditional family for G.

    This shows that the Bayesian network factorization and the Markov property
    are the same thing, justifying our approach to bootstrap validity. -/
theorem isMarkovDAG_iff_exists_factorization (G : FinDAG n) (p : JointPMF Ω) :
    p.IsMarkovDAG G ↔ ∃ cf : ConditionalFamily G Ω, p.FactorsAs G cf := by
  constructor
  · exact exists_conditionalFamily_of_isMarkovDAG G p
  · rintro ⟨cf, hf⟩
    exact isMarkovDAG_of_factorsAs G p cf hf

end
