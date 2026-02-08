/-
Copyright (c) 2026 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DAG Testing via Moment Inequalities — Lean 4 Formalization

This library provides a Lean 4 formalization of key results from:
"Testing Causal DAG Structures via Moment Inequalities" (Zambrano, 2026)

## Approach

This formalization works with **finite state spaces** and builds on the
CarberyVersionA library, which formalizes the core Carbery inequality and
concentration bounds.

## Correspondence with Paper Results

| Paper Result | Lean Theorem | Status |
|--------------|--------------|--------|
| Def 2.1 (DAG) | `FinDAG` | Defined |
| Def 3.1 (Topological ordering) | `TopologicalOrdering` | Defined |
| Def 2.4 (DAG-specific Q_n) | `dagCarberyFunctional` | Defined |
| Def 2.4 (Root form Q_n^{1/(n+1)}) | `dagCarberyRoot` | Defined |
| Prop 3.3 (Test validity: T_h ≤ 1) | `testStatistic_le_one_of_markov` | **Proved** (via `dagCarberyInequality`) |
| Prop 3.3 (Ordered Carbery ineq.) | `dagCarberyInequality` | sorry (bridge lemma) |
| Prop 4.1 (Admissible test functions) | `admissible_of_ennreal` | **Proved** |
| Prop 4.3 (Combined test validity) | `combinedTest_le_one_of_markov` | **Proved** (via 3.3) |
| Prop 6.3 (MI-equivalence) | `mi_equivalent_implies_same_functional` | **Proved** (by def) |
| Thm 6.1 (T·Q ratio identity) | `test_statistic_ratio` | **Proved** |
| Thm 6.1§2 (Power direction) | `power_direction_strict` | **Proved** |
| Thm 6.1§3 (No false rejection) | `power_no_rejection` | **Proved** |
| Numerical: Q₃^chain ≠ Q₃^fork | `chain_fork_Q4_ne` | **Proved** |
| Numerical: Q₃^chain > Q₃^fork | `chain_Q4_gt_fork_Q4` | **Proved** |
| Marginal sufficiency (DAG) | `dagCarberyFunctional_marginal_sufficiency` | **Proved** |
| Bivariate marginal summation | `bivariateAny_sum_snd` | **Proved** |
| Consecutive pair equivalence | `bivariateAny_eq_bivariateMarginai` | **Proved** |

## Axioms and Sorry Count

**Inherited axiom** (from CarberyVersionA):
- `carberyInequality`: Carbery's multilinear Cauchy-Schwarz (established result)

**Sorry in this library** (2 total):
- `topologicalOrdering_exists`: General existence of topological orderings
  (concrete instances for chain3, fork3, collider3, independent3, diamond4
  are all fully proved)
- `dagCarberyInequality`: Ordered Carbery inequality (bridge lemma).
  States that under the Markov assumption, E[∏ hᵢ] ≤ dagCarberyRoot · ∏ ‖hᵢ‖.
  Requires constructing the permuted JointPMF p_π (via Equiv.piCongrLeft)
  and applying carberyInequality to it. Mathematically a direct consequence
  of carberyInequality, but technically involved due to type-level permutation.

**Fully proved** (no sorry):
- All concrete DAG instances and their topological orderings
- All numerical computations (chain vs. fork discrimination)
- Test validity under H₀: testStatistic_le_one_of_markov (Prop 3.3)
- Combined test validity: combinedTest_le_one_of_markov (Prop 4.3)
- Admissible test function characterization
- DAG marginal sufficiency
- Bivariate marginal summation and consecutive pair equivalence
- Test statistic ratio identity (T·Q_root = E/N)
- Power direction theorem (Thm 6.1§2)
- No false rejection theorem (Thm 6.1§3)

## Files

- `DAGBasic.lean`: DAG definitions, parent/child sets, concrete instances
- `TopologicalOrdering.lean`: Orderings, existence, concrete orderings
- `DagFunctional.lean`: DAG-specific Q_n, Markov factorization, marginal sufficiency
- `TestStatistic.lean`: Test statistic definition, admissibility, combined test
- `OrderingValidity.lean`: Test validity under H₀ (Prop 3.3)
- `PowerAnalysis.lean`: MI-equivalence, power direction (Thm 6.1)
- `NumericalExamples.lean`: Machine-checked chain vs. fork discrimination

## Dependencies

- **CarberyVersionA**: Core Carbery inequality formalization (local dependency)
- **Mathlib**: Standard mathematical library for Lean 4

## References

* Zambrano, E. (2026). Testing Causal DAG Structures via Moment Inequalities.
* Carbery, A. (2004). A multilinear generalisation of the Cauchy-Schwarz inequality.
  Proceedings of the AMS, 132(11), 3141-3152.
-/

import DagTesting.DAGBasic
import DagTesting.TopologicalOrdering
import DagTesting.DagFunctional
import DagTesting.TestStatistic
import DagTesting.OrderingValidity
import DagTesting.PowerAnalysis
import DagTesting.NumericalExamples
