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
| Def 3.3 (DAG functional Q_n^G) | `dagCarberyFunctional` | Defined |
| Def 3.3 (Root form Q_n^{1/(n+1)}) | `dagCarberyRoot` | Defined |
| Prop 3.8 (Validity: T_h ≤ 1) | `testStatistic_le_one_of_markov` | **Proved** (via `dagCarberyInequality`) |
| Prop 3.8 (Ordered Carbery ineq.) | `dagCarberyInequality` | **Proved** (via `JointPMF.permute` + `Equiv.piCongrLeft`) |
| Def 4.1 (Test statistic) | `testStatistic` | Defined |
| Prop 4.3 (Admissible test functions) | `admissible_of_ennreal` | **Proved** |
| Def 4.6 (Combined test statistic) | `combinedTestStatistic` | Defined |
| Prop 4.7 (Combined test validity) | `combinedTest_le_one_of_markov` | **Proved** (via Prop 3.8) |
| Thm 6.1 (T·Q ratio identity) | `test_statistic_ratio` | **Proved** |
| Thm 6.1§2 (Power direction) | `power_direction_strict` | **Proved** |
| Thm 6.1§3 (No false rejection) | `power_no_rejection` | **Proved** |
| Def 6.5 (MI-equivalent DAGs) | `MIEquivalent` | Defined |
| Prop 6.6 (MI-equivalence) | `mi_equivalent_implies_same_functional` | **Proved** (by def) |
| Numerical: Q₃^chain ≠ Q₃^fork | `chain_fork_Q4_ne` | **Proved** |
| Numerical: Q₃^chain > Q₃^fork | `chain_Q4_gt_fork_Q4` | **Proved** |
| Marginal sufficiency (DAG) | `dagCarberyFunctional_marginal_sufficiency` | **Proved** |
| Bivariate marginal summation | `bivariateAny_sum_snd` | **Proved** |
| Consecutive pair equivalence | `bivariateAny_eq_bivariateMarginai` | **Proved** |
| Topological ordering existence | `topologicalOrdering_exists` | **Proved** (via ranking function) |
| Thm 5.3 (Bootstrap validity) | `bootstrap_validity` | **Proved** (via `isMarkovDAG_of_factorsAs`) |
| Thm 5.3 (Markov ↔ factorization) | `isMarkovDAG_iff_exists_factorization` | **Proved** |
| Prop 7.5 (Q_n stability) | `dagCarberyFunctional_continuous_in_marginals` | **Proved** |
| Prop 7.5 (Q_n monotonicity) | `dagCarberyFunctional_mono` | **Proved** |
| Prop 7.5 (Q_n boundedness) | `dagCarberyFunctional_le_card` | **Proved** |
| Root form stability | `dagCarberyRoot_continuous_in_marginals` | **Proved** |
| SubDAG ordering inheritance | `topologicalOrdering_of_subDAG` | **Proved** |
| SubDAG Markov inheritance | `isMarkovDAG_of_subDAG` | **Proved** |
| Q_n depends only on ordering | `dagCarberyFunctional_eq_of_perm_eq` | **Proved** |
| Q_n preserved under SubDAG | `dagCarberyFunctional_subDAG_eq` | **Proved** |
| Prop 6.3 (SubDAG test validity) | `testStatistic_le_one_of_subDAG_markov` | **Proved** |

## Axioms and Sorry Count

**Sorry count: 0** — all theorems in this library are fully proved.

**Inherited axiom** (from CarberyVersionA):
- `carberyInequality`: Carbery's multilinear Cauchy-Schwarz (established result)

**Fully proved** (no sorry):
- All concrete DAG instances and their topological orderings
- All numerical computations (chain vs. fork discrimination)
- Topological ordering existence: `topologicalOrdering_exists`
  (via ranking function from height encoding g(i) = n · f(i) + i)
- Ordered Carbery inequality: `dagCarberyInequality`
  (via `JointPMF.permute` + `Equiv.piCongrLeft`)
- Test validity under H₀: `testStatistic_le_one_of_markov` (Prop 3.8)
- Combined test validity: `combinedTest_le_one_of_markov` (Prop 4.7)
- Admissible test function characterization
- DAG marginal sufficiency
- Bivariate marginal summation and consecutive pair equivalence
- Test statistic ratio identity (T·Q_root = E/N)
- Power direction theorem (Thm 6.1§2)
- No false rejection theorem (Thm 6.1§3)
- Bootstrap validity: product-of-conditionals is Markov (Thm 5.3 core)
- Q_n stability: monotonicity, boundedness, continuity (Prop 7.5)
- SubDAG: ordering inheritance, Markov inheritance, Q_n preservation (Prop 6.3)
- Test validity under super-DAG of true structure (Prop 6.3)

## Files

- `DAGBasic.lean`: DAG definitions, parent/child sets, concrete instances
- `TopologicalOrdering.lean`: Orderings, existence, SubDAG inheritance, concrete orderings
- `DagFunctional.lean`: DAG-specific Q_n, Markov factorization, marginal sufficiency, SubDAG properties
- `TestStatistic.lean`: Test statistic definition, admissibility, combined test
- `OrderingValidity.lean`: Test validity under H₀ (Prop 3.8)
- `PowerAnalysis.lean`: MI-equivalence, power direction (Thm 6.1), SubDAG test validity (Prop 6.3)
- `NumericalExamples.lean`: Machine-checked chain vs. fork discrimination
- `BootstrapValidity.lean`: Product-of-conditionals is Markov, bootstrap T ≤ 1
- `QnStability.lean`: Q_n stability, monotonicity, boundedness, Lipschitz structure

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
import DagTesting.BootstrapValidity
import DagTesting.QnStability
