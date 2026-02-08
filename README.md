# DagTesting: Lean 4 Formalization of DAG Moment Inequality Tests

A Lean 4 formalization of key results from "Testing Causal DAG Structures via Moment Inequalities" (Zambrano, 2026). The formalization proves that a test statistic based on Carbery's multilinear generalization of the Cauchy-Schwarz inequality can discriminate between Markov-equivalent DAGs where standard conditional independence tests cannot. All theorems are fully proved (0 sorry's).

## Paper Reference

> Zambrano, E. (2026). Testing Causal DAG Structures via Moment Inequalities.
>
> Carbery, A. (2004). A multilinear generalisation of the Cauchy-Schwarz inequality. *Proceedings of the AMS*, 132(11), 3141-3152.

## Paper-to-Code Correspondence

| Paper Result | Lean Name | File | Status |
|---|---|---|---|
| **Definitions** | | | |
| Definition 2.1 (DAG) | `FinDAG` | `DAGBasic.lean` | Defined |
| Definition 3.1 (Topological ordering) | `TopologicalOrdering` | `TopologicalOrdering.lean` | Defined |
| Definition 3.3 (DAG functional Q_n^G) | `dagCarberyFunctional` | `DagFunctional.lean` | Defined |
| Definition 3.3 (Root form Q_n^{1/(n+1)}) | `dagCarberyRoot` | `DagFunctional.lean` | Defined |
| Definition 4.1 (Test statistic T_h) | `testStatistic` | `TestStatistic.lean` | Defined |
| Definition 4.6 (Combined test statistic) | `combinedTestStatistic` | `TestStatistic.lean` | Defined |
| Definition 6.5 (MI-equivalent DAGs) | `MIEquivalent` | `PowerAnalysis.lean` | Defined |
| **Test Validity** | | | |
| Proposition 3.8 (T_h <= 1 under H_0) | `testStatistic_le_one_of_markov` | `OrderingValidity.lean` | **Proved** |
| Proposition 3.8 (Ordered Carbery inequality) | `dagCarberyInequality` | `OrderingValidity.lean` | **Proved** |
| Proposition 4.3 (Admissible test functions) | `admissible_of_ennreal` | `TestStatistic.lean` | **Proved** |
| Proposition 4.7 (Combined test validity) | `combinedTest_le_one_of_markov` | `OrderingValidity.lean` | **Proved** |
| **Power Analysis** | | | |
| Theorem 6.1 (T*Q ratio identity) | `test_statistic_ratio` | `PowerAnalysis.lean` | **Proved** |
| Theorem 6.1, part 2 (Power direction) | `power_direction_strict` | `PowerAnalysis.lean` | **Proved** |
| Theorem 6.1, part 3 (No false rejection) | `power_no_rejection` | `PowerAnalysis.lean` | **Proved** |
| Proposition 6.6 (MI-equivalence) | `mi_equivalent_implies_same_functional` | `PowerAnalysis.lean` | **Proved** |
| **Structural Results** | | | |
| Topological ordering existence | `topologicalOrdering_exists` | `TopologicalOrdering.lean` | **Proved** |
| DAG marginal sufficiency | `dagCarberyFunctional_marginal_sufficiency` | `DagFunctional.lean` | **Proved** |
| Bivariate marginal summation | `bivariateAny_sum_snd` | `DagFunctional.lean` | **Proved** |
| Consecutive pair equivalence | `bivariateAny_eq_bivariateMarginai` | `DagFunctional.lean` | **Proved** |
| **Numerical Discrimination** | | | |
| Q_3^chain != Q_3^fork | `chain_fork_Q4_ne` | `NumericalExamples.lean` | **Proved** |
| Q_3^chain > Q_3^fork | `chain_Q4_gt_fork_Q4` | `NumericalExamples.lean` | **Proved** |

## Project Structure

```
DagTesting/
  DagTesting.lean              -- Root file (imports all modules)
  DagTesting/
    DAGBasic.lean              -- DAG definitions, parent/child sets, concrete instances
    TopologicalOrdering.lean   -- Topological orderings, existence theorem
    DagFunctional.lean         -- DAG-specific Q_n^G, Markov factorization, marginal sufficiency
    TestStatistic.lean         -- Test statistic T_h, admissibility, combined test
    OrderingValidity.lean      -- Test validity under H_0 (T_h <= 1)
    PowerAnalysis.lean         -- MI-equivalence, power direction (Theorem 6.1)
    NumericalExamples.lean     -- Machine-checked chain vs. fork discrimination
```

## Dependencies

- **[CarberyVersionA](../Carbery_Probabilistic_A/CarberyVersionA)**: Core Carbery inequality formalization (local path dependency)
- **[Mathlib](https://github.com/leanprover-community/mathlib4)**: v4.24.0
- **Lean 4**: v4.24.0

## Building

```bash
cd DagTesting
lake build
```

The build imports CarberyVersionA via a local path configured in `lakefile.lean`.

## Axioms and Logical Foundations

**Sorry count: 0** -- all theorems in this library are fully proved.

The only external axiom is inherited from CarberyVersionA:

- `carberyInequality`: Carbery's multilinear Cauchy-Schwarz inequality (an established mathematical result from Carbery 2004). This axiom states that for a joint PMF p on finite state spaces, E[prod_i h_i(X_i)] <= carberyFunctional(p)^{1/(n+1)} * prod_i ||h_i||_{n+1}.

All other results are proved from this axiom and standard Mathlib.

## Relationship to Paper Formulation

The Lean formalization uses the **Lebesgue (counting-measure) form** of Carbery's inequality (Theorem 2.7 in the paper), where norms are Lebesgue $L^{n+1}$ norms: $\|f_i\|_{L^{n+1}} = (\int |f_i|^{n+1}\, dx)^{1/(n+1)}$. The paper's test statistic (Definition 4.1) is defined using the **probability-measure (expectation) form** (Corollary 2.10), which includes a density correction factor $\prod_i p_i(X_i)^{1/(n+1)}$ in the numerator and uses $(\mathbb{E}[h_i^{n+1}])^{1/(n+1)}$ in the denominator. These two forms are equivalent via the substitution $f_i = g_i \cdot p_i^{1/(n+1)}$ (Definition 2.8 and Lemma 2.9 in the paper). The expectation form is more natural for statistical applications, while the Lebesgue form is more natural for the Lean formalization over finite state spaces with counting measure.

## Key Result Highlights

- **0 sorry's**: Every theorem is fully proved, including two technically challenging results:
  - `topologicalOrdering_exists`: Proved via a ranking function from the height encoding g(i) = n * f(i) + i.val
  - `dagCarberyInequality`: Proved by constructing a permuted JointPMF via `JointPMF.permute` and `Equiv.piCongrLeft`, then applying `carberyInequality`

- **Numerical discrimination**: Machine-checked proof that Q_3^chain(p) = 5597/15625 != 5408/15625 = Q_3^fork(p) for specific transition probabilities, demonstrating that the Carbery functional can distinguish Markov-equivalent DAGs (chain vs. fork) where conditional independence tests cannot.
