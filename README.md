# DagTesting: Lean 4 Formalization of DAG Moment Inequality Tests

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.24.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.24.0-blue)](https://github.com/leanprover-community/mathlib4)
[![Sorry count](https://img.shields.io/badge/sorry_count-0-brightgreen)]()

Machine-verified proofs that a test statistic based on Carbery's multilinear Cauchy--Schwarz inequality is valid for testing causal DAG structures. This is the first formalization showing that moment inequalities can **distinguish Markov-equivalent DAGs** --- structures that encode identical conditional independences and are invisible to all CI-based methods.

**Key results formalized:**

- The test statistic satisfies $T_h \leq 1$ under the null (test validity)
- The constrained bootstrap preserves this bound (bootstrap validity)
- Different DAGs yield different $Q_n$ values even when Markov equivalent (discrimination power)
- Machine-checked numerical proof: $Q_3^{\text{chain}} = 5597/15625 \neq 5408/15625 = Q_3^{\text{fork}}$

All theorems are fully proved with **0 sorry's**. The only axiom is Carbery's inequality itself, an established result from Carbery (2004).

## Related Repositories

| Repository | Description |
|------------|-------------|
| [dagMI](https://github.com/eduardo-zambrano/dagMI) | R package implementing the methodology |
| [dagMI-replication](https://github.com/eduardo-zambrano/dagMI-replication) | Replication package for all tables in the paper |
| [CarberyConcentration](https://github.com/eduardo-zambrano/CarberyConcentration) | Lean 4 formalization of the Carbery inequality (dependency) |

## Paper Reference

> Zambrano, E. (2026). Testing Causal DAG Structures via Moment Inequalities.
>
> Carbery, A. (2004). A multilinear generalisation of the Cauchy-Schwarz inequality. *Proceedings of the AMS*, 132(11), 3141-3152.

## What is Formalized

### Test validity (Propositions 3.8, 4.3, 4.7)

If the data-generating distribution is Markov with respect to a DAG $\mathcal{G}$, the test statistic satisfies $T_h^{\mathcal{G}} \leq 1$ for any admissible test function $h$. This is the core guarantee that the test has correct size.

### Bootstrap validity (Theorem 5.3)

A distribution factorizes according to a DAG's Markov property if and only if it can be written as a product of conditionals. The constrained bootstrap, which resamples from estimated conditionals, therefore generates draws that satisfy the null hypothesis.

### Power analysis (Theorem 6.1)

The test statistic decomposes as a ratio involving the $Q_n$ functional. When the true DAG differs from the hypothesized one, the bootstrap null distribution shifts, producing power --- even against Markov-equivalent alternatives.

### Numerical discrimination

A machine-checked proof that for specific transition probabilities on 4 nodes, $Q_3^{\text{chain}}(p) = 5597/15625$ while $Q_3^{\text{fork}}(p) = 5408/15625$. These two DAGs are Markov equivalent (same conditional independences), yet the Carbery functional distinguishes them. The kernel of computation is verified by Lean's `native_decide`.

### Stability (Proposition 7.4)

$Q_n$ is monotone under marginal dominance, bounded by $|\Omega|^n$, and continuous in the marginals.

## What is Not Formalized

- **Asymptotic distribution theory**: The bootstrap consistency argument (Section 5.2) relies on empirical process theory not available in Mathlib.
- **Continuous distributions**: The formalization uses finite state spaces with counting measure. The paper's results hold for continuous distributions with Lebesgue measure; the algebraic structure is identical (sums replace integrals).
- **Carbery's inequality itself**: Axiomatized as `carberyInequality`. This is a published result (Carbery 2004, Proc. AMS) whose proof involves real-analytic techniques outside the scope of this project.

## Paper-to-Code Correspondence

| Paper Result | Lean Name | File |
|---|---|---|
| **Definitions** | | |
| Definition 2.1 (DAG) | `FinDAG` | `DAGBasic.lean` |
| Definition 3.1 (Topological ordering) | `TopologicalOrdering` | `TopologicalOrdering.lean` |
| Definition 3.3 (DAG functional $Q_n^{\mathcal{G}}$) | `dagCarberyFunctional` | `DagFunctional.lean` |
| Definition 4.1 (Test statistic $T_h$) | `testStatistic` | `TestStatistic.lean` |
| Definition 4.6 (Combined test) | `combinedTestStatistic` | `TestStatistic.lean` |
| Definition 6.5 (MI-equivalence) | `MIEquivalent` | `PowerAnalysis.lean` |
| **Test Validity** | | |
| Proposition 3.8 ($T_h \leq 1$ under $H_0$) | `testStatistic_le_one_of_markov` | `OrderingValidity.lean` |
| Proposition 3.8 (Ordered Carbery inequality) | `dagCarberyInequality` | `OrderingValidity.lean` |
| Proposition 4.3 (Admissible test functions) | `admissible_of_ennreal` | `TestStatistic.lean` |
| Proposition 4.7 (Combined test validity) | `combinedTest_le_one_of_markov` | `OrderingValidity.lean` |
| **Bootstrap & Power** | | |
| Theorem 5.3 (Bootstrap validity) | `bootstrap_validity` | `BootstrapValidity.lean` |
| Theorem 5.3 (Markov iff factorization) | `isMarkovDAG_iff_exists_factorization` | `BootstrapValidity.lean` |
| Theorem 6.1 (Power direction) | `power_direction_strict` | `PowerAnalysis.lean` |
| Theorem 6.1 (No false rejection) | `power_no_rejection` | `PowerAnalysis.lean` |
| Proposition 6.2 (SubDAG validity) | `testStatistic_le_one_of_subDAG_markov` | `PowerAnalysis.lean` |
| Proposition 6.6 (MI-equivalence) | `mi_equivalent_implies_same_functional` | `PowerAnalysis.lean` |
| **Structural Results** | | |
| Topological ordering existence | `topologicalOrdering_exists` | `TopologicalOrdering.lean` |
| $Q_n$ marginal sufficiency | `dagCarberyFunctional_marginal_sufficiency` | `DagFunctional.lean` |
| $Q_n$ monotonicity | `dagCarberyFunctional_mono` | `QnStability.lean` |
| $Q_n$ boundedness | `dagCarberyFunctional_le_card` | `QnStability.lean` |
| $Q_n$ continuity | `dagCarberyFunctional_continuous_in_marginals` | `QnStability.lean` |
| **Numerical** | | |
| $Q_3^{\text{chain}} \neq Q_3^{\text{fork}}$ | `chain_fork_Q4_ne` | `NumericalExamples.lean` |
| $Q_3^{\text{chain}} > Q_3^{\text{fork}}$ | `chain_Q4_gt_fork_Q4` | `NumericalExamples.lean` |

## Building

Requires [Lean 4](https://lean-lang.org/) (v4.24.0) and [elan](https://github.com/leanprover/elan).

```bash
git clone https://github.com/eduardo-zambrano/DagTesting.git
cd DagTesting

# Install Mathlib cache (much faster than building from source)
lake exe cache get

# Build
lake build
```

### Dependency: CarberyConcentration

This project depends on [CarberyConcentration](https://github.com/eduardo-zambrano/CarberyConcentration), which formalizes the core Carbery inequality and concentration bounds. The `lakefile.toml` references it via a local path. To build from a fresh clone, you will also need to clone CarberyConcentration and adjust the path in `lakefile.toml`:

```toml
[[require]]
name = "CarberyVersionA"
path = "../CarberyConcentration"   # adjust to your local path
```

## Project Structure

```
DagTesting/
  DagTesting.lean              -- Root import file
  DagTesting/
    DAGBasic.lean              -- FinDAG, parent/child sets, concrete instances
    TopologicalOrdering.lean   -- Orderings, existence theorem
    DagFunctional.lean         -- Q_n^G, Markov factorization, marginal sufficiency
    TestStatistic.lean         -- T_h, admissibility, combined test
    OrderingValidity.lean      -- T_h <= 1 under H_0
    PowerAnalysis.lean         -- Power direction, MI-equivalence (Theorem 6.1)
    NumericalExamples.lean     -- Machine-checked chain vs. fork discrimination
    BootstrapValidity.lean     -- Factorization iff Markov (Theorem 5.3)
    QnStability.lean           -- Monotonicity, boundedness, continuity (Prop 7.4)
```

## Axioms

**Sorry count: 0** --- all theorems are fully proved.

The single external axiom, inherited from CarberyConcentration:

- `carberyInequality`: For a joint PMF $p$ on finite state spaces and nonnegative functions $h_i$, $\mathbb{E}[\prod_i h_i(X_i)] \leq Q_n(p)^{1/(n+1)} \cdot \prod_i \|h_i\|_{n+1}$.

This is Carbery's (2004) multilinear Cauchy--Schwarz inequality, a published result in the Proceedings of the AMS.

## Lebesgue vs. Expectation Form

The Lean formalization works with the **Lebesgue (counting-measure) form** of Carbery's inequality, where norms are $L^{n+1}$ norms over finite state spaces. The paper's test statistic uses the **expectation form**, which includes density correction factors $p_i(X_i)^{1/(n+1)}$. The two forms are equivalent via the substitution $f_i = g_i \cdot p_i^{1/(n+1)}$ (Definition 2.9 and Lemma 2.10 in the paper).

## Citation

```bibtex
@article{zambrano2026testing,
  title={Testing Causal {DAG} Structures via Moment Inequalities},
  author={Zambrano, Eduardo},
  year={2026},
  journal={Working paper}
}
```

## License

Apache 2.0
