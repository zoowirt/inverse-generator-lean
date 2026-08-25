# Theorem 1.1 of *A solution to the inverse generator problem and related questions*, in Lean 4

[![CI](https://github.com/zoowirt/inverse-generator-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/zoowirt/inverse-generator-lean/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.0--rc1-blue)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.0--rc1-blue)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

A complete, machine-checked proof of **Theorem 1.1** of

> E. Lorist, M. Meyries, M. Veraar,
> *A solution to the inverse generator problem and related questions*,
> [arXiv:2608.06272](https://arxiv.org/abs/2608.06272) (version 2).

The development is self-contained on top of [Mathlib](https://github.com/leanprover-community/mathlib4):
it contains no `sorry`, no `native_decide`, and no numerical or floating-point step.
The final result depends only on Lean's three standard axioms.

```
#print axioms InverseGenerator.theorem_finite
-- 'InverseGenerator.theorem_finite' depends on axioms:
--     [propext, Classical.choice, Quot.sound]
```

## The theorem

Theorem 1.1 asserts the existence of finite-dimensional witnesses for the inverse
generator problem, with an explicit absolute constant `C = 50`.  Let `α ∈ (0,1)`,
let `(y_k)` be the doubly exponential sequence `y₁ = 2`, `y_{k+1} = y_k² + 1`, and
set `ω_n = 1/y_{2n+1}`.  Then for every `n ≥ 1` there is an invertible, diagonalizable
`A_n ∈ M_{2n}(ℂ)` with

| | |
|---|---|
| `‖A_n‖ ≤ 1 + Cα/(1-α)` | uniformly bounded generator |
| `‖A_n⁻¹‖ ≤ ω_n^{-1/2}(1 + Cα/(1-α))` | controlled inverse |
| `‖e^{tA_n}‖ ≤ (1 + Cα/(1-α)) e^{-ω_n t}`, `t ≥ 0` | exponentially stable semigroup |
| `n^α/C ≤ ‖e^{π A_n⁻¹}‖ ≤ n^α` | the inverse generator is **not** uniformly bounded |
| `n ≤ log log(ω_n⁻¹) ≤ 2n` | doubly exponential decay rate |
| `σ(A_n) ⊆ {Re z ≤ -ω_n, \|z\| ≥ ω_n^{1/2}}` | spectral inclusion |
| `σ(A_n⁻¹) ⊆ {Re z = -1, \|z\| ≤ ω_n^{-1/2}}` | spectral inclusion |

All norms are `ℓ²`-operator norms, as in the paper.

In Lean, the statement is the `Prop` [`InverseGenerator.TheoremFinite`](InverseGenerator/TheoremFinite.lean)
and the proof is

```lean
theorem theorem_finite : TheoremFinite
```

in [`InverseGenerator/TheoremFinite.lean`](InverseGenerator/TheoremFinite.lean).  The
paper's suprema over `n` and `t` are rendered as universally quantified inequalities
and the two set inclusions as membership implications; both are equivalent and avoid
`sSup` side conditions.  The matrix `A_n` itself is `blockGen n α`, defined in
[`InverseGenerator/Blocks.lean`](InverseGenerator/Blocks.lean), which also documents
in what sense the formal statement *is* the paper's statement (dimension, choice of
norm, indexing of the eigenvalues).

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain in
[`lean-toolchain`](lean-toolchain) is fetched automatically.

```bash
git clone https://github.com/zoowirt/inverse-generator-lean.git
cd inverse-generator-lean
lake exe cache get     # download the prebuilt Mathlib olean files
lake build             # under a minute once the cache is in place
```

`lake build` type-checks the whole development, including the
`#guard_msgs`-protected `#print axioms` at the end of `TheoremFinite.lean`.  If the
build succeeds, Theorem 1.1 is proved.

Mathlib is pinned in [`lake-manifest.json`](lake-manifest.json) and nothing in this
repository auto-upgrades it, so the build stays reproducible.

## How the files correspond to the paper

The construction lives in §2 of the paper; the basis it rests on is Proposition 2.1,
proved in Appendix A.  Reading order is bottom-up.

| File | Paper |
|---|---|
| [`Coefficients.lean`](InverseGenerator/Coefficients.lean) | the generalized binomial coefficients `a_r(θ)` of Appendix A, and `convolutionid` |
| [`Toeplitz.lean`](InverseGenerator/Toeplitz.lean) | the fractional Toeplitz matrices `T_n(θ) = (I - R_n)^{-θ}` and their group law |
| [`AnalyticIneq.lean`](InverseGenerator/AnalyticIneq.lean) | the elementary inequalities the explicit constants force (`e^π ≤ 25`, `e ≤ 4 log 2`, …) |
| [`HarmonicBounds.lean`](InverseGenerator/HarmonicBounds.lean) | `log m + 1/2 ≤ H_m ≤ 1 + log m` |
| [`RpowSums.lean`](InverseGenerator/RpowSums.lean) | `eq:elementary-power-sums`, the `p`-series comparisons |
| [`CoeffBounds.lean`](InverseGenerator/CoeffBounds.lean) | **Lemma A.2**, the two-sided bounds on `a_r(θ)` |
| [`PrefixBound.lean`](InverseGenerator/PrefixBound.lean) | **Lemma A.1**, `eq:partial-convolution`, and the block form of `T_n(θ) Π_{n,k} T_n(-θ)` |
| [`SchurTest.lean`](InverseGenerator/SchurTest.lean) | the weighted Schur test (not in Mathlib) |
| [`PrefixNorm.lean`](InverseGenerator/PrefixNorm.lean) | **Lemma A.4**, the uniform prefix bound `‖T_n(θ) Π_{n,k} T_n(-θ) - Π_{n,k}‖ ≤ 6\|θ\|/(1-4θ²)` |
| [`Rotation.lean`](InverseGenerator/Rotation.lean) | **Proposition 2.1, Step 1**: the rotated basis `eq:rotated-basis` and the block form of `Δ_±` |
| [`NormGrowth.lean`](InverseGenerator/NormGrowth.lean) | **Lemma A.3** and the bound `n^α/2 ≤ ‖Δ_±‖ ≤ 2n^α` |
| [`BVMultiplier.lean`](InverseGenerator/BVMultiplier.lean) | **Proposition 2.1, Step 3**: summation by parts |
| [`RotatedPrefix.lean`](InverseGenerator/RotatedPrefix.lean) | **Proposition 2.1, Step 2**: `eq:evenindices`, the odd-index estimate, and the multiplier bound |
| [`Lacunary.lean`](InverseGenerator/Lacunary.lean) | the tower `(y_k)` of §2: parity, growth, summability |
| [`Blocks.lean`](InverseGenerator/Blocks.lean) | the matrices `A_n` of §2, and `e^{π A_n⁻¹} = e^{-π} Δ_±` |
| [`FlowVariation.lean`](InverseGenerator/FlowVariation.lean) | **Lemma 2.2**, `eq:shifted-exponential-variation` |
| [`TheoremFinite.lean`](InverseGenerator/TheoremFinite.lean) | **Theorem 1.1** |

Every declaration in the repository is reachable from `theorem_finite`, with a single
deliberate exception: `card_blockIndex` in `Blocks.lean`, which records that the index
type has `2n` elements and so exists only to make the statement auditable.

## Where the Lean proof takes a different route

Two steps of the proof of Proposition 2.1 are mechanized differently.  Neither is a
correction: both establish what the paper establishes, by a path that is cheaper to
formalize.  Both are documented at the declaration concerned, in
[`RotatedPrefix.lean`](InverseGenerator/RotatedPrefix.lean).

* **The row-norm bound** (`sum_sq_synthRow_le`).  The paper derives
  `‖v_{2j-1}‖² = 1 + ‖v_{2j-1} - w_{2j-1}‖²` from the orthogonality
  `(T_n(θ)* - I)e_j ⊥ e_j`.  Lean gets the same bound from
  `sum_sq_le_add_of_support`, the coordinatewise form of that step: at each coordinate
  either the reference vector vanishes or the two vectors agree, so the squared norms
  add termwise.  The gain is the shape of what follows — the triangle inequality
  `‖v‖ ≤ 1 + ‖v - w‖` would leave an irrational cross term `√(t_α/2)`, whereas the
  squared form keeps the closing inequality polynomial in `α`.
* **The rank-one estimate** (`l2_opNorm_coordProjZ_sub_le`).  The paper proves
  `‖E_{n,2j-1} - F_{n,2j-1}‖ ≤ (√13/2)·α/(1-α)`; Lean proves the rounder `2α/(1-α)`,
  which the budget still allows, since `3 + 2` is exactly the `5` of Proposition 2.1.
  The weaker constant is the price of the method: instead of manipulating the sum of
  square roots `‖z-w‖‖v‖ + ‖v-w‖`, the bound is squared through `(P+Q)² ≤ 2(P²+Q²)`,
  reducing the step to the numeric inequality `13/4 ≤ 4`.  That squaring is exactly
  tight against `√13/2` as `α → 0`, so it cannot reach the paper's constant — and does
  not need to.

Two further conveniences: the Schur row and column tests are parametrized over the
kernel constant, so they are one proof rather than two mirror images; and all `p`-series
estimates telescope against Bernoulli's inequality, so the development needs no measure
theory.

## Continuous integration

[`.github/workflows/ci.yml`](.github/workflows/ci.yml) builds the project from source on
every push and pull request, and checks three things:

1. `lake build --wfail` — every file elaborates, and *no* warning is emitted; in
   particular a `sorry` anywhere fails the build.
2. `leanchecker` — the compiled environment is replayed through an independent kernel,
   so the result does not depend on the elaborator being correct.
3. `axiom-audit` — nothing in the `InverseGenerator` namespace depends on an axiom
   outside `propext`, `Classical.choice`, `Quot.sound`.

## Citing

See [`CITATION.cff`](CITATION.cff).  Please cite the paper alongside this repository.

## License

Apache 2.0 — see [`LICENSE`](LICENSE).
