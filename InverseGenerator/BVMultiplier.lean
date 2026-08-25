/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Bounded-variation multipliers

Step 3 of the paper's proof of Proposition 2.1, in abstract form: for a basis
`(f_k)_{k<N}` with coordinate projections `E_k` and prefix projections
`Q_m = ∑_{j<m} E_j` of norm at most `K`,
```
‖∑_{k<N} c_k E_k‖ ≤ |c_{N-1}| ‖Q_N‖ + K ∑_{k<N-1} |c_{k+1} - c_k|.
```
So a multiplier is bounded by the *total variation* of its symbol, times the basis
constant — the mechanism that makes `A_n` bounded and its flow exponentially decaying
uniformly in time, even though the basis is badly conditional.

The only input is Abel summation, `Finset.sum_range_by_parts`:
```
∑_{k<N} c_k E_k = c_{N-1} Q_N - ∑_{k<N-1} (c_{k+1} - c_k) Q_{k+1},
```
after which the bound is the triangle inequality.  Nothing here is specific to
Toeplitz matrices, so it is stated for an arbitrary normed module.

## Main results

* `norm_sum_smul_le` : the estimate above, for `E : ℕ → M` in any normed module.
-/

namespace InverseGenerator

open Finset

variable {𝕜 M : Type*} [NormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]

/-- **Summation by parts** (Proposition 2.1, Step 3): the bounded-variation
multiplier bound.

`K` bounds the prefix projections `Q_{k+1}` for `k < N - 1`; the final prefix `Q_N`
appears separately, since in the application it is the identity. -/
theorem norm_sum_smul_le (N : ℕ) (c : ℕ → 𝕜) (E : ℕ → M) (K : ℝ)
    (hQ : ∀ k ∈ range (N - 1), ‖∑ j ∈ range (k + 1), E j‖ ≤ K) :
    ‖∑ k ∈ range N, c k • E k‖
      ≤ ‖c (N - 1)‖ * ‖∑ j ∈ range N, E j‖
        + K * ∑ k ∈ range (N - 1), ‖c (k + 1) - c k‖ := by
  rw [Finset.sum_range_by_parts]
  refine (norm_sub_le _ _).trans (add_le_add (norm_smul_le _ _) ?_)
  calc ‖∑ k ∈ range (N - 1), (c (k + 1) - c k) • ∑ j ∈ range (k + 1), E j‖
      ≤ ∑ k ∈ range (N - 1), ‖(c (k + 1) - c k) • ∑ j ∈ range (k + 1), E j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ range (N - 1), ‖c (k + 1) - c k‖ * K := by
        refine sum_le_sum fun k hk => (norm_smul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (hQ k hk) (norm_nonneg _)
    _ = K * ∑ k ∈ range (N - 1), ‖c (k + 1) - c k‖ := by
        rw [← sum_mul, mul_comm]

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [NormOneClass A]

end InverseGenerator
