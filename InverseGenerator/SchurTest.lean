/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Mul

/-!
# The weighted Schur test

If a matrix `R` admits positive weights `u`, `v` with
```
∑ q, ‖R p q‖ * v q ≤ C * u p     (row test)
∑ p, ‖R p q‖ * u p ≤ C * v q     (column test)
```
then `R` is bounded by `C` on `ℓ²`.  Mathlib has no Schur test, so this file
supplies one; nothing here is specific to the paper.

The paper uses it in Lemma A.4 with `u p = p^{-1/2}`, `v q = (q+1)^{-1/2}` to bound
the block `R = C A⁻¹` of the prefix projection.  That is the *only* place the range
`|θ| < 1/2` enters: the row test needs `θ > -1/2` and the column test needs
`θ < 1/2`.

## Main results

* `schur_sum_sq` : `∑ p ‖∑ q, R p q * x q‖ ^ 2 ≤ C ^ 2 * ∑ q, ‖x q‖ ^ 2`.
  Stated with bare sums, so no norm instance on the index types is required.

## Implementation notes

The proof is the classical weighted Cauchy–Schwarz split
`|R| |x| = √(|R| v) · √(|R| |x|²/v)`, which `Real.sum_sqrt_mul_sqrt_le` supplies
directly, followed by `Finset.sum_comm` to turn the row test into the column test.
Writing it this way avoids ever forming the `√` of a matrix entry.

The sums are written out rather than abbreviated by `set`: a `set` binder leaves
`(fun p => …) p` redexes that block `Finset.sum_comm` from matching the double sum.
-/

namespace InverseGenerator

open Finset

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Weighted Schur test**, elementary form. -/
theorem schur_sum_sq {R : Matrix m n ℂ} {u : m → ℝ} {v : n → ℝ} {C : ℝ}
    (hv : ∀ q, 0 < v q) (hC : 0 ≤ C)
    (hrow : ∀ p, ∑ q, ‖R p q‖ * v q ≤ C * u p)
    (hcol : ∀ q, ∑ p, ‖R p q‖ * u p ≤ C * v q)
    (x : n → ℂ) :
    ∑ p, ‖∑ q, R p q * x q‖ ^ 2 ≤ C ^ 2 * ∑ q, ‖x q‖ ^ 2 := by
  have hSnonneg : ∀ p : m, (0 : ℝ) ≤ ∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q := fun p =>
    sum_nonneg fun q _ => by have := (hv q).le; positivity
  -- Step 1: the weighted Cauchy–Schwarz split, squared, then the row test.
  have step : ∀ p : m, ‖∑ q, R p q * x q‖ ^ 2
      ≤ (C * u p) * ∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q := by
    intro p
    have habs : ‖∑ q, R p q * x q‖ ≤ ∑ q, ‖R p q‖ * ‖x q‖ :=
      (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun q _ => norm_mul _ _))
    have hsplit : ∀ q, Real.sqrt (‖R p q‖ * v q) * Real.sqrt (‖R p q‖ * ‖x q‖ ^ 2 / v q)
        = ‖R p q‖ * ‖x q‖ := by
      intro q
      have hvq := (hv q).ne'
      rw [← Real.sqrt_mul (by have := (hv q).le; positivity),
        show ‖R p q‖ * v q * (‖R p q‖ * ‖x q‖ ^ 2 / v q) = (‖R p q‖ * ‖x q‖) ^ 2 from by
          field_simp
          try ring]
      exact Real.sqrt_sq (by positivity)
    have hrowbig : (0 : ℝ) ≤ ∑ q, ‖R p q‖ * v q :=
      sum_nonneg fun q _ => by have := (hv q).le; positivity
    have hCS : ∑ q, ‖R p q‖ * ‖x q‖
        ≤ Real.sqrt (∑ q, ‖R p q‖ * v q)
            * Real.sqrt (∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q) :=
      calc ∑ q, ‖R p q‖ * ‖x q‖
          = ∑ q, Real.sqrt (‖R p q‖ * v q)
              * Real.sqrt (‖R p q‖ * ‖x q‖ ^ 2 / v q) :=
            sum_congr rfl fun q _ => (hsplit q).symm
        _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
              (fun q => by have := (hv q).le; positivity)
              (fun q => by have := (hv q).le; positivity)
    have hnn : (0 : ℝ) ≤ ∑ q, ‖R p q‖ * ‖x q‖ := sum_nonneg fun q _ => by positivity
    calc ‖∑ q, R p q * x q‖ ^ 2
        ≤ (∑ q, ‖R p q‖ * ‖x q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) habs 2
      _ ≤ (Real.sqrt (∑ q, ‖R p q‖ * v q)
            * Real.sqrt (∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q)) ^ 2 :=
          pow_le_pow_left₀ hnn hCS 2
      _ = (∑ q, ‖R p q‖ * v q) * ∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q := by
          rw [mul_pow, Real.sq_sqrt hrowbig, Real.sq_sqrt (hSnonneg p)]
      _ ≤ (C * u p) * ∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q :=
          mul_le_mul_of_nonneg_right (hrow p) (hSnonneg p)
  -- Step 2: swap the order of summation to expose the column test.
  have expand : ∑ p, (C * u p) * ∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q
      = ∑ q, (C * (‖x q‖ ^ 2 / v q)) * ∑ p, ‖R p q‖ * u p := by
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun q _ => sum_congr rfl fun p _ => by ring
  calc ∑ p, ‖∑ q, R p q * x q‖ ^ 2
      ≤ ∑ p, (C * u p) * ∑ q, ‖R p q‖ * ‖x q‖ ^ 2 / v q := sum_le_sum fun p _ => step p
    _ = ∑ q, (C * (‖x q‖ ^ 2 / v q)) * ∑ p, ‖R p q‖ * u p := expand
    _ ≤ ∑ q, (C * (‖x q‖ ^ 2 / v q)) * (C * v q) := by
        refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hcol q) ?_
        have := (hv q).le
        positivity
    _ = C ^ 2 * ∑ q, ‖x q‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun q _ => ?_
        have hvq := (hv q).ne'
        field_simp
        try ring

/-! ## Bridge to the `ℓ²` operator norm

`schur_sum_sq` is stated for bare sums.  The two lemmas below package it as a bound
on `Matrix.l2_opNorm`, which is what Lemma A.4 and Lemma A.3 need.  Note the
scoped instance: `‖·‖` on matrices means the `ℓ²`-operator norm only inside
`Matrix.Norms.L2Operator`.
-/

section OpNorm

open scoped Matrix.Norms.L2Operator

variable [DecidableEq n]

/-- `‖A‖ ≤ C` from the vector bound.  `Matrix.l2_opNorm_def` is `rfl` to the norm of
the associated continuous linear map, so `ContinuousLinearMap.opNorm_le_bound`
applies directly. -/
theorem l2_opNorm_le_of_mulVec {A : Matrix m n ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : EuclideanSpace ℂ n,
      ‖(EuclideanSpace.equiv m ℂ).symm (Matrix.mulVec A x)‖ ≤ C * ‖x‖) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h

/-- `‖A‖ ≤ C` from the **bare-sum** quadratic bound.  This is the same reduction as
in `l2_opNorm_le_of_schur`, factored out so that callers never touch
`EuclideanSpace`: all `WithLp` coercion friction stays inside the single `rfl`
below, which also keeps elaboration cheap. -/
theorem l2_opNorm_le_of_sum_sq {A : Matrix m n ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : n → ℂ, ∑ p, ‖∑ q, A p q * x q‖ ^ 2 ≤ C ^ 2 * ∑ q, ‖x q‖ ^ 2) :
    ‖A‖ ≤ C := by
  refine l2_opNorm_le_of_mulVec hC fun x => ?_
  have hpt : ∀ p : m,
      (EuclideanSpace.equiv m ℂ).symm (Matrix.mulVec A x) p = ∑ q, A p q * x q :=
    fun _ => rfl
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Finset.sum_congr rfl (fun p _ => by rw [hpt p] : ∀ p ∈ Finset.univ,
      ‖(EuclideanSpace.equiv m ℂ).symm (Matrix.mulVec A x) p‖ ^ 2
        = ‖∑ q, A p q * x q‖ ^ 2)]
  calc Real.sqrt (∑ p, ‖∑ q, A p q * x q‖ ^ 2)
      ≤ Real.sqrt (C ^ 2 * ∑ q, ‖x q‖ ^ 2) := Real.sqrt_le_sqrt (h (x : n → ℂ))
    _ = C * Real.sqrt (∑ q, ‖x q‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC]

/-- **Weighted Schur test**, operator-norm form: the row and column tests give
`‖R‖ ≤ C` in the `ℓ²`-operator norm. -/
theorem l2_opNorm_le_of_schur {R : Matrix m n ℂ} {u : m → ℝ} {v : n → ℝ} {C : ℝ}
    (hv : ∀ q, 0 < v q) (hC : 0 ≤ C)
    (hrow : ∀ p, ∑ q, ‖R p q‖ * v q ≤ C * u p)
    (hcol : ∀ q, ∑ p, ‖R p q‖ * u p ≤ C * v q) :
    ‖R‖ ≤ C := by
  refine l2_opNorm_le_of_mulVec hC fun x => ?_
  have hsq := schur_sum_sq hv hC hrow hcol (x : n → ℂ)
  -- the `EuclideanSpace` coercion is the identity on functions, so this is `rfl`,
  -- but stating it separately keeps it out of the `sqrt` where it is expensive
  have hpt : ∀ p : m,
      (EuclideanSpace.equiv m ℂ).symm (Matrix.mulVec R x) p = ∑ q, R p q * x q :=
    fun _ => rfl
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Finset.sum_congr rfl (fun p _ => by rw [hpt p] : ∀ p ∈ Finset.univ,
      ‖(EuclideanSpace.equiv m ℂ).symm (Matrix.mulVec R x) p‖ ^ 2
        = ‖∑ q, R p q * x q‖ ^ 2)]
  calc Real.sqrt (∑ p, ‖∑ q, R p q * x q‖ ^ 2)
      ≤ Real.sqrt (C ^ 2 * ∑ q, ‖x q‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C * Real.sqrt (∑ q, ‖x q‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC]

/-- The *lower*-bound companion: a bare-sum form of `Matrix.l2_opNorm_mulVec`.

Stating it this way means callers never have to build an `EuclideanSpace` element, so
all `WithLp` coercion friction is confined to this one proof. -/
theorem sqrt_sum_sq_mulVec_le {A : Matrix m n ℂ} (x : n → ℂ) :
    Real.sqrt (∑ p, ‖∑ q, A p q * x q‖ ^ 2) ≤ ‖A‖ * Real.sqrt (∑ q, ‖x q‖ ^ 2) := by
  have h := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv n ℂ).symm x)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  have e1 : ∀ p : m, (EuclideanSpace.equiv m ℂ).symm
      (Matrix.mulVec A ((EuclideanSpace.equiv n ℂ).symm x)) p = ∑ q, A p q * x q :=
    fun _ => rfl
  have e2 : ∀ q : n, ((EuclideanSpace.equiv n ℂ).symm x) q = x q := fun _ => rfl
  simp only [e1, e2] at h
  exact h

end OpNorm

end InverseGenerator
