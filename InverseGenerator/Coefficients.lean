/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Fractional binomial coefficients

The coefficients `a r θ = (θ)_r / r!` of the formal expansion
`(1 - x)^{-θ} = ∑ r, a r θ * x ^ r`, where `(θ)_r = θ(θ+1)⋯(θ+r-1)` is the
rising factorial.  These are the entries of the fractional Toeplitz matrices
`T_n(θ) = (I - R_n)^{-θ}` of Appendix A of the paper.

Everything here is characteristic-zero field algebra: no analysis, no order.
The two `peel` recursions below are the only facts needed to derive the
partial-convolution identity of Lemma A.1, the paper's key combinatorial step.

## Main definitions

* `InverseGenerator.binomCoeff r θ` : the coefficient `a r θ`.

## Main results

* `binomCoeff_succ_mul_right` : peeling the *last* factor of the rising
  factorial, `(r+1) * a (r+1) θ = a r θ * (θ + r)`.
* `binomCoeff_succ_mul_left` : peeling the *first* factor,
  `(r+1) * a (r+1) θ = θ * a r (θ + 1)`.
* `sum_binomCoeff` : the finite hockey-stick identity
  `∑ r ∈ range (m+1), a r θ = a m (θ + 1)` (the hockey-stick form of `convolutionid`).

Both recursions are stated in *cleared* form (multiplied through by `r+1`)
rather than as `a (r+1) θ = …/(r+1)`: this avoids a nonvanishing side condition
at every rewrite, and makes them directly usable by `linear_combination`.
-/

namespace InverseGenerator

open Finset

variable {K : Type*} [Field K] [CharZero K]

/-- The fractional binomial coefficient `a r θ = (θ)_r / r!`, where
`(θ)_r = θ(θ+1)⋯(θ+r-1)` is the rising factorial. -/
noncomputable def binomCoeff (r : ℕ) (θ : K) : K :=
  (∏ i ∈ range r, (θ + (i : K))) / (Nat.factorial r : K)

@[simp]
theorem binomCoeff_zero (θ : K) : binomCoeff 0 θ = 1 := by
  simp [binomCoeff]

/-- `r!` is nonzero in a characteristic-zero field. -/
theorem cast_factorial_ne_zero (r : ℕ) : ((Nat.factorial r : K)) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)

/-- `(r : K) + 1 ≠ 0` in a characteristic-zero field. -/
theorem cast_succ_ne_zero (r : ℕ) : ((r : K) + 1) ≠ 0 := by
  have h : ((r + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)
  push_cast at h
  exact h

omit [CharZero K] in
theorem cast_factorial_succ (r : ℕ) :
    ((Nat.factorial (r + 1) : ℕ) : K) = ((r : K) + 1) * (Nat.factorial r : K) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- Peeling the **last** factor of the rising factorial:
`(r+1) * a (r+1) θ = a r θ * (θ + r)`.  This is the recursion used to step `p`
upwards in Lemma A.1. -/
theorem binomCoeff_succ_mul_right (r : ℕ) (θ : K) :
    ((r : K) + 1) * binomCoeff (r + 1) θ = binomCoeff r θ * (θ + r) := by
  unfold binomCoeff
  rw [prod_range_succ, cast_factorial_succ]
  have h1 : ((r : K) + 1) ≠ 0 := cast_succ_ne_zero r
  have h2 : ((Nat.factorial r : K)) ≠ 0 := cast_factorial_ne_zero r
  field_simp

/-- Peeling the **first** factor of the rising factorial:
`(r+1) * a (r+1) θ = θ * a r (θ + 1)`.  Shifting the argument by one is what
converts `a (q+1) (-θ)` into `a q (1 - θ)`, the move that makes Lemma A.1
close. -/
theorem binomCoeff_succ_mul_left (r : ℕ) (θ : K) :
    ((r : K) + 1) * binomCoeff (r + 1) θ = θ * binomCoeff r (θ + 1) := by
  unfold binomCoeff
  rw [prod_range_succ']
  have hshift : ∏ i ∈ range r, (θ + ((i + 1 : ℕ) : K))
      = ∏ i ∈ range r, (θ + 1 + (i : K)) := by
    refine prod_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [hshift, cast_factorial_succ]
  have h1 : ((r : K) + 1) ≠ 0 := cast_succ_ne_zero r
  have h2 : ((Nat.factorial r : K)) ≠ 0 := cast_factorial_ne_zero r
  push_cast
  field_simp
  ring

/-- The shifted-argument form of `binomCoeff_succ_mul_left` specialised to `-θ`,
which is how it is used in Lemma A.1: `(q+1) * a (q+1) (-θ) = -θ * a q (1 - θ)`. -/
theorem binomCoeff_succ_mul_neg (r : ℕ) (θ : K) :
    ((r : K) + 1) * binomCoeff (r + 1) (-θ) = -θ * binomCoeff r (1 - θ) := by
  have h := binomCoeff_succ_mul_left r (-θ)
  rw [show (-θ + 1 : K) = 1 - θ by ring] at h
  exact h

/-- The finite hockey-stick identity, the hockey-stick form of `convolutionid`:
`∑ r ∈ range (m+1), a r θ = a m (θ + 1)`. -/
theorem sum_binomCoeff (m : ℕ) (θ : K) :
    ∑ r ∈ range (m + 1), binomCoeff r θ = binomCoeff m (θ + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    -- Cleared form of `a (m+1) (θ+1) - a m (θ+1) = a (m+1) θ`: multiply by `m+1`
    -- and eliminate both `a (m+1) _` terms via the two peel recursions.
    have hne : ((m : K) + 1) ≠ 0 := cast_succ_ne_zero m
    refine mul_left_cancel₀ hne ?_
    rw [mul_add, binomCoeff_succ_mul_right m (θ + 1), binomCoeff_succ_mul_left m θ]
    ring

omit [CharZero K] in
/-- `a r 0 = 0` for `r ≥ 1`: the rising factorial has a zero factor. -/
theorem binomCoeff_eq_zero_of_arg_zero {r : ℕ} (hr : 1 ≤ r) : binomCoeff r (0 : K) = 0 := by
  rw [binomCoeff, prod_eq_zero (mem_range.mpr hr) (by norm_num), zero_div]

/-! ### Agreement with the paper's displayed matrix

The paper writes `T_n(θ)` out explicitly in Appendix A.  Its subdiagonal entries are
`θ`, `θ(θ+1)/2`, `θ(θ+1)(θ+2)/6` and `θ(θ+1)(θ+2)(θ+3)/24`.  Checking these
against `binomCoeff` validates the *definition* against the source — something no
downstream theorem can do, since every later result is stated in terms of
`binomCoeff` itself.
-/

/-! ### The Vandermonde convolution

`binomCoeff` coincides with Mathlib's `Ring.multichoose`, so the Chu–Vandermonde
identity for binomial rings (`Ring.add_choose_eq`) can be reused rather than
reproved.  The bridge runs through `a r θ = (-1)^r * Ring.choose (-θ) r`, since
Chu–Vandermonde is stated for `Ring.choose` at a *fixed* pair of arguments while
`multichoose` shifts its first argument with the index.

This convolution is exactly the coefficient identity behind the group law
`T_n(θ) T_n(η) = T_n(θ+η)` of Lemma A.1, and hence behind
`T_n(θ)⁻¹ = T_n(-θ)`.
-/

open Polynomial in
omit [CharZero K] in
theorem smeval_ascPochhammer_eq_prod (r : ℕ) (θ : K) :
    (ascPochhammer ℕ r).smeval θ = ∏ i ∈ range r, (θ + (i : K)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ascPochhammer_succ_right, smeval_mul, ih, prod_range_succ, smeval_add, smeval_X,
      ← C_eq_natCast, smeval_C]
    simp

/-- `binomCoeff` is Mathlib's `Ring.multichoose`. -/
theorem binomCoeff_eq_multichoose (r : ℕ) (θ : K) :
    binomCoeff r θ = Ring.multichoose θ r := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer θ r
  rw [smeval_ascPochhammer_eq_prod] at h
  rw [binomCoeff, ← h, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (cast_factorial_ne_zero r)

/-- `a r θ = (-1)^r * Ring.choose (-θ) r`, the sign-flip bridge to `Ring.choose`. -/
theorem binomCoeff_eq_choose_neg (r : ℕ) (θ : K) :
    binomCoeff r θ = (-1 : K) ^ r * Ring.choose (-θ) r := by
  rw [binomCoeff_eq_multichoose, Ring.choose_neg', Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow_natCast, ← mul_assoc, ← mul_pow]
  norm_num

/-- **Vandermonde convolution**: `∑ r ≤ k, a r θ * a (k-r) η = a k (θ+η)`.
This is the coefficient form of the group law, `convolutionid` of Lemma A.1. -/
theorem vandermonde (k : ℕ) (θ η : K) :
    ∑ r ∈ range (k + 1), binomCoeff r θ * binomCoeff (k - r) η = binomCoeff k (θ + η) := by
  have hV := Ring.add_choose_eq (R := K) (r := -θ) (s := -η) k (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hV
  rw [binomCoeff_eq_choose_neg, show -(θ + η) = -θ + -η from by ring, hV, Finset.mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrk : r ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [binomCoeff_eq_choose_neg, binomCoeff_eq_choose_neg,
    show (-1 : K) ^ k = (-1 : K) ^ r * (-1 : K) ^ (k - r) from by
      rw [← pow_add, Nat.add_sub_cancel' hrk]]
  ring

end InverseGenerator
