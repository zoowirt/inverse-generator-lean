/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.Coefficients
import InverseGenerator.HarmonicBounds
import InverseGenerator.RpowSums
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma A.2: two-sided bounds on the fractional binomial coefficients

The paper's Lemma A.2 gives explicit two-sided bounds on `a_r(θ)`, with constants
that vanish as `θ → 0`.  The route taken here is the exact product formula
```
a_m(t+1) = ∏_{ℓ=1}^m (1 + t/ℓ)          (`binomCoeff_add_one_eq_coeffProd`)
```
which follows from the peel recursion by induction.  Taking logarithms converts the
product into `t · H_m` plus a convergent error, so `log (m+1) ≤ H_m ≤ 1 + log m` and
`∑ 1/ℓ² ≤ 2` from `HarmonicBounds.lean` give bounds with **explicit constants** — no
Stirling, no Gamma asymptotics, no `IsTheta` machinery.

## Main results

* `coeffProd_le_rpow_succ` : `∏ (1+t/ℓ) ≤ (m+1)^t` for `-1 ≤ t ≤ 0`.
* `rpow_succ_le_coeffProd` : `(m+1)^t ≤ ∏ (1+t/ℓ)` for `0 ≤ t ≤ 1`.
* `coeffProd_le_three_half_rpow_succ` : `∏ (1+t/ℓ) ≤ (3/2)(m+1)^t` for `0 ≤ t ≤ 1`.
* `abs_binomCoeff_le_mul_rpow`, `binomCoeff_le_three_half_mul_rpow` — Lemma A.2
  proper: `|a_p(θ)| ≤ |θ| p^{θ-1}` for `-1 < θ ≤ 0`, and
  `a_p(θ) ≤ (3/2) θ p^{θ-1}` for `0 ≤ θ ≤ 1`.
* `sum_abs_binomCoeff_neg_le_two`, `sum_abs_binomCoeff_le_two_rpow` — the `ℓ¹` sums.
* `sum_sq_binomCoeff_tail_pos`, `sum_sq_binomCoeff_tail_neg` — the `ℓ²` tails
  `∑_{r ≥ 1} a_r(θ)² = O(θ²)`.

## Implementation notes

The `|θ|` factor in front of every bound is the whole point: it is what
makes the prefix estimate, and hence Theorem 1.1's constant, vanish as `α → 0`.  It
comes from the peel `a_{p}(θ) = (θ/p) ∏_{ℓ<p}(1 + (θ-1)/ℓ)`, which isolates a single
factor of `θ` before the product is bounded.

The sharp side of the two-sided `rpow` comparison uses the elementary convexity
inequalities of `AnalyticIneq.lean` rather than Stirling or Gamma asymptotics, so
every constant is explicit and no asymptotic (`IsTheta`) machinery is involved.
-/

namespace InverseGenerator

open Finset

/-- `∏_{ℓ=1}^m (1 + t/ℓ)`.  Equals `a_m(t+1)`; see
`binomCoeff_add_one_eq_coeffProd`. -/
noncomputable def coeffProd (t : ℝ) (m : ℕ) : ℝ := ∏ ℓ ∈ Icc 1 m, (1 + t / ℓ)

@[simp] theorem coeffProd_zero (t : ℝ) : coeffProd t 0 = 1 := by simp [coeffProd]

theorem coeffProd_succ (t : ℝ) (m : ℕ) :
    coeffProd t (m + 1) = coeffProd t m * (1 + t / ((m : ℝ) + 1)) := by
  rw [coeffProd, coeffProd, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)]
  push_cast
  ring

/-- Each factor `1 + t/ℓ` is positive when `t > -1` and `ℓ ≥ 1`. -/
theorem one_add_div_pos {t : ℝ} (ht : -1 < t) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 0 < 1 + t / ℓ := by
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have : -1 < t / ℓ := by
    rw [lt_div_iff₀ hℓ0]
    nlinarith
  linarith

theorem coeffProd_pos {t : ℝ} (ht : -1 < t) (m : ℕ) : 0 < coeffProd t m :=
  Finset.prod_pos fun _ℓ hℓ => one_add_div_pos ht (Finset.mem_Icc.mp hℓ).1

/-- **The product formula**: `a_m(t+1) = ∏_{ℓ=1}^m (1 + t/ℓ)`.

This is the identity that makes Lemma A.2 elementary. -/
theorem binomCoeff_add_one_eq_coeffProd (t : ℝ) (m : ℕ) :
    binomCoeff m (t + 1) = coeffProd t m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := binomCoeff_succ_mul_right m (t + 1)
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    rw [coeffProd_succ, ← ih]
    field_simp
    linear_combination h

/-! ## Consequences for `binomCoeff` itself

Two facts, both immediate from the product formula, that the norm estimates need:
the sign of `a_r(θ)` for `θ ≥ 0`, and its sign for `θ ≤ 0` after the first index.
-/

/-- For `θ ≥ 0` all coefficients are nonnegative, so `|a_r θ| = a_r θ`. -/
theorem binomCoeff_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (r : ℕ) : 0 ≤ binomCoeff r θ := by
  rw [binomCoeff]
  refine div_nonneg (Finset.prod_nonneg fun i _ => ?_) (by positivity)
  have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

/-! ## The sharp `rpow` bounds (Lemma A.2)

Lemma A.2, with explicit constants that vanish with `θ`.  These feed the Schur-test
kernel bound of Lemma A.4 and the `ℓ²` column bounds of Proposition 2.1:

* `|a_p(θ)| ≤ |θ| p^{θ-1}` for `-1 < θ ≤ 0`;
* `a_p(θ) ≤ min{(3/2) θ p^{θ-1}, (p+1)^{θ-1}}` and `(p+1)^{θ-1} ≤ a_p(θ)` for `0 < θ ≤ 1`;
* `a_p(θ) ≤ θ p^{θ-1}` for `1 < θ < 2` (as `coeffProd t m ≤ (1+t) m^t`).

Everything is phrased through `coeffProd` and the peel identity
`a_{r+1}(θ) = θ · coeffProd θ r / (r+1)`.  The `3/2` bound is the delicate one: it
needs the sharpened harmonic bound `H_m ≥ log m + 1/2`
(`log_add_half_le_harmonicSum'`), the second-order bound `log(1-x) ≤ -x - x²/2`
(`log_one_sub_le`) and the numeric `e^{3/8} ≤ 3/2` (`exp_three_eighths_le`).
-/

/-- The explicit first-factor peel: `a_{r+1}(θ) = θ · coeffProd θ r / (r+1)`. -/
theorem binomCoeff_succ_eq (r : ℕ) (θ : ℝ) :
    binomCoeff (r + 1) θ = θ * coeffProd θ r / ((r : ℝ) + 1) := by
  have hkey := binomCoeff_succ_mul_left r θ
  rw [binomCoeff_add_one_eq_coeffProd] at hkey
  have hne : ((r : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linear_combination hkey

/-- Single-factor Bernoulli comparison, downward: `1 + t/x ≤ ((x+1)/x)^t` for
`-1 ≤ t ≤ 0` and `x ≥ 1`. -/
theorem one_add_div_le_rpow_ratio {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) {x : ℝ}
    (hx : 1 ≤ x) : 1 + t / x ≤ ((x + 1) / x) ^ t := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hbase : (0 : ℝ) < (x + 1) / x := by positivity
  have hinvx : (0 : ℝ) ≤ 1 / x := by positivity
  -- `(1 + 1/x)^{-t} ≤ 1 + (-t)/x`
  have hb : ((x + 1) / x) ^ (-t) ≤ 1 + -t / x := by
    have h := rpow_one_add_le_one_add_mul_self (s := 1 / x)
      (by linarith : (-1 : ℝ) ≤ 1 / x) (by linarith : (0 : ℝ) ≤ -t)
      (by linarith : -t ≤ 1)
    calc ((x + 1) / x) ^ (-t) = (1 + 1 / x) ^ (-t) := by
          rw [show (x + 1) / x = 1 + 1 / x from by field_simp]
      _ ≤ 1 + -t * (1 / x) := h
      _ = 1 + -t / x := by ring
  have hupos : (0 : ℝ) < ((x + 1) / x) ^ (-t) := Real.rpow_pos_of_pos hbase _
  have hntx : (0 : ℝ) ≤ -t / x := div_nonneg (by linarith) hx0.le
  have h1 : 1 - -t / x ≤ (1 + -t / x)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 + -t / x)]
    nlinarith [sq_nonneg (-t / x)]
  have h2 : (1 + -t / x)⁻¹ ≤ (((x + 1) / x) ^ (-t))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hupos hb
  have hfin : ((x + 1) / x) ^ t = (((x + 1) / x) ^ (-t))⁻¹ := by
    rw [← Real.rpow_neg hbase.le, neg_neg]
  rw [hfin]
  calc 1 + t / x = 1 - -t / x := by ring
    _ ≤ (((x + 1) / x) ^ (-t))⁻¹ := h1.trans h2

/-- Bernoulli upper product bound: `coeffProd t m ≤ (m+1)^t` for `-1 ≤ t ≤ 0`.
At `t = θ - 1` this is Lemma A.2's `a_r(θ) ≤ (r+1)^{θ-1}` for `0 ≤ θ ≤ 1`. -/
theorem coeffProd_le_rpow_succ {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) (m : ℕ) :
    coeffProd t m ≤ ((m : ℝ) + 1) ^ t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [coeffProd_succ]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hfac := one_add_div_le_rpow_ratio ht0 ht1 hm1
    have hnn : (0 : ℝ) ≤ 1 + t / ((m : ℝ) + 1) := by
      have hle : -(1 : ℝ) ≤ t / ((m : ℝ) + 1) := by
        rw [neg_le, ← neg_div, div_le_one hm0]
        linarith
      linarith
    have hcomb : ((m : ℝ) + 1) ^ t * (((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) ^ t
        = ((m : ℝ) + 1 + 1) ^ t := by
      rw [← Real.mul_rpow hm0.le (by positivity)]
      congr 1
      field_simp
    calc coeffProd t m * (1 + t / ((m : ℝ) + 1))
        ≤ ((m : ℝ) + 1) ^ t * (((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) ^ t :=
          mul_le_mul ih hfac hnn (Real.rpow_nonneg hm0.le t)
      _ = ((m : ℝ) + 1 + 1) ^ t := hcomb
      _ = (((m + 1 : ℕ) : ℝ) + 1) ^ t := by push_cast; ring_nf

/-- Single-factor Bernoulli comparison, upward: `((x+1)/x)^t ≤ 1 + t/x` for
`0 ≤ t ≤ 1` and `x ≥ 1`. -/
theorem rpow_ratio_le_one_add_div {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : ℝ}
    (hx : 1 ≤ x) : ((x + 1) / x) ^ t ≤ 1 + t / x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hinvx : (0 : ℝ) ≤ 1 / x := by positivity
  have h := rpow_one_add_le_one_add_mul_self (s := 1 / x)
    (by linarith : (-1 : ℝ) ≤ 1 / x) ht0 ht1
  calc ((x + 1) / x) ^ t = (1 + 1 / x) ^ t := by
        rw [show (x + 1) / x = 1 + 1 / x from by field_simp]
    _ ≤ 1 + t * (1 / x) := h
    _ = 1 + t / x := by ring

/-- Bernoulli lower product bound: `(m+1)^t ≤ coeffProd t m` for `0 ≤ t ≤ 1`.
At `t = θ - 1` this is Lemma A.2's `(r+1)^{θ-1} ≤ a_r(θ)` for `1 ≤ θ ≤ 2`. -/
theorem rpow_succ_le_coeffProd {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) :
    ((m : ℝ) + 1) ^ t ≤ coeffProd t m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [coeffProd_succ]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hfac := rpow_ratio_le_one_add_div ht0 ht1 hm1
    have hcp : (0 : ℝ) ≤ coeffProd t m :=
      le_trans (Real.rpow_nonneg hm0.le t) ih
    have hcomb : ((m : ℝ) + 1) ^ t * (((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) ^ t
        = ((m : ℝ) + 1 + 1) ^ t := by
      rw [← Real.mul_rpow hm0.le (by positivity)]
      congr 1
      field_simp
    calc (((m + 1 : ℕ) : ℝ) + 1) ^ t
        = ((m : ℝ) + 1 + 1) ^ t := by push_cast; ring_nf
      _ = ((m : ℝ) + 1) ^ t * (((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) ^ t := hcomb.symm
      _ ≤ coeffProd t m * (1 + t / ((m : ℝ) + 1)) :=
          mul_le_mul ih hfac (Real.rpow_nonneg (by positivity) t) hcp

/-- `coeffProd t m ≤ (1+t) m^t` for `t ≥ 0`, `m ≥ 1`: peel the first factor, then
`H_m - 1 ≤ log m`.  At `t = θ - 1` this is Lemma A.2's `a_r(θ) ≤ θ r^{θ-1}` for
`1 < θ < 2`. -/
theorem coeffProd_le_one_add_self_mul {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    coeffProd t m ≤ (1 + t) * (m : ℝ) ^ t := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [coeffProd, Finset.Icc_eq_cons_Ioc hm, Finset.prod_cons]
  have hprod_pos : ∀ ℓ ∈ Ioc 1 m, (0 : ℝ) < 1 + t / (ℓ : ℝ) := fun ℓ hℓ =>
    one_add_div_pos (by linarith) (le_of_lt (Finset.mem_Ioc.mp hℓ).1)
  have hP : (0 : ℝ) < ∏ ℓ ∈ Ioc 1 m, (1 + t / (ℓ : ℝ)) := Finset.prod_pos hprod_pos
  have hlog : Real.log (∏ ℓ ∈ Ioc 1 m, (1 + t / (ℓ : ℝ))) ≤ t * Real.log m := by
    rw [Real.log_prod (fun ℓ hℓ => (hprod_pos ℓ hℓ).ne')]
    have hH : harmonicSum m = 1 + ∑ ℓ ∈ Ioc 1 m, ((ℓ : ℝ))⁻¹ := by
      rw [harmonicSum, Finset.Icc_eq_cons_Ioc hm, Finset.sum_cons]
      norm_num
    calc ∑ ℓ ∈ Ioc 1 m, Real.log (1 + t / (ℓ : ℝ))
        ≤ ∑ ℓ ∈ Ioc 1 m, t / (ℓ : ℝ) := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          have h := Real.log_le_sub_one_of_pos (hprod_pos ℓ hℓ)
          linarith
      _ = t * ∑ ℓ ∈ Ioc 1 m, ((ℓ : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => div_eq_mul_inv _ _
      _ = t * (harmonicSum m - 1) := by rw [hH]; ring
      _ ≤ t * Real.log m := by
          have h := harmonicSum_le m
          nlinarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hP] at hexp
  have hrp : Real.exp (t * Real.log m) = (m : ℝ) ^ t := by
    rw [Real.rpow_def_of_pos hmR, mul_comm]
  rw [hrp] at hexp
  have hcast : (1 + t / ((1 : ℕ) : ℝ)) = 1 + t := by norm_num
  rw [hcast]
  exact mul_le_mul_of_nonneg_left hexp (by linarith)

/-- `coeffProd t m ≤ (3/2)(m+1)^t` for `0 ≤ t ≤ 1` — the sharp constant of
Lemma A.2's `a_p(θ) ≤ (3/2) θ p^{θ-1}`. -/
theorem coeffProd_le_three_half_rpow_succ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) :
    coeffProd t m ≤ 3 / 2 * ((m : ℝ) + 1) ^ t := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [coeffProd_zero, Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    norm_num
  set β := 1 - t with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  -- the exact identity `coeffProd t M = (M+1) ∏_{ℓ=1}^M (1 - β/(ℓ+1))`
  have hQid : ∀ M : ℕ, coeffProd t M = ((M : ℝ) + 1) * ∏ ℓ ∈ Icc 1 M, (1 - β / ((ℓ : ℝ) + 1)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [coeffProd_succ, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ M + 1)]
      have h1 : ((M : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((M : ℝ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      rw [hβ]
      field_simp
      ring
  have hfac_pos : ∀ ℓ ∈ Icc 1 m, (0 : ℝ) < 1 - β / ((ℓ : ℝ) + 1) := by
    intro ℓ hℓ
    have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hℓ).1
    have hhalf : β / ((ℓ : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  have hQpos : (0 : ℝ) < ∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1)) :=
    Finset.prod_pos hfac_pos
  -- `log Q ≤ -β (H_{m+1} - 1) - β²/8`
  have hlogQ : Real.log (∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1)))
      ≤ -(β * (harmonicSum (m + 1) - 1)) - β ^ 2 / 8 := by
    rw [Real.log_prod (fun ℓ hℓ => (hfac_pos ℓ hℓ).ne')]
    have hterm : ∀ ℓ ∈ Icc 1 m, Real.log (1 - β / ((ℓ : ℝ) + 1))
        ≤ -(β / ((ℓ : ℝ) + 1)) - (β / ((ℓ : ℝ) + 1)) ^ 2 / 2 := by
      intro ℓ hℓ
      have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hℓ).1
      have hx0 : 0 ≤ β / ((ℓ : ℝ) + 1) := by positivity
      have hx1 : β / ((ℓ : ℝ) + 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      exact log_one_sub_le hx0 hx1
    have hHsum : ∑ ℓ ∈ Icc 1 m, β / ((ℓ : ℝ) + 1) = β * (harmonicSum (m + 1) - 1) := by
      have hIco : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
        rw [Finset.Ico_add_one_right_eq_Icc]
      have hshift : ∑ ℓ ∈ Icc 1 m, (((ℓ : ℝ)) + 1)⁻¹
          = ∑ j ∈ Ioc 1 (m + 1), ((j : ℝ))⁻¹ := by
        rw [hIco, ← sum_Ico_add_one_eq_sum_Ioc (fun j => ((j : ℝ))⁻¹) 1 (m + 1)]
        exact Finset.sum_congr rfl fun ℓ _ => by push_cast; ring_nf
      have hH : harmonicSum (m + 1) = 1 + ∑ j ∈ Ioc 1 (m + 1), ((j : ℝ))⁻¹ := by
        rw [harmonicSum, Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ m + 1), Finset.sum_cons]
        norm_num
      calc ∑ ℓ ∈ Icc 1 m, β / ((ℓ : ℝ) + 1)
          = β * ∑ ℓ ∈ Icc 1 m, (((ℓ : ℝ)) + 1)⁻¹ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => div_eq_mul_inv _ _
        _ = β * (harmonicSum (m + 1) - 1) := by rw [hshift, hH]; ring
    have hsq : β ^ 2 / 8 ≤ ∑ ℓ ∈ Icc 1 m, (β / ((ℓ : ℝ) + 1)) ^ 2 / 2 := by
      have h1m : (1 : ℕ) ∈ Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
      have hone : (β / (((1 : ℕ) : ℝ) + 1)) ^ 2 / 2 = β ^ 2 / 8 := by
        norm_num
        ring
      calc β ^ 2 / 8 = (β / (((1 : ℕ) : ℝ) + 1)) ^ 2 / 2 := hone.symm
        _ ≤ ∑ ℓ ∈ Icc 1 m, (β / ((ℓ : ℝ) + 1)) ^ 2 / 2 :=
            Finset.single_le_sum (f := fun ℓ : ℕ => (β / ((ℓ : ℝ) + 1)) ^ 2 / 2)
              (fun ℓ _ => by positivity) h1m
    calc ∑ ℓ ∈ Icc 1 m, Real.log (1 - β / ((ℓ : ℝ) + 1))
        ≤ ∑ ℓ ∈ Icc 1 m, (-(β / ((ℓ : ℝ) + 1)) - (β / ((ℓ : ℝ) + 1)) ^ 2 / 2) :=
          Finset.sum_le_sum hterm
      _ = -(∑ ℓ ∈ Icc 1 m, β / ((ℓ : ℝ) + 1))
            - ∑ ℓ ∈ Icc 1 m, (β / ((ℓ : ℝ) + 1)) ^ 2 / 2 := by
          rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      _ ≤ -(β * (harmonicSum (m + 1) - 1)) - β ^ 2 / 8 := by
          rw [hHsum]
          linarith
  -- exponentiate and use `H_{m+1} ≥ log(m+1) + 1/2`
  have hHlow := log_add_half_le_harmonicSum' (m := m + 1) (by omega)
  have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcast : Real.log ((m + 1 : ℕ) : ℝ) = Real.log ((m : ℝ) + 1) := by push_cast; ring_nf
  rw [hcast] at hHlow
  have hexp1 : Real.log (∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1)))
      ≤ -(β * Real.log ((m : ℝ) + 1)) + (β / 2 - β ^ 2 / 8) := by
    have : β * (Real.log ((m : ℝ) + 1) - 1 / 2) ≤ β * (harmonicSum (m + 1) - 1) := by
      have hmono : Real.log ((m : ℝ) + 1) - 1 / 2 ≤ harmonicSum (m + 1) - 1 := by
        linarith
      exact mul_le_mul_of_nonneg_left hmono hβ0
    calc Real.log (∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1)))
        ≤ -(β * (harmonicSum (m + 1) - 1)) - β ^ 2 / 8 := hlogQ
      _ ≤ -(β * (Real.log ((m : ℝ) + 1) - 1 / 2)) - β ^ 2 / 8 := by linarith
      _ = -(β * Real.log ((m : ℝ) + 1)) + (β / 2 - β ^ 2 / 8) := by ring
  have hbmax : β / 2 - β ^ 2 / 8 ≤ 3 / 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ1) (by linarith : (0 : ℝ) ≤ 3 - β)]
  have hQle : ∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1))
      ≤ 3 / 2 * ((m : ℝ) + 1) ^ (-β) := by
    have hstep : Real.log (∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1)))
        ≤ -(β * Real.log ((m : ℝ) + 1)) + 3 / 8 := by linarith
    have hexp := Real.exp_le_exp.mpr hstep
    rw [Real.exp_log hQpos, Real.exp_add] at hexp
    have hrp : Real.exp (-(β * Real.log ((m : ℝ) + 1))) = ((m : ℝ) + 1) ^ (-β) := by
      rw [Real.rpow_def_of_pos hm1R]
      congr 1
      ring
    rw [hrp] at hexp
    calc ∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1))
        ≤ ((m : ℝ) + 1) ^ (-β) * Real.exp (3 / 8) := hexp
      _ ≤ ((m : ℝ) + 1) ^ (-β) * (3 / 2) :=
          mul_le_mul_of_nonneg_left exp_three_eighths_le (Real.rpow_nonneg hm1R.le _)
      _ = 3 / 2 * ((m : ℝ) + 1) ^ (-β) := by ring
  -- assemble: `(m+1) · Q ≤ (3/2)(m+1)^{1-β} = (3/2)(m+1)^t`
  have hfinal : ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ (-β)) = ((m : ℝ) + 1) ^ t := by
    rw [show ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ (-β))
        = ((m : ℝ) + 1) ^ (1 : ℝ) * (((m : ℝ) + 1) ^ (-β)) from by rw [Real.rpow_one],
      ← Real.rpow_add hm1R]
    congr 1
    rw [hβ]
    ring
  calc coeffProd t m
      = ((m : ℝ) + 1) * ∏ ℓ ∈ Icc 1 m, (1 - β / ((ℓ : ℝ) + 1)) := hQid m
    _ ≤ ((m : ℝ) + 1) * (3 / 2 * ((m : ℝ) + 1) ^ (-β)) :=
        mul_le_mul_of_nonneg_left hQle hm1R.le
    _ = 3 / 2 * (((m : ℝ) + 1) * (((m : ℝ) + 1) ^ (-β))) := by ring
    _ = 3 / 2 * ((m : ℝ) + 1) ^ t := by rw [hfinal]

/-- **Lemma A.2, first row**: `|a_p(θ)| ≤ |θ| p^{θ-1}` for `-1 < θ ≤ 0`, `p ≥ 1`. -/
theorem abs_binomCoeff_le_mul_rpow {θ : ℝ} (hθ0 : -1 < θ) (hθ1 : θ ≤ 0) {p : ℕ}
    (hp : 1 ≤ p) : |binomCoeff p θ| ≤ |θ| * (p : ℝ) ^ (θ - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hcp : (0 : ℝ) < coeffProd θ r := coeffProd_pos hθ0 r
  have hbound : coeffProd θ r ≤ ((r : ℝ) + 1) ^ θ := coeffProd_le_rpow_succ hθ0.le hθ1 r
  have hsplit : ((r : ℝ) + 1) ^ (θ - 1) = ((r : ℝ) + 1) ^ θ / ((r : ℝ) + 1) := by
    rw [Real.rpow_sub hr1, Real.rpow_one]
  rw [binomCoeff_succ_eq, abs_div, abs_mul, abs_of_pos hr1, abs_of_pos hcp]
  push_cast
  rw [hsplit, mul_div_assoc]
  gcongr

/-- **Lemma A.2, the `3/2` bound**: `a_p(θ) ≤ (3/2) θ p^{θ-1}` for `0 < θ ≤ 1`,
`p ≥ 1`.  The `θ` factor is what makes the prefix constant `6|θ|/(1-4θ²)` of
Lemma A.4 vanish as `θ → 0`, and hence `C = 50` reachable. -/
theorem binomCoeff_le_three_half_mul_rpow {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {p : ℕ}
    (hp : 1 ≤ p) : binomCoeff p θ ≤ 3 / 2 * θ * (p : ℝ) ^ (θ - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hkey : coeffProd θ r ≤ 3 / 2 * ((r : ℝ) + 1) ^ θ :=
    coeffProd_le_three_half_rpow_succ hθ0 hθ1 r
  have hsplit : ((r : ℝ) + 1) ^ (θ - 1) = ((r : ℝ) + 1) ^ θ / ((r : ℝ) + 1) := by
    rw [Real.rpow_sub hr1, Real.rpow_one]
  rw [binomCoeff_succ_eq]
  push_cast
  have hmul : θ * coeffProd θ r ≤ 3 / 2 * θ * ((r : ℝ) + 1) ^ θ := by
    calc θ * coeffProd θ r ≤ θ * (3 / 2 * ((r : ℝ) + 1) ^ θ) :=
          mul_le_mul_of_nonneg_left hkey hθ0
      _ = 3 / 2 * θ * ((r : ℝ) + 1) ^ θ := by ring
  calc θ * coeffProd θ r / ((r : ℝ) + 1)
      ≤ 3 / 2 * θ * ((r : ℝ) + 1) ^ θ / ((r : ℝ) + 1) := by gcongr
    _ = 3 / 2 * θ * (((r : ℝ) + 1) ^ θ / ((r : ℝ) + 1)) := by ring
    _ = 3 / 2 * θ * ((r : ℝ) + 1) ^ (θ - 1) := by rw [hsplit]

/-- `a_{r+1}(θ) ≤ 0` for `-1 < θ ≤ 0`: sign of the coefficients at a nonpositive
parameter. -/
theorem binomCoeff_succ_nonpos {θ : ℝ} (hθ0 : -1 < θ) (hθ1 : θ ≤ 0) (r : ℕ) :
    binomCoeff (r + 1) θ ≤ 0 := by
  rw [binomCoeff_succ_eq]
  have h1 : (0 : ℝ) < coeffProd θ r := coeffProd_pos hθ0 r
  have h2 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have h3 : θ * coeffProd θ r ≤ 0 := by nlinarith
  exact div_nonpos_of_nonpos_of_nonneg h3 h2.le

/-- **Lemma A.3 ingredient**: `∑_{r<n} |a_r(-σ)| = 2 - a_{n-1}(1-σ) ≤ 2` for
`0 ≤ σ < 1`.  This is what bounds `‖T_n(-σ)‖ ≤ 2`. -/
theorem sum_abs_binomCoeff_neg_le_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (n : ℕ) :
    ∑ r ∈ range n, |binomCoeff r (-σ)| ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Finset.range_zero, Finset.sum_empty]
    norm_num
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [binomCoeff_zero, abs_one]
  have habs : ∀ k, |binomCoeff (k + 1) (-σ)| = -binomCoeff (k + 1) (-σ) := fun k =>
    abs_of_nonpos (binomCoeff_succ_nonpos (by linarith) (by linarith) k)
  have hsum : ∑ k ∈ range m, binomCoeff (k + 1) (-σ) = binomCoeff m (1 - σ) - 1 := by
    have h := sum_binomCoeff m (-σ)
    rw [Finset.sum_range_succ'] at h
    rw [show (-σ + 1 : ℝ) = 1 - σ from by ring] at h
    simp only [binomCoeff_zero] at h
    linarith
  have hpos : 0 < binomCoeff m (1 - σ) := by
    rw [show (1 - σ : ℝ) = -σ + 1 from by ring, binomCoeff_add_one_eq_coeffProd]
    exact coeffProd_pos (by linarith) m
  have hneg : ∑ k ∈ range m, |binomCoeff (k + 1) (-σ)|
      = -∑ k ∈ range m, binomCoeff (k + 1) (-σ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => habs k
  rw [hneg, hsum]
  linarith

/-- **Lemma A.3 ingredient**: `∑_{r<n} a_r(σ) = coeffProd σ (n-1) ≤ 2 n^σ` for
`0 ≤ σ ≤ 1`.  This is what bounds `‖T_n(σ)‖ ≤ 2 n^σ`. -/
theorem sum_abs_binomCoeff_le_two_rpow {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ r ∈ range n, |binomCoeff r σ| ≤ 2 * (n : ℝ) ^ σ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ σ := Real.one_le_rpow (by exact_mod_cast hn) hσ0
  have habs : ∑ r ∈ range n, |binomCoeff r σ| = ∑ r ∈ range n, binomCoeff r σ :=
    Finset.sum_congr rfl fun r _ => abs_of_nonneg (binomCoeff_nonneg hσ0 r)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [habs, sum_binomCoeff m σ, binomCoeff_add_one_eq_coeffProd]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [coeffProd_zero]
    linarith
  · have h1 := coeffProd_le_one_add_self_mul hσ0 hm
    have hmono : (m : ℝ) ^ σ ≤ ((m + 1 : ℕ) : ℝ) ^ σ := by
      have : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact Real.rpow_le_rpow (Nat.cast_nonneg m) this hσ0
    have h2 : (1 + σ) * (m : ℝ) ^ σ ≤ 2 * ((m + 1 : ℕ) : ℝ) ^ σ := by
      have hp1 : (0 : ℝ) ≤ (m : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg m) σ
      nlinarith
    linarith

/-! ## Square-summable tails (Step 2 of Proposition 2.1)

The odd-index part of the prefix estimate needs the *tails* `∑_{r≥1} a_r(θ)²`
with constants proportional to `θ²`, so that the whole prefix difference is
`O(α/(1-α))`.  Both signs are needed, at `θ = ±α/2`.
-/

/-- For `0 < θ < 1/2`: `∑_{r=1}^m a_r(θ)² ≤ 9θ²/(2(1-2θ))`, from
`a_r(θ) ≤ (3/2)θ r^{θ-1}` and the super-critical `p`-series at `σ = 1 - 2θ`. -/
theorem sum_sq_binomCoeff_tail_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (m : ℕ) :
    ∑ r ∈ Icc 1 m, binomCoeff r θ ^ 2 ≤ 9 * θ ^ 2 / (2 * (1 - 2 * θ)) := by
  have hσ0 : (0 : ℝ) < 1 - 2 * θ := by linarith
  have hσ1 : (1 : ℝ) - 2 * θ ≤ 1 := by linarith
  have hterm : ∀ r ∈ Icc 1 m,
      binomCoeff r θ ^ 2 ≤ 9 / 4 * θ ^ 2 * (r : ℝ) ^ (-(1 + (1 - 2 * θ))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hb := binomCoeff_le_three_half_mul_rpow hθ0.le (by linarith) hr1
    have hnn : 0 ≤ binomCoeff r θ := binomCoeff_nonneg hθ0.le r
    have hsq : binomCoeff r θ ^ 2 ≤ (3 / 2 * θ * (r : ℝ) ^ (θ - 1)) ^ 2 :=
      pow_le_pow_left₀ hnn hb 2
    refine hsq.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, ← Real.rpow_natCast ((r : ℝ) ^ (θ - 1)) 2,
      ← Real.rpow_mul (by linarith)]
    push_cast
    rw [show (θ - 1) * 2 = -(1 + (1 - 2 * θ)) from by ring]
    ring
  have hS := sum_rpow_neg_le_of_one_lt hσ0 hσ1 m
  calc ∑ r ∈ Icc 1 m, binomCoeff r θ ^ 2
      ≤ ∑ r ∈ Icc 1 m, 9 / 4 * θ ^ 2 * (r : ℝ) ^ (-(1 + (1 - 2 * θ))) :=
        Finset.sum_le_sum hterm
    _ = 9 / 4 * θ ^ 2 * ∑ r ∈ Icc 1 m, (r : ℝ) ^ (-(1 + (1 - 2 * θ))) := by
        rw [Finset.mul_sum]
    _ ≤ 9 / 4 * θ ^ 2 * (1 + 1 / (1 - 2 * θ)) := by
        refine mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ 9 / 4 * θ ^ 2 * (2 / (1 - 2 * θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [le_div_iff₀ hσ0,
          show (1 + 1 / (1 - 2 * θ)) * (1 - 2 * θ) = (1 - 2 * θ) + 1 from by field_simp]
        linarith
    _ = 9 * θ ^ 2 / (2 * (1 - 2 * θ)) := by
        field_simp
        try ring

/-- For `-1/2 < θ ≤ 0`: `∑_{r=1}^m a_r(θ)² ≤ 2θ²`, from `|a_r(θ)| ≤ |θ| r^{θ-1}`
and `∑ r^{-2} ≤ 2` (the exponent `2 - 2θ ≥ 2` is dominated by `2`). -/
theorem sum_sq_binomCoeff_tail_neg {θ : ℝ} (hθ0 : -1 < θ) (hθ1 : θ ≤ 0) (m : ℕ) :
    ∑ r ∈ Icc 1 m, binomCoeff r θ ^ 2 ≤ 2 * θ ^ 2 := by
  have hterm : ∀ r ∈ Icc 1 m,
      binomCoeff r θ ^ 2 ≤ θ ^ 2 * (r : ℝ) ^ (-(1 + (1 : ℝ))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hb := abs_binomCoeff_le_mul_rpow hθ0 hθ1 hr1
    have hsq : binomCoeff r θ ^ 2 ≤ (|θ| * (r : ℝ) ^ (θ - 1)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    refine hsq.trans ?_
    rw [mul_pow, sq_abs, ← Real.rpow_natCast ((r : ℝ) ^ (θ - 1)) 2,
      ← Real.rpow_mul (by linarith)]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg θ)
    exact Real.rpow_le_rpow_of_exponent_le hrR (by linarith)
  have hS := sum_rpow_neg_le_of_one_lt (σ := 1) one_pos le_rfl m
  calc ∑ r ∈ Icc 1 m, binomCoeff r θ ^ 2
      ≤ ∑ r ∈ Icc 1 m, θ ^ 2 * (r : ℝ) ^ (-(1 + (1 : ℝ))) := Finset.sum_le_sum hterm
    _ = θ ^ 2 * ∑ r ∈ Icc 1 m, (r : ℝ) ^ (-(1 + (1 : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ θ ^ 2 * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg θ)
        rw [show (1 : ℝ) + 1 / 1 = 2 from by norm_num] at hS
        exact hS
    _ = 2 * θ ^ 2 := by ring

end InverseGenerator
