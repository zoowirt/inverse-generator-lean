/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.AnalyticIneq
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic and logarithmic toolkit for Lemma A.2

Lemma A.2 rests on the exact product formula `a_m(t+1) = ∏_{ℓ=1}^m (1 + t/ℓ)`
(see `CoeffBounds.lean`).  Taking logarithms turns two-sided bounds for it into
two-sided bounds for the harmonic number `H_m`, plus a convergent error series.
This file collects the elementary facts needed.

Mathlib already supplies `log (m+1) ≤ H_m ≤ 1 + log m`
(`log_add_one_le_harmonic`, `harmonic_le_one_add_log`), but states them for
`harmonic : ℕ → ℚ` indexed as `∑ i ∈ range m, (i+1)⁻¹`.  `harmonicSum` below is the
same quantity as a real sum over `ℓ ∈ Icc 1 m`, which is the shape the product
formula produces.

## Main results

* `harmonicSum_le` : `H_m ≤ 1 + log m`, from Mathlib's `harmonic_le_one_add_log`.
* `log_add_half_le_harmonicSum` : `log m + 1/2 + 1/(2m) ≤ H_m`, the sharpened lower
  bound the explicit constants need.  Mathlib's `log (m+1) ≤ H_m` is not enough: the
  `+1/2` is exactly what buys the factor `3/2` in `coeffProd_le_three_half_rpow_succ`
  instead of `e`.
-/

namespace InverseGenerator

open Finset

/-- `H_m = ∑_{ℓ=1}^m 1/ℓ`, as a real number. -/
noncomputable def harmonicSum (m : ℕ) : ℝ := ∑ ℓ ∈ Icc 1 m, (ℓ : ℝ)⁻¹

theorem harmonicSum_eq_harmonic (m : ℕ) : harmonicSum m = (harmonic m : ℝ) := by
  rw [harmonicSum, harmonic_eq_sum_Icc]
  push_cast
  rfl

/-- `H_m ≤ 1 + log m`. -/
theorem harmonicSum_le (m : ℕ) : harmonicSum m ≤ 1 + Real.log m := by
  rw [harmonicSum_eq_harmonic]
  exact harmonic_le_one_add_log m

/-- **The sharpened harmonic lower bound** `log m + 1/2 + 1/(2m) ≤ H_m`, by induction:
the induction step is exactly the trapezoid bound `log_one_add_le_trapezoid` at
`x = 1/m`, whose right side is `1/(2m) + 1/(2(m+1))`.  Mathlib's `log (m+1) ≤ H_m`
is half a unit weaker, which is not enough for the constant `3/2` of Lemma A.2. -/
theorem log_add_half_le_harmonicSum {m : ℕ} (hm : 1 ≤ m) :
    Real.log m + 1 / 2 + 1 / (2 * m) ≤ harmonicSum m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rw [harmonicSum]
      norm_num
    · have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
      have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      have hstep := ih hm0
      have htrap := log_one_add_le_trapezoid (x := 1 / (m : ℝ)) (by positivity)
      have hval : (1 / (m : ℝ)) * (1 / (m : ℝ) + 2) / (2 * (1 / (m : ℝ) + 1))
          = 1 / (2 * (m : ℝ)) + 1 / (2 * ((m : ℝ) + 1)) := by
        field_simp
        ring
      rw [hval] at htrap
      have hlog : Real.log ((m : ℝ) + 1) = Real.log m + Real.log (1 + 1 / (m : ℝ)) := by
        rw [← Real.log_mul hmR.ne' (by positivity)]
        congr 1
        field_simp
      have hsum : harmonicSum (m + 1) = harmonicSum m + ((m : ℝ) + 1)⁻¹ := by
        rw [harmonicSum, harmonicSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        push_cast
        ring
      rw [hsum]
      push_cast
      rw [hlog]
      have hinv : ((m : ℝ) + 1)⁻¹ = 1 / ((m : ℝ) + 1) := (inv_eq_one_div _)
      rw [hinv]
      have harith : 1 / (2 * ((m : ℝ) + 1)) + 1 / ((m : ℝ) + 1)
          = 1 / (2 * ((m : ℝ) + 1)) * 3 := by
        field_simp
        ring
      -- goal: log m + log(1+1/m) + 1/2 + 1/(2(m+1)) ≤ H_m + 1/(m+1)
      -- from: H_m ≥ log m + 1/2 + 1/(2m) and log(1+1/m) ≤ 1/(2m) + 1/(2(m+1))
      -- i.e. need 1/(2m) + 1/(2(m+1)) + 1/(2(m+1)) ≤ 1/(2m) + 1/(m+1) ✓ (equality)
      have hbal : 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) = 1 / ((m : ℝ) + 1) := by
        field_simp
        norm_num
      linarith

/-- `log m + 1/2 ≤ H_m` for `m ≥ 1`. -/
theorem log_add_half_le_harmonicSum' {m : ℕ} (hm : 1 ≤ m) :
    Real.log m + 1 / 2 ≤ harmonicSum m := by
  have h := log_add_half_le_harmonicSum hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  linarith

end InverseGenerator
