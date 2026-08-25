/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary analytic inequalities for the explicit constants

Theorem 1.1 carries the *explicit* absolute constant `C = 50`, which forces several
sharp elementary inequalities that a `≍_α` statement would not need:

* `log_one_add_le_trapezoid` — the trapezoid-rule bound
  `log(1+x) ≤ x(x+2)/(2(x+1))`, which drives `H_m ≥ log m + 1/2` and hence the
  `3/2` in Lemma A.2's bound `a_r(θ) ≤ (3/2) θ r^{θ-1}`;
* `log_one_sub_le` — `log(1-x) ≤ -x - x²/2`, the second-order term in the same bound;
* `exp_three_eighths_le` — `e^{3/8} ≤ 3/2`, closing Lemma A.2;
* `exp_pi_le_25`, `two_le_exp_pi` — `2 ≤ e^π ≤ 25`, giving `2e^π < 50` and
  `2e^{-π} ≤ 1` in Theorem 1.1's halves;
* `exp_one_le_four_mul_log_two` — `e ≤ 4 log 2`, which is *exactly* the inequality
  `n ≤ log log (ω_n⁻¹)` at `n = 1` (since `2 log 2 + log log 2 = log (4 log 2)`).

The two log bounds are proved by `monotoneOn_of_deriv_nonneg`: the difference has
derivative `(1 - (1+x)⁻¹)²/2` resp. `x²/(1-x)`, both visibly nonnegative.
-/

namespace InverseGenerator

open Real

/-- `e^{-x} ≤ 1/(1+x)` for `x ≥ 0`, from `1 + x ≤ e^x`. -/
theorem exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ (1 + x)⁻¹ := by
  have h := Real.add_one_le_exp x
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  rw [Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hx1 (by linarith)

/-- `e^x ≤ 1/(1-x)` for `x < 1`, from `1 - x ≤ e^{-x}`. -/
theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hx1 : (0 : ℝ) < 1 - x := by linarith
  have hpos := Real.exp_pos x
  rw [Real.exp_neg] at h
  rw [inv_eq_one_div, le_div_iff₀ hx1]
  calc Real.exp x * (1 - x) ≤ Real.exp x * (Real.exp x)⁻¹ :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

/-- **The trapezoid-rule log bound**: `log(1+x) ≤ x(x+2)/(2(x+1))` for `x ≥ 0`.
This is `∫₀ˣ dt/(1+t)` compared against the trapezoid rule on one interval; it is
what makes `H_m ≥ log m + 1/2` (rather than just `H_m ≥ log(m+1)`) provable. -/
theorem log_one_add_le_trapezoid {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (x + 2) / (2 * (x + 1)) := by
  set F : ℝ → ℝ := fun y => (y + 1 - (1 + y)⁻¹) / 2 - Real.log (1 + y) with hF
  -- derivative of `F` on `y > 0` is `(1 - (1+y)⁻¹)²/2 ≥ 0`
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt F ((1 - (1 + y)⁻¹) ^ 2 / 2) y := by
    intro y hy
    have hy1 : (0 : ℝ) < 1 + y := by linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 y := (hasDerivAt_id y).const_add 1
    have hinv : HasDerivAt (fun z : ℝ => (1 + z)⁻¹) (-1 / (1 + y) ^ 2) y :=
      h1.inv hy1.ne'
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y := by
      have := h1.log hy1.ne'
      simpa using this
    have hlin : HasDerivAt (fun z : ℝ => z + 1 - (1 + z)⁻¹) (1 - -1 / (1 + y) ^ 2) y :=
      ((hasDerivAt_id y).add_const 1).sub hinv
    have hall : HasDerivAt F ((1 - -1 / (1 + y) ^ 2) / 2 - 1 / (1 + y)) y :=
      (hlin.div_const 2).sub hlog
    convert hall using 1
    field_simp
    ring
  have hcont : ContinuousOn F (Set.Ici 0) := by
    have hne : ∀ y ∈ Set.Ici (0 : ℝ), 1 + y ≠ 0 := by
      intro y hy
      have : (0 : ℝ) ≤ y := hy
      positivity
    refine ContinuousOn.sub ?_ ?_
    · exact (((continuousOn_id.add continuousOn_const).sub
        ((continuousOn_const.add continuousOn_id).inv₀ hne)).div_const 2)
    · exact (continuousOn_const.add continuousOn_id).log hne
  have hdiff : DifferentiableOn ℝ F (interior (Set.Ici (0 : ℝ))) := by
    rw [interior_Ici]
    intro y hy
    exact ((hderiv y hy).differentiableAt).differentiableWithinAt
  have hd0 : ∀ y ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv F y := by
    rw [interior_Ici]
    intro y hy
    rw [(hderiv y hy).deriv]
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hd0
  have h0x : F 0 ≤ F x := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  have hF0 : F 0 = 0 := by
    simp [hF]
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hkey : Real.log (1 + x) ≤ (x + 1 - (1 + x)⁻¹) / 2 := by
    have := h0x
    rw [hF0] at this
    simp only [hF] at this
    linarith
  calc Real.log (1 + x) ≤ (x + 1 - (1 + x)⁻¹) / 2 := hkey
    _ = x * (x + 2) / (2 * (x + 1)) := by
        field_simp
        ring

/-- `log(1-x) ≤ -x - x²/2` for `0 ≤ x < 1`: the second-order Taylor upper bound. -/
theorem log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  set G : ℝ → ℝ := fun y => -y - y ^ 2 / 2 - Real.log (1 - y) with hG
  have hderiv : ∀ y : ℝ, 0 < y → y < 1 → HasDerivAt G (y ^ 2 / (1 - y)) y := by
    intro y hy hy1
    have h1y : (0 : ℝ) < 1 - y := by linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 - z)) (-1 / (1 - y)) y := by
      have := h1.log h1y.ne'
      simpa using this
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
      have := (hasDerivAt_pow 2 y).div_const 2
      simpa using this
    have hlin : HasDerivAt (fun z : ℝ => -z - z ^ 2 / 2) (-1 - y) y :=
      ((hasDerivAt_id y).neg).sub hsq
    have hall : HasDerivAt G (-1 - y - -1 / (1 - y)) y := hlin.sub hlog
    convert hall using 1
    field_simp
    ring
  have hcont : ContinuousOn G (Set.Icc 0 x) := by
    have hne : ∀ y ∈ Set.Icc (0 : ℝ) x, 1 - y ≠ 0 := by
      intro y hy
      have h := hy.2
      have : y < 1 := lt_of_le_of_lt h hx1
      linarith
    refine ContinuousOn.sub ?_ ?_
    · exact (continuousOn_id.neg).sub ((continuousOn_id.pow 2).div_const 2)
    · exact (continuousOn_const.sub continuousOn_id).log hne
  have hdiff : DifferentiableOn ℝ G (interior (Set.Icc (0 : ℝ) x)) := by
    rw [interior_Icc]
    intro y hy
    exact ((hderiv y hy.1 (hy.2.trans hx1)).differentiableAt).differentiableWithinAt
  have hd0 : ∀ y ∈ interior (Set.Icc (0 : ℝ) x), 0 ≤ deriv G y := by
    rw [interior_Icc]
    intro y hy
    have hy1 : y < 1 := hy.2.trans hx1
    rw [(hderiv y hy.1 hy1).deriv]
    have : (0 : ℝ) < 1 - y := by linarith
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont hdiff hd0
  have h0x : G 0 ≤ G x :=
    hmono (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0) hx0
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0] at h0x
  simp only [hG] at h0x
  linarith

/-- `e^3 ≤ 20.09`, from `e ≤ 2.7182818286`. -/
theorem exp_three_le : Real.exp 3 ≤ 20.09 := by
  have h1 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp 1 ^ (3 : ℕ) ≤ 2.7182818286 ^ (3 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
  rw [h1]
  refine h2.trans ?_
  norm_num

/-- `e^{3/8} ≤ 3/2`, since `e^3 ≤ 20.09 < 25.6 ≤ (3/2)^8`.  This is the constant
that closes Lemma A.2's bound `a_r(θ) ≤ (3/2) θ r^{θ-1}`. -/
theorem exp_three_eighths_le : Real.exp (3 / 8) ≤ 3 / 2 := by
  rcases le_or_gt (Real.exp (3 / 8)) (3 / 2) with h | h
  · exact h
  · exfalso
    have h8 : Real.exp (3 / 8) ^ (8 : ℕ) = Real.exp 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow : (3 / 2 : ℝ) ^ (8 : ℕ) ≤ Real.exp (3 / 8) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h.le 8
    rw [h8] at hpow
    have := exp_three_le
    norm_num at hpow
    linarith

/-- `e^π ≤ 25`: `e^π ≤ e^{3.15} = e^3 e^{0.15} ≤ 20.09 / 0.85 < 25`.
Hence `2 e^π < 50`, the lower constant of Theorem 1.1 at `C = 50`. -/
theorem exp_pi_le_25 : Real.exp Real.pi ≤ 25 := by
  have hpi : Real.pi ≤ 3 + 0.15 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have h1 : Real.exp Real.pi ≤ Real.exp 3 * Real.exp 0.15 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hpi
  have h2 := exp_three_le
  have h3 : Real.exp 0.15 ≤ (1 - 0.15 : ℝ)⁻¹ := exp_le_inv_one_sub (by norm_num)
  have h4 : ((1 : ℝ) - 0.15)⁻¹ = 20 / 17 := by norm_num
  have h5 : (0 : ℝ) < Real.exp 0.15 := Real.exp_pos _
  calc Real.exp Real.pi ≤ Real.exp 3 * Real.exp 0.15 := h1
    _ ≤ 20.09 * (20 / 17) := by
        rw [h4] at h3
        exact mul_le_mul h2 h3 h5.le (by norm_num)
    _ ≤ 25 := by norm_num

/-- `2 ≤ e^π`, so `2 e^{-π} ≤ 1`: the upper constant of Theorem 1.1 is `1`. -/
theorem two_le_exp_pi : 2 ≤ Real.exp Real.pi := by
  have h1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h2 : Real.exp 1 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr h1
  have h3 := Real.add_one_le_exp (1 : ℝ)
  linarith

/-- `e ≤ 4 log 2`.  Rewritten, this is `1 ≤ log(4 log 2) = 2 log 2 + log log 2`,
which is precisely `n ≤ log log (ω_n⁻¹)` at its tightest point `n = 1`. -/
theorem exp_one_le_four_mul_log_two : Real.exp 1 ≤ 4 * Real.log 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.log_two_gt_d9
  norm_num at h1 h2 ⊢
  linarith

end InverseGenerator
