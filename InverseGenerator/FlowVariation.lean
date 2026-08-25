/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.AnalyticIneq
import InverseGenerator.Blocks
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Flow variation of the tower spectrum (Lemma A.3)

The paper's Lemma A.3 (`eq:shifted-exponential-variation`), specialized to the tower sequence
`y₀ = 2`, `y_{k+1} = y_k² + 1`: the total variation of the *shifted* semigroup flow
along the spectrum `λ_k = (-1 + i y_k)⁻¹`,

  `∑_{k<M} ‖e^{t(λ_{k+1} + ω)} - e^{t(λ_k + ω)}‖ ≤ 10`,     `ω = 1/y_{2n+1}`,

uniformly in `t ≥ 0` and in the length `M`.  The shift by `ω` is what upgrades a
uniform flow bound to the *exponential decay* `‖e^{tA_n}‖ ≲ e^{-ω t}` of Theorem 1.1;
the variation bound has to survive it, and `10` is the price.

## Main results

* `sum_inv_tower_tail_le` — Lemma 2.2: the tail `∑_{N ≤ k < M} 1/y_k ≤ 2/y_N`.
* `towerSpec_re`, `norm_towerSpec_le` — location and size of the spectrum.
* `sum_norm_towerSpec_sub_le_one` — total variation of the spectrum is at most `1`.
* `norm_cexp_sub_cexp_le` — mean-value bound `‖e^w - e^z‖ ≤ ‖w - z‖` on the closed
  left half-plane.
* `flow_variation_le_eight` — the unshifted variation, at most `8`.
* `shifted_flow_variation_le_ten` — **Lemma A.3** for the tower.

## Proof sketch

For `t ≤ 4` the mean-value bound alone gives `∑ ≤ t ∑ 1/y_k ≤ t ≤ 4`.  For `t > 4`
pick the largest index `m` with `y_m² ≤ t` and split the sum: the early range
(`k + 2 ≤ m`) is controlled by the modulus `e^{-t/y_{k+2}} ≤ e^{-y_{k+2}} ≤ 2^{-(k+3)}`,
the middle (at most three terms) by the trivial bound `2`, and the tail (`k ≥ m + 2`)
again by the mean-value bound plus the geometric tail estimate.  Shifting the spectrum
by `ω ≤ 1/y_{2n+1}` costs a further factor bounded through
`sum_exp_two_pow_le_five`, and the total is at most `10`.
-/

namespace InverseGenerator

/-- Each tower step increases the sequence. -/
theorem tower_le_succ (k : ℕ) : tower k ≤ tower (k + 1) := by
  have h2 := two_mul_tower_le_tower_succ k
  omega

/-- `tower` is monotone. -/
theorem tower_le_tower {j k : ℕ} (h : j ≤ k) : tower j ≤ tower k := by
  induction k with
  | zero =>
    have hj : j = 0 := Nat.le_zero.mp h
    subst hj
    exact le_rfl
  | succ k ih =>
    by_cases hj : j ≤ k
    · exact le_trans (ih hj) (tower_le_succ k)
    · have hj' : j = k + 1 := by omega
      subst hj'
      exact le_rfl

/-- The tower dominates a geometric sequence started at `y_N`: `2^j y_N ≤ y_{N+j}`. -/
theorem two_pow_mul_tower_le (N j : ℕ) : 2 ^ j * tower N ≤ tower (N + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 := two_mul_tower_le_tower_succ (N + j)
    calc 2 ^ (j + 1) * tower N = 2 * (2 ^ j * tower N) := by ring
      _ ≤ 2 * tower (N + j) := by omega
      _ ≤ tower (N + j + 1) := h2

/-- Lemma 2.2: the tail of `∑ 1/y_k` is at most `2/y_N`. -/
theorem sum_inv_tower_tail_le (N M : ℕ) : ∑ k ∈ Finset.Ico N M, (1:ℝ)/tower k ≤ 2/tower N := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ j ∈ Finset.range (M - N),
      (1:ℝ)/(tower (N + j) : ℝ) ≤ (1/2 : ℝ)^j * ((1:ℝ)/(tower N : ℝ)) := by
    intro j _
    have hN : (0:ℝ) < (tower N : ℝ) := by exact_mod_cast tower_pos N
    have h1 : (0:ℝ) < (2:ℝ)^j * (tower N : ℝ) := mul_pos (by positivity) hN
    have h2 : (2:ℝ)^j * (tower N : ℝ) ≤ ((tower (N + j)) : ℝ) := by
      exact_mod_cast two_pow_mul_tower_le N j
    calc (1:ℝ)/(tower (N + j) : ℝ)
        ≤ 1/((2:ℝ)^j * (tower N : ℝ)) := one_div_le_one_div_of_le h1 h2
      _ = (1/2 : ℝ)^j * ((1:ℝ)/(tower N : ℝ)) := by
          rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  have hgeo : ∑ j ∈ Finset.range (M - N), (1/2 : ℝ)^j ≤ 2 := by
    have h := sum_half_pow_succ (M - N)
    have heq : ∑ j ∈ Finset.range (M - N), (1/2 : ℝ)^j
        = 2 * ∑ j ∈ Finset.range (M - N), (1/2 : ℝ)^(j+1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ]
      ring
    rw [heq, h]
    have h0 : (0:ℝ) ≤ (1/2 : ℝ)^(M - N) := by positivity
    linarith
  calc ∑ j ∈ Finset.range (M - N), (1:ℝ)/(tower (N + j) : ℝ)
      ≤ ∑ j ∈ Finset.range (M - N), (1/2 : ℝ)^j * ((1:ℝ)/(tower N : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (M - N), (1/2 : ℝ)^j) * ((1:ℝ)/(tower N : ℝ)) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * ((1:ℝ)/(tower N : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hgeo ?_
        positivity
    _ = 2/(tower N : ℝ) := by rw [mul_one_div]

/-- The spectrum lies on the boundary curve: `Re λ_k = -1/y_{k+1}`. -/
theorem towerSpec_re (k : ℕ) : (towerSpec k).re = -(1/(tower (k+1) : ℝ)) := by
  have him : (towerPoint k).im = (tower k : ℝ) := by simp [towerPoint]
  have hsq : Complex.normSq (towerPoint k) = (tower (k+1) : ℝ) := by
    rw [Complex.normSq_apply, towerPoint_re, him, tower_succ]
    push_cast
    ring
  rw [towerSpec, Complex.inv_re, towerPoint_re, hsq]
  ring

/-- `‖λ_k‖ ≤ 1/y_k`, since `|Im b_k| = y_k ≤ ‖b_k‖`. -/
theorem norm_towerSpec_le (k : ℕ) : ‖towerSpec k‖ ≤ 1/(tower k : ℝ) := by
  have hy : (0:ℝ) < (tower k : ℝ) := by exact_mod_cast tower_pos k
  have him : (towerPoint k).im = (tower k : ℝ) := by simp [towerPoint]
  have hge : (tower k : ℝ) ≤ ‖towerPoint k‖ := by
    have h := Complex.abs_im_le_norm (towerPoint k)
    rw [him, abs_of_nonneg hy.le] at h
    exact h
  rw [towerSpec, norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hy hge

/-- `Re (t λ_k) = -t/y_{k+1}`. -/
theorem re_ofReal_mul_towerSpec (t : ℝ) (k : ℕ) :
    ((t:ℂ) * towerSpec k).re = -(t/(tower (k+1) : ℝ)) := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, towerSpec_re]
  ring

/-- The modulus of the flow at `λ_k`: `‖e^{t λ_k}‖ = e^{-t/y_{k+1}}`. -/
theorem norm_cexp_mul_towerSpec (t : ℝ) (k : ℕ) :
    ‖Complex.exp ((t:ℂ) * towerSpec k)‖ = Real.exp (-(t/(tower (k+1) : ℝ))) := by
  rw [Complex.norm_exp, re_ofReal_mul_towerSpec]

/-- For `t ≥ 0` the flow at each spectral point is a contraction. -/
theorem norm_cexp_mul_towerSpec_le_one {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ‖Complex.exp ((t:ℂ) * towerSpec k)‖ ≤ 1 := by
  rw [norm_cexp_mul_towerSpec, Real.exp_le_one_iff]
  have hy : (0:ℝ) < (tower (k+1) : ℝ) := by exact_mod_cast tower_pos (k+1)
  have h0 : 0 ≤ t/(tower (k+1) : ℝ) := div_nonneg ht hy.le
  linarith

/-- `e^{-y} ≤ 1/y` for `y > 0`, from `y + 1 ≤ e^y`. -/
theorem exp_neg_le_one_div {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1/y := by
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_le_one_div_of_le hy ?_
  have h := Real.add_one_le_exp y
  linarith

/-- Mean-value bound: for `z, w` in the closed left half-plane, `‖e^w - e^z‖ ≤ ‖w - z‖`. -/
theorem norm_cexp_sub_cexp_le {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp w - Complex.exp z‖ ≤ ‖w - z‖ := by
  -- the flow along the segment from `z` to `w`
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => Complex.exp (z + s • (w - z)))
        (Complex.exp (z + s • (w - z)) * (w - z)) s := by
    intro s
    have h2 := (hasDerivAt_id s).smul_const (w - z)
    simp only [id_eq, one_smul] at h2
    have h1 : HasDerivAt (fun s : ℝ => z + s • (w - z)) (w - z) s := h2.const_add z
    exact h1.cexp
  -- on the segment the derivative has norm at most `‖w - z‖`
  have hbound : ∀ s ∈ Set.Ico (0:ℝ) 1,
      ‖Complex.exp (z + s • (w - z)) * (w - z)‖ ≤ ‖w - z‖ := by
    intro s hs
    rw [norm_mul, Complex.norm_exp]
    have hre : (z + s • (w - z)).re = (1 - s) * z.re + s * w.re := by
      simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
      ring
    have hre0 : (z + s • (w - z)).re ≤ 0 := by
      rw [hre]
      nlinarith [hs.1, hs.2, hz, hw]
    have hexp1 : Real.exp ((z + s • (w - z)).re) ≤ 1 := Real.exp_le_one_iff.mpr hre0
    calc Real.exp ((z + s • (w - z)).re) * ‖w - z‖
        ≤ 1 * ‖w - z‖ := mul_le_mul_of_nonneg_right hexp1 (norm_nonneg _)
      _ = ‖w - z‖ := one_mul _
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound
  have hkey : ‖Complex.exp (z + (1:ℝ) • (w - z)) - Complex.exp (z + (0:ℝ) • (w - z))‖
      ≤ ‖w - z‖ := hmvt
  have h1 : z + (1:ℝ) • (w - z) = w := by rw [one_smul]; ring
  have h0 : z + (0:ℝ) • (w - z) = z := by rw [zero_smul, add_zero]
  rwa [h1, h0] at hkey

/-- Modulus bound for one flow increment: the `k`-th term is at most `2 e^{-t/y_{k+2}}`. -/
theorem flow_term_le_modulus {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ‖Complex.exp ((t:ℂ) * towerSpec (k+1)) - Complex.exp ((t:ℂ) * towerSpec k)‖
      ≤ 2 * Real.exp (-(t/(tower (k+2) : ℝ))) := by
  have hy1 : (0:ℝ) < (tower (k+1) : ℝ) := by exact_mod_cast tower_pos (k+1)
  have hmono : t/(tower (k+2) : ℝ) ≤ t/(tower (k+1) : ℝ) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div t]
    refine mul_le_mul_of_nonneg_left ?_ ht
    exact one_div_le_one_div_of_le hy1 (by exact_mod_cast tower_le_tower (Nat.le_succ (k+1)))
  have h1 : ‖Complex.exp ((t:ℂ) * towerSpec (k+1))‖ = Real.exp (-(t/(tower (k+2) : ℝ))) :=
    norm_cexp_mul_towerSpec t (k+1)
  have h2 : ‖Complex.exp ((t:ℂ) * towerSpec k)‖ = Real.exp (-(t/(tower (k+1) : ℝ))) :=
    norm_cexp_mul_towerSpec t k
  have h3 : Real.exp (-(t/(tower (k+1) : ℝ))) ≤ Real.exp (-(t/(tower (k+2) : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  calc ‖Complex.exp ((t:ℂ) * towerSpec (k+1)) - Complex.exp ((t:ℂ) * towerSpec k)‖
      ≤ ‖Complex.exp ((t:ℂ) * towerSpec (k+1))‖ + ‖Complex.exp ((t:ℂ) * towerSpec k)‖ :=
        norm_sub_le _ _
    _ ≤ 2 * Real.exp (-(t/(tower (k+2) : ℝ))) := by rw [h1, h2]; linarith

/-- For `t > 4` there is a largest tower index `m` with `y_m² ≤ t`; beyond it,
`t < y_k²`. -/
theorem exists_threshold {t : ℝ} (ht4 : 4 < t) :
    ∃ m : ℕ, ((tower m : ℝ))^2 ≤ t ∧ ∀ k, m < k → t < ((tower k : ℝ))^2 := by
  classical
  have h0 : ((tower 0 : ℝ))^2 ≤ t := by
    have h4 : ((tower 0 : ℝ))^2 = 4 := by
      rw [tower_zero]
      norm_num
    linarith
  refine ⟨Nat.findGreatest (fun k => ((tower k : ℝ))^2 ≤ t) ⌈t⌉₊, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun k => ((tower k : ℝ))^2 ≤ t) (Nat.zero_le _) h0
  · intro k hk
    rcases le_or_gt k ⌈t⌉₊ with hkb | hbk
    · exact not_le.mp (Nat.findGreatest_is_greatest hk hkb)
    · have h1 : k + 1 < tower k := lt_of_lt_of_le Nat.lt_two_pow_self (two_pow_le_tower k)
      have h2 : ⌈t⌉₊ < tower k := by omega
      have h3 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
      have h4 : ((⌈t⌉₊ : ℕ) : ℝ) < (tower k : ℝ) := by exact_mod_cast h2
      have h5 : t < (tower k : ℝ) := lt_of_le_of_lt h3 h4
      have h6 : (2:ℝ) ≤ (tower k : ℝ) := by exact_mod_cast two_le_tower k
      nlinarith [sq_nonneg ((tower k : ℝ) - 2)]

/-! ## The sharpenings the explicit constants need

Beyond the unshifted variation bound above, Theorem 1.1 needs three sharper facts:

* the **exact modulus** `‖b_k‖² = y_{k+1}` and the lower bound `y_k ≤ ‖b_k‖`
  (for `‖A_n⁻¹‖ ≤ ω_n^{-1/2}(1 + Cα/(1-α))` and the spectral inclusions);
* the **sharp spectral variation** `‖λ_{k+2} - λ_{k+1}‖ ≤ 1/y_{k+1}`
  (`eq:lambdadiff`), total `≤ 1`, which drives `‖A_n‖ ≤ 1 + 5α/(1-α)`;
* the **shifted flow variation** `≤ 10` (`eq:shifted-exponential-variation`), which
  gives the exponential *decay* `‖e^{tA_n}‖ ≤ (1 + 50α/(1-α)) e^{-ω_n t}` and is the
  source of `C = 50 = 5 · 10`.  Its unshifted core is `flow_variation_le_eight`.
-/

/-- `‖b_k‖² = y_{k+1}`: the squared modulus of the inverse spectrum. -/
theorem normSq_towerPoint (k : ℕ) : Complex.normSq (towerPoint k) = (tower (k + 1) : ℝ) := by
  have him : (towerPoint k).im = (tower k : ℝ) := by simp [towerPoint]
  rw [Complex.normSq_apply, towerPoint_re, him, tower_succ]
  push_cast
  ring

theorem norm_towerPoint_sq (k : ℕ) : ‖towerPoint k‖ ^ 2 = (tower (k + 1) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, normSq_towerPoint]

/-- `y_k ≤ ‖b_k‖`, since `‖b_k‖² = y_{k+1} ≥ y_k²`. -/
theorem le_norm_towerPoint (k : ℕ) : (tower k : ℝ) ≤ ‖towerPoint k‖ := by
  have h1 := norm_towerPoint_sq k
  have h2 : ((tower k : ℝ)) ^ 2 ≤ ‖towerPoint k‖ ^ 2 := by
    rw [h1]
    exact_mod_cast tower_sq_le_tower_succ k
  have h3 : (0 : ℝ) ≤ (tower k : ℝ) := Nat.cast_nonneg _
  nlinarith [norm_nonneg (towerPoint k)]

/-- `‖b_k‖ ≤ √y_M` whenever `k + 1 ≤ M`. -/
theorem norm_towerPoint_le_sqrt {k M : ℕ} (h : k + 1 ≤ M) :
    ‖towerPoint k‖ ≤ Real.sqrt (tower M) := by
  have h1 : ‖towerPoint k‖ = Real.sqrt (tower (k + 1)) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_towerPoint_sq]
  rw [h1]
  exact Real.sqrt_le_sqrt (by exact_mod_cast tower_le_tower h)

/-- `‖b_{k+1} - b_k‖ = y_{k+2} - y_{k+1}` exactly: the inverse spectrum is a vertical
line and its variation telescopes. -/
theorem norm_towerPoint_sub (k : ℕ) :
    ‖towerPoint (k + 1) - towerPoint k‖ = (tower (k + 1) : ℝ) - (tower k : ℝ) := by
  have hle : (tower k : ℝ) ≤ (tower (k + 1) : ℝ) := by exact_mod_cast tower_le_succ k
  have hdiff : towerPoint (k + 1) - towerPoint k
      = Complex.I * ((((tower (k + 1) : ℝ) - (tower k : ℝ)) : ℝ) : ℂ) := by
    rw [towerPoint, towerPoint]
    push_cast
    ring
  rw [hdiff, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- Total variation of the inverse spectrum: `∑_{k<N} ‖b_{k+1} - b_k‖ ≤ y_{N+1}`
(it telescopes to `y_{N+1} - 2`). -/
theorem sum_norm_towerPoint_sub_le (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖towerPoint (k + 1) - towerPoint k‖ ≤ (tower N : ℝ) := by
  induction N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    exact_mod_cast Nat.zero_le (tower 0)
  | succ N ih =>
    rw [Finset.sum_range_succ, norm_towerPoint_sub]
    have h := ih
    linarith

/-- **`eq:lambdadiff`, sharp form**: `‖towerSpec (k+1) - towerSpec k‖ ≤ 1/y_{k+1}`,
i.e. `≤ 1/tower k` in the 0-based indexing.  This is what makes the total spectral
variation `≤ 1` (`eq:lacunary-variation`) rather than merely finite. -/
theorem norm_towerSpec_sub_le_inv (k : ℕ) :
    ‖towerSpec (k + 1) - towerSpec k‖ ≤ 1 / (tower k : ℝ) := by
  have ha0 : (0 : ℝ) < ‖towerPoint k‖ :=
    norm_pos_iff.mpr (towerPoint_ne_zero k)
  have hb0 : (0 : ℝ) < ‖towerPoint (k + 1)‖ :=
    norm_pos_iff.mpr (towerPoint_ne_zero (k + 1))
  have hdiff : towerSpec (k + 1) - towerSpec k
      = (towerPoint k - towerPoint (k + 1)) / (towerPoint (k + 1) * towerPoint k) := by
    rw [towerSpec, towerSpec]
    exact inv_sub_inv (towerPoint_ne_zero _) (towerPoint_ne_zero _)
  have hNb : (tower (k + 1) : ℝ) - (tower k : ℝ) ≤ ‖towerPoint (k + 1)‖ := by
    have h1 := le_norm_towerPoint (k + 1)
    have h2 : (0 : ℝ) ≤ (tower k : ℝ) := Nat.cast_nonneg _
    linarith
  have hTa : (tower k : ℝ) ≤ ‖towerPoint k‖ := le_norm_towerPoint k
  have hTpos : (0 : ℝ) < (tower k : ℝ) := by exact_mod_cast tower_pos k
  rw [hdiff, norm_div, norm_mul, norm_sub_rev, norm_towerPoint_sub]
  have hstep : ((tower (k + 1) : ℝ) - (tower k : ℝ))
        / (‖towerPoint (k + 1)‖ * ‖towerPoint k‖) ≤ 1 / ‖towerPoint k‖ := by
    rw [div_le_div_iff₀ (by positivity) ha0]
    calc ((tower (k + 1) : ℝ) - (tower k : ℝ)) * ‖towerPoint k‖
        ≤ ‖towerPoint (k + 1)‖ * ‖towerPoint k‖ :=
          mul_le_mul_of_nonneg_right hNb ha0.le
      _ = 1 * (‖towerPoint (k + 1)‖ * ‖towerPoint k‖) := by ring
  exact hstep.trans (one_div_le_one_div_of_le hTpos hTa)

/-- Total spectral variation `∑ ‖λ_{k+1} - λ_k‖ ≤ 1` (`eq:lacunary-variation`). -/
theorem sum_norm_towerSpec_sub_le_one (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖towerSpec (k + 1) - towerSpec k‖ ≤ 1 := by
  calc ∑ k ∈ Finset.range N, ‖towerSpec (k + 1) - towerSpec k‖
      ≤ ∑ k ∈ Finset.range N, (1 : ℝ) / (tower k : ℝ) :=
        Finset.sum_le_sum fun k _ => norm_towerSpec_sub_le_inv k
    _ ≤ 1 := sum_inv_tower_le_one N

/-- Sharp mean-value bound for one flow increment: at most `t/y_{k+1}`. -/
theorem flow_term_le_mvt' {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ‖Complex.exp ((t : ℂ) * towerSpec (k + 1)) - Complex.exp ((t : ℂ) * towerSpec k)‖
      ≤ t * (1 / (tower k : ℝ)) := by
  have hnonpos : ∀ j : ℕ, ((t : ℂ) * towerSpec j).re ≤ 0 := by
    intro j
    rw [re_ofReal_mul_towerSpec]
    have hy : (0 : ℝ) < (tower (j + 1) : ℝ) := by exact_mod_cast tower_pos (j + 1)
    have h0 : 0 ≤ t / (tower (j + 1) : ℝ) := div_nonneg ht hy.le
    linarith
  have h := norm_cexp_sub_cexp_le (hnonpos k) (hnonpos (k + 1))
  have heq : ‖(t : ℂ) * towerSpec (k + 1) - (t : ℂ) * towerSpec k‖
      = t * ‖towerSpec (k + 1) - towerSpec k‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [heq] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left (norm_towerSpec_sub_le_inv k) ht

/-- **The unshifted flow variation is at most `8`** (`eq:auxestlambda`): the sharp
version of `flow_variation_le`, needed for the shifted estimate below. -/
theorem flow_variation_le_eight {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      ‖Complex.exp ((t : ℂ) * towerSpec (k + 1)) - Complex.exp ((t : ℂ) * towerSpec k)‖
      ≤ 8 := by
  rcases le_or_gt t 4 with ht4 | ht4
  -- Small times: the sharp mean-value bound alone gives `≤ t ≤ 4`.
  · calc ∑ k ∈ Finset.range N,
        ‖Complex.exp ((t : ℂ) * towerSpec (k + 1)) - Complex.exp ((t : ℂ) * towerSpec k)‖
        ≤ ∑ k ∈ Finset.range N, t * ((1 : ℝ) / (tower k : ℝ)) :=
          Finset.sum_le_sum fun k _ => flow_term_le_mvt' ht k
      _ = t * ∑ k ∈ Finset.range N, (1 : ℝ) / (tower k : ℝ) := by rw [Finset.mul_sum]
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left (sum_inv_tower_le_one N) ht
      _ ≤ 8 := by linarith
  -- Large times: split at the threshold `m` with `y_m² ≤ t < y_{m+1}²`.
  · obtain ⟨m, hPm, hgt⟩ := exists_threshold ht4
    set F : ℕ → ℝ := fun k =>
      ‖Complex.exp ((t : ℂ) * towerSpec (k + 1)) - Complex.exp ((t : ℂ) * towerSpec k)‖
      with hF
    have hF0 : ∀ k, 0 ≤ F k := fun k => norm_nonneg _
    -- Early range: the modulus is geometrically small, total `≤ 1/2`.
    have hearly : ∀ k : ℕ, k + 2 ≤ m → F k ≤ (1 / 2 : ℝ) ^ (k + 2) := by
      intro k hkm
      have hyk : (0 : ℝ) < (tower (k + 2) : ℝ) := by exact_mod_cast tower_pos (k + 2)
      have hle' : (tower (k + 2) : ℝ) ≤ (tower m : ℝ) := by
        exact_mod_cast tower_le_tower hkm
      have hsq : ((tower (k + 2) : ℝ)) ^ 2 ≤ t := by
        have h := pow_le_pow_left₀ hyk.le hle' 2
        linarith
      have hdiv : (tower (k + 2) : ℝ) ≤ t / (tower (k + 2) : ℝ) := by
        rw [le_div_iff₀ hyk, ← pow_two]
        exact hsq
      have hexp1 : Real.exp (-(t / (tower (k + 2) : ℝ))) ≤ 1 / (tower (k + 2) : ℝ) :=
        le_trans (Real.exp_le_exp.mpr (by linarith)) (exp_neg_le_one_div hyk)
      have hpow : (1 : ℝ) / (tower (k + 2) : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 3) := by
        rw [div_pow, one_pow]
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact_mod_cast two_pow_le_tower (k + 2)
      have hpow2 : (2 : ℝ) * (1 / 2 : ℝ) ^ (k + 3) = (1 / 2 : ℝ) ^ (k + 2) := by
        have h3 : (1 / 2 : ℝ) ^ (k + 3) = (1 / 2 : ℝ) ^ (k + 2) * (1 / 2) :=
          pow_succ (1 / 2 : ℝ) (k + 2)
        rw [h3]
        ring
      calc F k ≤ 2 * Real.exp (-(t / (tower (k + 2) : ℝ))) := flow_term_le_modulus ht k
        _ ≤ 2 * ((1 / 2 : ℝ) ^ (k + 3)) := by linarith
        _ = (1 / 2 : ℝ) ^ (k + 2) := hpow2
    have hearly_sum :
        ∑ k ∈ (Finset.range N).filter (fun k => k + 2 ≤ m), F k ≤ 1 / 2 := by
      calc ∑ k ∈ (Finset.range N).filter (fun k => k + 2 ≤ m), F k
          ≤ ∑ k ∈ (Finset.range N).filter (fun k => k + 2 ≤ m), (1 / 2 : ℝ) ^ (k + 2) :=
            Finset.sum_le_sum fun k hk => hearly k (Finset.mem_filter.mp hk).2
        _ ≤ ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun k _ _ => by positivity
        _ = (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have h3 : (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) * (1 / 2) :=
              pow_succ (1 / 2 : ℝ) (k + 1)
            rw [h3]
            ring
        _ = (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ) ^ N) := by rw [sum_half_pow_succ]
        _ ≤ 1 / 2 := by
            have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
            nlinarith
    -- Every term is at most 2; the term at `k = m - 1` is at most `3/2`.
    have hD2 : ∀ k : ℕ, F k ≤ 2 := by
      intro k
      have h1 := norm_cexp_mul_towerSpec_le_one ht (k + 1)
      have h2 := norm_cexp_mul_towerSpec_le_one ht k
      have h3 := norm_sub_le (Complex.exp ((t : ℂ) * towerSpec (k + 1)))
        (Complex.exp ((t : ℂ) * towerSpec k))
      rw [hF]
      dsimp only
      linarith
    -- Middle: at most `11/2`.
    have hmid_gen : ∀ s : Finset ℕ, s ⊆ Finset.Icc (m - 1) (m + 1) →
        ∑ k ∈ s, F k ≤ 11 / 2 := by
      intro s hs
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · -- `m = 0`: at most two indices, each term at most 2.
        subst hm0
        have hcard : s.card ≤ 2 := by
          refine le_trans (Finset.card_le_card hs) ?_
          simp [Nat.card_Icc]
        calc ∑ k ∈ s, F k ≤ s.card • (2 : ℝ) :=
              Finset.sum_le_card_nsmul _ _ _ fun k _ => hD2 k
          _ = (s.card : ℝ) * 2 := by rw [nsmul_eq_mul]
          _ ≤ 11 / 2 := by
              have h2 : (s.card : ℝ) ≤ 2 := by exact_mod_cast hcard
              linarith
      · -- `m ≥ 1`: the term at `m - 1` is at most `3/2`, the two others at most 2.
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hs' : s ⊆ Finset.Icc m' (m' + 2) := by
          intro k hk
          have h := hs hk
          rw [Finset.mem_Icc] at h ⊢
          omega
        -- the refined bound at `k = m' = m - 1`
        have hm'_term : F m' ≤ 3 / 2 := by
          have hmod : ‖Complex.exp ((t : ℂ) * towerSpec m')‖
              ≤ Real.exp (-(t / (tower (m' + 1) : ℝ))) := by
            rw [norm_cexp_mul_towerSpec]
          have hy : (0 : ℝ) < (tower (m' + 1) : ℝ) := by
            exact_mod_cast tower_pos (m' + 1)
          have hty : (tower (m' + 1) : ℝ) ≤ t / (tower (m' + 1) : ℝ) := by
            rw [le_div_iff₀ hy, ← pow_two]
            exact hPm
          have h2y : (2 : ℝ) ≤ (tower (m' + 1) : ℝ) := by
            exact_mod_cast two_le_tower (m' + 1)
          have hsmall : Real.exp (-(t / (tower (m' + 1) : ℝ))) ≤ 1 / 3 := by
            calc Real.exp (-(t / (tower (m' + 1) : ℝ)))
                ≤ Real.exp (-(2 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
              _ ≤ (1 + 2 : ℝ)⁻¹ := exp_neg_le_inv_one_add (by norm_num)
              _ = 1 / 3 := by norm_num
          have h1 := norm_cexp_mul_towerSpec_le_one ht (m' + 1)
          have h3 := norm_sub_le (Complex.exp ((t : ℂ) * towerSpec (m' + 1)))
            (Complex.exp ((t : ℂ) * towerSpec m'))
          rw [hF]
          dsimp only
          have h4 : ‖Complex.exp ((t : ℂ) * towerSpec m')‖ ≤ 1 / 3 :=
            hmod.trans hsmall
          linarith
        calc ∑ k ∈ s, F k
            ≤ ∑ k ∈ Finset.Icc m' (m' + 2), F k :=
              Finset.sum_le_sum_of_subset_of_nonneg hs' fun k _ _ => hF0 k
          _ = F m' + F (m' + 1) + F (m' + 2) := by
              rw [show Finset.Icc m' (m' + 2) = {m', m' + 1, m' + 2} from by
                ext x
                simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
                omega]
              rw [Finset.sum_insert (by
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  omega),
                Finset.sum_insert (by
                  simp only [Finset.mem_singleton]
                  omega),
                Finset.sum_singleton]
              ring
          _ ≤ 3 / 2 + 2 + 2 := by
              have := hD2 (m' + 1)
              have := hD2 (m' + 2)
              linarith [hm'_term]
          _ ≤ 11 / 2 := by norm_num
    -- Tail: at most `2`, from the sharp mean-value bound and `t ≤ y_{m+2}`.
    have htail_gen : ∀ s : Finset ℕ, s ⊆ Finset.Ico (m + 2) N →
        ∑ k ∈ s, F k ≤ 2 := by
      intro s hs
      have hty : (0 : ℝ) < (tower (m + 2) : ℝ) := by exact_mod_cast tower_pos (m + 2)
      have hle_t : t ≤ (tower (m + 2) : ℝ) := by
        have h1 := hgt (m + 1) (Nat.lt_succ_self m)
        have h2 : ((tower (m + 1) : ℝ)) ^ 2 ≤ (tower (m + 2) : ℝ) := by
          exact_mod_cast tower_sq_le_tower_succ (m + 1)
        linarith
      calc ∑ k ∈ s, F k
          ≤ ∑ k ∈ s, t * ((1 : ℝ) / (tower k : ℝ)) :=
            Finset.sum_le_sum fun k _ => flow_term_le_mvt' ht k
        _ ≤ ∑ k ∈ Finset.Ico (m + 2) N, t * ((1 : ℝ) / (tower k : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hs fun k _ _ => ?_
            have hk : (0 : ℝ) < (tower k : ℝ) := by exact_mod_cast tower_pos k
            positivity
        _ = t * ∑ k ∈ Finset.Ico (m + 2) N, (1 : ℝ) / (tower k : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ t * (2 / (tower (m + 2) : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (sum_inv_tower_tail_le (m + 2) N) ?_
            linarith
        _ ≤ 2 := by
            have hq : t / (tower (m + 2) : ℝ) ≤ 1 := (div_le_one hty).mpr hle_t
            have heq : t * (2 / (tower (m + 2) : ℝ)) = 2 * (t / (tower (m + 2) : ℝ)) := by
              ring
            rw [heq]
            linarith
    have htail_sum :
        ∑ k ∈ ((Finset.range N).filter (fun k => ¬(k + 2 ≤ m))).filter (fun k => m + 2 ≤ k),
          F k ≤ 2 := by
      refine htail_gen _ fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_range, not_le] at hk
      simp only [Finset.mem_Ico]
      omega
    have hmid_sum :
        ∑ k ∈ ((Finset.range N).filter (fun k => ¬(k + 2 ≤ m))).filter (fun k => ¬(m + 2 ≤ k)),
          F k ≤ 11 / 2 := by
      refine hmid_gen _ fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_range, not_le] at hk
      simp only [Finset.mem_Icc]
      omega
    calc ∑ k ∈ Finset.range N, F k
        = (∑ k ∈ (Finset.range N).filter (fun k => k + 2 ≤ m), F k)
          + ∑ k ∈ (Finset.range N).filter (fun k => ¬(k + 2 ≤ m)), F k :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ = (∑ k ∈ (Finset.range N).filter (fun k => k + 2 ≤ m), F k)
          + ((∑ k ∈ ((Finset.range N).filter (fun k => ¬(k + 2 ≤ m))).filter
                (fun k => m + 2 ≤ k), F k)
            + ∑ k ∈ ((Finset.range N).filter (fun k => ¬(k + 2 ≤ m))).filter
                (fun k => ¬(m + 2 ≤ k)), F k) :=
          congrArg (_ + ·) (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ 1 / 2 + (2 + 11 / 2) := add_le_add hearly_sum (add_le_add htail_sum hmid_sum)
      _ = 8 := by norm_num

/-- `∑_{j<J} e^{-(2^j - 1)/9} ≤ 5`: four explicit terms plus a `(3/8)`-geometric
tail.  This is the numeric core of `eq:shifted-exponential-variation`. -/
theorem sum_exp_two_pow_le_five (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(((2 : ℝ) ^ j - 1) / 9)) ≤ 5 := by
  set f : ℕ → ℝ := fun j => Real.exp (-(((2 : ℝ) ^ j - 1) / 9)) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => (Real.exp_pos _).le
  have hfour : ∑ j ∈ Finset.range 4, f j ≤ 1 + 9 / 10 + 3 / 4 + 9 / 16 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    have h0 : f 0 = 1 := by
      rw [hf]
      norm_num
    have h1 : f 1 ≤ 9 / 10 := by
      rw [hf]
      have h := exp_neg_le_inv_one_add (x := 1 / 9) (by norm_num)
      calc Real.exp (-(((2 : ℝ) ^ 1 - 1) / 9)) = Real.exp (-(1 / 9)) := by norm_num
        _ ≤ (1 + 1 / 9)⁻¹ := h
        _ = 9 / 10 := by norm_num
    have h2 : f 2 ≤ 3 / 4 := by
      rw [hf]
      have h := exp_neg_le_inv_one_add (x := 1 / 3) (by norm_num)
      calc Real.exp (-(((2 : ℝ) ^ 2 - 1) / 9)) = Real.exp (-(1 / 3)) := by norm_num
        _ ≤ (1 + 1 / 3)⁻¹ := h
        _ = 3 / 4 := by norm_num
    have h3 : f 3 ≤ 9 / 16 := by
      rw [hf]
      have h := exp_neg_le_inv_one_add (x := 7 / 9) (by norm_num)
      calc Real.exp (-(((2 : ℝ) ^ 3 - 1) / 9)) = Real.exp (-(7 / 9)) := by norm_num
        _ ≤ (1 + 7 / 9)⁻¹ := h
        _ = 9 / 16 := by norm_num
    linarith
  have htail_term : ∀ j, 4 ≤ j → f j ≤ (3 / 8 : ℝ) ^ (j - 3) := by
    intro j hj
    have hnum : 15 * (j - 3) ≤ 2 ^ j - 1 := by
      have h1 : j - 4 < 2 ^ (j - 4) := Nat.lt_two_pow_self
      have h2 : 2 ^ j = 16 * 2 ^ (j - 4) := by
        rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← pow_add]
        congr 1
        omega
      have hone : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    have hreal : (5 / 3 : ℝ) * ((j : ℝ) - 3) ≤ ((2 : ℝ) ^ j - 1) / 9 := by
      have hcast : ((15 * (j - 3) : ℕ) : ℝ) ≤ ((2 ^ j - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnum
      have hone : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      have h3j : 3 ≤ j := by omega
      rw [Nat.cast_mul, Nat.cast_sub h3j, Nat.cast_sub hone] at hcast
      push_cast at hcast
      linarith
    have hmono : f j ≤ Real.exp (-(5 / 3 * ((j : ℝ) - 3))) := by
      rw [hf]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : Real.exp (-(5 / 3 * ((j : ℝ) - 3))) = Real.exp (-(5 / 3)) ^ (j - 3) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hcast : ((j - 3 : ℕ) : ℝ) = (j : ℝ) - 3 := by
        rw [Nat.cast_sub (by omega : 3 ≤ j)]
        norm_num
      rw [hcast]
      ring
    have hbase : Real.exp (-(5 / 3)) ≤ 3 / 8 := by
      calc Real.exp (-(5 / 3)) ≤ (1 + 5 / 3 : ℝ)⁻¹ :=
            exp_neg_le_inv_one_add (by norm_num)
        _ = 3 / 8 := by norm_num
    calc f j ≤ Real.exp (-(5 / 3)) ^ (j - 3) := hmono.trans_eq hpow
      _ ≤ (3 / 8 : ℝ) ^ (j - 3) := pow_le_pow_left₀ (Real.exp_pos _).le hbase _
  have hgeo : ∀ J', ∑ j ∈ Finset.Ico 4 J', (3 / 8 : ℝ) ^ (j - 3) ≤ 3 / 5 := by
    intro J'
    rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i, (3 / 8 : ℝ) ^ (4 + i - 3) = (3 / 8) * (3 / 8) ^ i := by
      intro i
      rw [show 4 + i - 3 = i + 1 from by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (J' - 4), (3 / 8 : ℝ) ^ i ≤ 8 / 5 := by
      rw [geom_sum_eq (by norm_num : (3 / 8 : ℝ) ≠ 1)]
      have hp : (0 : ℝ) ≤ (3 / 8 : ℝ) ^ (J' - 4) := by positivity
      have heq : ((3 / 8 : ℝ) ^ (J' - 4) - 1) / ((3 / 8 : ℝ) - 1)
          = (1 - (3 / 8 : ℝ) ^ (J' - 4)) * (8 / 5) := by
        field_simp
        ring
      rw [heq]
      nlinarith
    calc (3 / 8 : ℝ) * ∑ i ∈ Finset.range (J' - 4), (3 / 8 : ℝ) ^ i
        ≤ (3 / 8 : ℝ) * (8 / 5) := by
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 3 / 5 := by norm_num
  rcases le_or_gt J 4 with hJ | hJ
  · calc ∑ j ∈ Finset.range J, f j
        ≤ ∑ j ∈ Finset.range 4, f j :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hx) hJ)) fun j _ _ => hf0 j
      _ ≤ 1 + 9 / 10 + 3 / 4 + 9 / 16 := hfour
      _ ≤ 5 := by norm_num
  · have hsplit : ∑ j ∈ Finset.range J, f j
        = ∑ j ∈ Finset.range 4, f j + ∑ j ∈ Finset.Ico 4 J, f j := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive f (by omega : (0 : ℕ) ≤ 4) (by omega : 4 ≤ J)]
    have htail : ∑ j ∈ Finset.Ico 4 J, f j ≤ 3 / 5 := by
      calc ∑ j ∈ Finset.Ico 4 J, f j
          ≤ ∑ j ∈ Finset.Ico 4 J, (3 / 8 : ℝ) ^ (j - 3) := by
            refine Finset.sum_le_sum fun j hj => ?_
            exact htail_term j (Finset.mem_Ico.mp hj).1
        _ ≤ 3 / 5 := hgeo J
    rw [hsplit]
    linarith

/-- **`eq:shifted-exponential-variation`**: with the shift `ω = 1/y_{M+2}`
(`= 1/tower (M+1)`), the flow variation over the first `M` steps is at most `10`,
uniformly in `t ≥ 0`.  Applied at `M = 2n - 1` this gives the exponential decay
`‖e^{tA_n}‖ ≤ (1 + 50α/(1-α)) e^{-ω_n t}` of Theorem 1.1. -/
theorem shifted_flow_variation_le_ten {t : ℝ} (ht : 0 ≤ t) (M : ℕ) :
    ∑ k ∈ Finset.range M,
      ‖Complex.exp ((t : ℂ) * (towerSpec (k + 1) + (((tower (M + 1) : ℝ)⁻¹ : ℝ) : ℂ)))
        - Complex.exp ((t : ℂ) * (towerSpec k + (((tower (M + 1) : ℝ)⁻¹ : ℝ) : ℂ)))‖
      ≤ 10 := by
  set ω : ℝ := (tower (M + 1) : ℝ)⁻¹ with hω
  have hT : (0 : ℝ) < (tower (M + 1) : ℝ) := by exact_mod_cast tower_pos (M + 1)
  have hω0 : 0 < ω := by rw [hω]; positivity
  have hfactor : ∀ j : ℕ, Complex.exp ((t : ℂ) * (towerSpec j + ((ω : ℝ) : ℂ)))
      = Complex.exp ((t : ℂ) * ((ω : ℝ) : ℂ)) * Complex.exp ((t : ℂ) * towerSpec j) := by
    intro j
    rw [← Complex.exp_add]
    congr 1
    ring
  rcases le_or_gt t ((tower (M + 1) : ℝ) / 9) with hcase | hcase
  · -- Small times: factor out `e^{tω} ≤ e^{1/9} ≤ 9/8`.
    have hnorm : ‖Complex.exp ((t : ℂ) * ((ω : ℝ) : ℂ))‖ = Real.exp (t * ω) := by
      rw [← Complex.ofReal_mul, Complex.norm_exp, Complex.ofReal_re]
    have hexp98 : Real.exp (t * ω) ≤ 9 / 8 := by
      have h19 : t * ω ≤ 1 / 9 := by
        rw [hω]
        calc t * (tower (M + 1) : ℝ)⁻¹
            ≤ ((tower (M + 1) : ℝ) / 9) * (tower (M + 1) : ℝ)⁻¹ := by
              exact mul_le_mul_of_nonneg_right hcase (by positivity)
          _ = 1 / 9 := by field_simp
      calc Real.exp (t * ω) ≤ Real.exp (1 / 9) := Real.exp_le_exp.mpr h19
        _ ≤ (1 - 1 / 9 : ℝ)⁻¹ := exp_le_inv_one_sub (by norm_num)
        _ = 9 / 8 := by norm_num
    have hterm : ∀ k : ℕ,
        ‖Complex.exp ((t : ℂ) * (towerSpec (k + 1) + ((ω : ℝ) : ℂ)))
          - Complex.exp ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)))‖
        = Real.exp (t * ω)
          * ‖Complex.exp ((t : ℂ) * towerSpec (k + 1))
              - Complex.exp ((t : ℂ) * towerSpec k)‖ := by
      intro k
      rw [hfactor, hfactor, ← mul_sub, norm_mul, hnorm]
    calc ∑ k ∈ Finset.range M,
        ‖Complex.exp ((t : ℂ) * (towerSpec (k + 1) + ((ω : ℝ) : ℂ)))
          - Complex.exp ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)))‖
        = Real.exp (t * ω) * ∑ k ∈ Finset.range M,
            ‖Complex.exp ((t : ℂ) * towerSpec (k + 1))
              - Complex.exp ((t : ℂ) * towerSpec k)‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => hterm k
      _ ≤ (9 / 8) * 8 := by
          have h8 := flow_variation_le_eight ht M
          have hsnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range M,
              ‖Complex.exp ((t : ℂ) * towerSpec (k + 1))
                - Complex.exp ((t : ℂ) * towerSpec k)‖ :=
            Finset.sum_nonneg fun k _ => norm_nonneg _
          exact mul_le_mul hexp98 h8 hsnn (by norm_num)
      _ ≤ 10 := by norm_num
  · -- Large times: every modulus decays doubly exponentially.
    have hmod : ∀ k : ℕ, k ≤ M →
        ‖Complex.exp ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)))‖
          ≤ Real.exp (-(((2 : ℝ) ^ (M - k) - 1) / 9)) := by
      intro k hk
      have hk1 : (0 : ℝ) < (tower (k + 1) : ℝ) := by exact_mod_cast tower_pos (k + 1)
      have hre : ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ))).re
          = t * (-(1 / (tower (k + 1) : ℝ)) + ω) := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.add_re, Complex.ofReal_re, towerSpec_re]
      rw [Complex.norm_exp, hre]
      apply Real.exp_le_exp.mpr
      have hgrow : (2 : ℝ) ^ (M - k) * (tower (k + 1) : ℝ) ≤ (tower (M + 1) : ℝ) := by
        have h := two_pow_mul_tower_le (k + 1) (M - k)
        have heq : k + 1 + (M - k) = M + 1 := by omega
        rw [heq] at h
        exact_mod_cast h
      have hd : ((2 : ℝ) ^ (M - k) - 1) / (tower (M + 1) : ℝ)
          ≤ 1 / (tower (k + 1) : ℝ) - ω := by
        have h1 : (2 : ℝ) ^ (M - k) / (tower (M + 1) : ℝ) ≤ 1 / (tower (k + 1) : ℝ) := by
          rw [div_le_div_iff₀ hT hk1]
          calc (2 : ℝ) ^ (M - k) * (tower (k + 1) : ℝ) ≤ (tower (M + 1) : ℝ) := hgrow
            _ = 1 * (tower (M + 1) : ℝ) := (one_mul _).symm
        have h2 : ((2 : ℝ) ^ (M - k) - 1) / (tower (M + 1) : ℝ)
            = (2 : ℝ) ^ (M - k) / (tower (M + 1) : ℝ) - 1 / (tower (M + 1) : ℝ) := by
          ring
        rw [hω]
        rw [inv_eq_one_div]
        linarith
      have hprod : ((2 : ℝ) ^ (M - k) - 1) / 9 ≤ t * (1 / (tower (k + 1) : ℝ) - ω) := by
        have hdd : (0 : ℝ) ≤ ((2 : ℝ) ^ (M - k) - 1) / (tower (M + 1) : ℝ) := by
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (M - k) := one_le_pow₀ (by norm_num)
          positivity
        calc ((2 : ℝ) ^ (M - k) - 1) / 9
            = ((tower (M + 1) : ℝ) / 9)
                * (((2 : ℝ) ^ (M - k) - 1) / (tower (M + 1) : ℝ)) := by
              field_simp
          _ ≤ t * (((2 : ℝ) ^ (M - k) - 1) / (tower (M + 1) : ℝ)) :=
              mul_le_mul_of_nonneg_right hcase.le hdd
          _ ≤ t * (1 / (tower (k + 1) : ℝ) - ω) :=
              mul_le_mul_of_nonneg_left hd ht
      linarith
    set z : ℕ → ℝ := fun k =>
      ‖Complex.exp ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)))‖ with hz
    have hz0 : ∀ k, 0 ≤ z k := fun k => norm_nonneg _
    calc ∑ k ∈ Finset.range M,
        ‖Complex.exp ((t : ℂ) * (towerSpec (k + 1) + ((ω : ℝ) : ℂ)))
          - Complex.exp ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)))‖
        ≤ ∑ k ∈ Finset.range M, (z (k + 1) + z k) :=
          Finset.sum_le_sum fun k _ => norm_sub_le _ _
      _ = (∑ k ∈ Finset.range M, z (k + 1)) + ∑ k ∈ Finset.range M, z k :=
          Finset.sum_add_distrib
      _ ≤ 2 * ∑ k ∈ Finset.range (M + 1), z k := by
          have h1 : ∑ k ∈ Finset.range M, z (k + 1) ≤ ∑ k ∈ Finset.range (M + 1), z k := by
            rw [Finset.sum_range_succ' z M]
            have := hz0 0
            linarith
          have h2 : ∑ k ∈ Finset.range M, z k ≤ ∑ k ∈ Finset.range (M + 1), z k := by
            rw [Finset.sum_range_succ]
            have := hz0 M
            linarith
          linarith
      _ ≤ 2 * ∑ k ∈ Finset.range (M + 1), Real.exp (-(((2 : ℝ) ^ (M - k) - 1) / 9)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum fun k hk => ?_
          exact hmod k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      _ = 2 * ∑ j ∈ Finset.range (M + 1), Real.exp (-(((2 : ℝ) ^ j - 1) / 9)) := by
          congr 1
          have h := Finset.sum_range_reflect
            (fun j => Real.exp (-(((2 : ℝ) ^ j - 1) / 9))) (M + 1)
          rw [← h]
          refine Finset.sum_congr rfl fun k _ => ?_
          norm_num
      _ ≤ 2 * 5 :=
          mul_le_mul_of_nonneg_left (sum_exp_two_pow_le_five (M + 1)) (by norm_num)
      _ = 10 := by norm_num

end InverseGenerator
