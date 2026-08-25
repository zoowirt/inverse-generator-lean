/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power-sum estimates (the `p`-series toolkit)

Explicit-constant bounds for partial sums and tails of the `p`-series `∑ j^{-s}`:

* `sum_rpow_neg_le` : `∑_{j=1}^m j^{-s} ≤ m^{1-s}/(1-s)` for `0 ≤ s < 1`;
* `sum_Ioc_rpow_neg_le` : `∑_{j=m+1}^M j^{-(1+σ)} ≤ m^{-σ}/σ` for `0 < σ ≤ 1`;
* `sum_rpow_neg_le_of_one_lt` : `∑_{j=1}^m j^{-(1+σ)} ≤ 1 + 1/σ` for `0 < σ ≤ 1`.

These are the paper's `eq:elementary-power-sums`: the `Finset.sum`-versus-`rpow`
comparisons that the weighted Schur test of Lemma A.4 consumes, together with the
`ℓ²` column bounds of Proposition 2.1, Step 2.  The range `|θ| < 1/2` is visible
here: the Schur
splits instantiate `s = θ + 1/2` and `σ = θ + 1/2` (and their mirrors in `-θ`), so
the sub-critical lemma needs `θ < 1/2` and the super-critical one needs `θ > -1/2`.

## Implementation notes

No integrals: each estimate telescopes against `j^{1-s}` (respectively `j^{-σ}`),
with the pointwise step supplied by Bernoulli's inequality
`rpow_one_add_le_one_add_mul_self` (the `0 ≤ p ≤ 1` version).  This keeps the file
free of measure theory and gives small explicit constants.

The inductions are carried in *cleared* form — `(1-s) * ∑ ≤ m^{1-s}` rather than
`∑ ≤ m^{1-s}/(1-s)` — so that no division-monotonicity lemma is ever needed inside
an induction step; the divided forms are derived once at the end (cf. the same
policy for the recursions in `Coefficients.lean`).

The super-critical lemmas are restricted to exponents `1 + σ ≤ 2`.  That is all the
Schur test needs (`θ + 3/2 < 2`), and it is exactly the range where the reciprocal
Bernoulli step `(1-1/x)^σ ≤ 1 - σ/x` applies.
-/

namespace InverseGenerator

open Finset

/-- Pointwise telescoping bound, sub-critical range `0 ≤ s < 1`:
`(1-s)·x^{-s} ≤ x^{1-s} - (x-1)^{1-s}` for `x ≥ 1`. -/
theorem rpow_telescope_lt_one {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hx : 1 ≤ x) :
    (1 - s) * x ^ (-s) ≤ x ^ (1 - s) - (x - 1) ^ (1 - s) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hinv : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have hfrac : (0 : ℝ) ≤ 1 - 1 / x := by linarith
  have hdecomp : x - 1 = x * (1 - 1 / x) := by field_simp
  have hmul : (x - 1) ^ (1 - s) = x ^ (1 - s) * (1 - 1 / x) ^ (1 - s) := by
    rw [hdecomp, Real.mul_rpow hx0.le hfrac]
  have hbern : (1 - 1 / x) ^ (1 - s) ≤ 1 - (1 - s) / x := by
    have h := rpow_one_add_le_one_add_mul_self (s := -(1 / x))
      (by linarith : (-1 : ℝ) ≤ -(1 / x)) (p := 1 - s) (by linarith) (by linarith)
    rw [show (1 : ℝ) + -(1 / x) = 1 - 1 / x from by ring] at h
    calc (1 - 1 / x) ^ (1 - s) ≤ 1 + (1 - s) * -(1 / x) := h
      _ = 1 - (1 - s) / x := by ring
  have hxpow : x ^ (1 - s) * ((1 - s) / x) = (1 - s) * x ^ (-s) := by
    rw [show (1 : ℝ) - s = -s + 1 from by ring, Real.rpow_add hx0, Real.rpow_one]
    field_simp
    try ring
  have hle : (x - 1) ^ (1 - s) ≤ x ^ (1 - s) - (1 - s) * x ^ (-s) := by
    calc (x - 1) ^ (1 - s) = x ^ (1 - s) * (1 - 1 / x) ^ (1 - s) := hmul
      _ ≤ x ^ (1 - s) * (1 - (1 - s) / x) :=
          mul_le_mul_of_nonneg_left hbern (Real.rpow_nonneg hx0.le _)
      _ = x ^ (1 - s) - x ^ (1 - s) * ((1 - s) / x) := by ring
      _ = x ^ (1 - s) - (1 - s) * x ^ (-s) := by rw [hxpow]
  linarith

/-- Partial sums of the sub-critical `p`-series, cleared form:
`(1-s) * ∑_{j=1}^m j^{-s} ≤ m^{1-s}` for `0 ≤ s < 1`. -/
theorem mul_sum_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    (1 - s) * ∑ j ∈ Icc 1 m, (j : ℝ) ^ (-s) ≤ (m : ℝ) ^ (1 - s) := by
  induction m with
  | zero =>
    rw [show Finset.Icc 1 0 = ∅ from Finset.Icc_eq_empty (by omega), Finset.sum_empty,
      mul_zero, Nat.cast_zero, Real.zero_rpow (by linarith : (1 : ℝ) - s ≠ 0)]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), mul_add]
    have hx : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hpt := rpow_telescope_lt_one hs0 hs1 hx
    rw [show ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) from by push_cast; ring] at hpt
    linarith

/-- **Partial sums of the sub-critical `p`-series**:
`∑_{j=1}^m j^{-s} ≤ m^{1-s}/(1-s)` for `0 ≤ s < 1`. -/
theorem sum_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    ∑ j ∈ Icc 1 m, (j : ℝ) ^ (-s) ≤ (m : ℝ) ^ (1 - s) / (1 - s) := by
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - s)]
  linarith [mul_sum_rpow_neg_le hs0 hs1 m]

/-- Pointwise telescoping bound, super-critical range: for `0 < σ ≤ 1` and `x ≥ 2`,
`σ·x^{-(1+σ)} ≤ (x-1)^{-σ} - x^{-σ}`. -/
theorem rpow_telescope_gt_one {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hx : 2 ≤ x) :
    σ * x ^ (-(1 + σ)) ≤ (x - 1) ^ (-σ) - x ^ (-σ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x - 1 := by linarith
  have hd : σ / x ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hx0 (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hd0 : (0 : ℝ) < 1 - σ / x := by linarith
  have hinv : 1 / x ≤ 1 := by rw [div_le_one hx0]; linarith
  have hfrac : (0 : ℝ) ≤ 1 - 1 / x := by linarith
  have hdecomp : x - 1 = x * (1 - 1 / x) := by field_simp
  -- Step 1: `(x-1)^σ ≤ x^σ·(1 - σ/x)` by Bernoulli.
  have step1 : (x - 1) ^ σ ≤ x ^ σ * (1 - σ / x) := by
    rw [hdecomp, Real.mul_rpow hx0.le hfrac]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le σ)
    have h := rpow_one_add_le_one_add_mul_self (s := -(1 / x))
      (by linarith : (-1 : ℝ) ≤ -(1 / x)) (p := σ) hσ0.le hσ1
    rw [show (1 : ℝ) + -(1 / x) = 1 - 1 / x from by ring] at h
    calc (1 - 1 / x) ^ σ ≤ 1 + σ * -(1 / x) := h
      _ = 1 - σ / x := by ring
  have hpos1 : (0 : ℝ) < (x - 1) ^ σ := Real.rpow_pos_of_pos hx1 σ
  -- Step 2: invert.
  have step2 : x ^ (-σ) / (1 - σ / x) ≤ (x - 1) ^ (-σ) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hx1.le, inv_eq_one_div, inv_eq_one_div,
      div_div]
    exact one_div_le_one_div_of_le hpos1 step1
  -- Step 3: the gained factor is at least `σ/x`.
  have step3 : x ^ (-σ) * (σ / x) ≤ x ^ (-σ) / (1 - σ / x) - x ^ (-σ) := by
    have hxσ : (0 : ℝ) < x ^ (-σ) := Real.rpow_pos_of_pos hx0 _
    have hxσne : x - σ ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < x - σ)
    have expand : x ^ (-σ) / (1 - σ / x) - x ^ (-σ)
        = x ^ (-σ) * ((σ / x) / (1 - σ / x)) := by
      field_simp [hxσne]
      try ring
    rw [expand]
    refine mul_le_mul_of_nonneg_left ?_ hxσ.le
    have hσx : (0 : ℝ) ≤ σ / x := by positivity
    calc σ / x = σ / x * 1 := (mul_one _).symm
      _ ≤ σ / x * (1 / (1 - σ / x)) := by
          refine mul_le_mul_of_nonneg_left ?_ hσx
          rw [le_div_iff₀ hd0]
          linarith
      _ = σ / x / (1 - σ / x) := by ring
  -- Step 4: rewrite the left side.
  have step4 : x ^ (-σ) * (σ / x) = σ * x ^ (-(1 + σ)) := by
    rw [show -(1 + σ) = -σ + -1 from by ring, Real.rpow_add hx0, Real.rpow_neg_one]
    field_simp
    try ring
  linarith [step2, step3, step4]

/-- Tails of the super-critical `p`-series, cleared telescoped form: for `m ≤ M`,
`σ * ∑_{j=m+1}^M j^{-(1+σ)} ≤ m^{-σ} - M^{-σ}`. -/
theorem mul_sum_Ioc_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∀ M : ℕ, m ≤ M →
      σ * ∑ j ∈ Ioc m M, (j : ℝ) ^ (-(1 + σ)) ≤ (m : ℝ) ^ (-σ) - (M : ℝ) ^ (-σ) := by
  intro M
  induction M with
  | zero => intro h; exact absurd h (by omega)
  | succ M ihM =>
    intro hmM
    rcases Nat.lt_or_ge m (M + 1) with hlt | hge
    · have hmM' : m ≤ M := by omega
      rw [Finset.sum_Ioc_succ_top hmM', mul_add]
      have hx : (2 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
        have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_trans hm hmM'
        push_cast
        linarith
      have hpt := rpow_telescope_gt_one hσ0 hσ1 hx
      rw [show ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) from by push_cast; ring] at hpt
      linarith [ihM hmM']
    · rw [show m = M + 1 from by omega, Finset.Ioc_self, Finset.sum_empty, mul_zero,
        sub_self]

/-- **Tails of the super-critical `p`-series**: for `0 < σ ≤ 1` and `1 ≤ m`,
`∑_{j=m+1}^M j^{-(1+σ)} ≤ m^{-σ}/σ`, uniformly in `M`. -/
theorem sum_Ioc_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {m : ℕ} (hm : 1 ≤ m)
    (M : ℕ) :
    ∑ j ∈ Ioc m M, (j : ℝ) ^ (-(1 + σ)) ≤ (m : ℝ) ^ (-σ) / σ := by
  rw [le_div_iff₀ hσ0]
  rcases Nat.lt_or_ge M m with hlt | hge
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, zero_mul]
    positivity
  · have h := mul_sum_Ioc_rpow_neg_le hσ0 hσ1 hm M hge
    have hMnn : (0 : ℝ) ≤ (M : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg M) _
    linarith

/-! ## Reindexed forms

The Schur sums of Lemma A.4 arrive as sums over `range` and `Ico` of terms in
`q + 1`; the two helpers below shift them onto `Icc 1 m` and `Ioc p k`, and the
corollaries state the `p`-series bounds directly in that shifted form.
-/

/-- Shift `∑_{k<m} f (k+1)` onto `Icc 1 m`. -/
theorem sum_range_add_one_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ range m, f (k + 1) = ∑ j ∈ Icc 1 m, f j := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

/-- Shift `∑_{q ∈ Ico p k} f (q+1)` onto `Ioc p k`. -/
theorem sum_Ico_add_one_eq_sum_Ioc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p k : ℕ) :
    ∑ q ∈ Ico p k, f (q + 1) = ∑ j ∈ Ioc p k, f j := by
  have hIoc : Finset.Ioc p k = Finset.Ico (p + 1) (k + 1) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [show k + 1 - (p + 1) = k - p from by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_right_comm]

/-- Range form of `sum_rpow_neg_le`: `∑_{q<m} (q+1)^{-s} ≤ m^{1-s}/(1-s)`. -/
theorem sum_range_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    ∑ q ∈ range m, ((q : ℝ) + 1) ^ (-s) ≤ (m : ℝ) ^ (1 - s) / (1 - s) := by
  have h : ∑ q ∈ range m, ((q : ℝ) + 1) ^ (-s) = ∑ j ∈ Icc 1 m, (j : ℝ) ^ (-s) := by
    rw [← sum_range_add_one_eq_sum_Icc (fun j => (j : ℝ) ^ (-s)) m]
    exact Finset.sum_congr rfl fun q _ => by push_cast; ring_nf
  rw [h]
  exact sum_rpow_neg_le hs0 hs1 m

/-- `Ico` form of the tail bound: `∑_{q ∈ Ico p k} (q+1)^{-(1+σ)} ≤ p^{-σ}/σ`. -/
theorem sum_Ico_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {p : ℕ} (hp : 1 ≤ p)
    (k : ℕ) :
    ∑ q ∈ Ico p k, ((q : ℝ) + 1) ^ (-(1 + σ)) ≤ (p : ℝ) ^ (-σ) / σ := by
  have h : ∑ q ∈ Ico p k, ((q : ℝ) + 1) ^ (-(1 + σ))
      = ∑ j ∈ Ioc p k, (j : ℝ) ^ (-(1 + σ)) := by
    rw [← sum_Ico_add_one_eq_sum_Ioc (fun j => (j : ℝ) ^ (-(1 + σ))) p k]
    exact Finset.sum_congr rfl fun q _ => by push_cast; ring_nf
  rw [h]
  exact sum_Ioc_rpow_neg_le hσ0 hσ1 hp k

/-- **Full super-critical `p`-series**: for `0 < σ ≤ 1`,
`∑_{j=1}^m j^{-(1+σ)} ≤ 1 + 1/σ`. -/
theorem sum_rpow_neg_le_of_one_lt {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (m : ℕ) :
    ∑ j ∈ Icc 1 m, (j : ℝ) ^ (-(1 + σ)) ≤ 1 + 1 / σ := by
  rcases Nat.lt_or_ge m 1 with hm | hm
  · rw [show m = 0 from by omega,
      show Finset.Icc 1 0 = ∅ from Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · rw [Finset.Icc_eq_cons_Ioc hm, Finset.sum_cons]
    have htail := sum_Ioc_rpow_neg_le hσ0 hσ1 (le_refl 1) m
    rw [Nat.cast_one, Real.one_rpow] at htail ⊢
    linarith

/-! ## The lower `p`-series bound

`∑_{j=1}^m j^s ≥ m^{s+1}/(s+1)` for `s ≥ 0`, by the same telescoping style as the
upper bounds — the paper compares against `∫₀^m x^s dx`, but the pointwise Bernoulli
bound `x^{s+1} - (x-1)^{s+1} ≤ (s+1) x^s` avoids integrals entirely.  This feeds the
lower half of Lemma A.3's `‖T_n(α)‖ ≥ n^α/2` via the `1_n` test vector.
-/

/-- Pointwise telescoping bound for the lower `p`-series estimate: for `s ≥ 0` and
`x ≥ 1`, `x^{s+1} - (x-1)^{s+1} ≤ (s+1)·x^s`. -/
theorem rpow_telescope_lower {s x : ℝ} (hs : 0 ≤ s) (hx : 1 ≤ x) :
    x ^ (s + 1) - (x - 1) ^ (s + 1) ≤ (s + 1) * x ^ s := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hinv : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have hfrac : (0 : ℝ) ≤ 1 - 1 / x := by linarith
  have hdecomp : x - 1 = x * (1 - 1 / x) := by field_simp
  have hmul : (x - 1) ^ (s + 1) = x ^ (s + 1) * (1 - 1 / x) ^ (s + 1) := by
    rw [hdecomp, Real.mul_rpow hx0.le hfrac]
  have hbern : 1 - (s + 1) / x ≤ (1 - 1 / x) ^ (s + 1) := by
    have h := one_add_mul_self_le_rpow_one_add (s := -(1 / x))
      (by linarith : (-1 : ℝ) ≤ -(1 / x)) (p := s + 1) (by linarith)
    rw [show (1 : ℝ) + -(1 / x) = 1 - 1 / x from by ring] at h
    calc 1 - (s + 1) / x = 1 + (s + 1) * -(1 / x) := by ring
      _ ≤ (1 - 1 / x) ^ (s + 1) := h
  have hxpow : x ^ (s + 1) * ((s + 1) / x) = (s + 1) * x ^ s := by
    rw [Real.rpow_add hx0, Real.rpow_one]
    field_simp
    try ring
  calc x ^ (s + 1) - (x - 1) ^ (s + 1)
      = x ^ (s + 1) - x ^ (s + 1) * (1 - 1 / x) ^ (s + 1) := by rw [hmul]
    _ ≤ x ^ (s + 1) - x ^ (s + 1) * (1 - (s + 1) / x) := by
        have := mul_le_mul_of_nonneg_left hbern (Real.rpow_nonneg hx0.le (s + 1))
        linarith
    _ = x ^ (s + 1) * ((s + 1) / x) := by ring
    _ = (s + 1) * x ^ s := hxpow

/-- Cleared form of the lower `p`-series bound:
`m^{s+1} ≤ (s+1) ∑_{j=1}^m j^s` for `s ≥ 0`. -/
theorem rpow_le_mul_sum_rpow {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    (m : ℝ) ^ (s + 1) ≤ (s + 1) * ∑ j ∈ Icc 1 m, (j : ℝ) ^ s := by
  induction m with
  | zero =>
    rw [show Finset.Icc 1 0 = ∅ from Finset.Icc_eq_empty (by omega), Finset.sum_empty,
      mul_zero, Nat.cast_zero, Real.zero_rpow (by linarith : (s : ℝ) + 1 ≠ 0)]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), mul_add]
    have hx : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hpt := rpow_telescope_lower hs hx
    rw [show ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) from by push_cast; ring] at hpt
    linarith

/-- **Lower `p`-series bound**, `range` form:
`n^{s+1}/(s+1) ≤ ∑_{i<n} (i+1)^s` for `s ≥ 0`. -/
theorem rpow_div_le_sum_range_rpow {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    (n : ℝ) ^ (s + 1) / (s + 1) ≤ ∑ i ∈ range n, ((i : ℝ) + 1) ^ s := by
  have h : ∑ i ∈ range n, ((i : ℝ) + 1) ^ s = ∑ j ∈ Icc 1 n, (j : ℝ) ^ s := by
    rw [← sum_range_add_one_eq_sum_Icc (fun j => (j : ℝ) ^ s) n]
    exact Finset.sum_congr rfl fun q _ => by push_cast; ring_nf
  rw [h, div_le_iff₀ (by linarith : (0 : ℝ) < s + 1), mul_comm]
  exact rpow_le_mul_sum_rpow hs n

end InverseGenerator
