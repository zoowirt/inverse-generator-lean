/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.NormGrowth
import InverseGenerator.PrefixBound
import InverseGenerator.RpowSums

/-!
# Lemma A.4: the uniform fractional prefix bound

The paper's Lemma A.4: for `|θ| < 1/2`,
```
sup_n sup_{k ≤ n} ‖T_n(θ) Π_{n,k} T_n(-θ) - Π_{n,k}‖ ≤ 6|θ| / (1 - 4θ²) ,
```
the constant being `sharpPrefixConst θ` below.  The factor `|θ|` is what lets the
constant vanish as `θ → 0`, and hence what makes the explicit `C = 50` of
Theorem 1.1 reachable.

This lemma is the entire substitute for an external conditional-basis theorem, and
the one place where the range `|θ| < 1/2` is consumed: the row splits need `θ < 1/2`
and the column splits need `θ > -1/2` — neither is slack.

## Structure

* `norm_schurKernel_le'` — the sharp kernel bound `eq:prefix-kernel-bound`,
  `‖R_{p,q}‖ ≤ (3/2)|θ| p^θ (q+1)^{-θ}/(p+q)`, from the coefficient bounds of
  Lemma A.2.
* `schur_row_sum_le_of_kernel`, `schur_col_sum_le_of_kernel` — the row and column
  Schur tests: the weighted sums against `u_p = p^{-1/2}`, `v_q = (q+1)^{-1/2}`, via
  the four `p`-series splits of `RpowSums.lean` (`eq:elementary-power-sums`).  They
  are parametrized over the
  kernel constant `c`, so the row and column tests are one proof, not two.  These are
  ℕ-indexed scalar lemmas; all the analysis lives here.
* `prefixConj_eq_add` — the block form as a decomposition `Q = P_k + R̃`, `R̃` the
  zero-padded lower-left block, so that `‖Q - P_k‖ = ‖R̃‖` exactly.
* `l2_opNorm_prefixConj_sub_le` — **Lemma A.4**.

## Implementation notes

Proving both signs of `θ` directly costs only mirrored instantiations of the same
`p`-series lemmas.  The alternative — the flip duality `‖Q_k^{(θ)}‖ = ‖Q_{n-k}^{(-θ)}‖`
— would need `‖P‖ = ‖I - P‖` for Hilbert-space idempotents, which Mathlib does not
have and which is a nontrivial theorem of its own.

The weight `v` is set to `1` on the columns `j ≥ k` where the block vanishes: the
Schur test requires *strictly positive* weights, and `(k-j)^{-1/2}` would be `0` there.
-/

namespace InverseGenerator

open Finset Matrix

/-- `schurKernel` commutes with the coercion `ℝ → ℂ`. -/
theorem schurKernel_ofReal (θ : ℝ) (p q : ℕ) :
    ((schurKernel θ p q : ℝ) : ℂ) = schurKernel ((θ : ℂ)) p q := by
  rw [schurKernel, schurKernel]
  push_cast [binomCoeff_ofReal]
  ring

/-- **The kernel bound** (`eq:prefix-kernel-bound`):
`‖R_{p,q}‖ ≤ (3/2)|θ| p^θ (q+1)^{-θ} / (p+q)` for `|θ| < 1/2` and `p ≥ 1`.  The
`|θ|` factor is what makes the prefix constant vanish
as `θ → 0`, and hence the explicit `C = 50` of Theorem 1.1 reachable. -/
theorem norm_schurKernel_le' {θ : ℝ} (hθ : |θ| < 1 / 2) {p : ℕ} (hp : 1 ≤ p) (q : ℕ) :
    ‖schurKernel ((θ : ℂ)) p q‖
      ≤ 3 / 2 * |θ| * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((p : ℝ) + q) := by
  obtain ⟨hθl, hθr⟩ := abs_lt.mp hθ
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hpq : (0 : ℝ) < (p : ℝ) + q := by linarith
  -- the product bound `|a_p(θ)| · a_q(1-θ) ≤ (3/2)|θ| p^{θ-1} (q+1)^{-θ}`
  have hq1nn : 0 ≤ binomCoeff q (1 - θ) := binomCoeff_nonneg (by linarith) q
  have hcp : binomCoeff q (1 - θ) = coeffProd (-θ) q := by
    have := binomCoeff_add_one_eq_coeffProd (-θ) q
    rwa [show -θ + 1 = 1 - θ from by ring] at this
  have hprod : |binomCoeff p θ| * binomCoeff q (1 - θ)
      ≤ 3 / 2 * |θ| * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-θ) := by
    rcases lt_trichotomy θ 0 with hneg | hzero | hpos
    · -- `θ < 0`
      have h1 : |binomCoeff p θ| ≤ |θ| * (p : ℝ) ^ (θ - 1) :=
        abs_binomCoeff_le_mul_rpow (by linarith) hneg.le hp
      have h2 : binomCoeff q (1 - θ) ≤ 3 / 2 * ((q : ℝ) + 1) ^ (-θ) := by
        rw [hcp]
        rcases Nat.eq_zero_or_pos q with hq | hq
        · subst hq
          rw [coeffProd_zero, Nat.cast_zero, zero_add, Real.one_rpow]
          norm_num
        · have h3 := coeffProd_le_one_add_self_mul (t := -θ) (by linarith) hq
          have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
          have hmono : (q : ℝ) ^ (-θ) ≤ ((q : ℝ) + 1) ^ (-θ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
          have hqnn : (0 : ℝ) ≤ (q : ℝ) ^ (-θ) := Real.rpow_nonneg (by linarith) _
          calc coeffProd (-θ) q ≤ (1 + -θ) * (q : ℝ) ^ (-θ) := h3
            _ ≤ (3 / 2) * (q : ℝ) ^ (-θ) :=
                mul_le_mul_of_nonneg_right (by linarith) hqnn
            _ ≤ 3 / 2 * ((q : ℝ) + 1) ^ (-θ) :=
                mul_le_mul_of_nonneg_left hmono (by norm_num)
      calc |binomCoeff p θ| * binomCoeff q (1 - θ)
          ≤ (|θ| * (p : ℝ) ^ (θ - 1)) * (3 / 2 * ((q : ℝ) + 1) ^ (-θ)) :=
            mul_le_mul h1 h2 hq1nn (by positivity)
        _ = 3 / 2 * |θ| * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-θ) := by ring
    · -- `θ = 0`: the kernel vanishes and so does the bound.
      subst hzero
      rw [binomCoeff_eq_zero_of_arg_zero hp, abs_zero, zero_mul]
      simp
    · -- `θ > 0`
      have h1 : |binomCoeff p θ| ≤ 3 / 2 * θ * (p : ℝ) ^ (θ - 1) := by
        rw [abs_of_nonneg (binomCoeff_nonneg hpos.le p)]
        exact binomCoeff_le_three_half_mul_rpow hpos.le (by linarith) hp
      have h2 : binomCoeff q (1 - θ) ≤ ((q : ℝ) + 1) ^ (-θ) := by
        rw [hcp]
        exact coeffProd_le_rpow_succ (by linarith) (by linarith) q
      have habs : |θ| = θ := abs_of_pos hpos
      calc |binomCoeff p θ| * binomCoeff q (1 - θ)
          ≤ (3 / 2 * θ * (p : ℝ) ^ (θ - 1)) * ((q : ℝ) + 1) ^ (-θ) :=
            mul_le_mul h1 h2 hq1nn (by positivity)
        _ = 3 / 2 * |θ| * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-θ) := by rw [habs]
  -- assemble
  rw [← schurKernel_ofReal, Complex.norm_real, Real.norm_eq_abs, schurKernel,
    abs_mul, abs_mul]
  have hmid : |(p : ℝ) / ((p : ℝ) + q)| = (p : ℝ) / ((p : ℝ) + q) :=
    abs_of_pos (div_pos hp0 hpq)
  have hlast : |binomCoeff q (1 - θ)| = binomCoeff q (1 - θ) := abs_of_nonneg hq1nn
  rw [hmid, hlast]
  calc |binomCoeff p θ| * ((p : ℝ) / ((p : ℝ) + q)) * binomCoeff q (1 - θ)
      = (|binomCoeff p θ| * binomCoeff q (1 - θ)) * ((p : ℝ) / ((p : ℝ) + q)) := by
        ring
    _ ≤ (3 / 2 * |θ| * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-θ))
          * ((p : ℝ) / ((p : ℝ) + q)) :=
        mul_le_mul_of_nonneg_right hprod (div_pos hp0 hpq).le
    _ = 3 / 2 * |θ| * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((p : ℝ) + q) := by
        rw [Real.rpow_sub hp0, Real.rpow_one]
        field_simp
        try ring

/-! ## The weighted row and column tests -/

/-- **The row test, parametrized over the kernel constant**: if
`‖R_{p,q}‖ ≤ c p^θ (q+1)^{-θ}/(p+q)`, then
`∑_{q<k} ‖R_{p,q}‖ (q+1)^{-1/2} ≤ (c/(1/2-θ) + c/(1/2+θ)) p^{-1/2}`, uniformly
in `k`.  Parametrizing over `c` makes the row and column tests one proof; it is
instantiated at `c = (3/2)|θ|` from `norm_schurKernel_le'`. -/
theorem schur_row_sum_le_of_kernel {θ c : ℝ} (hθ : |θ| < 1 / 2) (hc : 0 ≤ c) {p : ℕ}
    (hp : 1 ≤ p)
    (hker : ∀ q : ℕ, ‖schurKernel ((θ : ℂ)) p q‖
      ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((p : ℝ) + q)) (k : ℕ) :
    ∑ q ∈ range k, ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ (c / (1 / 2 - θ) + c / (1 / 2 + θ)) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
  obtain ⟨hθl, hθr⟩ := abs_lt.mp hθ
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- the combined termwise bound
  have hcomb : ∀ q : ℕ, ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) / ((p : ℝ) + q) := by
    intro q
    have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have hw : (0 : ℝ) ≤ ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hq1.le _
    calc ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        ≤ (c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((p : ℝ) + q))
            * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right (hker q) hw
      _ = c * (p : ℝ) ^ θ * (((q : ℝ) + 1) ^ (-θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ))
            / ((p : ℝ) + q) := by ring
      _ = c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) / ((p : ℝ) + q) := by
          rw [← Real.rpow_add hq1, show -θ + -(1 / 2 : ℝ) = -(θ + 1 / 2) from by ring]
  -- part A: `q < p`, denominator `≥ p`
  have hpartA : ∑ q ∈ (range k).filter (fun q => q < p),
      ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ c / (1 / 2 - θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hAterm : ∀ q ∈ (range k).filter (fun q => q < p),
        ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
          ≤ c * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) := by
      intro q _
      have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
      have hqc : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      refine (hcomb q).trans ?_
      have hden : (p : ℝ) ≤ (p : ℝ) + q := by linarith
      have hnum : (0 : ℝ) ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) :=
        mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hp0.le _))
          (Real.rpow_nonneg hq1.le _)
      calc c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) / ((p : ℝ) + q)
          ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) / (p : ℝ) :=
            div_le_div_of_nonneg_left hnum hp0 hden
        _ = c * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) := by
            rw [Real.rpow_sub hp0, Real.rpow_one]
            ring
    calc ∑ q ∈ (range k).filter (fun q => q < p),
        ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        ≤ ∑ q ∈ (range k).filter (fun q => q < p),
            c * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) :=
          Finset.sum_le_sum hAterm
      _ ≤ ∑ q ∈ range p, c * (p : ℝ) ^ (θ - 1) * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ =>
            mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hp0.le _))
              (Real.rpow_nonneg (by positivity) _)
          intro q hq
          rw [Finset.mem_filter, Finset.mem_range] at hq
          exact Finset.mem_range.mpr hq.2
      _ = c * (p : ℝ) ^ (θ - 1) * ∑ q ∈ range p, ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) := by
          rw [← Finset.mul_sum]
      _ ≤ c * (p : ℝ) ^ (θ - 1) * ((p : ℝ) ^ (1 - (θ + 1 / 2)) / (1 - (θ + 1 / 2))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hc (Real.rpow_nonneg hp0.le _))
          exact sum_range_rpow_neg_le (by linarith) (by linarith) p
      _ = c / (1 / 2 - θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
          rw [show (1 : ℝ) - (θ + 1 / 2) = 1 / 2 - θ from by ring]
          have hcombine : (p : ℝ) ^ (θ - 1) * (p : ℝ) ^ (1 / 2 - θ)
              = (p : ℝ) ^ (-(1 / 2) : ℝ) := by
            rw [← Real.rpow_add hp0]
            congr 1
            ring
          calc c * (p : ℝ) ^ (θ - 1) * ((p : ℝ) ^ (1 / 2 - θ) / (1 / 2 - θ))
              = c * ((p : ℝ) ^ (θ - 1) * (p : ℝ) ^ (1 / 2 - θ)) / (1 / 2 - θ) := by ring
            _ = c * (p : ℝ) ^ (-(1 / 2) : ℝ) / (1 / 2 - θ) := by rw [hcombine]
            _ = c / (1 / 2 - θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by ring
  -- part B: `q ≥ p`, denominator `≥ q + 1`
  have hIcoB : (range k).filter (fun q => ¬ q < p) = Ico p k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]
    omega
  have hpartB : ∑ q ∈ (range k).filter (fun q => ¬ q < p),
      ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ c / (1 / 2 + θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hBterm : ∀ q ∈ (range k).filter (fun q => ¬ q < p),
        ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
          ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(1 + (θ + 1 / 2))) := by
      intro q _
      have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
      have hqc : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      refine (hcomb q).trans ?_
      have hden : (q : ℝ) + 1 ≤ (p : ℝ) + q := by linarith
      have hnum : (0 : ℝ) ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) :=
        mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hp0.le _))
          (Real.rpow_nonneg hq1.le _)
      calc c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) / ((p : ℝ) + q)
          ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(θ + 1 / 2)) / ((q : ℝ) + 1) :=
            div_le_div_of_nonneg_left hnum hq1 hden
        _ = c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(1 + (θ + 1 / 2))) := by
            rw [show -(1 + (θ + 1 / 2)) = -(θ + 1 / 2) + (-1 : ℝ) from by ring,
              Real.rpow_add hq1, Real.rpow_neg_one]
            ring
    calc ∑ q ∈ (range k).filter (fun q => ¬ q < p),
        ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        ≤ ∑ q ∈ (range k).filter (fun q => ¬ q < p),
            c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-(1 + (θ + 1 / 2))) :=
          Finset.sum_le_sum hBterm
      _ = c * (p : ℝ) ^ θ * ∑ q ∈ Ico p k, ((q : ℝ) + 1) ^ (-(1 + (θ + 1 / 2))) := by
          rw [hIcoB, ← Finset.mul_sum]
      _ ≤ c * (p : ℝ) ^ θ * ((p : ℝ) ^ (-(θ + 1 / 2)) / (θ + 1 / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hc (Real.rpow_nonneg hp0.le _))
          exact sum_Ico_rpow_neg_le (by linarith) (by linarith) hp k
      _ = c / (1 / 2 + θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
          have hcombine : (p : ℝ) ^ θ * (p : ℝ) ^ (-(θ + 1 / 2))
              = (p : ℝ) ^ (-(1 / 2) : ℝ) := by
            rw [← Real.rpow_add hp0]
            congr 1
            ring
          calc c * (p : ℝ) ^ θ * ((p : ℝ) ^ (-(θ + 1 / 2)) / (θ + 1 / 2))
              = c * ((p : ℝ) ^ θ * (p : ℝ) ^ (-(θ + 1 / 2))) / (θ + 1 / 2) := by ring
            _ = c * (p : ℝ) ^ (-(1 / 2) : ℝ) / (θ + 1 / 2) := by rw [hcombine]
            _ = c / (1 / 2 + θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
                rw [show θ + 1 / 2 = 1 / 2 + θ from by ring]
                ring
  calc ∑ q ∈ range k, ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      = (∑ q ∈ (range k).filter (fun q => q < p),
          ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ))
        + ∑ q ∈ (range k).filter (fun q => ¬ q < p),
          ‖schurKernel ((θ : ℂ)) p q‖ * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) :=
        (Finset.sum_filter_add_sum_filter_not (range k) (fun q => q < p) _).symm
    _ ≤ c / (1 / 2 - θ) * (p : ℝ) ^ (-(1 / 2) : ℝ)
        + c / (1 / 2 + θ) * (p : ℝ) ^ (-(1 / 2) : ℝ) := add_le_add hpartA hpartB
    _ = (c / (1 / 2 - θ) + c / (1 / 2 + θ)) * (p : ℝ) ^ (-(1 / 2) : ℝ) := by ring

/-- **The column test, parametrized over the kernel constant**: if
`‖R_{r+1,q}‖ ≤ c (r+1)^θ (q+1)^{-θ}/(r+1+q)`, then
`∑_{r<m} ‖R_{r+1,q}‖ (r+1)^{-1/2} ≤ (c/(1/2-θ) + c/(1/2+θ)) (q+1)^{-1/2}`,
uniformly in `m`. -/
theorem schur_col_sum_le_of_kernel {θ c : ℝ} (hθ : |θ| < 1 / 2) (hc : 0 ≤ c) (q : ℕ)
    (hker : ∀ r : ℕ, ‖schurKernel ((θ : ℂ)) (r + 1) q‖
      ≤ c * ((r : ℝ) + 1) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((r : ℝ) + 1 + q)) (m : ℕ) :
    ∑ r ∈ range m, ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ (c / (1 / 2 - θ) + c / (1 / 2 + θ)) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
  obtain ⟨hθl, hθr⟩ := abs_lt.mp hθ
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hqc : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  -- the combined termwise bound
  have hcomb : ∀ r : ℕ, ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) / (((r : ℝ) + 1) + q) := by
    intro r
    have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hK := hker r
    have hw : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hr1.le _
    calc ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        ≤ (c * ((r : ℝ) + 1) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((r : ℝ) + 1 + q))
            * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_right hK hw
      _ = c * ((q : ℝ) + 1) ^ (-θ) * (((r : ℝ) + 1) ^ θ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ))
            / (((r : ℝ) + 1) + q) := by ring
      _ = c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) / (((r : ℝ) + 1) + q) := by
          rw [← Real.rpow_add hr1, show θ + -(1 / 2 : ℝ) = θ - 1 / 2 from by ring]
  -- part A: `r + 1 ≤ q + 1`, denominator `≥ q + 1`
  have hpartA : ∑ r ∈ (range m).filter (fun r => r < q + 1),
      ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ c / (1 / 2 + θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
    have hAterm : ∀ r ∈ (range m).filter (fun r => r < q + 1),
        ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
          ≤ c * ((q : ℝ) + 1) ^ (-(θ + 1)) * ((r : ℝ) + 1) ^ (-(1 / 2 - θ)) := by
      intro r _
      have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      have hrc : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      refine (hcomb r).trans ?_
      have hden : (q : ℝ) + 1 ≤ ((r : ℝ) + 1) + q := by linarith
      have hnum : (0 : ℝ) ≤ c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) :=
        mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hq1.le _))
          (Real.rpow_nonneg hr1.le _)
      calc c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) / (((r : ℝ) + 1) + q)
          ≤ c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) / ((q : ℝ) + 1) :=
            div_le_div_of_nonneg_left hnum hq1 hden
        _ = c * ((q : ℝ) + 1) ^ (-(θ + 1)) * ((r : ℝ) + 1) ^ (-(1 / 2 - θ)) := by
            rw [show -(θ + 1) = -θ + (-1 : ℝ) from by ring, Real.rpow_add hq1,
              Real.rpow_neg_one, show -(1 / 2 - θ) = θ - 1 / 2 from by ring]
            ring
    calc ∑ r ∈ (range m).filter (fun r => r < q + 1),
        ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        ≤ ∑ r ∈ (range m).filter (fun r => r < q + 1),
            c * ((q : ℝ) + 1) ^ (-(θ + 1)) * ((r : ℝ) + 1) ^ (-(1 / 2 - θ)) :=
          Finset.sum_le_sum hAterm
      _ ≤ ∑ r ∈ range (q + 1),
            c * ((q : ℝ) + 1) ^ (-(θ + 1)) * ((r : ℝ) + 1) ^ (-(1 / 2 - θ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ =>
            mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hq1.le _))
              (Real.rpow_nonneg (by positivity) _)
          intro r hr
          rw [Finset.mem_filter, Finset.mem_range] at hr
          exact Finset.mem_range.mpr hr.2
      _ = c * ((q : ℝ) + 1) ^ (-(θ + 1))
            * ∑ r ∈ range (q + 1), ((r : ℝ) + 1) ^ (-(1 / 2 - θ)) := by
          rw [← Finset.mul_sum]
      _ ≤ c * ((q : ℝ) + 1) ^ (-(θ + 1))
            * (((q + 1 : ℕ) : ℝ) ^ (1 - (1 / 2 - θ)) / (1 - (1 / 2 - θ))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hc (Real.rpow_nonneg hq1.le _))
          exact sum_range_rpow_neg_le (by linarith) (by linarith) (q + 1)
      _ = c / (1 / 2 + θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
          push_cast
          rw [show (1 : ℝ) - (1 / 2 - θ) = 1 / 2 + θ from by ring]
          have hcombine : ((q : ℝ) + 1) ^ (-(θ + 1)) * ((q : ℝ) + 1) ^ (1 / 2 + θ)
              = ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
            rw [← Real.rpow_add hq1]
            congr 1
            ring
          calc c * ((q : ℝ) + 1) ^ (-(θ + 1))
                * (((q : ℝ) + 1) ^ (1 / 2 + θ) / (1 / 2 + θ))
              = c * (((q : ℝ) + 1) ^ (-(θ + 1)) * ((q : ℝ) + 1) ^ (1 / 2 + θ))
                  / (1 / 2 + θ) := by ring
            _ = c * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) / (1 / 2 + θ) := by rw [hcombine]
            _ = c / (1 / 2 + θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by ring
  -- part B: `r + 1 > q + 1`, denominator `≥ r + 1`
  have hIcoB : (range m).filter (fun r => ¬ r < q + 1) = Ico (q + 1) m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]
    omega
  have hpartB : ∑ r ∈ (range m).filter (fun r => ¬ r < q + 1),
      ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      ≤ c / (1 / 2 - θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
    have hBterm : ∀ r ∈ (range m).filter (fun r => ¬ r < q + 1),
        ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
          ≤ c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (-(1 + (1 / 2 - θ))) := by
      intro r _
      have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      have hrc : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      refine (hcomb r).trans ?_
      have hden : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) + q := by linarith
      have hnum : (0 : ℝ) ≤ c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) :=
        mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hq1.le _))
          (Real.rpow_nonneg hr1.le _)
      calc c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) / (((r : ℝ) + 1) + q)
          ≤ c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (θ - 1 / 2) / ((r : ℝ) + 1) :=
            div_le_div_of_nonneg_left hnum hr1 hden
        _ = c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (-(1 + (1 / 2 - θ))) := by
            rw [show -(1 + (1 / 2 - θ)) = θ - 1 / 2 + (-1 : ℝ) from by ring,
              Real.rpow_add hr1, Real.rpow_neg_one]
            ring
    calc ∑ r ∈ (range m).filter (fun r => ¬ r < q + 1),
        ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        ≤ ∑ r ∈ (range m).filter (fun r => ¬ r < q + 1),
            c * ((q : ℝ) + 1) ^ (-θ) * ((r : ℝ) + 1) ^ (-(1 + (1 / 2 - θ))) :=
          Finset.sum_le_sum hBterm
      _ = c * ((q : ℝ) + 1) ^ (-θ)
            * ∑ r ∈ Ico (q + 1) m, ((r : ℝ) + 1) ^ (-(1 + (1 / 2 - θ))) := by
          rw [hIcoB, ← Finset.mul_sum]
      _ ≤ c * ((q : ℝ) + 1) ^ (-θ)
            * (((q + 1 : ℕ) : ℝ) ^ (-(1 / 2 - θ)) / (1 / 2 - θ)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hc (Real.rpow_nonneg hq1.le _))
          exact sum_Ico_rpow_neg_le (by linarith) (by linarith) (by omega) m
      _ = c / (1 / 2 - θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
          push_cast
          have hcombine : ((q : ℝ) + 1) ^ (-θ) * ((q : ℝ) + 1) ^ (-(1 / 2 - θ))
              = ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
            rw [← Real.rpow_add hq1]
            congr 1
            ring
          calc c * ((q : ℝ) + 1) ^ (-θ) * (((q : ℝ) + 1) ^ (-(1 / 2 - θ)) / (1 / 2 - θ))
              = c * (((q : ℝ) + 1) ^ (-θ) * ((q : ℝ) + 1) ^ (-(1 / 2 - θ)))
                  / (1 / 2 - θ) := by ring
            _ = c * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) / (1 / 2 - θ) := by rw [hcombine]
            _ = c / (1 / 2 - θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by ring
  calc ∑ r ∈ range m, ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ)
      = (∑ r ∈ (range m).filter (fun r => r < q + 1),
          ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ))
        + ∑ r ∈ (range m).filter (fun r => ¬ r < q + 1),
          ‖schurKernel ((θ : ℂ)) (r + 1) q‖ * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ) :=
        (Finset.sum_filter_add_sum_filter_not (range m) (fun r => r < q + 1) _).symm
    _ ≤ c / (1 / 2 + θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)
        + c / (1 / 2 - θ) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := add_le_add hpartA hpartB
    _ = (c / (1 / 2 - θ) + c / (1 / 2 + θ)) * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by ring

/-! ## The block decomposition and the norm bound -/

section Matrixx

variable {K : Type*} [Field K] [CharZero K]

/-- The lower-left block `R`, zero-padded to a full `n × n` matrix. -/
noncomputable def lowBlock (n k : ℕ) (θ : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if k ≤ (i : ℕ) ∧ (j : ℕ) < k then schurKernel θ ((i : ℕ) - k + 1) (k - (j : ℕ) - 1)
    else 0

omit [CharZero K] in
theorem lowBlock_apply {n k : ℕ} (θ : K) (i j : Fin n) :
    lowBlock n k θ i j
      = if k ≤ (i : ℕ) ∧ (j : ℕ) < k then schurKernel θ ((i : ℕ) - k + 1) (k - (j : ℕ) - 1)
        else 0 := rfl

/-- The block form as a decomposition: `T_n(θ) P_k T_n(-θ) = P_k + R̃`. -/
theorem prefixConj_eq_add {n k : ℕ} (hk : k ≤ n) (θ : K) :
    prefixConj n k θ = prefixProj n k + lowBlock n k θ := by
  ext i j
  rw [Matrix.add_apply, lowBlock_apply]
  rw [show prefixProj n k (K := K) i j
      = if i = j then (if (i : ℕ) < k then (1 : K) else 0) else 0 from by
    rw [prefixProj, Matrix.diagonal_apply]]
  by_cases hik : (i : ℕ) < k
  · have hg : ¬(k ≤ (i : ℕ) ∧ (j : ℕ) < k) := by omega
    rw [prefixConj_apply_upper k θ i j hik, if_neg hg, add_zero]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, if_pos hik]
    · rw [if_neg hij, if_neg hij]
  · have hik' : k ≤ (i : ℕ) := by omega
    have hproj : (if i = j then (if (i : ℕ) < k then (1 : K) else 0) else 0) = 0 := by
      by_cases hij : i = j
      · rw [if_pos hij, if_neg hik]
      · rw [if_neg hij]
    rw [hproj, zero_add]
    by_cases hjk : (j : ℕ) < k
    · rw [prefixConj_apply_lower k θ hk i j hik' hjk, if_pos ⟨hik', hjk⟩]
    · rw [prefixConj_apply_right k θ i j (by omega), if_neg (fun h => hjk h.2)]

end Matrixx

section OpNorm

open scoped Matrix.Norms.L2Operator

/-- The padded block `R̃` passes the weighted Schur test, parametrized over the
kernel constant: if `‖R_{p,q}‖ ≤ c p^θ (q+1)^{-θ}/(p+q)`, then
`‖R̃‖ ≤ c/(1/2-θ) + c/(1/2+θ)`, uniformly in `n` and `k ≤ n`. -/
theorem l2_opNorm_lowBlock_le_of_kernel {θ c : ℝ} (hθ : |θ| < 1 / 2) (hc : 0 ≤ c)
    (hker : ∀ {p : ℕ}, 1 ≤ p → ∀ q : ℕ, ‖schurKernel ((θ : ℂ)) p q‖
      ≤ c * (p : ℝ) ^ θ * ((q : ℝ) + 1) ^ (-θ) / ((p : ℝ) + q))
    {n k : ℕ} (hk : k ≤ n) :
    ‖lowBlock n k ((θ : ℂ))‖ ≤ c / (1 / 2 - θ) + c / (1 / 2 + θ) := by
  obtain ⟨hθl, hθr⟩ := abs_lt.mp hθ
  have hC : (0 : ℝ) ≤ c / (1 / 2 - θ) + c / (1 / 2 + θ) := by
    have h1 : (0 : ℝ) ≤ c / (1 / 2 - θ) := div_nonneg hc (by linarith)
    have h2 : (0 : ℝ) ≤ c / (1 / 2 + θ) := div_nonneg hc (by linarith)
    linarith
  refine l2_opNorm_le_of_schur
    (u := fun i : Fin n => (((i : ℕ) - k + 1 : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))
    (v := fun j : Fin n =>
      if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1)
    ?_ hC ?_ ?_
  · -- positivity of the column weights
    intro j
    by_cases hj : (j : ℕ) < k
    · rw [if_pos hj]
      have h0 : (0 : ℝ) < ((k - (j : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < k - (j : ℕ) from by omega)
      exact Real.rpow_pos_of_pos h0 _
    · rw [if_neg hj]
      norm_num
  · -- row test
    intro i
    by_cases hik : k ≤ (i : ℕ)
    · -- active rows: reduce to `schur_row_sum_le` at `p = i - k + 1`
      have hp1 : 1 ≤ (i : ℕ) - k + 1 := by omega
      have hgoal : ∑ j : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
            * (if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1)
          ≤ (c / (1 / 2 - θ) + c / (1 / 2 + θ))
            * ((((i : ℕ) - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by
        have h1 : ∑ j : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
              * (if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1)
            = ∑ jn ∈ range n,
              (if k ≤ (i : ℕ) ∧ jn < k
                then ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) (k - jn - 1)‖ else 0)
              * (if jn < k then ((k - jn : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1) := by
          rw [← Fin.sum_univ_eq_sum_range (fun jn =>
            (if k ≤ (i : ℕ) ∧ jn < k
              then ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) (k - jn - 1)‖ else 0)
            * (if jn < k then ((k - jn : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1)) n]
          exact Finset.sum_congr rfl fun j _ => by
            rw [lowBlock_apply, apply_ite norm, norm_zero]
        have h2 : ∑ jn ∈ range n,
              ((if k ≤ (i : ℕ) ∧ jn < k
                then ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) (k - jn - 1)‖ else 0)
              * (if jn < k then ((k - jn : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1))
            = ∑ jn ∈ range k, ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) (k - jn - 1)‖
                * ((k - jn : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
          have hsub : range k ⊆ range n := fun x hx =>
            Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hk)
          have hvan : ∀ jn ∈ range n, jn ∉ range k →
              (if k ≤ (i : ℕ) ∧ jn < k
                then ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) (k - jn - 1)‖ else 0)
              * (if jn < k then ((k - jn : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1) = 0 := by
            intro jn _ hjn
            rw [Finset.mem_range, not_lt] at hjn
            rw [if_neg (fun h => absurd h.2 (by omega)), zero_mul]
          rw [← Finset.sum_subset hsub hvan]
          refine Finset.sum_congr rfl fun jn hjn => ?_
          rw [Finset.mem_range] at hjn
          rw [if_pos ⟨hik, hjn⟩, if_pos hjn]
        have h3 : ∑ jn ∈ range k, ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) (k - jn - 1)‖
              * ((k - jn : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)
            = ∑ q ∈ range k, ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) q‖
              * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
          rw [← Finset.sum_range_reflect (fun q =>
            ‖schurKernel ((θ : ℂ)) ((i : ℕ) - k + 1) q‖
              * ((q : ℝ) + 1) ^ (-(1 / 2) : ℝ)) k]
          refine Finset.sum_congr rfl fun jn hjn => ?_
          rw [Finset.mem_range] at hjn
          have e1 : k - jn - 1 = k - 1 - jn := by omega
          have e2 : ((k - jn : ℕ) : ℝ) = ((k - 1 - jn : ℕ) : ℝ) + 1 := by
            have h : k - jn = (k - 1 - jn) + 1 := by omega
            rw [h]
            push_cast
            ring
          rw [e1, e2]
        rw [h1, h2, h3]
        exact schur_row_sum_le_of_kernel hθ hc hp1 (fun q => hker hp1 q) k
      exact hgoal
    · -- zero rows
      have hgoal : ∑ j : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
            * (if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1)
          ≤ (c / (1 / 2 - θ) + c / (1 / 2 + θ))
            * ((((i : ℕ) - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by
        have hsum0 : ∑ j : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
              * (if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1)
            = 0 := Finset.sum_eq_zero fun j _ => by
          rw [lowBlock_apply, if_neg (fun h => absurd h.1 hik), norm_zero, zero_mul]
        rw [hsum0]
        exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact hgoal
  · -- column test
    intro j
    by_cases hjk : (j : ℕ) < k
    · -- active columns: reduce to `schur_col_sum_le` at `q = k - j - 1`
      have hgoal : ∑ i : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
            * ((((i : ℕ) - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)
          ≤ (c / (1 / 2 - θ) + c / (1 / 2 + θ))
            * (if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1) := by
        rw [if_pos hjk]
        have h1 : ∑ i : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
              * ((((i : ℕ) - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)
            = ∑ im ∈ range n,
              (if k ≤ im ∧ (j : ℕ) < k
                then ‖schurKernel ((θ : ℂ)) (im - k + 1) (k - (j : ℕ) - 1)‖ else 0)
              * (((im - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by
          rw [← Fin.sum_univ_eq_sum_range (fun im =>
            (if k ≤ im ∧ (j : ℕ) < k
              then ‖schurKernel ((θ : ℂ)) (im - k + 1) (k - (j : ℕ) - 1)‖ else 0)
            * (((im - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)) n]
          exact Finset.sum_congr rfl fun i _ => by
            rw [lowBlock_apply, apply_ite norm, norm_zero]
        have h2 : ∑ im ∈ range n,
              ((if k ≤ im ∧ (j : ℕ) < k
                then ‖schurKernel ((θ : ℂ)) (im - k + 1) (k - (j : ℕ) - 1)‖ else 0)
              * (((im - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ))
            = ∑ r ∈ range (n - k), ‖schurKernel ((θ : ℂ)) (r + 1) (k - (j : ℕ) - 1)‖
                * ((r : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
          have hsub : Finset.Ico k n ⊆ range n := fun x hx =>
            Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
          have hvan : ∀ im ∈ range n, im ∉ Finset.Ico k n →
              (if k ≤ im ∧ (j : ℕ) < k
                then ‖schurKernel ((θ : ℂ)) (im - k + 1) (k - (j : ℕ) - 1)‖ else 0)
              * (((im - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) = 0 := by
            intro im him hnot
            rw [Finset.mem_range] at him
            rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hnot
            rcases hnot with hnot | hnot
            · rw [if_neg (fun h => absurd h.1 (by omega)), zero_mul]
            · exact absurd him (by omega)
          rw [← Finset.sum_subset hsub hvan]
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [if_pos ⟨by omega, hjk⟩, show k + r - k + 1 = r + 1 from by omega]
          norm_cast
        rw [h1, h2]
        have h3 := schur_col_sum_le_of_kernel hθ hc (k - (j : ℕ) - 1)
          (fun r => by
            have h := hker (p := r + 1) (by omega) (k - (j : ℕ) - 1)
            push_cast at h ⊢
            exact h) (n - k)
        have e2 : ((k - (j : ℕ) - 1 : ℕ) : ℝ) + 1 = ((k - (j : ℕ) : ℕ) : ℝ) := by
          have h : (k - (j : ℕ) - 1) + 1 = k - (j : ℕ) := by omega
          rw [← h]
          push_cast
          ring
        rw [← e2]
        exact h3
      exact hgoal
    · -- zero columns
      have hgoal : ∑ i : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
            * ((((i : ℕ) - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)
          ≤ (c / (1 / 2 - θ) + c / (1 / 2 + θ))
            * (if (j : ℕ) < k then ((k - (j : ℕ) : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) else 1) := by
        rw [if_neg hjk]
        have hsum0 : ∑ i : Fin n, ‖lowBlock n k ((θ : ℂ)) i j‖
              * ((((i : ℕ) - k + 1 : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)
            = 0 := Finset.sum_eq_zero fun i _ => by
          rw [lowBlock_apply, if_neg (fun h => absurd h.2 hjk), norm_zero, zero_mul]
        rw [hsum0, mul_one]
        exact hC
      exact hgoal

/-- The prefix constant `6|θ|/(1-4θ²)` of Lemma A.4. -/
noncomputable def sharpPrefixConst (θ : ℝ) : ℝ := 6 * |θ| / (1 - 4 * θ ^ 2)

/-- The padded block `R̃` obeys `‖R̃‖ ≤ 6|θ|/(1-4θ²)`, via the kernel bound
`norm_schurKernel_le'` and the weighted Schur test. -/
theorem l2_opNorm_lowBlock_le' {θ : ℝ} (hθ : |θ| < 1 / 2) {n k : ℕ} (hk : k ≤ n) :
    ‖lowBlock n k ((θ : ℂ))‖ ≤ sharpPrefixConst θ := by
  obtain ⟨hθl, hθr⟩ := abs_lt.mp hθ
  have hc : (0 : ℝ) ≤ 3 / 2 * |θ| := by positivity
  have h := l2_opNorm_lowBlock_le_of_kernel hθ hc
    (fun {p} hp q => norm_schurKernel_le' hθ hp q) hk
  have heq : 3 / 2 * |θ| / (1 / 2 - θ) + 3 / 2 * |θ| / (1 / 2 + θ)
      = sharpPrefixConst θ := by
    have h1 : (0 : ℝ) < 1 / 2 - θ := by linarith
    have h2 : (0 : ℝ) < 1 / 2 + θ := by linarith
    have h3 : (1 : ℝ) - 4 * θ ^ 2 = (1 / 2 - θ) * ((1 / 2 + θ) * 4) := by ring
    rw [sharpPrefixConst, div_add_div _ _ (ne_of_gt h1) (ne_of_gt h2), h3,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  rwa [heq] at h

/-- **Lemma A.4**: the uniform prefix bound
`‖T_n(θ) Π_k T_n(-θ) - Π_k‖ ≤ 6|θ|/(1-4θ²)` for `|θ| < 1/2`, uniformly in `n` and
`k ≤ n`.  The `|θ|` factor makes the constant vanish as `θ → 0`, which is what the
multiplier bound `‖Δ_ξ‖ ≤ max|ξ| + (5α/(1-α)) Var(ξ)` needs. -/
theorem l2_opNorm_prefixConj_sub_le {θ : ℝ} (hθ : |θ| < 1 / 2) {n k : ℕ} (hk : k ≤ n) :
    ‖prefixConj n k ((θ : ℂ)) - prefixProj n k‖ ≤ sharpPrefixConst θ := by
  rw [prefixConj_eq_add hk, add_sub_cancel_left]
  exact l2_opNorm_lowBlock_le' hθ hk

end OpNorm

end InverseGenerator
