import HolographicUniverse.Perturbations
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The thermal integral `M(0) = 15 ζ(5)/π²` (ROADMAP M7.1)

Eq. (46) of the paper defines, for `κ ∈ ℝ⁴`,

  `M(κ) = ∫ d⁴κ'/(2π)⁴ ω₊ω₋ [1/2 + n(ω₊)][1/2 + n(ω₋)]`,
  `ω_± = √(κ'² + κ²/4 ± κ·κ')`, `n(x) = 1/(eˣ - 1)`,

with the UV-divergent vacuum term dropped. Expanding the product, the vacuum term is
`ω₊ω₋/4`, and the thermal part is `ω₊ω₋ (n₊n₋ + (n₊ + n₋)/2)` (`thermalM`). At `κ = 0` the vacuum
term is `|κ'|²/4`. Its integral has no scale, so dimensional regularization sets it to zero.
So `thermalM 0` is the paper's `M(0)`.

* `bose_add_sq`: `n + n² = eˣ/(eˣ - 1)²`.
* `hasSum_bose`: `eˣ/(eˣ - 1)² = Σ_{k ≥ 1} k e^{-kx}` for `x > 0`.
* `integral_bose`: `∫₀^∞ x⁵ eˣ/(eˣ - 1)² dx = 120 ζ(5)`. Each term gives
  `k ∫ x⁵ e^{-kx} dx = k Γ(6)/k⁶ = 120/k⁵`.
* `thermalM_zero`: **M7.1**, `M(0) = 15 ζ(5)/π²`. The integrand at `κ = 0` depends only on
  `|κ'|`. In polar coordinates on `ℝ⁴`, `d⁴κ' = 2π² y³ dy`, so
  `M(0) = (2π²/(2π)⁴) · 120 ζ(5) = 15 ζ(5)/π²`.
* `thermalM_zero_bounds`: `1.5758 ≤ M(0) ≤ 1.5761`, the paper's `1.576`.
* `eq48_leading_thermalM`: Eq. (48) at leading order with this `M(0)`, so the coefficient
  `25 ζ(5)/(3072π⁴)` no longer assumes the value of `M(0)`.

The thermal correlator (39), from which Eq. (46) follows, is still a hypothesis (M7.4). The
behavior of `M(κ)` away from `κ = 0` is M7.3.
-/

namespace WhiteHole

open Real Set MeasureTheory Filter

/-- The Bose–Einstein occupation number `n(x) = 1/(eˣ - 1)`. -/
noncomputable def bose (x : ℝ) : ℝ := 1 / (exp x - 1)

/-- `n + n² = eˣ/(eˣ - 1)²`, for `x ≠ 0`. -/
theorem bose_add_sq {x : ℝ} (hx : x ≠ 0) : bose x + bose x ^ 2 = exp x / (exp x - 1) ^ 2 := by
  have h : exp x - 1 ≠ 0 := sub_ne_zero.2 (mt (Real.exp_eq_one_iff x).1 hx)
  unfold bose
  field_simp
  ring

/-- **The Bose series.** For `x > 0`, `eˣ/(eˣ - 1)² = Σ_{k ≥ 0} (k + 1) e^{-(k+1)x}`. -/
theorem hasSum_bose {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ ↦ ((k : ℝ) + 1) * exp (-(((k : ℝ) + 1) * x)))
      (exp x / (exp x - 1) ^ 2) := by
  have hr0 : 0 < exp (-x) := exp_pos _
  have hr1 : exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  have h' := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero] at h'
  convert h' using 1
  · funext k
    push_cast
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  · have he : exp x - 1 ≠ 0 := sub_ne_zero.2 (mt (Real.exp_eq_one_iff x).1 hx.ne')
    rw [Real.exp_neg]
    have := exp_pos x
    field_simp

/-- `(k + 1) ∫₀^∞ x⁵ e^{-(k+1)x} dx = 120/(k + 1)⁵`. -/
theorem integral_bose_term (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ 5 * (((k : ℝ) + 1) * exp (-(((k : ℝ) + 1) * y)))
      = 120 / ((k : ℝ) + 1) ^ 5 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 6) (r := (k : ℝ) + 1) (by norm_num) hk
  have hG : Gamma 6 = 120 := by
    rw [show (6 : ℝ) = (5 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have e : ∫ y in Ioi (0 : ℝ), y ^ 5 * (((k : ℝ) + 1) * exp (-(((k : ℝ) + 1) * y)))
      = ((k : ℝ) + 1) * ∫ y in Ioi (0 : ℝ), y ^ ((6 : ℝ) - 1) * exp (-(((k : ℝ) + 1) * y)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    rw [show (6 : ℝ) - 1 = (5 : ℕ) by norm_num, rpow_natCast]
    ring
  rw [e, h, hG, show (1 / ((k : ℝ) + 1)) ^ (6 : ℝ) = (1 / ((k : ℝ) + 1)) ^ (6 : ℕ) by
    rw [← rpow_natCast]; norm_num]
  field_simp

/-- **The Bose–Einstein integral.** `∫₀^∞ x⁵ eˣ/(eˣ - 1)² dx = 120 ζ(5)`. -/
theorem integral_bose :
    ∫ y in Ioi (0 : ℝ), y ^ 5 * (exp y / (exp y - 1) ^ 2) = 120 * zeta5 := by
  set F : ℕ → ℝ → ℝ := fun k y ↦ y ^ 5 * (((k : ℝ) + 1) * exp (-(((k : ℝ) + 1) * y)))
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k ↦
    Integrable.of_integral_ne_zero (by
      change ∫ y in Ioi (0 : ℝ), F k y ≠ 0
      simp only [F]
      rw [integral_bose_term k]
      positivity)
  have hnorm : ∀ k, ∫ y in Ioi (0 : ℝ), ‖F k y‖ = 120 / ((k : ℝ) + 1) ^ 5 := fun k ↦ by
    rw [← integral_bose_term k]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy : (0 : ℝ) < y := hy
    exact Real.norm_of_nonneg (by simp only [F]; positivity)
  have hsum : Summable fun k ↦ ∫ y in Ioi (0 : ℝ), ‖F k y‖ := by
    simp_rw [hnorm]
    convert summable_zeta5.mul_left 120 using 1
    funext k
    ring
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have hL : ∑' k, ∫ y in Ioi (0 : ℝ), F k y = 120 * zeta5 := by
    simp only [F, integral_bose_term]
    rw [zeta5, ← tsum_mul_left]
    congr 1
    funext k
    ring
  rw [← hL, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  exact (((hasSum_bose hy).mul_left (y ^ 5)).tsum_eq).symm

/-- Momentum space `ℝ⁴` of the thermal integral. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- `ω_± = √(κ'² + κ²/4 ± κ·κ')`, with `sgn = ±1`. -/
noncomputable def omegaPM (sgn : ℝ) (κ κ' : E4) : ℝ :=
  √(‖κ'‖ ^ 2 + ‖κ‖ ^ 2 / 4 + sgn * inner ℝ κ κ')

/-- **The thermal part of `M(κ)`, Eq. (46).** The integrand is
`ω₊ω₋ (n₊n₋ + (n₊ + n₋)/2)/(2π)⁴`: the product `ω₊ω₋ [1/2 + n₊][1/2 + n₋]` without its vacuum term
`ω₊ω₋/4`. -/
noncomputable def thermalM (κ : E4) : ℝ :=
  ∫ κ' : E4, omegaPM 1 κ κ' * omegaPM (-1) κ κ'
    * (bose (omegaPM 1 κ κ') * bose (omegaPM (-1) κ κ')
      + (bose (omegaPM 1 κ κ') + bose (omegaPM (-1) κ κ')) / 2) / (2 * π) ^ 4

/-- At `κ = 0`, `ω_± = |κ'|`. -/
theorem omegaPM_zero (sgn : ℝ) (κ' : E4) : omegaPM sgn 0 κ' = ‖κ'‖ := by
  simp [omegaPM, sqrt_sq (norm_nonneg _)]

/-- The volume of the unit ball of `ℝ⁴` is `π²/2`. -/
theorem volume_ball_E4 : volume.real (Metric.ball (0 : E4) 1) = π ^ 2 / 2 := by
  rw [Measure.real, EuclideanSpace.volume_ball]
  have hG : Gamma ((Fintype.card (Fin 4) : ℝ) / 2 + 1) = 2 := by
    rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) / 2 + 1 = (2 : ℕ) + 1 by norm_num,
      Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hG, Fintype.card_fin, show √π ^ 4 = π ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_sqrt pi_pos.le]]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (by positivity)

/-- **M7.1: `M(0) = 15 ζ(5)/π²`.** In polar coordinates on `ℝ⁴`,
`M(0) = 4 · (π²/2) · ∫₀^∞ y³ · y²(n + n²)/(2π)⁴ dy = (2π²/(2π)⁴) · 120 ζ(5)`. -/
theorem thermalM_zero : thermalM 0 = 15 * zeta5 / π ^ 2 := by
  set g : ℝ → ℝ := fun y ↦ y * y * (bose y * bose y + (bose y + bose y) / 2) / (2 * π) ^ 4
  have h1 : thermalM 0 = ∫ κ' : E4, g ‖κ'‖ := by
    unfold thermalM
    simp only [omegaPM_zero, g]
  have hdim : Module.finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ E4 - 1) • g y
      = 120 * zeta5 / (2 * π) ^ 4 := by
    rw [← integral_bose, ← integral_div, hdim]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy : (0 : ℝ) < y := hy
    simp only [g, smul_eq_mul]
    rw [← bose_add_sq hy.ne']
    ring
  rw [h1, integral_fun_norm_addHaar, hrad, volume_ball_E4, hdim, nsmul_eq_mul, smul_eq_mul]
  have := pi_pos
  field_simp
  ring

/-- **The paper's value `M(0) ≈ 1.576`.** `1.5758 ≤ 15 ζ(5)/π² ≤ 1.5761`. -/
theorem thermalM_zero_bounds : 1.5758 ≤ thermalM 0 ∧ thermalM 0 ≤ 1.5761 := by
  rw [thermalM_zero]
  have hpi := pi_pos
  have hlo : (3.141592 : ℝ) ^ 2 < π ^ 2 := pow_lt_pow_left₀ pi_gt_d6 (by norm_num) (by norm_num)
  have hhi : π ^ 2 < (3.141593 : ℝ) ^ 2 := pow_lt_pow_left₀ pi_lt_d6 hpi.le (by norm_num)
  have hz1 := zeta5_lower
  have hz2 := zeta5_upper
  have hp2 : 0 < π ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hp2]; norm_num at hlo hhi ⊢; nlinarith
  · rw [div_le_iff₀ hp2]; norm_num at hlo hhi ⊢; nlinarith

/-- **Eq. (48) with `M(0)` computed.** With the thermal integral `M(0)` of Eq. (46), the first
line of Eq. (48) is `25 ζ(5)/(3072π⁴) · (T_b/M₅)⁶`. -/
theorem eq48_leading_thermalM (c : Couplings) {M5 Tb : ℝ} (h5 : c.IsM5 M5) :
    5 / (32 * π ^ 3) * (8 * π * c.Gb * Tb ^ 3 / 3) ^ 2 * (∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2)
        * thermalM 0
      = ampCoeff * (Tb / M5) ^ 6 := by
  rw [thermalM_zero, eq48_leading c h5, ampCoeff]

end WhiteHole
