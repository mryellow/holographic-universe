module

public import HolographicUniverse.Basic
public import HolographicUniverse.Integrals
public import HolographicUniverse.Zeta
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Thermal-atmosphere perturbations and late-time bounds (Secs. 4–5)

The physics inputs of Sec. 4 (thermal two-point function (39), Poisson equation, `Z₂`
identification `ζ = -Φ₄` (47), the small-`κ` value `M(0) = 15 ζ_R(5)/π²` (46)) are not derived
here. We take them as given and verify the algebra connecting them to the quoted results.
The integral `∫ dx/(1+x²)² = π/2` in Eq. (48) is proved in `Integrals.lean`, and the bounds on
`ζ(5)` that fix the numerical coefficient are proved in `Zeta.lean`.
-/

namespace WhiteHole

open Real

/-- **Eq. (48), leading order.** With `M(κ) → 15 ζ_R(5)/π²`, the first line of Eq. (48) equals
`25 ζ_R(5) / (3072 π⁴) · (T_b/M₅)⁶`. Here `z` stands for `ζ_R(5)`. The integral over the real
line is evaluated by `integral_univ_inv_one_add_sq_sq`. -/
theorem eq48_leading (c : Couplings) {M5 Tb z : ℝ} (h5 : c.IsM5 M5) :
    5 / (32 * π ^ 3) * (8 * π * c.Gb * Tb ^ 3 / 3) ^ 2 * (∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2)
        * (15 * z / π ^ 2)
      = 25 * z / (3072 * π ^ 4) * (Tb / M5) ^ 6 := by
  rw [integral_univ_inv_one_add_sq_sq]
  obtain ⟨hM5, h5⟩ := h5
  have hGb : c.Gb = 1 / (32 * π * M5 ^ 3) := by
    have := c.Gb_pos
    rw [h5]; field_simp
  rw [hGb]; field_simp; ring

/-- The numerical coefficient of the leading-order amplitude, Eq. (48): `25 ζ(5) / (3072 π⁴)`. -/
noncomputable def ampCoeff : ℝ := 25 * zeta5 / (3072 * π ^ 4)

/-- **Sharp bounds on the coefficient**: `8.6627×10⁻⁵ ≤ 25 ζ(5)/(3072 π⁴) ≤ 8.6631×10⁻⁵`
(the true value is `8.66299×10⁻⁵`). From `ζ(5) ∈ [1.0369, 1.03694]` and
`π ∈ (3.141592, 3.141593)`. -/
theorem ampCoeff_sharp : 8.6627e-5 ≤ ampCoeff ∧ ampCoeff ≤ 8.6631e-5 := by
  have hpi := pi_pos
  have hlo : (3.141592 : ℝ) ^ 4 < π ^ 4 := pow_lt_pow_left₀ pi_gt_d6 (by norm_num) (by norm_num)
  have hhi : π ^ 4 < (3.141593 : ℝ) ^ 4 := pow_lt_pow_left₀ pi_lt_d6 hpi.le (by norm_num)
  have hz1 := zeta5_lower
  have hz2 := zeta5_upper
  have hp4 : 0 < 3072 * π ^ 4 := by positivity
  unfold ampCoeff
  constructor
  · rw [le_div_iff₀ hp4]; norm_num at hlo hhi ⊢; nlinarith
  · rw [div_le_iff₀ hp4]; norm_num at hlo hhi ⊢; nlinarith

/-- **ROADMAP M1.4.** `25 ζ(5)/(3072 π⁴) ∈ [8.65, 8.67]×10⁻⁵`, the range used in Eq. (49). -/
theorem ampCoeff_bounds : 8.65e-5 ≤ ampCoeff ∧ ampCoeff ≤ 8.67e-5 :=
  ⟨le_trans (by norm_num) ampCoeff_sharp.1, ampCoeff_sharp.2.trans (by norm_num)⟩

/-- **Inverting `A = k y⁶`.** If the coefficient `k` lies in `[k_lo, k_hi]`, the amplitude lies
in `[A_lo, A_hi]`, and `y_lo⁶ k_hi ≤ A_lo` and `A_hi ≤ y_hi⁶ k_lo`, then `y ∈ [y_lo, y_hi]`.
The last two conditions are numerical checks, discharged by `norm_num` for a concrete data set. -/
theorem amplitude_inversion {y A k klo khi Alo Ahi ylo yhi : ℝ} (hy : 0 < y)
    (hA : A = k * y ^ 6) (hk : klo ≤ k ∧ k ≤ khi) (hAobs : Alo ≤ A ∧ A ≤ Ahi)
    (hklo : 0 < klo) (hyhi : 0 ≤ yhi) (hlo : ylo ^ 6 * khi ≤ Alo) (hhi : Ahi ≤ yhi ^ 6 * klo) :
    ylo ≤ y ∧ y ≤ yhi := by
  obtain ⟨hk1, hk2⟩ := hk; obtain ⟨hA1, hA2⟩ := hAobs
  have hy6 := pow_pos hy 6
  constructor
  · by_contra h; push Not at h
    have h6 : y ^ 6 < ylo ^ 6 := pow_lt_pow_left₀ h hy.le (by norm_num)
    have : k * y ^ 6 < ylo ^ 6 * khi := by nlinarith
    linarith
  · by_contra h; push Not at h
    have h6 : yhi ^ 6 < y ^ 6 := pow_lt_pow_left₀ h hyhi (by norm_num)
    have : yhi ^ 6 * klo < k * y ^ 6 := by nlinarith
    linarith

/-- **Eq. (49) for a general coefficient.** Inverting `A = k·y⁶` with the Planck 2013 amplitude
`A = (2.196 ± 0.059)×10⁻⁹` and `k ∈ [8.65, 8.67]×10⁻⁵` gives `y ∈ [0.1705, 0.1723]`. -/
theorem eq49_of_coeff {y A k : ℝ} (hy : 0 < y) (hA : A = k * y ^ 6)
    (hk : 8.65e-5 ≤ k ∧ k ≤ 8.67e-5) (hAobs : 2.137e-9 ≤ A ∧ A ≤ 2.255e-9) :
    0.1705 ≤ y ∧ y ≤ 0.1723 :=
  amplitude_inversion hy hA hk hAobs (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Eq. (51), upper bound.** The DGP constraint `r_c ≳ 3/H₀` gives `M₅³ ≤ H₀ M₄² / 6`. -/
theorem eq51 (c : Couplings) {M4 M5 H0 : ℝ} (h4 : c.IsM4 M4) (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) : M5 ^ 3 ≤ H0 * M4 ^ 2 / 6 := by
  rw [c.rc_eq_planck h4 h5, div_le_div_iff₀ hH0 (by have := h5.1; positivity)] at hrc
  linarith

/-- **Eq. (49).** If the measured amplitude is the leading-order prediction
`A = 25 ζ(5)/(3072 π⁴) · (T_b/M₅)⁶` (Eq. (48)) and lies in the Planck 2013 range
`(2.196 ± 0.059)×10⁻⁹`, then `T_b/M₅ ∈ [0.1705, 0.1723]`. This contains the paper's
`0.17139 ± 0.00077`. The coefficient is no longer a hypothesis (`ampCoeff_bounds`). -/
theorem eq49 {y A : ℝ} (hy : 0 < y) (hA : A = ampCoeff * y ^ 6)
    (hAobs : 2.137e-9 ≤ A ∧ A ≤ 2.255e-9) : 0.1705 ≤ y ∧ y ≤ 0.1723 :=
  eq49_of_coeff hy hA ampCoeff_bounds hAobs

/-- **Eq. (48) + (49) chained.** With `M(0) = 15ζ(5)/π²` the first line of Eq. (48) is
`ampCoeff · (T_b/M₅)⁶`. If that amplitude lies in the Planck 2013 range, then
`T_b/M₅ ∈ [0.1705, 0.1723]`. The only physics inputs left are the form of Eq. (48) and `M(0)`. -/
theorem eq48_eq49 (c : Couplings) {M5 Tb : ℝ} (h5 : c.IsM5 M5) (hTb : 0 < Tb)
    (hAobs : 2.137e-9 ≤ 5 / (32 * π ^ 3) * (8 * π * c.Gb * Tb ^ 3 / 3) ^ 2
        * (∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2) * (15 * zeta5 / π ^ 2) ∧
      5 / (32 * π ^ 3) * (8 * π * c.Gb * Tb ^ 3 / 3) ^ 2
        * (∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2) * (15 * zeta5 / π ^ 2) ≤ 2.255e-9) :
    0.1705 ≤ Tb / M5 ∧ Tb / M5 ≤ 0.1723 := by
  rw [eq48_leading c h5] at hAobs
  exact eq49 (div_pos hTb h5.1) rfl hAobs

end WhiteHole
