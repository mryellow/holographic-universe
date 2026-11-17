import HolographicUniverse.Basic
import HolographicUniverse.Integrals

/-!
# Thermal-atmosphere perturbations and late-time bounds (Secs. 4–5)

The physics inputs of Sec. 4 (thermal two-point function (39), Poisson equation, `Z₂`
identification `ζ = -Φ₄` (47), the small-`κ` value `M(0) = 15 ζ_R(5)/π²` (46)) are not derived
here. We take them as given and verify the algebra connecting them to the quoted results.
The integral `∫ dx/(1+x²)² = π/2` in Eq. (48) is proved in `Integrals.lean`.
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

/-- **Eq. (49).** Inverting the leading-order amplitude `A = c·(T_b/M₅)⁶` with the Planck
amplitude `A = (2.196 ± 0.059)×10⁻⁹` and `c ∈ [8.65, 8.67]×10⁻⁵` (Eq. (48)) gives
`T_b/M₅ ∈ [0.1705, 0.1723]`, which contains the paper's `0.17139 ± 0.00077`. -/
theorem eq49 {y A k : ℝ} (hy : 0 < y) (hA : A = k * y ^ 6)
    (hk : 8.65e-5 ≤ k ∧ k ≤ 8.67e-5) (hAobs : 2.137e-9 ≤ A ∧ A ≤ 2.255e-9) :
    0.1705 ≤ y ∧ y ≤ 0.1723 := by
  obtain ⟨hk1, hk2⟩ := hk; obtain ⟨hA1, hA2⟩ := hAobs
  constructor
  · by_contra h; push Not at h
    have : y ^ 6 < 0.1705 ^ 6 := pow_lt_pow_left₀ h hy.le (by norm_num)
    nlinarith [pow_pos hy 6]
  · by_contra h; push Not at h
    have : 0.1723 ^ 6 < y ^ 6 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    nlinarith [pow_pos hy 6]

/-- **Eq. (51), upper bound.** The DGP constraint `r_c ≳ 3/H₀` gives `M₅³ ≤ H₀ M₄² / 6`. -/
theorem eq51 (c : Couplings) {M4 M5 H0 : ℝ} (h4 : c.IsM4 M4) (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) : M5 ^ 3 ≤ H0 * M4 ^ 2 / 6 := by
  rw [c.rc_eq_planck h4 h5, div_le_div_iff₀ hH0 (by have := h5.1; positivity)] at hrc
  linarith

end WhiteHole
