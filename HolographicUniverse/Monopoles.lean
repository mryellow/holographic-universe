import HolographicUniverse.ObsData

/-!
# Temperature and monopole bounds, Eqs. (50) and (52) (ROADMAP M1.6)

Sec. 5 of the paper combines three facts:

* Eq. (49): `T_b ≃ 0.17 M₅`.
* Eq. (50): `H/2π ≲ T_b`, i.e. the thermal fluctuations of the atmosphere dominate the de Sitter
  (Gibbons–Hawking) fluctuations.
* Eq. (51)–(52): the DGP constraint `r_c ≳ 3/H₀` gives `M₅ ≲ 9 MeV`.

So the temperature of the brane never comes near the GUT scale, and no GUT monopoles form.

This file proves the arithmetic in that argument. The physics inputs stay hypotheses:

* the condition `H ≤ 2π T_b` of Eq. (50);
* the observed values `H₀ ≤ 1.47×10⁻⁴² GeV` (Planck 2013 `h ≤ 0.689`) and
  `G_N ≥ 6.708×10⁻³⁹ GeV⁻²`;
* the claim that `T_b` is the highest temperature the brane reaches (not formalized).

Units: natural units, with energies in GeV. The numerical hypotheses fix this choice.

Results:

* `eq50`: `H ≤ 2π T_b` and `T_b/M₅ ≤ 0.1723` give `H < 1.09 M₅`.
* `M5_cube_le`: Eq. (51) in terms of `G_N`, `M₅³ ≤ H₀ / (96π G_N)`. It does not need `M₄`.
* `eq52`: `M₅ ≤ 9 MeV`.
* `eq52_temperature`: `T_b ≤ 1.56 MeV`.
* `eq52_planck2013`, `eq52_planck2018`: the chain from the measured amplitude to `T_b ≤ 1.56 MeV`.
* `eq52_below_GUT`: for any `T_GUT ≥ 10¹⁵ GeV`, `T_b ≤ 1.6×10⁻¹⁸ T_GUT`.
-/

namespace WhiteHole

open Real

/-- **Eq. (50).** If the de Sitter temperature `H/2π` is at most `T_b`, and `T_b/M₅ ≤ 0.1723`
(the upper end of `eq49`), then the Hubble rate is below the 5D Planck mass: `H < 1.09 M₅`. -/
theorem eq50 {H Tb M5 : ℝ} (hM5 : 0 < M5) (hH : H / (2 * π) ≤ Tb) (hy : Tb / M5 ≤ 0.1723) :
    H < 1.09 * M5 := by
  rw [div_le_iff₀ (by positivity)] at hH
  rw [div_le_iff₀ hM5] at hy
  have h1 : Tb * (2 * π) ≤ 0.1723 * M5 * (2 * π) :=
    mul_le_mul_of_nonneg_right hy (by positivity)
  have h2 : 0.1723 * M5 * (2 * π) < 0.1723 * M5 * (2 * 3.15) :=
    mul_lt_mul_of_pos_left (by linarith [pi_lt_d2]) (by positivity)
  linarith

/-- **Eq. (51) without `M₄`.** `r_c ≥ 3/H₀` gives `M₅³ ≤ H₀ / (96π G_N)`. This is `eq51` with
`M₄² = 1/(16π G_N)` substituted. -/
theorem M5_cube_le (c : Couplings) {M5 H0 : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) : M5 ^ 3 ≤ H0 / (96 * π * c.GN) := by
  have hN := c.GN_pos
  have hb := c.Gb_pos
  rw [h5.2, div_le_div_iff₀ (by positivity) (by positivity)]
  unfold Couplings.rc at hrc
  rw [div_le_div_iff₀ hH0 hN] at hrc
  nlinarith [pi_pos]

/-- **Eq. (52).** With `r_c ≥ 3/H₀`, `H₀ ≤ 1.47×10⁻⁴² GeV` and `G_N ≥ 6.708×10⁻³⁹ GeV⁻²`, the 5D
Planck mass is at most `9 MeV`: `M₅ ≤ 9×10⁻³ GeV`. -/
theorem eq52 (c : Couplings) {M5 H0 : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN) :
    M5 ≤ 9e-3 := by
  have h := M5_cube_le c h5 hH0 hrc
  have hpi := pi_gt_d6
  have hden : (0 : ℝ) < 96 * π * c.GN := by have := c.GN_pos; positivity
  have hcube : M5 ^ 3 ≤ (9e-3 : ℝ) ^ 3 := by
    refine h.trans ?_
    rw [div_le_iff₀ hden]
    have : (96 * 3.141592 * 6.708e-39 : ℝ) ≤ 96 * π * c.GN := by
      have := c.GN_pos
      gcongr
    norm_num at this ⊢
    nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hcube

/-- **Eq. (52), temperature.** With `T_b/M₅ ≤ 0.1723` (Eq. (49)) and the inputs of `eq52`, the
brane temperature is at most `1.56 MeV`. -/
theorem eq52_temperature (c : Couplings) {M5 H0 Tb : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hy : Tb / M5 ≤ 0.1723) : Tb ≤ 1.56e-3 := by
  have hM := eq52 c h5 hH0 hrc hH0hi hGN
  rw [div_le_iff₀ h5.1] at hy
  nlinarith

/-- **No GUT monopoles.** Under the inputs of `eq52_temperature`, `T_b/T_GUT ≤ 1.6×10⁻¹⁸` for any
GUT temperature `T_GUT ≥ 10¹⁵ GeV`. That `T_b` is the highest
temperature the brane reaches is a physics claim of the paper, not proved here. -/
theorem eq52_below_GUT (c : Couplings) {M5 H0 Tb TGUT : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hy : Tb / M5 ≤ 0.1723) (hGUT : 1e15 ≤ TGUT) : Tb ≤ 1.6e-18 * TGUT := by
  have := eq52_temperature c h5 hH0 hrc hH0hi hGN hy
  linarith

/-- **Eqs. (48)–(52) chained, Planck 2013.** If the leading-order amplitude lies in the Planck
2013 interval, then `T_b ≤ 1.56 MeV`. The bound on `T_b/M₅` comes from `eq49_planck2013_sharp`. -/
theorem eq52_planck2013 (c : Couplings) {M5 H0 Tb : ℝ} (h5 : c.IsM5 M5) (hTb : 0 < Tb)
    (hH0 : 0 < H0) (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hAobs : planck2013.A_lo ≤ ampCoeff * (Tb / M5) ^ 6 ∧
      ampCoeff * (Tb / M5) ^ 6 ≤ planck2013.A_hi) :
    Tb ≤ 1.56e-3 :=
  eq52_temperature c h5 hH0 hrc hH0hi hGN
    ((eq49_planck2013_sharp (div_pos hTb h5.1) rfl hAobs).2.trans (by norm_num))

/-- **Eqs. (48)–(52) chained, Planck 2018.** The same bound with the Planck 2018 amplitude. The
inputs of `eq52` still hold for Planck 2018 (`h = 0.6736 ± 0.0054 ≤ 0.689`). -/
theorem eq52_planck2018 (c : Couplings) {M5 H0 Tb : ℝ} (h5 : c.IsM5 M5) (hTb : 0 < Tb)
    (hH0 : 0 < H0) (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hAobs : planck2018.A_lo ≤ ampCoeff * (Tb / M5) ^ 6 ∧
      ampCoeff * (Tb / M5) ^ 6 ≤ planck2018.A_hi) :
    Tb ≤ 1.56e-3 :=
  eq52_temperature c h5 hH0 hrc hH0hi hGN
    ((eq49_planck2018 (div_pos hTb h5.1) rfl hAobs).2.trans (by norm_num))

end WhiteHole
