module

public import HolographicUniverse.ObsData

@[expose] public section

/-!
# Hubble, Planck-mass and temperature bounds, Eqs. (50)–(52) (ROADMAP M1.6)

The monopole argument of Sec. 5, as written in the TeX source (arXiv:1309.1487v2):

* Eq. (50): `H/2π ≲ T_b ≃ 0.17 M₅`. The de Sitter temperature of the brane sets a minimum for
  the atmosphere temperature `T_b`.
* Eq. (51): `H ≲ M₅ ≲ (H₀ M₄²/6)^{1/3} ∼ 9 MeV`. The first inequality is Eq. (50). The second
  is the DGP constraint `r_c ≳ 3/H₀`.
* Eq. (52): the plasma temperature from the radiation-era Friedmann equation,
  `T ≲ 3×10⁴ (g_*/100)^{-1/4} TeV ≪ T_GUT ∼ 10¹² TeV`. So the GUT transition never happens
  and no monopoles form.

This file proves the arithmetic. The physics inputs stay hypotheses:

* the condition `H ≤ 2π T_b` of Eq. (50);
* the observed values `H₀ ≤ 1.47×10⁻⁴² GeV` (Planck 2013 `h ≤ 0.689`) and
  `G_N ≥ 6.708×10⁻³⁹ GeV⁻²`;
* the radiation-era Friedmann equation `H² = (8π G_N/3)(π²/30) g_* T⁴`, and the claim that this
  `H` is the largest Hubble rate the brane has (the brane emerges at finite size).

Units: natural units, with energies in GeV. The numerical hypotheses fix this choice.

Results:

* `eq50`: `H ≤ 2π T_b` and `T_b/M₅ ≤ 0.1723` give `H < 1.09 M₅`, the first half of Eq. (51).
* `M5_cube_le`: `M₅³ ≤ H₀/(96π G_N)`, the second half of Eq. (51) in terms of `G_N`.
* `eq51_numeric`: `M₅ ≤ 9 MeV`.
* `hubble_le`: `H ≤ 9.81 MeV`.
* `radiation_T4`: `g_* T⁴ = 90 H²/(8π³ G_N)`.
* `eq52`: `T ≤ 8.5×10⁷ GeV = 8.5×10⁴ TeV` for `g_* ≥ 100`. The paper's `3×10⁴ TeV` is the same
  order of magnitude. It drops an `O(1)` factor `(180/π²)^{1/4} ≈ 2.1`.
* `eq52_below_GUT`: `T ≤ 10⁻⁷ T_GUT` for any `T_GUT ≥ 10¹⁵ GeV`.

Not in the paper, but follows from the same inputs:

* `Tb_le`, `Tb_le_planck2013`, `Tb_le_planck2018`: the atmosphere temperature `T_b ≤ 1.56 MeV`.

Eq. (52) as printed, `T ∼ (M₄ H / g_*²)^{1/4}`, has the wrong dimension (`GeV^{1/2}`). The
radiation-era Friedmann equation gives `T = (180/π²)^{1/4} (M₄ H)^{1/2} g_*^{-1/4}`. The paper's
number matches this corrected form, not the printed one.
-/

namespace WhiteHole

open Real

/-- **Eq. (50), giving the first half of Eq. (51).** If the de Sitter temperature `H/2π` is at
most `T_b`, and `T_b/M₅ ≤ 0.1723` (the upper end of `eq49`), then the Hubble rate is below the 5D
Planck mass: `H < 1.09 M₅`. -/
theorem eq50 {H Tb M5 : ℝ} (hM5 : 0 < M5) (hH : H / (2 * π) ≤ Tb) (hy : Tb / M5 ≤ 0.1723) :
    H < 1.09 * M5 := by
  rw [div_le_iff₀ (by positivity)] at hH
  rw [div_le_iff₀ hM5] at hy
  have h1 : Tb * (2 * π) ≤ 0.1723 * M5 * (2 * π) :=
    mul_le_mul_of_nonneg_right hy (by positivity)
  have h2 : 0.1723 * M5 * (2 * π) < 0.1723 * M5 * (2 * 3.15) :=
    mul_lt_mul_of_pos_left (by linarith [pi_lt_d2]) (by positivity)
  linarith

/-- **Second half of Eq. (51), without `M₄`.** `r_c ≥ 3/H₀` gives `M₅³ ≤ H₀ / (96π G_N)`. This
is `eq51` with `M₄² = 1/(16π G_N)` substituted. -/
theorem M5_cube_le (c : Couplings) {M5 H0 : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) : M5 ^ 3 ≤ H0 / (96 * π * c.GN) := by
  have hN := c.GN_pos
  have hb := c.Gb_pos
  rw [h5.2, div_le_div_iff₀ (by positivity) (by positivity)]
  unfold Couplings.rc at hrc
  rw [div_le_div_iff₀ hH0 hN] at hrc
  nlinarith [pi_pos]

/-- **Eq. (51), numerically.** With `r_c ≥ 3/H₀`, `H₀ ≤ 1.47×10⁻⁴² GeV` and
`G_N ≥ 6.708×10⁻³⁹ GeV⁻²`, the 5D Planck mass is at most `9 MeV`: `M₅ ≤ 9×10⁻³ GeV`. -/
theorem eq51_numeric (c : Couplings) {M5 H0 : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
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

/-- **`H ≤ 9.81 MeV`.** `eq50` and `eq51_numeric` together. -/
theorem hubble_le (c : Couplings) {M5 H0 H Tb : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hH : H / (2 * π) ≤ Tb) (hy : Tb / M5 ≤ 0.1723) : H ≤ 9.81e-3 := by
  have h1 := eq50 h5.1 hH hy
  have h2 := eq51_numeric c h5 hH0 hrc hH0hi hGN
  linarith

/-- **Radiation-era temperature.** If `H² = (8π G_N/3) ρ_r` with `ρ_r = (π²/30) g_* T⁴`, then
`g_* T⁴ = 90 H² / (8π³ G_N)`. -/
theorem radiation_T4 (c : Couplings) {H T g : ℝ}
    (hF : H ^ 2 = 8 * π * c.GN / 3 * (π ^ 2 / 30 * g * T ^ 4)) :
    g * T ^ 4 = 90 * H ^ 2 / (8 * π ^ 3 * c.GN) := by
  have := c.GN_pos
  rw [hF]
  field_simp
  ring

/-- **Eq. (52).** With the inputs of `hubble_le`, an expanding radiation era (`H ≥ 0`) with
`g_* ≥ 100` relativistic species has plasma temperature `T ≤ 8.5×10⁷ GeV = 8.5×10⁴ TeV`. -/
theorem eq52 (c : Couplings) {M5 H0 H Tb T g : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hH : H / (2 * π) ≤ Tb) (hy : Tb / M5 ≤ 0.1723) (hHnn : 0 ≤ H)
    (hg : 100 ≤ g) (hF : H ^ 2 = 8 * π * c.GN / 3 * (π ^ 2 / 30 * g * T ^ 4)) :
    T ≤ 8.5e7 := by
  have hHle := hubble_le c h5 hH0 hrc hH0hi hGN hH hy
  have hpi3 : (3.141592 : ℝ) ^ 3 ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) pi_gt_d6.le 3
  have hN := c.GN_pos
  have hC : (8 * 3.141592 ^ 3 * 6.708e-39 / 90 : ℝ) ≤ 8 * π ^ 3 * c.GN / 90 := by gcongr
  have hT4 : 0 ≤ T ^ 4 := by positivity
  have hEq : 8 * π ^ 3 * c.GN / 90 * (g * T ^ 4) = H ^ 2 := by rw [hF]; ring
  have hgT : 100 * T ^ 4 ≤ g * T ^ 4 := mul_le_mul_of_nonneg_right hg hT4
  have hlow : (8 * 3.141592 ^ 3 * 6.708e-39 / 90 : ℝ) * (100 * T ^ 4) ≤ H ^ 2 := by
    rw [← hEq]
    calc (8 * 3.141592 ^ 3 * 6.708e-39 / 90 : ℝ) * (100 * T ^ 4)
        ≤ 8 * π ^ 3 * c.GN / 90 * (100 * T ^ 4) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ 8 * π ^ 3 * c.GN / 90 * (g * T ^ 4) :=
          mul_le_mul_of_nonneg_left hgT (by positivity)
  have hH2 : H ^ 2 ≤ (9.81e-3 : ℝ) ^ 2 := pow_le_pow_left₀ hHnn hHle 2
  have hT4le : T ^ 4 ≤ (8.5e7 : ℝ) ^ 4 := by
    norm_num at hlow hH2 ⊢
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hT4le

/-- **No GUT monopoles.** Under the inputs of `eq52`, `T ≤ 10⁻⁷ T_GUT` for any GUT temperature
`T_GUT ≥ 10¹⁵ GeV`. -/
theorem eq52_below_GUT (c : Couplings) {M5 H0 H Tb T g TGUT : ℝ} (h5 : c.IsM5 M5)
    (hH0 : 0 < H0) (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hH : H / (2 * π) ≤ Tb) (hy : Tb / M5 ≤ 0.1723) (hHnn : 0 ≤ H)
    (hg : 100 ≤ g) (hF : H ^ 2 = 8 * π * c.GN / 3 * (π ^ 2 / 30 * g * T ^ 4))
    (hGUT : 1e15 ≤ TGUT) : T ≤ 1e-7 * TGUT := by
  have := eq52 c h5 hH0 hrc hH0hi hGN hH hy hHnn hg hF
  linarith

/-! ## The atmosphere temperature (not in the paper) -/

/-- `T_b ≤ 1.56 MeV`, from `T_b/M₅ ≤ 0.1723` (Eq. (49)) and `eq51_numeric`. -/
theorem Tb_le (c : Couplings) {M5 H0 Tb : ℝ} (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hy : Tb / M5 ≤ 0.1723) : Tb ≤ 1.56e-3 := by
  have hM := eq51_numeric c h5 hH0 hrc hH0hi hGN
  rw [div_le_iff₀ h5.1] at hy
  nlinarith

/-- `T_b ≤ 1.56 MeV` from the Planck 2013 amplitude, through `eq49_planck2013_sharp`. -/
theorem Tb_le_planck2013 (c : Couplings) {M5 H0 Tb : ℝ} (h5 : c.IsM5 M5) (hTb : 0 < Tb)
    (hH0 : 0 < H0) (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hAobs : planck2013.A_lo ≤ ampCoeff * (Tb / M5) ^ 6 ∧
      ampCoeff * (Tb / M5) ^ 6 ≤ planck2013.A_hi) :
    Tb ≤ 1.56e-3 :=
  Tb_le c h5 hH0 hrc hH0hi hGN
    ((eq49_planck2013_sharp (div_pos hTb h5.1) rfl hAobs).2.trans (by norm_num))

/-- `T_b ≤ 1.56 MeV` from the Planck 2018 amplitude. The other inputs still hold for Planck 2018
(`h = 0.6736 ± 0.0054 ≤ 0.689`). -/
theorem Tb_le_planck2018 (c : Couplings) {M5 H0 Tb : ℝ} (h5 : c.IsM5 M5) (hTb : 0 < Tb)
    (hH0 : 0 < H0) (hrc : 3 / H0 ≤ c.rc) (hH0hi : H0 ≤ 1.47e-42) (hGN : 6.708e-39 ≤ c.GN)
    (hAobs : planck2018.A_lo ≤ ampCoeff * (Tb / M5) ^ 6 ∧
      ampCoeff * (Tb / M5) ^ 6 ≤ planck2018.A_hi) :
    Tb ≤ 1.56e-3 :=
  Tb_le c h5 hH0 hrc hH0hi hGN
    ((eq49_planck2018 (div_pos hTb h5.1) rfl hAobs).2.trans (by norm_num))

end WhiteHole
