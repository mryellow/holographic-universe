module

public import HolographicUniverse.AdSBulk

@[expose] public section

/-!
# A charged bulk: Reissner–Nordström₅ (ROADMAP M5.3)

For the bulk `f = 1 - r_h²/r² + q²/r⁴`, the bulk density of `rhoBulk` is `ρ_BH - ρ_Q`, with
`ρ_Q = 3𝒦³q²/(8πG_N a⁶)` (`rhoBulk_blackenRN`). The charge adds a term `∝ a⁻⁶`
(`rhoQ_mul_a6`). It has pressure `-ρ_Q` (equation of state `w = 1`, with negative density).

* **Eqs. (26) and (30)** hold with `ρ_BH` replaced by `ρ_BH - ρ_Q`. The reality bound is
  relaxed: `2(ρ_BH - ρ) ≤ ρ̃_s + 2ρ_Q` (`BulkCosmology.reality_RN`).
* **Eq. (16)** holds with `3P - ρ` replaced by `3P - ρ + 2ρ_Q` (`BulkCosmology.pressure_RN`).
* **Early times.** `ρ_Q/ρ_BH = 𝒦q²/(r_h² a²)` (`rhoQ_div_rhoBH5`). So the charge term
  dominates at small `a`, and the bulk density is negative exactly when `r_h² a² < 𝒦q²`
  (`rhoBulk_RN_neg_iff`). Any bound on extra radiation-like or stiff terms in the early
  universe, for example from BBN, bounds `q`.
* **Late times.** `ρ_bulk → 0` as `a → ∞` (`BulkCosmology.tendsto_rhoBulk_RN`), as for
  Schwarzschild.
* **No horizon above extremality.** If `r_h⁴ < 4q²`, then `f > 0` at every `r ≠ 0`
  (`blackenRN_pos`). There is no horizon and so no white hole. At the pressure singularity,
  `|H| < 1/(2r_c)` (`BulkCosmology.singularity_hubble_lt_RN`).
-/

namespace WhiteHole

open Real Filter Topology

/-- Blackening factor of the Reissner–Nordström₅ bulk, `f = 1 - r_h²/r² + q²/r⁴`. -/
noncomputable def blackenRN (rh q r : ℝ) : ℝ := 1 - rh ^ 2 / r ^ 2 + q ^ 2 / r ^ 4

/-- The density of the bulk charge on the brane, `ρ_Q = 3𝒦³q²/(8πG_N a⁶)`. -/
noncomputable def rhoQ (GN K q a : ℝ) : ℝ := 3 * K ^ 3 * q ^ 2 / (8 * π * GN * a ^ 6)

variable {GN K rh q a : ℝ}

/-- `f_RN = f_Schwarzschild + q²/r⁴`. -/
theorem blackenRN_eq (rh q r : ℝ) : blackenRN rh q r = blacken rh r + q ^ 2 / r ^ 4 := by
  unfold blackenRN blacken; ring

/-- **The charged bulk density.** For `f = 1 - r_h²/r² + q²/r⁴`, `ρ_bulk = ρ_BH - ρ_Q`. -/
theorem rhoBulk_blackenRN (hGN : 0 < GN) (hK : 0 < K) (ha : a ≠ 0) :
    rhoBulk GN K (blackenRN rh q) a = rhoBH5 GN K rh a - rhoQ GN K q a := by
  unfold rhoBulk blackenRN braneRadius rhoBH5 rhoQ
  rw [div_pow, div_pow, sq_sqrt hK.le, show √K ^ 4 = K ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_sqrt hK.le]]
  have := hGN.ne'
  have := hK.ne'
  field_simp
  ring

/-- `ρ_Q ∝ a⁻⁶`. -/
theorem rhoQ_mul_a6 (ha : a ≠ 0) : rhoQ GN K q a * a ^ 6 = rhoQ GN K q 1 := by
  unfold rhoQ
  field_simp

/-- `ρ_Q/ρ_BH = 𝒦q²/(r_h² a²)`. -/
theorem rhoQ_div_rhoBH5 (hGN : 0 < GN) (hK : 0 < K) (ha : a ≠ 0) (hrh : rh ≠ 0) :
    rhoQ GN K q a / rhoBH5 GN K rh a = K * q ^ 2 / (rh ^ 2 * a ^ 2) := by
  unfold rhoQ rhoBH5
  have := hGN.ne'
  have := hK.ne'
  field_simp

/-- **The charge dominates at small `a`.** The bulk density is negative exactly when
`r_h² a² < 𝒦q²`. -/
theorem rhoBulk_RN_neg_iff (hGN : 0 < GN) (hK : 0 < K) (ha : 0 < a) :
    rhoBulk GN K (blackenRN rh q) a < 0 ↔ rh ^ 2 * a ^ 2 < K * q ^ 2 := by
  rw [rhoBulk_blackenRN hGN hK ha.ne', sub_neg]
  unfold rhoBH5 rhoQ
  have hc : 0 < 3 * K ^ 2 / (8 * π * GN * a ^ 6) := by positivity
  rw [show 3 * K ^ 2 * rh ^ 2 / (8 * π * GN * a ^ 4)
      = 3 * K ^ 2 / (8 * π * GN * a ^ 6) * (rh ^ 2 * a ^ 2) by field_simp,
    show 3 * K ^ 3 * q ^ 2 / (8 * π * GN * a ^ 6)
      = 3 * K ^ 2 / (8 * π * GN * a ^ 6) * (K * q ^ 2) by field_simp]
  exact mul_lt_mul_iff_right₀ hc

/-- **No horizon above extremality.** If `r_h⁴ < 4q²`, then `f > 0` at every `r ≠ 0`:
`r⁴ f = (r² - r_h²/2)² + q² - r_h⁴/4`. -/
theorem blackenRN_pos (hq : rh ^ 4 < 4 * q ^ 2) {r : ℝ} (hr : r ≠ 0) : 0 < blackenRN rh q r := by
  have hr4 : 0 < r ^ 4 := by positivity
  have h : blackenRN rh q r = ((r ^ 2 - rh ^ 2 / 2) ^ 2 + (q ^ 2 - rh ^ 4 / 4)) / r ^ 4 := by
    unfold blackenRN
    field_simp
    ring
  rw [h]
  apply div_pos _ hr4
  nlinarith [sq_nonneg (r ^ 2 - rh ^ 2 / 2)]

namespace BulkCosmology

variable (M : BulkCosmology)

/-- In a charged bulk, `ρ_bulk(t) = ρ_BH(t) - ρ_Q(t)`. -/
theorem rhoBulk_RN (hf : M.f = blackenRN rh q) (t : ℝ) :
    M.rhoBulk t = rhoBH5 M.c.GN M.K rh (M.a t) - rhoQ M.c.GN M.K q (M.a t) := by
  rw [rhoBulk, hf]
  exact rhoBulk_blackenRN M.c.GN_pos M.K_pos (M.a_pos t).ne'

/-- **Eq. (30) in a charged bulk.** The reality bound is relaxed by `2ρ_Q`. -/
theorem reality_RN (hf : M.f = blackenRN rh q) (t : ℝ) :
    2 * (rhoBH5 M.c.GN M.K rh (M.a t) - M.ρ t) ≤ M.c.rhoS + 2 * rhoQ M.c.GN M.K q (M.a t) := by
  have := M.reality t
  rw [M.rhoBulk_RN hf] at this
  linarith

/-- **Eq. (16) in a charged bulk.** Away from `H = 0` and from the pressure singularity,
`P̃ = pressureTilde ρ̃_s ρ̃ (3P - ρ + 2ρ_Q)`. -/
theorem pressure_RN (hf : M.f = blackenRN rh q) (t : ℝ) (hH : deriv M.a t ≠ 0)
    (hsing : M.ρt t ≠ M.c.rhoS) :
    M.Pt t = pressureTilde M.c.rhoS (M.ρt t)
      (3 * M.P t - M.ρ t + 2 * rhoQ M.c.GN M.K q (M.a t)) := by
  have ha := M.a_pos t
  have hG := M.c.GN_pos
  set C := 3 * M.K ^ 2 * rh ^ 2 / (8 * π * M.c.GN)
  set D := 3 * M.K ^ 3 * q ^ 2 / (8 * π * M.c.GN)
  have hfun : M.rhoBulk = fun τ ↦ C / M.a τ ^ 4 - D / M.a τ ^ 6 := by
    funext τ
    rw [M.rhoBulk_RN hf]
    unfold rhoBH5 rhoQ
    simp only [C, D]
    have := (M.a_pos τ).ne'
    field_simp
  have hD : rhoQ M.c.GN M.K q (M.a t) = D / M.a t ^ 6 := by
    unfold rhoQ
    simp only [D]
    field_simp
  have hb : HasDerivAt M.rhoBulk
      ((0 * M.a t ^ 4 - C * (↑4 * M.a t ^ (4 - 1) * deriv M.a t)) / (M.a t ^ 4) ^ 2
        - (0 * M.a t ^ 6 - D * (↑6 * M.a t ^ (6 - 1) * deriv M.a t)) / (M.a t ^ 6) ^ 2) t := by
    rw [hfun]
    exact ((hasDerivAt_const t C).fun_div ((M.a_diff t).hasDerivAt.fun_pow 4)
      (pow_pos ha 4).ne').fun_sub ((hasDerivAt_const t D).fun_div
        ((M.a_diff t).hasDerivAt.fun_pow 6) (pow_pos ha 6).ne')
  rw [M.pressure t hH hsing hb (Pb := C / M.a t ^ 4 / 3 + -(D / M.a t ^ 6)) (by
    rw [hfun, H]
    field_simp
    ring)]
  have hq := M.isInduced t
  rw [hfun] at hq
  dsimp only at hq
  rw [sub_eq_add_neg] at hq
  rw [pressureTildeBulk_extra hq hsing, hD]
  ring_nf

/-- **Late times in a charged bulk.** If `a → ∞`, then `ρ_bulk → 0`. -/
theorem tendsto_rhoBulk_RN (hf : M.f = blackenRN rh q) (ha : Tendsto M.a atTop atTop) :
    Tendsto M.rhoBulk atTop (𝓝 0) := by
  have h4 := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop four_ne_zero).comp ha)).const_mul
    (3 * M.K ^ 2 * rh ^ 2 / (8 * π * M.c.GN))
  have h6 := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n := 6) (by norm_num)).comp
    ha)).const_mul (3 * M.K ^ 3 * q ^ 2 / (8 * π * M.c.GN))
  have h := h4.sub h6
  rw [mul_zero, mul_zero, sub_zero] at h
  refine h.congr fun t ↦ ?_
  rw [M.rhoBulk_RN hf]
  unfold rhoBH5 rhoQ
  simp only [Function.comp_apply]
  have := M.c.GN_pos
  have := (M.a_pos t).ne'
  field_simp

/-- **Above extremality the singularity is slow.** If `r_h⁴ < 4q²`, the bulk has no horizon,
and at the pressure singularity `|H| < 1/(2r_c)`. -/
theorem singularity_hubble_lt_RN (hf : M.f = blackenRN rh q) (hq : rh ^ 4 < 4 * q ^ 2) {t : ℝ}
    (h : M.ρt t = M.c.rhoS) : |M.H t| < 1 / (2 * M.c.rc) := by
  have hpos : 0 < M.fBrane t := by
    rw [fBrane, hf]
    exact blackenRN_pos hq (div_pos (M.a_pos t) (sqrt_pos.2 M.K_pos)).ne'
  have := (M.singularity_inside_iff h).not.1 (not_le.2 hpos)
  exact not_le.1 this

end BulkCosmology

end WhiteHole
