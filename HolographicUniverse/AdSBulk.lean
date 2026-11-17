import HolographicUniverse.GeneralBulk
import HolographicUniverse.Asymptotics

/-!
# A Schwarzschild–AdS₅ bulk (ROADMAP M5.2)

Sec. 5 of the paper says that with an AdS₅ bulk, `f = 1 + r²/L² - r_h²/r²`, the results "need
not significantly change". This file states exactly how they change. The bulk density of
`rhoBulk` becomes `ρ_BH - ρ_Λ`, with the constant `ρ_Λ = 3/(8πG_N L²)` (`rhoBulk_blackenAdS`).
The constant part is a vacuum term with pressure `+ρ_Λ`.

* **Eqs. (26) and (30)** hold with `ρ_BH` replaced by `ρ_BH - ρ_Λ`. The reality bound is
  relaxed: `2(ρ_BH - ρ) ≤ ρ̃_s + 2ρ_Λ` (`BulkCosmology.reality_AdS`).
* **Eq. (16)** holds with `3P - ρ` replaced by `3P - ρ - 4ρ_Λ` (`pressureTildeBulk_AdS`,
  `BulkCosmology.pressure_AdS`).
* **The horizon results** of `GeneralBulk.lean` hold for every `f`, so README issue 7 is
  unchanged. The AdS horizon is inside the Schwarzschild one: `f_AdS = f + r²/L²`
  (`blackenAdS_eq`).
* **Late times change.** If `a → ∞` and `ρ → 0`, then
  `ρ̃ → ρ̃_s(1 + sgn √(1 + 4r_c²/L²))` (`BulkCosmology.tendsto_rhoTilde_AdS`,
  `two_rhoLam_div_rhoS`). On the self-accelerating branch,
  `H² → (1 + √(1 + 4r_c²/L²))/(2r_c²)` (`BulkCosmology.tendsto_hubble_sq_AdS`). This is
  more than `1/r_c²`, by a relative amount of order `r_c²/L²`. On the normal branch the limit of
  `ρ̃` is negative, so the brane has a negative cosmological constant. Then the brane cannot
  expand forever: no normal-branch history with `ρ → 0` has `a → ∞`
  (`BulkCosmology.not_tendsto_atTop_normal_AdS`). This is a qualitative change for every finite
  `L`.

So the paper's statement holds for the early-time relations when `ρ_Λ ≪ ρ`, and for the
self-accelerating late-time rate when `L ≫ r_c`. It does not hold for the normal branch at late
times.
-/

namespace WhiteHole

open Real Filter Topology

/-- Blackening factor of the Schwarzschild–AdS₅ bulk, `f = 1 + r²/L² - r_h²/r²`. -/
noncomputable def blackenAdS (L rh r : ℝ) : ℝ := 1 + r ^ 2 / L ^ 2 - rh ^ 2 / r ^ 2

/-- The density of the AdS curvature on the brane, `ρ_Λ = 3/(8πG_N L²)`. -/
noncomputable def rhoLam (GN L : ℝ) : ℝ := 3 / (8 * π * GN * L ^ 2)

/-- The black-hole density `3𝒦²r_h²/(8πG_N a⁴)` of Eq. (28), without the parameter `H₀`. -/
noncomputable def rhoBH5 (GN K rh a : ℝ) : ℝ := 3 * K ^ 2 * rh ^ 2 / (8 * π * GN * a ^ 4)

variable {GN K L rh a : ℝ}

/-- `f_AdS = f_Schwarzschild + r²/L²`. -/
theorem blackenAdS_eq (L rh r : ℝ) : blackenAdS L rh r = blacken rh r + r ^ 2 / L ^ 2 := by
  unfold blackenAdS blacken; ring

/-- `rhoBH5` is `ρ_BH` of Eq. (28). -/
theorem rhoBH5_eq {H0 : ℝ} (hH0 : H0 ≠ 0) : rhoBH5 GN K rh a = rhoBH GN K H0 rh a :=
  (rhoBH_eq hH0).symm

/-- **The AdS bulk density.** For `f = 1 + r²/L² - r_h²/r²`, `ρ_bulk = ρ_BH - ρ_Λ`. -/
theorem rhoBulk_blackenAdS (hGN : 0 < GN) (hK : 0 < K) (ha : a ≠ 0) (hL : L ≠ 0) :
    rhoBulk GN K (blackenAdS L rh) a = rhoBH5 GN K rh a - rhoLam GN L := by
  unfold rhoBulk blackenAdS braneRadius rhoBH5 rhoLam
  rw [div_pow, sq_sqrt hK.le]
  have := hGN.ne'
  field_simp
  ring

/-- `2ρ_Λ/ρ̃_s = 4r_c²/L²`. -/
theorem two_rhoLam_div_rhoS (c : Couplings) (L : ℝ) :
    2 * rhoLam c.GN L / c.rhoS = 4 * c.rc ^ 2 / L ^ 2 := by
  unfold rhoLam Couplings.rhoS Couplings.rc
  have := c.GN_pos
  have := c.Gb_pos
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  field_simp
  ring

/-- **Eq. (16) with an extra bulk component.** Let the bulk density be `b + d`, where `b` has
the pressure `b/3` of `ρ_BH` and `d` has pressure `p`. If `ρ̃` solves the quadratic (26) with
bulk density `b + d`, then the general form of Eq. (16) is Eq. (16) with `T = 3P - ρ` replaced
by `T + d - 3p`. -/
theorem pressureTildeBulk_extra {s b d p ρ ρt P : ℝ} (hq : IsInduced s (b + d) ρ ρt)
    (hsing : ρt ≠ s) :
    pressureTildeBulk s ρt (P - (b / 3 + p)) = pressureTilde s ρt (3 * P - ρ + d - 3 * p) := by
  unfold IsInduced at hq
  have hne : s - ρt ≠ 0 := sub_ne_zero.2 (Ne.symm hsing)
  unfold pressureTildeBulk pressureTilde
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero hne) (mul_ne_zero three_ne_zero hne)]
  linear_combination (s - ρt) * hq

/-- **Eq. (16) in an AdS bulk, algebraic form.** The case `d = -λ`, `p = λ` of
`pressureTildeBulk_extra`: `T` is replaced by `T - 4λ`. -/
theorem pressureTildeBulk_AdS {s b l ρ ρt P : ℝ} (hq : IsInduced s (b - l) ρ ρt)
    (hsing : ρt ≠ s) :
    pressureTildeBulk s ρt (P - (b / 3 + l)) = pressureTilde s ρt (3 * P - ρ - 4 * l) := by
  rw [sub_eq_add_neg] at hq
  rw [pressureTildeBulk_extra hq hsing]
  ring_nf

namespace BulkCosmology

variable (M : BulkCosmology)

/-- In an AdS bulk, `ρ_bulk(t) = ρ_BH(t) - ρ_Λ`. -/
theorem rhoBulk_AdS (hf : M.f = blackenAdS L rh) (hL : L ≠ 0) (t : ℝ) :
    M.rhoBulk t = rhoBH5 M.c.GN M.K rh (M.a t) - rhoLam M.c.GN L := by
  rw [rhoBulk, hf]
  exact rhoBulk_blackenAdS M.c.GN_pos M.K_pos (M.a_pos t).ne' hL

/-- **Eq. (30) in an AdS bulk.** The reality bound is relaxed by `2ρ_Λ`. -/
theorem reality_AdS (hf : M.f = blackenAdS L rh) (hL : L ≠ 0) (t : ℝ) :
    2 * (rhoBH5 M.c.GN M.K rh (M.a t) - M.ρ t) ≤ M.c.rhoS + 2 * rhoLam M.c.GN L := by
  have := M.reality t
  rw [M.rhoBulk_AdS hf hL] at this
  linarith

/-- **Eq. (16) in an AdS bulk.** Away from `H = 0` and from the pressure singularity,
`P̃ = pressureTilde ρ̃_s ρ̃ (3P - ρ - 4ρ_Λ)`. -/
theorem pressure_AdS (hf : M.f = blackenAdS L rh) (hL : L ≠ 0) (t : ℝ)
    (hH : deriv M.a t ≠ 0) (hsing : M.ρt t ≠ M.c.rhoS) :
    M.Pt t = pressureTilde M.c.rhoS (M.ρt t) (3 * M.P t - M.ρ t - 4 * rhoLam M.c.GN L) := by
  have ha := M.a_pos t
  set C := 3 * M.K ^ 2 * rh ^ 2 / (8 * π * M.c.GN)
  have hC : ∀ τ, rhoBH5 M.c.GN M.K rh (M.a τ) = C / M.a τ ^ 4 := fun τ ↦ by
    unfold rhoBH5
    simp only [C]
    have := M.c.GN_pos
    have := (M.a_pos τ).ne'
    field_simp
  have hfun : M.rhoBulk = fun τ ↦ C / M.a τ ^ 4 - rhoLam M.c.GN L := by
    funext τ
    rw [M.rhoBulk_AdS hf hL, hC]
  have hb : HasDerivAt M.rhoBulk ((0 * M.a t ^ 4 - C * (↑4 * M.a t ^ (4 - 1) * deriv M.a t))
      / (M.a t ^ 4) ^ 2) t := by
    rw [hfun]
    exact ((hasDerivAt_const t C).fun_div ((M.a_diff t).hasDerivAt.fun_pow 4)
      (pow_pos ha 4).ne').sub_const _
  rw [M.pressure t hH hsing hb (Pb := C / M.a t ^ 4 / 3 + rhoLam M.c.GN L) (by
    rw [hfun, H]
    field_simp
    ring)]
  have hq := M.isInduced t
  rw [hfun] at hq
  exact pressureTildeBulk_AdS hq hsing

/-- **Late times in an AdS bulk.** If `a → ∞` and `ρ → 0` on the branch `sgn`, then
`ρ̃ → ρ̃_s(1 + sgn √(1 + 2ρ_Λ/ρ̃_s))`. -/
theorem tendsto_rhoTilde_AdS {sgn : ℝ} (hf : M.f = blackenAdS L rh) (hL : L ≠ 0)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBulk t) (M.ρ t))
    (ha : Tendsto M.a atTop atTop) (hρ : Tendsto M.ρ atTop (𝓝 0)) :
    Tendsto M.ρt atTop
      (𝓝 (M.c.rhoS * (1 + sgn * √(1 + 2 * rhoLam M.c.GN L / M.c.rhoS)))) := by
  have hb : Tendsto M.rhoBulk atTop (𝓝 (-rhoLam M.c.GN L)) := by
    have h4 := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop four_ne_zero).comp ha)).const_mul
      (3 * M.K ^ 2 * rh ^ 2 / (8 * π * M.c.GN))
    have h := h4.sub_const (rhoLam M.c.GN L)
    rw [mul_zero, zero_sub] at h
    refine h.congr fun t ↦ ?_
    rw [M.rhoBulk_AdS hf hL]
    unfold rhoBH5
    simp only [Function.comp_apply]
    have := M.c.GN_pos
    have := (M.a_pos t).ne'
    field_simp
  have h : Tendsto (fun t ↦ rhoTilde sgn M.c.rhoS (M.rhoBulk t) (M.ρ t)) atTop
      (𝓝 (rhoTilde sgn M.c.rhoS (-rhoLam M.c.GN L) 0)) := by
    unfold rhoTilde
    exact tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hb.sub hρ)).div_const _)).sqrt))
  convert h.congr fun t ↦ (hbr t).symm using 2
  unfold rhoTilde
  rw [sub_zero, mul_neg, neg_div, sub_neg_eq_add]

/-- **The late-time Hubble rate in an AdS bulk.** If `a → ∞` and `ρ → 0` on the branch `sgn`,
then `H² → (1 + sgn √(1 + 4r_c²/L²))/(2r_c²)`. For `sgn = 1` this exceeds `1/r_c²`. -/
theorem tendsto_hubble_sq_AdS {sgn : ℝ} (hf : M.f = blackenAdS L rh) (hL : L ≠ 0)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBulk t) (M.ρ t))
    (ha : Tendsto M.a atTop atTop) (hρ : Tendsto M.ρ atTop (𝓝 0)) :
    Tendsto (fun t ↦ M.H t ^ 2) atTop
      (𝓝 ((1 + sgn * √(1 + 4 * M.c.rc ^ 2 / L ^ 2)) / (2 * M.c.rc ^ 2))) := by
  have hρt := M.tendsto_rhoTilde_AdS hf hL hbr ha hρ
  rw [two_rhoLam_div_rhoS] at hρt
  have hK : Tendsto (fun t ↦ M.K / M.a t ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp ha)).const_mul
      M.K
    rw [mul_zero] at h
    exact h.congr fun t ↦ by simp [div_eq_mul_inv]
  have h := ((hρ.add hρt).const_mul (8 * π * M.c.GN / 3)).sub hK
  rw [zero_add, sub_zero, ← mul_assoc, M.c.gN_mul_rhoS] at h
  convert h.congr (fun t ↦ ?_) using 2
  · have := M.c.rc_pos
    field_simp
  · have := M.friedmann t
    unfold H
    linarith

/-- On the normal branch of an AdS bulk, the late-time induced density is negative:
`ρ̃_s(1 - √(1 + 2ρ_Λ/ρ̃_s)) < 0`. -/
theorem normal_limit_neg (hL : L ≠ 0) :
    M.c.rhoS * (1 + -1 * √(1 + 2 * rhoLam M.c.GN L / M.c.rhoS)) < 0 := by
  have hs := M.c.rhoS_pos
  have hl : 0 < rhoLam M.c.GN L := by
    unfold rhoLam
    have := M.c.GN_pos
    positivity
  have h1 : 1 < √(1 + 2 * rhoLam M.c.GN L / M.c.rhoS) := by
    rw [lt_sqrt zero_le_one]
    have : 0 < 2 * rhoLam M.c.GN L / M.c.rhoS := by positivity
    linarith
  nlinarith

/-- **M5.2: the AdS bulk changes the normal branch at late times.** On the normal branch of a
Schwarzschild–AdS₅ bulk, no history with `ρ → 0` has `a → ∞`. The limit of `ρ̃` would be
negative, and then `H² + 𝒦/a² = (8πG_N/3)(ρ + ρ̃)` would be negative at late times. -/
theorem not_tendsto_atTop_normal_AdS (hf : M.f = blackenAdS L rh) (hL : L ≠ 0)
    (hbr : ∀ t, M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBulk t) (M.ρ t))
    (hρ : Tendsto M.ρ atTop (𝓝 0)) : ¬ Tendsto M.a atTop atTop := by
  intro ha
  have hρt := M.tendsto_rhoTilde_AdS hf hL hbr ha hρ
  have h := (hρ.add hρt).const_mul (8 * π * M.c.GN / 3)
  rw [zero_add] at h
  have hnn : ∀ t, 0 ≤ 8 * π * M.c.GN / 3 * (M.ρ t + M.ρt t) := fun t ↦ by
    rw [← M.friedmann t]
    have := M.K_pos
    have := M.a_pos t
    positivity
  have hle := ge_of_tendsto' h hnn
  have hneg := M.normal_limit_neg hL
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  nlinarith

end BulkCosmology

end WhiteHole
