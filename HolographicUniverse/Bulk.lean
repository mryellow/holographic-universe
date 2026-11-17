import HolographicUniverse.Basic

/-!
# The 5D Schwarzschild bulk (Sec. 3)

Bulk metric `ds² = -f dt² + dr²/f + r² dΩ₃²` with `f(r) = 1 - r_h²/r²` (Eqs. (19)–(20)),
and the brane sitting at areal radius `r = a(τ)/√𝒦`.

## A general blackening factor (ROADMAP M5.1)

The embedding computation (24) uses `f` only through `𝒦 f(r)/a²` on the brane. For any
`f : ℝ → ℝ`, `rhoBulk` is the density that this term contributes to the Friedmann equation:
`𝒦 f(r)/a² = 𝒦/a² - (8π G_N/3) ρ_bulk` (`curv_mul_f`). For Schwarzschild, `ρ_bulk = ρ_BH`
(`rhoBulk_blacken`).
-/

namespace WhiteHole

open Real

/-- Blackening factor of the 5D Schwarzschild bulk, Eq. (20). -/
noncomputable def blacken (rh r : ℝ) : ℝ := 1 - rh ^ 2 / r ^ 2

/-- Areal radius of the brane in the bulk, `r = a / √𝒦`. -/
noncomputable def braneRadius (K a : ℝ) : ℝ := a / √K

/-- Curvature density parameter `Ω_k = -𝒦 / H₀²`. -/
noncomputable def omegaK (K H0 : ℝ) : ℝ := -K / H0 ^ 2

/-- Mean bulk black-hole density on the brane, Eq. (28). -/
noncomputable def rhoBH (GN K H0 rh a : ℝ) : ℝ :=
  3 * omegaK K H0 ^ 2 * H0 ^ 4 * rh ^ 2 / (8 * π * GN * a ^ 4)

/-- Integration constant identified with the bulk black-hole mass, Eq. (29). -/
noncomputable def mu (K H0 rh : ℝ) : ℝ := 3 * |omegaK K H0| * H0 ^ 2 * rh

variable {GN K H0 rh a : ℝ}

lemma rhoBH_eq (hH0 : H0 ≠ 0) :
    rhoBH GN K H0 rh a = 3 * K ^ 2 * rh ^ 2 / (8 * π * GN * a ^ 4) := by
  unfold rhoBH omegaK; field_simp

/-- `ρ_BH` scales like dark radiation, `∝ a⁻⁴`. -/
lemma rhoBH_scaling (hH0 : H0 ≠ 0) :
    rhoBH GN K H0 rh a = rhoBH GN K H0 rh 1 / a ^ 4 := by
  rw [rhoBH_eq hH0, rhoBH_eq hH0]; ring

/-- Eqs. (15) and (26) agree: `μ² / (12π G_N a⁴) = 2 ρ_BH`. -/
theorem mu_sq_term :
    mu K H0 rh ^ 2 / (12 * π * GN * a ^ 4) = 2 * rhoBH GN K H0 rh a := by
  unfold mu rhoBH
  rw [mul_pow, mul_pow, mul_pow, sq_abs]
  ring

/-- The square-root argument of Eqs. (24)–(25) is `H² + 𝒦 f(r)/a²` evaluated on the brane. -/
lemma curv_mul_blacken (hK : 0 < K) (ha : a ≠ 0) :
    K / a ^ 2 * blacken rh (braneRadius K a) = K / a ^ 2 - K ^ 2 * rh ^ 2 / a ^ 4 := by
  unfold blacken braneRadius
  rw [div_pow, sq_sqrt hK.le]
  field_simp

/-- `𝒦² r_h²/a⁴ = (8π G_N/3) ρ_BH`. -/
lemma rhoBH_term (hGN : GN ≠ 0) (hH0 : H0 ≠ 0) (ha : a ≠ 0) :
    K ^ 2 * rh ^ 2 / a ^ 4 = 8 * π * GN / 3 * rhoBH GN K H0 rh a := by
  rw [rhoBH_eq hH0]
  field_simp

/-- Density contributed by the bulk to the brane Friedmann equation, for a general blackening
factor `f` evaluated at the brane radius: `ρ_bulk = (3/(8π G_N)) (𝒦/a²) (1 - f(r))`. -/
noncomputable def rhoBulk (GN K : ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  3 / (8 * π * GN) * (K / a ^ 2) * (1 - f (braneRadius K a))

/-- The term `𝒦 f(r)/a²` of Eqs. (24)–(25), for any `f`. -/
lemma curv_mul_f (f : ℝ → ℝ) (hGN : GN ≠ 0) :
    K / a ^ 2 * f (braneRadius K a) = K / a ^ 2 - 8 * π * GN / 3 * rhoBulk GN K f a := by
  unfold rhoBulk
  field_simp
  ring

/-- **The Schwarzschild case.** For `f = 1 - r_h²/r²` the bulk density is `ρ_BH`, Eq. (28). -/
theorem rhoBulk_blacken (hGN : GN ≠ 0) (hK : 0 < K) (ha : a ≠ 0) (hH0 : H0 ≠ 0) :
    rhoBulk GN K (blacken rh) a = rhoBH GN K H0 rh a := by
  have h := curv_mul_f (blacken rh) (K := K) (a := a) hGN
  rw [curv_mul_blacken hK ha, rhoBH_term hGN hH0 ha] at h
  have hc : (8 * π * GN / 3) ≠ 0 := by positivity
  exact (mul_left_cancel₀ hc (by linarith)).symm

/-- The brane is outside the bulk horizon iff `f > 0` there. Crossing `r = r_h` is the
moment the brane universe "leaves the white hole" (green surface of Fig. 3). -/
theorem outside_horizon_iff (hrh : 0 ≤ rh) (hK : 0 < K) (ha : 0 < a) :
    0 < blacken rh (braneRadius K a) ↔ rh < braneRadius K a := by
  have hr : 0 < braneRadius K a := div_pos ha (sqrt_pos.2 hK)
  unfold blacken
  rw [sub_pos, div_lt_one (by positivity)]
  exact sq_lt_sq₀ hrh hr.le

end WhiteHole
