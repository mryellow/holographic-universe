import HolographicUniverse.Basic

/-!
# The 5D Schwarzschild bulk (Sec. 3)

Bulk metric `ds² = -f dt² + dr²/f + r² dΩ₃²` with `f(r) = 1 - r_h²/r²` (Eqs. (19)–(20)),
and the brane sitting at areal radius `r = a(τ)/√𝒦`.
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

/-- The brane is outside the bulk horizon iff `f > 0` there. Crossing `r = r_h` is the
moment the brane universe "leaves the white hole" (green surface of Fig. 3). -/
theorem outside_horizon_iff (hrh : 0 ≤ rh) (hK : 0 < K) (ha : 0 < a) :
    0 < blacken rh (braneRadius K a) ↔ rh < braneRadius K a := by
  have hr : 0 < braneRadius K a := div_pos ha (sqrt_pos.2 hK)
  unfold blacken
  rw [sub_pos, div_lt_one (by positivity)]
  exact sq_lt_sq₀ hrh hr.le

end WhiteHole
