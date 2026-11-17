import HolographicUniverse.Instances
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# An expanding instance with a bulk black hole and radiation (ROADMAP M2.2)

`Instances.lean` has a static family and the de Sitter vacuum (`r_h = 0`, no matter). This file
builds an instance with a bulk black hole (`r_h > 0`), radiation (`P = ρ/3`, `ρ > 0`), and a
non-static scale factor. It is a solution of the full equations of motion: it also obeys the
acceleration equation at every time (`radiationBounce_accelAt`), the bounce included.

**The closed form.** Take radiation with exactly the black-hole density, `ρ = ρ_BH`. Both scale
as `a⁻⁴`, so the reality bound (30) is `0 ≤ ρ̃_s` at all times, and the self-accelerating branch
is constant, `ρ̃_+ = 2ρ̃_s`. The Friedmann equation becomes

    ȧ² = 𝒦²r_h²/a² + a²/r_c² - 𝒦.

With `u = a²` this is `u̇² = 4(u²/r_c² - 𝒦u + 𝒦²r_h²)`. If `2 r_h ≤ r_c`, it has the solution

    a(t)² = 𝒦 r_c²/2 + q cosh(2t/r_c),   q = 𝒦 r_c √(r_c²/4 - r_h²),

which is positive for all `t`. At `r_h = 0` and `𝒦 = 1` it is `a = r_c cosh(t/r_c)`, the de
Sitter vacuum.

* `radiationBounce`: the instance, for every coupling, every `𝒦 > 0` and every `r_h` with
  `0 ≤ r_h` and `2 r_h ≤ r_c`. Orientation `ε = -1`, `ρ̃ = -P̃ = 2ρ̃_s`.
* `radiationBounce_selfAccelerating`: `ρ̃` is on the branch `ρ̃_+` of Eq. (26).
* `radiationBounce_pressure`: Eq. (16) holds at every time, the bounce included.
* `radiationBounce_accelAt`: the acceleration equation holds at every time.
* `radiationBounce_H_pos`: if `2 r_h < r_c`, the brane expands at every `t > 0`.
* `radiationBounce_outside`: the brane is outside the horizon at every time.
* `exists_expanding_radiation`: the M2.2 statement, with `r_h > 0`.

**Limits.** The instance needs the fine tuning `ρ = ρ_BH`. It is on the self-accelerating branch
and stays outside the horizon, so it is a black-hole history, not the paper's white-hole
history. On the normal branch with `ε = -1` there is no solution for ordinary matter (M2.3,
`NormalBranch.lean`).
-/

namespace WhiteHole

open Real

section Closed

variable {K r rh : ℝ}

/-- The amplitude `q = 𝒦 r √(r²/4 - r_h²)` of the bounce. -/
noncomputable def bounceQ (K r rh : ℝ) : ℝ := K * r * √(r ^ 2 / 4 - rh ^ 2)

/-- The square of the scale factor, `a² = 𝒦 r²/2 + q cosh(2t/r)`. -/
noncomputable def bounceU (K r rh t : ℝ) : ℝ := K * r ^ 2 / 2 + bounceQ K r rh * cosh (2 * t / r)

/-- The scale factor of the bounce. -/
noncomputable def bounceA (K r rh t : ℝ) : ℝ := √(bounceU K r rh t)

lemma bounceQ_nonneg (hK : 0 < K) (hr : 0 < r) : 0 ≤ bounceQ K r rh := by
  unfold bounceQ; positivity

lemma bounceQ_sq (hrh : 0 ≤ rh) (hr : 2 * rh ≤ r) :
    bounceQ K r rh ^ 2 = K ^ 2 * r ^ 2 * (r ^ 2 / 4 - rh ^ 2) := by
  unfold bounceQ
  rw [mul_pow, mul_pow, sq_sqrt (by nlinarith)]

lemma bounceU_pos (hK : 0 < K) (hr : 0 < r) (t : ℝ) : 0 < bounceU K r rh t := by
  have := bounceQ_nonneg (rh := rh) hK hr
  have := cosh_pos (2 * t / r)
  unfold bounceU; positivity

lemma bounceA_pos (hK : 0 < K) (hr : 0 < r) (t : ℝ) : 0 < bounceA K r rh t :=
  sqrt_pos.2 (bounceU_pos hK hr t)

lemma bounceA_sq (hK : 0 < K) (hr : 0 < r) (t : ℝ) : bounceA K r rh t ^ 2 = bounceU K r rh t :=
  sq_sqrt (bounceU_pos hK hr t).le

lemma hasDerivAt_bounceU (t : ℝ) :
    HasDerivAt (bounceU K r rh) (2 * bounceQ K r rh / r * sinh (2 * t / r)) t := by
  have h := (((hasDerivAt_cosh (2 * t / r)).comp t
    (((hasDerivAt_id t).const_mul 2).div_const r)).const_mul (bounceQ K r rh)).const_add
    (K * r ^ 2 / 2)
  exact h.congr_deriv (by ring)

lemma hasDerivAt_bounceA (hK : 0 < K) (hr : 0 < r) (t : ℝ) :
    HasDerivAt (bounceA K r rh)
      (bounceQ K r rh * sinh (2 * t / r) / (r * bounceA K r rh t)) t := by
  have h := (hasDerivAt_bounceU (rh := rh) (K := K) (r := r) t).sqrt (bounceU_pos hK hr t).ne'
  have hA := bounceA_pos (rh := rh) hK hr t
  refine h.congr_deriv ?_
  unfold bounceA at hA ⊢
  field_simp

lemma deriv_bounceA (hK : 0 < K) (hr : 0 < r) :
    deriv (bounceA K r rh)
      = fun t ↦ bounceQ K r rh * sinh (2 * t / r) / (r * bounceA K r rh t) :=
  funext fun t ↦ (hasDerivAt_bounceA hK hr t).deriv

/-- **The Friedmann equation of the bounce**, multiplied by `a²`:
`ȧ² + 𝒦 = 𝒦²r_h²/a² + a²/r²`. -/
lemma bounce_friedmann (hK : 0 < K) (hr : 0 < r) (hrh : 0 ≤ rh) (hrr : 2 * rh ≤ r) (t : ℝ) :
    deriv (bounceA K r rh) t ^ 2 + K
      = K ^ 2 * rh ^ 2 / bounceA K r rh t ^ 2 + bounceA K r rh t ^ 2 / r ^ 2 := by
  have hA := bounceA_pos (rh := rh) hK hr t
  have hA2 := bounceA_sq (rh := rh) hK hr t
  have hq := bounceQ_sq (K := K) hrh hrr
  have hc := cosh_sq (2 * t / r)
  rw [deriv_bounceA hK hr, div_pow, mul_pow]
  field_simp
  unfold bounceU at hA2
  linear_combination (r ^ 2 * K - bounceA K r rh t ^ 2 - (K * r ^ 2 / 2
    + bounceQ K r rh * cosh (2 * t / r))) * hA2 - bounceQ K r rh ^ 2 * hc - hq

/-- **The acceleration equation of the bounce:** `ä = -𝒦²r_h²/a³ + a/r²`, at every time. -/
lemma bounce_accel (hK : 0 < K) (hr : 0 < r) (hrh : 0 ≤ rh) (hrr : 2 * rh ≤ r) (t : ℝ) :
    HasDerivAt (deriv (bounceA K r rh))
      (-(K ^ 2 * rh ^ 2) / bounceA K r rh t ^ 3 + bounceA K r rh t / r ^ 2) t := by
  rw [deriv_bounceA hK hr]
  have hA := bounceA_pos (rh := rh) hK hr t
  have hA2 := bounceA_sq (rh := rh) hK hr t
  have hq := bounceQ_sq (K := K) hrh hrr
  have hc := cosh_sq (2 * t / r)
  have hN := ((hasDerivAt_sinh (2 * t / r)).comp t
    (((hasDerivAt_id t).const_mul 2).div_const r)).const_mul (bounceQ K r rh)
  have hD := (hasDerivAt_bounceA (rh := rh) hK hr t).const_mul r
  have h := hN.div hD (by positivity)
  refine h.congr_deriv ?_
  simp only [id, Function.comp_def]
  field_simp
  unfold bounceU at hA2
  linear_combination (2 * bounceQ K r rh * cosh (2 * t / r) - bounceA K r rh t ^ 2
    - (K * r ^ 2 / 2 + bounceQ K r rh * cosh (2 * t / r))) * hA2 + bounceQ K r rh ^ 2 * hc + hq

end Closed

/-- `ρ_BH` along a history has derivative `-4 ρ_BH ȧ/a`. -/
private lemma hasDerivAt_rhoBH_comp {GN K rh : ℝ} {a : ℝ → ℝ} {a' t : ℝ} (ha : HasDerivAt a a' t)
    (hne : a t ≠ 0) :
    HasDerivAt (fun t ↦ WhiteHole.rhoBH GN K 1 rh (a t))
      (-4 * WhiteHole.rhoBH GN K 1 rh (a t) * a' / a t) t := by
  have h := ((ha.pow 4).inv (pow_ne_zero 4 hne)).const_mul (WhiteHole.rhoBH GN K 1 rh 1)
  have e : (fun t ↦ WhiteHole.rhoBH GN K 1 rh (a t))
      = fun t ↦ WhiteHole.rhoBH GN K 1 rh 1 * (a t ^ 4)⁻¹ :=
    funext fun t ↦ by rw [rhoBH_scaling one_ne_zero, div_eq_mul_inv]
  rw [e]
  refine h.congr_deriv ?_
  rw [rhoBH_scaling (a := a t) one_ne_zero]
  simp only [Pi.pow_apply]
  field_simp
  ring

variable {K rh : ℝ}

/-- `H² + 𝒦/a² - 𝒦²r_h²/a⁴ = 1/r_c²` along the bounce. -/
private lemma bounce_arg (c : Couplings) (hK : 0 < K) (hrh : 0 ≤ rh) (hrc : 2 * rh ≤ c.rc)
    (t : ℝ) :
    (deriv (bounceA K c.rc rh) t / bounceA K c.rc rh t) ^ 2 + K / bounceA K c.rc rh t ^ 2
      - K ^ 2 * rh ^ 2 / bounceA K c.rc rh t ^ 4 = (1 / c.rc) ^ 2 := by
  have hr := c.rc_pos
  have hA := bounceA_pos (rh := rh) hK hr t
  rw [div_pow, ← add_div, bounce_friedmann hK hr hrh hrc t]
  field_simp
  ring

namespace BraneCosmology

/-- **An expanding brane with a bulk black hole and radiation.** Radiation with `ρ = ρ_BH`,
`a² = 𝒦 r_c²/2 + q cosh(2t/r_c)` with `q = 𝒦 r_c √(r_c²/4 - r_h²)`, orientation `ε = -1`, and
`ρ̃ = -P̃ = 2ρ̃_s`. Needs `2 r_h ≤ r_c`. -/
noncomputable def radiationBounce (c : Couplings) (K rh : ℝ) (hK : 0 < K) (hrh : 0 ≤ rh)
    (hrc : 2 * rh ≤ c.rc) : BraneCosmology where
  c := c
  K := K
  H0 := 1
  rh := rh
  ε := -1
  a := bounceA K c.rc rh
  ρ := fun t ↦ WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t)
  P := fun t ↦ WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t) / 3
  ρt := fun _ ↦ 2 * c.rhoS
  Pt := fun _ ↦ -(2 * c.rhoS)
  K_pos := hK
  H0_pos := one_pos
  rh_nonneg := hrh
  ε_sq := by norm_num
  a_pos := bounceA_pos hK c.rc_pos
  a_diff := fun t ↦ (hasDerivAt_bounceA hK c.rc_pos t).differentiableAt
  ρ_diff := fun t ↦ (hasDerivAt_rhoBH_comp (hasDerivAt_bounceA hK c.rc_pos t)
    (bounceA_pos hK c.rc_pos t).ne').differentiableAt
  ρt_diff := differentiable_const _
  friedmann := fun t ↦ by
    have hA := bounceA_pos (rh := rh) hK c.rc_pos t
    have hT := rhoBH_term (K := K) (rh := rh) c.GN_pos.ne' one_ne_zero hA.ne'
    have hS := c.gN_mul_rhoS
    linear_combination bounce_arg c hK hrh hrc t + hT - 2 * hS
  continuity := fun t ↦ by
    have hA := bounceA_pos (rh := rh) hK c.rc_pos t
    rw [(hasDerivAt_rhoBH_comp (hasDerivAt_bounceA hK c.rc_pos t) hA.ne').deriv,
      (hasDerivAt_bounceA hK c.rc_pos t).deriv]
    ring
  continuity_tilde := fun _ ↦ by simp
  junction := fun t ↦ by
    have hr := c.rc_pos
    rw [bounce_arg c hK hrh hrc t, sqrt_sq (by positivity)]
    linear_combination 2 * c.g_mul_rhoS
  junction_arg := fun t ↦ by
    rw [bounce_arg c hK hrh hrc t]
    positivity

variable (c : Couplings) (hK : 0 < K) (hrh : 0 ≤ rh) (hrc : 2 * rh ≤ c.rc)

/-- The bounce is on the self-accelerating branch `ρ̃_+` of Eq. (26). -/
theorem radiationBounce_selfAccelerating (t : ℝ) :
    (radiationBounce c K rh hK hrh hrc).ρt t
      = rhoTilde 1 c.rhoS ((radiationBounce c K rh hK hrh hrc).rhoBH t)
        ((radiationBounce c K rh hK hrh hrc).ρ t) := by
  change 2 * c.rhoS = rhoTilde 1 c.rhoS (WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t))
    (WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t))
  unfold rhoTilde
  simp only [sub_self, mul_zero, zero_div, sub_zero, sqrt_one]
  ring

/-- Eq. (16) holds for the bounce at every time, the bounce `t = 0` included. -/
theorem radiationBounce_pressure (t : ℝ) :
    (radiationBounce c K rh hK hrh hrc).Pt t
      = pressureTilde c.rhoS ((radiationBounce c K rh hK hrh hrc).ρt t)
        (3 * (radiationBounce c K rh hK hrh hrc).P t
          - (radiationBounce c K rh hK hrh hrc).ρ t) := by
  have := c.rhoS_pos
  change -(2 * c.rhoS) = pressureTilde c.rhoS (2 * c.rhoS)
    (3 * (WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t) / 3)
      - WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t))
  unfold pressureTilde
  field_simp
  ring

/-- **The bounce solves the equations of motion.** It obeys the acceleration equation at every
time, including the bounce `t = 0`, where `H = 0` and `accelAt_of_ne` does not apply. -/
theorem radiationBounce_accelAt (t : ℝ) : (radiationBounce c K rh hK hrh hrc).AccelAt t := by
  have hr := c.rc_pos
  have hA := bounceA_pos (rh := rh) hK hr t
  have hT := rhoBH_term (K := K) (rh := rh) c.GN_pos.ne' one_ne_zero hA.ne'
  have hS := c.gN_mul_rhoS
  refine (bounce_accel hK hr hrh hrc t).congr_deriv ?_
  change _ = -(4 * π * c.GN / 3) * (WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t)
    + 2 * c.rhoS + 3 * (WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t) / 3 + -(2 * c.rhoS)))
    * bounceA K c.rc rh t
  rw [show -(K ^ 2 * rh ^ 2) / bounceA K c.rc rh t ^ 3
    = -(K ^ 2 * rh ^ 2 / bounceA K c.rc rh t ^ 4) * bounceA K c.rc rh t by field_simp, hT]
  linear_combination (-2 * bounceA K c.rc rh t) * hS

/-- If `2 r_h < r_c`, the brane expands at every `t > 0`. -/
theorem radiationBounce_H_pos (hlt : 2 * rh < c.rc) {t : ℝ} (ht : 0 < t) :
    0 < (radiationBounce c K rh hK hrh hrc).H t := by
  have hr := c.rc_pos
  have hA := bounceA_pos (rh := rh) hK hr t
  have hq : 0 < bounceQ K c.rc rh := by
    unfold bounceQ
    have : 0 < c.rc ^ 2 / 4 - rh ^ 2 := by nlinarith
    positivity
  have hs : 0 < sinh (2 * t / c.rc) := sinh_pos_iff.2 (by positivity)
  change 0 < deriv (bounceA K c.rc rh) t / bounceA K c.rc rh t
  rw [(hasDerivAt_bounceA hK hr t).deriv]
  positivity

/-- The bounce stays outside the horizon (`f > 0` at the brane) at every time:
`a²/𝒦 ≥ r_c²/2 > r_h²`. -/
theorem radiationBounce_outside (t : ℝ) :
    0 < (radiationBounce c K rh hK hrh hrc).toBulk.fBrane t := by
  change 0 < blacken rh (braneRadius K (bounceA K c.rc rh t))
  have hr := c.rc_pos
  rw [outside_horizon_iff hrh hK (bounceA_pos hK hr t), braneRadius,
    lt_div_iff₀ (sqrt_pos.2 hK), bounceA, lt_sqrt (by positivity), mul_pow, sq_sqrt hK.le]
  have := mul_nonneg (bounceQ_nonneg (rh := rh) hK hr) (cosh_pos (2 * t / c.rc)).le
  have h4 : rh ^ 2 * 4 ≤ c.rc ^ 2 := by nlinarith
  unfold bounceU
  nlinarith [mul_le_mul_of_nonneg_left h4 hK.le, mul_pos hK (pow_pos hr 2)]

end BraneCosmology

/-- **ROADMAP M2.2.** There is a brane cosmology with a bulk black hole (`r_h > 0`), radiation
(`ρ > 0`, `P = ρ/3`), the paper's orientation `ε = -1`, and an expanding scale factor. It obeys
the acceleration equation and Eq. (16) at every time, so it is a solution of the equations of
motion, not only of the fields. -/
theorem exists_expanding_radiation :
    ∃ M : BraneCosmology, 0 < M.rh ∧ M.ε = -1 ∧ ∀ t, 0 < M.ρ t ∧ M.P t = M.ρ t / 3 ∧
      M.ρt t = rhoTilde 1 M.c.rhoS (M.rhoBH t) (M.ρ t) ∧ M.AccelAt t ∧
      M.Pt t = pressureTilde M.c.rhoS (M.ρt t) (3 * M.P t - M.ρ t) ∧ (0 < t → 0 < M.H t) := by
  let c : Couplings := ⟨1, 1, one_pos, one_pos⟩
  have hrc : c.rc = 1 := by change (1 : ℝ) / 1 = 1; norm_num
  have h1 : 2 * (1 / 4 : ℝ) ≤ c.rc := by rw [hrc]; norm_num
  have h2 : 2 * (1 / 4 : ℝ) < c.rc := by rw [hrc]; norm_num
  have h0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  refine ⟨BraneCosmology.radiationBounce c 1 (1 / 4) one_pos h0 h1,
    by change (0 : ℝ) < 1 / 4; norm_num, rfl,
    fun t ↦ ⟨?_, rfl, BraneCosmology.radiationBounce_selfAccelerating c one_pos h0 h1 t,
      BraneCosmology.radiationBounce_accelAt c one_pos h0 h1 t,
      BraneCosmology.radiationBounce_pressure c one_pos h0 h1 t,
      fun ht ↦ BraneCosmology.radiationBounce_H_pos c one_pos h0 h1 h2 ht⟩⟩
  have hA := bounceA_pos (rh := 1 / 4) one_pos c.rc_pos t
  change 0 < WhiteHole.rhoBH 1 1 1 (1 / 4) (bounceA 1 c.rc (1 / 4) t)
  rw [rhoBH_eq one_ne_zero]
  positivity

end WhiteHole
