module

public import HolographicUniverse.Orientation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Time dependence of `ρ_BH/ρ`, and what the orientation allows along a history (ROADMAP M3.2)

`ρ_BH ∝ a⁻⁴` (Eq. (28), `rhoBH_scaling`), so `ρ_BH/ρ = ρ_BH(a=1)/(ρ a⁴)`: `ratio_eq`. The
history of the ratio is the history of `ρ a⁴`.

**Eras.** From the continuity equation (12):

* `radiation_era_ratio`: where `P = ρ/3`, `ρ a⁴` is constant, so `ρ_BH/ρ` is constant.
* `matter_era_ratio`: where `P = 0`, `ρ a³` is constant, so `(ρ_BH/ρ) · a` is constant: the
  ratio falls as `1/a`.
* `ratio_antitoneOn`: for any matter with `P ≤ ρ/3` (radiation, dust, a cosmological constant,
  or a mixture) and `ρ > 0`, the ratio never rises while the universe expands.

**Fixed orientation.** In a `BraneCosmology`, `ε` is constant, and on the normal branch the sign
of `ρ̃_-` is the sign of `ρ_BH - ρ` (`Orientation.lean`). So:

* `rho_le_rhoBH_of_eps_neg`, `rhoBH_le_rho_of_eps_pos`: with `ε = -1` the normal branch keeps
  `ρ ≤ ρ_BH` at every time. With `ε = +1` it keeps `ρ_BH ≤ ρ`.
* `eps_of_singularity`: a history that reaches the pressure singularity `ρ̃ = ρ̃_s` has
  `ε = -1`.
* `matter_era_growth_le`: with `ε = -1`, a normal-branch matter era that starts at `t₁` ends
  before `a` grows by the factor `(ρ_BH/ρ)(t₁)`.
* `matter_era_growth_le_small`: with the paper's smallness bound (32) at `t₁`,
  `|ρ̃| ≤ ϵ ρ`, that factor is at most `1 + ϵ`. For the paper's `ϵ = 0.1`, the scale factor can
  grow by at most 10 % during the matter era. The real matter era grows `a` by a factor of
  about `10³`.

So a normal-branch history with a fixed `ε = -1` cannot contain a realistic matter era. A history
with fixed `ε = +1` can, but it cannot reach the pressure singularity.

**Variable orientation.** The paper's white-hole history (Sec. 3, the "black strip" of its
Fig. 3) starts at the pressure singularity in the radiation era, which needs `ε = -1`. It ends
today with `ρ_BH ≪ ρ`, which on the normal branch needs `ε = +1`. So `ε` has to change along
that history, and a `BraneCosmology` (constant `ε`) cannot describe it. If `ε` is allowed to
depend on time:

* `sign_change_inside`: when `ρ̃` changes sign, there is a time with `ρ̃ = 0` at which the brane
  is on or inside the horizon (`f(a) ≤ 0`). By the junction condition, `ε` can only change
  where `ρ̃ = 0`.
* `sign_const_outside`: a history that stays outside the horizon keeps one sign of `ρ̃`.
* `rhoTilde_minus_eq_zero_iff`: on the normal branch, `ρ̃ = 0` exactly when `ρ_BH = ρ`.

So the paper's black-hole history, which stays outside the horizon after it emerges, keeps
one orientation. The white-hole history can change orientation only while the brane is still
inside the horizon. The paper puts the horizon exit at `a ∼ 0.01–1`, so the crossing
`ρ_BH = ρ` must happen before that. The paper does not check this.

Not proved here: that a time-dependent `ε` is geometrically allowed at a point where `ρ̃ = 0`
(the bulk side kept by the `Z₂` reflection would change). This is open, with the geometric
reading of `ε = +1` (M3.1).
-/

namespace WhiteHole

open Real Set

section Flip

/-- **The normal branch vanishes exactly at `ρ_BH = ρ`.** -/
theorem rhoTilde_minus_eq_zero_iff {s b ρ : ℝ} (hs : 0 < s) :
    rhoTilde (-1) s b ρ = 0 ↔ b = ρ := by
  constructor
  · intro h
    rcases lt_trichotomy ρ b with hlt | heq | hgt
    · have := (rhoTilde_minus_pos_iff hs).2 hlt; linarith
    · exact heq.symm
    · have := (rhoTilde_minus_neg_iff hs).2 hgt; linarith
  · rintro rfl
    simp [rhoTilde]

variable {Gb K rh t₁ t₂ : ℝ} {a H ρt ε : ℝ → ℝ}

/-- **The orientation can change only on or inside the horizon.** Let `ε(t)` be allowed to
depend on time, with the spatial junction condition at every time. If `ρ̃` changes sign, then
at some time between, `ρ̃ = 0` and the brane is on or inside the horizon. -/
theorem sign_change_inside (hK : 0 < K) (ha : ∀ t ∈ uIcc t₁ t₂, 0 < a t)
    (hcont : ContinuousOn ρt (uIcc t₁ t₂)) (hε : ∀ t ∈ uIcc t₁ t₂, ε t ^ 2 = 1)
    (hJ : ∀ t ∈ uIcc t₁ t₂, ε t * √(H t ^ 2 + K / a t ^ 2 - K ^ 2 * rh ^ 2 / a t ^ 4)
      = -(8 * π * Gb / 3) * ρt t)
    (hArg : ∀ t ∈ uIcc t₁ t₂, 0 ≤ H t ^ 2 + K / a t ^ 2 - K ^ 2 * rh ^ 2 / a t ^ 4)
    (hsign : ρt t₁ * ρt t₂ < 0) :
    ∃ t ∈ uIcc t₁ t₂, ρt t = 0 ∧ blacken rh (braneRadius K (a t)) ≤ 0 := by
  have h0 : (0 : ℝ) ∈ uIcc (ρt t₁) (ρt t₂) := by
    rw [mem_uIcc]
    rcases lt_or_ge (ρt t₁) 0 with h | h
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  obtain ⟨t, ht, h⟩ := intermediate_value_uIcc hcont h0
  refine ⟨t, ht, h, rhoTilde_eq_zero_inside (Gb := Gb) hK (ha t ht) ?_ (hε t ht) (hArg t ht)⟩
  rw [← h]
  exact hJ t ht

/-- **Outside the horizon, `ρ̃` keeps its sign**, even if `ε` may depend on time. -/
theorem sign_const_outside (hK : 0 < K) (ha : ∀ t ∈ uIcc t₁ t₂, 0 < a t)
    (hcont : ContinuousOn ρt (uIcc t₁ t₂)) (hε : ∀ t ∈ uIcc t₁ t₂, ε t ^ 2 = 1)
    (hJ : ∀ t ∈ uIcc t₁ t₂, ε t * √(H t ^ 2 + K / a t ^ 2 - K ^ 2 * rh ^ 2 / a t ^ 4)
      = -(8 * π * Gb / 3) * ρt t)
    (hArg : ∀ t ∈ uIcc t₁ t₂, 0 ≤ H t ^ 2 + K / a t ^ 2 - K ^ 2 * rh ^ 2 / a t ^ 4)
    (hout : ∀ t ∈ uIcc t₁ t₂, 0 < blacken rh (braneRadius K (a t))) :
    0 ≤ ρt t₁ * ρt t₂ := by
  by_contra h
  push Not at h
  obtain ⟨t, ht, -, hf⟩ := sign_change_inside hK ha hcont hε hJ hArg h
  exact (hout t ht).not_ge hf

end Flip

namespace BraneCosmology

variable (M : BraneCosmology) {t₁ t₂ : ℝ}

/-- `ρ_BH` at `a = 1` (today). -/
noncomputable def rhoBH₁ : ℝ := WhiteHole.rhoBH M.c.GN M.K M.H0 M.rh 1

theorem rhoBH₁_nonneg : 0 ≤ M.rhoBH₁ := by
  rw [rhoBH₁, rhoBH_eq M.H0_pos.ne']
  have := M.c.GN_pos
  positivity

/-- **`ρ_BH/ρ = ρ_BH(a=1)/(ρ a⁴)`**, at every time, with no condition on `ρ`. -/
theorem ratio_eq (t : ℝ) : M.rhoBH t / M.ρ t = M.rhoBH₁ / (M.ρ t * M.a t ^ 4) := by
  rw [rhoBH, rhoBH_scaling M.H0_pos.ne', div_div, mul_comm, rhoBH₁]

/-- `(ρ_BH/ρ) · a = ρ_BH(a=1)/(ρ a³)`. -/
theorem ratio_mul_a (t : ℝ) : M.rhoBH t / M.ρ t * M.a t = M.rhoBH₁ / (M.ρ t * M.a t ^ 3) := by
  rw [ratio_eq, show M.ρ t * M.a t ^ 4 = M.ρ t * M.a t ^ 3 * M.a t by ring, ← div_div,
    div_mul_cancel₀ _ (M.a_pos t).ne']

/-- `d(ρ a⁴)/dt = a³ ȧ (ρ - 3P)`. -/
theorem hasDerivAt_rho_a4 (t : ℝ) :
    HasDerivAt (fun t ↦ M.ρ t * M.a t ^ 4) (M.a t ^ 3 * deriv M.a t * (M.ρ t - 3 * M.P t)) t := by
  have h := (M.ρ_diff t).hasDerivAt.mul ((M.a_diff t).hasDerivAt.pow 4)
  convert h using 1
  rw [M.continuity t]
  simp only [Pi.pow_apply]
  field_simp [(M.a_pos t).ne']
  ring

/-- `d(ρ a³)/dt = -3 a² ȧ P`. -/
theorem hasDerivAt_rho_a3 (t : ℝ) :
    HasDerivAt (fun t ↦ M.ρ t * M.a t ^ 3) (-3 * M.a t ^ 2 * deriv M.a t * M.P t) t := by
  have h := (M.ρ_diff t).hasDerivAt.mul ((M.a_diff t).hasDerivAt.pow 3)
  convert h using 1
  rw [M.continuity t]
  simp only [Pi.pow_apply]
  field_simp [(M.a_pos t).ne']
  ring

/-- A function with zero derivative on `[t₁, t₂]` is constant there. -/
private lemma const_of_deriv_zero {f : ℝ → ℝ} (hd : ∀ t ∈ Icc t₁ t₂, HasDerivAt f 0 t) :
    ∀ t ∈ Icc t₁ t₂, f t = f t₁ :=
  constant_of_has_deriv_right_zero (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

/-- **Radiation era: `ρ a⁴` is constant.** -/
theorem radiation_era_const (hP : ∀ t ∈ Icc t₁ t₂, M.P t = M.ρ t / 3) :
    ∀ t ∈ Icc t₁ t₂, M.ρ t * M.a t ^ 4 = M.ρ t₁ * M.a t₁ ^ 4 :=
  const_of_deriv_zero fun t ht ↦ by
    have h := M.hasDerivAt_rho_a4 t
    rwa [hP t ht, show M.ρ t - 3 * (M.ρ t / 3) = 0 by ring, mul_zero] at h

/-- **Radiation era: `ρ_BH/ρ` is constant.** -/
theorem radiation_era_ratio (hP : ∀ t ∈ Icc t₁ t₂, M.P t = M.ρ t / 3) :
    ∀ t ∈ Icc t₁ t₂, M.rhoBH t / M.ρ t = M.rhoBH t₁ / M.ρ t₁ := fun t ht ↦ by
  rw [ratio_eq, ratio_eq, M.radiation_era_const hP t ht]

/-- **Matter era: `ρ a³` is constant.** -/
theorem matter_era_const (hP : ∀ t ∈ Icc t₁ t₂, M.P t = 0) :
    ∀ t ∈ Icc t₁ t₂, M.ρ t * M.a t ^ 3 = M.ρ t₁ * M.a t₁ ^ 3 :=
  const_of_deriv_zero fun t ht ↦ by
    simpa [hP t ht] using M.hasDerivAt_rho_a3 t

/-- **Matter era: `ρ_BH/ρ ∝ 1/a`.** -/
theorem matter_era_ratio (hP : ∀ t ∈ Icc t₁ t₂, M.P t = 0) :
    ∀ t ∈ Icc t₁ t₂, M.rhoBH t / M.ρ t * M.a t = M.rhoBH t₁ / M.ρ t₁ * M.a t₁ := fun t ht ↦ by
  rw [ratio_mul_a, ratio_mul_a, M.matter_era_const hP t ht]

/-- While the universe expands with `P ≤ ρ/3`, `ρ a⁴` does not decrease. -/
theorem rho_a4_monotoneOn (hP : ∀ t ∈ Icc t₁ t₂, M.P t ≤ M.ρ t / 3)
    (hH : ∀ t ∈ Icc t₁ t₂, 0 ≤ deriv M.a t) :
    MonotoneOn (fun t ↦ M.ρ t * M.a t ^ 4) (Icc t₁ t₂) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun t _ ↦ (M.hasDerivAt_rho_a4 t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (M.hasDerivAt_rho_a4 t).differentiableAt.differentiableWithinAt) ?_
  intro t ht
  rw [interior_Icc] at ht
  have ht' := Ioo_subset_Icc_self ht
  rw [(M.hasDerivAt_rho_a4 t).deriv]
  have := hP t ht'
  have := M.a_pos t
  exact mul_nonneg (mul_nonneg (by positivity) (hH t ht')) (by linarith)

/-- **`ρ_BH/ρ` never rises while the universe expands**, for any matter with `P ≤ ρ/3` and
`ρ > 0`: radiation, dust, a cosmological constant, or a mixture. -/
theorem ratio_antitoneOn (hP : ∀ t ∈ Icc t₁ t₂, M.P t ≤ M.ρ t / 3)
    (hH : ∀ t ∈ Icc t₁ t₂, 0 ≤ deriv M.a t) (hρ : ∀ t ∈ Icc t₁ t₂, 0 < M.ρ t) :
    AntitoneOn (fun t ↦ M.rhoBH t / M.ρ t) (Icc t₁ t₂) := by
  intro x hx y hy hxy
  simp only [ratio_eq]
  have := M.a_pos x
  exact div_le_div_of_nonneg_left M.rhoBH₁_nonneg (by have := hρ x hx; positivity)
    (M.rho_a4_monotoneOn hP hH hx hy hxy)

/-- **`ε = -1` keeps the normal branch at `ρ ≤ ρ_BH`.** The history form of
`normal_branch_requires`. -/
theorem rho_le_rhoBH_of_eps_neg (hε : M.ε = -1) {t : ℝ}
    (hN : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t)) : M.ρ t ≤ M.rhoBH t := by
  by_contra h
  push Not at h
  have h1 := (rhoTilde_minus_neg_iff M.c.rhoS_pos).2 h
  have h2 := M.ρt_nonneg hε t
  rw [hN] at h2
  linarith

/-- **`ε = +1` keeps the normal branch at `ρ_BH ≤ ρ`.** -/
theorem rhoBH_le_rho_of_eps_pos (hε : M.ε = 1) {t : ℝ}
    (hN : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t)) : M.rhoBH t ≤ M.ρ t := by
  by_contra h
  push Not at h
  have h1 := (rhoTilde_minus_pos_iff M.c.rhoS_pos).2 h
  have h2 := M.eps_mul_ρt_nonpos t
  rw [hε, one_mul, hN] at h2
  linarith

/-- **The pressure singularity needs `ε = -1`.** At `ρ̃ = ρ̃_s > 0`, `ε ρ̃ ≤ 0` forces `ε = -1`. -/
theorem eps_of_singularity {t : ℝ} (h : M.ρt t = M.c.rhoS) : M.ε = -1 := by
  have h1 := M.eps_mul_ρt_nonpos t
  rw [h] at h1
  rcases eps_cases M.ε_sq with h' | h'
  · rw [h'] at h1; linarith [M.c.rhoS_pos]
  · exact h'

/-- **With `ε = -1`, a normal-branch matter era is short.** If the matter era starts at `t₁`
with `ρ > 0`, then at every later normal-branch time in it, `a(t) ≤ (ρ_BH/ρ)(t₁) · a(t₁)`. -/
theorem matter_era_growth_le (hε : M.ε = -1) (hP : ∀ t ∈ Icc t₁ t₂, M.P t = 0)
    (hρ₁ : 0 < M.ρ t₁) {t : ℝ} (ht : t ∈ Icc t₁ t₂)
    (hN : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t)) :
    M.a t ≤ M.rhoBH t₁ / M.ρ t₁ * M.a t₁ := by
  have ha := M.a_pos t
  have ha₁ := M.a_pos t₁
  have hρ : 0 < M.ρ t := by
    by_contra h
    push Not at h
    have := M.matter_era_const hP t ht
    nlinarith [mul_pos hρ₁ (pow_pos ha₁ 3), mul_nonpos_of_nonpos_of_nonneg h (pow_pos ha 3).le]
  have h1 : 1 ≤ M.rhoBH t / M.ρ t := (one_le_div hρ).2 (M.rho_le_rhoBH_of_eps_neg hε hN)
  rw [← M.matter_era_ratio hP t ht]
  nlinarith

/-- **With `ε = -1` and the smallness bound (32), a matter era grows `a` by at most `1 + ϵ`.**
For the paper's `ϵ = 0.1`, that is 10 %. -/
theorem matter_era_growth_le_small {ϵ : ℝ} (hε : M.ε = -1) (hP : ∀ t ∈ Icc t₁ t₂, M.P t = 0)
    (hρ₁ : 0 < M.ρ t₁) (hsmall : |M.ρt t₁| ≤ ϵ * M.ρ t₁) {t : ℝ} (ht : t ∈ Icc t₁ t₂)
    (hN : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t)) :
    M.a t ≤ (1 + ϵ) * M.a t₁ := by
  have h := M.matter_era_growth_le hε hP hρ₁ ht hN
  have hb : M.rhoBH t₁ ≤ (1 + ϵ) * M.ρ t₁ := by
    have hq := M.isInduced t₁
    unfold IsInduced at hq
    have hx := (abs_le.1 hsmall).2
    have hs := M.c.rhoS_pos
    nlinarith [sq_nonneg (M.ρt t₁)]
  have hr : M.rhoBH t₁ / M.ρ t₁ ≤ 1 + ϵ := by rwa [div_le_iff₀ hρ₁]
  calc M.a t ≤ M.rhoBH t₁ / M.ρ t₁ * M.a t₁ := h
    _ ≤ (1 + ϵ) * M.a t₁ := mul_le_mul_of_nonneg_right hr (M.a_pos t₁).le

end BraneCosmology

end WhiteHole
