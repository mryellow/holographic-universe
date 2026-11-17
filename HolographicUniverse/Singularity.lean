import HolographicUniverse.History

/-!
# The pressure singularity (ROADMAP M3.4)

Eq. (16) for `P̃` has the denominator `ρ̃_s - ρ̃`, so the induced pressure is singular at
`ρ̃ = ρ̃_s`. The paper says three things about this point:

1. The equality case of the reality bound (30) "indicates a pressure singularity" (Sec. 3).
2. It is "generically encountered at early times" (Sec. 5).
3. It "always happens inside a white hole horizon" (Sec. 5).

What is proved here:

* `isInduced_eq_rhoS_iff`, `BraneCosmology.singularity_iff`: `ρ̃ = ρ̃_s` exactly when the reality
  bound is saturated, `2(ρ_BH - ρ) = ρ̃_s`. This is claim 1, in both directions.
* `branches_meet_iff`, `rhoTilde_at_saturation`: under the reality bound, the two branches
  `ρ̃_±` are equal exactly at saturation, and there both equal `ρ̃_s`. So a history can pass
  between the branches only through the singularity.
* `BraneCosmology.singularity_inside_iff`: at the singularity, the brane is on or inside the
  horizon (`f(a) ≤ 0`) **exactly when `|H| ≥ 1/(2 r_c)`**. The strict forms are
  `singularity_strictly_inside_iff`. `singularity_inside_iff_curvature` gives the same
  condition as `𝒦/a² ≤ (8π G_N/3)(ρ + ρ̃_s/2)`: the curvature term does not dominate the
  Friedmann equation.
* `BraneCosmology.singularity_inside_of_rc`: if `r_c ≥ L` (for example the observational bound
  `r_c ≳ 1/H₀`), a singularity at a time with `|H| ≥ 1/(2L)` is on or inside the horizon.

So claim 3 is **not** unconditional. It holds at early times, where `H r_c ≫ 1`. A singularity
in a curvature-dominated phase with `|H| < 1/(2 r_c)` would be outside the horizon.

* `BraneCosmology.scale_factor_floor`: claim 2, in the form that holds without solving the
  dynamics. In an expanding era with `P ≤ ρ/3` on `[t₁, t₂]`, the reality bound gives
  `ρ̃_s a(t)⁴ ≥ 2(ρ_BH - ρ)(t₂) a(t₂)⁴` at every `t` in the era. So if the black hole dominates
  (`ρ_BH > ρ`) at `t₂`, the scale factor in that era has a positive minimum. The history cannot
  reach `a → 0` within it, and the bound is reached only at saturation, which is the singularity.

Not proved: that a history actually reaches the singularity. That needs solutions of the
equations of motion (M4).
-/

namespace WhiteHole

open Real Set

section Algebra

variable {s b ρ x : ℝ}

/-- **Claim 1: `ρ̃ = ρ̃_s` exactly at saturation of the reality bound.** -/
theorem isInduced_eq_rhoS_iff (hs : 0 < s) (h : IsInduced s b ρ x) :
    x = s ↔ 2 * (b - ρ) = s := by
  unfold IsInduced at h
  constructor
  · intro hx
    rw [hx] at h
    have : s * (2 * (b - ρ) - s) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hs.ne'
    · linarith
  · intro hb
    have : (x - s) ^ 2 = 0 := by linear_combination h - s * hb
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- `ρ̃_+ - ρ̃_- = 2 ρ̃_s √(1 - 2(ρ_BH - ρ)/ρ̃_s)`. -/
private lemma rhoTilde_sub (s b ρ : ℝ) :
    rhoTilde 1 s b ρ - rhoTilde (-1) s b ρ = 2 * s * √(1 - 2 * (b - ρ) / s) := by
  unfold rhoTilde; ring

/-- **The branches meet exactly at the singularity.** Under the reality bound (30),
`ρ̃_+ = ρ̃_-` exactly when the bound is saturated. -/
theorem branches_meet_iff (hs : 0 < s) (hreal : 2 * (b - ρ) ≤ s) :
    rhoTilde 1 s b ρ = rhoTilde (-1) s b ρ ↔ 2 * (b - ρ) = s := by
  rw [← sub_eq_zero, rhoTilde_sub, mul_eq_zero, sqrt_eq_zero', sub_nonpos,
    one_le_div hs]
  constructor
  · rintro (h | h)
    · exact absurd h (by positivity)
    · linarith
  · intro h; right; linarith

/-- At saturation, both branches equal `ρ̃_s`. -/
theorem rhoTilde_at_saturation (sgn : ℝ) (hs : 0 < s) (h : 2 * (b - ρ) = s) :
    rhoTilde sgn s b ρ = s := by
  unfold rhoTilde
  rw [h, div_self hs.ne', sub_self, sqrt_zero]
  ring

end Algebra

/-- `(8π G_b/3) ρ̃_s = 1/(2 r_c)`. -/
lemma Couplings.g_mul_rhoS (c : Couplings) : 8 * π * c.Gb / 3 * c.rhoS = 1 / (2 * c.rc) := by
  unfold Couplings.rhoS Couplings.rc
  have := c.GN_pos; have := c.Gb_pos
  field_simp
  ring

private lemma nonpos_iff_mul {c f : ℝ} (hc : 0 < c) : f ≤ 0 ↔ c * f ≤ 0 := by
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith [mul_pos hc h']

private lemma neg_iff_mul {c f : ℝ} (hc : 0 < c) : f < 0 ↔ c * f < 0 := by
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith [mul_nonneg hc.le h']

namespace BraneCosmology

variable (M : BraneCosmology)

/-- **Claim 1 along a history.** -/
theorem singularity_iff (t : ℝ) : M.ρt t = M.c.rhoS ↔ 2 * (M.rhoBH t - M.ρ t) = M.c.rhoS :=
  isInduced_eq_rhoS_iff M.c.rhoS_pos (M.isInduced t)

/-- At the singularity, `(𝒦/a²) f(a) = 1/(2 r_c)² - H²`. -/
private lemma blacken_at_singularity {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    M.K / M.a t ^ 2 * blacken M.rh (braneRadius M.K (M.a t))
      = (1 / (2 * M.c.rc)) ^ 2 - M.H t ^ 2 := by
  have hJ := M.junction t
  have hArg := M.junction_arg t
  rw [h] at hJ
  have hY : (deriv M.a t / M.a t) ^ 2 + M.K / M.a t ^ 2 - M.K ^ 2 * M.rh ^ 2 / M.a t ^ 4
      = (8 * π * M.c.Gb / 3 * M.c.rhoS) ^ 2 := by
    have h2 := congrArg (· ^ 2) hJ
    simp only [mul_pow, sq_sqrt hArg, M.ε_sq, one_mul] at h2
    rw [h2]
    ring
  rw [curv_mul_blacken M.K_pos (M.a_pos t).ne', H, ← M.c.g_mul_rhoS, ← hY]
  ring

/-- **Claim 3, exact form.** At the pressure singularity the brane is on or inside the
horizon exactly when `|H| ≥ 1/(2 r_c)`. -/
theorem singularity_inside_iff {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    blacken M.rh (braneRadius M.K (M.a t)) ≤ 0 ↔ 1 / (2 * M.c.rc) ≤ |M.H t| := by
  have hKa : 0 < M.K / M.a t ^ 2 := div_pos M.K_pos (pow_pos (M.a_pos t) 2)
  have hr : 0 ≤ 1 / (2 * M.c.rc) := by have := M.c.rc_pos; positivity
  rw [nonpos_iff_mul hKa, M.blacken_at_singularity h, sub_nonpos,
    sq_le_sq, abs_of_nonneg hr]

/-- At the pressure singularity the brane is strictly inside the horizon exactly when
`|H| > 1/(2 r_c)`. -/
theorem singularity_strictly_inside_iff {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    blacken M.rh (braneRadius M.K (M.a t)) < 0 ↔ 1 / (2 * M.c.rc) < |M.H t| := by
  have hKa : 0 < M.K / M.a t ^ 2 := div_pos M.K_pos (pow_pos (M.a_pos t) 2)
  have hr : 0 ≤ 1 / (2 * M.c.rc) := by have := M.c.rc_pos; positivity
  rw [neg_iff_mul hKa, M.blacken_at_singularity h, sub_neg,
    sq_lt_sq, abs_of_nonneg hr]

/-- **Claim 3, density form.** At the pressure singularity the brane is on or inside the
horizon exactly when the curvature term is at most `(8π G_N/3)(ρ + ρ̃_s/2)`. -/
theorem singularity_inside_iff_curvature {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    blacken M.rh (braneRadius M.K (M.a t)) ≤ 0 ↔
      M.K / M.a t ^ 2 ≤ 8 * π * M.c.GN / 3 * (M.ρ t + M.c.rhoS / 2) := by
  have hKa : 0 < M.K / M.a t ^ 2 := div_pos M.K_pos (pow_pos (M.a_pos t) 2)
  have hF := M.friedmann t
  rw [h] at hF
  have hκ : 8 * π * M.c.GN / 3 * M.c.rhoS = 2 * (1 / (2 * M.c.rc)) ^ 2 := by
    rw [← M.c.g_mul_rhoS]
    unfold Couplings.rhoS
    have := M.c.GN_pos; have := M.c.Gb_pos
    field_simp
    ring
  rw [nonpos_iff_mul hKa, M.blacken_at_singularity h, H]
  constructor <;> intro h' <;> nlinarith

/-- **Claim 3 at early times.** If `r_c ≥ L`, a pressure singularity at a time with
`|H| ≥ 1/(2L)` is on or inside the horizon. -/
theorem singularity_inside_of_rc {t L : ℝ} (h : M.ρt t = M.c.rhoS) (hL : 0 < L)
    (hrc : L ≤ M.c.rc) (hH : 1 / (2 * L) ≤ |M.H t|) :
    blacken M.rh (braneRadius M.K (M.a t)) ≤ 0 := by
  refine (M.singularity_inside_iff h).2 (le_trans ?_ hH)
  gcongr

/-- `ρ_BH a⁴` is a constant of the history. -/
theorem rhoBH_mul_a4 (t : ℝ) : M.rhoBH t * M.a t ^ 4 = M.rhoBH₁ := by
  rw [rhoBH, rhoBH_scaling M.H0_pos.ne', rhoBH₁, div_mul_cancel₀ _ (pow_pos (M.a_pos t) 4).ne']

/-- **Claim 2: a floor on the scale factor.** In an expanding era with `P ≤ ρ/3` on
`[t₁, t₂]`, the reality bound gives `ρ̃_s a(t)⁴ ≥ 2 (ρ_BH - ρ)(t₂) a(t₂)⁴` for every `t` in the
era. If `ρ_BH > ρ` at `t₂`, the scale factor has a positive minimum in the era. -/
theorem scale_factor_floor {t₁ t₂ : ℝ} (hP : ∀ t ∈ Icc t₁ t₂, M.P t ≤ M.ρ t / 3)
    (hH : ∀ t ∈ Icc t₁ t₂, 0 ≤ deriv M.a t) {t : ℝ} (ht : t ∈ Icc t₁ t₂) :
    2 * (M.rhoBH t₂ - M.ρ t₂) * M.a t₂ ^ 4 ≤ M.c.rhoS * M.a t ^ 4 := by
  have ht₂ : t₂ ∈ Icc t₁ t₂ := right_mem_Icc.2 (ht.1.trans ht.2)
  have hQ := M.rho_a4_monotoneOn hP hH ht ht₂ ht.2
  simp only at hQ
  have e := M.rhoBH_mul_a4 t
  have e₂ := M.rhoBH_mul_a4 t₂
  have r := mul_le_mul_of_nonneg_right (M.reality t) (pow_pos (M.a_pos t) 4).le
  nlinarith

end BraneCosmology

end WhiteHole
