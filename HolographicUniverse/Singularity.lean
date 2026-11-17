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

The horizon results hold for any blackening factor `f` (`BulkCosmology.singularity_inside_iff`
and its variants in `GeneralBulk.lean`). The versions here are the Schwarzschild case.

Not proved: that a history actually reaches the singularity. That needs solutions of the
equations of motion (M4).
-/

namespace WhiteHole

open Real Set

section Algebra

variable {s b ρ x : ℝ}

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

namespace BraneCosmology

variable (M : BraneCosmology)

/-- **Claim 1 along a history.** -/
theorem singularity_iff (t : ℝ) : M.ρt t = M.c.rhoS ↔ 2 * (M.rhoBH t - M.ρ t) = M.c.rhoS :=
  isInduced_eq_rhoS_iff M.c.rhoS_pos (M.isInduced t)

/-- **Claim 3, exact form.** At the pressure singularity the brane is on or inside the
horizon exactly when `|H| ≥ 1/(2 r_c)`. The case `f = 1 - r_h²/r²` of
`BulkCosmology.singularity_inside_iff`. -/
theorem singularity_inside_iff {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    blacken M.rh (braneRadius M.K (M.a t)) ≤ 0 ↔ 1 / (2 * M.c.rc) ≤ |M.H t| :=
  M.toBulk.singularity_inside_iff h

/-- At the pressure singularity the brane is strictly inside the horizon exactly when
`|H| > 1/(2 r_c)`. -/
theorem singularity_strictly_inside_iff {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    blacken M.rh (braneRadius M.K (M.a t)) < 0 ↔ 1 / (2 * M.c.rc) < |M.H t| :=
  M.toBulk.singularity_strictly_inside_iff h

/-- **Claim 3, density form.** At the pressure singularity the brane is on or inside the
horizon exactly when the curvature term is at most `(8π G_N/3)(ρ + ρ̃_s/2)`. -/
theorem singularity_inside_iff_curvature {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    blacken M.rh (braneRadius M.K (M.a t)) ≤ 0 ↔
      M.K / M.a t ^ 2 ≤ 8 * π * M.c.GN / 3 * (M.ρ t + M.c.rhoS / 2) :=
  M.toBulk.singularity_inside_iff_curvature h

/-- **Claim 3 at early times.** If `r_c ≥ L`, a pressure singularity at a time with
`|H| ≥ 1/(2L)` is on or inside the horizon. -/
theorem singularity_inside_of_rc {t L : ℝ} (h : M.ρt t = M.c.rhoS) (hL : 0 < L)
    (hrc : L ≤ M.c.rc) (hH : 1 / (2 * L) ≤ |M.H t|) :
    blacken M.rh (braneRadius M.K (M.a t)) ≤ 0 :=
  M.toBulk.singularity_inside_of_rc h hL hrc hH

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
