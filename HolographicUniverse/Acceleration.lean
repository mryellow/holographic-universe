module

public import HolographicUniverse.Model
public import Mathlib.Analysis.Calculus.Darboux

@[expose] public section

/-!
# The acceleration equation (ROADMAP M2.4)

`BraneCosmology` contains the Friedmann equation (11) and the continuity equations (12)–(13),
but not the acceleration (Raychaudhuri) equation

  `ä / a = -(4π G_N / 3) (ρ + ρ̃ + 3 (P + P̃))`.

This file shows how much of that equation the structure already implies.

* `differentiableAt_deriv_of_sq_eq`: if `ȧ² = g` with `g` differentiable, then `ȧ` is
  differentiable wherever `ȧ ≠ 0`. The sign of `ȧ` cannot flip near such a point, because a
  derivative has the intermediate value property (Darboux). So the second derivative `ä` exists
  without assuming it.
* `accel_of_friedmann`: differentiating the Friedmann equation and using both continuity
  equations gives the acceleration equation wherever `H ≠ 0`.
* `BraneCosmology.AccelAt`, `BraneCosmology.accelAt_of_ne`: the same for the structure. Every
  `BraneCosmology` satisfies the acceleration equation at every time with `H ≠ 0`, with no
  additional hypothesis.

At a time with `H = 0` the structure does **not** imply the equation: see
`BraneCosmology.static_not_accelAt` in `Instances.lean`.
-/

namespace WhiteHole

open Real Topology

/-- **Regularity from a first integral.** If `ȧ² = g` everywhere with `g` differentiable, then
`ȧ` is differentiable at every point where `ȧ ≠ 0`. Near such a point `g > 0`, so `ȧ` does not
vanish. By Darboux's theorem `ȧ` keeps one sign there, so `ȧ = ±√g` locally. -/
theorem differentiableAt_deriv_of_sq_eq {a g : ℝ → ℝ} {τ : ℝ} (ha : Differentiable ℝ a)
    (hg : Differentiable ℝ g) (hsq : ∀ t, deriv a t ^ 2 = g t) (hτ : deriv a τ ≠ 0) :
    DifferentiableAt ℝ (deriv a) τ := by
  have hgτ : 0 < g τ := by rw [← hsq]; positivity
  have hev : ∀ᶠ t in 𝓝 τ, 0 < g t := hg.continuous.continuousAt.eventually (lt_mem_nhds hgτ)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hne : ∀ x ∈ Metric.ball τ δ, deriv a x ≠ 0 := fun x hx h0 ↦ by
    have := hball x hx
    rw [← hsq, h0] at this
    simp at this
  have hmem : Metric.ball τ δ ∈ 𝓝 τ := Metric.ball_mem_nhds τ hδ
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_ball τ δ)
    (fun x _ ↦ (ha x).hasDerivAt.hasDerivWithinAt) hne with h | h
  · have heq : deriv a =ᶠ[𝓝 τ] fun t ↦ -√(g t) := by
      filter_upwards [hmem] with x hx
      rw [← hsq, sqrt_sq_eq_abs, abs_of_neg (h x hx), neg_neg]
    exact ((hg τ).sqrt hgτ.ne').neg.congr_of_eventuallyEq heq
  · have heq : deriv a =ᶠ[𝓝 τ] fun t ↦ √(g t) := by
      filter_upwards [hmem] with x hx
      rw [← hsq, sqrt_sq_eq_abs, abs_of_pos (h x hx)]
    exact ((hg τ).sqrt hgτ.ne').congr_of_eventuallyEq heq

/-- **Acceleration equation from Friedmann + continuity.** Suppose the Friedmann equation
`H² + 𝒦/a² = κ (ρ + ρ̃)` holds at all times and the continuity equations (12)–(13) hold at `τ`.
If `H(τ) ≠ 0`, then `ä/a = -(κ/2) (ρ + ρ̃ + 3 (P + P̃))` at `τ`. With `κ = 8π G_N / 3` this is the
usual acceleration equation. -/
theorem accel_of_friedmann {a ρ P ρt Pt : ℝ → ℝ} {τ a'' ρ' ρt' κ K : ℝ}
    (hF : ∀ t, (deriv a t / a t) ^ 2 + K / a t ^ 2 = κ * (ρ t + ρt t))
    (ha : DifferentiableAt ℝ a τ) (ha2 : HasDerivAt (deriv a) a'' τ)
    (hρ : HasDerivAt ρ ρ' τ) (hρt : HasDerivAt ρt ρt' τ)
    (ha0 : a τ ≠ 0) (hH : deriv a τ ≠ 0)
    (hcont : ρ' = -3 * (deriv a τ / a τ) * (ρ τ + P τ))
    (hcontt : ρt' = -3 * (deriv a τ / a τ) * (ρt τ + Pt τ)) :
    a'' / a τ = -(κ / 2) * (ρ τ + ρt τ + 3 * (P τ + Pt τ)) := by
  have h1 := ((ha2.fun_div ha.hasDerivAt ha0).fun_pow 2).fun_add
    ((hasDerivAt_const τ K).fun_div (ha.hasDerivAt.fun_pow 2) (pow_ne_zero 2 ha0))
  have h2 : HasDerivAt (fun t ↦ (deriv a t / a t) ^ 2 + K / a t ^ 2) (κ * (ρ' + ρt')) τ := by
    rw [show (fun t ↦ (deriv a t / a t) ^ 2 + K / a t ^ 2) = fun t ↦ κ * (ρ t + ρt t) from
      funext hF]
    exact (hρ.fun_add hρt).const_mul κ
  have hd := h1.unique h2
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_sub] at hd
  have hq := hF τ
  have hdiff : deriv a τ / a τ
      * (2 * (a'' / a τ) + κ * (ρ τ + ρt τ + 3 * (P τ + Pt τ))) = 0 := by
    rw [hcont, hcontt] at hd
    linear_combination (norm := (field_simp; ring)) hd + 2 * (deriv a τ / a τ) * hq
  rcases mul_eq_zero.1 hdiff with h | h
  · exact absurd h (div_ne_zero hH ha0)
  · linarith

namespace BraneCosmology

variable (M : BraneCosmology)

/-- The acceleration equation at time `t`: the second derivative `ä(t)` exists and equals
`-(4π G_N / 3) (ρ + ρ̃ + 3 (P + P̃)) a`. Stated with `HasDerivAt` so that it includes the
existence of `ä`. -/
def AccelAt (t : ℝ) : Prop :=
  HasDerivAt (deriv M.a)
    (-(4 * π * M.c.GN / 3) * (M.ρ t + M.ρt t + 3 * (M.P t + M.Pt t)) * M.a t) t

/-- The Friedmann equation solved for `ȧ²`. -/
lemma deriv_a_sq (t : ℝ) :
    deriv M.a t ^ 2 = 8 * π * M.c.GN / 3 * (M.ρ t + M.ρt t) * M.a t ^ 2 - M.K := by
  have ha := (M.a_pos t).ne'
  have h := M.friedmann t
  field_simp at h
  linear_combination h / 3

/-- `ȧ` is differentiable wherever `H ≠ 0`. The structure only assumes that `a` is
differentiable once. -/
theorem deriv_a_differentiableAt (t : ℝ) (hH : deriv M.a t ≠ 0) :
    DifferentiableAt ℝ (deriv M.a) t :=
  differentiableAt_deriv_of_sq_eq M.a_diff
    ((((M.ρ_diff.add M.ρt_diff).const_mul (8 * π * M.c.GN / 3)).mul (M.a_diff.pow 2)).sub_const
      M.K)
    M.deriv_a_sq hH

/-- **Every brane cosmology obeys the acceleration equation wherever `H ≠ 0`.** -/
theorem accelAt_of_ne (t : ℝ) (hH : deriv M.a t ≠ 0) : M.AccelAt t := by
  have ha := (M.a_pos t).ne'
  have ha2 := (M.deriv_a_differentiableAt t hH).hasDerivAt
  have h := accel_of_friedmann M.friedmann (M.a_diff t) ha2 (M.ρ_diff t).hasDerivAt
    (M.ρt_diff t).hasDerivAt ha hH (M.continuity t) (M.continuity_tilde t)
  unfold AccelAt
  convert ha2 using 1
  rw [div_eq_iff ha] at h
  rw [h]; ring

/-- The acceleration equation in the form `ä/a = -(4π G_N / 3) (ρ + ρ̃ + 3 (P + P̃))`. -/
theorem acceleration (t : ℝ) (hH : deriv M.a t ≠ 0) :
    deriv (deriv M.a) t / M.a t
      = -(4 * π * M.c.GN / 3) * (M.ρ t + M.ρt t + 3 * (M.P t + M.Pt t)) := by
  rw [(M.accelAt_of_ne t hH).deriv, mul_div_assoc, div_self (M.a_pos t).ne', mul_one]

end BraneCosmology

end WhiteHole
