module

public import HolographicUniverse.Dynamics
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-!
# Local existence and uniqueness (ROADMAP M4.2, first-order part)

For a barotropic fluid `P = wρ` on a fixed branch, a brane cosmology solves `ȧ² = F(a)`
(`BraneCosmology.reduction`, M4.1). Where `ȧ ≠ 0`, this is the autonomous first-order ODE
`ȧ = s √F(a)` with a fixed sign `s = ±1`. This file applies Mathlib's Picard–Lindelöf theorem to
it.

* `contDiffAt_friedmannF`: `F` is smooth at every `a ≠ 0` where the square root in `ρ̃_±` has a
  non-zero argument, `realityArg ≠ 0`. That argument is zero exactly at the pressure singularity
  (`BraneCosmology.realityArg_ne`).
* `exists_local_solution`: for initial data `a₀ > 0` away from the singularity, with
  `F(a₀) > 0`, and for either sign `s`, a local solution exists. It has `a > 0` and
  `ȧ² = F(a)` near `t₀`.
* `local_unique`: two local solutions of `ȧ = s √F(a)` with the same initial value agree near
  `t₀`.
* `BraneCosmology.locally_determined`: near a time with `H ≠ 0` and `ρ̃ ≠ ρ̃_s`, the scale factor
  of a brane cosmology is the unique solution of `ȧ = s √F(a)` with its value at that time. So
  the history is fixed locally by `a(t₀)`, the sign of `H(t₀)`, the constants and the branch.

Not covered here:

* Turning points `H = 0`. There `F(a) = 0`, `√F` is not Lipschitz, and the constant `a` is a
  second solution of `ȧ² = F(a)`. Uniqueness there needs the second-order equation
  `ä = F'(a)/2`, which `BraneCosmology.IsSolution` (M2.5) provides as the acceleration equation.
  See `TurningPoint.lean`.
* Global solutions. `BraneCosmology` needs `a` at every time, and a local solution does not
  give that.
-/

namespace WhiteHole

open Real Set Topology

/-- The argument of the square root in `ρ̃_±` (Eq. (26)) as a function of `a`, for matter
`ρ = ρ₀ a^{-3(1+w)}`: `1 - 2(ρ_BH - ρ)/ρ̃_s`. The reality bound (30) is `realityArg ≥ 0`. -/
noncomputable def realityArg (c : Couplings) (K H0 rh w ρ₀ a : ℝ) : ℝ :=
  1 - 2 * (rhoBH c.GN K H0 rh a - ρ₀ * a ^ (-(3 * (1 + w)))) / c.rhoS

/-- `F` written with `realityArg`. -/
theorem friedmannF_eq (c : Couplings) (K H0 rh w ρ₀ sgn a : ℝ) :
    friedmannF c K H0 rh w ρ₀ sgn a = 8 * π * c.GN / 3 * (ρ₀ * a ^ (-(3 * (1 + w)))
      + c.rhoS * (1 + sgn * √(realityArg c K H0 rh w ρ₀ a))) * a ^ 2 - K := rfl

/-- The argument of the square root in `ρ̃_±` is smooth away from `a = 0`. -/
theorem contDiffAt_realityArg {c : Couplings} {K H0 rh w ρ₀ a : ℝ} {n : WithTop ℕ∞}
    (ha : a ≠ 0) : ContDiffAt ℝ n (realityArg c K H0 rh w ρ₀) a := by
  have hGN := c.GN_pos.ne'
  have hs := c.rhoS_pos.ne'
  have hp : ContDiffAt ℝ n (fun a : ℝ ↦ a ^ (-(3 * (1 + w)))) a :=
    contDiffAt_rpow_const_of_ne ha
  unfold realityArg rhoBH
  have : 8 * π * c.GN * a ^ 4 ≠ 0 := by positivity
  fun_prop (disch := assumption)

/-- **`F` is smooth away from `a = 0` and from the pressure singularity.** -/
theorem contDiffAt_friedmannF {c : Couplings} {K H0 rh w ρ₀ sgn a : ℝ} {n : WithTop ℕ∞}
    (ha : a ≠ 0) (hD : realityArg c K H0 rh w ρ₀ a ≠ 0) :
    ContDiffAt ℝ n (friedmannF c K H0 rh w ρ₀ sgn) a := by
  have hp : ContDiffAt ℝ n (fun a : ℝ ↦ a ^ (-(3 * (1 + w)))) a :=
    contDiffAt_rpow_const_of_ne ha
  have := (contDiffAt_realityArg (c := c) (K := K) (H0 := H0) (rh := rh) (w := w) (ρ₀ := ρ₀)
    (n := n) ha).sqrt hD
  simp only [funext (friedmannF_eq c K H0 rh w ρ₀ sgn)]
  fun_prop

/-- The vector field `a ↦ s √F(a)` is `C¹` where `F ≠ 0`, so Picard–Lindelöf applies. -/
theorem contDiffAt_field {c : Couplings} {K H0 rh w ρ₀ sgn a s : ℝ}
    (ha : a ≠ 0) (hD : realityArg c K H0 rh w ρ₀ a ≠ 0)
    (hF : friedmannF c K H0 rh w ρ₀ sgn a ≠ 0) :
    ContDiffAt ℝ 1 (fun x ↦ s * √(friedmannF c K H0 rh w ρ₀ sgn x)) a :=
  contDiffAt_const.mul ((contDiffAt_friedmannF (n := 1) ha hD).sqrt hF)

/-- **Local existence.** For `a₀ > 0` away from the pressure singularity with `F(a₀) > 0`, and
for either sign `s = ±1`, there is a solution of `ȧ = s √F(a)` with `a(t₀) = a₀`. Near `t₀` it has
`a > 0` and solves `ȧ² = F(a)`. -/
theorem exists_local_solution {c : Couplings} {K H0 rh w ρ₀ sgn a₀ s : ℝ}
    (hs : s = 1 ∨ s = -1) (ha : 0 < a₀) (hD : realityArg c K H0 rh w ρ₀ a₀ ≠ 0)
    (hF : 0 < friedmannF c K H0 rh w ρ₀ sgn a₀) (t₀ : ℝ) :
    ∃ α : ℝ → ℝ, α t₀ = a₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < α t
      ∧ HasDerivAt α (s * √(friedmannF c K H0 rh w ρ₀ sgn (α t))) t
      ∧ deriv α t ^ 2 = friedmannF c K H0 rh w ρ₀ sgn (α t) := by
  set F := friedmannF c K H0 rh w ρ₀ sgn
  obtain ⟨α, hα0, ε, hε, hα⟩ := (contDiffAt_field (s := s) ha.ne' hD
    hF.ne').exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  refine ⟨α, hα0, ?_⟩
  have hI : Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : ContinuousAt α t₀ := (hα t₀ ⟨by linarith, by linarith⟩).continuousAt
  have hFc : ContinuousAt F a₀ := (contDiffAt_friedmannF (n := 0) ha.ne' hD).continuousAt
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < α t :=
    hcont.eventually (lt_mem_nhds (hα0 ▸ ha))
  have hFpos : ∀ᶠ t in 𝓝 t₀, 0 < F (α t) :=
    (hα0 ▸ hFc).comp hcont |>.eventually (lt_mem_nhds (by simpa [hα0] using hF))
  filter_upwards [hI, hpos, hFpos] with t ht hp hf
  refine ⟨hp, hα t ht, ?_⟩
  rw [(hα t ht).deriv, mul_pow, sq_sqrt hf.le]
  rcases hs with rfl | rfl <;> simp

/-- **Local uniqueness.** Two solutions of `ȧ = s √F(a)` near `t₀` with the same value
`a₀ > 0` at `t₀` agree near `t₀`, if `a₀` is away from the singularity and `F(a₀) ≠ 0`. -/
theorem local_unique {c : Couplings} {K H0 rh w ρ₀ sgn a₀ s t₀ : ℝ} {f g : ℝ → ℝ}
    (ha : 0 < a₀) (hD : realityArg c K H0 rh w ρ₀ a₀ ≠ 0)
    (hF : friedmannF c K H0 rh w ρ₀ sgn a₀ ≠ 0)
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (s * √(friedmannF c K H0 rh w ρ₀ sgn (f t))) t)
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (s * √(friedmannF c K H0 rh w ρ₀ sgn (g t))) t)
    (hf0 : f t₀ = a₀) (hg0 : g t₀ = a₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨L, U, hU, hL⟩ := (contDiffAt_field (s := s) ha.ne' hD hF).exists_lipschitzOnWith
  have hfU : ∀ᶠ t in 𝓝 t₀, f t ∈ U :=
    hf.self_of_nhds.continuousAt.preimage_mem_nhds (hf0 ▸ hU)
  have hgU : ∀ᶠ t in 𝓝 t₀, g t ∈ U :=
    hg.self_of_nhds.continuousAt.preimage_mem_nhds (hg0 ▸ hU)
  exact ODE_solution_unique_of_eventually (s := fun _ ↦ U)
    (Filter.Eventually.of_forall fun _ ↦ hL) (hf.and hfU) (hg.and hgU) (hf0.trans hg0.symm)

/-- **The sign of `ȧ` is locally fixed.** If `ȧ² = g` with `g` continuous at `τ` and
`s ȧ(τ) > 0`, then `ȧ = s √g` near `τ`. A derivative has the intermediate value property
(Darboux), and `ȧ ≠ 0` near `τ`. -/
theorem deriv_eventuallyEq_sqrt {a g : ℝ → ℝ} {τ s : ℝ} (hs : s = 1 ∨ s = -1)
    (ha : Differentiable ℝ a) (hg : ContinuousAt g τ) (hsq : ∀ t, deriv a t ^ 2 = g t)
    (hτ : 0 < s * deriv a τ) : deriv a =ᶠ[𝓝 τ] fun t ↦ s * √(g t) := by
  have hne0 : deriv a τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hgτ : 0 < g τ := by rw [← hsq]; positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hg.eventually (lt_mem_nhds hgτ))
  have hne : ∀ x ∈ Metric.ball τ δ, deriv a x ≠ 0 := fun x hx h0 ↦ by
    have := hball x hx
    rw [← hsq, h0] at this
    simp at this
  have hmem : Metric.ball τ δ ∈ 𝓝 τ := Metric.ball_mem_nhds τ hδ
  have hτb : τ ∈ Metric.ball τ δ := Metric.mem_ball_self hδ
  filter_upwards [hmem] with x hx
  rw [← hsq, sqrt_sq_eq_abs]
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_ball τ δ)
    (fun x _ ↦ (ha x).hasDerivAt.hasDerivWithinAt) hne with h | h
  · have := h τ hτb
    rcases hs with rfl | rfl
    · linarith
    · rw [abs_of_neg (h x hx)]; ring
  · have := h τ hτb
    rcases hs with rfl | rfl
    · rw [abs_of_pos (h x hx)]; ring
    · linarith

namespace BraneCosmology

variable (M : BraneCosmology)

/-- Away from the pressure singularity the argument of the square root is not zero. -/
theorem realityArg_ne {w sgn : ℝ} (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) {t : ℝ}
    (hns : M.ρt t ≠ M.c.rhoS) :
    realityArg M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) (M.a t) ≠ 0 := by
  intro h0
  apply hns
  rw [hbr t, M.rho_barotropic hw t]
  change M.c.rhoS * (1 + sgn * √(realityArg M.c M.K M.H0 M.rh w
    (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) (M.a t))) = M.c.rhoS
  rw [h0]; simp

/-- **ROADMAP M4.2, first-order part.** Take `P = wρ`, a fixed branch `sgn`, and a time `t₀`
with `s H(t₀) > 0` and `ρ̃(t₀) ≠ ρ̃_s`. Then every solution `f` of `ȧ = s √F(a)` near `t₀` with
`f(t₀) = a(t₀)` is equal to the scale factor near `t₀`. -/
theorem locally_determined {w sgn s : ℝ} (hs : s = 1 ∨ s = -1) (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) {t₀ : ℝ}
    (hH : 0 < s * deriv M.a t₀) (hns : M.ρt t₀ ≠ M.c.rhoS) {f : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f
      (s * √(friedmannF M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) sgn (f t))) t)
    (hf0 : f t₀ = M.a t₀) : f =ᶠ[𝓝 t₀] M.a := by
  set F := friedmannF M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) sgn
  have hD := M.realityArg_ne hw hbr hns
  have hsq : ∀ t, deriv M.a t ^ 2 = F (M.a t) := M.deriv_a_sq_eq hw hbr
  have hne0 : deriv M.a t₀ ≠ 0 := fun h ↦ by simp [h] at hH
  have hF : F (M.a t₀) ≠ 0 := by rw [← hsq]; positivity
  have hFc : ContinuousAt (fun t ↦ F (M.a t)) t₀ :=
    (contDiffAt_friedmannF (n := 0) (M.a_pos t₀).ne' hD).continuousAt.comp
      (M.a_diff t₀).continuousAt
  have heq := deriv_eventuallyEq_sqrt hs M.a_diff hFc hsq hH
  have hM : ∀ᶠ t in 𝓝 t₀, HasDerivAt M.a (s * √(F (M.a t))) t := by
    filter_upwards [heq] with t ht
    rw [← ht]; exact (M.a_diff t).hasDerivAt
  exact local_unique (M.a_pos t₀) hD hF hf hM hf0 rfl

end BraneCosmology

end WhiteHole
