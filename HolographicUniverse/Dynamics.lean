import HolographicUniverse.Bounce
import HolographicUniverse.Singularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Reduction to an ODE (ROADMAP M4.1)

For a barotropic fluid `P = wρ`, a `BraneCosmology` is fixed by one first-order autonomous ODE
for the scale factor, `ȧ² = F(a)`.

* `barotropic_const`, `rho_barotropic`: the continuity equation (12) gives
  `ρ = ρ₀ a^{-3(1+w)}` at every time, with `ρ₀ = ρ(0) a(0)^{3(1+w)}`. This uses no information
  about the branch.
* `branch_fixed`: if the history never reaches the pressure singularity `ρ̃ = ρ̃_s`, then `ρ̃`
  is on one branch `ρ̃_±` of Eq. (26) for all time. The two branches meet only at the
  singularity (`branches_meet_iff`), and `ρ̃` is continuous, so it cannot jump between them.
* `deriv_a_sq_eq`: on a branch `sgn`, the Friedmann equation (11) is `ȧ² = F(a)`, where
  `F = friedmannF` depends only on `a` and the constants of the model.
* `reduction`: the M4.1 statement. Under `P = wρ` and away from the singularity, there is one
  `sgn = ±1` with `ȧ² = F_sgn(a)` at every time.
* `radiationBounce_reduction`: the bounce of `Bounce.lean` is a solution of this ODE, with
  `w = 1/3` and `sgn = +1`.

`F` is not differentiable where the square root in `ρ̃_±` vanishes, which is the pressure
singularity. Away from it, and from `a = 0`, `F` is smooth, and Picard–Lindelöf gives local
solutions (M4.2). A first-order equation `ȧ² = F(a)` does not fix the solution through a turning
point `F(a) = 0`: the constant `a` is a spurious solution there. The second-order equation
`ä = F'(a)/2`, which is the acceleration equation, does fix it (M2.5).
-/

namespace WhiteHole

open Real Set

/-- The right side of `ȧ² = F(a)`, for matter `ρ = ρ₀ a^{-3(1+w)}` on the branch `sgn` of
Eq. (26): `F(a) = (8π G_N/3)(ρ + ρ̃_sgn) a² - 𝒦`. -/
noncomputable def friedmannF (c : Couplings) (K H0 rh w ρ₀ sgn a : ℝ) : ℝ :=
  8 * π * c.GN / 3 * (ρ₀ * a ^ (-(3 * (1 + w)))
    + rhoTilde sgn c.rhoS (rhoBH c.GN K H0 rh a) (ρ₀ * a ^ (-(3 * (1 + w))))) * a ^ 2 - K

/-- The normal branch is at or below `ρ̃_s`. -/
lemma rhoTilde_minus_le {s b ρ : ℝ} (hs : 0 < s) : rhoTilde (-1) s b ρ ≤ s := by
  unfold rhoTilde
  nlinarith [sqrt_nonneg (1 - 2 * (b - ρ) / s)]

/-- The self-accelerating branch is at or above `ρ̃_s`. -/
lemma le_rhoTilde_plus {s b ρ : ℝ} (hs : 0 < s) : s ≤ rhoTilde 1 s b ρ := by
  unfold rhoTilde
  nlinarith [sqrt_nonneg (1 - 2 * (b - ρ) / s)]

namespace BraneCosmology

variable (M : BraneCosmology)

/-- For `P = wρ`, `ρ a^{3(1+w)}` has zero derivative. -/
theorem hasDerivAt_rho_rpow {w : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (t : ℝ) :
    HasDerivAt (fun t ↦ M.ρ t * M.a t ^ (3 * (1 + w))) 0 t := by
  have ha := (M.a_pos t).ne'
  have h := (M.ρ_diff t).hasDerivAt.mul
    ((M.a_diff t).hasDerivAt.rpow_const (p := 3 * (1 + w)) (Or.inl ha))
  convert h using 1
  rw [M.continuity t, hw t, rpow_sub_one ha]
  field_simp
  ring

/-- **`ρ a^{3(1+w)}` is a constant of the history** when `P = wρ`. -/
theorem barotropic_const {w : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (t : ℝ) :
    M.ρ t * M.a t ^ (3 * (1 + w)) = M.ρ 0 * M.a 0 ^ (3 * (1 + w)) :=
  is_const_of_deriv_eq_zero (fun t ↦ (M.hasDerivAt_rho_rpow hw t).differentiableAt)
    (fun t ↦ (M.hasDerivAt_rho_rpow hw t).deriv) t 0

/-- **`ρ = ρ₀ a^{-3(1+w)}`** when `P = wρ`, with `ρ₀ = ρ(0) a(0)^{3(1+w)}`. -/
theorem rho_barotropic {w : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (t : ℝ) :
    M.ρ t = M.ρ 0 * M.a 0 ^ (3 * (1 + w)) * M.a t ^ (-(3 * (1 + w))) := by
  have ha := M.a_pos t
  rw [← M.barotropic_const hw t, rpow_neg ha.le, mul_assoc,
    mul_inv_cancel₀ (rpow_pos_of_pos ha _).ne', mul_one]

/-- **The branch is fixed away from the singularity.** If `ρ̃ ≠ ρ̃_s` at every time, then `ρ̃`
is on the same branch of Eq. (26) at every time. -/
theorem branch_fixed (hns : ∀ t, M.ρt t ≠ M.c.rhoS) :
    (∀ t, M.ρt t = rhoTilde 1 M.c.rhoS (M.rhoBH t) (M.ρ t)) ∨
      ∀ t, M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t) := by
  have hs := M.c.rhoS_pos
  -- `ρ̃ - ρ̃_s` keeps one sign, by the intermediate value theorem.
  have hside : ∀ t₁ t₂, M.c.rhoS < M.ρt t₁ → M.c.rhoS < M.ρt t₂ := by
    intro t₁ t₂ h₁
    by_contra h₂
    push Not at h₂
    have hmem : M.c.rhoS ∈ uIcc (M.ρt t₁) (M.ρt t₂) := by
      rw [mem_uIcc]; right; exact ⟨h₂, h₁.le⟩
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc M.ρt_diff.continuous.continuousOn hmem
    exact hns t ht
  rcases (hns 0).lt_or_gt with h0 | h0
  · right
    intro t
    have hlt : M.ρt t < M.c.rhoS :=
      (le_of_not_gt fun h ↦ (hside t 0 h).not_gt h0).lt_of_ne (hns t)
    refine (M.branches t).resolve_left fun h ↦ ?_
    exact (h ▸ hlt).not_ge (le_rhoTilde_plus hs)
  · left
    intro t
    refine (M.branches t).resolve_right fun h ↦ ?_
    exact (h ▸ hside 0 t h0).not_ge (rhoTilde_minus_le hs)

/-- **The Friedmann equation as an ODE for `a`.** On a branch `sgn`, with `P = wρ`,
`ȧ² = F(a)` at every time. -/
theorem deriv_a_sq_eq {w sgn : ℝ} (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) (t : ℝ) :
    deriv M.a t ^ 2
      = friedmannF M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) sgn (M.a t) := by
  rw [M.deriv_a_sq t, hbr t, M.rho_barotropic hw t]
  rfl

/-- **ROADMAP M4.1.** For `P = wρ`, a history that avoids the pressure singularity solves the
first-order autonomous ODE `ȧ² = F_sgn(a)` at every time, for one fixed branch `sgn = ±1`. -/
theorem reduction {w : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (hns : ∀ t, M.ρt t ≠ M.c.rhoS) :
    ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧ ∀ t, deriv M.a t ^ 2
      = friedmannF M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) sgn (M.a t) := by
  rcases M.branch_fixed hns with h | h
  · exact ⟨1, Or.inl rfl, M.deriv_a_sq_eq hw h⟩
  · exact ⟨-1, Or.inr rfl, M.deriv_a_sq_eq hw h⟩

/-- The bounce of `Bounce.lean` solves `ȧ² = F(a)` for radiation (`w = 1/3`) on the
self-accelerating branch. -/
theorem radiationBounce_reduction {c : Couplings} {K rh : ℝ} (hK : 0 < K) (hrh : 0 ≤ rh)
    (hrc : 2 * rh ≤ c.rc) (t : ℝ) :
    let M := radiationBounce c K rh hK hrh hrc
    deriv M.a t ^ 2
      = friedmannF M.c M.K M.H0 M.rh (1 / 3) (M.ρ 0 * M.a 0 ^ (3 * (1 + 1 / 3 : ℝ))) 1 (M.a t) :=
  (radiationBounce c K rh hK hrh hrc).deriv_a_sq_eq (fun t ↦ by
    change WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t) / 3
      = 1 / 3 * WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t)
    ring) (radiationBounce_selfAccelerating c hK hrh hrc) t

end BraneCosmology

end WhiteHole
