module

public import HolographicUniverse.GeneralBulk

@[expose] public section

/-!
# A brane cosmology in the 5D Schwarzschild bulk

`BraneCosmology` bundles the assumptions of Secs. 2–3 as fields. The geometric inputs (the
Brown–York junction condition with `Z₂` symmetry, the Gauss–Codazzi constraints (7)–(8), and the
embedding computation of the extrinsic curvature (24)) appear as hypotheses. Deriving them from
the action (1) would need pseudo-Riemannian hypersurface geometry that Mathlib does not have yet.
Replacing these fields with theorems is the main open direction of the project.

`BraneCosmology.toBulk` views a `BraneCosmology` as a `BulkCosmology` with `f = 1 - r_h²/r²`
(ROADMAP M5.1). The quadratic (26) and the sign of `ρ̃` are derived here from the general-bulk
results, using `ρ_bulk = ρ_BH` (`toBulk_rhoBulk`).
-/

namespace WhiteHole

open Real

/-- A homogeneous brane cosmology in a 5D Schwarzschild bulk (Secs. 2–3). -/
structure BraneCosmology where
  c : Couplings
  /-- Spatial curvature `𝒦 > 0` of the closed FRW slicing, Eq. (3). -/
  K : ℝ
  H0 : ℝ
  /-- Bulk horizon radius, Eq. (20). -/
  rh : ℝ
  /-- Orientation of the brane normal, Eq. (21). -/
  ε : ℝ
  a : ℝ → ℝ
  ρ : ℝ → ℝ
  P : ℝ → ℝ
  ρt : ℝ → ℝ
  Pt : ℝ → ℝ
  K_pos : 0 < K
  H0_pos : 0 < H0
  rh_nonneg : 0 ≤ rh
  ε_sq : ε ^ 2 = 1
  a_pos : ∀ t, 0 < a t
  a_diff : Differentiable ℝ a
  ρ_diff : Differentiable ℝ ρ
  ρt_diff : Differentiable ℝ ρt
  /-- Friedmann equation, Eq. (11). -/
  friedmann : ∀ t, (deriv a t / a t) ^ 2 + K / a t ^ 2 = 8 * π * c.GN / 3 * (ρ t + ρt t)
  /-- Matter continuity, Eq. (12). -/
  continuity : ∀ t, deriv ρ t = -3 * (deriv a t / a t) * (ρ t + P t)
  /-- Induced-fluid continuity, Eq. (13) (from the momentum constraint (7)). -/
  continuity_tilde : ∀ t, deriv ρt t = -3 * (deriv a t / a t) * (ρt t + Pt t)
  /-- Spatial junction condition: Eq. (10) equated with the embedding result Eq. (24). -/
  junction : ∀ t, ε * √((deriv a t / a t) ^ 2 + K / a t ^ 2 - K ^ 2 * rh ^ 2 / a t ^ 4)
    = -(8 * π * c.Gb / 3) * ρt t
  /-- The brane's 4-velocity (22) is real. -/
  junction_arg : ∀ t, 0 ≤ (deriv a t / a t) ^ 2 + K / a t ^ 2 - K ^ 2 * rh ^ 2 / a t ^ 4

namespace BraneCosmology

variable (M : BraneCosmology)

/-- Hubble rate `H = ȧ/a`. -/
noncomputable def H (t : ℝ) : ℝ := deriv M.a t / M.a t

/-- `ρ_BH(t)`, Eq. (28). -/
noncomputable def rhoBH (t : ℝ) : ℝ := WhiteHole.rhoBH M.c.GN M.K M.H0 M.rh (M.a t)

/-- The Schwarzschild bulk as a special case of the general bulk: `f = 1 - r_h²/r²`. -/
noncomputable def toBulk : BulkCosmology where
  c := M.c
  K := M.K
  f := blacken M.rh
  ε := M.ε
  a := M.a
  ρ := M.ρ
  P := M.P
  ρt := M.ρt
  Pt := M.Pt
  K_pos := M.K_pos
  ε_sq := M.ε_sq
  a_pos := M.a_pos
  a_diff := M.a_diff
  ρ_diff := M.ρ_diff
  ρt_diff := M.ρt_diff
  friedmann := M.friedmann
  continuity := M.continuity
  continuity_tilde := M.continuity_tilde
  junction := fun t ↦ by
    rw [curv_mul_blacken M.K_pos (M.a_pos t).ne', ← add_sub_assoc]; exact M.junction t
  junction_arg := fun t ↦ by
    rw [curv_mul_blacken M.K_pos (M.a_pos t).ne', ← add_sub_assoc]; exact M.junction_arg t

/-- For the Schwarzschild bulk, the bulk density is `ρ_BH`. -/
theorem toBulk_rhoBulk (t : ℝ) : M.toBulk.rhoBulk t = M.rhoBH t :=
  rhoBulk_blacken M.c.GN_pos.ne' M.K_pos (M.a_pos t).ne' M.H0_pos.ne'

/-- At the brane, the general blackening factor is `1 - r_h²/r²`. -/
theorem toBulk_fBrane (t : ℝ) : M.toBulk.fBrane t = blacken M.rh (braneRadius M.K (M.a t)) :=
  rfl

theorem isInduced (t : ℝ) : IsInduced M.c.rhoS (M.rhoBH t) (M.ρ t) (M.ρt t) :=
  M.toBulk_rhoBulk t ▸ M.toBulk.isInduced t

/-- **Reality, Eq. (30)**, holds at all times. -/
theorem reality (t : ℝ) : 2 * (M.rhoBH t - M.ρ t) ≤ M.c.rhoS :=
  WhiteHole.reality M.c.rhoS_pos (M.isInduced t)

/-- **Eq. (26).** At every time the induced density sits on one of the two branches. -/
theorem branches (t : ℝ) :
    M.ρt t = rhoTilde 1 M.c.rhoS (M.rhoBH t) (M.ρ t) ∨
      M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t) :=
  (isInduced_iff M.c.rhoS_pos (M.reality t)).1 (M.isInduced t)

/-- **Eq. (16).** Away from `H = 0` and from the pressure singularity `ρ̃ = ρ̃_s`, the induced
pressure is fixed by the matter content. -/
theorem pressure (t : ℝ) (hH : deriv M.a t ≠ 0) (hsing : M.ρt t ≠ M.c.rhoS) :
    M.Pt t = pressureTilde M.c.rhoS (M.ρt t) (3 * M.P t - M.ρ t) := by
  have hC : ∀ t, M.rhoBH t = WhiteHole.rhoBH M.c.GN M.K M.H0 M.rh 1 / M.a t ^ 4 :=
    fun t ↦ rhoBH_scaling M.H0_pos.ne'
  refine pressure_of_continuity (fun t ↦ hC t ▸ M.isInduced t)
    (M.a_diff t).hasDerivAt (M.ρ_diff t).hasDerivAt (M.ρt_diff t).hasDerivAt
    (M.a_pos t).ne' hH hsing (M.continuity t) (M.continuity_tilde t)

/-- With the paper's orientation `ε = -1`, the induced density is non-negative. -/
theorem ρt_nonneg (hε : M.ε = -1) (t : ℝ) : 0 ≤ M.ρt t :=
  M.toBulk.ρt_nonneg hε t

end BraneCosmology

end WhiteHole
