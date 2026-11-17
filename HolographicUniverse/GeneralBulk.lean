import HolographicUniverse.Pressure

/-!
# A brane cosmology in a general static bulk (ROADMAP M5.1)

`BulkCosmology` is `BraneCosmology` with the Schwarzschild blackening factor replaced by any
`f : ℝ → ℝ`. The bulk metric is `ds² = -f dt² + dr²/f + r² dΩ₃²`, and the brane sits at
`r = a/√𝒦`. The embedding computation (24) then puts `H² + 𝒦 f(r)/a²` under the square root.

Everything that uses `f` only through the junction condition holds for every `f`:

* `isInduced`, `reality`, `branches`: Eqs. (26) and (30), with `ρ_BH` replaced by the bulk
  density `ρ_bulk` of `rhoBulk`;
* `pressure`: Eq. (16) in the general form `pressureTildeBulk`, given the pressure `P_b` of the
  bulk density;
* `ρt_nonneg`: `ε = -1` forces `ρ̃ ≥ 0`;
* `singularity_iff`, `singularity_inside_iff` and its variants: the pressure singularity is the
  equality case of (30), and it is on or inside the horizon (`f ≤ 0` at the brane) exactly when
  `|H| ≥ 1/(2 r_c)`. So README issue 7 is a property of every bulk of this form.

`BraneCosmology.toBulk` (in `Model.lean`) is the Schwarzschild case, and the results for
`BraneCosmology` are derived from these.
-/

namespace WhiteHole

open Real

/-- A homogeneous brane cosmology in a static bulk with blackening factor `f`. -/
structure BulkCosmology where
  c : Couplings
  /-- Spatial curvature `𝒦 > 0` of the closed FRW slicing, Eq. (3). -/
  K : ℝ
  /-- Blackening factor of the bulk metric, a function of the areal radius. -/
  f : ℝ → ℝ
  /-- Orientation of the brane normal, Eq. (21). -/
  ε : ℝ
  a : ℝ → ℝ
  ρ : ℝ → ℝ
  P : ℝ → ℝ
  ρt : ℝ → ℝ
  Pt : ℝ → ℝ
  K_pos : 0 < K
  ε_sq : ε ^ 2 = 1
  a_pos : ∀ t, 0 < a t
  a_diff : Differentiable ℝ a
  ρ_diff : Differentiable ℝ ρ
  ρt_diff : Differentiable ℝ ρt
  /-- Friedmann equation, Eq. (11). -/
  friedmann : ∀ t, (deriv a t / a t) ^ 2 + K / a t ^ 2 = 8 * π * c.GN / 3 * (ρ t + ρt t)
  /-- Matter continuity, Eq. (12). -/
  continuity : ∀ t, deriv ρ t = -3 * (deriv a t / a t) * (ρ t + P t)
  /-- Induced-fluid continuity, Eq. (13). -/
  continuity_tilde : ∀ t, deriv ρt t = -3 * (deriv a t / a t) * (ρt t + Pt t)
  /-- Spatial junction condition: Eq. (10) equated with Eq. (24) for a general `f`. -/
  junction : ∀ t, ε * √((deriv a t / a t) ^ 2 + K / a t ^ 2 * f (braneRadius K (a t)))
    = -(8 * π * c.Gb / 3) * ρt t
  /-- The brane's 4-velocity (22) is real. -/
  junction_arg : ∀ t, 0 ≤ (deriv a t / a t) ^ 2 + K / a t ^ 2 * f (braneRadius K (a t))

/-- `f ≤ 0` is unchanged by a positive factor. -/
lemma nonpos_iff_mul {c f : ℝ} (hc : 0 < c) : f ≤ 0 ↔ c * f ≤ 0 := by
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith [mul_pos hc h']

/-- `f < 0` is unchanged by a positive factor. -/
lemma neg_iff_mul {c f : ℝ} (hc : 0 < c) : f < 0 ↔ c * f < 0 := by
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; push Not at h'; nlinarith [mul_nonneg hc.le h']

namespace BulkCosmology

variable (M : BulkCosmology)

/-- Hubble rate `H = ȧ/a`. -/
noncomputable def H (t : ℝ) : ℝ := deriv M.a t / M.a t

/-- The blackening factor at the brane. The brane is on or inside a horizon when this is
`≤ 0`. -/
noncomputable def fBrane (t : ℝ) : ℝ := M.f (braneRadius M.K (M.a t))

/-- The bulk density on the brane, `ρ_bulk(t)`. -/
noncomputable def rhoBulk (t : ℝ) : ℝ := WhiteHole.rhoBulk M.c.GN M.K M.f (M.a t)

/-- **Eq. (26) before solving, for any bulk.** -/
theorem isInduced (t : ℝ) : IsInduced M.c.rhoS (M.rhoBulk t) (M.ρ t) (M.ρt t) :=
  isInduced_of_junction_f M.c M.f M.ε_sq (M.friedmann t) (M.junction t) (M.junction_arg t)

/-- **Reality, Eq. (30), for any bulk.** -/
theorem reality (t : ℝ) : 2 * (M.rhoBulk t - M.ρ t) ≤ M.c.rhoS :=
  WhiteHole.reality M.c.rhoS_pos (M.isInduced t)

/-- **Eq. (26) for any bulk.** At every time the induced density is on one of the two
branches. -/
theorem branches (t : ℝ) :
    M.ρt t = rhoTilde 1 M.c.rhoS (M.rhoBulk t) (M.ρ t) ∨
      M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBulk t) (M.ρ t) :=
  (isInduced_iff M.c.rhoS_pos (M.reality t)).1 (M.isInduced t)

/-- **Eq. (16) for any bulk.** Suppose the bulk density has derivative `b'` at `t`, and define
its pressure `P_b` by the continuity equation `b' = -3H(ρ_bulk + P_b)`. Away from `H = 0` and
from the pressure singularity, `P̃ = (ρ̃² - 2ρ̃_s(P - P_b)) / (2(ρ̃_s - ρ̃))`. -/
theorem pressure (t : ℝ) (hH : deriv M.a t ≠ 0) (hsing : M.ρt t ≠ M.c.rhoS) {b' Pb : ℝ}
    (hb : HasDerivAt M.rhoBulk b' t) (hcontb : b' = -3 * M.H t * (M.rhoBulk t + Pb)) :
    M.Pt t = pressureTildeBulk M.c.rhoS (M.ρt t) (M.P t - Pb) :=
  pressure_of_continuity_bulk M.isInduced hb (M.ρ_diff t).hasDerivAt
    (M.ρt_diff t).hasDerivAt (M.a_pos t).ne' hH hsing (M.continuity t) (M.continuity_tilde t)
    hcontb

/-- With `ε = -1`, the induced density is non-negative, for any bulk. -/
theorem ρt_nonneg (hε : M.ε = -1) (t : ℝ) : 0 ≤ M.ρt t :=
  rhoTilde_nonneg_of_eps_neg M.c.Gb_pos (hε ▸ M.junction t)

/-- **The pressure singularity is the equality case of (30), for any bulk.** -/
theorem singularity_iff (t : ℝ) :
    M.ρt t = M.c.rhoS ↔ 2 * (M.rhoBulk t - M.ρ t) = M.c.rhoS :=
  isInduced_eq_rhoS_iff M.c.rhoS_pos (M.isInduced t)

/-- At the singularity, `(𝒦/a²) f(r) = 1/(2 r_c)² - H²`, for any `f`. -/
theorem f_at_singularity {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    M.K / M.a t ^ 2 * M.fBrane t = (1 / (2 * M.c.rc)) ^ 2 - M.H t ^ 2 := by
  have hJ := M.junction t
  have hArg := M.junction_arg t
  rw [h] at hJ
  have h2 := congrArg (· ^ 2) hJ
  simp only [mul_pow, sq_sqrt hArg, M.ε_sq, one_mul, neg_sq] at h2
  rw [fBrane, H, ← M.c.g_mul_rhoS]
  linarith

/-- **The horizon condition at the singularity, for any bulk.** At the pressure singularity
the brane is on or inside a horizon (`f ≤ 0` at the brane) exactly when `|H| ≥ 1/(2 r_c)`. -/
theorem singularity_inside_iff {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    M.fBrane t ≤ 0 ↔ 1 / (2 * M.c.rc) ≤ |M.H t| := by
  have hKa : 0 < M.K / M.a t ^ 2 := div_pos M.K_pos (pow_pos (M.a_pos t) 2)
  have hr : 0 ≤ 1 / (2 * M.c.rc) := by have := M.c.rc_pos; positivity
  rw [nonpos_iff_mul hKa, M.f_at_singularity h, sub_nonpos, sq_le_sq, abs_of_nonneg hr]

/-- At the pressure singularity the brane is strictly inside a horizon exactly when
`|H| > 1/(2 r_c)`, for any bulk. -/
theorem singularity_strictly_inside_iff {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    M.fBrane t < 0 ↔ 1 / (2 * M.c.rc) < |M.H t| := by
  have hKa : 0 < M.K / M.a t ^ 2 := div_pos M.K_pos (pow_pos (M.a_pos t) 2)
  have hr : 0 ≤ 1 / (2 * M.c.rc) := by have := M.c.rc_pos; positivity
  rw [neg_iff_mul hKa, M.f_at_singularity h, sub_neg, sq_lt_sq, abs_of_nonneg hr]

/-- **The horizon condition in densities, for any bulk.** At the pressure singularity the
brane is on or inside a horizon exactly when `𝒦/a² ≤ (8π G_N/3)(ρ + ρ̃_s/2)`. -/
theorem singularity_inside_iff_curvature {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    M.fBrane t ≤ 0 ↔ M.K / M.a t ^ 2 ≤ 8 * π * M.c.GN / 3 * (M.ρ t + M.c.rhoS / 2) := by
  have hKa : 0 < M.K / M.a t ^ 2 := div_pos M.K_pos (pow_pos (M.a_pos t) 2)
  have hF := M.friedmann t
  rw [h] at hF
  have hκ := M.c.gN_mul_rhoS
  rw [nonpos_iff_mul hKa, M.f_at_singularity h, H]
  constructor <;> intro h' <;> nlinarith

/-- **The horizon condition at early times, for any bulk.** If `r_c ≥ L`, a pressure
singularity at a time with `|H| ≥ 1/(2L)` is on or inside a horizon. -/
theorem singularity_inside_of_rc {t L : ℝ} (h : M.ρt t = M.c.rhoS) (hL : 0 < L)
    (hrc : L ≤ M.c.rc) (hH : 1 / (2 * L) ≤ |M.H t|) : M.fBrane t ≤ 0 := by
  refine (M.singularity_inside_iff h).2 (le_trans ?_ hH)
  gcongr

end BulkCosmology

end WhiteHole
