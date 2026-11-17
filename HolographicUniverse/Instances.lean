import HolographicUniverse.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Non-vacuity: explicit brane cosmologies (ROADMAP M2.1)

Every theorem about `BraneCosmology` would be vacuous if the fields of the structure
contradicted each other. This file rules that out by building instances:

* `BraneCosmology.static`: a family of static branes (`a = 1`) at fixed bulk radius `1/√𝒦`,
  for every coupling, either orientation `ε = ±1`, and every horizon radius with the brane on or
  outside the horizon (`𝒦 r_h² ≤ 1`).
* `BraneCosmology.deSitter`: the self-accelerating DGP vacuum in closed slicing,
  `a(t) = r_c cosh(t / r_c)`, with no matter and a flat bulk (`r_h = 0`).

**Caveat on the static family.** `BraneCosmology` contains the Friedmann equation and the two
continuity equations, but not the acceleration equation. When `H ≠ 0` the acceleration equation
follows from those three. When `H = 0` at all times it does not, and the continuity equations
hold for *any* pressure. The static instances therefore show that the fields are jointly
satisfiable, but they are not claimed to solve the full brane equations of motion: that would
fix `P` and `P̃`, which are set to zero here. The de Sitter instance has `H ≠ 0` for `t ≠ 0` and
is a real solution.
-/

namespace WhiteHole

open Real

/-- The normal branch is the root of the quadratic that lies at or below `ρ̃_s`. -/
theorem isInduced_normal_iff {s b ρ x : ℝ} (hs : 0 < s) (hreal : 2 * (b - ρ) ≤ s) :
    IsInduced s b ρ x ∧ x ≤ s ↔ x = rhoTilde (-1) s b ρ := by
  have hsqrt := sqrt_nonneg (1 - 2 * (b - ρ) / s)
  rw [isInduced_iff hs hreal]
  unfold rhoTilde
  constructor
  · rintro ⟨h | h, hle⟩
    · have h0 : √(1 - 2 * (b - ρ) / s) = 0 := by
        rw [h] at hle
        nlinarith
      rw [h, h0]; ring
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rw [h]
    nlinarith

namespace BraneCosmology

/-! ### Static branes -/

/-- A static brane at bulk radius `1/√𝒦`, on or outside the horizon. The junction condition
fixes `ρ̃ = -ε · 3√(𝒦 - 𝒦² r_h²) / (8π G_b)` and the Friedmann equation then fixes `ρ`.
See the module docstring for why `P` and `P̃` are unconstrained. -/
noncomputable def static (c : Couplings) (K rh ε : ℝ) (hK : 0 < K) (hrh : 0 ≤ rh)
    (hε : ε ^ 2 = 1) (hout : K * rh ^ 2 ≤ 1) : BraneCosmology where
  c := c
  K := K
  H0 := 1
  rh := rh
  ε := ε
  a := fun _ ↦ 1
  ρ := fun _ ↦ 3 * K / (8 * π * c.GN) + ε * (3 * √(K - K ^ 2 * rh ^ 2) / (8 * π * c.Gb))
  P := fun _ ↦ 0
  ρt := fun _ ↦ -ε * (3 * √(K - K ^ 2 * rh ^ 2) / (8 * π * c.Gb))
  Pt := fun _ ↦ 0
  K_pos := hK
  H0_pos := one_pos
  rh_nonneg := hrh
  ε_sq := hε
  a_pos := fun _ ↦ one_pos
  a_diff := differentiable_const _
  ρ_diff := differentiable_const _
  ρt_diff := differentiable_const _
  friedmann := fun _ ↦ by
    have := c.GN_pos; have := c.Gb_pos
    simp only [deriv_const]
    field_simp
    ring
  continuity := fun _ ↦ by simp
  continuity_tilde := fun _ ↦ by simp
  junction := fun _ ↦ by
    have := c.Gb_pos
    simp only [deriv_const, one_pow, div_one]
    rw [show (0 : ℝ) ^ 2 + K - K ^ 2 * rh ^ 2 = K - K ^ 2 * rh ^ 2 by ring]
    field_simp
  junction_arg := fun _ ↦ by
    simp only [deriv_const, one_pow, div_one]
    nlinarith [mul_nonneg hK.le (sub_nonneg.2 hout)]

/-- **Non-vacuity.** The fields of `BraneCosmology` are jointly satisfiable. -/
theorem nonempty : Nonempty BraneCosmology :=
  ⟨static ⟨1, 1, one_pos, one_pos⟩ 1 0 (-1) one_pos le_rfl (by norm_num) (by norm_num)⟩

/-- **The structure does not exclude the paper's setting.** There is an instance with the paper's
orientation `ε = -1`, a bulk black hole (`r_h > 0`), positive matter density, positive induced
density, and `ρ̃` on the normal branch. By `normal_branch_requires` any such instance has
`ρ ≤ ρ_BH`. The witness is static (`𝒦 = 1`, `r_h = 12/13`, `G_N = G_b = 1`), so the caveat in the
module docstring applies: an expanding witness needs ROADMAP M2.2. -/
theorem exists_normal_branch_eps_neg :
    ∃ M : BraneCosmology, M.ε = -1 ∧ 0 < M.rh ∧ ∀ t, 0 < M.ρ t ∧ 0 < M.ρt t ∧
      M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t) := by
  let M := static ⟨1, 1, one_pos, one_pos⟩ 1 (12 / 13) (-1) one_pos (by norm_num) (by norm_num)
    (by norm_num)
  have hsqrt : √((1 : ℝ) - 1 ^ 2 * (12 / 13) ^ 2) = 5 / 13 := by
    rw [show (1 : ℝ) - 1 ^ 2 * (12 / 13) ^ 2 = (5 / 13) ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  have hρt : ∀ t, M.ρt t = 15 / (104 * π) := fun t ↦ by
    change -(-1 : ℝ) * (3 * √((1 : ℝ) - 1 ^ 2 * (12 / 13) ^ 2) / (8 * π * 1)) = _
    rw [hsqrt]; field_simp; norm_num
  have hρ : ∀ t, M.ρ t = 24 / (104 * π) := fun t ↦ by
    change 3 * 1 / (8 * π * 1) + (-1 : ℝ) * (3 * √((1 : ℝ) - 1 ^ 2 * (12 / 13) ^ 2) / (8 * π * 1))
      = _
    rw [hsqrt]; field_simp; norm_num
  have hs : M.c.rhoS = 3 / (16 * π) := by
    change 3 * (1 : ℝ) / (16 * π * 1 ^ 2) = _
    norm_num
  refine ⟨M, rfl, by change (0 : ℝ) < 12 / 13; norm_num, fun t ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [hρ]; positivity
  · rw [hρt]; positivity
  · refine (isInduced_normal_iff M.c.rhoS_pos (M.reality t)).1 ⟨M.isInduced t, ?_⟩
    rw [hρt, hs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pi_pos]

/-! ### The self-accelerating de Sitter vacuum -/

private lemma hasDerivAt_dS {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ r * cosh (t / r)) (sinh (t / r)) t := by
  have h := ((hasDerivAt_cosh (t / r)).comp t ((hasDerivAt_id t).div_const r)).const_mul r
  exact h.congr_deriv (by field_simp)

/-- For `a = r cosh(t/r)` and `𝒦 = 1`, `H² + 𝒦/a² = 1/r²` at all times. -/
private lemma dS_hubble {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (deriv (fun t ↦ r * cosh (t / r)) t / (r * cosh (t / r))) ^ 2 + 1 / (r * cosh (t / r)) ^ 2
      = 1 / r ^ 2 := by
  have hc := cosh_pos (t / r)
  rw [(hasDerivAt_dS hr.ne' t).deriv, div_pow, ← add_div, ← cosh_sq, mul_pow]
  field_simp

/-- **The self-accelerating DGP vacuum** in closed slicing: `a(t) = r_c cosh(t / r_c)`, `𝒦 = 1`,
no matter, flat bulk (`r_h = 0`), orientation `ε = -1`. The induced fluid is a cosmological
constant, `ρ̃ = -P̃ = 2 ρ̃_s`, and `H² + 𝒦/a² = 1/r_c²`. Exists for every choice of couplings. -/
noncomputable def deSitter (c : Couplings) : BraneCosmology where
  c := c
  K := 1
  H0 := 1
  rh := 0
  ε := -1
  a := fun t ↦ c.rc * cosh (t / c.rc)
  ρ := fun _ ↦ 0
  P := fun _ ↦ 0
  ρt := fun _ ↦ 2 * c.rhoS
  Pt := fun _ ↦ -(2 * c.rhoS)
  K_pos := one_pos
  H0_pos := one_pos
  rh_nonneg := le_rfl
  ε_sq := by norm_num
  a_pos := fun t ↦ mul_pos c.rc_pos (cosh_pos _)
  a_diff := fun t ↦ (hasDerivAt_dS c.rc_pos.ne' t).differentiableAt
  ρ_diff := differentiable_const _
  ρt_diff := differentiable_const _
  friedmann := fun t ↦ by
    have := c.GN_pos; have := c.Gb_pos
    rw [dS_hubble c.rc_pos t]
    unfold Couplings.rc Couplings.rhoS
    field_simp
    ring
  continuity := fun _ ↦ by simp
  continuity_tilde := fun _ ↦ by simp
  junction := fun t ↦ by
    have := c.GN_pos; have := c.Gb_pos
    have hrc := c.rc_pos
    rw [show (deriv (fun t ↦ c.rc * cosh (t / c.rc)) t / (c.rc * cosh (t / c.rc))) ^ 2
        + 1 / (c.rc * cosh (t / c.rc)) ^ 2 - 1 ^ 2 * 0 ^ 2 / (c.rc * cosh (t / c.rc)) ^ 4
        = (1 / c.rc) ^ 2 by linear_combination dS_hubble hrc t,
      sqrt_sq (by positivity)]
    unfold Couplings.rc Couplings.rhoS
    field_simp
    ring
  junction_arg := fun t ↦ by
    rw [show (deriv (fun t ↦ c.rc * cosh (t / c.rc)) t / (c.rc * cosh (t / c.rc))) ^ 2
        + 1 / (c.rc * cosh (t / c.rc)) ^ 2 - 1 ^ 2 * 0 ^ 2 / (c.rc * cosh (t / c.rc)) ^ 4
        = (1 / c.rc) ^ 2 by linear_combination dS_hubble c.rc_pos t]
    positivity

/-- The Hubble rate of the de Sitter vacuum is `tanh(t / r_c) / r_c`. It tends to `1/r_c` at late
times and vanishes only at the bounce `t = 0`. -/
theorem deSitter_H (c : Couplings) (t : ℝ) : (deSitter c).H t = tanh (t / c.rc) / c.rc := by
  have hrc := c.rc_pos
  have hc := cosh_pos (t / c.rc)
  change deriv (fun t ↦ c.rc * cosh (t / c.rc)) t / (c.rc * cosh (t / c.rc)) = _
  rw [(hasDerivAt_dS hrc.ne' t).deriv, tanh_eq_sinh_div_cosh]
  field_simp

/-- The de Sitter vacuum sits on the self-accelerating branch `ρ̃_+` of Eq. (26). -/
theorem deSitter_selfAccelerating (c : Couplings) (t : ℝ) :
    (deSitter c).ρt t
      = rhoTilde 1 (deSitter c).c.rhoS ((deSitter c).rhoBH t) ((deSitter c).ρ t) := by
  change 2 * c.rhoS = rhoTilde 1 c.rhoS
    (WhiteHole.rhoBH c.GN 1 1 0 (c.rc * cosh (t / c.rc))) 0
  have hb : WhiteHole.rhoBH c.GN 1 1 0 (c.rc * cosh (t / c.rc)) = 0 := by
    unfold WhiteHole.rhoBH; simp
  rw [hb]
  unfold rhoTilde
  simp
  ring

/-- Eq. (16) holds for the de Sitter vacuum, including at the bounce where `H = 0`: the induced
fluid has `P̃ = -ρ̃`. -/
theorem deSitter_pressure (c : Couplings) (t : ℝ) :
    (deSitter c).Pt t = pressureTilde c.rhoS ((deSitter c).ρt t)
      (3 * (deSitter c).P t - (deSitter c).ρ t) := by
  have := c.rhoS_pos
  change -(2 * c.rhoS) = pressureTilde c.rhoS (2 * c.rhoS) (3 * 0 - 0)
  unfold pressureTilde
  field_simp
  ring

end BraneCosmology

end WhiteHole
