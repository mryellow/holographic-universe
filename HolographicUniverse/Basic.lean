module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Couplings and derived scales

Pourhasan, Afshordi & Mann, *Out of the White Hole: A Holographic Origin for the Big Bang*,
arXiv:1309.1487, JCAP 04 (2014) 005. Equation numbers refer to that paper.

Natural units `ħ = c = k_B = 1` throughout. Planck masses are characterised through powers
(`M₄² = 1/(16π G_N)`, `M₅³ = 1/(32π G_b)`, Eq. (2)) so that no `rpow` is needed.
-/

namespace WhiteHole

open Real

/-- Brane Newton constant `G_N` and bulk gravitational constant `G_b` (Eq. (1)). -/
structure Couplings where
  GN : ℝ
  Gb : ℝ
  GN_pos : 0 < GN
  Gb_pos : 0 < Gb

namespace Couplings

variable (c : Couplings)

/-- Characteristic density of the holographic fluid, Eq. (18): `ρ̃_s = 3 G_N / (16π G_b²)`. -/
noncomputable def rhoS : ℝ := 3 * c.GN / (16 * π * c.Gb ^ 2)

/-- DGP crossover scale `r_c = G_b / G_N`, Eq. (31). -/
noncomputable def rc : ℝ := c.Gb / c.GN

lemma rhoS_pos : 0 < c.rhoS := by
  have := c.GN_pos; have := c.Gb_pos
  unfold rhoS; positivity

lemma rc_pos : 0 < c.rc := div_pos c.Gb_pos c.GN_pos

/-- Eq. (31): `r_c = (3 / (16π G_N ρ̃_s))^{1/2} = G_b / G_N`. -/
theorem sqrt_eq_rc : √(3 / (16 * π * c.GN * c.rhoS)) = c.rc := by
  have hN := c.GN_pos; have hb := c.Gb_pos
  have h : 3 / (16 * π * c.GN * c.rhoS) = c.rc ^ 2 := by
    unfold rhoS rc; field_simp
  rw [h, sqrt_sq c.rc_pos.le]

/-- `(8π G_b/3) ρ̃_s = 1/(2 r_c)`. -/
lemma g_mul_rhoS : 8 * π * c.Gb / 3 * c.rhoS = 1 / (2 * c.rc) := by
  unfold rhoS rc
  have := c.GN_pos; have := c.Gb_pos
  field_simp
  ring

/-- `(8π G_N/3) ρ̃_s = 2 (1/(2 r_c))²`. -/
lemma gN_mul_rhoS : 8 * π * c.GN / 3 * c.rhoS = 2 * (1 / (2 * c.rc)) ^ 2 := by
  rw [← c.g_mul_rhoS]
  unfold rhoS
  have := c.GN_pos; have := c.Gb_pos
  field_simp
  ring

/-- `M₄` is the 4D Planck mass, Eq. (2). -/
def IsM4 (M4 : ℝ) : Prop := 0 < M4 ∧ M4 ^ 2 = 1 / (16 * π * c.GN)

/-- `M₅` is the 5D Planck mass, Eq. (2). -/
def IsM5 (M5 : ℝ) : Prop := 0 < M5 ∧ M5 ^ 3 = 1 / (32 * π * c.Gb)

/-- In Planck units the crossover scale is `r_c = M₄² / (2 M₅³)`. -/
lemma rc_eq_planck {M4 M5 : ℝ} (h4 : c.IsM4 M4) (h5 : c.IsM5 M5) :
    c.rc = M4 ^ 2 / (2 * M5 ^ 3) := by
  obtain ⟨-, h4⟩ := h4; obtain ⟨hM5, h5⟩ := h5
  have hN := c.GN_pos; have hb := c.Gb_pos
  rw [h4, h5]; unfold rc; field_simp; ring

end Couplings

end WhiteHole
