module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Definite integrals used in Sec. 4 (ROADMAP M1.1)

The leading-order amplitude, Eq. (48), contains `∫ dx / (1 + x²)²` over the whole real line.
This file proves that it equals `π / 2`, so `eq48_leading` no longer takes the value on trust.

The proof uses the antiderivative `F(x) = x / (2 (1 + x²)) + arctan(x) / 2`, which tends to
`∓π/4` at `∓∞`, with the fundamental theorem of calculus for improper integrals.
-/

namespace WhiteHole

open Real MeasureTheory Filter Topology

/-- `1 / (1 + x²)²` is integrable on the real line: it is dominated by `1 / (1 + x²)`. -/
theorem integrable_inv_one_add_sq_sq : Integrable fun x : ℝ ↦ 1 / (1 + x ^ 2) ^ 2 := by
  have hmeas : Measurable fun x : ℝ ↦ 1 / (1 + x ^ 2) ^ 2 := by fun_prop
  refine integrable_inv_one_add_sq.mono' hmeas.aestronglyMeasurable (.of_forall fun x ↦ ?_)
  have h1 : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have h0 : (0 : ℝ) < 1 + x ^ 2 := by linarith
  rw [norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ h0 (by nlinarith)

/-- The antiderivative `x / (2 (1 + x²)) + arctan(x) / 2` of `1 / (1 + x²)²`. -/
private lemma hasDerivAt_antideriv (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ x / (2 * (1 + x ^ 2)) + arctan x / 2) (1 / (1 + x ^ 2) ^ 2) x := by
  have h0 : (0 : ℝ) < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hden : HasDerivAt (fun x : ℝ ↦ 2 * (1 + x ^ 2)) (2 * (2 * x)) x := by
    have := (((hasDerivAt_id x).fun_pow 2).const_add 1).const_mul 2
    simpa using this
  have h := ((hasDerivAt_id x).fun_div hden (by positivity)).fun_add
    ((hasDerivAt_arctan x).div_const 2)
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `x / (2 (1 + x²))` is bounded by `1/|x|`, so it vanishes at `±∞`. -/
private lemma norm_rational_le (x : ℝ) : ‖x / (2 * (1 + x ^ 2))‖ ≤ ‖x⁻¹‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h0 : (0 : ℝ) < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hx' : 0 < |x| := abs_pos.2 hx
  rw [norm_div, norm_inv, norm_eq_abs, norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * _),
    ← one_div, div_le_div_iff₀ (by positivity) hx']
  nlinarith [sq_abs x]

private lemma tendsto_antideriv_atTop :
    Tendsto (fun x : ℝ ↦ x / (2 * (1 + x ^ 2)) + arctan x / 2) atTop (𝓝 (π / 4)) := by
  have h1 : Tendsto (fun x : ℝ ↦ x / (2 * (1 + x ^ 2))) atTop (𝓝 0) :=
    squeeze_zero_norm norm_rational_le (by simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).norm)
  have h2 : Tendsto (fun x : ℝ ↦ arctan x / 2) atTop (𝓝 (π / 2 / 2)) :=
    (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).div_const 2
  convert h1.add h2 using 2
  ring

private lemma tendsto_antideriv_atBot :
    Tendsto (fun x : ℝ ↦ x / (2 * (1 + x ^ 2)) + arctan x / 2) atBot (𝓝 (-(π / 4))) := by
  have h1 : Tendsto (fun x : ℝ ↦ x / (2 * (1 + x ^ 2))) atBot (𝓝 0) :=
    squeeze_zero_norm norm_rational_le (by simpa using (tendsto_inv_atBot_zero (𝕜 := ℝ)).norm)
  have h2 : Tendsto (fun x : ℝ ↦ arctan x / 2) atBot (𝓝 (-(π / 2) / 2)) :=
    (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).div_const 2
  convert h1.add h2 using 2
  ring

/-- **`∫ dx / (1 + x²)² = π / 2`** over the whole real line. This is the integral in Eq. (48). -/
theorem integral_univ_inv_one_add_sq_sq : ∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2 = π / 2 := by
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_antideriv integrable_inv_one_add_sq_sq
    tendsto_antideriv_atBot tendsto_antideriv_atTop]
  ring

end WhiteHole
