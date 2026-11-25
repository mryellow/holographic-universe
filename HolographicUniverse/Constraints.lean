module

public import HolographicUniverse.InducedFluid

@[expose] public section

/-!
# Observational bounds on `ρ̃_s` (Eqs. (32)–(35))

The smallness assumption (32), `|ρ̃| ≤ ε ρ`, combined with the quadratic (26) bounds
`ρ̃_s/ρ` branch by branch. Throughout, `s = ρ̃_s`, `b = ρ_BH`, `x = ρ̃` and `ε` is the
smallness parameter of Eq. (32) (not the normal orientation).

On the self-accelerating branch `x ≥ s`; on the normal branch `x ≤ s`.
-/

namespace WhiteHole

variable {s b ρ x ε : ℝ}

/-- The quadratic rewritten as `ρ_BH - ρ = x - x²/(2s)`, cleared of denominators. -/
private lemma quad' (h : IsInduced s b ρ x) : 2 * s * (b - ρ) = 2 * s * x - x ^ 2 := by
  unfold IsInduced at h; linarith

/-- **Eq. (33), self-accelerating branch.** -/
theorem eq33 (hs : 0 < s) (hρ : 0 < ρ) (h : IsInduced s b ρ x) (hplus : s ≤ x)
    (hsmall : |x| ≤ ε * ρ) (hden : 0 < 1 + ε - b / ρ) :
    s / ρ ≤ ε ^ 2 / 2 * (1 + ε - b / ρ)⁻¹ := by
  have hq := quad' h
  have hx := (abs_le.1 hsmall).2
  have key : 2 * s * (ρ * (1 + ε) - b) ≤ ε ^ 2 * ρ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : 0 ≤ ε * ρ + x - 2 * s)]
  rw [le_mul_inv_iff₀ hden, show s / ρ * (1 + ε - b / ρ) = 2 * s * (ρ * (1 + ε) - b) / (2 * ρ ^ 2)
    by field_simp, div_le_iff₀ (by positivity)]
  nlinarith

/-- Side remarks after Eq. (33): on the self-accelerating branch `ρ̃_s ≤ ε ρ` and
`ρ_BH ≤ (1 + ε/2) ρ`. -/
theorem eq33_side (hs : 0 < s) (h : IsInduced s b ρ x) (hplus : s ≤ x)
    (hsmall : |x| ≤ ε * ρ) : s ≤ ε * ρ ∧ b ≤ (1 + ε / 2) * ρ := by
  have hq := quad' h
  have hx := (abs_le.1 hsmall).2
  refine ⟨hplus.trans hx, ?_⟩
  have : 2 * s * (b - ρ) ≤ s ^ 2 := by nlinarith [sq_nonneg (x - s)]
  nlinarith

/-- **Eq. (34), normal branch, `ρ_BH/ρ < 1 - ε`.** -/
theorem eq34 (hs : 0 < s) (hρ : 0 < ρ) (h : IsInduced s b ρ x) (hminus : x ≤ s)
    (hsmall : |x| ≤ ε * ρ) (hden : b / ρ < 1 - ε) :
    s / ρ ≤ ε ^ 2 / 2 * (1 - ε - b / ρ)⁻¹ := by
  have hq := quad' h
  have hx := (abs_le.1 hsmall).1
  have hd : 0 < 1 - ε - b / ρ := by linarith
  have key : 2 * s * (ρ * (1 - ε) - b) ≤ ε ^ 2 * ρ ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ ε * ρ + x) (by linarith : 0 ≤ ε * ρ - x + 2 * s)]
  rw [le_mul_inv_iff₀ hd, show s / ρ * (1 - ε - b / ρ) = 2 * s * (ρ * (1 - ε) - b) / (2 * ρ ^ 2)
    by field_simp, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Eq. (35), `ρ_BH/ρ > 1 + ε/2`.** The paper states this for the normal branch, but the
branch hypothesis is not needed: reality (30) already forces `ε ρ < ρ̃_s`, so only the normal
branch survives. The denominator is positive as a consequence, not by assumption. -/
theorem eq35 (hs : 0 < s) (hρ : 0 < ρ) (hε : 0 < ε) (h : IsInduced s b ρ x)
    (hsmall : |x| ≤ ε * ρ) (hb : 1 + ε / 2 < b / ρ) :
    0 < 1 + ε - b / ρ ∧ ε ^ 2 / 2 * (1 + ε - b / ρ)⁻¹ ≤ s / ρ := by
  have hq := quad' h
  have hx := (abs_le.1 hsmall).2
  have hreal := reality hs h
  have hb' : (1 + ε / 2) * ρ < b := by rwa [lt_div_iff₀ hρ] at hb
  -- the reality bound pushes `ρ̃_s` above `ε ρ`, so `x ≤ ε ρ < s`
  have hsε : ε * ρ < s := by nlinarith
  have key : ε ^ 2 * ρ ^ 2 ≤ 2 * s * (ρ * (1 + ε) - b) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : 0 ≤ 2 * s - ε * ρ - x)]
  have hpos : 0 < ρ * (1 + ε) - b := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos (mul_pos hε hε) (mul_pos hρ hρ)]
  have hd : 0 < 1 + ε - b / ρ := by
    rw [show 1 + ε - b / ρ = (ρ * (1 + ε) - b) / ρ by field_simp]; positivity
  refine ⟨hd, ?_⟩
  rw [mul_inv_le_iff₀ hd,
    show s / ρ * (1 + ε - b / ρ) = 2 * s * (ρ * (1 + ε) - b) / (2 * ρ ^ 2) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith

end WhiteHole
