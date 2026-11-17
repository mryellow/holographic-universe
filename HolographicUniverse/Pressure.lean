import HolographicUniverse.InducedFluid
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Pressure of the induced fluid (Eqs. (16) and (27))

Eq. (16) is not an independent input: it follows from differentiating the quadratic
constraint along the flow and using the two continuity equations (12)–(13). That derivation
never uses `ε`, which is why only `ε = -1` in Eq. (27) is consistent with it.
-/

namespace WhiteHole

open Real

/-- Eq. (16): `P̃ = (ρ̃² + ρ̃_s(ρ̃ - T)) / (3(ρ̃_s - ρ̃))`, with `T = 3P - ρ` (Eq. (17)). -/
noncomputable def pressureTilde (s ρt T : ℝ) : ℝ := (ρt ^ 2 + s * (ρt - T)) / (3 * (s - ρt))

/-- Eq. (27), the bulk-embedding form, depending on the normal orientation `ε`. -/
noncomputable def pressureTildeEps (ε s ρt T : ℝ) : ℝ :=
  (-(1 + 2 * ε) * ρt ^ 2 + s * (ρt - T)) / (3 * (s + ε * ρt))

/-- With `ε = -1`, Eq. (27) is Eq. (16). -/
theorem eq27_neg_one : pressureTildeEps (-1) = pressureTilde := by
  funext s ρt T; unfold pressureTildeEps pressureTilde; ring_nf

/-- With `ε = +1`, Eq. (27) differs from Eq. (16). -/
theorem eq27_one_ne : pressureTildeEps 1 1 (1 / 2) 0 ≠ pressureTilde 1 (1 / 2) 0 := by
  unfold pressureTildeEps pressureTilde; norm_num

/-- **Eq. (16) from conservation.** Suppose that at every time the induced density obeys the
quadratic with `ρ_BH = C / a⁴`, and that `ρ` and `ρ̃` obey the continuity equations (12)–(13)
at `τ`. If `H(τ) ≠ 0` and `ρ̃ ≠ ρ̃_s`, the induced pressure is given by Eq. (16). -/
theorem pressure_of_continuity {a ρ P ρt Pt : ℝ → ℝ} {τ a' ρ' ρt' s C : ℝ}
    (hquad : ∀ t, IsInduced s (C / a t ^ 4) (ρ t) (ρt t))
    (ha : HasDerivAt a a' τ) (hρ : HasDerivAt ρ ρ' τ) (hρt : HasDerivAt ρt ρt' τ)
    (ha0 : a τ ≠ 0) (hH : a' ≠ 0) (hsing : ρt τ ≠ s)
    (hcont : ρ' = -3 * (a' / a τ) * (ρ τ + P τ))
    (hcontt : ρt' = -3 * (a' / a τ) * (ρt τ + Pt τ)) :
    Pt τ = pressureTilde s (ρt τ) (3 * P τ - ρ τ) := by
  unfold IsInduced at hquad
  have h0 : HasDerivAt (fun t ↦ ρt t ^ 2 - 2 * s * ρt t + 2 * s * (C / a t ^ 4 - ρ t)) 0 τ := by
    rw [show (fun t ↦ ρt t ^ 2 - 2 * s * ρt t + 2 * s * (C / a t ^ 4 - ρ t)) = fun _ ↦ 0 from
      funext hquad]
    exact hasDerivAt_const τ 0
  have h1 := ((hρt.fun_pow 2).fun_sub (hρt.const_mul (2 * s))).fun_add
    ((((hasDerivAt_const τ C).fun_div (ha.fun_pow 4) (pow_ne_zero 4 ha0)).fun_sub hρ).const_mul
      (2 * s))
  have hd := h0.unique h1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_sub] at hd
  have hq := hquad τ
  have hdiff : a' / a τ * (Pt τ * (3 * (s - ρt τ)) - (ρt τ ^ 2 + s * (ρt τ - (3 * P τ - ρ τ))))
      = 0 := by
    rw [hcont, hcontt] at hd
    linear_combination (norm := (field_simp; ring)) (-1 / 2) * hd + 2 * (a' / a τ) * hq
  have hne : s - ρt τ ≠ 0 := sub_ne_zero.2 (Ne.symm hsing)
  rcases mul_eq_zero.1 hdiff with h | h
  · exact absurd h (div_ne_zero hH ha0)
  · unfold pressureTilde
    rw [eq_div_iff (mul_ne_zero three_ne_zero hne)]
    linarith

end WhiteHole
