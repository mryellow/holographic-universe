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

For a general bulk (ROADMAP M5.1), the bulk density `b` obeys its own continuity equation
`ḃ = -3H(b + P_b)`. The same derivation then gives `pressureTildeBulk`:
`P̃ = (ρ̃² - 2ρ̃_s(P - P_b)) / (2(ρ̃_s - ρ̃))` (`pressure_of_continuity_bulk`). Schwarzschild has
`P_b = b/3`, like radiation, and this reduces to Eq. (16) (`pressureTildeBulk_radiation`).
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

/-- Eq. (16) for a general bulk: `P̃ = (ρ̃² - 2ρ̃_s ΔP) / (2(ρ̃_s - ρ̃))`, with `ΔP = P - P_b` the
matter pressure minus the pressure of the bulk density. -/
noncomputable def pressureTildeBulk (s ρt ΔP : ℝ) : ℝ := (ρt ^ 2 - 2 * s * ΔP) / (2 * (s - ρt))

/-- **Eq. (16) from conservation, for any bulk.** Suppose that at every time the induced
density obeys the quadratic with bulk density `b`, and that `ρ`, `ρ̃` and `b` obey continuity
equations at `τ`, with pressures `P`, `P̃` and `P_b`. If `H(τ) ≠ 0` and `ρ̃ ≠ ρ̃_s`, then
`P̃ = pressureTildeBulk ρ̃_s ρ̃ (P - P_b)`. -/
theorem pressure_of_continuity_bulk {a ρ P ρt Pt b : ℝ → ℝ} {τ a' ρ' ρt' b' s Pb : ℝ}
    (hquad : ∀ t, IsInduced s (b t) (ρ t) (ρt t))
    (hb : HasDerivAt b b' τ) (hρ : HasDerivAt ρ ρ' τ) (hρt : HasDerivAt ρt ρt' τ)
    (ha0 : a τ ≠ 0) (hH : a' ≠ 0) (hsing : ρt τ ≠ s)
    (hcont : ρ' = -3 * (a' / a τ) * (ρ τ + P τ))
    (hcontt : ρt' = -3 * (a' / a τ) * (ρt τ + Pt τ))
    (hcontb : b' = -3 * (a' / a τ) * (b τ + Pb)) :
    Pt τ = pressureTildeBulk s (ρt τ) (P τ - Pb) := by
  unfold IsInduced at hquad
  have h0 : HasDerivAt (fun t ↦ ρt t ^ 2 - 2 * s * ρt t + 2 * s * (b t - ρ t)) 0 τ := by
    rw [show (fun t ↦ ρt t ^ 2 - 2 * s * ρt t + 2 * s * (b t - ρ t)) = fun _ ↦ 0 from
      funext hquad]
    exact hasDerivAt_const τ 0
  have h1 := ((hρt.fun_pow 2).fun_sub (hρt.const_mul (2 * s))).fun_add
    ((hb.fun_sub hρ).const_mul (2 * s))
  have hd := h0.unique h1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
  have hq := hquad τ
  set H := a' / a τ with hHdef
  have hdiff : H * (Pt τ * (2 * (s - ρt τ)) - (ρt τ ^ 2 - 2 * s * (P τ - Pb))) = 0 := by
    rw [hcont, hcontt, hcontb] at hd
    linear_combination (-1 / 3) * hd + H * hq
  have hne : s - ρt τ ≠ 0 := sub_ne_zero.2 (Ne.symm hsing)
  rcases mul_eq_zero.1 hdiff with h | h
  · exact absurd h (div_ne_zero hH ha0)
  · unfold pressureTildeBulk
    rw [eq_div_iff (mul_ne_zero two_ne_zero hne)]
    linarith

/-- **A radiation-like bulk gives Eq. (16).** If `P_b = b/3` and the quadratic holds, the
general formula is Eq. (16) with `T = 3P - ρ`. -/
theorem pressureTildeBulk_radiation {s b ρ ρt P : ℝ} (hq : IsInduced s b ρ ρt) (hsing : ρt ≠ s) :
    pressureTildeBulk s ρt (P - b / 3) = pressureTilde s ρt (3 * P - ρ) := by
  unfold IsInduced at hq
  have hne : s - ρt ≠ 0 := sub_ne_zero.2 (Ne.symm hsing)
  unfold pressureTildeBulk pressureTilde
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero hne) (mul_ne_zero three_ne_zero hne)]
  linear_combination (s - ρt) * hq

/-- **Eq. (16) from conservation.** Suppose that at every time the induced density obeys the
quadratic with `ρ_BH = C / a⁴`, and that `ρ` and `ρ̃` obey the continuity equations (12)–(13)
at `τ`. If `H(τ) ≠ 0` and `ρ̃ ≠ ρ̃_s`, the induced pressure is given by Eq. (16). This is the
case `P_b = ρ_BH/3` of `pressure_of_continuity_bulk`. -/
theorem pressure_of_continuity {a ρ P ρt Pt : ℝ → ℝ} {τ a' ρ' ρt' s C : ℝ}
    (hquad : ∀ t, IsInduced s (C / a t ^ 4) (ρ t) (ρt t))
    (ha : HasDerivAt a a' τ) (hρ : HasDerivAt ρ ρ' τ) (hρt : HasDerivAt ρt ρt' τ)
    (ha0 : a τ ≠ 0) (hH : a' ≠ 0) (hsing : ρt τ ≠ s)
    (hcont : ρ' = -3 * (a' / a τ) * (ρ τ + P τ))
    (hcontt : ρt' = -3 * (a' / a τ) * (ρt τ + Pt τ)) :
    Pt τ = pressureTilde s (ρt τ) (3 * P τ - ρ τ) := by
  have hb := (hasDerivAt_const τ C).fun_div (ha.fun_pow 4) (pow_ne_zero 4 ha0)
  rw [pressure_of_continuity_bulk (b := fun t ↦ C / a t ^ 4) (Pb := C / a τ ^ 4 / 3) hquad hb hρ
    hρt ha0 hH hsing hcont hcontt (by field_simp; ring)]
  exact pressureTildeBulk_radiation (hquad τ) hsing

end WhiteHole
