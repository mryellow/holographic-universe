module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Holographic Universe: advertised statements

This module is the statement surface that a reader audits. It imports only Mathlib. It restates
the definitions the statements use; `comparator.json` checks that each one is identical to its
counterpart in the `HolographicUniverse` library. `Solution.lean` proves the theorems.

The setting is R. Pourhasan, N. Afshordi and R. B. Mann, *Out of the White Hole: A Holographic
Origin for the Big Bang*, arXiv:1309.1487, JCAP 04 (2014) 005. In that paper, a 3-brane outside a
5D black hole carries a thermal plasma. The primordial power spectrum of curvature perturbations
on the brane is set by the thermal integral `M(κ)` of its Eq. (46). The paper evaluates `M` at
`κ = 0`, which gives a scale-invariant spectrum, and attributes the observed red tilt
`n_s ≈ 0.965 < 1` to higher-order corrections. The results below are:

1. **The constants.** `ζ(5)` as a real series, its identification with `riemannZeta 5`, and
   rigorous bounds; the Bose–Einstein integral `∫₀^∞ x⁵eˣ/(eˣ − 1)² dx = 120 ζ(5)`; and
   `M(0) = 15 ζ(5)/π²`, the value the paper quotes as `≈ 1.576`.
2. **The thermal spectrum is blue.** `M` is strictly increasing in `|κ|`, its second derivative
   at `0` along a ray is `(10ζ(5) − ζ(3))/(16π²) > 0`, and every spectrum of the form
   `P(k) = C · M(k/s)` has spectral index `n_s(k) > 1` at every scale `k > 0`. So the
   next-order corrections of the paper's own mechanism tilt the spectrum the wrong way.
3. **The Jeans alternative.** For a spectrum amplified by a Jeans-type instability,
   `C · exp(2τ√(1 − (k/k_J)²))`, the running of the spectral index is an exact multiple of its
   tilt. For the same growth projected onto the brane, the total tilt over all scales,
   `∫₀^b (n_s − 1) d ln k`, is exactly `−2 ln cosh τ`.

The spectral index is `n_s(k) = 1 + d ln P/d ln k` and its running is `α_s = d n_s/d ln k`,
written with `deriv` so that no differentiability is assumed in the definitions. Each theorem
that differentiates states the hypotheses it needs.
-/

open Real MeasureTheory Filter Topology

namespace WhiteHole

/-! ## Definitions -/

/-- `ζ(5) = ∑_{n ≥ 1} 1/n⁵` as a real number. -/
noncomputable def zeta5 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5

/-- `ζ(3) = Σ_{n ≥ 1} 1/n³`, as a real series. -/
noncomputable def zeta3 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

/-- The Bose–Einstein occupation number `n(x) = 1/(eˣ - 1)`. -/
noncomputable def bose (x : ℝ) : ℝ := 1 / (exp x - 1)

/-- Momentum space `ℝ⁴` of the thermal integral. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- `ω_± = √(κ'² + κ²/4 ± κ·κ')`, with `sgn = ±1`. -/
noncomputable def omegaPM (sgn : ℝ) (κ κ' : E4) : ℝ :=
  √(‖κ'‖ ^ 2 + ‖κ‖ ^ 2 / 4 + sgn * inner ℝ κ κ')

/-- **The thermal part of `M(κ)`, Eq. (46) of the paper.** The integrand is
`ω₊ω₋ (n₊n₋ + (n₊ + n₋)/2)/(2π)⁴`: the product `ω₊ω₋ [1/2 + n₊][1/2 + n₋]` without its vacuum term
`ω₊ω₋/4`. -/
noncomputable def thermalM (κ : E4) : ℝ :=
  ∫ κ' : E4, omegaPM 1 κ κ' * omegaPM (-1) κ κ'
    * (bose (omegaPM 1 κ κ') * bose (omegaPM (-1) κ κ')
      + (bose (omegaPM 1 κ κ') + bose (omegaPM (-1) κ κ')) / 2) / (2 * π) ^ 4

/-- The unit vector `e = (1, 0, 0, 0)`. -/
noncomputable def eR : E4 := EuclideanSpace.single 0 1

/-- `M` along the ray, `m(t) = M(t e)`. -/
noncomputable def mRay (t : ℝ) : ℝ := thermalM (t • eR)

/-- The scalar spectral index `n_s(k) = 1 + d ln P / d ln k = 1 + k P'(k)/P(k)`. -/
noncomputable def spectralIndex (P : ℝ → ℝ) (k : ℝ) : ℝ := 1 + k * deriv P k / P k

/-- The running of the spectral index, `α_s(k) = d n_s / d ln k = k · n_s′(k)`. -/
noncomputable def runningIndex (P : ℝ → ℝ) (k : ℝ) : ℝ := k * deriv (spectralIndex P) k

/-- The exact linear growth of a 4D mode with `z = K/K_J`, started from rest:
`cosh²(τ√(1 − z²))`. For `z ≥ 1` the square root is `0`, so the growth is `1`: those modes
oscillate and do not grow. -/
noncomputable def jeansGrowthExact (τ z : ℝ) : ℝ := cosh (τ * √(1 - z ^ 2)) ^ 2

/-- The projection of Eq. (48) with growth: `I(y) = ∫ (1 + x²)⁻² F(y√(1 + x²)) dx`,
`y = k/k_J`. Without growth, `I = π/2`. -/
noncomputable def jeansProjected (τ y : ℝ) : ℝ :=
  ∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2 * jeansGrowthExact τ (y * √(1 + x ^ 2))

end WhiteHole

namespace HolographicUniverse

open WhiteHole

/-! ## 1. The constants -/

/-- **`ζ(5)`.** The real series `zeta5` is Mathlib's Riemann zeta function at `5`, and
`1.0369 ≤ ζ(5) ≤ 1.0370`. -/
theorem zeta5_spec : riemannZeta 5 = (zeta5 : ℂ) ∧ 1.0369 ≤ zeta5 ∧ zeta5 ≤ 1.0370 := by
  sorry

/-- **The Bose–Einstein integral.** `∫₀^∞ x⁵ eˣ/(eˣ - 1)² dx = 120 ζ(5)`. -/
theorem integral_bose :
    ∫ y in Set.Ioi (0 : ℝ), y ^ 5 * (exp y / (exp y - 1) ^ 2) = 120 * zeta5 := by
  sorry

/-- **`M(0) = 15 ζ(5)/π²`**, the value the paper quotes as `M(0) ≈ 1.576`. -/
theorem thermalM_zero : thermalM 0 = 15 * zeta5 / π ^ 2 ∧
    1.5758 ≤ thermalM 0 ∧ thermalM 0 ≤ 1.5761 := by
  sorry

/-! ## 2. The thermal spectrum is blue -/

/-- **`M` is strictly increasing in `|κ|`.** -/
theorem thermalM_lt_of_norm_lt {κ₁ κ₂ : E4} (h : ‖κ₁‖ < ‖κ₂‖) : thermalM κ₁ < thermalM κ₂ := by
  sorry

/-- **The second-order coefficient.** Along a ray, `m′(0) = 0` and
`m″(0) = (10ζ(5) − ζ(3))/(16π²)`, which is positive. -/
theorem mRay_second_order : deriv mRay 0 = 0 ∧
    HasDerivAt (deriv mRay) ((10 * zeta5 - zeta3) / (16 * π ^ 2)) 0 ∧
    0 < (10 * zeta5 - zeta3) / (16 * π ^ 2) := by
  sorry

/-- **The thermal spectrum is blue at every scale.** For `P(k) = C·M(k/s)` with `C ≠ 0` and
`s > 0`, `n_s(k) > 1` at every `k > 0`. Since `M(κ)` depends only on `|κ|`, `m` is `M` along any
ray. -/
theorem spectralIndex_thermal_gt_one {C s k : ℝ} (hC : C ≠ 0) (hs : 0 < s) (hk : 0 < k) :
    1 < spectralIndex (fun k ↦ C * mRay (k / s)) k := by
  sorry

/-! ## 3. The Jeans alternative -/

/-- **The Jeans running.** For the Jeans-amplified spectrum `P(k) = C · e^{2τ√(1 − (k/k_J)²)}`,
below the Jeans scale and with `y = k/k_J`, the tilt is `n_s − 1 = −2τy²/√(1 − y²)` and the
running is exactly `α_s = (1 + 1/(1 − y²))(n_s − 1)`. -/
theorem jeans_tilt_and_running {C τ kJ k : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ) (hk : 0 < k)
    (hk' : k < kJ) :
    spectralIndex (fun k ↦ C * exp (2 * τ * √(1 - (k / kJ) ^ 2))) k - 1 =
        -(2 * τ * (k / kJ) ^ 2 / √(1 - (k / kJ) ^ 2)) ∧
      runningIndex (fun k ↦ C * exp (2 * τ * √(1 - (k / kJ) ^ 2))) k =
        (1 + 1 / (1 - (k / kJ) ^ 2)) *
          (spectralIndex (fun k ↦ C * exp (2 * τ * √(1 - (k / kJ) ^ 2))) k - 1) := by
  sorry

/-- **On the brane, nothing happens above the Jeans scale.** The projected spectrum has
`n_s = 1` exactly for `k > k_J`. -/
theorem spectralIndex_jeansProjected_above {C τ kJ k : ℝ} (hkJ : 0 < kJ) (hk : kJ < k) :
    spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k = 1 := by
  sorry

/-- **The tilt budget.** For the brane spectrum `C · I(k/k_J)`, the total tilt
`∫₀^b (n_s − 1) d ln k` is exactly `−2 ln cosh τ` for any `b ≥ k_J`, as an improper integral at
`k → 0⁺`. -/
theorem tilt_budget {C τ kJ b : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ) (hb : kJ ≤ b) :
    Tendsto (fun a ↦ ∫ k in a..b, (spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k - 1) / k)
      (𝓝[>] 0) (𝓝 (-2 * log (cosh τ))) := by
  sorry

end HolographicUniverse
