# P1: red tilt from a residual Jeans instability

Pathway P1 of [`docs/TESTABILITY.md`](../../docs/TESTABILITY.md). Sec. 5 of the paper suggests
that the gravitational Jeans instability of the bulk thermal atmosphere, active for less than a
Hubble time, could give the observed red tilt. This note works that out at linear order and
confronts it with Planck 2018. Run the numbers with

```bash
cd phenomenology && uv run python p1_jeans/jeans_tilt.py
```

**Result.** In its linear form, P1 does not pass gate G1. Where the pivot lies well inside the
unstable range, the tilt comes with a running `α_s ≈ 2(n_s - 1) ≈ -0.065`, about 9σ from
Planck. A narrow window just below the Jeans scale fits `n_s` and `α_s` at the pivot. That window
needs `k_J` within 10% of a fixed value, and the spectrum is then exactly scale invariant for all
`k ≥ k_J ≈ 0.065 Mpc⁻¹`. It cannot reproduce the measured tilt across the range that Planck
measures best.

## 1. The atmosphere

The paper's atmosphere is a thermal gas of one massless scalar in 4+1 flat dimensions:

- `ρ = ∫ d⁴k/(2π)⁴ ω n(ω) = (2π²/(2π)⁴)·Γ(5)ζ(5)T⁵ = 3ζ(5)T⁵/π²` (the integral of `M7.1`),
- `p = ρ/4` (radiation in 4 space dimensions), so `c_s² = 1/4` and `ρ + p = 5ρ/4`.

## 2. Linear growth

The paper writes the 5D metric with `g₀₀ = -(1 + 4Φ₄)` (longitudinal gauge, Sec. 4). The
Newtonian potential is `2Φ₄`, and in 5D its source is `8πG_b(2ρ + 4p)/3` (for dust this is the paper's `∇²Φ₄ = (8πG_b/3)ρ`). For
a relativistic fluid on a static background (the Jeans swindle):

- continuity: `∂_t δρ = -(ρ + p)∇·v`,
- Euler: `(ρ + p)∂_t v = -∇δp - (ρ + p)∇(2Φ₄)`,
- Poisson: `∇²(2Φ₄) = 8πG_b(2δρ + 4δp)/3`.

With `δp = δρ/4` these give, for a 4D wavenumber `K`,

  `δ̈ = (Γ₀² - c_s²K²) δ`,  `Γ₀² = 10πG_b ρ`,  `K_J² = Γ₀²/c_s² = 40πG_b ρ`.

With `M₅³ = 1/(32πG_b)` (Eq. 2, `IsM5`), `K_J² = (15ζ(5)/4π²)·T⁵/M₅³`, so

  `K_J ≈ 0.63 T (T/M₅)^{3/2} ≈ 0.044 T` at `T/M₅ = 0.17`.

The paper quotes `0.2 T (T/M₅)^{3/2}`. The factor of 3 does not matter below: every result is
in terms of `y = k/k_J` and the growth `τ`.

Modes with `K < K_J` grow, and those with `K > K_J` oscillate. Starting from rest, after a time
`Δt` the power in a mode is multiplied by

  `F(z) = cosh²(τ√(1 - z²))` for `z = K/K_J < 1`,  `F(z) = 1` for `z ≥ 1`,  `τ = Γ₀Δt`.

`τ` is the number of e-folds of growth of the longest modes. Sec. 5 argues that `Γ₀Δt` is
limited by the Hubble time, so `τ` is the residual growth.

## 3. Projection onto the brane

Eq. (48) gets the brane spectrum from the 4D one by integrating over the fourth momentum
component `k₄ = kx`, so `K = k√(1 + x²)`. With the growth included,

  `Δ²_ζ(k) ∝ I(y) = ∫ dx (1 + x²)⁻² F(y√(1 + x²))`,  `y = k/k_J`,

with `k_J` the comoving Jeans wavenumber at `a_b`. Without growth, `I = π/2`
(`integral_univ_inv_one_add_sq_sq`). Then `n_s - 1 = d ln I/d ln y` and `α_s = dn_s/d ln y`.

The thermal factor `M(κ)` is left out. `M7.3` proves that it is blue at every scale
(`spectralIndex_thermal_gt_one`). Near the Jeans scale `κ ≲ κ_J ≈ 0.044`, and the small-`κ`
coefficient gives at most `0.037κ² ≈ 7×10⁻⁵`, which is negligible here.

## 4. Results

**Exact statements.**

1. *Unprojected shape.* For `F = e^{2τ√(1-y²)}`, `α_s/(n_s - 1) = 1 + 1/(1 - y²) ≥ 2`. A red tilt
   always comes with a running at least twice its size, with the same sign.
2. *Above the Jeans scale nothing happens.* For `y ≥ 1` every 4D mode in the projection has
   `K ≥ k ≥ k_J`, so `F = 1`, `I = π/2` and `n_s = 1` exactly.
3. *The total tilt is bounded.* `I(0⁺) = (π/2)cosh²τ` and `I(1) = π/2`, so
   `∫ (n_s - 1) d ln k = -2 ln cosh τ` over all scales. The instability can lower the spectrum
   by this much in total, and all of the drop happens below `k_J`.

**Numerics** (`jeans_tilt.py`; Planck 2018 `n_s = 0.9649 ± 0.0042`,
`α_s = -0.0045 ± 0.0067` from Planck 2018 X, TT,TE,EE+lowE+lensing):

| Pivot position | What is needed for `n_s = 0.965` | Outcome |
|---|---|---|
| `y ≤ 0.3` (well inside the unstable range) | `τ` from 0.36 (`y = 0.3`) to 97 (`y = 0.01`) | `α_s ≈ -0.062` to `-0.067`: **8.6σ to 9.4σ** from Planck |
| `0.74 ≤ y ≤ 0.81`, `0.165 ≤ τ ≤ 0.188` | pivot just below `k_J` | passes `(n_s, α_s)` at 2σ (best `χ² = 0.27`). But: |
| | | `n_s = 1` exactly for `k ≥ k_J ∈ [0.062, 0.068] Mpc⁻¹` |
| | | `ln P(0.1)/P(0.008) ∈ [-0.034, -0.026]` vs `-0.089 ± 0.011` from the power-law fit: **≥ 5σ** |
| | | `β_s = d²n_s/d ln k² ∈ [0.14, 0.43]` vs `0.022 ± 0.012`: **≥ 10σ** |

`n_s(k)` at the best window point (`τ = 0.188`, `y = 0.788`): 0.9999 at `k = 0.002`, 0.9969 at
0.01, 0.9784 at 0.03, 0.9628 at 0.05, 0.9731 at 0.06, and exactly 1 at 0.1 and above. This is
a dip localized around the pivot, not a tilt.

The two Planck comparisons in the window are approximate. The `ln P` ratio uses the
power-law posterior on `n_s` to set its error, and `β_s` assumes a Taylor expansion in `ln k`,
which this spectrum does not have. Both are off by a large factor, so the conclusion should
survive a full likelihood. That check (CAMB with the Planck likelihood through Cobaya) is the
way to make it final.

## 5. Verdict for G1

The linear residual Jeans instability gives a red tilt, but not the observed one. It either
comes with ~9σ running, or it is a narrow dip that needs `k_J` tuned to within 10% of
`0.065 Mpc⁻¹` and leaves `ℓ ≳ 900` exactly scale invariant. By the P1 falsification criterion
(`|n_s - 0.965| > 3σ` for every allowed parameter value, or a tuned parameter), the window is
fine-tuned and the rest of parameter space fails. **P1 in this form is ruled out.**

## 6. Assumptions

What could change the verdict, in order of importance:

1. **Linear theory.** With `τ ≲ 0.2` in the window the growth is mild, so this is safe there.
   In the `y ≪ 1` regime `τ` is large and nonlinear growth would follow, which makes things
   worse.
2. **Static background.** The paper assumes static equilibrium at `a_b`. In an expanding bulk
   region the growth is a power law in time, but `Γ(K)` stays analytic in `K²`, so result 1
   (`α_s → 2(n_s - 1)` as `y → 0`) does not depend on this.
3. **Sharp growth/no-growth split at `K_J`.** Result 2 depends on it. A smooth cutoff would
   spread the dip, but not remove the bound of result 3.
4. **Initial conditions.** `F` assumes the mode starts at rest. Random initial phases change
   `F` by an `O(1)` factor near `z = 1` and do not change results 1 and 3.
5. **One scalar degree of freedom**, as in the paper. More species change `K_J` only.
6. **Projection by Eq. (48).** The `Z₂` boundary at the brane is ignored, as in the paper.

## 7. Lean (M8, `Jeans.lean`)

Result 1 is proved for the spectrum `C·e^{2τ√(1 - (k/k_J)²)}`, before the projection:

- `spectralIndex_jeans`: below `k_J`, `n_s - 1 = -2τy²/√(1 - y²)`.
- `runningIndex_jeans`: `α_s = (1 + 1/(1 - y²))(n_s - 1)`, exactly. `runningIndex_jeans_le`:
  `α_s ≤ 2(n_s - 1)` for `τ ≥ 0`.
- `spectralIndex_jeans_above`: above `k_J`, `n_s = 1` (the unprojected form of result 2).
- `planck2018Running_not_fits_jeans`: no such spectrum fits Planck 2018 with running, for any
  `C ≠ 0`, `τ ≥ 0` and `k_J ≠ k_*`.

`Running.lean` (TESTABILITY P4) proves the leading-order form of result 1 for any local
extension.

Result 2 is proved for the projected spectrum, with the exact growth `cosh²(τ√(1 - z²))`:
`I(y) = π/2` for `y ≥ 1` (`jeansProjected_of_one_le`), so `C·I(k/k_J)` has `n_s = 1` exactly for
`k > k_J` (`spectralIndex_jeansProjected_above`).

The endpoints of result 3 are proved: `I(y) → (π/2)cosh²τ` as `y → 0`
(`tendsto_jeansProjected_zero`, by dominated convergence), so
`ln I(1) − ln I(0⁺) = −2 ln cosh τ` (`tendsto_log_jeansProjected_budget`). The spectrum falls by
exactly `cosh²τ` between the far infrared and the Jeans scale, which is the budget.

Still open, and not needed for the verdict: writing that budget as `∫(n_s − 1) d ln k`. It needs
`I` differentiable in `y` (differentiation under the integral), and the growth has a kink at
`z = 1`.
