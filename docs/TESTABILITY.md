# Testability roadmap

From "the conclusions follow from the assumptions" (the Lean formalization) to "here is a
number that an instrument can measure, and here is the result that would rule the model out".

This document lists the candidate observational tests, gives an honest verdict on each, and
provides a template for turning a candidate into a worked **pathway**. The companion
[`ROADMAP.md`](ROADMAP.md) covers the Lean side. Cross-references like `M7.2` point to its
milestones.

Equation and section numbers refer to Pourhasan, Afshordi & Mann, arXiv:1309.1487v2.

## 1. Where we start

### The simple model is already falsified

The paper says so itself. At leading order Eq. (48) does not depend on `k`, so the model
predicts an exactly scale-invariant spectrum, `n_s = 1`. Sec. 4 notes that the observed ~4%
red tilt "is not predicted in our simple model". Sec. 5 says the model "is already ruled out by
cosmological observations at >5σ level". With Planck 2018 (`n_s = 0.9649 ± 0.0042`) the
tension is about 8σ.

This is now a theorem (`ScaleInvariance.lean`, M7.2). `leading_order_ruled_out_planck2013` and
`leading_order_ruled_out_planck2018` prove that the leading-order spectrum fits neither release,
for any value of `T_b/M₅`. `planck2013_ns_excludes_one` and `planck2018_ns_excludes_one` prove
the >5σ and >8σ figures, reading each 1σ interval as a symmetric Gaussian error.

The paper calls this "the most immediate phenomenological challenge for our scenario".

**Consequence:** a testable hypothesis cannot be the 2014 model as written. It has to be an
**extended model** that produces a red tilt, and that extension then has to make further
predictions. Pathway P1 below comes first, and is a gate for everything else.

### Where G1 stands (2026-11-18)

**G1 has failed for both of the paper's extensions** at linear order:
- **P1 (Jeans instability)** fails on shape. For the unprojected spectrum this is proved in Lean
  (`planck2018Running_not_fits_jeans`). See P1 below.
- **P2 (cascading gravity)** fails on sign. It is proved in Lean for every `M₆`
  (`ObsData.not_fits_cascade`).

Three Lean results frame the situation:
- The full thermal spectrum is blue at every scale (`ObsData.not_fits_thermal`).
- So is the thermal spectrum times any nondecreasing factor (`ObsData.not_fits_thermal_mul`).
- Any extension that fits must have `d ln G/d ln k < −0.0309` at the Planck 2018 pivot
  (`planck2018_factor_slope`).

A fourth result closes the class (P4): no **local** extension of the paper's static mechanism
fits `n_s` and its running together (`planck2018Running_not_fits_local`). Local physics gives
`α_s ≤ 2(n_s − 1) ≤ −0.063`; Planck 2018 measures `−0.0045 ± 0.0067`.

`docs/NOTE.md`, Sec. 6, has the write-up of P1 and P2. What remains is outside the paper's
mechanism: modes imprinted at different times, or scale-free long-range correlations (see P4).

### What the formalization already gives

| Fact | Lean | Use for testing |
|---|---|---|
| `T_b/M₅ ≈ 0.171` is fixed by the CMB amplitude | `eq49`, `eq49_planck2013_sharp`, `eq49_planck2018` | One parameter is already used up by data. Planck 2013 gives `[0.17061, 0.17216]`; Planck 2018 gives `[0.1697, 0.17051]` |
| `r_c = M₄²/(2M₅³) ≳ 3/H₀` | `rc_eq_planck`, `eq51` | Gravity changes at **Hubble** scales, not at short distances |
| `ρ_BH ∝ a⁻⁴`, but suppressed | `rhoBH_scaling`, `BraneCosmology.darkRadiation_le`, `abs_deltaNeff_bbn` | Scales like radiation, but enters `H²` with weight `1/(r_c H)`, not `1`. BBN and `N_eff` cannot see it: `\|ΔN_eff\| ≤ 3×10⁻¹⁴` at BBN |
| `𝒦 > 0` (closed slicing) | `BraneCosmology.K_pos` | Predicts `Ω_k < 0` |
| Bounds on `ρ̃_s/ρ` per branch | `eq33`–`eq35` | Restrict the allowed parameter region |
| Normal-branch sign tension | `orientation_minus_branch`, `pressure_of_timelike_junction` | **Resolved** (M3.1): the paper's `ε = -1` is too strong. `ε` follows the sign of `ρ̃`, so the normal branch with `ρ_BH < ρ` has `ε = +1` |

### Parameter inventory

| Parameter | Meaning | Status |
|---|---|---|
| `G_N` (`M₄`) | 4D Newton constant | measured |
| `G_b` (`M₅`) | 5D gravitational constant | bounded: `M₅ ≤ 9 MeV` (Eq. 51, `eq51_numeric`), from `r_c ≳ 3/H₀` |
| `T_b` | temperature of the brane's thermal atmosphere | fixed relative to `M₅` by `A_s` (Eq. 49) |
| `𝒦`, i.e. `Ω_k` | spatial curvature | set by the parent's mass `M_*`: the paper's `−Ω_k ∼ M₅/M_*` (Sec. 5) holds at the start, when `H ∼ M₅`. Today, `−Ω_k ≈ 5×10⁻²²·(M_⊙/M_*)` for `M₅ = 9 MeV` (estimate, see O4) |
| `r_h`, i.e. `μ` | bulk black-hole horizon / mass | free; enters through `ρ_BH` |
| `ε` (Eq. 32) | allowed size of `ρ̃/ρ` | modeling choice, `~0.1` in the paper |
| branch, orientation | `ρ̃_±`, normal orientation | normal branch preferred (no ghosts); orientation fixed by the sign of `ρ̃` (`orientation_iff`) |
| *extension parameters* | whatever produces the red tilt | P1 (`τ`, `k_J`) and P2 (`M₆`, screening) both fail G1 at linear order. Any extension needs `d ln G/d ln k < −0.0309` at the pivot (`planck2018_factor_slope`), and a red tilt of power `p < 0.36` in `k` (`planck2018Running_not_fits_tilt`), which local physics does not give (P4) |

## 2. Catalogue of options

Verdicts:

- **Core:** follows from the model as written, or from the extension that P1 needs.
- **Extension:** needs a modified model, but the modification is well motivated.
- **Weak:** possible in principle, but it would not tell this model apart from standard
  inflation + ΛCDM.
- **Not applicable:** the model does not predict it, or the formalization rules it out.

| # | Option | Verdict | Distinguishes from inflation? | Data | Starting effort |
|---|---|---|---|---|---|
| O1 | Spectral tilt `n_s` and its running | **Core** (gate). Fails for every local extension (P4) | Yes, through how the tilt arises and the running it implies | Planck, ACT, SPT, Simons Observatory | Theory: hard |
| O2 | Primordial non-Gaussianity (`f_NL`, bispectrum shape) | **Core** | Probably: thermal correlators give a specific shape | Planck limits, future LSS surveys | Theory: hard |
| O3 | Tensor-to-scalar ratio `r` | **Core** | Yes, if the model predicts `r ≈ 0` or a distinct tensor tilt | BICEP/Keck, LiteBIRD | Theory: medium |
| O4 | Spatial curvature `Ω_k < 0`, together with large-scale anisotropy | **Not applicable** for a stellar-mass parent: `−Ω_k ≈ 5×10⁻²²·(M_⊙/M_*)` today (estimate) | Would, but is unobservable unless `M_* ≲ 10¹³ kg` | Planck + BAO (`|Ω_k| ≲ 0.002`), future 21 cm / LSS | Done (estimate) |
| O5 | Dark radiation `ΔN_eff` and BBN abundances | **Not applicable**: ruled out as a signal (`abs_deltaNeff_bbn`: `\|ΔN_eff\| ≤ 3×10⁻¹⁴`) | No | Planck, BBN (D/H, Yₚ), Simons Observatory | Done (Lean) |
| O6 | Late-time expansion `H(z)` (DGP normal branch) | **Core** | Weakly; the normal branch needs dark energy anyway | DESI BAO, SNe (Pantheon+, DES-Y5) | Low to medium |
| O7 | GW leakage: `d_L^GW ≠ d_L^EM` at Hubble distances | **Core**, small effect | Yes, if detected | LIGO/Virgo/KAGRA dark sirens, LISA, ET/CE | Medium |
| O8 | Large-angle power deficit (low `ℓ`) from the finite parent star | **Extension** | Weak; cosmic variance dominates at low `ℓ` | Planck, LiteBIRD | Medium |
| O9 | Hemispherical asymmetry from an asymmetric collapse | **Extension** (non-spherical bulk) | Yes, but the bulk Schwarzschild is spherical, so the current model predicts none | Planck | Hard |
| O10 | Charged / AdS bulk corrections (`a⁻⁶` term) | **Extension**; reduces to O6 | Indirect, through the late-time expansion only: the relative effect on `H²` grows with time (`BulkCosmology.abs_frw_sub_le` and scaling) | DESI BAO, SNe | Done (Lean bound + scaling) |
| O11 | GW "horizon echoes" | **Not applicable** | No: comes from other black-hole work, not derived here | — | — |
| O12 | Analogue gravity (BEC, fluid white holes) | **Weak** | No: tests the mechanism (thermal boundary → spectrum), not this cosmology | Lab experiments | — |
| O13 | Sub-millimetre deviations from Newton's law | **Not applicable** | — | Torsion balances | Ruled out by `eq51`: the crossover `r_c` is Hubble-sized, so DGP changes gravity at large distances, not small ones |

### Notes on each option

**O1, spectral tilt.** The paper suggests two ways to get a red tilt (Sec. 5):
(a) gravitational Jeans instability of the thermal atmosphere for `k < k_J ≃ 0.2 T_b (T_b/M₅)^{3/2}`,
which the paper itself calls "a potential origin for the slight red tilt (i.e. n_s < 1)";
(b) gradual "unfreezing" of extra graviton polarizations, as in cascading gravity.
Each is a *different extended model*. Both would need to produce `n_s ≈ 0.965` without
fine-tuning, and each then predicts a running `dn_s/d ln k`, which is a second, independent
check.

**O2, non-Gaussianity.** The paper lists this as the next challenge (Sec. 5) but gives no
prediction. A thermal origin generally gives a non-Gaussian signal unlike single-field
inflation. Computing the three-point function of the thermal atmosphere is the task. Lean side:
state the three-point function as a hypothesis, in the same style as Eq. (39).

**O3, tensors.** The paper does not discuss tensor modes. Thermal fluctuations of a matter
field source scalar curvature. What sources tensors here, and at what level? If the answer is
"nothing significant", then a detected `r` (for example by LiteBIRD) rules the model out.
Inflation predicts a range that reaches down to `r ~ 10⁻³`.

**O4, curvature with anisotropy.** *Update 2026-11-18: unobservable for a stellar-mass parent
(an order-of-magnitude estimate, not a Lean result).* Sec. 5 of the paper, item 2, reads:
"If one assumes that the initial Hubble constant is the ∼ 5D Planck mass ... we have
`−Ω_k ∼ (M₅r_h)⁻² ∼ M₅/M_*`". So this is the curvature at the start, when `H ∼ M₅`, not today.
`Ω_k ∝ 1/(aH)²` then grows with standard ΛCDM expansion (Planck 2018 values) from `H = M₅` to
`H₀`, by a factor `≈ 6×10³⁷` for `M₅ = 9 MeV` (the `eq51_numeric` bound) and `≈ 7×10³⁶` for
`M₅ = 1 MeV`. Today's value is about `M₅²/M_*` times a constant, so the bound on `M₅` caps it:
`−Ω_k ≈ 5×10⁻²²·(M_⊙/M_*)`. Meeting `|Ω_k| ≲ 0.002` only needs `M_* ≳ 5×10¹¹ kg`, so the
flatness problem is solved with a wide margin. But a *detectable* `Ω_k ≳ 10⁻⁴` needs
`M_* ≲ 10¹³ kg`, the mass of a mountain, not a star. The anisotropy that the paper pairs
with curvature appears "on the scale of the curvature", so it is unobservable too. The
estimate assumes standard radiation-era scaling from `H ∼ M₅` and ignores changes in `g_*`;
it is good to an order of magnitude.

The original note: the Lean structure requires `𝒦 > 0`, i.e. a closed
universe. The paper estimates `−Ω_k ∼ M₅/M_*` for a parent star of mass `M_*`, and says that a
detected curvature "should come with" large-scale anisotropy. The *pairing* is the distinctive
prediction. First check whether the closed slicing is essential or a choice: flat and open
slicings exist, with planar and hyperbolic black branes.

**O5, dark radiation and BBN.** *Update 2026-11-18: ruled out as a signal, in Lean
(`DarkRadiation.lean`, see P3).* The bulk black hole enters `H²` with weight `1/(r_c H)`, not
`1`, so `|ΔN_eff| ≤ 3×10⁻¹⁴` at BBN. The original note follows. It assumed the black hole
would act like full-weight extra radiation, which is false. In the radiation era `ρ_BH/ρ` is constant, since both scale as
`a⁻⁴` (`BraneCosmology.radiation_era_ratio`, M3.2). So the bulk black hole behaves like extra radiation at BBN and at
recombination. It enters the expansion through the quadratic (26), not by simple addition, so
work out the effective `ΔN_eff` through that equation.

**O10, charged and AdS bulks.** For any bulk, `|H² + 𝒦/a² − H_std²| ≤ (y² + y√(1 +
|ρ_bulk|/ρ))H_std²` with `y = 1/(r_c H_std)` (`BulkCosmology.abs_frw_sub_le`). On the normal
branch the leading term is attained when `|ρ − ρ_bulk| ≫ ρ̃_s`, since then
`ρ̃_- ≈ −√(2ρ̃_s(ρ − ρ_bulk))`. For a charge term `ρ_Q ∝ a⁻⁶`, the relative effect
`y√(1 + ρ_Q/ρ)` scales as `a√(a² + C)` in the radiation era and as `√(a³ + C)` in the matter
era (a scaling argument, not a Lean theorem). Both grow with `a`. So the charge is most visible
at late times, and BBN constrains it less than the late-time expansion does. O10 reduces to O6.
In Lean: during BBN any bulk density with `|ρ_bulk| ≤ 10²⁴ρ` gives `|ΔN_eff| ≤ 0.03`
(`BulkCosmology.abs_deltaNeff_bbn`).

**O6, expansion history.** The normal DGP branch does not self-accelerate, so it still needs
dark energy. Since `r_c ≳ 3/H₀`, the departures from ΛCDM are small. Most useful as a
consistency check and to bound `r_c`.

**O7, GW leakage.** In DGP, gravitational waves leak into the bulk over distances comparable
to `r_c`, so their luminosity distance grows faster than the one measured with light. Since
`r_c` is Hubble-sized, GW170817 at ~40 Mpc is too close to see this. High-redshift sirens are
needed: LISA massive black-hole binaries, Einstein Telescope / Cosmic Explorer.

## 3. Pathway template

Copy this block into section 5 for each new pathway.

```markdown
### P<n>: <short name>

- **Status:** idea | has formula | has code | has forecast | confronted with data | dead
- **Hypothesis (one sentence):** If <model + extension>, then <observable> = <value/range>.
- **Model inputs:** <parameters and assumptions; link Lean names>
- **Prediction:** <formula; free parameters; how the prediction is computed>
- **Null comparison:** <what inflation + ΛCDM predicts for the same observable>
- **Data / instrument:** <current constraint; upcoming sensitivity and date>
- **Falsification criterion (fixed in advance):** <the result that kills it>
- **Lean link:** <ROADMAP milestone; theorem names once they exist>
- **Next concrete step:** <one task, small enough to start this week>
- **Open questions:**
- **Log:** <date: what changed>
```

## 4. Decision gates

Work in order. Do not spend effort past a gate that has not been passed.

| Gate | Question | Passes when | Lean dependency |
|---|---|---|---|
| **G0** | Is the parameter region well defined? | The sign tension is resolved (done, M3.1) and the consistent (orientation, branch, `ρ_BH/ρ`) region is characterized across cosmic history (done, M3.2: `normal_branch_no_crossing`, `ratio_antitoneOn`, `matter_era_growth_le_small`). A fixed `ε = -1` excludes a realistic matter era, so the white-hole history needs `ε` to change, which is possible only on or inside the horizon (`sign_change_inside`). Whether `ε` may change is open | `M3.1`, `M3.2`, `M2` |
| **G1** | Can an extension produce the observed tilt? | Some extension (P1) gives `n_s` within 2σ of the data without fine-tuning | `M7.2`, `M7.3` |
| **G2** | Is the background consistent? | The extended model fits BBN, CMB and BAO at least as well as ΛCDM + `ΔN_eff` | `M4`, `M8` |
| **G3** | Is there a distinct prediction? | At least one observable (O2–O7) differs from inflation + ΛCDM by more than the forecast error of an instrument operating in the next ~10 years | `M8.2` |
| **G4** | Is it pre-registered? | The prediction and its falsification criterion are written down (and ideally posted) before the relevant data release | `M8.3` |

If G1 fails for every extension tried, the right conclusion is that the holographic origin is
ruled out in this form. That is a legitimate result.

## 5. Pathways

### P1: Red tilt from Jeans instability of the thermal atmosphere

- **Status:** has code. **Dead in its linear form** (G1 fails); see
  [`phenomenology/p1_jeans/README.md`](../phenomenology/p1_jeans/README.md)
- **Hypothesis:** If the brane's thermal atmosphere is gravitationally Jeans-unstable below
  `k_J ≃ 0.2 T_b (T_b/M₅)^{3/2}`, the resulting growth of long-wavelength modes gives
  `n_s − 1 ≈ −0.035` at the CMB pivot scale.
- **Model inputs:** `T_b/M₅` (fixed by `eq49`); the Jeans scale; the duration of the unstable
  phase relative to the Hubble time (the paper flags this as uncertain); normal branch.
- **Prediction:** `Δ²_ζ ∝ ∫ dx (1+x²)⁻² F(y√(1+x²))`, `y = k/k_J`, with the 4D growth
  `F(z) = cosh²(τ√(1-z²))` below the Jeans scale and `1` above it (`τ = Γ₀Δt`). Exact
  consequences: in the bulk, `α_s/(n_s - 1) = 1 + 1/(1 - y²) ≥ 2`; on the brane, `n_s = 1`
  exactly for `k ≥ k_J`; `∫(n_s - 1) d ln k = -2 ln cosh τ` over all scales.
- **Null comparison:** single-field slow roll gives `n_s ≈ 0.965` with running
  `α_s ~ (n_s−1)² ~ 10⁻³`.
- **Data:** Planck 2018 `n_s = 0.9649 ± 0.0042`. Running is currently consistent with zero at
  the `~10⁻²` level.
- **Falsification criterion:** the mechanism gives `|n_s − 0.965| > 3σ` for every allowed
  value of the extension parameters, or it needs an unstable phase longer than the cosmology
  permits.
- **Lean link:** `M7.2` (scale invariance at leading order → falsification theorem),
  `M7.3` (sign of the next-order term, `SecondOrder.lean`; `M′ > 0` at every scale,
  `BlueTilt.lean`), `M8.3` (`Jeans.lean`: exact result 1 for the unprojected spectrum,
  `runningIndex_jeans`, `planck2018Running_not_fits_jeans`; `Running.lean` for the class, P4).
- **Next concrete step:** none required. Optional: run CAMB with the window spectrum through the
  Planck 2018 likelihood (Cobaya), to make the numerical verdict on the window final. A
  nonlinear or non-static P1 stays local, so P4 covers it unless it tunes a feature to the
  pivot.
- **Open questions:** Is the instability actually active for long enough before horizon
  exit? Does it disturb the Gaussianity assumed in Eq. (39)?
- **Log:** 2026-11-17: created from Sec. 5 of the paper. 2026-11-18: M7.3 computation: in the
  simple model, the `O(κ²)` term is blue (`n_s − 1 ≈ 0.037κ²`). So the red tilt must come from
  the extension. The next order of the simple model cannot supply it. 2026-11-18: proved in Lean
  for small `κ` (`ObsData.not_fits_next_order`). 2026-11-18: proved for all `κ`: `n_s > 1` at
  every scale (`spectralIndex_thermal_gt_one`, `ObsData.not_fits_thermal`). The simple model
  gives a blue spectrum whatever `T_b` is, so P1 must reverse the sign, not just shift it.
  2026-11-18: linear Jeans computation (`phenomenology/p1_jeans/`). With the pivot well inside
  the unstable range, `n_s = 0.965` forces `α_s ≈ -0.065`: 8.6σ to 9.4σ from Planck 2018
  (`α_s = -0.0045 ± 0.0067`). A window at `y = k/k_J ∈ [0.74, 0.81]`, `τ ∈ [0.165, 0.188]`
  passes `(n_s, α_s)` at the pivot, but is fine-tuned (`k_J` within 10% of `0.065 Mpc⁻¹`), has
  `n_s = 1` exactly for `k ≥ k_J`, and gives `ln P(0.1)/P(0.008) ≥ -0.034` against
  `-0.089 ± 0.011`. Verdict: the falsification criterion is met, so P1 is dead in this form.
  G1 now rests on P2 or on a non-linear version of P1. 2026-11-18: P2 fails too (sign), so a
  non-linear or non-static P1 is the remaining route among the paper's suggestions.
  2026-11-18: P4 closes that route for local physics (`planck2018Running_not_fits_local`).
  Exact result 1 is proved in Lean for the unprojected spectrum, at every order in `y`
  (`runningIndex_jeans`, `planck2018Running_not_fits_jeans`).

### P2: Red tilt from cascading-gravity polarizations

- **Status:** has code. **Dead in its linear form** (G1 fails, on the sign); see
  [`phenomenology/p2_cascade/README.md`](../phenomenology/p2_cascade/README.md)
- **Hypothesis:** If extra graviton polarizations unfreeze gradually (cascading gravity, i.e.
  6D embedding with scale `M₆`), the strengthening of the bulk propagator in the infrared
  produces a red tilt.
- **Model inputs:** `M₅`, `M₆`; the transition scale `M₅³/M₆⁴`; the Vainshtein profile.
- **Prediction:** relative to 5D GR, the 4D power of `ζ` is multiplied by
  `G(K) = (K/(K + m))² · r^{2s(K)}`, with `m ∼ M₆⁴/M₅³` and `r = 3/(4(1 − c²))`. The extra
  scalar couples only to the trace `δT = -(1 − 4c²)δρ`. It boosts the Newtonian potential `g₀₀`,
  but it lowers the spatial potential that the paper identifies with `ζ` (Eq. 47), for every
  `0 ≤ c² ≤ 1/4`. For the paper's radiation atmosphere (`c² = 1/4`) it does nothing. `G` is
  nondecreasing in `K`, so with `M7.3` the result is `n_s > 1` at every scale, for every `M₆`.
- **Null comparison:** as P1.
- **Data:** as P1, plus large-scale-structure tests of modified gravity.
- **Falsification criterion:** as P1.
- **Lean link:** `M7.3` and `Cascade.lean` (M8.3). Tilts add (`spectralIndex_mul`), so `n_s > 1`
  survives any positive nondecreasing factor (`spectralIndex_thermal_mul_gt_one`). **Fourth
  falsification theorem:** `ObsData.not_fits_thermal_mul`, with the cascade instance
  `ObsData.not_fits_cascade`. The tensor-structure signs are `spatialCoeff_quarter_le_third`
  and `newtonCoeff_third_le_quarter`.
- **Next concrete step:** none for this form. Escape routes, all outside the paper's model:
  1. a ghost-like brane-bending mode, which the paper excises;
  2. a stiff atmosphere (`ρ < 4p`);
  3. a brane observable that follows `g₀₀`, not `g_ab`. The radiation atmosphere makes even
     this one ineffective.
- **Log:** 2026-11-17: created from Sec. 5 of the paper. 2026-11-18: linear computation
  (`phenomenology/p2_cascade/`). The 6D propagator softens gravity in the IR, and the scalar's
  `+(1/12)η_μν δT` term leaves `ζ` unchanged for radiation and lowers it by up to `3/4` for
  dust. Both are blue, so P2 is dead in this form. It fails on the sign, not on the shape. A
  counterfactual IR boost of `ζ`, `exp(B/(1 + (K/K_V)^q))`, would fit only if all three hold:
  - it is broad (`q ≲ 1.5`; on a power-law tail `|α_s/(n_s − 1)| = q`);
  - it is large (`B ≳ 0.1`, against `2 ln(9/8) = 0.24` for the dust Newtonian boost);
  - it is centred within a factor of about 3 of the pivot.

  G1 has now failed for both of the paper's extensions. 2026-11-18: proved in Lean for every
  `M₆`, `c² ≤ 1/4` and decreasing screening profile (`ObsData.not_fits_cascade`).
  2026-11-18: the exact Part B statements are in Lean (`Boost.lean`): `|n_s − 1| ≤ |B|q/4`, and
  `α_s/(n_s − 1) = q(1 − u)/(1 + u)` (`runningIndex_boost`).

### P3: Background: closed curvature, dark radiation, BBN

- **Status:** **closed** (2026-11-18). Dark radiation: proved in Lean for any bulk. Curvature:
  unobservable for a stellar-mass parent (order-of-magnitude estimate, O4). What remains is the
  late-time expansion, where `r_c H ∼ 1` (O6).
- **Hypothesis:** The extended model fits BBN, the CMB and BAO with `Ω_k < 0` and a
  bulk-black-hole contribution that acts like `ΔN_eff`, with values inside current bounds.
- **Model inputs:** `Ω_k`, `r_h`, `ρ̃_s`, branch; `ρ_BH ∝ a⁻⁴` (`rhoBH_scaling`).
- **Prediction:** `H(z)` from the normal branch of Eq. (26); effective `ΔN_eff(z)`; BBN yields.
- **Null comparison:** flat ΛCDM, `N_eff = 3.044`.
- **Data:** Planck 2018 + BAO `|Ω_k| ≲ 0.002`; Planck `N_eff = 2.99 ± 0.17`; DESI BAO; D/H and
  Yₚ.
- **Falsification criterion:** no allowed parameter point gives `Ω_k < 0` and `ΔN_eff` together
  within 2σ of the data.
- **Lean link:** `M3.2`, `M4.1`, `M8.1`. `BraneCosmology.normal_branch_frw_rc_of_le` (M4.4): on
  the normal branch with `0 ≤ ρ_BH ≤ ρ`, `|H² + 𝒦/a² − H_std²| ≤ H_std/r_c`, where
  `H_std² = (8πG_N/3)ρ`. So the bulk black hole changes `H²` by a relative amount of at most
  `1/(r_c H_std)`. It does not act as `ΔN_eff` where `r_c H ≫ 1`.
  `DarkRadiation.lean` removes both hypotheses (the branch and `ρ_BH ≤ ρ`):
  `|H² + 𝒦/a² − H_std²| ≤ (y + (3/2)y²)H_std²` with `y = 1/(r_c H_std)`, on either branch and for
  any `ρ_BH ≥ 0` (`BraneCosmology.abs_frw_sub_le`). On the normal branch the black hole's own part
  of `ρ̃` is `0 ≤ Δ ≤ ρ_BH/(r_c H_std)` (`BraneCosmology.darkRadiation_le`): it acts like dark
  radiation, but with weight `1/(r_c H)`, not `1` as in Randall–Sundrum. With `r_c ≥ 3/H₀`, the
  `ΔN_eff` inferred from `H²` is at most `3×10⁻¹⁴` during BBN (`H ≥ 10¹⁴H₀`, `ρ ≤ 8ρ_ν`;
  `abs_deltaNeff_bbn`) and at most `1.1×10⁻³` up to recombination (`H ≥ 10⁴H₀`, `ρ ≤ 32ρ_ν`;
  `abs_deltaNeff_recombination`). The epoch values of `H/H₀` and `ρ/ρ_ν` are ΛCDM hypotheses.
- **Consequence:** the early background passes G2 trivially: it is FRW to `10⁻¹⁴` at BBN. For
  the same reason it offers no early-universe signature for G3. Any background signature has to
  come from late times, where `r_c H ∼ 1` (DGP-type expansion, already constrained by BAO and
  supernovae), or from `Ω_k < 0`, which is standard curvature.
- **Next concrete step:** none. The early background is FRW to high precision (O5, O10), and the
  curvature is unobservable for a stellar-mass parent (O4). What remains of the background is
  the late-time expansion (O6).
- **Log:** 2026-11-17: created. 2026-11-17: the Lean bound above suggests that, on the normal
  branch with `ρ_BH ≤ ρ`, the `ΔN_eff` route needs `r_c H ≲ 1` at BBN. That conflicts with
  `r_c ≳ 1/H₀`. A numerical check with BBN values is still to do. 2026-11-18: done in Lean, with
  no branch and no `ρ_BH ≤ ρ` hypothesis (`DarkRadiation.lean`). `|ΔN_eff| ≤ 3×10⁻¹⁴` at BBN. The
  dark-radiation route is closed. 2026-11-18: extended to any bulk
  (`BulkCosmology.abs_frw_sub_le`): O10 reduces to O6. The paper's curvature estimate is for
  the initial time; evolved to today it gives `−Ω_k ≈ 5×10⁻²²·(M_⊙/M_*)`, unobservable for a
  stellar-mass parent (O4).

### P4: Any local, static extension of the paper's mechanism

- **Status:** **dead** (G1 fails for the whole class). Proved in Lean, given the form of the tilt.
- **Hypothesis:** Some extension of the paper's mechanism, with every mode imprinted at the one
  static equilibrium `(a_b, T_b)` (Sec. 4) and short-range physics with some scale `s`, gives
  `n_s ≈ 0.965` with the observed running.
- **Model inputs:** the paper's single imprinting moment; local physics, so the spectrum is
  analytic in `k²` near `k = 0`. Near the pivot the tilt is then
  `n_s − 1 = Σᵢ cᵢ (k/sᵢ)^{pᵢ}` with `pᵢ = 2, 4, …`. The thermal spectrum is one such term,
  blue with `p = 2` (`next_order_blue`). P1 and P2 are two choices of the other terms.
- **Why the obvious candidates fail:**
  - A cooling atmosphere (time-dependent `T_b`): every mode is imprinted at the same moment, so
    `T_b` changes only the amplitude.
  - A steeper red term: each term contributes `pᵢ` times its own tilt to the running
    (`runningIndex_of_tilt`). A single term gives `α_s = p(n_s − 1)` exactly.
- **Prediction:** with red terms of power `≥ q` and blue terms of power `≤ q`,
  `α_s ≤ q(n_s − 1)` (`runningIndex_le_of_tilt`). For local physics `q = 2`, so
  `α_s ≤ 2(n_s − 1)`.
- **Null comparison:** single-field slow roll, `α_s ~ (n_s − 1)² ~ 10⁻³`.
- **Data:** Planck 2018 VI, ΛCDM + running, TT,TE,EE+lowE+lensing: `n_s = 0.9641 ± 0.0044`,
  `dn_s/d ln k = −0.0045 ± 0.0067` (`planck2018Running`).
- **Falsification criterion:** `q(n_s,hi − 1) < α_s,lo`, i.e. the steepest allowed running is
  below the measured interval.
- **Result:** Planck 2018 excludes every `q ≥ 0.36` (`planck2018Running_not_fits_tilt`): a red
  tilt that fits must be nearly scale free in `k`. For local physics (`q = 2`) a fit to `n_s`
  forces `α_s ≤ −0.063` (`runningIndex_le_local_planck2018`), 8.7σ from the measured value
  (`planck2018Running_not_fits_local`). This generalizes P1's `α_s/(n_s − 1) ≥ 2` to every
  local extension, P1 and P2 included. For P1 the exact form, at every order in `y`, is in
  `Jeans.lean` (`runningIndex_jeans`).
- **Lean link:** `Running.lean`; ROADMAP M8.3.
- **What is not covered:**
  1. A tilt that breaks the sign condition. Locally, that is a red `k²` term cancelled by a blue
     `k⁴` term, so `α_s = 0` at the pivot only because the tilt has an extremum there. That is
     a feature tuned to the pivot, like P1's window, and the tilt does not stay red over the
     observed range.
  2. The exact thermal tilt, which the theorem uses at leading order (`∝ κ²`). The exact tilt is
     blue at every scale (`spectralIndex_thermal_gt_one`), which only makes the fit harder.
- **Ways out (both new models, not extensions of this paper):**
  1. Modes imprinted at different times, for example at horizon exit, as in inflation or
     string-gas cosmology. This replaces the paper's single static equilibrium.
  2. Scale-free, long-range correlations in the atmosphere (a near-critical state with an
     anomalous dimension `≈ 0.035`). Local physics does not give `p < 0.36`.
- **Next concrete step:** none within this paper's mechanism. By the rule in section 4, do not
  pursue either way out unless a concrete model is proposed.
- **Log:** 2026-11-18: created and closed. The cooling-atmosphere route fails because the paper
  imprints all modes at once. The running bound is proved in Lean for any finite sum of
  power-law tilts with the sign condition, and instantiated with Planck 2018 with running.

*(Add P5 onward from O2, O3 and O7 with the template.)*

## 6. Shared tooling

| Need | Tool | Notes |
|---|---|---|
| Background and Boltzmann code | CLASS (`classy`) or CAMB | CLASS accepts an external primordial spectrum, so P1/P2 can be plugged in. The background needs the branch of Eq. (26) |
| Sampling | Cobaya | Standard Planck/ACT/DESI likelihoods are available |
| Model comparison | Nested sampling (PolyChord) | Compute Bayesian evidence against ΛCDM, not only best-fit χ² |
| Forecasts | Fisher matrices | For G3: Simons Observatory, LiteBIRD, LISA |
| Agreement with Lean | Golden values (`M8.4`, `Golden.lean`) | `phenomenology/tests/test_golden.py` checks `jeans_tilt.py` and `cascade_tilt.py` against exact values proved in Lean; CI runs it. Add vectors for CLASS/CAMB code when it exists |

Suggested layout once code exists: `phenomenology/` with one subdirectory per pathway, kept
apart from the Lean library.

## 7. References

Check these before citing them in a paper.

- R. Pourhasan, N. Afshordi, R. B. Mann, *Out of the White Hole*, arXiv:1309.1487, JCAP 04 (2014) 005.
- G. Dvali, G. Gabadadze, M. Porrati, *4D gravity on a brane in 5D Minkowski space*, hep-th/0005016.
- C. de Rham, G. Dvali, S. Hofmann, J. Khoury, O. Pujolàs, M. Redi, A. J. Tolley, *Cascading
  gravity: extending the DGP model to higher dimension*, arXiv:0711.2072 (the paper's ref. [25]).
- C. de Rham, S. Hofmann, J. Khoury, A. J. Tolley, *Cascading gravity and degravitation*,
  arXiv:0712.2821.
- C. de Rham, J. Khoury, A. J. Tolley, *Cascading gravity is ghost free*, arXiv:1002.1075.
- J. Khoury, M. Wyman, *N-body simulations of DGP and degravitation theories*, arXiv:0903.1292.
- Planck Collaboration, *Planck 2018 results VI: Cosmological parameters*, arXiv:1807.06209.
- J. Pardo, M. Fishbach, D. Holz, D. Spergel, *Limits on the number of spacetime dimensions from GW170817*, arXiv:1801.08160.
- E. Di Valentino, A. Melchiorri, J. Silk, *Planck evidence for a closed Universe…*, arXiv:1911.02087.
- N. Afshordi et al., *From Planck data to Planck era: observational tests of holographic cosmology*, arXiv:1607.04878. (A different holographic model, but a useful example of a confrontation with data.)
