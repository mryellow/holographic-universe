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

### What the formalization already gives

| Fact | Lean | Use for testing |
|---|---|---|
| `T_b/M₅ ≈ 0.171` is fixed by the CMB amplitude | `eq49`, `eq49_planck2013_sharp`, `eq49_planck2018` | One parameter is already used up by data. Planck 2013 gives `[0.17061, 0.17216]`; Planck 2018 gives `[0.1697, 0.17051]` |
| `r_c = M₄²/(2M₅³) ≳ 3/H₀` | `rc_eq_planck`, `eq51` | Gravity changes at **Hubble** scales, not at short distances |
| `ρ_BH ∝ a⁻⁴` | `rhoBH_scaling` | Behaves like radiation, so BBN and `N_eff` can see it |
| `𝒦 > 0` (closed slicing) | `BraneCosmology.K_pos` | Predicts `Ω_k < 0` |
| Bounds on `ρ̃_s/ρ` per branch | `eq33`–`eq35` | Restrict the allowed parameter region |
| Normal-branch sign tension | `orientation_minus_branch`, `pressure_of_timelike_junction` | **Resolved** (M3.1): the paper's `ε = -1` is too strong. `ε` follows the sign of `ρ̃`, so the normal branch with `ρ_BH < ρ` has `ε = +1` |

### Parameter inventory

| Parameter | Meaning | Status |
|---|---|---|
| `G_N` (`M₄`) | 4D Newton constant | measured |
| `G_b` (`M₅`) | 5D gravitational constant | bounded: `M₅ ≤ 9 MeV` (Eq. 51, `eq51_numeric`), from `r_c ≳ 3/H₀` |
| `T_b` | temperature of the brane's thermal atmosphere | fixed relative to `M₅` by `A_s` (Eq. 49) |
| `𝒦`, i.e. `Ω_k` | spatial curvature | free; paper estimates `−Ω_k ∼ M₅/M_*` (Sec. 5) |
| `r_h`, i.e. `μ` | bulk black-hole horizon / mass | free; enters through `ρ_BH` |
| `ε` (Eq. 32) | allowed size of `ρ̃/ρ` | modeling choice, `~0.1` in the paper |
| branch, orientation | `ρ̃_±`, normal orientation | normal branch preferred (no ghosts); orientation fixed by the sign of `ρ̃` (`orientation_iff`) |
| *extension parameters* | whatever produces the red tilt | **to be defined by P1** |

## 2. Catalogue of options

Verdicts:

- **Core:** follows from the model as written, or from the extension that P1 needs.
- **Extension:** needs a modified model, but the modification is well motivated.
- **Weak:** possible in principle, but it would not tell this model apart from standard
  inflation + ΛCDM.
- **Not applicable:** the model does not predict it, or the formalization rules it out.

| # | Option | Verdict | Distinguishes from inflation? | Data | Starting effort |
|---|---|---|---|---|---|
| O1 | Spectral tilt `n_s` and its running | **Core** (gate) | Yes, through how the tilt arises and the running it implies | Planck, ACT, SPT, Simons Observatory | Theory: hard |
| O2 | Primordial non-Gaussianity (`f_NL`, bispectrum shape) | **Core** | Probably: thermal correlators give a specific shape | Planck limits, future LSS surveys | Theory: hard |
| O3 | Tensor-to-scalar ratio `r` | **Core** | Yes, if the model predicts `r ≈ 0` or a distinct tensor tilt | BICEP/Keck, LiteBIRD | Theory: medium |
| O4 | Spatial curvature `Ω_k < 0`, together with large-scale anisotropy | **Core** (paper, Sec. 5) | Yes: the paired signal is unusual | Planck + BAO (`|Ω_k| ≲ 0.002`), future 21 cm / LSS | Medium |
| O5 | Dark radiation `ΔN_eff` and BBN abundances | **Core** (paper, Sec. 5) | Partly; many models add dark radiation | Planck, BBN (D/H, Yₚ), Simons Observatory | Medium |
| O6 | Late-time expansion `H(z)` (DGP normal branch) | **Core** | Weakly; the normal branch needs dark energy anyway | DESI BAO, SNe (Pantheon+, DES-Y5) | Low to medium |
| O7 | GW leakage: `d_L^GW ≠ d_L^EM` at Hubble distances | **Core**, small effect | Yes, if detected | LIGO/Virgo/KAGRA dark sirens, LISA, ET/CE | Medium |
| O8 | Large-angle power deficit (low `ℓ`) from the finite parent star | **Extension** | Weak; cosmic variance dominates at low `ℓ` | Planck, LiteBIRD | Medium |
| O9 | Hemispherical asymmetry from an asymmetric collapse | **Extension** (non-spherical bulk) | Yes, but the bulk Schwarzschild is spherical, so the current model predicts none | Planck | Hard |
| O10 | Charged / AdS bulk corrections (`a⁻⁶` term) | **Extension** | Indirect, through BBN and the expansion | BBN, CMB | Low (Lean `M5.3`) |
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

**O4, curvature with anisotropy.** The Lean structure requires `𝒦 > 0`, i.e. a closed
universe. The paper estimates `−Ω_k ∼ M₅/M_*` for a parent star of mass `M_*`, and says that a
detected curvature "should come with" large-scale anisotropy. The *pairing* is the distinctive
prediction. First check whether the closed slicing is essential or a choice: flat and open
slicings exist, with planar and hyperbolic black branes.

**O5, dark radiation and BBN.** In the radiation era `ρ_BH/ρ` is constant, since both scale as
`a⁻⁴` (`BraneCosmology.radiation_era_ratio`, M3.2). So the bulk black hole behaves like extra radiation at BBN and at
recombination. It enters the expansion through the quadratic (26), not by simple addition, so
work out the effective `ΔN_eff` through that equation.

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
  `BlueTilt.lean`).
- **Next concrete step:** to close the window below, run CAMB with the window spectrum through
  the Planck 2018 likelihood (Cobaya). Otherwise move to P2, or to a nonlinear or
  non-static version of P1 that breaks the assumptions listed in the P1 note.
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
  G1 now rests on P2 or on a non-linear version of P1.

### P2: Red tilt from cascading-gravity polarizations

- **Status:** idea
- **Hypothesis:** If extra graviton polarizations unfreeze gradually (cascading gravity, i.e.
  6D embedding with scale `M₆`), the strengthening of the bulk propagator in the infrared
  produces a red tilt.
- **Model inputs:** `M₅`, `M₆`; the transition scale `M₅³/M₆⁴`.
- **Prediction:** to be derived.
- **Null comparison:** as P1.
- **Data:** as P1, plus large-scale-structure tests of modified gravity.
- **Falsification criterion:** as P1.
- **Lean link:** `M5.1` (generic bulk), new work on 6D embeddings.
- **Next concrete step:** literature review of cascading gravity (the paper's ref. [25]);
  find how the effective Newton constant runs with scale.
- **Log:** 2026-11-17: created from Sec. 5 of the paper.

### P3: Background: closed curvature, dark radiation, BBN

- **Status:** idea
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
- **Next concrete step:** write `H²(a)` on the normal branch in closed form as a function of
  `(ρ_m, ρ_r, ρ_Λ, ρ_BH, ρ̃_s, 𝒦)`. Plot it against flat ΛCDM for `ρ_BH/ρ_r ∈ {0.01, 0.1}`.
- **Log:** 2026-11-17: created. 2026-11-17: the Lean bound above suggests that, on the normal
  branch with `ρ_BH ≤ ρ`, the `ΔN_eff` route needs `r_c H ≲ 1` at BBN. That conflicts with
  `r_c ≳ 1/H₀`. A numerical check with BBN values is still to do.

*(Add P4 onward from O2, O3 and O7 with the template.)*

## 6. Shared tooling

| Need | Tool | Notes |
|---|---|---|
| Background and Boltzmann code | CLASS (`classy`) or CAMB | CLASS accepts an external primordial spectrum, so P1/P2 can be plugged in. The background needs the branch of Eq. (26) |
| Sampling | Cobaya | Standard Planck/ACT/DESI likelihoods are available |
| Model comparison | Nested sampling (PolyChord) | Compute Bayesian evidence against ΛCDM, not only best-fit χ² |
| Forecasts | Fisher matrices | For G3: Simons Observatory, LiteBIRD, LISA |
| Agreement with Lean | Golden values (`M8.4`) | Unit tests that check the code against the formulas proved in Lean |

Suggested layout once code exists: `phenomenology/` with one subdirectory per pathway, kept
apart from the Lean library.

## 7. References

Check these before citing them in a paper.

- R. Pourhasan, N. Afshordi, R. B. Mann, *Out of the White Hole*, arXiv:1309.1487, JCAP 04 (2014) 005.
- G. Dvali, G. Gabadadze, M. Porrati, *4D gravity on a brane in 5D Minkowski space*, hep-th/0005016.
- Planck Collaboration, *Planck 2018 results VI: Cosmological parameters*, arXiv:1807.06209.
- J. Pardo, M. Fishbach, D. Holz, D. Spergel, *Limits on the number of spacetime dimensions from GW170817*, arXiv:1801.08160.
- E. Di Valentino, A. Melchiorri, J. Silk, *Planck evidence for a closed Universe…*, arXiv:1911.02087.
- N. Afshordi et al., *From Planck data to Planck era: observational tests of holographic cosmology*, arXiv:1607.04878. (A different holographic model, but a useful example of a confrontation with data.)
