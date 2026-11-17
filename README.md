# Holographic Universe — a Lean 4 formalization

This project formalizes the mathematics of

> R. Pourhasan, N. Afshordi, R. B. Mann, *Out of the White Hole: A Holographic Origin for the
> Big Bang*, [arXiv:1309.1487](https://arxiv.org/abs/1309.1487), JCAP 04 (2014) 005.

## What "proving the paper" means here

The paper is a physics model, not a theorem. Its physical claims (that our universe *is* a
3-brane outside a 5D black hole) cannot be proven. What can be checked is that the stated
conclusions **follow from the stated assumptions**. In this project:

- The **assumptions** are explicit hypotheses. Most are bundled as fields of
  `WhiteHole.BraneCosmology` in `Model.lean`.
- The **derivations** are Lean theorems checked against Mathlib.
- **Inputs that Mathlib cannot yet express** are listed as hypotheses, not `axiom`s, so the
  development stays sound. Examples are extrinsic curvature of a hypersurface in a 5D Lorentzian
  manifold, and thermal QFT correlators.

## Layout

| File | Content |
|---|---|
| `Basic.lean` | Couplings `G_N`, `G_b`; `ρ̃_s` (18); `r_c` (31); Planck masses (2) |
| `Bulk.lean` | 5D Schwarzschild `f(r)` (20); brane radius; `ρ_BH` (28); `μ` (29); horizon crossing; bulk density `ρ_bulk` for a general `f` |
| `InducedFluid.lean` | Friedmann + junction ⇒ quadratic; branches (26); reality (30); sign of `ρ̃` |
| `Pressure.lean` | Eq. (16) derived from continuity (12)–(13); Eq. (27) vs (16) |
| `Constraints.lean` | Observational bounds (33), (34), (35) |
| `Integrals.lean` | `∫ dx/(1+x²)² = π/2` over the real line, used in Eq. (48) |
| `Zeta.lean` | `ζ(5)` as a real series, identified with `riemannZeta 5`; `1.0369 ≤ ζ(5) ≤ 1.0370` |
| `Perturbations.lean` | Eq. (48) algebra; inversion for `T_b/M₅` (49); `M₅` bound (51) |
| `ThermalIntegral.lean` | M7.1: the thermal integral `M(κ)` of Eq. (46); `∫₀^∞ x⁵eˣ/(eˣ-1)² dx = 120ζ(5)`; `M(0) = 15ζ(5)/π²` |
| `ObsData.lean` | Observational data as parameters (`ObsData`); Planck 2013 and Planck 2018 instances; Eqs. (49), (51) per release |
| `ScaleInvariance.lean` | Spectral index; `n_s = 1` at leading order; the first falsification theorem against Planck 2013 and 2018 |
| `Monopoles.lean` | Eq. (50); `H ≲ M₅ ≲ 9 MeV` (51); plasma temperature `T ≤ 8.5×10⁴ TeV ≪ T_GUT` (52) |
| `GeneralBulk.lean` | `BulkCosmology`: the model for any blackening factor `f`; Eqs. (26), (30), (16) and the pressure-singularity results in general form |
| `AdSBulk.lean` | M5.2: Schwarzschild–AdS₅. `ρ_bulk = ρ_BH - ρ_Λ`, `ρ_Λ = 3/(8πG_N L²)`; Eq. (16) with `3P - ρ - 4ρ_Λ`; late-time `H²` on each branch; the normal branch cannot expand forever |
| `ChargedBulk.lean` | M5.3: Reissner–Nordström₅. `ρ_bulk = ρ_BH - ρ_Q`, `ρ_Q ∝ a⁻⁶`; Eq. (16) with `3P - ρ + 2ρ_Q`; no horizon above extremality |
| `Model.lean` | `BraneCosmology` structure (the Schwarzschild bulk); `toBulk`; the results instantiated on it |
| `Acceleration.lean` | Acceleration equation derived from Friedmann + continuity where `H ≠ 0`; existence of `ä` |
| `Instances.lean` | Non-vacuity: explicit `BraneCosmology` instances (static family, self-accelerating de Sitter vacuum) |
| `Orientation.lean` | Normal orientation `ε`: Eq. (16) from the timelike junction condition for either `ε`; origin of Eq. (27); `ε` fixed by the sign of `ρ̃` |
| `History.lean` | `ρ_BH/ρ` along a history: constant in a radiation era, `∝ 1/a` in a matter era, never rising while the universe expands; matter-era bound for `ε = -1`; an orientation change needs the brane on or inside the horizon |
| `Bounce.lean` | An expanding solution with `r_h > 0` and radiation (`ρ = ρ_BH`, closed form); it obeys the acceleration equation at every time |
| `Dynamics.lean` | Solutions (`IsSolution`: acceleration equation and Eq. (16) at every time). Reduction to an ODE: `ρ = ρ₀a^{-3(1+w)}` for `P = wρ`; the branch is fixed away from the singularity; `ȧ² = F(a)` |
| `LocalExistence.lean` | Picard–Lindelöf for `ȧ = ±√F(a)`: local existence and uniqueness away from `H = 0` and the singularity; a history is fixed locally by its data |
| `TurningPoint.lean` | The acceleration equation is `ä = F'(a)/2`; Picard–Lindelöf for it on `ℝ²`; a solution is fixed locally by `a` and `ȧ`, also at `H = 0` |
| `MaximalSolution.lean` | Maximal solutions of an autonomous ODE with a `C¹` field on an open set: existence, uniqueness, escape from compact sets at a finite end. For `ä = F'(a)/2`: a history ends only at `a → 0`, the singularity or `a → ∞`; a brane cosmology is the global maximal solution of its data |
| `FromSolution.lean` | The converse: a global solution of `ȧ² = F(a)` in the domain, with an orientation `ε` that obeys `ε ρ̃ ≤ 0`, defines a `BraneCosmology`. It is a solution of the equations of motion if `ä = F'(a)/2` |
| `NormalBranch.lean` | M2.3: with `ε = -1`, on the normal branch, and for matter with `ρ + 3P > 0`, `3P ≤ ρ`, every solution has `ä < 0` at every time, so no `BraneCosmology` is a solution |
| `Horizon.lean` | M4.3: inside the horizon `ȧ ≠ 0`; an expanding brane inside was inside and expanding at every earlier time, a contracting one stays inside; the exit time `t*` with `a(t*) = √𝒦 r_h` is unique; `H² = (8πG_b ρ̃/3)²` on the horizon |
| `Asymptotics.lean` | M4.4: late times on each branch (de Sitter `H → 1/r_c` on `ρ̃_+`, `H → 0` on `ρ̃_-`); standard FRW on the normal branch up to a relative error `√(2ρ̃_s/ρ)`; `P̃ → ∞` at the singularity, and a `BraneCosmology` with `3P ≤ ρ` is at rest there |
| `Singularity.lean` | Pressure singularity: `ρ̃ = ρ̃_s` ⇔ reality bound (30) saturated ⇔ branches meet; inside the horizon ⇔ `\|H\| ≥ 1/(2r_c)`; a floor on `a` in an expanding era |
| `Audit.lean` | Build-time axiom audit: every declaration, plus a pinned `#print axioms` list for the headline theorems |

## Equation map

| Paper | Lean | Status |
|---|---|---|
| (2), (31) `r_c = G_b/G_N = (3/16πG_N ρ̃_s)^½` | `Couplings.sqrt_eq_rc`, `rc_eq_planck` | proved |
| (3)–(10) brane geometry, Brown–York, Gauss–Codazzi | `BraneCosmology` fields | **assumed** |
| (11)–(13) Friedmann + continuity | `BraneCosmology` fields | **assumed** |
| (14) | — | superseded: the content is reproduced via (16) below |
| (15) ≡ (26) given (29) | `eq15_eq_eq26`, `mu_sq_term` | proved |
| (16) induced pressure | `pressure_of_continuity`, `BraneCosmology.pressure` | **derived** from (11)–(13) + junction |
| (16), (26), (30) for a general bulk `f` (not in the paper) | `pressure_of_continuity_bulk`, `isInduced_of_bulk`, `BulkCosmology.isInduced`, `BulkCosmology.reality`, `BulkCosmology.pressure` | proved: `ρ_BH` becomes `ρ_bulk` (`rhoBulk_blacken` for Schwarzschild), and Eq. (16) becomes `P̃ = (ρ̃² - 2ρ̃_s(P - P_b))/(2(ρ̃_s - ρ̃))` |
| Sec. 5: an AdS bulk "need not significantly change" the results | `rhoBulk_blackenAdS`, `BulkCosmology.pressure_AdS`, `reality_AdS`, `tendsto_hubble_sq_AdS`, `not_tendsto_atTop_normal_AdS` | proved, with one qualification: `ρ_BH` becomes `ρ_BH - ρ_Λ` and `3P - ρ` becomes `3P - ρ - 4ρ_Λ`. The late-time rate on `ρ̃_+` is `H² → (1 + √(1 + 4r_c²/L²))/(2r_c²)`. On `ρ̃_-` the limit of `ρ̃` is negative, so without a brane tension no history with `ρ → 0` expands forever |
| Charged bulk (not in the paper) | `rhoBulk_blackenRN`, `BulkCosmology.pressure_RN`, `reality_RN`, `rhoBulk_RN_neg_iff`, `singularity_hubble_lt_RN` | proved: `ρ_BH` becomes `ρ_BH - ρ_Q` with `ρ_Q ∝ a⁻⁶`, and `3P - ρ` becomes `3P - ρ + 2ρ_Q`. Above extremality, `r_h⁴ < 4q²`, there is no horizon, and at the singularity `\|H\| < 1/(2r_c)` |
| (20), horizon crossing `r = r_h` | `outside_horizon_iff`, `curv_mul_blacken` | proved |
| Fig. 3: the universe leaves the white hole at one time `t*` | `BraneCosmology.exists_unique_exit`, `white_hole_past`, `black_hole_future`, `deriv_ne_zero_of_inside` | proved: no rest inside the horizon; if an expanding brane inside the horizon is on or outside it later, the first time on the horizon is unique and the brane expands before it. That the brane reaches the horizon is a hypothesis |
| (24) `K_ij` | `BraneCosmology.junction` | **assumed** (with a typo corrected, see below) |
| (25) `K_ττ` = (10), timelike junction | `pressure_of_timelike_junction` | proved: gives (16) for **either** `ε` (with (25) and the acceleration equation as hypotheses) |
| Orientation `ε` vs branch and `ρ_BH/ρ` | `orientation_iff`, `orientation_plus_branch`, `orientation_minus_branch`, `minkowski_normal_branch`, `BraneCosmology.normal_branch_no_crossing` | proved: `ε = -1 ⇔ ρ̃ > 0`, `ε = +1 ⇔ ρ̃ < 0` |
| (26) branches `ρ̃_±` | `isInduced_of_junction`, `isInduced_iff`, `BraneCosmology.branches` | **derived** |
| (27) at `ε = -1` equals (16) | `eq27_neg_one` (and `eq27_one_ne` for `ε = +1`) | proved |
| Origin of (27) | `eq27_of_dropped_sign` | proved: (27) is what (25) gives after substituting `X = +(8πG_b/3)ρ̃`, i.e. the `ε = -1` junction condition |
| (28) `ρ_BH ∝ a⁻⁴` | `rhoBH_scaling` | proved |
| (30) reality constraint | `reality`, `BraneCosmology.reality` | **derived** |
| (30) equality ⇔ pressure singularity | `isInduced_eq_rhoS_iff`, `BraneCosmology.singularity_iff`, `branches_meet_iff` | proved, both directions; the branches meet only there |
| Sec. 5: the singularity is "always" inside the white-hole horizon | `BraneCosmology.singularity_inside_iff`, `singularity_inside_iff_curvature`, `singularity_inside_of_rc` | proved **with a condition**: inside exactly when `\|H\| ≥ 1/(2r_c)` (issue 7) |
| Late times: de Sitter on the self-accelerating branch | `BraneCosmology.tendsto_deSitter`, `expands_of_self_acc`, `tendsto_late` | proved: for `P = wρ`, `w > -1`, `ρ ≥ 0`, an expanding history with `a(t₀)² > 2𝒦r_c²` has `a → ∞`, `ρ̃ → 2ρ̃_s`, `H → 1/r_c` |
| Late times on the normal branch | `BraneCosmology.tendsto_normal` | proved: if `a → ∞`, then `ρ̃ → 0` and `H → 0` |
| Normal branch is standard FRW when `ρ ≫ ρ̃_s` | `abs_rhoTilde_minus_le`, `BraneCosmology.normal_branch_frw`, `normal_branch_frw_of_le`, `normal_branch_frw_rc_of_le` | proved: `\|ρ̃_-\| ≤ √(2ρ̃_s\|ρ - ρ_BH\|)`, so the relative error is at most `√(2ρ̃_s/ρ) = 1/(r_c H_std)` for `0 ≤ ρ_BH ≤ ρ`, with `H_std² = (8πG_N/3)ρ` |
| (16) at the singularity: `P̃ → ∞` | `tendsto_pressureTilde_atTop` | proved, for `ρ̃ → ρ̃_s` from below and `3P - ρ < 2ρ̃_s` |
| The singularity in the formal model | `BraneCosmology.singularity_at_rest`, `singularity_outside_of_le` | proved: with `ρ̃` differentiable, `H(3P - ρ - 2ρ̃_s) = 0` there. For `3P ≤ ρ`, `H = 0` and the brane is outside the horizon. A history that reaches the singularity with `H ≠ 0` can only start or end there (issue 4) |
| (32) `|ρ̃| ≤ ερ` | hypothesis | **assumed** (observational input) |
| (33) + side remarks | `eq33`, `eq33_side` | proved |
| (34) | `eq34` | proved |
| (35) | `eq35` | proved, with fewer hypotheses than stated: the branch assumption is redundant, and positivity of the denominator follows |
| (39)–(45), (47) thermal correlators | — | **assumed** (out of Mathlib's reach) |
| (46) `M(0) = 15ζ(5)/π² ≈ 1.576` | `thermalM_zero`, `integral_bose`, `thermalM_zero_bounds` | proved from the integral (46), with the vacuum term `ω₊ω₋/4` dropped: `M(0) ∈ [1.5758, 1.5761]` |
| (48) `∫dx/(1+x²)² = π/2` | `integral_univ_inv_one_add_sq_sq` | proved |
| (48) `= 25ζ(5)/(3072π⁴)(T_b/M₅)⁶` | `eq48_leading`, `eq48_leading_thermalM` | proved, with `M(0)` from (46) |
| `ζ(5) ∈ [1.0369, 1.0370]` (enters the coefficient of (48)) | `zeta5_bounds`, `riemannZeta_five_bounds`; sharper `zeta5_upper : ζ(5) ≤ 1.03694` | proved |
| (48) coefficient `25ζ(5)/(3072π⁴) ∈ [8.65, 8.67]×10⁻⁵` | `ampCoeff_bounds`; sharper `ampCoeff_sharp : [8.6627, 8.6631]×10⁻⁵` | proved |
| (49) `T_b/M₅ ≈ 0.171` | `eq49`, `eq48_eq49` | proved: `[0.1705, 0.1723]` from the Planck 2013 amplitude, with no numerical hypotheses (`eq49_of_coeff` is the version for a general coefficient) |
| (49) for any data release | `ObsData.tbm5_bounds`, `amplitude_inversion` | proved |
| (49), Planck 2013, sharp | `eq49_planck2013_sharp` | proved: `[0.17061, 0.17216]`, the paper's `0.17139 ± 0.00077` |
| (49), Planck 2018 | `eq49_planck2018` | proved: `[0.1697, 0.17051]`, i.e. `0.1701 ± 0.0004`. Disjoint from the 2013 interval (`planck2013_planck2018_disjoint`) |
| (48) at leading order: `n_s = 1` | `leadingSpectrum_ns`, `spectralIndex_comp` (`n_s − 1 = κM′(κ)/M(κ)` for the full form) | proved |
| Sec. 5: the simple model is ruled out | `leading_order_ruled_out_planck2013`, `leading_order_ruled_out_planck2018`; `planck2013_ns_excludes_one` (>5σ), `planck2018_ns_excludes_one` (>8σ) | proved: the leading-order spectrum fits neither release, for any `T_b/M₅` |
| (50) `H/2π ≲ T_b ≃ 0.17 M₅` | `eq50` | proved: `H ≤ 2πT_b` (a hypothesis) and `T_b/M₅ ≤ 0.1723` give `H < 1.09 M₅` |
| (51) `H ≲ M₅` | `eq50` | proved (see (50)) |
| (51) `M₅³ ≤ H₀M₄²/6` | `eq51`; `ObsData.eq51` for a general `r_c H₀` bound; `M5_cube_le` in terms of `G_N` | proved |
| (51) `M₅ ≲ 9 MeV` | `eq51_numeric`; `hubble_le` (`H ≤ 9.81 MeV`) | proved, assuming `H₀ ≤ 1.47×10⁻⁴² GeV` and `G_N ≥ 6.708×10⁻³⁹ GeV⁻²` |
| (52) `T ≪ T_GUT` (no monopoles) | `radiation_T4`, `eq52`, `eq52_below_GUT` | proved: `T ≤ 8.5×10⁷ GeV` for `g_* ≥ 100`, so `T ≤ 10⁻⁷ T_GUT` for `T_GUT ≥ 10¹⁵ GeV`. The radiation-era Friedmann equation is a hypothesis. Eq. (52) as printed has a dimension error (see below) |
| Atmosphere temperature `T_b ≤ 1.56 MeV` (not in the paper) | `Tb_le`, `Tb_le_planck2013`, `Tb_le_planck2018` | proved |
| Acceleration equation `ä/a = -(4πG_N/3)(ρ + ρ̃ + 3(P + P̃))` | `accel_of_friedmann`, `BraneCosmology.accelAt_of_ne`, `acceleration` | **derived** from (11)–(13) wherever `H ≠ 0`; not implied at `H = 0` (`static_not_accelAt`) |
| `ä` exists wherever `H ≠ 0` | `differentiableAt_deriv_of_sq_eq`, `BraneCosmology.deriv_a_differentiableAt` | proved (Darboux); the structure assumes only one derivative |
| Non-vacuity of the assumptions | `BraneCosmology.nonempty`, `static`, `deSitter` | proved: instances exist for every coupling |
| Self-accelerating vacuum, `H² + 𝒦/a² = 1/r_c²` | `BraneCosmology.deSitter`, `deSitter_H`, `deSitter_selfAccelerating`, `deSitter_pressure`, `deSitter_accelAt` | proved |
| An expanding solution with `r_h > 0` and radiation | `exists_expanding_radiation`, `BraneCosmology.radiationBounce`, `radiationBounce_accelAt`, `radiationBounce_pressure` | proved, in closed form, for `ρ = ρ_BH` and `2r_h ≤ r_c`: `a² = 𝒦r_c²/2 + q cosh(2t/r_c)`, self-accelerating branch, `ε = -1` |
| `ε = -1` on the normal branch with `r_h > 0`, `ρ > 0` | `BraneCosmology.exists_normal_branch_eps_neg`, `BraneCosmology.not_isSolution_normal_eps_neg`, `not_isSolution_minus_branch` | a **static** witness exists, but it is not a solution. **No solution** exists for matter with `ρ + 3P > 0` and `3P ≤ ρ`: `P̃ ≥ 0` by Eq. (16), so `ä < 0` at every time, and `a` cannot stay positive for all time |
| Reduction to `ȧ² = F(a)` for `P = wρ` | `BraneCosmology.rho_barotropic`, `branch_fixed`, `reduction` | proved: away from the singularity the branch is fixed for all time |
| Solutions of the equations of motion | `BraneCosmology.IsSolution`, `isSolution_of_ne`, `static_not_isSolution`, `deSitter_isSolution`, `radiationBounce_isSolution` | defined; automatic wherever `H ≠ 0` |
| Local existence and uniqueness for `ȧ = ±√F(a)` | `exists_local_solution`, `local_unique`, `BraneCosmology.locally_determined` | proved away from `H = 0` and the singularity |
| Acceleration equation as `ä = F'(a)/2` | `hasDerivAt_friedmannF`, `BraneCosmology.accel_eq_deriv` | proved for solutions with `P = wρ`, away from the singularity, `H = 0` included |
| Local existence and uniqueness through turning points | `exists_local_solution₂`, `local_unique₂`, `BraneCosmology.locally_determined₂`, `equilibrium_of_rest`, `radiationBounce_determined` | proved away from the singularity |
| Maximal (global) solutions | `exists_isMaximalSolution`, `IsMaximalSolution.unique`, `IsMaximalSolution.eventually_not_mem_right`, `exists_maximal_history`, `BraneCosmology.maximal_eq` | proved: maximal solutions exist and are unique; at a finite end `a` leaves every compact subset of `{a > 0}` minus the singularity; a solution that never reaches the singularity is global |
| A `BraneCosmology` from a global solution | `hasDerivAt_rhoTildeX`, `junction_sq`, `BraneCosmology.ofSolution`, `ofSolution_isSolution`, `BraneCosmology.exists_of_maximal` | proved: a maximal solution on all of `ℝ`, with `ε ρ̃ ≤ 0`, is a `BraneCosmology` and a solution of the equations of motion |

## Issues the formalization surfaced

Issues 1–3 were checked against the TeX source of arXiv:1309.1487v2 (ROADMAP M3.1).

[`docs/NOTE.md`](docs/NOTE.md) collects these issues in a short note, ordered by their effect
on the paper's conclusions (ROADMAP M3.5).

1. **Typo in Eq. (24).** The square root contains `ȧ/√𝒦` in the source as well. Eq. (21) and
   the denominator of Eq. (25) both require `ȧ²/𝒦`. The corrected form is used here. Also,
   Eq. (24) matches Eq. (26) only if `Ω_ij` is read as the induced spatial metric
   `(a²/𝒦)Ω_ij`, i.e. `K^i_j = ε X δ^i_j`. That is the reading `BraneCosmology.junction` uses.
2. **Eq. (27) is wrong as printed for `ε = +1`.** The induced pressure follows from
   conservation alone (`pressure_of_continuity`), and also from the timelike junction condition
   (25) for either orientation (`pressure_of_timelike_junction`). Both give Eq. (16). Eq. (27)
   is what Eq. (25) gives after substituting `X = +(8πG_b/3)ρ̃`, which is the junction
   condition for `ε = -1` only (`eq27_of_dropped_sign`). For `ε = +1`, Eq. (27) disagrees with
   Eq. (16) (`eq27_one_ne`).
3. **The paper's `ε = -1` is too strong. Resolved: no tension on the normal branch.** The paper
   infers `ε = -1` by comparing Eq. (27) with Eq. (16). By issue 2 that comparison is circular.
   The spatial junction condition fixes `ε` by the sign of `ρ̃` instead (`orientation_iff`):
   - the self-accelerating branch needs `ε = -1` (`orientation_plus_branch`);
   - the normal branch needs `ε = -1` when `ρ_BH > ρ` and `ε = +1` when `ρ_BH < ρ`
     (`orientation_minus_branch`).

   So the normal-branch region `ρ_BH < ρ`, including Eq. (34), is consistent with `ε = +1`. The
   earlier "tension" (`normal_branch_requires`) came from assuming the paper's `ε = -1`. With no
   black hole, the standard DGP normal branch needs `ε = +1` (`minkowski_normal_branch`), so
   `ε = -1` cannot be right in general. One consequence remains: `ε` is constant, so a
   normal-branch history cannot have `ρ_BH > ρ` at one time and `ρ_BH < ρ` at another
   (`BraneCosmology.normal_branch_no_crossing`). `ρ̃ = 0` only happens on or inside the horizon
   (`rhoTilde_eq_zero_inside`). Issue 6 follows from this.
4. **`BraneCosmology` has no acceleration equation, and admits non-solutions.** The structure
   holds the Friedmann and continuity equations only. Wherever `H ≠ 0` these imply the
   acceleration equation (`BraneCosmology.accelAt_of_ne`), and also that `ä` exists. At `H = 0`
   they do not: a static brane satisfies every field with *any* pressure, and the static
   instances provably violate the acceleration equation (`static_not_accelAt`). They show the
   fields are consistent, but they are not solutions of the equations of motion. The same gap
   leaves `P̃` free at `H = 0`, because Eq. (16) is also derived only for `H ≠ 0`. See ROADMAP
   M2.4. The predicate `BraneCosmology.IsSolution` (M2.5) adds the acceleration equation and
   Eq. (16) at every time. It holds automatically wherever `H ≠ 0` (`isSolution_of_ne`), and
   it excludes the static instances (`static_not_isSolution`). `BraneCosmology.radiationBounce`
   is a solution, with `r_h > 0` and radiation (`radiationBounce_isSolution`). The structure
   also needs `ρ̃` to be differentiable at every time. At the pressure singularity this forces
   `H = 0` when `3P ≤ ρ` (`BraneCosmology.singularity_at_rest_of_le`). The paper's white-hole
   history starts at the singularity with `H ≠ 0`, so a `BraneCosmology` cannot contain that
   start.
5. **Eq. (52) has a dimension error.** As printed, `T ∼ (M₄H/g_*²)^{1/4}` has dimension
   `GeV^{1/2}`. The radiation-era Friedmann equation gives `T = (180/π²)^{1/4}(M₄H)^{1/2}g_*^{-1/4}`
   (`radiation_T4`), and the paper's number `3×10⁴ TeV` matches this form up to the `O(1)`
   factor. The conclusion `T ≪ T_GUT` holds with a large margin (`eq52_below_GUT`).

6. **The paper's white-hole history needs the orientation to change (ROADMAP M3.2).** That
   history starts at the pressure singularity in the radiation era and ends today with
   `ρ_BH ≪ ρ`. The singularity needs `ε = -1` (`eps_of_singularity`). Today's normal branch with
   `ρ_BH < ρ` needs `ε = +1`. With a fixed `ε = -1`, the normal branch keeps `ρ ≤ ρ_BH`, and a
   matter era can then grow `a` by at most the factor `(ρ_BH/ρ)` at its start
   (`matter_era_growth_le`). With the paper's own bound (32), `|ρ̃| ≤ 0.1 ρ`, that factor is at
   most 1.1 (`matter_era_growth_le_small`). The real matter era grows `a` by about `10³`. So
   `ε` must change from `-1` to `+1` along the history. If `ε` may depend on time, it can change
   only where `ρ̃ = 0`, and there the brane is on or inside the horizon (`sign_change_inside`).
   The paper puts the horizon exit at `a ∼ 0.01–1`, so the crossing `ρ_BH = ρ` must happen
   before that. The paper's black-hole history stays outside the horizon after it emerges, so
   it keeps one orientation (`sign_const_outside`). Whether an orientation change is
   geometrically allowed is open. `BraneCosmology` fixes `ε`, so it cannot describe the
   white-hole history.

7. **The pressure singularity is not always inside the horizon.** Sec. 5 says the
   singularity "always" happens inside a white-hole horizon. At `ρ̃ = ρ̃_s` the junction
   condition gives `(𝒦/a²) f(a) = 1/(2r_c)² - H²`. So the brane is on or inside the horizon
   exactly when `|H| ≥ 1/(2r_c)` (`BraneCosmology.singularity_inside_iff`). Equivalently, the
   curvature term `𝒦/a²` is at most `(8πG_N/3)(ρ + ρ̃_s/2)`
   (`singularity_inside_iff_curvature`). The condition holds at early times, where `H r_c ≫ 1`
   (`singularity_inside_of_rc`), so the paper's scenarios are not affected. But the claim is a
   consequence of the singularity happening early, not a property of the singularity itself. The
   result does not depend on the Schwarzschild form of `f`: it holds for every blackening
   factor (`BulkCosmology.singularity_inside_iff`).

## Soundness

`Audit.lean` runs on every build. It fails if any declaration in the library depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`, which also catches `sorry`.

## Roadmap

- [`docs/ROADMAP.md`](docs/ROADMAP.md): the Lean side. Closes the numerical gaps in Sec. 4,
  proves that a `BraneCosmology` exists, resolves the surfaced issues, covers dynamics, a
  general bulk, geometry from first principles, and an interface for stating predictions.
- [`docs/NOTE.md`](docs/NOTE.md): a short note on the issues above, for readers of the paper.
- [`docs/TESTABILITY.md`](docs/TESTABILITY.md): the physics side. Lists the candidate
  observational tests with a verdict on each, decision gates, and a template for building each
  test into a pathway. Note: the paper's simple model predicts `n_s = 1` and is ruled out by its
  own Sec. 5 (proved as `leading_order_ruled_out_planck2018`), so any testable version needs an
  extension that produces a red tilt.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

[`docs/TOOLING.md`](docs/TOOLING.md) has the full setup: how to install elan and Lean, the
Python environment in `phenomenology/` (CAMB, CLASS, Cobaya), and PolyChord.

Each module imports only the Mathlib files it needs, not all of `Mathlib`, so loading stays
fast on slow disks.
