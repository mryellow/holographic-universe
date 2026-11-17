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
| `Bulk.lean` | 5D Schwarzschild `f(r)` (20); brane radius; `ρ_BH` (28); `μ` (29); horizon crossing |
| `InducedFluid.lean` | Friedmann + junction ⇒ quadratic; branches (26); reality (30); sign of `ρ̃` |
| `Pressure.lean` | Eq. (16) derived from continuity (12)–(13); Eq. (27) vs (16) |
| `Constraints.lean` | Observational bounds (33), (34), (35) |
| `Integrals.lean` | `∫ dx/(1+x²)² = π/2` over the real line, used in Eq. (48) |
| `Zeta.lean` | `ζ(5)` as a real series, identified with `riemannZeta 5`; `1.0369 ≤ ζ(5) ≤ 1.0370` |
| `Perturbations.lean` | Eq. (48) algebra; inversion for `T_b/M₅` (49); `M₅` bound (51) |
| `ObsData.lean` | Observational data as parameters (`ObsData`); Planck 2013 and Planck 2018 instances; Eqs. (49), (51) per release |
| `Monopoles.lean` | Temperature bound (50); `M₅ ≲ 9 MeV` and `T_b ≲ 1.56 MeV` (52); `T_b ≪ T_GUT` |
| `Model.lean` | `BraneCosmology` structure and the results instantiated on it |
| `Acceleration.lean` | Acceleration equation derived from Friedmann + continuity where `H ≠ 0`; existence of `ä` |
| `Instances.lean` | Non-vacuity: explicit `BraneCosmology` instances (static family, self-accelerating de Sitter vacuum) |
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
| (20), horizon crossing `r = r_h` | `outside_horizon_iff`, `curv_mul_blacken` | proved |
| (24) `K_ij` | `BraneCosmology.junction` | **assumed** (with a typo corrected, see below) |
| (26) branches `ρ̃_±` | `isInduced_of_junction`, `isInduced_iff`, `BraneCosmology.branches` | **derived** |
| (27) at `ε = -1` equals (16) | `eq27_neg_one` (and `eq27_one_ne` for `ε = +1`) | proved |
| (28) `ρ_BH ∝ a⁻⁴` | `rhoBH_scaling` | proved |
| (30) reality constraint | `reality`, `BraneCosmology.reality` | **derived** |
| (32) `|ρ̃| ≤ ερ` | hypothesis | **assumed** (observational input) |
| (33) + side remarks | `eq33`, `eq33_side` | proved |
| (34) | `eq34` | proved |
| (35) | `eq35` | proved, with fewer hypotheses than stated: the branch assumption is redundant, and positivity of the denominator follows |
| (39)–(47) thermal correlators, `M(0) = 15ζ(5)/π²` | — | **assumed** (out of Mathlib's reach) |
| (48) `∫dx/(1+x²)² = π/2` | `integral_univ_inv_one_add_sq_sq` | proved |
| (48) `= 25ζ(5)/(3072π⁴)(T_b/M₅)⁶` | `eq48_leading` | proved, assuming `M(0)` |
| `ζ(5) ∈ [1.0369, 1.0370]` (enters the coefficient of (48)) | `zeta5_bounds`, `riemannZeta_five_bounds`; sharper `zeta5_upper : ζ(5) ≤ 1.03694` | proved |
| (48) coefficient `25ζ(5)/(3072π⁴) ∈ [8.65, 8.67]×10⁻⁵` | `ampCoeff_bounds`; sharper `ampCoeff_sharp : [8.6627, 8.6631]×10⁻⁵` | proved |
| (49) `T_b/M₅ ≈ 0.171` | `eq49`, `eq48_eq49` | proved: `[0.1705, 0.1723]` from the Planck 2013 amplitude, with no numerical hypotheses (`eq49_of_coeff` is the version for a general coefficient) |
| (49) for any data release | `ObsData.tbm5_bounds`, `amplitude_inversion` | proved |
| (49), Planck 2013, sharp | `eq49_planck2013_sharp` | proved: `[0.17061, 0.17216]`, the paper's `0.17139 ± 0.00077` |
| (49), Planck 2018 | `eq49_planck2018` | proved: `[0.1697, 0.17051]`, i.e. `0.1701 ± 0.0004`. Disjoint from the 2013 interval (`planck2013_planck2018_disjoint`) |
| (50) `H/2π ≲ T_b ≃ 0.17 M₅` | `eq50` | proved: `H ≤ 2πT_b` (a hypothesis) and `T_b/M₅ ≤ 0.1723` give `H < 1.09 M₅` |
| (51) `M₅³ ≤ H₀M₄²/6` | `eq51`; `ObsData.eq51` for a general `r_c H₀` bound; `M5_cube_le` in terms of `G_N` | proved |
| (52) `M₅ ≲ 9 MeV` | `eq52` | proved, assuming `H₀ ≤ 1.47×10⁻⁴² GeV` and `G_N ≥ 6.708×10⁻³⁹ GeV⁻²` |
| (52) `T_b ≪ T_GUT` (no monopoles) | `eq52_temperature`, `eq52_planck2013`, `eq52_planck2018`, `eq52_below_GUT` | proved: `T_b ≤ 1.56 MeV`, so `T_b ≤ 1.6×10⁻¹⁸ T_GUT` for `T_GUT ≥ 10¹⁵ GeV`. That `T_b` is the highest brane temperature is **assumed** |
| Acceleration equation `ä/a = -(4πG_N/3)(ρ + ρ̃ + 3(P + P̃))` | `accel_of_friedmann`, `BraneCosmology.accelAt_of_ne`, `acceleration` | **derived** from (11)–(13) wherever `H ≠ 0`; not implied at `H = 0` (`static_not_accelAt`) |
| `ä` exists wherever `H ≠ 0` | `differentiableAt_deriv_of_sq_eq`, `BraneCosmology.deriv_a_differentiableAt` | proved (Darboux); the structure assumes only one derivative |
| Non-vacuity of the assumptions | `BraneCosmology.nonempty`, `static`, `deSitter` | proved: instances exist for every coupling |
| Self-accelerating vacuum, `H² + 𝒦/a² = 1/r_c²` | `BraneCosmology.deSitter`, `deSitter_H`, `deSitter_selfAccelerating`, `deSitter_pressure`, `deSitter_accelAt` | proved |
| `ε = -1` on the normal branch with `r_h > 0`, `ρ > 0` | `BraneCosmology.exists_normal_branch_eps_neg` | proved for a **static** witness only |

## Issues the formalization surfaced

1. **Typo in Eq. (24).** The square root as printed contains `ȧ/√𝒦`. Eq. (21) and the
   denominator of Eq. (25) both require `ȧ²/𝒦`. The corrected form is used here.
2. **Eq. (16) does not depend on `ε`.** The induced pressure follows from conservation alone
   (`pressure_of_continuity`). So Eq. (27) can only be correct for `ε = -1`. For `ε = +1` it
   disagrees with Eq. (16) (`eq27_one_ne`).
3. **Sign tension on the normal branch.** With `ε = -1`, the spatial junction condition forces
   `ρ̃ ≥ 0` (`rhoTilde_nonneg_of_eps_neg`). But `ρ̃_- < 0` exactly when `ρ_BH < ρ`
   (`rhoTilde_minus_neg_iff`). So the part of the normal-branch region with `ρ_BH < ρ`,
   including the region of Eq. (34), is inconsistent with `ε = -1` (`normal_branch_requires`).
   The paper's Fig. 3 uses `ρ_BH = 1.05ρ` and is not affected. This may be a sign-convention
   issue rather than an error, and it should be checked against the TeX source.
4. **`BraneCosmology` has no acceleration equation, and admits non-solutions.** The structure
   holds the Friedmann and continuity equations only. Wherever `H ≠ 0` these imply the
   acceleration equation (`BraneCosmology.accelAt_of_ne`), and also that `ä` exists. At `H = 0`
   they do not: a static brane satisfies every field with *any* pressure, and the static
   instances provably violate the acceleration equation (`static_not_accelAt`). They show the
   fields are consistent, but they are not solutions of the equations of motion. The same gap
   leaves `P̃` free at `H = 0`, because Eq. (16) is also derived only for `H ≠ 0`. See ROADMAP
   M2.4.

## Soundness

`Audit.lean` runs on every build. It fails if any declaration in the library depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`, which also catches `sorry`.

## Roadmap

- [`docs/ROADMAP.md`](docs/ROADMAP.md): the Lean side. Closes the numerical gaps in Sec. 4,
  proves that a `BraneCosmology` exists, resolves the surfaced issues, covers dynamics, a
  general bulk, geometry from first principles, and an interface for stating predictions.
- [`docs/TESTABILITY.md`](docs/TESTABILITY.md): the physics side. Lists the candidate
  observational tests with a verdict on each, decision gates, and a template for building each
  test into a pathway. Note: the paper's simple model predicts `n_s = 1` and is ruled out by its
  own Sec. 5, so any testable version needs an extension that produces a red tilt.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

[`docs/TOOLING.md`](docs/TOOLING.md) has the full setup: how to install elan and Lean, the
Python environment in `phenomenology/` (CAMB, CLASS, Cobaya), and PolyChord.

Each module imports only the Mathlib files it needs, not all of `Mathlib`, so loading stays
fast on slow disks.
