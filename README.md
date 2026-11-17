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
| `Perturbations.lean` | Eq. (48) algebra; inversion for `T_b/M₅` (49); `M₅` bound (51) |
| `Model.lean` | `BraneCosmology` structure and the results instantiated on it |

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
| (48) `= 25ζ(5)/(3072π⁴)(T_b/M₅)⁶` | `eq48_leading` | proved, assuming `M(0)` and `∫dx/(1+x²)² = π/2` |
| (49) `T_b/M₅ ≈ 0.171` | `eq49` | proved: `[0.1705, 0.1723]` from the Planck amplitude |
| (51) `M₅³ ≤ H₀M₄²/6` | `eq51` | proved |

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
# elan is installed in ~/.elan; add it to PATH if needed:
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

Each module imports only the Mathlib files it needs, not all of `Mathlib`, so loading stays
fast on slow disks.
