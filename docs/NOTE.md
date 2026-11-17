# Notes on arXiv:1309.1487 from a Lean 4 formalization

This note collects the issues that the formalization in this repository found in

> R. Pourhasan, N. Afshordi, R. B. Mann, *Out of the White Hole: A Holographic Origin for the
> Big Bang*, [arXiv:1309.1487](https://arxiv.org/abs/1309.1487) (v2), JCAP 04 (2014) 005.

Equation and section numbers refer to v2. Each claim below names the Lean theorem that proves
it. The README has the full equation map. Its issues 1–7 are the source of this note, and the
numbers below are the README numbers.

## Method

The paper's assumptions are explicit hypotheses in Lean, not axioms. Most of them are fields of
the structure `BraneCosmology` (`HolographicUniverse/Model.lean`):

- the Friedmann equation (11) and the continuity equations (12)–(13);
- the spatial junction condition, Eqs. (10) and (24): `ε √(H² + 𝒦/a² − 𝒦²r_h²/a⁴) = −(8πG_b/3) ρ̃`,
  with a constant orientation `ε = ±1` of the brane normal.

The extrinsic-curvature computation and the thermal correlators of Sec. 4 are outside what
Mathlib can express. They enter as hypotheses. `HolographicUniverse/Audit.lean` runs on every
build and fails if any declaration uses an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. To check every statement below, run `lake build`.

## Summary

| # | Issue | Effect on the paper's conclusions |
|---|---|---|
| 6 | The white-hole history needs the orientation `ε` to change from `−1` to `+1` | Open. The history as described is not a solution of the model with a fixed `ε` |
| 3 | The choice `ε = −1` is inferred circularly, and is wrong on part of the normal branch | Removes an apparent inconsistency in Eq. (34). Leads to issue 6 |
| 7 | The pressure singularity is inside the white-hole horizon only when `\|H\| ≥ 1/(2r_c)` | None for the paper's scenarios. The word "always" in Sec. 5 is too strong |
| 2 | Eq. (27) holds for `ε = −1` only | None. Eq. (16) is correct for both orientations |
| 1 | Typo in Eq. (24): `ȧ/√𝒦` must be `ȧ²/𝒦` | None |
| 5 | Eq. (52) has a dimension error | None. The bound `T ≪ T_GUT` holds with a large margin |

Issue 4 is a limitation of the formal model, not of the paper. It is described at the end.

## 1. Orientation and the sign of the induced density (issues 2 and 3)

**Eq. (27) is the `ε = −1` case only.** The induced pressure `P̃` follows from the continuity
equation alone (`pressure_of_continuity`). It also follows from the timelike junction condition
(25) for either orientation (`pressure_of_timelike_junction`). Both routes give Eq. (16).
Eq. (27) is what Eq. (25) gives after the substitution `X = +(8πG_b/3) ρ̃`
(`eq27_of_dropped_sign`). That substitution is the junction condition for `ε = −1` only. For
`ε = +1`, Eq. (27) disagrees with Eq. (16) (`eq27_one_ne`).

**So the comparison of Eq. (27) with Eq. (16) cannot fix `ε`.** The paper uses this comparison
to choose `ε = −1`. By the result above, the comparison assumes `ε = −1`. The spatial junction
condition fixes `ε` from the sign of `ρ̃` instead (`orientation_iff`):

- `ε = −1` exactly when `ρ̃ > 0`, and `ε = +1` exactly when `ρ̃ < 0`;
- the self-accelerating branch `ρ̃_+` needs `ε = −1` (`orientation_plus_branch`);
- the normal branch `ρ̃_−` needs `ε = −1` when `ρ_BH > ρ`, and `ε = +1` when `ρ_BH < ρ`
  (`orientation_minus_branch`).

With `ε = −1` forced, the normal-branch region `ρ_BH < ρ` would be excluded
(`normal_branch_requires`). That region contains the paper's Eq. (34). With `ε = +1` it is
consistent. Without a black hole, the standard DGP normal branch also needs `ε = +1`
(`minkowski_normal_branch`). So `ε = −1` cannot hold in general.

**Consequence.** If `ε` is constant, a normal-branch history cannot have `ρ_BH > ρ` at one time
and `ρ_BH < ρ` at another (`BraneCosmology.normal_branch_no_crossing`).

## 2. The white-hole history needs an orientation change (issue 6)

The paper's white-hole history starts at the pressure singularity in the radiation era. It ends
today with `ρ_BH ≪ ρ`.

1. At the singularity, `ρ̃ = ρ̃_s > 0`, so `ε = −1` (`eps_of_singularity`).
2. Today the normal branch has `ρ_BH < ρ`, so `ε = +1` (section 1).
3. Suppose `ε = −1` for the whole history. Then the normal branch keeps `ρ ≤ ρ_BH`. In a
   matter era, `ρ_BH/ρ ∝ 1/a`, so the era can grow `a` by at most the factor `ρ_BH/ρ` at its
   start (`matter_era_growth_le`). With the paper's bound (32), `|ρ̃| ≤ 0.1 ρ`, this factor is
   at most 1.1 (`matter_era_growth_le_small`). The observed matter era grows `a` by about `10³`.

So `ε` must change from `−1` to `+1` along the history. Suppose `ε` is allowed to depend on time.
Then it can change sign only where `ρ̃ = 0`, and there the brane is on or inside the horizon
(`sign_change_inside`, `rhoTilde_eq_zero_inside`). The paper puts the exit from the horizon at
`a ∼ 0.01–1`. So the crossing `ρ_BH = ρ` must happen before that exit. A history that stays
outside the horizon keeps one orientation (`sign_const_outside`). This applies to the paper's
black-hole history.

**Open question.** Is a change of the normal orientation geometrically allowed for a brane
inside the white-hole horizon? The formal model fixes `ε`, so it cannot describe the
white-hole history in its current form.

## 3. The pressure singularity and the horizon (issue 7)

Three statements about the singularity `ρ̃ = ρ̃_s` hold exactly:

- It happens exactly when the reality bound (30) is saturated, `2(ρ_BH − ρ) = ρ̃_s`
  (`BraneCosmology.singularity_iff`, `isInduced_eq_rhoS_iff`).
- The two branches `ρ̃_±` meet only there (`branches_meet_iff`). So a history can change
  branch only through the singularity.
- In an expanding era with `P ≤ ρ/3` and `ρ_BH > ρ`, the reality bound gives a lower bound on
  `a`. Only the singularity reaches that bound (`BraneCosmology.scale_factor_floor`).

Sec. 5 says the singularity "always" happens inside a white-hole horizon. At `ρ̃ = ρ̃_s` the
junction condition gives

    (𝒦/a²) f(a) = 1/(2r_c)² − H².

So the brane is on or inside the horizon exactly when `|H| ≥ 1/(2r_c)`
(`BraneCosmology.singularity_inside_iff`). In terms of densities, the condition is
`𝒦/a² ≤ (8πG_N/3)(ρ + ρ̃_s/2)` (`singularity_inside_iff_curvature`). At early times `H r_c ≫ 1`,
so the condition holds (`singularity_inside_of_rc`). The paper's scenarios are therefore not
affected. But the property comes from the singularity happening early. It is not a property of
the singularity itself. The same condition holds for any static bulk
`ds² = -f dt² + dr²/f + r² dΩ₃²`, not only for Schwarzschild
(`BulkCosmology.singularity_inside_iff`).

## 4. Errata (issues 1 and 5)

**Eq. (24).** The TeX source has `ȧ/√𝒦` under the square root. Eq. (21) and the denominator
of Eq. (25) both need `ȧ²/𝒦`. Also, Eq. (24) agrees with Eq. (26) only if `Ω_ij` is read as the
induced spatial metric `(a²/𝒦) Ω_ij`, so that `K^i_j = ε X δ^i_j`. The formalization uses this
corrected form.

**Eq. (52).** As printed, `T ∼ (M₄H/g_*²)^{1/4}` has dimension `GeV^{1/2}`. The radiation-era
Friedmann equation gives `T = (180/π²)^{1/4} (M₄H)^{1/2} g_*^{−1/4}` (`radiation_T4`). The
paper's value `3×10⁴ TeV` matches this form up to an `O(1)` factor. With `g_* ≥ 100` and
`T_GUT ≥ 10¹⁵ GeV`, the result is `T ≤ 10⁻⁷ T_GUT` (`eq52_below_GUT`).

## 5. A limitation of the formal model (issue 4)

This is not an issue with the paper. `BraneCosmology` holds the Friedmann and continuity
equations, but not the acceleration equation. Where `H ≠ 0`, the fields imply the acceleration
equation and the existence of `ä` (`BraneCosmology.accelAt_of_ne`). At `H = 0` they do not. A
static brane satisfies every field with any pressure, and the static instances violate the
acceleration equation (`static_not_accelAt`). These instances show that the hypotheses are
consistent. They are not solutions of the equations of motion. Solutions are the subject of
ROADMAP Milestone 4.

## What the formalization confirms

The main derivations of the paper hold as stated, under the hypotheses above:

- the branches (26), the reality bound (30) and the induced pressure (16), from (11)–(13) and
  the junction condition;
- the observational bounds (33)–(35);
- the amplitude inversion (49), from the Planck 2013 amplitude;
- the bounds (50)–(51), and `T ≪ T_GUT` in (52).

The leading-order spectrum of Eq. (48) has `n_s = 1` exactly (`leadingSpectrum_ns`). Sec. 5
says that this simple model is ruled out at more than 5σ. The formalization proves that this
spectrum fits neither the Planck 2013 nor the Planck 2018 data
(`leading_order_ruled_out_planck2013`, `leading_order_ruled_out_planck2018`).
