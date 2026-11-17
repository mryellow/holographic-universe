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

Issue 4 is a limitation of the formal model, not of the paper. It is described in section 5.

Section 6 has the main physics result. The paper's spectrum is blue at every scale, so the
observed red tilt has to come from an extension. Neither of the two extensions that the paper
proposes gives it, and no local extension of its mechanism fits the tilt and its running
together.

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
black-hole history. Inside the horizon the brane is never at rest. A brane that expands inside
the horizon was inside and expanding at every earlier time (`BraneCosmology.white_hole_past`),
and its first time on the horizon is unique (`BraneCosmology.exists_unique_exit`). So before the
exit the white-hole history is one expanding phase inside the horizon. These proofs use only
the reality condition (22) on the brane's 4-velocity, not the orientation `ε`.

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
consistent. They are not solutions of the equations of motion. `BraneCosmology.radiationBounce`
is a solution: it has a bulk black hole and radiation, and obeys the acceleration equation at
every time (`radiationBounce_accelAt`). It needs the tuning `ρ = ρ_BH`. The predicate
`BraneCosmology.IsSolution` adds the acceleration equation and Eq. (16) as hypotheses. It
excludes the static instances (`static_not_isSolution`). General solutions are the subject of
ROADMAP Milestone 4. For a solution with `P = wρ`, the acceleration equation is
`ä = F'(a)/2`, where `ȧ² = F(a)` is the Friedmann equation (`BraneCosmology.accel_eq_deriv`).
So away from the singularity, `a` and `ȧ` at one time fix a solution locally, also at `H = 0`
(`BraneCosmology.locally_determined₂`). They also fix it globally: a solution that never
reaches the singularity is the maximal solution of its data (`BraneCosmology.maximal_eq`). A
maximal solution that ends in finite time ends at `a → 0`, at the singularity, or at
`a → ∞` (`exists_maximal_history`). Conversely, a global solution with a fixed orientation
defines an instance (`BraneCosmology.exists_of_maximal`).

The structure needs `a` at every time. This excludes the paper's orientation on the normal
branch. With `ε = −1` and `ρ̃ < ρ̃_s`, Eq. (16) gives `P̃ ≥ 0`. For matter with `ρ + 3P > 0`
and `P ≤ ρ/3`, the acceleration equation then gives `ä < 0` at every time. So no solution
exists for all time (`BraneCosmology.not_isSolution_normal_eps_neg`). This is the brane form of
the closed-universe result of general relativity. It is not an issue with the paper, whose
history starts at the singularity.

The structure also needs `ρ̃` to be differentiable at every time. At the pressure singularity,
`(ρ̃ − ρ̃_s)² = ρ̃_s² − 2ρ̃_s(ρ_BH − ρ)` then has derivative zero, which gives
`H (3P − ρ − 2ρ̃_s) = 0` (`BraneCosmology.singularity_at_rest`). For `3P ≤ ρ`, the brane is at
rest at the singularity and strictly outside the horizon (`singularity_outside_of_le`). So the
singularity of the paper, with `H ≠ 0` inside the horizon, is not a time of any
`BraneCosmology`. This agrees with the paper, where the singularity is the start of the
history. Near it `P̃ → +∞` (`tendsto_pressureTilde_atTop`).

At late times the formal model gives the expected limits (ROADMAP M4.4). On the
self-accelerating branch, an expanding history with `a² > 2𝒦r_c²` approaches de Sitter space
with `H → 1/r_c` (`BraneCosmology.tendsto_deSitter`). On the normal branch,
`|ρ̃| ≤ √(2ρ̃_s|ρ − ρ_BH|)`, so the Friedmann equation is standard up to a relative error
`√(2ρ̃_s/ρ)` (`BraneCosmology.normal_branch_frw_of_le`).

## What the formalization confirms

The main derivations of the paper hold as stated, under the hypotheses above:

- the branches (26), the reality bound (30) and the induced pressure (16), from (11)–(13) and
  the junction condition;
- the observational bounds (33)–(35);
- the value `M(0) = 15ζ(5)/π² ≈ 1.576` of Eq. (46), from the integral with the vacuum term
  dropped (`thermalM_zero`);
- the amplitude inversion (49), from the Planck 2013 amplitude;
- the bounds (50)–(51), and `T ≪ T_GUT` in (52).

Sec. 5 says that an AdS bulk adds "a small constant" and "need not significantly change" the
results. The formalization confirms the form of the change. The bulk density becomes
`ρ_BH − ρ_Λ`, with `ρ_Λ = 3/(8πG_N L²)` (`rhoBulk_blackenAdS`), and Eq. (16) changes by
`3P − ρ → 3P − ρ − 4ρ_Λ` (`BulkCosmology.pressure_AdS`). The constant is negative. On the
normal branch it gives a negative late-time `ρ̃`, so without a brane tension no history with
`ρ → 0` expands forever (`BulkCosmology.not_tendsto_atTop_normal_AdS`). The paper notes in
Sec. 1 that the normal branch needs a brane tension to fit the data. That tension would also
have to cancel this term.

The leading-order spectrum of Eq. (48) has `n_s = 1` exactly (`leadingSpectrum_ns`). Sec. 5
says that this simple model is ruled out at more than 5σ. The formalization proves that this
spectrum fits neither the Planck 2013 nor the Planck 2018 data
(`leading_order_ruled_out_planck2013`, `leading_order_ruled_out_planck2018`).

The next order in `κ = k/(a_bT_b)` does not help. `M(κ)` splits into a part with its minimum at
`κ = 0` and a part with its maximum there (`thermalM_eq`, `thermalA_zero_le`,
`thermalB_le_zero`). So the sign needs a computation. The formalization proves
`M(κ) = M(0) + (10ζ(5) − ζ(3))/(32π²)·κ² + o(κ²)`, with a positive coefficient
(`hasDerivAt_deriv_mRay`, `secondOrderCoeff_pos`). The tilt is blue, `n_s − 1 ≈ 0.037κ²`, and no
spectrum of this form fits `n_s < 1` with the pivot at small `κ` (`ObsData.not_fits_next_order`).
The restriction to small `κ` can be dropped. `M′(κ) > 0` for every `κ > 0`, because the part
that pulls `M` down changes at no more than half the rate of the part that pushes it up
(`b1_add_a1_pos`, `strictMonoOn_mRay`). So `n_s > 1` at every scale
(`spectralIndex_thermal_gt_one`), and no spectrum `C·M(k/s)` fits `n_s < 1`, wherever the pivot
is (`ObsData.not_fits_thermal`). A red tilt must come from outside the simple model. Section 6
tests the two extensions that the paper suggests, and then every local extension.

## 6. The red tilt: no extension within the paper's mechanism works

Sec. 5 of the paper proposes two ways to turn the scale-invariant spectrum red: a residual Jeans
instability of the bulk atmosphere, and cascading gravity. The repository works out both at
linear order (`phenomenology/p1_jeans/`, `phenomenology/p2_cascade/`), and then the whole class
of local extensions. None gives the observed spectrum. The tilt results, in order:

| | Spectrum | Result | Status |
|---|---|---|---|
| 1 | leading order, `C·M(0)` | `n_s = 1`, fits no release with `n_s < 1` | proved (`leading_order_ruled_out_planck2018`) |
| 2 | next order, small `κ` | `n_s − 1 ≈ 0.037κ² > 0` | proved (`ObsData.not_fits_next_order`) |
| 3 | full thermal spectrum `C·M(k/s)` | `n_s > 1` at every scale | proved (`ObsData.not_fits_thermal`) |
| 4 | `C·M(k/s)·G(k/s′)`, `G` nondecreasing | `n_s > 1` at every scale | proved (`ObsData.not_fits_thermal_mul`) |
| P2 | cascading gravity, linear | an instance of 4, for every `M₆` | proved, given the linear cascade factor (`ObsData.not_fits_cascade`) |
| P1 | Jeans instability, linear | red, but `α_s = (1 + 1/(1 − y²))(n_s − 1)`, ~9σ from Planck; or a tuned dip | unprojected spectrum proved (`planck2018Running_not_fits_jeans`); on the brane, `n_s = 1` above `k_J` and the tilt budget `2 ln cosh τ` proved; the window itself is numerical (`jeans_tilt.py`) |
| P4 | any local extension: tilt `Σᵢ cᵢ(k/sᵢ)^{pᵢ}`, `pᵢ ≥ 2` red | `α_s ≤ 2(n_s − 1) ≤ −0.063` | proved, given the form of the tilt (`planck2018Running_not_fits_local`) |

**Cascading gravity has the wrong sign.** The paper reads the red tilt as a bulk propagator that
"is getting stronger in the IR", and expects the extra polarization of cascading gravity to
supply this. The extra polarization is a scalar that couples to the trace of the stress tensor.
It strengthens the Newtonian potential `g₀₀` (`newtonCoeff_third_le_quarter`). But the paper
identifies `ζ` with the spatial potential (Eq. 47), and the scalar lowers that for every gas
with `ρ ≥ 4p` (`spatialCoeff_quarter_le_third`). For the paper's radiation atmosphere it does
nothing (`spatialCoeff_radiation`). The 6D propagator `1/(K² + mK)` also weakens gravity in the
infrared. So the cascade multiplies the spectrum by a factor that does not decrease with `k`
(`cascadeG_monotoneOn`), and the spectrum stays blue (`ObsData.not_fits_cascade`).

**The Jeans instability has the wrong shape.** For the unprojected growth `e^{2τ√(1 − y²)}`,
`y = k/k_J`, the tilt is red below the Jeans scale, but the running is exactly
`α_s = (1 + 1/(1 − y²))(n_s − 1)` (`runningIndex_jeans`), at least twice the tilt
(`runningIndex_jeans_le`). Above the Jeans scale `n_s = 1` (`spectralIndex_jeans_above`). So no
such spectrum fits Planck 2018 with running (`planck2018Running_not_fits_jeans`). After the
projection onto the brane (numerical, `jeans_tilt.py`), a pivot well inside the unstable range
gives `α_s ≈ 2(n_s − 1) ≈ −0.065`, about 9σ from Planck 2018. A narrow window just below the
Jeans scale fits `n_s` and `α_s` at the pivot. But it needs `k_J` tuned to within 10%, it leaves
`n_s = 1` exactly for `k ≥ k_J`, and it misses the slope across `0.008–0.1 Mpc⁻¹` by `≥ 5σ`.
The miss has an exact reason. On the brane, the total tilt over all scales is
`∫(n_s − 1) d ln k = −2 ln cosh τ` (proved, `tendsto_integral_spectralIndex_jeansBrane`). The
window has `τ ≤ 0.188` (numerical), so a budget of about `0.035`, and the slope Planck sees
across that range needs about `0.09`. The numerical results assume linear growth and a static
background. A full Planck likelihood run would make them final.

**No local extension works.** The paper imprints every mode at one moment, the static
equilibrium `(a_b, T_b)` of Sec. 4. So a cooling atmosphere changes only the amplitude. Within
that mechanism, an extension changes the shape through physics with some scale `s`. If that
physics is local, the spectrum is analytic in `k²`, and near the pivot the tilt is
`Σᵢ cᵢ(k/sᵢ)^{pᵢ}` with `pᵢ = 2, 4, …`. Each term contributes `pᵢ` times its own tilt to the
running (`runningIndex_of_tilt`). With red terms of power `≥ q` and blue terms of power `≤ q`,
`α_s ≤ q(n_s − 1)` (`runningIndex_le_of_tilt`). Planck 2018 with running excludes every
`q ≥ 0.36` (`planck2018Running_not_fits_tilt`). For local physics, `q = 2`, a fit to `n_s` would
force `α_s ≤ −0.063` (`runningIndex_le_local_planck2018`), against the measured
`−0.0045 ± 0.0067`. P1 and P2 are both in this class. The theorem does not cover a red `k²` term
cancelled by a blue `k⁴` term at the pivot. That is a feature tuned to the pivot, like P1's
window.

**What any rescue needs.** If `C·M(k/s)·G(k/s′)` fits a release, then at the pivot
`d ln G/d ln k < n_s,hi − 1` (`ObsData.Fits.factor_slope_lt`). For Planck 2018 that is
`< −0.0309` (`planck2018_factor_slope`), so `G′ < 0` at the pivot
(`ObsData.Fits.deriv_factor_neg`). The thermal factor adds a blue tilt of its own, so `G` must
carry more than the whole observed tilt. With the running bound, that red part must also be
nearly scale free: a power `p < 0.36` in `k`. For a smooth step `G = exp(B/(1 + (k/k_V)^q))`, the tilt is at most
`|B|q/4` (`abs_boostTilt_le`), and `α_s/(n_s − 1) = q(1 − u)/(1 + u)` with `u = (k/k_V)^q`
(`runningIndex_boost`). So the pivot must sit near the centre of a broad, large step.

**Conclusion.** In the form the paper gives, the model does not produce the observed spectrum,
with either of its proposed extensions or with any other local extension of its mechanism. This
is the outcome that `docs/TESTABILITY.md` (gate G1) names as a legitimate result. Two routes
remain, and both are new models rather than extensions of this paper: modes imprinted at
different times (for example at horizon exit), which replaces the single static equilibrium;
and scale-free, long-range correlations in the atmosphere (an anomalous dimension `≈ 0.035`),
which local physics does not give.
