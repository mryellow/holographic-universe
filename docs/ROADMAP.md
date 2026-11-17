# Formalization roadmap

This roadmap covers the Lean side of the project: what still has to be proved, in what order,
and what each step unlocks. The companion document [`TESTABILITY.md`](TESTABILITY.md) covers
the physics side, which turns the model into predictions that can be checked against data.

Equation numbers refer to Pourhasan, Afshordi & Mann, arXiv:1309.1487v2.

## Ground rules

- **Assumptions are hypotheses, never `axiom`s.** A physical input that Lean cannot derive yet
  goes in as a structure field or a theorem hypothesis, with its paper equation number in the
  docstring.
- **Definition of done for a theorem:** no `sorry`, and `#print axioms` lists only `propext`,
  `Classical.choice` and `Quot.sound`.
- **A hypothesis that gets discharged is removed.** When a field of `BraneCosmology` becomes a
  theorem, delete the field. Don't leave it as a redundant assumption.
- **Data are parameters, not constants.** Observational numbers (Planck amplitude, `r_c` bound)
  go into named hypotheses or a data structure, so a new data release does not mean rewriting
  proofs.

## Current status (snapshot)

| Area | State |
|---|---|
| Couplings, `r_c`, Planck masses (Eqs. 2, 18, 31) | proved |
| Bulk `f(r)`, `ρ_BH ∝ a⁻⁴`, horizon crossing (Eqs. 20, 28, 29) | proved |
| Quadratic and branches `ρ̃_±` (Eq. 26), reality (Eq. 30) | derived from junction + Friedmann |
| Induced pressure (Eq. 16) | derived from continuity (Eqs. 12–13) |
| General bulk `f` (M5) | Eqs. (26), (30), (16) and the singularity results proved for any `f` (`GeneralBulk.lean`); Schwarzschild derived as a special case. Schwarzschild–AdS₅ (`AdSBulk.lean`, M5.2) and Reissner–Nordström₅ (`ChargedBulk.lean`, M5.3) done |
| Observational bounds (Eqs. 33–35) | proved (Eq. 35 with fewer hypotheses than stated) |
| Leading-order amplitude (Eq. 48), `T_b/M₅` (Eq. 49), `M₅` bound (Eq. 51) | proved. `M(0) = 15ζ(5)/π²` is proved from the thermal integral (`thermalM_zero`, M7.1), so Eq. (48) no longer assumes it (`eq48_leading_thermalM`). The integral, `ζ(5)` and the coefficient range are proved (`Integrals.lean`, `Zeta.lean`, `ampCoeff_bounds`) |
| Brane geometry, Brown–York, Gauss–Codazzi (Eqs. 3–10), Friedmann (11) | **assumed** |
| Extrinsic curvature of the embedding (Eqs. 21–25) | **assumed** |
| Thermal correlators (Eqs. 39–47) | **assumed** |
| Eqs. (50)–(52) (Hubble, `M₅` and temperature bounds) | proved (`Monopoles.lean`), with `H₀`, `G_N`, the condition `H ≤ 2πT_b` and the radiation-era Friedmann equation as hypotheses |
| Normal orientation `ε` (Eqs. 21, 24, 25, 27) | resolved against the TeX source (`Orientation.lean`): `ε` is fixed by the sign of `ρ̃`, not by Eq. (27) |
| History of `ρ_BH/ρ` (M3.2) | proved (`History.lean`): era scaling, the matter-era bound for `ε = -1`, and orientation changes only on or inside the horizon |
| Pressure singularity (M3.4) | proved (`Singularity.lean`): at the saturated reality bound, where the branches meet; inside the horizon exactly when `\|H\| ≥ 1/(2r_c)` |
| Non-vacuity (does any `BraneCosmology` exist?) | proved (`Instances.lean`): a static family for both `ε = ±1` and any `r_h` outside the brane, and the self-accelerating de Sitter vacuum. An expanding solution with `r_h > 0` and radiation, in closed form (`Bounce.lean`, M2.2). With `ε = -1` on the normal branch there is **no** solution for ordinary matter (`NormalBranch.lean`, M2.3) |
| Dynamics (M4) | reduction to `ȧ² = F(a)` for `P = wρ` proved (`Dynamics.lean`, M4.1). Local existence and uniqueness away from the singularity proved, turning points included (`LocalExistence.lean`, `TurningPoint.lean`, M4.2). Maximal solutions proved, with escape from compact sets at a finite end (`MaximalSolution.lean`, M4.2). A global solution defines a `BraneCosmology` (`FromSolution.lean`, M4.2). Horizon-crossing time proved (`Horizon.lean`, M4.3). Late-time limits, the FRW limit and the singularity proved (`Asymptotics.lean`, M4.4) |
| Background vs BBN and CMB (TESTABILITY P3) | proved (`DarkRadiation.lean`): on either branch and for any `ρ_BH ≥ 0`, `H²` is standard FRW up to a relative `1/(r_c H_std)`. The bulk black hole is not dark radiation: `\|ΔN_eff\| ≤ 3×10⁻¹⁴` at BBN (`abs_deltaNeff_bbn`) |
| Axiom audit | enforced at build time (`Audit.lean`) |
| Acceleration equation | **derived** wherever `H ≠ 0`, with no smoothness assumption beyond the structure (`Acceleration.lean`). Not implied at `H = 0`: the static instances violate it. `BraneCosmology.IsSolution` adds it (M2.5) |

The formalization has surfaced seven issues: the Eq. (24) typo, Eq. (27) being wrong for
`ε = +1`, the paper's too-strong `ε = -1` (which caused the apparent normal-branch tension,
now resolved), the missing acceleration equation in `BraneCosmology` (M2.4), a dimension
error in Eq. (52), the white-hole history needing a change of orientation (M3.2), and the
horizon claim for the pressure singularity holding only when `|H| ≥ 1/(2r_c)` (M3.4). See the
README for details, and `docs/NOTE.md` for a short write-up (M3.5). The TeX source of
arXiv:1309.1487v2 was checked for issues 1–3 and 5. It is not committed: arXiv's default licence does not allow
redistribution. Get it from `https://arxiv.org/src/1309.1487v2`.

---

## Milestone 0: Guarantees and hygiene

Small and cheap, and makes every later milestone trustworthy.

- [x] **0.1 Axiom audit.** `HolographicUniverse/Audit.lean` has two checks. The `audit_axioms`
  command checks *every* declaration in the library, so new theorems are covered automatically.
  A `#print axioms` list for the headline theorems is pinned with `#guard_msgs`. The build fails
  if a `sorryAx` or a new axiom appears (tested with a planted `sorry` and `axiom`).
- [x] **0.2 CI.** `Audit.lean` is imported by the root module, so it is in the default target
  and `lean_action_ci.yml` checks it. A new module must be imported in both `Audit.lean` and
  `HolographicUniverse.lean`.
- [ ] **0.3 Assumption ledger.** Keep the README equation map in sync, or generate it from the
  docstrings, so every `BraneCosmology` field and every physics hypothesis is listed with its
  equation number. Partly done: `scripts/check_ledger.py` checks that every module is imported
  and listed, that every Lean name cited in `README.md`, `docs/NOTE.md` and `docs/ROADMAP.md`
  exists, and that the equation map cites every `BraneCosmology` field. CI runs it after the
  build (`lean_action_ci.yml`). Not done: the physics hypotheses of individual theorems.

## Milestone 1: Close the numerical gaps in Sec. 4

High value, and within reach of current Mathlib. When this is done, Eq. (49) depends only on
the physics inputs (`M(0)`, the leading-order form of Eq. 48) and the data, not on hand-supplied
numeric facts.

- [x] **1.1 `∫ dx/(1+x²)² = π/2`.** Done in `Integrals.lean`
  (`integral_univ_inv_one_add_sq_sq`), with the antiderivative `x/(2(1+x²)) + arctan(x)/2` and
  the improper FTC (`integral_of_hasDerivAt_of_tendsto`). `eq48_leading` now contains the
  integral itself, not the value `π/2`. The integral is over the whole real line: that is the
  domain that gives `π/2` (the half line gives `π/4`). The TeX source confirms the domain:
  Eq. (48) has `∫_{-∞}^{∞}`.
- [x] **1.2 Bounds on `ζ(5)`.** Done in `Zeta.lean`. `zeta5` is the real series `∑ 1/n⁵`, and
  `riemannZeta_five` identifies it with `riemannZeta 5`. The lower bound is the exact sum of the
  first ten terms (`1.0369073…`). The upper bound replaces the integral with a telescoping bound,
  `1/(m+1)⁵ ≤ 1/(4m⁴) - 1/(4(m+1)⁴)`, so the tail is at most `1/(4·10⁴)`. Results:
  `zeta5_bounds : 1.0369 ≤ ζ(5) ≤ 1.0370`, and the sharper `zeta5_upper : ζ(5) ≤ 1.03694`
  (`ζ(5) = 1.036927…`). `riemannZeta_five_bounds` restates them for `riemannZeta 5`.
- [x] **1.3 Bounds on `π`.** Mathlib's `Real.pi_gt_d6` and `Real.pi_lt_d6`, used in 1.4.
- [x] **1.4 Coefficient theorem.** Done in `Perturbations.lean`. `ampCoeff` is
  `25ζ(5)/(3072π⁴)`. `ampCoeff_bounds` proves `[8.65, 8.67]×10⁻⁵`, and `ampCoeff_sharp` proves
  `[8.6627, 8.6631]×10⁻⁵` (true value `8.66299×10⁻⁵`). `eq49` no longer has the `hk` hypothesis.
  The old statement is kept as `eq49_of_coeff`, for a general coefficient, because M1.5 needs it.
  `eq48_eq49` chains Eq. (48) into Eq. (49), so the only physics input left is `M(0)`.
- [x] **1.5 Data as parameters.** Done in `ObsData.lean`. `ObsData` holds the amplitude
  interval, pivot scale, `n_s` interval and `r_c H₀` bound. `ObsData.tbm5_bounds` and
  `ObsData.eq51` are the general statements. A result for a new release needs only two
  `norm_num` checks. Instances:
  - `planck2013` (the paper's values): `eq49_planck2013_sharp` gives `T_b/M₅ ∈ [0.17061, 0.17216]`.
    This matches the paper's `0.17139 ± 0.00077` to the last digit.
  - `planck2018`: the amplitude is stored as published, `exp(3.044 ± 0.014)·10⁻¹⁰`, and `exp` is
    bounded in the proof. `eq49_planck2018` gives `T_b/M₅ ∈ [0.1697, 0.17051]`.
  - `planck2013_planck2018_disjoint`: the two 1σ intervals do not overlap. This follows from the
    data alone (the 1σ amplitude intervals are disjoint), so it is not evidence against the
    model. It means a theorem proved with the 2013 numbers does not apply to the 2018 numbers.
  - The `n_s` fields are used by M7.2.
- [x] **1.6 Eqs. (50)–(52).** Done in `Monopoles.lean`. Energies are in GeV. Corrected after
  the TeX source check: Eq. (51) is `H ≲ M₅ ≲ (H₀M₄²/6)^{1/3} ∼ 9 MeV`, and Eq. (52) is the
  plasma temperature in the radiation era, not the atmosphere temperature `T_b`.
  - `eq50`: `H ≤ 2πT_b` and `T_b/M₅ ≤ 0.1723` give `H < 1.09 M₅`, the first half of Eq. (51).
    The condition `H ≤ 2πT_b` is a hypothesis.
  - `M5_cube_le`: the second half of Eq. (51) in terms of `G_N`, `M₅³ ≤ H₀/(96πG_N)`.
  - `eq51_numeric`: `M₅ ≤ 9 MeV`, from `r_c ≥ 3/H₀`, `H₀ ≤ 1.47×10⁻⁴² GeV` (`h ≤ 0.689`) and
    `G_N ≥ 6.708×10⁻³⁹ GeV⁻²`. The paper's `9 MeV` is reproduced. `hubble_le`: `H ≤ 9.81 MeV`.
  - `radiation_T4`, `eq52`: with the radiation-era Friedmann equation as a hypothesis and
    `g_* ≥ 100`, `T ≤ 8.5×10⁷ GeV = 8.5×10⁴ TeV`. The paper says `3×10⁴ TeV`. The difference
    is an `O(1)` factor, and the printed formula has a dimension error (README issue 5).
  - `eq52_below_GUT`: `T ≤ 10⁻⁷ T_GUT` for any `T_GUT ≥ 10¹⁵ GeV`.
  - Not in the paper: `Tb_le`, `Tb_le_planck2013`, `Tb_le_planck2018` give `T_b ≤ 1.56 MeV`.

## Milestone 2: Non-vacuity

Every theorem about `BraneCosmology` is vacuous if no such structure exists. This is the
most important gap in the current development.

- [x] **2.1 Trivial instance.** `Instances.lean` builds two:
  - `BraneCosmology.static`: a static brane (`a = 1`) for every coupling, either `ε = ±1`, and
    any `r_h` with `𝒦 r_h² ≤ 1`. Gives `BraneCosmology.nonempty`.
  - `BraneCosmology.deSitter`: the self-accelerating vacuum `a = r_c cosh(t/r_c)`, `r_h = 0`,
    `ρ = 0`, `ρ̃ = -P̃ = 2ρ̃_s`, for every coupling. It is expanding, and satisfies Eq. (16).
- [x] **2.2 Non-trivial instance.** Done in `Bounce.lean`, in closed form. For radiation with
  `ρ = ρ_BH` (both `∝ a⁻⁴`), the self-accelerating branch is constant, `ρ̃ = 2ρ̃_s`, and the
  Friedmann equation is `ȧ² = 𝒦²r_h²/a² + a²/r_c² - 𝒦`. If `2r_h ≤ r_c`, it has the solution
  `a² = 𝒦r_c²/2 + q cosh(2t/r_c)`, `q = 𝒦r_c√(r_c²/4 - r_h²)`, positive for all `t`
  (`BraneCosmology.radiationBounce`). At `r_h = 0`, `𝒦 = 1` it is the de Sitter vacuum. It obeys
  the acceleration equation and Eq. (16) at every time, the bounce included, so it is a solution
  of the equations of motion. It expands for `t > 0` when `2r_h < r_c`, and it stays outside the
  horizon. `exists_expanding_radiation` is the statement with `r_h > 0`, `ρ > 0`, `ε = -1`.
  Limits: the fine tuning `ρ = ρ_BH`, and the self-accelerating branch. Dust, or radiation with
  `ρ ≠ ρ_BH`, has no closed form here and needs M4.2.
- [x] **2.3 Consistency of the sign convention.** Show that the instance from 2.2 can have
  `ε = -1` on the normal branch. If it cannot, that is a sharp form of issue 3.
  **Answer: it cannot**, for matter with `ρ + 3P > 0` and `3P ≤ ρ` (dust and radiation with
  `ρ > 0`). Done in `NormalBranch.lean`:
  - `BraneCosmology.not_isSolution_normal_eps_neg`: no solution (`IsSolution`) has `ε = -1` and
    `ρ̃ < ρ̃_s` at every time. With `ε = -1`, `ρ̃ ≥ 0`. Then Eq. (16) gives `P̃ ≥ 0`, and the
    acceleration equation gives `ä < 0` at every time. A function with `ä < 0` on all of `ℝ`
    is not positive at every time (`exists_nonpos_of_strictAnti_deriv`).
  - `BraneCosmology.not_isSolution_minus_branch`: the same on the branch `ρ̃_-` away from the
    singularity.
  - The static witness `exists_normal_branch_eps_neg` is not a solution. So the fields alone
    allow `ε = -1` on the normal branch, but the equations of motion do not, if time is all
    of `ℝ`.
  - Interpretation: this is the brane form of a result of general relativity. A closed
    universe with `ρ + 3P > 0` decelerates at all times, so it has a finite past or a finite
    future. The induced fluid adds to the deceleration. A normal-branch history with `ε = -1`
    lives on a bounded interval of time (M4.2 gives it as a maximal solution). The paper's
    white-hole history starts at the singularity, so it is such a history. The result does
    not contradict the paper. It shows that `BraneCosmology`, with `a` at every time, cannot
    hold that history. The case `ε = +1` (`ρ_BH < ρ`) is not covered.
- [x] **2.4 Acceleration equation.** Done in `Acceleration.lean`:
  - `accel_of_friedmann`, `BraneCosmology.accelAt_of_ne`: Friedmann + continuity imply
    `ä/a = -(4πG_N/3)(ρ + ρ̃ + 3(P + P̃))` wherever `H ≠ 0`.
  - `differentiableAt_deriv_of_sq_eq`: `ä` exists wherever `H ≠ 0`. This did not need a new
    hypothesis. `ȧ² = g` with `g` differentiable, and Darboux's theorem fixes the sign of `ȧ`
    locally, so `ȧ = ±√g`.
  - `static_not_accelAt`: at `H = 0` the equation is **not** implied. Every static instance
    violates it (`ä = 0`, right side `-𝒦/2`).
  - `deSitter_accelAt`: the de Sitter vacuum satisfies it at all times, bounce included.
- [x] **2.5 Decision: the equations at `H = 0`.** The structure now has a predicate
  `BraneCosmology.AccelAt` but no field for it. Two quantities are undetermined on an interval
  with `H = 0`: `ä` (the acceleration equation) and `P̃` (Eq. (16), which in the paper comes
  from the `ττ` junction condition, Eq. (25)). Options:
  - **(a) Keep the structure, pass `AccelAt` as a hypothesis** where a theorem needs it. This
    is the current state. It is enough while every theorem is pointwise.
  - **(b) Add fields** for the acceleration equation and for Eq. (16) / Eq. (25). The fields
    are redundant wherever `H ≠ 0`. They exclude the static non-solutions.
  - Recommendation: stay with (a) until M4. Then take (b), because M4.2 needs it. The Friedmann
    equation as a first-order ODE `ȧ² = F(a)` has a spurious constant solution at every turning
    point `F(a*) = 0`, so uniqueness through a bounce fails without the acceleration equation.
  - **Decision: (c), a predicate.** `BraneCosmology.IsSolution` (`Dynamics.lean`) is the
    acceleration equation at every time, and Eq. (16) at every time with `ρ̃ ≠ ρ̃_s`. Eq. (16)
    divides by zero at the singularity, so the predicate does not constrain `P̃` there. This
    gives the effect of (b) without a change to the structure. The theorems about the
    structure stay as general as before, and the static instances stay valid as a check that
    the fields are consistent. A theorem that needs the equations of motion takes
    `M.IsSolution` as a hypothesis. Results: `isSolution_of_ne` (automatic wherever `H ≠ 0`),
    `static_not_isSolution`, `deSitter_isSolution`, `radiationBounce_isSolution`.

## Milestone 3: Resolve the surfaced issues

The testability work (`TESTABILITY.md`, gate G0) needs these settled first, because they
decide which part of parameter space is physical.

- [x] **3.1 Normal-branch sign tension.** Done in `Orientation.lean`, after checking the TeX
  source. Eqs. (6) and (10) are consistent with each other. The tension came from the paper's
  `ε = -1`, which is inferred circularly (see 3.3).
  - `orientation_iff`: where `X > 0`, `ε = -1 ⇔ ρ̃ > 0` and `ε = +1 ⇔ ρ̃ < 0`.
  - The consistent region: `ρ̃_+` needs `ε = -1` (`orientation_plus_branch`). `ρ̃_-` needs
    `ε = -1` if `ρ_BH > ρ` and `ε = +1` if `ρ_BH < ρ` (`orientation_minus_branch`).
  - `minkowski_normal_branch`: without a black hole the normal branch needs `ε = +1`, as in
    standard DGP.
  - `rhoTilde_eq_zero_inside`: `ρ̃ = 0` only on or inside the horizon.
  - Not yet decided: which side of the brane the `Z₂`-reflected bulk keeps for `ε = +1`, and
    whether that fits the paper's black-hole picture.
- [x] **3.2 Time dependence of `ρ_BH/ρ`.** Done in `History.lean`. Eras are hypotheses on an
  interval (`P = ρ/3`, `P = 0`, or `P ≤ ρ/3` with `ȧ ≥ 0`).
  - `radiation_era_ratio`: `ρ_BH/ρ` is constant. `matter_era_ratio`: `(ρ_BH/ρ) · a` is
    constant. `ratio_antitoneOn`: the ratio never rises while the universe expands with
    `P ≤ ρ/3`.
  - `rho_le_rhoBH_of_eps_neg`, `rhoBH_le_rho_of_eps_pos`: a fixed `ε` keeps one sign of
    `ρ_BH - ρ` on the normal branch. `eps_of_singularity`: the pressure singularity needs
    `ε = -1`.
  - `matter_era_growth_le_small`: with `ε = -1` and the bound (32) at its start, a normal-branch
    matter era grows `a` by at most `1 + ϵ` (10 % for `ϵ = 0.1`).
  - `sign_change_inside`, `sign_const_outside`: with a time-dependent `ε`, `ρ̃` can change sign
    only through `ρ̃ = 0`, on or inside the horizon.
  - Consequence (README issue 6): the paper's white-hole history needs `ε` to change from `-1`
    to `+1` before the brane leaves the horizon. Not decided: whether such a change is
    geometrically allowed. If it is, `BraneCosmology` needs a time-dependent `ε` (M4).
- [x] **3.3 Eq. (27) at `ε = +1`.** Eq. (27) is wrong as printed for `ε = +1`.
  `pressure_of_timelike_junction`: Eq. (25) set equal to the `ττ` part of Eq. (10) gives
  Eq. (16) for either `ε`, once `X = -ε(8πG_b/3)ρ̃` is used. `eq27_of_dropped_sign`: Eq. (27) is
  what the same step gives with `X = +(8πG_b/3)ρ̃`, which is true only for `ε = -1`.
- [x] **3.4 Pressure singularity.** Done in `Singularity.lean`. The horizon claim is in Sec. 5
  of the TeX source.
  - `isInduced_eq_rhoS_iff`, `BraneCosmology.singularity_iff`: `ρ̃ = ρ̃_s` exactly when
    `2(ρ_BH - ρ) = ρ̃_s`. `branches_meet_iff`: under (30), `ρ̃_+ = ρ̃_-` exactly there, and
    both equal `ρ̃_s` (`rhoTilde_at_saturation`).
  - `BraneCosmology.singularity_inside_iff`: at the singularity, `f(a) ≤ 0` exactly when
    `|H| ≥ 1/(2r_c)`. Strict form, density form (`𝒦/a² ≤ (8πG_N/3)(ρ + ρ̃_s/2)`) and an
    early-time corollary (`singularity_inside_of_rc`). The paper's "always" is conditional
    (README issue 7).
  - `BraneCosmology.scale_factor_floor`: in an expanding era with `P ≤ ρ/3`, the reality bound
    puts a floor under `a` once `ρ_BH > ρ`. That a history reaches the singularity needs M4.
- [x] **3.5 Write-up.** Done in `docs/NOTE.md`. It collects README issues 1–7, orders them by
  their effect on the paper's conclusions, and names the Lean theorem for each claim. Contacting
  the authors is optional and is the user's decision.

## Milestone 4: Dynamics

Turns the algebraic constraints into statements about whole histories.

- [x] **4.1 Reduction to an ODE.** Done in `Dynamics.lean`. For `P = wρ`, `ρ a^{3(1+w)}` is
  constant (`barotropic_const`, `rho_barotropic`). If the history never reaches the pressure
  singularity, `ρ̃` stays on one branch for all time (`branch_fixed`, by the intermediate value
  theorem: the branches meet only at the singularity). Then `ȧ² = F_sgn(a)` with
  `F = friedmannF` (`deriv_a_sq_eq`, `reduction`). The bounce of M2.2 solves it with `w = 1/3`,
  `sgn = +1` (`radiationBounce_reduction`).
- [x] **4.2 Local existence and uniqueness.** Use Mathlib's Picard–Lindelöf
  (`Analysis/ODE/PicardLindelof.lean`, `Analysis/ODE/ExistUnique.lean`) away from `H = 0` and
  from the pressure singularity. Feeds Milestone 2.2. At `H = 0` the first-order equation is
  not enough (see M2.5): use the second-order acceleration equation there.
  - [x] **First-order part.** Done in `LocalExistence.lean`. `F` is smooth away from `a = 0`
    and from the singularity, where the square root in `ρ̃_±` has a zero argument
    (`contDiffAt_friedmannF`, `BraneCosmology.realityArg_ne`). Where `F(a₀) > 0`, the field
    `s√F` is `C¹`, so `ȧ = s√F(a)`, `s = ±1`, has a local solution (`exists_local_solution`)
    and it is locally unique (`local_unique`). For a brane cosmology with `P = wρ` on a fixed
    branch, at a time with `H ≠ 0` and `ρ̃ ≠ ρ̃_s`, the scale factor is that unique solution
    near that time (`BraneCosmology.locally_determined`). The sign of `ȧ` is locally fixed by
    Darboux (`deriv_eventuallyEq_sqrt`).
  - [x] **Turning points.** Done in `TurningPoint.lean`. `F'(a)` in closed form is
    `2 · (-(4πG_N/3)(ρ + ρ̃ + 3(wρ + P̃)) a)`, with `P̃` from Eq. (16) (`hasDerivAt_friedmannF`).
    So for a solution (`IsSolution`) with `P = wρ`, the acceleration equation is
    `ä = F'(a)/2` at every time away from the singularity, `H = 0` included
    (`BraneCosmology.accel_eq_deriv`). Picard–Lindelöf on `ℝ²` for the pair `(a, ȧ)`: where
    `F` is `C²`, solutions exist and are locally unique (`exists_local_solution₂`,
    `local_unique₂`). If `ȧ(t₀)² = F(a(t₀))`, the solution solves `ȧ² = F(a)`, because
    `ȧ² - F(a)` is conserved. A solution is fixed locally by `a(t₀)` and `ȧ(t₀)`, also at
    `H = 0` (`BraneCosmology.locally_determined₂`). A solution stays at rest only where
    `F = F' = 0` (`equilibrium_of_rest`). The radiation bounce is the only solution with its
    data at the bounce (`radiationBounce_determined`).
  - [x] **Global solutions.** Done in `MaximalSolution.lean`. Decision: maximal intervals, not
    a structure on a time interval. For an autonomous ODE `ẋ = v(x)` with `v` `C¹` on an open
    set `U`: two solutions on an open interval that agree at one time agree on the interval
    (`IsSolOn.eqOn`); every initial value has a maximal solution on an open interval `J`
    (`exists_isMaximalSolution`), and it is unique (`IsMaximalSolution.unique`). At a finite
    end of `J`, the solution leaves every compact subset of `U` and does not come back
    (`IsMaximalSolution.eventually_not_mem_right`, `..._left`). Local existence time is uniform
    on compact sets (`exists_local_mem_of_isCompact`). For `ä = F'(a)/2` on the open set
    `braneDomain` (`a > 0`, away from the singularity): `ȧ² - F(a)` is conserved on `J`
    (`IsMaximalSolution.energy₂`), and at a finite end `a` leaves every compact subset of the
    domain (`exists_maximal_history`). So a history ends only at `a → 0`, at the pressure
    singularity, or at `a → ∞`. A brane-cosmology solution with `P = wρ` on a fixed branch that
    never reaches the singularity is the maximal solution of its data, and `J = ℝ`
    (`BraneCosmology.maximal_eq`).
  - [x] **From a global solution to a `BraneCosmology`.** Done in `FromSolution.lean`. The
    converse of `maximal_eq`. A differentiable `a` in `braneDomain` with `ȧ² = F(a)` at every
    time defines `ρ = ρ₀a^{-3(1+w)}`, `P = wρ`, `ρ̃ = ρ̃_sgn(a)` and `P̃` from Eq. (16)
    (`BraneCosmology.ofSolution`). The orientation `ε` must obey `ε ρ̃ ≤ 0` at every time, as
    in every instance (`eps_mul_ρt_nonpos`). The key step is `dρ̃/da = -3(ρ̃ + P̃)/a`
    (`hasDerivAt_rhoTildeX`), which is Eq. (13); it follows from `F'` by uniqueness of the
    derivative. If `ä = F'(a)/2` also holds, the instance is a solution
    (`ofSolution_isSolution`). For a maximal solution with interval `ℝ`:
    `BraneCosmology.exists_of_maximal`.
- [x] **4.3 Horizon-crossing time.** Done in `Horizon.lean`. Prove there is a `t*` with
  `a(t*)/√𝒦 = r_h`, and that it is unique while the brane is expanding. This is the moment the
  universe "leaves the white hole". Strictly inside the horizon, `a < a_h = √𝒦 r_h`, the
  junction condition gives `H² ≥ (𝒦/a⁴)(a_h² - a²) > 0`, so `ȧ ≠ 0`
  (`BraneCosmology.deriv_ne_zero_of_inside`). By Darboux, `ȧ` keeps one sign while the brane
  stays inside. A brane that expands inside the horizon was inside and expanding at every
  earlier time (`white_hole_past`). A brane that contracts inside stays inside and contracting
  (`black_hole_future`). If an expanding brane inside the horizon is on or outside it at some
  time, there is exactly one `t*` with `a(t*) = a_h` and the brane inside before it, and the
  brane expands before `t*` (`BraneCosmology.exists_unique_exit`). On the horizon,
  `H² = (8πG_b ρ̃/3)²` (`hubble_sq_at_horizon`). Not proved: that the brane reaches the
  horizon. That is a hypothesis, because `a` could approach `a_h` without reaching it.
- [x] **4.4 Asymptotics.** Done in `Asymptotics.lean`. Late times: on the self-accelerating
  branch `H → 1/r_c` (de Sitter). On the normal branch, recover standard FRW when `ρ ≫ ρ̃_s`.
  Early times: behavior near the singularity.
  - **Late times.** For `P = wρ`, `w > -1`, on one branch `sgn`, and `a → ∞`: `ρ → 0`,
    `ρ̃ → ρ̃_s(1 + sgn)` and `H² → (8πG_N/3) ρ̃_s(1 + sgn)` (`BraneCosmology.tendsto_late`). On
    `ρ̃_+`, `H² ≥ 1/(2r_c²) - 𝒦/a²`. So a history with `ρ ≥ 0` that expands at a time with
    `a² > 2𝒦r_c²` expands at every later time, has `a → ∞` (`expands_of_self_acc`), and has
    `H → 1/r_c` (`tendsto_deSitter`). On `ρ̃_-`, if `a → ∞`, then `ρ̃ → 0` and `H → 0`
    (`tendsto_normal`). There `a → ∞` is a hypothesis, because a closed universe can recollapse.
  - **Standard FRW.** `|ρ̃_-| ≤ √(2ρ̃_s|ρ - ρ_BH|)` under the reality bound
    (`abs_rhoTilde_minus_le`). So on the normal branch with `0 ≤ ρ_BH ≤ ρ`, the Friedmann
    equation is the standard one up to a relative error `√(2ρ̃_s/ρ)`
    (`BraneCosmology.normal_branch_frw_of_le`). This is `1/(r_c H_std)`, with
    `H_std² = (8πG_N/3)ρ`: the deviation is at most `H_std/r_c` (`normal_branch_frw_rc_of_le`).
  - **The singularity.** As `ρ̃ → ρ̃_s` from below with `3P - ρ < 2ρ̃_s`, `P̃ → +∞`
    (`tendsto_pressureTilde_atTop`). In a `BraneCosmology`, `ρ̃` is differentiable, and
    `(ρ̃ - ρ̃_s)² = ρ̃_s² - 2ρ̃_s(ρ_BH - ρ)`. The derivative of the left side is zero at the
    singularity, so `H(3P - ρ - 2ρ̃_s) = 0` there (`BraneCosmology.singularity_at_rest`). For
    `3P ≤ ρ` the brane is at rest at the singularity and strictly outside the horizon
    (`singularity_outside_of_le`). A history that reaches the singularity with `H ≠ 0` has,
    generically, `ρ̃ - ρ̃_s ∝ √|a - a_s|` by Eq. (26), which is not differentiable in `t`. Such a history can only start or
    end at the singularity, as the paper's white-hole history does.

## Milestone 5: Generalize the bulk

Needed by several testability pathways (curvature with anisotropy, AdS embedding).

- [x] **5.1 Generic blackening factor.** Done. `rhoBulk` (`Bulk.lean`) is the density that a
  general `f` contributes to the Friedmann equation, `𝒦f(r)/a² = 𝒦/a² - (8πG_N/3)ρ_bulk`
  (`curv_mul_f`). For Schwarzschild it is `ρ_BH` (`rhoBulk_blacken`). `isInduced_of_bulk` gives
  Eq. (26) for any bulk term. `pressure_of_continuity_bulk` gives Eq. (16) in the general form
  `P̃ = (ρ̃² - 2ρ̃_s(P - P_b))/(2(ρ̃_s - ρ̃))`, where `P_b` is the pressure of `ρ_bulk`; with
  `P_b = ρ_bulk/3` it is Eq. (16) (`pressureTildeBulk_radiation`). `BulkCosmology`
  (`GeneralBulk.lean`) is the model for any `f`, with Eqs. (26), (30), (16), and the
  pressure-singularity results. `BraneCosmology.toBulk` is the Schwarzschild case, and the
  quadratic, the sign of `ρ̃`, Eq. (16) and the singularity results for `BraneCosmology` are now
  derived from the general ones. README issue 7 holds for every `f`. Results that use
  `ρ_BH ∝ a⁻⁴` (`History.lean`, `scale_factor_floor`) stay Schwarzschild-specific.
- [x] **5.2 Schwarzschild–AdS₅.** Done in `AdSBulk.lean`. `f = 1 + r²/L² - r_h²/r²`. The
  paper says the results "need not significantly change" (Sec. 5). Prove that, or state
  precisely how they change. The bulk density is `ρ_BH - ρ_Λ`, `ρ_Λ = 3/(8πG_N L²)`
  (`rhoBulk_blackenAdS`): the "small constant" of Sec. 5, with a negative sign. Eqs. (26) and
  (30) hold with `ρ_BH - ρ_Λ`, and the reality bound is relaxed by `2ρ_Λ` (`reality_AdS`).
  Eq. (16) holds with `3P - ρ` replaced by `3P - ρ - 4ρ_Λ` (`pressure_AdS`). The general rule is
  `pressureTildeBulk_extra`: an extra bulk term with density `d` and pressure `p` replaces `T` by
  `T + d - 3p`. The horizon results are unchanged. At late times, with `a → ∞` and `ρ → 0`,
  `H² → (1 + sgn √(1 + 4r_c²/L²))/(2r_c²)` (`tendsto_hubble_sq_AdS`). On the normal branch the
  limit of `ρ̃` is negative, so no such history exists (`not_tendsto_atTop_normal_AdS`): without
  a brane tension, an AdS bulk makes the normal branch recollapse, for every finite `L`.
- [x] **5.3 Charged bulk (Reissner–Nordström).** Done in `ChargedBulk.lean`.
  `f = 1 - r_h²/r² + q²/r⁴`. This adds a `∝ a⁻⁶` term, which BBN can bound. The bulk density is
  `ρ_BH - ρ_Q`, `ρ_Q = 3𝒦³q²/(8πG_N a⁶)` (`rhoBulk_blackenRN`, `rhoQ_mul_a6`). Eq. (16) holds
  with `3P - ρ` replaced by `3P - ρ + 2ρ_Q` (`pressure_RN`), and the reality bound is relaxed by
  `2ρ_Q` (`reality_RN`). `ρ_Q/ρ_BH = 𝒦q²/(r_h²a²)`, so the bulk density is negative exactly
  when `r_h²a² < 𝒦q²` (`rhoBulk_RN_neg_iff`). Above extremality, `r_h⁴ < 4q²`, `f > 0`
  everywhere, so there is no horizon and no white hole, and at the singularity
  `|H| < 1/(2r_c)` (`singularity_hubble_lt_RN`). Not done: the numerical BBN bound on `q`. It
  needs the BBN constraint on extra energy density as an input.

## Milestone 6: Geometry from first principles (long term)

Replaces the geometric fields of `BraneCosmology` with theorems.

- [ ] **6.1 Coordinate route, Friedmann.** Write the FRW metric (Eq. 3) as explicit component
  functions on coordinates. Compute Christoffel symbols and the Einstein tensor with `deriv`,
  and derive Eq. (11). This needs no manifold library.
- [ ] **6.2 Coordinate route, embedding.** Use the same method for the brane `r = a(τ)/√𝒦`,
  `t = T(τ)` in the 5D Schwarzschild metric (Eq. 19). Derive the normal vector, the 4-velocity
  (Eq. 22) and `K_ij` (Eqs. 24–25). This would also settle the Eq. (24) typo for good.
- [ ] **6.3 Junction condition.** Derive the Israel / Brown–York condition (Eq. 6) from the
  action (Eq. 1). This needs variational calculus with boundary terms, and is the hardest item
  here.
- [ ] **6.4 Manifold route.** Mathlib has Riemannian metrics on bundles
  (`Geometry/Manifold/Riemannian`), but no pseudo-Riemannian metrics, Levi-Civita connection or
  Ricci curvature. Either contribute these upstream or keep using 6.1–6.2.

## Milestone 7: Perturbations (Sec. 4)

- [x] **7.1 `M(0) = 15ζ(5)/π²`.** Done in `ThermalIntegral.lean`. Define `M(κ)` as the integral
  in the paper. The value at zero needs the Bose–Einstein integral
  `∫₀^∞ x^{s-1}/(eˣ-1) dx = Γ(s)ζ(s)`. Mathlib does not have it, so it is proved for the case
  needed with the Bose series `eˣ/(eˣ-1)² = Σ k e^{-kx}` (`hasSum_bose`) and the Gamma integral:
  `∫₀^∞ x⁵eˣ/(eˣ-1)² dx = 120ζ(5)` (`integral_bose`). `thermalM` is the integral (46) over `ℝ⁴`
  without the vacuum term `ω₊ω₋/4`. At `κ = 0` that term is `|κ'|²/4`, which has no scale, so
  dimensional regularization sets it to zero. In polar coordinates (`integral_fun_norm_addHaar`,
  unit ball volume `π²/2`), `M(0) = 15ζ(5)/π²` (`thermalM_zero`), in `[1.5758, 1.5761]`
  (`thermalM_zero_bounds`). Eq. (48) no longer assumes `M(0)` (`eq48_leading_thermalM`).
- [x] **7.2 Scale invariance at leading order.** Done in `ScaleInvariance.lean`.
  - `spectralIndex P k = 1 + kP′(k)/P(k)`. `spectralIndex_powerLaw` checks the definition: it
    gives `n` for `A(k/k₀)^(n−1)`.
  - `spectralIndex_comp`: for `P(k) = C·M(k/s)`, `n_s − 1 = κM′(κ)/M(κ)`. The tilt has the sign
    of `M′`. This is the starting point for M7.3.
  - `leadingSpectrum_ns`: the leading-order spectrum has `n_s = 1` at every `k`.
  - `ObsData.Fits` and `ObsData.not_fits_of_locallyConst` are the template: if a release has
    `ns_hi < 1`, no spectrum that is constant near the pivot fits it.
  - **First falsification theorem:** `leading_order_ruled_out_planck2013` and
    `leading_order_ruled_out_planck2018`. The leading-order spectrum fits neither release, for
    any `T_b/M₅`. `planck2013_ns_excludes_one` (>5σ, the paper's figure) and
    `planck2018_ns_excludes_one` (>8σ) give the significance, under a Gaussian reading of the
    1σ intervals.
  - That next-order terms cannot rescue the model is M7.3 (`ObsData.not_fits_thermal`).
- [x] **7.3 Next-order term.** Find the sign and size of the `O((k/a_bT_b)²)` correction in
  Eq. (48). Show whether it can produce `n_s < 1` at CMB scales. Done, in `NextOrder.lean`,
  `RadialIntegrals.lean`, `SecondOrder.lean` (small `κ`) and `BlueTilt.lean` (all `κ`).
  - **Result.** Along a ray `κ = te`, `m(t) = M(te)` has `m′(0) = 0` (`deriv_mRay_zero`) and
    `m″(0) = (10ζ(5) - ζ(3))/(16π²) > 0` (`hasDerivAt_deriv_mRay`, `secondOrderCoeff_pos`). So
    `M(κ) = M(0) + (10ζ(5) - ζ(3))/(32π²)·κ² + o(κ²) ≈ 1.5759 + 0.02903κ²`, and
    `n_s - 1 ≈ 0.037κ² > 0`: the next order is blue. For small `κ > 0`, `M > 0` and `M′ > 0`
    (`next_order_blue`). **Second falsification theorem:** for a release with `n_s < 1`, no
    spectrum `C·M(k/s)` fits it with the pivot at small enough `κ = k/s`
    (`ObsData.not_fits_next_order`).
  - **Split.** `ω_± = |κ' ± κ/2|` (`omegaPM_one`, `omegaPM_neg_one`). With `φ(x) = x/(eˣ - 1)`,
    `(2π)⁴M(κ) = B(κ) + A(κ)` (`thermalM_eq`), with the autocorrelation
    `B(κ) = ∫φ(|u|)φ(|u - κ|)` and `A(κ) = ∫|v + κ|φ(|v|)`. `A` is convex and smallest at
    `κ = 0` (`convexOn_thermalA`, `thermalA_zero_le`). `B` is largest at `κ = 0`
    (`thermalB_le_zero`). So symmetry alone does not fix the sign.
  - **Radial integrals** (`RadialIntegrals.lean`). `∫₀^∞ r³φ′ dr = -π⁴/5` (`integral_dphiB`) and
    `∫₀^∞ r³φ′² dr = 2ζ(3) + π⁴/5 - 20ζ(5)` (`integral_dphiB_sq`). Each product of `n` and
    `1 + n` is `xᵃ/(1 - x)^{k+1}` with `x = e^{-r}` (`hasSum_bose_pow`), and
    `integral_pow_mul_series` integrates term by term.
  - **Expansion** (`SecondOrder.lean`). The kernel `|v + κ|` has an unbounded second derivative,
    so `A` is differentiated once (`hasDerivAt_thermalA_ray`). A shift then moves `t` into the
    smooth factor `φ` (`a1_eq`) for the second derivative. Bounds: `|φ′(r)| ≤ (3 + 4r)e^{-r}`
    (`abs_dphiB_le_exp`) and `|φ′| ≤ 1/2` (`abs_dphiB_le_half`). The same for `B`
    (`hasDerivAt_thermalB_ray`, `b1_eq`). Coordinate swaps are isometries, so
    `∫(w₀/|w|)²g(|w|) = ¼∫g(|w|)` (`integral_sq_coord_div`). Then `A″(0) = π⁶/10`
    (`hasDerivAt_a1_zero`) and `B″(0) = -(π²/2)∫r³φ′²` (`hasDerivAt_b1_zero`).
  - A direct quadrature of Eq. (46) agrees with the coefficient (`0.02901` at `κ = 0.25`,
    `0.02879` at `κ = 1`).
  - **All `κ`** (`BlueTilt.lean`). With `w ↦ -w` in `b1_eq`, `B′(t) + A′(t) = ∫ g(w)φ(|w - te|)`
    with `g(w) = ⟨w, e⟩/|w| · (1 + φ′(|w|))` (`b1_add_a1`). The reflection in `e^⊥` makes `g`
    odd, so `2(B′ + A′) = ∫ g(w)[φ(|w - te|) - φ(|w + te|)]` (`two_mul_b1_add_a1`). Now
    `1 + φ′ ≥ 1/2` and `φ` is strictly decreasing (`strictAntiOn_phiB`), so both factors have
    the sign of `w₀` and the integrand is positive almost everywhere (`b1_add_a1_pos`). So `m` is
    strictly increasing on `[0, ∞)` (`strictMonoOn_mRay`). Isometries preserve `M`
    (`thermalM_map`), so `M(κ) = m(|κ|)` (`thermalM_eq_mRay`) and `M` is strictly increasing in
    `|κ|` (`thermalM_lt_of_norm_lt`). Then `n_s > 1` at every `k > 0`
    (`spectralIndex_thermal_gt_one`). **Third falsification theorem:** for a release with
    `n_s < 1`, no spectrum `C·M(k/s)` fits it, for any `C ≠ 0` and `s > 0`
    (`ObsData.not_fits_thermal`). The question whether `κ` is small at CMB scales no longer
    matters.
- [ ] **7.4 Thermal correlator (Eq. 39).** Out of reach for now. Keep it as a hypothesis, but
  state it precisely as a property of a function on `ℝ⁴`, not in prose.

## Milestone 8: Prediction interface

The bridge to `TESTABILITY.md`. Each pathway there that reaches "has a formula" should get an
entry here.

- [ ] **8.1 `Observables.lean`.** Define each observable as a function of the model parameters:
  `A_s`, `n_s`, `r`, `f_NL`, `ΔN_eff`, `Ω_k`, `H(z)`, `d_L^GW/d_L^EM`.
- [ ] **8.2 Interval theorems.** For each observable, prove that the allowed parameter region
  maps into an explicit interval, in the style of `eq49`.
- [ ] **8.3 Falsification lemmas.** State them in contrapositive form: if the measured value is
  outside the proved interval, then a *named* hypothesis (a field of `BraneCosmology`, or a
  physics input) is false. This says *which* assumption failed, which most phenomenology does
  not.
  - **P2, cascading gravity** (`Cascade.lean`). Tilts add (`spectralIndex_mul`), so M7.3
    extends to `C·M(k/s)·G(k/s′)` for any positive `G` that is nondecreasing on `(0, ∞)`
    (`spectralIndex_thermal_mul_gt_one`). **Fourth falsification theorem:**
    `ObsData.not_fits_thermal_mul`. The linear cascade factor
    `G = (K/(K + m))²·exp(−Lσ(K))` is such a `G` (`cascadeG_monotoneOn`), since a healthy
    scalar coupled to the trace lowers the spatial potential for `c² ≤ 1/4`
    (`spatialCoeff_quarter_le_third`, `cascadeL_nonneg`). Instance:
    `ObsData.not_fits_cascade`.
  - **Any extension** (`Cascade.lean`). The converse: a fit of `C·M(k/s)·G(k/s′)` forces
    `d ln G/d ln k < n_s,hi − 1` at the pivot (`ObsData.Fits.factor_slope_lt`), so `G′ < 0`
    there (`ObsData.Fits.deriv_factor_neg`). For Planck 2018 the bound is `−0.0309`
    (`planck2018_factor_slope`). This names what a rescue of G1 must supply.
- [ ] **8.4 Golden values.** Evaluate the Lean definitions at fixed rational parameter points
  (`#eval` or `norm_num`). Use the results as test vectors for the numerical code (CLASS/CAMB
  modifications) in `TESTABILITY.md`, so the code and the proofs check the same formulas.

---

## Suggested order

| Order | Item | Why now |
|---|---|---|
| ✓ | M0.1–0.2 (audit, CI) | Done |
| ✓ | M2.1 (trivial instance) | Done |
| ✓ | M2.4 (acceleration equation) | Done; M2.5 (fields at `H = 0`) is a decision to take before M4 |
| ✓ | M1.1–1.6 | Done. Milestone 1 is complete |
| ✓ | M7.2 (falsification theorem) | Done |
| ✓ | M3.1, M3.3 | Done, against the TeX source |
| ✓ | M3.2 | Done |
| ✓ | M3.4 | Done |
| ✓ | M3.5 | Done (`docs/NOTE.md`) |
| ✓ | M5.1 (generic `f`) | Done (`GeneralBulk.lean`) |
| ✓ | M2.2 | Done in closed form (`Bounce.lean`) |
| ✓ | M4.1 | Done (`Dynamics.lean`) |
| ✓ | M2.5 | Done: the predicate `IsSolution` |
| ✓ | M4.2, first-order part | Done (`LocalExistence.lean`) |
| ✓ | M4.2, turning points | Done (`TurningPoint.lean`) |
| ✓ | M4.2, maximal solutions | Done (`MaximalSolution.lean`) |
| ✓ | M4.2, instance from a global solution | Done (`FromSolution.lean`) |
| ✓ | M2.3 | Done, negative (`NormalBranch.lean`) |
| ✓ | M4.3 | Done (`Horizon.lean`) |
| ✓ | M4.4 | Done (`Asymptotics.lean`) |
| ✓ | M5.2, M5.3 | Done (`AdSBulk.lean`, `ChargedBulk.lean`) |
| 8 | M8 | Grows alongside the testability pathways |
| ✓ | M7.1 | Done (`ThermalIntegral.lean`) |
| ✓ | M7.3 | Done for all `κ` (`SecondOrder.lean`, `BlueTilt.lean`) |
| 9 | M6 | Long-term foundations |
