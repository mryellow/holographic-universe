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
| Observational bounds (Eqs. 33–35) | proved (Eq. 35 with fewer hypotheses than stated) |
| Leading-order amplitude (Eq. 48), `T_b/M₅` (Eq. 49), `M₅` bound (Eq. 51) | proved, with `M(0) = 15ζ(5)/π²` as the only remaining hypothesis. The integral, `ζ(5)` and the coefficient range are proved (`Integrals.lean`, `Zeta.lean`, `ampCoeff_bounds`) |
| Brane geometry, Brown–York, Gauss–Codazzi (Eqs. 3–10), Friedmann (11) | **assumed** |
| Extrinsic curvature of the embedding (Eqs. 21–25) | **assumed** |
| Thermal correlators (Eqs. 39–47) | **assumed** |
| Eqs. (50)–(52) (Hubble, `M₅` and temperature bounds) | proved (`Monopoles.lean`), with `H₀`, `G_N`, the condition `H ≤ 2πT_b` and the radiation-era Friedmann equation as hypotheses |
| Normal orientation `ε` (Eqs. 21, 24, 25, 27) | resolved against the TeX source (`Orientation.lean`): `ε` is fixed by the sign of `ρ̃`, not by Eq. (27) |
| Non-vacuity (does any `BraneCosmology` exist?) | proved (`Instances.lean`): a static family for both `ε = ±1` and any `r_h` outside the brane, and the self-accelerating de Sitter vacuum. An expanding instance with `r_h > 0` and matter is still **open** |
| Axiom audit | enforced at build time (`Audit.lean`) |
| Acceleration equation | **derived** wherever `H ≠ 0`, with no smoothness assumption beyond the structure (`Acceleration.lean`). Not implied at `H = 0`: the static instances violate it |

The formalization has surfaced five issues: the Eq. (24) typo, Eq. (27) being wrong for
`ε = +1`, the paper's too-strong `ε = -1` (which caused the apparent normal-branch tension,
now resolved), the missing acceleration equation in `BraneCosmology` (M2.4), and a dimension
error in Eq. (52). See the README for details. The TeX source of arXiv:1309.1487v2 was checked
for issues 1–3 and 5. It is not committed: arXiv's default licence does not allow
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
  equation number. (Kept in sync by hand so far.)

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
- [ ] **2.2 Non-trivial instance.** Build an instance with `r_h > 0` and dust or radiation
  matter. Expect to need Milestone 4 (ODE existence) unless a closed-form solution exists for a
  special equation of state.
- [ ] **2.3 Consistency of the sign convention.** Show that the instance from 2.2 can have
  `ε = -1` on the normal branch. If it cannot, that is a sharp form of issue 3.
  Partial result: `exists_normal_branch_eps_neg` gives a *static* instance with `ε = -1`,
  `r_h > 0`, `ρ > 0`, `ρ̃ > 0` on the normal branch (with `ρ < ρ_BH`, as
  `normal_branch_requires` demands). So the fields alone do not exclude it. The expanding case
  is still open.
- [x] **2.4 Acceleration equation.** Done in `Acceleration.lean`:
  - `accel_of_friedmann`, `BraneCosmology.accelAt_of_ne`: Friedmann + continuity imply
    `ä/a = -(4πG_N/3)(ρ + ρ̃ + 3(P + P̃))` wherever `H ≠ 0`.
  - `differentiableAt_deriv_of_sq_eq`: `ä` exists wherever `H ≠ 0`. This did not need a new
    hypothesis. `ȧ² = g` with `g` differentiable, and Darboux's theorem fixes the sign of `ȧ`
    locally, so `ȧ = ±√g`.
  - `static_not_accelAt`: at `H = 0` the equation is **not** implied. Every static instance
    violates it (`ä = 0`, right side `-𝒦/2`).
  - `deSitter_accelAt`: the de Sitter vacuum satisfies it at all times, bounce included.
- [ ] **2.5 Decision: the equations at `H = 0`.** The structure now has a predicate
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
- [ ] **3.2 Time dependence of `ρ_BH/ρ`.** `ρ_BH ∝ a⁻⁴` is already proved. Prove that
  `ρ_BH/ρ` is constant in a radiation era (`ρ ∝ a⁻⁴`) and falls as `1/a` in a matter era
  (`ρ ∝ a⁻³`). Then combine with 3.1: a cosmology can move between regions over time, so the
  consistency condition has to hold along the whole history, not just at one instant.
- [x] **3.3 Eq. (27) at `ε = +1`.** Eq. (27) is wrong as printed for `ε = +1`.
  `pressure_of_timelike_junction`: Eq. (25) set equal to the `ττ` part of Eq. (10) gives
  Eq. (16) for either `ε`, once `X = -ε(8πG_b/3)ρ̃` is used. `eq27_of_dropped_sign`: Eq. (27) is
  what the same step gives with `X = +(8πG_b/3)ρ̃`, which is true only for `ε = -1`.
- [ ] **3.4 Pressure singularity.** Prove that `ρ̃ = ρ̃_s` holds exactly when the reality bound
  (30) is saturated, `2(ρ_BH - ρ) = ρ̃_s`. This is the point where the two branches meet. The
  paper argues that the singularity always lies inside the white-hole horizon (Sec. 5). Formalize
  that claim with `outside_horizon_iff`.
- [ ] **3.5 Write-up.** Collect 3.1–3.4 in a short note. Contacting the authors is optional
  and is the user's decision.

## Milestone 4: Dynamics

Turns the algebraic constraints into statements about whole histories.

- [ ] **4.1 Reduction to an ODE.** For a barotropic fluid `P = wρ`, use `ρ = ρ₀a^{-3(1+w)}`
  and the chosen branch of Eq. (26) to reduce `BraneCosmology` to a first-order autonomous ODE
  for `a(t)`.
- [ ] **4.2 Local existence and uniqueness.** Use Mathlib's Picard–Lindelöf
  (`Analysis/ODE/PicardLindelof.lean`, `Analysis/ODE/ExistUnique.lean`) away from `H = 0` and
  from the pressure singularity. Feeds Milestone 2.2. At `H = 0` the first-order equation is
  not enough (see M2.5): use the second-order acceleration equation there.
- [ ] **4.3 Horizon-crossing time.** Prove there is a `t*` with `a(t*)/√𝒦 = r_h`, and that it
  is unique while the brane is expanding. This is the moment the universe "leaves the white
  hole".
- [ ] **4.4 Asymptotics.** Late times: on the self-accelerating branch `H → 1/r_c` (de Sitter).
  On the normal branch, recover standard FRW when `ρ ≫ ρ̃_s`. Early times: behavior near the
  singularity.

## Milestone 5: Generalize the bulk

Needed by several testability pathways (curvature with anisotropy, AdS embedding).

- [ ] **5.1 Generic blackening factor.** Refactor `Bulk.lean` and `InducedFluid.lean` so that
  the theorems take any `f : ℝ → ℝ`, and recover the current results for `f = 1 - r_h²/r²`.
  Most proofs only use `f` through `curv_mul_blacken`.
- [ ] **5.2 Schwarzschild–AdS₅.** `f = 1 + r²/L² - r_h²/r²`. The paper says the results "need
  not significantly change" (Sec. 5). Prove that, or state precisely how they change.
- [ ] **5.3 Charged bulk (Reissner–Nordström).** `f = 1 - r_h²/r² + q²/r⁴`. This adds a
  `∝ a⁻⁶` term, which BBN can bound.

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

- [ ] **7.1 `M(0) = 15ζ(5)/π²`.** Define `M(κ)` as the integral in the paper. The value at
  zero needs the Bose–Einstein integral `∫₀^∞ x^{s-1}/(eˣ-1) dx = Γ(s)ζ(s)`. Check whether
  Mathlib has it; if not, prove it with a geometric series and the Gamma integral.
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
  - Not proved: that next-order terms cannot rescue the model (M7.3).
- [ ] **7.3 Next-order term.** Find the sign and size of the `O((k/a_bT_b)²)` correction in
  Eq. (48). Show whether it can produce `n_s < 1` at CMB scales. (Expect not: it is
  `k²`-suppressed, so it would tilt blue at large `k`.)
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
| 5 | M3.2, M3.4 | `BraneCosmology.normal_branch_no_crossing` already gives the history condition for 3.2. 3.2 adds the era-by-era behaviour of `ρ_BH/ρ` |
| 6 | M5.1 (generic `f`) | Refactor before more theorems depend on the concrete `f` |
| 7 | M4, M2.2 | Real solutions; needed for histories and BBN-era statements |
| 8 | M8 | Grows alongside the testability pathways |
| 9 | M6, M7.1 | Long-term foundations |
