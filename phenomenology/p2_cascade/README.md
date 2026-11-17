# P2: red tilt from cascading gravity

Pathway P2 of [`docs/TESTABILITY.md`](../../docs/TESTABILITY.md). Sec. 5 of the paper argues
that a red tilt means "the amplitude of 5D bulk graviton propagator, which enters in
Eq. (43), is getting stronger in the IR". It proposes cascading gravity (de Rham et al.,
arXiv:0711.2072) as the mechanism. In that model the 5D bulk is a 4-brane in a 6D bulk. Above
the length `M₅³/M₆⁴`, the scalar for the 4-brane's motion in 6D becomes weakly coupled and
"boosts the strength of the gravitational exchange amplitude". This note checks that claim at
linear order, for the paper's own observable. Run the numbers with

```bash
cd phenomenology && uv run python p2_cascade/cascade_tilt.py
```

**Result.** In its linear form, P2 does not pass gate G1. The boost is real for the Newtonian
potential `g₀₀`, but the paper's curvature perturbation is the spatial potential: `ζ = -Φ₄` is
read off `g_ab` (Eqs. 42, 47). For that potential the extra polarization adds nothing for
radiation and makes it weaker for any other gas. The 6D propagator also weakens gravity in the
infrared. Both effects are blue, so with `M7.3` the brane spectrum has `n_s > 1` at every scale,
for every `M₆`. The mechanism has the wrong sign. It is not a matter of the wrong size.

## 1. Linear cascading gravity for bulk sources

Static sources in the 5D bulk, with 4D spatial wavenumber `K`. Write the linear metric response
as

  `h_μν = 16πG_b · [δT_μν − λ η_μν δT] / (K² + mK)`  (up to gauge terms `∝ K_μK_ν`),

with `δT = η^{μν}δT_μν`.

- **5D general relativity:** `m = 0`, `λ = 1/(D − 2) = 1/3`.
- **Cascading gravity (4-brane in 6D):** the 4-brane is a codimension-1 DGP brane in 6D.
  - The propagator picks up the DGP form `1/(K² + mK)`, with `m ∼ M₆⁴/M₅³`. The force between
    bulk sources goes from `1/r³` to `1/r⁴` beyond `1/m`, as in the cascade
    `1/r² → 1/r³ → 1/r⁴` of de Rham, Hofmann, Khoury, Tolley (arXiv:0712.2821).
  - The brane-bending scalar couples to `δT` and turns the tensor structure into that of a
    massive 5D graviton, `λ = 1/(D − 1) = 1/4`. This is the vDVZ structure of DGP, one
    dimension up.
  - Vainshtein screening switches the scalar off near dense sources. That restores `λ = 1/3` at
    large `K`.

The scalar's whole contribution is the change of `λ`, which is `+(1/12)η_μν δT`. It is
proportional to the trace.

## 2. Which potential is ζ

The paper's metric is `g₀₀ = -(1 + 4Φ₄)`, `g_ab = (1 − 2Φ₄)δ_ab` (Eq. 42). In 5D GR the two
potentials are locked together, `h₀₀ = 2h₁₁`. The paper then computes `Φ₄` from the
Poisson equation for `g₀₀` and sets `ζ = -Φ₄` by matching the *spatial* metric (Eq. 47). With
`λ ≠ 1/3` the two potentials separate, and `ζ` follows `g_ab`.

For a fluid with `δp = c²δρ` in 4 space dimensions, `δT = -(1 − 4c²)δρ`. Per unit
`16πG_b δρ/(K² + mK)`:

| | massless (`λ = 1/3`) | massive (`λ = 1/4`) | ratio massive/massless |
|---|---|---|---|
| Newtonian, `h₀₀` | `1 − (1 − 4c²)/3` | `1 − (1 − 4c²)/4` | `≥ 1`: `9/8` for dust, `1` for radiation |
| spatial, `h_ab ∝ ζ` | `(1 − c²)/3` | `1/4` | `3/(4(1 − c²)) ≤ 1`: `3/4` for dust, `1` for radiation |

The paper's atmosphere is radiation in 4 space dimensions (`c² = 1/4`, `δT = 0`): the scalar
does not couple to it at all. For any gas with `ρ ≥ 4p` (`0 ≤ c² ≤ 1/4`), the scalar makes `ζ`
smaller. The boost the paper describes is the one that N-body work on cascading gravity sees in
structure growth (arXiv:0903.1292). It drives `g₀₀`, not `ζ`.

## 3. The brane spectrum

Relative to 5D GR, the 4D power of `ζ` is multiplied by

  `G(K) = (K/(K + m))² · r(c²)^{2s(K)}`,  `r = 3/(4(1 − c²)) ≤ 1`,

where `s(K)` runs from 1 (unscreened, small `K`) to 0 (screened, large `K`). Both factors are
nondecreasing in `K`. With Eq. (48) the brane spectrum is

  `Δ²_ζ(k) ∝ ∫ dx (1 + x²)⁻² G(k√(1 + x²)) M(k√(1 + x²)/T)`.

`M` is strictly increasing (`thermalM_lt_of_norm_lt`), and `G` is nondecreasing. So the
integrand increases with `k` at every `x`, and `n_s > 1` at every `k`, whatever `m`, `M₆`, `c²`
and the screening profile. The script checks this numerically. It finds `n_s − 1 > 0` over
`c² ∈ {0, 1/4}`, `m/K_V ∈ [0, 10]`, screening profiles `s = 1/(1 + (K/K_V)^q)` with
`q ∈ [0.5, 3]`, and six decades of `k`. For the radiation atmosphere with `m` near the pivot,
`n_s − 1` is of order 1: strongly blue.

## 4. What an infrared boost would have to look like

Part B of the script is a counterfactual. Suppose `ζ` *were* boosted like the dust Newtonian
potential, by `F = exp(B/(1 + (K/K_V)^q))` with `B ≤ 2 ln(9/8) = 0.236`. What fits Planck? This
is a guide for any future extension that strengthens the propagator in the infrared.

**Exact.** `d ln F/d ln K = −Bq·u/(1 + u)²` with `u = (K/K_V)^q`. The brane tilt is a weighted
average of this, so `|n_s − 1| ≤ Bq/4`. On the tails of the transition, `α_s/(n_s − 1) → ∓q`.
In general, a feature whose log-amplitude goes as a power `k^{±q}` gives `|α_s/(n_s − 1)| = q`
there. Planck at 2σ allows `α_s/(n_s − 1)` only in `[−0.33, 0.67]`. So the pivot must sit near
the centre of a broad transition.

**Numerics.** These require the joint `(n_s, α_s)` test at 2σ, plus `ln P(0.1)/P(0.008)` and
`β_s` within 2σ, both approximate as in P1.

| `q` | least `B` for `n_s = 0.965` | passing `k_V` (Mpc⁻¹) |
|---|---|---|
| 0.5 | 0.28 (2σ edge only) | 0.018 – 0.091 |
| 0.75 | 0.19 | 0.015 – 0.22 |
| 1 | 0.14 | 0.032 – 0.19 |
| 1.5 | 0.09 | 0.043 – 0.078 |
| 2, 3 | — | none |

So an infrared boost of the right sign could fit if three things hold:
- it is broad (`q ≲ 1.5`);
- it is large (`B ≳ 0.1`, a sizeable fraction of the largest dust boost);
- it is centred within a factor of about 3 of the pivot.

The sharp onset of Vainshtein screening does not qualify. For a point source in `d` space
dimensions the unscreened scalar force goes as `(r/r_V)^{d/2}`, which gives `q = 2` for `d = 4`.
This exponent is an estimate from the cubic-galileon decoupling limit, not a computation for the
thermal atmosphere.

## 5. Verdict for G1

At linear order, cascading gravity makes the paper's `ζ` weaker in the infrared, not stronger.
Two things cause this. The 6D propagator softens. The extra polarization couples only to the
stress-tensor trace, which vanishes for the radiation atmosphere and lowers `ζ` for any other
gas with `ρ ≥ 4p`. The result is a blue spectrum at every scale for every `M₆`. **P2 in this
form is ruled out**, and the reason is the sign. That is stronger than P1, which failed on shape.

## 6. Assumptions

What could change the verdict, in order of importance:

1. **The scalar is healthy.** A ghost brane-bending mode flips the sign of the `+(1/12)η_μν δT`
   term and would boost `ζ` for `ρ > 4p`. The self-accelerating branch has such a ghost, and the
   paper excises it (Sec. 5). Cascading gravity is ghost-free only with enough 3-brane tension
   (arXiv:1002.1075).
2. **`ρ ≥ 4p`.** A stiff atmosphere (`c² > 1/4`, `δT > 0`) would be boosted. That needs matter
   other than a thermal gas of free particles.
3. **`ζ = −Φ₄` read off the spatial metric.** This is the paper's Eq. (47). If the correct
   brane observable mixed in `g₀₀` (for example through the comoving gauge, or the 3-brane's own
   induced gravity), the dust-like boost of Part B would become relevant. The atmosphere is
   radiation, though, and for radiation both potentials are unchanged.
4. **Linear theory.** The Vainshtein profile `s(K)` is a model. The argument uses only
   `0 ≤ s ≤ 1` and that `s` decreases with `K`. The second condition would fail only if screening
   were *weaker* at short distances.
5. **The 3-brane is a probe** for bulk sources at these scales, as in the paper's Eq. (48).
6. **The tensor structure of the cascade.** `λ = 1/4` is the codimension-1 DGP result for the
   4-brane in 6D, which is the regime the paper invokes. Any healthy scalar that couples to `δT`
   gives the same sign.

## 7. Lean (M8, `Cascade.lean`)

Sections 2 and 3 are proved, with `G` taken as a definition (the physics input of this note):

- `spectralIndex_mul`: `n_s(P·G) − 1 = (n_s(P) − 1) + (n_s(G) − 1)`.
- `spectralIndex_thermal_mul_gt_one`: `C·M(k/s)·G(k/s′)` has `n_s > 1` at every `k > 0` for any
  positive, differentiable `G` that is nondecreasing on `(0, ∞)`.
- `ObsData.not_fits_thermal_mul`: **fourth falsification theorem.** No such spectrum fits a
  release with `n_s < 1`.
- `spatialCoeff_le_of_le`, `spatialCoeff_quarter_le_third`, `newtonCoeff_third_le_quarter`,
  `spatialCoeff_radiation`, `coeff_dust`: the table of Sec. 2. `cascadeL_nonneg`: `L ≥ 0`.
- `cascadeG_monotoneOn`, `ObsData.not_fits_cascade`: the instance
  `G = (K/(K + m))²·exp(−Lσ(K))`, for every `m ≥ 0`, `L ≥ 0` and differentiable antitone `σ`.

As in the earlier files, the Lean spectrum is `C·M(k/s)` times the factor. The projection
integral over `x` is not formalized. It preserves the conclusion because the integrand increases
with `k` pointwise (Sec. 3).

Still open: the Part B bounds `|n_s − 1| ≤ Bq/4` and `α_s/(n_s − 1) → ∓q`. These are
one-variable calculus.
