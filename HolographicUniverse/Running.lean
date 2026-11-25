module

public import HolographicUniverse.ScaleInvariance

@[expose] public section

/-!
# No local, static extension gives the observed tilt (P4)

The paper imprints every mode at one moment: the brane's static equilibrium with its thermal
atmosphere, at `(a_b, T_b)` (Sec. 4). A cooling atmosphere then changes only the amplitude, not
the shape. Within that mechanism, an extension changes the shape through physics with some scale
`s` (a Jeans length, a crossover scale, a correlation length). If that physics is local, the
spectrum is analytic in `k²` near `k = 0`. Near the pivot, the tilt is then a sum of power laws

  `n_s(k) − 1 = Σᵢ cᵢ (k/sᵢ)^{pᵢ}`,   with `pᵢ = 2, 4, …` (`powerTilt`).

The thermal spectrum itself is one such term: blue, `p = 2` (`spectralIndex_thermal_gt_one`,
`SecondOrder.lean`). P1 and P2 were two choices of the other terms.

* `runningIndex P k = k · d n_s/dk`, i.e. `α_s = d n_s / d ln k`.
* `runningIndex_of_tilt`: if the tilt is `Σᵢ cᵢ (k/sᵢ)^{pᵢ}` near `k`, then
  `α_s = Σᵢ pᵢ cᵢ (k/sᵢ)^{pᵢ}`. One term gives `α_s = p (n_s − 1)` exactly.
* `runningIndex_le_of_tilt`: if every red term (`cᵢ < 0`) has `pᵢ ≥ q` and every blue term
  (`cᵢ > 0`) has `pᵢ ≤ q`, then `α_s ≤ q (n_s − 1)`. This generalizes P1's
  `α_s/(n_s − 1) ≥ 2`.
* `RunningData`, `RunningData.Fits`: a release that fits `n_s` and its running together.
  `planck2018Running` is Planck 2018 VI, ΛCDM + `dn_s/d ln k`, TT,TE,EE+lowE+lensing:
  `n_s = 0.9641 ± 0.0044`, `α_s = −0.0045 ± 0.0067`.
* `RunningData.not_fits_of_tilt`: no such spectrum fits if `q (n_s,hi − 1) < α_s,lo`.
* `planck2018Running_not_fits_tilt`: for Planck 2018, every `q ≥ 0.36` is excluded. **The data
  need the red part of the tilt to be nearly scale free.**
* `planck2018Running_not_fits_local`: `q = 2`, the local case. A fit at the observed `n_s` would
  need `α_s ≤ −0.063`, against `−0.0045 ± 0.0067` (8.7σ).

**What is assumed** (as hypotheses): the form of the tilt near the pivot, and the sign
condition. The form is the physics input. It is exact for a finite sum of power laws, and the
leading behaviour of any spectrum analytic in `k²`. The thermal term enters at its leading order
`∝ κ²`.

**What is not covered.** A tilt whose terms break the sign condition: a red term with `p < q`,
or a blue term with `p > q`. In the local case this is a red `k²` term cancelled by a blue `k⁴`
term, so `α_s = 0` at the pivot because the tilt has an extremum there. That is a feature tuned
to the pivot, like P1's window. Two routes leave the class entirely:
1. modes imprinted at different times (for example at horizon exit), which replaces the paper's
   single static equilibrium;
2. scale-free, long-range correlations in the atmosphere (a power `p ≈ 0`, an anomalous
   dimension), which local physics does not give.
-/

namespace WhiteHole

open Real Filter Topology

/-- The running of the spectral index, `α_s(k) = d n_s / d ln k = k · n_s′(k)`. -/
noncomputable def runningIndex (P : ℝ → ℝ) (k : ℝ) : ℝ := k * deriv (spectralIndex P) k

/-- A tilt that is a finite sum of power laws, `Σᵢ cᵢ (k/sᵢ)^{pᵢ}`. -/
noncomputable def powerTilt {ι : Type*} (S : Finset ι) (c s p : ι → ℝ) (k : ℝ) : ℝ :=
  ∑ i ∈ S, c i * (k / s i) ^ p i

/-- `k · d/dk (k/s)^p = p (k/s)^p`. -/
theorem hasDerivAt_div_rpow {s p k : ℝ} (hs : 0 < s) (hk : 0 < k) :
    HasDerivAt (fun k ↦ (k / s) ^ p) (p * (k / s) ^ p / k) k := by
  have hks : k / s ≠ 0 := (div_pos hk hs).ne'
  have h : HasDerivAt (fun k ↦ (k / s) ^ p) (1 / s * p * (k / s) ^ (p - 1)) k :=
    ((hasDerivAt_id' k).div_const s).rpow_const (Or.inl hks)
  convert h using 1
  rw [rpow_sub_one hks]
  field_simp

/-- **The running of a power-law tilt.** `α_s = Σᵢ pᵢ cᵢ (k/sᵢ)^{pᵢ}`. -/
theorem runningIndex_of_tilt {ι : Type*} {S : Finset ι} {c s p : ι → ℝ} {P : ℝ → ℝ} {k : ℝ}
    (hs : ∀ i ∈ S, 0 < s i) (hk : 0 < k)
    (hP : spectralIndex P =ᶠ[𝓝 k] fun k ↦ 1 + powerTilt S c s p k) :
    runningIndex P k = ∑ i ∈ S, p i * (c i * (k / s i) ^ p i) := by
  have hd : HasDerivAt (fun k ↦ 1 + powerTilt S c s p k)
      (∑ i ∈ S, c i * (p i * (k / s i) ^ p i / k)) k := by
    unfold powerTilt
    refine (HasDerivAt.fun_sum fun i hi ↦ ?_).const_add 1
    exact (hasDerivAt_div_rpow (hs i hi) hk).const_mul (c i)
  rw [runningIndex, hP.deriv_eq, hd.deriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  field_simp

/-- **Steep red terms make the running at least as red as the tilt.** If every term has
`(pᵢ − q) cᵢ ≤ 0`, then `α_s ≤ q (n_s − 1)`. -/
theorem runningIndex_le_of_tilt {ι : Type*} {S : Finset ι} {c s p : ι → ℝ} {P : ℝ → ℝ}
    {k q : ℝ} (hs : ∀ i ∈ S, 0 < s i) (hk : 0 < k) (hsign : ∀ i ∈ S, (p i - q) * c i ≤ 0)
    (hP : spectralIndex P =ᶠ[𝓝 k] fun k ↦ 1 + powerTilt S c s p k) :
    runningIndex P k ≤ q * (spectralIndex P k - 1) := by
  rw [runningIndex_of_tilt hs hk hP, hP.eq_of_nhds, powerTilt, add_sub_cancel_left,
    Finset.mul_sum, ← sub_nonpos, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun i hi ↦ ?_
  have hx : 0 ≤ (k / s i) ^ p i := rpow_nonneg (div_pos hk (hs i hi)).le _
  have := mul_nonpos_of_nonpos_of_nonneg (hsign i hi) hx
  linarith

/-! ### Data with running -/

/-- `n_s` and its running from a fit that lets both vary, at one pivot (1σ intervals). The
amplitude plays no role here. -/
structure RunningData where
  /-- Pivot scale, in `Mpc⁻¹`. -/
  kPivot : ℝ
  /-- `n_s`: lower end. -/
  ns_lo : ℝ
  /-- `n_s`: upper end. -/
  ns_hi : ℝ
  /-- `α_s = dn_s/d ln k`: lower end. -/
  as_lo : ℝ
  /-- `α_s`: upper end. -/
  as_hi : ℝ
  kPivot_pos : 0 < kPivot
  ns_le : ns_lo ≤ ns_hi
  as_le : as_lo ≤ as_hi

namespace RunningData

variable (d : RunningData)

/-- The spectrum `P` fits `n_s` and `α_s` at the pivot. -/
def Fits (P : ℝ → ℝ) : Prop :=
  (d.ns_lo ≤ spectralIndex P d.kPivot ∧ spectralIndex P d.kPivot ≤ d.ns_hi) ∧
    (d.as_lo ≤ runningIndex P d.kPivot ∧ runningIndex P d.kPivot ≤ d.as_hi)

/-- **No-go for power-law tilts.** If `q (n_s,hi − 1) < α_s,lo`, no spectrum whose tilt near the
pivot is a sum of power laws with `(pᵢ − q) cᵢ ≤ 0` fits. -/
theorem not_fits_of_tilt {ι : Type*} {S : Finset ι} {c s p : ι → ℝ} {P : ℝ → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q * (d.ns_hi - 1) < d.as_lo) (hs : ∀ i ∈ S, 0 < s i)
    (hsign : ∀ i ∈ S, (p i - q) * c i ≤ 0)
    (hP : spectralIndex P =ᶠ[𝓝 d.kPivot] fun k ↦ 1 + powerTilt S c s p k) : ¬ d.Fits P := by
  rintro ⟨⟨-, hns⟩, ⟨has, -⟩⟩
  have h := runningIndex_le_of_tilt hs d.kPivot_pos hsign hP
  have := mul_le_mul_of_nonneg_left (sub_le_sub_right hns 1) hq0
  linarith

end RunningData

/-- **Planck 2018 with running** (VI, arXiv:1807.06209, ΛCDM + `dn_s/d ln k`,
TT,TE,EE+lowE+lensing): `n_s = 0.9641 ± 0.0044`, `dn_s/d ln k = −0.0045 ± 0.0067`, pivot
`0.05 Mpc⁻¹`. -/
noncomputable def planck2018Running : RunningData where
  kPivot := 0.05
  ns_lo := 0.9597
  ns_hi := 0.9685
  as_lo := -0.0112
  as_hi := 0.0022
  kPivot_pos := by norm_num
  ns_le := by norm_num
  as_le := by norm_num

/-- **Planck 2018 needs a nearly scale-free red tilt.** Every `q ≥ 0.36` is excluded: no tilt
with red terms of power `≥ q` and blue terms of power `≤ q` fits. -/
theorem planck2018Running_not_fits_tilt {ι : Type*} {S : Finset ι} {c s p : ι → ℝ}
    {P : ℝ → ℝ} {q : ℝ} (hq : 0.36 ≤ q) (hs : ∀ i ∈ S, 0 < s i)
    (hsign : ∀ i ∈ S, (p i - q) * c i ≤ 0)
    (hP : spectralIndex P =ᶠ[𝓝 planck2018Running.kPivot] fun k ↦ 1 + powerTilt S c s p k) :
    ¬ planck2018Running.Fits P :=
  planck2018Running.not_fits_of_tilt (by linarith) (by norm_num [planck2018Running]; linarith)
    hs hsign hP

/-- **Local extensions, Planck 2018.** Red terms with `pᵢ ≥ 2` (any local physics) and blue terms
with `pᵢ ≤ 2` (the thermal `κ²` term) never fit. A fit to `n_s` alone would force
`α_s ≤ 2 (n_s − 1) ≤ −0.063`. -/
theorem planck2018Running_not_fits_local {ι : Type*} {S : Finset ι} {c s p : ι → ℝ}
    {P : ℝ → ℝ} (hs : ∀ i ∈ S, 0 < s i) (hsign : ∀ i ∈ S, (p i - 2) * c i ≤ 0)
    (hP : spectralIndex P =ᶠ[𝓝 planck2018Running.kPivot] fun k ↦ 1 + powerTilt S c s p k) :
    ¬ planck2018Running.Fits P :=
  planck2018Running_not_fits_tilt (by norm_num) hs hsign hP

/-- **The local running bound at the observed tilt.** With `n_s ≤ 0.9685`, a local tilt has
`α_s ≤ −0.063`. -/
theorem runningIndex_le_local_planck2018 {ι : Type*} {S : Finset ι} {c s p : ι → ℝ}
    {P : ℝ → ℝ} (hs : ∀ i ∈ S, 0 < s i) (hsign : ∀ i ∈ S, (p i - 2) * c i ≤ 0)
    (hP : spectralIndex P =ᶠ[𝓝 planck2018Running.kPivot] fun k ↦ 1 + powerTilt S c s p k)
    (hns : spectralIndex P planck2018Running.kPivot ≤ planck2018Running.ns_hi) :
    runningIndex P planck2018Running.kPivot ≤ -0.063 := by
  have h := runningIndex_le_of_tilt hs planck2018Running.kPivot_pos hsign hP
  norm_num [planck2018Running] at hns h ⊢
  linarith

end WhiteHole
