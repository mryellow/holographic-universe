import HolographicUniverse.ObsData

/-!
# Scale invariance at leading order, and the first falsification theorem (ROADMAP M7.2)

The paper's power spectrum, Eq. (48), has the form `Δ²(k) = C · M(κ)` with `κ = k/(a_b T_b)`.
All the `k`-dependence is in `M`. At leading order `M(κ)` is replaced by `M(0)`, so the
spectrum does not depend on `k`, and the spectral index is exactly `n_s = 1`. Planck measures
`n_s < 1`. Sec. 5 of the paper says this rules out the simplest version of the model.

This file makes that argument a theorem, and a template for later tests:

* `spectralIndex P k = 1 + k P'(k) / P(k)`, i.e. `n_s - 1 = d ln P / d ln k`.
* `spectralIndex_powerLaw`: the definition gives `n` for `P = A (k/k₀)^(n-1)` (sanity check).
* `spectralIndex_comp`: for `P(k) = C · M(k/s)`, `n_s - 1 = κ M'(κ)/M(κ)`. The tilt has the sign
  of `M'(κ)`. This is the starting point for M7.3.
* `spectralIndex_const`, `spectralIndex_of_eventuallyEq`: a spectrum that is constant near the
  pivot has `n_s = 1`.
* `ObsData.Fits d P`: the spectrum `P` fits release `d` at the pivot, in both amplitude and
  `n_s` (1σ intervals).
* `ObsData.not_fits_of_locallyConst`: if `d.ns_hi < 1`, no spectrum that is constant near the
  pivot fits `d`.
* `leading_order_ruled_out_planck2013`, `leading_order_ruled_out_planck2018`: the leading-order
  spectrum of Eq. (48) fits neither release, for any value of `T_b/M₅`.
* `planck2013_ns_excludes_one`, `planck2018_ns_excludes_one`: `n_s = 1` is more than `5σ`
  (2013) and `8σ` (2018) from the central value, if the 1σ interval is read as a symmetric
  Gaussian error.

What is **not** proved: that the next-order terms cannot rescue the model. That is M7.3, and it
depends on the sign of `M'(κ)` at the pivot.
-/

namespace WhiteHole

open Real Filter Topology

/-- The scalar spectral index `n_s(k) = 1 + d ln P / d ln k = 1 + k P'(k)/P(k)`. -/
noncomputable def spectralIndex (P : ℝ → ℝ) (k : ℝ) : ℝ := 1 + k * deriv P k / P k

/-- **Sanity check.** The power law `P(k) = A (k/k₀)^(n-1)` has spectral index `n`. -/
theorem spectralIndex_powerLaw {A k0 n k : ℝ} (hA : A ≠ 0) (hk0 : 0 < k0) (hk : 0 < k) :
    spectralIndex (fun k ↦ A * (k / k0) ^ (n - 1)) k = n := by
  have hq : 0 < k / k0 := div_pos hk hk0
  have hd : HasDerivAt (fun k ↦ A * (k / k0) ^ (n - 1))
      (A * (k0⁻¹ * (n - 1) * (k / k0) ^ (n - 1 - 1))) k := by
    have := ((hasDerivAt_id k).div_const k0).rpow_const (p := n - 1) (Or.inl hq.ne')
    simpa using this.const_mul A
  rw [spectralIndex, hd.deriv, rpow_sub_one hq.ne']
  field_simp
  ring

/-- **The tilt of `C · M(k/s)`.** If `P(k) = C · M(k/s)`, then `n_s - 1 = κ M'(κ)/M(κ)` with
`κ = k/s`. So the spectrum is red (`n_s < 1`) exactly when `κ M'(κ)/M(κ) < 0`. -/
theorem spectralIndex_comp {C s k : ℝ} {M : ℝ → ℝ} (hC : C ≠ 0) (hs : s ≠ 0)
    (hM : DifferentiableAt ℝ M (k / s)) (hM0 : M (k / s) ≠ 0) :
    spectralIndex (fun k ↦ C * M (k / s)) k = 1 + k / s * deriv M (k / s) / M (k / s) := by
  have hd : HasDerivAt (fun k ↦ C * M (k / s)) (C * (deriv M (k / s) * (1 / s))) k := by
    have := hM.hasDerivAt.comp k ((hasDerivAt_id k).div_const s)
    simpa using this.const_mul C
  rw [spectralIndex, hd.deriv]
  field_simp

/-- **A constant spectrum has `n_s = 1`.** No condition on `A`. -/
theorem spectralIndex_const (A k : ℝ) : spectralIndex (fun _ ↦ A) k = 1 := by
  simp [spectralIndex]

/-- **A spectrum that is constant near `k` has `n_s(k) = 1`.** -/
theorem spectralIndex_of_eventuallyEq {P : ℝ → ℝ} {k : ℝ} (h : P =ᶠ[𝓝 k] fun _ ↦ P k) :
    spectralIndex P k = 1 := by
  rw [spectralIndex, h.deriv_eq]
  simp

/-- The leading-order spectrum of Eq. (48): `ampCoeff · (T_b/M₅)⁶` at every `k`. `eq48_leading`
shows that the first line of Eq. (48) with `M(κ) = M(0)` equals this, with no `k` in it. -/
noncomputable def leadingSpectrum (y : ℝ) : ℝ → ℝ := fun _ ↦ ampCoeff * y ^ 6

/-- **M7.2, scale invariance.** The leading-order spectrum has `n_s = 1` at every scale. -/
theorem leadingSpectrum_ns (y k : ℝ) : spectralIndex (leadingSpectrum y) k = 1 :=
  spectralIndex_const _ k

namespace ObsData

variable (d : ObsData)

/-- The spectrum `P` fits the data release `d` at the pivot scale: both the amplitude and the
spectral index lie in their 1σ intervals. -/
def Fits (P : ℝ → ℝ) : Prop :=
  (d.A_lo ≤ P d.kPivot ∧ P d.kPivot ≤ d.A_hi) ∧
    (d.ns_lo ≤ spectralIndex P d.kPivot ∧ spectralIndex P d.kPivot ≤ d.ns_hi)

/-- **Falsification template.** If the release puts `n_s` strictly below `1`, then no spectrum
that is constant near the pivot fits it. -/
theorem not_fits_of_locallyConst (hns : d.ns_hi < 1) {P : ℝ → ℝ}
    (hP : P =ᶠ[𝓝 d.kPivot] fun _ ↦ P d.kPivot) : ¬ d.Fits P := by
  rintro ⟨-, -, h⟩
  rw [spectralIndex_of_eventuallyEq hP] at h
  linarith

/-- **The leading-order spectrum fits no release with `n_s < 1`.** -/
theorem not_fits_leadingSpectrum (hns : d.ns_hi < 1) (y : ℝ) : ¬ d.Fits (leadingSpectrum y) :=
  d.not_fits_of_locallyConst hns (.of_eq rfl)

/-- `n_s = 1` lies more than `s` standard deviations above the central value, if the interval
`[ns_lo, ns_hi]` is read as `central ± 1σ`. -/
def NsExcludesOne (s : ℝ) : Prop := s * ((d.ns_hi - d.ns_lo) / 2) < 1 - (d.ns_lo + d.ns_hi) / 2

end ObsData

/-- **First falsification theorem, Planck 2013.** For no value of `T_b/M₅` does the leading-order
spectrum of Eq. (48) fit the Planck 2013 data. -/
theorem leading_order_ruled_out_planck2013 (y : ℝ) : ¬ planck2013.Fits (leadingSpectrum y) :=
  planck2013.not_fits_leadingSpectrum (by norm_num [planck2013]) y

/-- **First falsification theorem, Planck 2018.** -/
theorem leading_order_ruled_out_planck2018 (y : ℝ) : ¬ planck2018.Fits (leadingSpectrum y) :=
  planck2018.not_fits_leadingSpectrum (by norm_num [planck2018]) y

/-- Planck 2013 (`n_s = 0.9603 ± 0.0073`) puts `n_s = 1` more than `5σ` away, as the paper says. -/
theorem planck2013_ns_excludes_one : planck2013.NsExcludesOne 5 := by
  norm_num [ObsData.NsExcludesOne, planck2013]

/-- Planck 2018 (`n_s = 0.9649 ± 0.0042`) puts `n_s = 1` more than `8σ` away. -/
theorem planck2018_ns_excludes_one : planck2018.NsExcludesOne 8 := by
  norm_num [ObsData.NsExcludesOne, planck2018]

end WhiteHole
