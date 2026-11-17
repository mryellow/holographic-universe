import HolographicUniverse.Running

/-!
# P2, Part B: what an infrared boost would have to look like

Linear cascading gravity weakens `ζ` in the infrared (`Cascade.lean`), so P2 fails on the sign.
Part B of the P2 note (`phenomenology/p2_cascade/`, Sec. 4) asks the counterfactual: suppose
some extension *did* boost `ζ` in the infrared, by a smooth step

  `F(K) = C · exp(B/(1 + u))`,  `u = (K/K_V)^q`  (`boostSpectrum`).

What tilt and running does that give? This file proves the exact statements of that section,
for the unprojected spectrum:

* `spectralIndex_boost`: `n_s − 1 = −Bq·u/(1 + u)²` (`boostTilt`).
* `abs_boostTilt_le`: `|n_s − 1| ≤ |B|q/4`. The step can tilt the spectrum by at most a
  quarter of `Bq`, at its centre `u = 1`.
* `runningIndex_boost`: `α_s = q(1 − u)/(1 + u) · (n_s − 1)`, exactly. On the infrared tail
  (`u → 0`) the ratio `α_s/(n_s − 1)` tends to `q`, on the ultraviolet tail (`u → ∞`) to `−q`,
  and it vanishes only at the centre.
* `abs_runningIndex_boost_le`: `|α_s| ≤ q|n_s − 1|`.

With `planck2018Running_not_fits_tilt`, a tail of a step with `q ≥ 0.36` does not fit Planck
2018: the pivot must sit near the centre of a broad step. The numerical table of the P2 note
(which `q`, `B` and `K_V` pass) is not formalized.
-/

namespace WhiteHole

open Real Filter Topology

/-- A smooth infrared boost `C · exp(B/(1 + (K/K_V)^q))`. -/
noncomputable def boostSpectrum (C B q KV : ℝ) (K : ℝ) : ℝ := C * exp (B / (1 + (K / KV) ^ q))

/-- Its tilt, `n_s − 1 = −Bq·u/(1 + u)²` with `u = (K/K_V)^q`. -/
noncomputable def boostTilt (B q KV : ℝ) (K : ℝ) : ℝ :=
  -(B * q * (K / KV) ^ q / (1 + (K / KV) ^ q) ^ 2)

/-- **The tilt of a step.** `n_s − 1 = −Bq·u/(1 + u)²`. -/
theorem spectralIndex_boost {C B q KV K : ℝ} (hC : C ≠ 0) (hKV : 0 < KV) (hK : 0 < K) :
    spectralIndex (boostSpectrum C B q KV) K = 1 + boostTilt B q KV K := by
  have hu : 0 ≤ (K / KV) ^ q := rpow_nonneg (div_pos hK hKV).le _
  have h1 : (1 + (K / KV) ^ q) ≠ 0 := by positivity
  have hd : HasDerivAt (boostSpectrum C B q KV)
      (C * (exp (B / (1 + (K / KV) ^ q)) *
        (-(B * (q * (K / KV) ^ q / K)) / (1 + (K / KV) ^ q) ^ 2))) K := by
    have h := ((((hasDerivAt_div_rpow (p := q) hKV hK).const_add 1).inv h1).const_mul B).exp
      |>.const_mul C
    convert h using 1
    · ext x
      simp [boostSpectrum, div_eq_mul_inv]
    · simp only [Pi.inv_apply, ← div_eq_mul_inv]
      field_simp
  rw [spectralIndex, hd.deriv, boostTilt, boostSpectrum]
  have he := (exp_pos (B / (1 + (K / KV) ^ q))).ne'
  have hK0 := hK.ne'
  field_simp

/-- **A step tilts by at most `|B|q/4`.** -/
theorem abs_boostTilt_le {B q KV K : ℝ} (hq : 0 ≤ q) (hKV : 0 < KV) (hK : 0 < K) :
    |boostTilt B q KV K| ≤ |B| * q / 4 := by
  have hu : 0 ≤ (K / KV) ^ q := rpow_nonneg (div_pos hK hKV).le _
  rw [boostTilt]
  generalize (K / KV) ^ q = u at *
  have h1 : 0 < (1 + u) ^ 2 := by positivity
  rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hu,
    abs_of_pos h1, div_le_iff₀ h1]
  have hB := abs_nonneg B
  have : 4 * u ≤ (1 + u) ^ 2 := by nlinarith [sq_nonneg (1 - u)]
  nlinarith [mul_nonneg hB hq]

/-- The derivative of the step's tilt: `K · d/dK (n_s − 1) = q(1 − u)/(1 + u) · (n_s − 1)`. -/
theorem hasDerivAt_boostTilt {B q KV K : ℝ} (hKV : 0 < KV) (hK : 0 < K) :
    HasDerivAt (boostTilt B q KV)
      (q * (1 - (K / KV) ^ q) / (1 + (K / KV) ^ q) * boostTilt B q KV K / K) K := by
  have hu : 0 ≤ (K / KV) ^ q := rpow_nonneg (div_pos hK hKV).le _
  have h1 : (1 + (K / KV) ^ q) ≠ 0 := by positivity
  have hdu := hasDerivAt_div_rpow (p := q) hKV hK
  have h := (((hdu.const_mul (B * q)).div ((hdu.const_add 1).fun_pow 2)
    (pow_ne_zero 2 h1))).neg
  convert h using 1
  · ext x
    simp [boostTilt]
  simp only [boostTilt, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hK0 := hK.ne'
  generalize (K / KV) ^ q = u at *
  field_simp
  ring

/-- **The running of a step.** `α_s = q(1 − u)/(1 + u) · (n_s − 1)`, exactly. -/
theorem runningIndex_boost {C B q KV K : ℝ} (hC : C ≠ 0) (hKV : 0 < KV) (hK : 0 < K) :
    runningIndex (boostSpectrum C B q KV) K =
      q * (1 - (K / KV) ^ q) / (1 + (K / KV) ^ q) *
        (spectralIndex (boostSpectrum C B q KV) K - 1) := by
  have hev : spectralIndex (boostSpectrum C B q KV) =ᶠ[𝓝 K] fun K ↦ 1 + boostTilt B q KV K :=
    eventually_of_mem (Ioi_mem_nhds hK) fun x hx ↦ spectralIndex_boost hC hKV hx
  rw [runningIndex, hev.deriv_eq, ((hasDerivAt_boostTilt hKV hK).const_add 1).deriv,
    spectralIndex_boost hC hKV hK, add_sub_cancel_left]
  field_simp

/-- **A step runs by at most `q` times its tilt.** `|α_s| ≤ q|n_s − 1|`. -/
theorem abs_runningIndex_boost_le {C B q KV K : ℝ} (hC : C ≠ 0) (hq : 0 ≤ q) (hKV : 0 < KV)
    (hK : 0 < K) :
    |runningIndex (boostSpectrum C B q KV) K| ≤
      q * |spectralIndex (boostSpectrum C B q KV) K - 1| := by
  have hu : 0 ≤ (K / KV) ^ q := rpow_nonneg (div_pos hK hKV).le _
  rw [runningIndex_boost hC hKV hK, abs_mul]
  gcongr
  generalize (K / KV) ^ q = u at *
  have h1 : 0 < 1 + u := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos h1, div_le_iff₀ h1]
  have : |1 - u| ≤ 1 + u := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

end WhiteHole
