import HolographicUniverse.Running

/-!
# P1: the shape of a Jeans tilt

Pathway P1 (`docs/TESTABILITY.md`, `phenomenology/p1_jeans/`) takes the paper's suggestion
(Sec. 5) that a residual Jeans instability of the bulk atmosphere reddens the spectrum. At linear
order, a 4D mode with `y = K/K_J < 1` grows for `τ = Γ₀Δt` e-folds, and in the large-growth form
the power is multiplied by `e^{2τ√(1 − y²)}`. Above the Jeans scale nothing grows.

This file proves exact result 1 of the P1 note, for the unprojected spectrum
`C · e^{2τ√(1 − (k/k_J)²)}` (`jeansSpectrum`):

* `spectralIndex_jeans`: below the Jeans scale, `n_s − 1 = −2τ y²/√(1 − y²)` (`jeansTilt`). The
  tilt is red for `τ > 0`.
* `runningIndex_jeans`: `α_s = (1 + 1/(1 − y²)) (n_s − 1)`. This is exact, not a leading-order
  statement, and it is the case `q = 2` of `runningIndex_le_of_tilt` with every higher term.
* `runningIndex_jeans_le`: so `α_s ≤ 2 (n_s − 1)` for `τ ≥ 0`. A red tilt comes with a running at
  least twice as red.
* `spectralIndex_jeans_above`: above the Jeans scale, `n_s = 1` exactly (`Real.sqrt` of a
  negative number is `0`, which is the statement that those modes do not grow).
* `planck2018Running_not_fits_jeans`: **no such spectrum fits Planck 2018 with running**, for
  any `C ≠ 0`, `τ ≥ 0` and any Jeans scale `k_J ≠ k_*`. Below the Jeans scale a fit to `n_s`
  forces `α_s ≤ −0.063`; above it `n_s = 1`.

**What is not covered.** The projection onto the brane (the integral over `x` in the P1 note),
the exact growth `cosh²(τ√(1 − y²))` (the large-`τ` form is used here), and the pivot exactly at
`k_J`. The projection is what opens the narrow, tuned window of the P1 note; that window is
numerical (`jeans_tilt.py`).
-/

namespace WhiteHole

open Real Filter Topology

/-- The unprojected Jeans spectrum `C · e^{2τ√(1 − (k/k_J)²)}`. -/
noncomputable def jeansSpectrum (C τ kJ : ℝ) (k : ℝ) : ℝ := C * exp (2 * τ * √(1 - (k / kJ) ^ 2))

/-- The Jeans tilt `n_s − 1 = −2τ y²/√(1 − y²)`, `y = k/k_J`. -/
noncomputable def jeansTilt (τ kJ : ℝ) (k : ℝ) : ℝ := -(2 * τ * (k / kJ) ^ 2 / √(1 - (k / kJ) ^ 2))

theorem hasDerivAt_one_sub_div_sq {kJ : ℝ} (hkJ : kJ ≠ 0) (k : ℝ) :
    HasDerivAt (fun k ↦ 1 - (k / kJ) ^ 2) (-(2 * k / kJ ^ 2)) k := by
  have h := (((hasDerivAt_id' k).div_const kJ).fun_pow 2).const_sub 1
  convert h using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

theorem one_sub_div_sq_pos {kJ k : ℝ} (hkJ : 0 < kJ) (hk : 0 < k) (hk' : k < kJ) :
    0 < 1 - (k / kJ) ^ 2 := by
  have h1 : k / kJ < 1 := (div_lt_one hkJ).2 hk'
  have h0 : 0 < k / kJ := div_pos hk hkJ
  nlinarith

/-- **The Jeans tilt.** Below the Jeans scale, `n_s − 1 = −2τ y²/√(1 − y²)`. -/
theorem spectralIndex_jeans {C τ kJ k : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ) (hk : 0 < k)
    (hk' : k < kJ) : spectralIndex (jeansSpectrum C τ kJ) k = 1 + jeansTilt τ kJ k := by
  have hu := one_sub_div_sq_pos hkJ hk hk'
  have hs : 0 < √(1 - (k / kJ) ^ 2) := sqrt_pos.2 hu
  have hd : HasDerivAt (jeansSpectrum C τ kJ)
      (C * (exp (2 * τ * √(1 - (k / kJ) ^ 2)) *
        (2 * τ * (-(2 * k / kJ ^ 2) / (2 * √(1 - (k / kJ) ^ 2)))))) k :=
    ((((hasDerivAt_one_sub_div_sq hkJ.ne' k).sqrt hu.ne').const_mul (2 * τ)).exp).const_mul C
  rw [spectralIndex, hd.deriv, jeansTilt, jeansSpectrum]
  have he := (exp_pos (2 * τ * √(1 - (k / kJ) ^ 2))).ne'
  field_simp

/-- The derivative of the Jeans tilt: `k · d/dk (n_s − 1) = (1 + 1/(1 − y²)) (n_s − 1)`. -/
theorem hasDerivAt_jeansTilt {τ kJ k : ℝ} (hkJ : 0 < kJ) (hk : 0 < k) (hk' : k < kJ) :
    HasDerivAt (jeansTilt τ kJ)
      ((1 + 1 / (1 - (k / kJ) ^ 2)) * jeansTilt τ kJ k / k) k := by
  have hu := one_sub_div_sq_pos hkJ hk hk'
  have hs : 0 < √(1 - (k / kJ) ^ 2) := sqrt_pos.2 hu
  have hss : √(1 - (k / kJ) ^ 2) ^ 2 = 1 - (k / kJ) ^ 2 := sq_sqrt hu.le
  have hnum : HasDerivAt (fun k ↦ 2 * τ * (k / kJ) ^ 2)
      (2 * τ * (2 * k / kJ ^ 2)) k := by
    have h := (((hasDerivAt_id' k).div_const kJ).fun_pow 2).const_mul (2 * τ)
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  have hden := (hasDerivAt_one_sub_div_sq hkJ.ne' k).sqrt hu.ne'
  have h := (hnum.div hden hs.ne').neg
  convert h using 1
  · ext x
    rfl
  simp only [jeansTilt]
  have hkk : 2 * k / kJ ^ 2 = 2 * (k / kJ) ^ 2 / k := by field_simp
  rw [hkk]
  have hk0 := hk.ne'
  generalize k / kJ = y at *
  generalize √(1 - y ^ 2) = r at *
  rw [← hss]
  have hr0 := hs.ne'
  field_simp
  linear_combination (τ * y ^ 2) * hss

/-- **The Jeans running.** Below the Jeans scale, `α_s = (1 + 1/(1 − y²)) (n_s − 1)`, exactly. -/
theorem runningIndex_jeans {C τ kJ k : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ) (hk : 0 < k)
    (hk' : k < kJ) :
    runningIndex (jeansSpectrum C τ kJ) k =
      (1 + 1 / (1 - (k / kJ) ^ 2)) * (spectralIndex (jeansSpectrum C τ kJ) k - 1) := by
  have hev : spectralIndex (jeansSpectrum C τ kJ) =ᶠ[𝓝 k] fun k ↦ 1 + jeansTilt τ kJ k :=
    eventually_of_mem (Ioo_mem_nhds hk hk') fun x hx ↦ spectralIndex_jeans hC hkJ hx.1 hx.2
  rw [runningIndex, hev.deriv_eq, ((hasDerivAt_jeansTilt hkJ hk hk').const_add 1).deriv,
    spectralIndex_jeans hC hkJ hk hk', add_sub_cancel_left]
  field_simp

/-- The Jeans tilt is red for `τ ≥ 0`. -/
theorem jeansTilt_nonpos {τ kJ k : ℝ} (hτ : 0 ≤ τ) : jeansTilt τ kJ k ≤ 0 := by
  rw [jeansTilt, neg_nonpos]
  positivity

/-- **A Jeans tilt runs at least twice as red.** Below the Jeans scale, with `τ ≥ 0`,
`α_s ≤ 2 (n_s − 1)`. -/
theorem runningIndex_jeans_le {C τ kJ k : ℝ} (hC : C ≠ 0) (hτ : 0 ≤ τ) (hkJ : 0 < kJ)
    (hk : 0 < k) (hk' : k < kJ) :
    runningIndex (jeansSpectrum C τ kJ) k ≤ 2 * (spectralIndex (jeansSpectrum C τ kJ) k - 1) := by
  have hu := one_sub_div_sq_pos hkJ hk hk'
  have hu1 : 1 - (k / kJ) ^ 2 ≤ 1 := by nlinarith
  have hinv : 1 ≤ 1 / (1 - (k / kJ) ^ 2) := by rw [le_div_iff₀ hu]; linarith
  rw [runningIndex_jeans hC hkJ hk hk', spectralIndex_jeans hC hkJ hk hk', add_sub_cancel_left]
  have ht := jeansTilt_nonpos (τ := τ) (kJ := kJ) (k := k) hτ
  nlinarith

/-- **Above the Jeans scale nothing grows.** For `k > k_J > 0`, `n_s = 1` exactly. -/
theorem spectralIndex_jeans_above {C τ kJ k : ℝ} (hkJ : 0 < kJ) (hk : kJ < k) :
    spectralIndex (jeansSpectrum C τ kJ) k = 1 := by
  apply spectralIndex_of_eventuallyEq
  have hconst : ∀ x, kJ < x → jeansSpectrum C τ kJ x = C := by
    intro x hx
    have h1 : 1 < x / kJ := (one_lt_div hkJ).2 hx
    have hneg : 1 - (x / kJ) ^ 2 ≤ 0 := by nlinarith
    simp [jeansSpectrum, sqrt_eq_zero'.2 hneg]
  filter_upwards [lt_mem_nhds hk] with x hx
  rw [hconst x hx, hconst k hk]

/-- **P1 against Planck 2018 with running.** No unprojected Jeans spectrum `C·e^{2τ√(1 − y²)}`
with `C ≠ 0` and `τ ≥ 0` fits `n_s` and `α_s` together, wherever the Jeans scale is (other than
exactly at the pivot). Below `k_J` the tilt runs too fast; above it `n_s = 1`. -/
theorem planck2018Running_not_fits_jeans {C τ kJ : ℝ} (hC : C ≠ 0) (hτ : 0 ≤ τ) (hkJ : 0 < kJ)
    (hne : kJ ≠ planck2018Running.kPivot) :
    ¬ planck2018Running.Fits (jeansSpectrum C τ kJ) := by
  rintro ⟨⟨-, hns⟩, ⟨has, -⟩⟩
  have hk : (0 : ℝ) < planck2018Running.kPivot := planck2018Running.kPivot_pos
  rcases lt_or_gt_of_ne hne with h | h
  · rw [spectralIndex_jeans_above hkJ h] at hns
    norm_num [planck2018Running] at hns
  · have hle := runningIndex_jeans_le hC hτ hkJ hk h
    norm_num [planck2018Running] at hns has hle
    linarith

/-! ### The brane spectrum above the Jeans scale (P1, result 2) -/

/-- The exact linear growth of a 4D mode with `z = K/K_J`, started from rest:
`cosh²(τ√(1 − z²))`. For `z ≥ 1` the square root is `0`, so the growth is `1`: those modes
oscillate and do not grow. -/
noncomputable def jeansGrowthExact (τ z : ℝ) : ℝ := cosh (τ * √(1 - z ^ 2)) ^ 2

/-- The projection of Eq. (48) with growth: `I(y) = ∫ (1 + x²)⁻² F(y√(1 + x²)) dx`,
`y = k/k_J`. Without growth, `I = π/2`. -/
noncomputable def jeansProjected (τ y : ℝ) : ℝ :=
  ∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2 * jeansGrowthExact τ (y * √(1 + x ^ 2))

theorem jeansGrowthExact_of_one_le {τ z : ℝ} (hz : 1 ≤ z) : jeansGrowthExact τ z = 1 := by
  have h : 1 - z ^ 2 ≤ 0 := by nlinarith
  simp [jeansGrowthExact, sqrt_eq_zero'.2 h]

/-- **Above the Jeans scale nothing happens.** For `y ≥ 1`, every 4D mode in the projection has
`K ≥ k ≥ k_J`, so `I(y) = π/2`, the value without growth. -/
theorem jeansProjected_of_one_le {τ y : ℝ} (hy : 1 ≤ y) : jeansProjected τ y = π / 2 := by
  rw [← integral_univ_inv_one_add_sq_sq, jeansProjected]
  congr 1
  ext x
  have hx : 1 ≤ √(1 + x ^ 2) := by
    exact (le_sqrt zero_le_one (by positivity)).2 (by nlinarith [sq_nonneg x])
  rw [jeansGrowthExact_of_one_le (one_le_mul_of_one_le_of_one_le hy hx), mul_one]

/-- **The brane spectrum is scale invariant above the Jeans scale.** For `k > k_J > 0`,
`C · I(k/k_J)` has `n_s = 1` exactly. -/
theorem spectralIndex_jeansProjected_above {C τ kJ k : ℝ} (hkJ : 0 < kJ) (hk : kJ < k) :
    spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k = 1 := by
  apply spectralIndex_of_eventuallyEq
  have hconst : ∀ x, kJ < x → C * jeansProjected τ (x / kJ) = C * (π / 2) := fun x hx ↦ by
    rw [jeansProjected_of_one_le ((one_le_div hkJ).2 hx.le)]
  filter_upwards [lt_mem_nhds hk] with x hx
  rw [hconst x hx, hconst k hk]

end WhiteHole
