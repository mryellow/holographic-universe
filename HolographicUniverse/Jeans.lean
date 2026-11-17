import HolographicUniverse.Running
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

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

For the brane spectrum, with the exact growth `cosh²(τ√(1 − z²))` (`jeansProjected`):

* `jeansProjected_of_one_le`, `spectralIndex_jeansProjected_above`: result 2, `I(y) = π/2` and
  `n_s = 1` exactly above the Jeans scale.
* `tendsto_jeansProjected_zero`, `tendsto_log_jeansProjected_budget`: the endpoints of result 3,
  `I(0⁺) = (π/2)cosh²τ`, so `ln I(1) − ln I(0⁺) = −2 ln cosh τ`. The spectrum falls by exactly
  `cosh²τ` between the far infrared and the Jeans scale.
* `tendsto_integral_spectralIndex_jeansBrane`: result 3. For `C · I(k/k_J)`,
  `∫₀^b (n_s − 1) d ln k = −2 ln cosh τ` for any `b ≥ k_J` (improper at `0`). The total red tilt
  the instability can produce is `2 ln cosh τ ≈ τ²`, however it is spread over scales.

**What is not covered.** The projection onto the brane (the integral over `x` in the P1 note),
for the results above, the exact growth `cosh²(τ√(1 − y²))` (the large-`τ` form is used here),
and the pivot exactly at `k_J`. Below `k_J` the projected tilt is numerical (`jeans_tilt.py`):
it opens the narrow, tuned window of the P1 note.
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

/-! ### The total tilt budget below the Jeans scale (P1, result 3, endpoints) -/

theorem continuous_jeansGrowthExact (τ : ℝ) : Continuous (jeansGrowthExact τ) := by
  unfold jeansGrowthExact
  fun_prop

/-- The growth is at most `cosh²τ`, the growth of the mode with `z = 0`. -/
theorem jeansGrowthExact_le (τ z : ℝ) : jeansGrowthExact τ z ≤ cosh τ ^ 2 := by
  unfold jeansGrowthExact
  have hs : √(1 - z ^ 2) ≤ 1 := sqrt_le_one.2 (by nlinarith [sq_nonneg z])
  have h : cosh (τ * √(1 - z ^ 2)) ≤ cosh τ := by
    rw [cosh_le_cosh, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg τ) hs
  exact pow_le_pow_left₀ (cosh_pos _).le h 2

theorem jeansGrowthExact_nonneg (τ z : ℝ) : 0 ≤ jeansGrowthExact τ z := sq_nonneg _

/-- **Far below the Jeans scale every mode grows fully.** As `y → 0`, `I(y) → (π/2) cosh²τ`
(dominated convergence, with the bound `(1 + x²)⁻² cosh²τ`). -/
theorem tendsto_jeansProjected_zero (τ : ℝ) :
    Tendsto (jeansProjected τ) (𝓝 0) (𝓝 (π / 2 * cosh τ ^ 2)) := by
  have hlim : π / 2 * cosh τ ^ 2 =
      ∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2 * jeansGrowthExact τ (0 * √(1 + x ^ 2)) := by
    simp only [zero_mul, jeansGrowthExact, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, sqrt_one, mul_one]
    rw [MeasureTheory.integral_mul_const, integral_univ_inv_one_add_sq_sq]
  rw [hlim]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ ↦ 1 / (1 + x ^ 2) ^ 2 * cosh τ ^ 2)
  · refine Eventually.of_forall fun y ↦ ?_
    exact (continuous_const.div (by fun_prop) (fun x ↦ by positivity) |>.mul
      ((continuous_jeansGrowthExact τ).comp
        (continuous_const.mul (by fun_prop)))).aestronglyMeasurable
  · refine Eventually.of_forall fun y ↦ Eventually.of_forall fun x ↦ ?_
    rw [norm_mul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (jeansGrowthExact_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (jeansGrowthExact_le _ _) (by positivity)
  · exact integrable_inv_one_add_sq_sq.mul_const _
  · refine Eventually.of_forall fun x ↦ ?_
    exact (continuous_const.mul ((continuous_jeansGrowthExact τ).comp
      (continuous_id.mul continuous_const))).tendsto 0

/-- **The tilt budget (P1, result 3, endpoints).** `ln I(1) − ln I(y) → −2 ln cosh τ` as
`y → 0`: between the far infrared and the Jeans scale the brane spectrum falls by exactly
`cosh²τ`, so the instability has a total red tilt of `2 ln cosh τ ≈ τ²` to spend. -/
theorem tendsto_log_jeansProjected_budget (τ : ℝ) :
    Tendsto (fun y ↦ log (jeansProjected τ 1) - log (jeansProjected τ y)) (𝓝 0)
      (𝓝 (-2 * log (cosh τ))) := by
  have hc : cosh τ ≠ 0 := (cosh_pos τ).ne'
  have h := ((tendsto_jeansProjected_zero τ).log (by positivity)).const_sub
    (log (jeansProjected τ 1))
  convert h using 2
  rw [jeansProjected_of_one_le le_rfl, log_mul (by positivity) (by positivity), log_pow]
  push_cast
  ring

/-! ### The tilt budget as an integral (P1, result 3)

The growth `F(z) = cosh²(τ√(1 − z²))` has a kink at `z = ±1`, where its slope jumps from
`∓2τ²` to `0`. It is still Lipschitz, with constant `2τ² cosh²τ` (`abs_jeansGrowthExact_sub_le`),
and in the projection the kink sits at only two values of `x`. So the derivative passes under
the integral (`hasDerivAt_jeansProjected`), `I` is differentiable everywhere, and the
fundamental theorem of calculus applies to `ln I`. -/

section budget

open MeasureTheory

theorem abs_sinh_le (a : ℝ) : |sinh a| ≤ |a| * cosh a := by
  rw [abs_sinh, ← cosh_abs]
  set b := |a| with hb
  have hb0 : 0 ≤ b := abs_nonneg a
  have h := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc 0 b) continuous_sinh.continuousOn
    (fun x _ ↦ differentiableAt_sinh.differentiableWithinAt) (C := cosh b)
    (fun x hx ↦ by
      rw [interior_Icc] at hx
      rw [Real.deriv_sinh, cosh_le_cosh, abs_of_pos hx.1, abs_of_nonneg hb0]
      exact hx.2.le) 0 ⟨le_rfl, hb0⟩ b ⟨hb0, le_rfl⟩ hb0
  simpa [mul_comm] using h

theorem jeansGrowthExact_of_one_le_sq {τ z : ℝ} (hz : 1 ≤ z ^ 2) : jeansGrowthExact τ z = 1 := by
  simp [jeansGrowthExact, sqrt_eq_zero'.2 (by linarith : 1 - z ^ 2 ≤ 0)]

theorem hasDerivAt_jeansGrowthExact {τ z : ℝ} (hz : z ^ 2 < 1) :
    HasDerivAt (jeansGrowthExact τ)
      (-(2 * τ * z * cosh (τ * √(1 - z ^ 2)) * sinh (τ * √(1 - z ^ 2)) / √(1 - z ^ 2))) z := by
  have hs : 0 < 1 - z ^ 2 := by linarith
  have hs' : 0 < √(1 - z ^ 2) := sqrt_pos.2 hs
  have h := ((((hasDerivAt_id' z).fun_pow 2).const_sub 1).sqrt hs.ne'
    |>.const_mul τ |>.cosh).fun_pow 2
  convert h using 1
  · rfl
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  field_simp

/-- The growth is Lipschitz below the Jeans scale, with constant `2τ² cosh²τ`. -/
theorem abs_deriv_jeansGrowthExact_le {τ z : ℝ} (hz : z ^ 2 < 1) :
    |2 * τ * z * cosh (τ * √(1 - z ^ 2)) * sinh (τ * √(1 - z ^ 2)) / √(1 - z ^ 2)| ≤
      2 * τ ^ 2 * cosh τ ^ 2 := by
  have hs : 0 < 1 - z ^ 2 := by linarith
  set s := √(1 - z ^ 2) with hsdef
  have hs' : 0 < s := sqrt_pos.2 hs
  have hs1 : s ≤ 1 := sqrt_le_one.2 (by nlinarith [sq_nonneg z])
  have hz1 : |z| ≤ 1 := by
    rw [← abs_one, ← sq_le_sq]; linarith
  have hc0 : 0 ≤ cosh (τ * s) := (cosh_pos _).le
  have hc : cosh (τ * s) ≤ cosh τ := by
    rw [cosh_le_cosh, abs_mul, abs_of_pos hs']
    exact mul_le_of_le_one_right (abs_nonneg τ) hs1
  have hsh : |sinh (τ * s)| ≤ |τ| * s * cosh (τ * s) := by
    simpa [abs_mul, abs_of_pos hs'] using abs_sinh_le (τ * s)
  rw [abs_div, abs_of_pos hs', div_le_iff₀ hs']
  simp only [abs_mul, abs_two]
  calc 2 * |τ| * |z| * |cosh (τ * s)| * |sinh (τ * s)|
      ≤ 2 * |τ| * 1 * cosh (τ * s) * (|τ| * s * cosh (τ * s)) := by
        rw [abs_of_nonneg hc0]; gcongr
    _ = 2 * |τ| ^ 2 * cosh (τ * s) ^ 2 * s := by ring
    _ ≤ 2 * |τ| ^ 2 * cosh τ ^ 2 * s := by gcongr
    _ = 2 * τ ^ 2 * cosh τ ^ 2 * s := by rw [sq_abs]


theorem jeansGrowthExact_neg (τ z : ℝ) : jeansGrowthExact τ (-z) = jeansGrowthExact τ z := by
  simp [jeansGrowthExact]

theorem abs_jeansGrowthExact_sub_le_Icc {τ z₁ z₂ : ℝ} (h₁ : z₁ ∈ Set.Icc (-1 : ℝ) 1)
    (h₂ : z₂ ∈ Set.Icc (-1 : ℝ) 1) :
    |jeansGrowthExact τ z₁ - jeansGrowthExact τ z₂| ≤ 2 * τ ^ 2 * cosh τ ^ 2 * |z₁ - z₂| := by
  set K := 2 * τ ^ 2 * cosh τ ^ 2
  have hcont := (continuous_jeansGrowthExact τ).continuousOn (s := Set.Icc (-1 : ℝ) 1)
  have hsq : ∀ x ∈ interior (Set.Icc (-1 : ℝ) 1), x ^ 2 < 1 := fun x hx ↦ by
    rw [interior_Icc] at hx
    nlinarith [hx.1, hx.2]
  have hdiff : DifferentiableOn ℝ (jeansGrowthExact τ) (interior (Set.Icc (-1 : ℝ) 1)) :=
    fun x hx ↦ (hasDerivAt_jeansGrowthExact (hsq x hx)).differentiableAt.differentiableWithinAt
  have hbd : ∀ x ∈ interior (Set.Icc (-1 : ℝ) 1), |deriv (jeansGrowthExact τ) x| ≤ K :=
    fun x hx ↦ by
      rw [(hasDerivAt_jeansGrowthExact (hsq x hx)).deriv, abs_neg]
      exact abs_deriv_jeansGrowthExact_le (hsq x hx)
  have key : ∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1, a ≤ b →
      |jeansGrowthExact τ b - jeansGrowthExact τ a| ≤ K * |b - a| := fun a ha b hb hab ↦ by
    have hu := (convex_Icc (-1 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (fun x hx ↦ (le_abs_self _).trans (hbd x hx)) a ha b hb hab
    have hl := (convex_Icc (-1 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont hdiff
      (fun x hx ↦ (neg_abs_le _).trans' (neg_le_neg (hbd x hx))) a ha b hb hab
    rw [abs_of_nonneg (sub_nonneg.2 hab), abs_le]
    constructor <;> linarith
  rcases le_total z₁ z₂ with h | h
  · rw [abs_sub_comm, abs_sub_comm z₁]; exact key z₁ h₁ z₂ h₂ h
  · exact key z₂ h₂ z₁ h₁ h

/-- **The growth is Lipschitz**, with constant `2τ² cosh²τ`, across the kink at `z = ±1`. -/
theorem abs_jeansGrowthExact_sub_le (τ z₁ z₂ : ℝ) :
    |jeansGrowthExact τ z₁ - jeansGrowthExact τ z₂| ≤ 2 * τ ^ 2 * cosh τ ^ 2 * |z₁ - z₂| := by
  set c : ℝ → ℝ := fun z ↦ max (min z 1) (-1)
  have hc : ∀ z, jeansGrowthExact τ z = jeansGrowthExact τ (c z) := fun z ↦ by
    simp only [c]
    rcases le_total z 1 with h1 | h1
    · rcases le_total z (-1) with h2 | h2
      · rw [min_eq_left h1, max_eq_right h2, jeansGrowthExact_of_one_le_sq (by nlinarith),
          jeansGrowthExact_of_one_le_sq (by norm_num)]
      · rw [min_eq_left h1, max_eq_left h2]
    · rw [min_eq_right h1, max_eq_left (by norm_num), jeansGrowthExact_of_one_le h1,
        jeansGrowthExact_of_one_le le_rfl]
  have hmem : ∀ z, c z ∈ Set.Icc (-1 : ℝ) 1 := fun z ↦
    ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩
  have hlip : |c z₁ - c z₂| ≤ |z₁ - z₂| :=
    (abs_max_sub_max_le_abs _ _ _).trans <|
      (abs_min_sub_min_le_max _ _ _ _).trans (by simp)
  rw [hc z₁, hc z₂]
  exact (abs_jeansGrowthExact_sub_le_Icc (hmem z₁) (hmem z₂)).trans
    (mul_le_mul_of_nonneg_left hlip (by positivity))

theorem differentiableAt_jeansGrowthExact {τ z : ℝ} (hz : z ^ 2 ≠ 1) :
    DifferentiableAt ℝ (jeansGrowthExact τ) z := by
  rcases hz.lt_or_gt with h | h
  · exact (hasDerivAt_jeansGrowthExact h).differentiableAt
  · refine (differentiableAt_const (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const (continuous_pow 2)).mem_nhds h] with x hx
    exact jeansGrowthExact_of_one_le_sq (le_of_lt hx)

theorem one_le_jeansGrowthExact (τ z : ℝ) : 1 ≤ jeansGrowthExact τ z :=
  one_le_pow₀ (one_le_cosh _)

theorem integrable_jeansProjected (τ y : ℝ) :
    Integrable fun x : ℝ ↦ 1 / (1 + x ^ 2) ^ 2 * jeansGrowthExact τ (y * √(1 + x ^ 2)) := by
  refine (integrable_inv_one_add_sq_sq.mul_const (cosh τ ^ 2)).mono' ?_ ?_
  · exact (continuous_const.div (by fun_prop) (fun x ↦ by positivity) |>.mul
      ((continuous_jeansGrowthExact τ).comp
        (continuous_const.mul (by fun_prop)))).aestronglyMeasurable
  · refine Eventually.of_forall fun x ↦ ?_
    rw [norm_mul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (jeansGrowthExact_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (jeansGrowthExact_le _ _) (by positivity)

/-- The brane spectrum never falls below its value without growth. -/
theorem pi_div_two_le_jeansProjected (τ y : ℝ) : π / 2 ≤ jeansProjected τ y := by
  rw [← integral_univ_inv_one_add_sq_sq, jeansProjected]
  refine integral_mono integrable_inv_one_add_sq_sq (integrable_jeansProjected τ y) fun x ↦ ?_
  exact le_mul_of_one_le_right (by positivity) (one_le_jeansGrowthExact _ _)


/-- **The brane spectrum is differentiable**, at every `y`. The growth has a kink at `z = 1`, but
in the projection that kink sits at two values of `x` only, a null set, and the growth is
Lipschitz, so the derivative passes under the integral. -/
theorem hasDerivAt_jeansProjected (τ y₀ : ℝ) :
    HasDerivAt (jeansProjected τ)
      (∫ x : ℝ, 1 / (1 + x ^ 2) ^ 2 *
        (deriv (jeansGrowthExact τ) (y₀ * √(1 + x ^ 2)) * √(1 + x ^ 2))) y₀ := by
  set K := 2 * τ ^ 2 * cosh τ ^ 2
  have hK : 0 ≤ K := by positivity
  have hws : ∀ x : ℝ, 1 / (1 + x ^ 2) ^ 2 * √(1 + x ^ 2) ≤ (1 + x ^ 2)⁻¹ := fun x ↦ by
    have h1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hs : √(1 + x ^ 2) ≤ 1 + x ^ 2 := by
      rw [sqrt_le_left (by linarith)]; nlinarith
    have he : (1 + x ^ 2)⁻¹ * (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := by field_simp
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), he]
    exact hs
  refine (hasDerivAt_integral_of_dominated_loc_of_lip (F := fun y x ↦
      1 / (1 + x ^ 2) ^ 2 * jeansGrowthExact τ (y * √(1 + x ^ 2)))
    (bound := fun x ↦ K * (1 + x ^ 2)⁻¹) Filter.univ_mem ?_ (integrable_jeansProjected τ y₀) ?_
    ?_ (integrable_inv_one_add_sq.const_mul K) ?_).2
  · exact Eventually.of_forall fun y ↦ (integrable_jeansProjected τ y).aestronglyMeasurable
  · exact ((continuous_const.div (by fun_prop) (fun x ↦ by positivity)).measurable.mul
      (((measurable_deriv _).comp (measurable_const.mul (by fun_prop))).mul
        (by fun_prop))).aestronglyMeasurable
  · refine Eventually.of_forall fun x ↦ LipschitzOnWith.of_dist_le_mul fun y₁ _ y₂ _ ↦ ?_
    have hw : 0 < 1 / (1 + x ^ 2) ^ 2 := by positivity
    have hb : 0 ≤ K * (1 + x ^ 2)⁻¹ := mul_nonneg hK (by positivity)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, ← mul_sub, abs_mul, abs_of_pos hw,
      abs_of_nonneg hb]
    calc 1 / (1 + x ^ 2) ^ 2 *
          |jeansGrowthExact τ (y₁ * √(1 + x ^ 2)) - jeansGrowthExact τ (y₂ * √(1 + x ^ 2))|
        ≤ 1 / (1 + x ^ 2) ^ 2 * (K * (√(1 + x ^ 2) * |y₁ - y₂|)) := by
          gcongr
          refine (abs_jeansGrowthExact_sub_le _ _ _).trans_eq ?_
          rw [← sub_mul, abs_mul, abs_of_nonneg (sqrt_nonneg _), mul_comm |y₁ - y₂|]
      _ = K * (1 / (1 + x ^ 2) ^ 2 * √(1 + x ^ 2)) * |y₁ - y₂| := by ring
      _ ≤ K * (1 + x ^ 2)⁻¹ * |y₁ - y₂| := by gcongr; exact hws x
  · -- the kink is hit only where `y₀² (1 + x²) = 1`: at most two points
    by_cases hy : y₀ = 0
    · refine Eventually.of_forall fun x ↦ ?_
      have hd := differentiableAt_jeansGrowthExact (τ := τ) (z := y₀ * √(1 + x ^ 2))
        (by simp [hy])
      have h := (hd.hasDerivAt.comp y₀ ((hasDerivAt_id' y₀).mul_const (√(1 + x ^ 2)))).const_mul
        (1 / (1 + x ^ 2) ^ 2)
      convert h using 1
      · rfl
      · ring
    set c := (1 - y₀ ^ 2) / y₀ ^ 2
    have hnull : volume ({√c, -√c} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
    refine measure_mono_null (fun x hx ↦ ?_) hnull
    by_contra hxs
    refine hx ?_
    have hz : (y₀ * √(1 + x ^ 2)) ^ 2 ≠ 1 := by
      intro h
      rw [mul_pow, sq_sqrt (by positivity)] at h
      have hx2 : x ^ 2 = c := by
        simp only [c]; field_simp; linarith
      have hc : 0 ≤ c := hx2 ▸ sq_nonneg x
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans (sq_sqrt hc).symm) with h' | h'
      · exact hxs (by simp [h'])
      · exact hxs (by simp [h'])
    change HasDerivAt (fun y ↦ 1 / (1 + x ^ 2) ^ 2 * jeansGrowthExact τ (y * √(1 + x ^ 2)))
      (1 / (1 + x ^ 2) ^ 2 * (deriv (jeansGrowthExact τ) (y₀ * √(1 + x ^ 2)) * √(1 + x ^ 2))) y₀
    have h := ((differentiableAt_jeansGrowthExact (τ := τ) hz).hasDerivAt.comp y₀
      ((hasDerivAt_id' y₀).mul_const (√(1 + x ^ 2)))).const_mul (1 / (1 + x ^ 2) ^ 2)
    convert h using 1
    · rfl
    · ring


theorem abs_jeansProjected_sub_le (τ y₁ y₂ : ℝ) :
    |jeansProjected τ y₁ - jeansProjected τ y₂| ≤
      2 * τ ^ 2 * cosh τ ^ 2 * π * |y₁ - y₂| := by
  set K := 2 * τ ^ 2 * cosh τ ^ 2
  have hK : 0 ≤ K := by positivity
  rw [jeansProjected, jeansProjected,
    ← integral_sub (integrable_jeansProjected τ y₁) (integrable_jeansProjected τ y₂)]
  have hb : Integrable fun x : ℝ ↦ K * (1 + x ^ 2)⁻¹ * |y₁ - y₂| :=
    (integrable_inv_one_add_sq.const_mul K).mul_const _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun x ↦ ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
    have hws : 1 / (1 + x ^ 2) ^ 2 * √(1 + x ^ 2) ≤ (1 + x ^ 2)⁻¹ := by
      have h1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
      have hs : √(1 + x ^ 2) ≤ 1 + x ^ 2 := by
        rw [sqrt_le_left (by linarith)]; nlinarith
      have he : (1 + x ^ 2)⁻¹ * (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := by field_simp
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), he]
      exact hs
    calc 1 / (1 + x ^ 2) ^ 2 *
          |jeansGrowthExact τ (y₁ * √(1 + x ^ 2)) - jeansGrowthExact τ (y₂ * √(1 + x ^ 2))|
        ≤ 1 / (1 + x ^ 2) ^ 2 * (K * (√(1 + x ^ 2) * |y₁ - y₂|)) := by
          gcongr
          refine (abs_jeansGrowthExact_sub_le _ _ _).trans_eq ?_
          rw [← sub_mul, abs_mul, abs_of_nonneg (sqrt_nonneg _), mul_comm |y₁ - y₂|]
      _ = K * (1 / (1 + x ^ 2) ^ 2 * √(1 + x ^ 2)) * |y₁ - y₂| := by ring
      _ ≤ K * (1 + x ^ 2)⁻¹ * |y₁ - y₂| := by gcongr
  · rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

theorem abs_deriv_jeansProjected_le (τ y : ℝ) :
    |deriv (jeansProjected τ) y| ≤ 2 * τ ^ 2 * cosh τ ^ 2 * π := by
  have hK : 0 ≤ 2 * τ ^ 2 * cosh τ ^ 2 * π := by positivity
  have hL : LipschitzWith (Real.nnabs (2 * τ ^ 2 * cosh τ ^ 2 * π)) (jeansProjected τ) :=
    LipschitzWith.of_dist_le_mul fun a b ↦ by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK]
      exact abs_jeansProjected_sub_le τ a b
  have h := norm_deriv_le_of_lipschitz (x₀ := y) hL
  rwa [Real.norm_eq_abs, Real.coe_nnabs, abs_of_nonneg hK] at h

theorem jeansProjected_pos (τ y : ℝ) : 0 < jeansProjected τ y :=
  lt_of_lt_of_le (by positivity) (pi_div_two_le_jeansProjected τ y)

/-- **The integrated tilt.** For `0 < a, b`, `∫_a^b (n_s − 1) d ln y = ln I(b) − ln I(a)`. -/
theorem integral_spectralIndex_jeansProjected (τ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ y in a..b, (spectralIndex (jeansProjected τ) y - 1) / y =
      log (jeansProjected τ b) - log (jeansProjected τ a) := by
  have hpos := jeansProjected_pos τ
  have hd : ∀ y, HasDerivAt (jeansProjected τ) (deriv (jeansProjected τ) y) y := fun y ↦
    (hasDerivAt_jeansProjected τ y).differentiableAt.hasDerivAt
  have hcont : Continuous (jeansProjected τ) :=
    continuous_iff_continuousAt.2 fun y ↦ (hd y).continuousAt
  have hcongr : Set.EqOn (fun y ↦ (spectralIndex (jeansProjected τ) y - 1) / y)
      (fun y ↦ deriv (jeansProjected τ) y / jeansProjected τ y) (Set.uIcc a b) := fun y hy ↦ by
    have hy0 : 0 < y := by rcases Set.mem_uIcc.1 hy with h | h <;> linarith [h.1]
    have := (hpos y).ne'
    simp only [spectralIndex]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ (hd y).log (hpos y).ne') ?_
  refine (intervalIntegrable_const (c := 2 * τ ^ 2 * cosh τ ^ 2 * π / (π / 2))).mono_fun'
    ((measurable_deriv _).div hcont.measurable).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hpos y)]
  exact div_le_div₀ (by positivity) (abs_deriv_jeansProjected_le τ y) (by positivity)
    (pi_div_two_le_jeansProjected τ y)

/-- **The tilt budget (P1, result 3).** The total tilt of the brane spectrum over all scales,
`∫₀^b (n_s − 1) d ln y` for any `b ≥ 1`, is exactly `−2 ln cosh τ`, as an improper integral
at `y → 0⁺`. -/
theorem tendsto_integral_spectralIndex_jeansProjected (τ : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    Tendsto (fun a ↦ ∫ y in a..b, (spectralIndex (jeansProjected τ) y - 1) / y) (𝓝[>] 0)
      (𝓝 (-2 * log (cosh τ))) := by
  refine ((tendsto_log_jeansProjected_budget τ).mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun a ha ↦ ?_)
  dsimp only
  rw [integral_spectralIndex_jeansProjected τ ha (by linarith),
    jeansProjected_of_one_le hb, jeansProjected_of_one_le le_rfl]


/-- The brane spectrum in `k`: its index at `k` is the index of `I` at `y = k/k_J`. -/
theorem spectralIndex_jeansBrane {C τ kJ : ℝ} (hC : C ≠ 0) (hkJ : kJ ≠ 0) (k : ℝ) :
    spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k =
      spectralIndex (jeansProjected τ) (k / kJ) := by
  have h := (((hasDerivAt_jeansProjected τ (k / kJ)).differentiableAt.hasDerivAt.comp k
    ((hasDerivAt_id' k).div_const kJ)).const_mul C)
  replace h : HasDerivAt (fun k ↦ C * jeansProjected τ (k / kJ))
      (C * (deriv (jeansProjected τ) (k / kJ) * (1 / kJ))) k := h
  have hI := (jeansProjected_pos τ (k / kJ)).ne'
  rw [spectralIndex, spectralIndex, h.deriv]
  field_simp

/-- **The tilt budget in `k` (P1, result 3).** For the brane spectrum `C · I(k/k_J)`,
`∫₀^b (n_s − 1) d ln k = −2 ln cosh τ` for any `b ≥ k_J`, as an improper integral at
`k → 0⁺`. All of it is spent below the Jeans scale. -/
theorem tendsto_integral_spectralIndex_jeansBrane {C τ kJ b : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ)
    (hb : kJ ≤ b) :
    Tendsto (fun a ↦ ∫ k in a..b, (spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k - 1) / k)
      (𝓝[>] 0) (𝓝 (-2 * log (cosh τ))) := by
  have hdiv : Tendsto (fun a ↦ a / kJ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun a ha ↦ div_pos ha hkJ⟩
    simpa using ((continuous_id.div_const kJ).tendsto 0).mono_left nhdsWithin_le_nhds
  refine ((tendsto_integral_spectralIndex_jeansProjected τ ((one_le_div hkJ).2 hb)).comp
    hdiv).congr' (Eventually.of_forall fun a ↦ ?_)
  have hpt : ∀ k, (spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k - 1) / k =
      (spectralIndex (jeansProjected τ) (k / kJ) - 1) / (k / kJ) / kJ := fun k ↦ by
    rw [spectralIndex_jeansBrane hC hkJ.ne', div_div, div_mul_cancel₀ k hkJ.ne']
  simp only [Function.comp, hpt, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div (fun y ↦ (spectralIndex (jeansProjected τ) y - 1) / y)
      hkJ.ne', smul_eq_mul]
  field_simp

end budget

end WhiteHole
