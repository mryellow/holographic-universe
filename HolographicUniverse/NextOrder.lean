module

public import HolographicUniverse.ThermalIntegral
public import HolographicUniverse.ScaleInvariance
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# The thermal integral away from `κ = 0` (ROADMAP M7.3, first part)

`ω_± = |κ' ± κ/2|` (`omegaPM_one`, `omegaPM_neg_one`). With `φ(x) = x n(x) = x/(eˣ - 1)`
(`phiB`), the thermal integrand of Eq. (46) is `φ₊φ₋ + (ω₊φ₋ + ω₋φ₊)/2`. A shift of the
integration variable then splits `M(κ)` in two (`thermalM_eq`):

  `(2π)⁴ M(κ) = B(κ) + A(κ)`,
  `B(κ) = ∫ φ(|u|) φ(|u - κ|) d⁴u` (`thermalB`),  `A(κ) = ∫ |v + κ| φ(|v|) d⁴v` (`thermalA`).

The two parts pull in opposite directions:

* `A` is convex and even (`convexOn_thermalA`, `thermalA_neg`), so it has its minimum at
  `κ = 0` (`thermalA_zero_le`). It makes `M` grow, that is, it tilts the spectrum blue.
* `B` is an autocorrelation, so it has its maximum at `κ = 0` (`thermalB_le_zero`). It
  makes `M` fall, that is, it tilts the spectrum red.

So symmetry alone does not fix the sign of the `O(κ²)` term of Eq. (48).

The sign is settled in `SecondOrder.lean`: `M(κ) = M(0) + (10ζ(5) - ζ(3))/(32π²)·κ² + o(κ²)`.
The `A` term is larger by a factor of about 17, so the next order is blue.

`not_fits_of_deriv_nonneg` is the falsification step that this feeds. If `M' ≥ 0` at the
pivot, no spectrum `C · M(k/s)` fits a release with `n_s < 1`.
-/

namespace WhiteHole

open Real Set MeasureTheory Filter Topology

/-! ### `ω_±` as distances -/

/-- `ω₊ = |κ' + κ/2|`. -/
theorem omegaPM_one (κ κ' : E4) : omegaPM 1 κ κ' = ‖κ' + (1 / 2 : ℝ) • κ‖ := by
  rw [omegaPM, show ‖κ'‖ ^ 2 + ‖κ‖ ^ 2 / 4 + 1 * inner ℝ κ κ' = ‖κ' + (1 / 2 : ℝ) • κ‖ ^ 2 by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, real_inner_comm, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring]
  exact sqrt_sq (norm_nonneg _)

/-- `ω₋ = |κ' - κ/2|`. -/
theorem omegaPM_neg_one (κ κ' : E4) : omegaPM (-1) κ κ' = ‖κ' - (1 / 2 : ℝ) • κ‖ := by
  rw [omegaPM, show ‖κ'‖ ^ 2 + ‖κ‖ ^ 2 / 4 + -1 * inner ℝ κ κ' = ‖κ' - (1 / 2 : ℝ) • κ‖ ^ 2 by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, real_inner_comm, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring]
  exact sqrt_sq (norm_nonneg _)

/-! ### The weight `φ(x) = x n(x)` -/

/-- `φ(x) = x n(x) = x/(eˣ - 1)`. -/
noncomputable def phiB (x : ℝ) : ℝ := x * bose x

@[fun_prop] theorem measurable_phiB : Measurable phiB := by
  unfold phiB bose
  fun_prop

theorem phiB_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ phiB x := by
  unfold phiB bose
  have : 0 ≤ exp x - 1 := by linarith [add_one_le_exp x]
  positivity

/-- `φ(x) ≤ e^{-x/2}` for `x ≥ 0`, from `x e^{x/2} ≤ eˣ - 1`, that is, `t ≤ sinh t`. -/
theorem phiB_le_exp {x : ℝ} (hx : 0 ≤ x) : phiB x ≤ exp (-(1 / 2) * x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [phiB]
  have ht : 0 ≤ x / 2 := by positivity
  have hs := Real.self_le_sinh_iff.2 ht
  rw [Real.sinh_eq] at hs
  have he : exp x = exp (x / 2) * exp (x / 2) := by rw [← exp_add]; ring_nf
  have hm : exp (x / 2) * exp (-(x / 2)) = 1 := by rw [← exp_add]; simp
  have hn : exp (-(1 / 2) * x) = exp (-(x / 2)) := by ring_nf
  have hp : 0 < exp x - 1 := by linarith [add_one_lt_exp hx.ne']
  have h2 := exp_pos (x / 2)
  rw [hn, phiB, bose, mul_one_div, div_le_iff₀ hp]
  nlinarith [mul_le_mul_of_nonneg_left hs h2.le]

theorem phiB_le_one {x : ℝ} (hx : 0 ≤ x) : phiB x ≤ 1 :=
  (phiB_le_exp hx).trans (exp_le_one_iff.2 (by nlinarith))

/-- The radial weights `|u|ʲ φ(|u|)` are integrable on `ℝ⁴`. -/
theorem integrable_norm_pow_phiB (j : ℕ) : Integrable (fun u : E4 ↦ ‖u‖ ^ j * phiB ‖u‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun y ↦ y ^ j * phiB y),
    finrank_euclideanSpace_fin]
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((3 + j : ℕ) : ℝ)) (p := 1)
    (b := 1 / 2) (by have : (0 : ℝ) ≤ ((3 + j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) one_pos
    (by norm_num)
  refine hg.mono' (by fun_prop [measurable_phiB]) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y (hy : 0 < y) ↦ ?_)
  rw [rpow_natCast, rpow_one, smul_eq_mul, Real.norm_of_nonneg (by
    have := phiB_nonneg hy.le; positivity), pow_add, ← mul_assoc]
  have := phiB_le_exp hy.le
  gcongr

/-! ### The split `(2π)⁴ M = B + A` -/

/-- The radial weight `f(u) = φ(|u|)` on `ℝ⁴`. -/
noncomputable def phiR (u : E4) : ℝ := phiB ‖u‖

theorem phiR_nonneg (u : E4) : 0 ≤ phiR u := phiB_nonneg (norm_nonneg u)

theorem integrable_phiR : Integrable phiR := by
  have := integrable_norm_pow_phiB 0
  simp only [pow_zero, one_mul] at this
  exact this

@[fun_prop] theorem measurable_phiR : Measurable phiR := measurable_phiB.comp measurable_norm

theorem norm_phiR_le (u : E4) : ‖phiR u‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (phiR_nonneg u)]
  exact phiB_le_one (norm_nonneg u)

/-- The autocorrelation part, `B(κ) = ∫ φ(|u|) φ(|u - κ|) d⁴u`. -/
noncomputable def thermalB (κ : E4) : ℝ := ∫ u : E4, phiR u * phiR (u - κ)

/-- The cross part, `A(κ) = ∫ |v + κ| φ(|v|) d⁴v`. -/
noncomputable def thermalA (κ : E4) : ℝ := ∫ v : E4, ‖v + κ‖ * phiR v

theorem integrable_thermalB (κ : E4) : Integrable fun u : E4 ↦ phiR u * phiR (u - κ) :=
  integrable_phiR.mul_bdd ((measurable_phiR.comp (measurable_id.sub_const κ)).aestronglyMeasurable)
    (Eventually.of_forall fun u ↦ norm_phiR_le (u - κ))

theorem integrable_thermalA (κ : E4) : Integrable fun v : E4 ↦ ‖v + κ‖ * phiR v := by
  have h := (integrable_norm_pow_phiB 1).add (integrable_phiR.const_mul ‖κ‖)
  refine h.mono' (((continuous_norm.comp (continuous_id.add continuous_const)).measurable.mul
    measurable_phiR).aestronglyMeasurable) (Eventually.of_forall fun v ↦ ?_)
  have := phiR_nonneg v
  simp only [Pi.add_apply, pow_one]
  rw [Real.norm_of_nonneg (by positivity)]
  change ‖v + κ‖ * phiR v ≤ ‖v‖ * phiR v + ‖κ‖ * phiR v
  nlinarith [norm_add_le v κ]

/-- `A` is even. -/
theorem thermalA_neg (κ : E4) : thermalA (-κ) = thermalA κ := by
  unfold thermalA
  rw [← integral_neg_eq_self]
  congr 1
  funext v
  rw [phiR, phiR, norm_neg, show -v + -κ = -(v + κ) by abel, norm_neg]

/-- **The split of Eq. (46).** `(2π)⁴ M(κ) = B(κ) + A(κ)`. -/
theorem thermalM_eq (κ : E4) : thermalM κ = (thermalB κ + thermalA κ) / (2 * π) ^ 4 := by
  set h : E4 := (1 / 2 : ℝ) • κ
  have hh : h + h = κ := by rw [← add_smul]; norm_num
  have hpt : ∀ κ' : E4, omegaPM 1 κ κ' * omegaPM (-1) κ κ'
      * (bose (omegaPM 1 κ κ') * bose (omegaPM (-1) κ κ')
        + (bose (omegaPM 1 κ κ') + bose (omegaPM (-1) κ κ')) / 2)
      = phiR (κ' + h) * phiR (κ' - h)
        + (‖κ' + h‖ * phiR (κ' - h) + ‖κ' - h‖ * phiR (κ' + h)) / 2 := fun κ' ↦ by
    rw [omegaPM_one, omegaPM_neg_one]
    unfold phiR phiB
    ring
  have e1 : ∫ κ' : E4, phiR (κ' + h) * phiR (κ' - h) = thermalB κ := by
    rw [thermalB, ← integral_add_right_eq_self (fun u ↦ phiR u * phiR (u - κ)) h]
    congr 1
    funext κ'
    rw [show κ' + h - κ = κ' - h by rw [← hh]; abel]
  have e2 : ∫ κ' : E4, ‖κ' + h‖ * phiR (κ' - h) = thermalA κ := by
    rw [thermalA, ← integral_sub_right_eq_self (fun v ↦ ‖v + κ‖ * phiR v) h]
    congr 1
    funext κ'
    rw [show κ' - h + κ = κ' + h by rw [← hh]; abel]
  have e3 : ∫ κ' : E4, ‖κ' - h‖ * phiR (κ' + h) = thermalA κ := by
    rw [← thermalA_neg, thermalA, ← integral_add_right_eq_self (fun v ↦ ‖v + -κ‖ * phiR v) h]
    congr 1
    funext κ'
    rw [show κ' + h + -κ = κ' - h by rw [← hh]; abel]
  have iB : Integrable fun κ' : E4 ↦ phiR (κ' + h) * phiR (κ' - h) := by
    have := (integrable_thermalB κ).comp_add_right h
    refine this.congr (Eventually.of_forall fun κ' ↦ ?_)
    dsimp only
    rw [show κ' + h - κ = κ' - h by rw [← hh]; abel]
  have iA1 : Integrable fun κ' : E4 ↦ ‖κ' + h‖ * phiR (κ' - h) := by
    have := (integrable_thermalA κ).comp_sub_right h
    refine this.congr (Eventually.of_forall fun κ' ↦ ?_)
    dsimp only
    rw [show κ' - h + κ = κ' + h by rw [← hh]; abel]
  have iA2 : Integrable fun κ' : E4 ↦ ‖κ' - h‖ * phiR (κ' + h) := by
    have := (integrable_thermalA (-κ)).comp_add_right h
    refine this.congr (Eventually.of_forall fun κ' ↦ ?_)
    dsimp only
    rw [show κ' + h + -κ = κ' - h by rw [← hh]; abel]
  have iA : Integrable fun κ' : E4 ↦
      (‖κ' + h‖ * phiR (κ' - h) + ‖κ' - h‖ * phiR (κ' + h)) / 2 := (iA1.add iA2).div_const 2
  unfold thermalM
  simp_rw [hpt]
  rw [integral_div, integral_add iB iA, integral_div,
    integral_add iA1 iA2, e1, e2, e3]
  ring

/-! ### Opposite pulls of `A` and `B` -/

/-- **`A` is convex.** `|v + (aκ₁ + bκ₂)| ≤ a|v + κ₁| + b|v + κ₂|` for `a + b = 1`. -/
theorem convexOn_thermalA : ConvexOn ℝ univ thermalA := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [thermalA, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_thermalA x).const_mul a) ((integrable_thermalA y).const_mul b)]
  refine integral_mono (integrable_thermalA _)
    (((integrable_thermalA x).const_mul a).add ((integrable_thermalA y).const_mul b)) fun v ↦ ?_
  have hv : v + (a • x + b • y) = a • (v + x) + b • (v + y) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  have hn : ‖v + (a • x + b • y)‖ ≤ a * ‖v + x‖ + b * ‖v + y‖ := by
    rw [hv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have := phiR_nonneg v
  simp only
  nlinarith

/-- **`A` is smallest at `κ = 0`.** It pushes `M` up away from `κ = 0`. -/
theorem thermalA_zero_le (κ : E4) : thermalA 0 ≤ thermalA κ := by
  have h := convexOn_thermalA.2 (mem_univ κ) (mem_univ (-κ)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  rw [smul_neg, add_neg_cancel, thermalA_neg, smul_eq_mul] at h
  linarith

/-- **`B` is largest at `κ = 0`.** `φ₁φ₂ ≤ (φ₁² + φ₂²)/2`, and a shift does not change
`∫ φ²`. It pushes `M` down away from `κ = 0`. -/
theorem thermalB_le_zero (κ : E4) : thermalB κ ≤ thermalB 0 := by
  have hsq : Integrable fun u : E4 ↦ phiR u * phiR u := by
    simpa using integrable_thermalB 0
  have hsq' : Integrable fun u : E4 ↦ phiR (u - κ) * phiR (u - κ) := hsq.comp_sub_right κ
  have hshift : ∫ u : E4, phiR (u - κ) * phiR (u - κ) = ∫ u : E4, phiR u * phiR u :=
    integral_sub_right_eq_self (fun u ↦ phiR u * phiR u) κ
  have hle : thermalB κ ≤ ∫ u : E4, (phiR u * phiR u + phiR (u - κ) * phiR (u - κ)) / 2 :=
    integral_mono (integrable_thermalB κ) ((hsq.add hsq').div_const 2) fun u ↦ by
      nlinarith [sq_nonneg (phiR u - phiR (u - κ))]
  rw [integral_div, integral_add hsq hsq', hshift] at hle
  simpa [thermalB] using hle

/-! ### The falsification step -/

/-- **A non-decreasing `M` gives no red tilt.** If `P(k) = C · M(k/s)` with `s > 0`, and at the
pivot `M > 0` and `M' ≥ 0`, then `n_s ≥ 1`. So `P` fits no release with `n_s < 1`. -/
theorem ObsData.not_fits_of_deriv_nonneg (d : ObsData) (hns : d.ns_hi < 1) (hk : 0 ≤ d.kPivot)
    {C s : ℝ} {M : ℝ → ℝ} (hC : C ≠ 0) (hs : 0 < s)
    (hM : DifferentiableAt ℝ M (d.kPivot / s)) (hM0 : 0 < M (d.kPivot / s))
    (hM' : 0 ≤ deriv M (d.kPivot / s)) : ¬ d.Fits (fun k ↦ C * M (k / s)) := by
  rintro ⟨-, -, h⟩
  rw [spectralIndex_comp hC hs.ne' hM hM0.ne'] at h
  have : 0 ≤ d.kPivot / s * deriv M (d.kPivot / s) / M (d.kPivot / s) := by positivity
  linarith

end WhiteHole
