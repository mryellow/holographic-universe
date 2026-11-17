import HolographicUniverse.RadialIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The second-order term of `M(κ)` (ROADMAP M7.3, steps 2 and 3)

Along the ray `κ = t e` with `e = (1, 0, 0, 0)`, write `m(t) = M(t e)` (`mRay`). The result is

  `m′(0) = 0`,  `m″(0) = (10ζ(5) - ζ(3))/(16π²) > 0`

(`deriv_mRay_zero`, `hasDerivAt_deriv_mRay`, `secondOrderCoeff_pos`). So
`M(κ) = M(0) + (10ζ(5) - ζ(3))/(32π²)·κ² + o(κ²)`, and for small `κ > 0` both `M > 0` and
`M′ > 0` (`next_order_blue`). The spectrum `C·M(k/s)` then has `n_s > 1` near `k = 0`, and fits
no data release with `n_s < 1` if the pivot is in that range (`ObsData.not_fits_next_order`).

**Method.** `(2π)⁴M = B + A` (`thermalM_eq`). The kernel `|v + κ|` of `A` has an unbounded
second derivative, so differentiate once only:

1. `A′(t) = ∫ ⟨v + te, e⟩/|v + te| · φ(|v|) dv` (`hasDerivAt_thermalA_ray`). The derivative
   of `|v + te|` is bounded by `1`. It exists for every `v` off the line `ℝ e`, a null set
   (`ae_notMem_span_eR`).
2. Shift `v = w - te`: `A′(t) = ∫ ⟨w, e⟩/|w| · φ(|w - te|) dw` (`a1_eq`). Now `t` sits in the
   smooth factor `φ`. Differentiate again at `t = 0` with the decay bound
   `|φ′(r)| ≤ (3 + 4r)e^{-r}` (`abs_dphiB_le_exp`).
3. Do the same for `B` (`hasDerivAt_thermalB_ray`, `b1_eq`), with `|φ′| ≤ 1/2`
   (`abs_dphiB_le_half`).
4. Angular average: `∫ (w₀/|w|)² g(|w|) = ¼ ∫ g(|w|)` (`integral_sq_coord_div`). The four
   coordinates are exchanged by isometries, which preserve volume.
5. Radial integral: `∫_{ℝ⁴} g(|w|) = 2π² ∫₀^∞ r³ g(r) dr` (`integral_radial`). With
   `RadialIntegrals.lean`, `A″(0) = π⁶/10` and `B″(0) = -(π²/2)(2ζ(3) + π⁴/5 - 20ζ(5))`.

**Scope.** This covers small `κ` only. `BlueTilt.lean` extends the sign of `m′` to every
`t > 0`, with `a1_eq` and `b1_eq` from this file.
-/

namespace WhiteHole

open Real Set MeasureTheory Filter Topology Metric

/-! ### The direction `e` -/

/-- The unit vector `e = (1, 0, 0, 0)`. -/
noncomputable def eR : E4 := EuclideanSpace.single 0 1

theorem norm_eR : ‖eR‖ = 1 := by simp [eR]

theorem inner_eR (w : E4) : inner ℝ w eR = w 0 := by
  simp [eR, EuclideanSpace.inner_single_right]

theorem abs_inner_eR_div_le (w : E4) : |inner ℝ w eR / ‖w‖| ≤ 1 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [abs_div, abs_norm, div_le_one (norm_pos_iff.2 hw)]
  simpa [norm_eR] using abs_real_inner_le_norm w eR

/-- Almost every `v` lies off the line `ℝ e`. -/
theorem ae_notMem_span_eR : ∀ᵐ v : E4, v ∉ (ℝ ∙ eR) := by
  have hne : (ℝ ∙ eR) ≠ ⊤ := by
    intro h
    have h0 : eR ≠ 0 := by
      intro h0
      have := norm_eR
      rw [h0, norm_zero] at this
      norm_num at this
    have h1 := finrank_span_singleton (K := ℝ) h0
    rw [h, finrank_top, finrank_euclideanSpace_fin] at h1
    norm_num at h1
  exact measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_submodule volume _ hne)

theorem add_smul_eR_ne {v : E4} (hv : v ∉ (ℝ ∙ eR)) (t : ℝ) : v + t • eR ≠ 0 := fun h ↦
  hv (Submodule.mem_span_singleton.2 ⟨-t, by rw [neg_smul]; exact neg_eq_of_add_eq_zero_left h⟩)

theorem sub_smul_eR_ne {v : E4} (hv : v ∉ (ℝ ∙ eR)) (t : ℝ) : v - t • eR ≠ 0 := fun h ↦
  hv (Submodule.mem_span_singleton.2 ⟨t, (sub_eq_zero.1 h).symm⟩)

theorem ae_ne_zero_E4 : ∀ᵐ v : E4, v ≠ 0 :=
  ae_notMem_span_eR.mono fun _ hv h0 ↦ hv (h0 ▸ Submodule.zero_mem _)

/-! ### Derivatives along a line -/

/-- `d/ds |v + sd| = ⟨v + sd, d⟩/|v + sd|` where `v + sd ≠ 0`. -/
theorem hasDerivAt_norm_add_smul {v d : E4} {t : ℝ} (h : v + t • d ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ ‖v + s • d‖) (inner ℝ (v + t • d) d / ‖v + t • d‖) t := by
  have hf : HasDerivAt (fun s : ℝ ↦ v + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add v
  have hpos : 0 < ‖v + t • d‖ := norm_pos_iff.2 h
  have hs := hf.norm_sq.sqrt (by positivity)
  simp only [sqrt_sq (norm_nonneg _)] at hs
  convert hs using 1
  field_simp

/-- `d/ds |v - sd| = -⟨v - sd, d⟩/|v - sd|` where `v - sd ≠ 0`. -/
theorem hasDerivAt_norm_sub_smul {v d : E4} {t : ℝ} (h : v - t • d ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ ‖v - s • d‖) (-inner ℝ (v - t • d) d / ‖v - t • d‖) t := by
  have h' : v + t • (-d) ≠ 0 := by rwa [smul_neg, ← sub_eq_add_neg]
  have := hasDerivAt_norm_add_smul h'
  simp only [smul_neg, ← sub_eq_add_neg, inner_neg_right] at this
  exact this

/-! ### Bounds on `φ′` -/

@[fun_prop] theorem measurable_dphiB : Measurable dphiB := by
  unfold dphiB bose
  fun_prop

theorem dphiB_eq {r : ℝ} (hr : 0 < r) :
    dphiB r = (exp r - 1 - r * exp r) / (exp r - 1) ^ 2 := by
  have he : exp r - 1 ≠ 0 := by linarith [add_one_lt_exp hr.ne']
  unfold dphiB bose
  field_simp
  ring

/-- `|φ′(r)| ≤ 1/2` for `r ≥ 0`. -/
theorem abs_dphiB_le_half {r : ℝ} (hr : 0 ≤ r) : |dphiB r| ≤ 1 / 2 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [dphiB, bose]
  have hE := exp_pos r
  have hD : 0 < exp r - 1 := by linarith [add_one_lt_exp hr.ne']
  have hm : exp (-r) * exp r = 1 := by rw [← exp_add]; simp
  have h1 : exp r - 1 - r * exp r ≤ 0 := by
    have := add_one_le_exp (-r)
    nlinarith
  have hp := phiB_le_exp hr.le
  rw [phiB, bose, mul_one_div, div_le_iff₀ hD] at hp
  have hu : exp (-(1 / 2) * r) * exp (r / 2) = 1 := by rw [← exp_add]; ring_nf; simp
  have hu2 : exp (r / 2) * exp (r / 2) = exp r := by rw [← exp_add]; ring_nf
  have hru : r * exp (r / 2) ≤ exp r - 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hp (exp_pos (r / 2)).le]
  have hsq : r ^ 2 * exp r ≤ (exp r - 1) ^ 2 := by
    rw [← hu2]
    nlinarith [mul_self_le_mul_self (by positivity) hru]
  have hq := quadratic_le_exp_of_nonneg hr.le
  have hq' : 0 < 1 - r + r ^ 2 / 2 := by nlinarith [sq_nonneg (r - 1)]
  have key : r * exp r - exp r + 1 ≤ r ^ 2 * exp r / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hq hq'.le, pow_nonneg hr.le 4]
  rw [dphiB_eq hr, abs_div, abs_of_nonpos h1, abs_of_pos (by positivity),
    div_le_iff₀ (by positivity)]
  nlinarith

/-- **Decay of `φ′`.** `|φ′(r)| ≤ (3 + 4r)e^{-r}` for `r ≥ 0`. -/
theorem abs_dphiB_le_exp {r : ℝ} (hr : 0 ≤ r) : |dphiB r| ≤ (3 + 4 * r) * exp (-r) := by
  rcases lt_or_ge r 1 with h1 | h1
  · have he1 : exp (-1) ≤ exp (-r) := exp_le_exp.2 (by linarith)
    have h3 : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
    have hm : exp (-1) * exp 1 = 1 := by rw [← exp_add]; simp
    have : 1 / 3 < exp (-1) := by nlinarith [exp_pos 1, exp_pos (-1)]
    calc |dphiB r| ≤ 1 / 2 := abs_dphiB_le_half hr
      _ ≤ (3 + 4 * r) * exp (-r) := by nlinarith [exp_pos (-r)]
  · have hE : 2 ≤ exp r := by linarith [add_one_le_exp r]
    have hm : exp (-r) * exp r = 1 := by rw [← exp_add]; simp
    have hD : 0 < exp r - 1 := by linarith
    have hn0 : 0 ≤ bose r := by unfold bose; positivity
    have hn1 : bose r ≤ 1 := by
      unfold bose
      rw [div_le_one hD]
      linarith
    have hn2 : bose r ≤ 2 * exp (-r) := by
      unfold bose
      rw [div_le_iff₀ hD]
      nlinarith [exp_pos (-r)]
    have hr0 : 0 ≤ r := hr
    unfold dphiB
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hn0, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul hn2 (by linarith : 1 + bose r ≤ 2) (by linarith) (by positivity),
      exp_pos (-r)]

/-- The decay bound at a point `x` within `R` of `w`. -/
theorem abs_dphiB_norm_le {x w : E4} {R : ℝ} (h : ‖x - w‖ ≤ R) :
    |dphiB ‖x‖| ≤ exp R * ((3 + 4 * R) * exp (-‖w‖) + 4 * (‖w‖ * exp (-‖w‖))) := by
  have h1 := abs_dphiB_le_exp (norm_nonneg x)
  have hxw : ‖x‖ ≤ ‖w‖ + R := by linarith [norm_le_norm_add_norm_sub' x w]
  have hwx : ‖w‖ - R ≤ ‖x‖ := by
    have := norm_le_norm_add_norm_sub' w x
    rw [norm_sub_rev] at this
    linarith
  have he : exp (-‖x‖) ≤ exp R * exp (-‖w‖) := by
    rw [← exp_add]
    exact exp_le_exp.2 (by linarith)
  have hR : 0 ≤ R := (norm_nonneg _).trans h
  calc |dphiB ‖x‖| ≤ (3 + 4 * ‖x‖) * exp (-‖x‖) := h1
    _ ≤ (3 + 4 * R + 4 * ‖w‖) * (exp R * exp (-‖w‖)) :=
        mul_le_mul (by linarith) he (exp_pos _).le (by positivity)
    _ = exp R * ((3 + 4 * R) * exp (-‖w‖) + 4 * (‖w‖ * exp (-‖w‖))) := by ring

/-! ### Integrability on `ℝ⁴` -/

theorem integrable_norm_pow_mul_exp (j : ℕ) :
    Integrable (fun w : E4 ↦ ‖w‖ ^ j * exp (-‖w‖)) := by
  rw [integrable_fun_norm_addHaar volume (f := fun y ↦ y ^ j * exp (-y)),
    finrank_euclideanSpace_fin]
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((3 + j : ℕ) : ℝ)) (p := 1)
    (b := 1) (by linarith [Nat.cast_nonneg (α := ℝ) (3 + j)]) one_pos one_pos
  refine hg.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
  simp only [rpow_natCast, rpow_one, smul_eq_mul, neg_mul, one_mul]
  rw [show 4 - 1 = 3 from rfl, pow_add]
  ring

theorem integrable_decay (R : ℝ) :
    Integrable (fun w : E4 ↦ exp R * ((3 + 4 * R) * exp (-‖w‖) + 4 * (‖w‖ * exp (-‖w‖)))) := by
  have h0 := integrable_norm_pow_mul_exp 0
  have h1 := integrable_norm_pow_mul_exp 1
  simp only [pow_zero, one_mul, pow_one] at h0 h1
  exact ((h0.const_mul _).add (h1.const_mul _)).const_mul _

theorem integrable_dphiB_norm : Integrable (fun w : E4 ↦ dphiB ‖w‖) := by
  refine (integrable_decay 0).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_dphiB_norm_le (x := w) (w := w) (by simp)

theorem integrable_dphiB_norm_sq : Integrable (fun w : E4 ↦ dphiB ‖w‖ ^ 2) := by
  refine (integrable_dphiB_norm.norm.const_mul (1 / 2)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w ↦ ?_)
  have h := abs_dphiB_le_half (norm_nonneg w)
  rw [Real.norm_eq_abs, abs_pow, Real.norm_eq_abs, sq]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-! ### Radial and angular integrals -/

/-- `∫_{ℝ⁴} g(|w|) dw = 2π² ∫₀^∞ r³ g(r) dr`. -/
theorem integral_radial (g : ℝ → ℝ) :
    ∫ w : E4, g ‖w‖ = 2 * π ^ 2 * ∫ r in Ioi (0 : ℝ), r ^ 3 * g r := by
  rw [integral_fun_norm_addHaar volume g, volume_ball_E4, finrank_euclideanSpace_fin,
    nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul, show 4 - 1 = 3 from rfl]
  ring

/-- **Angular average.** `∫ (w₀/|w|)² g(|w|) dw = ¼ ∫ g(|w|) dw`. -/
theorem integral_sq_coord_div {g : ℝ → ℝ} (hg : Integrable fun w : E4 ↦ g ‖w‖) :
    ∫ w : E4, (inner ℝ w eR / ‖w‖) ^ 2 * g ‖w‖ = 1 / 4 * ∫ w : E4, g ‖w‖ := by
  set f : Fin 4 → ℝ := fun i ↦ ∫ w : E4, (w i / ‖w‖) ^ 2 * g ‖w‖
  have hle : ∀ (i : Fin 4) (w : E4), (w i / ‖w‖) ^ 2 ≤ 1 := fun i w ↦ by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    rw [div_pow, div_le_one (by positivity), EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun j ↦ w j ^ 2) (fun j _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  have hint : ∀ i : Fin 4, Integrable fun w : E4 ↦ (w i / ‖w‖) ^ 2 * g ‖w‖ := fun i ↦
    hg.bdd_mul (c := 1)
      ((((EuclideanSpace.proj i).continuous.measurable.div measurable_norm).pow_const
        2).aestronglyMeasurable)
      (Eventually.of_forall fun w ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hle i w)
  have hsym : ∀ i, f i = f 0 := fun i ↦ by
    let σ : E4 ≃ₗᵢ[ℝ] E4 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 i)
    have hσ : ∀ w : E4, σ w 0 = w i := fun w ↦ by
      simp [σ, Equiv.piCongrLeft']
    have h := σ.measurePreserving.integral_comp' (f := σ.toMeasurableEquiv)
      (fun w : E4 ↦ (w 0 / ‖w‖) ^ 2 * g ‖w‖)
    simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, hσ, LinearIsometryEquiv.norm_map] at h
    exact h
  have hsum : ∑ i, f i = ∫ w : E4, g ‖w‖ := by
    rw [← integral_finsetSum _ fun i _ ↦ hint i]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_E4] with w hw
    rw [← Finset.sum_mul]
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have : ∑ i, (w i / ‖w‖) ^ 2 = 1 := by
      simp_rw [div_pow]
      rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq, div_self (by positivity)]
    rw [this, one_mul]
  rw [Fin.sum_univ_four, hsym 1, hsym 2, hsym 3] at hsum
  simp only [inner_eR]
  change f 0 = _
  linarith

/-- An odd integrand integrates to zero. -/
theorem integral_odd_eq_zero {f : E4 → ℝ} (h : ∀ w, f (-w) = -f w) : ∫ w, f w = 0 := by
  have := integral_neg_eq_self f (volume : Measure E4)
  rw [show (fun w ↦ f (-w)) = fun w ↦ -f w from funext h, integral_neg] at this
  linarith

/-! ### `A″(0)` -/

/-- `A′(t)` along the ray. -/
noncomputable def a1 (t : ℝ) : ℝ := ∫ v : E4, inner ℝ (v + t • eR) eR / ‖v + t • eR‖ * phiR v

/-- **`A′(t)`.** -/
theorem hasDerivAt_thermalA_ray (t₀ : ℝ) :
    HasDerivAt (fun t ↦ thermalA (t • eR)) (a1 t₀) t₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := univ)
    (x₀ := t₀) (F := fun t v ↦ ‖v + t • eR‖ * phiR v)
    (F' := fun t v ↦ inner ℝ (v + t • eR) eR / ‖v + t • eR‖ * phiR v) (bound := phiR)
    univ_mem (Eventually.of_forall fun t ↦ (integrable_thermalA (t • eR)).aestronglyMeasurable)
    (integrable_thermalA (t₀ • eR)) (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun v x _ ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phiR_nonneg v)]
      exact mul_le_of_le_one_left (phiR_nonneg v) (abs_inner_eR_div_le _))
    integrable_phiR
    (ae_notMem_span_eR.mono fun v hv x _ ↦
      (hasDerivAt_norm_add_smul (add_smul_eR_ne hv x)).mul_const (phiR v))
  exact key.2

/-- **Shift.** `A′(t) = ∫ ⟨w, e⟩/|w| · φ(|w - te|) dw`. -/
theorem a1_eq (t : ℝ) : a1 t = ∫ w : E4, inner ℝ w eR / ‖w‖ * phiR (w - t • eR) := by
  rw [a1, ← integral_add_right_eq_self (fun w ↦ inner ℝ w eR / ‖w‖ * phiR (w - t • eR)) (t • eR)]
  simp only [add_sub_cancel_right]

theorem a1_zero : a1 0 = 0 := by
  rw [a1_eq]
  refine integral_odd_eq_zero fun w ↦ ?_
  simp only [zero_smul, sub_zero, inner_neg_left, norm_neg, phiR]
  ring

/-- **`A″(0) = π⁶/10`.** -/
theorem hasDerivAt_a1_zero : HasDerivAt a1 (π ^ 6 / 10) 0 := by
  have hfun : a1 = fun t ↦ ∫ w : E4, inner ℝ w eR / ‖w‖ * phiR (w - t • eR) := funext a1_eq
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := ball (0 : ℝ) 1) (x₀ := 0)
    (F := fun t w ↦ inner ℝ w eR / ‖w‖ * phiR (w - t • eR))
    (F' := fun t w ↦ inner ℝ w eR / ‖w‖
      * (dphiB ‖w - t • eR‖ * (-inner ℝ (w - t • eR) eR / ‖w - t • eR‖)))
    (bound := fun w ↦ exp 1 * ((3 + 4 * 1) * exp (-‖w‖) + 4 * (‖w‖ * exp (-‖w‖))))
    (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t ↦ by
      apply Measurable.aestronglyMeasurable
      unfold phiR
      fun_prop)
    (by
      simp only [zero_smul, sub_zero]
      refine integrable_phiR.bdd_mul (c := 1) (Measurable.aestronglyMeasurable (by fun_prop))
        (Eventually.of_forall fun w ↦ abs_inner_eR_div_le w))
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w t ht ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := abs_inner_eR_div_le w
      have h2 : |-inner ℝ (w - t • eR) eR / ‖w - t • eR‖| ≤ 1 := by
        rw [neg_div, abs_neg]; exact abs_inner_eR_div_le _
      have h3 := abs_dphiB_norm_le (x := w - t • eR) (w := w) (R := 1) (by
        rw [sub_sub_cancel_left, norm_neg, norm_smul, norm_eR, mul_one, Real.norm_eq_abs]
        exact (mem_ball_zero_iff.1 ht).le)
      calc |inner ℝ w eR / ‖w‖| * (|dphiB ‖w - t • eR‖|
            * |-inner ℝ (w - t • eR) eR / ‖w - t • eR‖|)
          ≤ 1 * (|dphiB ‖w - t • eR‖| * 1) := by gcongr
        _ ≤ _ := by rw [one_mul, mul_one]; exact h3)
    (integrable_decay 1)
    (ae_notMem_span_eR.mono fun w hw t _ ↦ by
      have hn := sub_smul_eR_ne hw t
      exact ((hasDerivAt_phiB (norm_ne_zero_iff.2 hn)).comp t
        (hasDerivAt_norm_sub_smul hn)).const_mul _)
  rw [hfun]
  convert key.2 using 1
  simp only [zero_smul, sub_zero]
  have e : (fun w : E4 ↦ inner ℝ w eR / ‖w‖ * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)))
      = fun w ↦ -((inner ℝ w eR / ‖w‖) ^ 2 * dphiB ‖w‖) := by
    funext w; ring
  rw [e, integral_neg, integral_sq_coord_div integrable_dphiB_norm, integral_radial,
    integral_dphiB]
  ring

/-! ### `B″(0)` -/

/-- `B′(t)` along the ray. -/
noncomputable def b1 (t : ℝ) : ℝ :=
  ∫ u : E4, phiR u * (dphiB ‖u - t • eR‖ * (-inner ℝ (u - t • eR) eR / ‖u - t • eR‖))

/-- **`B′(t)`.** -/
theorem hasDerivAt_thermalB_ray (t₀ : ℝ) :
    HasDerivAt (fun t ↦ thermalB (t • eR)) (b1 t₀) t₀ := by
  set R := |t₀| + 1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := ball t₀ 1) (x₀ := t₀) (F := fun t u ↦ phiR u * phiR (u - t • eR))
    (F' := fun t u ↦ phiR u
      * (dphiB ‖u - t • eR‖ * (-inner ℝ (u - t • eR) eR / ‖u - t • eR‖)))
    (bound := fun u ↦ exp R * ((3 + 4 * R) * exp (-‖u‖) + 4 * (‖u‖ * exp (-‖u‖))))
    (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t ↦ (integrable_thermalB (t • eR)).aestronglyMeasurable)
    (integrable_thermalB (t₀ • eR)) (Measurable.aestronglyMeasurable (by unfold phiR; fun_prop))
    (Eventually.of_forall fun u t ht ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |phiR u| ≤ 1 := by rw [← Real.norm_eq_abs]; exact norm_phiR_le u
      have h2 : |-inner ℝ (u - t • eR) eR / ‖u - t • eR‖| ≤ 1 := by
        rw [neg_div, abs_neg]; exact abs_inner_eR_div_le _
      have h3 := abs_dphiB_norm_le (x := u - t • eR) (w := u) (R := R) (by
        rw [sub_sub_cancel_left, norm_neg, norm_smul, norm_eR, mul_one, Real.norm_eq_abs]
        have := mem_ball_iff_norm.1 ht
        rw [Real.norm_eq_abs] at this
        simp only [R]
        linarith [abs_sub_abs_le_abs_sub t t₀])
      calc |phiR u| * (|dphiB ‖u - t • eR‖| * |-inner ℝ (u - t • eR) eR / ‖u - t • eR‖|)
          ≤ 1 * (|dphiB ‖u - t • eR‖| * 1) := by gcongr
        _ ≤ _ := by rw [one_mul, mul_one]; exact h3)
    (integrable_decay R)
    (ae_notMem_span_eR.mono fun u hu t _ ↦ by
      have hn := sub_smul_eR_ne hu t
      exact ((hasDerivAt_phiB (norm_ne_zero_iff.2 hn)).comp t
        (hasDerivAt_norm_sub_smul hn)).const_mul _)
  exact key.2

/-- **Shift.** `B′(t) = -∫ φ(|w + te|) φ′(|w|) ⟨w, e⟩/|w| dw`. -/
theorem b1_eq (t : ℝ) :
    b1 t = ∫ w : E4, phiR (w + t • eR) * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)) := by
  rw [b1, ← integral_sub_right_eq_self
    (fun w ↦ phiR (w + t • eR) * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖))) (t • eR)]
  simp only [sub_add_cancel]

theorem b1_zero : b1 0 = 0 := by
  rw [b1_eq]
  refine integral_odd_eq_zero fun w ↦ ?_
  simp only [zero_smul, add_zero, inner_neg_left, norm_neg, phiR]
  ring

/-- **`B″(0) = -(π²/2) ∫₀^∞ r³φ′² dr`.** -/
theorem hasDerivAt_b1_zero :
    HasDerivAt b1 (-(π ^ 2 / 2) * (2 * zeta3 + π ^ 4 / 5 - 20 * zeta5)) 0 := by
  have hfun : b1 = fun t ↦ ∫ w : E4, phiR (w + t • eR) * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)) :=
    funext b1_eq
  have hk : ∀ w : E4, |dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)| ≤ |dphiB ‖w‖| := fun w ↦ by
    rw [abs_mul, neg_div, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_inner_eR_div_le w)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := (univ : Set ℝ)) (x₀ := (0 : ℝ))
    (F := fun t w ↦ phiR (w + t • eR) * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)))
    (F' := fun t w ↦ dphiB ‖w + t • eR‖ * (inner ℝ (w + t • eR) eR / ‖w + t • eR‖)
      * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)))
    (bound := fun w ↦ 1 / 2 * (exp 0 * ((3 + 4 * 0) * exp (-‖w‖) + 4 * (‖w‖ * exp (-‖w‖)))))
    univ_mem
    (Eventually.of_forall fun t ↦ by
      apply Measurable.aestronglyMeasurable
      unfold phiR
      fun_prop)
    (by
      simp only [zero_smul, add_zero]
      refine integrable_dphiB_norm.norm.mono'
        (Measurable.aestronglyMeasurable (by unfold phiR; fun_prop))
        (Eventually.of_forall fun w ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have h1 : |phiR w| ≤ 1 := by rw [← Real.norm_eq_abs]; exact norm_phiR_le w
      calc |phiR w| * |dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)|
          ≤ 1 * |dphiB ‖w‖| := mul_le_mul h1 (hk w) (abs_nonneg _) zero_le_one
        _ = |dphiB ‖w‖| := one_mul _)
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w t _ ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := abs_dphiB_le_half (norm_nonneg (w + t • eR))
      have h2 := abs_inner_eR_div_le (w + t • eR)
      have h3 := abs_dphiB_norm_le (x := w) (w := w) (R := 0) (by simp)
      calc |dphiB ‖w + t • eR‖| * |inner ℝ (w + t • eR) eR / ‖w + t • eR‖|
            * |dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)|
          ≤ 1 / 2 * 1 * |dphiB ‖w‖| :=
            mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) (hk w) (abs_nonneg _)
              (by norm_num)
        _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h3 (by norm_num))
    ((integrable_decay 0).const_mul (1 / 2))
    (ae_notMem_span_eR.mono fun w hw t _ ↦ by
      have hn := add_smul_eR_ne hw t
      exact ((hasDerivAt_phiB (norm_ne_zero_iff.2 hn)).comp t
        (hasDerivAt_norm_add_smul hn)).mul_const _)
  rw [hfun]
  convert key.2 using 1
  simp only [zero_smul, add_zero]
  have e : (fun w : E4 ↦ dphiB ‖w‖ * (inner ℝ w eR / ‖w‖) * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)))
      = fun w ↦ -((inner ℝ w eR / ‖w‖) ^ 2 * dphiB ‖w‖ ^ 2) := by
    funext w; ring
  rw [e, integral_neg, integral_sq_coord_div (g := fun r ↦ dphiB r ^ 2) integrable_dphiB_norm_sq,
    integral_radial (fun r ↦ dphiB r ^ 2), integral_dphiB_sq]
  ring

/-! ### `M″(0)` and the tilt -/

/-- `M` along the ray, `m(t) = M(t e)`. -/
noncomputable def mRay (t : ℝ) : ℝ := thermalM (t • eR)

/-- The second derivative `m″(0) = (10ζ(5) - ζ(3))/(16π²)`. -/
noncomputable def secondOrderCoeff : ℝ := (10 * zeta5 - zeta3) / (16 * π ^ 2)

theorem secondOrderCoeff_pos : 0 < secondOrderCoeff := by
  have h3 := zeta3_le
  have h5 := zeta5_lower
  have : π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ pi_lt_d2 pi_pos.le (by norm_num)
  unfold secondOrderCoeff
  apply div_pos _ (by positivity)
  nlinarith

theorem hasDerivAt_mRay (t : ℝ) : HasDerivAt mRay ((b1 t + a1 t) / (2 * π) ^ 4) t := by
  have e : mRay = fun t ↦ (thermalB (t • eR) + thermalA (t • eR)) / (2 * π) ^ 4 :=
    funext fun t ↦ thermalM_eq _
  rw [e]
  exact ((hasDerivAt_thermalB_ray t).add (hasDerivAt_thermalA_ray t)).div_const _

theorem deriv_mRay : deriv mRay = fun t ↦ (b1 t + a1 t) / (2 * π) ^ 4 :=
  funext fun t ↦ (hasDerivAt_mRay t).deriv

/-- **`m′(0) = 0`.** -/
theorem deriv_mRay_zero : deriv mRay 0 = 0 := by
  rw [deriv_mRay]
  simp [a1_zero, b1_zero]

/-- **M7.3: `m″(0) = (10ζ(5) - ζ(3))/(16π²)`.** -/
theorem hasDerivAt_deriv_mRay : HasDerivAt (deriv mRay) secondOrderCoeff 0 := by
  rw [deriv_mRay]
  convert (hasDerivAt_b1_zero.add hasDerivAt_a1_zero).div_const ((2 * π) ^ 4) using 1
  unfold secondOrderCoeff
  have := pi_pos
  field_simp
  ring

/-- **The next order is blue.** For small `t > 0`, `m(t) > 0` and `m′(t) > 0`. -/
theorem next_order_blue : ∃ δ > 0, ∀ t ∈ Ioo 0 δ, 0 < mRay t ∧ 0 < deriv mRay t := by
  have hM0 : 0 < mRay 0 := by
    rw [mRay, zero_smul]
    linarith [thermalM_zero_bounds.1]
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < mRay t :=
    nhdsWithin_le_nhds ((hasDerivAt_mRay 0).continuousAt.eventually (lt_mem_nhds hM0))
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < deriv mRay t := by
    have h := hasDerivAt_deriv_mRay.tendsto_slope_zero_right.eventually
      (lt_mem_nhds secondOrderCoeff_pos)
    filter_upwards [h, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
    rw [zero_add, deriv_mRay_zero, sub_zero, smul_eq_mul] at ht
    exact (mul_pos_iff_of_pos_left (inv_pos.2 htpos)).1 ht
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h1.and h2)
  exact ⟨δ, hδ, fun t ht ↦ hsub ht⟩

/-- **The next order cannot produce a red tilt.** For any release with `n_s < 1`, there is a
`δ > 0` such that no spectrum `C·M(k/s)` fits it with the pivot at `κ = k/s ∈ (0, δ)`. -/
theorem ObsData.not_fits_next_order (d : ObsData) (hns : d.ns_hi < 1) :
    ∃ δ > 0, ∀ {C s : ℝ}, C ≠ 0 → 0 < s → d.kPivot / s ∈ Ioo 0 δ →
      ¬ d.Fits (fun k ↦ C * mRay (k / s)) := by
  obtain ⟨δ, hδ, h⟩ := next_order_blue
  refine ⟨δ, hδ, fun {C s} hC hs hk ↦ ?_⟩
  obtain ⟨hM, hM'⟩ := h _ hk
  exact d.not_fits_of_deriv_nonneg hns ((div_pos_iff_of_pos_right hs).1 hk.1).le hC hs
    (hasDerivAt_mRay _).differentiableAt hM hM'.le

end WhiteHole
