import HolographicUniverse.SecondOrder
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# `M(κ)` increases at every scale (ROADMAP M7.3, all `κ`)

`SecondOrder.lean` gives the sign of the `O(κ²)` term, so it covers small `κ` only. This file
removes that restriction: `m(t) = M(t e)` is strictly increasing on `[0, ∞)`
(`strictMonoOn_mRay`), and `M` depends only on `|κ|` (`thermalM_eq_mRay`). So
`|κ₁| < |κ₂| → M(κ₁) < M(κ₂)` (`thermalM_lt_of_norm_lt`), the spectrum `C·M(k/s)` has
`n_s > 1` at every `k > 0` (`spectralIndex_thermal_gt_one`), and it fits no release with
`n_s < 1`, wherever the pivot is (`ObsData.not_fits_thermal`).

**Method.** No new estimate is needed. Only signs are used.

1. *One integral.* `a1_eq` and `b1_eq` give `A′` and `B′` with `t` in the factor `φ`. Substitute
   `w ↦ -w` in `B′`. Then
   `B′(t) + A′(t) = ∫ g(w) φ(|w - te|) dw`, with `g(w) = ⟨w, e⟩/|w| · (1 + φ′(|w|))`
   (`b1_add_a1`).
2. *Reflection.* The reflection `ρ` in the hyperplane `e^⊥` preserves volume, `ρe = -e`, and
   `g ∘ ρ = -g`. So `2(B′ + A′) = ∫ g(w) [φ(|w - te|) - φ(|w + te|)] dw` (`two_mul_b1_add_a1`).
3. *Signs.* `1 + φ′ ≥ 1/2 > 0` (`abs_dphiB_le_half`), so `g` has the sign of `w₀ = ⟨w, e⟩`.
   `|w + te|² - |w - te|² = 4t w₀`, and `φ` is strictly decreasing on `(0, ∞)`
   (`strictAntiOn_phiB`). So for `t > 0` the bracket also has the sign of `w₀`, and the
   integrand is positive off the null set `w₀ = 0` (`gR_mul_diff_pos`).

In words: `B` pulls `M` down at a rate `φ′ ≥ -1/2` times the rate at which `A` pushes it up.
-/

namespace WhiteHole

open Real Set MeasureTheory Filter Topology

/-! ### `φ` is strictly decreasing -/

/-- `φ′(r) < 0` for `r > 0`: `(1 - r)eʳ < 1`. -/
theorem dphiB_neg {r : ℝ} (hr : 0 < r) : dphiB r < 0 := by
  rw [dphiB_eq hr]
  have hD : 0 < exp r - 1 := by linarith [add_one_lt_exp hr.ne']
  refine div_neg_of_neg_of_pos ?_ (by positivity)
  have h := add_one_lt_exp (show -r ≠ 0 by linarith)
  have hm : exp (-r) * exp r = 1 := by rw [← exp_add]; simp
  nlinarith [mul_lt_mul_of_pos_right h (exp_pos r)]

/-- **`φ(x) = x/(eˣ - 1)` is strictly decreasing on `(0, ∞)`.** -/
theorem strictAntiOn_phiB : StrictAntiOn phiB (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx ↦ (hasDerivAt_phiB (ne_of_gt hx)).continuousAt.continuousWithinAt) fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_phiB (ne_of_gt hx)).deriv]
  exact dphiB_neg hx

/-- `1 + φ′(r) > 0` for `r ≥ 0`, from `|φ′| ≤ 1/2`. -/
theorem one_add_dphiB_pos {r : ℝ} (hr : 0 ≤ r) : 0 < 1 + dphiB r := by
  have := (abs_le.1 (abs_dphiB_le_half hr)).1
  linarith

/-! ### The reflection in `e^⊥` -/

/-- The reflection `w₀ ↦ -w₀` in the hyperplane orthogonal to `e`. -/
noncomputable def reflR : E4 ≃ₗᵢ[ℝ] E4 := (ℝ ∙ eR)ᗮ.reflection

theorem reflR_eR : reflR eR = -eR :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg eR

theorem inner_reflR (w : E4) : inner ℝ (reflR w) eR = -inner ℝ w eR := by
  have h := reflR.inner_map_map w eR
  rw [reflR_eR, inner_neg_right] at h
  linarith

theorem norm_reflR_sub (w : E4) (t : ℝ) : ‖reflR w - t • eR‖ = ‖w + t • eR‖ := by
  rw [← reflR.norm_map (w + t • eR), map_add, map_smul, reflR_eR, smul_neg, sub_eq_add_neg]

/-- Almost every `w` has `w₀ ≠ 0`: the hyperplane `e^⊥` is a null set. -/
theorem ae_inner_eR_ne : ∀ᵐ w : E4, inner ℝ w eR ≠ 0 := by
  have hne : (ℝ ∙ eR)ᗮ ≠ ⊤ := by
    intro h
    have he : eR ∈ (ℝ ∙ eR)ᗮ := h ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq,
      norm_eR] at he
    norm_num at he
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_submodule volume _ hne)]
    with w hw
  exact fun h0 ↦ hw (Submodule.mem_orthogonal_singleton_iff_inner_left.2 h0)

/-! ### `B′ + A′` as one integral -/

/-- The odd weight `g(w) = ⟨w, e⟩/|w| · (1 + φ′(|w|))`. -/
noncomputable def gR (w : E4) : ℝ := inner ℝ w eR / ‖w‖ * (1 + dphiB ‖w‖)

@[fun_prop] theorem measurable_gR : Measurable gR := by
  unfold gR
  fun_prop

theorem abs_gR_le (w : E4) : |gR w| ≤ 3 / 2 := by
  rw [gR, abs_mul]
  have h1 := abs_inner_eR_div_le w
  have h2 := abs_le.1 (abs_dphiB_le_half (norm_nonneg w))
  have h3 : |1 + dphiB ‖w‖| ≤ 3 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  calc |inner ℝ w eR / ‖w‖| * |1 + dphiB ‖w‖| ≤ 1 * (3 / 2) :=
        mul_le_mul h1 h3 (abs_nonneg _) zero_le_one
    _ = 3 / 2 := one_mul _

theorem integrable_gR_mul (c : E4) : Integrable fun w ↦ gR w * phiR (w + c) :=
  (integrable_phiR.comp_add_right c).bdd_mul (c := 3 / 2) measurable_gR.aestronglyMeasurable
    (Eventually.of_forall fun w ↦ abs_gR_le w)

/-- **`B′ + A′` in one integral.** `B′(t) + A′(t) = ∫ g(w) φ(|w - te|) dw`. -/
theorem b1_add_a1 (t : ℝ) : b1 t + a1 t = ∫ w : E4, gR w * phiR (w - t • eR) := by
  have hb : b1 t = ∫ w : E4, inner ℝ w eR / ‖w‖ * dphiB ‖w‖ * phiR (w - t • eR) := by
    rw [b1_eq, ← integral_neg_eq_self
      (fun w ↦ phiR (w + t • eR) * (dphiB ‖w‖ * (-inner ℝ w eR / ‖w‖)))]
    congr 1
    funext w
    rw [show -w + t • eR = -(w - t • eR) by abel]
    simp only [phiR, inner_neg_left, norm_neg, neg_neg]
    ring
  have hi1 : Integrable fun w : E4 ↦ inner ℝ w eR / ‖w‖ * dphiB ‖w‖ * phiR (w - t • eR) :=
    (integrable_phiR.comp_sub_right (t • eR)).bdd_mul (c := 1 / 2)
      (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun w ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        calc |inner ℝ w eR / ‖w‖| * |dphiB ‖w‖| ≤ 1 * (1 / 2) :=
              mul_le_mul (abs_inner_eR_div_le w) (abs_dphiB_le_half (norm_nonneg w))
                (abs_nonneg _) zero_le_one
          _ = 1 / 2 := one_mul _)
  have hi2 : Integrable fun w : E4 ↦ inner ℝ w eR / ‖w‖ * phiR (w - t • eR) :=
    (integrable_phiR.comp_sub_right (t • eR)).bdd_mul (c := 1)
      (Measurable.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun w ↦ abs_inner_eR_div_le w)
  rw [hb, a1_eq, ← integral_add hi1 hi2]
  congr 1
  funext w
  unfold gR
  ring

/-- **Reflection.** `∫ g(w) φ(|w - te|) dw = -∫ g(w) φ(|w + te|) dw`. -/
theorem integral_gR_reflect (t : ℝ) :
    ∫ w : E4, gR w * phiR (w - t • eR) = -∫ w : E4, gR w * phiR (w + t • eR) := by
  have h := reflR.measurePreserving.integral_comp' (f := reflR.toMeasurableEquiv)
    (fun w : E4 ↦ gR w * phiR (w - t • eR))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at h
  rw [← h, ← integral_neg]
  congr 1
  funext w
  rw [gR, gR, inner_reflR, reflR.norm_map, phiR, phiR, norm_reflR_sub]
  ring

/-- `2(B′ + A′) = ∫ g(w) [φ(|w - te|) - φ(|w + te|)] dw`. -/
theorem two_mul_b1_add_a1 (t : ℝ) :
    2 * (b1 t + a1 t) = ∫ w : E4, gR w * (phiR (w - t • eR) - phiR (w + t • eR)) := by
  have e : (fun w : E4 ↦ gR w * (phiR (w - t • eR) - phiR (w + t • eR)))
      = fun w ↦ gR w * phiR (w + -(t • eR)) - gR w * phiR (w + t • eR) := by
    funext w
    rw [← sub_eq_add_neg, mul_sub]
  rw [e, integral_sub (integrable_gR_mul _) (integrable_gR_mul _), b1_add_a1]
  simp only [← sub_eq_add_neg]
  linarith [integral_gR_reflect t]

/-! ### The sign -/

/-- **The integrand is positive** for `t > 0`, off the line `ℝ e` and the hyperplane `w₀ = 0`. -/
theorem gR_mul_diff_pos {t : ℝ} (ht : 0 < t) {w : E4} (hw : w ∉ (ℝ ∙ eR))
    (h0 : inner ℝ w eR ≠ 0) : 0 < gR w * (phiR (w - t • eR) - phiR (w + t • eR)) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 fun h ↦ hw (h ▸ Submodule.zero_mem _)
  have h1 : 0 < ‖w - t • eR‖ := norm_pos_iff.2 (sub_smul_eR_ne hw t)
  have h2 : 0 < ‖w + t • eR‖ := norm_pos_iff.2 (add_smul_eR_ne hw t)
  have hsq : ‖w + t • eR‖ ^ 2 - ‖w - t • eR‖ ^ 2 = 4 * t * inner ℝ w eR := by
    rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right]
    ring
  have hd := one_add_dphiB_pos (norm_nonneg w)
  unfold gR phiR
  rcases h0.lt_or_gt with hneg | hpos
  · have hlt : ‖w + t • eR‖ < ‖w - t • eR‖ := by nlinarith
    have hphi : phiB ‖w - t • eR‖ < phiB ‖w + t • eR‖ := strictAntiOn_phiB h2 h1 hlt
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hneg hn) hd)
      (sub_neg.2 hphi)
  · have hlt : ‖w - t • eR‖ < ‖w + t • eR‖ := by nlinarith
    have hphi : phiB ‖w + t • eR‖ < phiB ‖w - t • eR‖ := strictAntiOn_phiB h1 h2 hlt
    exact mul_pos (mul_pos (div_pos hpos hn) hd) (sub_pos.2 hphi)

/-- **`B′ + A′ > 0` for every `t > 0`.** -/
theorem b1_add_a1_pos {t : ℝ} (ht : 0 < t) : 0 < b1 t + a1 t := by
  set f : E4 → ℝ := fun w ↦ gR w * (phiR (w - t • eR) - phiR (w + t • eR))
  have hpos : ∀ᵐ w : E4, 0 < f w := by
    filter_upwards [ae_notMem_span_eR, ae_inner_eR_ne] with w hw h0
    exact gR_mul_diff_pos ht hw h0
  have hint : Integrable f := by
    have := (integrable_gR_mul (-(t • eR))).sub (integrable_gR_mul (t • eR))
    refine this.congr (Eventually.of_forall fun w ↦ ?_)
    simp only [f, Pi.sub_apply, ← sub_eq_add_neg, mul_sub]
  have hI : 0 < ∫ w, f w := by
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun w h ↦ h.le) hint]
    by_contra hz
    rw [not_lt, nonpos_iff_eq_zero] at hz
    obtain ⟨w, h1, h2⟩ := (hpos.and (measure_eq_zero_iff_ae_notMem.1 hz)).exists
    exact h2 (Function.mem_support.2 h1.ne')
  linarith [two_mul_b1_add_a1 t]

/-! ### `M` increases at every scale -/

/-- **`m′(t) > 0` for every `t > 0`.** -/
theorem deriv_mRay_pos {t : ℝ} (ht : 0 < t) : 0 < deriv mRay t := by
  rw [(hasDerivAt_mRay t).deriv]
  exact div_pos (b1_add_a1_pos ht) (by positivity)

/-- **M7.3: `m` is strictly increasing on `[0, ∞)`.** -/
theorem strictMonoOn_mRay : StrictMonoOn mRay (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun t _ ↦ (hasDerivAt_mRay t).continuousAt.continuousWithinAt) fun t ht ↦ by
      rw [interior_Ici] at ht
      exact deriv_mRay_pos ht

theorem mRay_pos {t : ℝ} (ht : 0 ≤ t) : 0 < mRay t := by
  have hM0 : 0 < mRay 0 := by
    rw [mRay, zero_smul]
    linarith [thermalM_zero_bounds.1]
  rcases ht.eq_or_lt with rfl | ht
  · exact hM0
  · exact hM0.trans (strictMonoOn_mRay (mem_Ici.2 le_rfl) ht.le ht)

/-! ### `M` depends only on `|κ|` -/

theorem omegaPM_map (Q : E4 ≃ₗᵢ[ℝ] E4) (s : ℝ) (κ κ' : E4) :
    omegaPM s (Q κ) (Q κ') = omegaPM s κ κ' := by
  simp only [omegaPM, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map]

/-- **`M` is invariant under isometries of `ℝ⁴`.** -/
theorem thermalM_map (Q : E4 ≃ₗᵢ[ℝ] E4) (κ : E4) : thermalM (Q κ) = thermalM κ := by
  have h := Q.measurePreserving.integral_comp' (f := Q.toMeasurableEquiv)
    (fun κ' ↦ omegaPM 1 (Q κ) κ' * omegaPM (-1) (Q κ) κ'
      * (bose (omegaPM 1 (Q κ) κ') * bose (omegaPM (-1) (Q κ) κ')
        + (bose (omegaPM 1 (Q κ) κ') + bose (omegaPM (-1) (Q κ) κ')) / 2) / (2 * π) ^ 4)
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, omegaPM_map] at h
  unfold thermalM
  exact h.symm

/-- **`M(κ) = m(|κ|)`.** A reflection takes `κ` to `|κ| e`. -/
theorem thermalM_eq_mRay (κ : E4) : thermalM κ = mRay ‖κ‖ := by
  have h : ‖κ‖ = ‖‖κ‖ • eR‖ := by rw [norm_smul, norm_eR, mul_one, norm_norm]
  rw [mRay, ← thermalM_map (ℝ ∙ (κ - ‖κ‖ • eR))ᗮ.reflection κ,
    Submodule.reflection_sub h]

/-- **M7.3, all `κ`.** `M` is strictly increasing in `|κ|`. -/
theorem thermalM_lt_of_norm_lt {κ₁ κ₂ : E4} (h : ‖κ₁‖ < ‖κ₂‖) : thermalM κ₁ < thermalM κ₂ := by
  rw [thermalM_eq_mRay, thermalM_eq_mRay]
  exact strictMonoOn_mRay (norm_nonneg _) (norm_nonneg _) h

theorem thermalM_pos (κ : E4) : 0 < thermalM κ := by
  rw [thermalM_eq_mRay]
  exact mRay_pos (norm_nonneg _)

/-! ### The tilt -/

/-- **The spectrum is blue at every scale.** For `P(k) = C·M(k/s)` with `C ≠ 0` and `s > 0`,
`n_s(k) > 1` at every `k > 0`. -/
theorem spectralIndex_thermal_gt_one {C s k : ℝ} (hC : C ≠ 0) (hs : 0 < s) (hk : 0 < k) :
    1 < spectralIndex (fun k ↦ C * mRay (k / s)) k := by
  have hκ : 0 < k / s := div_pos hk hs
  rw [spectralIndex_comp hC hs.ne' (hasDerivAt_mRay _).differentiableAt (mRay_pos hκ.le).ne']
  have h1 := deriv_mRay_pos hκ
  have h2 := mRay_pos hκ.le
  have : 0 < k / s * deriv mRay (k / s) / mRay (k / s) := by positivity
  linarith

/-- **Third falsification theorem.** For a release with `n_s < 1`, no spectrum `C·M(k/s)` fits
it, for any amplitude `C`, any scale `s = a_b T_b > 0`, and so any `κ = k/s` at the pivot. This
is `ObsData.not_fits_next_order` without the condition that `κ` is small. -/
theorem ObsData.not_fits_thermal (d : ObsData) (hns : d.ns_hi < 1) {C s : ℝ} (hC : C ≠ 0)
    (hs : 0 < s) : ¬ d.Fits (fun k ↦ C * mRay (k / s)) := by
  rintro ⟨-, -, h⟩
  linarith [spectralIndex_thermal_gt_one hC hs d.kPivot_pos]

end WhiteHole
