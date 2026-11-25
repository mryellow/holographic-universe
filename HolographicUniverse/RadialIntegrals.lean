module

public import HolographicUniverse.NextOrder
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section

/-!
# Radial integrals of `φ′` (ROADMAP M7.3, step 1)

With `n(r) = 1/(eʳ - 1)` and `φ(r) = r n(r)`, the derivative is `φ′ = n - r n(1 + n)`
(`hasDerivAt_phiB`, `dphiB`). The second-order coefficient of `M(κ)` needs two radial integrals:

* `integral_dphiB`: `∫₀^∞ r³ φ′(r) dr = -π⁴/5`,
* `integral_dphiB_sq`: `∫₀^∞ r³ φ′(r)² dr = 2ζ(3) + π⁴/5 - 20ζ(5)`.

**Method.** With `x = e^{-r}`, each product of `n` and `1 + n` that appears is `xᵃ/(1 - x)^{k+1}`,
and `1/(1 - x)^{k+1} = Σ_j C(j + k, k) xʲ` (`hasSum_bose_pow`). Term by term,
`∫₀^∞ rᵖ e^{-(j+a)r} dr = p!/(j + a)^{p+1}` (`integral_pow_mul_exp`,
`integral_pow_mul_series`). The five sums that result reduce to `ζ(3)`, `ζ(4) = π⁴/90` and
`ζ(5)`.
-/

namespace WhiteHole

open Real Set MeasureTheory Filter Topology Nat

/-! ### `ζ(3)`, `ζ(4)`, and the shifted series -/

/-- `ζ(3) = Σ_{n ≥ 1} 1/n³`, as a real series. -/
noncomputable def zeta3 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

theorem hasSum_zeta3 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 3) zeta3 := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 3))
  push_cast at h
  exact h.hasSum

theorem hasSum_zeta4 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
  have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_four
  convert this using 1
  · funext n; push_cast; ring
  · simp

theorem hasSum_zeta5 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 5) zeta5 :=
  summable_zeta5.hasSum

/-- `ζ(3) ≤ ζ(2) = π²/6`. -/
theorem zeta3_le : zeta3 ≤ π ^ 2 / 6 := by
  have h2 := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have h2' : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    convert h2 using 1
    · funext n; push_cast; ring
    · simp
  refine hasSum_le (fun n ↦ ?_) hasSum_zeta3 h2'
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 (by norm_num))

/-- Dropping the first term: `Σ_{n ≥ 0} 1/(n + 2)ˢ = z - 1`. -/
theorem hasSum_shift_two {s : ℕ} {z : ℝ} (h : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s) z) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ s) (z - 1) := by
  have := (hasSum_nat_add_iff' 1).2 h
  convert this using 1
  · funext n; push_cast; ring
  · simp

/-! ### Term-wise integration -/

/-- `∫₀^∞ xᵖ e^{-rx} dx = p!/r^{p+1}`. -/
theorem integral_pow_mul_exp (p : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), x ^ p * exp (-(r * x)) = p ! / r ^ (p + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (p : ℝ) + 1) (r := r) (by positivity) hr
  rw [Gamma_nat_eq_factorial, add_sub_cancel_right,
    show (p : ℝ) + 1 = ((p + 1 : ℕ) : ℝ) by push_cast; ring, rpow_natCast] at h
  calc ∫ x in Ioi (0 : ℝ), x ^ p * exp (-(r * x))
      = ∫ x in Ioi (0 : ℝ), x ^ (p : ℝ) * exp (-(r * x)) := by simp_rw [rpow_natCast]
    _ = (1 / r) ^ (p + 1) * p ! := h
    _ = p ! / r ^ (p + 1) := by rw [one_div_pow]; ring

/-- **Term-wise integration.** If `F(r) = Σ_j c_j e^{-(j+a)r}` with `c_j ≥ 0`, then
`∫₀^∞ rᵖ F(r) dr = p! Σ_j c_j/(j + a)^{p+1}`, and the integrand is integrable. -/
theorem integral_pow_mul_series {c : ℕ → ℝ} {F : ℝ → ℝ} {a : ℝ} (p : ℕ) (ha : 0 < a)
    (hc : ∀ j, 0 ≤ c j) (hc0 : 0 < c 0)
    (hF : ∀ r : ℝ, 0 < r → HasSum (fun j : ℕ ↦ c j * exp (-(((j : ℝ) + a) * r))) (F r))
    (hs : Summable fun j : ℕ ↦ c j / ((j : ℝ) + a) ^ (p + 1)) :
    IntegrableOn (fun r ↦ r ^ p * F r) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), r ^ p * F r = p ! * ∑' j : ℕ, c j / ((j : ℝ) + a) ^ (p + 1) := by
  set G : ℕ → ℝ → ℝ := fun j r ↦ r ^ p * (c j * exp (-(((j : ℝ) + a) * r)))
  have hja : ∀ j : ℕ, (0 : ℝ) < j + a := fun j ↦ by positivity
  have hG : ∀ j, ∫ r in Ioi (0 : ℝ), G j r = c j * (p ! / ((j : ℝ) + a) ^ (p + 1)) := fun j ↦ by
    rw [← integral_pow_mul_exp p (hja j), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
    simp only [G]
    ring
  have hGi : ∀ j, Integrable (G j) (volume.restrict (Ioi 0)) := fun j ↦ by
    have := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p : ℝ)) (p := 1) (b := (j : ℝ) + a)
      (by linarith [Nat.cast_nonneg (α := ℝ) p]) one_pos (hja j)).const_mul (c j)
    refine IntegrableOn.congr_fun this (fun r _ ↦ ?_) measurableSet_Ioi
    simp only [G, rpow_natCast, rpow_one, neg_mul]
    ring
  have hnorm : ∀ j, ∫ r in Ioi (0 : ℝ), ‖G j r‖ = ∫ r in Ioi (0 : ℝ), G j r := fun j ↦
    setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦
      Real.norm_of_nonneg (by simp only [G]; have := hc j; positivity)
  have hsum : Summable fun j ↦ ∫ r in Ioi (0 : ℝ), ‖G j r‖ := by
    simp_rw [hnorm, hG]
    convert hs.mul_left (p ! : ℝ) using 1
    funext j
    ring
  have hval : ∫ r in Ioi (0 : ℝ), r ^ p * F r = ∑' j, ∫ r in Ioi (0 : ℝ), G j r := by
    rw [integral_tsum_of_summable_integral_norm hGi hsum]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    exact (((hF r hr).mul_left (r ^ p)).tsum_eq).symm
  have heq : ∫ r in Ioi (0 : ℝ), r ^ p * F r
      = p ! * ∑' j : ℕ, c j / ((j : ℝ) + a) ^ (p + 1) := by
    rw [hval]
    simp_rw [hG]
    rw [← tsum_mul_left]
    congr 1
    funext j
    ring
  refine ⟨Integrable.of_integral_ne_zero ?_, heq⟩
  rw [heq]
  refine (mul_pos (by positivity) (hs.tsum_pos (fun j ↦ ?_) 0 ?_)).ne'
  · have := hc j; have := hja j; positivity
  · have := hja 0; positivity

/-! ### The Bose series -/

/-- `xᵃ/(1 - x)^{k+1} = Σ_j C(j + k, k) e^{-(j+a)r}`, with `x = e^{-r}`. -/
theorem hasSum_bose_pow (k a : ℕ) {r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ ↦ ((j + k).choose k : ℝ) * exp (-(((j : ℝ) + a) * r)))
      (exp (-r) ^ a / (1 - exp (-r)) ^ (k + 1)) := by
  have hx0 : 0 < exp (-r) := exp_pos _
  have hx1 : exp (-r) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k
    (by rw [Real.norm_eq_abs, abs_of_pos hx0]; exact hx1)).mul_left (exp (-r) ^ a)
  convert h using 1
  · funext j
    simp only [← Real.exp_nat_mul]
    rw [mul_left_comm, ← exp_add]
    congr 2
    ring
  · ring

/-- `n(r) = x/(1 - x)` with `x = e^{-r}`. -/
theorem bose_eq_exp_neg {r : ℝ} (hr : 0 < r) : bose r = exp (-r) / (1 - exp (-r)) := by
  have he : exp r - 1 ≠ 0 := by linarith [add_one_lt_exp hr.ne']
  have hp := exp_pos r
  unfold bose
  rw [exp_neg]
  field_simp

/-- The five Bose series, in the form of `integral_pow_mul_series`. -/
theorem hasSum_bose_comb (k a : ℕ) {b : ℝ} (hb : (a : ℝ) = b) {r : ℝ} (hr : 0 < r) (F : ℝ)
    (hF : exp (-r) ^ a / (1 - exp (-r)) ^ (k + 1) = F) :
    HasSum (fun j : ℕ ↦ ((j + k).choose k : ℝ) * exp (-(((j : ℝ) + b) * r))) F := by
  subst hb hF
  exact hasSum_bose_pow k a hr

/-- Shorthand: `x = e^{-r}` with `1 - x ≠ 0`. -/
private theorem one_sub_exp_neg_ne {r : ℝ} (hr : 0 < r) : 1 - exp (-r) ≠ 0 := by
  linarith [Real.exp_lt_one_iff.2 (by linarith : -r < 0)]

/-! ### The five integrals -/

/-- `∫₀^∞ r³ n dr = 6ζ(4) = π⁴/15`. -/
theorem integral_bose_3 : IntegrableOn (fun r ↦ r ^ 3 * bose r) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), r ^ 3 * bose r = π ^ 4 / 15 := by
  have h := integral_pow_mul_series (c := fun j ↦ ((j + 0).choose 0 : ℝ)) (a := 1) (F := bose) 3
    one_pos (fun j ↦ by positivity) (by simp)
    (fun r hr ↦ hasSum_bose_comb 0 1 (by norm_num) hr (bose r) (by
      rw [bose_eq_exp_neg hr]; ring)) (by simpa using hasSum_zeta4.summable)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [add_zero, choose_zero_right, cast_one]
  rw [hasSum_zeta4.tsum_eq]
  norm_num [Nat.factorial]
  ring

/-- `∫₀^∞ r⁴ n(1 + n) dr = 24ζ(4)`. -/
theorem integral_bose_4 : IntegrableOn (fun r ↦ r ^ 4 * (bose r * (1 + bose r))) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), r ^ 4 * (bose r * (1 + bose r)) = 24 * (π ^ 4 / 90) := by
  have hs : HasSum (fun j : ℕ ↦ ((j + 1).choose 1 : ℝ) / ((j : ℝ) + 1) ^ (4 + 1)) (π ^ 4 / 90) := by
    convert hasSum_zeta4 using 1
    funext j
    rw [choose_one_right]
    push_cast
    have : (0 : ℝ) < j + 1 := by positivity
    field_simp
  have h := integral_pow_mul_series (c := fun j ↦ ((j + 1).choose 1 : ℝ)) (a := 1)
    (F := fun r ↦ bose r * (1 + bose r)) 4 one_pos (fun j ↦ by positivity) (by simp)
    (fun r hr ↦ hasSum_bose_comb 1 1 (by norm_num) hr (bose r * (1 + bose r)) (by
      have := one_sub_exp_neg_ne hr
      rw [bose_eq_exp_neg hr]; field_simp; ring)) (by exact_mod_cast hs.summable)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  push_cast at hs ⊢
  rw [hs.tsum_eq]
  norm_num [Nat.factorial]

/-- `Σ_j (j + 1)/(j + 2)⁴ = ζ(3) - ζ(4)`. -/
theorem hasSum_S3 : HasSum (fun j : ℕ ↦ ((j : ℝ) + 1) / ((j : ℝ) + 2) ^ 4)
    (zeta3 - π ^ 4 / 90) := by
  convert (hasSum_shift_two hasSum_zeta3).sub (hasSum_shift_two hasSum_zeta4) using 1
  · funext j
    have : (0 : ℝ) < j + 2 := by positivity
    field_simp
    ring
  · ring

/-- `Σ_j 1/(j + 2)³ - 1/(j + 2)⁵ = ζ(3) - ζ(5)`. -/
theorem hasSum_S5 : HasSum (fun j : ℕ ↦ ((j : ℝ) + 1) * ((j : ℝ) + 3) / ((j : ℝ) + 2) ^ 5)
    (zeta3 - zeta5) := by
  convert (hasSum_shift_two hasSum_zeta3).sub (hasSum_shift_two hasSum_zeta5) using 1
  · funext j
    have : (0 : ℝ) < j + 2 := by positivity
    field_simp
    ring
  · ring

/-- `∫₀^∞ r³ n² dr = 6(ζ(3) - ζ(4))`. -/
theorem integral_bose_sq : IntegrableOn (fun r ↦ r ^ 3 * bose r ^ 2) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), r ^ 3 * bose r ^ 2 = 6 * (zeta3 - π ^ 4 / 90) := by
  have hs : HasSum (fun j : ℕ ↦ ((j + 1).choose 1 : ℝ) / ((j : ℝ) + 2) ^ (3 + 1))
      (zeta3 - π ^ 4 / 90) := by
    convert hasSum_S3 using 1
    funext j
    rw [choose_one_right]
    push_cast
    ring
  have h := integral_pow_mul_series (c := fun j ↦ ((j + 1).choose 1 : ℝ)) (a := 2)
    (F := fun r ↦ bose r ^ 2) 3 two_pos (fun j ↦ by positivity) (by simp)
    (fun r hr ↦ by
      have := hasSum_bose_comb 1 2 (b := 2) (by norm_num) hr (bose r ^ 2) (by
        have := one_sub_exp_neg_ne hr
        rw [bose_eq_exp_neg hr]; field_simp)
      exact this) (by exact_mod_cast hs.summable)
  refine ⟨h.1, ?_⟩
  rw [h.2, hs.tsum_eq]
  norm_num [Nat.factorial]

/-- `∫₀^∞ r⁴ n²(1 + n) dr = 12(ζ(3) - ζ(4))`. -/
theorem integral_bose_sq_mul : IntegrableOn (fun r ↦ r ^ 4 * (bose r ^ 2 * (1 + bose r))) (Ioi 0)
    ∧ ∫ r in Ioi (0 : ℝ), r ^ 4 * (bose r ^ 2 * (1 + bose r)) = 12 * (zeta3 - π ^ 4 / 90) := by
  have hs : HasSum (fun j : ℕ ↦ ((j + 2).choose 2 : ℝ) / ((j : ℝ) + 2) ^ (4 + 1))
      ((zeta3 - π ^ 4 / 90) / 2) := by
    convert hasSum_S3.div_const 2 using 1
    funext j
    rw [cast_choose_two]
    push_cast
    have : (0 : ℝ) < j + 2 := by positivity
    field_simp
    ring
  have h := integral_pow_mul_series (c := fun j ↦ ((j + 2).choose 2 : ℝ)) (a := 2)
    (F := fun r ↦ bose r ^ 2 * (1 + bose r)) 4 two_pos (fun j ↦ by positivity) (by simp)
    (fun r hr ↦ by
      have := hasSum_bose_comb 2 2 (b := 2) (by norm_num) hr (bose r ^ 2 * (1 + bose r)) (by
        have := one_sub_exp_neg_ne hr
        rw [bose_eq_exp_neg hr]; field_simp; ring)
      exact this) (by exact_mod_cast hs.summable)
  refine ⟨h.1, ?_⟩
  rw [h.2, hs.tsum_eq]
  norm_num [Nat.factorial]
  ring

/-- `C(j + 3, 3) = (j + 1)(j + 2)(j + 3)/6`. -/
theorem cast_choose_three (j : ℕ) :
    ((j + 3).choose 3 : ℝ) = ((j : ℝ) + 1) * ((j : ℝ) + 2) * ((j : ℝ) + 3) / 6 := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq (j + 2) 2)
  push_cast at h
  rw [cast_choose_two] at h
  push_cast at h
  rw [show j + 2 + 1 = j + 3 by ring] at h
  linear_combination -h / 3

/-- `∫₀^∞ r⁵ (n(1 + n))² dr = 20(ζ(3) - ζ(5))`. -/
theorem integral_bose_mul_sq :
    IntegrableOn (fun r ↦ r ^ 5 * (bose r * (1 + bose r)) ^ 2) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), r ^ 5 * (bose r * (1 + bose r)) ^ 2 = 20 * (zeta3 - zeta5) := by
  have hs : HasSum (fun j : ℕ ↦ ((j + 3).choose 3 : ℝ) / ((j : ℝ) + 2) ^ (5 + 1))
      ((zeta3 - zeta5) / 6) := by
    convert hasSum_S5.div_const 6 using 1
    funext j
    rw [cast_choose_three]
    have : (0 : ℝ) < j + 2 := by positivity
    field_simp
  have h := integral_pow_mul_series (c := fun j ↦ ((j + 3).choose 3 : ℝ)) (a := 2)
    (F := fun r ↦ (bose r * (1 + bose r)) ^ 2) 5 two_pos (fun j ↦ by positivity) (by simp)
    (fun r hr ↦ by
      have := hasSum_bose_comb 3 2 (b := 2) (by norm_num) hr ((bose r * (1 + bose r)) ^ 2) (by
        have := one_sub_exp_neg_ne hr
        rw [bose_eq_exp_neg hr]; field_simp; ring)
      exact this) (by exact_mod_cast hs.summable)
  refine ⟨h.1, ?_⟩
  rw [h.2, hs.tsum_eq]
  norm_num [Nat.factorial]
  ring

/-! ### `φ′` and its two moments -/

/-- `φ′(r) = n - r n(1 + n)`. -/
noncomputable def dphiB (r : ℝ) : ℝ := bose r - r * (bose r * (1 + bose r))

/-- `φ′` is the derivative of `φ = r n(r)` away from `0`. -/
theorem hasDerivAt_phiB {r : ℝ} (hr : r ≠ 0) : HasDerivAt phiB (dphiB r) r := by
  have he : exp r - 1 ≠ 0 := sub_ne_zero.2 (mt (Real.exp_eq_one_iff r).1 hr)
  have hb : HasDerivAt (fun y ↦ 1 / (exp y - 1)) (-(exp r / (exp r - 1) ^ 2)) r := by
    have := (hasDerivAt_const r (1 : ℝ)).fun_div ((hasDerivAt_exp r).sub_const 1) he
    convert this using 1
    ring
  have h := (hasDerivAt_id' r).fun_mul hb
  have e : dphiB r = 1 * (1 / (exp r - 1)) + r * -(exp r / (exp r - 1) ^ 2) := by
    rw [← bose_add_sq hr]
    simp only [dphiB, bose]
    ring
  rw [e]
  exact h

/-- **`∫₀^∞ r³ φ′(r) dr = -π⁴/5`.** -/
theorem integral_dphiB : ∫ r in Ioi (0 : ℝ), r ^ 3 * dphiB r = -(π ^ 4 / 5) := by
  have e : (fun r ↦ r ^ 3 * dphiB r)
      = fun r ↦ r ^ 3 * bose r - r ^ 4 * (bose r * (1 + bose r)) := by
    funext r; unfold dphiB; ring
  rw [e, integral_sub integral_bose_3.1 integral_bose_4.1, integral_bose_3.2,
    integral_bose_4.2]
  ring

/-- **`∫₀^∞ r³ φ′(r)² dr = 2ζ(3) + π⁴/5 - 20ζ(5)`.** -/
theorem integral_dphiB_sq :
    ∫ r in Ioi (0 : ℝ), r ^ 3 * dphiB r ^ 2 = 2 * zeta3 + π ^ 4 / 5 - 20 * zeta5 := by
  have e : (fun r ↦ r ^ 3 * dphiB r ^ 2) = fun r ↦ r ^ 3 * bose r ^ 2
      - 2 * (r ^ 4 * (bose r ^ 2 * (1 + bose r))) + r ^ 5 * (bose r * (1 + bose r)) ^ 2 := by
    funext r; unfold dphiB; ring
  have i1 : IntegrableOn
      (fun r ↦ r ^ 3 * bose r ^ 2 - 2 * (r ^ 4 * (bose r ^ 2 * (1 + bose r)))) (Ioi 0) :=
    integral_bose_sq.1.sub (integral_bose_sq_mul.1.const_mul 2)
  rw [e, integral_add i1 integral_bose_mul_sq.1,
    integral_sub integral_bose_sq.1 (integral_bose_sq_mul.1.const_mul 2),
    integral_const_mul, integral_bose_sq.2, integral_bose_sq_mul.2, integral_bose_mul_sq.2]
  ring

/-- **The coefficient is positive.** `π⁴/5 - ∫ r³φ′² = 20ζ(5) - 2ζ(3) > 0`. -/
theorem integral_dphiB_sq_lt : ∫ r in Ioi (0 : ℝ), r ^ 3 * dphiB r ^ 2 < π ^ 4 / 5 := by
  rw [integral_dphiB_sq]
  have h3 := zeta3_le
  have h5 := zeta5_lower
  have := pi_lt_d2
  have : π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ this pi_pos.le (by norm_num)
  nlinarith

end WhiteHole
