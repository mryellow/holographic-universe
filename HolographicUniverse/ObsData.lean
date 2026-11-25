module

public import HolographicUniverse.Perturbations
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Observational data as parameters (ROADMAP M1.5)

The project's ground rules say that observational numbers are parameters, not constants, so that
a new data release does not mean rewriting proofs. `ObsData` bundles the numbers the Sec. 4–5
results depend on. The general theorems (`ObsData.tbm5_bounds`, `ObsData.eq51`) take an
`ObsData`. A data release is an instance, and a result for that release is one `norm_num` check.

Two instances:

* `planck2013`: the values the paper uses.
* `planck2018`: Planck 2018 VI (arXiv:1807.06209), TT,TE,EE+lowE+lensing. The amplitude is
  published as `ln(10¹⁰ A_s) = 3.044 ± 0.014`. The instance stores exactly that, as
  `exp(3.030)·10⁻¹⁰ ≤ A_s ≤ exp(3.058)·10⁻¹⁰`, and `exp` is bounded in the proofs.

Results:

* `eq49_planck2013_sharp`: `T_b/M₅ ∈ [0.17061, 0.17216]`. This reproduces the paper's
  `0.17139 ± 0.00077 = [0.17062, 0.17216]` to the last digit.
* `eq49_planck2018`: `T_b/M₅ ∈ [0.1697, 0.17051]`, i.e. `0.1701 ± 0.0004`.
* `planck2013_planck2018_disjoint`: the two 1σ intervals for `T_b/M₅` do not overlap. This is
  a fact about the two data releases (their 1σ amplitude intervals are already disjoint). It is
  **not** evidence against the model: `T_b/M₅` is a fitted parameter, and the newer data only
  move it. The consequence for the formalization is that a theorem instantiated with the 2013
  numbers says nothing about the 2018 numbers.

All numbers are 1σ intervals. Check them against the cited papers before quoting them.
-/

namespace WhiteHole

open Real

/-- The observational inputs to the Sec. 4–5 results, for one data release. -/
structure ObsData where
  /-- Scalar amplitude `A_s` at the pivot scale: lower end of the interval. -/
  A_lo : ℝ
  /-- Scalar amplitude `A_s` at the pivot scale: upper end of the interval. -/
  A_hi : ℝ
  /-- Pivot scale `k_*`, in `Mpc⁻¹`. -/
  kPivot : ℝ
  /-- Scalar spectral index `n_s`: lower end of the interval. -/
  ns_lo : ℝ
  /-- Scalar spectral index `n_s`: upper end of the interval. -/
  ns_hi : ℝ
  /-- Lower bound on the DGP crossover scale in Hubble units: `r_c ≥ rcH0 / H₀` (Eq. (51)). -/
  rcH0 : ℝ
  A_lo_pos : 0 < A_lo
  A_le : A_lo ≤ A_hi
  kPivot_pos : 0 < kPivot
  ns_le : ns_lo ≤ ns_hi
  rcH0_pos : 0 < rcH0

namespace ObsData

variable (d : ObsData)

/-- **Eq. (49) for any data release.** If the amplitude is the leading-order prediction
`A = ampCoeff · (T_b/M₅)⁶` and lies in the release's interval, then `T_b/M₅ ∈ [y_lo, y_hi]` for
any `y_lo, y_hi` that pass the two numerical checks. The coefficient enters through
`ampCoeff_sharp`. -/
theorem tbm5_bounds {y A ylo yhi : ℝ} (hy : 0 < y) (hA : A = ampCoeff * y ^ 6)
    (hAobs : d.A_lo ≤ A ∧ A ≤ d.A_hi) (hyhi : 0 ≤ yhi)
    (hlo : ylo ^ 6 * 8.6631e-5 ≤ d.A_lo) (hhi : d.A_hi ≤ yhi ^ 6 * 8.6627e-5) :
    ylo ≤ y ∧ y ≤ yhi :=
  amplitude_inversion hy hA ampCoeff_sharp hAobs (by norm_num) hyhi hlo hhi

/-- **Eq. (51) for any data release.** `r_c ≥ rcH0 / H₀` gives `M₅³ ≤ H₀ M₄² / (2 rcH0)`. -/
theorem eq51 (c : Couplings) {M4 M5 H0 : ℝ} (h4 : c.IsM4 M4) (h5 : c.IsM5 M5) (hH0 : 0 < H0)
    (hrc : d.rcH0 / H0 ≤ c.rc) : M5 ^ 3 ≤ H0 * M4 ^ 2 / (2 * d.rcH0) := by
  have := d.rcH0_pos
  have hM5 := pow_pos h5.1 3
  rw [c.rc_eq_planck h4 h5, div_le_div_iff₀ hH0 (by positivity)] at hrc
  rw [le_div_iff₀ (by positivity)]
  linarith

end ObsData

/-! ## Planck 2013 -/

/-- **Planck 2013**, as used in the paper: `A_s = (2.196 ± 0.059)×10⁻⁹`,
`n_s = 0.9603 ± 0.0073` (Planck 2013 XVI, Planck + WMAP polarization), pivot `0.05 Mpc⁻¹`, and
the paper's `r_c ≳ 3/H₀`. -/
noncomputable def planck2013 : ObsData where
  A_lo := 2.137e-9
  A_hi := 2.255e-9
  kPivot := 0.05
  ns_lo := 0.9530
  ns_hi := 0.9676
  rcH0 := 3
  A_lo_pos := by norm_num
  A_le := by norm_num
  kPivot_pos := by norm_num
  ns_le := by norm_num
  rcH0_pos := by norm_num

/-- **Eq. (49), Planck 2013, sharp.** `T_b/M₅ ∈ [0.17061, 0.17216]`. The paper quotes
`0.17139 ± 0.00077 = [0.17062, 0.17216]`. -/
theorem eq49_planck2013_sharp {y A : ℝ} (hy : 0 < y) (hA : A = ampCoeff * y ^ 6)
    (hAobs : planck2013.A_lo ≤ A ∧ A ≤ planck2013.A_hi) : 0.17061 ≤ y ∧ y ≤ 0.17216 :=
  planck2013.tbm5_bounds hy hA hAobs (by norm_num) (by norm_num [planck2013])
    (by norm_num [planck2013])

/-! ## Planck 2018 -/

/-- **Planck 2018** (arXiv:1807.06209, TT,TE,EE+lowE+lensing): `ln(10¹⁰ A_s) = 3.044 ± 0.014`,
stored without rounding as `A_s ∈ [exp(3.030), exp(3.058)]·10⁻¹⁰`; `n_s = 0.9649 ± 0.0042`;
pivot `0.05 Mpc⁻¹`; `r_c ≳ 3/H₀` as in the paper. -/
noncomputable def planck2018 : ObsData where
  A_lo := exp 3.030 * 1e-10
  A_hi := exp 3.058 * 1e-10
  kPivot := 0.05
  ns_lo := 0.9607
  ns_hi := 0.9691
  rcH0 := 3
  A_lo_pos := by positivity
  A_le := by gcongr; norm_num
  kPivot_pos := by norm_num
  ns_le := by norm_num
  rcH0_pos := by norm_num

/-- `exp 3 = e³`, bounded with Mathlib's nine-digit bounds on `e`. -/
private lemma exp_three_bounds : 2.7182818283 ^ 3 < exp 3 ∧ exp 3 < 2.7182818286 ^ 3 := by
  have h : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  exact ⟨pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num),
    pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)⟩

/-- `exp(3.030) ≥ e³ (1 + 0.03 + 0.03²/2)`. -/
private lemma exp_3030_lower : 20.6971 ≤ exp 3.030 := by
  have h : exp 3.030 = exp 3 * exp 0.03 := by rw [← exp_add]; norm_num
  have hq := quadratic_le_exp_of_nonneg (x := 0.03) (by norm_num)
  have he := exp_three_bounds.1
  rw [h]
  norm_num at hq he ⊢
  nlinarith [exp_pos 3]

/-- `exp(3.058) ≤ e³ (1 + x + x²/2 + 4x³/18)` with `x = 0.058` (`Real.exp_bound'`, three terms). -/
private lemma exp_3058_upper : exp 3.058 ≤ 21.2862 := by
  have h : exp 3.058 = exp 3 * exp 0.058 := by rw [← exp_add]; norm_num
  have hb := exp_bound' (x := 0.058) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  have he := exp_three_bounds.2
  rw [h]
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb he ⊢
  nlinarith [exp_pos 3, exp_pos 0.058]

/-- **Eq. (49), Planck 2018.** `T_b/M₅ ∈ [0.1697, 0.17051]`, i.e. `0.1701 ± 0.0004`. -/
theorem eq49_planck2018 {y A : ℝ} (hy : 0 < y) (hA : A = ampCoeff * y ^ 6)
    (hAobs : planck2018.A_lo ≤ A ∧ A ≤ planck2018.A_hi) : 0.1697 ≤ y ∧ y ≤ 0.17051 := by
  refine planck2018.tbm5_bounds hy hA hAobs (by norm_num) ?_ ?_
  · change (0.1697 : ℝ) ^ 6 * 8.6631e-5 ≤ exp 3.030 * 1e-10
    have := exp_3030_lower
    norm_num at this ⊢
    linarith
  · change exp 3.058 * 1e-10 ≤ (0.17051 : ℝ) ^ 6 * 8.6627e-5
    have := exp_3058_upper
    norm_num at this ⊢
    linarith

/-- **The 2013 and 2018 intervals for `T_b/M₅` do not overlap.** No single value of `T_b/M₅`
puts the leading-order amplitude inside both 1σ intervals. This is a statement about the two
data releases, not a test of the model: see the module docstring. -/
theorem planck2013_planck2018_disjoint :
    ¬∃ y > 0, (planck2013.A_lo ≤ ampCoeff * y ^ 6 ∧ ampCoeff * y ^ 6 ≤ planck2013.A_hi) ∧
      (planck2018.A_lo ≤ ampCoeff * y ^ 6 ∧ ampCoeff * y ^ 6 ≤ planck2018.A_hi) := by
  rintro ⟨y, hy, h13, h18⟩
  have := (eq49_planck2013_sharp hy rfl h13).1
  have := (eq49_planck2018 hy rfl h18).2
  linarith

/-- The paper's interval, `eq49 : T_b/M₅ ∈ [0.1705, 0.1723]`, as an instance of the general
theorem. It is wider than `eq49_planck2013_sharp` because it was stated with the coarser
coefficient range `[8.65, 8.67]×10⁻⁵`. -/
example {y A : ℝ} (hy : 0 < y) (hA : A = ampCoeff * y ^ 6)
    (hAobs : planck2013.A_lo ≤ A ∧ A ≤ planck2013.A_hi) : 0.1705 ≤ y ∧ y ≤ 0.1723 :=
  eq49 hy hA hAobs

end WhiteHole
