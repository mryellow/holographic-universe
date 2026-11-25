module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.PSeries

@[expose] public section

/-!
# Numerical bounds on `ζ(5)` (ROADMAP M1.2)

The coefficient of the leading-order amplitude, Eq. (48), is `25 ζ(5) / (3072 π⁴)`. This file
proves `1.0369 ≤ ζ(5) ≤ 1.0370` (the true value is `ζ(5) = 1.036927…`).

* `zeta5` is the real series `∑_{n ≥ 1} 1/n⁵`, and `riemannZeta_five` identifies it with
  Mathlib's `riemannZeta 5`.
* Lower bound: the series has non-negative terms, so it is at least its first ten terms,
  `∑_{n=1}^{10} 1/n⁵ = 1.0369073…`.
* Upper bound: for `m > 0`, `1/(m+1)⁵ ≤ 1/(4m⁴) - 1/(4(m+1)⁴)`. The tail after ten terms
  telescopes to at most `1/(4·10⁴)`, so `ζ(5) ≤ 1.0369324…`.
-/

namespace WhiteHole

open Finset

/-- `ζ(5) = ∑_{n ≥ 1} 1/n⁵` as a real number. -/
noncomputable def zeta5 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5

/-- `zeta5` is Mathlib's Riemann zeta function at `5`. -/
theorem riemannZeta_five : riemannZeta 5 = (zeta5 : ℂ) := by
  rw [zeta5, Complex.ofReal_tsum, zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num)]
  congr 1
  funext n
  rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  ring

/-- The terms of the series. -/
private lemma term_nonneg (n : ℕ) : 0 ≤ 1 / ((n : ℝ) + 1) ^ 5 := by positivity

/-- **Telescoping bound.** For `m > 0`, `1/(m+1)⁵ + 1/(4(m+1)⁴) ≤ 1/(4m⁴)`. Equivalently
`(m+5) m⁴ ≤ (m+1)⁵`. -/
private lemma term_telescope {m : ℝ} (hm : 0 < m) :
    1 / (m + 1) ^ 5 + 1 / (4 * (m + 1) ^ 4) ≤ 1 / (4 * m ^ 4) := by
  have hm1 : 0 < m + 1 := by linarith
  rw [show 1 / (m + 1) ^ 5 + 1 / (4 * (m + 1) ^ 4) = (m + 5) / (4 * (m + 1) ^ 5) by
      field_simp; ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (m + 1) ^ 5 - (m + 5) * m ^ 4 = 10 * m ^ 3 + 10 * m ^ 2 + 5 * m + 1 := by ring
  have : 0 ≤ 10 * m ^ 3 + 10 * m ^ 2 + 5 * m + 1 := by positivity
  nlinarith

/-- The first ten terms, `∑_{n=1}^{10} 1/n⁵`. -/
private noncomputable def S10 : ℝ := ∑ i ∈ range 10, 1 / ((i : ℝ) + 1) ^ 5

/-- Every partial sum past ten terms, plus the telescoping remainder, stays below
`S10 + 1/(4·10⁴)`. -/
private lemma partial_add_rem (k : ℕ) :
    ∑ i ∈ range (10 + k), 1 / ((i : ℝ) + 1) ^ 5 + 1 / (4 * ((10 + k : ℕ) : ℝ) ^ 4)
      ≤ S10 + 1 / (4 * 10 ^ 4) := by
  induction k with
  | zero => simp [S10]
  | succ k ih =>
    rw [← add_assoc, sum_range_succ]
    have hm : (0 : ℝ) < ((10 + k : ℕ) : ℝ) := by positivity
    have ht := term_telescope hm
    push_cast at ht ih ⊢
    linarith

/-- Every partial sum is at most `S10 + 1/(4·10⁴)`. -/
private lemma partial_le (n : ℕ) :
    ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 5 ≤ S10 + 1 / (4 * 10 ^ 4) := by
  have hsub : ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ^ 5 ≤ ∑ i ∈ range (10 + n), 1 / ((i : ℝ) + 1) ^ 5 :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by lia)) fun i _ _ ↦ term_nonneg i
  have hrem : 0 ≤ 1 / (4 * ((10 + n : ℕ) : ℝ) ^ 4) := by positivity
  linarith [partial_add_rem n]

private lemma S10_eq : S10 = 105376229094957931 / 101625502003200000 := by
  norm_num [S10, sum_range_succ]

/-- The series for `ζ(5)` converges. -/
theorem summable_zeta5 : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 5 :=
  summable_of_sum_range_le term_nonneg partial_le

/-- **Lower bound**, from the first ten terms: `1.0369 ≤ ζ(5)`. -/
theorem zeta5_lower : 1.0369 ≤ zeta5 := by
  have h := summable_zeta5.sum_le_tsum (range 10) fun i _ ↦ term_nonneg i
  have h10 : (1.0369 : ℝ) ≤ S10 := by rw [S10_eq]; norm_num
  exact h10.trans h

/-- **Upper bound**, from ten terms plus the telescoping tail: `ζ(5) ≤ 1.03694`. -/
theorem zeta5_upper : zeta5 ≤ 1.03694 := by
  have h := Real.tsum_le_of_sum_range_le term_nonneg partial_le
  have h10 : S10 + 1 / (4 * 10 ^ 4) ≤ (1.03694 : ℝ) := by rw [S10_eq]; norm_num
  exact h.trans h10

/-- **ROADMAP M1.2.** `1.0369 ≤ ζ(5) ≤ 1.0370`. -/
theorem zeta5_bounds : 1.0369 ≤ zeta5 ∧ zeta5 ≤ 1.0370 :=
  ⟨zeta5_lower, zeta5_upper.trans (by norm_num)⟩

/-- The same bounds stated for Mathlib's `riemannZeta 5`, which is real. -/
theorem riemannZeta_five_bounds :
    (riemannZeta 5).im = 0 ∧ 1.0369 ≤ (riemannZeta 5).re ∧ (riemannZeta 5).re ≤ 1.0370 := by
  rw [riemannZeta_five, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, zeta5_bounds⟩

end WhiteHole
