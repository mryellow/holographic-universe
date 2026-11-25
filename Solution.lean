module

public import HolographicUniverse

@[expose] public section

/-!
# Holographic Universe: proofs of the advertised statements

This module imports the full `HolographicUniverse` library, which provides the definitions that
`Challenge.lean` restates. Comparator checks that each definition and theorem below has exactly the
statement of its counterpart in `Challenge.lean`, and that the proofs use only `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Real MeasureTheory Filter Topology

namespace HolographicUniverse

open WhiteHole

theorem zeta5_spec : riemannZeta 5 = (zeta5 : ℂ) ∧ 1.0369 ≤ zeta5 ∧ zeta5 ≤ 1.0370 :=
  ⟨riemannZeta_five, zeta5_bounds⟩

theorem integral_bose :
    ∫ y in Set.Ioi (0 : ℝ), y ^ 5 * (exp y / (exp y - 1) ^ 2) = 120 * zeta5 :=
  WhiteHole.integral_bose

theorem thermalM_zero : thermalM 0 = 15 * zeta5 / π ^ 2 ∧
    1.5758 ≤ thermalM 0 ∧ thermalM 0 ≤ 1.5761 :=
  ⟨WhiteHole.thermalM_zero, thermalM_zero_bounds⟩

theorem thermalM_lt_of_norm_lt {κ₁ κ₂ : E4} (h : ‖κ₁‖ < ‖κ₂‖) : thermalM κ₁ < thermalM κ₂ :=
  WhiteHole.thermalM_lt_of_norm_lt h

theorem mRay_second_order : deriv mRay 0 = 0 ∧
    HasDerivAt (deriv mRay) ((10 * zeta5 - zeta3) / (16 * π ^ 2)) 0 ∧
    0 < (10 * zeta5 - zeta3) / (16 * π ^ 2) :=
  ⟨deriv_mRay_zero, hasDerivAt_deriv_mRay, secondOrderCoeff_pos⟩

theorem spectralIndex_thermal_gt_one {C s k : ℝ} (hC : C ≠ 0) (hs : 0 < s) (hk : 0 < k) :
    1 < spectralIndex (fun k ↦ C * mRay (k / s)) k :=
  WhiteHole.spectralIndex_thermal_gt_one hC hs hk

theorem jeans_tilt_and_running {C τ kJ k : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ) (hk : 0 < k)
    (hk' : k < kJ) :
    spectralIndex (fun k ↦ C * exp (2 * τ * √(1 - (k / kJ) ^ 2))) k - 1 =
        -(2 * τ * (k / kJ) ^ 2 / √(1 - (k / kJ) ^ 2)) ∧
      runningIndex (fun k ↦ C * exp (2 * τ * √(1 - (k / kJ) ^ 2))) k =
        (1 + 1 / (1 - (k / kJ) ^ 2)) *
          (spectralIndex (fun k ↦ C * exp (2 * τ * √(1 - (k / kJ) ^ 2))) k - 1) := by
  refine ⟨?_, runningIndex_jeans hC hkJ hk hk'⟩
  have h := spectralIndex_jeans (τ := τ) hC hkJ hk hk'
  rw [jeansTilt] at h
  exact sub_eq_of_eq_add' h

theorem spectralIndex_jeansProjected_above {C τ kJ k : ℝ} (hkJ : 0 < kJ) (hk : kJ < k) :
    spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k = 1 :=
  WhiteHole.spectralIndex_jeansProjected_above hkJ hk

theorem tilt_budget {C τ kJ b : ℝ} (hC : C ≠ 0) (hkJ : 0 < kJ) (hb : kJ ≤ b) :
    Tendsto (fun a ↦ ∫ k in a..b, (spectralIndex (fun k ↦ C * jeansProjected τ (k / kJ)) k - 1) / k)
      (𝓝[>] 0) (𝓝 (-2 * log (cosh τ))) :=
  tendsto_integral_spectralIndex_jeansBrane hC hkJ hb

end HolographicUniverse
