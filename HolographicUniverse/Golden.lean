module

public import HolographicUniverse.Jeans
public import HolographicUniverse.Boost

@[expose] public section

/-!
# Golden values (ROADMAP M8.4)

Exact values of the Lean spectra at rational parameter points. They are test vectors for the
numerical code in `phenomenology/`: `phenomenology/tests/test_golden.py` checks the Python
implementations against these numbers, so the code and the proofs use the same formulas.

| Spectrum | Point | `n_s − 1` | `α_s` | Lean |
|---|---|---|---|---|
| Jeans, unprojected | `τ = 1`, `k/k_J = 3/5` | `−9/10` | `−369/160` | `golden_jeans_tilt`, `golden_jeans_running` |
| Jeans, projected | `k/k_J = 6/5`, any `τ` | `0` (`I = π/2`) | | `golden_jeansProjected` |
| boost, centre | `B = 1`, `q = 2`, `K = K_V` | `−1/2` | `0` | `golden_boost_centre_tilt`, `golden_boost_centre_running` |
| boost, tail | `B = 1`, `q = 1`, `K = 2K_V` | `−2/9` | `2/27` | `golden_boost_tilt`, `golden_boost_running` |

The tensor-structure ratios of the cascade (`coeff_dust`: `3/4` and `9/8` for dust;
`spatialCoeff_radiation` for radiation) are golden values too.
-/

namespace WhiteHole

open Real

private theorem sqrt_jeans_point : √(1 - ((3 : ℝ) / 5) ^ 2) = 4 / 5 := by
  rw [show 1 - ((3 : ℝ) / 5) ^ 2 = (4 / 5) ^ 2 by norm_num]
  exact sqrt_sq (by norm_num)

/-- Jeans, unprojected: at `τ = 1`, `k = 3`, `k_J = 5`, `n_s − 1 = −9/10`. -/
theorem golden_jeans_tilt : spectralIndex (jeansSpectrum 1 1 5) 3 = 1 - 9 / 10 := by
  rw [spectralIndex_jeans one_ne_zero (by norm_num) (by norm_num) (by norm_num), jeansTilt,
    sqrt_jeans_point]
  norm_num

/-- Jeans, unprojected: at the same point, `α_s = (41/16)(−9/10) = −369/160`. -/
theorem golden_jeans_running : runningIndex (jeansSpectrum 1 1 5) 3 = -369 / 160 := by
  rw [runningIndex_jeans one_ne_zero (by norm_num) (by norm_num) (by norm_num),
    golden_jeans_tilt]
  norm_num

/-- Jeans, projected: above the Jeans scale `I = π/2`, for any `τ`. -/
theorem golden_jeansProjected (τ : ℝ) : jeansProjected τ (6 / 5) = π / 2 :=
  jeansProjected_of_one_le (by norm_num)

/-- Boost at its centre (`u = 1`), `B = 1`, `q = 2`: `n_s − 1 = −1/2`. -/
theorem golden_boost_centre_tilt : spectralIndex (boostSpectrum 1 1 2 1) 1 = 1 - 1 / 2 := by
  rw [spectralIndex_boost one_ne_zero one_pos one_pos, boostTilt]
  norm_num

/-- Boost at its centre: `α_s = 0`. -/
theorem golden_boost_centre_running : runningIndex (boostSpectrum 1 1 2 1) 1 = 0 := by
  rw [runningIndex_boost one_ne_zero one_pos one_pos]
  norm_num

/-- Boost on its tail (`u = 2`), `B = 1`, `q = 1`: `n_s − 1 = −2/9`. -/
theorem golden_boost_tilt : spectralIndex (boostSpectrum 1 1 1 1) 2 = 1 - 2 / 9 := by
  rw [spectralIndex_boost one_ne_zero one_pos two_pos, boostTilt]
  norm_num

/-- Boost on its tail: `α_s = (−1/3)(−2/9) = 2/27`. -/
theorem golden_boost_running : runningIndex (boostSpectrum 1 1 1 1) 2 = 2 / 27 := by
  rw [runningIndex_boost one_ne_zero one_pos two_pos, golden_boost_tilt]
  norm_num

end WhiteHole
