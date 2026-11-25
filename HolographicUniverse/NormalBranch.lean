module

public import HolographicUniverse.Dynamics
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# No eternal normal-branch solution with `ε = -1` (ROADMAP M2.3)

M2.3 asks for an expanding `BraneCosmology` on the normal branch with the paper's orientation
`ε = -1`. For ordinary matter there is none, expanding or not.

On the normal branch away from the singularity, `ρ̃ < ρ̃_s`. With `ε = -1`, `ρ̃ ≥ 0`
(`BraneCosmology.ρt_nonneg`). If the matter obeys `P ≤ ρ/3`, Eq. (16) then gives `P̃ ≥ 0`. If
it also obeys `ρ + 3P > 0`, the acceleration equation gives `ä < 0` at every time. A function
with `ä < 0` on all of `ℝ` is not positive at every time (`exists_nonpos_of_strictAnti_deriv`).
But a `BraneCosmology` has `a > 0` at every time.

This is the brane form of a result of general relativity: a closed universe with `ρ + 3P > 0`
decelerates at all times, so it does not exist for all time. Here the induced fluid adds to the
deceleration. A normal-branch history with `ε = -1` exists only on a bounded interval of time.
The structure `BraneCosmology` needs `a` at every time, so it cannot hold such a history.

* `exists_nonpos_of_strictAnti_deriv`: if `ȧ` is strictly decreasing, `a ≤ 0` at some time.
* `BraneCosmology.not_isSolution_normal_eps_neg`: no solution has `ε = -1`, `ρ̃ < ρ̃_s`,
  `ρ + 3P > 0` and `3P ≤ ρ` at every time.
* `BraneCosmology.not_isSolution_minus_branch`: the same, on the branch `ρ̃_-` of Eq. (26) away
  from the singularity.
-/

namespace WhiteHole

open Real Set

/-- **A strictly concave function on `ℝ` is not positive everywhere.** If `ḟ` is strictly
decreasing, then `f ≤ 0` at some time. -/
theorem exists_nonpos_of_strictAnti_deriv {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : StrictAnti f') : ∃ t, f t ≤ 0 := by
  have hc : ContinuousOn f univ := fun t _ ↦ (hf t).continuousAt.continuousWithinAt
  by_contra hpos
  simp only [not_exists, not_le] at hpos
  by_cases h0 : 0 < f' 0
  · -- `f` grows at least at the rate `ḟ(0)` before time `0`.
    set T := f 0 / f' 0 + 1 with hT_def
    have hT : 0 < T := by have := hpos 0; positivity
    obtain ⟨c, hcI, hcs⟩ := exists_hasDerivAt_eq_slope f f' (neg_lt_zero.2 hT)
      (hc.mono (subset_univ _)) fun x _ ↦ hf x
    have h1 : f' 0 < f' c := hf' hcI.2
    rw [hcs, lt_div_iff₀ (by linarith)] at h1
    have hm : f' 0 * T = f 0 + f' 0 := by rw [hT_def]; field_simp
    linarith [hpos (-T)]
  · -- `ḟ < 0` from time `1`, and `f` falls at least at the rate `-ḟ(1)` after it.
    have h1 : f' 1 < 0 := (hf' one_pos).trans_le (not_lt.1 h0)
    set T := 1 + (f 1 / -f' 1 + 1) with hT_def
    have hT : 1 < T := by
      have : 0 < f 1 / -f' 1 := div_pos (hpos 1) (by linarith)
      linarith
    obtain ⟨c, hcI, hcs⟩ := exists_hasDerivAt_eq_slope f f' hT
      (hc.mono (subset_univ _)) fun x _ ↦ hf x
    have h2 : f' c < f' 1 := hf' hcI.1
    rw [hcs, div_lt_iff₀ (by linarith)] at h2
    have hm : f' 1 * (T - 1) = -f 1 + f' 1 := by
      have := h1.ne
      rw [hT_def]; field_simp; ring
    linarith [hpos T]

namespace BraneCosmology

variable (M : BraneCosmology)

/-- **No eternal solution on the normal branch with `ε = -1`.** Suppose `ε = -1`, and at every
time `ρ̃ < ρ̃_s`, `ρ + 3P > 0` and `3P ≤ ρ`. Then `M` is not a solution of the equations of
motion: `P̃ ≥ 0` by Eq. (16), so `ä < 0` at every time, and `a` cannot stay positive. -/
theorem not_isSolution_normal_eps_neg (hsol : M.IsSolution) (hε : M.ε = -1)
    (hns : ∀ t, M.ρt t < M.c.rhoS) (hρP : ∀ t, 0 < M.ρ t + 3 * M.P t)
    (hP : ∀ t, 3 * M.P t ≤ M.ρ t) : False := by
  have hs := M.c.rhoS_pos
  have hneg : ∀ t,
      -(4 * π * M.c.GN / 3) * (M.ρ t + M.ρt t + 3 * (M.P t + M.Pt t)) * M.a t < 0 := by
    intro t
    have hρt := M.ρt_nonneg hε t
    have hPt : 0 ≤ M.Pt t := by
      rw [(hsol t).2 (hns t).ne]
      unfold pressureTilde
      apply div_nonneg
      · nlinarith [hP t, hns t]
      · linarith [hns t]
    have hX : 0 < M.ρ t + M.ρt t + 3 * (M.P t + M.Pt t) := by linarith [hρP t]
    have hG : 0 < 4 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
    have := mul_pos (mul_pos hG hX) (M.a_pos t)
    linarith
  have hanti : StrictAnti (deriv M.a) :=
    strictAnti_of_deriv_neg fun t ↦ (hsol t).1.deriv ▸ hneg t
  obtain ⟨t, ht⟩ := exists_nonpos_of_strictAnti_deriv (fun t ↦ (M.a_diff t).hasDerivAt) hanti
  exact (M.a_pos t).not_ge ht

/-- **M2.3.** No solution of the equations of motion is on the normal branch `ρ̃_-` of Eq. (26)
with `ε = -1`, away from the singularity, for matter with `ρ + 3P > 0` and `3P ≤ ρ`. This
includes dust and radiation with `ρ > 0`. -/
theorem not_isSolution_minus_branch (hsol : M.IsSolution) (hε : M.ε = -1)
    (hbr : ∀ t, M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t))
    (hns : ∀ t, M.ρt t ≠ M.c.rhoS) (hρP : ∀ t, 0 < M.ρ t + 3 * M.P t)
    (hP : ∀ t, 3 * M.P t ≤ M.ρ t) : False :=
  M.not_isSolution_normal_eps_neg hsol hε
    (fun t ↦ lt_of_le_of_ne (hbr t ▸ rhoTilde_minus_le M.c.rhoS_pos) (hns t)) hρP hP

end BraneCosmology

end WhiteHole
