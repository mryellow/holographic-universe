import HolographicUniverse.Model
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The horizon-crossing time (ROADMAP M4.3)

The brane sits at the bulk radius `r = a/√𝒦`, so it is on the bulk horizon `r = r_h` when
`a = a_h := √𝒦 r_h` (`BraneCosmology.aH`). The paper calls the moment of crossing the moment
the universe "leaves the white hole" (Fig. 3).

Strictly inside the horizon, `a < a_h`, the junction condition gives
`H² ≥ (𝒦/a⁴)(𝒦r_h² - a²) > 0`. So the brane cannot be at rest there
(`BraneCosmology.deriv_ne_zero_of_inside`). By Darboux's theorem, `ȧ` keeps one sign while the
brane stays inside. This is the brane form of the fact that inside a horizon the radius `r` is
a time coordinate.

* `BraneCosmology.white_hole_past`: a brane that expands inside the horizon at one time was
  inside the horizon and expanding at every earlier time. Nothing enters a white hole.
* `BraneCosmology.black_hole_future`: a brane that contracts inside the horizon stays inside and
  contracting at every later time. Nothing leaves a black hole.
* `BraneCosmology.exists_exit`: if the brane is inside at `t₀` and on or outside the horizon at
  `t₁ ≥ t₀`, there is a first time `t* ∈ (t₀, t₁]` on the horizon. The brane expands at every
  time in `[t₀, t*)`.
* `BraneCosmology.exists_unique_exit`: **M4.3.** For an expanding brane inside the horizon that
  is on or outside the horizon at some later time, there is exactly one `t*` with `a(t*) = a_h`
  and with the brane inside at every earlier time. Before `t*`, the brane expands at every time,
  and `a` is strictly increasing on `(-∞, t*]` (`strictMonoOn_Iic`).
* `BraneCosmology.hubble_sq_at_horizon`: on the horizon, `H² = (8πG_b ρ̃/3)²`.

The results use only the fields of `BraneCosmology`, not the acceleration equation. They do not
say that an expanding brane inside the horizon reaches the horizon. With `a` bounded and
increasing, it could approach `a_h` without reaching it.

The first three results hold for any differentiable `f` and level `h` such that `ḟ ≠ 0` where
`f < h` (`exists_first_exit`, `lt_and_deriv_neg_of_ge`, `lt_and_deriv_pos_of_le`).
-/

namespace WhiteHole

open Real Set

section Abstract

variable {f : ℝ → ℝ} {h t₀ : ℝ}

/-- **First exit.** Let `ḟ ≠ 0` wherever `f < h`. If `f(t₀) < h ≤ f(t₁)` with `t₀ ≤ t₁`, there
is a first time `τ ∈ (t₀, t₁]` with `f(τ) = h`. On `[t₀, τ)`, `f < h` and `ḟ > 0`. -/
theorem exists_first_exit {t₁ : ℝ} (hf : Differentiable ℝ f)
    (hne : ∀ t, f t < h → deriv f t ≠ 0) (h₀ : f t₀ < h) (h₁ : h ≤ f t₁) (ht : t₀ ≤ t₁) :
    ∃ τ ∈ Ioc t₀ t₁, f τ = h ∧ ∀ t ∈ Ico t₀ τ, f t < h ∧ 0 < deriv f t := by
  set S := Icc t₀ t₁ ∩ {t | h ≤ f t}
  have hS : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hf.continuous)
  have hSne : S.Nonempty := ⟨t₁, ⟨ht, le_rfl⟩, h₁⟩
  have hbdd : BddBelow S := ⟨t₀, fun t ht ↦ ht.1.1⟩
  have hτ : sInf S ∈ S := hS.csInf_mem hSne hbdd
  set τ := sInf S
  have hτ0 : t₀ < τ := by
    refine lt_of_le_of_ne hτ.1.1 fun e ↦ ?_
    rw [← e] at hτ
    exact (not_le.2 h₀) hτ.2
  have hbefore : ∀ t ∈ Ico t₀ τ, f t < h := fun t ht ↦ by
    by_contra hle
    rw [not_lt] at hle
    exact (csInf_le hbdd ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, hle⟩).not_gt ht.2
  have hfτ : f τ = h := by
    obtain ⟨s, hs, hfs⟩ :=
      intermediate_value_Icc hτ0.le hf.continuous.continuousOn ⟨h₀.le, hτ.2⟩
    have : τ ≤ s := csInf_le hbdd ⟨⟨hs.1, hs.2.trans hτ.1.2⟩, hfs.ge⟩
    rwa [le_antisymm hs.2 this] at hfs
  refine ⟨τ, ⟨hτ0, hτ.1.2⟩, hfτ, fun t ht ↦ ⟨hbefore t ht, ?_⟩⟩
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ico t₀ τ)
    (fun x _ ↦ (hf x).hasDerivAt.hasDerivWithinAt) (m := 0)
    (fun x hx ↦ hne x (hbefore x hx)) with hneg | hpos
  · -- If `f` decreased on `[t₀, τ)`, then `f(τ) < f(t₀) < h`.
    exfalso
    have hanti : StrictAntiOn f (Icc t₀ τ) :=
      strictAntiOn_of_deriv_neg (convex_Icc _ _) hf.continuous.continuousOn fun x hx ↦ by
        rw [interior_Icc] at hx
        exact hneg x (Ioo_subset_Ico_self hx)
    have := hanti (left_mem_Icc.2 hτ0.le) (right_mem_Icc.2 hτ0.le) hτ0
    linarith
  · exact hpos t ht

/-- **Nothing leaves a black hole.** Let `ḟ ≠ 0` wherever `f < h`. If `f(t₀) < h` and
`ḟ(t₀) < 0`, then `f < h` and `ḟ < 0` at every later time. -/
theorem lt_and_deriv_neg_of_ge (hf : Differentiable ℝ f) (hne : ∀ t, f t < h → deriv f t ≠ 0)
    (h₀ : f t₀ < h) (hv : deriv f t₀ < 0) {t : ℝ} (ht : t₀ ≤ t) :
    f t < h ∧ deriv f t < 0 := by
  have hin : ∀ t, t₀ ≤ t → f t < h := fun t ht ↦ by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨τ, hτ, -, hpos⟩ := exists_first_exit hf hne h₀ hle ht
    exact (hpos t₀ ⟨le_rfl, hτ.1⟩).2.not_gt hv
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ici t₀)
    (fun x _ ↦ (hf x).hasDerivAt.hasDerivWithinAt) (m := 0)
    (fun x hx ↦ hne x (hin x hx)) with hneg | hpos
  · exact ⟨hin t ht, hneg t ht⟩
  · exact absurd (hpos t₀ self_mem_Ici) hv.not_gt

/-- **Nothing enters a white hole.** Let `ḟ ≠ 0` wherever `f < h`. If `f(t₀) < h` and
`ḟ(t₀) > 0`, then `f < h` and `ḟ > 0` at every earlier time. -/
theorem lt_and_deriv_pos_of_le (hf : Differentiable ℝ f) (hne : ∀ t, f t < h → deriv f t ≠ 0)
    (h₀ : f t₀ < h) (hv : 0 < deriv f t₀) {t : ℝ} (ht : t ≤ t₀) :
    f t < h ∧ 0 < deriv f t := by
  have hg : Differentiable ℝ fun t ↦ f (-t) := hf.comp differentiable_neg
  have hne' : ∀ t, f (-t) < h → deriv (fun t ↦ f (-t)) t ≠ 0 := fun t ht ↦ by
    rw [deriv_comp_neg, neg_ne_zero]
    exact hne _ ht
  have h₀' : f (-(-t₀)) < h := by rwa [neg_neg]
  have hv' : deriv (fun t ↦ f (-t)) (-t₀) < 0 := by
    rw [deriv_comp_neg, neg_neg, neg_lt_zero]
    exact hv
  have := lt_and_deriv_neg_of_ge hg hne' h₀' hv' (neg_le_neg ht)
  rw [deriv_comp_neg, neg_neg, neg_lt_zero] at this
  exact this

end Abstract

namespace BraneCosmology

variable (M : BraneCosmology)

/-- The scale factor at which the brane is on the bulk horizon, `a_h = √𝒦 r_h`. -/
noncomputable def aH : ℝ := √M.K * M.rh

/-- `a < a_h` exactly when the brane radius `a/√𝒦` is inside the horizon radius `r_h`. -/
theorem lt_aH_iff (t : ℝ) : M.a t < M.aH ↔ braneRadius M.K (M.a t) < M.rh := by
  rw [braneRadius, div_lt_iff₀ (sqrt_pos.2 M.K_pos), aH, mul_comm]

/-- `a < a_h` exactly when the blackening factor at the brane is negative. -/
theorem lt_aH_iff_blacken (t : ℝ) :
    M.a t < M.aH ↔ blacken M.rh (braneRadius M.K (M.a t)) < 0 := by
  rw [M.lt_aH_iff, ← not_le, ← not_le, not_iff_not]
  have hr : 0 < braneRadius M.K (M.a t) := div_pos (M.a_pos t) (sqrt_pos.2 M.K_pos)
  unfold blacken
  rw [sub_nonneg, div_le_one (by positivity)]
  exact (sq_le_sq₀ M.rh_nonneg hr.le).symm

/-- `(𝒦/a²) - 𝒦²r_h²/a⁴ = 𝒦(a² - a_h²)/a⁴`. -/
private lemma curv_eq (t : ℝ) :
    M.K / M.a t ^ 2 - M.K ^ 2 * M.rh ^ 2 / M.a t ^ 4
      = M.K * (M.a t ^ 2 - M.aH ^ 2) / M.a t ^ 4 := by
  have := (M.a_pos t).ne'
  rw [aH, mul_pow, sq_sqrt M.K_pos.le]
  field_simp

/-- **The brane is never at rest strictly inside the horizon.** If `a < a_h`, the junction
condition gives `H² ≥ (𝒦/a⁴)(a_h² - a²) > 0`. -/
theorem deriv_ne_zero_of_inside {t : ℝ} (h : M.a t < M.aH) : deriv M.a t ≠ 0 := by
  intro h0
  have ha := M.a_pos t
  have harg := M.junction_arg t
  rw [add_sub_assoc, curv_eq, h0, zero_div, sq, zero_mul, zero_add] at harg
  have h2 : M.a t ^ 2 < M.aH ^ 2 := pow_lt_pow_left₀ h ha.le two_ne_zero
  have : M.K * (M.a t ^ 2 - M.aH ^ 2) / M.a t ^ 4 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg M.K_pos (by linarith)) (by positivity)
  linarith

/-- **Nothing enters a white hole.** If the brane is inside the horizon and expanding at `t₀`,
it was inside the horizon and expanding at every earlier time. -/
theorem white_hole_past {t₀ : ℝ} (h₀ : M.a t₀ < M.aH) (hv : 0 < deriv M.a t₀) {t : ℝ}
    (ht : t ≤ t₀) : M.a t < M.aH ∧ 0 < deriv M.a t :=
  lt_and_deriv_pos_of_le M.a_diff (fun _ ↦ M.deriv_ne_zero_of_inside) h₀ hv ht

/-- **Nothing leaves a black hole.** If the brane is inside the horizon and contracting at `t₀`,
it stays inside the horizon and contracting at every later time. -/
theorem black_hole_future {t₀ : ℝ} (h₀ : M.a t₀ < M.aH) (hv : deriv M.a t₀ < 0) {t : ℝ}
    (ht : t₀ ≤ t) : M.a t < M.aH ∧ deriv M.a t < 0 :=
  lt_and_deriv_neg_of_ge M.a_diff (fun _ ↦ M.deriv_ne_zero_of_inside) h₀ hv ht

/-- **First exit from the horizon.** If the brane is inside the horizon at `t₀` and on or
outside it at `t₁ ≥ t₀`, there is a first time `t* ∈ (t₀, t₁]` on the horizon. The brane is
inside and expanding at every time in `[t₀, t*)`. -/
theorem exists_exit {t₀ t₁ : ℝ} (h₀ : M.a t₀ < M.aH) (h₁ : M.aH ≤ M.a t₁) (ht : t₀ ≤ t₁) :
    ∃ τ ∈ Ioc t₀ t₁, M.a τ = M.aH ∧ ∀ t ∈ Ico t₀ τ, M.a t < M.aH ∧ 0 < deriv M.a t :=
  exists_first_exit M.a_diff (fun _ ↦ M.deriv_ne_zero_of_inside) h₀ h₁ ht

/-- **M4.3: the horizon-crossing time.** Let the brane be inside the horizon and expanding at
`t₀`, and on or outside the horizon at some time `t₁`. Then there is exactly one time `t*` with
`a(t*) = a_h` and with the brane inside the horizon at every earlier time. The brane expands at
every time before `t*`. -/
theorem exists_unique_exit {t₀ t₁ : ℝ} (h₀ : M.a t₀ < M.aH) (hv : 0 < deriv M.a t₀)
    (h₁ : M.aH ≤ M.a t₁) :
    ∃! τ, M.a τ = M.aH ∧ ∀ t < τ, M.a t < M.aH ∧ 0 < deriv M.a t := by
  have ht : t₀ ≤ t₁ := by
    by_contra hlt
    exact (M.white_hole_past h₀ hv (not_le.1 hlt).le).1.not_ge h₁
  obtain ⟨τ, hτ, hτh, hbefore⟩ := M.exists_exit h₀ h₁ ht
  refine ⟨τ, ⟨hτh, fun t ht ↦ ?_⟩, fun τ' ⟨hτ'h, hτ'⟩ ↦ ?_⟩
  · rcases le_or_gt t₀ t with h | h
    · exact hbefore t ⟨h, ht⟩
    · exact M.white_hole_past h₀ hv h.le
  · -- `τ' ≥ t₀`, since the brane is inside before `t₀` and on the horizon at `τ'`.
    have hτ'0 : t₀ ≤ τ' := by
      by_contra hlt
      exact (M.white_hole_past h₀ hv (not_le.1 hlt).le).1.ne hτ'h
    rcases lt_trichotomy τ' τ with h | h | h
    · exact absurd hτ'h (hbefore τ' ⟨hτ'0, h⟩).1.ne
    · exact h
    · exact absurd hτh (hτ' τ h).1.ne

/-- Before the exit time, the scale factor is strictly increasing. -/
theorem strictMonoOn_Iic {τ : ℝ} (h : ∀ t < τ, 0 < deriv M.a t) : StrictMonoOn M.a (Iic τ) :=
  strictMonoOn_of_deriv_pos (convex_Iic τ) M.a_diff.continuous.continuousOn fun t ht ↦ by
    rw [interior_Iic] at ht
    exact h t ht

/-- **The Hubble rate on the horizon.** At `a = a_h`, the junction condition reduces to
`H² = (8πG_b ρ̃/3)²`. -/
theorem hubble_sq_at_horizon {t : ℝ} (h : M.a t = M.aH) :
    M.H t ^ 2 = (8 * π * M.c.Gb / 3 * M.ρt t) ^ 2 := by
  have hj := congrArg (· ^ 2) (M.junction t)
  rw [mul_pow, M.ε_sq, one_mul, sq_sqrt (M.junction_arg t), add_sub_assoc, curv_eq,
    show M.a t ^ 2 - M.aH ^ 2 = 0 by rw [h, sub_self], mul_zero, zero_div, add_zero] at hj
  unfold H
  linear_combination hj

end BraneCosmology

end WhiteHole
