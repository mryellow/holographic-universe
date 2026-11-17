import HolographicUniverse.MaximalSolution

/-!
# From a global solution to a brane cosmology (ROADMAP M4.2)

`BraneCosmology.maximal_eq` shows that a brane cosmology with `P = wρ` on a fixed branch is a
global solution of `ä = F'(a)/2`. This file proves the converse. A scale factor `a` that is
defined for all time, stays in `braneDomain` (`a > 0`, away from the pressure singularity) and
obeys `ȧ² = F(a)` defines a `BraneCosmology`:

* `ρ = ρ₀ a^{-3(1+w)}` and `P = wρ`;
* `ρ̃ = ρ̃_sgn(a)`, the branch `sgn` of Eq. (26) (`rhoTildeX`);
* `P̃` from Eq. (16);
* the orientation `ε`, which must satisfy `ε ρ̃ ≤ 0` at every time.

The condition on `ε` is necessary: every `BraneCosmology` has `ε ρ̃ ≤ 0`
(`BraneCosmology.eps_mul_ρt_nonpos`). So a history in which `ρ̃` changes sign has no instance
(README issue 6).

* `hasDerivAt_rhoTildeX`: `dρ̃/da = -3(ρ̃ + P̃)/a`, with `P̃` from Eq. (16). This is the
  continuity equation (13) in terms of `a`. It follows from the derivative of `F`
  (`hasDerivAt_friedmannF`).
* `junction_sq`: on a solution of `ȧ² = F(a)`, the square-root argument of the junction
  condition is `((8πG_b/3) ρ̃)²`.
* `BraneCosmology.ofSolution`: the instance. If `a` also obeys `ä = F'(a)/2`, the instance is a
  solution of the equations of motion (`ofSolution_isSolution`).
* `BraneCosmology.exists_of_maximal`: the same for a maximal solution with interval `ℝ`.
-/

namespace WhiteHole

open Real Set

/-- The induced density on the branch `sgn` of Eq. (26), as a function of the scale factor, for
matter `ρ = ρ₀ a^{-3(1+w)}`. -/
noncomputable def rhoTildeX (c : Couplings) (K H0 rh w ρ₀ sgn x : ℝ) : ℝ :=
  rhoTilde sgn c.rhoS (rhoBH c.GN K H0 rh x) (ρ₀ * x ^ (-(3 * (1 + w))))

/-- `F` written with `rhoTildeX`. -/
theorem friedmannF_eq_rhoTildeX (c : Couplings) (K H0 rh w ρ₀ sgn x : ℝ) :
    friedmannF c K H0 rh w ρ₀ sgn x
      = 8 * π * c.GN / 3 * (ρ₀ * x ^ (-(3 * (1 + w))) + rhoTildeX c K H0 rh w ρ₀ sgn x) * x ^ 2
        - K := rfl

variable {c : Couplings} {K H0 rh w ρ₀ sgn x : ℝ}

/-- **The continuity equation (13) in terms of `a`.** Away from `a = 0` and from the
singularity, `dρ̃/da = -3(ρ̃ + P̃)/a`, where `P̃` is given by Eq. (16) with `P = wρ`. -/
theorem hasDerivAt_rhoTildeX (hsg : sgn ^ 2 = 1) (hx : 0 < x)
    (hD : 0 < realityArg c K H0 rh w ρ₀ x) :
    HasDerivAt (rhoTildeX c K H0 rh w ρ₀ sgn)
      (-3 * (rhoTildeX c K H0 rh w ρ₀ sgn x + pressureTilde c.rhoS
        (rhoTildeX c K H0 rh w ρ₀ sgn x)
        (3 * (w * (ρ₀ * x ^ (-(3 * (1 + w))))) - ρ₀ * x ^ (-(3 * (1 + w))))) / x) x := by
  have hGN := c.GN_pos
  have hg : DifferentiableAt ℝ (rhoTildeX c K H0 rh w ρ₀ sgn) x := by
    have e : rhoTildeX c K H0 rh w ρ₀ sgn
        = fun x ↦ c.rhoS * (1 + sgn * √(realityArg c K H0 rh w ρ₀ x)) := rfl
    rw [e]
    exact ((((contDiffAt_realityArg (n := 1) hx.ne').differentiableAt one_ne_zero).sqrt
      hD.ne').const_mul sgn |>.const_add 1).const_mul c.rhoS
  have hρ := (hasDerivAt_rpow_const (p := -(3 * (1 + w))) (Or.inl hx.ne')).const_mul ρ₀
  have hF : HasDerivAt (friedmannF c K H0 rh w ρ₀ sgn) _ x :=
    (((hρ.add hg.hasDerivAt).const_mul (8 * π * c.GN / 3)).mul (hasDerivAt_pow 2 x)).sub_const K
  have h := (hasDerivAt_friedmannF hsg hx hD).unique hF
  refine hg.hasDerivAt.congr_deriv ?_
  rw [rpow_sub_one hx.ne', show rhoTilde sgn c.rhoS (rhoBH c.GN K H0 rh x)
    (ρ₀ * x ^ (-(3 * (1 + w)))) = rhoTildeX c K H0 rh w ρ₀ sgn x from rfl] at h
  simp only [Pi.add_apply] at h
  generalize pressureTilde c.rhoS (rhoTildeX c K H0 rh w ρ₀ sgn x)
    (3 * (w * (ρ₀ * x ^ (-(3 * (1 + w))))) - ρ₀ * x ^ (-(3 * (1 + w)))) = Pt at h ⊢
  generalize rhoTildeX c K H0 rh w ρ₀ sgn x = g at h ⊢
  generalize deriv (rhoTildeX c K H0 rh w ρ₀ sgn) x = D at h ⊢
  generalize x ^ (-(3 * (1 + w))) = r at h ⊢
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h
  rw [eq_div_iff hx.ne']
  linear_combination (norm := (field_simp; ring)) (-3 / (8 * π * c.GN * x)) * h

/-- **The junction condition squared.** If `v² = F(a)`, then
`(v/a)² + 𝒦/a² - 𝒦²r_h²/a⁴ = ((8πG_b/3) ρ̃)²`. -/
theorem junction_sq (hH0 : H0 ≠ 0) (hx : 0 < x) (hD : 0 ≤ realityArg c K H0 rh w ρ₀ x)
    {v : ℝ} (hv : v ^ 2 = friedmannF c K H0 rh w ρ₀ sgn x) (hsg : sgn = 1 ∨ sgn = -1) :
    (v / x) ^ 2 + K / x ^ 2 - K ^ 2 * rh ^ 2 / x ^ 4
      = (8 * π * c.Gb / 3 * rhoTildeX c K H0 rh w ρ₀ sgn x) ^ 2 := by
  have hs := c.rhoS_pos
  have hGb := c.Gb_pos
  have hreal : 2 * (rhoBH c.GN K H0 rh x - ρ₀ * x ^ (-(3 * (1 + w)))) ≤ c.rhoS := by
    unfold realityArg at hD
    rwa [sub_nonneg, div_le_one hs] at hD
  have hI : IsInduced c.rhoS (rhoBH c.GN K H0 rh x) (ρ₀ * x ^ (-(3 * (1 + w))))
      (rhoTildeX c K H0 rh w ρ₀ sgn x) := by
    rw [isInduced_iff hs hreal]
    rcases hsg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [friedmannF_eq_rhoTildeX] at hv
  unfold IsInduced at hI
  have hsS : c.rhoS * (16 * π * c.Gb ^ 2) = 3 * c.GN := by
    unfold Couplings.rhoS; field_simp
  have e1 : (v / x) ^ 2 + K / x ^ 2 = 8 * π * c.GN / 3
      * (ρ₀ * x ^ (-(3 * (1 + w))) + rhoTildeX c K H0 rh w ρ₀ sgn x) := by
    rw [div_pow, ← add_div, hv]; field_simp; ring
  rw [rhoBH_term c.GN_pos.ne' hH0 hx.ne']
  linear_combination e1 - (64 * π ^ 2 * c.Gb ^ 2 / 9) * hI
    - (8 * π / 9) * (rhoTildeX c K H0 rh w ρ₀ sgn x + ρ₀ * x ^ (-(3 * (1 + w)))
      - rhoBH c.GN K H0 rh x) * hsS

namespace BraneCosmology

variable (c) in
/-- **A brane cosmology from a global solution of `ȧ² = F(a)`.** The scale factor `a` is
differentiable, stays in `braneDomain` and obeys `ȧ² = F(a)` at every time. The orientation `ε`
obeys `ε ρ̃ ≤ 0` at every time. Then `ρ = ρ₀ a^{-3(1+w)}`, `P = wρ`, `ρ̃` on the branch `sgn`,
and `P̃` from Eq. (16) define a brane cosmology. -/
noncomputable def ofSolution (ε : ℝ) (hK : 0 < K) (hH0 : 0 < H0) (hrh : 0 ≤ rh)
    (hε : ε ^ 2 = 1) (hsg : sgn = 1 ∨ sgn = -1) (a : ℝ → ℝ) (ha : Differentiable ℝ a)
    (hdom : ∀ t, a t ∈ braneDomain c K H0 rh w ρ₀)
    (hE : ∀ t, deriv a t ^ 2 = friedmannF c K H0 rh w ρ₀ sgn (a t))
    (hor : ∀ t, ε * rhoTildeX c K H0 rh w ρ₀ sgn (a t) ≤ 0) : BraneCosmology where
  c := c
  K := K
  H0 := H0
  rh := rh
  ε := ε
  a := a
  ρ := fun t ↦ ρ₀ * a t ^ (-(3 * (1 + w)))
  P := fun t ↦ w * (ρ₀ * a t ^ (-(3 * (1 + w))))
  ρt := fun t ↦ rhoTildeX c K H0 rh w ρ₀ sgn (a t)
  Pt := fun t ↦ pressureTilde c.rhoS (rhoTildeX c K H0 rh w ρ₀ sgn (a t))
    (3 * (w * (ρ₀ * a t ^ (-(3 * (1 + w))))) - ρ₀ * a t ^ (-(3 * (1 + w))))
  K_pos := hK
  H0_pos := hH0
  rh_nonneg := hrh
  ε_sq := hε
  a_pos := fun t ↦ (hdom t).1
  a_diff := ha
  ρ_diff := fun t ↦ ((ha t).rpow_const (Or.inl (hdom t).1.ne')).const_mul ρ₀
  ρt_diff := fun t ↦ ((hasDerivAt_rhoTildeX (by rcases hsg with rfl | rfl <;> norm_num)
    (hdom t).1 (hdom t).2).comp t (ha t).hasDerivAt).differentiableAt
  friedmann := fun t ↦ by
    have hx := (hdom t).1
    have h := hE t
    rw [friedmannF_eq_rhoTildeX] at h
    rw [div_pow, ← add_div, h]
    field_simp
    ring
  continuity := fun t ↦ by
    have hx := (hdom t).1
    rw [(((ha t).hasDerivAt.rpow_const (p := -(3 * (1 + w))) (Or.inl hx.ne')).const_mul
      ρ₀).deriv, rpow_sub_one hx.ne']
    field_simp
  continuity_tilde := fun t ↦ by
    have hx := (hdom t).1
    have h : HasDerivAt (fun t ↦ rhoTildeX c K H0 rh w ρ₀ sgn (a t)) _ t :=
      (hasDerivAt_rhoTildeX (by rcases hsg with rfl | rfl <;> norm_num) hx (hdom t).2).comp t
        (ha t).hasDerivAt
    rw [h.deriv]
    field_simp
  junction := fun t ↦ by
    have hg : 0 < 8 * π * c.Gb / 3 := by have := c.Gb_pos; positivity
    rw [junction_sq hH0.ne' (hdom t).1 (hdom t).2.le (hE t) hsg, sqrt_sq_eq_abs]
    have h := hor t
    rcases eps_cases hε with rfl | rfl
    · rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hg.le (by linarith))]; ring
    · rw [abs_of_nonneg (mul_nonneg hg.le (by linarith))]; ring
  junction_arg := fun t ↦ by
    rw [junction_sq hH0.ne' (hdom t).1 (hdom t).2.le (hE t) hsg]
    positivity

variable {ε : ℝ} {hK : 0 < K} {hH0 : 0 < H0} {hrh : 0 ≤ rh} {hε : ε ^ 2 = 1}
  {hsg : sgn = 1 ∨ sgn = -1} {a : ℝ → ℝ} {ha : Differentiable ℝ a}
  {hdom : ∀ t, a t ∈ braneDomain c K H0 rh w ρ₀}
  {hE : ∀ t, deriv a t ^ 2 = friedmannF c K H0 rh w ρ₀ sgn (a t)}
  {hor : ∀ t, ε * rhoTildeX c K H0 rh w ρ₀ sgn (a t) ≤ 0}

/-- The instance has `P = wρ`. -/
theorem ofSolution_barotropic (t : ℝ) :
    (ofSolution c ε hK hH0 hrh hε hsg a ha hdom hE hor).P t
      = w * (ofSolution c ε hK hH0 hrh hε hsg a ha hdom hE hor).ρ t := rfl

/-- The instance is on the branch `sgn` of Eq. (26). -/
theorem ofSolution_branch (t : ℝ) :
    let M := ofSolution c ε hK hH0 hrh hε hsg a ha hdom hE hor
    M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t) := rfl

/-- The matter constant of the instance is `ρ₀`. So `M.F w sgn` is `F` with `ρ₀`. -/
theorem ofSolution_rho0 :
    let M := ofSolution c ε hK hH0 hrh hε hsg a ha hdom hE hor
    M.ρ 0 * M.a 0 ^ (3 * (1 + w)) = ρ₀ := by
  have hx := (hdom 0).1
  change ρ₀ * a 0 ^ (-(3 * (1 + w))) * a 0 ^ (3 * (1 + w)) = ρ₀
  rw [rpow_neg hx.le, mul_assoc, inv_mul_cancel₀ (rpow_pos_of_pos hx _).ne', mul_one]

/-- **The instance is a solution of the equations of motion** if `a` also obeys
`ä = F'(a)/2`. -/
theorem ofSolution_isSolution
    (hacc : ∀ t, HasDerivAt (deriv a) (deriv (friedmannF c K H0 rh w ρ₀ sgn) (a t) / 2) t) :
    (ofSolution c ε hK hH0 hrh hε hsg a ha hdom hE hor).IsSolution := by
  intro t
  refine ⟨?_, fun _ ↦ rfl⟩
  have hsg2 : sgn ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
  have h := hacc t
  rw [(hasDerivAt_friedmannF hsg2 (hdom t).1 (hdom t).2).deriv] at h
  unfold AccelAt
  change HasDerivAt (deriv a) _ t
  convert h using 1
  dsimp only [ofSolution]
  unfold rhoTildeX
  ring

end BraneCosmology

namespace BraneCosmology

/-- **The converse of `maximal_eq`.** Take a maximal solution `γ = (a, ȧ)` of `ä = F'(a)/2` in
`braneDomain` whose interval is all of `ℝ`, with `ȧ² = F(a)` at one time. If the orientation `ε`
obeys `ε ρ̃ ≤ 0` along it, then there is a brane cosmology with scale factor `a`, `P = wρ`, `ρ̃` on
the branch `sgn`, and the given constants. It is a solution of the equations of motion. -/
theorem exists_of_maximal {c : Couplings} {K H0 rh w ρ₀ sgn ε t₀ : ℝ} (hK : 0 < K)
    (hH0 : 0 < H0) (hrh : 0 ≤ rh) (hε : ε ^ 2 = 1) (hsg : sgn = 1 ∨ sgn = -1)
    {γ : ℝ → ℝ × ℝ}
    (hm : IsMaximalSolution (secondOrderField (friedmannF c K H0 rh w ρ₀ sgn))
      (Prod.fst ⁻¹' braneDomain c K H0 rh w ρ₀) t₀ γ univ)
    (h0 : (γ t₀).2 ^ 2 = friedmannF c K H0 rh w ρ₀ sgn (γ t₀).1)
    (hor : ∀ t, ε * rhoTildeX c K H0 rh w ρ₀ sgn (γ t).1 ≤ 0) :
    ∃ M : BraneCosmology, M.IsSolution ∧ M.c = c ∧ M.K = K ∧ M.H0 = H0 ∧ M.rh = rh ∧
      M.ε = ε ∧ (∀ t, M.a t = (γ t).1 ∧ deriv M.a t = (γ t).2) ∧ (∀ t, M.P t = w * M.ρ t) ∧
      (∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) ∧
      M.ρ 0 * M.a 0 ^ (3 * (1 + w)) = ρ₀ := by
  have hF := contDiffAt_friedmannF_of_mem (c := c) (K := K) (H0 := H0) (rh := rh) (w := w)
    (ρ₀ := ρ₀) (sgn := sgn)
  have hd := fun t ↦ hm.isSolOn.hasDerivAt₂ (mem_univ t)
  have hda : deriv (fun t ↦ (γ t).1) = fun t ↦ (γ t).2 := funext fun t ↦ (hd t).1.deriv
  have hE := hm.energy₂ hF h0
  refine ⟨ofSolution c ε hK hH0 hrh hε hsg (fun t ↦ (γ t).1)
    (fun t ↦ (hd t).1.differentiableAt) (fun t ↦ (hm.isSolOn t (mem_univ t)).2)
    (fun t ↦ by rw [hda]; exact hE t (mem_univ t)) hor, ?_, rfl, rfl, rfl, rfl, rfl,
    fun t ↦ ⟨rfl, by change deriv (fun t ↦ (γ t).1) t = _; rw [hda]⟩, ofSolution_barotropic,
    ofSolution_branch, ofSolution_rho0⟩
  refine ofSolution_isSolution fun t ↦ ?_
  rw [hda]
  exact (hd t).2

end BraneCosmology

end WhiteHole
