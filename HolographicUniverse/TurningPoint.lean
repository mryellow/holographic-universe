import HolographicUniverse.LocalExistence

/-!
# Turning points (ROADMAP M4.2, second-order part)

At a turning point `H = 0`, the first-order equation `ȧ² = F(a)` does not fix the history: the
constant `a` is a second solution there. This file uses the acceleration equation instead.

* `hasDerivAt_friedmannF`: the derivative of `F` in closed form. It is
  `2 · (-(4πG_N/3)(ρ + ρ̃ + 3(P + P̃)) a)`, with `P = wρ` and `P̃` from Eq. (16).
* `BraneCosmology.accel_eq_deriv`: for a solution (`IsSolution`, M2.5) with `P = wρ` on a
  fixed branch, `ä = F'(a)/2` at every time away from the singularity, **`H = 0` included**.
  So the acceleration equation is the second-order form of the Friedmann equation.
* `local_unique₂`, `exists_local_solution₂`: Picard–Lindelöf for `ä = F'(a)/2` on `ℝ²`. Where
  `F` is `C²`, the solution with `a(t₀) = a₀` and `ȧ(t₀) = v₀` exists and is locally unique. If
  `v₀² = F(a₀)`, it solves `ȧ² = F(a)`, because `ȧ² - F(a)` is conserved. This includes `v₀ = 0`.
* `BraneCosmology.locally_determined₂`: near any time away from the singularity, `a(t₀)` and
  `ȧ(t₀)` fix a solution, also at `H = 0`.
* `BraneCosmology.equilibrium_of_rest`: a solution stays at rest near `t₀` only if
  `F(a) = F'(a) = 0`. At a turning point with `F'(a) ≠ 0`, the solution does not stay at rest.
* `BraneCosmology.radiationBounce_determined`: the radiation bounce is the only solution of
  `ä = F'(a)/2` with its data at the bounce `t = 0`.

Global solutions are still open.
-/

namespace WhiteHole

open Real Set Topology

/-- `ρ_BH ∝ a⁻⁴`, as a derivative in `a`. -/
theorem hasDerivAt_rhoBH_x {GN K H0 rh x : ℝ} (hGN : GN ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (rhoBH GN K H0 rh) (-4 * rhoBH GN K H0 rh x / x) x := by
  have hB : 8 * π * GN * x ^ 4 ≠ 0 := by positivity
  have h := (hasDerivAt_const x (3 * omegaK K H0 ^ 2 * H0 ^ 4 * rh ^ 2)).div
    ((hasDerivAt_pow 4 x).const_mul (8 * π * GN)) hB
  unfold rhoBH
  convert h using 1
  field_simp
  ring

/-- **The derivative of `F`.** Away from `a = 0` and from the singularity, for `sgn = ±1`,
`F'(a) = 2 · (-(4πG_N/3)(ρ + ρ̃ + 3(wρ + P̃)) a)`. Here `ρ = ρ₀a^{-3(1+w)}`, `ρ̃ = ρ̃_sgn`, and
`P̃` is given by Eq. (16). -/
theorem hasDerivAt_friedmannF {c : Couplings} {K H0 rh w ρ₀ sgn x : ℝ} (hsg : sgn ^ 2 = 1)
    (hx : 0 < x) (hD : 0 < realityArg c K H0 rh w ρ₀ x) :
    HasDerivAt (friedmannF c K H0 rh w ρ₀ sgn)
      (2 * (-(4 * π * c.GN / 3) * (ρ₀ * x ^ (-(3 * (1 + w)))
        + rhoTilde sgn c.rhoS (rhoBH c.GN K H0 rh x) (ρ₀ * x ^ (-(3 * (1 + w))))
        + 3 * (w * (ρ₀ * x ^ (-(3 * (1 + w))))
          + pressureTilde c.rhoS
            (rhoTilde sgn c.rhoS (rhoBH c.GN K H0 rh x) (ρ₀ * x ^ (-(3 * (1 + w)))))
            (3 * (w * (ρ₀ * x ^ (-(3 * (1 + w))))) - ρ₀ * x ^ (-(3 * (1 + w)))))) * x)) x := by
  have hs := c.rhoS_pos.ne'
  have hsg0 : sgn ≠ 0 := by rintro rfl; norm_num at hsg
  have hρ := (hasDerivAt_rpow_const (p := -(3 * (1 + w))) (Or.inl hx.ne')).const_mul ρ₀
  have hb := hasDerivAt_rhoBH_x (K := K) (H0 := H0) (rh := rh) c.GN_pos.ne' hx.ne'
  have hR : HasDerivAt (realityArg c K H0 rh w ρ₀) _ x :=
    (((hb.sub hρ).const_mul 2).div_const c.rhoS).const_sub 1
  have h := ((((hR.sqrt hD.ne').const_mul sgn).const_add 1).const_mul c.rhoS |>.fun_add hρ
    |>.const_mul (8 * π * c.GN / 3) |>.fun_mul (hasDerivAt_pow 2 x)).sub_const K
  rw [show friedmannF c K H0 rh w ρ₀ sgn = fun a ↦ 8 * π * c.GN / 3 * (c.rhoS *
      (1 + sgn * √(realityArg c K H0 rh w ρ₀ a)) + ρ₀ * a ^ (-(3 * (1 + w)))) * a ^ 2 - K from
    funext fun a ↦ by rw [friedmannF_eq]; ring]
  refine h.congr_deriv ?_
  have hq2 := sq_sqrt hD.le
  have hq : √(realityArg c K H0 rh w ρ₀ x) ≠ 0 := (sqrt_pos.2 hD).ne'
  rw [rpow_sub_one hx.ne']
  change _ = 2 * (-(4 * π * c.GN / 3) * (ρ₀ * x ^ (-(3 * (1 + w)))
    + c.rhoS * (1 + sgn * √(realityArg c K H0 rh w ρ₀ x)) + 3 * (w * (ρ₀ * x ^ (-(3 * (1 + w))))
      + pressureTilde c.rhoS (c.rhoS * (1 + sgn * √(realityArg c K H0 rh w ρ₀ x)))
        (3 * (w * (ρ₀ * x ^ (-(3 * (1 + w))))) - ρ₀ * x ^ (-(3 * (1 + w)))))) * x)
  unfold realityArg at hq2 hq ⊢
  generalize √(1 - 2 * (rhoBH c.GN K H0 rh x - ρ₀ * x ^ (-(3 * (1 + w)))) / c.rhoS) = q
    at hq2 hq ⊢
  generalize rhoBH c.GN K H0 rh x = b at hq2 ⊢
  generalize x ^ (-(3 * (1 + w))) = r at hq2 ⊢
  have hden : c.rhoS - c.rhoS * (1 + sgn * q) ≠ 0 := by
    rw [show c.rhoS - c.rhoS * (1 + sgn * q) = -(c.rhoS * sgn * q) by ring]
    exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hs hsg0) hq)
  unfold pressureTilde
  field_simp
  field_simp at hq2
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  linear_combination 8 * c.GN * x * (q * (-4 * b + 3 * (1 + w) * (ρ₀ * r)) - 2 * c.rhoS * q ^ 3)
    * hsg - 2 * q * (8 * c.GN * x) * hq2

/-! ### Picard–Lindelöf for `ä = F'(a)/2` -/

section SecondOrder

variable {F : ℝ → ℝ} {a₀ : ℝ}

/-- The first-order system on `ℝ²` for `ä = F'(a)/2`: `(a, v) ↦ (v, F'(a)/2)`. -/
noncomputable def secondOrderField (F : ℝ → ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (y.2, deriv F y.1 / 2)

lemma contDiffAt_secondOrderField (hF : ContDiffAt ℝ 2 F a₀) (v₀ : ℝ) :
    ContDiffAt ℝ 1 (secondOrderField F) (a₀, v₀) := by
  have h : ContDiffAt ℝ 1 (deriv F) a₀ := hF.derivWithin (by norm_num)
  exact contDiffAt_snd.prodMk ((h.comp (a₀, v₀) contDiffAt_fst).div_const 2)

/-- A solution of `ä = F'(a)/2`, written as a curve in `ℝ²`, solves the first-order system. -/
lemma hasDerivAt_curve {f f' : ℝ → ℝ} {t : ℝ} (h1 : HasDerivAt f (f' t) t)
    (h2 : HasDerivAt f' (deriv F (f t) / 2) t) :
    HasDerivAt (fun t ↦ (f t, f' t)) (secondOrderField F (f t, f' t)) t :=
  h1.prodMk h2

/-- **Local uniqueness for `ä = F'(a)/2`.** Where `F` is `C²`, two solutions with the same
`a(t₀)` and `ȧ(t₀)` agree near `t₀`. This includes turning points `ȧ(t₀) = 0`. -/
theorem local_unique₂ (hF : ContDiffAt ℝ 2 F a₀) {t₀ : ℝ} {f f' g g' : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (f' t) t ∧ HasDerivAt f' (deriv F (f t) / 2) t)
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (g' t) t ∧ HasDerivAt g' (deriv F (g t) / 2) t)
    (hf0 : f t₀ = a₀) (hg0 : g t₀ = a₀) (h' : f' t₀ = g' t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨L, U, hU, hL⟩ := (contDiffAt_secondOrderField hF (f' t₀)).exists_lipschitzOnWith
  have curve : ∀ {f₁ f₁' : ℝ → ℝ}, (∀ᶠ t in 𝓝 t₀,
      HasDerivAt f₁ (f₁' t) t ∧ HasDerivAt f₁' (deriv F (f₁ t) / 2) t) → f₁ t₀ = a₀ →
      f₁' t₀ = f' t₀ → ∀ᶠ t in 𝓝 t₀,
        HasDerivAt (fun t ↦ (f₁ t, f₁' t)) (secondOrderField F (f₁ t, f₁' t)) t
          ∧ (f₁ t, f₁' t) ∈ U := by
    intro f₁ f₁' h h0 h0'
    have hc : ContinuousAt (fun t ↦ (f₁ t, f₁' t)) t₀ :=
      h.self_of_nhds.1.continuousAt.prodMk h.self_of_nhds.2.continuousAt
    exact (h.mono fun t ht ↦ hasDerivAt_curve ht.1 ht.2).and
      (hc.preimage_mem_nhds (by rw [h0, h0']; exact hU))
  have hcf := curve hf hf0 rfl
  have hcg := curve hg hg0 h'.symm
  have := ODE_solution_unique_of_eventually (v := fun _ ↦ secondOrderField F)
    (s := fun _ ↦ U) (Filter.Eventually.of_forall fun _ ↦ hL) hcf hcg (by rw [hf0, hg0, h'])
  filter_upwards [this] with t ht
  exact congrArg Prod.fst ht

/-- **Local existence for `ä = F'(a)/2`.** Where `F` is `C²`, for any `v₀` there is a local
solution with `a(t₀) = a₀` and `ȧ(t₀) = v₀`. If `v₀² = F(a₀)`, it also solves `ȧ² = F(a)` near
`t₀`. This includes a turning point, `v₀ = 0` and `F(a₀) = 0`. -/
theorem exists_local_solution₂ (hF : ContDiffAt ℝ 2 F a₀) (v₀ t₀ : ℝ) :
    ∃ f f' : ℝ → ℝ, f t₀ = a₀ ∧ f' t₀ = v₀ ∧ ∀ᶠ t in 𝓝 t₀,
      HasDerivAt f (f' t) t ∧ HasDerivAt f' (deriv F (f t) / 2) t
        ∧ (v₀ ^ 2 = F a₀ → deriv f t ^ 2 = F (f t)) := by
  obtain ⟨γ, hγ0, ε, hε, hγ⟩ := (contDiffAt_secondOrderField hF
    v₀).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  set f := fun t ↦ (γ t).1
  set f' := fun t ↦ (γ t).2
  have hd : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt f (f' t) t ∧ HasDerivAt f' (deriv F (f t) / 2) t := fun t ht ↦
    ⟨(hasFDerivAt_fst.comp_hasDerivAt t (hγ t ht) :),
      (hasFDerivAt_snd.comp_hasDerivAt t (hγ t ht) :)⟩
  have hI : Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : ContinuousAt f t₀ := (hd t₀ ⟨by linarith, by linarith⟩).1.continuousAt
  have hf0 : f t₀ = a₀ := by simp [f, hγ0]
  have hF' : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ F (f t) :=
    hcont.eventually (hf0 ▸ (hF.eventually (by simp)).mono fun _ h ↦
      h.differentiableAt (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 ((Filter.eventually_of_mem hI
    fun t ht ↦ hd t ht).and hF')
  refine ⟨f, f', hf0, by simp [f', hγ0], ?_⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht
  refine ⟨(hball t ht).1.1, (hball t ht).1.2, fun hv ↦ ?_⟩
  -- `ȧ² - F(a)` is constant on the ball.
  have hE : ∀ s ∈ Metric.ball t₀ δ,
      HasDerivAt (fun s ↦ f' s ^ 2 - F (f s)) 0 s := fun s hs ↦ by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hball s hs
    have h4 := (h2.fun_pow 2).fun_sub (h3.hasDerivAt.comp s h1)
    simp only [Function.comp_def] at h4
    convert h4 using 1
    ring
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t₀ δ).isPreconnected
    (fun s hs ↦ (hE s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hE s hs).deriv) ht (Metric.mem_ball_self hδ)
  simp only [hf0, show f' t₀ = v₀ by simp [f', hγ0], hv, sub_self] at hconst
  rw [(hball t ht).1.1.deriv]
  linarith

end SecondOrder

namespace BraneCosmology

variable (M : BraneCosmology)

/-- The right side of `ȧ² = F(a)` for this history, with `P = wρ` on the branch `sgn`. -/
noncomputable def F (w sgn : ℝ) : ℝ → ℝ :=
  friedmannF M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) sgn

/-- Away from the singularity the argument of the square root is positive (reality bound). -/
theorem realityArg_pos {w sgn : ℝ} (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) {t : ℝ}
    (hns : M.ρt t ≠ M.c.rhoS) :
    0 < realityArg M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w))) (M.a t) := by
  refine lt_of_le_of_ne ?_ (M.realityArg_ne hw hbr hns).symm
  have hr := M.reality t
  rw [M.rho_barotropic hw t] at hr
  unfold realityArg
  rw [sub_nonneg, div_le_one M.c.rhoS_pos]
  exact hr

/-- **The acceleration equation is `ä = F'(a)/2`.** For a solution with `P = wρ` on the branch
`sgn = ±1`, at every time away from the singularity. This includes the times with `H = 0`. -/
theorem accel_eq_deriv (hsol : M.IsSolution) {w sgn : ℝ} (hsg : sgn ^ 2 = 1)
    (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) {t : ℝ}
    (hns : M.ρt t ≠ M.c.rhoS) :
    HasDerivAt (deriv M.a) (deriv (M.F w sgn) (M.a t) / 2) t := by
  have h := (hsol t).1
  have hP := (hsol t).2 hns
  unfold AccelAt at h
  unfold F
  rw [(hasDerivAt_friedmannF hsg (M.a_pos t) (M.realityArg_pos hw hbr hns)).deriv,
    mul_div_cancel_left₀ _ two_ne_zero]
  convert h using 2
  rw [hP, hw t, hbr t, M.rho_barotropic hw t]
  rfl

/-- **ROADMAP M4.2 at turning points.** Take a solution with `P = wρ` on the branch
`sgn = ±1`, and a time `t₀` away from the singularity. Every solution `f` of `ä = F'(a)/2` near
`t₀` with `f(t₀) = a(t₀)` and `ḟ(t₀) = ȧ(t₀)` is equal to the scale factor near `t₀`. This
also holds when `H(t₀) = 0`. -/
theorem locally_determined₂ (hsol : M.IsSolution) {w sgn : ℝ} (hsg : sgn ^ 2 = 1)
    (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) {t₀ : ℝ}
    (hns : M.ρt t₀ ≠ M.c.rhoS) {f f' : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (f' t) t ∧ HasDerivAt f' (deriv (M.F w sgn) (f t) / 2) t)
    (hf0 : f t₀ = M.a t₀) (hf'0 : f' t₀ = deriv M.a t₀) : f =ᶠ[𝓝 t₀] M.a := by
  have hF : ContDiffAt ℝ 2 (M.F w sgn) (M.a t₀) :=
    contDiffAt_friedmannF (M.a_pos t₀).ne' (M.realityArg_ne hw hbr hns)
  have hns' : ∀ᶠ t in 𝓝 t₀, M.ρt t ≠ M.c.rhoS :=
    M.ρt_diff.continuous.continuousAt.eventually_ne hns
  have hM : ∀ᶠ t in 𝓝 t₀, HasDerivAt M.a (deriv M.a t) t
      ∧ HasDerivAt (deriv M.a) (deriv (M.F w sgn) (M.a t) / 2) t := by
    filter_upwards [hns'] with t ht
    exact ⟨(M.a_diff t).hasDerivAt, M.accel_eq_deriv hsol hsg hw hbr ht⟩
  exact local_unique₂ hF hf hM hf0 rfl hf'0

/-- **A solution rests only at an equilibrium.** If `ȧ = 0` on a neighbourhood of `t₀`, away
from the singularity, then `F(a) = 0` and `F'(a) = 0` at `t₀`. So at a turning point with
`F'(a) ≠ 0` the solution does not stay at rest. Compare the static instances, which are not
solutions (`static_not_isSolution`). -/
theorem equilibrium_of_rest (hsol : M.IsSolution) {w sgn : ℝ} (hsg : sgn ^ 2 = 1)
    (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t)) {t₀ : ℝ}
    (hns : M.ρt t₀ ≠ M.c.rhoS) (hrest : deriv M.a =ᶠ[𝓝 t₀] fun _ ↦ 0) :
    M.F w sgn (M.a t₀) = 0 ∧ deriv (M.F w sgn) (M.a t₀) = 0 := by
  have h1 := M.accel_eq_deriv hsol hsg hw hbr hns
  have h2 : HasDerivAt (deriv M.a) 0 t₀ :=
    (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq hrest
  have h3 := M.deriv_a_sq_eq hw hbr t₀
  rw [hrest.self_of_nhds] at h3
  refine ⟨by unfold F; rw [← h3]; ring, ?_⟩
  linarith [h1.unique h2]

/-- **The radiation bounce is fixed by its data at the bounce.** At `t = 0`, `H = 0`. Every
solution of `ä = F'(a)/2` near `t = 0` with `a(0)` equal to the bounce's and `ȧ(0) = 0` is the
bounce near `t = 0`. -/
theorem radiationBounce_determined {c : Couplings} {K rh : ℝ} (hK : 0 < K) (hrh : 0 ≤ rh)
    (hrc : 2 * rh ≤ c.rc) {f f' : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝 0, HasDerivAt f (f' t) t
      ∧ HasDerivAt f' (deriv ((radiationBounce c K rh hK hrh hrc).F (1 / 3) 1) (f t) / 2) t)
    (hf0 : f 0 = (radiationBounce c K rh hK hrh hrc).a 0) (hf'0 : f' 0 = 0) :
    f =ᶠ[𝓝 0] (radiationBounce c K rh hK hrh hrc).a := by
  have hs := c.rhoS_pos
  have hw : ∀ t, (radiationBounce c K rh hK hrh hrc).P t
      = 1 / 3 * (radiationBounce c K rh hK hrh hrc).ρ t := fun t ↦ by
    change WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t) / 3
      = 1 / 3 * WhiteHole.rhoBH c.GN K 1 rh (bounceA K c.rc rh t)
    ring
  have hH : deriv (radiationBounce c K rh hK hrh hrc).a 0 = 0 := by
    change deriv (bounceA K c.rc rh) 0 = 0
    rw [(hasDerivAt_bounceA hK c.rc_pos 0).deriv]
    simp
  refine (radiationBounce c K rh hK hrh hrc).locally_determined₂
    (radiationBounce_isSolution hK hrh hrc) (by norm_num) hw
    (radiationBounce_selfAccelerating c hK hrh hrc) ?_ hf hf0 (hf'0.trans hH.symm)
  change 2 * c.rhoS ≠ c.rhoS
  linarith

end BraneCosmology

end WhiteHole
