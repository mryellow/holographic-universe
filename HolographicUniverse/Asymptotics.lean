import HolographicUniverse.Dynamics
import HolographicUniverse.Horizon

/-!
# Asymptotics (ROADMAP M4.4)

**Late times.** Let `P = wρ` with `w > -1`, on one branch `sgn` at every time, and let
`a → ∞`. Then `ρ → 0`, `ρ_BH → 0`, `ρ̃ → ρ̃_s(1 + sgn)` and
`H² → (8πG_N/3) ρ̃_s (1 + sgn)` (`BraneCosmology.tendsto_late`).

* On the self-accelerating branch, `H → 1/r_c`: the brane approaches de Sitter space. An
  expanding history with `ρ ≥ 0` and `a(t₀)² > 2𝒦r_c²` keeps expanding, has `a → ∞`, and so
  has `H → 1/r_c` (`BraneCosmology.tendsto_deSitter`). It is not necessary to assume `a → ∞`.
* On the normal branch, `ρ̃ → 0` and `H → 0` (`BraneCosmology.tendsto_normal`). That `a → ∞`
  is a hypothesis here: a closed universe on this branch can recollapse.

**Standard FRW.** On the normal branch, `|ρ̃| ≤ √(2ρ̃_s |ρ - ρ_BH|)` (`abs_rhoTilde_minus_le`).
So the Friedmann equation is the standard one up to a relative error `√(2ρ̃_s/ρ)` when
`0 ≤ ρ_BH ≤ ρ` (`BraneCosmology.normal_branch_frw`, `normal_branch_frw_of_le`). It is standard
FRW when `ρ ≫ ρ̃_s`.

**Near the singularity.** As `ρ̃ → ρ̃_s` from below, with `3P - ρ` near a value below `2ρ̃_s`,
`P̃ → +∞` (`tendsto_pressureTilde_atTop`). In a `BraneCosmology`, `ρ̃` is differentiable at every
time. `(ρ̃ - ρ̃_s)² = ρ̃_s² - 2ρ̃_s(ρ_BH - ρ)` then has derivative zero at the singularity, and so
`H (3P - ρ - 2ρ̃_s) = 0` there (`BraneCosmology.singularity_at_rest`). For `3P ≤ ρ`, the brane
is at rest at the singularity (`singularity_at_rest_of_le`), and it is strictly outside the
horizon (`singularity_outside_of_le`). So a history that reaches the singularity with `H ≠ 0`,
as the paper's white-hole history does, has a `ρ̃` that is not differentiable there. Generically
`ρ̃ - ρ̃_s ∝ √|a - a_s|` by Eq. (26). The singularity can only be an end of such a history.
-/

namespace WhiteHole

open Real Set Filter Topology

/-! ### Limits of the branches -/

/-- As `ρ_BH, ρ → 0`, the branch `ρ̃_sgn` tends to `ρ̃_s(1 + sgn)`. -/
theorem tendsto_rhoTilde (sgn s : ℝ) {ι : Type*} {l : Filter ι} {b ρ : ι → ℝ}
    (hb : Tendsto b l (𝓝 0)) (hρ : Tendsto ρ l (𝓝 0)) :
    Tendsto (fun i ↦ rhoTilde sgn s (b i) (ρ i)) l (𝓝 (s * (1 + sgn))) := by
  have h : Tendsto (fun i ↦ rhoTilde sgn s (b i) (ρ i)) l (𝓝 (rhoTilde sgn s 0 0)) := by
    unfold rhoTilde
    exact tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hb.sub hρ)).div_const s)).sqrt))
  convert h using 2
  unfold rhoTilde
  simp

/-- **The normal branch is small.** Under the reality bound (30),
`|ρ̃_-| ≤ √(2ρ̃_s |ρ - ρ_BH|)`. -/
theorem abs_rhoTilde_minus_le {s b ρ : ℝ} (hs : 0 < s) (hreal : 2 * (b - ρ) ≤ s) :
    |rhoTilde (-1) s b ρ| ≤ √(2 * s * |ρ - b|) := by
  unfold rhoTilde
  set y := 2 * (b - ρ) / s with hy_def
  have hy : y ≤ 1 := by rw [hy_def, div_le_one hs]; exact hreal
  have key : |1 - √(1 - y)| ≤ √|y| := by
    apply abs_le_sqrt
    have h1 : 0 ≤ 1 - y := by linarith
    have hq := sq_sqrt h1
    have hq0 := sqrt_nonneg (1 - y)
    rcases le_total y 0 with hy0 | hy0
    · rw [abs_of_nonpos hy0]
      nlinarith
    · rw [abs_of_nonneg hy0]
      nlinarith
  have hsq : √(2 * s * |ρ - b|) = s * √|y| := by
    rw [show 2 * s * |ρ - b| = s ^ 2 * |y| by
      rw [hy_def, abs_div, abs_of_pos hs, abs_mul, abs_two, abs_sub_comm]
      field_simp, sqrt_mul (sq_nonneg _), sqrt_sq hs.le]
  rw [hsq, show s * (1 + -1 * √(1 - y)) = s * (1 - √(1 - y)) by ring, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left key hs.le

/-- **Eq. (16) at the singularity.** As `ρ̃ → ρ̃_s` from below, with `T = 3P - ρ → T₀ < 2ρ̃_s`,
the induced pressure tends to `+∞`. -/
theorem tendsto_pressureTilde_atTop {ι : Type*} {l : Filter ι} {s T₀ : ℝ} {x T : ι → ℝ}
    (hs : 0 < s) (hx : Tendsto x l (𝓝 s)) (hxl : ∀ᶠ i in l, x i < s)
    (hT : Tendsto T l (𝓝 T₀)) (hT₀ : T₀ < 2 * s) :
    Tendsto (fun i ↦ pressureTilde s (x i) (T i)) l atTop := by
  unfold pressureTilde
  have hnum : Tendsto (fun i ↦ x i ^ 2 + s * (x i - T i)) l (𝓝 (s ^ 2 + s * (s - T₀))) :=
    (hx.pow 2).add (tendsto_const_nhds.mul (hx.sub hT))
  have hpos : 0 < s ^ 2 + s * (s - T₀) := by nlinarith
  have hden : Tendsto (fun i ↦ 3 * (s - x i)) l (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hxl.mono fun i hi ↦ ?_⟩
    · have := (tendsto_const_nhds (x := s)).sub hx |>.const_mul 3
      rwa [sub_self, mul_zero] at this
    · simp only [mem_Ioi]
      linarith
  simp_rw [div_eq_mul_inv]
  exact hnum.pos_mul_atTop hpos (tendsto_inv_nhdsGT_zero.comp hden)

namespace BraneCosmology

variable (M : BraneCosmology)

/-! ### Late times -/

/-- **Late times, on either branch.** Let `P = wρ` with `w > -1`, let `ρ̃` be on the branch
`sgn` at every time, and let `a → ∞`. Then `ρ → 0`, `ρ̃ → ρ̃_s(1 + sgn)`, and
`H² → (8πG_N/3) ρ̃_s(1 + sgn)`. -/
theorem tendsto_late {w sgn : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (hw1 : -1 < w)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t))
    (ha : Tendsto M.a atTop atTop) :
    Tendsto M.ρ atTop (𝓝 0) ∧ Tendsto M.ρt atTop (𝓝 (M.c.rhoS * (1 + sgn))) ∧
      Tendsto (fun t ↦ M.H t ^ 2) atTop
        (𝓝 (8 * π * M.c.GN / 3 * (M.c.rhoS * (1 + sgn)))) := by
  have hρ : Tendsto M.ρ atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < 3 * (1 + w))).comp ha).const_mul
      (M.ρ 0 * M.a 0 ^ (3 * (1 + w)))
    rw [mul_zero] at h
    exact h.congr fun t ↦ (M.rho_barotropic hw t).symm
  have hb : Tendsto M.rhoBH atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop four_ne_zero).comp ha))).const_mul
      M.rhoBH₁
    rw [mul_zero] at h
    refine h.congr fun t ↦ ?_
    rw [← M.rhoBH_mul_a4 t]
    simp only [Function.comp_apply]
    field_simp [(M.a_pos t).ne']
  have hρt : Tendsto M.ρt atTop (𝓝 (M.c.rhoS * (1 + sgn))) :=
    (tendsto_rhoTilde sgn _ hb hρ).congr fun t ↦ (hbr t).symm
  refine ⟨hρ, hρt, ?_⟩
  have hK : Tendsto (fun t ↦ M.K / M.a t ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp ha)).const_mul
      M.K
    rw [mul_zero] at h
    exact h.congr fun t ↦ by simp [div_eq_mul_inv]
  have h := ((hρ.add hρt).const_mul (8 * π * M.c.GN / 3)).sub hK
  rw [zero_add, sub_zero] at h
  refine h.congr fun t ↦ ?_
  have := M.friedmann t
  unfold H
  linarith

/-- If `H² → L²` with `L ≥ 0`, and the brane is eventually expanding, then `H → L`. -/
theorem tendsto_hubble_of_sq {L : ℝ} (hL : 0 ≤ L)
    (hH2 : Tendsto (fun t ↦ M.H t ^ 2) atTop (𝓝 (L ^ 2)))
    (hpos : ∀ᶠ t in atTop, 0 < deriv M.a t) : Tendsto M.H atTop (𝓝 L) := by
  have h := hH2.sqrt
  rw [sqrt_sq hL] at h
  refine h.congr' (hpos.mono fun t ht ↦ ?_)
  exact sqrt_sq (div_pos ht (M.a_pos t)).le

/-- **The self-accelerating branch keeps expanding.** Let `ρ ≥ 0` and `ρ̃ ≥ ρ̃_s` at every time.
Then `H² ≥ 1/(2r_c²) - 𝒦/a²`. If at `t₀` the brane expands and `a(t₀)² > 2𝒦r_c²`, it expands at
every later time, and `a → ∞`. -/
theorem expands_of_self_acc {t₀ : ℝ} (hρ : ∀ t, 0 ≤ M.ρ t) (hρt : ∀ t, M.c.rhoS ≤ M.ρt t)
    (h₀ : 2 * M.K * M.c.rc ^ 2 < M.a t₀ ^ 2) (hv : 0 < deriv M.a t₀) :
    (∀ t, t₀ ≤ t → 0 < deriv M.a t) ∧ Tendsto M.a atTop atTop := by
  have hK := M.K_pos
  have hrc := M.c.rc_pos
  have ha₀ := M.a_pos t₀
  -- A level `a₁ < a(t₀)` with `a₁² > 2𝒦r_c²`.
  set ac := √(2 * M.K * M.c.rc ^ 2)
  have hac : ac < M.a t₀ := (sqrt_lt' ha₀).2 h₀
  have hac0 : 0 ≤ ac := sqrt_nonneg _
  set a₁ := (ac + M.a t₀) / 2
  have ha₁ : ac < a₁ := by simp only [a₁]; linarith
  have ha₁' : a₁ < M.a t₀ := by simp only [a₁]; linarith
  have ha₁0 : 0 < a₁ := by linarith
  have ha₁sq : 2 * M.K * M.c.rc ^ 2 < a₁ ^ 2 := by
    have := pow_lt_pow_left₀ ha₁ hac0 two_ne_zero
    rwa [sq_sqrt (by positivity)] at this
  set κ := 1 / (2 * M.c.rc ^ 2) - M.K / a₁ ^ 2
  have hκ : 0 < κ := by
    simp only [κ, sub_pos]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  -- `H² ≥ κ` wherever `a > a₁`.
  have hH : ∀ t, a₁ < M.a t → κ ≤ M.H t ^ 2 := fun t ht ↦ by
    have hF := M.friedmann t
    have hs := M.c.gN_mul_rhoS
    have hGρ : 0 ≤ 8 * π * M.c.GN / 3 * M.ρ t := by have := M.c.GN_pos; have := hρ t; positivity
    have hG : 8 * π * M.c.GN / 3 * M.c.rhoS ≤ 8 * π * M.c.GN / 3 * M.ρt t :=
      mul_le_mul_of_nonneg_left (hρt t) (by have := M.c.GN_pos; positivity)
    have hKa : M.K / M.a t ^ 2 ≤ M.K / a₁ ^ 2 :=
      div_le_div_of_nonneg_left hK.le (by positivity) (pow_le_pow_left₀ ha₁0.le ht.le 2)
    have he : 2 * (1 / (2 * M.c.rc)) ^ 2 = 1 / (2 * M.c.rc ^ 2) := by field_simp
    simp only [κ]
    unfold H
    nlinarith
  have hd : ∀ x, deriv (fun t ↦ -M.a t) x = -deriv M.a x := fun x ↦
    (M.a_diff x).hasDerivAt.neg.deriv
  have hne : ∀ t, (fun t ↦ -M.a t) t < -a₁ → deriv (fun t ↦ -M.a t) t ≠ 0 := fun t ht ↦ by
    rw [hd, neg_ne_zero]
    have h := hH t (by simp only at ht; linarith)
    intro h0
    rw [H, h0, zero_div, sq, zero_mul] at h
    linarith
  have hfwd : ∀ t, t₀ ≤ t → a₁ < M.a t ∧ 0 < deriv M.a t := fun t ht ↦ by
    have := lt_and_deriv_neg_of_ge (f := fun t ↦ -M.a t) (h := -a₁) M.a_diff.neg hne
      (by linarith) (by rw [hd, neg_lt_zero]; exact hv) ht
    rw [hd, neg_lt_zero] at this
    exact ⟨by linarith [this.1], this.2⟩
  refine ⟨fun t ht ↦ (hfwd t ht).2, ?_⟩
  -- `ȧ ≥ C := √κ a₁` from `t₀` on, so `a` grows at least linearly.
  set C := √κ * a₁
  have hC : 0 < C := mul_pos (sqrt_pos.2 hκ) ha₁0
  have hCle : ∀ t, t₀ ≤ t → C ≤ deriv M.a t := fun t ht ↦ by
    obtain ⟨hat, hvt⟩ := hfwd t ht
    have hat0 := M.a_pos t
    rw [← pow_le_pow_iff_left₀ hC.le hvt.le two_ne_zero]
    have h1 := hH t hat
    have h2 : a₁ ^ 2 ≤ M.a t ^ 2 := pow_le_pow_left₀ ha₁0.le hat.le 2
    have h3 : deriv M.a t ^ 2 = M.H t ^ 2 * M.a t ^ 2 := by unfold H; field_simp
    rw [h3, mul_pow, sq_sqrt hκ.le]
    exact mul_le_mul h1 h2 (by positivity) (sq_nonneg _)
  have hgrow : ∀ t, t₀ ≤ t → C * (t - t₀) ≤ M.a t - M.a t₀ := fun t ht ↦
    (convex_Ici t₀).mul_sub_le_image_sub_of_le_deriv M.a_diff.continuous.continuousOn
      M.a_diff.differentiableOn (fun x hx ↦ by
        rw [interior_Ici] at hx
        exact hCle x (le_of_lt hx)) t₀ self_mem_Ici t ht ht
  have hlin : Tendsto (fun t ↦ C * (t + -t₀) + M.a t₀) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop hC)
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop t₀] with t ht
  have := hgrow t ht
  linarith

/-- **M4.4, self-accelerating branch: de Sitter at late times.** Let `P = wρ` with `w > -1` and
`ρ ≥ 0`, and let `ρ̃` be on the branch `ρ̃_+` at every time. If at `t₀` the brane expands and
`a(t₀)² > 2𝒦r_c²`, then `a → ∞`, `ρ̃ → 2ρ̃_s`, and `H → 1/r_c`. -/
theorem tendsto_deSitter {w t₀ : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (hw1 : -1 < w)
    (hbr : ∀ t, M.ρt t = rhoTilde 1 M.c.rhoS (M.rhoBH t) (M.ρ t)) (hρ : ∀ t, 0 ≤ M.ρ t)
    (h₀ : 2 * M.K * M.c.rc ^ 2 < M.a t₀ ^ 2) (hv : 0 < deriv M.a t₀) :
    Tendsto M.a atTop atTop ∧ Tendsto M.ρt atTop (𝓝 (2 * M.c.rhoS)) ∧
      Tendsto M.H atTop (𝓝 (1 / M.c.rc)) := by
  have hρt : ∀ t, M.c.rhoS ≤ M.ρt t := fun t ↦ hbr t ▸ le_rhoTilde_plus M.c.rhoS_pos
  obtain ⟨hexp, ha⟩ := M.expands_of_self_acc hρ hρt h₀ hv
  obtain ⟨-, hρt', hH2⟩ := M.tendsto_late hw hw1 hbr ha
  refine ⟨ha, by rwa [mul_comm, one_add_one_eq_two] at hρt', ?_⟩
  have he : 8 * π * M.c.GN / 3 * (M.c.rhoS * (1 + 1)) = (1 / M.c.rc) ^ 2 := by
    rw [← mul_assoc, M.c.gN_mul_rhoS]
    have := M.c.rc_pos
    field_simp
    ring
  rw [he] at hH2
  exact M.tendsto_hubble_of_sq (by have := M.c.rc_pos; positivity) hH2
    ((eventually_ge_atTop t₀).mono hexp)

/-- **M4.4, normal branch: Minkowski at late times.** Let `P = wρ` with `w > -1`, and let `ρ̃`
be on the branch `ρ̃_-` at every time. If `a → ∞`, then `ρ̃ → 0` and `H → 0`. -/
theorem tendsto_normal {w : ℝ} (hw : ∀ t, M.P t = w * M.ρ t) (hw1 : -1 < w)
    (hbr : ∀ t, M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t))
    (ha : Tendsto M.a atTop atTop) :
    Tendsto M.ρt atTop (𝓝 0) ∧ Tendsto M.H atTop (𝓝 0) := by
  obtain ⟨-, hρt, hH2⟩ := M.tendsto_late hw hw1 hbr ha
  norm_num at hρt hH2
  refine ⟨hρt, ?_⟩
  have h := hH2.sqrt
  rw [sqrt_zero] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact h.congr fun t ↦ sqrt_sq_eq_abs _

/-! ### Standard FRW on the normal branch -/

/-- **The normal branch is standard FRW up to `√(2ρ̃_s|ρ - ρ_BH|)`.** On the branch `ρ̃_-`,
`|H² + 𝒦/a² - (8πG_N/3) ρ| ≤ (8πG_N/3) √(2ρ̃_s |ρ - ρ_BH|)`. -/
theorem normal_branch_frw {t : ℝ} (hbr : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t)) :
    |M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t|
      ≤ 8 * π * M.c.GN / 3 * √(2 * M.c.rhoS * |M.ρ t - M.rhoBH t|) := by
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  have hF := M.friedmann t
  rw [show M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t
      = 8 * π * M.c.GN / 3 * M.ρt t by unfold H; linarith, abs_mul, abs_of_pos hG, hbr]
  exact mul_le_mul_of_nonneg_left (abs_rhoTilde_minus_le M.c.rhoS_pos (M.reality t))
    hG.le

/-- **M4.4: standard FRW when `ρ ≫ ρ̃_s`.** On the branch `ρ̃_-`, with `0 ≤ ρ_BH ≤ ρ` and
`ρ > 0`, the relative error of the standard Friedmann equation is at most `√(2ρ̃_s/ρ)`:
`|H² + 𝒦/a² - (8πG_N/3) ρ| ≤ √(2ρ̃_s/ρ) · (8πG_N/3) ρ`. -/
theorem normal_branch_frw_of_le {t : ℝ}
    (hbr : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t))
    (hb : 0 ≤ M.rhoBH t) (hρ : M.rhoBH t ≤ M.ρ t) (hρ0 : 0 < M.ρ t) :
    |M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t|
      ≤ √(2 * M.c.rhoS / M.ρ t) * (8 * π * M.c.GN / 3 * M.ρ t) := by
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  refine (M.normal_branch_frw hbr).trans ?_
  have hs := M.c.rhoS_pos
  have h1 : √(2 * M.c.rhoS * |M.ρ t - M.rhoBH t|) ≤ √(2 * M.c.rhoS / M.ρ t) * M.ρ t := by
    have e : 2 * M.c.rhoS * M.ρ t = 2 * M.c.rhoS / M.ρ t * M.ρ t ^ 2 := by
      field_simp
    rw [abs_of_nonneg (by linarith)]
    calc √(2 * M.c.rhoS * (M.ρ t - M.rhoBH t)) ≤ √(2 * M.c.rhoS * M.ρ t) :=
          sqrt_le_sqrt (by nlinarith)
      _ = _ := by rw [e, sqrt_mul (by positivity), sqrt_sq hρ0.le]
  calc 8 * π * M.c.GN / 3 * √(2 * M.c.rhoS * |M.ρ t - M.rhoBH t|)
      ≤ 8 * π * M.c.GN / 3 * (√(2 * M.c.rhoS / M.ρ t) * M.ρ t) :=
        mul_le_mul_of_nonneg_left h1 hG.le
    _ = _ := by ring

/-! ### The singularity -/

/-- **At the singularity, `H = 0` or `3P - ρ = 2ρ̃_s`.** In a `BraneCosmology`, `ρ̃` is
differentiable. The function `(ρ̃ - ρ̃_s)² = ρ̃_s² - 2ρ̃_s(ρ_BH - ρ)` has derivative zero where
`ρ̃ = ρ̃_s`. By Eq. (12) and `ρ_BH ∝ a⁻⁴`, that derivative is `-2ρ̃_s H (3P - ρ - 2ρ̃_s)`. -/
theorem singularity_at_rest {t : ℝ} (h : M.ρt t = M.c.rhoS) :
    deriv M.a t = 0 ∨ 3 * M.P t - M.ρ t = 2 * M.c.rhoS := by
  have hs := M.c.rhoS_pos
  have ha := M.a_pos t
  have hB : ∀ τ, M.rhoBH τ = M.rhoBH₁ / M.a τ ^ 4 := fun τ ↦
    (eq_div_iff (pow_pos (M.a_pos τ) 4).ne').2 (M.rhoBH_mul_a4 τ)
  have hq : (fun τ ↦ (M.ρt τ - M.c.rhoS) ^ 2)
      = fun τ ↦ M.c.rhoS ^ 2 - 2 * M.c.rhoS * (M.rhoBH₁ / M.a τ ^ 4 - M.ρ τ) := by
    funext τ
    have := M.isInduced τ
    unfold IsInduced at this
    rw [hB τ] at this
    linear_combination this
  have hL : HasDerivAt (fun τ ↦ (M.ρt τ - M.c.rhoS) ^ 2) 0 t := by
    have := ((M.ρt_diff t).hasDerivAt.sub_const M.c.rhoS).fun_pow 2
    simpa [h] using this
  have hR := (((hasDerivAt_const t M.rhoBH₁).fun_div ((M.a_diff t).hasDerivAt.fun_pow 4)
    (pow_pos ha 4).ne').fun_sub (M.ρ_diff t).hasDerivAt).const_mul (2 * M.c.rhoS)
    |>.const_sub (M.c.rhoS ^ 2)
  rw [← hq] at hR
  have e := hR.unique hL
  rw [M.continuity t] at e
  have hsing := (M.singularity_iff t).1 h
  rw [hB t] at hsing
  have key : deriv M.a t * (3 * M.P t - M.ρ t - 2 * M.c.rhoS) = 0 := by
    have hB₁ : M.rhoBH₁ = (M.ρ t + M.c.rhoS / 2) * M.a t ^ 4 := by
      field_simp at hsing
      linear_combination hsing / 2
    rw [hB₁] at e
    field_simp at e
    norm_num at e
    have e' : M.a t ^ 3 * (deriv M.a t * (3 * M.P t - M.ρ t - 2 * M.c.rhoS)) = 0 := by
      linear_combination e.resolve_left hs.ne' / 2
    exact (mul_eq_zero.1 e').resolve_left (pow_pos ha 3).ne'
  rcases mul_eq_zero.1 key with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- For `3P ≤ ρ` (radiation, dust, and any `P ≤ ρ/3`), the brane is at rest at the
singularity. -/
theorem singularity_at_rest_of_le {t : ℝ} (h : M.ρt t = M.c.rhoS) (hP : 3 * M.P t ≤ M.ρ t) :
    deriv M.a t = 0 :=
  (M.singularity_at_rest h).resolve_right fun e ↦ by linarith [M.c.rhoS_pos]

/-- **In a `BraneCosmology`, the singularity is outside the horizon.** For `3P ≤ ρ`, the brane
is at rest at the singularity, and `|H| = 0 < 1/(2r_c)`. So it is strictly outside the
horizon (`singularity_inside_iff`). -/
theorem singularity_outside_of_le {t : ℝ} (h : M.ρt t = M.c.rhoS) (hP : 3 * M.P t ≤ M.ρ t) :
    0 < blacken M.rh (braneRadius M.K (M.a t)) := by
  rw [← not_le, M.singularity_inside_iff h, H, M.singularity_at_rest_of_le h hP, zero_div,
    abs_zero, not_le]
  have := M.c.rc_pos
  positivity

end BraneCosmology

end WhiteHole
