import HolographicUniverse.TurningPoint

/-!
# Maximal solutions (ROADMAP M4.2, global part)

Mathlib proves local existence and uniqueness (Picard–Lindelöf). This file extends a local
solution of an autonomous ODE `ẋ = v(x)` to a maximal open interval of existence. The vector
field `v` is `C¹` on an open set `U`, and solutions stay in `U`.

* `IsSolOn.eqOn`: two solutions on an open interval that agree at one time agree on the whole
  interval.
* `exists_isMaximalSolution`: every initial value in `U` has a maximal solution. Every other
  solution with the same initial value lives on a sub-interval and agrees with it there
  (`IsMaximalSolution.eqOn`).
* `IsMaximalSolution.eventually_not_mem_right`, `..._left`: at a finite end of the maximal
  interval, the solution leaves every compact subset of `U`. So a solution that stays in a
  compact subset of `U` exists for all time (`IsMaximalSolution.eq_univ_of_mem`).

Then the second-order equation `ä = F'(a)/2` (`TurningPoint.lean`), on an open set `D` of
scale factors where `F` is `C²`:

* `exists_isMaximalSolution₂`: maximal solutions exist. If `ȧ² = F(a)` at the initial time,
  it holds on the whole maximal interval (`IsMaximalSolution.energy₂`).
* `IsMaximalSolution.eventually_fst_not_mem_right`, `..._left`: at a finite end of the maximal
  interval, `a` leaves every compact subset of `D`.

For the brane cosmology with `P = wρ`, `D` is the set of `a > 0` away from the pressure
singularity (`braneDomain`, `isOpen_braneDomain`). So a history of `ä = F'(a)/2` that ends
in finite time ends at `a → 0`, at the pressure singularity, or at `a → ∞`.

* `BraneCosmology.maximal_eq`: a solution (`IsSolution`) with `P = wρ` on a fixed branch that
  never reaches the singularity is the maximal solution of its data, and that maximal solution
  exists for all time.
-/

namespace WhiteHole

open Real Set Topology Metric
open scoped NNReal

section Autonomous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E → E} {U : Set E}

/-- `γ` solves `ẋ = v(x)` at every time in `I`, and stays in `U` there. -/
def IsSolOn (v : E → E) (U : Set E) (γ : ℝ → E) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, HasDerivAt γ (v (γ t)) t ∧ γ t ∈ U

lemma IsSolOn.mono {γ : ℝ → E} {I I' : Set ℝ} (h : IsSolOn v U γ I) (hI : I' ⊆ I) :
    IsSolOn v U γ I' := fun t ht ↦ h t (hI ht)

/-- Local uniqueness at a point where `v` is `C¹`. -/
theorem eventuallyEq_of_contDiffAt {γ γ' : ℝ → E} {t : ℝ} (hv : ContDiffAt ℝ 1 v (γ t))
    (hγ : ∀ᶠ s in 𝓝 t, HasDerivAt γ (v (γ s)) s)
    (hγ' : ∀ᶠ s in 𝓝 t, HasDerivAt γ' (v (γ' s)) s) (h : γ t = γ' t) : γ =ᶠ[𝓝 t] γ' := by
  obtain ⟨K, s, hs, hl⟩ := hv.exists_lipschitzOnWith
  have hc : ContinuousAt γ t := hγ.self_of_nhds.continuousAt
  have hc' : ContinuousAt γ' t := hγ'.self_of_nhds.continuousAt
  exact ODE_solution_unique_of_eventually (v := fun _ ↦ v) (s := fun _ ↦ s)
    (.of_forall fun _ ↦ hl) (hγ.and (hc.preimage_mem_nhds hs))
    (hγ'.and (hc'.preimage_mem_nhds (h ▸ hs))) h

/-- **Uniqueness on an interval.** Two solutions on an open preconnected set that agree at one
time agree everywhere on it. -/
theorem IsSolOn.eqOn (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {I : Set ℝ} (hI : IsOpen I)
    (hIc : IsPreconnected I) {γ γ' : ℝ → E} (hγ : IsSolOn v U γ I) (hγ' : IsSolOn v U γ' I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h : γ t₀ = γ' t₀) : EqOn γ γ' I := by
  have hloc : ∀ t ∈ I, γ t = γ' t → γ =ᶠ[𝓝 t] γ' := fun t ht h ↦
    eventuallyEq_of_contDiffAt (hv _ (hγ t ht).2)
      (Filter.eventually_of_mem (hI.mem_nhds ht) fun s hs ↦ (hγ s hs).1)
      (Filter.eventually_of_mem (hI.mem_nhds ht) fun s hs ↦ (hγ' s hs).1) h
  have hsub : I ⊆ {t | γ =ᶠ[𝓝 t] γ'} := by
    refine hIc.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds
      ⟨t₀, ht₀, hloc t₀ ht₀ h⟩ ?_
    rintro t ⟨htc, ht⟩
    refine hloc t ht ?_
    have hfreq : ∃ᶠ s in 𝓝 t, γ s = γ' s :=
      (mem_closure_iff_frequently.1 htc).mono fun s hs ↦ hs.self_of_nhds
    exact tendsto_nhds_unique_of_frequently_eq (hγ t ht).1.continuousAt
      (hγ' t ht).1.continuousAt hfreq
  exact fun t ht ↦ (hsub ht).self_of_nhds

variable [CompleteSpace E]

/-- **Local existence that stays in `U`**, uniformly for initial values near `x₀`. -/
theorem exists_local_mem (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U) (hv : ContDiffAt ℝ 1 v x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∀ t₀ : ℝ, ∃ α : ℝ → E, α t₀ = x ∧
      IsSolOn v U α (Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  obtain ⟨b, hb, hbU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have har : (r : ℝ) ≤ a := by
    have h := (hpl 0).mul_max_le
    have : (0 : ℝ) ≤ L * max (0 + ε - 0) (0 - (0 - ε)) :=
      mul_nonneg L.2 (le_max_of_le_left (by linarith))
    simp only at h
    linarith
  set a' : ℝ≥0 := min a (b / 2).toNNReal with ha'
  have hb2 : ((b / 2).toNNReal : ℝ) = b / 2 := Real.coe_toNNReal _ (by positivity)
  have ha'0 : (0 : ℝ) < a' := by
    rw [ha', NNReal.coe_min, hb2]
    exact lt_min (by exact_mod_cast hr.trans_le (by exact_mod_cast har)) (by positivity)
  set r' : ℝ≥0 := a' / 2 with hr'
  have hr'0 : (0 : ℝ) < r' := by rw [hr']; push_cast; positivity
  obtain ⟨ε', hε', hpl'⟩ := IsPicardLindelof.exists_shrink_radius hε (hpl 0) (min_le_left _ _)
    (a' := a') (r' := r') (by rw [hr']; exact NNReal.half_lt_self (by exact_mod_cast ha'0.ne'))
  refine ⟨r', hr'0, ε', hε', fun x hx t₀ ↦ ?_⟩
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl' hx
  have hderiv : ∀ t ∈ Icc (0 - ε') (0 + ε'),
      HasDerivWithinAt α.compProj (v (α.compProj t)) (Icc (0 - ε') (0 + ε')) t := by
    intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc (⟨0, by simp [hε'.le]⟩ : Icc (0 - ε') (0 + ε')).2
      hpl'.continuousOn_uncurry α.continuous_compProj.continuousOn
      (fun _ _ ↦ α.compProj_mem_closedBall hpl'.mul_max_le) x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  have h0 : α.compProj 0 = x := by
    have := ODE.FunSpace.next_apply₀ hpl' hx α
    rw [hα] at this
    rw [ODE.FunSpace.compProj_of_mem (by simp [hε'.le])]
    exact this
  refine ⟨fun t ↦ α.compProj (t - t₀), by simpa using h0, fun t ht ↦ ⟨?_, ?_⟩⟩
  · have ht' : t - t₀ ∈ Ioo (0 - ε') (0 + ε') := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hderiv _ (Ioo_subset_Icc_self ht')).hasDerivAt
      (Icc_mem_nhds ht'.1 ht'.2)).comp_sub_const t t₀
  · apply hbU
    have h1 := α.compProj_mem_closedBall hpl'.mul_max_le (t := t - t₀)
    rw [mem_ball]
    rw [mem_closedBall] at h1
    calc dist (α.compProj (t - t₀)) x₀ ≤ a' := h1
      _ ≤ b / 2 := by rw [ha', NNReal.coe_min, hb2]; exact min_le_right _ _
      _ < b := half_lt_self hb

/-- **Uniform local existence on a compact set.** -/
theorem exists_local_mem_of_isCompact (hU : IsOpen U) (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x)
    {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ ε > (0 : ℝ), ∀ x ∈ C, ∀ t₀ : ℝ, ∃ α : ℝ → E, α t₀ = x ∧
      IsSolOn v U α (Ioo (t₀ - ε) (t₀ + ε)) := by
  classical
  choose! r hr ε hε h using fun x (hx : x ∈ U) ↦ exists_local_mem hU hx (hv x hx)
  obtain ⟨s, hsC, hcover⟩ := hC.elim_nhds_subcover (fun x ↦ closedBall x (r x))
    fun x hx ↦ closedBall_mem_nhds x (hr x (hCU hx))
  set ε₀ := (insert 1 (s.image ε)).min' (Finset.insert_nonempty _ _)
  have hε₀ : 0 < ε₀ := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hε x (hCU (hsC x hx))
  refine ⟨ε₀, hε₀, fun x hx t₀ ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  obtain ⟨α, hα0, hα⟩ := h y (hCU (hsC y hy)) x hxy t₀
  have hle : ε₀ ≤ ε y :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  exact ⟨α, hα0, hα.mono (Ioo_subset_Ioo (by linarith) (by linarith))⟩

/-- `γ` on `J` is a **maximal solution** with initial time `t₀`: `J` is an open interval that
contains `t₀`, `γ` solves the equation on `J`, and every solution on an open interval through
`t₀` with the same initial value lives inside `J`. -/
structure IsMaximalSolution (v : E → E) (U : Set E) (t₀ : ℝ) (γ : ℝ → E) (J : Set ℝ) :
    Prop where
  isOpen : IsOpen J
  ordConnected : J.OrdConnected
  mem : t₀ ∈ J
  isSolOn : IsSolOn v U γ J
  maximal : ∀ ⦃I : Set ℝ⦄ ⦃γ' : ℝ → E⦄, IsOpen I → I.OrdConnected → t₀ ∈ I →
    IsSolOn v U γ' I → γ' t₀ = γ t₀ → I ⊆ J

/-- **Existence of a maximal solution.** -/
theorem exists_isMaximalSolution (hU : IsOpen U) (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {x₀ : E}
    (hx₀ : x₀ ∈ U) (t₀ : ℝ) : ∃ γ J, γ t₀ = x₀ ∧ IsMaximalSolution v U t₀ γ J := by
  classical
  let P : (ℝ → E) → Set ℝ → Prop := fun γ I ↦
    IsOpen I ∧ I.OrdConnected ∧ t₀ ∈ I ∧ γ t₀ = x₀ ∧ IsSolOn v U γ I
  have hagree : ∀ {γ I γ' I'}, P γ I → P γ' I' → EqOn γ γ' (I ∩ I') := fun h h' ↦
    IsSolOn.eqOn hv (h.1.inter h'.1) (h.2.1.inter h'.2.1).isPreconnected
      (h.2.2.2.2.mono inter_subset_left) (h'.2.2.2.2.mono inter_subset_right)
      ⟨h.2.2.1, h'.2.2.1⟩ (h.2.2.2.1.trans h'.2.2.2.1.symm)
  let J : Set ℝ := {t | ∃ γ I, P γ I ∧ t ∈ I}
  let γm : ℝ → E := fun t ↦ if h : t ∈ J then h.choose t else x₀
  have hγm : ∀ {γ I}, P γ I → EqOn γm γ I := by
    intro γ I h t ht
    have hJ : t ∈ J := ⟨γ, I, h, ht⟩
    simp only [γm, hJ, ↓reduceDIte]
    obtain ⟨I', hP', ht'⟩ := hJ.choose_spec
    exact hagree hP' h ⟨ht', ht⟩
  obtain ⟨r, hr, ε, hε, hloc⟩ := exists_local_mem hU hx₀ (hv x₀ hx₀)
  obtain ⟨α, hα0, hα⟩ := hloc x₀ (mem_closedBall_self hr.le) t₀
  have hP0 : P α (Ioo (t₀ - ε) (t₀ + ε)) :=
    ⟨isOpen_Ioo, ordConnected_Ioo, ⟨by linarith, by linarith⟩, hα0, hα⟩
  have hm0 : γm t₀ = x₀ := (hγm hP0 hP0.2.2.1).trans hα0
  refine ⟨γm, J, hm0, ⟨?_, ⟨?_⟩, ⟨α, _, hP0, hP0.2.2.1⟩, ?_, ?_⟩⟩
  · rw [isOpen_iff_mem_nhds]
    rintro t ⟨γ, I, h, ht⟩
    exact Filter.mem_of_superset (h.1.mem_nhds ht) fun s hs ↦ ⟨γ, I, h, hs⟩
  · rintro x ⟨γ, I, h, hx⟩ y ⟨γ', I', h', hy⟩ z hz
    rcases le_total z t₀ with hz0 | hz0
    · exact ⟨γ, I, h, h.2.1.out hx h.2.2.1 ⟨hz.1, hz0⟩⟩
    · exact ⟨γ', I', h', h'.2.1.out h'.2.2.1 hy ⟨hz0, hz.2⟩⟩
  · rintro t ⟨γ, I, h, ht⟩
    have heq : γm =ᶠ[𝓝 t] γ := Filter.eventually_of_mem (h.1.mem_nhds ht) (hγm h)
    have := h.2.2.2.2 t ht
    rw [← hγm h ht] at this
    exact ⟨this.1.congr_of_eventuallyEq heq, this.2⟩
  · intro I γ' hI hIc ht₀ hsol h0 t ht
    exact ⟨γ', I, ⟨hI, hIc, ht₀, h0.trans hm0, hsol⟩, ht⟩

variable {t₀ : ℝ} {γ : ℝ → E} {J : Set ℝ}

omit [CompleteSpace E] in
/-- **Uniqueness.** Every solution on an open interval through `t₀`, with the initial value of
the maximal solution, lives inside the maximal interval and agrees with the maximal solution
there. -/
theorem IsMaximalSolution.eqOn (hm : IsMaximalSolution v U t₀ γ J)
    (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {I : Set ℝ} {γ' : ℝ → E} (hI : IsOpen I)
    (hIc : I.OrdConnected) (ht₀ : t₀ ∈ I) (hsol : IsSolOn v U γ' I) (h0 : γ' t₀ = γ t₀) :
    I ⊆ J ∧ EqOn γ' γ I := by
  have hIJ := hm.maximal hI hIc ht₀ hsol h0
  exact ⟨hIJ, IsSolOn.eqOn hv hI hIc.isPreconnected hsol (hm.isSolOn.mono hIJ) ht₀ h0⟩

omit [CompleteSpace E] in
/-- Two maximal solutions with the same initial value are the same. -/
theorem IsMaximalSolution.unique (hm : IsMaximalSolution v U t₀ γ J)
    (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {γ' : ℝ → E} {J' : Set ℝ}
    (hm' : IsMaximalSolution v U t₀ γ' J') (h0 : γ' t₀ = γ t₀) : J' = J ∧ EqOn γ' γ J := by
  have h1 := hm.eqOn hv hm'.isOpen hm'.ordConnected hm'.mem hm'.isSolOn h0
  have h2 := hm'.maximal hm.isOpen hm.ordConnected hm.mem hm.isSolOn h0.symm
  have hJ : J' = J := h1.1.antisymm h2
  exact ⟨hJ, hJ ▸ h1.2⟩

omit [CompleteSpace E] in
/-- **Extension step.** A solution on `(t₁ - ε, t₁ + ε)` that agrees with the maximal solution
at a time `t₁` of the maximal interval lives inside the maximal interval. -/
theorem IsMaximalSolution.Ioo_subset (hm : IsMaximalSolution v U t₀ γ J)
    (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {t₁ ε : ℝ} (ht₁ : t₁ ∈ J) {α : ℝ → E}
    (hα0 : α t₁ = γ t₁) (hα : IsSolOn v U α (Ioo (t₁ - ε) (t₁ + ε))) :
    Ioo (t₁ - ε) (t₁ + ε) ⊆ J := by
  classical
  rcases le_or_gt ε 0 with hε | hε
  · intro t ht
    exact absurd (ht.1.trans ht.2) (by linarith)
  set I := Ioo (t₁ - ε) (t₁ + ε)
  have ht₁I : t₁ ∈ I := ⟨by linarith, by linarith⟩
  have hagree : EqOn γ α (J ∩ I) :=
    IsSolOn.eqOn hv (hm.isOpen.inter isOpen_Ioo)
      (hm.ordConnected.inter ordConnected_Ioo).isPreconnected (hm.isSolOn.mono inter_subset_left)
      (hα.mono inter_subset_right) ⟨ht₁, ht₁I⟩ hα0.symm
  set γ' : ℝ → E := fun t ↦ if t ∈ J then γ t else α t
  have h1 : EqOn γ' γ J := fun t ht ↦ by simp only [γ', ht, ↓reduceIte]
  have h2 : EqOn γ' α I := fun t ht ↦ by
    by_cases hJ : t ∈ J
    · simp only [γ', hJ, ↓reduceIte]
      exact hagree ⟨hJ, ht⟩
    · simp only [γ', hJ, ↓reduceIte]
  have hsol : IsSolOn v U γ' (J ∪ I) := by
    rintro t (ht | ht)
    · have h := hm.isSolOn t ht
      rw [← h1 ht] at h
      exact ⟨h.1.congr_of_eventuallyEq (Filter.eventually_of_mem (hm.isOpen.mem_nhds ht) h1), h.2⟩
    · have h := hα t ht
      rw [← h2 ht] at h
      exact ⟨h.1.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) h2),
        h.2⟩
  have hord : (J ∪ I).OrdConnected := isPreconnected_iff_ordConnected.1
    (IsPreconnected.union t₁ ht₁ ht₁I hm.ordConnected.isPreconnected isPreconnected_Ioo)
  exact subset_union_right.trans
    (hm.maximal (hm.isOpen.union isOpen_Ioo) hord (Or.inl hm.mem) hsol (h1 hm.mem))

/-- **Escape at a finite right end.** If the maximal interval is bounded above by `b`, the
solution leaves every compact subset of `U` before `b`, and does not come back. -/
theorem IsMaximalSolution.eventually_not_mem_right (hm : IsMaximalSolution v U t₀ γ J)
    (hU : IsOpen U) (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {C : Set E} (hC : IsCompact C)
    (hCU : C ⊆ U) {b : ℝ} (hb : ∀ t ∈ J, t < b) : ∃ τ < b, ∀ t ∈ J, τ < t → γ t ∉ C := by
  obtain ⟨ε, hε, hloc⟩ := exists_local_mem_of_isCompact hU hv hC hCU
  refine ⟨b - ε, by linarith, fun t ht hτ htC ↦ ?_⟩
  obtain ⟨α, hα0, hα⟩ := hloc _ htC t
  have := hm.Ioo_subset hv ht hα0 hα
    (show b ∈ Ioo (t - ε) (t + ε) from ⟨by linarith [hb t ht], by linarith⟩)
  exact lt_irrefl b (hb b this)

/-- **Escape at a finite left end.** -/
theorem IsMaximalSolution.eventually_not_mem_left (hm : IsMaximalSolution v U t₀ γ J)
    (hU : IsOpen U) (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {C : Set E} (hC : IsCompact C)
    (hCU : C ⊆ U) {b : ℝ} (hb : ∀ t ∈ J, b < t) : ∃ τ > b, ∀ t ∈ J, t < τ → γ t ∉ C := by
  obtain ⟨ε, hε, hloc⟩ := exists_local_mem_of_isCompact hU hv hC hCU
  refine ⟨b + ε, by linarith, fun t ht hτ htC ↦ ?_⟩
  obtain ⟨α, hα0, hα⟩ := hloc _ htC t
  have := hm.Ioo_subset hv ht hα0 hα
    (show b ∈ Ioo (t - ε) (t + ε) from ⟨by linarith, by linarith [hb t ht]⟩)
  exact lt_irrefl b (hb b this)

/-- Points of an open set are strictly below its supremum. -/
lemma lt_csSup_of_isOpen {J : Set ℝ} (hJ : IsOpen J) (hb : BddAbove J) {t : ℝ} (ht : t ∈ J) :
    t < sSup J := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJ t ht
  have : t + ε / 2 ∈ J := hball (by rw [mem_ball, Real.dist_eq]; rw [abs_of_pos] <;> linarith)
  linarith [le_csSup hb this]

/-- **Global existence.** A maximal solution that stays in a compact subset of `U` exists for
all time. -/
theorem IsMaximalSolution.eq_univ_of_mem (hm : IsMaximalSolution v U t₀ γ J) (hU : IsOpen U)
    (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U)
    (hγC : ∀ t ∈ J, γ t ∈ C) : J = univ := by
  have hne : J.Nonempty := ⟨t₀, hm.mem⟩
  have habove : ¬ BddAbove J := fun hb ↦ by
    obtain ⟨τ, hτ, h⟩ := hm.eventually_not_mem_right hU hv hC hCU
      fun t ht ↦ lt_csSup_of_isOpen hm.isOpen hb ht
    have : sSup J ≤ τ := csSup_le hne fun t ht ↦ not_lt.1 fun h' ↦ h t ht h' (hγC t ht)
    linarith
  have hbelow : ¬ BddBelow J := fun hb ↦ by
    have hlt : ∀ t ∈ J, sInf J < t := fun t ht ↦ by
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hm.isOpen t ht
      have : t - ε / 2 ∈ J :=
        hball (by rw [mem_ball, Real.dist_eq, abs_of_neg] <;> linarith)
      linarith [csInf_le hb this]
    obtain ⟨τ, hτ, h⟩ := hm.eventually_not_mem_left hU hv hC hCU hlt
    have : τ ≤ sInf J := le_csInf hne fun t ht ↦ not_lt.1 fun h' ↦ h t ht h' (hγC t ht)
    linarith
  refine eq_univ_of_forall fun t ↦ ?_
  obtain ⟨y, hy, hty⟩ := not_bddAbove_iff.1 habove t
  obtain ⟨x, hx, hxt⟩ := not_bddBelow_iff.1 hbelow t
  exact hm.ordConnected.out hx hy ⟨hxt.le, hty.le⟩

end Autonomous

/-! ### The second-order equation `ä = F'(a)/2` -/

section SecondOrderMax

variable {F : ℝ → ℝ} {D : Set ℝ} {t₀ : ℝ} {γ : ℝ → ℝ × ℝ} {J : Set ℝ}

lemma contDiffAt_secondOrderField_of_mem (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a) :
    ∀ y ∈ (Prod.fst ⁻¹' D : Set (ℝ × ℝ)), ContDiffAt ℝ 1 (secondOrderField F) y :=
  fun y hy ↦ contDiffAt_secondOrderField (hF _ hy) y.2

/-- **Maximal solutions of `ä = F'(a)/2`** exist for every `a(t₀) ∈ D` and every `ȧ(t₀)`.
The state is `(a, ȧ)`. -/
theorem exists_isMaximalSolution₂ (hD : IsOpen D) (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a)
    {a₀ : ℝ} (ha₀ : a₀ ∈ D) (v₀ t₀ : ℝ) : ∃ γ J, γ t₀ = (a₀, v₀) ∧
      IsMaximalSolution (secondOrderField F) (Prod.fst ⁻¹' D) t₀ γ J :=
  exists_isMaximalSolution (hD.preimage continuous_fst)
    (contDiffAt_secondOrderField_of_mem hF) (show (a₀, v₀).1 ∈ D from ha₀) t₀

/-- The two components of a solution: `ȧ = v` and `v̇ = F'(a)/2`. -/
lemma IsSolOn.hasDerivAt₂ {I : Set ℝ} (h : IsSolOn (secondOrderField F) (Prod.fst ⁻¹' D) γ I)
    {t : ℝ} (ht : t ∈ I) : HasDerivAt (fun s ↦ (γ s).1) (γ t).2 t
      ∧ HasDerivAt (fun s ↦ (γ s).2) (deriv F (γ t).1 / 2) t :=
  ⟨(hasFDerivAt_fst.comp_hasDerivAt t (h t ht).1 :),
    (hasFDerivAt_snd.comp_hasDerivAt t (h t ht).1 :)⟩

/-- **Conservation of `ȧ² - F(a)`.** If `ȧ² = F(a)` at the initial time, it holds on the whole
maximal interval. -/
theorem IsMaximalSolution.energy₂
    (hm : IsMaximalSolution (secondOrderField F) (Prod.fst ⁻¹' D) t₀ γ J)
    (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a) (h0 : (γ t₀).2 ^ 2 = F (γ t₀).1) :
    ∀ t ∈ J, (γ t).2 ^ 2 = F (γ t).1 := by
  have hE : ∀ t ∈ J, HasDerivAt (fun s ↦ (γ s).2 ^ 2 - F (γ s).1) 0 t := fun t ht ↦ by
    obtain ⟨h1, h2⟩ := hm.isSolOn.hasDerivAt₂ ht
    have h3 : HasDerivAt F (deriv F (γ t).1) (γ t).1 :=
      ((hF _ (hm.isSolOn t ht).2).differentiableAt (by norm_num)).hasDerivAt
    have h4 := (h2.fun_pow 2).fun_sub (h3.comp t h1)
    simp only [Function.comp_def] at h4
    convert h4 using 1
    ring
  intro t ht
  have := hm.isOpen.is_const_of_deriv_eq_zero hm.ordConnected.isPreconnected
    (fun s hs ↦ (hE s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hE s hs).deriv) ht hm.mem
  simp only [h0, sub_self] at this
  linarith

/-- On a solution of `ȧ² = F(a)`, a compact set of `a` values in `D` gives a compact set of
states in `D × ℝ`. -/
lemma exists_compact_states (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a) {C : Set ℝ} (hC : IsCompact C)
    (hCD : C ⊆ D) : ∃ C' : Set (ℝ × ℝ), IsCompact C' ∧ C' ⊆ Prod.fst ⁻¹' D ∧
      ∀ y : ℝ × ℝ, y.1 ∈ C → y.2 ^ 2 = F y.1 → y ∈ C' := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (f := F)
    fun a ha ↦ (hF a (hCD ha)).continuousAt.continuousWithinAt
  refine ⟨C ×ˢ Icc (-(|M| + 1)) (|M| + 1), hC.prod isCompact_Icc, fun y hy ↦ hCD hy.1,
    fun y hy hE ↦ ⟨hy, ?_⟩⟩
  have hb := hM _ hy
  rw [Real.norm_eq_abs] at hb
  have hy2 : y.2 ^ 2 ≤ |M| := by
    rw [hE]
    exact (le_abs_self _).trans (hb.trans (le_abs_self M))
  rw [mem_Icc, ← abs_le]
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (|M| + 1) ^ 2 < |y.2| ^ 2 := by gcongr
  rw [sq_abs] at h1
  nlinarith [abs_nonneg M]

/-- **At a finite right end, `a` leaves every compact subset of `D`.** This holds for a maximal
solution of `ä = F'(a)/2` with `ȧ² = F(a)`. -/
theorem IsMaximalSolution.eventually_fst_not_mem_right
    (hm : IsMaximalSolution (secondOrderField F) (Prod.fst ⁻¹' D) t₀ γ J) (hD : IsOpen D)
    (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a) (h0 : (γ t₀).2 ^ 2 = F (γ t₀).1) {C : Set ℝ}
    (hC : IsCompact C) (hCD : C ⊆ D) {b : ℝ} (hb : ∀ t ∈ J, t < b) :
    ∃ τ < b, ∀ t ∈ J, τ < t → (γ t).1 ∉ C := by
  obtain ⟨C', hC', hC'D, hmem⟩ := exists_compact_states hF hC hCD
  obtain ⟨τ, hτ, h⟩ := hm.eventually_not_mem_right (hD.preimage continuous_fst)
    (contDiffAt_secondOrderField_of_mem hF) hC' hC'D hb
  exact ⟨τ, hτ, fun t ht htτ hmem' ↦ h t ht htτ (hmem _ hmem' (hm.energy₂ hF h0 t ht))⟩

/-- **At a finite left end, `a` leaves every compact subset of `D`.** -/
theorem IsMaximalSolution.eventually_fst_not_mem_left
    (hm : IsMaximalSolution (secondOrderField F) (Prod.fst ⁻¹' D) t₀ γ J) (hD : IsOpen D)
    (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a) (h0 : (γ t₀).2 ^ 2 = F (γ t₀).1) {C : Set ℝ}
    (hC : IsCompact C) (hCD : C ⊆ D) {b : ℝ} (hb : ∀ t ∈ J, b < t) :
    ∃ τ > b, ∀ t ∈ J, t < τ → (γ t).1 ∉ C := by
  obtain ⟨C', hC', hC'D, hmem⟩ := exists_compact_states hF hC hCD
  obtain ⟨τ, hτ, h⟩ := hm.eventually_not_mem_left (hD.preimage continuous_fst)
    (contDiffAt_secondOrderField_of_mem hF) hC' hC'D hb
  exact ⟨τ, hτ, fun t ht htτ hmem' ↦ h t ht htτ (hmem _ hmem' (hm.energy₂ hF h0 t ht))⟩

/-- **Global existence for `ä = F'(a)/2`.** A maximal solution with `ȧ² = F(a)` whose `a`
stays in a compact subset of `D` exists for all time. -/
theorem IsMaximalSolution.eq_univ_of_fst_mem
    (hm : IsMaximalSolution (secondOrderField F) (Prod.fst ⁻¹' D) t₀ γ J) (hD : IsOpen D)
    (hF : ∀ a ∈ D, ContDiffAt ℝ 2 F a) (h0 : (γ t₀).2 ^ 2 = F (γ t₀).1) {C : Set ℝ}
    (hC : IsCompact C) (hCD : C ⊆ D) (hγC : ∀ t ∈ J, (γ t).1 ∈ C) : J = univ := by
  obtain ⟨C', hC', hC'D, hmem⟩ := exists_compact_states hF hC hCD
  exact hm.eq_univ_of_mem (hD.preimage continuous_fst) (contDiffAt_secondOrderField_of_mem hF)
    hC' hC'D fun t ht ↦ hmem _ (hγC t ht) (hm.energy₂ hF h0 t ht)

end SecondOrderMax

/-! ### Brane cosmology -/

/-- The scale factors where `F` is smooth: `a > 0`, away from the pressure singularity. -/
def braneDomain (c : Couplings) (K H0 rh w ρ₀ : ℝ) : Set ℝ :=
  {a | 0 < a ∧ 0 < realityArg c K H0 rh w ρ₀ a}

theorem isOpen_braneDomain (c : Couplings) (K H0 rh w ρ₀ : ℝ) :
    IsOpen (braneDomain c K H0 rh w ρ₀) := by
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨ha, hR⟩
  have hc : ContinuousAt (realityArg c K H0 rh w ρ₀) a :=
    (contDiffAt_realityArg (n := 0) ha.ne').continuousAt
  filter_upwards [Ioi_mem_nhds ha, hc.eventually (Ioi_mem_nhds hR)] with x h1 h2
  exact ⟨h1, h2⟩

theorem contDiffAt_friedmannF_of_mem {c : Couplings} {K H0 rh w ρ₀ sgn : ℝ} :
    ∀ a ∈ braneDomain c K H0 rh w ρ₀, ContDiffAt ℝ 2 (friedmannF c K H0 rh w ρ₀ sgn) a :=
  fun _ ha ↦ contDiffAt_friedmannF ha.1.ne' ha.2.ne'

/-- **Maximal histories.** For `P = wρ` on the branch `sgn`, every `a₀ > 0` away from the
pressure singularity, with `ȧ₀² = F(a₀)`, has a maximal solution of `ä = F'(a)/2`. It obeys
`ȧ² = F(a)` on its whole interval. At a finite end of the interval, `a` leaves every compact
subset of the domain: the history ends at `a → 0`, at the pressure singularity, or at
`a → ∞`. -/
theorem exists_maximal_history {c : Couplings} {K H0 rh w ρ₀ sgn a₀ v₀ : ℝ}
    (ha₀ : a₀ ∈ braneDomain c K H0 rh w ρ₀) (hv₀ : v₀ ^ 2 = friedmannF c K H0 rh w ρ₀ sgn a₀)
    (t₀ : ℝ) : ∃ γ J, γ t₀ = (a₀, v₀) ∧
      IsMaximalSolution (secondOrderField (friedmannF c K H0 rh w ρ₀ sgn))
        (Prod.fst ⁻¹' braneDomain c K H0 rh w ρ₀) t₀ γ J ∧
      (∀ t ∈ J, (γ t).2 ^ 2 = friedmannF c K H0 rh w ρ₀ sgn (γ t).1) ∧
      ∀ C, IsCompact C → C ⊆ braneDomain c K H0 rh w ρ₀ →
        (∀ b, (∀ t ∈ J, t < b) → ∃ τ < b, ∀ t ∈ J, τ < t → (γ t).1 ∉ C) ∧
        (∀ b, (∀ t ∈ J, b < t) → ∃ τ > b, ∀ t ∈ J, t < τ → (γ t).1 ∉ C) := by
  obtain ⟨γ, J, h0, hm⟩ := exists_isMaximalSolution₂ (isOpen_braneDomain c K H0 rh w ρ₀)
    contDiffAt_friedmannF_of_mem ha₀ v₀ t₀
  have hE : (γ t₀).2 ^ 2 = friedmannF c K H0 rh w ρ₀ sgn (γ t₀).1 := by rw [h0]; exact hv₀
  exact ⟨γ, J, h0, hm, hm.energy₂ contDiffAt_friedmannF_of_mem hE, fun C hC hCD ↦
    ⟨fun _ hb ↦ hm.eventually_fst_not_mem_right (isOpen_braneDomain c K H0 rh w ρ₀)
      contDiffAt_friedmannF_of_mem hE hC hCD hb,
     fun _ hb ↦ hm.eventually_fst_not_mem_left (isOpen_braneDomain c K H0 rh w ρ₀)
      contDiffAt_friedmannF_of_mem hE hC hCD hb⟩⟩

namespace BraneCosmology

variable (M : BraneCosmology)

/-- The domain of `M.F w sgn`. -/
noncomputable def domain (w : ℝ) : Set ℝ :=
  braneDomain M.c M.K M.H0 M.rh w (M.ρ 0 * M.a 0 ^ (3 * (1 + w)))

/-- **A brane cosmology is the maximal solution of its data, and that solution is global.**
Take a solution (`IsSolution`) with `P = wρ` on the branch `sgn = ±1` that never reaches the
pressure singularity. The maximal solution of `ä = F'(a)/2` with the data `(a(t₀), ȧ(t₀))`
exists for all time and is `(a, ȧ)`. -/
theorem maximal_eq (hsol : M.IsSolution) {w sgn : ℝ} (hsg : sgn ^ 2 = 1)
    (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t))
    (hns : ∀ t, M.ρt t ≠ M.c.rhoS) {t₀ : ℝ} {γ : ℝ → ℝ × ℝ} {J : Set ℝ}
    (hm : IsMaximalSolution (secondOrderField (M.F w sgn)) (Prod.fst ⁻¹' M.domain w) t₀ γ J)
    (h0 : γ t₀ = (M.a t₀, deriv M.a t₀)) : J = univ ∧ ∀ t, γ t = (M.a t, deriv M.a t) := by
  have hsolM : IsSolOn (secondOrderField (M.F w sgn)) (Prod.fst ⁻¹' M.domain w)
      (fun t ↦ (M.a t, deriv M.a t)) univ := fun t _ ↦
    ⟨hasDerivAt_curve (M.a_diff t).hasDerivAt (M.accel_eq_deriv hsol hsg hw hbr (hns t)),
      M.a_pos t, M.realityArg_pos hw hbr (hns t)⟩
  obtain ⟨h1, h2⟩ := hm.eqOn (contDiffAt_secondOrderField_of_mem contDiffAt_friedmannF_of_mem)
    isOpen_univ ordConnected_univ (mem_univ _) hsolM h0.symm
  exact ⟨eq_univ_of_univ_subset h1, fun t ↦ (h2 (mem_univ t)).symm⟩

/-- **The data of a global history.** If the maximal solution with the data of a time `t₀` has
a finite end, no brane-cosmology solution as in `maximal_eq` has that data at `t₀`. -/
theorem not_bdd_of_maximal (hsol : M.IsSolution) {w sgn : ℝ} (hsg : sgn ^ 2 = 1)
    (hw : ∀ t, M.P t = w * M.ρ t)
    (hbr : ∀ t, M.ρt t = rhoTilde sgn M.c.rhoS (M.rhoBH t) (M.ρ t))
    (hns : ∀ t, M.ρt t ≠ M.c.rhoS) {t₀ : ℝ} {γ : ℝ → ℝ × ℝ} {J : Set ℝ}
    (hm : IsMaximalSolution (secondOrderField (M.F w sgn)) (Prod.fst ⁻¹' M.domain w) t₀ γ J)
    (h0 : γ t₀ = (M.a t₀, deriv M.a t₀)) : ¬ BddAbove J ∧ ¬ BddBelow J := by
  rw [(M.maximal_eq hsol hsg hw hbr hns hm h0).1]
  exact ⟨not_bddAbove_univ, not_bddBelow_univ⟩

end BraneCosmology

end WhiteHole
