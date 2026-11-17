import HolographicUniverse.BlueTilt

/-!
# Cascading gravity cannot make the spectrum red (P2; fourth falsification theorem)

Sec. 5 of the paper suggests that a red tilt could come from a bulk graviton propagator that
gets stronger in the infrared, as in cascading gravity (the 5D bulk as a 4-brane in 6D).
`phenomenology/p2_cascade/README.md` works this out at linear order. Relative to 5D general
relativity, the 4D power of the paper's `ζ = -Φ₄` gets multiplied by

  `G(K) = (K/(K + m))² · exp(-L σ(K))`.

* `(K/(K + m))²` (`cascadeFactor`) is the 6D propagator `1/(K² + mK)`, with `m ∼ M₆⁴/M₅³`.
* `exp(-L σ(K))` is the change of tensor structure, from `λ = 1/3` (massless 5D graviton) to
  `λ = 1/4` (with the brane-bending scalar). `σ` runs from 1 (unscreened, small `K`) to 0
  (Vainshtein-screened, large `K`). `L = 2 ln(r_GR/r_cascade)` compares the spatial-potential
  coefficients `c² + λ(1 − 4c²)` (`spatialCoeff`).

Both factors are nondecreasing in `K`. This file proves that this is enough.

* `spectralIndex_mul`: `n_s(P·G) − 1 = (n_s(P) − 1) + (n_s(G) − 1)`.
* `one_le_spectralIndex_comp`: a positive nondecreasing factor `G(k/s)` has `n_s ≥ 1`.
* `spectralIndex_thermal_mul_gt_one`: `C·M(k/s)·G(k/s′)` has `n_s > 1` at every `k > 0`.
* `ObsData.not_fits_thermal_mul`: **fourth falsification theorem.** No such spectrum fits a
  release with `n_s < 1`. This holds for any positive, differentiable `G` that is nondecreasing
  on `(0, ∞)`, so for any modification of the bulk propagator that weakens gravity in the
  infrared.
* `spatialCoeff_le_of_le`, `spatialCoeff_quarter_le_third`, `newtonCoeff_third_le_quarter`: a
  healthy scalar coupled to the trace lowers `λ`. That lowers the spatial potential (`ζ`) and
  raises the Newtonian one, for every `0 ≤ c² ≤ 1/4`. The two coincide for radiation
  (`spatialCoeff_radiation`). So `L ≥ 0` (`cascadeL_nonneg`).
* `ObsData.not_fits_cascade`: the instance `G = cascadeFactor · exp(-L σ)`, for every `m ≥ 0`,
  every `L ≥ 0` and every antitone screening profile `σ`.

**What is assumed** (as named hypotheses or definitions, not axioms): the linear form of `G`
above, which is a physics input from the P2 note; and the paper's spectrum form `C·M(k/s)`,
which the earlier files already use.
-/

namespace WhiteHole

open Real Set Filter Topology

/-! ### Spectral index of a product -/

/-- **Product rule.** `n_s(P·G) − 1 = (n_s(P) − 1) + (n_s(G) − 1)`: tilts add. -/
theorem spectralIndex_mul {P G : ℝ → ℝ} {k : ℝ} (hP : DifferentiableAt ℝ P k)
    (hG : DifferentiableAt ℝ G k) (hP0 : P k ≠ 0) (hG0 : G k ≠ 0) :
    spectralIndex (fun k ↦ P k * G k) k = spectralIndex P k + spectralIndex G k - 1 := by
  have hd : HasDerivAt (fun k ↦ P k * G k) (deriv P k * G k + P k * deriv G k) k :=
    hP.hasDerivAt.mul hG.hasDerivAt
  rw [spectralIndex, spectralIndex, spectralIndex, hd.deriv]
  field_simp
  ring

/-- A function that is monotone on `(0, ∞)` has `deriv ≥ 0` there. -/
theorem deriv_nonneg_of_monotoneOn {G : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hG : MonotoneOn G (Ioi 0)) : 0 ≤ deriv G x := by
  rw [← derivWithin_of_mem_nhds (Ioi_mem_nhds hx)]
  exact hG.derivWithin_nonneg

/-- A positive factor `G(k/s)`, nondecreasing in `k`, has `n_s ≥ 1`. -/
theorem one_le_spectralIndex_comp {G : ℝ → ℝ} {s k : ℝ} (hs : 0 < s) (hk : 0 < k)
    (hG : MonotoneOn G (Ioi 0)) (hGd : DifferentiableAt ℝ G (k / s)) (hG0 : 0 < G (k / s)) :
    1 ≤ spectralIndex (fun k ↦ G (k / s)) k := by
  have h := spectralIndex_comp (C := 1) one_ne_zero hs.ne' hGd hG0.ne'
  simp only [one_mul] at h
  rw [h]
  have hκ : 0 < k / s := div_pos hk hs
  have := div_nonneg (mul_nonneg hκ.le (deriv_nonneg_of_monotoneOn hκ hG)) hG0.le
  linarith

/-- **`M7.3` survives any nondecreasing factor.** `C·M(k/s)·G(k/s′)` has `n_s > 1` at every
`k > 0`, if `G` is positive and nondecreasing on `(0, ∞)`. -/
theorem spectralIndex_thermal_mul_gt_one {C s s' k : ℝ} {G : ℝ → ℝ} (hC : C ≠ 0) (hs : 0 < s)
    (hs' : 0 < s') (hk : 0 < k) (hG : MonotoneOn G (Ioi 0))
    (hGd : DifferentiableAt ℝ G (k / s')) (hG0 : 0 < G (k / s')) :
    1 < spectralIndex (fun k ↦ C * mRay (k / s) * G (k / s')) k := by
  have hκ : 0 < k / s := div_pos hk hs
  have hs1 : DifferentiableAt ℝ (fun k : ℝ ↦ k / s) k := differentiableAt_id.div_const s
  have hs2 : DifferentiableAt ℝ (fun k : ℝ ↦ k / s') k := differentiableAt_id.div_const s'
  have hm : DifferentiableAt ℝ mRay (k / s) := (hasDerivAt_mRay _).differentiableAt
  have hm1 := hm.comp k hs1
  have hg1 := hGd.comp k hs2
  have hPd : DifferentiableAt ℝ (fun k ↦ C * mRay (k / s)) k := hm1.const_mul C
  have hGd' : DifferentiableAt ℝ (fun k ↦ G (k / s')) k := hg1
  rw [spectralIndex_mul hPd hGd' (mul_ne_zero hC (mRay_pos hκ.le).ne') hG0.ne']
  linarith [spectralIndex_thermal_gt_one hC hs hk, one_le_spectralIndex_comp hs' hk hG hGd hG0]

/-- **Fourth falsification theorem.** For a release with `n_s < 1`, no spectrum
`C·M(k/s)·G(k/s′)` fits it, for any positive, differentiable `G` that is nondecreasing on
`(0, ∞)`. A bulk propagator that weakens gravity in the infrared cannot produce the red tilt. -/
theorem ObsData.not_fits_thermal_mul (d : ObsData) (hns : d.ns_hi < 1) {C s s' : ℝ}
    {G : ℝ → ℝ} (hC : C ≠ 0) (hs : 0 < s) (hs' : 0 < s') (hG : MonotoneOn G (Ioi 0))
    (hGd : ∀ K, 0 < K → DifferentiableAt ℝ G K) (hG0 : ∀ K, 0 < K → 0 < G K) :
    ¬ d.Fits (fun k ↦ C * mRay (k / s) * G (k / s')) := by
  rintro ⟨-, -, h⟩
  have hκ : 0 < d.kPivot / s' := div_pos d.kPivot_pos hs'
  linarith [spectralIndex_thermal_mul_gt_one hC hs hs' d.kPivot_pos hG (hGd _ hκ) (hG0 _ hκ)]

/-! ### Tensor structure: the scalar lowers `ζ` -/

/-- Coefficient of `δ_ab` in `h_ab`, per unit `16πG_b δρ/(K² + mK)`, for tensor structure
`δT_μν − λ η_μν δT` and a fluid with `δp = c² δρ` in 4 space dimensions. The paper's `ζ` is
read off this potential (Eq. 47). -/
def spatialCoeff (lam c2 : ℝ) : ℝ := c2 + lam * (1 - 4 * c2)

/-- `h₀₀`, in the same units: the Newtonian potential. -/
def newtonCoeff (lam c2 : ℝ) : ℝ := 1 - lam * (1 - 4 * c2)

/-- A healthy scalar coupled to the trace lowers `λ`. For `ρ ≥ 4p` (`c² ≤ 1/4`), that lowers the
spatial potential. -/
theorem spatialCoeff_le_of_le {lam lam' c2 : ℝ} (hl : lam' ≤ lam) (hc : c2 ≤ 1 / 4) :
    spatialCoeff lam' c2 ≤ spatialCoeff lam c2 := by
  unfold spatialCoeff
  nlinarith

/-- ... and raises the Newtonian potential. -/
theorem newtonCoeff_le_of_le {lam lam' c2 : ℝ} (hl : lam' ≤ lam) (hc : c2 ≤ 1 / 4) :
    newtonCoeff lam c2 ≤ newtonCoeff lam' c2 := by
  unfold newtonCoeff
  nlinarith

/-- Massive (`λ = 1/4`) against massless (`λ = 1/3`): `ζ` is never boosted. -/
theorem spatialCoeff_quarter_le_third {c2 : ℝ} (hc : c2 ≤ 1 / 4) :
    spatialCoeff (1 / 4) c2 ≤ spatialCoeff (1 / 3) c2 :=
  spatialCoeff_le_of_le (by norm_num) hc

/-- The Newtonian potential is boosted (by `9/8` for dust). This is the boost Sec. 5 refers
to. -/
theorem newtonCoeff_third_le_quarter {c2 : ℝ} (hc : c2 ≤ 1 / 4) :
    newtonCoeff (1 / 3) c2 ≤ newtonCoeff (1 / 4) c2 :=
  newtonCoeff_le_of_le (by norm_num) hc

/-- For the paper's radiation atmosphere (`c² = 1/4`, traceless) nothing changes. -/
theorem spatialCoeff_radiation (lam : ℝ) : spatialCoeff lam (1 / 4) = 1 / 4 := by
  unfold spatialCoeff
  ring

/-- The dust values: `ζ` drops to `3/4`, the Newtonian potential rises by `9/8`. -/
theorem coeff_dust :
    spatialCoeff (1 / 4) 0 / spatialCoeff (1 / 3) 0 = 3 / 4 ∧
      newtonCoeff (1 / 4) 0 / newtonCoeff (1 / 3) 0 = 9 / 8 := by
  unfold spatialCoeff newtonCoeff
  norm_num

/-- `L = 2 ln(r_GR / r_cascade) ≥ 0` for `0 ≤ c² ≤ 1/4`: the unscreened tensor structure
multiplies the power of `ζ` by `exp(-L) ≤ 1`. -/
theorem cascadeL_nonneg {c2 : ℝ} (hc : c2 ≤ 1 / 4) :
    0 ≤ 2 * log (spatialCoeff (1 / 3) c2 / spatialCoeff (1 / 4) c2) := by
  have hpos : 0 < spatialCoeff (1 / 4) c2 := by unfold spatialCoeff; linarith
  have := (one_le_div hpos).2 (spatialCoeff_quarter_le_third hc)
  have := log_nonneg this
  linarith

/-! ### The cascade instance -/

/-- The 6D propagator factor `(K/(K + m))²`: `1/(K² + mK)` relative to `1/K²`. -/
noncomputable def cascadeFactor (m K : ℝ) : ℝ := (K / (K + m)) ^ 2

theorem cascadeFactor_monotoneOn {m : ℝ} (hm : 0 ≤ m) :
    MonotoneOn (cascadeFactor m) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  unfold cascadeFactor
  apply pow_le_pow_left₀ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem cascadeFactor_pos {m K : ℝ} (hm : 0 ≤ m) (hK : 0 < K) : 0 < cascadeFactor m K := by
  unfold cascadeFactor
  positivity

theorem differentiableAt_cascadeFactor {m K : ℝ} (hm : 0 ≤ m) (hK : 0 < K) :
    DifferentiableAt ℝ (cascadeFactor m) K := by
  have : K + m ≠ 0 := by positivity
  unfold cascadeFactor
  fun_prop (disch := assumption)

/-- The full linear cascade factor `G(K) = (K/(K + m))² · exp(-L σ(K))`. -/
noncomputable def cascadeG (m L : ℝ) (σ : ℝ → ℝ) (K : ℝ) : ℝ :=
  cascadeFactor m K * exp (-L * σ K)

/-- `G` is nondecreasing: the propagator factor is, and with `L ≥ 0` and `σ` antitone
(screening grows with `K`) so is `exp(-L σ)`. -/
theorem cascadeG_monotoneOn {m L : ℝ} {σ : ℝ → ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hσ : AntitoneOn σ (Ioi 0)) : MonotoneOn (cascadeG m L σ) (Ioi 0) := by
  intro a ha b hb hab
  unfold cascadeG
  have he : exp (-L * σ a) ≤ exp (-L * σ b) :=
    exp_le_exp.2 (by nlinarith [hσ ha hb hab])
  exact mul_le_mul (cascadeFactor_monotoneOn hm ha hb hab) he (exp_pos _).le
    (cascadeFactor_pos hm hb).le

/-- **Fourth falsification theorem, cascade instance.** For a release with `n_s < 1`, the
linear cascading spectrum `C·M(k/s)·G(k/s′)` does not fit, for any `m ≥ 0` (any `M₆`), any
`L ≥ 0` (any `c² ≤ 1/4`, by `cascadeL_nonneg`), and any differentiable screening profile
`σ` that decreases with `K`. -/
theorem ObsData.not_fits_cascade (d : ObsData) (hns : d.ns_hi < 1) {C s s' m L : ℝ}
    {σ : ℝ → ℝ} (hC : C ≠ 0) (hs : 0 < s) (hs' : 0 < s') (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hσ : AntitoneOn σ (Ioi 0)) (hσd : ∀ K, 0 < K → DifferentiableAt ℝ σ K) :
    ¬ d.Fits (fun k ↦ C * mRay (k / s) * cascadeG m L σ (k / s')) :=
  d.not_fits_thermal_mul hns hC hs hs' (cascadeG_monotoneOn hm hL hσ)
    (fun K hK ↦ (differentiableAt_cascadeFactor hm hK).mul
      ((((hσd K hK).const_mul (-L))).exp))
    (fun _ hK ↦ mul_pos (cascadeFactor_pos hm hK) (exp_pos _))

end WhiteHole
