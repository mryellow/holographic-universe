import HolographicUniverse.Asymptotics
import HolographicUniverse.ObsData

/-!
# The bulk black hole is not dark radiation (TESTABILITY P3)

In a Randall–Sundrum brane world, a bulk black hole enters the brane's Friedmann equation as
"dark radiation": a term `∝ a⁻⁴` with the full weight of `ρ_BH`, constrained by BBN and the CMB
through `ΔN_eff`. P3 asked whether the same happens here. It does not. The induced gravity on
the brane suppresses every effect of the bulk, by a factor `1/(r_c H_std)`, where
`H_std² = (8πG_N/3)ρ` is the standard Hubble rate of the brane matter.

**Both branches, no bound on `ρ_BH`.** Any root of the quadratic (26) satisfies
`|ρ̃| ≤ 2ρ̃_s + √(2ρ̃_s|ρ - ρ_BH|)` (`abs_le_of_isInduced`). With `ρ_BH ≥ 0` (always true,
`BraneCosmology.rhoBH_nonneg`) and the reality bound (30), this gives
`|ρ̃| ≤ (y + (3/2)y²)ρ` with `y = 1/(r_c H_std)` (`abs_le_rel_of_isInduced`). So
`|H² + 𝒦/a² - H_std²| ≤ (y + (3/2)y²)·H_std²` (`BraneCosmology.abs_frw_sub_le`). This
strengthens `normal_branch_frw_rc_of_le`: no branch and no bound `ρ_BH ≤ ρ` are assumed.

**Any bulk.** For a bulk density of either sign (Schwarzschild–AdS, Reissner–Nordström, any
`f`), `|ρ̃| ≤ (y² + y√(1 + |ρ_bulk|/ρ))ρ` (`abs_le_rel_of_isInduced_any`), so
`|H² + 𝒦/a² - H_std²| ≤ (y² + y√(1 + |ρ_bulk|/ρ))·H_std²` (`BulkCosmology.abs_frw_sub_le`).

**The black-hole part.** On the normal branch, write `ρ̃ = ρ̃_-(0, ρ) + Δ`, where `Δ` is the
part due to the black hole. Then `0 ≤ Δ ≤ ρ_BH/(r_c H_std)` (`rhoTilde_minus_sub_le`,
`BraneCosmology.darkRadiation_le`). The black hole does act like dark radiation (`Δ ≥ 0`), but
with weight `1/(r_c H_std)` instead of `1`.

**`ΔN_eff`.** Measure the deviation of `H² + 𝒦/a²` from `H_std²` in units of one neutrino
species, `(8πG_N/3)ρ_ν` (`BraneCosmology.deltaNeff`). If `r_c ≥ R/H₀`, `H_std ≥ N H₀` and
`ρ ≤ g ρ_ν`, then `|ΔN_eff| ≤ g(z + (3/2)z²)` with `z = 1/(RN)` (`abs_deltaNeff_le`). With the
paper's `r_c ≳ 3/H₀`:

* **BBN** (`abs_deltaNeff_bbn`): `H ≥ 10¹⁴ H₀` for `T ≳ 0.07 MeV`, and `ρ ≤ 8ρ_ν` in the
  radiation era (`ρ/ρ_ν` is `43/7` before e± annihilation and about `7.45` after it). So
  `|ΔN_eff| ≤ 3×10⁻¹⁴`.
* **Up to recombination** (`abs_deltaNeff_recombination`): `H ≥ 10⁴ H₀` for `z ≳ 1090`, and
  `ρ ≤ 32ρ_ν` (matter included). So `|ΔN_eff| ≤ 1.1×10⁻³`.

Both are far below the Planck 2018 error (`σ(N_eff) ≈ 0.17`) and the error forecast for the next
CMB experiments (`≈ 0.03`). The numbers for `H/H₀` and `ρ/ρ_ν` are hypotheses, not proved: they
are standard ΛCDM values (Planck 2018 parameters, `g_* = 10.75` and `3.36`).
-/

namespace WhiteHole

open Real

/-! ### Any root of the quadratic -/

/-- **Both branches deviate little.** Any root `x = ρ̃` of the quadratic (26), on either branch,
satisfies `|ρ̃| ≤ 2ρ̃_s + √(2ρ̃_s|ρ - ρ_BH|)`. -/
theorem abs_le_of_isInduced {s b ρ x : ℝ} (hs : 0 < s) (h : IsInduced s b ρ x) :
    |x| ≤ 2 * s + √(2 * s * |ρ - b|) := by
  unfold IsInduced at h
  set u := √(2 * s * |ρ - b|)
  have hu : 0 ≤ u := sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * s * |ρ - b| := sq_sqrt (by positivity)
  have hle : 2 * s * (ρ - b) ≤ u ^ 2 := by
    rw [hu2]; exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have hsq : (x - s) ^ 2 ≤ (s + u) ^ 2 := by nlinarith
  have h2 := abs_le_of_sq_le_sq' hsq (by positivity)
  rw [abs_le]
  constructor <;> linarith [h2.1, h2.2]

/-- **In units of `ρ`.** Let `ρ_BH ≥ 0`, and let `y ≥ 0` with `y²ρ = 2ρ̃_s`. Then any root of the
quadratic (26) satisfies `|ρ̃| ≤ (y + (3/2)y²)ρ`. In a brane cosmology `y = 1/(r_c H_std)`. No
branch and no bound `ρ_BH ≤ ρ` are assumed: reality (30) caps `ρ_BH - ρ` at `ρ̃_s/2`. -/
theorem abs_le_rel_of_isInduced {s b ρ x y : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hb : 0 ≤ b)
    (hy : 0 ≤ y) (hyρ : y ^ 2 * ρ = 2 * s) (h : IsInduced s b ρ x) :
    |x| ≤ (y + 3 / 2 * y ^ 2) * ρ := by
  have hreal := reality hs h
  have hy2 : (y * ρ) ^ 2 = 2 * s * ρ := by rw [← hyρ]; ring
  have hsq : 2 * s * |ρ - b| ≤ (y * ρ + s) ^ 2 := by
    have hyρ0 : 0 ≤ y * ρ := mul_nonneg hy hρ.le
    rcases le_total b ρ with hbρ | hbρ
    · rw [abs_of_nonneg (by linarith)]
      nlinarith
    · rw [abs_of_nonpos (by linarith)]
      nlinarith
  have hu : √(2 * s * |ρ - b|) ≤ y * ρ + s :=
    (sqrt_le_sqrt hsq).trans_eq (sqrt_sq (by positivity))
  have := abs_le_of_isInduced hs h
  linear_combination this + hu - (3 / 2 : ℝ) * hyρ

/-- **Any bulk.** For a bulk density `b` of either sign (Schwarzschild–AdS, Reissner–Nordström,
any `f`), with `y ≥ 0` and `y²ρ = 2ρ̃_s`: `|ρ̃| ≤ (y² + y√(1 + |b|/ρ))ρ`. The bulk enters with
weight `y = 1/(r_c H_std)`, under a square root. -/
theorem abs_le_rel_of_isInduced_any {s b ρ x y : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hy : 0 ≤ y)
    (hyρ : y ^ 2 * ρ = 2 * s) (h : IsInduced s b ρ x) :
    |x| ≤ (y ^ 2 + y * √(1 + |b| / ρ)) * ρ := by
  have h1 := abs_le_of_isInduced hs h
  have e : 2 * s * (ρ + |b|) = (y * ρ) ^ 2 * (1 + |b| / ρ) := by
    rw [← hyρ]; field_simp
  have htri : |ρ - b| ≤ ρ + |b| :=
    abs_le.2 ⟨by linarith [le_abs_self b], by linarith [neg_abs_le b]⟩
  have hle : 2 * s * |ρ - b| ≤ (y * ρ) ^ 2 * (1 + |b| / ρ) := by
    rw [← e]; exact mul_le_mul_of_nonneg_left htri (by positivity)
  have hu : √(2 * s * |ρ - b|) ≤ y * ρ * √(1 + |b| / ρ) := by
    calc _ ≤ √((y * ρ) ^ 2 * (1 + |b| / ρ)) := sqrt_le_sqrt hle
      _ = _ := by rw [sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]
  linear_combination h1 + hu - hyρ

/-- `y = 1/(r_c √((8πG_N/3)ρ))` satisfies `y²ρ = 2ρ̃_s`. -/
theorem Couplings.inv_rc_sqrt_sq_mul (c : Couplings) {ρ : ℝ} (hρ : 0 < ρ) :
    (1 / (c.rc * √(8 * π * c.GN / 3 * ρ))) ^ 2 * ρ = 2 * c.rhoS := by
  have hG : 0 < 8 * π * c.GN / 3 := by have := c.GN_pos; positivity
  have hrc := c.rc_pos
  have hg := c.gN_mul_rhoS
  rw [div_pow, mul_pow, sq_sqrt (by positivity)]
  have hs : c.rhoS = 1 / (2 * c.rc ^ 2) / (8 * π * c.GN / 3) := by
    rw [eq_div_iff hG.ne', mul_comm, hg]; ring
  rw [hs]
  field_simp

/-- **Standard FRW for any bulk.** In a `BulkCosmology` with `ρ > 0`, and with
`H_std = √((8πG_N/3)ρ)` and `y = 1/(r_c H_std)`:
`|H² + 𝒦/a² - H_std²| ≤ (y² + y√(1 + |ρ_bulk|/ρ))·H_std²`, on either branch. -/
theorem BulkCosmology.abs_frw_sub_le (M : BulkCosmology) {t : ℝ} (hρ : 0 < M.ρ t) :
    |M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t|
      ≤ ((1 / (M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t))) ^ 2
          + 1 / (M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t)) * √(1 + |M.rhoBulk t| / M.ρ t))
        * (8 * π * M.c.GN / 3 * M.ρ t) := by
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  have hy : 0 ≤ 1 / (M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t)) := by
    have := M.c.rc_pos; positivity
  have hx := abs_le_rel_of_isInduced_any M.c.rhoS_pos hρ hy (M.c.inv_rc_sqrt_sq_mul hρ)
    (M.isInduced t)
  have hF := M.friedmann t
  rw [show M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t
      = 8 * π * M.c.GN / 3 * M.ρt t by unfold BulkCosmology.H; linarith, abs_mul, abs_of_pos hG]
  calc 8 * π * M.c.GN / 3 * |M.ρt t| ≤ 8 * π * M.c.GN / 3 * (_ * M.ρ t) :=
        mul_le_mul_of_nonneg_left hx hG.le
    _ = _ := by ring

/-! ### The black-hole part on the normal branch -/

/-- **The bulk black hole as suppressed dark radiation.** On the normal branch, the part of `ρ̃`
due to the black hole, `Δ = ρ̃_-(ρ_BH, ρ) - ρ̃_-(0, ρ)`, satisfies `0 ≤ Δ ≤ y ρ_BH`, where
`y ≥ 0` and `y²ρ = 2ρ̃_s`. In a brane cosmology `y = 1/(r_c H_std)`. -/
theorem rhoTilde_minus_sub_le {s b ρ y : ℝ} (hs : 0 < s) (hb : 0 ≤ b)
    (hy : 0 ≤ y) (hyρ : y ^ 2 * ρ = 2 * s) (hreal : 2 * (b - ρ) ≤ s) :
    0 ≤ rhoTilde (-1) s b ρ - rhoTilde (-1) s 0 ρ ∧
      rhoTilde (-1) s b ρ - rhoTilde (-1) s 0 ρ ≤ y * b := by
  unfold rhoTilde
  set A := 1 - 2 * (0 - ρ) / s with hA
  set B := 1 - 2 * (b - ρ) / s with hB
  have hB0 : 0 ≤ B := by
    rw [hB, sub_nonneg, div_le_one hs]; exact hreal
  have hBA : B ≤ A := by
    have : 2 * (0 - ρ) / s ≤ 2 * (b - ρ) / s := by gcongr
    rw [hA, hB]; linarith
  have hsA : s * A = s + 2 * ρ := by rw [hA]; field_simp; ring
  have hAB : s * (A - B) = 2 * b := by rw [hA, hB]; field_simp; ring
  set p := √A
  set q := √B
  have hp2 : p ^ 2 = A := sq_sqrt (hB0.trans hBA)
  have hq2 : q ^ 2 = B := sq_sqrt hB0
  have hq : 0 ≤ q := sqrt_nonneg _
  have hp0 : 0 ≤ p := sqrt_nonneg _
  have hqp : q ≤ p := sqrt_le_sqrt hBA
  rw [show s * (1 + -1 * q) - s * (1 + -1 * p) = s * (p - q) by ring]
  refine ⟨mul_nonneg hs.le (by linarith), ?_⟩
  -- `y p ≥ 2`, since `s (y p)² = s y² + 4 s`
  have h1 : s * (y * p) ^ 2 = s * y ^ 2 + 4 * s := by
    rw [mul_pow, hp2]; linear_combination y ^ 2 * hsA + 2 * hyρ
  have h2 : 4 ≤ (y * p) ^ 2 :=
    le_of_mul_le_mul_left (by nlinarith [sq_nonneg y]) hs
  have hyp : 0 ≤ y * p := mul_nonneg hy hp0
  have h3 : 2 ≤ y * p := by nlinarith
  have hp : 0 < p := pos_of_mul_pos_right (by linarith) hy
  have hpq : s * (p - q) * (p + q) = 2 * b := by rw [← hAB, ← hp2, ← hq2]; ring
  refine le_of_mul_le_mul_right ?_ (by linarith : 0 < p + q)
  rw [hpq]
  nlinarith [mul_nonneg (mul_nonneg hy hb) hq, mul_nonneg hb (sub_nonneg.2 h3)]

/-! ### In a brane cosmology -/

namespace BraneCosmology

variable (M : BraneCosmology)

/-- `ρ_BH ≥ 0` at every time: Eq. (28) is a square. -/
theorem rhoBH_nonneg (t : ℝ) : 0 ≤ M.rhoBH t := by
  unfold rhoBH
  rw [WhiteHole.rhoBH_eq M.H0_pos.ne']
  have := M.c.GN_pos
  have := M.a_pos t
  positivity

/-- The standard Hubble rate of the brane matter alone, `H_std = √((8πG_N/3)ρ)`. -/
noncomputable def Hstd (t : ℝ) : ℝ := √(8 * π * M.c.GN / 3 * M.ρ t)

theorem Hstd_sq {t : ℝ} (hρ : 0 ≤ M.ρ t) : M.Hstd t ^ 2 = 8 * π * M.c.GN / 3 * M.ρ t := by
  have := M.c.GN_pos
  exact sq_sqrt (by positivity)

theorem Hstd_pos {t : ℝ} (hρ : 0 < M.ρ t) : 0 < M.Hstd t := by
  have := M.c.GN_pos
  exact sqrt_pos.2 (by positivity)

/-- `y = 1/(r_c H_std)` satisfies `y²ρ = 2ρ̃_s`. -/
theorem inv_rc_Hstd_sq_mul {t : ℝ} (hρ : 0 < M.ρ t) :
    (1 / (M.c.rc * M.Hstd t)) ^ 2 * M.ρ t = 2 * M.c.rhoS :=
  M.c.inv_rc_sqrt_sq_mul hρ

/-- **Standard FRW on both branches, for any `ρ_BH`.** With `ρ > 0` and `y = 1/(r_c H_std)`,
`|H² + 𝒦/a² - H_std²| ≤ (y + (3/2)y²)·H_std²`. Unlike `normal_branch_frw_rc_of_le`, this
assumes no branch and no bound `ρ_BH ≤ ρ`. -/
theorem abs_frw_sub_le {t : ℝ} (hρ : 0 < M.ρ t) :
    |M.H t ^ 2 + M.K / M.a t ^ 2 - M.Hstd t ^ 2|
      ≤ (1 / (M.c.rc * M.Hstd t) + 3 / 2 * (1 / (M.c.rc * M.Hstd t)) ^ 2) * M.Hstd t ^ 2 := by
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  have hy : 0 ≤ 1 / (M.c.rc * M.Hstd t) := by
    have := M.c.rc_pos; have := M.Hstd_pos hρ; positivity
  have hx := abs_le_rel_of_isInduced M.c.rhoS_pos hρ (M.rhoBH_nonneg t) hy
    (M.inv_rc_Hstd_sq_mul hρ) (M.isInduced t)
  have hF := M.friedmann t
  rw [show M.H t ^ 2 + M.K / M.a t ^ 2 - M.Hstd t ^ 2 = 8 * π * M.c.GN / 3 * M.ρt t by
      rw [M.Hstd_sq hρ.le]; unfold H; linarith,
    abs_mul, abs_of_pos hG, M.Hstd_sq hρ.le]
  calc 8 * π * M.c.GN / 3 * |M.ρt t|
      ≤ 8 * π * M.c.GN / 3 * ((1 / (M.c.rc * M.Hstd t)
          + 3 / 2 * (1 / (M.c.rc * M.Hstd t)) ^ 2) * M.ρ t) :=
        mul_le_mul_of_nonneg_left hx hG.le
    _ = _ := by ring

/-- **The black hole's part is positive and suppressed.** On the normal branch, the part of
`ρ̃` due to the bulk black hole, `Δ = ρ̃ - ρ̃_-(0, ρ)`, satisfies
`0 ≤ Δ ≤ ρ_BH/(r_c H_std)`. In Randall–Sundrum the corresponding weight is `1`. -/
theorem darkRadiation_le {t : ℝ} (hρ : 0 < M.ρ t)
    (hbr : M.ρt t = rhoTilde (-1) M.c.rhoS (M.rhoBH t) (M.ρ t)) :
    0 ≤ M.ρt t - rhoTilde (-1) M.c.rhoS 0 (M.ρ t) ∧
      M.ρt t - rhoTilde (-1) M.c.rhoS 0 (M.ρ t) ≤ M.rhoBH t / (M.c.rc * M.Hstd t) := by
  have hy : 0 ≤ 1 / (M.c.rc * M.Hstd t) := by
    have := M.c.rc_pos; have := M.Hstd_pos hρ; positivity
  rw [hbr, ← one_div_mul_eq_div]
  exact rhoTilde_minus_sub_le M.c.rhoS_pos (M.rhoBH_nonneg t) hy (M.inv_rc_Hstd_sq_mul hρ)
    (M.reality t)

/-- The deviation of `H² + 𝒦/a²` from `H_std²` at time `t`, in units of `(8πG_N/3)ρ_ν`, where
`ρ_ν` is the density of one neutrino species. This is the `ΔN_eff` that a fit with standard
FRW would infer from the expansion rate at that time. -/
noncomputable def deltaNeff (t ρν : ℝ) : ℝ :=
  (M.H t ^ 2 + M.K / M.a t ^ 2 - M.Hstd t ^ 2) / (8 * π * M.c.GN / 3 * ρν)

/-- **`ΔN_eff` for any data release and epoch.** If `r_c ≥ R/H₀` (`R = d.rcH0`),
`H_std ≥ N H₀` and `ρ ≤ g ρ_ν`, then `|ΔN_eff| ≤ g(z + (3/2)z²)` with `z = 1/(RN)`. -/
theorem abs_deltaNeff_le (d : ObsData) {t ρν g N : ℝ} (hρ : 0 < M.ρ t) (hν : 0 < ρν)
    (hg : M.ρ t ≤ g * ρν) (hN : 0 < N) (hrc : d.rcH0 / M.H0 ≤ M.c.rc)
    (hH : N * M.H0 ≤ M.Hstd t) :
    |M.deltaNeff t ρν| ≤ g * (1 / (d.rcH0 * N) + 3 / 2 * (1 / (d.rcH0 * N)) ^ 2) := by
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  have hR := d.rcH0_pos
  have hH0 := M.H0_pos
  have hHs := M.Hstd_pos hρ
  -- `r_c H_std ≥ R N`, so `y ≤ z`
  have hRN : d.rcH0 * N ≤ M.c.rc * M.Hstd t := by
    calc d.rcH0 * N = d.rcH0 / M.H0 * (N * M.H0) := by field_simp
      _ ≤ M.c.rc * M.Hstd t := mul_le_mul hrc hH (by positivity) M.c.rc_pos.le
  set y := 1 / (M.c.rc * M.Hstd t)
  set z := 1 / (d.rcH0 * N)
  have hy : 0 ≤ y := by have := M.c.rc_pos; positivity
  have hyz : y ≤ z := one_div_le_one_div_of_le (by positivity) hRN
  have hf : y + 3 / 2 * y ^ 2 ≤ z + 3 / 2 * z ^ 2 := by
    have := pow_le_pow_left₀ hy hyz 2; linarith
  have hfz : 0 ≤ z + 3 / 2 * z ^ 2 := by positivity
  have hdev := M.abs_frw_sub_le hρ
  unfold deltaNeff
  have hden : 0 < 8 * π * M.c.GN / 3 * ρν := mul_pos hG hν
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |M.H t ^ 2 + M.K / M.a t ^ 2 - M.Hstd t ^ 2|
      ≤ (y + 3 / 2 * y ^ 2) * M.Hstd t ^ 2 := hdev
    _ ≤ (z + 3 / 2 * z ^ 2) * (8 * π * M.c.GN / 3 * M.ρ t) := by
        rw [M.Hstd_sq hρ.le]; gcongr
    _ ≤ (z + 3 / 2 * z ^ 2) * (8 * π * M.c.GN / 3 * (g * ρν)) := by gcongr
    _ = _ := by ring

/-- **BBN: the bulk black hole is invisible.** With the paper's `r_c ≥ 3/H₀`, during BBN
(`H_std ≥ 10¹⁴ H₀`, `ρ ≤ 8ρ_ν`): `|ΔN_eff| ≤ 3×10⁻¹⁴`. -/
theorem abs_deltaNeff_bbn {t ρν : ℝ} (hρ : 0 < M.ρ t) (hν : 0 < ρν) (hg : M.ρ t ≤ 8 * ρν)
    (hrc : planck2018.rcH0 / M.H0 ≤ M.c.rc) (hH : 1e14 * M.H0 ≤ M.Hstd t) :
    |M.deltaNeff t ρν| ≤ 3e-14 :=
  (M.abs_deltaNeff_le planck2018 hρ hν hg (by norm_num) hrc hH).trans
    (by norm_num [planck2018])

/-- **Up to recombination.** With `r_c ≥ 3/H₀`, `H_std ≥ 10⁴ H₀` and `ρ ≤ 32ρ_ν` (true for
`z ≳ 1090`): `|ΔN_eff| ≤ 1.1×10⁻³`. -/
theorem abs_deltaNeff_recombination {t ρν : ℝ} (hρ : 0 < M.ρ t) (hν : 0 < ρν)
    (hg : M.ρ t ≤ 32 * ρν) (hrc : planck2018.rcH0 / M.H0 ≤ M.c.rc)
    (hH : 1e4 * M.H0 ≤ M.Hstd t) :
    |M.deltaNeff t ρν| ≤ 1.1e-3 :=
  (M.abs_deltaNeff_le planck2018 hρ hν hg (by norm_num) hrc hH).trans
    (by norm_num [planck2018])

end BraneCosmology

/-! ### Any bulk: BBN bounds a bulk charge only if it is enormous (M5.3) -/

/-- **`ΔN_eff` for any bulk.** If `1/(r_c H_std) ≤ z`, `ρ ≤ g ρ_ν` and `|ρ_bulk| ≤ m ρ`, then the
`ΔN_eff` inferred from `H² + 𝒦/a²` is at most `g(z² + z√(1 + m))`. -/
theorem BulkCosmology.abs_deltaNeff_le (M : BulkCosmology) {t ρν g z m : ℝ} (hρ : 0 < M.ρ t)
    (hν : 0 < ρν) (hg : M.ρ t ≤ g * ρν)
    (hz : 1 / (M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t)) ≤ z) (hm : |M.rhoBulk t| ≤ m * M.ρ t) :
    |(M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t) / (8 * π * M.c.GN / 3 * ρν)|
      ≤ g * (z ^ 2 + z * √(1 + m)) := by
  have hG : 0 < 8 * π * M.c.GN / 3 := by have := M.c.GN_pos; positivity
  set y := 1 / (M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t))
  have hy : 0 ≤ y := by have := M.c.rc_pos; positivity
  have hz0 : 0 ≤ z := hy.trans hz
  have hr : |M.rhoBulk t| / M.ρ t ≤ m := (div_le_iff₀ hρ).2 hm
  have hsq : √(1 + |M.rhoBulk t| / M.ρ t) ≤ √(1 + m) := sqrt_le_sqrt (by linarith)
  have hf : y ^ 2 + y * √(1 + |M.rhoBulk t| / M.ρ t) ≤ z ^ 2 + z * √(1 + m) := by
    have := pow_le_pow_left₀ hy hz 2
    have := mul_le_mul hz hsq (sqrt_nonneg _) hz0
    linarith
  have hfz : 0 ≤ z ^ 2 + z * √(1 + m) := by positivity
  have hdev := M.abs_frw_sub_le hρ
  have hden : 0 < 8 * π * M.c.GN / 3 * ρν := mul_pos hG hν
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t|
      ≤ (y ^ 2 + y * √(1 + |M.rhoBulk t| / M.ρ t)) * (8 * π * M.c.GN / 3 * M.ρ t) := hdev
    _ ≤ (z ^ 2 + z * √(1 + m)) * (8 * π * M.c.GN / 3 * M.ρ t) := by gcongr
    _ ≤ (z ^ 2 + z * √(1 + m)) * (8 * π * M.c.GN / 3 * (g * ρν)) := by gcongr
    _ = _ := by ring

/-- **BBN does not see a bulk charge below `10²⁴ ρ`.** During BBN, with `r_c H_std ≥ 3×10¹⁴`
(`r_c ≥ 3/H₀`, `H_std ≥ 10¹⁴ H₀`) and `ρ ≤ 8ρ_ν`, any bulk density with `|ρ_bulk| ≤ 10²⁴ ρ`
gives `|ΔN_eff| ≤ 0.03`. For Reissner–Nordström, `ρ_bulk = ρ_BH − ρ_Q` (`rhoBulk_blackenRN`), so
BBN constrains the charge only if `ρ_Q` exceeds the brane density by about `10²⁴`. -/
theorem BulkCosmology.abs_deltaNeff_bbn (M : BulkCosmology) {t ρν : ℝ} (hρ : 0 < M.ρ t)
    (hν : 0 < ρν) (hg : M.ρ t ≤ 8 * ρν)
    (hrc : 3e14 ≤ M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t))
    (hm : |M.rhoBulk t| ≤ 1e24 * M.ρ t) :
    |(M.H t ^ 2 + M.K / M.a t ^ 2 - 8 * π * M.c.GN / 3 * M.ρ t) / (8 * π * M.c.GN / 3 * ρν)|
      ≤ 0.03 := by
  have hz : 1 / (M.c.rc * √(8 * π * M.c.GN / 3 * M.ρ t)) ≤ 1 / 3e14 :=
    one_div_le_one_div_of_le (by norm_num) hrc
  refine (M.abs_deltaNeff_le hρ hν hg hz hm).trans ?_
  have hs : √(1 + 1e24 : ℝ) ≤ 1e12 + 1 :=
    calc √(1 + 1e24 : ℝ) ≤ √((1e12 + 1) ^ 2) := sqrt_le_sqrt (by norm_num)
      _ = 1e12 + 1 := sqrt_sq (by norm_num)
  have : (1 / 3e14 : ℝ) * √(1 + 1e24) ≤ 1 / 3e14 * (1e12 + 1) :=
    mul_le_mul_of_nonneg_left hs (by norm_num)
  nlinarith

end WhiteHole
