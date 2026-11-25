module

public import HolographicUniverse.Acceleration

@[expose] public section

/-!
# Orientation of the brane normal (ROADMAP M3.1, M3.3)

The paper concludes that the normal orientation is `ε = -1`, by comparing its Eq. (27) with
Eq. (16). Checked against the TeX source (arXiv:1309.1487v2), that comparison is circular:

* The spatial junction condition (Eqs. (10) and (24)) reads `ε X = -(8π G_b/3) ρ̃`, where
  `X = √(H² + 𝒦/a² - 𝒦² r_h²/a⁴) ≥ 0` is also the denominator of Eq. (25). So
  `X = -ε (8π G_b/3) ρ̃`.
* The timelike junction condition equates Eq. (25), `K_ττ = -ε (𝒦² r_h²/a⁴ + ä/a)/X`, with the
  `ττ` component of Eq. (10), `K_ττ = -8π G_b (P̃ + 2ρ̃/3)`.
* Substituting `X = -ε (8π G_b/3) ρ̃` cancels `ε` completely, and gives Eq. (16) for **both**
  orientations: `pressure_of_timelike_junction`.
* Substituting `X = +(8π G_b/3) ρ̃` instead, which is the spatial condition with `ε = -1`, gives
  Eq. (27) exactly: `eq27_of_dropped_sign`. So Eq. (27) already assumes `ε = -1`. Comparing
  it with Eq. (16) cannot then determine `ε`.

What does fix `ε` is the sign of `ρ̃`, through the spatial junction condition:

* `orientation_iff`: where `X > 0`, `ε = -1 ↔ ρ̃ > 0` and `ε = +1 ↔ ρ̃ < 0`.
* `orientation_plus_branch`: the self-accelerating branch `ρ̃_+` needs `ε = -1`.
* `orientation_minus_branch`: the normal branch `ρ̃_-` needs `ε = -1` when `ρ_BH > ρ`, and
  `ε = +1` when `ρ_BH < ρ`.
* `minkowski_normal_branch`: in particular, with no black hole (`ρ_BH = 0`, standard DGP) and
  `ρ > 0`, the normal branch has `ε = +1`. The paper's `ε = -1` would exclude the standard DGP
  normal branch, which confirms that `ε = -1` is too strong.
* `rhoTilde_eq_zero_inside`: `ρ̃ = 0` only when the brane is on or inside the horizon
  (`f(a) ≤ 0`). Outside the horizon `ρ̃ ≠ 0`, so the orientation is well defined.
* `BraneCosmology.eps_mul_ρt_nonpos`, `BraneCosmology.ρt_sign_const`: `ε` is a constant of the
  structure, so `ρ̃` never changes sign along a history. A normal-branch history with
  `ρ_BH > ρ` at one time and `ρ_BH < ρ` at another, both with `X > 0`, is not a
  `BraneCosmology`: `BraneCosmology.normal_branch_no_crossing`.

This resolves the normal-branch "sign tension" (README issue 3): the region `ρ_BH < ρ` of the
normal branch is consistent, with `ε = +1`. It also settles M3.3: Eq. (27) is wrong as printed
for `ε = +1`, and the induced pressure is Eq. (16) for either orientation.

The geometric reading of `ε = +1` (which side of the brane the `Z₂`-reflected bulk keeps) is
not formalized here.
-/

namespace WhiteHole

open Real

section Timelike

/-- The algebra behind `pressure_of_timelike_junction`, with `s = ρ̃_s`, `g = 8π G_b/3`, and
`8π G_N/3 = 2 s g²` already substituted. -/
private lemma pressure_alg {s g ε X b ρ P ρt Pt : ℝ} (hg : g ≠ 0) (hε : ε ^ 2 = 1)
    (hJ : ε * X = -g * ρt) (hX : X ≠ 0)
    (hTT : -ε * (2 * s * g ^ 2 * b - s * g ^ 2 * (ρ + ρt + 3 * (P + Pt))) / X
      = -(3 * g) * (Pt + 2 * ρt / 3))
    (hq : ρt ^ 2 - 2 * s * ρt + 2 * s * (b - ρ) = 0) (hsing : ρt ≠ s) :
    Pt = pressureTilde s ρt (3 * P - ρ) := by
  have hX' : X = -ε * g * ρt := by linear_combination ε * hJ - X * hε
  rw [div_eq_iff hX, hX'] at hTT
  set E := 2 * s * b - s * (ρ + ρt + 3 * (P + Pt)) + 3 * ρt * Pt + 2 * ρt ^ 2 with hEdef
  have hE : g ^ 2 * E = 0 := by linear_combination (-ε) * hTT - (g ^ 2 * E) * hε
  have hE0 : E = 0 := (mul_eq_zero.1 hE).resolve_left (pow_ne_zero 2 hg)
  have hne : s - ρt ≠ 0 := sub_ne_zero.2 (Ne.symm hsing)
  unfold pressureTilde
  rw [eq_div_iff (mul_ne_zero three_ne_zero hne)]
  linear_combination hq - hE0

/-- The algebra behind `eq27_of_dropped_sign`. -/
private lemma eq27_alg {s g ε X b ρ P ρt Pt : ℝ} (hg : g ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hX : X = g * ρt) (hX0 : X ≠ 0)
    (hTT : -ε * (2 * s * g ^ 2 * b - s * g ^ 2 * (ρ + ρt + 3 * (P + Pt))) / X
      = -(3 * g) * (Pt + 2 * ρt / 3))
    (hq : ρt ^ 2 - 2 * s * ρt + 2 * s * (b - ρ) = 0) (hden : s + ε * ρt ≠ 0) :
    Pt = pressureTildeEps ε s ρt (3 * P - ρ) := by
  rw [div_eq_iff hX0, hX] at hTT
  set F := ε * (2 * s * b - s * (ρ + ρt + 3 * (P + Pt))) - 3 * ρt * Pt - 2 * ρt ^ 2 with hFdef
  have hF : g ^ 2 * F = 0 := by linear_combination -hTT
  have hF0 : F = 0 := (mul_eq_zero.1 hF).resolve_left (pow_ne_zero 2 hg)
  unfold pressureTildeEps
  rw [eq_div_iff (mul_ne_zero three_ne_zero hden)]
  rcases hε with rfl | rfl
  · linear_combination hq - hF0
  · linear_combination hF0 + hq

variable (c : Couplings) {ε X B A ρ P ρt Pt b : ℝ}

/-- `8π G_N/3 = 2 ρ̃_s (8π G_b/3)²`: the identity behind `r_c² = 3/(16π G_N ρ̃_s)`. -/
private lemma kappa_eq : 8 * π * c.GN / 3 = 2 * c.rhoS * (8 * π * c.Gb / 3) ^ 2 := by
  have := c.Gb_pos
  unfold Couplings.rhoS
  field_simp
  ring

/-- Rewrite `B + A` in the form used by the algebra lemmas. -/
private lemma BA_eq (hB : B = 8 * π * c.GN / 3 * b)
    (hAcc : A = -(4 * π * c.GN / 3) * (ρ + ρt + 3 * (P + Pt))) :
    B + A = 2 * c.rhoS * (8 * π * c.Gb / 3) ^ 2 * b
      - c.rhoS * (8 * π * c.Gb / 3) ^ 2 * (ρ + ρt + 3 * (P + Pt)) := by
  have h := kappa_eq c
  rw [hB, hAcc]
  linear_combination (b - (ρ + ρt + 3 * (P + Pt)) / 2) * h

/-- **Eq. (16) from the timelike junction condition, for either orientation.** Inputs:
the spatial junction condition `ε X = -(8π G_b/3) ρ̃` with `X ≠ 0`; the timelike junction
condition, Eq. (25) equal to the `ττ` component of Eq. (10); `B = 𝒦² r_h²/a⁴ = (8π G_N/3) ρ_BH`;
the acceleration equation for `A = ä/a`; and the quadratic of Eq. (26). Then `P̃` is Eq. (16).
`ε` does not appear in the conclusion. -/
theorem pressure_of_timelike_junction (hε : ε ^ 2 = 1)
    (hJ : ε * X = -(8 * π * c.Gb / 3) * ρt) (hX : X ≠ 0)
    (hTT : -ε * (B + A) / X = -(8 * π * c.Gb) * (Pt + 2 * ρt / 3))
    (hB : B = 8 * π * c.GN / 3 * b) (hAcc : A = -(4 * π * c.GN / 3) * (ρ + ρt + 3 * (P + Pt)))
    (hq : IsInduced c.rhoS b ρ ρt) (hsing : ρt ≠ c.rhoS) :
    Pt = pressureTilde c.rhoS ρt (3 * P - ρ) := by
  have hg : 8 * π * c.Gb / 3 ≠ 0 := by have := c.Gb_pos; positivity
  rw [BA_eq c hB hAcc] at hTT
  refine pressure_alg hg hε hJ hX ?_ hq hsing
  rw [hTT]; ring

/-- **Where Eq. (27) comes from.** With the substitution `X = +(8π G_b/3) ρ̃` (the spatial
junction condition with `ε = -1`) in the timelike junction condition, the pressure is
Eq. (27) for the given `ε`. So Eq. (27) mixes the two orientations whenever `ε = +1`. -/
theorem eq27_of_dropped_sign (hε : ε = 1 ∨ ε = -1)
    (hX : X = 8 * π * c.Gb / 3 * ρt) (hX0 : X ≠ 0)
    (hTT : -ε * (B + A) / X = -(8 * π * c.Gb) * (Pt + 2 * ρt / 3))
    (hB : B = 8 * π * c.GN / 3 * b) (hAcc : A = -(4 * π * c.GN / 3) * (ρ + ρt + 3 * (P + Pt)))
    (hq : IsInduced c.rhoS b ρ ρt) (hden : c.rhoS + ε * ρt ≠ 0) :
    Pt = pressureTildeEps ε c.rhoS ρt (3 * P - ρ) := by
  have hg : 8 * π * c.Gb / 3 ≠ 0 := by have := c.Gb_pos; positivity
  rw [BA_eq c hB hAcc] at hTT
  refine eq27_alg hg hε hX hX0 ?_ hq hden
  rw [hTT]; ring

end Timelike

section Sign

variable {Gb ε Y ρt : ℝ}

/-- `ε = ±1` from `ε² = 1`. -/
lemma eps_cases (hε : ε ^ 2 = 1) : ε = 1 ∨ ε = -1 := by
  have : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith

/-- **The sign of `ρ̃` fixes the orientation.** Where the square-root argument `Y` of
Eqs. (24)–(25) is positive, `ε = -1 ↔ ρ̃ > 0` and `ε = +1 ↔ ρ̃ < 0`. -/
theorem orientation_iff (hGb : 0 < Gb) (hε : ε ^ 2 = 1)
    (hJ : ε * √Y = -(8 * π * Gb / 3) * ρt) (hY : 0 < Y) :
    (ε = -1 ↔ 0 < ρt) ∧ (ε = 1 ↔ ρt < 0) := by
  have hg : 0 < 8 * π * Gb / 3 := by positivity
  have hs := sqrt_pos.2 hY
  rcases eps_cases hε with rfl | rfl
  · have : ρt < 0 := by nlinarith
    exact ⟨⟨by norm_num, fun h ↦ by linarith⟩, ⟨fun _ ↦ this, fun _ ↦ rfl⟩⟩
  · have : 0 < ρt := by nlinarith
    exact ⟨⟨fun _ ↦ this, fun _ ↦ rfl⟩, ⟨by norm_num, fun h ↦ by linarith⟩⟩

/-- `ε ρ̃ ≤ 0` always: the spatial junction condition with `X ≥ 0`. -/
theorem eps_mul_rhoTilde_nonpos (hGb : 0 < Gb) (hε : ε ^ 2 = 1)
    (hJ : ε * √Y = -(8 * π * Gb / 3) * ρt) : ε * ρt ≤ 0 := by
  have hg : 0 < 8 * π * Gb / 3 := by positivity
  have h : √Y = -(8 * π * Gb / 3) * (ε * ρt) := by linear_combination ε * hJ - √Y * hε
  nlinarith [sqrt_nonneg Y]

end Sign

section Branches

variable {Gb ε Y s b ρ : ℝ}

/-- The normal branch is positive exactly when the black hole dominates matter. -/
theorem rhoTilde_minus_pos_iff (hs : 0 < s) : 0 < rhoTilde (-1) s b ρ ↔ ρ < b := by
  have key : 0 < rhoTilde (-1) s b ρ ↔ √(1 - 2 * (b - ρ) / s) < 1 := by
    unfold rhoTilde
    constructor <;> intro h <;> nlinarith
  rw [key, sqrt_lt' one_pos, one_pow, sub_lt_self_iff, div_pos_iff_of_pos_right hs]
  constructor <;> intro h <;> linarith

/-- **Self-accelerating branch: `ε = -1`.** `ρ̃_+ ≥ ρ̃_s > 0`. -/
theorem orientation_plus_branch (hGb : 0 < Gb) (hs : 0 < s) (hε : ε ^ 2 = 1)
    (hJ : ε * √Y = -(8 * π * Gb / 3) * rhoTilde 1 s b ρ) (hY : 0 < Y) : ε = -1 := by
  refine ((orientation_iff hGb hε hJ hY).1).2 ?_
  unfold rhoTilde
  have := sqrt_nonneg (1 - 2 * (b - ρ) / s)
  nlinarith

/-- **Normal branch: the orientation follows `ρ_BH - ρ`.** `ε = -1` exactly when
`ρ_BH > ρ`, and `ε = +1` exactly when `ρ_BH < ρ`. -/
theorem orientation_minus_branch (hGb : 0 < Gb) (hs : 0 < s) (hε : ε ^ 2 = 1)
    (hJ : ε * √Y = -(8 * π * Gb / 3) * rhoTilde (-1) s b ρ) (hY : 0 < Y) :
    (ε = -1 ↔ ρ < b) ∧ (ε = 1 ↔ b < ρ) := by
  obtain ⟨h1, h2⟩ := orientation_iff hGb hε hJ hY
  exact ⟨h1.trans (rhoTilde_minus_pos_iff hs), h2.trans (rhoTilde_minus_neg_iff hs)⟩

/-- **Standard DGP normal branch: `ε = +1`.** With no bulk black hole (`ρ_BH = 0`) and
`ρ > 0`, the normal branch needs `ε = +1`, not the paper's `ε = -1`. -/
theorem minkowski_normal_branch (hGb : 0 < Gb) (hs : 0 < s) (hε : ε ^ 2 = 1) (hρ : 0 < ρ)
    (hJ : ε * √Y = -(8 * π * Gb / 3) * rhoTilde (-1) s 0 ρ) (hY : 0 < Y) : ε = 1 :=
  (orientation_minus_branch hGb hs hε hJ hY).2.2 hρ

end Branches

/-- **`ρ̃ = 0` only on or inside the horizon.** If the induced density vanishes, the spatial
junction condition forces `X = 0`, so `f(a) = -ȧ²/𝒦 ≤ 0`. -/
theorem rhoTilde_eq_zero_inside {Gb ε K rh a H : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hJ : ε * √(H ^ 2 + K / a ^ 2 - K ^ 2 * rh ^ 2 / a ^ 4) = -(8 * π * Gb / 3) * 0)
    (hε : ε ^ 2 = 1) (hArg : 0 ≤ H ^ 2 + K / a ^ 2 - K ^ 2 * rh ^ 2 / a ^ 4) :
    blacken rh (braneRadius K a) ≤ 0 := by
  have hε0 : ε ≠ 0 := by rintro rfl; norm_num at hε
  have hY : H ^ 2 + K / a ^ 2 - K ^ 2 * rh ^ 2 / a ^ 4 = 0 := by
    rw [mul_zero, mul_eq_zero, sqrt_eq_zero hArg] at hJ
    exact hJ.resolve_left hε0
  have hf := curv_mul_blacken (rh := rh) hK ha.ne'
  have hKa : 0 < K / a ^ 2 := by positivity
  by_contra h
  push Not at h
  have : 0 < K / a ^ 2 * blacken rh (braneRadius K a) := mul_pos hKa h
  nlinarith [sq_nonneg H]

namespace BraneCosmology

variable (M : BraneCosmology)

/-- `ε ρ̃ ≤ 0` at every time. -/
theorem eps_mul_ρt_nonpos (t : ℝ) : M.ε * M.ρt t ≤ 0 :=
  eps_mul_rhoTilde_nonpos M.c.Gb_pos M.ε_sq (M.junction t)

/-- **`ρ̃` keeps one sign along the history.** The orientation `ε` is a constant of the
structure, so `ρ̃` cannot be positive at one time and negative at another. -/
theorem ρt_sign_const (t₁ t₂ : ℝ) : ¬ (0 < M.ρt t₁ ∧ M.ρt t₂ < 0) := by
  rintro ⟨h1, h2⟩
  have e1 := M.eps_mul_ρt_nonpos t₁
  have e2 := M.eps_mul_ρt_nonpos t₂
  rcases eps_cases M.ε_sq with h | h <;> rw [h] at e1 e2 <;> linarith

/-- **No crossing of `ρ_BH = ρ` on the normal branch.** If `ρ̃ = ρ̃_-` at two times, one with
`ρ_BH > ρ` and one with `ρ_BH < ρ`, the history is not a `BraneCosmology`. A normal-branch
history has to keep one sign of `ρ_BH - ρ` (where `ρ̃ ≠ 0`). -/
theorem normal_branch_no_crossing {t₁ t₂ : ℝ}
    (h₁ : M.ρt t₁ = rhoTilde (-1) M.c.rhoS (M.rhoBH t₁) (M.ρ t₁)) (hlt₁ : M.ρ t₁ < M.rhoBH t₁)
    (h₂ : M.ρt t₂ = rhoTilde (-1) M.c.rhoS (M.rhoBH t₂) (M.ρ t₂)) (hlt₂ : M.rhoBH t₂ < M.ρ t₂) :
    False := by
  have hs := M.c.rhoS_pos
  refine M.ρt_sign_const t₁ t₂ ⟨?_, ?_⟩
  · rw [h₁]; exact (rhoTilde_minus_pos_iff hs).2 hlt₁
  · rw [h₂]; exact (rhoTilde_minus_neg_iff hs).2 hlt₂

end BraneCosmology

end WhiteHole
