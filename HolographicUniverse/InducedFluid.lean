module

public import HolographicUniverse.Bulk

@[expose] public section

/-!
# The induced (holographic) fluid (Secs. 2–3)

The Brown–York junction condition (6) with the perfect-fluid ansatz (9) gives Eq. (10),
whose spatial part reads `K^i_j = -(8π G_b/3) ρ̃ δ^i_j`. The embedding computation (24) gives
the same mixed component as `ε √(H² + 𝒦 f/a²)`. Together with the Friedmann equation (11) this
forces `ρ̃` onto a quadratic whose roots are Eq. (26).

The core statement `isInduced_of_bulk` takes any bulk contribution `b` under the root, so it
serves a general blackening factor (`isInduced_of_junction_f`, ROADMAP M5.1).

Note: as printed, Eq. (24) has `ȧ/√𝒦` under the root; consistency with Eq. (21) and with the
denominator of Eq. (25) requires `ȧ²/𝒦`, which is what we use.
-/

namespace WhiteHole

open Real

/-- The quadratic satisfied by the induced density `x = ρ̃` (Eq. (26) before solving),
with `s = ρ̃_s`, `b = ρ_BH`. -/
def IsInduced (s b ρ x : ℝ) : Prop := x ^ 2 - 2 * s * x + 2 * s * (b - ρ) = 0

/-- The two branches of Eq. (26); `sgn = 1` is self-accelerating, `sgn = -1` is normal. -/
noncomputable def rhoTilde (sgn s b ρ : ℝ) : ℝ := s * (1 + sgn * √(1 - 2 * (b - ρ) / s))

/-- **Friedmann + junction ⇒ quadratic, for any bulk.** Write the bulk contribution to the
square root of Eq. (24) as `-(8π G_N/3) b`. From Eq. (11), the spatial junction condition and
`ε² = 1`, the induced density satisfies the quadratic of Eq. (26) with `ρ_BH` replaced by `b`. -/
theorem isInduced_of_bulk (c : Couplings) {K ε a H b ρ ρt : ℝ}
    (hε : ε ^ 2 = 1)
    (hFried : H ^ 2 + K / a ^ 2 = 8 * π * c.GN / 3 * (ρ + ρt))
    (hJunc : ε * √(H ^ 2 + K / a ^ 2 - 8 * π * c.GN / 3 * b) = -(8 * π * c.Gb / 3) * ρt)
    (hArg : 0 ≤ H ^ 2 + K / a ^ 2 - 8 * π * c.GN / 3 * b) :
    IsInduced c.rhoS b ρ ρt := by
  have hN := c.GN_pos; have hb := c.Gb_pos
  have hsq : (8 * π * c.Gb / 3) ^ 2 * ρt ^ 2 = H ^ 2 + K / a ^ 2 - 8 * π * c.GN / 3 * b := by
    have := congrArg (· ^ 2) hJunc
    simp only [mul_pow, sq_sqrt hArg, hε, one_mul, neg_sq] at this
    linarith
  unfold IsInduced Couplings.rhoS
  linear_combination (norm := (field_simp; ring))
    (9 / (64 * π ^ 2 * c.Gb ^ 2)) * hsq + (9 / (64 * π ^ 2 * c.Gb ^ 2)) * hFried

/-- **The quadratic for a general blackening factor `f`.** The junction condition with
`H² + 𝒦 f(r)/a²` under the root gives Eq. (26) with `ρ_BH` replaced by `ρ_bulk`. -/
theorem isInduced_of_junction_f (c : Couplings) (f : ℝ → ℝ) {K ε a H ρ ρt : ℝ}
    (hε : ε ^ 2 = 1)
    (hFried : H ^ 2 + K / a ^ 2 = 8 * π * c.GN / 3 * (ρ + ρt))
    (hJunc : ε * √(H ^ 2 + K / a ^ 2 * f (braneRadius K a)) = -(8 * π * c.Gb / 3) * ρt)
    (hArg : 0 ≤ H ^ 2 + K / a ^ 2 * f (braneRadius K a)) :
    IsInduced c.rhoS (rhoBulk c.GN K f a) ρ ρt := by
  rw [curv_mul_f f c.GN_pos.ne', ← add_sub_assoc] at hJunc hArg
  exact isInduced_of_bulk c hε hFried hJunc hArg

/-- **Friedmann + junction ⇒ quadratic, Schwarzschild bulk.** From Eq. (11), the spatial
junction condition (Eqs. (10) and (24)) and `ε² = 1`, the induced density satisfies the
quadratic of Eq. (26). -/
theorem isInduced_of_junction (c : Couplings) {K H0 rh ε a H ρ ρt : ℝ}
    (hε : ε ^ 2 = 1) (ha : a ≠ 0) (hH0 : H0 ≠ 0)
    (hFried : H ^ 2 + K / a ^ 2 = 8 * π * c.GN / 3 * (ρ + ρt))
    (hJunc : ε * √(H ^ 2 + K / a ^ 2 - K ^ 2 * rh ^ 2 / a ^ 4) = -(8 * π * c.Gb / 3) * ρt)
    (hArg : 0 ≤ H ^ 2 + K / a ^ 2 - K ^ 2 * rh ^ 2 / a ^ 4) :
    IsInduced c.rhoS (rhoBH c.GN K H0 rh a) ρ ρt := by
  rw [rhoBH_term c.GN_pos.ne' hH0 ha] at hJunc hArg
  exact isInduced_of_bulk c hε hFried hJunc hArg

/-- **Reality constraint, Eq. (30).** A real induced density exists only if
`ρ̃_s ≥ 2(ρ_BH - ρ)`. -/
theorem reality {s b ρ x : ℝ} (hs : 0 < s) (h : IsInduced s b ρ x) : 2 * (b - ρ) ≤ s := by
  unfold IsInduced at h
  nlinarith [sq_nonneg (x - s)]

/-- **The pressure singularity is the equality case of Eq. (30).** `ρ̃ = ρ̃_s` exactly when the
reality bound is saturated (ROADMAP M3.4). -/
theorem isInduced_eq_rhoS_iff {s b ρ x : ℝ} (hs : 0 < s) (h : IsInduced s b ρ x) :
    x = s ↔ 2 * (b - ρ) = s := by
  unfold IsInduced at h
  constructor
  · intro hx
    rw [hx] at h
    have : s * (2 * (b - ρ) - s) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hs.ne'
    · linarith
  · intro hb
    have : (x - s) ^ 2 = 0 := by linear_combination h - s * hb
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- **Eq. (26).** Under the reality condition the quadratic has exactly the two branches
`ρ̃_± = ρ̃_s (1 ± √(1 - 2(ρ_BH - ρ)/ρ̃_s))`. -/
theorem isInduced_iff {s b ρ x : ℝ} (hs : 0 < s) (hreal : 2 * (b - ρ) ≤ s) :
    IsInduced s b ρ x ↔ x = rhoTilde 1 s b ρ ∨ x = rhoTilde (-1) s b ρ := by
  have hD : 0 ≤ 1 - 2 * (b - ρ) / s := by
    rw [sub_nonneg, div_le_one hs]; exact hreal
  have key : IsInduced s b ρ x ↔ (x - s) ^ 2 = (s * √(1 - 2 * (b - ρ) / s)) ^ 2 := by
    rw [mul_pow, sq_sqrt hD]
    unfold IsInduced
    constructor <;> intro h
    · field_simp; linear_combination h
    · field_simp at h; linear_combination h
  rw [key, sq_eq_sq_iff_eq_or_eq_neg]
  unfold rhoTilde
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith

/-- Eq. (15) and Eq. (26) are the same expression once `μ` is identified via Eq. (29). -/
theorem eq15_eq_eq26 {GN K H0 rh a s ρ sgn : ℝ} :
    s * (1 + sgn * √(1 - mu K H0 rh ^ 2 / (12 * π * GN * s) * (1 / a ^ 4) + 2 * ρ / s))
      = rhoTilde sgn s (rhoBH GN K H0 rh a) ρ := by
  have h := mu_sq_term (GN := GN) (a := a) (rh := rh) (K := K) (H0 := H0)
  unfold rhoTilde
  congr 3
  rw [show mu K H0 rh ^ 2 / (12 * π * GN * s) * (1 / a ^ 4)
      = mu K H0 rh ^ 2 / (12 * π * GN * a ^ 4) / s by ring, h]
  ring_nf

/-- The sign of the induced density is fixed by the orientation `ε` of the normal:
with `ε = -1` (the paper's choice) the junction condition forces `ρ̃ ≥ 0`. -/
theorem rhoTilde_nonneg_of_eps_neg {Gb X ρt : ℝ} (hGb : 0 < Gb)
    (hJunc : -1 * √X = -(8 * π * Gb / 3) * ρt) : 0 ≤ ρt := by
  have hc : 0 < 8 * π * Gb / 3 := by positivity
  nlinarith [sqrt_nonneg X]

/-- The normal branch is negative exactly when ordinary matter dominates the bulk black hole. -/
theorem rhoTilde_minus_neg_iff {s b ρ : ℝ} (hs : 0 < s) :
    rhoTilde (-1) s b ρ < 0 ↔ b < ρ := by
  have key : rhoTilde (-1) s b ρ < 0 ↔ 1 < √(1 - 2 * (b - ρ) / s) := by
    unfold rhoTilde
    constructor <;> intro h <;> nlinarith
  rw [key, lt_sqrt zero_le_one, one_pow,
    show 1 - 2 * (b - ρ) / s = 1 + 2 * (ρ - b) / s by ring, lt_add_iff_pos_right,
    div_pos_iff_of_pos_right hs]
  constructor <;> intro h <;> linarith

/-- With the paper's `ε = -1`, the normal branch `ρ̃_-` is compatible with the junction
condition only when `ρ_BH ≥ ρ`. The region `ρ_BH < ρ` (part of Eq. (34)) needs `ε = +1`. This
is not a contradiction: `ε = -1` is inferred circularly in the paper, and Eq. (16) holds for
either orientation. See `Orientation.lean` (`orientation_minus_branch`,
`pressure_of_timelike_junction`). -/
theorem normal_branch_requires {Gb X s b ρ : ℝ} (hGb : 0 < Gb) (hs : 0 < s)
    (hJunc : -1 * √X = -(8 * π * Gb / 3) * rhoTilde (-1) s b ρ) : ρ ≤ b := by
  by_contra h
  have := (rhoTilde_minus_neg_iff (b := b) (ρ := ρ) hs).2 (not_le.1 h)
  have := rhoTilde_nonneg_of_eps_neg hGb hJunc
  linarith

end WhiteHole
