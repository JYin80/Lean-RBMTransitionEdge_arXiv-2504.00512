module

public import RBMTransitionEdge.Edge.FcDet
public import RBMTransitionEdge.Edge.FcRigid
public import RBMTransitionEdge.LocalLaw.Rigidity
public import RBMTransitionEdge.Prob.BlockOU

@[expose] public section

/-!
# The free-convolution edge and curvature of `V` in the proof of Lemma 4.1

For `V = e^{-𝔱/2} H + Λ` and `t' = 1 - e^{-𝔱}`, the right edge `E_fc` and the curvature `γ_fc` of
the free convolution of the spectrum of `V` with the semicircle law of variance `t'` are close to
`E⁺` and `γ₊` with high probability (proof of Lemma 4.1 [CVtG], after [CorrelatedBandAOP,
Section 6.1]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ## Elementary inequalities -/

/-- `|1/p - 1/q| ≤ |p - q| / m²` for `0 < m ≤ p` and `m ≤ q`. -/
private lemma FcClose_inv_lip {m p q : ℝ} (hm : 0 < m) (hp : m ≤ p) (hq : m ≤ q) :
    |1 / p - 1 / q| ≤ |p - q| / m ^ 2 := by
  have hp0 : 0 < p := hm.trans_le hp
  have hq0 : 0 < q := hm.trans_le hq
  have e : 1 / p - 1 / q = (q - p) / (p * q) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hp0 hq0), abs_sub_comm]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith [mul_le_mul hp hq hm.le hp0.le]

/-- `|1/p³ - 1/q³| ≤ 3 |p - q| / m⁴` for `0 < m ≤ p` and `m ≤ q`. -/
private lemma FcClose_inv3_lip {m p q : ℝ} (hm : 0 < m) (hp : m ≤ p) (hq : m ≤ q) :
    |1 / p ^ 3 - 1 / q ^ 3| ≤ 3 * |p - q| / m ^ 4 := by
  have hp0 : 0 < p := hm.trans_le hp
  have hq0 : 0 < q := hm.trans_le hq
  have e : 1 / p ^ 3 - 1 / q ^ 3 =
      (1 / p - 1 / q) * (1 / p ^ 2 + 1 / (p * q) + 1 / q ^ 2) := by
    field_simp; ring
  have h1 := FcClose_inv_lip hm hp hq
  have hm2 : 0 < m ^ 2 := by positivity
  have b1 : 1 / p ^ 2 ≤ 1 / m ^ 2 :=
    one_div_le_one_div_of_le hm2 (pow_le_pow_left₀ hm.le hp 2)
  have b2 : 1 / (p * q) ≤ 1 / m ^ 2 :=
    one_div_le_one_div_of_le hm2 (by nlinarith [mul_le_mul hp hq hm.le hp0.le])
  have b3 : 1 / q ^ 2 ≤ 1 / m ^ 2 :=
    one_div_le_one_div_of_le hm2 (pow_le_pow_left₀ hm.le hq 2)
  have hs0 : 0 ≤ 1 / p ^ 2 + 1 / (p * q) + 1 / q ^ 2 := by positivity
  rw [e, abs_mul, abs_of_nonneg hs0]
  calc |1 / p - 1 / q| * (1 / p ^ 2 + 1 / (p * q) + 1 / q ^ 2)
      ≤ |p - q| / m ^ 2 * (3 * (1 / m ^ 2)) :=
        mul_le_mul h1 (by linarith) hs0 (by positivity)
    _ = 3 * |p - q| / m ^ 4 := by field_simp

/-- `(q - p) / q³ ≤ 1/p² - 1/q²` for `0 < p ≤ q`. -/
private lemma FcClose_inv2_gap {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (q - p) * (1 / q ^ 3) ≤ 1 / p ^ 2 - 1 / q ^ 2 := by
  have hq : 0 < q := hp.trans_le hpq
  have e : 1 / p ^ 2 - 1 / q ^ 2 - (q - p) * (1 / q ^ 3) =
      (q - p) * (q ^ 2 + p * q - p ^ 2) / (p ^ 2 * q ^ 3) := by
    field_simp; ring
  have h0 : 0 ≤ (q - p) * (q ^ 2 + p * q - p ^ 2) / (p ^ 2 * q ^ 3) :=
    div_nonneg (mul_nonneg (sub_nonneg.2 hpq) (by nlinarith)) (by positivity)
  linarith

/-! ## Moments of a density supported left of `E` -/

/-- A continuous probability density `ρ ≥ 0` that vanishes on `[E, ∞)`. -/
private def FcClose_Dens (ρ : ℝ → ℝ) (E : ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ Continuous ρ ∧ Integrable ρ ∧ ∫ x, ρ x = 1 ∧ ∀ x, E ≤ x → ρ x = 0

/-- The moment `∫ ρ(x) (u - x)^{-j} dx`. -/
private def FcClose_r (ρ : ℝ → ℝ) (j : ℕ) (u : ℝ) : ℝ := ∫ x, ρ x / (u - x) ^ j

/-- The integrand of `FcClose_r ρ j u` is integrable for `u > E`. -/
private lemma FcClose_int {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) (j : ℕ) {u : ℝ}
    (hu : E < u) : Integrable fun x => ρ x / (u - x) ^ j := by
  obtain ⟨h0, hc, hi, -, hz⟩ := hd
  have hpos : 0 < u - E := by linarith
  refine (hi.mul_const (((u - E) ^ j)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hc.measurable.div
      ((measurable_const.sub measurable_id).pow_const j)).aestronglyMeasurable
  · by_cases hx : E ≤ x
    · simp [hz x hx]
    · rw [not_le] at hx
      have hux : u - E ≤ u - x := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (h0 x), abs_of_pos (pow_pos (by linarith) j),
        div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hpos j) (pow_le_pow_left₀ hpos.le hux j))
        (h0 x)

/-- `|∫ f - ∫ g| ≤ ∫ h` when `|f - g| ≤ h` pointwise. -/
private lemma FcClose_diff_le {f g h : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hh : Integrable h) (hb : ∀ x, |f x - g x| ≤ h x) : |(∫ x, f x) - ∫ x, g x| ≤ ∫ x, h x := by
  rw [← integral_sub hf hg]
  have := norm_integral_le_of_norm_le hh (Filter.Eventually.of_forall fun x =>
    (by rw [Real.norm_eq_abs]; exact hb x : ‖f x - g x‖ ≤ h x))
  rwa [Real.norm_eq_abs] at this

/-- `|r_1(a) - r_1(b)| ≤ |a - b| r_2(m)` for `E < m ≤ a, b`. -/
private lemma FcClose_lip1 {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) {m a b : ℝ} (hm : E < m)
    (ha : m ≤ a) (hb : m ≤ b) :
    |FcClose_r ρ 1 a - FcClose_r ρ 1 b| ≤ |a - b| * FcClose_r ρ 2 m := by
  unfold FcClose_r
  rw [← integral_const_mul]
  refine FcClose_diff_le (FcClose_int hd 1 (by linarith)) (FcClose_int hd 1 (by linarith))
    ((FcClose_int hd 2 hm).const_mul _) fun x => ?_
  by_cases hx : E ≤ x
  · simp [hd.2.2.2.2 x hx]
  · rw [not_le] at hx
    have h := FcClose_inv_lip (show 0 < m - x by linarith) (show m - x ≤ a - x by linarith)
      (show m - x ≤ b - x by linarith)
    have e1 : ρ x / (a - x) ^ 1 - ρ x / (b - x) ^ 1 = ρ x * (1 / (a - x) - 1 / (b - x)) := by
      simp only [pow_one]; ring
    have e2 : |a - b| * (ρ x / (m - x) ^ 2) = ρ x * (|a - x - (b - x)| / (m - x) ^ 2) := by
      rw [show a - x - (b - x) = a - b by ring]; ring
    rw [e1, e2, abs_mul, abs_of_nonneg (hd.1 x)]
    exact mul_le_mul_of_nonneg_left h (hd.1 x)

/-- `|r_3(a) - r_3(b)| ≤ 3 |a - b| r_4(m)` for `E < m ≤ a, b`. -/
private lemma FcClose_lip3 {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) {m a b : ℝ} (hm : E < m)
    (ha : m ≤ a) (hb : m ≤ b) :
    |FcClose_r ρ 3 a - FcClose_r ρ 3 b| ≤ 3 * |a - b| * FcClose_r ρ 4 m := by
  unfold FcClose_r
  rw [← integral_const_mul]
  refine FcClose_diff_le (FcClose_int hd 3 (by linarith)) (FcClose_int hd 3 (by linarith))
    ((FcClose_int hd 4 hm).const_mul _) fun x => ?_
  by_cases hx : E ≤ x
  · simp [hd.2.2.2.2 x hx]
  · rw [not_le] at hx
    have h := FcClose_inv3_lip (show 0 < m - x by linarith) (show m - x ≤ a - x by linarith)
      (show m - x ≤ b - x by linarith)
    have e1 : ρ x / (a - x) ^ 3 - ρ x / (b - x) ^ 3 =
        ρ x * (1 / (a - x) ^ 3 - 1 / (b - x) ^ 3) := by ring
    have e2 : 3 * |a - b| * (ρ x / (m - x) ^ 4) =
        ρ x * (3 * |a - x - (b - x)| / (m - x) ^ 4) := by
      rw [show a - x - (b - x) = a - b by ring]; ring
    rw [e1, e2, abs_mul, abs_of_nonneg (hd.1 x)]
    exact mul_le_mul_of_nonneg_left h (hd.1 x)

/-- `(b - a) r_3(b) ≤ r_2(a) - r_2(b)` for `E < a ≤ b`. -/
private lemma FcClose_gap {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) {a b : ℝ} (ha : E < a)
    (hab : a ≤ b) : (b - a) * FcClose_r ρ 3 b ≤ FcClose_r ρ 2 a - FcClose_r ρ 2 b := by
  unfold FcClose_r
  rw [← integral_const_mul, ← integral_sub (FcClose_int hd 2 ha) (FcClose_int hd 2 (by linarith))]
  refine integral_mono ((FcClose_int hd 3 (by linarith)).const_mul _)
    ((FcClose_int hd 2 ha).sub (FcClose_int hd 2 (by linarith))) fun x => ?_
  by_cases hx : E ≤ x
  · simp [hd.2.2.2.2 x hx]
  · rw [not_le] at hx
    have h := FcClose_inv2_gap (show 0 < a - x by linarith) (show a - x ≤ b - x by linarith)
    have e1 : (b - a) * (ρ x / (b - x) ^ 3) = ρ x * ((b - x - (a - x)) * (1 / (b - x) ^ 3)) := by
      rw [show b - x - (a - x) = b - a by ring]; ring
    have e2 : ρ x / (a - x) ^ 2 - ρ x / (b - x) ^ 2 =
        ρ x * (1 / (a - x) ^ 2 - 1 / (b - x) ^ 2) := by ring
    simp only
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h (hd.1 x)

/-- `r_2(u) ≤ 1` for `u ≥ E + 1`. -/
private lemma FcClose_far {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) {u : ℝ} (hu : E + 1 ≤ u) :
    FcClose_r ρ 2 u ≤ 1 := by
  unfold FcClose_r
  rw [← hd.2.2.2.1]
  refine integral_mono (FcClose_int hd 2 (by linarith)) hd.2.2.1 fun x => ?_
  by_cases hx : E ≤ x
  · simp [hd.2.2.2.2 x hx]
  · rw [not_le] at hx
    have h1 : 1 ≤ (u - x) ^ 2 := by nlinarith
    exact div_le_self (hd.1 x) h1


/-! ## The deterministic perturbation of the root -/

/-- From `T r = 1`, `s r ≤ K₁` and `1 ≤ K₁ s r`: `s ≤ K₁ T` and `T ≤ K₁ s`. -/
private lemma FcClose_scale {T s r K₁ : ℝ} (hT : 0 < T) (hr : T * r = 1) (hu : s * r ≤ K₁)
    (hl : 1 ≤ K₁ * (s * r)) : s ≤ K₁ * T ∧ T ≤ K₁ * s := by
  constructor
  · have e1 : s = T * (s * r) := by linear_combination (-s) * hr
    rw [e1, mul_comm K₁]
    exact mul_le_mul_of_nonneg_left hu hT.le
  · have e1 : K₁ * s = T * (K₁ * (s * r)) := by linear_combination (-(K₁ * s)) * hr
    rw [e1]
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * (K₁ * (s * r)) := mul_le_mul_of_nonneg_left hl hT.le

/-- `x ≥ 0` from `1 ≤ K₁ (σ x)` with `K₁, σ ≥ 0`. -/
private lemma FcClose_nonneg {K₁ σ x : ℝ} (hK : 0 ≤ K₁) (hσ : 0 ≤ σ) (h : 1 ≤ K₁ * (σ * x)) :
    0 ≤ x := by
  by_contra hx
  rw [not_le] at hx
  have : K₁ * (σ * x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK
    (mul_nonpos_of_nonneg_of_nonpos hσ hx.le)
  linarith

/-- `s/2 ≤ √x` for `s ≥ 0` and `s²/4 ≤ x`. -/
private lemma FcClose_sqrt_ge {s x : ℝ} (hs : 0 ≤ s) (hx : s ^ 2 / 4 ≤ x) :
    s / 2 ≤ Real.sqrt x := by
  rw [show s / 2 = Real.sqrt ((s / 2) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `√x ≤ 2 s` for `s ≥ 0` and `x ≤ 4 s²`. -/
private lemma FcClose_sqrt_le {s x : ℝ} (hs : 0 ≤ s) (hx : x ≤ 4 * s ^ 2) :
    Real.sqrt x ≤ 2 * s := by
  rw [show 2 * s = Real.sqrt ((2 * s) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The upper end of the bracket of the root: `T m < 1`. -/
private lemma FcClose_hi {T s δ K K₁ e R2 r2 r3 m2 : ℝ} (hT : 0 < T) (hs : 0 < s) (hK : 0 < K)
    (he : 0 < e) (hδs : δ * s = 16 * K * K₁ * e) (h3 : 1 ≤ 8 * K₁ * (s ^ 3 * r3))
    (hg : δ * r3 ≤ R2 - r2) (hR2 : T * R2 = 1) (hm : |m2 - r2| * s ^ 4 ≤ K * e) :
    T * m2 < 1 := by
  have hs4 : 0 < s ^ 4 := by positivity
  have h1 : m2 ≤ r2 + |m2 - r2| := by linarith [le_abs_self (m2 - r2)]
  have h2 : 2 * K * e ≤ δ * r3 * s ^ 4 := by
    have e1 : δ * r3 * s ^ 4 = 2 * K * e * (8 * K₁ * (s ^ 3 * r3)) := by
      linear_combination (r3 * s ^ 3) * hδs
    rw [e1]
    exact le_mul_of_one_le_right (by positivity) h3
  have h4 : T * m2 ≤ 1 - T * (δ * r3) + T * |m2 - r2| := by
    have := mul_le_mul_of_nonneg_left h1 hT.le
    have := mul_le_mul_of_nonneg_left hg hT.le
    linarith
  have h5 : T * m2 * s ^ 4 ≤ s ^ 4 - T * (δ * r3 * s ^ 4) + T * (|m2 - r2| * s ^ 4) := by
    have := mul_le_mul_of_nonneg_right h4 hs4.le
    linarith
  have h6 : T * (2 * K * e) ≤ T * (δ * r3 * s ^ 4) := mul_le_mul_of_nonneg_left h2 hT.le
  have h7 : T * (|m2 - r2| * s ^ 4) ≤ T * (K * e) := mul_le_mul_of_nonneg_left hm hT.le
  have h8 : 0 < T * (K * e) := by positivity
  have : T * m2 * s ^ 4 < 1 * s ^ 4 := by linarith
  exact lt_of_mul_lt_mul_right this hs4.le

/-- The lower end of the bracket of the root: `T m > 1`. -/
private lemma FcClose_lo {T s δ K K₁ e R2 R3 r2 m2 : ℝ} (hT : 0 < T) (hs : 0 < s) (hK : 0 < K)
    (he : 0 < e) (hδs : δ * s = 16 * K * K₁ * e) (h3 : 1 ≤ K₁ * (s ^ 3 * R3))
    (hg : δ * R3 ≤ r2 - R2) (hR2 : T * R2 = 1) (hm : |m2 - r2| * s ^ 4 ≤ 4 * (K * e)) :
    1 < T * m2 := by
  have hs4 : 0 < s ^ 4 := by positivity
  have h1 : r2 - |m2 - r2| ≤ m2 := by linarith [neg_abs_le (m2 - r2)]
  have h2 : 16 * K * e ≤ δ * R3 * s ^ 4 := by
    have e1 : δ * R3 * s ^ 4 = 16 * K * e * (K₁ * (s ^ 3 * R3)) := by
      linear_combination (R3 * s ^ 3) * hδs
    rw [e1]
    exact le_mul_of_one_le_right (by positivity) h3
  have h4 : 1 + T * (δ * R3) - T * |m2 - r2| ≤ T * m2 := by
    have := mul_le_mul_of_nonneg_left h1 hT.le
    have := mul_le_mul_of_nonneg_left hg hT.le
    linarith
  have h5 : s ^ 4 + T * (δ * R3 * s ^ 4) - T * (|m2 - r2| * s ^ 4) ≤ T * m2 * s ^ 4 := by
    have := mul_le_mul_of_nonneg_right h4 hs4.le
    linarith
  have h6 : T * (16 * K * e) ≤ T * (δ * R3 * s ^ 4) := mul_le_mul_of_nonneg_left h2 hT.le
  have h7 : T * (|m2 - r2| * s ^ 4) ≤ T * (4 * (K * e)) := mul_le_mul_of_nonneg_left hm hT.le
  have h8 : 0 < T * (K * e) := by positivity
  have : 1 * s ^ 4 < T * m2 * s ^ 4 := by linarith
  exact lt_of_mul_lt_mul_right this hs4.le

/-- The arithmetic of the edge bound: `d + T Y + T Z ≤ 50 K K₁⁴ e / T`. -/
private lemma FcClose_edge_arith {T s δ K K₁ e d Y Z : ℝ} (hT : 0 < T) (hs : 0 < s) (hK : 0 < K)
    (he : 0 < e) (hK₁ : 1 ≤ K₁) (hTs : T ≤ K₁ * s) (hδs : δ * s = 16 * K * K₁ * e)
    (hd : d ≤ δ) (hY : Y * s ^ 2 ≤ 2 * (K * e)) (hZ : Z * s ≤ δ * (2 * K₁)) :
    d + T * Y + T * Z ≤ 50 * K * K₁ ^ 4 * e / T := by
  rw [le_div_iff₀ hT]
  obtain ⟨q, hq⟩ : ∃ q, q = T / s := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqK : q ≤ K₁ := by rw [hq, div_le_iff₀ hs]; linarith
  have hTq : T = q * s := by rw [hq]; field_simp
  have h1 : d * T ≤ 16 * K * K₁ * e * q := by
    have : δ * T = 16 * K * K₁ * e * q := by
      rw [hTq, show δ * (q * s) = (δ * s) * q by ring, hδs]
    rw [← this]; exact mul_le_mul_of_nonneg_right hd hT.le
  have h2 : T * Y * T ≤ 2 * (K * e) * q ^ 2 := by
    rw [hTq, show q * s * Y * (q * s) = q ^ 2 * (Y * s ^ 2) by ring, mul_comm (2 * (K * e))]
    exact mul_le_mul_of_nonneg_left hY (by positivity)
  have h3 : T * Z * T ≤ 2 * K₁ * (16 * K * K₁ * e) * q ^ 2 := by
    rw [hTq, show q * s * Z * (q * s) = q ^ 2 * s * (Z * s) by ring]
    have h1 : q ^ 2 * s * (Z * s) ≤ q ^ 2 * s * (δ * (2 * K₁)) :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    have h2 : q ^ 2 * s * (δ * (2 * K₁)) = 2 * K₁ * (δ * s) * q ^ 2 := by ring
    rw [h2, hδs] at h1
    exact h1
  have hq2 : q ^ 2 ≤ K₁ ^ 2 := pow_le_pow_left₀ hq0 hqK 2
  have hK0 : 0 < K₁ := by linarith
  have hKe : 0 < K * e := mul_pos hK he
  have h4 : 16 * K * K₁ * e * q ≤ 16 * K * K₁ * e * K₁ :=
    mul_le_mul_of_nonneg_left hqK (by positivity)
  have h5 : 2 * (K * e) * q ^ 2 ≤ 2 * (K * e) * K₁ ^ 2 :=
    mul_le_mul_of_nonneg_left hq2 (by positivity)
  have h6 : 2 * K₁ * (16 * K * K₁ * e) * q ^ 2 ≤ 2 * K₁ * (16 * K * K₁ * e) * K₁ ^ 2 :=
    mul_le_mul_of_nonneg_left hq2 (by positivity)
  have hK2 : K₁ ^ 2 ≤ K₁ ^ 4 := pow_le_pow_right₀ hK₁ (by norm_num)
  have hK1 : K₁ ≤ K₁ ^ 2 := by nlinarith
  have h7 : K * e * K₁ ^ 2 ≤ K * e * K₁ ^ 4 := mul_le_mul_of_nonneg_left hK2 hKe.le
  have h8 : K * e * K₁ ^ 4 = K * K₁ ^ 4 * e := by ring
  have e1 : (d + T * Y + T * Z) * T = d * T + T * Y * T + T * Z * T := by ring
  have e2 : 16 * K * K₁ * e * K₁ = 16 * (K * e * K₁ ^ 2) := by ring
  have e3 : 2 * K₁ * (16 * K * K₁ * e) * K₁ ^ 2 = 32 * (K * e * K₁ ^ 4) := by ring
  nlinarith

/-- The arithmetic of the third-moment bound: `Y + Z ≤ 1544 K K₁⁶ e T^{-3} R`. -/
private lemma FcClose_mom3_arith {T s K K₁ e Y Z R : ℝ} (hT : 0 < T) (hs : 0 < s) (hK : 0 < K)
    (he : 0 < e) (hK₁ : 1 ≤ K₁) (hTs : T ≤ K₁ * s) (hY : Y * s ^ 6 ≤ 8 * (K * e))
    (hZ : Z * s ^ 6 ≤ 1536 * K * K₁ ^ 2 * e) (h3 : 1 ≤ K₁ * (s ^ 3 * R)) :
    Y + Z ≤ 1544 * K * K₁ ^ 6 * (e / T ^ 3) * R := by
  have hs6 : 0 < s ^ 6 := by positivity
  have hT30 : 0 < T ^ 3 := by positivity
  have hK₁2 : 1 ≤ K₁ ^ 2 := one_le_pow₀ hK₁
  have hsum : (Y + Z) * s ^ 6 ≤ 1544 * K * K₁ ^ 2 * e := by
    have : 8 * (K * e) ≤ 8 * (K * e) * K₁ ^ 2 :=
      le_mul_of_one_le_right (by positivity) hK₁2
    nlinarith
  have hT3 : T ^ 3 ≤ K₁ ^ 3 * s ^ 3 := by
    have := pow_le_pow_left₀ hT.le hTs 3
    rwa [mul_pow] at this
  have hfin : 1544 * K * K₁ ^ 2 * e ≤ 1544 * K * K₁ ^ 6 * (e / T ^ 3) * R * s ^ 6 := by
    have e1 : 1544 * K * K₁ ^ 6 * (e / T ^ 3) * R * s ^ 6 =
        1544 * K * K₁ ^ 2 * e * ((K₁ * (s ^ 3 * R)) * (K₁ ^ 3 * s ^ 3 / T ^ 3)) := by
      field_simp
    rw [e1]
    have h1 : 1 ≤ K₁ ^ 3 * s ^ 3 / T ^ 3 := by rw [le_div_iff₀ hT30]; linarith
    have h2 : 1 ≤ (K₁ * (s ^ 3 * R)) * (K₁ ^ 3 * s ^ 3 / T ^ 3) := by nlinarith
    exact le_mul_of_one_le_right (by positivity) h2
  exact le_of_mul_le_mul_right (hsum.trans hfin) hs6

/-- The location of the root `u_fc` of `T m_2(u) = 1` (proof of Lemma 4.1 [CVtG]): with
`κ_* = u_* - E = s²`, `δ = 16 K K₁ e / s`, one has `T ≤ K₁ s`, `δ ≤ κ_*/2`, `4w ≤ κ_* ≤ 1/2`,
`|u_fc - u_*| ≤ δ` and `1 ≤ K₁ s³ r_3(u_*)`. -/
private lemma FcClose_loc {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) (m : ℕ → ℝ → ℝ)
    {K K₁ T e w l us uf : ℝ} (hK : 0 < K) (hK₁ : 1 ≤ K₁) (hT : 0 < T) (he : 0 < e)
    (hw : 0 < w)
    (hedge : ∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      1 ≤ K₁ * (Real.sqrt κ ^ (2 * j - 3) * FcClose_r ρ j (E + κ)) ∧
        Real.sqrt κ ^ (2 * j - 3) * FcClose_r ρ j (E + κ) ≤ K₁)
    (hrig : ∀ u : ℝ, w ≤ u - E → u - E ≤ 1 →
      |m 2 u - FcClose_r ρ 2 u| * (u - E) ^ 2 ≤ K * e)
    (hanti : ∀ u v : ℝ, l < u → u ≤ v → m 2 v ≤ m 2 u)
    (hl : l ≤ E + w) (hus : E < us) (hr2 : T * FcClose_r ρ 2 us = 1) (hluf : l < uf)
    (hm2 : T * m 2 uf = 1)
    (hS2 : K₁ ^ 2 * T ^ 2 ≤ 1 / 2) (hS3 : 4 * w * K₁ ^ 2 ≤ T ^ 2)
    (hS4 : 32 * K * K₁ ^ 4 * e ≤ T ^ 3) :
    ∃ s δ : ℝ, 0 < s ∧ s ^ 2 = us - E ∧ T ≤ K₁ * s ∧ δ * s = 16 * K * K₁ * e ∧ 0 < δ ∧
      δ ≤ (us - E) / 2 ∧ 4 * w ≤ us - E ∧ us - E ≤ 1 / 2 ∧ |uf - us| ≤ δ ∧
      1 ≤ K₁ * (s ^ 3 * FcClose_r ρ 3 us) := by
  have hK₁0 : 0 < K₁ := by linarith
  have hK₁2 : 1 ≤ K₁ ^ 2 := one_le_pow₀ hK₁
  have hT1 : T < 1 := by
    have : T ^ 2 ≤ 1 / 2 := by nlinarith
    nlinarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = us - E := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by linarith
  have hus' : E + κ = us := by rw [hκ]; ring
  have hκ1 : κ ≤ 1 := by
    by_contra h
    have h1 := FcClose_far hd (show E + 1 ≤ us by linarith)
    have h2 : T * FcClose_r ρ 2 us ≤ T * 1 := mul_le_mul_of_nonneg_left h1 hT.le
    linarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt κ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hκ0
  have hss : s ^ 2 = κ := by rw [hs]; exact Real.sq_sqrt hκ0.le
  obtain ⟨h2l, h2u⟩ := hedge 2 le_rfl (by norm_num) κ hκ0 hκ1
  rw [hus', show (2 * 2 - 3 : ℕ) = 1 from rfl, pow_one, ← hs] at h2l h2u
  obtain ⟨hsT, hTs⟩ := FcClose_scale hT hr2 h2u h2l
  have hκ2 : κ ≤ 1 / 2 := by
    have := pow_le_pow_left₀ hs0.le hsT 2
    rw [hss, mul_pow] at this
    linarith
  have hT3 : T ^ 3 ≤ K₁ ^ 3 * s ^ 3 := by
    have := pow_le_pow_left₀ hT.le hTs 3
    rwa [mul_pow] at this
  have hT2 : T ^ 2 ≤ K₁ ^ 2 * κ := by
    have := pow_le_pow_left₀ hT.le hTs 2
    rwa [mul_pow, hss] at this
  have hs3 : 32 * K * K₁ * e ≤ s ^ 3 := by
    have h1 : K₁ ^ 3 * (32 * K * K₁ * e) ≤ K₁ ^ 3 * s ^ 3 := by
      have : K₁ ^ 3 * (32 * K * K₁ * e) = 32 * K * K₁ ^ 4 * e := by ring
      linarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hwκ : 4 * w ≤ κ := by
    have h1 : K₁ ^ 2 * (4 * w) ≤ K₁ ^ 2 * κ := by linarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 16 * K * K₁ * e / s := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδs : δ * s = 16 * K * K₁ * e := by rw [hδ]; field_simp
  have hδκ : δ ≤ κ / 2 := by
    refine le_of_mul_le_mul_right ?_ hs0
    rw [hδs, ← hss]
    have : s ^ 2 / 2 * s = s ^ 3 / 2 := by ring
    linarith
  have hb1 : κ ≤ us + δ - E := by linarith
  have hb2 : us + δ - E ≤ 3 * κ / 2 := by linarith
  have ha1 : κ / 2 ≤ us - δ - E := by linarith
  have ha2 : us - δ - E ≤ 3 * κ / 2 := by linarith
  have hEa : E < us - δ := by linarith
  -- `T m_2(u_* + δ) < 1`
  obtain ⟨h3b, -⟩ := hedge 3 (by norm_num) (by norm_num) (us + δ - E) (by linarith) (by linarith)
  rw [show E + (us + δ - E) = us + δ by ring, show (2 * 3 - 3 : ℕ) = 3 from rfl] at h3b
  have hσb := FcClose_sqrt_le hs0.le (show us + δ - E ≤ 4 * s ^ 2 by linarith)
  have hr3b0 := FcClose_nonneg hK₁0.le (by positivity) h3b
  have hr3b : 1 ≤ 8 * K₁ * (s ^ 3 * FcClose_r ρ 3 (us + δ)) := by
    have h1 : Real.sqrt (us + δ - E) ^ 3 ≤ (2 * s) ^ 3 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hσb 3
    calc (1 : ℝ) ≤ K₁ * (Real.sqrt (us + δ - E) ^ 3 * FcClose_r ρ 3 (us + δ)) := h3b
      _ ≤ K₁ * ((2 * s) ^ 3 * FcClose_r ρ 3 (us + δ)) := by gcongr
      _ = 8 * K₁ * (s ^ 3 * FcClose_r ρ 3 (us + δ)) := by ring
  have hgb := FcClose_gap hd hus (show us ≤ us + δ by linarith)
  rw [show us + δ - us = δ by ring] at hgb
  have hmb : |m 2 (us + δ) - FcClose_r ρ 2 (us + δ)| * s ^ 4 ≤ K * e := by
    have h0 := hrig (us + δ) (by linarith) (by linarith)
    have h1 : s ^ 4 ≤ (us + δ - E) ^ 2 := by
      rw [show s ^ 4 = κ ^ 2 by rw [← hss]; ring]
      exact pow_le_pow_left₀ hκ0.le hb1 2
    exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans h0
  have hTb := FcClose_hi hT hs0 hK he hδs hr3b hgb hr2 hmb
  -- `T m_2(u_* - δ) > 1`
  obtain ⟨h3l, -⟩ := hedge 3 (by norm_num) (by norm_num) κ hκ0 hκ1
  rw [hus', show (2 * 3 - 3 : ℕ) = 3 from rfl, ← hs] at h3l
  have hga := FcClose_gap hd hEa (show us - δ ≤ us by linarith)
  rw [show us - (us - δ) = δ by ring] at hga
  have hma : |m 2 (us - δ) - FcClose_r ρ 2 (us - δ)| * s ^ 4 ≤ 4 * (K * e) := by
    have h0 := hrig (us - δ) (by linarith) (by linarith)
    have h1 : s ^ 4 ≤ 4 * (us - δ - E) ^ 2 := by
      rw [show s ^ 4 = κ ^ 2 by rw [← hss]; ring]
      have := pow_le_pow_left₀ (by positivity) ha1 2
      linarith
    calc |m 2 (us - δ) - FcClose_r ρ 2 (us - δ)| * s ^ 4
        ≤ |m 2 (us - δ) - FcClose_r ρ 2 (us - δ)| * (4 * (us - δ - E) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = 4 * (|m 2 (us - δ) - FcClose_r ρ 2 (us - δ)| * (us - δ - E) ^ 2) := by ring
      _ ≤ 4 * (K * e) := by linarith
  have hTa := FcClose_lo hT hs0 hK he hδs h3l hga hr2 hma
  -- the root lies between
  have hla : l < us - δ := by linarith
  have hufb : uf < us + δ := by
    by_contra h
    rw [not_lt] at h
    have h1 := mul_le_mul_of_nonneg_left (hanti (us + δ) uf (by linarith) h) hT.le
    linarith
  have hufa : us - δ < uf := by
    by_contra h
    rw [not_lt] at h
    have h1 := mul_le_mul_of_nonneg_left (hanti uf (us - δ) hluf h) hT.le
    linarith
  refine ⟨s, δ, hs0, by rw [hss, hκ], hTs, hδs, hδ0, by rw [← hκ]; exact hδκ,
    by rw [← hκ]; exact hwκ,
    by rw [← hκ]; exact hκ2, ?_, h3l⟩
  rw [abs_le]; constructor <;> linarith

/-- The perturbation of the root of `T r_2(u) = 1` (proof of Lemma 4.1 [CVtG]): for a density `ρ`
supported left of `E` with `r_j(E + κ) ∼ κ^{3/2-j}` (`j = 2, 3, 4`, `κ ≤ 1`), moments `m_j` with
`|m_j - r_j|(u - E)^j ≤ K e` on the window `w ≤ u - E ≤ 1`, `m_2` decreasing right of `l ≤ E + w`,
the roots `T r_2(u_*) = 1` and `T m_2(u_fc) = 1`, and the three smallness conditions, the edges
`u + T m_1(u)` differ by at most `50 K K₁⁴ e / T`, `r_3(u_*) > 0`, and
`|m_3(u_fc) - r_3(u_*)| ≤ 1544 K K₁⁶ e T^{-3} r_3(u_*)`. -/
private lemma FcClose_core {ρ : ℝ → ℝ} {E : ℝ} (hd : FcClose_Dens ρ E) (m : ℕ → ℝ → ℝ)
    {K K₁ T e w l us uf : ℝ} (hK : 0 < K) (hK₁ : 1 ≤ K₁) (hT : 0 < T) (he : 0 < e)
    (hw : 0 < w)
    (hedge : ∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      1 ≤ K₁ * (Real.sqrt κ ^ (2 * j - 3) * FcClose_r ρ j (E + κ)) ∧
        Real.sqrt κ ^ (2 * j - 3) * FcClose_r ρ j (E + κ) ≤ K₁)
    (hrig : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ u : ℝ, w ≤ u - E → u - E ≤ 1 →
      |m j u - FcClose_r ρ j u| * (u - E) ^ j ≤ K * e)
    (hanti : ∀ u v : ℝ, l < u → u ≤ v → m 2 v ≤ m 2 u)
    (hl : l ≤ E + w) (hus : E < us) (hr2 : T * FcClose_r ρ 2 us = 1) (hluf : l < uf)
    (hm2 : T * m 2 uf = 1)
    (hS2 : K₁ ^ 2 * T ^ 2 ≤ 1 / 2) (hS3 : 4 * w * K₁ ^ 2 ≤ T ^ 2)
    (hS4 : 32 * K * K₁ ^ 4 * e ≤ T ^ 3) :
    |(uf + T * m 1 uf) - (us + T * FcClose_r ρ 1 us)| ≤ 50 * K * K₁ ^ 4 * e / T ∧
      0 < FcClose_r ρ 3 us ∧
      |m 3 uf - FcClose_r ρ 3 us| ≤ 1544 * K * K₁ ^ 6 * (e / T ^ 3) * FcClose_r ρ 3 us := by
  obtain ⟨s, δ, hs0, hss, hTs, hδs, hδ0, hδκ, hwκ, hκ2, hdu, h3l⟩ :=
    FcClose_loc hd m hK hK₁ hT he hw hedge
      (fun u h1 h2 => hrig 2 (by norm_num) (by norm_num) u h1 h2)
      hanti hl hus hr2 hluf hm2 hS2 hS3 hS4
  have hK₁0 : 0 < K₁ := by linarith
  have hdu' := abs_le.1 hdu
  have hf1 : (us - E) / 2 ≤ uf - E := by linarith
  have hf2 : uf - E ≤ 3 * (us - E) / 2 := by linarith
  have hfw : w ≤ uf - E := by linarith
  have hf1' : uf - E ≤ 1 := by linarith
  have ha1 : (us - E) / 2 ≤ us - δ - E := by linarith
  have hEa : E < us - δ := by linarith
  have hσa := FcClose_sqrt_ge hs0.le (show s ^ 2 / 4 ≤ us - δ - E by rw [hss]; linarith)
  obtain ⟨h2al, h2a⟩ := hedge 2 le_rfl (by norm_num) (us - δ - E) (by linarith) (by linarith)
  rw [show E + (us - δ - E) = us - δ by ring, show (2 * 2 - 3 : ℕ) = 1 from rfl, pow_one]
    at h2al h2a
  obtain ⟨h4al, h4a⟩ := hedge 4 (by norm_num) le_rfl (us - δ - E) (by linarith) (by linarith)
  rw [show E + (us - δ - E) = us - δ by ring, show (2 * 4 - 3 : ℕ) = 5 from rfl] at h4al h4a
  have hr2a0 := FcClose_nonneg hK₁0.le (Real.sqrt_nonneg _) h2al
  have hr4a0 := FcClose_nonneg hK₁0.le (by positivity) h4al
  have hr2a : s * FcClose_r ρ 2 (us - δ) ≤ 2 * K₁ := by
    have : s / 2 * FcClose_r ρ 2 (us - δ) ≤ Real.sqrt (us - δ - E) * FcClose_r ρ 2 (us - δ) :=
      mul_le_mul_of_nonneg_right hσa hr2a0
    linarith
  have hr4a : s ^ 5 * FcClose_r ρ 4 (us - δ) ≤ 32 * K₁ := by
    have h1 : (s / 2) ^ 5 ≤ Real.sqrt (us - δ - E) ^ 5 := pow_le_pow_left₀ (by positivity) hσa 5
    have : (s / 2) ^ 5 * FcClose_r ρ 4 (us - δ) ≤
        Real.sqrt (us - δ - E) ^ 5 * FcClose_r ρ 4 (us - δ) :=
      mul_le_mul_of_nonneg_right h1 hr4a0
    have e1 : (s / 2) ^ 5 * FcClose_r ρ 4 (us - δ) = s ^ 5 * FcClose_r ρ 4 (us - δ) / 32 := by ring
    linarith
  have hm1 := hrig 1 le_rfl (by norm_num) uf hfw hf1'
  have hm3 := hrig 3 (by norm_num) le_rfl uf hfw hf1'
  rw [pow_one] at hm1
  have hl1 := FcClose_lip1 hd hEa (show us - δ ≤ uf by linarith) (show us - δ ≤ us by linarith)
  have hl3 := FcClose_lip3 hd hEa (show us - δ ≤ uf by linarith) (show us - δ ≤ us by linarith)
  have hR3 : 0 < FcClose_r ρ 3 us := by
    have h0 := FcClose_nonneg hK₁0.le (by positivity) h3l
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero, mul_zero] at h3l; linarith
  refine ⟨?_, hR3, ?_⟩
  · have hY : |m 1 uf - FcClose_r ρ 1 uf| * s ^ 2 ≤ 2 * (K * e) := by
      have : |m 1 uf - FcClose_r ρ 1 uf| * s ^ 2 ≤ |m 1 uf - FcClose_r ρ 1 uf| * (2 * (uf - E)) :=
        mul_le_mul_of_nonneg_left (by rw [hss]; linarith) (abs_nonneg _)
      linarith
    have hZ : |FcClose_r ρ 1 uf - FcClose_r ρ 1 us| * s ≤ δ * (2 * K₁) := by
      calc |FcClose_r ρ 1 uf - FcClose_r ρ 1 us| * s
          ≤ |uf - us| * FcClose_r ρ 2 (us - δ) * s := mul_le_mul_of_nonneg_right hl1 hs0.le
        _ = |uf - us| * (s * FcClose_r ρ 2 (us - δ)) := by ring
        _ ≤ δ * (2 * K₁) := mul_le_mul hdu hr2a (by positivity) hδ0.le
    have htri : |(uf + T * m 1 uf) - (us + T * FcClose_r ρ 1 us)| ≤
        |uf - us| + T * |m 1 uf - FcClose_r ρ 1 uf| +
          T * |FcClose_r ρ 1 uf - FcClose_r ρ 1 us| := by
      have e1 : (uf + T * m 1 uf) - (us + T * FcClose_r ρ 1 us) =
          (uf - us) + T * (m 1 uf - FcClose_r ρ 1 uf) +
            T * (FcClose_r ρ 1 uf - FcClose_r ρ 1 us) := by ring
      rw [e1]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
      · rw [abs_mul, abs_of_pos hT]
      · rw [abs_mul, abs_of_pos hT]
    exact htri.trans (FcClose_edge_arith hT hs0 hK he hK₁ hTs hδs hdu hY hZ)
  · have hY : |m 3 uf - FcClose_r ρ 3 uf| * s ^ 6 ≤ 8 * (K * e) := by
      have h1 : s ^ 6 ≤ 8 * (uf - E) ^ 3 := by
        have : ((us - E) / 2) ^ 3 ≤ (uf - E) ^ 3 := pow_le_pow_left₀ (by positivity) hf1 3
        rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hss]
        linarith
      calc |m 3 uf - FcClose_r ρ 3 uf| * s ^ 6
          ≤ |m 3 uf - FcClose_r ρ 3 uf| * (8 * (uf - E) ^ 3) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = 8 * (|m 3 uf - FcClose_r ρ 3 uf| * (uf - E) ^ 3) := by ring
        _ ≤ 8 * (K * e) := by linarith
    have hZ : |FcClose_r ρ 3 uf - FcClose_r ρ 3 us| * s ^ 6 ≤ 1536 * K * K₁ ^ 2 * e := by
      calc |FcClose_r ρ 3 uf - FcClose_r ρ 3 us| * s ^ 6
          ≤ 3 * |uf - us| * FcClose_r ρ 4 (us - δ) * s ^ 6 :=
            mul_le_mul_of_nonneg_right hl3 (by positivity)
        _ = 3 * (|uf - us| * s) * (s ^ 5 * FcClose_r ρ 4 (us - δ)) := by ring
        _ ≤ 3 * (δ * s) * (32 * K₁) := by
            gcongr
        _ = 1536 * K * K₁ ^ 2 * e := by rw [hδs]; ring
    have htri : |m 3 uf - FcClose_r ρ 3 us| ≤
        |m 3 uf - FcClose_r ρ 3 uf| + |FcClose_r ρ 3 uf - FcClose_r ρ 3 us| := by
      have e1 : m 3 uf - FcClose_r ρ 3 us =
          (m 3 uf - FcClose_r ρ 3 uf) + (FcClose_r ρ 3 uf - FcClose_r ρ 3 us) := by ring
      rw [e1]; exact abs_add_le _ _
    exact htri.trans (FcClose_mom3_arith hT hs0 hK he hK₁ hTs hY hZ h3l)

/-! ## Rescaling, the eigenvalue moments and the law -/

/-- `rhoMom Λ c j ξ = c^j rhoMom Λ 1 j (cξ)` for `c > 0` (substitution `y = cx`). -/
private lemma FcClose_rhoMom_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    {c : ℝ} (hc : 0 < c) (j : ℕ) (ξ : ℝ) :
    rhoMom Λ c j ξ = c ^ j * FcClose_r (rho Λ) j (c * ξ) := by
  have h1 : rhoMom Λ c j ξ = ∫ x, (fun y => c * rho Λ y / (ξ - y / c) ^ j) (c * x) := by
    rw [rhoMom]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_div_cancel_left₀ x hc.ne']
  have h2 : ∀ y : ℝ, c * rho Λ y / (ξ - y / c) ^ j =
      c * c ^ j * (rho Λ y / (c * ξ - y) ^ j) := fun y => by
    have : ξ - y / c = (c * ξ - y) / c := by field_simp
    rw [this, div_pow, div_div_eq_mul_div]
    ring
  rw [h1, Measure.integral_comp_mul_left (fun y => c * rho Λ y / (ξ - y / c) ^ j) c,
    abs_of_pos (inv_pos.2 hc), smul_eq_mul]
  simp only [h2]
  rw [integral_const_mul, FcClose_r]
  field_simp

/-- `rhoMom Λ 1 j u = ∫ ρ_Λ(x) (u - x)^{-j} dx`. -/
private lemma FcClose_rhoMom_one {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (j : ℕ) (u : ℝ) : rhoMom Λ 1 j u = FcClose_r (rho Λ) j u := by
  simp [rhoMom, FcClose_r]

/-- The density `ρ_N` of (2.19) [eq:density_rhoN] for `‖Λ‖ ≤ 1/10` is a continuous probability
density vanishing on `[E⁺, ∞)`. -/
private lemma FcClose_dens {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    FcClose_Dens (rho Λ) (Eplus Λ) := by
  obtain ⟨h0, hc, hi, hm, -⟩ := rho_stieltjes Λ hΛ hℓ
  obtain ⟨-, hs⟩ := rho_support Λ hΛ hℓ
  refine ⟨h0, hc, hi, hm, fun x hx => ?_⟩
  have : x ∉ Function.support (rho Λ) := by
    rw [hs]; exact fun h => absurd h.2 (not_lt.2 hx)
  simpa [Function.mem_support] using this

/-- `V = e^{-𝔱/2} H + Λ = c⁻¹ (H + cΛ)` with `c = e^{𝔱/2}`, and `cΛ` the interaction of the
coupling `cA` (proof of Lemma 4.1 [CVtG]). -/
private lemma FcClose_edgeV (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ct : ℝ)
    (w : Fin D → Coords N) :
    edgeV D N A ct w = (((Real.exp (edgeTime N ct / 2) : ℝ) : ℂ))⁻¹ •
      HLam D N (((Real.exp (edgeTime N ct / 2) : ℝ) : ℂ) • A) w := by
  have hc : ((Real.exp (edgeTime N ct / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  unfold edgeV HLam
  rw [← lam_smul, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
  congr 2
  rw [show -edgeTime N ct / 2 = -(edgeTime N ct / 2) by ring, Real.exp_neg, Complex.ofReal_inv]

/-- `‖cA‖ = c ‖A‖` for `c > 0`. -/
private lemma FcClose_opNorm_smul {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    {c : ℝ} (hc : 0 < c) : opNorm ((c : ℂ) • A) = c * opNorm A := by
  simp only [opNorm]
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

/-- The eigenvalues are at most `λ_1`. -/
private lemma FcClose_eigs_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (i : Fin (Fintype.card ι)) : eigs X i ≤ eigK X 1 := by
  have h0 : 0 < Fintype.card ι := Fintype.card_pos
  have e : eigK X 1 = eigs X ⟨0, h0⟩ := by
    unfold eigK; simp [h0]
  have e2 : eigs X = hX.eigenvalues₀ := by simp [eigs, hX]
  rw [e, e2]
  exact hX.eigenvalues₀_antitone (Fin.zero_le _)

/-- `ξ ↦ ⟨(ξ - X)^{-2}⟩` decreases to the right of `λ_1`. -/
private lemma FcClose_mom2_anti {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {u v : ℝ} (hu : eigK X 1 < u) (huv : u ≤ v) :
    fcMom X 2 v ≤ fcMom X 2 u := by
  unfold fcMom
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine Finset.sum_le_sum fun i _ => ?_
  have := FcClose_eigs_le X hX i
  exact one_div_le_one_div_of_le (pow_pos (by linarith) 2)
    (pow_le_pow_left₀ (by linarith) (by linarith) 2)

/-- The block matrix `H` of (1.3) [matrix_H], as an array, is a measurable function of the
coordinates. -/
private lemma FcClose_measurable_blockH (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  change Measurable fun w : Fin D → Coords N => blockH D N w p q
  unfold blockH
  by_cases h : p.1 = q.1
  · simp only [h, ↓reduceIte]
    unfold wig
    by_cases h1 : p.2 = q.2
    · simp only [h1, ite_true]
      exact measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_pi_apply q.2).comp (measurable_fst.comp (measurable_pi_apply q.1))))
    · by_cases h2 : p.2 < q.2
      · simp only [h1, h2, ite_true, ite_false]
        exact measurable_const.mul ((measurable_pi_apply q.2).comp ((measurable_pi_apply p.2).comp
          (measurable_snd.comp (measurable_pi_apply q.1))))
      · simp only [h1, h2, ite_false]
        exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
          ((measurable_pi_apply p.2).comp ((measurable_pi_apply q.2).comp
            (measurable_snd.comp (measurable_pi_apply q.1)))))
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- `|Q^{-1/3} - P^{-1/3}| ≤ 2 r P^{-1/3}` for `P > 0`, `|Q - P| ≤ r P` and `r ≤ 1/2`. -/
private lemma FcClose_gam {P Q r : ℝ} (hP : 0 < P) (hr : r ≤ 1 / 2) (h : |Q - P| ≤ r * P) :
    |Q ^ (-(1 / 3 : ℝ)) - P ^ (-(1 / 3 : ℝ))| ≤ 2 * r * P ^ (-(1 / 3 : ℝ)) := by
  have hr0 : 0 ≤ r := by
    have := (abs_nonneg (Q - P)).trans h
    exact nonneg_of_mul_nonneg_left this hP
  have hQ : P / 2 ≤ Q := by
    have := (abs_le.1 h).1
    nlinarith
  have hQ0 : 0 < Q := by linarith
  have hcube : ∀ x : ℝ, 0 < x → (x ^ (-(1 / 3 : ℝ))) ^ 3 = x⁻¹ := fun x hx => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    exact Real.rpow_neg_one x
  obtain ⟨a, ha⟩ : ∃ a, a = Q ^ (-(1 / 3 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = P ^ (-(1 / 3 : ℝ)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos hQ0 _
  have hb0 : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos hP _
  rw [← ha, ← hb]
  have ha3 : a ^ 3 = Q⁻¹ := by rw [ha]; exact hcube Q hQ0
  have hb3 : b ^ 3 = P⁻¹ := by rw [hb]; exact hcube P hP
  have key : (a - b) * (a ^ 2 + a * b + b ^ 2) = (P - Q) / (P * Q) := by
    rw [show (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 by ring, ha3, hb3]
    field_simp
  have h1 : |a - b| * b ^ 2 ≤ |a - b| * (a ^ 2 + a * b + b ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_pos ha0 hb0]) (abs_nonneg _)
  have h2 : |a - b| * (a ^ 2 + a * b + b ^ 2) = |P - Q| / (P * Q) := by
    rw [← abs_of_pos (show 0 < a ^ 2 + a * b + b ^ 2 by positivity), ← abs_mul, key, abs_div,
      abs_of_pos (mul_pos hP hQ0)]
  have h3 : |P - Q| / (P * Q) ≤ r * a ^ 3 := by
    rw [ha3, abs_sub_comm, div_le_iff₀ (mul_pos hP hQ0)]
    calc |Q - P| ≤ r * P := h
      _ = r * Q⁻¹ * (P * Q) := by field_simp
  have h4 : a ^ 3 ≤ 2 * b ^ 3 := by
    rw [ha3, hb3]
    rw [inv_le_iff_one_le_mul₀ hQ0]
    have : 2 * P⁻¹ * Q = 2 * Q / P := by field_simp
    rw [this, le_div_iff₀ hP]
    linarith
  have h5 : |a - b| * b ^ 2 ≤ 2 * r * b * b ^ 2 := by
    calc |a - b| * b ^ 2 ≤ r * a ^ 3 := by linarith
      _ ≤ r * (2 * b ^ 3) := mul_le_mul_of_nonneg_left h4 hr0
      _ = 2 * r * b * b ^ 2 := by ring
  exact le_of_mul_le_mul_right h5 (by positivity)

/-- `B ≤ N^a` for all large `N`, when `a > 0`. -/
private lemma FcClose_ev_ge (B a : ℝ) (ha : 0 < a) : ∀ᶠ N : ℕ in atTop, B ≤ (N : ℝ) ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- `N^{-a} ≤ b` for all large `N`, when `a, b > 0`. -/
private lemma FcClose_ev_le (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-a) ≤ b :=
  ((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hb)

/-- `B n^b ≤ n^{a+b}` from `B ≤ n^a`, `n > 0`. -/
private lemma FcClose_rpow_le {n B a b : ℝ} (hn : 0 < n) (h : B ≤ n ^ a) :
    B * n ^ b ≤ n ^ (a + b) := by
  rw [Real.rpow_add hn]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hn.le _)

/-- `κ^{3/2-j} = 1/(√κ)^{2j-3}` for `κ > 0`, `j ≥ 2`. -/
private lemma FcClose_rpow_sqrt {κ : ℝ} (hκ : 0 < κ) {j : ℕ} (hj : 2 ≤ j) :
    κ ^ ((3 / 2 : ℝ) - j) = 1 / Real.sqrt κ ^ (2 * j - 3) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hκ.le, one_div,
    ← Real.rpow_neg hκ.le]
  congr 1
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- `K₁² T² ≤ 1/2` from `T ≤ 2𝔱` and `𝔱 ≤ 1/(3K₁)`. -/
private lemma FcClose_S2 {K₁ T 𝔱 : ℝ} (hK₁ : 0 < K₁) (hT : 0 < T) (hT2 : T ≤ 2 * 𝔱)
    (h𝔱 : 𝔱 ≤ 1 / (3 * K₁)) : K₁ ^ 2 * T ^ 2 ≤ 1 / 2 := by
  have h0 : K₁ * 𝔱 ≤ 1 / 3 := by
    rw [le_div_iff₀ (by positivity)] at h𝔱
    linarith
  have h1 : K₁ * T ≤ 2 / 3 := by
    have := mul_le_mul_of_nonneg_left hT2 hK₁.le
    linarith
  have h2 : 0 ≤ K₁ * T := by positivity
  have h3 : (K₁ * T) ^ 2 ≤ (2 / 3) ^ 2 := pow_le_pow_left₀ h2 h1 2
  rw [mul_pow] at h3
  linarith

/-- The bound of `fcMom_rigid` in product form: `|x| d^j ≤ K (N^{τ'} N^{-1})`. -/
private lemma FcClose_rig_conv {x K a b d : ℝ} {j : ℕ} (hd : 0 < d)
    (h : |x| ≤ K * a * (b * d ^ (-(j : ℝ)))) : |x| * d ^ j ≤ K * (a * b) := by
  rw [Real.rpow_neg hd.le, Real.rpow_natCast] at h
  have hp : 0 < d ^ j := pow_pos hd j
  calc |x| * d ^ j ≤ K * a * (b * (d ^ j)⁻¹) * d ^ j := mul_le_mul_of_nonneg_right h hp.le
    _ = K * (a * b) := by field_simp

/-- The top eigenvalue from rigidity at `k = 1` and `γ_1 ≤ E⁺`: `λ_1 ≤ E⁺ + w`. -/
private lemma FcClose_top {l q E w a b : ℝ} (h1 : |l - q| ≤ a * (b * 1)) (h2 : q ≤ E)
    (h3 : a * b ≤ w) : l ≤ E + w := by
  have := (abs_le.1 h1).2
  linarith

/-- The two bounds of Lemma 4.1 [CVtG] on the free-convolution data, deterministically: for
Hermitian `X` whose moments satisfy the comparison with `ρ_N` of `Λ' = cΛ` on the window, with
`λ_1(X) ≤ E⁺(Λ') + w` and the smallness conditions, `V = c⁻¹ X` has
`|E_fc - E⁺(Λ)| ≤ η_E` and `|γ_fc - γ₊(Λ)| ≤ η_G`, where `t' = 1 - c^{-2}`. -/
private lemma FcClose_det {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ Λ' X : Matrix ι ι ℂ) (hX : X.IsHermitian) (hΛh : Λ.IsHermitian)
    (hΛn : opNorm Λ ≤ 1 / 10) (hΛ'h : Λ'.IsHermitian) (hΛ'n : opNorm Λ' ≤ 1 / 10)
    {c t' T K K₁ e w ηE ηG : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (hΛΛ' : (c : ℂ) • Λ = Λ')
    (hct : 1 - c⁻¹ ^ 2 = t') (hT : T = t' * c ^ 2) (hK : 0 < K) (hK₁ : 1 ≤ K₁) (he : 0 < e)
    (hw : 0 < w)
    (hedge : ∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      1 ≤ K₁ * (Real.sqrt κ ^ (2 * j - 3) * FcClose_r (rho Λ') j (Eplus Λ' + κ)) ∧
        Real.sqrt κ ^ (2 * j - 3) * FcClose_r (rho Λ') j (Eplus Λ' + κ) ≤ K₁)
    (hrig : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ u : ℝ, w ≤ u - Eplus Λ' → u - Eplus Λ' ≤ 1 →
      |fcMom X j u - FcClose_r (rho Λ') j u| * (u - Eplus Λ') ^ j ≤ K * e)
    (hl : eigK X 1 ≤ Eplus Λ' + w)
    (hS2 : K₁ ^ 2 * T ^ 2 ≤ 1 / 2) (hS3 : 4 * w * K₁ ^ 2 ≤ T ^ 2)
    (hS4 : 32 * K * K₁ ^ 4 * e ≤ T ^ 3)
    (hfinE : 50 * K * K₁ ^ 4 * e / T ≤ ηE)
    (hfinG : 4 * (1544 * K * K₁ ^ 6 * (e / T ^ 3)) ≤ ηG) (hηG : ηG ≤ 1) :
    |fcEdge (((c : ℂ))⁻¹ • X) t' - Eplus Λ| ≤ ηE ∧
      |fcGamma (((c : ℂ))⁻¹ • X) t' - gammaPlus Λ| ≤ ηG := by
  have hc0 : 0 < c := by linarith
  have ht'0 : 0 < t' := by
    rw [← hct]
    have h1 : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc1
    have h2 : 0 < c⁻¹ := inv_pos.2 hc0
    nlinarith
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨ξs, hs1, hs2, hs3, hs4⟩ := fcDet_eq Λ hΛh c hc1 hc2 (by rw [hΛΛ']; exact hΛ'n)
  rw [hΛΛ'] at hs1 hs2 hs3 hs4
  rw [hct] at hs2 hs3 hs4
  rw [FcClose_rhoMom_smul _ hc0] at hs2 hs3 hs4
  have hd := FcClose_dens Λ' hΛ'h hΛ'n
  have hus : Eplus Λ' < c * ξs := by
    have := mul_lt_mul_of_pos_left hs1 hc0
    rwa [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] at this
  have hr2 : T * FcClose_r (rho Λ') 2 (c * ξs) = 1 := by
    rw [hT]; linear_combination hs2
  have hcinv : ((c : ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hV : (((c : ℂ))⁻¹ • X).IsHermitian := by
    rw [hcinv]; exact hX.smul (by simp [IsSelfAdjoint])
  obtain ⟨hf1, hf2, -⟩ := fcXi_spec _ hV t' ht'0
  obtain ⟨ξf, hξf⟩ : ∃ ξf, ξf = fcXi (((c : ℂ))⁻¹ • X) t' := ⟨_, rfl⟩
  rw [← hξf] at hf1 hf2
  have heig : eigK (((c : ℂ))⁻¹ • X) 1 = c⁻¹ * eigK X 1 := by
    rw [hcinv]; exact eigK_smul X hX c⁻¹ (inv_pos.2 hc0) 1
  have hmom : ∀ j ξ, fcMom (((c : ℂ))⁻¹ • X) j ξ = c ^ j * fcMom X j (c * ξ) :=
    fun j ξ => fcMom_smul X hX c hc0 j ξ
  rw [hmom] at hf2
  rw [heig] at hf1
  have hluf : eigK X 1 < c * ξf := by
    have := mul_lt_mul_of_pos_left hf1 hc0
    rwa [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] at this
  have hm2 : T * fcMom X 2 (c * ξf) = 1 := by rw [hT]; linear_combination hf2
  have hanti : ∀ u v : ℝ, eigK X 1 < u → u ≤ v → fcMom X 2 v ≤ fcMom X 2 u :=
    fun u v hu huv => FcClose_mom2_anti X hX hu huv
  obtain ⟨hEb, hR3, hM3⟩ := FcClose_core hd (fun j u => fcMom X j u) hK hK₁ hT0 he hw
    hedge hrig hanti hl hus hr2 hluf hm2 hS2 hS3 hS4
  constructor
  · have e1 : c * (fcEdge (((c : ℂ))⁻¹ • X) t' - Eplus Λ) =
        (c * ξf + T * fcMom X 1 (c * ξf)) -
          (c * ξs + T * FcClose_r (rho Λ') 1 (c * ξs)) := by
      rw [fcEdge, ← hξf, hmom, hs3, hT]; ring
    have h1 : |fcEdge (((c : ℂ))⁻¹ • X) t' - Eplus Λ| ≤
        |c * (fcEdge (((c : ℂ))⁻¹ • X) t' - Eplus Λ)| := by
      rw [abs_mul, abs_of_pos hc0]
      exact le_mul_of_one_le_left (abs_nonneg _) hc1.le
    rw [e1] at h1
    exact (h1.trans hEb).trans hfinE
  · set r' := 1544 * K * K₁ ^ 6 * (e / T ^ 3) with hr'
    have hr'0 : 0 ≤ r' := by positivity
    have hr'2 : r' ≤ 1 / 2 := by linarith
    have hc3p : 0 < c ^ 3 := by positivity
    have hP : 0 < c ^ 3 * FcClose_r (rho Λ') 3 (c * ξs) := mul_pos hc3p hR3
    have hQP : |c ^ 3 * fcMom X 3 (c * ξf) - c ^ 3 * FcClose_r (rho Λ') 3 (c * ξs)| ≤
        r' * (c ^ 3 * FcClose_r (rho Λ') 3 (c * ξs)) := by
      rw [← mul_sub, abs_mul, abs_of_pos hc3p]
      calc c ^ 3 * |fcMom X 3 (c * ξf) - FcClose_r (rho Λ') 3 (c * ξs)|
          ≤ c ^ 3 * (r' * FcClose_r (rho Λ') 3 (c * ξs)) :=
            mul_le_mul_of_nonneg_left hM3 hc3p.le
        _ = _ := by ring
    have hg := FcClose_gam hP hr'2 hQP
    have hγ2 : gammaPlus Λ ≤ 2 := (def_gamma_limits Λ hΛh hΛn).2.2.2.1
    unfold fcGamma
    rw [← hξf, hmom, hs4, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 ht'0)]
    rw [hs4] at hγ2
    calc t'⁻¹ * |(c ^ 3 * fcMom X 3 (c * ξf)) ^ (-(1 / 3 : ℝ)) -
            (c ^ 3 * FcClose_r (rho Λ') 3 (c * ξs)) ^ (-(1 / 3 : ℝ))|
        ≤ t'⁻¹ * (2 * r' * (c ^ 3 * FcClose_r (rho Λ') 3 (c * ξs)) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hg (inv_pos.2 ht'0).le
      _ = 2 * r' * (t'⁻¹ * (c ^ 3 * FcClose_r (rho Λ') 3 (c * ξs)) ^ (-(1 / 3 : ℝ))) := by
          ring
      _ ≤ 2 * r' * 2 := mul_le_mul_of_nonneg_left hγ2 (by positivity)
      _ ≤ ηG := by linarith

/-- The bounds of `rhoMom_edge` in product form: `1 ≤ K₁ σ r` and `σ r ≤ K₁` from
`K₀⁻¹/σ ≤ r ≤ K₀/σ`, `K₀ ≤ K₁`. -/
private lemma FcClose_edge_conv {K₀ K₁ σ r : ℝ} (hK₀ : 0 < K₀) (hK₀₁ : K₀ ≤ K₁) (hσ : 0 < σ)
    (hlo : K₀⁻¹ * (1 / σ) ≤ r) (hhi : r ≤ K₀ * (1 / σ)) :
    1 ≤ K₁ * (σ * r) ∧ σ * r ≤ K₁ := by
  have h1 : 1 ≤ K₀ * (σ * r) := by
    have := mul_le_mul_of_nonneg_left hlo (show 0 ≤ K₀ * σ by positivity)
    have e1 : K₀ * σ * (K₀⁻¹ * (1 / σ)) = 1 := by field_simp
    rw [e1] at this; linarith
  have hr0 : 0 ≤ σ * r := FcClose_nonneg hK₀.le zero_le_one (by rw [one_mul]; exact h1)
  have h2 : σ * r ≤ K₀ := by
    have := mul_le_mul_of_nonneg_left hhi hσ.le
    have e1 : σ * (K₀ * (1 / σ)) = K₀ := by field_simp
    rw [e1] at this; exact this
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hK₀₁ hr0), h2.trans hK₀₁⟩

/-- The comparison of the free-convolution data with `E⁺` and `γ₊` in the proof of Lemma 4.1
[CVtG] (after [CorrelatedBandAOP, Section 6.1]): for `𝔠 ∈ (0, 1/10)`, `𝔱 = N^{-1/3+𝔠}`,
`V = e^{-𝔱/2} H + Λ`, `t' = 1 - e^{-𝔱}` and `ε ∈ (0, 𝔠)`, outside an event of probability
`≤ N^{-D'}`, `|E_fc - E⁺| ≤ N^{-2/3-ε}` and `|γ_fc - γ₊| ≤ N^{-ε}`. -/
theorem fc_close (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) (ct : ℝ)
    (hct : 0 < ct) (hct' : ct < 1 / 10) (ε : ℝ) (hε : 0 < ε) (hεc : ε < ct) :
    ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      blockLaw D N L {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - ε) <
          |fcEdge (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - Eplus (lam D N A)| ∨
        (N : ℝ) ^ (-ε) <
          |fcGamma (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - gammaPlus (lam D N A)|} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro D' hD'
  obtain ⟨K, hK, hrigK⟩ := fcMom_rigid D hD (δA / 2) (by linarith)
  obtain ⟨K₀, hK₀, hedgeK⟩ := rhoMom_edge
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = max K₀ 1 := ⟨_, rfl⟩
  have hK₁1 : 1 ≤ K₁ := by rw [hK₁]; exact le_max_right _ _
  have hK₀₁ : K₀ ≤ K₁ := by rw [hK₁]; exact le_max_left _ _
  have hK₁0 : 0 < K₁ := by linarith
  obtain ⟨cg, Cg, hcg, hCg, Nk, hNk⟩ := kappa_gamma_k D hD (δA / 2) (by linarith)
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ℝ, τ' = (ct - ε) / 4 := ⟨_, rfl⟩
  have hτ0 : 0 < τ' := by rw [hτ']; linarith
  have hτ1 : τ' ≤ 1 / 10 := by rw [hτ']; linarith
  obtain ⟨N₁, hN₁⟩ := hrigK τ' hτ0 hτ1
  obtain ⟨N₂, hN₂⟩ := rigidity D (by omega) (δA / 2) (by linarith) C τ' hτ0 D' hD'
  have hev := (eventually_ge_atTop 2).and
    ((FcClose_ev_le (1 / (3 * K₁)) (1 / 3 - ct) (by positivity) (by linarith)).and
    ((FcClose_ev_le (1 / 2) (δA / 2) (by norm_num) (by linarith)).and
    ((FcClose_ev_le (1 / 40) δA (by norm_num) hδA).and
    ((FcClose_ev_ge (4 * K₁ ^ 2) (2 * ct - 2 * τ') (by rw [hτ']; linarith)).and
    ((FcClose_ev_ge (32 * K * K₁ ^ 4) (3 * ct - τ') (by rw [hτ']; linarith)).and
    ((FcClose_ev_ge (50 * K * K₁ ^ 4) (ct - τ' - ε) (by rw [hτ']; linarith)).and
    (FcClose_ev_ge (4 * (1544 * K * K₁ ^ 6)) (3 * ct - τ' - ε) (by rw [hτ']; linarith))))))))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 hev
  refine ⟨max (max N₁ N₂) (max Nk N₃), fun N hN L A hA => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN1, hN2⟩, hNk', hN3⟩ := hN
  obtain ⟨hNtwo, h𝔱s, hδh, hδ40, hc3, hc4, hc5, hc6⟩ := hN₃ N hN3
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have hDN : 1 ≤ D * N := by nlinarith
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  -- the time, the scale `c = e^{𝔱/2}` and `t' = 1 - e^{-𝔱}`
  obtain ⟨𝔱, h𝔱⟩ : ∃ 𝔱, 𝔱 = edgeTime N ct := ⟨_, rfl⟩
  have h𝔱' : 𝔱 = (N : ℝ) ^ (-(1 / 3 : ℝ) + ct) := by rw [h𝔱]; rfl
  have h𝔱0 : 0 < 𝔱 := by rw [h𝔱']; positivity
  have h𝔱K : 𝔱 ≤ 1 / (3 * K₁) := by
    rw [h𝔱', show -(1 / 3 : ℝ) + ct = -(1 / 3 - ct) by ring]; exact h𝔱s
  have h𝔱1 : 𝔱 ≤ 1 / 3 := h𝔱K.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  obtain ⟨c, hc⟩ : ∃ c, c = Real.exp (𝔱 / 2) := ⟨_, rfl⟩
  have hc1 : 1 < c := by rw [hc]; exact Real.one_lt_exp_iff.2 (by linarith)
  have hc0 : 0 < c := by linarith
  have hc2 : c ≤ 2 := by
    have h1 := Real.abs_exp_sub_one_le (x := 𝔱 / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [abs_of_pos (by linarith : 0 < 𝔱 / 2)] at h1
    have h2 := (abs_le.1 h1).2
    rw [hc]; linarith
  obtain ⟨t', ht'⟩ : ∃ t', t' = 1 - Real.exp (-𝔱) := ⟨_, rfl⟩
  have hct : 1 - c⁻¹ ^ 2 = t' := by
    rw [hc, ht', ← Real.exp_neg, sq, ← Real.exp_add]
    congr 2; ring
  have ht'0 : 0 < t' := by rw [ht']; linarith [Real.exp_lt_one_iff.2 (show -𝔱 < 0 by linarith)]
  obtain ⟨T, hT⟩ : ∃ T, T = t' * c ^ 2 := ⟨_, rfl⟩
  have hTe : T = Real.exp 𝔱 - 1 := by
    rw [hT, ht', hc, sq, ← Real.exp_add, show 𝔱 / 2 + 𝔱 / 2 = 𝔱 by ring, sub_mul, one_mul,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h𝔱T : 𝔱 ≤ T := by rw [hTe]; linarith [Real.add_one_le_exp 𝔱]
  have hT0 : 0 < T := by linarith
  have hT2 : T ≤ 2 * 𝔱 := by
    have h1 := Real.abs_exp_sub_one_le (x := 𝔱) (by rw [abs_of_pos h𝔱0]; linarith)
    rw [abs_of_pos h𝔱0] at h1
    rw [hTe]; exact (le_abs_self _).trans h1
  -- the couplings `A' = cA`, `Λ = Λ(A)`, `Λ' = Λ(cA) = cΛ`
  obtain ⟨A', hA'⟩ : ∃ A', A' = ((c : ℝ) : ℂ) • A := ⟨_, rfl⟩
  have hδsplit : (N : ℝ) ^ (-δA) = (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(δA / 2)) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hNδ0 : 0 ≤ (N : ℝ) ^ (-(δA / 2)) := Real.rpow_nonneg hn0.le _
  have hA0 : 0 ≤ opNorm A := norm_nonneg _
  have hA'n : opNorm A' ≤ (N : ℝ) ^ (-(δA / 2)) := by
    rw [hA', FcClose_opNorm_smul A hc0]
    calc c * opNorm A ≤ 2 * (N : ℝ) ^ (-δA) := mul_le_mul hc2 hA hA0 (by norm_num)
      _ = 2 * (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(δA / 2)) := by rw [hδsplit]; ring
      _ ≤ 1 * (N : ℝ) ^ (-(δA / 2)) := by
          apply mul_le_mul_of_nonneg_right _ hNδ0; linarith
      _ = _ := one_mul _
  have hΛΛ' : ((c : ℝ) : ℂ) • lam D N A = lam D N A' := by rw [hA']; exact lam_smul D N A c
  have hΛ'h : (lam D N A').IsHermitian := lam_isHermitian D N A'
  have hΛh : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hΛ'n : opNorm (lam D N A') ≤ 1 / 10 := by
    have h1 := opNorm_lam_le D N A'
    have h2 : opNorm A' ≤ 2 * (N : ℝ) ^ (-δA) := by
      rw [hA', FcClose_opNorm_smul A hc0]; exact mul_le_mul hc2 hA hA0 (by norm_num)
    linarith
  have hΛn : opNorm (lam D N A) ≤ 1 / 10 := by
    have h1 := opNorm_lam_le D N A
    linarith
  obtain ⟨E, hE⟩ : ∃ E, E = Eplus (lam D N A') := ⟨_, rfl⟩
  have hedge : ∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      1 ≤ K₁ * (Real.sqrt κ ^ (2 * j - 3) * FcClose_r (rho (lam D N A')) j (E + κ)) ∧
        Real.sqrt κ ^ (2 * j - 3) * FcClose_r (rho (lam D N A')) j (E + κ) ≤ K₁ := by
    intro j hj2 hj4 κ hκ hκ1
    obtain ⟨hlo, hhi⟩ := hedgeK (Idx D N) (lam D N A') hΛ'h hΛ'n j hj2 hj4 κ hκ hκ1
    rw [FcClose_rpow_sqrt hκ hj2, FcClose_rhoMom_one, ← hE] at hlo hhi
    exact FcClose_edge_conv hK₀ hK₀₁ (pow_pos (Real.sqrt_pos.2 hκ) _) hlo hhi
  -- the rates
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (N : ℝ) ^ τ' * (N : ℝ) ^ (-(1 : ℝ)) := ⟨_, rfl⟩
  have he' : e = (N : ℝ) ^ (τ' + -1) := by rw [he, Real.rpow_add hn0]
  have he0 : 0 < e := by rw [he']; positivity
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * τ') := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have h𝔱2 : 𝔱 ^ 2 = (N : ℝ) ^ ((2 * ct - 2 * τ') + (-(2 / 3 : ℝ) + 2 * τ')) := by
    rw [sq, h𝔱', ← Real.rpow_add hn0]; congr 1; ring
  have h𝔱3 : 𝔱 ^ 3 = (N : ℝ) ^ ((3 * ct - τ') + (τ' + -1)) := by
    rw [show 𝔱 ^ 3 = 𝔱 * 𝔱 * 𝔱 by ring, h𝔱', ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; ring
  have hS2 := FcClose_S2 hK₁0 hT0 hT2 h𝔱K
  have hS3 : 4 * w * K₁ ^ 2 ≤ T ^ 2 := by
    have h1 := FcClose_rpow_le (b := -(2 / 3 : ℝ) + 2 * τ') hn0 hc3
    rw [← hw, ← h𝔱2] at h1
    have h2 : 𝔱 ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ h𝔱0.le h𝔱T 2
    linarith
  have hS4 : 32 * K * K₁ ^ 4 * e ≤ T ^ 3 := by
    have h1 := FcClose_rpow_le (b := τ' + -1) hn0 hc4
    rw [← he', ← h𝔱3] at h1
    have h2 : 𝔱 ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ h𝔱0.le h𝔱T 3
    linarith
  have hfinE : 50 * K * K₁ ^ 4 * e / T ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) - ε) := by
    have h2 : 50 * K * K₁ ^ 4 * e / T ≤ 50 * K * K₁ ^ 4 * e / 𝔱 :=
      div_le_div_of_nonneg_left (by positivity) h𝔱0 h𝔱T
    refine h2.trans ?_
    rw [div_le_iff₀ h𝔱0, h𝔱', ← Real.rpow_add hn0, he']
    have h3 := FcClose_rpow_le (b := τ' + -1) hn0 hc5
    rw [show ct - τ' - ε + (τ' + -1) = -(2 / 3 : ℝ) - ε + (-(1 / 3 : ℝ) + ct) by ring] at h3
    exact h3
  have hfinG : 4 * (1544 * K * K₁ ^ 6 * (e / T ^ 3)) ≤ (N : ℝ) ^ (-ε) := by
    have h2 : e / T ^ 3 ≤ e / 𝔱 ^ 3 :=
      div_le_div_of_nonneg_left he0.le (by positivity) (pow_le_pow_left₀ h𝔱0.le h𝔱T 3)
    have h3 : 4 * (1544 * K * K₁ ^ 6) * e ≤ (N : ℝ) ^ (-ε) * 𝔱 ^ 3 := by
      have h4 := FcClose_rpow_le (b := τ' + -1) hn0 hc6
      rw [he', h𝔱3, ← Real.rpow_add hn0]
      rw [show 3 * ct - τ' - ε + (τ' + -1) = -ε + (3 * ct - τ' + (τ' + -1)) by ring] at h4
      exact h4
    have h5 : 4 * (1544 * K * K₁ ^ 6) * (e / 𝔱 ^ 3) ≤ (N : ℝ) ^ (-ε) := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; exact h3
    calc 4 * (1544 * K * K₁ ^ 6 * (e / T ^ 3)) = 4 * (1544 * K * K₁ ^ 6) * (e / T ^ 3) := by
          ring
      _ ≤ 4 * (1544 * K * K₁ ^ 6) * (e / 𝔱 ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := h5
  have hNε : (N : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hγ1 : (N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ w := by
    rw [← Real.rpow_add hn0, hw]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  -- the deterministic consequence of rigidity
  have key : ∀ w' : Fin D → Coords N, IsRigid D N A' τ' (HLam D N A' w') →
      |fcEdge (edgeV D N A ct w') (1 - Real.exp (-edgeTime N ct)) - Eplus (lam D N A)| ≤
          (N : ℝ) ^ (-(2 / 3 : ℝ) - ε) ∧
        |fcGamma (edgeV D N A ct w') (1 - Real.exp (-edgeTime N ct)) - gammaPlus (lam D N A)| ≤
          (N : ℝ) ^ (-ε) := by
    intro w' hrig
    have hX : (HLam D N A' w').IsHermitian := HLam_isHermitian D N A' w'
    have hVX : edgeV D N A ct w' = ((c : ℂ))⁻¹ • HLam D N A' w' := by
      rw [FcClose_edgeV, ← h𝔱, ← hc, ← hA']
    rw [hVX, show 1 - Real.exp (-edgeTime N ct) = t' by rw [ht', h𝔱]]
    have hrig' : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ u : ℝ, w ≤ u - E → u - E ≤ 1 →
        |fcMom (HLam D N A' w') j u - FcClose_r (rho (lam D N A')) j u| * (u - E) ^ j ≤
          K * e := by
      intro j hj hj3 u hu1 hu2
      rw [hw] at hu1
      have h := hN₁ N hN1 A' hA'n _ hX hrig j hj hj3 u (by rw [← hE]; exact hu1)
        (by rw [← hE]; exact hu2)
      rw [FcClose_rhoMom_one, ← hE] at h
      rw [he]
      exact FcClose_rig_conv (lt_of_lt_of_le (by positivity) hu1) h
    have hl : eigK (HLam D N A' w') 1 ≤ E + w := by
      have h1 := hrig 1 le_rfl hDN
      rw [rk_one D N hDN, Real.one_rpow] at h1
      have h2 := (hNk N hNk' A' hA'n 1 le_rfl hDN).1
      rw [← hE] at h2
      have h3 : 0 ≤ cg * (((1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
        positivity
      exact FcClose_top h1 (by linarith) hγ1
    rw [hE] at hedge hrig' hl
    exact FcClose_det (lam D N A) (lam D N A') _ hX hΛh hΛn hΛ'h hΛ'n hc1 hc2 hΛΛ' hct hT hK
      hK₁1 he0 hw0 hedge hrig' hl hS2 hS3 hS4 hfinE hfinG hNε
  -- the probability bound
  have hS := hN₂ N hN2 1 zero_le_one le_rfl _ (llClass_blockH D N C L) A' hA'n
  refine le_trans (measure_mono ?_)
    ((Measure.le_map_apply (FcClose_measurable_blockH D N).aemeasurable _).trans hS)
  intro w' hw'
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  by_contra hne
  push Not at hne
  have hrig : IsRigid D N A' τ' (HLam D N A' w') := fun k hk1 hk2 => by
    have := hne k hk1 hk2
    rw [Equiv.apply_symm_apply] at this
    exact this
  obtain ⟨h1, h2⟩ := key w' hrig
  rcases hw' with h | h <;> linarith

end RBMTransitionEdge

end
