module

public import RBMTransitionEdge.Main.Statements
public import RBMTransitionEdge.Det.Density
public import RBMTransitionEdge.Det.Regular

@[expose] public section

/-!
# The quantile increment

The increment of `γ_i - γ_i^{sc}` over `|i - k| ≤ N^τ` behind the correlation comparison of
Theorem 2.5 [theorem_localized_eigenvalue].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section QIAlg
variable {ι : Type*} [Fintype ι]

/-- The normalized sum `n⁻¹ Σ_j f_j`. -/
private def QI_av (f : ι → ℝ) : ℝ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, f j

private lemma QI_av_mono {f g : ι → ℝ} (h : ∀ j, f j ≤ g j) : QI_av f ≤ QI_av g := by
  unfold QI_av
  gcongr with j
  exact h j

private lemma QI_card_pos [Nonempty ι] : (0 : ℝ) < Fintype.card ι := by
  exact_mod_cast Fintype.card_pos

private lemma QI_av_const [Nonempty ι] (a : ℝ) : QI_av (fun _ : ι => a) = a := by
  unfold QI_av
  have := (QI_card_pos (ι := ι)).ne'
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma QI_av_sub (f g : ι → ℝ) : QI_av (fun j => f j - g j) = QI_av f - QI_av g := by
  unfold QI_av
  rw [Finset.sum_sub_distrib]
  ring

private lemma QI_av_add (f g : ι → ℝ) : QI_av (fun j => f j + g j) = QI_av f + QI_av g := by
  unfold QI_av
  rw [Finset.sum_add_distrib]
  ring

private lemma QI_av_mul_left (a : ℝ) (f : ι → ℝ) :
    QI_av (fun j => a * f j) = a * QI_av f := by
  unfold QI_av
  rw [← Finset.mul_sum]
  ring

private lemma QI_abs_av (f : ι → ℝ) : |QI_av f| ≤ QI_av (fun j => |f j|) := by
  unfold QI_av
  rw [abs_mul, abs_of_nonneg (by positivity)]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

private lemma QI_av_lt [Nonempty ι] {f g : ι → ℝ} (h : ∀ j, f j < g j) :
    QI_av f < QI_av g := by
  unfold QI_av
  have : (0 : ℝ) < ((Fintype.card ι : ℝ))⁻¹ := inv_pos.2 QI_card_pos
  exact mul_lt_mul_of_pos_left
    (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => h j) this

private lemma QI_av_nonneg {f : ι → ℝ} (h : ∀ j, 0 ≤ f j) : 0 ≤ QI_av f := by
  unfold QI_av
  have : 0 ≤ ∑ j, f j := Finset.sum_nonneg fun j _ => h j
  positivity

/-- With `Σ_j μ_j = 0`: `|n⁻¹ Σ_j μ_j f_j| ≤ L n⁻¹ Σ_j μ_j²` when `|f_j - f₀| ≤ L |μ_j|`. -/
private lemma QI_av_mu (μ : ι → ℝ) (h0 : ∑ j, μ j = 0) (f : ι → ℝ) (f0 L : ℝ)
    (hf : ∀ j, |f j - f0| ≤ L * |μ j|) :
    |QI_av (fun j => μ j * f j)| ≤ L * QI_av (fun j => μ j ^ 2) := by
  have e : QI_av (fun j => μ j * f j) = QI_av (fun j => μ j * (f j - f0)) := by
    unfold QI_av
    congr 1
    have : ∑ j, μ j * (f j - f0) = (∑ j, μ j * f j) - f0 * ∑ j, μ j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      funext j
      ring
    rw [this, h0]
    ring
  rw [e]
  refine (QI_abs_av _).trans ?_
  rw [← QI_av_mul_left]
  apply QI_av_mono
  intro j
  rw [abs_mul]
  calc |μ j| * |f j - f0| ≤ |μ j| * (L * |μ j|) := by gcongr; exact hf j
    _ = L * μ j ^ 2 := by rw [← sq_abs (μ j)]; ring

/-- A quotient `m Y / Z` with `|Y| ≤ a`, `Z ≥ b > 0`, `a ≤ L b` is at most `L |m|`. -/
private lemma QI_frac {m Y Z a b L : ℝ} (hY : |Y| ≤ a) (hZ : b ≤ Z) (hb : 0 < b)
    (hab : a ≤ L * b) : |m * Y / Z| ≤ L * |m| := by
  have hZ0 : 0 < Z := lt_of_lt_of_le hb hZ
  rw [abs_div, abs_mul, abs_of_pos hZ0, div_le_iff₀ hZ0]
  have h1 : |m| * |Y| ≤ |m| * a := by gcongr
  have h2 : |m| * a ≤ |m| * (L * b) := by gcongr
  have h3 : 0 ≤ L := by
    have : 0 ≤ a := (abs_nonneg Y).trans hY
    by_contra h
    have h := lt_of_not_ge h
    nlinarith
  have h4 : |m| * (L * b) ≤ L * |m| * Z := by
    have : |m| * (L * b) = L * |m| * b := by ring
    rw [this]
    gcongr
  linarith

/-- `r² - 2rmc + m² = |m - ω|²` for `ω = r(c + i√(1-c²))`. -/
private def QI_dd (m r c : ℝ) : ℝ := r ^ 2 - 2 * r * m * c + m ^ 2

private lemma QI_mc {m c : ℝ} (hc : |c| ≤ 1) : |m * c| ≤ |m| := by
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hc

private lemma QI_dd_ge {m r c : ℝ} (hm : |m| ≤ 1 / 10) (hc : |c| ≤ 1) (hr : 1 / 10 ≤ r) :
    (r - 1 / 10) ^ 2 ≤ QI_dd m r c := by
  unfold QI_dd
  have h1 := QI_mc (m := m) hc
  have h2 : m * c ≤ |m| := (le_abs_self _).trans h1
  have h4 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  nlinarith [mul_nonneg (by linarith : 0 ≤ r) (by linarith : 0 ≤ |m| - m * c),
    mul_nonneg (by linarith : 0 ≤ 1 / 10 - |m|)
      (by linarith [abs_nonneg m] : (0 : ℝ) ≤ 2 * r - |m| - 1 / 10)]

private lemma QI_dd_le {m r c : ℝ} (hm : |m| ≤ 1 / 10) (hc : |c| ≤ 1) (hr : 0 ≤ r) :
    QI_dd m r c ≤ (r + 1 / 10) ^ 2 := by
  unfold QI_dd
  have h1 := QI_mc (m := m) hc
  have h2 : -(m * c) ≤ |m| := (neg_le_abs _).trans h1
  have h4 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  nlinarith [mul_nonneg hr (by linarith : 0 ≤ |m| + m * c),
    mul_nonneg (by linarith : 0 ≤ 1 / 10 - |m|)
      (by linarith [abs_nonneg m] : (0 : ℝ) ≤ 2 * r + |m| + 1 / 10)]

private lemma QI_dd_pos {m r c : ℝ} (hm : |m| ≤ 1 / 10) (hc : |c| ≤ 1) (hr : 1 / 10 < r) :
    0 < QI_dd m r c := by
  have := QI_dd_ge hm hc hr.le
  have : 0 < (r - 1 / 10) ^ 2 := by
    have : 0 < r - 1 / 10 := by linarith
    positivity
  linarith

private lemma QI_dd_lo {m r c : ℝ} (hm : |m| ≤ 1 / 10) (hc : |c| ≤ 1) (hr : 9 / 10 ≤ r) :
    16 / 25 ≤ QI_dd m r c := by
  have := QI_dd_ge hm hc (by linarith : (1 / 10 : ℝ) ≤ r)
  nlinarith

private lemma QI_dd_hi {m r c : ℝ} (hm : |m| ≤ 1 / 10) (hc : |c| ≤ 1) (hr0 : 0 ≤ r)
    (hr : r ≤ 11 / 10) : QI_dd m r c ≤ 36 / 25 := by
  have := QI_dd_le hm hc hr0
  nlinarith

/-- `Q(r, c) = n⁻¹ Σ_j |μ_j - ω|⁻²` for `ω = r(c + i√(1-c²))`. -/
private def QI_Q (μ : ι → ℝ) (r c : ℝ) : ℝ := QI_av fun j => 1 / QI_dd (μ j) r c

/-- The radius `R(c) ∈ [9/10, 11/10]` with `Q(R(c), c) = 1`. -/
private def QI_R (μ : ι → ℝ) (c : ℝ) : ℝ :=
  if h : ∃ r : ℝ, 9 / 10 ≤ r ∧ r ≤ 11 / 10 ∧ QI_Q μ r c = 1 then h.choose else 1

private lemma QI_Q_cont (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {c : ℝ} (hc : |c| ≤ 1) :
    ContinuousOn (fun r => QI_Q μ r c) (Set.Icc (9 / 10) (11 / 10)) := by
  unfold QI_Q QI_av
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro j _
  apply ContinuousOn.div continuousOn_const
    (show ContinuousOn (fun r => QI_dd (μ j) r c) _ by unfold QI_dd; fun_prop)
  intro r hr
  exact (QI_dd_pos (hμ j) hc (by linarith [hr.1])).ne'

private lemma QI_R_spec [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {c : ℝ}
    (hc : |c| ≤ 1) :
    9 / 10 ≤ QI_R μ c ∧ QI_R μ c ≤ 11 / 10 ∧ QI_Q μ (QI_R μ c) c = 1 := by
  have hex : ∃ r : ℝ, 9 / 10 ≤ r ∧ r ≤ 11 / 10 ∧ QI_Q μ r c = 1 := by
    have h1 : 1 ≤ QI_Q μ (9 / 10) c := by
      unfold QI_Q
      calc (1 : ℝ) = QI_av (fun _ : ι => (1 : ℝ)) := (QI_av_const 1).symm
        _ ≤ _ := QI_av_mono fun j => by
          have h := QI_dd_le (hμ j) hc (by norm_num : (0 : ℝ) ≤ 9 / 10)
          have h' := QI_dd_pos (hμ j) hc (by norm_num : (1 / 10 : ℝ) < 9 / 10)
          rw [le_div_iff₀ h']
          nlinarith
    have h2 : QI_Q μ (11 / 10) c ≤ 1 := by
      unfold QI_Q
      calc _ ≤ QI_av (fun _ : ι => (1 : ℝ)) := QI_av_mono fun j => by
            have h := QI_dd_ge (hμ j) hc (by norm_num : (1 / 10 : ℝ) ≤ 11 / 10)
            have h' := QI_dd_pos (hμ j) hc (by norm_num : (1 / 10 : ℝ) < 11 / 10)
            rw [div_le_iff₀ h']
            nlinarith
        _ = 1 := QI_av_const 1
    obtain ⟨r, hr, hr'⟩ := intermediate_value_Icc' (by norm_num : (9 / 10 : ℝ) ≤ 11 / 10)
      (QI_Q_cont μ hμ hc) (show (1 : ℝ) ∈ Set.Icc _ _ from ⟨h2, h1⟩)
    exact ⟨r, hr.1, hr.2, hr'⟩
  unfold QI_R
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hex h

/-- `Q(·, c)` is strictly decreasing on `r > 1/10`. -/
private lemma QI_Q_lt [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {c r r' : ℝ}
    (hc : |c| ≤ 1) (hr : 1 / 10 < r) (hrr : r < r') : QI_Q μ r' c < QI_Q μ r c := by
  unfold QI_Q
  apply QI_av_lt
  intro j
  have h1 := QI_dd_pos (hμ j) hc hr
  have h2 := QI_dd_pos (hμ j) hc (hr.trans hrr)
  rw [div_lt_div_iff₀ h2 h1, one_mul, one_mul]
  have h3 := QI_mc (m := μ j) hc
  have h4 : μ j * c ≤ 1 / 10 := (le_abs_self _).trans (h3.trans (hμ j))
  unfold QI_dd
  nlinarith

private lemma QI_R_unique [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {c r : ℝ}
    (hc : |c| ≤ 1) (hr : 9 / 10 ≤ r) (hQ : QI_Q μ r c = 1) : r = QI_R μ c := by
  obtain ⟨h1, h2, h3⟩ := QI_R_spec μ hμ hc
  rcases lt_trichotomy r (QI_R μ c) with h | h | h
  · have := QI_Q_lt μ hμ hc (by linarith) h
    linarith
  · exact h
  · have := QI_Q_lt μ hμ hc (by linarith) h
    linarith

/-- `A(r, r', c)` with `Q(r, c) - Q(r', c) = (r' - r) A`. -/
private def QI_A (μ : ι → ℝ) (r r' c : ℝ) : ℝ :=
  QI_av fun j => (r + r' - 2 * μ j * c) / (QI_dd (μ j) r c * QI_dd (μ j) r' c)

/-- `B(r, c, c')` with `Q(r, c) - Q(r, c') = (c - c') B`. -/
private def QI_B (μ : ι → ℝ) (r c c' : ℝ) : ℝ :=
  QI_av fun j => μ j * (2 * r / (QI_dd (μ j) r c * QI_dd (μ j) r c'))

private lemma QI_Q_sub_r (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {r r' c : ℝ} (hc : |c| ≤ 1)
    (hr : 1 / 10 < r) (hr' : 1 / 10 < r') :
    QI_Q μ r c - QI_Q μ r' c = (r' - r) * QI_A μ r r' c := by
  unfold QI_Q QI_A
  rw [← QI_av_sub, ← QI_av_mul_left]
  congr 1
  funext j
  have h1 := (QI_dd_pos (hμ j) hc hr).ne'
  have h2 := (QI_dd_pos (hμ j) hc hr').ne'
  field_simp
  unfold QI_dd
  ring

private lemma QI_Q_sub_c (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {r c c' : ℝ} (hc : |c| ≤ 1)
    (hc' : |c'| ≤ 1) (hr : 1 / 10 < r) :
    QI_Q μ r c - QI_Q μ r c' = (c - c') * QI_B μ r c c' := by
  unfold QI_Q QI_B
  rw [← QI_av_sub, ← QI_av_mul_left]
  congr 1
  funext j
  have h1 := (QI_dd_pos (hμ j) hc hr).ne'
  have h2 := (QI_dd_pos (hμ j) hc' hr).ne'
  field_simp
  unfold QI_dd
  ring

private lemma QI_A_ge [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {r r' c : ℝ}
    (hc : |c| ≤ 1) (hr : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10) (hr' : 9 / 10 ≤ r')
    (hr1' : r' ≤ 11 / 10) : 3 / 4 ≤ QI_A μ r r' c := by
  unfold QI_A
  calc (3 / 4 : ℝ) = QI_av (fun _ : ι => (3 / 4 : ℝ)) := (QI_av_const _).symm
    _ ≤ _ := QI_av_mono fun j => by
      have h1 := QI_dd_lo (hμ j) hc hr
      have h2 := QI_dd_lo (hμ j) hc hr'
      have h3 := QI_dd_hi (hμ j) hc (by linarith) hr1
      have h4 := QI_dd_hi (hμ j) hc (by linarith) hr1'
      have h5 : QI_dd (μ j) r c * QI_dd (μ j) r' c ≤ 36 / 25 * (36 / 25) :=
        mul_le_mul h3 h4 (by linarith) (by norm_num)
      have h6 := QI_mc (m := μ j) hc
      have h7 : μ j * c ≤ 1 / 10 := (le_abs_self _).trans (h6.trans (hμ j))
      rw [le_div_iff₀ (by positivity)]
      nlinarith

private lemma QI_B_le (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) (h0 : ∑ j, μ j = 0)
    {r c c' : ℝ} (hc : |c| ≤ 1) (hc' : |c'| ≤ 1) (hr : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10) :
    |QI_B μ r c c'| ≤ 50 * QI_av (fun j => μ j ^ 2) := by
  unfold QI_B
  refine QI_av_mu μ h0 _ (2 / r ^ 3) 50 fun j => ?_
  set m := μ j
  have hm := hμ j
  have h1 := QI_dd_lo hm hc hr
  have h2 := QI_dd_lo hm hc' hr
  have hr0 : 0 < r := by linarith
  have e : 2 * r / (QI_dd m r c * QI_dd m r c') - 2 / r ^ 3 =
      m * (-2 * (r ^ 2 * (2 * m - 2 * r * c - 2 * r * c') +
        m * (m - 2 * r * c) * (m - 2 * r * c'))) / (r ^ 3 * (QI_dd m r c * QI_dd m r c')) := by
    have : QI_dd m r c ≠ 0 := by linarith
    have : QI_dd m r c' ≠ 0 := by linarith
    field_simp
    unfold QI_dd
    ring
  rw [e]
  have hcl := abs_le.1 hc
  have hcl' := abs_le.1 hc'
  have hml := abs_le.1 hm
  refine QI_frac (a := 2 * ((121 / 100) * (23 / 5) + (1 / 10) * (23 / 10) * (23 / 10)))
    (b := (729 / 1000) * ((16 / 25) * (16 / 25))) ?_ ?_ (by norm_num) (by norm_num)
  · have e1 : |2 * m - 2 * r * c - 2 * r * c'| ≤ 23 / 5 := by
      rw [abs_le]; constructor <;> nlinarith
    have e2 : |m - 2 * r * c| ≤ 23 / 10 := by
      rw [abs_le]; constructor <;> nlinarith
    have e3 : |m - 2 * r * c'| ≤ 23 / 10 := by
      rw [abs_le]; constructor <;> nlinarith
    have e4 : |r ^ 2| ≤ 121 / 100 := by
      rw [abs_of_nonneg (by positivity)]; nlinarith
    rw [abs_mul, abs_neg, abs_two]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul]
    gcongr
  · have : (729 / 1000 : ℝ) ≤ r ^ 3 := by nlinarith
    gcongr

/-- `|Q(r, c) - r⁻²| ≤ 13 ⟨μ²⟩`. -/
private lemma QI_Q_sub_inv [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {r c : ℝ} (hc : |c| ≤ 1) (hr : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10) :
    |QI_Q μ r c - 1 / r ^ 2| ≤ 13 * QI_av (fun j => μ j ^ 2) := by
  have hr0 : 0 < r := by linarith
  have e : QI_Q μ r c - 1 / r ^ 2 =
      QI_av (fun j => μ j * ((2 * r * c - μ j) / (r ^ 2 * QI_dd (μ j) r c))) := by
    unfold QI_Q
    rw [← QI_av_const (ι := ι) (1 / r ^ 2), ← QI_av_sub]
    congr 1
    funext j
    have := (QI_dd_pos (hμ j) hc (by linarith : (1 / 10 : ℝ) < r)).ne'
    field_simp
    unfold QI_dd
    ring
  rw [e]
  refine QI_av_mu μ h0 _ (2 * c / r ^ 3) 13 fun j => ?_
  set m := μ j
  have hm := hμ j
  have h1 := QI_dd_lo hm hc hr
  have e2 : (2 * r * c - m) / (r ^ 2 * QI_dd m r c) - 2 * c / r ^ 3 =
      m * (-r + 4 * r * c ^ 2 - 2 * c * m) / (r ^ 3 * QI_dd m r c) := by
    have : QI_dd m r c ≠ 0 := by linarith
    field_simp
    unfold QI_dd
    ring
  rw [e2]
  have hcl := abs_le.1 hc
  have hml := abs_le.1 hm
  refine QI_frac (a := 57 / 10) (b := (729 / 1000) * (16 / 25)) ?_ ?_ (by norm_num)
    (by norm_num)
  · rw [abs_le]; constructor <;> nlinarith
  · have : (729 / 1000 : ℝ) ≤ r ^ 3 := by nlinarith
    gcongr

private lemma QI_R_sub_one [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {c : ℝ} (hc : |c| ≤ 1) :
    |QI_R μ c - 1| ≤ 9 * QI_av (fun j => μ j ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := QI_R_spec μ hμ hc
  have h := QI_Q_sub_inv μ hμ h0 hc h1 h2
  rw [h3] at h
  set R := QI_R μ c
  have hs : 0 ≤ QI_av (fun j => μ j ^ 2) := QI_av_nonneg fun j => sq_nonneg _
  have e : R - 1 = R ^ 2 * (1 - 1 / R ^ 2) / (R + 1) := by
    have : R ≠ 0 := by linarith
    have : R + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_of_pos (by linarith : 0 < R + 1), abs_of_pos (by positivity),
    div_le_iff₀ (by linarith)]
  have : R ^ 2 ≤ 121 / 100 := by nlinarith
  calc R ^ 2 * |1 - 1 / R ^ 2| ≤ 121 / 100 * (13 * QI_av (fun j => μ j ^ 2)) := by
        gcongr
    _ ≤ 9 * QI_av (fun j => μ j ^ 2) * (R + 1) := by nlinarith

private lemma QI_R_sub [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10) {c c' : ℝ}
    (hc : |c| ≤ 1) (hc' : |c'| ≤ 1) :
    (QI_R μ c' - QI_R μ c) * QI_A μ (QI_R μ c) (QI_R μ c') c =
      (c' - c) * QI_B μ (QI_R μ c') c c' := by
  obtain ⟨h1, h2, h3⟩ := QI_R_spec μ hμ hc
  obtain ⟨h1', h2', h3'⟩ := QI_R_spec μ hμ hc'
  have e1 := QI_Q_sub_r μ hμ hc (by linarith : (1 / 10 : ℝ) < QI_R μ c)
    (by linarith : (1 / 10 : ℝ) < QI_R μ c')
  have e2 := QI_Q_sub_c μ hμ hc hc' (by linarith : (1 / 10 : ℝ) < QI_R μ c')
  rw [h3] at e1
  rw [h3'] at e2
  linarith

private lemma QI_R_lip [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {c c' : ℝ} (hc : |c| ≤ 1) (hc' : |c'| ≤ 1) :
    |QI_R μ c' - QI_R μ c| ≤ 67 * QI_av (fun j => μ j ^ 2) * |c' - c| := by
  obtain ⟨h1, h2, -⟩ := QI_R_spec μ hμ hc
  obtain ⟨h1', h2', -⟩ := QI_R_spec μ hμ hc'
  have e := QI_R_sub μ hμ hc hc'
  have hA := QI_A_ge μ hμ (c := c) hc h1 h2 h1' h2'
  have hB := QI_B_le μ hμ h0 (r := QI_R μ c') hc hc' h1' h2'
  have hs : 0 ≤ QI_av (fun j => μ j ^ 2) := QI_av_nonneg fun j => sq_nonneg _
  have : |QI_R μ c' - QI_R μ c| * QI_A μ (QI_R μ c) (QI_R μ c') c ≤
      |c' - c| * (50 * QI_av (fun j => μ j ^ 2)) := by
    rw [← abs_of_pos (by linarith : 0 < QI_A μ (QI_R μ c) (QI_R μ c') c), ← abs_mul, e,
      abs_mul]
    gcongr
  have h4 : 0 ≤ |QI_R μ c' - QI_R μ c| := abs_nonneg _
  have h5 : 0 ≤ |c' - c| := abs_nonneg _
  nlinarith

/-- `E(c) = 2R(c)c - n⁻¹ Σ_j μ_j |μ_j - ω|⁻²`, the real point `ω - m_μ(ω)`. -/
private def QI_E (μ : ι → ℝ) (c : ℝ) : ℝ :=
  2 * QI_R μ c * c - QI_av fun j => μ j / QI_dd (μ j) (QI_R μ c) c

private lemma QI_E_lip [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {c c' : ℝ} (hc : |c| ≤ 1) (hc' : |c'| ≤ 1) :
    |(QI_E μ c' - 2 * c') - (QI_E μ c - 2 * c)| ≤
      250 * QI_av (fun j => μ j ^ 2) * |c' - c| := by
  obtain ⟨h1, h2, -⟩ := QI_R_spec μ hμ hc
  obtain ⟨h1', h2', -⟩ := QI_R_spec μ hμ hc'
  have hR1 := QI_R_sub_one μ hμ h0 hc'
  have hRl := QI_R_lip μ hμ h0 hc hc'
  set s := QI_av (fun j => μ j ^ 2)
  set r := QI_R μ c
  set r' := QI_R μ c'
  have hs : 0 ≤ s := QI_av_nonneg fun j => sq_nonneg _
  have e : (QI_E μ c' - 2 * c') - (QI_E μ c - 2 * c) =
      (2 * (r' - 1) * (c' - c) + 2 * c * (r' - r)) -
        QI_av (fun j => μ j / QI_dd (μ j) r' c' - μ j / QI_dd (μ j) r c) := by
    unfold QI_E
    rw [QI_av_sub]
    ring
  rw [e]
  have hcl := abs_le.1 hc
  have hcl' := abs_le.1 hc'
  have hT : ∀ j, |μ j / QI_dd (μ j) r' c' - μ j / QI_dd (μ j) r c| ≤
      (3 / 5) * |r' - r| + 6 * μ j ^ 2 * |c' - c| := by
    intro j
    set m := μ j
    have hm := hμ j
    have hml := abs_le.1 hm
    have d1 := QI_dd_lo hm hc h1
    have d2 := QI_dd_lo hm hc' h1'
    have e1 : m / QI_dd m r' c' - m / QI_dd m r c =
        m * ((r - r') * (r + r') - 2 * m * (r * c - r' * c')) /
          (QI_dd m r' c' * QI_dd m r c) := by
      have : QI_dd m r c ≠ 0 := by linarith
      have : QI_dd m r' c' ≠ 0 := by linarith
      field_simp
      unfold QI_dd
      ring
    rw [e1, abs_div, abs_mul,
      abs_of_pos (show 0 < QI_dd m r' c' * QI_dd m r c from mul_pos (by linarith) (by linarith))]
    have hp : 16 / 25 * (16 / 25) ≤ QI_dd m r' c' * QI_dd m r c := by gcongr
    have hX : |(r - r') * (r + r') - 2 * m * (r * c - r' * c')| ≤
        (11 / 5) * |r' - r| + 2 * |m| * (|r' - r| + (11 / 10) * |c' - c|) := by
      have f1 : |r * c - r' * c'| ≤ |r' - r| + (11 / 10) * |c' - c| := by
        have : r * c - r' * c' = (r - r') * c + r' * (c - c') := by ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_sub_comm r r', abs_sub_comm c c',
          abs_of_pos (by linarith : 0 < r')]
        gcongr
        · exact mul_le_of_le_one_right (abs_nonneg _) hc
      have f2 : |(r - r') * (r + r')| ≤ (11 / 5) * |r' - r| := by
        rw [abs_mul, abs_sub_comm, abs_of_pos (by linarith : 0 < r + r'), mul_comm]
        gcongr
        linarith
      refine (abs_sub _ _).trans (add_le_add f2 ?_)
      rw [abs_mul, abs_mul, abs_two]
      gcongr
    have hm2 : |m| ^ 2 = m ^ 2 := sq_abs m
    rw [div_le_iff₀ (by positivity)]
    have ha : 0 ≤ |m| := abs_nonneg m
    have hb : 0 ≤ |r' - r| := abs_nonneg _
    have hc0 : 0 ≤ |c' - c| := abs_nonneg _
    calc |m| * |(r - r') * (r + r') - 2 * m * (r * c - r' * c')|
        ≤ |m| * ((11 / 5) * |r' - r| + 2 * |m| * (|r' - r| + (11 / 10) * |c' - c|)) := by
          gcongr
      _ ≤ ((3 / 5) * |r' - r| + 6 * m ^ 2 * |c' - c|) * (16 / 25 * (16 / 25)) := by
          nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha ha) hb,
            mul_nonneg (mul_nonneg ha ha) hc0]
      _ ≤ _ := by gcongr
  have hav : |QI_av (fun j => μ j / QI_dd (μ j) r' c' - μ j / QI_dd (μ j) r c)| ≤
      (3 / 5) * |r' - r| + 6 * s * |c' - c| := by
    refine (QI_abs_av _).trans ?_
    calc _ ≤ QI_av (fun j => (3 / 5) * |r' - r| + 6 * |c' - c| * μ j ^ 2) :=
          QI_av_mono fun j => by linarith [hT j]
      _ = _ := by
          rw [QI_av_add, QI_av_const, QI_av_mul_left]
          ring
  have hA : |2 * (r' - 1) * (c' - c) + 2 * c * (r' - r)| ≤ 2 * (9 * s) * |c' - c| +
      2 * (67 * s * |c' - c|) := by
    have t1 : |2 * (r' - 1) * (c' - c)| ≤ 2 * (9 * s) * |c' - c| := by
      rw [abs_mul, abs_mul, abs_two]
      gcongr
    have t2 : |2 * c * (r' - r)| ≤ 2 * (67 * s * |c' - c|) := by
      rw [abs_mul, abs_mul, abs_two]
      have h0' : 0 ≤ |r' - r| := abs_nonneg _
      calc 2 * |c| * |r' - r| ≤ 2 * 1 * |r' - r| := by gcongr
        _ ≤ _ := by linarith
    exact (abs_add_le _ _).trans (add_le_add t1 t2)
  refine (abs_sub _ _).trans ?_
  have : 0 ≤ |c' - c| := abs_nonneg _
  nlinarith

private lemma QI_contAt_of_lip {f : ℝ → ℝ} {c₀ K : ℝ}
    (h : ∀ᶠ c in 𝓝 c₀, |f c - f c₀| ≤ K * |c - c₀|) : ContinuousAt f c₀ := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun c => norm_nonneg _)
    (h.mono fun c hc => by simpa [Real.norm_eq_abs] using hc) ?_
  have : Tendsto (fun c => K * |c - c₀|) (𝓝 c₀) (𝓝 (K * |c₀ - c₀|)) :=
    ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).tendsto c₀)
  simpa using this

private lemma QI_Icc_mem {c₀ : ℝ} (hc : c₀ ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ c in 𝓝 c₀, |c| ≤ 1 :=
  Filter.eventually_of_mem (Icc_mem_nhds hc.1 hc.2) fun _ h => abs_le.2 h

private lemma QI_R_contAt [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {c₀ : ℝ} (hc : c₀ ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousAt (QI_R μ) c₀ :=
  QI_contAt_of_lip ((QI_Icc_mem hc).mono fun _ h =>
    QI_R_lip μ hμ h0 (abs_le.2 ⟨hc.1.le, hc.2.le⟩) h)

private lemma QI_R_hasDerivAt [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {c₀ : ℝ} (hc : c₀ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (QI_R μ) (QI_B μ (QI_R μ c₀) c₀ c₀ / QI_A μ (QI_R μ c₀) (QI_R μ c₀) c₀) c₀ := by
  have hc0 : |c₀| ≤ 1 := abs_le.2 ⟨hc.1.le, hc.2.le⟩
  have hR := QI_R_contAt μ hμ h0 hc
  obtain ⟨h1, h2, -⟩ := QI_R_spec μ hμ hc0
  have hdd : ∀ j (r c : ℝ), |c| ≤ 1 → 9 / 10 ≤ r → QI_dd (μ j) r c ≠ 0 := fun j r c hc hr =>
    (QI_dd_pos (hμ j) hc (by linarith)).ne'
  have hB : ContinuousAt (fun c => QI_B μ (QI_R μ c) c₀ c) c₀ := by
    unfold QI_B QI_av
    refine continuousAt_const.mul (tendsto_finsetSum _ fun j _ => ?_)
    have hd : ContinuousAt (fun c => QI_dd (μ j) (QI_R μ c) c₀ * QI_dd (μ j) (QI_R μ c) c) c₀ := by
      unfold QI_dd
      fun_prop
    exact continuousAt_const.mul (ContinuousAt.div (f := fun c => 2 * QI_R μ c)
      (continuousAt_const.mul hR) hd (mul_ne_zero (hdd j _ _ hc0 h1) (hdd j _ _ hc0 h1)))
  have hA : ContinuousAt (fun c => QI_A μ (QI_R μ c₀) (QI_R μ c) c₀) c₀ := by
    unfold QI_A QI_av
    refine continuousAt_const.mul (tendsto_finsetSum _ fun j _ => ?_)
    have hd : ContinuousAt (fun c => QI_dd (μ j) (QI_R μ c₀) c₀ * QI_dd (μ j) (QI_R μ c) c₀)
        c₀ := by
      unfold QI_dd
      fun_prop
    have hn : ContinuousAt (fun c => QI_R μ c₀ + QI_R μ c - 2 * μ j * c₀) c₀ := by fun_prop
    exact ContinuousAt.div hn hd (mul_ne_zero (hdd j _ _ hc0 h1) (hdd j _ _ hc0 h1))
  have hA0 : QI_A μ (QI_R μ c₀) (QI_R μ c₀) c₀ ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (QI_A_ge μ hμ hc0 h1 h2 h1 h2)).ne'
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim := (hB.div hA hA0).tendsto.mono_left (nhdsWithin_le_nhds (s := {c₀}ᶜ))
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (QI_Icc_mem hc), self_mem_nhdsWithin] with c hc' hne
  have hne' : c - c₀ ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨h1', h2', -⟩ := QI_R_spec μ hμ hc'
  have hApos := QI_A_ge μ hμ hc0 h1 h2 h1' h2'
  have e := QI_R_sub μ hμ hc0 hc'
  have hA1 : QI_A μ (QI_R μ c₀) (QI_R μ c) c₀ ≠ 0 := by linarith
  rw [slope_def_field, Pi.div_apply, div_eq_div_iff hA1 hne']
  linarith

private lemma QI_E_hasDerivAt [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) {c₀ : ℝ} (hc : c₀ ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ e' : ℝ, HasDerivAt (QI_E μ) e' c₀ ∧ |e' - 2| ≤ 250 * QI_av (fun j => μ j ^ 2) := by
  have hc0 : |c₀| ≤ 1 := abs_le.2 ⟨hc.1.le, hc.2.le⟩
  have hRd := (QI_R_hasDerivAt μ hμ h0 hc).differentiableAt
  obtain ⟨h1, -, -⟩ := QI_R_spec μ hμ hc0
  have hd : DifferentiableAt ℝ (QI_E μ) c₀ := by
    have hsum : DifferentiableAt ℝ (fun c => ∑ j, μ j / QI_dd (μ j) (QI_R μ c) c) c₀ := by
      refine DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
        (A := fun j c => μ j / QI_dd (μ j) (QI_R μ c) c) fun j _ => ?_
      have hdd : DifferentiableAt ℝ (fun c => QI_dd (μ j) (QI_R μ c) c) c₀ := by
        unfold QI_dd
        fun_prop
      have hne : QI_dd (μ j) (QI_R μ c₀) c₀ ≠ 0 :=
        (QI_dd_pos (hμ j) hc0 (show (1 / 10 : ℝ) < QI_R μ c₀ by linarith)).ne'
      exact DifferentiableAt.div (differentiableAt_const _) hdd hne
    have h2 : DifferentiableAt ℝ (fun c => 2 * QI_R μ c * c) c₀ := by fun_prop
    have e : QI_E μ = fun c => 2 * QI_R μ c * c -
        ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j / QI_dd (μ j) (QI_R μ c) c := rfl
    rw [e]
    exact h2.sub (hsum.const_mul _)
  refine ⟨deriv (QI_E μ) c₀, hd.hasDerivAt, ?_⟩
  have hs : 0 ≤ QI_av (fun j => μ j ^ 2) := QI_av_nonneg fun j => sq_nonneg _
  have h2 : HasDerivAt (fun c => QI_E μ c - 2 * c) (deriv (QI_E μ) c₀ - 2 * 1) c₀ :=
    hd.hasDerivAt.sub ((hasDerivAt_id c₀).const_mul 2)
  have := h2.le_of_lip' (C := 250 * QI_av (fun j => μ j ^ 2)) (mul_nonneg (by norm_num) hs)
    ((QI_Icc_mem hc).mono fun c h => by
    have := QI_E_lip μ hμ h0 hc0 h
    simpa [Real.norm_eq_abs] using this)
  simpa [Real.norm_eq_abs] using this

private lemma QI_contOn_of_lip {f : ℝ → ℝ} {K : ℝ}
    (h : ∀ c ∈ Set.Icc (-1 : ℝ) 1, ∀ c' ∈ Set.Icc (-1 : ℝ) 1, |f c' - f c| ≤ K * |c' - c|) :
    ContinuousOn f (Set.Icc (-1) 1) := by
  intro c hc
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun c => norm_nonneg _)
    (Filter.eventually_of_mem self_mem_nhdsWithin fun c' hc' => by
      simpa [Real.norm_eq_abs] using h c hc c' hc') ?_
  have : Tendsto (fun c' => K * |c' - c|) (𝓝 c) (𝓝 (K * |c - c|)) :=
    ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).tendsto c)
  simpa using this.mono_left nhdsWithin_le_nhds

private lemma QI_E_contOn [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) : ContinuousOn (QI_E μ) (Set.Icc (-1) 1) := by
  refine QI_contOn_of_lip (K := 2 + 250 * QI_av (fun j => μ j ^ 2)) fun c hc c' hc' => ?_
  have := QI_E_lip μ hμ h0 (abs_le.2 hc) (abs_le.2 hc')
  have e : QI_E μ c' - QI_E μ c = 2 * (c' - c) + ((QI_E μ c' - 2 * c') - (QI_E μ c - 2 * c)) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_two]
  linarith

/-- `E` is strictly increasing on `[-1, 1]`. -/
private lemma QI_E_strictMono [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) (hs : QI_av (fun j => μ j ^ 2) ≤ 1 / 1000) {c c' : ℝ} (hc : |c| ≤ 1)
    (hc' : |c'| ≤ 1) (hcc : c < c') : QI_E μ c < QI_E μ c' := by
  have := QI_E_lip μ hμ h0 hc hc'
  rw [abs_of_pos (by linarith : 0 < c' - c)] at this
  have h := (abs_le.1 this).1
  nlinarith

end QIAlg

section QICmp
open Set

/-- `σ(c) = 2√(1-c²)/π`, the semicircle density in the variable `c = E/2` times `2`. -/
private def QI_sig (c : ℝ) : ℝ := 2 * Real.sqrt (1 - c ^ 2) / Real.pi

/-- `(1 - c)^{3/2}`. -/
private def QI_p32 (c : ℝ) : ℝ := (1 - c) * Real.sqrt (1 - c)

private lemma QI_sig_nonneg (c : ℝ) : 0 ≤ QI_sig c := by
  unfold QI_sig
  have := Real.pi_pos
  positivity

private lemma QI_sig_pos {c : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1) : 0 < QI_sig c := by
  unfold QI_sig
  have := Real.pi_pos
  have : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
  have := Real.sqrt_pos.2 this
  positivity

private lemma QI_sig_neg (c : ℝ) : QI_sig (-c) = QI_sig c := by
  unfold QI_sig
  rw [neg_sq]

private lemma QI_sqrt_mul {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    Real.sqrt (1 - c ^ 2) = Real.sqrt (1 - c) * Real.sqrt (1 + c) := by
  rw [← Real.sqrt_mul (by linarith [hc.2])]
  congr 1
  ring

private lemma QI_p32_nonneg {c : ℝ} (hc : c ≤ 1) : 0 ≤ QI_p32 c := by
  unfold QI_p32
  have : 0 ≤ 1 - c := by linarith
  positivity

private lemma QI_p32_hasDerivAt {c : ℝ} (hc : c < 1) :
    HasDerivAt QI_p32 (-(3 / 2) * Real.sqrt (1 - c)) c := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) c := by
    simpa using (hasDerivAt_id c).const_sub 1
  have hpos : 0 < 1 - c := by linarith
  have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x)) (-1 / (2 * Real.sqrt (1 - c))) c := by
    exact h1.sqrt hpos.ne'
  have h3 := h1.mul h2
  have hs : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.2 hpos
  have e : -1 * Real.sqrt (1 - c) + (1 - c) * (-1 / (2 * Real.sqrt (1 - c))) =
      -(3 / 2) * Real.sqrt (1 - c) := by
    have hsq : Real.sqrt (1 - c) * Real.sqrt (1 - c) = 1 - c := Real.mul_self_sqrt hpos.le
    field_simp
    nlinarith [hsq]
  rw [e] at h3
  exact h3

private lemma QI_xsx_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    x * Real.sqrt x < y * Real.sqrt y := by
  have h1 := Real.sqrt_lt_sqrt hx hxy
  have h2 := Real.sqrt_nonneg x
  nlinarith

private lemma QI_sqrt_quarter (x : ℝ) : Real.sqrt (x / 4) = Real.sqrt x / 2 := by
  rw [show x / 4 = x * (1 / 2) ^ 2 by ring, Real.sqrt_mul' _ (by positivity),
    Real.sqrt_sq (by norm_num)]
  ring

private lemma QI_anti {f f' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hn : ∀ x ∈ Ioo a b, f' x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hc (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at hx
    rw [(hd x hx).deriv]
    exact hn x hx

private lemma QI_mono {f f' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hn : ∀ x ∈ Ioo a b, 0 ≤ f' x) :
    MonotoneOn f (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hc (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at hx
    rw [(hd x hx).deriv]
    exact hn x hx

/-- The comparison `(1 ∓ ε) h ≤ H ≤ (1 ± ε) h` (and the same for `1 - H`, `1 - h`) for two
tails with `H' = -wσ`, `h' = -σ`, `|w - 1| ≤ ε`. -/
private lemma QI_cmp {H h w : ℝ → ℝ} {ε : ℝ} (hHc : ContinuousOn H (Icc (-1) 1))
    (hhc : ContinuousOn h (Icc (-1) 1))
    (hHd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt H (-(w c * QI_sig c)) c)
    (hhd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (-QI_sig c) c)
    (hw : ∀ c ∈ Ioo (-1 : ℝ) 1, |w c - 1| ≤ ε)
    (hH1 : H 1 = 0) (hh1 : h 1 = 0) (hHm : H (-1) = 1) (hhm : h (-1) = 1) :
    ∀ c ∈ Icc (-1 : ℝ) 1, (1 - ε) * h c ≤ H c ∧ H c ≤ (1 + ε) * h c ∧
      (1 - ε) * (1 - h c) ≤ 1 - H c ∧ 1 - H c ≤ (1 + ε) * (1 - h c) := by
  intro c hc
  have h1mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hmmem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hwl : ∀ x ∈ Ioo (-1 : ℝ) 1, 1 - ε ≤ w x := fun x hx => by
    have := (abs_le.1 (hw x hx)).1; linarith
  have hwu : ∀ x ∈ Ioo (-1 : ℝ) 1, w x ≤ 1 + ε := fun x hx => by
    have := (abs_le.1 (hw x hx)).2; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hA : AntitoneOn (fun x => H x - (1 - ε) * h x) (Icc (-1) 1) := by
      refine QI_anti (hHc.sub (hhc.const_smul (1 - ε))) (fun x hx =>
        (hHd x hx).sub ((hhd x hx).const_mul (1 - ε))) fun x hx => ?_
      have := QI_sig_nonneg x
      nlinarith [hwl x hx]
    have := hA hc h1mem hc.2
    simp only [hH1, hh1, mul_zero, sub_zero] at this
    linarith
  · have hA : AntitoneOn (fun x => (1 + ε) * h x - H x) (Icc (-1) 1) := by
      refine QI_anti ((hhc.const_smul (1 + ε)).sub hHc) (fun x hx =>
        ((hhd x hx).const_mul (1 + ε)).sub (hHd x hx)) fun x hx => ?_
      have := QI_sig_nonneg x
      nlinarith [hwu x hx]
    have := hA hc h1mem hc.2
    simp only [hH1, hh1, mul_zero, sub_zero] at this
    linarith
  · have hM : MonotoneOn (fun x => (1 - H x) - (1 - ε) * (1 - h x)) (Icc (-1) 1) := by
      refine QI_mono ((continuousOn_const.sub hHc).sub
        ((continuousOn_const.sub hhc).const_smul (1 - ε))) (fun x hx =>
        ((hHd x hx).const_sub 1).sub (((hhd x hx).const_sub 1).const_mul (1 - ε)))
        fun x hx => ?_
      have := QI_sig_nonneg x
      nlinarith [hwl x hx]
    have := hM hmmem hc hc.1
    simp only [hHm, hhm, sub_self, mul_zero] at this
    linarith
  · have hM : MonotoneOn (fun x => (1 + ε) * (1 - h x) - (1 - H x)) (Icc (-1) 1) := by
      refine QI_mono (((continuousOn_const.sub hhc).const_smul (1 + ε)).sub
        (continuousOn_const.sub hHc)) (fun x hx =>
        (((hhd x hx).const_sub 1).const_mul (1 + ε)).sub ((hHd x hx).const_sub 1))
        fun x hx => ?_
      have := QI_sig_nonneg x
      nlinarith [hwu x hx]
    have := hM hmmem hc hc.1
    simp only [hHm, hhm, sub_self, mul_zero] at this
    linarith

private lemma QI_p32_cont : Continuous QI_p32 := by
  unfold QI_p32
  fun_prop

private lemma QI_negIcc {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) : -c ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [hc.2], by linarith [hc.1]⟩

private lemma QI_negIoo {c : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1) : -c ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [hc.2], by linarith [hc.1]⟩

/-- The tail `h` of the semicircle in the variable `c`: symmetry, the bounds
`(1/6)(1-c)^{3/2} ≤ h(c) ≤ (1-c)^{3/2}`, strict decrease. -/
private lemma QI_hfacts {h : ℝ → ℝ} (hhc : ContinuousOn h (Icc (-1) 1))
    (hhd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (-QI_sig c) c) (hh1 : h 1 = 0)
    (hhm : h (-1) = 1) :
    (∀ c ∈ Icc (-1 : ℝ) 1, h (-c) = 1 - h c) ∧ (∀ c ∈ Icc (-1 : ℝ) 1, h c ≤ QI_p32 c) ∧
      (∀ c ∈ Icc (-1 : ℝ) 1, (1 / 6) * QI_p32 c ≤ h c) ∧ StrictAntiOn h (Icc (-1) 1) := by
  have h1mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hmmem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hanti : StrictAntiOn h (Icc (-1) 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hhc fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hhd x hx).deriv]
    linarith [QI_sig_pos hx]
  have hsym : ∀ c ∈ Icc (-1 : ℝ) 1, h (-c) = 1 - h c := by
    have hkc : ContinuousOn (fun x => h x + h (-x)) (Icc (-1) 1) :=
      hhc.add (hhc.comp continuousOn_neg fun x hx => QI_negIcc hx)
    have hkd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x => h x + h (-x)) 0 x := by
      intro x hx
      have h2 : HasDerivAt (fun x => h (-x)) (-QI_sig (-x) * -1) x :=
        (hhd (-x) (QI_negIoo hx)).comp x (hasDerivAt_neg x)
      refine ((hhd x hx).add h2).congr_deriv ?_
      rw [QI_sig_neg]
      ring
    have hA := QI_anti hkc hkd fun _ _ => le_rfl
    have hM := QI_mono hkc hkd fun _ _ => le_rfl
    intro c hc
    have a1 := hA hc h1mem hc.2
    have a2 := hM hc h1mem hc.2
    simp only [hh1, hhm] at a1 a2
    linarith
  have hsig_up : ∀ x ∈ Ioo (-1 : ℝ) 1, QI_sig x ≤ Real.sqrt (1 - x) := by
    intro x hx
    unfold QI_sig
    rw [QI_sqrt_mul ⟨hx.1.le, hx.2.le⟩, div_le_iff₀ Real.pi_pos]
    have hb : Real.sqrt (1 + x) ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (by linarith [hx.1] : (0 : ℝ) ≤ 1 + x),
        Real.sqrt_nonneg (1 + x), hx.2]
    have ha := Real.sqrt_nonneg (1 - x)
    nlinarith [Real.pi_gt_three]
  have hup : ∀ c ∈ Icc (-1 : ℝ) 1, h c ≤ QI_p32 c := by
    have hA : AntitoneOn (fun x => QI_p32 x - h x) (Icc (-1) 1) :=
      QI_anti (QI_p32_cont.continuousOn.sub hhc)
        (fun x hx => (QI_p32_hasDerivAt hx.2).sub (hhd x hx)) fun x hx => by
          have := hsig_up x hx
          have := Real.sqrt_nonneg (1 - x)
          linarith
    intro c hc
    have := hA hc h1mem hc.2
    simp only [hh1, QI_p32, sub_self, zero_mul] at this
    unfold QI_p32
    linarith
  have hlo : ∀ c ∈ Icc (-1 : ℝ) 1, (1 / 6) * QI_p32 c ≤ h c := by
    intro c hc
    rcases le_total 0 c with h0 | h0
    · have hA : AntitoneOn (fun x => h x - (1 / 6) * QI_p32 x) (Icc 0 1) := by
        refine QI_anti ((hhc.mono (Icc_subset_Icc (by norm_num) le_rfl)).sub
          (continuousOn_const.mul QI_p32_cont.continuousOn))
          (fun x hx => (hhd x ⟨by linarith [hx.1], hx.2⟩).sub
            ((QI_p32_hasDerivAt hx.2).const_mul (1 / 6))) fun x hx => ?_
        have hs : (1 / 2) * Real.sqrt (1 - x) ≤ QI_sig x := by
          unfold QI_sig
          rw [QI_sqrt_mul ⟨by linarith [hx.1], hx.2.le⟩, le_div_iff₀ Real.pi_pos]
          have hb : 1 ≤ Real.sqrt (1 + x) := by
            have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + x by linarith [hx.1])
            rwa [Real.sqrt_one] at this
          have ha := Real.sqrt_nonneg (1 - x)
          nlinarith [Real.pi_lt_four]
        have := Real.sqrt_nonneg (1 - x)
        linarith
      have := hA ⟨h0, hc.2⟩ ⟨by norm_num, le_rfl⟩ hc.2
      simp only [hh1, QI_p32, sub_self, zero_mul, mul_zero] at this
      unfold QI_p32
      linarith
    · have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have hh0 : h 0 = 1 / 2 := by
        have := hsym 0 h0mem
        rw [neg_zero] at this
        linarith
      have hc0 : h 0 ≤ h c := hanti.antitoneOn hc h0mem h0
      have hb : Real.sqrt (1 - c) ≤ 3 / 2 := by
        nlinarith [Real.sq_sqrt (by linarith [hc.2] : (0 : ℝ) ≤ 1 - c),
          Real.sqrt_nonneg (1 - c), hc.1]
      have : QI_p32 c ≤ 3 := by
        unfold QI_p32
        have : 1 - c ≤ 2 := by linarith [hc.1]
        have := Real.sqrt_nonneg (1 - c)
        nlinarith
      linarith
  exact ⟨hsym, hup, hlo, hanti⟩

/-- One side of the location estimate: if `h(b) = H(u)` with `u < b`, then
`b - u ≤ 4ε(1 - u²)`. -/
private lemma QI_loc1 {H h : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hhc : ContinuousOn h (Icc (-1) 1))
    (hhd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (-QI_sig c) c)
    (hsym : ∀ c ∈ Icc (-1 : ℝ) 1, h (-c) = 1 - h c) (hup : ∀ c ∈ Icc (-1 : ℝ) 1, h c ≤ QI_p32 c)
    (hlo : ∀ c ∈ Icc (-1 : ℝ) 1, (1 / 6) * QI_p32 c ≤ h c)
    (hi : ∀ c ∈ Icc (-1 : ℝ) 1, (1 - ε) * h c ≤ H c)
    (hiv : ∀ c ∈ Icc (-1 : ℝ) 1, 1 - H c ≤ (1 + ε) * (1 - h c))
    {u b : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) (hub : u < b)
    (hbu : h b = H u) : b - u ≤ 4 * ε * (1 - u ^ 2) := by
  have huI : u ∈ Icc (-1 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  -- `1 - b ≥ (1 - u)/4`
  have hb4 : (1 - u) / 4 ≤ 1 - b := by
    by_contra hcon
    have hlt := lt_of_not_ge hcon
    have h1 := QI_xsx_lt (by linarith [hb.2]) hlt
    rw [QI_sqrt_quarter] at h1
    have h2 : h b ≤ (1 - b) * Real.sqrt (1 - b) := hup b hb
    have h3 : (1 - ε) * h u ≤ h b := hbu ▸ hi u huI
    have h4 : (1 / 6) * ((1 - u) * Real.sqrt (1 - u)) ≤ h u := hlo u huI
    have h5 : 0 ≤ (1 - u) * Real.sqrt (1 - u) := by
      have : 0 ≤ 1 - u := by linarith [hu.2]
      positivity
    have h6 : 0 ≤ h u := le_trans (by positivity) h4
    nlinarith
  -- the mean value theorem on `[u, b]`
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope h (fun c => -QI_sig c) hub
    (hhc.mono (Icc_subset_Icc hu.1.le hb.2))
    (fun x hx => hhd x ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hb.2]⟩)
  have hξI : ξ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hξ.1, hu.1], by linarith [hξ.2, hb.2]⟩
  have hdiff : h u - h b = QI_sig ξ * (b - u) := by
    rw [eq_div_iff (by linarith)] at hξd
    linarith
  -- `σ(ξ) ≥ √(1 - u²)/π`
  have hX : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hsX := Real.sqrt_pos.2 hX
  have hsig : Real.sqrt (1 - u ^ 2) / Real.pi ≤ QI_sig ξ := by
    unfold QI_sig
    have h1 : (1 - u ^ 2) / 4 ≤ 1 - ξ ^ 2 := by
      have e1 : (1 - u) / 4 ≤ 1 - ξ := by linarith [hξ.2]
      have e2 : 1 + u ≤ 1 + ξ := by linarith [hξ.1]
      have : (1 - u ^ 2) / 4 = ((1 - u) / 4) * (1 + u) := by ring
      rw [this, show 1 - ξ ^ 2 = (1 - ξ) * (1 + ξ) by ring]
      exact mul_le_mul e1 e2 (by linarith [hu.1]) (by linarith [hξ.2])
    have h2 : Real.sqrt (1 - u ^ 2) / 2 ≤ Real.sqrt (1 - ξ ^ 2) := by
      rw [← QI_sqrt_quarter]
      exact Real.sqrt_le_sqrt h1
    rw [div_le_div_iff_of_pos_right Real.pi_pos]
    linarith
  -- `h(u) - H(u) ≤ ε min(h(u), 1 - h(u)) ≤ ε (1 - u²)^{3/2}`
  have hmin : h u - h b ≤ ε * ((1 - u ^ 2) * Real.sqrt (1 - u ^ 2)) := by
    rw [hbu]
    have k1 : h u - H u ≤ ε * h u := by linarith [hi u huI]
    have k2 : h u - H u ≤ ε * (1 - h u) := by linarith [hiv u huI]
    have k3 : h u ≤ (1 - u) * Real.sqrt (1 - u) := hup u huI
    have k4 : 1 - h u ≤ (1 + u) * Real.sqrt (1 + u) := by
      have := hup (-u) (QI_negIcc huI)
      rw [hsym u huI] at this
      unfold QI_p32 at this
      simpa [sub_neg_eq_add] using this
    rcases le_total u 0 with hu0 | hu0
    · -- `1 + u ≤ 1 - u`, `1 + u ≤ 1 - u²`
      have e : 1 + u ≤ 1 - u ^ 2 := by nlinarith [hu.1]
      have e' : Real.sqrt (1 + u) ≤ Real.sqrt (1 - u ^ 2) := Real.sqrt_le_sqrt e
      have : (1 + u) * Real.sqrt (1 + u) ≤ (1 - u ^ 2) * Real.sqrt (1 - u ^ 2) :=
        mul_le_mul e e' (Real.sqrt_nonneg _) hX.le
      nlinarith
    · have e : 1 - u ≤ 1 - u ^ 2 := by nlinarith [hu.2]
      have e' : Real.sqrt (1 - u) ≤ Real.sqrt (1 - u ^ 2) := Real.sqrt_le_sqrt e
      have : (1 - u) * Real.sqrt (1 - u) ≤ (1 - u ^ 2) * Real.sqrt (1 - u ^ 2) :=
        mul_le_mul e e' (Real.sqrt_nonneg _) hX.le
      nlinarith
  rw [hdiff] at hmin
  have h7 : Real.sqrt (1 - u ^ 2) / Real.pi * (b - u) ≤
      ε * ((1 - u ^ 2) * Real.sqrt (1 - u ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hsig (by linarith)) hmin
  have h8 : b - u ≤ Real.pi * ε * (1 - u ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at h7
    have : Real.sqrt (1 - u ^ 2) * (b - u) ≤
        Real.sqrt (1 - u ^ 2) * (Real.pi * ε * (1 - u ^ 2)) := by linarith
    exact le_of_mul_le_mul_left this hsX
  have : Real.pi * ε * (1 - u ^ 2) ≤ 4 * ε * (1 - u ^ 2) := by
    have := Real.pi_lt_four
    have : 0 ≤ ε * (1 - u ^ 2) := mul_nonneg hε hX.le
    nlinarith
  linarith

/-- The location estimate `|b - u| ≤ 4ε(1 - u²)` when `h(b) = H(u)`. -/
private lemma QI_loc {H h : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hhc : ContinuousOn h (Icc (-1) 1))
    (hhd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (-QI_sig c) c)
    (hsym : ∀ c ∈ Icc (-1 : ℝ) 1, h (-c) = 1 - h c) (hup : ∀ c ∈ Icc (-1 : ℝ) 1, h c ≤ QI_p32 c)
    (hlo : ∀ c ∈ Icc (-1 : ℝ) 1, (1 / 6) * QI_p32 c ≤ h c)
    (hcmp : ∀ c ∈ Icc (-1 : ℝ) 1, (1 - ε) * h c ≤ H c ∧ H c ≤ (1 + ε) * h c ∧
      (1 - ε) * (1 - h c) ≤ 1 - H c ∧ 1 - H c ≤ (1 + ε) * (1 - h c))
    {u b : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) (hbu : h b = H u) :
    |b - u| ≤ 4 * ε * (1 - u ^ 2) := by
  have hX : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  rcases lt_trichotomy u b with hub | hub | hub
  · rw [abs_of_pos (by linarith)]
    exact QI_loc1 hε hε1 hhc hhd hsym hup hlo (fun c hc => (hcmp c hc).1)
      (fun c hc => (hcmp c hc).2.2.2) hu hb hub hbu
  · rw [← hub, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hε) hX
  · -- reflect: `H̃(c) = 1 - H(-c)`
    rw [abs_of_neg (by linarith)]
    have := QI_loc1 (H := fun c => 1 - H (-c)) hε hε1 hhc hhd hsym hup hlo
      (fun c hc => by
        have := (hcmp (-c) (QI_negIcc hc)).2.2.1
        have e := hsym c hc
        have e' : h (-c) = 1 - h c := e
        rw [e'] at this
        linarith)
      (fun c hc => by
        have := (hcmp (-c) (QI_negIcc hc)).2.1
        have e' : h (-c) = 1 - h c := hsym c hc
        rw [e'] at this
        linarith)
      (QI_negIoo hu) (QI_negIcc hb) (by linarith)
      (by rw [hsym b hb, hbu]; simp)
    rw [neg_sq] at this
    linarith

/-- A choice of `b ∈ [-1, 1]` with `h(b) = y`. -/
private def QI_inv (h : ℝ → ℝ) (y : ℝ) : ℝ :=
  if hy : ∃ b ∈ Icc (-1 : ℝ) 1, h b = y then hy.choose else 0

private lemma QI_inv_spec {h : ℝ → ℝ} (hhc : ContinuousOn h (Icc (-1) 1)) (hh1 : h 1 = 0)
    (hhm : h (-1) = 1) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    QI_inv h y ∈ Icc (-1 : ℝ) 1 ∧ h (QI_inv h y) = y := by
  have hex : ∃ b ∈ Icc (-1 : ℝ) 1, h b = y := by
    have := intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 1) hhc
      (show y ∈ Icc (h 1) (h (-1)) by rw [hh1, hhm]; exact hy)
    obtain ⟨b, hb, hb'⟩ := this
    exact ⟨b, hb, hb'⟩
  rw [QI_inv, dite_eq_left hex]
  exact hex.choose_spec

private lemma QI_inv_contAt {h : ℝ → ℝ} (hhc : ContinuousOn h (Icc (-1) 1))
    (hanti : StrictAntiOn h (Icc (-1) 1)) (hh1 : h 1 = 0) (hhm : h (-1) = 1) {y₀ : ℝ}
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) : ContinuousAt (QI_inv h) y₀ := by
  have hev : ∀ᶠ y in 𝓝 y₀, y ∈ Icc (0 : ℝ) 1 := Icc_mem_nhds hy₀.1 hy₀.2
  obtain ⟨hb₀, hhb₀⟩ := QI_inv_spec hhc hh1 hhm ⟨hy₀.1.le, hy₀.2.le⟩
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a ha
    by_cases ha1 : a < -1
    · filter_upwards [hev] with y hy
      exact lt_of_lt_of_le ha1 (QI_inv_spec hhc hh1 hhm hy).1.1
    · have haI : a ∈ Icc (-1 : ℝ) 1 := ⟨le_of_not_gt ha1, by linarith [hb₀.2]⟩
      have hlt : y₀ < h a := by
        have := hanti haI hb₀ ha
        rwa [hhb₀] at this
      filter_upwards [hev, eventually_lt_nhds hlt] with y hy hyl
      obtain ⟨hb, hhb⟩ := QI_inv_spec hhc hh1 hhm hy
      by_contra hle
      have := hanti.antitoneOn hb haI (le_of_not_gt hle)
      rw [hhb] at this
      linarith
  · intro a ha
    by_cases ha1 : 1 < a
    · filter_upwards [hev] with y hy
      exact lt_of_le_of_lt (QI_inv_spec hhc hh1 hhm hy).1.2 ha1
    · have haI : a ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hb₀.1], le_of_not_gt ha1⟩
      have hlt : h a < y₀ := by
        have := hanti hb₀ haI ha
        rwa [hhb₀] at this
      filter_upwards [hev, eventually_gt_nhds hlt] with y hy hyl
      obtain ⟨hb, hhb⟩ := QI_inv_spec hhc hh1 hhm hy
      by_contra hle
      have := hanti.antitoneOn haI hb (le_of_not_gt hle)
      rw [hhb] at this
      linarith

private lemma QI_inv_mem {h : ℝ → ℝ} (hhc : ContinuousOn h (Icc (-1) 1)) (hh1 : h 1 = 0)
    (hhm : h (-1) = 1) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : QI_inv h y ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨hb, hhb⟩ := QI_inv_spec hhc hh1 hhm ⟨hy.1.le, hy.2.le⟩
  refine ⟨lt_of_le_of_ne hb.1 fun e => ?_, lt_of_le_of_ne hb.2 fun e => ?_⟩
  · rw [← e, hhm] at hhb
    linarith [hy.2]
  · rw [e, hh1] at hhb
    linarith [hy.1]

private lemma QI_inv_hasDerivAt {h : ℝ → ℝ} (hhc : ContinuousOn h (Icc (-1) 1))
    (hhd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (-QI_sig c) c)
    (hanti : StrictAntiOn h (Icc (-1) 1)) (hh1 : h 1 = 0) (hhm : h (-1) = 1) {y₀ : ℝ}
    (hy₀ : y₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (QI_inv h) (-QI_sig (QI_inv h y₀))⁻¹ y₀ := by
  have hm := QI_inv_mem hhc hh1 hhm hy₀
  have hev : ∀ᶠ y in 𝓝 y₀, y ∈ Icc (0 : ℝ) 1 := Icc_mem_nhds hy₀.1 hy₀.2
  refine HasDerivAt.of_local_left_inverse (QI_inv_contAt hhc hanti hh1 hhm hy₀) (hhd _ hm)
    (by linarith [QI_sig_pos hm]) ?_
  filter_upwards [hev] with y hy
  exact (QI_inv_spec hhc hh1 hhm hy).2

/-- `|w σ(u)/σ(b) - 1| ≤ 11ε` when `|b - u| ≤ 4ε(1 - u²)` and `|w - 1| ≤ ε`. -/
private lemma QI_ratio {u b w ε : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hbI : b ∈ Icc (-1 : ℝ) 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hb : |b - u| ≤ 4 * ε * (1 - u ^ 2))
    (hw : |w - 1| ≤ ε) : |w * QI_sig u / QI_sig b - 1| ≤ 11 * ε := by
  set X := 1 - u ^ 2 with hXd
  set Y := 1 - b ^ 2 with hYd
  have hX : 0 < X := by nlinarith [hu.1, hu.2]
  have hub : |u + b| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hbI.1, hbI.2]
  have hYX : |Y - X| ≤ 8 * ε * X := by
    have : Y - X = (u - b) * (u + b) := by rw [hXd, hYd]; ring
    rw [this, abs_mul, abs_sub_comm]
    have := abs_nonneg (b - u)
    calc |b - u| * |u + b| ≤ (4 * ε * X) * 2 := by
          gcongr
      _ = 8 * ε * X := by ring
  have hY : (1 - 8 * ε) * X ≤ Y := by
    have := (abs_le.1 hYX).1
    linarith
  have hYp : 0 < Y := lt_of_lt_of_le (by nlinarith) hY
  have hsY := Real.sqrt_pos.2 hYp
  have e : w * QI_sig u / QI_sig b = w * Real.sqrt (X / Y) := by
    have e1 : QI_sig u = 2 * Real.sqrt X / Real.pi := rfl
    have e2 : QI_sig b = 2 * Real.sqrt Y / Real.pi := rfl
    rw [e1, e2, Real.sqrt_div hX.le]
    have := Real.pi_pos.ne'
    field_simp
  rw [e]
  set t := X / Y with htd
  have ht0 : 0 ≤ t := div_nonneg hX.le hYp.le
  have ht : |t - 1| ≤ 9 * ε := by
    have : t - 1 = (X - Y) / Y := by rw [htd]; field_simp
    rw [this, abs_div, abs_of_pos hYp, abs_sub_comm, div_le_iff₀ hYp]
    have : 0 ≤ ε * X := mul_nonneg hε hX.le
    nlinarith
  have hst : |Real.sqrt t - 1| ≤ 9 * ε := by
    have h1 : Real.sqrt t - 1 = (t - 1) / (Real.sqrt t + 1) := by
      have : Real.sqrt t + 1 ≠ 0 := by positivity
      field_simp
      linear_combination Real.mul_self_sqrt ht0
    rw [h1, abs_div, abs_of_pos (by positivity : 0 < Real.sqrt t + 1)]
    calc |t - 1| / (Real.sqrt t + 1) ≤ |t - 1| / 1 := by
          gcongr
          linarith [Real.sqrt_nonneg t]
      _ ≤ 9 * ε := by rw [div_one]; exact ht
  have hsle : Real.sqrt t ≤ 1 + 9 * ε := by linarith [(abs_le.1 hst).2]
  have e2 : w * Real.sqrt t - 1 = (w - 1) * Real.sqrt t + (Real.sqrt t - 1) := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
  have : |w - 1| * Real.sqrt t ≤ ε * (1 + 9 * ε) :=
    mul_le_mul hw hsle (Real.sqrt_nonneg t) hε
  nlinarith

/-- The increment of `u - b(u)`, where `h(b(u)) = H(u)`, is at most `11ε|u - v|`. -/
private lemma QI_incr {H h w : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 100)
    (hHc : ContinuousOn H (Icc (-1) 1)) (hhc : ContinuousOn h (Icc (-1) 1))
    (hHd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt H (-(w c * QI_sig c)) c)
    (hhd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (-QI_sig c) c)
    (hw : ∀ c ∈ Ioo (-1 : ℝ) 1, |w c - 1| ≤ ε)
    (hH1 : H 1 = 0) (hh1 : h 1 = 0) (hHm : H (-1) = 1) (hhm : h (-1) = 1)
    {u v bu bv : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hv : v ∈ Ioo (-1 : ℝ) 1)
    (hbu : bu ∈ Icc (-1 : ℝ) 1) (hbv : bv ∈ Icc (-1 : ℝ) 1) (hbu' : h bu = H u)
    (hbv' : h bv = H v) : |(u - bu) - (v - bv)| ≤ 11 * ε * |u - v| := by
  obtain ⟨hsym, hup, hlo, hanti⟩ := QI_hfacts hhc hhd hh1 hhm
  have hcmp := QI_cmp hHc hhc hHd hhd hw hH1 hh1 hHm hhm
  have h1mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hmmem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  -- `H(x) ∈ (0, 1)` inside
  have hHI : ∀ x ∈ Ioo (-1 : ℝ) 1, H x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have a1 : 0 < h x := by
      have := hanti hxI h1mem hx.2
      rwa [hh1] at this
    have a2 : h x < 1 := by
      have := hanti hmmem hxI hx.1
      rwa [hhm] at this
    have := hcmp x hxI
    constructor <;> nlinarith
  set ψ := fun x => QI_inv h (H x) with hψ
  have hψd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x => x - ψ x)
      (1 - (-QI_sig (ψ x))⁻¹ * (-(w x * QI_sig x))) x := fun x hx =>
    (hasDerivAt_id x).sub ((QI_inv_hasDerivAt hhc hhd hanti hh1 hhm (hHI x hx)).comp x
      (hHd x hx))
  have hψb : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ b ∈ Icc (-1 : ℝ) 1, h b = H x → ψ x = b := by
    intro x hx b hb hhb
    obtain ⟨hm, hhm'⟩ := QI_inv_spec hhc hh1 hhm ⟨(hHI x hx).1.le, (hHI x hx).2.le⟩
    exact hanti.injOn hm hb (hhm'.trans hhb.symm)
  have hder : ∀ x ∈ Ioo (-1 : ℝ) 1,
      |1 - (-QI_sig (ψ x))⁻¹ * (-(w x * QI_sig x))| ≤ 11 * ε := by
    intro x hx
    obtain ⟨hm, hhm'⟩ := QI_inv_spec hhc hh1 hhm ⟨(hHI x hx).1.le, (hHI x hx).2.le⟩
    have hloc := QI_loc hε (by linarith) hhc hhd hsym hup hlo hcmp hx hm hhm'
    have := QI_ratio hx hm hε hε1 hloc (hw x hx)
    have hs := QI_sig_pos (QI_inv_mem hhc hh1 hhm (hHI x hx))
    rw [abs_sub_comm]
    convert this using 2
    simp only [hψ]
    field_simp
  rw [← hψb u hu bu hbu hbu', ← hψb v hv bv hbv hbv']
  -- mean value theorem on the segment
  have key : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 → a < b →
      |(b - ψ b) - (a - ψ a)| ≤ 11 * ε * |b - a| := by
    intro a b ha hb hab
    have hsub : Icc a b ⊆ Ioo (-1 : ℝ) 1 := fun x hx =>
      ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun x => x - ψ x)
      (fun x => 1 - (-QI_sig (ψ x))⁻¹ * (-(w x * QI_sig x))) hab
      (fun x hx => (hψd x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => hψd x (hsub (Ioo_subset_Icc_self hx)))
    have hξI : ξ ∈ Ioo (-1 : ℝ) 1 := hsub (Ioo_subset_Icc_self hξ)
    have e : (b - ψ b) - (a - ψ a) =
        (1 - (-QI_sig (ψ ξ))⁻¹ * (-(w ξ * QI_sig ξ))) * (b - a) := by
      rw [hξd]
      field_simp [(by linarith : b - a ≠ 0)]
    rw [e, abs_mul]
    gcongr
    exact hder ξ hξI
  rcases lt_trichotomy u v with huv | huv | huv
  · have := key u v hu hv huv
    rw [abs_sub_comm, abs_sub_comm u v]
    exact this
  · rw [huv]
    simp
  · exact key v u hv hu huv

/-- The tail decreases at least at rate `(9/10)(2/π)√((1 - v)(1 + u))` on `[u, v]`. -/
private lemma QI_Hslope {H w : ℝ → ℝ} {ε : ℝ} (hε1 : ε ≤ 1 / 10)
    (hHc : ContinuousOn H (Icc (-1) 1))
    (hHd : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt H (-(w c * QI_sig c)) c)
    (hw : ∀ c ∈ Ioo (-1 : ℝ) 1, |w c - 1| ≤ ε) {u v : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1)
    (hv : v ∈ Ioo (-1 : ℝ) 1) (huv : u < v) :
    (9 / 10) * (2 * Real.sqrt ((1 - v) * (1 + u)) / Real.pi) * (v - u) ≤ H u - H v := by
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope H (fun c => -(w c * QI_sig c)) huv
    (hHc.mono (Icc_subset_Icc hu.1.le hv.2.le))
    (fun x hx => hHd x ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hv.2]⟩)
  have hξI : ξ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hξ.1, hu.1], by linarith [hξ.2, hv.2]⟩
  have hdiff : H u - H v = w ξ * QI_sig ξ * (v - u) := by
    rw [eq_div_iff (by linarith)] at hξd
    linarith
  have hwl : 9 / 10 ≤ w ξ := by have := (abs_le.1 (hw ξ hξI)).1; linarith
  have hs : 2 * Real.sqrt ((1 - v) * (1 + u)) / Real.pi ≤ QI_sig ξ := by
    unfold QI_sig
    gcongr
    rw [show 1 - ξ ^ 2 = (1 - ξ) * (1 + ξ) by ring]
    exact mul_le_mul (by linarith [hξ.2]) (by linarith [hξ.1]) (by linarith [hu.1])
      (by linarith [hξ.2, hv.2])
  rw [hdiff]
  have h0 : 0 ≤ 2 * Real.sqrt ((1 - v) * (1 + u)) / Real.pi := by
    have := Real.pi_pos
    positivity
  have : 0 ≤ v - u := by linarith
  calc (9 / 10) * (2 * Real.sqrt ((1 - v) * (1 + u)) / Real.pi) * (v - u)
      ≤ w ξ * QI_sig ξ * (v - u) := by gcongr

end QICmp

section QITail
open Set

/-- The tail `F(x) = ∫_x^∞ ρ`. -/
private def QI_F (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Ioi x, ρ t

private lemma QI_F_eq {ρ : ℝ → ℝ} (hρi : Integrable ρ) {b : ℝ} (hz : ∀ t, b < t → ρ t = 0)
    (x : ℝ) : QI_F ρ x = ∫ t in x..b, ρ t := by
  unfold QI_F
  rcases le_total x b with hxb | hxb
  · have h0 : ∫ t in Ioi b, ρ t = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t ht
    rw [← Ioc_union_Ioi_eq_Ioi hxb, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hρi.integrableOn hρi.integrableOn, h0, add_zero,
      intervalIntegral.integral_of_le hxb]
  · have h0 : ∫ t in Ioi x, ρ t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t (lt_of_le_of_lt hxb ht)
    have h1 : ∫ t in Ioc b x, ρ t = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t ht.1
    rw [h0, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxb, h1, neg_zero]

private lemma QI_F_hasDerivAt {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρi : Integrable ρ) {b : ℝ}
    (hz : ∀ t, b < t → ρ t = 0) (x : ℝ) : HasDerivAt (QI_F ρ) (-ρ x) x := by
  have e : QI_F ρ = fun y => -∫ t in b..y, ρ t := by
    funext y
    rw [QI_F_eq hρi hz y, intervalIntegral.integral_symm]
  rw [e]
  exact (hρc.integral_hasStrictDerivAt b x).hasDerivAt.neg

private lemma QI_F_left {ρ : ℝ → ℝ} (hρi : Integrable ρ) (hρ1 : ∫ t, ρ t = 1) {a b : ℝ}
    (hz : ∀ t, t ∉ Ioo a b → ρ t = 0) : QI_F ρ a = 1 := by
  rw [QI_F_eq hρi (b := b) (fun t (ht : b < t) => hz t fun h => by linarith [h.2]) a,
    intervalIntegral.integral_eq_integral_of_support_subset, hρ1]
  intro t ht
  by_contra h
  exact ht (hz t fun h' => h ⟨h'.1, h'.2.le⟩)

private lemma QI_F_right {ρ : ℝ → ℝ} (hρi : Integrable ρ) {b : ℝ}
    (hz : ∀ t, b < t → ρ t = 0) : QI_F ρ b = 0 := by
  rw [QI_F_eq hρi hz b, intervalIntegral.integral_same]

/-- The quantile `sSup {x : p ≤ F(x)}` is the point `x₀ ∈ (a, b)` with `F(x₀) = p`. -/
private lemma QI_sSup {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρi : Integrable ρ)
    (hρ0 : ∀ t, 0 ≤ ρ t) {a b : ℝ} (hz : ∀ t, b < t → ρ t = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < ρ t) {x₀ p : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hp : QI_F ρ x₀ = p) :
    sSup {x : ℝ | p ≤ ∫ t in Ioi x, ρ t} = x₀ := by
  have hd := QI_F_hasDerivAt hρc hρi hz
  have hanti : Antitone (QI_F ρ) :=
    antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => by
      rw [(hd x).deriv]; linarith [hρ0 x]
  have hsanti : StrictAntiOn (QI_F ρ) (Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    linarith [hpos x hx]
  refine IsGreatest.csSup_eq ⟨?_, fun x hx => ?_⟩
  · change p ≤ QI_F ρ x₀
    rw [hp]
  · by_contra hlt
    have hlt := lt_of_not_ge hlt
    have hx' : p ≤ QI_F ρ x := hx
    have hx₀I : x₀ ∈ Icc a b := ⟨hx₀.1.le, hx₀.2.le⟩
    rcases le_total x b with hxb | hxb
    · have := hsanti hx₀I ⟨by linarith [hx₀.1], hxb⟩ hlt
      linarith
    · have h1 := hanti hxb
      have h2 := hsanti hx₀I ⟨hx₀.1.le.trans hx₀.2.le, le_rfl⟩ hx₀.2
      linarith

end QITail

section QISpec

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def QI_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma QI_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    QI_cd U d * QI_cd U e = QI_cd U (fun j => d j * e j) := by
  rw [QI_cd, QI_cd, QI_cd, ← map_mul, diagonal_mul_diagonal]

private lemma QI_cd_one (U : Matrix.unitaryGroup ι ℂ) : QI_cd U (fun _ => 1) = 1 := by
  rw [QI_cd, diagonal_one, map_one]

private lemma QI_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • QI_cd U d = QI_cd U (fun j => c * d j) := by
  rw [QI_cd, QI_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma QI_cd_sub (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    QI_cd U d - QI_cd U e = QI_cd U (fun j => d j - e j) := by
  rw [QI_cd, QI_cd, QI_cd, ← map_sub, diagonal_sub]

private lemma QI_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    QI_cd U d - c • (1 : Matrix ι ι ℂ) = QI_cd U (fun j => d j - c) := by
  rw [← QI_cd_one U, QI_cd_smul, QI_cd_sub]
  simp

private lemma QI_cd_conjTranspose (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    (QI_cd U d)ᴴ = QI_cd U (fun j => star (d j)) := by
  rw [← star_eq_conjTranspose, QI_cd, QI_cd, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose]
  rfl

private lemma QI_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (QI_cd U d) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d j := by
  rw [ntr, QI_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]

private lemma QI_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (QI_cd U d)⁻¹ = QI_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [QI_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact QI_cd_one U

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma QI_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
    |hΛ.eigenvalues j| ≤ opNorm Λ := by
  have hv : ‖hΛ.eigenvectorBasis j‖ = 1 := hΛ.eigenvectorBasis.norm_eq_one j
  have hT : Matrix.toEuclideanCLM (𝕜 := ℂ) Λ (hΛ.eigenvectorBasis j) =
      ((hΛ.eigenvalues j : ℂ)) • hΛ.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, hΛ.mulVec_eigenvectorBasis, WithLp.ofLp_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have := (Matrix.toEuclideanCLM (𝕜 := ℂ) Λ).le_opNorm (hΛ.eigenvectorBasis j)
  rw [hT, norm_smul, hv, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-- A Hermitian matrix is `U diag(μ) U^*` with real `μ`, `|μ_j| ≤ ‖Λ‖`. -/
private lemma QI_decomp {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ),
      Λ = QI_cd U (fun j => (μ j : ℂ)) ∧ ∀ j, |μ j| ≤ opNorm Λ :=
  ⟨_, _, hΛ.spectral_theorem, QI_eig_le hΛ⟩

private lemma QI_ne_of_im (x : ℝ) {w : ℂ} (h : 0 < w.im) : (x : ℂ) - w ≠ 0 := by
  intro e
  have := congrArg Complex.im e
  simp at this
  linarith

end QISpec

section QILam
open scoped Matrix.Norms.L2Operator

/-- The embedding of the `N`-dimensional space as the `a`-th block. -/
private def QI_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma QI_J_conj_mul (D N : ℕ) (a : Fin D) : (QI_J D N a)ᴴ * QI_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, QI_J, Matrix.of_apply, Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma QI_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖QI_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (QI_J D N a)
  rw [QI_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖QI_J D N a‖ := norm_nonneg _
  nlinarith

private lemma QI_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖QI_J D N a * M * (QI_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := QI_J_norm D N hN a
  have hb := QI_J_norm D N hN b
  calc ‖QI_J D N a * M * (QI_J D N b)ᴴ‖ ≤ ‖QI_J D N a * M‖ * ‖(QI_J D N b)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖QI_J D N a‖ * ‖M‖) * ‖(QI_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma QI_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (QI_J D N a * M * (QI_J D N b)ᴴ) p q = if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, QI_J, Prod.ext_iff, h1, h2]

private lemma QI_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then QI_J D N a * A * (QI_J D N b)ᴴ else 0) +
        (if fwd D b a then QI_J D N a * Aᴴ * (QI_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D, (if fwd D a b then QI_J D N a * A * (QI_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, QI_block_apply]
  have e2 : ∀ a b : Fin D, (if fwd D b a then QI_J D N a * Aᴴ * (QI_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, QI_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖lam D N A‖ ≤ 2D²‖A‖`. -/
private lemma QI_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [QI_lam_eq]
  have hb : ∀ a b : Fin D, ‖(if fwd D a b then QI_J D N a * A * (QI_J D N b)ᴴ else 0) +
      (if fwd D b a then QI_J D N a * Aᴴ * (QI_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then QI_J D N a * A * (QI_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact QI_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then QI_J D N a * Aᴴ * (QI_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (QI_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end QILam

section QILam2

private lemma QI_lam_diag (D N : ℕ) (_hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) (p : Idx D N) :
    lam D N A p p = 0 := by
  have h : ¬ fwd D p.1 p.1 := by
    unfold fwd
    rintro (h | ⟨h3, h1, h0⟩)
    · omega
    · omega
  simp [lam, h]

private lemma QI_ntr_lam (D N : ℕ) (hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) :
    ntr (lam D N A) = 0 := by
  simp [ntr, Matrix.trace, QI_lam_diag D N hD]

/-- `⟨Λ²⟩ ≤ 4D ‖A‖²_HS / N` for `Λ = lam D N A`. -/
private lemma QI_avgSq_lam (D N : ℕ) (_hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    avgSq (lam D N A) ≤ 4 * D * hsNorm A ^ 2 / N := by
  have hH := lam_isHermitian D N A
  set Λ := lam D N A
  have hn : (Fintype.card (Idx D N) : ℝ) = D * N := by simp
  have hDN : (0 : ℝ) < D * N := by
    have : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  -- `⟨Λ²⟩ = (DN)⁻¹ Σ_{p,q} |Λ_pq|²`
  have e : avgSq Λ = ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 := by
    unfold avgSq ntr
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    have : ∀ p q : Idx D N, Λ p q * Λ q p = ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) := by
      intro p q
      have : Λ q p = star (Λ p q) := by
        have := congrFun (congrFun hH.eq q) p
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
        ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) = ((((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 : ℝ) : ℂ) by
      push_cast [Fintype.card_prod, Fintype.card_fin]; ring]
    rw [Complex.ofReal_re]
  -- each entry
  have hent : ∀ p q : Idx D N, ‖Λ p q‖ ^ 2 ≤ 2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
    intro p q
    simp only [Λ, lam]
    have h1 : ‖(if fwd D p.1 q.1 then A p.2 q.2 else 0)‖ ≤ ‖A p.2 q.2‖ := by
      split_ifs <;> simp
    have h2 : ‖(if fwd D q.1 p.1 then star (A q.2 p.2) else 0)‖ ≤ ‖A q.2 p.2‖ := by
      split_ifs <;> simp
    set x := (if fwd D p.1 q.1 then A p.2 q.2 else 0)
    set y := (if fwd D q.1 p.1 then star (A q.2 p.2) else 0)
    have hxy := norm_add_le x y
    have h3 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    have h1' : ‖x‖ ^ 2 ≤ ‖A p.2 q.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖y‖ ^ 2 ≤ ‖A q.2 p.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have key : ∀ g : Fin N → Fin N → ℝ, ∑ p : Idx D N, ∑ q : Idx D N, g p.2 q.2 =
      (D : ℝ) ^ 2 * ∑ i, ∑ j, g i j := by
    intro g
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsum : ∑ p : Idx D N, ∑ q : Idx D N, (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) =
      2 * (D : ℝ) ^ 2 * hsNorm A ^ 2 := by
    have hs : hsNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
      unfold hsNorm; rw [Real.sq_sqrt (by positivity)]
    simp only [Finset.sum_add_distrib]
    rw [key (fun i j => ‖A i j‖ ^ 2), key (fun i j => ‖A j i‖ ^ 2), hs,
      Finset.sum_comm (f := fun i j => ‖A j i‖ ^ 2)]
    ring
  rw [e]
  calc ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2
      ≤ ((D : ℝ) * N)⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
          2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
        gcongr with p _ q _; exact hent p q
    _ = 4 * D * hsNorm A ^ 2 / N := by
        simp only [← Finset.mul_sum]
        rw [hsum]
        field_simp
        ring

end QILam2


section QIIdent
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ρ_N(E) = π⁻¹ Im m(E)` for the boundary value `m(E)` of Definition 2.7 [defn_Mm]. -/
private lemma QI_rho_eq [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (E : ℝ) : rho Λ E = (mExt Λ E).im / Real.pi := by
  obtain ⟨hc, -⟩ := mExt_boundary Λ hΛ hℓ
  have hmem : (E : ℂ) ∈ {z : ℂ | 0 ≤ z.im} := by simp
  have h1 : Tendsto (fun η : ℝ => (E : ℂ) + (η : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (E : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc' : Continuous (fun η : ℝ => (E : ℂ) + (η : ℂ) * Complex.I) := by fun_prop
      have h := hc'.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      have : 0 < η := hη
      change 0 ≤ ((E : ℂ) + (η : ℂ) * Complex.I).im
      simp [this.le]
  have h2 : Tendsto (fun η : ℝ => mExt Λ ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (mExt Λ E)) := (hc _ hmem).tendsto.comp h1
  have h3 : Tendsto (fun η : ℝ => (mSol Λ ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (mExt Λ E).im) := by
    refine ((Complex.continuous_im.tendsto _).comp h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have him : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
    simp only [Function.comp, mExt, him, ↓reduceIte]
  unfold rho
  rw [h3.limUnder_eq]

/-- On `(E⁻, E⁺)`, by (2.16) [self_m] and (A.4) [equation_E_in_spectrum], with
`ω = E + m(E) = r(c + i√(1-c²))`: `r = R(c)`, `E = E(c)` and
`ρ_N(E) = R(c)√(1-c²)/π`. -/
private lemma QI_ident [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ)
    (hdec : Λ = QI_cd U (fun j => (μ j : ℂ))) (hμ : ∀ j, |μ j| ≤ 1 / 10) {E : ℝ}
    (hE : E ∈ Ioo (Eminus Λ) (Eplus Λ)) :
    ∃ c ∈ Ioo (-1 : ℝ) 1, QI_E μ c = E ∧
      rho Λ E = QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi := by
  obtain ⟨-, hb⟩ := mExt_boundary Λ hΛ hℓ
  obtain ⟨hnorm, hm, -⟩ := hb E
  obtain ⟨hρ0, -⟩ := rho_stieltjes Λ hΛ hℓ
  obtain ⟨-, hsupp⟩ := rho_support Λ hΛ hℓ
  have hρeq := QI_rho_eq Λ hΛ hℓ E
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, (E : ℂ) + mExt Λ E = ω := ⟨_, rfl⟩
  have hωre : ω.re = E + (mExt Λ E).re := by rw [← hω]; simp
  have hωim : ω.im = (mExt Λ E).im := by rw [← hω]; simp
  have hρE : 0 < rho Λ E := by
    have hs : E ∈ Function.support (rho Λ) := by rw [hsupp]; exact hE
    exact lt_of_le_of_ne (hρ0 E) (Ne.symm hs)
  have hy : 0 < ω.im := by
    rw [hωim]
    rw [hρeq] at hρE
    exact (div_pos_iff_of_pos_right Real.pi_pos).1 hρE
  have hne : ∀ j, (μ j : ℂ) - ω ≠ 0 := fun j => QI_ne_of_im (μ j) hy
  have hL : Λ - ω • (1 : Matrix ι ι ℂ) = QI_cd U (fun j => (μ j : ℂ) - ω) := by
    rw [hdec, QI_cd_sub_smul_one]
  have hM : MExt Λ E = QI_cd U (fun j => ((μ j : ℂ) - ω)⁻¹) := by
    change (Λ - ((E : ℂ) + mExt Λ E) • (1 : Matrix ι ι ℂ))⁻¹ = _
    rw [hω, hL, QI_cd_inv _ _ hne]
  set x := ω.re with hxd
  set y := ω.im with hyd
  have hdj : ∀ j, Complex.normSq ((μ j : ℂ) - ω) = (μ j - x) ^ 2 + y ^ 2 := by
    intro j
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring
  have hdpos : ∀ j, 0 < (μ j - x) ^ 2 + y ^ 2 := fun j => by positivity
  -- `⟨M M^*⟩ = 1`
  have hMM := equation_E_in_spectrum Λ hΛ hℓ E ⟨hE.1.le, hE.2.le⟩
  rw [hM, QI_cd_conjTranspose, QI_cd_mul, QI_ntr_cd] at hMM
  have hQ1 : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, 1 / ((μ j - x) ^ 2 + y ^ 2) = 1 := by
    have e : ∀ j, ((μ j : ℂ) - ω)⁻¹ * star (((μ j : ℂ) - ω)⁻¹) =
        ((1 / ((μ j - x) ^ 2 + y ^ 2) : ℝ) : ℂ) := by
      intro j
      rw [Complex.star_def, Complex.mul_conj, map_inv₀, hdj]
      push_cast
      ring
    have h2 : ((((Fintype.card ι : ℝ))⁻¹ * ∑ j, 1 / ((μ j - x) ^ 2 + y ^ 2) : ℝ) : ℂ) = 1 := by
      rw [← hMM]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e j]
      push_cast
      ring
    exact_mod_cast h2
  -- `Re m`
  have hmre : (mExt Λ E).re = ((Fintype.card ι : ℝ))⁻¹ *
      ∑ j, (μ j - x) / ((μ j - x) ^ 2 + y ^ 2) := by
    rw [hm, hM, QI_ntr_cd]
    rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.inv_re, hdj]
    simp [hxd]
  -- polar coordinates
  set r := ‖ω‖ with hrd
  have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := by
    rw [hrd, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hr9 : 9 / 10 ≤ r := by
    have : ‖(E : ℂ) + mExt Λ E‖ = r := by rw [hω]
    rw [this] at hnorm
    linarith
  have hr0 : 0 < r := by linarith
  set c := x / r with hcd
  have hrc : r * c = x := by rw [hcd]; field_simp
  have hxr : |x| < r := abs_lt_of_sq_lt_sq (by nlinarith) hr0.le
  have hc1 : |c| < 1 := by
    rw [hcd, abs_div, abs_of_pos hr0, div_lt_one hr0]
    exact hxr
  have hcI : c ∈ Ioo (-1 : ℝ) 1 := ⟨(abs_lt.1 hc1).1, (abs_lt.1 hc1).2⟩
  have hdd : ∀ j, QI_dd (μ j) r c = (μ j - x) ^ 2 + y ^ 2 := by
    intro j
    unfold QI_dd
    have : 2 * r * μ j * c = 2 * μ j * (r * c) := by ring
    rw [this, hrc, hr2]
    ring
  have hQ : QI_Q μ r c = 1 := by
    unfold QI_Q QI_av
    simp only [hdd]
    exact hQ1
  have hrR : r = QI_R μ c := QI_R_unique μ hμ hc1.le hr9 hQ
  refine ⟨c, hcI, ?_, ?_⟩
  · unfold QI_E
    rw [← hrR, mul_assoc, hrc]
    unfold QI_av
    simp only [hdd]
    have e1 : E = x - (mExt Λ E).re := by rw [hωre]; ring
    rw [e1, hmre]
    have e2 : ∑ j, (μ j - x) / ((μ j - x) ^ 2 + y ^ 2) =
        (∑ j, μ j / ((μ j - x) ^ 2 + y ^ 2)) - x * ∑ j, 1 / ((μ j - x) ^ 2 + y ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := (hdpos j).ne'
      field_simp
    rw [e2]
    linear_combination (-x) * hQ1
  · rw [← hrR, hρeq, ← hωim]
    congr 1
    have h1c : 1 - c ^ 2 = (y / r) ^ 2 := by
      rw [hcd]
      field_simp
      linarith [hr2]
    rw [h1c, Real.sqrt_sq (by positivity)]
    field_simp

end QIIdent

section QIStruct
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `w(c) = R(c) E'(c)/2`: the tail of `ρ_N` in the variable `c` has derivative `-w σ`. -/
private def QI_w (μ : ι → ℝ) (c : ℝ) : ℝ := QI_R μ c * deriv (QI_E μ) c / 2

/-- `E(-1) = E⁻`, `E(1) = E⁺`, and `ρ_N(E(c)) = R(c)√(1-c²)/π` on `(-1, 1)`. -/
private lemma QI_ends [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ)
    (hdec : Λ = QI_cd U (fun j => (μ j : ℂ))) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) (hs : QI_av (fun j => μ j ^ 2) ≤ 1 / 1000) :
    QI_E μ (-1) = Eminus Λ ∧ QI_E μ 1 = Eplus Λ ∧
      ∀ c ∈ Ioo (-1 : ℝ) 1, QI_E μ c ∈ Ioo (Eminus Λ) (Eplus Λ) ∧
        rho Λ (QI_E μ c) = QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi := by
  have hA := fun E (hE : E ∈ Ioo (Eminus Λ) (Eplus Λ)) => QI_ident Λ hΛ hℓ U μ hdec hμ hE
  have hmono : ∀ c c' : ℝ, |c| ≤ 1 → |c'| ≤ 1 → c < c' → QI_E μ c < QI_E μ c' :=
    fun c c' hc hc' h => QI_E_strictMono μ hμ h0 hs hc hc' h
  have hinj : ∀ c c' : ℝ, |c| ≤ 1 → |c'| ≤ 1 → QI_E μ c = QI_E μ c' → c = c' := by
    intro c c' hc hc' he
    rcases lt_trichotomy c c' with h | h | h
    · have := hmono c c' hc hc' h; linarith
    · exact h
    · have := hmono c' c hc' hc h; linarith
  have hcont := QI_E_contOn μ hμ h0
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  obtain ⟨-, hρc, -⟩ := rho_stieltjes Λ hΛ hℓ
  have hzero : ∀ E, E ∉ Ioo (Eminus Λ) (Eplus Λ) → rho Λ E = 0 := fun E hE =>
    Function.notMem_support.1 (by rw [hsupp]; exact hE)
  have hm1 : |(-1 : ℝ)| ≤ 1 := by norm_num
  have hp1 : |(1 : ℝ)| ≤ 1 := by norm_num
  have habs : ∀ c ∈ Ioo (-1 : ℝ) 1, |c| ≤ 1 := fun c hc => abs_le.2 ⟨hc.1.le, hc.2.le⟩
  have hfpos : ∀ c ∈ Ioo (-1 : ℝ) 1, 0 < QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi := by
    intro c hc
    have h1 := (QI_R_spec μ hμ (habs c hc)).1
    have : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
    have := Real.sqrt_pos.2 this
    have := Real.pi_pos
    have : 0 < QI_R μ c := by linarith
    positivity
  -- the identity cannot reach an endpoint from inside
  have hcontra : ∀ cs ∈ Ioo (-1 : ℝ) 1, rho Λ (QI_E μ cs) = 0 → ∀ l : Filter ℝ, l.NeBot →
      l ≤ 𝓝 cs → (∀ᶠ c in l, rho Λ (QI_E μ c) =
        QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi) → False := by
    intro cs hcs hz l hl hle hev
    have hEc : ContinuousAt (QI_E μ) cs := hcont.continuousAt (Icc_mem_nhds hcs.1 hcs.2)
    have hRc : ContinuousAt (QI_R μ) cs := QI_R_contAt μ hμ h0 hcs
    have hg : ContinuousAt (fun c => rho Λ (QI_E μ c) -
        QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi) cs := by
      have h1 : ContinuousAt (fun c => rho Λ (QI_E μ c)) cs := hρc.continuousAt.comp hEc
      have h2 : ContinuousAt (fun c : ℝ => Real.sqrt (1 - c ^ 2)) cs := by fun_prop
      exact h1.sub ((hRc.mul h2).div_const _)
    have t1 := hg.tendsto.mono_left hle
    have t2 : Tendsto (fun c => rho Λ (QI_E μ c) -
        QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi) l (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun c hc => by simp only; rw [hc, sub_self])
    have := tendsto_nhds_unique t1 t2
    rw [hz, zero_sub, neg_eq_zero] at this
    exact (hfpos cs hcs).ne' this
  have hev_in : ∀ cs ∈ Ioo (-1 : ℝ) 1, ∀ c : ℝ, |c| ≤ 1 →
      QI_E μ c ∈ Ioo (Eminus Λ) (Eplus Λ) →
      rho Λ (QI_E μ c) = QI_R μ c * Real.sqrt (1 - c ^ 2) / Real.pi := by
    intro cs _ c hc hE
    obtain ⟨c₁, hc₁, hc₁E, hρ⟩ := hA _ hE
    have := hinj c₁ c (habs c₁ hc₁) hc hc₁E
    subst this
    exact hρ
  have s1 : QI_E μ (-1) ≤ Eminus Λ := by
    by_contra h
    have h := lt_of_not_ge h
    have hE : min (QI_E μ (-1)) ((Eminus Λ + Eplus Λ) / 2) ∈ Ioo (Eminus Λ) (Eplus Λ) :=
      ⟨lt_min h (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    obtain ⟨c, hc, hcE, -⟩ := hA _ hE
    have := hmono (-1) c hm1 (habs c hc) hc.1
    rw [hcE] at this
    linarith [min_le_left (QI_E μ (-1)) ((Eminus Λ + Eplus Λ) / 2)]
  have s2 : Eplus Λ ≤ QI_E μ 1 := by
    by_contra h
    have h := lt_of_not_ge h
    have hE : max (QI_E μ 1) ((Eminus Λ + Eplus Λ) / 2) ∈ Ioo (Eminus Λ) (Eplus Λ) :=
      ⟨lt_of_lt_of_le (by linarith) (le_max_right _ _), max_lt h (by linarith)⟩
    obtain ⟨c, hc, hcE, -⟩ := hA _ hE
    have := hmono c 1 (habs c hc) hp1 hc.2
    rw [hcE] at this
    linarith [le_max_left (QI_E μ 1) ((Eminus Λ + Eplus Λ) / 2)]
  have s3 : QI_E μ 1 ≤ Eplus Λ := by
    by_contra h
    have h := lt_of_not_ge h
    obtain ⟨cs, hcs, hcsE⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont
      (show Eplus Λ ∈ Icc (QI_E μ (-1)) (QI_E μ 1) from ⟨by linarith, h.le⟩)
    have hcsI : cs ∈ Ioo (-1 : ℝ) 1 := by
      refine ⟨lt_of_le_of_ne hcs.1 fun e => ?_, lt_of_le_of_ne hcs.2 fun e => ?_⟩
      · rw [← e] at hcsE; linarith
      · rw [e] at hcsE; linarith
    refine hcontra cs hcsI (by rw [hcsE]; exact hzero _ fun h' => lt_irrefl _ h'.2)
      (𝓝[<] cs) inferInstance nhdsWithin_le_nhds ?_
    have hEc : ContinuousAt (QI_E μ) cs := hcont.continuousAt (Icc_mem_nhds hcsI.1 hcsI.2)
    have hev1 : ∀ᶠ c in 𝓝 cs, Eminus Λ < QI_E μ c :=
      hEc.eventually (eventually_gt_nhds (by rw [hcsE]; exact hlt))
    filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds (QI_Icc_mem hcsI),
      self_mem_nhdsWithin] with c h1 h2 h3
    refine hev_in cs hcsI c h2 ⟨h1, ?_⟩
    rw [← hcsE]
    exact hmono c cs h2 (habs cs hcsI) h3
  have s4 : Eminus Λ ≤ QI_E μ (-1) := by
    by_contra h
    have h := lt_of_not_ge h
    obtain ⟨cs, hcs, hcsE⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont
      (show Eminus Λ ∈ Icc (QI_E μ (-1)) (QI_E μ 1) from ⟨h.le, by linarith⟩)
    have hcsI : cs ∈ Ioo (-1 : ℝ) 1 := by
      refine ⟨lt_of_le_of_ne hcs.1 fun e => ?_, lt_of_le_of_ne hcs.2 fun e => ?_⟩
      · rw [← e] at hcsE; linarith
      · rw [e] at hcsE; linarith
    refine hcontra cs hcsI (by rw [hcsE]; exact hzero _ fun h' => lt_irrefl _ h'.1)
      (𝓝[>] cs) inferInstance nhdsWithin_le_nhds ?_
    have hEc : ContinuousAt (QI_E μ) cs := hcont.continuousAt (Icc_mem_nhds hcsI.1 hcsI.2)
    have hev1 : ∀ᶠ c in 𝓝 cs, QI_E μ c < Eplus Λ :=
      hEc.eventually (eventually_lt_nhds (by rw [hcsE]; exact hlt))
    filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds (QI_Icc_mem hcsI),
      self_mem_nhdsWithin] with c h1 h2 h3
    refine hev_in cs hcsI c h2 ⟨?_, h1⟩
    rw [← hcsE]
    exact hmono cs c (habs cs hcsI) h2 h3
  have em : QI_E μ (-1) = Eminus Λ := le_antisymm s1 s4
  have ep : QI_E μ 1 = Eplus Λ := le_antisymm s3 s2
  refine ⟨em, ep, fun c hc => ?_⟩
  have hmem : QI_E μ c ∈ Ioo (Eminus Λ) (Eplus Λ) :=
    ⟨by rw [← em]; exact hmono (-1) c hm1 (habs c hc) hc.1,
      by rw [← ep]; exact hmono c 1 (habs c hc) hp1 hc.2⟩
  exact ⟨hmem, hev_in c hc c (habs c hc) hmem⟩

/-- The tail `H(c) = ∫_{E(c)}^∞ ρ_N` of (2.19) [eq:density_rhoN]: continuity, `H' = -wσ` with
`|w - 1| ≤ 140⟨Λ²⟩`, `H(1) = 0`, `H(-1) = 1`, and the quantile (2.20) [eq:gammak] is `E(c)` when
`H(c) = (q - 1/2)/DN`. -/
private lemma QI_struct [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ)
    (hdec : Λ = QI_cd U (fun j => (μ j : ℂ))) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (h0 : ∑ j, μ j = 0) (hs : QI_av (fun j => μ j ^ 2) ≤ 1 / 1000) :
    ContinuousOn (fun c => QI_F (rho Λ) (QI_E μ c)) (Icc (-1) 1) ∧
      (∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun c => QI_F (rho Λ) (QI_E μ c))
        (-(QI_w μ c * QI_sig c)) c) ∧
      (∀ c ∈ Ioo (-1 : ℝ) 1, |QI_w μ c - 1| ≤ 140 * QI_av (fun j => μ j ^ 2)) ∧
      QI_F (rho Λ) (QI_E μ 1) = 0 ∧ QI_F (rho Λ) (QI_E μ (-1)) = 1 ∧
      (∀ c ∈ Ioo (-1 : ℝ) 1, ∀ p : ℝ, QI_F (rho Λ) (QI_E μ c) = p →
        sSup {x : ℝ | p ≤ ∫ t in Ioi x, rho Λ t} = QI_E μ c) := by
  obtain ⟨hEm, hEp, hin⟩ := QI_ends Λ hΛ hℓ U μ hdec hμ h0 hs
  obtain ⟨hρ0, hρc, hρi, hρ1, -⟩ := rho_stieltjes Λ hΛ hℓ
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  have hzero : ∀ t, t ∉ Ioo (Eminus Λ) (Eplus Λ) → rho Λ t = 0 := fun t ht =>
    Function.notMem_support.1 (by rw [hsupp]; exact ht)
  have hz : ∀ t, Eplus Λ < t → rho Λ t = 0 := fun t ht =>
    hzero t fun h => by linarith [h.2]
  have hpos : ∀ t ∈ Ioo (Eminus Λ) (Eplus Λ), 0 < rho Λ t := by
    intro t ht
    have hs' : t ∈ Function.support (rho Λ) := by rw [hsupp]; exact ht
    exact lt_of_le_of_ne (hρ0 t) (Ne.symm hs')
  have hFd := QI_F_hasDerivAt hρc hρi hz
  have hFc : Continuous (QI_F (rho Λ)) :=
    continuous_iff_continuousAt.2 fun x => (hFd x).continuousAt
  have hsn : 0 ≤ QI_av (fun j => μ j ^ 2) := QI_av_nonneg fun j => sq_nonneg _
  refine ⟨hFc.comp_continuousOn (QI_E_contOn μ hμ h0), fun c hc => ?_, fun c hc => ?_, ?_, ?_,
    fun c hc p hp => QI_sSup hρc hρi hρ0 hz hpos (hin c hc).1 hp⟩
  · obtain ⟨e', he', -⟩ := QI_E_hasDerivAt μ hμ h0 hc
    have h := (hFd (QI_E μ c)).comp c he'
    rw [(hin c hc).2] at h
    refine h.congr_deriv ?_
    unfold QI_w QI_sig
    rw [he'.deriv]
    ring
  · obtain ⟨e', he', hle⟩ := QI_E_hasDerivAt μ hμ h0 hc
    unfold QI_w
    rw [he'.deriv]
    have hR := QI_R_sub_one μ hμ h0 (abs_le.2 ⟨hc.1.le, hc.2.le⟩)
    set s := QI_av (fun j => μ j ^ 2)
    have he1 : |e'| ≤ 2 + 250 * s := by
      have := abs_sub_abs_le_abs_sub e' 2
      rw [abs_two] at this
      linarith
    have e : QI_R μ c * e' / 2 - 1 = (QI_R μ c - 1) * e' / 2 + (e' - 2) / 2 := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_div, abs_mul, abs_two]
    have h1 : |QI_R μ c - 1| * |e'| ≤ (9 * s) * (2 + 250 * s) :=
      mul_le_mul hR he1 (abs_nonneg _) (by positivity)
    nlinarith
  · rw [hEp]
    exact QI_F_right hρi hz
  · rw [hEm]
    exact QI_F_left hρi hρ1 hzero

end QIStruct

private lemma QI_rpow_pow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) :
    (x ^ y) ^ n = x ^ (y * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

private lemma QI_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [QI_rpow_pow hx]
  norm_num

/-- If `z ≥ 0` and `z³ ≥ t³/(5b³)`, then `z ≥ t/(2b)`. -/
private lemma QI_cube_le {z t b : ℝ} (hz : 0 ≤ z) (ht : 0 ≤ t) (hb : 0 < b)
    (h : t ^ 3 / (5 * b ^ 3) ≤ z ^ 3) : t / (2 * b) ≤ z := by
  by_contra hlt
  have hlt := lt_of_not_ge hlt
  have h1 : z ^ 3 < (t / (2 * b)) ^ 3 := pow_lt_pow_left₀ hlt hz (by norm_num)
  have h2 : (t / (2 * b)) ^ 3 = t ^ 3 / (8 * b ^ 3) := by
    field_simp
    ring
  rw [h2] at h1
  have h3 : t ^ 3 / (8 * b ^ 3) ≤ t ^ 3 / (5 * b ^ 3) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_pos hb 3]
  linarith


open Set in
set_option maxHeartbeats 1000000 in
/-- `|c_i - c_k| ≤ (20π/9) a₃⁴/(t m₃²) + 8 a₃³/m₃³` for the points `H(c_q) = (q - 1/2)/M`,
`M = m₃³`, `k = t³`, `|i - k| ≤ a₃³`, `2k ≤ M + 1`. -/
private lemma QI_delta {H hh w : ℝ → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100)
    (hHc : ContinuousOn H (Set.Icc (-1) 1))
    (hHd : ∀ c ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt H (-(w c * QI_sig c)) c)
    (hHw : ∀ c ∈ Set.Ioo (-1 : ℝ) 1, |w c - 1| ≤ ε)
    (hcmp : ∀ c ∈ Set.Icc (-1 : ℝ) 1, (1 - ε) * hh c ≤ H c ∧ H c ≤ (1 + ε) * hh c ∧
      (1 - ε) * (1 - hh c) ≤ 1 - H c ∧ 1 - H c ≤ (1 + ε) * (1 - hh c))
    (hsym : ∀ c ∈ Set.Icc (-1 : ℝ) 1, hh (-c) = 1 - hh c)
    (hup : ∀ c ∈ Set.Icc (-1 : ℝ) 1, hh c ≤ QI_p32 c)
    (hh0 : ∀ c ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ hh c)
    {ci ck K Mr t m3 a3 : ℝ} {i : ℝ} (hci : ci ∈ Set.Ioo (-1 : ℝ) 1)
    (hck : ck ∈ Set.Ioo (-1 : ℝ) 1) (hMr0 : 0 < Mr) (hK1 : 1 ≤ K) (hiR : 1 ≤ i)
    (h2K : 2 * K ≤ Mr + 1) (hik : |i - K| ≤ a3 ^ 3) (ha31 : 1 ≤ a3) (ht0 : 0 < t)
    (hm30 : 0 < m3) (ht3 : t ^ 3 = K) (hm33 : m3 ^ 3 = Mr)
    (hHci : H ci = (i - 1 / 2) / Mr) (hHck : H ck = (K - 1 / 2) / Mr) :
    |ci - ck| ≤ (20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2) + 8 * a3 ^ 3 / m3 ^ 3 := by
  have ha30 : 0 < a3 := by linarith
  have hT0 : 0 ≤ (20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2) := by
    have := Real.pi_pos
    positivity
  have hS0 : 0 ≤ 8 * a3 ^ 3 / m3 ^ 3 := by positivity
  by_cases hcase : a3 ^ 3 ≤ Mr / 4
  · have hik' := abs_le.1 hik
    -- `1 + c ≥ 1/4` where `H(c) ≤ 3/4`
    have hplus : ∀ c ∈ Ioo (-1 : ℝ) 1, H c ≤ 3 / 4 → 1 / 4 ≤ 1 + c := by
      intro c hc hHc'
      have hcI : c ∈ Icc (-1 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
      have h1 := (hcmp c hcI).2.2.2
      have h2 := hup (-c) (QI_negIcc hcI)
      rw [hsym c hcI] at h2
      unfold QI_p32 at h2
      rw [sub_neg_eq_add] at h2
      by_contra hlt
      have hlt := lt_of_not_ge hlt
      have h3 := QI_xsx_lt (by linarith [hc.1]) hlt
      rw [show (1 : ℝ) / 4 = 1 / 4 from rfl, QI_sqrt_quarter, Real.sqrt_one] at h3
      nlinarith
    -- `(1 - c)^{3/2} ≥ k / (5 N^τ DN)` where `H(c) ≥ k / (4 N^τ DN)`
    have hminus : ∀ c ∈ Ioo (-1 : ℝ) 1, K / (4 * a3 ^ 3 * Mr) ≤ H c →
        t / (2 * (a3 * m3)) ≤ Real.sqrt (1 - c) := by
      intro c hc hHc'
      have hcI : c ∈ Icc (-1 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
      have h1 := (hcmp c hcI).2.1
      have h2 := hup c hcI
      unfold QI_p32 at h2
      have hz3 : Real.sqrt (1 - c) ^ 3 = (1 - c) * Real.sqrt (1 - c) := by
        rw [pow_succ, Real.sq_sqrt (by linarith [hc.2])]
      refine QI_cube_le (Real.sqrt_nonneg _) ht0.le (by positivity) ?_
      rw [hz3, mul_pow, ht3, hm33]
      have h4 : K / (4 * a3 ^ 3 * Mr) ≤ (101 / 100) * ((1 - c) * Real.sqrt (1 - c)) := by
        have := hh0 c hcI
        nlinarith
      have h5 : K / (5 * (a3 ^ 3 * Mr)) ≤ (100 / 101) * (K / (4 * a3 ^ 3 * Mr)) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [pow_pos ha30 3]
      linarith
    -- the values of `H` at `c_i`, `c_k`
    have hpi_le : H ci ≤ 3 / 4 := by
      rw [hHci, div_le_iff₀ hMr0]
      linarith
    have hpk_le : H ck ≤ 3 / 4 := by
      rw [hHck, div_le_iff₀ hMr0]
      linarith
    have hmin : K / (2 * a3 ^ 3) ≤ (i : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ a3 ^ 3 := one_le_pow₀ ha31
      rcases le_total K (2 * a3 ^ 3) with hK2 | hK2
      · nlinarith
      · nlinarith
    have hKa : K / (2 * a3 ^ 3) ≤ K := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ a3 ^ 3 := one_le_pow₀ ha31
      nlinarith
    have hpi_ge : K / (4 * a3 ^ 3 * Mr) ≤ H ci := by
      rw [hHci, div_le_div_iff₀ (by positivity) hMr0]
      have : K / (2 * a3 ^ 3) ≤ 2 * ((i : ℝ) - 1 / 2) := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    have hpk_ge : K / (4 * a3 ^ 3 * Mr) ≤ H ck := by
      rw [hHck, div_le_div_iff₀ (by positivity) hMr0]
      have : K / (2 * a3 ^ 3) ≤ 2 * (K - 1 / 2) := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    have hdiff : |H ci - H ck| ≤ a3 ^ 3 / Mr := by
      rw [hHci, hHck, ← sub_div, abs_div, abs_of_pos hMr0]
      gcongr
      have : (i : ℝ) - 1 / 2 - (K - 1 / 2) = i - K := by ring
      rw [this]
      exact hik
    -- the slope estimate on `[u, v]`
    have hcl : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u < v → H u ≤ 3 / 4 →
        K / (4 * a3 ^ 3 * Mr) ≤ H v → H u - H v ≤ a3 ^ 3 / Mr →
        v - u ≤ (20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2) := by
      intro u v hu hv huv hHu hHv hHuv
      have hsl := QI_Hslope (by linarith) hHc hHd hHw hu hv huv
      have h1 := hplus u hu hHu
      have h2 := hminus v hv hHv
      have h3 : (1 / 2) * (t / (2 * (a3 * m3))) ≤ Real.sqrt ((1 - v) * (1 + u)) := by
        rw [Real.sqrt_mul (by linarith [hv.2])]
        have : 1 / 2 ≤ Real.sqrt (1 + u) := by
          rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by rw [QI_sqrt_quarter, Real.sqrt_one]]
          exact Real.sqrt_le_sqrt h1
        have h0' : 0 ≤ t / (2 * (a3 * m3)) := by positivity
        nlinarith [Real.sqrt_nonneg (1 - v)]
      have hπ := Real.pi_pos
      have h4 : (9 / 10) * (2 * ((1 / 2) * (t / (2 * (a3 * m3)))) / Real.pi) * (v - u) ≤
          a3 ^ 3 / Mr := by
        refine le_trans ?_ (hsl.trans hHuv)
        gcongr
      rw [← hm33] at h4
      have e1 : (9 / 10) * (2 * ((1 / 2) * (t / (2 * (a3 * m3)))) / Real.pi) * (v - u) =
          (9 * t * (v - u)) / (20 * Real.pi * a3 * m3) := by
        field_simp
        ring
      rw [e1, div_le_div_iff₀ (by positivity) (by positivity)] at h4
      rw [le_div_iff₀ (by positivity)]
      have : (v - u) * (t * m3 ^ 2) * (9 * m3) ≤ (20 * Real.pi / 9) * a3 ^ 4 * (9 * m3) := by
        nlinarith
      have h9m : 0 < 9 * m3 := by positivity
      exact le_of_mul_le_mul_right this h9m
    rcases lt_trichotomy ci ck with hlt | heq | hgt
    · rw [abs_sub_comm, abs_of_pos (by linarith)]
      have := hcl ci ck hci hck hlt hpi_le hpk_ge (le_trans (le_abs_self _) hdiff)
      linarith
    · rw [heq, sub_self, abs_zero]
      positivity
    · rw [abs_of_pos (by linarith)]
      have := hcl ck ci hck hci hgt hpk_le hpi_ge
        (le_trans (le_abs_self _) (by rw [abs_sub_comm]; exact hdiff))
      linarith
  · have hcase := lt_of_not_ge hcase
    have h2 : 2 ≤ 8 * a3 ^ 3 / m3 ^ 3 := by
      rw [hm33, le_div_iff₀ hMr0]
      linarith
    have hδ2 : |ci - ck| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hci.1, hci.2, hck.1, hck.2]
    linarith

/-- The final comparison of sizes: `3330 ⟨Λ²⟩ |c_i - c_k|` against
`240000 D² N^{τ-ε_A} k^{-4/3} (DN)^{-2/3}`, written with `k = t³`, `DN = m₃³`, `N = n₃³`,
`N^τ = a₃³`, `e = N^{-ε_A}`. -/
private lemma QI_arith {s δ t m3 n3 a3 e D : ℝ} (hδ0 : 0 ≤ δ) (ht0 : 0 < t)
    (hm30 : 0 < m3) (hn30 : 0 < n3) (ha30 : 0 < a3) (he0 : 0 < e) (hD1 : 1 ≤ D) (he1 : e ≤ 1)
    (hae : e * a3 ≤ 1) (htm : t ≤ m3) (hmD : m3 ≤ D * n3)
    (hsb : s ≤ 4 * D * (n3 * e / t) ^ 2 / n3 ^ 3)
    (hδ : δ ≤ (20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2) + 8 * a3 ^ 3 / m3 ^ 3) :
    3330 * s * δ ≤ 240000 * D ^ 2 * (a3 ^ 3 * e) * (1 / t ^ 3) / (m3 ^ 2 * t) := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hD0 : 0 < D := by linarith
  set S := 4 * D * (n3 * e / t) ^ 2 / n3 ^ 3 with hS
  have hS0 : 0 ≤ S := by positivity
  set T := 120000 * D ^ 2 * (a3 ^ 3 * e) / (t ^ 4 * m3 ^ 2) with hT
  have h1 : 3330 * s * δ ≤ 3330 * S * ((20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2) +
      8 * a3 ^ 3 / m3 ^ 3) := by
    gcongr
  have T1 : 3330 * S * ((20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2)) ≤ T := by
    have e1 : 3330 * S * ((20 * Real.pi / 9) * a3 ^ 4 / (t * m3 ^ 2)) =
        (3330 * 4 * (20 * Real.pi / 9)) * (e * a3) * t * (D * e * a3 ^ 3) /
          (n3 * t ^ 4 * m3 ^ 2) := by
      rw [hS]
      field_simp
    rw [e1, hT, div_le_div_iff₀ (by positivity) (by positivity)]
    have k0 : (3330 * 4 * (20 * Real.pi / 9)) ≤ 120000 := by nlinarith
    have k1 : (3330 * 4 * (20 * Real.pi / 9)) * (e * a3) * t ≤ 120000 * (D * n3) := by
      have ht' : t ≤ D * n3 := htm.trans hmD
      have hk : 0 ≤ (3330 * 4 * (20 * Real.pi / 9)) := by positivity
      calc (3330 * 4 * (20 * Real.pi / 9)) * (e * a3) * t
          ≤ (3330 * 4 * (20 * Real.pi / 9)) * 1 * (D * n3) := by gcongr
        _ ≤ 120000 * (D * n3) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right k0 (by positivity)
    calc (3330 * 4 * (20 * Real.pi / 9)) * (e * a3) * t * (D * e * a3 ^ 3) * (t ^ 4 * m3 ^ 2)
        ≤ (120000 * (D * n3)) * (D * e * a3 ^ 3) * (t ^ 4 * m3 ^ 2) := by gcongr
      _ = 120000 * D ^ 2 * (a3 ^ 3 * e) * (n3 * t ^ 4 * m3 ^ 2) := by ring
  have T2 : 3330 * S * (8 * a3 ^ 3 / m3 ^ 3) ≤ T := by
    have e1 : 3330 * S * (8 * a3 ^ 3 / m3 ^ 3) =
        (3330 * 4 * 8) * e * t ^ 2 * (D * e * a3 ^ 3) / (n3 * t ^ 4 * m3 ^ 3) := by
      rw [hS]
      field_simp
    rw [e1, hT, div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : (3330 * 4 * 8) * e * t ^ 2 ≤ 120000 * (D * n3 * m3) := by
      have ht2 : t ^ 2 ≤ m3 * (D * n3) := by
        rw [sq]
        exact mul_le_mul htm (htm.trans hmD) ht0.le hm30.le
      calc (3330 * 4 * 8) * e * t ^ 2 ≤ (3330 * 4 * 8) * 1 * (m3 * (D * n3)) := by gcongr
        _ ≤ 120000 * (D * n3 * m3) := by
          nlinarith [mul_pos hD0 hn30, mul_pos (mul_pos hD0 hn30) hm30]
    calc (3330 * 4 * 8) * e * t ^ 2 * (D * e * a3 ^ 3) * (t ^ 4 * m3 ^ 2)
        ≤ (120000 * (D * n3 * m3)) * (D * e * a3 ^ 3) * (t ^ 4 * m3 ^ 2) := by gcongr
      _ = 120000 * D ^ 2 * (a3 ^ 3 * e) * (n3 * t ^ 4 * m3 ^ 3) := by ring
  have e2 : 240000 * D ^ 2 * (a3 ^ 3 * e) * (1 / t ^ 3) / (m3 ^ 2 * t) = 2 * T := by
    rw [hT]
    field_simp
    ring
  rw [e2]
  linarith

/-- The quantile increment behind the correlation comparison of Theorem 2.5
[theorem_localized_eigenvalue] (the step from (2.11) [eq:main_perurb]): under (2.8)
[eq:condA2] at `k` with `2k ≤ DN + 1`, for every index `i` with `|i - k| ≤ N^τ`,
`|(γ_i - γ_i^{sc}) - (γ_k - γ_k^{sc})| ≤ C N^{τ - ε_A} 𝔯(k)^{-1} s^{-1}`,
`s = (DN)^{2/3} 𝔯(k)^{1/3}`. -/
theorem quant_increment (D : ℕ) (hD : 2 ≤ D) (δA εA τ : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hτ : 0 < τ) (hτA : τ < εA / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ i : ℕ, 1 ≤ i → i ≤ D * N → |(i : ℝ) - k| ≤ (N : ℝ) ^ τ →
        |(quant (rho (lam D N A)) (D * N) i - quant rhoSc (D * N) i) -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * (N : ℝ) ^ (τ - εA) * rk D N k ^ (-(1 : ℝ)) /
            (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ)) := by
  open Set in
  -- the threshold `N₀`: `‖Λ‖ ≤ 2D²N^{-δ_A} ≤ 1/200`
  have hlim : Tendsto (fun N : ℕ => 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
    simpa using this.const_mul (2 * (D : ℝ) ^ 2)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 200)))
  refine ⟨240000 * (D : ℝ) ^ 2, by positivity, max N₁ 1,
    fun N hN A hA k hk1 hk2 hhs i hi1 hi2 hik => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hD0 : 0 < D := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, hD0⟩, ⟨0, hN1⟩)⟩
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hkM : k ≤ D * N := by omega
  -- `Λ = U diag(μ) U^*`
  have hΛ := lam_isHermitian D N A
  have hℓ : opNorm (lam D N A) ≤ 1 / 200 := by
    refine (QI_opNorm_lam D N hN1 A).trans ?_
    have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
    have h2 : 2 * (D : ℝ) ^ 2 * opNorm A ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) := by gcongr
    have h3 : 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) < 1 / 200 := h1
    linarith
  obtain ⟨U, μ, hdec, hμ'⟩ := QI_decomp hΛ
  have hμ : ∀ j, |μ j| ≤ 1 / 200 := fun j => (hμ' j).trans hℓ
  have hμ10 : ∀ j, |μ j| ≤ 1 / 10 := fun j => (hμ j).trans (by norm_num)
  have h0 : ∑ j, μ j = 0 := by
    have h := QI_ntr_lam D N hD A
    rw [hdec, QI_ntr_cd] at h
    have hc : ((Fintype.card (Idx D N) : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
    have h' := (mul_eq_zero.1 h).resolve_left hc
    exact_mod_cast h'
  have hss : QI_av (fun j => μ j ^ 2) = avgSq (lam D N A) := by
    unfold avgSq
    rw [hdec, QI_cd_mul, QI_ntr_cd]
    unfold QI_av
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ = (((Fintype.card (Idx D N) : ℝ))⁻¹ : ℝ) by
      push_cast; rfl, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  set s := QI_av (fun j => μ j ^ 2) with hsd
  have hs0 : 0 ≤ s := QI_av_nonneg fun j => sq_nonneg _
  have hs_small : s ≤ 1 / 40000 := by
    calc s ≤ QI_av (fun _ : Idx D N => (1 / 40000 : ℝ)) := QI_av_mono fun j => by
          have := hμ j
          have : μ j ^ 2 = |μ j| ^ 2 := (sq_abs _).symm
          nlinarith [abs_nonneg (μ j)]
      _ = 1 / 40000 := QI_av_const _
  have hsA : s ≤ 4 * D * hsNorm A ^ 2 / N := hss ▸ QI_avgSq_lam D N hD hN1 A
  obtain ⟨hHc, hHd, hHw, hH1, hHm, hHq⟩ := QI_struct (lam D N A) hΛ (hℓ.trans (by norm_num))
    U μ hdec hμ10 h0 (by linarith)
  -- the semicircle: `Λ = 0`
  have hΛ0 : (0 : Matrix (Idx D N) (Idx D N) ℂ).IsHermitian := isHermitian_zero
  have hℓ0 : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by unfold opNorm; simp
  obtain ⟨U₀, μ₀, hdec₀, hμ₀'⟩ := QI_decomp hΛ0
  have hμ₀ : ∀ j, μ₀ j = 0 := fun j => abs_nonpos_iff.1 ((hμ₀' j).trans hℓ0.le)
  have hμ₀10 : ∀ j, |μ₀ j| ≤ 1 / 10 := by intro j; rw [hμ₀ j]; norm_num
  have h00 : ∑ j, μ₀ j = 0 := by simp [hμ₀]
  have hs00 : QI_av (fun j => μ₀ j ^ 2) = 0 := by simp [hμ₀, QI_av]
  obtain ⟨hhc, hhd, hhw, hh1, hhm, hhq⟩ := QI_struct 0 hΛ0 (by rw [hℓ0]; norm_num) U₀ μ₀
    hdec₀ hμ₀10 h00 (by rw [hs00]; norm_num)
  have hw1 : ∀ c ∈ Ioo (-1 : ℝ) 1, QI_w μ₀ c = 1 := fun c hc => by
    have := hhw c hc
    rw [hs00, mul_zero] at this
    have := abs_nonneg (QI_w μ₀ c - 1)
    have h' : |QI_w μ₀ c - 1| = 0 := by linarith
    linarith [abs_eq_zero.1 h']
  have hhd' : ∀ c ∈ Ioo (-1 : ℝ) 1, HasDerivAt
      (fun c => QI_F (rho (0 : Matrix (Idx D N) (Idx D N) ℂ)) (QI_E μ₀ c)) (-QI_sig c) c :=
    fun c hc => by simpa [hw1 c hc] using hhd c hc
  have hE0 : ∀ c : ℝ, |c| ≤ 1 → QI_E μ₀ c = 2 * c := by
    intro c hc
    have hR := QI_R_sub_one μ₀ hμ₀10 h00 hc
    rw [hs00, mul_zero] at hR
    have hR1 : QI_R μ₀ c = 1 := by
      have := abs_nonneg (QI_R μ₀ c - 1)
      have h' : |QI_R μ₀ c - 1| = 0 := by linarith
      linarith [abs_eq_zero.1 h']
    unfold QI_E
    rw [hR1]
    simp [hμ₀, QI_av]
  have hrho0 : rho (0 : Matrix (Idx D N) (Idx D N) ℂ) = rhoSc := rho_zero.2.1
  set H := fun c => QI_F (rho (lam D N A)) (QI_E μ c) with hHdef
  set hh := fun c => QI_F (rho (0 : Matrix (Idx D N) (Idx D N) ℂ)) (QI_E μ₀ c) with hhdef
  set Mr : ℝ := ((D * N : ℕ) : ℝ) with hMr
  have hMr0 : 0 < Mr := by
    rw [hMr]
    exact_mod_cast Nat.mul_pos hD0 hN1
  set ε := 140 * s with hεd
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 100 := by linarith
  have hp : ∀ q : ℕ, 1 ≤ q → q ≤ D * N → ((q : ℝ) - 1 / 2) / Mr ∈ Ioo (0 : ℝ) 1 := by
    intro q hq1 hq2
    have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have h2 : (q : ℝ) ≤ Mr := by rw [hMr]; exact_mod_cast hq2
    exact ⟨div_pos (by linarith) hMr0, by rw [div_lt_one hMr0]; linarith⟩
  have hroot : ∀ F : ℝ → ℝ, ContinuousOn F (Icc (-1) 1) → F 1 = 0 → F (-1) = 1 →
      ∀ p ∈ Ioo (0 : ℝ) 1, ∃ c ∈ Ioo (-1 : ℝ) 1, F c = p := by
    intro F hF h1 hm p hp
    obtain ⟨c, hc, hcp⟩ := intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 1) hF
      (show p ∈ Icc (F 1) (F (-1)) by rw [h1, hm]; exact ⟨hp.1.le, hp.2.le⟩)
    refine ⟨c, ⟨lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩, hcp⟩
    · rintro rfl
      rw [hm] at hcp
      linarith [hp.2]
    · rintro rfl
      rw [h1] at hcp
      linarith [hp.1]
  obtain ⟨ci, hci, hHci⟩ := hroot H hHc hH1 hHm _ (hp i hi1 hi2)
  obtain ⟨ck, hck, hHck⟩ := hroot H hHc hH1 hHm _ (hp k hk1 hkM)
  obtain ⟨bi, hbi, hhbi⟩ := hroot hh hhc hh1 hhm _ (hp i hi1 hi2)
  obtain ⟨bk, hbk, hhbk⟩ := hroot hh hhc hh1 hhm _ (hp k hk1 hkM)
  have habs : ∀ c ∈ Ioo (-1 : ℝ) 1, |c| ≤ 1 := fun c hc => abs_le.2 ⟨hc.1.le, hc.2.le⟩
  have qi : quant (rho (lam D N A)) (D * N) i = QI_E μ ci := hHq ci hci _ hHci
  have qk : quant (rho (lam D N A)) (D * N) k = QI_E μ ck := hHq ck hck _ hHck
  have qsi : quant rhoSc (D * N) i = 2 * bi := by
    rw [← hrho0, ← hE0 bi (habs bi hbi)]
    exact hhq bi hbi _ hhbi
  have qsk : quant rhoSc (D * N) k = 2 * bk := by
    rw [← hrho0, ← hE0 bk (habs bk hbk)]
    exact hhq bk hbk _ hhbk
  rw [qi, qk, qsi, qsk]
  -- the two increments
  have hinc := QI_incr hε0 hε1 hHc hhc hHd hhd' hHw hH1 hh1 hHm hhm hci hck
    (Ioo_subset_Icc_self hbi) (Ioo_subset_Icc_self hbk) (hhbi.trans hHci.symm)
    (hhbk.trans hHck.symm)
  have hlipE := QI_E_lip μ hμ10 h0 (habs ck hck) (habs ci hci)
  have hmain : |(QI_E μ ci - 2 * bi) - (QI_E μ ck - 2 * bk)| ≤ 3330 * s * |ci - ck| := by
    have e : (QI_E μ ci - 2 * bi) - (QI_E μ ck - 2 * bk) =
        ((QI_E μ ci - 2 * ci) - (QI_E μ ck - 2 * ck)) + 2 * ((ci - bi) - (ck - bk)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two]
    rw [hεd] at hinc
    linarith
  -- cube roots: `k = t³`, `DN = m₃³`, `N = n₃³`, `N^τ = a₃³`, `e = N^{-ε_A}`
  set K : ℝ := (k : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact_mod_cast hk1
  have hKM : K ≤ Mr := by rw [hK, hMr]; exact_mod_cast hkM
  have h2K : 2 * K ≤ Mr + 1 := by
    rw [hK, hMr]
    exact_mod_cast hk2
  have hrk : rk D N k = K := by
    unfold rk
    rw [show min k (D * N + 1 - k) = k by omega]
  set t := K ^ (1 / 3 : ℝ) with ht
  set m3 := Mr ^ (1 / 3 : ℝ) with hm3
  set n3 := (N : ℝ) ^ (1 / 3 : ℝ) with hn3
  set a3 := (N : ℝ) ^ (τ / 3) with ha3
  set e := (N : ℝ) ^ (-εA) with he
  have ht3 : t ^ 3 = K := QI_cube (by linarith)
  have hm33 : m3 ^ 3 = Mr := QI_cube hMr0.le
  have hn33 : n3 ^ 3 = N := QI_cube hn0.le
  have ha33 : a3 ^ 3 = (N : ℝ) ^ τ := by
    rw [ha3, QI_rpow_pow hn0.le]
    congr 1
    push_cast
    ring
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  have hm30 : 0 < m3 := Real.rpow_pos_of_pos hMr0 _
  have hn30 : 0 < n3 := Real.rpow_pos_of_pos hn0 _
  have ha30 : 0 < a3 := Real.rpow_pos_of_pos hn0 _
  have he0 : 0 < e := Real.rpow_pos_of_pos hn0 _
  have he1 : e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.2 hεA.le)
  have ha31 : 1 ≤ a3 := Real.one_le_rpow hn (by linarith)
  have hae : e * a3 ≤ 1 := by
    rw [ha3, he, ← Real.rpow_add hn0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have htm : t ≤ m3 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hm30.le ?_
    rw [ht3, hm33]
    exact hKM
  have hmD : m3 ≤ D * n3 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    rw [hm33, mul_pow, hn33, hMr]
    push_cast
    have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.mpr hD0
    have hD3 : (D : ℝ) ≤ (D : ℝ) ^ 3 := by
      calc (D : ℝ) = D * 1 * 1 := by ring
        _ ≤ D * D * D := by gcongr
        _ = (D : ℝ) ^ 3 := by ring
    exact mul_le_mul_of_nonneg_right hD3 hn0.le
  have hrk1 : rk D N k ^ (-(1 : ℝ)) = 1 / t ^ 3 := by
    rw [hrk, Real.rpow_neg_one, ht3, one_div]
  have hrk3 : rk D N k ^ (1 / 3 : ℝ) = t := by rw [hrk]
  have hrkm : rk D N k ^ (-(1 / 3 : ℝ)) = 1 / t := by
    rw [hrk, Real.rpow_neg (by linarith), ← ht, inv_eq_one_div]
  have hNe : (N : ℝ) ^ ((1 / 3 : ℝ) - εA) = n3 * e := by
    rw [sub_eq_add_neg, Real.rpow_add hn0]
  have hNte : (N : ℝ) ^ (τ - εA) = a3 ^ 3 * e := by
    rw [sub_eq_add_neg, Real.rpow_add hn0, ha33]
  have hM23 : Mr ^ (2 / 3 : ℝ) = m3 ^ 2 := by
    rw [hm3, QI_rpow_pow hMr0.le]
    norm_num
  -- the bound on `⟨Λ²⟩`
  have hhs' : hsNorm A ≤ n3 * e / t := by
    rw [hNe, hrkm] at hhs
    rwa [mul_one_div] at hhs
  have hsb : s ≤ 4 * D * (n3 * e / t) ^ 2 / n3 ^ 3 := by
    rw [hn33]
    refine hsA.trans ?_
    have h0' : 0 ≤ hsNorm A := Real.sqrt_nonneg _
    gcongr
  rw [ha33.symm] at hik
  rw [hrk1, hrk3, hNte, hM23]
  have hcmp := QI_cmp hHc hhc hHd hhd' hHw hH1 hh1 hHm hhm
  obtain ⟨hsym, hup, hlo, -⟩ := QI_hfacts hhc hhd' hh1 hhm
  have hh0 : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ hh c := fun c hc =>
    le_trans (mul_nonneg (by norm_num) (QI_p32_nonneg hc.2)) (hlo c hc)
  clear_value H hh t m3 n3 a3 e K Mr ε s
  -- the bound on `|c_i - c_k|`
  have hδ := QI_delta hε0 hε1 hHc hHd hHw hcmp hsym hup hh0 hci hck hMr0 hK1
    (by exact_mod_cast hi1) h2K hik ha31 ht0 hm30 ht3 hm33 hHci hHck
  exact le_trans hmain (QI_arith (abs_nonneg _) ht0 hm30 hn30 ha30 he0
    (Nat.one_le_cast.mpr hD0) he1 hae htm hmD hsb hδ)

end RBMTransitionEdge

end
