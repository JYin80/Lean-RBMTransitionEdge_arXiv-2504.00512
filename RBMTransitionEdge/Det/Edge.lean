module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core

@[expose] public section

/-!
# Edges and square-root behaviour

Boundary values of `m` on ℝ (Definition 2.7 [defn_Mm]); the support of `ρ_N` of (2.19)
[eq:density_rhoN] is one interval `[E⁻, E⁺]`; the limits (2.6) [eq:def_gamma]; the square-root
behaviour (A.1) [square_root_density]; the edge bounds (A.2) [edge_close_to_edge_sc].
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `κ_E = |E⁺ - E| ∧ |E - E⁻|`, the distance from `E` to the edges of `ρ_N` (§2.2). -/
def kappa {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (E : ℝ) : ℝ :=
  min |Eplus Λ - E| |E - Eminus Λ|


section Scalar

variable {ι : Type*} [Fintype ι]

/-- The normalized sum `n⁻¹ Σ_j f_j`, real form. -/
private def Edge_av (f : ι → ℝ) : ℝ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, f j

/-- The normalized sum `n⁻¹ Σ_j f_j`, complex form. -/
private def Edge_avc (f : ι → ℂ) : ℂ := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, f j

private lemma Edge_av_le {f g : ι → ℝ} (h : ∀ j, f j ≤ g j) : Edge_av f ≤ Edge_av g := by
  unfold Edge_av; gcongr with j; exact h j

private lemma Edge_av_lt [Nonempty ι] {f g : ι → ℝ} (h : ∀ j, f j < g j) :
    Edge_av f < Edge_av g := by
  unfold Edge_av
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact mul_lt_mul_of_pos_left (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => h j)
    (inv_pos.2 hn)

private lemma Edge_av_const [Nonempty ι] (c : ℝ) : Edge_av (fun _ : ι => c) = c := by
  unfold Edge_av
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

private lemma Edge_av_add (f g : ι → ℝ) :
    Edge_av (fun j => f j + g j) = Edge_av f + Edge_av g := by
  unfold Edge_av; rw [Finset.sum_add_distrib]; ring

private lemma Edge_av_sub (f g : ι → ℝ) :
    Edge_av (fun j => f j - g j) = Edge_av f - Edge_av g := by
  unfold Edge_av; rw [Finset.sum_sub_distrib]; ring

private lemma Edge_av_mul (c : ℝ) (f : ι → ℝ) : Edge_av (fun j => c * f j) = c * Edge_av f := by
  unfold Edge_av; rw [← Finset.mul_sum]; ring

private lemma Edge_av_neg (f : ι → ℝ) : Edge_av (fun j => -f j) = -Edge_av f := by
  unfold Edge_av; rw [Finset.sum_neg_distrib]; ring

/-- A weighted mean with weights of mean `1` lies between the bounds of the values. -/
private lemma Edge_av_wt [Nonempty ι] {w r : ι → ℝ} {p q : ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : Edge_av w = 1) (hr : ∀ j, p ≤ r j ∧ r j ≤ q) :
    p ≤ Edge_av (fun j => w j * r j) ∧ Edge_av (fun j => w j * r j) ≤ q := by
  constructor
  · calc p = Edge_av (fun j => p * w j) := by rw [Edge_av_mul, hw, mul_one]
      _ ≤ _ := Edge_av_le fun j => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hr j).1 (hw0 j)
  · calc Edge_av (fun j => w j * r j) ≤ Edge_av (fun j => q * w j) :=
          Edge_av_le fun j => by rw [mul_comm q]; exact mul_le_mul_of_nonneg_left (hr j).2 (hw0 j)
      _ = q := by rw [Edge_av_mul, hw, mul_one]

private lemma Edge_avc_ofReal (f : ι → ℝ) : Edge_avc (fun j => (f j : ℂ)) = ((Edge_av f : ℝ) : ℂ) := by
  unfold Edge_avc Edge_av; push_cast; rfl

private lemma Edge_avc_re (f : ι → ℂ) : (Edge_avc f).re = Edge_av (fun j => (f j).re) := by
  unfold Edge_avc Edge_av
  rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum]

private lemma Edge_avc_im (f : ι → ℂ) : (Edge_avc f).im = Edge_av (fun j => (f j).im) := by
  unfold Edge_avc Edge_av
  rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.im_ofReal_mul, Complex.im_sum]

private lemma Edge_avc_add (f g : ι → ℂ) :
    Edge_avc (fun j => f j + g j) = Edge_avc f + Edge_avc g := by
  unfold Edge_avc; rw [Finset.sum_add_distrib]; ring

private lemma Edge_avc_sub (f g : ι → ℂ) :
    Edge_avc (fun j => f j - g j) = Edge_avc f - Edge_avc g := by
  unfold Edge_avc; rw [Finset.sum_sub_distrib]; ring

private lemma Edge_avc_mul (c : ℂ) (f : ι → ℂ) : Edge_avc (fun j => c * f j) = c * Edge_avc f := by
  unfold Edge_avc; rw [← Finset.mul_sum]; ring

private lemma Edge_avc_neg (f : ι → ℂ) : Edge_avc (fun j => -f j) = -Edge_avc f := by
  unfold Edge_avc; rw [Finset.sum_neg_distrib]; ring

/-- `s(ζ) = ⟨(Λ - ζ)⁻¹⟩` for eigenvalues `μ`; (2.16) [self_m] reads `m = s(z + m)`. -/
private def Edge_S (μ : ι → ℝ) (ζ : ℂ) : ℂ := Edge_avc fun j => ((μ j : ℂ) - ζ)⁻¹

/-- `F(ζ) = ⟨|Λ - ζ|⁻²⟩`, the quantity `⟨M M^*⟩` of (A.3) [equation_z_im_m]. -/
private def Edge_F (μ : ι → ℝ) (ζ : ℂ) : ℝ := Edge_av fun j => ‖((μ j : ℂ) - ζ)⁻¹‖ ^ 2

/-- `G(u) = ⟨(u - Λ)⁻²⟩` for real `u`. -/
private def Edge_G (μ : ι → ℝ) (u : ℝ) : ℝ := Edge_av fun j => ((u - μ j) ^ 2)⁻¹

/-- `φ(u) = u + ⟨(u - Λ)⁻¹⟩`, the real inverse of `z ↦ z + m(z)` on the real axis. -/
private def Edge_phi (μ : ι → ℝ) (u : ℝ) : ℝ := u + Edge_av fun j => (u - μ j)⁻¹

/-- The critical point `w₊ > max μ` of `φ`: `⟨(w₊ - Λ)⁻²⟩ = 1`. -/
private def Edge_wp (μ : ι → ℝ) : ℝ :=
  if h : ∃ u : ℝ, (∀ j, μ j < u) ∧ Edge_G μ u = 1 then h.choose else 0

/-- The right edge `φ(w₊)`. -/
private def Edge_ep (μ : ι → ℝ) : ℝ := Edge_phi μ (Edge_wp μ)

/-- The left edge `-φ_{-μ}(w₊(-μ))`. -/
private def Edge_em (μ : ι → ℝ) : ℝ := -Edge_ep (fun j => -μ j)

/-- `g(w) = ⟨(w₊ - Λ)⁻² (w - Λ)⁻¹⟩`, so that `w - s(w) - E⁺ = (w - w₊)² g(w)`. -/
private def Edge_g (μ : ι → ℝ) (w : ℂ) : ℂ :=
  Edge_avc fun j => ((((Edge_wp μ - μ j) ^ 2)⁻¹ : ℝ) : ℂ) * (w - (μ j : ℂ))⁻¹

private lemma Edge_inv_expand {K : Type*} [Field K] (x d : K) (hx : x ≠ 0) (hxd : x + d ≠ 0) :
    (x + d)⁻¹ = x⁻¹ - d * (x ^ 2)⁻¹ + d ^ 2 * ((x ^ 2)⁻¹ * (x + d)⁻¹) := by
  field_simp; ring

private lemma Edge_G_lt {μ : ι → ℝ} [Nonempty ι] {u v : ℝ} (hu : ∀ j, μ j < u) (huv : u < v) :
    Edge_G μ v < Edge_G μ u := by
  unfold Edge_G
  refine Edge_av_lt fun j => ?_
  have h1 : 0 < u - μ j := by linarith [hu j]
  apply inv_strictAnti₀ (by positivity)
  nlinarith

private lemma Edge_G_le {μ : ι → ℝ} {u v : ℝ} (hu : ∀ j, μ j < u) (huv : u ≤ v) :
    Edge_G μ v ≤ Edge_G μ u := by
  unfold Edge_G
  refine Edge_av_le fun j => ?_
  have h1 : 0 < u - μ j := by linarith [hu j]
  apply inv_anti₀ (by positivity)
  nlinarith

variable [Nonempty ι]

omit [Fintype ι] in
private lemma Edge_l0 {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) : 0 ≤ ℓ :=
  (abs_nonneg _).trans (hμ (Classical.arbitrary ι))

/-- `w₊` exists, `G(w₊) = 1`, and `|w₊ - 1| ≤ ℓ`. -/
private lemma Edge_wp_spec {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) :
    (∀ j, μ j < Edge_wp μ) ∧ Edge_G μ (Edge_wp μ) = 1 ∧ 1 - ℓ ≤ Edge_wp μ ∧
      Edge_wp μ ≤ 1 + ℓ := by
  have hl0 := Edge_l0 hμ
  have hb : ∀ j, -ℓ ≤ μ j ∧ μ j ≤ ℓ := fun j => abs_le.1 (hμ j)
  have hcont : ContinuousOn (Edge_G μ) (Set.Icc (1 - ℓ) (1 + ℓ)) := by
    have : ∀ j, ContinuousOn (fun u : ℝ => ((u - μ j) ^ 2)⁻¹) (Set.Icc (1 - ℓ) (1 + ℓ)) := by
      intro j
      apply ContinuousOn.inv₀ ((continuous_id.sub continuous_const).pow 2).continuousOn
      intro u hu
      have := hb j; have := hu.1; exact pow_ne_zero _ (by linarith : 0 < u - μ j).ne'
    show ContinuousOn (fun u : ℝ => ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ((u - μ j) ^ 2)⁻¹) _
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => this j)
  have h1 : 1 ≤ Edge_G μ (1 - ℓ) := by
    unfold Edge_G
    calc (1 : ℝ) = Edge_av (fun _ : ι => (1 : ℝ)) := (Edge_av_const 1).symm
      _ ≤ _ := Edge_av_le fun j => by
        have := hb j
        have h0 : 0 < 1 - ℓ - μ j := by linarith
        rw [one_le_inv₀ (by positivity)]
        nlinarith
  have h2 : Edge_G μ (1 + ℓ) ≤ 1 := by
    unfold Edge_G
    calc _ ≤ Edge_av (fun _ : ι => (1 : ℝ)) := Edge_av_le fun j => by
          have := hb j
          have h0 : 1 ≤ 1 + ℓ - μ j := by linarith
          rw [inv_le_one₀ (by positivity)]
          nlinarith
      _ = 1 := Edge_av_const 1
  obtain ⟨u₀, hu₀, hG⟩ := intermediate_value_Icc' (by linarith) hcont ⟨h2, h1⟩
  have hlt : ∀ j, μ j < u₀ := fun j => by linarith [hb j, hu₀.1]
  have hex : ∃ u : ℝ, (∀ j, μ j < u) ∧ Edge_G μ u = 1 := ⟨u₀, hlt, hG⟩
  have hspec := hex.choose_spec
  have heq : Edge_wp μ = hex.choose := by
    unfold Edge_wp; split_ifs; rfl
  have hu : hex.choose = u₀ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := Edge_G_lt hspec.1 h; linarith [hspec.2]
    · have := Edge_G_lt hlt h; linarith [hspec.2]
  rw [heq, hu]
  exact ⟨hlt, hG, hu₀.1, hu₀.2⟩

/-- `x_j = w₊ - μ_j ∈ [1 - 2ℓ, 1 + 2ℓ]`. -/
private lemma Edge_x_bd {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (j : ι) :
    1 - 2 * ℓ ≤ Edge_wp μ - μ j ∧ Edge_wp μ - μ j ≤ 1 + 2 * ℓ := by
  have := Edge_wp_spec hμ hℓ
  have := abs_le.1 (hμ j)
  constructor <;> linarith

/-- `φ(u) - E⁺ = (u - w₊)² ⟨(w₊ - Λ)⁻² (u - Λ)⁻¹⟩` for real `u > max μ`. -/
private lemma Edge_phi_id {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (u : ℝ)
    (hu : ∀ j, μ j < u) :
    Edge_phi μ u - Edge_ep μ = (u - Edge_wp μ) ^ 2 *
      Edge_av (fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹ * (u - μ j)⁻¹) := by
  obtain ⟨hw, hG, -, -⟩ := Edge_wp_spec hμ hℓ
  set wp := Edge_wp μ
  have e : ∀ j, (u - μ j)⁻¹ - (wp - μ j)⁻¹ =
      -(u - wp) * ((wp - μ j) ^ 2)⁻¹ + (u - wp) ^ 2 * (((wp - μ j) ^ 2)⁻¹ * (u - μ j)⁻¹) := by
    intro j
    have h := Edge_inv_expand (wp - μ j) (u - wp) (by linarith [hw j]) (by linarith [hu j])
    rw [show wp - μ j + (u - wp) = u - μ j by ring] at h
    linear_combination h
  calc Edge_phi μ u - Edge_ep μ =
      (u - wp) + Edge_av (fun j => (u - μ j)⁻¹ - (wp - μ j)⁻¹) := by
        unfold Edge_ep Edge_phi; rw [Edge_av_sub]; ring
    _ = (u - wp) + Edge_av (fun j => -(u - wp) * ((wp - μ j) ^ 2)⁻¹ +
          (u - wp) ^ 2 * (((wp - μ j) ^ 2)⁻¹ * (u - μ j)⁻¹)) := by
        congr 1; congr 1; funext j; exact e j
    _ = _ := by
        rw [Edge_av_add, Edge_av_mul, Edge_av_mul]
        unfold Edge_G at hG
        rw [hG]; ring

/-- `φ(u) ≥ E⁺` for real `u > max μ`. -/
private lemma Edge_phi_ge {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (u : ℝ)
    (hu : ∀ j, μ j < u) : Edge_ep μ ≤ Edge_phi μ u := by
  have h := Edge_phi_id hμ hℓ u hu
  have hw := (Edge_wp_spec hμ hℓ).1
  have : 0 ≤ (u - Edge_wp μ) ^ 2 * Edge_av (fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹ * (u - μ j)⁻¹) := by
    apply mul_nonneg (sq_nonneg _)
    calc (0 : ℝ) = Edge_av (fun _ : ι => (0 : ℝ)) := (Edge_av_const 0).symm
      _ ≤ _ := Edge_av_le fun j => by
        have := hw j; have := hu j
        have : 0 < u - μ j := by linarith
        positivity
  linarith

/-- `w - s(w) - E⁺ = (w - w₊)² g(w)` for `w` off the spectrum. -/
private lemma Edge_Phi_id {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (w : ℂ)
    (hw : ∀ j, (μ j : ℂ) ≠ w) :
    w - Edge_S μ w - (Edge_ep μ : ℂ) = (w - (Edge_wp μ : ℂ)) ^ 2 * Edge_g μ w := by
  obtain ⟨hx, hG, -, -⟩ := Edge_wp_spec hμ hℓ
  set wp := Edge_wp μ
  have hX : ∀ j, ((wp - μ j : ℝ) : ℂ) ≠ 0 := fun j => by
    have := hx j; exact_mod_cast (show wp - μ j ≠ 0 by linarith)
  have hXd : ∀ j, ((wp - μ j : ℝ) : ℂ) + (w - wp) ≠ 0 := fun j h => hw j (by
    push_cast at h; linear_combination -h)
  have e : ∀ j, -((μ j : ℂ) - w)⁻¹ - (((wp - μ j)⁻¹ : ℝ) : ℂ) =
      -(w - wp) * ((((wp - μ j) ^ 2)⁻¹ : ℝ) : ℂ) +
        (w - wp) ^ 2 * (((((wp - μ j) ^ 2)⁻¹ : ℝ) : ℂ) * (w - (μ j : ℂ))⁻¹) := by
    intro j
    have h := Edge_inv_expand _ (w - wp) (hX j) (hXd j)
    rw [show ((wp - μ j : ℝ) : ℂ) + (w - wp) = w - μ j by push_cast; ring] at h
    rw [show -((μ j : ℂ) - w)⁻¹ = (w - μ j)⁻¹ by rw [← inv_neg, neg_sub]]
    push_cast at h ⊢
    linear_combination h
  have hG' : Edge_avc (fun j => ((((wp - μ j) ^ 2)⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [Edge_avc_ofReal]; unfold Edge_G at hG; rw [hG]; simp
  have hep : (Edge_ep μ : ℂ) = (wp : ℂ) + Edge_avc (fun j => (((wp - μ j)⁻¹ : ℝ) : ℂ)) := by
    rw [Edge_avc_ofReal]; unfold Edge_ep Edge_phi; push_cast; rfl
  calc w - Edge_S μ w - (Edge_ep μ : ℂ) =
      (w - wp) + Edge_avc (fun j => -((μ j : ℂ) - w)⁻¹ - (((wp - μ j)⁻¹ : ℝ) : ℂ)) := by
        rw [hep, Edge_avc_sub, Edge_avc_neg]; unfold Edge_S; ring
    _ = (w - wp) + Edge_avc (fun j => -(w - wp) * ((((wp - μ j) ^ 2)⁻¹ : ℝ) : ℂ) +
          (w - wp) ^ 2 * (((((wp - μ j) ^ 2)⁻¹ : ℝ) : ℂ) * (w - (μ j : ℂ))⁻¹)) := by
        congr 1; congr 1; funext j; exact e j
    _ = _ := by
        rw [Edge_avc_add, Edge_avc_mul, Edge_avc_mul, hG']; unfold Edge_g; ring

/-- `E⁺ = 2 + ⟨Λ⟩ + ⟨(x - 1)²/x⟩` with `x = w₊ - Λ`. -/
private lemma Edge_ep_eq {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) :
    Edge_ep μ = 2 + Edge_av μ + Edge_av (fun j => (Edge_wp μ - μ j - 1) ^ 2 / (Edge_wp μ - μ j)) := by
  have hx := (Edge_wp_spec hμ hℓ).1
  have e : ∀ j, (Edge_wp μ - μ j)⁻¹ =
      (Edge_wp μ - μ j - 1) ^ 2 / (Edge_wp μ - μ j) - (Edge_wp μ - μ j) + 2 := fun j => by
    have : Edge_wp μ - μ j ≠ 0 := by linarith [hx j]
    field_simp; ring
  unfold Edge_ep Edge_phi
  rw [show (fun j => (Edge_wp μ - μ j)⁻¹) = fun j => (Edge_wp μ - μ j - 1) ^ 2 / (Edge_wp μ - μ j) -
      (Edge_wp μ - μ j) + 2 from funext e, Edge_av_add, Edge_av_sub, Edge_av_const, Edge_av_sub,
    Edge_av_const]
  ring

/-- `2 - ℓ ≤ E⁺ ≤ 2 + ℓ + 5ℓ²`. -/
private lemma Edge_ep_bd {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) :
    2 - ℓ ≤ Edge_ep μ ∧ Edge_ep μ ≤ 2 + ℓ + 5 * ℓ ^ 2 := by
  have hl0 := Edge_l0 hμ
  rw [Edge_ep_eq hμ hℓ]
  have hw := Edge_wp_spec hμ hℓ
  have hA : -ℓ ≤ Edge_av μ ∧ Edge_av μ ≤ ℓ := by
    constructor
    · calc -ℓ = Edge_av (fun _ : ι => -ℓ) := (Edge_av_const _).symm
        _ ≤ _ := Edge_av_le fun j => (abs_le.1 (hμ j)).1
    · calc Edge_av μ ≤ Edge_av (fun _ : ι => ℓ) := Edge_av_le fun j => (abs_le.1 (hμ j)).2
        _ = ℓ := Edge_av_const _
  have hB : 0 ≤ Edge_av (fun j => (Edge_wp μ - μ j - 1) ^ 2 / (Edge_wp μ - μ j)) ∧
      Edge_av (fun j => (Edge_wp μ - μ j - 1) ^ 2 / (Edge_wp μ - μ j)) ≤ 5 * ℓ ^ 2 := by
    constructor
    · calc (0 : ℝ) = Edge_av (fun _ : ι => (0 : ℝ)) := (Edge_av_const _).symm
        _ ≤ _ := Edge_av_le fun j => by
          have := Edge_x_bd hμ hℓ j
          apply div_nonneg (sq_nonneg _); linarith
    · calc _ ≤ Edge_av (fun _ : ι => 5 * ℓ ^ 2) := Edge_av_le fun j => by
            have := Edge_x_bd hμ hℓ j
            have hpos : 0 < Edge_wp μ - μ j := by linarith
            rw [div_le_iff₀ hpos]
            have h1 : (Edge_wp μ - μ j - 1) ^ 2 ≤ (2 * ℓ) ^ 2 := by
              apply sq_le_sq'; linarith; linarith
            nlinarith
        _ = _ := Edge_av_const _
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]
/-! ### Reflection `Λ ↦ -Λ` -/

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_neg_bd {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) : ∀ j, |(fun j => -μ j) j| ≤ ℓ :=
  fun j => by simpa using hμ j

omit [Nonempty ι] in
private lemma Edge_phi_neg (μ : ι → ℝ) (u : ℝ) : Edge_phi (fun j => -μ j) (-u) = -Edge_phi μ u := by
  unfold Edge_phi
  rw [show (fun j => (-u - -μ j)⁻¹) = fun j => -(u - μ j)⁻¹ from funext fun j => by
    rw [← inv_neg]; ring_nf, Edge_av_neg]
  ring

omit [Nonempty ι] in
private lemma Edge_avc_star (f : ι → ℂ) : Edge_avc (fun j => star (f j)) = star (Edge_avc f) := by
  unfold Edge_avc; rw [star_mul', star_sum, star_inv₀, star_natCast]

omit [Nonempty ι] in
private lemma Edge_S_neg (μ : ι → ℝ) (ζ : ℂ) :
    Edge_S (fun j => -μ j) (-star ζ) = -star (Edge_S μ ζ) := by
  unfold Edge_S
  show Edge_avc (fun j => (((-μ j : ℝ) : ℂ) - -star ζ)⁻¹) = _
  have e : (fun j => (((-μ j : ℝ) : ℂ) - -star ζ)⁻¹) = fun j => -star (((μ j : ℂ) - ζ)⁻¹) := by
    funext j
    rw [star_inv₀, star_sub, Complex.star_def, Complex.conj_ofReal, ← inv_neg]
    push_cast; ring_nf
  rw [e, Edge_avc_neg, Edge_avc_star]

omit [Nonempty ι] in
private lemma Edge_F_neg (μ : ι → ℝ) (ζ : ℂ) :
    Edge_F (fun j => -μ j) (-star ζ) = Edge_F μ ζ := by
  unfold Edge_F; congr 1; funext j
  rw [norm_inv, norm_inv, show ((-μ j : ℝ) : ℂ) - -star ζ = -star ((μ j : ℂ) - ζ) by
    rw [star_sub, Complex.star_def, Complex.conj_ofReal]; push_cast; ring, norm_neg, norm_star]

/-! ### Uniqueness of solutions in the closed upper half plane -/

omit [Nonempty ι] in
private lemma Edge_S_sub (μ : ι → ℝ) {w w' : ℂ} (hw : ∀ j, (μ j : ℂ) ≠ w)
    (hw' : ∀ j, (μ j : ℂ) ≠ w') :
    Edge_S μ w - Edge_S μ w' =
      (w - w') * Edge_avc (fun j => ((μ j : ℂ) - w)⁻¹ * ((μ j : ℂ) - w')⁻¹) := by
  unfold Edge_S
  rw [← Edge_avc_sub, ← Edge_avc_mul]
  congr 1; funext j
  have h1 : (μ j : ℂ) - w ≠ 0 := sub_ne_zero.2 (hw j)
  have h2 : (μ j : ℂ) - w' ≠ 0 := sub_ne_zero.2 (hw' j)
  field_simp; ring

omit [Nonempty ι] in
/-- `Im s(ζ) = Im ζ · F(ζ)`. -/
private lemma Edge_S_im (μ : ι → ℝ) (ζ : ℂ) : (Edge_S μ ζ).im = ζ.im * Edge_F μ ζ := by
  unfold Edge_S Edge_F
  rw [Edge_avc_im, ← Edge_av_mul]
  congr 1; funext j
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.inv_im]
  simp [div_eq_mul_inv]

/-- Two points of the closed upper half plane off the spectrum with `F ≤ 1` and the same value
of `w - s(w)` coincide. -/
private lemma Edge_unique (μ : ι → ℝ) {w w' : ℂ} (hw : 0 ≤ w.im) (hw' : 0 ≤ w'.im)
    (hne : ∀ j, (μ j : ℂ) ≠ w) (hne' : ∀ j, (μ j : ℂ) ≠ w') (hF : Edge_F μ w ≤ 1)
    (hF' : Edge_F μ w' ≤ 1) (h : w - Edge_S μ w = w' - Edge_S μ w') : w = w' := by
  by_contra hww
  have hd := Edge_S_sub μ hne hne'
  set a : ι → ℂ := fun j => ((μ j : ℂ) - w)⁻¹
  set b : ι → ℂ := fun j => ((μ j : ℂ) - w')⁻¹
  have hP : Edge_avc (fun j => a j * b j) = 1 := by
    have h2 : (w - w') * (1 - Edge_avc (fun j => a j * b j)) = 0 := by
      linear_combination h + hd
    rcases mul_eq_zero.1 h2 with e | e
    · exact absurd (sub_eq_zero.1 e) hww
    · exact (sub_eq_zero.1 e).symm
  have key : ∀ j, 2 * (a j * b j).re = ‖a j‖ ^ 2 + ‖b j‖ ^ 2 - ‖a j - star (b j)‖ ^ 2 := by
    intro j
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hre := congrArg Complex.re hP
  rw [Edge_avc_re, Complex.one_re] at hre
  have hsum : Edge_av (fun j => ‖a j - star (b j)‖ ^ 2) ≤ 0 := by
    have e2 : Edge_av (fun j => ‖a j - star (b j)‖ ^ 2) =
        Edge_F μ w + Edge_F μ w' - 2 * Edge_av (fun j => (a j * b j).re) := by
      unfold Edge_F
      rw [← Edge_av_add, ← Edge_av_mul, ← Edge_av_sub]
      congr 1; funext j; linarith [key j]
    rw [e2, hre]; linarith
  have hz : ∀ j, ‖a j - star (b j)‖ ^ 2 = 0 := by
    unfold Edge_av at hsum
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hs : ∑ j, ‖a j - star (b j)‖ ^ 2 ≤ 0 := by
      by_contra hc; rw [not_le] at hc
      have := mul_pos (inv_pos.2 hn) hc; linarith
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1
      (le_antisymm hs (Finset.sum_nonneg fun j _ => by positivity)) j (Finset.mem_univ j)
  obtain j := Classical.arbitrary ι
  have hj : a j = star (b j) := by
    have := hz j; rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at this; exact this
  have hj' : (μ j : ℂ) - w = (μ j : ℂ) - (starRingEnd ℂ) w' := by
    have : ((μ j : ℂ) - w)⁻¹ = ((μ j : ℂ) - (starRingEnd ℂ) w')⁻¹ := by
      have h' := hj
      simp only [a, b, star_inv₀, star_sub, Complex.star_def, Complex.conj_ofReal] at h'
      exact h'
    exact inv_injective this
  have e : w = (starRingEnd ℂ) w' := by linear_combination -hj'
  have him : w.im = 0 := by
    have := congrArg Complex.im e; simp at this; linarith
  have him' : w'.im = 0 := by
    have := congrArg Complex.im e; simp at this; linarith
  apply hww
  apply Complex.ext
  · have := congrArg Complex.re e; simpa using this
  · rw [him, him']

/-! ### Boundary values by compactness -/

/-- The closed conditions satisfied by `m(z)` on the closed upper half plane: `Im(z + m) ≥ 0`,
`|z + m| ≥ 1 - ℓ`, `F(z + m) ≤ 1`, `m = s(z + m)` and `|m| ≤ 1`. -/
private def Edge_Q (μ : ι → ℝ) (ℓ : ℝ) (z m : ℂ) : Prop :=
  0 ≤ (z + m).im ∧ 1 - ℓ ≤ ‖z + m‖ ∧ Edge_F μ (z + m) ≤ 1 ∧ m = Edge_S μ (z + m) ∧ ‖m‖ ≤ 1

/-- The properties of `m = mSol Λ` on the upper half plane in scalar form. -/
private def Edge_Hm (μ : ι → ℝ) (ℓ : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧ m z = Edge_S μ (z + m z) ∧ ‖m z‖ < 1 ∧ 1 - ℓ < ‖z + m z‖

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_ne_of_norm {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {w : ℂ} (hw : 1 - ℓ ≤ ‖w‖) : ∀ j, (μ j : ℂ) ≠ w := fun j e => by
  have := hμ j
  rw [← e, Complex.norm_real, Real.norm_eq_abs] at hw
  linarith

omit [Nonempty ι] in
private lemma Edge_S_cont (μ : ι → ℝ) {ζ : ℂ} (hζ : ∀ j, (μ j : ℂ) ≠ ζ) :
    ContinuousAt (Edge_S μ) ζ := by
  unfold Edge_S Edge_avc
  have hne : ∀ j, (μ j : ℂ) - ζ ≠ 0 := fun j => sub_ne_zero.2 (hζ j)
  fun_prop (disch := exact hne _)

omit [Nonempty ι] in
private lemma Edge_F_cont (μ : ι → ℝ) {ζ : ℂ} (hζ : ∀ j, (μ j : ℂ) ≠ ζ) :
    ContinuousAt (Edge_F μ) ζ := by
  unfold Edge_F Edge_av
  have hne : ∀ j, (μ j : ℂ) - ζ ≠ 0 := fun j => sub_ne_zero.2 (hζ j)
  have : ∀ j, ContinuousAt (fun ζ : ℂ => ‖((μ j : ℂ) - ζ)⁻¹‖ ^ 2) ζ := fun j =>
    ((continuousAt_const.sub continuousAt_id).inv₀ (hne j)).norm.pow 2
  exact continuousAt_const.mul (tendsto_finsetSum _ fun j _ => this j)

omit [Nonempty ι] in
private lemma Edge_Q_lim {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {α : Type*} {l : Filter α} [l.NeBot] {p q : α → ℂ} {z₀ c : ℂ} (hp : Tendsto p l (𝓝 z₀))
    (hq : Tendsto q l (𝓝 c)) (hQ : ∀ᶠ a in l, Edge_Q μ ℓ (p a) (q a)) : Edge_Q μ ℓ z₀ c := by
  have hpq : Tendsto (fun a => p a + q a) l (𝓝 (z₀ + c)) := hp.add hq
  have h1 : 0 ≤ (z₀ + c).im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hpq) (hQ.mono fun a h => h.1)
  have h2 : 1 - ℓ ≤ ‖z₀ + c‖ :=
    ge_of_tendsto ((continuous_norm.tendsto _).comp hpq) (hQ.mono fun a h => h.2.1)
  have h5 : ‖c‖ ≤ 1 := le_of_tendsto ((continuous_norm.tendsto _).comp hq) (hQ.mono fun a h => h.2.2.2.2)
  have hne := Edge_ne_of_norm hμ hℓ h2
  have h3 : Edge_F μ (z₀ + c) ≤ 1 :=
    le_of_tendsto ((Edge_F_cont μ hne).tendsto.comp hpq) (hQ.mono fun a h => h.2.2.1)
  have h4 : c = Edge_S μ (z₀ + c) := by
    refine tendsto_nhds_unique hq (((Edge_S_cont μ hne).tendsto.comp hpq).congr' ?_)
    exact hQ.mono fun a h => h.2.2.2.1.symm
  exact ⟨h1, h2, h3, h4, h5⟩

private lemma Edge_Q_unique {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {z m₁ m₂ : ℂ} (h₁ : Edge_Q μ ℓ z m₁) (h₂ : Edge_Q μ ℓ z m₂) : m₁ = m₂ := by
  have e := Edge_unique μ h₁.1 h₂.1 (Edge_ne_of_norm hμ hℓ h₁.2.1) (Edge_ne_of_norm hμ hℓ h₂.2.1)
    h₁.2.2.1 h₂.2.2.1 (by rw [← h₁.2.2.2.1, ← h₂.2.2.2.1]; ring)
  linear_combination e

omit [Nonempty ι] in
private lemma Edge_Q_cluster {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {l : Filter ℂ} {z₀ x : ℂ} {f : ℂ → ℂ} (hl : l ≤ 𝓝 z₀)
    (hf : ∀ᶠ z in l, Edge_Q μ ℓ z (f z)) (hx : MapClusterPt x l f) : Edge_Q μ ℓ z₀ x := by
  obtain ⟨U, hU, hUx⟩ := mapClusterPt_iff_ultrafilter.1 hx
  exact Edge_Q_lim hμ hℓ (l := (U : Filter ℂ)) (tendsto_id.mono_left (hU.trans hl)) hUx (hU hf)

private lemma Edge_Q_tendsto {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {l : Filter ℂ} {z₀ c : ℂ} {f : ℂ → ℂ} (hl : l ≤ 𝓝 z₀)
    (hf : ∀ᶠ z in l, Edge_Q μ ℓ z (f z)) (hc : Edge_Q μ ℓ z₀ c) : Tendsto f l (𝓝 c) :=
  (isCompact_closedBall (0 : ℂ) 1).tendsto_nhds_of_unique_mapClusterPt
    (hf.mono fun z h => by simpa using h.2.2.2.2)
    fun x _ hx => Edge_Q_unique hμ hℓ (Edge_Q_cluster hμ hℓ hl hf hx) hc

omit [Nonempty ι] in
private lemma Edge_Hm_Q {μ : ι → ℝ} {ℓ : ℝ} {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) {z : ℂ}
    (hz : 0 < z.im) : Edge_Q μ ℓ z (m z) := by
  obtain ⟨h1, h2, h3, h4⟩ := hm z hz
  refine ⟨by simp; linarith, h4.le, ?_, h2, h3.le⟩
  have := congrArg Complex.im h2
  rw [Edge_S_im, Complex.add_im] at this
  by_contra hc; rw [not_le] at hc
  nlinarith

/-- The vertical approach `x + iη`, `η ↓ 0`, stays in the upper half plane. -/
private lemma Edge_vert (x : ℂ) (hx : x.im = 0) :
    Tendsto (fun η : ℝ => x + (η : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝[{z : ℂ | 0 < z.im}] x) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · have : Tendsto (fun η : ℝ => x + (η : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (x + ((0 : ℝ) : ℂ) * Complex.I)) :=
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with η hη
    simp [hx]; exact hη

/-- `m` extended to `ℂ` as in Definition 2.7 [defn_Mm]: reflection below the axis and the vertical
limit on the axis. -/
private def Edge_mext (m : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then m z
  else if z.im < 0 then star (m (star z))
  else limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => m (z + (η : ℂ) * Complex.I)

/-- `π⁻¹ lim_{η↓0} Im m(x + iη)`, the density (2.19) [eq:density_rhoN] built from `m`. -/
private def Edge_rho (m : ℂ → ℂ) (x : ℝ) : ℝ :=
  (limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => (m ((x : ℂ) + (η : ℂ) * Complex.I)).im) / Real.pi

/-- On the real axis the boundary value satisfies the closed conditions and is the limit of `m`
from the upper half plane. -/
private lemma Edge_mext_real {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) (x : ℂ) (hx : x.im = 0) :
    Edge_Q μ ℓ x (Edge_mext m x) ∧
      Tendsto m (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (Edge_mext m x)) := by
  have hv := Edge_vert x hx
  have : (𝓝[{z : ℂ | 0 < z.im}] x).NeBot := hv.neBot
  have hf : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] x, Edge_Q μ ℓ z (m z) :=
    eventually_nhdsWithin_of_forall fun z hz => Edge_Hm_Q hm hz
  obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_mapClusterPt
    (f := 𝓝[{z : ℂ | 0 < z.im}] x) (u := m)
    (Filter.le_principal_iff.2 (hf.mono fun z h => by simpa using h.2.2.2.2))
  have hQc := Edge_Q_cluster hμ hℓ nhdsWithin_le_nhds hf hc
  have hT := Edge_Q_tendsto hμ hℓ nhdsWithin_le_nhds hf hQc
  have e : Edge_mext m x = c := by
    unfold Edge_mext
    simp only [hx, lt_irrefl, ↓reduceIte]
    exact (hT.comp hv).limUnder_eq
  rw [e]; exact ⟨hQc, hT⟩

private lemma Edge_mext_Q {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) (z : ℂ) (hz : 0 ≤ z.im) : Edge_Q μ ℓ z (Edge_mext m z) := by
  rcases hz.lt_or_eq with h | h
  · have e : Edge_mext m z = m z := by unfold Edge_mext; simp [h]
    rw [e]; exact Edge_Hm_Q hm h
  · exact (Edge_mext_real hμ hℓ hm z h.symm).1

private lemma Edge_mext_cont {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) : ContinuousOn (Edge_mext m) {z : ℂ | 0 ≤ z.im} := fun z hz =>
  Edge_Q_tendsto hμ hℓ nhdsWithin_le_nhds
    (eventually_nhdsWithin_of_forall fun w hw => Edge_mext_Q hμ hℓ hm w hw)
    (Edge_mext_Q hμ hℓ hm z hz)

private lemma Edge_rho_eq {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) (x : ℝ) :
    Edge_rho m x = (Edge_mext m x).im / Real.pi := by
  have h := (Edge_mext_real hμ hℓ hm x (Complex.ofReal_im x)).2
  have h2 := ((Complex.continuous_im.tendsto _).comp (h.comp (Edge_vert x (Complex.ofReal_im x))))
  unfold Edge_rho
  congr 1
  exact h2.limUnder_eq

omit [Nonempty ι] in
private lemma Edge_S_real (μ : ι → ℝ) (u : ℝ) :
    Edge_S μ (u : ℂ) = ((-Edge_av (fun j => (u - μ j)⁻¹) : ℝ) : ℂ) := by
  unfold Edge_S
  rw [← Edge_av_neg, ← Edge_avc_ofReal]
  congr 1; funext j
  rw [← inv_neg, neg_sub]; push_cast; rfl

omit [Nonempty ι] in
private lemma Edge_F_real (μ : ι → ℝ) (u : ℝ) : Edge_F μ (u : ℂ) = Edge_G μ u := by
  unfold Edge_F Edge_G
  congr 1; funext j
  rw [norm_inv, show (μ j : ℂ) - u = ((μ j - u : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, inv_pow, sq_abs]
  ring_nf

omit [Nonempty ι] in
private lemma Edge_Q_neg (μ : ι → ℝ) (ℓ : ℝ) (z m : ℂ) :
    Edge_Q (fun j => -μ j) ℓ (-star z) (-star m) ↔ Edge_Q μ ℓ z m := by
  have e : -star z + -star m = -star (z + m) := by rw [star_add]; ring
  unfold Edge_Q
  rw [e, Edge_F_neg, Edge_S_neg, norm_neg, norm_star, norm_neg, norm_star]
  simp only [Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg, neg_inj]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, (RingHom.injective _ h4), h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, by rw [← h4], h5⟩

/-- A real point `u ≥ w₊` gives the real boundary value `u - φ(u)` at `φ(u)`. -/
private lemma Edge_real_Q {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (u : ℝ)
    (hu : Edge_wp μ ≤ u) : Edge_Q μ ℓ (Edge_phi μ u : ℂ) ((u - Edge_phi μ u : ℝ) : ℂ) := by
  obtain ⟨hx, hG, h1, -⟩ := Edge_wp_spec hμ hℓ
  have hl0 := Edge_l0 hμ
  have hu' : ∀ j, μ j < u := fun j => (hx j).trans_le hu
  have e : (Edge_phi μ u : ℂ) + ((u - Edge_phi μ u : ℝ) : ℂ) = (u : ℂ) := by push_cast; ring
  have hav : 0 ≤ Edge_av (fun j => (u - μ j)⁻¹) ∧ Edge_av (fun j => (u - μ j)⁻¹) ≤ 1 := by
    constructor
    · calc (0 : ℝ) = Edge_av (fun _ : ι => (0 : ℝ)) := (Edge_av_const _).symm
        _ ≤ _ := Edge_av_le fun j => by have := hu' j; exact inv_nonneg.2 (by linarith)
    · calc _ ≤ Edge_av (fun j => (1 + ((Edge_wp μ - μ j) ^ 2)⁻¹) / 2) := Edge_av_le fun j => by
            have h0 : 0 < Edge_wp μ - μ j := by linarith [hx j]
            have h2 : (u - μ j)⁻¹ ≤ (Edge_wp μ - μ j)⁻¹ := inv_anti₀ h0 (by linarith)
            have h3 : (Edge_wp μ - μ j)⁻¹ ≤ (1 + ((Edge_wp μ - μ j) ^ 2)⁻¹) / 2 := by
              rw [← inv_pow]; nlinarith [sq_nonneg ((Edge_wp μ - μ j)⁻¹ - 1)]
            linarith
        _ = 1 := by
            rw [show (fun j => (1 + ((Edge_wp μ - μ j) ^ 2)⁻¹) / 2) =
              fun j => (1 / 2) * 1 + (1 / 2) * ((Edge_wp μ - μ j) ^ 2)⁻¹ from funext fun j => by ring,
              Edge_av_add, Edge_av_mul, Edge_av_mul, Edge_av_const]
            unfold Edge_G at hG; rw [hG]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; simp
  · rw [e, Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_nonneg (by linarith)]; linarith
  · rw [e, Edge_F_real]; exact hG ▸ Edge_G_le hx hu
  · rw [e, Edge_S_real]; unfold Edge_phi; push_cast; ring
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; unfold Edge_phi; constructor <;> linarith

/-- For `E ≥ E⁺` there is a real `u ≥ w₊` with `φ(u) = E`. -/
private lemma Edge_root {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (E : ℝ)
    (hE : Edge_ep μ ≤ E) : ∃ u, Edge_wp μ ≤ u ∧ Edge_phi μ u = E := by
  obtain ⟨hx, -, -, h2⟩ := Edge_wp_spec hμ hℓ
  have hep := (Edge_ep_bd hμ hℓ).1
  have hl0 := Edge_l0 hμ
  have hwE : Edge_wp μ ≤ E := by linarith
  have hcont : ContinuousOn (Edge_phi μ) (Set.Icc (Edge_wp μ) E) := by
    have : ∀ j, ContinuousOn (fun u : ℝ => (u - μ j)⁻¹) (Set.Icc (Edge_wp μ) E) := fun j =>
      ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn fun u hu => by
        have := hx j; have := hu.1; exact (by linarith : 0 < u - μ j).ne'
    show ContinuousOn (fun u : ℝ => u + ((Fintype.card ι : ℝ))⁻¹ * ∑ j, (u - μ j)⁻¹) _
    exact continuousOn_id.add (continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => this j))
  have hE2 : E ≤ Edge_phi μ E := by
    unfold Edge_phi
    have : 0 ≤ Edge_av (fun j => (E - μ j)⁻¹) :=
      calc (0 : ℝ) = Edge_av (fun _ : ι => (0 : ℝ)) := (Edge_av_const _).symm
        _ ≤ _ := Edge_av_le fun j => by have := hx j; exact inv_nonneg.2 (by linarith)
    linarith
  obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc hwE hcont ⟨hE, hE2⟩
  exact ⟨u, hu.1, hu'⟩

omit [Nonempty ι] in
/-- `x ↦ -x` maps the boundary values of `m` to those of `z ↦ -conj m(-conj z)`. -/
private lemma Edge_Hm_neg {μ : ι → ℝ} {ℓ : ℝ} {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    Edge_Hm (fun j => -μ j) ℓ (fun z => -star (m (-star z))) := by
  intro z hz
  have hz' : 0 < (-star z).im := by simpa using hz
  obtain ⟨h1, h2, h3, h4⟩ := hm _ hz'
  have e : z + -star (m (-star z)) = -star (-star z + m (-star z)) := by
    rw [star_add, star_neg, star_star]; ring
  refine ⟨by simpa using h1, ?_, by rwa [norm_neg, norm_star], ?_⟩
  · rw [e, Edge_S_neg, ← h2]
  · rwa [e, norm_neg, norm_star]

/-- `ρ(x) = 0` for `x ≥ E⁺` or `x ≤ E⁻`, and `ρ(x) > 0` in between. -/
private lemma Edge_rho_pos_iff {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) (E : ℝ) :
    (Edge_ep μ ≤ E → (Edge_mext m E).im = 0) ∧ (E ≤ Edge_em μ → (Edge_mext m E).im = 0) ∧
      (Edge_em μ < E → E < Edge_ep μ → 0 < (Edge_mext m E).im) := by
  have hQ := (Edge_mext_real hμ hℓ hm (E : ℂ) (Complex.ofReal_im E)).1
  refine ⟨fun hE => ?_, fun hE => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := Edge_root hμ hℓ E hE
    rw [Edge_Q_unique hμ hℓ hQ (Edge_real_Q hμ hℓ u hu)]; simp
  · have hμ' := Edge_neg_bd hμ
    obtain ⟨u, hu, hu'⟩ := Edge_root hμ' hℓ (-E) (by unfold Edge_em at hE; linarith)
    have h : Edge_Q μ ℓ (E : ℂ) (-((u + E : ℝ) : ℂ)) := by
      rw [← Edge_Q_neg]
      have := Edge_real_Q hμ' hℓ u hu
      rw [hu'] at this
      have e1 : -star (E : ℂ) = ((-E : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
      have e2 : -star (-((u + E : ℝ) : ℂ)) = ((u - -E : ℝ) : ℂ) := by
        rw [star_neg, neg_neg, Complex.star_def, Complex.conj_ofReal]; push_cast; ring
      rw [e1, e2]; exact this
    rw [Edge_Q_unique hμ hℓ hQ h]; simp
  · obtain ⟨him, hnorm, -, hS, -⟩ := hQ
    rw [Complex.add_im, Complex.ofReal_im, zero_add] at him
    rcases him.lt_or_eq with h | h
    · exact h
    exfalso
    set c := Edge_mext m E
    have hw : (E : ℂ) + c = ((E + c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [← h]
    have hphi : Edge_phi μ (E + c.re) = E := by
      have := congrArg Complex.re hS
      rw [hw, Edge_S_real] at this
      simp only [Complex.ofReal_re] at this
      unfold Edge_phi; linarith
    rw [hw, Complex.norm_real, Real.norm_eq_abs] at hnorm
    have hl0 := Edge_l0 hμ
    rcases le_or_gt 0 (E + c.re) with hp | hn
    · rw [abs_of_nonneg hp] at hnorm
      have := Edge_phi_ge hμ hℓ (E + c.re) fun j => by linarith [(abs_le.1 (hμ j)).2]
      linarith
    · rw [abs_of_neg hn] at hnorm
      have := Edge_phi_ge (Edge_neg_bd hμ) hℓ (-(E + c.re)) fun j => by
        linarith [(abs_le.1 (hμ j)).1]
      rw [Edge_phi_neg] at this
      unfold Edge_em at h1
      linarith

/-- The support of `ρ` is `(E⁻, E⁺)`. -/
private lemma Edge_support {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    Function.support (Edge_rho m) = Set.Ioo (Edge_em μ) (Edge_ep μ) := by
  ext x
  rw [Function.mem_support, Edge_rho_eq hμ hℓ hm, Set.mem_Ioo, div_ne_zero_iff]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨h1, h2, h3⟩ := Edge_rho_pos_iff hμ hℓ hm x
  constructor
  · rintro ⟨h, -⟩
    constructor
    · by_contra hc; exact h (h2 (not_lt.1 hc))
    · by_contra hc; exact h (h1 (not_lt.1 hc))
  · rintro ⟨ha, hb⟩; exact ⟨(h3 ha hb).ne', hπ⟩

private lemma Edge_em_lt {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) :
    Edge_em μ < Edge_ep μ := by
  have h1 := (Edge_ep_bd hμ hℓ).1
  have h2 := (Edge_ep_bd (Edge_neg_bd hμ) hℓ).1
  unfold Edge_em; linarith

private lemma Edge_Ep_eq {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    sSup (Function.support (Edge_rho m)) = Edge_ep μ ∧
      sInf (Function.support (Edge_rho m)) = Edge_em μ := by
  rw [Edge_support hμ hℓ hm]
  exact ⟨csSup_Ioo (Edge_em_lt hμ hℓ), csInf_Ioo (Edge_em_lt hμ hℓ)⟩

/-- `m(E⁺) = w₊ - E⁺` is real. -/
private lemma Edge_mext_ep {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    Edge_mext m (Edge_ep μ) = ((Edge_wp μ - Edge_ep μ : ℝ) : ℂ) :=
  Edge_Q_unique hμ hℓ (Edge_mext_real hμ hℓ hm _ (Complex.ofReal_im _)).1
    (Edge_real_Q hμ hℓ (Edge_wp μ) le_rfl)

/-! ### The limits (2.6) -/

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_F_sq (q : ℂ) (hq : 0 ≤ q.im) :
    Real.sqrt ((‖q ^ 2‖ - (q ^ 2).re) / 2) = q.im := by
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re]
  rw [show (q.re * q.re + q.im * q.im - (q.re * q.re - q.im * q.im)) / 2 = q.im ^ 2 by ring]
  exact Real.sqrt_sq hq

/-- `⟨(w₊ - Λ)⁻³⟩ ∈ [5/6, 5/4]`, with `w₊ - μ_j ≠ 0`. -/
private lemma Edge_c3_bd {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) :
    5 / 6 ≤ Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹) ∧
      Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹) ≤ 5 / 4 ∧ ∀ j, (Edge_wp μ - μ j) ^ 3 ≠ 0 := by
  have hG := (Edge_wp_spec hμ hℓ).2.1
  have h := Edge_av_wt (w := fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹) (r := fun j => (Edge_wp μ - μ j)⁻¹)
    (p := 5 / 6) (q := 5 / 4) (fun j => inv_nonneg.2 (sq_nonneg _)) hG fun j => by
      have := Edge_x_bd hμ hℓ j
      constructor
      · rw [le_inv_comm₀ (by norm_num) (by linarith)]; norm_num; linarith
      · rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
  have e : (fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹ * (Edge_wp μ - μ j)⁻¹) =
      fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹ := funext fun j => by rw [← mul_inv, ← pow_succ]
  rw [e] at h
  refine ⟨h.1, h.2, fun j => pow_ne_zero _ ?_⟩
  have := (Edge_wp_spec hμ hℓ).1 j
  linarith

omit [Nonempty ι] in
private lemma Edge_g_cont (μ : ι → ℝ) {w : ℂ} (hw : ∀ j, (μ j : ℂ) ≠ w) :
    ContinuousAt (Edge_g μ) w := by
  unfold Edge_g Edge_avc
  have hne : ∀ j, w - (μ j : ℂ) ≠ 0 := fun j => sub_ne_zero.2 (hw j).symm
  fun_prop (disch := exact hne _)

private lemma Edge_g_wp {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) :
    Edge_g μ (Edge_wp μ) = ((Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹) : ℝ) : ℂ) := by
  have hx := (Edge_wp_spec hμ hℓ).1
  unfold Edge_g
  rw [← Edge_avc_ofReal]
  congr 1; funext j
  have : ((Edge_wp μ : ℂ) - (μ j : ℂ)) = ((Edge_wp μ - μ j : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  have h0 : Edge_wp μ - μ j ≠ 0 := by linarith [hx j]
  push_cast
  field_simp

/-- (2.6) [eq:def_gamma] at `E⁺`: `ρ(E)/√(E⁺ - E) → ⟨(w₊ - Λ)⁻³⟩^{-1/2}/π`. -/
private lemma Edge_gamma_lim {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    Tendsto (fun E => Edge_rho m E / Real.sqrt (Edge_ep μ - E)) (𝓝[<] (Edge_ep μ))
      (𝓝 ((Real.sqrt (Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹)))⁻¹ / Real.pi)) := by
  obtain ⟨hx, -, -, -⟩ := Edge_wp_spec hμ hℓ
  set c₃ := Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹) with hc₃
  have hc := Edge_c3_bd hμ hℓ
  set w : ℝ → ℂ := fun E => (E : ℂ) + Edge_mext m E with hwdef
  have hwp : ∀ j, (μ j : ℂ) ≠ (Edge_wp μ : ℂ) := fun j => by
    exact_mod_cast (hx j).ne
  -- `w(E) → w₊`
  have hw : Tendsto w (𝓝[<] (Edge_ep μ)) (𝓝 (Edge_wp μ : ℂ)) := by
    have h1 := Edge_mext_cont hμ hℓ hm (Edge_ep μ : ℂ) (by simp)
    have h2 : Tendsto (fun E : ℝ => (E : ℂ)) (𝓝[<] (Edge_ep μ))
        (𝓝[{z : ℂ | 0 ≤ z.im}] (Edge_ep μ : ℂ)) := by
      apply tendsto_nhdsWithin_iff.2
      exact ⟨(Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds,
        Eventually.of_forall fun E => by simp⟩
    have h3 := (Complex.continuous_ofReal.tendsto (Edge_ep μ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (Edge_ep μ)))
    have h4 := h3.add (h1.tendsto.comp h2)
    rw [Edge_mext_ep hμ hℓ hm] at h4
    have e : (Edge_wp μ : ℂ) = (Edge_ep μ : ℂ) + ((Edge_wp μ - Edge_ep μ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact h4
  set Fq : ℂ → ℝ := fun p => Real.sqrt ((‖p‖ - p.re) / 2) with hFq
  have hgc : Edge_g μ (Edge_wp μ) ≠ 0 := by
    rw [Edge_g_wp hμ hℓ]; exact_mod_cast (by linarith [hc.1] : c₃ ≠ 0)
  have hFc : ContinuousAt (fun w => Fq (-(Edge_g μ w)⁻¹)) (Edge_wp μ : ℂ) := by
    have : ContinuousAt (fun w => -(Edge_g μ w)⁻¹) (Edge_wp μ : ℂ) :=
      ((Edge_g_cont μ hwp).inv₀ hgc).neg
    exact (Real.continuous_sqrt.continuousAt.comp
      (((continuous_norm.continuousAt.comp this).sub
        (Complex.continuous_re.continuousAt.comp this)).div_const 2))
  have hlim := hFc.tendsto.comp hw
  have hval : Fq (-(Edge_g μ (Edge_wp μ))⁻¹) = (Real.sqrt c₃)⁻¹ := by
    rw [Edge_g_wp hμ hℓ, hFq]
    simp only
    rw [show (-(((c₃ : ℝ) : ℂ))⁻¹) = ((-c₃⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, Complex.ofReal_re, abs_neg, abs_of_pos (inv_pos.2 (by linarith [hc.1])),
      ← Real.sqrt_inv]
    congr 1; ring
  rw [hval] at hlim
  refine (hlim.div_const Real.pi).congr' ?_
  have hem := Edge_em_lt hμ hℓ
  filter_upwards [Ioo_mem_nhdsLT hem] with E hE
  -- the identity at `E ∈ (E⁻, E⁺)`
  have hb := (Edge_rho_pos_iff hμ hℓ hm E).2.2 hE.1 hE.2
  have hQ := (Edge_mext_real hμ hℓ hm (E : ℂ) (Complex.ofReal_im E)).1
  have hne := Edge_ne_of_norm hμ hℓ hQ.2.1
  have hid := Edge_Phi_id hμ hℓ ((E : ℂ) + Edge_mext m E) hne
  rw [← hQ.2.2.2.1, add_sub_cancel_right] at hid
  set g := Edge_g μ ((E : ℂ) + Edge_mext m E)
  set d := (E : ℂ) + Edge_mext m E - (Edge_wp μ : ℂ)
  have hpos : 0 < Edge_ep μ - E := by linarith [hE.2]
  have hs : 0 < Real.sqrt (Edge_ep μ - E) := Real.sqrt_pos.2 hpos
  have hg0 : g ≠ 0 := fun h0 => by
    rw [h0, mul_zero, sub_eq_zero] at hid
    have := congrArg Complex.re hid; simp at this; linarith
  set q := d / ((Real.sqrt (Edge_ep μ - E) : ℝ) : ℂ)
  have hq2 : q ^ 2 = -g⁻¹ := by
    have hss : ((Real.sqrt (Edge_ep μ - E) : ℝ) : ℂ) ^ 2 = ((Edge_ep μ - E : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le]
    have hsne : ((Edge_ep μ - E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [div_pow, hss, eq_neg_iff_add_eq_zero, div_add' _ _ _ hsne, div_eq_zero_iff]
    left
    have : d ^ 2 = ((E : ℂ) - Edge_ep μ) / g := by rw [eq_div_iff hg0, ← hid]
    rw [this]; field_simp; push_cast; ring
  have hqim : q.im = (Edge_mext m E).im / Real.sqrt (Edge_ep μ - E) := by
    simp only [q, d, Complex.div_ofReal_im, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      zero_add, sub_zero]
  have := Edge_F_sq q (by rw [hqim]; exact div_nonneg hb.le hs.le)
  change Real.sqrt ((‖-g⁻¹‖ - (-g⁻¹).re) / 2) / Real.pi = _
  rw [← hq2, this, hqim, Edge_rho_eq hμ hℓ hm]
  ring

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_rho_neg (m : ℂ → ℂ) (x : ℝ) :
    Edge_rho (fun z => -star (m (-star z))) (-x) = Edge_rho m x := by
  unfold Edge_rho
  congr 2; funext η
  have : -star (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I) = (x : ℂ) + (η : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  show (-star (m (-star (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)))).im = _
  rw [this, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

/-- (2.6) [eq:def_gamma] at `E⁻`. -/
private lemma Edge_gamma_lim' {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    Tendsto (fun E => Edge_rho m E / Real.sqrt (E - Edge_em μ)) (𝓝[>] (Edge_em μ))
      (𝓝 ((Real.sqrt (Edge_av (fun j => ((Edge_wp (fun j => -μ j) - -μ j) ^ 3)⁻¹)))⁻¹ /
        Real.pi)) := by
  have ht : Tendsto (fun x : ℝ => -x) (𝓝[>] (Edge_em μ)) (𝓝[<] (Edge_ep (fun j => -μ j))) := by
    have := tendsto_neg_nhdsGT (a := Edge_em μ)
    rwa [show -Edge_em μ = Edge_ep (fun j => -μ j) by unfold Edge_em; ring] at this
  have h := (Edge_gamma_lim (Edge_neg_bd hμ) hℓ (Edge_Hm_neg hm)).comp ht
  refine h.congr fun E => ?_
  simp only [Function.comp, Edge_rho_neg]
  congr 2; unfold Edge_em; ring

private lemma Edge_rpow_bd {y : ℝ} (h1 : 1 / 2 ≤ y) (h2 : y ≤ 2) :
    1 / 2 ≤ y ^ (2 / 3 : ℝ) ∧ y ^ (2 / 3 : ℝ) ≤ 2 := by
  rcases le_total y 1 with h | h
  · exact ⟨h1.trans (Real.self_le_rpow_of_le_one (by linarith) h (by norm_num)),
      (Real.rpow_le_one (by linarith) h (by norm_num)).trans (by norm_num)⟩
  · exact ⟨(by norm_num : (1 : ℝ) / 2 ≤ 1).trans (Real.one_le_rpow h (by norm_num)),
      (Real.rpow_le_self_of_one_le h (by norm_num)).trans h2⟩

private lemma Edge_inv_sqrt_bd {c : ℝ} (h1 : 5 / 6 ≤ c) (h2 : c ≤ 5 / 4) :
    1 / 2 ≤ (Real.sqrt c)⁻¹ ∧ (Real.sqrt c)⁻¹ ≤ 2 := by
  have hs1 : 1 / 2 ≤ Real.sqrt c := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs2 : Real.sqrt c ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  constructor
  · rw [le_inv_comm₀ (by norm_num) (by linarith)]; linarith
  · rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

private lemma Edge_rpow_inv {y : ℝ} (hy : 0 ≤ y) : (y ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = y := by
  rw [← Real.rpow_mul hy]; norm_num

/-! ### Square-root behaviour near the edges -/

omit [Nonempty ι] in
private lemma Edge_g_parts (μ : ι → ℝ) (w : ℂ) :
    (Edge_g μ w).re = Edge_av (fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹ *
        ((w.re - μ j) / ((w.re - μ j) ^ 2 + w.im ^ 2))) ∧
      (Edge_g μ w).im = -w.im * Edge_av (fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹ *
        ((w.re - μ j) ^ 2 + w.im ^ 2)⁻¹) := by
  unfold Edge_g
  rw [Edge_avc_re, Edge_avc_im, ← Edge_av_mul]
  constructor <;> congr 1 <;> funext j
  · rw [Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring_nf
  · rw [Complex.im_ofReal_mul, Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring

/-- Near `w₊`: `ζ = w - s(w) - E⁺ = (w - w₊)² g(w)` in real coordinates `w - w₊ = a + ib`. -/
private lemma Edge_near_core {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (w : ℂ)
    (ha : |w.re - Edge_wp μ| ≤ 1 / 20) (hb : 0 ≤ w.im) (hb' : w.im ≤ 1 / 20) :
    ∃ R T : ℝ, 47 / 100 ≤ R ∧ R ≤ 23 / 10 ∧ 0 ≤ T ∧ T ≤ 16 / 9 ∧
      (w - Edge_S μ w - Edge_ep μ).re =
        ((w.re - Edge_wp μ) ^ 2 - w.im ^ 2) * R + 2 * (w.re - Edge_wp μ) * w.im ^ 2 * T ∧
      (w - Edge_S μ w - Edge_ep μ).im =
        2 * (w.re - Edge_wp μ) * w.im * R - ((w.re - Edge_wp μ) ^ 2 - w.im ^ 2) * w.im * T := by
  obtain ⟨hx, hG, -, -⟩ := Edge_wp_spec hμ hℓ
  have hab := abs_le.1 ha
  have hu : ∀ j, 3 / 4 ≤ w.re - μ j ∧ w.re - μ j ≤ 5 / 4 := fun j => by
    have := Edge_x_bd hμ hℓ j; constructor <;> linarith
  have hne : ∀ j, (μ j : ℂ) ≠ w := fun j e => by
    have := congrArg Complex.re e; simp at this; linarith [(hu j).1]
  obtain ⟨hR, hT⟩ := Edge_g_parts μ w
  set R := (Edge_g μ w).re
  set T := Edge_av (fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹ * ((w.re - μ j) ^ 2 + w.im ^ 2)⁻¹)
  have hRb := Edge_av_wt (w := fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹)
    (r := fun j => (w.re - μ j) / ((w.re - μ j) ^ 2 + w.im ^ 2)) (p := 47 / 100) (q := 23 / 10)
    (fun j => inv_nonneg.2 (sq_nonneg _)) hG fun j => by
      have := hu j
      have hd : 0 < (w.re - μ j) ^ 2 + w.im ^ 2 := by nlinarith
      constructor
      · rw [le_div_iff₀ hd]; nlinarith
      · rw [div_le_iff₀ hd]; nlinarith
  have hTb := Edge_av_wt (w := fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹)
    (r := fun j => ((w.re - μ j) ^ 2 + w.im ^ 2)⁻¹) (p := 0) (q := 16 / 9)
    (fun j => inv_nonneg.2 (sq_nonneg _)) hG fun j => by
      have := hu j
      have hd : 9 / 16 ≤ (w.re - μ j) ^ 2 + w.im ^ 2 := by nlinarith
      exact ⟨inv_nonneg.2 (by linarith), by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith⟩
  have hid := Edge_Phi_id hμ hℓ w hne
  refine ⟨R, T, ?_, ?_, hTb.1, hTb.2, ?_, ?_⟩
  · rw [hR]; exact hRb.1
  · rw [hR]; exact hRb.2
  · rw [hid, Complex.mul_re, sq, Complex.mul_re, Complex.mul_im, hT]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  · rw [hid, Complex.mul_im, sq, Complex.mul_re, Complex.mul_im, hT]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring

set_option maxHeartbeats 1000000 in
/-- The real algebra of the near-edge equations. -/
private lemma Edge_alg {a b R T X Y : ℝ} (hb : 0 ≤ b) (ha : |a| ≤ 1 / 20) (hb' : b ≤ 1 / 20)
    (hR : 47 / 100 ≤ R) (hR' : R ≤ 23 / 10) (hT : 0 ≤ T) (hT' : T ≤ 16 / 9)
    (hX : X = (a ^ 2 - b ^ 2) * R + 2 * a * b ^ 2 * T)
    (hY : Y = 2 * a * b * R - (a ^ 2 - b ^ 2) * b * T) :
    (X ≤ 0 → a ^ 2 ≤ 2 * b ^ 2) ∧
      (0 < X → 0 < Y → 0 < a ∧ b ^ 2 ≤ 8 * a ^ 2 ∧ 4 / 5 * a * b ≤ Y ∧ Y ≤ 6 * a * b) ∧
      (47 / 100) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 ≤ X ^ 2 + Y ^ 2 ∧
      X ^ 2 + Y ^ 2 ≤ 6 * (a ^ 2 + b ^ 2) ^ 2 := by
  have hab := abs_le.1 ha
  have hXY : X ^ 2 + Y ^ 2 = (a ^ 2 + b ^ 2) ^ 2 * (R ^ 2 + b ^ 2 * T ^ 2) := by
    rw [hX, hY]; ring
  have haT : |2 * a * T| ≤ 1 / 5 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hT]
    have : |a| * T ≤ 1 / 20 * (16 / 9) := mul_le_mul ha hT' hT (by norm_num)
    norm_num at this ⊢; linarith
  have haT' := abs_le.1 haT
  refine ⟨fun h => ?_, fun h1 h2 => ?_, ?_, ?_⟩
  · rw [hX] at h
    have : a ^ 2 * R ≤ b ^ 2 * (R + 2 * a * T * (-1)) + b ^ 2 * (2 * a * T * 0) := by nlinarith
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) (by linarith : (0 : ℝ) ≤ R - 1 / 5)]
  · have ha0 : 0 < a := by
      by_contra hc; rw [not_lt] at hc
      rw [hX] at h1; rw [hY] at h2
      have h3 : b ^ 2 < a ^ 2 := by
        by_contra h4; rw [not_lt] at h4
        nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 hc) (sq_nonneg b)) hT]
      nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 hc) hb) (by linarith : (0 : ℝ) ≤ R),
        mul_nonneg (mul_nonneg (sub_nonneg.2 h3.le) hb) hT]
    have hb8 : b ^ 2 ≤ 8 * a ^ 2 := by
      rw [hX] at h1
      have h5 : 0 < R - 2 * a * T := by linarith
      nlinarith [mul_nonneg (sq_nonneg b) h5.le, mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ R)]
    refine ⟨ha0, hb8, ?_, ?_⟩
    · rw [hY]
      have : 4 / 5 * a ≤ 2 * a * R - (a ^ 2 - b ^ 2) * T := by
        nlinarith [mul_nonneg (sq_nonneg b) hT, mul_nonneg (mul_nonneg ha0.le ha0.le) hT]
      nlinarith [mul_le_mul_of_nonneg_right this hb]
    · rw [hY]
      have : 2 * a * R - (a ^ 2 - b ^ 2) * T ≤ 6 * a := by
        nlinarith [mul_nonneg (sq_nonneg a) hT, mul_le_mul_of_nonneg_right hb8 hT]
      nlinarith [mul_le_mul_of_nonneg_right this hb]
  · rw [hXY]
    have : (47 / 100) ^ 2 ≤ R ^ 2 + b ^ 2 * T ^ 2 := by nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg T)]
    nlinarith [sq_nonneg (a ^ 2 + b ^ 2)]
  · rw [hXY]
    have : R ^ 2 + b ^ 2 * T ^ 2 ≤ 6 := by
      have : b ^ 2 ≤ 1 / 400 := by nlinarith
      have : T ^ 2 ≤ (16 / 9) ^ 2 := by nlinarith
      nlinarith [mul_le_mul this (by linarith : T ^ 2 ≤ (16 / 9) ^ 2) (sq_nonneg T) (by norm_num)]
    nlinarith [sq_nonneg (a ^ 2 + b ^ 2)]

/-- `|w - w₊|² ≤ 50 |w - s(w) - E⁺|` for `Re w ≥ 1/2`, `|w| ≤ 4`. -/
private lemma Edge_d_small {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (w : ℂ)
    (hu : 1 / 2 ≤ w.re) (hw : ‖w‖ ≤ 4) :
    ‖w - Edge_wp μ‖ ^ 2 ≤ 50 * ‖w - Edge_S μ w - Edge_ep μ‖ := by
  obtain ⟨-, hG, -, -⟩ := Edge_wp_spec hμ hℓ
  have hne : ∀ j, (μ j : ℂ) ≠ w := fun j e => by
    have := congrArg Complex.re e; simp at this; linarith [(abs_le.1 (hμ j)).2]
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 16 := by
    have : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg w]
  have hre := (Edge_g_parts μ w).1
  have hRb := Edge_av_wt (w := fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹)
    (r := fun j => (w.re - μ j) / ((w.re - μ j) ^ 2 + w.im ^ 2)) (p := 1 / 50) (q := 5 / 2)
    (fun j => inv_nonneg.2 (sq_nonneg _)) hG fun j => by
      have := abs_le.1 (hμ j)
      have h0 : 2 / 5 ≤ w.re - μ j := by linarith
      have hd : 0 < (w.re - μ j) ^ 2 + w.im ^ 2 := by nlinarith
      have hwr : |w.re| ≤ 4 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg w.im]
      have hwr' := abs_le.1 hwr
      constructor
      · rw [le_div_iff₀ hd]; nlinarith
      · rw [div_le_iff₀ hd]; nlinarith [sq_nonneg w.im]
  have hid := Edge_Phi_id hμ hℓ w hne
  rw [hid, norm_mul, norm_pow]
  have : (1 : ℝ) / 50 ≤ ‖Edge_g μ w‖ := hRb.1.trans (hre ▸ Complex.re_le_norm _)
  nlinarith [sq_nonneg ‖w - (Edge_wp μ : ℂ)‖]

/-- If `Im w = b` with `b² ≤ 1/100`, `|w| ≥ 1 - ℓ` and `Re w > 0`, then
`Re(w - s(w)) ≥ E⁺ - 3b²`. -/
private lemma Edge_far_in {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (w : ℂ)
    (hn : 1 - ℓ ≤ ‖w‖) (hb : w.im ^ 2 ≤ 1 / 100) (hu : 0 < w.re) :
    Edge_ep μ - 3 * w.im ^ 2 ≤ (w - Edge_S μ w).re := by
  have hl0 := Edge_l0 hμ
  have hw2 : (1 - ℓ) ^ 2 ≤ w.re ^ 2 + w.im ^ 2 := by
    have : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith
  have hu2 : 4 / 5 ≤ w.re ^ 2 := by nlinarith
  have hu1 : 89 / 100 ≤ w.re := by nlinarith
  have hx : ∀ j, 79 / 100 ≤ w.re - μ j := fun j => by linarith [(abs_le.1 (hμ j)).2]
  have e : (w - Edge_S μ w).re = w.re +
      Edge_av (fun j => (w.re - μ j) / ((w.re - μ j) ^ 2 + w.im ^ 2)) := by
    unfold Edge_S
    rw [Complex.sub_re, Edge_avc_re, sub_eq_add_neg, ← Edge_av_neg]
    congr 2; funext j
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    ring
  have h1 := Edge_phi_ge hμ hℓ w.re fun j => by linarith [hx j, (abs_le.1 (hμ j)).2]
  have h2 : Edge_av (fun j => (w.re - μ j)⁻¹) - 3 * w.im ^ 2 ≤
      Edge_av (fun j => (w.re - μ j) / ((w.re - μ j) ^ 2 + w.im ^ 2)) := by
    rw [← Edge_av_const (ι := ι) (3 * w.im ^ 2), ← Edge_av_sub]
    refine Edge_av_le fun j => ?_
    have := hx j
    have hp : 0 < w.re - μ j := by linarith
    have hd : 0 < (w.re - μ j) ^ 2 + w.im ^ 2 := by positivity
    rw [le_div_iff₀ hd, sub_mul, inv_mul_eq_div, add_div, sq, mul_self_div_self, ← sq]
    have h3 : 1 / 3 ≤ (w.re - μ j) ^ 3 := by nlinarith
    have h4 : w.im ^ 2 / (w.re - μ j) ≤ 3 * w.im ^ 2 * ((w.re - μ j) ^ 2 + w.im ^ 2) := by
      rw [div_le_iff₀ hp]; nlinarith [sq_nonneg w.im, mul_nonneg (sq_nonneg w.im) (sq_nonneg w.im)]
    nlinarith
  unfold Edge_phi at h1
  rw [e]; linarith

/-- The comparison `|(w - s(w)) - φ(u)| ≥ Im w (1 - G(u))/2` for real `u ≥ w₊`. -/
private lemma Edge_cmp {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (w : ℂ)
    (hb : 0 < w.im) (hF : Edge_F μ w ≤ 1) (u : ℝ) (hu : Edge_wp μ ≤ u) :
    w.im * (1 - Edge_G μ u) / 2 ≤ ‖w - Edge_S μ w - (Edge_phi μ u : ℂ)‖ := by
  obtain ⟨hx, hG, -, -⟩ := Edge_wp_spec hμ hℓ
  have hGu : Edge_G μ u ≤ 1 := hG ▸ Edge_G_le hx hu
  have hne : ∀ j, (μ j : ℂ) ≠ w := fun j e => by rw [← e] at hb; simp at hb
  have hne' : ∀ j, (μ j : ℂ) ≠ (u : ℂ) := fun j => by exact_mod_cast ((hx j).trans_le hu).ne
  have hphi : (Edge_phi μ u : ℂ) = (u : ℂ) - Edge_S μ u := by
    rw [Edge_S_real]; unfold Edge_phi; push_cast; ring
  have hd := Edge_S_sub μ hne hne'
  set P := Edge_avc (fun j => ((μ j : ℂ) - w)⁻¹ * ((μ j : ℂ) - u)⁻¹)
  have e : w - Edge_S μ w - (Edge_phi μ u : ℂ) = (w - u) * (1 - P) := by
    rw [hphi]; linear_combination -hd
  have hP : P.re ≤ (Edge_F μ w + Edge_G μ u) / 2 := by
    rw [← Edge_F_real]
    calc P.re = Edge_av (fun j => (((μ j : ℂ) - w)⁻¹ * ((μ j : ℂ) - u)⁻¹).re) := Edge_avc_re _
      _ ≤ Edge_av (fun j => (1 / 2) * ‖((μ j : ℂ) - w)⁻¹‖ ^ 2 +
            (1 / 2) * ‖((μ j : ℂ) - (u : ℂ))⁻¹‖ ^ 2) := Edge_av_le fun j => by
          have := Complex.re_le_norm (((μ j : ℂ) - w)⁻¹ * ((μ j : ℂ) - u)⁻¹)
          rw [norm_mul] at this
          nlinarith [sq_nonneg (‖((μ j : ℂ) - w)⁻¹‖ - ‖((μ j : ℂ) - (u : ℂ))⁻¹‖)]
      _ = _ := by rw [Edge_av_add, Edge_av_mul, Edge_av_mul]; unfold Edge_F; ring
  have h1 : w.im ≤ ‖w - u‖ := by
    have := Complex.abs_im_le_norm (w - u)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith [le_abs_self w.im]
  have h2 : (1 - Edge_G μ u) / 2 ≤ ‖1 - P‖ := by
    have := Complex.re_le_norm (1 - P)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  rw [e, norm_mul]
  have h3 : 0 ≤ (1 - Edge_G μ u) / 2 := by linarith
  calc w.im * (1 - Edge_G μ u) / 2 = w.im * ((1 - Edge_G μ u) / 2) := by ring
    _ ≤ ‖w - u‖ * ‖1 - P‖ := mul_le_mul h1 h2 h3 (norm_nonneg _)

/-- `G(w₊ + δ) ≤ 1.44/(1.44 + δ²)` and `φ(w₊ + δ) - E⁺ ≤ 1.25 δ²` for `δ ≥ 0`. -/
private lemma Edge_out_bd {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10) (u : ℝ)
    (hu : Edge_wp μ ≤ u) :
    Edge_G μ u ≤ 36 / 25 / (36 / 25 + (u - Edge_wp μ) ^ 2) ∧
      Edge_phi μ u - Edge_ep μ ≤ 5 / 4 * (u - Edge_wp μ) ^ 2 := by
  obtain ⟨hx, hG, -, -⟩ := Edge_wp_spec hμ hℓ
  set δ := u - Edge_wp μ
  have hδ : 0 ≤ δ := by simp only [δ]; linarith
  constructor
  · have := (Edge_av_wt (w := fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹)
      (r := fun j => (Edge_wp μ - μ j) ^ 2 / (u - μ j) ^ 2) (p := 0)
      (q := 36 / 25 / (36 / 25 + δ ^ 2)) (fun j => inv_nonneg.2 (sq_nonneg _)) hG fun j => by
        have hb := Edge_x_bd hμ hℓ j
        have hp : 0 < Edge_wp μ - μ j := by linarith
        have hq : u - μ j = (Edge_wp μ - μ j) + δ := by simp only [δ]; ring
        constructor
        · positivity
        · rw [div_le_div_iff₀ (by rw [hq]; positivity) (by positivity), hq]
          have hx2 : (Edge_wp μ - μ j) ^ 2 ≤ 36 / 25 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg δ), mul_nonneg hp.le hδ]).2
    refine le_trans (le_of_eq ?_) this
    unfold Edge_G; congr 1; funext j
    have hp : Edge_wp μ - μ j ≠ 0 := by linarith [hx j]
    field_simp
  · rw [Edge_phi_id hμ hℓ u fun j => (hx j).trans_le hu]
    have := (Edge_av_wt (w := fun j => ((Edge_wp μ - μ j) ^ 2)⁻¹) (r := fun j => (u - μ j)⁻¹)
      (p := 0) (q := 5 / 4) (fun j => inv_nonneg.2 (sq_nonneg _)) hG fun j => by
        have hb := Edge_x_bd hμ hℓ j
        constructor
        · exact inv_nonneg.2 (by linarith)
        · rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith).2
    nlinarith [sq_nonneg δ]

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_s_sq {X η : ℝ} (hη : 0 ≤ η) :
    X ^ 2 + η ^ 2 ≤ (|X| + η) ^ 2 ∧ (|X| + η) ^ 2 ≤ 2 * (X ^ 2 + η ^ 2) := by
  have h0 := abs_nonneg X
  have h1 := sq_abs X
  constructor
  · nlinarith only [h0, h1, hη]
  · nlinarith only [h1, sq_nonneg (|X| - η)]

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_fin_in {a b X η K : ℝ} (hη : 0 ≤ η) (hK : 100 ≤ K)
    (h1 : a ^ 2 ≤ 2 * b ^ 2) (h3 : (47 / 100) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 ≤ X ^ 2 + η ^ 2)
    (h4 : X ^ 2 + η ^ 2 ≤ 6 * (a ^ 2 + b ^ 2) ^ 2) :
    K⁻¹ * (|X| + η) ≤ b ^ 2 ∧ b ^ 2 ≤ K * (|X| + η) := by
  obtain ⟨s1, s2⟩ := Edge_s_sq (X := X) hη
  have hsn : 0 ≤ |X| + η := by positivity
  have hb2 := sq_nonneg b
  have hs1 : |X| + η ≤ 11 * b ^ 2 := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    nlinarith only [s2, h4, h1, hb2]
  have hs3 : 47 / 100 * b ^ 2 ≤ |X| + η := by
    refine le_of_pow_le_pow_left₀ two_ne_zero hsn ?_
    have : (b ^ 2) ^ 2 ≤ (a ^ 2 + b ^ 2) ^ 2 := pow_le_pow_left₀ hb2 (by nlinarith only [sq_nonneg a]) 2
    nlinarith only [s1, h3, this]
  have hKi : K⁻¹ ≤ 1 / 100 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
  constructor
  · nlinarith only [hKi, hsn, hs1, inv_nonneg.2 (show (0 : ℝ) ≤ K by linarith)]
  · nlinarith only [hs3, hK, hsn]

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_fin_out {a b X η K : ℝ} (hb : 0 ≤ b) (hη : 0 < η) (hK : 100 ≤ K) (ha0 : 0 < a)
    (hb8 : b ^ 2 ≤ 8 * a ^ 2) (hY1 : 4 / 5 * a * b ≤ η) (hY2 : η ≤ 6 * a * b)
    (h3 : (47 / 100) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 ≤ X ^ 2 + η ^ 2)
    (h4 : X ^ 2 + η ^ 2 ≤ 6 * (a ^ 2 + b ^ 2) ^ 2) :
    K⁻¹ * η ^ 2 ≤ b ^ 2 * (|X| + η) ∧ b ^ 2 * (|X| + η) ≤ K * η ^ 2 := by
  obtain ⟨s1, s2⟩ := Edge_s_sq (X := X) hη.le
  have hsn : 0 ≤ |X| + η := by positivity
  have ha2 := sq_nonneg a
  have hs1 : |X| + η ≤ 32 * a ^ 2 := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    have : (a ^ 2 + b ^ 2) ^ 2 ≤ (9 * a ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith only [s2, h4, this]
  have hs3 : 47 / 100 * a ^ 2 ≤ |X| + η := by
    refine le_of_pow_le_pow_left₀ two_ne_zero hsn ?_
    have : (a ^ 2) ^ 2 ≤ (a ^ 2 + b ^ 2) ^ 2 := pow_le_pow_left₀ ha2 (by nlinarith only [sq_nonneg b]) 2
    nlinarith only [s1, h3, this]
  have hab : 0 ≤ a * b := mul_nonneg ha0.le hb
  have e1 : η ^ 2 ≤ (6 * a * b) ^ 2 := pow_le_pow_left₀ hη.le hY2 2
  have e2 : (4 / 5 * a * b) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hY1 2
  have hKi : K⁻¹ ≤ 1 / 100 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
  have hb2 := sq_nonneg b
  constructor
  · have : K⁻¹ * η ^ 2 ≤ 1 / 100 * η ^ 2 := mul_le_mul_of_nonneg_right hKi (sq_nonneg _)
    have : b ^ 2 * (47 / 100 * a ^ 2) ≤ b ^ 2 * (|X| + η) := mul_le_mul_of_nonneg_left hs3 hb2
    nlinarith only [this, e1, ‹K⁻¹ * η ^ 2 ≤ 1 / 100 * η ^ 2›]
  · have : b ^ 2 * (|X| + η) ≤ b ^ 2 * (32 * a ^ 2) := mul_le_mul_of_nonneg_left hs1 hb2
    have : 50 * η ^ 2 ≤ K * η ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith only [‹b ^ 2 * (|X| + η) ≤ b ^ 2 * (32 * a ^ 2)›, e2, this]

/-- Near `E⁺`: `Im(z + m)² ≍ |E⁺ - Re z| + Im z` inside and
`Im(z + m)² (|Re z - E⁺| + Im z) ≍ (Im z)²` outside. -/
private lemma Edge_right_near {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {R₀ : ℝ} (hR₀ : 3 ≤ R₀) {z c : ℂ} (hQ : Edge_Q μ ℓ z c) (hz : 0 ≤ z.im)
    (hnear : ‖z - (Edge_ep μ : ℂ)‖ ≤ 1 / 20000) :
    (z.re ≤ Edge_ep μ →
      (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3))⁻¹ * (|z.re - Edge_ep μ| + z.im) ≤ (z + c).im ^ 2 ∧
      (z + c).im ^ 2 ≤ 10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) * (|z.re - Edge_ep μ| + z.im)) ∧
    (Edge_ep μ < z.re → 0 < z.im →
      (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3))⁻¹ * z.im ^ 2 ≤
        (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ∧
      (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ≤
        10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) * z.im ^ 2) := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5⟩ := hQ
  have hl0 := Edge_l0 hμ
  have hep := Edge_ep_bd hμ hℓ
  have hepU : Edge_ep μ ≤ 43 / 20 := by nlinarith only [hep.2, hℓ, hl0]
  have hepL : 19 / 10 ≤ Edge_ep μ := by linarith only [hep.1, hℓ]
  have hK : 100 ≤ 10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) := by
    have : 16 ≤ (R₀ + 1) ^ 2 := by nlinarith only [hR₀]
    nlinarith only [this, hR₀]
  have hzw : z + c - Edge_S μ (z + c) = z := by rw [← hQ4]; ring
  have hXa : |z.re - Edge_ep μ| ≤ 1 / 20000 := by
    have := Complex.abs_re_le_norm (z - (Edge_ep μ : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this; linarith
  have hcre : -1 ≤ c.re := (abs_le.1 ((Complex.abs_re_le_norm c).trans hQ5)).1
  have hwre : 1 / 2 ≤ (z + c).re := by
    rw [Complex.add_re]; linarith [(abs_le.1 hXa).1]
  have hwn4 : ‖z + c‖ ≤ 4 := by
    have : ‖z‖ ≤ ‖z - (Edge_ep μ : ℂ)‖ + ‖(Edge_ep μ : ℂ)‖ := norm_le_norm_sub_add _ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < Edge_ep μ by linarith)]
      at this
    exact (norm_add_le _ _).trans (by linarith)
  have hd := Edge_d_small hμ hℓ (z + c) hwre hwn4
  rw [hzw] at hd
  have hd2 : ((z + c).re - Edge_wp μ) ^ 2 + (z + c).im ^ 2 ≤ 1 / 400 := by
    have : ‖z + c - (Edge_wp μ : ℂ)‖ ^ 2 = ((z + c).re - Edge_wp μ) ^ 2 + (z + c).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
      ring
    linarith
  have ha : |(z + c).re - Edge_wp μ| ≤ 1 / 20 := by
    have h : ((z + c).re - Edge_wp μ) ^ 2 ≤ (1 / 20) ^ 2 := by
      nlinarith only [hd2, sq_nonneg (z + c).im]
    have := sq_le_sq.1 h
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)] at this
  have hb2 : (z + c).im ^ 2 ≤ 1 / 400 := by
    nlinarith only [hd2, sq_nonneg ((z + c).re - Edge_wp μ)]
  have hb' : (z + c).im ≤ 1 / 20 := by nlinarith only [hb2, hQ1]
  obtain ⟨R, T, hR, hR', hT, hT', hre, him⟩ := Edge_near_core hμ hℓ (z + c) ha hQ1 hb'
  rw [hzw] at hre him
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at hre him
  obtain ⟨al1, al2, al3, al4⟩ := Edge_alg hQ1 ha hb' hR hR' hT hT' hre him
  constructor
  · intro hin
    exact Edge_fin_in hz hK (al1 (by linarith)) al3 al4
  · intro hout hηp
    obtain ⟨ha0, hb8, hY1, hY2⟩ := al2 (by linarith) hηp
    exact Edge_fin_out hQ1 hηp hK ha0 hb8 hY1 hY2 al3 al4

/-- Away from `E⁺`: the same bounds. -/
private lemma Edge_right_far {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {R₀ : ℝ} (hR₀ : 3 ≤ R₀) {z c : ℂ} (hQ : Edge_Q μ ℓ z c) (hz : 0 ≤ z.im)
    (hmid : (Edge_em μ + Edge_ep μ) / 2 ≤ z.re) (hzn : ‖z‖ ≤ R₀)
    (hfar : 1 / 20000 < ‖z - (Edge_ep μ : ℂ)‖) :
    (z.re ≤ Edge_ep μ →
      (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3))⁻¹ * (|z.re - Edge_ep μ| + z.im) ≤ (z + c).im ^ 2 ∧
      (z + c).im ^ 2 ≤ 10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) * (|z.re - Edge_ep μ| + z.im)) ∧
    (Edge_ep μ < z.re → 0 < z.im →
      (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3))⁻¹ * z.im ^ 2 ≤
        (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ∧
      (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ≤
        10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) * z.im ^ 2) := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5⟩ := hQ
  have hl0 := Edge_l0 hμ
  have hep := Edge_ep_bd hμ hℓ
  have hem := Edge_ep_bd (Edge_neg_bd hμ) hℓ
  have hepU : Edge_ep μ ≤ 43 / 20 := by nlinarith only [hep.2, hℓ, hl0]
  have hepL : 19 / 10 ≤ Edge_ep μ := by linarith only [hep.1, hℓ]
  have hemL : 19 / 10 ≤ Edge_ep (fun j => -μ j) := by linarith only [hem.1, hℓ]
  have hemd : Edge_em μ = -Edge_ep (fun j => -μ j) := rfl
  have hR1 : 4 ≤ R₀ + 1 := by linarith
  have hR2 : 16 ≤ (R₀ + 1) ^ 2 := by nlinarith only [hR1]
  have hzw : z + c - Edge_S μ (z + c) = z := by rw [← hQ4]; ring
  have hFn : 0 ≤ Edge_F μ (z + c) := by
    unfold Edge_F
    calc (0 : ℝ) = Edge_av (fun _ : ι => (0 : ℝ)) := (Edge_av_const _).symm
      _ ≤ _ := Edge_av_le fun j => sq_nonneg _
  have hbη : z.im ≤ (z + c).im := by
    have e1 : c.im = (z + c).im * Edge_F μ (z + c) := by
      conv_lhs => rw [hQ4]
      rw [Edge_S_im]
    have e2 : (z + c).im = z.im + c.im := Complex.add_im _ _
    have := mul_nonneg hQ1 hFn
    linarith
  have hzre : |z.re| ≤ R₀ := (Complex.abs_re_le_norm z).trans hzn
  have hzim : z.im ≤ R₀ := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzn)
  have hwn : ‖z + c‖ ≤ R₀ + 1 := (norm_add_le _ _).trans (by linarith)
  have hbR : (z + c).im ≤ R₀ + 1 :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm (z + c)).trans hwn)
  have hsR : |z.re - Edge_ep μ| + z.im ≤ 2 * R₀ + 3 := by
    have : |z.re - Edge_ep μ| ≤ R₀ + 43 / 20 :=
      abs_le.2 ⟨by linarith [(abs_le.1 hzre).1], by linarith [(abs_le.1 hzre).2]⟩
    linarith
  have hnz2 : ‖z - (Edge_ep μ : ℂ)‖ ^ 2 = (z.re - Edge_ep μ) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  have hnzs : ‖z - (Edge_ep μ : ℂ)‖ ≤ |z.re - Edge_ep μ| + z.im := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - (Edge_ep μ : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h
    rwa [abs_of_nonneg hz] at h
  have hsr : 1 / 20000 < |z.re - Edge_ep μ| + z.im := lt_of_lt_of_le hfar hnzs
  have hsn : 0 ≤ |z.re - Edge_ep μ| + z.im := by positivity
  have hf2 : (1 / 20000) ^ 2 < (z.re - Edge_ep μ) ^ 2 + z.im ^ 2 := by
    rw [← hnz2]; exact pow_lt_pow_left₀ hfar (by norm_num) (by norm_num)
  set K := 10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) with hK
  have hK0 : 0 < K := by positivity
  have hb0 := hQ1
  constructor
  · intro hin
    have hbl : 1 / 40000 ≤ (z + c).im := by
      by_contra hc; rw [not_le] at hc
      have hb2 : (z + c).im ^ 2 ≤ 1 / 100 := by nlinarith only [hc, hb0]
      have hb3 : (z + c).im ^ 2 ≤ (1 / 40000) ^ 2 := pow_le_pow_left₀ hb0 hc.le 2
      rcases le_or_gt (1 / 40000) (Edge_ep μ - z.re) with hX1 | hX1
      · have hw2 : (1 - ℓ) ^ 2 ≤ (z + c).re ^ 2 + (z + c).im ^ 2 := by
          have : ‖z + c‖ ^ 2 = (z + c).re ^ 2 + (z + c).im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          rw [← this]; exact pow_le_pow_left₀ (by linarith) hQ2 2
        have hl2 : 81 / 100 ≤ (1 - ℓ) ^ 2 := by nlinarith only [hℓ, hl0]
        rcases lt_or_gt_of_ne (show (z + c).re ≠ 0 by
            intro h0; rw [h0] at hw2; linarith) with hn | hp
        · have e1 : (-star (z + c)).im = (z + c).im := by simp [add_comm]
          have e2 : (-star (z + c)).re = -(z + c).re := by simp
          have h := Edge_far_in (Edge_neg_bd hμ) hℓ (-star (z + c)) (by rwa [norm_neg, norm_star])
            (by rw [e1]; exact hb2) (by rw [e2]; linarith)
          rw [show -star (z + c) - Edge_S (fun j => -μ j) (-star (z + c)) =
            -star (z + c - Edge_S μ (z + c)) by rw [Edge_S_neg, star_sub]; ring, hzw] at h
          simp only [Complex.neg_re, Complex.star_def, Complex.conj_re, Complex.neg_im,
            Complex.conj_im, neg_neg] at h
          rw [hemd] at hmid
          linarith
        · have h := Edge_far_in hμ hℓ (z + c) hQ2 hb2 hp
          rw [hzw] at h
          linarith
      · have hX2 : (z.re - Edge_ep μ) ^ 2 ≤ (1 / 40000) ^ 2 := by
          have : 0 ≤ Edge_ep μ - z.re := by linarith
          nlinarith only [this, hX1]
        have hη2 : (1 / 40000) ^ 2 < z.im ^ 2 := by linarith
        have : 1 / 40000 < z.im := by
          by_contra h5; rw [not_lt] at h5
          have := pow_le_pow_left₀ hz h5 2; linarith
        linarith
    constructor
    · calc K⁻¹ * (|z.re - Edge_ep μ| + z.im) ≤ K⁻¹ * (2 * R₀ + 3) :=
            mul_le_mul_of_nonneg_left hsR (inv_nonneg.2 hK0.le)
        _ ≤ (1 / 40000) ^ 2 := by
            rw [inv_mul_le_iff₀ hK0, hK]
            nlinarith only [hR2, hR₀]
        _ ≤ (z + c).im ^ 2 := pow_le_pow_left₀ (by norm_num) hbl 2
    · calc (z + c).im ^ 2 ≤ (R₀ + 1) ^ 2 := pow_le_pow_left₀ hb0 hbR 2
        _ ≤ K * (1 / 20000) := by rw [hK]; nlinarith only [hR2, hR₀]
        _ ≤ K * (|z.re - Edge_ep μ| + z.im) := mul_le_mul_of_nonneg_left hsr.le hK0.le
  · intro hout hηp
    constructor
    · calc K⁻¹ * z.im ^ 2 ≤ (1 / 20000) * z.im ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            rw [inv_le_comm₀ hK0 (by norm_num), hK]; norm_num
            nlinarith only [hR2, hR₀]
        _ ≤ (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) := by
            have : z.im ^ 2 ≤ (z + c).im ^ 2 := pow_le_pow_left₀ hz hbη 2
            nlinarith only [this, hsr, sq_nonneg z.im]
    · rcases le_or_gt (1 / 40000) z.im with hη1 | hη1
      · calc (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ≤ (R₀ + 1) ^ 2 * (2 * R₀ + 3) :=
              mul_le_mul (pow_le_pow_left₀ hb0 hbR 2) hsR hsn (by positivity)
          _ ≤ K * (1 / 40000) ^ 2 := by rw [hK]; nlinarith only [hR2, hR₀]
          _ ≤ K * z.im ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hη1 2) hK0.le
      · have hXp : 0 < z.re - Edge_ep μ := by linarith
        have hη2 : z.im ^ 2 ≤ (1 / 40000) ^ 2 := pow_le_pow_left₀ hz hη1.le 2
        have hX2 : 1 / 40000 < z.re - Edge_ep μ := by
          by_contra h5; rw [not_lt] at h5
          have := pow_le_pow_left₀ hXp.le h5 2; linarith
        obtain ⟨u, hu, hphi⟩ := Edge_root hμ hℓ z.re (by linarith)
        obtain ⟨hG, hph⟩ := Edge_out_bd hμ hℓ u hu
        have hδ : 1 / 50000 ≤ (u - Edge_wp μ) ^ 2 := by
          rw [hphi] at hph; linarith
        have hG2 : 1 / 100000 ≤ 1 - Edge_G μ u := by
          have h1 : 0 < 36 / 25 + (u - Edge_wp μ) ^ 2 := by positivity
          have : 36 / 25 / (36 / 25 + (u - Edge_wp μ) ^ 2) ≤ 1 - 1 / 100000 := by
            rw [div_le_iff₀ h1]; nlinarith only [hδ]
          linarith
        have hc := Edge_cmp hμ hℓ (z + c) (by linarith) hQ3 u hu
        rw [hzw, hphi] at hc
        have hη3 : ‖z - (z.re : ℂ)‖ = z.im := by
          have : z - (z.re : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
            apply Complex.ext <;> simp
          rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_nonneg hz]
        rw [hη3] at hc
        have hbb : (z + c).im ≤ 200000 * z.im := by
          nlinarith only [hc, hG2, hb0]
        calc (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ≤ (200000 * z.im) ^ 2 * (2 * R₀ + 3) :=
              mul_le_mul (pow_le_pow_left₀ hb0 hbb 2) hsR hsn (by positivity)
          _ ≤ K * z.im ^ 2 := by
              have h1 : (0 : ℝ) ≤ 2 * R₀ + 3 := by linarith
              have h2 : (0 : ℝ) ≤ (R₀ + 1) ^ 2 - 16 := by linarith
              have h3 := mul_nonneg (mul_nonneg (sq_nonneg z.im) h1) h2
              have h4 := mul_nonneg (sq_nonneg z.im) h1
              rw [hK]; nlinarith only [h3, h4]

/-- `Im(z + m)² ≍ |E⁺ - Re z| + Im z` inside and `Im(z + m)² (|Re z - E⁺| + Im z) ≍ (Im z)²` outside,
on the right half `Re z ≥ (E⁻ + E⁺)/2`, `|z| ≤ R₀`. -/
private lemma Edge_right {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {R₀ : ℝ} (hR₀ : 3 ≤ R₀) {z c : ℂ} (hQ : Edge_Q μ ℓ z c) (hz : 0 ≤ z.im)
    (hmid : (Edge_em μ + Edge_ep μ) / 2 ≤ z.re) (hzn : ‖z‖ ≤ R₀) :
    (z.re ≤ Edge_ep μ →
      (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3))⁻¹ * (|z.re - Edge_ep μ| + z.im) ≤ (z + c).im ^ 2 ∧
      (z + c).im ^ 2 ≤ 10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) * (|z.re - Edge_ep μ| + z.im)) ∧
    (Edge_ep μ < z.re → 0 < z.im →
      (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3))⁻¹ * z.im ^ 2 ≤
        (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ∧
      (z + c).im ^ 2 * (|z.re - Edge_ep μ| + z.im) ≤
        10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) * z.im ^ 2) := by
  rcases le_or_gt ‖z - (Edge_ep μ : ℂ)‖ (1 / 20000) with hnear | hfar
  · exact Edge_right_near hμ hℓ hR₀ hQ hz hnear
  · exact Edge_right_far hμ hℓ hR₀ hQ hz hmid hzn hfar

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_conv_in {y b F F₀ K s : ℝ} (hb : 0 ≤ b) (hy : y = b * F) (hF₀ : 0 < F₀)
    (hF1 : F₀ ≤ F) (hF2 : F ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : K⁻¹ * s ≤ b ^ 2)
    (h2 : b ^ 2 ≤ K * s) :
    10 * ((10 * K / F₀)⁻¹ * Real.sqrt s) ≤ y ∧ y ≤ 10 * K / F₀ * Real.sqrt s := by
  have hC : 0 < 10 * K / F₀ := by positivity
  have hy0 : 0 ≤ y := by rw [hy]; exact mul_nonneg hb (hF₀.le.trans hF1)
  have hCF : (10 * K / F₀) ^ 2 * F₀ ^ 2 = 100 * K ^ 2 := by field_simp; ring
  have hF2' : F₀ ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hF₀.le hF1 2
  have hF3 : F ^ 2 ≤ 1 := by nlinarith only [hF2, hF₀, hF1]
  have hKs : s ≤ K * (K * (K⁻¹ * s)) := by
    rw [← mul_assoc K K⁻¹, mul_inv_cancel₀ (by linarith), one_mul]; nlinarith only [hK, hs]
  constructor
  · have hsq : Real.sqrt s ≤ 10 * K / F₀ * y / 10 := by
      rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, hy, mul_pow]
      have : (10 * K / F₀) ^ 2 * (b ^ 2 * F ^ 2) ≥ (10 * K / F₀) ^ 2 * (K⁻¹ * s * F₀ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 hF2' (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      have e : (10 * K / F₀) ^ 2 * (K⁻¹ * s * F₀ ^ 2) = 100 * (K * (K * (K⁻¹ * s))) := by
        rw [show (10 * K / F₀) ^ 2 * (K⁻¹ * s * F₀ ^ 2) = (10 * K / F₀) ^ 2 * F₀ ^ 2 * (K⁻¹ * s) by
          ring, hCF]; ring
      rw [le_div_iff₀ (by norm_num)]
      nlinarith only [this, e, hKs, hs]
    calc 10 * ((10 * K / F₀)⁻¹ * Real.sqrt s) = (10 * K / F₀)⁻¹ * (10 * Real.sqrt s) := by ring
      _ ≤ (10 * K / F₀)⁻¹ * (10 * K / F₀ * y) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hC.le)
      _ = y := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  · rw [show 10 * K / F₀ * Real.sqrt s = Real.sqrt ((10 * K / F₀) ^ 2 * s) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC.le], Real.le_sqrt hy0 (by positivity), hy,
      mul_pow]
    have hC2 : K ≤ (10 * K / F₀) ^ 2 := by
      have : (10 * K / F₀) ^ 2 * F₀ ^ 2 ≤ (10 * K / F₀) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hF₀, hF1, hF2]) (sq_nonneg _)
      nlinarith only [this, hCF, hK]
    calc b ^ 2 * F ^ 2 ≤ b ^ 2 * 1 := mul_le_mul_of_nonneg_left hF3 (sq_nonneg _)
      _ ≤ K * s := by linarith
      _ ≤ (10 * K / F₀) ^ 2 * s := mul_le_mul_of_nonneg_right hC2 hs

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_conv_out {y b F F₀ K s η : ℝ} (hb : 0 ≤ b) (hy : y = b * F) (hF₀ : 0 < F₀)
    (hF1 : F₀ ≤ F) (hF2 : F ≤ 1) (hK : 1 ≤ K) (hs : 0 < s) (hη : 0 < η)
    (h1 : K⁻¹ * η ^ 2 ≤ b ^ 2 * s) (h2 : b ^ 2 * s ≤ K * η ^ 2) :
    (10 * K / F₀)⁻¹ * (η / Real.sqrt s) ≤ y ∧ y ≤ 10 * K / F₀ * (η / Real.sqrt s) := by
  have hC : 0 < 10 * K / F₀ := by positivity
  have hy0 : 0 ≤ y := by rw [hy]; exact mul_nonneg hb (hF₀.le.trans hF1)
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hts : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hCF : (10 * K / F₀) ^ 2 * F₀ ^ 2 = 100 * K ^ 2 := by field_simp; ring
  have hF2' : F₀ ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hF₀.le hF1 2
  have hF3 : F ^ 2 ≤ 1 := by nlinarith only [hF2, hF₀, hF1]
  have hKη : η ^ 2 ≤ K * (K * (K⁻¹ * η ^ 2)) := by
    rw [← mul_assoc K K⁻¹, mul_inv_cancel₀ (by linarith), one_mul]; nlinarith only [hK, sq_nonneg η]
  constructor
  · rw [inv_mul_le_iff₀ hC, div_le_iff₀ ht]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, mul_pow, hts, hy, mul_pow]
    have : (10 * K / F₀) ^ 2 * (b ^ 2 * F ^ 2) * s ≥ (10 * K / F₀) ^ 2 * F₀ ^ 2 * (K⁻¹ * η ^ 2) := by
      have := mul_le_mul h1 hF2' (sq_nonneg _) (by positivity)
      nlinarith only [this, sq_nonneg (10 * K / F₀)]
    rw [hCF] at this
    nlinarith only [this, hKη]
  · rw [mul_div_assoc', le_div_iff₀ ht]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, mul_pow, hts, hy, mul_pow]
    have hC2 : K ≤ (10 * K / F₀) ^ 2 := by
      have : (10 * K / F₀) ^ 2 * F₀ ^ 2 ≤ (10 * K / F₀) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hF₀, hF1, hF2]) (sq_nonneg _)
      nlinarith only [this, hCF, hK]
    calc b ^ 2 * F ^ 2 * s ≤ b ^ 2 * s := by
          nlinarith only [mul_le_mul_of_nonneg_left hF3 (mul_nonneg (sq_nonneg b) hs.le)]
      _ ≤ K * η ^ 2 := h2
      _ ≤ (10 * K / F₀) ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_conv_rho {y b F F₀ K s q : ℝ} (hb : 0 ≤ b) (hy : y = b * F) (hF₀ : 0 < F₀)
    (hF1 : F₀ ≤ F) (hF2 : F ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : K⁻¹ * s ≤ b ^ 2)
    (h2 : b ^ 2 ≤ K * s) (hq : 9 / 5 ≤ q) (hq' : q ≤ 9 / 2) :
    (10 * K / F₀)⁻¹ * Real.sqrt (s * q) ≤ y / Real.pi ∧
      y / Real.pi ≤ 10 * K / F₀ * Real.sqrt (s * q) := by
  obtain ⟨c1, c2⟩ := Edge_conv_in hb hy hF₀ hF1 hF2 hK hs h1 h2
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_le_four
  have hC : 0 < 10 * K / F₀ := by positivity
  have hsq : Real.sqrt (s * q) = Real.sqrt s * Real.sqrt q := Real.sqrt_mul hs q
  have hq1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hq2 : Real.sqrt q ≤ 9 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hs0 := Real.sqrt_nonneg s
  have h0 : 0 ≤ (10 * K / F₀)⁻¹ * Real.sqrt s := by positivity
  constructor
  · rw [hsq, le_div_iff₀ (by linarith)]
    have : Real.sqrt q * Real.pi ≤ 9 := by nlinarith only [hq2, hπ4, hq1, hπ]
    calc (10 * K / F₀)⁻¹ * (Real.sqrt s * Real.sqrt q) * Real.pi =
        ((10 * K / F₀)⁻¹ * Real.sqrt s) * (Real.sqrt q * Real.pi) := by ring
      _ ≤ ((10 * K / F₀)⁻¹ * Real.sqrt s) * 9 := mul_le_mul_of_nonneg_left this h0
      _ ≤ y := by linarith
  · rw [hsq, div_le_iff₀ (by linarith)]
    have hy0 : 0 ≤ y := le_trans (by positivity) c1
    calc y ≤ 10 * K / F₀ * Real.sqrt s := c2
      _ ≤ 10 * K / F₀ * (Real.sqrt s * Real.sqrt q) * Real.pi := by
          have : 0 ≤ 10 * K / F₀ * Real.sqrt s := by positivity
          nlinarith only [this, hq1, hπ, mul_nonneg this (by linarith : (0 : ℝ) ≤ Real.sqrt q - 1)]

/-- The constant of (A.1) [square_root_density] for `|z| ≤ R₀`. -/
private def Edge_C (R₀ : ℝ) : ℝ := 10 * (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3)) / ((R₀ + 2) ^ 2)⁻¹

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_C_pos {R₀ : ℝ} (hR₀ : 3 ≤ R₀) : 0 < Edge_C R₀ := by
  unfold Edge_C
  have : 0 < R₀ + 1 := by linarith
  have : 0 < 2 * R₀ + 3 := by linarith
  have : 0 < R₀ + 2 := by linarith
  positivity

omit [Nonempty ι] in
private lemma Edge_em_neg (μ : ι → ℝ) : Edge_em (fun j => -μ j) = -Edge_ep μ := by
  unfold Edge_em
  rw [show (fun j => -(fun j => -μ j) j) = μ from funext fun j => neg_neg _]

/-- (A.1) [square_root_density] on the right half `Re z ≥ (E⁻ + E⁺)/2`. -/
private lemma Edge_half {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {R₀ : ℝ} (hR₀ : 3 ≤ R₀) {z c : ℂ} (hQ : Edge_Q μ ℓ z c) (hz : 0 ≤ z.im)
    (hmid : (Edge_em μ + Edge_ep μ) / 2 ≤ z.re) (hzn : ‖z‖ ≤ R₀) :
    (z.re ≤ Edge_ep μ →
      (Edge_C R₀)⁻¹ * Real.sqrt (|z.re - Edge_ep μ| + z.im) ≤ c.im ∧
        c.im ≤ Edge_C R₀ * Real.sqrt (|z.re - Edge_ep μ| + z.im)) ∧
    (Edge_ep μ < z.re → 0 < z.im →
      (Edge_C R₀)⁻¹ * (z.im / Real.sqrt (|z.re - Edge_ep μ| + z.im)) ≤ c.im ∧
        c.im ≤ Edge_C R₀ * (z.im / Real.sqrt (|z.re - Edge_ep μ| + z.im))) ∧
    (z.im = 0 → z.re ≤ Edge_ep μ →
      (Edge_C R₀)⁻¹ * Real.sqrt ((Edge_ep μ - z.re) * (z.re - Edge_em μ)) ≤ c.im / Real.pi ∧
        c.im / Real.pi ≤ Edge_C R₀ * Real.sqrt ((Edge_ep μ - z.re) * (z.re - Edge_em μ))) := by
  obtain ⟨r1, r2⟩ := Edge_right hμ hℓ hR₀ hQ hz hmid hzn
  obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5⟩ := hQ
  have hl0 := Edge_l0 hμ
  have hF : c.im = (z + c).im * Edge_F μ (z + c) := by
    conv_lhs => rw [hQ4]
    rw [Edge_S_im]
  have hR2 : 0 < R₀ + 2 := by linarith
  have hF₀ : 0 < ((R₀ + 2) ^ 2)⁻¹ := by positivity
  have hwn : ‖z + c‖ ≤ R₀ + 1 := (norm_add_le _ _).trans (by linarith)
  have hF1 : ((R₀ + 2) ^ 2)⁻¹ ≤ Edge_F μ (z + c) := by
    unfold Edge_F
    calc ((R₀ + 2) ^ 2)⁻¹ = Edge_av (fun _ : ι => ((R₀ + 2) ^ 2)⁻¹) := (Edge_av_const _).symm
      _ ≤ _ := Edge_av_le fun j => by
        rw [norm_inv, inv_pow]
        have h1 : ‖(μ j : ℂ) - (z + c)‖ ≤ R₀ + 2 := by
          refine (norm_sub_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hμ j]
        have h2 : 0 < ‖(μ j : ℂ) - (z + c)‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          exact Edge_ne_of_norm hμ hℓ hQ2 j
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le h1 2)
  have hK : 1 ≤ 10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3) := by
    have : 1 ≤ (R₀ + 1) ^ 2 := by nlinarith only [hR₀]
    nlinarith only [this, hR₀]
  have hC : Edge_C R₀ = 10 * (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3)) / ((R₀ + 2) ^ 2)⁻¹ := rfl
  refine ⟨fun hin => ?_, fun hout hηp => ?_, fun h0 hin => ?_⟩
  · have hs : 0 ≤ |z.re - Edge_ep μ| + z.im := by positivity
    obtain ⟨k1, k2⟩ := r1 hin
    obtain ⟨c1, c2⟩ := Edge_conv_in hQ1 hF hF₀ hF1 hQ3 hK hs k1 k2
    rw [hC]
    refine ⟨le_trans ?_ c1, c2⟩
    have : 0 ≤ (10 * (10 ^ 11 * (R₀ + 1) ^ 2 * (2 * R₀ + 3)) / ((R₀ + 2) ^ 2)⁻¹)⁻¹ *
        Real.sqrt (|z.re - Edge_ep μ| + z.im) := by positivity
    linarith
  · have hs : 0 < |z.re - Edge_ep μ| + z.im := by positivity
    obtain ⟨k1, k2⟩ := r2 hout hηp
    rw [hC]
    exact Edge_conv_out hQ1 hF hF₀ hF1 hQ3 hK hs hηp k1 k2
  · have hep := Edge_ep_bd hμ hℓ
    have hem := Edge_ep_bd (Edge_neg_bd hμ) hℓ
    have hemd : Edge_em μ = -Edge_ep (fun j => -μ j) := rfl
    have hs0 : |z.re - Edge_ep μ| + z.im = Edge_ep μ - z.re := by
      rw [h0, add_zero, abs_of_nonpos (by linarith)]; ring
    have hs : 0 ≤ Edge_ep μ - z.re := by linarith
    obtain ⟨k1, k2⟩ := r1 hin
    rw [hs0] at k1 k2
    have hq : 9 / 5 ≤ z.re - Edge_em μ := by nlinarith only [hmid, hep.1, hem.1, hemd, hℓ]
    have hq' : z.re - Edge_em μ ≤ 9 / 2 := by nlinarith only [hin, hep.2, hem.2, hemd, hℓ, hl0]
    rw [hC]
    exact Edge_conv_rho hQ1 hF hF₀ hF1 hQ3 hK hs k1 k2 hq hq'

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_kappa_right {ep em x : ℝ} (h : em < ep) (hx : (em + ep) / 2 ≤ x) :
    min |ep - x| |x - em| = |x - ep| := by
  rw [abs_sub_comm x ep]
  apply min_eq_left
  rcases le_or_gt x ep with h1 | h1
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith

omit [Fintype ι] [Nonempty ι] in
private lemma Edge_kappa_left {ep em x : ℝ} (h : em < ep) (hx : x ≤ (em + ep) / 2) :
    min |ep - x| |x - em| = |-x - -em| := by
  rw [show -x - -em = -(x - em) by ring, abs_neg]
  apply min_eq_right
  rcases le_or_gt em x with h1 | h1
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith

/-- (A.1) [square_root_density] in scalar form. -/
private lemma Edge_full {μ : ι → ℝ} {ℓ : ℝ} (hμ : ∀ j, |μ j| ≤ ℓ) (hℓ : ℓ ≤ 1 / 10)
    {R₀ : ℝ} (hR₀ : 3 ≤ R₀) {m : ℂ → ℂ} (hm : Edge_Hm μ ℓ m) :
    (∀ x ∈ Set.Icc (Edge_em μ) (Edge_ep μ),
      (Edge_C R₀)⁻¹ * Real.sqrt ((Edge_ep μ - x) * (x - Edge_em μ)) ≤ Edge_rho m x ∧
        Edge_rho m x ≤ Edge_C R₀ * Real.sqrt ((Edge_ep μ - x) * (x - Edge_em μ))) ∧
    ∀ z : ℂ, ‖z‖ ≤ R₀ → 0 < z.im →
      (z.re ∈ Set.Icc (Edge_em μ) (Edge_ep μ) →
        (Edge_C R₀)⁻¹ * Real.sqrt (min |Edge_ep μ - z.re| |z.re - Edge_em μ| + z.im) ≤ (m z).im ∧
          (m z).im ≤ Edge_C R₀ * Real.sqrt (min |Edge_ep μ - z.re| |z.re - Edge_em μ| + z.im)) ∧
      (z.re ∉ Set.Icc (Edge_em μ) (Edge_ep μ) →
        (Edge_C R₀)⁻¹ * (z.im / Real.sqrt (min |Edge_ep μ - z.re| |z.re - Edge_em μ| + z.im)) ≤
            (m z).im ∧
          (m z).im ≤ Edge_C R₀ *
            (z.im / Real.sqrt (min |Edge_ep μ - z.re| |z.re - Edge_em μ| + z.im))) := by
  have hlt := Edge_em_lt hμ hℓ
  have hμ' := Edge_neg_bd hμ
  have hm' := Edge_Hm_neg hm
  have hep' : Edge_ep (fun j => -μ j) = -Edge_em μ := by unfold Edge_em; ring
  have hem' := Edge_em_neg μ
  have hmid' : ∀ x : ℝ, x ≤ (Edge_em μ + Edge_ep μ) / 2 →
      (Edge_em (fun j => -μ j) + Edge_ep (fun j => -μ j)) / 2 ≤ -x := fun x hx => by
    rw [hep', hem']; linarith
  refine ⟨fun x hx => ?_, fun z hzn hz => ?_⟩
  · rw [Edge_rho_eq hμ hℓ hm]
    have hQ := Edge_mext_Q hμ hℓ hm (x : ℂ) (by simp)
    rcases le_total ((Edge_em μ + Edge_ep μ) / 2) x with hr | hl
    · have := (Edge_half hμ hℓ hR₀ hQ (by simp) (by simpa using hr)
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;>
          nlinarith [hx.1, hx.2, (Edge_ep_bd hμ hℓ).2, (Edge_ep_bd hμ' hℓ).2,
            (Edge_ep_bd hμ hℓ).1, (Edge_ep_bd hμ' hℓ).1, Edge_l0 hμ, show Edge_em μ =
              -Edge_ep (fun j => -μ j) from rfl])).2.2 (by simp) (by simpa using hx.2)
      simpa using this
    · have hQ' := (Edge_Q_neg μ ℓ _ _).2 hQ
      have hzr : (-star (x : ℂ)).re = -x := by simp
      have := (Edge_half hμ' hℓ hR₀ hQ' (by simp) (by rw [hzr]; exact hmid' x hl)
        (by rw [norm_neg, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;>
          nlinarith [hx.1, hx.2, (Edge_ep_bd hμ hℓ).2, (Edge_ep_bd hμ' hℓ).2,
            (Edge_ep_bd hμ hℓ).1, (Edge_ep_bd hμ' hℓ).1, Edge_l0 hμ, show Edge_em μ =
              -Edge_ep (fun j => -μ j) from rfl])).2.2 (by simp)
          (by rw [hzr, hep']; linarith [hx.1])
      rw [hzr, hep', hem'] at this
      have e : (-Edge_em μ - -x) * (-x - -Edge_ep μ) = (Edge_ep μ - x) * (x - Edge_em μ) := by ring
      rw [e] at this
      simpa using this
  · have hQ := Edge_Hm_Q hm hz
    rcases le_total ((Edge_em μ + Edge_ep μ) / 2) z.re with hr | hl
    · have H := Edge_half hμ hℓ hR₀ hQ hz.le hr hzn
      rw [Edge_kappa_right hlt hr]
      refine ⟨fun hin => H.1 hin.2, fun hout => H.2.1 ?_ hz⟩
      by_contra hc; rw [not_lt] at hc
      exact hout ⟨by linarith, hc⟩
    · have hQ' := (Edge_Q_neg μ ℓ _ _).2 hQ
      have hzr : (-star z).re = -z.re := by simp
      have hzi : (-star z).im = z.im := by simp
      have hci : (-star (m z)).im = (m z).im := by simp
      have H := Edge_half hμ' hℓ hR₀ hQ' (by rw [hzi]; exact hz.le) (by rw [hzr]; exact hmid' _ hl)
        (by rwa [norm_neg, norm_star])
      rw [hzr, hzi, hci, hep'] at H
      rw [Edge_kappa_left hlt hl]
      refine ⟨fun hin => H.1 (by linarith [hin.1]), fun hout => H.2.1 ?_ hz⟩
      by_contra hc; rw [not_lt] at hc
      exact hout ⟨by linarith, by linarith⟩

end Scalar

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def Edge_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma Edge_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Edge_cd U d * Edge_cd U e = Edge_cd U (fun j => d j * e j) := by
  rw [Edge_cd, Edge_cd, Edge_cd, ← map_mul, diagonal_mul_diagonal]

private lemma Edge_cd_one (U : Matrix.unitaryGroup ι ℂ) : Edge_cd U (fun _ => 1) = 1 := by
  rw [Edge_cd, diagonal_one, map_one]

private lemma Edge_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • Edge_cd U d = Edge_cd U (fun j => c * d j) := by
  rw [Edge_cd, Edge_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma Edge_cd_sub (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Edge_cd U d - Edge_cd U e = Edge_cd U (fun j => d j - e j) := by
  rw [Edge_cd, Edge_cd, Edge_cd, ← map_sub, diagonal_sub]

private lemma Edge_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    Edge_cd U d - c • (1 : Matrix ι ι ℂ) = Edge_cd U (fun j => d j - c) := by
  rw [← Edge_cd_one U, Edge_cd_smul, Edge_cd_sub]
  simp

private lemma Edge_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (Edge_cd U d) = Edge_avc d := by
  rw [ntr, Edge_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]
  rfl

private lemma Edge_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (Edge_cd U d)⁻¹ = Edge_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [Edge_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact Edge_cd_one U

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma Edge_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
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
private lemma Edge_decomp {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ),
      Λ = Edge_cd U (fun j => (μ j : ℂ)) ∧ ∀ j, |μ j| ≤ opNorm Λ :=
  ⟨_, _, hΛ.spectral_theorem, Edge_eig_le hΛ⟩

private lemma Edge_res (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {ζ : ℂ}
    (h : ∀ j, (μ j : ℂ) ≠ ζ) :
    (Edge_cd U (fun j => (μ j : ℂ)) - ζ • (1 : Matrix ι ι ℂ))⁻¹ =
      Edge_cd U (fun j => ((μ j : ℂ) - ζ)⁻¹) := by
  rw [Edge_cd_sub_smul_one, Edge_cd_inv _ _ fun j => sub_ne_zero.2 (h j)]

private lemma Edge_ntr_res (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {ζ : ℂ}
    (h : ∀ j, (μ j : ℂ) ≠ ζ) :
    ntr (Edge_cd U (fun j => (μ j : ℂ)) - ζ • (1 : Matrix ι ι ℂ))⁻¹ = Edge_S μ ζ := by
  rw [Edge_res U μ h, Edge_ntr_cd]; rfl

private lemma Edge_res_mul (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {ζ : ℂ}
    (h : ∀ j, (μ j : ℂ) ≠ ζ) :
    (Edge_cd U (fun j => (μ j : ℂ)) - ζ • (1 : Matrix ι ι ℂ)) *
      (Edge_cd U (fun j => (μ j : ℂ)) - ζ • (1 : Matrix ι ι ℂ))⁻¹ = 1 := by
  rw [Edge_res U μ h, Edge_cd_sub_smul_one, Edge_cd_mul]
  simp only [mul_inv_cancel₀ (sub_ne_zero.2 (h _))]
  exact Edge_cd_one U

omit [Fintype ι] [DecidableEq ι] in
private lemma Edge_ne_of_im {μ : ι → ℝ} {ζ : ℂ} (h : 0 < ζ.im) : ∀ j, (μ j : ℂ) ≠ ζ :=
  fun j e => by rw [← e, Complex.ofReal_im] at h; exact lt_irrefl _ h

/-- `mSol Λ` satisfies the scalar form of (2.16) [self_m] and the a priori bounds. -/
private lemma Edge_Hm_mSol [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ)
    (hΛ : (Edge_cd U (fun j => (μ j : ℂ))).IsHermitian)
    (hℓ : opNorm (Edge_cd U (fun j => (μ j : ℂ))) ≤ 1 / 10) :
    Edge_Hm μ (opNorm (Edge_cd U (fun j => (μ j : ℂ)))) (mSol (Edge_cd U (fun j => (μ j : ℂ)))) := by
  intro z hz
  obtain ⟨h1, h2, -⟩ := mSol_spec _ hΛ z hz
  obtain ⟨h4, h3, -⟩ := mSol_apriori _ hΛ hℓ z hz
  refine ⟨h1, ?_, h3, h4⟩
  have e : ntr (MSol (Edge_cd U (fun j => (μ j : ℂ))) z) =
      Edge_S μ (z + mSol (Edge_cd U (fun j => (μ j : ℂ))) z) := by
    rw [MSol, Edge_ntr_res U μ (Edge_ne_of_im (by simp; linarith))]
  rw [e] at h2; exact h2

/-- `E^±` of `Λ = U diag(μ) U^*` are the scalar edges `φ(w_±)`. -/
private lemma Edge_E_eq [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ)
    (hΛ : (Edge_cd U (fun j => (μ j : ℂ))).IsHermitian)
    (hℓ : opNorm (Edge_cd U (fun j => (μ j : ℂ))) ≤ 1 / 10)
    (hμ : ∀ j, |μ j| ≤ opNorm (Edge_cd U (fun j => (μ j : ℂ)))) :
    Eplus (Edge_cd U (fun j => (μ j : ℂ))) = Edge_ep μ ∧
      Eminus (Edge_cd U (fun j => (μ j : ℂ))) = Edge_em μ :=
  Edge_Ep_eq hμ hℓ (Edge_Hm_mSol U μ hΛ hℓ)

end Mat

/-- Boundary values of Definition 2.7 [defn_Mm] used in (A.4) [equation_E_in_spectrum] and
(A.32) [derivative_of_edge]: for `‖Λ‖ ≤ 1/10`, `mExt Λ` is continuous on `Im z ≥ 0`, and at every
real `E` it solves (2.16) [self_m] with a genuine inverse and `|E + m(E)| ≥ 1 - ‖Λ‖`. -/
theorem mExt_boundary {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    ContinuousOn (mExt Λ) {z : ℂ | 0 ≤ z.im} ∧
      ∀ E : ℝ, 1 - opNorm Λ ≤ ‖(E : ℂ) + mExt Λ E‖ ∧ mExt Λ E = ntr (MExt Λ E) ∧
        (Λ - ((E : ℂ) + mExt Λ E) • (1 : Matrix ι ι ℂ)) * MExt Λ E = 1 := by
  obtain ⟨U, μ, rfl, hμ⟩ := Edge_decomp hΛ
  have hm := Edge_Hm_mSol U μ hΛ hℓ
  have hE : mExt (Edge_cd U fun j => (μ j : ℂ)) = Edge_mext (mSol (Edge_cd U fun j => (μ j : ℂ))) :=
    rfl
  refine ⟨hE ▸ Edge_mext_cont hμ hℓ hm, fun E => ?_⟩
  rw [MExt, hE]
  obtain ⟨-, h2, -, h4, -⟩ := Edge_mext_Q hμ hℓ hm (E : ℂ) (by simp)
  have hne := Edge_ne_of_norm hμ hℓ h2
  exact ⟨h2, by rw [Edge_ntr_res U μ hne]; exact h4, Edge_res_mul U μ hne⟩

/-- The support of `ρ_N` is the single interval `[E⁻, E⁺]` (§2.2, after (2.19)
[eq:density_rhoN]): `ρ_N > 0` exactly on `(E⁻, E⁺)`. -/
theorem rho_support {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Eminus Λ < Eplus Λ ∧ Function.support (rho Λ) = Set.Ioo (Eminus Λ) (Eplus Λ) := by
  obtain ⟨U, μ, rfl, hμ⟩ := Edge_decomp hΛ
  obtain ⟨h1, h2⟩ := Edge_E_eq U μ hΛ hℓ hμ
  rw [h1, h2]
  exact ⟨Edge_em_lt hμ hℓ, Edge_support hμ hℓ (Edge_Hm_mSol U μ hΛ hℓ)⟩

/-- (2.6) [eq:def_gamma]: the two limits exist and define `γ_± ∈ [1/2, 2]`. -/
theorem def_gamma_limits {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Tendsto (fun E => rho Λ E / Real.sqrt (Eplus Λ - E)) (𝓝[<] (Eplus Λ))
        (𝓝 (gammaPlus Λ ^ (3 / 2 : ℝ) / Real.pi)) ∧
      Tendsto (fun E => rho Λ E / Real.sqrt (E - Eminus Λ)) (𝓝[>] (Eminus Λ))
        (𝓝 (gammaMinus Λ ^ (3 / 2 : ℝ) / Real.pi)) ∧
      1 / 2 ≤ gammaPlus Λ ∧ gammaPlus Λ ≤ 2 ∧ 1 / 2 ≤ gammaMinus Λ ∧ gammaMinus Λ ≤ 2 := by
  obtain ⟨U, μ, rfl, hμ⟩ := Edge_decomp hΛ
  have hm := Edge_Hm_mSol U μ hΛ hℓ
  obtain ⟨h1, h2⟩ := Edge_E_eq U μ hΛ hℓ hμ
  have hp := Edge_gamma_lim hμ hℓ hm
  have hn := Edge_gamma_lim' hμ hℓ hm
  have cp := Edge_c3_bd hμ hℓ
  have cn := Edge_c3_bd (Edge_neg_bd hμ) hℓ
  set Lp := (Real.sqrt (Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹)))⁻¹ / Real.pi
  set Ln := (Real.sqrt (Edge_av (fun j => ((Edge_wp (fun j => -μ j) - -μ j) ^ 3)⁻¹)))⁻¹ /
    Real.pi
  have bp := Edge_inv_sqrt_bd cp.1 cp.2.1
  have bn := Edge_inv_sqrt_bd cn.1 cn.2.1
  have hπ := Real.pi_pos
  have hgp : gammaPlus (Edge_cd U fun j => (μ j : ℂ)) = (Real.pi * Lp) ^ (2 / 3 : ℝ) := by
    unfold gammaPlus; rw [h1]; congr 2; exact hp.limUnder_eq
  have hgn : gammaMinus (Edge_cd U fun j => (μ j : ℂ)) = (Real.pi * Ln) ^ (2 / 3 : ℝ) := by
    unfold gammaMinus; rw [h2]; congr 2; exact hn.limUnder_eq
  have ep : Real.pi * Lp = (Real.sqrt (Edge_av (fun j => ((Edge_wp μ - μ j) ^ 3)⁻¹)))⁻¹ := by
    simp only [Lp]; field_simp
  have en : Real.pi * Ln =
      (Real.sqrt (Edge_av (fun j => ((Edge_wp (fun j => -μ j) - -μ j) ^ 3)⁻¹)))⁻¹ := by
    simp only [Ln]; field_simp
  rw [hgp, hgn, Edge_rpow_inv (by rw [ep]; linarith), Edge_rpow_inv (by rw [en]; linarith),
    mul_div_cancel_left₀ _ hπ.ne', mul_div_cancel_left₀ _ hπ.ne', h1, h2, ep, en]
  exact ⟨hp, hn, (Edge_rpow_bd bp.1 bp.2).1, (Edge_rpow_bd bp.1 bp.2).2, (Edge_rpow_bd bn.1 bn.2).1,
    (Edge_rpow_bd bn.1 bn.2).2⟩

/-- (A.1) [square_root_density] of Lemma A.1 [lemma_usual_properties_of_m_and_mu]: square-root
behaviour of `ρ_N` on `[E⁻, E⁺]`, and `Im m ∼ √(κ+η)` inside, `Im m ∼ η/√(κ+η)` outside, for
`|z| ≤ τ⁻¹`, `η > 0`; the constant depends on `τ` only. -/
theorem square_root_density (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      (∀ x ∈ Set.Icc (Eminus Λ) (Eplus Λ),
        C⁻¹ * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ)) ≤ rho Λ x ∧
          rho Λ x ≤ C * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ))) ∧
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        (z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ) →
          C⁻¹ * Real.sqrt (kappa Λ z.re + z.im) ≤ (mSol Λ z).im ∧
            (mSol Λ z).im ≤ C * Real.sqrt (kappa Λ z.re + z.im)) ∧
        (z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ) →
          C⁻¹ * (z.im / Real.sqrt (kappa Λ z.re + z.im)) ≤ (mSol Λ z).im ∧
            (mSol Λ z).im ≤ C * (z.im / Real.sqrt (kappa Λ z.re + z.im))) := by
  have hR₀ : (3 : ℝ) ≤ τ⁻¹ + 3 := by linarith [inv_pos.2 hτ]
  refine ⟨Edge_C (τ⁻¹ + 3), Edge_C_pos hR₀, fun ι _ _ _ Λ hΛ hℓ => ?_⟩
  obtain ⟨U, μ, rfl, hμ⟩ := Edge_decomp hΛ
  have hm := Edge_Hm_mSol U μ hΛ hℓ
  obtain ⟨h1, h2⟩ := Edge_E_eq U μ hΛ hℓ hμ
  have hk : ∀ E : ℝ, kappa (Edge_cd U fun j => (μ j : ℂ)) E =
      min |Edge_ep μ - E| |E - Edge_em μ| := fun E => by unfold kappa; rw [h1, h2]
  simp only [hk]
  rw [h1, h2]
  obtain ⟨F1, F2⟩ := Edge_full hμ hℓ hR₀ hm
  exact ⟨F1, fun z hzn hz => F2 z (hzn.trans (by linarith)) hz⟩

/-- (A.2) [edge_close_to_edge_sc]: `|2 - E⁺| + |2 + E⁻| ≤ C‖Λ‖`, `C` absolute. -/
theorem edge_close_to_edge_sc :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      |2 - Eplus Λ| + |2 + Eminus Λ| ≤ C * opNorm Λ := by
  refine ⟨3, by norm_num, fun ι _ _ _ Λ hΛ hℓ => ?_⟩
  obtain ⟨U, μ, rfl, hμ⟩ := Edge_decomp hΛ
  obtain ⟨h1, h2⟩ := Edge_E_eq U μ hΛ hℓ hμ
  rw [h1, h2]
  have b1 := Edge_ep_bd hμ hℓ
  have b2 := Edge_ep_bd (Edge_neg_bd hμ) hℓ
  have hl0 := Edge_l0 hμ
  unfold Edge_em
  have e1 : |2 - Edge_ep μ| ≤ 3 / 2 * opNorm (Edge_cd U fun j => (μ j : ℂ)) :=
    abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have e2 : |2 + -Edge_ep (fun j => -μ j)| ≤ 3 / 2 * opNorm (Edge_cd U fun j => (μ j : ℂ)) :=
    abs_le.2 ⟨by nlinarith, by nlinarith⟩
  linarith

end RBMTransitionEdge

end
