module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic

@[expose] public section

/-!
# The self-consistent equation (2.16): existence, uniqueness and first identities

Definition 2.7 [defn_Mm]: the solution `m` of (2.16) [self_m] with `Im m > 0` exists, is unique and analytic on the
upper half plane; its extension `mExt` to `ℂ` by reflection and boundary values; the identities (A.3)
[equation_z_im_m], the a priori bounds behind the expansion (A.19) [taylor_expansion_M] and the
derivatives (A.43) [derivative_m_t_z_with_t_and_z].
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The solution `m(z)` of (2.16) [self_m] on all of `ℂ`: `mSol Λ z` for `Im z > 0`, the reflection
`m(z̄) = conj m(z)` of Definition 2.7 [defn_Mm] for `Im z < 0`, and the boundary value
`lim_{η↓0} m(E + iη)` at a real point `z = E`. -/
def mExt {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then mSol Λ z
  else if z.im < 0 then star (mSol Λ (star z))
  else limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => mSol Λ (z + (η : ℂ) * Complex.I)

/-- `M(z) = (Λ - z - m(z))⁻¹` of (2.17) [def_G0], built from `mExt`. -/
def MExt {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (Λ - (z + mExt Λ z) • (1 : Matrix ι ι ℂ))⁻¹

/-- The Stieltjes transform `m_sc(z)` of the semicircle density (2.18) [eq:semidensity]: the
solution of (2.16) [self_m] for `Λ = 0`. -/
def msc (z : ℂ) : ℂ := mExt (0 : Matrix (Fin 1) (Fin 1) ℂ) z

/-- `⟨Λ²⟩`, the normalized trace of `Λ²`. -/
def avgSq {ι : Type*} [Fintype ι] (Λ : Matrix ι ι ℂ) : ℝ := (ntr (Λ * Λ)).re


section Aux

variable {ι : Type*} [Fintype ι]

/-- `s(ζ) = n⁻¹ Σ_j (μ_j - ζ)⁻¹`, the normalized trace of `(Λ - ζ)⁻¹` when `Λ` has eigenvalues
`μ_j`; (2.16) [self_m] reads `m = s(z + m)`. -/
private def Core_S (μ : ι → ℝ) (ζ : ℂ) : ℂ :=
  ((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - ζ)⁻¹

/-- `n⁻¹ Σ_j |μ_j - ζ|⁻²`, the normalized trace of `M M^*` in (A.3) [equation_z_im_m]. -/
private def Core_A (μ : ι → ℝ) (ζ : ℂ) : ℝ :=
  ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖((μ j : ℂ) - ζ)⁻¹‖ ^ 2

private lemma Core_ne (x : ℝ) {ζ : ℂ} (h : 0 < ζ.im) : (x : ℂ) - ζ ≠ 0 := by
  intro e
  have := congrArg Complex.im e
  simp at this
  linarith

private lemma Core_im_inv (x : ℝ) (ζ : ℂ) :
    (((x : ℂ) - ζ)⁻¹).im = ζ.im * ‖((x : ℂ) - ζ)⁻¹‖ ^ 2 := by
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.inv_im]
  simp [div_eq_mul_inv]

/-- For `Im ζ > 0`, `x - ζ ≠ 0` and `|x - ζ|⁻¹ ≤ (Im ζ)⁻¹`. -/
private lemma Core_norm_inv_le (x : ℝ) {ζ : ℂ} (h : 0 < ζ.im) :
    (x : ℂ) - ζ ≠ 0 ∧ ‖((x : ℂ) - ζ)⁻¹‖ ≤ ζ.im⁻¹ := by
  refine ⟨Core_ne x h, ?_⟩
  rw [norm_inv]
  apply inv_anti₀ h
  have := Complex.abs_im_le_norm ((x : ℂ) - ζ)
  rwa [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos h] at this

private lemma Core_card_inv_eq : ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) := by
  push_cast; rfl

private lemma Core_im_S (μ : ι → ℝ) (ζ : ℂ) : (Core_S μ ζ).im = ζ.im * Core_A μ ζ := by
  rw [Core_S, Core_A, Core_card_inv_eq, Complex.im_ofReal_mul, Complex.im_sum]
  simp only [Core_im_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma Core_A_pos [Nonempty ι] (μ : ι → ℝ) {ζ : ℂ} (h : 0 < ζ.im) : 0 < Core_A μ ζ := by
  unfold Core_A
  apply mul_pos (inv_pos.2 (by exact_mod_cast Fintype.card_pos))
  apply Finset.sum_pos (fun j _ => by
    exact pow_pos (norm_pos_iff.2 (inv_ne_zero (Core_ne (μ j) h))) 2) Finset.univ_nonempty

private lemma Core_A_nonneg (μ : ι → ℝ) (ζ : ℂ) : 0 ≤ Core_A μ ζ := by
  unfold Core_A; positivity

/-- For `Im ζ > 0`, every `μ_j - ζ ≠ 0` and `n⁻¹ Σ_j |μ_j - ζ|⁻¹ ≤ (Im ζ)⁻¹`. -/
private lemma Core_sum_norm_le [Nonempty ι] (μ : ι → ℝ) {ζ : ℂ} (h : 0 < ζ.im) :
    (∀ j, (μ j : ℂ) - ζ ≠ 0) ∧ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖((μ j : ℂ) - ζ)⁻¹‖ ≤ ζ.im⁻¹ := by
  refine ⟨fun j => Core_ne (μ j) h, ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖((μ j : ℂ) - ζ)⁻¹‖
      ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, ζ.im⁻¹ := by
        gcongr with j; exact (Core_norm_inv_le (μ j) h).2
    _ = ζ.im⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

private lemma Core_norm_S_le' (μ : ι → ℝ) (ζ : ℂ) :
    ‖Core_S μ ζ‖ ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖((μ j : ℂ) - ζ)⁻¹‖ := by
  rw [Core_S, norm_mul, norm_inv]
  simp only [Complex.norm_natCast]
  gcongr
  exact norm_sum_le _ _

/-- Cauchy–Schwarz for normalized sums. -/
private lemma Core_cs (a b : ι → ℂ) :
    ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, a j * b j‖ ^ 2 ≤
      (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖a j‖ ^ 2) *
        (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2) := by
  have h1 : ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, a j * b j‖ ≤
      ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖a j‖ * ‖b j‖ := by
    rw [norm_mul, norm_inv]
    simp only [Complex.norm_natCast]
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖b j‖)
  calc _ ≤ (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by
        gcongr
    _ = ((Fintype.card ι : ℝ))⁻¹ ^ 2 * (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by ring
    _ ≤ ((Fintype.card ι : ℝ))⁻¹ ^ 2 * ((∑ j, ‖a j‖ ^ 2) * ∑ j, ‖b j‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- The arithmetic–geometric bound for normalized sums. -/
private lemma Core_amgm (a b : ι → ℂ) :
    ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, a j * b j‖ ≤
      ((((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖a j‖ ^ 2) +
        (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2)) / 2 := by
  rw [norm_mul, norm_inv]
  simp only [Complex.norm_natCast]
  calc ((Fintype.card ι : ℝ))⁻¹ * ‖∑ j, a j * b j‖
      ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, (‖a j‖ ^ 2 + ‖b j‖ ^ 2) / 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        nlinarith [two_mul_le_add_sq ‖a j‖ ‖b j‖]
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]; ring

/-- The difference of two normalized resolvent sums. -/
private lemma Core_key (μ μ' : ι → ℝ) {ζ ζ' : ℂ} (h : 0 < ζ.im) (h' : 0 < ζ'.im) :
    Core_S μ ζ - Core_S μ' ζ' =
      (ζ - ζ') * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - ζ)⁻¹ * ((μ' j : ℂ) - ζ')⁻¹) +
      ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, ((μ' j : ℂ) - (μ j : ℂ)) * (((μ j : ℂ) - ζ)⁻¹ * ((μ' j : ℂ) - ζ')⁻¹) := by
  have e : ∀ j, ((μ j : ℂ) - ζ)⁻¹ - ((μ' j : ℂ) - ζ')⁻¹ =
      (ζ - ζ') * (((μ j : ℂ) - ζ)⁻¹ * ((μ' j : ℂ) - ζ')⁻¹) +
        ((μ' j : ℂ) - (μ j : ℂ)) * (((μ j : ℂ) - ζ)⁻¹ * ((μ' j : ℂ) - ζ')⁻¹) := by
    intro j
    have h1 := Core_ne (μ j) h
    have h2 := Core_ne (μ' j) h'
    field_simp
    ring
  simp only [Core_S, ← mul_sub, ← Finset.sum_sub_distrib, e, Finset.sum_add_distrib, mul_add,
    ← Finset.mul_sum]
  ring


/-- A solution of `w = s(z + w)` has `n⁻¹ Σ_j |μ_j - z - w|⁻² (Im z + Im w) = Im w`, the scalar
form of (A.3) [equation_z_im_m]. -/
private lemma Core_A_sol (μ : ι → ℝ) {z w : ℂ} (h : w = Core_S μ (z + w)) :
    Core_A μ (z + w) * (z.im + w.im) = w.im := by
  have := congrArg Complex.im h
  rw [Core_im_S, Complex.add_im] at this
  linarith

private lemma Core_A_sol_lt (μ : ι → ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (h : w = Core_S μ (z + w)) : Core_A μ (z + w) < 1 := by
  have h1 := Core_A_sol μ h
  have h2 := Core_A_nonneg μ (z + w)
  nlinarith

/-- Two solutions of the scalar form of (2.16) [self_m]: `(w - w')(1 - P) = (z - z') P + R`. -/
private lemma Core_sol_diff (μ μ' : ι → ℝ) {z z' w w' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (hw : 0 < w.im) (hw' : 0 < w'.im) (h : w = Core_S μ (z + w)) (h' : w' = Core_S μ' (z' + w')) :
    (w - w') * (1 - ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, ((μ j : ℂ) - (z + w))⁻¹ * ((μ' j : ℂ) - (z' + w'))⁻¹) =
      (z - z') * (((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, ((μ j : ℂ) - (z + w))⁻¹ * ((μ' j : ℂ) - (z' + w'))⁻¹) +
      ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, ((μ' j : ℂ) - (μ j : ℂ)) * (((μ j : ℂ) - (z + w))⁻¹ * ((μ' j : ℂ) - (z' + w'))⁻¹) := by
  have k := Core_key μ μ' (ζ := z + w) (ζ' := z' + w') (by simp; linarith) (by simp; linarith)
  rw [← h, ← h'] at k
  linear_combination k

/-- For a solution `w' = s'(z' + w')` with `Im z', Im w' > 0`: every `μ'_j - z' - w' ≠ 0`, and
`|n⁻¹ Σ_j (μ_j - z - w)⁻¹ (μ'_j - z' - w')⁻¹| ≤ (n⁻¹ Σ_j |μ_j - z - w|⁻² + 1)/2`. -/
private lemma Core_P_lt (μ μ' : ι → ℝ) {z z' w w' : ℂ} (hz' : 0 < z'.im) (hw' : 0 < w'.im)
    (h' : w' = Core_S μ' (z' + w')) :
    (∀ j, (μ' j : ℂ) - (z' + w') ≠ 0) ∧
    ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - (z + w))⁻¹ * ((μ' j : ℂ) - (z' + w'))⁻¹‖ ≤
      (Core_A μ (z + w) + 1) / 2 := by
  refine ⟨fun j => Core_ne (μ' j) (by simp; linarith), ?_⟩
  have := Core_amgm (fun j => ((μ j : ℂ) - (z + w))⁻¹) (fun j => ((μ' j : ℂ) - (z' + w'))⁻¹)
  have h2 := Core_A_sol_lt μ' hz' hw' h'
  simp only [Core_A] at h2 ⊢
  linarith

/-- Uniqueness in Definition 2.7 [defn_Mm]: `w = s(z + w)` has at most one solution with
`Im w > 0`. -/
private lemma Core_unique (μ : ι → ℝ) {z w w' : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) (hw' : 0 < w'.im) (h : w = Core_S μ (z + w)) (h' : w' = Core_S μ (z + w')) :
    w = w' := by
  have k := Core_sol_diff μ μ hz hz hw hw' h h'
  have hP := (Core_P_lt μ μ (z := z) (w := w) hz hw' h').2
  have hA := Core_A_sol_lt μ hz hw h
  simp only [sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at k
  rcases mul_eq_zero.1 k with e | e
  · exact sub_eq_zero.1 e
  · exfalso
    rw [sub_eq_zero] at e
    rw [← e, norm_one] at hP
    linarith

/-- Existence in Definition 2.7 [defn_Mm]: `w = s(z + w)` has a solution with `Im w > 0`, the
limit of the iterates `w_{k+1} = s(z + w_k)`. -/
private lemma Core_exists [Nonempty ι] (μ : ι → ℝ) {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, 0 < w.im ∧ w = Core_S μ (z + w) := by
  set η := z.im with hη
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun w => Core_S μ (z + w) := ⟨_, rfl⟩
  have hζ : ∀ w : ℂ, 0 ≤ w.im → 0 < (z + w).im := fun w hw => by simp; linarith
  have hFim : ∀ w : ℂ, (F w).im = Core_A μ (z + w) * (η + w.im) := fun w => by
    rw [hF]; simp only [Core_im_S, Complex.add_im]; ring
  have hFpos : ∀ w : ℂ, 0 ≤ w.im → 0 < (F w).im := fun w hw => by
    rw [hFim]; exact mul_pos (Core_A_pos μ (hζ w hw)) (by linarith)
  have hFnorm : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ η⁻¹ := fun w hw => by
    rw [hF]
    refine (Core_norm_S_le' μ _).trans ((Core_sum_norm_le μ (hζ w hw)).2.trans ?_)
    apply inv_anti₀ hz
    simp; linarith
  have hFlip : ∀ w w' : ℂ, 0 ≤ w.im → 0 ≤ w'.im →
      ‖F w - F w'‖ ^ 2 ≤ ‖w - w'‖ ^ 2 * (Core_A μ (z + w) * Core_A μ (z + w')) := by
    intro w w' hw hw'
    have k := Core_key μ μ (hζ w hw) (hζ w' hw')
    simp only [sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at k
    have hc := Core_cs (fun j => ((μ j : ℂ) - (z + w))⁻¹) (fun j => ((μ j : ℂ) - (z + w'))⁻¹)
    rw [hF]
    change ‖Core_S μ (z + w) - Core_S μ (z + w')‖ ^ 2 ≤ _
    rw [k, show z + w - (z + w') = w - w' by ring, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  obtain ⟨u, hu0, hu_succ⟩ : ∃ u : ℕ → ℂ, u 0 = F Complex.I ∧ ∀ k, u (k + 1) = F (u k) :=
    ⟨fun k => F^[k + 1] Complex.I, rfl, fun k => Function.iterate_succ_apply' F (k + 1) _⟩
  have hu_im : ∀ k, 0 < (u k).im := by
    intro k
    cases k with
    | zero => rw [hu0]; exact hFpos _ (by simp)
    | succ k =>
      rw [hu_succ]
      apply hFpos
      induction k with
      | zero => rw [hu0]; exact (hFpos _ (by simp)).le
      | succ k ih => rw [hu_succ]; exact (hFpos _ ih).le
  have hu_norm : ∀ k, ‖u k‖ ≤ η⁻¹ := by
    intro k
    cases k with
    | zero => rw [hu0]; exact hFnorm _ (by simp)
    | succ k => rw [hu_succ]; exact hFnorm _ (hu_im k).le
  have hu_imle : ∀ k, (u k).im ≤ η⁻¹ := fun k =>
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hu_norm k))
  set q : ℝ := (1 + η ^ 2)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hxq : ∀ x : ℝ, 0 ≤ x → x ≤ η⁻¹ → x ≤ q * (η + x) := by
    intro x hx0 hx1
    have hxη : x * η ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hx1 hz.le
      rwa [inv_mul_cancel₀ hz.ne'] at this
    rw [hq, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- `x A ≤ q · Im F` where `x = Im w`, `A = A(z + w)`
  have hxA : ∀ k, (u k).im * Core_A μ (z + u k) ≤ q * (u (k + 1)).im := by
    intro k
    rw [hu_succ, hFim]
    have := hxq _ (hu_im k).le (hu_imle k)
    have hA := Core_A_nonneg μ (z + u k)
    nlinarith
  set d0 : ℝ := ‖u 1 - u 0‖ ^ 2 / ((u 1).im * (u 0).im) with hd0
  have hd0nn : 0 ≤ d0 := by have := hu_im 0; have := hu_im 1; positivity
  have hclaim : ∀ k, ‖u (k + 1) - u k‖ ^ 2 ≤ d0 * q ^ (2 * k) * ((u (k + 1)).im * (u k).im) := by
    intro k
    induction k with
    | zero =>
      have : 0 < (u 1).im * (u 0).im := mul_pos (hu_im 1) (hu_im 0)
      simp [hd0, div_mul_cancel₀ _ this.ne']
    | succ k ih =>
      have hl := hFlip (u (k + 1)) (u k) (hu_im _).le (hu_im _).le
      rw [← hu_succ, ← hu_succ] at hl
      refine hl.trans ?_
      have e1 := hxA (k + 1)
      have e2 := hxA k
      have hA1 := Core_A_nonneg μ (z + u (k + 1))
      have hA2 := Core_A_nonneg μ (z + u k)
      have hi1 := hu_im k
      have hi2 := hu_im (k + 1)
      have hi3 := hu_im (k + 2)
      calc ‖u (k + 1) - u k‖ ^ 2 * (Core_A μ (z + u (k + 1)) * Core_A μ (z + u k))
          ≤ d0 * q ^ (2 * k) * ((u (k + 1)).im * (u k).im) *
              (Core_A μ (z + u (k + 1)) * Core_A μ (z + u k)) := by gcongr
        _ = d0 * q ^ (2 * k) * (((u (k + 1)).im * Core_A μ (z + u (k + 1))) *
              ((u k).im * Core_A μ (z + u k))) := by ring
        _ ≤ d0 * q ^ (2 * k) * ((q * (u (k + 2)).im) * (q * (u (k + 1)).im)) := by
              gcongr
        _ = d0 * q ^ (2 * (k + 1)) * ((u (k + 1 + 1)).im * (u (k + 1)).im) := by ring
  have hdist : ∀ k, dist (u k) (u (k + 1)) ≤ (Real.sqrt d0 * η⁻¹) * q ^ k := by
    intro k
    rw [dist_comm, dist_eq_norm]
    have hb : ‖u (k + 1) - u k‖ ^ 2 ≤ (Real.sqrt d0 * η⁻¹ * q ^ k) ^ 2 := by
      refine (hclaim k).trans ?_
      have h1 := hu_imle k
      have h2 := hu_imle (k + 1)
      have h3 := hu_im k
      have h4 := hu_im (k + 1)
      rw [mul_pow, mul_pow, Real.sq_sqrt hd0nn, ← pow_mul, mul_comm k 2]
      have : (u (k + 1)).im * (u k).im ≤ η⁻¹ ^ 2 := by
        rw [sq]; exact mul_le_mul h2 h1 h3.le (by positivity)
      calc d0 * q ^ (2 * k) * ((u (k + 1)).im * (u k).im) ≤ d0 * q ^ (2 * k) * η⁻¹ ^ 2 := by
            gcongr
        _ = _ := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hb
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q _ hq1 hdist)
  have hwim : 0 ≤ w.im :=
    ge_of_tendsto' ((Complex.continuous_im.tendsto w).comp hw) fun k => (hu_im k).le
  have hFc : ContinuousAt F w := by
    have hne : ∀ j, (μ j : ℂ) - (z + w) ≠ 0 := fun j => Core_ne (μ j) (hζ w hwim)
    rw [hF]
    simp only [Core_S]
    fun_prop (disch := exact hne _)
  have e1 : Tendsto (fun k => u (k + 1)) atTop (𝓝 w) := hw.comp (tendsto_add_atTop_nat 1)
  have e2 : Tendsto (fun k => u (k + 1)) atTop (𝓝 (F w)) := by
    simp only [hu_succ]; exact hFc.tendsto.comp hw
  have hfix : w = F w := tendsto_nhds_unique e1 e2
  have hpos : 0 < w.im := by rw [hfix]; exact hFpos w hwim
  refine ⟨w, hpos, ?_⟩
  subst hF
  exact hfix

section Mat

variable [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def Core_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma Core_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Core_cd U d * Core_cd U e = Core_cd U (fun j => d j * e j) := by
  rw [Core_cd, Core_cd, Core_cd, ← map_mul, diagonal_mul_diagonal]

private lemma Core_cd_one (U : Matrix.unitaryGroup ι ℂ) : Core_cd U (fun _ => 1) = 1 := by
  rw [Core_cd, diagonal_one, map_one]

private lemma Core_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • Core_cd U d = Core_cd U (fun j => c * d j) := by
  rw [Core_cd, Core_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma Core_cd_sub (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Core_cd U d - Core_cd U e = Core_cd U (fun j => d j - e j) := by
  rw [Core_cd, Core_cd, Core_cd, ← map_sub, diagonal_sub]

private lemma Core_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    Core_cd U d - c • (1 : Matrix ι ι ℂ) = Core_cd U (fun j => d j - c) := by
  rw [← Core_cd_one U, Core_cd_smul, Core_cd_sub]
  simp

private lemma Core_cd_pow (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (l : ℕ) :
    Core_cd U d ^ l = Core_cd U (fun j => d j ^ l) := by
  rw [Core_cd, Core_cd, ← map_pow, diagonal_pow]
  rfl

private lemma Core_cd_conjTranspose (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    (Core_cd U d)ᴴ = Core_cd U (fun j => star (d j)) := by
  rw [← star_eq_conjTranspose, Core_cd, Core_cd, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose]
  rfl

private lemma Core_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (Core_cd U d) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d j := by
  rw [ntr, Core_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]

private lemma Core_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (Core_cd U d)⁻¹ = Core_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [Core_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact Core_cd_one U

/-- The spectral decomposition of a Hermitian matrix. -/
private lemma Core_spec {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    Λ = Core_cd hΛ.eigenvectorUnitary (fun j => (hΛ.eigenvalues j : ℂ)) :=
  hΛ.spectral_theorem

/-- `(Λ - ζ)⁻¹ = U diag((μ_j - ζ)⁻¹) U^*` for `Λ = U diag(μ) U^*` and `Im ζ > 0`. -/
private lemma Core_resolvent (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {ζ : ℂ} (h : 0 < ζ.im) :
    (Core_cd U (fun j => (μ j : ℂ)) - ζ • (1 : Matrix ι ι ℂ))⁻¹ =
      Core_cd U (fun j => ((μ j : ℂ) - ζ)⁻¹) := by
  rw [Core_cd_sub_smul_one, Core_cd_inv _ _ fun j => Core_ne (μ j) h]

private lemma Core_ntr_resolvent (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {ζ : ℂ}
    (h : 0 < ζ.im) :
    ntr (Core_cd U (fun j => (μ j : ℂ)) - ζ • (1 : Matrix ι ι ℂ))⁻¹ = Core_S μ ζ := by
  rw [Core_resolvent U μ h, Core_ntr_cd]
  rfl

private lemma Core_pred_iff (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z : ℂ} (hz : 0 < z.im)
    (w : ℂ) :
    (0 < w.im ∧ w = ntr (Core_cd U (fun j => (μ j : ℂ)) - (z + w) • (1 : Matrix ι ι ℂ))⁻¹) ↔
      (0 < w.im ∧ w = Core_S μ (z + w)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Core_ntr_resolvent U μ (by simp; linarith)] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Core_ntr_resolvent U μ (by simp; linarith)]

/-- Definition 2.7 [defn_Mm] for `Λ = U diag(μ) U^*`. -/
private lemma Core_eu [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    ∃! w : ℂ, 0 < w.im ∧
      w = ntr (Core_cd U (fun j => (μ j : ℂ)) - (z + w) • (1 : Matrix ι ι ℂ))⁻¹ := by
  rw [existsUnique_congr (Core_pred_iff U μ hz)]
  obtain ⟨w, hw, hw'⟩ := Core_exists μ hz
  exact ⟨w, ⟨hw, hw'⟩, fun v hv => Core_unique μ hz hv.1 hw hv.2 hw'⟩

/-- `m = mSol Λ z` solves `m = s(z + m)`, the scalar form of (2.16) [self_m], and
`M = U diag((μ_j - z - m)⁻¹) U^*` in (2.17) [def_G0]. -/
private lemma Core_mSol [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    0 < (mSol (Core_cd U (fun j => (μ j : ℂ))) z).im ∧
      mSol (Core_cd U (fun j => (μ j : ℂ))) z =
        Core_S μ (z + mSol (Core_cd U (fun j => (μ j : ℂ))) z) ∧
      MSol (Core_cd U (fun j => (μ j : ℂ))) z =
        Core_cd U (fun j => ((μ j : ℂ) - (z + mSol (Core_cd U (fun j => (μ j : ℂ))) z))⁻¹) := by
  have h := (Core_eu U μ hz).exists
  have hs : 0 < (mSol (Core_cd U (fun j => (μ j : ℂ))) z).im ∧
      mSol (Core_cd U (fun j => (μ j : ℂ))) z =
        ntr (Core_cd U (fun j => (μ j : ℂ)) -
          (z + mSol (Core_cd U (fun j => (μ j : ℂ))) z) • (1 : Matrix ι ι ℂ))⁻¹ := by
    unfold mSol
    simp only [h, dite_true]
    exact h.choose_spec
  have hs' := (Core_pred_iff U μ hz _).1 hs
  refine ⟨hs'.1, hs'.2, ?_⟩
  rw [MSol, Core_resolvent U μ (by simp; linarith [hs'.1])]

/-- A function with `‖f x - f x₀‖ ≤ C ‖x - x₀‖` near `x₀` is continuous at `x₀`. -/
private lemma Core_tendsto_of_lip {α : Type*} [NormedAddCommGroup α] (f : α → ℂ) (x₀ : α) (C : ℝ)
    (h : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) h ?_
  have : Tendsto (fun x => C * ‖x - x₀‖) (𝓝 x₀) (𝓝 (C * ‖x₀ - x₀‖)) :=
    ((continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x₀)
  simpa using this

/-- The `z`-derivative in (A.43) [derivative_m_t_z_with_t_and_z], for `Λ = U diag(μ) U^*`. -/
private lemma Core_deriv_z [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) :
    HasDerivAt (mSol (Core_cd U (fun j => (μ j : ℂ))))
      ((((Fintype.card ι : ℂ))⁻¹ *
          ∑ j, ((μ j : ℂ) - (z₀ + mSol (Core_cd U (fun j => (μ j : ℂ))) z₀))⁻¹ *
            ((μ j : ℂ) - (z₀ + mSol (Core_cd U (fun j => (μ j : ℂ))) z₀))⁻¹) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ *
          ∑ j, ((μ j : ℂ) - (z₀ + mSol (Core_cd U (fun j => (μ j : ℂ))) z₀))⁻¹ *
            ((μ j : ℂ) - (z₀ + mSol (Core_cd U (fun j => (μ j : ℂ))) z₀))⁻¹)) z₀ := by
  set m := mSol (Core_cd U (fun j => (μ j : ℂ))) with hm
  set P : ℂ → ℂ := fun z => ((Fintype.card ι : ℂ))⁻¹ *
    ∑ j, ((μ j : ℂ) - (z₀ + m z₀))⁻¹ * ((μ j : ℂ) - (z + m z))⁻¹ with hP
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : ∀ᶠ z in 𝓝 z₀, 0 < z.im := hopen.mem_nhds hz₀
  have hs₀ := Core_mSol U μ hz₀
  set p : ℝ := (Core_A μ (z₀ + m z₀) + 1) / 2 with hp
  have hp1 : p < 1 := by have := Core_A_sol_lt μ hz₀ hs₀.1 hs₀.2.1; rw [hp]; linarith
  have hPle : ∀ z : ℂ, 0 < z.im → ‖P z‖ ≤ p := fun z hz =>
    (Core_P_lt μ μ (z := z₀) (w := m z₀) hz (Core_mSol U μ hz).1 (Core_mSol U μ hz).2.1).2
  have hid : ∀ z : ℂ, 0 < z.im → (m z₀ - m z) * (1 - P z) = (z₀ - z) * P z := fun z hz => by
    have := Core_sol_diff μ μ hz₀ hz hs₀.1 (Core_mSol U μ hz).1 hs₀.2.1 (Core_mSol U μ hz).2.1
    simpa only [sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] using this
  have hne : ∀ z : ℂ, 0 < z.im → 1 - P z ≠ 0 := fun z hz e => by
    have h1 : P z = 1 := (sub_eq_zero.1 e).symm
    have := hPle z hz
    rw [h1, norm_one] at this
    linarith
  have hslope : ∀ z : ℂ, 0 < z.im → z ≠ z₀ → slope m z₀ z = P z / (1 - P z) := fun z hz hzz => by
    rw [slope_def_field, eq_div_iff (hne z hz), div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.2 hzz)]
    linear_combination (-1 : ℂ) * hid z hz
  -- continuity of `m` at `z₀`
  have hcont : Tendsto m (𝓝 z₀) (𝓝 (m z₀)) := by
    refine Core_tendsto_of_lip m z₀ (1 - p)⁻¹ (hev.mono fun z hz => ?_)
    have h1 := hid z hz
    have h2 : ‖m z - m z₀‖ * ‖1 - P z‖ = ‖z - z₀‖ * ‖P z‖ := by
      rw [← norm_mul, ← norm_mul, ← norm_neg, ← norm_neg ((z - z₀) * P z)]
      congr 1
      linear_combination h1
    have h3 : 1 - p ≤ ‖1 - P z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (P z)
      rw [norm_one] at this
      linarith [hPle z hz]
    have h4 : ‖P z‖ ≤ 1 := (hPle z hz).trans hp1.le
    rw [le_inv_mul_iff₀ (by linarith)]
    calc (1 - p) * ‖m z - m z₀‖ ≤ ‖1 - P z‖ * ‖m z - m z₀‖ := by gcongr
      _ = ‖z - z₀‖ * ‖P z‖ := by rw [mul_comm, h2]
      _ ≤ ‖z - z₀‖ * 1 := by gcongr
      _ = ‖z - z₀‖ := mul_one _
  have hne₀ : ∀ j, (μ j : ℂ) - (z₀ + m z₀) ≠ 0 := fun j =>
    Core_ne (μ j) (by simp; linarith [hs₀.1])
  have hPt : Tendsto P (𝓝 z₀) (𝓝 (P z₀)) := by
    simp only [hP]
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => Tendsto.const_mul _ ?_)
    exact ((tendsto_const_nhds.sub (tendsto_id.add hcont))).inv₀ (hne₀ j)
  have hq : Tendsto (fun z => P z / (1 - P z)) (𝓝 z₀) (𝓝 (P z₀ / (1 - P z₀))) :=
    hPt.div (tendsto_const_nhds.sub hPt) (hne z₀ hz₀)
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hq.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hzz
  exact (hslope z hz hzz).symm

private lemma Core_cd_real_smul (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (s : ℝ) :
    (s : ℂ) • Core_cd U (fun j => (μ j : ℂ)) = Core_cd U (fun j => ((s * μ j : ℝ) : ℂ)) := by
  rw [Core_cd_smul]
  congr 1
  funext j
  push_cast
  ring

/-- For `Im z, Im w > 0`, `x - z - w ≠ 0` and `|x - z - w|⁻¹ ≤ (Im z)⁻¹`. -/
private lemma Core_norm_inv_le' (x : ℝ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (x : ℂ) - (z + w) ≠ 0 ∧ ‖((x : ℂ) - (z + w))⁻¹‖ ≤ z.im⁻¹ :=
  ⟨Core_ne x (by simp; linarith),
    (Core_norm_inv_le x (by simp; linarith)).2.trans (inv_anti₀ hz (by simp; linarith))⟩

/-- The `t`-derivative in (A.43) [derivative_m_t_z_with_t_and_z], for `Λ = U diag(μ) U^*`. -/
private lemma Core_deriv_t [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z : ℂ}
    (hz : 0 < z.im) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mSol (Core_cd U (fun j => ((s * μ j : ℝ) : ℂ))) z)
      (-(((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) *
          ((((t * μ j : ℝ) : ℂ) - (z + mSol (Core_cd U (fun j => ((t * μ j : ℝ) : ℂ))) z))⁻¹ *
            (((t * μ j : ℝ) : ℂ) - (z + mSol (Core_cd U (fun j => ((t * μ j : ℝ) : ℂ))) z))⁻¹)) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j,
          (((t * μ j : ℝ) : ℂ) - (z + mSol (Core_cd U (fun j => ((t * μ j : ℝ) : ℂ))) z))⁻¹ *
            (((t * μ j : ℝ) : ℂ) - (z + mSol (Core_cd U (fun j => ((t * μ j : ℝ) : ℂ))) z))⁻¹))
      t := by
  set m : ℝ → ℂ := fun s => mSol (Core_cd U (fun j => ((s * μ j : ℝ) : ℂ))) z with hm
  have hs : ∀ s : ℝ, 0 < (m s).im ∧ m s = Core_S (fun j => s * μ j) (z + m s) := fun s =>
    ⟨(Core_mSol U (fun j => s * μ j) hz).1, (Core_mSol U (fun j => s * μ j) hz).2.1⟩
  set P : ℝ → ℂ := fun s => ((Fintype.card ι : ℂ))⁻¹ *
    ∑ j, (((t * μ j : ℝ) : ℂ) - (z + m t))⁻¹ * (((s * μ j : ℝ) : ℂ) - (z + m s))⁻¹ with hP
  set Q : ℝ → ℂ := fun s => ((Fintype.card ι : ℂ))⁻¹ *
    ∑ j, (μ j : ℂ) * ((((t * μ j : ℝ) : ℂ) - (z + m t))⁻¹ * (((s * μ j : ℝ) : ℂ) - (z + m s))⁻¹)
    with hQ
  set p : ℝ := (Core_A (fun j => t * μ j) (z + m t) + 1) / 2 with hp
  have hp1 : p < 1 := by
    have := Core_A_sol_lt (fun j => t * μ j) hz (hs t).1 (hs t).2
    rw [hp]; linarith
  have hPle : ∀ s : ℝ, ‖P s‖ ≤ p := fun s =>
    (Core_P_lt (fun j => t * μ j) (fun j => s * μ j) (z := z) (w := m t) hz (hs s).1 (hs s).2).2
  set K : ℝ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖(μ j : ℂ)‖ * (z.im⁻¹ * z.im⁻¹) with hK
  have hQle : ∀ s : ℝ, ‖Q s‖ ≤ K := fun s => by
    simp only [hQ, hK, norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul]
    gcongr
    · exact (Core_norm_inv_le' _ hz (hs t).1).2
    · exact (Core_norm_inv_le' _ hz (hs s).1).2
  have hid : ∀ s : ℝ, (m t - m s) * (1 - P s) = ((s : ℂ) - t) * Q s := fun s => by
    have := Core_sol_diff (fun j => t * μ j) (fun j => s * μ j) hz hz (hs t).1 (hs s).1 (hs t).2
      (hs s).2
    simp only [sub_self, zero_mul, zero_add] at this
    rw [this, hQ]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hne : ∀ s : ℝ, 1 - P s ≠ 0 := fun s e => by
    have h1 : P s = 1 := (sub_eq_zero.1 e).symm
    have := hPle s
    rw [h1, norm_one] at this
    linarith
  have hslope : ∀ s : ℝ, s ≠ t → slope m t s = -Q s / (1 - P s) := fun s hst => by
    have hst' : (s : ℂ) - t ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hst)
    rw [slope_def_module, Complex.real_smul, eq_div_iff (hne s)]
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * hid s
  have hcont : Tendsto m (𝓝 t) (𝓝 (m t)) := by
    refine Core_tendsto_of_lip m t ((1 - p)⁻¹ * K) (Eventually.of_forall fun s => ?_)
    have h2 : ‖m s - m t‖ * ‖1 - P s‖ = ‖s - t‖ * ‖Q s‖ := by
      rw [← norm_mul, show ‖s - t‖ = ‖((s : ℂ) - t)‖ by
        rw [← Complex.ofReal_sub, Complex.norm_real], ← norm_mul, ← norm_neg]
      congr 1
      linear_combination hid s
    have h3 : 1 - p ≤ ‖1 - P s‖ := by
      have := norm_sub_norm_le (1 : ℂ) (P s)
      rw [norm_one] at this
      linarith [hPle s]
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hQle s)
    rw [mul_assoc, le_inv_mul_iff₀ (by linarith)]
    calc (1 - p) * ‖m s - m t‖ ≤ ‖1 - P s‖ * ‖m s - m t‖ := by gcongr
      _ = ‖s - t‖ * ‖Q s‖ := by rw [mul_comm, h2]
      _ ≤ ‖s - t‖ * K := by gcongr; exact hQle s
      _ = K * ‖s - t‖ := mul_comm _ _
  have hne₀ : ∀ j, ((t * μ j : ℝ) : ℂ) - (z + m t) ≠ 0 := fun j =>
    Core_ne _ (by simp; linarith [(hs t).1])
  have hb : ∀ j, Tendsto (fun s : ℝ => (((s * μ j : ℝ) : ℂ) - (z + m s))⁻¹) (𝓝 t)
      (𝓝 ((((t * μ j : ℝ) : ℂ) - (z + m t))⁻¹)) := fun j => by
    have h1 : Tendsto (fun s : ℝ => ((s * μ j : ℝ) : ℂ)) (𝓝 t) (𝓝 ((t * μ j : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).tendsto t
    exact (h1.sub (tendsto_const_nhds.add hcont)).inv₀ (hne₀ j)
  have hPt : Tendsto P (𝓝 t) (𝓝 (P t)) := by
    simp only [hP]
    exact Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => Tendsto.const_mul _ (hb j))
  have hQt : Tendsto Q (𝓝 t) (𝓝 (Q t)) := by
    simp only [hQ]
    exact Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ =>
      Tendsto.const_mul _ (Tendsto.const_mul _ (hb j)))
  have hq : Tendsto (fun s => -Q s / (1 - P s)) (𝓝 t) (𝓝 (-Q t / (1 - P t))) :=
    hQt.neg.div (tendsto_const_nhds.sub hPt) (hne t)
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hq.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hst
  exact (hslope s hst).symm

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma Core_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
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
private lemma Core_decomp {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ),
      Λ = Core_cd U (fun j => (μ j : ℂ)) ∧ ∀ j, |μ j| ≤ opNorm Λ :=
  ⟨_, _, Core_spec hΛ, Core_eig_le hΛ⟩

/-- `|z + m| > 1 - ℓ` when every `|μ_j| ≤ ℓ`. -/
private lemma Core_zeta_gt [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (ℓ : ℝ)
    (hμ : ∀ j, |μ j| ≤ ℓ) {z : ℂ} (hz : 0 < z.im) :
    1 - ℓ < ‖z + mSol (Core_cd U (fun j => (μ j : ℂ))) z‖ := by
  set m := mSol (Core_cd U (fun j => (μ j : ℂ))) z
  have hs := Core_mSol U μ hz
  have hA := Core_A_sol_lt μ hz hs.1 hs.2.1
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ j, ‖((μ j : ℂ) - (z + m))⁻¹‖ ^ 2 < ∑ _j : ι, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    unfold Core_A at hA
    rwa [inv_mul_lt_iff₀ hn, mul_one] at hA
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt hsum
  have hne := Core_ne (μ j) (ζ := z + m) (by simp; linarith [hs.1])
  have h1 : 1 < ‖(μ j : ℂ) - (z + m)‖ := by
    rw [norm_inv, inv_pow] at hj
    have h0 : 0 < ‖(μ j : ℂ) - (z + m)‖ ^ 2 := by positivity
    have : 1 < ‖(μ j : ℂ) - (z + m)‖ ^ 2 := by
      rwa [inv_lt_one₀ h0] at hj
    nlinarith [norm_nonneg ((μ j : ℂ) - (z + m))]
  have h2 := norm_sub_le (μ j : ℂ) (z + m)
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  linarith [hμ j]

/-- `|m| < 1`. -/
private lemma Core_m_lt [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z : ℂ}
    (hz : 0 < z.im) : ‖mSol (Core_cd U (fun j => (μ j : ℂ))) z‖ < 1 := by
  have hs := Core_mSol U μ hz
  have hA := Core_A_sol_lt μ hz hs.1 hs.2.1
  set m := mSol (Core_cd U (fun j => (μ j : ℂ))) z
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set X := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖((μ j : ℂ) - (z + m))⁻¹‖ with hX
  have h1 : ‖m‖ ≤ X := by
    rw [hs.2.1]
    exact Core_norm_S_le' μ _
  have h2 : X ^ 2 ≤ Core_A μ (z + m) := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => ‖((μ j : ℂ) - (z + m))⁻¹‖)
    rw [Finset.card_univ] at this
    rw [hX, Core_A, mul_pow]
    calc ((Fintype.card ι : ℝ))⁻¹ ^ 2 * (∑ j, ‖((μ j : ℂ) - (z + m))⁻¹‖) ^ 2
        ≤ ((Fintype.card ι : ℝ))⁻¹ ^ 2 *
            ((Fintype.card ι : ℝ) * ∑ j, ‖((μ j : ℂ) - (z + m))⁻¹‖ ^ 2) := by gcongr
      _ = _ := by field_simp
  have hX0 : 0 ≤ X := by positivity
  have : X < 1 := by nlinarith
  linarith

end Mat

end Aux

/-- Definition 2.7 [defn_Mm]: for Hermitian `Λ` and `Im z > 0`, (2.16) [self_m] has exactly one
solution with positive imaginary part. -/
theorem mSol_existsUnique {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ∃! w : ℂ, 0 < w.im ∧ w = ntr (Λ - (z + w) • (1 : Matrix ι ι ℂ))⁻¹ := by
  obtain ⟨U, μ, rfl, -⟩ := Core_decomp hΛ
  exact Core_eu U μ hz

/-- Definition 2.7 [defn_Mm]: `mSol Λ z` solves (2.16) [self_m] with `Im m > 0`, and the inverse
in (2.17) [def_G0] is a genuine inverse. -/
theorem mSol_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    0 < (mSol Λ z).im ∧ mSol Λ z = ntr (MSol Λ z) ∧
      (Λ - (z + mSol Λ z) • (1 : Matrix ι ι ℂ)) * MSol Λ z = 1 := by
  obtain ⟨U, μ, rfl, -⟩ := Core_decomp hΛ
  obtain ⟨h1, h2, h3⟩ := Core_mSol U μ hz
  refine ⟨h1, ?_, ?_⟩
  · rw [h3, Core_ntr_cd]
    exact h2
  · rw [h3, Core_cd_sub_smul_one, Core_cd_mul]
    simp only [mul_inv_cancel₀ (Core_ne _ (show 0 < (z + mSol _ z).im by simp; linarith))]
    exact Core_cd_one U

/-- Definition 2.7 [defn_Mm]: `m` is analytic on the upper half plane. -/
theorem mSol_analyticOnNhd {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) :
    AnalyticOnNhd ℂ (mSol Λ) {z : ℂ | 0 < z.im} := by
  obtain ⟨U, μ, rfl, -⟩ := Core_decomp hΛ
  exact DifferentiableOn.analyticOnNhd (fun z hz =>
    (Core_deriv_z U μ hz).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_im)

/-- Definition 2.7 [defn_Mm]: `m(z̄) = conj m(z)` and `M(z̄) = M(z)^*` for `z ∉ ℝ`. -/
theorem mExt_conj {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    mExt Λ (star z) = star (mExt Λ z) ∧ MExt Λ (star z) = (MExt Λ z)ᴴ := by
  have h1 : mExt Λ (star z) = star (mExt Λ z) := by
    rcases lt_or_gt_of_ne hz with h | h
    · have h' : 0 < (star z).im := by simpa using h
      simp only [mExt, h', h.not_gt, ↓reduceIte, h, star_star]
    · have h' : (star z).im < 0 := by simpa using h
      simp only [mExt, h', h'.not_gt, h, ↓reduceIte, star_star]
  refine ⟨h1, ?_⟩
  rw [MExt, MExt, h1, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_smul,
    conjTranspose_one, hΛ.eq, star_add]

/-- A priori bounds behind (A.19) [taylor_expansion_M]: for `‖Λ‖ ≤ 1/10` and `Im z > 0`,
`|z + m| > 1 - ‖Λ‖`, `|m| < 1` and `‖M‖ < (1 - 2‖Λ‖)⁻¹`. -/
theorem mSol_apriori {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    1 - opNorm Λ < ‖z + mSol Λ z‖ ∧ ‖mSol Λ z‖ < 1 ∧
      opNorm (MSol Λ z) < (1 - 2 * opNorm Λ)⁻¹ := by
  have hspec := mSol_spec Λ hΛ z hz
  obtain ⟨U, μ, rfl, hμ⟩ := Core_decomp hΛ
  set ℓ := opNorm (Core_cd U (fun j => (μ j : ℂ)))
  have hζ := Core_zeta_gt U μ ℓ hμ hz
  refine ⟨hζ, Core_m_lt U μ hz, ?_⟩
  set Λ := Core_cd U (fun j => (μ j : ℂ))
  set ζ := z + mSol Λ z
  have hℓ0 : 0 ≤ ℓ := norm_nonneg _
  have hpos : 0 < ‖ζ‖ - ℓ := by linarith
  have hT : ∀ y, (‖ζ‖ - ℓ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (MSol Λ z) y‖ ≤ ‖y‖ := by
    intro y
    set x := Matrix.toEuclideanCLM (𝕜 := ℂ) (MSol Λ z) y
    have hy : Matrix.toEuclideanCLM (𝕜 := ℂ) Λ x - ζ • x = y := by
      have := congrArg (fun A => Matrix.toEuclideanCLM (𝕜 := ℂ) A y) hspec.2.2
      simp only [map_mul, map_sub, map_smul, map_one] at this
      exact this
    have h1 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Λ x‖ ≤ ℓ * ‖x‖ :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ) Λ).le_opNorm x
    have h2 : ‖ζ • x‖ - ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Λ x‖ ≤ ‖y‖ := by
      rw [← hy, ← norm_neg (_ - _), neg_sub]
      exact norm_sub_norm_le _ _
    rw [norm_smul] at h2
    nlinarith
  have hle : opNorm (MSol Λ z) ≤ (‖ζ‖ - ℓ)⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hpos.le) fun y => ?_
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hT y
  refine hle.trans_lt ?_
  exact inv_strictAnti₀ (by linarith) (by linarith)

/-- (A.43) [derivative_m_t_z_with_t_and_z]: `∂_z m = ⟨M²⟩ / (1 - ⟨M²⟩)` and, for `M_t` the matrix
of `tΛ`, `∂_t m_t = -⟨Λ M_t²⟩ / (1 - ⟨M_t²⟩)`. -/
theorem derivative_m_t_z {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (t : ℝ) :
    HasDerivAt (mSol Λ) (ntr (MSol Λ z ^ 2) / (1 - ntr (MSol Λ z ^ 2))) z ∧
      HasDerivAt (fun s : ℝ => mSol ((s : ℂ) • Λ) z)
        (-ntr (Λ * MSol ((t : ℂ) • Λ) z ^ 2) / (1 - ntr (MSol ((t : ℂ) • Λ) z ^ 2))) t := by
  obtain ⟨U, μ, rfl, -⟩ := Core_decomp hΛ
  constructor
  · rw [(Core_mSol U μ hz).2.2, Core_cd_pow, Core_ntr_cd]
    simpa only [sq] using Core_deriv_z U μ hz
  · simp only [Core_cd_real_smul]
    rw [(Core_mSol U (fun j => t * μ j) hz).2.2, Core_cd_pow, Core_cd_mul, Core_ntr_cd,
      Core_ntr_cd]
    simpa only [sq] using Core_deriv_t U μ hz t

/-- (A.3) [equation_z_im_m]: `⟨M M^*⟩ = Im m / (Im m + η)`, together with the identity
`M - M^* = 2i (η + Im m) M M^*`. -/
theorem equation_z_im_m {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ntr (MSol Λ z * (MSol Λ z)ᴴ) = (((mSol Λ z).im / ((mSol Λ z).im + z.im) : ℝ) : ℂ) ∧
      MSol Λ z - (MSol Λ z)ᴴ =
        (2 * Complex.I * ((z.im + (mSol Λ z).im : ℝ) : ℂ)) • (MSol Λ z * (MSol Λ z)ᴴ) := by
  obtain ⟨U, μ, rfl, -⟩ := Core_decomp hΛ
  obtain ⟨h1, h2, h3⟩ := Core_mSol U μ hz
  have hA := Core_A_sol μ h2
  set m := mSol (Core_cd U (fun j => (μ j : ℂ))) z
  have hden : 0 < m.im + z.im := by linarith
  rw [h3, Core_cd_conjTranspose, Core_cd_mul]
  constructor
  · rw [Core_ntr_cd]
    have e : ∀ j, ((μ j : ℂ) - (z + m))⁻¹ * star ((μ j : ℂ) - (z + m))⁻¹ =
        ((‖((μ j : ℂ) - (z + m))⁻¹‖ ^ 2 : ℝ) : ℂ) := fun j => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e]
    have hA' : Core_A μ (z + m) = m.im / (m.im + z.im) := by
      rw [eq_div_iff hden.ne']; linarith
    rw [← hA', Core_A]
    push_cast
    rfl
  · rw [Core_cd_sub, Core_cd_smul]
    congr 1
    funext j
    have hi := Core_im_inv (μ j) (z + m)
    rw [Complex.add_im] at hi
    generalize ((μ j : ℂ) - (z + m))⁻¹ = a at hi ⊢
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    generalize ‖a‖ ^ 2 = r at hi ⊢
    apply Complex.ext
    · simp
    · simp [hi]
      ring

end RBMTransitionEdge

end
