module

public import RBMTransitionEdge.LocalLaw.CumulantClass
public import RBMTransitionEdge.LocalLaw.ResPolyDer
public import RBMTransitionEdge.Prob.GridMartingale

@[expose] public section

/-!
# Chains of resolvents

Chains `B₁G₁B₂G₂⋯B_pG_p` of §3 (Definitions 3.1 [def_wtM], 3.2 [defLK3]), their entrywise
derivative along a Hermitian slice.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The chain `B₁ G₁ B₂ G₂ ⋯ B_p G_p`, `G_r = (h + Λ_r - ξ_r)⁻¹`, listed as `(B_r, Λ_r, ξ_r)`:
the products of resolvents of Definitions 3.1 [def_wtM] and 3.2 [defLK3] and of (3.57)
[eq:quad_integrand]. -/
def chainB {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ)) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  (l.map fun f => f.1 * res (Matrix.of h + f.2.1) f.2.2).prod

/-- The slice `w ↦ setEntry h i j w` is real-differentiable. -/
private lemma Chain_diff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    Differentiable ℝ (fun x : ℂ => setEntry h i j x) := by
  refine differentiable_pi.mpr fun p => differentiable_pi.mpr fun m => ?_
  by_cases hij : i = j
  · subst hij
    by_cases hpm : p = i ∧ m = i
    · have e : (fun x : ℂ => setEntry h i i x p m) = fun x => ((x.re : ℝ) : ℂ) := by
        funext x; simp [setEntry, hpm]
      rw [e]
      exact (Complex.ofRealCLM.comp Complex.reCLM).differentiable
    · have e : (fun x : ℂ => setEntry h i i x p m) = fun _ => h p m := by
        funext x; simp [setEntry, hpm]
      rw [e]
      exact differentiable_const _
  · by_cases h1 : p = i ∧ m = j
    · have e : (fun x : ℂ => setEntry h i j x p m) = fun x => x := by
        funext x; simp [setEntry, hij, h1]
      rw [e]
      exact differentiable_id
    · by_cases h2 : p = j ∧ m = i
      · have e : (fun x : ℂ => setEntry h i j x p m) = fun x => starRingEnd ℂ x := by
          funext x; simp [setEntry, hij, h2]
        rw [e]
        exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiable
      · have e : (fun x : ℂ => setEntry h i j x p m) = fun _ => h p m := by
          funext x; simp [setEntry, hij, h1, h2]
        rw [e]
        exact differentiable_const _

/-- Every entry of the resolvent along the slice is real-differentiable. -/
private lemma Chain_diff_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (ξ : ℂ) (hξ : ξ.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j p m : Idx D N) :
    Differentiable ℝ (fun x : ℂ => res (Matrix.of (setEntry h i j x) + Λ) ξ p m) := by
  have e : (fun x : ℂ => res (Matrix.of (setEntry h i j x) + Λ) ξ p m) =
      (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + Λ) ξ p m) ∘
        fun x : ℂ => setEntry h i j x := by
    funext x
    simp only [Function.comp]
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact ((contDiff_res_symArr Λ hΛ ξ hξ p m 1).differentiable (by norm_num)).comp
    (Chain_diff_slice h i j)

/-- The Wirtinger derivative of a finite sum. -/
private lemma Chain_dW_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    dW (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dW (F a) w := by
  have e : fderiv ℝ (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, fderiv ℝ (F a) w := fderiv_fun_sum hF
  simp only [dW, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- The Wirtinger derivative of a constant multiple. -/
private lemma Chain_dW_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) :
    dW (fun x => c * F x) w = c * dW F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  simp only [dW, e, _root_.smul_apply, smul_eq_mul]; ring


/-- Differentiability and the first Wirtinger derivative of every chain entry along the slice. -/
private lemma Chain_dW_aux {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) → ∀ k m : Idx D N,
      Differentiable ℝ (fun w => chainB (setEntry h i j w) l k m) ∧
      dW (fun w => chainB (setEntry h i j w) l k m) = fun w =>
        -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
          chainB (setEntry h i j w) (l.take (r + 1)) k i *
            (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
              chainB (setEntry h i j w) (l.drop (r + 1))) j m := by
  intro l
  induction l with
  | nil =>
    intro _ k m
    simp only [chainB, List.map_nil, List.prod_nil]
    refine ⟨differentiable_const _, ?_⟩
    funext w
    simp [dW]
  | cons a t ih =>
    intro hl k m
    have ha := hl a (by simp)
    have ht := ih (fun f hf => hl f (by simp [hf]))
    set Gm : ℂ → Matrix (Idx D N) (Idx D N) ℂ :=
      fun w => res (Matrix.of (setEntry h i j w) + a.2.1) a.2.2 with hGm
    set c : ℂ := -(if i = j then 1 / 2 else 1) with hc
    have hG : ∀ p q, Differentiable ℝ (fun x : ℂ => Gm x p q) := fun p q =>
      Chain_diff_res a.2.1 ha.1 a.2.2 ha.2 h hh i j p q
    have hGd : ∀ w p q, dW (fun x => Gm x p q) w = c * (Gm w p i * Gm w j q) := fun w p q =>
      congrFun (res_dW a.2.1 ha.1 a.2.2 ha.2 h hh i j p q).1 w
    have hcons : ∀ (w : ℂ) (t' : List (Matrix (Idx D N) (Idx D N) ℂ ×
        Matrix (Idx D N) (Idx D N) ℂ × ℂ)), chainB (setEntry h i j w) (a :: t') =
        (a.1 * Gm w) * chainB (setEntry h i j w) t' := fun w t' => by
      simp only [chainB, List.map_cons, List.prod_cons, hGm]
    have hE : (fun w => chainB (setEntry h i j w) (a :: t) k m) = fun w =>
        ∑ q, (∑ s, a.1 k s * Gm w s q) * chainB (setEntry h i j w) t q m := by
      funext w
      rw [hcons w t, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    have hP : ∀ q, Differentiable ℝ (fun x => ∑ s, a.1 k s * Gm x s q) := fun q =>
      Differentiable.fun_sum fun s _ => (hG s q).const_mul _
    rw [hE]
    refine ⟨Differentiable.fun_sum fun q _ => (hP q).mul (ht q m).1, ?_⟩
    funext w
    have hdw : dW (fun x => ∑ q, (∑ s, a.1 k s * Gm x s q) *
          chainB (setEntry h i j x) t q m) w =
        ∑ q, (dW (fun x => ∑ s, a.1 k s * Gm x s q) w * chainB (setEntry h i j w) t q m +
          (∑ s, a.1 k s * Gm w s q) * dW (fun x => chainB (setEntry h i j x) t q m) w) := by
      rw [Chain_dW_sum Finset.univ (fun q x => (∑ s, a.1 k s * Gm x s q) *
        chainB (setEntry h i j x) t q m) (fun q _ => ((hP q) w).mul ((ht q m).1 w))]
      exact Finset.sum_congr rfl fun q _ => (dW_mul (hP q w) ((ht q m).1 w)).1
    have hP1 : ∀ q, dW (fun x => ∑ s, a.1 k s * Gm x s q) w =
        ∑ s, a.1 k s * (c * (Gm w s i * Gm w j q)) := by
      intro q
      rw [Chain_dW_sum Finset.univ (fun s x => a.1 k s * Gm x s q)
        (fun s _ => ((hG s q) w).const_mul _)]
      exact Finset.sum_congr rfl fun s _ => by
        rw [Chain_dW_const_mul (F := fun x => Gm x s q) _ (hG s q w), hGd]
    have hC : ∀ q, dW (fun x => chainB (setEntry h i j x) t q m) w =
        c * ∑ r : Fin t.length, chainB (setEntry h i j w) (t.take (r + 1)) q i *
          (res (Matrix.of (setEntry h i j w) + (t.get r).2.1) (t.get r).2.2 *
            chainB (setEntry h i j w) (t.drop (r + 1))) j m := fun q => congrFun (ht q m).2 w
    rw [hdw]
    simp only [hP1, hC]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.length_cons, List.get_eq_getElem,
      List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ, List.getElem_cons_zero,
      List.take_zero, List.drop_zero]
    have hnil : chainB (setEntry h i j w) [] = 1 := by simp [chainB]
    have h1 : chainB (setEntry h i j w) [a] = a.1 * Gm w := by
      rw [hcons w [], hnil, mul_one]
    have e2 : ∀ (X : Idx D N → Fin t.length → ℂ) (Y : Fin t.length → ℂ) (P : Idx D N → ℂ),
        ∑ x, P x * (c * ∑ r, X x r * Y r) = c * ∑ r, (∑ x, P x * X x r) * Y r := by
      intro X Y P
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => by ring
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    · rw [h1]
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => by ring
    · refine (e2 _ _ _).trans ?_
      congr 1

/-- The first Wirtinger derivative of a chain entry along a Hermitian slice:
`∂_w (B₁G₁⋯B_pG_p)_{km} = -c Σ_r (B₁G₁⋯B_rG_r)_{ki} (G_r B_{r+1}G_{r+1}⋯B_pG_p)_{jm}`, `c = 1`
for `i ≠ j` and `c = 1/2` for `i = j`. -/
theorem chainB_dW {D N : ℕ}
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j k m : Idx D N) :
    dW (fun w => chainB (setEntry h i j w) l k m) = fun w =>
      -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
        chainB (setEntry h i j w) (l.take (r + 1)) k i *
          (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
            chainB (setEntry h i j w) (l.drop (r + 1))) j m := by
  exact (Chain_dW_aux h hh i j l hl k m).2

end RBMTransitionEdge

end
