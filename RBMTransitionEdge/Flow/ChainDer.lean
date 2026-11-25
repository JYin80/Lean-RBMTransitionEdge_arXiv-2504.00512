module

public import RBMTransitionEdge.Flow.Chain

@[expose] public section

/-!
# Wirtinger calculus for the resolvent chains of §3

The conjugate derivative of a chain entry along a Hermitian slice, the bounds on the Wirtinger
derivatives of all orders of chain entries and loops built from Definitions 3.1 [def_wtM] and 3.2
[defLK3] (the input of Lemma 2.11 [lem:complex_cumu] in Lemmas 3.6, 3.7, 3.14, 3.15), and a chain
entry as a resolvent polynomial.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The factors `(B, Λ, ξ)` of a chain. -/
abbrev CD_T (D N : ℕ) :=
  Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ

/-- The slice `w ↦ setEntry h i j w` is real-differentiable. -/
private lemma CD_diff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
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
private lemma CD_diff_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
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
    (CD_diff_slice h i j)

/-- The Wirtinger derivative of a finite sum. -/
private lemma CD_dW_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    dW (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dW (F a) w := by
  have e : fderiv ℝ (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, fderiv ℝ (F a) w := fderiv_fun_sum hF
  simp only [dW, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- The conjugate Wirtinger derivative of a finite sum. -/
private lemma CD_dWbar_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    dWbar (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dWbar (F a) w := by
  have e : fderiv ℝ (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, fderiv ℝ (F a) w := fderiv_fun_sum hF
  simp only [dWbar, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

/-- The Wirtinger derivative of a constant multiple. -/
private lemma CD_dW_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) :
    dW (fun x => c * F x) w = c * dW F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  simp only [dW, e, _root_.smul_apply, smul_eq_mul]; ring

/-- The conjugate Wirtinger derivative of a constant multiple. -/
private lemma CD_dWbar_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) :
    dWbar (fun x => c * F x) w = c * dWbar F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  simp only [dWbar, e, _root_.smul_apply, smul_eq_mul]; ring

/-- Differentiability and the conjugate Wirtinger derivative of every chain entry along the
slice. -/
private lemma CD_dWbar_aux {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    ∀ l : List (CD_T D N),
      (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) → ∀ k m : Idx D N,
      Differentiable ℝ (fun w => chainB (setEntry h i j w) l k m) ∧
      dWbar (fun w => chainB (setEntry h i j w) l k m) = fun w =>
        -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
          chainB (setEntry h i j w) (l.take (r + 1)) k j *
            (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
              chainB (setEntry h i j w) (l.drop (r + 1))) i m := by
  intro l
  induction l with
  | nil =>
    intro _ k m
    simp only [chainB, List.map_nil, List.prod_nil]
    refine ⟨differentiable_const _, ?_⟩
    funext w
    simp [dWbar]
  | cons a t ih =>
    intro hl k m
    have ha := hl a (by simp)
    have ht := ih (fun f hf => hl f (by simp [hf]))
    set Gm : ℂ → Matrix (Idx D N) (Idx D N) ℂ :=
      fun w => res (Matrix.of (setEntry h i j w) + a.2.1) a.2.2 with hGm
    set c : ℂ := -(if i = j then 1 / 2 else 1) with hc
    have hG : ∀ p q, Differentiable ℝ (fun x : ℂ => Gm x p q) := fun p q =>
      CD_diff_res a.2.1 ha.1 a.2.2 ha.2 h hh i j p q
    have hGd : ∀ w p q, dWbar (fun x => Gm x p q) w = c * (Gm w p j * Gm w i q) := fun w p q =>
      congrFun (res_dW a.2.1 ha.1 a.2.2 ha.2 h hh i j p q).2 w
    have hcons : ∀ (w : ℂ) (t' : List (CD_T D N)), chainB (setEntry h i j w) (a :: t') =
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
    have hdw : dWbar (fun x => ∑ q, (∑ s, a.1 k s * Gm x s q) *
          chainB (setEntry h i j x) t q m) w =
        ∑ q, (dWbar (fun x => ∑ s, a.1 k s * Gm x s q) w * chainB (setEntry h i j w) t q m +
          (∑ s, a.1 k s * Gm w s q) * dWbar (fun x => chainB (setEntry h i j x) t q m) w) := by
      rw [CD_dWbar_sum Finset.univ (fun q x => (∑ s, a.1 k s * Gm x s q) *
        chainB (setEntry h i j x) t q m) (fun q _ => ((hP q) w).mul ((ht q m).1 w))]
      exact Finset.sum_congr rfl fun q _ => (dW_mul (hP q w) ((ht q m).1 w)).2
    have hP1 : ∀ q, dWbar (fun x => ∑ s, a.1 k s * Gm x s q) w =
        ∑ s, a.1 k s * (c * (Gm w s j * Gm w i q)) := by
      intro q
      rw [CD_dWbar_sum Finset.univ (fun s x => a.1 k s * Gm x s q)
        (fun s _ => ((hG s q) w).const_mul _)]
      exact Finset.sum_congr rfl fun s _ => by
        rw [CD_dWbar_const_mul (F := fun x => Gm x s q) _ (hG s q w), hGd]
    have hC : ∀ q, dWbar (fun x => chainB (setEntry h i j x) t q m) w =
        c * ∑ r : Fin t.length, chainB (setEntry h i j w) (t.take (r + 1)) q j *
          (res (Matrix.of (setEntry h i j w) + (t.get r).2.1) (t.get r).2.2 *
            chainB (setEntry h i j w) (t.drop (r + 1))) i m := fun q => congrFun (ht q m).2 w
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



/-- The conjugate Wirtinger derivative of a chain entry along a Hermitian slice:
`∂_{w̄} (B₁G₁⋯B_pG_p)_{km} = -c Σ_r (B₁G₁⋯B_rG_r)_{kj} (G_r B_{r+1}G_{r+1}⋯B_pG_p)_{im}`, `c = 1`
for `i ≠ j` and `c = 1/2` for `i = j`. -/
theorem chainB_dWbar {D N : ℕ}
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j k m : Idx D N) :
    dWbar (fun w => chainB (setEntry h i j w) l k m) = fun w =>
      -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
        chainB (setEntry h i j w) (l.take (r + 1)) k j *
          (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
            chainB (setEntry h i j w) (l.drop (r + 1))) i m := by
  exact (CD_dWbar_aux h hh i j l hl k m).2

/-- The entry `x^* B₁G₁⋯B_pG_p y` of a chain along the slice, as a function of `w`. -/
private def CD_atom {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (x y : Idx D N → ℂ) (l : List (CD_T D N)) : ℂ → ℂ :=
  fun w => star x ⬝ᵥ (chainB (setEntry h i j w) l *ᵥ y)

/-- The entry as a double sum over the coordinates of `x` and `y`. -/
private lemma CD_atom_eq {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (x y : Idx D N → ℂ) (l : List (CD_T D N)) (w : ℂ) :
    CD_atom h i j x y l w =
      ∑ k, star (x k) * ∑ m, y m * chainB (setEntry h i j w) l k m := by
  simp only [CD_atom, dotProduct, Pi.star_apply, Matrix.mulVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- The entry against the unit vector `e_a` on the right: `x^* M e_a`. -/
private lemma CD_atom_right {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (x : Idx D N → ℂ) (a : Idx D N) (l : List (CD_T D N)) (w : ℂ) :
    CD_atom h i j x (Pi.single a 1) l w =
      ∑ k, star (x k) * chainB (setEntry h i j w) l k a := by
  rw [CD_atom_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Finset.sum_eq_single a]
  · simp
  · intro m _ hm
    simp [hm]
  · simp

/-- The entry against the unit vector `e_a` on the left: `e_a^* M y`. -/
private lemma CD_atom_left {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (a : Idx D N) (y : Idx D N → ℂ) (l : List (CD_T D N)) (w : ℂ) :
    CD_atom h i j (Pi.single a 1) y l w =
      ∑ m, y m * chainB (setEntry h i j w) l a m := by
  rw [CD_atom_eq, Finset.sum_eq_single a]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- A chain whose first matrix factor is `1` is the resolvent times the rest of the chain. -/
private lemma CD_chainB_cons_one {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (g : CD_T D N)
    (t : List (CD_T D N)) :
    chainB h ((1, g.2) :: t) = res (Matrix.of h + g.2.1) g.2.2 * chainB h t := by
  simp [chainB]

/-- The Wirtinger derivatives of a bilinear combination of differentiable entries act on the
entries. -/
private lemma CD_dW_bil {D N : ℕ} (F : Idx D N → Idx D N → ℂ → ℂ)
    (hF : ∀ k m, Differentiable ℝ (F k m)) (x y : Idx D N → ℂ) :
    (dW (fun w => ∑ k, star (x k) * ∑ m, y m * F k m w) =
      fun w => ∑ k, star (x k) * ∑ m, y m * dW (F k m) w) ∧
    (dWbar (fun w => ∑ k, star (x k) * ∑ m, y m * F k m w) =
      fun w => ∑ k, star (x k) * ∑ m, y m * dWbar (F k m) w) := by
  have hin : ∀ k, Differentiable ℝ (fun w => ∑ m, y m * F k m w) := fun k =>
    Differentiable.fun_sum fun m _ => (hF k m).const_mul _
  constructor
  · funext w
    rw [CD_dW_sum Finset.univ (fun k w => star (x k) * ∑ m, y m * F k m w)
      (fun k _ => ((hin k) w).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [CD_dW_const_mul _ ((hin k) w),
      CD_dW_sum Finset.univ (fun m w => y m * F k m w) (fun m _ => ((hF k m) w).const_mul _)]
    congr 1
    exact Finset.sum_congr rfl fun m _ => CD_dW_const_mul _ ((hF k m) w)
  · funext w
    rw [CD_dWbar_sum Finset.univ (fun k w => star (x k) * ∑ m, y m * F k m w)
      (fun k _ => ((hin k) w).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [CD_dWbar_const_mul _ ((hin k) w),
      CD_dWbar_sum Finset.univ (fun m w => y m * F k m w) (fun m _ => ((hF k m) w).const_mul _)]
    congr 1
    exact Finset.sum_congr rfl fun m _ => CD_dWbar_const_mul _ ((hF k m) w)

/-- Exchange of the order of summation in a product of two sums. -/
private lemma CD_sum_swap {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (a : ι → ℂ) (b : κ → ℂ) (c : ℂ) (T : ρ → ι → ℂ) (U : ρ → κ → ℂ) :
    ∑ k, a k * ∑ m, b m * (c * ∑ r, T r k * U r m) =
      c * ∑ r, (∑ k, a k * T r k) * ∑ m, b m * U r m := by
  have h1 : ∀ k, a k * ∑ m, b m * (c * ∑ r, T r k * U r m) =
      c * ∑ r, ∑ m, a k * T r k * (b m * U r m) := by
    intro k
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => by ring
  have h2 : ∀ r, (∑ k, a k * T r k) * ∑ m, b m * U r m =
      ∑ k, ∑ m, a k * T r k * (b m * U r m) := by
    intro r
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [h1, h2, ← Finset.mul_sum]
  rw [Finset.sum_comm]


/-- The Wirtinger derivatives of an entry `x^* B₁G₁⋯B_pG_p y` are sums of products of two entries of
chains of lengths `r + 1` and `p - r`. -/
private lemma CD_atom_der {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (l : List (CD_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (x y : Idx D N → ℂ) :
    (dW (CD_atom h i j x y l) = fun w => -(if i = j then 1 / 2 else 1) *
      ∑ r : Fin l.length, CD_atom h i j x (Pi.single i 1) (l.take (r + 1)) w *
        CD_atom h i j (Pi.single j 1) y ((1, (l.get r).2) :: l.drop (r + 1)) w) ∧
    (dWbar (CD_atom h i j x y l) = fun w => -(if i = j then 1 / 2 else 1) *
      ∑ r : Fin l.length, CD_atom h i j x (Pi.single j 1) (l.take (r + 1)) w *
        CD_atom h i j (Pi.single i 1) y ((1, (l.get r).2) :: l.drop (r + 1)) w) := by
  have hF : ∀ k m, Differentiable ℝ (fun w => chainB (setEntry h i j w) l k m) := fun k m =>
    (CD_dWbar_aux h hh i j l hl k m).1
  have hA : CD_atom h i j x y l =
      fun w => ∑ k, star (x k) * ∑ m, y m * chainB (setEntry h i j w) l k m :=
    funext fun w => CD_atom_eq h i j x y l w
  obtain ⟨h1, h2⟩ := CD_dW_bil (fun k m w => chainB (setEntry h i j w) l k m) hF x y
  rw [hA]
  constructor
  · rw [h1]
    funext w
    simp only [chainB_dW l hl h hh i j, CD_atom_right, CD_atom_left, CD_chainB_cons_one]
    exact CD_sum_swap _ _ _
      (fun (r : Fin l.length) k => chainB (setEntry h i j w) (l.take (r + 1)) k i)
      (fun (r : Fin l.length) m =>
        (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
        chainB (setEntry h i j w) (l.drop (r + 1))) j m)
  · rw [h2]
    funext w
    simp only [(CD_dWbar_aux h hh i j l hl _ _).2, CD_atom_right, CD_atom_left,
      CD_chainB_cons_one]
    exact CD_sum_swap _ _ _
      (fun (r : Fin l.length) k => chainB (setEntry h i j w) (l.take (r + 1)) k j)
      (fun (r : Fin l.length) m =>
        (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
        chainB (setEntry h i j w) (l.drop (r + 1))) i m)



/-- Every entry along the slice is real-differentiable. -/
private lemma CD_atom_diff {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (l : List (CD_T D N)) (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (x y : Idx D N → ℂ) : Differentiable ℝ (CD_atom h i j x y l) := by
  have hD : ∀ k m, Differentiable ℝ (fun w => chainB (setEntry h i j w) l k m) := fun k m =>
    (CD_dWbar_aux h hh i j l hl k m).1
  have e : CD_atom h i j x y l =
      fun w => ∑ k, star (x k) * ∑ m, y m * chainB (setEntry h i j w) l k m :=
    funext fun w => CD_atom_eq h i j x y l w
  rw [e]
  exact Differentiable.fun_sum fun k _ => Differentiable.const_mul
    (Differentiable.fun_sum fun m _ => (hD k m).const_mul _) _

/-- The entry between two unit vectors is a matrix entry of the chain. -/
private lemma CD_atom_diag {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j a b : Idx D N)
    (l : List (CD_T D N)) (w : ℂ) :
    CD_atom h i j (Pi.single a 1) (Pi.single b 1) l w = chainB (setEntry h i j w) l a b := by
  rw [CD_atom_left, Finset.sum_eq_single b]
  · simp
  · intro m _ hm
    simp [hm]
  · simp

/-- The chain of a concatenated list is the product of the chains. -/
private lemma CD_chainB_append {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (l l' : List (CD_T D N)) :
    chainB h (l ++ l') = chainB h l * chainB h l' := by
  simp [chainB, List.map_append, List.prod_append]

/-- An admissible entry of length `q`: `x^* B₁G₁⋯B_qG_q y` with `x, y ∈ X` and every factor in
`adm`. -/
private def CD_Atm {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (X : Set (Idx D N → ℂ)) (adm : Set (CD_T D N)) (q : ℕ) (F : ℂ → ℂ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ X, ∃ l' : List (CD_T D N),
    (∀ f ∈ l', f ∈ adm) ∧ l'.length = q ∧ 1 ≤ q ∧ F = CD_atom h i j x y l'

/-- Products of `n ≥ 1` admissible entries whose lengths add up to `S`. -/
private inductive CD_Pr {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (X : Set (Idx D N → ℂ)) (adm : Set (CD_T D N)) : ℕ → ℕ → (ℂ → ℂ) → Prop
  | single {q : ℕ} {F : ℂ → ℂ} : CD_Atm h i j X adm q F → CD_Pr h i j X adm 1 q F
  | cons {n S q : ℕ} {A F : ℂ → ℂ} : CD_Atm h i j X adm q A → CD_Pr h i j X adm n S F →
      CD_Pr h i j X adm (n + 1) (S + q) (fun w => A w * F w)

/-- Linear combinations, with coefficients of total modulus at most `K`, of products of `n`
admissible entries of total length `S`. -/
private inductive CD_Sm {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (X : Set (Idx D N → ℂ)) (adm : Set (CD_T D N)) (n S : ℕ) : ℝ → (ℂ → ℂ) → Prop
  | zero : CD_Sm h i j X adm n S 0 (fun _ => 0)
  | pr {F : ℂ → ℂ} : CD_Pr h i j X adm n S F → CD_Sm h i j X adm n S 1 F
  | add {K K' : ℝ} {F G : ℂ → ℂ} : CD_Sm h i j X adm n S K F → CD_Sm h i j X adm n S K' G →
      CD_Sm h i j X adm n S (K + K') (fun w => F w + G w)
  | smul {K : ℝ} {F : ℂ → ℂ} (c : ℂ) : CD_Sm h i j X adm n S K F →
      CD_Sm h i j X adm n S (‖c‖ * K) (fun w => c * F w)
  | mono {K K' : ℝ} {F : ℂ → ℂ} : K ≤ K' → CD_Sm h i j X adm n S K F →
      CD_Sm h i j X adm n S K' F
  | congr {K : ℝ} {F G : ℂ → ℂ} : (∀ w, F w = G w) → CD_Sm h i j X adm n S K F →
      CD_Sm h i j X adm n S K G

section Calculus

variable {D N : ℕ} {h : Idx D N → Idx D N → ℂ} {i j : Idx D N} {X : Set (Idx D N → ℂ)}
  {adm : Set (CD_T D N)}

/-- Equal indices give the same product class. -/
private lemma CD_Pr.cast {n n' S S' : ℕ} {F : ℂ → ℂ} (hn : n = n') (hS : S = S')
    (hF : CD_Pr h i j X adm n S F) : CD_Pr h i j X adm n' S' F := by
  subst hn hS; exact hF

/-- The product classes are closed under pointwise equality. -/
private lemma CD_Pr.congr {n S : ℕ} {F G : ℂ → ℂ} (hFG : ∀ w, F w = G w)
    (hF : CD_Pr h i j X adm n S F) : CD_Pr h i j X adm n S G := by
  have : F = G := funext hFG
  subst this; exact hF

/-- Equal indices give the same combination class. -/
private lemma CD_Sm.cast {n n' S S' : ℕ} {K : ℝ} {F : ℂ → ℂ} (hn : n = n') (hS : S = S')
    (hF : CD_Sm h i j X adm n S K F) : CD_Sm h i j X adm n' S' K F := by
  subst hn hS; exact hF

/-- A product has at least one entry. -/
private lemma CD_Pr.pos {n S : ℕ} {F : ℂ → ℂ} (hF : CD_Pr h i j X adm n S F) : 1 ≤ n := by
  cases hF <;> omega

/-- The total length of `n` entries is at least `n`. -/
private lemma CD_Pr.le {n S : ℕ} {F : ℂ → ℂ} (hF : CD_Pr h i j X adm n S F) : n ≤ S := by
  induction hF with
  | single hA => obtain ⟨_, _, _, _, _, _, _, hq, _⟩ := hA; omega
  | cons hA _ ih => obtain ⟨_, _, _, _, _, _, _, hq, _⟩ := hA; omega

/-- The coefficient mass is nonnegative. -/
private lemma CD_Sm.nonneg {n S : ℕ} {K : ℝ} {F : ℂ → ℂ} (hF : CD_Sm h i j X adm n S K F) :
    0 ≤ K := by
  induction hF with
  | zero => exact le_refl _
  | pr _ => exact zero_le_one
  | add _ _ ih1 ih2 => exact add_nonneg ih1 ih2
  | smul c _ ih => exact mul_nonneg (norm_nonneg _) ih
  | mono hK _ ih => exact ih.trans hK
  | congr _ _ ih => exact ih

/-- Admissible entries are real-differentiable. -/
private lemma CD_Atm.diff (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) {q : ℕ} {F : ℂ → ℂ}
    (hF : CD_Atm h i j X adm q F) : Differentiable ℝ F := by
  obtain ⟨x, _, y, _, l', hl', _, _, rfl⟩ := hF
  exact CD_atom_diff h hh i j l' (fun f hf => hadm f (hl' f hf)) x y

/-- Products of admissible entries are real-differentiable. -/
private lemma CD_Pr.diff (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) {n S : ℕ} {F : ℂ → ℂ}
    (hF : CD_Pr h i j X adm n S F) : Differentiable ℝ F := by
  induction hF with
  | single hA => exact hA.diff hh hadm
  | cons hA _ ih => exact (hA.diff hh hadm).mul ih

/-- Combinations of products of admissible entries are real-differentiable. -/
private lemma CD_Sm.diff (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) {n S : ℕ} {K : ℝ} {F : ℂ → ℂ}
    (hF : CD_Sm h i j X adm n S K F) : Differentiable ℝ F := by
  induction hF with
  | zero => exact differentiable_const _
  | pr hP => exact hP.diff hh hadm
  | add _ _ ih1 ih2 => exact ih1.add ih2
  | smul c _ ih => exact ih.const_mul c
  | mono _ _ ih => exact ih
  | congr hFG _ ih =>
    have : _ = _ := funext hFG
    subst this; exact ih


/-- The Wirtinger derivative of a sum of real-differentiable functions. -/
private lemma CD_dW_add {F G : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℝ F w)
    (hG : DifferentiableAt ℝ G w) :
    dW (fun x => F x + G x) w = dW F w + dW G w := by
  have e : fderiv ℝ (fun x => F x + G x) w = fderiv ℝ F w + fderiv ℝ G w := fderiv_add hF hG
  simp only [dW, e, _root_.add_apply]; ring

/-- The conjugate Wirtinger derivative of a sum of real-differentiable functions. -/
private lemma CD_dWbar_add {F G : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℝ F w)
    (hG : DifferentiableAt ℝ G w) :
    dWbar (fun x => F x + G x) w = dWbar F w + dWbar G w := by
  have e : fderiv ℝ (fun x => F x + G x) w = fderiv ℝ F w + fderiv ℝ G w := fderiv_add hF hG
  simp only [dWbar, e, _root_.add_apply]; ring

/-- A finite sum of combinations. -/
private lemma CD_Sm.sum {n S : ℕ} {K : ℝ} {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ a ∈ s, CD_Sm h i j X adm n S K (F a)) :
    CD_Sm h i j X adm n S (s.card * K) (fun w => ∑ a ∈ s, F a w) := by
  induction s using Finset.induction_on with
  | empty => exact (CD_Sm.zero.mono (by simp)).congr (fun _ => by simp)
  | insert a s ha ih =>
    have t := (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))
    refine (t.mono ?_).congr (fun w => by rw [Finset.sum_insert ha])
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    linarith

/-- A product of two products is a product. -/
private lemma CD_Pr.mul {n S n' S' : ℕ} {F G : ℂ → ℂ} (hF : CD_Pr h i j X adm n S F)
    (hG : CD_Pr h i j X adm n' S' G) :
    CD_Pr h i j X adm (n + n') (S + S') (fun w => F w * G w) := by
  induction hF with
  | single hA => exact (CD_Pr.cons hA hG).cast (by omega) (by omega)
  | cons hA _ ih =>
    exact ((CD_Pr.cons hA ih).cast (by omega) (by omega)).congr (fun w => by ring)

/-- Multiplying a combination by a product of admissible entries. -/
private lemma CD_Sm.mul_pr {n S n' S' : ℕ} {K : ℝ} {F G : ℂ → ℂ}
    (hF : CD_Sm h i j X adm n S K F) (hG : CD_Pr h i j X adm n' S' G) :
    CD_Sm h i j X adm (n + n') (S + S') K (fun w => F w * G w) := by
  induction hF with
  | zero => exact CD_Sm.zero.congr (fun _ => by simp)
  | pr hP => exact CD_Sm.pr (hP.mul hG)
  | add _ _ ih1 ih2 => exact (ih1.add ih2).congr (fun w => by ring)
  | smul c _ ih => exact (ih.smul c).congr (fun w => by ring)
  | mono hK _ ih => exact ih.mono hK
  | congr hFG _ ih => exact ih.congr (fun w => by simp [hFG w])

/-- Multiplying a combination by one admissible entry. -/
private lemma CD_Sm.mul_atm {n S q : ℕ} {K : ℝ} {F A : ℂ → ℂ}
    (hF : CD_Sm h i j X adm n S K F) (hA : CD_Atm h i j X adm q A) :
    CD_Sm h i j X adm (n + 1) (S + q) K (fun w => A w * F w) :=
  (hF.mul_pr (CD_Pr.single hA)).congr (fun _ => mul_comm _ _)


/-- The two entries of one term of a first derivative of an entry of length `p` form a product
of two admissible entries of total length `p + 1`. -/
private lemma CD_pair_Pr (x y u v : Idx D N → ℂ) (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ X)
    (hv : v ∈ X) {l' : List (CD_T D N)} (hl' : ∀ f ∈ l', f ∈ adm)
    (hone : ∀ f ∈ adm, ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) ∈ adm) (r : Fin l'.length) :
    CD_Pr h i j X adm 2 (l'.length + 1) (fun w => CD_atom h i j x u (l'.take (r + 1)) w *
      CD_atom h i j v y ((1, (l'.get r).2) :: l'.drop (r + 1)) w) := by
  have hr := r.isLt
  have hlen1 : (l'.take (r + 1)).length = r + 1 := by
    rw [List.length_take]; omega
  have hlen2 : ((1, (l'.get r).2) :: l'.drop (r + 1)).length = 1 + (l'.length - (r + 1)) := by
    simp [List.length_drop]; omega
  have hA1 : CD_Atm h i j X adm (r + 1) (CD_atom h i j x u (l'.take (r + 1))) :=
    ⟨x, hx, u, hu, l'.take (r + 1), fun f hf => hl' f (List.mem_of_mem_take hf), hlen1,
      by omega, rfl⟩
  have hA2 : CD_Atm h i j X adm (1 + (l'.length - (r + 1)))
      (CD_atom h i j v y ((1, (l'.get r).2) :: l'.drop (r + 1))) := by
    refine ⟨v, hv, y, hy, _, ?_, hlen2, by omega, rfl⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hone _ (hl' _ (List.get_mem _ _))
    · exact hl' f (List.mem_of_mem_drop hf)
  exact ((CD_Pr.cons hA1 (CD_Pr.single hA2)).cast rfl (by omega))

/-- The first derivatives of an admissible entry of length `q` are combinations of products of
two admissible entries of total length `q + 1`, with coefficient mass at most `q`. -/
private lemma CD_Atm.der (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (hone : ∀ f ∈ adm, ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) ∈ adm)
    (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X) {q : ℕ} {A : ℂ → ℂ}
    (hA : CD_Atm h i j X adm q A) :
    CD_Sm h i j X adm 2 (q + 1) q (dW A) ∧ CD_Sm h i j X adm 2 (q + 1) q (dWbar A) := by
  obtain ⟨x, hx, y, hy, l', hl', hlen, hq, rfl⟩ := hA
  have hl : ∀ f ∈ l', f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := fun f hf => hadm f (hl' f hf)
  obtain ⟨h1, h2⟩ := CD_atom_der h hh i j l' hl x y
  have hc : ‖-(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have key : ∀ (u v : Idx D N → ℂ), u ∈ X → v ∈ X →
      CD_Sm h i j X adm 2 (q + 1) q (fun w => -(if i = j then 1 / 2 else 1) *
        ∑ r : Fin l'.length, CD_atom h i j x u (l'.take (r + 1)) w *
          CD_atom h i j v y ((1, (l'.get r).2) :: l'.drop (r + 1)) w) := by
    intro u v hu hv
    have hs := CD_Sm.sum (h := h) (i := i) (j := j) (X := X) (adm := adm) (n := 2) (S := q + 1)
      (K := 1) (Finset.univ : Finset (Fin l'.length))
      (fun (r : Fin l'.length) w => CD_atom h i j x u (l'.take (r + 1)) w *
        CD_atom h i j v y ((1, (l'.get r).2) :: l'.drop (r + 1)) w)
      (fun r _ => CD_Sm.pr ((CD_pair_Pr x y u v hx hy hu hv hl' hone r).cast rfl
        (by omega)))
    have hs2 := hs.smul (-(if i = j then (1 / 2 : ℂ) else 1))
    refine hs2.mono ?_
    rw [Finset.card_univ, Fintype.card_fin, hlen]
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  rw [h1, h2]
  exact ⟨key _ _ hX.1 hX.2, key _ _ hX.2 hX.1⟩


/-- The first derivatives of a product of `n` entries of total length `S` are combinations of
products of `n + 1` entries of total length `S + 1`, with coefficient mass at most `S`. -/
private lemma CD_Pr.der (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (hone : ∀ f ∈ adm, ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) ∈ adm)
    (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X) {n S : ℕ} {F : ℂ → ℂ}
    (hF : CD_Pr h i j X adm n S F) :
    CD_Sm h i j X adm (n + 1) (S + 1) S (dW F) ∧
      CD_Sm h i j X adm (n + 1) (S + 1) S (dWbar F) := by
  induction hF with
  | single hA => exact hA.der hh hadm hone hX
  | @cons n S q A F hA hF ih =>
    have hAd := hA.diff hh hadm
    have hFd := hF.diff hh hadm
    obtain ⟨hA1, hA2⟩ := hA.der hh hadm hone hX
    obtain ⟨hF1, hF2⟩ := ih
    constructor
    · have t1 : CD_Sm h i j X adm (n + 1 + 1) (S + q + 1) (q : ℝ) (fun w => dW A w * F w) :=
        (hA1.mul_pr hF).cast (by omega) (by omega)
      have t2 : CD_Sm h i j X adm (n + 1 + 1) (S + q + 1) (S : ℝ) (fun w => A w * dW F w) :=
        (hF1.mul_atm hA).cast (by omega) (by omega)
      refine ((t1.add t2).mono ?_).congr (fun w => ?_)
      · push_cast; linarith
      · exact ((dW_mul (hAd w) (hFd w)).1).symm
    · have t1 : CD_Sm h i j X adm (n + 1 + 1) (S + q + 1) (q : ℝ)
          (fun w => dWbar A w * F w) :=
        (hA2.mul_pr hF).cast (by omega) (by omega)
      have t2 : CD_Sm h i j X adm (n + 1 + 1) (S + q + 1) (S : ℝ)
          (fun w => A w * dWbar F w) :=
        (hF2.mul_atm hA).cast (by omega) (by omega)
      refine ((t1.add t2).mono ?_).congr (fun w => ?_)
      · push_cast; linarith
      · exact ((dW_mul (hAd w) (hFd w)).2).symm

/-- The Wirtinger derivative of the zero function. -/
private lemma CD_dW_zero : dW (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
  funext w; simp [dW]

/-- The conjugate Wirtinger derivative of the zero function. -/
private lemma CD_dWbar_zero : dWbar (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
  funext w; simp [dWbar]

/-- One Wirtinger derivative takes a combination of `n` entries of total length `S` to a
combination of `n + 1` entries of total length `S + 1`, with the coefficient mass multiplied by
at most `S`. -/
private lemma CD_Sm.der (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (hone : ∀ f ∈ adm, ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) ∈ adm)
    (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X) {n S : ℕ} {K : ℝ} {F : ℂ → ℂ}
    (hF : CD_Sm h i j X adm n S K F) :
    CD_Sm h i j X adm (n + 1) (S + 1) (K * S) (dW F) ∧
      CD_Sm h i j X adm (n + 1) (S + 1) (K * S) (dWbar F) := by
  induction hF with
  | zero =>
    rw [CD_dW_zero, CD_dWbar_zero]
    exact ⟨CD_Sm.zero.mono (by simp), CD_Sm.zero.mono (by simp)⟩
  | pr hP =>
    obtain ⟨h1, h2⟩ := hP.der hh hadm hone hX
    exact ⟨h1.mono (by simp), h2.mono (by simp)⟩
  | @add K K' F G hF hG ih1 ih2 =>
    obtain ⟨a1, a2⟩ := ih1
    obtain ⟨b1, b2⟩ := ih2
    have hFd := hF.diff hh hadm
    have hGd := hG.diff hh hadm
    constructor
    · have t := a1.add b1
      refine (t.mono (le_of_eq (by ring))).congr (fun w => ?_)
      exact (CD_dW_add (hFd w) (hGd w)).symm
    · have t := a2.add b2
      refine (t.mono (le_of_eq (by ring))).congr (fun w => ?_)
      exact (CD_dWbar_add (hFd w) (hGd w)).symm
  | @smul K F c hF ih =>
    obtain ⟨a1, a2⟩ := ih
    have hFd := hF.diff hh hadm
    constructor
    · refine ((a1.smul c).mono (le_of_eq (by ring))).congr (fun w => ?_)
      exact (CD_dW_const_mul c (hFd w)).symm
    · refine ((a2.smul c).mono (le_of_eq (by ring))).congr (fun w => ?_)
      exact (CD_dWbar_const_mul c (hFd w)).symm
  | @mono K K' F hK hF ih =>
    obtain ⟨a1, a2⟩ := ih
    have hS : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    exact ⟨a1.mono (mul_le_mul_of_nonneg_right hK hS),
      a2.mono (mul_le_mul_of_nonneg_right hK hS)⟩
  | @congr K F G hFG hF ih =>
    have e : F = G := funext hFG
    subst e
    exact ih


/-- Iterating one of the derivatives `b ≤ ν` times. -/
private lemma CD_Sm.iter (op : (ℂ → ℂ) → (ℂ → ℂ))
    (hop : ∀ {n S : ℕ} {K : ℝ} {F : ℂ → ℂ}, CD_Sm h i j X adm n S K F →
      CD_Sm h i j X adm (n + 1) (S + 1) (K * S) (op F))
    {n S : ℕ} {K : ℝ} {F : ℂ → ℂ} (hF : CD_Sm h i j X adm n S K F) (ν : ℕ) :
    ∀ b ≤ ν, CD_Sm h i j X adm (n + b) (S + b) (K * ((S + ν : ℕ) : ℝ) ^ b) (op^[b] F) := by
  intro b
  induction b with
  | zero =>
    intro _
    simpa using hF
  | succ b ih =>
    intro hb
    have t := hop (ih (by omega))
    rw [Function.iterate_succ_apply']
    refine t.mono ?_
    have hK := hF.nonneg
    have hx : (0 : ℝ) ≤ ((S + ν : ℕ) : ℝ) := Nat.cast_nonneg _
    have hSb : ((S + b : ℕ) : ℝ) ≤ ((S + ν : ℕ) : ℝ) := by
      exact_mod_cast (by omega : S + b ≤ S + ν)
    have h1 : (0 : ℝ) ≤ K * ((S + ν : ℕ) : ℝ) ^ b := mul_nonneg hK (pow_nonneg hx _)
    calc K * ((S + ν : ℕ) : ℝ) ^ b * ((S + b : ℕ) : ℝ)
        ≤ K * ((S + ν : ℕ) : ℝ) ^ b * ((S + ν : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hSb h1
      _ = K * ((S + ν : ℕ) : ℝ) ^ (b + 1) := by rw [pow_succ]; ring

/-- `∂_w^a ∂_{w̄}^b` of a combination of `n` entries of total length `S`. -/
private lemma CD_Sm.wirt (hh : (Matrix.of h).IsHermitian)
    (hadm : ∀ f ∈ adm, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (hone : ∀ f ∈ adm, ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) ∈ adm)
    (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X) {n S : ℕ} {K : ℝ} {F : ℂ → ℂ}
    (hF : CD_Sm h i j X adm n S K F) (a b : ℕ) :
    CD_Sm h i j X adm (n + b + a) (S + b + a) (K * ((S + a + b : ℕ) : ℝ) ^ (a + b))
      (wirt a b F) := by
  have s1 := CD_Sm.iter dWbar (fun hG => (hG.der hh hadm hone hX).2) hF (a + b) b
    (by omega)
  have s2 := CD_Sm.iter dW (fun hG => (hG.der hh hadm hone hX).1) s1 a a le_rfl
  refine s2.mono (le_of_eq ?_)
  have e1 : S + (a + b) = S + a + b := by omega
  have e2 : S + b + a = S + a + b := by omega
  rw [e1, e2, pow_add]
  ring


/-- The bound on a product of `n` admissible entries of total length `S ≤ n + p`, from the bounds
`Γ q` on single entries of length `q ≤ p + 1` and `Γ a Γ b ≤ Γ 1 Γ (a + b - 1)`. -/
private lemma CD_Pr.bound (Γ : ℕ → ℝ)
    (hΓ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Γ a * Γ b ≤ Γ 1 * Γ (a + b - 1)) (p : ℕ) (w : ℂ)
    (hnn : ∀ q, 1 ≤ q → q ≤ p + 1 → 0 ≤ Γ q)
    (hat : ∀ q A, CD_Atm h i j X adm q A → q ≤ p + 1 → ‖A w‖ ≤ Γ q)
    {n S : ℕ} {F : ℂ → ℂ} (hF : CD_Pr h i j X adm n S F) (hS : S ≤ n + p) :
    ‖F w‖ ≤ Γ 1 ^ (n - 1) * Γ (S + 1 - n) := by
  induction hF with
  | @single q F hA =>
    have hq : 1 ≤ q := by obtain ⟨_, _, _, _, _, _, _, hq, _⟩ := hA; exact hq
    have := hat q F hA (by omega)
    simpa using this
  | @cons n S q A F hA hF ih =>
    have hq : 1 ≤ q := by obtain ⟨_, _, _, _, _, _, _, hq, _⟩ := hA; exact hq
    have hn := hF.pos
    have hnS := hF.le
    have ih' := ih (by omega)
    have hAw := hat q A hA (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : (0 : ℝ) ≤ Γ 1 ^ m := pow_nonneg (hnn 1 le_rfl (by omega)) _
    have hq0 : 0 ≤ Γ q := hnn q hq (by omega)
    have hr := hΓ q (S + 1 - (m + 1)) hq (by omega)
    simp only [Nat.add_sub_cancel] at ih' ⊢
    rw [norm_mul]
    calc ‖A w‖ * ‖F w‖ ≤ Γ q * (Γ 1 ^ m * Γ (S + 1 - (m + 1))) :=
          mul_le_mul hAw ih' (norm_nonneg _) hq0
      _ = Γ 1 ^ m * (Γ q * Γ (S + 1 - (m + 1))) := by ring
      _ ≤ Γ 1 ^ m * (Γ 1 * Γ (q + (S + 1 - (m + 1)) - 1)) := mul_le_mul_of_nonneg_left hr h1
      _ = Γ 1 ^ (m + 1) * Γ (S + q + 1 - (m + 1 + 1)) := by
          rw [pow_succ]
          have e : q + (S + 1 - (m + 1)) - 1 = S + q + 1 - (m + 1 + 1) := by omega
          rw [e]; ring

private lemma CD_Sm.bound (Γ : ℕ → ℝ)
    (hΓ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Γ a * Γ b ≤ Γ 1 * Γ (a + b - 1)) (p : ℕ) (w : ℂ)
    (hnn : ∀ q, 1 ≤ q → q ≤ p + 1 → 0 ≤ Γ q)
    (hat : ∀ q A, CD_Atm h i j X adm q A → q ≤ p + 1 → ‖A w‖ ≤ Γ q)
    {n S : ℕ} {K : ℝ} {F : ℂ → ℂ} (hF : CD_Sm h i j X adm n S K F) (h2 : n ≤ S)
    (hS : S ≤ n + p) : ‖F w‖ ≤ K * (Γ 1 ^ (n - 1) * Γ (S + 1 - n)) := by
  have hX : 0 ≤ Γ 1 ^ (n - 1) * Γ (S + 1 - n) :=
    mul_nonneg (pow_nonneg (hnn 1 le_rfl (by omega)) _) (hnn _ (by omega) (by omega))
  induction hF with
  | zero => simp
  | pr hP => simpa using hP.bound Γ hΓ p w hnn hat hS
  | add _ _ ih1 ih2 =>
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ _ := by linarith [ih1, ih2]
  | smul c _ ih =>
    rw [norm_mul]
    calc ‖c‖ * ‖_‖ ≤ ‖c‖ * (_ * (Γ 1 ^ (n - 1) * Γ (S + 1 - n))) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = _ := by ring
  | mono hK _ ih => exact ih.trans (mul_le_mul_of_nonneg_right hK hX)
  | congr hFG _ ih => rw [← hFG]; exact ih

end Calculus


/-- The factors of `l`, and the factors `(1, Λ, ξ)` for the pairs `(Λ, ξ)` of `l`. -/
private def CD_adm {D N : ℕ} (l : List (CD_T D N)) : Set (CD_T D N) :=
  {f | f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)}

/-- Every factor of `l` is admissible. -/
private lemma CD_adm_sub {D N : ℕ} (l : List (CD_T D N)) : ∀ f ∈ l, f ∈ CD_adm l :=
  fun _ hf => Or.inl hf

/-- Admissible factors have a Hermitian deformation and a spectral parameter off the real axis. -/
private lemma CD_adm_herm {D N : ℕ} {l : List (CD_T D N)}
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) :
    ∀ f ∈ CD_adm l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  rcases hf with hf | ⟨_, g, hg, hgf⟩
  · exact hl f hf
  · have := hl g hg
    rw [← hgf]; exact this

/-- Replacing the matrix factor of an admissible factor by `1` gives an admissible factor. -/
private lemma CD_adm_one {D N : ℕ} (l : List (CD_T D N)) :
    ∀ f ∈ CD_adm l, ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) ∈ CD_adm l := by
  intro f hf
  rcases hf with hf | ⟨_, g, hg, hgf⟩
  · exact Or.inr ⟨rfl, f, hf, rfl⟩
  · exact Or.inr ⟨rfl, g, hg, hgf⟩

/-- The hypotheses of the derivative bounds: `Γ q ≥ 0` for `1 ≤ q ≤ p + 1`, and the bound `Γ q`
on every admissible entry of length `q ≤ p + 1` at `w`. -/
private lemma CD_hyps {D N : ℕ} (l : List (CD_T D N)) (hl0 : 1 ≤ l.length)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w : ℂ) (Γ : ℕ → ℝ)
    (X : Set (Idx D N → ℂ)) (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X)
    (hG : ∀ l' : List (CD_T D N), 1 ≤ l'.length → l'.length ≤ l.length + 1 →
      (∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) →
      ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB (setEntry h i j w) l' *ᵥ y)‖ ≤ Γ l'.length) :
    (∀ q, 1 ≤ q → q ≤ l.length + 1 → 0 ≤ Γ q) ∧
    (∀ q A, CD_Atm h i j X (CD_adm l) q A → q ≤ l.length + 1 → ‖A w‖ ≤ Γ q) := by
  constructor
  · intro q hq hqp
    obtain ⟨g, hg⟩ : ∃ g, g ∈ l := List.length_pos_iff_exists_mem.mp hl0
    have := hG (List.replicate q ((1 : Matrix (Idx D N) (Idx D N) ℂ), g.2)) (by simpa using hq)
      (by simpa using hqp)
      (fun f hf => Or.inr ⟨(List.eq_of_mem_replicate hf) ▸ rfl, g, hg,
        (List.eq_of_mem_replicate hf) ▸ rfl⟩) _ hX.1 _ hX.1
    simp only [List.length_replicate] at this
    exact (norm_nonneg _).trans this
  · rintro q A ⟨x, hx, y, hy, l', hl', hlen, hq, rfl⟩ hqp
    have := hG l' (by omega) (by omega) hl' x hx y hy
    rw [hlen] at this
    exact this




/-- Wirtinger derivatives of order `(a, b)` of a chain entry `x^* B₁G₁⋯B_pG_p y` along a
Hermitian slice: if every chain `l'` of length `q ≤ p + 1` built from the factors of `l` (each
`B_r` possibly replaced by `1`) has entries `≤ Γ q` between the vectors of `X ∋ e_i, e_j` at the
point, and `Γ a Γ b ≤ Γ 1 Γ (a + b - 1)`, then the derivative is at most
`(p + a + b)^{a+b} Γ₁^{a+b} Γ_p` there. -/
theorem chainB_wirt_le {D N : ℕ}
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl0 : 1 ≤ l.length) (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (Γ : ℕ → ℝ) (hΓ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Γ a * Γ b ≤ Γ 1 * Γ (a + b - 1))
    (X : Set (Idx D N → ℂ)) (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X)
    (hG : ∀ l' : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      1 ≤ l'.length → l'.length ≤ l.length + 1 →
      (∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) →
      ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB (setEntry h i j w) l' *ᵥ y)‖ ≤ Γ l'.length)
    (a b : ℕ) :
    ∀ x ∈ X, ∀ y ∈ X,
      ‖wirt a b (fun w' => star x ⬝ᵥ (chainB (setEntry h i j w') l *ᵥ y)) w‖ ≤
        ((l.length + a + b : ℕ) : ℝ) ^ (a + b) * Γ 1 ^ (a + b) * Γ l.length := by
  intro x hx y hy
  obtain ⟨hnn, hat⟩ := CD_hyps l hl0 h i j w Γ X hX hG
  have hadm := CD_adm_herm hl
  have hone := CD_adm_one l
  have h0 : CD_Sm h i j X (CD_adm l) 1 l.length 1 (CD_atom h i j x y l) :=
    CD_Sm.pr (CD_Pr.single ⟨x, hx, y, hy, l, CD_adm_sub l, rfl, hl0, rfl⟩)
  have hS := h0.wirt hh hadm hone hX a b
  have hb := hS.bound Γ hΓ l.length w hnn hat (by omega) (by omega)
  have e1 : 1 + b + a - 1 = a + b := by omega
  have e2 : l.length + b + a + 1 - (1 + b + a) = l.length := by omega
  rw [e1, e2] at hb
  calc ‖wirt a b (fun w' => star x ⬝ᵥ (chainB (setEntry h i j w') l *ᵥ y)) w‖
      ≤ 1 * ((l.length + a + b : ℕ) : ℝ) ^ (a + b) * (Γ 1 ^ (a + b) * Γ l.length) := hb
    _ = _ := by ring


/-- A loop is the normalized sum of the diagonal entries of the chain. -/
private lemma CD_ntr_eq {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (l : List (CD_T D N)) :
    (fun w => ntr (chainB (setEntry h i j w) l)) = fun w =>
      ((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ *
        ∑ k, CD_atom h i j (Pi.single k 1) (Pi.single k 1) l w := by
  funext w
  simp [ntr, Matrix.trace, CD_atom_diag]

/-- The first derivatives of a loop. -/
private lemma CD_loop_der {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (l : List (CD_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) :
    (dW (fun w => ntr (chainB (setEntry h i j w) l)) = fun w =>
      ((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ * (-(if i = j then 1 / 2 else 1) *
        ∑ r : Fin l.length, CD_atom h i j (Pi.single j 1) (Pi.single i 1)
          (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1)) w)) ∧
    (dWbar (fun w => ntr (chainB (setEntry h i j w) l)) = fun w =>
      ((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ * (-(if i = j then 1 / 2 else 1) *
        ∑ r : Fin l.length, CD_atom h i j (Pi.single i 1) (Pi.single j 1)
          (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1)) w)) := by
  have hdk : ∀ k, Differentiable ℝ (CD_atom h i j (Pi.single k 1) (Pi.single k 1) l) :=
    fun k => CD_atom_diff h hh i j l hl _ _
  have hrot : ∀ (r : Fin l.length) (u v : Idx D N) (w : ℂ),
      ∑ k, chainB (setEntry h i j w) (l.take (r + 1)) k v *
        chainB (setEntry h i j w) ((1, (l.get r).2) :: l.drop (r + 1)) u k =
      CD_atom h i j (Pi.single u 1) (Pi.single v 1)
        (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1)) w := by
    intro r u v w
    rw [CD_atom_diag, CD_chainB_append, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [CD_ntr_eq]
  constructor
  · funext w
    rw [CD_dW_const_mul _ ((Differentiable.fun_sum fun k _ => hdk k) w),
      CD_dW_sum Finset.univ (fun k w => CD_atom h i j (Pi.single k 1) (Pi.single k 1) l w)
        (fun k _ => hdk k w)]
    congr 1
    have hd : ∀ k, dW (CD_atom h i j (Pi.single k 1) (Pi.single k 1) l) w =
        -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
          chainB (setEntry h i j w) (l.take (r + 1)) k i *
            chainB (setEntry h i j w) ((1, (l.get r).2) :: l.drop (r + 1)) j k := by
      intro k
      rw [(CD_atom_der h hh i j l hl _ _).1]
      simp only [CD_atom_diag]
    simp only [hd]
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine congrArg (HMul.hMul _) ?_
    exact Finset.sum_congr rfl fun r _ => hrot r j i w
  · funext w
    rw [CD_dWbar_const_mul _ ((Differentiable.fun_sum fun k _ => hdk k) w),
      CD_dWbar_sum Finset.univ (fun k w => CD_atom h i j (Pi.single k 1) (Pi.single k 1) l w)
        (fun k _ => hdk k w)]
    congr 1
    have hd : ∀ k, dWbar (CD_atom h i j (Pi.single k 1) (Pi.single k 1) l) w =
        -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
          chainB (setEntry h i j w) (l.take (r + 1)) k j *
            chainB (setEntry h i j w) ((1, (l.get r).2) :: l.drop (r + 1)) i k := by
      intro k
      rw [(CD_atom_der h hh i j l hl _ _).2]
      simp only [CD_atom_diag]
    simp only [hd]
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine congrArg (HMul.hMul _) ?_
    exact Finset.sum_congr rfl fun r _ => hrot r i j w


/-- The first derivatives of a loop are combinations of single entries of length `p + 1`. -/
private lemma CD_loop_Sm {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (X : Set (Idx D N → ℂ)) (l : List (CD_T D N)) (u v : Idx D N → ℂ) (hu : u ∈ X) (hv : v ∈ X) :
    CD_Sm h i j X (CD_adm l) 1 (l.length + 1) (l.length : ℝ) (fun w =>
      -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length, CD_atom h i j u v
        (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1)) w) := by
  have hat : ∀ r : Fin l.length, CD_Atm h i j X (CD_adm l) (l.length + 1)
      (CD_atom h i j u v (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1))) := by
    intro r
    have hr := r.isLt
    refine ⟨u, hu, v, hv, _, ?_, ?_, by omega, rfl⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact CD_adm_one l _ (CD_adm_sub l _ (List.get_mem _ _))
        · exact CD_adm_sub l f (List.mem_of_mem_drop hf)
      · exact CD_adm_sub l f (List.mem_of_mem_take hf)
    · simp only [List.length_append, List.length_cons, List.length_drop, List.length_take]
      omega
  have hs := CD_Sm.sum (h := h) (i := i) (j := j) (X := X) (adm := CD_adm l) (n := 1)
    (S := l.length + 1) (K := 1) (Finset.univ : Finset (Fin l.length))
    (fun (r : Fin l.length) w => CD_atom h i j u v
      (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1)) w)
    (fun r _ => CD_Sm.pr (CD_Pr.single (hat r)))
  have hs2 := hs.smul (-(if i = j then (1 / 2 : ℂ) else 1))
  refine hs2.mono ?_
  have hc : ‖-(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs <;> norm_num
  rw [Finset.card_univ, Fintype.card_fin]
  have : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
  nlinarith


/-- Wirtinger derivatives of order `(a, b)`, `a + b ≥ 1`, of a loop `⟨B₁G₁⋯B_pG_p⟩` along a
Hermitian slice, under the hypotheses of `chainB_wirt_le`: at most
`(p + a + b)^{a+b} (DN)⁻¹ Γ₁^{a+b-1} Γ_{p+1}` (the bound `|∂^{(a,b)} loop| ≲ N⁻¹ max Π Γ` used
with Lemma 2.11 [lem:complex_cumu]). -/
theorem loopB_wirt_le {D N : ℕ}
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl0 : 1 ≤ l.length) (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (Γ : ℕ → ℝ) (hΓ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Γ a * Γ b ≤ Γ 1 * Γ (a + b - 1))
    (X : Set (Idx D N → ℂ)) (hX : Pi.single i 1 ∈ X ∧ Pi.single j 1 ∈ X)
    (hG : ∀ l' : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      1 ≤ l'.length → l'.length ≤ l.length + 1 →
      (∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) →
      ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB (setEntry h i j w) l' *ᵥ y)‖ ≤ Γ l'.length)
    (a b : ℕ) (hab : 1 ≤ a + b) :
    ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') l)) w‖ ≤
      ((l.length + a + b : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) * N)⁻¹ * Γ 1 ^ (a + b - 1) *
        Γ (l.length + 1) := by
  obtain ⟨hnn, hat⟩ := CD_hyps l hl0 h i j w Γ X hX hG
  have hadm := CD_adm_herm hl
  have hone := CD_adm_one l
  obtain ⟨hd1, hd2⟩ := CD_loop_der h hh i j l hl
  have hκ : ‖((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    simp [Fintype.card_prod]
  have hΓ1 : 0 ≤ Γ 1 := hnn 1 le_rfl (by omega)
  have hΓp : 0 ≤ Γ (l.length + 1) := hnn _ (by omega) le_rfl
  have key : ∀ (a' b' : ℕ) (F1 : ℂ → ℂ),
      CD_Sm h i j X (CD_adm l) 1 (l.length + 1) (((D : ℝ) * N)⁻¹ * l.length) F1 →
      a' + b' + 1 = a + b →
      wirt a b (fun w' => ntr (chainB (setEntry h i j w') l)) = wirt a' b' F1 →
      ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') l)) w‖ ≤
        ((l.length + a + b : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) * N)⁻¹ * Γ 1 ^ (a + b - 1) *
          Γ (l.length + 1) := by
    intro a' b' F1 hF1 hab' hw
    rw [hw]
    have hS := hF1.wirt hh hadm hone hX a' b'
    have hb := hS.bound Γ hΓ l.length w hnn hat (by omega) (by omega)
    have e1 : 1 + b' + a' - 1 = a' + b' := by omega
    have e2 : l.length + 1 + b' + a' + 1 - (1 + b' + a') = l.length + 1 := by omega
    have e3 : l.length + 1 + a' + b' = l.length + a + b := by omega
    have e4 : a + b - 1 = a' + b' := by omega
    have e5 : a + b = a' + b' + 1 := by omega
    rw [e1, e2, e3] at hb
    rw [e4, e5]
    set P : ℝ := ((l.length + a + b : ℕ) : ℝ) with hP
    have hp : (l.length : ℝ) ≤ P := by
      rw [hP]; exact_mod_cast (by omega : l.length ≤ l.length + a + b)
    have hP0 : 0 ≤ P := le_trans (Nat.cast_nonneg _) hp
    have hY : 0 ≤ ((D : ℝ) * N)⁻¹ * P ^ (a' + b') * (Γ 1 ^ (a' + b') * Γ (l.length + 1)) := by
      have : 0 ≤ ((D : ℝ) * N)⁻¹ := by rw [← hκ]; exact norm_nonneg _
      positivity
    calc _ ≤ _ := hb
      _ = (l.length : ℝ) * (((D : ℝ) * N)⁻¹ * P ^ (a' + b') *
          (Γ 1 ^ (a' + b') * Γ (l.length + 1))) := by ring
      _ ≤ P * (((D : ℝ) * N)⁻¹ * P ^ (a' + b') *
          (Γ 1 ^ (a' + b') * Γ (l.length + 1))) := mul_le_mul_of_nonneg_right hp hY
      _ = _ := by rw [pow_succ]; ring
  have hF1 : ∀ F1 : ℂ → ℂ, ∀ u v : Idx D N → ℂ, u ∈ X → v ∈ X →
      F1 = (fun w => ((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ * (-(if i = j then 1 / 2 else 1) *
        ∑ r : Fin l.length, CD_atom h i j u v
          (((1, (l.get r).2) :: l.drop (r + 1)) ++ l.take (r + 1)) w)) →
      CD_Sm h i j X (CD_adm l) 1 (l.length + 1) (((D : ℝ) * N)⁻¹ * l.length) F1 := by
    intro F1 u v hu hv hF
    rw [hF, ← hκ]
    exact (CD_loop_Sm h i j X l u v hu hv).smul _
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · subst hb0
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact key a' 0 _ (hF1 _ _ _ hX.2 hX.1 hd1) (by omega) rfl
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact key a b' _ (hF1 _ _ _ hX.1 hX.2 hd2) (by omega) rfl


/-- The operator norm of the conjugate transpose. -/
private lemma CD_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

/-- `Σ_r |(A u)_r|² ≤ ‖A‖² Σ_r |u_r|²`. -/
private lemma CD_sq_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (u : ι → ℂ) : ∑ r, ‖(A *ᵥ u) r‖ ^ 2 ≤ opNorm A ^ 2 * ∑ r, ‖u r‖ ^ 2 := by
  have h1 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 u)‖ ≤
      opNorm A * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 u)‖ ^ 2 =
      ∑ r, ‖(A *ᵥ u) r‖ ^ 2 := by
    rw [Matrix.toEuclideanCLM_toLp, PiLp.norm_sq_eq_of_L2]
  have h3 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ r, ‖u r‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  rw [← h2, ← h3, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2


/-- The vector `‖B‖⁻¹ Bᴴ u`, of norm at most `1` for a unit `u`. -/
private def CD_nv {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (u : Idx D N → ℂ) :
    Idx D N → ℂ :=
  ((opNorm B : ℝ) : ℂ)⁻¹ • (Bᴴ *ᵥ u)

/-- The vector `CD_nv B u` has squared norm at most `1` when `u` does. -/
private lemma CD_nv_norm {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (u : Idx D N → ℂ)
    (hu : ∑ r, ‖u r‖ ^ 2 ≤ 1) : ∑ r, ‖CD_nv B u r‖ ^ 2 ≤ 1 := by
  have hβ : 0 ≤ opNorm B := norm_nonneg _
  have hsq := CD_sq_mulVec_le Bᴴ u
  rw [CD_opNorm_conjTranspose] at hsq
  have e : ∀ r, ‖CD_nv B u r‖ ^ 2 = ((opNorm B)⁻¹) ^ 2 * ‖(Bᴴ *ᵥ u) r‖ ^ 2 := by
    intro r
    simp [CD_nv, mul_pow, abs_of_nonneg hβ]
  simp only [e, ← Finset.mul_sum]
  rcases hβ.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · calc ((opNorm B)⁻¹) ^ 2 * ∑ r, ‖(Bᴴ *ᵥ u) r‖ ^ 2
        ≤ ((opNorm B)⁻¹) ^ 2 * (opNorm B ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left (hsq.trans (by gcongr)) (by positivity)
      _ = 1 := by field_simp

/-- `‖B‖ · CD_nv B u = Bᴴ u`. -/
private lemma CD_nv_smul {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (u : Idx D N → ℂ) :
    ((opNorm B : ℝ) : ℂ) • CD_nv B u = Bᴴ *ᵥ u := by
  by_cases h0 : opNorm B = 0
  · have hsq := CD_sq_mulVec_le Bᴴ u
    rw [CD_opNorm_conjTranspose, h0] at hsq
    have hz : ∀ r, (Bᴴ *ᵥ u) r = 0 := by
      intro r
      have hs : ∑ r, ‖(Bᴴ *ᵥ u) r‖ ^ 2 ≤ 0 := by simpa using hsq
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp
        (le_antisymm hs (Finset.sum_nonneg fun _ _ => by positivity)) r (Finset.mem_univ r)
      simpa using h1
    ext r
    simp [CD_nv, h0, hz r]
  · unfold CD_nv
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr h0), one_smul]

/-- `x^* (B z) = (Bᴴ x)^* z`. -/
private lemma CD_form {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (x z : Idx D N → ℂ) :
    star x ⬝ᵥ (B *ᵥ z) = star (Bᴴ *ᵥ x) ⬝ᵥ z := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

/-- `x^* (B z) = ‖B‖ (CD_nv B x)^* z`. -/
private lemma CD_form_nv {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (x z : Idx D N → ℂ) :
    star x ⬝ᵥ (B *ᵥ z) = ((opNorm B : ℝ) : ℂ) * (star (CD_nv B x) ⬝ᵥ z) := by
  rw [CD_form, ← CD_nv_smul B x, star_smul, smul_dotProduct]
  simp


/-- The unit vectors `e_k`. -/
private def CD_E (D N : ℕ) : Finset (Idx D N → ℂ) :=
  Finset.univ.image fun k : Idx D N => Pi.single k 1

/-- The vectors `‖B‖⁻¹ Bᴴ e_k` over the factors `(B, Λ, ξ)` of `t`. -/
private def CD_Vt {D N : ℕ} (t : List (CD_T D N)) : Finset (Idx D N → ℂ) :=
  t.toFinset.biUnion fun f => Finset.univ.image fun k : Idx D N => CD_nv f.1 (Pi.single k 1)

/-- The set of vectors of the resolvent polynomial of `x^* B₁G₁ ⋯ y` with `(B₁, …) = a :: t`. -/
private def CD_V {D N : ℕ} (a : CD_T D N) (t : List (CD_T D N)) (x y : Idx D N → ℂ) :
    Finset (Idx D N → ℂ) :=
  insert (CD_nv a.1 x) (insert y (CD_E D N ∪ CD_Vt t))

/-- The index set has `D N` elements. -/
private lemma CD_card_idx (D N : ℕ) : (Finset.univ : Finset (Idx D N)).card = D * N := by
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- At most `D N` unit vectors. -/
private lemma CD_E_card (D N : ℕ) : (CD_E D N).card ≤ D * N :=
  Finset.card_image_le.trans (CD_card_idx D N).le

/-- At most `|t| D N` vectors `‖B‖⁻¹ Bᴴ e_k` over the factors of `t`. -/
private lemma CD_Vt_card {D N : ℕ} (t : List (CD_T D N)) : (CD_Vt t).card ≤ t.length * (D * N) := by
  unfold CD_Vt
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ f ∈ t.toFinset, (Finset.univ.image fun k : Idx D N => CD_nv f.1 (Pi.single k 1)).card
      ≤ ∑ _f ∈ t.toFinset, D * N :=
        Finset.sum_le_sum fun f _ => Finset.card_image_le.trans (CD_card_idx D N).le
    _ = t.toFinset.card * (D * N) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ t.length * (D * N) := Nat.mul_le_mul_right _ (List.toFinset_card_le t)

/-- The vector set has at most `(|t| + 1) D N + 2` elements. -/
private lemma CD_V_card {D N : ℕ} (a : CD_T D N) (t : List (CD_T D N)) (x y : Idx D N → ℂ) :
    (CD_V a t x y).card ≤ (t.length + 1) * (D * N) + 2 := by
  have h1 := Finset.card_insert_le (CD_nv a.1 x) (insert y (CD_E D N ∪ CD_Vt t))
  have h2 := Finset.card_insert_le y (CD_E D N ∪ CD_Vt t)
  have h3 := Finset.card_union_le (CD_E D N) (CD_Vt t)
  have h4 := CD_E_card D N
  have h5 := CD_Vt_card t
  have h6 : (t.length + 1) * (D * N) = t.length * (D * N) + D * N := by ring
  unfold CD_V
  omega

/-- A unit vector has squared norm `1`. -/
private lemma CD_single_norm {D N : ℕ} (k : Idx D N) :
    ∑ r, ‖(Pi.single k (1 : ℂ) : Idx D N → ℂ) r‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

/-- All vectors of the vector set have squared norm at most `1`. -/
private lemma CD_V_norm {D N : ℕ} (a : CD_T D N) (t : List (CD_T D N)) (x y : Idx D N → ℂ)
    (hx : ∑ r, ‖x r‖ ^ 2 ≤ 1) (hy : ∑ r, ‖y r‖ ^ 2 ≤ 1) :
    ∀ v ∈ CD_V a t x y, ∑ r, ‖v r‖ ^ 2 ≤ 1 := by
  intro v hv
  unfold CD_V at hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact CD_nv_norm _ _ hx
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact hy
  rcases Finset.mem_union.mp hv with hv | hv
  · unfold CD_E at hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
    exact (CD_single_norm k).le
  · unfold CD_Vt at hv
    obtain ⟨f, _, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
    exact CD_nv_norm _ _ (CD_single_norm k).le

/-- The vector set of the tail of a chain, started at a unit vector, lies in the vector set of the
chain. -/
private lemma CD_V_mono {D N : ℕ} (a b : CD_T D N) (t : List (CD_T D N)) (x y : Idx D N → ℂ)
    (k : Idx D N) : CD_V b t (Pi.single k 1) y ⊆ CD_V a (b :: t) x y := by
  intro v hv
  unfold CD_V at hv ⊢
  refine Finset.mem_insert_of_mem ?_
  rcases Finset.mem_insert.mp hv with rfl | hv
  · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
    unfold CD_Vt
    exact Finset.mem_biUnion.mpr ⟨b, by simp, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem ?_
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ hv
    · refine Finset.mem_union_right _ ?_
      unfold CD_Vt at hv ⊢
      obtain ⟨f, hf, hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨f,
        List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hf)), hv⟩


/-- Insertion of `Σ_k e_k e_kᴴ = 1` after a matrix factor. -/
private lemma CD_expand {D N : ℕ} (G : Matrix (Idx D N) (Idx D N) ℂ) (u w : Idx D N → ℂ) :
    star u ⬝ᵥ (G *ᵥ w) = ∑ k, (star u ⬝ᵥ (G *ᵥ Pi.single k 1)) * w k := by
  conv_lhs => rw [pi_eq_sum_univ' w]
  simp only [Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul, dotProduct_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The value of a resolvent polynomial whose monomials all start with the factor `F`. -/
private lemma CD_prepend_eval {D N : ℕ} (c : ℂ) (F : ResFactor D N) (Q : ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (Q.map fun s => (c * s.1, F :: s.2)) h =
      c * resFactorEval F h * resPolyEval Q h := by
  induction Q with
  | nil => simp [resPolyEval]
  | cons s Q ih =>
    simp only [List.map_cons, resPolyEval, List.sum_cons, resMonoEval, List.prod_cons] at ih ⊢
    rw [ih]
    ring

/-- The value of a concatenation of resolvent polynomials is the sum of their values. -/
private lemma CD_flatMap_eval {D N : ℕ} {ι : Type*} (L : List ι) (f : ι → ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (L.flatMap f) h = (L.map fun k => resPolyEval (f k) h).sum := by
  induction L with
  | nil => simp [resPolyEval]
  | cons k L ih => rw [List.flatMap_cons, resPolyEval_append, ih, List.map_cons, List.sum_cons]

/-- The total modulus of the coefficients of a resolvent polynomial. -/
private def CD_coef {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun s => ‖s.1‖).sum

/-- The coefficient mass of a concatenation is the sum of the coefficient masses. -/
private lemma CD_coef_flatMap {D N : ℕ} {ι : Type*} (L : List ι) (f : ι → ResPoly D N) :
    CD_coef (L.flatMap f) = (L.map fun k => CD_coef (f k)).sum := by
  induction L with
  | nil => simp [CD_coef]
  | cons k L ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp [CD_coef, List.map_append, List.sum_append]

/-- Prepending a factor to every monomial and scaling by `c` scales the coefficient mass by
`‖c‖`. -/
private lemma CD_coef_prepend {D N : ℕ} (c : ℂ) (F : ResFactor D N) (Q : ResPoly D N) :
    CD_coef (Q.map fun s => (c * s.1, F :: s.2)) = ‖c‖ * CD_coef Q := by
  simp only [CD_coef, List.map_map, Function.comp_def, norm_mul]
  rw [List.sum_map_mul_left]


/-- `e_k^* w = w k`. -/
private lemma CD_star_single_dot {D N : ℕ} (k : Idx D N) (w : Idx D N → ℂ) :
    star (Pi.single k (1 : ℂ) : Idx D N → ℂ) ⬝ᵥ w = w k := by
  simp

/-- The resolvent polynomial of `x^* B₁G₁ ⋯ B_pG_p y`: insert `Σ_k e_k e_kᴴ` between the factors. -/
private lemma CD_resPoly_aux {D N : ℕ} : ∀ (t : List (CD_T D N)) (a : CD_T D N)
    (x y : Idx D N → ℂ), ∃ P : ResPoly D N,
      (∀ s ∈ P, s.2.length = t.length + 1 ∧ ∀ f ∈ s.2, f.1 ∈ CD_V a t x y ∧ f.2.1 ∈ CD_V a t x y ∧
        ∃ g ∈ a :: t, f.2.2 = g.2) ∧
      CD_coef P ≤ ((D : ℝ) * N) ^ t.length * ((a :: t).map fun f => opNorm f.1).prod ∧
      ∀ h, resPolyEval P h = star x ⬝ᵥ (chainB h (a :: t) *ᵥ y) := by
  intro t
  induction t with
  | nil =>
    intro a x y
    refine ⟨[(((opNorm a.1 : ℝ) : ℂ), [(CD_nv a.1 x, y, a.2.1, a.2.2)])], ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      refine ⟨by simp, ?_⟩
      intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      refine ⟨?_, ?_, a, by simp, rfl⟩
      · simp [CD_V]
      · simp [CD_V]
    · have hβ : 0 ≤ opNorm a.1 := norm_nonneg _
      simp [CD_coef, abs_of_nonneg hβ]
    · intro h
      simp only [resPolyEval, resMonoEval, resFactorEval, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, chainB, add_zero, mul_one]
      rw [← Matrix.mulVec_mulVec, CD_form_nv a.1 x]
  | cons b t ih =>
    intro a x y
    choose Pk hPk using fun k : Idx D N => ih b (Pi.single k 1) y
    refine ⟨(Finset.univ : Finset (Idx D N)).toList.flatMap fun k => (Pk k).map fun s =>
      (((opNorm a.1 : ℝ) : ℂ) * s.1, (CD_nv a.1 x, Pi.single k 1, a.2.1, a.2.2) :: s.2),
      ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨k, _, hs⟩ := List.mem_flatMap.mp hs
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hlen, hfac⟩ := (hPk k).1 s0 hs0
      refine ⟨by simp [hlen], ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · refine ⟨?_, ?_, a, List.mem_cons_self, rfl⟩
        · unfold CD_V; exact Finset.mem_insert_self _ _
        · unfold CD_V
          refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
          unfold CD_E
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      · obtain ⟨h1, h2, g, hg, hgf⟩ := hfac f hf
        exact ⟨CD_V_mono a b t x y k h1, CD_V_mono a b t x y k h2, g,
          List.mem_cons_of_mem _ hg, hgf⟩
    · rw [CD_coef_flatMap, Finset.sum_map_toList]
      have hbd : ∀ k : Idx D N, CD_coef ((Pk k).map fun s => (((opNorm a.1 : ℝ) : ℂ) * s.1,
          (CD_nv a.1 x, Pi.single k 1, a.2.1, a.2.2) :: s.2)) ≤
          opNorm a.1 * (((D : ℝ) * N) ^ t.length * ((b :: t).map fun f => opNorm f.1).prod) := by
        intro k
        have hβ : 0 ≤ opNorm a.1 := norm_nonneg _
        rw [CD_coef_prepend, Complex.norm_real, Real.norm_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left (hPk k).2.1 hβ
      refine (Finset.sum_le_sum fun k _ => hbd k).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      push_cast
      ring_nf
      exact le_refl _
    · intro h
      rw [CD_flatMap_eval, Finset.sum_map_toList]
      set G := res (Matrix.of h + a.2.1) a.2.2 with hG
      set C := chainB h (b :: t) with hC
      have hk : ∀ k : Idx D N, resPolyEval ((Pk k).map fun s => (((opNorm a.1 : ℝ) : ℂ) * s.1,
          (CD_nv a.1 x, Pi.single k 1, a.2.1, a.2.2) :: s.2)) h =
          ((opNorm a.1 : ℝ) : ℂ) * (star (CD_nv a.1 x) ⬝ᵥ (G *ᵥ Pi.single k 1)) *
            ((C *ᵥ y) k) := by
        intro k
        rw [CD_prepend_eval, (hPk k).2.2 h]
        simp only [resFactorEval, hG, hC]
        rw [CD_star_single_dot]
      have hch : chainB h (a :: b :: t) = (a.1 * G) * C := by
        simp [chainB, hG, hC]
      rw [hch, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, CD_form_nv a.1 x,
        CD_expand G (CD_nv a.1 x) (C *ᵥ y), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hk k]
      ring


/-- A chain entry `x^* B₁G₁⋯B_pG_p y` with `‖x‖, ‖y‖ ≤ 1` is a resolvent polynomial in the form
used with Lemma 2.11 [lem:complex_cumu]: its monomials have `p` factors, with the pairs `(Λ_r, ξ_r)`
of the chain and vectors of norm `≤ 1` from a set of at most `p DN + 2` vectors, and coefficient
sum at most `(DN)^{p-1} Π ‖B_r‖`. -/
theorem chainB_resPoly {D N : ℕ}
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl0 : 1 ≤ l.length) (x y : Idx D N → ℂ) (hx : ∑ r, ‖x r‖ ^ 2 ≤ 1)
    (hy : ∑ r, ‖y r‖ ^ 2 ≤ 1) :
    ∃ (V : Finset (Idx D N → ℂ)) (P : ResPoly D N),
      V.card ≤ l.length * (D * N) + 2 ∧ (∀ v ∈ V, ∑ r, ‖v r‖ ^ 2 ≤ 1) ∧
      (∀ t ∈ P, t.2.length = l.length ∧
        ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧ ∃ g ∈ l, f.2.2 = g.2) ∧
      (P.map fun t => ‖t.1‖).sum ≤
        ((D : ℝ) * N) ^ (l.length - 1) * (l.map fun f => opNorm f.1).prod ∧
      ∀ h : Idx D N → Idx D N → ℂ, resPolyEval P h = star x ⬝ᵥ (chainB h l *ᵥ y) := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := List.exists_cons_of_length_pos hl0
  obtain ⟨P, hP1, hP2, hP3⟩ := CD_resPoly_aux t a x y
  refine ⟨CD_V a t x y, P, ?_, CD_V_norm a t x y hx hy, ?_, ?_, hP3⟩
  · simpa using CD_V_card a t x y
  · intro s hs
    obtain ⟨h1, h2⟩ := hP1 s hs
    exact ⟨by simpa using h1, fun f hf => h2 f hf⟩
  · simpa [CD_coef] using hP2

end RBMTransitionEdge

end
