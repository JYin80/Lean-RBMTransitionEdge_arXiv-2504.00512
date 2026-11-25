module

public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.LocalLaw.MultiRes
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgEval
import all RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.LocalLaw.MultiRes

@[expose] public section

/-!
# The generic bound for the class of the further expansion in the proof of Lemma 5.5

Every well-formed expression `𝓡` of the class of (5.79)–(5.81) satisfies
`𝓡 ≺ N^{-size′₁} η^{-size′₂-2} ‖A‖²` in expectation, uniformly in its entry labels, for slots
satisfying the hypotheses of Lemma A.4 [lemma_necessary_estimates]: the bound before the
termination argument of the further expansion, with `η^{-2}` in place of the two indicators.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ## Facts of the words, the evaluation and Lemma A.4 [lemma_necessary_estimates] -/

open private isEntP isResP isGoodP segOK segsOK wf_iff WfP exists_first_ent findIdx_ent charsP_eq
  nfac from RBMTransitionEdge.Localized.Expansion.PkgWords
open private PE_wm_lw PE_wm_append PE_wm_cons PE_wm_nil PE_lm PE_isEnt PE_wv PE_wt PE_val PE_coef
  PE_evalH from RBMTransitionEdge.Localized.Expansion.PkgEval
open private Bd_isRes Bd_isL Bd_let Bd_wordMat_eq Bd_isL_count Bd_dec Bd_dec_len Bd_dec_mem
  Bd_prod_norm Bd_prod_normL Bd_list_norm Bd_Cl Bd_zc Bd_eta Bd_Cl_mono Bd_unif Bd_facts Bd_G_eq
  Bd_wv Bd_Bv Bd_mat_resWord Bd_bndA4_le Bd_ofFn_smul Bd_cw Bd_cw_ge Bd_cw_mono Bd_loop Bd_weight
  Bd_opNorm_nonneg Bd_ntr_le Bd_opNorm_one Bd_opNorm_E Bd_G_norm Bd_opNorm_sub Bd_zpow_lower
  Bd_large Bd_opNorm_conjTranspose Bd_opNorm_zero Bd_list_prod_pow
  from RBMTransitionEdge.Localized.Expansion.Bound
open private MultiRes_vn MultiRes_vn_sq MultiRes_vn_nonneg MultiRes_vn_smul MultiRes_vn_eq_zero
  MultiRes_vn_mulVec_le from RBMTransitionEdge.LocalLaw.MultiRes

/-- The cyclic segments of a word, as in `PkgExpr.wf`. -/
private def PB_segs (w : List PkgLetter) : List (List PkgLetter) :=
  if w.any isEntP then (w.rotate (w.findIdx isEntP + 1)).dropLast.splitOnP isEntP else [w]

private lemma PB_segOK (w : List PkgLetter) : segOK w = (PB_segs w).all fun v => v.any isGoodP :=
  rfl

/-- The counts along the segments of `splitOnP isEntP`. -/
private lemma PB_split (q : PkgLetter → Bool) (hq : ∀ x, isEntP x = true → q x = false) :
    ∀ l : List PkgLetter, ((l.splitOnP isEntP).map (List.countP q)).sum = l.countP q ∧
      (l.splitOnP isEntP).length = l.countP isEntP + 1 ∧
      (∀ s ∈ l.splitOnP isEntP, ∀ y ∈ s, isEntP y = false) ∧
      ((l.splitOnP isEntP).map List.length).sum ≤ l.length
  | [] => by simp
  | x :: l => by
    obtain ⟨h1, h2, h3, h4⟩ := PB_split q hq l
    rw [List.splitOnP_cons_eq_ite_modifyHead]
    by_cases hx : isEntP x = true
    · simp only [hx, ite_true, List.map_cons, List.sum_cons, List.countP_nil, h1,
        List.countP_cons, hq x hx, List.length_cons, h2, List.length_nil]
      refine ⟨by simp, by simp, fun s hs y hy => ?_, by omega⟩
      rcases List.mem_cons.1 hs with rfl | hs
      · simp at hy
      · exact h3 s hs y hy
    · have hx' : isEntP x = false := by simpa using hx
      obtain ⟨hd, tl, he⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil isEntP l)
      rw [he] at h1 h2 h3 h4
      simp only [hx', Bool.false_eq_true, ite_false, he, List.modifyHead_cons, List.map_cons,
        List.sum_cons, List.countP_cons, List.length_cons] at h1 h2 h4 ⊢
      refine ⟨by omega, by omega, fun s hs y hy => ?_, by omega⟩
      rcases List.mem_cons.1 hs with rfl | hs
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hx'
        · exact h3 _ (List.mem_cons_self) y hy
      · exact h3 s (List.mem_cons_of_mem _ hs) y hy

/-- The segments of `P Δ Q`, `P` free of `Δ`: those of `Q P`. -/
private lemma PB_segs_ent (P Q : List PkgLetter) (u v : ℕ) (hP : ∀ y ∈ P, isEntP y = false) :
    PB_segs (P ++ .ent u v :: Q) = (Q ++ P).splitOnP isEntP := by
  unfold PB_segs
  have h1 : (P ++ .ent u v :: Q).any isEntP = true := by simp [isEntP]
  simp only [h1, ↓reduceIte, findIdx_ent P Q u v hP]
  have h2 : (P ++ .ent u v :: Q).rotate (P.length + 1) = (Q ++ P) ++ [.ent u v] := by
    rw [List.rotate_eq_drop_append_take (by simp)]
    have e0 : P ++ .ent u v :: Q = (P ++ [.ent u v]) ++ Q := by simp
    have e1 : (P ++ .ent u v :: Q).drop (P.length + 1) = Q := by
      rw [e0]; exact List.drop_left' (by simp)
    have e2 : (P ++ .ent u v :: Q).take (P.length + 1) = P ++ [.ent u v] := by
      rw [e0]; exact List.take_left' (by simp)
    rw [e1, e2]; simp
  rw [h2, List.dropLast_concat]

/-- The counts along the cyclic segments of a word. -/
private lemma PB_segs_count (q : PkgLetter → Bool) (hq : ∀ x, isEntP x = true → q x = false)
    (w : List PkgLetter) : ((PB_segs w).map (List.countP q)).sum = w.countP q ∧
      (PB_segs w).length = nfac w ∧ (∀ s ∈ PB_segs w, ∀ y ∈ s, isEntP y = false) ∧
      (∀ s ∈ PB_segs w, s.length ≤ w.length) := by
  by_cases hw : w.any isEntP = true
  · obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent w hw
    rw [PB_segs_ent P Q x y hP]
    obtain ⟨h1, h2, h3, h4⟩ := PB_split q hq (Q ++ P)
    have hent : isEntP (.ent x y) = true := rfl
    refine ⟨?_, ?_, h3, fun s hs => ?_⟩
    · rw [h1]; simp [List.countP_append, hq _ hent]; omega
    · unfold nfac; simp only [hw, ↓reduceIte]; rw [h2]; simp [List.countP_append, hent]
      have : (P.countP isEntP) = 0 := List.countP_eq_zero.2 fun z hz => by simp [hP z hz]
      omega
    · have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hs)
      have h5 : (Q ++ P).length ≤ (P ++ .ent x y :: Q).length := by simp; omega
      omega
  · have hw' : ∀ y ∈ w, isEntP y = false := by simpa using hw
    have e : PB_segs w = [w] := by unfold PB_segs; simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [e]
    refine ⟨by simp, by simp [nfac, hw], fun s hs => ?_, fun s hs => ?_⟩
    · rw [List.mem_singleton] at hs; subst hs; exact hw'
    · rw [List.mem_singleton] at hs; subst hs; exact le_rfl


/-- The loop letters of a list of letters. -/
private def PB_toL (s : List PkgLetter) : List LoopLetter :=
  s.filterMap fun x => match x with | .lw y => some y | .ent _ _ => none

private lemma PB_toL_eq : ∀ s : List PkgLetter, (∀ y ∈ s, isEntP y = false) →
    (PB_toL s).map PkgLetter.lw = s
  | [], _ => rfl
  | .lw y :: s, h => by
    have := PB_toL_eq s fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [PB_toL, List.filterMap_cons] at this ⊢
    simp [this]
  | .ent u v :: s, h => by simp [isEntP] at h

section Mat

variable {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
  (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)

private lemma PB_mat_ent (A B : List PkgLetter) (x y : ℕ) :
    pkgWordMat G M E L κ (A ++ .ent x y :: B) = pkgWordMat G M E L κ A *
      (Matrix.of fun k l => if k = κ x ∧ l = κ y then (1 : ℂ) else 0) * pkgWordMat G M E L κ B := by
  rw [PE_wm_append, PE_wm_cons, Matrix.mul_assoc]
  rfl

/-- The trace of a word `P Δ_{xy} Q` is the entry `(Q P)_{κy κx}`. -/
private lemma PB_trace_ent (P Q : List PkgLetter) (x y : ℕ) :
    (pkgWordMat G M E L κ (P ++ .ent x y :: Q)).trace =
      pkgWordMat G M E L κ (Q ++ P) (κ y) (κ x) := by
  rw [PB_mat_ent, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← PE_wm_append]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one,
    mul_zero, ite_and]
  simp [Finset.sum_ite_eq']

/-- An entry of `A Δ_{xy} B` is `A_{a κx} B_{κy b}`. -/
private lemma PB_entry_ent (A B : List PkgLetter) (x y : ℕ) (a b : Idx D N) :
    pkgWordMat G M E L κ (A ++ .ent x y :: B) a b =
      pkgWordMat G M E L κ A a (κ x) * pkgWordMat G M E L κ B (κ y) b := by
  rw [PB_mat_ent]
  simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_and,
    Finset.sum_mul, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- The entries of a word are bounded by the product of bounds on the entries of its
segments. -/
private lemma PB_entry_le (β : List PkgLetter → ℝ) :
    ∀ (n : ℕ) (l : List PkgLetter), l.length ≤ n → (∀ s ∈ l.splitOnP isEntP, 0 ≤ β s) →
      (∀ s ∈ l.splitOnP isEntP, ∀ a b, ‖pkgWordMat G M E L κ s a b‖ ≤ β s) →
      ∀ a b, ‖pkgWordMat G M E L κ l a b‖ ≤ ((l.splitOnP isEntP).map β).prod
  | n, l, hn, h0, h, a, b => by
    by_cases hl : l.any isEntP = true
    · obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent l hl
      have hs : (P ++ .ent x y :: Q).splitOnP isEntP = P :: Q.splitOnP isEntP := by
        rw [List.splitOnP_append_cons P Q (rfl : isEntP (.ent x y) = true),
          List.splitOnP_eq_singleton hP]
        rfl
      rw [hs] at h0 h ⊢
      rw [PB_entry_ent, norm_mul, List.map_cons, List.prod_cons]
      match n with
      | 0 => simp at hn
      | n + 1 =>
        have hQ : Q.length ≤ n := by simp at hn; omega
        have ih := PB_entry_le β n Q hQ (fun s hs => h0 s (List.mem_cons_of_mem _ hs))
          (fun s hs => h s (List.mem_cons_of_mem _ hs)) (κ y) b
        exact mul_le_mul (h P List.mem_cons_self _ _) ih (norm_nonneg _)
          (h0 P List.mem_cons_self)
    · have hl' : ∀ y ∈ l, isEntP y = false := by simpa using hl
      rw [List.splitOnP_eq_singleton hl'] at h ⊢
      simpa using h l List.mem_cons_self a b

end Mat


/-! ## One segment -/

/-- The isotropic half of (A.53) [entprodG] uniformly over `Bd_Cl`, for slots `σ i`. -/
private lemma PB_iso_unif (D : ℕ) (hD : 1 ≤ D) (p : ℕ) (hp : 1 ≤ p) (σ : Fin p → Fin 2)
    (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀)
    (C : ℕ → ℝ) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
      ∀ u v : Idx D N → ℂ, ∑ y, ‖u y‖ ^ 2 = 1 → ∑ y, ‖v y‖ ^ 2 = 1 →
        x.1 {h | (N : ℝ) ^ τ'' *
              bndA4 (fun i => (mSol ((x.2.c (σ i) : ℂ) • lam D N x.2.A) (x.2.z (σ i))).im)
                (fun i => (x.2.z (σ i)).im) p <
            ‖star u ⬝ᵥ (resProd (fun i => res (Matrix.of h + (x.2.c (σ i) : ℂ) • lam D N x.2.A)
              (x.2.z (σ i))) s B *ᵥ v)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ'' hτ'' D' hD'
  refine Bd_unif D δA C₀ K C (by linarith) _ fun x hx => ?_
  obtain ⟨N₀, hN₀⟩ := entprodG_local D p hp δA τ c₀ C₀ hτ hc₀ hC₀ C (fun _ => 1)
    (fun N => (x N).1) (fun N => (x N).2.A)
    ⟨hD, hδA, fun _ => ⟨zero_le_one, le_rfl⟩, fun N => (hx N).1, fun N => (hx N).2.1⟩
    (fun N => (hx N).2.2.1) (fun N i => (x N).2.c (σ i)) (fun N i => (hx N).2.2.2.1 (σ i))
    (fun N => {z | (∀ a, Bd_zc D τ c₀ N (x N).2 a) ∧ z = fun i => (x N).2.z (σ i)})
    (fun N z hz i => by
      obtain ⟨h1, rfl⟩ := hz
      exact h1 (σ i)) τ'' hτ'' D' hD'
  exact Filter.eventually_atTop.mpr ⟨N₀, fun N hN hz s B hB u v hu hv =>
    (hN₀ N hN _ ⟨hz, rfl⟩ s B hB).2 u v hu hv⟩

/-- `X = ‖X‖ Y` with `‖Y‖ ≤ 1`. -/
private lemma PB_normalize {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    ∃ Y : Matrix ι ι ℂ, opNorm Y ≤ 1 ∧ X = ((opNorm X : ℝ) : ℂ) • Y := by
  by_cases h : opNorm X = 0
  · have hX : X = 0 := by
      unfold opNorm at h
      rw [norm_eq_zero] at h
      exact (map_eq_zero_iff (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (EquivLike.injective _)).1 h
    exact ⟨0, by rw [Bd_opNorm_zero]; norm_num, by simp [hX]⟩
  · have h0 : 0 < opNorm X := lt_of_le_of_ne (Bd_opNorm_nonneg X) (Ne.symm h)
    refine ⟨(((opNorm X)⁻¹ : ℝ) : ℂ) • X, ?_, ?_⟩
    · rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0),
        inv_mul_cancel₀ h]
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h, Complex.ofReal_one, one_smul]

/-- Scaling `Λ̃` scales a word by its number of letters `Λ̃`. -/
private lemma PB_Lscale {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (c : ℂ) (L : Matrix ι ι ℂ) : ∀ w : List LoopLetter,
    loopWordMat G M E (c • L) w = c ^ (w.countP Bd_isL) • loopWordMat G M E L w
  | [] => by simp [loopWordMat]
  | x :: w => by
    have ih := PB_Lscale G M E c L w
    have e : ∀ L' : Matrix ι ι ℂ, loopWordMat G M E L' (x :: w) =
        loopWordMat G M E L' [x] * loopWordMat G M E L' w := fun _ => by simp [loopWordMat]
    rw [e, e, ih]
    cases x <;> simp [loopWordMat, Bd_isL, List.countP_cons, pow_succ, smul_smul, mul_comm]

/-- A segment of non-resolvent letters with `‖𝔐_a‖ ≤ 5/4`, `‖E_x‖ ≤ 1`, `‖L‖ ≤ 1`. -/
private lemma PB_seg_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (hM : ∀ a, opNorm (M a) ≤ 5 / 4)
    (hE : ∀ y, opNorm (E y) ≤ 1) (hL : opNorm L ≤ 1) (v q : List LoopLetter)
    (hq : ∀ x ∈ q, x ∈ v ∧ Bd_isRes x = false) (hlen : q.length ≤ v.length) :
    opNorm ((q.map (Bd_let 0 M E L)).prod) ≤ (5 / 4) ^ v.length := by
  refine (Bd_prod_norm q _ (5 / 4) (by norm_num) fun x hx => ?_).trans
    (pow_le_pow_right₀ (by norm_num) hlen)
  obtain ⟨-, hxr⟩ := hq x hx
  cases x with
  | res a => simp [Bd_isRes] at hxr
  | det a => exact hM a
  | proj y => exact (hE y).trans (by norm_num)
  | lamt o => exact hL.trans (by norm_num)

private lemma PB_Bv_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (hM : ∀ a, opNorm (M a) ≤ 5 / 4)
    (hE : ∀ y, opNorm (E y) ≤ 1) (hL : opNorm L ≤ 1) (v : List LoopLetter)
    (j : Fin ((Bd_dec v).2.length + 1)) : opNorm (Bd_Bv M E L v j) ≤ (5 / 4) ^ v.length := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Bd_Bv, Fin.cons_zero]
    exact PB_seg_norm M E L hM hE hL v _ (Bd_dec_mem v).1 (Bd_dec_mem v).2.1
  · simp only [Bd_Bv, Fin.cons_succ]
    exact PB_seg_norm M E L hM hE hL v _ ((Bd_dec_mem v).2.2 _ (List.get_mem _ _)).1
      ((Bd_dec_mem v).2.2 _ (List.get_mem _ _)).2

/-- `(X Y)_{ab} = (X^* e_a)^* Y e_b`. -/
private lemma PB_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) (a b : ι) :
    star (Xᴴ *ᵥ Pi.single a 1) ⬝ᵥ (Y *ᵥ Pi.single b 1) = (X * Y) a b := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

private lemma PB_single_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι) :
    ∑ y, ‖(Pi.single b (1 : ℂ) : ι → ℂ) y‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single b (fun y _ hy => by simp [hy]) (by simp)]
  simp


/-- An entry of a word with `p ≥ 1` resolvents, by the isotropic half of (A.53) [entprodG]:
`|(Π)_{ab}| ≺ η^{-(p-1)} ‖Λ̃‖^{#Λ̃}`. -/
private lemma PB_seg_res (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hr : 1 ≤ w.countP Bd_isRes) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) → ∀ a b : Idx D N,
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖loopWordMat (x.2.G h) x.2.M E x.2.Lt w a b‖ ≤
            (5 / 4) ^ (w.length * (w.countP Bd_isRes + 1)) * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.Lt ^ (w.countP Bd_isL) := by
  intro τ'' hτ'' D' hD'
  set p := (Bd_dec w).2.length with hp
  have hpr : p = w.countP Bd_isRes := Bd_dec_len w
  have hp1 : 1 ≤ p := by omega
  set σ : Fin p → Fin 2 := fun j => ((Bd_dec w).2.get j).1 with hσ
  have hU := PB_iso_unif D hD p hp1 σ δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C τ'' hτ'' D' hD'
  filter_upwards [hU, Filter.eventually_ge_atTop 1] with N hN hN1 x hx hz E hE a b
  obtain ⟨-, hM, -, hη, hηz, him⟩ := Bd_facts hD hN1 hC₀ hx hz
  obtain ⟨Lh, hLh, hLeq⟩ := PB_normalize x.2.Lt
  set Rs : ℝ := (5 / 4) ^ w.length with hRs
  have hRs1 : 1 ≤ Rs := one_le_pow₀ (by norm_num)
  have hRs0 : 0 < Rs := by linarith
  set B' : Fin p → Matrix (Idx D N) (Idx D N) ℂ :=
    fun j => ((Rs⁻¹ : ℝ) : ℂ) • Bd_Bv x.2.M E Lh w j.succ with hB'
  have hB'n : ∀ j, opNorm (B' j) ≤ 1 := by
    intro j
    simp only [hB']
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRs0),
      inv_mul_le_iff₀ hRs0, mul_one]
    exact PB_Bv_norm x.2.M E Lh hM hE hLh w j.succ
  set B0 := Bd_Bv x.2.M E Lh w 0 with hB0
  set u0 : Idx D N → ℂ := B0ᴴ *ᵥ Pi.single a 1 with hu0
  set vb : Idx D N → ℂ := Pi.single b 1 with hvb
  have hvb1 : ∑ y, ‖vb y‖ ^ 2 = 1 := PB_single_sq b
  have hvn1 : MultiRes_vn (Pi.single a (1 : ℂ) : Idx D N → ℂ) = 1 := by
    have h1 := MultiRes_vn_sq (Pi.single a (1 : ℂ) : Idx D N → ℂ)
    rw [PB_single_sq a] at h1
    have h0 := MultiRes_vn_nonneg (Pi.single a (1 : ℂ) : Idx D N → ℂ)
    nlinarith
  have hu0n : MultiRes_vn u0 ≤ Rs := by
    refine (MultiRes_vn_mulVec_le _ _).trans ?_
    rw [hvn1, mul_one, Bd_opNorm_conjTranspose]
    exact PB_Bv_norm x.2.M E Lh hM hE hLh w 0
  -- the entry as a bilinear form
  have hmat : ∀ h, (Matrix.of h).IsHermitian →
      loopWordMat (x.2.G h) x.2.M E x.2.Lt w a b =
        ((opNorm x.2.Lt : ℝ) : ℂ) ^ (w.countP Bd_isL) * ((Rs : ℝ) : ℂ) ^ p *
          (star u0 ⬝ᵥ (resProd (fun i => res (Matrix.of h + (x.2.c (σ i) : ℂ) • lam D N x.2.A)
            (x.2.z (σ i))) (fun j => x.2.s (σ j)) B' *ᵥ vb)) := by
    intro h hh
    set Gr : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ :=
      fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i) with hGr
    have hsc := PB_Lscale (x.2.G h) x.2.M E ((opNorm x.2.Lt : ℝ) : ℂ) Lh w
    rw [← hLeq] at hsc
    have hkey1 : resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j)) B' =
        ((Rs⁻¹ : ℝ) : ℂ) ^ p • resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j))
          (fun j => Bd_Bv x.2.M E Lh w j.succ) := by
      unfold resProd
      exact Bd_ofFn_smul _ _ _
    have hkey2 : resWord Gr (Bd_wv x.2.s w) (Bd_Bv x.2.M E Lh w) =
        B0 * resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j))
          (fun j => Bd_Bv x.2.M E Lh w j.succ) := by
      unfold resWord resProd
      rfl
    have hRR : ((Rs : ℝ) : ℂ) ^ p * ((Rs⁻¹ : ℝ) : ℂ) ^ p = 1 := by
      rw [← mul_pow]
      push_cast
      rw [mul_inv_cancel₀ (by exact_mod_cast hRs0.ne'), one_pow]
    set P := resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j))
      (fun j => Bd_Bv x.2.M E Lh w j.succ) with hP
    rw [hsc, Bd_wordMat_eq, Bd_G_eq _ _ hh, Bd_mat_resWord Gr, hkey2, hkey1, Matrix.smul_apply,
      smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hu0, hvb, PB_dot]
    linear_combination (-(((opNorm x.2.Lt : ℝ) : ℂ) ^ (w.countP Bd_isL) * (B0 * P) a b)) * hRR
  have hbnd : ∀ y : ℂ, ‖y‖ ≤ (N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (p - 1) →
      ‖((opNorm x.2.Lt : ℝ) : ℂ) ^ (w.countP Bd_isL) * ((Rs : ℝ) : ℂ) ^ p *
        (((MultiRes_vn u0 : ℝ) : ℂ) * y)‖ ≤
      (5 / 4) ^ (w.length * (w.countP Bd_isRes + 1)) * (N : ℝ) ^ τ'' *
        (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.Lt ^ (w.countP Bd_isL) := by
    intro y hy
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Bd_opNorm_nonneg _), abs_of_pos hRs0, abs_of_nonneg (MultiRes_vn_nonneg _),
      ← hpr]
    have hk : 0 ≤ (Bd_eta x.2)⁻¹ ^ (p - 1) := by positivity
    have hL0 : 0 ≤ opNorm x.2.Lt ^ (w.countP Bd_isL) := pow_nonneg (Bd_opNorm_nonneg _) _
    have hRp : Rs ^ p * Rs = (5 / 4) ^ (w.length * (p + 1)) := by
      rw [hRs, ← pow_succ, ← pow_mul]
    calc opNorm x.2.Lt ^ (w.countP Bd_isL) * Rs ^ p * (MultiRes_vn u0 * ‖y‖)
        ≤ opNorm x.2.Lt ^ (w.countP Bd_isL) * Rs ^ p *
            (Rs * ((N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (p - 1))) := by
          gcongr
      _ = (Rs ^ p * Rs) * (N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (p - 1) *
            opNorm x.2.Lt ^ (w.countP Bd_isL) := by ring
      _ = _ := by rw [hRp]
  by_cases hu : MultiRes_vn u0 = 0
  · have hu' : u0 = 0 := MultiRes_vn_eq_zero hu
    refine ⟨∅, by simp, fun h hh _ => ?_⟩
    rw [hmat h hh, hu', star_zero, zero_dotProduct, mul_zero, norm_zero]
    have := hbnd 0 (by rw [norm_zero]; positivity)
    simpa using (norm_nonneg _).trans this
  · have hu0p : 0 < MultiRes_vn u0 := lt_of_le_of_ne (MultiRes_vn_nonneg _) (Ne.symm hu)
    set uh : Idx D N → ℂ := (((MultiRes_vn u0)⁻¹ : ℝ) : ℂ) • u0 with huh
    have huh1 : ∑ y, ‖uh y‖ ^ 2 = 1 := by
      rw [← MultiRes_vn_sq, huh, MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hu0p), inv_mul_cancel₀ hu, one_pow]
    have hu0eq : u0 = ((MultiRes_vn u0 : ℝ) : ℂ) • uh := by
      rw [huh, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hu, Complex.ofReal_one, one_smul]
    refine ⟨_, hN x hx hz (fun j => x.2.s (σ j)) B' hB'n uh vb huh1 hvb1, fun h hh hbad => ?_⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hbad
    rw [hmat h hh]
    have : star u0 = ((MultiRes_vn u0 : ℝ) : ℂ) • star uh := by
      conv_lhs => rw [hu0eq]
      rw [star_smul, Complex.star_def, Complex.conj_ofReal]
    rw [this, smul_dotProduct, smul_eq_mul]
    refine hbnd _ (hbad.trans ?_)
    have : Nonempty (Fin p) := ⟨⟨0, hp1⟩⟩
    exact mul_le_mul_of_nonneg_left (Bd_bndA4_le _ _ p (Bd_eta x.2) hη (fun i => him (σ i))
      (fun i => hηz (σ i))) (by positivity)


private lemma PB_cw_le (D : ℕ) (hD : 1 ≤ D) (K : ℝ) (L len k p : ℕ) (hlen : len ≤ L)
    (hp : p ≤ len) (hk : k ≤ 2) :
    (5 / 4 : ℝ) ^ (len * (p + 1)) * (2 + 4 * |K|) ^ k ≤ Bd_cw D K (L + 1) := by
  unfold Bd_cw
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hQ : (1 : ℝ) ≤ 2 + 4 * |K| := by linarith [abs_nonneg K]
  have h1 : (5 / 4 : ℝ) ^ (len * (p + 1)) ≤ (5 / 4) ^ ((L + 1) * (L + 1)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul (by omega) (by omega))
  have h2 : (2 + 4 * |K|) ^ k ≤ (2 + 4 * |K|) ^ 2 := pow_le_pow_right₀ hQ hk
  have h3 : (0 : ℝ) ≤ (2 + 4 * |K|) ^ 2 := by positivity
  calc (5 / 4 : ℝ) ^ (len * (p + 1)) * (2 + 4 * |K|) ^ k
      ≤ (5 / 4) ^ ((L + 1) * (L + 1)) * (2 + 4 * |K|) ^ 2 := by gcongr
    _ ≤ (5 / 4) ^ ((L + 1) * (L + 1)) * (4 * D) * (2 + 4 * |K|) ^ 2 := by
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith

/-- The entries of one segment, uniformly in the entry, off one event of probability
`≤ N^{-D'}`: `|(Π)_{ab}| ≤ C N^{τ''} η^{-(p-1)₊} ‖A‖^{#Λ̃}`, `p` the number of resolvents. -/
private lemma PB_seg_all (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hw2 : w.countP Bd_isL ≤ 2) (Lw : ℕ) (hlen : w.length ≤ Lw) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → ∀ a b : Idx D N,
          ‖loopWordMat (x.2.G h) x.2.M E x.2.Lt w a b‖ ≤
            Bd_cw D K (Lw + 1) * (N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) *
              opNorm x.2.A ^ (w.countP Bd_isL) := by
  intro τ'' hτ'' D' hD'
  have hplen : w.countP Bd_isRes ≤ w.length := List.countP_le_length
  rcases Nat.eq_zero_or_pos (w.countP Bd_isRes) with hr | hr
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN1 x hx hz E hE
    refine ⟨∅, by simp, fun h _ _ a b => ?_⟩
    obtain ⟨-, hM, hLt, -, -, -⟩ := Bd_facts hD hN1 hC₀ hx hz
    have hA0 := Bd_opNorm_nonneg x.2.A
    have hK0 : (1 : ℝ) ≤ 2 + 4 * |K| := by linarith [abs_nonneg K]
    have hQ : 0 ≤ (2 + 4 * |K|) * opNorm x.2.A := by positivity
    have hprod := Bd_prod_normL w (Bd_let (x.2.G h) x.2.M E x.2.Lt) (5 / 4)
      ((2 + 4 * |K|) * opNorm x.2.A) (by norm_num) hQ (fun y hy => by
        have hyr : Bd_isRes y = false := by simpa using List.countP_eq_zero.mp hr y hy
        cases y with
        | res a => simp [Bd_isRes] at hyr
        | det a => simpa [Bd_isL, Bd_let] using hM a
        | proj y => simpa [Bd_isL, Bd_let] using (hE y).trans (by norm_num : (1 : ℝ) ≤ 5 / 4)
        | lamt o => simpa [Bd_isL, Bd_let] using hLt)
    rw [hr, Nat.zero_sub, pow_zero, mul_one]
    have hN1' : (1 : ℝ) ≤ (N : ℝ) ^ τ'' := Real.one_le_rpow (by exact_mod_cast hN1) hτ''.le
    have hcw := PB_cw_le D hD K Lw w.length (w.countP Bd_isL) 0 hlen (Nat.zero_le _) hw2
    have hcw1 : (5 / 4 : ℝ) ^ w.length ≤ (5 / 4) ^ (w.length * (0 + 1)) := by simp
    have hAc : 0 ≤ opNorm x.2.A ^ (w.countP Bd_isL) := by positivity
    have hcw0 : 0 ≤ Bd_cw D K (Lw + 1) := le_trans (by positivity) hcw
    calc ‖loopWordMat (x.2.G h) x.2.M E x.2.Lt w a b‖
        ≤ opNorm (loopWordMat (x.2.G h) x.2.M E x.2.Lt w) := norm_apply_le_opNorm _ _ _
      _ ≤ (5 / 4) ^ w.length * ((2 + 4 * |K|) * opNorm x.2.A) ^ (w.countP Bd_isL) := by
          rw [Bd_wordMat_eq]; exact hprod
      _ = ((5 / 4) ^ w.length * (2 + 4 * |K|) ^ (w.countP Bd_isL)) *
            opNorm x.2.A ^ (w.countP Bd_isL) := by rw [mul_pow]; ring
      _ ≤ Bd_cw D K (Lw + 1) * opNorm x.2.A ^ (w.countP Bd_isL) := by
          refine mul_le_mul_of_nonneg_right ?_ hAc
          exact (mul_le_mul_of_nonneg_right hcw1 (by positivity)).trans hcw
      _ ≤ Bd_cw D K (Lw + 1) * (N : ℝ) ^ τ'' * opNorm x.2.A ^ (w.countP Bd_isL) := by
          refine mul_le_mul_of_nonneg_right ?_ hAc
          exact le_mul_of_one_le_right hcw0 hN1'
  · have hU := PB_seg_res D hD δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C w hr τ'' hτ'' (D' + 3) (by linarith)
    filter_upwards [hU, Filter.eventually_ge_atTop (D ^ 2 + 1)] with N hN hN1 x hx hz E hE
    have hN1' : 1 ≤ N := by nlinarith
    obtain ⟨-, -, hLt, hη, -, -⟩ := Bd_facts hD hN1' hC₀ hx hz
    choose bad hbad1 hbad2 using hN x hx hz E hE
    refine ⟨⋃ ab : Idx D N × Idx D N, bad ab.1 ab.2, ?_, fun h hh hb a b => ?_⟩
    · refine (measure_iUnion_fintype_le _ _).trans ?_
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN1'
      have hNDD : (0 : ℝ) ≤ (N : ℝ) ^ (-(D' + 3)) := by positivity
      refine (Finset.sum_le_sum fun ab _ => hbad1 ab.1 ab.2).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hc : ((Fintype.card (Idx D N × Idx D N) : ℕ) : ℝ) = ((D : ℝ) * N) ^ 2 := by
        simp [Fintype.card_prod]; ring
      rw [hc]
      have e1 : (N : ℝ) ^ (-(D' + 3)) = (N : ℝ) ^ (-D') * ((N : ℝ) ^ 3)⁻¹ := by
        rw [show -(D' + 3) = -D' + -3 by ring, Real.rpow_add hNr, Real.rpow_neg hNr.le (3 : ℝ)]
        norm_cast
      rw [e1]
      have hD2 : ((D : ℝ)) ^ 2 + 1 ≤ N := by exact_mod_cast hN1
      have hND : ((D : ℝ) * N) ^ 2 * ((N : ℝ) ^ 3)⁻¹ ≤ 1 := by
        rw [mul_pow, mul_assoc, show (N : ℝ) ^ 2 * ((N : ℝ) ^ 3)⁻¹ = (N : ℝ)⁻¹ by
          field_simp]
        rw [mul_inv_le_iff₀ hNr]
        linarith
      have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (-D') := by positivity
      nlinarith
    · have hbab : h ∉ bad a b := fun hm => hb (Set.mem_iUnion.mpr ⟨(a, b), hm⟩)
      refine (hbad2 a b h hh hbab).trans ?_
      have hA0 := Bd_opNorm_nonneg x.2.A
      have hcw := PB_cw_le D hD K Lw w.length (w.countP Bd_isL) (w.countP Bd_isRes) hlen hplen hw2
      have hL : opNorm x.2.Lt ^ (w.countP Bd_isL) ≤
          (2 + 4 * |K|) ^ (w.countP Bd_isL) * opNorm x.2.A ^ (w.countP Bd_isL) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (Bd_opNorm_nonneg _) hLt _
      have hk : 0 ≤ (N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) := by
        positivity
      calc (5 / 4 : ℝ) ^ (w.length * (w.countP Bd_isRes + 1)) * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.Lt ^ (w.countP Bd_isL)
          ≤ (5 / 4 : ℝ) ^ (w.length * (w.countP Bd_isRes + 1)) * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) *
            ((2 + 4 * |K|) ^ (w.countP Bd_isL) * opNorm x.2.A ^ (w.countP Bd_isL)) := by
            gcongr
        _ = ((5 / 4 : ℝ) ^ (w.length * (w.countP Bd_isRes + 1)) *
              (2 + 4 * |K|) ^ (w.countP Bd_isL)) *
            ((N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1)) *
            opNorm x.2.A ^ (w.countP Bd_isL) := by ring
        _ ≤ Bd_cw D K (Lw + 1) * ((N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1)) *
            opNorm x.2.A ^ (w.countP Bd_isL) := by gcongr
        _ = _ := by ring


/-! ## One word -/

/-- The letter is a `Λ̃`. -/
private def PB_isL (x : PkgLetter) : Bool :=
  match x with | .lw (.lamt _) => true | _ => false

private lemma PB_toL_counts (s : List PkgLetter) (hs : ∀ y ∈ s, isEntP y = false) :
    (PB_toL s).countP Bd_isRes = s.countP isResP ∧ (PB_toL s).countP Bd_isL = s.countP PB_isL ∧
      (PB_toL s).length = s.length := by
  have e := PB_toL_eq s hs
  have h1 : isResP ∘ PkgLetter.lw = Bd_isRes := by funext x; cases x <;> rfl
  have h2 : PB_isL ∘ PkgLetter.lw = Bd_isL := by funext x; cases x <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · conv_rhs => rw [← e]
    rw [List.countP_map, h1]
  · conv_rhs => rw [← e]
    rw [List.countP_map, h2]
  · conv_rhs => rw [← e]
    rw [List.length_map]

/-- The factor of a word: its trace if it has a letter `Δ`, its normalized trace otherwise. -/
private def PB_val {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (w : List PkgLetter) : ℂ :=
  if w.any isEntP then (pkgWordMat G M E L κ w).trace else ntr (pkgWordMat G M E L κ w)

/-- The factor of a word from bounds on its cyclic segments. -/
private lemma PB_val_le {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (w : List PkgLetter) (β : List PkgLetter → ℝ) (hβ : ∀ s ∈ PB_segs w, 0 ≤ β s)
    (hntr : w.any isEntP = false → ‖ntr (pkgWordMat G M E L κ w)‖ ≤ β w)
    (hent : w.any isEntP = true → ∀ s ∈ PB_segs w, ∀ a b, ‖pkgWordMat G M E L κ s a b‖ ≤ β s) :
    ‖PB_val G M E L κ w‖ ≤ ((PB_segs w).map β).prod := by
  unfold PB_val
  by_cases hw : w.any isEntP = true
  · have hent' := hent hw
    simp only [hw, ↓reduceIte]
    obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent _ hw
    rw [PB_segs_ent P Q x y hP] at hβ hent' ⊢
    rw [PB_trace_ent]
    exact PB_entry_le G M E L κ β _ _ le_rfl hβ hent' _ _
  · have hw' : w.any isEntP = false := by simpa using hw
    have e : PB_segs w = [w] := by unfold PB_segs; rw [hw']; rfl
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    rw [e]
    simpa using hntr hw'


private lemma PB_matL {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (s : List PkgLetter) (hs : ∀ y ∈ s, isEntP y = false) :
    pkgWordMat G M E L κ s = loopWordMat G M E L (PB_toL s) := by
  conv_lhs => rw [← PB_toL_eq s hs]
  exact PE_wm_lw G M E L κ _

/-- The factor of one word off an event of probability `≤ k N^{-D'}`, `k` its number of cyclic
segments: `≤ (C N^{τ''})^k η^{-Σ(p_s - 1)₊} ‖A‖^{#Λ̃}`. -/
private lemma PB_word (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List PkgLetter)
    (hw2 : w.countP PB_isL ≤ 2) (Lw : ℕ) (hlen : w.length ≤ Lw) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) → ∀ κ : ℕ → Idx D N,
      ∃ bad : Set (Idx D N → Idx D N → ℂ),
        x.1 bad ≤ ENNReal.ofReal ((PB_segs w).length * (N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖PB_val (x.2.G h) x.2.M E x.2.Lt κ w‖ ≤
            (Bd_cw D K (Lw + 1) * (N : ℝ) ^ τ'') ^ (PB_segs w).length *
              (Bd_eta x.2)⁻¹ ^ ((PB_segs w).map fun s => s.countP isResP - 1).sum *
              opNorm x.2.A ^ ((PB_segs w).map (List.countP PB_isL)).sum := by
  intro τ'' hτ'' D' hD'
  have hq : ∀ y, isEntP y = true → PB_isL y = false := by
    intro y hy; cases y with | lw z => simp [isEntP] at hy | ent => rfl
  obtain ⟨hcL, -, hfree, hslen⟩ := PB_segs_count PB_isL hq w
  have hseg : ∀ s ∈ PB_segs w, (PB_toL s).countP Bd_isL ≤ 2 ∧ (PB_toL s).length ≤ Lw := by
    intro s hs
    obtain ⟨-, h2, h3⟩ := PB_toL_counts s (hfree s hs)
    rw [h2, h3]
    refine ⟨le_trans ?_ hw2, (hslen s hs).trans hlen⟩
    rw [← hcL]
    exact List.le_sum_of_mem (List.mem_map_of_mem hs)
  by_cases hw : w.any isEntP = true
  · obtain ⟨P, i₁, j₁, Q, hP, rfl⟩ := exists_first_ent _ hw
    have hall := (Filter.eventually_all_finset (PB_segs (P ++ .ent i₁ j₁ :: Q)).toFinset).mpr
      fun s hs => PB_seg_all D hD δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C (PB_toL s)
        (hseg s (List.mem_toFinset.mp hs)).1 Lw (hseg s (List.mem_toFinset.mp hs)).2 τ'' hτ'' D' hD'
    filter_upwards [hall, Filter.eventually_ge_atTop 1] with N hN hN1 x hx hz E hE κ
    obtain ⟨-, -, -, hη, -, -⟩ := Bd_facts hD hN1 hC₀ hx hz
    set SG := PB_segs (P ++ .ent i₁ j₁ :: Q) with hSG
    have hb : ∀ i : Fin SG.length, ∃ bad : Set (Idx D N → Idx D N → ℂ),
        x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → ∀ a b : Idx D N,
          ‖loopWordMat (x.2.G h) x.2.M E x.2.Lt (PB_toL (SG.get i)) a b‖ ≤
            Bd_cw D K (Lw + 1) * (N : ℝ) ^ τ'' *
              (Bd_eta x.2)⁻¹ ^ ((PB_toL (SG.get i)).countP Bd_isRes - 1) *
              opNorm x.2.A ^ ((PB_toL (SG.get i)).countP Bd_isL) :=
      fun i => hN _ (List.mem_toFinset.mpr (List.get_mem _ _)) x hx hz E hE
    choose bad hb1 hb2 using hb
    refine ⟨⋃ i, bad i, ?_, fun h hh hbad => ?_⟩
    · refine (measure_iUnion_fintype_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hb1 i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    · have hA0 := Bd_opNorm_nonneg x.2.A
      have hcw0 : 0 ≤ Bd_cw D K (Lw + 1) :=
        le_trans zero_le_one (Bd_cw_ge D hD K (Lw + 1)).2.2.2
      have hent : ∀ s ∈ SG, ∀ a b, ‖pkgWordMat (x.2.G h) x.2.M E x.2.Lt κ s a b‖ ≤
          Bd_cw D K (Lw + 1) * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (s.countP isResP - 1) * opNorm x.2.A ^ (s.countP PB_isL) := by
        intro s hs a b
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hs
        obtain ⟨h1, h2, -⟩ := PB_toL_counts _ (hfree _ hs)
        have := hb2 i h hh (fun hm => hbad (Set.mem_iUnion.mpr ⟨i, hm⟩)) a b
        rw [h1, h2] at this
        rw [PB_matL _ _ _ _ _ _ (hfree _ hs)]
        exact this
      refine (PB_val_le (x.2.G h) x.2.M E x.2.Lt κ _ _ (fun s _ => by positivity)
        (fun h' => by rw [hw] at h'; exact absurd h' (by simp)) (fun _ => hent)).trans ?_
      rw [Bd_list_prod_pow]
  · have hw' : w.any isEntP = false := by simpa using hw
    have e : PB_segs w = [w] := by unfold PB_segs; rw [hw']; rfl
    have hs : w ∈ PB_segs w := by rw [e]; exact List.mem_singleton_self _
    obtain ⟨h1, h2, h3⟩ := PB_toL_counts _ (hfree _ hs)
    have hU := Bd_loop D hD δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C (PB_toL w) (hseg w hs).1 τ'' hτ'' D' hD'
    filter_upwards [hU, Filter.eventually_ge_atTop 1] with N hN hN1 x hx hz E hE κ
    obtain ⟨-, -, -, hη, -, -⟩ := Bd_facts hD hN1 hC₀ hx hz
    obtain ⟨bad, hb1, hb2⟩ := hN x hx hz E hE
    refine ⟨bad, by rw [e]; simpa using hb1, fun h hh hbad => ?_⟩
    unfold PB_val
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    rw [PB_matL _ _ _ _ _ _ (hfree _ hs), e]
    refine (hb2 h hh hbad).trans ?_
    rw [h1, h2, h3]
    simp only [List.length_singleton, pow_one, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    have hA0 := Bd_opNorm_nonneg x.2.A
    gcongr
    exact Bd_cw_mono D K (by omega)


/-- The deterministic bound of the factor of one word: `≤ (N^{L})^k (Q‖A‖)^{#Λ̃}` when the
resolvents have norm `≤ N`. -/
private lemma PB_word_crude {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (Q : ℝ) (hQ : 0 ≤ Q) (hN : (2 : ℝ) ≤ N) (hG : ∀ a, opNorm (G a) ≤ N)
    (hM : ∀ a, opNorm (M a) ≤ 5 / 4) (hE : ∀ y, opNorm (E y) ≤ 1) (hL : opNorm L ≤ Q)
    (w : List PkgLetter) (Lw : ℕ) (hlen : w.length ≤ Lw) :
    ‖PB_val G M E L κ w‖ ≤ ((N : ℝ) ^ Lw) ^ (PB_segs w).length *
      (1 : ℝ) ^ ((PB_segs w).map fun s => s.countP isResP - 1).sum *
      Q ^ ((PB_segs w).map (List.countP PB_isL)).sum := by
  have hq : ∀ y, isEntP y = true → PB_isL y = false := by
    intro y hy; cases y with | lw z => simp [isEntP] at hy | ent => rfl
  obtain ⟨-, -, hfree, hslen⟩ := PB_segs_count PB_isL hq w
  have hseg : ∀ s ∈ PB_segs w, opNorm (pkgWordMat G M E L κ s) ≤
      (N : ℝ) ^ Lw * (1 : ℝ) ^ (s.countP isResP - 1) * Q ^ (s.countP PB_isL) := by
    intro s hs
    obtain ⟨-, h2, h3⟩ := PB_toL_counts _ (hfree _ hs)
    rw [PB_matL _ _ _ _ _ _ (hfree _ hs), Bd_wordMat_eq, one_pow, mul_one, ← h2]
    refine (Bd_prod_normL _ _ N Q (by linarith) hQ fun y _ => ?_).trans ?_
    · cases y with
      | res a => simpa [Bd_isL, Bd_let] using hG a
      | det a => simpa [Bd_isL, Bd_let] using (hM a).trans (by linarith)
      | proj y => simpa [Bd_isL, Bd_let] using (hE y).trans (by linarith)
      | lamt o => simpa [Bd_isL, Bd_let] using hL
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_right₀ (by linarith) (by rw [h3]; exact (hslen s hs).trans hlen)
  refine (PB_val_le G M E L κ w _ (fun s _ => by positivity) (fun hw => ?_)
    (fun _ s hs a b => (norm_apply_le_opNorm _ _ _).trans (hseg s hs))).trans ?_
  · have e : PB_segs w = [w] := by unfold PB_segs; rw [hw]; rfl
    exact (Bd_ntr_le _).trans (hseg w (by rw [e]; exact List.mem_singleton_self _))
  · rw [Bd_list_prod_pow]

/-! ## The class `𝓡`: counting -/

private lemma PB_isL_count (l : List PkgLetter) :
    l.countP PB_isL = l.count (.lw (.lamt 0)) + l.count (.lw (.lamt 1)) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.countP_cons, List.count_cons, List.count_cons, ih]
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp [PB_isL]
    · simp [PB_isL]
    · simp [PB_isL]
    · fin_cases o <;> simp [PB_isL] <;> omega
    · simp [PB_isL]

private lemma PB_sum_seg : ∀ SG : List (List PkgLetter), (∀ s ∈ SG, s.any isGoodP = true) →
    ∃ z, z ≤ (SG.map (List.countP PB_isL)).sum ∧
      (SG.map fun s => s.countP isResP - 1).sum + SG.length = (SG.map (List.countP isResP)).sum + z
  | [], _ => ⟨0, by simp, by simp⟩
  | s :: SG, hg => by
    obtain ⟨z, hz1, hz2⟩ := PB_sum_seg SG fun t ht => hg t (List.mem_cons_of_mem _ ht)
    have hs := hg s List.mem_cons_self
    have hl : s.countP isResP = 0 → 1 ≤ s.countP PB_isL := by
      intro h0
      obtain ⟨y, hy, hyg⟩ := List.any_eq_true.mp hs
      have hyr : isResP y = false := by simpa using List.countP_eq_zero.mp h0 y hy
      have : PB_isL y = true := by
        rcases y with ((a | a | y | o) | ⟨u, v⟩) <;> simp_all [isGoodP, isResP, PB_isL]
      exact List.countP_pos_iff.mpr ⟨y, hy, this⟩
    refine ⟨z + (if s.countP isResP = 0 then 1 else 0), ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      split_ifs with h0
      · have := hl h0; omega
      · omega
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      split_ifs <;> omega

private lemma PB_sum_words : ∀ W : List (List PkgLetter), (∀ w ∈ W, ∀ s ∈ PB_segs w,
    s.any isGoodP = true) →
    ∃ z, z ≤ (W.map fun w => ((PB_segs w).map (List.countP PB_isL)).sum).sum ∧
      (W.map fun w => ((PB_segs w).map fun s => s.countP isResP - 1).sum).sum +
        (W.map fun w => (PB_segs w).length).sum =
      (W.map fun w => ((PB_segs w).map (List.countP isResP)).sum).sum + z
  | [], _ => ⟨0, by simp, by simp⟩
  | w :: W, hg => by
    obtain ⟨z, hz1, hz2⟩ := PB_sum_words W fun t ht => hg t (List.mem_cons_of_mem _ ht)
    obtain ⟨z', hz1', hz2'⟩ := PB_sum_seg (PB_segs w) (hg w List.mem_cons_self)
    refine ⟨z + z', ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons, List.sum_cons]; omega

/-- The counts of a member of the class `𝓡`. -/
private lemma PB_counts (R : PkgExpr) (hR : R.wf = true) :
    (R.loops.map fun w => (PB_segs w).length).sum = (R.loops.map nfac).sum ∧
    (R.loops.map fun w => ((PB_segs w).map (List.countP PB_isL)).sum).sum = 2 ∧
    (∀ w ∈ R.loops, w.countP PB_isL ≤ 2) ∧
    ∃ z, z ≤ 2 ∧ (R.loops.map fun w => ((PB_segs w).map fun s => s.countP isResP - 1).sum).sum +
        (R.loops.map nfac).sum = (R.loops.map (List.countP isResP)).sum + z := by
  obtain ⟨hl0, hl1, hseg, -, -⟩ := (wf_iff R).1 hR
  have hqL : ∀ y, isEntP y = true → PB_isL y = false := by
    intro y hy; cases y with | lw z => simp [isEntP] at hy | ent => rfl
  have hqR : ∀ y, isEntP y = true → isResP y = false := by
    intro y hy; cases y with | lw z => simp [isEntP] at hy | ent => rfl
  have e1 : (R.loops.map fun w => (PB_segs w).length) = R.loops.map nfac :=
    List.map_congr_left fun w _ => (PB_segs_count PB_isL hqL w).2.1
  have e2 : (R.loops.map fun w => ((PB_segs w).map (List.countP PB_isL)).sum) =
      R.loops.map (List.countP PB_isL) :=
    List.map_congr_left fun w _ => (PB_segs_count PB_isL hqL w).1
  have e3 : (R.loops.map fun w => ((PB_segs w).map (List.countP isResP)).sum) =
      R.loops.map (List.countP isResP) :=
    List.map_congr_left fun w _ => (PB_segs_count isResP hqR w).1
  have hL : (R.loops.map (List.countP PB_isL)).sum = 2 := by
    have : R.loops.map (List.countP PB_isL) = R.loops.map fun w =>
        w.count (.lw (.lamt 0)) + w.count (.lw (.lamt 1)) :=
      List.map_congr_left fun w _ => PB_isL_count w
    rw [this, List.sum_map_add, hl0, hl1]
  have hg : ∀ w ∈ R.loops, ∀ s ∈ PB_segs w, s.any isGoodP = true := by
    intro w hw
    have := hseg w hw
    rw [PB_segOK, List.all_eq_true] at this
    exact this
  refine ⟨by rw [e1], by rw [e2, hL], fun w hw => ?_, ?_⟩
  · rw [← hL]
    exact List.le_sum_of_mem (List.mem_map_of_mem hw)
  · obtain ⟨z, hz1, hz2⟩ := PB_sum_words R.loops hg
    rw [e2, hL] at hz1
    rw [e1, e3] at hz2
    exact ⟨z, hz1, hz2⟩


/-! ## The value of an expression from bounds on its factors -/

private lemma PB_list_prod_pow3 {α : Type*} (l : List α) (a b c : ℝ) (k f g : α → ℕ) :
    (l.map fun x => a ^ k x * b ^ f x * c ^ g x).prod =
      a ^ (l.map k).sum * b ^ (l.map f).sum * c ^ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
    rw [pow_add, pow_add, pow_add]
    ring

/-- `|c_𝓡 Σ_ι Π W Π w| ≤ |cf| D^{dexp} N^{-S} D^{nb} Wb^u Lc^{n} X^{Σ(p_s-1)₊} Y^{#Λ̃}`. -/
private lemma PB_evalH_le {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (Wb Lc X Y : ℝ) (hWb : 0 ≤ Wb)
    (hW : ∀ ι : Fin R.nb → Fin D, ∀ p ∈ R.weights,
      ‖ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)‖ ≤ Wb)
    (hL : ∀ ι : Fin R.nb → Fin D, ∀ w ∈ R.loops, ‖PB_val (e.G h) e.M (e.E ι) e.Lt κ w‖ ≤
      Lc ^ (PB_segs w).length * X ^ ((PB_segs w).map fun s => s.countP isResP - 1).sum *
        Y ^ ((PB_segs w).map (List.countP PB_isL)).sum) :
    ‖R.evalH e κ h‖ ≤ |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) * ((D : ℝ) ^ R.nb *
      (Wb ^ R.weights.length * (Lc ^ (R.loops.map fun w => (PB_segs w).length).sum *
        X ^ (R.loops.map fun w => ((PB_segs w).map fun s => s.countP isResP - 1).sum).sum *
        Y ^ (R.loops.map fun w => ((PB_segs w).map (List.countP PB_isL)).sum).sum))) := by
  rw [PE_evalH R e κ h rfl]
  refine (norm_sum_le _ _).trans ?_
  have hcoef : ‖PE_coef D N R‖ = |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) := by
    unfold PE_coef
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_intCast]
  have hc0 : 0 ≤ |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) := by positivity
  have hterm : ∀ ι : Fin R.nb → Fin D, ‖PE_val e ι κ R h‖ ≤
      |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) *
      (Wb ^ R.weights.length * (Lc ^ (R.loops.map fun w => (PB_segs w).length).sum *
        X ^ (R.loops.map fun w => ((PB_segs w).map fun s => s.countP isResP - 1).sum).sum *
        Y ^ (R.loops.map fun w => ((PB_segs w).map (List.countP PB_isL)).sum).sum)) := by
    intro ι
    unfold PE_val
    rw [norm_mul, hcoef, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    have h1 := Bd_list_norm R.weights (PE_wt e ι h) (fun _ => Wb) (hW ι)
    have h2 := Bd_list_norm R.loops (PE_wv e ι κ h) _ (hL ι)
    rw [List.map_const', List.prod_replicate] at h1
    rw [PB_list_prod_pow3] at h2
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  refine (Finset.sum_le_sum fun ι _ => hterm ι).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

/-! ## Arithmetic of the final bound -/

/-- The good-event part of the bound. -/
private lemma PB_good_arith (D N : ℕ) (hN : 1 ≤ N) (cf dexp S : ℤ) (nb u n Sa d : ℕ)
    (Cbig Tt η τ' τ'' A : ℝ) (E : ℤ) (hd : d ≤ 2) (hE : E = ((u + Sa + d : ℕ) : ℤ))
    (hη : 0 < η) (hηT : η ≤ Tt) (hTt : 1 ≤ Tt) (hCbig : 0 ≤ Cbig) (hττ : τ'' * (u + n) ≤ τ' / 2)
    (hlarge : 2 * (|(cf : ℝ)| * (D : ℝ) ^ dexp * (D : ℝ) ^ nb * Cbig ^ n * Tt ^ 2) ≤
      (N : ℝ) ^ (τ' / 2)) :
    |(cf : ℝ)| * (D : ℝ) ^ dexp * (N : ℝ) ^ (-S) * ((D : ℝ) ^ nb *
      (((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * η⁻¹)) ^ u * ((Cbig * (N : ℝ) ^ τ'') ^ n * η⁻¹ ^ Sa *
        A ^ 2))) ≤
      1 / 2 * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(S + u)) * η ^ (-E) * A ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set P := (N : ℝ) ^ τ'' with hP
  set K₀ := |(cf : ℝ)| * (D : ℝ) ^ dexp * (D : ℝ) ^ nb * Cbig ^ n with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set X := (N : ℝ) ^ (-S) with hX
  have hX0 : 0 ≤ X := by positivity
  have hNz : (N : ℝ) ^ (-(S + u)) = X * ((N : ℝ)⁻¹) ^ u := by
    rw [hX, neg_add, zpow_add₀ hNr.ne', zpow_neg (N : ℝ) (u : ℤ), zpow_natCast, inv_pow]
  have hEz : η ^ (-E) = η⁻¹ ^ (u + Sa) * η⁻¹ ^ d := by
    rw [hE, _root_.zpow_neg, zpow_natCast, ← inv_pow, pow_add]
  have hPu : P ^ (u + n) ≤ (N : ℝ) ^ (τ' / 2) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hηd : η⁻¹ ^ (u + Sa) ≤ Tt ^ 2 * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := by
    have h1 : η ^ d ≤ Tt ^ 2 :=
      (pow_le_pow_left₀ hη.le hηT d).trans (pow_le_pow_right₀ hTt hd)
    have h2 : η⁻¹ ^ (u + Sa) = η ^ d * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := by
      rw [← mul_assoc, mul_comm (η ^ d), mul_assoc, ← mul_pow, mul_inv_cancel₀ hη.ne', one_pow,
        mul_one]
    calc η⁻¹ ^ (u + Sa) = η ^ d * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := h2
      _ ≤ Tt ^ 2 * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hhalf : K₀ * Tt ^ 2 * (N : ℝ) ^ (τ' / 2) ≤ 1 / 2 * (N : ℝ) ^ τ' := by
    have : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
      rw [← Real.rpow_add hNr]; ring_nf
    rw [this]
    have h0 : 0 ≤ (N : ℝ) ^ (τ' / 2) := by positivity
    nlinarith
  calc |(cf : ℝ)| * (D : ℝ) ^ dexp * X * ((D : ℝ) ^ nb * ((P * ((N : ℝ)⁻¹ * η⁻¹)) ^ u *
        ((Cbig * P) ^ n * η⁻¹ ^ Sa * A ^ 2)))
      = K₀ * P ^ (u + n) * (X * ((N : ℝ)⁻¹) ^ u) * η⁻¹ ^ (u + Sa) * A ^ 2 := by
        rw [hK₀]; ring
    _ ≤ K₀ * (N : ℝ) ^ (τ' / 2) * (X * ((N : ℝ)⁻¹) ^ u) *
          (Tt ^ 2 * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d)) * A ^ 2 := by
        gcongr
    _ = (K₀ * Tt ^ 2 * (N : ℝ) ^ (τ' / 2)) *
          ((X * ((N : ℝ)⁻¹) ^ u) * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) * A ^ 2) := by ring
    _ ≤ (1 / 2 * (N : ℝ) ^ τ') *
          ((X * ((N : ℝ)⁻¹) ^ u) * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) * A ^ 2) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
    _ = _ := by rw [hNz, hEz]; ring

/-- The bad-event part of the bound. -/
private lemma PB_bad_arith (D N : ℕ) (hN : 1 ≤ N) (cf dexp S : ℤ) (nb u n Ltot Dn Sa : ℕ)
    (QL Tt η τ' A m : ℝ) (E : ℤ) (hDn : Dn = u + Ltot * n + (u + E.natAbs) + 1)
    (hη : 0 < η) (hη1 : (N : ℝ)⁻¹ ≤ η) (hηT : η ≤ Tt) (hTt : 1 ≤ Tt) (hτ' : 0 < τ')
    (hm : m ≤ (D : ℝ) ^ nb * (u + n) * (N : ℝ) ^ (-(Dn : ℝ)))
    (hlarge : 2 * (|(cf : ℝ)| * (D : ℝ) ^ dexp * (D : ℝ) ^ nb * 2 ^ u * QL ^ 2 *
      ((D : ℝ) ^ nb * (u + n))) * Tt ^ E.natAbs ≤ N) :
    |(cf : ℝ)| * (D : ℝ) ^ dexp * (N : ℝ) ^ (-S) * ((D : ℝ) ^ nb * ((2 * (N : ℝ)) ^ u *
      (((N : ℝ) ^ Ltot) ^ n * (1 : ℝ) ^ Sa * (QL * A) ^ 2))) * m ≤
      1 / 2 * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(S + u)) * η ^ (-E) * A ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Cb := |(cf : ℝ)| * (D : ℝ) ^ dexp * (D : ℝ) ^ nb * 2 ^ u * QL ^ 2 * ((D : ℝ) ^ nb * (u + n))
    with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set X := (N : ℝ) ^ (-S) with hX
  have hX0 : 0 < X := by positivity
  set M₀ : ℝ := (N : ℝ) ^ (u + E.natAbs) with hM₀
  have hM₀0 : 0 < M₀ := by positivity
  have hDnr : (N : ℝ) ^ (-(Dn : ℝ)) = (((N : ℝ) ^ u * ((N : ℝ) ^ Ltot) ^ n) * M₀ * N)⁻¹ := by
    rw [Real.rpow_neg hNr.le, Real.rpow_natCast, hDn, hM₀, pow_add, pow_add, pow_add, pow_one,
      pow_mul]
  have hlow : X * (M₀ * Tt ^ E.natAbs)⁻¹ ≤ (N : ℝ) ^ (-(S + u)) * η ^ (-E) := by
    have h1 := Bd_zpow_lower η Tt N hη hTt hN1 hη1 hηT (-E)
    rw [Int.natAbs_neg] at h1
    have h2 : (N : ℝ) ^ (-(S + u)) = X * ((N : ℝ) ^ u)⁻¹ := by
      rw [hX, neg_add, zpow_add₀ hNr.ne', zpow_neg (N : ℝ) (u : ℤ), zpow_natCast]
    rw [h2]
    have h3 : X * (M₀ * Tt ^ E.natAbs)⁻¹ = X * ((N : ℝ) ^ u)⁻¹ * ((Tt * N) ^ E.natAbs)⁻¹ := by
      rw [hM₀, mul_pow, pow_add]
      field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hRg : 1 / 2 * (X * (M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2) ≤
      1 / 2 * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(S + u)) * η ^ (-E) * A ^ 2)) := by
    have hNτ : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
    have h0 : 0 ≤ (N : ℝ) ^ (-(S + u)) * η ^ (-E) * A ^ 2 :=
      mul_nonneg ((by positivity : (0 : ℝ) ≤ X * (M₀ * Tt ^ E.natAbs)⁻¹).trans hlow)
        (by positivity)
    have : X * (M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2 ≤ (N : ℝ) ^ (-(S + u)) * η ^ (-E) * A ^ 2 :=
      mul_le_mul_of_nonneg_right hlow (by positivity)
    nlinarith
  refine le_trans ?_ hRg
  have hTt0 : 0 < Tt ^ E.natAbs := by positivity
  have hkey : Cb * (M₀ * N)⁻¹ ≤ 1 / 2 * (M₀ * Tt ^ E.natAbs)⁻¹ := by
    rw [mul_inv, mul_inv, ← mul_assoc, ← mul_assoc]
    rw [show Cb * M₀⁻¹ * (N : ℝ)⁻¹ = M₀⁻¹ * (Cb / N) by ring,
      show 1 / 2 * M₀⁻¹ * (Tt ^ E.natAbs)⁻¹ = M₀⁻¹ * (1 / (2 * Tt ^ E.natAbs)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_div_iff₀ hNr (by positivity)]
    linarith
  calc |(cf : ℝ)| * (D : ℝ) ^ dexp * X * ((D : ℝ) ^ nb * ((2 * (N : ℝ)) ^ u *
        (((N : ℝ) ^ Ltot) ^ n * (1 : ℝ) ^ Sa * (QL * A) ^ 2))) * m
      ≤ |(cf : ℝ)| * (D : ℝ) ^ dexp * X * ((D : ℝ) ^ nb * ((2 * (N : ℝ)) ^ u *
        (((N : ℝ) ^ Ltot) ^ n * (1 : ℝ) ^ Sa * (QL * A) ^ 2))) *
          ((D : ℝ) ^ nb * (u + n) * (((N : ℝ) ^ u * ((N : ℝ) ^ Ltot) ^ n) * M₀ * N)⁻¹) := by
        rw [← hDnr]
        gcongr
    _ = X * (Cb * ((M₀ * N)⁻¹)) * A ^ 2 := by
        rw [hCb]
        have hu0 : (N : ℝ) ^ u ≠ 0 := by positivity
        have hu1 : ((N : ℝ) ^ Ltot) ^ n ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ X * (1 / 2 * (M₀ * Tt ^ E.natAbs)⁻¹) * A ^ 2 := by gcongr
    _ = 1 / 2 * (X * (M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2) := by ring


/-- The generic bound for the class `𝓡` above the stopping rule of the further expansion:
`𝓡 ≺ N^{-size′₁} η^{-size′₂-2} ‖A‖²`, `size′ = (S + u, m - n + u)`, in expectation and uniformly in
the entry labels, for slots satisfying the hypotheses of Lemma A.4 [lemma_necessary_estimates];
`η = min(Im z₀, Im z₁)`. -/
theorem pkg_generic_bound (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (R : PkgExpr) (hR : R.wf = true) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
        c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) → ∀ κ : ℕ → Idx D N,
        ‖∫ h, R.evalH e κ h ∂μ‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(R.charsP.2.2.2 + R.charsP.2.2.1)) *
            min (e.z 0).im (e.z 1).im ^ (-(R.charsP.1 - R.charsP.2.1 + R.charsP.2.2.1 + 2)) *
            opNorm e.A ^ 2) := by
  intro τ' hτ'
  obtain ⟨hnS, hLS, hw2, z, hz2, hSaz⟩ := PB_counts R hR
  have hD1 : 1 ≤ D := by omega
  set u := R.weights.length with hu
  set n := (R.loops.map nfac).sum with hn
  set m := (R.loops.map (List.countP isResP)).sum with hm
  set Ltot := (R.loops.map List.length).sum with hLtot
  set Sa := (R.loops.map fun w => ((PB_segs w).map fun s => s.countP isResP - 1).sum).sum
    with hSa
  set E : ℤ := R.charsP.1 - R.charsP.2.1 + R.charsP.2.2.1 + 2 with hE
  have hch : R.charsP = ((m : ℤ), (n : ℤ), (u : ℤ), R.S) := charsP_eq R
  obtain ⟨d, hd, hEd⟩ : ∃ d : ℕ, d ≤ 2 ∧ E = ((u + Sa + d : ℕ) : ℤ) := by
    refine ⟨2 - z, by omega, ?_⟩
    rw [hE, hch]
    push_cast
    omega
  set Tt : ℝ := max 1 τ⁻¹ with hTt
  have hTt1 : 1 ≤ Tt := le_max_left _ _
  set QL : ℝ := 2 + 4 * |K| with hQL
  set Cbig : ℝ := Bd_cw D K (Ltot + 1) with hCbig
  have hCbig0 : 0 ≤ Cbig := le_trans zero_le_one (Bd_cw_ge D hD1 K (Ltot + 1)).2.2.2
  set C₁ : ℝ := |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (D : ℝ) ^ R.nb * Cbig ^ n * Tt ^ 2 with hC₁
  set Cb : ℝ := |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (D : ℝ) ^ R.nb * 2 ^ u * QL ^ 2 *
    ((D : ℝ) ^ R.nb * (u + n)) with hCb
  set τ'' : ℝ := τ' / (2 * ((u : ℝ) + n + 1)) with hτ''def
  have hτ'' : 0 < τ'' := by positivity
  have hττ : τ'' * (u + n) ≤ τ' / 2 := by
    rw [hτ''def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set Dn : ℕ := u + Ltot * n + (u + E.natAbs) + 1 with hDn
  have hDn0 : (0 : ℝ) < (Dn : ℝ) := by positivity
  have hW := Bd_weight D hD1 δA τ C₀ hδA hτ hC₀ C τ'' hτ'' Dn hDn0
  have hlenw : ∀ w ∈ R.loops, w.length ≤ Ltot := fun w hw =>
    List.le_sum_of_mem (List.mem_map_of_mem hw)
  have hL := (Filter.eventually_all_finset R.loops.toFinset).mpr fun w hw =>
    PB_word D hD1 δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C w (hw2 w (List.mem_toFinset.mp hw)) Ltot
      (hlenw w (List.mem_toFinset.mp hw)) τ'' hτ'' Dn hDn0
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hW.and hL)
  obtain ⟨N₂, hN₂⟩ := Bd_large (τ' / 2) (2 * C₁) (by positivity)
  obtain ⟨N₃, hN₃⟩ := Bd_large 1 (2 * Cb * Tt ^ E.natAbs) one_pos
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN μ hμ e hA hA2 hc hz hδ κ => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hWN, hLN⟩ := hN₁ N hNa
  have hlarge1 := hN₂ N hNb
  have hlarge2 : 2 * Cb * Tt ^ E.natAbs ≤ N := by simpa using hN₃ N hNc
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hx : (μ, e) ∈ Bd_Cl D δA C₀ K C N := ⟨hμ, hA, hA2, hc, hδ⟩
  obtain ⟨hA1, hM, hLt, hη, hηz, -⟩ := Bd_facts hD1 (by omega) hC₀ hx hz
  have hM' : ∀ a, opNorm (e.M a) ≤ 5 / 4 := hM
  have hLt' : opNorm e.Lt ≤ QL * opNorm e.A := hLt
  have hη' : 0 < Bd_eta e := hη
  have hηz' : ∀ a, Bd_eta e ≤ (e.z a).im := hηz
  have hA0 := Bd_opNorm_nonneg e.A
  have := hμ.prob
  have hzN : ∀ a, (N : ℝ)⁻¹ ≤ |(e.z a).im| := by
    intro a
    refine le_trans ?_ (hz a).1.2
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hηT : Bd_eta e ≤ Tt := by
    refine (hηz' 0).trans ((Complex.im_le_norm _).trans ((hz 0).1.1.trans ?_))
    exact le_max_right _ _
  have hη1 : (N : ℝ)⁻¹ ≤ Bd_eta e := by
    unfold Bd_eta
    refine le_min ?_ ?_
    · have := hzN 0; rwa [abs_of_pos (hz 0).2.1] at this
    · have := hzN 1; rwa [abs_of_pos (hz 1).2.1] at this
  -- the events
  have hWb : ∀ (ι : Fin R.nb → Fin D) (i : Fin u), ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Dn : ℝ))) ∧ ∀ h, h ∉ bad →
        ‖ntr ((e.G h (R.weights.get i).1 - e.M (R.weights.get i).1) *
          e.E ι (R.weights.get i).2)‖ ≤
          (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |(e.z (R.weights.get i).1).im|)) :=
    fun ι i => hWN μ hμ e hA hc (fun a => (hz a).1) _ _ (Bd_opNorm_E e ι _)
  choose bW hbW1 hbW2 using hWb
  have hLb : ∀ (ι : Fin R.nb → Fin D) (i : Fin R.loops.length),
      ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((PB_segs (R.loops.get i)).length * (N : ℝ) ^ (-(Dn : ℝ))) ∧
      ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
        ‖PB_val (e.G h) e.M (e.E ι) e.Lt κ (R.loops.get i)‖ ≤
          (Cbig * (N : ℝ) ^ τ'') ^ (PB_segs (R.loops.get i)).length *
            (Bd_eta e)⁻¹ ^ ((PB_segs (R.loops.get i)).map fun s => s.countP isResP - 1).sum *
            opNorm e.A ^ ((PB_segs (R.loops.get i)).map (List.countP PB_isL)).sum :=
    fun ι i => hLN (R.loops.get i) (List.mem_toFinset.mpr (List.get_mem _ _)) (μ, e) hx hz
      (e.E ι) (Bd_opNorm_E e ι) κ
  choose bL hbL1 hbL2 using hLb
  set bad : Set (Idx D N → Idx D N → ℂ) := ⋃ ι, ((⋃ i, bW ι i) ∪ ⋃ i, bL ι i) with hbad
  have hNDn : 0 ≤ (N : ℝ) ^ (-(Dn : ℝ)) := by positivity
  have hmbad : μ.real bad ≤ (D : ℝ) ^ R.nb * (u + n) * (N : ℝ) ^ (-(Dn : ℝ)) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    have hι : ∀ ι : Fin R.nb → Fin D, μ.real ((⋃ i, bW ι i) ∪ ⋃ i, bL ι i) ≤
        ((u : ℝ) + n) * (N : ℝ) ^ (-(Dn : ℝ)) := by
      intro ι
      refine (measureReal_union_le _ _).trans ?_
      refine (add_le_add (measureReal_iUnion_fintype_le _)
        (measureReal_iUnion_fintype_le _)).trans ?_
      refine (add_le_add (Finset.sum_le_sum fun i _ =>
        ENNReal.toReal_le_of_le_ofReal hNDn (hbW1 ι i)) (Finset.sum_le_sum fun i _ =>
        ENNReal.toReal_le_of_le_ofReal (by positivity) (hbL1 ι i))).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
      have hsum : ∑ i : Fin R.loops.length, ((PB_segs (R.loops.get i)).length : ℝ) = n := by
        have := Fin.sum_univ_fun_getElem R.loops fun w => ((PB_segs w).length : ℝ)
        simp only [List.get_eq_getElem]
        rw [this, ← hnS, Nat.cast_list_sum, List.map_map]
        rfl
      rw [hsum]
      ring_nf
      exact le_rfl
    refine (Finset.sum_le_sum fun ι _ => hι ι).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl
  -- the two pointwise bounds
  set RHS : ℝ := (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(R.charsP.2.2.2 + R.charsP.2.2.1)) *
    min (e.z 0).im (e.z 1).im ^ (-(R.charsP.1 - R.charsP.2.1 + R.charsP.2.2.1 + 2)) *
    opNorm e.A ^ 2) with hRHS
  have hRHS' : RHS = (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(R.S + (u : ℤ))) * Bd_eta e ^ (-E) *
      opNorm e.A ^ 2) := by rw [hRHS, hE, hch]; rfl
  set Rb : ℝ := |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) * ((D : ℝ) ^ R.nb *
      ((2 * (N : ℝ)) ^ u * (((N : ℝ) ^ Ltot) ^ n * (1 : ℝ) ^ Sa * (QL * opNorm e.A) ^ 2)))
    with hRb
  have hcrude : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ‖R.evalH e κ h‖ ≤ Rb := by
    intro h hh
    have hG : ∀ a, opNorm (e.G h a) ≤ N := by
      intro a
      refine (Bd_G_norm e h hh a (hz a).2.1.ne').trans ?_
      rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (hzN a)) (by positivity)]
      exact hzN a
    have h1 := PB_evalH_le R e κ h (2 * N) ((N : ℝ) ^ Ltot) 1 (QL * opNorm e.A) (by positivity)
      (fun ι p _ => by
        refine (Bd_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
        have h1 := Bd_opNorm_sub (e.G h p.1) (e.M p.1)
        have h2 := hG p.1
        have h3 := hM' p.1
        have h0 := Bd_opNorm_nonneg (e.G h p.1 - e.M p.1)
        calc opNorm (e.G h p.1 - e.M p.1) * opNorm (e.E ι p.2)
            ≤ opNorm (e.G h p.1 - e.M p.1) * 1 :=
              mul_le_mul_of_nonneg_left (Bd_opNorm_E e ι p.2) h0
          _ ≤ 2 * N := by linarith)
      (fun ι w hw => PB_word_crude (e.G h) e.M (e.E ι) e.Lt κ (QL * opNorm e.A) (by positivity)
        hNr hG hM' (Bd_opNorm_E e ι) hLt' w Ltot (hlenw w hw))
    rw [hnS, hLS] at h1
    exact h1
  have hgood : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → h ∉ bad →
      ‖R.evalH e κ h‖ ≤ 1 / 2 * RHS := by
    intro h hh hb
    have hbW : ∀ ι i, h ∉ bW ι i := fun ι i hm =>
      hb (Set.mem_iUnion.mpr ⟨ι, Or.inl (Set.mem_iUnion.mpr ⟨i, hm⟩)⟩)
    have hbL : ∀ ι i, h ∉ bL ι i := fun ι i hm =>
      hb (Set.mem_iUnion.mpr ⟨ι, Or.inr (Set.mem_iUnion.mpr ⟨i, hm⟩)⟩)
    have h1 := PB_evalH_le R e κ h ((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * (Bd_eta e)⁻¹))
      (Cbig * (N : ℝ) ^ τ'') (Bd_eta e)⁻¹ (opNorm e.A) (by positivity) (fun ι p hp => by
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
        refine (hbW2 ι i h (hbW ι i)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hzi := hηz' (R.weights.get i).1
        have hzp := (hz (R.weights.get i).1).2.1
        rw [abs_of_pos hzp, one_div, mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hη' hzi) (by positivity))
      (fun ι w hw => by
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
        exact hbL2 ι i h hh (hbL ι i))
    rw [hnS, hLS] at h1
    refine h1.trans ?_
    rw [hRHS']
    exact PB_good_arith D N (by omega) R.cf R.dexp R.S R.nb u n Sa d Cbig Tt (Bd_eta e) τ' τ''
      (opNorm e.A) E hd hEd hη' hηT hTt1 hCbig0 hττ hlarge1
  have hRb0 : 0 ≤ Rb := by positivity
  -- integrate
  have hpt : ∀ᵐ h ∂μ, ‖R.evalH e κ h‖ ≤
      1 / 2 * RHS + (toMeasurable μ bad).indicator (fun _ => Rb) h := by
    filter_upwards [hμ.herm] with h hh
    by_cases hb : h ∈ toMeasurable μ bad
    · rw [Set.indicator_of_mem hb]
      have hRHS0 : 0 ≤ RHS := by
        rw [hRHS']
        have := Bd_zpow_lower (Bd_eta e) Tt N hη' hTt1 (by linarith) hη1 hηT (-E)
        have h2 : 0 ≤ (N : ℝ) ^ (-(R.S + (u : ℤ))) := by positivity
        have h3 : 0 ≤ Bd_eta e ^ (-E) := le_trans (by positivity) this
        positivity
      exact (hcrude h hh).trans (by linarith)
    · rw [Set.indicator_of_notMem hb, add_zero]
      exact hgood h hh fun h' => hb (subset_toMeasurable _ _ h')
  have hint : Integrable (fun h => 1 / 2 * RHS + (toMeasurable μ bad).indicator (fun _ => Rb) h)
      μ := (integrable_const _).add
        ((integrable_const Rb).indicator (measurableSet_toMeasurable _ _))
  refine (norm_integral_le_of_norm_le hint hpt).trans ?_
  rw [integral_add (integrable_const _)
    ((integrable_const Rb).indicator (measurableSet_toMeasurable _ _)), integral_const,
    integral_indicator_const _ (measurableSet_toMeasurable _ _), probReal_univ, one_smul,
    smul_eq_mul]
  have hreal : μ.real (toMeasurable μ bad) = μ.real bad := by
    simp only [Measure.real, measure_toMeasurable]
  rw [hreal]
  have hbadb : μ.real bad * Rb ≤ 1 / 2 * RHS := by
    rw [mul_comm, hRHS']
    exact PB_bad_arith D N (by omega) R.cf R.dexp R.S R.nb u n Ltot Dn Sa QL Tt (Bd_eta e) τ'
      (opNorm e.A) (μ.real bad) E hDn hη' hη1 hηT hTt1 hτ' hmbad hlarge2
  linarith


end RBMTransitionEdge

end
