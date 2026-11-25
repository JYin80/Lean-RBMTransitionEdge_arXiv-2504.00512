module

public import RBMTransitionEdge.LocalLaw.LocalLaw
public import RBMTransitionEdge.Localized.Expansion.Poly
public import RBMTransitionEdge.Localized.Expansion.Terminate

@[expose] public section

/-!
# The Gaussian step and the tree sum of the expansion of §5.3

The expansion (5.40) [expansion_for_integral_by_part_term] in expectation, with the remainder
terms of (5.41) [reminder_terms_expansion], and its sum over the rounds of the expansion from the
starting loop (5.30) [starting_point_of_expansion].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Products and sums over lists -/

/-- A product over a list is the product over the range of its positions. -/
private lemma GS_prod_list {α : Type*} (f : α → ℂ) (d : α) :
    ∀ l : List α, (l.map f).prod = ∏ k ∈ Finset.range l.length, f (l.getD k d)
  | [] => by simp
  | x :: l => by
      rw [List.length_cons, Finset.prod_range_succ', List.map_cons, List.prod_cons,
        GS_prod_list f d l]
      simp [mul_comm]

/-- A product over a list with the entry `j` erased is the product over the other positions. -/
private lemma GS_prod_eraseIdx {α : Type*} (f : α → ℂ) (d : α) :
    ∀ (l : List α) (j : ℕ), j < l.length →
      ((l.eraseIdx j).map f).prod = ∏ k ∈ (Finset.range l.length).erase j, f (l.getD k d)
  | [], j, h => by simp at h
  | x :: l, 0, _ => by
      rw [List.eraseIdx_cons_zero, GS_prod_list f d l, List.length_cons, Finset.range_add_one',
        Finset.erase_insert (by simp), Finset.prod_map]
      exact Finset.prod_congr rfl fun k _ => rfl
  | x :: l, j + 1, h => by
      have hj : j < l.length := by simpa using h
      have e := Finset.map_erase ⟨fun i : ℕ => i + 1, fun a b h => by simpa using h⟩
        (Finset.range l.length) j
      rw [List.eraseIdx_cons_succ, List.map_cons, List.prod_cons, GS_prod_eraseIdx f d l j hj,
        List.length_cons, Finset.range_add_one', Finset.erase_insert_of_ne (by omega),
        Finset.prod_insert (by simp)]
      erw [← e]
      rw [Finset.prod_map]
      exact congrArg₂ _ rfl (Finset.prod_congr rfl fun k _ => rfl)

/-- The entries of a list after `set`. -/
private lemma GS_getD_set {α : Type*} (l : List α) (ℓ : ℕ) (hℓ : ℓ < l.length) (x d : α) (k : ℕ) :
    (l.set ℓ x).getD k d = if k = ℓ then x else l.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases hk : k = ℓ
  · subst hk; simp [hℓ]
  · simp [hk, Ne.symm hk]

/-- A sum over `List.range` is a sum over `Finset.range`. -/
private lemma GS_sum_range {β : Type*} [AddCommMonoid β] (f : ℕ → β) :
    ∀ n, ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, GS_sum_range f n,
        Finset.sum_range_succ]
      simp

/-- A sum over a `filterMap` list. -/
private lemma GS_sum_filterMap {α β : Type*} (g : α → Option β) (F : β → ℂ) :
    ∀ l : List α, ((l.filterMap g).map F).sum = (l.map fun x => (g x).elim 0 F).sum
  | [] => by simp
  | x :: l => by
      rw [List.filterMap_cons]
      cases hx : g x with
      | none => simp [GS_sum_filterMap g F l, hx]
      | some y => simp [GS_sum_filterMap g F l, hx]

/-- A sum over a `flatMap` list. -/
private lemma GS_sum_flatMap {α β : Type*} (g : α → List β) (F : β → ℂ) :
    ∀ l : List α, ((l.flatMap g).map F).sum = (l.map fun x => ((g x).map F).sum).sum
  | [] => by simp
  | x :: l => by
      rw [List.flatMap_cons, List.map_append, List.sum_append, GS_sum_flatMap g F l]
      simp

/-! ### Words, the decomposition (5.38) and the bound block indices -/

section Words

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of a word with one more letter in front. -/
private lemma GS_word_cons (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (x : LoopLetter) (w : List LoopLetter) :
    loopWordMat G M E L (x :: w) = loopWordMat G M E L [x] * loopWordMat G M E L w := by
  simp [loopWordMat]

/-- The matrix of a word of at least two letters: the first letter split off. -/
private lemma GS_word_cons2 (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (x y : LoopLetter) (w : List LoopLetter) :
    loopWordMat G M E L (x :: y :: w) = loopWordMat G M E L [x] * loopWordMat G M E L (y :: w) := by
  simp [loopWordMat]

/-- The matrix of a concatenation of words is the product of the matrices. -/
private lemma GS_word_append (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (u v : List LoopLetter) :
    loopWordMat G M E L (u ++ v) = loopWordMat G M E L u * loopWordMat G M E L v := by
  simp [loopWordMat, List.prod_append]

/-- The matrices of the single letters. -/
private lemma GS_word_single (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) :
    (∀ a, loopWordMat G M E L [.res a] = G a) ∧ (∀ a, loopWordMat G M E L [.det a] = M a) ∧
      (∀ y, loopWordMat G M E L [.proj y] = E y) ∧ (∀ o, loopWordMat G M E L [.lamt o] = L) := by
  simp [loopWordMat]

/-- The matrix of a word depends on the projections only through the indices of its letters. -/
private lemma GS_word_congrE (G M : Fin 2 → Matrix ι ι ℂ) (E E' : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) : ∀ w : List LoopLetter, (∀ y, LoopLetter.proj y ∈ w → E y = E' y) →
      loopWordMat G M E L w = loopWordMat G M E' L w
  | [], _ => rfl
  | x :: w, h => by
      rw [GS_word_cons, GS_word_cons G M E', GS_word_congrE G M E E' L w
        fun y hy => h y (List.mem_cons_of_mem _ hy)]
      cases x with
      | proj y => simp [loopWordMat, h y List.mem_cons_self]
      | _ => rfl

/-- The trace of a word is invariant under rotation of the word. -/
private lemma GS_trace_rotate (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (w : List LoopLetter) (r : ℕ) :
    (loopWordMat G M E L (w.rotate r)).trace = (loopWordMat G M E L w).trace := by
  rw [List.rotate_eq_drop_append_take_mod, GS_word_append, Matrix.trace_mul_comm, ← GS_word_append,
    List.take_append_drop]

end Words

/-- The decomposition (5.38) [explicit_cT] returned by `focus`: the focused loop `w` rotates to
`𝒢_a · tl`. -/
private lemma GS_focus {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ w : List LoopLetter, T.loops[ℓ]? = some w ∧ ∃ r : ℕ, w.rotate r = .res a :: tl := by
  unfold LoopExpr.focus at h
  dsimp only at h
  generalize (if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = o at h
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i a' tl' hrot
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨w, hw, r, hrot⟩
        · cases h
      · cases h

/-- In the class (5.33) [definition_class_of_expression_loop] every block index of a loop or of a
light weight is bound. -/
private lemma GS_wf_bound {T : LoopExpr} (hT : T.wf = true) :
    (∀ w ∈ T.loops, ∀ y, LoopLetter.proj y ∈ w → y < T.nb) ∧ ∀ p ∈ T.weights, p.2 < T.nb := by
  simp only [LoopExpr.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨-, h4⟩, h5⟩ := hT
  refine ⟨fun w hw y hy => ?_, h5⟩
  simpa using h4 w hw _ hy

/-- A sum over the values of `nb + 1` bound block indices: the last index separately. -/
private lemma GS_sum_snoc {D nb : ℕ} (F : (Fin (nb + 1) → Fin D) → ℂ) :
    ∑ ι' : Fin (nb + 1) → Fin D, F ι' = ∑ ι : Fin nb → Fin D, ∑ x : Fin D, F (Fin.snoc ι x) := by
  rw [← (Fin.snocEquiv (fun _ => Fin D)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The block projections at the extended values of the bound block indices. -/
private lemma GS_E_snoc {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (x : Fin D) :
    (∀ y, y < nb → e.E (Fin.snoc (α := fun _ => Fin D) ι x) y = e.E ι y) ∧
      e.E (Fin.snoc (α := fun _ => Fin D) ι x) nb = Ea D N x := by
  refine ⟨fun y hy => ?_, ?_⟩
  · have h1 : y < nb + 1 := by omega
    simp only [LoopEnv.E, h1, hy, dite_true]
    have : (⟨y, h1⟩ : Fin (nb + 1)) = Fin.castSucc ⟨y, hy⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · simp only [LoopEnv.E, Nat.lt_succ_self, dite_true]
    have : (⟨nb, Nat.lt_succ_self nb⟩ : Fin (nb + 1)) = Fin.last nb := rfl
    rw [this, Fin.snoc_last]

/-! ### Wirtinger derivatives along the one-entry substitution -/

/-- `∂_w` (`b = false`) or `∂_{w̄}` (`b = true`) of Lemma 2.11 [lem:complex_cumu]. -/
private def GS_d : Bool → (ℂ → ℂ) → ℂ → ℂ
  | false => dW
  | true => dWbar

/-- `f` is real-differentiable everywhere and `GS_d b f = g`. -/
private def GS_has (b : Bool) (f g : ℂ → ℂ) : Prop :=
  (∀ w, DifferentiableAt ℝ f w) ∧ ∀ w, GS_d b f w = g w

/-- A constant has derivative `0`. -/
private lemma GS_has_const (b : Bool) (c : ℂ) : GS_has b (fun _ => c) (fun _ => 0) := by
  refine ⟨fun w => differentiableAt_const c, fun w => ?_⟩
  cases b <;> simp [GS_d, dW, dWbar]

/-- The derivative of a sum. -/
private lemma GS_has_add {b : Bool} {f g f' g' : ℂ → ℂ} (hf : GS_has b f f') (hg : GS_has b g g') :
    GS_has b (fun w => f w + g w) (fun w => f' w + g' w) := by
  refine ⟨fun w => (hf.1 w).add (hg.1 w), fun w => ?_⟩
  beta_reduce
  rw [← hf.2 w, ← hg.2 w]
  have e : fderiv ℝ (fun w => f w + g w) w = fderiv ℝ f w + fderiv ℝ g w :=
    fderiv_add (hf.1 w) (hg.1 w)
  cases b <;> simp only [GS_d, dW, dWbar, e, _root_.add_apply] <;> ring

/-- The derivative of a product. -/
private lemma GS_has_mul {b : Bool} {f g f' g' : ℂ → ℂ} (hf : GS_has b f f') (hg : GS_has b g g') :
    GS_has b (fun w => f w * g w) (fun w => f' w * g w + f w * g' w) := by
  refine ⟨fun w => (hf.1 w).mul (hg.1 w), fun w => ?_⟩
  beta_reduce
  rw [← hf.2 w, ← hg.2 w]
  have e := dW_mul (hf.1 w) (hg.1 w)
  cases b
  · exact e.1
  · exact e.2

/-- The derivative of a constant multiple. -/
private lemma GS_has_cmul {b : Bool} {f f' : ℂ → ℂ} (c : ℂ) (hf : GS_has b f f') :
    GS_has b (fun w => c * f w) (fun w => c * f' w) := by
  have := GS_has_mul (GS_has_const b c) hf
  refine ⟨this.1, fun w => ?_⟩
  rw [this.2 w]
  ring

/-- The derivative of a difference. -/
private lemma GS_has_sub {b : Bool} {f g f' g' : ℂ → ℂ} (hf : GS_has b f f') (hg : GS_has b g g') :
    GS_has b (fun w => f w - g w) (fun w => f' w - g' w) := by
  have := GS_has_add hf (GS_has_cmul (-1) hg)
  refine ⟨fun w => ?_, fun w => ?_⟩
  · have e : (fun w => f w - g w) = fun w => f w + -1 * g w := by funext w; ring
    rw [e]
    exact this.1 w
  · have e : (fun w => f w - g w) = fun w => f w + -1 * g w := by funext w; ring
    rw [e, this.2 w]
    ring

/-- The derivative of a finite sum. -/
private lemma GS_has_sum {b : Bool} {κ : Type*} (S : Finset κ) {f f' : κ → ℂ → ℂ}
    (hf : ∀ k ∈ S, GS_has b (f k) (f' k)) :
    GS_has b (fun w => ∑ k ∈ S, f k w) (fun w => ∑ k ∈ S, f' k w) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GS_has_const b 0
  | insert a S ha ih =>
    have := GS_has_add (hf a (Finset.mem_insert_self a S))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using this

/-- The Leibniz rule for a finite product. -/
private lemma GS_has_prod {b : Bool} {κ : Type*} [DecidableEq κ] (S : Finset κ) {f f' : κ → ℂ → ℂ}
    (hf : ∀ k ∈ S, GS_has b (f k) (f' k)) :
    GS_has b (fun w => ∏ k ∈ S, f k w)
      (fun w => ∑ k ∈ S, f' k w * ∏ k' ∈ S.erase k, f k' w) := by
  induction S using Finset.induction_on with
  | empty => simpa using GS_has_const b 1
  | insert a S ha ih =>
    have h := GS_has_mul (hf a (Finset.mem_insert_self a S))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    refine ⟨fun w => ?_, fun w => ?_⟩
    · simpa [Finset.prod_insert ha] using h.1 w
    · have e : (fun w => ∏ k ∈ insert a S, f k w) = fun w => f a w * ∏ k ∈ S, f k w := by
        funext w; rw [Finset.prod_insert ha]
      rw [e, h.2 w]
      beta_reduce
      rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      rw [Finset.erase_insert_of_ne (Ne.symm hka), Finset.prod_insert (fun h => ha
        (Finset.mem_of_mem_erase h))]
      ring

section Mat

variable {ι : Type*}

/-- Every entry of `F` has derivative the entry of `F'`. -/
private def GS_hasM (b : Bool) (F F' : ℂ → Matrix ι ι ℂ) : Prop :=
  ∀ k l, GS_has b (fun w => F w k l) (fun w => F' w k l)

/-- A constant matrix has derivative `0`. -/
private lemma GS_hasM_const (b : Bool) (A : Matrix ι ι ℂ) :
    GS_hasM b (fun _ => A) (fun _ => 0) := fun k l => by
  simpa using GS_has_const b (A k l)

/-- The derivative of a product of matrices. -/
private lemma GS_hasM_mul [Fintype ι] {b : Bool} {F G F' G' : ℂ → Matrix ι ι ℂ}
    (hF : GS_hasM b F F') (hG : GS_hasM b G G') :
    GS_hasM b (fun w => F w * G w) (fun w => F' w * G w + F w * G' w) :=
  fun k l => by
    have := GS_has_sum (Finset.univ : Finset ι) (fun m _ => GS_has_mul (hF k m) (hG m l))
    simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using this

/-- The derivative of a difference of matrices. -/
private lemma GS_hasM_sub {b : Bool} {F G F' G' : ℂ → Matrix ι ι ℂ} (hF : GS_hasM b F F')
    (hG : GS_hasM b G G') : GS_hasM b (fun w => F w - G w) (fun w => F' w - G' w) :=
  fun k l => by simpa using GS_has_sub (hF k l) (hG k l)

/-- The derivative of a normalized trace. -/
private lemma GS_has_ntr [Fintype ι] {b : Bool} {F F' : ℂ → Matrix ι ι ℂ} (hF : GS_hasM b F F') :
    GS_has b (fun w => ntr (F w)) (fun w => ntr (F' w)) := by
  have := GS_has_cmul ((Fintype.card ι : ℂ))⁻¹
    (GS_has_sum (Finset.univ : Finset ι) (fun k _ => hF k k))
  simpa [ntr, Matrix.trace] using this

/-- The term of the derivative of a word at the position `q`: the letter `𝒢_b` at `q` replaced by
`G' b`. -/
private def GS_posD [Fintype ι] [DecidableEq ι] (G G' M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (w : List LoopLetter) (q : ℕ) : Matrix ι ι ℂ :=
  match w[q]? with
  | some (.res b) => loopWordMat G M E L (w.take q) * G' b * loopWordMat G M E L (w.drop (q + 1))
  | _ => 0

/-- The derivative of a word: the sum over the positions of its resolvents. -/
private def GS_wordD [Fintype ι] [DecidableEq ι] (G G' M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (w : List LoopLetter) : Matrix ι ι ℂ :=
  ∑ q ∈ Finset.range w.length, GS_posD G G' M E L w q

/-- The derivative of a single letter. -/
private def GS_letD (G' : Fin 2 → Matrix ι ι ℂ) : LoopLetter → Matrix ι ι ℂ
  | .res b => G' b
  | _ => 0

/-- The Leibniz rule for a word with one more letter in front. -/
private lemma GS_wordD_cons [Fintype ι] [DecidableEq ι] (G G' M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (x : LoopLetter) (w : List LoopLetter) :
    GS_wordD G G' M E L (x :: w) = GS_letD G' x * loopWordMat G M E L w +
      loopWordMat G M E L [x] * GS_wordD G G' M E L w := by
  have h1 : ∀ q, GS_posD G G' M E L (x :: w) (q + 1) =
      loopWordMat G M E L [x] * GS_posD G G' M E L w q := by
    intro q
    unfold GS_posD
    simp only [List.getElem?_cons_succ, List.take_succ_cons, List.drop_succ_cons]
    cases hq : w[q]? with
    | none => simp
    | some y =>
      cases y with
      | res b => simp only; rw [GS_word_cons G M E L x (w.take q)]; simp only [Matrix.mul_assoc]
      | _ => simp
  have h0 : GS_posD G G' M E L (x :: w) 0 = GS_letD G' x * loopWordMat G M E L w := by
    unfold GS_posD
    cases x <;> simp [GS_letD, loopWordMat]
  unfold GS_wordD
  rw [List.length_cons, Finset.sum_range_succ', Finset.sum_congr rfl (fun q _ => h1 q),
    ← Finset.mul_sum, h0, add_comm]

/-- The derivative of a word whose resolvents have derivatives `G'`. -/
private lemma GS_hasM_word [Fintype ι] [DecidableEq ι] {b : Bool} (G G' : ℂ → Fin 2 → Matrix ι ι ℂ)
    (M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (hG : ∀ a, GS_hasM b (fun w => G w a) (fun w => G' w a)) :
    ∀ l : List LoopLetter, GS_hasM b (fun w => loopWordMat (G w) M E L l)
      (fun w => GS_wordD (G w) (G' w) M E L l)
  | [] => fun k k' => by
      simpa [loopWordMat, GS_wordD] using GS_has_const b ((1 : Matrix ι ι ℂ) k k')
  | x :: l => by
      have ih := GS_hasM_word G G' M E L hG l
      have hx : GS_hasM b (fun w => loopWordMat (G w) M E L [x]) (fun w => GS_letD (G' w) x) := by
        cases x with
        | res a => simpa [loopWordMat, GS_letD] using hG a
        | det a => simpa [loopWordMat, GS_letD] using GS_hasM_const b (M a)
        | proj y => simpa [loopWordMat, GS_letD] using GS_hasM_const b (E y)
        | lamt o => simpa [loopWordMat, GS_letD] using GS_hasM_const b L
      have := GS_hasM_mul hx ih
      intro k k'
      simpa [GS_word_cons _ M E L x l, GS_wordD_cons] using this k k'

end Mat

/-- `GS_has` for functions and derivatives that agree pointwise with given ones. -/
private lemma GS_has_congr {b : Bool} {f f₁ g g₁ : ℂ → ℂ} (hf : ∀ w, f w = f₁ w)
    (hg : ∀ w, g w = g₁ w) (h : GS_has b f₁ g₁) : GS_has b f g := by
  have e : f = f₁ := funext hf
  subst e
  exact ⟨h.1, fun w => (h.2 w).trans (hg w).symm⟩

/-! ### The derivative of `(F 𝒢)_{ij} W ⋯ f ⋯` in the entry `(i, j)` -/

/-- An entry of `A (c E_{ij}) B`. -/
private lemma GS_single_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (i j k l : ι) (c : ℂ) :
    (A * (c • Matrix.single i j (1 : ℂ)) * B) k l = c * (A k i * B j l) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_and]
  simp [Finset.sum_ite_eq]

/-- The one-entry substitution is a smooth function of the new value. -/
private lemma GS_contDiff_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (n : WithTop ℕ∞) : ContDiff ℝ n (fun w : ℂ => setEntry h i j w) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hre : ContDiff ℝ n (fun w : ℂ => ((w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
  have hcw : ContDiff ℝ n (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.contDiff
  simp only [setEntry]
  split_ifs
  · exact hre
  · exact contDiff_const
  · exact contDiff_id
  · exact hcw
  · exact contDiff_const

/-- For a Hermitian array the substituted array is its own Hermitian part. -/
private lemma GS_symArr_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    symArr (setEntry h i j w) = setEntry h i j w := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- A substitution in a Hermitian array is Hermitian. -/
private lemma GS_setEntry_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  rw [← GS_symArr_setEntry h hh i j w]
  exact symArr_isHermitian _

/-- The slot deformation `c_a Λ` is Hermitian. -/
private lemma GS_slot_herm {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) :
    ((e.c a : ℂ) • lam D N e.A).IsHermitian := by
  have := lam_isHermitian D N e.A
  unfold Matrix.IsHermitian at this ⊢
  rw [Matrix.conjTranspose_smul, this]
  simp

/-- The spectral parameter of the slot `a`, `z_a` or `z̄_a`, is not real. -/
private lemma GS_slot_im {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (a : Fin 2) :
    (if e.s a then star (e.z a) else e.z a).im ≠ 0 := by
  split_ifs
  · simpa using (hz a).ne'
  · exact (hz a).ne'

/-- The direction `c E_{ij}` (`b = false`) or `c E_{ji}` (`b = true`) of the derivatives of a
resolvent in `res_dW`, `c = 1/2` on the diagonal and `1` off it. -/
private def GS_dir {D N : ℕ} (i j : Idx D N) : Bool → Matrix (Idx D N) (Idx D N) ℂ
  | false => (if i = j then (1 / 2 : ℂ) else 1) • Matrix.single i j 1
  | true => (if i = j then (1 / 2 : ℂ) else 1) • Matrix.single j i 1

/-- The derivative `-𝒢_a Δ 𝒢_a` of the resolvent of the slot `a` in the direction `Δ`. -/
private def GS_dG {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (Δ : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin 2) : Matrix (Idx D N) (Idx D N) ℂ :=
  -(e.G h a * Δ * e.G h a)

/-- The derivatives `∂_w 𝒢 = -𝒢 (c E_{ij}) 𝒢` and `∂_{w̄} 𝒢 = -𝒢 (c E_{ji}) 𝒢` of the resolvent
of a slot along the one-entry substitution in a Hermitian array. -/
private lemma GS_hasM_res {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (b : Bool)
    (a : Fin 2) :
    GS_hasM b (fun w => e.G (setEntry h i j w) a)
      (fun w => GS_dG e (setEntry h i j w) (GS_dir i j b) a) := by
  intro k l
  obtain ⟨d1, d2⟩ := res_dW ((e.c a : ℂ) • lam D N e.A) (GS_slot_herm e a) _ (GS_slot_im e hz a)
    h hh i j k l
  have hd : ∀ w, DifferentiableAt ℝ (fun w => e.G (setEntry h i j w) a k l) w := by
    intro w
    have e1 : (fun w => e.G (setEntry h i j w) a k l) = (fun h' : Idx D N → Idx D N → ℂ =>
        res (Matrix.of (symArr h') + (e.c a : ℂ) • lam D N e.A)
          (if e.s a then star (e.z a) else e.z a) k l) ∘ fun w => setEntry h i j w := by
      funext w
      simp only [Function.comp, GS_symArr_setEntry h hh i j w, LoopEnv.G]
    rw [e1]
    exact ((contDiff_res_symArr _ (GS_slot_herm e a) _ (GS_slot_im e hz a) k l 1).comp
      (GS_contDiff_setEntry h i j 1)).differentiable (by norm_num) w
  refine ⟨hd, fun w => ?_⟩
  cases b
  · have := congrFun d1 w
    simp only [GS_d, LoopEnv.G] at this ⊢
    rw [this, GS_dG, GS_dir, Matrix.neg_apply, GS_single_entry]
    simp only [LoopEnv.G]
    ring
  · have := congrFun d2 w
    simp only [GS_d, LoopEnv.G] at this ⊢
    rw [this, GS_dG, GS_dir, Matrix.neg_apply, GS_single_entry]
    simp only [LoopEnv.G]
    ring

/-- The value of a light weight `⟨(𝒢_b - 𝔐_b) E_y⟩` at the array `h`. -/
private def GS_wv {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : Fin 2 × ℕ) : ℂ :=
  ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)

/-- The derivative of a light weight in the direction `Δ`. -/
private def GS_wd {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (Δ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ) (p : Fin 2 × ℕ) : ℂ :=
  ntr (GS_dG e h Δ p.1 * e.E ι p.2)

/-- The value of a loop `⟨w⟩` at the array `h`. -/
private def GS_lv {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (w : List LoopLetter) : ℂ :=
  ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)

/-- The derivative of a loop in the direction `Δ`. -/
private def GS_ld {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (Δ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ) (w : List LoopLetter) : ℂ :=
  ntr (GS_wordD (e.G h) (GS_dG e h Δ) e.M (e.E ι) e.Lt w)

/-- The product `W₁ ⋯ W_u` of the light weights of an expression at the array `h`. -/
private def GS_Wt {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (ι : Fin T.nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ∏ k ∈ Finset.range T.weights.length, GS_wv e ι h (T.weights.getD k (0, 0))

/-- The product of the loops of an expression other than the loop at position `ℓ`. -/
private def GS_Lr {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (ι : Fin T.nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (ℓ : ℕ) : ℂ :=
  ∏ k ∈ (Finset.range T.loops.length).erase ℓ, GS_lv e ι h (T.loops.getD k [])

/-- The derivative of `(F 𝒢)_{ij} W₁ ⋯ W_u f^{(1)} ⋯ f^{(n-1)}` of (5.41)
[reminder_terms_expansion] in the direction `Δ`, by the Leibniz rule. -/
private def GS_pkgD {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (ι : Fin T.nb → Fin D)
    (i j : Idx D N) (Δ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  match T.focus with
  | none => 0
  | some (ℓ, a, tl) =>
    (e.M a * GS_wordD (e.G h) (GS_dG e h Δ) e.M (e.E ι) e.Lt tl * e.G h a) i j *
      GS_Wt T e ι h * GS_Lr T e ι h ℓ +
    (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * GS_dG e h Δ a) i j *
      GS_Wt T e ι h * GS_Lr T e ι h ℓ +
    (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a) i j *
      (∑ k ∈ Finset.range T.weights.length, GS_wd e ι Δ h (T.weights.getD k (0, 0)) *
        ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0))) *
      GS_Lr T e ι h ℓ +
    (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a) i j * GS_Wt T e ι h *
      (∑ k ∈ (Finset.range T.loops.length).erase ℓ, GS_ld e ι Δ h (T.loops.getD k []) *
        ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
          GS_lv e ι h (T.loops.getD k' []))

/-- `pkgVal` with the products written over positions. -/
private lemma GS_pkgVal_eq {D N : ℕ} (T : LoopExpr) {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N) (ι : Fin T.nb → Fin D) (i j : Idx D N)
    (h : Idx D N → Idx D N → ℂ) :
    T.pkgVal e ι i j h = (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a) i j *
      GS_Wt T e ι h * GS_Lr T e ι h ℓ := by
  obtain ⟨w, hw, -⟩ := GS_focus hf
  have hℓ : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have e1 : T.pkgVal e ι i j h =
      loopWordMat (e.G h) e.M (e.E ι) e.Lt (.det a :: tl ++ [.res a]) i j *
        (T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
        ((T.loops.eraseIdx ℓ).map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod := by
    unfold LoopExpr.pkgVal
    rw [hf]
  have e2 : loopWordMat (e.G h) e.M (e.E ι) e.Lt (.det a :: tl ++ [.res a]) =
      e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a := by
    rw [GS_word_append (e.G h) e.M (e.E ι) e.Lt (.det a :: tl) [.res a],
      GS_word_cons (e.G h) e.M (e.E ι) e.Lt (.det a) tl]
    simp only [GS_word_single]
  rw [e1, GS_prod_list _ (0, 0), GS_prod_eraseIdx _ [] _ _ hℓ]
  simp only [e2, GS_wv, GS_lv, GS_Wt, GS_Lr]

/-- The derivatives `∂_w`, `∂_{w̄}` of `(F 𝒢)_{ij} W ⋯ f ⋯` along the substitution of the entry
`(i, j)` of a Hermitian array are its Leibniz derivatives in the directions of `res_dW`. -/
private lemma GS_pkgVal_d {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (ι : Fin T.nb → Fin D)
    (i j : Idx D N) (b : Bool) (w : ℂ) :
    GS_d b (fun w => T.pkgVal e ι i j (setEntry h i j w)) w =
      GS_pkgD T e ι i j (GS_dir i j b) (setEntry h i j w) := by
  rcases hf : T.focus with _ | ⟨ℓ, a, tl⟩
  · have e1 : (fun w => T.pkgVal e ι i j (setEntry h i j w)) = fun _ => 0 := by
      funext w; simp [LoopExpr.pkgVal, hf]
    rw [e1, (GS_has_const b 0).2 w]
    simp [GS_pkgD, hf]
  · have hG := fun a => GS_hasM_res e hz h hh i j b a
    have hW := GS_hasM_word (fun w => e.G (setEntry h i j w))
      (fun w a => GS_dG e (setEntry h i j w) (GS_dir i j b) a) e.M (e.E ι) e.Lt hG
    have hF := GS_hasM_mul (GS_hasM_mul (GS_hasM_const b (e.M a)) (hW tl)) (hG a) i j
    have hwt : ∀ p : Fin 2 × ℕ, GS_has b (fun w => GS_wv e ι (setEntry h i j w) p)
        (fun w => GS_wd e ι (GS_dir i j b) (setEntry h i j w) p) := by
      intro p
      refine GS_has_congr (fun w => rfl) (fun w => ?_) (GS_has_ntr (GS_hasM_mul
        (GS_hasM_sub (hG p.1) (GS_hasM_const b (e.M p.1))) (GS_hasM_const b (e.E ι p.2))))
      simp [GS_wd]
    have hlv : ∀ w' : List LoopLetter, GS_has b (fun w => GS_lv e ι (setEntry h i j w) w')
        (fun w => GS_ld e ι (GS_dir i j b) (setEntry h i j w) w') := fun w' => GS_has_ntr (hW w')
    have hall := GS_has_mul (GS_has_mul hF
      (GS_has_prod (Finset.range T.weights.length) fun k _ => hwt (T.weights.getD k (0, 0))))
      (GS_has_prod ((Finset.range T.loops.length).erase ℓ) fun k _ => hlv (T.loops.getD k []))
    refine (GS_has_congr (g := fun w => GS_pkgD T e ι i j (GS_dir i j b) (setEntry h i j w))
      (fun w => GS_pkgVal_eq T hf e ι i j _) (fun w => ?_) hall).2 w
    simp only [GS_pkgD, hf, GS_Wt, GS_Lr]
    simp only [zero_mul, zero_add, Matrix.add_apply, Matrix.mul_assoc]
    ring

/-- The Leibniz derivative of `(F 𝒢)_{ij} W ⋯ f ⋯` is linear in the direction. -/
private lemma GS_pkgD_smul {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (ι : Fin T.nb → Fin D)
    (i j : Idx D N) (c : ℂ) (Δ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ) :
    GS_pkgD T e ι i j (c • Δ) h = c * GS_pkgD T e ι i j Δ h := by
  have hdG : GS_dG e h (c • Δ) = fun a => c • GS_dG e h Δ a := by
    funext a
    simp only [GS_dG, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hWD : ∀ w, GS_wordD (e.G h) (GS_dG e h (c • Δ)) e.M (e.E ι) e.Lt w =
      c • GS_wordD (e.G h) (GS_dG e h Δ) e.M (e.E ι) e.Lt w := by
    intro w
    unfold GS_wordD
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold GS_posD
    split
    · rw [hdG]; simp only [Matrix.mul_smul, Matrix.smul_mul]
    · simp
  have hwd : ∀ p, GS_wd e ι (c • Δ) h p = c * GS_wd e ι Δ h p := by
    intro p
    simp only [GS_wd, hdG, Matrix.smul_mul, ntr, Matrix.trace_smul, smul_eq_mul]
    ring
  have hld : ∀ w, GS_ld e ι (c • Δ) h w = c * GS_ld e ι Δ h w := by
    intro w
    simp only [GS_ld, hWD, ntr, Matrix.trace_smul, smul_eq_mul]
    ring
  unfold GS_pkgD
  split
  · simp
  · simp only [hWD]
    simp only [hwd, hld, hdG, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
    ring

/-! ### Sums over the entries of a block -/

/-- A sum over the pairs of entries in the same block is a sum over the blocks. -/
private lemma GS_sum_block {D N : ℕ} (f : Idx D N → Idx D N → ℂ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then f i j else 0) =
      ∑ x : Fin D, ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) * f i j := by
  symm
  calc ∑ x : Fin D, ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) * f i j
      = ∑ i : Idx D N, ∑ x : Fin D, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) * f i j :=
        Finset.sum_comm
    _ = ∑ i : Idx D N, ∑ j : Idx D N, ∑ x : Fin D, (Ea D N x i i * Ea D N x j j) * f i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  have e1 : ∑ x : Fin D, Ea D N x i i * Ea D N x j j = if i.1 = j.1 then 1 else 0 := by
    simp only [Ea, Matrix.diagonal_apply_eq, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [eq_comm]
  rw [e1]
  split_ifs <;> simp

/-- `Σ_{i,j ∈ 𝓘_x} (P E_{ij} Q)_{ij} = Tr(P E_x) Tr(Q E_x)`. -/
private lemma GS_block_entry {D N : ℕ} (x : Fin D) (P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      (P * Matrix.single i j (1 : ℂ) * Q) i j = (P * Ea D N x).trace * (Q * Ea D N x).trace := by
  have e1 : ∀ i j, (P * Matrix.single i j (1 : ℂ) * Q) i j = P i i * Q j j := by
    intro i j
    have := GS_single_entry P Q i j i j 1
    simpa using this
  simp only [e1, Matrix.trace, Matrix.diag, Ea, Matrix.mul_diagonal, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diagonal_apply_eq]
  ring

/-- `Σ_{i,j ∈ 𝓘_x} Y_{ij} Tr(P E_{ij} Q) = Tr(Y E_x Q P E_x)`. -/
private lemma GS_block_trace {D N : ℕ} (x : Fin D) (Y P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      (Y i j * (P * Matrix.single i j (1 : ℂ) * Q).trace) =
      (Y * Ea D N x * (Q * P) * Ea D N x).trace := by
  have e1 : ∀ i j, (P * Matrix.single i j (1 : ℂ) * Q).trace = (Q * P) j i := by
    intro i j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
    simp [Finset.sum_ite_eq, ite_and]
  simp only [e1]
  generalize Q * P = R
  simp only [Matrix.trace, Matrix.diag, Ea]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul]
  by_cases hi : i.1 = x <;> by_cases hj : j.1 = x <;> simp [hi, hj, mul_comm]

/-! ### The values of the terms of the five operations -/

/-- A product over a list after `set`. -/
private lemma GS_prod_set {α : Type*} (f : α → ℂ) (d : α) (l : List α) (ℓ : ℕ)
    (hℓ : ℓ < l.length) (x : α) :
    ((l.set ℓ x).map f).prod = f x * ∏ k ∈ (Finset.range l.length).erase ℓ, f (l.getD k d) := by
  rw [GS_prod_list f d, List.length_set, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hℓ)]
  congr 1
  · rw [GS_getD_set l ℓ hℓ x d]; simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [GS_getD_set l ℓ hℓ x d]; simp [Finset.ne_of_mem_erase hk]

/-- A product over a list after `set` at `ℓ` and `eraseIdx` at `j ≠ ℓ`. -/
private lemma GS_prod_set_eraseIdx {α : Type*} (f : α → ℂ) (d : α) (l : List α) (ℓ j : ℕ)
    (hℓ : ℓ < l.length) (hj : j < l.length) (hjℓ : j ≠ ℓ) (x : α) :
    (((l.set ℓ x).eraseIdx j).map f).prod =
      f x * ∏ k ∈ ((Finset.range l.length).erase ℓ).erase j, f (l.getD k d) := by
  rw [GS_prod_eraseIdx f d _ j (by simpa using hj), List.length_set,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hjℓ, Finset.mem_range.2 hℓ⟩),
    Finset.erase_right_comm]
  congr 1
  · rw [GS_getD_set l ℓ hℓ x d]; simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [GS_getD_set l ℓ hℓ x d]; simp [Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)]

/-- An entry of a list at a position below its length is a member. -/
private lemma GS_getD_mem {α : Type*} (l : List α) (d : α) (k : ℕ) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- The data of the decomposition (5.38) [explicit_cT] for an expression of the class: the
position of the focused loop, the bound block indices of `tl`, and the loop `⟨𝒢_a tl⟩` as the
focused loop. -/
private lemma GS_focus_data {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) :
    ℓ < T.loops.length ∧ (∀ y, LoopLetter.proj y ∈ tl → y < T.nb) ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
        (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ),
        (loopWordMat G M E L (T.loops.getD ℓ [])).trace = (G a * loopWordMat G M E L tl).trace := by
  obtain ⟨w, hw, r, hrot⟩ := GS_focus hf
  have hℓ : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hwm : w ∈ T.loops := List.mem_of_getElem? hw
  have hgw : T.loops.getD ℓ [] = w := by rw [List.getD_eq_getElem?_getD, hw]; rfl
  refine ⟨hℓ, fun y hy => (GS_wf_bound hT).1 w hwm y ?_, fun G M E L => ?_⟩
  · have : LoopLetter.proj y ∈ w.rotate r := by rw [hrot]; exact List.mem_cons_of_mem _ hy
    exact List.mem_rotate.1 this
  · rw [hgw, ← GS_trace_rotate G M E L w r, hrot, GS_word_cons]
    simp only [GS_word_single]

/-- The value of an expression with a focus: `c_𝒯 Σ_ι W ⋯ ⟨𝒢_a tl⟩ ⋯`. -/
private lemma GS_evalH_focus {D N : ℕ} {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) :
    T.evalH e h = (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D,
      GS_Wt T e ι h * ntr (e.G h a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl) *
        GS_Lr T e ι h ℓ := by
  obtain ⟨hℓ, -, htr⟩ := GS_focus_data hT hf
  unfold LoopExpr.evalH
  congr 1
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [GS_prod_list _ (0, 0), GS_prod_list _ [],
    ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hℓ)]
  simp only [GS_Wt, GS_Lr, GS_wv, GS_lv, ntr, htr]
  ring

/-- The term `𝔯` (5.42) [sreplace_def]: `c_𝒯 Σ_ι W ⋯ ⟨𝔐_a tl⟩ ⋯`. -/
private lemma GS_op_rep {D N : ℕ} {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) :
    ((T.apply .rep).map fun T' => T'.evalH e h).sum =
      (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D,
        GS_Wt T e ι h * ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl) *
          GS_Lr T e ι h ℓ := by
  obtain ⟨hℓ, -, -⟩ := GS_focus_data hT hf
  simp only [LoopExpr.apply, hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  unfold LoopExpr.evalH
  congr 1
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [GS_prod_list _ (0, 0), GS_prod_set _ [] _ _ hℓ, GS_word_cons]
  simp only [GS_Wt, GS_Lr, GS_wv, GS_lv, GS_word_single]
  ring

/-- The matrix of a word whose block indices are bound by the first `nb` indices does not see the
value of the index `nb`. -/
private lemma GS_W_snoc {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (x : Fin D)
    (h : Idx D N → Idx D N → ℂ) (w : List LoopLetter)
    (hw : ∀ y, LoopLetter.proj y ∈ w → y < nb) :
    loopWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt w =
      loopWordMat (e.G h) e.M (e.E ι) e.Lt w :=
  GS_word_congrE _ _ _ _ _ w fun y hy => (GS_E_snoc e ι x).1 y (hw y hy)

/-- The light weights at the extended values of the bound block indices. -/
private lemma GS_Wt_snoc {D N : ℕ} {T : LoopExpr} (hT : T.wf = true) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (x : Fin D) (h : Idx D N → Idx D N → ℂ) :
    (T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) *
      e.E (Fin.snoc (α := fun _ => Fin D) ι x) p.2)).prod = GS_Wt T e ι h := by
  rw [List.map_congr_left fun p hp => by rw [(GS_E_snoc e ι x).1 p.2 ((GS_wf_bound hT).2 p hp)],
    GS_prod_list _ (0, 0)]
  rfl

/-- The loops at the extended values of the bound block indices. -/
private lemma GS_lv_snoc {D N : ℕ} {T : LoopExpr} (hT : T.wf = true) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (x : Fin D) (h : Idx D N → Idx D N → ℂ) (k : ℕ)
    (hk : k < T.loops.length) :
    ntr (loopWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt
      (T.loops.getD k [])) = GS_lv e ι h (T.loops.getD k []) := by
  rw [GS_W_snoc e ι x h _ fun y hy => (GS_wf_bound hT).1 _ (GS_getD_mem _ _ k hk) y hy]
  rfl

/-- The trace is `DN` times the normalized trace. -/
private lemma GS_trace_ntr {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0)
    (X : Matrix (Idx D N) (Idx D N) ℂ) : X.trace = ((D : ℂ) * N) * ntr X := by
  have : ((Fintype.card (Idx D N) : ℕ) : ℂ) = (D : ℂ) * N := by
    simp [Fintype.card_prod]
  unfold ntr
  rw [this, ← mul_assoc, mul_inv_cancel₀ (by simp [hD, hN]), one_mul]

/-- The term `𝔠₁` (5.43) [scut1_def]: `D c_𝒯 Σ_ι Σ_x W ⋯ ⟨(𝒢_a - 𝔐_a) E_x⟩ ⟨F 𝒢_a E_x⟩ ⋯`. -/
private lemma GS_op_cut1 {D N : ℕ} (hD : D ≠ 0) {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) :
    ((T.apply .cut1).map fun T' => T'.evalH e h).sum =
      (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D,
        (D : ℂ) * GS_Wt T e ι h * ntr ((e.G h a - e.M a) * Ea D N x) *
          ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x) *
            GS_Lr T e ι h ℓ := by
  obtain ⟨hℓ, htl, -⟩ := GS_focus_data hT hf
  simp only [LoopExpr.apply, hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  unfold LoopExpr.evalH
  dsimp only
  rw [GS_sum_snoc, zpow_add_one₀ (Nat.cast_ne_zero.2 hD), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [List.map_append, List.prod_append, GS_Wt_snoc hT, GS_prod_set _ [] _ _ hℓ]
  rw [GS_word_append, GS_word_cons _ _ _ _ (.det a) tl, GS_W_snoc e ι x h tl htl,
    GS_word_cons _ _ _ _ (.res a) [.proj T.nb]]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    (GS_E_snoc e ι x).2, GS_word_single]
  have hL : ∏ k ∈ (Finset.range T.loops.length).erase ℓ,
      ntr (loopWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt
        (T.loops.getD k [])) = GS_Lr T e ι h ℓ :=
    Finset.prod_congr rfl fun k hk => GS_lv_snoc hT e ι x h k
      (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
  rw [hL]
  simp only [Matrix.mul_assoc]
  ring

/-- The pair of loops of the term `𝔠₂` (5.44) [scut_2] cut at the position `q` of `tl`:
`⟨𝔐_a tl[..q] 𝒢_b E_x⟩ ⟨𝒢_b tl[q+1..] 𝒢_a E_x⟩` when `tl[q] = 𝒢_b`, and `0` otherwise. -/
private def GS_c2 {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ)
    (a : Fin 2) (tl : List LoopLetter) (x : Fin D) (q : ℕ) : ℂ :=
  match tl[q]? with
  | some (.res b) => ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.take q) * e.G h b *
      Ea D N x) * ntr (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.drop (q + 1)) *
        e.G h a * Ea D N x)
  | _ => 0

/-- The terms `𝔠₂` (5.44) [scut_2]: `D c_𝒯 Σ_ι Σ_x W ⋯ Σ_q ⟨𝔐_a tl[..q] 𝒢_b E_x⟩
⟨𝒢_b tl[q+1..] 𝒢_a E_x⟩ ⋯`. -/
private lemma GS_op_cut2 {D N : ℕ} (hD : D ≠ 0) {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) :
    ((T.apply .cut2).map fun T' => T'.evalH e h).sum =
      (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D,
        (D : ℂ) * GS_Wt T e ι h * GS_Lr T e ι h ℓ *
          ∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q := by
  obtain ⟨hℓ, htl, -⟩ := GS_focus_data hT hf
  simp only [LoopExpr.apply, hf]
  rw [GS_sum_filterMap, GS_sum_range]
  set c := (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ with hc
  have hR : c * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D, (D : ℂ) * GS_Wt T e ι h * GS_Lr T e ι h ℓ *
      ∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q =
      ∑ q ∈ Finset.range tl.length, c * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D,
        (D : ℂ) * GS_Wt T e ι h * GS_Lr T e ι h ℓ * GS_c2 e ι h a tl x q := by
    rw [← Finset.mul_sum]
    congr 1
    calc ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D, (D : ℂ) * GS_Wt T e ι h * GS_Lr T e ι h ℓ *
          ∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q
        = ∑ ι : Fin T.nb → Fin D, ∑ q ∈ Finset.range tl.length, ∑ x : Fin D,
          (D : ℂ) * GS_Wt T e ι h * GS_Lr T e ι h ℓ * GS_c2 e ι h a tl x q := by
          refine Finset.sum_congr rfl fun ι _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
      _ = _ := Finset.sum_comm
  rw [hR]
  refine Finset.sum_congr rfl fun q hq => ?_
  rcases hq' : tl[q]? with _ | y
  · simp [hq', GS_c2]
  · cases y with
    | res b =>
      simp only [Option.elim]
      have hlt := (List.getElem?_eq_some_iff.1 hq').1
      have htake : tl.take (q + 1) = tl.take q ++ [.res b] := by
        rw [List.take_add_one, hq']; rfl
      have hdrop : tl.drop q = .res b :: tl.drop (q + 1) := by
        rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hq').2]
      have htk : ∀ y, LoopLetter.proj y ∈ tl.take q → y < T.nb :=
        fun y hy => htl y (List.mem_of_mem_take hy)
      have hdr : ∀ y, LoopLetter.proj y ∈ tl.drop (q + 1) → y < T.nb :=
        fun y hy => htl y (List.mem_of_mem_drop hy)
      unfold LoopExpr.evalH
      dsimp only
      rw [GS_sum_snoc, zpow_add_one₀ (Nat.cast_ne_zero.2 hD), hc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GS_Wt_snoc hT, List.map_append, List.prod_append, GS_prod_set _ [] _ _ hℓ]
      rw [GS_word_append, GS_word_cons _ _ _ _ (.det a) (tl.take (q + 1)), htake, GS_word_append,
        GS_W_snoc e ι x h _ htk]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [GS_word_append, GS_word_cons _ _ _ _ (.proj T.nb) (tl.drop q),
        hdrop, GS_word_cons _ _ _ _ (.res b) (tl.drop (q + 1)), GS_W_snoc e ι x h _ hdr]
      simp only [(GS_E_snoc e ι x).2, GS_word_single]
      have hL : ∏ k ∈ (Finset.range T.loops.length).erase ℓ,
          ntr (loopWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt
            (T.loops.getD k [])) = GS_Lr T e ι h ℓ :=
        Finset.prod_congr rfl fun k hk => GS_lv_snoc hT e ι x h k
          (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
      have hC : ntr (Ea D N x * (e.G h b * (loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.drop (q + 1)) *
          e.G h a))) = ntr (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.drop (q + 1)) *
            e.G h a * Ea D N x) := by
        unfold ntr
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      simp only [Matrix.mul_assoc] at hC ⊢
      rw [hL, hC]
      simp only [GS_c2, hq', Matrix.mul_assoc]
      ring
    | _ => simp [hq', GS_c2]

/-- The terms `𝔭₁` (5.45) [splug1_def]: `D⁻¹ N⁻² c_𝒯 Σ_ι Σ_x Σ_k ⟨F 𝒢_a E_x 𝒢_b E_y 𝒢_b E_x⟩
Π_{k' ≠ k} W_{k'} ⋯`, the light weight `(b, y)` at the position `k` plugged in. -/
private lemma GS_op_plug1 {D N : ℕ} (hD : D ≠ 0) {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) :
    ((T.apply .plug1).map fun T' => T'.evalH e h).sum =
      (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D,
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Lr T e ι h ℓ *
          ∑ k ∈ Finset.range T.weights.length,
            ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x *
              e.G h (T.weights.getD k (0, 0)).1 * e.E ι (T.weights.getD k (0, 0)).2 *
              e.G h (T.weights.getD k (0, 0)).1 * Ea D N x) *
            ∏ k' ∈ (Finset.range T.weights.length).erase k,
              GS_wv e ι h (T.weights.getD k' (0, 0)) := by
  obtain ⟨hℓ, htl, -⟩ := GS_focus_data hT hf
  simp only [LoopExpr.apply, hf]
  rw [GS_sum_filterMap, GS_sum_range]
  set c := (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ with hc
  have hR : ∀ F : (Fin T.nb → Fin D) → Fin D → ℕ → ℂ,
      c * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D, (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Lr T e ι h ℓ *
        ∑ k ∈ Finset.range T.weights.length, F ι x k =
      ∑ k ∈ Finset.range T.weights.length, c * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D,
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Lr T e ι h ℓ * F ι x k := by
    intro F
    rw [← Finset.mul_sum]
    congr 1
    calc ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D, (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Lr T e ι h ℓ *
          ∑ k ∈ Finset.range T.weights.length, F ι x k
        = ∑ ι : Fin T.nb → Fin D, ∑ k ∈ Finset.range T.weights.length, ∑ x : Fin D,
          (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Lr T e ι h ℓ * F ι x k := by
          refine Finset.sum_congr rfl fun ι _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
      _ = _ := Finset.sum_comm
  rw [hR]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hku : k < T.weights.length := Finset.mem_range.1 hk
  have hgk : T.weights[k]? = some (T.weights.getD k (0, 0)) := by
    rw [List.getD_eq_getElem _ _ hku, List.getElem?_eq_getElem hku]
  have hpm : T.weights.getD k (0, 0) ∈ T.weights := GS_getD_mem _ _ k hku
  have hy : (T.weights.getD k (0, 0)).2 < T.nb := (GS_wf_bound hT).2 _ hpm
  rw [hgk]
  simp only [Option.elim]
  unfold LoopExpr.evalH
  dsimp only
  rw [GS_sum_snoc, zpow_sub_one₀ (Nat.cast_ne_zero.2 hD), hc, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GS_prod_eraseIdx _ (0, 0) _ _ hku, GS_prod_set _ [] _ _ hℓ]
  rw [GS_word_append, GS_word_cons _ _ _ _ (.det a) tl, GS_W_snoc e ι x h tl htl]
  simp only [GS_word_cons2, GS_word_single, (GS_E_snoc e ι x).2, (GS_E_snoc e ι x).1 _ hy]
  have hL : ∏ k ∈ (Finset.range T.loops.length).erase ℓ,
      ntr (loopWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt
        (T.loops.getD k [])) = GS_Lr T e ι h ℓ :=
    Finset.prod_congr rfl fun k hk => GS_lv_snoc hT e ι x h k
      (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
  have hW : ∏ k' ∈ (Finset.range T.weights.length).erase k,
      ntr ((e.G h (T.weights.getD k' (0, 0)).1 - e.M (T.weights.getD k' (0, 0)).1) *
        e.E (Fin.snoc (α := fun _ => Fin D) ι x) (T.weights.getD k' (0, 0)).2) =
      ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0)) := by
    refine Finset.prod_congr rfl fun k' hk' => ?_
    have hk'u := Finset.mem_range.1 (Finset.mem_of_mem_erase hk')
    rw [(GS_E_snoc e ι x).1 _ ((GS_wf_bound hT).2 _ (GS_getD_mem _ _ k' hk'u))]
    rfl
  rw [hL, hW, pow_add, mul_inv]
  simp only [Matrix.mul_assoc]
  ring

/-- The loop of the term `𝔭₂` (5.46) [splug2_def] plugging the loop `f` at its position `q`:
`⟨F 𝒢_a E_x f_{q..} f_{..q} 𝒢_b E_x⟩` when `f[q] = 𝒢_b`, and `0` otherwise. -/
private def GS_p2 {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ)
    (a : Fin 2) (tl : List LoopLetter) (x : Fin D) (f : List LoopLetter) (q : ℕ) : ℂ :=
  match f[q]? with
  | some (.res b) => ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x *
      loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.rotate q) * e.G h b * Ea D N x)
  | _ => 0

/-- Exchanging an inner finite sum with the sums over the bound block indices. -/
private lemma GS_sum_swap {D nb : ℕ} {κ : Type*} (S : Finset κ) (c : ℂ)
    (K : (Fin nb → Fin D) → Fin D → ℂ) (F : (Fin nb → Fin D) → Fin D → κ → ℂ) :
    c * ∑ ι : Fin nb → Fin D, ∑ x : Fin D, K ι x * ∑ k ∈ S, F ι x k =
      ∑ k ∈ S, c * ∑ ι : Fin nb → Fin D, ∑ x : Fin D, K ι x * F ι x k := by
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ ι : Fin nb → Fin D, ∑ x : Fin D, K ι x * ∑ k ∈ S, F ι x k
      = ∑ ι : Fin nb → Fin D, ∑ k ∈ S, ∑ x : Fin D, K ι x * F ι x k := by
        refine Finset.sum_congr rfl fun ι _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    _ = _ := Finset.sum_comm

/-- The terms `𝔭₂` (5.46) [splug2_def]: `D⁻¹ N⁻² c_𝒯 Σ_ι Σ_x W ⋯ Σ_{k ≠ ℓ} Σ_q
⟨F 𝒢_a E_x f_{q..} f_{..q} 𝒢_b E_x⟩ Π_{k' ≠ ℓ, k} ⟨f_{k'}⟩`, the loop `f = f_k` plugged in at its
position `q`. -/
private lemma GS_op_plug2 {D N : ℕ} (hD : D ≠ 0) {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) :
    ((T.apply .plug2).map fun T' => T'.evalH e h).sum =
      (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D, ∑ x : Fin D,
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Wt T e ι h *
          ∑ k ∈ (Finset.range T.loops.length).erase ℓ,
            ∑ q ∈ Finset.range (T.loops.getD k []).length,
              GS_p2 e ι h a tl x (T.loops.getD k []) q *
              ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
                GS_lv e ι h (T.loops.getD k' []) := by
  obtain ⟨hℓ, htl, -⟩ := GS_focus_data hT hf
  simp only [LoopExpr.apply, hf]
  rw [GS_sum_flatMap, GS_sum_range, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hℓ)]
  simp only [ite_true, List.map_nil, List.sum_nil, zero_add]
  rw [GS_sum_swap]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkℓ : k ≠ ℓ := Finset.ne_of_mem_erase hk
  have hkn : k < T.loops.length := Finset.mem_range.1 (Finset.mem_of_mem_erase hk)
  have hgk : T.loops[k]? = some (T.loops.getD k []) := by
    rw [List.getD_eq_getElem _ _ hkn, List.getElem?_eq_getElem hkn]
  have hfm : T.loops.getD k [] ∈ T.loops := GS_getD_mem _ _ k hkn
  have hfb : ∀ y, LoopLetter.proj y ∈ T.loops.getD k [] → y < T.nb :=
    (GS_wf_bound hT).1 _ hfm
  simp only [hkℓ, ite_false, hgk]
  rw [GS_sum_filterMap, GS_sum_range, GS_sum_swap]
  refine Finset.sum_congr rfl fun q hq => ?_
  set f := T.loops.getD k [] with hfdef
  rcases hq' : f[q]? with _ | y
  · simp [hq', GS_p2]
  · cases y with
    | res b =>
      simp only [Option.elim]
      have hrb : ∀ y, LoopLetter.proj y ∈ f.rotate q → y < T.nb :=
        fun y hy => hfb y (List.mem_rotate.1 hy)
      unfold LoopExpr.evalH
      dsimp only
      rw [GS_sum_snoc, zpow_sub_one₀ (Nat.cast_ne_zero.2 hD), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GS_Wt_snoc hT, GS_prod_set_eraseIdx _ [] _ _ _ hℓ hkn hkℓ]
      rw [GS_word_append, GS_word_append, GS_word_append, GS_word_cons _ _ _ _ (.det a) tl,
        GS_W_snoc e ι x h tl htl, GS_W_snoc e ι x h _ hrb]
      simp only [GS_word_cons2, GS_word_single, (GS_E_snoc e ι x).2]
      have hL : ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
          ntr (loopWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt
            (T.loops.getD k' [])) =
          ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
            GS_lv e ι h (T.loops.getD k' []) :=
        Finset.prod_congr rfl fun k' hk' => GS_lv_snoc hT e ι x h k'
          (Finset.mem_range.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk')))
      rw [hL, pow_add, mul_inv]
      simp only [GS_p2, hq', Matrix.mul_assoc]
      ring
    | _ => simp [hq', GS_p2]

/-! ### The Leibniz derivative summed over the entries of a block -/

/-- The derivatives of the resolvents of `tl` summed over a block: the terms `𝔠₂` (5.44)
[scut_2]. -/
private lemma GS_sd1 {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0) (T : LoopExpr) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (h : Idx D N → Idx D N → ℂ) (a : Fin 2) (tl : List LoopLetter)
    (ℓ : ℕ) (x : Fin D) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      ((e.M a * GS_wordD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl *
        e.G h a) i j * GS_Wt T e ι h * GS_Lr T e ι h ℓ) =
      -((D : ℂ) * N) ^ 2 * GS_Wt T e ι h * GS_Lr T e ι h ℓ *
        ∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q := by
  have key : ∀ i j : Idx D N,
      (e.M a * GS_wordD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl *
        e.G h a) i j = ∑ q ∈ Finset.range tl.length,
          (e.M a * GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl q *
            e.G h a) i j := by
    intro i j
    unfold GS_wordD
    rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
  simp only [key, Finset.sum_mul, Finset.mul_sum]
  calc ∑ i : Idx D N, ∑ j : Idx D N, ∑ q ∈ Finset.range tl.length, Ea D N x i i * Ea D N x j j *
        ((e.M a * GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl q *
          e.G h a) i j * GS_Wt T e ι h * GS_Lr T e ι h ℓ)
      = ∑ i : Idx D N, ∑ q ∈ Finset.range tl.length, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
        ((e.M a * GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl q *
          e.G h a) i j * GS_Wt T e ι h * GS_Lr T e ι h ℓ) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ q ∈ Finset.range tl.length, ∑ i : Idx D N, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
        ((e.M a * GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl q *
          e.G h a) i j * GS_Wt T e ι h * GS_Lr T e ι h ℓ) := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rcases hq : tl[q]? with _ | y
      · simp [GS_posD, GS_c2, hq]
      · cases y with
        | res b =>
          have e1 : ∀ i j : Idx D N,
              (e.M a * GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt tl q *
                e.G h a) i j = -((e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.take q) *
                  e.G h b) * Matrix.single i j (1 : ℂ) *
                  (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.drop (q + 1)) *
                    e.G h a)) i j := by
            intro i j
            simp only [GS_posD, hq, GS_dG, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
              Matrix.neg_apply]
          simp only [e1]
          have e2 := GS_block_entry x (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.take q) *
            e.G h b) (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.drop (q + 1)) * e.G h a)
          rw [GS_trace_ntr hD hN, GS_trace_ntr hD hN] at e2
          simp only [GS_c2, hq]
          rw [← sub_eq_zero]
          have e3 : ∑ i : Idx D N, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
              (-(e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.take q) * e.G h b *
                Matrix.single i j (1 : ℂ) * (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt
                  (tl.drop (q + 1)) * e.G h a)) i j * GS_Wt T e ι h * GS_Lr T e ι h ℓ) =
              -(GS_Wt T e ι h * GS_Lr T e ι h ℓ) * ∑ i : Idx D N, ∑ j : Idx D N,
                Ea D N x i i * Ea D N x j j *
                (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt (tl.take q) * e.G h b *
                  Matrix.single i j (1 : ℂ) * (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt
                    (tl.drop (q + 1)) * e.G h a)) i j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [e3, e2]
          simp only [Matrix.mul_assoc]
          ring
        | _ => simp [GS_posD, GS_c2, hq]

/-- `Σ_{i,j ∈ 𝓘_x} Y_{ij} ⟨P E_{ij} Q⟩ = ⟨Y E_x Q P E_x⟩`. -/
private lemma GS_block_ntr {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0) (x : Fin D)
    (Y P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      (Y i j * ntr (P * Matrix.single i j (1 : ℂ) * Q)) =
        ntr (Y * Ea D N x * (Q * P) * Ea D N x) := by
  have hκ : ((D : ℂ) * N) ≠ 0 := by simp [hD, hN]
  have e1 : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, ntr X = ((D : ℂ) * N)⁻¹ * X.trace := by
    intro X
    rw [GS_trace_ntr hD hN X, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
  have e2 := GS_block_trace x Y P Q
  rw [e1 (Y * Ea D N x * (Q * P) * Ea D N x), ← e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e1]
  ring

/-- The derivative of the last resolvent `𝒢_a` of `F 𝒢` summed over a block: with `-𝗆⟨F 𝒢⟩`, the
term `𝔠₁` (5.43) [scut1_def]. -/
private lemma GS_sd2 {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0) (T : LoopExpr) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (h : Idx D N → Idx D N → ℂ) (a : Fin 2) (tl : List LoopLetter)
    (ℓ : ℕ) (x : Fin D) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      ((e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * GS_dG e h (Matrix.single i j 1) a) i j *
        GS_Wt T e ι h * GS_Lr T e ι h ℓ) =
      -((D : ℂ) * N) ^ 2 * GS_Wt T e ι h * GS_Lr T e ι h ℓ *
        (ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x) *
          ntr (e.G h a * Ea D N x)) := by
  have e1 : ∀ i j : Idx D N,
      (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * GS_dG e h (Matrix.single i j 1) a) i j =
        -((e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a) *
          Matrix.single i j (1 : ℂ) * e.G h a) i j := by
    intro i j
    simp only [GS_dG, Matrix.mul_neg, Matrix.mul_assoc, Matrix.neg_apply]
  have e2 := GS_block_entry x (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a)
    (e.G h a)
  rw [GS_trace_ntr hD hN, GS_trace_ntr hD hN] at e2
  simp only [e1]
  have e3 : ∑ i : Idx D N, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
      (-(e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a *
        Matrix.single i j (1 : ℂ) * e.G h a) i j * GS_Wt T e ι h * GS_Lr T e ι h ℓ) =
      -(GS_Wt T e ι h * GS_Lr T e ι h ℓ) * ∑ i : Idx D N, ∑ j : Idx D N,
        Ea D N x i i * Ea D N x j j *
        (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a *
          Matrix.single i j (1 : ℂ) * e.G h a) i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e3, e2]
  ring

/-- The derivatives of the light weights summed over a block: the terms `𝔭₁` (5.45)
[splug1_def]. -/
private lemma GS_sd3 {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0) (T : LoopExpr) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (h : Idx D N → Idx D N → ℂ) (a : Fin 2) (tl : List LoopLetter)
    (ℓ : ℕ) (x : Fin D) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      ((e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a) i j *
        (∑ k ∈ Finset.range T.weights.length,
          GS_wd e ι (Matrix.single i j 1) h (T.weights.getD k (0, 0)) *
          ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0))) *
        GS_Lr T e ι h ℓ) =
      -GS_Lr T e ι h ℓ * ∑ k ∈ Finset.range T.weights.length,
        ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x *
          e.G h (T.weights.getD k (0, 0)).1 * e.E ι (T.weights.getD k (0, 0)).2 *
          e.G h (T.weights.getD k (0, 0)).1 * Ea D N x) *
        ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0)) := by
  set F := e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a with hF
  have e1 : ∀ (i j : Idx D N) (p : Fin 2 × ℕ), GS_wd e ι (Matrix.single i j 1) h p =
      -ntr (e.G h p.1 * Matrix.single i j (1 : ℂ) * (e.G h p.1 * e.E ι p.2)) := by
    intro i j p
    simp only [GS_wd, GS_dG, Matrix.neg_mul, Matrix.mul_assoc, ntr, Matrix.trace_neg, mul_neg]
  simp only [e1, neg_mul, Finset.sum_neg_distrib, mul_neg, neg_mul, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  calc ∑ i : Idx D N, ∑ j : Idx D N, ∑ k ∈ Finset.range T.weights.length,
        Ea D N x i i * Ea D N x j j * (F i j * (ntr (e.G h (T.weights.getD k (0, 0)).1 *
          Matrix.single i j (1 : ℂ) * (e.G h (T.weights.getD k (0, 0)).1 *
            e.E ι (T.weights.getD k (0, 0)).2)) *
          ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0))) *
          GS_Lr T e ι h ℓ)
      = ∑ i : Idx D N, ∑ k ∈ Finset.range T.weights.length, ∑ j : Idx D N,
        Ea D N x i i * Ea D N x j j * (F i j * (ntr (e.G h (T.weights.getD k (0, 0)).1 *
          Matrix.single i j (1 : ℂ) * (e.G h (T.weights.getD k (0, 0)).1 *
            e.E ι (T.weights.getD k (0, 0)).2)) *
          ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0))) *
          GS_Lr T e ι h ℓ) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range T.weights.length, ∑ i : Idx D N, ∑ j : Idx D N,
        Ea D N x i i * Ea D N x j j * (F i j * (ntr (e.G h (T.weights.getD k (0, 0)).1 *
          Matrix.single i j (1 : ℂ) * (e.G h (T.weights.getD k (0, 0)).1 *
            e.E ι (T.weights.getD k (0, 0)).2)) *
          ∏ k' ∈ (Finset.range T.weights.length).erase k, GS_wv e ι h (T.weights.getD k' (0, 0))) *
          GS_Lr T e ι h ℓ) := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have e2 := GS_block_ntr hD hN x F (e.G h (T.weights.getD k (0, 0)).1)
        (e.G h (T.weights.getD k (0, 0)).1 * e.E ι (T.weights.getD k (0, 0)).2)
      rw [← sub_eq_zero]
      have e3 : ∑ i : Idx D N, ∑ j : Idx D N,
          Ea D N x i i * Ea D N x j j * (F i j * (ntr (e.G h (T.weights.getD k (0, 0)).1 *
            Matrix.single i j (1 : ℂ) * (e.G h (T.weights.getD k (0, 0)).1 *
              e.E ι (T.weights.getD k (0, 0)).2)) *
            ∏ k' ∈ (Finset.range T.weights.length).erase k,
              GS_wv e ι h (T.weights.getD k' (0, 0))) * GS_Lr T e ι h ℓ) =
          (GS_Lr T e ι h ℓ * ∏ k' ∈ (Finset.range T.weights.length).erase k,
              GS_wv e ι h (T.weights.getD k' (0, 0))) *
            ∑ i : Idx D N, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
              (F i j * ntr (e.G h (T.weights.getD k (0, 0)).1 * Matrix.single i j (1 : ℂ) *
                (e.G h (T.weights.getD k (0, 0)).1 * e.E ι (T.weights.getD k (0, 0)).2))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e3, e2]
      simp only [Matrix.mul_assoc]
      ring

/-- Exchanging a double sum over all entries with an inner finite sum. -/
private lemma GS_sum_comm3 {α β κ : Type*} [Fintype α] [Fintype β] (S : Finset κ)
    (f : α → β → κ → ℂ) : ∑ i, ∑ j, ∑ k ∈ S, f i j k = ∑ k ∈ S, ∑ i, ∑ j, f i j k := by
  calc ∑ i, ∑ j, ∑ k ∈ S, f i j k = ∑ i, ∑ k ∈ S, ∑ j, f i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The derivatives of the other loops summed over a block: the terms `𝔭₂` (5.46)
[splug2_def]. -/
private lemma GS_sd4 {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0) (T : LoopExpr) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (h : Idx D N → Idx D N → ℂ) (a : Fin 2) (tl : List LoopLetter)
    (ℓ : ℕ) (x : Fin D) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      ((e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a) i j * GS_Wt T e ι h *
        (∑ k ∈ (Finset.range T.loops.length).erase ℓ,
          GS_ld e ι (Matrix.single i j 1) h (T.loops.getD k []) *
          ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
            GS_lv e ι h (T.loops.getD k' []))) =
      -GS_Wt T e ι h * ∑ k ∈ (Finset.range T.loops.length).erase ℓ,
        ∑ q ∈ Finset.range (T.loops.getD k []).length,
          GS_p2 e ι h a tl x (T.loops.getD k []) q *
          ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
            GS_lv e ι h (T.loops.getD k' []) := by
  set F := e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a with hF
  set S := (Finset.range T.loops.length).erase ℓ with hS
  have e1 : ∀ (i j : Idx D N) (f : List LoopLetter), GS_ld e ι (Matrix.single i j 1) h f =
      ∑ q ∈ Finset.range f.length,
        ntr (GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt f q) := by
    intro i j f
    simp only [GS_ld, GS_wordD, ntr, Matrix.trace_sum, Finset.mul_sum]
  simp only [e1, Finset.sum_mul, Finset.mul_sum]
  rw [GS_sum_comm3]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GS_sum_comm3]
  refine Finset.sum_congr rfl fun q _ => ?_
  set f := T.loops.getD k [] with hfdef
  rcases hq : f[q]? with _ | y
  · simp [GS_posD, GS_p2, hq, ntr]
  · cases y with
    | res b =>
      have hlt := (List.getElem?_eq_some_iff.1 hq).1
      have e2 : ∀ i j : Idx D N,
          ntr (GS_posD (e.G h) (GS_dG e h (Matrix.single i j 1)) e.M (e.E ι) e.Lt f q) =
            -ntr ((loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.take q) * e.G h b) *
              Matrix.single i j (1 : ℂ) *
              (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.drop (q + 1)))) := by
        intro i j
        simp only [GS_posD, hq, GS_dG, Matrix.neg_mul, Matrix.mul_assoc, ntr,
          Matrix.trace_neg, mul_neg]
      have hrot : loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.rotate q) =
          e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.drop (q + 1)) *
            loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.take q) := by
        rw [List.rotate_eq_drop_append_take hlt.le, GS_word_append, List.drop_eq_getElem_cons hlt,
          (List.getElem?_eq_some_iff.1 hq).2, GS_word_cons]
        simp only [GS_word_single]
      have e3 := GS_block_ntr hD hN x F
        (loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.take q) * e.G h b)
        (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.drop (q + 1)))
      simp only [e2]
      rw [← sub_eq_zero]
      have e4 : ∑ i : Idx D N, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
          (F i j * GS_Wt T e ι h *
            (-ntr ((loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.take q) * e.G h b) *
              Matrix.single i j (1 : ℂ) *
              (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.drop (q + 1)))) *
            ∏ k' ∈ S.erase k, GS_lv e ι h (T.loops.getD k' []))) =
          -(GS_Wt T e ι h * ∏ k' ∈ S.erase k, GS_lv e ι h (T.loops.getD k' [])) *
            ∑ i : Idx D N, ∑ j : Idx D N, Ea D N x i i * Ea D N x j j *
              (F i j * ntr ((loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.take q) * e.G h b) *
                Matrix.single i j (1 : ℂ) *
                (e.G h b * loopWordMat (e.G h) e.M (e.E ι) e.Lt (f.drop (q + 1))))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e4, e3]
      simp only [GS_p2, hq, hrot, hF, Matrix.mul_assoc]
      ring
    | _ => simp [GS_posD, GS_p2, hq, ntr]

/-! ### The resolvent identity (2.43) and the identity `D ⟨𝔐 E_x⟩ = 𝗆` -/

/-- The block projections sum to the identity. -/
private lemma GS_sum_Ea (D N : ℕ) : ∑ x : Fin D, Ea D N x = 1 := by
  ext k l
  simp only [Matrix.sum_apply, Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl; simp [Finset.sum_ite_eq]
  · simp [hkl]

/-- The scalar `𝗆_a` of the slot `a`: `m(z_a)` or `m(z̄_a)` for the deformation `c_a Λ`. -/
private def GS_m {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) : ℂ :=
  mExt ((e.c a : ℂ) • lam D N e.A) (if e.s a then star (e.z a) else e.z a)

/-- `D ⟨𝔐_a E_x⟩ = 𝗆_a` of `def_M_scalar` (2.13) [def_M], summed against `⟨F E_x⟩`:
`𝗆_a ⟨F⟩ = D Σ_x ⟨𝔐_a E_x⟩ ⟨F E_x⟩`. -/
private lemma GS_m_id {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (a : Fin 2) (F : Matrix (Idx D N) (Idx D N) ℂ) :
    GS_m e a * ntr F = ∑ x : Fin D, (D : ℂ) * ntr (e.M a * Ea D N x) * ntr (F * Ea D N x) := by
  obtain ⟨h1, -⟩ := def_M_scalar D hD N hN ((e.c a : ℂ) • e.A) _ (GS_slot_im e hz a)
  rw [← lam_smul] at h1
  have e1 : ∀ x : Fin D, (D : ℂ) * ntr (e.M a * Ea D N x) = GS_m e a := h1
  simp only [e1]
  rw [← Finset.mul_sum]
  congr 1
  have : ∑ x : Fin D, ntr (F * Ea D N x) = ntr (F * ∑ x : Fin D, Ea D N x) := by
    simp only [ntr, Matrix.trace_sum, Finset.mul_sum]
  rw [this, GS_sum_Ea, Matrix.mul_one]

/-- The resolvent identity (2.43) [eq:id_G0G1] `𝒢 = 𝔐 - 𝒢 (h + 𝗆) 𝔐` inside a loop:
`⟨𝒢_a X⟩ = ⟨𝔐_a X⟩ - (DN)⁻¹ Σ_{ij} h̄_{ij} (𝔐_a X 𝒢_a)_{ij} - 𝗆_a ⟨𝔐_a X 𝒢_a⟩` for a Hermitian
array. -/
private lemma GS_res_id {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (a : Fin 2) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (e.G h a * X) = ntr (e.M a * X) -
      ((D : ℂ) * N)⁻¹ * (∑ i : Idx D N, ∑ j : Idx D N,
        starRingEnd ℂ (h i j) * (e.M a * X * e.G h a) i j) -
      GS_m e a * ntr (e.M a * X * e.G h a) := by
  have hD0 : D ≠ 0 := by omega
  have hN0 : N ≠ 0 := by omega
  set Λ := (e.c a : ℂ) • lam D N e.A with hΛ
  set ζ := if e.s a then star (e.z a) else e.z a with hζ
  set m := GS_m e a with hm
  set G := e.G h a with hG
  set M := e.M a with hM
  obtain ⟨-, hdy⟩ := def_M_scalar D hD N hN ((e.c a : ℂ) • e.A) _ (GS_slot_im e hz a)
  rw [← lam_smul] at hdy
  have hdy' : (Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M = 1 := by
    have : ((m + ζ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Λ) * M = -1 :=
      eq_neg_of_add_eq_zero_left hdy
    rw [show Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
      -((m + ζ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Λ) by rw [add_comm]; abel, Matrix.neg_mul,
      this, neg_neg]
  obtain ⟨-, hG2⟩ := res_mul_sub_of_im_ne (Matrix.of h + Λ) (hh.add (GS_slot_herm e a)) ζ
    (GS_slot_im e hz a)
  have hG2' : G * (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 := hG2
  have key : G = M - G * Matrix.of h * M - m • (G * M) := by
    calc G = G * ((Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M) := by
          rw [hdy', Matrix.mul_one]
      _ = (G * (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) - G * Matrix.of h -
          m • G) * M := by
          rw [← Matrix.mul_assoc]
          congr 1
          simp only [Matrix.mul_sub, Matrix.mul_add, add_smul, Matrix.mul_smul, Matrix.mul_one]
          abel
      _ = M - G * Matrix.of h * M - m • (G * M) := by
          rw [hG2', Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have hκ : ((Fintype.card (Idx D N) : ℕ) : ℂ) = (D : ℂ) * N := by simp [Fintype.card_prod]
  have htr : (Matrix.of h * (M * X * G)).trace =
      ∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) * (M * X * G) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hh.apply i j
    simp only [Matrix.of_apply] at this
    rw [← this, Complex.star_def, Complex.conj_conj]
  calc ntr (G * X) = ntr ((M - G * Matrix.of h * M - m • (G * M)) * X) := by rw [← key]
    _ = ntr (M * X) - ((D : ℂ) * N)⁻¹ * (Matrix.of h * (M * X * G)).trace -
        m * ntr (M * X * G) := by
        simp only [Matrix.sub_mul, Matrix.smul_mul, ntr, Matrix.trace_sub, Matrix.trace_smul,
          smul_eq_mul, hκ]
        rw [Matrix.trace_mul_comm (G * Matrix.of h * M) X, Matrix.trace_mul_comm (G * M) X]
        rw [show X * (G * Matrix.of h * M) = (X * G) * (Matrix.of h * M) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm (X * G),
          show Matrix.of h * M * (X * G) = Matrix.of h * (M * X * G) by
          simp only [Matrix.mul_assoc], show X * (G * M) = (X * G) * M by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm (X * G) M,
          show M * (X * G) = M * X * G by simp only [Matrix.mul_assoc]]
        ring
    _ = _ := by rw [htr]

/-! ### The expansion (5.40) at a Hermitian array -/

/-- The terms of the five operations at one value of the bound block indices: the Leibniz
derivative summed over the entries of each block, with `-𝗆_a ⟨F 𝒢_a⟩`. -/
private lemma GS_step_id_one {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (T : LoopExpr) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (ι : Fin T.nb → Fin D) :
    GS_Wt T e ι h * ntr (e.G h a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl) * GS_Lr T e ι h ℓ -
      GS_Wt T e ι h * ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl) * GS_Lr T e ι h ℓ -
      ∑ x : Fin D, ((D : ℂ) * GS_Wt T e ι h * ntr ((e.G h a - e.M a) * Ea D N x) *
          ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x) *
            GS_Lr T e ι h ℓ +
        (D : ℂ) * GS_Wt T e ι h * GS_Lr T e ι h ℓ *
          (∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q) +
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Lr T e ι h ℓ *
          (∑ k ∈ Finset.range T.weights.length,
            ntr (e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a * Ea D N x *
              e.G h (T.weights.getD k (0, 0)).1 * e.E ι (T.weights.getD k (0, 0)).2 *
              e.G h (T.weights.getD k (0, 0)).1 * Ea D N x) *
            (∏ k' ∈ (Finset.range T.weights.length).erase k,
              GS_wv e ι h (T.weights.getD k' (0, 0)))) +
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * GS_Wt T e ι h *
          ∑ k ∈ (Finset.range T.loops.length).erase ℓ,
            ∑ q ∈ Finset.range (T.loops.getD k []).length,
              GS_p2 e ι h a tl x (T.loops.getD k []) q *
              ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
                GS_lv e ι h (T.loops.getD k' [])) =
      -((D : ℂ) * N)⁻¹ * (∑ i : Idx D N, ∑ j : Idx D N,
          T.pkgVal e ι i j h * starRingEnd ℂ (h i j)) +
        ((D : ℂ) * N)⁻¹ * (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
          (if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0) := by
  have hD0 : D ≠ 0 := by omega
  have hN0 : N ≠ 0 := by omega
  have hDc : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hD0
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0
  set W := GS_Wt T e ι h with hW
  set Lr := GS_Lr T e ι h ℓ with hLr
  set X := loopWordMat (e.G h) e.M (e.E ι) e.Lt tl with hX
  set F := e.M a * X * e.G h a with hF
  -- the resolvent identity and `𝗆`
  have hres := GS_res_id hD hN e hz h hh a X
  have hmid := GS_m_id hD hN e hz a F
  -- the values of `pkgVal`
  have hpk : ∑ i : Idx D N, ∑ j : Idx D N, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) =
      W * Lr * ∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) * F i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GS_pkgVal_eq T hf]
    ring
  -- the Leibniz derivative summed over the blocks
  have hder : ∑ i : Idx D N, ∑ j : Idx D N,
      (if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0) =
      ∑ x : Fin D, (-((D : ℂ) * N) ^ 2 * W * Lr *
          (∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q) +
        -((D : ℂ) * N) ^ 2 * W * Lr * (ntr (F * Ea D N x) * ntr (e.G h a * Ea D N x)) +
        -Lr * (∑ k ∈ Finset.range T.weights.length,
          ntr (F * Ea D N x * e.G h (T.weights.getD k (0, 0)).1 *
            e.E ι (T.weights.getD k (0, 0)).2 * e.G h (T.weights.getD k (0, 0)).1 * Ea D N x) *
          (∏ k' ∈ (Finset.range T.weights.length).erase k,
            GS_wv e ι h (T.weights.getD k' (0, 0)))) +
        -W * ∑ k ∈ (Finset.range T.loops.length).erase ℓ,
          ∑ q ∈ Finset.range (T.loops.getD k []).length,
            GS_p2 e ι h a tl x (T.loops.getD k []) q *
            ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
              GS_lv e ι h (T.loops.getD k' [])) := by
    rw [GS_sum_block]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← GS_sd1 hD0 hN0 T e ι h a tl ℓ x, ← GS_sd2 hD0 hN0 T e ι h a tl ℓ x,
      ← GS_sd3 hD0 hN0 T e ι h a tl ℓ x, ← GS_sd4 hD0 hN0 T e ι h a tl ℓ x,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [GS_pkgD, hf]
    ring
  rw [hpk, hder, hres]
  have hsub : ∀ x : Fin D, ntr ((e.G h a - e.M a) * Ea D N x) =
      ntr (e.G h a * Ea D N x) - ntr (e.M a * Ea D N x) := by
    intro x
    simp only [Matrix.sub_mul, ntr, Matrix.trace_sub, mul_sub]
  have hsum : (∑ x : Fin D, ((D : ℂ) * W * ntr ((e.G h a - e.M a) * Ea D N x) *
          ntr (F * Ea D N x) * Lr +
        (D : ℂ) * W * Lr * (∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q) +
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * Lr *
          (∑ k ∈ Finset.range T.weights.length,
            ntr (F * Ea D N x * e.G h (T.weights.getD k (0, 0)).1 *
              e.E ι (T.weights.getD k (0, 0)).2 * e.G h (T.weights.getD k (0, 0)).1 * Ea D N x) *
            (∏ k' ∈ (Finset.range T.weights.length).erase k,
              GS_wv e ι h (T.weights.getD k' (0, 0)))) +
        (D : ℂ)⁻¹ * ((N : ℂ) ^ 2)⁻¹ * W *
          ∑ k ∈ (Finset.range T.loops.length).erase ℓ,
            ∑ q ∈ Finset.range (T.loops.getD k []).length,
              GS_p2 e ι h a tl x (T.loops.getD k []) q *
              ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
                GS_lv e ι h (T.loops.getD k' []))) +
      ((D : ℂ) * N)⁻¹ * (N : ℂ)⁻¹ * ∑ x : Fin D, (-((D : ℂ) * N) ^ 2 * W * Lr *
          (∑ q ∈ Finset.range tl.length, GS_c2 e ι h a tl x q) +
        -((D : ℂ) * N) ^ 2 * W * Lr * (ntr (F * Ea D N x) * ntr (e.G h a * Ea D N x)) +
        -Lr * (∑ k ∈ Finset.range T.weights.length,
          ntr (F * Ea D N x * e.G h (T.weights.getD k (0, 0)).1 *
            e.E ι (T.weights.getD k (0, 0)).2 * e.G h (T.weights.getD k (0, 0)).1 * Ea D N x) *
          (∏ k' ∈ (Finset.range T.weights.length).erase k,
            GS_wv e ι h (T.weights.getD k' (0, 0)))) +
        -W * ∑ k ∈ (Finset.range T.loops.length).erase ℓ,
          ∑ q ∈ Finset.range (T.loops.getD k []).length,
            GS_p2 e ι h a tl x (T.loops.getD k []) q *
            ∏ k' ∈ ((Finset.range T.loops.length).erase ℓ).erase k,
              GS_lv e ι h (T.loops.getD k' [])) =
      -(W * Lr) * ∑ x : Fin D, (D : ℂ) * ntr (e.M a * Ea D N x) * ntr (F * Ea D N x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsub]
    field_simp
    ring
  simp only [hF] at hsum hmid ⊢
  linear_combination (-(W * Lr)) * hmid - hsum

/-- The expansion (5.40) [expansion_for_integral_by_part_term] at a Hermitian array, before the
expectation: `𝒯 - Σ_{𝒯' ∈ step} 𝒯'` is `c_𝒯 Σ_ι` of `-(DN)⁻¹ Σ_{ij} (F 𝒢)_{ij} W ⋯ f ⋯ h̄_{ij}` and
of `(DN)⁻¹ N⁻¹ Σ_{i, j in one block}` of its Leibniz derivative in the direction `E_{ij}`. -/
private lemma GS_step_id {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) {T : LoopExpr} (hT : T.wf = true)
    {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl))
    (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    T.evalH e h - (T.step.map fun T' => T'.evalH e h).sum =
      (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D,
        (-((D : ℂ) * N)⁻¹ * (∑ i : Idx D N, ∑ j : Idx D N,
            T.pkgVal e ι i j h * starRingEnd ℂ (h i j)) +
          ((D : ℂ) * N)⁻¹ * (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
            (if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0)) := by
  have hD0 : D ≠ 0 := by omega
  have hstep : (T.step.map fun T' => T'.evalH e h).sum =
      ((T.apply .rep).map fun T' => T'.evalH e h).sum +
      ((T.apply .cut1).map fun T' => T'.evalH e h).sum +
      ((T.apply .cut2).map fun T' => T'.evalH e h).sum +
      ((T.apply .plug1).map fun T' => T'.evalH e h).sum +
      ((T.apply .plug2).map fun T' => T'.evalH e h).sum := by
    simp only [LoopExpr.step, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.sum_append]
    ring
  rw [hstep, GS_evalH_focus hT hf, GS_op_rep hT hf, GS_op_cut1 hD0 hT hf, GS_op_cut2 hD0 hT hf,
    GS_op_plug1 hD0 hT hf, GS_op_plug2 hD0 hT hf]
  rw [← Finset.sum_congr rfl fun ι _ => GS_step_id_one hD hN T hf e hz h hh ι]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, mul_add]
  ring

/-! ### Integrability -/

/-- On Hermitian arrays, `f` agrees with a continuous function and is bounded. -/
private def GS_nice {D N : ℕ} (f : (Idx D N → Idx D N → ℂ) → ℂ) : Prop :=
  (∃ g : (Idx D N → Idx D N → ℂ) → ℂ, Continuous g ∧
    ∀ h, (Matrix.of h).IsHermitian → f h = g h) ∧
  ∃ B : ℝ, ∀ h, (Matrix.of h).IsHermitian → ‖f h‖ ≤ B

/-- Constants are `GS_nice`. -/
private lemma GS_nice_const {D N : ℕ} (c : ℂ) : GS_nice (D := D) (N := N) fun _ => c :=
  ⟨⟨fun _ => c, continuous_const, fun _ _ => rfl⟩, ‖c‖, fun _ _ => le_rfl⟩

/-- Sums of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_add {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f)
    (hg : GS_nice g) : GS_nice fun h => f h + g h := by
  obtain ⟨⟨f', hf'c, hf'⟩, Bf, hBf⟩ := hf
  obtain ⟨⟨g', hg'c, hg'⟩, Bg, hBg⟩ := hg
  refine ⟨⟨fun h => f' h + g' h, hf'c.add hg'c, fun h hh => by
    beta_reduce; rw [hf' h hh, hg' h hh]⟩,
    Bf + Bg, fun h hh => (norm_add_le _ _).trans (add_le_add (hBf h hh) (hBg h hh))⟩

/-- Products of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_mul {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f)
    (hg : GS_nice g) : GS_nice fun h => f h * g h := by
  obtain ⟨⟨f', hf'c, hf'⟩, Bf, hBf⟩ := hf
  obtain ⟨⟨g', hg'c, hg'⟩, Bg, hBg⟩ := hg
  refine ⟨⟨fun h => f' h * g' h, hf'c.mul hg'c, fun h hh => by
    beta_reduce; rw [hf' h hh, hg' h hh]⟩,
    Bf * Bg, fun h hh => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hBf h hh) (hBg h hh) (norm_nonneg _) ((norm_nonneg _).trans (hBf h hh))

/-- Differences of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_sub {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f)
    (hg : GS_nice g) : GS_nice fun h => f h - g h := by
  have := GS_nice_add hf (GS_nice_mul (GS_nice_const (-1)) hg)
  simpa [sub_eq_add_neg] using this

/-- Finite sums of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_sum {D N : ℕ} {κ : Type*} (S : Finset κ)
    {f : κ → (Idx D N → Idx D N → ℂ) → ℂ} (hf : ∀ k ∈ S, GS_nice (f k)) :
    GS_nice fun h => ∑ k ∈ S, f k h := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GS_nice_const (D := D) (N := N) 0
  | insert a S ha ih =>
    simpa [Finset.sum_insert ha] using GS_nice_add (hf a (Finset.mem_insert_self a S))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-- Finite products of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_prod {D N : ℕ} {κ : Type*} (S : Finset κ)
    {f : κ → (Idx D N → Idx D N → ℂ) → ℂ} (hf : ∀ k ∈ S, GS_nice (f k)) :
    GS_nice fun h => ∏ k ∈ S, f k h := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GS_nice_const (D := D) (N := N) 1
  | insert a S ha ih =>
    simpa [Finset.prod_insert ha] using GS_nice_mul (hf a (Finset.mem_insert_self a S))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-- Every entry of the matrix function is `GS_nice`. -/
private def GS_niceM {D N : ℕ}
    (F : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  ∀ k l, GS_nice fun h => F h k l

/-- Products of `GS_niceM` matrix functions are `GS_niceM`. -/
private lemma GS_niceM_mul {D N : ℕ} {F G : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hF : GS_niceM F) (hG : GS_niceM G) : GS_niceM fun h => F h * G h := fun k l => by
  simpa [Matrix.mul_apply] using GS_nice_sum Finset.univ fun m _ => GS_nice_mul (hF k m) (hG m l)

/-- Constant matrices are `GS_niceM`. -/
private lemma GS_niceM_const {D N : ℕ} (A : Matrix (Idx D N) (Idx D N) ℂ) :
    GS_niceM fun _ => A := fun k l => GS_nice_const (A k l)

/-- Normalized traces of `GS_niceM` matrix functions are `GS_nice`. -/
private lemma GS_nice_ntr {D N : ℕ} {F : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hF : GS_niceM F) : GS_nice fun h => ntr (F h) := by
  simpa [ntr, Matrix.trace] using
    GS_nice_mul (GS_nice_const _) (GS_nice_sum Finset.univ fun k _ => hF k k)

/-- An entry is bounded by the operator norm. -/
private lemma GS_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : A i j = ((Matrix.toEuclideanCLM (𝕜 := ℂ) A) (EuclideanSpace.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec_single]
  rw [h3]
  exact (PiLp.norm_apply_le _ i).trans h1

/-- The operator norm of the adjoint. -/
private lemma GS_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- The resolvent of a slot is bounded entrywise by `(Im z_a)⁻¹` on Hermitian arrays and agrees
there with the continuous resolvent of the Hermitian part. -/
private lemma GS_niceM_G {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (a : Fin 2) :
    GS_niceM fun h => e.G h a := by
  intro k l
  refine ⟨⟨fun h => res (Matrix.of (symArr h) + (e.c a : ℂ) • lam D N e.A)
    (if e.s a then star (e.z a) else e.z a) k l,
    (contDiff_res_symArr _ (GS_slot_herm e a) _ (GS_slot_im e hz a) k l 0).continuous,
    fun h hh => by simp only [LoopEnv.G, symArr_of_isHermitian h hh]⟩, (e.z a).im⁻¹,
    fun h hh => ?_⟩
  have hX := hh.add (GS_slot_herm e a)
  refine (GS_entry_le _ k l).trans ?_
  simp only [LoopEnv.G]
  split_ifs
  · rw [show star (e.z a) = starRingEnd ℂ (e.z a) from rfl, res_conj _ hX _ (hz a),
      GS_opNorm_conjTranspose]
    exact opNorm_res_le _ hX _ (hz a)
  · exact opNorm_res_le _ hX _ (hz a)

/-- The matrices of words are `GS_niceM`. -/
private lemma GS_niceM_word {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) :
    ∀ w : List LoopLetter, GS_niceM fun h => loopWordMat (e.G h) e.M (e.E ι) e.Lt w
  | [] => by simpa [loopWordMat] using GS_niceM_const (D := D) (N := N) 1
  | x :: w => by
      have ih := GS_niceM_word e hz ι w
      have hx : GS_niceM fun h => loopWordMat (e.G h) e.M (e.E ι) e.Lt [x] := by
        cases x with
        | res a => simpa [loopWordMat] using GS_niceM_G e hz a
        | det a => simpa [loopWordMat] using GS_niceM_const (e.M a)
        | proj y => simpa [loopWordMat] using GS_niceM_const (e.E ι y)
        | lamt o => simpa [loopWordMat] using GS_niceM_const e.Lt
      simpa [GS_word_cons _ _ _ _ x w] using GS_niceM_mul hx ih

/-- A light weight `⟨(𝒢_b - 𝔐_b) E_y⟩` is `GS_nice`. -/
private lemma GS_nice_wv {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) (p : Fin 2 × ℕ) : GS_nice fun h => GS_wv e ι h p :=
  GS_nice_ntr (GS_niceM_mul (fun k l => by
    simpa using GS_nice_sub (GS_niceM_G e hz p.1 k l) (GS_nice_const (e.M p.1 k l)))
    (GS_niceM_const _))

/-- A product of light weights is `GS_nice`. -/
private lemma GS_nice_weights {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) : ∀ ws : List (Fin 2 × ℕ),
      GS_nice fun h => (ws.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod
  | [] => by simpa using GS_nice_const (D := D) (N := N) 1
  | p :: ws => by
      have := GS_nice_mul (GS_nice_wv e hz ι p) (GS_nice_weights e hz ι ws)
      simpa [GS_wv] using this

/-- A product of loops is `GS_nice`. -/
private lemma GS_nice_loops {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) : ∀ ls : List (List LoopLetter),
      GS_nice fun h => (ls.map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod
  | [] => by simpa using GS_nice_const (D := D) (N := N) 1
  | w :: ls => by
      have := GS_nice_mul (GS_nice_ntr (GS_niceM_word e hz ι w)) (GS_nice_loops e hz ι ls)
      simpa using this

/-- The values of the expressions of the class are `GS_nice`. -/
private lemma GS_nice_evalH {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) : GS_nice fun h => T.evalH e h := by
  unfold LoopExpr.evalH
  exact GS_nice_mul (GS_nice_const _) (GS_nice_sum _ fun ι _ =>
    GS_nice_mul (GS_nice_weights e hz ι T.weights) (GS_nice_loops e hz ι T.loops))

/-- The function `(F 𝒢)_{ij} W ⋯ f ⋯` is `GS_nice`. -/
private lemma GS_nice_pkgVal {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (ι : Fin T.nb → Fin D) (i j : Idx D N) :
    GS_nice fun h => T.pkgVal e ι i j h := by
  unfold LoopExpr.pkgVal
  split
  · exact GS_nice_const 0
  · exact GS_nice_mul (GS_nice_mul (GS_niceM_word e hz ι _ i j) (GS_nice_weights e hz ι _))
      (GS_nice_loops e hz ι _)

/-- The Leibniz derivative of `(F 𝒢)_{ij} W ⋯ f ⋯` is `GS_nice`. -/
private lemma GS_nice_pkgD {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (ι : Fin T.nb → Fin D) (i j : Idx D N)
    (Δ : Matrix (Idx D N) (Idx D N) ℂ) : GS_nice fun h => GS_pkgD T e ι i j Δ h := by
  have hdG : ∀ b, GS_niceM fun h => GS_dG e h Δ b := fun b k l => by
    have := GS_niceM_mul (GS_niceM_mul (GS_niceM_G e hz b) (GS_niceM_const Δ))
      (GS_niceM_G e hz b) k l
    simpa [GS_dG] using GS_nice_mul (GS_nice_const (-1)) this
  have hWD : ∀ w, GS_niceM fun h => GS_wordD (e.G h) (GS_dG e h Δ) e.M (e.E ι) e.Lt w := by
    intro w k l
    unfold GS_wordD
    simp only [Matrix.sum_apply]
    refine GS_nice_sum _ fun q _ => ?_
    unfold GS_posD
    rcases hq : w[q]? with _ | y
    · simpa using GS_nice_const (D := D) (N := N) 0
    · cases y with
      | res b =>
        exact GS_niceM_mul (GS_niceM_mul (GS_niceM_word e hz ι _) (hdG b))
          (GS_niceM_word e hz ι _) k l
      | _ => simpa using GS_nice_const (D := D) (N := N) 0
  have hwv : ∀ p, GS_nice fun h => GS_wv e ι h p := fun p => GS_nice_wv e hz ι p
  have hwd : ∀ p, GS_nice fun h => GS_wd e ι Δ h p := fun p =>
    GS_nice_ntr (GS_niceM_mul (hdG p.1) (GS_niceM_const _))
  have hlv : ∀ w, GS_nice fun h => GS_lv e ι h w := fun w => GS_nice_ntr (GS_niceM_word e hz ι w)
  have hld : ∀ w, GS_nice fun h => GS_ld e ι Δ h w := fun w => GS_nice_ntr (hWD w)
  have hWt : GS_nice fun h => GS_Wt T e ι h := GS_nice_prod _ fun k _ => hwv _
  have hLr : ∀ ℓ, GS_nice fun h => GS_Lr T e ι h ℓ := fun ℓ => GS_nice_prod _ fun k _ => hlv _
  unfold GS_pkgD
  split
  · exact GS_nice_const 0
  · rename_i ℓ a tl _
    have hF : GS_niceM fun h => e.M a * loopWordMat (e.G h) e.M (e.E ι) e.Lt tl * e.G h a :=
      GS_niceM_mul (GS_niceM_mul (GS_niceM_const _) (GS_niceM_word e hz ι tl)) (GS_niceM_G e hz a)
    refine GS_nice_add (GS_nice_add (GS_nice_add ?_ ?_) ?_) ?_
    · exact GS_nice_mul (GS_nice_mul (GS_niceM_mul (GS_niceM_mul (GS_niceM_const _) (hWD tl))
        (GS_niceM_G e hz a) i j) hWt) (hLr ℓ)
    · exact GS_nice_mul (GS_nice_mul (GS_niceM_mul (GS_niceM_mul (GS_niceM_const _)
        (GS_niceM_word e hz ι tl)) (hdG a) i j) hWt) (hLr ℓ)
    · exact GS_nice_mul (GS_nice_mul (hF i j) (GS_nice_sum _ fun k _ =>
        GS_nice_mul (hwd _) (GS_nice_prod _ fun k' _ => hwv _))) (hLr ℓ)
    · exact GS_nice_mul (GS_nice_mul (hF i j) hWt) (GS_nice_sum _ fun k _ =>
        GS_nice_mul (hld _) (GS_nice_prod _ fun k' _ => hlv _))

/-- `GS_nice` functions are integrable for a law of almost surely Hermitian arrays. -/
private lemma GS_nice_integrable {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian)
    {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f) : Integrable f μ := by
  obtain ⟨⟨g, hgc, hg⟩, B, hB⟩ := hf
  refine Integrable.of_bound (hgc.aestronglyMeasurable.congr ?_) B ?_
  · filter_upwards [hμ] with h hh using (hg h hh).symm
  · filter_upwards [hμ] with h hh using hB h hh

/-- A `GS_nice` function times `h̄_{ij}` is integrable for a member of the class. -/
private lemma GS_nice_integrable_mul {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ)
    {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f) (i j : Idx D N) :
    Integrable (fun h => f h * starRingEnd ℂ (h i j)) μ := by
  have := hμ.prob
  obtain ⟨⟨g, hgc, hg⟩, B, hB⟩ := hf
  have hm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ :=
    (Complex.continuous_conj.comp
      ((continuous_apply j).comp (continuous_apply i))).aestronglyMeasurable
  have hint : Integrable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ := by
    refine (integrable_norm_iff hm).1 ?_
    simpa using hμ.integrable 1 i j
  refine hint.bdd_mul (c := B) (hgc.aestronglyMeasurable.congr ?_) ?_
  · filter_upwards [hμ.herm] with h hh using (hg h hh).symm
  · filter_upwards [hμ.herm] with h hh using hB h hh

/-! ### The terms `p + q ≤ 1` of Lemma 2.11 -/

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma GS_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      rw [hk, hl]
      have hre : (((h i i).re : ℝ) : ℂ) = h i i := Complex.conj_eq_iff_re.mp (h1 i i)
      simp [setEntry, hre]
    · simp [setEntry, hkl]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd, h1 k l]
      · simp [setEntry, hd, h1', h2]

/-- `𝒞^{(0,1)}(h) = 𝒞^{(1,0)}(h̄)`. -/
private lemma GS_ccum01 (ν : Measure ℂ) : ccum ν 0 1 = ccum (ν.map (starRingEnd ℂ)) 1 0 := by
  unfold ccum jointCum
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun B _ => ?_
  have hc : Continuous fun z : ℂ => ∏ i ∈ B, (if ((i : Fin (1 + 0)) : ℕ) < 1 then (fun z => z)
      else fun z => starRingEnd ℂ z) z :=
    continuous_finsetProd _ fun i _ => by
      split_ifs <;> first | exact continuous_id | exact Complex.continuous_conj
  rw [integral_map Complex.continuous_conj.measurable.aemeasurable hc.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun z => Finset.prod_congr rfl fun i _ => ?_)
  have : (i : ℕ) = 0 := by omega
  simp

/-- The low cumulants of an entry in a diagonal block for the block profile (`θ = 1`):
`𝒞^{(0,1)} = 0`, `𝒞^{(1,1)} = N⁻¹`, `𝒞^{(0,2)} = N⁻¹ δ_{ij}`. -/
private lemma GS_ccum_low {D N : ℕ} {C : ℕ → ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C 1 μ) (i j : Idx D N) (hij : i.1 = j.1) :
    ccum (μ.map fun h => h i j) 0 1 = 0 ∧ ccum (μ.map fun h => h i j) 1 1 = (N : ℂ)⁻¹ ∧
      ccum (μ.map fun h => h i j) 0 2 = if i = j then (N : ℂ)⁻¹ else 0 := by
  obtain ⟨-, h11, -, h02⟩ := llClass_ccum_low D N C 1 μ hμ i j
  have hv : (varProf D N 1 i j : ℂ) = (N : ℂ)⁻¹ := by simp [varProf, hij]
  refine ⟨?_, by rw [h11, hv], by rw [h02, hv]⟩
  rw [GS_ccum01]
  have hm1 : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  rw [Measure.map_map Complex.continuous_conj.measurable hm1]
  have e : (starRingEnd ℂ ∘ fun h : Idx D N → Idx D N → ℂ => h i j) =ᵐ[μ]
      fun h => h j i := by
    filter_upwards [hμ.herm] with h hh
    have := hh.apply j i
    simpa [Complex.star_def] using this
  rw [Measure.map_congr e]
  exact (llClass_ccum_low D N C 1 μ hμ j i).1

/-- The terms `p + q ≤ 1` of Lemma 2.11 [lem:complex_cumu] for `(F 𝒢)_{ij} W ⋯ f ⋯` and an
entry in a diagonal block: `N⁻¹ E` of the Leibniz derivative in the direction `E_{ij}`. -/
private lemma GS_low_terms {D N : ℕ} {C : ℕ → ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C 1 μ) (T : LoopExpr) (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin T.nb → Fin D) (i j : Idx D N) (hij : i.1 = j.1) :
    ccum (μ.map fun h => h i j) 0 1 / ((Nat.factorial 0 * Nat.factorial 0 : ℕ) : ℂ) *
        ∫ h, wirt 0 0 (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ +
      ccum (μ.map fun h => h i j) 1 1 / ((Nat.factorial 1 * Nat.factorial 0 : ℕ) : ℂ) *
        ∫ h, wirt 1 0 (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ +
      ccum (μ.map fun h => h i j) 0 2 / ((Nat.factorial 0 * Nat.factorial 1 : ℕ) : ℂ) *
        ∫ h, wirt 0 1 (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ =
      (N : ℂ)⁻¹ * ∫ h, GS_pkgD T e ι i j (Matrix.single i j 1) h ∂μ := by
  obtain ⟨h01, h11, h02⟩ := GS_ccum_low hμ i j hij
  have hw10 : ∫ h, wirt 1 0 (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ =
      (if i = j then (1 / 2 : ℂ) else 1) * ∫ h, GS_pkgD T e ι i j (Matrix.single i j 1) h ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have := GS_pkgVal_d T e hz h hh ι i j false (h i j)
    simp only [GS_d, GS_setEntry_self h hh] at this
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one, this, GS_dir,
      GS_pkgD_smul]
  have hw01 : ∫ h, wirt 0 1 (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ =
      (if i = j then (1 / 2 : ℂ) else 1) * ∫ h, GS_pkgD T e ι i j (Matrix.single j i 1) h ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have := GS_pkgVal_d T e hz h hh ι i j true (h i j)
    simp only [GS_d, GS_setEntry_self h hh] at this
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one, this, GS_dir,
      GS_pkgD_smul]
  rw [h01, h11, h02, hw10, hw01]
  by_cases hd : i = j
  · subst hd
    simp
    ring
  · simp [hd]

/-- The triangle `p + q ≤ l` split into the terms `p + q ≤ 1` and `p + q ≥ 2`. -/
private lemma GS_tri (l : ℕ) (hl : 1 ≤ l) (f : ℕ → ℕ → ℂ) :
    ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), f p q =
      f 0 0 + f 1 0 + f 0 1 + ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 2 ≤ p + q then f p q else 0) := by
  have hs : ∀ p q, f p q = (if p + q < 2 then f p q else 0) + (if 2 ≤ p + q then f p q else 0) := by
    intro p q
    by_cases h : 2 ≤ p + q
    · simp [h, show ¬ p + q < 2 by omega]
    · simp [h, show p + q < 2 by omega]
  have e1 : ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), f p q =
      (∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if p + q < 2 then f p q else 0)) +
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 2 ≤ p + q then f p q else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => hs p q
  have e2 : ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if p + q < 2 then f p q else 0) = f 0 0 + f 1 0 + f 0 1 := by
    rw [Finset.sum_eq_add_of_mem 0 1 (by simp) (by simp; omega) (by omega) (fun p hp hpq => ?_)]
    · have g0 : ∑ q ∈ Finset.range (l + 1 - 0), (if 0 + q < 2 then f 0 q else 0) =
          f 0 0 + f 0 1 := by
        rw [Finset.sum_eq_add_of_mem 0 1 (by simp) (by simp; omega) (by omega)
          (fun q hq hqq => by simp; omega)]
        simp
      have g1 : ∑ q ∈ Finset.range (l + 1 - 1), (if 1 + q < 2 then f 1 q else 0) = f 1 0 := by
        rw [Finset.sum_eq_single_of_mem 0 (by simp; omega) (fun q hq hq0 => by simp; omega)]
        simp
      rw [g0, g1]
      ring
    · refine Finset.sum_eq_zero fun q _ => ?_
      simp only [ite_eq_right_iff]
      intro h
      omega
  rw [e1, e2]

/-- For the block profile (`θ = 1`) an entry outside the diagonal blocks vanishes almost surely,
so `E f(h) h̄_{ij} = 0`. -/
private lemma GS_offblock {D N : ℕ} {C : ℕ → ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C 1 μ) (i j : Idx D N) (hij : i.1 ≠ j.1)
    (f : (Idx D N → Idx D N → ℂ) → ℂ) : ∫ h, f h * starRingEnd ℂ (h i j) ∂μ = 0 := by
  have h0 : (fun h : Idx D N → Idx D N → ℂ => ‖h i j‖ ^ 2) =ᵐ[μ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun h => by positivity) (hμ.integrable 2 i j)).1 ?_
    rw [hμ.var i j]
    simp [varProf, hij]
  have : (fun h : Idx D N → Idx D N → ℂ => f h * starRingEnd ℂ (h i j)) =ᵐ[μ] 0 := by
    filter_upwards [h0] with h hh
    have : h i j = 0 := by simpa using hh
    simp [this]
  rw [integral_congr_ae this]
  simp

/-- A sum over a list of integrable functions is integrable. -/
private lemma GS_integrable_list {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (F : LoopExpr → (Idx D N → Idx D N → ℂ) → ℂ) (hF : ∀ T, Integrable (F T) μ) :
    ∀ L : List LoopExpr, Integrable (fun h => (L.map fun T => F T h).sum) μ
  | [] => by simp
  | T :: L => by
      simp only [List.map_cons, List.sum_cons]
      exact (hF T).add (GS_integrable_list F hF L)

/-- The integral of a sum over a list of integrable functions. -/
private lemma GS_integral_list {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (F : LoopExpr → (Idx D N → Idx D N → ℂ) → ℂ) (hF : ∀ T, Integrable (F T) μ) :
    ∀ L : List LoopExpr, ∫ h, (L.map fun T => F T h).sum ∂μ = (L.map fun T => ∫ h, F T h ∂μ).sum
  | [] => by simp
  | T :: L => by
      simp only [List.map_cons, List.sum_cons]
      rw [integral_add (hF T) (GS_integrable_list F hF L), GS_integral_list F hF L]

/-- Exchanging a sum over the triangle `p + q ≤ l` with an inner finite sum. -/
private lemma GS_sum_comm_tri {κ : Type*} (l : ℕ) (S : Finset κ) (F : ℕ → ℕ → κ → ℂ) :
    ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), ∑ k ∈ S, F p q k =
      ∑ k ∈ S, ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), F p q k := by
  calc ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), ∑ k ∈ S, F p q k
      = ∑ p ∈ Finset.range (l + 1), ∑ k ∈ S, ∑ q ∈ Finset.range (l + 1 - p), F p q k :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The expansion (5.40) [expansion_for_integral_by_part_term] in expectation with its exact
remainder: `E 𝒯 - Σ_{𝒯'} E 𝒯' - Σ_{2 ≤ p+q ≤ l} 𝓡_𝒯(p, q)` is `-c_𝒯/(ND) Σ_ι Σ_{i,j}` over the
entries in the diagonal blocks of the remainder of Lemma 2.11 [lem:complex_cumu] for
`(F 𝒢)_{ij} W ⋯ f ⋯` at order `l`. -/
private lemma GS_exact {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) {C : ℕ → ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) {T : LoopExpr}
    (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (hf : T.focus = some (ℓ, a, tl)) (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (l : ℕ)
    (hl : 1 ≤ l) :
    (∫ h, T.evalH e h ∂μ) - (T.step.map fun T' => ∫ h, T'.evalH e h ∂μ).sum -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then T.remPQ e μ p q else 0) =
      -((D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹) / ((D : ℂ) * N) *
        ∑ ι : Fin T.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
          (if i.1 = j.1 then (∫ h, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) ∂μ) -
            ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
              ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
                ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ
          else 0) := by
  have hprob := hμ.prob
  set c := (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ with hc
  set κ := (D : ℂ) * N with hκ
  set A : (Fin T.nb → Fin D) → Idx D N → Idx D N → ℂ :=
    fun ι i j => ∫ h, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) ∂μ with hA
  set B : (Fin T.nb → Fin D) → Idx D N → Idx D N → ℂ :=
    fun ι i j => ∫ h, GS_pkgD T e ι i j (Matrix.single i j 1) h ∂μ with hB
  set K : ℕ → ℕ → (Fin T.nb → Fin D) → Idx D N → Idx D N → ℂ :=
    fun p q ι i j => ccum (μ.map fun h => h i j) p (q + 1) /
      ((p.factorial * q.factorial : ℕ) : ℂ) *
        ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ with hK
  have hint : ∀ T' : LoopExpr, Integrable (fun h => T'.evalH e h) μ :=
    fun T' => GS_nice_integrable hμ.herm (GS_nice_evalH T' e hz)
  have hiA : ∀ ι i j, Integrable (fun h => T.pkgVal e ι i j h * starRingEnd ℂ (h i j)) μ :=
    fun ι i j => GS_nice_integrable_mul hμ (GS_nice_pkgVal T e hz ι i j) i j
  have hiB : ∀ ι (i j : Idx D N), Integrable (fun h =>
      if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0) μ := by
    intro ι i j
    by_cases hij : i.1 = j.1
    · simpa [hij] using GS_nice_integrable hμ.herm (GS_nice_pkgD T e hz ι i j (Matrix.single i j 1))
    · simp [hij]
  -- the expectation of the identity at Hermitian arrays
  have h1 : (∫ h, T.evalH e h ∂μ) - (T.step.map fun T' => ∫ h, T'.evalH e h ∂μ).sum =
      c * ∑ ι : Fin T.nb → Fin D, (-κ⁻¹ * (∑ i : Idx D N, ∑ j : Idx D N, A ι i j) +
        κ⁻¹ * (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
          (if i.1 = j.1 then B ι i j else 0)) := by
    rw [← GS_integral_list (fun T' h => T'.evalH e h) hint,
      ← integral_sub (hint T) (GS_integrable_list _ hint _)]
    have hae : (fun h => T.evalH e h - (T.step.map fun T' => T'.evalH e h).sum) =ᵐ[μ]
        fun h => c * ∑ ι : Fin T.nb → Fin D, (-κ⁻¹ * (∑ i : Idx D N, ∑ j : Idx D N,
            T.pkgVal e ι i j h * starRingEnd ℂ (h i j)) +
          κ⁻¹ * (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
            (if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0)) := by
      filter_upwards [hμ.herm] with h hh using GS_step_id hD hN hT hf e hz h hh
    rw [integral_congr_ae hae, integral_const_mul]
    congr 1
    have hi1 : ∀ ι, Integrable (fun h => ∑ i : Idx D N, ∑ j : Idx D N,
        T.pkgVal e ι i j h * starRingEnd ℂ (h i j)) μ := fun ι =>
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hiA ι i j
    have hi2 : ∀ ι, Integrable (fun h => ∑ i : Idx D N, ∑ j : Idx D N,
        (if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0)) μ := fun ι =>
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hiB ι i j
    have hi3 : ∀ ι, Integrable (fun h => -κ⁻¹ * (∑ i : Idx D N, ∑ j : Idx D N,
        T.pkgVal e ι i j h * starRingEnd ℂ (h i j)) + κ⁻¹ * (N : ℂ)⁻¹ * ∑ i : Idx D N,
          ∑ j : Idx D N, (if i.1 = j.1 then GS_pkgD T e ι i j (Matrix.single i j 1) h else 0)) μ :=
      fun ι => ((hi1 ι).const_mul _).add ((hi2 ι).const_mul _)
    rw [integral_finsetSum _ fun ι _ => hi3 ι]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [integral_add ((hi1 ι).const_mul _) ((hi2 ι).const_mul _), integral_const_mul,
      integral_const_mul,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hiA ι i j,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hiB ι i j]
    congr 2
    · exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hiA ι i j
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hiB ι i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i.1 = j.1 <;> simp [hij, hB]
  -- the remainder terms `p + q ≥ 2`
  have h2 : ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 2 ≤ p + q then T.remPQ e μ p q else 0) =
      -c / κ * ∑ ι : Fin T.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
        (if i.1 = j.1 then ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then K p q ι i j else 0) else 0) := by
    have e1 : ∀ p q, (if 2 ≤ p + q then T.remPQ e μ p q else 0) =
        -c / κ * ∑ ι : Fin T.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
          (if 2 ≤ p + q then (if i.1 = j.1 then K p q ι i j else 0) else 0) := by
      intro p q
      by_cases hpq : 2 ≤ p + q
      · simp only [hpq, ite_true]
        rfl
      · simp [hpq]
    simp only [e1, ← Finset.mul_sum]
    congr 1
    rw [GS_sum_comm_tri]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [GS_sum_comm_tri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GS_sum_comm_tri]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i.1 = j.1 <;> simp [hij]
  rw [h1, h2]
  -- each entry in a diagonal block
  have h3 : ∀ ι (i j : Idx D N), (if i.1 = j.1 then A ι i j -
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), K p q ι i j else 0) =
      A ι i j - (N : ℂ)⁻¹ * (if i.1 = j.1 then B ι i j else 0) -
        (if i.1 = j.1 then ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then K p q ι i j else 0) else 0) := by
    intro ι i j
    by_cases hij : i.1 = j.1
    · simp only [hij, ite_true]
      rw [GS_tri l hl, ← GS_low_terms hμ T e hz ι i j hij]
      simp only [hK, Nat.factorial_zero, Nat.factorial_one]
      ring
    · simp only [hij, ite_false, mul_zero, sub_zero]
      exact (GS_offblock hμ i j hij _).symm
  simp only [hA, hB, hK] at h3 ⊢
  rw [Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => h3 ι i j]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-! ### Norm bounds on the slots -/

/-- `|⟨B⟩| ≤ ‖B‖`. -/
private lemma GS_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    ‖ntr B‖ ≤ opNorm B := by
  have h0 : 0 ≤ opNorm B := norm_nonneg _
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc | hc
  · simp [hc, h0]
  · have hc' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hc
    rw [inv_mul_le_iff₀ hc']
    calc ‖B.trace‖ ≤ ∑ i, ‖B i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, opNorm B := Finset.sum_le_sum fun i _ => GS_entry_le B i i
      _ = (Fintype.card ι : ℝ) * opNorm B := by simp

/-- The bounds on the slots of an environment with `2 C₀ ‖A‖ ≤ 1/10`, `|c_a| ≤ C₀`, `Im z_a > 0`
and `|δ| ≤ K ⟨Λ²⟩`: `‖c_a Λ‖ ≤ 1/10`, `‖𝔐_a‖ ≤ 5/4`, `|m(z_a)| < 1` and `‖Λ̃‖ ≤ (2 + |K|) ‖A‖`. -/
private lemma GS_norms {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (C₀ K : ℝ) (hC₀ : 1 ≤ C₀)
    (e : LoopEnv D N) (hA : 2 * C₀ * opNorm e.A ≤ 1 / 10) (hc : ∀ a, |e.c a| ≤ C₀)
    (hz : ∀ a, 0 < (e.z a).im) (hδ : |e.δ| ≤ K * avgSq (lam D N e.A)) :
    (∀ a, opNorm ((e.c a : ℂ) • lam D N e.A) ≤ 1 / 10) ∧ (∀ a, opNorm (e.M a) ≤ 5 / 4) ∧
      (∀ a, ‖mExt ((e.c a : ℂ) • lam D N e.A) (e.z a)‖ < 1) ∧
      opNorm e.Lt ≤ (2 + |K|) * opNorm e.A ∧
      (∀ a, opNorm (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a)) ≤ 5 / 4) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hA0 : 0 ≤ opNorm e.A := norm_nonneg _
  have hslot : ∀ a, opNorm ((e.c a : ℂ) • lam D N e.A) ≤ 1 / 10 := by
    intro a
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |e.c a| * opNorm (lam D N e.A) ≤ C₀ * (2 * opNorm e.A) :=
          mul_le_mul (hc a) (opNorm_lam_le D N e.A) (norm_nonneg _) (by linarith)
      _ ≤ 1 / 10 := by linarith
  have hmsol : ∀ a, mExt ((e.c a : ℂ) • lam D N e.A) (e.z a) =
      mSol ((e.c a : ℂ) • lam D N e.A) (e.z a) := fun a => by simp [mExt, hz a]
  have hMsol : ∀ a, MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) =
      MSol ((e.c a : ℂ) • lam D N e.A) (e.z a) := fun a => by rw [MExt, MSol, hmsol a]
  have hM5 : ∀ a, opNorm (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a)) ≤ 5 / 4 := by
    intro a
    obtain ⟨-, -, h3⟩ := mSol_apriori _ (GS_slot_herm e a) (hslot a) _ (hz a)
    have h4 : (1 - 2 * opNorm ((e.c a : ℂ) • lam D N e.A))⁻¹ ≤ 5 / 4 := by
      have := hslot a
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    rw [hMsol]; exact h3.le.trans h4
  refine ⟨hslot, fun a => ?_, fun a => ?_, ?_, hM5⟩
  · have h5 := hM5 a
    simp only [LoopEnv.M]
    split_ifs
    · rw [(mExt_conj _ (GS_slot_herm e a) _ (hz a).ne').2, GS_opNorm_conjTranspose]
      exact h5
    · exact h5
  · rw [hmsol]
    exact (mSol_apriori _ (GS_slot_herm e a) (hslot a) _ (hz a)).2.1
  · have hA' : opNorm e.A ≤ 1 / 20 := by nlinarith
    have hone : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 := by
      unfold opNorm
      rw [map_one]
      exact ContinuousLinearMap.norm_id_le
    have hav : |avgSq (lam D N e.A)| ≤ opNorm (lam D N e.A) ^ 2 := by
      unfold avgSq
      refine (Complex.abs_re_le_norm _).trans ((GS_ntr_le _).trans ?_)
      rw [sq]
      exact opNorm_mul_le _ _
    have hL := opNorm_lam_le D N e.A
    have hL0 : 0 ≤ opNorm (lam D N e.A) := norm_nonneg _
    have hδ' : |e.δ| ≤ |K| * (4 * opNorm e.A ^ 2) := by
      calc |e.δ| ≤ K * avgSq (lam D N e.A) := hδ
        _ ≤ |K| * |avgSq (lam D N e.A)| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ |K| * (opNorm (lam D N e.A) ^ 2) := mul_le_mul_of_nonneg_left hav (abs_nonneg _)
        _ ≤ |K| * (4 * opNorm e.A ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            nlinarith
    have hLt : opNorm e.Lt ≤ opNorm (lam D N e.A) + |e.δ| := by
      unfold LoopEnv.Lt
      rw [sub_eq_add_neg, ← neg_smul]
      refine (opNorm_add_le _ _).trans ?_
      rw [opNorm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_left hone (abs_nonneg e.δ)
      linarith
    have hK0 : 0 ≤ |K| := abs_nonneg K
    have h4 : |K| * (4 * opNorm e.A ^ 2) ≤ |K| * opNorm e.A :=
      mul_le_mul_of_nonneg_left (by nlinarith) hK0
    nlinarith

/-! ### The event of the one-entry expansion -/

/-- `N^{τ/4} (√(|Im m|/(N|η|)) + 1/(N|η|)) ≤ 1` for `|m| ≤ 1`, `|η| ≥ N^{-1+τ}` and
`N ≥ 2^{4/τ}`. -/
private lemma GS_psi_le (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : (2 : ℝ) ^ (4 / τ) ≤ N) (m z : ℂ)
    (hm : ‖m‖ ≤ 1) (hz : (N : ℝ) ^ (-1 + τ) ≤ |z.im|) :
    (N : ℝ) ^ (τ / 4) * (Real.sqrt (|m.im| / ((N : ℝ) * |z.im|)) + 1 / ((N : ℝ) * |z.im|)) ≤ 1 := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 / τ) := Real.one_le_rpow (by norm_num) (by positivity)
  have hN1 : (1 : ℝ) ≤ N := h2.trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  set t := (N : ℝ) ^ (τ / 4) with ht
  have ht2 : 2 ≤ t := by
    have := Real.rpow_le_rpow (by positivity) hN (show 0 ≤ τ / 4 by positivity)
    rwa [← Real.rpow_mul (by norm_num), show 4 / τ * (τ / 4) = 1 by field_simp,
      Real.rpow_one] at this
  have ht4 : (N : ℝ) ^ τ = t ^ 4 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hu : t ^ 4 ≤ (N : ℝ) * |z.im| := by
    rw [← ht4]
    calc (N : ℝ) ^ τ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := by
          rw [← Real.rpow_one_add' hN0.le (by linarith)]
          norm_num
      _ ≤ (N : ℝ) * |z.im| := mul_le_mul_of_nonneg_left hz hN0.le
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < (N : ℝ) * |z.im| := lt_of_lt_of_le (by positivity) hu
  have hmi : |m.im| ≤ 1 := (Complex.abs_im_le_norm m).trans hm
  have hs : Real.sqrt (|m.im| / ((N : ℝ) * |z.im|)) ≤ 1 / t ^ 2 := by
    rw [show (1 : ℝ) / t ^ 2 = Real.sqrt (1 / t ^ 4) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, show t ^ 4 = (t ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hu0 (by positivity)]
    nlinarith [abs_nonneg m.im]
  have hv : 1 / ((N : ℝ) * |z.im|) ≤ 1 / t ^ 4 := one_div_le_one_div_of_le (by positivity) hu
  calc t * (Real.sqrt (|m.im| / ((N : ℝ) * |z.im|)) + 1 / ((N : ℝ) * |z.im|))
      ≤ t * (1 / t ^ 2 + 1 / t ^ 4) := mul_le_mul_of_nonneg_left (add_le_add hs hv) ht0.le
    _ ≤ 1 := by
      rw [mul_add, show t * (1 / t ^ 2) = 1 / t by field_simp,
        show t * (1 / t ^ 4) = 1 / t ^ 3 by field_simp]
      have h1 : 1 / t ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ht2
      have h3 : 1 / t ^ 3 ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
      linarith

/-- The family `{(c_a Λ, z_a)}` of the pairs of the slots. -/
private def GS_Xi {D N : ℕ} (e : LoopEnv D N) : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
  Finset.univ.image fun a : Fin 2 => ((e.c a : ℂ) • lam D N e.A, e.z a)

/-- The standard basis of `ℂ^{DN}`. -/
private def GS_V (D N : ℕ) : Finset (Idx D N → ℂ) :=
  Finset.univ.image fun k : Idx D N => Pi.single k (1 : ℂ)

/-- The event where an entry of a resolvent of a slot exceeds `3`, from (2.22)
[eq:aniso_local] of Lemma 2.9 [lem_loc] (`aniso_local`): its probability is at most
`2 (DN)² N^{-D''}`. -/
private lemma GS_event (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (K : ℝ) :
    ∀ D'' : ℝ, 0 < D'' → ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
        μ {h | ∃ p ∈ GS_Xi e, ∃ x ∈ GS_V D N, ∃ y ∈ GS_V D N,
            3 < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ≤
          ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'')) := by
  intro D'' hD''
  obtain ⟨Na, hNa⟩ := aniso_local D (by omega) (δA / 2) τ (by linarith) hτ C (τ / 4) (by linarith)
    D'' hD''
  refine ⟨max Na (max ⌈C₀ ^ (2 / δA)⌉₊ (max ⌈(2 : ℝ) ^ (4 / τ)⌉₊ 1)), ?_⟩
  intro N hN μ hμ e hA hA2 hc hz hδ
  have hprob := hμ.prob
  have hNa' : Na ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right (le_of_max_le_right hN))
  have hNC : C₀ ^ (2 / δA) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left (le_of_max_le_right hN))
  have hN2 : (2 : ℝ) ^ (4 / τ) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left (le_of_max_le_right
      (le_of_max_le_right hN)))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hslot, -, hm1, -, hM5⟩ := GS_norms hD hN1 C₀ K hC₀ e hA2 hc (fun a => (hz a).2) hδ
  -- the slots are small
  have hsmall : ∀ a, opNorm ((e.c a : ℂ) • e.A) ≤ (N : ℝ) ^ (-(δA / 2)) := by
    intro a
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hC : C₀ ≤ (N : ℝ) ^ (δA / 2) := by
      have := Real.rpow_le_rpow (by positivity) hNC (show 0 ≤ δA / 2 by positivity)
      rwa [← Real.rpow_mul (by linarith), show 2 / δA * (δA / 2) = 1 by field_simp,
        Real.rpow_one] at this
    calc |e.c a| * opNorm e.A ≤ C₀ * (N : ℝ) ^ (-δA) :=
          mul_le_mul (hc a) hA (norm_nonneg _) (by linarith)
      _ ≤ (N : ℝ) ^ (δA / 2) * (N : ℝ) ^ (-δA) :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ = (N : ℝ) ^ (-(δA / 2)) := by
          rw [← Real.rpow_add hN0]
          ring_nf
  set bad : Fin 2 × Idx D N × Idx D N → Set (Idx D N → Idx D N → ℂ) := fun t =>
    {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ (τ / 4) * psiIso (lam D N ((e.c t.1 : ℂ) • e.A)) N z <
      ‖star (Pi.single t.2.1 (1 : ℂ)) ⬝ᵥ ((res (Matrix.of h + lam D N ((e.c t.1 : ℂ) • e.A)) z -
        MExt (lam D N ((e.c t.1 : ℂ) • e.A)) z) *ᵥ Pi.single t.2.2 (1 : ℂ))‖} with hbad
  have hone : ∀ k : Idx D N, ∑ i, ‖(Pi.single k (1 : ℂ) : Idx D N → ℂ) i‖ ^ 2 = 1 := by
    intro k
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hb : ∀ t, μ (bad t) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'')) := fun t =>
    hNa N hNa' 1 zero_le_one le_rfl μ hμ _ (hsmall t.1) _ _ (hone _) (hone _)
  have hsub : {h : Idx D N → Idx D N → ℂ | ∃ p ∈ GS_Xi e, ∃ x ∈ GS_V D N, ∃ y ∈ GS_V D N,
      3 < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ⊆
      {h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ t, bad t := by
    rintro h ⟨p, hp, x, hx, y, hy, h3⟩
    by_cases hh : (Matrix.of h).IsHermitian
    · right
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hy
      refine Set.mem_iUnion.2 ⟨(a, k, l), e.z a, (hz a).1, ?_⟩
      rw [symArr_of_isHermitian h hh] at h3
      have e1 : resFactorEval (Pi.single k (1 : ℂ), Pi.single l (1 : ℂ),
          (e.c a : ℂ) • lam D N e.A, e.z a) h =
          res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a) k l := by
        simp [resFactorEval, Matrix.mulVec_single]
      have e2 : star (Pi.single k (1 : ℂ)) ⬝ᵥ
          ((res (Matrix.of h + lam D N ((e.c a : ℂ) • e.A)) (e.z a) -
            MExt (lam D N ((e.c a : ℂ) • e.A)) (e.z a)) *ᵥ Pi.single l (1 : ℂ)) =
          res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a) k l -
            MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) k l := by
        rw [← lam_smul]
        simp [Matrix.mulVec_single]
      rw [e2]
      rw [e1] at h3
      have hMk := (GS_entry_le (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a)) k l).trans (hM5 a)
      have hpsi : (N : ℝ) ^ (τ / 4) * psiIso (lam D N ((e.c a : ℂ) • e.A)) N (e.z a) ≤ 1 := by
        unfold psiIso
        refine GS_psi_le τ hτ N hN2 _ _ ?_ (hz a).1.2
        rw [← lam_smul]
        exact (hm1 a).le
      have := norm_sub_norm_le (res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a) k l)
        (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) k l)
      linarith
    · left; exact hh
  have hherm : μ {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} = 0 :=
    ae_iff.mp hμ.herm
  calc μ {h | ∃ p ∈ GS_Xi e, ∃ x ∈ GS_V D N, ∃ y ∈ GS_V D N,
        3 < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖}
      ≤ μ ({h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ t, bad t) := measure_mono hsub
    _ ≤ μ {h | ¬ (Matrix.of h).IsHermitian} + μ (⋃ t, bad t) := measure_union_le _ _
    _ ≤ 0 + ∑ t, μ (bad t) := by rw [hherm]; gcongr; exact measure_iUnion_fintype_le _ _
    _ ≤ 0 + ∑ _t : Fin 2 × Idx D N × Idx D N, ENNReal.ofReal ((N : ℝ) ^ (-D'')) := by
        gcongr with t; exact hb t
    _ = ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'')) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [Fintype.card_prod, Fintype.card_fin]
        push_cast
        ring

/-! ### The remainder bound -/

/-- The coefficient `D^{dexp} N^{-S}` has modulus at most `D^{dexp⁺}`. -/
private lemma GS_coef (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (dexp : ℤ) (S : ℕ) :
    ‖(D : ℂ) ^ dexp * ((N : ℂ) ^ S)⁻¹‖ ≤ (D : ℝ) ^ dexp.toNat := by
  rw [norm_mul, norm_zpow, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (D : ℝ) ^ dexp ≤ (D : ℝ) ^ dexp.toNat := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ hD' (Int.self_le_toNat dexp)
  have h2 : ((N : ℝ) ^ S)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hN')
  calc (D : ℝ) ^ dexp * ((N : ℝ) ^ S)⁻¹ ≤ (D : ℝ) ^ dexp * 1 :=
        mul_le_mul_of_nonneg_left h2 (zpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (D : ℝ) ^ dexp.toNat := by rw [mul_one]; exact h1

/-- The final numerical inequality: `Q n^{c+1} (n^{-(c+d+3)} 18^L + 2^L n^L s n^{-E}) ≤ n^{-(d+1)}`
for `E = c + 1 + L + d + 2` and `Q (18^L + 2^L s) ≤ n`. -/
private lemma GS_num (n : ℝ) (hn : 1 ≤ n) (Q s : ℝ) (L c d E : ℕ) (hE : E = c + 1 + L + d + 2)
    (hbig : Q * (18 ^ L + 2 ^ L * s) ≤ n) :
    Q * n ^ (c + 1) * ((n ^ (c + d + 3))⁻¹ * 18 ^ L + 2 ^ L * n ^ L * (s * (n ^ E)⁻¹)) ≤
      (n ^ (d + 1))⁻¹ := by
  have hn0 : 0 < n := by linarith
  have key : Q * n ^ (c + 1) * ((n ^ (c + d + 3))⁻¹ * 18 ^ L + 2 ^ L * n ^ L * (s * (n ^ E)⁻¹)) =
      Q * (18 ^ L + 2 ^ L * s) * (n ^ (d + 2))⁻¹ := by
    rw [hE]
    field_simp
    ring
  rw [key]
  calc Q * (18 ^ L + 2 ^ L * s) * (n ^ (d + 2))⁻¹ ≤ n * (n ^ (d + 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = (n ^ (d + 1))⁻¹ := by field_simp; ring

/-- The expansion (5.40) for every order `l ≥ l₀(𝒯, D')`: the remainder of Lemma 2.11
[lem:complex_cumu] at order `l`, summed over the entries and the bound block indices, is at most
`N^{-D'} ‖A‖²` for `N ≥ N₀(l)`, uniformly in the class and in the slots. -/
private lemma GS_gauss_all (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (T : LoopExpr) (hT : T.wf = true) (hf : T.focus.isSome = true) :
    ∀ D' : ℝ, 0 < D' → ∃ l₀ : ℕ, 1 ≤ l₀ ∧ ∀ l : ℕ, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
        ‖(∫ h, T.evalH e h ∂μ) - (T.step.map fun T' => ∫ h, T'.evalH e h ∂μ).sum -
            ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
              (if 2 ≤ p + q then T.remPQ e μ p q else 0)‖ ≤
          (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
  intro D' hD'
  obtain ⟨⟨ℓ, a, tl⟩, hfoc⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨cP, hP⟩ := loop_pkgVal_poly T hT
  set m := (T.charsZ.1 + T.charsZ.2.2.1).toNat with hm
  set d := ⌈D'⌉₊ with hd
  refine ⟨2 * (cP + d + 3), by omega, fun l hl => ?_⟩
  set L := m + l + 1 with hL
  set E := cP + 1 + L + d + 2 with hE
  obtain ⟨Khp, hKhp0, hKhp⟩ := expansion_hp l m (8 * E) C
  obtain ⟨N₁, hN₁⟩ := GS_event D hD δA τ C₀ hδA hτ hC₀ C K ((2 * E + 2 : ℕ) : ℝ)
    (by positivity)
  set Q := (D : ℝ) ^ (T.dexp.toNat + T.nb + cP + 1) * Khp * 4 ^ cP * (2 + |K|) ^ 2 with hQ
  set s := Real.sqrt (2 * (D : ℝ) ^ 2 + 1) with hs
  refine ⟨max N₁ (max (72 ^ 4) ⌈Q * (18 ^ L + 2 ^ L * s)⌉₊), ?_⟩
  intro N hN μ hμ e hA hA2 hc hz hδ
  have hprob := hμ.prob
  have hNN₁ : N₁ ≤ N := le_of_max_le_left hN
  have hN72 : 72 ^ 4 ≤ N := le_of_max_le_left (le_of_max_le_right hN)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN72
  have hNQ : Q * (18 ^ L + 2 ^ L * s) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right (le_of_max_le_right hN))
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hD1 : 1 ≤ D := by omega
  have hzpos : ∀ a, 0 < (e.z a).im := fun a => (hz a).2
  obtain ⟨-, hMn, -, hLt, -⟩ := GS_norms hD hN1 C₀ K hC₀ e hA2 hc hzpos hδ
  have hev := hN₁ N hNN₁ μ hμ e hA hA2 hc hz hδ
  set ε₀ := 2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-((2 * E + 2 : ℕ) : ℝ)) with hε₀
  set M := (N : ℝ) ^ (-(1 / 4 : ℝ)) with hM
  set η := min (e.z 0).im (e.z 1).im with hη
  have hη0 : 0 < η := lt_min (hzpos 0) (hzpos 1)
  have hηN : (N : ℝ) ^ (-1 + τ) ≤ η := by
    refine le_min ?_ ?_
    · have := (hz 0).1.2; rwa [abs_of_pos (hzpos 0)] at this
    · have := (hz 1).1.2; rwa [abs_of_pos (hzpos 1)] at this
  have hη1 : 1 + η⁻¹ ≤ 2 * N := by
    have h1 : η⁻¹ ≤ ((N : ℝ) ^ (-1 + τ))⁻¹ := inv_anti₀ (by positivity) hηN
    have h2 : ((N : ℝ) ^ (-1 + τ))⁻¹ ≤ N := by
      rw [← Real.rpow_neg hn0.le]
      calc (N : ℝ) ^ (-(-1 + τ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = N := Real.rpow_one _
    linarith
  have hM0 : 0 < M := by positivity
  have hM72 : 24 * M * 3 ≤ 1 := by
    have h1 : (72 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have := Real.rpow_le_rpow (by norm_num) (show ((72 : ℝ) ^ 4) ≤ N by exact_mod_cast hN72)
        (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      rwa [show ((72 : ℝ) ^ 4) = (72 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
        show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at this
    have h2 : M = ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hn0.le _
    rw [h2]
    have h3 : ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹ ≤ 1 / 72 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hε₀0 : 0 ≤ ε₀ := by positivity
  set Bnd := Khp * (((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2) *
    ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * 3) ^ (m + l + 1) +
      (2 * N) ^ (m + l + 1) * Real.sqrt (ε₀ + ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-((8 * E : ℕ) : ℝ))))
    with hBnd
  have hBnd0 : 0 ≤ Bnd := by positivity
  have herr : ∀ (ι : Fin T.nb → Fin D) (i j : Idx D N), i.1 = j.1 →
      ‖(∫ h, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
            ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ‖ ≤ Bnd := by
    intro ι i j hij
    obtain ⟨P, hPe, hPt, hPm⟩ := hP D N e ι i j
    have hΞ : ∀ p ∈ GS_Xi e, p.1.IsHermitian ∧ η ≤ p.2.im := by
      intro p hp
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
      refine ⟨GS_slot_herm e b, ?_⟩
      fin_cases b
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hVn : ∀ x ∈ GS_V D N, ∑ r, ‖x r‖ ^ 2 ≤ 1 := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
      simp
    have hVi : ∀ k : Idx D N, Pi.single k (1 : ℂ) ∈ GS_V D N := fun k =>
      Finset.mem_image_of_mem _ (Finset.mem_univ k)
    have hP' : ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ GS_V D N ∧ f.2.1 ∈ GS_V D N ∧
        ∃ p ∈ GS_Xi e, f.2.2 = p ∨ f.2.2 = (p.1, starRingEnd ℂ p.2) := by
      intro t ht
      refine ⟨(hPt t ht).1, fun f hf => ?_⟩
      obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, b, hb⟩ := (hPt t ht).2 f hf
      refine ⟨hk ▸ hVi k, hk' ▸ hVi k', ((e.c b : ℂ) • lam D N e.A, e.z b),
        Finset.mem_image_of_mem _ (Finset.mem_univ b), ?_⟩
      rw [hb]
      by_cases hs : e.s b
      · right; simp [hs]
      · left; simp [hs]
    have key := hKhp D N 1 μ hμ (GS_Xi e) η hη0 hΞ i j (GS_V D N) (hVi i) (hVi j) hVn P hP'
      3 M ε₀ (by norm_num) hM0 hM72 hε₀0 hev
    have e1 : ∫ h, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) ∂μ =
        ∫ h, resPolyEval P h * starRingEnd ℂ (h i j) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hμ.herm] with h hh
      rw [hPe h hh]
    have e2 : ∀ p q, ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ =
        ∫ h, wirt p q (fun w => resPolyEval P (setEntry h i j w)) (h i j) ∂μ := by
      intro p q
      refine integral_congr_ae ?_
      filter_upwards [hμ.herm] with h hh
      have : (fun w => T.pkgVal e ι i j (setEntry h i j w)) =
          fun w => resPolyEval P (setEntry h i j w) := by
        funext w
        exact hPe _ (GS_setEntry_herm h hh i j w)
      rw [this]
    simp only [e1, e2]
    refine key.trans ?_
    have hmass : (P.map fun t => ‖t.1‖).sum ≤
        ((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2 := by
      refine hPm.trans ?_
      have hM01 : 1 + opNorm (e.M 0) + opNorm (e.M 1) ≤ 4 := by
        linarith [hMn 0, hMn 1]
      have hLt0 : 0 ≤ opNorm e.Lt := norm_nonneg _
      have hm0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
      have hm1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
      gcongr
    have hL1 : (1 + η⁻¹) ^ (m + l + 1) ≤ (2 * N) ^ (m + l + 1) :=
      pow_le_pow_left₀ (by positivity) hη1 _
    rw [hBnd]
    gcongr
  rw [GS_exact hD hN1 hμ hT hfoc e hzpos l (by omega)]
  set c := (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ with hc
  have hcn : ‖c‖ ≤ (D : ℝ) ^ T.dexp.toNat := GS_coef D N hD1 hN1 T.dexp T.S
  have hκ0 : (0 : ℝ) < (D : ℝ) * N := by
    have : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    positivity
  have hsum : ‖∑ ι : Fin T.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
      (if i.1 = j.1 then (∫ h, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
            ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ
      else 0)‖ ≤ (D : ℝ) ^ T.nb * ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _ι : Fin T.nb → Fin D, ∑ _i : Idx D N, ∑ _j : Idx D N, Bnd :=
          Finset.sum_le_sum fun ι _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
              split_ifs with hij
              · exact herr ι i j hij
              · simpa using hBnd0))
      _ = (D : ℝ) ^ T.nb * ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hnorm : ‖-c / ((D : ℂ) * N)‖ = ‖c‖ / ((D : ℝ) * N) := by
    rw [norm_div, norm_neg, show ‖(D : ℂ) * N‖ = (D : ℝ) * N by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]]
  -- the terms of `Bnd`
  have hT1 : (N : ℝ) ^ (-((l : ℝ) + 2) / 2) ≤ ((N : ℝ) ^ (cP + d + 3))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn0.le]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have : (2 * ((cP + d + 3 : ℕ) : ℝ)) ≤ l := by exact_mod_cast hl
    push_cast at this ⊢
    linarith
  have hT2 : Real.sqrt (ε₀ + ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-((8 * E : ℕ) : ℝ))) =
      s * ((N : ℝ) ^ E)⁻¹ := by
    have h14 : (N : ℝ) ^ ((1 : ℝ) / 2) * M = (N : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hM, ← Real.rpow_add hn0]; norm_num
    have hk : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ (-((8 * E : ℕ) : ℝ)) = ((N : ℝ) ^ (2 * E))⁻¹ := by
      rw [← Real.rpow_mul hn0.le, ← Real.rpow_natCast, ← Real.rpow_neg hn0.le]
      congr 1
      push_cast
      ring
    have hε : ε₀ = 2 * (D : ℝ) ^ 2 * ((N : ℝ) ^ (2 * E))⁻¹ := by
      rw [hε₀, Real.rpow_neg hn0.le, Real.rpow_natCast]
      field_simp
      ring
    rw [h14, hk, hε, show 2 * (D : ℝ) ^ 2 * ((N : ℝ) ^ (2 * E))⁻¹ + ((N : ℝ) ^ (2 * E))⁻¹ =
      (2 * (D : ℝ) ^ 2 + 1) * (((N : ℝ) ^ E)⁻¹) ^ 2 by rw [pow_mul']; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hfin : (D : ℝ) ^ T.dexp.toNat * (D : ℝ) ^ T.nb * ((D : ℝ) * N) * Bnd ≤
      ((N : ℝ) ^ (d + 1))⁻¹ * opNorm e.A ^ 2 := by
    have hA0 : 0 ≤ opNorm e.A ^ 2 := sq_nonneg _
    have hK0 : 0 ≤ (2 + |K|) := by positivity
    have hnum := GS_num (N : ℝ) hn1 Q s L cP d E hE hNQ
    have hb1 : Bnd ≤ Khp * (((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2) *
        (((N : ℝ) ^ (cP + d + 3))⁻¹ * 18 ^ L + 2 ^ L * (N : ℝ) ^ L * (s * ((N : ℝ) ^ E)⁻¹)) := by
      rw [hBnd, hT2, show (6 * 3 : ℝ) = 18 by norm_num]
      gcongr
      exact le_of_eq (mul_pow _ _ _)
    calc (D : ℝ) ^ T.dexp.toNat * (D : ℝ) ^ T.nb * ((D : ℝ) * N) * Bnd
        ≤ (D : ℝ) ^ T.dexp.toNat * (D : ℝ) ^ T.nb * ((D : ℝ) * N) *
          (Khp * (((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2) *
          (((N : ℝ) ^ (cP + d + 3))⁻¹ * 18 ^ L + 2 ^ L * (N : ℝ) ^ L * (s * ((N : ℝ) ^ E)⁻¹))) :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (Q * (N : ℝ) ^ (cP + 1) * (((N : ℝ) ^ (cP + d + 3))⁻¹ * 18 ^ L +
          2 ^ L * (N : ℝ) ^ L * (s * ((N : ℝ) ^ E)⁻¹))) * opNorm e.A ^ 2 := by
          rw [hQ]; ring
      _ ≤ ((N : ℝ) ^ (d + 1))⁻¹ * opNorm e.A ^ 2 := mul_le_mul_of_nonneg_right hnum hA0
  have hD'd : ((N : ℝ) ^ (d + 1))⁻¹ ≤ (N : ℝ) ^ (-D') := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn0.le]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have := Nat.le_ceil D'
    push_cast
    linarith
  calc ‖-c / ((D : ℂ) * N) * ∑ ι : Fin T.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
      (if i.1 = j.1 then (∫ h, T.pkgVal e ι i j h * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
            ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ
      else 0)‖ ≤ ‖c‖ / ((D : ℝ) * N) * ((D : ℝ) ^ T.nb * ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd) := by
        rw [norm_mul, hnorm]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (D : ℝ) ^ T.dexp.toNat / ((D : ℝ) * N) *
        ((D : ℝ) ^ T.nb * ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd) := by gcongr
    _ = (D : ℝ) ^ T.dexp.toNat * (D : ℝ) ^ T.nb * ((D : ℝ) * N) * Bnd := by
        field_simp
    _ ≤ ((N : ℝ) ^ (d + 1))⁻¹ * opNorm e.A ^ 2 := hfin
    _ ≤ (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := mul_le_mul_of_nonneg_right hD'd (sq_nonneg _)

/-! ### The decomposition (5.38) of the expanded expressions -/

/-- A sum of natural numbers over a list is the sum over the range of its positions. -/
private lemma GS_sum_list_nat {α : Type*} (f : α → ℕ) (d : α) :
    ∀ l : List α, (l.map f).sum = ∑ k ∈ Finset.range l.length, f (l.getD k d)
  | [] => by simp
  | x :: l => by
      rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
        GS_sum_list_nat f d l]
      simp [add_comm]

/-- An expression of the class (5.33) [definition_class_of_expression_loop] with `k₁ ≥ 1` or
`k₂ ≥ 1` has the decomposition (5.38) [explicit_cT]. -/
private lemma GS_focus_isSome {T : LoopExpr} (hT : T.wf = true) (hk : 1 ≤ T.kk 0 ∨ 1 ≤ T.kk 1) :
    T.focus.isSome = true := by
  set o : Fin 2 := if 1 ≤ T.kk 0 then 0 else 1 with ho
  have hko : 1 ≤ T.kk o := by
    by_cases h : 1 ≤ T.kk 0
    · simp only [ho, h, ite_true]
    · simp only [ho, h, ite_false]; omega
  have hcnt : (T.loops.map fun w => w.count (.lamt o)).sum = 1 := by
    simp only [LoopExpr.wf, Bool.and_eq_true, beq_iff_eq] at hT
    obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := hT
    by_cases h : 1 ≤ T.kk 0
    · simpa [ho, h] using h0
    · simpa [ho, h] using h1
  rw [GS_sum_list_nat _ []] at hcnt
  set p : List LoopLetter → Bool := fun w => w.contains (.lamt o) with hp
  set n := T.loops.length with hn
  -- the loops containing `Λ̃_o`
  have hpos : ∀ k, p (T.loops.getD k []) = true ↔ 1 ≤ (T.loops.getD k []).count (.lamt o) := by
    intro k
    simp only [hp, List.contains_iff_mem]
    exact ⟨fun h => List.count_pos_iff.2 h, fun h => List.count_pos_iff.1 h⟩
  have hex : ∃ w ∈ T.loops, p w = true := by
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : (∑ k ∈ Finset.range n,
      (T.loops.getD k []).count (.lamt o)) ≠ 0)
    exact ⟨_, GS_getD_mem _ _ k (Finset.mem_range.1 hk), (hpos k).2 (by omega)⟩
  set ℓ := T.loops.findIdx p with hℓdef
  have hℓ : ℓ < n := List.findIdx_lt_length_of_exists hex
  have hgℓ : T.loops.getD ℓ [] = T.loops[ℓ] := List.getD_eq_getElem _ _ hℓ
  have hpℓ : p (T.loops.getD ℓ []) = true := by rw [hgℓ]; exact List.findIdx_getElem
  have huniq : ∀ k < n, k ≠ ℓ → p (T.loops.getD k []) = false := by
    intro k hk hkℓ
    by_contra hc
    have hc' : p (T.loops.getD k []) = true := by simpa using hc
    have := Finset.add_le_sum (f := fun k => (T.loops.getD k []).count (.lamt o))
      (s := Finset.range n) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hk)
      (Finset.mem_range.2 hℓ) hkℓ
    have h1 := (hpos k).1 hc'
    have h2 := (hpos ℓ).1 hpℓ
    omega
  -- `k_o` is the count of the loop at `ℓ`
  set f : List LoopLetter → ℕ := fun w => if w.contains (.lamt o) then
    ((((w.rotate (w.idxOf (.lamt o))).drop 1).reverse.takeWhile fun x =>
        match x with | .lamt _ => false | _ => true).countP fun x =>
          match x with | .res _ => true | _ => false) else 0 with hfdef
  have hkk : T.kk o = f (T.loops.getD ℓ []) := by
    have h0 : T.kk o = (T.loops.map f).sum := rfl
    rw [h0, GS_sum_list_nat _ [], ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hℓ)]
    rw [Finset.sum_eq_zero (fun k hk => ?_), add_zero]
    have := huniq k (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
      (Finset.ne_of_mem_erase hk)
    simp only [hp] at this
    simp only [hfdef, this, Bool.false_eq_true, ite_false]
  set w₀ := T.loops.getD ℓ [] with hw₀
  have hfw : 1 ≤ f w₀ := hkk ▸ hko
  -- a resolvent in the loop at `ℓ`
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, LoopLetter.res b ∈ w₀ := by
    have hc : w₀.contains (.lamt o) = true := hpℓ
    simp only [hfdef, hc, ite_true] at hfw
    obtain ⟨x, hx, hxr⟩ := List.countP_pos_iff.1 hfw
    cases x with
    | res b =>
      refine ⟨b, ?_⟩
      have h1 := (List.takeWhile_sublist _).subset hx
      rw [List.mem_reverse] at h1
      exact List.mem_rotate.1 (List.mem_of_mem_drop h1)
    | _ => simp at hxr
  set r := w₀.idxOf (LoopLetter.res b) with hr
  have hrl : r < w₀.length := List.idxOf_lt_length_of_mem hb
  have hwr : w₀[r] = LoopLetter.res b := List.getElem_idxOf hrl
  -- the search for a resolvent succeeds
  set i := w₀.idxOf (LoopLetter.lamt o) with hi
  set m := w₀.length with hm
  have hm0 : 0 < m := by omega
  set q := (i + m - 1 - r) % m with hq
  have hqm : q < m := Nat.mod_lt _ hm0
  have hqr : (i + m - 1 - q) % m = r := by
    have h1 := Nat.mod_add_div (i + m - 1 - r) m
    have h2 : i + m - 1 - q = m * ((i + m - 1 - r) / m) + r := by omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt hrl]
  -- the focus
  unfold LoopExpr.focus
  dsimp only
  rw [show T.loops[T.loops.findIdx fun w => w.contains (LoopLetter.lamt o)]? = some w₀ by
    rw [hgℓ]; exact List.getElem?_eq_getElem hℓ]
  dsimp only
  split
  · rename_i heq
    exfalso
    have := List.find?_eq_none.1 heq r (List.mem_map.2 ⟨q, List.mem_range.2 hqm, hqr⟩)
    simp [List.getElem?_eq_getElem hrl, hwr] at this
  rename_i r' hr'
  have hr'p := List.find?_some hr'
  have hr'm : r' < m := by
    obtain ⟨j, -, hj⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hr')
    rw [← hj]; exact Nat.mod_lt _ hm0
  obtain ⟨b', hb'⟩ : ∃ b', w₀[r'] = LoopLetter.res b' := by
    rw [List.getElem?_eq_getElem hr'm] at hr'p
    revert hr'p
    cases w₀[r'] with
    | res b' => exact fun _ => ⟨b', rfl⟩
    | _ => simp
  have hrot : w₀.rotate r' = LoopLetter.res b' :: (w₀.drop (r' + 1) ++ w₀.take r') := by
    rw [List.rotate_eq_drop_append_take hr'm.le, List.drop_eq_getElem_cons hr'm, hb']
    rfl
  rw [hrot]
  simp only [Option.isSome_ite]
  exact hko

/-! ### The tree sum -/

/-- Bounds that hold for every `l ≥ l₀(T)` and `N ≥ N₀(T, l)`, for each expression of a list, add
up over the list with common `l₀` and `N₀`. -/
private lemma GS_combine (D : ℕ) (L : List LoopExpr)
    (Bd : LoopExpr → ℕ → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℝ)
    (Hyp : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → Prop)
    (X : (N : ℕ) → LoopEnv D N → ℝ)
    (h : ∀ T ∈ L, ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ μ e, Hyp N μ e →
      Bd T l N μ e ≤ X N e) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ μ e, Hyp N μ e → 0 ≤ X N e →
      (L.map fun T => Bd T l N μ e).sum ≤ L.length * X N e := by
  induction L with
  | nil => exact ⟨0, fun l _ => ⟨0, fun N _ μ e _ hX => by simp⟩⟩
  | cons T L ih =>
    obtain ⟨l₁, h₁⟩ := h T List.mem_cons_self
    obtain ⟨l₂, h₂⟩ := ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    refine ⟨max l₁ l₂, fun l hl => ?_⟩
    obtain ⟨N₁, hN₁⟩ := h₁ l (le_of_max_le_left hl)
    obtain ⟨N₂, hN₂⟩ := h₂ l (le_of_max_le_right hl)
    refine ⟨max N₁ N₂, fun N hN μ e hH hX => ?_⟩
    have a1 := hN₁ N (le_of_max_le_left hN) μ e hH
    have a2 := hN₂ N (le_of_max_le_right hN) μ e hH hX
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

/-- A sum over a list is bounded by the sum of the norms. -/
private lemma GS_norm_list_sum (L : List LoopExpr) (f : LoopExpr → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map fun T => ‖f T‖).sum := by
  induction L with
  | nil => simp
  | cons T L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

/-- One round of the expansion: the expressions of the list minus those of the next round minus the
remainders of the expressions expanded is the sum over the list of the expansions (5.40) of the
expressions that are not stopped. -/
private lemma GS_err_split (ε : ℝ) (E R : LoopExpr → ℂ) :
    ∀ L : List LoopExpr, (L.map E).sum -
        ((L.flatMap fun T => if T.Stopped ε then [T] else T.step).map E).sum -
        ((L.filter fun T => decide (¬ T.Stopped ε)).map R).sum =
      (L.map fun T => if T.Stopped ε then 0 else E T - (T.step.map E).sum - R T).sum
  | [] => by simp
  | T :: L => by
      have ih := GS_err_split ε E R L
      by_cases hT : T.Stopped ε
      · simp only [List.map_cons, List.sum_cons, List.flatMap_cons, hT, ite_true, List.map_append,
          List.sum_append, List.filter_cons, decide_not, decide_true, Bool.not_true,
          Bool.false_eq_true, ite_false, List.map_nil, List.sum_nil, add_zero] at ih ⊢
        linear_combination ih
      · simp only [List.map_cons, List.sum_cons, List.flatMap_cons, hT, ite_false, List.map_append,
          List.sum_append, List.filter_cons, decide_not, decide_false, Bool.not_false,
          ite_true] at ih ⊢
        linear_combination ih

/-- The tree sum for a list of expressions of the class: after `n` rounds, for every
`l ≥ l₀` and `N ≥ N₀(l)`. -/
private lemma GS_tree (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ K ε : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) :
    ∀ n : ℕ, ∀ L : List LoopExpr, (∀ T ∈ L, T.wf = true) → ∀ D' : ℝ, 0 < D' →
      ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
        ‖(L.map fun T => ∫ h, T.evalH e h ∂μ).sum -
            ((loopIter ε n L).map fun T => ∫ h, T.evalH e h ∂μ).sum -
            ((loopInner ε n L).map fun T =>
              ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
                (if 2 ≤ p + q then T.remPQ e μ p q else 0)).sum‖ ≤
          (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro L hL D' hD'
    refine ⟨0, fun l _ => ⟨0, fun N _ μ hμ e _ _ _ _ _ => ?_⟩⟩
    simp only [loopIter, loopInner, sub_self, List.map_nil, List.sum_nil, norm_zero]
    positivity
  | succ n ih =>
    intro L hL D' hD'
    set L' := L.flatMap fun T => if T.Stopped ε then [T] else T.step with hL'def
    have hL' : ∀ T ∈ L', T.wf = true := by
      intro T' hT'
      obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
      by_cases hs : T.Stopped ε
      · simp only [hs, ite_true, List.mem_singleton] at hT'T
        exact hT'T ▸ hL T hT
      · simp only [hs, ite_false] at hT'T
        exact loop_step_wf T (hL T hT) T' hT'T
    obtain ⟨l₁, hl₁⟩ := ih L' hL' (D' + 1) (by linarith)
    set Hyp : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → Prop :=
      fun N μ e => LLClass D N C 1 μ ∧ opNorm e.A ≤ (N : ℝ) ^ (-δA) ∧
        2 * C₀ * opNorm e.A ≤ 1 / 10 ∧ (∀ a, |e.c a| ≤ C₀) ∧
        (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) ∧ |e.δ| ≤ K * avgSq (lam D N e.A) with hHyp
    set Bd : LoopExpr → ℕ → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℝ :=
      fun T l N μ e => ‖if T.Stopped ε then 0 else (∫ h, T.evalH e h ∂μ) -
        (T.step.map fun T' => ∫ h, T'.evalH e h ∂μ).sum -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then T.remPQ e μ p q else 0)‖ with hBd
    set X : (N : ℕ) → LoopEnv D N → ℝ := fun N e => (N : ℝ) ^ (-(D' + 1)) * opNorm e.A ^ 2
      with hX
    have hT : ∀ T ∈ L, ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ μ e, Hyp N μ e →
        Bd T l N μ e ≤ X N e := by
      intro T hTL
      by_cases hs : T.Stopped ε
      · refine ⟨0, fun l _ => ⟨0, fun N _ μ e _ => ?_⟩⟩
        simp only [hBd, hX, hs, ite_true, norm_zero]
        positivity
      · have hk : 1 ≤ T.kk 0 ∨ 1 ≤ T.kk 1 := by
          simp only [LoopExpr.Stopped, not_or, not_and_or] at hs
          omega
        obtain ⟨l₀, -, hl₀⟩ := GS_gauss_all D hD δA τ C₀ K hδA hτ hC₀ C T (hL T hTL)
          (GS_focus_isSome (hL T hTL) hk) (D' + 1) (by linarith)
        refine ⟨l₀, fun l hl => ?_⟩
        obtain ⟨N₀, hN₀⟩ := hl₀ l hl
        refine ⟨N₀, fun N hN μ e ⟨hμ, hA, hA2, hc, hz, hδ⟩ => ?_⟩
        simp only [hBd, hX, hs, ite_false]
        exact hN₀ N hN μ hμ e hA hA2 hc hz hδ
    obtain ⟨l₂, hl₂⟩ := GS_combine D L Bd Hyp X hT
    refine ⟨max l₁ l₂, fun l hl => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hl₁ l (le_of_max_le_left hl)
    obtain ⟨N₂, hN₂⟩ := hl₂ l (le_of_max_le_right hl)
    refine ⟨max (max N₁ N₂) (L.length + 1), fun N hN μ hμ e hA hA2 hc hz hδ => ?_⟩
    have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
    have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
    have hNL : L.length + 1 ≤ N := le_of_max_le_right hN
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hX0 : 0 ≤ X N e := by simp only [hX]; positivity
    have b1 := hN₁ N hN1 μ hμ e hA hA2 hc hz hδ
    have b2 := hN₂ N hN2 μ e ⟨hμ, hA, hA2, hc, hz, hδ⟩ hX0
    set E : LoopExpr → ℂ := fun T => ∫ h, T.evalH e h ∂μ with hE
    set R : LoopExpr → ℂ := fun T => ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 2 ≤ p + q then T.remPQ e μ p q else 0) with hR
    have hsplit := GS_err_split ε E R L
    have e1 : (L.map E).sum - ((loopIter ε (n + 1) L).map E).sum -
        ((loopInner ε (n + 1) L).map R).sum =
        (L.map fun T => if T.Stopped ε then 0 else E T - (T.step.map E).sum - R T).sum +
        ((L'.map E).sum - ((loopIter ε n L').map E).sum - ((loopInner ε n L').map R).sum) := by
      simp only [loopIter, loopInner, List.map_append, List.sum_append]
      rw [← hsplit]
      ring
    rw [e1]
    have b3 : ‖(L.map fun T => if T.Stopped ε then 0 else E T - (T.step.map E).sum - R T).sum‖ ≤
        L.length * X N e := (GS_norm_list_sum L _).trans b2
    have hfin : ((L.length : ℝ) + 1) * X N e ≤ (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
      simp only [hX]
      rw [neg_add, Real.rpow_add hn0, Real.rpow_neg_one]
      have hL1 : ((L.length : ℝ) + 1) ≤ N := by exact_mod_cast hNL
      have h0 : 0 ≤ (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by positivity
      calc ((L.length : ℝ) + 1) * ((N : ℝ) ^ (-D') * (N : ℝ)⁻¹ * opNorm e.A ^ 2)
          = ((L.length : ℝ) + 1) * (N : ℝ)⁻¹ * ((N : ℝ) ^ (-D') * opNorm e.A ^ 2) := by ring
        _ ≤ 1 * ((N : ℝ) ^ (-D') * opNorm e.A ^ 2) := by
            gcongr
            rw [mul_inv_le_iff₀ hn0]; linarith
        _ = _ := one_mul _
    calc _ ≤ ‖(L.map fun T => if T.Stopped ε then 0 else E T - (T.step.map E).sum - R T).sum‖ +
          ‖(L'.map E).sum - ((loopIter ε n L').map E).sum - ((loopInner ε n L').map R).sum‖ :=
          norm_add_le _ _
      _ ≤ L.length * X N e + X N e := add_le_add b3 b1
      _ = ((L.length : ℝ) + 1) * X N e := by ring
      _ ≤ _ := hfin

/-- The tree sum: after `n` rounds, the expectation of the starting loop (5.30)
[starting_point_of_expansion] is the sum of the expectations of the expressions reached, plus the
terms `𝓡_𝒯(p, q)`, `2 ≤ p + q ≤ l`, of the expanded expressions, up to `N^{-D'} ‖A‖²`. -/
theorem loop_tree_sum (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ K ε : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (n : ℕ) :
    ∀ D' : ℝ, 0 < D' → ∃ l : ℕ, 2 ≤ l ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
        ‖(∫ h, loopStart.evalH e h ∂μ) -
            ((loopIter ε n [loopStart]).map fun T => ∫ h, T.evalH e h ∂μ).sum -
            ((loopInner ε n [loopStart]).map fun T =>
              ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
                (if 2 ≤ p + q then T.remPQ e μ p q else 0)).sum‖ ≤
          (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
  intro D' hD'
  obtain ⟨l₀, hl⟩ := GS_tree D hD δA τ C₀ K ε hδA hτ hC₀ C n [loopStart] (by decide) D' hD'
  obtain ⟨N₀, hN₀⟩ := hl (max l₀ 2) (le_max_left _ _)
  refine ⟨max l₀ 2, le_max_right _ _, N₀, fun N hN μ hμ e hA hA2 hc hz hδ => ?_⟩
  simpa using hN₀ N hN μ hμ e hA hA2 hc hz hδ

end RBMTransitionEdge

end
