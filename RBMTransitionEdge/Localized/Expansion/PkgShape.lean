module

public import RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# The packages of the derivative structures of the further expansion

The heavy packages of a word of the class (5.79) [further_expansion_expression_Type_1], and the
shape of the derivative structures of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]
in the proof of Lemma 5.5 [claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The letter is a resolvent `𝒢_a`. -/
def PkgLetter.isRes (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | _ => false

/-- The letter is a matrix `Δ`. -/
def PkgLetter.isEnt (x : PkgLetter) : Bool :=
  match x with | .ent _ _ => true | _ => false

/-- The letter is a `Λ̃`. -/
def PkgLetter.isLam (x : PkgLetter) : Bool :=
  match x with | .lw (.lamt _) => true | _ => false

/-- The heavy packages of (5.79) [further_expansion_expression_Type_1] of a word with a letter `Δ`:
the subwords between consecutive letters `Δ`, cyclically, starting after the first `Δ`; for a word
without `Δ`, the word itself. -/
def pkgSegs (w : List PkgLetter) : List (List PkgLetter) :=
  if w.any PkgLetter.isEnt then
    ((w.rotate (w.findIdx PkgLetter.isEnt + 1)).dropLast).splitOnP PkgLetter.isEnt
  else [w]

/-! ### Auxiliary facts: the segments of a list at its letters `Δ` -/

private theorem isEnt_ent (u v : ℕ) : PkgLetter.isEnt (.ent u v) = true := rfl
private theorem isEnt_lw (x : LoopLetter) : PkgLetter.isEnt (.lw x) = false := rfl
private theorem isRes_res (a : Fin 2) : PkgLetter.isRes (.lw (.res a)) = true := rfl

/-- The pieces of a list cut at its letters `Δ`. -/
private abbrev Seg (l : List PkgLetter) : List (List PkgLetter) := l.splitOnP PkgLetter.isEnt

private theorem seg_cons (Z : List PkgLetter) : ∃ (σ : List PkgLetter) (L : List (List PkgLetter)),
    Seg Z = σ :: L := by
  cases h : Seg Z with
  | nil => exact absurd h (List.splitOnP_ne_nil _ _)
  | cons σ L => exact ⟨σ, L, rfl⟩

/-- The pieces of a concatenation: the last piece of the first list and the first piece of the
second list are glued. -/
private theorem seg_split : ∀ Z₁ : List PkgLetter, ∃ (L₁ : List (List PkgLetter))
    (σ₁ : List PkgLetter), Seg Z₁ = L₁ ++ [σ₁] ∧ ∀ (Z₂ σ₂ : List PkgLetter)
      (L₂ : List (List PkgLetter)), Seg Z₂ = σ₂ :: L₂ →
        Seg (Z₁ ++ Z₂) = L₁ ++ (σ₁ ++ σ₂) :: L₂
  | [] => ⟨[], [], by simp [Seg], fun Z₂ σ₂ L₂ h => by simpa [Seg] using h⟩
  | x :: Z₁ => by
      obtain ⟨L₁, σ₁, h1, hall⟩ := seg_split Z₁
      by_cases hx : PkgLetter.isEnt x = true
      · refine ⟨[] :: L₁, σ₁, ?_, fun Z₂ σ₂ L₂ h => ?_⟩
        · simp only [Seg, List.splitOnP_cons_eq_ite_modifyHead, hx, ↓reduceIte] at h1 ⊢
          rw [h1]; rfl
        · have := hall Z₂ σ₂ L₂ h
          simp only [Seg, List.splitOnP_cons_eq_ite_modifyHead, hx, ↓reduceIte,
            List.cons_append] at this ⊢
          rw [this]
      · have hx' : PkgLetter.isEnt x = false := by simpa using hx
        cases L₁ with
        | nil =>
            refine ⟨[], x :: σ₁, ?_, fun Z₂ σ₂ L₂ h => ?_⟩
            · simp only [Seg, List.splitOnP_cons_eq_ite_modifyHead, hx', Bool.false_eq_true,
                ↓reduceIte, List.nil_append] at h1 ⊢
              rw [h1]; rfl
            · have := hall Z₂ σ₂ L₂ h
              simp only [Seg, List.splitOnP_cons_eq_ite_modifyHead, hx', Bool.false_eq_true,
                ↓reduceIte, List.nil_append, List.cons_append] at this ⊢
              rw [this]; rfl
        | cons h0 t =>
            refine ⟨(x :: h0) :: t, σ₁, ?_, fun Z₂ σ₂ L₂ h => ?_⟩
            · simp only [Seg, List.splitOnP_cons_eq_ite_modifyHead, hx', Bool.false_eq_true,
                ↓reduceIte, List.cons_append] at h1 ⊢
              rw [h1]; rfl
            · have := hall Z₂ σ₂ L₂ h
              simp only [Seg, List.splitOnP_cons_eq_ite_modifyHead, hx', Bool.false_eq_true,
                ↓reduceIte, List.cons_append] at this ⊢
              rw [this]; rfl

/-- The pieces after doubling a resolvent with a `Δ` in between. -/
private theorem seg_ins (Z₁ Z₂ : List PkgLetter) (c : Fin 2) (u v : ℕ) :
    ∃ (L₁ : List (List PkgLetter)) (σ₁ σ₂ : List PkgLetter) (L₂ : List (List PkgLetter)),
      Seg (Z₁ ++ .lw (.res c) :: Z₂) = L₁ ++ (σ₁ ++ .lw (.res c) :: σ₂) :: L₂ ∧
      Seg (Z₁ ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂) =
        L₁ ++ (σ₁ ++ [.lw (.res c)]) :: (.lw (.res c) :: σ₂) :: L₂ := by
  obtain ⟨L₁, σ₁, h1, hall⟩ := seg_split Z₁
  obtain ⟨σ₂, L₂, h2⟩ := seg_cons Z₂
  have hrz : Seg (.lw (.res c) :: Z₂) = (.lw (.res c) :: σ₂) :: L₂ := by
    have h2' : Z₂.splitOnP PkgLetter.isEnt = σ₂ :: L₂ := h2
    rw [Seg, List.splitOnP_cons_eq_ite_modifyHead, h2']
    simp only [isEnt_lw, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hr : Seg [PkgLetter.lw (.res c)] = [[.lw (.res c)]] :=
    List.splitOnP_eq_singleton (by simp [isEnt_lw])
  refine ⟨L₁, σ₁, σ₂, L₂, hall _ _ _ hrz, ?_⟩
  have e : Z₁ ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂ =
      (Z₁ ++ [.lw (.res c)]) ++ .ent u v :: (.lw (.res c) :: Z₂) := by simp
  rw [e]
  refine (List.splitOnP_append_cons _ _ (isEnt_ent u v)).trans ?_
  change Seg _ ++ Seg _ = _
  have h3 := hall [.lw (.res c)] [.lw (.res c)] [] hr
  rw [h3, hrz]
  simp

private theorem free_of_any {l : List PkgLetter} (h : l.any PkgLetter.isEnt = false) :
    ∀ z ∈ l, PkgLetter.isEnt z = false := by
  intro z hz
  by_contra hne
  have : l.any PkgLetter.isEnt = true := List.any_eq_true.2 ⟨z, hz, by simpa using hne⟩
  rw [this] at h
  exact absurd h (by simp)

/-- A list with a letter `Δ` splits at its first one. -/
private theorem PSh_exists_first_ent : ∀ w : List PkgLetter, w.any PkgLetter.isEnt = true →
    ∃ (P : List PkgLetter) (x y : ℕ) (Q : List PkgLetter),
      (∀ z ∈ P, PkgLetter.isEnt z = false) ∧ w = P ++ .ent x y :: Q
  | [], h => by simp at h
  | z :: w, h => by
      match z with
      | .ent x y => exact ⟨[], x, y, w, by simp, rfl⟩
      | .lw z' =>
          have h' : w.any PkgLetter.isEnt = true := by simpa [PkgLetter.isEnt] using h
          obtain ⟨P, x, y, Q, hP, hw⟩ := PSh_exists_first_ent w h'
          refine ⟨.lw z' :: P, x, y, Q, ?_, by simp [hw]⟩
          intro t ht
          rcases List.mem_cons.1 ht with rfl | ht
          · rfl
          · exact hP t ht

private theorem PSh_findIdx_ent (P Q : List PkgLetter) (u v : ℕ)
    (hP : ∀ y ∈ P, PkgLetter.isEnt y = false) :
    (P ++ .ent u v :: Q).findIdx PkgLetter.isEnt = P.length := by
  induction P with
  | nil => simp [List.findIdx_cons, isEnt_ent]
  | cons z P ih =>
      rw [List.cons_append, List.findIdx_cons, hP z (List.mem_cons_self)]
      simp [ih (fun y hy => hP y (List.mem_cons_of_mem _ hy))]

/-- The packages of a word cut at its first letter `Δ`: the pieces of the list read from just
after that `Δ`. -/
private theorem pkgSegs_first (P Q : List PkgLetter) (u v : ℕ)
    (hP : ∀ y ∈ P, PkgLetter.isEnt y = false) :
    pkgSegs (P ++ .ent u v :: Q) = Seg (Q ++ P) := by
  unfold pkgSegs
  have h1 : (P ++ .ent u v :: Q).any PkgLetter.isEnt = true := by simp [PkgLetter.isEnt]
  simp only [h1, ↓reduceIte, PSh_findIdx_ent P Q u v hP]
  have h2 : (P ++ .ent u v :: Q).rotate (P.length + 1) = (Q ++ P) ++ [.ent u v] := by
    rw [List.rotate_eq_drop_append_take (by simp)]
    have e0 : P ++ .ent u v :: Q = (P ++ [.ent u v]) ++ Q := by simp
    have e1 : (P ++ .ent u v :: Q).drop (P.length + 1) = Q := by
      rw [e0]; exact List.drop_left' (by simp)
    have e2 : (P ++ .ent u v :: Q).take (P.length + 1) = P ++ [.ent u v] := by
      rw [e0]; exact List.take_left' (by simp)
    rw [e1, e2]; simp
  rw [h2, List.dropLast_concat]

private theorem PSh_ent_split (A B P Q : List PkgLetter) (u v x y : ℕ)
    (hP : ∀ z ∈ P, PkgLetter.isEnt z = false) (h : A ++ .ent u v :: B = P ++ .ent x y :: Q) :
    (A = P ∧ B = Q) ∨ ∃ A', A = P ++ .ent x y :: A' ∧ Q = A' ++ .ent u v :: B := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · cases as with
    | nil =>
        simp only [List.nil_append, List.append_nil] at h1 h2
        exact Or.inl ⟨h1.symm, (List.cons.inj h2).2⟩
    | cons z as' =>
        have hz : z = .ent u v := (List.cons.inj h2).1.symm
        have := hP z (by rw [h1]; simp)
        rw [hz] at this
        simp [isEnt_ent] at this
  · cases bs with
    | nil =>
        simp only [List.nil_append, List.append_nil] at h1 h2
        exact Or.inl ⟨h1, (List.cons.inj h2).2.symm⟩
    | cons z bs' =>
        have hz : z = .ent x y := (List.cons.inj h2).1.symm
        subst hz
        exact Or.inr ⟨bs', h1, (List.cons.inj h2).2⟩

/-- The packages of a word with a `Δ` at a given place: up to order, the pieces of the list read
from just after that `Δ`. -/
private theorem pkgSegs_perm (A B : List PkgLetter) (u v : ℕ) :
    (pkgSegs (A ++ .ent u v :: B)).Perm (Seg (B ++ A)) := by
  obtain ⟨P, x, y, Q, hP, hw⟩ := PSh_exists_first_ent (A ++ .ent u v :: B) (by simp [PkgLetter.isEnt])
  rw [hw, pkgSegs_first P Q x y hP]
  rcases PSh_ent_split A B P Q u v x y hP hw with ⟨rfl, rfl⟩ | ⟨A', rfl, rfl⟩
  · exact List.Perm.refl _
  · have e1 : (A' ++ .ent u v :: B) ++ P = A' ++ .ent u v :: (B ++ P) := by simp
    have e2 : B ++ (P ++ .ent x y :: A') = (B ++ P) ++ .ent x y :: A' := by simp
    rw [e1, e2]
    change (Seg (A' ++ .ent u v :: (B ++ P))).Perm (Seg ((B ++ P) ++ .ent x y :: A'))
    unfold Seg
    rw [List.splitOnP_append_cons _ _ (isEnt_ent u v),
      List.splitOnP_append_cons _ _ (isEnt_ent x y)]
    exact List.perm_append_comm

/-- Doubling a resolvent of a word with a letter `Δ`, with a `Δ` in between: the packages of the
two words, up to order. -/
private theorem pkgSegs_ins (Z₁ Z₂ : List PkgLetter) (c : Fin 2) (u v : ℕ)
    (h : (Z₁ ++ .lw (.res c) :: Z₂).any PkgLetter.isEnt = true) :
    ∃ (L₁ : List (List PkgLetter)) (σ₁ σ₂ : List PkgLetter) (L₂ : List (List PkgLetter)),
      (pkgSegs (Z₁ ++ .lw (.res c) :: Z₂)).Perm (L₁ ++ (σ₁ ++ .lw (.res c) :: σ₂) :: L₂) ∧
      (pkgSegs (Z₁ ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂)).Perm
        (L₁ ++ (σ₁ ++ [.lw (.res c)]) :: (.lw (.res c) :: σ₂) :: L₂) := by
  by_cases h1 : Z₁.any PkgLetter.isEnt = true
  · obtain ⟨P, x, y, Q, -, hZ⟩ := PSh_exists_first_ent Z₁ h1
    obtain ⟨L₁, σ₁, σ₂, L₂, g1, g2⟩ := seg_ins Q (Z₂ ++ P) c u v
    refine ⟨L₁, σ₁, σ₂, L₂, ?_, ?_⟩
    · have e : Z₁ ++ .lw (.res c) :: Z₂ = P ++ .ent x y :: (Q ++ .lw (.res c) :: Z₂) := by
        simp [hZ]
      have e2 : (Q ++ PkgLetter.lw (.res c) :: Z₂) ++ P = Q ++ .lw (.res c) :: (Z₂ ++ P) := by
        simp
      rw [e]
      refine (pkgSegs_perm _ _ x y).trans ?_
      rw [e2, g1]
    · have e : Z₁ ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂ =
          P ++ .ent x y :: (Q ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂) := by
        simp [hZ]
      have e2 : (Q ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂) ++ P =
          Q ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ (Z₂ ++ P) := by simp
      rw [e]
      refine (pkgSegs_perm _ _ x y).trans ?_
      rw [e2, g2]
  · have h2 : Z₂.any PkgLetter.isEnt = true := by
      simp only [Bool.not_eq_true] at h1
      simpa [h1, List.any_append, PkgLetter.isEnt] using h
    obtain ⟨P, x, y, Q, -, hZ⟩ := PSh_exists_first_ent Z₂ h2
    obtain ⟨L₁, σ₁, σ₂, L₂, g1, g2⟩ := seg_ins (Q ++ Z₁) P c u v
    refine ⟨L₁, σ₁, σ₂, L₂, ?_, ?_⟩
    · have e : Z₁ ++ .lw (.res c) :: Z₂ = (Z₁ ++ .lw (.res c) :: P) ++ .ent x y :: Q := by
        simp [hZ]
      have e2 : Q ++ (Z₁ ++ PkgLetter.lw (.res c) :: P) = (Q ++ Z₁) ++ .lw (.res c) :: P := by
        simp
      rw [e]
      refine (pkgSegs_perm _ _ x y).trans ?_
      rw [e2, g1]
    · have e : Z₁ ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂ =
          (Z₁ ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ P) ++ .ent x y :: Q := by
        simp [hZ]
      have e2 : Q ++ (Z₁ ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ P) =
          (Q ++ Z₁) ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ P := by simp
      rw [e]
      refine (pkgSegs_perm _ _ x y).trans ?_
      rw [e2, g2]

/-- Doubling a resolvent of a word without `Δ`, with a `Δ` in between, gives one package. -/
private theorem pkgSegs_ins_free (Z₁ Z₂ : List PkgLetter) (c : Fin 2) (u v : ℕ)
    (h : (Z₁ ++ .lw (.res c) :: Z₂).any PkgLetter.isEnt = false) :
    (pkgSegs (Z₁ ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂)).Perm
      [.lw (.res c) :: (Z₂ ++ Z₁ ++ [.lw (.res c)])] := by
  have e : Z₁ ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂ =
      (Z₁ ++ [.lw (.res c)]) ++ .ent u v :: (.lw (.res c) :: Z₂) := by simp
  rw [e]
  refine (pkgSegs_perm _ _ u v).trans ?_
  have hf := free_of_any h
  have : Seg (.lw (.res c) :: Z₂ ++ (Z₁ ++ [.lw (.res c)])) =
      [.lw (.res c) :: Z₂ ++ (Z₁ ++ [.lw (.res c)])] := by
    refine List.splitOnP_eq_singleton ?_
    intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (rfl | hz) | hz | rfl
    · rfl
    · exact hf z (by simp [hz])
    · exact hf z (by simp [hz])
    · rfl
  rw [this]
  simp

/-! ### Auxiliary facts: the count of packages without a leading resolvent -/

/-- The number of packages of a word not starting with a resolvent; `0` for a word without `Δ`
(the summand of `pkg_dwirt_shape`). -/
private def Nw (w : List PkgLetter) : ℕ :=
  if w.any PkgLetter.isEnt then
    (pkgSegs w).countP fun σ => σ.head?.map PkgLetter.isRes != some true
  else 0

/-- The package ends with a resolvent. -/
private def LastRes (σ : List PkgLetter) : Prop := σ.getLast?.map PkgLetter.isRes = some true

private theorem lastRes_snoc (σ : List PkgLetter) (c : Fin 2) :
    LastRes (σ ++ [.lw (.res c)]) := by
  simp [LastRes, isRes_res]

private theorem lastRes_cons (σ₁ σ₂ : List PkgLetter) (c : Fin 2)
    (h : LastRes (σ₁ ++ .lw (.res c) :: σ₂)) : LastRes (.lw (.res c) :: σ₂) := by
  rcases List.eq_nil_or_concat σ₂ with rfl | ⟨l', b, rfl⟩
  · simp [LastRes, isRes_res]
  · simpa [LastRes, List.concat_eq_append] using h

private theorem any_ins (Z₁ Z₂ : List PkgLetter) (c : Fin 2) (u v : ℕ) :
    (Z₁ ++ [PkgLetter.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂).any PkgLetter.isEnt = true := by
  simp [List.any_append, PkgLetter.isEnt]

private theorem Nw_ins (Z₁ Z₂ : List PkgLetter) (c : Fin 2) (u v : ℕ) :
    Nw (Z₁ ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂) = Nw (Z₁ ++ .lw (.res c) :: Z₂) := by
  by_cases h : (Z₁ ++ PkgLetter.lw (.res c) :: Z₂).any PkgLetter.isEnt = true
  · obtain ⟨L₁, σ₁, σ₂, L₂, p1, p2⟩ := pkgSegs_ins Z₁ Z₂ c u v h
    unfold Nw
    simp only [h, any_ins Z₁ Z₂ c u v, ↓reduceIte]
    rw [List.Perm.countP_eq _ p1, List.Perm.countP_eq _ p2]
    rcases σ₁ with _ | ⟨x, σ₁⟩ <;> simp [List.countP_append, List.countP_cons, isRes_res]
  · have h' : (Z₁ ++ PkgLetter.lw (.res c) :: Z₂).any PkgLetter.isEnt = false := by simpa using h
    unfold Nw
    simp only [any_ins Z₁ Z₂ c u v, h, ↓reduceIte]
    rw [List.Perm.countP_eq _ (pkgSegs_ins_free Z₁ Z₂ c u v h')]
    simp [isRes_res]

private theorem last_ins (Z₁ Z₂ : List PkgLetter) (c : Fin 2) (u v : ℕ)
    (hold : (Z₁ ++ PkgLetter.lw (.res c) :: Z₂).any PkgLetter.isEnt = true →
      ∀ σ ∈ pkgSegs (Z₁ ++ PkgLetter.lw (.res c) :: Z₂), LastRes σ) :
    ∀ σ ∈ pkgSegs (Z₁ ++ [.lw (.res c), .ent u v, .lw (.res c)] ++ Z₂), LastRes σ := by
  intro σ hσ
  by_cases h : (Z₁ ++ PkgLetter.lw (.res c) :: Z₂).any PkgLetter.isEnt = true
  · obtain ⟨L₁, σ₁, σ₂, L₂, p1, p2⟩ := pkgSegs_ins Z₁ Z₂ c u v h
    have ho := hold h
    rw [p2.mem_iff] at hσ
    simp only [List.mem_append, List.mem_cons] at hσ
    rcases hσ with hσ | rfl | rfl | hσ
    · exact ho σ (p1.symm.mem_iff.1 (by simp [hσ]))
    · exact lastRes_snoc _ c
    · exact lastRes_cons σ₁ σ₂ c (ho _ (p1.symm.mem_iff.1 (by simp)))
    · exact ho σ (p1.symm.mem_iff.1 (by simp [hσ]))
  · have h' : (Z₁ ++ PkgLetter.lw (.res c) :: Z₂).any PkgLetter.isEnt = false := by simpa using h
    rw [(pkgSegs_ins_free Z₁ Z₂ c u v h').mem_iff] at hσ
    rw [List.mem_singleton] at hσ
    subst hσ
    have : PkgLetter.lw (.res c) :: (Z₂ ++ Z₁ ++ [.lw (.res c)]) =
        (PkgLetter.lw (.res c) :: (Z₂ ++ Z₁)) ++ [.lw (.res c)] := by simp
    rw [this]
    exact lastRes_snoc _ c

/-- The word of the new loop of a derivative hitting a light weight. -/
private theorem Nw_weight (b : Fin 2) (y u v : ℕ) :
    Nw [.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] = 0 := by
  have h1 : ([PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] : List PkgLetter).any
      PkgLetter.isEnt = true := by simp [PkgLetter.isEnt]
  have h2 : Seg ([.lw (.res b), .lw (.proj y)] ++ [.lw (.res b)]) =
      [[.lw (.res b), .lw (.proj y), .lw (.res b)]] := by
    refine List.splitOnP_eq_singleton ?_
    intro z hz
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> rfl
  have h3 := pkgSegs_perm [.lw (.res b)] [.lw (.res b), .lw (.proj y)] u v
  rw [h2] at h3
  unfold Nw
  simp only [h1, ↓reduceIte]
  have e : ([PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] : List PkgLetter) =
      [.lw (.res b)] ++ .ent u v :: [.lw (.res b), .lw (.proj y)] := rfl
  rw [e, List.Perm.countP_eq _ h3]
  simp [isRes_res]

private theorem last_weight (b : Fin 2) (y u v : ℕ) :
    ∀ σ ∈ pkgSegs [.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)], LastRes σ := by
  intro σ hσ
  have h2 : Seg ([.lw (.res b), .lw (.proj y)] ++ [.lw (.res b)]) =
      [[.lw (.res b), .lw (.proj y), .lw (.res b)]] := by
    refine List.splitOnP_eq_singleton ?_
    intro z hz
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> rfl
  have h3 := pkgSegs_perm [.lw (.res b)] [.lw (.res b), .lw (.proj y)] u v
  rw [h2] at h3
  have e : ([PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] : List PkgLetter) =
      [.lw (.res b)] ++ .ent u v :: [.lw (.res b), .lw (.proj y)] := rfl
  rw [e, h3.mem_iff, List.mem_singleton] at hσ
  subst hσ
  exact lastRes_snoc [.lw (.res b), .lw (.proj y)] b

/-! ### Auxiliary facts: one derivative -/

/-- Replacing the entry `w` at position `i` of a list changes a sum of values by the difference of
the values. -/
private theorem sum_map_set {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (i : ℕ) (w x : α), l[i]? = some w →
      ((l.set i x).map f).sum + f w = (l.map f).sum + f x
  | [], i, w, x, h => by simp at h
  | y :: l, 0, w, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
  | y :: l, i + 1, w, x, h => by
      have := sum_map_set f l i w x (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- A list splits at the position of one of its entries. -/
private theorem split_at {α : Type*} (w : List α) (r : ℕ) (x : α) (h : w[r]? = some x) :
    w = w.take r ++ x :: w.drop (r + 1) := by
  obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem_cons_drop hr, List.take_append_drop]

/-- The terms of one derivative `PkgExpr.dent`: a resolvent of a loop is doubled with a `Δ` in
between, or a light weight becomes a new loop. -/
private theorem dent_cases (R R' : PkgExpr) (u v : ℕ) (h : R' ∈ R.dent u v) :
    (∃ (ℓ : ℕ) (X Y : List PkgLetter) (a : Fin 2), R.loops[ℓ]? = some (X ++ .lw (.res a) :: Y) ∧
      R'.loops = R.loops.set ℓ (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y)) ∨
    ∃ (b : Fin 2) (y : ℕ),
      R'.loops = R.loops ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]] := by
  unfold PkgExpr.dent at h
  rcases List.mem_append.1 h with h | h
  · left
    obtain ⟨ℓ, -, h⟩ := List.mem_flatMap.1 h
    rcases hℓ : R.loops[ℓ]? with _ | w
    · simp [hℓ] at h
    · simp only [hℓ] at h
      obtain ⟨r, -, h⟩ := List.mem_filterMap.1 h
      split at h
      · rename_i a hr
        simp only [Option.some.injEq] at h
        have hw := split_at w r _ hr
        refine ⟨ℓ, w.take r, w.drop (r + 1), a, by rw [← hw]; exact hℓ, ?_⟩
        rw [← h]
      · simp at h
  · right
    obtain ⟨j, -, h⟩ := List.mem_filterMap.1 h
    split at h
    · rename_i b y hj
      simp only [Option.some.injEq] at h
      exact ⟨b, y, by rw [← h]⟩
    · simp at h

/-- A word with a resolvent after a prefix `H` without resolvents. -/
private theorem res_split (H X Y Z : List PkgLetter) (c : Fin 2)
    (hH : ∀ z ∈ H, PkgLetter.isRes z = false) (h : X ++ .lw (.res c) :: Y = H ++ Z) :
    ∃ X', X = H ++ X' ∧ Z = X' ++ .lw (.res c) :: Y := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · cases as with
    | nil =>
        simp only [List.nil_append, List.append_nil] at h1 h2
        exact ⟨[], by simpa using h1.symm, by simpa using h2.symm⟩
    | cons z as' =>
        have hz : z = .lw (.res c) := (List.cons.inj h2).1.symm
        have := hH z (by rw [h1]; simp)
        rw [hz, isRes_res] at this
        exact absurd this (by simp)
  · exact ⟨bs, h1, h2⟩

/-- A word ending in a letter that is not a resolvent, with a resolvent. -/
private theorem snoc_split (X Y Z : List PkgLetter) (c : Fin 2) (e : PkgLetter)
    (he : PkgLetter.isRes e = false) (h : X ++ .lw (.res c) :: Y = Z ++ [e]) :
    ∃ Y', Y = Y' ++ [e] ∧ Z = X ++ .lw (.res c) :: Y' := by
  rcases List.eq_nil_or_concat Y with rfl | ⟨Y', b, rfl⟩
  · have h' : (X ++ [PkgLetter.lw (.res c)]) = Z ++ [e] := by simpa using h
    have := (List.append_inj' h' (by simp)).2
    have hh : PkgLetter.lw (.res c) = e := by simpa using this
    rw [← hh, isRes_res] at he
    exact absurd he (by simp)
  · have h' : (X ++ .lw (.res c) :: Y') ++ [b] = Z ++ [e] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' (by simp)
    exact ⟨Y', by rw [List.concat_eq_append, show b = e by simpa using h2], h1.symm⟩

/-! ### Auxiliary facts: the invariants along the derivatives -/

/-- The invariants of the loops `L` of a derivative structure with `c` letters `Δ`: the number of
letters `Δ`; the main word `H ⋯ Δ_{10}` with the prefix `H` of `𝔐_a`, the letters before `Λ̃_o`
and `Λ̃_o`; one package without a leading resolvent; every package ends with a resolvent; the loops
of `T` without a resolvent. -/
private structure ShapeInv (H : List PkgLetter) (c : ℕ) (T : LoopExpr)
    (L : List (List PkgLetter)) : Prop where
  cnt : (L.map fun w => w.countP PkgLetter.isEnt).sum = c
  main : ∃ (Q : List PkgLetter) (rest : List (List PkgLetter)),
    L = (H ++ Q ++ [.ent 1 0]) :: rest
  one : (L.map Nw).sum = 1
  last : ∀ w ∈ L, w.any PkgLetter.isEnt = true → ∀ σ ∈ pkgSegs w, LastRes σ
  keep : ∀ w ∈ T.loops, (w.any fun x => match x with | .res _ => true | _ => false) = false →
    w.map PkgLetter.lw ∈ L

private theorem countP_ins (X Y : List PkgLetter) (a : Fin 2) (u v : ℕ) :
    (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).countP PkgLetter.isEnt =
      (X ++ PkgLetter.lw (.res a) :: Y).countP PkgLetter.isEnt + 1 := by
  simp [List.countP_append, List.countP_cons, PkgLetter.isEnt]
  omega

private theorem ShapeInv.step {H : List PkgLetter} (hH : ∀ z ∈ H, PkgLetter.isRes z = false)
    {c : ℕ} {T : LoopExpr} {R R' : PkgExpr} (u v : ℕ) (hI : ShapeInv H c T R.loops)
    (h : R' ∈ R.dent u v) : ShapeInv H (c + 1) T R'.loops := by
  rcases dent_cases R R' u v h with ⟨ℓ, X, Y, a, hℓ, hl⟩ | ⟨b, y, hl⟩
  · have hmem : X ++ PkgLetter.lw (.res a) :: Y ∈ R.loops := List.mem_of_getElem? hℓ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := sum_map_set (fun w => w.countP PkgLetter.isEnt) R.loops ℓ _
        (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
      have h2 := hI.cnt
      have h3 := countP_ins X Y a u v
      rw [hl]
      omega
    · obtain ⟨Q, rest, hL⟩ := hI.main
      rw [hl]
      cases ℓ with
      | zero =>
          rw [hL] at hℓ
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hℓ
          obtain ⟨Y', hY, hQ⟩ := snoc_split X Y (H ++ Q) a (.ent 1 0) rfl hℓ.symm
          obtain ⟨X', hX, hQ'⟩ := res_split H X Y' Q a hH hQ.symm
          refine ⟨X' ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y', rest, ?_⟩
          rw [hL, List.set_cons_zero, hX, hY]
          simp
      | succ k =>
          rw [hL]
          exact ⟨Q, rest.set k (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y), by
            rw [List.set_cons_succ]⟩
    · have := sum_map_set Nw R.loops ℓ _ (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
      have h2 := hI.one
      have h3 := Nw_ins X Y a u v
      rw [hl]
      omega
    · intro w hw
      rw [hl] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | rfl
      · exact hI.last w hw
      · exact fun _ => last_ins X Y a u v (fun hh => hI.last _ hmem hh)
    · intro w hw hres
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 (hI.keep w hw hres)
      refine List.mem_iff_getElem?.2 ⟨m, ?_⟩
      rw [hl, List.getElem?_set]
      by_cases hmℓ : ℓ = m
      · subst hmℓ
        rw [hℓ] at hm
        have hm' : w.map PkgLetter.lw = X ++ PkgLetter.lw (.res a) :: Y := Option.some.inj hm.symm
        have : PkgLetter.lw (LoopLetter.res a) ∈ w.map PkgLetter.lw := by rw [hm']; simp
        obtain ⟨x, hx, hxe⟩ := List.mem_map.1 this
        have hx' : x = LoopLetter.res a := PkgLetter.lw.inj hxe
        subst hx'
        have : (w.any fun x => match x with | .res _ => true | _ => false) = true :=
          List.any_eq_true.2 ⟨_, hx, rfl⟩
        rw [this] at hres
        exact absurd hres (by simp)
      · simpa [hmℓ] using hm
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := hI.cnt
      rw [hl, List.map_append, List.sum_append]
      simp [List.countP_cons, PkgLetter.isEnt, this]
    · obtain ⟨Q, rest, hL⟩ := hI.main
      exact ⟨Q, rest ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]], by
        rw [hl, hL]; rfl⟩
    · have := hI.one
      rw [hl, List.map_append, List.sum_append, this, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nw_weight]
      rfl
    · intro w hw hany σ hσ
      rw [hl, List.mem_append] at hw
      rcases hw with hw | hw
      · exact hI.last w hw hany σ hσ
      · rw [List.mem_singleton] at hw
        subst hw
        exact last_weight b y u v σ hσ
    · intro w hw hres
      rw [hl]
      exact List.mem_append_left _ (hI.keep w hw hres)

/-! ### Auxiliary facts: the focus of a word -/

/-- The letter of a loop word is a resolvent. -/
private def isResL (x : LoopLetter) : Bool :=
  match x with | .res _ => true | _ => false

/-- The entry at position `m` of the loop word `w` is a resolvent. -/
private def ResAt (w : List LoopLetter) (m : ℕ) : Bool :=
  match w[m]? with | some (.res _) => true | _ => false

private theorem idx_mod (i n j m : ℕ) (hj : j < n) (hm : m < n)
    (h : (m = i - 1 - j ∧ j < i) ∨ (m = n + i - 1 - j ∧ i ≤ j)) : (i + n - 1 - j) % n = m := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have : i + n - 1 - j = (i - 1 - j) + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private theorem mod_val (i n j : ℕ) (hi : i < n) (hj : j < n) :
    (i + n - 1 - j) % n = if j < i then i - 1 - j else n + i - 1 - j := by
  split_ifs with h
  · exact idx_mod i n j _ hj (by omega) (Or.inl ⟨rfl, h⟩)
  · exact idx_mod i n j _ hj (by omega) (Or.inr ⟨rfl, by omega⟩)

/-- The first resolvent to the left of the entry `x` of a loop word `w` (cyclically), put in front
by the rotation: the letters between this resolvent and `x` are not resolvents. -/
private theorem rotate_left_res (w : List LoopLetter) (x : LoopLetter) (hx : x ∈ w)
    (hxr : isResL x = false) (a : Fin 2) (tl : List LoopLetter) (r : ℕ)
    (hr : (((List.range w.length).map fun j => (w.idxOf x + w.length - 1 - j) % w.length).find?
      (ResAt w)) = some r)
    (hrot : w.rotate r = .res a :: tl) :
    ∃ tl₀ tl₁ : List LoopLetter, tl = tl₀ ++ x :: tl₁ ∧ ∀ z ∈ tl₀, isResL z = false := by
  set n := w.length with hn
  set i := w.idxOf x with hi_def
  have hi : i < n := List.idxOf_lt_length_iff.2 hx
  have hwi : w[i] = x := List.getElem_idxOf hi
  have hwi' : w[i]? = some x := by rw [List.getElem?_eq_getElem hi, hwi]
  rw [List.find?_eq_some_iff_getElem] at hr
  obtain ⟨hpr, k, hk, hkr, hbef⟩ := hr
  simp only [List.length_map, List.length_range] at hk
  simp only [List.getElem_map, List.getElem_range] at hkr hbef
  have hrn : r < n := by
    rw [← hkr]; exact Nat.mod_lt _ (by omega)
  have hwr : ∃ a'', w[r]? = some (.res a'') := by
    unfold ResAt at hpr
    split at hpr
    · rename_i a'' h; exact ⟨a'', h⟩
    · simp at hpr
  obtain ⟨a'', hwr⟩ := hwr
  have hwr' : w[r] = .res a'' := by
    rw [List.getElem?_eq_getElem hrn] at hwr; exact Option.some.inj hwr
  have hnr : ∀ m (hm : m < n), (∃ j, j < k ∧ (i + n - 1 - j) % n = m) → isResL w[m] = false := by
    rintro m hm ⟨j, hj, hjm⟩
    have := hbef j hj
    rw [hjm] at this
    unfold ResAt at this
    rw [List.getElem?_eq_getElem hm] at this
    revert this
    cases hh : w[m] <;> simp [isResL]
  have hdrop : w.drop r = .res a'' :: w.drop (r + 1) := by
    rw [List.drop_eq_getElem_cons hrn, hwr']
  have htl : tl = w.drop (r + 1) ++ w.take r := by
    rw [List.rotate_eq_drop_append_take (by omega), hdrop] at hrot
    simpa using (List.cons.inj hrot).2.symm
  have hdi : w.drop i = x :: w.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hwi]
  have hrv := mod_val i n k hi hk
  rw [hkr] at hrv
  by_cases hki : k < i
  · -- the resolvent is to the left of `x` in the word
    simp only [hki, ↓reduceIte] at hrv
    refine ⟨(w.drop (r + 1)).take (i - r - 1), w.drop (i + 1) ++ w.take r, ?_, ?_⟩
    · rw [htl]
      have e1 : w.drop (r + 1) = (w.drop (r + 1)).take (i - r - 1) ++ x :: w.drop (i + 1) := by
        conv_lhs => rw [← List.take_append_drop (i - r - 1) (w.drop (r + 1))]
        rw [List.drop_drop, show r + 1 + (i - r - 1) = i by omega, hdi]
      conv_lhs => rw [e1]
      simp
    · intro z hz
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
      simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop] at hm ⊢
      refine hnr _ (by omega) ⟨k - 1 - m, by omega, ?_⟩
      exact idx_mod i n _ _ (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
  · -- the resolvent is to the right of `x`: the cycle passes through the end of the word
    simp only [hki, ↓reduceIte] at hrv
    have hri : i < r := by
      rcases Nat.lt_or_ge i r with h | h
      · exact h
      · exfalso
        have : r = i := by omega
        rw [this, hwi'] at hwr
        have hxx : x = .res a'' := Option.some.inj hwr
        rw [hxx] at hxr
        exact absurd hxr (by simp [isResL])
    refine ⟨w.drop (r + 1) ++ w.take i, (w.drop (i + 1)).take (r - i - 1), ?_, ?_⟩
    · rw [htl]
      have e1 : w.take r = w.take i ++ x :: (w.drop (i + 1)).take (r - i - 1) := by
        have h1 : r = i + (r - i - 1 + 1) := by omega
        conv_lhs => rw [h1, List.take_add, hdi, List.take_succ_cons]
      conv_lhs => rw [e1]
      simp
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
        simp only [List.length_drop, List.getElem_drop] at hm ⊢
        refine hnr _ (by omega) ⟨k - 1 - m, by omega, ?_⟩
        exact idx_mod i n _ _ (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩)
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hz
        simp only [List.length_take, List.getElem_take] at hm ⊢
        refine hnr _ (by omega) ⟨i - 1 - m, by omega, ?_⟩
        exact idx_mod i n _ _ (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)

private theorem count_lamt_one {T : LoopExpr} (hT : T.wf = true) (o : Fin 2)
    {w : List LoopLetter} (hw : w ∈ T.loops) (hc : w.contains (.lamt o) = true) :
    w.count (.lamt o) = 1 := by
  unfold LoopExpr.wf at hT
  simp only [Bool.and_eq_true, beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := hT
  have hs : (T.loops.map fun w => w.count (.lamt o)).sum = 1 := by
    fin_cases o
    · exact h0
    · exact h1
  have hle : w.count (.lamt o) ≤ 1 := hs ▸ List.le_sum_of_mem (List.mem_map_of_mem hw)
  have hpos : 0 < w.count (.lamt o) := List.count_pos_iff.2 (List.contains_iff_mem.1 hc)
  omega

/-- The focus of `T` (5.38) [explicit_cT]: the loop `w` is a rotation of `𝒢_a · tl`, and
`tl = tl₀ Λ̃_o tl₁` with no resolvent in `tl₀` (`Λ̃_o` occurs once). -/
private theorem focus_shape {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (h : T.focus = some (ℓ, a, tl)) :
    ∃ (w tl₀ tl₁ : List LoopLetter), T.loops[ℓ]? = some w ∧ w.Perm (.res a :: tl) ∧
      tl = tl₀ ++ .lamt (if 1 ≤ T.kk 0 then 0 else 1) :: tl₁ ∧
      (∀ x ∈ tl₀, isResL x = false) ∧ .lamt (if 1 ≤ T.kk 0 then 0 else 1) ∉ tl₀ := by
  unfold LoopExpr.focus at h
  dsimp only at h
  generalize (if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = o at h ⊢
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
          have hwm : w ∈ T.loops := List.mem_of_getElem? hw
          have hc : w.contains (.lamt o) = true := by
            obtain ⟨hlt, hwe⟩ := List.getElem?_eq_some_iff.1 hw
            have := List.findIdx_getElem (p := fun w : List LoopLetter => w.contains (.lamt o))
              (xs := T.loops) (w := hlt)
            rwa [hwe] at this
          have hx : LoopLetter.lamt o ∈ w := List.contains_iff_mem.1 hc
          have hperm : w.Perm (.res a' :: tl') := by
            rw [← hrot]; exact (List.rotate_perm w r).symm
          obtain ⟨tl₀, tl₁, he, hfree⟩ := rotate_left_res w (.lamt o) hx rfl a' tl' r hr hrot
          refine ⟨w, tl₀, tl₁, hw, hperm, he, hfree, ?_⟩
          have h1 := count_lamt_one hT o hwm hc
          have h2 := hperm.count_eq (.lamt o)
          rw [h1] at h2
          have h3 : (LoopLetter.res a' :: tl').count (.lamt o) = tl'.count (.lamt o) := by
            simp
          rw [h3, he, List.count_append, List.count_cons] at h2
          simp only [beq_self_eq_true, ↓reduceIte] at h2
          exact List.count_eq_zero.1 (by omega)
        · cases h
      · cases h

/-! ### Auxiliary facts: the start `pkgStart` -/

private theorem any_lw (l : List LoopLetter) :
    (l.map PkgLetter.lw).any PkgLetter.isEnt = false := by
  rw [Bool.eq_false_iff, Ne, List.any_eq_true]
  rintro ⟨x, hx, hxe⟩
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  exact absurd hxe (by simp [isEnt_lw])

private theorem countP_lw (l : List LoopLetter) :
    (l.map PkgLetter.lw).countP PkgLetter.isEnt = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  simp [isEnt_lw]

private theorem Nw_lw (l : List LoopLetter) : Nw (l.map PkgLetter.lw) = 0 := by
  unfold Nw
  rw [any_lw]
  rfl

private theorem sum_lw (Ls : List (List LoopLetter)) (f : List PkgLetter → ℕ)
    (hf : ∀ l : List LoopLetter, f (l.map PkgLetter.lw) = 0) :
    ((Ls.map fun w => w.map PkgLetter.lw).map f).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
  exact hf w

private theorem ShapeInv.start {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl tl₀ tl₁ w : List LoopLetter}
    {o : Fin 2} (hf : T.focus = some (ℓ, a, tl)) (hw : T.loops[ℓ]? = some w)
    (hperm : w.Perm (.res a :: tl)) (he : tl = tl₀ ++ .lamt o :: tl₁) :
    ShapeInv ((LoopLetter.det a :: tl₀).map PkgLetter.lw ++ [.lw (.lamt o)]) 1 T
      T.pkgStart.loops := by
  have hs : T.pkgStart.loops = (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map
      PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
        (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw := by
    unfold LoopExpr.pkgStart
    rw [hf]
  have hA : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw =
      ((LoopLetter.det a :: tl₀).map PkgLetter.lw ++ [.lw (.lamt o)]) ++
        (tl₁ ++ [LoopLetter.res a]).map PkgLetter.lw := by
    rw [he]; simp
  have hseg : pkgSegs (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0]) |>.Perm [(LoopLetter.det a :: tl ++ [LoopLetter.res a]).map
        PkgLetter.lw] := by
    have := pkgSegs_perm ((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) [] 1 0
    have e : Seg ([] ++ (LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) =
        [(LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw] :=
      List.splitOnP_eq_singleton (by
        intro z hz
        rw [List.nil_append] at hz
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hz
        exact isEnt_lw y)
    rw [e] at this
    simpa using this
  have hany : (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0]).any PkgLetter.isEnt = true := by
    simp [List.any_append, PkgLetter.isEnt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, List.map_cons, List.sum_cons, sum_lw _ _ countP_lw]
    simp [List.countP_append, PkgLetter.isEnt]
  · refine ⟨(tl₁ ++ [LoopLetter.res a]).map PkgLetter.lw,
      (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw, ?_⟩
    rw [hs, hA]
  · rw [hs, List.map_cons, List.sum_cons, sum_lw _ _ Nw_lw]
    unfold Nw
    simp only [hany, ↓reduceIte]
    rw [List.Perm.countP_eq _ hseg]
    simp [PkgLetter.isRes]
  · intro w' hw' hany' σ hσ
    rw [hs, List.mem_cons] at hw'
    rcases hw' with rfl | hw'
    · rw [hseg.mem_iff, List.mem_singleton] at hσ
      subst hσ
      have : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw =
          (LoopLetter.det a :: tl).map PkgLetter.lw ++ [.lw (.res a)] := by simp
      rw [this]
      exact lastRes_snoc _ a
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hw'
      rw [any_lw] at hany'
      exact absurd hany' (by simp)
  · intro w' hw' hres
    rw [hs]
    refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨w', ?_, rfl⟩)
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hw'
    refine List.mem_eraseIdx_iff_getElem?.2 ⟨m, ?_, hm⟩
    rintro rfl
    rw [hw] at hm
    have hww : w = w' := Option.some.inj hm
    subst hww
    have hmem : LoopLetter.res a ∈ w := hperm.mem_iff.2 (by simp)
    have : (w.any fun x => match x with | .res _ => true | _ => false) = true :=
      List.any_eq_true.2 ⟨_, hmem, rfl⟩
    rw [this] at hres
    exact absurd hres (by simp)

/-- `n` derivatives `PkgExpr.dent`, each raising the number of letters `Δ` by one. -/
private theorem ShapeInv.iter {H : List PkgLetter} (hH : ∀ z ∈ H, PkgLetter.isRes z = false)
    {T : LoopExpr} (u v : ℕ) : ∀ (n c : ℕ) (L : List PkgExpr),
      (∀ R ∈ L, ShapeInv H c T R.loops) →
      ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[n] L,
        ShapeInv H (c + n) T R.loops
  | 0, c, L, h => fun R hR => by simpa using h R hR
  | n + 1, c, L, h => fun R hR => by
      rw [Function.iterate_succ_apply'] at hR
      obtain ⟨R₀, hR₀, hR⟩ := List.mem_flatMap.1 hR
      exact (ShapeInv.iter hH u v n c L h R₀ hR₀).step hH u v hR

/-- The prefix of a list without `Δ`: it stays in the first piece. -/
private theorem seg_free_append (P Q : List PkgLetter) (hP : ∀ z ∈ P, PkgLetter.isEnt z = false) :
    ∃ (σ : List PkgLetter) (L : List (List PkgLetter)),
      Seg Q = σ :: L ∧ Seg (P ++ Q) = (P ++ σ) :: L := by
  obtain ⟨L₁, σ₁, h1, hall⟩ := seg_split P
  obtain ⟨σ, L, h2⟩ := seg_cons Q
  have hP1 : Seg P = [P] := List.splitOnP_eq_singleton hP
  rw [hP1] at h1
  obtain ⟨hL, hσ⟩ := List.append_inj' (show L₁ ++ [σ₁] = [] ++ [P] by simpa using h1.symm)
    (by simp)
  have hL' : L₁ = [] := by simpa using hL
  have hσ' : σ₁ = P := by simpa using hσ
  subst hL' hσ'
  exact ⟨σ, L, h2, by simpa using hall Q σ L h2⟩

private theorem takeWhile_pre {α : Type*} (p : α → Bool) :
    ∀ (P R : List α) (y : α), (∀ z ∈ P, p z = true) → p y = false →
      (P ++ y :: R).takeWhile p = P
  | [], R, y, _, hy => by simp [hy]
  | z :: P, R, y, h, hy => by
      have hz := h z (List.mem_cons_self)
      simp [hz,
        takeWhile_pre p P R y (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')) hy]

/-- The derivative structures of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]:
they have `1 + p + q` letters `Δ`; the first word is the main word, whose first package starts
with `𝔐_a`, has no resolvent to the left of `Λ̃_o` and contains `Λ̃_o`; every other package
starts with a resolvent; every package ends with a resolvent; the loops of `𝒯` without a
resolvent are unchanged. -/
theorem pkg_dwirt_shape (T : LoopExpr) (hT : T.wf = true) (ℓ : ℕ) (a : Fin 2)
    (tl : List LoopLetter) (hf : T.focus = some (ℓ, a, tl)) (u v p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt u v p q) :
    (R.loops.map fun w => w.countP PkgLetter.isEnt).sum = 1 + p + q ∧
    (∃ w ∈ R.loops.head?, ∃ σ ∈ pkgSegs w, σ.head? = some (.lw (.det a)) ∧
      σ.contains (.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))) = true ∧
      (σ.takeWhile fun x => x ≠ .lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))).countP
        PkgLetter.isRes = 0) ∧
    ((R.loops.map fun w => if w.any PkgLetter.isEnt then
        (pkgSegs w).countP fun σ => σ.head?.map PkgLetter.isRes != some true else 0).sum = 1) ∧
    (∀ w ∈ R.loops, w.any PkgLetter.isEnt = true → ∀ σ ∈ pkgSegs w,
      σ.getLast?.map PkgLetter.isRes = some true) ∧
    (∀ w ∈ T.loops, (w.any fun x => match x with | .res _ => true | _ => false) = false →
      w.map PkgLetter.lw ∈ R.loops) := by
  obtain ⟨w, tl₀, tl₁, hw, hperm, he, hfree, hnl⟩ := focus_shape hT hf
  have hI0 := ShapeInv.start hf hw hperm he
  have hH : ∀ z ∈ (LoopLetter.det a :: tl₀).map PkgLetter.lw ++
      [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))], PkgLetter.isRes z = false := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · have := hfree x hx
        revert this
        cases x <;> simp [PkgLetter.isRes, isResL]
    · rw [List.mem_singleton] at hz
      subst hz
      rfl
  unfold PkgExpr.dwirt at hR
  have h1 := ShapeInv.iter hH (T := T) v u q 1 [T.pkgStart]
    (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hI0)
  have h2 := ShapeInv.iter hH (T := T) u v p (1 + q) _ h1 R hR
  refine ⟨?_, ?_, h2.one, h2.last, h2.keep⟩
  · rw [h2.cnt]; omega
  · obtain ⟨Q, rest, hL⟩ := h2.main
    refine ⟨(LoopLetter.det a :: tl₀).map PkgLetter.lw ++
      [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))] ++ Q ++ [.ent 1 0], by rw [hL]; simp,
      ?_⟩
    obtain ⟨σ, L, hσ, hseg⟩ := seg_free_append
      ((LoopLetter.det a :: tl₀).map PkgLetter.lw ++
        [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))]) Q (by
          intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
            exact isEnt_lw x
          · rw [List.mem_singleton] at hz
            subst hz
            rfl)
    have hp := pkgSegs_perm ((LoopLetter.det a :: tl₀).map PkgLetter.lw ++
        [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))] ++ Q) [] 1 0
    rw [List.nil_append] at hp
    refine ⟨(LoopLetter.det a :: tl₀).map PkgLetter.lw ++
      [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))] ++ σ, ?_, ?_, ?_, ?_⟩
    · exact hp.symm.mem_iff.1 (by rw [hseg]; exact List.mem_cons_self)
    · simp
    · simp
    · have e : (LoopLetter.det a :: tl₀).map PkgLetter.lw ++
          [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))] ++ σ =
          (PkgLetter.lw (.det a) :: tl₀.map PkgLetter.lw) ++
            PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1)) :: σ := by simp
      rw [e, takeWhile_pre]
      · rw [List.countP_eq_zero]
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · simp [PkgLetter.isRes]
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
          have := hfree x hx
          revert this
          cases x <;> simp [PkgLetter.isRes, isResL]
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · simp
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
          have : x ≠ .lamt (if 1 ≤ T.kk 0 then 0 else 1) := fun hh => hnl (hh ▸ hx)
          simpa using this
      · simp

end RBMTransitionEdge

end
