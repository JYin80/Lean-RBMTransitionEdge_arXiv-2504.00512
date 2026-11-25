module

public import RBMTransitionEdge.Localized.Expansion.PkgCounts
public import RBMTransitionEdge.Localized.Expansion.Counts
public import RBMTransitionEdge.Localized.Expansion.PkgShape
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.Counts
import all RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# The invariants of the further expansion of Lemma 5.5

The labels, the place of `Λ̃₁`, the counts (5.86) [character_relation_further_expansion] and
(5.87) [character_relation_further_expansion2], the Type and the class `𝓡` of (5.79)–(5.81)
[further_expansion_expression_Type_1]–[further_expansion_expression_Type_3] on every expression
reached or expanded from a derivative structure in the proof of Lemma 5.5
[claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `fR = S - m + n + 1` of (5.86) [character_relation_further_expansion], `(m, n, u, S)` the
characters of Table 2 [table_effect_of_operations_2]. -/
def PkgExpr.fR (R : PkgExpr) : ℤ :=
  match R.charsP with
  | (m, n, _, S) => S - m + n + 1

/-- `m + u + fR - 4`, the number of operations other than `𝔣𝔯` in (5.87)
[character_relation_further_expansion2]. -/
def PkgExpr.fsig (R : PkgExpr) : ℤ :=
  match R.charsP with
  | (m, _, u, _) => m + u + R.fR - 4

/-- The entry labels `(u, v)` of the letters `Δ_{uv}` of an expression. -/
def PkgExpr.entLabels (R : PkgExpr) : List (ℕ × ℕ) :=
  R.loops.flatMap fun w => w.filterMap fun x => match x with
    | .ent u v => some (u, v)
    | _ => none

/-- Slot `a'` enters the expression only through one resolvent `𝒢_{a'}`: no `𝔐_{a'}` and no
light weight of slot `a'`. -/
def PkgExpr.onlyRes (R : PkgExpr) (a' : Fin 2) : Bool :=
  R.weights.all (fun p => p.1 != a') &&
  R.loops.all (fun w => !(w.contains (.lw (.det a')))) &&
  (R.loops.map fun w => w.count (.lw (.res a'))).sum == 1

open private focus_foc from RBMTransitionEdge.Localized.Expansion.Counts
open private dent_cases pkgSegs_perm seg_free_append takeWhile_pre
  from RBMTransitionEdge.Localized.Expansion.PkgShape
open private sum_map_set sum_map_eraseIdx from RBMTransitionEdge.Localized.Expansion.PkgWords

/-! ### Auxiliary facts: induction on the further tree -/

/-- A property kept by one step of the further expansion holds on the whole further tree of
a list whose members have it. -/
private theorem inv_fTree (P : PkgExpr → Prop) (hstep : ∀ S, P S → ∀ R ∈ S.fstep, P R) :
    ∀ (k : ℕ) (L : List PkgExpr), (∀ S ∈ L, P S) → ∀ R ∈ fTree k L, P R
  | 0, L, hL, R, hR => hL R hR
  | k + 1, L, hL, R, hR => by
      refine inv_fTree P hstep k (L.flatMap PkgExpr.fstep) (fun S hS => ?_) R hR
      obtain ⟨S', hS', hSS⟩ := List.mem_flatMap.1 hS
      exact hstep S' (hL S' hS') S hSS

/-- A property of `𝓡₀` kept by one step of the further expansion holds on every expression
reached or expanded from `𝓡₀`. -/
private theorem inv_reach (P : PkgExpr → Prop) (hstep : ∀ S, P S → ∀ R ∈ S.fstep, P R)
    (ε : ℝ) (j : ℕ) (R₀ R : PkgExpr) (h0 : P R₀)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) : P R :=
  inv_fTree P hstep _ [R₀] (fun S hS => by rw [List.mem_singleton.1 hS]; exact h0) R
    (pkg_fdepth ε j R₀ R hR)

/-! ### Auxiliary facts: the terms of one step -/

/-- The word `W` of the terms of `fterms`: `𝒢_a tl` closed by `𝔐_a` (resolvent to the right) or
`𝔐_a tl` closed by `𝒢_a` (resolvent to the left). -/
private def invW (right : Bool) (a : Fin 2) (tl : List PkgLetter) : List PkgLetter :=
  if right then .lw (.res a) :: tl ++ [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]

/-- The loops of every term of `fterms`: the chosen resolvent `𝒢_a` stands at the head of the
rotation `𝒢_a tl` of a word `w`, and the term is the replacement, the light weight, a cut at a
resolvent of `W`, the plug of a light weight, or the join with a resolvent of another word. -/
private theorem fterms_cases (P R' : PkgExpr) (o : PkgOp) (h : (o, R') ∈ P.fterms) :
    ∃ (ℓ r : ℕ) (right : Bool) (w : List PkgLetter) (a : Fin 2) (tl : List PkgLetter),
      P.loops[ℓ]? = some w ∧ w.rotate r = .lw (.res a) :: tl ∧
      (R'.loops = P.loops.set ℓ (.lw (.det a) :: tl) ∨
       R'.loops = P.loops.set ℓ (if right then .lw (.proj P.nb) :: invW right a tl
         else invW right a tl ++ [.lw (.proj P.nb)]) ∨
       (∃ (q : ℕ) (b : Fin 2), (invW right a tl)[q]? = some (.lw (.res b)) ∧
         R'.loops = P.loops.set ℓ ((invW right a tl).take (q + 1) ++ [.lw (.proj P.nb)]) ++
           [.lw (.proj P.nb) :: (invW right a tl).drop q]) ∨
       (∃ (b : Fin 2) (y : ℕ), R'.loops = P.loops.set ℓ (invW right a tl ++
         [.lw (.proj P.nb), .lw (.res b), .lw (.proj y), .lw (.res b), .lw (.proj P.nb)])) ∨
       (∃ (j : ℕ) (f F : List PkgLetter) (q : ℕ) (b : Fin 2), j ≠ ℓ ∧ P.loops[j]? = some f ∧
         f.rotate q = .lw (.res b) :: F ∧
         R'.loops = (P.loops.set ℓ (invW right a tl ++ [.lw (.proj P.nb)] ++ f.rotate q ++
           [.lw (.res b), .lw (.proj P.nb)])).eraseIdx j)) := by
  unfold PkgExpr.fterms at h
  split at h
  · simp at h
  · rename_i ℓ r right hf
    split at h
    · simp at h
    · rename_i w hw
      split at h
      · rename_i a tl hrot
        dsimp only at h
        have hWdef : (if right = true then PkgLetter.lw (.res a) :: tl ++ [PkgLetter.lw (.det a)]
            else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)]) = invW right a tl := rfl
        rw [hWdef] at h
        refine ⟨ℓ, r, right, w, a, tl, hw, hrot, ?_⟩
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with h | h
              · obtain ⟨-, rfl⟩ := Prod.mk.inj h
                exact Or.inl rfl
              · rcases List.mem_cons.1 h with h | h
                · obtain ⟨-, rfl⟩ := Prod.mk.inj h
                  exact Or.inr (Or.inl rfl)
                · simp at h
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 h
              split at hq
              · simp at hq
              · split at hq
                · rename_i b hqb
                  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  exact Or.inr (Or.inr (Or.inl ⟨q, b, hqb, rfl⟩))
                · simp at hq
          · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
            split at hj
            · rename_i b y hjb
              obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨b, y, rfl⟩)))
            · simp at hj
        · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
          split at hj
          · simp at hj
          · rename_i hjℓ
            split at hj
            · simp at hj
            · rename_i f hf'
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · rename_i b hqb
                obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                have hrh : ∃ F, f.rotate q = .lw (.res b) :: F := by
                  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hqb
                  refine ⟨f.drop (q + 1) ++ f.take q, ?_⟩
                  rw [List.rotate_eq_drop_append_take_mod, Nat.mod_eq_of_lt hlt,
                    List.drop_eq_getElem_cons hlt, hget]
                  rfl
                obtain ⟨F, hF⟩ := hrh
                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, f, F, q, b, hjℓ, hf', hF, rfl⟩)))
              · simp at hq
      · simp at h

/-! ### Auxiliary facts: the stretch of letters before `Λ̃₁` in a heavy package -/

/-- A rotation of a list swaps its two parts. -/
private theorem rotated_split {α : Type*} {l l' : List α} (h : l.IsRotated l') :
    ∃ A B : List α, l = A ++ B ∧ l' = B ++ A := by
  obtain ⟨n, hn⟩ := h
  refine ⟨l.take (n % l.length), l.drop (n % l.length), (List.take_append_drop _ _).symm, ?_⟩
  rw [← hn, List.rotate_eq_drop_append_take_mod]

/-- The letters between a `Δ` and `Λ̃₁`: no `Δ`, no resolvent and no `Λ̃`. -/
private def FreeS (S : List PkgLetter) : Prop :=
  ∀ x ∈ S, x.isEnt = false ∧ x.isRes = false ∧ x.isLam = false

/-- The word cyclically contains `Δ_{uv} S Λ̃₁` with `S` free of `Δ`, resolvents and `Λ̃`. -/
private def ArcW (w : List PkgLetter) : Prop :=
  ∃ (u v : ℕ) (S Y : List PkgLetter), FreeS S ∧
    (PkgLetter.ent u v :: (S ++ .lw (.lamt 0) :: Y)).IsRotated w

/-- A word with the block `Δ_{uv} S Λ̃₁` inside it has the property. -/
private theorem arcW_of_infix (A B S : List PkgLetter) (u v : ℕ) (hS : FreeS S) :
    ArcW (A ++ (PkgLetter.ent u v :: (S ++ [PkgLetter.lw (.lamt 0)])) ++ B) := by
  refine ⟨u, v, S, B ++ A, hS, ?_⟩
  have h := List.isRotated_append (l := PkgLetter.ent u v :: (S ++ .lw (.lamt 0) :: B))
    (l' := A)
  have e1 : (PkgLetter.ent u v :: (S ++ .lw (.lamt 0) :: B)) ++ A =
      PkgLetter.ent u v :: (S ++ .lw (.lamt 0) :: (B ++ A)) := by simp
  have e2 : A ++ (PkgLetter.ent u v :: (S ++ .lw (.lamt 0) :: B)) =
      A ++ (PkgLetter.ent u v :: (S ++ [PkgLetter.lw (.lamt 0)])) ++ B := by simp
  rw [e1, e2] at h
  exact h

/-- The property is invariant under rotation of the word. -/
private theorem ArcW.rot {w w' : List PkgLetter} (h : ArcW w) (hr : w.IsRotated w') : ArcW w' := by
  obtain ⟨u, v, S, Y, hS, hrot⟩ := h
  exact ⟨u, v, S, Y, hS, hrot.trans hr⟩

/-- The letters of the block `Δ_{uv} S Λ̃₁` are not resolvents. -/
private theorem arc_not_res (u v : ℕ) (S : List PkgLetter) (hS : FreeS S) (a : Fin 2) :
    PkgLetter.lw (.res a) ∉ (PkgLetter.ent u v :: (S ++ [PkgLetter.lw (.lamt 0)])) := by
  intro h
  rcases List.mem_cons.1 h with h | h
  · cases h
  · rcases List.mem_append.1 h with h | h
    · have := (hS _ h).2.1
      simp [PkgLetter.isRes] at this
    · rw [List.mem_singleton] at h
      cases h

/-- If a word with the block `Δ_{uv} S Λ̃₁` is rotated to start at a resolvent `𝒢_a`, the rest
contains the block. -/
private theorem arc_in_tl (w tl : List PkgLetter) (r : ℕ) (a : Fin 2) (h : ArcW w)
    (hr : w.rotate r = .lw (.res a) :: tl) :
    ∃ (A B S : List PkgLetter) (u v : ℕ), FreeS S ∧
      tl = A ++ (PkgLetter.ent u v :: (S ++ [PkgLetter.lw (.lamt 0)])) ++ B := by
  obtain ⟨u, v, S, Y, hS, hrot⟩ := h
  have h2 : (PkgLetter.ent u v :: (S ++ .lw (.lamt 0) :: Y)).IsRotated (.lw (.res a) :: tl) :=
    hrot.trans (by rw [← hr]; exact (List.IsRotated.forall w r).symm)
  obtain ⟨A₁, B₁, hL, hres⟩ := rotated_split h2
  have hnr := arc_not_res u v S hS a
  have hL' : (PkgLetter.ent u v :: (S ++ [PkgLetter.lw (.lamt 0)])) ++ Y = A₁ ++ B₁ := by
    rw [← hL]; simp
  rcases List.append_eq_append_iff.1 hL'.symm with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases a' with _ | ⟨x, a''⟩
    · rw [List.append_nil] at h1
      rw [List.nil_append] at h2
      subst h1
      rcases B₁ with _ | ⟨y, Y'⟩
      · simp at hres
      · simp only [List.cons_append, List.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        refine ⟨Y', [], S, u, v, hS, ?_⟩
        simp
    · simp only [List.cons_append] at h2
      rw [h2] at hres
      simp only [List.cons_append, List.cons.injEq] at hres
      have hx := hres.1
      exact absurd (by rw [h1, hx]; simp) hnr
  · rcases B₁ with _ | ⟨x, B'⟩
    · simp only [List.nil_append] at hres
      rw [h1] at hres
      simp at hres
    · simp only [List.cons_append, List.cons.injEq] at hres
      obtain ⟨-, rfl⟩ := hres
      refine ⟨B', c', S, u, v, hS, ?_⟩
      rw [h1]
      simp

/-- A list that splits at a letter outside a block contains the block on one side of it. -/
private theorem infix_split {α : Type*} (X Y A B arc : List α) (c : α) (hc : c ∉ arc)
    (h : X ++ c :: Y = A ++ arc ++ B) :
    (∃ B', X = A ++ arc ++ B') ∨ (∃ A', Y = A' ++ arc ++ B) := by
  rw [List.append_assoc] at h
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases a' with _ | ⟨x, a''⟩
    · rw [List.append_nil] at h1
      subst h1
      rcases arc with _ | ⟨y, arc'⟩
      · exact Or.inl ⟨[], by simp⟩
      · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h2
        exact absurd (h2.1 ▸ List.mem_cons_self) hc
    · simp only [List.cons_append, List.cons.injEq] at h2
      exact Or.inr ⟨a'', by rw [h2.2]; simp⟩
  · rcases List.append_eq_append_iff.1 h2 with ⟨a', h3, h4⟩ | ⟨c'', h3, h4⟩
    · exact Or.inl ⟨a', by rw [h1, h3]; simp⟩
    · rcases c'' with _ | ⟨x, c'''⟩
      · rw [List.append_nil] at h3
        exact Or.inl ⟨[], by rw [h1, ← h3]; simp⟩
      · simp only [List.cons_append, List.cons.injEq] at h4
        exact absurd (by rw [h3, ← h4.1]; simp) hc

/-! ### Auxiliary facts: lists of words -/

/-- The entry written by `List.set` is a member of the new list. -/
private theorem mem_set_self {α : Type*} (L : List α) (ℓ : ℕ) (N w : α) (hw : L[ℓ]? = some w) :
    N ∈ L.set ℓ N := by
  have hl : ℓ < L.length := (List.getElem?_eq_some_iff.1 hw).1
  exact List.mem_iff_getElem?.2 ⟨ℓ, List.getElem?_set_self hl⟩

/-- An entry different from the replaced one stays in the list after `List.set`. -/
private theorem mem_set_of_ne {α : Type*} (L : List α) (ℓ : ℕ) (N w w₁ : α)
    (hw : L[ℓ]? = some w) (h : w₁ ∈ L) (hne : w₁ ≠ w) : w₁ ∈ L.set ℓ N := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  have hiℓ : ℓ ≠ i := by
    rintro rfl
    rw [hw] at hi
    exact hne (Option.some.inj hi).symm
  exact List.mem_iff_getElem?.2 ⟨i, by rw [List.getElem?_set_ne hiℓ]; exact hi⟩

/-- An entry at another position stays in the list after `List.eraseIdx`. -/
private theorem mem_eraseIdx_of {α : Type*} (L : List α) (j i : ℕ) (x : α) (hij : i ≠ j)
    (h : L[i]? = some x) : x ∈ L.eraseIdx j :=
  List.mem_eraseIdx_iff_getElem?.2 ⟨i, hij, h⟩

/-- A word split at the entry `res b` in position `q`: the two overlapping pieces of a cut. -/
private theorem cut_pieces (W : List PkgLetter) (q : ℕ) (b : Fin 2)
    (h : W[q]? = some (.lw (.res b))) :
    ∃ X Y : List PkgLetter, W = X ++ .lw (.res b) :: Y ∧ W.take (q + 1) = X ++ [.lw (.res b)] ∧
      W.drop q = .lw (.res b) :: Y := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  have hd : W.drop q = .lw (.res b) :: W.drop (q + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  refine ⟨W.take q, W.drop (q + 1), ?_, ?_, hd⟩
  · conv_lhs => rw [← List.take_append_drop q W, hd]
  · rw [List.take_add_one, h]
    rfl

/-- A block inside `tl` is inside the word `W` of the terms of `fterms`. -/
private theorem invW_infix (right : Bool) (a : Fin 2) (tl A arc B : List PkgLetter)
    (h : tl = A ++ arc ++ B) :
    ∃ W₁ W₂ : List PkgLetter, invW right a tl = W₁ ++ arc ++ W₂ := by
  subst h
  cases right
  · exact ⟨.lw (.det a) :: A, B ++ [.lw (.res a)], by simp [invW]⟩
  · exact ⟨.lw (.res a) :: A, B ++ [.lw (.det a)], by simp [invW]⟩

/-! ### Auxiliary facts: the block `Δ S Λ̃₁` under the derivative and the further expansion -/

/-- Some word of the expression contains cyclically a block `Δ_{uv} S Λ̃₁`. -/
private def ArcInv (R : PkgExpr) : Prop := ∃ w ∈ R.loops, ArcW w

/-- One derivative `∂` with `∂𝒢 = -𝒢 Δ_{uv} 𝒢` keeps a block `Δ S Λ̃₁` in some word: it
inserts at a resolvent, which lies outside the block. -/
private theorem arcInv_dent (R R' : PkgExpr) (u v : ℕ) (hR : ArcInv R) (h : R' ∈ R.dent u v) :
    ArcInv R' := by
  obtain ⟨w₁, hw₁, harc⟩ := hR
  rcases dent_cases R R' u v h with ⟨ℓ, X, Y, a, hℓ, hl⟩ | ⟨b, y, hl⟩
  · by_cases hw : w₁ = X ++ .lw (.res a) :: Y
    · subst hw
      have hrot : (X ++ .lw (.res a) :: Y).rotate X.length = .lw (.res a) :: (Y ++ X) :=
        List.rotate_append_length_eq X (.lw (.res a) :: Y)
      obtain ⟨A, B, S, u', v', hS, htl⟩ := arc_in_tl _ _ _ _ harc hrot
      refine ⟨X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y, ?_, ?_⟩
      · rw [hl]
        exact mem_set_self _ ℓ _ _ hℓ
      · have h1 := arcW_of_infix ([.lw (.res a), .ent u v, .lw (.res a)] ++ A) B S u' v' hS
        refine h1.rot ?_
        have h2 := List.isRotated_append (l := X) (l' := [PkgLetter.lw (.res a), .ent u v,
          .lw (.res a)] ++ Y)
        have e1 : X ++ ([PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y) =
            X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y := by simp
        have e2 : ([PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y) ++ X =
            [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ A ++
              PkgLetter.ent u' v' :: (S ++ [PkgLetter.lw (.lamt 0)]) ++ B := by
          simp only [List.append_assoc] at htl ⊢
          rw [htl]
        rw [e1, e2] at h2
        exact h2.symm
    · exact ⟨w₁, by rw [hl]; exact mem_set_of_ne _ ℓ _ _ _ hℓ hw₁ hw, harc⟩
  · exact ⟨w₁, by rw [hl]; exact List.mem_append_left _ hw₁, harc⟩

/-- `List.set` at a valid position puts the new entry there. -/
private theorem getElem?_set_self_of {α : Type*} (L : List α) (ℓ : ℕ) (N w : α)
    (hw : L[ℓ]? = some w) : (L.set ℓ N)[ℓ]? = some N :=
  List.getElem?_set_self (List.getElem?_eq_some_iff.1 hw).1

/-- One step of the further expansion keeps a block `Δ_{uv} S Λ̃₁` in some word: every term
acts at one resolvent, which lies outside the block. -/
private theorem arcInv_step (P : PkgExpr) (hP : ArcInv P) (R' : PkgExpr) (h : R' ∈ P.fstep) :
    ArcInv R' := by
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  change ArcInv R''
  obtain ⟨ℓ, r, right, w, a, tl, hw, hrot, hcases⟩ := fterms_cases P R'' o hmem
  obtain ⟨w₁, hw₁, harc⟩ := hP
  by_cases hww : w₁ = w
  · subst hww
    obtain ⟨A, B, S, u, v, hS, htl⟩ := arc_in_tl _ _ r a harc hrot
    obtain ⟨W₁, W₂, hW⟩ := invW_infix right a tl A _ B htl
    rcases hcases with hl | hl | ⟨q, b, hq, hl⟩ | ⟨b, y, hl⟩ | ⟨j, f, F, q, b, hjℓ, hf, hF, hl⟩
    · refine ⟨.lw (.det a) :: tl, by rw [hl]; exact mem_set_self _ ℓ _ _ hw, ?_⟩
      have h1 := arcW_of_infix (.lw (.det a) :: A) B S u v hS
      have e : PkgLetter.lw (.det a) :: tl = (.lw (.det a) :: A) ++
          (PkgLetter.ent u v :: (S ++ [PkgLetter.lw (.lamt 0)])) ++ B := by rw [htl]; simp
      rw [e]
      exact h1
    · refine ⟨_, by rw [hl]; exact mem_set_self _ ℓ _ _ hw, ?_⟩
      cases right
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hW]
        have h1 := arcW_of_infix W₁ (W₂ ++ [.lw (.proj P.nb)]) S u v hS
        simpa using h1
      · simp only [↓reduceIte]
        rw [hW]
        have h1 := arcW_of_infix (.lw (.proj P.nb) :: W₁) W₂ S u v hS
        simpa using h1
    · obtain ⟨X, Y, hXY, htake, hdrop⟩ := cut_pieces _ q b hq
      rcases infix_split X Y W₁ W₂ _ (.lw (.res b)) (arc_not_res u v S hS b)
          (hXY.symm.trans hW) with ⟨B', hX⟩ | ⟨A', hY⟩
      · refine ⟨_, by rw [hl]; exact List.mem_append_left _ (mem_set_self _ ℓ _ _ hw), ?_⟩
        rw [htake, hX]
        have h1 := arcW_of_infix W₁ (B' ++ [.lw (.res b), .lw (.proj P.nb)]) S u v hS
        simpa using h1
      · refine ⟨_, by rw [hl]; exact List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [hdrop, hY]
        have h1 := arcW_of_infix (.lw (.proj P.nb) :: .lw (.res b) :: A') W₂ S u v hS
        simpa using h1
    · refine ⟨_, by rw [hl]; exact mem_set_self _ ℓ _ _ hw, ?_⟩
      rw [hW]
      have h1 := arcW_of_infix W₁ (W₂ ++ [.lw (.proj P.nb), .lw (.res b), .lw (.proj y),
        .lw (.res b), .lw (.proj P.nb)]) S u v hS
      simpa using h1
    · have hM : ∀ M, R''.loops = (P.loops.set ℓ M).eraseIdx j → M ∈ R''.loops := fun M hM => by
        rw [hM]
        exact mem_eraseIdx_of _ j ℓ _ (Ne.symm hjℓ) (getElem?_set_self_of _ ℓ _ _ hw)
      refine ⟨_, hM _ hl, ?_⟩
      rw [hW]
      have h1 := arcW_of_infix W₁ (W₂ ++ [.lw (.proj P.nb)] ++ f.rotate q ++
        [.lw (.res b), .lw (.proj P.nb)]) S u v hS
      simpa using h1
  · rcases hcases with hl | hl | ⟨q, b, hq, hl⟩ | ⟨b, y, hl⟩ | ⟨j, f, F, q, b, hjℓ, hf, hF, hl⟩
    · exact ⟨w₁, by rw [hl]; exact mem_set_of_ne _ ℓ _ _ _ hw hw₁ hww, harc⟩
    · exact ⟨w₁, by rw [hl]; exact mem_set_of_ne _ ℓ _ _ _ hw hw₁ hww, harc⟩
    · exact ⟨w₁, by rw [hl]; exact List.mem_append_left _ (mem_set_of_ne _ ℓ _ _ _ hw hw₁ hww),
        harc⟩
    · exact ⟨w₁, by rw [hl]; exact mem_set_of_ne _ ℓ _ _ _ hw hw₁ hww, harc⟩
    · have hM : ∀ M, R''.loops = (P.loops.set ℓ M).eraseIdx j → M ∈ R''.loops := fun M hM => by
        rw [hM]
        exact mem_eraseIdx_of _ j ℓ _ (Ne.symm hjℓ) (getElem?_set_self_of _ ℓ _ _ hw)
      by_cases hwf : w₁ = f
      · subst hwf
        obtain ⟨A, B, S, u, v, hS, hFt⟩ := arc_in_tl _ _ q b harc hF
        refine ⟨_, hM _ hl, ?_⟩
        rw [hF, hFt]
        have h1 := arcW_of_infix (invW right a tl ++ [.lw (.proj P.nb), .lw (.res b)] ++ A)
          (B ++ [.lw (.res b), .lw (.proj P.nb)]) S u v hS
        simpa using h1
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw₁
        have hiℓ : ℓ ≠ i := by
          rintro rfl
          rw [hw] at hi
          exact hww (Option.some.inj hi).symm
        have hij : j ≠ i := by
          rintro rfl
          rw [hf] at hi
          exact hwf (Option.some.inj hi).symm
        refine ⟨w₁, ?_, harc⟩
        rw [hl]
        exact mem_eraseIdx_of _ j i w₁ (Ne.symm hij) (by rw [List.getElem?_set_ne hiℓ]; exact hi)

/-! ### Auxiliary facts: the start of the further expansion -/

/-- Without a focus, the start has no loops and no light weights, so no derivative of it exists. -/
private theorem dent_empty (E : PkgExpr) (hl : E.loops = []) (hw : E.weights = []) (u v : ℕ) :
    E.dent u v = [] := by
  simp [PkgExpr.dent, hl, hw]

/-- A derivative structure of the start with `p + q = 2` exists only if the focus of `𝒯` is some. -/
private theorem focus_isSome (T : LoopExpr) (p q : ℕ) (hpq : p + q = 2) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) : T.focus.isSome = true := by
  by_contra hno
  have hn : T.focus = none := by simpa using hno
  have hE : T.pkgStart.loops = [] ∧ T.pkgStart.weights = [] := by
    unfold LoopExpr.pkgStart
    rw [hn]
    exact ⟨rfl, rfl⟩
  have hF : ∀ u v : ℕ, (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v) [] = [] :=
    fun u v => rfl
  have hI : ∀ (u v p : ℕ), (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[p] [] =
      [] := fun u v p => Function.iterate_fixed (hF u v) p
  have hS : ∀ (u v : ℕ), [T.pkgStart].flatMap (fun R' => R'.dent u v) = [] := fun u v => by
    simp [dent_empty _ hE.1 hE.2]
  unfold PkgExpr.dwirt at hR
  rcases q with _ | q
  · rcases p with _ | p
    · omega
    · rw [Function.iterate_succ_apply, Function.iterate_zero_apply] at hR
      rw [hS, hI] at hR
      simp at hR
  · rw [Function.iterate_succ_apply, hS, hI, hI] at hR
    simp at hR

/-- The loops of the start when the focus is `(ℓ, a, tl)`: the package `𝔐_a tl 𝒢_a Δ₁₀` and the
other loops of `T`. -/
private theorem pkgStart_loops {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (hf : T.focus = some (ℓ, a, tl)) :
    T.pkgStart.loops = (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0]) :: (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw := by
  unfold LoopExpr.pkgStart
  rw [hf]

/-- The start `(𝔐_a B Λ̃₁ ⋯ 𝒢_a Δ₁₀)` of a loop with `k₁ ≥ 1` contains a block `Δ S Λ̃₁`:
`B` has no resolvent and no `Λ̃`. -/
private theorem arcInv_start (T : LoopExpr) (hT : T.wf = true) (hk : 1 ≤ T.kk 0) (ℓ : ℕ)
    (a : Fin 2) (tl : List LoopLetter) (hf : T.focus = some (ℓ, a, tl)) :
    ArcInv T.pkgStart := by
  obtain ⟨o, o', w, B, Y, hoo, hw, htl, F⟩ := focus_foc hT hf
  obtain ⟨-, -, hnlB, hrsB, -⟩ := F
  have ho : o = 0 := by
    rcases hoo with ⟨h, -, -⟩ | ⟨-, -, h⟩
    · exact h
    · omega
  subst ho
  refine ⟨_, by rw [pkgStart_loops hf]; exact List.mem_cons_self, ?_⟩
  have hS : FreeS ((LoopLetter.det a :: B).map PkgLetter.lw) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨rfl, rfl, rfl⟩
    · cases z with
      | res c =>
          have := List.countP_eq_zero.1 hrsB _ hz
          exact absurd rfl this
      | det c => exact ⟨rfl, rfl, rfl⟩
      | proj y => exact ⟨rfl, rfl, rfl⟩
      | lamt k => exact absurd hz (hnlB k)
  refine ⟨1, 0, (LoopLetter.det a :: B).map PkgLetter.lw,
    (Y ++ [LoopLetter.res a]).map PkgLetter.lw, hS, ?_⟩
  have e : ((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0] = (((LoopLetter.det a :: B).map PkgLetter.lw ++ PkgLetter.lw
        (.lamt 0) :: (Y ++ [LoopLetter.res a]).map PkgLetter.lw) ++ [PkgLetter.ent 1 0]) := by
    rw [htl]
    simp
  rw [e]
  exact (List.isRotated_concat _ _).symm

/-- The block `Δ S Λ̃₁` survives any number of derivatives. -/
private theorem arcInv_iter (u v : ℕ) : ∀ (p : ℕ) (L : List PkgExpr), (∀ R ∈ L, ArcInv R) →
    ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[p] L, ArcInv R
  | 0, L, hL, R, hR => hL R hR
  | p + 1, L, hL, R, hR => by
      rw [Function.iterate_succ_apply] at hR
      refine arcInv_iter u v p _ ?_ R hR
      intro R' hR'
      obtain ⟨R'', hR'', hd⟩ := List.mem_flatMap.1 hR'
      exact arcInv_dent R'' R' u v (hL R'' hR'') hd

/-- The derivative structures of a start with `k₁ ≥ 1` contain a block `Δ S Λ̃₁`. -/
private theorem arcInv_dwirt (T : LoopExpr) (hT : T.wf = true) (hk : 1 ≤ T.kk 0) (p q : ℕ)
    (hpq : p + q = 2) (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) : ArcInv R := by
  obtain ⟨⟨ℓ, a, tl⟩, hfoc⟩ := Option.isSome_iff_exists.1 (focus_isSome T p q hpq R hR)
  have h0 := arcInv_start T hT hk ℓ a tl hfoc
  unfold PkgExpr.dwirt at hR
  refine arcInv_iter 0 1 p _ (fun R₁ hR₁ => ?_) R hR
  refine arcInv_iter 1 0 q [T.pkgStart] ?_ R₁ hR₁
  intro R₂ hR₂
  rw [List.mem_singleton.1 hR₂]
  exact h0

/-- A word with a block `Δ S Λ̃₁` has a heavy package in which `Λ̃₁` is preceded by the letters
`S` and no resolvent or `Λ̃`. -/
private theorem arcW_target (w : List PkgLetter) (h : ArcW w) :
    w.any PkgLetter.isEnt = true ∧ ∃ σ ∈ pkgSegs w, PkgLetter.lw (.lamt 0) ∈ σ ∧
      (σ.takeWhile fun x => x ≠ PkgLetter.lw (.lamt 0)).all
        (fun x => !x.isRes && !x.isLam) = true := by
  obtain ⟨u, v, S, Y, hS, hrot⟩ := h
  refine ⟨List.any_eq_true.2 ⟨.ent u v, ?_, rfl⟩, ?_⟩
  · exact hrot.mem_iff.1 List.mem_cons_self
  obtain ⟨A₁, B₁, hL, hw⟩ := rotated_split hrot
  have hdec : ∃ A B' : List PkgLetter, w = A ++ .ent u v :: B' ∧
      B' ++ A = S ++ .lw (.lamt 0) :: Y := by
    rcases A₁ with _ | ⟨x, A₁'⟩
    · simp only [List.nil_append] at hL
      subst hL
      exact ⟨[], S ++ .lw (.lamt 0) :: Y, by simpa using hw, by simp⟩
    · simp only [List.cons_append, List.cons.injEq] at hL
      obtain ⟨rfl, hL2⟩ := hL
      exact ⟨B₁, A₁', by rw [hw], hL2.symm⟩
  obtain ⟨A, B', hwA, hBA⟩ := hdec
  have hP : ∀ z ∈ S ++ [PkgLetter.lw (.lamt 0)], PkgLetter.isEnt z = false := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact (hS z hz).1
    · rw [List.mem_singleton] at hz
      subst hz
      rfl
  obtain ⟨σ, L, hσ, hseg⟩ := seg_free_append (S ++ [PkgLetter.lw (.lamt 0)]) Y hP
  have hperm := pkgSegs_perm A B' u v
  rw [← hwA, hBA] at hperm
  have e : S ++ PkgLetter.lw (.lamt 0) :: Y = S ++ [PkgLetter.lw (.lamt 0)] ++ Y := by simp
  rw [e, hseg] at hperm
  refine ⟨(S ++ [PkgLetter.lw (.lamt 0)]) ++ σ, hperm.symm.mem_iff.1 List.mem_cons_self, ?_, ?_⟩
  · simp
  · have e2 : (S ++ [PkgLetter.lw (.lamt 0)]) ++ σ = S ++ PkgLetter.lw (.lamt 0) :: σ := by simp
    rw [e2, takeWhile_pre]
    · rw [List.all_eq_true]
      intro z hz
      have := hS z hz
      simp [this.2.1, this.2.2]
    · intro z hz
      have := (hS z hz).2.2
      have hz' : z ≠ PkgLetter.lw (.lamt 0) := by
        rintro rfl
        simp [PkgLetter.isLam] at this
      simpa using hz'
    · simp

/-! ### Auxiliary facts: the letters `Δ` of the further expansion -/

/-- The number of letters `Δ` of a word. -/
private def cE (w : List PkgLetter) : ℕ := w.countP PkgLetter.isEnt

/-- The number of letters `Δ` of the empty word is `0`. -/
private theorem cE_nil : cE ([] : List PkgLetter) = 0 := rfl

/-- The number of letters `Δ` of a concatenation. -/
private theorem cE_append (A B : List PkgLetter) : cE (A ++ B) = cE A + cE B := by
  simp [cE, List.countP_append]

/-- A loop letter is not a letter `Δ`. -/
private theorem cE_cons_lw (x : LoopLetter) (l : List PkgLetter) : cE (.lw x :: l) = cE l := by
  simp [cE, PkgLetter.isEnt]

/-- A letter `Δ` counts once. -/
private theorem cE_ent (u v : ℕ) (l : List PkgLetter) : cE (.ent u v :: l) = cE l + 1 := by
  simp [cE, List.countP_cons, PkgLetter.isEnt]

/-- A word of loop letters has no letter `Δ`. -/
private theorem cE_lw_map (l : List LoopLetter) : cE (l.map PkgLetter.lw) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, cE_cons_lw, ih]

/-- Every letter `Δ` of the word has the entry label `(0, 1)` or `(1, 0)`. -/
private def GW (w : List PkgLetter) : Prop :=
  ∀ u v : ℕ, PkgLetter.ent u v ∈ w → (u, v) = (0, 1) ∨ (u, v) = (1, 0)

/-- The expression has `k` letters `Δ` in all, each with entry label `(0, 1)` or `(1, 0)`. -/
private def LabK (k : ℕ) (R : PkgExpr) : Prop :=
  (R.loops.map cE).sum = k ∧ ∀ w ∈ R.loops, GW w

/-- One step of the further expansion keeps the number and the labels of the letters `Δ`: every
term cuts, joins and rearranges the letters of the expanded words, and adds only letters
`𝔐`, `𝒢`, `E_x`. -/
private theorem labK_step (k : ℕ) (P : PkgExpr) (hP : LabK k P) (R' : PkgExpr)
    (h : R' ∈ P.fstep) : LabK k R' := by
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  change LabK k R''
  obtain ⟨ℓ, r, right, w, a, tl, hw, hrot, hcases⟩ := fterms_cases P R'' o hmem
  obtain ⟨hsum, hgood⟩ := hP
  suffices key : (R''.loops.map cE).sum = (P.loops.map cE).sum ∧ ∀ w' ∈ R''.loops, GW w' from
    ⟨key.1.trans hsum, key.2⟩
  have hwm : w ∈ P.loops := List.mem_of_getElem? hw
  have hcw : cE w = cE tl := by
    have := (List.rotate_perm w r).countP_eq PkgLetter.isEnt
    rw [hrot] at this
    simpa [cE, List.countP_cons, PkgLetter.isEnt] using this.symm
  have hgtl : ∀ u v, PkgLetter.ent u v ∈ tl → (u, v) = (0, 1) ∨ (u, v) = (1, 0) := by
    intro u v hu
    refine hgood w hwm u v ?_
    rw [← List.mem_rotate (n := r), hrot]
    exact List.mem_cons_of_mem _ hu
  have hcW : cE (invW right a tl) = cE tl := by
    cases right <;> simp [invW, cE, List.countP_append, PkgLetter.isEnt]
  have hgW : ∀ u v, PkgLetter.ent u v ∈ invW right a tl → (u, v) = (0, 1) ∨ (u, v) = (1, 0) := by
    intro u v hu
    refine hgtl u v ?_
    cases right <;> simpa [invW] using hu
  have set_case : ∀ N, R''.loops = P.loops.set ℓ N → cE N = cE w → GW N →
      (R''.loops.map cE).sum = (P.loops.map cE).sum ∧ ∀ w' ∈ R''.loops, GW w' := by
    intro N hl hc hN
    have h1 := sum_map_set cE P.loops ℓ w N hw
    refine ⟨by rw [hl]; omega, fun w' hw' => ?_⟩
    rw [hl] at hw'
    rcases List.mem_or_eq_of_mem_set hw' with h | rfl
    · exact hgood w' h
    · exact hN
  rcases hcases with hl | hl | ⟨q, b, hq, hl⟩ | ⟨b, y, hl⟩ | ⟨j, f, F, q, b, hjℓ, hf, hF, hl⟩
  · exact set_case _ hl (by rw [cE_cons_lw, hcw]) (fun u v hu => hgtl u v (by simpa using hu))
  · cases right
    · simp only [Bool.false_eq_true, ↓reduceIte] at hl
      refine set_case _ hl (by rw [cE_append, hcW, hcw]; simp [cE, PkgLetter.isEnt]) ?_
      intro u v hu
      rcases List.mem_append.1 hu with hu | hu
      · exact hgW u v hu
      · rw [List.mem_singleton] at hu
        cases hu
    · simp only [↓reduceIte] at hl
      refine set_case _ hl (by rw [cE_cons_lw, hcW, hcw]) ?_
      intro u v hu
      rcases List.mem_cons.1 hu with hu | hu
      · cases hu
      · exact hgW u v hu
  · obtain ⟨X, Y, hXY, htake, hdrop⟩ := cut_pieces _ q b hq
    have h1 := sum_map_set cE P.loops ℓ w
      ((invW right a tl).take (q + 1) ++ [.lw (.proj P.nb)]) hw
    have hA : cE ((invW right a tl).take (q + 1) ++ [.lw (.proj P.nb)]) = cE X := by
      rw [htake]
      simp [cE, List.countP_append, PkgLetter.isEnt]
    have hB : cE (.lw (.proj P.nb) :: (invW right a tl).drop q) = cE Y := by
      rw [hdrop, cE_cons_lw, cE_cons_lw]
    have hWc : cE X + cE Y = cE tl := by
      rw [← hcW, hXY]
      simp [cE, List.countP_append, PkgLetter.isEnt]
    refine ⟨?_, ?_⟩
    · rw [hl, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · intro w' hw'
      rw [hl] at hw'
      rcases List.mem_append.1 hw' with h | h
      · rcases List.mem_or_eq_of_mem_set h with h | rfl
        · exact hgood w' h
        · intro u v hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hgW u v (List.mem_of_mem_take hu)
          · rw [List.mem_singleton] at hu
            cases hu
      · rw [List.mem_singleton] at h
        subst h
        intro u v hu
        rcases List.mem_cons.1 hu with hu | hu
        · cases hu
        · exact hgW u v (List.mem_of_mem_drop hu)
  · refine set_case _ hl ?_ ?_
    · rw [cE_append, hcW, hcw]
      simp [cE, PkgLetter.isEnt]
    · intro u v hu
      rcases List.mem_append.1 hu with hu | hu
      · exact hgW u v hu
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with hu | hu | hu | hu | hu <;> cases hu
  · have hfm : f ∈ P.loops := List.mem_of_getElem? hf
    have hcf : cE (f.rotate q) = cE f := by
      simpa [cE] using (List.rotate_perm f q).countP_eq PkgLetter.isEnt
    have h1 := sum_map_set cE P.loops ℓ w (invW right a tl ++ [.lw (.proj P.nb)] ++ f.rotate q ++
      [.lw (.res b), .lw (.proj P.nb)]) hw
    have hj : (P.loops.set ℓ (invW right a tl ++ [.lw (.proj P.nb)] ++ f.rotate q ++
        [.lw (.res b), .lw (.proj P.nb)]))[j]? = some f := by
      rw [List.getElem?_set_ne (Ne.symm hjℓ)]
      exact hf
    have h2 := sum_map_eraseIdx cE _ j f hj
    have hcM : cE (invW right a tl ++ [.lw (.proj P.nb)] ++ f.rotate q ++
        [.lw (.res b), .lw (.proj P.nb)]) = cE tl + cE f := by
      simp only [cE_append, hcW, hcf]
      simp [cE, PkgLetter.isEnt]
    refine ⟨by rw [hl]; omega, fun w' hw' => ?_⟩
    rw [hl] at hw'
    rcases List.mem_or_eq_of_mem_set (List.mem_of_mem_eraseIdx hw') with h | rfl
    · exact hgood w' h
    · intro u v hu
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
        List.mem_rotate] at hu
      rcases hu with ((hu | hu) | hu) | hu | hu
      · exact hgW u v hu
      · cases hu
      · exact hgood f hfm u v hu
      · cases hu
      · cases hu

/-- One derivative with label `(u, v) ∈ {(0, 1), (1, 0)}` adds one letter `Δ_{uv}`. -/
private theorem labK_dent (k : ℕ) (u v : ℕ) (huv : (u, v) = (0, 1) ∨ (u, v) = (1, 0))
    (R R' : PkgExpr) (hR : LabK k R) (h : R' ∈ R.dent u v) : LabK (k + 1) R' := by
  obtain ⟨hsum, hgood⟩ := hR
  rcases dent_cases R R' u v h with ⟨ℓ, X, Y, a, hℓ, hl⟩ | ⟨b, y, hl⟩
  · have h1 := sum_map_set cE R.loops ℓ (X ++ .lw (.res a) :: Y)
      (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
    have hc : cE (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y) =
        cE (X ++ .lw (.res a) :: Y) + 1 := by
      simp only [cE_append, cE_cons_lw, cE_ent, cE_nil]
      omega
    refine ⟨by rw [hl]; omega, fun w' hw' => ?_⟩
    rw [hl] at hw'
    rcases List.mem_or_eq_of_mem_set hw' with h | rfl
    · exact hgood w' h
    · intro u' v' hu
      have hold := hgood _ (List.mem_of_getElem? hℓ) u' v'
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hu hold
      rcases hu with (hu | (hu | hu | hu)) | hu
      · exact hold (Or.inl hu)
      · cases hu
      · obtain ⟨rfl, rfl⟩ := PkgLetter.ent.inj hu
        exact huv
      · cases hu
      · exact hold (Or.inr (Or.inr hu))
  · refine ⟨?_, fun w' hw' => ?_⟩
    · rw [hl, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, cE_cons_lw,
        cE_ent, cE_nil]
      omega
    · rw [hl] at hw'
      rcases List.mem_append.1 hw' with h | h
      · exact hgood w' h
      · rw [List.mem_singleton] at h
        subst h
        intro u' v' hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with hu | hu | hu | hu
        · cases hu
        · obtain ⟨rfl, rfl⟩ := PkgLetter.ent.inj hu
          exact huv
        · cases hu
        · cases hu

/-- `p` derivatives with labels in `{(0, 1), (1, 0)}` add `p` letters `Δ`. -/
private theorem labK_iter (u v : ℕ) (huv : (u, v) = (0, 1) ∨ (u, v) = (1, 0)) :
    ∀ (p k : ℕ) (L : List PkgExpr), (∀ R ∈ L, LabK k R) →
      ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[p] L, LabK (k + p) R
  | 0, k, L, hL, R, hR => hL R hR
  | p + 1, k, L, hL, R, hR => by
      rw [Function.iterate_succ_apply] at hR
      have := labK_iter u v huv p (k + 1) _ (fun R' hR' => by
        obtain ⟨R'', hR'', hd⟩ := List.mem_flatMap.1 hR'
        exact labK_dent k u v huv R'' R' (hL R'' hR'') hd) R hR
      rw [show k + (p + 1) = k + 1 + p by omega]
      exact this

/-- The start has one letter `Δ₁₀`. -/
private theorem labK_start (T : LoopExpr) {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (hf : T.focus = some (ℓ, a, tl)) : LabK 1 T.pkgStart := by
  rw [LabK, pkgStart_loops hf]
  refine ⟨?_, fun w' hw' => ?_⟩
  · simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, cE_append]
    have : ((T.loops.eraseIdx ℓ).map fun x => cE (x.map PkgLetter.lw)).sum = 0 := by
      rw [List.sum_eq_zero_iff]
      intro n hn
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hn
      exact cE_lw_map x
    rw [this, cE_lw_map]
    simp [cE, PkgLetter.isEnt]
  · intro u v hu
    rcases List.mem_cons.1 hw' with rfl | hw'
    · simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with ⟨x, -, hx⟩ | hu
      · cases hx
      · obtain ⟨rfl, rfl⟩ := PkgLetter.ent.inj hu
        exact Or.inr rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw'
      simp only [List.mem_map] at hu
      obtain ⟨y, -, hy⟩ := hu
      cases hy

/-- The derivative structures of the start with `p + q = 2` have three letters `Δ`, each with
label `(0, 1)` or `(1, 0)`. -/
private theorem labK_dwirt (T : LoopExpr) (p q : ℕ) (hpq : p + q = 2) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) : LabK 3 R := by
  obtain ⟨⟨ℓ, a, tl⟩, hfoc⟩ := Option.isSome_iff_exists.1 (focus_isSome T p q hpq R hR)
  have h0 := labK_start T hfoc
  unfold PkgExpr.dwirt at hR
  have h1 := labK_iter 1 0 (Or.inr rfl) q 1 [T.pkgStart] (fun R₂ hR₂ => by
    rw [List.mem_singleton.1 hR₂]; exact h0)
  have h2 := labK_iter 0 1 (Or.inl rfl) p (1 + q) _ h1 R hR
  rw [show 1 + q + p = 3 by omega] at h2
  exact h2

/-! ### Auxiliary facts: the counts `fR` and `fsig` -/

/-- `fR` as a function of the characters `(m, n, u, S)`. -/
private theorem fR_eq (R : PkgExpr) :
    R.fR = R.charsP.2.2.2 - R.charsP.1 + R.charsP.2.1 + 1 := by
  unfold PkgExpr.fR
  rcases R.charsP with ⟨m, n, u, S⟩
  rfl

/-- `fsig` as a function of the characters `(m, n, u, S)`. -/
private theorem fsig_eq (R : PkgExpr) :
    R.fsig = R.charsP.1 + R.charsP.2.2.1 +
      (R.charsP.2.2.2 - R.charsP.1 + R.charsP.2.1 + 1) - 4 := by
  unfold PkgExpr.fsig
  rw [fR_eq]

/-- `fdepth` as a function of the characters `(m, n, u, S)`. -/
private theorem fdepth_eq (R : PkgExpr) :
    R.fdepth = R.charsP.1 + R.charsP.2.2.1 + 2 * (R.charsP.2.2.2 - R.charsP.1 + R.charsP.2.1) := by
  unfold PkgExpr.fdepth
  rcases R.charsP with ⟨m, n, u, S⟩
  rfl

/-- `fsig + fR = fdepth - 2`: (5.86) [character_relation_further_expansion] and (5.87)
[character_relation_further_expansion2]. -/
private theorem fsig_add_fR (R : PkgExpr) : R.fsig + R.fR = R.fdepth - 2 := by
  rw [fsig_eq, fR_eq, fdepth_eq]
  omega

/-- One step of the further expansion does not lower `fR` and `fsig`: each row of Table 2
[table_effect_of_operations_2] raises `S - m + n` by `0` or `1` and `fsig` by `1` or `0`. -/
private theorem fR_step (S R' : PkgExpr) (h : R' ∈ S.fstep) : S.fR ≤ R'.fR ∧ S.fsig ≤ R'.fsig := by
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  have h2 := pkg_table2 S o R'' hmem
  change S.fR ≤ R''.fR ∧ S.fsig ≤ R''.fsig
  simp only [fR_eq, fsig_eq, h2, Prod.fst_add, Prod.snd_add]
  cases o <;> simp only [PkgOp.delta] <;> constructor <;> omega

/-! ### Auxiliary facts: the labels and the hypotheses of the invariants -/

/-- The number of entry labels of a word is its number of letters `Δ`. -/
private theorem length_entsOf (w : List PkgLetter) :
    (w.filterMap fun x => match x with | .ent u v => some (u, v) | _ => none).length = cE w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      cases x with
      | lw y => simpa [List.filterMap_cons, cE_cons_lw] using ih
      | ent u v => simp [cE_ent, ih]

/-- The number of entry labels of an expression is its number of letters `Δ`. -/
private theorem entLabels_length (R : PkgExpr) : R.entLabels.length = (R.loops.map cE).sum := by
  unfold PkgExpr.entLabels
  rw [List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun w _ => length_entsOf w)

/-- Every entry label of an expression is that of a letter `Δ` of one of its words. -/
private theorem entLabels_mem (R : PkgExpr) (x : ℕ × ℕ) (hx : x ∈ R.entLabels) :
    ∃ w ∈ R.loops, PkgLetter.ent x.1 x.2 ∈ w := by
  unfold PkgExpr.entLabels at hx
  obtain ⟨w, hw, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨y, hy, hxy⟩ := List.mem_filterMap.1 hx
  cases y with
  | lw z => simp at hxy
  | ent u v =>
      have : (u, v) = x := Option.some.inj hxy
      subst this
      exact ⟨w, hw, hy⟩

/-- `𝒯` is of the class `𝒯` of (5.33) [definition_class_of_expression_loop]. -/
private theorem reach_wf (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart]) :
    T.wf = true :=
  (loop_reach ε n T (Or.inr hT)).1

/-- `k₁ = 0` forces `R ≥ 1`, so `R = 0` forces `k₁ ≥ 1`: below (5.50)
[counting_character_of_term]. -/
private theorem reach_kk (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) : 1 ≤ T.kk 0 := by
  by_contra h
  have := (loop_reach ε n T (Or.inr hT)).2.2.1 (by omega)
  omega

/-- (C0) for the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
an expression reached or expanded from a derivative structure `𝓡₀` of `𝓡_𝒯(p₀, q₀)`,
`p₀ + q₀ = 2`, has exactly three letters `Δ`, each `Δ₀₁` or `Δ₁₀` (the six `⋆` of (5.79)
[further_expansion_expression_Type_1] are three `α` and three `β`). -/
theorem pkg_inv_lab (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    R.entLabels.length = 3 ∧ (∀ x ∈ R.entLabels, x = (0, 1) ∨ x = (1, 0)) ∧
      ∀ w ∈ R.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2 := by
  have h0 : LabK 3 R₀ := labK_dwirt T p₀ q₀ hpq R₀ hR₀
  obtain ⟨hsum, hgood⟩ := inv_reach (LabK 3) (fun S hS R' hR' => labK_step 3 S hS R' hR') ε j R₀
    R h0 hR
  refine ⟨by rw [entLabels_length, hsum], fun x hx => ?_, fun w hw u v hu => ?_⟩
  · obtain ⟨w, hw, hxw⟩ := entLabels_mem R x hx
    exact hgood w hw x.1 x.2 hxw
  · rcases hgood w hw u v hu with h | h <;> simp only [Prod.mk.injEq] at h <;> omega

/-- (C1) for the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
`Λ̃₁` lies in a heavy package, and that package has no resolvent and no `Λ̃₂` before `Λ̃₁`
(the form `(𝔐 B Λ̃₁ ⋯)_{⋆⋆}` of (5.79)–(5.81) [further_expansion_expression_Type_1]–
[further_expansion_expression_Type_3]). -/
theorem pkg_inv_lam1 (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    ∃ w ∈ R.loops, w.any PkgLetter.isEnt = true ∧ ∃ σ ∈ pkgSegs w,
      PkgLetter.lw (.lamt 0) ∈ σ ∧
      (σ.takeWhile fun x => x ≠ PkgLetter.lw (.lamt 0)).all
        (fun x => !x.isRes && !x.isLam) = true := by
  have hTw := reach_wf ε n T hT
  have hk := reach_kk ε n T hT hR0
  have h0 : ArcInv R₀ := arcInv_dwirt T hTw hk p₀ q₀ hpq R₀ hR₀
  obtain ⟨w, hw, harc⟩ := inv_reach ArcInv (fun S hS R' hR' => arcInv_step S hS R' hR') ε j R₀ R
    h0 hR
  obtain ⟨hany, σ, hσ, h2, h3⟩ := arcW_target w harc
  exact ⟨w, hw, hany, σ, hσ, h2, h3⟩

/-- (C3) for the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
(5.86) [character_relation_further_expansion] and (5.87)
[character_relation_further_expansion2] as counts: `fR ≥ 0`, `fR(𝓡₀) = 0`, the number of
operations other than `𝔣𝔯` is at least that of the first tree, `𝒯` lies in the first tree after
that many rounds, and `𝓡` in the further tree after `fR + Σ` rounds of its own. -/
theorem pkg_inv_counts (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    0 ≤ R.fR ∧ R₀.fR = 0 ∧ 0 ≤ R₀.fsig ∧ R₀.fsig ≤ R.fsig ∧ T ∈ loopTree R₀.fsig.toNat ∧
      R ∈ fTree (R.fsig + R.fR - R₀.fsig).toNat [R₀] := by
  have hTw := reach_wf ε n T hT
  have hfoc := focus_isSome T p₀ q₀ hpq R₀ hR₀
  obtain ⟨-, hrow⟩ := pkg_table3 T hTw hfoc p₀ q₀ hpq R₀ hR₀
  have hΔ : (R₀.charsP.1 - T.charsZ.1) + (R₀.charsP.2.2.1 - T.charsZ.2.2.1) = 2 ∧
      (R₀.charsP.2.2.2 - T.charsZ.2.2.2) - (R₀.charsP.1 - T.charsZ.1) +
        (R₀.charsP.2.1 - T.charsZ.2.1) = 0 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrow
    rcases hrow with h | h | h | h | h | h | h | h <;>
      (have e1 := congrArg Prod.fst h
       have e2 := congrArg (fun p => p.2.1) h
       have e3 := congrArg (fun p => p.2.2.1) h
       have e4 := congrArg (fun p => p.2.2.2) h
       simp at e1 e2 e3 e4
       omega)
  have hrc : T.rcount = T.charsZ.2.2.2 - T.charsZ.1 + T.charsZ.2.1 + 1 := by
    unfold LoopExpr.rcount
    rcases T.charsZ with ⟨m, n, u, S⟩
    rfl
  obtain ⟨R', C₁, C₂, P₁, P₂, hch⟩ := (loop_reach ε n T (Or.inr hT)).2.2.2
  have hc1 := congrArg Prod.fst hch
  have hc2 := congrArg (fun p => p.2.1) hch
  have hc3 := congrArg (fun p => p.2.2.1) hch
  have hc4 := congrArg (fun p => p.2.2.2) hch
  simp only at hc1 hc2 hc3 hc4
  have hfR0 : R₀.fR = 0 := by
    rw [fR_eq]
    omega
  have hsig0 : R₀.fsig = T.charsZ.1 + T.charsZ.2.2.1 + 2 * T.rcount - 2 := by
    rw [fsig_eq]
    omega
  have hge := inv_reach (fun S => R₀.fR ≤ S.fR ∧ R₀.fsig ≤ S.fsig)
    (fun S hS R' hR' => ⟨hS.1.trans (fR_step S R' hR').1, hS.2.trans (fR_step S R' hR').2⟩) ε j R₀
    R ⟨le_refl _, le_refl _⟩ hR
  have hfd := pkg_fdepth ε j R₀ R hR
  have e1 := fsig_add_fR R
  have e2 := fsig_add_fR R₀
  refine ⟨by omega, hfR0, by omega, hge.2, ?_, ?_⟩
  · rw [hsig0]
    exact loop_depth ε n T (Or.inr hT)
  · have : R.fsig + R.fR - R₀.fsig = R.fdepth - R₀.fdepth := by omega
    rw [this]
    exact hfd

/-- An expression of the class `𝓡` of (5.79)–(5.81) [further_expansion_expression_Type_1]–
[further_expansion_expression_Type_3] has a Type: `ptype ∈ {1, 2, 3}`. -/
theorem pkg_ptype_pos (R : PkgExpr) (hR : R.wf = true) : R.ptype ≠ 0 := by
  unfold PkgExpr.ptype
  have h1 : (R.loops.map fun w => w.count (.lw (.lamt 1))).sum = 1 := by
    unfold PkgExpr.wf at hR
    simp only [Bool.and_eq_true, beq_iff_eq] at hR
    exact hR.1.1.1.2
  rcases hfind : R.loops.find? (fun w => w.contains (.lw (.lamt 1))) with _ | w₂
  · exfalso
    have h2 := List.find?_eq_none.1 hfind
    have h3 : (R.loops.map fun w => w.count (.lw (.lamt 1))).sum = 0 := by
      rw [List.sum_eq_zero_iff]
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      have := h2 w hw
      rw [List.count_eq_zero]
      intro hmem
      exact this (by simpa using hmem)
    omega
  · simp only [hfind]
    split_ifs <;> decide

/-- (C2) for the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
every expression reached or expanded from a derivative structure `𝓡₀` of `𝓡_𝒯(p₀, q₀)`,
`p₀ + q₀ = 2`, is of the class `𝓡` of (5.79)–(5.81) [further_expansion_expression_Type_1]–
[further_expansion_expression_Type_3] (`wf`), as Table 2 [table_effect_of_operations_2] keeps it. -/
theorem pkg_inv_wf (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) : R.wf = true := by
  have hTw := reach_wf ε n T hT
  have hfoc := focus_isSome T p₀ q₀ hpq R₀ hR₀
  have h0 : R₀.wf = true := (pkg_table3 T hTw hfoc p₀ q₀ hpq R₀ hR₀).1
  exact inv_reach (fun S => S.wf = true) (fun S hS R' hR' => pkg_step_wf S hS R' hR') ε j R₀ R h0 hR

end RBMTransitionEdge

end
