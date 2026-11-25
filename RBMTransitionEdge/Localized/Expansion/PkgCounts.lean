module

public import RBMTransitionEdge.Localized.Expansion.Counts
public import RBMTransitionEdge.Localized.Expansion.PkgShape
public import RBMTransitionEdge.Localized.Expansion.PkgTerminate

@[expose] public section

/-!
# The further tree of the expansion in the proof of Lemma 5.5

The tree of the further expansion without the stopping rule, the depth of the expressions reached
(Table 2 [table_effect_of_operations_2], (5.86) [character_relation_further_expansion]), and (5.37)
[number_of_G_type_1] in the further expansion of the proof of Lemma 5.5
[claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The expressions after `j` steps of the further expansion without stopping rule. -/
def fTree : ℕ → List PkgExpr → List PkgExpr
  | 0, L => L
  | j + 1, L => fTree j (L.flatMap PkgExpr.fstep)

/-- `m + u + 2(S - m + n)`, with `(m, n, u, S)` the characters of Table 2
[table_effect_of_operations_2]: each of the eleven operations raises it by one. -/
def PkgExpr.fdepth (R : PkgExpr) : ℤ :=
  match R.charsP with
  | (m, n, u, S) => m + u + 2 * (S - m + n)

/-! ### Auxiliary facts: the further tree and its depth -/

private theorem fTree_flat (k : ℕ) :
    ∀ L : List PkgExpr, fTree k L = L.flatMap fun S => fTree k [S] := by
  induction k with
  | zero => intro L; simp [fTree]
  | succ k ih =>
    intro L
    have h1 : ∀ S : PkgExpr, fTree (k + 1) [S] = fTree k S.fstep := by
      intro S; simp [fTree]
    rw [show fTree (k + 1) L = fTree k (L.flatMap PkgExpr.fstep) from rfl,
      ih (L.flatMap PkgExpr.fstep), List.flatMap_assoc]
    refine List.flatMap_congr (fun S _ => ?_)
    rw [h1, ih S.fstep]

private theorem mem_fTree (k : ℕ) (L : List PkgExpr) (R : PkgExpr) :
    R ∈ fTree k L ↔ ∃ S ∈ L, R ∈ fTree k [S] := by
  rw [fTree_flat, List.mem_flatMap]

private theorem fTree_succ_single (k : ℕ) (S : PkgExpr) : fTree (k + 1) [S] = fTree k S.fstep := by
  simp [fTree]

/-- Every term of one step raises `fdepth` by one: Table 2 [table_effect_of_operations_2]. -/
private theorem fdepth_fterms (R : PkgExpr) (o : PkgOp) (R' : PkgExpr)
    (h : (o, R') ∈ R.fterms) : R'.fdepth = R.fdepth + 1 := by
  have h2 := pkg_table2 R o R' h
  unfold PkgExpr.fdepth
  rw [h2]
  rcases hR : R.charsP with ⟨m, n, u, S⟩
  cases o <;> simp only [PkgOp.delta] <;> ring

private theorem fdepth_fstep (R R' : PkgExpr) (h : R' ∈ R.fstep) : R'.fdepth = R.fdepth + 1 := by
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  exact fdepth_fterms R o R'' hmem

private theorem fTree_fdepth : ∀ (k : ℕ) (R₁ R : PkgExpr), R ∈ fTree k [R₁] →
    R.fdepth = R₁.fdepth + k
  | 0, R₁, R, h => by
      simp only [fTree, List.mem_singleton] at h
      subst h; simp
  | k + 1, R₁, R, h => by
      rw [fTree_succ_single, mem_fTree] at h
      obtain ⟨S, hS, hR⟩ := h
      have := fTree_fdepth k S R hR
      have h2 := fdepth_fstep R₁ S hS
      push_cast
      omega

/-! ### Auxiliary facts: the rounds of the further expansion -/

/-- One round of the further expansion. -/
private def fRound (ε : ℝ) (L : List PkgExpr) : List PkgExpr :=
  L.flatMap fun R => if R.FStopped ε then [R] else R.fstep

private theorem mem_fRound (ε : ℝ) (L : List PkgExpr) (R : PkgExpr) (h : R ∈ fRound ε L) :
    ∃ S ∈ L, R = S ∨ (¬ S.FStopped ε ∧ R ∈ S.fstep) := by
  obtain ⟨S, hS, hR⟩ := List.mem_flatMap.1 h
  refine ⟨S, hS, ?_⟩
  by_cases hs : S.FStopped ε
  · simp only [hs, ↓reduceIte] at hR
    exact Or.inl (List.mem_singleton.1 hR)
  · simp only [hs, ↓reduceIte] at hR
    exact Or.inr ⟨hs, hR⟩

private theorem fInner_succ (ε : ℝ) (n : ℕ) (L : List PkgExpr) :
    fInner ε (n + 1) L = L.filter (fun R => decide (¬ R.FStopped ε)) ++
      fInner ε n (fRound ε L) := rfl

/-- The expressions reached or expanded in `n` rounds from the list `L`. -/
private theorem rounds_cases (ε : ℝ) (n : ℕ) (L : List PkgExpr) (R : PkgExpr)
    (h : R ∈ fIter ε (n + 1) L ∨ R ∈ fInner ε (n + 1) L) :
    (R ∈ L) ∨ (R ∈ fIter ε n (fRound ε L) ∨ R ∈ fInner ε n (fRound ε L)) := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · rw [fInner_succ, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (List.mem_of_mem_filter h)
    · exact Or.inr (Or.inr h)

private theorem fdepth_gen (ε : ℝ) : ∀ (n : ℕ) (L : List PkgExpr) (R : PkgExpr),
    (R ∈ fIter ε n L ∨ R ∈ fInner ε n L) →
      ∃ R₀ ∈ L, R ∈ fTree (R.fdepth - R₀.fdepth).toNat [R₀]
  | 0, L, R, h => by
      rcases h with h | h
      · exact ⟨R, h, by simp [fTree]⟩
      · simp [fInner] at h
  | n + 1, L, R, h => by
      rcases rounds_cases ε n L R h with h | h
      · exact ⟨R, h, by simp [fTree]⟩
      · obtain ⟨R₁, hR₁, hmem⟩ := fdepth_gen ε n (fRound ε L) R h
        obtain ⟨S, hS, h | ⟨-, hR₁S⟩⟩ := mem_fRound ε L R₁ hR₁
        · subst h; exact ⟨R₁, hS, hmem⟩
        · refine ⟨S, hS, ?_⟩
          have hd := fdepth_fstep S R₁ hR₁S
          have hF := fTree_fdepth _ R₁ R hmem
          have hk : (R.fdepth - S.fdepth).toNat = (R.fdepth - R₁.fdepth).toNat + 1 := by omega
          rw [hk, fTree_succ_single, mem_fTree]
          exact ⟨R₁, hR₁S, hmem⟩

/-- Every expression reached or expanded by the further expansion of `𝓡₀` lies in the further
tree without stopping rule after `fdepth 𝓡 - fdepth 𝓡₀` steps, by Table 2
[table_effect_of_operations_2] and (5.86) [character_relation_further_expansion]. -/
theorem pkg_fdepth (ε : ℝ) (j : ℕ) (R₀ R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    R ∈ fTree (R.fdepth - R₀.fdepth).toNat [R₀] := by
  obtain ⟨S, hS, h⟩ := fdepth_gen ε j [R₀] R hR
  rw [List.mem_singleton.1 hS] at h
  exact h

/-! ### Auxiliary facts: the word of the cut in the rules (i)–(iv) of the further expansion -/

/-- The search of `takeWhile` and `find?` along `f 0, f 1, …` returns some `f k`: `P` holds on
`f 0, …, f k` and `Q` fails on `f 0, …, f (k - 1)`. -/
private theorem seek_aux2 (P Q : ℕ → Bool) (r : ℕ) : ∀ (n : ℕ) (f : ℕ → ℕ),
    (((List.range n).map f).takeWhile P).find? Q = some r →
      ∃ k < n, r = f k ∧ (∀ j ≤ k, P (f j) = true) ∧ Q (f k) = true ∧ ∀ j < k, Q (f j) = false
  | 0, f, h => by simp at h
  | n + 1, f, h => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.takeWhile_cons] at h
      by_cases hP : P (f 0) = true
      · simp only [hP, ↓reduceIte] at h
        rw [List.find?_cons] at h
        cases hQ : Q (f 0)
        · rw [hQ] at h
          obtain ⟨k, hk, hr, hPk, hQk, hQj⟩ := seek_aux2 P Q r n (f ∘ Nat.succ) h
          refine ⟨k + 1, by omega, hr, ?_, hQk, ?_⟩
          · intro j hj
            cases j with
            | zero => exact hP
            | succ j => exact hPk j (by omega)
          · intro j hj
            cases j with
            | zero => exact hQ
            | succ j => exact hQj j (by omega)
        · rw [hQ] at h
          have := Option.some.inj h
          subst this
          refine ⟨0, by omega, rfl, ?_, hQ, fun j hj => absurd hj (by omega)⟩
          intro j hj
          have : j = 0 := by omega
          subst this
          exact hP
      · simp [hP] at h
  
/-- The positions searched by `pkgSeek`. -/
private def seekPos2 (len i : ℕ) (right : Bool) (j : ℕ) : ℕ :=
  if right then (i + 1 + j) % len else (i + len - 1 - j) % len

private theorem res_false_of_match (z : PkgLetter)
    (h : (match some z with | some (PkgLetter.lw (LoopLetter.res _)) => true | _ => false) =
      false) :
    z.isRes = false := by
  cases z with
  | ent u v => rfl
  | lw x => cases x <;> first | rfl | simp at h

private theorem pkgSeek_pos2 (w : List PkgLetter) (i r : ℕ) (right : Bool)
    (h : pkgSeek w i right = some r) :
    ∃ k, k + 1 < w.length ∧ r = seekPos2 w.length i right k ∧
      (∀ j < k, ∃ z, w[seekPos2 w.length i right j]? = some z ∧ z.isRes = false) ∧
      ∃ b, w[r]? = some (.lw (.res b)) := by
  have h' : (((List.range (w.length - 1)).map (seekPos2 w.length i right)).takeWhile
      fun r => match w[r]? with
        | some (PkgLetter.ent _ _) => false | some (PkgLetter.lw (LoopLetter.lamt _)) => false
        | _ => true).find? (fun r =>
      match w[r]? with | some (PkgLetter.lw (LoopLetter.res _)) => true | _ => false) = some r := h
  obtain ⟨k, hk, hr, -, hQ, hQj⟩ := seek_aux2 _ _ r _ _ h'
  have hlen : 0 < w.length := by omega
  have hmem : ∀ j, w[seekPos2 w.length i right j]? ≠ none := by
    intro j
    have : seekPos2 w.length i right j < w.length := by
      unfold seekPos2
      split <;> exact Nat.mod_lt _ hlen
    rw [List.getElem?_eq_getElem this]
    simp
  refine ⟨k, by omega, hr, ?_, ?_⟩
  · intro j hj
    have hQj' := hQj j hj
    rcases hz : w[seekPos2 w.length i right j]? with _ | z
    · exact absurd hz (hmem j)
    · refine ⟨z, rfl, ?_⟩
      rw [hz] at hQj'
      exact res_false_of_match z hQj'
  · rw [hr]
    revert hQ
    rcases hz : w[seekPos2 w.length i right k]? with _ | z
    · simp
    · intro hQ
      match z, hQ with
      | .lw (.res b), _ => exact ⟨b, rfl⟩
      | .ent _ _, hQ => exact absurd hQ (by simp)
      | .lw (.det _), hQ => exact absurd hQ (by simp)
      | .lw (.proj _), hQ => exact absurd hQ (by simp)
      | .lw (.lamt _), hQ => exact absurd hQ (by simp)

/-- The letters of the rotated word `𝒢_a tl` after and before the letter `Λ̃` from which the rules
(i)–(iv) search: no resolvent lies after it (`right`) or before it (`left`). -/
private theorem seek_tl2 (w : List PkgLetter) (i r : ℕ) (right : Bool) (g : PkgLetter)
    (hg : w[i]? = some g) (h : pkgSeek w i right = some r) (a : Fin 2) (tl : List PkgLetter)
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    (right = true → ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₂, z.isRes = false) ∧
    (right = false → ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₁, z.isRes = false) := by
  obtain ⟨k, hk, hr, hfree, b, hb⟩ := pkgSeek_pos2 w i r right h
  have hi : i < w.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen : 0 < w.length := by omega
  have hulen : (w.rotate i).length = w.length := List.length_rotate _ _
  have hu : ∀ m, m < w.length → (w.rotate i)[m]? = w[(m + i) % w.length]? := fun m hm =>
    List.getElem?_rotate hm
  have hu0 : (w.rotate i)[0]? = some g := by
    rw [hu 0 hlen, zero_add, Nat.mod_eq_of_lt hi]
    exact hg
  obtain ⟨T', hT'⟩ : ∃ T', w.rotate i = g :: T' := by
    rcases hrot0 : w.rotate i with _ | ⟨x, T'⟩
    · rw [hrot0] at hu0
      simp at hu0
    · rw [hrot0, List.getElem?_cons_zero, Option.some.injEq] at hu0
      subst hu0
      exact ⟨T', rfl⟩
  constructor
  · rintro rfl
    have e1 : r = (i + 1 + k) % w.length := by simpa [seekPos2] using hr
    have hrr : w.rotate r = (w.rotate i).rotate (k + 1) := by
      rw [e1, List.rotate_mod, List.rotate_rotate]
      congr 1
      omega
    have hposk : (w.rotate i)[k + 1]? = some (.lw (.res b)) := by
      rw [hu _ (by omega)]
      have : (k + 1 + i) % w.length = r := by rw [e1]; congr 1; omega
      rw [this]
      exact hb
    rw [hrr, List.rotate_eq_drop_append_take (by omega)] at hrot
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hposk
    rw [List.drop_eq_getElem_cons hlt, hget, hT'] at hrot
    have hcons := List.cons.inj hrot
    refine ⟨(w.rotate i).drop (k + 1 + 1), T'.take k, ?_, ?_⟩
    · rw [← hcons.2, hT']
      simp
    · intro z hz
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hz
      rw [List.getElem?_take] at hn
      split at hn
      · rename_i hnk
        have hzu : (w.rotate i)[n + 1]? = some z := by rw [hT']; simpa using hn
        rw [hu _ (by omega)] at hzu
        obtain ⟨z', hz', hz'e⟩ := hfree n (by omega)
        have e2 : (n + 1 + i) % w.length = seekPos2 w.length i true n := by
          simp only [seekPos2, ite_true]; congr 1; omega
        rw [e2, hz'] at hzu
        cases hzu
        exact hz'e
      · simp at hn
  · rintro rfl
    have e1 : r = (i + w.length - 1 - k) % w.length := by simpa [seekPos2] using hr
    set c := w.length - 1 - k with hc
    have hrr : w.rotate r = (w.rotate i).rotate c := by
      rw [e1, List.rotate_mod, List.rotate_rotate]
      congr 1
      omega
    have hposk : (w.rotate i)[c]? = some (.lw (.res b)) := by
      rw [hu _ (by omega)]
      have : (c + i) % w.length = r := by rw [e1]; congr 1; omega
      rw [this]
      exact hb
    rw [hrr, List.rotate_eq_drop_append_take (by omega)] at hrot
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hposk
    rw [List.drop_eq_getElem_cons hlt, hget] at hrot
    have hcons := List.cons.inj hrot
    obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    refine ⟨(w.rotate i).drop (c + 1), T'.take c', ?_, ?_⟩
    · rw [← hcons.2, hT', hc']
      simp
    · intro z hz
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hz
      rw [List.getElem?_drop] at hn
      have hn' : c + 1 + n < w.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hn
        cases hn
      obtain ⟨z', hz', hz'e⟩ := hfree (k - 1 - n) (by omega)
      have e2 : (c + 1 + n + i) % w.length = seekPos2 w.length i false (k - 1 - n) := by
        simp only [seekPos2, Bool.false_eq_true, ite_false]; congr 1; omega
      rw [hu _ hn', e2, hz'] at hn
      cases hn
      exact hz'e

private theorem fc_findIdx_mem {α : Type*} (l : List α) (p : α → Bool) (x : α)
    (h : l[l.findIdx p]? = some x) : p x = true := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  have := List.findIdx_getElem (p := p) (xs := l) (w := hlt)
  rwa [hget] at this

private theorem fc_contains_idx (w : List PkgLetter) (x : PkgLetter) (h : w.contains x = true) :
    w[w.idxOf x]? = some x := by
  have hm : x ∈ w := List.contains_iff_mem.1 h
  have hlt : w.idxOf x < w.length := List.idxOf_lt_length_iff.2 hm
  rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]

private theorem fc_some_inj3 {ℓ ℓ' r r' : ℕ} {s s' : Bool}
    (h : some (ℓ', r', s') = some (ℓ, r, s)) : ℓ' = ℓ ∧ r' = r ∧ s' = s := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨h3, h4⟩ := Prod.mk.inj h2
  exact ⟨h1, h3, h4⟩

/-- The expanded word of `ffocus` contains a `Λ̃`, from which `pkgSeek` searches. -/
private theorem fc_ffocus_data (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (w : List PkgLetter)
    (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w) :
    ∃ i o, w[i]? = some (.lw (.lamt o)) ∧ pkgSeek w i right = some r := by
  unfold PkgExpr.ffocus at hf
  dsimp only at hf
  split at hf
  · rename_i w₂ w₁ h₂ h₁
    have c₂ : w₂.contains (.lw (.lamt 1)) = true :=
      fc_findIdx_mem R.loops (fun w => w.contains (.lw (.lamt 1))) w₂ h₂
    have c₁ : w₁.contains (.lw (.lamt 0)) = true :=
      fc_findIdx_mem R.loops (fun w => w.contains (.lw (.lamt 0))) w₁ h₁
    split at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
        rw [h₂] at hw
        cases hw
        exact ⟨_, 1, fc_contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
          rw [h₁] at hw
          cases hw
          exact ⟨_, 0, fc_contains_idx _ _ c₁, hr'⟩
        · split at hf
          · rename_i r' hr'
            obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
            rw [h₂] at hw
            cases hw
            exact ⟨_, 1, fc_contains_idx _ _ c₂, hr'⟩
          · simp at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
        rw [h₂] at hw
        cases hw
        exact ⟨_, 1, fc_contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
          rw [h₁] at hw
          cases hw
          exact ⟨_, 0, fc_contains_idx _ _ c₁, hr'⟩
        · simp at hf
  · simp at hf

/-- The word `𝒢_a tl` of the rotation of the expanded word has a letter `Λ̃` in `tl`, with no
resolvent after it when the resolvent lies to its right, and none before it when it lies to its
left. -/
private theorem focus_shape (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (w : List PkgLetter)
    (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w) (a : Fin 2)
    (tl : List PkgLetter) (hrot : w.rotate r = .lw (.res a) :: tl) :
    ∃ (L₁ L₂ : List PkgLetter) (g : PkgLetter), g.isLam = true ∧ tl = L₁ ++ g :: L₂ ∧
      (right = true → ∀ z ∈ L₂, z.isRes = false) ∧
      (right = false → ∀ z ∈ L₁, z.isRes = false) := by
  obtain ⟨i, o, hi, hs⟩ := fc_ffocus_data R ℓ r right w hf hw
  obtain ⟨h1, h2⟩ := seek_tl2 w i r right _ hi hs a tl hrot
  cases right
  · obtain ⟨L₁, L₂, hL, hres⟩ := h2 rfl
    exact ⟨L₁, L₂, _, rfl, hL, fun h => absurd h (by simp), fun _ => hres⟩
  · obtain ⟨L₁, L₂, hL, hres⟩ := h1 rfl
    exact ⟨L₁, L₂, _, rfl, hL, fun _ => hres, fun h => absurd h (by simp)⟩

/-- The loop word `v` (of a loop `⟨·⟩` if it has no `Δ`) with a letter `Δ` or `Λ̃`, or with at
least two resolvents: the statement of (5.37) [number_of_G_type_1] for one word. -/
private def Free2 (v : List PkgLetter) : Prop :=
  v.any PkgLetter.isEnt = false → v.any PkgLetter.isLam = false → 2 ≤ v.countP PkgLetter.isRes

/-- Every word of the expression satisfies `Free2`. -/
private def FreeInv (R : PkgExpr) : Prop := ∀ w ∈ R.loops, Free2 w

private theorem free2_of_lam (v : List PkgLetter) (g : PkgLetter) (hg : g ∈ v)
    (hl : g.isLam = true) : Free2 v := by
  intro _ h
  have : v.any PkgLetter.isLam = true := List.any_eq_true.2 ⟨g, hg, hl⟩
  rw [this] at h
  exact absurd h (by simp)

private theorem free2_of_two (v : List PkgLetter) (h : 2 ≤ v.countP PkgLetter.isRes) :
    Free2 v := fun _ _ => h

/-- Two resolvents at distinct places of a word. -/
private theorem two_of_idx (l : List PkgLetter) (s t : ℕ) (x y : PkgLetter)
    (hs : l[s]? = some x) (hx : x.isRes = true) (ht : l[t]? = some y) (hy : y.isRes = true)
    (hst : s < t) : 2 ≤ l.countP PkgLetter.isRes := by
  have h1 : 0 < (l.take t).countP PkgLetter.isRes := by
    rw [List.countP_pos_iff]
    refine ⟨x, List.mem_of_getElem? (i := s) ?_, hx⟩
    rw [List.getElem?_take_of_lt hst]
    exact hs
  have h2 : 0 < (l.drop t).countP PkgLetter.isRes := by
    rw [List.countP_pos_iff]
    refine ⟨y, List.mem_of_getElem? (i := 0) ?_, hy⟩
    rw [List.getElem?_drop, Nat.add_zero]
    exact ht
  have h3 := List.countP_append (p := PkgLetter.isRes) (l₁ := l.take t) (l₂ := l.drop t)
  rw [List.take_append_drop] at h3
  omega

/-- The word of the expanded loop in the terms of `fterms`: `𝒢_a tl` closed by `𝔐_a` (resolvent
to the right) or by `𝒢_a` (resolvent to the left). -/
private def wordWc (right : Bool) (a : Fin 2) (tl : List PkgLetter) : List PkgLetter :=
  if right then .lw (.res a) :: tl ++ [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]

/-- The cut at a resolvent `q` of the word `W` of `fterms`: the two words of the cut. Right case:
the word `A` has the resolvents at `0` and `q`; the word `B` contains the `Λ̃`. Left case: the
word `B` has the resolvents at `q` and at the last place; the word `A` contains the `Λ̃`. -/
private theorem cut_free (right : Bool) (a : Fin 2) (L₁ L₂ : List PkgLetter) (g px : PkgLetter)
    (hg : g.isLam = true)
    (hR : right = true → ∀ z ∈ L₂, z.isRes = false)
    (hL : right = false → ∀ z ∈ L₁, z.isRes = false)
    (q : ℕ) (b : Fin 2) (hq : (wordWc right a (L₁ ++ g :: L₂))[q]? = some (.lw (.res b)))
    (hne : ¬ ((right && q == 0) || (!right && q + 1 == (wordWc right a (L₁ ++ g :: L₂)).length))) :
    Free2 ((wordWc right a (L₁ ++ g :: L₂)).take (q + 1) ++ [px]) ∧
      Free2 (px :: (wordWc right a (L₁ ++ g :: L₂)).drop q) := by
  have hglam : g.isRes = false := by
    cases g with
    | ent u v => rfl
    | lw x => cases x <;> first | rfl | simp [PkgLetter.isLam] at hg
  cases right
  · -- the resolvent lies to the left
    have hres := hL rfl
    set W := wordWc false a (L₁ ++ g :: L₂) with hWdef
    have hW : W = (.lw (.det a) :: L₁) ++ g :: (L₂ ++ [.lw (.res a)]) := by
      simp [hWdef, wordWc]
    have hW' : W = (.lw (.det a) :: (L₁ ++ g :: L₂)) ++ [.lw (.res a)] := by
      simp [hWdef, wordWc]
    have hlt : q < W.length := (List.getElem?_eq_some_iff.1 hq).1
    have hWlen : W.length = (L₁ ++ g :: L₂).length + 2 := by
      rw [hW']; simp; omega
    have hne' : q + 1 ≠ W.length := by
      intro h
      apply hne
      simp [h]
    have hpre : (L₁.length + 1) ≤ q := by
      by_contra hlt'
      have hq' : q < ((.lw (.det a) :: L₁) : List PkgLetter).length := by simp; omega
      rw [hW, List.getElem?_append_left hq'] at hq
      have hm := List.mem_of_getElem? hq
      rcases List.mem_cons.1 hm with h | h
      · cases h
      · have := hres _ h
        simp [PkgLetter.isRes] at this
    constructor
    · refine free2_of_lam _ g ?_ hg
      refine List.mem_append_left _ (List.mem_of_getElem? (i := L₁.length + 1) ?_)
      rw [List.getElem?_take_of_lt (by omega), hW, List.getElem?_append_right (by simp)]
      simp
    · refine free2_of_two _ ?_
      have hY : q < (L₁ ++ g :: L₂).length + 1 := by omega
      refine two_of_idx _ 1 ((L₁ ++ g :: L₂).length + 1 - q + 1) (.lw (.res b)) (.lw (.res a))
        ?_ rfl ?_ rfl (by omega)
      · simpa [List.getElem?_drop] using hq
      · simp only [List.getElem?_cons_succ, List.getElem?_drop]
        have : q + ((L₁ ++ g :: L₂).length + 1 - q) = (L₁ ++ g :: L₂).length + 1 := by omega
        rw [this, hW']
        simp
  · -- the resolvent lies to the right
    have hres := hR rfl
    set W := wordWc true a (L₁ ++ g :: L₂) with hWdef
    have hW : W = (.lw (.res a) :: L₁) ++ g :: (L₂ ++ [.lw (.det a)]) := by
      simp [hWdef, wordWc]
    have hlt : q < W.length := (List.getElem?_eq_some_iff.1 hq).1
    have hq0 : q ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hW0 : W[0]? = some (.lw (.res a)) := by
      rw [hW]; simp
    have hpre : q < L₁.length + 1 := by
      by_contra hlt'
      rw [hW, List.getElem?_append_right (by simp; omega)] at hq
      obtain ⟨j, hj⟩ : ∃ j, q - ((.lw (.res a) :: L₁ : List PkgLetter).length) = j := ⟨_, rfl⟩
      rw [hj] at hq
      cases j with
      | zero =>
        have hq' : g = .lw (.res b) := by simpa using hq
        rw [hq'] at hglam
        simp [PkgLetter.isRes] at hglam
      | succ j =>
        simp only [List.getElem?_cons_succ] at hq
        have hm := List.mem_of_getElem? hq
        rcases List.mem_append.1 hm with h | h
        · have := hres _ h
          simp [PkgLetter.isRes] at this
        · simp at h
    constructor
    · refine free2_of_two _ (two_of_idx _ 0 q (.lw (.res a)) (.lw (.res b)) ?_ rfl ?_ rfl
        (by omega))
      · rw [List.getElem?_append_left (by rw [List.length_take]; omega),
          List.getElem?_take_of_lt (by omega)]
        exact hW0
      · rw [List.getElem?_append_left (by rw [List.length_take]; omega),
          List.getElem?_take_of_lt (by omega)]
        exact hq
    · refine free2_of_lam _ g (List.mem_cons_of_mem _ (List.mem_of_getElem?
        (i := L₁.length + 1 - q) ?_)) hg
      rw [List.getElem?_drop, show q + (L₁.length + 1 - q) = L₁.length + 1 by omega, hW,
        List.getElem?_append_right (by simp)]
      simp
/-! ### Auxiliary facts: one step of the further expansion keeps the loops with two resolvents -/

private theorem freeInv_set (R : PkgExpr) (hR : FreeInv R) (ℓ : ℕ) (N : List PkgLetter)
    (hN : Free2 N) : ∀ w' ∈ R.loops.set ℓ N, Free2 w' := by
  intro w' hw'
  rcases List.mem_or_eq_of_mem_set hw' with h | h
  · exact hR w' h
  · rw [h]; exact hN

/-- One step of the further expansion: the terms of `fterms` keep the property (5.37)
[number_of_G_type_1] of the words without `Δ` and without `Λ̃`: the word that is changed contains
the `Λ̃` of the expanded word, except for the two words of a cut at a resolvent, where the word
without `Λ̃` has two resolvents (the rules (i)–(iv) choose the resolvent next to the `Λ̃`). -/
private theorem fterms_free (P : PkgExpr) (hP : FreeInv P) (o : PkgOp) (R' : PkgExpr)
    (h : (o, R') ∈ P.fterms) : FreeInv R' := by
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
            else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)]) = wordWc right a tl := rfl
        rw [hWdef] at h
        obtain ⟨L₁, L₂, g, hg, rfl, hR, hL⟩ := focus_shape P ℓ r right w hf hw a tl hrot
        have hgW : g ∈ wordWc right a (L₁ ++ g :: L₂) := by
          cases right <;> simp [wordWc]
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with h | h
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                exact freeInv_set P hP ℓ _ (free2_of_lam _ g (by simp) hg)
              · rcases List.mem_cons.1 h with h | h
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                  refine freeInv_set P hP ℓ _ (free2_of_lam _ g ?_ hg)
                  cases right <;> simp [wordWc] at hgW ⊢
                · simp at h
            · -- cut at another resolvent of the expanded word
              obtain ⟨q, hq1, hq⟩ := List.mem_filterMap.1 h
              split at hq
              · simp at hq
              · rename_i hne
                split at hq
                · rename_i b hqb
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  obtain ⟨hA, hB⟩ := cut_free right a L₁ L₂ g (.lw (.proj P.nb)) hg hR hL q b
                    (by simpa [wordWc] using hqb) (by simpa [wordWc] using hne)
                  intro w' hw'
                  change w' ∈ P.loops.set ℓ _ ++ [_] at hw'
                  rcases List.mem_append.1 hw' with h' | h'
                  · exact freeInv_set P hP ℓ _ (by simpa [wordWc] using hA) w' h'
                  · rw [List.mem_singleton.1 h']
                    simpa [wordWc] using hB
                · simp at hq
          · -- plug of a light weight
            obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
            split at hj
            · rename_i b y hjb
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
              refine freeInv_set P hP ℓ _ (free2_of_lam _ g ?_ hg)
              simp [hgW]
            · simp at hj
        · -- join with a resolvent of another word
          obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
          split at hj
          · simp at hj
          · rename_i hjℓ
            split at hj
            · simp at hj
            · rename_i f hf'
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · rename_i b hqb
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                intro w' hw'
                change w' ∈ (P.loops.set ℓ _).eraseIdx j at hw'
                exact freeInv_set P hP ℓ _ (free2_of_lam _ g (by simp [hgW]) hg) w'
                  (List.mem_of_mem_eraseIdx hw')
              · simp at hq
      · simp at h

private theorem fstep_free (P : PkgExpr) (hP : FreeInv P) (R' : PkgExpr) (h : R' ∈ P.fstep) :
    FreeInv R' := by
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  exact fterms_free P hP o R'' hmem

private theorem ffree_gen (ε : ℝ) : ∀ (n : ℕ) (L : List PkgExpr), (∀ S ∈ L, FreeInv S) →
    ∀ R : PkgExpr, (R ∈ fIter ε n L ∨ R ∈ fInner ε n L) → FreeInv R
  | 0, L, hL, R, h => by
      rcases h with h | h
      · exact hL R h
      · simp [fInner] at h
  | n + 1, L, hL, R, h => by
      rcases rounds_cases ε n L R h with h | h
      · exact hL R h
      · refine ffree_gen ε n (fRound ε L) (fun S' hS' => ?_) R h
        obtain ⟨S, hS, h | ⟨-, hR⟩⟩ := mem_fRound ε L S' hS'
        · rw [h]; exact hL S hS
        · exact fstep_free S (hL S hS) S' hR

/-! ### Auxiliary facts: the loops of the derivative structures -/

/-- The words without `Δ` of the expression are loops of `T`. -/
private def OnlyLoops (T : LoopExpr) (R : PkgExpr) : Prop :=
  ∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → ∃ v ∈ T.loops, w = v.map PkgLetter.lw

private theorem onlyLoops_start (T : LoopExpr) : OnlyLoops T T.pkgStart := by
  intro w hw hent
  unfold LoopExpr.pkgStart at hw
  split at hw
  · simp at hw
  · rename_i ℓ a tl hfoc
    rcases List.mem_cons.1 hw with rfl | hw
    · simp [PkgLetter.isEnt] at hent
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      exact ⟨v, List.mem_of_mem_eraseIdx hv, rfl⟩

private theorem onlyLoops_dent (T : LoopExpr) (R : PkgExpr) (u v : ℕ) (hR : OnlyLoops T R)
    (R' : PkgExpr) (h : R' ∈ R.dent u v) : OnlyLoops T R' := by
  unfold PkgExpr.dent at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨ℓ, -, h⟩ := List.mem_flatMap.1 h
    split at h
    · simp at h
    · rename_i w hw
      obtain ⟨r, -, h⟩ := List.mem_filterMap.1 h
      split at h
      · rename_i a hra
        obtain rfl := Option.some.inj h
        intro w' hw' hent
        change w' ∈ R.loops.set ℓ _ at hw'
        rcases List.mem_or_eq_of_mem_set hw' with h' | h'
        · exact hR w' h' hent
        · subst h'
          simp [PkgLetter.isEnt] at hent
      · simp at h
  · obtain ⟨j, -, h⟩ := List.mem_filterMap.1 h
    split at h
    · rename_i b y hj
      obtain rfl := Option.some.inj h
      intro w' hw' hent
      change w' ∈ R.loops ++ _ at hw'
      rcases List.mem_append.1 hw' with h' | h'
      · exact hR w' h' hent
      · rw [List.mem_singleton] at h'
        subst h'
        simp [PkgLetter.isEnt] at hent
    · simp at h

private theorem onlyLoops_iter (T : LoopExpr) (u v : ℕ) : ∀ (p : ℕ) (L : List PkgExpr),
    (∀ R ∈ L, OnlyLoops T R) →
    ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[p] L, OnlyLoops T R
  | 0, L, hL, R, hR => hL R hR
  | p + 1, L, hL, R, hR => by
      rw [Function.iterate_succ_apply] at hR
      refine onlyLoops_iter T u v p _ ?_ R hR
      intro R' hR'
      obtain ⟨R'', hR'', hd⟩ := List.mem_flatMap.1 hR'
      exact onlyLoops_dent T R'' u v (hL R'' hR'') R' hd

private theorem onlyLoops_dwirt (T : LoopExpr) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) : OnlyLoops T R := by
  unfold PkgExpr.dwirt at hR
  refine onlyLoops_iter T 0 1 p _ (fun R₁ hR₁ => ?_) R hR
  refine onlyLoops_iter T 1 0 q [T.pkgStart] ?_ R₁ hR₁
  intro R₂ hR₂
  rw [List.mem_singleton.1 hR₂]
  exact onlyLoops_start T

private theorem countP_lw_isRes (v : List LoopLetter) :
    (v.map PkgLetter.lw).countP PkgLetter.isRes =
      v.countP fun x => match x with | .res _ => true | _ => false := by
  rw [List.countP_map]
  congr 1
  funext x
  cases x <;> rfl

/-- The loops of `T` lead to words with two resolvents: (5.37) [number_of_G_type_1] at the start of
the further expansion. -/
private theorem free_base (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (p q : ℕ) (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) : FreeInv R := by
  intro w hw hent hlam
  obtain ⟨v, hv, rfl⟩ := onlyLoops_dwirt T p q R hR w hw hent
  have hc : ∀ x : LoopLetter, (∃ k, x = .lamt k) → x ∉ v := by
    rintro x ⟨k, rfl⟩ hx
    have : (v.map PkgLetter.lw).any PkgLetter.isLam = true :=
      List.any_eq_true.2 ⟨.lw (.lamt k), List.mem_map.2 ⟨_, hx, rfl⟩, rfl⟩
    rw [this] at hlam
    exact absurd hlam (by simp)
  have h0 : v.contains (.lamt 0) = false := by
    by_contra hcon
    exact hc (.lamt 0) ⟨0, rfl⟩ (List.contains_iff_mem.1 (by simpa using hcon))
  have h1 : v.contains (.lamt 1) = false := by
    by_contra hcon
    exact hc (.lamt 1) ⟨1, rfl⟩ (List.contains_iff_mem.1 (by simpa using hcon))
  rw [countP_lw_isRes]
  exact loop_free_two ε n T (Or.inr hT) v hv h0 h1


/-- (5.37) [number_of_G_type_1] in the further expansion: every loop without `Δ` and without `Λ̃`
of an expression reached or expanded from a derivative structure `𝓡₀` has at least two
resolvents. -/
theorem pkg_ffree_two (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀)
    (j : ℕ) (R : PkgExpr) (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    ∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → w.any PkgLetter.isLam = false →
      2 ≤ w.countP PkgLetter.isRes := by
  have hfree := ffree_gen ε j [R₀]
    (fun S hS => by rw [List.mem_singleton.1 hS]; exact free_base ε n T hT p₀ q₀ R₀ hR₀) R hR
  intro w hw hent hlam
  exact hfree w hw hent hlam

end RBMTransitionEdge
end
