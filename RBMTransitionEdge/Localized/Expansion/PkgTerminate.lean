module

public import RBMTransitionEdge.Localized.Expansion.PkgOps
public import RBMTransitionEdge.Localized.Expansion.Reach

@[expose] public section

/-!
# The stopping rule and the termination of the further expansion of Lemma 5.5

The quantity `Ψ′` of an expression of the class of (5.79)–(5.81), the stopping rule `Ψ′ ≥ 4` or
no rule (i)–(iv) applies, the rounds of the further expansion and its inner nodes, and the
termination of the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]
from every starting expression `𝓡₀` of Table 3 [table_Classification_of_Initial_Values].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `Ψ′(𝓡) = (size′₁ - size′₂) + ε (size′₂ + 2)` with `size′ = (S + u, m - n + u)` of the further
expansion (before the stopping rule of Lemma 5.5 [claim_estimate_remainder_terms]). -/
def PkgExpr.psiP (ε : ℝ) (R : PkgExpr) : ℝ :=
  match R.charsP with
  | (m, n, u, S) => ((S + u - (m - n + u) : ℤ) : ℝ) + ε * ((m - n + u + 2 : ℤ) : ℝ)

/-- The stopping rule of the further expansion: `Ψ′ ≥ 4`, or none of the rules (i)–(iv) applies
(`k₁ = k₂ = 0`). -/
def PkgExpr.FStopped (ε : ℝ) (R : PkgExpr) : Prop :=
  4 ≤ R.psiP ε ∨ R.ffocus = none

/-- The expressions after `n` rounds of the further expansion. -/
def fIter (ε : ℝ) : ℕ → List PkgExpr → List PkgExpr
  | 0, L => L
  | n + 1, L => fIter ε n (L.flatMap fun R => if R.FStopped ε then [R] else R.fstep)

/-- The expressions expanded during `n` rounds of the further expansion, each contributing its
remainder `𝓔^{(2)}_𝓡`. -/
def fInner (ε : ℝ) : ℕ → List PkgExpr → List PkgExpr
  | 0, _ => []
  | n + 1, L => L.filter (fun R => decide (¬ R.FStopped ε)) ++
      fInner ε n (L.flatMap fun R => if R.FStopped ε then [R] else R.fstep)


/-! ### Auxiliary facts: the rounds of the further expansion -/

private theorem fIter_nil (ε : ℝ) : ∀ n : ℕ, fIter ε n [] = []
  | 0 => rfl
  | n + 1 => by simpa [fIter] using fIter_nil ε n

private theorem fIter_append (ε : ℝ) :
    ∀ (n : ℕ) (L₁ L₂ : List PkgExpr), fIter ε n (L₁ ++ L₂) = fIter ε n L₁ ++ fIter ε n L₂
  | 0, _, _ => rfl
  | n + 1, L₁, L₂ => by
      simp only [fIter, List.flatMap_append]
      exact fIter_append ε n _ _

private theorem fIter_flat (ε : ℝ) (n : ℕ) :
    ∀ L : List PkgExpr, fIter ε n L = L.flatMap fun R => fIter ε n [R]
  | [] => by simp [fIter_nil]
  | R :: L => by
      rw [show R :: L = [R] ++ L from rfl, fIter_append, fIter_flat ε n L]
      simp

private theorem fIter_stopped (ε : ℝ) (R : PkgExpr) (hs : R.FStopped ε) :
    ∀ n : ℕ, fIter ε n [R] = [R]
  | 0 => rfl
  | n + 1 => by simpa [fIter, hs] using fIter_stopped ε R hs n

private theorem fIter_succ_of_not (ε : ℝ) (R : PkgExpr) (hs : ¬ R.FStopped ε) (n : ℕ) :
    fIter ε (n + 1) [R] = fIter ε n R.fstep := by
  simp [fIter, hs]

private theorem fIter_add (ε : ℝ) :
    ∀ (n d : ℕ) (L : List PkgExpr), fIter ε (n + d) L = fIter ε d (fIter ε n L)
  | 0, d, L => by rw [Nat.zero_add]; rfl
  | n + 1, d, L => by
      rw [show n + 1 + d = (n + d) + 1 by omega]
      exact fIter_add ε n d _

private theorem fIter_all_stopped (ε : ℝ) (d : ℕ) :
    ∀ L : List PkgExpr, (∀ R ∈ L, R.FStopped ε) → fIter ε d L = L
  | [], _ => fIter_nil ε d
  | R :: L, h => by
      rw [show R :: L = [R] ++ L from rfl, fIter_append,
        fIter_stopped ε R (h R List.mem_cons_self),
        fIter_all_stopped ε d L (fun R' hR' => h R' (List.mem_cons_of_mem _ hR'))]

/-- After `T` rounds every expression of the further expansion from `R` is stopped. -/
private def Done (ε : ℝ) (R : PkgExpr) (T : ℕ) : Prop :=
  ∀ R' ∈ fIter ε T [R], R'.FStopped ε

private theorem done_mono (ε : ℝ) (R : PkgExpr) (T T' : ℕ) (h : Done ε R T) (hT : T ≤ T') :
    Done ε R T' := by
  intro R' hR'
  rw [show T' = T + (T' - T) by omega, fIter_add, fIter_all_stopped ε _ _ h] at hR'
  exact h R' hR'

private theorem done_list (ε : ℝ) :
    ∀ L : List PkgExpr, (∀ R ∈ L, ∃ T, Done ε R T) → ∃ T, ∀ R ∈ L, Done ε R T
  | [], _ => ⟨0, by simp⟩
  | R :: L, h => by
      obtain ⟨T₁, h₁⟩ := h R List.mem_cons_self
      obtain ⟨T₂, h₂⟩ := done_list ε L (fun R' hR' => h R' (List.mem_cons_of_mem _ hR'))
      refine ⟨max T₁ T₂, fun R' hR' => ?_⟩
      rcases List.mem_cons.1 hR' with rfl | hR'
      · exact done_mono ε _ _ _ h₁ (le_max_left _ _)
      · exact done_mono ε _ _ _ (h₂ R' hR') (le_max_right _ _)

/-! ### Auxiliary facts: the change of `Ψ′` -/

/-- The change of `Ψ′` under an operation of Table 2 [table_effect_of_operations_2]. -/
private def dpsi (ε : ℝ) (o : PkgOp) : ℝ :=
  match o.delta with
  | (dm, dn, du, dS) => ((dS + du - (dm - dn + du) : ℤ) : ℝ) + ε * ((dm - dn + du : ℤ) : ℝ)

private theorem psi_step (ε : ℝ) (R : PkgExpr) (o : PkgOp) (R' : PkgExpr)
    (h : (o, R') ∈ R.fterms) : R'.psiP ε = R.psiP ε + dpsi ε o := by
  have h2 := pkg_table2 R o R' h
  unfold PkgExpr.psiP
  rw [h2]
  obtain ⟨m, n, u, S⟩ := R.charsP
  cases o <;> simp only [PkgOp.delta, dpsi] <;> push_cast <;> ring

private theorem dpsi_nonneg (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (o : PkgOp) : 0 ≤ dpsi ε o := by
  cases o <;> simp only [dpsi, PkgOp.delta] <;> push_cast <;> linarith

private theorem dpsi_gain (ε : ℝ) (hε : 0 < ε) (o : PkgOp) (h1 : o ≠ .fcut2)
    (h2 : o ≠ .slash2) : min ε (1 - ε) ≤ dpsi ε o := by
  cases o <;> simp only [dpsi, PkgOp.delta] <;> push_cast <;>
    first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | (have := min_le_left ε (1 - ε); have := min_le_right ε (1 - ε); linarith)

/-- The number of gains left before `Ψ′ ≥ 4`. -/
private def gainsLeft (ε : ℝ) (R : PkgExpr) : ℕ :=
  ⌈(4 - R.psiP ε) / min ε (1 - ε)⌉₊

private theorem gainsLeft_le (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (R R' : PkgExpr)
    (h : R.psiP ε ≤ R'.psiP ε) : gainsLeft ε R' ≤ gainsLeft ε R := by
  have hδ : 0 < min ε (1 - ε) := lt_min hε (by linarith)
  unfold gainsLeft
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (by linarith) hδ.le

private theorem gainsLeft_lt (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (R R' : PkgExpr)
    (hR : R.psiP ε < 4) (h : R.psiP ε + min ε (1 - ε) ≤ R'.psiP ε) :
    gainsLeft ε R' < gainsLeft ε R := by
  have hδ : 0 < min ε (1 - ε) := lt_min hε (by linarith)
  unfold gainsLeft
  set x := (4 - R.psiP ε) / min ε (1 - ε) with hx
  have hx0 : 0 < x := div_pos (by linarith) hδ
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    intro h0
    rw [Nat.ceil_eq_zero] at h0
    linarith)
  have hle : (4 - R'.psiP ε) / min ε (1 - ε) ≤ x - 1 := by
    rw [hx, div_sub_one hδ.ne', div_le_div_iff_of_pos_right hδ]
    linarith
  have h2 : ⌈(4 - R'.psiP ε) / min ε (1 - ε)⌉₊ ≤ ⌈x⌉₊ - 1 := by
    rw [Nat.ceil_le]
    have := Nat.le_ceil x
    push_cast [hc]
    linarith
  omega

/-! ### Auxiliary facts: the count of resolvents of the words with a `Λ̃` -/

/-- The letter `x` is a resolvent `𝒢_a`. -/
private def isResP (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | _ => false

/-- The letter `x` is one of `Λ̃₁`, `Λ̃₂`. -/
private def isLamP (x : PkgLetter) : Bool :=
  match x with | .lw (.lamt _) => true | _ => false

/-- The number of letters `Λ̃` of a word. -/
private def tC (v : List PkgLetter) : ℕ :=
  v.countP isLamP

/-- The number of letters `Λ̃` of a word times its number of resolvents. -/
private def wM (v : List PkgLetter) : ℕ :=
  tC v * v.countP isResP

/-- The sum over the words of the number of letters `Λ̃` times the number of resolvents. -/
private def pkM (R : PkgExpr) : ℕ :=
  (R.loops.map wM).sum

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

/-- The search of `takeWhile` and `find?` along `f 0, f 1, …` returns some `f k`; `P` holds on
`f 0, …, f k`, and `Q` fails on `f 0, …, f (k - 1)`. -/
private theorem seek_aux (P Q : ℕ → Bool) (r : ℕ) : ∀ (n : ℕ) (f : ℕ → ℕ),
    (((List.range n).map f).takeWhile P).find? Q = some r →
      ∃ k < n, r = f k ∧ (∀ j ≤ k, P (f j) = true) ∧ (∀ j < k, Q (f j) = false) ∧
        Q (f k) = true
  | 0, f, h => by simp at h
  | n + 1, f, h => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.takeWhile_cons] at h
      by_cases hP : P (f 0) = true
      · simp only [hP, ↓reduceIte] at h
        rw [List.find?_cons] at h
        cases hQ : Q (f 0)
        · rw [hQ] at h
          obtain ⟨k, hk, hr, hPk, hQk', hQk⟩ := seek_aux P Q r n (f ∘ Nat.succ) h
          refine ⟨k + 1, by omega, hr, ?_, ?_, hQk⟩
          · intro j hj
            cases j with
            | zero => exact hP
            | succ j => exact hPk j (by omega)
          · intro j hj
            cases j with
            | zero => exact hQ
            | succ j => exact hQk' j (by omega)
        · rw [hQ] at h
          have := Option.some.inj h
          subst this
          refine ⟨0, by omega, rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), hQ⟩
          intro j hj
          have : j = 0 := by omega
          subst this
          exact hP
      · simp [hP] at h

/-- The positions searched by `pkgSeek`. -/
private def seekPos (len i : ℕ) (right : Bool) (j : ℕ) : ℕ :=
  if right then (i + 1 + j) % len else (i + len - 1 - j) % len

private theorem pkgSeek_pos (w : List PkgLetter) (i r : ℕ) (right : Bool)
    (h : pkgSeek w i right = some r) :
    ∃ k, k + 1 < w.length ∧ r = seekPos w.length i right k ∧
      (∀ j < k, ∃ z, w[seekPos w.length i right j]? = some z ∧ isResP z = false) ∧
      ∃ b, w[r]? = some (.lw (.res b)) := by
  have h' : (((List.range (w.length - 1)).map (seekPos w.length i right)).takeWhile
      fun r => match w[r]? with
        | some (PkgLetter.ent _ _) => false | some (PkgLetter.lw (LoopLetter.lamt _)) => false
        | _ => true).find? (fun r =>
      match w[r]? with | some (PkgLetter.lw (LoopLetter.res _)) => true | _ => false) = some r := h
  obtain ⟨k, hk, hr, -, hQ', hQ⟩ := seek_aux _ _ r _ _ h'
  have hlen : 0 < w.length := by omega
  have hmem : ∀ j, w[seekPos w.length i right j]? ≠ none := by
    intro j
    have : seekPos w.length i right j < w.length := by
      unfold seekPos
      split <;> exact Nat.mod_lt _ hlen
    rw [List.getElem?_eq_getElem this]
    simp
  refine ⟨k, by omega, hr, ?_, ?_⟩
  · intro j hj
    have hQj := hQ' j hj
    rcases hz : w[seekPos w.length i right j]? with _ | z
    · exact absurd hz (hmem j)
    · refine ⟨z, rfl, ?_⟩
      rw [hz] at hQj
      match z, hQj with
      | .ent _ _, _ => rfl
      | .lw (.res _), hQj => exact absurd hQj (by simp)
      | .lw (.det _), _ => rfl
      | .lw (.proj _), _ => rfl
      | .lw (.lamt _), _ => rfl
  · rw [hr]
    revert hQ
    rcases hz : w[seekPos w.length i right k]? with _ | z
    · simp
    · intro hQ
      match z, hQ with
      | .lw (.res b), _ => exact ⟨b, rfl⟩
      | .ent _ _, hQ => exact absurd hQ (by simp)
      | .lw (.det _), hQ => exact absurd hQ (by simp)
      | .lw (.proj _), hQ => exact absurd hQ (by simp)
      | .lw (.lamt _), hQ => exact absurd hQ (by simp)

/-- The resolvent found by `pkgSeek` from the letter `g` at position `i`: no resolvent lies
between `g` and it on the side searched. -/
private theorem seek_tl (w : List PkgLetter) (i r : ℕ) (right : Bool) (g : PkgLetter)
    (hg : w[i]? = some g) (h : pkgSeek w i right = some r) (a : Fin 2) (tl : List PkgLetter)
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    (right = true → ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₂, isResP z = false) ∧
    (right = false → ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₁, isResP z = false) := by
  obtain ⟨k, hk, hr, hfree, b, hb⟩ := pkgSeek_pos w i r right h
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
    have e1 : r = (i + 1 + k) % w.length := by simpa [seekPos] using hr
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
        obtain ⟨z', hz', hz'e⟩ := hfree n hnk
        have e2 : (n + 1 + i) % w.length = seekPos w.length i true n := by
          simp only [seekPos, ite_true]; congr 1; omega
        rw [e2, hz'] at hzu
        cases hzu
        exact hz'e
      · simp at hn
  · rintro rfl
    have e1 : r = (i + w.length - 1 - k) % w.length := by simpa [seekPos] using hr
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
      have e2 : (c + 1 + n + i) % w.length = seekPos w.length i false (k - 1 - n) := by
        simp only [seekPos, Bool.false_eq_true, ite_false]; congr 1; omega
      rw [hu _ hn', e2, hz'] at hn
      cases hn
      exact hz'e

private theorem findIdx_mem {α : Type*} (l : List α) (p : α → Bool) (x : α)
    (h : l[l.findIdx p]? = some x) : p x = true := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  have := List.findIdx_getElem (p := p) (xs := l) (w := hlt)
  rwa [hget] at this

private theorem contains_idx (w : List PkgLetter) (x : PkgLetter) (h : w.contains x = true) :
    w[w.idxOf x]? = some x := by
  have hm : x ∈ w := List.contains_iff_mem.1 h
  have hlt : w.idxOf x < w.length := List.idxOf_lt_length_iff.2 hm
  rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]

private theorem some_inj3 {ℓ ℓ' r r' : ℕ} {s s' : Bool}
    (h : some (ℓ', r', s') = some (ℓ, r, s)) : ℓ' = ℓ ∧ r' = r ∧ s' = s := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨h3, h4⟩ := Prod.mk.inj h2
  exact ⟨h1, h3, h4⟩

/-- The loop and the position of the letter `Λ̃` from which `ffocus` searches. -/
private theorem ffocus_data (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (w : List PkgLetter)
    (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w) :
    ∃ i o, w[i]? = some (.lw (.lamt o)) ∧ pkgSeek w i right = some r := by
  unfold PkgExpr.ffocus at hf
  dsimp only at hf
  split at hf
  · rename_i w₂ w₁ h₂ h₁
    have c₂ : w₂.contains (.lw (.lamt 1)) = true :=
      findIdx_mem R.loops (fun w => w.contains (.lw (.lamt 1))) w₂ h₂
    have c₁ : w₁.contains (.lw (.lamt 0)) = true :=
      findIdx_mem R.loops (fun w => w.contains (.lw (.lamt 0))) w₁ h₁
    split at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
        rw [h₂] at hw
        cases hw
        exact ⟨_, 1, contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
          rw [h₁] at hw
          cases hw
          exact ⟨_, 0, contains_idx _ _ c₁, hr'⟩
        · split at hf
          · rename_i r' hr'
            obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
            rw [h₂] at hw
            cases hw
            exact ⟨_, 1, contains_idx _ _ c₂, hr'⟩
          · simp at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
        rw [h₂] at hw
        cases hw
        exact ⟨_, 1, contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
          rw [h₁] at hw
          cases hw
          exact ⟨_, 0, contains_idx _ _ c₁, hr'⟩
        · simp at hf
  · simp at hf

/-- The word `W` of the terms of a further expansion: the word of the resolvent to expand with a
`𝔐` on the side of `Λ̃`. -/
private def wordW (right : Bool) (a : Fin 2) (tl : List PkgLetter) : List PkgLetter :=
  if right then .lw (.res a) :: tl ++ [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]

/-- A cut on the right of `Λ̃`: the resolvent `𝒢_b` lies between the expanded `𝒢_a` and `Λ̃`, so the
piece without `Λ̃` keeps `𝒢_a`. -/
private theorem cut_right (a b o : Fin 2) (L₁ L₂ U V : List PkgLetter)
    (h2 : ∀ z ∈ L₂, isResP z = false) (hU : U ≠ [])
    (h : U ++ .lw (.res b) :: V = (.lw (.res a) :: L₁) ++ .lw (.lamt o) :: (L₂ ++ [.lw (.det a)])) :
    .lw (.lamt o) ∈ V ∧ .lw (.res a) ∈ U := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h3⟩ | ⟨bs, h1, h3⟩
  · cases as with
    | nil => simp at h3
    | cons x as' =>
        obtain ⟨-, rfl⟩ := List.cons.inj h3
        refine ⟨by simp, ?_⟩
        cases U with
        | nil => exact absurd rfl hU
        | cons u U' =>
            obtain ⟨rfl, -⟩ := List.cons.inj h1
            exact List.mem_cons_self
  · exfalso
    cases bs with
    | nil => simp at h3
    | cons x bs' =>
        have hm : PkgLetter.lw (.res b) ∈ L₂ ++ [.lw (.det a)] := by
          rw [(List.cons.inj h3).2]
          simp
        rcases List.mem_append.1 hm with hm | hm
        · have := h2 _ hm
          simp [isResP] at this
        · simp at hm

/-- A cut on the left of `Λ̃`: the piece without `Λ̃` keeps the expanded `𝒢_a`. -/
private theorem cut_left (a b o : Fin 2) (L₁ L₂ U V : List PkgLetter)
    (h1 : ∀ z ∈ L₁, isResP z = false) (hV : V ≠ [])
    (h : U ++ .lw (.res b) :: V = (.lw (.det a) :: L₁) ++ .lw (.lamt o) :: (L₂ ++ [.lw (.res a)])) :
    .lw (.lamt o) ∈ U ∧ .lw (.res a) ∈ V := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1', h3⟩ | ⟨bs, h1', h3⟩
  · exfalso
    cases as with
    | nil => simp at h3
    | cons x as' =>
        obtain ⟨rfl, -⟩ := List.cons.inj h3
        have hm : PkgLetter.lw (.res b) ∈ PkgLetter.lw (.det a) :: L₁ := by
          rw [h1']
          simp
        rcases List.mem_cons.1 hm with hm | hm
        · cases hm
        · have := h1 _ hm
          simp [isResP] at this
  · cases bs with
    | nil => simp at h3
    | cons x bs' =>
        obtain ⟨rfl, h4⟩ := List.cons.inj h3
        refine ⟨by rw [h1']; simp, ?_⟩
        rcases List.eq_nil_or_concat V with hV0 | ⟨V', y, rfl⟩
        · exact absurd hV0 hV
        · have h5 : L₂ ++ [.lw (.res a)] = (bs' ++ .lw (.res b) :: V') ++ [y] := by
            rw [h4]
            simp
          have := (List.append_inj' h5 rfl).2
          simp only [List.cons.injEq, and_true] at this
          simp [this]

/-- The two pieces of a cut have fewer resolvents weighted by their letters `Λ̃` than the word. -/
private theorem pieces_lt (w U V : List PkgLetter) (b : Fin 2) (y : ℕ)
    (ht : tC U + tC V = tC w) (hr : U.countP isResP + V.countP isResP + 1 = w.countP isResP)
    (hn : (1 ≤ tC U ∧ 1 ≤ V.countP isResP) ∨ (1 ≤ tC V ∧ 1 ≤ U.countP isResP)) :
    wM (U ++ [.lw (.res b), .lw (.proj y)]) + wM (.lw (.proj y) :: .lw (.res b) :: V) <
      wM w := by
  have e1 : wM (U ++ [.lw (.res b), .lw (.proj y)]) = tC U * (U.countP isResP + 1) := by
    simp [wM, tC, isLamP, isResP, List.countP_append, List.countP_cons]
  have e2 : wM (.lw (.proj y) :: .lw (.res b) :: V) = tC V * (V.countP isResP + 1) := by
    simp [wM, tC, isLamP, isResP, List.countP_cons]
  have e3 : wM w = tC w * w.countP isResP := rfl
  rw [e1, e2, e3, ← ht, ← hr]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith

/-- A cut at the resolvent `𝒢_b` of the word `W` of the expanded `𝒢_a`: the two pieces have fewer
resolvents weighted by their letters `Λ̃` than the word. -/
private theorem cut_wM (R : PkgExpr) (ℓ r q : ℕ) (right : Bool) (w tl : List PkgLetter)
    (a b : Fin 2) (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) (hq : (wordW right a tl)[q]? = some (.lw (.res b)))
    (hex1 : right = true → q ≠ 0) (hex2 : right = false → q + 1 ≠ (wordW right a tl).length)
    (y : ℕ) :
    wM ((wordW right a tl).take (q + 1) ++ [.lw (.proj y)]) +
      wM (.lw (.proj y) :: (wordW right a tl).drop q) < wM w := by
  obtain ⟨i, o, hi, hs⟩ := ffocus_data R ℓ r right w hf hw
  obtain ⟨hR, hL⟩ := seek_tl w i r right _ hi hs a tl hrot
  have hperm : (PkgLetter.lw (.res a) :: tl).Perm w := hrot ▸ List.rotate_perm w r
  have hqlt : q < (wordW right a tl).length := (List.getElem?_eq_some_iff.1 hq).1
  set W := wordW right a tl with hWdef
  have hsplit : W = W.take q ++ .lw (.res b) :: W.drop (q + 1) := by
    obtain ⟨hr', hget⟩ := List.getElem?_eq_some_iff.1 hq
    rw [← hget, List.getElem_cons_drop, List.take_append_drop]
  have hUl : (W.take q).length = q := List.length_take_of_le hqlt.le
  generalize W.take q = U at hsplit hUl
  generalize W.drop (q + 1) = V at hsplit
  have hP1 : W.take (q + 1) ++ [.lw (.proj y)] = U ++ [.lw (.res b), .lw (.proj y)] := by
    rw [hsplit, ← hUl, List.take_length_add_append]
    simp
  have hP2 : PkgLetter.lw (.proj y) :: W.drop q = .lw (.proj y) :: .lw (.res b) :: V := by
    rw [hsplit, ← hUl, List.drop_left]
  rw [hP1, hP2]
  have htW : tC W = tC tl := by
    rw [hWdef]
    unfold wordW tC
    cases right <;> simp [List.countP_append, isLamP]
  have hrW : W.countP isResP = tl.countP isResP + 1 := by
    rw [hWdef]
    unfold wordW
    cases right <;> simp [List.countP_append, List.countP_cons, isResP]
  have htw : tC w = tC tl := by
    unfold tC
    rw [← hperm.countP_eq]
    simp [isLamP]
  have hrw : w.countP isResP = tl.countP isResP + 1 := by
    rw [← hperm.countP_eq]
    simp [List.countP_cons, isResP]
  have htUV : tC U + tC V = tC W := by
    rw [hsplit]
    unfold tC
    simp [List.countP_append, isLamP]
  have hrUV : U.countP isResP + V.countP isResP + 1 = W.countP isResP := by
    rw [hsplit]
    simp [List.countP_append, List.countP_cons, isResP]
    omega
  apply pieces_lt w U V b y (by omega) (by omega)
  have hres : ∀ L : List PkgLetter, PkgLetter.lw (.res a) ∈ L → 1 ≤ L.countP isResP := by
    intro L hL
    exact List.countP_pos_iff.2 ⟨_, hL, rfl⟩
  have hlam : ∀ L : List PkgLetter, PkgLetter.lw (.lamt o) ∈ L → 1 ≤ tC L := by
    intro L hL
    exact List.countP_pos_iff.2 ⟨_, hL, rfl⟩
  cases right
  · obtain ⟨L₁, L₂, rfl, h1⟩ := hL rfl
    have hV : V ≠ [] := by
      rintro rfl
      apply hex2 rfl
      rw [hsplit, List.length_append, hUl]
      simp
    have hW' : U ++ .lw (.res b) :: V =
        (.lw (.det a) :: L₁) ++ .lw (.lamt o) :: (L₂ ++ [.lw (.res a)]) := by
      rw [← hsplit, hWdef]
      simp [wordW]
    obtain ⟨h3, h4⟩ := cut_left a b o L₁ L₂ U V h1 hV hW'
    exact Or.inl ⟨hlam U h3, hres V h4⟩
  · obtain ⟨L₁, L₂, rfl, h2⟩ := hR rfl
    have hU : U ≠ [] := by
      rintro rfl
      exact hex1 rfl (by simpa using hUl.symm)
    have hW' : U ++ .lw (.res b) :: V =
        (.lw (.res a) :: L₁) ++ .lw (.lamt o) :: (L₂ ++ [.lw (.det a)]) := by
      rw [← hsplit, hWdef]
      simp [wordW]
    obtain ⟨h3, h4⟩ := cut_right a b o L₁ L₂ U V h2 hU hW'
    exact Or.inr ⟨hlam V h3, hres U h4⟩

/-- Every term of the further expansion either raises `Ψ′` by a gain, or is a cut, which lowers
`pkM`. -/
private theorem fterms_cases (R : PkgExpr) (o : PkgOp) (R' : PkgExpr) (h : (o, R') ∈ R.fterms) :
    (o ≠ .fcut2 ∧ o ≠ .slash2) ∨ pkM R' < pkM R := by
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
            else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)]) = wordW right a tl := rfl
        rw [hWdef] at h
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · left
              rcases List.mem_cons.1 h with h | h
              · obtain ⟨rfl, -⟩ := Prod.mk.inj h
                exact ⟨by decide, by decide⟩
              · rcases List.mem_cons.1 h with h | h
                · obtain ⟨rfl, -⟩ := Prod.mk.inj h
                  split <;> exact ⟨by decide, by decide⟩
                · simp at h
            · -- cut at another resolvent of the expanded word
              right
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 h
              split at hq
              · simp at hq
              · rename_i hex
                split at hq
                · rename_i b hqb
                  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  have hlt := cut_wM R ℓ r q right w tl a b hf hw hrot hqb
                    (fun h1 h2 => hex (by simp [h1, h2]))
                    (fun h1 h2 => hex (by simp [h1, h2])) R.nb
                  have hs := sum_map_set wM R.loops ℓ w
                    ((wordW right a tl).take (q + 1) ++ [.lw (.proj R.nb)]) hw
                  unfold pkM
                  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
                    List.sum_cons, List.sum_nil]
                  omega
                · simp at hq
          · left
            obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
            split at hj
            · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hj)
              split <;> exact ⟨by decide, by decide⟩
            · simp at hj
        · left
          obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
          split at hj
          · simp at hj
          · split at hj
            · simp at hj
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hq)
                split <;> split <;> exact ⟨by decide, by decide⟩
              · simp at hq
      · simp at h

/-- The further expansion from any expression stops after finitely many rounds. -/
private theorem pkgT_all (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (R : PkgExpr) : ∃ T, Done ε R T := by
  have hwf : WellFounded (Prod.Lex (· < ·) (· < ·) : ℕ × ℕ → ℕ × ℕ → Prop) :=
    WellFounded.prod_lex wellFounded_lt wellFounded_lt
  refine (InvImage.wf (fun R : PkgExpr => (gainsLeft ε R, pkM R)) hwf).induction
    (C := fun R => ∃ T, Done ε R T) R ?_
  intro R IH
  by_cases hs : R.FStopped ε
  · refine ⟨0, fun R' hR' => ?_⟩
    rw [fIter_stopped ε R hs] at hR'
    rw [List.mem_singleton.1 hR']
    exact hs
  · have hψ : R.psiP ε < 4 := by
      by_contra h4
      exact hs (Or.inl (not_lt.1 h4))
    have hch : ∀ R' ∈ R.fstep, ∃ T, Done ε R' T := by
      intro R' hR'
      obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 hR'
      apply IH
      have hp := psi_step ε R o _ hmem
      have hle := gainsLeft_le ε hε hε' R _ (by rw [hp]; linarith [dpsi_nonneg ε hε hε' o])
      rcases fterms_cases R o _ hmem with ⟨h1, h2⟩ | hM
      · exact Prod.Lex.left _ _
          (gainsLeft_lt ε hε hε' R _ hψ (by rw [hp]; linarith [dpsi_gain ε hε o h1 h2]))
      · rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact Prod.Lex.left _ _ hlt
        · change Prod.Lex _ _ (gainsLeft ε _, pkM _) (gainsLeft ε R, pkM R)
          rw [heq]
          exact Prod.Lex.right _ hM
    obtain ⟨T, hT⟩ := done_list ε _ hch
    refine ⟨T + 1, fun R' hR' => ?_⟩
    rw [fIter_succ_of_not ε R hs, fIter_flat] at hR'
    obtain ⟨R'', h1, h2⟩ := List.mem_flatMap.1 hR'
    exact hT R'' h1 R' h2

/-- The further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms] stops after a
number of rounds that depends on `ε` and the starting expression only: the rules (i)–(iv) are run
through in order, and each operation `𝔣𝔯`, `𝔣𝔠₂`, `𝔰𝔩𝔞𝔰𝔥₂` lowers the number of resolvents of the
segment selected by the active rule. -/
theorem pkg_terminates (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (h1 : 1 ≤ T.kk 0) (p q : ℕ) (hpq : p + q = 2)
    (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p q) :
    ∃ T₀ : ℕ, ∀ R ∈ fIter ε T₀ [R₀], R.FStopped ε := by
  exact pkgT_all ε hε hε' R₀

end RBMTransitionEdge

end
