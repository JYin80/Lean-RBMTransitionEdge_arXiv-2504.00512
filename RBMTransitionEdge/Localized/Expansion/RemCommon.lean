module

public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# Facts of every Type on the expressions of the further expansion

For the expressions of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the order of the rules (i)–(iv) for an expression not of
Type II, with the empty sides it passes over; and the uniqueness of the package entry holding `Λ̃_o`
(Example 5.7 [example_estimate_reminder_reminder_terms] and the companion cases (1)–(3), (8),
(9)).
-/

namespace RBMTransitionEdge

/-! ### The order of the rules -/

/-- The first word holding `Λ̃_o`, read by index as in `ffocusSide`, is the one found by
`find?` as in `lamSide` and `ptype`. -/
private theorem RC_idx (L : List (List PkgLetter)) (o : Fin 2) :
    L[L.findIdx fun w => w.contains (.lw (.lamt o))]? =
      L.find? fun w => w.contains (.lw (.lamt o)) :=
  List.find?_eq_getElem?_findIdx.symm

/-- If the search `pkgSeek` of a side of `Λ̃_o` finds no resolvent, that side of `Λ̃_o` has no
resolvent: both read the same letters. -/
private theorem RC_seek_none (R : PkgExpr) (o : Fin 2) (right : Bool) (w : List PkgLetter)
    (hw : (R.loops.find? fun w => w.contains (.lw (.lamt o))) = some w)
    (hs : pkgSeek w (w.idxOf (.lw (.lamt o))) right = none) : R.lamSide o right = 0 := by
  unfold PkgExpr.lamSide
  rw [hw]
  unfold pkgSeek at hs
  rw [List.find?_eq_none] at hs
  simp only
  rw [List.countP_eq_zero]
  exact hs

/-- The order of the rules (i)–(iv) of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms] for an expression not of Type II: the side chosen is the right
side of `Λ̃₂`, the right side of `Λ̃₁` or the left side of `Λ̃₂`, and the right sides passed over
are empty. -/
theorem pkg_ffocusSide_cases (R : PkgExpr) (hR : R.ptype ≠ 2) :
    (R.ffocusSide = none ∨ R.ffocusSide = some (1, true) ∨ R.ffocusSide = some (0, true) ∨
        R.ffocusSide = some (1, false)) ∧
      (R.ffocusSide = some (0, true) → R.lamSide 1 true = 0) ∧
      (R.ffocusSide = some (1, false) → R.lamSide 1 true = 0 ∧ R.lamSide 0 true = 0) := by
  have k₂ := RC_idx R.loops 1
  have k₁ := RC_idx R.loops 0
  unfold PkgExpr.ffocusSide
  rcases h₂ : R.loops.find? (fun w => w.contains (.lw (.lamt 1))) with _ | w₂ <;>
    rw [h₂] at k₂
  · simp only [k₂]; simp
  rcases h₁ : R.loops.find? (fun w => w.contains (.lw (.lamt 0))) with _ | w₁ <;>
    rw [h₁] at k₁
  · simp only [k₂, k₁]; simp
  have hE : w₂.any PkgLetter.isEnt = true := by
    by_contra hn
    apply hR
    unfold PkgExpr.ptype
    rw [h₂]
    dsimp only
    rw [ite_eq_left (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.2 hn)]
  simp only [k₂, k₁]
  rw [ite_eq_left (by exact hE)]
  rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) true with _ | r₁
  · rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂
    · rcases s3 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₃
      · simp only [s1, s2, s3]; simp
      · simp only [s1, s2, s3, reduceCtorEq, Option.some.injEq, Prod.mk.injEq]
        exact ⟨by simp, fun h => absurd h.2 (by decide),
          fun _ => ⟨RC_seek_none R 1 true w₂ h₂ s1, RC_seek_none R 0 true w₁ h₁ s2⟩⟩
    · simp only [s1, s2, reduceCtorEq, Option.some.injEq, Prod.mk.injEq]
      exact ⟨by simp, fun _ => RC_seek_none R 1 true w₂ h₂ s1, fun h => absurd h.1 (by decide)⟩
  · simp only [s1, reduceCtorEq, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by simp, fun h => absurd h.1 (by decide), fun h => absurd h.2 (by decide)⟩

/-! ### The package entry holding `Λ̃_o` -/

open private FW_pents FW_pw FW_pw_segs FW_pw_free FW_wf_count
  from RBMTransitionEdge.Localized.Expansion.FEntWords
open private PB_segs_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private isEntP from RBMTransitionEdge.Localized.Expansion.PkgWords

/-- The sum of `h` over a list is `h a` plus the sum over the list with `a` erased. -/
private theorem RC_sum_erase {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (a : α)
    (ha : a ∈ L) (h : α → ℕ) : (L.map h).sum = h a + ((L.erase a).map h).sum := by
  rw [((List.perm_cons_erase ha).map h).sum_eq]
  simp

/-- In a well-formed expression, the letter `Λ̃_o` lies in at most one package entry, counted
with multiplicity. -/
private theorem RC_pents_cnt (X : PkgExpr) (hX : X.wf = true) (o : Fin 2) :
    (X.pents.map fun e => e.2.2.count (.lw (.lamt o))).sum ≤ 1 := by
  have hw : ∀ w : List PkgLetter, ((FW_pw w).map fun e => e.2.2.count (.lw (.lamt o))).sum ≤
      w.count (.lw (.lamt o)) := by
    intro w
    cases hE : w.any PkgLetter.isEnt
    · rw [FW_pw_free w hE]; simp
    · have h1 : ((FW_pw w).map fun e => e.2.2.count (.lw (.lamt o))) =
          (pkgSegs w).map fun σ => σ.count (.lw (.lamt o)) := by
        rw [← FW_pw_segs w hE, List.map_map]
        rfl
      rw [h1]
      have h2 := (PB_segs_count (fun x => x == .lw (.lamt o)) (fun x hx => by
        rcases x with _ | ⟨u, v⟩
        · simp [isEntP] at hx
        · rfl) w).1
      exact le_of_eq h2
  have key : ∀ L : List (List PkgLetter), ((L.flatMap FW_pw).map
      fun e => e.2.2.count (.lw (.lamt o))).sum ≤ (L.map fun w => w.count (.lw (.lamt o))).sum := by
    intro L
    induction L with
    | nil => simp
    | cons w L ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      have := hw w
      omega
  rw [FW_pents]
  exact (key _).trans (FW_wf_count X hX o).le

/-- In a well-formed expression of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms], two package entries holding `Λ̃_o` are equal. -/
theorem pkg_pents_lam_uniq (X : PkgExpr) (hX : X.wf = true) (o : Fin 2)
    (e e' : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (he' : e' ∈ X.pents)
    (ho : PkgLetter.lw (.lamt o) ∈ e.2.2) (ho' : PkgLetter.lw (.lamt o) ∈ e'.2.2) : e = e' := by
  by_contra hne
  rw [← List.count_pos_iff] at ho ho'
  have h1 := RC_sum_erase _ _ he fun e => e.2.2.count (.lw (.lamt o))
  have h2 := List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun e : ℕ × ℕ × List PkgLetter => e.2.2.count (.lw (.lamt o)))
    ((List.mem_erase_of_ne (Ne.symm hne)).2 he'))
  have := RC_pents_cnt X hX o
  omega

end RBMTransitionEdge
