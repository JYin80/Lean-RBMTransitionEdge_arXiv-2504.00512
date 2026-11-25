module

public import RBMTransitionEdge.Localized.Expansion.PkgInv
public import RBMTransitionEdge.Localized.Expansion.FFactor
public import RBMTransitionEdge.Localized.Expansion.Rem2Expand
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgOps
public import RBMTransitionEdge.Localized.Expansion.PkgCounts
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgOps
import all RBMTransitionEdge.Localized.Expansion.PkgCounts
import all RBMTransitionEdge.Localized.Expansion.FFactor

@[expose] public section

/-!
# The place of `Λ̃` relative to the chosen resolvent

For an expression of the further expansion with a focus: the focus `ffocus` is a loop of the
expression and a resolvent `𝒢_a` found by `pkgSeek` from a letter `Λ̃` of that loop, and the letters
between `Λ̃` and `𝒢_a` are neither `Δ` nor resolvents, for the resolvent expanded in (5.83)
[concrete_expansion_tl_2_heavy_package_right] and (5.84) [concrete_expansion_tl_2_loop] in the
proof of Lemma 5.5 [claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private isEntP exists_first_ent findIdx_ent from RBMTransitionEdge.Localized.Expansion.PkgWords
open private PB_segs_ent from RBMTransitionEdge.Localized.Expansion.PkgBound
open private sum_map_set from RBMTransitionEdge.Localized.Expansion.PkgWords
open private seek_tl pkgSeek_pos from RBMTransitionEdge.Localized.Expansion.PkgOps
open private seek_tl2 fc_findIdx_mem fc_contains_idx fc_some_inj3
  from RBMTransitionEdge.Localized.Expansion.PkgCounts
open private FF_wf FF_pk FF_ents FF_len FF_ffacs FF_ents_free FF_ents_ent
  from RBMTransitionEdge.Localized.Expansion.FFactor

/-! ### The place of `Λ̃` relative to the chosen resolvent -/

/-- The focus of `ffocus` is a loop of the expression and a resolvent found by `pkgSeek` from a
letter `Λ̃` of that loop. -/
private lemma FH_focus (R : PkgExpr) (ℓ r : ℕ) (right : Bool)
    (hf : R.ffocus = some (ℓ, r, right)) :
    ∃ (w : List PkgLetter), R.loops[ℓ]? = some w ∧
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
        exact ⟨w₂, h₂, _, 1, fc_contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
          exact ⟨w₁, h₁, _, 0, fc_contains_idx _ _ c₁, hr'⟩
        · split at hf
          · rename_i r' hr'
            obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
            exact ⟨w₂, h₂, _, 1, fc_contains_idx _ _ c₂, hr'⟩
          · simp at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
        exact ⟨w₂, h₂, _, 1, fc_contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := fc_some_inj3 hf
          exact ⟨w₁, h₁, _, 0, fc_contains_idx _ _ c₁, hr'⟩
        · simp at hf
  · simp at hf

/-- Two suffixes after a letter `g` of the same list: the shorter has both properties. -/
private lemma FH_comb_R {α : Type*} (p q : α → Prop) (tl : List α) (g : α)
    (h1 : ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₂, p z)
    (h2 : ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₂, q z) :
    ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₂, p z ∧ q z := by
  obtain ⟨A, B, hAB, hp⟩ := h1
  obtain ⟨C, D, hCD, hq⟩ := h2
  have h : A ++ g :: B = C ++ g :: D := hAB.symm.trans hCD
  rcases List.append_eq_append_iff.1 h with ⟨a', h1', h2'⟩ | ⟨c', h1', h2'⟩
  · -- `C = A ++ a'`, `g :: B = a' ++ g :: D`: `D` is a suffix of `B`
    rcases a' with _ | ⟨c₀, a''⟩
    · have : B = D := by simpa using h2'
      subst this
      exact ⟨A, B, hAB, fun z hz => ⟨hp z hz, hq z hz⟩⟩
    · have hB : B = a'' ++ g :: D := (List.cons.inj h2').2
      refine ⟨C, D, hCD, fun z hz => ⟨hp z ?_, hq z hz⟩⟩
      rw [hB]; simp [hz]
  · -- `A = C ++ c'`, `g :: D = c' ++ g :: B`: `B` is a suffix of `D`
    rcases c' with _ | ⟨c₀, c''⟩
    · have : D = B := by simpa using h2'
      subst this
      exact ⟨A, D, hAB, fun z hz => ⟨hp z hz, hq z hz⟩⟩
    · have hD : D = c'' ++ g :: B := (List.cons.inj h2').2
      refine ⟨A, B, hAB, fun z hz => ⟨hp z hz, hq z ?_⟩⟩
      rw [hD]; simp [hz]

/-- Two prefixes before a letter `g` of the same list: the shorter has both properties. -/
private lemma FH_comb_L {α : Type*} (p q : α → Prop) (tl : List α) (g : α)
    (h1 : ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₁, p z)
    (h2 : ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₁, q z) :
    ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₁, p z ∧ q z := by
  obtain ⟨A, B, hAB, hp⟩ := h1
  obtain ⟨C, D, hCD, hq⟩ := h2
  have h : A ++ g :: B = C ++ g :: D := hAB.symm.trans hCD
  rcases List.append_eq_append_iff.1 h with ⟨a', h1', h2'⟩ | ⟨c', h1', h2'⟩
  · -- `C = A ++ a'`: `A` is a prefix of `C`
    refine ⟨A, B, hAB, fun z hz => ⟨hp z hz, hq z ?_⟩⟩
    rw [h1']; simp [hz]
  · -- `A = C ++ c'`: `C` is a prefix of `A`
    refine ⟨C, D, hCD, fun z hz => ⟨hp z ?_, hq z hz⟩⟩
    rw [h1']; simp [hz]

/-- The rotation `𝒢_a tl` of the loop at the focus, `tl` cut at the letter `Λ̃`: the letters between
`Λ̃` and `𝒢_a` (after it for `right`, before it otherwise) are neither `Δ` nor resolvents. -/
private lemma FH_shape (w : List PkgLetter) (i r : ℕ) (right : Bool) (o : Fin 2)
    (hg : w[i]? = some (.lw (.lamt o))) (h : pkgSeek w i right = some r) :
    ∃ (a : Fin 2) (tl : List PkgLetter), w.rotate r = .lw (.res a) :: tl ∧
      (right = true → ∃ Y X, tl = Y ++ .lw (.lamt o) :: X ∧
        ∀ z ∈ X, isEntP z = false ∧ z.isRes = false) ∧
      (right = false → ∃ X Y, tl = X ++ .lw (.lamt o) :: Y ∧
        ∀ z ∈ X, isEntP z = false ∧ z.isRes = false) := by
  obtain ⟨k, hk, hr, hfree, b, hb⟩ := pkgSeek_pos w i r right h
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hb
  have hrot : w.rotate r = .lw (.res b) :: (w.drop (r + 1) ++ w.take r) := by
    rw [List.rotate_eq_drop_append_take hlt.le, List.drop_eq_getElem_cons hlt, hget]
    rfl
  refine ⟨b, _, hrot, fun hright => ?_, fun hright => ?_⟩
  · have a1 := (seek_tl w i r right _ hg h b _ hrot).1 hright
    have a2 := (seek_tl2 w i r right _ hg h b _ hrot).1 hright
    obtain ⟨Y, X, hYX, hX⟩ := FH_comb_R (fun z => isEntP z = false) (fun z => z.isRes = false)
      _ _ a1 a2
    exact ⟨Y, X, hYX, hX⟩
  · have a1 := (seek_tl w i r right _ hg h b _ hrot).2 hright
    have a2 := (seek_tl2 w i r right _ hg h b _ hrot).2 hright
    obtain ⟨X, Y, hXY, hX⟩ := FH_comb_L (fun z => isEntP z = false) (fun z => z.isRes = false)
      _ _ a1 a2
    exact ⟨X, Y, hXY, hX⟩

end RBMTransitionEdge

end
