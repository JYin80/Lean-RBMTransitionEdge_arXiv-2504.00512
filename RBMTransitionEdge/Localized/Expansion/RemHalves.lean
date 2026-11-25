module

public import RBMTransitionEdge.Localized.Expansion.RemStep
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.PairG
public import RBMTransitionEdge.Localized.Expansion.PkgShape
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.PairG
import all RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.FHalves
import all RBMTransitionEdge.Localized.Expansion.RemStep

@[expose] public section

/-!
# The halves of the expanded word through the derivatives

Under the binders of the remainder pins of the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
the entry of the `Λ̃`-half of `R.fpkg` in a derivative structure `R'` (role `0`), the end pieces of
every segment of `R.fpkg`, the sides of the letters `Λ̃`, the start of the segment of `Λ̃₁`, and
the free resolvents of (5.79) [further_expansion_expression_Type_1]; and the sides of a letter
`Λ̃` alone in a loop, the side chosen by the rules, and `freeTwo` through the expanded word.
-/

namespace RBMTransitionEdge

open private FW_pw FW_pents FW_pw_segs FW_pw_free FW_pw_eq FW_mem_pents FW_seg_cyc FW_count_le
  FW_wf_count FW_lamSide_mem FW_wside FW_wside_split FW_wside_cyc FW_run FW_run_cons FW_run_nil
  FW_run_congr FW_run_go FW_go FW_go_ent FW_go_lam FW_split_struct FW_split_last FW_split_mem
  FW_two_le FW_focus FW_findIdx_mem FW_rent FW_g FW_mk FW_g_isSome from RBMTransitionEdge.Localized.Expansion.FEntWords
open private PG_E PG_len from RBMTransitionEdge.Localized.Expansion.PairG
open private PSh_exists_first_ent pkgSegs_first dent_cases from RBMTransitionEdge.Localized.Expansion.PkgShape
open private isEntP from RBMTransitionEdge.Localized.Expansion.PkgWords
open private FH_shape from RBMTransitionEdge.Localized.Expansion.FHalves
open private RS_pw RS_pents RS_flat RS_flat_set RS_pw_rot RS_swap RS_core RS_cut RS_fpkg
  from RBMTransitionEdge.Localized.Expansion.RemStep

/-! ### Lists -/

/-- A list `A r B` read as `P y Q` with `r ≠ y`: `r` lies in `P` or in `Q`. -/
private theorem RH_cut {α : Type*} (A B P Q : List α) (r y : α) (hry : r ≠ y)
    (h : A ++ r :: B = P ++ y :: Q) :
    (∃ M, P = A ++ r :: M ∧ B = M ++ y :: Q) ∨ (∃ M, A = P ++ y :: M ∧ Q = M ++ r :: B) := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases a' with _ | ⟨c, a''⟩
    · simp only [List.nil_append, List.cons.injEq] at h2
      exact absurd h2.1 hry
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      exact Or.inl ⟨a'', h1, h2⟩
  · rcases c' with _ | ⟨c, c''⟩
    · simp only [List.nil_append, List.cons.injEq] at h2
      exact absurd h2.1.symm hry
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      exact Or.inr ⟨c'', h1, h2⟩

/-- A list is free of `p`, or splits at its first letter with `p`. -/
private theorem RH_first {α : Type*} (p : α → Bool) : ∀ l : List α,
    (∀ z ∈ l, p z = false) ∨ ∃ l₁ z l₂, l = l₁ ++ z :: l₂ ∧ p z = true ∧ ∀ x ∈ l₁, p x = false
  | [] => Or.inl (by simp)
  | x :: l => by
      cases hx : p x
      · rcases RH_first p l with h | ⟨l₁, z, l₂, rfl, hz, h1⟩
        · exact Or.inl fun z hz => by
            rcases List.mem_cons.1 hz with rfl | hz
            · exact hx
            · exact h z hz
        · exact Or.inr ⟨x :: l₁, z, l₂, rfl, hz, fun y hy => by
            rcases List.mem_cons.1 hy with rfl | hy
            · exact hx
            · exact h1 y hy⟩
      · exact Or.inr ⟨[], x, l, rfl, hx, by simp⟩

/-- A letter without `p` lies in a piece of `splitOnP p`. -/
private theorem RH_split_mem {α : Type*} (p : α → Bool) (x : α) (hx : p x = false) :
    ∀ l : List α, x ∈ l → ∃ s ∈ l.splitOnP p, x ∈ s
  | [], h => by simp at h
  | y :: l, h => by
      rw [List.splitOnP_cons_eq_ite_modifyHead]
      obtain ⟨s₀, L, hs⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p l)
      rcases List.mem_cons.1 h with rfl | h
      · rw [hx, hs]
        exact ⟨x :: s₀, by simp, by simp⟩
      · obtain ⟨s, hs', hxs⟩ := RH_split_mem p x hx l h
        cases hy : p y
        · rw [hs] at hs' ⊢
          rcases List.mem_cons.1 hs' with rfl | hs'
          · exact ⟨y :: s, by simp, by simp [hxs]⟩
          · exact ⟨s, by simp [hs'], hxs⟩
        · exact ⟨s, by simp [hs'], hxs⟩

/-! ### The entries of an expression -/

/-- Every letter of a word with a `Δ`, other than a `Δ`, lies in a package entry. -/
private theorem RH_lament (X : PkgExpr) (w : List PkgLetter) (hw : w ∈ X.loops)
    (hE : w.any PkgLetter.isEnt = true) (x : PkgLetter) (hx : x ∈ w) (hxE : x.isEnt = false) :
    ∃ e ∈ X.pents, x ∈ e.2.2 := by
  have hseg : ∃ σ ∈ pkgSegs w, x ∈ σ := by
    obtain ⟨P, u, v, Q, hP, rfl⟩ := PSh_exists_first_ent w hE
    rw [pkgSegs_first P Q u v hP]
    refine RH_split_mem _ x hxE _ ?_
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with h | rfl | h
    · exact Or.inr h
    · simp [PkgLetter.isEnt] at hxE
    · exact Or.inl h
  obtain ⟨σ, hσ, hxσ⟩ := hseg
  rw [← FW_pw_segs w hE] at hσ
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hσ
  exact ⟨e, by rw [FW_pents]; exact List.mem_flatMap.2 ⟨w, hw, he⟩, hxσ⟩

/-- The labels of the package entries are labels of letters `Δ` of the words. -/
private theorem RH_labels (X : PkgExpr) (k : ℕ)
    (h : ∀ w ∈ X.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < k ∧ v < k)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) : e.1 < k ∧ e.2.1 < k := by
  rw [FW_pents] at he
  obtain ⟨w, hw, he⟩ := List.mem_flatMap.1 he
  cases hE : w.any PkgLetter.isEnt
  · rw [FW_pw_free w hE] at he; simp at he
  · rw [FW_pw_eq w hE] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
    have hlen := PG_len w hE
    have ht' : t < (PG_E w).length := hlen ▸ List.mem_range.1 ht
    have hmemE : ∀ q ∈ PG_E w, PkgLetter.ent q.1 q.2 ∈ w := by
      intro q hq
      unfold PG_E at hq
      obtain ⟨z, hz, hzq⟩ := List.mem_filterMap.1 hq
      rcases z with _ | ⟨u, v⟩
      · simp at hzq
      · simp only [Option.some.injEq] at hzq
        subst hzq
        exact List.mem_rotate.1 hz
    have hget : ∀ i, i < (PG_E w).length → (PG_E w).getD i (0, 0) ∈ PG_E w := fun i hi => by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    have h1 := hmemE _ (hget t ht')
    have h2 := hmemE _ (hget ((t + 1) % (PG_E w).length) (Nat.mod_lt _ (by omega)))
    exact ⟨(h w hw _ _ h1).2, (h w hw _ _ h2).1⟩

/-- `freeTwo` is a package entry without `Λ̃` with two resolvents. -/
private theorem RH_freeTwo (X : PkgExpr) : X.freeTwo = true ↔
    ∃ e ∈ X.pents, e.2.2.any PkgLetter.isLam = false ∧ 2 ≤ e.2.2.countP PkgLetter.isRes := by
  unfold PkgExpr.freeTwo
  rw [List.any_eq_true, FW_pents]
  constructor
  · rintro ⟨w, hw, h⟩
    rw [Bool.and_eq_true] at h
    obtain ⟨hE, h⟩ := h
    obtain ⟨σ, hσ, h⟩ := List.any_eq_true.1 h
    rw [← FW_pw_segs w hE] at hσ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hσ
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
    exact ⟨e, List.mem_flatMap.2 ⟨w, hw, he⟩, h⟩
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨w, hw, he⟩ := List.mem_flatMap.1 he
    cases hE : w.any PkgLetter.isEnt
    · rw [FW_pw_free w hE] at he; simp at he
    · refine ⟨w, hw, ?_⟩
      rw [hE, Bool.true_and, List.any_eq_true, ← FW_pw_segs w hE]
      exact ⟨e.2.2, List.mem_map_of_mem he, by simp [h1, h2]⟩

/-- Under `wf`, a package entry holds `Λ̃_o` at most once. -/
private theorem RH_count (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) : e.2.2.count (.lw (.lamt o)) ≤ 1 := by
  obtain ⟨w, hwL, hwE, hσw⟩ := FW_mem_pents X e he
  obtain ⟨-, M, hrot, -⟩ := FW_seg_cyc w e.2.2 hwE hσw
  have hc1 := FW_count_le X hX o w hwL
  have hcw := hrot.perm.count_eq (.lw (.lamt o))
  rw [List.count_append] at hcw
  omega

/-! ### The sides of `Λ̃` -/

/-- The sides of `Λ̃_o` in its package entry `P Λ̃_o Q`: the runs of `Q` and of `P` reversed. -/
private theorem RH_sides (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) (P Q : List PkgLetter) (hσ : e.2.2 = P ++ .lw (.lamt o) :: Q) :
    X.lamSide o true = FW_run Q ∧ X.lamSide o false = FW_run P.reverse := by
  obtain ⟨w, hwL, hwE, hσw⟩ := FW_mem_pents X e he
  obtain ⟨-, M, hrot, ⟨u, v, M₁, hM₁⟩, ⟨u', v', M₂, hM₂⟩⟩ := FW_seg_cyc w e.2.2 hwE hσw
  have hc1 := FW_count_le X hX o w hwL
  have hcw := hrot.perm.count_eq (.lw (.lamt o))
  rw [hσ] at hcw
  simp only [List.count_append, List.count_cons_self] at hcw
  have h1 : PkgLetter.lw (.lamt o) ∉ P := List.count_eq_zero.1 (by omega)
  have h2 : PkgLetter.lw (.lamt o) ∉ Q := List.count_eq_zero.1 (by omega)
  have h3 : PkgLetter.lw (.lamt o) ∉ M := List.count_eq_zero.1 (by omega)
  have hmem : PkgLetter.lw (.lamt o) ∈ w := hrot.perm.symm.subset (by rw [hσ]; simp)
  have hsum := (FW_wf_count X hX o).le
  rw [FW_lamSide_mem X o false hsum w hwL hmem, FW_lamSide_mem X o true hsum w hwL hmem]
  have hcyc : w ~r (.lw (.lamt o) :: (Q ++ M ++ P)) := by
    refine hrot.trans ?_
    rw [hσ]
    have e1 : P ++ PkgLetter.lw (.lamt o) :: Q ++ M = P ++ (.lw (.lamt o) :: (Q ++ M)) := by simp
    rw [e1]
    refine List.isRotated_append.trans ?_
    simp only [List.cons_append, List.append_assoc]
    exact List.IsRotated.refl _
  obtain ⟨hR, hL⟩ := FW_wside_cyc w _ o hcyc (by simp [h1, h2, h3])
  rw [hR, hL]
  have hM0 : FW_run (M ++ P) = FW_run [] := by
    rw [hM₁, List.cons_append, FW_go_ent, FW_run_nil]
  have hM0' : FW_run (M.reverse ++ Q.reverse) = FW_run [] := by
    rw [hM₂]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [FW_go_ent, FW_run_nil]
  constructor
  · have := FW_run_congr _ _ hM0 Q
    rw [List.append_nil] at this
    rw [List.append_assoc]; exact this
  · have := FW_run_congr _ _ hM0' P.reverse
    rw [List.append_nil] at this
    simp only [List.reverse_append, List.append_assoc]; exact this

/-- A list without resolvents has the run `0`. -/
private theorem RH_run_zero (l : List PkgLetter) (hl : ∀ z ∈ l, z.isRes = false) :
    FW_run l = 0 := by
  unfold FW_run
  exact List.countP_eq_zero.2 fun z hz => by
    simp [hl z ((List.takeWhile_sublist _).subset hz)]

/-- A letter `Λ̃_o` in a word without resolvents has both sides `0`. -/
private theorem RH_side_zero (X : PkgExpr) (hX : X.wf = true) (w : List PkgLetter)
    (hw : w ∈ X.loops) (o : Fin 2) (ho : PkgLetter.lw (.lamt o) ∈ w)
    (hres : ∀ z ∈ w, z.isRes = false) (s : Bool) : X.lamSide o s = 0 := by
  rw [FW_lamSide_mem X o s (FW_wf_count X hX o).le w hw ho]
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ho
  have hc := FW_count_le X hX o _ hw
  simp only [List.count_append, List.count_cons_self] at hc
  have hA : PkgLetter.lw (.lamt o) ∉ A := List.count_eq_zero.1 (by omega)
  obtain ⟨hR, hL⟩ := FW_wside_split A B o hA
  have hBA : ∀ z ∈ B ++ A, z.isRes = false := fun z hz => hres z (by
    simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
  cases s
  · rw [hL]; exact RH_run_zero _ fun z hz => hBA z (List.mem_reverse.1 hz)
  · rw [hR]; exact RH_run_zero _ hBA

/-- The side of `pkgSeek` is empty exactly when the search finds no resolvent. -/
private theorem RH_seek (w : List PkgLetter) (o : Fin 2) (b : Bool) :
    FW_wside w o b = 0 ↔ pkgSeek w (w.idxOf (.lw (.lamt o))) b = none := by
  unfold FW_wside pkgSeek
  rw [List.countP_eq_zero, List.find?_eq_none]
  exact Iff.rfl

/-! ### The parts of a segment and the role of its entry -/

/-- The segment starts with a resolvent. -/
private def RH_hr (σ : List PkgLetter) : Prop :=
  ∃ (b : Fin 2) (t : List PkgLetter), σ = .lw (.res b) :: t

/-- The segment ends with a resolvent. -/
private def RH_lr (σ : List PkgLetter) : Prop :=
  ∃ (b : Fin 2) (t : List PkgLetter), σ = t ++ [.lw (.res b)]

/-- An inner label of an entry has a resolvent next to it in the segment. -/
private def RH_K (e : ℕ × ℕ × List PkgLetter) : Prop :=
  (2 ≤ e.1 → RH_hr e.2.2) ∧ (2 ≤ e.2.1 → RH_lr e.2.2)

private theorem RH_parts_hr (σ : List PkgLetter) (h : RH_hr σ) :
    ∃ k, (pkgParts σ).head? = some (k + 1) := by
  obtain ⟨b, t, rfl⟩ := h
  unfold pkgParts
  rw [List.splitOnP_cons_eq_ite_modifyHead]
  obtain ⟨s₀, L, hs⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil PkgLetter.isLam t)
  rw [hs]
  refine ⟨s₀.countP PkgLetter.isRes, ?_⟩
  simp only [PkgLetter.isLam, Bool.false_eq_true, ↓reduceIte, List.modifyHead_cons, List.map_cons,
    List.head?_cons, Option.some.injEq]
  exact List.countP_cons_of_pos rfl

private theorem RH_parts_lr (σ : List PkgLetter) (h : RH_lr σ) :
    ∃ k, (pkgParts σ).getLast? = some (k + 1) := by
  obtain ⟨b, t, rfl⟩ := h
  obtain ⟨L, sl, L₁, hs, hl, hL₁, hsl⟩ := FW_split_last PkgLetter.isLam (t ++ [.lw (.res b)])
  unfold pkgParts
  rw [hs]
  have hmem : PkgLetter.lw (.res b) ∈ sl := by
    rcases List.eq_nil_or_concat sl with rfl | ⟨sl', z, rfl⟩
    · exfalso
      rw [List.append_nil] at hl
      rcases hL₁ with rfl | ⟨L₁', y, rfl, hy⟩
      · simp at hl
      · have := congrArg List.getLast? hl
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.some.injEq] at this
        rw [← this] at hy
        simp [PkgLetter.isLam] at hy
    · have := congrArg List.getLast? hl
      simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, Option.some.injEq] at this ⊢
      rw [this]; simp
  have hpos := List.countP_pos_iff.2 ⟨_, hmem, (rfl : PkgLetter.isRes (.lw (.res b)) = true)⟩
  refine ⟨sl.countP PkgLetter.isRes - 1, ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.some.injEq]
  omega

/-- A segment `P y Q` with a letter `Λ̃` at `y` and no resolvent in `Q`: two parts at least, the
last one `0`. -/
private theorem RH_parts_last (σ P Q : List PkgLetter) (y : PkgLetter) (hy : y.isLam = true)
    (hσ : σ = P ++ y :: Q) (hQ : ∀ z ∈ Q, z.isRes = false) :
    2 ≤ (pkgParts σ).length ∧ (pkgParts σ).getLast? = some 0 := by
  unfold pkgParts
  rw [hσ, List.splitOnP_append_cons _ _ hy]
  obtain ⟨L, sl, L₁, hs, hl, -, -⟩ := FW_split_last PkgLetter.isLam Q
  obtain ⟨s₀, L₀, h0⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil PkgLetter.isLam P)
  rw [hs, h0]
  have hc : sl.countP PkgLetter.isRes = 0 := List.countP_eq_zero.2 fun z hz => by
    simp [hQ z (by rw [hl]; exact List.mem_append_right _ hz)]
  refine ⟨by simp; omega, ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, hc]

/-- A segment `P y Q` with a letter `Λ̃` at `y` and no resolvent in `P`: two parts at least, the
first one `0`. -/
private theorem RH_parts_head (σ P Q : List PkgLetter) (y : PkgLetter) (hy : y.isLam = true)
    (hσ : σ = P ++ y :: Q) (hP : ∀ z ∈ P, z.isRes = false) :
    2 ≤ (pkgParts σ).length ∧ (pkgParts σ).head? = some 0 := by
  unfold pkgParts
  rw [hσ, List.splitOnP_append_cons _ _ hy]
  obtain ⟨s₀, rest, hs, ⟨L₂, hP', -⟩, -, -⟩ := FW_split_struct PkgLetter.isLam P
  obtain ⟨s₁, L₁, h1⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil PkgLetter.isLam Q)
  rw [hs, h1]
  have hc : s₀.countP PkgLetter.isRes = 0 := List.countP_eq_zero.2 fun z hz => by
    simp [hP z (by rw [hP']; exact List.mem_append_left _ hz)]
  refine ⟨by simp; omega, ?_⟩
  simp [hc]

/-- The role `0` of an entry datum. -/
private theorem RH_role0 (d : FEnt) : FEnt.role d = 0 ↔ 2 ≤ d.2.2.1.length ∧
    ((d.2.2.1.head? = some 0 ∧ 2 ≤ d.1) ∨ (d.2.2.1.getLast? = some 0 ∧ 2 ≤ d.2.1)) := by
  unfold FEnt.role fInnerL
  split_ifs with h1 h2 h3 <;> simp_all

/-- The factor of a package entry has an entry datum. -/
private theorem RH_ent (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) :
    ∃ d, (X.rent e).entData = some d := by
  have h := FW_g_isSome X (FW_mk X.fpm e)
  rw [← FW_rent] at h
  exact Option.isSome_iff_exists.1 (by rw [h]; rfl)

private theorem RH_getD (l : List ℕ) (t : ℕ) (ht : t < l.length) : l[t]? = some (l.getD t 0) := by
  rw [List.getD_eq_getElem _ _ ht, List.getElem?_eq_getElem ht]

/-- An entry with a resolvent next to each inner label does not have role `0`. -/
private theorem RH_role_K (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents)
    (hK : RH_K e) (d : FEnt) (hd : (X.rent e).entData = some d) : FEnt.role d ≠ 0 := by
  obtain ⟨hx, hy, hlen, hp⟩ := pkg_rent_parts X e he d hd
  intro h0
  obtain ⟨-, h⟩ := (RH_role0 d).1 h0
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨k, hk⟩ := RH_parts_hr _ (hK.1 (hx ▸ h2))
    have hl : 0 < (pkgParts e.2.2).length := by
      rcases h : pkgParts e.2.2 with _ | _ <;> simp_all
    have a1 := RH_getD _ 0 hl
    have a2 := RH_getD d.2.2.1 0 (by rw [hlen]; exact hl)
    rw [← List.head?_eq_getElem?, hk] at a1
    rw [← List.head?_eq_getElem?, h1] at a2
    have := (hp 0 hl).1
    simp only [Option.some.injEq] at a1 a2
    omega
  · obtain ⟨k, hk⟩ := RH_parts_lr _ (hK.2 (hy ▸ h2))
    have hl : 0 < (pkgParts e.2.2).length := by
      rcases h : pkgParts e.2.2 with _ | _ <;> simp_all
    have a1 := RH_getD _ _ (Nat.sub_lt hl Nat.one_pos)
    have a2 := RH_getD d.2.2.1 ((pkgParts e.2.2).length - 1)
      (by rw [hlen]; exact Nat.sub_lt hl Nat.one_pos)
    have e2 : d.2.2.1.getLast? = d.2.2.1[(pkgParts e.2.2).length - 1]? := by
      rw [List.getLast?_eq_getElem?, hlen]
    rw [← List.getLast?_eq_getElem?, hk] at a1
    rw [← e2, h1] at a2
    have := (hp _ (Nat.sub_lt hl Nat.one_pos)).1
    simp only [Option.some.injEq] at a1 a2
    omega

/-- The `Λ̃`-half ending at an inner label, with no resolvent after a letter `Λ̃`, has role `0` and
last part `0`. -/
private theorem RH_role_R (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents)
    (hy : 2 ≤ e.2.1) (P Q : List PkgLetter) (o : Fin 2) (hσ : e.2.2 = P ++ .lw (.lamt o) :: Q)
    (hQ : ∀ z ∈ Q, z.isRes = false) :
    ∃ d, (X.rent e).entData = some d ∧ FEnt.role d = 0 ∧ d.2.2.1.getLast? = some 0 := by
  obtain ⟨d, hd⟩ := RH_ent X e
  obtain ⟨-, hy', hlen, hp⟩ := pkg_rent_parts X e he d hd
  obtain ⟨h2, hl0⟩ := RH_parts_last _ P Q _ rfl hσ hQ
  have hl : 0 < (pkgParts e.2.2).length := by omega
  have a1 := RH_getD _ _ (Nat.sub_lt hl Nat.one_pos)
  rw [← List.getLast?_eq_getElem?, hl0] at a1
  simp only [Option.some.injEq] at a1
  have h0 := (hp _ (Nat.sub_lt hl Nat.one_pos)).2.2 a1.symm
  have a2 := RH_getD d.2.2.1 ((pkgParts e.2.2).length - 1)
    (by rw [hlen]; exact Nat.sub_lt hl Nat.one_pos)
  have e2 : d.2.2.1.getLast? = d.2.2.1[(pkgParts e.2.2).length - 1]? := by
    rw [List.getLast?_eq_getElem?, hlen]
  rw [h0, ← e2] at a2
  exact ⟨d, hd, (RH_role0 d).2 ⟨hlen ▸ h2, Or.inr ⟨a2, hy' ▸ hy⟩⟩, a2⟩

/-- The `Λ̃`-half starting at an inner label, with no resolvent before a letter `Λ̃`, has role `0`
and first part `0`. -/
private theorem RH_role_L (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents)
    (hx : 2 ≤ e.1) (P Q : List PkgLetter) (o : Fin 2) (hσ : e.2.2 = P ++ .lw (.lamt o) :: Q)
    (hP : ∀ z ∈ P, z.isRes = false) :
    ∃ d, (X.rent e).entData = some d ∧ FEnt.role d = 0 ∧ d.2.2.1.head? = some 0 := by
  obtain ⟨d, hd⟩ := RH_ent X e
  obtain ⟨hx', -, hlen, hp⟩ := pkg_rent_parts X e he d hd
  obtain ⟨h2, hl0⟩ := RH_parts_head _ P Q _ rfl hσ hP
  have hl : 0 < (pkgParts e.2.2).length := by omega
  have a1 := RH_getD _ 0 hl
  rw [← List.head?_eq_getElem?, hl0] at a1
  simp only [Option.some.injEq] at a1
  have h0 := (hp 0 hl).2.2 a1.symm
  have a2 := RH_getD d.2.2.1 0 (by rw [hlen]; exact hl)
  rw [h0, ← List.head?_eq_getElem?] at a2
  exact ⟨d, hd, (RH_role0 d).2 ⟨hlen ▸ h2, Or.inl ⟨a2, hx' ▸ hx⟩⟩, a2⟩

/-- The count of a property of the entry data of `rfacs`, over the package entries. -/
private theorem RH_cnt (X : PkgExpr) (p : FEnt → Bool) :
    (X.rfacs.filterMap FFac.entData).countP p =
      X.pents.countP fun e => ((X.rent e).entData.map p).getD false := by
  have h1 : X.rfacs.filterMap FFac.entData =
      (X.rfacs.filter fun f => f.entData.isSome).filterMap FFac.entData := by
    rw [List.filterMap_filter]
    refine List.filterMap_congr fun x _ => ?_
    cases h : x.entData <;> simp
  rw [h1, pkg_rfacs_pents, List.filterMap_map, List.countP_filterMap]
  rfl

/-! ### The three statements on one expression -/

private theorem RH_isEntP (z : PkgLetter) : isEntP z = z.isEnt := by
  rcases z with _ | _ <;> rfl

/-- A letter `Λ̃` is `Λ̃_o` or `Λ̃_{1-o}`. -/
private theorem RH_lam (z : PkgLetter) (hz : z.isLam = true) (o : Fin 2) :
    z = .lw (.lamt o) ∨ z = .lw (.lamt (1 - o)) := by
  rcases z with ((b | b | y | o') | ⟨u, v⟩) <;> simp [PkgLetter.isLam] at hz
  fin_cases o <;> fin_cases o' <;> simp

/-- The sides of a letter `Λ̃_o` alone in a word without `Δ` are its resolvents. -/
private theorem RH_lamSide_free (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : w.contains (.lw (.lamt o)) = true)
    (hfree : w.any PkgLetter.isEnt = false) (h1 : w.contains (.lw (.lamt (1 - o))) = false)
    (right : Bool) : R.lamSide o right = w.countP PkgLetter.isRes := by
  have ho' : PkgLetter.lw (.lamt o) ∈ w := by simpa using ho
  have h1' : PkgLetter.lw (.lamt (1 - o)) ∉ w := by simpa using h1
  rw [FW_lamSide_mem R o right (FW_wf_count R hR o).le w hw ho']
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ho'
  have hc := FW_count_le R hR o _ hw
  simp only [List.count_append, List.count_cons_self] at hc
  have hA : PkgLetter.lw (.lamt o) ∉ A := List.count_eq_zero.1 (by omega)
  have hB : PkgLetter.lw (.lamt o) ∉ B := List.count_eq_zero.1 (by omega)
  obtain ⟨hR', hL'⟩ := FW_wside_split A B o hA
  have hgo : ∀ z ∈ B ++ A, FW_go z = true := by
    intro z hz
    have hzw : z ∈ A ++ .lw (.lamt o) :: B := by
      simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
    have hzE : z.isEnt = false := by
      have := List.any_eq_false.1 hfree z hzw; simpa using this
    have hzL : z.isLam = false := by
      cases hl : z.isLam
      · rfl
      · rcases RH_lam z hl o with rfl | rfl
        · simp only [List.mem_append] at hz; tauto
        · exact absurd hzw h1'
    simp [FW_go, hzE, hzL]
  have hcnt : (A ++ PkgLetter.lw (.lamt o) :: B).countP PkgLetter.isRes =
      (B ++ A).countP PkgLetter.isRes := by
    simp only [List.countP_append, List.countP_cons]
    simp [PkgLetter.isRes]; omega
  rw [hcnt]
  cases right
  · rw [hL', ← List.append_nil (B ++ A).reverse,
      FW_run_go _ (fun z hz => hgo z (List.mem_reverse.1 hz)), FW_run_nil, List.countP_reverse]
    simp
  · rw [hR', ← List.append_nil (B ++ A), FW_run_go _ hgo, FW_run_nil]
    simp

/-- The side chosen by the rules has a resolvent. -/
private theorem RH_ffocusSide_pos (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) (side : Bool)
    (h : R.ffocusSide = some (o, side)) : 1 ≤ R.lamSide o side := by
  have hs := (pkg_ffocusSide R).1
  rw [h] at hs
  obtain ⟨⟨ℓ, r, b⟩, hf⟩ := Option.isSome_iff_exists.1 hs.symm
  obtain ⟨o', w, hw, ho', hseek, hs'⟩ := FW_focus R ℓ r b hf
  rw [h, Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  rw [FW_lamSide_mem R o side (FW_wf_count R hR o).le w (List.mem_of_getElem? hw) ho']
  by_contra hlt
  have h0 := (RH_seek w o side).1 (by omega)
  rw [hseek] at h0
  simp at h0

/-- The expanded word of the further expansion on the package entries, with the letter `Λ̃_o` of
the chosen side: to the right, the half ending at label `3` is `A Λ̃_o X 𝔐_a` with no resolvent in
`X`; to the left, the half starting at label `2` is `𝔐_a X Λ̃_o B` with no resolvent in `X`. The
half with `Λ̃_o` is listed first. -/
private theorem RH_fpkg (R : PkgExpr) (o : Fin 2) (side : Bool)
    (hs : R.ffocusSide = some (o, side)) :
    (side = true →
      (∃ e ∈ R.pents, ∃ (A X B : List PkgLetter) (a : Fin 2), (∀ z ∈ X, z.isRes = false) ∧
        e.2.2 = A ++ .lw (.lamt o) :: (X ++ .lw (.res a) :: B) ∧
        R.fpkg.pents.Perm ((e.1, 3, A ++ .lw (.lamt o) :: (X ++ [.lw (.det a)])) ::
          (R.pents.erase e ++ [(2, e.2.1, .lw (.res a) :: B)]))) ∨
      (∃ (Y X : List PkgLetter) (a : Fin 2), (∀ z ∈ X, z.isRes = false) ∧
        R.fpkg.pents.Perm
          ((2, 3, (.lw (.res a) :: Y) ++ .lw (.lamt o) :: (X ++ [.lw (.det a)])) :: R.pents))) ∧
    (side = false →
      (∃ e ∈ R.pents, ∃ (A X B : List PkgLetter) (a : Fin 2), (∀ z ∈ X, z.isRes = false) ∧
        e.2.2 = A ++ .lw (.res a) :: (X ++ .lw (.lamt o) :: B) ∧
        R.fpkg.pents.Perm ((2, e.2.1, (.lw (.det a) :: X) ++ .lw (.lamt o) :: B) ::
          (R.pents.erase e ++ [(e.1, 3, A ++ [.lw (.res a)])]))) ∨
      (∃ (X Y : List PkgLetter) (a : Fin 2), (∀ z ∈ X, z.isRes = false) ∧
        R.fpkg.pents.Perm
          ((2, 3, (.lw (.det a) :: X) ++ .lw (.lamt o) :: (Y ++ [.lw (.res a)])) :: R.pents))) := by
  have hsome := (pkg_ffocusSide R).1
  rw [hs] at hsome
  obtain ⟨⟨ℓ, r, b⟩, hf⟩ := Option.isSome_iff_exists.1 hsome.symm
  obtain ⟨o', w, hw, ho', hseek, hs'⟩ := FW_focus R ℓ r b hf
  rw [hs, Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  obtain ⟨a, tl, hrot, hR', hL'⟩ := FH_shape w _ r side o (List.getElem?_idxOf ho') hseek
  obtain ⟨-, -, -, hND⟩ := pkg_fpkg_pents R ℓ r side hf w hw a tl hrot
  obtain ⟨hl, -, -⟩ := RS_fpkg R ℓ r side w a tl hf hw hrot
  have hp := RS_flat R.loops RS_pw ℓ w hw
  rw [← RS_pents] at hp
  refine ⟨fun hside => ?_, fun hside => ?_⟩
  · subst hside
    obtain ⟨Y, X, hYX, hX⟩ := hR' rfl
    cases hE : w.any PkgLetter.isEnt
    · right
      refine ⟨Y, X, a, fun z hz => (hX z hz).2, ?_⟩
      refine (hND hE).trans ?_
      rw [hYX]
      refine List.perm_append_comm.trans ?_
      simp
    · left
      have hrE : (w.rotate r).any PkgLetter.isEnt = true := by
        rw [(List.rotate_perm w r).any_eq]; exact hE
      rw [hrot] at hrE
      have htl : tl.any PkgLetter.isEnt = true := by simpa [PkgLetter.isEnt] using hrE
      have hY : Y.any PkgLetter.isEnt = true := by
        rw [hYX, List.any_append] at htl
        have hX' : (PkgLetter.lw (.lamt o) :: X).any PkgLetter.isEnt = false :=
          List.any_eq_false.2 fun z hz => by
            rcases List.mem_cons.1 hz with rfl | hz
            · simp [PkgLetter.isEnt]
            · have h' : z.isEnt = false := by rw [← RH_isEntP]; exact (hX z hz).1
              simp [h']
        rw [hX', Bool.or_false] at htl
        exact htl
      have hPf : ∀ z ∈ PkgLetter.lw (.lamt o) :: X, z.isEnt = false := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · rfl
        · rw [← RH_isEntP]; exact (hX z hz).1
      obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut Y (.lw (.lamt o) :: X) hY
      rw [← hYX] at hcut
      obtain ⟨L, vl, σ, k1, k2⟩ := RS_core a (.lw (.res a)) (.lw (.det a)) rfl rfl 3 2 p q B Z
        (.lw (.lamt o) :: X) hB hPf
      rw [← hcut] at k1 k2
      have hrw := RS_pw_rot w hE r
      rw [hrot] at hrw
      have hp' : R.fpkg.pents.Perm
          (RS_pw ((.lw (.res a) :: tl) ++ [.lw (.det a), .ent 3 2]) ++
            (R.loops.eraseIdx ℓ).flatMap RS_pw) := by
        rw [RS_pents, hl]
        have e : (if true = true then PkgLetter.lw (.res a) :: tl ++ [.lw (.det a)]
            else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2] =
            (.lw (.res a) :: tl) ++ [.lw (.det a), .ent 3 2] := by simp
        rw [e]
        exact RS_flat_set _ _ ℓ _ _ hw
      obtain ⟨hmem, hperm⟩ := RS_swap R.pents R.fpkg.pents L _ _
        (vl, p, σ ++ (.lw (.lamt o) :: X) ++ .lw (.res a) :: B)
        (hp.trans ((hrw.symm.trans k1).append_right _)) (hp'.trans (k2.append_right _))
      refine ⟨_, hmem, σ, X, B, a, fun z hz => (hX z hz).2, by simp, ?_⟩
      refine hperm.trans ?_
      have e : (vl, 3, σ ++ (PkgLetter.lw (.lamt o) :: X) ++ [PkgLetter.lw (.det a)]) =
          (vl, 3, σ ++ .lw (.lamt o) :: (X ++ [.lw (.det a)])) := by simp
      rw [e]
      exact List.perm_middle
  · subst hside
    obtain ⟨X, Y, hXY, hX⟩ := hL' rfl
    cases hE : w.any PkgLetter.isEnt
    · right
      refine ⟨X, Y, a, fun z hz => (hX z hz).2, ?_⟩
      refine (hND hE).trans ?_
      rw [hXY]
      refine List.perm_append_comm.trans ?_
      simp
    · left
      have hrE : (w.rotate r).any PkgLetter.isEnt = true := by
        rw [(List.rotate_perm w r).any_eq]; exact hE
      rw [hrot] at hrE
      have htl : tl.any PkgLetter.isEnt = true := by simpa [PkgLetter.isEnt] using hrE
      obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut tl [] htl
      rw [List.append_nil] at hcut
      obtain ⟨L, vl, σ, k1, k2⟩ := RS_core a (.lw (.det a)) (.lw (.res a)) rfl rfl 3 2 p q B Z []
        hB (by simp)
      simp only [List.append_nil] at k1 k2 hcut
      rw [← hcut] at k1 k2
      have hrw := RS_pw_rot w hE r
      rw [hrot] at hrw
      have hp' : R.fpkg.pents.Perm
          (RS_pw ((.lw (.det a) :: tl) ++ [.lw (.res a), .ent 3 2]) ++
            (R.loops.eraseIdx ℓ).flatMap RS_pw) := by
        rw [RS_pents, hl]
        have e : (if false = true then PkgLetter.lw (.res a) :: tl ++ [.lw (.det a)]
            else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2] =
            (.lw (.det a) :: tl) ++ [.lw (.res a), .ent 3 2] := by simp
        rw [e]
        exact RS_flat_set _ _ ℓ _ _ hw
      obtain ⟨hmem, hperm⟩ := RS_swap R.pents R.fpkg.pents L _ _ (vl, p, σ ++ .lw (.res a) :: B)
        (hp.trans ((hrw.symm.trans k1).append_right _)) (hp'.trans (k2.append_right _))
      have hBX : ∃ M, B = X ++ .lw (.lamt o) :: M := by
        rw [hXY] at hcut
        rcases RH_cut B Z X Y (.ent p q) (.lw (.lamt o)) (by simp) hcut.symm with
          ⟨M, h1, -⟩ | ⟨M, h1, -⟩
        · exfalso
          have := (hX (.ent p q) (by rw [h1]; simp)).1
          simp [isEntP] at this
        · exact ⟨M, h1⟩
      obtain ⟨M, rfl⟩ := hBX
      refine ⟨_, hmem, σ, X, M, a, fun z hz => (hX z hz).2, rfl, ?_⟩
      refine hperm.trans ?_
      have e : (2, p, PkgLetter.lw (.det a) :: (X ++ PkgLetter.lw (.lamt o) :: M)) =
          (2, p, (.lw (.det a) :: X) ++ .lw (.lamt o) :: M) := by simp
      rw [e, show ∀ (l : List (ℕ × ℕ × List PkgLetter)) x y, l ++ [x, y] = (l ++ [x]) ++ [y] from
        fun l x y => by simp]
      refine List.perm_append_comm.trans ?_
      simp

/-! ### One derivative on the package entries -/

/-- An entry kept by a derivative that cuts another entry `c`, and the other entries after it. -/
private theorem RH_keep {α : Type*} [BEq α] [LawfulBEq α] (L L' N : List α) (c e : α)
    (hL' : L'.Perm (L.erase c ++ N)) (he : e ∈ L) (hne : e ≠ c) :
    e ∈ L' ∧ ∀ x ∈ L'.erase e, x ∈ L.erase e ∨ x ∈ N := by
  have h1 : e ∈ L.erase c := (List.mem_erase_of_ne hne).2 he
  have h2 : L'.Perm (e :: ((L.erase c).erase e ++ N)) :=
    hL'.trans (((List.perm_cons_erase h1).append_right N).trans (by simp))
  refine ⟨h2.symm.subset List.mem_cons_self, fun x hx => ?_⟩
  have h3 := h2.erase e
  rw [List.erase_cons_head] at h3
  rcases List.mem_append.1 (h3.subset hx) with hx | hx
  · rw [List.erase_comm] at hx
    exact Or.inl (List.mem_of_mem_erase hx)
  · exact Or.inr hx

/-- An entry kept by a derivative that adds new entries, and the other entries after it. -/
private theorem RH_keep' {α : Type*} [BEq α] [LawfulBEq α] (L L' N : List α) (e : α)
    (hL' : L'.Perm (L ++ N)) (he : e ∈ L) :
    e ∈ L' ∧ ∀ x ∈ L'.erase e, x ∈ L.erase e ∨ x ∈ N := by
  have h2 : L'.Perm (e :: (L.erase e ++ N)) :=
    hL'.trans (((List.perm_cons_erase he).append_right N).trans (by simp))
  refine ⟨h2.symm.subset List.mem_cons_self, fun x hx => ?_⟩
  have h3 := h2.erase e
  rw [List.erase_cons_head] at h3
  exact List.mem_append.1 (h3.subset hx)

/-- The two pieces of a cut entry, and the other entries after each of them. -/
private theorem RH_new {α : Type*} [BEq α] [LawfulBEq α] (L L' : List α) (c p₁ p₂ : α)
    (hL' : L'.Perm (L.erase c ++ [p₁, p₂])) :
    p₁ ∈ L' ∧ p₂ ∈ L' ∧ (∀ x ∈ L'.erase p₂, x ∈ L.erase c ∨ x = p₁) ∧
      (∀ x ∈ L'.erase p₁, x ∈ L.erase c ∨ x = p₂) := by
  have h1 : L'.Perm (p₂ :: (L.erase c ++ [p₁])) := by
    refine hL'.trans ?_
    rw [show L.erase c ++ [p₁, p₂] = (L.erase c ++ [p₁]) ++ [p₂] by simp]
    exact List.perm_append_comm.trans (by simp)
  have h2 : L'.Perm (p₁ :: (L.erase c ++ [p₂])) := hL'.trans List.perm_middle
  refine ⟨h2.symm.subset List.mem_cons_self, h1.symm.subset List.mem_cons_self,
    fun x hx => ?_, fun x hx => ?_⟩
  · have h3 := h1.erase p₂
    rw [List.erase_cons_head] at h3
    rcases List.mem_append.1 (h3.subset hx) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (List.mem_singleton.1 hx)
  · have h3 := h2.erase p₁
    rw [List.erase_cons_head] at h3
    rcases List.mem_append.1 (h3.subset hx) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (List.mem_singleton.1 hx)

private theorem RH_hr_cut (A B : List PkgLetter) (b : Fin 2) (h : RH_hr (A ++ .lw (.res b) :: B)) :
    RH_hr (A ++ [.lw (.res b)]) := by
  rcases A with _ | ⟨x, A⟩
  · exact ⟨b, [], rfl⟩
  · obtain ⟨b', t, h⟩ := h
    simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨b', A ++ [.lw (.res b)], by rw [h.1]; rfl⟩

private theorem RH_lr_cut (A B : List PkgLetter) (b : Fin 2) (h : RH_lr (A ++ .lw (.res b) :: B)) :
    RH_lr (.lw (.res b) :: B) := by
  rcases List.eq_nil_or_concat B with rfl | ⟨B', z, rfl⟩
  · exact ⟨b, [], rfl⟩
  · obtain ⟨b', t, h⟩ := h
    have h' : (A ++ .lw (.res b) :: B') ++ [z] = t ++ [.lw (.res b')] := by simpa using h
    have hz := (List.append_inj' h' rfl).2
    simp only [List.cons.injEq, and_true] at hz
    subst hz
    exact ⟨b', .lw (.res b) :: B', by simp⟩

/-- The pieces of a cut entry with a resolvent next to each inner label keep it. -/
private theorem RH_K_cut (c : ℕ × ℕ × List PkgLetter) (A B : List PkgLetter) (b : Fin 2)
    (hc : c.2.2 = A ++ .lw (.res b) :: B) (u v : ℕ) :
    ((2 ≤ c.1 → RH_hr c.2.2) → RH_K (c.1, u, A ++ [.lw (.res b)])) ∧
      ((2 ≤ c.2.1 → RH_lr c.2.2) → RH_K (v, c.2.1, .lw (.res b) :: B)) := by
  refine ⟨fun h => ⟨fun hx => RH_hr_cut A B b (hc ▸ h hx), fun _ => ⟨b, A, rfl⟩⟩,
    fun h => ⟨fun _ => ⟨b, B, rfl⟩, fun hy => RH_lr_cut A B b (hc ▸ h hy)⟩⟩

/-- One derivative: every entry has an end piece at each of its two ends. -/
private theorem RH_pc_step (X X' : PkgExpr) (u v : ℕ) (hu : 2 ≤ u ∧ u < 4) (hv : 2 ≤ v ∧ v < 4)
    (h : X' ∈ X.dent u v) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) :
    (∃ e' ∈ X'.pents, e'.1 = e.1 ∧ e'.2.2 <+: e.2.2 ∧ ((e'.2.1 = e.2.1 ∧ e'.2.2 = e.2.2) ∨
        (2 ≤ e'.2.1 ∧ e'.2.1 < 4 ∧ e'.2.2.getLast?.map PkgLetter.isRes = some true))) ∧
    (∃ e' ∈ X'.pents, e'.2.1 = e.2.1 ∧ e'.2.2 <:+ e.2.2 ∧ ((e'.1 = e.1 ∧ e'.2.2 = e.2.2) ∨
        (2 ≤ e'.1 ∧ e'.1 < 4 ∧ e'.2.2.head?.map PkgLetter.isRes = some true))) := by
  have stay : e ∈ X'.pents →
      (∃ e' ∈ X'.pents, e'.1 = e.1 ∧ e'.2.2 <+: e.2.2 ∧ ((e'.2.1 = e.2.1 ∧ e'.2.2 = e.2.2) ∨
        (2 ≤ e'.2.1 ∧ e'.2.1 < 4 ∧ e'.2.2.getLast?.map PkgLetter.isRes = some true))) ∧
      (∃ e' ∈ X'.pents, e'.2.1 = e.2.1 ∧ e'.2.2 <:+ e.2.2 ∧ ((e'.1 = e.1 ∧ e'.2.2 = e.2.2) ∨
        (2 ≤ e'.1 ∧ e'.1 < 4 ∧ e'.2.2.head?.map PkgLetter.isRes = some true))) := fun hm =>
    ⟨⟨e, hm, rfl, List.prefix_refl _, Or.inl ⟨rfl, rfl⟩⟩,
      ⟨e, hm, rfl, List.suffix_refl _, Or.inl ⟨rfl, rfl⟩⟩⟩
  obtain ⟨-, h1 | h2 | h3⟩ := pkg_dent_pents X u v X' h
  · obtain ⟨c, hc, A, b, B, hcσ, -, hp⟩ := h1
    obtain ⟨m1, m2, -, -⟩ := RH_new X.pents X'.pents c _ _ hp
    by_cases hec : e = c
    · subst hec
      exact ⟨⟨_, m1, rfl, ⟨B, by rw [hcσ]; simp⟩, Or.inr ⟨hu.1, hu.2, by simp [PkgLetter.isRes]⟩⟩,
        ⟨_, m2, rfl, ⟨A, hcσ.symm⟩, Or.inr ⟨hv.1, hv.2, by simp [PkgLetter.isRes]⟩⟩⟩
    · exact stay (RH_keep X.pents X'.pents _ c e hp he hec).1
  · obtain ⟨A, b, B, -, -, -, hp⟩ := h2
    exact stay (RH_keep' X.pents X'.pents _ e hp he).1
  · obtain ⟨b, y, -, -, hp⟩ := h3
    exact stay (RH_keep' X.pents X'.pents _ e hp he).1

/-- The end pieces of every entry of `F` in `X` (`pkg_rem_pieces`). -/
private def RH_Jpc (F X : PkgExpr) : Prop :=
  ∀ e₀ ∈ F.pents,
    (∃ e ∈ X.pents, e.1 = e₀.1 ∧ e.2.2 <+: e₀.2.2 ∧
      ((e.2.1 = e₀.2.1 ∧ e.2.2 = e₀.2.2) ∨
        (2 ≤ e.2.1 ∧ e.2.1 < 4 ∧ e.2.2.getLast?.map PkgLetter.isRes = some true))) ∧
    (∃ e ∈ X.pents, e.2.1 = e₀.2.1 ∧ e.2.2 <:+ e₀.2.2 ∧
      ((e.1 = e₀.1 ∧ e.2.2 = e₀.2.2) ∨
        (2 ≤ e.1 ∧ e.1 < 4 ∧ e.2.2.head?.map PkgLetter.isRes = some true)))

private theorem RH_Jpc_step (F X X' : PkgExpr) (u v : ℕ) (hu : 2 ≤ u ∧ u < 4)
    (hv : 2 ≤ v ∧ v < 4) (h : X' ∈ X.dent u v) (hJ : RH_Jpc F X) : RH_Jpc F X' := by
  intro e₀ he₀
  obtain ⟨⟨e, he, h1, h2, h3⟩, ⟨f, hf, k1, k2, k3⟩⟩ := hJ e₀ he₀
  obtain ⟨⟨e', he', g1, g2, g3⟩, -⟩ := RH_pc_step X X' u v hu hv h e he
  obtain ⟨-, ⟨f', hf', l1, l2, l3⟩⟩ := RH_pc_step X X' u v hu hv h f hf
  refine ⟨⟨e', he', g1.trans h1, g2.trans h2, ?_⟩, ⟨f', hf', l1.trans k1, l2.trans k2, ?_⟩⟩
  · rcases g3 with ⟨g3, g4⟩ | g3
    · rw [g3, g4]; exact h3
    · exact Or.inr g3
  · rcases l3 with ⟨l3, l4⟩ | l3
    · rw [l3, l4]; exact k3
    · exact Or.inr l3

/-- The `Λ̃`-half to the right of `Λ̃_o`, as in `pkg_rem_role0`, with a resolvent next to every
other inner label. -/
private def RH_JR (o : Fin 2) (e₀ : ℕ × ℕ × List PkgLetter) (X : PkgExpr) : Prop :=
  ∃ e ∈ X.pents, e.2.1 = 3 ∧
    (∃ P Q, e.2.2 = P ++ .lw (.lamt o) :: Q ∧ ∀ z ∈ Q, z.isRes = false) ∧
    (2 ≤ e.1 → RH_hr e.2.2) ∧ e.2.2 <:+ e₀.2.2 ∧
    ((e.1 = e₀.1 ∧ e.2.2 = e₀.2.2) ∨ (2 ≤ e.1 ∧ e.1 < 4)) ∧ ∀ e' ∈ X.pents.erase e, RH_K e'

/-- The `Λ̃`-half to the left of `Λ̃_o`, as in `pkg_rem_role0`, with a resolvent next to every
other inner label. -/
private def RH_JL (o : Fin 2) (e₀ : ℕ × ℕ × List PkgLetter) (X : PkgExpr) : Prop :=
  ∃ e ∈ X.pents, e.1 = 2 ∧
    (∃ P Q, e.2.2 = P ++ .lw (.lamt o) :: Q ∧ ∀ z ∈ P, z.isRes = false) ∧
    (2 ≤ e.2.1 → RH_lr e.2.2) ∧ e.2.2 <+: e₀.2.2 ∧
    ((e.2.1 = e₀.2.1 ∧ e.2.2 = e₀.2.2) ∨ (2 ≤ e.2.1 ∧ e.2.1 < 4)) ∧ ∀ e' ∈ X.pents.erase e, RH_K e'

/-- The other entries after a derivative that keeps the entry `e`. -/
private theorem RH_K_keep (X X' : PkgExpr) (u v : ℕ) (h : X' ∈ X.dent u v)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (hK : ∀ e' ∈ X.pents.erase e, RH_K e') :
    (∃ c ∈ X.pents, ∃ (A : List PkgLetter) (b : Fin 2) (B : List PkgLetter),
        c.2.2 = A ++ .lw (.res b) :: B ∧
        X'.pents.Perm (X.pents.erase c ++
          [(c.1, u, A ++ [.lw (.res b)]), (v, c.2.1, .lw (.res b) :: B)]) ∧
        c = e) ∨
      (e ∈ X'.pents ∧ ∀ e' ∈ X'.pents.erase e, RH_K e') := by
  obtain ⟨-, h1 | h2 | h3⟩ := pkg_dent_pents X u v X' h
  · obtain ⟨c, hc, A, b, B, hcσ, -, hp⟩ := h1
    by_cases hec : e = c
    · exact Or.inl ⟨c, hc, A, b, B, hcσ, hp, hec.symm⟩
    · right
      have hcK : RH_K c := hK c ((List.mem_erase_of_ne (Ne.symm hec)).2 hc)
      obtain ⟨hm, hk⟩ := RH_keep X.pents X'.pents _ c e hp he hec
      refine ⟨hm, fun x hx => ?_⟩
      rcases hk x hx with hx | hx
      · exact hK x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact (RH_K_cut c A B b hcσ u v).1 hcK.1
        · exact (RH_K_cut c A B b hcσ u v).2 hcK.2
  · obtain ⟨A, b, B, -, -, -, hp⟩ := h2
    right
    obtain ⟨hm, hk⟩ := RH_keep' X.pents X'.pents _ e hp he
    refine ⟨hm, fun x hx => ?_⟩
    rcases hk x hx with hx | hx
    · exact hK x hx
    · rw [List.mem_singleton.1 hx]
      exact ⟨fun _ => ⟨b, _, rfl⟩, fun _ => ⟨b, .lw (.res b) :: B ++ A, by simp⟩⟩
  · obtain ⟨b, y, -, -, hp⟩ := h3
    right
    obtain ⟨hm, hk⟩ := RH_keep' X.pents X'.pents _ e hp he
    refine ⟨hm, fun x hx => ?_⟩
    rcases hk x hx with hx | hx
    · exact hK x hx
    · rw [List.mem_singleton.1 hx]
      exact ⟨fun _ => ⟨b, _, rfl⟩, fun _ => ⟨b, [.lw (.res b), .lw (.proj y)], rfl⟩⟩

private theorem RH_JR_step (o : Fin 2) (e₀ : ℕ × ℕ × List PkgLetter) (X X' : PkgExpr) (u v : ℕ)
    (hv : 2 ≤ v ∧ v < 4) (h : X' ∈ X.dent u v) (hJ : RH_JR o e₀ X) : RH_JR o e₀ X' := by
  obtain ⟨e, he, hy, ⟨P, Q, hσ, hQ⟩, hx, hsuf, hlab, hK⟩ := hJ
  rcases RH_K_keep X X' u v h e he hK with ⟨c, hc, A, b, B, hcσ, hp, rfl⟩ | ⟨hm, hk⟩
  · obtain ⟨-, m2, k2, -⟩ := RH_new X.pents X'.pents c _ _ hp
    rcases RH_cut A B P Q (.lw (.res b)) (.lw (.lamt o)) (by simp) (hcσ.symm.trans hσ) with
      ⟨M, -, hB⟩ | ⟨M, -, hQ'⟩
    · refine ⟨_, m2, hy, ⟨.lw (.res b) :: M, Q, by rw [hB]; rfl, hQ⟩, fun _ => ⟨b, B, rfl⟩,
        List.IsSuffix.trans ⟨A, hcσ.symm⟩ hsuf, Or.inr hv, fun x hx' => ?_⟩
      rcases k2 x hx' with hx' | rfl
      · exact hK x hx'
      · exact (RH_K_cut c A B b hcσ u v).1 hx
    · exfalso
      have := hQ (.lw (.res b)) (by rw [hQ']; simp)
      simp [PkgLetter.isRes] at this
  · exact ⟨e, hm, hy, ⟨P, Q, hσ, hQ⟩, hx, hsuf, hlab, hk⟩

private theorem RH_JL_step (o : Fin 2) (e₀ : ℕ × ℕ × List PkgLetter) (X X' : PkgExpr) (u v : ℕ)
    (hu : 2 ≤ u ∧ u < 4) (h : X' ∈ X.dent u v) (hJ : RH_JL o e₀ X) : RH_JL o e₀ X' := by
  obtain ⟨e, he, hx, ⟨P, Q, hσ, hP⟩, hy, hpre, hlab, hK⟩ := hJ
  rcases RH_K_keep X X' u v h e he hK with ⟨c, hc, A, b, B, hcσ, hp, rfl⟩ | ⟨hm, hk⟩
  · obtain ⟨m1, -, -, k1⟩ := RH_new X.pents X'.pents c _ _ hp
    rcases RH_cut A B P Q (.lw (.res b)) (.lw (.lamt o)) (by simp) (hcσ.symm.trans hσ) with
      ⟨M, hP', -⟩ | ⟨M, hA, -⟩
    · exfalso
      have := hP (.lw (.res b)) (by rw [hP']; simp)
      simp [PkgLetter.isRes] at this
    · refine ⟨_, m1, hx, ⟨P, M ++ [.lw (.res b)], by rw [hA]; simp, hP⟩, fun _ => ⟨b, A, rfl⟩,
        List.IsPrefix.trans ⟨B, by rw [hcσ]; simp⟩ hpre, Or.inr hu, fun x hx' => ?_⟩
      rcases k1 x hx' with hx' | rfl
      · exact hK x hx'
      · exact (RH_K_cut c A B b hcσ u v).2 hy
  · exact ⟨e, hm, hx, ⟨P, Q, hσ, hP⟩, hy, hpre, hlab, hk⟩

/-- The segment of `Λ̃₁` starts at an outer label, with no resolvent and no `Λ̃` before `Λ̃₁`. -/
private def RH_J1 (X : PkgExpr) : Prop :=
  ∃ e ∈ X.pents, ∃ P Q, e.2.2 = P ++ .lw (.lamt 0) :: Q ∧ e.1 < 2 ∧
    ∀ z ∈ P, z.isRes = false ∧ z.isLam = false

private theorem RH_J1_step (X X' : PkgExpr) (u v : ℕ) (h : X' ∈ X.dent u v) (hJ : RH_J1 X) :
    RH_J1 X' := by
  obtain ⟨e, he, P, Q, hσ, hx, hP⟩ := hJ
  obtain ⟨-, h1 | h2 | h3⟩ := pkg_dent_pents X u v X' h
  · obtain ⟨c, hc, A, b, B, hcσ, -, hp⟩ := h1
    by_cases hec : e = c
    · subst hec
      obtain ⟨m1, -, -, -⟩ := RH_new X.pents X'.pents e _ _ hp
      rcases RH_cut A B P Q (.lw (.res b)) (.lw (.lamt 0)) (by simp) (hcσ.symm.trans hσ) with
        ⟨M, hP', -⟩ | ⟨M, hA, -⟩
      · exfalso
        have := (hP (.lw (.res b)) (by rw [hP']; simp)).1
        simp [PkgLetter.isRes] at this
      · exact ⟨_, m1, P, M ++ [.lw (.res b)], by rw [hA]; simp, hx, hP⟩
    · exact ⟨e, (RH_keep X.pents X'.pents _ c e hp he hec).1, P, Q, hσ, hx, hP⟩
  · obtain ⟨A, b, B, -, -, -, hp⟩ := h2
    exact ⟨e, (RH_keep' X.pents X'.pents _ e hp he).1, P, Q, hσ, hx, hP⟩
  · obtain ⟨b, y, -, -, hp⟩ := h3
    exact ⟨e, (RH_keep' X.pents X'.pents _ e hp he).1, P, Q, hσ, hx, hP⟩

/-! ### One derivative on the sides of `Λ̃` -/

/-- The run up to a resolvent `𝒢_b` cut out of `L 𝒢_b Z`: the same run, or both runs pass `L` and
`𝒢_b`. -/
private theorem RH_run_cut (b : Fin 2) (Z : List PkgLetter) : ∀ L : List PkgLetter,
    FW_run (L ++ [.lw (.res b)]) = FW_run (L ++ .lw (.res b) :: Z) ∨
      (FW_run (L ++ [.lw (.res b)]) = L.countP PkgLetter.isRes + 1 ∧
        FW_run (L ++ .lw (.res b) :: Z) = L.countP PkgLetter.isRes + 1 + FW_run Z)
  | [] => by
      right
      simp only [List.nil_append, FW_run_cons, List.countP_nil, FW_run_nil]
      simp [FW_go, PkgLetter.isEnt, PkgLetter.isLam, PkgLetter.isRes]
  | x :: L => by
      rcases RH_run_cut b Z L with h | ⟨h1, h2⟩
      · left; simp only [List.cons_append, FW_run_cons, h]
      · simp only [List.cons_append, FW_run_cons, h1, h2, List.countP_cons]
        cases FW_go x
        · left; simp
        · right
          simp only [↓reduceIte]
          constructor <;> split_ifs <;> omega

private theorem RH_run_rel (b : Fin 2) (L Z : List PkgLetter) :
    FW_run (L ++ [.lw (.res b)]) ≤ FW_run (L ++ .lw (.res b) :: Z) ∧
      (FW_run (L ++ .lw (.res b) :: Z) = 0 ↔ FW_run (L ++ [.lw (.res b)]) = 0) := by
  rcases RH_run_cut b Z L with h | ⟨h1, h2⟩
  · rw [h]; exact ⟨le_rfl, Iff.rfl⟩
  · rw [h1, h2]; omega

/-- A run of at least two up to a resolvent `𝒢_b` cut out of `L 𝒢_b Z` (`Z` without `Δ`): the
run up to `𝒢_b` is at least two, or `𝒢_b Z` has no `Λ̃` and two resolvents, or the run before the
first `Λ̃` of `Z`, read back to `𝒢_b`, is at least two. -/
private theorem RH_run_two (b : Fin 2) (L Z : List PkgLetter) (hZ : ∀ z ∈ Z, z.isEnt = false)
    (h : 2 ≤ FW_run (L ++ .lw (.res b) :: Z)) :
    2 ≤ FW_run (L ++ [.lw (.res b)]) ∨
      ((∀ z ∈ Z, z.isLam = false) ∧ 2 ≤ (PkgLetter.lw (.res b) :: Z).countP PkgLetter.isRes) ∨
      (∃ Z₁ z Z₂, Z = Z₁ ++ z :: Z₂ ∧ z.isLam = true ∧
        2 ≤ FW_run (Z₁.reverse ++ [.lw (.res b)])) := by
  rcases RH_run_cut b Z L with h1 | ⟨h1, h2⟩
  · exact Or.inl (h1 ▸ h)
  · by_cases hc : 1 ≤ L.countP PkgLetter.isRes
    · left; omega
    · have hZ1 : 1 ≤ FW_run Z := by omega
      rcases RH_first PkgLetter.isLam Z with hl | ⟨Z₁, z, Z₂, rfl, hz, hl⟩
      · right; left
        have hgo : ∀ z ∈ Z, FW_go z = true := fun z hz => by simp [FW_go, hZ z hz, hl z hz]
        have := FW_run_go Z hgo []
        rw [List.append_nil, FW_run_nil] at this
        refine ⟨hl, ?_⟩
        rw [List.countP_cons_of_pos rfl]
        omega
      · right; right
        have hgo : ∀ x ∈ Z₁, FW_go x = true := fun x hx => by
          simp [FW_go, hZ x (by simp [hx]), hl x hx]
        have e1 := FW_run_go Z₁ hgo (z :: Z₂)
        rw [FW_go_lam z hz] at e1
        have hgo' : ∀ x ∈ Z₁.reverse ++ [PkgLetter.lw (.res b)], FW_go x = true := by
          intro x hx
          simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hgo x hx
          · rfl
        have e2 := FW_run_go _ hgo' []
        rw [List.append_nil, FW_run_nil, List.countP_append, List.countP_reverse,
          List.countP_singleton] at e2
        refine ⟨Z₁, z, Z₂, rfl, hz, ?_⟩
        have hrb : (PkgLetter.lw (.res b)).isRes = true := rfl
        rw [e2, hrb]
        simp only [↓reduceIte] at h2 ⊢
        rw [e1] at h2
        omega

private theorem RH_mem_set {α : Type*} (l : List α) (ℓ : ℕ) (w₀ N w : α) (h : l[ℓ]? = some w₀)
    (hw : w ∈ l) (hne : w ≠ w₀) : w ∈ l.set ℓ N := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hw
  have hkℓ : ℓ ≠ k := by
    rintro rfl
    rw [List.getElem?_eq_getElem hk] at h
    exact hne (Option.some.inj h)
  have hk' : k < (l.set ℓ N).length := by simpa using hk
  rw [← List.getElem_set_ne hkℓ hk']
  exact List.getElem_mem _

/-- The place of `Λ̃_o`: in a package entry, or in a word without resolvents. -/
private def RH_loc (X : PkgExpr) (o : Fin 2) : Prop :=
  (∃ e ∈ X.pents, ∃ P Q, e.2.2 = P ++ .lw (.lamt o) :: Q) ∨
    (∃ w ∈ X.loops, PkgLetter.lw (.lamt o) ∈ w ∧ ∀ z ∈ w, z.isRes = false)

/-- A package entry has no letter `Δ`. -/
private theorem RH_free (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) :
    ∀ z ∈ e.2.2, z.isEnt = false := by
  obtain ⟨w, -, hwE, hσw⟩ := FW_mem_pents X e he
  exact (FW_seg_cyc w e.2.2 hwE hσw).1

/-- One derivative on the sides of `Λ̃_o`: a side is never larger, an empty side stays empty, a
nonempty side stays nonempty, and a side with two resolvents keeps two, or gives a package without
`Λ̃` with two resolvents, or the facing side of the other `Λ̃` with two. -/
private theorem RH_side_step (X X' : PkgExpr) (u v : ℕ) (hX : X.wf = true)
    (h : X' ∈ X.dent u v) (o : Fin 2) (hl : RH_loc X o) :
    RH_loc X' o ∧ ∀ s : Bool, X'.lamSide o s ≤ X.lamSide o s ∧
      (X.lamSide o s = 0 ↔ X'.lamSide o s = 0) ∧
      (2 ≤ X.lamSide o s → 2 ≤ X'.lamSide o s ∨ X'.freeTwo = true ∨
        2 ≤ X'.lamSide (1 - o) (!s)) := by
  have hX' := (pkg_dent_wf X X' u v hX h).1
  rcases hl with ⟨e, he, P, Q, hσ⟩ | ⟨w, hw, ho, hres⟩
  swap
  · have hw' : w ∈ X'.loops := by
      rcases dent_cases X X' u v h with ⟨ℓ, A₀, B₀, a, hℓ, hl'⟩ | ⟨b, y, hl'⟩
      · rw [hl']
        refine RH_mem_set _ _ _ _ _ hℓ hw fun hwe => ?_
        have := hres (.lw (.res a)) (by rw [hwe]; simp)
        simp [PkgLetter.isRes] at this
      · rw [hl']; exact List.mem_append_left _ hw
    refine ⟨Or.inr ⟨w, hw', ho, hres⟩, fun s => ?_⟩
    rw [RH_side_zero X hX w hw o ho hres s, RH_side_zero X' hX' w hw' o ho hres s]
    simp
  have hcnt := RH_count X hX e he o
  rw [hσ] at hcnt
  simp only [List.count_append, List.count_cons_self] at hcnt
  have hPo : PkgLetter.lw (.lamt o) ∉ P := List.count_eq_zero.1 (by omega)
  have hQo : PkgLetter.lw (.lamt o) ∉ Q := List.count_eq_zero.1 (by omega)
  have hfr := RH_free X e he
  rw [hσ] at hfr
  obtain ⟨hRt, hLf⟩ := RH_sides X hX e he o P Q hσ
  have same : e ∈ X'.pents → RH_loc X' o ∧ ∀ s : Bool, X'.lamSide o s ≤ X.lamSide o s ∧
      (X.lamSide o s = 0 ↔ X'.lamSide o s = 0) ∧
      (2 ≤ X.lamSide o s → 2 ≤ X'.lamSide o s ∨ X'.freeTwo = true ∨
        2 ≤ X'.lamSide (1 - o) (!s)) := fun hm => by
    obtain ⟨hRt', hLf'⟩ := RH_sides X' hX' e hm o P Q hσ
    refine ⟨Or.inl ⟨e, hm, P, Q, hσ⟩, fun s => ?_⟩
    have : X'.lamSide o s = X.lamSide o s := by
      cases s
      · rw [hLf, hLf']
      · rw [hRt, hRt']
    rw [this]
    exact ⟨le_rfl, Iff.rfl, fun h => Or.inl h⟩
  obtain ⟨-, h1 | h2 | h3⟩ := pkg_dent_pents X u v X' h
  · obtain ⟨c, hc, A, b, B, hcσ, -, hp⟩ := h1
    by_cases hec : e = c
    · subst hec
      obtain ⟨m1, m2, -, -⟩ := RH_new X.pents X'.pents e _ _ hp
      rcases RH_cut A B P Q (.lw (.res b)) (.lw (.lamt o)) (by simp) (hcσ.symm.trans hσ) with
        ⟨M, hP, hB⟩ | ⟨M, hA, hQ⟩
      · -- `Λ̃_o` lies in the right piece `𝒢_b M Λ̃_o Q`
        obtain ⟨hRt', hLf'⟩ := RH_sides X' hX' _ m2 o (.lw (.res b) :: M) Q (by rw [hB]; rfl)
        have hold : X.lamSide o false = FW_run (M.reverse ++ .lw (.res b) :: A.reverse) := by
          rw [hLf, hP]; simp
        have hnew : X'.lamSide o false = FW_run (M.reverse ++ [.lw (.res b)]) := by
          rw [hLf']; simp
        refine ⟨Or.inl ⟨_, m2, .lw (.res b) :: M, Q, by rw [hB]; rfl⟩, fun s => ?_⟩
        cases s
        · obtain ⟨r1, r2⟩ := RH_run_rel b M.reverse A.reverse
          rw [hold, hnew]
          refine ⟨r1, r2, fun h2 => ?_⟩
          have hAE : ∀ z ∈ A.reverse, z.isEnt = false := fun z hz =>
            hfr z (by rw [hP]; simp [List.mem_reverse.1 hz])
          rcases RH_run_two b M.reverse A.reverse hAE h2 with h4 | ⟨hlam, h4⟩ |
              ⟨Z₁, z, Z₂, hZ, hz, h4⟩
          · exact Or.inl h4
          · right; left
            refine (RH_freeTwo X').2 ⟨_, m1, ?_, ?_⟩
            · simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
              rw [List.any_eq_false.2 fun z hz => by
                simp [hlam z (List.mem_reverse.2 hz)]]
              rfl
            · simp only [List.countP_cons, List.countP_reverse] at h4
              simp only [List.countP_append, List.countP_singleton]
              simpa [PkgLetter.isRes] using h4
          · right; right
            have hA' : A = Z₂.reverse ++ z :: Z₁.reverse := by
              rw [← List.reverse_reverse A, hZ]; simp
            have hzo : z = .lw (.lamt (1 - o)) := by
              rcases RH_lam z hz o with rfl | h5
              · exact absurd (by rw [hP, hA']; simp) hPo
              · exact h5
            obtain ⟨hR2, -⟩ := RH_sides X' hX' _ m1 (1 - o) Z₂.reverse
              (Z₁.reverse ++ [.lw (.res b)]) (by rw [hA', hzo]; simp)
            rw [Bool.not_false, hR2]
            exact h4
        · rw [hRt, hRt']
          exact ⟨le_rfl, Iff.rfl, fun h => Or.inl h⟩
      · -- `Λ̃_o` lies in the left piece `P Λ̃_o M 𝒢_b`
        obtain ⟨hRt', hLf'⟩ := RH_sides X' hX' _ m1 o P (M ++ [.lw (.res b)]) (by rw [hA]; simp)
        refine ⟨Or.inl ⟨_, m1, P, M ++ [.lw (.res b)], by rw [hA]; simp⟩, fun s => ?_⟩
        cases s
        · rw [hLf, hLf']
          exact ⟨le_rfl, Iff.rfl, fun h => Or.inl h⟩
        · obtain ⟨r1, r2⟩ := RH_run_rel b M B
          rw [hRt, hRt', hQ]
          refine ⟨r1, r2, fun h2 => ?_⟩
          have hBE : ∀ z ∈ B, z.isEnt = false := fun z hz =>
            hfr z (by rw [hQ]; simp [hz])
          rcases RH_run_two b M B hBE h2 with h4 | ⟨hlam, h4⟩ | ⟨Z₁, z, Z₂, hZ, hz, h4⟩
          · exact Or.inl h4
          · right; left
            refine (RH_freeTwo X').2 ⟨_, m2, ?_, h4⟩
            simp only [List.any_cons]
            rw [List.any_eq_false.2 fun z hz => by simp [hlam z hz]]
            rfl
          · right; right
            have hzo : z = .lw (.lamt (1 - o)) := by
              rcases RH_lam z hz o with rfl | h5
              · exact absurd (by rw [hQ, hZ]; simp) hQo
              · exact h5
            obtain ⟨-, hL2⟩ := RH_sides X' hX' _ m2 (1 - o) (.lw (.res b) :: Z₁) Z₂
              (by rw [hZ, hzo]; rfl)
            rw [Bool.not_true, hL2]
            simpa using h4
    · exact same (RH_keep X.pents X'.pents _ c e hp he hec).1
  · obtain ⟨A, b, B, -, -, -, hp⟩ := h2
    exact same (RH_keep' X.pents X'.pents _ e hp he).1
  · obtain ⟨b, y, -, -, hp⟩ := h3
    exact same (RH_keep' X.pents X'.pents _ e hp he).1

/-- One derivative keeps a package without `Λ̃` with two resolvents. -/
private theorem RH_free_step (X X' : PkgExpr) (u v : ℕ) (h : X' ∈ X.dent u v)
    (hf : X.freeTwo = true) : X'.freeTwo = true := by
  obtain ⟨e, he, hlam, h2⟩ := (RH_freeTwo X).1 hf
  obtain ⟨-, h1 | h2' | h3⟩ := pkg_dent_pents X u v X' h
  · obtain ⟨c, hc, A, b, B, hcσ, -, hp⟩ := h1
    by_cases hec : e = c
    · subst hec
      obtain ⟨m1, m2, -, -⟩ := RH_new X.pents X'.pents e _ _ hp
      rw [hcσ] at hlam h2
      simp only [List.any_append, List.any_cons, Bool.or_eq_false_iff] at hlam
      simp only [List.countP_append, List.countP_cons] at h2
      have hrb : (PkgLetter.lw (.res b)).isRes = true := rfl
      simp only [hrb, ↓reduceIte] at h2
      by_cases hA : 1 ≤ A.countP PkgLetter.isRes
      · refine (RH_freeTwo X').2 ⟨_, m1, by simp [hlam.1, PkgLetter.isLam], ?_⟩
        simp only [List.countP_append, List.countP_singleton, hrb, ↓reduceIte]
        omega
      · refine (RH_freeTwo X').2 ⟨_, m2, by simp [hlam.2.2, PkgLetter.isLam], ?_⟩
        rw [List.countP_cons_of_pos rfl]
        omega
    · exact (RH_freeTwo X').2 ⟨e, (RH_keep X.pents X'.pents _ c e hp he hec).1, hlam, h2⟩
  · obtain ⟨A, b, B, -, -, -, hp⟩ := h2'
    exact (RH_freeTwo X').2 ⟨e, (RH_keep' X.pents X'.pents _ e hp he).1, hlam, h2⟩
  · obtain ⟨b, y, -, -, hp⟩ := h3
    exact (RH_freeTwo X').2 ⟨e, (RH_keep' X.pents X'.pents _ e hp he).1, hlam, h2⟩

/-! ### The expanded word under the binders of the remainder pins -/

/-- The derivative structures `dwirt 2 3` carry a property kept by one derivative with inner
labels. -/
private theorem RH_iter (Pr : PkgExpr → Prop)
    (h : ∀ X u v, 2 ≤ u ∧ u < 4 → 2 ≤ v ∧ v < 4 → Pr X → ∀ X' ∈ X.dent u v, Pr X')
    (F : PkgExpr) (hF : Pr F) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ F.dwirt 2 3 p q) : Pr R' :=
  pkg_dwirt_iter (fun _ X => Pr X) 2 3
    (fun _ X hX X' hX' => h X 2 3 (by omega) (by omega) hX X' hX')
    (fun _ X hX X' hX' => h X 3 2 (by omega) (by omega) hX X' hX') F hF p q R' hR'

/-- The two letters `Λ̃` lie in one loop each. -/
private theorem RH_some_loop (X : PkgExpr) (hX : X.wf = true) (o : Fin 2) :
    ∃ w ∈ X.loops, PkgLetter.lw (.lamt o) ∈ w := by
  have h := FW_wf_count X hX o
  obtain ⟨x, hx, hpos⟩ := List.sum_pos_iff_exists_pos_nat.1 (by omega :
    0 < (X.loops.map fun w => w.count (PkgLetter.lw (.lamt o))).sum)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  exact ⟨w, hw, List.count_pos_iff.1 hpos⟩

/-- Two loops holding the same `Λ̃_o` are equal. -/
private theorem RH_uniq (X : PkgExpr) (hX : X.wf = true) (o : Fin 2) (w w' : List PkgLetter)
    (hw : w ∈ X.loops) (hw' : w' ∈ X.loops) (ho : PkgLetter.lw (.lamt o) ∈ w)
    (ho' : PkgLetter.lw (.lamt o) ∈ w') : w = w' := by
  by_contra hne
  have := FW_two_le (fun w => w.count (.lw (.lamt o))) w w' hne (List.count_pos_iff.2 ho)
    (List.count_pos_iff.2 ho') X.loops hw hw'
  have := FW_wf_count X hX o
  omega

/-- A letter of a package entry lies in a word with a `Δ`. -/
private theorem RH_ent_loop (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents)
    (x : PkgLetter) (hx : x ∈ e.2.2) : ∃ w ∈ X.loops, w.any PkgLetter.isEnt = true ∧ x ∈ w := by
  obtain ⟨w, hwL, hwE, hσw⟩ := FW_mem_pents X e he
  obtain ⟨-, M, hrot, -⟩ := FW_seg_cyc w e.2.2 hwE hσw
  exact ⟨w, hwL, hwE, hrot.perm.symm.subset (List.mem_append_left _ hx)⟩

/-- When the loop of `Λ̃₂` has no `Δ` and a resolvent to the left of `Λ̃₂`, the rules choose the
left side of `Λ̃₂`. -/
private theorem RH_side12 (R : PkgExpr) (hR : R.wf = true) (w : List PkgLetter) (hw : w ∈ R.loops)
    (ho : PkgLetter.lw (.lamt 1) ∈ w) (hE : w.any PkgLetter.isEnt = false)
    (hseek : (pkgSeek w (w.idxOf (.lw (.lamt 1))) false).isSome = true) :
    R.ffocusSide = some (1, false) := by
  have hlt₂ := List.findIdx_lt_length_of_exists (p := fun w => w.contains (.lw (.lamt 1)))
    ⟨w, hw, by simpa using ho⟩
  have h₂ := List.getElem?_eq_getElem hlt₂
  have hw₂ := RH_uniq R hR 1 _ w (List.getElem_mem _) hw
    (FW_findIdx_mem R.loops 1 _ h₂) ho
  rw [hw₂] at h₂
  obtain ⟨w₁, hw₁, ho₁⟩ := RH_some_loop R hR 0
  have hlt₁ := List.findIdx_lt_length_of_exists (p := fun w => w.contains (.lw (.lamt 0)))
    ⟨w₁, hw₁, by simpa using ho₁⟩
  have h₁ := List.getElem?_eq_getElem hlt₁
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hseek
  unfold PkgExpr.ffocusSide
  simp only [h₂, h₁]
  have hE' : ¬ (w.any PkgLetter.isEnt = true) := by rw [hE]; simp
  rw [ite_eq_right (by exact hE'), hr]

/-- A word without `Δ` of the expanded word is a word of the expression. -/
private theorem RH_fpkg_loops (R : PkgExpr) (hf : R.ffocus.isSome = true) (w : List PkgLetter)
    (hw : w ∈ R.fpkg.loops) (hE : w.any PkgLetter.isEnt = false) : w ∈ R.loops := by
  obtain ⟨⟨ℓ, r, b⟩, hf'⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨o', w', hw', ho', hseek, -⟩ := FW_focus R ℓ r b hf'
  obtain ⟨a, tl, hrot, -, -⟩ := FH_shape w' _ r b o' (List.getElem?_idxOf ho') hseek
  obtain ⟨hl, -, -⟩ := RS_fpkg R ℓ r b w' a tl hf' hw' hrot
  rw [hl] at hw
  rcases List.mem_or_eq_of_mem_set hw with hw | rfl
  · exact hw
  · exfalso
    cases b <;> simp [PkgLetter.isEnt] at hE

/-- The facts at the expanded word under the binders of the remainder pins: `wf`, a focus, the
outer labels of the expression, the segment of `Λ̃₁`, and the place of both letters `Λ̃`. -/
private theorem RH_base (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr) (hR : R ∈ fInner ε j [R₀]) :
    R.wf = true ∧ R.ffocus.isSome = true ∧ R.fpkg.wf = true ∧
      (∀ e ∈ R.pents, e.1 < 2 ∧ e.2.1 < 2) ∧ RH_J1 R.fpkg ∧ ∀ o, RH_loc R.fpkg o := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  have hFw := pkg_fpkg_wf R hRw hfoc
  have hlab : ∀ e ∈ R.pents, e.1 < 2 ∧ e.2.1 < 2 :=
    RH_labels R 2 (pkg_inv_lab ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).2.2
  -- the segment of `Λ̃₁` in `R`
  have hJR : RH_J1 R := by
    obtain ⟨w, hw, hwE, σ, hσ, hmem, hall⟩ := pkg_inv_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R
      (Or.inr hR)
    rw [← FW_pw_segs w hwE] at hσ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hσ
    have he' : e ∈ R.pents := by rw [FW_pents]; exact List.mem_flatMap.2 ⟨w, hw, he⟩
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem hmem
    have hc := RH_count R hRw e he' 0
    rw [hPQ] at hc
    simp only [List.count_append, List.count_cons_self] at hc
    have hP : PkgLetter.lw (.lamt 0) ∉ P := List.count_eq_zero.1 (by omega)
    have htw : e.2.2.takeWhile (fun x => decide (x ≠ PkgLetter.lw (.lamt 0))) = P := by
      rw [hPQ, List.takeWhile_append_of_pos (fun a ha => by
        simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact hP ha),
        List.takeWhile_cons_of_neg (by simp)]
      simp
    rw [htw, List.all_eq_true] at hall
    refine ⟨e, he', P, Q, hPQ, (hlab e he').1, fun z hz => ?_⟩
    have := hall z hz
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this
  -- the segment of `Λ̃₁` in `R.fpkg`
  have hJF : RH_J1 R.fpkg := by
    obtain ⟨e, he, P, Q, hσ, hx, hP⟩ := hJR
    obtain ⟨⟨o, side⟩, hs⟩ := Option.isSome_iff_exists.1 (by
      rw [(pkg_ffocusSide R).1]; exact hfoc)
    obtain ⟨hT1, hF1⟩ := RH_fpkg R o side hs
    have hPr : ∀ z ∈ P, z.isRes = false := fun z hz => (hP z hz).1
    cases side
    · rcases hF1 rfl with ⟨c, hc, A, X, B, a, -, hcσ, hp⟩ | ⟨X, Y, a, -, hp⟩
      · by_cases hec : e = c
        · subst hec
          rcases RH_cut A (X ++ .lw (.lamt o) :: B) P Q (.lw (.res a)) (.lw (.lamt 0)) (by simp)
            (hcσ.symm.trans hσ) with ⟨M, hP', -⟩ | ⟨M, hA, -⟩
          · exfalso
            have := hPr (.lw (.res a)) (by rw [hP']; simp)
            simp [PkgLetter.isRes] at this
          · refine ⟨(e.1, 3, A ++ [.lw (.res a)]), hp.symm.subset (by simp), P,
              M ++ [.lw (.res a)], ?_, hx, hP⟩
            simp only
            rw [hA]; simp
        · have : e ∈ R.pents.erase c := (List.mem_erase_of_ne hec).2 he
          exact ⟨e, hp.symm.subset (by simp [this]), P, Q, hσ, hx, hP⟩
      · exact ⟨e, hp.symm.subset (by simp [he]), P, Q, hσ, hx, hP⟩
    · rcases hT1 rfl with ⟨c, hc, A, X, B, a, -, hcσ, hp⟩ | ⟨Y, X, a, -, hp⟩
      · by_cases hec : e = c
        · subst hec
          have hcσ' : e.2.2 = (A ++ .lw (.lamt o) :: X) ++ .lw (.res a) :: B := by
            rw [hcσ]; simp
          rcases RH_cut _ B P Q (.lw (.res a)) (.lw (.lamt 0)) (by simp)
            (hcσ'.symm.trans hσ) with ⟨M, hP', -⟩ | ⟨M, hA, -⟩
          · exfalso
            have := hPr (.lw (.res a)) (by rw [hP']; simp)
            simp [PkgLetter.isRes] at this
          · refine ⟨(e.1, 3, A ++ .lw (.lamt o) :: (X ++ [.lw (.det a)])),
              hp.symm.subset List.mem_cons_self, P, M ++ [.lw (.det a)], ?_, hx, hP⟩
            simp only
            rw [show A ++ PkgLetter.lw (.lamt o) :: (X ++ [.lw (.det a)]) =
              (A ++ .lw (.lamt o) :: X) ++ [.lw (.det a)] by simp, hA]
            simp
        · have : e ∈ R.pents.erase c := (List.mem_erase_of_ne hec).2 he
          exact ⟨e, hp.symm.subset (by simp [this]), P, Q, hσ, hx, hP⟩
      · exact ⟨e, hp.symm.subset (by simp [he]), P, Q, hσ, hx, hP⟩
  refine ⟨hRw, hfoc, hFw, hlab, hJF, fun o => ?_⟩
  obtain ⟨w, hw, ho⟩ := RH_some_loop R.fpkg hFw o
  cases hE : w.any PkgLetter.isEnt
  swap
  · obtain ⟨e, he, hx⟩ := RH_lament R.fpkg w hw hE _ ho rfl
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem hx
    exact Or.inl ⟨e, he, P, Q, hPQ⟩
  · -- a word without `Δ`: the loop of `Λ̃₂`, without resolvents
    right
    refine ⟨w, hw, ho, ?_⟩
    obtain ⟨e₁, he₁, P₁, Q₁, hσ₁, -, -⟩ := hJF
    obtain ⟨w₁, hw₁, hw₁E, hm₁⟩ := RH_ent_loop R.fpkg e₁ he₁ (.lw (.lamt 0)) (by rw [hσ₁]; simp)
    have ho0 : o ≠ 0 := by
      rintro rfl
      have := RH_uniq R.fpkg hFw 0 w w₁ hw hw₁ ho hm₁
      rw [this, hw₁E] at hE
      exact Bool.noConfusion hE
    have ho1 : o = 1 := by
      fin_cases o
      · exact absurd rfl ho0
      · rfl
    subst ho1
    have h0 : PkgLetter.lw (.lamt 0) ∉ w := fun h => by
      have := RH_uniq R.fpkg hFw 0 w w₁ hw hw₁ h hm₁
      rw [this, hw₁E] at hE
      exact Bool.noConfusion hE
    have hside := RH_lamSide_free R.fpkg hFw 1 w hw (by simpa using ho) hE
      (by simpa using h0) false
    have hfl := pkg_fpkg_lamSide R hRw hfoc 1 false
    have hzero : R.fpkg.lamSide 1 false = 0 := by
      rw [hfl]
      split_ifs with hsd
      · rfl
      · have hwR := RH_fpkg_loops R hfoc w hw hE
        rw [FW_lamSide_mem R 1 false (FW_wf_count R hRw 1).le w hwR ho]
        refine (RH_seek w 1 false).2 ?_
        cases hsk : pkgSeek w (w.idxOf (.lw (.lamt 1))) false
        · rfl
        · exact absurd (RH_side12 R hRw w hwR ho hE (by rw [hsk]; rfl)) hsd
    rw [hzero] at hside
    intro z hz
    have := List.countP_eq_zero.1 hside.symm z hz
    simpa using this

/-- The `Λ̃`-half of the expanded word, right of `Λ̃_o`. -/
private theorem RH_JR_base (R : PkgExpr) (o : Fin 2) (hs : R.ffocusSide = some (o, true))
    (hlab : ∀ e ∈ R.pents, e.1 < 2 ∧ e.2.1 < 2) :
    ∃ e₀ ∈ R.fpkg.pents, PkgLetter.lw (.lamt o) ∈ e₀.2.2 ∧ e₀.2.1 = 3 ∧ RH_JR o e₀ R.fpkg := by
  obtain ⟨hT1, -⟩ := RH_fpkg R o true hs
  rcases hT1 rfl with ⟨c, hc, A, X, B, a, hX, -, hp⟩ | ⟨Y, X, a, hX, hp⟩
  · have hm := hp.symm.subset List.mem_cons_self
    have hc2 := hlab c hc
    refine ⟨_, hm, by simp, rfl, _, hm, rfl, ⟨A, X ++ [.lw (.det a)], rfl, fun z hz => ?_⟩,
      fun h => absurd h (by simp only; omega), List.suffix_refl _, Or.inl ⟨rfl, rfl⟩,
      fun x hx => ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hX z hz
      · rfl
    · have h3 := hp.erase (c.1, 3, A ++ .lw (.lamt o) :: (X ++ [.lw (.det a)]))
      rw [List.erase_cons_head] at h3
      rcases List.mem_append.1 (h3.subset hx) with hx | hx
      · have := hlab x (List.mem_of_mem_erase hx)
        exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      · rw [List.mem_singleton.1 hx]
        exact ⟨fun _ => ⟨a, B, rfl⟩, fun h => absurd h (by simp only; omega)⟩
  · have hm := hp.symm.subset List.mem_cons_self
    refine ⟨_, hm, by simp, rfl, _, hm, rfl, ⟨_, X ++ [.lw (.det a)], rfl, fun z hz => ?_⟩,
      fun _ => ⟨a, Y ++ .lw (.lamt o) :: (X ++ [.lw (.det a)]), by simp⟩, List.suffix_refl _,
      Or.inl ⟨rfl, rfl⟩, fun x hx => ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hX z hz
      · rfl
    · have h3 := hp.erase (2, 3, (.lw (.res a) :: Y) ++ .lw (.lamt o) :: (X ++ [.lw (.det a)]))
      rw [List.erase_cons_head] at h3
      have := hlab x (h3.subset hx)
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- The `Λ̃`-half of the expanded word, left of `Λ̃_o`. -/
private theorem RH_JL_base (R : PkgExpr) (o : Fin 2) (hs : R.ffocusSide = some (o, false))
    (hlab : ∀ e ∈ R.pents, e.1 < 2 ∧ e.2.1 < 2) :
    ∃ e₀ ∈ R.fpkg.pents, PkgLetter.lw (.lamt o) ∈ e₀.2.2 ∧ e₀.1 = 2 ∧ RH_JL o e₀ R.fpkg := by
  obtain ⟨-, hF1⟩ := RH_fpkg R o false hs
  have hPr : ∀ (X : List PkgLetter) (a : Fin 2), (∀ z ∈ X, z.isRes = false) →
      ∀ z ∈ PkgLetter.lw (.det a) :: X, z.isRes = false := fun X a hX z hz => by
    rcases List.mem_cons.1 hz with rfl | hz
    · rfl
    · exact hX z hz
  rcases hF1 rfl with ⟨c, hc, A, X, B, a, hX, -, hp⟩ | ⟨X, Y, a, hX, hp⟩
  · have hm := hp.symm.subset List.mem_cons_self
    have hc2 := hlab c hc
    refine ⟨_, hm, by simp, rfl, _, hm, rfl, ⟨_, B, rfl, hPr X a hX⟩,
      fun h => absurd h (by simp only; omega), List.prefix_refl _, Or.inl ⟨rfl, rfl⟩,
      fun x hx => ?_⟩
    have h3 := hp.erase (2, c.2.1, (.lw (.det a) :: X) ++ .lw (.lamt o) :: B)
    rw [List.erase_cons_head] at h3
    rcases List.mem_append.1 (h3.subset hx) with hx | hx
    · have := hlab x (List.mem_of_mem_erase hx)
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · rw [List.mem_singleton.1 hx]
      exact ⟨fun h => absurd h (by simp only; omega), fun _ => ⟨a, A, rfl⟩⟩
  · have hm := hp.symm.subset List.mem_cons_self
    refine ⟨_, hm, by simp, rfl, _, hm, rfl, ⟨_, Y ++ [.lw (.res a)], rfl, hPr X a hX⟩,
      fun _ => ⟨a, (.lw (.det a) :: X) ++ .lw (.lamt o) :: Y, by simp⟩, List.prefix_refl _,
      Or.inl ⟨rfl, rfl⟩, fun x hx => ?_⟩
    have h3 := hp.erase (2, 3, (.lw (.det a) :: X) ++ .lw (.lamt o) :: (Y ++ [.lw (.res a)]))
    rw [List.erase_cons_head] at h3
    have := hlab x (h3.subset hx)
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- `freeTwo` survives the expanded word. -/
private theorem RH_fpkg_freeTwo (R : PkgExpr) (hf : R.ffocus.isSome = true)
    (h : R.freeTwo = true) : R.fpkg.freeTwo = true := by
  obtain ⟨e₁, he₁, hlam, h2⟩ := (RH_freeTwo R).1 h
  obtain ⟨⟨o, side⟩, hs⟩ := Option.isSome_iff_exists.1 (by
    rw [(pkg_ffocusSide R).1]; exact hf)
  obtain ⟨hT1, hF1⟩ := RH_fpkg R o side hs
  refine (RH_freeTwo _).2 ⟨e₁, ?_, hlam, h2⟩
  cases side
  · rcases hF1 rfl with ⟨c, hc, A, X, B, a, -, hcσ, hp⟩ | ⟨X, Y, a, -, hp⟩
    · have hec : e₁ ≠ c := by
        rintro rfl; rw [hcσ] at hlam; simp [PkgLetter.isLam] at hlam
      exact hp.symm.subset (by simp [(List.mem_erase_of_ne hec).2 he₁])
    · exact hp.symm.subset (by simp [he₁])
  · rcases hT1 rfl with ⟨c, hc, A, X, B, a, -, hcσ, hp⟩ | ⟨Y, X, a, -, hp⟩
    · have hec : e₁ ≠ c := by
        rintro rfl; rw [hcσ] at hlam; simp [PkgLetter.isLam] at hlam
      exact hp.symm.subset (by simp [(List.mem_erase_of_ne hec).2 he₁])
    · exact hp.symm.subset (by simp [he₁])

/-- Q3 (a): one entry has role `0`: the piece of the `Λ̃`-half of `fpkg` at its `𝔐`-end, with
`Λ̃_o`; its other label is that of the half if uncut, inner otherwise. -/
theorem pkg_rem_role0 (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q)
    (o : Fin 2) (side : Bool) (hs : R.ffocusSide = some (o, side)) :
    ((R'.rfacs.filterMap FFac.entData).countP fun d => FEnt.role d == 0) = 1 ∧
      ∃ e ∈ R'.pents, ∃ e₀ ∈ R.fpkg.pents, PkgLetter.lw (.lamt o) ∈ e.2.2 ∧
        PkgLetter.lw (.lamt o) ∈ e₀.2.2 ∧ ((R'.rent e).entData.map FEnt.role) = some 0 ∧
        (side = true → e.2.1 = 3 ∧ e₀.2.1 = 3 ∧ e.2.2 <:+ e₀.2.2 ∧
          ((e.1 = e₀.1 ∧ e.2.2 = e₀.2.2) ∨ (2 ≤ e.1 ∧ e.1 < 4)) ∧
          ((R'.rent e).entData.bind fun d => d.2.2.1.getLast?) = some 0) ∧
        (side = false → e.1 = 2 ∧ e₀.1 = 2 ∧ e.2.2 <+: e₀.2.2 ∧
          ((e.2.1 = e₀.2.1 ∧ e.2.2 = e₀.2.2) ∨ (2 ≤ e.2.1 ∧ e.2.1 < 4)) ∧
          ((R'.rent e).entData.bind fun d => d.2.2.1.head?) = some 0) := by
  obtain ⟨-, -, -, hlab, -, -⟩ := RH_base ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have count : ∀ e ∈ R'.pents, (∀ x ∈ R'.pents.erase e, RH_K x) →
      ∀ d, (R'.rent e).entData = some d → FEnt.role d = 0 →
        ((R'.rfacs.filterMap FFac.entData).countP fun d => FEnt.role d == 0) = 1 := by
    intro e he hK d hd hrole
    rw [RH_cnt, (List.perm_cons_erase he).countP_eq, List.countP_cons,
      List.countP_eq_zero.2 fun x hx => ?_]
    · simp [hd, hrole]
    · obtain ⟨dx, hdx⟩ := RH_ent R' x
      have := RH_role_K R' x (List.mem_of_mem_erase hx) (hK x hx) dx hdx
      simp [hdx, this]
  cases side
  · obtain ⟨e₀, he₀, hoe₀, hx₀, hJ⟩ := RH_JL_base R o hs hlab
    have hJ' := RH_iter (RH_JL o e₀)
      (fun X u v hu _ hJ X' hX' => RH_JL_step o e₀ X X' u v hu hX' hJ) R.fpkg hJ p q R' hR'
    obtain ⟨e, he, hx, ⟨P, Q, hσ, hP⟩, -, hpre, hlab', hK⟩ := hJ'
    obtain ⟨d, hd, hrole, hhead⟩ := RH_role_L R' e he (by omega) P Q o hσ hP
    refine ⟨count e he hK d hd hrole, e, he, e₀, he₀, by rw [hσ]; simp, hoe₀,
      by rw [hd]; simp [hrole], fun h => absurd h (by simp), fun _ =>
        ⟨hx, hx₀, hpre, hlab', by rw [hd]; simpa using hhead⟩⟩
  · obtain ⟨e₀, he₀, hoe₀, hy₀, hJ⟩ := RH_JR_base R o hs hlab
    have hJ' := RH_iter (RH_JR o e₀)
      (fun X u v _ hv hJ X' hX' => RH_JR_step o e₀ X X' u v hv hX' hJ) R.fpkg hJ p q R' hR'
    obtain ⟨e, he, hy, ⟨P, Q, hσ, hQ⟩, -, hsuf, hlab', hK⟩ := hJ'
    obtain ⟨d, hd, hrole, hlast⟩ := RH_role_R R' e he (by omega) P Q o hσ hQ
    refine ⟨count e he hK d hd hrole, e, he, e₀, he₀, by rw [hσ]; simp, hoe₀,
      by rw [hd]; simp [hrole], fun _ =>
        ⟨hy, hy₀, hsuf, hlab', by rw [hd]; simpa using hlast⟩, fun h => absurd h (by simp)⟩

/-- Q3 (b): the two end pieces of every segment of `fpkg`: the segment itself, or a piece cut
at a resolvent with an inner label at the cut. -/
theorem pkg_rem_pieces (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    ∀ e₀ ∈ R.fpkg.pents,
      (∃ e ∈ R'.pents, e.1 = e₀.1 ∧ e.2.2 <+: e₀.2.2 ∧
        ((e.2.1 = e₀.2.1 ∧ e.2.2 = e₀.2.2) ∨
          (2 ≤ e.2.1 ∧ e.2.1 < 4 ∧ e.2.2.getLast?.map PkgLetter.isRes = some true))) ∧
      (∃ e ∈ R'.pents, e.2.1 = e₀.2.1 ∧ e.2.2 <:+ e₀.2.2 ∧
        ((e.1 = e₀.1 ∧ e.2.2 = e₀.2.2) ∨
          (2 ≤ e.1 ∧ e.1 < 4 ∧ e.2.2.head?.map PkgLetter.isRes = some true))) :=
  RH_iter (RH_Jpc R.fpkg) (fun X u v hu hv hJ X' hX' => RH_Jpc_step R.fpkg X X' u v hu hv hX' hJ)
    R.fpkg (fun e₀ he₀ => ⟨⟨e₀, he₀, rfl, List.prefix_refl _, Or.inl ⟨rfl, rfl⟩⟩,
      ⟨e₀, he₀, rfl, List.suffix_refl _, Or.inl ⟨rfl, rfl⟩⟩⟩) p q R' hR'

/-- Q3 (c2): a derivative keeps an empty side empty and a nonempty side nonempty, never larger. -/
theorem pkg_rem_sides (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    ∀ (o : Fin 2) (side : Bool), (R.fpkg.lamSide o side = 0 → R'.lamSide o side = 0) ∧
      (1 ≤ R.fpkg.lamSide o side →
        1 ≤ R'.lamSide o side ∧ R'.lamSide o side ≤ R.fpkg.lamSide o side) := by
  obtain ⟨-, -, hFw, -, -, hloc⟩ := RH_base ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have h := RH_iter (fun X => X.wf = true ∧ (∀ o, RH_loc X o) ∧ ∀ o s,
      X.lamSide o s ≤ R.fpkg.lamSide o s ∧ (R.fpkg.lamSide o s = 0 ↔ X.lamSide o s = 0))
    (fun X u v _ _ hX X' hX' => by
      obtain ⟨hw, hl, hs⟩ := hX
      refine ⟨(pkg_dent_wf X X' u v hw hX').1,
        fun o => (RH_side_step X X' u v hw hX' o (hl o)).1, fun o s => ?_⟩
      obtain ⟨a1, a2, -⟩ := (RH_side_step X X' u v hw hX' o (hl o)).2 s
      exact ⟨a1.trans (hs o s).1, (hs o s).2.trans a2⟩)
    R.fpkg ⟨hFw, hloc, fun _ _ => ⟨le_rfl, Iff.rfl⟩⟩ p q R' hR'
  intro o side
  obtain ⟨a1, a2⟩ := h.2.2 o side
  refine ⟨a2.1, fun h1 => ⟨?_, a1⟩⟩
  by_contra h0
  have := a2.2 (by omega)
  omega

/-- Q3 (c3): the segment of `Λ̃₁` starts at an outer label, with no resolvent and no `Λ̃₂` before
`Λ̃₁`. -/
theorem pkg_rem_lam1 (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    R'.lamSide 0 false = 0 ∧ ∃ e ∈ R'.pents, PkgLetter.lw (.lamt 0) ∈ e.2.2 ∧ e.1 < 2 ∧
      (e.2.2.takeWhile fun x => x != PkgLetter.lw (.lamt 0)).all
        (fun x => !x.isRes && !x.isLam) = true := by
  obtain ⟨-, -, hFw, -, hJ, -⟩ := RH_base ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  obtain ⟨e, he, P, Q, hσ, hx, hP⟩ := RH_iter RH_J1
    (fun X u v _ _ hJ X' hX' => RH_J1_step X X' u v hX' hJ) R.fpkg hJ p q R' hR'
  have hw : R'.wf = true := RH_iter (fun X => X.wf = true)
    (fun X u v _ _ h X' hX' => (pkg_dent_wf X X' u v h hX').1) R.fpkg hFw p q R' hR'
  have hP0 : PkgLetter.lw (.lamt 0) ∉ P := fun h => by
    have := (hP _ h).2
    simp [PkgLetter.isLam] at this
  refine ⟨?_, e, he, by rw [hσ]; simp, hx, ?_⟩
  · rw [(RH_sides R' hw e he 0 P Q hσ).2]
    exact RH_run_zero _ fun z hz => (hP z (List.mem_reverse.1 hz)).1
  · have htw : e.2.2.takeWhile (fun x => x != PkgLetter.lw (.lamt 0)) = P := by
      rw [hσ, List.takeWhile_append_of_pos (fun a ha => by
        simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hP0 ha),
        List.takeWhile_cons_of_neg (by simp)]
      simp
    rw [htw, List.all_eq_true]
    intro z hz
    simp [(hP z hz).1, (hP z hz).2]

/-- Q3 (d): a segment without `Λ̃` with two resolvents, or a side with two, survives the
derivatives as such a segment or side. -/
theorem pkg_rem_free (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    (R.fpkg.freeTwo = true → R'.freeTwo = true) ∧
      ∀ (o : Fin 2) (side : Bool), 2 ≤ R.fpkg.lamSide o side →
        2 ≤ R'.lamSide o side ∨ R'.freeTwo = true ∨ 2 ≤ R'.lamSide (1 - o) (!side) := by
  obtain ⟨-, -, hFw, -, -, hloc⟩ := RH_base ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have h := RH_iter (fun X => X.wf = true ∧ (∀ o, RH_loc X o) ∧
      (R.fpkg.freeTwo = true → X.freeTwo = true) ∧ ∀ o s, 2 ≤ R.fpkg.lamSide o s →
        2 ≤ X.lamSide o s ∨ X.freeTwo = true ∨ 2 ≤ X.lamSide (1 - o) (!s))
    (fun X u v _ _ hX X' hX' => by
      obtain ⟨hw, hl, hf, hs⟩ := hX
      refine ⟨(pkg_dent_wf X X' u v hw hX').1,
        fun o => (RH_side_step X X' u v hw hX' o (hl o)).1,
        fun h => RH_free_step X X' u v hX' (hf h), fun o s h2 => ?_⟩
      rcases hs o s h2 with h3 | h3 | h3
      · exact (RH_side_step X X' u v hw hX' o (hl o)).2 s |>.2.2 h3
      · exact Or.inr (Or.inl (RH_free_step X X' u v hX' h3))
      · rcases (RH_side_step X X' u v hw hX' (1 - o) (hl (1 - o))).2 (!s) |>.2.2 h3 with
          h4 | h4 | h4
        · exact Or.inr (Or.inr h4)
        · exact Or.inr (Or.inl h4)
        · rw [sub_sub_cancel, Bool.not_not] at h4
          exact Or.inl h4)
    R.fpkg ⟨hFw, hloc, id, fun _ _ h => Or.inl h⟩ p q R' hR'
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- The sides of a letter `Λ̃_o` alone in a loop without `Δ`, in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: both are the number of resolvents of the loop. -/
theorem pkg_lamSide_free (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : w.contains (.lw (.lamt o)) = true)
    (hfree : w.any PkgLetter.isEnt = false) (h1 : w.contains (.lw (.lamt (1 - o))) = false)
    (right : Bool) : R.lamSide o right = w.countP PkgLetter.isRes :=
  RH_lamSide_free R hR o w hw ho hfree h1 right

/-- The side chosen by the rules (i)–(iv) of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms] has a resolvent. -/
theorem pkg_ffocusSide_pos (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) (side : Bool)
    (h : R.ffocusSide = some (o, side)) : 1 ≤ R.lamSide o side :=
  RH_ffocusSide_pos R hR o side h

/-- The expanded word of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms] keeps a package of a word with `Δ`, without `Λ̃`, with at least
two resolvents. -/
theorem pkg_fpkg_freeTwo (R : PkgExpr) (hR : R.wf = true) (hf : R.ffocus.isSome = true)
    (h : R.freeTwo = true) : R.fpkg.freeTwo = true :=
  RH_fpkg_freeTwo R hf h

end RBMTransitionEdge
