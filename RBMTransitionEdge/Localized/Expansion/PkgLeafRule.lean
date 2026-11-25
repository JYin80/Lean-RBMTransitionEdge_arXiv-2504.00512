module

public import RBMTransitionEdge.Localized.Expansion.FRuleRun
public import RBMTransitionEdge.Localized.Expansion.PkgInv2
public import RBMTransitionEdge.Localized.Expansion.PkgLists
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.RemStep
public import RBMTransitionEdge.Localized.Expansion.RemCounts
public import RBMTransitionEdge.Localized.Expansion.RemHalves
public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.FFactor
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.FRule
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.FFactor
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.RemCounts
import all RBMTransitionEdge.Localized.Expansion.FRule

@[expose] public section

/-!
# The rule lemma of the leaves

For every leaf of the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]
(the further terminal cases (i)–(iii)): its labels are `0, 1`, and the assignment `fruleLeaf` of
the factor list of the rules is valid, and its bound with the prefactor of a leaf passes the rows.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### The run of `fruleLeaf` on three entries -/

/-- The uses of the four labels after the entries `cs` with their options. -/
private def PL_cap (cs : List (FEnt × Option FOpt)) : List ℕ :=
  [(cs.map fun c => fuseOne c 0).sum, (cs.map fun c => fuseOne c 1).sum,
    (cs.map fun c => fuseOne c 2).sum, (cs.map fun c => fuseOne c 3).sum]

/-- The uses of the labels `0, 1` by the entries `cs` with their options. -/
private def PL_U (cs : List (FEnt × Option FOpt)) : ℕ :=
  (cs.map fun c => fuseOne c 0 + fuseOne c 1).sum

/-- A list of length `4` is determined by its four values. -/
private lemma PL_list4 (L : List ℕ) (hL : L.length = 4) (v : ℕ → ℕ)
    (h : ∀ l : ℕ, l < 4 → L.getD l 0 = v l) : L = [v 0, v 1, v 2, v 3] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, L = [a, b, c, d] := by
    match L, hL with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]

/-- The value of `Forall₂` at one index. -/
private lemma PL_f2 {α β : Type*} (P : α → β → Prop) :
    ∀ (l₁ : List α) (l₂ : List β), List.Forall₂ P l₁ l₂ → ∀ (t : ℕ) (a : α), l₁[t]? = some a →
      ∃ b, l₂[t]? = some b ∧ P a b
  | [], _, _, t, a, h => by simp at h
  | x :: l₁, y :: l₂, List.Forall₂.cons hxy h, t, a, ha => by
      cases t with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
          subst ha
          exact ⟨y, rfl, hxy⟩
      | succ t =>
          simp only [List.getElem?_cons_succ] at ha ⊢
          exact PL_f2 P l₁ l₂ h t a ha

/-- The left fold of the product of monomials adds the components. -/
private lemma PL_foldl : ∀ (L : List FMono) (acc : FMono), L.foldl FMono.mul acc =
    ⟨acc.a + (L.map FMono.a).sum, acc.i + (L.map FMono.i).sum, acc.l + (L.map FMono.l).sum,
      acc.d + (L.map FMono.d).sum, acc.o + (L.map FMono.o).sum⟩
  | [], acc => by simp
  | q :: L, acc => by
      rw [List.foldl_cons, PL_foldl L]
      simp only [FMono.mul, List.map_cons, List.sum_cons, FMono.mk.injEq]
      omega

/-- The product of a list of monomials adds the components. -/
private lemma PL_prodL (L : List FMono) : FMono.prodL L =
    ⟨(L.map FMono.a).sum, (L.map FMono.i).sum, (L.map FMono.l).sum, (L.map FMono.d).sum,
      (L.map FMono.o).sum⟩ := by
  unfold FMono.prodL
  rw [PL_foldl]
  simp

/-- The run of `fruleLeaf` on a factor list with three entries: in the order of `fruleOrd`, the
entries `d₀, d₁, d₂` (a permutation of the entries, nondecreasing in `FEnt.role`) take the first
kind of their lists that fits the uses of the entries before them; the uses of the labels are
those of the three options; and every monomial of the bound is the label monomial times the sizes
of the loops and light weights times one monomial of each option. -/
private lemma PL_run (F : List FFac) (hE3 : (F.filterMap FFac.entData).length = 3) :
    ∃ (d0 d1 d2 : FEnt) (k0 k1 k2 : FKind) (o0 o1 o2 : FOpt),
      [d0, d1, d2].Perm (F.filterMap FFac.entData) ∧
      d0.role ≤ d1.role ∧ d1.role ≤ d2.role ∧
      fruleFit [0, 0, 0, 0] d0 true = some (k0, o0) ∧
      fruleFit (PL_cap [(d0, some o0)]) d1 true = some (k1, o1) ∧
      fruleFit (PL_cap [(d0, some o0), (d1, some o1)]) d2 true = some (k2, o2) ∧
      (∀ l : ℕ, l < 4 → fuses F (fruleLeaf F) l =
        ([(d0, some o0), (d1, some o1), (d2, some o2)].map fun c => fuseOne c l).sum) ∧
      ∀ mm ∈ fboundM F (fruleLeaf F), ∃ q0 ∈ o0.val, ∃ q1 ∈ o1.val, ∃ q2 ∈ o2.val,
        mm = ((⟨((List.range 4).map fun l => 2 - (fuses F (fruleLeaf F) l : ℤ)).sum, 0, 0, 0, 0⟩ :
          FMono).mul (FMono.prodL (F.map FFac.fixV))).mul ((q0.mul q1).mul q2) := by
  set E := F.filterMap FFac.entData with hEdef
  obtain ⟨hperm, hpair⟩ := frule_run_order E
  have hlen : (fruleOrd E).length = 3 := by rw [hperm.length_eq, List.length_range, hE3]
  obtain ⟨t0, t1, t2, hord⟩ := List.length_eq_three.1 hlen
  have hmem : ∀ t ∈ fruleOrd E, t < 3 := fun t ht => by
    have := hperm.subset ht
    simpa [hE3] using this
  rw [hord] at hmem hpair hperm
  have ht0 := hmem t0 (by simp)
  have ht1 := hmem t1 (by simp)
  have ht2 := hmem t2 (by simp)
  obtain ⟨d0, hd0⟩ : ∃ d, E[t0]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨d1, hd1⟩ : ∃ d, E[t1]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨d2, hd2⟩ : ∃ d, E[t2]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hk0 : (fruleOrd E)[0]? = some t0 := by rw [hord]; rfl
  have hk1 : (fruleOrd E)[1]? = some t1 := by rw [hord]; rfl
  have hk2 : (fruleOrd E)[2]? = some t2 := by rw [hord]; rfl
  have hg : fruleLeaf F = ⟨frk, fruleE E true⟩ := rfl
  rw [hg]
  have hcap : ∀ k l, l < 4 → (fruleCap E true k).getD l 0 =
      ((([t0, t1, t2].take k).map fun t =>
        (((fchosen F ⟨frk, fruleE E true⟩)[t]?).map fun c => fuseOne c l).getD 0)).sum := by
    intro k l hl
    rw [frule_run_cap F true k l hl, hord]
  have hlen4 : ∀ k, (fruleCap E true k).length = 4 := fun k =>
    (frule_run_mono E true k k 0 le_rfl).2.1
  have hcap0 : fruleCap E true 0 = [0, 0, 0, 0] := (frule_run_mono E true 0 0 0 le_rfl).1
  obtain ⟨⟨k0, o0⟩, hf0⟩ := Option.isSome_iff_exists.1 (frule_run_fits F true 0 t0 d0 hk0 hd0)
  rw [hcap0] at hf0
  obtain ⟨-, -, hc0⟩ := frule_run_chosen F true 0 t0 d0 hk0 hd0 k0 o0 (by rw [hcap0]; exact hf0)
  rw [← hEdef] at hc0
  have hcap1 : fruleCap E true 1 = PL_cap [(d0, some o0)] := by
    rw [PL_list4 _ (hlen4 1) (fun l => ([(d0, some o0)].map fun c => fuseOne c l).sum)]
    · rfl
    · intro l hl
      rw [hcap 1 l hl]
      simp [hc0]
  obtain ⟨⟨k1, o1⟩, hf1⟩ := Option.isSome_iff_exists.1 (frule_run_fits F true 1 t1 d1 hk1 hd1)
  obtain ⟨-, -, hc1⟩ := frule_run_chosen F true 1 t1 d1 hk1 hd1 k1 o1 hf1
  rw [← hEdef] at hc1
  rw [hcap1] at hf1
  have hcap2 : fruleCap E true 2 = PL_cap [(d0, some o0), (d1, some o1)] := by
    rw [PL_list4 _ (hlen4 2)
      (fun l => ([(d0, some o0), (d1, some o1)].map fun c => fuseOne c l).sum)]
    · rfl
    · intro l hl
      rw [hcap 2 l hl]
      simp [hc0, hc1]
  obtain ⟨⟨k2, o2⟩, hf2⟩ := Option.isSome_iff_exists.1 (frule_run_fits F true 2 t2 d2 hk2 hd2)
  obtain ⟨-, -, hc2⟩ := frule_run_chosen F true 2 t2 d2 hk2 hd2 k2 o2 hf2
  rw [← hEdef] at hc2
  rw [hcap2] at hf2
  have huses : ∀ l : ℕ, l < 4 → fuses F ⟨frk, fruleE E true⟩ l =
      ([(d0, some o0), (d1, some o1), (d2, some o2)].map fun c => fuseOne c l).sum := by
    intro l hl
    rw [frule_run_uses F true l hl, hE3, hcap 3 l hl]
    simp [hc0, hc1, hc2]
  -- the permutation of the entries
  have hgd : ∀ t d, E[t]? = some d → E.getD t FEnt.dflt = d := fun t d h => by
    rw [List.getD_eq_getElem?_getD, h]; rfl
  obtain ⟨e0, e1, e2, hE⟩ := List.length_eq_three.1 hE3
  have hPerm : [d0, d1, d2].Perm E := by
    have h1 := hperm.map (fun t => E.getD t FEnt.dflt)
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, hgd _ _ hd0, hgd _ _ hd1,
      hgd _ _ hd2] at h1
    refine h1.trans ?_
    rw [hE]
    rfl
  have hroles := hpair
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, hgd _ _ hd0, hgd _ _ hd1, hgd _ _ hd2] at hroles
  refine ⟨d0, d1, d2, k0, k1, k2, o0, o1, o2, hPerm, hroles.1.1, hroles.2.1, hf0, hf1, hf2, huses,
    fun mm hmm => ?_⟩
  obtain ⟨qs, hqs, rfl⟩ := (fboundM_mem F _ (frule_run_some F true) mm).1 hmm
  obtain ⟨b0, hb0, o', ho', hq0⟩ := PL_f2 _ _ _ hqs t0 _ hc0
  cases ho'
  obtain ⟨b1, hb1, o', ho', hq1⟩ := PL_f2 _ _ _ hqs t1 _ hc1
  cases ho'
  obtain ⟨b2, hb2, o', ho', hq2⟩ := PL_f2 _ _ _ hqs t2 _ hc2
  cases ho'
  refine ⟨b0, hq0, b1, hq1, b2, hq2, ?_⟩
  have hqlen : qs.length = 3 := by
    rw [← hqs.length_eq]
    refine le_antisymm ?_ ?_
    · unfold fchosen
      exact (List.length_filterMap_le _ _).trans (by rw [List.length_range]; exact hE3.le)
    · have h2 : 2 ∈ [t0, t1, t2] := hperm.symm.subset (List.mem_range.2 (by omega))
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h2
      rcases h2 with h | h | h <;> subst h
      · exact (List.getElem?_eq_some_iff.1 hc0).1
      · exact (List.getElem?_eq_some_iff.1 hc1).1
      · exact (List.getElem?_eq_some_iff.1 hc2).1
  have hqd : ∀ t b, qs[t]? = some b → qs.getD t ⟨0, 0, 0, 0, 0⟩ = b := fun t b h => by
    rw [List.getD_eq_getElem?_getD, h]; rfl
  have hQ : [b0, b1, b2].Perm qs := by
    have h1 := hperm.map (fun t => qs.getD t ⟨0, 0, 0, 0, 0⟩)
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, hqd _ _ hb0, hqd _ _ hb1,
      hqd _ _ hb2] at h1
    rw [hE3] at h1
    refine h1.trans ?_
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 hqlen
    rfl
  have hs : ∀ f : FMono → ℤ, (qs.map f).sum = f b0 + f b1 + f b2 := fun f => by
    rw [← (hQ.map f).sum_eq]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have hsn : ∀ f : FMono → ℕ, (qs.map f).sum = f b0 + f b1 + f b2 := fun f => by
    rw [← (hQ.map f).sum_eq]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  congr 1
  rw [PL_prodL qs]
  simp only [FMono.mul, hs, hsn]

/-! ### The factors of an expression: light weights, entries, loops -/

open private FW_g FW_rfacs FW_mk FW_rent FW_wf_free FW_wf_ent FW_fresN FW_fres FW_piece_cnt0
  FW_two_le FW_wf_count FW_one FW_sum_one from RBMTransitionEdge.Localized.Expansion.FEntWords
open private FF_ffacs FF_wf from RBMTransitionEdge.Localized.Expansion.FFactor
open private charsP_eq nfac isResP from RBMTransitionEdge.Localized.Expansion.PkgWords
open private RC_mem_rfacs RC_g_loop RC_g_ent RC_flet RC_E RC_rent_some RC_parts_len RC_isLam_cnt
  RC_letter' RC_onlyDet_res from RBMTransitionEdge.Localized.Expansion.RemCounts

/-- The factor is a light weight. -/
private def PL_isWt (f : FFac) : Bool := match f with
  | .wt _ _ => true
  | _ => false

/-- The sum of a component of the sizes `fixV` of a factor list: `(Nη)⁻¹` per light weight, and the
sizes of the loops (an entry has size `1`). -/
private lemma PL_fix_sum (p : FMono → ℤ) (hp : p ⟨0, 0, 0, 0, 0⟩ = 0) : ∀ F : List FFac,
    (F.map fun f => p f.fixV).sum = (F.countP PL_isWt : ℤ) * p ⟨-2, 0, 2, 0, 0⟩ +
      ((fLoops F).map fun w => p (FFac.loop w).fixV).sum
  | [] => by simp [fLoops]
  | f :: F => by
      have ih := PL_fix_sum p hp F
      rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
      · simp only [List.map_cons, List.sum_cons, FFac.fixV, hp, List.countP_cons, PL_isWt,
          fLoops, List.filterMap_cons] at ih ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add] at ih ⊢
        exact ih
      · simp only [List.map_cons, List.sum_cons, List.countP_cons, PL_isWt, fLoops,
          List.filterMap_cons] at ih ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at ih ⊢
        rw [ih]; ring
      · simp only [List.map_cons, List.sum_cons, FFac.fixV, List.countP_cons, PL_isWt, fLoops,
          List.filterMap_cons] at ih ⊢
        simp only [↓reduceIte] at ih ⊢
        rw [ih]; push_cast; ring

/-- The number of entries and loops of a factor list. -/
private lemma PL_one_sum : ∀ F : List FFac,
    (F.map FW_one).sum = (F.filterMap FFac.entData).length + (fLoops F).length
  | [] => by simp [fLoops]
  | f :: F => by
      have ih := PL_one_sum F
      rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
        simp only [List.map_cons, List.sum_cons, FW_one, fLoops, List.filterMap_cons,
          FFac.entData, List.length_cons] at ih ⊢ <;> omega

/-- `n`, the number of factors of Table 2 [table_effect_of_operations_2], is the number of
entries and loops of `rfacs`. -/
private lemma PL_n (X : PkgExpr) :
    X.charsP.2.1 = ((X.rfacs.filterMap FFac.entData).length + (fLoops X.rfacs).length : ℕ) := by
  rw [← PL_one_sum, FW_rfacs, List.map_map]
  have : (FW_one ∘ FW_g X) = FW_one := funext fun f => by
    unfold FW_g
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> split_ifs <;> rfl
  rw [this, FW_sum_one, charsP_eq]

/-- The light weights of `rfacs` are those of the expression. -/
private lemma PL_wt (X : PkgExpr) : X.rfacs.countP PL_isWt = X.weights.length := by
  rw [FW_rfacs, List.countP_map, FF_ffacs, List.countP_append]
  have hg : (PL_isWt ∘ FW_g X) = PL_isWt := funext fun f => by
    unfold FW_g
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> split_ifs <;> rfl
  rw [hg]
  have h1 : (X.weights.map fun p => FFac.wt p.1 p.2).countP PL_isWt = X.weights.length := by
    rw [List.countP_eq_length.2 (fun f hf => by obtain ⟨p, -, rfl⟩ := List.mem_map.1 hf; rfl),
      List.length_map]
  have h2 : (X.loops.flatMap (FF_wf (fun _ => false) X.fpm)).countP PL_isWt = 0 := by
    refine List.countP_eq_zero.2 fun f hf => ?_
    obtain ⟨w, -, hf⟩ := List.mem_flatMap.1 hf
    cases hw : w.any PkgLetter.isEnt
    · rw [FW_wf_free _ w hw, List.mem_singleton] at hf
      subst hf
      simp [PL_isWt]
    · rw [FW_wf_ent _ w hw, List.mem_map] at hf
      obtain ⟨e, -, rfl⟩ := hf
      simp [PL_isWt, FW_mk]
  rw [h1, h2, add_zero]

/-- A loop factor of `rfacs` comes from a word without `Δ`. -/
private lemma PL_loop_src (X : PkgExpr) (W : List FLet) (hW : W ∈ fLoops X.rfacs) :
    ∃ w₀ ∈ X.loops, w₀.any PkgLetter.isEnt = false ∧
      FW_g X (.loop (w₀.filterMap (PkgLetter.flet (fun _ => false) X.fpm))) = .loop W := by
  obtain ⟨f, hf, hfW⟩ := List.mem_filterMap.1 hW
  rcases f with ⟨x, y, W'⟩ | W' | ⟨a, x⟩ <;> simp only [Option.some.injEq, reduceCtorEq] at hfW
  subst hfW
  rcases RC_mem_rfacs X _ hf with ⟨p, -, h⟩ | ⟨e, -, h⟩ | ⟨w₀, hw₀, hE, h⟩
  · cases h
  · rw [FW_rent] at h
    unfold FW_mk at h
    obtain ⟨W'', hW'', -⟩ := RC_g_ent X e.1 e.2.1
      (e.2.2.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
    rw [hW''] at h
    cases h
  · exact ⟨w₀, hw₀, hE, h.symm⟩

/-- A word without `Δ` gives a loop factor of `rfacs`. -/
private lemma PL_loop_mem (X : PkgExpr) (w₀ : List PkgLetter) (hw : w₀ ∈ X.loops)
    (hE : w₀.any PkgLetter.isEnt = false) :
    ∃ W ∈ fLoops X.rfacs,
      FW_g X (.loop (w₀.filterMap (PkgLetter.flet (fun _ => false) X.fpm))) = .loop W := by
  obtain ⟨W, hW, -⟩ := RC_g_loop X (w₀.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
  refine ⟨W, List.mem_filterMap.2 ⟨.loop W, ?_, rfl⟩, hW⟩
  rw [← hW, FW_rfacs, FF_ffacs]
  refine List.mem_map_of_mem (List.mem_append_right _ (List.mem_flatMap.2 ⟨w₀, hw, ?_⟩))
  rw [FW_wf_free _ w₀ hE]
  exact List.mem_singleton_self _

/-- Doubling the resolvents of a word without resolvent changes nothing. -/
private lemma PL_dup_nores (a : Fin 2) : ∀ W : List FLet, W.countP FW_fres = 0 →
    W.flatMap (FLet.dupRes a) = W
  | [], _ => rfl
  | x :: W, h => by
      rw [List.countP_cons] at h
      have hW : W.countP FW_fres = 0 := by omega
      rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y | _
      · simp [FW_fres] at h
      all_goals simp [FLet.dupRes, PL_dup_nores a W hW]

/-- The pairing through `𝒢` keeps a loop without resolvent. -/
private lemma PL_g_nores (X : PkgExpr) (W : List FLet) (h : W.countP FW_fres = 0) :
    FW_g X (.loop W) = .loop W := by
  unfold FW_g
  split_ifs <;> simp [FFac.dupRes, PL_dup_nores _ W h]

/-- The letters of a word without `Δ` as factor letters. -/
private lemma PL_flet_map (pr : Fin 2 → Bool) : ∀ w : List PkgLetter,
    w.any PkgLetter.isEnt = false →
    w.filterMap (PkgLetter.flet (fun _ => false) pr) =
      w.map fun x => (PkgLetter.flet (fun _ => false) pr x).getD .lamt
  | [], _ => rfl
  | x :: w, h => by
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      have ih := PL_flet_map pr w h.2
      rcases x with ((b | b | y | o) | ⟨u, v⟩)
      · simp [PkgLetter.flet, ih]
      · simp [PkgLetter.flet, ih]
      · simp [PkgLetter.flet, ih]
      · simp [PkgLetter.flet, ih]
      · simp [PkgLetter.isEnt] at h

/-! ### The leaves: entries, loops, Type -/

/-- An entry of a factor list has at least one part, and its extra size is `(Im m)^{2c}`. -/
private lemma PL_ent_form (F : List FFac) (d : FEnt) (hd : d ∈ F.filterMap FFac.entData) :
    1 ≤ d.2.2.1.length ∧ ∃ c : ℕ, d.2.2.2.1 = ⟨0, 2 * (c : ℤ), 0, 0, 0⟩ := by
  obtain ⟨f, -, hf⟩ := List.mem_filterMap.1 hd
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
    simp only [FFac.entData, Option.some.injEq, reduceCtorEq] at hf
  subst hf
  refine ⟨?_, _, rfl⟩
  simp only [FLet.parts, List.length_map]
  exact List.length_pos_of_ne_nil (List.splitOnP_ne_nil _ w)

/-- At a leaf, `Λ̃₁` is not in a word without `Δ`. -/
private lemma PL_lam1_free (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (w₀ : List PkgLetter) (hw₀ : w₀ ∈ R.loops)
    (hE : w₀.any PkgLetter.isEnt = false) : PkgLetter.lw (.lamt 0) ∉ w₀ := by
  intro hm
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨w, hw, hwE, σ, hσ, hmσ, -⟩ := pkg_inv_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨e, he, rfl⟩ := pkg_pents_segs R w hw hwE σ hσ
  obtain ⟨w', hw', hw'E, hm'⟩ := RC_letter' R e he _ hmσ
  have hne : w' ≠ w₀ := by
    rintro rfl
    rw [hE] at hw'E
    cases hw'E
  have := FW_two_le (fun w => w.count (PkgLetter.lw (.lamt 0))) w' w₀ hne
    (List.count_pos_iff.2 hm') (List.count_pos_iff.2 hm) R.loops hw' hw₀
  rw [FW_wf_count R hRw 0] at this
  omega

/-- At a leaf, a word without `Δ` with a letter `Λ̃` holds `Λ̃₂` and no resolvent (its sides are
empty). -/
private lemma PL_lam_free (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) (w₀ : List PkgLetter) (hw₀ : w₀ ∈ R.loops)
    (hE : w₀.any PkgLetter.isEnt = false) (o : Fin 2) (ho : PkgLetter.lw (.lamt o) ∈ w₀) :
    o = 1 ∧ w₀.countP PkgLetter.isRes = 0 := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  have h0 := PL_lam1_free ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR w₀ hw₀ hE
  have ho1 : o = 1 := by
    fin_cases o
    · exact absurd ho h0
    · rfl
  subst ho1
  refine ⟨rfl, ?_⟩
  have hs := pkg_lamSide_free R hRw 1 w₀ hw₀ (by simpa using ho) hE (by simpa using h0) true
  rw [(pkg_leaf_sides ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf).1 1 true] at hs
  omega

/-- At a leaf, a loop factor without `Λ̃` has at least two resolvents, and a loop factor with
`Λ̃` has none. -/
private lemma PL_loop_facts (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) (W : List FLet)
    (hW : W ∈ fLoops R.rfacs) :
    (FLet.lamt ∉ W → 2 ≤ fresN W) ∧ (FLet.lamt ∈ W → fresN W = 0) := by
  obtain ⟨w₀, hw₀, hE, h⟩ := PL_loop_src R W hW
  obtain ⟨W', hW', hsub, hsup, hcnt⟩ :=
    RC_g_loop R (w₀.filterMap (PkgLetter.flet (fun _ => false) R.fpm))
  rw [hW'] at h
  injection h with h
  subst h
  refine ⟨fun hlam => ?_, fun hlam => ?_⟩
  · have hL : w₀.any PkgLetter.isLam = false := by
      refine List.any_eq_false.2 fun x hx hxl => hlam ?_
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> simp [PkgLetter.isLam] at hxl
      exact hsup _ (List.mem_filterMap.2 ⟨_, hx, rfl⟩) (fun _ _ h => by cases h)
    have h2 := pkg_ffree_two ε n T hT p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR) w₀ hw₀ hE hL
    rw [FW_fresN]
    rw [FW_piece_cnt0] at hcnt
    omega
  · have h0 := hsub _ hlam (fun _ _ h => by cases h)
    obtain ⟨-, -, h3⟩ := RC_flet R.fpm w₀ _ h0
    obtain ⟨o, ho⟩ := h3 rfl
    obtain ⟨-, hres⟩ := PL_lam_free ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf w₀ hw₀ hE o ho
    have hc0 : (w₀.filterMap (PkgLetter.flet (fun _ => false) R.fpm)).countP FW_fres = 0 := by
      rw [FW_piece_cnt0]
      exact hres
    rw [PL_g_nores R _ hc0] at hW'
    injection hW' with hW''
    rw [FW_fresN, ← hW'', hc0]

/-- At a leaf with `gainLam2`, the loop factor of `Λ̃₂` holds `Λ̃` and is `⟨𝔐_a Λ̃ 𝔐_b E_x⟩` up to
rotation, with `a ≠ b`. -/
private lemma PL_gain (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) (hg : R.gainLam2 = true) :
    ∃ W ∈ fLoops R.rfacs, FLet.lamt ∈ W ∧ ∃ r < W.length, ∃ (a b : Fin 2) (pa pb : Bool) (x : ℕ),
      a ≠ b ∧ W.rotate r = [.det a pa, .lamt, .det b pb, .proj x] := by
  unfold PkgExpr.gainLam2 at hg
  obtain ⟨w₀, hw₀, hc⟩ := List.any_eq_true.1 hg
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
  obtain ⟨⟨hl2, hE⟩, hgl⟩ := hc
  have hl2' : PkgLetter.lw (.lamt 1) ∈ w₀ := by simpa using hl2
  obtain ⟨-, hres⟩ := PL_lam_free ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf w₀ hw₀ hE 1 hl2'
  obtain ⟨W, hW, hWeq⟩ := PL_loop_mem R w₀ hw₀ hE
  have hc0 : (w₀.filterMap (PkgLetter.flet (fun _ => false) R.fpm)).countP FW_fres = 0 := by
    rw [FW_piece_cnt0]
    exact hres
  rw [PL_g_nores R _ hc0] at hWeq
  injection hWeq with hWeq
  subst hWeq
  refine ⟨_, hW, List.mem_filterMap.2 ⟨_, hl2', rfl⟩, ?_⟩
  rw [PL_flet_map R.fpm w₀ hE]
  unfold pkgGainLoop at hgl
  obtain ⟨r, hr, hm⟩ := List.any_eq_true.1 hgl
  refine ⟨r, by simpa using hr, ?_⟩
  rw [← List.map_rotate]
  generalize w₀.rotate r = V at hm ⊢
  split at hm
  · rename_i a o b x
    refine ⟨a, b, R.fpm a, R.fpm b, x, by simpa using hm, ?_⟩
    simp [PkgLetter.flet]
  · cases hm

/-- The size of the loop factor `⟨𝔐_a Λ̃ 𝔐_b E_x⟩`, `a ≠ b`: `(Nη)⁻¹ ‖A‖_HS² Im m`. -/
private lemma PL_gain_val (W : List FLet) (hc : W.count FLet.lamt = 1) (hr : fresN W = 0)
    (r : ℕ) (hrl : r < W.length) (a b : Fin 2) (pa pb : Bool) (x : ℕ) (hab : a ≠ b)
    (hrot : W.rotate r = [.det a pa, .lamt, .det b pb, .proj x]) :
    (FFac.loop W).fixV.i = 2 := by
  have hnl : W.countP (· == FLet.lamt) = W.count FLet.lamt := rfl
  simp only [FFac.fixV, hnl, hc, ↓reduceIte, one_ne_zero]
  split_ifs with hr' hg
  · rfl
  · exfalso
    apply hg
    refine List.any_eq_true.2 ⟨r, List.mem_range.2 hrl, ?_⟩
    rw [hrot]
    simp [hab]
  · exact absurd hr hr'

/-- The Type is `1`, `2` or `3`. -/
private lemma PL_ptype_le (X : PkgExpr) : X.ptype ≤ 3 := by
  unfold PkgExpr.ptype
  split
  · omega
  · split_ifs <;> omega

/-- At a leaf, the entry of `Λ̃₁` has at least two parts. -/
private lemma PL_lam1_ent (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) :
    ∃ d ∈ R.rfacs.filterMap FFac.entData, 2 ≤ d.2.2.1.length := by
  obtain ⟨w, hw, hwE, σ, hσ, hmσ, -⟩ := pkg_inv_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨e, he, rfl⟩ := pkg_pents_segs R w hw hwE σ hσ
  obtain ⟨d, hd, -, -⟩ := RC_rent_some R e
  refine ⟨d, ?_, ?_⟩
  · rw [RC_E]
    exact List.mem_filterMap.2 ⟨e, he, hd⟩
  · obtain ⟨-, -, hl, -⟩ := pkg_rent_parts R e he d hd
    rw [hl, RC_parts_len]
    have : 0 < e.2.2.countP PkgLetter.isLam := List.countP_pos_iff.2 ⟨_, hmσ, rfl⟩
    omega

/-- In Type III (5.81) [further_expansion_expression_Type_3], one entry has three parts. -/
private lemma PL_ptype3 (X : PkgExpr) (hX : X.ptype = 3) :
    ∃ d ∈ X.rfacs.filterMap FFac.entData, 3 ≤ d.2.2.1.length := by
  obtain ⟨e, he, h0, h1⟩ := pkg_ptype3_seg X hX
  obtain ⟨d, hd, -, -⟩ := RC_rent_some X e
  refine ⟨d, ?_, ?_⟩
  · rw [RC_E]
    exact List.mem_filterMap.2 ⟨e, he, hd⟩
  · obtain ⟨-, -, hl, -⟩ := pkg_rent_parts X e he d hd
    rw [hl, RC_parts_len, RC_isLam_cnt]
    have := List.count_pos_iff.2 h0
    have := List.count_pos_iff.2 h1
    omega

/-- In Type II (5.80) [further_expansion_expression_Type_2], a loop factor holds `Λ̃`. -/
private lemma PL_ptype2 (X : PkgExpr) (hX : X.ptype = 2) :
    ∃ W ∈ fLoops X.rfacs, FLet.lamt ∈ W := by
  unfold PkgExpr.ptype at hX
  rcases hfind : X.loops.find? (fun w => w.contains (.lw (.lamt 1))) with _ | w₂
  · rw [hfind] at hX
    cases hX
  rw [hfind] at hX
  have hw₂ : w₂ ∈ X.loops := List.mem_of_find?_eq_some hfind
  have hl : PkgLetter.lw (.lamt 1) ∈ w₂ := by simpa using List.find?_some hfind
  simp only at hX
  split_ifs at hX with h1 h2
  all_goals try (exfalso; omega)
  have h1' : (!(w₂.any PkgLetter.isEnt)) = true := h1
  have hE : w₂.any PkgLetter.isEnt = false := by simpa using h1'
  obtain ⟨W, hW, hWeq⟩ := PL_loop_mem X w₂ hw₂ hE
  obtain ⟨W', hW', -, hsup, -⟩ :=
    RC_g_loop X (w₂.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
  rw [hW'] at hWeq
  injection hWeq with hWeq
  subst hWeq
  exact ⟨W', hW, hsup _ (List.mem_filterMap.2 ⟨_, hl, rfl⟩) (fun _ _ h => by cases h)⟩

/-- The resolvents of a word are those of slot `0` and slot `1`. -/
private lemma PL_res_split : ∀ w : List PkgLetter,
    (w.countP fun x => match x with | .lw (.res _) => true | _ => false) =
      w.count (.lw (.res 0)) + w.count (.lw (.res 1))
  | [] => rfl
  | x :: w => by
      have ih := PL_res_split w
      rw [List.countP_cons, List.count_cons, List.count_cons, ih]
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases b
      all_goals simp
      all_goals omega

/-- With `fR = 2` and `Σ = 0`, slot `1` only through one `𝔐₁` excludes the pairing through
`𝒢`: `π = 0`. -/
private lemma PL_M6 (X : PkgExpr) (hfR : X.fR = 2) (hs : X.fsig = 0) (h1 : X.onlyDet 1 = true) :
    X.fpi = 0 := by
  have h1' := h1
  unfold PkgExpr.onlyDet at h1'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h1'
  obtain ⟨⟨hw1, hr1⟩, -⟩ := h1'
  have hc1 : (X.loops.map fun w => w.count (.lw (.res 1))).sum = 0 :=
    List.sum_eq_zero fun k hk => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
      have := hr1 w hw
      exact List.count_eq_zero.2 (by simpa using this)
  have hg1 : X.fpg 1 = false := by
    unfold PkgExpr.fpg PkgExpr.onlyRes
    simp [hc1]
  have hg0 : X.fpg 0 = false := by
    by_contra hcon
    have hg : X.fpg 0 = true := by simpa using hcon
    unfold PkgExpr.fpg PkgExpr.onlyRes at hg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hg
    obtain ⟨⟨⟨hw0, -⟩, hc0⟩, -⟩ := hg
    have hnil : X.weights = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      have a0 := hw0 p hp
      have a1 := hw1 p hp
      obtain ⟨a, x⟩ := p
      fin_cases a <;> simp_all
    have hm : X.charsP.1 = 1 := by
      rw [charsP_eq]
      simp only
      have : (X.loops.map fun w => w.countP isResP).sum =
          (X.loops.map fun w => w.count (.lw (.res 0))).sum +
            (X.loops.map fun w => w.count (.lw (.res 1))).sum := by
        rw [← List.sum_map_add]
        exact congrArg List.sum (List.map_congr_left fun w _ => PL_res_split w)
      rw [this, hc0, hc1]
      rfl
    have hfs : X.fsig = X.charsP.1 + X.charsP.2.2.1 + X.fR - 4 := rfl
    have hu : X.charsP.2.2.1 = (X.weights.length : ℤ) := rfl
    rw [hnil] at hu
    rw [hfs, hm, hu, hfR] at hs
    simp at hs
  simp [PkgExpr.fpi, hg0, hg1]

/-- Slot `1` only through one `𝔐₁`, every word with `Δ`, and a resolvent of slot `0`: the
pairing through `𝔐₁` of the rules. -/
private lemma PL_fpm1 (X : PkgExpr) (h1 : X.onlyDet 1 = true)
    (hE : ∀ w ∈ X.loops, w.any PkgLetter.isEnt = true) (w : List PkgLetter) (hw : w ∈ X.loops)
    (hr : PkgLetter.lw (.res 0) ∈ w) : X.fpm 1 = true := by
  have h0 := RC_onlyDet_res X 0 w hw hr
  unfold PkgExpr.fpm
  simp only [h1, h0, Bool.true_and, Bool.false_and, Bool.not_false, Bool.or_true, Bool.and_true]
  exact List.all_eq_true.2 fun w hw => by simp [hE w hw]

/-- Slot `1` only through one `𝔐₁`, no loop factor, and two resolvents: the pairing through
`𝔐₁` of the rules. -/
private lemma PL_typeIII_fpm (X : PkgExpr) (h1 : X.onlyDet 1 = true) (hL : fLoops X.rfacs = [])
    (hm : X.charsP.1 = 2) : X.fpm 1 = true := by
  have hE : ∀ w ∈ X.loops, w.any PkgLetter.isEnt = true := fun w hw => by
    by_contra hc
    obtain ⟨W, hW, -⟩ := PL_loop_mem X w hw (by simpa using hc)
    rw [hL] at hW
    cases hW
  have h1' := h1
  unfold PkgExpr.onlyDet at h1'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h1'
  obtain ⟨⟨-, hr1⟩, -⟩ := h1'
  have hc1 : (X.loops.map fun w => w.count (.lw (.res 1))).sum = 0 :=
    List.sum_eq_zero fun k hk => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
      exact List.count_eq_zero.2 (by simpa using hr1 w hw)
  have hc0 : (X.loops.map fun w => w.count (.lw (.res 0))).sum = 2 := by
    rw [charsP_eq] at hm
    simp only at hm
    have : (X.loops.map fun w => w.countP isResP).sum =
        (X.loops.map fun w => w.count (.lw (.res 0))).sum +
          (X.loops.map fun w => w.count (.lw (.res 1))).sum := by
      rw [← List.sum_map_add]
      exact congrArg List.sum (List.map_congr_left fun w _ => PL_res_split w)
    rw [this, hc1] at hm
    omega
  obtain ⟨w, hw, hpos⟩ : ∃ w ∈ X.loops, 0 < w.count (.lw (.res 0)) := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt, Nat.le_zero] at hcon
    have : (X.loops.map fun w => w.count (.lw (.res 0))).sum = 0 :=
      List.sum_eq_zero fun k hk => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        exact hcon w hw
    omega
  exact PL_fpm1 X h1 hE w hw (List.count_pos_iff.1 hpos)

/-! ### The loops of a leaf, summed -/

/-- `ψ(0) = 1`. -/
private lemma PL_psi_zero : FMono.psi 0 = ⟨0, 0, 0, 0, 0⟩ := rfl

/-- `ψ(1) = 1`. -/
private lemma PL_psi_one : FMono.psi 1 = ⟨0, 0, 0, 0, 0⟩ := rfl

/-- `ψ(r) = (Im m) η^{1-r}` for `r ≥ 2`. -/
private lemma PL_psi_ge (r : ℕ) (h : 2 ≤ r) : FMono.psi r = ⟨0, 2, 2 * ((r : ℤ) - 1), 0, 0⟩ := by
  simp [FMono.psi, h]

/-- `ω(0) = 1`. -/
private lemma PL_omega_zero : FMono.omega 0 = ⟨0, 0, 0, 0, 0⟩ := rfl

/-- `ω(r) = (Im m)^{1/2} η^{1/2-r}` for `r ≥ 1`. -/
private lemma PL_omega_ge (r : ℕ) (h : 1 ≤ r) : FMono.omega r = ⟨0, 1, 2 * (r : ℤ) - 1, 0, 0⟩ := by
  simp [FMono.omega, h]

/-- The size of one loop factor of a leaf: `ψ(r)` with `r ≥ 2` without `Λ̃`, `(Nη)⁻¹ ‖A‖_HS²`,
with `Im m` when it passes the gain test, with one `Λ̃` and no resolvent. -/
private lemma PL_loop_val (W : List FLet) (h1 : FLet.lamt ∉ W → 2 ≤ fresN W)
    (h2 : FLet.lamt ∈ W → fresN W = 0) (h3 : W.count FLet.lamt ≤ 1) :
    (FFac.loop W).fixV.a = -2 * (W.count FLet.lamt : ℤ) ∧
    (FFac.loop W).fixV.l = 2 * ((fresN W : ℤ) - 1) + 2 * (W.count FLet.lamt : ℤ) ∧
    (FFac.loop W).fixV.d = 2 * W.count FLet.lamt ∧ (FFac.loop W).fixV.o = 0 ∧
    ((FFac.loop W).fixV.i = 2 ∨ (W.count FLet.lamt = 1 ∧ (FFac.loop W).fixV.i = 0)) ∧
    1 - 2 * (W.count FLet.lamt : ℤ) ≤ (fresN W : ℤ) - 1 := by
  have hnl : W.countP (· == FLet.lamt) = W.count FLet.lamt := rfl
  rcases Nat.lt_or_ge (W.count FLet.lamt) 1 with hc | hc
  · have hc0 : W.count FLet.lamt = 0 := by omega
    have hge := h1 (List.count_eq_zero.1 hc0)
    have hfix : (FFac.loop W).fixV = FMono.psi (fresN W) := by
      simp only [FFac.fixV, hnl, hc0, ↓reduceIte]
      rfl
    rw [hfix, PL_psi_ge _ hge, hc0]
    refine ⟨by simp, by simp, by simp, by simp, Or.inl rfl, by push_cast; omega⟩
  · have hc1 : W.count FLet.lamt = 1 := by omega
    have hr0 := h2 (List.count_pos_iff.1 (by omega))
    rw [hc1]
    have hfix : (FFac.loop W).fixV.a = -2 ∧ (FFac.loop W).fixV.l = 0 ∧
        (FFac.loop W).fixV.d = 2 ∧ (FFac.loop W).fixV.o = 0 ∧
        ((FFac.loop W).fixV.i = 2 ∨ (FFac.loop W).fixV.i = 0) := by
      simp only [FFac.fixV, hnl, hc1, ↓reduceIte, one_ne_zero]
      split_ifs with hr' hg
      · simp
      · simp
      · exact absurd hr0 hr'
    rw [hr0]
    obtain ⟨g1, g2, g3, g4, g5⟩ := hfix
    refine ⟨by rw [g1]; norm_num, by rw [g2]; norm_num, by rw [g3], g4, ?_, by norm_num⟩
    rcases g5 with g5 | g5
    · exact Or.inl g5
    · exact Or.inr ⟨rfl, g5⟩

/-- The facts of one loop factor of a leaf. -/
private def PL_LoopOK (W : List FLet) : Prop :=
  (FLet.lamt ∉ W → 2 ≤ fresN W) ∧ (FLet.lamt ∈ W → fresN W = 0) ∧ W.count FLet.lamt ≤ 1

/-- The sizes of the loop factors of a leaf, summed. -/
private lemma PL_agg : ∀ Ls : List (List FLet), (∀ W ∈ Ls, PL_LoopOK W) →
    (Ls.map fun W => (FFac.loop W).fixV.a).sum =
      -2 * (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum ∧
    (Ls.map fun W => (FFac.loop W).fixV.l).sum =
      2 * (Ls.map fun W => (fresN W : ℤ) - 1).sum +
        2 * (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum ∧
    (Ls.map fun W => ((FFac.loop W).fixV.d : ℤ)).sum =
      2 * (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum ∧
    (Ls.map fun W => ((FFac.loop W).fixV.o : ℤ)).sum = 0 ∧
    (Ls.length : ℤ) - 2 * (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum ≤
      (Ls.map fun W => (fresN W : ℤ) - 1).sum ∧
    2 * (Ls.length : ℤ) - 2 * (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum ≤
      (Ls.map fun W => (FFac.loop W).fixV.i).sum ∧
    (Ls.map fun W => (FFac.loop W).fixV.i).sum ≤ 2 * (Ls.length : ℤ) ∧
    (Ls.map fun W => (FFac.loop W).fixV.i).sum % 2 = 0
  | [], _ => by simp
  | W :: Ls, h => by
      have hW := h W List.mem_cons_self
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := PL_loop_val W hW.1 hW.2.1 hW.2.2
      have ih := PL_agg Ls fun W hW => h W (List.mem_cons_of_mem _ hW)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      rw [a1, a2, a3, a4]
      push_cast
      omega

/-- A loop factor of a leaf with one `Λ̃` that passes the gain test lifts the sum of the powers of
`Im m` of the loops by `2`. -/
private lemma PL_agg_gain : ∀ Ls : List (List FLet), (∀ W ∈ Ls, PL_LoopOK W) →
    ∀ W₀ ∈ Ls, W₀.count FLet.lamt = 1 → (FFac.loop W₀).fixV.i = 2 →
    2 * (Ls.length : ℤ) - 2 * (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum + 2 ≤
      (Ls.map fun W => (FFac.loop W).fixV.i).sum
  | [], _, W₀, h, _, _ => by simp at h
  | W :: Ls, h, W₀, hW₀, hc, hi => by
      have hW := h W List.mem_cons_self
      obtain ⟨-, -, -, -, a5, -⟩ := PL_loop_val W hW.1 hW.2.1 hW.2.2
      have hagg := PL_agg Ls fun W hW => h W (List.mem_cons_of_mem _ hW)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      rcases List.mem_cons.1 hW₀ with rfl | hW₀'
      · rw [hc, hi]
        push_cast
        omega
      · have ih := PL_agg_gain Ls (fun W hW => h W (List.mem_cons_of_mem _ hW)) W₀ hW₀' hc hi
        omega

/-- The role of an entry with labels `0, 1`: `1` with `Λ̃`, `3` without. -/
private lemma PL_role (d : FEnt) (hx : d.1 < 2) (hy : d.2.1 < 2) :
    d.role = if 2 ≤ d.2.2.1.length then 1 else 3 := by
  unfold FEnt.role fInnerL
  simp [show ¬ 2 ≤ d.1 by omega, show ¬ 2 ≤ d.2.1 by omega]

/-- The ends at label `1` of an entry with labels `0, 1`. -/
private lemma PL_cnt1 (x y : ℕ) (hx : x < 2) (hy : y < 2) : [x, y].count 1 = x + y := by
  interval_cases x <;> interval_cases y <;> rfl

/-- The uses of the labels `2, 3` by an entry with labels `0, 1` are `0`. -/
private lemma PL_fuse23 (d : FEnt) (o : Option FOpt) (hx : d.1 < 2) (hy : d.2.1 < 2) :
    fuseOne (d, o) 2 = 0 ∧ fuseOne (d, o) 3 = 0 := by
  unfold fuseOne
  rcases o with _ | o
  · exact ⟨rfl, rfl⟩
  · simp only
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega

/-- The number of empty sides next to `Λ̃` when every side is empty. -/
private lemma PL_empty (X : PkgExpr) (hs : ∀ (o : Fin 2) (side : Bool), X.lamSide o side = 0) :
    X.emptySides = if X.ptype = 1 then 3 else 2 := by
  unfold PkgExpr.emptySides
  simp only [hs]
  split <;> simp_all

/-! ### The rows, Type by Type

The three profiles of the entries of a leaf, in the order of the rule: `(2, 0, 0)` (one entry
with both `Λ̃`), `(1, 1, 0)`, and `(1, 0, 0)` with `Λ̃₂` in a loop. In each, the rule is evaluated
for every placement of the labels `0, 1`, and the integer test of the bound with the prefactor
reduces to linear inequalities in `fR`, `u`, `π`, the resolvents and the loops. -/

open private FR_ok_iff from RBMTransitionEdge.Localized.Expansion.FRule

set_option linter.flexible false in
set_option maxHeartbeats 4000000 in -- `simp` evaluates the rule at every placement of the labels
/-- The rows for the profile `(2, 0, 0)` (Type III, or Type I with `fR ≥ 3`). -/
private lemma PL_coreA (x0 y0 x1 y1 x2 y2 : ℕ) (hx0 : x0 < 2) (hy0 : y0 < 2) (hx1 : x1 < 2)
    (hy1 : y1 < 2) (hx2 : x2 < 2) (hy2 : y2 < 2) (hsum : x0 + y0 + x1 + y1 + x2 + y2 = 3)
    (r1 r2 : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2) (i0 i1 i2 : ℤ)
    (hei : (i0 = 0 ∨ i0 = 2) ∧ (i1 = 0 ∨ i1 = 2) ∧ (i2 = 0 ∨ i2 = 2) ∧ i0 + i1 + i2 ≤ 2)
    (b0 b1 b2 : Bool) (k0 k1 k2 : FKind) (o0 o1 o2 : FOpt)
    (h0 : fruleFit [0, 0, 0, 0] (x0, y0, [0, 0, 0], ⟨0, i0, 0, 0, 0⟩, b0) true = some (k0, o0))
    (h1 : fruleFit (PL_cap [((x0, y0, [0, 0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0)])
      (x1, y1, [r1], ⟨0, i1, 0, 0, 0⟩, b1) true = some (k1, o1))
    (h2 : fruleFit (PL_cap [((x0, y0, [0, 0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0),
      ((x1, y1, [r1], ⟨0, i1, 0, 0, 0⟩, b1), some o1)]) (x2, y2, [r2], ⟨0, i2, 0, 0, 0⟩, b2)
      true = some (k2, o2))
    (q0 q1 q2 : FMono) (hq0 : q0 ∈ o0.val) (hq1 : q1 ∈ o1.val) (hq2 : q2 ∈ o2.val)
    (fR u π T nL IL m : ℤ) (hu : 0 ≤ u) (hπ : 0 ≤ π ∧ π ≤ 1) (hnL : 0 ≤ nL) (hT : nL ≤ T)
    (hIL : IL = 2 * nL) (hsig : 0 ≤ m + u + fR - 4) (hm : m = r1 + r2 + T + nL - π)
    (hTy : 3 ≤ fR ∨ (2 ≤ fR ∧ (fR = 2 → m + u + fR - 4 = 0 → i0 + i1 + i2 = 2 ∧ π = 0)))
    (M : FMono)
    (hMa : M.a = 1 - ((PL_U [((x0, y0, [0, 0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0),
      ((x1, y1, [r1], ⟨0, i1, 0, 0, 0⟩, b1), some o1),
      ((x2, y2, [r2], ⟨0, i2, 0, 0, 0⟩, b2), some o2)] : ℕ) : ℤ) - 2 * u - 2 * fR -
      2 * (-1 + ((r1 : ℤ) - 1) + ((r2 : ℤ) - 1)) - 2 * T + 2 * π + q0.a + q1.a + q2.a)
    (hMi : M.i = q0.i + q1.i + q2.i + IL)
    (hMl : M.l = 2 * u + 2 * T + q0.l + q1.l + q2.l - 2 * π)
    (hMd : M.d = q0.d + q1.d + q2.d) (hMo : M.o = q0.o + q1.o + q2.o) :
    M.ok = true := by
  rw [FR_ok_iff, hMa, hMi, hMl, hMd, hMo]
  clear hMa hMi hMl hMd hMo
  interval_cases x0 <;> interval_cases y0 <;> interval_cases x1 <;> interval_cases y1 <;>
    interval_cases x2 <;> interval_cases y2 <;> (try omega) <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk] at h0 <;>
    obtain ⟨rfl, rfl⟩ := h0 <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk, PL_cap, fuseOne] at h1 <;>
    obtain ⟨rfl, rfl⟩ := h1 <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk, PL_cap, fuseOne] at h2 <;>
    obtain ⟨rfl, rfl⟩ := h2 <;>
    simp only [List.mem_singleton] at hq0 hq1 hq2 <;> subst hq0 hq1 hq2 <;>
    rcases (show r1 = 1 ∨ 2 ≤ r1 by omega) with rfl | g1 <;>
    rcases (show r2 = 1 ∨ 2 ≤ r2 by omega) with rfl | g2 <;>
    simp (disch := omega) [PL_U, fuseOne, FMono.mul, PL_psi_zero, PL_psi_one, PL_psi_ge,
      PL_omega_ge] <;>
    omega

set_option linter.flexible false in
set_option maxHeartbeats 4000000 in -- `simp` evaluates the rule at every placement of the labels
/-- The rows for the profile `(1, 1, 0)` (Type I, `fR ≥ 3`). -/
private lemma PL_coreB (x0 y0 x1 y1 x2 y2 : ℕ) (hx0 : x0 < 2) (hy0 : y0 < 2) (hx1 : x1 < 2)
    (hy1 : y1 < 2) (hx2 : x2 < 2) (hy2 : y2 < 2) (hsum : x0 + y0 + x1 + y1 + x2 + y2 = 3)
    (r2 : ℕ) (hr2 : 1 ≤ r2) (i0 i1 i2 : ℤ)
    (hei : (i0 = 0 ∨ i0 = 2) ∧ (i1 = 0 ∨ i1 = 2) ∧ (i2 = 0 ∨ i2 = 2) ∧ i0 + i1 + i2 ≤ 2)
    (b0 b1 b2 : Bool) (k0 k1 k2 : FKind) (o0 o1 o2 : FOpt)
    (h0 : fruleFit [0, 0, 0, 0] (x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0) true = some (k0, o0))
    (h1 : fruleFit (PL_cap [((x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0)])
      (x1, y1, [0, 0], ⟨0, i1, 0, 0, 0⟩, b1) true = some (k1, o1))
    (h2 : fruleFit (PL_cap [((x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0),
      ((x1, y1, [0, 0], ⟨0, i1, 0, 0, 0⟩, b1), some o1)]) (x2, y2, [r2], ⟨0, i2, 0, 0, 0⟩, b2)
      true = some (k2, o2))
    (q0 q1 q2 : FMono) (hq0 : q0 ∈ o0.val) (hq1 : q1 ∈ o1.val) (hq2 : q2 ∈ o2.val)
    (fR u π T nL IL m : ℤ) (hu : 0 ≤ u) (hπ : 0 ≤ π ∧ π ≤ 1) (hnL : 0 ≤ nL) (hT : nL ≤ T)
    (hIL : IL = 2 * nL) (hsig : 0 ≤ m + u + fR - 4) (hm : m = r2 + T + nL - π)
    (hTy : 3 ≤ fR)
    (M : FMono)
    (hMa : M.a = 1 - ((PL_U [((x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0),
      ((x1, y1, [0, 0], ⟨0, i1, 0, 0, 0⟩, b1), some o1),
      ((x2, y2, [r2], ⟨0, i2, 0, 0, 0⟩, b2), some o2)] : ℕ) : ℤ) - 2 * u - 2 * fR -
      2 * (-1 + -1 + ((r2 : ℤ) - 1)) - 2 * T + 2 * π + q0.a + q1.a + q2.a)
    (hMi : M.i = q0.i + q1.i + q2.i + IL)
    (hMl : M.l = 2 * u + 2 * T + q0.l + q1.l + q2.l - 2 * π)
    (hMd : M.d = q0.d + q1.d + q2.d) (hMo : M.o = q0.o + q1.o + q2.o) :
    M.ok = true := by
  rw [FR_ok_iff, hMa, hMi, hMl, hMd, hMo]
  clear hMa hMi hMl hMd hMo
  interval_cases x0 <;> interval_cases y0 <;> interval_cases x1 <;> interval_cases y1 <;>
    interval_cases x2 <;> interval_cases y2 <;> (try omega) <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk] at h0 <;>
    obtain ⟨rfl, rfl⟩ := h0 <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk, PL_cap, fuseOne] at h1 <;>
    obtain ⟨rfl, rfl⟩ := h1 <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk, PL_cap, fuseOne] at h2 <;>
    obtain ⟨rfl, rfl⟩ := h2 <;>
    simp only [List.mem_singleton] at hq0 hq1 hq2 <;> subst hq0 hq1 hq2 <;>
    rcases (show r2 = 1 ∨ 2 ≤ r2 by omega) with rfl | g2 <;>
    simp (disch := omega) [PL_U, fuseOne, FMono.mul, fhalf, PL_psi_zero, PL_psi_one, PL_psi_ge,
      PL_omega_zero, PL_omega_ge] <;>
    omega

set_option linter.flexible false in
set_option maxHeartbeats 4000000 in -- `simp` evaluates the rule at every placement of the labels
/-- The rows for the profile `(1, 0, 0)` with `Λ̃₂` in a loop (Type II, or Type I with
`fR ≥ 3`). -/
private lemma PL_coreC (x0 y0 x1 y1 x2 y2 : ℕ) (hx0 : x0 < 2) (hy0 : y0 < 2) (hx1 : x1 < 2)
    (hy1 : y1 < 2) (hx2 : x2 < 2) (hy2 : y2 < 2) (hsum : x0 + y0 + x1 + y1 + x2 + y2 = 3)
    (r1 r2 : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2) (i0 i1 i2 : ℤ)
    (hei : (i0 = 0 ∨ i0 = 2) ∧ (i1 = 0 ∨ i1 = 2) ∧ (i2 = 0 ∨ i2 = 2) ∧ i0 + i1 + i2 ≤ 2)
    (b0 b1 b2 : Bool) (k0 k1 k2 : FKind) (o0 o1 o2 : FOpt)
    (h0 : fruleFit [0, 0, 0, 0] (x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0) true = some (k0, o0))
    (h1 : fruleFit (PL_cap [((x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0)])
      (x1, y1, [r1], ⟨0, i1, 0, 0, 0⟩, b1) true = some (k1, o1))
    (h2 : fruleFit (PL_cap [((x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0),
      ((x1, y1, [r1], ⟨0, i1, 0, 0, 0⟩, b1), some o1)]) (x2, y2, [r2], ⟨0, i2, 0, 0, 0⟩, b2)
      true = some (k2, o2))
    (q0 q1 q2 : FMono) (hq0 : q0 ∈ o0.val) (hq1 : q1 ∈ o1.val) (hq2 : q2 ∈ o2.val)
    (fR u π T nL IL G m : ℤ) (hu : 0 ≤ u) (hπ : 0 ≤ π ∧ π ≤ 1) (hnL : 1 ≤ nL) (hT : nL - 2 ≤ T)
    (hG : 0 ≤ G ∧ G ≤ 1) (hIL : IL = 2 * nL - 2 + 2 * G) (hsig : 0 ≤ m + u + fR - 4)
    (hm : m = r1 + r2 + T + nL - π)
    (hTy : 3 ≤ fR ∨ (2 ≤ fR ∧ 1 ≤ m + u + fR - 4 ∧ (fR = 2 →
      (m + u + fR - 4 = 1 → G = 1 ∧ (2 ≤ r1 ∨ 2 ≤ r2)) ∧
      (m + u + fR - 4 = 2 → G = 1 ∨ 2 ≤ r1 ∨ 2 ≤ r2))))
    (M : FMono)
    (hMa : M.a = 1 - ((PL_U [((x0, y0, [0, 0], ⟨0, i0, 0, 0, 0⟩, b0), some o0),
      ((x1, y1, [r1], ⟨0, i1, 0, 0, 0⟩, b1), some o1),
      ((x2, y2, [r2], ⟨0, i2, 0, 0, 0⟩, b2), some o2)] : ℕ) : ℤ) - 2 * u - 2 - 2 * fR -
      2 * (-1 + ((r1 : ℤ) - 1) + ((r2 : ℤ) - 1)) - 2 * T + 2 * π + q0.a + q1.a + q2.a)
    (hMi : M.i = q0.i + q1.i + q2.i + IL)
    (hMl : M.l = 2 * u + 2 * T + 2 + q0.l + q1.l + q2.l - 2 * π)
    (hMd : M.d = q0.d + q1.d + q2.d + 2) (hMo : M.o = q0.o + q1.o + q2.o) :
    M.ok = true := by
  rw [FR_ok_iff, hMa, hMi, hMl, hMd, hMo]
  clear hMa hMi hMl hMd hMo
  interval_cases x0 <;> interval_cases y0 <;> interval_cases x1 <;> interval_cases y1 <;>
    interval_cases x2 <;> interval_cases y2 <;> (try omega) <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk] at h0 <;>
    obtain ⟨rfl, rfl⟩ := h0 <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk, PL_cap, fuseOne] at h1 <;>
    obtain ⟨rfl, rfl⟩ := h1 <;>
    simp [fruleFit, FEnt.prefs, fkindFit, fkindOpt, frk, PL_cap, fuseOne] at h2 <;>
    obtain ⟨rfl, rfl⟩ := h2 <;>
    simp only [List.mem_singleton] at hq0 hq1 hq2 <;> subst hq0 hq1 hq2 <;>
    rcases (show r1 = 1 ∨ 2 ≤ r1 by omega) with rfl | g1 <;>
    rcases (show r2 = 1 ∨ 2 ≤ r2 by omega) with rfl | g2 <;>
    simp (disch := omega) [PL_U, fuseOne, FMono.mul, fhalf, PL_psi_zero, PL_psi_one, PL_psi_ge,
      PL_omega_zero, PL_omega_ge] <;>
    omega

/-! ### The bound of a leaf -/

set_option maxHeartbeats 1600000 in -- the three profiles of a leaf are treated in one proof
/-- Every monomial of the bound of `fruleLeaf` at a leaf of the further expansion, with the
prefactor `N^{-9/2 - S}` and the factor `η` of the pairing through a resolvent, passes the integer
test of the rows. -/
private lemma PL_bound (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) :
    ∀ mm ∈ fboundM R.rfacs (fruleLeaf R.rfacs),
      ((mm.mul ⟨-9 - 2 * R.S, 0, 0, 0, 0⟩).mul R.rext).ok = true := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨hE3, hlen1, hnl, hends⟩ := pkg_leaf_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have hlab := (pkg_leaf_local ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR).1
  have hsides := (pkg_leaf_sides ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf).1
  have hzero := (pkg_leaf_sides ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf).2
  have hextsum := (pkg_rfacs_ext R).2
  have hres := pkg_rfacs_res R
  have hn := PL_n R
  have hwt := PL_wt R
  obtain ⟨-, -, hs0, hs0', -, -⟩ := pkg_inv_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  have hempty := pkg_inv_empty ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  rw [PL_empty R hsides] at hempty
  have hpt0 := pkg_ptype_pos R hRw
  have hpt3 := PL_ptype_le R
  obtain ⟨hL2, hL3, -⟩ := pkg_lists' ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  -- the loops
  obtain ⟨dL, hdL, hdL2⟩ := PL_lam1_ent ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have hEnl : 1 ≤ ((R.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum :=
    le_trans (by omega : 1 ≤ dL.2.2.1.length - 1) (List.le_sum_of_mem (List.mem_map_of_mem hdL))
  have hLok : ∀ W ∈ fLoops R.rfacs, PL_LoopOK W := fun W hW => by
    obtain ⟨a, b⟩ := PL_loop_facts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf W hW
    refine ⟨a, b, ?_⟩
    have := List.le_sum_of_mem
      (List.mem_map_of_mem (f := fun w : List FLet => w.count FLet.lamt) hW)
    omega
  obtain ⟨ga, gl, gd, go, gT, gI1, gI2, gI3⟩ := PL_agg _ hLok
  have hL1 : ((fLoops R.rfacs).map fun W => (W.count FLet.lamt : ℤ)).sum =
      (((fLoops R.rfacs).map fun W => W.count FLet.lamt).sum : ℕ) := by
    push_cast [Nat.cast_list_sum, List.map_map]
    rfl
  -- the run
  obtain ⟨d0, d1, d2, k0, k1, k2, o0, o1, o2, hP, hr01, hr12, hf0, hf1, hf2, huses, hb⟩ :=
    PL_run R.rfacs hE3
  intro mm hmm
  obtain ⟨q0, hq0, q1, hq1, q2, hq2, rfl⟩ := hb mm hmm
  have hsZ : ∀ f : FEnt → ℤ, ((R.rfacs.filterMap FFac.entData).map f).sum = f d0 + f d1 + f d2 :=
    fun f => by
      rw [← (hP.map f).sum_eq]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
  have hsN : ∀ f : FEnt → ℕ, ((R.rfacs.filterMap FFac.entData).map f).sum = f d0 + f d1 + f d2 :=
    fun f => by
      rw [← (hP.map f).sum_eq]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
  have hm0 : d0 ∈ R.rfacs.filterMap FFac.entData := hP.subset (by simp)
  have hm1 : d1 ∈ R.rfacs.filterMap FFac.entData := hP.subset (by simp)
  have hm2 : d2 ∈ R.rfacs.filterMap FFac.entData := hP.subset (by simp)
  have hdL' : dL = d0 ∨ dL = d1 ∨ dL = d2 := by simpa using hP.symm.subset hdL
  have hone : 2 ≤ d0.2.2.1.length ∨ 2 ≤ d1.2.2.1.length ∨ 2 ≤ d2.2.2.1.length := by
    rcases hdL' with rfl | rfl | rfl <;> simp [hdL2]
  have hmem3 : ∀ d ∈ R.rfacs.filterMap FFac.entData, d = d0 ∨ d = d1 ∨ d = d2 := fun d hd => by
    simpa using hP.symm.subset hd
  obtain ⟨hx0, hy0⟩ := hlab d0 hm0
  obtain ⟨hx1, hy1⟩ := hlab d1 hm1
  obtain ⟨hx2, hy2⟩ := hlab d2 hm2
  obtain ⟨hl0, c0, he0⟩ := PL_ent_form _ d0 hm0
  obtain ⟨hl1, c1, he1⟩ := PL_ent_form _ d1 hm1
  obtain ⟨hl2, c2, he2⟩ := PL_ent_form _ d2 hm2
  have hsum : d0.1 + d0.2.1 + d1.1 + d1.2.1 + d2.1 + d2.2.1 = 3 := by
    have h := hends 1 (by norm_num)
    rw [List.count_flatMap, hsN] at h
    simp only [Function.comp_apply, PL_cnt1 _ _ hx0 hy0, PL_cnt1 _ _ hx1 hy1,
      PL_cnt1 _ _ hx2 hy2, show (1 : ℕ) < 2 by norm_num, ↓reduceIte] at h
    omega
  have hnl' := hnl
  rw [hsN] at hnl'
  have hci : 2 * (c0 : ℤ) + 2 * c1 + 2 * c2 ≤ 2 := by
    have := hextsum
    rw [hsZ, he0, he1, he2] at this
    simpa using this
  rw [PL_role d0 hx0 hy0, PL_role d1 hx1 hy1] at hr01
  rw [PL_role d1 hx1 hy1, PL_role d2 hx2 hy2] at hr12
  -- the factors of the monomial
  have hfR : R.fR = R.S - R.charsP.1 + R.charsP.2.1 + 1 := rfl
  have hfsig : R.fsig = R.charsP.1 + (R.weights.length : ℤ) + R.fR - 4 := rfl
  have hrext : R.rext = ⟨0, 0, -2 * (R.fpi : ℤ), 0, 0⟩ := by
    unfold PkgExpr.rext PkgExpr.fpi
    split_ifs <;> simp
  have hπ1 : R.fpi ≤ 1 := by
    unfold PkgExpr.fpi
    split_ifs <;> simp
  have hU := PL_fuse23 d0 (some o0) hx0 hy0
  have hU1 := PL_fuse23 d1 (some o1) hx1 hy1
  have hU2 := PL_fuse23 d2 (some o2) hx2 hy2
  have hlabA : ((List.range 4).map fun l => 2 - (fuses R.rfacs (fruleLeaf R.rfacs) l : ℤ)).sum =
      8 - (PL_U [(d0, some o0), (d1, some o1), (d2, some o2)] : ℤ) := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
    rw [huses 0 (by norm_num), huses 1 (by norm_num), huses 2 (by norm_num),
      huses 3 (by norm_num)]
    simp only [PL_U, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hU.1, hU.2,
      hU1.1, hU1.2, hU2.1, hU2.2]
    push_cast
    ring
  have hfix := PL_prodL (R.rfacs.map FFac.fixV)
  simp only [List.map_map, Function.comp_def] at hfix
  have hfa := PL_fix_sum FMono.a rfl R.rfacs
  have hfi := PL_fix_sum FMono.i rfl R.rfacs
  have hfl := PL_fix_sum FMono.l rfl R.rfacs
  have hfd := PL_fix_sum (fun m => (m.d : ℤ)) rfl R.rfacs
  have hfo := PL_fix_sum (fun m => (m.o : ℤ)) rfl R.rfacs
  rw [hwt] at hfa hfi hfl hfd hfo
  simp only at hfa hfi hfl hfd hfo
  push_cast at hfa hfi hfl hfd hfo
  have hres' := hres
  rw [hsZ] at hres'
  rw [hE3] at hn
  set Ls := fLoops R.rfacs with hLs
  set nL1 := (Ls.map fun W => (W.count FLet.lamt : ℤ)).sum with hnL1
  set T' := (Ls.map fun W => (fresN W : ℤ) - 1).sum with hT'
  set IL := (Ls.map fun W => (FFac.loop W).fixV.i).sum with hIL
  -- the components
  have hMa : ((((({ a := ((List.range 4).map fun l => 2 -
      (fuses R.rfacs (fruleLeaf R.rfacs) l : ℤ)).sum, i := 0, l := 0, d := 0, o := 0 } :
      FMono).mul (FMono.prodL (R.rfacs.map FFac.fixV))).mul ((q0.mul q1).mul q2)).mul
      ⟨-9 - 2 * R.S, 0, 0, 0, 0⟩).mul R.rext).a =
      1 - (PL_U [(d0, some o0), (d1, some o1), (d2, some o2)] : ℤ) -
        2 * (R.weights.length : ℤ) - 2 * nL1 - 2 * R.fR -
        2 * (((d0.2.2.1.sum : ℤ) - 1) + ((d1.2.2.1.sum : ℤ) - 1) + ((d2.2.2.1.sum : ℤ) - 1)) -
        2 * T' + 2 * (R.fpi : ℤ) + q0.a + q1.a + q2.a := by
    simp only [FMono.mul, hrext, hfix, hlabA]
    push_cast at hn
    linarith
  have hMi : ((((({ a := ((List.range 4).map fun l => 2 -
      (fuses R.rfacs (fruleLeaf R.rfacs) l : ℤ)).sum, i := 0, l := 0, d := 0, o := 0 } :
      FMono).mul (FMono.prodL (R.rfacs.map FFac.fixV))).mul ((q0.mul q1).mul q2)).mul
      ⟨-9 - 2 * R.S, 0, 0, 0, 0⟩).mul R.rext).i = q0.i + q1.i + q2.i + IL := by
    simp only [FMono.mul, hrext, hfix]
    linarith
  have hMl : ((((({ a := ((List.range 4).map fun l => 2 -
      (fuses R.rfacs (fruleLeaf R.rfacs) l : ℤ)).sum, i := 0, l := 0, d := 0, o := 0 } :
      FMono).mul (FMono.prodL (R.rfacs.map FFac.fixV))).mul ((q0.mul q1).mul q2)).mul
      ⟨-9 - 2 * R.S, 0, 0, 0, 0⟩).mul R.rext).l =
      2 * (R.weights.length : ℤ) + 2 * T' + 2 * nL1 + q0.l + q1.l + q2.l - 2 * (R.fpi : ℤ) := by
    simp only [FMono.mul, hrext, hfix]
    linarith
  have hMd : (((((({ a := ((List.range 4).map fun l => 2 -
      (fuses R.rfacs (fruleLeaf R.rfacs) l : ℤ)).sum, i := 0, l := 0, d := 0, o := 0 } :
      FMono).mul (FMono.prodL (R.rfacs.map FFac.fixV))).mul ((q0.mul q1).mul q2)).mul
      ⟨-9 - 2 * R.S, 0, 0, 0, 0⟩).mul R.rext).d : ℤ) = q0.d + q1.d + q2.d + 2 * nL1 := by
    simp only [FMono.mul, hrext, hfix]
    push_cast
    simp only [List.map_map, Function.comp_def]
    linarith
  have hMo : (((((({ a := ((List.range 4).map fun l => 2 -
      (fuses R.rfacs (fruleLeaf R.rfacs) l : ℤ)).sum, i := 0, l := 0, d := 0, o := 0 } :
      FMono).mul (FMono.prodL (R.rfacs.map FFac.fixV))).mul ((q0.mul q1).mul q2)).mul
      ⟨-9 - 2 * R.S, 0, 0, 0, 0⟩).mul R.rext).o : ℤ) = q0.o + q1.o + q2.o := by
    simp only [FMono.mul, hrext, hfix]
    push_cast
    simp only [List.map_map, Function.comp_def]
    linarith
  have hm : R.charsP.1 = (d0.2.2.1.sum : ℤ) + d1.2.2.1.sum + d2.2.2.1.sum + T' +
      (Ls.length : ℤ) - R.fpi := by
    push_cast at hn
    linarith
  have hsig : 0 ≤ R.charsP.1 + (R.weights.length : ℤ) + R.fR - 4 := by
    rw [← hfsig]
    omega
  have hnL1N : nL1 = (((Ls.map fun W => W.count FLet.lamt).sum : ℕ) : ℤ) := hL1
  have hprof : (d0.2.2.1.length = 3 ∧ d1.2.2.1.length = 1 ∧ d2.2.2.1.length = 1 ∧ nL1 = 0) ∨
      (d0.2.2.1.length = 2 ∧ d1.2.2.1.length = 2 ∧ d2.2.2.1.length = 1 ∧ nL1 = 0) ∨
      (d0.2.2.1.length = 2 ∧ d1.2.2.1.length = 1 ∧ d2.2.2.1.length = 1 ∧ nL1 = 1) := by
    have hr01' : 2 ≤ d1.2.2.1.length → 2 ≤ d0.2.2.1.length := fun h => by
      by_contra h'
      rw [ite_eq_right h', ite_eq_left h] at hr01
      omega
    have hr12' : 2 ≤ d2.2.2.1.length → 2 ≤ d1.2.2.1.length := fun h => by
      by_contra h'
      rw [ite_eq_right h', ite_eq_left h] at hr12
      omega
    omega
  -- no `Λ̃` in a loop when the entries carry both
  have hnoL : nL1 = 0 → R.ptype ≠ 2 := fun h0 h2 => by
    obtain ⟨W, hW, hlW⟩ := PL_ptype2 R h2
    rw [← hLs] at hW
    have h1 := List.le_sum_of_mem
      (List.mem_map_of_mem (f := fun w : List FLet => w.count FLet.lamt) hW)
    have h2 := List.count_pos_iff.2 hlW
    omega
  have hlenE : ∀ d ∈ R.rfacs.filterMap FFac.entData, d.2.2.1.length ≤ d0.2.2.1.length ∨
      d = d1 ∨ d = d2 := fun d hd => by
    rcases hmem3 d hd with rfl | rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hprof with ⟨hA0, hA1, hA2, hAn⟩ | ⟨hB0, hB1, hB2, hBn⟩ | ⟨hC0, hC1, hC2, hCn⟩
  · -- the profile `(2, 0, 0)`
    have hTy : 3 ≤ R.fR ∨ (2 ≤ R.fR ∧ (R.fR = 2 →
        R.charsP.1 + (R.weights.length : ℤ) + R.fR - 4 = 0 →
        2 * (c0 : ℤ) + 2 * c1 + 2 * c2 = 2 ∧ (R.fpi : ℤ) = 0)) := by
      have hp2 := hnoL hAn
      by_cases hp1 : R.ptype = 1
      · left
        simpa [hp1] using hempty
      · right
        have hp3 : R.ptype = 3 := by omega
        refine ⟨by simpa [hp1] using hempty, fun hfR2 hs => ?_⟩
        have hs' : R.fsig = 0 := by rw [hfsig]; exact hs
        have h1 := hL3 hf hp3 hfR2 hs'
        have hπ0 := PL_M6 R hfR2 hs' h1
        have hr1 := hlen1 d1 hm1 hA1
        have hr2 := hlen1 d2 hm2 hA2
        have hd0z : d0.2.2.1.sum = 0 := by
          have hz := hzero d0 hm0 (by omega)
          exact List.sum_eq_zero fun x hx => hz x hx
        rw [hπ0] at hm
        have hLs : Ls.length = 0 := by
          push_cast at hm
          omega
        have hm2 : R.charsP.1 = 2 := by
          push_cast at hm
          omega
        have hfpm := PL_typeIII_fpm R h1 (List.length_eq_zero_iff.1 hLs) hm2
        have hext2 := pkg_fpm_ext R 1 hfpm
        rw [hsZ, he0, he1, he2] at hext2
        simp only at hext2
        refine ⟨by omega, by rw [hπ0]; rfl⟩
    obtain ⟨x0, y0, P0, e0, b0⟩ := d0
    obtain ⟨x1, y1, P1, e1, b1⟩ := d1
    obtain ⟨x2, y2, P2, e2, b2⟩ := d2
    dsimp only at hA0 hA1 hA2 he0 he1 he2 hx0 hy0 hx1 hy1 hx2 hy2 hsum hm hMa
    subst he0 he1 he2
    have hr1 := hlen1 _ hm1 hA1
    have hr2 := hlen1 _ hm2 hA2
    have hz := hzero _ hm0 (by dsimp only; omega)
    dsimp only at hr1 hr2 hz
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 hA0
    obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 :=
      ⟨hz a (by simp), hz b (by simp), hz c (by simp)⟩
    obtain ⟨r1, rfl⟩ := List.length_eq_one_iff.1 hA1
    obtain ⟨r2, rfl⟩ := List.length_eq_one_iff.1 hA2
    simp only [List.sum_cons, List.sum_nil, add_zero] at hr1 hr2 hm hMa
    exact PL_coreA x0 y0 x1 y1 x2 y2 hx0 hy0 hx1 hy1 hx2 hy2 hsum r1 r2 hr1 hr2
      (2 * c0) (2 * c1) (2 * c2) (by omega) b0 b1 b2 k0 k1 k2 o0 o1 o2 hf0 hf1 hf2
      q0 q1 q2 hq0 hq1 hq2 R.fR (R.weights.length) R.fpi T' Ls.length IL R.charsP.1
      (by positivity) ⟨by positivity, by exact_mod_cast hπ1⟩ (by positivity) (by omega)
      (by omega) hsig (by push_cast at hm ⊢; omega) hTy _ (by rw [hMa]; push_cast; omega) hMi
      (by rw [hMl]; omega) (by omega) (by omega)
  · -- the profile `(1, 1, 0)`
    have hTy : 3 ≤ R.fR := by
      have hp2 := hnoL hBn
      have hp3 : R.ptype ≠ 3 := fun h3 => by
        obtain ⟨d, hd, hd3⟩ := PL_ptype3 R h3
        rcases hmem3 d hd with rfl | rfl | rfl <;> omega
      have hp1 : R.ptype = 1 := by omega
      simpa [hp1] using hempty
    obtain ⟨x0, y0, P0, e0, b0⟩ := d0
    obtain ⟨x1, y1, P1, e1, b1⟩ := d1
    obtain ⟨x2, y2, P2, e2, b2⟩ := d2
    dsimp only at hB0 hB1 hB2 he0 he1 he2 hx0 hy0 hx1 hy1 hx2 hy2 hsum hm hMa
    subst he0 he1 he2
    have hr2 := hlen1 _ hm2 hB2
    have hz0 := hzero _ hm0 (by dsimp only; omega)
    have hz1 := hzero _ hm1 (by dsimp only; omega)
    dsimp only at hr2 hz0 hz1
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hB0
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨hz0 a (by simp), hz0 b (by simp)⟩
    obtain ⟨a', b', rfl⟩ := List.length_eq_two.1 hB1
    obtain ⟨rfl, rfl⟩ : a' = 0 ∧ b' = 0 := ⟨hz1 a' (by simp), hz1 b' (by simp)⟩
    obtain ⟨r2, rfl⟩ := List.length_eq_one_iff.1 hB2
    simp only [List.sum_cons, List.sum_nil, add_zero] at hr2 hm hMa
    exact PL_coreB x0 y0 x1 y1 x2 y2 hx0 hy0 hx1 hy1 hx2 hy2 hsum r2 hr2
      (2 * c0) (2 * c1) (2 * c2) (by omega) b0 b1 b2 k0 k1 k2 o0 o1 o2 hf0 hf1 hf2
      q0 q1 q2 hq0 hq1 hq2 R.fR (R.weights.length) R.fpi T' Ls.length IL R.charsP.1
      (by positivity) ⟨by positivity, by exact_mod_cast hπ1⟩ (by positivity) (by omega)
      (by omega) hsig (by push_cast at hm ⊢; omega) hTy _ (by rw [hMa]; push_cast; omega) hMi
      (by rw [hMl]; omega) (by omega) (by omega)
  · -- the profile `(1, 0, 0)` with `Λ̃₂` in a loop
    have hLpos : 1 ≤ Ls.length := by
      refine List.length_pos_of_ne_nil fun h => ?_
      rw [h] at hnL1
      simp at hnL1
      omega
    obtain ⟨G, hG, hILG⟩ : ∃ G : ℤ, (0 ≤ G ∧ G ≤ 1) ∧ IL = 2 * (Ls.length : ℤ) - 2 + 2 * G :=
      ⟨(IL - 2 * Ls.length + 2) / 2, by omega, by omega⟩
    have hgain : R.gainLam2 = true → G = 1 := fun hg => by
      obtain ⟨W, hW, hlW, r, hrl, a, b, pa, pb, x, hab, hrot⟩ :=
        PL_gain ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf hg
      rw [← hLs] at hW
      obtain ⟨-, hr0, hc1⟩ := hLok W hW
      have hc : W.count FLet.lamt = 1 := by
        have := List.count_pos_iff.2 hlW
        omega
      have hi := PL_gain_val W hc (hr0 hlW) r hrl a b pa pb x hab hrot
      have := PL_agg_gain Ls hLok W hW hc hi
      omega
    have hft : R.freeTwo = true → 2 ≤ d1.2.2.1.sum ∨ 2 ≤ d2.2.2.1.sum := fun h => by
      obtain ⟨d, hd, hd1, hd2⟩ := pkg_freeTwo_ent R h
      rcases hmem3 d hd with rfl | rfl | rfl
      · omega
      · exact Or.inl hd2
      · exact Or.inr hd2
    have hTy : 3 ≤ R.fR ∨ (2 ≤ R.fR ∧ 1 ≤ R.charsP.1 + (R.weights.length : ℤ) + R.fR - 4 ∧
        (R.fR = 2 → (R.charsP.1 + (R.weights.length : ℤ) + R.fR - 4 = 1 →
          G = 1 ∧ (2 ≤ d1.2.2.1.sum ∨ 2 ≤ d2.2.2.1.sum)) ∧
          (R.charsP.1 + (R.weights.length : ℤ) + R.fR - 4 = 2 →
            G = 1 ∨ 2 ≤ d1.2.2.1.sum ∨ 2 ≤ d2.2.2.1.sum))) := by
      have hp3 : R.ptype ≠ 3 := fun h3 => by
        obtain ⟨d, hd, hd3⟩ := PL_ptype3 R h3
        rcases hmem3 d hd with rfl | rfl | rfl <;> omega
      by_cases hp1 : R.ptype = 1
      · left
        simpa [hp1] using hempty
      · right
        have hp2 : R.ptype = 2 := by omega
        have hII := pkg_inv_typeII ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR) hp2
        refine ⟨by simpa [hp1] using hempty, by rw [← hfsig]; exact hII,
          fun hfR2 => ⟨fun hs1 => ?_, fun hs2 => ?_⟩⟩
        · obtain ⟨hg, hft'⟩ := (hL2 hf hp2 hfR2).1 (by rw [hfsig]; exact hs1)
          exact ⟨hgain hg, hft hft'⟩
        · rcases (hL2 hf hp2 hfR2).2 (by rw [hfsig]; exact hs2) with hg | hft'
          · exact Or.inl (hgain hg)
          · exact Or.inr (hft hft')
    obtain ⟨x0, y0, P0, e0, b0⟩ := d0
    obtain ⟨x1, y1, P1, e1, b1⟩ := d1
    obtain ⟨x2, y2, P2, e2, b2⟩ := d2
    dsimp only at hC0 hC1 hC2 he0 he1 he2 hx0 hy0 hx1 hy1 hx2 hy2 hsum hm hMa hTy
    subst he0 he1 he2
    have hr1 := hlen1 _ hm1 hC1
    have hr2 := hlen1 _ hm2 hC2
    have hz0 := hzero _ hm0 (by dsimp only; omega)
    dsimp only at hr1 hr2 hz0
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hC0
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨hz0 a (by simp), hz0 b (by simp)⟩
    obtain ⟨r1, rfl⟩ := List.length_eq_one_iff.1 hC1
    obtain ⟨r2, rfl⟩ := List.length_eq_one_iff.1 hC2
    simp only [List.sum_cons, List.sum_nil, add_zero] at hr1 hr2 hm hMa hTy
    exact PL_coreC x0 y0 x1 y1 x2 y2 hx0 hy0 hx1 hy1 hx2 hy2 hsum r1 r2 hr1 hr2
      (2 * c0) (2 * c1) (2 * c2) (by omega) b0 b1 b2 k0 k1 k2 o0 o1 o2 hf0 hf1 hf2
      q0 q1 q2 hq0 hq1 hq2 R.fR (R.weights.length) R.fpi T' Ls.length IL G R.charsP.1
      (by positivity) ⟨by positivity, by exact_mod_cast hπ1⟩ (by exact_mod_cast hLpos)
      (by omega) hG hILG hsig (by push_cast at hm ⊢; omega) (by exact_mod_cast hTy) _
      (by rw [hMa]; push_cast; omega) hMi (by rw [hMl]; omega) (by omega) (by omega)

/-! ### The rule lemma -/

/-- The rule of the further terminal cases (i)–(iii) in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: for every expression of the further
expansion to which no rule applies, its labels are `0, 1`, and the assignment `fruleLeaf` is valid
and its bound, with the prefactor `(DN)^{-1} N^{-3/2} N^{-S}` and `N^{-2}` for the unused labels
`2, 3`, passes the rows. -/
theorem pkg_rule_leaf (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) :
    (∀ w ∈ R.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2) ∧
      FRuleOK R (-9 - 2 * R.S) (fruleLeaf R.rfacs) := by
  exact ⟨(pkg_inv_lab ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)).2.2,
    pkg_leaf_valid ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR,
    PL_bound ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf⟩

end RBMTransitionEdge

end
