module

public import RBMTransitionEdge.Localized.Expansion.RemStep
public import RBMTransitionEdge.Localized.Expansion.FRuleRun
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.PkgColl
public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.FFactor
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PairG
import all RBMTransitionEdge.Localized.Expansion.PkgColl
import all RBMTransitionEdge.Localized.Expansion.RemStep
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.FFactor
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PairG
import all RBMTransitionEdge.Localized.Expansion.FHalves

@[expose] public section

/-!
# The counts of the derivative structures

Under the binders of the remainder pins of the proof of Lemma 5.5 [claim_estimate_remainder_terms]
(an expression of the further expansion, `p + q ≥ 2` derivatives, a structure `R'` of
`𝓔^{(2)}_𝓡(p, q)`): the factors of `R'.rfacs` satisfy the local conditions, so the rule is valid;
the number of entries, the letters `Λ̃` and the resolvents, `fR`, the paired letters, the ends at
the four labels, the loops without `Λ̃` or without resolvent, `m + u`, and the pairing of the
exceptional subcase of case (8); the same for the leaves (the further terminal cases (i)–(iii));
and, for every expression, the segments of the package entries, the entry of `freeTwo`, the power
of `Im m` of the pairing through `𝔐`, and the entry of Type III with both letters `Λ̃`.
-/

namespace RBMTransitionEdge

open private dent_cases' from RBMTransitionEdge.Localized.Expansion.PkgColl
open private RS_pw RS_pents RS_ents RS_chain RS_pw_any RS_pw_free RS_pw_segs RS_pw_good RS_segOK
  RS_chain_last RS_chain_free RS_pw_comm RS_pw_rot RS_flat RS_flat_set RS_core RS_cut RS_free
  RS_swap RS_fpkg RS_sum_set
  from RBMTransitionEdge.Localized.Expansion.RemStep
open private FW_mk FW_g FW_rfacs FW_rent FW_mem_pents FW_seg_le FW_split_count FW_split_pre
  FW_parts FW_parts_dup FW_cntP FW_sum_cnt FW_iv_sum FW_iv FW_pd FW_pd_dup FW_lamSide_mem
  FW_wside FW_wside_split FW_run FW_go FW_count_le FW_wf_count FW_two_le FW_wf_ent FW_wf_free
  FW_pw FW_pw_free FW_pw_segs FW_pents FW_piece_cnt0 FW_cnt_dup FW_fres FW_fresN
  from RBMTransitionEdge.Localized.Expansion.FEntWords
open private wf_iff WfP WfP.mk segOK isGoodP sum_map_set charsP_eq nfac isEntP isResP projOK
  from RBMTransitionEdge.Localized.Expansion.PkgWords
open private FF_ffacs FF_wf from RBMTransitionEdge.Localized.Expansion.FFactor
open private PB_segs_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private PG_onlyRes_iff PG_flatMap_sum from RBMTransitionEdge.Localized.Expansion.PairG
open private FH_focus FH_shape from RBMTransitionEdge.Localized.Expansion.FHalves

/-! ### The entries of `rfacs` and the package entries -/

/-- The factor of a package entry is an entry with the labels of the package entry. -/
private theorem RC_rent_some (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) :
    ∃ d, (X.rent e).entData = some d ∧ d.1 = e.1 ∧ d.2.1 = e.2.1 := by
  unfold PkgExpr.rent
  split_ifs <;> simp [FFac.dupRes, FFac.entData]

/-- The entries of `rfacs` are the entries of the package entries. -/
private theorem RC_E (X : PkgExpr) :
    X.rfacs.filterMap FFac.entData = X.pents.filterMap fun e => (X.rent e).entData := by
  have h := congrArg (List.filterMap FFac.entData) (pkg_rfacs_pents X)
  rw [List.filterMap_filter, List.filterMap_map] at h
  rw [show (fun e => (X.rent e).entData) = FFac.entData ∘ X.rent from rfl, ← h]
  congr 1
  funext f
  cases hf : f.entData <;> simp

private theorem RC_E_mem (X : PkgExpr) (d : FEnt) (hd : d ∈ X.rfacs.filterMap FFac.entData) :
    ∃ e ∈ X.pents, (X.rent e).entData = some d := by
  rw [RC_E, List.mem_filterMap] at hd
  exact hd

private theorem RC_E_list (X : PkgExpr) : ∀ L : List (ℕ × ℕ × List PkgLetter),
    (L.filterMap fun e => (X.rent e).entData).length = L.length ∧
      ((L.filterMap fun e => (X.rent e).entData).flatMap fun d => [d.1, d.2.1]) =
        L.flatMap fun e => [e.1, e.2.1]
  | [] => by simp
  | e :: L => by
      obtain ⟨d, hd, h1, h2⟩ := RC_rent_some X e
      obtain ⟨ih1, ih2⟩ := RC_E_list X L
      simp only [List.filterMap_cons, hd, List.length_cons, ih1, List.flatMap_cons, ih2, h1, h2,
        true_and]

private theorem RC_E_len (X : PkgExpr) :
    (X.rfacs.filterMap FFac.entData).length = X.pents.length := by
  rw [RC_E]; exact (RC_E_list X _).1

private theorem RC_E_ends (X : PkgExpr) :
    ((X.rfacs.filterMap FFac.entData).flatMap fun d => [d.1, d.2.1]) =
      X.pents.flatMap fun e => [e.1, e.2.1] := by
  rw [RC_E]; exact (RC_E_list X _).2

/-! ### The ends of the package entries are the labels of the letters `Δ` -/

private theorem RC_chain_ends (u₀ : ℕ) : ∀ (Z acc : List PkgLetter) (v : ℕ),
    ((RS_chain u₀ v acc Z).flatMap fun e => [e.1, e.2.1]).Perm
      (v :: u₀ :: (RS_ents Z).flatMap fun x => [x.1, x.2])
  | [], acc, v => by simp [RS_chain, RS_ents]
  | .lw y :: Z, acc, v => by
      have e1 : RS_ents (.lw y :: Z) = RS_ents Z := by simp [RS_ents]
      rw [e1]
      simpa [RS_chain] using RC_chain_ends u₀ Z (acc ++ [.lw y]) v
  | .ent u v' :: Z, acc, v => by
      have e1 : RS_ents (.ent u v' :: Z) = (u, v') :: RS_ents Z := by simp [RS_ents]
      rw [e1]
      have ih := RC_chain_ends u₀ Z [] v'
      simp only [RS_chain, List.flatMap_cons, List.cons_append, List.nil_append]
      refine ((ih.cons u).cons v).trans ?_
      exact List.perm_iff_count.2 fun x => by simp only [List.count_cons]; omega

private theorem RC_ents_free (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = false) :
    RS_ents w = [] := by
  unfold RS_ents
  refine List.filterMap_eq_nil_iff.2 fun z hz => ?_
  rcases z with _ | ⟨u, v⟩
  · rfl
  · have := RS_free w hw _ hz
    simp [PkgLetter.isEnt] at this

private theorem RC_pw_ends (w : List PkgLetter) :
    ((RS_pw w).flatMap fun e => [e.1, e.2.1]).Perm ((RS_ents w).flatMap fun x => [x.1, x.2]) := by
  cases hw : w.any PkgLetter.isEnt
  · rw [RS_pw_free w hw, RC_ents_free w hw]
    exact List.Perm.refl _
  · obtain ⟨z, hz, hzE⟩ := List.any_eq_true.1 hw
    rcases z with _ | ⟨u, v⟩
    · simp [PkgLetter.isEnt] at hzE
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hz
    refine ((RS_pw_any A B u v).flatMap_right _).trans ((RC_chain_ends u (B ++ A) [] v).trans ?_)
    simp only [RS_ents, List.filterMap_append, List.filterMap_cons, List.flatMap_append,
      List.flatMap_cons]
    exact List.perm_iff_count.2 fun x => by
      simp only [List.count_cons, List.count_append, List.cons_append, List.nil_append]; omega

/-- The ends of the package entries are the labels of the letters `Δ`, up to order. -/
private theorem RC_ends (X : PkgExpr) :
    (X.pents.flatMap fun e => [e.1, e.2.1]).Perm (X.entLabels.flatMap fun x => [x.1, x.2]) := by
  rw [RS_pents, List.flatMap_assoc]
  have : X.entLabels = X.loops.flatMap RS_ents := rfl
  rw [this, List.flatMap_assoc]
  exact List.Perm.flatMap_left _ fun w _ => RC_pw_ends w

private theorem RC_len2 {α : Type*} (f g : α → ℕ) : ∀ L : List α,
    (L.flatMap fun e => [f e, g e]).length = 2 * L.length
  | [] => rfl
  | e :: L => by simp [RC_len2 f g L]; ring

private theorem RC_cnt01 : ∀ L : List (ℕ × ℕ), (∀ x ∈ L, x = (0, 1) ∨ x = (1, 0)) → ∀ l : ℕ,
    (L.flatMap fun x => [x.1, x.2]).count l = if l < 2 then L.length else 0
  | [], _, l => by simp
  | x :: L, h, l => by
      have ih := RC_cnt01 L (fun y hy => h y (List.mem_cons_of_mem _ hy)) l
      rw [List.flatMap_cons, List.count_append, ih]
      rcases h x List.mem_cons_self with rfl | rfl <;>
        simp only [List.count_cons, List.count_nil, List.length_cons, beq_iff_eq] <;>
        split_ifs <;> omega

/-- At an expression of the further expansion: three package entries, and the ends `0, 1` three
times each. -/
private theorem RC_ends_R (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    R.pents.length = 3 ∧ ∀ l : ℕ,
      (R.pents.flatMap fun e => [e.1, e.2.1]).count l = if l < 2 then 3 else 0 := by
  obtain ⟨h1, h2, -⟩ := pkg_inv_lab ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have hp := RC_ends R
  refine ⟨?_, fun l => ?_⟩
  · have := hp.length_eq
    rw [RC_len2, RC_len2, h1] at this
    omega
  · rw [hp.count_eq, RC_cnt01 _ h2 l, h1]

/-! ### One derivative on the package entries: their number, their ends, their letters -/

private theorem RC_step_P (X X' : PkgExpr) (u v : ℕ) (h : X' ∈ X.dent u v) :
    X'.pents.length = X.pents.length + 1 ∧
    (∀ l, (X'.pents.flatMap fun e => [e.1, e.2.1]).count l =
      (X.pents.flatMap fun e => [e.1, e.2.1]).count l + [u, v].count l) ∧
    (∀ z, (∃ e ∈ X.pents, z ∈ e.2.2) → ∃ e ∈ X'.pents, z ∈ e.2.2) := by
  obtain ⟨-, ⟨e, he, A, b, B, hσ, -, hp⟩ | ⟨A, b, B, -, -, -, hp⟩ | ⟨b, y, -, -, hp⟩⟩ :=
    pkg_dent_pents X u v X' h
  · have hc := List.perm_cons_erase he
    refine ⟨?_, fun l => ?_, fun z ⟨e₁, he₁, hz⟩ => ?_⟩
    · rw [hp.length_eq, List.length_append, List.length_erase_of_mem he]
      have := List.length_pos_of_mem he
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [(hp.flatMap_right _).count_eq, (hc.flatMap_right _).count_eq]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.count_append, List.count_cons, List.count_nil, List.cons_append, List.nil_append]
      split_ifs <;> omega
    · by_cases hee : e₁ = e
      · subst hee
        rw [hσ] at hz
        rcases List.mem_append.1 hz with hz | hz
        · exact ⟨(e₁.1, u, A ++ [.lw (.res b)]), hp.symm.subset (by simp), by simp [hz]⟩
        · exact ⟨(v, e₁.2.1, .lw (.res b) :: B), hp.symm.subset (by simp), hz⟩
      · exact ⟨e₁, hp.symm.subset (List.mem_append_left _ ((List.mem_erase_of_ne hee).2 he₁)),
          hz⟩
  all_goals
    refine ⟨by rw [hp.length_eq]; simp, fun l => ?_, fun z ⟨e₁, he₁, hz⟩ =>
      ⟨e₁, hp.symm.subset (List.mem_append_left _ he₁), hz⟩⟩
    rw [(hp.flatMap_right _).count_eq]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.count_append, List.count_cons, List.count_nil]
    split_ifs <;> omega

/-- The number, the ends and the letters of the package entries along the derivatives. -/
private def RC_JP (F : PkgExpr) (k : ℕ) (X : PkgExpr) : Prop :=
  X.pents.length = F.pents.length + k ∧
    (∀ l, (X.pents.flatMap fun e => [e.1, e.2.1]).count l =
      (F.pents.flatMap fun e => [e.1, e.2.1]).count l + if l = 2 ∨ l = 3 then k else 0) ∧
    (∀ z, (∃ e ∈ F.pents, z ∈ e.2.2) → ∃ e ∈ X.pents, z ∈ e.2.2)

private theorem RC_iter_P (F : PkgExpr) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ F.dwirt 2 3 p q) :
    RC_JP F (p + q) R' := by
  have step : ∀ u v : ℕ, (u = 2 ∧ v = 3 ∨ u = 3 ∧ v = 2) → ∀ k X, RC_JP F k X →
      ∀ X' ∈ X.dent u v, RC_JP F (k + 1) X' := by
    intro u v huv k X ⟨h1, h2, h3⟩ X' hX'
    obtain ⟨g1, g2, g3⟩ := RC_step_P X X' u v hX'
    refine ⟨by omega, fun l => ?_, fun z hz => g3 z (h3 z hz)⟩
    rw [g2 l, h2 l]
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [List.count_cons, List.count_nil, beq_iff_eq] <;> split_ifs <;> omega
  exact pkg_dwirt_iter (RC_JP F) 2 3 (step 2 3 (Or.inl ⟨rfl, rfl⟩))
    (step 3 2 (Or.inr ⟨rfl, rfl⟩)) F ⟨by simp, fun l => by simp, fun z hz => hz⟩ p q R' hR'

/-! ### One derivative on the words: the well-formedness, the counts, the loops without `Δ` -/

/-- The well-formedness, `fR`, `m + u`, the loops without `Δ` and the light weights along the
derivatives. -/
private def RC_JL (F : PkgExpr) (k : ℕ) (X : PkgExpr) : Prop :=
  X.wf = true ∧ X.fR = F.fR ∧
    X.charsP.1 + X.charsP.2.2.1 = F.charsP.1 + F.charsP.2.2.1 + (k : ℤ) ∧
    (∀ w ∈ X.loops, w.any PkgLetter.isEnt = false → w ∈ F.loops) ∧
    (∀ x ∈ X.weights, x ∈ F.weights)

private theorem RC_step_L (F : PkgExpr) (u v k : ℕ) (X : PkgExpr) (hX : RC_JL F k X)
    (X' : PkgExpr) (h : X' ∈ X.dent u v) : RC_JL F (k + 1) X' := by
  obtain ⟨hw, hfR, hmu, hfree, hwt⟩ := hX
  obtain ⟨hw', hc⟩ := pkg_dent_wf X X' u v hw h
  refine ⟨hw', ?_, ?_, ?_, ?_⟩
  · rw [← hfR]
    unfold PkgExpr.fR
    rcases hcs : X.charsP with ⟨m, n, u', S⟩
    rcases hc with hc | hc | hc <;> rw [hc, hcs] <;> dsimp only <;> ring
  · rcases hc with hc | hc | hc <;> rw [hc] <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> push_cast <;> linarith
  · rcases dent_cases' X X' u v h with ⟨ℓ, A, B, a, -, -, -, -, hl, -, -⟩ |
      ⟨j, b, y, -, -, -, -, -, -, hl⟩
    · intro w hw hE
      rw [hl] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | rfl
      · exact hfree w hw hE
      · simp [PkgLetter.isEnt] at hE
    · intro w hw hE
      rw [hl] at hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hfree w hw hE
      · rw [List.mem_singleton] at hw
        subst hw
        simp [PkgLetter.isEnt] at hE
  · rcases dent_cases' X X' u v h with ⟨ℓ, A, B, a, -, -, -, hwt', -, -, -⟩ |
      ⟨j, b, y, -, -, -, -, -, hwt', -⟩
    · rw [hwt']; exact hwt
    · rw [hwt']; exact fun x hx => hwt x (List.mem_of_mem_eraseIdx hx)

private theorem RC_iter_L (F : PkgExpr) (hF : F.wf = true) (p q : ℕ) (R' : PkgExpr)
    (hR' : R' ∈ F.dwirt 2 3 p q) : RC_JL F (p + q) R' :=
  pkg_dwirt_iter (RC_JL F) 2 3 (fun k X hX X' h => RC_step_L F 2 3 k X hX X' h)
    (fun k X hX X' h => RC_step_L F 3 2 k X hX X' h) F
    ⟨hF, rfl, by simp, fun w hw _ => hw, fun x hx => hx⟩ p q R' hR'

/-- A member of a list other than the value at `ℓ` is a member after `set ℓ`. -/
private theorem RC_mem_set (l : List (List PkgLetter)) (ℓ : ℕ) (w₀ N w : List PkgLetter)
    (h : l[ℓ]? = some w₀) (hw : w ∈ l) (hne : w ≠ w₀) : w ∈ l.set ℓ N := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hiℓ : ℓ ≠ i := by
    rintro rfl
    exact hne (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h))
  have hi' : i < (l.set ℓ N).length := by simpa using hi
  rw [← List.getElem_set_ne hiℓ hi']
  exact List.getElem_mem hi'

/-- A loop without resolvent survives every derivative. -/
private theorem RC_iter_res (F : PkgExpr) (w : List PkgLetter)
    (hres : w.any PkgLetter.isRes = false) (hw : w ∈ F.loops) (p q : ℕ) (R' : PkgExpr)
    (hR' : R' ∈ F.dwirt 2 3 p q) : w ∈ R'.loops := by
  have step : ∀ (u v : ℕ) (k : ℕ) (X : PkgExpr), w ∈ X.loops → ∀ X' ∈ X.dent u v,
      w ∈ X'.loops := by
    intro u v _ X hX X' h
    rcases dent_cases' X X' u v h with ⟨ℓ, A, B, a, hℓ, -, -, -, hl, -, -⟩ |
      ⟨j, b, y, -, -, -, -, -, -, hl⟩
    · rw [hl]
      refine RC_mem_set _ ℓ _ _ w hℓ hX ?_
      rintro rfl
      simp [PkgLetter.isRes] at hres
    · rw [hl]
      exact List.mem_append_left _ hX
  exact pkg_dwirt_iter (fun _ X => w ∈ X.loops) 2 3 (fun k X hX X' h => step 2 3 k X hX X' h)
    (fun k X hX X' h => step 3 2 k X hX X' h) F hw p q R' hR'

/-! ### The expanded word -/

private theorem RC_fpkg (R : PkgExpr) (hf : R.ffocus.isSome = true) :
    ∃ (ℓ r : ℕ) (right : Bool) (w : List PkgLetter) (a : Fin 2) (tl : List PkgLetter),
      R.ffocus = some (ℓ, r, right) ∧ R.loops[ℓ]? = some w ∧ w.rotate r = .lw (.res a) :: tl ∧
      R.fpkg.loops = R.loops.set ℓ ((if right then .lw (.res a) :: tl ++ [.lw (.det a)]
        else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2]) ∧
      R.fpkg.weights = R.weights ∧ R.fpkg.nb = R.nb ∧
      R.fpkg.S = if w.any PkgLetter.isEnt then R.S else R.S + 1 := by
  obtain ⟨⟨ℓ, r, right⟩, hf'⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨w, hw, i, o, hi, hs⟩ := FH_focus R ℓ r right hf'
  obtain ⟨a, tl, hrot, -, -⟩ := FH_shape w i r right o hi hs
  obtain ⟨hl, hwt, hnb⟩ := RS_fpkg R ℓ r right w a tl hf' hw hrot
  refine ⟨ℓ, r, right, w, a, tl, hf', hw, hrot, hl, hwt, hnb, ?_⟩
  unfold PkgExpr.fpkg
  simp only [hf', hw, hrot]
  rfl

/-- `fpkg` adds one to `fR` and keeps `m + u`. -/
private theorem RC_fpkg_chars (R : PkgExpr) (hf : R.ffocus.isSome = true) :
    R.fpkg.fR = R.fR + 1 ∧
      R.fpkg.charsP.1 + R.fpkg.charsP.2.2.1 = R.charsP.1 + R.charsP.2.2.1 := by
  obtain ⟨ℓ, r, right, w, a, tl, -, hw, hrot, hl, hwt, -, hS⟩ := RC_fpkg R hf
  obtain ⟨Wn, hWn⟩ : ∃ Wn : List PkgLetter, Wn = (if right then .lw (.res a) :: tl ++
      [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2] := ⟨_, rfl⟩
  rw [← hWn] at hl
  have hr1 : w.countP isResP = (PkgLetter.lw (.res a) :: tl).countP isResP := by
    rw [← hrot]; exact ((List.rotate_perm w r).countP_eq _).symm
  have hr2 : w.countP isEntP = (PkgLetter.lw (.res a) :: tl).countP isEntP := by
    rw [← hrot]; exact ((List.rotate_perm w r).countP_eq _).symm
  have hres : Wn.countP isResP = w.countP isResP := by
    rw [hr1, hWn]; cases right <;> simp [List.countP_append, List.countP_cons, isResP]
  have hent : Wn.countP isEntP = w.countP isEntP + 1 := by
    rw [hr2, hWn]; cases right <;> simp [List.countP_append, List.countP_cons, isEntP]
  have hnW : nfac Wn = w.countP isEntP + 1 := by
    unfold nfac
    rw [ite_eq_left (by rw [hWn]; cases right <;> simp [isEntP]), hent]
  have s1 := sum_map_set (fun w => w.countP isResP) R.loops ℓ w Wn hw
  have s2 := sum_map_set nfac R.loops ℓ w Wn hw
  rw [hres] at s1
  unfold PkgExpr.fR
  rw [charsP_eq, charsP_eq, hl, hwt, hS]
  have hEq : w.any PkgLetter.isEnt = w.any isEntP := rfl
  cases hE : w.any PkgLetter.isEnt
  · have h0 : w.countP isEntP = 0 :=
      List.countP_eq_zero.2 fun z hz => by
        have := RS_free w hE z hz
        rcases z with _ | ⟨u, v⟩ <;> simp_all [isEntP, PkgLetter.isEnt]
    have hnw : nfac w = 1 := by unfold nfac; rw [← hEq, hE]; rfl
    rw [hnW, h0, hnw] at s2
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor <;> omega
  · have hnw : nfac w = w.countP isEntP := by unfold nfac; rw [← hEq, hE]; rfl
    rw [hnW, hnw] at s2
    simp only [↓reduceIte]
    constructor <;> omega

/-- `fpkg` on the package entries: one more entry, the ends `2, 3` added, and the letters `𝔐_a`,
`𝒢_a` of the focus in its entries. -/
private theorem RC_fpkg_P (R : PkgExpr) (hf : R.ffocus.isSome = true) :
    ∃ a : Fin 2, R.fpkg.pents.length = R.pents.length + 1 ∧
      (∀ l, (R.fpkg.pents.flatMap fun e => [e.1, e.2.1]).count l =
        (R.pents.flatMap fun e => [e.1, e.2.1]).count l + [2, 3].count l) ∧
      (∃ e ∈ R.fpkg.pents, PkgLetter.lw (.det a) ∈ e.2.2) ∧
      (∃ e ∈ R.fpkg.pents, PkgLetter.lw (.res a) ∈ e.2.2) := by
  obtain ⟨ℓ, r, right, w, a, tl, hf', hw, hrot, -⟩ := RC_fpkg R hf
  obtain ⟨-, -, hE, hF⟩ := pkg_fpkg_pents R ℓ r right hf' w hw a tl hrot
  refine ⟨a, ?_⟩
  cases hwE : w.any PkgLetter.isEnt
  · have hp := hF hwE
    have hl : R.fpkg.pents.length = R.pents.length + 1 := by rw [hp.length_eq]; simp
    have hc : ∀ l, (R.fpkg.pents.flatMap fun e => [e.1, e.2.1]).count l =
        (R.pents.flatMap fun e => [e.1, e.2.1]).count l + [2, 3].count l := fun l => by
      rw [(hp.flatMap_right _).count_eq]
      simp [List.flatMap_append, List.count_append]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp
    · exact ⟨hl, hc, ⟨(2, 3, .lw (.det a) :: tl ++ [.lw (.res a)]), hp.symm.subset (by simp),
        by simp⟩, ⟨(2, 3, .lw (.det a) :: tl ++ [.lw (.res a)]), hp.symm.subset (by simp),
        by simp⟩⟩
    · exact ⟨hl, hc, ⟨(2, 3, .lw (.res a) :: tl ++ [.lw (.det a)]), hp.symm.subset (by simp),
        by simp⟩, ⟨(2, 3, .lw (.res a) :: tl ++ [.lw (.det a)]), hp.symm.subset (by simp),
        by simp⟩⟩
  · obtain ⟨e, he, A, B, -, hp⟩ := hE hwE
    have hc := List.perm_cons_erase he
    have hlen := List.length_pos_of_mem he
    have hcnt : ∀ x y : ℕ × ℕ × List PkgLetter, x.1 = e.1 → x.2.1 = 3 → y.1 = 2 →
        y.2.1 = e.2.1 → R.fpkg.pents.Perm (R.pents.erase e ++ [x, y]) →
        R.fpkg.pents.length = R.pents.length + 1 ∧
        ∀ l, (R.fpkg.pents.flatMap fun e => [e.1, e.2.1]).count l =
          (R.pents.flatMap fun e => [e.1, e.2.1]).count l + [2, 3].count l := by
      intro x y h1 h3 h2 h4 hp
      refine ⟨?_, fun l => ?_⟩
      · rw [hp.length_eq, List.length_append, List.length_erase_of_mem he]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [(hp.flatMap_right _).count_eq, (hc.flatMap_right _).count_eq]
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.count_append, List.count_cons, List.count_nil, List.cons_append, List.nil_append,
          h1, h3, h2, h4]
        split_ifs <;> omega
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp
    · obtain ⟨g1, g2⟩ := hcnt (e.1, 3, A ++ [.lw (.res a)]) (2, e.2.1, .lw (.det a) :: B)
        rfl rfl rfl rfl hp
      exact ⟨g1, g2, ⟨(2, e.2.1, .lw (.det a) :: B), hp.symm.subset (by simp), by simp⟩,
        ⟨(e.1, 3, A ++ [.lw (.res a)]), hp.symm.subset (by simp), by simp⟩⟩
    · obtain ⟨g1, g2⟩ := hcnt (e.1, 3, A ++ [.lw (.det a)]) (2, e.2.1, .lw (.res a) :: B)
        rfl rfl rfl rfl hp
      exact ⟨g1, g2, ⟨(e.1, 3, A ++ [.lw (.det a)]), hp.symm.subset (by simp), by simp⟩,
        ⟨(2, e.2.1, .lw (.res a) :: B), hp.symm.subset (by simp), by simp⟩⟩

/-- The loops without `Δ` of the expanded expression are loops of `R`. -/
private theorem RC_fpkg_free (R : PkgExpr) (hf : R.ffocus.isSome = true) (w : List PkgLetter)
    (hw : w ∈ R.fpkg.loops) (hE : w.any PkgLetter.isEnt = false) : w ∈ R.loops := by
  obtain ⟨ℓ, r, right, w₀, a, tl, -, -, -, hl, -⟩ := RC_fpkg R hf
  rw [hl] at hw
  rcases List.mem_or_eq_of_mem_set hw with hw | rfl
  · exact hw
  · cases right <;> simp [PkgLetter.isEnt] at hE

/-- A loop of `R` without resolvent is a loop of the expanded expression. -/
private theorem RC_fpkg_res (R : PkgExpr) (hf : R.ffocus.isSome = true) (w : List PkgLetter)
    (hw : w ∈ R.loops) (hres : w.any PkgLetter.isRes = false) : w ∈ R.fpkg.loops := by
  obtain ⟨ℓ, r, right, w₀, a, tl, -, hw₀, hrot, hl, -⟩ := RC_fpkg R hf
  rw [hl]
  refine RC_mem_set _ ℓ _ _ w hw₀ hw ?_
  rintro rfl
  have : PkgLetter.lw (.res a) ∈ w := List.mem_rotate.1 (by rw [hrot]; exact List.mem_cons_self)
  have := List.any_eq_false.1 hres _ this
  simp [PkgLetter.isRes] at this

/-! ### The letters of the package entries, and the factors of `rfacs` -/

/-- A letter of a package entry is a letter of a word. -/
private theorem RC_letter' (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents)
    (z : PkgLetter) (hz : z ∈ e.2.2) : ∃ w ∈ X.loops, w.any PkgLetter.isEnt = true ∧ z ∈ w := by
  obtain ⟨w, hw, hwE, hσ⟩ := FW_mem_pents X e he
  refine ⟨w, hw, hwE, ?_⟩
  have hzE : PkgLetter.isEnt z = false :=
    (PB_segs_count (fun _ => false) (fun _ _ => rfl) w).2.2.1 _ hσ z hz
  have h1 := FW_seg_le (fun x => x == z && !x.isEnt) (fun u v => by simp [PkgLetter.isEnt]) w
    e.2.2 hσ
  have h2 : 0 < e.2.2.countP (fun x => x == z && !x.isEnt) :=
    List.countP_pos_iff.2 ⟨z, hz, by simp [hzE]⟩
  obtain ⟨x, hx, hxz⟩ := List.countP_pos_iff.1
    (by omega : 0 < w.countP (fun x => x == z && !x.isEnt))
  simp only [Bool.and_eq_true, beq_iff_eq] at hxz
  rw [← hxz.1]
  exact hx

private theorem RC_letter (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents)
    (z : PkgLetter) (hz : z ∈ e.2.2) : ∃ w ∈ X.loops, z ∈ w := by
  obtain ⟨w, hw, -, h⟩ := RC_letter' X e he z hz
  exact ⟨w, hw, h⟩

/-- In a well-formed expression every package entry has a resolvent or a `Λ̃`. -/
private theorem RC_good (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) : e.2.2.any isGoodP = true := by
  obtain ⟨-, -, hseg, -, -⟩ := (wf_iff X).1 hX
  rw [RS_pents, List.mem_flatMap] at he
  obtain ⟨w, hw, he⟩ := he
  cases hwE : w.any PkgLetter.isEnt
  · rw [RS_pw_free w hwE] at he; simp at he
  · exact RS_pw_good w hwE (hseg w hw) e he

private theorem RC_parts_len (σ : List PkgLetter) :
    (pkgParts σ).length = σ.countP PkgLetter.isLam + 1 := by
  unfold pkgParts
  rw [List.length_map]
  exact (FW_split_count PkgLetter.isLam (fun _ => false) (fun _ _ => rfl) σ).2

private theorem RC_parts_one (σ : List PkgLetter) (h : ∀ x ∈ σ, PkgLetter.isLam x = false) :
    pkgParts σ = [σ.countP PkgLetter.isRes] := by
  unfold pkgParts
  rw [List.splitOnP_eq_singleton h]
  rfl

/-- The factors of `rfacs`: the light weights, the entries of the package entries, and the loops
of the words without `Δ`. -/
private theorem RC_mem_rfacs (X : PkgExpr) (f : FFac) (hf : f ∈ X.rfacs) :
    (∃ p ∈ X.weights, f = .wt p.1 p.2) ∨ (∃ e ∈ X.pents, f = X.rent e) ∨
      ∃ w ∈ X.loops, w.any PkgLetter.isEnt = false ∧
        f = FW_g X (.loop (w.filterMap (PkgLetter.flet (fun _ => false) X.fpm))) := by
  rw [FW_rfacs, List.mem_map] at hf
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  rw [FF_ffacs, List.mem_append] at hf₀
  rcases hf₀ with hf₀ | hf₀
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hf₀
    left
    refine ⟨p, hp, ?_⟩
    unfold FW_g
    split_ifs <;> rfl
  · obtain ⟨w, hw, hf₀⟩ := List.mem_flatMap.1 hf₀
    cases hwE : w.any PkgLetter.isEnt
    · rw [FW_wf_free _ w hwE, List.mem_singleton] at hf₀
      exact Or.inr (Or.inr ⟨w, hw, hwE, by rw [hf₀]⟩)
    · rw [FW_wf_ent _ w hwE, List.mem_map] at hf₀
      obtain ⟨e, he, rfl⟩ := hf₀
      refine Or.inr (Or.inl ⟨e, ?_, (FW_rent X e).symm⟩)
      rw [FW_pents, List.mem_flatMap]
      exact ⟨w, hw, he⟩

private theorem RC_dup_mem (a : Fin 2) (W : List FLet) (z : FLet)
    (hz : z ∈ W.flatMap (FLet.dupRes a)) (hr : ∀ b f, z ≠ .res b f) : z ∈ W := by
  obtain ⟨x, hx, hzx⟩ := List.mem_flatMap.1 hz
  rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y | _
  · simp only [FLet.dupRes] at hzx
    split_ifs at hzx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hzx <;>
      rcases hzx with rfl | rfl <;> exact absurd rfl (hr _ _)
  all_goals simp only [FLet.dupRes, List.mem_singleton] at hzx; subst hzx; exact hx

private theorem RC_dup_mem' (a : Fin 2) (W : List FLet) (z : FLet) (hz : z ∈ W)
    (hr : ∀ b f, z ≠ .res b f) : z ∈ W.flatMap (FLet.dupRes a) := by
  refine List.mem_flatMap.2 ⟨z, hz, ?_⟩
  rcases z with ⟨b, f⟩ | ⟨b, f⟩ | y | _
  · exact absurd rfl (hr b f)
  all_goals simp [FLet.dupRes]

/-- The pairing through `𝒢` keeps the kind of a factor and every letter other than a resolvent. -/
private theorem RC_g_ent (X : PkgExpr) (x y : ℕ) (W : List FLet) :
    ∃ W', FW_g X (.ent x y W) = .ent x y W' ∧ (∀ z ∈ W', (∀ b f, z ≠ .res b f) → z ∈ W) ∧
      ∀ z ∈ W, (∀ b f, z ≠ .res b f) → z ∈ W' := by
  unfold FW_g
  split_ifs
  · exact ⟨_, rfl, RC_dup_mem 0 W, RC_dup_mem' 0 W⟩
  · exact ⟨_, rfl, RC_dup_mem 1 W, RC_dup_mem' 1 W⟩
  · exact ⟨W, rfl, fun z hz _ => hz, fun z hz _ => hz⟩

private theorem RC_g_loop (X : PkgExpr) (W : List FLet) :
    ∃ W', FW_g X (.loop W) = .loop W' ∧ (∀ z ∈ W', (∀ b f, z ≠ .res b f) → z ∈ W) ∧
      (∀ z ∈ W, (∀ b f, z ≠ .res b f) → z ∈ W') ∧ W.countP FW_fres ≤ W'.countP FW_fres := by
  unfold FW_g
  split_ifs
  · exact ⟨_, rfl, RC_dup_mem 0 W, RC_dup_mem' 0 W, by rw [FW_cnt_dup]; omega⟩
  · exact ⟨_, rfl, RC_dup_mem 1 W, RC_dup_mem' 1 W, by rw [FW_cnt_dup]; omega⟩
  · exact ⟨W, rfl, fun z hz _ => hz, fun z hz _ => hz, le_rfl⟩

private theorem RC_flet (pr : Fin 2 → Bool) (σ : List PkgLetter) (z : FLet)
    (hz : z ∈ σ.filterMap (PkgLetter.flet (fun _ => false) pr)) :
    (∀ u, z = .proj u → PkgLetter.lw (.proj u) ∈ σ) ∧
      (∀ a b, z = .det a b → PkgLetter.lw (.det a) ∈ σ ∧ b = pr a) ∧
      (z = .lamt → ∃ o, PkgLetter.lw (.lamt o) ∈ σ) := by
  obtain ⟨x, hx, hxz⟩ := List.mem_filterMap.1 hz
  rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> simp only [PkgLetter.flet, Option.some.injEq,
    reduceCtorEq] at hxz <;> subst hxz
  · exact ⟨fun u h => (by cases h), fun a b' h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun u h => (by cases h), fun a' b' h => (by cases h; exact ⟨hx, rfl⟩),
      fun h => (by cases h)⟩
  · exact ⟨fun u h => (by cases h; exact hx), fun a b h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun u h => (by cases h), fun a b h => (by cases h), fun _ => ⟨o, hx⟩⟩

/-- The local conditions of `fvalid` hold on `rfacs` of a well-formed expression whose entry labels
are below `4`. -/
private theorem RC_local (X : PkgExpr) (hX : X.wf = true)
    (hl : ∀ e ∈ X.pents, e.1 < 4 ∧ e.2.1 < 4) : fLocal X.nb X.rfacs = true := by
  obtain ⟨-, -, -, hproj, hwt⟩ := (wf_iff X).1 hX
  unfold fLocal
  rw [List.all_eq_true]
  intro f hf
  rcases RC_mem_rfacs X f hf with ⟨p, hp, rfl⟩ | ⟨e, he, rfl⟩ | ⟨w, hw, hwE, rfl⟩
  · simp [hwt p hp]
  · rw [FW_rent]
    obtain ⟨W', hW', hsub, -⟩ := RC_g_ent X e.1 e.2.1 (e.2.2.filterMap
      (PkgLetter.flet (fun _ => false) X.fpm))
    unfold FW_mk
    rw [hW']
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨(hl e he).1, (hl e he).2⟩, fun z hz => ?_⟩
    rcases z with ⟨b, f⟩ | ⟨b, f⟩ | y | _
    · rfl
    · rfl
    · have h1 := (RC_flet X.fpm e.2.2 _ (hsub _ hz (by simp))).1 y rfl
      obtain ⟨w, hw, hyw⟩ := RC_letter X e he _ h1
      simp [hproj w hw y hyw]
    · rfl
  · obtain ⟨W', hW', hsub, -, -⟩ :=
      RC_g_loop X (w.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
    rw [hW']
    simp only [List.all_eq_true]
    intro z hz
    rcases z with ⟨b, f⟩ | ⟨b, f⟩ | y | _
    · rfl
    · obtain ⟨hb, rfl⟩ := (RC_flet X.fpm w _ (hsub _ hz (by simp))).2.1 b f rfl
      have : X.fpm b = false := by
        unfold PkgExpr.fpm
        have h2 : (X.loops.all fun w => w.any PkgLetter.isEnt || !w.contains (.lw (.det b))) =
            false := by
          rw [List.all_eq_false]
          exact ⟨w, hw, by simp [hwE, hb]⟩
        rw [h2]
        simp
      simp [this]
    · have h1 := (RC_flet X.fpm w _ (hsub _ hz (by simp))).1 y rfl
      simp [hproj w hw y h1]
    · rfl

/-- The ends of the package entries are below `B` when no count at or above `B` is positive. -/
private theorem RC_ends_lt (X : PkgExpr) (B : ℕ)
    (h : ∀ l, B ≤ l → (X.pents.flatMap fun e => [e.1, e.2.1]).count l = 0) :
    ∀ e ∈ X.pents, e.1 < B ∧ e.2.1 < B := by
  intro e he
  have m1 : e.1 ∈ X.pents.flatMap fun e => [e.1, e.2.1] :=
    List.mem_flatMap.2 ⟨e, he, by simp⟩
  have m2 : e.2.1 ∈ X.pents.flatMap fun e => [e.1, e.2.1] :=
    List.mem_flatMap.2 ⟨e, he, by simp⟩
  constructor
  · by_contra hc
    have := h e.1 (by omega)
    rw [List.count_eq_zero] at this
    exact this m1
  · by_contra hc
    have := h e.2.1 (by omega)
    rw [List.count_eq_zero] at this
    exact this m2

/-- An entry without `Λ̃` of a well-formed expression has a resolvent. -/
private theorem RC_lam_b (X : PkgExpr) (hX : X.wf = true) (d : FEnt)
    (hd : d ∈ X.rfacs.filterMap FFac.entData) (h1 : d.2.2.1.length = 1) : 1 ≤ d.2.2.1.sum := by
  obtain ⟨e, he, hde⟩ := RC_E_mem X d hd
  obtain ⟨-, -, hl, hp⟩ := pkg_rent_parts X e he d hde
  have hnl : e.2.2.countP PkgLetter.isLam = 0 := by rw [RC_parts_len] at hl; omega
  have hnl' : ∀ x ∈ e.2.2, PkgLetter.isLam x = false := fun x hx => by
    by_contra hc
    have := List.countP_pos_iff.2 ⟨x, hx, by simpa using hc⟩
    omega
  have hres : 1 ≤ e.2.2.countP PkgLetter.isRes := by
    obtain ⟨x, hx, hgx⟩ := List.any_eq_true.1 (RC_good X hX e he)
    have hxl := hnl' x hx
    refine List.countP_pos_iff.2 ⟨x, hx, ?_⟩
    rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> simp_all [isGoodP, PkgLetter.isRes,
      PkgLetter.isLam]
  have hpk : pkgParts e.2.2 = [e.2.2.countP PkgLetter.isRes] := by
    unfold pkgParts
    rw [List.splitOnP_eq_singleton hnl']
    rfl
  obtain ⟨g1, -, -⟩ := hp 0 (by rw [hpk]; simp)
  rw [hpk] at g1
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 h1
  rw [hy] at g1 ⊢
  simp only [List.getD_cons_zero, List.sum_cons, List.sum_nil, add_zero] at g1 ⊢
  omega

private def RC_isL (x : FLet) : Bool := x == .lamt

private theorem RC_lam_dup (a : Fin 2) : ∀ w : List FLet,
    (w.flatMap (FLet.dupRes a)).countP RC_isL = w.countP RC_isL
  | [] => by simp
  | x :: w => by
      have ih := RC_lam_dup a w
      rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y | _ <;>
        simp only [List.flatMap_cons, FLet.dupRes, List.countP_append, List.countP_cons, ih] <;>
        split_ifs <;> simp_all [RC_isL]; omega

private theorem RC_lam_sum : ∀ F : List FFac,
    ((F.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum +
        ((fLoops F).map fun w => w.count FLet.lamt).sum = (F.map (FW_cntP RC_isL)).sum
  | [] => by simp [fLoops]
  | f :: F => by
      have ih := RC_lam_sum F
      simp only [fLoops] at ih ⊢
      rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
        simp only [List.filterMap_cons, FFac.entData, List.map_cons, List.sum_cons, FW_cntP]
      · have := (FW_split_count (fun x => x == FLet.lamt) (fun _ => false) (fun _ _ => rfl) w).2
        have h2 : (FLet.parts w).length - 1 = w.countP RC_isL := by
          rw [FLet.parts, List.length_map, this, Nat.add_sub_cancel]; rfl
        rw [h2]; omega
      · have h2 : w.count FLet.lamt = w.countP RC_isL := by rw [List.count_eq_countP]; rfl
        rw [h2]; omega
      · simpa using ih

/-- The entries and the loops of `rfacs` of a well-formed expression carry the two letters `Λ̃`. -/
private theorem RC_lam_c (X : PkgExpr) (hX : X.wf = true) :
    ((X.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum +
        ((fLoops X.rfacs).map fun w => w.count FLet.lamt).sum = 2 := by
  rw [RC_lam_sum, FW_rfacs, List.map_map]
  have hg : (FW_cntP RC_isL ∘ FW_g X) = FW_cntP RC_isL := by
    funext f
    unfold FW_g
    split_ifs <;> rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
      simp [FFac.dupRes, FW_cntP, RC_lam_dup]
  rw [hg, FW_sum_cnt]
  have h : ∀ w : List PkgLetter, (w.countP fun x =>
      ((PkgLetter.flet (fun _ => false) X.fpm x).map RC_isL).getD false) =
      w.count (.lw (.lamt 0)) + w.count (.lw (.lamt 1)) := by
    intro w
    induction w with
    | nil => simp
    | cons x w ih =>
        rw [List.countP_cons, List.count_cons, List.count_cons, ih]
        rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases o
        all_goals (simp [PkgLetter.flet, RC_isL]; try omega)
  rw [List.map_congr_left fun w _ => h w]
  have e0 := FW_wf_count X hX 0
  have e1 := FW_wf_count X hX 1
  have hs : ∀ L : List (List PkgLetter), (L.map fun w => w.count (.lw (.lamt 0)) +
      w.count (.lw (.lamt 1))).sum = (L.map fun w => w.count (.lw (.lamt 0))).sum +
        (L.map fun w => w.count (.lw (.lamt 1))).sum := by
    intro L
    induction L with
    | nil => simp
    | cons w L ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [hs, e0, e1]

/-- A word read from `Λ̃₁` with `Λ̃₂` before the next `Δ` has a package entry holding both. -/
private theorem RC_seg_both (w : List PkgLetter) (hE : w.any PkgLetter.isEnt = true) (k : ℕ)
    (Y : List PkgLetter) (hrot : w.rotate k = .lw (.lamt 0) :: Y) (P : PkgLetter → Bool)
    (hP1 : ∀ u v, P (.ent u v) = false) (hP2 : ∀ x, P (.lw x) = true)
    (hm1 : PkgLetter.lw (.lamt 1) ∈ Y.takeWhile P) :
    ∃ e ∈ RS_pw w, PkgLetter.lw (.lamt 0) ∈ e.2.2 ∧ PkgLetter.lw (.lamt 1) ∈ e.2.2 := by
  have hYE : Y.any PkgLetter.isEnt = true := by
    have h4 := (List.rotate_perm w k).any_eq (f := PkgLetter.isEnt)
    rw [hrot, hE] at h4
    simpa [PkgLetter.isEnt] using h4
  obtain ⟨z, hz, hzE⟩ := List.any_eq_true.1 hYE
  have hne : Y.dropWhile P ≠ [] := by
    intro hD
    have := List.dropWhile_eq_nil_iff.1 hD z hz
    rcases z with _ | ⟨u, v⟩
    · simp [PkgLetter.isEnt] at hzE
    · rw [hP1] at this; exact absurd this (by decide)
  obtain ⟨d, D', hD⟩ := List.exists_cons_of_ne_nil hne
  have hd : P d = false := by
    have := List.head_dropWhile_not P hne
    simpa only [hD, List.head_cons] using this
  rcases d with x | ⟨u, v⟩
  · rw [hP2] at hd; exact absurd hd (by decide)
  have hY : Y = Y.takeWhile P ++ .ent u v :: D' := by
    rw [← hD, List.takeWhile_append_dropWhile]
  have hT : ∀ z ∈ PkgLetter.lw (.lamt 0) :: Y.takeWhile P, z.isEnt = false := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · rfl
    · have := List.mem_takeWhile_imp hz
      rcases z with _ | ⟨u', v'⟩
      · rfl
      · rw [hP1] at this; exact absurd this (by decide)
  obtain ⟨L, vl, σ, hch⟩ := RS_chain_last D' [] v
  have hp := RS_pw_any (.lw (.lamt 0) :: Y.takeWhile P) D' u v
  rw [hch u _ hT] at hp
  have hr := RS_pw_rot w hE k
  have e1 : (PkgLetter.lw (.lamt 0) :: Y.takeWhile P) ++ .ent u v :: D' = w.rotate k := by
    rw [hrot, List.cons_append, ← hY]
  rw [e1] at hp
  exact ⟨_, hr.subset (hp.symm.subset (List.mem_append_right _ (List.mem_singleton_self _))),
    List.mem_append_right _ List.mem_cons_self,
    List.mem_append_right _ (List.mem_cons_of_mem _ hm1)⟩

private theorem RC_pents_segs (X : PkgExpr) (w : List PkgLetter) (hw : w ∈ X.loops)
    (hE : w.any PkgLetter.isEnt = true) (σ : List PkgLetter) (hσ : σ ∈ pkgSegs w) :
    ∃ e ∈ X.pents, e.2.2 = σ := by
  rw [← FW_pw_segs w hE] at hσ
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hσ
  exact ⟨e, by rw [FW_pents, List.mem_flatMap]; exact ⟨w, hw, he⟩, rfl⟩

/-! ### The sides at a leaf -/

private theorem RC_seek_none (w : List PkgLetter) (o : Fin 2) (right : Bool)
    (h : pkgSeek w (w.idxOf (.lw (.lamt o))) right = none) : FW_wside w o right = 0 := by
  unfold pkgSeek at h
  unfold FW_wside
  exact List.countP_eq_zero.2 fun x hx hq => List.find?_eq_none.1 h x hx hq

private theorem RC_tw {α : Type*} (p : α → Bool) (y : α) (r : List α) (hy : p y = false) :
    ∀ T : List α, (∀ z ∈ T, p z = true) → (T ++ y :: r).takeWhile p = T
  | [], _ => by simp [hy]
  | z :: T, h => by
      rw [List.cons_append, List.takeWhile_cons, ite_eq_left (h z List.mem_cons_self),
        RC_tw p y r hy T (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))]

private theorem RC_parts_split (T rest : List PkgLetter) (y : PkgLetter)
    (hT : ∀ z ∈ T, PkgLetter.isLam z = false) (hy : PkgLetter.isLam y = true) :
    pkgParts (T ++ y :: rest) = T.countP PkgLetter.isRes :: pkgParts rest := by
  unfold pkgParts
  rw [FW_split_pre PkgLetter.isLam T (y :: rest) hT, List.splitOnP_cons_eq_ite_modifyHead,
    ite_eq_left hy]
  simp

private theorem RC_isLam_cnt : ∀ w : List PkgLetter,
    w.countP PkgLetter.isLam = w.count (.lw (.lamt 0)) + w.count (.lw (.lamt 1))
  | [] => rfl
  | x :: w => by
      rw [List.countP_cons, List.count_cons, List.count_cons, RC_isLam_cnt w]
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases o
      all_goals (simp [PkgLetter.isLam]; try omega)

/-- The first letter `Λ̃` of a list. -/
private theorem RC_first_lam (σ : List PkgLetter) (h : 1 ≤ σ.countP PkgLetter.isLam) :
    ∃ T o rest, σ = T ++ .lw (.lamt o) :: rest ∧ ∀ z ∈ T, PkgLetter.isLam z = false := by
  have hne : σ.dropWhile (fun x : PkgLetter => !x.isLam) ≠ [] := by
    intro hD
    have hall := List.dropWhile_eq_nil_iff.1 hD
    obtain ⟨x, hx, hxl⟩ := List.countP_pos_iff.1 (by omega : 0 < σ.countP PkgLetter.isLam)
    have := hall x hx
    simp [hxl] at this
  obtain ⟨y, rest, hD⟩ := List.exists_cons_of_ne_nil hne
  have hy : (!y.isLam) = false := by
    have := List.head_dropWhile_not (fun x : PkgLetter => !x.isLam) hne
    simpa only [hD, List.head_cons] using this
  rcases y with ((b | b | x | o) | ⟨u, v⟩) <;> simp [PkgLetter.isLam] at hy
  refine ⟨σ.takeWhile (fun x : PkgLetter => !x.isLam), o, rest, ?_, fun z hz => ?_⟩
  · rw [← hD, List.takeWhile_append_dropWhile]
  · have := List.mem_takeWhile_imp hz
    simpa using this

/-- A package entry of a well-formed expression holds each letter `Λ̃` at most once. -/
private theorem RC_seg_cnt (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) : e.2.2.count (.lw (.lamt o)) ≤ 1 := by
  obtain ⟨w, hw, -, hσ⟩ := FW_mem_pents X e he
  have := FW_seg_le (fun x => x == .lw (.lamt o)) (fun u v => rfl) w e.2.2 hσ
  rw [← List.count_eq_countP, ← List.count_eq_countP] at this
  exact this.trans (FW_count_le X hX o w hw)

/-- In a well-formed expression with empty sides, every part of a package entry with `Λ̃` is `0`. -/
private theorem RC_parts_zero (X : PkgExpr) (hX : X.wf = true)
    (hs : ∀ (o : Fin 2) (side : Bool), X.lamSide o side = 0)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (h1 : 1 ≤ e.2.2.countP PkgLetter.isLam) :
    ∀ t, (pkgParts e.2.2).getD t 0 = 0 := by
  have hcl := RC_seg_cnt X hX e he
  have hle : e.2.2.countP PkgLetter.isLam ≤ 2 := by
    rw [RC_isLam_cnt]; have := hcl 0; have := hcl 1; omega
  have side : ∀ (o : Fin 2) (T rest : List PkgLetter), e.2.2 = T ++ .lw (.lamt o) :: rest →
      (∀ z ∈ T, z ≠ .lw (.lamt o)) →
      (pkgParts e.2.2).getD (T.countP PkgLetter.isLam) 0 = 0 ∧
        (pkgParts e.2.2).getD (T.countP PkgLetter.isLam + 1) 0 = 0 := by
    intro o T rest hσ' hT
    have hk : (e.2.2.takeWhile fun x => x != .lw (.lamt o)) = T := by
      rw [hσ']
      exact RC_tw _ _ _ (by simp) T (fun z hz => by simpa using hT z hz)
    obtain ⟨g1, g2⟩ := pkg_pents_sides X hX e he o (by rw [hσ']; simp)
    rw [hk] at g1 g2
    exact ⟨g1.trans (hs o false), g2.trans (hs o true)⟩
  have hnl : ∀ T : List PkgLetter, (∀ z ∈ T, PkgLetter.isLam z = false) →
      T.countP PkgLetter.isLam = 0 := fun T hT =>
    List.countP_eq_zero.2 fun z hz h => by simp [hT z hz] at h
  have hne : ∀ (T : List PkgLetter) (o : Fin 2), (∀ z ∈ T, PkgLetter.isLam z = false) →
      ∀ z ∈ T, z ≠ .lw (.lamt o) := fun T o hT z hz hz' => by
    have := hT z hz; rw [hz'] at this; simp [PkgLetter.isLam] at this
  obtain ⟨T₁, o₁, r₁, hσ₁, hT₁⟩ := RC_first_lam e.2.2 h1
  obtain ⟨a0, a1⟩ := side o₁ T₁ r₁ hσ₁ (hne T₁ o₁ hT₁)
  rw [hnl T₁ hT₁] at a0 a1
  have hpk : pkgParts e.2.2 = T₁.countP PkgLetter.isRes :: pkgParts r₁ := by
    rw [hσ₁]; exact RC_parts_split _ _ _ hT₁ rfl
  have hc1 : e.2.2.countP PkgLetter.isLam = 1 + r₁.countP PkgLetter.isLam := by
    rw [hσ₁, List.countP_append, List.countP_cons, hnl T₁ hT₁]; simp [PkgLetter.isLam]; omega
  intro t
  rcases t with _ | _ | t
  · exact a0
  · exact a1
  · by_cases hr : 1 ≤ r₁.countP PkgLetter.isLam
    · obtain ⟨T₂, o₂, r₂, hr₂, hT₂⟩ := RC_first_lam r₁ hr
      have hc2 : r₁.countP PkgLetter.isLam = 1 + r₂.countP PkgLetter.isLam := by
        rw [hr₂, List.countP_append, List.countP_cons, hnl T₂ hT₂]; simp [PkgLetter.isLam]; omega
      have hr₂0 : ∀ x ∈ r₂, PkgLetter.isLam x = false := fun x hx => by
        by_contra hc
        have := List.countP_pos_iff.2 ⟨x, hx, by simpa using hc⟩
        omega
      have ho : o₂ ≠ o₁ := by
        rintro rfl
        have := hcl o₂
        rw [hσ₁, hr₂] at this
        simp only [List.count_append, List.count_cons_self] at this
        omega
      have hT12 : ∀ z ∈ T₁ ++ PkgLetter.lw (.lamt o₁) :: T₂, z ≠ .lw (.lamt o₂) := by
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hne T₁ o₂ hT₁ z hz
        · rcases List.mem_cons.1 hz with rfl | hz
          · intro h; simp at h; exact ho h.symm
          · exact hne T₂ o₂ hT₂ z hz
      obtain ⟨b1, b2⟩ := side o₂ (T₁ ++ .lw (.lamt o₁) :: T₂) r₂ (by rw [hσ₁, hr₂]; simp) hT12
      have hcT : (T₁ ++ PkgLetter.lw (.lamt o₁) :: T₂).countP PkgLetter.isLam = 1 := by
        rw [List.countP_append, List.countP_cons, hnl T₁ hT₁, hnl T₂ hT₂]; simp [PkgLetter.isLam]
      rw [hcT] at b2
      rcases t with _ | t
      · exact b2
      · rw [hpk, hr₂, RC_parts_split _ _ _ hT₂ rfl, RC_parts_one r₂ hr₂0]
        simp
    · have hr0 : ∀ x ∈ r₁, PkgLetter.isLam x = false := fun x hx => by
        by_contra hc
        have := List.countP_pos_iff.2 ⟨x, hx, by simpa using hc⟩
        omega
      rw [hpk, RC_parts_one r₁ hr0]
      simp

private theorem RC_find_some (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) :
    ∃ w, R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt o))]? = some w ∧
      w ∈ R.loops ∧ PkgLetter.lw (.lamt o) ∈ w := by
  rw [← List.find?_eq_getElem?_findIdx]
  cases h : R.loops.find? fun w => w.contains (.lw (.lamt o)) with
  | none =>
      exfalso
      have hall := List.find?_eq_none.1 h
      have : (R.loops.map fun w => w.count (.lw (.lamt o))).sum = 0 :=
        List.sum_eq_zero fun k hk => by
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
          exact List.count_eq_zero.2 fun hm => hall w hw (by simpa using hm)
      rw [FW_wf_count R hR o] at this
      exact absurd this one_ne_zero
  | some w => exact ⟨w, rfl, List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- At a leaf without focus, the four sides next to the letters `Λ̃` are empty. -/
private theorem RC_leaf_sides (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) :
    ∀ (o : Fin 2) (side : Bool), R.lamSide o side = 0 := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨w, hw, hwE, σ, hσ, hm, hall⟩ := pkg_inv_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨e, he, rfl⟩ := RC_pents_segs R w hw hwE σ hσ
  have l0 : R.lamSide 0 false = 0 := by
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hm
    have hc := RC_seg_cnt R hRw e he 0
    rw [hAB, List.count_append, List.count_cons_self] at hc
    have hA : ∀ z ∈ A, z ≠ .lw (.lamt 0) := fun z hz hz' => by
      rw [hz'] at hz
      have := List.count_pos_iff.2 hz
      omega
    have h1 : (e.2.2.takeWhile fun x => decide (x ≠ .lw (.lamt 0))) = A := by
      rw [hAB]; exact RC_tw _ _ _ (by simp) A (fun z hz => by simpa using hA z hz)
    have h2 : (e.2.2.takeWhile fun x => x != .lw (.lamt 0)) = A := by
      rw [hAB]; exact RC_tw _ _ _ (by simp) A (fun z hz => by simpa using hA z hz)
    rw [h1] at hall
    have hA' : ∀ z ∈ A, PkgLetter.isLam z = false ∧ z.isRes = false := fun z hz => by
      have := List.all_eq_true.1 hall z hz
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact ⟨this.2, this.1⟩
    obtain ⟨g1, -⟩ := pkg_pents_sides R hRw e he 0 hm
    rw [h2, hAB, RC_parts_split A B _ (fun z hz => (hA' z hz).1) rfl] at g1
    have hc0 : A.countP PkgLetter.isLam = 0 :=
      List.countP_eq_zero.2 fun z hz h => by simp [(hA' z hz).1] at h
    have hr0 : A.countP PkgLetter.isRes = 0 :=
      List.countP_eq_zero.2 fun z hz h => by simp [(hA' z hz).2] at h
    rw [hc0, hr0] at g1
    exact g1.symm
  obtain ⟨w₂, h₂, hw₂, hm₂⟩ := RC_find_some R hRw 1
  obtain ⟨w₁, h₁, hw₁, hm₁⟩ := RC_find_some R hRw 0
  have L1 := fun right => FW_lamSide_mem R 1 right (FW_wf_count R hRw 1).le w₂ hw₂ hm₂
  have L0 := fun right => FW_lamSide_mem R 0 right (FW_wf_count R hRw 0).le w₁ hw₁ hm₁
  unfold PkgExpr.ffocus at hf
  simp only [h₂, h₁] at hf
  by_cases hE : w₂.any PkgLetter.isEnt = true
  · rw [ite_eq_left (by exact hE)] at hf
    rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) true with _ | r₁ <;>
      rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂ <;>
      rcases s3 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₃ <;>
      simp only [s1, s2, s3, reduceCtorEq] at hf
    have k01 : R.lamSide 0 true = 0 := by rw [L0]; exact RC_seek_none _ _ _ s2
    have k10 : R.lamSide 1 false = 0 := by rw [L1]; exact RC_seek_none _ _ _ s3
    have k11 : R.lamSide 1 true = 0 := by rw [L1]; exact RC_seek_none _ _ _ s1
    intro o side
    fin_cases o <;> cases side
    exacts [l0, k01, k10, k11]
  · rw [ite_eq_right (by exact hE)] at hf
    rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₁ <;>
      rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂ <;>
      simp only [s1, s2, reduceCtorEq] at hf
    have hE' : w₂.any PkgLetter.isEnt = false := by simpa using hE
    have hn0 : PkgLetter.lw (.lamt 0) ∉ w₂ := by
      intro h0
      obtain ⟨w', hw', hwE', hm'⟩ := RC_letter' R e he _ hm
      have hne : w₂ ≠ w' := by rintro rfl; rw [hE'] at hwE'; exact absurd hwE' (by decide)
      have := FW_two_le (fun w => w.count (PkgLetter.lw (.lamt 0))) w₂ w' hne
        (List.count_pos_iff.2 h0) (List.count_pos_iff.2 hm') R.loops hw₂ hw'
      rw [FW_wf_count R hRw 0] at this
      omega
    have hsym : FW_wside w₂ 1 true = FW_wside w₂ 1 false := by
      obtain ⟨A, B, rfl⟩ := List.append_of_mem hm₂
      have hc := FW_count_le R hRw 1 _ hw₂
      rw [List.count_append, List.count_cons_self] at hc
      have hA : PkgLetter.lw (.lamt 1) ∉ A := List.count_eq_zero.1 (by omega)
      have hB : PkgLetter.lw (.lamt 1) ∉ B := List.count_eq_zero.1 (by omega)
      obtain ⟨t1, t2⟩ := FW_wside_split A B 1 hA
      rw [t1, t2]
      have hgo : ∀ z ∈ B ++ A, FW_go z = true := by
        intro z hz
        have hzw : z ∈ A ++ PkgLetter.lw (.lamt 1) :: B := by
          rcases List.mem_append.1 hz with hz | hz <;> simp [hz]
        have hzE := RS_free _ hE' z hzw
        have hz0 : z ≠ .lw (.lamt 0) := fun h => hn0 (h ▸ hzw)
        have hz1 : z ≠ .lw (.lamt 1) := by
          rintro rfl
          rcases List.mem_append.1 hz with hz | hz
          · exact hB hz
          · exact hA hz
        unfold FW_go
        rcases z with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases o
        all_goals simp_all [PkgLetter.isLam, PkgLetter.isEnt]
      unfold FW_run
      rw [List.takeWhile_eq_self_iff.2 hgo,
        List.takeWhile_eq_self_iff.2 (fun z hz => hgo z (List.mem_reverse.1 hz)),
        List.countP_reverse]
    have k01 : R.lamSide 0 true = 0 := by rw [L0]; exact RC_seek_none _ _ _ s2
    have k10 : R.lamSide 1 false = 0 := by rw [L1]; exact RC_seek_none _ _ _ s1
    have k11 : R.lamSide 1 true = 0 := by rw [L1, hsym]; exact RC_seek_none _ _ _ s1
    intro o side
    fin_cases o <;> cases side
    exacts [l0, k01, k10, k11]

/-! ### The pairings -/

private theorem RC_onlyDet_det (X : PkgExpr) (c : Fin 2)
    (h : ∀ w ∈ X.loops, PkgLetter.lw (.det c) ∉ w) : X.onlyDet c = false := by
  have : (X.loops.map fun w => w.count (.lw (.det c))).sum = 0 :=
    List.sum_eq_zero fun k hk => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
      exact List.count_eq_zero.2 (h w hw)
  unfold PkgExpr.onlyDet
  rw [this]
  simp

private theorem RC_onlyDet_res (X : PkgExpr) (c : Fin 2) (w : List PkgLetter) (hw : w ∈ X.loops)
    (hr : PkgLetter.lw (.res c) ∈ w) : X.onlyDet c = false := by
  have : (X.loops.all fun w => !(w.contains (.lw (.res c)))) = false :=
    List.all_eq_false.2 ⟨w, hw, by simp [hr]⟩
  unfold PkgExpr.onlyDet
  rw [this]
  simp

private theorem RC_onlyRes_det (X : PkgExpr) (c : Fin 2) (w : List PkgLetter) (hw : w ∈ X.loops)
    (hd : PkgLetter.lw (.det c) ∈ w) : X.onlyRes c = false := by
  cases h : X.onlyRes c
  · rfl
  · exact absurd hd (((PG_onlyRes_iff X c).1 h).1.2 w hw)

private theorem RC_fpm_of (X : PkgExpr) (c : Fin 2) (h : X.onlyDet c = false) :
    X.fpm c = false := by
  unfold PkgExpr.fpm
  rw [h]
  rfl

private theorem RC_fpg_of (X : PkgExpr) (c : Fin 2) (h : X.onlyRes c = false) :
    X.fpg c = false := by
  unfold PkgExpr.fpg
  rw [h]
  rfl

/-- Without a pairing through `𝔐`, no entry of `rfacs` has extra powers of `Im m`. -/
private theorem RC_iv_zero (X : PkgExpr) (h0 : X.fpm 0 = false) (h1 : X.fpm 1 = false) :
    ((X.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum = 0 := by
  rw [FW_iv_sum]
  refine List.sum_eq_zero fun k hk => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hk
  rcases RC_mem_rfacs X f hf with ⟨p, -, rfl⟩ | ⟨e, -, rfl⟩ | ⟨w, -, -, rfl⟩
  · rfl
  · rw [FW_rent]
    unfold FW_mk
    obtain ⟨W', hW', hsub, -⟩ := RC_g_ent X e.1 e.2.1
      (e.2.2.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
    rw [hW']
    simp only [FW_iv]
    have : W'.countP FW_pd = 0 := List.countP_eq_zero.2 fun z hz hpd => by
      rcases z with ⟨b, f⟩ | ⟨b, f⟩ | y | _ <;> simp only [FW_pd, reduceCtorEq] at hpd
      obtain ⟨-, hb⟩ := (RC_flet X.fpm e.2.2 _ (hsub _ hz (fun _ _ h => by cases h))).2.1 b f rfl
      subst hpd
      fin_cases b <;> simp_all
    rw [this]
    rfl
  · obtain ⟨W', hW', -⟩ := RC_g_loop X (w.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
    rw [hW']
    rfl

/-! ### The exceptional subcase of case (8): the pairing through `𝒢₁` -/

/-- One derivative on the words and on the package entries at once, with the slot of the resolvent
that is hit. -/
private theorem RC_dent (X : PkgExpr) (u v : ℕ) (X' : PkgExpr) (hX' : X' ∈ X.dent u v) :
    (∃ (ℓ : ℕ) (A₀ : List PkgLetter) (b : Fin 2) (B₀ : List PkgLetter),
        X.loops[ℓ]? = some (A₀ ++ .lw (.res b) :: B₀) ∧ X'.weights = X.weights ∧
        X'.loops = X.loops.set ℓ (A₀ ++ [.lw (.res b), .ent u v, .lw (.res b)] ++ B₀) ∧
        ((∃ e ∈ X.pents, ∃ (A B : List PkgLetter), e.2.2 = A ++ .lw (.res b) :: B ∧
          X'.pents.Perm (X.pents.erase e ++
            [(e.1, u, A ++ [.lw (.res b)]), (v, e.2.1, .lw (.res b) :: B)])) ∨
         ((A₀ ++ .lw (.res b) :: B₀).any PkgLetter.isEnt = false ∧
          X'.pents.Perm (X.pents ++ [(v, u, .lw (.res b) :: B₀ ++ A₀ ++ [.lw (.res b)])])))) ∨
      ∃ (j : ℕ) (b : Fin 2) (y : ℕ), X.weights[j]? = some (b, y) ∧
        X'.weights = X.weights.eraseIdx j ∧
        X'.loops = X.loops ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]] ∧
        X'.pents.Perm (X.pents ++ [(v, u, [.lw (.res b), .lw (.proj y), .lw (.res b)])]) := by
  rcases dent_cases' X X' u v hX' with
    ⟨ℓ, A₀, B₀, a, hℓ, -, -, hwt, hl, -, -⟩ | ⟨j, b, y, hj, -, -, -, -, hwt, hl⟩
  · left
    refine ⟨ℓ, A₀, a, B₀, hℓ, hwt, hl, ?_⟩
    have hp := RS_flat X.loops RS_pw ℓ _ hℓ
    rw [← RS_pents] at hp
    have hp' : X'.pents.Perm
        (RS_pw (A₀ ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ B₀) ++
          (X.loops.eraseIdx ℓ).flatMap RS_pw) := by
      rw [RS_pents, hl]
      exact RS_flat_set _ _ ℓ _ _ hℓ
    cases hE : (A₀ ++ .lw (.res a) :: B₀).any PkgLetter.isEnt
    · right
      refine ⟨rfl, ?_⟩
      rw [RS_pw_free _ hE, List.nil_append] at hp
      have e : A₀ ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ B₀ =
          (A₀ ++ [.lw (.res a)]) ++ .ent u v :: (.lw (.res a) :: B₀) := by simp
      have hfree : ∀ z ∈ (PkgLetter.lw (.res a) :: B₀) ++ (A₀ ++ [.lw (.res a)]),
          z.isEnt = false := by
        intro z hz
        refine RS_free _ hE z ?_
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        tauto
      rw [e] at hp'
      have h1 := RS_pw_any (A₀ ++ [.lw (.res a)]) (.lw (.res a) :: B₀) u v
      rw [RS_chain_free u _ [] v hfree, List.nil_append] at h1
      have e3 : (PkgLetter.lw (.res a) :: B₀) ++ (A₀ ++ [.lw (.res a)]) =
          .lw (.res a) :: B₀ ++ A₀ ++ [.lw (.res a)] := by simp
      rw [e3] at h1
      exact hp'.trans ((h1.append_right _).trans
        (List.perm_append_comm.trans (hp.symm.append_right _)))
    · left
      have hc1 := RS_pw_comm A₀ (.lw (.res a) :: B₀) hE
      have hc2 := RS_pw_comm (A₀ ++ [.lw (.res a), .ent u v]) (.lw (.res a) :: B₀)
        (by simp [PkgLetter.isEnt])
      have e1 : A₀ ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ B₀ =
          (A₀ ++ [.lw (.res a), .ent u v]) ++ (.lw (.res a) :: B₀) := by simp
      have e2 : (PkgLetter.lw (.res a) :: B₀) ++ (A₀ ++ [.lw (.res a), .ent u v]) =
          (.lw (.res a) :: (B₀ ++ A₀)) ++ [.lw (.res a), .ent u v] := by simp
      have e3 : (PkgLetter.lw (.res a) :: B₀) ++ A₀ = .lw (.res a) :: (B₀ ++ A₀) := by simp
      rw [e3] at hc1
      rw [← e1, e2] at hc2
      have htl : (B₀ ++ A₀).any PkgLetter.isEnt = true := by
        have : (B₀ ++ A₀).any PkgLetter.isEnt =
            (A₀ ++ .lw (.res a) :: B₀).any PkgLetter.isEnt := by
          simp only [List.any_append, List.any_cons, PkgLetter.isEnt, Bool.false_or]
          exact Bool.or_comm _ _
        rw [this, hE]
      obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut (B₀ ++ A₀) [] htl
      rw [List.append_nil] at hcut
      obtain ⟨L, vl, σ, h1, h2⟩ := RS_core a (.lw (.res a)) (.lw (.res a)) rfl rfl u v p q B Z []
        hB (by simp)
      simp only [List.append_nil] at h1 h2 hcut
      rw [← hcut] at h1 h2
      obtain ⟨hmem, hperm⟩ := RS_swap X.pents X'.pents L _ _ (vl, p, σ ++ .lw (.res a) :: B)
        (hp.trans ((hc1.trans h1).append_right _)) (hp'.trans ((hc2.trans h2).append_right _))
      exact ⟨_, hmem, σ, B, rfl, hperm⟩
  · right
    refine ⟨j, b, y, hj, hwt, hl, ?_⟩
    rw [RS_pents, hl, List.flatMap_append, ← RS_pents, List.flatMap_singleton]
    refine List.Perm.append_left _ ?_
    have e : [PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] =
        [.lw (.res b)] ++ .ent u v :: [.lw (.res b), .lw (.proj y)] := rfl
    rw [e]
    exact (RS_pw_any _ _ u v).trans (List.Perm.refl _)

/-- The counts of a letter other than `Δ` in the package entries are at most those in the
words. -/
private theorem RC_psum (X : PkgExpr) (z : PkgLetter) (hz : z.isEnt = false) :
    (X.pents.map fun e => e.2.2.count z).sum ≤ (X.loops.map fun w => w.count z).sum := by
  have hw : ∀ w : List PkgLetter, ((RS_pw w).map fun e => e.2.2.count z).sum ≤ w.count z := by
    intro w
    cases hwE : w.any PkgLetter.isEnt
    · rw [RS_pw_free w hwE]; simp
    · have h1 := congrArg (fun L => (L.map (List.countP fun x => x == z)).sum) (RS_pw_segs w hwE)
      simp only [List.map_map] at h1
      have h2 : ((pkgSegs w).map (List.countP fun x => x == z)).sum =
          w.countP (fun x => x == z) :=
        (PB_segs_count (fun x => x == z) (fun x hx => by
          rcases x with _ | ⟨u, v⟩
          · simp [isEntP] at hx
          · rcases z with _ | ⟨u', v'⟩
            · rfl
            · simp [PkgLetter.isEnt] at hz) w).1
      have h3 : ((RS_pw w).map fun e => e.2.2.count z) =
          (RS_pw w).map ((List.countP fun x => x == z) ∘ fun e => e.2.2) := by
        refine List.map_congr_left fun e _ => ?_
        simp [List.count_eq_countP]
      rw [h3, h1, h2, List.count_eq_countP]
  rw [RS_pents, PG_flatMap_sum]
  induction X.loops with
  | nil => simp
  | cons w L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hw w) ih

/-- The entry `𝔐₀ Λ̃₁ 𝒢₁ Λ̃₂ 𝔐₀` of both letters `Λ̃` in the expanded word of the exceptional
subcase of case (8). -/
private def RC_s0 : List PkgLetter :=
  [.lw (.det 0), .lw (.lamt 0), .lw (.res 1), .lw (.lamt 1), .lw (.det 0)]

/-- The invariant of the exceptional subcase of case (8) along the derivatives: an entry with two
letters `Λ̃` is `RC_s0` with slot `1` only through one resolvent, and no loop without `Δ` has a
`Λ̃`. -/
private def RC_J (X : PkgExpr) : Prop :=
  (∀ e ∈ X.pents, 2 ≤ e.2.2.countP PkgLetter.isLam → e.2.2 = RC_s0 ∧ X.onlyRes 1 = true) ∧
    ∀ w ∈ X.loops, w.any PkgLetter.isEnt = false → w.any PkgLetter.isLam = false

private theorem RC_fin2 (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

private theorem RC_s0_split (A B : List PkgLetter) (b : Fin 2)
    (h : RC_s0 = A ++ PkgLetter.lw (.res b) :: B) :
    (A ++ [PkgLetter.lw (.res b)]).countP PkgLetter.isLam ≤ 1 ∧
      (PkgLetter.lw (.res b) :: B).countP PkgLetter.isLam ≤ 1 := by
  unfold RC_s0 at h
  rcases A with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, A⟩⟩⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, List.cons.injEq, PkgLetter.lw.injEq,
      reduceCtorEq, LoopLetter.res.injEq, false_and, and_false] at h
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    constructor <;> decide
  · obtain ⟨-, -, -, -, -, h⟩ := h
    simp at h

/-- `onlyRes 1` survives a derivative at a resolvent of slot `0`. -/
private theorem RC_only1_set (X X' : PkgExpr) (h1 : X.onlyRes 1 = true) (ℓ : ℕ)
    (W W' : List PkgLetter) (hℓ : X.loops[ℓ]? = some W) (hl : X'.loops = X.loops.set ℓ W')
    (hwt : ∀ p ∈ X'.weights, p ∈ X.weights)
    (hr : W'.count (.lw (.res 1)) = W.count (.lw (.res 1)))
    (hd : ∀ z ∈ W', z = .lw (.det 1) → z ∈ W) : X'.onlyRes 1 = true := by
  obtain ⟨⟨hw1, hd1⟩, hc1⟩ := (PG_onlyRes_iff X 1).1 h1
  refine (PG_onlyRes_iff X' 1).2 ⟨⟨fun p hp => hw1 p (hwt p hp), fun w hw hm => ?_⟩, ?_⟩
  · rw [hl] at hw
    rcases List.mem_or_eq_of_mem_set hw with hw | rfl
    · exact hd1 w hw hm
    · exact hd1 W (List.mem_of_getElem? hℓ) (hd _ hm rfl)
  · have := sum_map_set (fun w => w.count (PkgLetter.lw (.res 1))) X.loops ℓ W W' hℓ
    rw [hl]
    omega

private theorem RC_J_step (X : PkgExpr) (hJ : RC_J X) (u v : ℕ) (X' : PkgExpr)
    (h : X' ∈ X.dent u v) : RC_J X' := by
  obtain ⟨hJ1, hJ2⟩ := hJ
  -- `b ≠ 1` when `X` has the entry `RC_s0` and a resolvent `𝒢_b` of another entry is hit
  have hcnt : ∀ e ∈ X.pents, ∀ e' ∈ X.pents.erase e, e'.2.2 = RC_s0 → X.onlyRes 1 = true →
      PkgLetter.lw (.res 1) ∉ e.2.2 := by
    intro e he e' he' hs0 h1 hm
    have hc := (List.perm_cons_erase he).map (fun e => e.2.2.count (PkgLetter.lw (.res 1)))
    have hs := hc.sum_eq
    simp only [List.map_cons, List.sum_cons] at hs
    have g1 := List.count_pos_iff.2 hm
    have g2 : 1 ≤ e'.2.2.count (PkgLetter.lw (.res 1)) := by rw [hs0]; decide
    have g3 := List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun e : ℕ × ℕ × List PkgLetter => e.2.2.count (PkgLetter.lw (.res 1))) he')
    have g4 := RC_psum X (.lw (.res 1)) rfl
    rw [((PG_onlyRes_iff X 1).1 h1).2] at g4
    omega
  rcases RC_dent X u v X' h with ⟨ℓ, A₀, b, B₀, hℓ, hwt, hl, hP⟩ | ⟨j, b, y, hj, hwt, hl, hp⟩
  · have hW := List.mem_of_getElem? hℓ
    have h3 : ∀ w ∈ X'.loops, w.any PkgLetter.isEnt = false → w.any PkgLetter.isLam = false := by
      intro w hw hE
      rw [hl] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | rfl
      · exact hJ2 w hw hE
      · simp [PkgLetter.isEnt] at hE
    have hkeep : b = 0 → X.onlyRes 1 = true → X'.onlyRes 1 = true := by
      rintro rfl h1
      refine RC_only1_set X X' h1 ℓ _ _ hℓ hl (by rw [hwt]; exact fun p hp => hp) ?_ ?_
      · simp [List.count_append]
      · intro z hz hz1
        subst hz1
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with (hz | hz | hz | hz) | hz
        · exact Or.inl hz
        · simp at hz
        · simp at hz
        · simp at hz
        · exact Or.inr (Or.inr hz)
    refine ⟨fun e' he' h2 => ?_, h3⟩
    rcases hP with ⟨e, he, A, B, hσ, hp⟩ | ⟨hE, hp⟩
    · rcases List.mem_append.1 (hp.subset he') with he'' | he''
      · obtain ⟨hs0, h1⟩ := hJ1 e' (List.mem_of_mem_erase he'') h2
        refine ⟨hs0, hkeep ?_ h1⟩
        have := hcnt e he e' he'' hs0 h1
        rw [hσ] at this
        rcases RC_fin2 b with rfl | rfl
        · rfl
        · simp at this
      · exfalso
        have hle : e'.2.2.countP PkgLetter.isLam ≤ e.2.2.countP PkgLetter.isLam := by
          rw [hσ]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he''
          rcases he'' with rfl | rfl <;> simp [List.countP_append, List.countP_cons]
        obtain ⟨hs0, -⟩ := hJ1 e he (by omega)
        rw [hσ] at hs0
        obtain ⟨c1, c2⟩ := RC_s0_split A B b hs0.symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he''
        rcases he'' with rfl | rfl <;> simp only at h2 <;> omega
    · rcases List.mem_append.1 (hp.subset he') with he'' | he''
      · obtain ⟨hs0, h1⟩ := hJ1 e' he'' h2
        refine ⟨hs0, hkeep ?_ h1⟩
        rcases RC_fin2 b with rfl | rfl
        · rfl
        · exfalso
          obtain ⟨w'', hw'', hwE'', hm''⟩ :=
            RC_letter' X e' he'' (PkgLetter.lw (.res 1)) (by rw [hs0]; decide)
          have hne : A₀ ++ PkgLetter.lw (.res 1) :: B₀ ≠ w'' := by
            rintro rfl; rw [hE] at hwE''; exact absurd hwE'' (by decide)
          have := FW_two_le (fun w => w.count (PkgLetter.lw (.res 1))) _ w'' hne
            (List.count_pos_iff.2 (by simp)) (List.count_pos_iff.2 hm'') X.loops hW hw''
          rw [((PG_onlyRes_iff X 1).1 h1).2] at this
          omega
      · exfalso
        rw [List.mem_singleton] at he''
        subst he''
        have hL := hJ2 _ hW hE
        have h0 : (A₀ ++ PkgLetter.lw (.res b) :: B₀).countP PkgLetter.isLam = 0 :=
          List.countP_eq_zero.2 fun x hx hl' => by
            rw [List.any_eq_false] at hL; exact hL x hx hl'
        dsimp only at h2
        simp only [List.countP_append, List.countP_cons, List.countP_nil, PkgLetter.isLam,
          Bool.false_eq_true, ↓reduceIte] at h2 h0
        omega
  · have hb : ∀ X : PkgExpr, X.onlyRes 1 = true → (b, y) ∈ X.weights → b = 0 := by
      intro X h1 hm
      have := ((PG_onlyRes_iff X 1).1 h1).1.1 _ hm
      rcases RC_fin2 b with rfl | rfl
      · rfl
      · exact absurd rfl this
    refine ⟨fun e' he' h2 => ?_, fun w hw hE => ?_⟩
    · rcases List.mem_append.1 (hp.subset he') with he'' | he''
      · obtain ⟨hs0, h1⟩ := hJ1 e' he'' h2
        refine ⟨hs0, ?_⟩
        have hb0 := hb X h1 (List.mem_of_getElem? hj)
        subst hb0
        obtain ⟨⟨hw1, hd1⟩, hc1⟩ := (PG_onlyRes_iff X 1).1 h1
        refine (PG_onlyRes_iff X' 1).2 ⟨⟨fun p hp => hw1 p ?_, fun w hw hm => ?_⟩, ?_⟩
        · rw [hwt] at hp; exact List.mem_of_mem_eraseIdx hp
        · rw [hl] at hw
          rcases List.mem_append.1 hw with hw | hw
          · exact hd1 w hw hm
          · rw [List.mem_singleton] at hw; subst hw; simp at hm
        · rw [hl, List.map_append, List.sum_append, hc1]
          simp
      · rw [List.mem_singleton] at he''
        subst he''
        simp [PkgLetter.isLam] at h2
    · rw [hl] at hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hJ2 w hw hE
      · rw [List.mem_singleton] at hw; subst hw; simp [PkgLetter.isEnt] at hE

/-- The start of the exceptional subcase of case (8): the expanded words of the derivative
structures of `𝒯₀` of Type III with `fR = 0`, `Σ = 0`. -/
private theorem RC_J_base (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ loopStart.pkgStart.dwirt 0 1 p₀ q₀) (hf : R₀.ffocus.isSome = true)
    (h3 : R₀.ptype = 3) (h0 : R₀.fR = 0) (hs : R₀.fsig = 0) : RC_J R₀.fpkg := by
  have key : ∀ pq ∈ [((0 : ℕ), (2 : ℕ)), (1, 1), (2, 0)],
      ∀ R₀ ∈ loopStart.pkgStart.dwirt 0 1 pq.1 pq.2, R₀.ffocus.isSome = true → R₀.ptype = 3 →
        R₀.fR = 0 → R₀.fsig = 0 →
        (∀ e ∈ R₀.fpkg.pents, 2 ≤ e.2.2.countP PkgLetter.isLam →
          e.2.2 = RC_s0 ∧ R₀.fpkg.onlyRes 1 = true) ∧
        ∀ w ∈ R₀.fpkg.loops, w.any PkgLetter.isEnt = false → w.any PkgLetter.isLam = false := by
    decide
  have hpq' : (p₀, q₀) ∈ [((0 : ℕ), (2 : ℕ)), (1, 1), (2, 0)] := by
    have : p₀ ≤ 2 := by omega
    interval_cases p₀ <;> simp <;> omega
  exact key _ hpq' R₀ hR₀ hf h3 h0 hs

/-! ### The derivative structures `R'` -/

private theorem RC_B (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    R'.wf = true ∧ R'.fR = R.fR + 1 ∧
    R'.charsP.1 + R'.charsP.2.2.1 = R.charsP.1 + R.charsP.2.2.1 + ((p + q : ℕ) : ℤ) ∧
    (∀ w ∈ R'.loops, w.any PkgLetter.isEnt = false → w ∈ R.loops) ∧
    R'.pents.length = 4 + (p + q) ∧
    (∀ l, (R'.pents.flatMap fun e => [e.1, e.2.1]).count l =
      if l < 2 then 3 else if l < 4 then 1 + (p + q) else 0) ∧
    ∃ a : Fin 2, (∃ e ∈ R'.pents, PkgLetter.lw (.det a) ∈ e.2.2) ∧
      (∃ e ∈ R'.pents, PkgLetter.lw (.res a) ∈ e.2.2) := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  have hFw := pkg_fpkg_wf R hRw hfoc
  obtain ⟨hw, hfR, hmu, hfree, -⟩ := RC_iter_L R.fpkg hFw p q R' hR'
  obtain ⟨hl, hc, hz⟩ := RC_iter_P R.fpkg p q R' hR'
  obtain ⟨g1, g2⟩ := RC_fpkg_chars R hfoc
  obtain ⟨a, f1, f2, f3, f4⟩ := RC_fpkg_P R hfoc
  obtain ⟨r1, r2⟩ := RC_ends_R ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  refine ⟨hw, by rw [hfR, g1], by rw [hmu, g2], fun w hw' hE =>
    RC_fpkg_free R hfoc w (hfree w hw' hE) hE, by omega, fun l => ?_, a, hz _ f3, hz _ f4⟩
  rw [hc l, f2 l, r2 l]
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

/-- Q1: the factors of a derivative structure satisfy the local conditions. -/
theorem pkg_rem_local (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    fLocal R'.nb R'.rfacs = true := by
  obtain ⟨hw, -, -, -, -, hc, -⟩ := RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  refine RC_local R' hw (RC_ends_lt R' 4 fun l hl => ?_)
  rw [hc l]
  simp only [show ¬ l < 2 by omega, show ¬ l < 4 by omega, ↓reduceIte]

/-- Q1: `frule` is valid on a derivative structure. -/
theorem pkg_rem_valid (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    fvalid R'.nb R'.rfacs (frule R'.rfacs) = true :=
  frule_run_valid _ _ false (pkg_rem_local ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')

/-- Q2 (a): `|E| = 4 + p + q`. -/
theorem pkg_rem_nent (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    (R'.rfacs.filterMap FFac.entData).length = 4 + (p + q) := by
  obtain ⟨-, -, -, -, hl, -⟩ := RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  rw [RC_E_len, hl]

/-- Q2 (b), (c): an entry without `Λ̃` has a resolvent; the entries and loops carry two `Λ̃`. -/
theorem pkg_rem_lam (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    (∀ d ∈ R'.rfacs.filterMap FFac.entData, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum) ∧
      ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum +
        ((fLoops R'.rfacs).map fun w => w.count FLet.lamt).sum = 2 := by
  obtain ⟨hw, -⟩ := RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  exact ⟨fun d hd h1 => RC_lam_b R' hw d hd h1, RC_lam_c R' hw⟩

/-- Q2 (d2): the derivatives keep `fR`, and `fpkg` adds one. -/
theorem pkg_rem_fR (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    R'.fR = R.fR + 1 := by
  exact (RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2.1

/-- Q2 (e): at most one pairing in all. -/
theorem pkg_rem_pair (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum + 2 * R'.fpi ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, a, ⟨e₁, he₁, hd⟩, ⟨e₂, he₂, hr⟩⟩ :=
    RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨w₁, hw₁, hd'⟩ := RC_letter R' e₁ he₁ _ hd
  obtain ⟨w₂, hw₂, hr'⟩ := RC_letter R' e₂ he₂ _ hr
  have hga : R'.fpg a = false := RC_fpg_of R' a (RC_onlyRes_det R' a w₁ hw₁ hd')
  have hma : R'.fpm a = false := RC_fpm_of R' a (RC_onlyDet_res R' a w₂ hw₂ hr')
  have key : ∀ c : Fin 2, R'.fpg c = true → R'.fpm 0 = false ∧ R'.fpm 1 = false := by
    intro c hc
    have hmc : R'.fpm c = false := by
      refine RC_fpm_of R' c (RC_onlyDet_det R' c fun w hw => ?_)
      have hoc : R'.onlyRes c = true := by
        unfold PkgExpr.fpg at hc; simp only [Bool.and_eq_true] at hc; exact hc.1
      exact ((PG_onlyRes_iff R' c).1 hoc).1.2 w hw
    have hca : c ≠ a := by rintro rfl; rw [hga] at hc; exact absurd hc (by decide)
    fin_cases a <;> fin_cases c <;> simp_all
  obtain ⟨-, hext⟩ := pkg_rfacs_ext R'
  unfold PkgExpr.fpi
  by_cases hg : (R'.fpg 0 || R'.fpg 1) = true
  · rw [ite_eq_left hg]
    have hc : ∃ c : Fin 2, R'.fpg c = true := by
      simp only [Bool.or_eq_true] at hg
      rcases hg with hg | hg
      · exact ⟨0, hg⟩
      · exact ⟨1, hg⟩
    obtain ⟨c, hc⟩ := hc
    obtain ⟨h0, h1⟩ := key c hc
    rw [RC_iv_zero R' h0 h1]
    norm_num
  · rw [ite_eq_right hg]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    exact hext

/-- Q2 (f): the ends of the entries: labels `0, 1` three times, `2, 3` `1 + p + q` times. -/
theorem pkg_rem_ends (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    ∀ l : ℕ, l < 4 → ((R'.rfacs.filterMap FFac.entData).flatMap fun d => [d.1, d.2.1]).count l =
      if l < 2 then 3 else 1 + (p + q) := by
  obtain ⟨-, -, -, -, -, hc, -⟩ := RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  intro l hl
  rw [RC_E_ends, hc l]
  split_ifs <;> omega

/-- Q2 (g): a loop without `Δ` is a loop of `R`; a loop factor without `Λ̃` has two
resolvents. -/
theorem pkg_rem_loops (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    (∀ w ∈ R'.loops, w.any PkgLetter.isEnt = false → w ∈ R.loops) ∧
      ∀ w ∈ fLoops R'.rfacs, FLet.lamt ∉ w → 2 ≤ fresN w := by
  obtain ⟨-, -, -, hfree, -⟩ := RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  refine ⟨fun w hw hE => hfree w hw hE, fun w hw hlam => ?_⟩
  obtain ⟨f, hf, hfw⟩ := List.mem_filterMap.1 hw
  rcases f with ⟨x, y, W⟩ | W | ⟨a, x⟩ <;> simp only [Option.some.injEq, reduceCtorEq] at hfw
  subst hfw
  rcases RC_mem_rfacs R' _ hf with ⟨p, -, h⟩ | ⟨e, -, h⟩ | ⟨w₀, hw₀, hE, h⟩
  · cases h
  · rw [FW_rent] at h
    unfold FW_mk at h
    obtain ⟨W', hW', -⟩ := RC_g_ent R' e.1 e.2.1
      (e.2.2.filterMap (PkgLetter.flet (fun _ => false) R'.fpm))
    rw [hW'] at h
    cases h
  · obtain ⟨W', hW', -, hsup, hcnt⟩ :=
      RC_g_loop R' (w₀.filterMap (PkgLetter.flet (fun _ => false) R'.fpm))
    rw [hW'] at h
    cases h
    have hL : w₀.any PkgLetter.isLam = false := by
      refine List.any_eq_false.2 fun x hx hxl => hlam ?_
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> simp [PkgLetter.isLam] at hxl
      exact hsup _ (List.mem_filterMap.2 ⟨_, hx, rfl⟩) (fun _ _ h => by cases h)
    have h2 := pkg_ffree_two ε n T hT p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR) w₀ (hfree w₀ hw₀ hE) hE hL
    rw [FW_fresN]
    rw [FW_piece_cnt0] at hcnt
    omega

/-- Q1, leaf: entry labels below `2`, and the local conditions. -/
theorem pkg_leaf_local (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) :
    (∀ d ∈ R.rfacs.filterMap FFac.entData, d.1 < 2 ∧ d.2.1 < 2) ∧
      fLocal R.nb R.rfacs = true := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨-, hc⟩ := RC_ends_R ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  have hlt := RC_ends_lt R 2 fun l hl => by
    rw [hc l]
    simp only [show ¬ l < 2 by omega, ↓reduceIte]
  refine ⟨fun d hd => ?_, RC_local R hRw fun e he =>
    ⟨by have := (hlt e he).1; omega, by have := (hlt e he).2; omega⟩⟩
  obtain ⟨e, he, hde⟩ := RC_E_mem R d hd
  obtain ⟨d', hd', h1, h2⟩ := RC_rent_some R e
  rw [hde] at hd'
  cases hd'
  rw [h1, h2]
  exact hlt e he

/-- Q1, leaf: `fruleLeaf` is valid. -/
theorem pkg_leaf_valid (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) :
    fvalid R.nb R.rfacs (fruleLeaf R.rfacs) = true :=
  frule_run_valid _ _ true (pkg_leaf_local ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR).2

/-- Q2, leaf: three entries, the `Λ̃` count, the resolvents of the entries without `Λ̃`, and the
ends `0, 1` three times each. -/
theorem pkg_leaf_counts (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) :
    (R.rfacs.filterMap FFac.entData).length = 3 ∧
      (∀ d ∈ R.rfacs.filterMap FFac.entData, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum) ∧
      ((R.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum +
        ((fLoops R.rfacs).map fun w => w.count FLet.lamt).sum = 2 ∧
      ∀ l : ℕ, l < 4 → ((R.rfacs.filterMap FFac.entData).flatMap fun d => [d.1, d.2.1]).count l =
        if l < 2 then 3 else 0 := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  obtain ⟨hl, hc⟩ := RC_ends_R ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  refine ⟨by rw [RC_E_len, hl], fun d hd h1 => RC_lam_b R hRw d hd h1, RC_lam_c R hRw,
    fun l _ => ?_⟩
  rw [RC_E_ends, hc l]

/-- Q3, leaf: every side is empty, so every entry with `Λ̃` has all parts `0`. -/
theorem pkg_leaf_sides (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) :
    (∀ (o : Fin 2) (side : Bool), R.lamSide o side = 0) ∧
      ∀ d ∈ R.rfacs.filterMap FFac.entData, 2 ≤ d.2.2.1.length → ∀ x ∈ d.2.2.1, x = 0 := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inl hR)
  have hs := RC_leaf_sides ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf
  refine ⟨hs, fun d hd h2 x hx => ?_⟩
  obtain ⟨e, he, hde⟩ := RC_E_mem R d hd
  obtain ⟨-, -, hl, hp⟩ := pkg_rent_parts R e he d hde
  have h1 : 1 ≤ e.2.2.countP PkgLetter.isLam := by rw [RC_parts_len] at hl; omega
  have hz := RC_parts_zero R hRw hs e he h1
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
  have := (hp t (by omega)).2.2 (hz t)
  rwa [List.getD_eq_getElem _ _ ht] at this

/-- Under the binders of the remainder pins of the proof of Lemma 5.5
[claim_estimate_remainder_terms]: a loop of `R` without resolvent is a loop of every derivative
structure `R'` (it is neither expanded nor differentiated). -/
theorem pkg_rem_resfree (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q)
    (w : List PkgLetter) (hw : w ∈ R.loops) (hres : w.any PkgLetter.isRes = false) :
    w ∈ R'.loops := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  exact RC_iter_res R.fpkg w hres (RC_fpkg_res R hfoc w hw hres) p q R' hR'

/-- Under the binders of the remainder pins of the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the number of resolvents and light weights `m + u` grows by one
with each of the `p + q` derivatives, and the expanded word keeps it. -/
theorem pkg_rem_mu (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    R'.charsP.1 + R'.charsP.2.2.1 = R.charsP.1 + R.charsP.2.2.1 + ((p + q : ℕ) : ℤ) := by
  exact (RC_B ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2.2.1

/-- Under the binders of the remainder pins of the proof of Lemma 5.5
[claim_estimate_remainder_terms], the exceptional subcase of case (8) (Type III, `fR = 0`,
`Σ = 0`): an entry of `R'` with both letters `Λ̃` has the parts `[0, 2, 0]`, and the resolvent
between them is the one doubled by the pairing through `𝒢`. -/
theorem pkg_rem_pairG (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q)
    (hty : R.ptype = 3) (hfR : R.fR = 0) (hs : R.fsig = 0) (d : FEnt)
    (hd : d ∈ R'.rfacs.filterMap FFac.entData) (h3 : d.2.2.1.length = 3) :
    R'.fpi = 1 ∧ d.2.2.1 = [0, 2, 0] := by
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  obtain ⟨-, -, -, -, h5⟩ := pkg_lists' ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  obtain ⟨rfl, rfl, -⟩ := h5 hfoc hty hfR hs
  have hJ : RC_J R' := pkg_dwirt_iter (fun _ X => RC_J X) 2 3
    (fun _ X hX X' h => RC_J_step X hX 2 3 X' h) (fun _ X hX X' h => RC_J_step X hX 3 2 X' h) _
    (RC_J_base p₀ q₀ hpq _ hR₀ hfoc hty hfR hs) p q R' hR'
  obtain ⟨e, he, hde⟩ := RC_E_mem R' d hd
  obtain ⟨-, -, hl, -⟩ := pkg_rent_parts R' e he d hde
  have h2 : 2 ≤ e.2.2.countP PkgLetter.isLam := by rw [RC_parts_len] at hl; omega
  obtain ⟨hs0, h1⟩ := hJ.1 e he h2
  obtain ⟨w, hw, hdw⟩ := RC_letter R' e he (.lw (.det 0)) (by rw [hs0]; decide)
  have h0 : R'.onlyRes 0 = false := RC_onlyRes_det R' 0 w hw hdw
  have hg0 : R'.fpg 0 = false := RC_fpg_of R' 0 h0
  have hg1 : R'.fpg 1 = true := by unfold PkgExpr.fpg; rw [h1, h0]; rfl
  refine ⟨by unfold PkgExpr.fpi; rw [hg0, hg1]; rfl, ?_⟩
  simp only [PkgExpr.rent, hg0, hg1, Bool.false_eq_true, ↓reduceIte, FFac.dupRes, FFac.entData,
    Option.some.injEq] at hde
  rw [← hde]
  change FLet.parts _ = _
  rw [FW_parts_dup, hs0]
  decide

/-- In an expression of Type III of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms], one package entry holds both letters `Λ̃`. -/
theorem pkg_ptype3_seg (X : PkgExpr) (hX : X.ptype = 3) :
    ∃ e ∈ X.pents, PkgLetter.lw (.lamt 0) ∈ e.2.2 ∧ PkgLetter.lw (.lamt 1) ∈ e.2.2 := by
  unfold PkgExpr.ptype at hX
  rcases hfind : X.loops.find? (fun w => w.contains (.lw (.lamt 1))) with _ | w₂
  · rw [hfind] at hX; exact absurd hX (by decide)
  rw [hfind] at hX
  have hw₂ : w₂ ∈ X.loops := List.mem_of_find?_eq_some hfind
  simp only at hX
  split_ifs at hX with h1 h2
  · exact absurd hX (by decide)
  swap
  · exact absurd hX (by decide)
  have hE : w₂.any PkgLetter.isEnt = true := by
    cases hc : w₂.any PkgLetter.isEnt
    · exact absurd (show (!(w₂.any PkgLetter.isEnt)) = true by rw [hc]; rfl) h1
    · rfl
  simp only [Bool.and_eq_true] at h2
  obtain ⟨h0, h3⟩ := h2
  have hm0 : PkgLetter.lw (.lamt 0) ∈ w₂ := by simpa using h0
  have hi : w₂.idxOf (PkgLetter.lw (.lamt 0)) < w₂.length := List.idxOf_lt_length_iff.2 hm0
  have hrot : w₂.rotate (w₂.idxOf (PkgLetter.lw (.lamt 0))) = .lw (.lamt 0) ::
      (w₂.drop (w₂.idxOf (PkgLetter.lw (.lamt 0)) + 1) ++
        w₂.take (w₂.idxOf (PkgLetter.lw (.lamt 0)))) := by
    rw [List.rotate_eq_drop_append_take hi.le, List.drop_eq_getElem_cons hi,
      List.getElem_idxOf hi]
    rfl
  rw [hrot, List.drop_one, List.tail_cons] at h3
  have hm1 := by simpa using h3
  obtain ⟨e, he, g0, g1⟩ := RC_seg_both w₂ hE _ _ hrot _ (fun _ _ => rfl) (fun _ => rfl) hm1
  exact ⟨e, by rw [RS_pents, List.mem_flatMap]; exact ⟨w₂, hw₂, he⟩, g0, g1⟩

/-- Every segment of a word with `Δ` of an expression of the further expansion in the proof of
Lemma 5.5 [claim_estimate_remainder_terms] is the segment of one of its package entries. -/
theorem pkg_pents_segs (X : PkgExpr) (w : List PkgLetter) (hw : w ∈ X.loops)
    (hE : w.any PkgLetter.isEnt = true) (σ : List PkgLetter) (hσ : σ ∈ pkgSegs w) :
    ∃ e ∈ X.pents, e.2.2 = σ := by
  exact RC_pents_segs X w hw hE σ hσ

/-- A package of a word with `Δ`, without `Λ̃`, with at least two resolvents (`freeTwo`) is an
entry of `rfacs` with one part of at least two resolvents, in the proof of Lemma 5.5
[claim_estimate_remainder_terms]. -/
theorem pkg_freeTwo_ent (X : PkgExpr) (h : X.freeTwo = true) :
    ∃ d ∈ X.rfacs.filterMap FFac.entData, d.2.2.1.length = 1 ∧ 2 ≤ d.2.2.1.sum := by
  unfold PkgExpr.freeTwo at h
  obtain ⟨w, hw, hw'⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at hw'
  obtain ⟨hE, hσ⟩ := hw'
  obtain ⟨σ, hσ, hσ'⟩ := List.any_eq_true.1 hσ
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hσ'
  obtain ⟨hnl, h2⟩ := hσ'
  obtain ⟨e, he, rfl⟩ := pkg_pents_segs X w hw hE σ hσ
  obtain ⟨d, hd, -, -⟩ := RC_rent_some X e
  have hdmem : d ∈ X.rfacs.filterMap FFac.entData := by
    rw [RC_E]; exact List.mem_filterMap.2 ⟨e, he, hd⟩
  obtain ⟨-, -, hl, hp⟩ := pkg_rent_parts X e he d hd
  have hpk := RC_parts_one e.2.2 (fun x hx => by
    by_contra hc
    exact absurd (List.any_eq_true.2 ⟨x, hx, by simpa using hc⟩) (by rw [hnl]; simp))
  obtain ⟨g1, -, -⟩ := hp 0 (by rw [hpk]; simp)
  rw [hpk] at hl g1
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 hl
  refine ⟨d, hdmem, by rw [hy]; rfl, ?_⟩
  rw [hy] at g1 ⊢
  simp only [List.getD_cons_zero, List.sum_cons, List.sum_nil, add_zero] at g1 ⊢
  omega

/-- The pairing through `𝔐_a` of the rules puts `Im m` on one entry of `rfacs`, in the proof of
Lemma 5.5 [claim_estimate_remainder_terms]: the total power of `Im m` of the entries is at least
`2` (half powers). -/
theorem pkg_fpm_ext (X : PkgExpr) (a : Fin 2) (h : X.fpm a = true) :
    2 ≤ ((X.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum := by
  have h' := h
  unfold PkgExpr.fpm at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨hd, hall⟩, -⟩ := h'
  unfold PkgExpr.onlyDet at hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨-, hsum⟩ := hd
  obtain ⟨w, hw, hwd⟩ : ∃ w ∈ X.loops, PkgLetter.lw (.det a) ∈ w := by
    by_contra hc
    simp only [not_exists, not_and] at hc
    have : (X.loops.map fun w => w.count (.lw (.det a))).sum = 0 :=
      List.sum_eq_zero fun c hc' => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc'
        exact List.count_eq_zero.2 (hc w hw)
    omega
  have hwE : w.any PkgLetter.isEnt = true := by
    have := List.all_eq_true.1 hall w hw
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    rcases this with h | h
    · exact h
    · simp [hwd] at h
  obtain ⟨σ, hσ, hdσ⟩ : ∃ σ ∈ pkgSegs w, PkgLetter.lw (.det a) ∈ σ := by
    by_contra hc
    simp only [not_exists, not_and] at hc
    have h1 : ((pkgSegs w).map (List.countP fun x => x == PkgLetter.lw (.det a))).sum =
        w.countP (fun x => x == PkgLetter.lw (.det a)) :=
      (PB_segs_count (fun x => x == PkgLetter.lw (.det a)) (fun x hx => by
        rcases x with _ | ⟨u, v⟩ <;> simp_all [isEntP]) w).1
    have h2 : 0 < w.countP (fun x => x == PkgLetter.lw (.det a)) :=
      List.countP_pos_iff.2 ⟨_, hwd, by simp⟩
    have h3 : ((pkgSegs w).map (List.countP fun x => x == PkgLetter.lw (.det a))).sum = 0 :=
      List.sum_eq_zero fun c hc' => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hc'
        refine List.countP_eq_zero.2 fun x hx hxe => hc σ hσ ?_
        simp only [beq_iff_eq] at hxe
        rw [← hxe]
        exact hx
    omega
  obtain ⟨e, he, rfl⟩ := pkg_pents_segs X w hw hwE σ hσ
  have hmem : X.rent e ∈ X.rfacs := by
    have : X.rent e ∈ X.rfacs.filter (fun f => f.entData.isSome) := by
      rw [pkg_rfacs_pents]; exact List.mem_map_of_mem he
    exact List.mem_of_mem_filter this
  rw [FW_iv_sum]
  have hnn : ∀ x ∈ X.rfacs.map FW_iv, 0 ≤ x := by
    intro x hx
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp [FW_iv]
  refine le_trans ?_ (List.single_le_sum hnn _ (List.mem_map_of_mem hmem))
  rw [FW_rent]
  unfold FW_mk
  obtain ⟨W', hW', -, hsup⟩ := RC_g_ent X e.1 e.2.1
    (e.2.2.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
  rw [hW']
  have hdet : FLet.det a true ∈ W' :=
    hsup _ (List.mem_filterMap.2 ⟨_, hdσ, by simp [PkgLetter.flet, h]⟩) (fun _ _ h => by cases h)
  have hc : 1 ≤ W'.countP FW_pd := List.countP_pos_iff.2 ⟨_, hdet, rfl⟩
  simp only [FW_iv]
  omega

end RBMTransitionEdge
