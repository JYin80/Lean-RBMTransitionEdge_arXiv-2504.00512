module

public import RBMTransitionEdge.Localized.Expansion.RemCounts
public import RBMTransitionEdge.Localized.Expansion.RemHalves
public import RBMTransitionEdge.Localized.Expansion.RemCommon
public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.RemCounts
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# The entries with `Λ̃` of the derivative structures of Type I

Under the binders of the remainder pins of the proof of Lemma 5.5 [claim_estimate_remainder_terms],
for an expression of Type I: the two entries of `R'` with a letter `Λ̃` (two parts each), the other
entries with one part, and their labels and parts in each case of the rules (i)–(iv) (Example 5.7
[example_estimate_reminder_reminder_terms] and the companion cases (1)–(3)).
-/

namespace RBMTransitionEdge

open private RC_rent_some RC_E RC_E_mem RC_letter' RC_parts_len RC_tw RC_isLam_cnt RC_seg_cnt
  RC_fpkg RC_ends_R from RBMTransitionEdge.Localized.Expansion.RemCounts
open private FW_two_le FW_wf_count FW_count_le FW_seg_cyc FW_rot_uniq FW_split_count
  from RBMTransitionEdge.Localized.Expansion.FEntWords
open private PB_segs_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private isEntP from RBMTransitionEdge.Localized.Expansion.PkgWords

/-! ### Letters `Λ̃` in the package entries -/

/-- Each letter `Λ̃_o` lies in a package entry, and no package entry holds both. -/
private def RT_J (X : PkgExpr) : Prop :=
  X.wf = true ∧ (∀ o : Fin 2, ∃ e ∈ X.pents, PkgLetter.lw (.lamt o) ∈ e.2.2) ∧
    ∀ e ∈ X.pents, PkgLetter.lw (.lamt 0) ∈ e.2.2 → PkgLetter.lw (.lamt 1) ∉ e.2.2

private theorem RT_fin2 (o : Fin 2) : o = 0 ∨ o = 1 := by
  fin_cases o <;> simp

/-- A word without `Δ` holds no letter `Λ̃` that lies in a package entry. -/
private theorem RT_free_lam (X : PkgExpr) (hX : X.wf = true) (w : List PkgLetter)
    (hw : w ∈ X.loops) (hE : w.any PkgLetter.isEnt = false) (o : Fin 2)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (ho : PkgLetter.lw (.lamt o) ∈ e.2.2) :
    PkgLetter.lw (.lamt o) ∉ w := by
  intro hw'
  obtain ⟨w', hw'L, hw'E, hz⟩ := RC_letter' X e he _ ho
  have hne : w' ≠ w := by
    rintro rfl
    rw [hE] at hw'E
    exact absurd hw'E (by decide)
  have h2 := FW_two_le (fun w => w.count (.lw (.lamt o))) w' w hne (List.count_pos_iff.2 hz)
    (List.count_pos_iff.2 hw') X.loops hw'L hw
  have h1 := FW_wf_count X hX o
  omega

/-- A letter `Λ̃` of `A c` with `c` not a `Λ̃` is a letter of `A`. -/
private theorem RT_mem_l (A : List PkgLetter) (c : PkgLetter) (hc : c.isLam = false) (o : Fin 2)
    (h : PkgLetter.lw (.lamt o) ∈ A ++ [c]) : PkgLetter.lw (.lamt o) ∈ A := by
  rcases List.mem_append.1 h with h | h
  · exact h
  · rw [List.mem_singleton] at h
    subst h
    simp [PkgLetter.isLam] at hc

/-- A letter `Λ̃` of `c B` with `c` not a `Λ̃` is a letter of `B`. -/
private theorem RT_mem_r (B : List PkgLetter) (c : PkgLetter) (hc : c.isLam = false) (o : Fin 2)
    (h : PkgLetter.lw (.lamt o) ∈ c :: B) : PkgLetter.lw (.lamt o) ∈ B := by
  rcases List.mem_cons.1 h with h | h
  · subst h
    simp [PkgLetter.isLam] at hc
  · exact h

/-- A package entry `A c B` cut into `A c₁` and `c₂ B` keeps the letters `Λ̃` apart. -/
private theorem RT_cut (X X' : PkgExpr) (hJ : RT_J X) (hw : X'.wf = true)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (A B : List PkgLetter) (c c₁ c₂ : PkgLetter)
    (hc : e.2.2 = A ++ c :: B) (h0 : c.isLam = false) (h1 : c₁.isLam = false)
    (h2 : c₂.isLam = false) (x₁ y₁ x₂ y₂ : ℕ)
    (hp : X'.pents.Perm (X.pents.erase e ++ [(x₁, y₁, A ++ [c₁]), (x₂, y₂, c₂ :: B)])) :
    RT_J X' := by
  obtain ⟨-, hex, hnb⟩ := hJ
  refine ⟨hw, fun o => ?_, fun f hf hf0 hf1 => ?_⟩
  · obtain ⟨e', he', ho⟩ := hex o
    by_cases hee : e' = e
    · rw [hee, hc] at ho
      rcases List.mem_append.1 ho with ho | ho
      · exact ⟨(x₁, y₁, A ++ [c₁]), hp.symm.subset (by simp), List.mem_append_left _ ho⟩
      · exact ⟨(x₂, y₂, c₂ :: B), hp.symm.subset (by simp),
          List.mem_cons_of_mem _ (RT_mem_r B c h0 o ho)⟩
    · exact ⟨e', hp.symm.subset (List.mem_append_left _ ((List.mem_erase_of_ne hee).2 he')), ho⟩
  · rcases List.mem_append.1 (hp.subset hf) with hf' | hf'
    · exact hnb f (List.mem_of_mem_erase hf') hf0 hf1
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf'
      rcases hf' with rfl | rfl
      · exact hnb e he (by rw [hc]; exact List.mem_append_left _ (RT_mem_l A c₁ h1 0 hf0))
          (by rw [hc]; exact List.mem_append_left _ (RT_mem_l A c₁ h1 1 hf1))
      · exact hnb e he
          (by rw [hc]; exact List.mem_append_right _ (List.mem_cons_of_mem _
            (RT_mem_r B c₂ h2 0 hf0)))
          (by rw [hc]; exact List.mem_append_right _ (List.mem_cons_of_mem _
            (RT_mem_r B c₂ h2 1 hf1)))

/-- A new package entry without `Λ̃` keeps the letters `Λ̃` apart. -/
private theorem RT_add (X X' : PkgExpr) (hJ : RT_J X) (hw : X'.wf = true)
    (f : ℕ × ℕ × List PkgLetter) (hf : ∀ o : Fin 2, PkgLetter.lw (.lamt o) ∉ f.2.2)
    (hp : X'.pents.Perm (X.pents ++ [f])) : RT_J X' := by
  obtain ⟨-, hex, hnb⟩ := hJ
  refine ⟨hw, fun o => ?_, fun g hg hg0 hg1 => ?_⟩
  · obtain ⟨e', he', ho⟩ := hex o
    exact ⟨e', hp.symm.subset (List.mem_append_left _ he'), ho⟩
  · rcases List.mem_append.1 (hp.subset hg) with hg' | hg'
    · exact hnb g hg' hg0 hg1
    · rw [List.mem_singleton] at hg'
      subst hg'
      exact hf 0 hg0

/-- One derivative of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] keeps the
letters `Λ̃` in package entries, apart. -/
private theorem RT_dent (X : PkgExpr) (hJ : RT_J X) (u v : ℕ) (X' : PkgExpr)
    (h : X' ∈ X.dent u v) : RT_J X' := by
  have hw := (pkg_dent_wf X X' u v hJ.1 h).1
  obtain ⟨-, ⟨e, he, A, b, B, hσ, -, hp⟩ | ⟨A, b, B, hmem, hE, -, hp⟩ | ⟨b, y, -, -, hp⟩⟩ :=
    pkg_dent_pents X u v X' h
  · exact RT_cut X X' hJ hw e he A B _ _ _ hσ rfl rfl rfl _ _ _ _ hp
  · refine RT_add X X' hJ hw _ (fun o ho => ?_) hp
    obtain ⟨e', he', ho'⟩ := hJ.2.1 o
    refine RT_free_lam X hJ.1 _ hmem hE o e' he' ho' ?_
    simp only [List.mem_cons, List.mem_append, PkgLetter.lw.injEq, reduceCtorEq,
      false_or] at ho ⊢
    tauto
  · refine RT_add X X' hJ hw _ (fun o ho => ?_) hp
    simp at ho

/-- The expanded word of the rules (i)–(iv) keeps the letters `Λ̃` in package entries, apart. -/
private theorem RT_fpkg (R : PkgExpr) (hJ : RT_J R) (hf : R.ffocus.isSome = true) :
    RT_J R.fpkg := by
  have hw := pkg_fpkg_wf R hJ.1 hf
  obtain ⟨ℓ, r, right, w, a, tl, hf', hwℓ, hrot, -⟩ := RC_fpkg R hf
  obtain ⟨-, -, hE, hF⟩ := pkg_fpkg_pents R ℓ r right hf' w hwℓ a tl hrot
  have hwL : w ∈ R.loops := List.mem_of_getElem? hwℓ
  have htl : ∀ z ∈ tl, z ∈ w := fun z hz =>
    List.mem_rotate.1 (by rw [hrot]; exact List.mem_cons_of_mem _ hz)
  cases hwE : w.any PkgLetter.isEnt
  · refine RT_add R R.fpkg hJ hw _ (fun o ho => ?_) (hF hwE)
    obtain ⟨e', he', ho'⟩ := hJ.2.1 o
    refine RT_free_lam R hJ.1 w hwL hwE o e' he' ho' (htl _ ?_)
    cases right <;> simpa using ho
  · obtain ⟨e, he, A, B, hσ, hp⟩ := hE hwE
    cases right
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp
      exact RT_cut R R.fpkg hJ hw e he A B _ _ _ hσ rfl rfl rfl _ _ _ _ hp
    · simp only [↓reduceIte] at hp
      exact RT_cut R R.fpkg hJ hw e he A B _ _ _ hσ rfl rfl rfl _ _ _ _ hp

/-- The rotation of a word to the first place of one of its letters. -/
private theorem RT_rot_idx (w : List PkgLetter) (x : PkgLetter) (hx : x ∈ w) :
    ∃ V, w.rotate (w.idxOf x) = x :: V := by
  have hlt : w.idxOf x < w.length := List.idxOf_lt_length_of_mem hx
  refine ⟨w.drop (w.idxOf x + 1) ++ w.take (w.idxOf x), ?_⟩
  rw [List.rotate_eq_drop_append_take hlt.le, List.drop_eq_getElem_cons hlt,
    List.getElem_idxOf hlt]
  rfl

/-- In an expression of Type I of (5.79) [further_expansion_expression_Type_1] whose package of
`Λ̃₁` has no `Λ̃` before `Λ̃₁`, each `Λ̃_o` lies in a package entry, and no entry holds both. -/
private theorem RT_base (R : PkgExpr) (hw : R.wf = true) (hty : R.ptype = 1)
    (h1 : ∃ w ∈ R.loops, w.any PkgLetter.isEnt = true ∧ ∃ σ ∈ pkgSegs w,
      PkgLetter.lw (.lamt 0) ∈ σ ∧
      (σ.takeWhile fun x => x ≠ PkgLetter.lw (.lamt 0)).all
        (fun x => !x.isRes && !x.isLam) = true) :
    RT_J R := by
  obtain ⟨w₀, hw₀, hE₀, σ₀, hσ₀, hm₀, htw⟩ := h1
  obtain ⟨e₀, he₀, hσe⟩ := pkg_pents_segs R w₀ hw₀ hE₀ σ₀ hσ₀
  unfold PkgExpr.ptype at hty
  rcases hfind : R.loops.find? (fun w => w.contains (.lw (.lamt 1))) with _ | w₂
  · rw [hfind] at hty
    exact absurd hty (by decide)
  rw [hfind] at hty
  have hw₂ : w₂ ∈ R.loops := List.mem_of_find?_eq_some hfind
  have hl₂ : PkgLetter.lw (.lamt 1) ∈ w₂ := by simpa using List.find?_some hfind
  simp only at hty
  split_ifs at hty with hA hB
  · omega
  · omega
  have hE₂ : w₂.any PkgLetter.isEnt = true := by
    have h' : ¬ (!(w₂.any PkgLetter.isEnt)) = true := hA
    simpa using h'
  refine ⟨hw, fun o => ?_, fun e he h0 h1 => ?_⟩
  · rcases RT_fin2 o with rfl | rfl
    · exact ⟨e₀, he₀, hσe ▸ hm₀⟩
    · have hc : ((pkgSegs w₂).map (List.countP fun x => x == .lw (.lamt 1))).sum =
          w₂.countP (fun x => x == .lw (.lamt 1)) :=
        (PB_segs_count (fun x => x == .lw (.lamt 1)) (fun x hx => by
          rcases x with _ | ⟨u, v⟩
          · simp [isEntP] at hx
          · rfl) w₂).1
      have hpos : 0 < w₂.countP (fun x => x == .lw (.lamt 1)) :=
        List.countP_pos_iff.2 ⟨_, hl₂, by simp⟩
      obtain ⟨n, hn, hn0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero (by omega : _ ≠ 0)
        (l := (pkgSegs w₂).map (List.countP fun x => x == .lw (.lamt 1)))
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hn
      obtain ⟨z, hz, hzq⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero hn0)
      rw [beq_iff_eq] at hzq
      subst hzq
      obtain ⟨e, he, rfl⟩ := pkg_pents_segs R w₂ hw₂ hE₂ σ hσ
      exact ⟨e, he, hz⟩
  · have hee : e = e₀ := pkg_pents_lam_uniq R hw 0 e e₀ he he₀ h0 (hσe ▸ hm₀)
    have h1' : PkgLetter.lw (.lamt 1) ∈ σ₀ := by rw [← hσe, ← hee]; exact h1
    obtain ⟨T, rest, hTr⟩ := List.append_of_mem hm₀
    have hc0 : σ₀.count (.lw (.lamt 0)) ≤ 1 := hσe ▸ RC_seg_cnt R hw e₀ he₀ 0
    have hT0 : PkgLetter.lw (.lamt 0) ∉ T := by
      intro h
      rw [hTr, List.count_append, List.count_cons_self] at hc0
      have := List.count_pos_iff.2 h
      omega
    have htk : (σ₀.takeWhile fun x => decide (x ≠ PkgLetter.lw (.lamt 0))) = T := by
      rw [hTr]
      exact RC_tw _ _ rest (by simp) T (fun z hz => by
        simp only [ne_eq, decide_eq_true_eq]
        rintro rfl
        exact hT0 hz)
    rw [htk] at htw
    have hT1 : PkgLetter.lw (.lamt 1) ∉ T := fun h => by
      have := List.all_eq_true.1 htw _ h
      simp [PkgLetter.isLam] at this
    have hr1 : PkgLetter.lw (.lamt 1) ∈ rest := by
      rw [hTr] at h1'
      rcases List.mem_append.1 h1' with h | h
      · exact absurd h hT1
      · rcases List.mem_cons.1 h with h | h
        · exact absurd h (by decide)
        · exact h
    obtain ⟨hσE, M, hrot, ⟨u, v, M₁, hM₁⟩, -⟩ := FW_seg_cyc w₀ σ₀ hE₀ hσ₀
    have hrot' : w₀ ~r (PkgLetter.lw (.lamt 0) :: (rest ++ PkgLetter.ent u v :: (M₁ ++ T))) := by
      refine hrot.trans ?_
      rw [hTr, hM₁]
      have e1 : T ++ PkgLetter.lw (.lamt 0) :: rest ++ PkgLetter.ent u v :: M₁ =
          T ++ (PkgLetter.lw (.lamt 0) :: (rest ++ PkgLetter.ent u v :: M₁)) := by simp
      rw [e1]
      refine List.isRotated_append.trans ?_
      simp only [List.cons_append, List.append_assoc]
      exact List.IsRotated.refl _
    have h1w₀ : PkgLetter.lw (.lamt 1) ∈ w₀ := hrot'.perm.symm.subset (by simp [hr1])
    have hw20 : w₂ = w₀ := by
      by_contra hne
      have := FW_two_le (fun w => w.count (.lw (.lamt 1))) w₂ w₀ hne (List.count_pos_iff.2 hl₂)
        (List.count_pos_iff.2 h1w₀) R.loops hw₂ hw₀
      have := FW_wf_count R hw 1
      omega
    subst hw20
    apply hB
    have h0w : PkgLetter.lw (.lamt 0) ∈ w₂ := hrot'.perm.symm.subset List.mem_cons_self
    obtain ⟨V, hV⟩ := RT_rot_idx w₂ _ h0w
    have hVeq : V = rest ++ PkgLetter.ent u v :: (M₁ ++ T) := by
      refine FW_rot_uniq _ V _ ((List.IsRotated.symm (show w₂ ~r _ from ⟨_, hV⟩)).trans hrot') ?_
      intro hV0
      have hc := FW_count_le R hw 0 w₂ hw₂
      rw [← (List.rotate_perm w₂ (w₂.idxOf (.lw (.lamt 0)))).count_eq, hV,
        List.count_cons_self] at hc
      have := List.count_pos_iff.2 hV0
      omega
    have key : ∀ p : PkgLetter → Bool, p (.ent u v) = false → (∀ z ∈ rest, p z = true) →
        ((rest ++ PkgLetter.ent u v :: (M₁ ++ T)).takeWhile p).contains
          (.lw (.lamt 1)) = true := by
      intro p hp hp'
      rw [RC_tw p _ _ hp rest hp']
      exact List.elem_eq_true_of_mem hr1
    rw [hV, hVeq, Bool.and_eq_true]
    refine ⟨List.elem_eq_true_of_mem h0w, key _ rfl fun z hz => ?_⟩
    have := hσE z (by rw [hTr]; simp [hz])
    rcases z with _ | ⟨u', v'⟩
    · rfl
    · simp [PkgLetter.isEnt] at this

/-- The parts of a package entry with the one letter `Λ̃_o` are the two sides of `Λ̃_o`. -/
private theorem RT_pkgParts (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) (ho : PkgLetter.lw (.lamt o) ∈ e.2.2)
    (h1 : e.2.2.countP PkgLetter.isLam = 1) :
    pkgParts e.2.2 = [X.lamSide o false, X.lamSide o true] := by
  obtain ⟨T, rest, hTr⟩ := List.append_of_mem ho
  have hT : ∀ z ∈ T, PkgLetter.isLam z = false := by
    intro z hz
    by_contra hz'
    rw [hTr, List.countP_append, List.countP_cons] at h1
    have := List.countP_pos_iff.2 ⟨z, hz, by simpa using hz'⟩
    simp only [PkgLetter.isLam, ↓reduceIte] at h1
    omega
  have hk : ((e.2.2.takeWhile fun x => x != .lw (.lamt o)).countP PkgLetter.isLam) = 0 := by
    rw [hTr, RC_tw _ _ rest (by simp) T (fun z hz => by
      have := hT z hz
      simp only [bne_iff_ne, ne_eq]
      rintro rfl
      simp [PkgLetter.isLam] at this)]
    exact List.countP_eq_zero.2 fun z hz => by simp [hT z hz]
  obtain ⟨s0, s1⟩ := pkg_pents_sides X hX e he o ho
  rw [hk] at s0 s1
  have hl := RC_parts_len e.2.2
  rw [h1] at hl
  rcases hP : pkgParts e.2.2 with _ | ⟨a, _ | ⟨b, _ | ⟨c, L⟩⟩⟩ <;> rw [hP] at hl <;>
    simp at hl
  rw [hP] at s0 s1
  simp only [List.getD_cons_zero, List.getD_cons_succ] at s0 s1
  rw [s0, s1]

/-- The data of the entry of a package with the one letter `Λ̃_o`: its labels, and two parts
bounded below by the sides of `Λ̃_o` and zero where they are. -/
private theorem RT_parts (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) (ho : PkgLetter.lw (.lamt o) ∈ e.2.2)
    (h1 : e.2.2.countP PkgLetter.isLam = 1) (d : FEnt) (hd : (X.rent e).entData = some d) :
    d.1 = e.1 ∧ d.2.1 = e.2.1 ∧ ∃ p₀ p₁ : ℕ, d.2.2.1 = [p₀, p₁] ∧
      X.lamSide o false ≤ p₀ ∧ (X.lamSide o false = 0 → p₀ = 0) ∧
      X.lamSide o true ≤ p₁ ∧ (X.lamSide o true = 0 → p₁ = 0) := by
  have hP := RT_pkgParts X hX e he o ho h1
  obtain ⟨g1, g2, g3, g4⟩ := pkg_rent_parts X e he d hd
  rw [hP] at g3 g4
  refine ⟨g1, g2, ?_⟩
  rcases hD : d.2.2.1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, L⟩⟩⟩ <;> rw [hD] at g3 g4 <;> simp at g3
  have t0 := g4 0 (by simp)
  have t1 := g4 1 (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at t0 t1
  exact ⟨a, b, rfl, t0.1, t0.2.2, t1.1, t1.2.2⟩

/-- A package entry of a well-formed expression with `Λ̃_o` and no other `Λ̃` has one `Λ̃`. -/
private theorem RT_cnt1 (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) (ho : PkgLetter.lw (.lamt o) ∈ e.2.2)
    (hn : ∀ o' : Fin 2, PkgLetter.lw (.lamt o') ∈ e.2.2 → o' = o) :
    e.2.2.countP PkgLetter.isLam = 1 := by
  rw [RC_isLam_cnt]
  have c0 := RC_seg_cnt X hX e he 0
  have c1 := RC_seg_cnt X hX e he 1
  have p := List.count_pos_iff.2 ho
  rcases RT_fin2 o with rfl | rfl
  · have : e.2.2.count (.lw (.lamt 1)) = 0 :=
      List.count_eq_zero.2 fun h => absurd (hn 1 h) (by decide)
    omega
  · have : e.2.2.count (.lw (.lamt 0)) = 0 :=
      List.count_eq_zero.2 fun h => absurd (hn 0 h) (by decide)
    omega

/-- The ends of the package entries of an expression with labels `0`, `1` only are `0`, `1`. -/
private theorem RT_lab (R : PkgExpr)
    (hc : ∀ l : ℕ, (R.pents.flatMap fun e => [e.1, e.2.1]).count l = if l < 2 then 3 else 0)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ R.pents) : e.1 < 2 ∧ e.2.1 < 2 := by
  have k : ∀ l, l ∈ [e.1, e.2.1] → l < 2 := by
    intro l hl
    by_contra h
    have h0 := hc l
    simp only [h, ↓reduceIte] at h0
    have h1 : l ∈ R.pents.flatMap fun e => [e.1, e.2.1] := List.mem_flatMap.2 ⟨e, he, hl⟩
    rw [← List.count_pos_iff] at h1
    omega
  exact ⟨k _ (by simp), k _ (by simp)⟩

/-- An entry with parts `[a, 0]` and an inner right label has role `0`. -/
private theorem RT_role_last (d : FEnt) (a : ℕ) (hd : d.2.2.1 = [a, 0]) (hy : 2 ≤ d.2.1) :
    FEnt.role d = 0 := by
  unfold FEnt.role fInnerL
  rw [hd]
  simp [hy]

/-- An entry with parts `[0, b]` and an inner left label has role `0`. -/
private theorem RT_role_head (d : FEnt) (b : ℕ) (hd : d.2.2.1 = [0, b]) (hx : 2 ≤ d.1) :
    FEnt.role d = 0 := by
  unfold FEnt.role fInnerL
  rw [hd]
  simp [hx]

/-- Under rule (iv) (the left side of `Λ̃₂`), a package entry of the expanded word that starts at
the label `2` and holds `Λ̃₂` ends at a label `0` or `1`. -/
private theorem RT_half_lab (R : PkgExpr) (hJ : RT_J R) (hf : R.ffocus.isSome = true)
    (hc : ∀ l : ℕ, (R.pents.flatMap fun e => [e.1, e.2.1]).count l = if l < 2 then 3 else 0)
    (hfs : R.ffocusSide = some (1, false)) (e₀ : ℕ × ℕ × List PkgLetter)
    (he₀ : e₀ ∈ R.fpkg.pents) (h₀ : e₀.1 = 2) (hl : PkgLetter.lw (.lamt 1) ∈ e₀.2.2) :
    e₀.2.1 < 2 := by
  obtain ⟨ℓ, r, right, w, a, tl, hf', hwℓ, hrot, -⟩ := RC_fpkg R hf
  obtain ⟨o', ho'⟩ := (pkg_ffocusSide R).2 ℓ r right hf'
  rw [hfs, Option.some.injEq, Prod.mk.injEq] at ho'
  obtain ⟨-, rfl⟩ := ho'
  obtain ⟨-, -, hE, hF⟩ := pkg_fpkg_pents R ℓ r false hf' w hwℓ a tl hrot
  simp only [Bool.false_eq_true, ↓reduceIte] at hE hF
  have hwL : w ∈ R.loops := List.mem_of_getElem? hwℓ
  cases hwE : w.any PkgLetter.isEnt
  · rcases List.mem_append.1 ((hF hwE).subset he₀) with h | h
    · have := (RT_lab R hc e₀ h).1
      omega
    · rw [List.mem_singleton] at h
      subst h
      obtain ⟨e', he', ho⟩ := hJ.2.1 1
      have htl : PkgLetter.lw (.lamt 1) ∈ tl := by simpa using hl
      exact absurd (List.mem_rotate.1 (by rw [hrot]; exact List.mem_cons_of_mem _ htl))
        (RT_free_lam R hJ.1 w hwL hwE 1 e' he' ho)
  · obtain ⟨e, he, A, B, -, hp⟩ := hE hwE
    rcases List.mem_append.1 (hp.subset he₀) with h | h
    · have := (RT_lab R hc e₀ (List.mem_of_mem_erase h)).1
      omega
    · have hle := RT_lab R hc e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl
      · simp only at h₀
        omega
      · exact hle.2

/-! ### The entries with `Λ̃` -/

/-- The two entries with a letter `Λ̃` of a derivative structure of an expression of Type I in
the proof of Lemma 5.5 [claim_estimate_remainder_terms] (Example 5.7
[example_estimate_reminder_reminder_terms], cases (1)–(3)): the entries of `R'` are `d₁`, `d₂`
with two parts each and entries with one part, and the labels and parts of `d₁`, `d₂` in each
case of the rules (i)–(iv). -/
theorem pkg_typeOne_lams (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 1) (p q : ℕ) (R' : PkgExpr)
    (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) (o : Fin 2) (side : Bool)
    (hfs : R.ffocusSide = some (o, side)) :
    ∃ d₁ d₂ : FEnt, ∃ E₀ : List FEnt,
      (R'.rfacs.filterMap FFac.entData).Perm (d₁ :: d₂ :: E₀) ∧
      d₁.2.2.1.length = 2 ∧ d₂.2.2.1.length = 2 ∧ (∀ d ∈ E₀, d.2.2.1.length = 1) ∧
      ((o, side) = (1, true) → d₂.2.1 = 3 ∧ (∃ r₂ : ℕ, 1 ≤ r₂ ∧ d₂.2.2.1 = [r₂, 0]) ∧
        d₁.1 < 2 ∧ ∃ r₁ : ℕ, 1 ≤ r₁ ∧ d₁.2.2.1 = [0, r₁]) ∧
      ((o, side) = (0, true) → d₂.2.1 < 2 ∧ (∃ r₂ : ℕ, 1 ≤ r₂ ∧ d₂.2.2.1 = [r₂, 0]) ∧
        d₁.1 < 2 ∧ d₁.2.1 = 3 ∧ d₁.2.2.1 = [0, 0]) ∧
      ((o, side) = (1, false) → d₂.1 = 2 ∧ d₂.2.1 < 2 ∧ d₂.2.2.1 = [0, 0] ∧
        d₁.1 < 2 ∧ d₁.2.1 < 2 ∧ d₁.2.2.1 = [0, 0]) := by
  have hRw : R.wf = true := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hf : R.ffocus.isSome = true := pkg_fInner_focus ε j [R₀] R hR
  have hJR : RT_J R :=
    RT_base R hRw hty (pkg_inv_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR))
  have hJF : RT_J R.fpkg := RT_fpkg R hJR hf
  have hJ' : RT_J R' := pkg_dwirt_iter (fun _ X => RT_J X) 2 3
    (fun _ X hX X' h => RT_dent X hX 2 3 X' h) (fun _ X hX X' h => RT_dent X hX 3 2 X' h)
    R.fpkg hJF p q R' hR'
  obtain ⟨hw', hex, hnb⟩ := hJ'
  obtain ⟨e₁, he₁, h₁⟩ := hex 0
  obtain ⟨e₂, he₂, h₂⟩ := hex 1
  have n₁ : PkgLetter.lw (.lamt 1) ∉ e₁.2.2 := hnb e₁ he₁ h₁
  have n₂ : PkgLetter.lw (.lamt 0) ∉ e₂.2.2 := fun h => hnb e₂ he₂ h h₂
  have hne : e₁ ≠ e₂ := by
    rintro rfl
    exact n₁ h₂
  have c₁ : e₁.2.2.countP PkgLetter.isLam = 1 := RT_cnt1 R' hw' e₁ he₁ 0 h₁ fun o' h => by
    rcases RT_fin2 o' with rfl | rfl
    · rfl
    · exact absurd h n₁
  have c₂ : e₂.2.2.countP PkgLetter.isLam = 1 := RT_cnt1 R' hw' e₂ he₂ 1 h₂ fun o' h => by
    rcases RT_fin2 o' with rfl | rfl
    · exact absurd h n₂
    · rfl
  obtain ⟨d₁, hd₁, -, -⟩ := RC_rent_some R' e₁
  obtain ⟨d₂, hd₂, -, -⟩ := RC_rent_some R' e₂
  obtain ⟨g₁x, g₁y, a₁, b₁, hP₁, l₁a, z₁a, l₁b, z₁b⟩ := RT_parts R' hw' e₁ he₁ 0 h₁ c₁ d₁ hd₁
  obtain ⟨g₂x, g₂y, a₂, b₂, hP₂, l₂a, z₂a, l₂b, z₂b⟩ := RT_parts R' hw' e₂ he₂ 1 h₂ c₂ d₂ hd₂
  -- the entries of `R'` as `d₁ :: d₂ :: E₀`
  have hm₂ : e₂ ∈ R'.pents.erase e₁ := (List.mem_erase_of_ne hne.symm).2 he₂
  have hperm : R'.pents.Perm (e₁ :: e₂ :: (R'.pents.erase e₁).erase e₂) :=
    (List.perm_cons_erase he₁).trans ((List.perm_cons_erase hm₂).cons e₁)
  have hE : (R'.rfacs.filterMap FFac.entData).Perm
      (d₁ :: d₂ :: ((R'.pents.erase e₁).erase e₂).filterMap fun e => (R'.rent e).entData) := by
    rw [RC_E]
    have := hperm.filterMap (fun e => (R'.rent e).entData)
    rwa [List.filterMap_cons_some (f := fun e => (R'.rent e).entData) hd₁,
      List.filterMap_cons_some (f := fun e => (R'.rent e).entData) hd₂] at this
  refine ⟨d₁, d₂, _, hE, by rw [hP₁]; rfl, by rw [hP₂]; rfl, fun d hd => ?_, ?_⟩
  · -- every other entry has one part
    have hlam := (pkg_rem_lam ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2
    rw [(hE.map _).sum_eq] at hlam
    simp only [List.map_cons, List.sum_cons, hP₁, hP₂, List.length_cons, List.length_nil]
      at hlam
    have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d : FEnt => d.2.2.1.length - 1)
      hd)
    have hdE : d ∈ R'.rfacs.filterMap FFac.entData :=
      hE.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
    obtain ⟨e, he, hde⟩ := RC_E_mem R' d hdE
    obtain ⟨-, -, hl, -⟩ := pkg_rent_parts R' e he d hde
    rw [RC_parts_len] at hl
    have hu : ((((R'.pents.erase e₁).erase e₂).filterMap fun e => (R'.rent e).entData).map
        fun d : FEnt => d.2.2.1.length - 1).sum = 0 := by
      generalize ((((R'.pents.erase e₁).erase e₂).filterMap fun e => (R'.rent e).entData).map
        fun d : FEnt => d.2.2.1.length - 1).sum = U at hlam ⊢
      generalize ((fLoops R'.rfacs).map fun w => w.count FLet.lamt).sum = L at hlam
      omega
    rw [hu] at hle
    omega
  -- the common facts of the three cases
  have hcases := pkg_ffocusSide_cases R (by rw [hty]; decide)
  obtain ⟨hcnt0, er, her, e0, he0, hro, hro0, hrole, hst, hsf⟩ :=
    pkg_rem_role0 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' o side hfs
  obtain ⟨hl0, el, hel, hlo, hlx, -⟩ :=
    pkg_rem_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hsd := pkg_rem_sides ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hfl := pkg_fpkg_lamSide R hRw hf
  have k0 : R.fpkg.lamSide o side = 0 := by rw [hfl, hfs]; simp
  have k1 : ∀ (o' : Fin 2) (s' : Bool), (o', s') ≠ (o, side) →
      R.fpkg.lamSide o' s' = R.lamSide o' s' := fun o' s' h => by
    rw [hfl, hfs]
    simp [Ne.symm h]
  have hord := (pkg_inv_order ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).1 hty
  have hpos := pkg_ffocusSide_pos R hRw o side hfs
  have hx₁ : d₁.1 < 2 := by
    rw [g₁x, ← pkg_pents_lam_uniq R' hw' 0 el e₁ hel he₁ hlo h₁]
    exact hlx
  have ha₁ : a₁ = 0 := z₁a hl0
  have hrole2 : ¬ (FEnt.role d₁ = 0 ∧ FEnt.role d₂ = 0) := by
    rintro ⟨r1, r2⟩
    rw [hE.countP_eq] at hcnt0
    simp only [List.countP_cons, r1, r2, beq_self_eq_true, ↓reduceIte] at hcnt0
    omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · -- rule (i): the right side of `Λ̃₂`
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have her2 : er = e₂ := pkg_pents_lam_uniq R' hw' 1 er e₂ her he₂ hro h₂
    have hb₂ : b₂ = 0 := z₂b ((hsd 1 true).1 k0)
    have ha₂ : 1 ≤ a₂ := le_trans ((hsd 1 false).2 (by
      rw [k1 1 false (by decide)]; exact (hord.1 hpos).2)).1 l₂a
    have hb₁ : 1 ≤ b₁ := le_trans ((hsd 0 true).2 (by
      rw [k1 0 true (by decide)]; exact (hord.1 hpos).1)).1 l₁b
    refine ⟨by rw [g₂y, ← her2]; exact (hst rfl).1, ⟨a₂, ha₂, by rw [hP₂, hb₂]⟩, hx₁,
      ⟨b₁, hb₁, by rw [hP₁, ha₁]⟩⟩
  · -- rule (iii): the right side of `Λ̃₁`
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have her1 : er = e₁ := pkg_pents_lam_uniq R' hw' 0 er e₁ her he₁ hro h₁
    have h3 := hcases.2.1 hfs
    have hb₂ : b₂ = 0 := z₂b ((hsd 1 true).1 (by rw [k1 1 true (by decide)]; exact h3))
    have ha₂ : 1 ≤ a₂ := by
      refine le_trans ((hsd 1 false).2 ?_).1 l₂a
      rw [k1 1 false (by decide)]
      by_contra h0
      have := (hord.2 (by omega)).1
      omega
    have hb₁ : b₁ = 0 := z₁b ((hsd 0 true).1 k0)
    refine ⟨?_, ⟨a₂, ha₂, by rw [hP₂, hb₂]⟩, hx₁, by rw [g₁y, ← her1]; exact (hst rfl).1,
      by rw [hP₁, ha₁, hb₁]⟩
    by_contra hy
    refine hrole2 ⟨?_, RT_role_last d₂ a₂ (by rw [hP₂, hb₂]) (by omega)⟩
    rw [her1, hd₁] at hrole
    simpa using hrole
  · -- rule (iv): the left side of `Λ̃₂`
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have her2 : er = e₂ := pkg_pents_lam_uniq R' hw' 1 er e₂ her he₂ hro h₂
    obtain ⟨h3, h1⟩ := hcases.2.2 hfs
    have hf10 : R.fpkg.lamSide 1 false = 0 := k0
    have hf11 : R.fpkg.lamSide 1 true = 0 := by rw [k1 1 true (by decide)]; exact h3
    have hf01 : R.fpkg.lamSide 0 true = 0 := by rw [k1 0 true (by decide)]; exact h1
    have ha₂ : a₂ = 0 := z₂a ((hsd 1 false).1 hf10)
    have hb₂ : b₂ = 0 := z₂b ((hsd 1 true).1 hf11)
    have hb₁ : b₁ = 0 := z₁b ((hsd 0 true).1 hf01)
    have hx₂ : d₂.1 = 2 := by rw [g₂x, ← her2]; exact (hsf rfl).1
    refine ⟨hx₂, ?_, by rw [hP₂, ha₂, hb₂], hx₁, ?_, by rw [hP₁, ha₁, hb₁]⟩
    · -- the end piece at the label `2` of the half holding `Λ̃₂` is the whole half
      have hx0 : e0.1 = 2 := (hsf rfl).2.1
      have hn0 : PkgLetter.lw (.lamt 0) ∉ e0.2.2 := fun h => hJF.2.2 e0 he0 h hro0
      have hc0 : e0.2.2.countP PkgLetter.isLam = 1 := RT_cnt1 R.fpkg hJF.1 e0 he0 1 hro0
        fun o' h => by
          rcases RT_fin2 o' with rfl | rfl
          · exact absurd h hn0
          · rfl
      have hP0 := RT_pkgParts R.fpkg hJF.1 e0 he0 1 hro0 hc0
      rw [hf10, hf11] at hP0
      have hres : e0.2.2.countP PkgLetter.isRes = 0 := by
        have hs := (FW_split_count PkgLetter.isLam PkgLetter.isRes (fun x hx => by
          rcases x with ((b | b | y | k) | ⟨u, v⟩) <;>
            first | rfl | simp [PkgLetter.isLam] at hx) e0.2.2).1
        change (pkgParts e0.2.2).sum = _ at hs
        rw [hP0] at hs
        simp at hs
        omega
      obtain ⟨e', he', hx', hpre, hcut⟩ :=
        (pkg_rem_pieces ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' e0 he0).1
      rcases hcut with ⟨hy', hw''⟩ | ⟨-, -, hlast⟩
      · have he'2 : e' = e₂ :=
          pkg_pents_lam_uniq R' hw' 1 e' e₂ he' he₂ (by rw [hw'']; exact hro0) h₂
        rw [g₂y, ← he'2, hy']
        exact RT_half_lab R hJR hf (RC_ends_R ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).2
          hfs e0 he0 hx0 hro0
      · exfalso
        obtain ⟨z, hz, hzr⟩ := Option.map_eq_some_iff.1 hlast
        have hz0 : z ∈ e0.2.2 := hpre.subset (List.mem_of_getLast? hz)
        have := List.countP_pos_iff.2 ⟨z, hz0, hzr⟩
        omega
    · -- the right label of the entry of `Λ̃₁`
      by_contra hy
      refine hrole2 ⟨RT_role_last d₁ 0 (by rw [hP₁, ha₁, hb₁]) (by omega), ?_⟩
      exact RT_role_head d₂ 0 (by rw [hP₂, ha₂, hb₂]) (by omega)

end RBMTransitionEdge
