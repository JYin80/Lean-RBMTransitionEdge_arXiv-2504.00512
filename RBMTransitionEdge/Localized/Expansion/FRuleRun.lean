module

public import RBMTransitionEdge.Localized.Expansion.FRule
public import RBMTransitionEdge.Localized.Expansion.FOpts
import all RBMTransitionEdge.Localized.Expansion.FOpts

@[expose] public section

/-!
# The run of the rule

The rule of the further-class bound in the proof of Lemma 5.5 [claim_estimate_remainder_terms],
step by step: the order in which it treats the entries, the uses of the four labels after each
step, the first kind that fits; the rule is valid when the factors satisfy the local conditions,
each entry gets the option of the first kind of its list that fits the uses before it, the entries
with `Λ̃` come first, the uses only grow, and a kind skipped by the rule would overfill a label.
-/

namespace RBMTransitionEdge

deriving instance DecidableEq for FOpt

/-- The order in which `fruleRun` treats the entries (`FEnt.before`, by insertion sort). -/
def fruleOrd (E : List FEnt) : List ℕ :=
  (List.range E.length).insertionSort fun s t =>
    (E.getD s FEnt.dflt).before (E.getD t FEnt.dflt) = true

/-- One step of `fruleRun`: entry `t` takes the first kind of its list that fits. -/
def fruleStep (menu : Bool) (E : List FEnt) (leaf : Bool)
    (st : List ℕ × List (ℕ × ℕ × Option FOpt)) (t : ℕ) :
    List ℕ × List (ℕ × ℕ × Option FOpt) :=
  let d := E.getD t FEnt.dflt
  let os := if menu then d.opts else []
  match (d.prefs leaf).findSome? (fkindFit menu frk st.1 d os) with
  | none => (st.1, (t, 0, fkindOpt d .sup) :: st.2)
  | some (i, o) =>
    let cap := st.1.set d.1 (st.1.getD d.1 0 + o.cx)
    let cap := if d.1 = d.2.1 then cap else cap.set d.2.1 (cap.getD d.2.1 0 + o.cy)
    (cap, (t, i, some o) :: st.2)

/-- `fruleRun` is the fold of `fruleStep` along `fruleOrd`. -/
theorem fruleRun_eq (menu : Bool) (E : List FEnt) (leaf : Bool) :
    fruleRun menu E leaf = (fruleOrd E).foldl (fruleStep menu E leaf) ([0, 0, 0, 0], []) := rfl

/-- The uses of the labels `0, 1, 2, 3` after the first `k` entries of `fruleOrd`. -/
def fruleCap (E : List FEnt) (leaf : Bool) (k : ℕ) : List ℕ :=
  (((fruleOrd E).take k).foldl (fruleStep true E leaf) ([0, 0, 0, 0], [])).1

/-- The first kind of the list of `d` whose option fits the uses `cap` and the order `frk`. -/
def fruleFit (cap : List ℕ) (d : FEnt) (leaf : Bool) : Option (FKind × FOpt) :=
  (d.prefs leaf).findSome? fun k => (fkindFit false frk cap d [] k).map fun p => (k, p.2)

/-- The local conditions of `fvalid`: labels below `4`, block indices below `nb`, no paired letter
in a loop. -/
def fLocal (nb : ℕ) (F : List FFac) : Bool :=
  F.all fun f => match f with
    | .ent x y w => x < 4 && y < 4 && w.all fun z => match z with | .proj u => u < nb | _ => true
    | .loop w => w.all fun z => match z with
        | .proj u => u < nb
        | .det _ pr => !pr
        | _ => true
    | .wt _ u => u < nb

/-- The uses of label `l` by one entry with its option, as counted in `fuses`. -/
def fuseOne (c : FEnt × Option FOpt) (l : ℕ) : ℕ :=
  match c.2 with
  | some o => (if c.1.1 = l then o.cx else 0) + (if c.1.2.1 = l ∧ c.1.1 ≠ l then o.cy else 0)
  | none => 0

open private FO_fchosen from RBMTransitionEdge.Localized.Expansion.FOpts

/-! ## The state of the run -/

/-- The value of a list after `List.set`, read with `getD`. -/
private lemma FRR_setD (c : List ℕ) (i v l : ℕ) :
    (c.set i v).getD l 0 = if i = l ∧ l < c.length then v else c.getD l 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = l
  · subst h
    by_cases h' : i < c.length
    · simp [h']
    · simp [h']
  · simp [h]

/-- The uses after one entry takes an option with uses `a` at `x` and `b` at `y`. -/
private lemma FRR_upd (c : List ℕ) (x y a b l : ℕ) :
    (if x = y then c.set x (c.getD x 0 + a) else
      (c.set x (c.getD x 0 + a)).set y ((c.set x (c.getD x 0 + a)).getD y 0 + b)).getD l 0 =
      c.getD l 0 + (if l < c.length then
        (if x = l then a else 0) + (if y = l ∧ x ≠ l then b else 0) else 0) := by
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte]
    rw [FRR_setD]
    by_cases hl : x = l
    · subst hl
      by_cases h' : x < c.length <;> simp [h']
    · simp [hl]
  · simp only [hxy, ↓reduceIte]
    rw [FRR_setD, FRR_setD, FRR_setD, List.length_set]
    by_cases hl : x = l
    · subst hl
      by_cases h' : x < c.length <;> simp [h', Ne.symm hxy]
    · by_cases hl' : y = l
      · subst hl'
        by_cases h' : y < c.length <;> simp [h', hl]
      · simp [hl, hl']

/-- The length of the uses after one entry takes an option. -/
private lemma FRR_updLen (c : List ℕ) (x y a b : ℕ) :
    (if x = y then c.set x (c.getD x 0 + a) else
      (c.set x (c.getD x 0 + a)).set y ((c.set x (c.getD x 0 + a)).getD y 0 + b)).length =
      c.length := by
  split_ifs <;> simp

/-- With the menu, a kind gives the index of its option in the menu. -/
private lemma FRR_fit_el (rk c : List ℕ) (d : FEnt) (k : FKind) :
    fkindFit true rk c d d.opts k =
      (fkindFit false rk c d [] k).map fun p => (foptIdx d.opts p.2, p.2) := by
  unfold fkindFit
  cases h : fkindOpt d k with
  | none => rfl
  | some o =>
    have hi : foptIdx d.opts o < d.opts.length :=
      (List.getElem?_eq_some_iff.1 (foptIdx_mem _ _ (fkind_mem d k o h))).1
    simp only [↓reduceIte, hi, decide_true, Bool.not_true, Bool.false_or, Bool.true_and,
      Bool.not_false, Bool.true_or, Bool.false_eq_true]
    split_ifs <;> rfl

/-- `findSome?` commutes with a map of the values. -/
private lemma FRR_findSome_map {α β γ : Type*} (f : α → Option β) (g : β → γ) (L : List α) :
    L.findSome? (fun a => (f a).map g) = (L.findSome? f).map g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.findSome?_cons]
    cases f a <;> simp [ih]

/-- The first fitting kind with the menu is `fruleFit`, with the index of its option. -/
private lemma FRR_fit_menu (c : List ℕ) (d : FEnt) (leaf : Bool) :
    (d.prefs leaf).findSome? (fkindFit true frk c d d.opts) =
      (fruleFit c d leaf).map fun q => (foptIdx d.opts q.2, q.2) := by
  unfold fruleFit
  rw [← FRR_findSome_map]
  congr 1
  funext k
  rw [FRR_fit_el, Option.map_map]
  rfl

/-- A step whose entry has no fitting kind. -/
private lemma FRR_step_none (E : List FEnt) (leaf : Bool)
    (st : List ℕ × List (ℕ × ℕ × Option FOpt)) (t : ℕ)
    (h : fruleFit st.1 (E.getD t FEnt.dflt) leaf = none) :
    fruleStep true E leaf st t = (st.1, (t, 0, fkindOpt (E.getD t FEnt.dflt) .sup) :: st.2) := by
  unfold fruleStep
  simp only [↓reduceIte]
  rw [FRR_fit_menu, h]
  rfl

/-- A step whose entry takes the kind `kd` with option `o`. -/
private lemma FRR_step_some (E : List FEnt) (leaf : Bool)
    (st : List ℕ × List (ℕ × ℕ × Option FOpt)) (t : ℕ) (kd : FKind) (o : FOpt)
    (h : fruleFit st.1 (E.getD t FEnt.dflt) leaf = some (kd, o)) :
    (∀ l, (fruleStep true E leaf st t).1.getD l 0 = st.1.getD l 0 +
      (if l < st.1.length then fuseOne (E.getD t FEnt.dflt, some o) l else 0)) ∧
    (fruleStep true E leaf st t).1.length = st.1.length ∧
    (fruleStep true E leaf st t).2 =
      (t, foptIdx (E.getD t FEnt.dflt).opts o, some o) :: st.2 := by
  unfold fruleStep
  simp only [↓reduceIte]
  rw [FRR_fit_menu, h]
  refine ⟨fun l => ?_, FRR_updLen _ _ _ _ _, rfl⟩
  exact FRR_upd _ _ _ _ _ _

/-- The kind `sup` is in every list of kinds. -/
private lemma FRR_sup_mem (d : FEnt) (leaf : Bool) : FKind.sup ∈ d.prefs leaf := by
  unfold FEnt.prefs
  split_ifs <;> simp <;> split_ifs <;> simp

/-- Every kind of `takeWhile (· != a)` of `l₁ ++ a :: l₂` lies in `l₁`. -/
private lemma FRR_takeWhile (l₁ l₂ : List FKind) (a : FKind) :
    ∀ x ∈ (l₁ ++ a :: l₂).takeWhile (fun y => y != a), x ∈ l₁ := by
  induction l₁ with
  | nil => simp
  | cons b l ih =>
    intro x hx
    rw [List.cons_append, List.takeWhile_cons] at hx
    split_ifs at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih x hx)
    · simp at hx

/-- What `fruleFit` returns: a kind of the list, its option, the capacities and the orders that
it checks, and the kinds before it fail. -/
private lemma FRR_fit_spec (c : List ℕ) (d : FEnt) (leaf : Bool) (kd : FKind) (o : FOpt)
    (h : fruleFit c d leaf = some (kd, o)) :
    kd ∈ d.prefs leaf ∧ fkindOpt d kd = some o ∧ c.getD d.1 0 + o.cx ≤ 2 ∧
      (d.1 = d.2.1 ∨ c.getD d.2.1 0 + o.cy ≤ 2) ∧
      (o.ord = 1 → frk.getD d.1 0 < frk.getD d.2.1 0) ∧
      (o.ord = -1 → frk.getD d.2.1 0 < frk.getD d.1 0) ∧
      ∀ k' ∈ (d.prefs leaf).takeWhile (fun k'' => k'' != kd),
        fkindFit false frk c d [] k' = none := by
  obtain ⟨l₁, a, l₂, hl, ha, hn⟩ := List.findSome?_eq_some_iff.1 h
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 ha
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, hpo⟩ := hpe
  refine ⟨hl ▸ List.mem_append_right _ List.mem_cons_self, ?_⟩
  have hw : ∀ k' ∈ (d.prefs leaf).takeWhile (fun k'' => k'' != a),
      fkindFit false frk c d [] k' = none := by
    intro k' hk'
    rw [hl] at hk'
    exact Option.map_eq_none_iff.1 (hn k' (FRR_takeWhile l₁ l₂ a k' hk'))
  unfold fkindFit at hp
  cases hk : fkindOpt d a with
  | none => rw [hk] at hp; exact absurd hp (by simp)
  | some o' =>
    rw [hk] at hp
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.true_and]
      at hp
    split_ifs at hp with hc
    simp only [Option.some.injEq] at hp
    subst hp
    simp only at hpo
    subst hpo
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    refine ⟨rfl, h1, h2, fun h => ?_, fun h => ?_, hw⟩
    · rcases h3 with h3 | h3
      · exact absurd h h3
      · exact h3
    · rcases h4 with h4 | h4
      · exact absurd h h4
      · exact h4

/-- A kind with an option and a compatible order that does not fit overfills a label. -/
private lemma FRR_fit_none (c : List ℕ) (d : FEnt) (k' : FKind) (o' : FOpt)
    (h : fkindFit false frk c d [] k' = none) (ho' : fkindOpt d k' = some o')
    (hord : ((o'.ord != 1 || decide (frk.getD d.1 0 < frk.getD d.2.1 0)) &&
      (o'.ord != -1 || decide (frk.getD d.2.1 0 < frk.getD d.1 0))) = true) :
    2 < c.getD d.1 0 + o'.cx ∨ (d.1 ≠ d.2.1 ∧ 2 < c.getD d.2.1 0 + o'.cy) := by
  unfold fkindFit at h
  rw [ho'] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.true_and] at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc hord
  rcases Nat.lt_or_ge 2 (c.getD d.1 0 + o'.cx) with h1 | h1
  · exact Or.inl h1
  by_cases hxy : d.1 = d.2.1
  · exact absurd ⟨⟨⟨h1, Or.inl hxy⟩, hord.1⟩, hord.2⟩ hc
  rcases Nat.lt_or_ge 2 (c.getD d.2.1 0 + o'.cy) with h2 | h2
  · exact Or.inr ⟨hxy, h2⟩
  · exact absurd ⟨⟨⟨h1, Or.inr h2⟩, hord.1⟩, hord.2⟩ hc

/-- `sup` fits uses at most `2`, so `fruleFit` finds a kind. -/
private lemma FRR_fits (c : List ℕ) (hc : ∀ l, c.getD l 0 ≤ 2) (d : FEnt) (leaf : Bool) :
    (fruleFit c d leaf).isSome = true := by
  unfold fruleFit
  rw [List.findSome?_isSome_iff]
  refine ⟨.sup, FRR_sup_mem d leaf, ?_⟩
  have h1 := hc d.1
  have h2 := hc d.2.1
  rw [List.getD_eq_getElem?_getD] at h1 h2
  simp [fkindFit, fkindOpt, h1, h2]

/-- Each step keeps four labels with uses at most `2`. -/
private lemma FRR_inv (E : List FEnt) (leaf : Bool) :
    ∀ (L : List ℕ) (st : List ℕ × List (ℕ × ℕ × Option FOpt)), st.1.length = 4 →
      (∀ l, st.1.getD l 0 ≤ 2) →
      (L.foldl (fruleStep true E leaf) st).1.length = 4 ∧
        ∀ l, (L.foldl (fruleStep true E leaf) st).1.getD l 0 ≤ 2
  | [], _, h1, h2 => ⟨h1, h2⟩
  | t :: L, st, h1, h2 => by
    rw [List.foldl_cons]
    apply FRR_inv E leaf L
    · cases hf : fruleFit st.1 (E.getD t FEnt.dflt) leaf with
      | none => rw [FRR_step_none E leaf st t hf]; exact h1
      | some q => rw [(FRR_step_some E leaf st t q.1 q.2 hf).2.1]; exact h1
    · intro l
      cases hf : fruleFit st.1 (E.getD t FEnt.dflt) leaf with
      | none => rw [FRR_step_none E leaf st t hf]; exact h2 l
      | some q =>
        rw [(FRR_step_some E leaf st t q.1 q.2 hf).1 l]
        obtain ⟨-, -, hx, hy, -⟩ := FRR_fit_spec _ _ _ _ _ hf
        have hl := h2 l
        simp only [fuseOne]
        generalize E.getD t FEnt.dflt = d at hx hy
        rcases d with ⟨x, y, _⟩
        simp only at hx hy ⊢
        by_cases hxl : x = l
        · subst hxl
          have : ¬ (y = x ∧ x ≠ x) := fun h => h.2 rfl
          simp only [this, ↓reduceIte]
          split_ifs <;> omega
        · by_cases hyl : y = l
          · subst hyl
            have hxy : x ≠ y := hxl
            simp only [hxl, ↓reduceIte, ne_eq, not_false_eq_true, and_self]
            rcases hy with hy | hy
            · exact absurd hy hxy
            · split_ifs <;> omega
          · simp only [hxl, hyl, false_and, ↓reduceIte]
            split_ifs <;> omega

/-- The uses only grow along the run. -/
private lemma FRR_mono (E : List FEnt) (leaf : Bool) (l : ℕ) :
    ∀ (L : List ℕ) (st : List ℕ × List (ℕ × ℕ × Option FOpt)),
      st.1.getD l 0 ≤ (L.foldl (fruleStep true E leaf) st).1.getD l 0
  | [], _ => le_rfl
  | t :: L, st => by
    rw [List.foldl_cons]
    refine le_trans ?_ (FRR_mono E leaf l L _)
    cases hf : fruleFit st.1 (E.getD t FEnt.dflt) leaf with
    | none => rw [FRR_step_none E leaf st t hf]
    | some q =>
      rw [(FRR_step_some E leaf st t q.1 q.2 hf).1 l]
      omega

/-- Each step adds one record, with the index of its entry first. -/
private lemma FRR_snd (E : List FEnt) (leaf : Bool) :
    ∀ (L : List ℕ) (st : List ℕ × List (ℕ × ℕ × Option FOpt)),
      ∃ R : List (ℕ × ℕ × Option FOpt), (L.foldl (fruleStep true E leaf) st).2 = R ++ st.2 ∧
        R.map Prod.fst = L.reverse
  | [], _ => ⟨[], rfl, rfl⟩
  | t :: L, st => by
    rw [List.foldl_cons]
    obtain ⟨r, hr⟩ : ∃ r : ℕ × Option FOpt, (fruleStep true E leaf st t).2 = (t, r) :: st.2 := by
      cases hf : fruleFit st.1 (E.getD t FEnt.dflt) leaf with
      | none => exact ⟨_, by rw [FRR_step_none E leaf st t hf]⟩
      | some q => exact ⟨_, (FRR_step_some E leaf st t q.1 q.2 hf).2.2⟩
    obtain ⟨R, h1, h2⟩ := FRR_snd E leaf L (fruleStep true E leaf st t)
    refine ⟨R ++ [(t, r)], ?_, ?_⟩
    · rw [h1, hr, List.append_assoc]
      rfl
    · simp [h2]

/-! ## The order of the run -/

/-- `fListLe` is total. -/
private lemma FRR_le_total : ∀ s t : List ℕ, fListLe s t = true ∨ fListLe t s = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: s, b :: t => by
    simp only [fListLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rcases lt_trichotomy a b with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases FRR_le_total s t with h | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl h)

/-- `fListLe` is transitive. -/
private lemma FRR_le_trans : ∀ s t u : List ℕ,
    fListLe s t = true → fListLe t u = true → fListLe s u = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [fListLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [fListLe] at h
  | a :: s, b :: t, c :: u, h1, h2 => by
    simp only [fListLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, FRR_le_trans s t u h1 h2⟩

/-- `FEnt.before` is total. -/
private lemma FRR_before_total (d e : FEnt) : d.before e = true ∨ e.before d = true := by
  have T := FRR_le_total d.2.2.1 e.2.2.1
  unfold FEnt.before
  revert T
  generalize fListLe d.2.2.1 e.2.2.1 = p
  generalize fListLe e.2.2.1 d.2.2.1 = q
  cases p <;> cases q <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
      and_false, and_true, or_false, or_true, forall_const, false_implies] <;> omega

/-- `FEnt.before` is transitive. -/
private lemma FRR_before_trans (a b c : FEnt) (h1 : a.before b = true) (h2 : b.before c = true) :
    a.before c = true := by
  have T := FRR_le_trans a.2.2.1 b.2.2.1 c.2.2.1
  unfold FEnt.before at *
  revert T h1 h2
  generalize fListLe a.2.2.1 b.2.2.1 = p
  generalize fListLe b.2.2.1 c.2.2.1 = q
  generalize fListLe a.2.2.1 c.2.2.1 = r
  cases p <;> cases q <;> cases r <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
      and_false, and_true, or_false, forall_const, IsEmpty.forall_iff] <;> intros <;>
    first | omega | trivial

/-- `fruleOrd` is a permutation of the indices. -/
private lemma FRR_perm (E : List FEnt) : (fruleOrd E).Perm (List.range E.length) :=
  List.perm_insertionSort _ _

/-- `fruleOrd` has no repeated index. -/
private lemma FRR_nodup (E : List FEnt) : (fruleOrd E).Nodup :=
  (FRR_perm E).nodup_iff.2 List.nodup_range

/-- `fruleOrd` has length `|E|`. -/
private lemma FRR_len (E : List FEnt) : (fruleOrd E).length = E.length := by
  rw [(FRR_perm E).length_eq, List.length_range]

/-- An index of `fruleOrd` is an index of `E`. -/
private lemma FRR_lt (E : List FEnt) (k t : ℕ) (ht : (fruleOrd E)[k]? = some t) :
    t < E.length := by
  have hm : t ∈ fruleOrd E := List.mem_of_getElem? ht
  rw [(FRR_perm E).mem_iff, List.mem_range] at hm
  exact hm

/-- Every index of `E` is treated at some step. -/
private lemma FRR_step_of (E : List FEnt) (t : ℕ) (ht : t < E.length) :
    ∃ k : ℕ, (fruleOrd E)[k]? = some t := by
  have hm : t ∈ fruleOrd E := (FRR_perm E).mem_iff.2 (List.mem_range.2 ht)
  exact List.mem_iff_getElem?.1 hm

/-! ## The records of the run -/

/-- The record of the entry treated at step `k` is the one this step adds. -/
private lemma FRR_find (E : List FEnt) (leaf : Bool) (k t : ℕ)
    (ht : (fruleOrd E)[k]? = some t) :
    (fruleRun true E leaf).2.find? (fun p => decide (p.1 = t)) =
      (fruleStep true E leaf (((fruleOrd E).take k).foldl (fruleStep true E leaf)
        ([0, 0, 0, 0], [])) t).2.head? := by
  obtain ⟨hk, hkt⟩ := List.getElem?_eq_some_iff.1 ht
  have hdrop := List.drop_eq_getElem_cons hk
  rw [hkt] at hdrop
  have hnd : t ∉ (fruleOrd E).drop (k + 1) := by
    have := (FRR_nodup E).sublist (List.drop_sublist k _)
    rw [hdrop] at this
    exact (List.nodup_cons.1 this).1
  have hsplit : fruleOrd E = (fruleOrd E).take k ++ t :: (fruleOrd E).drop (k + 1) := by
    rw [← hdrop, List.take_append_drop]
  rw [fruleRun_eq]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  generalize ((fruleOrd E).take k).foldl (fruleStep true E leaf) ([0, 0, 0, 0], []) = S
  obtain ⟨r, hr⟩ : ∃ r : ℕ × Option FOpt, (fruleStep true E leaf S t).2 = (t, r) :: S.2 := by
    cases hf : fruleFit S.1 (E.getD t FEnt.dflt) leaf with
    | none => exact ⟨_, by rw [FRR_step_none E leaf S t hf]⟩
    | some q => exact ⟨_, (FRR_step_some E leaf S t q.1 q.2 hf).2.2⟩
  obtain ⟨R, h1, h2⟩ := FRR_snd E leaf ((fruleOrd E).drop (k + 1)) (fruleStep true E leaf S t)
  rw [h1, hr, List.find?_append]
  have hR : R.find? (fun p => decide (p.1 = t)) = none := by
    rw [List.find?_eq_none]
    intro x hx hxt
    apply hnd
    have : x.1 ∈ R.map Prod.fst := List.mem_map_of_mem hx
    rw [h2, List.mem_reverse] at this
    simpa using (decide_eq_true_iff.1 hxt) ▸ this
  rw [hR]
  simp

/-- The option index of `fruleE` at the entry treated at step `k`. -/
private lemma FRR_E (E : List FEnt) (leaf : Bool) (k t : ℕ) (ht : (fruleOrd E)[k]? = some t)
    (kd : FKind) (o : FOpt)
    (hfit : fruleFit (fruleCap E leaf k) (E.getD t FEnt.dflt) leaf = some (kd, o)) :
    (fruleE E leaf).getD t 0 = foptIdx (E.getD t FEnt.dflt).opts o := by
  have hlt := FRR_lt E k t ht
  unfold fruleE
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  rw [FRR_find E leaf k t ht, (FRR_step_some E leaf _ t kd o hfit).2.2]
  rfl

/-- The entry treated at step `k` gets the option of its first fitting kind. -/
private lemma FRR_chosen (F : List FFac) (leaf : Bool) (k t : ℕ) (d : FEnt)
    (ht : (fruleOrd (F.filterMap FFac.entData))[k]? = some t)
    (hd : (F.filterMap FFac.entData)[t]? = some d) (kd : FKind) (o : FOpt)
    (hfit : fruleFit (fruleCap (F.filterMap FFac.entData) leaf k) d leaf = some (kd, o)) :
    (fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩)[t]? = some (d, some o) := by
  have hdD : (F.filterMap FFac.entData).getD t FEnt.dflt = d := by
    rw [List.getD_eq_getElem?_getD, hd]
    rfl
  rw [FO_fchosen, List.getElem?_mapIdx, hd]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  rw [FRR_E _ leaf k t ht kd o (hdD ▸ hfit), hdD]
  exact foptIdx_mem _ _ (fkind_mem d kd o (FRR_fit_spec _ _ _ _ _ hfit).2.1)

/-- The uses after `k` steps: four labels, each used at most twice. -/
private lemma FRR_capInv (E : List FEnt) (leaf : Bool) (k : ℕ) :
    (fruleCap E leaf k).length = 4 ∧ ∀ l, (fruleCap E leaf k).getD l 0 ≤ 2 :=
  FRR_inv E leaf _ _ rfl fun l => by
    rw [List.getD_eq_getElem?_getD]
    rcases l with _ | _ | _ | _ | l <;> simp

/-- Every entry of `fchosen` is the entry treated at some step, with the option of its first
fitting kind. -/
private lemma FRR_all (F : List FFac) (leaf : Bool)
    (c : FEnt × Option FOpt) (hc : c ∈ fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩) :
    ∃ k t d kd o, (fruleOrd (F.filterMap FFac.entData))[k]? = some t ∧
      (F.filterMap FFac.entData)[t]? = some d ∧
      fruleFit (fruleCap (F.filterMap FFac.entData) leaf k) d leaf = some (kd, o) ∧
      c = (d, some o) := by
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hc
  have ht' := ht
  rw [FO_fchosen, List.getElem?_mapIdx] at ht'
  obtain ⟨d, hd, -⟩ := Option.map_eq_some_iff.1 ht'
  obtain ⟨k, hk⟩ := FRR_step_of _ t (List.getElem?_eq_some_iff.1 hd).1
  obtain ⟨⟨kd, o⟩, hfit⟩ := Option.isSome_iff_exists.1
    (FRR_fits _ (FRR_capInv (F.filterMap FFac.entData) leaf k).2 d leaf)
  refine ⟨k, t, d, kd, o, hk, hd, hfit, ?_⟩
  rw [FRR_chosen F leaf k t d hk hd kd o hfit] at ht
  exact (Option.some.inj ht).symm

/-! ## The uses along the run -/

/-- A sum over a list is the sum over its indices. -/
private lemma FRR_sum_idx {α : Type*} (C : List α) (f : α → ℕ) :
    (C.map f).sum = ((List.range C.length).map fun t => ((C[t]?).map f).getD 0).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getElem?_eq_getElem (by simpa using h1)]
  rfl

/-- The uses after `k` steps are the uses of the options of the first `k` entries. -/
private lemma FRR_cap (F : List FFac) (leaf : Bool) (k l : ℕ) (hl : l < 4) :
    (fruleCap (F.filterMap FFac.entData) leaf k).getD l 0 =
      (((fruleOrd (F.filterMap FFac.entData)).take k).map fun t =>
        (((fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩)[t]?).map
          fun c => fuseOne c l).getD 0).sum := by
  induction k with
  | zero =>
    simp only [fruleCap, List.take_zero, List.foldl_nil, List.map_nil, List.sum_nil]
    rw [List.getD_eq_getElem?_getD]
    rcases l with _ | _ | _ | _ | l <;> simp
  | succ k ih =>
    have hlen := (FRR_capInv (F.filterMap FFac.entData) leaf k).1
    unfold fruleCap at ih hlen ⊢
    rw [List.take_add_one]
    cases hk : (fruleOrd (F.filterMap FFac.entData))[k]? with
    | none => simpa using ih
    | some t =>
      have hlt := FRR_lt _ k t hk
      obtain ⟨d, hd⟩ : ∃ d, (F.filterMap FFac.entData)[t]? = some d :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hdD : (F.filterMap FFac.entData).getD t FEnt.dflt = d := by
        rw [List.getD_eq_getElem?_getD, hd]
        rfl
      obtain ⟨⟨kd, o⟩, hfit⟩ := Option.isSome_iff_exists.1
        (FRR_fits _ (FRR_capInv (F.filterMap FFac.entData) leaf k).2 d leaf)
      have hs := FRR_step_some (F.filterMap FFac.entData) leaf _ t kd o (hdD ▸ hfit)
      simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, add_zero]
      rw [hs.1 l, ih, hlen, FRR_chosen F leaf k t d hk hd kd o hfit, hdD]
      simp only [hl, ↓reduceIte, Option.map_some, Option.getD_some]

/-- `fuses` is the final value of the uses. -/
private lemma FRR_uses (F : List FFac) (leaf : Bool) (l : ℕ) (hl : l < 4) :
    fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ l =
      (fruleCap (F.filterMap FFac.entData) leaf (F.filterMap FFac.entData).length).getD l 0 := by
  rw [FRR_cap F leaf _ l hl, List.take_of_length_le (le_of_eq (FRR_len _)),
    ((FRR_perm _).map _).sum_eq]
  unfold fuses
  rw [FRR_sum_idx]
  have hlen : (fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩).length =
      (F.filterMap FFac.entData).length := by
    rw [FO_fchosen, List.length_mapIdx]
  rw [hlen]
  rfl

/-- `FEnt.before` puts the roles in order. -/
private lemma FRR_before_role (d e : FEnt) (h : d.before e = true) : d.role ≤ e.role := by
  unfold FEnt.before at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h, -⟩ <;> omega

/-- Q0 (a): the rule is valid when the factors satisfy the local conditions. -/
theorem frule_run_valid (nb : ℕ) (F : List FFac) (leaf : Bool) (hF : fLocal nb F = true) :
    fvalid nb F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ = true := by
  rw [fvalid_eq]
  simp only [fvalidL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨rfl, by simp [fruleE]⟩, ?_⟩, ?_⟩, ?_⟩
  · intro f hf
    exact List.all_eq_true.1 hF f hf
  · intro c hc
    obtain ⟨k, t, d, kd, o, -, -, hfit, rfl⟩ := FRR_all F leaf c hc
    obtain ⟨-, -, -, -, h1, h2, -⟩ := FRR_fit_spec _ _ _ _ _ hfit
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨(em (o.ord = 1)).elim (fun h => Or.inr (h1 h)) Or.inl,
      (em (o.ord = -1)).elim (fun h => Or.inr (h2 h)) Or.inl⟩
  · intro l hl
    rw [FRR_uses F leaf l (List.mem_range.1 hl)]
    exact (FRR_capInv _ leaf _).2 l

/-- Q0 (b): every entry has an option (the hypothesis of `fboundM_mem`). -/
theorem frule_run_some (F : List FFac) (leaf : Bool) :
    ∀ c ∈ fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩, c.2.isSome = true := by
  intro c hc
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := FRR_all F leaf c hc
  rfl

/-- Q0 (b): the entry treated at step `k` has a fitting kind. -/
theorem frule_run_fits (F : List FFac) (leaf : Bool) (k t : ℕ) (d : FEnt)
    (ht : (fruleOrd (F.filterMap FFac.entData))[k]? = some t)
    (hd : (F.filterMap FFac.entData)[t]? = some d) :
    (fruleFit (fruleCap (F.filterMap FFac.entData) leaf k) d leaf).isSome = true := by
  exact (fun _ _ => FRR_fits _ (FRR_capInv _ leaf k).2 d leaf) ht hd

/-- Q0 (b): the option of the entry treated at step `k` is that of the first kind of its list
that fits the uses of the entries treated before it; the kind is in the list. -/
theorem frule_run_chosen (F : List FFac) (leaf : Bool) (k t : ℕ) (d : FEnt)
    (ht : (fruleOrd (F.filterMap FFac.entData))[k]? = some t)
    (hd : (F.filterMap FFac.entData)[t]? = some d) (kd : FKind) (o : FOpt)
    (hfit : fruleFit (fruleCap (F.filterMap FFac.entData) leaf k) d leaf = some (kd, o)) :
    kd ∈ d.prefs leaf ∧ fkindOpt d kd = some o ∧
      (fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩)[t]? = some (d, some o) := by
  obtain ⟨h1, h2, -⟩ := FRR_fit_spec _ _ _ _ _ hfit
  exact ⟨h1, h2, FRR_chosen F leaf k t d ht hd kd o hfit⟩

/-- Q0 (b): the uses after `k` steps are the uses of the options of the first `k` entries. -/
theorem frule_run_cap (F : List FFac) (leaf : Bool) (k l : ℕ) (hl : l < 4) :
    (fruleCap (F.filterMap FFac.entData) leaf k).getD l 0 =
      (((fruleOrd (F.filterMap FFac.entData)).take k).map fun t =>
        (((fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩)[t]?).map
          fun c => fuseOne c l).getD 0).sum := by
  exact FRR_cap F leaf k l hl

/-- Q0 (b): `fuses` is the final value of the uses. -/
theorem frule_run_uses (F : List FFac) (leaf : Bool) (l : ℕ) (hl : l < 4) :
    fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ l =
      (fruleCap (F.filterMap FFac.entData) leaf (F.filterMap FFac.entData).length).getD l 0 := by
  exact FRR_uses F leaf l hl

/-- Q0 (c): `fruleOrd` is a permutation of the indices, nondecreasing in `FEnt.role`. -/
theorem frule_run_order (E : List FEnt) :
    (fruleOrd E).Perm (List.range E.length) ∧
      (fruleOrd E).Pairwise fun s t => (E.getD s FEnt.dflt).role ≤ (E.getD t FEnt.dflt).role := by
  refine ⟨FRR_perm E, ?_⟩
  have hp := @List.pairwise_insertionSort ℕ
    (fun s t => (E.getD s FEnt.dflt).before (E.getD t FEnt.dflt) = true) _
    ⟨fun _ _ => FRR_before_total _ _⟩ ⟨fun _ _ _ => FRR_before_trans _ _ _⟩ (List.range E.length)
  exact hp.imp fun h => FRR_before_role _ _ h

/-- Q0 (c): the uses start at `0` and only grow. -/
theorem frule_run_mono (E : List FEnt) (leaf : Bool) (k k' l : ℕ) (h : k ≤ k') :
    fruleCap E leaf 0 = [0, 0, 0, 0] ∧ (fruleCap E leaf k).length = 4 ∧
      (fruleCap E leaf k).getD l 0 ≤ (fruleCap E leaf k').getD l 0 := by
  refine ⟨rfl, (FRR_capInv E leaf k).1, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold fruleCap
  rw [List.take_add, List.foldl_append]
  exact FRR_mono E leaf l _ _

/-- Q0 (d), saturation: a kind before the chosen one whose order agrees with `frk` would overfill
a label at the end of the run. -/
theorem frule_run_sat (F : List FFac) (leaf : Bool) (k t : ℕ) (d : FEnt)
    (ht : (fruleOrd (F.filterMap FFac.entData))[k]? = some t)
    (hd : (F.filterMap FFac.entData)[t]? = some d) (kd : FKind) (o : FOpt)
    (hfit : fruleFit (fruleCap (F.filterMap FFac.entData) leaf k) d leaf = some (kd, o))
    (k' : FKind) (hk' : k' ∈ (d.prefs leaf).takeWhile fun k'' => k'' != kd) (o' : FOpt)
    (ho' : fkindOpt d k' = some o')
    (hord : ((o'.ord != 1 || decide (frk.getD d.1 0 < frk.getD d.2.1 0)) &&
      (o'.ord != -1 || decide (frk.getD d.2.1 0 < frk.getD d.1 0))) = true) :
    2 < fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ d.1 + o'.cx ∨
      (d.1 ≠ d.2.1 ∧ 2 < fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ d.2.1 + o'.cy) := by
  refine (fun (_ : (F.filterMap FFac.entData)[t]? = some d) => ?_) hd
  obtain ⟨-, -, -, -, -, -, hw⟩ := FRR_fit_spec _ _ _ _ _ hfit
  have hn := FRR_fit_none _ d k' o' (hw k' hk') ho' hord
  have hle : ∀ z, (fruleCap (F.filterMap FFac.entData) leaf k).getD z 0 ≤
      fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ z := by
    intro z
    by_cases hz : z < 4
    · rw [frule_run_uses F leaf z hz]
      have hk : k ≤ (F.filterMap FFac.entData).length := by
        have := (List.getElem?_eq_some_iff.1 ht).1
        rw [FRR_len] at this
        omega
      exact (frule_run_mono _ leaf k _ z hk).2.2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [(FRR_capInv _ leaf k).1]; omega)]
      simp
  rcases hn with h | ⟨hne, h⟩
  · exact Or.inl (by have := hle d.1; omega)
  · exact Or.inr ⟨hne, by have := hle d.2.1; omega⟩

end RBMTransitionEdge
