module

public import RBMTransitionEdge.Localized.Expansion.FRuleRun
public import RBMTransitionEdge.Localized.Expansion.FOpts
import all RBMTransitionEdge.Localized.Expansion.FOpts
import all RBMTransitionEdge.Localized.Expansion.FRuleRun

@[expose] public section

/-!
# The Ward count of the run of the rule

The run of the rule of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms] on a factor list: the designated label of an entry with one part
and its Ward use there or a full label; the lower bound `ω ≥ Σ_ℓ min(N_ℓ, 2 - u_ℓ)` on the number
of Ward uses; the uses of the four labels split into those of the entries with at least two parts
and the Ward uses; and the ends of the entries with one part counted by pairs of labels (the
role-2 Ward uses of Example 5.7 [example_estimate_reminder_reminder_terms] and the companion
cases (1)–(3)).
-/

namespace RBMTransitionEdge

/-- The entries of a factor list with the options chosen by the run of the rule of the further
expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms] (`leaf = false`: the rule
`frule`; `leaf = true`: the rule of the further terminal cases). -/
def fruleC (F : List FFac) (leaf : Bool) : List (FEnt × Option FOpt) :=
  fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩

/-- The designated label of an entry with two labels, in the run of the rule of the proof of
Lemma 5.5 [claim_estimate_remainder_terms]: the label of smaller rank in `frk`, the only label at
which the run can give the entry its Ward use (Example 5.7
[example_estimate_reminder_reminder_terms]). -/
def fwardLab (d : FEnt) : ℕ :=
  if frk.getD d.1 0 < frk.getD d.2.1 0 then d.1 else d.2.1

/-- The number `ω` of entries with one part that take a Ward use, in the run of the rule of the
proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def fwardW (F : List FFac) (leaf : Bool) : ℕ :=
  (fruleC F leaf).countP fun c => decide (c.1.2.2.1.length ≤ 1) &&
    (match c.2 with
      | some o => o.cx + o.cy == 1
      | none => false)

/-- The number `N_ℓ` of entries with one part, two different labels below `4` and designated label
`ℓ`, in the run of the rule of the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def fwardN (F : List FFac) (leaf : Bool) (l : ℕ) : ℕ :=
  (fruleC F leaf).countP fun c => decide (c.1.2.2.1.length ≤ 1 ∧ c.1.1 ≠ c.1.2.1 ∧ c.1.1 < 4 ∧
    c.1.2.1 < 4 ∧ fwardLab c.1 = l)

/-- The uses `u_ℓ` of label `ℓ` by the entries with at least two parts, in the run of the rule of
the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def fwardU (F : List FFac) (leaf : Bool) (l : ℕ) : ℕ :=
  (((fruleC F leaf).filter fun c => decide (2 ≤ c.1.2.2.1.length)).map fun c => fuseOne c l).sum

/-- The number `e_ℓ` of ends at label `ℓ` of the entries with one part, in the run of the rule of
the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def fwardE (F : List FFac) (leaf : Bool) (l : ℕ) : ℕ :=
  (((fruleC F leaf).filter fun c => decide (c.1.2.2.1.length ≤ 1)).map fun c =>
    (if c.1.1 = l then 1 else 0) + (if c.1.2.1 = l then 1 else 0)).sum

/-- The number `c_{ab}` of entries with one part and the labels `{a, b}`, in the run of the rule
of the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def fwardC (F : List FFac) (leaf : Bool) (a b : ℕ) : ℕ :=
  (fruleC F leaf).countP fun c => decide (c.1.2.2.1.length ≤ 1 ∧
    ((c.1.1 = a ∧ c.1.2.1 = b) ∨ (c.1.1 = b ∧ c.1.2.1 = a)))

open private FO_fchosen from RBMTransitionEdge.Localized.Expansion.FOpts
open private FRR_fit_spec FRR_capInv FRR_all from RBMTransitionEdge.Localized.Expansion.FRuleRun

/-! ## Sums over lists -/

/-- A count is a sum of indicators. -/
private lemma FRW_countP {α : Type*} (C : List α) (p : α → Bool) :
    C.countP p = (C.map fun c => if p c then 1 else 0).sum := by
  induction C with
  | nil => rfl
  | cons a C ih =>
    rw [List.countP_cons, ih, List.map_cons, List.sum_cons]
    omega

/-- A sum over a filtered list is a sum of the values on the kept elements. -/
private lemma FRW_filter {α : Type*} (C : List α) (q : α → Bool) (f : α → ℕ) :
    ((C.filter q).map f).sum = (C.map fun c => if q c then f c else 0).sum := by
  induction C with
  | nil => rfl
  | cons a C ih =>
    by_cases h : q a = true
    · simp [h, ih]
    · simp [h, ih]

/-- Two sums commute. -/
private lemma FRW_comm {α : Type*} (L : List ℕ) (C : List α) (φ : ℕ → α → ℕ) :
    (L.map fun l => (C.map (φ l)).sum).sum = (C.map fun c => (L.map fun l => φ l c).sum).sum := by
  induction C with
  | nil => simp
  | cons a C ih => simp [List.sum_map_add, ih]

/-- A sum is monotone in its terms. -/
private lemma FRW_le {α : Type*} (C : List α) (f g : α → ℕ) (h : ∀ c ∈ C, f c ≤ g c) :
    (C.map f).sum ≤ (C.map g).sum := by
  induction C with
  | nil => exact le_rfl
  | cons a C ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (ih fun c hc => h c (List.mem_cons_of_mem a hc))

/-- A sum depends only on its terms. -/
private lemma FRW_eq {α : Type*} (C : List α) (f g : α → ℕ) (h : ∀ c ∈ C, f c = g c) :
    (C.map f).sum = (C.map g).sum := by
  rw [List.map_congr_left h]

/-- A sum over the four labels. -/
private lemma FRW_r4 (f : ℕ → ℕ) : ((List.range 4).map f).sum = f 0 + f 1 + f 2 + f 3 := by
  simp [List.range_succ, Nat.add_assoc]

/-! ## The options of an entry with one part -/

/-- The kinds tried for an entry with one part: sup alone on the diagonal, otherwise its Ward
kinds by blocks and then sup. -/
private lemma FRW_prefs (d : FEnt) (leaf : Bool) (hP : d.2.2.1.length ≤ 1) :
    d.prefs leaf = if d.1 = d.2.1 then [.sup] else
      (if fInnerL d.1 && !fInnerL d.2.1 then [.wardX]
       else if fInnerL d.2.1 && !fInnerL d.1 then [.wardY]
       else [.wardX, .wardY]) ++ [.sup] := by
  have h0 : d.2.2.1.length - 1 = 0 := by omega
  unfold FEnt.prefs
  simp only [h0]
  split_ifs <;> simp_all

/-- The kind taken by an entry with one part: sup with no use, a Ward row with one use at the row
label and order `1`, or a Ward column with one use at the column label and order `-1`. -/
private lemma FRW_kinds (d : FEnt) (leaf : Bool) (hP : d.2.2.1.length ≤ 1) (kd : FKind)
    (hk : kd ∈ d.prefs leaf) (o : FOpt) (ho : fkindOpt d kd = some o) :
    (kd = .sup ∧ o.cx = 0 ∧ o.cy = 0) ∨
      (d.1 ≠ d.2.1 ∧ kd = .wardX ∧ o.cx = 1 ∧ o.cy = 0 ∧ o.ord = 1) ∨
      (d.1 ≠ d.2.1 ∧ kd = .wardY ∧ o.cx = 0 ∧ o.cy = 1 ∧ o.ord = -1) := by
  rw [FRW_prefs d leaf hP] at hk
  have hsup : kd = .sup → (kd = .sup ∧ o.cx = 0 ∧ o.cy = 0) := by
    rintro rfl
    simp only [fkindOpt, Option.some.injEq] at ho
    subst ho
    exact ⟨rfl, rfl, rfl⟩
  have hX : d.1 ≠ d.2.1 → kd = .wardX → (d.1 ≠ d.2.1 ∧ kd = .wardX ∧ o.cx = 1 ∧ o.cy = 0 ∧
      o.ord = 1) := by
    rintro hxy rfl
    simp only [fkindOpt, hxy, ↓reduceIte, Option.some.injEq] at ho
    subst ho
    exact ⟨hxy, rfl, rfl, rfl, rfl⟩
  have hY : d.1 ≠ d.2.1 → kd = .wardY → (d.1 ≠ d.2.1 ∧ kd = .wardY ∧ o.cx = 0 ∧ o.cy = 1 ∧
      o.ord = -1) := by
    rintro hxy rfl
    simp only [fkindOpt, hxy, ↓reduceIte, Option.some.injEq] at ho
    subst ho
    exact ⟨hxy, rfl, rfl, rfl, rfl⟩
  by_cases hxy : d.1 = d.2.1
  · simp only [hxy, ↓reduceIte] at hk
    exact Or.inl (hsup (List.mem_singleton.1 hk))
  · simp only [hxy, ↓reduceIte] at hk
    have hk' : kd = .wardX ∨ kd = .wardY ∨ kd = .sup := by
      split_ifs at hk <;> simp at hk <;> tauto
    rcases hk' with hk' | hk' | hk'
    · exact Or.inr (Or.inl (hX hxy hk'))
    · exact Or.inr (Or.inr (hY hxy hk'))
    · exact Or.inl (hsup hk')

/-- The ranks of `frk` are different on two different labels below `4`. -/
private lemma FRW_rk_ne (x y : ℕ) (hx : x < 4) (hy : y < 4) (hxy : x ≠ y) :
    frk.getD x 0 ≠ frk.getD y 0 := by
  interval_cases x <;> interval_cases y <;> first | exact absurd rfl hxy | decide

/-- The Ward kind at the designated label is tried before sup. -/
private lemma FRW_kappa (d : FEnt) (leaf : Bool) (hP : d.2.2.1.length ≤ 1) (hxy : d.1 ≠ d.2.1)
    (hx : d.1 < 4) (hy : d.2.1 < 4) :
    (if frk.getD d.1 0 < frk.getD d.2.1 0 then FKind.wardX else FKind.wardY) ∈
      (d.prefs leaf).takeWhile fun k => k != .sup := by
  rw [FRW_prefs d leaf hP]
  simp only [hxy, ↓reduceIte]
  obtain ⟨x, y, r⟩ := d
  simp only at hx hy hxy ⊢
  interval_cases x <;> interval_cases y <;> first | exact absurd rfl hxy | simp [frk, fInnerL]

/-- Every chosen entry is an entry of the factor list with the option of a kind of its list,
whose order agrees with `frk`. -/
private lemma FRW_entry (F : List FFac) (leaf : Bool) (c : FEnt × Option FOpt)
    (hc : c ∈ fruleC F leaf) :
    ∃ d o kd, c = (d, some o) ∧ d ∈ F.filterMap FFac.entData ∧ kd ∈ d.prefs leaf ∧
      fkindOpt d kd = some o ∧ (o.ord = 1 → frk.getD d.1 0 < frk.getD d.2.1 0) ∧
      (o.ord = -1 → frk.getD d.2.1 0 < frk.getD d.1 0) := by
  obtain ⟨k, t, d, kd, o, -, hd, hfit, rfl⟩ := FRR_all F leaf c hc
  obtain ⟨h1, h2, -, -, h5, h6, -⟩ := FRR_fit_spec _ _ _ _ _ hfit
  exact ⟨d, o, kd, rfl, List.mem_of_getElem? hd, h1, h2, h5, h6⟩

/-- A chosen entry with one part uses no label, or one label of its own once. -/
private lemma FRW_one (F : List FFac) (leaf : Bool) (c : FEnt × Option FOpt)
    (hc : c ∈ fruleC F leaf) (hP : c.1.2.2.1.length ≤ 1) :
    ∃ o, c.2 = some o ∧ ((o.cx + o.cy = 0 ∧ ∀ l, fuseOne c l = 0) ∨
      (o.cx + o.cy = 1 ∧ ∃ z, (z = c.1.1 ∨ z = c.1.2.1) ∧
        ∀ l, fuseOne c l = if z = l then 1 else 0)) := by
  obtain ⟨d, o, kd, rfl, -, hk, ho, -, -⟩ := FRW_entry F leaf c hc
  refine ⟨o, rfl, ?_⟩
  rcases FRW_kinds d leaf hP kd hk o ho with ⟨-, h1, h2⟩ | ⟨hxy, -, h1, h2, -⟩ |
      ⟨hxy, -, h1, h2, -⟩
  · refine Or.inl ⟨by omega, fun l => ?_⟩
    simp [fuseOne, h1, h2]
  · refine Or.inr ⟨by omega, d.1, Or.inl rfl, fun l => ?_⟩
    simp only [fuseOne, h1, h2]
    split_ifs <;> omega
  · refine Or.inr ⟨by omega, d.2.1, Or.inr rfl, fun l => ?_⟩
    simp only [fuseOne, h1, h2]
    split_ifs <;> omega

/-- The indicator of one label, summed over the four labels. -/
private lemma FRW_ind (z : ℕ) :
    ((List.range 4).map fun l => if z = l then 1 else 0).sum = if z < 4 then 1 else 0 := by
  rw [FRW_r4]
  split_ifs <;> omega

/-- The uses of the four labels by a chosen entry with one part: at most one, and exactly one for
a Ward use when its labels are below `4`. -/
private lemma FRW_one_sum (F : List FFac) (leaf : Bool) (c : FEnt × Option FOpt)
    (hc : c ∈ fruleC F leaf) (hP : c.1.2.2.1.length ≤ 1) :
    ((List.range 4).map fun l => fuseOne c l).sum ≤
        (if (match c.2 with
          | some o => o.cx + o.cy == 1
          | none => false) = true then 1 else 0) ∧
      (c.1.1 < 4 → c.1.2.1 < 4 → ((List.range 4).map fun l => fuseOne c l).sum =
        (if (match c.2 with
          | some o => o.cx + o.cy == 1
          | none => false) = true then 1 else 0)) := by
  obtain ⟨o, ho, ⟨h0, hu⟩ | ⟨h1, z, hz, hu⟩⟩ := FRW_one F leaf c hc hP
  · have hs : ((List.range 4).map fun l => fuseOne c l).sum = 0 := by simp [hu]
    rw [hs, ho]
    simp [h0]
  · have hs : ((List.range 4).map fun l => fuseOne c l).sum = if z < 4 then 1 else 0 := by
      rw [← FRW_ind]
      simp only [hu]
    rw [hs, ho]
    simp only [h1, beq_self_eq_true, ↓reduceIte]
    refine ⟨by split_ifs <;> omega, fun hx hy => ?_⟩
    rcases hz with rfl | rfl <;> simp [hx, hy]

/-! ## The uses of a label -/

/-- The uses `ω_ℓ` of label `ℓ` by the entries with one part. -/
private def FRW_om (F : List FFac) (leaf : Bool) (l : ℕ) : ℕ :=
  (((fruleC F leaf).filter fun c => decide (c.1.2.2.1.length ≤ 1)).map fun c => fuseOne c l).sum

/-- The uses of a label split into those of the entries with at least two parts and those of the
entries with one part. -/
private lemma FRW_split (F : List FFac) (leaf : Bool) (l : ℕ) :
    fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ l =
      fwardU F leaf l + FRW_om F leaf l := by
  have hf : fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ l =
      ((fruleC F leaf).map fun c => fuseOne c l).sum := rfl
  rw [hf, fwardU, FRW_om, FRW_filter, FRW_filter, ← List.sum_map_add]
  refine FRW_eq _ _ _ fun c _ => ?_
  by_cases h : 2 ≤ c.1.2.2.1.length
  · have h' : ¬ c.1.2.2.1.length ≤ 1 := by omega
    simp [h, h']
  · have h' : c.1.2.2.1.length ≤ 1 := by omega
    simp [h, h']

/-- The uses of the four labels by the entries with one part, against the number of Ward uses:
at most `ω`, and `ω` when every label is below `4`. -/
private lemma FRW_om_sum (F : List FFac) (leaf : Bool) :
    ((List.range 4).map fun l => FRW_om F leaf l).sum ≤ fwardW F leaf ∧
      ((∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4) →
        ((List.range 4).map fun l => FRW_om F leaf l).sum = fwardW F leaf) := by
  have hL : ((List.range 4).map fun l => FRW_om F leaf l).sum =
      ((fruleC F leaf).map fun c => if decide (c.1.2.2.1.length ≤ 1) = true then
        ((List.range 4).map fun l => fuseOne c l).sum else 0).sum := by
    simp only [FRW_om, FRW_filter]
    rw [FRW_comm]
    refine FRW_eq _ _ _ fun c _ => ?_
    split_ifs <;> simp
  have hW : fwardW F leaf = ((fruleC F leaf).map fun c => if decide (c.1.2.2.1.length ≤ 1) = true
      then (if (match c.2 with
          | some o => o.cx + o.cy == 1
          | none => false) = true then 1 else 0) else 0).sum := by
    rw [fwardW, FRW_countP]
    refine FRW_eq _ _ _ fun c _ => ?_
    by_cases h : c.1.2.2.1.length ≤ 1 <;> simp [h]
  rw [hL, hW]
  refine ⟨FRW_le _ _ _ fun c hc => ?_, fun h4 => FRW_eq _ _ _ fun c hc => ?_⟩
  · by_cases h : c.1.2.2.1.length ≤ 1
    · simp only [h, decide_true, ↓reduceIte]
      exact (FRW_one_sum F leaf c hc h).1
    · simp [h]
  · by_cases h : c.1.2.2.1.length ≤ 1
    · simp only [h, decide_true, ↓reduceIte]
      obtain ⟨d, o, kd, rfl, hd, -⟩ := FRW_entry F leaf c hc
      exact (FRW_one_sum F leaf _ hc h).2 (h4 d hd).1 (h4 d hd).2
    · simp [h]

/-- The uses of labels below `4` are at most `2`. -/
private lemma FRW_cap (F : List FFac) (leaf : Bool) (l : ℕ) (hl : l < 4) :
    fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ l ≤ 2 := by
  rw [frule_run_uses F leaf l hl]
  exact (FRR_capInv _ leaf _).2 l

/-- The Ward use of the run of the rule in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: an entry with one part and two different labels below `4`
takes its Ward use at its designated label and uses no other label, or the final uses of that
label are `2`. -/
theorem frule_ward_or_full (F : List FFac) (leaf : Bool) (t : ℕ) (d : FEnt)
    (hd : (F.filterMap FFac.entData)[t]? = some d) (hxy : d.1 ≠ d.2.1) (hx : d.1 < 4)
    (hy : d.2.1 < 4) (hP : d.2.2.1.length ≤ 1) :
    (∃ o : FOpt, (fruleC F leaf)[t]? = some (d, some o) ∧
        ∀ l : ℕ, fuseOne (d, some o) l = if l = fwardLab d then 1 else 0) ∨
      fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ (fwardLab d) = 2 := by
  have hlt : t < (F.filterMap FFac.entData).length := (List.getElem?_eq_some_iff.1 hd).1
  obtain ⟨k, hk⟩ : ∃ k, (fruleOrd (F.filterMap FFac.entData))[k]? = some t :=
    List.mem_iff_getElem?.1 ((frule_run_order _).1.mem_iff.2 (List.mem_range.2 hlt))
  obtain ⟨⟨kd, o⟩, hfit⟩ := Option.isSome_iff_exists.1 (frule_run_fits F leaf k t d hk hd)
  obtain ⟨hkd, ho, hC⟩ := frule_run_chosen F leaf k t d hk hd kd o hfit
  obtain ⟨-, -, -, -, h1, h2, -⟩ := FRR_fit_spec _ _ _ _ _ hfit
  have hne := FRW_rk_ne _ _ hx hy hxy
  rcases FRW_kinds d leaf hP kd hkd o ho with ⟨rfl, -, -⟩ | ⟨-, -, hcx, hcy, hord⟩ |
      ⟨-, -, hcx, hcy, hord⟩
  · right
    have hκ := FRW_kappa d leaf hP hxy hx hy
    by_cases hr : frk.getD d.1 0 < frk.getD d.2.1 0
    · simp only [hr, ↓reduceIte] at hκ
      have hs := frule_run_sat F leaf k t d hk hd .sup o hfit .wardX hκ
        ⟨1, 0, 1, [((FMono.omega d.2.2.1.sum).mul ⟨0, 0, 0, 0, d.2.2.1.length - 1⟩).mul
          d.2.2.2.1]⟩ (by simp [fkindOpt, hxy]) (by simpa using hr)
      have c1 := FRW_cap F leaf _ hx
      have c2 := FRW_cap F leaf _ hy
      simp only at hs
      simp only [fwardLab, hr, ↓reduceIte]
      omega
    · simp only [hr, ↓reduceIte] at hκ
      have hr' : frk.getD d.2.1 0 < frk.getD d.1 0 := by omega
      have hs := frule_run_sat F leaf k t d hk hd .sup o hfit .wardY hκ
        ⟨0, 1, -1, [((FMono.omega d.2.2.1.sum).mul ⟨0, 0, 0, 0, d.2.2.1.length - 1⟩).mul
          d.2.2.2.1]⟩ (by simp [fkindOpt, hxy]) (by simpa using hr')
      have c1 := FRW_cap F leaf _ hx
      have c2 := FRW_cap F leaf _ hy
      simp only at hs
      simp only [fwardLab, hr, ↓reduceIte]
      omega
  · left
    have hr := h1 hord
    refine ⟨o, hC, fun l => ?_⟩
    simp only [fuseOne, fwardLab, hr, ↓reduceIte, hcx, hcy]
    split_ifs <;> omega
  · left
    have hr : ¬ frk.getD d.1 0 < frk.getD d.2.1 0 := by have := h2 hord; omega
    refine ⟨o, hC, fun l => ?_⟩
    simp only [fuseOne, fwardLab, hr, ↓reduceIte, hcx, hcy]
    split_ifs <;> omega

/-- The bound `min(N_ℓ, 2 - u_ℓ) ≤ ω_ℓ` at one label. -/
private lemma FRW_min (F : List FFac) (leaf : Bool) (l : ℕ) :
    min (fwardN F leaf l) (2 - fwardU F leaf l) ≤ FRW_om F leaf l := by
  by_cases hall : ∀ c ∈ fruleC F leaf, (c.1.2.2.1.length ≤ 1 ∧ c.1.1 ≠ c.1.2.1 ∧ c.1.1 < 4 ∧
      c.1.2.1 < 4 ∧ fwardLab c.1 = l) → fuseOne c l = 1
  · refine le_trans (min_le_left _ _) ?_
    rw [fwardN, FRW_countP, FRW_om, FRW_filter]
    refine FRW_le _ _ _ fun c hc => ?_
    by_cases h : c.1.2.2.1.length ≤ 1 ∧ c.1.1 ≠ c.1.2.1 ∧ c.1.1 < 4 ∧ c.1.2.1 < 4 ∧
        fwardLab c.1 = l
    · simp only [h, decide_true, ↓reduceIte, hall c hc h]
      simp [h]
    · simp only [decide_eq_true_eq, h, ↓reduceIte]
      exact Nat.zero_le _
  · push Not at hall
    obtain ⟨⟨d₀, oc⟩, hc, ⟨hP, hxy, hx, hy, hl⟩, hne⟩ := hall
    simp only at hP hxy hx hy hl hne
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hc
    have ht' := ht
    rw [fruleC, FO_fchosen, List.getElem?_mapIdx] at ht'
    obtain ⟨d, hd, hdc⟩ := Option.map_eq_some_iff.1 ht'
    obtain ⟨rfl, -⟩ := Prod.mk.inj hdc
    rcases frule_ward_or_full F leaf t d hd hxy hx hy hP with ⟨o, ho, hu⟩ | hfull
    · rw [ht] at ho
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ho)
      exact absurd (by simp [hu l, hl]) hne
    · rw [hl, FRW_split] at hfull
      omega

/-- The ends of one entry with labels below `4` at a label below `4`, by pairs of labels. -/
private lemma FRW_ends_pt (x y l : ℕ) (hx : x < 4) (hy : y < 4) (hl : l < 4) :
    (if x = l then 1 else 0) + (if y = l then 1 else 0) =
      2 * (if (x = l ∧ y = l) ∨ (x = l ∧ y = l) then 1 else 0) +
        (((List.range 4).filter fun b => b != l).map fun b =>
          if (x = l ∧ y = b) ∨ (x = b ∧ y = l) then 1 else 0).sum := by
  interval_cases x <;> interval_cases y <;> interval_cases l <;> decide

/-- The designated label of an entry with two different labels below `4`, by pairs of labels:
`0` for `{0, 1}`, never `1`, `2` for every pair with `2`, `3` for `{0, 3}` and `{1, 3}`. -/
private lemma FRW_lab (d : FEnt) :
    ((d.1 ≠ d.2.1 ∧ d.1 < 4 ∧ d.2.1 < 4 ∧ fwardLab d = 0) ↔
        ((d.1 = 0 ∧ d.2.1 = 1) ∨ (d.1 = 1 ∧ d.2.1 = 0))) ∧
      ¬ (d.1 ≠ d.2.1 ∧ d.1 < 4 ∧ d.2.1 < 4 ∧ fwardLab d = 1) ∧
      ((d.1 ≠ d.2.1 ∧ d.1 < 4 ∧ d.2.1 < 4 ∧ fwardLab d = 2) ↔
        (((d.1 = 0 ∧ d.2.1 = 2) ∨ (d.1 = 2 ∧ d.2.1 = 0)) ∨
          ((d.1 = 1 ∧ d.2.1 = 2) ∨ (d.1 = 2 ∧ d.2.1 = 1)) ∨
          ((d.1 = 2 ∧ d.2.1 = 3) ∨ (d.1 = 3 ∧ d.2.1 = 2)))) ∧
      ((d.1 ≠ d.2.1 ∧ d.1 < 4 ∧ d.2.1 < 4 ∧ fwardLab d = 3) ↔
        (((d.1 = 0 ∧ d.2.1 = 3) ∨ (d.1 = 3 ∧ d.2.1 = 0)) ∨
          ((d.1 = 1 ∧ d.2.1 = 3) ∨ (d.1 = 3 ∧ d.2.1 = 1)))) := by
  obtain ⟨x, y, r⟩ := d
  simp only [fwardLab]
  by_cases hx : x < 4
  · by_cases hy : y < 4
    · interval_cases x <;> interval_cases y <;> simp [frk]
    · refine ⟨⟨fun h => absurd h.2.2.1 hy, fun h => by omega⟩, fun h => hy h.2.2.1,
        ⟨fun h => absurd h.2.2.1 hy, fun h => by omega⟩,
        ⟨fun h => absurd h.2.2.1 hy, fun h => by omega⟩⟩
  · refine ⟨⟨fun h => absurd h.2.1 hx, fun h => by omega⟩, fun h => hx h.2.1,
      ⟨fun h => absurd h.2.1 hx, fun h => by omega⟩,
      ⟨fun h => absurd h.2.1 hx, fun h => by omega⟩⟩

/-! ## The statements on the run of the rule -/

/-- The count of the Ward uses of the run of the rule in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: `ω ≥ Σ_{ℓ < 4} min(N_ℓ, 2 - u_ℓ)`. -/
theorem frule_ward_count (F : List FFac) (leaf : Bool) :
    ((List.range 4).map fun l => min (fwardN F leaf l) (2 - fwardU F leaf l)).sum ≤
      fwardW F leaf := by
  refine le_trans ?_ (FRW_om_sum F leaf).1
  rw [FRW_r4, FRW_r4]
  have := FRW_min F leaf 0
  have := FRW_min F leaf 1
  have := FRW_min F leaf 2
  have := FRW_min F leaf 3
  omega

/-- The uses of the four labels by the run of the rule in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: those of the entries with at least two parts and one per Ward
use, when every label is below `4`. -/
theorem frule_uses_split (F : List FFac) (leaf : Bool)
    (h4 : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4) :
    ((List.range 4).map fun l => fuses F ⟨frk, fruleE (F.filterMap FFac.entData) leaf⟩ l).sum =
      ((List.range 4).map fun l => fwardU F leaf l).sum + fwardW F leaf := by
  rw [← (FRW_om_sum F leaf).2 h4, ← List.sum_map_add]
  exact FRW_eq _ _ _ fun l _ => FRW_split F leaf l

/-- The ends at label `ℓ` of the entries with one part, by pairs of labels, in the run of the
rule of the proof of Lemma 5.5 [claim_estimate_remainder_terms]: `e_ℓ = 2 c_{ℓℓ} + Σ_{b ≠ ℓ}
c_{ℓb}`, when every label is below `4`. -/
theorem frule_ends_pairs (F : List FFac) (leaf : Bool)
    (h4 : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4) (l : ℕ) (hl : l < 4) :
    fwardE F leaf l = 2 * fwardC F leaf l l +
      (((List.range 4).filter fun b => b != l).map fun b => fwardC F leaf l b).sum := by
  rw [fwardE, FRW_filter]
  simp only [fwardC, FRW_countP]
  rw [FRW_comm, ← List.sum_map_mul_left, ← List.sum_map_add]
  refine FRW_eq _ _ _ fun c hc => ?_
  obtain ⟨d, o, kd, rfl, hd, -⟩ := FRW_entry F leaf c hc
  by_cases hP : d.2.2.1.length ≤ 1
  · simp only [hP, decide_true, true_and, decide_eq_true_eq, ↓reduceIte]
    exact FRW_ends_pt _ _ _ (h4 d hd).1 (h4 d hd).2 hl
  · simp [hP]

/-- The numbers `N_ℓ` by pairs of labels, in the run of the rule of the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the designated label is `2` for every pair with `2`, `3` for
`{0, 3}` and `{1, 3}`, `0` for `{0, 1}`, never `1`. -/
theorem frule_wardN_pairs (F : List FFac) (leaf : Bool) :
    fwardN F leaf 0 = fwardC F leaf 0 1 ∧ fwardN F leaf 1 = 0 ∧
      fwardN F leaf 2 = fwardC F leaf 0 2 + fwardC F leaf 1 2 + fwardC F leaf 2 3 ∧
      fwardN F leaf 3 = fwardC F leaf 0 3 + fwardC F leaf 1 3 := by
  simp only [fwardN, fwardC, FRW_countP, ← List.sum_map_add]
  refine ⟨FRW_eq _ _ _ fun c _ => ?_, ?_, FRW_eq _ _ _ fun c _ => ?_,
    FRW_eq _ _ _ fun c _ => ?_⟩
  · simp only [decide_eq_true_eq, (FRW_lab c.1).1]
  · refine (FRW_eq _ _ (fun _ => 0) fun c _ => ?_).trans (by simp)
    split_ifs with h
    · exact absurd (of_decide_eq_true h).2 (FRW_lab c.1).2.1
    · rfl
  · simp only [decide_eq_true_eq, (FRW_lab c.1).2.2.1]
    split_ifs <;> omega
  · simp only [decide_eq_true_eq, (FRW_lab c.1).2.2.2]
    split_ifs <;> omega

end RBMTransitionEdge
