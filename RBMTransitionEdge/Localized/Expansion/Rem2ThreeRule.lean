module

public import RBMTransitionEdge.Localized.Expansion.FRuleRun
public import RBMTransitionEdge.Localized.Expansion.PkgInv2
public import RBMTransitionEdge.Localized.Expansion.PkgLists
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.RemStep
public import RBMTransitionEdge.Localized.Expansion.RemCounts
public import RBMTransitionEdge.Localized.Expansion.RemHalves
public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.RemHalves
import all RBMTransitionEdge.Localized.Expansion.RemCounts

@[expose] public section

/-!
# The rule lemma of Type III

For every expression of Type III expanded in the further expansion of the proof of Lemma 5.5
[claim_estimate_remainder_terms], every `p + q ≥ 2` and every derivative structure `R'` of
`𝓔^{(2)}_𝓡(p, q)`: the assignment `frule` of the factor list of the rules (with the pairing through
`𝒢₁` of the exceptional subcase of case (8)) is valid, and its bound with the prefactor passes the
rows (the companion cases (8), (9)).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### The integer test of the rows -/

/-- `FMono.ok` from the five inequalities of the three points, for total degree `2` in `‖A‖`. -/
private theorem R3_ok (m : FMono) (hi : 0 ≤ m.i) (hdo : m.d + m.o = 2)
    (h1 : 6 * (m.a + m.l) + 12 ≤ 0) (h2 : 6 * (m.a + m.l) + 12 ≤ 3 * m.l + 4)
    (h3 : 6 * (m.a + m.l) + 12 + m.i - 2 * m.l ≤ 8)
    (h4 : 6 * (m.a + m.l) + 12 + 8 ≤ 2 * m.l + 2 * m.i)
    (h5 : 6 * (m.a + m.l) + 12 ≤ 4 * m.l + m.i) : m.ok = true := by
  have hd : m.d ≤ 2 := by omega
  have hdo' : (m.d : ℤ) + m.o = 2 := by exact_mod_cast hdo
  have e1 : (if 2 ≤ m.d then 4 * ((m.d : ℤ) - 2) else 0) = 0 := by
    split_ifs with h
    · have : m.d = 2 := by omega
      simp [this]
    · rfl
  have e2 : (if 2 ≤ m.d then 6 * ((m.d : ℤ) - 2) else 0) = 0 := by
    split_ifs with h
    · have : m.d = 2 := by omega
      simp [this]
    · rfl
  simp only [FMono.ok, e1, e2, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨⟨hi, by omega⟩, ?_, ?_, ?_⟩ <;> omega

/-- The product of a list of monomials, by components. -/
private theorem R3_fold (L : List FMono) (m : FMono) : L.foldl FMono.mul m =
    ⟨m.a + (L.map FMono.a).sum, m.i + (L.map FMono.i).sum, m.l + (L.map FMono.l).sum,
      m.d + (L.map FMono.d).sum, m.o + (L.map FMono.o).sum⟩ := by
  induction L generalizing m with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    simp only [FMono.mul, List.map_cons, List.sum_cons, FMono.mk.injEq]
    omega

private theorem R3_prodL (L : List FMono) : FMono.prodL L =
    ⟨(L.map FMono.a).sum, (L.map FMono.i).sum, (L.map FMono.l).sum,
      (L.map FMono.d).sum, (L.map FMono.o).sum⟩ := by
  unfold FMono.prodL
  rw [R3_fold]
  simp

/-! ### The bounds of one entry -/

/-- The uses of an entry with its option, as counted in `fuses`. -/
private def R3u (d : FEnt) (o : FOpt) : ℤ := o.cx + (if d.2.1 = d.1 then 0 else (o.cy : ℤ))

/-- The bounds of one entry `d` with its option `o` and a monomial `q` of it, against its count
`nl` of `Λ̃`, its resolvents `r`, its extra `Im m` `e` and its uses `u`. -/
private def R3PP (d : FEnt) (o : FOpt) (q : FMono) : Prop :=
  q.a + q.l ≤ R3u d o + 2 * ((d.2.2.1.sum : ℤ) - 1) - ((d.2.2.1.length : ℤ) - 1) +
      (if d.2.2.1.sum = 0 then 1 else 0) ∧
    2 * ((d.2.2.1.sum : ℤ) - 1) + R3u d o - ((d.2.2.1.length : ℤ) - 1) +
      (if d.2.2.1.sum = 0 then 1 else 0) ≤ q.l ∧
    d.2.2.2.1.i + R3u d o - ((d.2.2.1.length : ℤ) - 1) - (if d.2.2.1.sum = 0 then 1 else 0) +
      2 * (if d.2.2.1.length = 3 ∧ 2 ≤ d.2.2.1.sum then 1 else 0) ≤ q.i ∧
    q.i ≤ d.2.2.2.1.i + R3u d o - ((d.2.2.1.length : ℤ) - 1) + 2 * ((d.2.2.1.sum : ℤ) - 1) +
      2 * (if d.2.2.1.sum = 0 then 1 else 0) ∧
    (q.d : ℤ) + q.o = (d.2.2.1.length : ℤ) - 1 ∧ 0 ≤ q.i ∧
    1 ≤ (d.2.2.1.sum : ℤ) + (if d.2.2.1.sum = 0 then 1 else 0)

/-- An entry without `Λ̃`, with a resolvent and an extra size `(Im m)^e`, in sup or in a Ward
row or column. -/
private theorem R3PP_free (x y r : ℕ) (ext : FMono) (det : Bool) (hr : 1 ≤ r)
    (he : ext.a = 0 ∧ ext.l = 0 ∧ ext.d = 0 ∧ ext.o = 0 ∧ 0 ≤ ext.i) (k : FKind)
    (hk : k ∈ FEnt.prefs (x, y, [r], ext, det) false) (o : FOpt)
    (ho : fkindOpt (x, y, [r], ext, det) k = some o) (q : FMono) (hq : q ∈ o.val) :
    R3PP (x, y, [r], ext, det) o q := by
  obtain ⟨ea, el, ed, eo, ei⟩ := he
  obtain ⟨a, i, l, d₀, o₀⟩ := ext
  simp only at ea el ed eo ei
  subst ea el ed eo
  have hk' : k = .sup ∨ k = .wardX ∨ k = .wardY := by
    unfold FEnt.prefs at hk
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hk
    split_ifs at hk <;> simp at hk <;> tauto
  rcases hk' with rfl | rfl | rfl
  · simp only [fkindOpt, List.sum_cons, List.sum_nil, add_zero, List.length_cons,
      List.length_nil, Option.some.injEq] at ho
    subst ho
    simp only [List.mem_singleton] at hq
    subst hq
    unfold R3PP R3u FMono.psi
    split_ifs <;> simp_all [FMono.mul] <;> omega
  · simp only [fkindOpt] at ho
    split_ifs at ho with hxy
    simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
      Option.some.injEq] at ho
    subst ho
    simp only [List.mem_singleton] at hq
    subst hq
    unfold R3PP R3u FMono.omega
    split_ifs <;> simp_all [FMono.mul]; omega
  · simp only [fkindOpt] at ho
    split_ifs at ho with hxy
    simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
      Option.some.injEq] at ho
    subst ho
    simp only [List.mem_singleton] at hq
    subst hq
    unfold R3PP R3u FMono.omega
    split_ifs <;> simp_all [FMono.mul]; omega

/-- The first kind of an entry fits. -/
private theorem R3_fit_head (cap : List ℕ) (d : FEnt) (k : FKind) (ks : List FKind)
    (hp : d.prefs false = k :: ks) (o : FOpt) (hf : fkindFit false frk cap d [] k = some (0, o)) :
    fruleFit cap d false = some (k, o) := by
  unfold fruleFit
  rw [hp, List.findSome?_cons, hf]
  rfl

/-- The entry with both letters `Λ̃` and an outer and an inner label takes the double split. -/
private theorem R3_fit_dbl (x y r : ℕ) (ext : FMono) (det : Bool) (hxy : x ≠ y) (hr : 1 ≤ r)
    (he : ext.a = 0 ∧ ext.l = 0 ∧ ext.d = 0 ∧ ext.o = 0 ∧ 0 ≤ ext.i) (cap : List ℕ)
    (hcx : cap.getD x 0 ≤ 1) (hcy : cap.getD y 0 ≤ 1) (kd : FKind) (o : FOpt)
    (h : fruleFit cap (x, y, [0, r, 0], ext, det) false = some (kd, o)) :
    (∀ q ∈ o.val, R3PP (x, y, [0, r, 0], ext, det) o q) ∧
      ∀ l, fuseOne ((x, y, [0, r, 0], ext, det), some o) l =
        (if x = l then 1 else 0) + (if y = l then 1 else 0) := by
  have hp : FEnt.prefs (x, y, [0, r, 0], ext, det) false =
      .dbl true true :: [.dbl true false, .dbl false true, .isoX, .isoY, .sup] := by
    simp [FEnt.prefs, hxy]
  rw [R3_fit_head cap _ _ _ hp ⟨1, 1, 0, [((FMono.psi r).mul ⟨0, 0, 0, 2, 0⟩).mul ext]⟩
    (by
      simp only [List.getD_eq_getElem?_getD] at hcx hcy
      simp [fkindFit, fkindOpt, hxy]; omega)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨ea, el, ed, eo, ei⟩ := he
  obtain ⟨a, i, l, d₀, o₀⟩ := ext
  simp only at ea el ed eo ei
  subst ea el ed eo
  refine ⟨fun q hq => ?_, fun l => ?_⟩
  · simp only [List.mem_singleton] at hq
    subst hq
    unfold R3PP R3u FMono.psi
    split_ifs <;> simp_all [FMono.mul] <;> omega
  · simp [fuseOne]
    split_ifs <;> omega

/-- An entry with one letter `Λ̃` and distinct labels takes the Hilbert–Schmidt norm. -/
private theorem R3_fit_hs (x y a b : ℕ) (ext : FMono) (det : Bool) (hxy : x ≠ y)
    (he : ext.a = 0 ∧ ext.l = 0 ∧ ext.d = 0 ∧ ext.o = 0 ∧ 0 ≤ ext.i) (cap : List ℕ)
    (hcx : cap.getD x 0 ≤ 1) (hcy : cap.getD y 0 ≤ 1) (kd : FKind) (o : FOpt)
    (h : fruleFit cap (x, y, [a, b], ext, det) false = some (kd, o)) :
    (∀ q ∈ o.val, R3PP (x, y, [a, b], ext, det) o q) ∧
      ∀ l, fuseOne ((x, y, [a, b], ext, det), some o) l =
        (if x = l then 1 else 0) + (if y = l then 1 else 0) := by
  obtain ⟨ks, hp⟩ : ∃ ks, FEnt.prefs (x, y, [a, b], ext, det) false = .hs :: ks := by
    simp only [FEnt.prefs, hxy, ↓reduceIte, List.length_cons, List.length_nil]
    exact ⟨_, rfl⟩
  rw [R3_fit_head cap _ _ _ hp ⟨1, 1, 0, [(fhalf 1 (a + b) true).mul ext]⟩
    (by simp only [List.getD_eq_getElem?_getD] at hcx hcy; simp [fkindFit, fkindOpt, hxy]; omega)]
    at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨ea, el, ed, eo, ei⟩ := he
  obtain ⟨a', i, l, d₀, o₀⟩ := ext
  simp only at ea el ed eo ei
  subst ea el ed eo
  refine ⟨fun q hq => ?_, fun l => ?_⟩
  · simp only [List.mem_singleton] at hq
    subst hq
    unfold R3PP R3u fhalf FMono.omega
    split_ifs <;> simp_all [FMono.mul] <;> omega
  · simp [fuseOne]
    split_ifs <;> omega

/-- The entry `(3, 3)` with one letter `Λ̃`, resolvents before it and none after it takes the
isotropic split at the column. -/
private theorem R3_fit_isoY (x r : ℕ) (ext : FMono) (det : Bool) (hr : 1 ≤ r)
    (he : ext.a = 0 ∧ ext.l = 0 ∧ ext.d = 0 ∧ ext.o = 0 ∧ 0 ≤ ext.i) (cap : List ℕ)
    (hcx : cap.getD x 0 ≤ 1) (kd : FKind) (o : FOpt)
    (h : fruleFit cap (x, x, [r, 0], ext, det) false = some (kd, o)) :
    (∀ q ∈ o.val, R3PP (x, x, [r, 0], ext, det) o q) ∧
      ∀ l, fuseOne ((x, x, [r, 0], ext, det), some o) l = (if x = l then 1 else 0) := by
  have hr0 : r ≠ 0 := by omega
  obtain ⟨ks, hp⟩ : ∃ ks, FEnt.prefs (x, x, [r, 0], ext, det) false = .isoX :: .isoY :: ks := by
    simp only [FEnt.prefs, ↓reduceIte, List.length_cons, List.length_nil]
    exact ⟨_, rfl⟩
  have h1 : fkindFit false frk cap (x, x, [r, 0], ext, det) [] .isoX = none := by
    simp [fkindFit, fkindOpt, hr0]
  have h2 : fkindFit false frk cap (x, x, [r, 0], ext, det) [] .isoY =
      some (0, ⟨1, 0, 0,
        [((fhalf 1 0 true).mul ((FMono.psi r).mul ⟨0, 0, 0, 0, 0⟩)).mul ext]⟩) := by
    simp only [List.getD_eq_getElem?_getD] at hcx
    simp [fkindFit, fkindOpt]
    omega
  unfold fruleFit at h
  rw [hp, List.findSome?_cons, h1, Option.map_none, List.findSome?_cons, h2] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨ea, el, ed, eo, ei⟩ := he
  obtain ⟨a', i, l, d₀, o₀⟩ := ext
  simp only at ea el ed eo ei
  subst ea el ed eo
  refine ⟨fun q hq => ?_, fun l => ?_⟩
  · simp only [List.mem_singleton] at hq
    subst hq
    unfold R3PP R3u fhalf FMono.omega FMono.psi
    split_ifs <;> simp_all [FMono.mul] <;> omega
  · simp [fuseOne]

/-- An entry without `Λ̃`, with one inner and one outer label, takes its Ward row or column when
its inner label has at most one use. -/
private theorem R3_fit_ward (x y r : ℕ) (ext : FMono) (det : Bool)
    (hxy : (2 ≤ x ∧ x < 4 ∧ y < 2) ∨ (2 ≤ y ∧ y < 4 ∧ x < 2)) (cap : List ℕ)
    (hcx : cap.getD x 0 ≤ 1) (hcy : cap.getD y 0 ≤ 1) (kd : FKind) (o : FOpt)
    (h : fruleFit cap (x, y, [r], ext, det) false = some (kd, o)) :
    R3u (x, y, [r], ext, det) o = 1 := by
  rcases hxy with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hp : FEnt.prefs (x, y, [r], ext, det) false = .wardX :: [.sup] := by
      have e1 : fInnerL x = true := by simp [fInnerL]; omega
      have e2 : fInnerL y = false := by simp [fInnerL]; omega
      simp [FEnt.prefs, e1, e2, show x ≠ y by omega]
    rw [R3_fit_head cap _ _ _ hp ⟨1, 0, 1, [((FMono.omega r).mul ⟨0, 0, 0, 0, 0⟩).mul ext]⟩
      (by
        simp only [List.getD_eq_getElem?_getD] at hcx hcy
        have hx : x = 2 ∨ x = 3 := by omega
        have hy : y = 0 ∨ y = 1 := by omega
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp [fkindFit, fkindOpt, frk] <;> omega)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [R3u]
  · have hp : FEnt.prefs (x, y, [r], ext, det) false = .wardY :: [.sup] := by
      have e1 : fInnerL y = true := by simp [fInnerL]; omega
      have e2 : fInnerL x = false := by simp [fInnerL]; omega
      simp [FEnt.prefs, e1, e2, show x ≠ y by omega]
    rw [R3_fit_head cap _ _ _ hp ⟨0, 1, -1, [((FMono.omega r).mul ⟨0, 0, 0, 0, 0⟩).mul ext]⟩
      (by
        simp only [List.getD_eq_getElem?_getD] at hcx hcy
        have hy : y = 2 ∨ y = 3 := by omega
        have hx : x = 0 ∨ x = 1 := by omega
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp [fkindFit, fkindOpt, frk] <;> omega)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [R3u]
    omega

/-! ### The run of the rule -/

/-- A list read at the indices of its range. -/
private theorem R3_range_getD (E : List FEnt) :
    (List.range E.length).map (fun t => E.getD t FEnt.dflt) = E := by
  refine List.ext_getElem (by simp) fun t h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The entries treated up to step `k` satisfy a predicate of the roles that every later one
satisfies at least as well: at most as many steps as entries with that predicate. -/
private theorem R3_pos (E : List FEnt) (ρ n k t : ℕ)
    (hn : E.countP (fun d => decide (d.role ≤ ρ)) = n) (ht : (fruleOrd E)[k]? = some t)
    (hr : (E.getD t FEnt.dflt).role ≤ ρ) : k < n := by
  obtain ⟨hperm, hpw⟩ := frule_run_order E
  have hk : k < (fruleOrd E).length := (List.getElem?_eq_some_iff.1 ht).1
  have hkt : (fruleOrd E)[k] = t := (List.getElem?_eq_some_iff.1 ht).2
  have hmap : ((fruleOrd E).map fun t => E.getD t FEnt.dflt).Perm E := by
    have := hperm.map (fun t => E.getD t FEnt.dflt)
    rwa [R3_range_getD] at this
  have hc := hmap.countP_eq (fun d => decide (d.role ≤ ρ))
  have htake : (((fruleOrd E).take (k + 1)).map fun t => E.getD t FEnt.dflt).countP
      (fun d => decide (d.role ≤ ρ)) = k + 1 := by
    rw [List.countP_eq_length.2, List.length_map, List.length_take]
    · omega
    · intro d hd
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hd
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht'
      rw [List.length_take] at hj
      rw [List.getElem_take]
      simp only [decide_eq_true_eq]
      rcases Nat.lt_or_ge j k with hjk | hjk
      · have := List.pairwise_iff_getElem.1 hpw j k (by omega) hk hjk
        rw [hkt] at this
        omega
      · have : j = k := by omega
        subst this
        rw [hkt]
        exact hr
  have hle : (((fruleOrd E).take (k + 1)).map fun t => E.getD t FEnt.dflt).countP
      (fun d => decide (d.role ≤ ρ)) ≤
      ((fruleOrd E).map fun t => E.getD t FEnt.dflt).countP (fun d => decide (d.role ≤ ρ)) := by
    conv_rhs => rw [← List.take_append_drop (k + 1) (fruleOrd E)]
    rw [List.map_append, List.countP_append]
    omega
  omega

/-- An entry of a larger role than `ρ` comes after every entry of role at most `ρ`. -/
private theorem R3_pos' (E : List FEnt) (ρ n k t : ℕ)
    (hn : E.countP (fun d => decide (d.role ≤ ρ)) = n) (ht : (fruleOrd E)[k]? = some t)
    (hr : ρ < (E.getD t FEnt.dflt).role) : n ≤ k := by
  obtain ⟨hperm, hpw⟩ := frule_run_order E
  have hk : k < (fruleOrd E).length := (List.getElem?_eq_some_iff.1 ht).1
  have hkt : (fruleOrd E)[k] = t := (List.getElem?_eq_some_iff.1 ht).2
  have hmap : ((fruleOrd E).map fun t => E.getD t FEnt.dflt).Perm E := by
    have := hperm.map (fun t => E.getD t FEnt.dflt)
    rwa [R3_range_getD] at this
  have hc := hmap.countP_eq (fun d => decide (d.role ≤ ρ))
  have hdrop : (((fruleOrd E).drop k).map fun t => E.getD t FEnt.dflt).countP
      (fun d => decide (d.role ≤ ρ)) = 0 := by
    rw [List.countP_eq_zero]
    intro d hd
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hd
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht'
    rw [List.length_drop] at hj
    rw [List.getElem_drop]
    simp only [decide_eq_true_eq, not_le]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [Nat.add_zero, hkt]; exact hr
    · have := List.pairwise_iff_getElem.1 hpw k (k + j) hk (by omega) (by omega)
      rw [hkt] at this
      omega
  have htake : (((fruleOrd E).take k).map fun t => E.getD t FEnt.dflt).countP
      (fun d => decide (d.role ≤ ρ)) ≤ k := by
    refine (List.countP_le_length).trans ?_
    simp
  rw [← List.take_append_drop k (fruleOrd E), List.map_append, List.countP_append, hdrop] at hc
  omega

/-- The entries of the chosen list are the entries of the factor list. -/
private theorem R3_fst (F : List FFac) (g : FAsg) :
    (fchosen F g).map Prod.fst = F.filterMap FFac.entData := by
  have h : fchosen F g = (List.range (F.filterMap FFac.entData).length).map fun t =>
      ((F.filterMap FFac.entData).getD t FEnt.dflt,
        (FEnt.opts ((F.filterMap FFac.entData).getD t FEnt.dflt))[g.opt.getD t 0]?) := by
    unfold fchosen
    refine List.filterMap_eq_map_iff_forall_eq_some.2 fun t ht => ?_
    simp only [List.mem_range] at ht
    simp [List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD, FEnt.opts]
  rw [h, List.map_map]
  exact R3_range_getD _

/-- The uses after `k + 1` steps: those after `k` steps and those of the entry of step `k`. -/
private theorem R3_cap_succ (F : List FFac) (k t l : ℕ) (hl : l < 4) (d : FEnt) (o : FOpt)
    (ht : (fruleOrd (F.filterMap FFac.entData))[k]? = some t)
    (hc : (fchosen F ⟨frk, fruleE (F.filterMap FFac.entData) false⟩)[t]? = some (d, some o)) :
    (fruleCap (F.filterMap FFac.entData) false (k + 1)).getD l 0 =
      (fruleCap (F.filterMap FFac.entData) false k).getD l 0 + fuseOne (d, some o) l := by
  rw [frule_run_cap F false (k + 1) l hl, frule_run_cap F false k l hl, List.take_add_one, ht]
  simp [hc]

/-- The uses after any number of steps are at most the final uses. -/
private theorem R3_cap_le (F : List FFac) (k l : ℕ) (hl : l < 4)
    (hk : k ≤ (F.filterMap FFac.entData).length) :
    (fruleCap (F.filterMap FFac.entData) false k).getD l 0 ≤
      fuses F ⟨frk, fruleE (F.filterMap FFac.entData) false⟩ l := by
  rw [frule_run_uses F false l hl]
  exact (frule_run_mono _ false k _ l hk).2.2

/-- The uses of a chosen entry. -/
private def R3U (c : FEnt × Option FOpt) : ℤ :=
  match c.2 with
  | some o => R3u c.1 o
  | none => 0

/-- The uses of the four labels add up to the uses of the entries. -/
private theorem R3_U (L : List (FEnt × Option FOpt)) (hL : ∀ c ∈ L, c.1.1 < 4 ∧ c.1.2.1 < 4) :
    ((List.range 4).map fun l => ((L.map fun c => fuseOne c l).sum : ℤ)).sum =
      (L.map R3U).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    obtain ⟨hx, hy⟩ := hL c List.mem_cons_self
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.cons_append] at ih' ⊢
    push_cast at ih' ⊢
    have key : (fuseOne c 0 : ℤ) + fuseOne c 1 + fuseOne c 2 + fuseOne c 3 = R3U c := by
      obtain ⟨⟨x, y, rest⟩, oo⟩ := c
      simp only at hx hy
      rcases oo with _ | o
      · simp [fuseOne, R3U]
      · simp only [fuseOne, R3U, R3u]
        interval_cases x <;> interval_cases y <;> simp <;> ring
    linarith

/-- The count `nl` of `Λ̃` of an entry. -/
private def R3nl (d : FEnt) : ℤ := (d.2.2.1.length : ℤ) - 1

/-- The resolvents of an entry, less one. -/
private def R3rr (d : FEnt) : ℤ := (d.2.2.1.sum : ℤ) - 1

/-- `1` for an entry without resolvent. -/
private def R3zz (d : FEnt) : ℤ := if d.2.2.1.sum = 0 then 1 else 0

/-- `1` for an entry with both letters `Λ̃` and at least two resolvents. -/
private def R3bb (d : FEnt) : ℤ := if d.2.2.1.length = 3 ∧ 2 ≤ d.2.2.1.sum then 1 else 0

/-- The bounds of the entries, added up along the chosen list and the monomials of the bound. -/
private theorem R3_agg (L : List (FEnt × Option FOpt)) (qs : List FMono)
    (h2 : List.Forall₂ (fun c q => ∃ o, c.2 = some o ∧ q ∈ o.val) L qs)
    (hP : ∀ c ∈ L, ∀ o, c.2 = some o → ∀ q ∈ o.val, R3PP c.1 o q) :
    (qs.map FMono.a).sum + (qs.map FMono.l).sum ≤ (L.map R3U).sum +
        2 * (L.map fun c => R3rr c.1).sum - (L.map fun c => R3nl c.1).sum +
        (L.map fun c => R3zz c.1).sum ∧
      2 * (L.map fun c => R3rr c.1).sum + (L.map R3U).sum - (L.map fun c => R3nl c.1).sum +
        (L.map fun c => R3zz c.1).sum ≤ (qs.map FMono.l).sum ∧
      (L.map fun c => c.1.2.2.2.1.i).sum + (L.map R3U).sum - (L.map fun c => R3nl c.1).sum -
        (L.map fun c => R3zz c.1).sum + 2 * (L.map fun c => R3bb c.1).sum ≤
        (qs.map FMono.i).sum ∧
      (qs.map FMono.i).sum ≤ (L.map fun c => c.1.2.2.2.1.i).sum + (L.map R3U).sum -
        (L.map fun c => R3nl c.1).sum + 2 * (L.map fun c => R3rr c.1).sum +
        2 * (L.map fun c => R3zz c.1).sum ∧
      ((qs.map FMono.d).sum : ℤ) + (qs.map FMono.o).sum = (L.map fun c => R3nl c.1).sum ∧
      0 ≤ (qs.map FMono.i).sum ∧
      0 ≤ (L.map fun c => R3rr c.1).sum + (L.map fun c => R3zz c.1).sum := by
  induction h2 with
  | nil => simp
  | @cons c q L qs hcq _ ih =>
    have ih' := ih fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
    obtain ⟨o, hco, hq⟩ := hcq
    have hp := hP c List.mem_cons_self o hco q hq
    have hU : R3U c = R3u c.1 o := by simp [R3U, hco]
    unfold R3PP at hp
    simp only [List.map_cons, List.sum_cons, R3nl, R3rr, R3zz, R3bb] at ih' ⊢
    push_cast at ih' hp ⊢
    rw [hU]
    omega

/-- The sizes of the loops and the light weights of a factor list whose loops have no `Λ̃` and at
least two resolvents. -/
private theorem R3_fix (F : List FFac)
    (hF : ∀ w ∈ fLoops F, FLet.lamt ∉ w ∧ 2 ≤ fresN w) :
    FMono.prodL (F.map FFac.fixV) =
      ⟨-2 * (F.countP fun f => match f with | .wt _ _ => true | _ => false),
        2 * (fLoops F).length,
        2 * (F.countP fun f => match f with | .wt _ _ => true | _ => false) +
          2 * ((fLoops F).map fun w => (fresN w : ℤ) - 1).sum, 0, 0⟩ := by
  rw [R3_prodL]
  induction F with
  | nil => simp [fLoops]
  | cons f F ih =>
    have ih' := ih fun w hw => hF w (by
      simp only [fLoops, List.filterMap_cons] at hw ⊢
      split <;> simp_all)
    simp only [FMono.mk.injEq] at ih' ⊢
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih'
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
    · have e : fLoops (FFac.ent x y w :: F) = fLoops F := by simp [fLoops]
      simp only [List.map_cons, List.sum_cons, FFac.fixV, e, List.countP_cons]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      omega
    · have hw := hF w (by simp [fLoops])
      have hfx : (FFac.loop w).fixV = ⟨0, 2, 2 * ((fresN w : ℤ) - 1), 0, 0⟩ := by
        have hnl : w.countP (· == FLet.lamt) = 0 := List.countP_eq_zero.2 fun x hx hxl => by
          simp only [beq_iff_eq] at hxl; subst hxl; exact hw.1 hx
        have h1 : (FFac.loop w).fixV = FMono.psi (fresN w) := by
          simp only [FFac.fixV, hnl, ↓reduceIte]
          rfl
        simp only [h1, FMono.psi, hw.2, ↓reduceIte]
      have e : fLoops (FFac.loop w :: F) = w :: fLoops F := by simp [fLoops]
      simp only [List.map_cons, List.sum_cons, hfx, e, List.countP_cons, List.length_cons]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      push_cast
      omega
    · have e : fLoops (FFac.wt a x :: F) = fLoops F := by simp [fLoops]
      simp only [List.map_cons, List.sum_cons, FFac.fixV, e, List.countP_cons]
      simp only [↓reduceIte]
      omega

/-! ### The counts of a derivative structure -/

open private FW_one FW_sum_one FW_g FW_rfacs from RBMTransitionEdge.Localized.Expansion.FEntWords
open private charsP_eq from RBMTransitionEdge.Localized.Expansion.PkgWords

/-- The light weights of the factor list of the rules are those of the expression. -/
private theorem R3_wt (X : PkgExpr) :
    (X.rfacs.countP fun f => match f with | .wt _ _ => true | _ => false) = X.weights.length := by
  unfold PkgExpr.rfacs
  rw [List.countP_map]
  have hg : ((fun f : FFac => match f with | .wt _ _ => true | _ => false) ∘
      fun f : FFac => if X.fpg 0 = true then f.dupRes 0 else if X.fpg 1 = true then f.dupRes 1
        else f) = fun f : FFac => match f with | .wt _ _ => true | _ => false := by
    funext f
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp only [Function.comp] <;> split_ifs <;> rfl
  rw [hg]
  unfold PkgExpr.ffacs
  rw [List.countP_append, List.countP_map]
  have h1 : (X.weights.countP ((fun f : FFac => match f with | .wt _ _ => true | _ => false) ∘
      fun p => FFac.wt p.1 p.2)) = X.weights.length := by
    rw [List.countP_eq_length]
    intro _ _
    rfl
  rw [h1, Nat.add_eq_left, List.countP_eq_zero]
  intro f hf
  rw [List.mem_flatMap] at hf
  obtain ⟨w, -, hf⟩ := hf
  split_ifs at hf
  · obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 hf
    split at ht <;> simp only [Option.some.injEq, reduceCtorEq] at ht
    subst ht
    simp
  · simp only [List.mem_singleton] at hf
    subst hf
    simp

/-- The number `n` of factors of an expression: one per entry and one per loop of the factor
list of the rules. -/
private theorem R3_n (X : PkgExpr) :
    X.charsP.2.1 = (X.rfacs.filterMap FFac.entData).length + (fLoops X.rfacs).length := by
  have h1 : ∀ F : List FFac, (F.map FW_one).sum =
      (F.filterMap FFac.entData).length + (fLoops F).length := by
    intro F
    induction F with
    | nil => simp [fLoops]
    | cons f F ih =>
      rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
        simp [FW_one, fLoops, FFac.entData, List.filterMap_cons, ih] at ih ⊢ <;> omega
  have h2 : (X.rfacs.map FW_one).sum = ((X.ffacs (fun _ => false) X.fpm).map FW_one).sum := by
    rw [FW_rfacs, List.map_map]
    congr 1
    refine List.map_congr_left fun f _ => ?_
    simp only [Function.comp, FW_g]
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> split_ifs <;> rfl
  rw [charsP_eq]
  simp only
  rw [← FW_sum_one, ← h2, h1]
  push_cast
  rfl

/-! ### The bound from the counts -/

/-- The bound of the rule passes the rows, from the bounds of the entries, the counts of the
structure (its `S`, the number of resolvents and light weights, the loops), the pairings, and a
lower bound of the uses. -/
private theorem R3_bound (R' : PkgExpr) (s : ℕ) (f F : ℤ) (hs : 2 ≤ s) (hf : 0 ≤ f) (hF : 0 ≤ F)
    (hS : R'.S = f + ((R'.rfacs.filterMap FFac.entData).map R3rr).sum +
      ((fLoops R'.rfacs).map fun w => (fresN w : ℤ) - 1).sum - R'.fpi)
    (hM4 : ((R'.rfacs.filterMap FFac.entData).map R3rr).sum +
      ((fLoops R'.rfacs).map fun w => (fresN w : ℤ)).sum + R'.weights.length = F - f + R'.fpi)
    (hloops : ∀ w ∈ fLoops R'.rfacs, FLet.lamt ∉ w ∧ 2 ≤ fresN w)
    (hlab : ∀ d ∈ R'.rfacs.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4)
    (hpair : ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum + 2 * R'.fpi ≤ 2)
    (he : ∀ d ∈ R'.rfacs.filterMap FFac.entData, 0 ≤ d.2.2.2.1.i)
    (hnl : ((R'.rfacs.filterMap FFac.entData).map R3nl).sum = 2)
    (hPP : ∀ c ∈ fchosen R'.rfacs (frule R'.rfacs), ∀ o, c.2 = some o → ∀ q ∈ o.val,
      R3PP c.1 o q)
    (hU3 : 3 ≤ ((List.range 4).map fun l => (fuses R'.rfacs (frule R'.rfacs) l : ℤ)).sum)
    (hz : ((R'.rfacs.filterMap FFac.entData).map R3zz).sum ≤ 1)
    (hz1 : ((R'.rfacs.filterMap FFac.entData).map R3zz).sum = 1 → 1 ≤ f ∧
      4 ≤ ((List.range 4).map fun l => (fuses R'.rfacs (frule R'.rfacs) l : ℤ)).sum)
    (hU4 : 4 ≤ ((List.range 4).map fun l => (fuses R'.rfacs (frule R'.rfacs) l : ℤ)).sum ∨
      1 ≤ F + 2 * f + ((R'.rfacs.filterMap FFac.entData).map R3bb).sum ∨ 3 ≤ s) :
    ∀ m ∈ fboundM R'.rfacs (frule R'.rfacs),
      ((m.mul ⟨-((s : ℕ) : ℤ) - 6 - 2 * R'.S, 0, 0, 0, 0⟩).mul R'.rext).ok = true := by
  intro m hm
  have hsome : ∀ c ∈ fchosen R'.rfacs (frule R'.rfacs), c.2.isSome = true :=
    frule_run_some _ false
  obtain ⟨qs, h2, rfl⟩ := (fboundM_mem _ _ hsome m).1 hm
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := R3_agg _ qs h2 hPP
  have hfst : ∀ h : FEnt → ℤ, ((fchosen R'.rfacs (frule R'.rfacs)).map fun c => h c.1).sum =
      ((R'.rfacs.filterMap FFac.entData).map h).sum := by
    intro h
    rw [← R3_fst R'.rfacs (frule R'.rfacs), List.map_map]
    rfl
  rw [hfst R3rr, hfst R3nl, hfst R3zz, hfst R3bb, hfst fun d => d.2.2.2.1.i] at *
  have hUsum : ((List.range 4).map fun l => (fuses R'.rfacs (frule R'.rfacs) l : ℤ)).sum =
      ((fchosen R'.rfacs (frule R'.rfacs)).map R3U).sum := by
    have := R3_U (fchosen R'.rfacs (frule R'.rfacs)) fun c hc => by
      have : c.1 ∈ R'.rfacs.filterMap FFac.entData := by
        rw [← R3_fst R'.rfacs (frule R'.rfacs)]
        exact List.mem_map_of_mem hc
      exact hlab c.1 this
    rw [← this]
    rfl
  rw [hUsum] at hU3 hz1 hU4
  have hfix := R3_fix R'.rfacs hloops
  rw [R3_wt] at hfix
  have hlab4 : ((List.range 4).map fun l => (2 : ℤ) -
      (fuses R'.rfacs (frule R'.rfacs) l : ℤ)).sum =
      8 - ((fchosen R'.rfacs (frule R'.rfacs)).map R3U).sum := by
    rw [← hUsum]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.cons_append]
    ring
  have hloopsum : ((fLoops R'.rfacs).map fun w => (fresN w : ℤ)).sum =
      ((fLoops R'.rfacs).map fun w => (fresN w : ℤ) - 1).sum + (fLoops R'.rfacs).length := by
    have : ∀ L : List (List FLet), (L.map fun w => (fresN w : ℤ)).sum =
        (L.map fun w => (fresN w : ℤ) - 1).sum + L.length := by
      intro L
      induction L with
      | nil => simp
      | cons w L ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring
    exact this _
  have hloopres : (fLoops R'.rfacs).length ≤
      ((fLoops R'.rfacs).map fun w => (fresN w : ℤ) - 1).sum := by
    have : ∀ L : List (List FLet), (∀ w ∈ L, 2 ≤ fresN w) →
        (L.length : ℤ) ≤ (L.map fun w => (fresN w : ℤ) - 1).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons w L ih =>
        have h1 := hL w List.mem_cons_self
        have h2 := ih fun w' hw' => hL w' (List.mem_cons_of_mem _ hw')
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        push_cast
        omega
    exact this _ fun w hw => (hloops w hw).2
  have hesum : 0 ≤ ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum :=
    List.sum_nonneg fun x hx => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    exact he d hd
  have hpi : R'.fpi ≤ 1 := by unfold PkgExpr.fpi; split_ifs <;> simp
  have hext : R'.rext = ⟨0, 0, -2 * (R'.fpi : ℤ), 0, 0⟩ := by
    unfold PkgExpr.rext PkgExpr.fpi
    split_ifs <;> simp
  rw [hext, hfix, hlab4, R3_prodL]
  simp only [FMono.mul]
  have hd5 : (((qs.map FMono.d).sum : ℕ) : ℤ) + (((qs.map FMono.o).sum : ℕ) : ℤ) = 2 := by
    rw [a5, hnl]
  have hz0 : 0 ≤ ((R'.rfacs.filterMap FFac.entData).map R3zz).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
      unfold R3zz; split_ifs <;> simp
  have hb0 : 0 ≤ ((R'.rfacs.filterMap FFac.entData).map R3bb).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
      unfold R3bb; split_ifs <;> simp
  apply R3_ok
  all_goals
    simp only [zero_add, add_zero]
  all_goals
    generalize ((fchosen R'.rfacs (frule R'.rfacs)).map R3U).sum = U at *
    generalize ((R'.rfacs.filterMap FFac.entData).map R3rr).sum = Sr at *
    generalize ((R'.rfacs.filterMap FFac.entData).map R3nl).sum = Snl at *
    generalize ((R'.rfacs.filterMap FFac.entData).map R3zz).sum = Sz at *
    generalize ((R'.rfacs.filterMap FFac.entData).map R3bb).sum = Sb at *
    generalize ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum = Se at *
    generalize ((fLoops R'.rfacs).map fun w => (fresN w : ℤ) - 1).sum = Lr at *
    generalize ((fLoops R'.rfacs).map fun w => (fresN w : ℤ)).sum = Lf at *
    generalize (qs.map FMono.a).sum = Qa at *
    generalize (qs.map FMono.i).sum = Qi at *
    generalize (qs.map FMono.l).sum = Ql at *
    omega

/-! ### The steps of the rule -/

/-- Every entry is treated at some step, with the first kind of its list that fits the uses
before it. -/
private theorem R3_step (F : List FFac) (t : ℕ) (ht : t < (F.filterMap FFac.entData).length) :
    ∃ k kd o, (fruleOrd (F.filterMap FFac.entData))[k]? = some t ∧
      fruleFit (fruleCap (F.filterMap FFac.entData) false k)
        ((F.filterMap FFac.entData)[t]) false = some (kd, o) ∧
      kd ∈ FEnt.prefs ((F.filterMap FFac.entData)[t]) false ∧
      fkindOpt ((F.filterMap FFac.entData)[t]) kd = some o ∧
      (fchosen F (frule F))[t]? = some ((F.filterMap FFac.entData)[t], some o) := by
  have hmem : t ∈ fruleOrd (F.filterMap FFac.entData) :=
    (frule_run_order _).1.symm.subset (List.mem_range.2 ht)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hmem
  have hd : (F.filterMap FFac.entData)[t]? = some ((F.filterMap FFac.entData)[t]) :=
    List.getElem?_eq_getElem ht
  obtain ⟨⟨kd, o⟩, hfit⟩ := Option.isSome_iff_exists.1 (frule_run_fits F false k t _ hk hd)
  obtain ⟨h1, h2, h3⟩ := frule_run_chosen F false k t _ hk hd kd o hfit
  exact ⟨k, kd, o, hk, hfit, h1, h2, h3⟩

/-- Every chosen entry is that of an index of the entries. -/
private theorem R3_chosen_mem (F : List FFac) (c : FEnt × Option FOpt)
    (hc : c ∈ fchosen F (frule F)) :
    ∃ t, ∃ ht : t < (F.filterMap FFac.entData).length,
      (fchosen F (frule F))[t]? = some c ∧ c.1 = (F.filterMap FFac.entData)[t] := by
  obtain ⟨t, htc⟩ := List.mem_iff_getElem?.1 hc
  have h1 := congrArg (fun L => L[t]?) (R3_fst F (frule F))
  simp only [List.getElem?_map, htc, Option.map_some] at h1
  have ht : t < (F.filterMap FFac.entData).length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at h1
    simp at h1
  refine ⟨t, ht, htc, ?_⟩
  rw [List.getElem?_eq_getElem ht] at h1
  exact Option.some.inj h1

/-- The uses of the four labels after `k + 1` steps. -/
private theorem R3_capsum (F : List FFac) (k t : ℕ) (d : FEnt) (o : FOpt)
    (hlab : d.1 < 4 ∧ d.2.1 < 4)
    (ht : (fruleOrd (F.filterMap FFac.entData))[k]? = some t)
    (hc : (fchosen F (frule F))[t]? = some (d, some o)) :
    ((List.range 4).map fun l =>
      ((fruleCap (F.filterMap FFac.entData) false (k + 1)).getD l 0 : ℤ)).sum =
      ((List.range 4).map fun l =>
        ((fruleCap (F.filterMap FFac.entData) false k).getD l 0 : ℤ)).sum + R3u d o := by
  have h1 := R3_U [(d, some o)] fun c hc => by
    simp only [List.mem_singleton] at hc; subst hc; exact hlab
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, R3U] at h1
  rw [← h1]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.cons_append]
  rw [R3_cap_succ F k t 0 (by norm_num) d o ht hc, R3_cap_succ F k t 1 (by norm_num) d o ht hc,
    R3_cap_succ F k t 2 (by norm_num) d o ht hc, R3_cap_succ F k t 3 (by norm_num) d o ht hc]
  push_cast
  ring

/-- The final uses of the four labels are at least those after `k` steps. -/
private theorem R3_Uge (F : List FFac) (k : ℕ) (hk : k ≤ (F.filterMap FFac.entData).length) :
    ((List.range 4).map fun l =>
      ((fruleCap (F.filterMap FFac.entData) false k).getD l 0 : ℤ)).sum ≤
      ((List.range 4).map fun l => (fuses F (frule F) l : ℤ)).sum := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.cons_append]
  have h0 := R3_cap_le F k 0 (by norm_num) hk
  have h1 := R3_cap_le F k 1 (by norm_num) hk
  have h2 := R3_cap_le F k 2 (by norm_num) hk
  have h3 := R3_cap_le F k 3 (by norm_num) hk
  unfold frule
  omega

/-- The uses of the four labels before the first step. -/
private theorem R3_cap0 (E : List FEnt) (l : ℕ) : (fruleCap E false 0).getD l 0 = 0 := by
  rw [(frule_run_mono E false 0 0 l le_rfl).1]
  rcases l with _ | _ | _ | _ | l <;> rfl

/-- The role of an entry without `Λ̃`. -/
private theorem R3_role_free (d : FEnt) (h : d.2.2.1.length = 1) : 2 ≤ d.role := by
  unfold FEnt.role
  split_ifs <;> omega

/-- An entry without `Λ̃`, with a resolvent and labels below `4`, has role `2` exactly when one
label is inner and the other outer. -/
private theorem R3_role_two (d : FEnt) (h : d.2.2.1.length = 1) (hr : 1 ≤ d.2.2.1.sum)
    (hl : d.1 < 4 ∧ d.2.1 < 4) :
    d.role = 2 ↔ (2 ≤ d.1 ∧ d.1 < 4 ∧ d.2.1 < 2) ∨ (2 ≤ d.2.1 ∧ d.2.1 < 4 ∧ d.1 < 2) := by
  have h2 : ¬ 2 ≤ d.2.2.1.length := by omega
  unfold FEnt.role
  simp only [h2, ↓reduceIte, fInnerL, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    decide_eq_decide]
  split_ifs with h1 <;> omega

/-- The entry treated at step `k` takes the first kind of its list that fits. -/
private theorem R3_step_at (F : List FFac) (k t : ℕ)
    (hk : (fruleOrd (F.filterMap FFac.entData))[k]? = some t) :
    ∃ ht : t < (F.filterMap FFac.entData).length, ∃ kd o,
      fruleFit (fruleCap (F.filterMap FFac.entData) false k)
        ((F.filterMap FFac.entData)[t]) false = some (kd, o) ∧
      (fchosen F (frule F))[t]? = some ((F.filterMap FFac.entData)[t], some o) := by
  have ht : t < (F.filterMap FFac.entData).length := by
    have hmem : t ∈ fruleOrd (F.filterMap FFac.entData) := List.mem_of_getElem? hk
    exact List.mem_range.1 ((frule_run_order _).1.subset hmem)
  have hd : (F.filterMap FFac.entData)[t]? = some ((F.filterMap FFac.entData)[t]) :=
    List.getElem?_eq_getElem ht
  obtain ⟨⟨kd, o⟩, hfit⟩ := Option.isSome_iff_exists.1 (frule_run_fits F false k t _ hk hd)
  obtain ⟨-, -, h3⟩ := frule_run_chosen F false k t _ hk hd kd o hfit
  exact ⟨ht, kd, o, hfit, h3⟩

/-- The bounds of all chosen entries from those of the entries at their steps. -/
private theorem R3_PP_of (F : List FFac)
    (h : ∀ t (ht : t < (F.filterMap FFac.entData).length) k kd o,
      (fruleOrd (F.filterMap FFac.entData))[k]? = some t →
      fruleFit (fruleCap (F.filterMap FFac.entData) false k)
        ((F.filterMap FFac.entData)[t]) false = some (kd, o) →
      kd ∈ FEnt.prefs ((F.filterMap FFac.entData)[t]) false →
      fkindOpt ((F.filterMap FFac.entData)[t]) kd = some o →
      ∀ q ∈ o.val, R3PP ((F.filterMap FFac.entData)[t]) o q) :
    ∀ c ∈ fchosen F (frule F), ∀ o, c.2 = some o → ∀ q ∈ o.val, R3PP c.1 o q := by
  intro c hc o hco q hq
  obtain ⟨t, ht, htc, hc1⟩ := R3_chosen_mem F c hc
  obtain ⟨k, kd, o', hk, hfit, hkd, hko, hch⟩ := R3_step F t ht
  rw [htc, Option.some.injEq] at hch
  subst hch
  simp only [Option.some.injEq] at hco
  rw [← hco] at hq ⊢
  exact h t ht k kd o' hk hfit hkd hko q hq

/-- The bounds of an entry without `Λ̃`. -/
private theorem R3PP_free' (d : FEnt) (h1 : d.2.2.1.length = 1) (hr : 1 ≤ d.2.2.1.sum)
    (he : d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧ d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧
      0 ≤ d.2.2.2.1.i) (k : FKind) (hk : k ∈ FEnt.prefs d false) (o : FOpt)
    (ho : fkindOpt d k = some o) (q : FMono) (hq : q ∈ o.val) : R3PP d o q := by
  obtain ⟨x, y, parts, ext, det⟩ := d
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.1 h1
  simp only [List.sum_cons, List.sum_nil, add_zero] at hr
  exact R3PP_free x y r ext det hr he k hk o ho q hq

/-- The number of outer ends of an entry. -/
private def R3out (d : FEnt) : ℕ := [d.1, d.2.1].count 0 + [d.1, d.2.1].count 1

private theorem R3out_eq (d : FEnt) :
    R3out d = (if d.1 < 2 then 1 else 0) + (if d.2.1 < 2 then 1 else 0) := by
  unfold R3out
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

/-- The outer ends of the entries are the ends at the labels `0, 1`. -/
private theorem R3out_sum (E : List FEnt) :
    (E.map R3out).sum = (E.flatMap fun d => [d.1, d.2.1]).count 0 +
      (E.flatMap fun d => [d.1, d.2.1]).count 1 := by
  rw [List.count_flatMap, List.count_flatMap, ← List.sum_map_add]
  rfl

private theorem R3_even (L : List FEnt) (hc : ∀ d ∈ L, R3out d ≠ 1) :
    (L.map R3out).sum % 2 = 0 := by
  induction L with
  | nil => simp
  | cons d L ih =>
    have h1 := hc d List.mem_cons_self
    have h2 := ih (fun d' hd' => hc d' (List.mem_cons_of_mem _ hd'))
    have h3 : R3out d ≤ 2 := by rw [R3out_eq]; split_ifs <;> omega
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A list of entries with an odd number of outer ends has an entry with exactly one. -/
private theorem R3_odd (L : List FEnt) (h : (L.map R3out).sum % 2 = 1) :
    ∃ d ∈ L, R3out d = 1 := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have := R3_even L hc
  omega

/-- A sum over a list is the value at a member and the sum over the rest. -/
private theorem R3_sum_erase {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (a : α) (ha : a ∈ L)
    (h : α → ℤ) : (L.map h).sum = h a + ((L.erase a).map h).sum := by
  rw [((List.perm_cons_erase ha).map h).sum_eq]
  simp

private theorem R3_sum_erase_nat {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (a : α) (ha : a ∈ L)
    (h : α → ℕ) : (L.map h).sum = h a + ((L.erase a).map h).sum := by
  rw [((List.perm_cons_erase ha).map h).sum_eq]
  simp

/-- The roles do not decrease along the order of the rule. -/
private theorem R3_role_le (E : List FEnt) (k k' t t' : ℕ) (h : k ≤ k')
    (ht : (fruleOrd E)[k]? = some t) (ht' : (fruleOrd E)[k']? = some t') :
    (E.getD t FEnt.dflt).role ≤ (E.getD t' FEnt.dflt).role := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · rw [ht] at ht'; cases ht'; exact le_rfl
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 ht
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 ht'
  exact List.pairwise_iff_getElem.1 (frule_run_order E).2 k k' hk hk' h

/-- The step `k` exists below the number of entries. -/
private theorem R3_ord_some (E : List FEnt) (k : ℕ) (hk : k < E.length) :
    ∃ t, (fruleOrd E)[k]? = some t := by
  have hl : (fruleOrd E).length = E.length := by
    rw [(frule_run_order E).1.length_eq, List.length_range]
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- The sum of the uses of the four labels at the ends `x, y` of an entry used once each. -/
private theorem R3_sum2 (x y : ℕ) (hx : x < 4) (hy : y < 4) :
    ((List.range 4).map fun l => ((if x = l then 1 else 0) + (if y = l then 1 else 0) : ℤ)).sum =
      2 := by
  interval_cases x <;> interval_cases y <;> decide

/-- The first role-`2` entry after `n` entries of roles `0, 1` takes its Ward row or column when
its labels have at most one use, and adds it to the uses. -/
private theorem R3_ward_step (F : List FFac) (n t₂ : ℕ)
    (hn : (F.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 1)) = n)
    (hfree : ∀ d ∈ F.filterMap FFac.entData, 2 ≤ FEnt.role d → d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum)
    (hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4)
    (ht₂ : t₂ < (F.filterMap FFac.entData).length)
    (hr₂ : FEnt.role ((F.filterMap FFac.entData)[t₂]) = 2)
    (hcap : ∀ t (ht : t < (F.filterMap FFac.entData).length),
      FEnt.role ((F.filterMap FFac.entData)[t]) = 2 →
      (fruleCap (F.filterMap FFac.entData) false n).getD ((F.filterMap FFac.entData)[t]).1 0 ≤ 1 ∧
      (fruleCap (F.filterMap FFac.entData) false n).getD ((F.filterMap FFac.entData)[t]).2.1 0 ≤ 1)
    (hlen : n + 1 ≤ (F.filterMap FFac.entData).length) :
    ((List.range 4).map fun l =>
      ((fruleCap (F.filterMap FFac.entData) false n).getD l 0 : ℤ)).sum + 1 ≤
      ((List.range 4).map fun l => (fuses F (frule F) l : ℤ)).sum := by
  obtain ⟨k₂, -, -, hk₂, -⟩ := R3_step F t₂ ht₂
  obtain ⟨t, ht⟩ := R3_ord_some (F.filterMap FFac.entData) n (by omega)
  obtain ⟨htl, kd, o, hfit, hch⟩ := R3_step_at F n t ht
  have hgetD : ∀ t' (h : t' < (F.filterMap FFac.entData).length),
      (F.filterMap FFac.entData).getD t' FEnt.dflt = (F.filterMap FFac.entData)[t'] :=
    fun t' h => List.getD_eq_getElem _ _ h
  have hk₂n : n ≤ k₂ := R3_pos' _ 1 n k₂ t₂ hn hk₂ (by rw [hgetD t₂ ht₂, hr₂]; omega)
  have hrole : FEnt.role ((F.filterMap FFac.entData)[t]) = 2 := by
    have h1 := R3_role_le _ n k₂ t t₂ (by omega) ht hk₂
    rw [hgetD t htl, hgetD t₂ ht₂, hr₂] at h1
    by_contra h2
    have := R3_pos _ 1 n n t hn ht (by rw [hgetD t htl]; omega)
    omega
  obtain ⟨hl1, hs1⟩ := hfree _ (List.getElem_mem htl) (by omega)
  have hlb := hlab _ (List.getElem_mem htl)
  obtain ⟨c1, c2⟩ := hcap t htl hrole
  have hw := (R3_role_two _ hl1 hs1 hlb).1 hrole
  have hsum := R3_capsum F n t _ o hlb ht hch
  generalize hd : (F.filterMap FFac.entData)[t] = d at hfit hl1 hs1 hw c1 c2 hsum
  obtain ⟨x, y, parts, e, det⟩ := d
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.1 hl1
  have hu := R3_fit_ward x y r e det hw _ c1 c2 kd o hfit
  rw [hu] at hsum
  have := R3_Uge F (n + 1) hlen
  omega

/-! ### The three shapes of case (8) and case (9) -/

/-- The entry of role `0` is treated first, with the uses `0`. -/
private theorem R3_first (F : List FFac) (P : FEnt) (hP : P ∈ F.filterMap FFac.entData)
    (hP0 : FEnt.role P = 0)
    (hrole : (F.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 0)) = 1) :
    ∃ tP, ∃ htP : tP < (F.filterMap FFac.entData).length,
      (F.filterMap FFac.entData)[tP] = P ∧ (fruleOrd (F.filterMap FFac.entData))[0]? = some tP ∧
      ∃ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 0) P false = some (kd, o) ∧
        (fchosen F (frule F))[tP]? = some (P, some o) := by
  obtain ⟨tP, htP, hEtP⟩ := List.getElem_of_mem hP
  obtain ⟨kP, kd, o, hkP, hfit, -, -, hch⟩ := R3_step F tP htP
  have : kP < 1 := R3_pos _ 0 1 kP tP hrole hkP (by rw [List.getD_eq_getElem _ _ htP, hEtP, hP0])
  have hk0 : kP = 0 := by omega
  subst hk0
  rw [hEtP] at hfit hch
  exact ⟨tP, htP, hEtP, hkP, kd, o, hfit, hch⟩

/-- Case (8) with both letters `Λ̃` in one entry `(x₀, 3)`, `x₀` outer, parts `[0, r, 0]`. -/
private theorem R3_case_b (F : List FFac) (x₀ r : ℕ) (eP : FMono) (dP : Bool)
    (hP : (x₀, 3, [0, r, 0], eP, dP) ∈ F.filterMap FFac.entData) (hx₀ : x₀ < 2) (hr : 1 ≤ r)
    (hfree : ∀ d ∈ F.filterMap FFac.entData, d ≠ (x₀, 3, [0, r, 0], eP, dP) →
      d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum)
    (hext : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i)
    (hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4)
    (hrole : (F.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 0)) = 1)
    (hends : ((F.filterMap FFac.entData).map R3out).sum = 6) :
    (∀ c ∈ fchosen F (frule F), ∀ o, c.2 = some o → ∀ q ∈ o.val, R3PP c.1 o q) ∧
      3 ≤ ((List.range 4).map fun l => (fuses F (frule F) l : ℤ)).sum ∧
      ((F.filterMap FFac.entData).map R3zz).sum = 0 ∧
      (2 ≤ r → 1 ≤ ((F.filterMap FFac.entData).map R3bb).sum) ∧
      ((F.filterMap FFac.entData).map R3nl).sum = 2 := by
  have hP0 : FEnt.role (x₀, 3, [0, r, 0], eP, dP) = 0 := by
    simp [FEnt.role, fInnerL]
  have hc := (List.perm_cons_erase hP).countP_eq (fun d => decide (FEnt.role d ≤ 0))
  rw [hrole, List.countP_cons, hP0] at hc
  simp only [le_refl, decide_true, ↓reduceIte] at hc
  have hc0 : ((F.filterMap FFac.entData).erase (x₀, 3, [0, r, 0], eP, dP)).countP
      (fun d => decide (FEnt.role d ≤ 0)) = 0 := by omega
  have hrest : ∀ d ∈ (F.filterMap FFac.entData).erase (x₀, 3, [0, r, 0], eP, dP),
      d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum := by
    intro d hd
    have hne : d ≠ (x₀, 3, [0, r, 0], eP, dP) := by
      rintro rfl
      exact (List.countP_eq_zero.1 hc0 _ hd) (by simp [hP0])
    exact hfree d (List.mem_of_mem_erase hd) hne
  have hzero : ∀ (h : FEnt → ℤ), (∀ d, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum → h d = 0) →
      ((F.filterMap FFac.entData).map h).sum = h (x₀, 3, [0, r, 0], eP, dP) := by
    intro h hh
    rw [R3_sum_erase _ _ hP h, List.sum_eq_zero, add_zero]
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    exact hh d (hrest d hd).1 (hrest d hd).2
  obtain ⟨tP, htP, hEtP, hord0, kdP, oP, hfitP, hchP⟩ := R3_first F _ hP hP0 hrole
  have hdbl := R3_fit_dbl x₀ 3 r eP dP (by omega) hr (hext _ hP) _
    (by rw [R3_cap0]; omega) (by rw [R3_cap0]; omega) kdP oP hfitP
  refine ⟨R3_PP_of F fun t ht k kd o hk hfit hkd hko q hq => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hdt : (F.filterMap FFac.entData)[t] = (x₀, 3, [0, r, 0], eP, dP)
    · have : k < 1 := R3_pos _ 0 1 k t hrole hk
        (by rw [List.getD_eq_getElem _ _ ht, hdt, hP0])
      have hk0 : k = 0 := by omega
      subst hk0
      rw [hdt] at hfit ⊢
      exact (R3_fit_dbl x₀ 3 r eP dP (by omega) hr (hext _ hP) _
        (by rw [R3_cap0]; omega) (by rw [R3_cap0]; omega) kd o hfit).1 q hq
    · obtain ⟨h1, h2⟩ := hfree _ (List.getElem_mem ht) hdt
      exact R3PP_free' _ h1 h2 (hext _ (List.getElem_mem ht)) kd hkd o hko q hq
  · -- an entry of role `2` exists by the parity of the outer ends
    have hout := R3_sum_erase_nat _ _ hP R3out
    rw [hends, R3out_eq] at hout
    simp only [hx₀, ↓reduceIte, show ¬ (3 : ℕ) < 2 by omega] at hout
    obtain ⟨d₂, hd₂, h₂⟩ := R3_odd ((F.filterMap FFac.entData).erase (x₀, 3, [0, r, 0], eP, dP))
      (by omega)
    obtain ⟨hl₂, hs₂⟩ := hrest d₂ hd₂
    have hd₂E := List.mem_of_mem_erase hd₂
    have hr₂ : FEnt.role d₂ = 2 := by
      rw [R3_role_two _ hl₂ hs₂ (hlab _ hd₂E)]
      rw [R3out_eq] at h₂
      have := hlab _ hd₂E
      split_ifs at h₂ <;> omega
    obtain ⟨t₂, ht₂, hEt₂⟩ := List.getElem_of_mem hd₂E
    have hn1 : (F.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 1)) = 1 := by
      have hc1 := (List.perm_cons_erase hP).countP_eq (fun d => decide (FEnt.role d ≤ 1))
      rw [List.countP_cons, hP0] at hc1
      simp only [zero_le, decide_true, ↓reduceIte] at hc1
      rw [hc1, List.countP_eq_zero.2]
      intro d hd
      have := R3_role_free d (hrest d hd).1
      simp only [decide_eq_true_eq]
      omega
    have hlen : 2 ≤ (F.filterMap FFac.entData).length := by
      have h1 := (List.perm_cons_erase hP).length_eq
      have h2 : 1 ≤ ((F.filterMap FFac.entData).erase (x₀, 3, [0, r, 0], eP, dP)).length :=
        List.length_pos_of_mem hd₂
      rw [h1, List.length_cons]
      omega
    have hcap1 : ∀ l, l < 4 → (fruleCap (F.filterMap FFac.entData) false 1).getD l 0 =
        (if x₀ = l then 1 else 0) + (if 3 = l then 1 else 0) := by
      intro l hl
      rw [R3_cap_succ F 0 tP l hl _ oP hord0 hchP, R3_cap0, hdbl.2 l]
      omega
    have hw := R3_ward_step F 1 t₂ hn1 (fun d hd h2 => by
        by_cases hdP : d = (x₀, 3, [0, r, 0], eP, dP)
        · subst hdP; omega
        · exact hfree d hd hdP) hlab ht₂ (by rw [hEt₂, hr₂])
      (fun t ht _ => by
        have hl := hlab _ (List.getElem_mem ht)
        rw [hcap1 _ hl.1, hcap1 _ hl.2]
        constructor <;> split_ifs <;> omega) hlen
    have hsum1 : ((List.range 4).map fun l =>
        ((fruleCap (F.filterMap FFac.entData) false 1).getD l 0 : ℤ)).sum = 2 := by
      rw [← R3_sum2 x₀ 3 (by omega) (by omega)]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.cons_append]
      rw [hcap1 0 (by norm_num), hcap1 1 (by norm_num), hcap1 2 (by norm_num),
        hcap1 3 (by norm_num)]
      push_cast
      ring
    omega
  · rw [hzero R3zz fun d _ h => by unfold R3zz; simp; omega]
    unfold R3zz; simp; omega
  · intro h2
    have hge : R3bb (x₀, 3, [0, r, 0], eP, dP) ≤ ((F.filterMap FFac.entData).map R3bb).sum := by
      rw [R3_sum_erase _ _ hP R3bb]
      have : 0 ≤ (((F.filterMap FFac.entData).erase (x₀, 3, [0, r, 0], eP, dP)).map R3bb).sum :=
        List.sum_nonneg fun x hx => by
          obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
          unfold R3bb; split_ifs <;> simp
      omega
    have : R3bb (x₀, 3, [0, r, 0], eP, dP) = 1 := by
      unfold R3bb; simp; omega
    omega
  · rw [hzero R3nl fun d h _ => by unfold R3nl; omega]
    unfold R3nl; simp

/-- Two entries with one letter `Λ̃` each, of roles `0` and `1`, and the rest without `Λ̃`: the
rest, the counts of the roles, and the sums over the entries. -/
private theorem R3_two (E : List FEnt) (P Λ : FEnt) (hP : P ∈ E) (hΛ : Λ ∈ E)
    (hP0 : FEnt.role P = 0) (hΛ1 : FEnt.role Λ = 1) (hPl : P.2.2.1.length = 2)
    (hΛl : Λ.2.2.1.length = 2)
    (hfree : ∀ d ∈ E, d ≠ P → d ≠ Λ → d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum)
    (hnl : (E.map R3nl).sum ≤ 2) :
    (∀ d ∈ (E.erase P).erase Λ, d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum) ∧
      (∀ h : FEnt → ℤ, (E.map h).sum = h P + h Λ + (((E.erase P).erase Λ).map h).sum) ∧
      (∀ h : FEnt → ℕ, (E.map h).sum = h P + h Λ + (((E.erase P).erase Λ).map h).sum) ∧
      E.countP (fun d => decide (FEnt.role d ≤ 0)) = 1 ∧
      E.countP (fun d => decide (FEnt.role d ≤ 1)) = 2 ∧
      (∀ d ∈ E, d ≠ P → d ≠ Λ → d ∈ (E.erase P).erase Λ) := by
  have hne : Λ ≠ P := by rintro rfl; rw [hP0] at hΛ1; exact absurd hΛ1 (by decide)
  have hΛ' : Λ ∈ E.erase P := (List.mem_erase_of_ne hne).2 hΛ
  have hsZ : ∀ h : FEnt → ℤ, (E.map h).sum = h P + h Λ + (((E.erase P).erase Λ).map h).sum := by
    intro h
    rw [R3_sum_erase _ _ hP h, R3_sum_erase _ _ hΛ' h]
    ring
  have hsN : ∀ h : FEnt → ℕ, (E.map h).sum = h P + h Λ + (((E.erase P).erase Λ).map h).sum := by
    intro h
    rw [R3_sum_erase_nat _ _ hP h, R3_sum_erase_nat _ _ hΛ' h]
    ring
  have hrest : ∀ d ∈ (E.erase P).erase Λ, d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum := by
    intro d hd
    have hdE : d ∈ E := List.mem_of_mem_erase (List.mem_of_mem_erase hd)
    by_cases h1 : d = P
    · exfalso
      have h0 : ∀ x ∈ (((E.erase P).erase Λ).erase d), 0 ≤ R3nl x := by
        intro x hx
        have hxE : x ∈ E :=
          List.mem_of_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
        unfold R3nl
        by_cases hx1 : x = P
        · subst hx1; rw [hPl]; norm_num
        by_cases hx2 : x = Λ
        · subst hx2; rw [hΛl]; norm_num
        rw [(hfree x hxE hx1 hx2).1]; norm_num
      have := R3_sum_erase _ _ hd R3nl
      have h3 : 0 ≤ ((((E.erase P).erase Λ).erase d).map R3nl).sum :=
        List.sum_nonneg fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact h0 y hy
      have h4 := hsZ R3nl
      have eP : R3nl P = 1 := by unfold R3nl; rw [hPl]; norm_num
      have eΛ : R3nl Λ = 1 := by unfold R3nl; rw [hΛl]; norm_num
      subst h1
      omega
    by_cases h2 : d = Λ
    · exfalso
      have h0 : ∀ x ∈ (((E.erase P).erase Λ).erase d), 0 ≤ R3nl x := by
        intro x hx
        have hxE : x ∈ E :=
          List.mem_of_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
        unfold R3nl
        by_cases hx1 : x = P
        · subst hx1; rw [hPl]; norm_num
        by_cases hx2 : x = Λ
        · subst hx2; rw [hΛl]; norm_num
        rw [(hfree x hxE hx1 hx2).1]; norm_num
      have := R3_sum_erase _ _ hd R3nl
      have h3 : 0 ≤ ((((E.erase P).erase Λ).erase d).map R3nl).sum :=
        List.sum_nonneg fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact h0 y hy
      have h4 := hsZ R3nl
      have eP : R3nl P = 1 := by unfold R3nl; rw [hPl]; norm_num
      have eΛ : R3nl Λ = 1 := by unfold R3nl; rw [hΛl]; norm_num
      subst h2
      omega
    exact hfree d hdE h1 h2
  have hcount : ∀ ρ : ℕ, E.countP (fun d => decide (FEnt.role d ≤ ρ)) =
      (if FEnt.role P ≤ ρ then 1 else 0) + (if FEnt.role Λ ≤ ρ then 1 else 0) +
        ((E.erase P).erase Λ).countP (fun d => decide (FEnt.role d ≤ ρ)) := by
    intro ρ
    rw [(List.perm_cons_erase hP).countP_eq, List.countP_cons,
      (List.perm_cons_erase hΛ').countP_eq, List.countP_cons]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  have hz : ∀ ρ, ρ ≤ 1 → ((E.erase P).erase Λ).countP (fun d => decide (FEnt.role d ≤ ρ)) = 0 := by
    intro ρ hρ
    rw [List.countP_eq_zero]
    intro d hd
    have := R3_role_free d (hrest d hd).1
    simp only [decide_eq_true_eq]
    omega
  refine ⟨hrest, hsZ, hsN, ?_, ?_, fun d hd h1 h2 =>
    (List.mem_erase_of_ne h2).2 ((List.mem_erase_of_ne h1).2 hd)⟩
  · rw [hcount 0, hz 0 (by norm_num), hP0, hΛ1]; rfl
  · rw [hcount 1, hz 1 le_rfl, hP0, hΛ1]; rfl

/-- The entry of role `1` is treated second, after the entry of role `0`. -/
private theorem R3_second (F : List FFac) (Λ : FEnt) (hΛ : Λ ∈ F.filterMap FFac.entData)
    (hΛ1 : FEnt.role Λ = 1)
    (h0 : (F.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 0)) = 1)
    (h1 : (F.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 1)) = 2) :
    ∃ tΛ, ∃ htΛ : tΛ < (F.filterMap FFac.entData).length,
      (F.filterMap FFac.entData)[tΛ] = Λ ∧ (fruleOrd (F.filterMap FFac.entData))[1]? = some tΛ ∧
      ∃ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 1) Λ false = some (kd, o) ∧
        (fchosen F (frule F))[tΛ]? = some (Λ, some o) := by
  obtain ⟨tΛ, htΛ, hEt⟩ := List.getElem_of_mem hΛ
  obtain ⟨k, kd, o, hk, hfit, -, -, hch⟩ := R3_step F tΛ htΛ
  have a1 : k < 2 := R3_pos _ 1 2 k tΛ h1 hk (by rw [List.getD_eq_getElem _ _ htΛ, hEt, hΛ1])
  have a2 : 1 ≤ k :=
    R3_pos' _ 0 1 k tΛ h0 hk (by rw [List.getD_eq_getElem _ _ htΛ, hEt, hΛ1]; omega)
  have hk1 : k = 1 := by omega
  subst hk1
  rw [hEt] at hfit hch
  exact ⟨tΛ, htΛ, hEt, hk, kd, o, hfit, hch⟩

/-- Case (8) with the letters `Λ̃` in two entries: `(ℓ₂, 3)` with parts `[r_R, 0]` (`Λ̃₂`) and
`(x₀, ℓ₁)` with parts `[0, r_L]` (`Λ̃₁`), `x₀` outer, `ℓ₁, ℓ₂` inner. -/
private theorem R3_case_a (F : List FFac) (s ℓ₂ rR x₀ ℓ₁ rL : ℕ) (eP eL : FMono) (dP dL : Bool)
    (hP : (ℓ₂, 3, [rR, 0], eP, dP) ∈ F.filterMap FFac.entData)
    (hΛ : (x₀, ℓ₁, [0, rL], eL, dL) ∈ F.filterMap FFac.entData)
    (hℓ₂ : 2 ≤ ℓ₂ ∧ ℓ₂ < 4) (hrR : 1 ≤ rR) (hx₀ : x₀ < 2) (hℓ₁ : 2 ≤ ℓ₁ ∧ ℓ₁ < 4) (hrL : 1 ≤ rL)
    (hfree : ∀ d ∈ F.filterMap FFac.entData, d ≠ (ℓ₂, 3, [rR, 0], eP, dP) →
      d ≠ (x₀, ℓ₁, [0, rL], eL, dL) → d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum)
    (hnl : ((F.filterMap FFac.entData).map R3nl).sum ≤ 2)
    (hext : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i)
    (hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4)
    (hends : ((F.filterMap FFac.entData).map R3out).sum = 6)
    (h3 : ((F.filterMap FFac.entData).flatMap fun d => [d.1, d.2.1]).count 3 = 1 + s) :
    (∀ c ∈ fchosen F (frule F), ∀ o, c.2 = some o → ∀ q ∈ o.val, R3PP c.1 o q) ∧
      3 ≤ ((List.range 4).map fun l => (fuses F (frule F) l : ℤ)).sum ∧
      (4 ≤ ((List.range 4).map fun l => (fuses F (frule F) l : ℤ)).sum ∨ 3 ≤ s) ∧
      ((F.filterMap FFac.entData).map R3zz).sum = 0 ∧
      ((F.filterMap FFac.entData).map R3nl).sum = 2 := by
  have hrR0 : rR ≠ 0 := by omega
  have hrL0 : rL ≠ 0 := by omega
  have hP0 : FEnt.role (ℓ₂, 3, [rR, 0], eP, dP) = 0 := by simp [FEnt.role, fInnerL, hrR0]
  have hΛ1 : FEnt.role (x₀, ℓ₁, [0, rL], eL, dL) = 1 := by
    simp [FEnt.role, fInnerL, hrL0]; omega
  obtain ⟨hrest, hsZ, hsN, h0, h1, hmemR⟩ := R3_two _ _ _ hP hΛ hP0 hΛ1 rfl rfl hfree hnl
  -- the entry `(ℓ₂, 3)` at step `0`
  have hP_fit : ∀ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 0)
      (ℓ₂, 3, [rR, 0], eP, dP) false = some (kd, o) →
      (∀ q ∈ o.val, R3PP (ℓ₂, 3, [rR, 0], eP, dP) o q) ∧
      (∀ l, fuseOne ((ℓ₂, 3, [rR, 0], eP, dP), some o) l =
        (if ℓ₂ = 2 then (if 2 = l then 1 else 0) else 0) + (if 3 = l then 1 else 0)) := by
    intro kd o hfit
    rcases (show ℓ₂ = 2 ∨ ℓ₂ = 3 by omega) with rfl | rfl
    · obtain ⟨a, b⟩ := R3_fit_hs 2 3 rR 0 eP dP (by omega) (hext _ hP) _ (by rw [R3_cap0]; omega)
        (by rw [R3_cap0]; omega) kd o hfit
      exact ⟨a, fun l => by rw [b l]; simp⟩
    · obtain ⟨a, b⟩ := R3_fit_isoY 3 rR eP dP hrR (hext _ hP) _ (by rw [R3_cap0]; omega) kd o hfit
      exact ⟨a, fun l => by rw [b l]; simp⟩
  obtain ⟨tP, htP, hEtP, hord0, kdP, oP, hfitP, hchP⟩ := R3_first F _ hP hP0 h0
  obtain ⟨hPP_P, hfuseP⟩ := hP_fit kdP oP hfitP
  have hcap1 : ∀ l, l < 4 → (fruleCap (F.filterMap FFac.entData) false 1).getD l 0 =
      (if ℓ₂ = 2 then (if 2 = l then 1 else 0) else 0) + (if 3 = l then 1 else 0) := by
    intro l hl
    rw [R3_cap_succ F 0 tP l hl _ oP hord0 hchP, R3_cap0, hfuseP l]
    omega
  have hΛ_fit : ∀ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 1)
      (x₀, ℓ₁, [0, rL], eL, dL) false = some (kd, o) →
      (∀ q ∈ o.val, R3PP (x₀, ℓ₁, [0, rL], eL, dL) o q) ∧
      ∀ l, fuseOne ((x₀, ℓ₁, [0, rL], eL, dL), some o) l =
        (if x₀ = l then 1 else 0) + (if ℓ₁ = l then 1 else 0) := by
    intro kd o hfit
    exact R3_fit_hs x₀ ℓ₁ 0 rL eL dL (by omega) (hext _ hΛ) _
      (by rw [hcap1 _ (by omega)]; split_ifs <;> omega)
      (by rw [hcap1 _ (by omega)]; split_ifs <;> omega) kd o hfit
  obtain ⟨tΛ, htΛ, hEtΛ, hord1, kdΛ, oΛ, hfitΛ, hchΛ⟩ := R3_second F _ hΛ hΛ1 h0 h1
  obtain ⟨hPP_Λ, hfuseΛ⟩ := hΛ_fit kdΛ oΛ hfitΛ
  have hcap2 : ∀ l, l < 4 → (fruleCap (F.filterMap FFac.entData) false 2).getD l 0 =
      (if ℓ₂ = 2 then (if 2 = l then 1 else 0) else 0) + (if 3 = l then 1 else 0) +
        (if x₀ = l then 1 else 0) + (if ℓ₁ = l then 1 else 0) := by
    intro l hl
    rw [R3_cap_succ F 1 tΛ l hl _ oΛ hord1 hchΛ, hcap1 l hl, hfuseΛ l]
    omega
  have hsum2 : ((List.range 4).map fun l =>
      ((fruleCap (F.filterMap FFac.entData) false 2).getD l 0 : ℤ)).sum =
        (if ℓ₂ = 2 then 4 else 3) := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.cons_append]
    rw [hcap2 0 (by norm_num), hcap2 1 (by norm_num), hcap2 2 (by norm_num),
      hcap2 3 (by norm_num)]
    rcases (show ℓ₂ = 2 ∨ ℓ₂ = 3 by omega) with rfl | rfl <;>
    rcases (show x₀ = 0 ∨ x₀ = 1 by omega) with rfl | rfl <;>
    rcases (show ℓ₁ = 2 ∨ ℓ₁ = 3 by omega) with rfl | rfl <;> decide
  have hlen2 : 2 ≤ (F.filterMap FFac.entData).length := by
    have := (List.getElem?_eq_some_iff.1 hord1).1
    rw [(frule_run_order _).1.length_eq, List.length_range] at this
    omega
  have hU2 := R3_Uge F 2 hlen2
  refine ⟨R3_PP_of F fun t ht k kd o hk hfit hkd hko q hq => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hdP : (F.filterMap FFac.entData)[t] = (ℓ₂, 3, [rR, 0], eP, dP)
    · have : k < 1 := R3_pos _ 0 1 k t h0 hk (by rw [List.getD_eq_getElem _ _ ht, hdP, hP0])
      have hk0 : k = 0 := by omega
      subst hk0
      rw [hdP] at hfit ⊢
      exact (hP_fit kd o hfit).1 q hq
    by_cases hdΛ : (F.filterMap FFac.entData)[t] = (x₀, ℓ₁, [0, rL], eL, dL)
    · have a1 : k < 2 := R3_pos _ 1 2 k t h1 hk
        (by rw [List.getD_eq_getElem _ _ ht, hdΛ, hΛ1])
      have a2 : 1 ≤ k := R3_pos' _ 0 1 k t h0 hk
        (by rw [List.getD_eq_getElem _ _ ht, hdΛ, hΛ1]; omega)
      have hk1 : k = 1 := by omega
      subst hk1
      rw [hdΛ] at hfit ⊢
      exact (hΛ_fit kd o hfit).1 q hq
    obtain ⟨a, b⟩ := hfree _ (List.getElem_mem ht) hdP hdΛ
    exact R3PP_free' _ a b (hext _ (List.getElem_mem ht)) kd hkd o hko q hq
  · split_ifs at hsum2 <;> omega
  · rcases (show ℓ₂ = 2 ∨ ℓ₂ = 3 by omega) with rfl | rfl
    · left
      rw [show (if (2 : ℕ) = 2 then (4 : ℤ) else 3) = 4 from rfl] at hsum2
      omega
    rcases Nat.lt_or_ge s 3 with hs | hs
    swap
    · exact Or.inr hs
    left
    -- `s ≤ 2`: the first entry of role `2` takes its Ward row or column
    have hout := hsN R3out
    rw [hends, R3out_eq, R3out_eq] at hout
    simp only [show ¬ (3 : ℕ) < 2 by omega, hx₀, show ¬ ℓ₁ < 2 by omega, ↓reduceIte] at hout
    obtain ⟨d₂, hd₂, h₂⟩ := R3_odd (((F.filterMap FFac.entData).erase (3, 3, [rR, 0], eP, dP)).erase
      (x₀, ℓ₁, [0, rL], eL, dL)) (by omega)
    obtain ⟨hl₂, hs₂⟩ := hrest d₂ hd₂
    have hd₂E := List.mem_of_mem_erase (List.mem_of_mem_erase hd₂)
    have hr₂ : FEnt.role d₂ = 2 := by
      rw [R3_role_two _ hl₂ hs₂ (hlab _ hd₂E)]
      rw [R3out_eq] at h₂
      have := hlab _ hd₂E
      split_ifs at h₂ <;> omega
    obtain ⟨t₂, ht₂, hEt₂⟩ := List.getElem_of_mem hd₂E
    have hc3 : (((F.filterMap FFac.entData).map fun d => [d.1, d.2.1].count 3).sum) = 1 + s := by
      rw [← h3, List.count_flatMap]
      rfl
    rw [hsN fun d => [d.1, d.2.1].count 3] at hc3
    have cP : [(3 : ℕ), 3].count 3 = 2 := rfl
    have cΛ : [x₀, ℓ₁].count 3 = if ℓ₁ = 3 then 1 else 0 := by
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    rw [cP, cΛ] at hc3
    have key : ∀ l, l < 4 → (l = 3 → ℓ₁ = 3 → False) →
        (fruleCap (F.filterMap FFac.entData) false 2).getD l 0 ≤ 1 := by
      intro l hl h
      have h' : ¬ (l = 3 ∧ ℓ₁ = 3) := fun ⟨a, b⟩ => h a b
      rw [hcap2 l hl]
      simp only [show (3 : ℕ) ≠ 2 by omega, ↓reduceIte, zero_add]
      split_ifs <;> omega
    have hw := R3_ward_step F 2 t₂ h1 (fun d hd h2 => by
        by_cases hdP : d = (3, 3, [rR, 0], eP, dP)
        · subst hdP; rw [hP0] at h2; omega
        by_cases hdΛ : d = (x₀, ℓ₁, [0, rL], eL, dL)
        · subst hdΛ; rw [hΛ1] at h2; omega
        exact hfree d hd hdP hdΛ) hlab ht₂ (by rw [hEt₂, hr₂])
      (fun t ht hrt => by
        have hl := hlab _ (List.getElem_mem ht)
        have hne1 : (F.filterMap FFac.entData)[t] ≠ (3, 3, [rR, 0], eP, dP) := by
          intro h; rw [h, hP0] at hrt; omega
        have hne2 : (F.filterMap FFac.entData)[t] ≠ (x₀, ℓ₁, [0, rL], eL, dL) := by
          intro h; rw [h, hΛ1] at hrt; omega
        have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d => [d.1, d.2.1].count 3)
          (hmemR _ (List.getElem_mem ht) hne1 hne2))
        beta_reduce at hle
        have e1 : ℓ₁ = 3 → (F.filterMap FFac.entData)[t].1 ≠ 3 := by
          intro h h'
          have : 1 ≤ [(F.filterMap FFac.entData)[t].1, (F.filterMap FFac.entData)[t].2.1].count 3 :=
            List.count_pos_iff.2 (by simp [h'])
          have hif : (if ℓ₁ = 3 then (1 : ℕ) else 0) = 1 := by simp [h]
          omega
        have e2 : ℓ₁ = 3 → (F.filterMap FFac.entData)[t].2.1 ≠ 3 := by
          intro h h'
          have : 1 ≤ [(F.filterMap FFac.entData)[t].1, (F.filterMap FFac.entData)[t].2.1].count 3 :=
            List.count_pos_iff.2 (by simp [h'])
          have hif : (if ℓ₁ = 3 then (1 : ℕ) else 0) = 1 := by simp [h]
          omega
        exact ⟨key _ hl.1 fun a b => e1 b a, key _ hl.2 fun a b => e2 b a⟩) (by
          have h1' := (List.perm_cons_erase hd₂E).length_eq
          have : 2 ≤ ((F.filterMap FFac.entData).erase d₂).length := by
            have hne1 : (3, 3, [rR, 0], eP, dP) ≠ d₂ := by
              intro h; rw [← h, hP0] at hr₂; omega
            have hne2 : (x₀, ℓ₁, [0, rL], eL, dL) ≠ d₂ := by
              intro h; rw [← h, hΛ1] at hr₂; omega
            have m1 : (3, 3, [rR, 0], eP, dP) ∈ (F.filterMap FFac.entData).erase d₂ :=
              (List.mem_erase_of_ne hne1).2 hP
            have m2 := (List.mem_erase_of_ne hne2).2 hΛ
            have e := (List.perm_cons_erase m1).length_eq
            rw [List.length_cons] at e
            have m2' : (x₀, ℓ₁, [0, rL], eL, dL) ∈
                ((F.filterMap FFac.entData).erase d₂).erase (3, 3, [rR, 0], eP, dP) :=
              (List.mem_erase_of_ne (by intro h; rw [h, hP0] at hΛ1; omega)).2 m2
            have := List.length_pos_of_mem m2'
            omega
          rw [h1', List.length_cons]
          omega)
    simp only [↓reduceIte, show (3 : ℕ) ≠ 2 by omega] at hsum2
    omega
  · rw [hsZ R3zz, List.sum_eq_zero]
    · unfold R3zz; simp [hrR0, hrL0]
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      unfold R3zz
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      have := (hrest d hd).2; omega
  · rw [hsZ R3nl, List.sum_eq_zero]
    · unfold R3nl; simp
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      unfold R3nl; rw [(hrest d hd).1]; norm_num

/-- Case (9): the half `(x₀, 3)` with `Λ̃₁` and no resolvent, `x₀` outer, and the entry `(ℓ, y)`
with `Λ̃₂`, parts `[r_W, 0]`, `ℓ` inner and `y` outer. -/
private theorem R3_case_9 (F : List FFac) (x₀ ℓ y rW : ℕ) (eP eW : FMono) (dP dW : Bool)
    (hP : (x₀, 3, [0, 0], eP, dP) ∈ F.filterMap FFac.entData)
    (hW : (ℓ, y, [rW, 0], eW, dW) ∈ F.filterMap FFac.entData)
    (hx₀ : x₀ < 2) (hℓ : 2 ≤ ℓ ∧ ℓ < 4) (hy : y < 2) (hrW : 1 ≤ rW)
    (hfree : ∀ d ∈ F.filterMap FFac.entData, d ≠ (x₀, 3, [0, 0], eP, dP) →
      d ≠ (ℓ, y, [rW, 0], eW, dW) → d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum)
    (hnl : ((F.filterMap FFac.entData).map R3nl).sum ≤ 2)
    (hext : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i) :
    (∀ c ∈ fchosen F (frule F), ∀ o, c.2 = some o → ∀ q ∈ o.val, R3PP c.1 o q) ∧
      4 ≤ ((List.range 4).map fun l => (fuses F (frule F) l : ℤ)).sum ∧
      ((F.filterMap FFac.entData).map R3zz).sum = 1 ∧
      ((F.filterMap FFac.entData).map R3nl).sum = 2 := by
  have hrW0 : rW ≠ 0 := by omega
  have hP0 : FEnt.role (x₀, 3, [0, 0], eP, dP) = 0 := by simp [FEnt.role, fInnerL]
  have hW1 : FEnt.role (ℓ, y, [rW, 0], eW, dW) = 1 := by
    simp [FEnt.role, fInnerL, hrW0]; omega
  obtain ⟨hrest, hsZ, hsN, h0, h1, -⟩ := R3_two _ _ _ hP hW hP0 hW1 rfl rfl hfree hnl
  have hP_fit : ∀ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 0)
      (x₀, 3, [0, 0], eP, dP) false = some (kd, o) →
      (∀ q ∈ o.val, R3PP (x₀, 3, [0, 0], eP, dP) o q) ∧
      ∀ l, fuseOne ((x₀, 3, [0, 0], eP, dP), some o) l =
        (if x₀ = l then 1 else 0) + (if 3 = l then 1 else 0) := fun kd o hfit =>
    R3_fit_hs x₀ 3 0 0 eP dP (by omega) (hext _ hP) _ (by rw [R3_cap0]; omega)
      (by rw [R3_cap0]; omega) kd o hfit
  obtain ⟨tP, htP, hEtP, hord0, kdP, oP, hfitP, hchP⟩ := R3_first F _ hP hP0 h0
  have hcap1 : ∀ l, l < 4 → (fruleCap (F.filterMap FFac.entData) false 1).getD l 0 =
      (if x₀ = l then 1 else 0) + (if 3 = l then 1 else 0) := by
    intro l hl
    rw [R3_cap_succ F 0 tP l hl _ oP hord0 hchP, R3_cap0, (hP_fit kdP oP hfitP).2 l]
    omega
  have hW_fit : ∀ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 1)
      (ℓ, y, [rW, 0], eW, dW) false = some (kd, o) →
      (∀ q ∈ o.val, R3PP (ℓ, y, [rW, 0], eW, dW) o q) ∧
      ∀ l, fuseOne ((ℓ, y, [rW, 0], eW, dW), some o) l =
        (if ℓ = l then 1 else 0) + (if y = l then 1 else 0) := fun kd o hfit =>
    R3_fit_hs ℓ y rW 0 eW dW (by omega) (hext _ hW) _
      (by rw [hcap1 _ (by omega)]; split_ifs <;> omega)
      (by rw [hcap1 _ (by omega)]; split_ifs <;> omega) kd o hfit
  obtain ⟨tW, htW, hEtW, hord1, kdW, oW, hfitW, hchW⟩ := R3_second F _ hW hW1 h0 h1
  have hcap2 : ∀ l, l < 4 → (fruleCap (F.filterMap FFac.entData) false 2).getD l 0 =
      (if x₀ = l then 1 else 0) + (if 3 = l then 1 else 0) +
        ((if ℓ = l then 1 else 0) + (if y = l then 1 else 0)) := by
    intro l hl
    rw [R3_cap_succ F 1 tW l hl _ oW hord1 hchW, hcap1 l hl, (hW_fit kdW oW hfitW).2 l]
  have hlen2 : 2 ≤ (F.filterMap FFac.entData).length := by
    have := (List.getElem?_eq_some_iff.1 hord1).1
    rw [(frule_run_order _).1.length_eq, List.length_range] at this
    omega
  have hU2 := R3_Uge F 2 hlen2
  refine ⟨R3_PP_of F fun t ht k kd o hk hfit hkd hko q hq => ?_, ?_, ?_, ?_⟩
  · by_cases hdP : (F.filterMap FFac.entData)[t] = (x₀, 3, [0, 0], eP, dP)
    · have : k < 1 := R3_pos _ 0 1 k t h0 hk (by rw [List.getD_eq_getElem _ _ ht, hdP, hP0])
      have hk0 : k = 0 := by omega
      subst hk0
      rw [hdP] at hfit ⊢
      exact (hP_fit kd o hfit).1 q hq
    by_cases hdW : (F.filterMap FFac.entData)[t] = (ℓ, y, [rW, 0], eW, dW)
    · have a1 : k < 2 := R3_pos _ 1 2 k t h1 hk
        (by rw [List.getD_eq_getElem _ _ ht, hdW, hW1])
      have a2 : 1 ≤ k := R3_pos' _ 0 1 k t h0 hk
        (by rw [List.getD_eq_getElem _ _ ht, hdW, hW1]; omega)
      have hk1 : k = 1 := by omega
      subst hk1
      rw [hdW] at hfit ⊢
      exact (hW_fit kd o hfit).1 q hq
    obtain ⟨a, b⟩ := hfree _ (List.getElem_mem ht) hdP hdW
    exact R3PP_free' _ a b (hext _ (List.getElem_mem ht)) kd hkd o hko q hq
  · have hsum2 : ((List.range 4).map fun l =>
        ((fruleCap (F.filterMap FFac.entData) false 2).getD l 0 : ℤ)).sum = 4 := by
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.cons_append]
      rw [hcap2 0 (by norm_num), hcap2 1 (by norm_num), hcap2 2 (by norm_num),
        hcap2 3 (by norm_num)]
      rcases (show x₀ = 0 ∨ x₀ = 1 by omega) with rfl | rfl <;>
      rcases (show ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl <;>
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide
    omega
  · rw [hsZ R3zz, List.sum_eq_zero]
    · unfold R3zz; simp [hrW0]
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      unfold R3zz
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      have := (hrest d hd).2; omega
  · rw [hsZ R3nl, List.sum_eq_zero]
    · unfold R3nl; simp
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      unfold R3nl; rw [(hrest d hd).1]; norm_num

/-! ### The package entries with `Λ̃` -/

open private FW_pents FW_pw FW_pw_segs FW_pw_free FW_mem_pents FW_seg_cyc FW_wf_count
  FW_lamSide_mem FW_run FW_run_go FW_go_lam FW_go FW_findIdx_mem FW_wside
  from RBMTransitionEdge.Localized.Expansion.FEntWords
open private PB_segs_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private isEntP from RBMTransitionEdge.Localized.Expansion.PkgWords
open private RH_sides RH_fpkg RH_seek RH_lam RH_uniq RH_ent_loop
  from RBMTransitionEdge.Localized.Expansion.RemHalves
open private RC_E RC_E_mem RC_rent_some RC_parts_len RC_seg_cnt RC_isLam_cnt
  from RBMTransitionEdge.Localized.Expansion.RemCounts

/-- In a well-formed expression, the letter `Λ̃_o` lies in at most one package entry, counted
with multiplicity. -/
private theorem R3_pents_cnt (X : PkgExpr) (hX : X.wf = true) (o : Fin 2) :
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

/-- In a well-formed expression, two package entries holding `Λ̃_o` are equal. -/
private theorem R3_uniq (X : PkgExpr) (hX : X.wf = true) (o : Fin 2)
    (e e' : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (he' : e' ∈ X.pents)
    (ho : PkgLetter.lw (.lamt o) ∈ e.2.2) (ho' : PkgLetter.lw (.lamt o) ∈ e'.2.2) : e = e' := by
  by_contra hne
  rw [← List.count_pos_iff] at ho ho'
  have h1 := R3_sum_erase_nat _ _ he fun e => e.2.2.count (.lw (.lamt o))
  have h2 := List.le_sum_of_mem (List.mem_map_of_mem
    (f := fun e : ℕ × ℕ × List PkgLetter => e.2.2.count (.lw (.lamt o)))
    ((List.mem_erase_of_ne (Ne.symm hne)).2 he'))
  have := R3_pents_cnt X hX o
  omega

/-- A list with two letters `Λ̃_0, Λ̃_1`, each once, and no `Λ̃` before `Λ̃_0`. -/
private theorem R3_split (σ : List PkgLetter) (h0 : PkgLetter.lw (.lamt 0) ∈ σ)
    (h1 : PkgLetter.lw (.lamt 1) ∈ σ) (c0 : σ.count (.lw (.lamt 0)) ≤ 1)
    (c1 : σ.count (.lw (.lamt 1)) ≤ 1)
    (hT : ∀ z ∈ σ.takeWhile (fun x => x != PkgLetter.lw (.lamt 0)), z.isLam = false) :
    ∃ T M U, σ = T ++ .lw (.lamt 0) :: (M ++ .lw (.lamt 1) :: U) ∧
      (∀ z ∈ T, z.isLam = false) ∧ (∀ z ∈ M, z.isLam = false) := by
  obtain ⟨T, ρ, rfl⟩ := List.append_of_mem h0
  simp only [List.count_append, List.count_cons_self] at c0
  have hT0 : PkgLetter.lw (.lamt 0) ∉ T := List.count_eq_zero.1 (by omega)
  have hρ0 : PkgLetter.lw (.lamt 0) ∉ ρ := List.count_eq_zero.1 (by omega)
  have htw : (T ++ PkgLetter.lw (.lamt 0) :: ρ).takeWhile
      (fun x => x != PkgLetter.lw (.lamt 0)) = T := by
    rw [List.takeWhile_append_of_pos (fun a ha => by
      simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hT0 ha)]
    simp
  rw [htw] at hT
  have h1ρ : PkgLetter.lw (.lamt 1) ∈ ρ := by
    rcases List.mem_append.1 h1 with h | h
    · exact absurd (hT _ h) (by simp [PkgLetter.isLam])
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h (by decide)
      · exact h
  obtain ⟨M, U, rfl⟩ := List.append_of_mem h1ρ
  simp only [List.count_append, List.count_cons_self, List.count_cons] at c1
  have hM1 : PkgLetter.lw (.lamt 1) ∉ M := List.count_eq_zero.1 (by omega)
  refine ⟨T, M, U, rfl, hT, fun z hz => ?_⟩
  by_contra hl
  rcases RH_lam z (by simpa using hl) 0 with rfl | h
  · exact hρ0 (List.mem_append_left _ hz)
  · subst h
    exact hM1 hz

/-- The middle side of `Λ̃₁ ⋯ Λ̃₂` in one package entry, read from both letters. -/
private theorem R3_mid (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (T M U : List PkgLetter)
    (hσ : e.2.2 = T ++ .lw (.lamt 0) :: (M ++ .lw (.lamt 1) :: U))
    (hM : ∀ z ∈ M, z.isLam = false) :
    X.lamSide 0 true = M.countP PkgLetter.isRes ∧ X.lamSide 1 false = M.countP PkgLetter.isRes := by
  obtain ⟨w, -, hwE, hσw⟩ := FW_mem_pents X e he
  obtain ⟨hnE, -⟩ := FW_seg_cyc w e.2.2 hwE hσw
  have hgo : ∀ z ∈ M, FW_go z = true := fun z hz => by
    have h1 := hnE z (by rw [hσ]; simp [hz])
    simp [FW_go, h1, hM z hz]
  refine ⟨?_, ?_⟩
  · rw [(RH_sides X hX e he 0 T _ hσ).1, FW_run_go M hgo, FW_go_lam _ rfl]
    simp
  · have hσ' : e.2.2 = (T ++ .lw (.lamt 0) :: M) ++ .lw (.lamt 1) :: U := by
      rw [hσ]; simp
    rw [(RH_sides X hX e he 1 _ U hσ').2]
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [FW_run_go M.reverse (fun z hz => hgo z (List.mem_reverse.1 hz)), FW_go_lam _ rfl,
      List.countP_reverse]
    simp

/-- The side chosen by the rules (i)–(iv) when the word of `Λ̃₂` has a `Δ`: the side `a₁` right
of `Λ̃₁` is chosen only when `Λ̃₂` has no resolvent on its right, the left of `Λ̃₂` only when also
`a₁ = 0`, and the left of `Λ̃₁` never. -/
private theorem R3_side (R : PkgExpr) (hR : R.wf = true)
    (hE : ∀ w ∈ R.loops, PkgLetter.lw (.lamt 1) ∈ w → w.any PkgLetter.isEnt = true)
    (o : Fin 2) (side : Bool) (h : R.ffocusSide = some (o, side)) :
    (o = 0 → side = true ∧ R.lamSide 1 true = 0) ∧
      (o = 1 → side = false → R.lamSide 1 true = 0 ∧ R.lamSide 0 true = 0) := by
  unfold PkgExpr.ffocusSide at h
  rcases h₂ : R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt 1))]? with _ | w₂ <;>
    rcases h₁ : R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt 0))]? with _ | w₁ <;>
    simp only [h₂, h₁, reduceCtorEq] at h
  have m₂ := FW_findIdx_mem R.loops 1 w₂ h₂
  have m₁ := FW_findIdx_mem R.loops 0 w₁ h₁
  have hw₂ : w₂ ∈ R.loops := List.mem_of_getElem? h₂
  have hw₁ : w₁ ∈ R.loops := List.mem_of_getElem? h₁
  split_ifs at h with hc
  swap
  · exact absurd (hE w₂ hw₂ m₂) hc
  have e1 : R.lamSide 1 true = FW_wside w₂ 1 true :=
    FW_lamSide_mem R 1 true (FW_wf_count R hR 1).le w₂ hw₂ m₂
  have e0 : R.lamSide 0 true = FW_wside w₁ 0 true :=
    FW_lamSide_mem R 0 true (FW_wf_count R hR 0).le w₁ hw₁ m₁
  cases hs1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) true <;>
    cases hs2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true <;>
    cases hs3 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false <;>
    simp only [hs1, hs2, hs3, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    have z1 := (RH_seek w₂ 1 true).2
    have z0 := (RH_seek w₁ 0 true).2
    simp only [hs1, hs2, forall_const] at z1 z0
    refine ⟨fun ho => ?_, fun _ hs => ?_⟩
  all_goals first
    | exact absurd ho (by decide)
    | exact absurd hs (by decide)
    | exact ⟨rfl, by rw [e1]; exact z1⟩
    | exact ⟨by rw [e1]; exact z1, by rw [e0]; exact z0⟩

/-- The entry of a package entry: its labels, and its parts against those of the segment. -/
private theorem R3_D (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) :
    ∃ d, (X.rent e).entData = some d ∧ d ∈ X.rfacs.filterMap FFac.entData ∧ d.1 = e.1 ∧
      d.2.1 = e.2.1 ∧ d.2.2.1.length = e.2.2.countP PkgLetter.isLam + 1 ∧
      ∀ t < (pkgParts e.2.2).length, (pkgParts e.2.2).getD t 0 ≤ d.2.2.1.getD t 0 ∧
        ((pkgParts e.2.2).getD t 0 = 0 → d.2.2.1.getD t 0 = 0) := by
  obtain ⟨d, hd, -, -⟩ := RC_rent_some X e
  obtain ⟨h1, h2, hl, hp⟩ := pkg_rent_parts X e he d hd
  refine ⟨d, hd, ?_, h1, h2, by rw [hl, RC_parts_len], fun t ht => ⟨(hp t ht).1, (hp t ht).2.2⟩⟩
  rw [RC_E]
  exact List.mem_filterMap.2 ⟨e, he, hd⟩

/-- No `Λ̃` before `Λ̃_o` when the other letter `Λ̃` is absent. -/
private theorem R3_k0 (o : Fin 2) (σ : List PkgLetter) (h : PkgLetter.lw (.lamt (1 - o)) ∉ σ) :
    (σ.takeWhile fun x => x != PkgLetter.lw (.lamt o)).countP PkgLetter.isLam = 0 := by
  rw [List.countP_eq_zero]
  intro z hz hl
  have hzσ := (List.takeWhile_sublist _).subset hz
  have hne := List.mem_takeWhile_imp hz
  rcases RH_lam z hl o with rfl | rfl
  · simp at hne
  · exact h hzσ

/-- A letter `Λ̃` before which a list has no letter `Λ̃`. -/
private theorem R3_k0' (o : Fin 2) (σ : List PkgLetter)
    (h : (σ.takeWhile fun x => x != PkgLetter.lw (.lamt o)).all
      (fun x => !x.isRes && !x.isLam) = true) :
    (σ.takeWhile fun x => x != PkgLetter.lw (.lamt o)).countP PkgLetter.isLam = 0 := by
  rw [List.countP_eq_zero]
  intro z hz hl
  have := List.all_eq_true.1 h z hz
  simp [hl] at this

/-- The number of `Λ̃` of a package entry from its letters. -/
private theorem R3_nlam (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) :
    e.2.2.countP PkgLetter.isLam = (if PkgLetter.lw (.lamt 0) ∈ e.2.2 then 1 else 0) +
      (if PkgLetter.lw (.lamt 1) ∈ e.2.2 then 1 else 0) := by
  rw [RC_isLam_cnt]
  have c0 := RC_seg_cnt X hX e he 0
  have c1 := RC_seg_cnt X hX e he 1
  by_cases h0 : PkgLetter.lw (.lamt 0) ∈ e.2.2 <;> by_cases h1 : PkgLetter.lw (.lamt 1) ∈ e.2.2
  · have := List.count_pos_iff.2 h0; have := List.count_pos_iff.2 h1
    simp only [h0, h1, ↓reduceIte]; omega
  · have := List.count_pos_iff.2 h0; have := List.count_eq_zero.2 h1
    simp only [h0, h1, ↓reduceIte]; omega
  · have := List.count_eq_zero.2 h0; have := List.count_pos_iff.2 h1
    simp only [h0, h1, ↓reduceIte]; omega
  · have := List.count_eq_zero.2 h0; have := List.count_eq_zero.2 h1
    simp only [h0, h1, ↓reduceIte]; omega

/-- The entries of a factor list have at least one part. -/
private theorem R3_pos_len (F : List FFac) :
    ∀ d ∈ F.filterMap FFac.entData, 1 ≤ d.2.2.1.length := by
  intro d hd
  obtain ⟨f, -, hf⟩ := List.mem_filterMap.1 hd
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp only [FFac.entData, Option.some.injEq,
    reduceCtorEq] at hf
  subst hf
  simp only [FLet.parts, List.length_map]
  exact List.length_pos_iff.2 (List.splitOnP_ne_nil _ _)

/-- Every entry outside one entry with both letters `Λ̃` has none, when the entries carry at most
two `Λ̃`. -/
private theorem R3_free1 (E : List FEnt) (hpos : ∀ d ∈ E, 1 ≤ d.2.2.1.length)
    (hsum : (E.map fun d => d.2.2.1.length - 1).sum ≤ 2)
    (hb : ∀ d ∈ E, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum) (P : FEnt) (hP : P ∈ E)
    (hPl : P.2.2.1.length = 3) :
    ∀ d ∈ E, d ≠ P → d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum := by
  intro d hd hne
  have h1 := R3_sum_erase_nat _ _ hP fun d => d.2.2.1.length - 1
  have h2 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d : FEnt => d.2.2.1.length - 1)
    ((List.mem_erase_of_ne hne).2 hd))
  have h3 := hpos d hd
  simp only [hPl] at h1
  have : d.2.2.1.length = 1 := by omega
  exact ⟨this, hb d hd this⟩

/-- Every entry outside two entries with one letter `Λ̃` each has none, when the entries carry at
most two `Λ̃`. -/
private theorem R3_free2 (E : List FEnt) (hpos : ∀ d ∈ E, 1 ≤ d.2.2.1.length)
    (hsum : (E.map fun d => d.2.2.1.length - 1).sum ≤ 2)
    (hb : ∀ d ∈ E, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum) (P Λ : FEnt) (hP : P ∈ E) (hΛ : Λ ∈ E)
    (hne : Λ ≠ P) (hPl : P.2.2.1.length = 2) (hΛl : Λ.2.2.1.length = 2) :
    ∀ d ∈ E, d ≠ P → d ≠ Λ → d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum := by
  intro d hd h1 h2
  have hΛ' : Λ ∈ E.erase P := (List.mem_erase_of_ne hne).2 hΛ
  have e1 := R3_sum_erase_nat _ _ hP fun d => d.2.2.1.length - 1
  have e2 := R3_sum_erase_nat _ _ hΛ' fun d => d.2.2.1.length - 1
  have e3 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d : FEnt => d.2.2.1.length - 1)
    ((List.mem_erase_of_ne h2).2 ((List.mem_erase_of_ne h1).2 hd)))
  have h3 := hpos d hd
  simp only [hPl, hΛl] at e1 e2
  have : d.2.2.1.length = 1 := by omega
  exact ⟨this, hb d hd this⟩

/-- The sum of `nl` over the entries, in the integers. -/
private theorem R3_nl_cast (E : List FEnt) (hpos : ∀ d ∈ E, 1 ≤ d.2.2.1.length) :
    (E.map R3nl).sum = (((E.map fun d => d.2.2.1.length - 1).sum : ℕ) : ℤ) := by
  induction E with
  | nil => simp
  | cons d E ih =>
    have h1 := hpos d List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, R3nl]
    push_cast
    rw [ih fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')]
    push_cast [Nat.cast_sub h1]
    ring

/-- A prefix without a letter of a list `L₁ y L₂` is a prefix of `L₁`. -/
private theorem R3_prefix {α : Type*} (l L₁ L₂ : List α) (y : α) (h : l <+: L₁ ++ y :: L₂)
    (hy : y ∉ l) : l <+: L₁ := by
  rcases Nat.lt_or_ge L₁.length l.length with hlt | hle
  · exfalso
    have h1 : L₁ ++ [y] <+: L₁ ++ y :: L₂ := by
      rw [show L₁ ++ y :: L₂ = (L₁ ++ [y]) ++ L₂ by simp]; exact List.prefix_append _ _
    have := List.prefix_of_prefix_length_le h1 h (by simp; omega)
    exact hy (this.subset (by simp))
  · exact List.prefix_of_prefix_length_le h (List.prefix_append _ _) hle

/-- A suffix without a letter of a list `L₁ y L₂` is a suffix of `L₂`. -/
private theorem R3_suffix {α : Type*} (l L₁ L₂ : List α) (y : α) (h : l <:+ L₁ ++ y :: L₂)
    (hy : y ∉ l) : l <:+ L₂ := by
  rcases Nat.lt_or_ge L₂.length l.length with hlt | hle
  · exfalso
    have h1 : y :: L₂ <:+ L₁ ++ y :: L₂ := List.suffix_append _ _
    have := List.suffix_of_suffix_length_le h1 h (by simp; omega)
    exact hy (this.subset (by simp))
  · exact List.suffix_of_suffix_length_le h
      ((List.suffix_cons y L₂).trans (List.suffix_append L₁ (y :: L₂))) hle

/-- The prefix before `Λ̃₀` with no letter `Λ̃`, read with `≠` or with `!=`. -/
private theorem R3_tw (σ : List PkgLetter) (y : PkgLetter) :
    σ.takeWhile (fun x => decide (x ≠ y)) = σ.takeWhile (fun x => x != y) := by
  congr 1

/-- In Type III, the package entry with `Λ̃₁` and `Λ̃₂`: `T Λ̃₁ M Λ̃₂ U` with no `Λ̃` and no
resolvent in `T`, no `Λ̃` in `M`; the middle side seen from both letters. -/
private theorem R3_Rlevel (ε : ℝ) (n : ℕ) (T₀ : LoopExpr) (hT : T₀ ∈ loopInner ε n [loopStart])
    (hR0 : T₀.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T₀.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 3) :
    ∃ eM ∈ R.pents, ∃ T M U, eM.2.2 = T ++ .lw (.lamt 0) :: (M ++ .lw (.lamt 1) :: U) ∧
      (∀ z ∈ T, z.isLam = false ∧ z.isRes = false) ∧ (∀ z ∈ M, z.isLam = false) ∧
      R.lamSide 0 true = R.lamSide 1 false := by
  have hRw := pkg_inv_wf ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  obtain ⟨eM, heM, h0, h1⟩ := pkg_ptype3_seg R hty
  obtain ⟨w, hw, hwE, σ, hσ, hσ0, hσT⟩ :=
    pkg_inv_lam1 ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  obtain ⟨e', he', he'σ⟩ := pkg_pents_segs R w hw hwE σ hσ
  have hee : e' = eM := R3_uniq R hRw 0 e' eM he' heM (by rw [he'σ]; exact hσ0) h0
  subst hee
  rw [R3_tw] at hσT
  rw [← he'σ] at hσT
  obtain ⟨T, M, U, hTMU, hT', hM⟩ := R3_split e'.2.2 h0 h1 (RC_seg_cnt R hRw e' heM 0)
    (RC_seg_cnt R hRw e' heM 1) fun z hz => by
      have := List.all_eq_true.1 hσT z hz
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact this.2
  have hTtw : e'.2.2.takeWhile (fun x => x != PkgLetter.lw (.lamt 0)) = T := by
    have hT0 : PkgLetter.lw (.lamt 0) ∉ T := fun h => by simpa [PkgLetter.isLam] using hT' _ h
    rw [hTMU, List.takeWhile_append_of_pos (fun a ha => by
      simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hT0 ha)]
    simp
  rw [hTtw] at hσT
  obtain ⟨m0, m1⟩ := R3_mid R hRw e' heM T M U hTMU hM
  refine ⟨e', heM, T, M, U, hTMU, fun z hz => ?_, hM, by rw [m0, m1]⟩
  have := List.all_eq_true.1 hσT z hz
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact ⟨this.2, this.1⟩

/-- A letter that occurs once splits a list in one way. -/
private theorem R3_split_eq {α : Type*} (A B A' B' : List α) (y : α)
    (h : A ++ y :: B = A' ++ y :: B') (hA : y ∉ A) (hA' : y ∉ A') : A = A' ∧ B = B' := by
  have h1 : A <+: A' := R3_prefix A A' B' y (h ▸ List.prefix_append _ _) hA
  have h2 : A' <+: A := R3_prefix A' A B y (h.symm ▸ List.prefix_append _ _) hA'
  have hl : A.length = A'.length := le_antisymm h1.length_le h2.length_le
  have hAA : A = A' := h1.eq_of_length hl
  subst hAA
  simpa using h

/-- Case (8) on the expanded word: one package entry holds both letters `Λ̃`. -/
private theorem R3_fpkg8 (R : PkgExpr) (hR : R.wf = true) (hfoc : R.ffocus.isSome = true)
    (hs : R.ffocusSide = some (1, true)) (eM : ℕ × ℕ × List PkgLetter) (heM : eM ∈ R.pents)
    (T M U : List PkgLetter) (hTMU : eM.2.2 = T ++ .lw (.lamt 0) :: (M ++ .lw (.lamt 1) :: U))
    (hT : ∀ z ∈ T, z.isLam = false ∧ z.isRes = false) :
    ∃ eΛ ∈ R.fpkg.pents, PkgLetter.lw (.lamt 0) ∈ eΛ.2.2 ∧ PkgLetter.lw (.lamt 1) ∈ eΛ.2.2 := by
  have hFw := pkg_fpkg_wf R hR hfoc
  have h1M : PkgLetter.lw (.lamt 1) ∈ eM.2.2 := by rw [hTMU]; simp
  rcases (RH_fpkg R 1 true hs).1 rfl with ⟨e, he, A, X, B, a, -, hσ, hp⟩ | ⟨Y, X, a, -, hp⟩
  · have h1e : PkgLetter.lw (.lamt 1) ∈ e.2.2 := by rw [hσ]; simp
    have hee : e = eM := R3_uniq R hR 1 e eM he heM h1e h1M
    subst hee
    have c1 := RC_seg_cnt R hR e he 1
    have hA1 : PkgLetter.lw (.lamt 1) ∉ A := fun h => by
      rw [hσ] at c1; simp only [List.count_append, List.count_cons_self] at c1
      have := List.count_pos_iff.2 h; omega
    have hA0 : PkgLetter.lw (.lamt 0) ∈ A := by
      rcases Nat.lt_or_ge T.length A.length with hlt | hle
      · have p1 : T ++ [PkgLetter.lw (.lamt 0)] <+: e.2.2 := by
          rw [hTMU]; exact ⟨M ++ .lw (.lamt 1) :: U, by simp⟩
        have p2 : A <+: e.2.2 := by rw [hσ]; exact List.prefix_append _ _
        have := List.prefix_of_prefix_length_le p1 p2 (by simp; omega)
        exact this.subset (by simp)
      · exfalso
        have p1 : A ++ [PkgLetter.lw (.lamt 1)] <+: e.2.2 := by
          rw [hσ]; exact ⟨X ++ .lw (.res a) :: B, by simp⟩
        have p2 : T ++ [PkgLetter.lw (.lamt 0)] <+: e.2.2 := by
          rw [hTMU]; exact ⟨M ++ .lw (.lamt 1) :: U, by simp⟩
        have := List.prefix_of_prefix_length_le p1 p2 (by simp; omega)
        have hm := this.subset (show PkgLetter.lw (.lamt 1) ∈ A ++ [PkgLetter.lw (.lamt 1)] by simp)
        simp only [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact absurd (hT _ hm).1 (by simp [PkgLetter.isLam])
        · exact absurd hm (by decide)
    refine ⟨(e.1, 3, A ++ .lw (.lamt 1) :: (X ++ [.lw (.det a)])), hp.symm.subset (by simp),
      by simp [hA0], by simp⟩
  · exfalso
    have hc := R3_pents_cnt R.fpkg hFw 1
    rw [(hp.map fun e => e.2.2.count (PkgLetter.lw (.lamt 1))).sum_eq] at hc
    simp only [List.map_cons, List.sum_cons] at hc
    have h1 : 1 ≤ ((PkgLetter.lw (.res a) :: Y) ++ PkgLetter.lw (.lamt 1) ::
        (X ++ [PkgLetter.lw (.det a)])).count (PkgLetter.lw (.lamt 1)) :=
      List.count_pos_iff.2 (by simp)
    have h2 := List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun e : ℕ × ℕ × List PkgLetter => e.2.2.count (PkgLetter.lw (.lamt 1))) heM)
    have h3 := List.count_pos_iff.2 h1M
    omega

/-- Case (9) on the expanded word: the half `𝒢_a ⋯` of the cut package entry holds `Λ̃₂`, with
no resolvent after it. -/
private theorem R3_fpkg9 (R : PkgExpr) (hR : R.wf = true) (hfoc : R.ffocus.isSome = true)
    (hs : R.ffocusSide = some (0, true)) (eM : ℕ × ℕ × List PkgLetter) (heM : eM ∈ R.pents)
    (T M U : List PkgLetter) (hTMU : eM.2.2 = T ++ .lw (.lamt 0) :: (M ++ .lw (.lamt 1) :: U))
    (hT : ∀ z ∈ T, z.isLam = false ∧ z.isRes = false) (hM : ∀ z ∈ M, z.isLam = false)
    (ha₁ : 1 ≤ R.lamSide 0 true) (ha₂ : R.lamSide 1 true = 0) :
    ∃ eG ∈ R.fpkg.pents, eG.1 = 2 ∧ ∃ B₁ B₂ : List PkgLetter, ∃ a : Fin 2,
      eG.2.2 = (.lw (.res a) :: B₁) ++ .lw (.lamt 1) :: B₂ ∧ ∀ z ∈ B₂, z.isRes = false := by
  have hFw := pkg_fpkg_wf R hR hfoc
  have h0M : PkgLetter.lw (.lamt 0) ∈ eM.2.2 := by rw [hTMU]; simp
  have c0 := RC_seg_cnt R hR eM heM 0
  have c1 := RC_seg_cnt R hR eM heM 1
  rcases (RH_fpkg R 0 true hs).1 rfl with ⟨e, he, A, X, B, a, hX, hσ, hp⟩ | ⟨Y, X, a, -, hp⟩
  · have h0e : PkgLetter.lw (.lamt 0) ∈ e.2.2 := by rw [hσ]; simp
    have hee : e = eM := R3_uniq R hR 0 e eM he heM h0e h0M
    subst hee
    have hT0 : PkgLetter.lw (.lamt 0) ∉ T := fun h => by simpa [PkgLetter.isLam] using (hT _ h).1
    have hA0 : PkgLetter.lw (.lamt 0) ∉ A := fun h => by
      rw [hσ] at c0; simp only [List.count_append, List.count_cons_self] at c0
      have := List.count_pos_iff.2 h; omega
    obtain ⟨-, hrest⟩ := R3_split_eq A (X ++ .lw (.res a) :: B) T (M ++ .lw (.lamt 1) :: U) _
      (hσ.symm.trans hTMU) hA0 hT0
    -- `Λ̃₂` lies after the cut resolvent
    have hM1 : PkgLetter.lw (.lamt 1) ∉ M := fun h => by
      rw [hTMU] at c1; simp only [List.count_append, List.count_cons_self, List.count_cons] at c1
      have := List.count_pos_iff.2 h; omega
    have hX1 : PkgLetter.lw (.lamt 1) ∉ X := by
      intro h1
      obtain ⟨X₁, X₂, rfl⟩ := List.append_of_mem h1
      have hX₁ : PkgLetter.lw (.lamt 1) ∉ X₁ := by
        intro h
        have hsp : e.2.2 = (A ++ PkgLetter.lw (.lamt 0) :: X₁) ++ PkgLetter.lw (.lamt 1) ::
            (X₂ ++ PkgLetter.lw (.res a) :: B) := by rw [hσ]; simp
        rw [hsp, List.count_append, List.count_cons_self] at c1
        have := List.count_pos_iff.2 (show PkgLetter.lw (.lamt 1) ∈
          A ++ PkgLetter.lw (.lamt 0) :: X₁ by simp [h])
        omega
      obtain ⟨hMX, -⟩ := R3_split_eq M U X₁ (X₂ ++ PkgLetter.lw (.res a) :: B) _
        (hrest.symm.trans (by simp)) hM1 hX₁
      have hm := (R3_mid R hR e he T M U hTMU hM).1
      rw [hMX, List.countP_eq_zero.2 fun z hz => by
        simpa using hX z (List.mem_append_left _ hz)] at hm
      omega
    have hB1 : PkgLetter.lw (.lamt 1) ∈ B := by
      have : PkgLetter.lw (.lamt 1) ∈ X ++ PkgLetter.lw (.res a) :: B := by rw [hrest]; simp
      simp only [List.mem_append, List.mem_cons] at this
      rcases this with h | h | h
      · exact absurd h hX1
      · cases h
      · exact h
    obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hB1
    have hB₁ : PkgLetter.lw (.lamt 1) ∉ X ++ PkgLetter.lw (.res a) :: B₁ := by
      intro h
      have hsp : e.2.2 = (A ++ PkgLetter.lw (.lamt 0) :: (X ++ PkgLetter.lw (.res a) :: B₁)) ++
          PkgLetter.lw (.lamt 1) :: B₂ := by rw [hσ]; simp
      rw [hsp, List.count_append, List.count_cons_self] at c1
      have := List.count_pos_iff.2 (show PkgLetter.lw (.lamt 1) ∈
        A ++ PkgLetter.lw (.lamt 0) :: (X ++ PkgLetter.lw (.res a) :: B₁) by simp [h])
      omega
    obtain ⟨-, hUeq⟩ := R3_split_eq M U (X ++ PkgLetter.lw (.res a) :: B₁) B₂ _
      (hrest.symm.trans (by simp)) hM1 hB₁
    refine ⟨(2, e.2.1, PkgLetter.lw (.res a) :: (B₁ ++ PkgLetter.lw (.lamt 1) :: B₂)),
      hp.symm.subset (by simp), rfl, B₁, B₂, a, by simp, ?_⟩
    -- no resolvent right of `Λ̃₂`: the side `a₂` is empty
    rw [← hUeq]
    have hσ' : e.2.2 = (T ++ PkgLetter.lw (.lamt 0) :: M) ++ PkgLetter.lw (.lamt 1) :: U := by
      rw [hTMU]; simp
    have hs1 := (RH_sides R hR e he 1 _ U hσ').1
    obtain ⟨w, -, hwE, hσw⟩ := FW_mem_pents R e he
    obtain ⟨hnE, -⟩ := FW_seg_cyc w e.2.2 hwE hσw
    have hU0 : PkgLetter.lw (.lamt 0) ∉ U := fun h => by
      rw [hTMU, List.count_append, List.count_cons_self] at c0
      have := List.count_pos_iff.2 (show PkgLetter.lw (.lamt 0) ∈ M ++ PkgLetter.lw (.lamt 1) :: U
        by simp [h])
      omega
    have hU1 : PkgLetter.lw (.lamt 1) ∉ U := fun h => by
      rw [hσ', List.count_append, List.count_cons_self] at c1
      have := List.count_pos_iff.2 h
      omega
    have hgo : ∀ z ∈ U, FW_go z = true := fun z hz => by
      have h1 := hnE z (by rw [hσ']; simp [hz])
      have h2 : z.isLam = false := by
        by_contra hl
        rcases RH_lam z (by simpa using hl) 0 with rfl | rfl
        · exact hU0 hz
        · exact hU1 hz
      simp [FW_go, h1, h2]
    have hrun := FW_run_go U hgo []
    rw [List.append_nil] at hrun
    have hz : U.countP PkgLetter.isRes = 0 := by
      have : FW_run ([] : List PkgLetter) = 0 := rfl
      omega
    intro z hz'
    by_contra hr
    have := List.countP_pos_iff.2 ⟨z, hz', by simpa using hr⟩
    omega
  · exfalso
    have hc := R3_pents_cnt R.fpkg hFw 0
    rw [(hp.map fun e => e.2.2.count (PkgLetter.lw (.lamt 0))).sum_eq] at hc
    simp only [List.map_cons, List.sum_cons] at hc
    have h1 : 1 ≤ ((PkgLetter.lw (.res a) :: Y) ++ PkgLetter.lw (.lamt 0) ::
        (X ++ [PkgLetter.lw (.det a)])).count (PkgLetter.lw (.lamt 0)) :=
      List.count_pos_iff.2 (by simp)
    have h2 := List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun e : ℕ × ℕ × List PkgLetter => e.2.2.count (PkgLetter.lw (.lamt 0))) heM)
    have h3 := List.count_pos_iff.2 h0M
    omega

/-- The common facts of a derivative structure of Type III: the well-formedness of `R`, of its
expanded word and of `R'`, the side of the focus, the entry `T Λ̃₁ M Λ̃₂ U` of `R`, and `a₁`. -/
private theorem R3_common (ε : ℝ) (n : ℕ) (T₀ : LoopExpr) (hT : T₀ ∈ loopInner ε n [loopStart])
    (hR0 : T₀.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T₀.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    R.wf = true ∧ R.ffocus.isSome = true ∧ R.fpkg.wf = true ∧ R'.wf = true ∧
      R.fpkg ∈ R.fpkg.dwirt 2 3 0 0 := by
  have hRw := pkg_inv_wf ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  have hFw := pkg_fpkg_wf R hRw hfoc
  refine ⟨hRw, hfoc, hFw, pkg_dwirt_iter (fun _ X => X.wf = true) 2 3
    (fun _ X hX X' h => (pkg_dent_wf X X' 2 3 hX h).1)
    (fun _ X hX X' h => (pkg_dent_wf X X' 3 2 hX h).1) _ hFw p q R' hR', by
      simp [PkgExpr.dwirt]⟩

/-- A list of length `3` from its entries. -/
private theorem R3_l3 (l : List ℕ) (h : l.length = 3) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0] := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 h
  rfl

/-- A list of length `2` from its entries. -/
private theorem R3_l2 (l : List ℕ) (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h
  rfl

/-- Case (8): the entries with `Λ̃` of a derivative structure, `(x₀, 3)` with both letters and
parts `[0, r, 0]`, or `(ℓ₂, 3)` with `Λ̃₂` and parts `[r_R, 0]` and `(x₀, ℓ₁)` with `Λ̃₁` and parts
`[0, r_L]`. -/
private theorem R3_shape8 (ε : ℝ) (n : ℕ) (T₀ : LoopExpr) (hT : T₀ ∈ loopInner ε n [loopStart])
    (hR0 : T₀.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T₀.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 3) (p q : ℕ) (R' : PkgExpr)
    (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) (hs : R.ffocusSide = some (1, true)) :
    (∃ x₀ r eP dP, ((x₀, 3, [0, r, 0], eP, dP) : FEnt) ∈ R'.rfacs.filterMap FFac.entData ∧
      x₀ < 2 ∧ 1 ≤ r) ∨
    (∃ ℓ₂ rR x₀ ℓ₁ rL eP eL dP dL,
      ((ℓ₂, 3, [rR, 0], eP, dP) : FEnt) ∈ R'.rfacs.filterMap FFac.entData ∧
      ((x₀, ℓ₁, [0, rL], eL, dL) : FEnt) ∈ R'.rfacs.filterMap FFac.entData ∧
      2 ≤ ℓ₂ ∧ ℓ₂ < 4 ∧ 1 ≤ rR ∧ x₀ < 2 ∧ 2 ≤ ℓ₁ ∧ ℓ₁ < 4 ∧ 1 ≤ rL) := by
  obtain ⟨hRw, hfoc, hFw, hR'w, hF0⟩ := R3_common ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨eM, heM, T, M, U, hTMU, hT', -, hmid⟩ :=
    R3_Rlevel ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty
  have ha₂ : 1 ≤ R.lamSide 1 true := pkg_ffocusSide_pos R hRw 1 true hs
  have ha₁ : 1 ≤ R.lamSide 0 true :=
    (pkg_inv_order ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).2.2 hty ha₂
  have hfl := pkg_fpkg_lamSide R hRw hfoc
  have hsd := pkg_rem_sides ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have s1t : R'.lamSide 1 true = 0 := (hsd 1 true).1 (by rw [hfl]; simp [hs])
  have s0t : 1 ≤ R'.lamSide 0 true :=
    ((hsd 0 true).2 (by rw [hfl, hs, ite_eq_right (by decide)]; exact ha₁)).1
  have s1f : 1 ≤ R'.lamSide 1 false :=
    ((hsd 1 false).2 (by
      rw [hfl, hs, ite_eq_right (by decide), ← hmid]; exact ha₁)).1
  obtain ⟨s0f, e₁, he₁, h0e₁, he₁x, he₁T⟩ :=
    pkg_rem_lam1 ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨-, e, he, e₀, he₀, h1e, h1e₀, -, hright, -⟩ :=
    pkg_rem_role0 ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' 1 true hs
  obtain ⟨he3, -, -, hcut, hlast⟩ := hright rfl
  obtain ⟨d, hd, hdE, hd1, hd2, hdlen, hdparts⟩ := R3_D R' e he
  have hpl : ∀ e' : ℕ × ℕ × List PkgLetter, (pkgParts e'.2.2).length =
      e'.2.2.countP PkgLetter.isLam + 1 := fun e' => RC_parts_len _
  by_cases h0e : PkgLetter.lw (.lamt 0) ∈ e.2.2
  · left
    have hee : e₁ = e := R3_uniq R' hR'w 0 e₁ e he₁ he h0e₁ h0e
    subst hee
    have hn := R3_nlam R' hR'w e₁ he₁
    simp only [h0e, h1e, ↓reduceIte] at hn
    have hk0 := R3_k0' 0 e₁.2.2 he₁T
    obtain ⟨g0, g1⟩ := pkg_pents_sides R' hR'w e₁ he₁ 0 h0e
    rw [hk0, s0f] at g0
    rw [hk0, zero_add] at g1
    have hlen : d.2.2.1.length = 3 := by rw [hdlen, hn]
    have p0 := (hdparts 0 (by rw [hpl, hn]; omega)).2 g0
    have p1 := (hdparts 1 (by rw [hpl, hn]; omega)).1
    have hl : d.2.2.1.getLast? = some 0 := by simpa [hd] using hlast
    obtain ⟨x, y, parts, ext, det⟩ := d
    simp only at hd1 hd2 hlen p0 p1 hl hdE
    rw [R3_l3 parts hlen] at hl hdE
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
    rw [p0, hl, hd2, he3] at hdE
    exact ⟨x, parts.getD 1 0, ext, det, hdE, hd1 ▸ he₁x, by omega⟩
  · right
    obtain ⟨eΛ, heΛ, h0Λ, h1Λ⟩ := R3_fpkg8 R hRw hfoc hs eM heM T M U hTMU hT'
    have he₀Λ : e₀ = eΛ := R3_uniq R.fpkg hFw 1 e₀ eΛ he₀ heΛ h1e₀ h1Λ
    subst he₀Λ
    have hin : 2 ≤ e.1 ∧ e.1 < 4 := by
      rcases hcut with ⟨-, h⟩ | h
      · exact absurd (h ▸ h0Λ) h0e
      · exact h
    -- the entry `(ℓ₂, 3)` with `Λ̃₂`
    have hn := R3_nlam R' hR'w e he
    simp only [h0e, h1e, ↓reduceIte] at hn
    have hk1 := R3_k0 1 e.2.2 (by simpa using h0e)
    obtain ⟨g0, g1⟩ := pkg_pents_sides R' hR'w e he 1 h1e
    rw [hk1] at g0
    rw [hk1, zero_add, s1t] at g1
    have hlen : d.2.2.1.length = 2 := by rw [hdlen, hn]
    have p0 := (hdparts 0 (by rw [hpl, hn]; omega)).1
    have p1 := (hdparts 1 (by rw [hpl, hn]; omega)).2 g1
    -- the entry `(x₀, ℓ₁)` with `Λ̃₁`
    have h1e₁ : PkgLetter.lw (.lamt 1) ∉ e₁.2.2 := fun h => by
      have := R3_uniq R' hR'w 1 e₁ e he₁ he h h1e
      subst this; exact h0e h0e₁
    obtain ⟨d₁, hd₁, hd₁E, hd₁1, hd₁2, hd₁len, hd₁parts⟩ := R3_D R' e₁ he₁
    have hn₁ := R3_nlam R' hR'w e₁ he₁
    simp only [h0e₁, h1e₁, ↓reduceIte] at hn₁
    have hk0 := R3_k0' 0 e₁.2.2 he₁T
    obtain ⟨f0, f1⟩ := pkg_pents_sides R' hR'w e₁ he₁ 0 h0e₁
    rw [hk0, s0f] at f0
    rw [hk0, zero_add] at f1
    have hlen₁ : d₁.2.2.1.length = 2 := by rw [hd₁len, hn₁]
    have q0 := (hd₁parts 0 (by rw [hpl, hn₁]; omega)).2 f0
    have q1 := (hd₁parts 1 (by rw [hpl, hn₁]; omega)).1
    -- `ℓ₁` is inner: the piece of `Λ̃₁` is cut at a resolvent
    obtain ⟨-, e₁F, he₁F, h0e₁F, -, he₁FT⟩ :=
      pkg_rem_lam1 ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR 0 0 R.fpkg hF0
    have hFΛ : e₁F = e₀ := R3_uniq R.fpkg hFw 0 e₁F e₀ he₁F heΛ h0e₁F h0Λ
    subst hFΛ
    obtain ⟨⟨e'', he'', -, hpre, hcut'⟩, -⟩ :=
      pkg_rem_pieces ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' e₁F heΛ
    have hℓ₁ : 2 ≤ e₁.2.1 ∧ e₁.2.1 < 4 := by
      rcases hcut' with ⟨-, h⟩ | ⟨c1, c2, c3⟩
      · exfalso
        have := R3_uniq R' hR'w 1 e'' e he'' he (h ▸ h1Λ) h1e
        subst this
        exact h0e (h ▸ h0Λ)
      · have h0e'' : PkgLetter.lw (.lamt 0) ∈ e''.2.2 := by
          by_contra hn0
          obtain ⟨Tf, rest, hTf⟩ := List.append_of_mem h0Λ
          have c0 := RC_seg_cnt R.fpkg hFw e₁F heΛ 0
          rw [hTf, List.count_append, List.count_cons_self] at c0
          have hTf0 : PkgLetter.lw (.lamt 0) ∉ Tf := fun h => by
            have := List.count_pos_iff.2 h; omega
          have htw : e₁F.2.2.takeWhile (fun x => x != PkgLetter.lw (.lamt 0)) = Tf := by
            rw [hTf, List.takeWhile_append_of_pos (fun a ha => by
              simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hTf0 ha)]
            simp
          rw [hTf] at hpre
          have hp := R3_prefix _ _ _ _ hpre hn0
          obtain ⟨z, hz⟩ : ∃ z, e''.2.2.getLast? = some z := by
            cases h' : e''.2.2.getLast? with
            | none => rw [h'] at c3; simp at c3
            | some z => exact ⟨z, rfl⟩
          rw [hz] at c3
          simp only [Option.map_some, Option.some.injEq] at c3
          have hzT : z ∈ Tf := hp.subset (List.mem_of_getLast? hz)
          rw [htw] at he₁FT
          have := List.all_eq_true.1 he₁FT z hzT
          simp [c3] at this
        have := R3_uniq R' hR'w 0 e'' e₁ he'' he₁ h0e'' h0e₁
        subst this
        exact ⟨c1, c2⟩
    obtain ⟨x, y, parts, ext, det⟩ := d
    obtain ⟨x₁, y₁, parts₁, ext₁, det₁⟩ := d₁
    simp only at hd1 hd2 hlen p0 p1 hdE hd₁1 hd₁2 hlen₁ q0 q1 hd₁E
    rw [R3_l2 parts hlen, p1, hd2, he3] at hdE
    rw [R3_l2 parts₁ hlen₁, q0, hd₁1, hd₁2] at hd₁E
    rw [hd1] at hdE
    exact ⟨e.1, parts.getD 0 0, e₁.1, e₁.2.1, parts₁.getD 1 0, ext, ext₁, det, det₁, hdE, hd₁E,
      hin.1, hin.2, by omega, he₁x, hℓ₁.1, hℓ₁.2, by omega⟩

/-- Case (9): the entries with `Λ̃` of a derivative structure, `(x₀, 3)` with `Λ̃₁` and parts
`[0, 0]`, and `(ℓ, y)` with `Λ̃₂` and parts `[r_W, 0]`, `ℓ` inner; and `fR ≥ 1`. -/
private theorem R3_shape9 (ε : ℝ) (n : ℕ) (T₀ : LoopExpr) (hT : T₀ ∈ loopInner ε n [loopStart])
    (hR0 : T₀.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T₀.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 3) (p q : ℕ) (R' : PkgExpr)
    (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) (hs : R.ffocusSide = some (0, true)) :
    1 ≤ R.fR ∧ ∃ x₀ ℓ y rW eP eW dP dW,
      ((x₀, 3, [0, 0], eP, dP) : FEnt) ∈ R'.rfacs.filterMap FFac.entData ∧
      ((ℓ, y, [rW, 0], eW, dW) : FEnt) ∈ R'.rfacs.filterMap FFac.entData ∧
      x₀ < 2 ∧ 2 ≤ ℓ ∧ ℓ < 4 ∧ 1 ≤ rW := by
  obtain ⟨hRw, hfoc, hFw, hR'w, -⟩ := R3_common ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨eM, heM, T, M, U, hTMU, hT', hM, hmid⟩ :=
    R3_Rlevel ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty
  have h1M : PkgLetter.lw (.lamt 1) ∈ eM.2.2 := by rw [hTMU]; simp
  have hE : ∀ w ∈ R.loops, PkgLetter.lw (.lamt 1) ∈ w → w.any PkgLetter.isEnt = true := by
    intro w hw h1
    obtain ⟨w', hw', hw'E, h1'⟩ := RH_ent_loop R eM heM _ h1M
    rw [RH_uniq R hRw 1 w w' hw hw' h1 h1']
    exact hw'E
  have ha₂ : R.lamSide 1 true = 0 := ((R3_side R hRw hE 0 true hs).1 rfl).2
  have ha₁ : 1 ≤ R.lamSide 0 true := pkg_ffocusSide_pos R hRw 0 true hs
  have hfR : 1 ≤ R.fR := by
    have h := pkg_inv_empty ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
    unfold PkgExpr.emptySides at h
    rw [hty, ha₂] at h
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at h
    split_ifs at h <;> push_cast at h <;> omega
  have hfl := pkg_fpkg_lamSide R hRw hfoc
  have hsd := pkg_rem_sides ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have s0t : R'.lamSide 0 true = 0 := (hsd 0 true).1 (by rw [hfl]; simp [hs])
  have s1t : R'.lamSide 1 true = 0 := (hsd 1 true).1 (by rw [hfl]; simp [hs, ha₂])
  have s1f : 1 ≤ R'.lamSide 1 false :=
    ((hsd 1 false).2 (by
      rw [hfl, hs, ite_eq_right (by decide), ← hmid]; exact ha₁)).1
  obtain ⟨s0f, e₁, he₁, h0e₁, he₁x, he₁T⟩ :=
    pkg_rem_lam1 ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨-, e, he, e₀, he₀, h0e, -, -, hright, -⟩ :=
    pkg_rem_role0 ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' 0 true hs
  obtain ⟨he3, -, -, -, -⟩ := hright rfl
  have hee : e₁ = e := R3_uniq R' hR'w 0 e₁ e he₁ he h0e₁ h0e
  subst hee
  have h1e : PkgLetter.lw (.lamt 1) ∉ e₁.2.2 := by
    intro h1
    obtain ⟨T', M', U', hσ, -, hM'⟩ := R3_split e₁.2.2 h0e₁ h1 (RC_seg_cnt R' hR'w e₁ he₁ 0)
      (RC_seg_cnt R' hR'w e₁ he₁ 1) fun z hz => by
        have := List.all_eq_true.1 he₁T z hz
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
        exact this.2
    obtain ⟨m0, m1⟩ := R3_mid R' hR'w e₁ he₁ T' M' U' hσ hM'
    omega
  have hpl : ∀ e' : ℕ × ℕ × List PkgLetter, (pkgParts e'.2.2).length =
      e'.2.2.countP PkgLetter.isLam + 1 := fun e' => RC_parts_len _
  -- the half `(x₀, 3)` with `Λ̃₁`
  obtain ⟨d, hd, hdE, hd1, hd2, hdlen, hdparts⟩ := R3_D R' e₁ he₁
  have hn := R3_nlam R' hR'w e₁ he₁
  simp only [h0e₁, h1e, ↓reduceIte] at hn
  have hk0 := R3_k0' 0 e₁.2.2 he₁T
  obtain ⟨g0, g1⟩ := pkg_pents_sides R' hR'w e₁ he₁ 0 h0e₁
  rw [hk0, s0f] at g0
  rw [hk0, zero_add, s0t] at g1
  have hlen : d.2.2.1.length = 2 := by rw [hdlen, hn]
  have p0 := (hdparts 0 (by rw [hpl, hn]; omega)).2 g0
  have p1 := (hdparts 1 (by rw [hpl, hn]; omega)).2 g1
  -- the piece of the half `𝒢_a ⋯` with `Λ̃₂`
  obtain ⟨eG, heG, heG1, B₁, B₂, a, hσG, hB₂⟩ :=
    R3_fpkg9 R hRw hfoc hs eM heM T M U hTMU hT' hM ha₁ ha₂
  obtain ⟨-, ⟨e', he', -, hsuf, hcut⟩⟩ :=
    pkg_rem_pieces ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' eG heG
  have h1e' : PkgLetter.lw (.lamt 1) ∈ e'.2.2 := by
    rcases hcut with ⟨-, h⟩ | ⟨-, -, c3⟩
    · rw [h, hσG]; simp
    · by_contra hn1
      rw [hσG] at hsuf
      have hs' := R3_suffix _ _ _ _ hsuf hn1
      obtain ⟨z, hz⟩ : ∃ z, e'.2.2.head? = some z := by
        cases h' : e'.2.2.head? with
        | none => rw [h'] at c3; simp at c3
        | some z => exact ⟨z, rfl⟩
      rw [hz] at c3
      simp only [Option.map_some, Option.some.injEq] at c3
      have hzB : z ∈ B₂ := hs'.subset (List.mem_of_head? hz)
      rw [hB₂ z hzB] at c3
      exact absurd c3 (by decide)
  have hℓ : 2 ≤ e'.1 ∧ e'.1 < 4 := by
    rcases hcut with ⟨h, -⟩ | ⟨c1, c2, -⟩
    · rw [h, heG1]; omega
    · exact ⟨c1, c2⟩
  have h0e' : PkgLetter.lw (.lamt 0) ∉ e'.2.2 := fun h => by
    have := R3_uniq R' hR'w 0 e' e₁ he' he₁ h h0e₁
    subst this; exact h1e h1e'
  obtain ⟨d', hd', hd'E, hd'1, hd'2, hd'len, hd'parts⟩ := R3_D R' e' he'
  have hn' := R3_nlam R' hR'w e' he'
  simp only [h0e', h1e', ↓reduceIte] at hn'
  have hk1 := R3_k0 1 e'.2.2 (by simpa using h0e')
  obtain ⟨f0, f1⟩ := pkg_pents_sides R' hR'w e' he' 1 h1e'
  rw [hk1] at f0
  rw [hk1, zero_add, s1t] at f1
  have hlen' : d'.2.2.1.length = 2 := by rw [hd'len, hn']
  have q0 := (hd'parts 0 (by rw [hpl, hn']; omega)).1
  have q1 := (hd'parts 1 (by rw [hpl, hn']; omega)).2 f1
  obtain ⟨x, y, parts, ext, det⟩ := d
  obtain ⟨x', y', parts', ext', det'⟩ := d'
  simp only at hd1 hd2 hlen p0 p1 hdE hd'1 hd'2 hlen' q0 q1 hd'E
  rw [R3_l2 parts hlen, p0, p1, hd1, hd2, he3] at hdE
  rw [R3_l2 parts' hlen', q1, hd'1] at hd'E
  exact ⟨hfR, e₁.1, e'.1, y', parts'.getD 0 0, ext, ext', det, det', hdE, hd'E, he₁x, hℓ.1, hℓ.2,
    by omega⟩

/-- The counts of a derivative structure: its `S` against the parts and the loops, the number of
resolvents and light weights (5.86) [character_relation_further_expansion], the labels below `4`,
and `fR, Σ ≥ 0`. -/
private theorem R3_counts (ε : ℝ) (n : ℕ) (T₀ : LoopExpr) (hT : T₀ ∈ loopInner ε n [loopStart])
    (hR0 : T₀.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T₀.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    R'.S = R.fR + ((R'.rfacs.filterMap FFac.entData).map R3rr).sum +
        ((fLoops R'.rfacs).map fun w => (fresN w : ℤ) - 1).sum - R'.fpi ∧
      ((R'.rfacs.filterMap FFac.entData).map R3rr).sum +
        ((fLoops R'.rfacs).map fun w => (fresN w : ℤ)).sum + R'.weights.length =
        R.fsig - R.fR + R'.fpi ∧
      (∀ d ∈ R'.rfacs.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4) ∧ 0 ≤ R.fR ∧ 0 ≤ R.fsig := by
  have hres := pkg_rfacs_res R'
  have hfR := pkg_rem_fR ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hmu := pkg_rem_mu ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hnent := pkg_rem_nent ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hn := R3_n R'
  obtain ⟨hf0, -, hs0, hsle, -⟩ := pkg_inv_counts ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hloc := pkg_rem_local ε n T₀ hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have e1 : ((R'.rfacs.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1) =
      (R'.rfacs.filterMap FFac.entData).map R3rr := rfl
  have hL : ((fLoops R'.rfacs).map fun w => (fresN w : ℤ)).sum =
      ((fLoops R'.rfacs).map fun w => (fresN w : ℤ) - 1).sum + (fLoops R'.rfacs).length := by
    have : ∀ L : List (List FLet), (L.map fun w => (fresN w : ℤ)).sum =
        (L.map fun w => (fresN w : ℤ) - 1).sum + L.length := by
      intro L
      induction L with
      | nil => simp
      | cons w L ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring
    exact this _
  rw [e1] at hres
  refine ⟨?_, ?_, ?_, hf0, hs0.trans hsle⟩
  rotate_left 2
  · intro d hd
    obtain ⟨f, hf, hfd⟩ := List.mem_filterMap.1 hd
    have := List.all_eq_true.1 hloc f hf
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp only [FFac.entData, Option.some.injEq,
      reduceCtorEq] at hfd
    subst hfd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2⟩
  all_goals
    have hc' : R'.charsP = (R'.charsP.1, R'.charsP.2.1, R'.charsP.2.2.1, R'.charsP.2.2.2) := rfl
    have hc : R.charsP = (R.charsP.1, R.charsP.2.1, R.charsP.2.2.1, R.charsP.2.2.2) := rfl
    have hS : R'.charsP.2.2.2 = R'.S := rfl
    have hu : R'.charsP.2.2.1 = (R'.weights.length : ℤ) := rfl
    unfold PkgExpr.fR at hfR
    rw [hc', hc] at hfR
    simp only at hfR
    rw [hn, hnent] at hres
  · unfold PkgExpr.fR
    rw [hc]
    simp only
    rw [← hS]; push_cast at hres ⊢; linarith
  · unfold PkgExpr.fsig PkgExpr.fR
    rw [hc]
    simp only
    rw [hL, ← hu]
    push_cast at hres hmu ⊢
    linarith

/-- The rule of the companion cases (8), (9) in the proof of Lemma 5.5
[claim_estimate_remainder_terms], with the pairing through `𝒢₁` of the exceptional subcase of
case (8), for the remainder terms of Type III, as the rule lemma of Type I does for Type I. -/
theorem pkg_rule_three (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 3) (p q : ℕ) (hpq' : 2 ≤ p + q)
    (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) (frule R'.rfacs) := by
  refine ⟨pkg_rem_valid ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR', ?_⟩
  obtain ⟨hRw, hfoc, -, -, -⟩ := R3_common ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨hS, hM4, hlab, hf0, hF0⟩ := R3_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨hb, hsumN⟩ := pkg_rem_lam ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hpair := pkg_rem_pair ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hext := (pkg_rfacs_ext R').1
  have hends := pkg_rem_ends ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hloopsL := (pkg_rem_loops ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2
  have hpos := R3_pos_len R'.rfacs
  have hnlE : ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum ≤ 2 := by
    omega
  have hout : ((R'.rfacs.filterMap FFac.entData).map R3out).sum = 6 := by
    rw [R3out_sum, hends 0 (by norm_num), hends 1 (by norm_num)]
    rfl
  have he : ∀ d ∈ R'.rfacs.filterMap FFac.entData, 0 ≤ d.2.2.2.1.i :=
    fun d hd => (hext d hd).2.2.2.2
  -- the loops have no `Λ̃` once the entries carry both
  have hloops : ((R'.rfacs.filterMap FFac.entData).map R3nl).sum = 2 →
      ∀ w ∈ fLoops R'.rfacs, FLet.lamt ∉ w ∧ 2 ≤ fresN w := by
    intro h2 w hw
    rw [R3_nl_cast _ hpos] at h2
    have h0 : ((fLoops R'.rfacs).map fun w => w.count FLet.lamt).sum = 0 := by
      have : ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum = 2 := by
        exact_mod_cast h2
      omega
    have hw0 : w.count FLet.lamt = 0 := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count FLet.lamt) hw)
      omega
    have hl : FLet.lamt ∉ w := List.count_eq_zero.1 hw0
    exact ⟨hl, hloopsL w hw hl⟩
  -- the entry `T Λ̃₁ M Λ̃₂ U` of `R` and the side of the focus
  obtain ⟨eM, heM, T', M, U, hTMU, -, -, hmid⟩ :=
    R3_Rlevel ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty
  have hE : ∀ w ∈ R.loops, PkgLetter.lw (.lamt 1) ∈ w → w.any PkgLetter.isEnt = true := by
    intro w hw h1
    obtain ⟨w', hw', hw'E, h1'⟩ := RH_ent_loop R eM heM (PkgLetter.lw (.lamt 1))
      (by rw [hTMU]; simp)
    rw [RH_uniq R hRw 1 w w' hw hw' h1 h1']
    exact hw'E
  obtain ⟨⟨o, side⟩, hs⟩ := Option.isSome_iff_exists.1
    (show R.ffocusSide.isSome = true by rw [(pkg_ffocusSide R).1]; exact hfoc)
  have hside := R3_side R hRw hE o side hs
  have hcnt : ∀ o' side', R.ffocusSide = some (o', side') →
      (R'.rfacs.filterMap FFac.entData).countP (fun d => decide (FEnt.role d ≤ 0)) = 1 := by
    intro o' side' hs'
    rw [← (pkg_rem_role0 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' o' side' hs').1]
    refine List.countP_congr fun d _ => ?_
    simp
  have hpq2 : 2 ≤ p + q := hpq'
  fin_cases o <;> cases side
  · -- `(0, left)`: never chosen
    exact absurd ((hside.1 rfl).1) (by decide)
  · -- case (9)
    obtain ⟨hfR1, x₀, ℓ, y, rW, eP, eW, dP, dW, hP, hW, hx₀, hℓ1, hℓ2, hrW⟩ :=
      R3_shape9 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q R' hR' hs
    have hne : ((ℓ, y, [rW, 0], eW, dW) : FEnt) ≠ (x₀, 3, [0, 0], eP, dP) := by
      intro h; simp only [Prod.mk.injEq] at h; omega
    have hy : y < 2 := by
      by_contra hy
      have hr0 : FEnt.role ((ℓ, y, [rW, 0], eW, dW) : FEnt) = 0 := by
        simp [FEnt.role, fInnerL]; omega
      have hr0' : FEnt.role ((x₀, 3, [0, 0], eP, dP) : FEnt) = 0 := by
        simp [FEnt.role, fInnerL]
      have h1 := hcnt 0 true hs
      rw [(List.perm_cons_erase hP).countP_eq, List.countP_cons, hr0'] at h1
      have h2 : 0 < ((R'.rfacs.filterMap FFac.entData).erase (x₀, 3, [0, 0], eP, dP)).countP
          (fun d => decide (FEnt.role d ≤ 0)) :=
        List.countP_pos_iff.2 ⟨_, (List.mem_erase_of_ne hne).2 hW, by simp [hr0]⟩
      simp only [le_refl, decide_true, ↓reduceIte] at h1
      omega
    have hfree := R3_free2 _ hpos hnlE hb _ _ hP hW hne rfl rfl
    obtain ⟨hPP, hU, hz, hnl⟩ := R3_case_9 R'.rfacs x₀ ℓ y rW eP eW dP dW hP hW hx₀ ⟨hℓ1, hℓ2⟩
      hy hrW hfree (by rw [R3_nl_cast _ hpos]; exact_mod_cast hnlE) hext
    exact R3_bound R' (p + q) R.fR R.fsig hpq2 hf0 hF0 hS hM4 (hloops hnl) hlab hpair he hnl
      hPP (by omega) (by omega) (fun _ => ⟨hfR1, hU⟩) (Or.inl hU)
  · -- `(1, left)`: excluded by `a₁ = a₂`, seen from both letters
    obtain ⟨h1, h0⟩ := hside.2 rfl rfl
    have := pkg_ffocusSide_pos R hRw 1 false hs
    omega
  · -- case (8)
    rcases R3_shape8 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q R' hR' hs with
      ⟨x₀, r, eP, dP, hP, hx₀, hr⟩ |
      ⟨ℓ₂, rR, x₀, ℓ₁, rL, eP, eL, dP, dL, hP, hΛ, hℓ₂, hℓ₂', hrR, hx₀, hℓ₁, hℓ₁', hrL⟩
    · have hfree := R3_free1 _ hpos hnlE hb _ hP rfl
      obtain ⟨hPP, hU, hz, hbb, hnl⟩ := R3_case_b R'.rfacs x₀ r eP dP hP hx₀ hr hfree hext hlab
        (hcnt 1 true hs) hout
      refine R3_bound R' (p + q) R.fR R.fsig hpq2 hf0 hF0 hS hM4 (hloops hnl) hlab hpair he hnl
        hPP hU (by omega) (fun h => by omega) (Or.inr (Or.inl ?_))
      have hb0 : 0 ≤ ((R'.rfacs.filterMap FFac.entData).map R3bb).sum :=
        List.sum_nonneg fun x hx => by
          obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
          unfold R3bb; split_ifs <;> simp
      by_cases hx : R.fR = 0 ∧ R.fsig = 0
      · have := (pkg_rem_pairG ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' hty hx.1 hx.2 _ hP
          rfl).2
        simp only [List.cons.injEq] at this
        have := hbb (by omega)
        omega
      · omega
    · have hne : ((x₀, ℓ₁, [0, rL], eL, dL) : FEnt) ≠ (ℓ₂, 3, [rR, 0], eP, dP) := by
        intro h; simp only [Prod.mk.injEq] at h; omega
      have hfree := R3_free2 _ hpos hnlE hb _ _ hP hΛ hne rfl rfl
      have h3 := hends 3 (by norm_num)
      simp only [show ¬ (3 : ℕ) < 2 by omega, ↓reduceIte] at h3
      obtain ⟨hPP, hU, hU4, hz, hnl⟩ := R3_case_a R'.rfacs (p + q) ℓ₂ rR x₀ ℓ₁ rL eP eL dP dL hP hΛ
        ⟨hℓ₂, hℓ₂'⟩ hrR hx₀ ⟨hℓ₁, hℓ₁'⟩ hrL hfree
        (by rw [R3_nl_cast _ hpos]; exact_mod_cast hnlE) hext hlab hout h3
      exact R3_bound R' (p + q) R.fR R.fsig hpq2 hf0 hF0 hS hM4 (hloops hnl) hlab hpair he hnl
        hPP hU (by omega) (fun h => by omega) (hU4.elim Or.inl fun h => Or.inr (Or.inr h))

end RBMTransitionEdge

end
