module

public import RBMTransitionEdge.Localized.Expansion.FRule
public import RBMTransitionEdge.Localized.Expansion.PkgInv2
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.RemStep
public import RBMTransitionEdge.Localized.Expansion.RemCounts
public import RBMTransitionEdge.Localized.Expansion.RemHalves
public import RBMTransitionEdge.Localized.Expansion.FRuleWard
public import RBMTransitionEdge.Localized.Expansion.RemCommon
public import RBMTransitionEdge.Localized.Expansion.RemTypeOne
public import RBMTransitionEdge.Localized.Expansion.Rem2ThreeRule
public import RBMTransitionEdge.Localized.Expansion.Rem2TwoRule
import all RBMTransitionEdge.Localized.Expansion.Rem2ThreeRule
import all RBMTransitionEdge.Localized.Expansion.Rem2TwoRule

@[expose] public section

/-!
# The rule lemma of Type I

For every expression of Type I expanded in the further expansion of the proof of Lemma 5.5
[claim_estimate_remainder_terms], every `p + q ≥ 2` and every derivative structure `R'` of
`𝓔^{(2)}_𝓡(p, q)`: the assignment `frule` of the factor list of the rules is valid, and its bound
with the prefactor passes the rows (Example 5.7 [example_estimate_reminder_reminder_terms] and the
companion cases (1)–(3)).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private R3PP R3u R3nl R3rr R3zz R3bb R3_bound R3_counts R3_common R3_two R3_first R3_second
  R3_fit_head R3_fit_hs R3_fit_isoY R3_cap0 R3_cap_succ R3_PP_of R3PP_free' R3_pos R3_pos'
  R3_pos_len R3_fst R3_sum_erase_nat
  from RBMTransitionEdge.Localized.Expansion.Rem2ThreeRule
open private R2T_final R2T_zgen R2T_g1 R2T_g2 R2T_g3 R2T_g4 R2T_g5 R2T_h1 R2T_h2 R2T_h3 R2T_h4
  R2T_h5 R2T_uc R2T_r R2T_e R2T_al R2T_fac R2T_isWt R2T_zip_mem R2T_zip_ex R2T_zof
  R2T_sum_nonpos R2T_sum_one R2T_sum_two R2T_lab4 R2T_class R2T_E_len R2T_S R2T_U R2T_rext
  R2T_qs_sumN R2T_qs_mem R2T_sumN_zero R2T_sumZ_nonneg R2T_fchosen_fst
  from RBMTransitionEdge.Localized.Expansion.Rem2TwoRule

/-! ### The entries with `Λ̃` -/

/-- The diagonal entry with one letter `Λ̃`, no resolvent before it and resolvents after it takes
the isotropic split at the row. -/
private theorem R1_fit_isoX (x r : ℕ) (ext : FMono) (det : Bool) (hr : 1 ≤ r)
    (he : ext.a = 0 ∧ ext.l = 0 ∧ ext.d = 0 ∧ ext.o = 0 ∧ 0 ≤ ext.i) (cap : List ℕ)
    (hcx : cap.getD x 0 ≤ 1) (kd : FKind) (o : FOpt)
    (h : fruleFit cap (x, x, [0, r], ext, det) false = some (kd, o)) :
    (∀ q ∈ o.val, R3PP (x, x, [0, r], ext, det) o q) ∧
      ∀ l, fuseOne ((x, x, [0, r], ext, det), some o) l = (if x = l then 1 else 0) := by
  obtain ⟨ks, hp⟩ : ∃ ks, FEnt.prefs (x, x, [0, r], ext, det) false = .isoX :: ks := by
    simp only [FEnt.prefs, ↓reduceIte, List.length_cons, List.length_nil]
    exact ⟨_, rfl⟩
  rw [R3_fit_head cap _ _ _ hp ⟨1, 0, 0,
      [((fhalf 1 0 true).mul ((FMono.psi r).mul ⟨0, 0, 0, 0, 0⟩)).mul ext]⟩
    (by simp only [List.getD_eq_getElem?_getD] at hcx; simp [fkindFit, fkindOpt]; omega)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
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

/-- The diagonal entry with one letter `Λ̃` and no resolvent, in the isotropic split at the row:
the five linear forms of the integer test. -/
private theorem R1_zdiag (x : ℕ) (ext : FMono) (det : Bool) (o : FOpt) (q : FMono)
    (hq : q ∈ o.val) (hx : ext.a = 0 ∧ ext.l = 0 ∧ ext.d = 0 ∧ ext.o = 0 ∧ 0 ≤ ext.i)
    (ho : fkindOpt (x, x, [0, 0], ext, det) .isoX = some o) :
    q.d = 1 ∧ q.o = 0 ∧ 0 ≤ q.i ∧ R2T_g1 (((x, x, [0, 0], ext, det), some o), q) ≤ 2 ∧
      R2T_g2 (((x, x, [0, 0], ext, det), some o), q) ≤ 3 ∧
      R2T_g3 (((x, x, [0, 0], ext, det), some o), q) ≤ 18 ∧
      R2T_g4 (((x, x, [0, 0], ext, det), some o), q) ≤ 6 ∧
      R2T_g5 (((x, x, [0, 0], ext, det), some o), q) ≤ 9 := by
  obtain ⟨ea, el, ed, eo, ei⟩ := hx
  obtain ⟨a', i, l, d₀, o₀⟩ := ext
  simp only at ea el ed eo ei
  subst ea el ed eo
  simp [fkindOpt] at ho
  subst ho
  simp only [List.mem_singleton] at hq
  subst hq
  simp only [R2T_g1, R2T_g2, R2T_g3, R2T_g4, R2T_g5, R2T_al, R2T_uc, R2T_r, R2T_e, FMono.psi,
    FMono.omega, fhalf, FMono.mul, List.sum_cons, List.sum_nil, add_zero]
  simp
  omega

/-! ### The first two steps of the rule -/

/-- The entry of role `0` and the entry of role `1` with one letter `Λ̃` each, treated at the
steps `0` and `1`, and the other entries without `Λ̃` and with a resolvent: the bounds of every
chosen entry, and the options and the uses of the two entries with `Λ̃`. -/
private theorem R1_core (F : List FFac) (P Λ : FEnt) (uP uΛ : ℕ → ℕ)
    (hP : P ∈ F.filterMap FFac.entData) (hΛ : Λ ∈ F.filterMap FFac.entData)
    (hP0 : FEnt.role P = 0) (hΛ1 : FEnt.role Λ = 1)
    (hPl : P.2.2.1.length = 2) (hΛl : Λ.2.2.1.length = 2)
    (hfree : ∀ d ∈ F.filterMap FFac.entData, d ≠ P → d ≠ Λ →
      d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum)
    (hnl : ((F.filterMap FFac.entData).map R3nl).sum ≤ 2)
    (hext : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i)
    (hΛlab : Λ.1 < 4 ∧ Λ.2.1 < 4)
    (hPfit : ∀ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 0) P false =
      some (kd, o) → (∀ q ∈ o.val, R3PP P o q) ∧ ∀ l, fuseOne (P, some o) l = uP l)
    (huP : ∀ l, uP l ≤ 1)
    (hΛfit : ∀ cap : List ℕ, cap.getD Λ.1 0 ≤ 1 → cap.getD Λ.2.1 0 ≤ 1 → ∀ kd o,
      fruleFit cap Λ false = some (kd, o) →
      (∀ q ∈ o.val, R3PP Λ o q) ∧ ∀ l, fuseOne (Λ, some o) l = uΛ l) :
    (∀ c ∈ fchosen F (frule F), ∀ o, c.2 = some o → ∀ q ∈ o.val, R3PP c.1 o q) ∧
      ∃ oP oΛ, (P, some oP) ∈ fchosen F (frule F) ∧ (Λ, some oΛ) ∈ fchosen F (frule F) ∧
        (∀ l, fuseOne (P, some oP) l = uP l) ∧ ∀ l, fuseOne (Λ, some oΛ) l = uΛ l := by
  obtain ⟨-, -, -, h0, h1, -⟩ := R3_two _ _ _ hP hΛ hP0 hΛ1 hPl hΛl hfree hnl
  obtain ⟨tP, -, -, hord0, kdP, oP, hfitP, hchP⟩ := R3_first F _ hP hP0 h0
  obtain ⟨-, hfuseP⟩ := hPfit kdP oP hfitP
  have hcap1 : ∀ l, l < 4 → (fruleCap (F.filterMap FFac.entData) false 1).getD l 0 = uP l := by
    intro l hl
    rw [R3_cap_succ F 0 tP l hl _ oP hord0 hchP, R3_cap0, hfuseP l]
    omega
  have hΛfit1 : ∀ kd o, fruleFit (fruleCap (F.filterMap FFac.entData) false 1) Λ false =
      some (kd, o) → (∀ q ∈ o.val, R3PP Λ o q) ∧ ∀ l, fuseOne (Λ, some o) l = uΛ l :=
    hΛfit _ (by rw [hcap1 _ hΛlab.1]; exact huP _) (by rw [hcap1 _ hΛlab.2]; exact huP _)
  obtain ⟨tΛ, -, -, -, kdΛ, oΛ, hfitΛ, hchΛ⟩ := R3_second F _ hΛ hΛ1 h0 h1
  refine ⟨R3_PP_of F fun t ht k kd o hk hfit hkd hko q hq => ?_, oP, oΛ,
    List.mem_of_getElem? hchP, List.mem_of_getElem? hchΛ, hfuseP, (hΛfit1 kdΛ oΛ hfitΛ).2⟩
  by_cases hdP : (F.filterMap FFac.entData)[t] = P
  · have : k < 1 := R3_pos _ 0 1 k t h0 hk (by rw [List.getD_eq_getElem _ _ ht, hdP, hP0])
    have hk0 : k = 0 := by omega
    subst hk0
    rw [hdP] at hfit ⊢
    exact (hPfit kd o hfit).1 q hq
  by_cases hdΛ : (F.filterMap FFac.entData)[t] = Λ
  · have a1 : k < 2 := R3_pos _ 1 2 k t h1 hk (by rw [List.getD_eq_getElem _ _ ht, hdΛ, hΛ1])
    have a2 : 1 ≤ k := R3_pos' _ 0 1 k t h0 hk
      (by rw [List.getD_eq_getElem _ _ ht, hdΛ, hΛ1]; omega)
    have hk1 : k = 1 := by omega
    subst hk1
    rw [hdΛ] at hfit ⊢
    exact (hΛfit1 kd o hfit).1 q hq
  obtain ⟨a, b⟩ := hfree _ (List.getElem_mem ht) hdP hdΛ
  exact R3PP_free' _ a b (hext _ (List.getElem_mem ht)) kd hkd o hko q hq

/-! ### The Ward uses of the entries without `Λ̃` -/

/-- A list of length `2` with two different members is a permutation of them. -/
private theorem R1_perm2 {α : Type*} (l : List α) (a b : α) (hl : l.length = 2) (ha : a ∈ l)
    (hb : b ∈ l) (hab : a ≠ b) : l.Perm [a, b] := by
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact List.Perm.refl _
  · exact List.Perm.swap _ _ _
  · exact absurd rfl hab

/-- A sum over a list is the sum over the members with a property and over the others. -/
private theorem R1_split {α : Type*} (L : List α) (p : α → Bool) (f : α → ℕ) :
    (L.map f).sum = ((L.filter p).map f).sum + ((L.filter fun x => !p x).map f).sum := by
  rw [← List.sum_append, ← List.map_append]
  exact ((List.filter_append_perm p L).map f).sum_eq.symm

/-- With exactly two entries with `Λ̃`, chosen with the options `o_P`, `o_Λ`: the uses `u_ℓ` of
the entries with `Λ̃` are theirs, and the ends `e_ℓ` of the entries without `Λ̃` are the ends of
all entries less theirs. -/
private theorem R1_ward (F : List FFac) (s : ℕ) (P Λ : FEnt) (oP oΛ : FOpt)
    (hcP : (P, some oP) ∈ fchosen F (frule F)) (hcΛ : (Λ, some oΛ) ∈ fchosen F (frule F))
    (hPΛ : P ≠ Λ) (hPl : 2 ≤ P.2.2.1.length) (hΛl : 2 ≤ Λ.2.2.1.length)
    (hcnt : (F.filterMap FFac.entData).countP (fun d => decide (2 ≤ d.2.2.1.length)) = 2)
    (hends : ∀ l : ℕ, l < 4 → ((F.filterMap FFac.entData).flatMap fun d => [d.1, d.2.1]).count l =
      if l < 2 then 3 else 1 + s) :
    (∀ l, fwardU F false l = fuseOne (P, some oP) l + fuseOne (Λ, some oΛ) l) ∧
      ∀ l, l < 4 → fwardE F false l + ([P.1, P.2.1].count l + [Λ.1, Λ.2.1].count l) =
        if l < 2 then 3 else 1 + s := by
  have hfst : (fchosen F (frule F)).map Prod.fst = F.filterMap FFac.entData := R3_fst F (frule F)
  have hperm : ((fchosen F (frule F)).filter fun c => decide (2 ≤ c.1.2.2.1.length)).Perm
      [(P, some oP), (Λ, some oΛ)] := by
    refine R1_perm2 _ _ _ ?_ (List.mem_filter.2 ⟨hcP, by simpa using hPl⟩)
      (List.mem_filter.2 ⟨hcΛ, by simpa using hΛl⟩) (fun h => hPΛ (congrArg Prod.fst h))
    have h := congrArg List.length (List.filter_map (f := Prod.fst)
      (p := fun d : FEnt => decide (2 ≤ d.2.2.1.length)) (l := fchosen F (frule F)))
    rw [hfst, List.length_map, ← List.countP_eq_length_filter, hcnt] at h
    exact h.symm
  refine ⟨fun l => ?_, fun l hl => ?_⟩
  · unfold fwardU
    rw [show fruleC F false = fchosen F (frule F) from rfl, (hperm.map _).sum_eq]
    simp
  · rw [← hends l hl, List.count_flatMap, ← hfst, List.map_map,
      R1_split _ (fun c => decide (2 ≤ c.1.2.2.1.length)), (hperm.map _).sum_eq]
    have hE : fwardE F false l = (((fchosen F (frule F)).filter fun c =>
        !decide (2 ≤ c.1.2.2.1.length)).map (List.count l ∘ (fun d => [d.1, d.2.1]) ∘
          Prod.fst)).sum := by
      unfold fwardE fruleC
      rw [List.filter_congr (q := fun c => !decide (2 ≤ c.1.2.2.1.length)) (fun c _ => by
        by_cases h : 2 ≤ c.1.2.2.1.length <;> simp [h] <;> omega)]
      congr 1
      refine List.map_congr_left fun c _ => ?_
      simp only [Function.comp, List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> simp_all
    rw [hE]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
    ring

/-- The fact `e_ℓ = 2 c_{ℓℓ} + Σ_{b ≠ ℓ} c_{ℓb}` at the four labels, the numbers `N_ℓ` by pairs,
and `ω ≥ Σ_ℓ min(N_ℓ, 2 - u_ℓ)`, written with `c_{ab}` for `a ≤ b`. -/
private theorem R1_pairs (F : List FFac)
    (h4 : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4) :
    fwardE F false 0 = 2 * fwardC F false 0 0 + fwardC F false 0 1 + fwardC F false 0 2 +
        fwardC F false 0 3 ∧
      fwardE F false 1 = 2 * fwardC F false 1 1 + fwardC F false 0 1 + fwardC F false 1 2 +
        fwardC F false 1 3 ∧
      fwardE F false 2 = 2 * fwardC F false 2 2 + fwardC F false 0 2 + fwardC F false 1 2 +
        fwardC F false 2 3 ∧
      fwardE F false 3 = 2 * fwardC F false 3 3 + fwardC F false 0 3 + fwardC F false 1 3 +
        fwardC F false 2 3 ∧
      min (fwardC F false 0 1) (2 - fwardU F false 0) +
        min (fwardC F false 0 2 + fwardC F false 1 2 + fwardC F false 2 3) (2 - fwardU F false 2) +
        min (fwardC F false 0 3 + fwardC F false 1 3) (2 - fwardU F false 3) ≤
        fwardW F false := by
  have hsym : ∀ a b, fwardC F false a b = fwardC F false b a := by
    intro a b
    unfold fwardC
    refine List.countP_congr fun c _ => ?_
    simp only [decide_eq_true_eq]
    tauto
  have e0 := frule_ends_pairs F false h4 0 (by norm_num)
  have e1 := frule_ends_pairs F false h4 1 (by norm_num)
  have e2 := frule_ends_pairs F false h4 2 (by norm_num)
  have e3 := frule_ends_pairs F false h4 3 (by norm_num)
  rw [show (List.range 4).filter (fun b => b != 0) = [1, 2, 3] from rfl] at e0
  rw [show (List.range 4).filter (fun b => b != 1) = [0, 2, 3] from rfl] at e1
  rw [show (List.range 4).filter (fun b => b != 2) = [0, 1, 3] from rfl] at e2
  rw [show (List.range 4).filter (fun b => b != 3) = [0, 1, 2] from rfl] at e3
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at e0 e1 e2 e3
  rw [hsym 1 0] at e1
  rw [hsym 2 0, hsym 2 1] at e2
  rw [hsym 3 0, hsym 3 1, hsym 3 2] at e3
  have hw := frule_ward_count F false
  obtain ⟨n0, n1, n2, n3⟩ := frule_wardN_pairs F false
  rw [show List.range 4 = [0, 1, 2, 3] from rfl] at hw
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, n0, n1, n2, n3,
    Nat.zero_min, zero_add] at hw
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ### The counts of the Ward uses in the three cases -/

set_option maxHeartbeats 1000000 in
-- The 32 cases of the three labels, each closed by `omega`.
/-- Case (1) (Example 5.7 [example_estimate_reminder_reminder_terms]): the uses of the four labels
with the entries `(x₂, 3)` with `Λ̃₂` and `(x₁, y₁)` with `Λ̃₁`, `x₁` outer, against the ends of the
entries without `Λ̃`. -/
private theorem R1_arith1 (x₂ x₁ y₁ s W : ℕ) (u e : ℕ → ℕ) (c : ℕ → ℕ → ℕ) (hx₂ : x₂ < 4)
    (hx₁ : x₁ < 2) (hy₁ : y₁ < 4) (hs : 2 ≤ s)
    (hu : ∀ l, u l = ((if x₂ = 3 then (if 3 = l then 1 else 0) else
      (if x₂ = l then 1 else 0) + (if 3 = l then 1 else 0)) +
      (if x₁ = y₁ then (if x₁ = l then 1 else 0) else
        (if x₁ = l then 1 else 0) + (if y₁ = l then 1 else 0))))
    (he : ∀ l, l < 4 → e l + ([x₂, 3].count l + [x₁, y₁].count l) = if l < 2 then 3 else 1 + s)
    (h0 : e 0 = 2 * c 0 0 + c 0 1 + c 0 2 + c 0 3) (h1 : e 1 = 2 * c 1 1 + c 0 1 + c 1 2 + c 1 3)
    (h2 : e 2 = 2 * c 2 2 + c 0 2 + c 1 2 + c 2 3) (h3 : e 3 = 2 * c 3 3 + c 0 3 + c 1 3 + c 2 3)
    (hW : min (c 0 1) (2 - u 0) + min (c 0 2 + c 1 2 + c 2 3) (2 - u 2) +
      min (c 0 3 + c 1 3) (2 - u 3) ≤ W) :
    3 ≤ u 0 + u 1 + u 2 + u 3 + W ∧ (4 ≤ u 0 + u 1 + u 2 + u 3 + W ∨ 3 ≤ s) := by
  have u0 := hu 0
  have u1 := hu 1
  have u2 := hu 2
  have u3 := hu 3
  have e0 := he 0 (by norm_num)
  have e1 := he 1 (by norm_num)
  have e2 := he 2 (by norm_num)
  have e3 := he 3 (by norm_num)
  interval_cases x₂ <;> interval_cases x₁ <;> interval_cases y₁ <;>
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at u0 u1 u2 u3 e0 e1 e2 e3 <;>
    norm_num at u0 u1 u2 u3 e0 e1 e2 e3 <;> omega

/-- Case (2): the uses with the entries `(x₁, 3)` with `Λ̃₁` and `(x₂, y₂)` with `Λ̃₂`, `y₂` outer,
against the ends of the entries without `Λ̃`. -/
private theorem R1_arith2 (x₁ x₂ y₂ s W : ℕ) (u e : ℕ → ℕ) (c : ℕ → ℕ → ℕ) (hx₁ : x₁ < 2)
    (hx₂ : x₂ < 4) (hy₂ : y₂ < 2)
    (hu : ∀ l, u l = ((if x₁ = l then 1 else 0) + (if 3 = l then 1 else 0)) +
      (if x₂ = y₂ then (if y₂ = l then 1 else 0) else
        (if x₂ = l then 1 else 0) + (if y₂ = l then 1 else 0)))
    (he : ∀ l, l < 4 → e l + ([x₁, 3].count l + [x₂, y₂].count l) = if l < 2 then 3 else 1 + s)
    (h0 : e 0 = 2 * c 0 0 + c 0 1 + c 0 2 + c 0 3) (h1 : e 1 = 2 * c 1 1 + c 0 1 + c 1 2 + c 1 3)
    (h2 : e 2 = 2 * c 2 2 + c 0 2 + c 1 2 + c 2 3) (h3 : e 3 = 2 * c 3 3 + c 0 3 + c 1 3 + c 2 3)
    (hW : min (c 0 1) (2 - u 0) + min (c 0 2 + c 1 2 + c 2 3) (2 - u 2) +
      min (c 0 3 + c 1 3) (2 - u 3) ≤ W) :
    4 ≤ u 0 + u 1 + u 2 + u 3 + W := by
  have u0 := hu 0
  have u1 := hu 1
  have u2 := hu 2
  have u3 := hu 3
  have e0 := he 0 (by norm_num)
  have e1 := he 1 (by norm_num)
  have e2 := he 2 (by norm_num)
  have e3 := he 3 (by norm_num)
  interval_cases x₁ <;> interval_cases x₂ <;> interval_cases y₂ <;>
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at u0 u1 u2 u3 e0 e1 e2 e3 <;>
    norm_num at u0 u1 u2 u3 e0 e1 e2 e3 <;> omega

/-- Case (3): the uses with the entries `(2, y₂)` with `Λ̃₂` and `(x₁, y₁)` with `Λ̃₁`, `x₁, y₁, y₂`
outer, against the ends of the entries without `Λ̃`: at least one Ward use. -/
private theorem R1_arith3 (x₁ y₁ y₂ s W : ℕ) (u e : ℕ → ℕ) (c : ℕ → ℕ → ℕ) (hx₁ : x₁ < 2)
    (hy₁ : y₁ < 2) (hy₂ : y₂ < 2)
    (hu : ∀ l, u l = ((if 2 = l then 1 else 0) + (if y₂ = l then 1 else 0)) +
      (if x₁ = y₁ then (if x₁ = l then 1 else 0) else
        (if x₁ = l then 1 else 0) + (if y₁ = l then 1 else 0)))
    (he : ∀ l, l < 4 → e l + ([2, y₂].count l + [x₁, y₁].count l) = if l < 2 then 3 else 1 + s)
    (h0 : e 0 = 2 * c 0 0 + c 0 1 + c 0 2 + c 0 3) (h1 : e 1 = 2 * c 1 1 + c 0 1 + c 1 2 + c 1 3)
    (h2 : e 2 = 2 * c 2 2 + c 0 2 + c 1 2 + c 2 3) (h3 : e 3 = 2 * c 3 3 + c 0 3 + c 1 3 + c 2 3)
    (hW : min (c 0 1) (2 - u 0) + min (c 0 2 + c 1 2 + c 2 3) (2 - u 2) +
      min (c 0 3 + c 1 3) (2 - u 3) ≤ W) :
    1 ≤ W := by
  have u0 := hu 0
  have u1 := hu 1
  have u2 := hu 2
  have u3 := hu 3
  have e0 := he 0 (by norm_num)
  have e1 := he 1 (by norm_num)
  have e2 := he 2 (by norm_num)
  have e3 := he 3 (by norm_num)
  interval_cases x₁ <;> interval_cases y₁ <;> interval_cases y₂ <;>
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at u0 u1 u2 u3 e0 e1 e2 e3 <;>
    norm_num at u0 u1 u2 u3 e0 e1 e2 e3 <;> omega

/-! ### The rule lemma -/

/-- The rule of Example 5.7 [example_estimate_reminder_reminder_terms] and the companion cases
(1)–(3) in the proof of Lemma 5.5 [claim_estimate_remainder_terms], for the remainder terms of Type
I: for every expression of Type I expanded in the further expansion, every `p + q ≥ 2` and every
derivative structure `R'` of `𝓔^{(2)}_𝓡(p, q)`, the assignment `frule` is valid and its bound, with
the prefactor `(DN)^{-1} N^{-3/2} N^{-(p+q+1)/2} N^{-S}`, passes the rows. -/
theorem pkg_rule_one (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 1) (p q : ℕ) (hpq' : 2 ≤ p + q)
    (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) (frule R'.rfacs) := by
  refine ⟨pkg_rem_valid ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR', ?_⟩
  obtain ⟨hRw, hfoc, -, -, -⟩ := R3_common ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨hS, hM4, hlab, hf0, hF0⟩ := R3_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨hb, hsumL⟩ := pkg_rem_lam ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hpair := pkg_rem_pair ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hext := (pkg_rfacs_ext R').1
  have hends := pkg_rem_ends ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hloopsL := (pkg_rem_loops ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2
  have he : ∀ d ∈ R'.rfacs.filterMap FFac.entData, 0 ≤ d.2.2.2.1.i :=
    fun d hd => (hext d hd).2.2.2.2
  obtain ⟨⟨o, side⟩, hs⟩ := Option.isSome_iff_exists.1
    (show R.ffocusSide.isSome = true by rw [(pkg_ffocusSide R).1]; exact hfoc)
  obtain ⟨hcs, hc0t, hc1f⟩ := pkg_ffocusSide_cases R (by rw [hty]; decide)
  obtain ⟨d₁, d₂, E₀, hperm, hl₁, hl₂, hE₀, hk1, hk2, hk3⟩ :=
    pkg_typeOne_lams ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q R' hR' o side hs
  -- the entries as `d₁ :: d₂ :: E₀`
  have hmem : ∀ d, d ∈ R'.rfacs.filterMap FFac.entData ↔ d = d₁ ∨ d = d₂ ∨ d ∈ E₀ := by
    intro d
    rw [hperm.mem_iff]
    simp
  have hsumZ : ∀ h : FEnt → ℤ, ((R'.rfacs.filterMap FFac.entData).map h).sum =
      h d₁ + h d₂ + (E₀.map h).sum := by
    intro h
    rw [(hperm.map h).sum_eq]
    simp only [List.map_cons, List.sum_cons]
    ring
  have hE₀b : ∀ d ∈ E₀, d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum := fun d hd =>
    ⟨hE₀ d hd, hb d ((hmem d).2 (Or.inr (Or.inr hd))) (hE₀ d hd)⟩
  have hE₀z : ∀ h : FEnt → ℤ, (∀ d : FEnt, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum → h d = 0) →
      (E₀.map h).sum = 0 := by
    intro h hh
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    exact hh d (hE₀b d hd).1 (hE₀b d hd).2
  have hfree : ∀ d ∈ R'.rfacs.filterMap FFac.entData, d ≠ d₁ → d ≠ d₂ →
      d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum := by
    intro d hd h1 h2
    rcases (hmem d).1 hd with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact hE₀b d h
  have hnl : ((R'.rfacs.filterMap FFac.entData).map R3nl).sum = 2 := by
    rw [hsumZ, hE₀z R3nl fun d h _ => by unfold R3nl; rw [h]; norm_num]
    unfold R3nl
    rw [hl₁, hl₂]
    norm_num
  have hloops : ∀ w ∈ fLoops R'.rfacs, FLet.lamt ∉ w ∧ 2 ≤ fresN w := by
    intro w hw
    have h2 : ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum = 2 := by
      rw [(hperm.map _).sum_eq]
      simp only [List.map_cons, List.sum_cons, hl₁, hl₂]
      rw [List.sum_eq_zero fun x hx => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
        simp [hE₀ d hd]]
      rfl
    have hw0 : w.count FLet.lamt = 0 := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count FLet.lamt) hw)
      omega
    have hl : FLet.lamt ∉ w := List.count_eq_zero.1 hw0
    exact ⟨hl, hloopsL w hw hl⟩
  have hcnt : (R'.rfacs.filterMap FFac.entData).countP
      (fun d => decide (2 ≤ d.2.2.1.length)) = 2 := by
    rw [hperm.countP_eq, List.countP_cons, List.countP_cons,
      List.countP_eq_zero.2 fun d hd => by simp [hE₀ d hd]]
    simp [hl₁, hl₂]
  have hsplit := frule_uses_split R'.rfacs false hlab
  have hU : ((List.range 4).map fun l => (fuses R'.rfacs (frule R'.rfacs) l : ℤ)).sum =
      fwardU R'.rfacs false 0 + fwardU R'.rfacs false 1 + fwardU R'.rfacs false 2 +
        fwardU R'.rfacs false 3 + fwardW R'.rfacs false := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hsplit
    rw [show frule R'.rfacs = ⟨frk, fruleE (R'.rfacs.filterMap FFac.entData) false⟩ from rfl]
    simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at h ⊢
    push_cast at h ⊢
    linarith
  obtain ⟨c0, c1, c2, c3, hW⟩ := R1_pairs R'.rfacs hlab
  rcases hcs with h | h | h | h
  · rw [hs] at h
    exact absurd h (by simp)
  · -- case (1), Example 5.7: rule (i), the right side of `Λ̃₂`
    rw [hs] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hy₂, ⟨r₂, hr₂, hp₂⟩, hx₁, r₁, hr₁, hp₁⟩ := hk1 rfl
    clear hk1 hk2 hk3
    obtain ⟨x₁, y₁, P₁, e₁, b₁⟩ := d₁
    obtain ⟨x₂, y₂, P₂, e₂, b₂⟩ := d₂
    simp only at hy₂ hp₂ hx₁ hp₁
    subst hy₂ hp₂ hp₁
    have hd₁ : ((x₁, y₁, [0, r₁], e₁, b₁) : FEnt) ∈ R'.rfacs.filterMap FFac.entData :=
      (hmem _).2 (Or.inl rfl)
    have hd₂ : ((x₂, 3, [r₂, 0], e₂, b₂) : FEnt) ∈ R'.rfacs.filterMap FFac.entData :=
      (hmem _).2 (Or.inr (Or.inl rfl))
    have hlab₁ := hlab _ hd₁
    have hlab₂ := hlab _ hd₂
    simp only at hlab₁ hlab₂
    have hne : ((x₂, 3, [r₂, 0], e₂, b₂) : FEnt) ≠ (x₁, y₁, [0, r₁], e₁, b₁) := by
      intro h
      simp only [Prod.mk.injEq, List.cons.injEq] at h
      omega
    obtain ⟨hPP, oP, oΛ, hcP, hcΛ, hfP, hfΛ⟩ := R1_core R'.rfacs (x₂, 3, [r₂, 0], e₂, b₂)
      (x₁, y₁, [0, r₁], e₁, b₁)
      (fun l => if x₂ = 3 then (if 3 = l then 1 else 0) else
        (if x₂ = l then 1 else 0) + (if 3 = l then 1 else 0))
      (fun l => if x₁ = y₁ then (if x₁ = l then 1 else 0) else
        (if x₁ = l then 1 else 0) + (if y₁ = l then 1 else 0))
      hd₂ hd₁ (by simp [FEnt.role, fInnerL])
      (by simp [FEnt.role, fInnerL, show ¬ 2 ≤ x₁ by omega, show r₁ ≠ 0 by omega])
      rfl rfl (fun d hd h1 h2 => hfree d hd h2 h1) (by omega) hext hlab₁
      (fun kd o hfit => by
        by_cases hx : x₂ = 3
        · subst hx
          obtain ⟨a, b⟩ := R3_fit_isoY 3 r₂ e₂ b₂ hr₂ (hext _ hd₂) _
            (by rw [R3_cap0]; omega) kd o hfit
          exact ⟨a, fun l => by rw [b l]; simp⟩
        · obtain ⟨a, b⟩ := R3_fit_hs x₂ 3 r₂ 0 e₂ b₂ hx (hext _ hd₂) _
            (by rw [R3_cap0]; omega) (by rw [R3_cap0]; omega) kd o hfit
          exact ⟨a, fun l => by rw [b l]; simp [hx]⟩)
      (fun l => by split_ifs <;> omega)
      (fun cap hcx hcy kd o hfit => by
        by_cases hxy : x₁ = y₁
        · subst hxy
          obtain ⟨a, b⟩ := R1_fit_isoX x₁ r₁ e₁ b₁ hr₁ (hext _ hd₁) cap hcx kd o hfit
          exact ⟨a, fun l => by rw [b l]; simp⟩
        · obtain ⟨a, b⟩ := R3_fit_hs x₁ y₁ 0 r₁ e₁ b₁ hxy (hext _ hd₁) cap hcx hcy kd o hfit
          exact ⟨a, fun l => by rw [b l]; simp [hxy]⟩)
    obtain ⟨hwU, hwE⟩ := R1_ward R'.rfacs (p + q) _ _ oP oΛ hcP hcΛ hne (by simp) (by simp)
      hcnt hends
    obtain ⟨a1, a2⟩ := R1_arith1 x₂ x₁ y₁ (p + q) (fwardW R'.rfacs false) (fwardU R'.rfacs false)
      (fwardE R'.rfacs false) (fwardC R'.rfacs false) hlab₂.1 hx₁ hlab₁.2 hpq'
      (fun l => by rw [hwU l, hfP l, hfΛ l]) (fun l hl => hwE l hl) c0 c1 c2 c3 hW
    have hzz : ((R'.rfacs.filterMap FFac.entData).map R3zz).sum = 0 := by
      rw [hsumZ, hE₀z R3zz fun d _ h => by unfold R3zz; simp; omega]
      unfold R3zz
      simp
      omega
    refine R3_bound R' (p + q) R.fR R.fsig hpq' hf0 hF0 hS hM4 hloops hlab hpair he hnl hPP
      (by rw [hU]; omega) (by omega) (fun h => by omega) ?_
    rcases a2 with a2 | a2
    · exact Or.inl (by rw [hU]; omega)
    · exact Or.inr (Or.inr a2)
  · -- case (2): rule (iii), the right side of `Λ̃₁`
    rw [hs] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hy₂, ⟨r₂, hr₂, hp₂⟩, hx₁, hy₁, hp₁⟩ := hk2 rfl
    have hfR1 : 1 ≤ R.fR := by
      have h := pkg_inv_empty ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
      unfold PkgExpr.emptySides at h
      rw [hty, hc0t hs] at h
      simp only [List.count_cons, List.count_nil, beq_iff_eq] at h
      split_ifs at h <;> push_cast at h <;> omega
    clear hk1 hk2 hk3
    obtain ⟨x₁, y₁, P₁, e₁, b₁⟩ := d₁
    obtain ⟨x₂, y₂, P₂, e₂, b₂⟩ := d₂
    simp only at hy₂ hp₂ hx₁ hy₁ hp₁
    subst hy₁ hp₂ hp₁
    have hd₁ : ((x₁, 3, [0, 0], e₁, b₁) : FEnt) ∈ R'.rfacs.filterMap FFac.entData :=
      (hmem _).2 (Or.inl rfl)
    have hd₂ : ((x₂, y₂, [r₂, 0], e₂, b₂) : FEnt) ∈ R'.rfacs.filterMap FFac.entData :=
      (hmem _).2 (Or.inr (Or.inl rfl))
    have hlab₁ := hlab _ hd₁
    have hlab₂ := hlab _ hd₂
    simp only at hlab₁ hlab₂
    have hne : ((x₁, 3, [0, 0], e₁, b₁) : FEnt) ≠ (x₂, y₂, [r₂, 0], e₂, b₂) := by
      intro h
      simp only [Prod.mk.injEq, List.cons.injEq] at h
      omega
    obtain ⟨hPP, oP, oΛ, hcP, hcΛ, hfP, hfΛ⟩ := R1_core R'.rfacs (x₁, 3, [0, 0], e₁, b₁)
      (x₂, y₂, [r₂, 0], e₂, b₂)
      (fun l => (if x₁ = l then 1 else 0) + (if 3 = l then 1 else 0))
      (fun l => if x₂ = y₂ then (if y₂ = l then 1 else 0) else
        (if x₂ = l then 1 else 0) + (if y₂ = l then 1 else 0))
      hd₁ hd₂ (by simp [FEnt.role, fInnerL])
      (by simp [FEnt.role, fInnerL, show ¬ 2 ≤ y₂ by omega, show r₂ ≠ 0 by omega])
      rfl rfl hfree (by omega) hext hlab₂
      (fun kd o hfit => by
        obtain ⟨a, b⟩ := R3_fit_hs x₁ 3 0 0 e₁ b₁ (by omega) (hext _ hd₁) _
          (by rw [R3_cap0]; omega) (by rw [R3_cap0]; omega) kd o hfit
        exact ⟨a, b⟩)
      (fun l => by split_ifs <;> omega)
      (fun cap hcx hcy kd o hfit => by
        by_cases hxy : x₂ = y₂
        · subst hxy
          obtain ⟨a, b⟩ := R3_fit_isoY x₂ r₂ e₂ b₂ hr₂ (hext _ hd₂) cap hcx kd o hfit
          exact ⟨a, fun l => by rw [b l]; simp⟩
        · obtain ⟨a, b⟩ := R3_fit_hs x₂ y₂ r₂ 0 e₂ b₂ hxy (hext _ hd₂) cap hcx hcy kd o hfit
          exact ⟨a, fun l => by rw [b l]; simp [hxy]⟩)
    obtain ⟨hwU, hwE⟩ := R1_ward R'.rfacs (p + q) _ _ oP oΛ hcP hcΛ hne (by simp) (by simp)
      hcnt hends
    have a1 := R1_arith2 x₁ x₂ y₂ (p + q) (fwardW R'.rfacs false) (fwardU R'.rfacs false)
      (fwardE R'.rfacs false) (fwardC R'.rfacs false) hx₁ hlab₂.1 hy₂
      (fun l => by rw [hwU l, hfP l, hfΛ l]) (fun l hl => hwE l hl) c0 c1 c2 c3 hW
    have hzz : ((R'.rfacs.filterMap FFac.entData).map R3zz).sum = 1 := by
      rw [hsumZ, hE₀z R3zz fun d _ h => by unfold R3zz; simp; omega]
      unfold R3zz
      simp
      omega
    exact R3_bound R' (p + q) R.fR R.fsig hpq' hf0 hF0 hS hM4 hloops hlab hpair he hnl hPP
      (by rw [hU]; omega) (by omega)
      (fun _ => ⟨by exact_mod_cast hfR1, by rw [hU]; omega⟩)
      (Or.inl (by rw [hU]; omega))
  · -- case (3): rule (iv), the left side of `Λ̃₂`
    rw [hs] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hx₂, hy₂, hp₂, hx₁, hy₁, hp₁⟩ := hk3 rfl
    have hfR2 : 2 ≤ R.fR := by
      have h := pkg_inv_empty ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
      unfold PkgExpr.emptySides at h
      obtain ⟨h1, h0⟩ := hc1f hs
      rw [hty, h1, h0] at h
      simp only [List.count_cons, List.count_nil, beq_iff_eq] at h
      split_ifs at h <;> push_cast at h <;> omega
    clear hk1 hk2 hk3
    have hlen₂ : ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.1.length - 1).sum = 2 := by
      rw [(hperm.map _).sum_eq]
      simp only [List.map_cons, List.sum_cons, hl₁, hl₂]
      rw [List.sum_eq_zero fun x hx => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
        simp [hE₀ d hd]]
      rfl
    have hcnt₁ : (R'.rfacs.filterMap FFac.entData).countP (fun d => decide (d = d₁)) = 1 := by
      have hne : d₂ ≠ d₁ := by
        intro h
        rw [h] at hx₂
        omega
      rw [hperm.countP_eq, List.countP_cons, List.countP_cons,
        List.countP_eq_zero.2 fun d hd => by
          simp only [decide_eq_true_eq]
          intro h
          have := hE₀ d hd
          rw [h, hl₁] at this
          omega]
      simp [hne]
    obtain ⟨x₁, y₁, P₁, e₁, b₁⟩ := d₁
    obtain ⟨x₂, y₂, P₂, e₂, b₂⟩ := d₂
    simp only at hx₂ hy₂ hp₂ hx₁ hy₁ hp₁
    subst hx₂ hp₂ hp₁
    have hd₁ : ((x₁, y₁, [0, 0], e₁, b₁) : FEnt) ∈ R'.rfacs.filterMap FFac.entData :=
      (hmem _).2 (Or.inl rfl)
    have hd₂ : ((2, y₂, [0, 0], e₂, b₂) : FEnt) ∈ R'.rfacs.filterMap FFac.entData :=
      (hmem _).2 (Or.inr (Or.inl rfl))
    have hne : ((2, y₂, [0, 0], e₂, b₂) : FEnt) ≠ (x₁, y₁, [0, 0], e₁, b₁) := by
      intro h
      simp only [Prod.mk.injEq] at h
      omega
    -- the option of every entry
    have hcl := R2T_class R'.rfacs _ rfl (R2T_E_len R'.rfacs) hcnt.le (fun d hd hl => by
        rcases (hmem d).1 hd with rfl | rfl | h
        · exact ⟨rfl, fun _ => rfl⟩
        · exact ⟨rfl, fun _ => rfl⟩
        · have := hE₀ d h
          omega)
      ⟨_, hd₂, by simp [FEnt.role, fInnerL]⟩
    have hopt : ∀ d ∈ R'.rfacs.filterMap FFac.entData, d.2.2.1 = [0, 0] →
        ∃ o, (d, some o) ∈ fchosen R'.rfacs (frule R'.rfacs) ∧
          fkindOpt d (if d.1 = d.2.1 then .isoX else .hs) = some o ∧
          ∀ l, fuseOne (d, some o) l = if d.1 = d.2.1 then (if d.1 = l then 1 else 0) else
            (if d.1 = l then 1 else 0) + (if d.2.1 = l then 1 else 0) := by
      intro d hd hp
      rw [← R2T_fchosen_fst R'.rfacs (frule R'.rfacs)] at hd
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
      obtain ⟨o, hco, hk⟩ := hcl c hc
      have hk2 : fkindOpt c.1 (if c.1.1 = c.1.2.1 then .isoX else .hs) = some o := by
        rcases hk with ⟨hl, -⟩ | ⟨-, hk⟩
        · rw [hp] at hl
          simp at hl
        · exact hk
      refine ⟨o, by rw [← hco]; exact hc, hk2, fun l => ?_⟩
      obtain ⟨⟨x, y, P, ext, det⟩, oc⟩ := c
      simp only at hp hk2 ⊢
      subst hp
      by_cases hxy : x = y
      · subst hxy
        simp [fkindOpt] at hk2
        subst hk2
        simp [fuseOne]
      · simp [fkindOpt, hxy] at hk2
        subst hk2
        simp only [fuseOne, hxy, ↓reduceIte]
        split_ifs <;> omega
    obtain ⟨oP, hcP, -, hfP⟩ := hopt _ hd₂ rfl
    obtain ⟨oΛ, hcΛ, hkΛ, hfΛ⟩ := hopt _ hd₁ rfl
    obtain ⟨hwU, hwE⟩ := R1_ward R'.rfacs (p + q) _ _ oP oΛ hcP hcΛ hne (by simp) (by simp)
      hcnt hends
    have hW1 := R1_arith3 x₁ y₁ y₂ (p + q) (fwardW R'.rfacs false) (fwardU R'.rfacs false)
      (fwardE R'.rfacs false) (fwardC R'.rfacs false) hx₁ hy₁ hy₂
      (fun l => by
        rw [hwU l, hfP l, hfΛ l]
        simp only [show (2 : ℕ) ≠ y₂ by omega, ↓reduceIte])
      (fun l hl => hwE l hl) c0 c1 c2 c3 hW
    -- an entry without `Λ̃` in its Ward row or column
    obtain ⟨cW, hcW, hcWp⟩ := List.countP_pos_iff.1 (show 0 < fwardW R'.rfacs false by omega)
    obtain ⟨oW, hoW, hkW⟩ := hcl cW hcW
    simp only [hoW, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcWp
    obtain ⟨hlW, hsW⟩ := hcWp
    obtain ⟨hlW1, kW, hkWp, hkWo⟩ : cW.1.2.2.1.length = 1 ∧
        ∃ k ∈ FEnt.prefs cW.1 false, fkindOpt cW.1 k = some oW := by
      rcases hkW with h | ⟨h, -⟩
      · exact h
      · omega
    have hucW : R2T_uc cW = 1 := by
      unfold R2T_uc
      rw [hoW]
      simp only
      by_cases hxy : cW.1.1 = cW.1.2.1
      · exfalso
        simp only [FEnt.prefs, hxy, ↓reduceIte, hlW1, Nat.sub_self] at hkWp
        simp at hkWp
        subst hkWp
        simp only [fkindOpt, Option.some.injEq] at hkWo
        subst hkWo
        simp at hsW
      · simp only [hxy, ↓reduceIte]
        exact hsW
    intro m hm
    obtain ⟨qs, hF2, hmq⟩ :=
      (fboundM_mem R'.rfacs (frule R'.rfacs) (frule_run_some R'.rfacs false) m).1 hm
    have hl := hF2.length_eq
    -- the five linear forms of every entry
    have hz : ∀ z ∈ (fchosen R'.rfacs (frule R'.rfacs)).zip qs,
        z.2.d = z.1.1.2.2.1.length - 1 ∧ z.2.o = 0 ∧ 0 ≤ z.2.i ∧
        (z.1.1 ≠ (x₁, y₁, [0, 0], e₁, b₁) → R2T_g1 z ≤ 0 ∧ R2T_g2 z ≤ 0 ∧ R2T_g3 z ≤ 0 ∧
          R2T_g4 z ≤ 0 ∧ R2T_g5 z ≤ 0 ∧
          (z.1.1.2.2.1.length = 1 → R2T_uc z.1 = 1 → R2T_g1 z ≤ -4) ∧
          (z.1.1.2.2.1.length = 2 → R2T_g1 z ≤ -4 ∧ R2T_g2 z ≤ -15)) ∧
        (z.1.1 = (x₁, y₁, [0, 0], e₁, b₁) → R2T_g1 z ≤ 2 ∧ R2T_g2 z ≤ 3 ∧ R2T_g3 z ≤ 18 ∧
          R2T_g4 z ≤ 6 ∧ R2T_g5 z ≤ 9) := by
      intro z hz
      obtain ⟨o, ho, hq⟩ := R2T_zip_mem hF2 z hz
      have hcC : z.1 ∈ fchosen R'.rfacs (frule R'.rfacs) := (List.of_mem_zip hz).1
      have hdE : z.1.1 ∈ R'.rfacs.filterMap FFac.entData := by
        rw [← R2T_fchosen_fst R'.rfacs (frule R'.rfacs)]
        exact List.mem_map_of_mem hcC
      obtain ⟨o', ho', hc⟩ := hcl z.1 hcC
      rw [ho] at ho'
      obtain rfl := Option.some.inj ho'
      obtain ⟨⟨d, oc⟩, q⟩ := z
      simp only at ho hq hc hdE ⊢
      subst ho
      by_cases hd1 : d = (x₁, y₁, [0, 0], e₁, b₁)
      · subst hd1
        have hk : fkindOpt (x₁, y₁, [0, 0], e₁, b₁) (if x₁ = y₁ then .isoX else .hs) = some o := by
          rcases hc with ⟨hl, -⟩ | ⟨-, hk⟩
          · simp at hl
          · exact hk
        by_cases hxy : x₁ = y₁
        · subst hxy
          simp only [↓reduceIte] at hk
          obtain ⟨a1, a2, a3, b1, b2, b3, b4, b5⟩ := R1_zdiag x₁ e₁ b₁ o q hq (hext _ hd₁) hk
          exact ⟨by simp only [List.length_cons, List.length_nil]; omega, a2, a3,
            fun h => absurd rfl h, fun _ => ⟨b1, b2, b3, b4, b5⟩⟩
        · obtain ⟨a1, a2, a3, b1, b2, b3, b4, b5, -⟩ := R2T_zgen _ o q hq (hext _ hd₁)
            (Or.inr ⟨rfl, rfl, hk, Or.inr hxy⟩)
          exact ⟨a1, a2, a3, fun h => absurd rfl h,
            fun _ => ⟨by omega, by omega, by omega, by omega, by omega⟩⟩
      · have hc' : (d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum ∧
            ∃ k ∈ FEnt.prefs d false, fkindOpt d k = some o) ∨
            (d.2.2.1.length = 2 ∧ d.2.2.1.head? = some 0 ∧
              fkindOpt d (if d.1 = d.2.1 then .isoX else .hs) = some o ∧
              (1 ≤ d.2.2.1.sum ∨ d.1 ≠ d.2.1)) := by
          rcases hc with ⟨hl, k, hk, hk'⟩ | ⟨hl, hk⟩
          · exact Or.inl ⟨hl, hb d hdE hl, k, hk, hk'⟩
          · rcases (hmem d).1 hdE with h | h | h
            · exact absurd h hd1
            · subst h
              exact Or.inr ⟨hl, rfl, hk, Or.inr (by simp only; omega)⟩
            · have := hE₀ d h
              omega
        obtain ⟨a1, a2, a3, b1, b2, b3, b4, b5, c1, c2, -, -⟩ := R2T_zgen d o q hq (hext d hdE) hc'
        exact ⟨a1, a2, a3, fun _ => ⟨b1, b2, b3, b4, b5, fun hl hu => c1 hl (Or.inl hu), c2⟩,
          fun h => absurd h hd1⟩
    -- the entries of `d₁`, `d₂` and of the Ward use among the monomials
    obtain ⟨zL, hzL, hzLd⟩ := R2T_zof R'.rfacs qs hF2 _ hd₁
    obtain ⟨zP, hzP, hzPd⟩ := R2T_zof R'.rfacs qs hF2 _ hd₂
    obtain ⟨qW, hzW⟩ := R2T_zip_ex hF2 cW hcW
    have hcntZ : ((fchosen R'.rfacs (frule R'.rfacs)).zip qs).countP
        (fun z => decide (z.1.1 = (x₁, y₁, [0, 0], e₁, b₁))) = 1 := by
      have hm : ((fchosen R'.rfacs (frule R'.rfacs)).zip qs).map (fun z => z.1.1) =
          R'.rfacs.filterMap FFac.entData := by
        have h1 : ((fchosen R'.rfacs (frule R'.rfacs)).zip qs).map Prod.fst =
            fchosen R'.rfacs (frule R'.rfacs) := List.map_fst_zip (by omega)
        rw [show (fun z : (FEnt × Option FOpt) × FMono => z.1.1) = Prod.fst ∘ Prod.fst from rfl,
          ← List.map_map, h1, R2T_fchosen_fst]
      rw [← hcnt₁, ← hm, List.countP_map]
      rfl
    have hEr : ∀ z ∈ ((fchosen R'.rfacs (frule R'.rfacs)).zip qs).erase zL,
        z.1.1 ≠ (x₁, y₁, [0, 0], e₁, b₁) := by
      have h := (List.perm_cons_erase hzL).countP_eq
        (fun z => decide (z.1.1 = (x₁, y₁, [0, 0], e₁, b₁)))
      rw [hcntZ, List.countP_cons] at h
      simp only [hzLd, decide_true, ↓reduceIte] at h
      have h0 : (((fchosen R'.rfacs (frule R'.rfacs)).zip qs).erase zL).countP
          (fun z => decide (z.1.1 = (x₁, y₁, [0, 0], e₁, b₁))) = 0 := by omega
      intro z hz hzd
      exact absurd (by simpa using hzd) (List.countP_eq_zero.1 h0 z hz)
    have hPL : zP ≠ zL := fun h => hne (by rw [← hzPd, ← hzLd, h])
    have hWL : (cW, qW) ≠ zL := fun h => by
      have : cW.1.2.2.1.length = 2 := by rw [show cW = zL.1 by rw [← h], hzLd]; rfl
      omega
    have hWP : zP ≠ (cW, qW) := fun h => by
      have : cW.1.2.2.1.length = 2 := by rw [show cW = zP.1 by rw [h], hzPd]; rfl
      omega
    have hzP' := (List.mem_erase_of_ne hPL).2 hzP
    have hzW' := (List.mem_erase_of_ne hWL).2 hzW
    have hsplit3 : ∀ g : (FEnt × Option FOpt) × FMono → ℤ,
        (((fchosen R'.rfacs (frule R'.rfacs)).zip qs).map g).sum =
          g zL + ((((fchosen R'.rfacs (frule R'.rfacs)).zip qs).erase zL).map g).sum := by
      intro g
      rw [((List.perm_cons_erase hzL).map g).sum_eq, List.map_cons, List.sum_cons]
    have hneg : ∀ z ∈ ((fchosen R'.rfacs (frule R'.rfacs)).zip qs).erase zL,
        R2T_g1 z ≤ 0 ∧ R2T_g2 z ≤ 0 ∧ R2T_g3 z ≤ 0 ∧ R2T_g4 z ≤ 0 ∧ R2T_g5 z ≤ 0 := by
      intro z hz'
      obtain ⟨-, -, -, h, -⟩ := hz z (List.mem_of_mem_erase hz')
      obtain ⟨b1, b2, b3, b4, b5, -⟩ := h (hEr z hz')
      exact ⟨b1, b2, b3, b4, b5⟩
    obtain ⟨-, -, -, -, bL⟩ := hz zL hzL
    obtain ⟨bL1, bL2, bL3, bL4, bL5⟩ := bL hzLd
    obtain ⟨-, -, -, bP, -⟩ := hz zP hzP
    obtain ⟨-, -, -, -, -, -, bP2⟩ := bP (by rw [hzPd]; exact hne)
    rw [hzPd] at bP2
    obtain ⟨bP21, bP22⟩ := bP2 rfl
    obtain ⟨-, -, -, bW, -⟩ := hz (cW, qW) hzW
    obtain ⟨-, -, -, -, -, bW1, -⟩ := bW (fun h => by
      have : cW.1.2.2.1.length = 2 := by simp only at h; rw [h]; rfl
      omega)
    have bW1' := bW1 hlW1 hucW
    have hG1 := hsplit3 R2T_g1
    have hG1' := R2T_sum_two _ R2T_g1 (fun z hz' => (hneg z hz').1) zP (cW, qW) hzP' hzW' hWP
    have hG2 := hsplit3 R2T_g2
    have hG2' := R2T_sum_one _ R2T_g2 (fun z hz' => (hneg z hz').2.1) zP hzP'
    have hG3 := hsplit3 R2T_g3
    have hG3' := R2T_sum_nonpos _ R2T_g3 fun z hz' => (hneg z hz').2.2.1
    have hG4 := hsplit3 R2T_g4
    have hG4' := R2T_sum_nonpos _ R2T_g4 fun z hz' => (hneg z hz').2.2.2.1
    have hG5 := hsplit3 R2T_g5
    have hG5' := R2T_sum_nonpos _ R2T_g5 fun z hz' => (hneg z hz').2.2.2.2
    -- the loops and light weights
    have hloopsF : ∀ f ∈ R'.rfacs, ∀ w, f = .loop w → FLet.lamt ∉ w ∧ 2 ≤ fresN w := by
      intro f hf w rfl
      exact hloops w (List.mem_filterMap.2 ⟨_, hf, rfl⟩)
    have hfac := fun f hf => R2T_fac f (hloopsF f hf)
    -- the counts
    have hS' := R2T_S R' R.fR (pkg_rem_fR ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
    have hU' := R2T_U R R' (p + q) (pkg_rem_mu ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
      (pkg_rem_nent ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
    have hfpi : R'.fpi ≤ 1 := by unfold PkgExpr.fpi; split_ifs <;> simp
    have hZE0 : 0 ≤ ((R'.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum :=
      R2T_sumZ_nonneg _ _ fun d hd => (hext d hd).2.2.2.2
    rw [R2T_rext R']
    refine R2T_final R'.rfacs qs hF2 hlab ((p + q : ℕ) : ℤ) R.fR R.fsig R'.fpi R'.S _ hS' hU' rfl
      (-6) (-12) 18 6 9 0 0 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.1)
      (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.1)
      (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.2.1)
      (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.2.2.1)
      (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.2.2.2) ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_ ?_ m
      hmq
    · rw [R2T_qs_sumN _ qs hl FMono.d (fun d => d.2.2.1.length - 1) fun z hz' => (hz z hz').1,
        R2T_fchosen_fst, hlen₂, R2T_sumN_zero (R'.rfacs.map FFac.fixV) FMono.d fun x hx' => by
          obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'; exact (hfac f hf).1]
    · rw [R2T_qs_sumN _ qs hl FMono.o (fun _ => 0) fun z hz' => (hz z hz').2.1,
        R2T_sumN_zero (R'.rfacs.map FFac.fixV) FMono.o fun x hx' => by
          obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'; exact (hfac f hf).2.1]
      simp only [add_zero]
      exact R2T_sumN_zero _ _ fun _ _ => rfl
    · have h1 := R2T_sumZ_nonneg qs FMono.i fun q hq => by
        obtain ⟨z, hz', rfl⟩ := R2T_qs_mem _ qs hl q hq; exact (hz z hz').2.2.1
      have h2 := R2T_sumZ_nonneg (R'.rfacs.map FFac.fixV) FMono.i fun x hx' => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'; exact (hfac f hf).2.2.1
      omega
    all_goals
      try simp only [Nat.sub_self, Nat.cast_zero, Nat.cast_ofNat]
      push_cast
      omega

end RBMTransitionEdge

end
