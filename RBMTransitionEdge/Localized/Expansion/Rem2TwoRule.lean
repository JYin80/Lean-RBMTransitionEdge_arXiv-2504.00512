module

public import RBMTransitionEdge.Localized.Expansion.FRuleRun
public import RBMTransitionEdge.Localized.Expansion.PkgInv2
public import RBMTransitionEdge.Localized.Expansion.PkgLists
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.RemStep
public import RBMTransitionEdge.Localized.Expansion.RemCounts
public import RBMTransitionEdge.Localized.Expansion.RemHalves
public import RBMTransitionEdge.Localized.Expansion.FOpts
public import RBMTransitionEdge.Localized.Expansion.FRule
public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.FFactor
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.FOpts
import all RBMTransitionEdge.Localized.Expansion.FRule
import all RBMTransitionEdge.Localized.Expansion.FEntWords
import all RBMTransitionEdge.Localized.Expansion.FFactor
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.RemHalves

@[expose] public section

/-!
# The rule lemma of Type II

For every expression of Type II expanded in the further expansion of the proof of Lemma 5.5
[claim_estimate_remainder_terms], every `p + q ≥ 2` and every derivative structure `R'` of
`𝓔^{(2)}_𝓡(p, q)`: the assignment `frule` of the factor list of the rules is valid, and its bound
with the prefactor passes the rows (the companion cases (5), (6)).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The `ℓ²` uses of an entry with its option, as counted in `fuses`. -/
private def R2T_uc (c : FEnt × Option FOpt) : ℕ :=
  match c.2 with
  | some o => o.cx + if c.1.1 = c.1.2.1 then 0 else o.cy
  | none => 0

/-- The number of resolvents of an entry minus one. -/
private def R2T_r (c : FEnt × Option FOpt) : ℤ := (c.1.2.2.1.sum : ℤ) - 1

/-- The power of `Im m` (doubled) of the paired letters of an entry. -/
private def R2T_e (c : FEnt × Option FOpt) : ℤ := c.1.2.2.2.1.i

/-- The power of `N` (doubled) of one monomial of an entry, with `N^{-1/2}` per `ℓ²` use and
`N^{-1}` per resolvent beyond the first. -/
private def R2T_al (z : (FEnt × Option FOpt) × FMono) : ℤ :=
  z.2.a - R2T_uc z.1 - 2 * R2T_r z.1

/-- The five linear forms of the integer test on one entry, normalized by its resolvents. -/
private def R2T_g1 (z : (FEnt × Option FOpt) × FMono) : ℤ :=
  6 * R2T_al z - 2 * z.2.i + 4 * z.2.l + 4 * R2T_r z.1 + 2 * R2T_e z.1
private def R2T_g2 (z : (FEnt × Option FOpt) × FMono) : ℤ :=
  18 * R2T_al z - 3 * z.2.i + 6 * z.2.l + 15 * R2T_r z.1 + 3 * R2T_e z.1
private def R2T_g3 (z : (FEnt × Option FOpt) × FMono) : ℤ :=
  18 * R2T_al z + 12 * z.2.l + 3 * z.2.i - 3 * R2T_e z.1
private def R2T_g4 (z : (FEnt × Option FOpt) × FMono) : ℤ :=
  6 * R2T_al z + 6 * z.2.l
private def R2T_g5 (z : (FEnt × Option FOpt) × FMono) : ℤ :=
  18 * R2T_al z + 9 * z.2.l + 9 * R2T_r z.1

/-- One entry without `Λ̃`. -/
private theorem R2T_ent0 (x y r : ℕ) (e : ℤ) (det : Bool) (k : FKind) (o : FOpt) (q : FMono)
    (hk : k ∈ FEnt.prefs (x, y, [r], ⟨0, e, 0, 0, 0⟩, det) false)
    (ho : fkindOpt (x, y, [r], ⟨0, e, 0, 0, 0⟩, det) k = some o) (hq : q ∈ o.val)
    (he : 0 ≤ e) (hr : 1 ≤ r) :
    let z : (FEnt × Option FOpt) × FMono := (((x, y, [r], ⟨0, e, 0, 0, 0⟩, det), some o), q)
    q.d = 0 ∧ q.o = 0 ∧ 0 ≤ q.i ∧ R2T_g1 z ≤ 0 ∧ R2T_g2 z ≤ 0 ∧ R2T_g3 z ≤ 0 ∧
      R2T_g4 z ≤ 0 ∧ R2T_g5 z ≤ 0 ∧ (R2T_uc z.1 = 1 ∨ 2 ≤ r → R2T_g1 z ≤ -4) := by
  intro z
  simp only [FEnt.prefs, List.length_singleton, Nat.sub_self] at hk
  by_cases hxy : x = y
  · simp [hxy] at hk
    subst hk
    simp only [fkindOpt, List.sum_cons, List.sum_nil, add_zero, List.length_singleton,
      Nat.sub_self, Option.some.injEq] at ho
    subst ho
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [z, R2T_g1, R2T_g2, R2T_g3, R2T_g4, R2T_g5, R2T_al, R2T_uc, R2T_r, R2T_e, FMono.psi,
      FMono.mul, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> simp <;> omega
  · have hk' : k = .wardX ∨ k = .wardY ∨ k = .sup := by
      simp only [hxy] at hk
      split_ifs at hk <;> simp at hk <;> tauto
    clear hk
    rcases hk' with rfl | rfl | rfl <;>
      simp only [fkindOpt, hxy, ↓reduceIte, List.sum_cons, List.sum_nil, add_zero,
        List.length_singleton, Nat.sub_self, Option.some.injEq] at ho <;>
      subst ho <;>
      simp only [List.mem_singleton] at hq <;>
      subst hq <;>
      simp only [z, R2T_g1, R2T_g2, R2T_g3, R2T_g4, R2T_g5, R2T_al, R2T_uc, R2T_r, R2T_e,
        FMono.psi, FMono.omega, FMono.mul, List.sum_cons, List.sum_nil, add_zero, hxy] <;>
      split_ifs <;> first | contradiction | (simp; omega)

/-- One entry with one `Λ̃`, empty left part, in the Hilbert–Schmidt norm or the split at `Λ̃`. -/
private theorem R2T_ent1 (x y r : ℕ) (e : ℤ) (det : Bool) (o : FOpt) (q : FMono)
    (ho : fkindOpt (x, y, [0, r], ⟨0, e, 0, 0, 0⟩, det)
      (if x = y then FKind.isoX else FKind.hs) = some o) (hq : q ∈ o.val)
    (he : 0 ≤ e) (hr : 1 ≤ r ∨ x ≠ y) :
    let z : (FEnt × Option FOpt) × FMono := (((x, y, [0, r], ⟨0, e, 0, 0, 0⟩, det), some o), q)
    q.d = 1 ∧ q.o = 0 ∧ 0 ≤ q.i ∧ R2T_g1 z ≤ 0 ∧ R2T_g2 z ≤ 0 ∧ R2T_g3 z ≤ 0 ∧
      R2T_g4 z ≤ 0 ∧ R2T_g5 z ≤ 0 ∧ (R2T_g1 z ≤ -4 ∧ R2T_g2 z ≤ -15) ∧
      (1 ≤ r → R2T_g1 z ≤ -6 ∧ R2T_g2 z ≤ -18 ∧ R2T_g3 z ≤ -18 ∧ R2T_g4 z ≤ -6 ∧
        R2T_g5 z ≤ -18) ∧ (2 ≤ r → R2T_g1 z ≤ -10) := by
  intro z
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true, fkindOpt, List.length_cons, List.length_singleton, List.head?_cons,
      List.drop_one, List.tail_cons, List.sum_cons, List.sum_nil, add_zero] at ho
    simp at ho
    subst ho
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [z, R2T_g1, R2T_g2, R2T_g3, R2T_g4, R2T_g5, R2T_al, R2T_uc, R2T_r, R2T_e,
      FMono.psi, FMono.omega, fhalf, FMono.mul, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> simp <;> omega
  · simp only [hxy, ite_false, fkindOpt, List.length_cons, List.length_singleton,
      List.sum_cons, List.sum_nil, add_zero, Option.some.injEq] at ho
    subst ho
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [z, R2T_g1, R2T_g2, R2T_g3, R2T_g4, R2T_g5, R2T_al, R2T_uc, R2T_r, R2T_e,
      FMono.psi, FMono.omega, fhalf, FMono.mul, List.sum_cons, List.sum_nil, add_zero, hxy]
    split_ifs <;> simp <;> omega

/-! ### Sums over lists -/

private theorem R2T_sum_nonpos {α : Type*} (L : List α) (f : α → ℤ) (hf : ∀ z ∈ L, f z ≤ 0) :
    (L.map f).sum ≤ 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hf x (by simp)
    have h2 := ih fun z hz => hf z (by simp [hz])
    omega

private theorem R2T_sum_one {α : Type*} [DecidableEq α] (L : List α) (f : α → ℤ)
    (hf : ∀ z ∈ L, f z ≤ 0) (a : α) (ha : a ∈ L) : (L.map f).sum ≤ f a := by
  have h := (List.perm_cons_erase ha).map f
  rw [h.sum_eq, List.map_cons, List.sum_cons]
  have := R2T_sum_nonpos (L.erase a) f fun z hz => hf z (List.mem_of_mem_erase hz)
  omega

private theorem R2T_sum_two {α : Type*} [DecidableEq α] (L : List α) (f : α → ℤ)
    (hf : ∀ z ∈ L, f z ≤ 0) (a b : α) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    (L.map f).sum ≤ f a + f b := by
  have h := (List.perm_cons_erase ha).map f
  rw [h.sum_eq, List.map_cons, List.sum_cons]
  have := R2T_sum_one (L.erase a) f (fun z hz => hf z (List.mem_of_mem_erase hz)) b
    ((List.mem_erase_of_ne (Ne.symm hab)).2 hb)
  omega

private theorem R2T_sum_three {α : Type*} [DecidableEq α] (L : List α) (f : α → ℤ)
    (hf : ∀ z ∈ L, f z ≤ 0) (a b c : α) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : (L.map f).sum ≤ f a + f b + f c := by
  have h := (List.perm_cons_erase ha).map f
  rw [h.sum_eq, List.map_cons, List.sum_cons]
  have := R2T_sum_two (L.erase a) f (fun z hz => hf z (List.mem_of_mem_erase hz)) b c
    ((List.mem_erase_of_ne (Ne.symm hab)).2 hb) ((List.mem_erase_of_ne (Ne.symm hac)).2 hc) hbc
  omega

private theorem R2T_nat_two {α : Type*} [DecidableEq α] (L : List α) (f : α → ℕ) (a b : α)
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : f a + f b ≤ (L.map f).sum := by
  have h := (List.perm_cons_erase ha).map f
  rw [h.sum_eq, List.map_cons, List.sum_cons]
  have := List.le_sum_of_mem
    (List.mem_map_of_mem (f := f) ((List.mem_erase_of_ne (Ne.symm hab)).2 hb))
  omega

private theorem R2T_nat_three {α : Type*} [DecidableEq α] (L : List α) (f : α → ℕ) (a b c : α)
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c ≤ (L.map f).sum := by
  have h := (List.perm_cons_erase ha).map f
  rw [h.sum_eq, List.map_cons, List.sum_cons]
  have := R2T_nat_two (L.erase a) f b c ((List.mem_erase_of_ne (Ne.symm hab)).2 hb)
    ((List.mem_erase_of_ne (Ne.symm hac)).2 hc) hbc
  omega

private theorem R2T_zip_mem {α β : Type*} {R : α → β → Prop} {C : List α} {qs : List β}
    (h : List.Forall₂ R C qs) : ∀ z ∈ C.zip qs, R z.1 z.2 := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro z hz
    simp only [List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hab
    · exact ih z hz

private theorem R2T_zip_ex {α β : Type*} {R : α → β → Prop} {C : List α} {qs : List β}
    (h : List.Forall₂ R C qs) : ∀ c ∈ C, ∃ q, (c, q) ∈ C.zip qs := by
  induction h with
  | nil => simp
  | @cons a b _ _ _ _ ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨b, by simp⟩
    · obtain ⟨q, hq⟩ := ih c hc
      exact ⟨q, by simp [hq]⟩

private theorem R2T_prodL (L : List FMono) : FMono.prodL L =
    ⟨(L.map FMono.a).sum, (L.map FMono.i).sum, (L.map FMono.l).sum, (L.map FMono.d).sum,
      (L.map FMono.o).sum⟩ := by
  have key : ∀ (L : List FMono) (m : FMono), L.foldl FMono.mul m =
      ⟨m.a + (L.map FMono.a).sum, m.i + (L.map FMono.i).sum, m.l + (L.map FMono.l).sum,
        m.d + (L.map FMono.d).sum, m.o + (L.map FMono.o).sum⟩ := by
    intro L
    induction L with
    | nil => intro m; simp
    | cons x L ih =>
      intro m
      rw [List.foldl_cons, ih]
      simp only [FMono.mul, List.map_cons, List.sum_cons, FMono.mk.injEq]
      omega
  unfold FMono.prodL
  rw [key]
  simp

/-! ### The loops and light weights -/

/-- The resolvents of a loop, `1` for a light weight. -/
private def R2T_un (f : FFac) : ℤ :=
  match f with
  | .loop w => fresN w
  | .wt _ _ => 1
  | .ent _ _ _ => 0

/-- Twice the resolvents of a loop minus one. -/
private def R2T_sh (f : FFac) : ℤ :=
  match f with
  | .loop w => 2 * ((fresN w : ℤ) - 1)
  | _ => 0

/-- The power of `N` (doubled) of a loop or a light weight, normalized by its resolvents. -/
private def R2T_be (f : FFac) : ℤ := f.fixV.a - R2T_sh f

/-- The five linear forms of the integer test on a loop or a light weight. -/
private def R2T_h1 (f : FFac) : ℤ :=
  6 * R2T_be f - 2 * f.fixV.i + 4 * f.fixV.l + 4 * R2T_un f
private def R2T_h2 (f : FFac) : ℤ :=
  18 * R2T_be f - 3 * f.fixV.i + 6 * f.fixV.l + 15 * R2T_un f
private def R2T_h3 (f : FFac) : ℤ :=
  18 * R2T_be f + 12 * f.fixV.l + 3 * f.fixV.i
private def R2T_h4 (f : FFac) : ℤ :=
  6 * R2T_be f + 6 * f.fixV.l
private def R2T_h5 (f : FFac) : ℤ :=
  18 * R2T_be f + 9 * f.fixV.l + 9 * R2T_un f

/-- A factor other than a loop with `Λ̃`. -/
private theorem R2T_fac (f : FFac) (hf : ∀ w, f = .loop w → FLet.lamt ∉ w ∧ 2 ≤ fresN w) :
    f.fixV.d = 0 ∧ f.fixV.o = 0 ∧ 0 ≤ f.fixV.i ∧ R2T_h1 f ≤ 0 ∧ R2T_h2 f ≤ 0 ∧ R2T_h3 f ≤ 0 ∧
      R2T_h4 f ≤ 0 ∧ R2T_h5 f ≤ 0 := by
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
  · simp [FFac.fixV, R2T_h1, R2T_h2, R2T_h3, R2T_h4, R2T_h5, R2T_be, R2T_sh, R2T_un]
  · obtain ⟨h1, h2⟩ := hf w rfl
    have hc : w.countP (· == FLet.lamt) = 0 := by
      rw [List.countP_eq_zero]
      intro z hz
      simp only [beq_iff_eq]
      rintro rfl
      exact h1 hz
    have hv : (FFac.loop w).fixV = FMono.psi (fresN w) := by
      simp only [FFac.fixV, hc, ↓reduceIte]; rfl
    simp only [R2T_h1, R2T_h2, R2T_h3, R2T_h4, R2T_h5, R2T_be, R2T_sh, R2T_un, hv, FMono.psi]
    split_ifs <;> simp <;> omega
  · simp [FFac.fixV, R2T_h1, R2T_h2, R2T_h3, R2T_h4, R2T_h5, R2T_be, R2T_sh, R2T_un]

/-- The size of the loop of `Λ̃₂` without resolvent: `⟨Λ²⟩`, with `Im m` when the gain applies. -/
private theorem R2T_fixL (w : List FLet) (h1 : w.count FLet.lamt = 1) (h0 : fresN w = 0) :
    (FFac.loop w).fixV = ⟨-2, 0, 0, 2, 0⟩ ∨ (FFac.loop w).fixV = ⟨-2, 2, 0, 2, 0⟩ := by
  have hc : w.countP (· == FLet.lamt) = 1 := h1
  unfold FFac.fixV
  simp only [hc]
  split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl | exact absurd h0 ‹_› |
    (exfalso; omega)

/-- The gain of the loop `⟨𝔐_a Λ̃ 𝔐_b E_x⟩`, `a ≠ b`. -/
private theorem R2T_fixL_gain (w : List FLet) (h1 : w.count FLet.lamt = 1) (h0 : fresN w = 0)
    (t : ℕ) (ht : t < w.length) (a b : Fin 2) (pa pb : Bool) (x : ℕ) (hab : a ≠ b)
    (hrot : w.rotate t = [.det a pa, .lamt, .det b pb, .proj x]) :
    (FFac.loop w).fixV = ⟨-2, 2, 0, 2, 0⟩ := by
  have hc : w.countP (· == FLet.lamt) = 1 := h1
  unfold FFac.fixV
  simp only [hc]
  split_ifs <;> first | rfl | exact absurd h0 ‹_› | (exfalso; omega) |
    (exfalso; rename_i hng; exact hng (List.any_eq_true.2 ⟨t, List.mem_range.2 ht, by
      rw [hrot]; simp [hab]⟩))

/-- The quantities of the loop of `Λ̃₂` without resolvent. -/
private theorem R2T_facL (w : List FLet) (h1 : w.count FLet.lamt = 1) (h0 : fresN w = 0) :
    (FFac.loop w).fixV.d = 2 ∧ (FFac.loop w).fixV.o = 0 ∧ 0 ≤ (FFac.loop w).fixV.i ∧
      (FFac.loop w).fixV.i ≤ 2 ∧ R2T_un (.loop w) = 0 ∧
      R2T_h1 (.loop w) = -2 * (FFac.loop w).fixV.i ∧
      R2T_h2 (.loop w) = -3 * (FFac.loop w).fixV.i ∧
      R2T_h3 (.loop w) = 3 * (FFac.loop w).fixV.i ∧ R2T_h4 (.loop w) = 0 ∧
      R2T_h5 (.loop w) = 0 := by
  simp only [R2T_h1, R2T_h2, R2T_h3, R2T_h4, R2T_h5, R2T_be, R2T_sh, R2T_un, h0]
  rcases R2T_fixL w h1 h0 with h | h <;> rw [h] <;> simp

/-! ### The run of the rule -/

open private FO_fchosen from RBMTransitionEdge.Localized.Expansion.FOpts

private theorem R2T_fchosen_fst (F : List FFac) (g : FAsg) :
    (fchosen F g).map Prod.fst = F.filterMap FFac.entData := by
  rw [FO_fchosen]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

private theorem R2T_chosen (F : List FFac) (c : FEnt × Option FOpt)
    (hc : c ∈ fchosen F (frule F)) :
    ∃ k t kd o, (fruleOrd (F.filterMap FFac.entData))[k]? = some t ∧
      (F.filterMap FFac.entData)[t]? = some c.1 ∧ c.2 = some o ∧
      fruleFit (fruleCap (F.filterMap FFac.entData) false k) c.1 false = some (kd, o) ∧
      kd ∈ c.1.prefs false ∧ fkindOpt c.1 kd = some o := by
  set E := F.filterMap FFac.entData with hE
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hc
  have hlen : (fchosen F (frule F)).length = E.length := by
    rw [FO_fchosen]; simp [E]
  have htl : t < E.length := hlen ▸ (List.getElem?_eq_some_iff.1 ht).1
  obtain ⟨d, hd⟩ : ∃ d, E[t]? = some d := ⟨_, List.getElem?_eq_getElem htl⟩
  have htm : t ∈ fruleOrd E := (frule_run_order E).1.symm.subset (List.mem_range.2 htl)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 htm
  obtain ⟨⟨kd, o⟩, hfit⟩ := Option.isSome_iff_exists.1 (frule_run_fits F false k t d hk hd)
  obtain ⟨h1, h2, h3⟩ := frule_run_chosen F false k t d hk hd kd o hfit
  have hcd : c = (d, some o) := by
    have : (fchosen F (frule F))[t]? = some (d, some o) := h3
    rw [ht] at this
    exact Option.some.inj this
  subst hcd
  exact ⟨k, t, kd, o, hk, hd, rfl, hfit, h1, h2⟩

private theorem R2T_ord_role (E : List FEnt) (j₁ j₂ t₁ t₂ : ℕ) (hj : j₁ < j₂)
    (h₁ : (fruleOrd E)[j₁]? = some t₁) (h₂ : (fruleOrd E)[j₂]? = some t₂) :
    (E.getD t₁ FEnt.dflt).role ≤ (E.getD t₂ FEnt.dflt).role := by
  have hp := List.pairwise_iff_getElem.1 (frule_run_order E).2
  obtain ⟨hl₁, rfl⟩ := List.getElem?_eq_some_iff.1 h₁
  obtain ⟨hl₂, rfl⟩ := List.getElem?_eq_some_iff.1 h₂
  exact hp j₁ j₂ hl₁ hl₂ hj

private theorem R2T_getD_range (E : List FEnt) :
    (List.range E.length).map (fun t => E.getD t FEnt.dflt) = E := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

private theorem R2T_cnt_take (E : List FEnt) (p : FEnt → Bool) (m : ℕ) (hm : m ≤ E.length)
    (h : ∀ j < m, ∀ t, (fruleOrd E)[j]? = some t → p (E.getD t FEnt.dflt) = true) :
    m ≤ E.countP p := by
  have hperm := (frule_run_order E).1
  have hnd : ((fruleOrd E).take m).Nodup :=
    (hperm.nodup_iff.2 List.nodup_range).sublist (List.take_sublist _ _)
  have hsub : (fruleOrd E).take m ⊆
      (List.range E.length).filter fun t => p (E.getD t FEnt.dflt) := by
    intro t ht
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    have hjm : j < m := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      simp at this; omega
    rw [List.getElem?_take, ite_eq_left_iff.2 (fun h => absurd hjm h)] at hj
    have htE : t < E.length :=
      List.mem_range.1 (hperm.subset (List.mem_of_getElem? hj))
    exact List.mem_filter.2 ⟨List.mem_range.2 htE, h j hjm t hj⟩
  have h1 := hnd.length_le_of_subset hsub
  have hlen : ((fruleOrd E).take m).length = m := by
    simp [hperm.length_eq]; omega
  have h2 : ((List.range E.length).filter fun t => p (E.getD t FEnt.dflt)).length =
      E.countP p := by
    rw [← List.countP_eq_length_filter]
    conv_rhs => rw [← R2T_getD_range E]
    rw [List.countP_map]
    rfl
  omega

private theorem R2T_fit_head (cap : List ℕ) (d : FEnt) (k : FKind) (rest : List FKind) (o : FOpt)
    (hp : d.prefs false = k :: rest) (hf : fkindFit false frk cap d [] k = some (0, o)) :
    fruleFit cap d false = some (k, o) := by
  unfold fruleFit
  rw [hp, List.findSome?_cons, hf]
  rfl

/-- An entry with one `Λ̃` takes the Hilbert–Schmidt norm (distinct labels) or the split at its
first `Λ̃` (equal labels) when every label has at most one use. -/
private theorem R2T_fit1 (x y : ℕ) (p0 p1 : ℕ) (ext : FMono) (det : Bool) (cap : List ℕ)
    (hh : x = y → p0 = 0) (hcap : ∀ l, cap.getD l 0 ≤ 1) :
    ∃ o, fruleFit cap (x, y, [p0, p1], ext, det) false =
        some ((if x = y then FKind.isoX else FKind.hs), o) ∧
      fkindOpt (x, y, [p0, p1], ext, det) (if x = y then FKind.isoX else FKind.hs) = some o ∧
      ∀ l, fuseOne ((x, y, [p0, p1], ext, det), some o) l ≤ 1 := by
  by_cases hxy : x = y
  · subst hxy
    obtain rfl := hh rfl
    have hc := hcap x
    simp only [ite_true]
    obtain ⟨rest, hp⟩ : ∃ rest, FEnt.prefs (x, x, [0, p1], ext, det) false = .isoX :: rest :=
      ⟨_, by simp [FEnt.prefs]; rfl⟩
    obtain ⟨o, ho⟩ : ∃ o, fkindOpt (x, x, [0, p1], ext, det) .isoX = some o :=
      Option.isSome_iff_exists.1 (by simp [fkindOpt])
    have ho' := ho
    simp only [fkindOpt] at ho'
    simp at ho'
    subst ho'
    refine ⟨_, R2T_fit_head _ _ _ rest _ hp ?_, ho, ?_⟩
    · simp only [fkindFit, ho]
      simp only [List.getD_eq_getElem?_getD] at hc
      simp
      omega
    · intro l
      simp only [fuseOne]
      split_ifs <;> simp
  · have hc := hcap x
    have hc' := hcap y
    simp only [hxy, ite_false]
    obtain ⟨rest, hp⟩ : ∃ rest, FEnt.prefs (x, y, [p0, p1], ext, det) false = .hs :: rest :=
      ⟨_, by simp [FEnt.prefs, hxy]; rfl⟩
    have ho : fkindOpt (x, y, [p0, p1], ext, det) .hs =
        some ⟨1, 1, 0, [(fhalf 1 (p0 + p1) true).mul ext]⟩ := by
      simp [fkindOpt, hxy]
    refine ⟨_, R2T_fit_head _ _ _ rest _ hp ?_, ho, ?_⟩
    · simp only [fkindFit, ho]
      simp only [List.getD_eq_getElem?_getD] at hc hc'
      simp [hxy]
      omega
    · intro l
      simp only [fuseOne]
      split_ifs <;> simp_all

private theorem R2T_frk (l : ℕ) :
    frk[l]?.getD 0 = if l = 0 then 2 else if l = 1 then 3 else if l = 3 then 1 else 0 := by
  rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with h | h | h | h | h
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · rw [List.getElem?_eq_none (by simp [frk]; omega)]
    simp only [Option.getD_none]
    split_ifs <;> omega

/-- An entry without `Λ̃` with one inner label takes its Ward row or column when every label has at
most one use. -/
private theorem R2T_fitW (x y r : ℕ) (ext : FMono) (det : Bool) (cap : List ℕ)
    (hin : (2 ≤ x ∧ y < 2) ∨ (x < 2 ∧ 2 ≤ y)) (hcap : ∀ l, cap.getD l 0 ≤ 1) :
    ∃ k o, fruleFit cap (x, y, [r], ext, det) false = some (k, o) ∧
      R2T_uc ((x, y, [r], ext, det), some o) = 1 := by
  have hc := hcap x
  have hc' := hcap y
  simp only [List.getD_eq_getElem?_getD] at hc hc'
  have hxy : x ≠ y := by omega
  rcases hin with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨rest, hp⟩ : ∃ rest, FEnt.prefs (x, y, [r], ext, det) false = .wardX :: rest :=
      ⟨_, by simp [FEnt.prefs, hxy, fInnerL, h1, h2]; rfl⟩
    have ho : fkindOpt (x, y, [r], ext, det) .wardX =
        some ⟨1, 0, 1, [((FMono.omega r).mul ⟨0, 0, 0, 0, 0⟩).mul ext]⟩ := by
      simp [fkindOpt, hxy]
    refine ⟨_, ⟨1, 0, 1, [((FMono.omega r).mul ⟨0, 0, 0, 0, 0⟩).mul ext]⟩,
      R2T_fit_head _ _ _ rest _ hp ?_, by simp [R2T_uc, hxy]⟩
    simp only [fkindFit, ho]
    have hr := R2T_frk x
    have hr' := R2T_frk y
    simp [hxy]
    split_ifs at hr hr' <;> omega
  · obtain ⟨rest, hp⟩ : ∃ rest, FEnt.prefs (x, y, [r], ext, det) false = .wardY :: rest :=
      ⟨_, by simp [FEnt.prefs, hxy, fInnerL, h1, h2]; rfl⟩
    have ho : fkindOpt (x, y, [r], ext, det) .wardY =
        some ⟨0, 1, -1, [((FMono.omega r).mul ⟨0, 0, 0, 0, 0⟩).mul ext]⟩ := by
      simp [fkindOpt, hxy]
    refine ⟨_, ⟨0, 1, -1, [((FMono.omega r).mul ⟨0, 0, 0, 0, 0⟩).mul ext]⟩,
      R2T_fit_head _ _ _ rest _ hp ?_, by simp [R2T_uc, hxy]⟩
    simp only [fkindFit, ho]
    have hr := R2T_frk x
    have hr' := R2T_frk y
    simp [hxy]
    split_ifs at hr hr' <;> omega

private theorem R2T_role_le1 (d : FEnt) : d.role ≤ 1 ↔ 2 ≤ d.2.2.1.length := by
  unfold FEnt.role
  split_ifs <;> simp_all

private theorem R2T_role2 (d : FEnt) (h : d.role = 2) :
    d.2.2.1.length < 2 ∧ 1 ≤ d.2.2.1.sum ∧ ((2 ≤ d.1 ∧ d.2.1 < 2) ∨ (d.1 < 2 ∧ 2 ≤ d.2.1)) := by
  rcases Nat.lt_or_ge d.2.2.1.length 2 with h1 | h1
  · simp only [FEnt.role, not_le.2 h1, ↓reduceIte] at h
    split_ifs at h with h3
    · simp only [fInnerL, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h3
      refine ⟨h1, h3.1, ?_⟩
      by_cases hx : 2 ≤ d.1 <;> by_cases hy : 2 ≤ d.2.1 <;> simp_all
    · omega
  · simp only [FEnt.role, h1, ↓reduceIte] at h
    split_ifs at h <;> omega

private theorem R2T_getD (E : List FEnt) (t : ℕ) (d : FEnt) (h : E[t]? = some d) :
    E.getD t FEnt.dflt = d := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- The entry treated first has role `0`. -/
private theorem R2T_first (E : List FEnt) (h0 : ∃ d ∈ E, d.role = 0) :
    ∃ t d, (fruleOrd E)[0]? = some t ∧ E[t]? = some d ∧ d.role = 0 := by
  obtain ⟨d, hd, hr⟩ := h0
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hd
  have htl := (List.getElem?_eq_some_iff.1 ht).1
  have htm : t ∈ fruleOrd E := (frule_run_order E).1.symm.subset (List.mem_range.2 htl)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 htm
  have hlen : 0 < (fruleOrd E).length := by
    rw [(frule_run_order E).1.length_eq]; simp; omega
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, (fruleOrd E)[0]? = some t₀ := ⟨_, List.getElem?_eq_getElem hlen⟩
  have ht₀l : t₀ < E.length := List.mem_range.1 ((frule_run_order E).1.subset
    (List.mem_of_getElem? ht₀))
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, E[t₀]? = some d₀ := ⟨_, List.getElem?_eq_getElem ht₀l⟩
  refine ⟨t₀, d₀, ht₀, hd₀, ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · rw [ht₀] at hj
    obtain rfl := Option.some.inj hj
    rw [hd₀] at ht
    obtain rfl := Option.some.inj ht
    exact hr
  · have := R2T_ord_role E 0 j t₀ t hjp ht₀ hj
    rw [R2T_getD E t₀ d₀ hd₀, R2T_getD E t d ht, hr] at this
    omega

/-- The uses after the first entry are at most one per label. -/
private theorem R2T_cap1 (F : List FFac) (E : List FEnt) (hE : F.filterMap FFac.entData = E)
    (hsh : ∀ d ∈ E, 2 ≤ d.2.2.1.length →
      d.2.2.1.length = 2 ∧ (d.1 = d.2.1 → d.2.2.1.head? = some 0))
    (h0 : ∃ d ∈ E, FEnt.role d = 0) (k : ℕ) (hk : k ≤ 1) (l : ℕ) :
    (fruleCap E false k).getD l 0 ≤ 1 := by
  obtain ⟨-, hlen4, -⟩ := frule_run_mono E false k k l le_rfl
  by_cases hl : 4 ≤ l
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
  rcases Nat.lt_or_ge k 1 with hk0 | hk1
  · obtain rfl : k = 0 := by omega
    rw [(frule_run_mono E false 0 0 l le_rfl).1]
    interval_cases l <;> simp
  obtain rfl : k = 1 := by omega
  obtain ⟨t₀, d₀, ht₀, hd₀, hr₀⟩ := R2T_first E h0
  have hcap := frule_run_cap F false 1 l (by omega)
  rw [hE] at hcap
  rw [hcap]
  have htake : (fruleOrd E).take 1 = [t₀] := by
    rw [List.take_one, List.head?_eq_getElem?, ht₀]; rfl
  rw [htake]
  obtain ⟨hl2, hdi⟩ := hsh d₀ (List.mem_of_getElem? hd₀) ((R2T_role_le1 d₀).1 (by omega))
  obtain ⟨x, y, P, ext, det⟩ := d₀
  obtain ⟨p0, p1, rfl⟩ := List.length_eq_two.1 hl2
  have hh : x = y → p0 = 0 := fun h => by simpa using hdi h
  have hc0 : ∀ l, (fruleCap E false 0).getD l 0 ≤ 1 := by
    intro l
    rw [(frule_run_mono E false 0 0 l le_rfl).1]
    rcases (show l < 4 ∨ 4 ≤ l by omega) with h | h
    · interval_cases l <;> simp
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; simp
  obtain ⟨o, hfit, -, huse⟩ := R2T_fit1 x y p0 p1 ext det _ hh hc0
  obtain ⟨-, -, hch⟩ := frule_run_chosen F false 0 t₀ _ (hE ▸ ht₀) (hE ▸ hd₀) _ o (hE ▸ hfit)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hE] at hch
  rw [hch]
  exact huse l

/-- The option of every entry: one of its list for an entry without `Λ̃`, the Hilbert–Schmidt norm
or the split at `Λ̃` for an entry with one `Λ̃`. -/
private theorem R2T_class (F : List FFac) (E : List FEnt) (hE : F.filterMap FFac.entData = E)
    (hE1 : ∀ d ∈ E, 1 ≤ d.2.2.1.length)
    (hcnt : E.countP (fun d => 2 ≤ d.2.2.1.length) ≤ 2)
    (hsh : ∀ d ∈ E, 2 ≤ d.2.2.1.length →
      d.2.2.1.length = 2 ∧ (d.1 = d.2.1 → d.2.2.1.head? = some 0))
    (h0 : ∃ d ∈ E, FEnt.role d = 0) :
    ∀ c ∈ fchosen F (frule F), ∃ o, c.2 = some o ∧
      ((c.1.2.2.1.length = 1 ∧ ∃ k ∈ FEnt.prefs c.1 false, fkindOpt c.1 k = some o) ∨
        (c.1.2.2.1.length = 2 ∧
          fkindOpt c.1 (if c.1.1 = c.1.2.1 then .isoX else .hs) = some o)) := by
  intro c hc
  obtain ⟨k, t, kd, o, hk, ht, hc2, hfit, hkd, ho⟩ := R2T_chosen F c hc
  rw [hE] at hk ht hfit
  have hcE : c.1 ∈ E := List.mem_of_getElem? ht
  refine ⟨o, hc2, ?_⟩
  by_cases hl : 2 ≤ c.1.2.2.1.length
  · right
    obtain ⟨hl2, hdi⟩ := hsh c.1 hcE hl
    refine ⟨hl2, ?_⟩
    have hkl : k ≤ 1 := by
      have hkE : k < E.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1
        rwa [(frule_run_order E).1.length_eq, List.length_range] at this
      have := R2T_cnt_take E (fun d => 2 ≤ d.2.2.1.length) (k + 1) (by omega) (by
        intro j hj t' ht'
        simp only [decide_eq_true_eq]
        rcases Nat.lt_or_ge j k with hjk | hjk
        · have := R2T_ord_role E j k t' t hjk ht' hk
          rw [R2T_getD E t c.1 ht] at this
          exact (R2T_role_le1 _).1 (this.trans ((R2T_role_le1 _).2 hl))
        · obtain rfl : j = k := by omega
          rw [ht'] at hk
          obtain rfl := Option.some.inj hk
          rw [R2T_getD E t' c.1 ht]
          exact hl)
      omega
    have hcap := R2T_cap1 F E hE hsh h0 k hkl
    obtain ⟨⟨x, y, P, ext, det⟩, c2⟩ := c
    simp only at hl2 hdi hfit ⊢
    obtain ⟨p0, p1, rfl⟩ := List.length_eq_two.1 hl2
    have hh : x = y → p0 = 0 := fun h => by simpa using hdi h
    obtain ⟨o', hfit', ho', -⟩ := R2T_fit1 x y p0 p1 ext det _ hh hcap
    rw [hfit] at hfit'
    simp only [Option.some.injEq, Prod.mk.injEq] at hfit'
    rw [hfit'.2]
    exact ho'
  · left
    exact ⟨by have := hE1 c.1 hcE; omega, kd, hkd, ho⟩

/-- When one entry has a letter `Λ̃`, with role `0`, and some entry has role `2`, the entry treated
second has role `2` and takes its Ward row or column. -/
private theorem R2T_ward (F : List FFac) (E : List FEnt) (hE : F.filterMap FFac.entData = E)
    (hE1 : ∀ d ∈ E, 1 ≤ d.2.2.1.length)
    (hcnt : E.countP (fun d => 2 ≤ d.2.2.1.length) ≤ 1)
    (hsh : ∀ d ∈ E, 2 ≤ d.2.2.1.length →
      d.2.2.1.length = 2 ∧ (d.1 = d.2.1 → d.2.2.1.head? = some 0))
    (h0 : ∃ d ∈ E, FEnt.role d = 0) (h2 : ∃ d ∈ E, FEnt.role d = 2) :
    ∃ c ∈ fchosen F (frule F), c.1.2.2.1.length = 1 ∧ R2T_uc c = 1 := by
  obtain ⟨t₀, d₀, ht₀, hd₀, hr₀⟩ := R2T_first E h0
  obtain ⟨d₂, hd₂, hr₂⟩ := h2
  obtain ⟨t₂, ht₂⟩ := List.mem_iff_getElem?.1 hd₂
  have ht₂l := (List.getElem?_eq_some_iff.1 ht₂).1
  have hperm := (frule_run_order E).1
  obtain ⟨j₂, hj₂⟩ := List.mem_iff_getElem?.1 (hperm.symm.subset (List.mem_range.2 ht₂l))
  have hj₂0 : j₂ ≠ 0 := by
    rintro rfl
    rw [ht₀] at hj₂
    obtain rfl := Option.some.inj hj₂
    rw [hd₀] at ht₂
    obtain rfl := Option.some.inj ht₂
    omega
  have hlen : 1 < (fruleOrd E).length := by
    have := (List.getElem?_eq_some_iff.1 hj₂).1; omega
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, (fruleOrd E)[1]? = some t₁ := ⟨_, List.getElem?_eq_getElem hlen⟩
  have ht₁l : t₁ < E.length := List.mem_range.1 (hperm.subset (List.mem_of_getElem? ht₁))
  obtain ⟨d₁, hd₁⟩ : ∃ d₁, E[t₁]? = some d₁ := ⟨_, List.getElem?_eq_getElem ht₁l⟩
  have hle2 : FEnt.role d₁ ≤ 2 := by
    rcases Nat.lt_or_ge 1 j₂ with h | h
    · have := R2T_ord_role E 1 j₂ t₁ t₂ h ht₁ hj₂
      rwa [R2T_getD E t₁ d₁ hd₁, R2T_getD E t₂ d₂ ht₂, hr₂] at this
    · obtain rfl : j₂ = 1 := by omega
      rw [ht₁] at hj₂
      obtain rfl := Option.some.inj hj₂
      rw [hd₁] at ht₂
      obtain rfl := Option.some.inj ht₂
      omega
  have hge2 : 2 ≤ FEnt.role d₁ := by
    by_contra hlt
    have hoE : (fruleOrd E).length = E.length := by rw [hperm.length_eq, List.length_range]
    have := R2T_cnt_take E (fun d => 2 ≤ d.2.2.1.length) 2 (by omega) (by
      intro j hj t' ht'
      simp only [decide_eq_true_eq]
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [ht₀] at ht'
        obtain rfl := Option.some.inj ht'
        rw [R2T_getD E _ d₀ hd₀]
        exact (R2T_role_le1 _).1 (by omega)
      · rw [ht₁] at ht'
        obtain rfl := Option.some.inj ht'
        rw [R2T_getD E _ d₁ hd₁]
        exact (R2T_role_le1 _).1 (by omega))
    omega
  obtain ⟨hl1, hs1, hin⟩ := R2T_role2 d₁ (by omega)
  have hcap := R2T_cap1 F E hE hsh h0 1 le_rfl
  have hl1' : d₁.2.2.1.length = 1 := by have := hE1 d₁ (List.mem_of_getElem? hd₁); omega
  obtain ⟨x, y, P, ext, det⟩ := d₁
  simp only at hl1' hs1 hin
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.1 hl1'
  obtain ⟨kd, o, hfit, hu⟩ := R2T_fitW x y r ext det _ hin hcap
  obtain ⟨-, -, hch⟩ := frule_run_chosen F false 1 t₁ _ (hE ▸ ht₁) (hE ▸ hd₁) kd o (hE ▸ hfit)
  exact ⟨_, List.mem_of_getElem? hch, rfl, hu⟩

/-! ### The integer test -/

open private FR_ok_iff from RBMTransitionEdge.Localized.Expansion.FRule

/-- The integer test of `FMono.ok` from five linear inequalities. -/
private theorem R2T_okI (M : FMono) (hi : 0 ≤ M.i) (hdo : 2 ≤ M.d + M.o)
    (e1 : 6 * M.a - 2 * M.i + 4 * M.l + 20 + 4 * ((M.d - 2 : ℕ) : ℤ) ≤ 0)
    (e2 : 18 * M.a - 3 * M.i + 6 * M.l + 36 + 6 * ((M.d - 2 : ℕ) : ℤ) ≤ 0)
    (m1 : 6 * M.a + 6 * M.l + 12 ≤ 0) (m2 : 18 * M.a + 9 * M.l + 24 ≤ 0)
    (b2 : 18 * M.a + 12 * M.l + 3 * M.i + 12 - 6 * ((M.d : ℤ) + M.o - 2) ≤ 0) :
    M.ok = true := by
  rw [FR_ok_iff]
  refine ⟨hi, hdo, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-! ### Counting the factors -/

open private FW_one FW_g FW_rfacs FW_sum_one FW_wf_free FW_wf_ent FW_mk
  from RBMTransitionEdge.Localized.Expansion.FEntWords
open private FF_ffacs FF_wf from RBMTransitionEdge.Localized.Expansion.FFactor
open private charsP_eq from RBMTransitionEdge.Localized.Expansion.PkgWords

/-- `1` for a light weight, `0` otherwise. -/
private def R2T_isWt (f : FFac) : ℕ :=
  match f with
  | .wt _ _ => 1
  | _ => 0

private theorem R2T_un_sum (F : List FFac) : (F.map R2T_un).sum =
    ((fLoops F).map fun w => (fresN w : ℤ)).sum + ((F.map R2T_isWt).sum : ℤ) := by
  induction F with
  | nil => simp [fLoops]
  | cons f F ih =>
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
      simp [fLoops, R2T_un, R2T_isWt] at ih ⊢ <;> rw [ih] <;> push_cast <;> ring

private theorem R2T_sh_sum (F : List FFac) : (F.map R2T_sh).sum =
    2 * ((fLoops F).map fun w => (fresN w : ℤ) - 1).sum := by
  induction F with
  | nil => simp [fLoops]
  | cons f F ih =>
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
      simp [fLoops, R2T_sh] at ih ⊢ <;> rw [ih] <;> ring

private theorem R2T_one_sum (F : List FFac) : (F.map FW_one).sum =
    (F.filterMap FFac.entData).length + (fLoops F).length := by
  induction F with
  | nil => simp [fLoops]
  | cons f F ih =>
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
      simp [fLoops, FW_one, FFac.entData, List.filterMap_cons] at ih ⊢ <;> omega

private theorem R2T_g_kind (X : PkgExpr) (f : FFac) :
    FW_one (FW_g X f) = FW_one f ∧ R2T_isWt (FW_g X f) = R2T_isWt f := by
  unfold FW_g
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> split_ifs <;> simp [FW_one, R2T_isWt, FFac.dupRes]

/-- The number of factors `n` is the number of entries and loops, and the light weights are the
factors `.wt`. -/
private theorem R2T_nfac (X : PkgExpr) :
    X.charsP.2.1 = ((X.rfacs.filterMap FFac.entData).length + (fLoops X.rfacs).length : ℕ) ∧
      (X.rfacs.map R2T_isWt).sum = X.weights.length := by
  constructor
  · rw [charsP_eq]
    simp only
    rw [← FW_sum_one, ← R2T_one_sum, FW_rfacs, List.map_map]
    congr 2
    exact List.map_congr_left fun f _ => ((R2T_g_kind X f).1).symm
  · rw [FW_rfacs, List.map_map, FF_ffacs, List.map_append, List.sum_append]
    have h1 : (X.weights.map fun p => FFac.wt p.1 p.2).map (R2T_isWt ∘ FW_g X) =
        X.weights.map fun _ => 1 := by
      simp only [List.map_map]
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp]
      rw [(R2T_g_kind X _).2]
      rfl
    have h2 : ((X.loops.flatMap (FF_wf (fun _ => false) X.fpm)).map (R2T_isWt ∘ FW_g X)).sum
        = 0 := by
      rw [List.sum_eq_zero_iff]
      intro n hn
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hn
      obtain ⟨w, -, hfw⟩ := List.mem_flatMap.1 hf
      simp only [Function.comp, (R2T_g_kind X f).2]
      cases hw : w.any PkgLetter.isEnt
      · rw [FW_wf_free _ w hw, List.mem_singleton] at hfw
        subst hfw; rfl
      · rw [FW_wf_ent _ w hw] at hfw
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hfw
        rfl
    rw [h1, h2]
    simp

/-! ### The two companion cases -/

open private RH_side12 RH_seek RH_uniq RH_some_loop RH_ent_loop
  from RBMTransitionEdge.Localized.Expansion.RemHalves
open private FW_lamSide_mem FW_wf_count FW_findIdx_mem FW_wside
  from RBMTransitionEdge.Localized.Expansion.FEntWords

/-- When the loop of `Λ̃₂` has no `Δ` and no resolvent to the left of `Λ̃₂`, the rules choose the
right side of `Λ̃₁`, if any. -/
private theorem R2T_side0 (R : PkgExpr) (hR : R.wf = true) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : PkgLetter.lw (.lamt 1) ∈ w) (hE : w.any PkgLetter.isEnt = false)
    (hseek : pkgSeek w (w.idxOf (.lw (.lamt 1))) false = none) :
    R.ffocusSide = none ∨ R.ffocusSide = some (0, true) := by
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
  unfold PkgExpr.ffocusSide
  simp only [h₂, h₁]
  have hE' : ¬ (w.any PkgLetter.isEnt = true) := by rw [hE]; simp
  rw [ite_eq_right (by exact hE'), hseek]
  dsimp only
  split <;> simp

/-- The two companion cases of Type II: the loop `w₂` of `Λ̃₂` (no `Δ`, no `Λ̃₁`), and the side
chosen by the rules: left of `Λ̃₂` when `w₂` has a resolvent (case (5)), right of `Λ̃₁` when it
has none (case (6)). -/
private theorem R2T_cases (R : PkgExpr) (hR : R.wf = true) (hty : R.ptype = 2)
    (hlam1 : ∃ w ∈ R.loops, w.any PkgLetter.isEnt = true ∧ PkgLetter.lw (.lamt 0) ∈ w)
    (hf : R.ffocus.isSome = true) :
    ∃ w₂ ∈ R.loops, PkgLetter.lw (.lamt 1) ∈ w₂ ∧ w₂.any PkgLetter.isEnt = false ∧
      PkgLetter.lw (.lamt 0) ∉ w₂ ∧ (∀ s, R.lamSide 1 s = w₂.countP PkgLetter.isRes) ∧
      ((R.ffocusSide = some (1, false) ∧ 1 ≤ w₂.countP PkgLetter.isRes) ∨
        (R.ffocusSide = some (0, true) ∧ w₂.countP PkgLetter.isRes = 0)) := by
  unfold PkgExpr.ptype at hty
  cases hfind : R.loops.find? (fun w => w.contains (.lw (.lamt 1))) with
  | none => rw [hfind] at hty; simp at hty
  | some w₂ =>
    rw [hfind] at hty
    have hfree : w₂.any PkgLetter.isEnt = false := by
      dsimp only at hty
      split_ifs at hty with hc1
      · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc1
        rw [List.any_eq_false] at hc1 ⊢
        intro x hx
        have := hc1 x hx
        rcases x with _ | ⟨u, v⟩
        · simp [PkgLetter.isEnt]
        · simp at this
      all_goals omega
    have hw : w₂ ∈ R.loops := List.mem_of_find?_eq_some hfind
    have hmem : PkgLetter.lw (.lamt 1) ∈ w₂ := by
      have := List.find?_some hfind
      simpa using this
    have h0 : PkgLetter.lw (.lamt 0) ∉ w₂ := by
      intro h0
      obtain ⟨w, hwL, hwE, hw0⟩ := hlam1
      have := RH_uniq R hR 0 w w₂ hwL hw hw0 h0
      subst this
      rw [hwE] at hfree
      exact Bool.noConfusion hfree
    have hside : ∀ s, R.lamSide 1 s = w₂.countP PkgLetter.isRes := fun s =>
      pkg_lamSide_free R hR 1 w₂ hw (by simpa using hmem) hfree (by simpa using h0) s
    refine ⟨w₂, hw, hmem, hfree, h0, hside, ?_⟩
    cases hs : (pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false).isSome
    · have hn : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false = none := by
        simpa using hs
      have hz : R.lamSide 1 false = 0 := by
        rw [FW_lamSide_mem R 1 false (FW_wf_count R hR 1).le w₂ hw hmem]
        exact (RH_seek w₂ 1 false).2 hn
      right
      refine ⟨?_, by rw [← hside false, hz]⟩
      have hsome : R.ffocusSide.isSome = true := by rw [(pkg_ffocusSide R).1]; exact hf
      rcases R2T_side0 R hR w₂ hw hmem hfree hn with h | h
      · rw [h] at hsome; simp at hsome
      · exact h
    · have h1 := RH_side12 R hR w₂ hw hmem hfree hs
      left
      refine ⟨h1, ?_⟩
      rw [← hside false]
      exact pkg_ffocusSide_pos R hR 1 false h1

/-! ### The monomials of the bound -/

/-- The uses of label `l` by an entry with its option, as in `fuses`. -/
private def R2T_t (c : FEnt × Option FOpt) (l : ℕ) : ℕ :=
  match c.2 with
  | some o => (if c.1.1 = l then o.cx else 0) + (if c.1.2.1 = l ∧ c.1.1 ≠ l then o.cy else 0)
  | none => 0

private theorem R2T_t_sum (c : FEnt × Option FOpt) (hx : c.1.1 < 4) (hy : c.1.2.1 < 4) :
    R2T_t c 0 + R2T_t c 1 + R2T_t c 2 + R2T_t c 3 = R2T_uc c := by
  obtain ⟨⟨x, y, P, ext, det⟩, oc⟩ := c
  cases oc with
  | none => rfl
  | some o =>
    simp only [R2T_t, R2T_uc] at hx hy ⊢
    split_ifs <;> omega

private theorem R2T_lab (F : List FFac)
    (hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4) :
    ((List.range 4).map fun l => 2 - (fuses F (frule F) l : ℤ)).sum =
      8 - (((fchosen F (frule F)).map R2T_uc).sum : ℤ) := by
  have hC : ∀ c ∈ fchosen F (frule F), c.1.1 < 4 ∧ c.1.2.1 < 4 := by
    intro c hc
    apply hlab
    rw [← R2T_fchosen_fst F (frule F)]
    exact List.mem_map_of_mem hc
  have hf : ∀ l, fuses F (frule F) l = ((fchosen F (frule F)).map fun c => R2T_t c l).sum :=
    fun l => rfl
  have h4 : ((fchosen F (frule F)).map R2T_uc).sum = ((fchosen F (frule F)).map fun c =>
      R2T_t c 0 + R2T_t c 1 + R2T_t c 2 + R2T_t c 3).sum := by
    congr 1
    exact List.map_congr_left fun c hc => (R2T_t_sum c (hC c hc).1 (hC c hc).2).symm
  simp only [List.sum_map_add] at h4
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.nil_append, List.cons_append, add_zero, hf]
  omega

private theorem R2T_zfst {β : Type*} (C : List (FEnt × Option FOpt)) (qs : List β)
    (hl : C.length = qs.length) (f : FEnt × Option FOpt → ℤ) :
    ((C.zip qs).map fun z => f z.1).sum = (C.map f).sum := by
  show ((C.zip qs).map (f ∘ Prod.fst)).sum = _
  rw [← List.map_map, List.map_fst_zip (by omega)]

private theorem R2T_zsnd {α : Type*} (C : List α) (qs : List FMono)
    (hl : C.length = qs.length) (f : FMono → ℤ) :
    ((C.zip qs).map fun z => f z.2).sum = (qs.map f).sum := by
  show ((C.zip qs).map (f ∘ Prod.snd)).sum = _
  rw [← List.map_map, List.map_snd_zip (by omega)]

private theorem R2T_gsum (Z : List ((FEnt × Option FOpt) × FMono)) :
    (Z.map R2T_al).sum = (Z.map fun z => z.2.a).sum - (Z.map fun z => (R2T_uc z.1 : ℤ)).sum -
      2 * (Z.map fun z => R2T_r z.1).sum ∧
    (Z.map R2T_g1).sum = 6 * (Z.map R2T_al).sum - 2 * (Z.map fun z => z.2.i).sum +
      4 * (Z.map fun z => z.2.l).sum + 4 * (Z.map fun z => R2T_r z.1).sum +
      2 * (Z.map fun z => R2T_e z.1).sum ∧
    (Z.map R2T_g2).sum = 18 * (Z.map R2T_al).sum - 3 * (Z.map fun z => z.2.i).sum +
      6 * (Z.map fun z => z.2.l).sum + 15 * (Z.map fun z => R2T_r z.1).sum +
      3 * (Z.map fun z => R2T_e z.1).sum ∧
    (Z.map R2T_g3).sum = 18 * (Z.map R2T_al).sum + 12 * (Z.map fun z => z.2.l).sum +
      3 * (Z.map fun z => z.2.i).sum - 3 * (Z.map fun z => R2T_e z.1).sum ∧
    (Z.map R2T_g4).sum = 6 * (Z.map R2T_al).sum + 6 * (Z.map fun z => z.2.l).sum ∧
    (Z.map R2T_g5).sum = 18 * (Z.map R2T_al).sum + 9 * (Z.map fun z => z.2.l).sum +
      9 * (Z.map fun z => R2T_r z.1).sum := by
  induction Z with
  | nil => simp
  | cons z Z ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih
    simp only [R2T_g1, R2T_g2, R2T_g3, R2T_g4, R2T_g5, R2T_al] at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem R2T_hsum (F : List FFac) :
    (F.map R2T_be).sum = ((F.map FFac.fixV).map FMono.a).sum - (F.map R2T_sh).sum ∧
    (F.map R2T_h1).sum = 6 * (F.map R2T_be).sum - 2 * ((F.map FFac.fixV).map FMono.i).sum +
      4 * ((F.map FFac.fixV).map FMono.l).sum + 4 * (F.map R2T_un).sum ∧
    (F.map R2T_h2).sum = 18 * (F.map R2T_be).sum - 3 * ((F.map FFac.fixV).map FMono.i).sum +
      6 * ((F.map FFac.fixV).map FMono.l).sum + 15 * (F.map R2T_un).sum ∧
    (F.map R2T_h3).sum = 18 * (F.map R2T_be).sum + 12 * ((F.map FFac.fixV).map FMono.l).sum +
      3 * ((F.map FFac.fixV).map FMono.i).sum ∧
    (F.map R2T_h4).sum = 6 * (F.map R2T_be).sum + 6 * ((F.map FFac.fixV).map FMono.l).sum ∧
    (F.map R2T_h5).sum = 18 * (F.map R2T_be).sum + 9 * ((F.map FFac.fixV).map FMono.l).sum +
      9 * (F.map R2T_un).sum := by
  induction F with
  | nil => simp
  | cons f F ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih
    simp only [R2T_h1, R2T_h2, R2T_h3, R2T_h4, R2T_h5, R2T_be] at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem R2T_Cfst (F : List FFac) (f : FEnt → ℤ) :
    ((fchosen F (frule F)).map fun c => f c.1).sum = ((F.filterMap FFac.entData).map f).sum := by
  rw [← R2T_fchosen_fst F (frule F), List.map_map]
  rfl

/-- The integer test for one monomial of the bound, from upper bounds on the five sums over the
entries and on the five sums over the loops and light weights. -/
private theorem R2T_final (F : List FFac) (qs : List FMono)
    (hF2 : List.Forall₂ (fun c q => ∃ o, c.2 = some o ∧ q ∈ o.val) (fchosen F (frule F)) qs)
    (hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4)
    (s fR fsig π S' ZE : ℤ)
    (hS : S' = fR + ((F.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum +
      ((fLoops F).map fun w => (fresN w : ℤ) - 1).sum - π)
    (hU : ((F.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum +
      ((fLoops F).map fun w => (fresN w : ℤ)).sum + ((F.map R2T_isWt).sum : ℤ) = fsig - fR + π)
    (hZE : ((F.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum = ZE)
    (G1 G2 G3 G4 G5 H1 H2 H3 H4 H5 : ℤ) (D : ℕ)
    (hG1 : (((fchosen F (frule F)).zip qs).map R2T_g1).sum ≤ G1)
    (hG2 : (((fchosen F (frule F)).zip qs).map R2T_g2).sum ≤ G2)
    (hG3 : (((fchosen F (frule F)).zip qs).map R2T_g3).sum ≤ G3)
    (hG4 : (((fchosen F (frule F)).zip qs).map R2T_g4).sum ≤ G4)
    (hG5 : (((fchosen F (frule F)).zip qs).map R2T_g5).sum ≤ G5)
    (hH1 : (F.map R2T_h1).sum ≤ H1) (hH2 : (F.map R2T_h2).sum ≤ H2)
    (hH3 : (F.map R2T_h3).sum ≤ H3) (hH4 : (F.map R2T_h4).sum ≤ H4)
    (hH5 : (F.map R2T_h5).sum ≤ H5)
    (hD : (qs.map FMono.d).sum + ((F.map FFac.fixV).map FMono.d).sum = D)
    (hO : (qs.map FMono.o).sum + ((F.map FFac.fixV).map FMono.o).sum = 0)
    (hI : 0 ≤ (qs.map FMono.i).sum + ((F.map FFac.fixV).map FMono.i).sum) (hD2 : 2 ≤ D)
    (c1 : 32 - 6 * s - 12 * fR + 4 * π - 4 * (fsig - fR + π) - 2 * ZE + G1 + H1 +
      4 * ((D - 2 : ℕ) : ℤ) ≤ 0)
    (c2 : 72 - 18 * s - 36 * fR + 24 * π - 15 * (fsig - fR + π) - 3 * ZE + G2 + H2 +
      6 * ((D - 2 : ℕ) : ℤ) ≤ 0)
    (c3 : 48 - 18 * s - 36 * fR + 12 * π + 3 * ZE + G3 + H3 - 6 * ((D : ℤ) - 2) ≤ 0)
    (c4 : 24 - 6 * s - 12 * fR + G4 + H4 ≤ 0)
    (c5 : 60 - 18 * s - 36 * fR + 18 * π - 9 * (fsig - fR + π) + G5 + H5 ≤ 0)
    (m : FMono)
    (hm : m = ((⟨((List.range 4).map fun l => 2 - (fuses F (frule F) l : ℤ)).sum, 0, 0, 0, 0⟩ :
      FMono).mul (FMono.prodL (F.map FFac.fixV))).mul (FMono.prodL qs)) :
    ((m.mul ⟨-s - 6 - 2 * S', 0, 0, 0, 0⟩).mul ⟨0, 0, -2 * π, 0, 0⟩).ok = true := by
  have hl := hF2.length_eq
  obtain ⟨Z, hZ⟩ : ∃ Z : List ((FEnt × Option FOpt) × FMono),
      Z = (fchosen F (frule F)).zip qs := ⟨_, rfl⟩
  rw [← hZ] at hG1 hG2 hG3 hG4 hG5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := R2T_gsum Z
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ := R2T_hsum F
  have zu : (Z.map fun z => (R2T_uc z.1 : ℤ)).sum =
      (((fchosen F (frule F)).map R2T_uc).sum : ℤ) := by
    subst hZ
    rw [R2T_zfst _ qs hl (fun c => (R2T_uc c : ℤ)), Nat.cast_list_sum, List.map_map]; rfl
  have zr : (Z.map fun z => R2T_r z.1).sum =
      ((F.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum := by
    subst hZ
    rw [R2T_zfst _ qs hl R2T_r]; exact R2T_Cfst F fun d => (d.2.2.1.sum : ℤ) - 1
  have ze : (Z.map fun z => R2T_e z.1).sum = ZE := by
    subst hZ
    rw [R2T_zfst _ qs hl R2T_e, ← hZE]; exact R2T_Cfst F fun d => d.2.2.2.1.i
  have za : (Z.map fun z => z.2.a).sum = (qs.map FMono.a).sum := by
    subst hZ; exact R2T_zsnd _ qs hl FMono.a
  have zi : (Z.map fun z => z.2.i).sum = (qs.map FMono.i).sum := by
    subst hZ; exact R2T_zsnd _ qs hl FMono.i
  have zl : (Z.map fun z => z.2.l).sum = (qs.map FMono.l).sum := by
    subst hZ; exact R2T_zsnd _ qs hl FMono.l
  have hlab' := R2T_lab F hlab
  have hsh := R2T_sh_sum F
  have hun := R2T_un_sum F
  subst hm
  apply R2T_okI
  all_goals simp only [FMono.mul, R2T_prodL, add_zero]
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-! ### One entry with its option -/

/-- The bounds on the functionals of one entry with its option and one monomial of it. -/
private theorem R2T_zgen (d : FEnt) (o : FOpt) (q : FMono) (hq : q ∈ o.val)
    (hx : d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧ d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧
      0 ≤ d.2.2.2.1.i)
    (hc : (d.2.2.1.length = 1 ∧ 1 ≤ d.2.2.1.sum ∧ ∃ k ∈ FEnt.prefs d false, fkindOpt d k = some o) ∨
      (d.2.2.1.length = 2 ∧ d.2.2.1.head? = some 0 ∧
        fkindOpt d (if d.1 = d.2.1 then .isoX else .hs) = some o ∧
        (1 ≤ d.2.2.1.sum ∨ d.1 ≠ d.2.1))) :
    q.d = d.2.2.1.length - 1 ∧ q.o = 0 ∧ 0 ≤ q.i ∧ R2T_g1 ((d, some o), q) ≤ 0 ∧
      R2T_g2 ((d, some o), q) ≤ 0 ∧ R2T_g3 ((d, some o), q) ≤ 0 ∧
      R2T_g4 ((d, some o), q) ≤ 0 ∧ R2T_g5 ((d, some o), q) ≤ 0 ∧
      (d.2.2.1.length = 1 → (R2T_uc (d, some o) = 1 ∨ 2 ≤ d.2.2.1.sum) →
        R2T_g1 ((d, some o), q) ≤ -4) ∧
      (d.2.2.1.length = 2 → R2T_g1 ((d, some o), q) ≤ -4 ∧ R2T_g2 ((d, some o), q) ≤ -15) ∧
      (d.2.2.1.length = 2 → 1 ≤ d.2.2.1.sum → R2T_g1 ((d, some o), q) ≤ -6 ∧
        R2T_g2 ((d, some o), q) ≤ -18 ∧ R2T_g3 ((d, some o), q) ≤ -18 ∧
        R2T_g4 ((d, some o), q) ≤ -6 ∧ R2T_g5 ((d, some o), q) ≤ -18) ∧
      (d.2.2.1.length = 2 → 2 ≤ d.2.2.1.sum → R2T_g1 ((d, some o), q) ≤ -10) := by
  obtain ⟨x, y, P, ⟨ea, ei, el, ed, eo⟩, det⟩ := d
  simp only at hx hc ⊢
  obtain ⟨rfl, rfl, rfl, rfl, he⟩ := hx
  rcases hc with ⟨hl, hr, k, hk, ho⟩ | ⟨hl, hh, ho, hr⟩
  · obtain ⟨r, rfl⟩ := List.length_eq_one_iff.1 hl
    simp only [List.sum_cons, List.sum_nil, add_zero] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := R2T_ent0 x y r ei det k o q hk ho hq he hr
    simp only [List.length_singleton, List.sum_cons, List.sum_nil, add_zero]
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun _ => h9, by omega, by omega, by omega⟩
  · obtain ⟨p0, p1, rfl⟩ := List.length_eq_two.1 hl
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [List.sum_cons, List.sum_nil, add_zero, zero_add] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      R2T_ent1 x y p1 ei det o q ho hq he hr
    simp only [List.length_cons, List.length_singleton, List.sum_cons, List.sum_nil, add_zero,
      zero_add]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by omega, fun _ => h9, fun _ => h10, fun _ => h11⟩

/-! ### Facts on the factors of an expression -/

open private RH_ent from RBMTransitionEdge.Localized.Expansion.RemHalves

private theorem R2T_pent_ent (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) :
    ∃ d, (X.rent e).entData = some d ∧ d ∈ X.rfacs.filterMap FFac.entData := by
  obtain ⟨d, hd⟩ := RH_ent X e
  refine ⟨d, hd, List.mem_filterMap.2 ⟨X.rent e, ?_, hd⟩⟩
  have : X.rent e ∈ X.rfacs.filter fun f => f.entData.isSome := by
    rw [pkg_rfacs_pents]; exact List.mem_map_of_mem he
  exact (List.mem_filter.1 this).1

private theorem R2T_parts_two (σ : List PkgLetter) (o : Fin 2) (h : PkgLetter.lw (.lamt o) ∈ σ) :
    2 ≤ (pkgParts σ).length := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem h
  unfold pkgParts
  rw [List.splitOnP_append_cons A B (by rfl), List.map_append, List.length_append,
    List.length_map, List.length_map]
  have h1 := List.length_pos_iff.2 (List.splitOnP_ne_nil PkgLetter.isLam A)
  have h2 := List.length_pos_iff.2 (List.splitOnP_ne_nil PkgLetter.isLam B)
  omega

private theorem R2T_E_len (F : List FFac) : ∀ d ∈ F.filterMap FFac.entData, 1 ≤ d.2.2.1.length := by
  intro d hd
  obtain ⟨f, -, hf⟩ := List.mem_filterMap.1 hd
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp [FFac.entData] at hf
  subst hf
  simp only [FLet.parts, List.length_map]
  exact List.length_pos_iff.2 (List.splitOnP_ne_nil _ _)

private theorem R2T_lab4 (F : List FFac) (nb : ℕ) (h : fLocal nb F = true) :
    ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4 := by
  intro d hd
  obtain ⟨f, hfF, hf⟩ := List.mem_filterMap.1 hd
  have := List.all_eq_true.1 h f hfF
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp [FFac.entData] at hf
  subst hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2⟩

private theorem R2T_rext (X : PkgExpr) : X.rext = ⟨0, 0, -2 * (X.fpi : ℤ), 0, 0⟩ := by
  unfold PkgExpr.rext PkgExpr.fpi
  split_ifs <;> simp

private theorem R2T_cnt_le (E : List FEnt) :
    E.countP (fun d => 2 ≤ d.2.2.1.length) ≤ (E.map fun d => d.2.2.1.length - 1).sum := by
  induction E with
  | nil => simp
  | cons d E ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    split_ifs with h <;> simp_all <;> omega

private theorem R2T_sub_one (L : List (List FLet)) :
    (L.map fun w => (fresN w : ℤ)).sum = (L.map fun w => (fresN w : ℤ) - 1).sum + L.length := by
  induction L with
  | nil => simp
  | cons w L ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

/-- The number of inner labels of an entry. -/
private def R2T_inn (d : FEnt) : ℕ := (if 2 ≤ d.1 then 1 else 0) + (if 2 ≤ d.2.1 then 1 else 0)

private theorem R2T_par_sum (E : List FEnt)
    (h : ∀ d ∈ E, R2T_inn d % 2 = if 2 ≤ d.2.2.1.length then 1 else 0) :
    (E.map R2T_inn).sum % 2 = E.countP (fun d => 2 ≤ d.2.2.1.length) % 2 := by
  induction E with
  | nil => simp
  | cons d E ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    have h1 := h d (by simp)
    have h2 := ih fun d hd => h d (by simp [hd])
    split_ifs at h1 ⊢ <;> simp_all <;> omega

/-- Among the entries of the remainder terms of case (6), some entry has role `2`: the inner labels
`i, j` occur an even number of times, and the entry with `Λ̃` has exactly one. -/
private theorem R2T_parity (E : List FEnt) (s : ℕ) (hlab : ∀ d ∈ E, d.1 < 4 ∧ d.2.1 < 4)
    (hends : ∀ l : ℕ, l < 4 → (E.flatMap fun d => [d.1, d.2.1]).count l =
      if l < 2 then 3 else 1 + s)
    (hE1 : ∀ d ∈ E, 1 ≤ d.2.2.1.length) (hsum : ∀ d ∈ E, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum)
    (hcnt : E.countP (fun d => 2 ≤ d.2.2.1.length) = 1)
    (hP : ∀ d ∈ E, 2 ≤ d.2.2.1.length → (2 ≤ d.1 ∧ d.2.1 < 2) ∨ (d.1 < 2 ∧ 2 ≤ d.2.1)) :
    ∃ d ∈ E, FEnt.role d = 2 := by
  by_contra hno
  push Not at hno
  have h23 : (E.map R2T_inn).sum = 2 + 2 * s := by
    have e2 := hends 2 (by omega)
    have e3 := hends 3 (by omega)
    simp only [List.count_flatMap] at e2 e3
    have : (E.map R2T_inn).sum = (E.map fun d => [d.1, d.2.1].count 2).sum +
        (E.map fun d => [d.1, d.2.1].count 3).sum := by
      rw [← List.sum_map_add]
      congr 1
      refine List.map_congr_left fun d hd => ?_
      obtain ⟨hx, hy⟩ := hlab d hd
      simp only [R2T_inn, List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    rw [this]
    simp only [Function.comp_def] at e2 e3
    simp at e2 e3
    omega
  have hp := R2T_par_sum E (fun d hd => by
    split_ifs with hl
    · rcases hP d hd hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [R2T_inn] <;> split_ifs <;> omega
    · have hl1 : d.2.2.1.length = 1 := by have := hE1 d hd; omega
      have hr := hsum d hd hl1
      have hn := hno d hd
      unfold FEnt.role at hn
      simp only [show ¬ 2 ≤ d.2.2.1.length by omega, ↓reduceIte] at hn
      split_ifs at hn with h3
      · exact absurd rfl hn
      · simp only [fInnerL, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
          not_and, not_not] at h3
        have := h3 hr
        simp only [R2T_inn]
        by_cases hx : 2 ≤ d.1 <;> by_cases hy : 2 ≤ d.2.1 <;>
          simp only [hx, hy, decide_true, decide_false, ↓reduceIte] at this ⊢ <;>
          first | rfl | exact absurd this (by decide))
  rw [hcnt, h23] at hp
  omega

private theorem R2T_sumN_zero {α : Type*} (L : List α) (f : α → ℕ) (h : ∀ x ∈ L, f x = 0) :
    (L.map f).sum = 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, h x (by simp), ih fun y hy => h y (by simp [hy])]

private theorem R2T_sumZ_nonneg {α : Type*} (L : List α) (f : α → ℤ) (h : ∀ x ∈ L, 0 ≤ f x) :
    0 ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    omega

/-! ### The counts of a derivative structure -/

private theorem R2T_qs_mem {α : Type*} (C : List α) (qs : List FMono) (hl : C.length = qs.length) :
    ∀ q ∈ qs, ∃ z ∈ C.zip qs, z.2 = q := by
  intro q hq
  rw [← List.map_snd_zip (l₁ := C) (l₂ := qs) (by omega)] at hq
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
  exact ⟨z, hz, rfl⟩

private theorem R2T_qs_sumN (C : List (FEnt × Option FOpt)) (qs : List FMono)
    (hl : C.length = qs.length) (f : FMono → ℕ) (g : FEnt → ℕ)
    (h : ∀ z ∈ C.zip qs, f z.2 = g z.1.1) : (qs.map f).sum = ((C.map Prod.fst).map g).sum := by
  rw [← List.map_snd_zip (l₁ := C) (l₂ := qs) (by omega), List.map_map]
  conv_rhs => rw [← List.map_fst_zip (l₁ := C) (l₂ := qs) (by omega), List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun z hz => h z hz

private theorem R2T_S (X : PkgExpr) (k : ℤ) (h : X.fR = k + 1) :
    X.S = k + ((X.rfacs.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum +
      ((fLoops X.rfacs).map fun w => (fresN w : ℤ) - 1).sum - X.fpi := by
  have hres := pkg_rfacs_res X
  unfold PkgExpr.fR at h
  have hc : X.charsP.2.2.2 = X.S := rfl
  rcases hX : X.charsP with ⟨m, n, u, S⟩
  rw [hX] at h hres hc
  simp only at h hres hc
  omega

private theorem R2T_U (R X : PkgExpr) (s : ℕ) (hmu : X.charsP.1 + X.charsP.2.2.1 =
      R.charsP.1 + R.charsP.2.2.1 + (s : ℤ))
    (hn : (X.rfacs.filterMap FFac.entData).length = 4 + s) :
    ((X.rfacs.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum +
      ((fLoops X.rfacs).map fun w => (fresN w : ℤ)).sum + ((X.rfacs.map R2T_isWt).sum : ℤ) =
      R.fsig - R.fR + X.fpi := by
  have hres := pkg_rfacs_res X
  obtain ⟨hn', hw⟩ := R2T_nfac X
  have hsub := R2T_sub_one (fLoops X.rfacs)
  have hu : X.charsP.2.2.1 = X.weights.length := rfl
  unfold PkgExpr.fsig
  rw [hw]
  rcases hR : R.charsP with ⟨m, n, u, S⟩
  rw [hR] at hmu
  simp only at hmu ⊢
  rw [hn] at hn'
  have hl : ((fLoops X.rfacs).length : ℤ) = ((fLoops X.rfacs).length : ℕ) := rfl
  omega

/-! ### Facts common to the two cases -/

/-- The bundle of the facts on the entries used by both cases. -/
private theorem R2T_zall (F : List FFac) (qs : List FMono)
    (hF2 : List.Forall₂ (fun c q => ∃ o, c.2 = some o ∧ q ∈ o.val) (fchosen F (frule F)) qs)
    (hcl : ∀ c ∈ fchosen F (frule F), ∃ o, c.2 = some o ∧
      ((c.1.2.2.1.length = 1 ∧ ∃ k ∈ FEnt.prefs c.1 false, fkindOpt c.1 k = some o) ∨
        (c.1.2.2.1.length = 2 ∧
          fkindOpt c.1 (if c.1.1 = c.1.2.1 then .isoX else .hs) = some o)))
    (hx : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i)
    (h1 : ∀ d ∈ F.filterMap FFac.entData, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum)
    (h2 : ∀ d ∈ F.filterMap FFac.entData, d.2.2.1.length = 2 →
      d.2.2.1.head? = some 0 ∧ (1 ≤ d.2.2.1.sum ∨ d.1 ≠ d.2.1)) :
    ∀ z ∈ (fchosen F (frule F)).zip qs, z.2.d = z.1.1.2.2.1.length - 1 ∧ z.2.o = 0 ∧
      0 ≤ z.2.i ∧ R2T_g1 z ≤ 0 ∧ R2T_g2 z ≤ 0 ∧ R2T_g3 z ≤ 0 ∧ R2T_g4 z ≤ 0 ∧
      R2T_g5 z ≤ 0 ∧
      (z.1.1.2.2.1.length = 1 → (R2T_uc z.1 = 1 ∨ 2 ≤ z.1.1.2.2.1.sum) → R2T_g1 z ≤ -4) ∧
      (z.1.1.2.2.1.length = 2 → R2T_g1 z ≤ -4 ∧ R2T_g2 z ≤ -15) ∧
      (z.1.1.2.2.1.length = 2 → 1 ≤ z.1.1.2.2.1.sum → R2T_g1 z ≤ -6 ∧ R2T_g2 z ≤ -18 ∧
        R2T_g3 z ≤ -18 ∧ R2T_g4 z ≤ -6 ∧ R2T_g5 z ≤ -18) ∧
      (z.1.1.2.2.1.length = 2 → 2 ≤ z.1.1.2.2.1.sum → R2T_g1 z ≤ -10) := by
  intro z hz
  obtain ⟨o, ho, hq⟩ := R2T_zip_mem hF2 z hz
  have hcC : z.1 ∈ fchosen F (frule F) := (List.of_mem_zip hz).1
  have hdE : z.1.1 ∈ F.filterMap FFac.entData := by
    rw [← R2T_fchosen_fst F (frule F)]; exact List.mem_map_of_mem hcC
  obtain ⟨o', ho', hc⟩ := hcl z.1 hcC
  rw [ho] at ho'
  obtain rfl := Option.some.inj ho'
  obtain ⟨⟨d, oc⟩, q⟩ := z
  simp only at ho hq hc hdE ⊢
  subst ho
  refine R2T_zgen d o q hq (hx d hdE) ?_
  rcases hc with ⟨hl, k, hk, hk'⟩ | ⟨hl, hk⟩
  · exact Or.inl ⟨hl, h1 d hdE hl, k, hk, hk'⟩
  · obtain ⟨hh, hr⟩ := h2 d hdE hl
    exact Or.inr ⟨hl, hh, hk, hr⟩

/-- The monomials of the bound in the setting of both cases: an entry `c` of the rule and a member
`(c, q)` of the monomials. -/
private theorem R2T_zof (F : List FFac) (qs : List FMono)
    (hF2 : List.Forall₂ (fun c q => ∃ o, c.2 = some o ∧ q ∈ o.val) (fchosen F (frule F)) qs)
    (d : FEnt) (hd : d ∈ F.filterMap FFac.entData) :
    ∃ z ∈ (fchosen F (frule F)).zip qs, z.1.1 = d := by
  rw [← R2T_fchosen_fst F (frule F)] at hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  obtain ⟨q, hq⟩ := R2T_zip_ex hF2 c hc
  exact ⟨(c, q), hq, rfl⟩

/-- Case (5) of the proof of Lemma 5.5 [claim_estimate_remainder_terms] for Type II: the loop of
`Λ̃₂` has `c₂ ≥ 1` resolvents and the rules expand at the left of `Λ̃₂`. -/
private theorem R2T_case5 (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 2) (p q : ℕ) (hpq' : 2 ≤ p + q)
    (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) (hs : R.ffocusSide = some (1, false))
    (c₂ : ℕ) (hc₂ : 1 ≤ c₂) (hside : ∀ s, R.lamSide 1 s = c₂) :
    FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) (frule R'.rfacs) := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  have hFw := pkg_fpkg_wf R hRw hfoc
  have hR'w : R'.wf = true := pkg_dwirt_iter (fun _ X => X.wf = true) 2 3
    (fun _ X h X' hX' => (pkg_dent_wf X X' 2 3 h hX').1)
    (fun _ X h X' hX' => (pkg_dent_wf X X' 3 2 h hX').1) R.fpkg hFw p q R' hR'
  have hsides := pkg_rem_sides ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hfS := pkg_fpkg_lamSide R hRw hfoc
  have hA0 : 1 ≤ R.lamSide 0 true :=
    (pkg_inv_order ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).2.1 hty (by rw [hside]; omega)
  have hF0 : R.fpkg.lamSide 0 true = R.lamSide 0 true := by rw [hfS]; simp [hs]
  have hF1 : R.fpkg.lamSide 1 true = c₂ := by rw [hfS]; simp [hs, hside]
  have hF1' : R.fpkg.lamSide 1 false = 0 := by rw [hfS]; simp [hs]
  have hR0t : 1 ≤ R'.lamSide 0 true := ((hsides 0 true).2 (by omega)).1
  have hR1t : 1 ≤ R'.lamSide 1 true := ((hsides 1 true).2 (by omega)).1
  have hR1f : R'.lamSide 1 false = 0 := (hsides 1 false).1 hF1'
  obtain ⟨hR0f, e₁, he₁, hl₁, hx₁, -⟩ :=
    pkg_rem_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨-, e, he, e₀, -, hle, -, hrole, -, hleft⟩ :=
    pkg_rem_role0 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' 1 false hs
  obtain ⟨hex, -, -, -, hhead⟩ := hleft rfl
  set F := R'.rfacs with hFdef
  obtain ⟨E, hE⟩ : ∃ E : List FEnt, F.filterMap FFac.entData = E := ⟨_, rfl⟩
  obtain ⟨dP, hdP, hdPE⟩ := R2T_pent_ent R' e he
  obtain ⟨dL, hdL, hdLE⟩ := R2T_pent_ent R' e₁ he₁
  rw [← hFdef, hE] at hdPE hdLE
  obtain ⟨rP1, -, rP3, rP4⟩ := pkg_rent_parts R' e he dP hdP
  obtain ⟨rL1, -, rL3, rL4⟩ := pkg_rent_parts R' e₁ he₁ dL hdL
  obtain ⟨-, sP⟩ := pkg_pents_sides R' hR'w e he 1 hle
  obtain ⟨sL0, sL⟩ := pkg_pents_sides R' hR'w e₁ he₁ 0 hl₁
  set cP := (e.2.2.takeWhile fun x => x != .lw (.lamt 1)).countP PkgLetter.isLam
  set cL := (e₁.2.2.takeWhile fun x => x != .lw (.lamt 0)).countP PkgLetter.isLam
  have hcP : cP + 1 < (pkgParts e.2.2).length := by
    by_contra h
    rw [List.getD_eq_default _ _ (by omega)] at sP
    omega
  have hcL : cL + 1 < (pkgParts e₁.2.2).length := by
    by_contra h
    rw [List.getD_eq_default _ _ (by omega)] at sL
    omega
  -- the counts of `Λ̃`
  obtain ⟨hlam1, hlam2⟩ := pkg_rem_lam ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  rw [hE] at hlam1 hlam2
  replace hlam1 : ∀ d ∈ E, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum := hlam1
  replace hlam2 : (E.map fun d : FEnt => d.2.2.1.length - 1).sum +
      ((fLoops F).map fun w => w.count FLet.lamt).sum = 2 := hlam2
  have hPL : dP ≠ dL := by
    intro h
    have : dP.1 = dL.1 := by rw [h]
    omega
  have hnl := R2T_nat_two E (fun d => d.2.2.1.length - 1) dP dL hdPE hdLE hPL
  have hlenP : dP.2.2.1.length = 2 := by omega
  have hlenL : dL.2.2.1.length = 2 := by omega
  have hoth : ∀ d ∈ E, 2 ≤ d.2.2.1.length → d = dP ∨ d = dL := by
    intro d hd hl
    by_contra hne
    push Not at hne
    have := R2T_nat_three E (fun d => d.2.2.1.length - 1) dP dL d hdPE hdLE hd hPL
      (Ne.symm hne.1) (Ne.symm hne.2)
    omega
  have hloops0 : ((fLoops F).map fun w => w.count FLet.lamt).sum = 0 := by omega
  have hnl2 : (E.map fun d : FEnt => d.2.2.1.length - 1).sum = 2 := by omega
  -- the parts of `P` and `Λ'`
  have hcP0 : cP = 0 := by rw [rP3] at hlenP; omega
  have hcL0 : cL = 0 := by rw [rL3] at hlenL; omega
  rw [hcP0] at sP
  rw [hcL0] at sL sL0
  have hP1 : R'.lamSide 1 true ≤ dP.2.2.1.getD 1 0 := by
    rw [← sP]; exact (rP4 1 (by omega)).1
  have hL1 : R'.lamSide 0 true ≤ dL.2.2.1.getD 1 0 := by
    rw [← sL]; exact (rL4 1 (by omega)).1
  have hPh : dP.2.2.1.head? = some 0 := by simpa [hdP] using hhead
  have hLh : dL.2.2.1.head? = some 0 := by
    have h0 := (rL4 0 (by omega)).2.2 (by rw [sL0, hR0f])
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlenL
    rw [hab] at h0 ⊢
    simp only [List.getD_cons_zero] at h0
    simp [h0]
  have hshape : ∀ d ∈ E, d.2.2.1.length = 2 →
      d.2.2.1.head? = some 0 ∧ 1 ≤ d.2.2.1.sum ∧ (2 ≤ d.2.2.1.getD 1 0 → 2 ≤ d.2.2.1.sum) := by
    intro d hd hl
    have key : ∀ P : List ℕ, P.length = 2 → P.head? = some 0 →
        1 ≤ P.getD 1 0 → P.head? = some 0 ∧ 1 ≤ P.sum ∧ (2 ≤ P.getD 1 0 → 2 ≤ P.sum) := by
      intro P hl hh h1
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hl
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp at h1 ⊢
      omega
    rcases hoth d hd (by omega) with rfl | rfl
    · exact key _ hl hPh (by omega)
    · exact key _ hl hLh (by omega)
  have hroleP : FEnt.role dP = 0 := by simpa [hdP] using hrole
  -- the facts on all entries
  have hE1 : ∀ d ∈ E, 1 ≤ d.2.2.1.length := hE ▸ R2T_E_len F
  have hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4 :=
    R2T_lab4 F R'.nb (pkg_rem_local ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
  have hx : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i := (pkg_rfacs_ext R').1
  have hcl := R2T_class F E hE hE1 ((R2T_cnt_le E).trans (by omega))
    (fun d hd hl => by
      have h2 := hshape d hd (by have := hoth d hd hl; rcases this with rfl | rfl <;> omega)
      exact ⟨by rcases hoth d hd hl with rfl | rfl <;> omega, fun _ => h2.1⟩)
    ⟨dP, hdPE, hroleP⟩
  refine ⟨pkg_rem_valid ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR', fun m hm => ?_⟩
  obtain ⟨qs, hF2, hmq⟩ := (fboundM_mem F (frule F) (frule_run_some F false) m).1 hm
  have hl := hF2.length_eq
  have hz := R2T_zall F qs hF2 hcl hx (hE ▸ hlam1) (fun d hd hl => by
    rw [hE] at hd
    obtain ⟨h1, h2, -⟩ := hshape d hd hl
    exact ⟨h1, Or.inl h2⟩)
  obtain ⟨zP, hzP, hzPd⟩ := R2T_zof F qs hF2 dP (hE ▸ hdPE)
  obtain ⟨zL, hzL, hzLd⟩ := R2T_zof F qs hF2 dL (hE ▸ hdLE)
  have hzPL : zP ≠ zL := fun h => hPL (by rw [← hzPd, ← hzLd, h])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, bP, bP2⟩ := hz zP hzP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, bL, bL2⟩ := hz zL hzL
  rw [hzPd] at bP bP2
  rw [hzLd] at bL bL2
  obtain ⟨bP1, bP2', bP3, bP4, bP5⟩ := bP hlenP (hshape dP hdPE hlenP).2.1
  obtain ⟨bL1, bL2', bL3, bL4, bL5⟩ := bL hlenL (hshape dL hdLE hlenL).2.1
  have hgen := fun (g : (FEnt × Option FOpt) × FMono → ℤ)
      (hg : ∀ z ∈ (fchosen F (frule F)).zip qs, g z ≤ 0) =>
    R2T_sum_two _ g hg zP zL hzP hzL hzPL
  -- the loops and light weights
  have hloopsF : ∀ f ∈ F, ∀ w, f = .loop w → FLet.lamt ∉ w ∧ 2 ≤ fresN w := by
    intro f hf w rfl
    have hw : w ∈ fLoops F := List.mem_filterMap.2 ⟨_, hf, rfl⟩
    have hc0 : w.count FLet.lamt = 0 := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count FLet.lamt) hw)
      omega
    have hn : FLet.lamt ∉ w := List.count_eq_zero.1 hc0
    exact ⟨hn, (pkg_rem_loops ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2 w hw hn⟩
  have hfac := fun f hf => R2T_fac f (hloopsF f hf)
  -- the counts
  have hfR := pkg_rem_fR ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hS := R2T_S R' R.fR hfR
  have hU := R2T_U R R' (p + q) (pkg_rem_mu ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
    (pkg_rem_nent ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
  have hpair : ((F.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum + 2 * (R'.fpi : ℤ) ≤ 2 :=
    pkg_rem_pair ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hfpi : R'.fpi ≤ 1 := by unfold PkgExpr.fpi; split_ifs <;> simp
  have hfR0 := (pkg_inv_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).1
  have hsig := pkg_inv_typeII ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR) hty
  have hZE0 : 0 ≤ ((F.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum :=
    R2T_sumZ_nonneg _ _ fun d hd => (hx d hd).2.2.2.2
  -- the extra `Im m` of the exceptional subcase
  obtain ⟨b, hb01, hbx, hG1⟩ : ∃ b : ℤ, 0 ≤ b ∧ (R.fR = 0 → R.fsig = 1 → b = 1) ∧
      (((fchosen F (frule F)).zip qs).map R2T_g1).sum ≤ -12 - 4 * b := by
    by_cases hx5 : R.fR = 0 ∧ R.fsig = 1
    · refine ⟨1, by norm_num, fun _ _ => rfl, ?_⟩
      have hfree := pkg_rem_free ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
      have h3 : R'.freeTwo = true ∨ 2 ≤ dL.2.2.1.sum ∨ 2 ≤ dP.2.2.1.sum := by
        rcases (pkg_lists' ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).2.2.1 hfoc hty
          hx5.1 hx5.2 with hft | h0t | h1f
        · exact Or.inl (hfree.1 (pkg_fpkg_freeTwo R hRw hfoc hft))
        · rcases hfree.2 0 true (by rw [hF0]; exact h0t) with h | h | h
          · exact Or.inr (Or.inl ((hshape dL hdLE hlenL).2.2 (by omega)))
          · exact Or.inl h
          · simp only [sub_zero, Bool.not_true] at h; omega
        · rcases hfree.2 1 true (by rw [hF1, ← hside false]; exact h1f) with h | h | h
          · exact Or.inr (Or.inr ((hshape dP hdPE hlenP).2.2 (by omega)))
          · exact Or.inl h
          · simp only [sub_self, Bool.not_true] at h; omega
      rcases h3 with hft | h2 | h2
      · obtain ⟨dT, hdT, hlT, hsT⟩ := pkg_freeTwo_ent R' hft
        obtain ⟨zT, hzT, hzTd⟩ := R2T_zof F qs hF2 dT hdT
        have hTP : zP ≠ zT := fun h => by
          have : dP.2.2.1.length = dT.2.2.1.length := by rw [← hzPd, ← hzTd, h]
          omega
        have hTL : zL ≠ zT := fun h => by
          have : dL.2.2.1.length = dT.2.2.1.length := by rw [← hzLd, ← hzTd, h]
          omega
        have hT := (hz zT hzT).2.2.2.2.2.2.2.2.1
        rw [hzTd] at hT
        have := R2T_sum_three _ R2T_g1 (fun z hz' => (hz z hz').2.2.2.1) zP zL zT hzP hzL hzT
          hzPL hTP hTL
        have := hT hlT (Or.inr hsT)
        omega
      · have := bL2 hlenL h2
        have := hgen R2T_g1 fun z hz' => (hz z hz').2.2.2.1
        omega
      · have := bP2 hlenP h2
        have := hgen R2T_g1 fun z hz' => (hz z hz').2.2.2.1
        omega
    · refine ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hx5, ?_⟩
      have := hgen R2T_g1 fun z hz' => (hz z hz').2.2.2.1
      omega
  rw [R2T_rext R']
  refine R2T_final F qs hF2 hlab ((p + q : ℕ) : ℤ) R.fR R.fsig R'.fpi R'.S _ hS hU rfl
    (-12 - 4 * b) (-36) (-36) (-12) (-36) 0 0 0 0 0 2 hG1
    ((hgen R2T_g2 fun z hz' => (hz z hz').2.2.2.2.1).trans (by omega))
    ((hgen R2T_g3 fun z hz' => (hz z hz').2.2.2.2.2.1).trans (by omega))
    ((hgen R2T_g4 fun z hz' => (hz z hz').2.2.2.2.2.2.1).trans (by omega))
    ((hgen R2T_g5 fun z hz' => (hz z hz').2.2.2.2.2.2.2.1).trans (by omega))
    (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.1)
    (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.1)
    (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.2.1)
    (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.2.2.1)
    (R2T_sum_nonpos _ _ fun f hf => (hfac f hf).2.2.2.2.2.2.2) ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_ ?_ m hmq
  · rw [R2T_qs_sumN _ qs hl FMono.d (fun d => d.2.2.1.length - 1) fun z hz' => (hz z hz').1,
      R2T_fchosen_fst, hE, hnl2, R2T_sumN_zero (F.map FFac.fixV) FMono.d fun x hx' => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'; exact (hfac f hf).1]
  · rw [R2T_qs_sumN _ qs hl FMono.o (fun _ => 0) fun z hz' => (hz z hz').2.1,
      R2T_sumN_zero (F.map FFac.fixV) FMono.o fun x hx' => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'; exact (hfac f hf).2.1]
    simp only [add_zero]
    exact R2T_sumN_zero _ _ fun _ _ => rfl
  · have h1 := R2T_sumZ_nonneg qs FMono.i fun q hq => by
      obtain ⟨z, hz', rfl⟩ := R2T_qs_mem _ qs hl q hq; exact (hz z hz').2.2.1
    have h2 := R2T_sumZ_nonneg (F.map FFac.fixV) FMono.i fun x hx' => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'; exact (hfac f hf).2.2.1
    omega
  · by_cases hx5 : R.fR = 0 ∧ R.fsig = 1
    · have := hbx hx5.1 hx5.2
      simp only [Nat.sub_self, Nat.cast_zero]
      push_cast
      omega
    · simp only [Nat.sub_self, Nat.cast_zero]
      push_cast
      omega
  · simp only [Nat.sub_self, Nat.cast_zero]
    push_cast
    omega
  · push_cast
    omega
  · push_cast
    omega
  · push_cast
    omega

/-! ### The loop of `Λ̃₂` without resolvent -/

private theorem R2T_perm_sum {α M : Type*} [DecidableEq α] [AddCommMonoid M] (F : List α) (f0 : α)
    (hf0 : f0 ∈ F) (g : α → M) : (F.map g).sum = g f0 + ((F.erase f0).map g).sum := by
  rw [((List.perm_cons_erase hf0).map g).sum_eq, List.map_cons, List.sum_cons]

private theorem R2T_fm_map {α β : Type*} (f : α → Option β) (b : β) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome = true) : l.filterMap f = l.map fun x => (f x).getD b := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    rw [List.filterMap_cons, hy, List.map_cons, hy, ih fun z hz => h z (by simp [hz])]
    rfl

private theorem R2T_fm_rot {α β : Type*} (f : α → Option β) (b : β) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome = true) (n : ℕ) :
    (l.filterMap f).rotate n = (l.rotate n).filterMap f := by
  rw [R2T_fm_map f b l h, R2T_fm_map f b (l.rotate n) fun x hx => h x (List.mem_rotate.1 hx),
    List.map_rotate]

private theorem R2T_dup_nores (a : Fin 2) (w : List FLet) (h : ∀ x ∈ w, ∀ c f, x ≠ .res c f) :
    w.flatMap (FLet.dupRes a) = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.flatMap_cons, ih fun y hy => h y (by simp [hy])]
    rcases x with ⟨c, f⟩ | ⟨c, pr⟩ | y | _
    · exact absurd rfl (h _ (by simp) c f)
    all_goals rfl

/-- The loop `⟨𝔐_a Λ̃₂ 𝔐_b E_x⟩`, `a ≠ b`, of `gainLam2` is a rotation of four letters. -/
private theorem R2T_gain (R : PkgExpr) (hR : R.wf = true) (w₂ : List PkgLetter)
    (hw : w₂ ∈ R.loops) (hm : PkgLetter.lw (.lamt 1) ∈ w₂) (hg : R.gainLam2 = true) :
    ∃ r < w₂.length, ∃ (a b : Fin 2) (o : Fin 2) (x : ℕ), a ≠ b ∧
      w₂.rotate r = [.lw (.det a), .lw (.lamt o), .lw (.det b), .lw (.proj x)] := by
  unfold PkgExpr.gainLam2 at hg
  obtain ⟨w, hwL, hw'⟩ := List.any_eq_true.1 hg
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw'
  obtain ⟨⟨hc, -⟩, hgl⟩ := hw'
  have := RH_uniq R hR 1 w w₂ hwL hw (by simpa using hc) hm
  subst this
  unfold pkgGainLoop at hgl
  obtain ⟨r, hr, hm'⟩ := List.any_eq_true.1 hgl
  refine ⟨r, List.mem_range.1 hr, ?_⟩
  split at hm'
  · rename_i a o b x heq
    exact ⟨a, b, o, x, by simpa using hm', heq⟩
  · simp at hm'

/-- Case (6) of the proof of Lemma 5.5 [claim_estimate_remainder_terms] for Type II: the loop of
`Λ̃₂` has no resolvent and the rules expand at the right of `Λ̃₁`. -/
private theorem R2T_case6 (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 2) (p q : ℕ) (hpq' : 2 ≤ p + q)
    (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) (hs : R.ffocusSide = some (0, true))
    (w₂ : List PkgLetter) (hw₂ : w₂ ∈ R.loops) (hm₂ : PkgLetter.lw (.lamt 1) ∈ w₂)
    (hE₂ : w₂.any PkgLetter.isEnt = false) (hr₂ : w₂.countP PkgLetter.isRes = 0)
    (hside : ∀ s, R.lamSide 1 s = 0) :
    FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) (frule R'.rfacs) := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  have hFw := pkg_fpkg_wf R hRw hfoc
  have hR'w : R'.wf = true := pkg_dwirt_iter (fun _ X => X.wf = true) 2 3
    (fun _ X h X' hX' => (pkg_dent_wf X X' 2 3 h hX').1)
    (fun _ X h X' hX' => (pkg_dent_wf X X' 3 2 h hX').1) R.fpkg hFw p q R' hR'
  -- `fR ≥ 1`: the empty left side of `Λ̃₂`
  have hfR1 : 1 ≤ R.fR := by
    have h := pkg_inv_empty ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
    unfold PkgExpr.emptySides at h
    rw [hty, hside false] at h
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at h
    split_ifs at h <;> push_cast at h <;> omega
  obtain ⟨hR0f, e₁, he₁, hl₁, hx₁, hall₁⟩ :=
    pkg_rem_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  obtain ⟨-, e, he, e₀, -, hle, -, hrole, hright, -⟩ :=
    pkg_rem_role0 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' 0 true hs
  obtain ⟨hey, -, -, -, hlast⟩ := hright rfl
  set F := R'.rfacs with hFdef
  obtain ⟨E, hE⟩ : ∃ E : List FEnt, F.filterMap FFac.entData = E := ⟨_, rfl⟩
  obtain ⟨dP, hdP, hdPE⟩ := R2T_pent_ent R' e he
  obtain ⟨dL, hdL, hdLE⟩ := R2T_pent_ent R' e₁ he₁
  rw [← hFdef, hE] at hdPE hdLE
  obtain ⟨-, rP2, rP3, -⟩ := pkg_rent_parts R' e he dP hdP
  obtain ⟨rL1, -, rL3, rL4⟩ := pkg_rent_parts R' e₁ he₁ dL hdL
  have hroleP : FEnt.role dP = 0 := by simpa [hdP] using hrole
  have hlenP2 : 2 ≤ dP.2.2.1.length := (R2T_role_le1 dP).1 (by omega)
  have hlenL2 : 2 ≤ dL.2.2.1.length := by rw [rL3]; exact R2T_parts_two _ 0 hl₁
  -- the loop of `Λ̃₂`
  have hres : w₂.any PkgLetter.isRes = false := by
    rw [List.any_eq_false]; intro x hx hxr
    have := List.countP_pos_iff.2 ⟨x, hx, hxr⟩
    omega
  have hw₂' := pkg_rem_resfree ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR' w₂ hw₂ hres
  set wf := w₂.filterMap (PkgLetter.flet (fun _ => false) R'.fpm) with hwf
  have hnores : ∀ x ∈ wf, ∀ c f, x ≠ .res c f := by
    intro x hx c f hxe
    subst hxe
    obtain ⟨y, hy, hyx⟩ := List.mem_filterMap.1 hx
    rcases y with ((b | b | y | o) | ⟨u, v⟩) <;> simp [PkgLetter.flet] at hyx
    have := List.any_eq_false.1 hres _ hy
    simp [PkgLetter.isRes] at this
  have hfL : FFac.loop wf ∈ F := by
    have h1 : FFac.loop wf ∈ R'.ffacs (fun _ => false) R'.fpm := by
      rw [FF_ffacs]
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨w₂, hw₂', ?_⟩)
      rw [FW_wf_free _ w₂ hE₂]
      exact List.mem_singleton_self _
    have h2 : FW_g R' (FFac.loop wf) = FFac.loop wf := by
      unfold FW_g
      split_ifs <;> simp [FFac.dupRes, R2T_dup_nores _ wf hnores]
    rw [hFdef, FW_rfacs, ← h2]
    exact List.mem_map_of_mem h1
  have hwfL : wf ∈ fLoops F := List.mem_filterMap.2 ⟨_, hfL, rfl⟩
  have hcwf : 1 ≤ wf.count FLet.lamt := List.count_pos_iff.2
    (List.mem_filterMap.2 ⟨_, hm₂, rfl⟩)
  have hrwf : fresN wf = 0 := by
    unfold fresN
    rw [List.countP_eq_zero]
    intro x hx
    rcases x with ⟨c, f⟩ | _ | _ | _
    · exact absurd rfl (hnores _ hx c f)
    all_goals simp
  -- the counts of `Λ̃`
  obtain ⟨hlam1, hlam2⟩ := pkg_rem_lam ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  rw [hE] at hlam1 hlam2
  replace hlam1 : ∀ d ∈ E, d.2.2.1.length = 1 → 1 ≤ d.2.2.1.sum := hlam1
  replace hlam2 : (E.map fun d : FEnt => d.2.2.1.length - 1).sum +
      ((fLoops F).map fun w => w.count FLet.lamt).sum = 2 := hlam2
  have hLwf := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count FLet.lamt) hwfL)
  have hPE := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d : FEnt => d.2.2.1.length - 1)
    hdPE)
  have hPL : dL = dP := by
    by_contra hne
    have := R2T_nat_two E (fun d => d.2.2.1.length - 1) dP dL hdPE hdLE (Ne.symm hne)
    omega
  subst hPL
  have hlenP : dL.2.2.1.length = 2 := by omega
  have hnl1 : (E.map fun d : FEnt => d.2.2.1.length - 1).sum = 1 := by omega
  have hwf1 : wf.count FLet.lamt = 1 := by omega
  have hoth : ∀ d ∈ E, 2 ≤ d.2.2.1.length → d = dL := by
    intro d hd hl
    by_contra hne
    have := R2T_nat_two E (fun d => d.2.2.1.length - 1) dL d hdLE hd (Ne.symm hne)
    omega
  -- the parts of `P`
  have hc0 : (e₁.2.2.takeWhile fun x => x != .lw (.lamt 0)).countP PkgLetter.isLam = 0 := by
    rw [List.countP_eq_zero]
    intro x hx hxl
    have := List.all_eq_true.1 hall₁ x hx
    simp [hxl] at this
  obtain ⟨sL0, -⟩ := pkg_pents_sides R' hR'w e₁ he₁ 0 hl₁
  rw [hc0] at sL0
  have hP0 : dL.2.2.1.getD 0 0 = 0 := (rL4 0 (by omega)).2.2 (by rw [sL0, hR0f])
  have hPl : dL.2.2.1.getLast? = some 0 := by simpa [hdP] using hlast
  have hPparts : dL.2.2.1 = [0, 0] := by
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlenP
    rw [hab] at hP0 hPl ⊢
    simp at hP0 hPl
    rw [hP0, hPl]
  have hx1 : dL.1 < 2 := by rw [rL1]; exact hx₁
  have hy3 : dL.2.1 = 3 := by rw [rP2, hey]
  -- the facts on all entries
  have hE1 : ∀ d ∈ E, 1 ≤ d.2.2.1.length := hE ▸ R2T_E_len F
  have hlab : ∀ d ∈ F.filterMap FFac.entData, d.1 < 4 ∧ d.2.1 < 4 :=
    R2T_lab4 F R'.nb (pkg_rem_local ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
  have hx : ∀ d ∈ F.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i := (pkg_rfacs_ext R').1
  have hsh : ∀ d ∈ E, 2 ≤ d.2.2.1.length →
      d.2.2.1.length = 2 ∧ (d.1 = d.2.1 → d.2.2.1.head? = some 0) := by
    intro d hd hl
    obtain rfl := hoth d hd hl
    exact ⟨hlenP, fun _ => by rw [hPparts]; rfl⟩
  have hcnt1 : E.countP (fun d => 2 ≤ d.2.2.1.length) ≤ 1 := (R2T_cnt_le E).trans (by omega)
  have hcnt1' : E.countP (fun d => 2 ≤ d.2.2.1.length) = 1 := by
    have := (List.countP_pos_iff (p := fun d : FEnt => decide (2 ≤ d.2.2.1.length))).2
      ⟨dL, hdLE, decide_eq_true hlenL2⟩
    omega
  have hends := pkg_rem_ends ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  rw [← hFdef, hE] at hends
  have h2 := R2T_parity E (p + q) (hE ▸ hlab) hends hE1 hlam1 hcnt1' (fun d hd hl => by
    obtain rfl := hoth d hd hl
    omega)
  have hcl := R2T_class F E hE hE1 (by omega) hsh ⟨dL, hdLE, hroleP⟩
  obtain ⟨cW, hcW, hlW, huW⟩ := R2T_ward F E hE hE1 hcnt1 hsh ⟨dL, hdLE, hroleP⟩ h2
  refine ⟨pkg_rem_valid ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR', fun m hm => ?_⟩
  obtain ⟨qs, hF2, hmq⟩ := (fboundM_mem F (frule F) (frule_run_some F false) m).1 hm
  have hl := hF2.length_eq
  have hz := R2T_zall F qs hF2 hcl hx (hE ▸ hlam1) (fun d hd hl => by
    rw [hE] at hd
    obtain rfl := hoth d hd (by omega)
    refine ⟨by rw [hPparts]; rfl, Or.inr (by omega)⟩)
  obtain ⟨zP, hzP, hzPd⟩ := R2T_zof F qs hF2 dL (hE ▸ hdLE)
  obtain ⟨qW, hzW⟩ := R2T_zip_ex hF2 cW hcW
  have hzPW : zP ≠ (cW, qW) := fun h => by
    have : dL.2.2.1.length = cW.1.2.2.1.length := by rw [← hzPd, h]
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, bP, -, -⟩ := hz zP hzP
  rw [hzPd] at bP
  obtain ⟨bP1, bP2⟩ := bP hlenP
  have bW := (hz _ hzW).2.2.2.2.2.2.2.2.1 hlW (Or.inl huW)
  have hgen := fun (g : (FEnt × Option FOpt) × FMono → ℤ)
      (hg : ∀ z ∈ (fchosen F (frule F)).zip qs, g z ≤ 0) =>
    R2T_sum_two _ g hg zP _ hzP hzW hzPW
  -- the loops and light weights
  have hLsum : ((fLoops F).map fun w => w.count FLet.lamt).sum = 1 := by omega
  have hloopsF : ∀ f ∈ F.erase (.loop wf), ∀ w, f = .loop w → FLet.lamt ∉ w ∧ 2 ≤ fresN w := by
    intro f hf w rfl
    have hw : w ∈ fLoops (F.erase (.loop wf)) := List.mem_filterMap.2 ⟨_, hf, rfl⟩
    have hperm : (fLoops F).Perm (wf :: fLoops (F.erase (.loop wf))) :=
      (List.perm_cons_erase hfL).filterMap _
    have hs1 := (hperm.map fun w => w.count FLet.lamt).sum_eq
    simp only [List.map_cons, List.sum_cons] at hs1
    have hc0 : w.count FLet.lamt = 0 := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count FLet.lamt) hw)
      omega
    have hn : FLet.lamt ∉ w := List.count_eq_zero.1 hc0
    exact ⟨hn, (pkg_rem_loops ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR').2 w
      (hperm.symm.subset (List.mem_cons_of_mem _ hw)) hn⟩
  have hfac := fun f hf => R2T_fac f (hloopsF f hf)
  obtain ⟨fL1, fL2, fL3, fL4, fL5, fL6, fL7, fL8, fL9, fL10⟩ := R2T_facL wf hwf1 hrwf
  have hHk := fun (g : FFac → ℤ) (hg : ∀ f ∈ F.erase (.loop wf), g f ≤ 0) => by
    have := R2T_perm_sum F (.loop wf) hfL g
    have := R2T_sum_nonpos _ g hg
    exact (show (F.map g).sum ≤ g (.loop wf) by omega)
  -- the counts
  have hfR := pkg_rem_fR ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hS := R2T_S R' R.fR hfR
  have hU := R2T_U R R' (p + q) (pkg_rem_mu ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
    (pkg_rem_nent ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR')
  have hpair : ((F.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum + 2 * (R'.fpi : ℤ) ≤ 2 :=
    pkg_rem_pair ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR p q R' hR'
  have hfpi : R'.fpi ≤ 1 := by unfold PkgExpr.fpi; split_ifs <;> simp
  have hsig := pkg_inv_typeII ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR) hty
  have hZE0 : 0 ≤ ((F.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum :=
    R2T_sumZ_nonneg _ _ fun d hd => (hx d hd).2.2.2.2
  -- the gain of the loop of `Λ̃₂` in the exceptional subcase
  have hgain : R.fR = 1 → R.fsig = 1 → (FFac.loop wf).fixV.i = 2 := by
    intro h1 h2
    have hg := (pkg_lists' ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)).2.2.2.1 hfoc hty
      (hside false) h1 h2
    obtain ⟨r, hr, a, b, o, x, hab, hrot⟩ := R2T_gain R hRw w₂ hw₂ hm₂ hg
    have htot : ∀ y ∈ w₂, (PkgLetter.flet (fun _ => false) R'.fpm y).isSome = true := by
      intro y hy
      rcases y with _ | ⟨u, v⟩
      · rename_i z; rcases z <;> rfl
      · have := List.any_eq_false.1 hE₂ _ hy
        simp [PkgLetter.isEnt] at this
    have hrot' : wf.rotate r = [.det a (R'.fpm a), .lamt, .det b (R'.fpm b), .proj x] := by
      rw [hwf, R2T_fm_rot _ FLet.lamt w₂ htot r, hrot]
      rfl
    have hlen : wf.length = w₂.length := by
      rw [hwf, R2T_fm_map _ FLet.lamt w₂ htot, List.length_map]
    rw [R2T_fixL_gain wf hwf1 hrwf r (by omega) a b _ _ x hab hrot']
  rw [R2T_rext R']
  refine R2T_final F qs hF2 hlab ((p + q : ℕ) : ℤ) R.fR R.fsig R'.fpi R'.S _ hS hU rfl
    (-8) (-15) 0 0 0 (-2 * (FFac.loop wf).fixV.i) (-3 * (FFac.loop wf).fixV.i)
    (3 * (FFac.loop wf).fixV.i) 0 0 3
    ((hgen R2T_g1 fun z hz' => (hz z hz').2.2.2.1).trans (by omega))
    ((hgen R2T_g2 fun z hz' => (hz z hz').2.2.2.2.1).trans (by
      have := (hz _ hzW).2.2.2.2.1; omega))
    (R2T_sum_nonpos _ _ fun z hz' => (hz z hz').2.2.2.2.2.1)
    (R2T_sum_nonpos _ _ fun z hz' => (hz z hz').2.2.2.2.2.2.1)
    (R2T_sum_nonpos _ _ fun z hz' => (hz z hz').2.2.2.2.2.2.2.1)
    ((hHk R2T_h1 fun f hf => (hfac f hf).2.2.2.1).trans (by omega))
    ((hHk R2T_h2 fun f hf => (hfac f hf).2.2.2.2.1).trans (by omega))
    ((hHk R2T_h3 fun f hf => (hfac f hf).2.2.2.2.2.1).trans (by omega))
    ((hHk R2T_h4 fun f hf => (hfac f hf).2.2.2.2.2.2.1).trans (by omega))
    ((hHk R2T_h5 fun f hf => (hfac f hf).2.2.2.2.2.2.2).trans (by omega))
    ?_ ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ ?_ m hmq
  · rw [R2T_qs_sumN _ qs hl FMono.d (fun d => d.2.2.1.length - 1) fun z hz' => (hz z hz').1,
      R2T_fchosen_fst, hE, hnl1, List.map_map, R2T_perm_sum F (.loop wf) hfL,
      R2T_sumN_zero (F.erase (.loop wf)) (FMono.d ∘ FFac.fixV) fun f hf => (hfac f hf).1]
    simp only [Function.comp, fL1]
    rfl
  · rw [R2T_qs_sumN _ qs hl FMono.o (fun _ => 0) fun z hz' => (hz z hz').2.1,
      R2T_sumN_zero ((fchosen F (frule F)).map Prod.fst) (fun _ => 0) (fun _ _ => rfl),
      zero_add, List.map_map, R2T_perm_sum F (.loop wf) hfL,
      R2T_sumN_zero (F.erase (.loop wf)) (FMono.o ∘ FFac.fixV) fun f hf => (hfac f hf).2.1]
    simp only [Function.comp, fL2, add_zero]
  · have h1 := R2T_sumZ_nonneg qs FMono.i fun q hq => by
      obtain ⟨z, hz', rfl⟩ := R2T_qs_mem _ qs hl q hq; exact (hz z hz').2.2.1
    have h2 := R2T_sumZ_nonneg (F.map FFac.fixV) FMono.i fun x hx' => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'
      by_cases hfe : f = .loop wf
      · subst hfe; exact fL3
      · exact (hfac f ((List.mem_erase_of_ne hfe).2 hf)).2.2.1
    omega
  · by_cases hx6 : R.fR = 1 ∧ R.fsig = 1
    · have := hgain hx6.1 hx6.2
      push_cast
      omega
    · push_cast
      omega
  · push_cast
    omega
  · push_cast
    omega
  · push_cast
    omega
  · push_cast
    omega

/-- The rule of the companion cases (5), (6) in the proof of Lemma 5.5
[claim_estimate_remainder_terms], for the remainder terms of Type II, as the rule lemma of Type I
does for Type I. -/
theorem pkg_rule_two (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 2) (p q : ℕ) (hpq' : 2 ≤ p + q)
    (R' : PkgExpr) (hR' : R' ∈ R.fpkg.dwirt 2 3 p q) :
    FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) (frule R'.rfacs) := by
  have hRw := pkg_inv_wf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R (Or.inr hR)
  have hfoc := pkg_fInner_focus ε j [R₀] R hR
  have hlam1 : ∃ w ∈ R.loops, w.any PkgLetter.isEnt = true ∧ PkgLetter.lw (.lamt 0) ∈ w := by
    obtain ⟨w, hw, hwE, σ, hσ, hmem, -⟩ := pkg_inv_lam1 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R
      (Or.inr hR)
    obtain ⟨e, he, rfl⟩ := pkg_pents_segs R w hw hwE σ hσ
    exact RH_ent_loop R e he _ hmem
  obtain ⟨w₂, hw₂, hm₂, hE₂, -, hside, hcase⟩ := R2T_cases R hRw hty hlam1 hfoc
  rcases hcase with ⟨hs, hc⟩ | ⟨hs, hc⟩
  · exact R2T_case5 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q hpq' R' hR' hs _ hc hside
  · exact R2T_case6 ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q hpq' R' hR' hs w₂ hw₂ hm₂ hE₂ hc
      fun s => (hside s).trans hc

end RBMTransitionEdge

end
