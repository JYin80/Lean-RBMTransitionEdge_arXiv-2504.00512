module

public import RBMTransitionEdge.Localized.Expansion.PkgInv
public import RBMTransitionEdge.Localized.Expansion.PkgShape
public import RBMTransitionEdge.Localized.Expansion.Counts
import all RBMTransitionEdge.Localized.Expansion.PkgInv
import all RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.Counts

@[expose] public section

/-!
# The sides of `Λ̃` in the further expansion of Lemma 5.5

The numbers of resolvents next to `Λ̃₁` and `Λ̃₂` (the side counts `a₁, …, a₄` of (5.79)–(5.81)
[further_expansion_expression_Type_1]–[further_expansion_expression_Type_3]), the order in which
the rules (i)–(iv) empty them, the bound of the number of empty sides by `fR`, and `Σ ≥ 1` in
Type II, on every expression reached from a derivative structure in the proof of Lemma 5.5
[claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The number of resolvents next to `Λ̃_o` on one side (`right`), up to the next letter `Δ` or
`Λ̃`: `a₁` (`o = 0`, right), `a₂` (`o = 1`, left), `a₃` (`o = 1`, right) of (5.79)
[further_expansion_expression_Type_1]; `a₄` of (5.80) [further_expansion_expression_Type_2]
(`o = 1`, left); `a₁`, `a₂` of (5.81) [further_expansion_expression_Type_3] (`o = 1`, left and
right). `0` when `Λ̃_o` is absent. -/
def PkgExpr.lamSide (R : PkgExpr) (o : Fin 2) (right : Bool) : ℕ :=
  match R.loops.find? fun w => w.contains (.lw (.lamt o)) with
  | none => 0
  | some w =>
    let i := w.idxOf (.lw (.lamt o))
    (((List.range (w.length - 1)).map fun t =>
        if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length).takeWhile
      fun r => match w[r]? with
        | some (PkgLetter.ent _ _) => false
        | some (PkgLetter.lw (LoopLetter.lamt _)) => false
        | _ => true).countP fun r => match w[r]? with
          | some (PkgLetter.lw (LoopLetter.res _)) => true
          | _ => false

/-- The number of empty sides next to `Λ̃`: `a₁, a₂, a₃` in Type I, `a₁` and the loop of `Λ̃₂`
in Type II, `a₁` (between the two) and `a₂` in Type III. -/
def PkgExpr.emptySides (R : PkgExpr) : ℕ :=
  match R.ptype with
  | 1 => [R.lamSide 0 true, R.lamSide 1 false, R.lamSide 1 true].count 0
  | 2 => [R.lamSide 0 true, R.lamSide 1 false].count 0
  | _ => [R.lamSide 0 true, R.lamSide 1 true].count 0

open private inv_reach fR_step fsig_eq fR_eq fterms_cases invW rotated_split cut_pieces ArcInv ArcW
  FreeS pkgStart_loops focus_isSome arcInv_dwirt arcInv_step reach_wf reach_kk
  from RBMTransitionEdge.Localized.Expansion.PkgInv
open private split_at dent_cases from RBMTransitionEdge.Localized.Expansion.PkgShape
open private focus_foc kk_eq_kloop kloop lseg notLam rcR count_le_one uniq_loop
  from RBMTransitionEdge.Localized.Expansion.Counts

/-! ### Auxiliary facts: `Σ ≥ 1` in Type II -/

/-- Some word of the expression contains `Λ̃₂` and no letter `Δ`: the word `⟨Λ̃₂ Π⟩` of Type II. -/
private def Alpha (R : PkgExpr) : Prop :=
  ∃ L ∈ R.loops, PkgLetter.lw (.lamt 1) ∈ L ∧ (L.any fun x => match x with
    | .ent _ _ => true | _ => false) = false

/-- Type II has a word with `Λ̃₂` and no `Δ`. -/
private theorem alpha_of_ptype (R : PkgExpr) (h : R.ptype = 2) : Alpha R := by
  unfold PkgExpr.ptype at h
  rcases hf : R.loops.find? (fun w => w.contains (.lw (.lamt 1))) with _ | w₂
  · rw [hf] at h
    simp at h
  · rw [hf] at h
    dsimp only at h
    refine ⟨w₂, List.mem_of_find?_eq_some hf, ?_, ?_⟩
    · simpa using List.find?_some hf
    · split_ifs at h with h1 h2
      · rw [List.any_eq_false]
        simp only [Bool.not_eq_true', List.any_eq_false] at h1
        intro x hx hx'
        have := h1 x hx
        cases x <;> simp_all
      · omega
      · omega

/-- The first term of `fterms` is the only one with the operation `𝔣𝔯`; it replaces the chosen
resolvent `𝒢_a` of the word `w` by `𝔐_a`. -/
private theorem fterms_frep (P R' : PkgExpr) (h : (PkgOp.frep, R') ∈ P.fterms) :
    ∃ (ℓ r : ℕ) (w : List PkgLetter) (a : Fin 2) (tl : List PkgLetter),
      P.loops[ℓ]? = some w ∧ w.rotate r = .lw (.res a) :: tl ∧
      R'.loops = P.loops.set ℓ (.lw (.det a) :: tl) := by
  unfold PkgExpr.fterms at h
  split at h
  · simp at h
  · rename_i ℓ r right hf
    split at h
    · simp at h
    · rename_i w hw
      split at h
      · rename_i a tl hrot
        dsimp only at h
        have hWdef : (if right = true then PkgLetter.lw (.res a) :: tl ++ [PkgLetter.lw (.det a)]
            else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)]) = invW right a tl := rfl
        rw [hWdef] at h
        refine ⟨ℓ, r, w, a, tl, hw, hrot, ?_⟩
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with h | h
              · obtain ⟨-, rfl⟩ := Prod.mk.inj h
                rfl
              · rcases List.mem_cons.1 h with h | h
                · obtain ⟨hop, -⟩ := Prod.mk.inj h
                  split_ifs at hop
                · simp at h
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 h
              split at hq
              · simp at hq
              · split at hq
                · obtain ⟨hop, -⟩ := Prod.mk.inj (Option.some.inj hq)
                  split_ifs at hop
                · simp at hq
          · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
            split at hj
            · obtain ⟨hop, -⟩ := Prod.mk.inj (Option.some.inj hj)
              split_ifs at hop
            · simp at hj
        · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
          split at hj
          · simp at hj
          · split at hj
            · simp at hj
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · obtain ⟨hop, -⟩ := Prod.mk.inj (Option.some.inj hq)
                split_ifs at hop
              · simp at hq
      · simp at h

/-- The change of `fsig` along a term: `0` at `𝔣𝔯`, `1` at the ten other rows of Table 2
[table_effect_of_operations_2]. -/
private theorem fsig_term (S R' : PkgExpr) (o : PkgOp) (h : (o, R') ∈ S.fterms) :
    (o = PkgOp.frep → R'.fsig = S.fsig) ∧ (o ≠ PkgOp.frep → R'.fsig = S.fsig + 1) := by
  have h2 := pkg_table2 S o R' h
  simp only [fsig_eq, h2, Prod.fst_add, Prod.snd_add]
  cases o <;> simp [PkgOp.delta] <;> omega

/-- `𝔣𝔯` keeps a word with `Λ̃₂` and no `Δ`. -/
private theorem alpha_frep (S R' : PkgExpr) (h : (PkgOp.frep, R') ∈ S.fterms) (hA : Alpha R') :
    Alpha S := by
  obtain ⟨ℓ, r, w, a, tl, hw, hrot, hl⟩ := fterms_frep S R' h
  obtain ⟨L, hL, h2, h3⟩ := hA
  rw [hl] at hL
  rcases List.mem_or_eq_of_mem_set hL with hL | rfl
  · exact ⟨L, hL, h2, h3⟩
  · refine ⟨w, List.mem_of_getElem? hw, ?_, ?_⟩
    · rw [← List.mem_rotate (n := r), hrot]
      rcases List.mem_cons.1 h2 with h2 | h2
      · cases h2
      · exact List.mem_cons_of_mem _ h2
    · rw [List.any_eq_false] at h3 ⊢
      intro x hx
      rw [← List.mem_rotate (n := r), hrot] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact h3 x (List.mem_cons_of_mem _ hx)

/-- One derivative `∂` of a single word with `𝒢_a` replaced by `𝒢_a Δ_{uv} 𝒢_a`. -/
private theorem dent_single (R R' : PkgExpr) (u v : ℕ) (hw : R.weights = [])
    (h : R' ∈ R.dent u v) :
    ∃ (ℓ : ℕ) (X Y : List PkgLetter) (a : Fin 2), R.loops[ℓ]? = some (X ++ .lw (.res a) :: Y) ∧
      R'.loops = R.loops.set ℓ (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) ∧
      R'.weights = [] := by
  unfold PkgExpr.dent at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨ℓ, -, h⟩ := List.mem_flatMap.1 h
    rcases hℓ : R.loops[ℓ]? with _ | w
    · simp [hℓ] at h
    · simp only [hℓ] at h
      obtain ⟨r, -, h⟩ := List.mem_filterMap.1 h
      split at h
      · rename_i a hr
        simp only [Option.some.injEq] at h
        have hw' := split_at w r _ hr
        refine ⟨ℓ, w.take r, w.drop (r + 1), a, by rw [← hw']; exact hℓ, ?_, ?_⟩
        · rw [← h]
        · rw [← h]
          exact hw
      · simp at h
  · obtain ⟨j, hj, -⟩ := List.mem_filterMap.1 h
    simp [hw] at hj

/-- A single word with the letter `Δ₁₀` stays a single word with `Δ₁₀` under derivatives. -/
private def Single (R : PkgExpr) : Prop :=
  ∃ w, R.loops = [w] ∧ PkgLetter.ent 1 0 ∈ w ∧ R.weights = []

private theorem single_dent (u v : ℕ) (R R' : PkgExpr) (hR : Single R) (h : R' ∈ R.dent u v) :
    Single R' := by
  obtain ⟨w, hl, he, hw⟩ := hR
  obtain ⟨ℓ, X, Y, a, hℓ, hl', hw'⟩ := dent_single R R' u v hw h
  rw [hl] at hℓ hl'
  rcases ℓ with _ | ℓ
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hℓ
    subst hℓ
    refine ⟨_, by simpa using hl', ?_, hw'⟩
    simp only [List.mem_append, List.mem_cons] at he ⊢
    tauto
  · simp at hℓ

private theorem single_iter (u v : ℕ) : ∀ (p : ℕ) (L : List PkgExpr), (∀ R ∈ L, Single R) →
    ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[p] L, Single R
  | 0, L, hL, R, hR => hL R hR
  | p + 1, L, hL, R, hR => by
      rw [Function.iterate_succ_apply] at hR
      refine single_iter u v p _ ?_ R hR
      intro R' hR'
      obtain ⟨R'', hR'', hd⟩ := List.mem_flatMap.1 hR'
      exact single_dent u v R'' R' (hL R'' hR'') hd

/-- The derivative structures of the starting loop have one word, which has a letter `Δ`. -/
private theorem single_start (p q : ℕ) (R : PkgExpr) (hR : R ∈ loopStart.pkgStart.dwirt 0 1 p q) :
    Single R := by
  have h0 : Single loopStart.pkgStart := by
    refine ⟨[.lw (.det 0), .lw (.lamt 0), .lw (.res 1), .lw (.lamt 1), .lw (.res 0), .ent 1 0], ?_,
      by simp, ?_⟩
    · unfold LoopExpr.pkgStart
      rw [show loopStart.focus = some (0, 0, [.lamt 0, .res 1, .lamt 1]) by decide]
      rfl
    · unfold LoopExpr.pkgStart
      rw [show loopStart.focus = some (0, 0, [.lamt 0, .res 1, .lamt 1]) by decide]
      rfl
  unfold PkgExpr.dwirt at hR
  refine single_iter 0 1 p _ (fun R₁ hR₁ => ?_) R hR
  refine single_iter 1 0 q [loopStart.pkgStart] ?_ R₁ hR₁
  intro R₂ hR₂
  rw [List.mem_singleton.1 hR₂]
  exact h0

/-- `Σ ≥ 0`, and `Σ ≥ 1` when a word has `Λ̃₂` and no `Δ`. -/
private def SigInv (S : PkgExpr) : Prop := 0 ≤ S.fsig ∧ (Alpha S → 1 ≤ S.fsig)

/-- One step of the further expansion keeps `SigInv`: `𝔣𝔯` keeps `Σ` and the word, every other
row of Table 2 [table_effect_of_operations_2] raises `Σ` by one. -/
private theorem sigInv_step (S : PkgExpr) (hS : SigInv S) (R' : PkgExpr) (h : R' ∈ S.fstep) :
    SigInv R' := by
  have hmono := fR_step S R' h
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  have hm : S.fsig ≤ R''.fsig := hmono.2
  change SigInv R''
  refine ⟨by have := hS.1; omega, fun hA => ?_⟩
  obtain ⟨h1, h2⟩ := fsig_term S R'' o hmem
  by_cases ho : o = PkgOp.frep
  · subst ho
    have := hS.2 (alpha_frep S R'' hmem hA)
    rw [h1 rfl]
    exact this
  · have := h2 ho
    have := hS.1
    omega

/-! ### Auxiliary facts: the kinds of the letters and their cyclic neighbours

A side of `Λ̃_o` is nonempty exactly when the first letter next to `Λ̃_o` in that direction that is
not `𝔐` or `E_x` is a resolvent. The words are therefore read through the kinds `𝒢`, `Δ`, `Λ̃_o` of
their letters, cyclically; one step of the further expansion changes the cyclically consecutive
pairs of kinds only at the resolvent it acts on. -/

/-- The kind of a letter that stops or is counted by a side: a resolvent, a `Δ`, or `Λ̃_o`. -/
private inductive Kd
  | g
  | d
  | l (o : Fin 2)
  deriving DecidableEq

/-- The kind of a letter; `𝔐_a` and `E_x` have none. -/
private def kd : PkgLetter → Option Kd
  | .lw (.res _) => some .g
  | .ent _ _ => some .d
  | .lw (.lamt o) => some (.l o)
  | .lw (.det _) => none
  | .lw (.proj _) => none

/-- The kinds of the letters of a word, in order. -/
private def kw (w : List PkgLetter) : List Kd := w.filterMap kd

/-- The consecutive pairs of a list. -/
private def lp : List Kd → List (Kd × Kd)
  | x :: y :: t => (x, y) :: lp (y :: t)
  | _ => []

/-- The pair `p` is consecutive in the cyclic word `l`. -/
private def CP (l : List Kd) (p : Kd × Kd) : Prop :=
  p ∈ lp l ∨ (l.getLast? = some p.1 ∧ l.head? = some p.2)

private theorem mem_lp_append (p : Kd × Kd) : ∀ A B : List Kd,
    p ∈ lp (A ++ B) ↔ p ∈ lp A ∨ p ∈ lp B ∨ (A.getLast? = some p.1 ∧ B.head? = some p.2)
  | [], B => by simp [lp]
  | [x], [] => by simp [lp]
  | [x], y :: B => by
      obtain ⟨p1, p2⟩ := p
      simp [lp, Prod.ext_iff]
      tauto
  | x :: y :: A, B => by
      have ih := mem_lp_append p (y :: A) B
      simp only [List.cons_append] at ih ⊢
      simp only [lp, List.mem_cons, ih, List.getLast?_cons_cons]
      tauto

private theorem lp_mem : ∀ (x : Kd) (Z : List Kd) (p : Kd × Kd), p ∈ lp (x :: Z) →
    p.1 ∈ x :: Z ∧ p.2 ∈ Z
  | x, [], p, h => by simp [lp] at h
  | x, y :: Z, p, h => by
      simp only [lp, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := lp_mem y Z p h
        exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

private theorem CP_comm (A B : List Kd) (p : Kd × Kd) : CP (A ++ B) p ↔ CP (B ++ A) p := by
  rcases A with _ | ⟨a, A⟩
  · simp
  rcases B with _ | ⟨b, B⟩
  · simp
  unfold CP
  rw [mem_lp_append, mem_lp_append]
  simp only [List.getLast?_append, List.head?_append, List.getLast?_cons, List.head?_cons,
    Option.some_or]
  tauto

private theorem CP_rot {l l' : List Kd} (h : l.IsRotated l') (p : Kd × Kd) : CP l p ↔ CP l' p := by
  obtain ⟨A, B, rfl, rfl⟩ := rotated_split h
  exact CP_comm A B p

private theorem CP_J (A B : List Kd) (hA : A ≠ []) (hB : B ≠ [])
    (h : (A.head? = some .g ∧ B.head? = some .g) ∨ (A.getLast? = some .g ∧ B.getLast? = some .g))
    (p : Kd × Kd) : CP (A ++ B) p ↔ CP A p ∨ CP B p := by
  rcases A with _ | ⟨a, A⟩
  · exact absurd rfl hA
  rcases B with _ | ⟨b, B⟩
  · exact absurd rfl hB
  unfold CP
  rw [mem_lp_append]
  obtain ⟨p1, p2⟩ := p
  simp only [List.getLast?_append, List.head?_append, List.getLast?_cons, List.head?_cons,
    Option.some_or, Option.some.injEq] at h ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · tauto
  · rw [h1, h2]
    tauto

private theorem CP_dup (A B : List Kd) (p : Kd × Kd) :
    CP (A ++ .g :: .g :: B) p ↔ CP (A ++ .g :: B) p ∨ p = (.g, .g) := by
  rw [CP_comm, CP_comm A]
  unfold CP
  simp only [List.cons_append, lp, List.mem_cons, List.getLast?_cons_cons, List.head?_cons]
  tauto

private theorem CP_single (x : Kd) (p : Kd × Kd) : CP [x] p ↔ p = (x, x) := by
  obtain ⟨p1, p2⟩ := p
  simp [CP, lp, Prod.ext_iff, eq_comm]

private theorem CP_cut (A B : List Kd) (p : Kd × Kd) (hp : p ≠ (.g, .g))
    (h : (A ++ .g :: B).head? = some .g ∨ (A ++ .g :: B).getLast? = some .g) :
    CP (A ++ [.g]) p ∨ CP (.g :: B) p ↔ CP (A ++ .g :: B) p := by
  rcases A with _ | ⟨a, A⟩
  · simp only [List.nil_append, CP_single, hp, false_or]
  rcases B with _ | ⟨b, B⟩
  · simp only [CP_single, hp, or_false]
  have hc : ((a :: A ++ [Kd.g]).head? = some .g ∧ (Kd.g :: b :: B).head? = some .g) ∨
      ((a :: A ++ [Kd.g]).getLast? = some .g ∧ (Kd.g :: b :: B).getLast? = some .g) := by
    have e3 : (a :: A ++ Kd.g :: b :: B).getLast? = (b :: B).getLast? := by
      rw [List.getLast?_append, List.getLast?_cons_cons]
      simp [List.getLast?_cons]
    rw [e3] at h
    rcases h with h | h
    · exact Or.inl ⟨by simpa using h, rfl⟩
    · exact Or.inr ⟨by rw [List.getLast?_append]; simp,
        by rw [List.getLast?_cons_cons]; exact h⟩
  have hJ := CP_J (a :: A ++ [.g]) (.g :: b :: B) (by simp) (by simp) hc p
  have e2 : (a :: A ++ [Kd.g]) ++ (Kd.g :: b :: B) = (a :: A) ++ .g :: .g :: b :: B := by simp
  rw [e2, CP_dup] at hJ
  rw [← hJ]
  simp [hp]

private theorem CP_gcons (t : List Kd) (ht : t ≠ []) (p : Kd × Kd) :
    CP (.g :: t) p ↔ (p.1 = .g ∧ t.head? = some p.2) ∨ p ∈ lp t ∨
      (t.getLast? = some p.1 ∧ p.2 = .g) := by
  rcases t with _ | ⟨y, t⟩
  · exact absurd rfl ht
  obtain ⟨p1, p2⟩ := p
  simp only [CP, lp, List.mem_cons, Prod.ext_iff, List.getLast?_cons_cons, List.head?_cons,
    Option.some.injEq]
  constructor
  · rintro ((⟨h1, h2⟩ | h) | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2.symm⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
  · rintro (⟨h1, h2⟩ | h | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl ⟨h1, h2.symm⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨h1, h2.symm⟩

private theorem CP_x_fst (x y : Kd) (Z : List Kd) (hx : x ∉ Z) :
    CP (x :: Z) (x, y) ↔ (Z ++ [x]).head? = some y := by
  rcases Z with _ | ⟨z, Z⟩
  · simp [CP, lp]
  · have h1 : (x, y) ∉ lp (z :: Z) := fun h => hx (lp_mem z Z _ h).1
    have h2 : (x :: z :: Z).getLast? ≠ some x := by
      rw [List.getLast?_cons_cons]
      intro h
      exact hx (List.mem_of_getLast? h)
    simp only [CP, lp, List.mem_cons, Prod.ext_iff, h1, or_false, List.cons_append,
      List.head?_cons, Option.some.injEq, true_and]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h.symm
      · exact absurd h h2
    · intro h
      exact Or.inl h.symm

private theorem CP_x_snd (x y : Kd) (Z : List Kd) (hx : x ∉ Z) :
    CP (x :: Z) (y, x) ↔ (x :: Z).getLast? = some y := by
  have h1 : (y, x) ∉ lp (x :: Z) := fun h => hx (lp_mem x Z _ h).2
  simp [CP, h1]

private theorem rot_to {x : Kd} {l : List Kd} (h : x ∈ l) : ∃ Z, l.IsRotated (x :: Z) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨t ++ s, by simpa using (List.isRotated_append (l := s) (l' := x :: t))⟩

private theorem kw_append (A B : List PkgLetter) : kw (A ++ B) = kw A ++ kw B :=
  List.filterMap_append

private theorem kw_rot {w w' : List PkgLetter} (h : w.IsRotated w') : (kw w).IsRotated (kw w') := by
  obtain ⟨A, B, rfl, rfl⟩ := rotated_split h
  rw [kw_append, kw_append]
  exact List.isRotated_append

/-- The kinds `Δ`, `Λ̃_o` of a word, without the resolvents. -/
private def bw (l : List Kd) : List Kd := l.filter (· != .g)

private theorem bw_rot {l l' : List Kd} (h : l.IsRotated l') : (bw l).IsRotated (bw l') := by
  obtain ⟨A, B, rfl, rfl⟩ := rotated_split h
  simp only [bw, List.filter_append]
  exact List.isRotated_append

private theorem CP_mem {l : List Kd} {p : Kd × Kd} (h : CP l p) : p.1 ∈ l ∧ p.2 ∈ l := by
  rcases h with h | ⟨h1, h2⟩
  · rcases l with _ | ⟨x, Z⟩
    · simp [lp] at h
    · have := lp_mem x Z p h
      exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩
  · exact ⟨List.mem_of_getLast? h1, List.mem_of_mem_head? h2⟩

/-- `Λ̃_o` occurs exactly once in the words of the expression. -/
private def UO (R : PkgExpr) (o : Fin 2) : Prop :=
  (R.loops.map fun w => w.count (.lw (.lamt o))).sum = 1

private theorem uo_of_wf (R : PkgExpr) (h : R.wf = true) (o : Fin 2) : UO R o := by
  unfold PkgExpr.wf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold UO
  rcases (by decide : ∀ o : Fin 2, o = 0 ∨ o = 1) o with rfl | rfl
  · exact h.1.1.1.1
  · exact h.1.1.1.2

private theorem uniq_word {x : PkgLetter} : ∀ {L : List (List PkgLetter)},
    (L.map fun w => w.count x).sum = 1 → ∀ {v w : List PkgLetter}, v ∈ L → x ∈ v → w ∈ L →
      x ∈ w → v = w ∧ v.count x = 1
  | [], _, _, _, hv, _, _, _ => absurd hv (List.not_mem_nil)
  | u :: L, h, v, w, hv, hxv, hw, hxw => by
      rw [List.map_cons, List.sum_cons] at h
      have hpos : ∀ z ∈ L, x ∈ z → 1 ≤ (L.map fun w => w.count x).sum := fun z hz hxz =>
        le_trans (List.count_pos_iff.2 hxz) (List.le_sum_of_mem (List.mem_map_of_mem hz))
      rcases List.mem_cons.1 hv with rfl | hv' <;> rcases List.mem_cons.1 hw with rfl | hw'
      · have := List.count_pos_iff.2 hxv
        exact ⟨rfl, by omega⟩
      · have := hpos w hw' hxw
        have := List.count_pos_iff.2 hxv
        omega
      · have := hpos v hv' hxv
        have := List.count_pos_iff.2 hxw
        omega
      · have := hpos v hv' hxv
        have h' : (L.map fun w => w.count x).sum = 1 := by omega
        exact uniq_word h' hv' hxv hw' hxw

/-- Some word of the list other than at the positions `s` has the property. -/
private def Oth (L : List (List PkgLetter)) (s : List ℕ) (Φ : List PkgLetter → Prop) : Prop :=
  ∃ i v, i ∉ s ∧ L[i]? = some v ∧ Φ v

private theorem ex_idx (L : List (List PkgLetter)) (Φ : List PkgLetter → Prop) :
    (∃ v ∈ L, Φ v) ↔ ∃ (i : ℕ) (v : List PkgLetter), L[i]? = some v ∧ Φ v := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
    exact ⟨i, v, hi, h⟩
  · rintro ⟨i, v, hi, h⟩
    exact ⟨v, List.mem_iff_getElem?.2 ⟨i, hi⟩, h⟩

private theorem ex_get (L : List (List PkgLetter)) (Φ : List PkgLetter → Prop) (ℓ : ℕ)
    (w : List PkgLetter) (h : L[ℓ]? = some w) : (∃ v ∈ L, Φ v) ↔ Φ w ∨ Oth L [ℓ] Φ := by
  rw [ex_idx]
  constructor
  · rintro ⟨i, v, hi, hv⟩
    by_cases hiℓ : i = ℓ
    · subst hiℓ
      rw [h] at hi
      cases hi
      exact Or.inl hv
    · exact Or.inr ⟨i, v, by simpa using hiℓ, hi, hv⟩
  · rintro (hv | ⟨i, v, -, hi, hv⟩)
    · exact ⟨ℓ, w, h, hv⟩
    · exact ⟨i, v, hi, hv⟩

private theorem ex_get2 (L : List (List PkgLetter)) (Φ : List PkgLetter → Prop) (ℓ j : ℕ)
    (w f : List PkgLetter) (h : L[ℓ]? = some w) (hf : L[j]? = some f) (hj : j ≠ ℓ) :
    (∃ v ∈ L, Φ v) ↔ Φ w ∨ Φ f ∨ Oth L [ℓ, j] Φ := by
  rw [ex_idx]
  constructor
  · rintro ⟨i, v, hi, hv⟩
    by_cases hiℓ : i = ℓ
    · subst hiℓ
      rw [h] at hi
      cases hi
      exact Or.inl hv
    · by_cases hij : i = j
      · subst hij
        rw [hf] at hi
        cases hi
        exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr ⟨i, v, by simp [hiℓ, hij], hi, hv⟩)
  · rintro (hv | hv | ⟨i, v, -, hi, hv⟩)
    · exact ⟨ℓ, w, h, hv⟩
    · exact ⟨j, f, hf, hv⟩
    · exact ⟨i, v, hi, hv⟩

private theorem ex_set (L : List (List PkgLetter)) (Φ : List PkgLetter → Prop) (ℓ : ℕ)
    (w N : List PkgLetter) (h : L[ℓ]? = some w) :
    (∃ v ∈ L.set ℓ N, Φ v) ↔ Φ N ∨ Oth L [ℓ] Φ := by
  have hl : ℓ < L.length := (List.getElem?_eq_some_iff.1 h).1
  rw [ex_idx]
  constructor
  · rintro ⟨i, v, hi, hv⟩
    rw [List.getElem?_set] at hi
    by_cases hiℓ : ℓ = i
    · subst hiℓ
      simp only [↓reduceIte, hl] at hi
      cases hi
      exact Or.inl hv
    · simp only [hiℓ, ↓reduceIte] at hi
      exact Or.inr ⟨i, v, by simpa [eq_comm] using hiℓ, hi, hv⟩
  · rintro (hv | ⟨i, v, hi', hi, hv⟩)
    · exact ⟨ℓ, N, by rw [List.getElem?_set_self hl], hv⟩
    · refine ⟨i, v, ?_, hv⟩
      rw [List.getElem?_set_ne (by simpa [eq_comm] using hi')]
      exact hi

private theorem ex_set_app (L : List (List PkgLetter)) (Φ : List PkgLetter → Prop) (ℓ : ℕ)
    (w N M : List PkgLetter) (h : L[ℓ]? = some w) :
    (∃ v ∈ L.set ℓ N ++ [M], Φ v) ↔ Φ N ∨ Φ M ∨ Oth L [ℓ] Φ := by
  have := ex_set L Φ ℓ w N h
  constructor
  · rintro ⟨v, hv, hΦ⟩
    rcases List.mem_append.1 hv with hv | hv
    · rcases this.1 ⟨v, hv, hΦ⟩ with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)
    · rw [List.mem_singleton.1 hv] at hΦ
      exact Or.inr (Or.inl hΦ)
  · rintro (h1 | h1 | h1)
    · obtain ⟨v, hv, hΦ⟩ := this.2 (Or.inl h1)
      exact ⟨v, List.mem_append_left _ hv, hΦ⟩
    · exact ⟨M, by simp, h1⟩
    · obtain ⟨v, hv, hΦ⟩ := this.2 (Or.inr h1)
      exact ⟨v, List.mem_append_left _ hv, hΦ⟩

private theorem ex_set_erase (L : List (List PkgLetter)) (Φ : List PkgLetter → Prop) (ℓ j : ℕ)
    (w N : List PkgLetter) (h : L[ℓ]? = some w) (hj : j ≠ ℓ) :
    (∃ v ∈ (L.set ℓ N).eraseIdx j, Φ v) ↔ Φ N ∨ Oth L [ℓ, j] Φ := by
  have hl : ℓ < L.length := (List.getElem?_eq_some_iff.1 h).1
  constructor
  · rintro ⟨v, hv, hΦ⟩
    obtain ⟨i, hij, hi⟩ := List.mem_eraseIdx_iff_getElem?.1 hv
    rw [List.getElem?_set] at hi
    by_cases hiℓ : ℓ = i
    · subst hiℓ
      simp only [↓reduceIte, hl] at hi
      cases hi
      exact Or.inl hΦ
    · simp only [hiℓ, ↓reduceIte] at hi
      exact Or.inr ⟨i, v, by simp [hij, Ne.symm hiℓ], hi, hΦ⟩
  · rintro (hΦ | ⟨i, v, hi', hi, hΦ⟩)
    · exact ⟨N, List.mem_eraseIdx_iff_getElem?.2 ⟨ℓ, Ne.symm hj, by
        rw [List.getElem?_set_self hl]⟩, hΦ⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi'
      refine ⟨v, List.mem_eraseIdx_iff_getElem?.2 ⟨i, hi'.2, ?_⟩, hΦ⟩
      rw [List.getElem?_set_ne (Ne.symm hi'.1)]
      exact hi

/-- Some word of the expression has the cyclically consecutive kinds `p`. -/
private def PS (R : PkgExpr) (p : Kd × Kd) : Prop := ∃ w ∈ R.loops, CP (kw w) p

private theorem mem_kw {y : Kd} {w : List PkgLetter} : y ∈ kw w ↔ ∃ x ∈ w, kd x = some y :=
  List.mem_filterMap

private theorem l_mem_kw (o : Fin 2) (w : List PkgLetter) :
    Kd.l o ∈ kw w ↔ PkgLetter.lw (.lamt o) ∈ w := by
  rw [mem_kw]
  constructor
  · rintro ⟨x, hx, h⟩
    match x, h with
    | .lw (.lamt o'), h =>
      simp only [kd, Option.some.injEq, Kd.l.injEq] at h
      subst h
      exact hx
  · intro h
    exact ⟨_, h, rfl⟩

private theorem count_kw_l (o : Fin 2) : ∀ w : List PkgLetter,
    (kw w).count (.l o) = w.count (.lw (.lamt o))
  | [] => rfl
  | x :: w => by
      have ih := count_kw_l o w
      match x with
      | .lw (.res a) => simpa [kw, kd, List.filterMap_cons, List.count_cons] using ih
      | .lw (.det a) => simpa [kw, kd, List.filterMap_cons, List.count_cons] using ih
      | .lw (.proj y) => simpa [kw, kd, List.filterMap_cons, List.count_cons] using ih
      | .lw (.lamt o') => simpa [kw, kd, List.filterMap_cons, List.count_cons] using ih
      | .ent u v => simpa [kw, kd, List.filterMap_cons, List.count_cons] using ih

/-- The unique word with `Λ̃_o`: the kinds rotated to start at `Λ̃_o`. -/
private theorem word_rot (R : PkgExpr) (o : Fin 2) (hU : UO R o) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : PkgLetter.lw (.lamt o) ∈ w) :
    ∃ Z, (kw w).IsRotated (.l o :: Z) ∧ Kd.l o ∉ Z := by
  have hc := (uniq_word hU hw ho hw ho).2
  obtain ⟨Z, hZ⟩ := rot_to ((l_mem_kw o w).2 ho)
  refine ⟨Z, hZ, fun hm => ?_⟩
  have h1 := hZ.perm.count_eq (Kd.l o)
  rw [count_kw_l, hc, List.count_cons_self] at h1
  have := List.count_pos_iff.2 hm
  omega

/-- A pair with `Λ̃_o` lies in the unique word with `Λ̃_o`. -/
private theorem PS_word (R : PkgExpr) (o : Fin 2) (hU : UO R o) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : PkgLetter.lw (.lamt o) ∈ w) (p : Kd × Kd)
    (hp : p.1 = .l o ∨ p.2 = .l o) : PS R p ↔ CP (kw w) p := by
  constructor
  · rintro ⟨v, hv, h⟩
    have hm := CP_mem h
    have hov : PkgLetter.lw (.lamt o) ∈ v := by
      rw [← l_mem_kw]
      rcases hp with hp | hp
      · rw [← hp]; exact hm.1
      · rw [← hp]; exact hm.2
    rw [← (uniq_word hU hv hov hw ho).1]
    exact h
  · intro h
    exact ⟨w, hw, h⟩

/-- The search of the rules continues past the letter: it is not a `Δ` and not a `Λ̃`. -/
private def pP : Option PkgLetter → Bool
  | some (.ent _ _) => false
  | some (.lw (.lamt _)) => false
  | _ => true

/-- The letter is a resolvent. -/
private def pQ : Option PkgLetter → Bool
  | some (.lw (.res _)) => true
  | _ => false

private theorem tw_head : ∀ Z : List PkgLetter,
    (∃ o ∈ (Z.map some).takeWhile pP, pQ o = true) ↔ (kw Z).head? = some .g
  | [] => by simp [kw]
  | x :: Z => by
      have ih := tw_head Z
      match x with
      | .lw (.res a) =>
        exact iff_of_true ⟨some (.lw (.res a)), by simp [List.takeWhile_cons, pP], rfl⟩
          (by simp [kw, kd])
      | .lw (.det a) => simpa [List.takeWhile_cons, pP, pQ, kw, kd, List.filterMap_cons] using ih
      | .lw (.proj y) => simpa [List.takeWhile_cons, pP, pQ, kw, kd, List.filterMap_cons] using ih
      | .lw (.lamt o) => simp [pP, kw, kd]
      | .ent u v => simp [pP, kw, kd]

private theorem idx_map (w : List PkgLetter) (i : ℕ) (x : PkgLetter) (Z : List PkgLetter)
    (hrot : w.rotate i = x :: Z) (right : Bool) :
    ((List.range (w.length - 1)).map fun t =>
      if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length).map
        (fun r => w[r]?) = (if right then Z else Z.reverse).map some := by
  have hlen : w.length = Z.length + 1 := by
    rw [← List.length_rotate w i, hrot]
    rfl
  apply List.ext_getElem
  · cases right <;> simp [hlen]
  · intro t h1 h2
    simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp]
    have ht : t < Z.length := by simp [hlen] at h1; omega
    cases right
    · simp only [Bool.false_eq_true, ↓reduceIte, List.getElem_reverse]
      have := List.getElem?_rotate (l := w) (n := i) (m := Z.length - t) (by omega)
      rw [hrot] at this
      have e : (Z.length - t + i) % w.length = (i + w.length - 1 - t) % w.length := by
        congr 1; omega
      rw [← e, ← this]
      have e2 : Z.length - t = (Z.length - 1 - t) + 1 := by omega
      rw [e2, List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega)]
    · simp only [↓reduceIte]
      have := List.getElem?_rotate (l := w) (n := i) (m := t + 1) (by omega)
      rw [hrot] at this
      have e : (t + 1 + i) % w.length = (i + 1 + t) % w.length := by congr 1; omega
      rw [← e, ← this, List.getElem?_cons_succ, List.getElem?_eq_getElem ht]

private theorem tw_map (l : List ℕ) (f : ℕ → Option PkgLetter) :
    (∃ r ∈ l.takeWhile (pP ∘ f), (pQ ∘ f) r = true) ↔
      ∃ o ∈ (l.map f).takeWhile pP, pQ o = true := by
  rw [List.takeWhile_map]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨f r, List.mem_map_of_mem hr, h⟩
  · rintro ⟨o, ho, h⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ho
    exact ⟨r, hr, h⟩

private theorem seek_gen (w : List PkgLetter) (i : ℕ) (x : PkgLetter) (Z : List PkgLetter)
    (hrot : w.rotate i = x :: Z) (right : Bool) (P Q : ℕ → Bool)
    (hP : ∀ r, P r = pP w[r]?) (hQ : ∀ r, Q r = pQ w[r]?) :
    (∃ r ∈ ((List.range (w.length - 1)).map fun t =>
        if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length).takeWhile P,
      Q r = true) ↔ (if right then (kw Z).head? else (kw Z).getLast?) = some .g := by
  have eP : P = pP ∘ (fun r => w[r]?) := funext hP
  have eQ : Q = pQ ∘ (fun r => w[r]?) := funext hQ
  subst eP eQ
  rw [tw_map, idx_map w i x Z hrot right]
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [tw_head, kw, List.filterMap_reverse, List.head?_reverse]
    rfl
  · simp only [↓reduceIte]
    exact tw_head Z

private theorem rot_idx {α : Type*} [DecidableEq α] {x : α} {w : List α} (h : x ∈ w) :
    ∃ Z, w.rotate (w.idxOf x) = x :: Z := by
  have hlt : w.idxOf x < w.length := List.idxOf_lt_length_iff.2 h
  refine ⟨w.drop (w.idxOf x + 1) ++ w.take (w.idxOf x), ?_⟩
  rw [List.rotate_eq_drop_append_take hlt.le, List.drop_eq_getElem_cons hlt, List.getElem_idxOf]
  rfl

private theorem find_lam (R : PkgExpr) (o : Fin 2) (hU : UO R o) : ∃ w,
    R.loops.find? (fun w => w.contains (.lw (.lamt o))) = some w ∧ w ∈ R.loops ∧
      PkgLetter.lw (.lamt o) ∈ w := by
  rcases hf : R.loops.find? (fun w => w.contains (.lw (.lamt o))) with _ | w
  · exfalso
    have h2 := List.find?_eq_none.1 hf
    have h3 : (R.loops.map fun w => w.count (.lw (.lamt o))).sum = 0 := by
      rw [List.sum_eq_zero_iff]
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      rw [List.count_eq_zero]
      intro hmem
      exact h2 w hw (by simpa using hmem)
    unfold UO at hU
    omega
  · exact ⟨w, hf, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- Right side `(o, true)` / left side `(o, false)` of `Λ̃_o` has a resolvent. -/
private def SB (R : PkgExpr) (o : Fin 2) (right : Bool) : Prop :=
  if right then PS R (.l o, .g) else PS R (.g, .l o)

private theorem side_bit (R : PkgExpr) (o : Fin 2) (hU : UO R o) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : PkgLetter.lw (.lamt o) ∈ w) (i : ℕ) (Z : List PkgLetter)
    (hrot : w.rotate i = .lw (.lamt o) :: Z) (right : Bool) :
    (if right then (kw Z).head? else (kw Z).getLast?) = some .g ↔ SB R o right := by
  have hc := (uniq_word hU hw ho hw ho).2
  have hZ : Kd.l o ∉ kw Z := by
    rw [l_mem_kw]
    intro hm
    have h1 := (List.rotate_perm w i).count_eq (PkgLetter.lw (.lamt o))
    rw [hrot, hc, List.count_cons_self] at h1
    have := List.count_pos_iff.2 hm
    omega
  have hkr : (kw w).IsRotated (.l o :: kw Z) := by
    have := kw_rot (List.IsRotated.forall w i).symm
    rw [hrot] at this
    exact this
  cases right
  · simp only [SB, Bool.false_eq_true, ↓reduceIte]
    rw [PS_word R o hU w hw ho _ (Or.inr rfl), CP_rot hkr, CP_x_snd _ _ _ hZ]
    rcases h : kw Z with _ | ⟨z, Z'⟩
    · simp
    · simp [List.getLast?_cons]
  · simp only [SB, ↓reduceIte]
    rw [PS_word R o hU w hw ho _ (Or.inl rfl), CP_rot hkr, CP_x_fst _ _ _ hZ]
    rcases h : kw Z with _ | ⟨z, Z'⟩
    · simp
    · simp

/-- `1 ≤ lamSide` exactly when the side has a resolvent. -/
private theorem lamSide_pos (R : PkgExpr) (o : Fin 2) (hU : UO R o) (right : Bool) :
    1 ≤ R.lamSide o right ↔ SB R o right := by
  obtain ⟨w, hf, hw, ho⟩ := find_lam R o hU
  obtain ⟨Z, hZ⟩ := rot_idx ho
  rw [← side_bit R o hU w hw ho _ Z hZ right]
  unfold PkgExpr.lamSide
  rw [hf]
  dsimp only
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, List.countP_pos_iff]
  exact seek_gen w _ _ Z hZ right _ _ (fun r => by
      cases w[r]? with
      | none => rfl
      | some x => rcases x with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> rfl)
    (fun r => by
      cases w[r]? with
      | none => rfl
      | some x => rcases x with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> rfl)

/-- The search of the rules from `Λ̃_o` succeeds exactly when the side has a resolvent. -/
private theorem seek_bit (R : PkgExpr) (o : Fin 2) (hU : UO R o) (w : List PkgLetter)
    (hf : R.loops.find? (fun w => w.contains (.lw (.lamt o))) = some w) (right : Bool) :
    (pkgSeek w (w.idxOf (.lw (.lamt o))) right).isSome = true ↔ SB R o right := by
  have hw := List.mem_of_find?_eq_some hf
  have ho : PkgLetter.lw (.lamt o) ∈ w := by simpa using List.find?_some hf
  obtain ⟨Z, hZ⟩ := rot_idx ho
  rw [← side_bit R o hU w hw ho _ Z hZ right]
  unfold pkgSeek
  rw [List.find?_isSome]
  exact seek_gen w _ _ Z hZ right _ _ (fun r => by
      cases w[r]? with
      | none => rfl
      | some x => rcases x with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> rfl)
    (fun r => by
      cases w[r]? with
      | none => rfl
      | some x => rcases x with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> rfl)

private theorem tw_find (P Q : ℕ → Bool) :
    ∀ (l : List ℕ) (r : ℕ), (l.takeWhile P).find? Q = some r →
    ∃ k, ∃ hk : k < l.length, l[k] = r ∧ Q r = true ∧
      ∀ j (hj : j < k), P (l[j]'(Nat.lt_trans hj hk)) = true ∧
        Q (l[j]'(Nat.lt_trans hj hk)) = false
  | [], r, h => by simp at h
  | y :: l, r, h => by
      rw [List.takeWhile_cons] at h
      by_cases hP : P y = true
      · simp only [hP, ↓reduceIte, List.find?_cons] at h
        cases hQ : Q y
        · rw [hQ] at h
          obtain ⟨k, hk, hkr, hQr, hpre⟩ := tw_find P Q l r h
          refine ⟨k + 1, by simp; omega, by simpa using hkr, hQr, ?_⟩
          intro j hj
          cases j with
          | zero => exact ⟨hP, hQ⟩
          | succ j => simpa using hpre j (by omega)
        · rw [hQ] at h
          cases h
          exact ⟨0, by simp, rfl, hQ, fun j hj => absurd hj (by omega)⟩
      · simp [hP] at h

private theorem rot_split (x y : PkgLetter) (A B : List PkgLetter) :
    (x :: (A ++ y :: B)).rotate (1 + A.length) = y :: (B ++ x :: A) := by
  have h := List.rotate_append_length_eq (x :: A) (y :: B)
  have e : (x :: A).length = 1 + A.length := by simp; omega
  rw [e] at h
  simpa using h

private theorem seek_pos_gen (w : List PkgLetter) (i r : ℕ) (x : PkgLetter) (Z : List PkgLetter)
    (hrot : w.rotate i = x :: Z) (right : Bool) (P Q : ℕ → Bool)
    (hP : ∀ r, P r = pP w[r]?) (hQ : ∀ r, Q r = pQ w[r]?)
    (h : (((List.range (w.length - 1)).map fun t =>
        if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length).takeWhile
          P).find? Q = some r) :
    ∃ (A B : List PkgLetter) (b : Fin 2), kw A = [] ∧
      w.rotate r = .lw (.res b) :: (if right then B ++ x :: A else A ++ x :: B) := by
  have hlen : w.length = Z.length + 1 := by rw [← List.length_rotate w i, hrot]; rfl
  obtain ⟨k, hk, hkr, hQr, hpre⟩ := tw_find _ _ _ r h
  have hmap := idx_map w i x Z hrot right
  have hZ'len : (if right then Z else Z.reverse).length = Z.length := by split <;> simp
  have hkZ : k < Z.length := by simp at hk; omega
  have hval : ∀ j (hj : j < Z.length),
      w[(if right then (i + 1 + j) % w.length else (i + w.length - 1 - j) % w.length)]? =
        some ((if right then Z else Z.reverse)[j]'(by omega)) := by
    intro j hj
    have := congrArg (fun L => L[j]?) hmap
    simp only [List.map_map, List.getElem?_map,
      List.getElem?_range (show j < w.length - 1 by omega),
      Option.map_some, Function.comp] at this
    have e : (if right then Z else Z.reverse)[j]? =
        some ((if right then Z else Z.reverse)[j]'(by rw [hZ'len]; exact hj)) :=
      List.getElem?_eq_getElem _
    rw [e, Option.map_some] at this
    exact Option.some.inj this
  have hidx : ∀ j (hj : j < ((List.range (w.length - 1)).map fun t =>
      if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length).length),
      ((List.range (w.length - 1)).map fun t =>
        if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length)[j] =
      (if right then (i + 1 + j) % w.length else (i + w.length - 1 - j) % w.length) := by
    intro j hj
    simp
  set Z' := if right then Z else Z.reverse with hZ'
  have hneu : ∀ j (hj : j < k), kd (Z'[j]'(by omega)) = none := by
    intro j hj
    obtain ⟨h1, h2⟩ := hpre j hj
    rw [hP, hidx, hval j (by omega)] at h1
    rw [hQ, hidx, hval j (by omega)] at h2
    revert h1 h2
    rcases Z'[j]'(by omega) with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> simp [pP, pQ, kd]
  obtain ⟨b, hb⟩ : ∃ b, Z'[k]'(by omega) = .lw (.res b) := by
    rw [← hkr, hQ, hidx, hval k hkZ] at hQr
    revert hQr
    rcases Z'[k]'(by omega) with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> simp [pQ]
  have hsplit : Z' = Z'.take k ++ .lw (.res b) :: Z'.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k Z', List.drop_eq_getElem_cons (by omega), hb]
  have hA : kw (Z'.take k) = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hz
    rw [List.getElem_take]
    exact hneu j (by simp at hj; omega)
  have hr : r = (if right then (i + 1 + k) % w.length else (i + w.length - 1 - k) % w.length) := by
    rw [← hkr, hidx]
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at hZ' hr ⊢
    refine ⟨(Z'.take k).reverse, (Z'.drop (k + 1)).reverse, b, ?_, ?_⟩
    · rw [kw, List.filterMap_reverse]
      rw [kw] at hA
      rw [hA]
      rfl
    · have hZ : Z = (Z'.drop (k + 1)).reverse ++ .lw (.res b) :: (Z'.take k).reverse := by
        have := congrArg List.reverse hsplit
        rw [hZ', List.reverse_reverse] at this
        rw [this]
        simp [hZ']
      have hl : ((Z'.drop (k + 1)).reverse).length = Z.length - 1 - k := by
        simp [hZ']
        omega
      rw [hr, List.rotate_mod]
      have e : i + w.length - 1 - k = i + (1 + ((Z'.drop (k + 1)).reverse).length) := by
        rw [hl]; omega
      rw [e, ← List.rotate_rotate, hrot]
      conv_lhs => rw [hZ]
      exact rot_split _ _ _ _
  · simp only [↓reduceIte] at hZ' hr ⊢
    refine ⟨Z'.take k, Z'.drop (k + 1), b, hA, ?_⟩
    rw [hr, List.rotate_mod]
    have hl : (Z'.take k).length = k := by simp [hZ']; omega
    have e : i + 1 + k = i + (1 + (Z'.take k).length) := by rw [hl]; omega
    rw [e, ← List.rotate_rotate, hrot]
    have hZ : Z = Z'.take k ++ .lw (.res b) :: Z'.drop (k + 1) := by
      calc Z = Z' := hZ'.symm
        _ = _ := hsplit
    conv_lhs => rw [hZ]
    exact rot_split _ _ _ _

private theorem seek_pos (w : List PkgLetter) (i r : ℕ) (x : PkgLetter) (Z : List PkgLetter)
    (hrot : w.rotate i = x :: Z) (right : Bool) (h : pkgSeek w i right = some r) :
    ∃ (A B : List PkgLetter) (b : Fin 2), kw A = [] ∧
      w.rotate r = .lw (.res b) :: (if right then B ++ x :: A else A ++ x :: B) := by
  unfold pkgSeek at h
  exact seek_pos_gen w i r x Z hrot right _ _ (fun r => by
      cases w[r]? with
      | none => rfl
      | some x => rcases x with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> rfl)
    (fun r => by
      cases w[r]? with
      | none => rfl
      | some x => rcases x with ⟨_ | _ | _ | _⟩ | ⟨_, _⟩ <;> rfl) h

private theorem d_mem_iff (w : List PkgLetter) (p : PkgLetter → Bool)
    (hp1 : ∀ u v, p (.ent u v) = true) (hp2 : ∀ x, p (.lw x) = false) :
    w.any p = true ↔ Kd.d ∈ kw w := by
  rw [List.any_eq_true, mem_kw]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x with
    | lw y => rw [hp2] at h; cases h
    | ent u v => exact ⟨_, hx, rfl⟩
  · rintro ⟨x, hx, h⟩
    cases x with
    | lw y => rcases y <;> simp [kd] at h
    | ent u v => exact ⟨_, hx, hp1 u v⟩

private theorem d_of_any (w : List PkgLetter) (p : PkgLetter → Bool)
    (hp1 : ∀ u v, p (.ent u v) = true) (hp2 : ∀ x, p (.lw x) = false) (h : w.any p = true) :
    Kd.d ∈ kw w := (d_mem_iff w p hp1 hp2).1 h

private theorem nd_of_any (w : List PkgLetter) (p : PkgLetter → Bool)
    (hp1 : ∀ u v, p (.ent u v) = true) (hp2 : ∀ x, p (.lw x) = false) (h : w.any p = false) :
    Kd.d ∉ kw w := fun hd => by rw [(d_mem_iff w p hp1 hp2).2 hd] at h; cases h

private theorem tw_l1 (p : PkgLetter → Bool) (hp1 : ∀ u v, p (.ent u v) = false)
    (hp2 : ∀ x, p (.lw x) = true) : ∀ Z : List PkgLetter, PkgLetter.lw (.lamt 0) ∉ Z →
    ((Z.takeWhile p).contains (.lw (.lamt 1)) = true ↔ (bw (kw Z)).head? = some (.l 1))
  | [], _ => by simp [kw, bw]
  | x :: Z, hZ => by
      have ih := tw_l1 p hp1 hp2 Z (fun h => hZ (List.mem_cons_of_mem _ h))
      match x with
      | .lw (.res a) =>
        rw [List.takeWhile_cons, hp2]
        simpa [kw, kd, bw] using ih
      | .lw (.det a) =>
        rw [List.takeWhile_cons, hp2]
        simpa [kw, kd, bw, List.filterMap_cons] using ih
      | .lw (.proj y) =>
        rw [List.takeWhile_cons, hp2]
        simpa [kw, kd, bw, List.filterMap_cons] using ih
      | .lw (.lamt o) =>
        rcases (by decide : ∀ o : Fin 2, o = 0 ∨ o = 1) o with rfl | rfl
        · exact absurd List.mem_cons_self hZ
        · rw [List.takeWhile_cons, hp2]
          simp [kw, kd, bw]
      | .ent u v =>
        rw [List.takeWhile_cons, hp1]
        simp [kw, kd, bw]

private theorem bw_cons_l (o : Fin 2) (l : List Kd) : bw (.l o :: l) = .l o :: bw l := by
  simp [bw]

private theorem t3_iff (R : PkgExpr) (hU0 : UO R 0) (w : List PkgLetter) (hw : w ∈ R.loops)
    (p : PkgLetter → Bool) (hp1 : ∀ u v, p (.ent u v) = false) (hp2 : ∀ x, p (.lw x) = true) :
    (w.contains (.lw (.lamt 0)) && (((w.rotate (w.idxOf (.lw (.lamt 0)))).drop 1).takeWhile
      p).contains (.lw (.lamt 1))) = true ↔ CP (bw (kw w)) (.l 0, .l 1) := by
  rw [Bool.and_eq_true]
  have key : ∀ (h0 : PkgLetter.lw (.lamt 0) ∈ w), ((((w.rotate (w.idxOf (.lw (.lamt 0)))).drop
      1).takeWhile p).contains (.lw (.lamt 1)) = true ↔ CP (bw (kw w)) (.l 0, .l 1)) := by
    intro h0
    obtain ⟨Z, hZ⟩ := rot_idx h0
    have hc := (uniq_word hU0 hw h0 hw h0).2
    have hZ0 : PkgLetter.lw (.lamt 0) ∉ Z := by
      intro hm
      have h1 := (List.rotate_perm w (w.idxOf (.lw (.lamt 0)))).count_eq (PkgLetter.lw (.lamt 0))
      rw [hZ, hc, List.count_cons_self] at h1
      have := List.count_pos_iff.2 hm
      omega
    have hb : Kd.l 0 ∉ bw (kw Z) := by
      intro hm
      exact hZ0 ((l_mem_kw 0 Z).1 (List.mem_filter.1 hm).1)
    have hrot : (bw (kw w)).IsRotated (.l 0 :: bw (kw Z)) := by
      have := bw_rot (kw_rot (List.IsRotated.forall w (w.idxOf (.lw (.lamt 0)))).symm)
      rw [hZ] at this
      exact this
    rw [hZ, List.drop_one, List.tail_cons, tw_l1 p hp1 hp2 Z hZ0, CP_rot hrot,
      CP_x_fst _ _ _ hb]
    rcases bw (kw Z) with _ | ⟨y, l⟩
    · simp
    · simp
  constructor
  · rintro ⟨h0, h1⟩
    have h0' : PkgLetter.lw (.lamt 0) ∈ w := by simpa using h0
    exact (key h0').1 h1
  · intro h
    have h0' : PkgLetter.lw (.lamt 0) ∈ w := by
      have := (CP_mem h).1
      exact (l_mem_kw 0 w).1 (List.mem_filter.1 this).1
    exact ⟨by simpa using h0', (key h0').2 h⟩

/-- A property of the unique word with `Λ̃₂`. -/
private theorem ex_l1 (R : PkgExpr) (hU1 : UO R 1) (w₂ : List PkgLetter) (hw₂ : w₂ ∈ R.loops)
    (h₂ : PkgLetter.lw (.lamt 1) ∈ w₂) (Φ : List PkgLetter → Prop) :
    (∃ w ∈ R.loops, Kd.l 1 ∈ kw w ∧ Φ w) ↔ Φ w₂ := by
  constructor
  · rintro ⟨w, hw, h1, h⟩
    rwa [(uniq_word hU1 hw ((l_mem_kw 1 w).1 h1) hw₂ h₂).1] at h
  · intro h
    exact ⟨w₂, hw₂, (l_mem_kw 1 w₂).2 h₂, h⟩

/-- The Type of (5.79)–(5.81) through the kinds: Type II has `Λ̃₂` in a word without `Δ`,
Type III has `Λ̃₁` followed by `Λ̃₂` up to resolvents in a word with `Δ`. -/
private theorem ptype_cases (R : PkgExpr) (hU0 : UO R 0) (hU1 : UO R 1) :
    (R.ptype = 2 ↔ ∃ w ∈ R.loops, Kd.l 1 ∈ kw w ∧ Kd.d ∉ kw w) ∧
    (R.ptype = 3 ↔ ∃ w ∈ R.loops, Kd.d ∈ kw w ∧ CP (bw (kw w)) (.l 0, .l 1)) ∧
    (R.ptype = 1 ∨ R.ptype = 2 ∨ R.ptype = 3) := by
  obtain ⟨w₂, hf, hw₂, h₂⟩ := find_lam R 1 hU1
  have hex2 := ex_l1 R hU1 w₂ hw₂ h₂ (fun w => Kd.d ∉ kw w)
  have hex3 : (∃ w ∈ R.loops, Kd.d ∈ kw w ∧ CP (bw (kw w)) (.l 0, .l 1)) ↔
      Kd.d ∈ kw w₂ ∧ CP (bw (kw w₂)) (.l 0, .l 1) := by
    rw [← ex_l1 R hU1 w₂ hw₂ h₂ (fun w => Kd.d ∈ kw w ∧ CP (bw (kw w)) (.l 0, .l 1))]
    constructor
    · rintro ⟨w, hw, h1, h2⟩
      exact ⟨w, hw, (List.mem_filter.1 (CP_mem h2).2).1, h1, h2⟩
    · rintro ⟨w, hw, -, h⟩
      exact ⟨w, hw, h⟩
  unfold PkgExpr.ptype
  rw [hf]
  dsimp only
  split_ifs with hA hB
  · rw [Bool.not_eq_true'] at hA
    have hd : Kd.d ∉ kw w₂ := nd_of_any w₂ _ (by intros; rfl) (by intro x; cases x <;> rfl) hA
    exact ⟨iff_of_true rfl (hex2.2 hd), iff_of_false (by decide) (fun h => hd (hex3.1 h).1),
      Or.inr (Or.inl rfl)⟩
  · rw [Bool.not_eq_true', Bool.not_eq_false] at hA
    have hd : Kd.d ∈ kw w₂ := d_of_any w₂ _ (by intros; rfl) (by intro x; cases x <;> rfl) hA
    have hc := (t3_iff R hU0 w₂ hw₂ _ (by intros; rfl) (by intro x; cases x <;> rfl)).1 hB
    exact ⟨iff_of_false (by decide) (fun h => (hex2.1 h) hd), iff_of_true rfl (hex3.2 ⟨hd, hc⟩),
      Or.inr (Or.inr rfl)⟩
  · rw [Bool.not_eq_true', Bool.not_eq_false] at hA
    have hd : Kd.d ∈ kw w₂ := d_of_any w₂ _ (by intros; rfl) (by intro x; cases x <;> rfl) hA
    have hc : ¬ CP (bw (kw w₂)) (.l 0, .l 1) := fun h =>
      hB ((t3_iff R hU0 w₂ hw₂ _ (by intros; rfl) (by intro x; cases x <;> rfl)).2 h)
    exact ⟨iff_of_false (by decide) (fun h => (hex2.1 h) hd),
      iff_of_false (by decide) (fun h => hc (hex3.1 h).2), Or.inl rfl⟩

private theorem focus_rule (S : PkgExpr) (hU0 : UO S 0) (hU1 : UO S 1) (ℓ r : ℕ) (right : Bool)
    (hf : S.ffocus = some (ℓ, r, right)) :
    ∃ (o : Fin 2) (w : List PkgLetter), S.loops[ℓ]? = some w ∧ w ∈ S.loops ∧
      PkgLetter.lw (.lamt o) ∈ w ∧ pkgSeek w (w.idxOf (.lw (.lamt o))) right = some r ∧
      (S.ptype ≠ 2 → (o = 1 ∧ right = true) ∨ (o = 0 ∧ right = true ∧ ¬ SB S 1 true) ∨
        (o = 1 ∧ right = false ∧ ¬ SB S 1 true ∧ ¬ SB S 0 true)) ∧
      (S.ptype = 2 → (o = 1 ∧ right = false) ∨ (o = 0 ∧ right = true ∧ ¬ SB S 1 false)) := by
  obtain ⟨w₂, hf₂, hw₂, h₂⟩ := find_lam S 1 hU1
  obtain ⟨w₁, hf₁, hw₁, h₁⟩ := find_lam S 0 hU0
  have g₂ : S.loops[S.loops.findIdx fun w => w.contains (.lw (.lamt 1))]? = some w₂ := by
    rw [← List.find?_eq_getElem?_findIdx]
    exact hf₂
  have g₁ : S.loops[S.loops.findIdx fun w => w.contains (.lw (.lamt 0))]? = some w₁ := by
    rw [← List.find?_eq_getElem?_findIdx]
    exact hf₁
  have hpt : S.ptype = 2 ↔ Kd.d ∉ kw w₂ := by
    rw [(ptype_cases S hU0 hU1).1]
    exact ex_l1 S hU1 w₂ hw₂ h₂ (fun w => Kd.d ∉ kw w)
  have nb : ∀ (o : Fin 2) (w : List PkgLetter),
      S.loops.find? (fun w => w.contains (.lw (.lamt o))) = some w → UO S o → ∀ right,
      pkgSeek w (w.idxOf (.lw (.lamt o))) right = none → ¬ SB S o right := by
    intro o w hf hU right hn hs
    have := (seek_bit S o hU w hf right).2 hs
    rw [hn] at this
    cases this
  have inj : ∀ {ℓ' r' : ℕ} {s' : Bool}, some (ℓ', r', s') = some (ℓ, r, right) →
      ℓ' = ℓ ∧ r' = r ∧ s' = right := by
    intro ℓ' r' s' h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h
  unfold PkgExpr.ffocus at hf
  dsimp only at hf
  rw [g₂, g₁] at hf
  dsimp only at hf
  split at hf
  · rename_i hA
    have hd : Kd.d ∈ kw w₂ := d_of_any w₂ _ (by intros; rfl) (by intro x; cases x <;> rfl) hA
    have hn2 : S.ptype ≠ 2 := fun h => (hpt.1 h) hd
    split at hf
    · rename_i r' hr'
      obtain ⟨rfl, rfl, rfl⟩ := inj hf
      exact ⟨1, w₂, g₂, hw₂, h₂, hr', fun _ => Or.inl ⟨rfl, rfl⟩, fun h => absurd h hn2⟩
    · rename_i hr2
      have nb1 := nb 1 w₂ hf₂ hU1 true hr2
      split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := inj hf
        exact ⟨0, w₁, g₁, hw₁, h₁, hr', fun _ => Or.inr (Or.inl ⟨rfl, rfl, nb1⟩),
          fun h => absurd h hn2⟩
      · rename_i hr1
        have nb0 := nb 0 w₁ hf₁ hU0 true hr1
        split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := inj hf
          exact ⟨1, w₂, g₂, hw₂, h₂, hr', fun _ => Or.inr (Or.inr ⟨rfl, rfl, nb1, nb0⟩),
            fun h => absurd h hn2⟩
        · simp at hf
  · rename_i hA
    rw [Bool.not_eq_true] at hA
    have hd : Kd.d ∉ kw w₂ := nd_of_any w₂ _ (by intros; rfl) (by intro x; cases x <;> rfl) hA
    have h2 : S.ptype = 2 := hpt.2 hd
    split at hf
    · rename_i r' hr'
      obtain ⟨rfl, rfl, rfl⟩ := inj hf
      exact ⟨1, w₂, g₂, hw₂, h₂, hr', fun h => absurd h2 h, fun _ => Or.inl ⟨rfl, rfl⟩⟩
    · rename_i hr2
      have nb1 := nb 1 w₂ hf₂ hU1 false hr2
      split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := inj hf
        exact ⟨0, w₁, g₁, hw₁, h₁, hr', fun h => absurd h2 h,
          fun _ => Or.inr ⟨rfl, rfl, nb1⟩⟩
      · simp at hf


private theorem fterms_data (P R' : PkgExpr) (o : PkgOp) (h : (o, R') ∈ P.fterms) :
    ∃ (ℓ r : ℕ) (right : Bool) (w : List PkgLetter) (a : Fin 2) (tl : List PkgLetter),
      P.ffocus = some (ℓ, r, right) ∧ P.loops[ℓ]? = some w ∧ w.rotate r = .lw (.res a) :: tl ∧
      ((o = PkgOp.frep ∧ R'.loops = P.loops.set ℓ (.lw (.det a) :: tl)) ∨
       (o ≠ PkgOp.frep ∧
       (R'.loops = P.loops.set ℓ (if right then .lw (.proj P.nb) :: invW right a tl
         else invW right a tl ++ [.lw (.proj P.nb)]) ∨
       (∃ (q : ℕ) (b : Fin 2), (invW right a tl)[q]? = some (.lw (.res b)) ∧
         R'.loops = P.loops.set ℓ ((invW right a tl).take (q + 1) ++ [.lw (.proj P.nb)]) ++
           [.lw (.proj P.nb) :: (invW right a tl).drop q]) ∨
       (∃ (b : Fin 2) (y : ℕ), R'.loops = P.loops.set ℓ (invW right a tl ++
         [.lw (.proj P.nb), .lw (.res b), .lw (.proj y), .lw (.res b), .lw (.proj P.nb)])) ∨
       (∃ (j : ℕ) (f F : List PkgLetter) (q : ℕ) (b : Fin 2), j ≠ ℓ ∧ P.loops[j]? = some f ∧
         f.rotate q = .lw (.res b) :: F ∧
         R'.loops = (P.loops.set ℓ (invW right a tl ++ [.lw (.proj P.nb)] ++ f.rotate q ++
           [.lw (.res b), .lw (.proj P.nb)])).eraseIdx j)))) := by
  unfold PkgExpr.fterms at h
  split at h
  · simp at h
  · rename_i ℓ r right hf
    split at h
    · simp at h
    · rename_i w hw
      split at h
      · rename_i a tl hrot
        dsimp only at h
        have hWdef : (if right = true then PkgLetter.lw (.res a) :: tl ++ [PkgLetter.lw (.det a)]
            else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)]) = invW right a tl := rfl
        rw [hWdef] at h
        refine ⟨ℓ, r, right, w, a, tl, hf, hw, hrot, ?_⟩
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with h | h
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                exact Or.inl ⟨rfl, rfl⟩
              · rcases List.mem_cons.1 h with h | h
                · obtain ⟨hop, rfl⟩ := Prod.mk.inj h
                  refine Or.inr ⟨?_, Or.inl rfl⟩
                  rw [hop]
                  split <;> decide
                · simp at h
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 h
              split at hq
              · simp at hq
              · split at hq
                · rename_i b hqb
                  obtain ⟨hop, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  refine Or.inr ⟨?_, Or.inr (Or.inl ⟨q, b, hqb, rfl⟩)⟩
                  rw [← hop]
                  split_ifs <;> decide
                · simp at hq
          · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
            split at hj
            · rename_i b y hjb
              obtain ⟨hop, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
              refine Or.inr ⟨?_, Or.inr (Or.inr (Or.inl ⟨b, y, rfl⟩))⟩
              rw [← hop]
              split_ifs <;> decide
            · simp at hj
        · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
          split at hj
          · simp at hj
          · rename_i hjℓ
            split at hj
            · simp at hj
            · rename_i f hf'
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · rename_i b hqb
                obtain ⟨hop, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                have hrh : ∃ F, f.rotate q = .lw (.res b) :: F := by
                  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hqb
                  refine ⟨f.drop (q + 1) ++ f.take q, ?_⟩
                  rw [List.rotate_eq_drop_append_take_mod, Nat.mod_eq_of_lt hlt,
                    List.drop_eq_getElem_cons hlt, hget]
                  rfl
                obtain ⟨F, hF⟩ := hrh
                refine Or.inr ⟨?_, Or.inr (Or.inr (Or.inr ⟨j, f, F, q, b, hjℓ, hf', hF, rfl⟩))⟩
                rw [← hop]
                split_ifs <;> decide
              · simp at hq
      · simp at h

/-- The change of `fR` along a term: `1` at `𝔣𝔯`, `0` at the ten other rows of Table 2
[table_effect_of_operations_2]. -/
private theorem fR_term (S R' : PkgExpr) (o : PkgOp) (h : (o, R') ∈ S.fterms) :
    (o = PkgOp.frep → R'.fR = S.fR + 1) ∧ (o ≠ PkgOp.frep → R'.fR = S.fR) := by
  have h2 := pkg_table2 S o R' h
  simp only [fR_eq, h2, Prod.fst_add, Prod.snd_add]
  cases o <;> simp [PkgOp.delta] <;> omega


private theorem kw_invW (right : Bool) (a : Fin 2) (tl : List PkgLetter) :
    kw (invW right a tl) = if right then .g :: kw tl else kw tl ++ [.g] := by
  cases right <;> simp [invW, kw, kd, List.filterMap_append, List.filterMap_cons]

private theorem CP_gg (p : Kd × Kd) : CP [.g, .g] p ↔ p = (.g, .g) := by
  obtain ⟨p1, p2⟩ := p
  simp [CP, lp, Prod.ext_iff]
  tauto

/-- A term other than `𝔣𝔯` keeps every cyclically consecutive pair of kinds other than `𝒢 𝒢`. -/
private theorem nf_pairs (S R' : PkgExpr) (o : PkgOp) (h : (o, R') ∈ S.fterms)
    (ho : o ≠ PkgOp.frep) (p : Kd × Kd) (hp : p ≠ (.g, .g)) : PS R' p ↔ PS S p := by
  obtain ⟨ℓ, r, right, w, a, tl, -, hw, hrot, hc⟩ := fterms_data S R' o h
  rcases hc with ⟨hfr, -⟩ | ⟨-, hc⟩
  · exact absurd hfr ho
  set K := kw (invW right a tl) with hKdef
  have hw' : CP (kw w) p ↔ CP K p := by
    have h1 : (kw w).IsRotated (.g :: kw tl) := by
      have := kw_rot (List.IsRotated.forall w r).symm
      rw [hrot] at this
      exact this
    have h2 : K.IsRotated (.g :: kw tl) := by
      rw [hKdef, kw_invW]
      cases right
      · exact List.isRotated_concat _ _
      · exact List.IsRotated.refl _
    rw [CP_rot h1, CP_rot h2]
  have hK : K.head? = some .g ∨ K.getLast? = some .g := by
    rw [hKdef, kw_invW]
    cases right
    · right; simp
    · left; simp
  have hKne : K ≠ [] := by
    rw [hKdef, kw_invW]; cases right <;> simp
  have hS1 : PS S p ↔ CP K p ∨ Oth S.loops [ℓ] (fun v => CP (kw v) p) := by
    rw [PS, ex_get S.loops (fun v => CP (kw v) p) ℓ w hw, hw']
  rcases hc with hl | ⟨q, b, hq, hl⟩ | ⟨b, y, hl⟩ | ⟨j, f, F, q, b, hjℓ, hf, hF, hl⟩
  · rw [hS1, PS, hl, ex_set S.loops (fun v => CP (kw v) p) ℓ w _ hw]
    have e : kw (if right then .lw (.proj S.nb) :: invW right a tl
        else invW right a tl ++ [.lw (.proj S.nb)]) = K := by
      cases right
      · simp [hKdef, kw, kd]
      · rfl
    rw [e]
  · rw [hS1, PS, hl, ex_set_app S.loops (fun v => CP (kw v) p) ℓ w _ _ hw]
    obtain ⟨X, Y, hXY, htake, hdrop⟩ := cut_pieces _ q b hq
    have e1 : kw ((invW right a tl).take (q + 1) ++ [.lw (.proj S.nb)]) = kw X ++ [.g] := by
      rw [htake]
      simp [kw, kd, List.filterMap_append]
    have e2 : kw (.lw (.proj S.nb) :: (invW right a tl).drop q) = .g :: kw Y := by
      rw [hdrop]
      rfl
    have e3 : K = kw X ++ .g :: kw Y := by
      rw [hKdef, hXY, kw_append]
      rfl
    rw [e1, e2]
    rw [e3] at hK
    rw [e3, ← CP_cut _ _ p hp hK]
    tauto
  · rw [hS1, PS, hl, ex_set S.loops (fun v => CP (kw v) p) ℓ w _ hw]
    have e : kw (invW right a tl ++ [.lw (.proj S.nb), .lw (.res b), .lw (.proj y), .lw (.res b),
        .lw (.proj S.nb)]) = K ++ [.g, .g] := by
      rw [kw_append]
      rfl
    have hK2 : (K.head? = some .g ∧ ([Kd.g, .g] : List Kd).head? = some .g) ∨
        (K.getLast? = some .g ∧ ([Kd.g, .g] : List Kd).getLast? = some .g) := by
      rcases hK with hK | hK
      · exact Or.inl ⟨hK, rfl⟩
      · exact Or.inr ⟨hK, rfl⟩
    rw [e, CP_J _ _ hKne (by simp) hK2, CP_gg]
    simp [hp]
  · unfold PS
    rw [ex_get2 S.loops (fun v => CP (kw v) p) ℓ j w f hw hf hjℓ, hw', hl,
      ex_set_erase S.loops (fun v => CP (kw v) p) ℓ j w _ hw hjℓ]
    have hf' : CP (kw f) p ↔ CP (.g :: kw F) p := by
      have := kw_rot (List.IsRotated.forall f q).symm
      rw [hF] at this
      exact CP_rot this p
    have e : kw (invW right a tl ++ [.lw (.proj S.nb)] ++ f.rotate q ++
        [.lw (.res b), .lw (.proj S.nb)]) = K ++ ((Kd.g :: kw F) ++ [.g]) := by
      rw [kw_append, kw_append, kw_append, hF]
      have e1 : kw [PkgLetter.lw (.proj S.nb)] = [] := rfl
      have e2 : kw [PkgLetter.lw (.res b), .lw (.proj S.nb)] = [.g] := rfl
      have e3 : kw (.lw (.res b) :: F) = .g :: kw F := rfl
      rw [e1, e2, e3, List.append_nil, List.append_assoc]
    have hK2 : (K.head? = some .g ∧ ((Kd.g :: kw F) ++ [Kd.g]).head? = some .g) ∨
        (K.getLast? = some .g ∧ ((Kd.g :: kw F) ++ [Kd.g]).getLast? = some .g) := by
      rcases hK with hK | hK
      · exact Or.inl ⟨hK, rfl⟩
      · exact Or.inr ⟨hK, by rw [List.getLast?_append]; simp⟩
    rw [e, CP_J _ _ hKne (by simp) hK2, CP_J _ _ (by simp) (by simp) (Or.inl ⟨rfl, rfl⟩),
      CP_single, hf']
    simp only [hp, or_false, or_assoc]

/-- The replacement `𝔣𝔯` removes the resolvent `𝒢_a` chosen by the rules: the kinds of its word
are `𝒢 t` cyclically, become `t`, and `t` ends (resolvent right of `Λ̃_o`) or starts (left)
with `Λ̃_o`. -/
private theorem frep_data (S R' : PkgExpr) (hU0 : UO S 0) (hU1 : UO S 1)
    (h : (PkgOp.frep, R') ∈ S.fterms) :
    ∃ (o : Fin 2) (right : Bool) (ℓ : ℕ) (w : List PkgLetter) (t : List Kd),
      S.loops[ℓ]? = some w ∧ (kw w).IsRotated (.g :: t) ∧
      (∀ Ψ : List Kd → Prop, (∃ v ∈ R'.loops, Ψ (kw v)) ↔
        Ψ t ∨ Oth S.loops [ℓ] (fun v => Ψ (kw v))) ∧
      (right = true → t.getLast? = some (.l o)) ∧ (right = false → t.head? = some (.l o)) ∧
      (S.ptype ≠ 2 → (o = 1 ∧ right = true) ∨ (o = 0 ∧ right = true ∧ ¬ SB S 1 true) ∨
        (o = 1 ∧ right = false ∧ ¬ SB S 1 true ∧ ¬ SB S 0 true)) ∧
      (S.ptype = 2 → (o = 1 ∧ right = false) ∨ (o = 0 ∧ right = true ∧ ¬ SB S 1 false)) := by
  obtain ⟨ℓ, r, right, w, a, tl, hf, hw, hrot, hc⟩ := fterms_data S R' _ h
  rcases hc with ⟨-, hl⟩ | ⟨hne, -⟩
  swap
  · exact absurd rfl hne
  obtain ⟨o, w', hw', -, ho, hs, h1, h2⟩ := focus_rule S hU0 hU1 ℓ r right hf
  rw [hw] at hw'
  cases hw'
  obtain ⟨Z, hZ⟩ := rot_idx ho
  obtain ⟨A, B, b, hA, hrb⟩ := seek_pos w _ r _ Z hZ right hs
  rw [hrot] at hrb
  have htl := (List.cons.inj hrb).2
  refine ⟨o, right, ℓ, w, kw tl, hw, ?_, ?_, ?_, ?_, h1, h2⟩
  · have := kw_rot (List.IsRotated.forall w r).symm
    rw [hrot] at this
    exact this
  · intro Ψ
    rw [hl, ex_set S.loops (fun v => Ψ (kw v)) ℓ w _ hw]
    rfl
  · rintro rfl
    rw [htl]
    simp only [↓reduceIte]
    rw [kw_append]
    change (kw B ++ Kd.l o :: kw A).getLast? = _
    rw [hA]
    simp
  · rintro rfl
    rw [htl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [kw_append, hA]
    rfl

private theorem frep_pairs (t : List Kd) (x : Kd) (hx : x ≠ .g) (y : Kd) (hy : y ≠ .g) :
    (t.getLast? = some x → y ≠ x → (CP t (y, .g) ↔ CP (.g :: t) (y, .g))) ∧
    (t.getLast? = some x → CP t (.g, y) → CP (.g :: t) (.g, y)) ∧
    (t.getLast? = some x → CP (.g :: t) (.g, y) → CP t (.g, y) ∨ t.head? = some y) ∧
    (t.head? = some x → y ≠ x → (CP t (.g, y) ↔ CP (.g :: t) (.g, y))) ∧
    (t.head? = some x → CP t (y, .g) → CP (.g :: t) (y, .g)) ∧
    (t.head? = some x → CP (.g :: t) (y, .g) → CP t (y, .g) ∨ t.getLast? = some y) := by
  rcases t with _ | ⟨z, t⟩
  · simp
  have ht : z :: t ≠ [] := by simp
  have G := CP_gcons _ ht
  have T : ∀ p, CP (z :: t) p ↔ p ∈ lp (z :: t) ∨
      ((z :: t).getLast? = some p.1 ∧ (z :: t).head? = some p.2) := fun p => Iff.rfl
  simp only [G, T]
  refine ⟨fun h hne => ?_, fun h h1 => ?_, fun h h1 => ?_, fun h hne => ?_, fun h h1 => ?_,
    fun h h1 => ?_⟩
  · rw [h]
    simp only [Option.some.injEq, hne.symm, false_and, or_false, hy, false_and, false_or,
      and_true]
  · rw [h] at h1 ⊢
    simp only [Option.some.injEq] at h1 ⊢
    rcases h1 with h1 | ⟨h1, -⟩
    · exact Or.inr (Or.inl h1)
    · exact absurd h1 hx
  · rw [h] at h1 ⊢
    simp only [Option.some.injEq] at h1 ⊢
    rcases h1 with ⟨-, h1⟩ | h1 | ⟨h1, -⟩
    · exact Or.inr h1
    · exact Or.inl (Or.inl h1)
    · exact absurd h1 hx
  · rw [h]
    simp only [Option.some.injEq, hne.symm, and_false, or_false, hy, false_or, and_false]
  · rw [h] at h1 ⊢
    simp only [Option.some.injEq] at h1 ⊢
    rcases h1 with h1 | ⟨-, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact absurd h1 hx
  · rw [h] at h1 ⊢
    simp only [Option.some.injEq] at h1 ⊢
    rcases h1 with ⟨-, h1⟩ | h1 | ⟨h1, -⟩
    · exact absurd h1 hx
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1


/-- (C1): the word with `Λ̃₁` has a letter `Δ`. -/
private theorem arc_d (S : PkgExpr) (hA : ArcInv S) (hU0 : UO S 0) (w : List PkgLetter)
    (hw : w ∈ S.loops) (h0 : Kd.l 0 ∈ kw w) : Kd.d ∈ kw w := by
  obtain ⟨v, hv, u, v', S', Y, -, hrot⟩ := hA
  have h1 : PkgLetter.lw (.lamt 0) ∈ v := hrot.mem_iff.1 (by simp)
  have h2 : PkgLetter.ent u v' ∈ v := hrot.mem_iff.1 (by simp)
  rw [← (uniq_word hU0 hv h1 hw ((l_mem_kw 0 w).1 h0)).1]
  exact mem_kw.2 ⟨_, h2, rfl⟩

private theorem bw_head : ∀ (Z : List Kd) (y : Kd), (bw Z).head? = some y →
    ∃ k D, Z = List.replicate k .g ++ y :: D
  | [], y, h => by simp [bw] at h
  | z :: Z, y, h => by
      by_cases hz : z = .g
      · subst hz
        have : (bw Z).head? = some y := by simpa [bw] using h
        obtain ⟨k, D, rfl⟩ := bw_head Z y this
        exact ⟨k + 1, D, by simp [List.replicate_succ]⟩
      · have : z = y := by simpa [bw, hz] using h
        exact ⟨0, Z, by simp [this]⟩

/-- In Type II the loop of `Λ̃₂` has resolvents on both sides of `Λ̃₂` or on none. -/
private theorem st_II (R : PkgExpr) (hwf : R.wf = true) (hA : ArcInv R) (h : R.ptype = 2) :
    (SB R 1 false ↔ SB R 1 true) ∧ (¬ SB R 1 false → PS R (.l 1, .l 1)) := by
  have hU0 := uo_of_wf R hwf 0
  have hU1 := uo_of_wf R hwf 1
  obtain ⟨w, hw, h1, hd⟩ := (ptype_cases R hU0 hU1).1.1 h
  have h1' := (l_mem_kw 1 w).1 h1
  obtain ⟨Z, hZ, hZ1⟩ := word_rot R 1 hU1 w hw h1'
  have hg : ∀ z ∈ Z, z = .g := by
    intro z hz
    have hz' : z ∈ kw w := hZ.mem_iff.2 (List.mem_cons_of_mem _ hz)
    match z, hz, hz' with
    | .g, _, _ => rfl
    | .d, _, hz' => exact absurd hz' hd
    | .l o, hz, hz' =>
      rcases (by decide : ∀ o : Fin 2, o = 0 ∨ o = 1) o with rfl | rfl
      · exact absurd (arc_d R hA hU0 w hw hz') hd
      · exact absurd hz hZ1
  have eL : SB R 1 false ↔ (Kd.l 1 :: Z).getLast? = some .g := by
    simp only [SB, Bool.false_eq_true, ↓reduceIte]
    rw [PS_word R 1 hU1 w hw h1' _ (Or.inr rfl), CP_rot hZ, CP_x_snd _ _ _ hZ1]
  have eR : SB R 1 true ↔ (Z ++ [Kd.l 1]).head? = some .g := by
    simp only [SB, ↓reduceIte]
    rw [PS_word R 1 hU1 w hw h1' _ (Or.inl rfl), CP_rot hZ, CP_x_fst _ _ _ hZ1]
  rcases Z with _ | ⟨z, Z'⟩
  · refine ⟨by rw [eL, eR]; simp, fun _ => ⟨w, hw, ?_⟩⟩
    rw [CP_rot hZ, CP_single]
  · have hz : z = .g := hg z (by simp)
    have hlast : (Kd.l 1 :: z :: Z').getLast? = some .g := by
      rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (by simp)]
      exact congrArg some (hg _ (List.getLast_mem _))
    refine ⟨iff_of_true (eL.2 hlast) (eR.2 (by simp [hz])), fun h => absurd (eL.2 hlast) h⟩

/-- In Type III the stretch between `Λ̃₁` and `Λ̃₂` is the right side of `Λ̃₁` and the left side
of `Λ̃₂`. -/
private theorem st_III (R : PkgExpr) (hwf : R.wf = true) (h : R.ptype = 3) :
    (SB R 0 true ↔ SB R 1 false) ∧ (¬ SB R 0 true → PS R (.l 0, .l 1)) := by
  have hU0 := uo_of_wf R hwf 0
  have hU1 := uo_of_wf R hwf 1
  obtain ⟨w, hw, -, hc⟩ := (ptype_cases R hU0 hU1).2.1.1 h
  have h0 : Kd.l 0 ∈ kw w := (List.mem_filter.1 (CP_mem hc).1).1
  have h1 : Kd.l 1 ∈ kw w := (List.mem_filter.1 (CP_mem hc).2).1
  obtain ⟨Z, hZ, hZ0⟩ := word_rot R 0 hU0 w hw ((l_mem_kw 0 w).1 h0)
  have hb : (bw (kw w)).IsRotated (.l 0 :: bw Z) := by
    have := bw_rot hZ
    rwa [bw_cons_l] at this
  rw [CP_rot hb, CP_x_fst (.l 0) (.l 1) (bw Z) (fun hm => hZ0 (List.mem_filter.1 hm).1)] at hc
  have hc' : (bw Z).head? = some (.l 1) := by
    rcases hbZ : bw Z with _ | ⟨y, l⟩
    · rw [hbZ] at hc
      simp at hc
    · rw [hbZ] at hc
      simpa using hc
  obtain ⟨k, D, rfl⟩ := bw_head Z _ hc'
  have hc1 : (kw w).count (.l 1) = 1 := by
    rw [count_kw_l]
    exact (uniq_word hU1 hw ((l_mem_kw 1 w).1 h1) hw ((l_mem_kw 1 w).1 h1)).2
  have hD1 : Kd.l 1 ∉ D := by
    intro hm
    have := hZ.perm.count_eq (Kd.l 1)
    rw [hc1] at this
    simp [List.count_append, List.count_replicate] at this
    have := List.count_pos_iff.2 hm
    omega
  have hrot1 : (kw w).IsRotated (.l 1 :: (D ++ .l 0 :: List.replicate k .g)) := by
    refine hZ.trans ?_
    have := List.isRotated_append (l := Kd.l 0 :: List.replicate k .g) (l' := Kd.l 1 :: D)
    simpa using this
  have hn1 : Kd.l 1 ∉ D ++ .l 0 :: List.replicate k .g := by
    simp [hD1, List.mem_replicate]
  have eR : SB R 0 true ↔ (List.replicate k Kd.g ++ Kd.l 1 :: D ++ [Kd.l 0]).head? = some .g := by
    simp only [SB, ↓reduceIte]
    rw [PS_word R 0 hU0 w hw ((l_mem_kw 0 w).1 h0) _ (Or.inl rfl), CP_rot hZ, CP_x_fst _ _ _ hZ0]
  have eL : SB R 1 false ↔
      (Kd.l 1 :: (D ++ .l 0 :: List.replicate k .g)).getLast? = some .g := by
    simp only [SB, Bool.false_eq_true, ↓reduceIte]
    rw [PS_word R 1 hU1 w hw ((l_mem_kw 1 w).1 h1) _ (Or.inr rfl), CP_rot hrot1,
      CP_x_snd _ _ _ hn1]
  rcases k with _ | k
  · refine ⟨iff_of_false (by rw [eR]; simp) (by
      rw [eL]
      simp only [List.replicate_zero]
      rw [← List.cons_append, List.getLast?_append]
      simp),
      fun _ => ⟨w, hw, ?_⟩⟩
    rw [CP_rot hZ]
    left
    simp [lp]
  · have hR : SB R 0 true := by rw [eR]; simp [List.replicate_succ]
    refine ⟨iff_of_true hR ?_, fun h => absurd hR h⟩
    rw [eL, List.getLast?_cons, List.getLast?_append, List.getLast?_cons,
      List.getLast?_replicate]
    simp

/-- A loop `⟨Λ̃₂⟩` without resolvent is Type II. -/
private theorem st_11 (R : PkgExpr) (hwf : R.wf = true) (h : PS R (.l 1, .l 1)) :
    R.ptype = 2 := by
  have hU0 := uo_of_wf R hwf 0
  have hU1 := uo_of_wf R hwf 1
  obtain ⟨w, hw, hc⟩ := h
  have h1 := (CP_mem hc).1
  obtain ⟨Z, hZ, hZ1⟩ := word_rot R 1 hU1 w hw ((l_mem_kw 1 w).1 h1)
  rw [CP_rot hZ, CP_x_fst _ _ _ hZ1] at hc
  have hZe : Z = [] := by
    rcases Z with _ | ⟨z, Z'⟩
    · rfl
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hc
      subst hc
      exact absurd List.mem_cons_self hZ1
  subst hZe
  refine (ptype_cases R hU0 hU1).1.2 ⟨w, hw, h1, fun hd => ?_⟩
  have := hZ.mem_iff.1 hd
  simp at this

/-- `Λ̃₁` directly followed by `Λ̃₂` is Type III. -/
private theorem st_01 (R : PkgExpr) (hwf : R.wf = true) (hA : ArcInv R)
    (h : PS R (.l 0, .l 1)) : R.ptype = 3 := by
  have hU0 := uo_of_wf R hwf 0
  have hU1 := uo_of_wf R hwf 1
  obtain ⟨w, hw, hc⟩ := h
  have h0 := (CP_mem hc).1
  obtain ⟨Z, hZ, hZ0⟩ := word_rot R 0 hU0 w hw ((l_mem_kw 0 w).1 h0)
  rw [CP_rot hZ, CP_x_fst _ _ _ hZ0] at hc
  obtain ⟨Z', rfl⟩ : ∃ Z', Z = .l 1 :: Z' := by
    rcases Z with _ | ⟨z, Z'⟩
    · simp at hc
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hc
      exact ⟨Z', by rw [hc]⟩
  refine (ptype_cases R hU0 hU1).2.1.2 ⟨w, hw, arc_d R hA hU0 w hw h0, ?_⟩
  rw [CP_rot (bw_rot hZ)]
  left
  simp [bw, lp]

/-! ### The invariant of the order and of the empty sides -/

/-- `0` if the side has a resolvent, `1` if it is empty. -/
private def ez (P : Prop) : ℕ := if P then 0 else 1

private theorem ez_le (P : Prop) : ez P ≤ 1 := by unfold ez; split <;> omega
private theorem ez_of {P : Prop} (h : P) : ez P = 0 := by unfold ez; simp [h]
private theorem ez_of_not {P : Prop} (h : ¬ P) : ez P = 1 := by unfold ez; simp [h]

/-- (I1)–(I4) through the sides. -/
private def OrdB (R : PkgExpr) : Prop :=
  (R.ptype = 1 → (SB R 1 true → SB R 0 true ∧ SB R 1 false) ∧
    (¬ SB R 1 false → ¬ SB R 0 true ∧ ¬ SB R 1 true)) ∧
  (R.ptype = 2 → SB R 1 false → SB R 0 true) ∧
  (R.ptype = 3 → SB R 1 true → SB R 0 true)

/-- The number of empty sides through the sides. -/
private def EB (R : PkgExpr) : ℕ :=
  if R.ptype = 1 then ez (SB R 0 true) + ez (SB R 1 false) + ez (SB R 1 true)
  else if R.ptype = 2 then ez (SB R 0 true) + ez (SB R 1 false)
  else ez (SB R 0 true) + ez (SB R 1 true)

private theorem trans_nf (τ τ' : ℕ) (b0 l1 r1 P11 P01 : Prop)
    (hτ : τ = 1 ∨ τ = 2 ∨ τ = 3) (hτ' : τ' = 1 ∨ τ' = 2 ∨ τ' = 3)
    (h2 : τ = 2 → (l1 ↔ r1) ∧ (¬ l1 → P11)) (h3 : τ = 3 → (b0 ↔ l1) ∧ (¬ b0 → P01))
    (h2' : τ' = 2 → (l1 ↔ r1)) (h3' : τ' = 3 → (b0 ↔ l1))
    (k11 : P11 → τ' = 2) (k01 : P01 → τ' = 3)
    (hO : (τ = 1 → (r1 → b0 ∧ l1) ∧ (¬ l1 → ¬ b0 ∧ ¬ r1)) ∧ (τ = 2 → l1 → b0) ∧
      (τ = 3 → r1 → b0)) :
    ((τ' = 1 → (r1 → b0 ∧ l1) ∧ (¬ l1 → ¬ b0 ∧ ¬ r1)) ∧ (τ' = 2 → l1 → b0) ∧
      (τ' = 3 → r1 → b0)) ∧
    (if τ' = 1 then ez b0 + ez l1 + ez r1 else if τ' = 2 then ez b0 + ez l1 else ez b0 + ez r1) ≤
    (if τ = 1 then ez b0 + ez l1 + ez r1 else if τ = 2 then ez b0 + ez l1 else ez b0 + ez r1) := by
  rcases hτ with rfl | rfl | rfl <;> rcases hτ' with rfl | rfl | rfl <;>
    by_cases hb0 : b0 <;> by_cases hl1 : l1 <;> by_cases hr1 : r1 <;> simp_all [ez]

/-- One term other than `𝔣𝔯` keeps the order and does not raise the number of empty sides. -/
private theorem nf_step (S R' : PkgExpr) (o : PkgOp) (h : (o, R') ∈ S.fterms)
    (ho : o ≠ PkgOp.frep) (hw : S.wf = true) (hA : ArcInv S) (hw' : R'.wf = true)
    (hA' : ArcInv R') (hO : OrdB S) : OrdB R' ∧ EB R' ≤ EB S := by
  have e0 : SB R' 0 true ↔ SB S 0 true := nf_pairs S R' o h ho _ (by decide)
  have e1 : SB R' 1 false ↔ SB S 1 false := nf_pairs S R' o h ho _ (by decide)
  have e2 : SB R' 1 true ↔ SB S 1 true := nf_pairs S R' o h ho _ (by decide)
  have p11 : PS R' (.l 1, .l 1) ↔ PS S (.l 1, .l 1) := nf_pairs S R' o h ho _ (by decide)
  have p01 : PS R' (.l 0, .l 1) ↔ PS S (.l 0, .l 1) := nf_pairs S R' o h ho _ (by decide)
  have hτ := (ptype_cases S (uo_of_wf S hw 0) (uo_of_wf S hw 1)).2.2
  have hτ' := (ptype_cases R' (uo_of_wf R' hw' 0) (uo_of_wf R' hw' 1)).2.2
  have h2' : R'.ptype = 2 → (SB S 1 false ↔ SB S 1 true) := fun h => by
    rw [← e1, ← e2]; exact (st_II R' hw' hA' h).1
  have h3' : R'.ptype = 3 → (SB S 0 true ↔ SB S 1 false) := fun h => by
    rw [← e0, ← e1]; exact (st_III R' hw' h).1
  unfold OrdB EB
  rw [e0, e1, e2]
  exact trans_nf S.ptype R'.ptype _ _ _ (PS S (.l 1, .l 1)) (PS S (.l 0, .l 1)) hτ hτ'
    (fun h => st_II S hw hA h) (fun h => st_III S hw h) h2' h3'
    (fun h => st_11 R' hw' (p11.2 h)) (fun h => st_01 R' hw' hA' (p01.2 h)) hO

private theorem bw_head_of (t : List Kd) (y : Kd) (hy : y ≠ .g) (h : t.head? = some y) :
    (bw t).head? = some y := by
  rcases t with _ | ⟨z, t⟩
  · simp at h
  · simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp [bw, hy]

private theorem bw_last_of (t : List Kd) (y : Kd) (hy : y ≠ .g) (h : t.getLast? = some y) :
    (bw t).getLast? = some y := by
  obtain ⟨t', rfl⟩ := List.getLast?_eq_some_iff.1 h
  simp [bw, List.filter_append, hy]

/-- The replacement `𝔣𝔯` keeps the Type, keeps the order, and raises the number of empty sides
by at most one. -/
private theorem frep_step (S R' : PkgExpr) (h : (PkgOp.frep, R') ∈ S.fterms)
    (hw : S.wf = true) (hA : ArcInv S) (hw' : R'.wf = true) (hO : OrdB S) :
    OrdB R' ∧ EB R' ≤ EB S + 1 := by
  have hU0 := uo_of_wf S hw 0
  have hU1 := uo_of_wf S hw 1
  obtain ⟨o, right, ℓ, w, t, hwl, hrot, htr, hR, hL, f1, f2⟩ := frep_data S R' hU0 hU1 h
  have hwm : w ∈ S.loops := List.mem_of_getElem? hwl
  have hS : ∀ Ψ : List Kd → Prop, (∃ v ∈ S.loops, Ψ (kw v)) ↔
      Ψ (kw w) ∨ Oth S.loops [ℓ] (fun v => Ψ (kw v)) :=
    fun Ψ => ex_get S.loops (fun v => Ψ (kw v)) ℓ w hwl
  have tr : ∀ p, (PS R' p ↔ CP t p ∨ Oth S.loops [ℓ] (fun v => CP (kw v) p)) ∧
      (PS S p ↔ CP (.g :: t) p ∨ Oth S.loops [ℓ] (fun v => CP (kw v) p)) := fun p =>
    ⟨htr (fun l => CP l p), by rw [PS, hS (fun l => CP l p), CP_rot hrot]⟩
  have hl1 : ∀ o', Kd.l o' ≠ Kd.g := fun o' => by simp
  -- the Type is kept
  have hpt : R'.ptype = S.ptype := by
    have key : ∀ Ψ : List Kd → Prop, (Ψ (kw w) ↔ Ψ t) →
        ((∃ v ∈ R'.loops, Ψ (kw v)) ↔ (∃ v ∈ S.loops, Ψ (kw v))) := by
      intro Ψ hΨ
      rw [htr Ψ, hS Ψ, hΨ]
    have hU0' := uo_of_wf R' hw' 0
    have hU1' := uo_of_wf R' hw' 1
    have k2 : R'.ptype = 2 ↔ S.ptype = 2 := by
      rw [(ptype_cases R' hU0' hU1').1, (ptype_cases S hU0 hU1).1]
      refine key (fun l => Kd.l 1 ∈ l ∧ Kd.d ∉ l) ?_
      simp only [hrot.mem_iff, List.mem_cons, reduceCtorEq, false_or]
    have k3 : R'.ptype = 3 ↔ S.ptype = 3 := by
      rw [(ptype_cases R' hU0' hU1').2.1, (ptype_cases S hU0 hU1).2.1]
      refine key (fun l => Kd.d ∈ l ∧ CP (bw l) (.l 0, .l 1)) ?_
      have hb : (bw (kw w)).IsRotated (bw t) := by
        have := bw_rot hrot
        simpa [bw] using this
      simp only [hrot.mem_iff, List.mem_cons, reduceCtorEq, false_or, CP_rot hb]
    rcases (ptype_cases R' hU0' hU1').2.2 with h' | h' | h' <;>
      rcases (ptype_cases S hU0 hU1).2.2 with h'' | h'' | h'' <;> simp_all
  -- the sides
  have A1 : right = true → ∀ o', o' ≠ o → (SB R' o' true ↔ SB S o' true) := by
    intro hr o' hne
    simp only [SB, ↓reduceIte]
    rw [(tr _).1, (tr _).2,
      (frep_pairs t _ (hl1 o) _ (hl1 o')).1 (hR hr) (fun h => hne (Kd.l.inj h))]
  have A3 : right = true → ∀ o', SB S o' false → SB R' o' false ∨ t.head? = some (.l o') := by
    intro hr o' h1
    simp only [SB, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    rw [(tr _).2] at h1
    rw [(tr _).1]
    rcases h1 with h1 | h1
    · rcases (frep_pairs t _ (hl1 o) _ (hl1 o')).2.2.1 (hR hr) h1 with h2 | h2
      · exact Or.inl (Or.inl h2)
      · exact Or.inr h2
    · exact Or.inl (Or.inr h1)
  have A2 : right = true → ∀ o', SB R' o' false → SB S o' false := by
    intro hr o' h1
    simp only [SB, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    rw [(tr _).1] at h1
    rw [(tr _).2]
    rcases h1 with h1 | h1
    · exact Or.inl ((frep_pairs t _ (hl1 o) _ (hl1 o')).2.1 (hR hr) h1)
    · exact Or.inr h1
  have B2 : right = false → ∀ o', SB R' o' true → SB S o' true := by
    intro hr o' h1
    simp only [SB, ↓reduceIte] at h1 ⊢
    rw [(tr _).1] at h1
    rw [(tr _).2]
    rcases h1 with h1 | h1
    · exact Or.inl ((frep_pairs t _ (hl1 o) _ (hl1 o')).2.2.2.2.1 (hL hr) h1)
    · exact Or.inr h1
  have B3 : right = false → ∀ o', SB S o' true → SB R' o' true ∨ t.getLast? = some (.l o') := by
    intro hr o' h1
    simp only [SB, ↓reduceIte] at h1 ⊢
    rw [(tr _).2] at h1
    rw [(tr _).1]
    rcases h1 with h1 | h1
    · rcases (frep_pairs t _ (hl1 o) _ (hl1 o')).2.2.2.2.2 (hL hr) h1 with h2 | h2
      · exact Or.inl (Or.inl h2)
      · exact Or.inr h2
    · exact Or.inl (Or.inr h1)
  have FR : right = true → SB S o true := by
    intro hr
    simp only [SB, ↓reduceIte]
    rw [(tr _).2]
    left
    have ht : t ≠ [] := by
      intro h
      have := hR hr
      rw [h] at this
      simp at this
    rw [CP_gcons t ht]
    exact Or.inr (Or.inr ⟨hR hr, rfl⟩)
  have FL : right = false → SB S o false := by
    intro hr
    simp only [SB, Bool.false_eq_true, ↓reduceIte]
    rw [(tr _).2]
    left
    have ht : t ≠ [] := by
      intro h
      have := hL hr
      rw [h] at this
      simp at this
    rw [CP_gcons t ht]
    exact Or.inl ⟨rfl, hL hr⟩
  -- the contradictions
  have X1 : t.head? = some (.l 1) → t.getLast? = some (.l 1) → S.ptype = 2 := by
    intro h1 h2
    have hc : (Kd.g :: t).count (.l 1) = 1 := by
      rw [← hrot.perm.count_eq, count_kw_l]
      have hm : PkgLetter.lw (.lamt 1) ∈ w := by
        rw [← l_mem_kw, hrot.mem_iff]
        exact List.mem_cons_of_mem _ (List.mem_of_mem_head? h1)
      exact (uniq_word hU1 hwm hm hwm hm).2
    obtain ⟨t', rfl⟩ : ∃ t', t = .l 1 :: t' := by
      rcases t with _ | ⟨z, t'⟩
      · simp at h1
      · simp only [List.head?_cons, Option.some.injEq] at h1
        exact ⟨t', by rw [h1]⟩
    have ht' : t' = [] := by
      rcases t' with _ | ⟨z, t''⟩
      · rfl
      · exfalso
        rw [List.getLast?_cons_cons] at h2
        have := List.mem_of_getLast? h2
        have h3 : 1 ≤ (z :: t'').count (Kd.l 1) := List.count_pos_iff.2 this
        have h4 : (Kd.g :: Kd.l 1 :: z :: t'').count (Kd.l 1) =
            (z :: t'').count (Kd.l 1) + 1 := by
          rw [List.count_cons, List.count_cons]
          simp
        omega
    subst ht'
    refine (ptype_cases S hU0 hU1).1.2 ⟨w, hwm, by rw [hrot.mem_iff]; simp, ?_⟩
    rw [hrot.mem_iff]
    simp
  have X3 : t.head? = some (.l 1) → t.getLast? = some (.l 0) → S.ptype = 3 := by
    intro h1 h2
    have h0 : Kd.l 0 ∈ kw w := by
      rw [hrot.mem_iff]
      exact List.mem_cons_of_mem _ (List.mem_of_getLast? h2)
    refine (ptype_cases S hU0 hU1).2.1.2 ⟨w, hwm, arc_d S hA hU0 w hwm h0, ?_⟩
    have hb : (bw (kw w)).IsRotated (bw t) := by
      have := bw_rot hrot
      simpa [bw] using this
    rw [CP_rot hb]
    exact Or.inr ⟨bw_last_of t _ (hl1 0) h2, bw_head_of t _ (hl1 1) h1⟩
  have hτS := (ptype_cases S hU0 hU1).2.2
  unfold OrdB EB
  rw [hpt]
  unfold OrdB at hO
  have l0 := ez_le (SB R' 0 true)
  have l1 := ez_le (SB R' 1 false)
  have l2 := ez_le (SB R' 1 true)
  rcases hτS with hτ | hτ | hτ
  · have hn2 : S.ptype ≠ 2 := by omega
    simp only [hτ, ↓reduceIte, true_implies, Nat.reduceEqDiff, false_implies, and_true] at hO ⊢
    rcases f1 hn2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, nr1⟩ | ⟨rfl, rfl, nr1, nb0⟩
    · have r1 := FR rfl
      obtain ⟨b0, b1⟩ := hO.1 r1
      have b0' := (A1 rfl 0 (by decide)).2 b0
      have b1' : SB R' 1 false := by
        rcases A3 rfl 1 b1 with h | h
        · exact h
        · exact absurd (X1 h (hR rfl)) hn2
      refine ⟨⟨fun _ => ⟨b0', b1'⟩, fun h => absurd b1' h⟩, ?_⟩
      rw [ez_of b0', ez_of b1']
      omega
    · have b0 := FR rfl
      have b1 : SB S 1 false := by
        by_contra hb1
        exact (hO.2 hb1).1 b0
      have b1' : SB R' 1 false := by
        rcases A3 rfl 1 b1 with h | h
        · exact h
        · rw [X3 h (hR rfl)] at hτ
          omega
      have r1' : ¬ SB R' 1 true := fun h => nr1 ((A1 rfl 1 (by decide)).1 h)
      refine ⟨⟨fun h => absurd h r1', fun h => absurd b1' h⟩, ?_⟩
      rw [ez_of b1', ez_of_not nr1, ez_of b1]
      omega
    · have r1' : ¬ SB R' 1 true := fun h => nr1 (B2 rfl 1 h)
      have b0' : ¬ SB R' 0 true := fun h => nb0 (B2 rfl 0 h)
      have b1 := FL rfl
      refine ⟨⟨fun h => absurd h r1', fun _ => ⟨b0', r1'⟩⟩, ?_⟩
      rw [ez_of_not nb0, ez_of b1, ez_of_not nr1]
      omega
  · simp only [hτ, ↓reduceIte, Nat.reduceEqDiff, false_implies, true_implies, true_and,
      and_true] at hO ⊢
    rcases f2 hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl, nl1⟩
    · have b1 := FL rfl
      have b0 := hO b1
      have b0' : SB R' 0 true := by
        rcases B3 rfl 0 b0 with h | h
        · exact h
        · rw [X3 (hL rfl) h] at hτ
          omega
      refine ⟨fun _ => b0', ?_⟩
      rw [ez_of b0', ez_of b0, ez_of b1]
      omega
    · have l1' : ¬ SB R' 1 false := fun h => nl1 (A2 rfl 1 h)
      have b0 := FR rfl
      refine ⟨fun h => absurd h l1', ?_⟩
      rw [ez_of b0, ez_of_not nl1, ez_of_not l1']
      omega
  · have hn2 : S.ptype ≠ 2 := by omega
    simp only [hτ, ↓reduceIte, Nat.reduceEqDiff, false_implies, true_implies, true_and] at hO ⊢
    rcases f1 hn2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, nr1⟩ | ⟨rfl, rfl, nr1, nb0⟩
    · have b0 := hO (FR rfl)
      have b0' := (A1 rfl 0 (by decide)).2 b0
      refine ⟨fun _ => b0', ?_⟩
      rw [ez_of b0', ez_of b0]
      omega
    · have r1' : ¬ SB R' 1 true := fun h => nr1 ((A1 rfl 1 (by decide)).1 h)
      refine ⟨fun h => absurd h r1', ?_⟩
      rw [ez_of (FR rfl), ez_of_not nr1, ez_of_not r1']
      omega
    · have r1' : ¬ SB R' 1 true := fun h => nr1 (B2 rfl 1 h)
      refine ⟨fun h => absurd h r1', ?_⟩
      rw [ez_of_not nb0, ez_of_not nr1, ez_of_not r1']
      omega

/-! ### The start of the further expansion -/


private theorem tw_res : ∀ L : List LoopLetter, 1 ≤ (L.takeWhile notLam).countP rcR →
    (kw (L.map PkgLetter.lw)).head? = some .g
  | [], h => by simp at h
  | x :: L, h => by
      match x with
      | .res a => simp [kw, kd]
      | .det a =>
        have e : (List.takeWhile notLam (LoopLetter.det a :: L)).countP rcR =
            (L.takeWhile notLam).countP rcR := by simp [List.takeWhile_cons, notLam, rcR]
        simpa [kw, kd, List.filterMap_cons] using tw_res L (e ▸ h)
      | .proj y =>
        have e : (List.takeWhile notLam (LoopLetter.proj y :: L)).countP rcR =
            (L.takeWhile notLam).countP rcR := by simp [List.takeWhile_cons, notLam, rcR]
        simpa [kw, kd, List.filterMap_cons] using tw_res L (e ▸ h)
      | .lamt o => simp [notLam] at h

/-- `k_o ≥ 1`: the letter before `Λ̃_o` in its loop, up to `𝔐` and `E_x`, is a resolvent. -/
private theorem kk_pred (T : LoopExpr) (hT : T.wf = true) (o : Fin 2) (hk : 1 ≤ T.kk o) :
    ∃ (j : ℕ) (v V : List LoopLetter), T.loops[j]? = some v ∧
      v.rotate (v.idxOf (.lamt o)) = .lamt o :: V ∧
      (kw (V.map PkgLetter.lw)).getLast? = some .g := by
  obtain ⟨v, hv, hov⟩ : ∃ v ∈ T.loops, LoopLetter.lamt o ∈ v := by
    by_contra hno
    have hno' : ∀ v ∈ T.loops, LoopLetter.lamt o ∉ v := fun v hv h => hno ⟨v, hv, h⟩
    have : T.kk o = 0 := by
      unfold LoopExpr.kk
      rw [List.sum_eq_zero_iff]
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      have : w.contains (.lamt o) = false := by simpa using hno' w hw
      simp only [this, Bool.false_eq_true, ↓reduceIte]
    omega
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hv
  have hk' := kk_eq_kloop hT o hj hov
  obtain ⟨V, hV⟩ := rot_idx hov
  refine ⟨j, v, V, hj, hV, ?_⟩
  have h1 : 1 ≤ lseg V := by
    rw [hk'] at hk
    unfold kloop at hk
    have hc : v.contains (.lamt o) = true := by simpa using hov
    simp only [hc, ↓reduceIte, hV, List.drop_one, List.tail_cons] at hk
    exact hk
  unfold lseg at h1
  have := tw_res _ h1
  rw [List.map_reverse, kw, List.filterMap_reverse, List.head?_reverse] at this
  exact this

private theorem kwL_mem (Y : List LoopLetter) (x : Kd) (h : x ∈ kw (Y.map PkgLetter.lw)) :
    x = .g ∨ ∃ k, x = .l k ∧ LoopLetter.lamt k ∈ Y := by
  obtain ⟨z, hz, hk⟩ := mem_kw.1 h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  cases y with
  | res c => simp [kd] at hk; exact Or.inl hk.symm
  | det c => simp [kd] at hk
  | proj c => simp [kd] at hk
  | lamt k =>
    simp only [kd, Option.some.injEq] at hk
    exact Or.inr ⟨k, hk.symm, hy⟩

private theorem kwL_rot {v v' : List LoopLetter} (h : v.IsRotated v') :
    (kw (v.map PkgLetter.lw)).IsRotated (kw (v'.map PkgLetter.lw)) :=
  kw_rot (h.map _)

private theorem count_kwL (k : Fin 2) (v : List LoopLetter) :
    (kw (v.map PkgLetter.lw)).count (.l k) = v.count (.lamt k) := by
  rw [count_kw_l]
  induction v with
  | nil => rfl
  | cons x v ih =>
    simp only [List.map_cons, List.count_cons, ih]
    congr 1
    simp

/-- At the start `(F 𝒢)_{ij} ⋯` of (5.65) [explicit_reminder_terms_before_expansions] with
`k₁, k₂ ≥ 1`, the right side of `Λ̃₁` and both sides of `Λ̃₂` hold resolvents. -/
private theorem base_bits (T : LoopExpr) (hT : T.wf = true) (hk0 : 1 ≤ T.kk 0)
    (hk1 : 1 ≤ T.kk 1) (ℓ : ℕ) (a : Fin 2) (tl : List LoopLetter)
    (hf : T.focus = some (ℓ, a, tl)) :
    PS T.pkgStart (.l 0, .g) ∧ PS T.pkgStart (.g, .l 1) ∧ PS T.pkgStart (.l 1, .g) := by
  obtain ⟨o, o', w, B, Y, hoo, hw, htl, F⟩ := focus_foc hT hf
  obtain ⟨rfl, rfl⟩ : o = 0 ∧ o' = 1 := by
    rcases hoo with ⟨h1, h2, -⟩ | ⟨-, -, h⟩
    · exact ⟨h1, h2⟩
    · omega
  obtain ⟨-, ⟨r, hr⟩, hnlB, hrsB, -⟩ := F
  have hl := pkgStart_loops hf
  have hwm : w ∈ T.loops := List.mem_of_getElem? hw
  have hB : kw (B.map PkgLetter.lw) = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    cases y with
    | res c => exact absurd (List.countP_eq_zero.1 hrsB _ hy) (by simp [rcR])
    | det c => rfl
    | proj z => rfl
    | lamt k => exact absurd hy (hnlB k)
  have hkW : kw (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0]) = (.l 0 :: kw (Y.map PkgLetter.lw)) ++ [.g, .d] := by
    rw [htl]
    simp only [kw, List.filterMap_map] at hB ⊢
    simp [List.filterMap_append, List.filterMap_cons, kd, hB]
  have hW₀m : ((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0] ∈ T.pkgStart.loops := by
    rw [hl]
    exact List.mem_cons_self
  have hwrot : (kw (w.map PkgLetter.lw)).IsRotated (.g :: .l 0 :: kw (Y.map PkgLetter.lw)) := by
    have := kwL_rot (List.IsRotated.forall w r).symm
    rw [hr] at this
    have e : kw ((LoopLetter.res a :: (B ++ LoopLetter.lamt 0 :: Y)).map PkgLetter.lw) =
        Kd.g :: Kd.l 0 :: kw (Y.map PkgLetter.lw) := by
      simp only [List.map_cons, List.map_append]
      rw [show ∀ l, kw (PkgLetter.lw (.res a) :: l) = .g :: kw l from fun _ => rfl, kw_append, hB]
      rfl
    rw [e] at this
    exact this
  have hc0 := count_le_one hT hwm 0
  have hc1 := count_le_one hT hwm 1
  have hcrot : ∀ k, (LoopLetter.res a :: (B ++ LoopLetter.lamt 0 :: Y)).count (.lamt k) ≤ 1 := by
    intro k
    rw [← hr, (List.rotate_perm w r).count_eq]
    exact count_le_one hT hwm k
  have hY0 : LoopLetter.lamt 0 ∉ Y := by
    intro hm
    have := hcrot 0
    simp [List.count_append, List.count_eq_zero.2 (hnlB 0)] at this
    have := List.count_pos_iff.2 hm
    omega
  have h0w : LoopLetter.lamt 0 ∈ w := by
    rw [← List.mem_rotate (n := r), hr]
    simp
  obtain ⟨j, v, V, hj, hV, hlast⟩ := kk_pred T hT 1 hk1
  have hvm : v ∈ T.loops := List.mem_of_getElem? hj
  have h1v : LoopLetter.lamt 1 ∈ v := by
    rw [← List.mem_rotate (n := v.idxOf (.lamt 1)), hV]
    exact List.mem_cons_self
  have hV1 : LoopLetter.lamt 1 ∉ V := by
    intro hm
    have := count_le_one hT hvm 1
    rw [← (List.rotate_perm v (v.idxOf (.lamt 1))).count_eq, hV] at this
    simp at this
    have := List.count_pos_iff.2 hm
    omega
  have hkV1 : Kd.l 1 ∉ kw (V.map PkgLetter.lw) := by
    intro hm
    rcases kwL_mem V _ hm with h | ⟨k, hk, hkV⟩
    · cases h
    · rw [Kd.l.injEq] at hk
      subst hk
      exact hV1 hkV
  have hvrot : (kw (v.map PkgLetter.lw)).IsRotated (.l 1 :: kw (V.map PkgLetter.lw)) := by
    have := kwL_rot (List.IsRotated.forall v (v.idxOf (.lamt 1))).symm
    rw [hV] at this
    exact this
  have hpred : CP (kw (v.map PkgLetter.lw)) (.g, .l 1) := by
    rw [CP_rot hvrot, CP_x_snd _ _ _ hkV1]
    rcases hk : kw (V.map PkgLetter.lw) with _ | ⟨z, Z⟩
    · rw [hk] at hlast
      simp at hlast
    · rw [hk] at hlast
      rw [List.getLast?_cons_cons]
      exact hlast
  by_cases hjℓ : j = ℓ
  · subst hjℓ
    rw [hw] at hj
    cases hj
    -- `Λ̃₂` lies in the focused loop, in `Y`
    have hlp : (Kd.g, Kd.l 1) ∈ lp (.l 0 :: kw (Y.map PkgLetter.lw)) := by
      rw [CP_rot hwrot, CP_gcons _ (by simp)] at hpred
      rcases hpred with ⟨-, h⟩ | h | ⟨-, h⟩
      · simp at h
      · exact h
      · cases h
    have hY1 : (kw (Y.map PkgLetter.lw)).count (.l 1) ≤ 1 := by
      rw [count_kwL]
      have := hcrot 1
      simp [List.count_append, List.count_eq_zero.2 (hnlB 1)] at this
      omega
    have hYg : ∀ x ∈ kw (Y.map PkgLetter.lw), x = .g ∨ x = .l 1 := by
      intro x hx
      rcases kwL_mem Y x hx with h | ⟨k, rfl, hk⟩
      · exact Or.inl h
      · rcases (by decide : ∀ o : Fin 2, o = 0 ∨ o = 1) k with rfl | rfl
        · exact absurd hk hY0
        · exact Or.inr rfl
    refine ⟨⟨_, hW₀m, ?_⟩, ⟨_, hW₀m, ?_⟩, ⟨_, hW₀m, ?_⟩⟩
    · rw [hkW]
      left
      rcases hk : kw (Y.map PkgLetter.lw) with _ | ⟨y, Z⟩
      · simp [lp]
      · rw [hk] at hlp hYg hY1
        rcases hYg y (by simp) with rfl | rfl
        · simp [lp]
        · exfalso
          simp only [lp, List.mem_cons, Prod.mk.injEq, reduceCtorEq, false_and, false_or] at hlp
          have h3 : Kd.l 1 ∈ Z := (lp_mem _ _ _ hlp).2
          have h2 := List.count_pos_iff.2 h3
          rw [List.count_cons_self] at hY1
          omega
    · rw [hkW]
      left
      rw [mem_lp_append]
      exact Or.inl hlp
    · rw [hkW]
      left
      have hm : Kd.l 1 ∈ kw (Y.map PkgLetter.lw) := (lp_mem _ _ _ hlp).2
      obtain ⟨A, B', hAB⟩ := List.append_of_mem hm
      have e : (Kd.l 0 :: kw (Y.map PkgLetter.lw)) ++ [Kd.g, Kd.d] =
          (Kd.l 0 :: A) ++ (Kd.l 1 :: (B' ++ [Kd.g, Kd.d])) := by
        rw [hAB]
        simp
      rw [e, mem_lp_append]
      right
      left
      rcases B' with _ | ⟨z, B'⟩
      · simp [lp]
      · have hz : z = .g := by
          rcases hYg z (by rw [hAB]; simp) with h | h
          · exact h
          · exfalso
            rw [hAB, h] at hY1
            simp [List.count_append] at hY1
            omega
        subst hz
        simp [lp]
  · -- `Λ̃₂` lies in another loop `v`
    have h1w : LoopLetter.lamt 1 ∉ w := uniq_loop hT 1 hj h1v ℓ w (Ne.symm hjℓ) hw
    have h0v : LoopLetter.lamt 0 ∉ v := uniq_loop hT 0 hw h0w j v hjℓ hj
    have hvm' : v.map PkgLetter.lw ∈ T.pkgStart.loops := by
      rw [hl]
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem
        (List.mem_eraseIdx_iff_getElem?.2 ⟨j, hjℓ, hj⟩))
    have hVg : ∀ x ∈ kw (V.map PkgLetter.lw), x = .g := by
      intro x hx
      rcases kwL_mem V x hx with h | ⟨k, rfl, hk⟩
      · exact h
      · rcases (by decide : ∀ o : Fin 2, o = 0 ∨ o = 1) k with rfl | rfl
        · exfalso
          apply h0v
          rw [← List.mem_rotate (n := v.idxOf (.lamt 1)), hV]
          exact List.mem_cons_of_mem _ hk
        · exact absurd hk hV1
    have hYg : ∀ x ∈ kw (Y.map PkgLetter.lw), x = .g := by
      intro x hx
      rcases kwL_mem Y x hx with h | ⟨k, rfl, hk⟩
      · exact h
      · rcases (by decide : ∀ o : Fin 2, o = 0 ∨ o = 1) k with rfl | rfl
        · exact absurd hk hY0
        · exfalso
          apply h1w
          rw [← List.mem_rotate (n := r), hr]
          simp [hk]
    refine ⟨⟨_, hW₀m, ?_⟩, ⟨_, hvm', hpred⟩, ⟨_, hvm', ?_⟩⟩
    · rw [hkW]
      left
      rcases hk : kw (Y.map PkgLetter.lw) with _ | ⟨y, Z⟩
      · simp [lp]
      · rw [hk] at hYg
        rw [hYg y (by simp)]
        simp [lp]
    · rw [CP_rot hvrot, CP_x_fst _ _ _ hkV1]
      rcases hk : kw (V.map PkgLetter.lw) with _ | ⟨z, Z⟩
      · rw [hk] at hlast
        simp at hlast
      · rw [hk] at hVg
        rw [hVg z (by simp)]
        rfl

/-- One derivative `∂` keeps every cyclically consecutive pair of kinds: `𝒢` becomes `𝒢 Δ 𝒢`. -/
private theorem ps_dent (R R' : PkgExpr) (u v : ℕ) (h : R' ∈ R.dent u v) (p : Kd × Kd)
    (hp : PS R p) : PS R' p := by
  rcases dent_cases R R' u v h with ⟨ℓ, X, Y, a, hℓ, hl⟩ | ⟨b, y, hl⟩
  · unfold PS at hp ⊢
    rw [ex_get R.loops (fun w => CP (kw w) p) ℓ _ hℓ] at hp
    rw [hl, ex_set R.loops (fun w => CP (kw w) p) ℓ _ _ hℓ]
    rcases hp with hp | hp
    · left
      have e1 : kw (X ++ .lw (.res a) :: Y) = kw X ++ .g :: kw Y := by
        rw [kw_append]
        rfl
      have e2 : kw (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) =
          kw X ++ .g :: .d :: .g :: kw Y := by
        rw [kw_append, kw_append]
        simp only [List.append_assoc]
        rfl
      simp only [e1] at hp
      simp only [e2]
      rw [CP_comm] at hp ⊢
      have e3 : (Kd.g :: .d :: .g :: kw Y) ++ kw X = [.g, .d] ++ (.g :: (kw Y ++ kw X)) := by
        simp
      rw [e3, CP_J _ _ (by simp) (by simp) (Or.inl ⟨rfl, rfl⟩)]
      right
      simpa using hp
    · exact Or.inr hp
  · obtain ⟨w, hw, hc⟩ := hp
    exact ⟨w, by rw [hl]; exact List.mem_append_left _ hw, hc⟩

private theorem ps_iter (u v : ℕ) (p : Kd × Kd) : ∀ (n : ℕ) (L : List PkgExpr),
    (∀ R ∈ L, PS R p) →
    ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[n] L, PS R p
  | 0, L, hL, R, hR => hL R hR
  | n + 1, L, hL, R, hR => by
      rw [Function.iterate_succ_apply] at hR
      refine ps_iter u v p n _ ?_ R hR
      intro R' hR'
      obtain ⟨R'', hR'', hd⟩ := List.mem_flatMap.1 hR'
      exact ps_dent R'' R' u v hd p (hL R'' hR'')

private theorem ps_dwirt (T : LoopExpr) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (pp : Kd × Kd) (h : PS T.pkgStart pp) : PS R pp := by
  unfold PkgExpr.dwirt at hR
  refine ps_iter 0 1 pp p _ (fun R₁ hR₁ => ?_) R hR
  refine ps_iter 1 0 pp q [T.pkgStart] ?_ R₁ hR₁
  intro R₂ hR₂
  rw [List.mem_singleton.1 hR₂]
  exact h

/-- The invariant: the class `𝓡`, (C1), (I1)–(I4), and (I5q) `#(empty sides) ≤ fR`. -/
private def Inv (S : PkgExpr) : Prop :=
  S.wf = true ∧ ArcInv S ∧ OrdB S ∧ (EB S : ℤ) ≤ S.fR

/-- `𝓡₀` has no empty side, so the invariant holds there. -/
private theorem inv_start (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) : Inv R₀ := by
  have hTw := reach_wf ε n T hT
  have hk0 := reach_kk ε n T hT hR0
  have hk1 := (loop_reach ε n T (Or.inr hT)).2.1 hk0
  have hfoc := focus_isSome T p₀ q₀ hpq R₀ hR₀
  obtain ⟨⟨ℓ, a, tl⟩, hf⟩ := Option.isSome_iff_exists.1 hfoc
  obtain ⟨b0, b1, b2⟩ := base_bits T hTw hk0 hk1 ℓ a tl hf
  have s0 : SB R₀ 0 true := ps_dwirt T p₀ q₀ R₀ hR₀ _ b0
  have s1 : SB R₀ 1 false := ps_dwirt T p₀ q₀ R₀ hR₀ _ b1
  have s2 : SB R₀ 1 true := ps_dwirt T p₀ q₀ R₀ hR₀ _ b2
  have hc := pkg_inv_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ 0 R₀ (Or.inl (by simp [fIter]))
  refine ⟨(pkg_table3 T hTw hfoc p₀ q₀ hpq R₀ hR₀).1, arcInv_dwirt T hTw hk0 p₀ q₀ hpq R₀ hR₀,
    ⟨fun _ => ⟨fun _ => ⟨s0, s1⟩, fun h => absurd s1 h⟩, fun _ _ => s0, fun _ _ => s0⟩, ?_⟩
  unfold EB
  rw [ez_of s0, ez_of s1, ez_of s2]
  have := hc.1
  split_ifs <;> simpa using this

/-- One step of the further expansion keeps the invariant: `𝔣𝔯` raises `fR` by one and the number
of empty sides by at most one, every other row of Table 2 [table_effect_of_operations_2] keeps
both. -/
private theorem inv_step (S : PkgExpr) (hS : Inv S) (R' : PkgExpr) (h : R' ∈ S.fstep) :
    Inv R' := by
  obtain ⟨hw, hA, hO, hE⟩ := hS
  have hw' := pkg_step_wf S hw R' h
  have hA' := arcInv_step S hA R' h
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  dsimp only at hw' hA' ⊢
  have hf := fR_term S R'' o hmem
  by_cases ho : o = PkgOp.frep
  · subst ho
    obtain ⟨hO', hE'⟩ := frep_step S R'' hmem hw hA hw' hO
    refine ⟨hw', hA', hO', ?_⟩
    rw [hf.1 rfl]
    have : (EB R'' : ℤ) ≤ (EB S : ℤ) + 1 := by exact_mod_cast hE'
    omega
  · obtain ⟨hO', hE'⟩ := nf_step S R'' o hmem ho hw hA hw' hA' hO
    refine ⟨hw', hA', hO', ?_⟩
    rw [hf.2 ho]
    have : (EB R'' : ℤ) ≤ (EB S : ℤ) := by exact_mod_cast hE'
    omega

/-- (I1)–(I4) of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms], the order in which the rules (i)–(iv) empty the sides of
`Λ̃`: Type I: `a₃ ≥ 1 ⇒ a₁, a₂ ≥ 1` and `a₂ = 0 ⇒ a₁ = a₃ = 0`; Type II: `a₄ ≥ 1 ⇒ a₁ ≥ 1`;
Type III: `a₂ ≥ 1 ⇒ a₁ ≥ 1`. -/
theorem pkg_inv_order (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    (R.ptype = 1 → (1 ≤ R.lamSide 1 true → 1 ≤ R.lamSide 0 true ∧ 1 ≤ R.lamSide 1 false) ∧
      (R.lamSide 1 false = 0 → R.lamSide 0 true = 0 ∧ R.lamSide 1 true = 0)) ∧
    (R.ptype = 2 → 1 ≤ R.lamSide 1 false → 1 ≤ R.lamSide 0 true) ∧
    (R.ptype = 3 → 1 ≤ R.lamSide 1 true → 1 ≤ R.lamSide 0 true) := by
  obtain ⟨hw, -, hO, -⟩ := inv_reach Inv inv_step ε j R₀ R
    (inv_start ε n T hT hR0 p₀ q₀ hpq R₀ hR₀) hR
  have e1 : ∀ o right, (1 ≤ R.lamSide o right ↔ SB R o right) :=
    fun o right => lamSide_pos R o (uo_of_wf R hw o) right
  have e0 : ∀ o right, (R.lamSide o right = 0 ↔ ¬ SB R o right) := fun o right => by
    rw [← e1]
    omega
  simp only [e1, e0]
  exact hO


/-- (I5q) of the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
every empty side next to `Λ̃` costs one replacement `𝔣𝔯`, so `#(empty sides) ≤ fR`; in
particular `fR ≥ 2` at every expression to which no rule applies (the claim before (5.88)
[further_expansion_Type_1]), and `fR ≥ 3` there in Type I. -/
theorem pkg_inv_empty (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    (R.emptySides : ℤ) ≤ R.fR := by
  obtain ⟨hw, -, -, hE⟩ := inv_reach Inv inv_step ε j R₀ R
    (inv_start ε n T hT hR0 p₀ q₀ hpq R₀ hR₀) hR
  have e0 : ∀ o right, (if R.lamSide o right = 0 then 1 else 0) = ez (SB R o right) :=
    fun o right => by
      have := lamSide_pos R o (uo_of_wf R hw o) right
      by_cases h : SB R o right
      · have h1 := this.2 h
        rw [ez_of h]
        simp only [show R.lamSide o right ≠ 0 by omega, ↓reduceIte]
      · have h1 : ¬ 1 ≤ R.lamSide o right := fun h' => h (this.1 h')
        rw [ez_of_not h]
        simp only [show R.lamSide o right = 0 by omega, ↓reduceIte]
  have hEB : R.emptySides = EB R := by
    unfold PkgExpr.emptySides EB
    rcases (ptype_cases R (uo_of_wf R hw 0) (uo_of_wf R hw 1)).2.2 with h | h | h <;>
      simp only [h, ↓reduceIte, Nat.reduceEqDiff, List.count_cons, List.count_nil, beq_iff_eq,
        ← e0] <;> omega
  rw [hEB]
  exact hE


/-- (I6) of the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]: a
loop with `Λ̃₂` needs an operation other than `𝔣𝔯`, so `Σ ≥ 1` in Type II
((5.80) [further_expansion_expression_Type_2], [sum_geq_1_because_of_a_loop_containing_tl_2]). -/
theorem pkg_inv_typeII (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) (hty : R.ptype = 2) : 1 ≤ R.fsig := by
  have hc := pkg_inv_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ 0 R₀ (Or.inl (by simp [fIter]))
  have h0 : SigInv R₀ := by
    refine ⟨hc.2.2.1, fun hA => ?_⟩
    by_contra hlt
    have hz : R₀.fsig = 0 := by
      have := hc.2.2.1
      omega
    have hT' := hc.2.2.2.2.1
    rw [hz] at hT'
    have hTl : T = loopStart := by simpa [loopTree] using hT'
    subst hTl
    obtain ⟨w, hl, he, -⟩ := single_start p₀ q₀ R₀ hR₀
    obtain ⟨L, hL, -, hL2⟩ := hA
    rw [hl, List.mem_singleton] at hL
    subst hL
    rw [List.any_eq_false] at hL2
    exact absurd rfl (hL2 _ he)
  exact (inv_reach SigInv sigInv_step ε j R₀ R h0 hR).2 (alpha_of_ptype R hty)

end RBMTransitionEdge

end
