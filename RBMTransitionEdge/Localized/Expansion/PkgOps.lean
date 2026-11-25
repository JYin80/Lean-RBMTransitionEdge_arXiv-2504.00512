module

public import RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# The operations of the further expansion in the proof of Lemma 5.5

The rules (i)–(iv) for the resolvent to expand, the eleven operations of Table 2
[table_effect_of_operations_2] as the terms of one Gaussian integration by parts ((5.83)
[concrete_expansion_tl_2_heavy_package_right], (5.84) [concrete_expansion_tl_2_loop]), the Type
of (5.79)–(5.81), Table 2, and the closure of the class under the operations.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The first resolvent cyclically to the right (`right = true`) or to the left of position `i` of
the word `w`, before the next letter `Δ` or `Λ̃`: the search of the rules (i)–(iv) of the further
expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def pkgSeek (w : List PkgLetter) (i : ℕ) (right : Bool) : Option ℕ :=
  (((List.range (w.length - 1)).map fun j =>
      if right then (i + 1 + j) % w.length else (i + w.length - 1 - j) % w.length).takeWhile
    fun r => match w[r]? with
      | some (PkgLetter.ent _ _) => false | some (PkgLetter.lw (LoopLetter.lamt _)) => false
      | _ => true).find? fun r =>
    match w[r]? with | some (PkgLetter.lw (LoopLetter.res _)) => true | _ => false

/-- The rules (i)–(iv) of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the loop `ℓ`, the position `r` of the chosen resolvent, and
whether it lies to the right of its `Λ̃` (expanded by `𝒢 = 𝔐 - 𝔐(H + m)𝒢`) or to the left
(`𝒢 = 𝔐 - 𝒢(H + m)𝔐`); `none` when no rule applies. -/
def PkgExpr.ffocus (R : PkgExpr) : Option (ℕ × ℕ × Bool) :=
  let ℓ₂ := R.loops.findIdx fun w => w.contains (.lw (.lamt 1))
  let ℓ₁ := R.loops.findIdx fun w => w.contains (.lw (.lamt 0))
  match R.loops[ℓ₂]?, R.loops[ℓ₁]? with
  | some w₂, some w₁ =>
    let i₂ := w₂.idxOf (.lw (.lamt 1))
    let i₁ := w₁.idxOf (.lw (.lamt 0))
    if w₂.any (fun x => match x with | .ent _ _ => true | _ => false) then
      match pkgSeek w₂ i₂ true with
      | some r => some (ℓ₂, r, true)
      | none => match pkgSeek w₁ i₁ true with
        | some r => some (ℓ₁, r, true)
        | none => match pkgSeek w₂ i₂ false with
          | some r => some (ℓ₂, r, false)
          | none => none
    else
      match pkgSeek w₂ i₂ false with
      | some r => some (ℓ₂, r, false)
      | none => match pkgSeek w₁ i₁ true with
        | some r => some (ℓ₁, r, true)
        | none => none
  | _, _ => none

/-- The eleven operations of Table 2 [table_effect_of_operations_2]:
`𝔣𝔯, 𝔣𝔠₁, 𝔣𝔠₂, 𝔣𝔭₁, 𝔣𝔭₂, 𝔪𝔢𝔯𝔤𝔢, 𝔰𝔩𝔞𝔰𝔥₁, 𝔰𝔩𝔞𝔰𝔥₂, 𝔦𝔫𝔰𝔢𝔯𝔱₁, 𝔦𝔫𝔰𝔢𝔯𝔱₂, 𝔢𝔵𝔠𝔥𝔞𝔫𝔤𝔢`. -/
inductive PkgOp
  | frep
  | fcut1
  | fcut2
  | fplug1
  | fplug2
  | merge
  | slash1
  | slash2
  | insert1
  | insert2
  | exchange
  deriving DecidableEq

/-- The rows of Table 2 [table_effect_of_operations_2]: the change of `(m, n, u, S)`. -/
def PkgOp.delta : PkgOp → ℤ × ℤ × ℤ × ℤ
  | .frep => (-1, 0, 0, 0)
  | .fcut1 => (0, 0, 1, 0)
  | .fcut2 => (1, 1, 0, 0)
  | .fplug1 => (2, 0, -1, 2)
  | .fplug2 => (1, -1, 0, 2)
  | .merge => (1, -1, 0, 2)
  | .slash1 => (0, 0, 1, 0)
  | .slash2 => (1, 1, 0, 0)
  | .insert1 => (2, 0, -1, 2)
  | .insert2 => (1, -1, 0, 2)
  | .exchange => (1, 0, 0, 1)

/-- The Gaussian integration by parts terms of (5.83)
[concrete_expansion_tl_2_heavy_package_right] and (5.84) [concrete_expansion_tl_2_loop] at the
resolvent chosen by `ffocus`, each with its operation: the replacement, the light weight, the cut at
each other resolvent of the expanded word, the plug of each light weight, and the join with each
resolvent of each other word; the coefficient changes by `N⁻¹ (DN)^d`, `d` the change in the number
of factors `⟨·⟩`. -/
def PkgExpr.fterms (R : PkgExpr) : List (PkgOp × PkgExpr) :=
  match R.ffocus with
  | none => []
  | some (ℓ, r, right) =>
    match R.loops[ℓ]? with
    | none => []
    | some w =>
      match w.rotate r with
      | .lw (.res a) :: tl =>
        let pl : List PkgLetter → Bool :=
          fun v => !(v.any fun x => match x with | .ent _ _ => true | _ => false)
        let W : List PkgLetter := if right then .lw (.res a) :: tl ++ [.lw (.det a)]
          else .lw (.det a) :: tl ++ [.lw (.res a)]
        let px : PkgLetter := .lw (.proj R.nb)
        [(PkgOp.frep, { R with loops := R.loops.set ℓ (.lw (.det a) :: tl) }),
          (if pl w then PkgOp.fcut1 else PkgOp.slash1,
            { R with
              dexp := R.dexp + 1, nb := R.nb + 1, weights := R.weights ++ [(a, R.nb)],
              loops := R.loops.set ℓ (if right then px :: W else W ++ [px]) })] ++
        ((List.range W.length).filterMap fun q =>
          if (right && q == 0) || (!right && q + 1 == W.length) then none else
          match W[q]? with
          | some (PkgLetter.lw (LoopLetter.res _)) =>
            let d : ℤ := (if pl (W.take (q + 1) ++ [px]) then 1 else 0) +
              (if pl (px :: W.drop q) then 1 else 0) - (if pl w then 1 else 0)
            some (if pl (W.take (q + 1) ++ [px]) && pl (px :: W.drop q) then PkgOp.fcut2
                else if pl (W.take (q + 1) ++ [px]) || pl (px :: W.drop q) then PkgOp.slash2
                else PkgOp.exchange,
              { R with
                dexp := R.dexp + d, S := R.S + 1 - d, nb := R.nb + 1,
                loops := R.loops.set ℓ (W.take (q + 1) ++ [px]) ++ [px :: W.drop q] })
          | _ => none) ++
        ((List.range R.weights.length).filterMap fun j =>
          match R.weights[j]? with
          | some (b, y) => some (if pl w then PkgOp.fplug1 else PkgOp.insert1,
              { R with
                dexp := R.dexp - 1, S := R.S + 2, nb := R.nb + 1, weights := R.weights.eraseIdx j,
                loops := R.loops.set ℓ (W ++ [px, .lw (.res b), .lw (.proj y), .lw (.res b), px]) })
          | none => none) ++
        ((List.range R.loops.length).flatMap fun j =>
          if j = ℓ then [] else
          match R.loops[j]? with
          | none => []
          | some f => (List.range f.length).filterMap fun q =>
            match f[q]? with
            | some (PkgLetter.lw (LoopLetter.res b)) =>
              let d : ℤ := (if pl (W ++ [px] ++ f.rotate q ++ [.lw (.res b), px]) then 1 else 0) -
                (if pl w then 1 else 0) - (if pl f then 1 else 0)
              some (if pl w then (if pl f then PkgOp.fplug2 else PkgOp.merge)
                  else (if pl f then PkgOp.insert2 else PkgOp.exchange),
                { R with
                  dexp := R.dexp + d, S := R.S + 1 - d, nb := R.nb + 1,
                  loops := (R.loops.set ℓ (W ++ [px] ++ f.rotate q ++ [.lw (.res b), px])).eraseIdx
                    j })
            | _ => none)
      | _ => []

/-- All Gaussian integration by parts terms of one step of the further expansion. -/
def PkgExpr.fstep (R : PkgExpr) : List PkgExpr :=
  R.fterms.map Prod.snd

/-- The Type of (5.79)–(5.81): `2` if `Λ̃₂` lies in a loop `⟨·⟩` (Type II), `3` if `Λ̃₁` and `Λ̃₂`
lie in one heavy package (Type III), `1` otherwise (Type I). -/
def PkgExpr.ptype (R : PkgExpr) : ℕ :=
  match R.loops.find? (fun w => w.contains (.lw (.lamt 1))) with
  | none => 0
  | some w₂ =>
    if !(w₂.any fun x => match x with | .ent _ _ => true | _ => false) then 2
    else if w₂.contains (.lw (.lamt 0)) &&
        (((w₂.rotate (w₂.idxOf (.lw (.lamt 0)))).drop 1).takeWhile fun x =>
          match x with | .ent _ _ => false | _ => true).contains (.lw (.lamt 1)) then 3
    else 1

/-! ### Auxiliary facts: the letters of a word and the summary of its cyclic segments -/

/-- The letter `x` is a matrix `Δ`. -/
private def isEntP (x : PkgLetter) : Bool :=
  match x with | .ent _ _ => true | _ => false

/-- The letter `x` is a resolvent `𝒢_a`. -/
private def isResP (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | _ => false

/-- The letter `x` is a resolvent or a `Λ̃`. -/
private def isGoodP (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | .lw (.lamt _) => true | _ => false

/-- The word `v` has no letter `Δ` (a loop `⟨·⟩`). -/
private def plB (v : List PkgLetter) : Bool := !(v.any isEntP)

/-- The factor of a word in the number `n` of factors: each package, and each word without `Δ`
once. -/
private def nfac (w : List PkgLetter) : ℕ :=
  if w.any isEntP then w.countP isEntP else 1

/-- The summary of a list of letters, read as a word cut at its letters `Δ`: it has a `Δ`, the part
before the first `Δ` contains a resolvent or a `Λ̃`, the part after the last `Δ` does, and all the
parts between two letters `Δ` do. -/
private structure Sm where
  e : Bool
  pre : Bool
  suf : Bool
  mid : Bool
  deriving DecidableEq, Fintype

/-- The summary of the empty list. -/
private def Sm.nil : Sm := ⟨false, false, false, true⟩

/-- The summary of a list after one more letter in front. -/
private def Sm.step (ie ig : Bool) (s : Sm) : Sm :=
  if ie then ⟨true, false, if s.e then s.suf else s.pre, if s.e then s.pre && s.mid else true⟩
  else ⟨s.e, ig || s.pre, if s.e then s.suf else ig || s.pre, s.mid⟩

/-- The summary of the concatenation of two lists. -/
private def Sm.comb (s t : Sm) : Sm :=
  ⟨s.e || t.e, if s.e then s.pre else s.pre || t.pre, if t.e then t.suf else t.suf || s.suf,
    s.mid && t.mid && (if s.e && t.e then s.suf || t.pre else true)⟩

/-- A summary of a list without `Δ` has equal `pre` and `suf`, and no parts between letters `Δ`. -/
private def Sm.Inv (s : Sm) : Prop := s.e = false → s.suf = s.pre ∧ s.mid = true

private instance (s : Sm) : Decidable s.Inv := by unfold Sm.Inv; infer_instance

/-- All segments of a list, cut at its letters `Δ`, are good. -/
private def Sm.lin (s : Sm) : Bool := if s.e then s.pre && s.mid && s.suf else s.pre

/-- All cyclic segments of a word are good. -/
private def Sm.ok (s : Sm) : Bool := if s.e then s.mid && (s.pre || s.suf) else s.pre

/-- The summary of a list of letters. -/
private def summ : List PkgLetter → Sm
  | [] => Sm.nil
  | x :: l => Sm.step (isEntP x) (isGoodP x) (summ l)

private theorem summ_nil : summ [] = Sm.nil := rfl
private theorem summ_cons (x : PkgLetter) (l : List PkgLetter) :
    summ (x :: l) = Sm.step (isEntP x) (isGoodP x) (summ l) := rfl

private theorem step_inv (ie ig : Bool) (s : Sm) (h : s.Inv) : (Sm.step ie ig s).Inv := by
  revert s h ie ig; decide

private theorem summ_inv : ∀ l : List PkgLetter, (summ l).Inv
  | [] => by decide
  | x :: l => step_inv _ _ _ (summ_inv l)

private theorem step_comb (ie ig : Bool) (s t : Sm) (hs : s.Inv) (ht : t.Inv) :
    Sm.step ie ig (Sm.comb s t) = Sm.comb (Sm.step ie ig s) t := by
  revert s t hs ht ie ig; decide

private theorem nil_comb (s : Sm) : Sm.comb Sm.nil s = s := by
  revert s; decide

private theorem summ_append (U V : List PkgLetter) : summ (U ++ V) = Sm.comb (summ U) (summ V) := by
  induction U with
  | nil => rw [List.nil_append, summ_nil, nil_comb]
  | cons x U ih =>
    rw [List.cons_append, summ_cons, ih, summ_cons, step_comb _ _ _ _ (summ_inv U) (summ_inv V)]

private theorem isEntP_ent (u v : ℕ) : isEntP (.ent u v) = true := rfl
private theorem isEntP_lw (x : LoopLetter) : isEntP (.lw x) = false := rfl
private theorem isGoodP_res (a : Fin 2) : isGoodP (.lw (.res a)) = true := rfl
private theorem isGoodP_det (a : Fin 2) : isGoodP (.lw (.det a)) = false := rfl
private theorem isGoodP_proj (a : ℕ) : isGoodP (.lw (.proj a)) = false := rfl
private theorem isGoodP_ent (u v : ℕ) : isGoodP (.ent u v) = false := rfl
private theorem isResP_res (a : Fin 2) : isResP (.lw (.res a)) = true := rfl
private theorem isResP_det (a : Fin 2) : isResP (.lw (.det a)) = false := rfl
private theorem isResP_proj (a : ℕ) : isResP (.lw (.proj a)) = false := rfl

/-- Every segment cut out by the letters `Δ` of a list contains a resolvent or a `Λ̃`. -/
private def segsOK (l : List PkgLetter) : Bool :=
  (l.splitOnP isEntP).all fun v => v.any isGoodP

/-- The condition on the packages of one word in `PkgExpr.wf`: a word without `Δ` contains a
resolvent or a `Λ̃`, a word with `Δ` has this in each of its cyclic segments. -/
private def segOK (w : List PkgLetter) : Bool :=
  (if w.any isEntP then (w.rotate (w.findIdx isEntP + 1)).dropLast.splitOnP isEntP else [w]).all
    fun v => v.any isGoodP

private theorem splitOnP_summ : ∀ l : List PkgLetter, ∃ h t, l.splitOnP isEntP = h :: t ∧
    h.any isGoodP = (summ l).pre ∧
      t.all (fun v => v.any isGoodP) = (if (summ l).e then (summ l).mid && (summ l).suf else true)
  | [] => ⟨[], [], by simp [summ, Sm.nil]⟩
  | x :: l => by
      obtain ⟨h, t, h1, h2, h3⟩ := splitOnP_summ l
      match x with
      | .ent u v =>
          refine ⟨[], h :: t, ?_, ?_, ?_⟩
          · rw [List.splitOnP_cons_eq_ite_modifyHead, h1]
            simp [isEntP_ent]
          · simp [summ_cons, Sm.step, isEntP_ent]
          · simp only [summ_cons, Sm.step, isEntP_ent, ite_true, List.all_cons, h2, h3]
            cases (summ l).e <;> simp [Bool.and_assoc]
      | .lw y =>
          refine ⟨.lw y :: h, t, ?_, ?_, ?_⟩
          · rw [List.splitOnP_cons_eq_ite_modifyHead, h1]
            simp [isEntP_lw]
          · simp [summ_cons, Sm.step, isEntP_lw, h2]
          · simp only [summ_cons, Sm.step, isEntP_lw, Bool.false_eq_true, ite_false, h3]
            cases (summ l).e <;> simp

private theorem segsOK_eq (l : List PkgLetter) : segsOK l = (summ l).lin := by
  obtain ⟨h, t, h1, h2, h3⟩ := splitOnP_summ l
  unfold segsOK
  rw [h1, List.all_cons, h2, h3]
  unfold Sm.lin
  cases (summ l).e <;> simp [Bool.and_assoc]

private theorem summ_free (w : List PkgLetter) (h : ∀ z ∈ w, isEntP z = false) :
    summ w = ⟨false, w.any isGoodP, w.any isGoodP, true⟩ := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [summ_cons, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)), h x (List.mem_cons_self)]
    simp [Sm.step, List.any_cons]

/-- A list with a letter `Δ` splits at it. -/
private theorem exists_first_ent : ∀ w : List PkgLetter, w.any isEntP = true →
    ∃ (P : List PkgLetter) (x y : ℕ) (Q : List PkgLetter),
      (∀ z ∈ P, isEntP z = false) ∧ w = P ++ .ent x y :: Q
  | [], h => by simp at h
  | z :: w, h => by
      match z with
      | .ent x y => exact ⟨[], x, y, w, by simp, rfl⟩
      | .lw z' =>
          have h' : w.any isEntP = true := by simpa [isEntP] using h
          obtain ⟨P, x, y, Q, hP, hw⟩ := exists_first_ent w h'
          refine ⟨.lw z' :: P, x, y, Q, ?_, by simp [hw]⟩
          intro t ht
          rcases List.mem_cons.1 ht with rfl | ht
          · rfl
          · exact hP t ht

private theorem findIdx_ent (P Q : List PkgLetter) (u v : ℕ) (hP : ∀ y ∈ P, isEntP y = false) :
    (P ++ .ent u v :: Q).findIdx isEntP = P.length := by
  induction P with
  | nil => simp [List.findIdx_cons, isEntP_ent]
  | cons z P ih =>
      rw [List.cons_append, List.findIdx_cons, hP z (List.mem_cons_self)]
      simp [ih (fun y hy => hP y (List.mem_cons_of_mem _ hy))]

/-- The cyclic segments of `P Δ Q` with `P` free of `Δ`: those of `Q P`. -/
private theorem segOK_first (P Q : List PkgLetter) (u v : ℕ) (hP : ∀ y ∈ P, isEntP y = false) :
    segOK (P ++ .ent u v :: Q) = segsOK (Q ++ P) := by
  unfold segOK
  have h1 : (P ++ .ent u v :: Q).any isEntP = true := by simp [isEntP]
  simp only [h1, ↓reduceIte, findIdx_ent P Q u v hP]
  have h2 : (P ++ .ent u v :: Q).rotate (P.length + 1) = (Q ++ P) ++ [.ent u v] := by
    rw [List.rotate_eq_drop_append_take (by simp)]
    have e0 : P ++ .ent u v :: Q = (P ++ [.ent u v]) ++ Q := by simp
    have e1 : (P ++ .ent u v :: Q).drop (P.length + 1) = Q := by
      rw [e0]; exact List.drop_left' (by simp)
    have e2 : (P ++ .ent u v :: Q).take (P.length + 1) = P ++ [.ent u v] := by
      rw [e0]; exact List.take_left' (by simp)
    rw [e1, e2]; simp
  rw [h2, List.dropLast_concat]
  rfl

private theorem segOK_eq (w : List PkgLetter) : segOK w = (summ w).ok := by
  cases hw : w.any isEntP
  · have hfree : ∀ z ∈ w, isEntP z = false := by
      intro z hz
      by_contra hne
      have : w.any isEntP = true := List.any_eq_true.2 ⟨z, hz, by simpa using hne⟩
      rw [this] at hw
      exact absurd hw (by simp)
    rw [summ_free w hfree]
    unfold segOK
    simp [hw, Sm.ok]
  · obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent w hw
    rw [segOK_first P Q x y hP, segsOK_eq, summ_append, summ_append, summ_free P hP, summ_cons]
    have hQ := summ_inv Q
    generalize summ Q = sQ at hQ ⊢
    simp only [isEntP_ent, isGoodP_ent]
    revert sQ hQ
    generalize P.any isGoodP = p
    revert p
    decide

private theorem ok_comm (s t : Sm) (hs : s.Inv) (ht : t.Inv) :
    (Sm.comb s t).ok = (Sm.comb t s).ok := by
  revert s t hs ht; decide

private theorem cyc_append_comm (A B : List PkgLetter) :
    (summ (A ++ B)).ok = (summ (B ++ A)).ok := by
  rw [summ_append, summ_append, ok_comm _ _ (summ_inv A) (summ_inv B)]

/-- The cyclic segments of a word do not change under a rotation. -/
private theorem cyc_rotate (w : List PkgLetter) (n : ℕ) : (summ (w.rotate n)).ok = (summ w).ok := by
  rw [List.rotate_eq_drop_append_take_mod, cyc_append_comm, List.take_append_drop]

/-- The block indices of the letters `proj` in the word `w` are all `< nb`. -/
private def projOK (nb : ℕ) (w : List PkgLetter) : Prop :=
  ∀ y : ℕ, PkgLetter.lw (.proj y) ∈ w → y < nb

/-- The class `𝓡` as a proposition. -/
private structure WfP (R : PkgExpr) : Prop where
  lam0 : (R.loops.map fun w => w.count (.lw (.lamt 0))).sum = 1
  lam1 : (R.loops.map fun w => w.count (.lw (.lamt 1))).sum = 1
  seg : ∀ w ∈ R.loops, (summ w).ok = true
  proj : ∀ w ∈ R.loops, projOK R.nb w
  wt : ∀ p ∈ R.weights, p.2 < R.nb

private theorem projOK_iff (nb : ℕ) (w : List PkgLetter) :
    (w.all fun x => match x with | .lw (.proj y) => decide (y < nb) | _ => true) = true ↔
      projOK nb w := by
  rw [List.all_eq_true]
  constructor
  · intro h y hy
    simpa using h _ hy
  · intro h x hx
    match x, hx with
    | .lw (.proj y), hx => simpa using h y hx
    | .lw (.res _), _ => rfl
    | .lw (.det _), _ => rfl
    | .lw (.lamt _), _ => rfl
    | .ent _ _, _ => rfl

private theorem wf_iff (R : PkgExpr) : R.wf = true ↔ WfP R := by
  unfold PkgExpr.wf
  change ((R.loops.map fun w => w.count (.lw (.lamt 0))).sum == 1 &&
      (R.loops.map fun w => w.count (.lw (.lamt 1))).sum == 1 && R.loops.all segOK &&
      R.loops.all (fun w => w.all fun x => match x with
        | .lw (.proj y) => decide (y < R.nb) | _ => true) &&
      R.weights.all fun p => decide (p.2 < R.nb)) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, segOK_eq]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
    exact ⟨h0, h1, h2, fun w hw => (projOK_iff _ _).1 (List.all_eq_true.2 (h3 w hw)), h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, fun w hw => List.all_eq_true.1 ((projOK_iff _ _).2 (h3 w hw))⟩, h4⟩

/-! ### Auxiliary facts: sums over lists, positions -/

/-- Replacing the entry `w` at position `i` of a list changes a sum of values by the difference of
the values. -/
private theorem sum_map_set {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (i : ℕ) (w x : α), l[i]? = some w →
      ((l.set i x).map f).sum + f w = (l.map f).sum + f x
  | [], i, w, x, h => by simp at h
  | y :: l, 0, w, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
  | y :: l, i + 1, w, x, h => by
      have := sum_map_set f l i w x (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- Erasing the entry `w` at position `i` of a list removes its value from a sum. -/
private theorem sum_map_eraseIdx {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (i : ℕ) (w : α), l[i]? = some w →
      ((l.eraseIdx i).map f).sum + f w = (l.map f).sum
  | [], i, w, h => by simp at h
  | y :: l, 0, w, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.eraseIdx_cons_zero, List.map_cons, List.sum_cons]
      omega
  | y :: l, i + 1, w, h => by
      have := sum_map_eraseIdx f l i w (by simpa using h)
      simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons]
      omega

private theorem free_of_any {l : List PkgLetter} (h : l.any isEntP = false) :
    ∀ z ∈ l, isEntP z = false := by
  intro z hz
  by_contra hne
  have : l.any isEntP = true := List.any_eq_true.2 ⟨z, hz, by simpa using hne⟩
  rw [this] at h
  exact absurd h (by simp)

/-- The number of factors of a word with `e` letters `Δ`: `e` plus one if there is none. -/
private theorem nfac_eq (v : List PkgLetter) :
    nfac v = v.countP isEntP + (if plB v then 1 else 0) := by
  unfold nfac plB
  cases h : v.any isEntP
  · have : v.countP isEntP = 0 := by
      rw [List.countP_eq_zero]
      intro z hz
      simp [free_of_any h z hz]
    simp [this]
  · simp

private theorem plB_iff (v : List PkgLetter) : plB v = true ↔ v.countP isEntP = 0 := by
  unfold plB
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, List.any_eq_true, List.countP_eq_zero]
  simp

private theorem plB_append (U V : List PkgLetter) : plB (U ++ V) = (plB U && plB V) := by
  unfold plB
  simp [List.any_append]

private theorem plB_cons_lw (x : LoopLetter) (V : List PkgLetter) : plB (.lw x :: V) = plB V := by
  unfold plB
  simp [List.any_cons, isEntP_lw]

private theorem plB_eq (v : List PkgLetter) : plB v = decide (v.countP isEntP = 0) := by
  cases h : plB v
  · simp only [Bool.false_eq, decide_eq_false_iff_not]
    intro h'
    rw [← plB_iff, h] at h'
    exact Bool.false_ne_true h'
  · simpa [plB_iff] using h

private theorem plB_perm {U V : List PkgLetter} (h : U.Perm V) : plB U = plB V := by
  rw [plB_eq, plB_eq, h.countP_eq]

/-- The word `W` of the terms of a further expansion: the word of the resolvent to expand with a
`𝔐` on the side of `Λ̃`. -/
private def wordW (right : Bool) (a : Fin 2) (tl : List PkgLetter) : List PkgLetter :=
  if right then .lw (.res a) :: tl ++ [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]

private theorem wordW_perm (right : Bool) (a : Fin 2) (tl : List PkgLetter) :
    (wordW right a tl).Perm (.lw (.det a) :: .lw (.res a) :: tl) := by
  refine List.perm_iff_count.2 fun x => ?_
  unfold wordW
  cases right <;> simp [List.count_cons, List.count_append]
  omega

private theorem projOK_mono {nb nb' : ℕ} (h : nb ≤ nb') {w : List PkgLetter} (hw : projOK nb w) :
    projOK nb' w := fun y hy => lt_of_lt_of_le (hw y hy) h

/-- The loops of `R'` are those of `R` with the word `w` at `ℓ` replaced by `N`. -/
private theorem wfP_set (R R' : PkgExpr) (ℓ : ℕ) (w N : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hR : WfP R) (hl : R'.loops = R.loops.set ℓ N)
    (hnb : R.nb ≤ R'.nb) (hwt : ∀ p ∈ R'.weights, p.2 < R'.nb)
    (hlam : ∀ o : Fin 2, N.count (.lw (.lamt o)) = w.count (.lw (.lamt o)))
    (hseg : (summ N).ok = true) (hproj : projOK R'.nb N) : WfP R' := by
  refine ⟨?_, ?_, ?_, ?_, hwt⟩
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 0))) R.loops ℓ w N hw
    have h2 := hR.lam0
    have h3 := hlam 0
    rw [hl]
    beta_reduce at h1
    omega
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 1))) R.loops ℓ w N hw
    have h2 := hR.lam1
    have h3 := hlam 1
    rw [hl]
    beta_reduce at h1
    omega
  · intro w₁ hw₁
    rw [hl] at hw₁
    rcases List.mem_or_eq_of_mem_set hw₁ with h | rfl
    · exact hR.seg w₁ h
    · exact hseg
  · intro w₁ hw₁
    rw [hl] at hw₁
    rcases List.mem_or_eq_of_mem_set hw₁ with h | rfl
    · exact projOK_mono hnb (hR.proj w₁ h)
    · exact hproj

/-- The loops of `R'` are those of `R` with the word `w` at `ℓ` replaced by `A`, and `B` added. -/
private theorem wfP_cut (R R' : PkgExpr) (ℓ : ℕ) (w A B : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hR : WfP R) (hl : R'.loops = R.loops.set ℓ A ++ [B])
    (hnb : R.nb ≤ R'.nb) (hwt : ∀ p ∈ R'.weights, p.2 < R'.nb)
    (hlam : ∀ o : Fin 2, A.count (.lw (.lamt o)) + B.count (.lw (.lamt o)) =
      w.count (.lw (.lamt o)))
    (hsegA : (summ A).ok = true) (hsegB : (summ B).ok = true) (hprojA : projOK R'.nb A)
    (hprojB : projOK R'.nb B) : WfP R' := by
  refine ⟨?_, ?_, ?_, ?_, hwt⟩
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 0))) R.loops ℓ w A hw
    have h2 := hR.lam0
    have h3 := hlam 0
    rw [hl, List.map_append, List.sum_append]
    beta_reduce at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 1))) R.loops ℓ w A hw
    have h2 := hR.lam1
    have h3 := hlam 1
    rw [hl, List.map_append, List.sum_append]
    beta_reduce at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · intro w₁ hw₁
    rw [hl] at hw₁
    rcases List.mem_append.1 hw₁ with h | h
    · rcases List.mem_or_eq_of_mem_set h with h | rfl
      · exact hR.seg w₁ h
      · exact hsegA
    · rw [List.mem_singleton] at h
      subst h
      exact hsegB
  · intro w₁ hw₁
    rw [hl] at hw₁
    rcases List.mem_append.1 hw₁ with h | h
    · rcases List.mem_or_eq_of_mem_set h with h | rfl
      · exact projOK_mono hnb (hR.proj w₁ h)
      · exact hprojA
    · rw [List.mem_singleton] at h
      subst h
      exact hprojB

/-- The loops of `R'` are those of `R` with the word `w` at `ℓ` replaced by `N` and the word `f`
at `j ≠ ℓ` erased. -/
private theorem wfP_join (R R' : PkgExpr) (ℓ j : ℕ) (w f N : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hf : R.loops[j]? = some f) (hjℓ : j ≠ ℓ) (hR : WfP R)
    (hl : R'.loops = (R.loops.set ℓ N).eraseIdx j)
    (hnb : R.nb ≤ R'.nb) (hwt : ∀ p ∈ R'.weights, p.2 < R'.nb)
    (hlam : ∀ o : Fin 2, N.count (.lw (.lamt o)) =
      w.count (.lw (.lamt o)) + f.count (.lw (.lamt o)))
    (hseg : (summ N).ok = true) (hproj : projOK R'.nb N) : WfP R' := by
  have hf' : (R.loops.set ℓ N)[j]? = some f := by
    rw [List.getElem?_set_ne (Ne.symm hjℓ)]
    exact hf
  have hlℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  refine ⟨?_, ?_, ?_, ?_, hwt⟩
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 0))) R.loops ℓ w N hw
    have h0 := sum_map_eraseIdx (fun w => w.count (.lw (.lamt 0))) _ j f hf'
    have h2 := hR.lam0
    have h3 := hlam 0
    rw [hl]
    beta_reduce at h0 h1
    omega
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 1))) R.loops ℓ w N hw
    have h0 := sum_map_eraseIdx (fun w => w.count (.lw (.lamt 1))) _ j f hf'
    have h2 := hR.lam1
    have h3 := hlam 1
    rw [hl]
    beta_reduce at h0 h1
    omega
  · intro w₁ hw₁
    rw [hl] at hw₁
    have hw₁' := List.mem_of_mem_eraseIdx hw₁
    rcases List.mem_or_eq_of_mem_set hw₁' with h | rfl
    · exact hR.seg w₁ h
    · exact hseg
  · intro w₁ hw₁
    rw [hl] at hw₁
    have hw₁' := List.mem_of_mem_eraseIdx hw₁
    rcases List.mem_or_eq_of_mem_set hw₁' with h | rfl
    · exact projOK_mono hnb (hR.proj w₁ h)
    · exact hproj

private theorem charsP_u (R : PkgExpr) : R.charsP.2.2.1 = ((R.weights.length : ℕ) : ℤ) := rfl
private theorem charsP_S (R : PkgExpr) : R.charsP.2.2.2 = R.S := rfl

private theorem charsP_eq (R : PkgExpr) :
    R.charsP = ((((R.loops.map fun w => w.countP isResP).sum : ℕ) : ℤ),
      (((R.loops.map nfac).sum : ℕ) : ℤ), ((R.weights.length : ℕ) : ℤ), R.S) := rfl

private theorem chars_set (R R' : PkgExpr) (ℓ : ℕ) (w N : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hl : R'.loops = R.loops.set ℓ N) :
    R'.charsP.1 + ((w.countP isResP : ℕ) : ℤ) = R.charsP.1 + ((N.countP isResP : ℕ) : ℤ) ∧
    R'.charsP.2.1 + ((nfac w : ℕ) : ℤ) = R.charsP.2.1 + ((nfac N : ℕ) : ℤ) := by
  have h1 := sum_map_set (fun w => w.countP isResP) R.loops ℓ w N hw
  have h2 := sum_map_set nfac R.loops ℓ w N hw
  rw [charsP_eq, charsP_eq, hl]
  beta_reduce at h1 h2
  refine ⟨?_, ?_⟩ <;> dsimp only <;> omega

private theorem chars_cut (R R' : PkgExpr) (ℓ : ℕ) (w A B : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hl : R'.loops = R.loops.set ℓ A ++ [B]) :
    R'.charsP.1 + ((w.countP isResP : ℕ) : ℤ) =
      R.charsP.1 + ((A.countP isResP : ℕ) : ℤ) + ((B.countP isResP : ℕ) : ℤ) ∧
    R'.charsP.2.1 + ((nfac w : ℕ) : ℤ) =
      R.charsP.2.1 + ((nfac A : ℕ) : ℤ) + ((nfac B : ℕ) : ℤ) := by
  have h1 := sum_map_set (fun w => w.countP isResP) R.loops ℓ w A hw
  have h2 := sum_map_set nfac R.loops ℓ w A hw
  rw [charsP_eq, charsP_eq, hl]
  beta_reduce at h1 h2
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  refine ⟨?_, ?_⟩ <;> omega

private theorem chars_join (R R' : PkgExpr) (ℓ j : ℕ) (w f N : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hf : R.loops[j]? = some f) (hjℓ : j ≠ ℓ)
    (hl : R'.loops = (R.loops.set ℓ N).eraseIdx j) :
    R'.charsP.1 + ((w.countP isResP : ℕ) : ℤ) + ((f.countP isResP : ℕ) : ℤ) =
      R.charsP.1 + ((N.countP isResP : ℕ) : ℤ) ∧
    R'.charsP.2.1 + ((nfac w : ℕ) : ℤ) + ((nfac f : ℕ) : ℤ) =
      R.charsP.2.1 + ((nfac N : ℕ) : ℤ) := by
  have hf' : (R.loops.set ℓ N)[j]? = some f := by
    rw [List.getElem?_set_ne (Ne.symm hjℓ)]
    exact hf
  have h1 := sum_map_set (fun w => w.countP isResP) R.loops ℓ w N hw
  have h2 := sum_map_set nfac R.loops ℓ w N hw
  have h3 := sum_map_eraseIdx (fun w => w.countP isResP) _ j f hf'
  have h4 := sum_map_eraseIdx nfac _ j f hf'
  rw [charsP_eq, charsP_eq, hl]
  beta_reduce at h1 h2 h3 h4
  refine ⟨?_, ?_⟩ <;> dsimp only <;> omega

private theorem K1_cyc (a : Fin 2) (tl : List PkgLetter)
    (hP1 : (summ tl).pre = true ∨ (summ tl).suf = true)
    (h : (summ (.lw (.res a) :: tl)).ok = true) : (summ (.lw (.det a) :: tl)).ok = true := by
  rw [summ_cons] at h ⊢
  have hi := summ_inv tl
  generalize summ tl = s at *
  simp only [isEntP_lw, isGoodP_res, isGoodP_det] at h ⊢
  revert s; decide

/-- The replacement `𝔣𝔯` of the resolvent chosen by `ffocus`. -/
private theorem K1_spec (R R' : PkgExpr) (ℓ r : ℕ) (w tl : List PkgLetter) (a : Fin 2)
    (hw : R.loops[ℓ]? = some w) (hrot : w.rotate r = .lw (.res a) :: tl)
    (hP1 : (summ tl).pre = true ∨ (summ tl).suf = true)
    (hl : R'.loops = R.loops.set ℓ (.lw (.det a) :: tl)) (hwt : R'.weights = R.weights)
    (hnb : R'.nb = R.nb) (hS : R'.S = R.S) :
    R'.charsP = R.charsP + PkgOp.frep.delta ∧ (WfP R → WfP R') := by
  have hperm : (PkgLetter.lw (.res a) :: tl).Perm w := hrot ▸ List.rotate_perm w r
  have hcyc : (summ (.lw (.res a) :: tl)).ok = (summ w).ok := by
    rw [← hrot, cyc_rotate]
  refine ⟨?_, fun hR => ?_⟩
  · obtain ⟨c1, c2⟩ := chars_set R R' ℓ w _ hw hl
    have e1 := hperm.countP_eq isResP
    have e2 := hperm.countP_eq isEntP
    have e3 := plB_perm hperm
    have f1 : nfac w = nfac tl := by
      rw [nfac_eq, nfac_eq, ← e2, ← e3]
      simp [isEntP_lw, plB_cons_lw]
    have f2 : nfac (.lw (.det a) :: tl) = nfac tl := by
      rw [nfac_eq, nfac_eq, plB_cons_lw]
      simp [isEntP_lw]
    simp only [List.countP_cons, isResP_res, isResP_det, ite_true, Bool.false_eq_true,
      ite_false] at e1 c1
    rw [f1, f2] at c2
    have u0 := charsP_u R
    have u1 := charsP_u R'
    have S0 := charsP_S R
    have S1 := charsP_S R'
    rw [hwt] at u1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp only [Prod.fst_add, PkgOp.delta]; omega
    · simp only [Prod.fst_add, Prod.snd_add, PkgOp.delta]; omega
    · simp only [Prod.fst_add, Prod.snd_add, PkgOp.delta]; omega
    · simp only [Prod.snd_add, PkgOp.delta]; omega
  · refine wfP_set R R' ℓ w _ hw hR hl (by omega) (fun p hp => ?_) ?_ ?_ ?_
    · rw [hwt] at hp; rw [hnb]; exact hR.wt p hp
    · intro o
      have := hperm.count_eq (.lw (.lamt o))
      simp at this ⊢
      omega
    · apply K1_cyc a tl hP1
      rw [hcyc]
      exact hR.seg w (List.mem_of_getElem? hw)
    · intro y hy
      have hy' : PkgLetter.lw (.proj y) ∈ tl := by
        rcases List.mem_cons.1 hy with h | h
        · cases h
        · exact h
      have := hR.proj w (List.mem_of_getElem? hw) y (hperm.mem_iff.1 (List.mem_cons_of_mem _ hy'))
      rw [hnb]
      exact this

private theorem summ_cons_bad (x : PkgLetter) (hx : isEntP x = false) (hg : isGoodP x = false)
    (X : List PkgLetter) : summ (x :: X) = summ X := by
  rw [summ_cons, hx, hg]
  have := summ_inv X
  generalize summ X = s at *
  revert s; decide

private theorem summ_append_bad (x : PkgLetter) (hx : isEntP x = false) (hg : isGoodP x = false)
    (X : List PkgLetter) : summ (X ++ [x]) = summ X := by
  have h1 : summ [x] = Sm.nil := by
    rw [summ_cons, hx, hg]; rfl
  rw [summ_append, h1]
  generalize summ X = s
  revert s; decide

private theorem wordW_cyc (right : Bool) (a : Fin 2) (tl : List PkgLetter) :
    (summ (wordW right a tl)).ok = (summ (.lw (.res a) :: tl)).ok := by
  unfold wordW
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [cyc_append_comm, List.singleton_append, summ_cons, summ_cons_bad (.lw (.det a)) rfl rfl]
    rfl
  · simp only [↓reduceIte]
    rw [summ_append_bad _ rfl rfl]

/-- A word `w` that is a rotation of `𝒢 · tl` has one resolvent more than `tl`, and the same
letters `Δ`, factor, letters `Λ̃`, letters and cyclic segments as `𝒢 · tl`. -/
private theorem rot_facts {w tl : List PkgLetter} {a : Fin 2} {r : ℕ}
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    w.countP isResP = tl.countP isResP + 1 ∧ nfac w = nfac tl ∧
      (∀ o : Fin 2, w.count (.lw (.lamt o)) = tl.count (.lw (.lamt o))) ∧
      (∀ x, x ∈ w ↔ x = .lw (.res a) ∨ x ∈ tl) ∧ (summ (.lw (.res a) :: tl)).ok = (summ w).ok ∧
      (w.countP isEntP = tl.countP isEntP) ∧ plB w = plB tl := by
  have hperm : (PkgLetter.lw (.res a) :: tl).Perm w := hrot ▸ List.rotate_perm w r
  have e2 := hperm.countP_eq isEntP
  have e3 := plB_perm hperm
  simp only [List.countP_cons, isEntP_lw, Bool.false_eq_true, ite_false, plB_cons_lw,
    add_zero] at e2 e3
  refine ⟨?_, ?_, ?_, ?_, ?_, e2.symm, e3.symm⟩
  · have := hperm.countP_eq isResP
    simp only [List.countP_cons, isResP_res, ite_true] at this
    omega
  · rw [nfac_eq, nfac_eq, ← e2, e3]
  · intro o
    have := hperm.count_eq (.lw (.lamt o))
    simpa [List.count_cons] using this.symm
  · intro x
    rw [← hperm.mem_iff, List.mem_cons]
  · rw [← hrot, cyc_rotate]

/-- The terms of `𝔣𝔠₁` and `𝔰𝔩𝔞𝔰𝔥₁`: the light weight `⟨E_x(𝒢 - 𝔐)⟩` with the new index. -/
private theorem K2_spec (R R' : PkgExpr) (ℓ r : ℕ) (w tl N : List PkgLetter) (a : Fin 2)
    (right : Bool) (hw : R.loops[ℓ]? = some w) (hrot : w.rotate r = .lw (.res a) :: tl)
    (hN : N.Perm (.lw (.proj R.nb) :: wordW right a tl))
    (hNc : (summ N).ok = (summ (.lw (.res a) :: tl)).ok)
    (hl : R'.loops = R.loops.set ℓ N) (hwt : R'.weights = R.weights ++ [(a, R.nb)])
    (hnb : R'.nb = R.nb + 1) (hS : R'.S = R.S) :
    R'.charsP = R.charsP + ((0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ)) ∧ (WfP R → WfP R') := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := rot_facts hrot
  have hN' : N.Perm (.lw (.proj R.nb) :: .lw (.det a) :: .lw (.res a) :: tl) :=
    hN.trans (List.Perm.cons _ (wordW_perm right a tl))
  have n1 := hN'.countP_eq isResP
  have n2 := hN'.countP_eq isEntP
  have n3 := plB_perm hN'
  simp only [List.countP_cons, isResP_res, isResP_det, isResP_proj, isEntP_lw, ite_true,
    Bool.false_eq_true, ite_false, plB_cons_lw, add_zero] at n1 n2 n3
  refine ⟨?_, fun hR => ?_⟩
  · obtain ⟨c1, c2⟩ := chars_set R R' ℓ w N hw hl
    have f1 : nfac N = nfac w := by
      rw [nfac_eq, nfac_eq, n2, n3, r6, r7]
    rw [f1] at c2
    have u0 := charsP_u R
    have u1 := charsP_u R'
    have S0 := charsP_S R
    have S1 := charsP_S R'
    rw [hwt] at u1
    simp only [List.length_append, List.length_singleton] at u1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.fst_add, Prod.snd_add]; omega
    · simp only [Prod.fst_add, Prod.snd_add]; push_cast at u1 ⊢; omega
    · simp only [Prod.snd_add]; omega
  · refine wfP_set R R' ℓ w N hw hR hl (by omega) (fun p hp => ?_) ?_ ?_ ?_
    · rw [hwt] at hp
      rw [hnb]
      rcases List.mem_append.1 hp with h | h
      · exact lt_of_lt_of_le (hR.wt p h) (Nat.le_succ _)
      · rw [List.mem_singleton] at h
        subst h
        exact Nat.lt_succ_self _
    · intro o
      have := hN'.count_eq (.lw (.lamt o))
      simp at this
      rw [r3 o]
      simpa using this
    · rw [hNc]
      exact (r5 ▸ hR.seg w (List.mem_of_getElem? hw) : _)
    · intro y hy
      rw [hnb]
      have := hN'.mem_iff.1 hy
      simp only [List.mem_cons] at this
      rcases this with h | h | h | h
      · have := PkgLetter.lw.inj h
        cases this
        exact Nat.lt_succ_self _
      · cases h
      · cases h
      · have := hR.proj w (List.mem_of_getElem? hw) y ((r4 _).2 (Or.inr h))
        exact lt_of_lt_of_le this (Nat.le_succ _)

private theorem cyc_append_good (X Z : List PkgLetter) (hZ : summ Z = ⟨false, true, true, true⟩)
    (h : (summ X).ok = true) : (summ (X ++ Z)).ok = true := by
  rw [summ_append, hZ]
  have := summ_inv X
  generalize summ X = s at *
  revert s; decide

/-- The terms of `𝔣𝔭₁` and `𝔦𝔫𝔰𝔢𝔯𝔱₁`: the plug of the light weight `(b, y)`. -/
private theorem K4_spec (R R' : PkgExpr) (ℓ r j : ℕ) (w tl : List PkgLetter) (a b : Fin 2)
    (y : ℕ) (right : Bool) (hw : R.loops[ℓ]? = some w) (hrot : w.rotate r = .lw (.res a) :: tl)
    (hj : R.weights[j]? = some (b, y))
    (hl : R'.loops = R.loops.set ℓ
      (wordW right a tl ++ [.lw (.proj R.nb), .lw (.res b), .lw (.proj y), .lw (.res b),
        .lw (.proj R.nb)]))
    (hwt : R'.weights = R.weights.eraseIdx j) (hnb : R'.nb = R.nb + 1) (hS : R'.S = R.S + 2) :
    R'.charsP = R.charsP + ((2 : ℤ), (0 : ℤ), (-1 : ℤ), (2 : ℤ)) ∧ (WfP R → WfP R') := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := rot_facts hrot
  have hWp := wordW_perm right a tl
  have w1 := hWp.countP_eq isResP
  have w2 := hWp.countP_eq isEntP
  have w3 := plB_perm hWp
  simp only [List.countP_cons, isResP_res, isResP_det, isEntP_lw, ite_true,
    Bool.false_eq_true, ite_false, plB_cons_lw, add_zero] at w1 w2 w3
  have hj' : j < R.weights.length := (List.getElem?_eq_some_iff.1 hj).1
  have hlen := List.length_eraseIdx_of_lt hj'
  have hZ : ([PkgLetter.lw (.proj R.nb), .lw (.res b), .lw (.proj y), .lw (.res b),
      .lw (.proj R.nb)] : List PkgLetter).countP isResP = 2 := by
    simp [List.countP_cons, isResP]
  have hZe : ([PkgLetter.lw (.proj R.nb), .lw (.res b), .lw (.proj y), .lw (.res b),
      .lw (.proj R.nb)] : List PkgLetter).countP isEntP = 0 := by
    simp [isEntP]
  have hZp : plB ([PkgLetter.lw (.proj R.nb), .lw (.res b), .lw (.proj y), .lw (.res b),
      .lw (.proj R.nb)] : List PkgLetter) = true := by
    simp [plB, isEntP]
  refine ⟨?_, fun hR => ?_⟩
  · obtain ⟨c1, c2⟩ := chars_set R R' ℓ w _ hw hl
    have f1 : nfac (wordW right a tl ++ [.lw (.proj R.nb), .lw (.res b), .lw (.proj y),
        .lw (.res b), .lw (.proj R.nb)]) = nfac w := by
      rw [nfac_eq, nfac_eq, plB_append, hZp, List.countP_append, hZe, w2, w3, r6, r7]
      simp
    rw [f1] at c2
    rw [List.countP_append, hZ, w1] at c1
    have u0 := charsP_u R
    have u1 := charsP_u R'
    have S0 := charsP_S R
    have S1 := charsP_S R'
    rw [hwt, hlen] at u1
    have u0' : ((R.weights.length : ℕ) : ℤ) = ((R.weights.length - 1 : ℕ) : ℤ) + 1 := by omega
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.fst_add, Prod.snd_add]; omega
    · simp only [Prod.fst_add, Prod.snd_add]; omega
    · simp only [Prod.snd_add]; omega
  · have hyb : y < R.nb := hR.wt (b, y) (List.mem_of_getElem? hj)
    refine wfP_set R R' ℓ w _ hw hR hl (by omega) (fun p hp => ?_) ?_ ?_ ?_
    · rw [hwt] at hp
      rw [hnb]
      exact lt_of_lt_of_le (hR.wt p (List.mem_of_mem_eraseIdx hp)) (Nat.le_succ _)
    · intro o
      have := hWp.count_eq (.lw (.lamt o))
      simp only [List.count_append, List.count_cons] at this ⊢
      rw [r3 o]
      simp at this ⊢
      omega
    · apply cyc_append_good _ _ (by rfl)
      rw [wordW_cyc, r5]
      exact hR.seg w (List.mem_of_getElem? hw)
    · intro y' hy
      rw [hnb]
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h | h | h | h | h
      · have := (hWp.mem_iff.1 h)
        simp only [List.mem_cons] at this
        rcases this with h | h | h
        · cases h
        · cases h
        · exact lt_of_lt_of_le (hR.proj w (List.mem_of_getElem? hw) y' ((r4 _).2 (Or.inr h)))
            (Nat.le_succ _)
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_self _
      · cases h
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_of_lt hyb
      · cases h
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_self _

private theorem cut_cyc (X Y : List PkgLetter) (b : Fin 2) (n : ℕ)
    (h : (summ (X ++ .lw (.res b) :: Y)).ok = true) :
    (summ (X ++ [.lw (.res b)] ++ [.lw (.proj n)])).ok = true ∧
      (summ (.lw (.proj n) :: .lw (.res b) :: Y)).ok = true := by
  simp only [summ_append, summ_cons, isEntP_lw, isGoodP_res, isGoodP_proj] at h ⊢
  have h1 := summ_inv X
  have h2 := summ_inv Y
  generalize summ X = sX at *
  generalize summ Y = sY at *
  revert sX sY; decide

private theorem plB_nil : plB ([] : List PkgLetter) = true := by simp [plB]

/-- The terms of `𝔣𝔠₂`, `𝔰𝔩𝔞𝔰𝔥₂`, `𝔢𝔵𝔠𝔥𝔞𝔫𝔤𝔢`, cut at the resolvent `𝒢_b` between `X` and `Y`. -/
private theorem K3_core (R R' : PkgExpr) (ℓ r : ℕ) (w tl X Y : List PkgLetter) (a b : Fin 2)
    (o : PkgOp) (hw : R.loops[ℓ]? = some w) (hrot : w.rotate r = .lw (.res a) :: tl)
    (hW : (X ++ .lw (.res b) :: Y).Perm (.lw (.det a) :: .lw (.res a) :: tl))
    (hWc : (summ (X ++ .lw (.res b) :: Y)).ok = (summ (.lw (.res a) :: tl)).ok)
    (ho : o = if (plB X && plB Y) = true then PkgOp.fcut2
      else if (plB X || plB Y) = true then PkgOp.slash2 else PkgOp.exchange)
    (hl : R'.loops = R.loops.set ℓ (X ++ [.lw (.res b)] ++ [.lw (.proj R.nb)]) ++
      [.lw (.proj R.nb) :: .lw (.res b) :: Y])
    (hwt : R'.weights = R.weights) (hnb : R'.nb = R.nb + 1)
    (hS : R'.S = R.S + 1 - ((if plB X = true then 1 else 0) + (if plB Y = true then 1 else 0) -
      (if plB w = true then 1 else 0))) :
    R'.charsP = R.charsP + o.delta ∧ (WfP R → WfP R') := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := rot_facts hrot
  have w1 := hW.countP_eq isResP
  have w2 := hW.countP_eq isEntP
  have w3 := plB_perm hW
  simp only [List.countP_cons, List.countP_append, isResP_res, isResP_det, isEntP_lw,
    ite_true, Bool.false_eq_true, ite_false, plB_cons_lw, plB_append, add_zero] at w1 w2 w3
  have pA : plB (X ++ [.lw (.res b)] ++ [.lw (.proj R.nb)]) = plB X := by
    simp [plB_append, plB_cons_lw, plB_nil]
  have pB : plB (PkgLetter.lw (.proj R.nb) :: .lw (.res b) :: Y) = plB Y := by
    simp [plB_cons_lw]
  refine ⟨?_, fun hR => ?_⟩
  · obtain ⟨c1, c2⟩ := chars_cut R R' ℓ w _ _ hw hl
    have f1 : nfac (X ++ [.lw (.res b)] ++ [.lw (.proj R.nb)]) =
        X.countP isEntP + (if plB X then 1 else 0) := by
      rw [nfac_eq, pA]
      simp [List.countP_append, isEntP]
    have f2 : nfac (PkgLetter.lw (.proj R.nb) :: .lw (.res b) :: Y) =
        Y.countP isEntP + (if plB Y then 1 else 0) := by
      rw [nfac_eq, pB]
      simp [isEntP]
    have f3 : nfac w = X.countP isEntP + Y.countP isEntP + (if plB X && plB Y then 1 else 0) := by
      rw [r2, nfac_eq, ← w2, ← w3]
    have u0 := charsP_u R
    have u1 := charsP_u R'
    have S0 := charsP_S R
    have S1 := charsP_S R'
    rw [hwt] at u1
    have cres1 : (X ++ [PkgLetter.lw (.res b)] ++ [PkgLetter.lw (.proj R.nb)]).countP isResP =
        X.countP isResP + 1 := by
      simp [List.countP_append, List.countP_cons, isResP_res, isResP_proj]
    have cres2 : (PkgLetter.lw (.proj R.nb) :: PkgLetter.lw (.res b) :: Y).countP isResP =
        Y.countP isResP + 1 := by
      simp [List.countP_cons, isResP_res, isResP_proj]
    rw [f1, f2, f3] at c2
    rw [cres1, cres2, r1] at c1
    rw [r7, ← w3] at hS
    subst ho
    cases hX : plB X <;> cases hY : plB Y <;> simp only [hX, hY] at hS c2 ⊢ <;>
      simp only [Bool.and_self, Bool.and_true, Bool.and_false, Bool.or_self,
        Bool.or_false, Bool.or_true, ite_true,
        ite_false, Bool.false_eq_true] at hS c2 ⊢ <;>
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      simp only [Prod.fst_add, Prod.snd_add, PkgOp.delta] <;> push_cast at c1 c2 hS ⊢ <;> omega
  · have hWproj : ∀ y : ℕ,
        (PkgLetter.lw (.proj y) ∈ X ∨ PkgLetter.lw (.proj y) ∈ Y) → y < R.nb := by
      intro y hy
      have hmem : PkgLetter.lw (.proj y) ∈ X ++ .lw (.res b) :: Y := by
        rcases hy with hy | hy
        · exact List.mem_append_left _ hy
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
      have := hW.mem_iff.1 hmem
      simp only [List.mem_cons] at this
      rcases this with h | h | h
      · cases h
      · cases h
      · exact hR.proj w (List.mem_of_getElem? hw) y ((r4 _).2 (Or.inr h))
    have hcyc : (summ (X ++ .lw (.res b) :: Y)).ok = true := by
      rw [hWc, r5]
      exact hR.seg w (List.mem_of_getElem? hw)
    refine wfP_cut R R' ℓ w _ _ hw hR hl (by omega) (fun p hp => ?_) ?_ (cut_cyc X Y b R.nb hcyc).1
      (cut_cyc X Y b R.nb hcyc).2 ?_ ?_
    · rw [hwt] at hp
      rw [hnb]
      exact lt_of_lt_of_le (hR.wt p hp) (Nat.le_succ _)
    · intro o
      have := hW.count_eq (.lw (.lamt o))
      simp only [List.count_append, List.count_cons] at this ⊢
      rw [r3 o]
      simp at this ⊢
      omega
    · intro y hy
      rw [hnb]
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with (h | h) | h
      · exact lt_of_lt_of_le (hWproj y (Or.inl h)) (Nat.le_succ _)
      · cases h
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_self _
    · intro y hy
      rw [hnb]
      simp only [List.mem_cons] at hy
      rcases hy with h | h | h
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_self _
      · cases h
      · exact lt_of_lt_of_le (hWproj y (Or.inr h)) (Nat.le_succ _)

private theorem join_cyc (W F : List PkgLetter) (b : Fin 2) (n : ℕ) (hW : (summ W).ok = true)
    (hF : (summ (.lw (.res b) :: F)).ok = true) :
    (summ (W ++ [.lw (.proj n)] ++ (.lw (.res b) :: F) ++ [.lw (.res b), .lw (.proj n)])).ok =
      true := by
  simp only [summ_append, summ_cons, isEntP_lw, isGoodP_res, isGoodP_proj, summ_nil] at hW hF ⊢
  have h1 := summ_inv W
  have h2 := summ_inv F
  generalize summ W = sW at *
  generalize summ F = sF at *
  revert sW sF; decide

/-- The terms of `𝔣𝔭₂`, `𝔪𝔢𝔯𝔤𝔢`, `𝔦𝔫𝔰𝔢𝔯𝔱₂`, `𝔢𝔵𝔠𝔥𝔞𝔫𝔤𝔢`: the join with a resolvent of the word
`f`. -/
private theorem K5_core (R R' : PkgExpr) (ℓ r j q : ℕ) (w tl f F : List PkgLetter) (a b : Fin 2)
    (right : Bool) (o : PkgOp) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) (hf : R.loops[j]? = some f) (hjℓ : j ≠ ℓ)
    (hfrot : f.rotate q = .lw (.res b) :: F)
    (ho : o = if plB w = true then (if plB f = true then PkgOp.fplug2 else PkgOp.merge)
      else (if plB f = true then PkgOp.insert2 else PkgOp.exchange))
    (hl : R'.loops = (R.loops.set ℓ (wordW right a tl ++ [.lw (.proj R.nb)] ++
      f.rotate q ++ [.lw (.res b), .lw (.proj R.nb)])).eraseIdx j)
    (hwt : R'.weights = R.weights) (hnb : R'.nb = R.nb + 1)
    (hS : R'.S = R.S + 1 - ((if plB (wordW right a tl ++ [.lw (.proj R.nb)] ++ f.rotate q ++
      [.lw (.res b), .lw (.proj R.nb)]) = true then 1 else 0) -
      (if plB w = true then 1 else 0) - (if plB f = true then 1 else 0))) :
    R'.charsP = R.charsP + o.delta ∧ (WfP R → WfP R') := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := rot_facts hrot
  have hWp := wordW_perm right a tl
  have w1 := hWp.countP_eq isResP
  have w2 := hWp.countP_eq isEntP
  have w3 := plB_perm hWp
  simp only [List.countP_cons, isResP_res, isResP_det, isEntP_lw, ite_true,
    Bool.false_eq_true, ite_false, plB_cons_lw, add_zero] at w1 w2 w3
  have hFp : (PkgLetter.lw (.res b) :: F).Perm f := hfrot ▸ List.rotate_perm f q
  have g1 := hFp.countP_eq isResP
  have g2 := hFp.countP_eq isEntP
  have g3 := plB_perm hFp
  simp only [List.countP_cons, isResP_res, isEntP_lw, ite_true, Bool.false_eq_true, ite_false,
    plB_cons_lw, add_zero] at g1 g2 g3
  rw [hfrot] at hl hS
  have pN : plB (wordW right a tl ++ [.lw (.proj R.nb)] ++ (.lw (.res b) :: F) ++
      [.lw (.res b), .lw (.proj R.nb)]) = (plB w && plB f) := by
    simp only [plB_append, plB_cons_lw, plB_nil, Bool.and_true]
    rw [w3, g3, r7]
  refine ⟨?_, fun hR => ?_⟩
  · obtain ⟨c1, c2⟩ := chars_join R R' ℓ j w f _ hw hf hjℓ hl
    have cres : (wordW right a tl ++ [.lw (.proj R.nb)] ++ (.lw (.res b) :: F) ++
        [.lw (.res b), .lw (.proj R.nb)] : List PkgLetter).countP isResP =
        w.countP isResP + f.countP isResP + 1 := by
      simp only [List.countP_append, List.countP_cons, isResP_res, isResP_proj, ite_true,
        Bool.false_eq_true, ite_false, List.countP_nil]
      omega
    have f3 : nfac (wordW right a tl ++ [.lw (.proj R.nb)] ++ (.lw (.res b) :: F) ++
        [.lw (.res b), .lw (.proj R.nb)]) =
        w.countP isEntP + f.countP isEntP + (if (plB w && plB f) = true then 1 else 0) := by
      rw [nfac_eq, pN]
      simp only [List.countP_append, List.countP_cons, isEntP_lw, Bool.false_eq_true,
        ite_false, List.countP_nil, add_zero]
      omega
    rw [nfac_eq w, nfac_eq f] at c2
    rw [cres] at c1
    rw [f3] at c2
    rw [pN] at hS
    have u0 := charsP_u R
    have u1 := charsP_u R'
    have S0 := charsP_S R
    have S1 := charsP_S R'
    rw [hwt] at u1
    subst ho
    cases hX : plB w <;> cases hY : plB f <;> simp only [hX, hY] at hS c2 ⊢ <;>
      simp only [Bool.and_self, Bool.and_true, Bool.and_false, ite_true,
        ite_false, Bool.false_eq_true] at hS c2 ⊢ <;>
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      simp only [Prod.fst_add, Prod.snd_add, PkgOp.delta] <;> push_cast at c1 c2 hS ⊢ <;> omega
  · have hWc : (summ (wordW right a tl)).ok = true := by
      rw [wordW_cyc, r5]
      exact hR.seg w (List.mem_of_getElem? hw)
    have hfmem := List.mem_of_getElem? hf
    have hcycF : (summ (.lw (.res b) :: F)).ok = true := by
      rw [← hfrot, cyc_rotate]
      exact hR.seg f hfmem
    refine wfP_join R R' ℓ j w f _ hw hf hjℓ hR hl (by omega) (fun p hp => ?_) ?_
      (join_cyc _ _ b R.nb hWc hcycF) ?_
    · rw [hwt] at hp
      rw [hnb]
      exact lt_of_lt_of_le (hR.wt p hp) (Nat.le_succ _)
    · intro o
      have h1 := hWp.count_eq (.lw (.lamt o))
      have h2 := hFp.count_eq (.lw (.lamt o))
      simp only [List.count_append, List.count_cons] at h1 h2 ⊢
      rw [r3 o]
      simp at h1 h2 ⊢
      omega
    · intro y hy
      rw [hnb]
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with ((h | h) | h | h) | h | h
      · have := hWp.mem_iff.1 h
        simp only [List.mem_cons] at this
        rcases this with h | h | h
        · cases h
        · cases h
        · exact lt_of_lt_of_le (hR.proj w (List.mem_of_getElem? hw) y ((r4 _).2 (Or.inr h)))
            (Nat.le_succ _)
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_self _
      · cases h
      · have := hFp.mem_iff.1 (List.mem_cons_of_mem _ h)
        exact lt_of_lt_of_le (hR.proj f hfmem y this) (Nat.le_succ _)
      · cases h
      · have := PkgLetter.lw.inj h; cases this; exact Nat.lt_succ_self _

private theorem plB_A (X : List PkgLetter) (b : Fin 2) (n : ℕ) :
    plB (X ++ [.lw (.res b)] ++ [.lw (.proj n)]) = plB X := by
  simp [plB_append, plB_cons_lw, plB_nil]

private theorem plB_B (Y : List PkgLetter) (b : Fin 2) (n : ℕ) :
    plB (.lw (.proj n) :: .lw (.res b) :: Y) = plB Y := by
  simp [plB_cons_lw]

private theorem rotate_head (f : List PkgLetter) (q : ℕ) (b : Fin 2)
    (h : f[q]? = some (.lw (.res b))) : ∃ F, f.rotate q = .lw (.res b) :: F := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  refine ⟨f.drop (q + 1) ++ f.take q, ?_⟩
  rw [List.rotate_eq_drop_append_take_mod, Nat.mod_eq_of_lt hlt, List.drop_eq_getElem_cons hlt,
    hget]
  rfl

/-- The terms `𝔣𝔠₂`, `𝔰𝔩𝔞𝔰𝔥₂`, `𝔢𝔵𝔠𝔥𝔞𝔫𝔤𝔢` of a cut at the position `q` of `W`. -/
private theorem K3_spec (R R' : PkgExpr) (ℓ r q : ℕ) (w tl : List PkgLetter) (a b : Fin 2)
    (right : Bool) (o : PkgOp) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) (hq : (wordW right a tl)[q]? = some (.lw (.res b)))
    (ho : o = if (plB ((wordW right a tl).take (q + 1) ++ [.lw (.proj R.nb)]) &&
          plB (.lw (.proj R.nb) :: (wordW right a tl).drop q)) = true then PkgOp.fcut2
      else if (plB ((wordW right a tl).take (q + 1) ++ [.lw (.proj R.nb)]) ||
          plB (.lw (.proj R.nb) :: (wordW right a tl).drop q)) = true then PkgOp.slash2
      else PkgOp.exchange)
    (hl : R'.loops = R.loops.set ℓ ((wordW right a tl).take (q + 1) ++ [.lw (.proj R.nb)]) ++
      [.lw (.proj R.nb) :: (wordW right a tl).drop q])
    (hwt : R'.weights = R.weights) (hnb : R'.nb = R.nb + 1)
    (hS : R'.S = R.S + 1 - ((if plB ((wordW right a tl).take (q + 1) ++ [.lw (.proj R.nb)]) = true
        then 1 else 0) + (if plB (.lw (.proj R.nb) :: (wordW right a tl).drop q) = true
        then 1 else 0) - (if plB w = true then 1 else 0))) :
    R'.charsP = R.charsP + o.delta ∧ (WfP R → WfP R') := by
  have hWp := wordW_perm right a tl
  have hWc := wordW_cyc right a tl
  generalize wordW right a tl = W at *
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hq
  have e1 : W.take (q + 1) = W.take q ++ [.lw (.res b)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, hget]
    rfl
  have e2 : W.drop q = .lw (.res b) :: W.drop (q + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  have e3 : W = W.take q ++ .lw (.res b) :: W.drop (q + 1) := by
    conv_lhs => rw [← List.take_append_drop q W, e2]
  rw [e1, e2, plB_A, plB_B] at ho hS
  rw [e1, e2] at hl
  rw [e3] at hWp hWc
  exact K3_core R R' ℓ r w tl _ _ a b o hw hrot hWp hWc ho hl hwt hnb hS

/-- The search of `takeWhile` and `find?` along `f 0, f 1, …` returns some `f k`, and `P` holds on
`f 0, …, f k`. -/
private theorem seek_aux (P Q : ℕ → Bool) (r : ℕ) : ∀ (n : ℕ) (f : ℕ → ℕ),
    (((List.range n).map f).takeWhile P).find? Q = some r →
      ∃ k < n, r = f k ∧ (∀ j ≤ k, P (f j) = true) ∧ Q (f k) = true
  | 0, f, h => by simp at h
  | n + 1, f, h => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.takeWhile_cons] at h
      by_cases hP : P (f 0) = true
      · simp only [hP, ↓reduceIte] at h
        rw [List.find?_cons] at h
        cases hQ : Q (f 0)
        · rw [hQ] at h
          obtain ⟨k, hk, hr, hPk, hQk⟩ := seek_aux P Q r n (f ∘ Nat.succ) h
          refine ⟨k + 1, by omega, hr, ?_, hQk⟩
          intro j hj
          cases j with
          | zero => exact hP
          | succ j => exact hPk j (by omega)
        · rw [hQ] at h
          have := Option.some.inj h
          subst this
          refine ⟨0, by omega, rfl, ?_, hQ⟩
          intro j hj
          have : j = 0 := by omega
          subst this
          exact hP
      · simp [hP] at h

/-- The positions searched by `pkgSeek`. -/
private def seekPos (len i : ℕ) (right : Bool) (j : ℕ) : ℕ :=
  if right then (i + 1 + j) % len else (i + len - 1 - j) % len

private theorem pkgSeek_pos (w : List PkgLetter) (i r : ℕ) (right : Bool)
    (h : pkgSeek w i right = some r) :
    ∃ k, k + 1 < w.length ∧ r = seekPos w.length i right k ∧
      (∀ j ≤ k, ∃ z, w[seekPos w.length i right j]? = some z ∧ isEntP z = false) ∧
      ∃ b, w[r]? = some (.lw (.res b)) := by
  have h' : (((List.range (w.length - 1)).map (seekPos w.length i right)).takeWhile
      fun r => match w[r]? with
        | some (PkgLetter.ent _ _) => false | some (PkgLetter.lw (LoopLetter.lamt _)) => false
        | _ => true).find? (fun r =>
      match w[r]? with | some (PkgLetter.lw (LoopLetter.res _)) => true | _ => false) = some r := h
  obtain ⟨k, hk, hr, hP, hQ⟩ := seek_aux _ _ r _ _ h'
  have hlen : 0 < w.length := by omega
  have hmem : ∀ j, w[seekPos w.length i right j]? ≠ none := by
    intro j
    have : seekPos w.length i right j < w.length := by
      unfold seekPos
      split <;> exact Nat.mod_lt _ hlen
    rw [List.getElem?_eq_getElem this]
    simp
  refine ⟨k, by omega, hr, ?_, ?_⟩
  · intro j hj
    have hPj := hP j hj
    rcases hz : w[seekPos w.length i right j]? with _ | z
    · exact absurd hz (hmem j)
    · refine ⟨z, rfl, ?_⟩
      rw [hz] at hPj
      match z, hPj with
      | .ent _ _, hPj => exact absurd hPj (by simp)
      | .lw (.res _), _ => rfl
      | .lw (.det _), _ => rfl
      | .lw (.proj _), _ => rfl
      | .lw (.lamt _), hPj => exact absurd hPj (by simp)
  · rw [hr]
    revert hQ
    rcases hz : w[seekPos w.length i right k]? with _ | z
    · simp
    · intro hQ
      match z, hQ with
      | .lw (.res b), _ => exact ⟨b, rfl⟩
      | .ent _ _, hQ => exact absurd hQ (by simp)
      | .lw (.det _), hQ => exact absurd hQ (by simp)
      | .lw (.proj _), hQ => exact absurd hQ (by simp)
      | .lw (.lamt _), hQ => exact absurd hQ (by simp)

private theorem seek_tl (w : List PkgLetter) (i r : ℕ) (right : Bool) (g : PkgLetter)
    (hg : w[i]? = some g) (h : pkgSeek w i right = some r) (a : Fin 2) (tl : List PkgLetter)
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    (right = true → ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₂, isEntP z = false) ∧
    (right = false → ∃ L₁ L₂, tl = L₁ ++ g :: L₂ ∧ ∀ z ∈ L₁, isEntP z = false) := by
  obtain ⟨k, hk, hr, hfree, b, hb⟩ := pkgSeek_pos w i r right h
  have hi : i < w.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen : 0 < w.length := by omega
  have hulen : (w.rotate i).length = w.length := List.length_rotate _ _
  have hu : ∀ m, m < w.length → (w.rotate i)[m]? = w[(m + i) % w.length]? := fun m hm =>
    List.getElem?_rotate hm
  have hu0 : (w.rotate i)[0]? = some g := by
    rw [hu 0 hlen, zero_add, Nat.mod_eq_of_lt hi]
    exact hg
  obtain ⟨T', hT'⟩ : ∃ T', w.rotate i = g :: T' := by
    rcases hrot0 : w.rotate i with _ | ⟨x, T'⟩
    · rw [hrot0] at hu0
      simp at hu0
    · rw [hrot0, List.getElem?_cons_zero, Option.some.injEq] at hu0
      subst hu0
      exact ⟨T', rfl⟩
  constructor
  · rintro rfl
    have e1 : r = (i + 1 + k) % w.length := by simpa [seekPos] using hr
    have hrr : w.rotate r = (w.rotate i).rotate (k + 1) := by
      rw [e1, List.rotate_mod, List.rotate_rotate]
      congr 1
      omega
    have hposk : (w.rotate i)[k + 1]? = some (.lw (.res b)) := by
      rw [hu _ (by omega)]
      have : (k + 1 + i) % w.length = r := by rw [e1]; congr 1; omega
      rw [this]
      exact hb
    rw [hrr, List.rotate_eq_drop_append_take (by omega)] at hrot
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hposk
    rw [List.drop_eq_getElem_cons hlt, hget, hT'] at hrot
    have hcons := List.cons.inj hrot
    refine ⟨(w.rotate i).drop (k + 1 + 1), T'.take k, ?_, ?_⟩
    · rw [← hcons.2, hT']
      simp
    · intro z hz
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hz
      rw [List.getElem?_take] at hn
      split at hn
      · rename_i hnk
        have hzu : (w.rotate i)[n + 1]? = some z := by rw [hT']; simpa using hn
        rw [hu _ (by omega)] at hzu
        obtain ⟨z', hz', hz'e⟩ := hfree n (by omega)
        have e2 : (n + 1 + i) % w.length = seekPos w.length i true n := by
          simp only [seekPos, ite_true]; congr 1; omega
        rw [e2, hz'] at hzu
        cases hzu
        exact hz'e
      · simp at hn
  · rintro rfl
    have e1 : r = (i + w.length - 1 - k) % w.length := by simpa [seekPos] using hr
    set c := w.length - 1 - k with hc
    have hrr : w.rotate r = (w.rotate i).rotate c := by
      rw [e1, List.rotate_mod, List.rotate_rotate]
      congr 1
      omega
    have hposk : (w.rotate i)[c]? = some (.lw (.res b)) := by
      rw [hu _ (by omega)]
      have : (c + i) % w.length = r := by rw [e1]; congr 1; omega
      rw [this]
      exact hb
    rw [hrr, List.rotate_eq_drop_append_take (by omega)] at hrot
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hposk
    rw [List.drop_eq_getElem_cons hlt, hget] at hrot
    have hcons := List.cons.inj hrot
    obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    refine ⟨(w.rotate i).drop (c + 1), T'.take c', ?_, ?_⟩
    · rw [← hcons.2, hT', hc']
      simp
    · intro z hz
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hz
      rw [List.getElem?_drop] at hn
      have hn' : c + 1 + n < w.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hn
        cases hn
      obtain ⟨z', hz', hz'e⟩ := hfree (k - 1 - n) (by omega)
      have e2 : (c + 1 + n + i) % w.length = seekPos w.length i false (k - 1 - n) := by
        simp only [seekPos, Bool.false_eq_true, ite_false]; congr 1; omega
      rw [hu _ hn', e2, hz'] at hn
      cases hn
      exact hz'e

private theorem findIdx_mem {α : Type*} (l : List α) (p : α → Bool) (x : α)
    (h : l[l.findIdx p]? = some x) : p x = true := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  have := List.findIdx_getElem (p := p) (xs := l) (w := hlt)
  rwa [hget] at this

private theorem contains_idx (w : List PkgLetter) (x : PkgLetter) (h : w.contains x = true) :
    w[w.idxOf x]? = some x := by
  have hm : x ∈ w := List.contains_iff_mem.1 h
  have hlt : w.idxOf x < w.length := List.idxOf_lt_length_iff.2 hm
  rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]

private theorem some_inj3 {ℓ ℓ' r r' : ℕ} {s s' : Bool}
    (h : some (ℓ', r', s') = some (ℓ, r, s)) : ℓ' = ℓ ∧ r' = r ∧ s' = s := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨h3, h4⟩ := Prod.mk.inj h2
  exact ⟨h1, h3, h4⟩

/-- The loop and the position of the letter `Λ̃` from which `ffocus` searches. -/
private theorem ffocus_data (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (w : List PkgLetter)
    (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w) :
    ∃ i o, w[i]? = some (.lw (.lamt o)) ∧ pkgSeek w i right = some r := by
  unfold PkgExpr.ffocus at hf
  dsimp only at hf
  split at hf
  · rename_i w₂ w₁ h₂ h₁
    have c₂ : w₂.contains (.lw (.lamt 1)) = true :=
      findIdx_mem R.loops (fun w => w.contains (.lw (.lamt 1))) w₂ h₂
    have c₁ : w₁.contains (.lw (.lamt 0)) = true :=
      findIdx_mem R.loops (fun w => w.contains (.lw (.lamt 0))) w₁ h₁
    split at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
        rw [h₂] at hw
        cases hw
        exact ⟨_, 1, contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
          rw [h₁] at hw
          cases hw
          exact ⟨_, 0, contains_idx _ _ c₁, hr'⟩
        · split at hf
          · rename_i r' hr'
            obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
            rw [h₂] at hw
            cases hw
            exact ⟨_, 1, contains_idx _ _ c₂, hr'⟩
          · simp at hf
    · split at hf
      · rename_i r' hr'
        obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
        rw [h₂] at hw
        cases hw
        exact ⟨_, 1, contains_idx _ _ c₂, hr'⟩
      · split at hf
        · rename_i r' hr'
          obtain ⟨rfl, rfl, rfl⟩ := some_inj3 hf
          rw [h₁] at hw
          cases hw
          exact ⟨_, 0, contains_idx _ _ c₁, hr'⟩
        · simp at hf
  · simp at hf

private theorem good_not_ent (g : PkgLetter) (hg : isGoodP g = true) : isEntP g = false := by
  match g, hg with
  | .lw (.res _), _ => rfl
  | .lw (.lamt _), _ => rfl

/-- The summary of `L₁ g L₂` with `g` good and `L₂` free of `Δ` has a good part after its last
`Δ`. -/
private theorem suf_of (L₁ L₂ : List PkgLetter) (g : PkgLetter) (hg : isGoodP g = true)
    (hL : ∀ z ∈ L₂, isEntP z = false) : (summ (L₁ ++ g :: L₂)).suf = true := by
  rw [summ_append, summ_cons, summ_free L₂ hL, good_not_ent g hg, hg]
  simp [Sm.comb, Sm.step]

/-- The summary of `L₁ g L₂` with `g` good and `L₁` free of `Δ` has a good part before its first
`Δ`. -/
private theorem pre_of (L₁ L₂ : List PkgLetter) (g : PkgLetter) (hg : isGoodP g = true)
    (hL : ∀ z ∈ L₁, isEntP z = false) : (summ (L₁ ++ g :: L₂)).pre = true := by
  rw [summ_append, summ_cons, summ_free L₁ hL, good_not_ent g hg, hg]
  simp [Sm.comb, Sm.step]

private theorem ffocus_spec (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (w tl : List PkgLetter)
    (a : Fin 2) (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    (summ tl).pre = true ∨ (summ tl).suf = true := by
  obtain ⟨i, o, hi, hs⟩ := ffocus_data R ℓ r right w hf hw
  obtain ⟨h1, h2⟩ := seek_tl w i r right _ hi hs a tl hrot
  cases right
  · obtain ⟨L₁, L₂, rfl, hL⟩ := h2 rfl
    exact Or.inl (pre_of L₁ L₂ _ rfl hL)
  · obtain ⟨L₁, L₂, rfl, hL⟩ := h1 rfl
    exact Or.inr (suf_of L₁ L₂ _ rfl hL)

private theorem K2_N (right : Bool) (a : Fin 2) (tl : List PkgLetter) (n : ℕ) :
    (if right = true then PkgLetter.lw (.proj n) :: wordW right a tl
      else wordW right a tl ++ [.lw (.proj n)]).Perm (.lw (.proj n) :: wordW right a tl) ∧
    (summ (if right = true then PkgLetter.lw (.proj n) :: wordW right a tl
      else wordW right a tl ++ [.lw (.proj n)])).ok = (summ (.lw (.res a) :: tl)).ok := by
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨List.perm_append_singleton _ _, ?_⟩
    rw [summ_append_bad _ rfl rfl, wordW_cyc]
  · simp only [↓reduceIte]
    refine ⟨List.Perm.refl _, ?_⟩
    rw [summ_cons_bad _ rfl rfl, wordW_cyc]

private theorem delta_light (c : Bool) :
    (if c = true then PkgOp.fcut1 else PkgOp.slash1).delta =
      ((0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ)) := by
  cases c <;> rfl

private theorem delta_plug (c : Bool) :
    (if c = true then PkgOp.fplug1 else PkgOp.insert1).delta =
      ((2 : ℤ), (0 : ℤ), (-1 : ℤ), (2 : ℤ)) := by
  cases c <;> rfl

/-- Table 2 and the class `𝓡` for every term of `fterms`. -/
private theorem fterms_spec (R : PkgExpr) (o : PkgOp) (R' : PkgExpr)
    (h : (o, R') ∈ R.fterms) : R'.charsP = R.charsP + o.delta ∧ (WfP R → WfP R') := by
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
            else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)]) = wordW right a tl := rfl
        rw [hWdef] at h
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with h | h
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                exact K1_spec R _ ℓ r w tl a hw hrot (ffocus_spec R ℓ r right w tl a hf hw hrot)
                  rfl rfl rfl rfl
              · rcases List.mem_cons.1 h with h | h
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                  rw [delta_light]
                  exact K2_spec R _ ℓ r w tl _ a right hw hrot (K2_N right a tl R.nb).1
                    (K2_N right a tl R.nb).2 rfl rfl rfl rfl
                · simp at h
            · -- cut at another resolvent of the expanded word
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 h
              split at hq
              · simp at hq
              · split at hq
                · rename_i b hqb
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  exact K3_spec R _ ℓ r q w tl a b right _ hw hrot hqb rfl rfl rfl rfl rfl
                · simp at hq
          · -- plug of a light weight
            obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
            split at hj
            · rename_i b y hjb
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
              rw [delta_plug]
              exact K4_spec R _ ℓ r j w tl a b y right hw hrot hjb rfl rfl rfl rfl
            · simp at hj
        · -- join with a resolvent of another word
          obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
          split at hj
          · simp at hj
          · rename_i hjℓ
            split at hj
            · simp at hj
            · rename_i f hf'
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · rename_i b hqb
                obtain ⟨F, hF⟩ := rotate_head f q b hqb
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                exact K5_core R _ ℓ r j q w tl f F a b right _ hw hrot hf' hjℓ hF rfl rfl rfl
                  rfl rfl
              · simp at hq
      · simp at h

/-- Table 2 [table_effect_of_operations_2]: each operation of the further expansion changes
`(m, n, u, S)` by its row. -/
theorem pkg_table2 (R : PkgExpr) (o : PkgOp) (R' : PkgExpr) (h : (o, R') ∈ R.fterms) :
    R'.charsP = R.charsP + o.delta :=
  (fterms_spec R o R' h).1

/-- The operations of the further expansion map the class `𝓡` of (5.79)–(5.81)
[further_expansion_expression_Type_1]–[further_expansion_expression_Type_3] into itself. -/
theorem pkg_step_wf (R : PkgExpr) (hR : R.wf = true) (R' : PkgExpr) (h : R' ∈ R.fstep) :
    R'.wf = true := by
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  exact (wf_iff R'').2 ((fterms_spec R o R'' hmem).2 ((wf_iff R).1 hR))

end RBMTransitionEdge

end
