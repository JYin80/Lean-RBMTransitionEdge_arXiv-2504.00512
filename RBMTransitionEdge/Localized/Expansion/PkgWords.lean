module

public import RBMTransitionEdge.Localized.Expansion.Words

@[expose] public section

/-!
# The words of the further expansion in the proof of Lemma 5.5

The class `𝓡` of (5.79)–(5.81) [further_expansion_expression_Type_1]–
[further_expansion_expression_Type_3] at fixed entry labels, its characters, the start
`(F 𝒢)_{ij} W ⋯ f ⋯` of (5.65) [explicit_reminder_terms_before_expansions], the derivative
structures of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] and Table 3
[table_Classification_of_Initial_Values].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A letter of the words of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: a letter of the loop words, or the matrix `Δ_{uv} = e_u e_vᵀ`
at the entry labels `u, v`. A word with `r ≥ 1` letters `Δ` is evaluated by its trace, which is the
product of the `r` heavy packages `(⋯)_{⋆⋆}` of (5.79) [further_expansion_expression_Type_1] cut
out by the `Δ`'s. -/
inductive PkgLetter
  | lw (x : LoopLetter)
  | ent (u v : ℕ)
  deriving DecidableEq

/-- An expression `c_𝓡 · 𝒲^{(u)} · Υ_n^{(m)}` of the class (5.79)–(5.81)
[further_expansion_expression_Type_1]–[further_expansion_expression_Type_3] at fixed entry labels,
with `c_𝓡 = cf · D^{dexp} N^{-S}`: `nb` bound block indices, the light weights
`⟨(𝒢_a - 𝔐_a) E_x⟩` listed by `(a, x)`, and the loops listed by their words; a loop with a letter
`Δ` is a product of heavy packages, a loop without one is a loop `⟨·⟩`. -/
structure PkgExpr where
  /-- The integer factor (sign and multiplicity) of the coefficient. -/
  cf : ℤ
  /-- The power of `D` in the coefficient. -/
  dexp : ℤ
  /-- The number `S` of factors `N⁻¹` in the coefficient. -/
  S : ℤ
  /-- The number of bound block indices. -/
  nb : ℕ
  /-- The light weights `⟨(𝒢_a - 𝔐_a) E_x⟩`, listed by `(a, x)`. -/
  weights : List (Fin 2 × ℕ)
  /-- The loops and products of heavy packages, each listed by its word. -/
  loops : List (List PkgLetter)
  deriving DecidableEq

/-- The characters `(m, n, u, S)` of Table 2 [table_effect_of_operations_2]: resolvents, factors
(each heavy package and each loop `⟨·⟩` counted once), light weights, factors `N⁻¹`. -/
def PkgExpr.charsP (R : PkgExpr) : ℤ × ℤ × ℤ × ℤ :=
  (((R.loops.map fun w => w.countP fun x => match x with
      | .lw (.res _) => true | _ => false).sum : ℕ),
    ((R.loops.map fun w => if w.any (fun x => match x with | .ent _ _ => true | _ => false)
      then w.countP (fun x => match x with | .ent _ _ => true | _ => false) else 1).sum : ℕ),
    R.weights.length, R.S)

/-- The class `𝓡` of (5.79)–(5.81): exactly one `Λ̃₁` and one `Λ̃₂`; every loop `⟨·⟩` and every
heavy package without `Λ̃` contains a resolvent; every block index is bound. -/
def PkgExpr.wf (R : PkgExpr) : Bool :=
  (R.loops.map fun w => w.count (.lw (.lamt 0))).sum == 1 &&
  (R.loops.map fun w => w.count (.lw (.lamt 1))).sum == 1 &&
  R.loops.all (fun w =>
    (if w.any (fun x => match x with | .ent _ _ => true | _ => false) then
      ((w.rotate (w.findIdx (fun x => match x with | .ent _ _ => true | _ => false) + 1)).dropLast
        |>.splitOnP fun x => match x with | .ent _ _ => true | _ => false)
     else [w]).all fun v => v.any fun x => match x with
      | .lw (.res _) => true | .lw (.lamt _) => true | _ => false) &&
  R.loops.all (fun w => w.all fun x => match x with
    | .lw (.proj y) => decide (y < R.nb) | _ => true) &&
  R.weights.all fun p => decide (p.2 < R.nb)

/-- The function `(F 𝒢)_{ij} W₁ ⋯ W_u f^{(1)} ⋯ f^{(n-1)}` of (5.65)
[explicit_reminder_terms_before_expansions] with the coefficient `c_𝒯`, as an expression of the
class `𝓡`: `(F 𝒢)_{ij} = Tr(F 𝒢 Δ_{ji})` with the labels `0 ↦ i`, `1 ↦ j`. -/
def LoopExpr.pkgStart (T : LoopExpr) : PkgExpr :=
  match T.focus with
  | none => ⟨0, 0, 0, 0, [], []⟩
  | some (ℓ, a, tl) =>
    ⟨1, T.dexp, T.S, T.nb, T.weights,
      (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
        (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw⟩

/-- One derivative `∂` with `∂𝒢 = -𝒢 Δ_{uv} 𝒢`, as a list of expressions: one term per resolvent
of a loop and per light weight; a loop `⟨·⟩` or a light weight that is hit becomes a heavy package,
`⟨X⟩ = (DN)⁻¹ Tr X`. -/
def PkgExpr.dent (R : PkgExpr) (u v : ℕ) : List PkgExpr :=
  ((List.range R.loops.length).flatMap fun ℓ =>
    match R.loops[ℓ]? with
    | none => []
    | some w => (List.range w.length).filterMap fun r =>
      match w[r]? with
      | some (PkgLetter.lw (LoopLetter.res a)) =>
        let pl : Bool := !(w.any fun x => match x with | .ent _ _ => true | _ => false)
        some { R with
          cf := -R.cf, dexp := if pl then R.dexp - 1 else R.dexp,
          S := if pl then R.S + 1 else R.S,
          loops := R.loops.set ℓ (w.take r ++ [.lw (.res a), .ent u v, .lw (.res a)] ++
            w.drop (r + 1)) }
      | _ => none) ++
  ((List.range R.weights.length).filterMap fun j =>
    match R.weights[j]? with
    | some (b, y) => some { R with
        cf := -R.cf, dexp := R.dexp - 1, S := R.S + 1, weights := R.weights.eraseIdx j,
        loops := R.loops ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]] }
    | none => none)

/-- The derivative structures of `∂^p_w ∂^q_w̄` (`w = h_{ij}`, labels `u ↦ i`, `v ↦ j`):
`∂_w` inserts `Δ_{ij}`, `∂_w̄` inserts `Δ_{ji}`, as in (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]. -/
def PkgExpr.dwirt (R : PkgExpr) (u v p q : ℕ) : List PkgExpr :=
  (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[p]
    ((fun L : List PkgExpr => L.flatMap fun R' => R'.dent v u)^[q] [R])


/-! ### Auxiliary facts: letters and the cyclic segments of a word -/

/-- The letter `x` is a matrix `Δ`. -/
private def isEntP (x : PkgLetter) : Bool :=
  match x with | .ent _ _ => true | _ => false

/-- The letter `x` is a resolvent `𝒢_a`. -/
private def isResP (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | _ => false

/-- The letter `x` is a resolvent or a `Λ̃`. -/
private def isGoodP (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | .lw (.lamt _) => true | _ => false

/-- The letter `x` of a loop word is a resolvent. -/
private def PW_isResL (x : LoopLetter) : Bool :=
  match x with | .res _ => true | _ => false

/-- Every segment cut out by the letters `Δ` of a list contains a resolvent or a `Λ̃`. -/
private def segsOK (l : List PkgLetter) : Bool :=
  (l.splitOnP isEntP).all fun v => v.any isGoodP

/-- The condition on the packages of one word in `PkgExpr.wf`: a word without `Δ` contains a
resolvent or a `Λ̃`, a word with `Δ` has this in each of its cyclic segments. -/
private def segOK (w : List PkgLetter) : Bool :=
  (if w.any isEntP then (w.rotate (w.findIdx isEntP + 1)).dropLast.splitOnP isEntP else [w]).all
    fun v => v.any isGoodP

/-- The factor of a word in the number `n` of factors: each package, and each word without `Δ`
once. -/
private def nfac (w : List PkgLetter) : ℕ :=
  if w.any isEntP then w.countP isEntP else 1

private theorem charsP_eq (R : PkgExpr) :
    R.charsP = ((((R.loops.map fun w => w.countP isResP).sum : ℕ) : ℤ),
      (((R.loops.map nfac).sum : ℕ) : ℤ), ((R.weights.length : ℕ) : ℤ), R.S) := rfl

/-- The block indices of the letters `proj` in the word `w` are all `< nb`. -/
private def projOK (nb : ℕ) (w : List PkgLetter) : Prop :=
  ∀ y : ℕ, PkgLetter.lw (.proj y) ∈ w → y < nb

/-- The class `𝓡` as a proposition. -/
private structure WfP (R : PkgExpr) : Prop where
  lam0 : (R.loops.map fun w => w.count (.lw (.lamt 0))).sum = 1
  lam1 : (R.loops.map fun w => w.count (.lw (.lamt 1))).sum = 1
  seg : ∀ w ∈ R.loops, segOK w = true
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
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
    exact ⟨h0, h1, h2, fun w hw => (projOK_iff _ _).1 (List.all_eq_true.2 (h3 w hw)), h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, fun w hw => List.all_eq_true.1 ((projOK_iff _ _).2 (h3 w hw))⟩, h4⟩

private theorem isEntP_ent (u v : ℕ) : isEntP (.ent u v) = true := rfl
private theorem isEntP_lw (x : LoopLetter) : isEntP (.lw x) = false := rfl

/-- The scan of a list of letters: the state is (all segments so far contain a resolvent or a
`Λ̃`, the current segment does). -/
private def scanStep (s : Bool × Bool) (x : PkgLetter) : Bool × Bool :=
  match x with
  | .ent _ _ => (s.1 && s.2, false)
  | .lw (.res _) => (s.1, true)
  | .lw (.lamt _) => (s.1, true)
  | .lw (.det _) => s
  | .lw (.proj _) => s

private theorem scan_eq : ∀ (l p : List PkgLetter) (ok : Bool), (∀ y ∈ p, isEntP y = false) →
    ((l.foldl scanStep (ok, p.any isGoodP)).1 && (l.foldl scanStep (ok, p.any isGoodP)).2) =
      (ok && segsOK (p ++ l))
  | [], p, ok, hp => by
      simp [segsOK, List.splitOnP_eq_singleton hp]
  | x :: l, p, ok, hp => by
      match x with
      | .ent u v =>
          have h := scan_eq l [] (ok && p.any isGoodP) (by simp)
          have h2 : (p ++ .ent u v :: l).splitOnP isEntP = p :: l.splitOnP isEntP := by
            rw [List.splitOnP_append_cons p l (isEntP_ent u v), List.splitOnP_eq_singleton hp]
            rfl
          simp only [List.foldl_cons, scanStep, List.any_nil, Bool.and_assoc] at h ⊢
          simp only [segsOK, h2, List.all_cons, List.nil_append] at h ⊢
          rw [h]
      | .lw y =>
          have hp' : ∀ z ∈ p ++ [PkgLetter.lw y], isEntP z = false := by
            intro z hz
            rcases List.mem_append.1 hz with hz | hz
            · exact hp z hz
            · rw [List.mem_singleton] at hz
              subst hz
              rfl
          have h := scan_eq l (p ++ [PkgLetter.lw y]) ok hp'
          have h3 : scanStep (ok, p.any isGoodP) (PkgLetter.lw y) =
              (ok, (p ++ [PkgLetter.lw y]).any isGoodP) := by
            cases y <;> simp [scanStep, isGoodP]
          rw [List.foldl_cons, h3, h]
          simp

private theorem segsOK_eq_scan (l : List PkgLetter) :
    segsOK l = ((l.foldl scanStep (true, false)).1 && (l.foldl scanStep (true, false)).2) := by
  have := scan_eq l [] true (by simp)
  simpa using this.symm

private theorem segsOK_free (l : List PkgLetter) (h : ∀ y ∈ l, isEntP y = false) :
    segsOK l = l.any isGoodP := by
  simp [segsOK, List.splitOnP_eq_singleton h]

private theorem segsOK_append_ent (U V : List PkgLetter) (u v : ℕ) :
    segsOK (U ++ .ent u v :: V) = (segsOK U && segsOK V) := by
  simp [segsOK, List.splitOnP_append_cons U V (isEntP_ent u v), List.all_append]

/-- Doubling a resolvent with a `Δ` in between does not change the segments. -/
private theorem segsOK_ins (X Y : List PkgLetter) (a : Fin 2) (u v : ℕ) :
    segsOK (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) =
      segsOK (X ++ .lw (.res a) :: Y) := by
  rw [segsOK_eq_scan, segsOK_eq_scan]
  simp only [List.append_assoc, List.foldl_append, List.cons_append, List.nil_append,
    List.foldl_cons]
  generalize X.foldl scanStep (true, false) = s
  obtain ⟨o, b⟩ := s
  simp [scanStep]

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

private theorem ent_split (A B P Q : List PkgLetter) (u v x y : ℕ)
    (hP : ∀ z ∈ P, isEntP z = false) (h : A ++ .ent u v :: B = P ++ .ent x y :: Q) :
    (A = P ∧ B = Q) ∨ ∃ A', A = P ++ .ent x y :: A' ∧ Q = A' ++ .ent u v :: B := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · cases as with
    | nil =>
        simp only [List.nil_append, List.append_nil] at h1 h2
        exact Or.inl ⟨h1.symm, (List.cons.inj h2).2⟩
    | cons z as' =>
        have hz : z = .ent u v := (List.cons.inj h2).1.symm
        have := hP z (by rw [h1]; simp)
        rw [hz] at this
        simp [isEntP_ent] at this
  · cases bs with
    | nil =>
        simp only [List.nil_append, List.append_nil] at h1 h2
        exact Or.inl ⟨h1, (List.cons.inj h2).2.symm⟩
    | cons z bs' =>
        have hz : z = .ent x y := (List.cons.inj h2).1.symm
        subst hz
        exact Or.inr ⟨bs', h1, (List.cons.inj h2).2⟩

/-- The cyclic segments of a word with a `Δ` at a given place: those of the list read from just
after that `Δ`. -/
private theorem segOK_decomp (A B : List PkgLetter) (u v : ℕ) :
    segOK (A ++ .ent u v :: B) = segsOK (B ++ A) := by
  obtain ⟨P, x, y, Q, hP, hw⟩ := exists_first_ent (A ++ .ent u v :: B) (by simp [isEntP])
  rw [hw, segOK_first P Q x y hP]
  rcases ent_split A B P Q u v x y hP hw with ⟨rfl, rfl⟩ | ⟨A', rfl, rfl⟩
  · rfl
  · have e1 : (A' ++ .ent u v :: B) ++ P = A' ++ .ent u v :: (B ++ P) := by simp
    have e2 : B ++ (P ++ .ent x y :: A') = (B ++ P) ++ .ent x y :: A' := by simp
    rw [e1, e2, segsOK_append_ent, segsOK_append_ent, Bool.and_comm]

/-- Doubling a resolvent of a word with a `Δ`, with a `Δ` in between, keeps its cyclic
segments good. -/
private theorem segOK_ins (X Y : List PkgLetter) (a : Fin 2) (u v : ℕ)
    (h : (X ++ .lw (.res a) :: Y).any isEntP = true) :
    segOK (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) =
      segOK (X ++ .lw (.res a) :: Y) := by
  obtain ⟨A, x, y, B, -, hw⟩ := exists_first_ent _ h
  rcases List.append_eq_append_iff.1 hw with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · cases as with
    | nil => simp at h2
    | cons z as' =>
        have hz : z = .lw (.res a) := (List.cons.inj h2).1.symm
        subst hz
        have hY : Y = as' ++ .ent x y :: B := (List.cons.inj h2).2
        subst hY h1
        have e1 : X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ (as' ++ .ent x y :: B) =
            (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ as') ++ .ent x y :: B := by simp
        have e2 : X ++ .lw (.res a) :: (as' ++ .ent x y :: B) =
            (X ++ .lw (.res a) :: as') ++ .ent x y :: B := by simp
        rw [e1, e2, segOK_decomp, segOK_decomp]
        simpa [List.append_assoc] using segsOK_ins (B ++ X) as' a u v
  · cases bs with
    | nil => simp at h2
    | cons z bs' =>
        have hz : z = .ent x y := (List.cons.inj h2).1.symm
        subst hz
        have hB : B = bs' ++ .lw (.res a) :: Y := (List.cons.inj h2).2
        subst hB h1
        have e1 : (A ++ .ent x y :: bs') ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y =
            A ++ .ent x y :: (bs' ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) := by simp
        have e2 : (A ++ .ent x y :: bs') ++ .lw (.res a) :: Y =
            A ++ .ent x y :: (bs' ++ .lw (.res a) :: Y) := by simp
        rw [e1, e2, segOK_decomp, segOK_decomp]
        simpa [List.append_assoc] using segsOK_ins bs' (Y ++ A) a u v

/-! ### Auxiliary facts: sums over lists and the derivative `dent` -/

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

/-- A list splits at the position of one of its entries. -/
private theorem split_at {α : Type*} (w : List α) (r : ℕ) (x : α) (h : w[r]? = some x) :
    w = w.take r ++ x :: w.drop (r + 1) := by
  obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem_cons_drop hr, List.take_append_drop]

private theorem free_of_any {l : List PkgLetter} (h : l.any isEntP = false) :
    ∀ z ∈ l, isEntP z = false := by
  intro z hz
  by_contra hne
  have : l.any isEntP = true := List.any_eq_true.2 ⟨z, hz, by simpa using hne⟩
  rw [this] at h
  exact absurd h (by simp)

/-- One derivative hitting the resolvent `𝒢_a` of the word `X 𝒢_a Y` in position `ℓ`: the
expression stays in the class `𝓡`, and its characters change by one of two rows. -/
private theorem dent_loop (R R' : PkgExpr) (ℓ : ℕ) (X Y : List PkgLetter) (a : Fin 2) (u v : ℕ)
    (hℓ : R.loops[ℓ]? = some (X ++ .lw (.res a) :: Y)) (hR : WfP R)
    (hl : R'.loops = R.loops.set ℓ (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y))
    (hw : R'.weights = R.weights) (hnb : R'.nb = R.nb)
    (hS : R'.S = if (X ++ .lw (.res a) :: Y).any isEntP then R.S else R.S + 1) :
    WfP R' ∧ (R'.charsP = R.charsP + (1, 1, 0, 0) ∨ R'.charsP = R.charsP + (1, 0, 0, 1)) := by
  have hmem : X ++ .lw (.res a) :: Y ∈ R.loops := List.mem_of_getElem? hℓ
  have hcount : ∀ o : Fin 2, (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).count
      (PkgLetter.lw (.lamt o)) = (X ++ .lw (.res a) :: Y).count (PkgLetter.lw (.lamt o)) := by
    intro o
    simp [List.count_append]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 0))) R.loops ℓ _
      (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
    have h2 := hR.lam0
    rw [hl]
    simp only [hcount] at h1
    omega
  · have h1 := sum_map_set (fun w => w.count (.lw (.lamt 1))) R.loops ℓ _
      (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
    have h2 := hR.lam1
    rw [hl]
    simp only [hcount] at h1
    omega
  · intro w₁ hw₁
    rw [hl] at hw₁
    rcases List.mem_or_eq_of_mem_set hw₁ with h | rfl
    · exact hR.seg w₁ h
    · cases ha : (X ++ .lw (.res a) :: Y).any isEntP
      · have hfree := free_of_any ha
        have e : X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y =
            (X ++ [.lw (.res a)]) ++ .ent u v :: (.lw (.res a) :: Y) := by simp
        rw [e, segOK_decomp, segsOK_free]
        · simp [isGoodP]
        · intro z hz
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff,
            or_false] at hz
          rcases hz with (hz | hz) | hz | hz
          all_goals first | (subst hz; rfl) | exact hfree z (by simp [hz])
      · rw [segOK_ins X Y a u v ha]
        exact hR.seg _ hmem
  · intro w₁ hw₁
    rw [hl] at hw₁
    rw [hnb]
    rcases List.mem_or_eq_of_mem_set hw₁ with h | rfl
    · exact hR.proj w₁ h
    · intro y hy
      apply hR.proj _ hmem y
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hy ⊢
      rcases hy with (hy | hy | hy | hy) | hy
      · exact Or.inl hy
      · simp at hy
      · simp at hy
      · simp at hy
      · exact Or.inr (Or.inr hy)
  · rw [hw, hnb]; exact hR.wt
  · rw [charsP_eq, charsP_eq, hl, hw, hS]
    have hr := sum_map_set (fun w => w.countP isResP) R.loops ℓ _
      (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
    have hn := sum_map_set nfac R.loops ℓ _
      (X ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ Y) hℓ
    have c1 : (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).countP isResP =
        (X ++ .lw (.res a) :: Y).countP isResP + 1 := by
      simp [List.countP_append, List.countP_cons, isResP]
      omega
    have c2 : (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).countP isEntP =
        (X ++ .lw (.res a) :: Y).countP isEntP + 1 := by
      simp [List.countP_append, List.countP_cons, isEntP]
      omega
    have c3 : (X ++ [PkgLetter.lw (.res a), .ent u v, .lw (.res a)] ++ Y).any isEntP = true := by
      simp [isEntP]
    simp only [nfac, c3, ↓reduceIte] at hn
    beta_reduce at hr hn
    cases ha : (X ++ .lw (.res a) :: Y).any isEntP
    · right
      have hz : (X ++ .lw (.res a) :: Y).countP isEntP = 0 := by
        rw [List.countP_eq_zero]
        intro z hz
        simp [free_of_any ha z hz]
      simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn ⊢
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega
    · left
      simp only [ha, ↓reduceIte] at hn ⊢
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega

/-- One derivative hitting the light weight `(b, y)` in position `j`: it becomes the loop
`⟨𝒢_b Δ 𝒢_b E_y⟩`; the expression stays in the class `𝓡`, and its characters change by the
third row. -/
private theorem dent_weight (R R' : PkgExpr) (j : ℕ) (b : Fin 2) (y u v : ℕ)
    (hj : R.weights[j]? = some (b, y)) (hR : WfP R)
    (hl : R'.loops = R.loops ++ [[.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)]])
    (hw : R'.weights = R.weights.eraseIdx j) (hnb : R'.nb = R.nb) (hS : R'.S = R.S + 1) :
    WfP R' ∧ R'.charsP = R.charsP + (2, 1, -1, 1) := by
  have hy : y < R.nb := hR.wt _ (List.mem_of_getElem? hj)
  have hj' : j < R.weights.length := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hR.lam0
    rw [hl]
    simpa [List.count_cons] using this
  · have := hR.lam1
    rw [hl]
    simpa [List.count_cons] using this
  · intro w₁ hw₁
    rw [hl] at hw₁
    rcases List.mem_append.1 hw₁ with h | h
    · exact hR.seg w₁ h
    · rw [List.mem_singleton] at h
      subst h
      have e : [PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] =
          [.lw (.res b)] ++ .ent u v :: [.lw (.res b), .lw (.proj y)] := rfl
      rw [e, segOK_decomp, segsOK_free]
      · simp [isGoodP]
      · intro z hz
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with (hz | hz) | hz <;> subst hz <;> rfl
  · intro w₁ hw₁
    rw [hl] at hw₁
    rw [hnb]
    rcases List.mem_append.1 hw₁ with h | h
    · exact hR.proj w₁ h
    · rw [List.mem_singleton] at h
      subst h
      intro y' hy'
      have hyy : y' = y := by simpa using hy'
      rw [hyy]
      exact hy
  · intro p hp
    rw [hw] at hp
    rw [hnb]
    exact hR.wt p (List.mem_of_mem_eraseIdx hp)
  · rw [charsP_eq, charsP_eq, hl, hw, hS]
    have hlen := List.length_eraseIdx_of_lt hj'
    have hres : ([PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] :
        List PkgLetter).countP isResP = 2 := by
      simp [List.countP_cons, isResP]
    have hnf : nfac [PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] = 1 := by
      simp [nfac, isEntP, List.countP_cons]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hres, hnf, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> omega

/-- One derivative `∂` with `∂𝒢 = -𝒢 Δ_{uv} 𝒢` keeps the class `𝓡`, and changes the characters by
one of the three rows `(1, 1, 0, 0)` (a resolvent of a word with `Δ`), `(1, 0, 0, 1)` (a resolvent
of a word without `Δ`), `(2, 1, -1, 1)` (a light weight). -/
private theorem dent_spec (R R' : PkgExpr) (u v : ℕ) (hR : R.wf = true) (h : R' ∈ R.dent u v) :
    R'.wf = true ∧ (R'.charsP = R.charsP + (1, 1, 0, 0) ∨ R'.charsP = R.charsP + (1, 0, 0, 1) ∨
      R'.charsP = R.charsP + (2, 1, -1, 1)) := by
  rw [wf_iff] at hR ⊢
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
        have hw := split_at w r _ hr
        have hℓ' : R.loops[ℓ]? =
            some (w.take r ++ .lw (.res a) :: w.drop (r + 1)) := by rw [← hw]; exact hℓ
        have := dent_loop R R' ℓ (w.take r) (w.drop (r + 1)) a u v hℓ' hR (by rw [← h])
          (by rw [← h]) (by rw [← h])
          (by
            rw [← hw, ← h]
            change (if (!w.any isEntP) = true then R.S + 1 else R.S) =
              if w.any isEntP = true then R.S else R.S + 1
            cases w.any isEntP <;> rfl)
        exact ⟨this.1, this.2.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
      · simp at h
  · obtain ⟨j, -, h⟩ := List.mem_filterMap.1 h
    split at h
    · rename_i b y hj
      simp only [Option.some.injEq] at h
      have := dent_weight R R' j b y u v hj hR (by rw [← h]) (by rw [← h]) (by rw [← h])
        (by rw [← h])
      exact ⟨this.1, Or.inr (Or.inr this.2)⟩
    · simp at h

/-! ### Auxiliary facts: the start `pkgStart` -/

/-- The focused loop `w` of `T` is a permutation of `𝒢_a · tl`. -/
private theorem focus_data {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ w : List LoopLetter, T.loops[ℓ]? = some w ∧ w.Perm (.res a :: tl) := by
  unfold LoopExpr.focus at h
  dsimp only at h
  generalize (if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = o at h
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i a' tl' hrot
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨w, hw, ?_⟩
          rw [← hrot]
          exact (List.rotate_perm w r).symm
        · cases h
      · cases h

private theorem pkgStart_eq {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    T.pkgStart = ⟨1, T.dexp, T.S, T.nb, T.weights,
      (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
        (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw⟩ := by
  unfold LoopExpr.pkgStart
  rw [h]

private theorem countP_lw (l : List LoopLetter) :
    (l.map PkgLetter.lw).countP isResP = l.countP PW_isResL := by
  rw [List.countP_map]
  congr 1
  funext x
  cases x <;> rfl

private theorem any_lw (l : List LoopLetter) : (l.map PkgLetter.lw).any isEntP = false := by
  rw [Bool.eq_false_iff, Ne, List.any_eq_true]
  rintro ⟨z, hz, hz'⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
  simp [isEntP_lw] at hz'

private theorem nfac_lw (l : List LoopLetter) : nfac (l.map PkgLetter.lw) = 1 := by
  simp only [nfac, any_lw, Bool.false_eq_true, ↓reduceIte]

/-- The heavy package of `pkgStart`. -/
private abbrev pkgWord (a : Fin 2) (tl : List LoopLetter) : List PkgLetter :=
  ((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++ [PkgLetter.ent 1 0]

private theorem cntRes_pkgWord (a : Fin 2) (tl : List LoopLetter) :
    (pkgWord a tl).countP isResP = tl.countP PW_isResL + 1 := by
  rw [pkgWord, List.countP_append, countP_lw]
  simp [List.countP_append, List.countP_cons, PW_isResL, isResP]

private theorem nfac_pkgWord (a : Fin 2) (tl : List LoopLetter) : nfac (pkgWord a tl) = 1 := by
  have h1 : (pkgWord a tl).any isEntP = true := by simp [pkgWord, isEntP]
  have h2 : (pkgWord a tl).countP isEntP = 1 := by
    simp only [pkgWord, List.countP_append]
    have : ((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw).countP isEntP = 0 := by
      rw [List.countP_eq_zero]
      intro z hz
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
      simp [isEntP_lw]
    rw [this]
    simp [isEntP]
  simp [nfac, h1, h2]

private theorem pkgStart_charsP {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) : T.pkgStart.charsP = T.charsZ := by
  obtain ⟨w, hw, hperm⟩ := focus_data h
  have hz : T.charsZ = ((((T.loops.map fun w => w.countP PW_isResL).sum : ℕ) : ℤ),
      ((T.loops.length : ℕ) : ℤ), ((T.weights.length : ℕ) : ℤ), ((T.S : ℕ) : ℤ)) := rfl
  have hsum := sum_map_eraseIdx (fun w => w.countP PW_isResL) T.loops ℓ w hw
  have hperm' := hperm.countP_eq PW_isResL
  have hcons : (LoopLetter.res a :: tl).countP PW_isResL = tl.countP PW_isResL + 1 := by
    simp [List.countP_cons, PW_isResL]
  have hlen : T.loops.length = (T.loops.eraseIdx ℓ).length + 1 := by
    have hl : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
    rw [List.length_eraseIdx_of_lt hl]
    omega
  rw [pkgStart_eq h, charsP_eq, hz]
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, countP_lw, nfac_lw]
  have hn : ((T.loops.eraseIdx ℓ).map fun _ => 1).sum = (T.loops.eraseIdx ℓ).length := by
    simp [List.map_const', List.sum_replicate]
  simp only [cntRes_pkgWord, nfac_pkgWord, hn]
  beta_reduce at hsum hperm'
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, trivial⟩ <;> omega

private theorem count_lw (l : List LoopLetter) (x : LoopLetter) :
    (l.map PkgLetter.lw).count (PkgLetter.lw x) = l.count x :=
  List.count_map_of_injective l PkgLetter.lw (fun _ _ h => PkgLetter.lw.inj h) x

private theorem any_good (w : List LoopLetter)
    (h : (w.contains (.lamt 0) || w.contains (.lamt 1) || w.any fun x => match x with
      | .res _ => true | _ => false) = true) : (w.map PkgLetter.lw).any isGoodP = true := by
  simp only [Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem] at h
  rw [List.any_eq_true]
  rcases h with (h | h) | ⟨x, hx, hx'⟩
  · exact ⟨.lw (.lamt 0), List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩
  · exact ⟨.lw (.lamt 1), List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩
  · refine ⟨.lw x, List.mem_map.2 ⟨_, hx, rfl⟩, ?_⟩
    cases x <;> simp_all [isGoodP]

private theorem pkgStart_wf {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (h : T.focus = some (ℓ, a, tl)) : T.pkgStart.wf = true := by
  rw [wf_iff]
  obtain ⟨w, hw, hperm⟩ := focus_data h
  unfold LoopExpr.wf at hT
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hT
  have h3' : ∀ w ∈ T.loops, ∀ y : ℕ, LoopLetter.proj y ∈ w → y < T.nb := fun w hw y hy => by
    simpa using h3 w hw _ hy
  rw [pkgStart_eq h]
  have hlam : ∀ o : Fin 2, (T.loops.map fun w => w.count (LoopLetter.lamt o)).sum = 1 →
      (((pkgWord a tl) :: (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw).map
        fun w => w.count (PkgLetter.lw (.lamt o))).sum = 1 := by
    intro o ho
    have hs := sum_map_eraseIdx (fun w => w.count (LoopLetter.lamt o)) T.loops ℓ w hw
    have hp := hperm.count_eq (LoopLetter.lamt o)
    have hc : (LoopLetter.res a :: tl).count (LoopLetter.lamt o) =
        tl.count (LoopLetter.lamt o) := by
      simp
    have hP : (pkgWord a tl).count (PkgLetter.lw (.lamt o)) = tl.count (LoopLetter.lamt o) := by
      rw [pkgWord, List.count_append, count_lw]
      simp [List.count_append]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, count_lw]
    beta_reduce at hs
    rw [hP]
    omega
  have hmemw : ∀ w' ∈ T.loops.eraseIdx ℓ, w' ∈ T.loops := fun w' hw' =>
    List.mem_of_mem_eraseIdx hw'
  refine ⟨hlam 0 h0, hlam 1 h1, ?_, ?_, ?_⟩
  · intro w₁ hw₁
    rcases List.mem_cons.1 hw₁ with rfl | hw₁
    · rw [segOK_decomp, List.nil_append, segsOK_free]
      · rw [List.any_eq_true]
        exact ⟨.lw (.res a), List.mem_map.2 ⟨.res a, by simp, rfl⟩, rfl⟩
      · intro z hz
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
        rfl
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw₁
      have := any_good w' (h2 w' (hmemw w' hw'))
      unfold segOK
      rw [any_lw]
      simp only [Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
      exact this
  · intro w₁ hw₁ y hy
    rcases List.mem_cons.1 hw₁ with rfl | hw₁
    · have hy' : LoopLetter.proj y ∈ tl := by
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
          or_false] at hy
        rcases hy with ⟨x, hx, hxy⟩ | hy
        · have hxy' : x = LoopLetter.proj y := PkgLetter.lw.inj hxy
          subst hxy'
          simpa using hx
        · simp at hy
      have hyw : LoopLetter.proj y ∈ w :=
        hperm.mem_iff.2 (List.mem_cons_of_mem _ hy')
      exact h3' w (List.mem_of_getElem? hw) _ hyw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw₁
      obtain ⟨x, hx, hxy⟩ := List.mem_map.1 hy
      have hxy' : x = LoopLetter.proj y := PkgLetter.lw.inj hxy
      subst hxy'
      exact h3' w' (hmemw w' hw') _ hx
  · exact h4

/-- Two derivatives starting from an expression of the class `𝓡`: the result lies in the class,
and its characters exceed those of the start by one of the eight rows of Table 3
[table_Classification_of_Initial_Values]. -/
private theorem two_hits (R0 R : PkgExpr) (u₁ v₁ u₂ v₂ : ℕ) (hw : R0.wf = true)
    (h : R ∈ ([R0].flatMap fun R' => R'.dent u₁ v₁).flatMap fun R' => R'.dent u₂ v₂) :
    R.wf = true ∧ R.charsP - R0.charsP ∈ [((2 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ)), (3, 2, -1, 1),
      (2, 1, 0, 1), (3, 1, -1, 2), (4, 2, -2, 2), (3, 2, -1, 1), (2, 0, 0, 2), (2, 1, 0, 1)] := by
  obtain ⟨R1, h1, h2⟩ := List.mem_flatMap.1 h
  obtain ⟨R0', h0', h1'⟩ := List.mem_flatMap.1 h1
  have e : R0' = R0 := by simpa using h0'
  subst e
  obtain ⟨hw1, hc1⟩ := dent_spec R0' R1 u₁ v₁ hw h1'
  obtain ⟨hw2, hc2⟩ := dent_spec R1 R u₂ v₂ hw1 h2
  refine ⟨hw2, ?_⟩
  rcases hc1 with hc1 | hc1 | hc1 <;> rcases hc2 with hc2 | hc2 | hc2 <;> rw [hc2, hc1] <;>
    simp only [add_assoc, add_sub_cancel_left] <;> decide

/-- Table 3 [table_Classification_of_Initial_Values]: for `p + q = 2`, every derivative structure
`𝓡₀` of `𝓡_𝒯(p, q)` lies in the class `𝓡` and its characters exceed those of `𝒯` by one of the
eight rows. -/
theorem pkg_table3 (T : LoopExpr) (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ)
    (hpq : p + q = 2) (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) :
    R.wf = true ∧ R.charsP - T.charsZ ∈ [((2 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ)), (3, 2, -1, 1),
      (2, 1, 0, 1), (3, 1, -1, 2), (4, 2, -2, 2), (3, 2, -1, 1), (2, 0, 0, 2), (2, 1, 0, 1)] := by
  obtain ⟨⟨ℓ, a, tl⟩, hfoc⟩ := Option.isSome_iff_exists.1 hf
  have hw0 := pkgStart_wf hT hfoc
  have hc0 := pkgStart_charsP hfoc
  rcases (show p = 0 ∧ q = 2 ∨ p = 1 ∧ q = 1 ∨ p = 2 ∧ q = 0 by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h : R ∈ ([T.pkgStart].flatMap fun R' => R'.dent 1 0).flatMap fun R' => R'.dent 1 0 := hR
    have := two_hits _ _ _ _ _ _ hw0 h
    rwa [hc0] at this
  · have h : R ∈ ([T.pkgStart].flatMap fun R' => R'.dent 1 0).flatMap fun R' => R'.dent 0 1 := hR
    have := two_hits _ _ _ _ _ _ hw0 h
    rwa [hc0] at this
  · have h : R ∈ ([T.pkgStart].flatMap fun R' => R'.dent 0 1).flatMap fun R' => R'.dent 0 1 := hR
    have := two_hits _ _ _ _ _ _ hw0 h
    rwa [hc0] at this

end RBMTransitionEdge

end
