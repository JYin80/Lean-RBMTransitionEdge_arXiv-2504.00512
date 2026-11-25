module

public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.PkgCounts
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.PkgEval
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgEval

@[expose] public section

/-!
# The factors of an expression of the further class

The value of an expression of the class `𝓡` of (5.79)–(5.81)
[further_expansion_expression_Type_1]–[further_expansion_expression_Type_3] as its coefficient
times a sum over the block indices of a product of factors (package entries, loops, light
weights), with a flag per resolvent letter: the factorization behind (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] in the proof of Lemma 5.5
[claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A letter of a factor of the further-class bound: a resolvent of slot `a` with its own flag
(`true`: the adjoint), `𝔐_a` (`true`: `𝔐_a - 𝔐_aᴴ`), `E_x`, `Λ̃`. -/
inductive FLet
  | res (a : Fin 2) (f : Bool)
  | det (a : Fin 2) (pr : Bool)
  | proj (x : ℕ)
  | lamt
  deriving DecidableEq

/-- A factor: the entry `(w)_{κ x, κ y}` of a heavy package, a loop `⟨w⟩`, or a light weight
`⟨(𝒢_a - 𝔐_a) E_x⟩`. -/
inductive FFac
  | ent (x y : ℕ) (w : List FLet)
  | loop (w : List FLet)
  | wt (a : Fin 2) (x : ℕ)
  deriving DecidableEq

/-- The matrix of a letter at the array `h`: `res(h + c_a Λ, z_a)` or its adjoint, `𝔐_a` or
`𝔐_a - 𝔐_aᴴ`, `E_x`, `Λ̃`. -/
def FLet.mat {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) : FLet → Matrix (Idx D N) (Idx D N) ℂ
  | .res a f => if f then (RBMTransitionEdge.res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))ᴴ
      else RBMTransitionEdge.res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a)
  | .det a pr => if pr then e.M a - (e.M a)ᴴ else e.M a
  | .proj x => e.E ι x
  | .lamt => e.Lt

/-- The value of a factor at the labels `κ`. -/
def FFac.val {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) : FFac → ℂ
  | .ent x y w => (w.map (FLet.mat e ι h)).prod (κ x) (κ y)
  | .loop w => ntr (w.map (FLet.mat e ι h)).prod
  | .wt a x => ntr ((e.G h a - e.M a) * e.E ι x)

/-- A letter of the class `𝓡` as a factor letter, with the flags `s` and the paired slots `pr`. -/
def PkgLetter.flet (s pr : Fin 2 → Bool) : PkgLetter → Option FLet
  | .lw (.res a) => some (.res a (s a))
  | .lw (.det a) => some (.det a (pr a))
  | .lw (.proj x) => some (.proj x)
  | .lw (.lamt _) => some .lamt
  | .ent _ _ => none

/-- The factors of an expression of the class `𝓡` of (5.79)–(5.81)
[further_expansion_expression_Type_1]–[further_expansion_expression_Type_3]: its light weights,
its loops, and one entry per package of a word with `Δ`, between the labels `v` of the `Δ_{uv}`
before it and `u'` of the `Δ_{u'v'}` after it. -/
def PkgExpr.ffacs (R : PkgExpr) (s pr : Fin 2 → Bool) : List FFac :=
  R.weights.map (fun p => FFac.wt p.1 p.2) ++
  R.loops.flatMap fun w => if w.any PkgLetter.isEnt then
    let E := (w.rotate (w.findIdx PkgLetter.isEnt)).filterMap fun z => match z with
      | .ent u v => some (u, v)
      | _ => none
    let S := pkgSegs w
    (List.range S.length).filterMap fun t => match S[t]?, E[t]?, E[(t + 1) % E.length]? with
      | some σ, some e₀, some e₁ => some (FFac.ent e₀.2 e₁.1 (σ.filterMap (PkgLetter.flet s pr)))
      | _, _, _ => none
  else [FFac.loop (w.filterMap (PkgLetter.flet s pr))]

/-! ### The matrix of a word without `Δ` as a product of factor letters -/

open private isEntP exists_first_ent findIdx_ent from RBMTransitionEdge.Localized.Expansion.PkgWords
open private PB_segs_ent PB_split PB_trace_ent PB_entry_ent
  from RBMTransitionEdge.Localized.Expansion.PkgBound
open private PE_wm_nil PE_wm_cons PE_lm_res PE_lm_det PE_lm_proj PE_lm_lamt
  from RBMTransitionEdge.Localized.Expansion.PkgEval

/-- The labels `(u, v)` of the letters `Δ_{uv}` of a list, in order. -/
private def FF_ents (Z : List PkgLetter) : List (ℕ × ℕ) :=
  Z.filterMap fun z => match z with
    | .ent u v => some (u, v)
    | _ => none

private lemma FF_ents_free : ∀ Z : List PkgLetter, (∀ y ∈ Z, isEntP y = false) →
    FF_ents Z = []
  | [], _ => rfl
  | .lw y :: Z, h => by
    have := FF_ents_free Z fun z hz => h z (List.mem_cons_of_mem _ hz)
    simpa [FF_ents] using this
  | .ent u v :: Z, h => by simp [isEntP] at h

private lemma FF_ents_ent (P Q : List PkgLetter) (x y : ℕ) (hP : ∀ z ∈ P, isEntP z = false) :
    FF_ents (P ++ .ent x y :: Q) = (x, y) :: FF_ents Q := by
  have h1 : FF_ents (P ++ .ent x y :: Q) = FF_ents P ++ FF_ents (.ent x y :: Q) :=
    List.filterMap_append
  rw [h1, FF_ents_free P hP]
  simp [FF_ents]

/-- The number of pieces of a list cut at its letters `Δ` is one more than their number. -/
private lemma FF_len (Z : List PkgLetter) :
    (Z.splitOnP isEntP).length = (FF_ents Z).length + 1 := by
  rw [(PB_split (fun _ => false) (fun _ _ => rfl) Z).2.1, FF_ents, List.length_filterMap_eq_countP]
  congr 2
  funext a
  cases a <;> simp [isEntP]

private lemma FF_herm {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (a : Fin 2) :
    (Matrix.of h + (e.c a : ℂ) • lam D N e.A).IsHermitian := by
  refine hh.add ?_
  have := (lam_isHermitian D N e.A).eq
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, this]
  simp

/-- The letter `𝒢_a` with its flag `e.s a` is the matrix `𝒢_a`. -/
private lemma FF_mat_res {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) {nb : ℕ} (ι : Fin nb → Fin D)
    (a : Fin 2) : FLet.mat e ι h (.res a (e.s a)) = e.G h a := by
  unfold FLet.mat LoopEnv.G
  cases hs : e.s a
  · simp
  · simpa using (res_conj _ (FF_herm e h hh a) (e.z a) (hz a)).symm

/-- A word without `Δ` is the product of the matrices of its factor letters. -/
private lemma FF_free {D N : ℕ} (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    {nb : ℕ} (ι : Fin nb → Fin D) (κ : ℕ → Idx D N) :
    ∀ σ : List PkgLetter, (∀ y ∈ σ, isEntP y = false) →
      pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ σ =
        ((σ.filterMap (PkgLetter.flet e.s pr)).map (FLet.mat e ι h)).prod
  | [], _ => by simp [PE_wm_nil]
  | x :: σ, hσ => by
    have ih := FF_free e pr hz h hh ι κ σ fun y hy => hσ y (List.mem_cons_of_mem _ hy)
    rw [PE_wm_cons, ih]
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp [PE_lm_res, PkgLetter.flet, FF_mat_res e hz h hh ι a]
    · simp [PE_lm_det, PkgLetter.flet, LoopEnv.pairM, FLet.mat]
    · simp [PE_lm_proj, PkgLetter.flet, FLet.mat]
    · simp [PE_lm_lamt, PkgLetter.flet, FLet.mat]
    · have := hσ (.ent u v) List.mem_cons_self
      simp [isEntP] at this

/-! ### The entries of a word as a product along its letters `Δ` -/

section Chain

variable {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
  (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)

/-- An entry of a word is the product of the entries of its pieces cut at the letters `Δ`: the
`t`-th piece is read between the label `v` of the `(t-1)`-th `Δ_{uv}` (or the row `a`) and the label
`u` of the `t`-th (or the column `b`). -/
private lemma FF_chain : ∀ (n : ℕ) (Z : List PkgLetter), Z.length ≤ n → ∀ a b : Idx D N,
    pkgWordMat G M E L κ Z a b = ∏ t ∈ Finset.range (Z.splitOnP isEntP).length,
      pkgWordMat G M E L κ ((Z.splitOnP isEntP).getD t [])
        (if t = 0 then a else κ ((FF_ents Z).getD (t - 1) (0, 0)).2)
        (if t < (FF_ents Z).length then κ ((FF_ents Z).getD t (0, 0)).1 else b)
  | n, Z, hn, a, b => by
    by_cases hZ : Z.any isEntP = true
    · obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent Z hZ
      have hs : (P ++ .ent x y :: Q).splitOnP isEntP = P :: Q.splitOnP isEntP :=
        List.splitOnP_append_cons_of_forall_mem hP _ rfl Q
      rw [hs, FF_ents_ent P Q x y hP, PB_entry_ent]
      match n with
      | 0 => simp at hn
      | n + 1 =>
        have hQ : Q.length ≤ n := by simp at hn; omega
        rw [FF_chain n Q hQ (κ y) b, List.length_cons, Finset.prod_range_succ', mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun k _ => ?_
          rcases k with _ | k <;> simp
    · have hf : ∀ y ∈ Z, isEntP y = false := by simpa using hZ
      rw [List.splitOnP_eq_singleton hf, FF_ents_free Z hf]
      simp

end Chain

/-! ### The factors of one word -/

/-- The entries of the packages of a word with `Δ`, as in `PkgExpr.ffacs`: the `t`-th piece `S[t]`
between the labels `E[t].2` and `E[t+1].1` of the letters `Δ`, cyclically. -/
private def FF_pk (s pr : Fin 2 → Bool) (S : List (List PkgLetter)) (E : List (ℕ × ℕ)) :
    List FFac :=
  (List.range S.length).filterMap fun t => match S[t]?, E[t]?, E[(t + 1) % E.length]? with
    | some σ, some e₀, some e₁ => some (FFac.ent e₀.2 e₁.1 (σ.filterMap (PkgLetter.flet s pr)))
    | _, _, _ => none

/-- The factors of one word of an expression of the class `𝓡`, as in `PkgExpr.ffacs`. -/
private def FF_wf (s pr : Fin 2 → Bool) (w : List PkgLetter) : List FFac :=
  if w.any PkgLetter.isEnt then
    FF_pk s pr (pkgSegs w) ((w.rotate (w.findIdx PkgLetter.isEnt)).filterMap fun z => match z with
      | .ent u v => some (u, v)
      | _ => none)
  else [FFac.loop (w.filterMap (PkgLetter.flet s pr))]

private lemma FF_ffacs (R : PkgExpr) (s pr : Fin 2 → Bool) :
    R.ffacs s pr = R.weights.map (fun p => FFac.wt p.1 p.2) ++ R.loops.flatMap (FF_wf s pr) :=
  rfl

private lemma FF_filterMap_prod {α : Type*} (f : ℕ → Option α) (g : ℕ → α) (v : α → ℂ) :
    ∀ n, (∀ t < n, f t = some (g t)) →
      (((List.range n).filterMap f).map v).prod = ∏ t ∈ Finset.range n, v (g t)
  | 0, _ => by simp
  | n + 1, hf => by
    rw [List.range_succ, List.filterMap_append, List.map_append, List.prod_append,
      Finset.prod_range_succ, FF_filterMap_prod f g v n fun t ht => hf t (by omega)]
    simp [hf n (by omega)]

private lemma FF_pk_prod (s pr : Fin 2 → Bool) (S : List (List PkgLetter)) (E : List (ℕ × ℕ))
    (hlen : S.length = E.length) (v : FFac → ℂ) :
    ((FF_pk s pr S E).map v).prod = ∏ t ∈ Finset.range S.length,
      v (FFac.ent (E.getD t (0, 0)).2 (E.getD ((t + 1) % E.length) (0, 0)).1
        ((S.getD t []).filterMap (PkgLetter.flet s pr))) := by
  refine FF_filterMap_prod _ _ v S.length fun t ht => ?_
  have h1 : t < E.length := hlen ▸ ht
  have h2 : (t + 1) % E.length < E.length := Nat.mod_lt _ (by omega)
  simp [List.getElem?_eq_getElem ht, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    List.getD_eq_getElem?_getD]

/-- The value of a word with a letter `Δ` is the product of the entries of its packages. -/
private lemma FF_wf_ent {D N : ℕ} (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    {nb : ℕ} (ι : Fin nb → Fin D) (κ : ℕ → Idx D N) (P Q : List PkgLetter) (x y : ℕ)
    (hP : ∀ z ∈ P, isEntP z = false) :
    (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ (P ++ .ent x y :: Q)).trace =
      ((FF_wf e.s pr (P ++ .ent x y :: Q)).map (FFac.val e ι κ h)).prod := by
  have hw : (P ++ .ent x y :: Q).any PkgLetter.isEnt = true := by simp [PkgLetter.isEnt]
  have hrot : (P ++ .ent x y :: Q).rotate ((P ++ .ent x y :: Q).findIdx PkgLetter.isEnt) =
      .ent x y :: (Q ++ P) := by
    rw [show (P ++ .ent x y :: Q).findIdx PkgLetter.isEnt = P.length from findIdx_ent P Q x y hP]
    exact List.rotate_append_length_eq P (.ent x y :: Q)
  have hS : pkgSegs (P ++ .ent x y :: Q) = (Q ++ P).splitOnP isEntP := PB_segs_ent P Q x y hP
  have hE : ((.ent x y :: (Q ++ P) : List PkgLetter).filterMap fun z => match z with
      | .ent u v => some (u, v)
      | _ => none) = (x, y) :: FF_ents (Q ++ P) := rfl
  have hl : (pkgSegs (P ++ .ent x y :: Q)).length = ((x, y) :: FF_ents (Q ++ P)).length := by
    rw [hS, FF_len]; rfl
  rw [FF_wf]
  simp only [hw, ↓reduceIte]
  rw [hrot, hE, hS, FF_pk_prod _ _ _ _ (hS ▸ hl) _, PB_trace_ent,
    FF_chain _ _ _ _ κ _ (Q ++ P) le_rfl]
  refine Finset.prod_congr rfl fun t ht => ?_
  have hfree : ∀ z ∈ (Q ++ P).splitOnP isEntP, ∀ y ∈ z, isEntP y = false := fun z hz =>
    (PB_split (fun _ => false) (fun _ _ => rfl) (Q ++ P)).2.2.1 z hz
  have hmem : ((Q ++ P).splitOnP isEntP).getD t [] ∈ (Q ++ P).splitOnP isEntP := by
    have ht' := Finset.mem_range.1 ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
    exact List.getElem_mem ht'
  have ht' := Finset.mem_range.1 ht
  rw [FF_len] at ht'
  have hL : (if t = 0 then κ y else κ ((FF_ents (Q ++ P)).getD (t - 1) (0, 0)).2) =
      κ (((x, y) :: FF_ents (Q ++ P)).getD t (0, 0)).2 := by
    rcases t with _ | t <;> simp
  have hR : (if t < (FF_ents (Q ++ P)).length then κ ((FF_ents (Q ++ P)).getD t (0, 0)).1
      else κ x) = κ (((x, y) :: FF_ents (Q ++ P)).getD
        ((t + 1) % ((x, y) :: FF_ents (Q ++ P)).length) (0, 0)).1 := by
    simp only [List.length_cons]
    by_cases htl : t < (FF_ents (Q ++ P)).length
    · simp only [htl, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp
    · have : t = (FF_ents (Q ++ P)).length := by omega
      subst this
      simp
  rw [FFac.val, FF_free e pr hz h hh ι κ _ (hfree _ hmem), hL, hR]

/-- The value of one word of an expression of the class `𝓡`: the trace of a word with `Δ` is the
product of its package entries, a word without `Δ` is a loop. -/
private lemma FF_word {D N : ℕ} (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    {nb : ℕ} (ι : Fin nb → Fin D) (κ : ℕ → Idx D N) (w : List PkgLetter) :
    (if w.any PkgLetter.isEnt
      then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w).trace
      else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w)) =
      ((FF_wf e.s pr w).map (FFac.val e ι κ h)).prod := by
  by_cases hw : w.any isEntP = true
  · have hw2 : w.any PkgLetter.isEnt = true := hw
    obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent w hw
    simp only [hw2, ↓reduceIte]
    exact FF_wf_ent e pr hz h hh ι κ P Q x y hP
  · have hf : ∀ y ∈ w, isEntP y = false := by simpa using hw
    have h0 : w.any isEntP = false := by simpa using hw
    have hw' : w.any PkgLetter.isEnt = false := h0
    simp only [hw', Bool.false_eq_true, ↓reduceIte, FF_wf]
    simp [FFac.val, FF_free e pr hz h hh ι κ w hf]

private lemma FF_flatMap_prod {α β : Type*} (F : α → List β) (g : β → ℂ) :
    ∀ L : List α, (((L.flatMap F).map g).prod) = (L.map fun w => ((F w).map g).prod).prod
  | [] => by simp
  | a :: L => by simp [List.flatMap_cons, FF_flatMap_prod F g L]

/-- (N0), the factorization behind (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]
and every display of the remainders in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
at a Hermitian array the value of an expression of the class `𝓡` is its coefficient times the
sum over the block indices of the product of its factors (the trace of a word with `Δ` is the
product of its package entries). -/
theorem pkg_evalP_ffacs {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (hz : ∀ a, 0 < (e.z a).im) (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    R.evalP e pr κ h = (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) *
      ∑ ι : Fin R.nb → Fin D, ((R.ffacs e.s pr).map (FFac.val e ι κ h)).prod := by
  unfold PkgExpr.evalP
  rw [FF_ffacs]
  congr 1
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [List.map_append, List.prod_append, FF_flatMap_prod]
  congr 1
  · simp [FFac.val, List.map_map, Function.comp_def]
  · exact congrArg List.prod (List.map_congr_left fun w _ => FF_word e pr hz h hh ι κ w)

end RBMTransitionEdge

end
