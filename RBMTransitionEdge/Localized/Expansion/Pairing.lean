module

public import RBMTransitionEdge.Localized.Expansion.Counts
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.PkgShape

@[expose] public section

/-!
# The pairing inside the derivative structures of the further expansion

The pairing (P) of (5.58) [eq:polar2] with Definition 2.7 [defn_Mm] on one deterministic letter
inside the derivative structures of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression],
and the bound (A.3) [equation_z_im_m] on the paired letter at the slots of Lemmas 5.2 and 5.4.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The deterministic letters of the pairing (P) of (5.58) [eq:polar2]: `𝔐_a - 𝔐_a^*` at the
slots `a` with `pr a`, and `𝔐_a` at the others. -/
def LoopEnv.pairM {D N : ℕ} (e : LoopEnv D N) (pr : Fin 2 → Bool) (a : Fin 2) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  if pr a then e.M a - (e.M a)ᴴ else e.M a

/-- The value of an expression of the class `𝓡` of (5.79)–(5.81) with the deterministic letters
of `LoopEnv.pairM` in its words. -/
def PkgExpr.evalP {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) * ∑ ι : Fin R.nb → Fin D,
    (R.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
    (R.loops.map fun w => if w.any PkgLetter.isEnt
      then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w).trace
      else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w)).prod

/-- Slot `a'` enters the expression only through one deterministic letter `𝔐_{a'}`: no resolvent
and no light weight of slot `a'`. -/
def PkgExpr.onlyDet (R : PkgExpr) (a' : Fin 2) : Bool :=
  R.weights.all (fun p => p.1 != a') &&
  R.loops.all (fun w => !(w.contains (.lw (.res a')))) &&
  (R.loops.map fun w => w.count (.lw (.det a'))).sum == 1

/-! ### The value with given deterministic letters -/

/-- The value of an expression of the class `𝓡` with the deterministic letters `Mf` in its words
and the letters `𝔐_a` of `e` in its light weights. -/
private def Pr_val {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (Mf : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) * ∑ ι : Fin R.nb → Fin D,
    (R.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
    (R.loops.map fun w => if w.any PkgLetter.isEnt
      then (pkgWordMat (e.G h) Mf (e.E ι) e.Lt κ w).trace
      else ntr (pkgWordMat (e.G h) Mf (e.E ι) e.Lt κ w)).prod

private lemma Pr_evalH {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) : R.evalH e κ h = Pr_val R e κ h e.M := rfl

private lemma Pr_evalP {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) :
    R.evalP e pr κ h = Pr_val R e κ h (e.pairM pr) := rfl

/-! ### Words: dependence on the letters that occur -/

section Words

variable {D N : ℕ} (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
  (κ : ℕ → Idx D N)

private lemma Pr_wm_cons (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (x : PkgLetter)
    (w : List PkgLetter) :
    pkgWordMat G M E L κ (x :: w) = pkgWordMat G M E L κ [x] * pkgWordMat G M E L κ w := by
  simp [pkgWordMat]

/-- The matrix of a word depends only on the letters `𝒢_c`, `𝔐_c` that occur in it. -/
private lemma Pr_wm_congr (G G' M M' : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (w : List PkgLetter) (hG : ∀ c, PkgLetter.lw (.res c) ∈ w → G c = G' c)
    (hM : ∀ c, PkgLetter.lw (.det c) ∈ w → M c = M' c) :
    pkgWordMat G M E L κ w = pkgWordMat G' M' E L κ w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [Pr_wm_cons, Pr_wm_cons _ _ _ G' M']
    congr 1
    · rcases x with ((a | a | y | o) | ⟨u, v⟩)
      · simp [pkgWordMat, loopWordMat, hG a (by simp)]
      · simp [pkgWordMat, loopWordMat, hM a (by simp)]
      · rfl
      · rfl
      · rfl
    · exact ih (fun c hc => hG c (by simp [hc])) (fun c hc => hM c (by simp [hc]))

/-- A word with no letter `𝔐_{a'}` does not depend on it. -/
private lemma Pr_wm_free (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (a' : Fin 2)
    (X Y : Matrix (Idx D N) (Idx D N) ℂ) (w : List PkgLetter)
    (hw : w.count (.lw (.det a')) = 0) :
    pkgWordMat G (Function.update M a' X) E L κ w =
      pkgWordMat G (Function.update M a' Y) E L κ w := by
  refine Pr_wm_congr E L κ _ _ _ _ w (fun _ _ => rfl) fun c hc => ?_
  have hne : c ≠ a' := by
    rintro rfl
    exact (List.count_eq_zero.1 hw) hc
  simp [Function.update_of_ne hne]

/-- A word with exactly one letter `𝔐_{a'}` is additive in it. -/
private lemma Pr_wm_add (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (a' : Fin 2)
    (X Y : Matrix (Idx D N) (Idx D N) ℂ) (w : List PkgLetter)
    (hw : w.count (.lw (.det a')) = 1) :
    pkgWordMat G (Function.update M a' (X + Y)) E L κ w =
      pkgWordMat G (Function.update M a' X) E L κ w +
        pkgWordMat G (Function.update M a' Y) E L κ w := by
  induction w with
  | nil => simp at hw
  | cons x w ih =>
    rw [Pr_wm_cons, Pr_wm_cons _ _ _ _ (Function.update M a' X),
      Pr_wm_cons _ _ _ _ (Function.update M a' Y)]
    rw [List.count_cons] at hw
    by_cases hx : x = .lw (.det a')
    · subst hx
      simp only [beq_self_eq_true, ↓reduceIte] at hw
      have h0 : w.count (.lw (.det a')) = 0 := by omega
      rw [Pr_wm_free E L κ G M a' (X + Y) X w h0, Pr_wm_free E L κ G M a' Y X w h0]
      simp [pkgWordMat, loopWordMat, add_mul]
    · have hb : (x == PkgLetter.lw (.det a')) = false := by simpa using hx
      simp only [hb, Bool.false_eq_true, ↓reduceIte, add_zero] at hw
      rw [ih hw, mul_add]
      have h1 := Pr_wm_free E L κ G M a' (X + Y) X [x] (by simp [hx])
      have h2 := Pr_wm_free E L κ G M a' Y X [x] (by simp [hx])
      rw [h1, h2]

end Words

private lemma Pr_ntr_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A + B) = ntr A + ntr B := by
  simp [ntr, Matrix.trace_add, mul_add]

/-- The factor of a word, as a function of the letter `𝔐_{a'}`. -/
private def Pr_wf {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X : Matrix (Idx D N) (Idx D N) ℂ)
    (w : List PkgLetter) : ℂ :=
  if w.any PkgLetter.isEnt
  then (pkgWordMat (e.G h) (Function.update e.M a' X) (e.E ι) e.Lt κ w).trace
  else ntr (pkgWordMat (e.G h) (Function.update e.M a' X) (e.E ι) e.Lt κ w)

private lemma Pr_wf_free {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ)
    (w : List PkgLetter) (hw : w.count (.lw (.det a')) = 0) :
    Pr_wf e ι κ h a' X w = Pr_wf e ι κ h a' Y w := by
  unfold Pr_wf
  rw [Pr_wm_free _ _ _ _ _ a' X Y w hw]

private lemma Pr_prod_free {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ ls : List (List PkgLetter), (ls.map fun w => w.count (.lw (.det a'))).sum = 0 →
      (ls.map (Pr_wf e ι κ h a' X)).prod = (ls.map (Pr_wf e ι κ h a' Y)).prod
  | [], _ => by simp only [List.map_nil]
  | w :: ls, hls => by
    rw [List.map_cons, List.sum_cons] at hls
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      Pr_wf_free e ι κ h a' X Y w (by omega), Pr_prod_free e ι κ h a' X Y ls (by omega)]

private lemma Pr_wf_add {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ)
    (w : List PkgLetter) (hw : w.count (.lw (.det a')) = 1) :
    Pr_wf e ι κ h a' (X + Y) w = Pr_wf e ι κ h a' X w + Pr_wf e ι κ h a' Y w := by
  unfold Pr_wf
  rw [Pr_wm_add _ _ _ _ _ a' X Y w hw]
  split_ifs
  · rw [Matrix.trace_add]
  · rw [Pr_ntr_add]

/-- The product of the loops is additive in `𝔐_{a'}` when it occurs exactly once. -/
private lemma Pr_prod_add {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ ls : List (List PkgLetter), (ls.map fun w => w.count (.lw (.det a'))).sum = 1 →
    (ls.map (Pr_wf e ι κ h a' (X + Y))).prod =
      (ls.map (Pr_wf e ι κ h a' X)).prod + (ls.map (Pr_wf e ι κ h a' Y)).prod
  | [], hl => by simp at hl
  | w :: ls, hl => by
    rw [List.map_cons, List.sum_cons] at hl
    simp only [List.map_cons, List.prod_cons]
    rcases Nat.eq_zero_or_pos (w.count (.lw (.det a'))) with hw | hw
    · rw [Pr_prod_add e ι κ h a' X Y ls (by omega), Pr_wf_free e ι κ h a' (X + Y) X w hw,
        Pr_wf_free e ι κ h a' Y X w hw, mul_add]
    · have hls : (ls.map fun w => w.count (.lw (.det a'))).sum = 0 := by omega
      rw [Pr_prod_free e ι κ h a' (X + Y) X ls hls, Pr_prod_free e ι κ h a' Y X ls hls,
        ← add_mul, Pr_wf_add e ι κ h a' X Y w (by omega)]

/-- The value is additive in the letter `𝔐_{a'}` of the words when it occurs exactly once. -/
private lemma Pr_val_add {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ)
    (hl : (R.loops.map fun w => w.count (.lw (.det a'))).sum = 1) :
    Pr_val R e κ h (Function.update e.M a' (X + Y)) =
      Pr_val R e κ h (Function.update e.M a' X) + Pr_val R e κ h (Function.update e.M a' Y) := by
  unfold Pr_val
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [← mul_add]
  congr 1
  exact Pr_prod_add e ι κ h a' X Y R.loops hl

/-- The value is linear in the letter `𝔐_{a'}`: the difference of two values is the value at the
difference. -/
private lemma Pr_val_sub {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ)
    (hl : (R.loops.map fun w => w.count (.lw (.det a'))).sum = 1) :
    Pr_val R e κ h (Function.update e.M a' X) - Pr_val R e κ h (Function.update e.M a' Y) =
      Pr_val R e κ h (Function.update e.M a' (X - Y)) := by
  have := Pr_val_add R e κ h a' (X - Y) Y hl
  rw [sub_add_cancel] at this
  rw [this]
  ring

/-- Two values agree when their light weights and the matrices of their words agree. -/
private lemma Pr_val_congr {D N : ℕ} (R : PkgExpr) (e e' : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (Mf Mf' : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (hw : ∀ (ι : Fin R.nb → Fin D), ∀ p ∈ R.weights,
      ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2) = ntr ((e'.G h p.1 - e'.M p.1) * e'.E ι p.2))
    (hl : ∀ (ι : Fin R.nb → Fin D), ∀ w ∈ R.loops,
      pkgWordMat (e.G h) Mf (e.E ι) e.Lt κ w = pkgWordMat (e'.G h) Mf' (e'.E ι) e'.Lt κ w) :
    Pr_val R e κ h Mf = Pr_val R e' κ h Mf' := by
  unfold Pr_val
  have hs : ∀ ι : Fin R.nb → Fin D,
      (R.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
        (R.loops.map fun w => if w.any PkgLetter.isEnt
          then (pkgWordMat (e.G h) Mf (e.E ι) e.Lt κ w).trace
          else ntr (pkgWordMat (e.G h) Mf (e.E ι) e.Lt κ w)).prod =
      (R.weights.map fun p => ntr ((e'.G h p.1 - e'.M p.1) * e'.E ι p.2)).prod *
        (R.loops.map fun w => if w.any PkgLetter.isEnt
          then (pkgWordMat (e'.G h) Mf' (e'.E ι) e'.Lt κ w).trace
          else ntr (pkgWordMat (e'.G h) Mf' (e'.E ι) e'.Lt κ w)).prod := by
    intro ι
    rw [List.map_congr_left (hw ι), List.map_congr_left (l := R.loops) fun w hwl => by
      rw [hl ι w hwl]]
  rw [Finset.sum_congr rfl fun ι _ => hs ι]

/-- `PkgExpr.onlyDet` as a proposition. -/
private lemma Pr_onlyDet_iff (R : PkgExpr) (a' : Fin 2) :
    R.onlyDet a' = true ↔ ((∀ p ∈ R.weights, p.1 ≠ a') ∧
      (∀ w ∈ R.loops, PkgLetter.lw (.res a') ∉ w)) ∧
      (R.loops.map fun w => w.count (.lw (.det a'))).sum = 1 := by
  simp only [PkgExpr.onlyDet, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, beq_iff_eq]

/-- With no paired slot, `evalP` is the value `evalH` of the expression. -/
theorem pkg_evalP_false {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) : R.evalP e (fun _ => false) κ h = R.evalH e κ h := by
  have hM : e.pairM (fun _ => false) = e.M := by
    funext a
    simp [LoopEnv.pairM]
  rw [Pr_evalP, Pr_evalH, hM]

/-- The pairing (P) of (5.58) [eq:polar2] with Definition 2.7 [defn_Mm]: if slot `a'` enters
only through one letter `𝔐_{a'}`, the signed sum over its flag replaces that letter by
`𝔐_{a'} - 𝔐_{a'}^*`. -/
theorem pkg_pair_ident {D N : ℕ} (R : PkgExpr) (a' : Fin 2) (hR : R.onlyDet a' = true)
    (e : LoopEnv D N) (he : (e.z a').im ≠ 0) (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) :
    ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
        R.evalH { e with s := Function.update e.s a' b } κ h =
      R.evalP { e with s := Function.update e.s a' false } (fun a => decide (a = a')) κ h := by
  obtain ⟨⟨hw, hG⟩, hc⟩ := (Pr_onlyDet_iff R a').1 hR
  set e₀ : LoopEnv D N := { e with s := Function.update e.s a' false } with he₀
  -- the value at the flag `b` of slot `a'` has the letter `𝔐_{a'}` of that flag in its words
  have hflag : ∀ b : Bool, R.evalH { e with s := Function.update e.s a' b } κ h =
      Pr_val R e₀ κ h (Function.update e₀.M a'
        (({ e with s := Function.update e.s a' b } : LoopEnv D N).M a')) := by
    intro b
    have hGc : ∀ c, c ≠ a' → ({ e with s := Function.update e.s a' b } : LoopEnv D N).G h c =
        e₀.G h c := by
      intro c hc'
      simp [LoopEnv.G, he₀, Function.update_of_ne hc']
    have hMc : ∀ c, c ≠ a' → ({ e with s := Function.update e.s a' b } : LoopEnv D N).M c =
        e₀.M c := by
      intro c hc'
      simp [LoopEnv.M, he₀, Function.update_of_ne hc']
    rw [Pr_evalH]
    refine Pr_val_congr R _ _ κ h _ _ (fun ι p hp => ?_) (fun ι w hwl => ?_)
    · rw [hGc p.1 (hw p hp), hMc p.1 (hw p hp)]
      rfl
    · refine Pr_wm_congr _ _ _ _ _ _ _ w (fun c hcw => ?_) (fun c _ => ?_)
      · have hca : c ≠ a' := by
          rintro rfl
          exact (hG w hwl) hcw
        exact hGc c hca
      · by_cases hca : c = a'
        · subst hca
          simp
        · rw [Function.update_of_ne hca]
          exact hMc c hca
  -- the paired letters
  have hpair : e₀.pairM (fun a => decide (a = a')) =
      Function.update e₀.M a' (e₀.M a' - (e₀.M a')ᴴ) := by
    funext c
    by_cases hca : c = a'
    · subst hca
      simp [LoopEnv.pairM]
    · simp [LoopEnv.pairM, hca]
  -- the letter at the flag `true` is the adjoint of the letter at the flag `false`
  have hconj : ({ e with s := Function.update e.s a' true } : LoopEnv D N).M a' =
      (e₀.M a')ᴴ := by
    rcases isEmpty_or_nonempty (Idx D N) with hE | hE
    · ext i
      exact isEmptyElim i
    · have hherm : ((e.c a' : ℂ) • lam D N e.A).IsHermitian := by
        have := lam_isHermitian D N e.A
        unfold Matrix.IsHermitian at this ⊢
        rw [Matrix.conjTranspose_smul, this]
        simp
      have := (mExt_conj _ hherm (e.z a') he).2
      simpa [LoopEnv.M, he₀] using this
  have hfalse : ({ e with s := Function.update e.s a' false } : LoopEnv D N).M a' = e₀.M a' := rfl
  rw [Fintype.sum_bool, hflag true, hflag false, hconj, hfalse, Pr_evalP, hpair]
  simp only [ite_true, Bool.false_eq_true, ite_false, neg_one_mul, one_mul]
  rw [← sub_eq_neg_add, Pr_val_sub R e₀ κ h a' _ _ hc]

/-! ### The bound (A.3) on one slot -/

section Norms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma Pr_opNorm_conjTranspose (X : Matrix ι ι ℂ) : opNorm Xᴴ = opNorm X := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) X)

private lemma Pr_opNorm_neg (X : Matrix ι ι ℂ) : opNorm (-X) = opNorm X := by
  unfold opNorm
  rw [map_neg, norm_neg]

private lemma Pr_opNorm_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `⟨M M^*⟩ ≥ ‖X‖⁻²` for `X M = 1`: every row of `M` has norm at least `‖X‖⁻¹`. -/
private lemma Pr_ntr_lower [Nonempty ι] (X M : Matrix ι ι ℂ) (hXM : X * M = 1) (B : ℝ)
    (hB : opNorm X ≤ B) : 1 ≤ B ^ 2 * (ntr (M * Mᴴ)).re := by
  have hMX : M * X = 1 := mul_eq_one_comm.1 hXM
  have hH : Xᴴ * Mᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hMX, Matrix.conjTranspose_one]
  have hcol : ∀ i, 1 ≤ B ^ 2 * ∑ j, ‖M i j‖ ^ 2 := by
    intro i
    set v := Matrix.toEuclideanCLM (𝕜 := ℂ) Mᴴ (EuclideanSpace.single i (1 : ℂ)) with hv
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) Xᴴ v = EuclideanSpace.single i (1 : ℂ) := by
      change (Matrix.toEuclideanCLM (𝕜 := ℂ) Xᴴ * Matrix.toEuclideanCLM (𝕜 := ℂ) Mᴴ)
        (EuclideanSpace.single i (1 : ℂ)) = _
      rw [← map_mul, hH, map_one]
      rfl
    have h2 : (1 : ℝ) ≤ opNorm Xᴴ * ‖v‖ := by
      have := (Matrix.toEuclideanCLM (𝕜 := ℂ) Xᴴ).le_opNorm v
      rw [h1] at this
      simpa [opNorm] using this
    have h3 : ‖v‖ ^ 2 = ∑ j, ‖M i j‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : v j = Mᴴ j i := by simp [hv, Matrix.mulVec_single]
      rw [this, Matrix.conjTranspose_apply, norm_star]
    rw [Pr_opNorm_conjTranspose] at h2
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    have hX0 : 0 ≤ opNorm X := norm_nonneg _
    rw [← h3]
    nlinarith [mul_le_mul_of_nonneg_right hB hv0]
  have htr : (ntr (M * Mᴴ)).re = (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
    unfold ntr Matrix.trace
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have e1 : ∀ i j, M i j * star (M i j) = ((‖M i j‖ ^ 2 : ℝ) : ℂ) := fun i j => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e1]
    have e2 : ((Fintype.card ι : ℂ))⁻¹ * ∑ i, ∑ j, ((‖M i j‖ ^ 2 : ℝ) : ℂ) =
        (((Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e2, Complex.ofReal_re]
  have hsum : (Fintype.card ι : ℝ) ≤ B ^ 2 * ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hcol i
    simpa using this
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [htr, show B ^ 2 * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, ‖M i j‖ ^ 2) =
    (Fintype.card ι : ℝ)⁻¹ * (B ^ 2 * ∑ i, ∑ j, ‖M i j‖ ^ 2) by ring, le_inv_mul_iff₀ hc,
    mul_one]
  exact hsum

/-- (A.3) [equation_z_im_m] with `‖M‖ ≤ 5/4` and `η ≤ (R + 2)² Im m` for `|z| ≤ R`:
`‖M - M^*‖ ≤ (25/8) (R + 2)² Im m`. -/
private lemma Pr_gen [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (R : ℝ) (hzR : ‖z‖ ≤ R) :
    opNorm (MSol Λ z - (MSol Λ z)ᴴ) ≤ 25 / 8 * (R + 2) ^ 2 * (mSol Λ z).im := by
  obtain ⟨hm, -, hinv⟩ := mSol_spec Λ hΛ z hz
  obtain ⟨-, hm1, hM⟩ := mSol_apriori Λ hΛ hℓ z hz
  obtain ⟨hA3, hid⟩ := equation_z_im_m Λ hΛ z hz
  have hΛ0 : 0 ≤ opNorm Λ := norm_nonneg _
  have hX : opNorm (Λ - (z + mSol Λ z) • (1 : Matrix ι ι ℂ)) ≤ R + 2 := by
    have h1 : opNorm (Λ - (z + mSol Λ z) • (1 : Matrix ι ι ℂ)) ≤
        opNorm Λ + ‖z + mSol Λ z‖ * opNorm (1 : Matrix ι ι ℂ) := by
      rw [sub_eq_add_neg, ← neg_smul]
      refine (opNorm_add_le _ _).trans ?_
      rw [opNorm_smul, norm_neg]
    have h2 : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := Pr_opNorm_one
    have h20 : 0 ≤ opNorm (1 : Matrix ι ι ℂ) := norm_nonneg _
    have h3 : ‖z + mSol Λ z‖ ≤ R + 1 := (norm_add_le _ _).trans (by linarith)
    nlinarith [norm_nonneg (z + mSol Λ z)]
  have hlow := Pr_ntr_lower _ (MSol Λ z) hinv (R + 2) hX
  rw [hA3, Complex.ofReal_re] at hlow
  have hden : 0 < (mSol Λ z).im + z.im := by linarith
  have hkey : (mSol Λ z).im + z.im ≤ (R + 2) ^ 2 * (mSol Λ z).im := by
    rw [← mul_div_assoc, le_div_iff₀ hden, one_mul] at hlow
    exact hlow
  rw [hid, opNorm_smul]
  have hn : ‖2 * Complex.I * ((z.im + (mSol Λ z).im : ℝ) : ℂ)‖ = 2 * (z.im + (mSol Λ z).im) := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    norm_num
  rw [hn]
  have hM' : opNorm (MSol Λ z) ≤ 5 / 4 := by
    have h2 : (1 - 2 * opNorm Λ)⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hMM : opNorm (MSol Λ z * (MSol Λ z)ᴴ) ≤ 25 / 16 := by
    refine (opNorm_mul_le _ _).trans ?_
    rw [Pr_opNorm_conjTranspose]
    have : 0 ≤ opNorm (MSol Λ z) := norm_nonneg _
    nlinarith
  calc 2 * (z.im + (mSol Λ z).im) * opNorm (MSol Λ z * (MSol Λ z)ᴴ)
      ≤ 2 * (z.im + (mSol Λ z).im) * (25 / 16) :=
        mul_le_mul_of_nonneg_left hMM (by linarith)
    _ ≤ 25 / 8 * (R + 2) ^ 2 * (mSol Λ z).im := by nlinarith

end Norms

/-- `m(0, z) = m_sc(z)` on `Idx D N` for `Im z > 0`, from (A.5) [eq:msc] at `Λ = 0`. -/
private lemma Pr_msc_zero {D N : ℕ} [Nonempty (Idx D N)] (z : ℂ) (hz : 0 < z.im) :
    mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z = msc z := by
  obtain ⟨C, -, hCs⟩ := eq_msc_traceless (‖z‖ + 1)⁻¹ (by positivity)
  have h := hCs (Idx D N) 0 Matrix.isHermitian_zero (by simp [opNorm]) (by simp [ntr]) z
    (by rw [inv_inv]; linarith) hz
  have h0 : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by simp [opNorm]
  rw [h0, mul_zero] at h
  have h2 : 0 ≤ opNorm (MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z -
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := norm_nonneg _
  have h1 : ‖mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z - msc z‖ = 0 :=
    le_antisymm (by linarith) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 h1)

/-- (A.3) [equation_z_im_m] at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law]
and 5.4 [lemma_localized_eigenvalue_local_law]: `‖𝔐_a - 𝔐_a^*‖ ≤ K Im m`, with `Im m` of slot `1`,
every flag. -/
theorem pkg_pair_norm (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ a : Fin 2, opNorm (e.M a - (e.M a)ᴴ) ≤
        K * (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im := by
  obtain ⟨c₀, K₀, -, -, N₁, hN₁⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨C₁, hC₁, N₂, hN₂⟩ := regular_estimate_localized_eigenvector D hD δA εA ε hδA hεA hε hε'
  refine ⟨25 / 8 * (2 / ε + 2) ^ 2 * max 1 C₁, by positivity, max (max N₁ N₂) 1, ?_⟩
  intro N hN A hA k hk hkN hhs e he a
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hDN : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hN1)
  have hkDN : k ≤ D * N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨hA2, hc, hz, -⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    A hA k hk hkN hhs e he
  have hherm : ∀ b : Fin 2, ((e.c b : ℂ) • lam D N e.A).IsHermitian := fun b => by
    have := lam_isHermitian D N e.A
    unfold Matrix.IsHermitian at this ⊢
    rw [Matrix.conjTranspose_smul, this]
    simp
  have hℓ : opNorm ((e.c a : ℂ) • lam D N e.A) ≤ 1 / 10 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := opNorm_lam_le D N e.A
    have h2 := hc a
    have h3 : 0 ≤ opNorm (lam D N e.A) := norm_nonneg _
    nlinarith [abs_nonneg (e.c a)]
  obtain ⟨hzd, hzpos, -, -⟩ := hz a
  have hzR : ‖e.z a‖ ≤ 2 / ε := by
    have := hzd.1
    rwa [inv_div] at this
  have hgen := Pr_gen _ (hherm a) hℓ (e.z a) hzpos (2 / ε) hzR
  have hflag : opNorm (e.M a - (e.M a)ᴴ) = opNorm (MSol ((e.c a : ℂ) • lam D N e.A) (e.z a) -
      (MSol ((e.c a : ℂ) • lam D N e.A) (e.z a))ᴴ) := by
    have hext : MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) =
        MSol ((e.c a : ℂ) • lam D N e.A) (e.z a) := by
      have hm : mExt ((e.c a : ℂ) • lam D N e.A) (e.z a) =
          mSol ((e.c a : ℂ) • lam D N e.A) (e.z a) := by
        simp [mExt, hzpos]
      unfold MExt MSol
      rw [hm]
    unfold LoopEnv.M
    cases e.s a
    · simp only [Bool.false_eq_true, ite_false, hext]
    · simp only [↓reduceIte]
      rw [(mExt_conj _ (hherm a) _ hzpos.ne').2, hext,
        Matrix.conjTranspose_conjTranspose, ← neg_sub, Pr_opNorm_neg]
  rw [hflag]
  refine hgen.trans ?_
  have hm1 : 0 ≤ (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im :=
    (mSol_spec _ (hherm 1) _ (hz 1).2.1).1.le
  suffices hs : (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤
      max 1 C₁ * (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im by
    have := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 25 / 8 * (2 / ε + 2) ^ 2 by positivity)
    linarith
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have hone : (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im ≤
      max 1 C₁ * (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im :=
    le_mul_of_one_le_left hm1 (le_max_left _ _)
  rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
  · rcases ha with rfl | rfl
    · -- slot `0` of Lemma 5.2: `m(0, z₀) = m_sc(z₀)` and (5.3) [sim_m_sc_and_m]
      obtain ⟨hreg, -⟩ := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
        A hA k hk hkDN hhs
      have hz0 := (hz 0).2.1
      have hz1 := (hz 1).2.1
      simp only [evecEnv, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_zero,
        zero_smul, Complex.ofReal_one, one_smul] at hz0 hz1 ⊢
      rw [Pr_msc_zero _ hz0]
      have hext : mExt (lam D N A) (zOne (lam D N A) k ε) =
          mSol (lam D N A) (zOne (lam D N A) k ε) := by
        simp [mExt, hz1]
      rw [hext] at hreg
      have hC₁' : (msc (zOne (lam D N A) k ε - (shiftEv (lam D N A)
          (zOne (lam D N A) k ε) : ℂ))).im ≤ C₁ * (mSol (lam D N A) (zOne (lam D N A) k ε)).im := by
        rw [inv_mul_le_iff₀ hC₁] at hreg
        exact hreg
      exact hC₁'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        ((mSol_spec _ (lam_isHermitian D N A) _ hz1).1.le))
    · exact hone
  · rcases ha with rfl | rfl
    · exact hone
    · exact hone

end RBMTransitionEdge


end
