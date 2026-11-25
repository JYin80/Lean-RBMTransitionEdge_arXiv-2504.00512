module

public import RBMTransitionEdge.Localized.Expansion.PkgInv
public import RBMTransitionEdge.Localized.Expansion.FFactor
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.FFactor
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# The pairing through one resolvent

If slot `a'` enters an expression only through one resolvent `𝒢_{a'}`, the signed sum over its
flag turns it into `𝒢_{a'} - 𝒢_{a'}ᴴ = 2 i η 𝒢_{a'} 𝒢_{a'}ᴴ`: the pairing of companion case (8),
exceptional subcase, in the proof of Lemma 5.5 [claim_estimate_remainder_terms], with (5.29)
[expansion_of_im].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The letter `𝒢_{a'}` replaced by `𝒢_{a'} 𝒢_{a'}ᴴ`. -/
def FLet.dupRes (a' : Fin 2) : FLet → List FLet
  | .res a f => if a = a' then [.res a false, .res a true] else [.res a f]
  | x => [x]

/-- The factor with every `𝒢_{a'}` replaced by `𝒢_{a'} 𝒢_{a'}ᴴ`. -/
def FFac.dupRes (a' : Fin 2) : FFac → FFac
  | .ent x y w => .ent x y (w.flatMap (FLet.dupRes a'))
  | .loop w => .loop (w.flatMap (FLet.dupRes a'))
  | .wt a x => .wt a x


/-! ### Letters and factors with the resolvent of slot `a'` set to a given matrix -/

open private FF_pk FF_wf FF_ffacs FF_herm FF_ents FF_len from RBMTransitionEdge.Localized.Expansion.FFactor
open private PB_segs_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private isEntP exists_first_ent findIdx_ent from RBMTransitionEdge.Localized.Expansion.PkgWords
open private PB_segs_ent from RBMTransitionEdge.Localized.Expansion.PkgBound

/-- The letter is a resolvent of slot `a'`, with either flag. -/
private def PG_isR (a' : Fin 2) : FLet → Bool
  | .res a _ => decide (a = a')
  | _ => false

/-- The letter is `𝔐_{a'}`, paired or not. -/
private def PG_isD (a' : Fin 2) : FLet → Bool
  | .det a _ => decide (a = a')
  | _ => false

/-- The number of resolvents of slot `a'` in a factor. -/
private def PG_cR (a' : Fin 2) : FFac → ℕ
  | .ent _ _ w => w.countP (PG_isR a')
  | .loop w => w.countP (PG_isR a')
  | .wt _ _ => 0

/-- The number of letters `𝔐_{a'}` in a factor, and `1` for a light weight of slot `a'`. -/
private def PG_bad (a' : Fin 2) : FFac → ℕ
  | .ent _ _ w => w.countP (PG_isD a')
  | .loop w => w.countP (PG_isD a')
  | .wt a _ => if a = a' then 1 else 0

/-- The letter with the resolvent of slot `a'` given the flag `b`. -/
private def PG_setF (a' : Fin 2) (b : Bool) (l : FLet) : FLet :=
  if PG_isR a' l then .res a' b else l

/-- A map on the letters of a factor. -/
private def PG_mapL (g : FLet → FLet) : FFac → FFac
  | .ent x y w => .ent x y (w.map g)
  | .loop w => .loop (w.map g)
  | .wt a x => .wt a x

/-- The matrix of a letter, with `X` in place of every resolvent of slot `a'`. -/
private def PG_mX {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X : Matrix (Idx D N) (Idx D N) ℂ) (l : FLet) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  if PG_isR a' l then X else FLet.mat e ι h l

/-- The value of a factor, with `X` in place of every resolvent of slot `a'`. -/
private def PG_valX {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2)
    (X : Matrix (Idx D N) (Idx D N) ℂ) : FFac → ℂ
  | .ent x y w => (w.map (PG_mX e ι h a' X)).prod (κ x) (κ y)
  | .loop w => ntr (w.map (PG_mX e ι h a' X)).prod
  | .wt a x => FFac.val e ι κ h (.wt a x)

/-! ### The factor list at another flag of slot `a'` -/

private lemma PG_flet (s pr : Fin 2 → Bool) (a' : Fin 2) (b : Bool) (w : List PkgLetter) :
    w.filterMap (PkgLetter.flet (Function.update s a' b) pr) =
      (w.filterMap (PkgLetter.flet s pr)).map (PG_setF a' b) := by
  rw [List.map_filterMap]
  refine List.filterMap_congr fun x _ => ?_
  rcases x with ((a | a | y | o) | ⟨u, v⟩)
  · by_cases ha : a = a'
    · subst ha
      simp [PkgLetter.flet, PG_setF, PG_isR]
    · simp [PkgLetter.flet, PG_setF, PG_isR, ha]
  all_goals simp [PkgLetter.flet, PG_setF, PG_isR]

private lemma PG_range_getD {α β : Type*} (S : List α) (d : α) (g : α → β) :
    (List.range S.length).map (fun t => g (S.getD t d)) = S.map g := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-- The entries of the packages of a word, as a map over the pieces. -/
private lemma PG_pk (s pr : Fin 2 → Bool) (S : List (List PkgLetter)) (E : List (ℕ × ℕ))
    (hlen : S.length = E.length) :
    FF_pk s pr S E = (List.range S.length).map fun t =>
      FFac.ent (E.getD t (0, 0)).2 (E.getD ((t + 1) % E.length) (0, 0)).1
        ((S.getD t []).filterMap (PkgLetter.flet s pr)) := by
  unfold FF_pk
  rw [← List.filterMap_eq_map]
  refine List.filterMap_congr fun t ht => ?_
  have ht' : t < S.length := List.mem_range.1 ht
  have h1 : t < E.length := hlen ▸ ht'
  have h2 : (t + 1) % E.length < E.length := Nat.mod_lt _ (by omega)
  simp [List.getElem?_eq_getElem ht', List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    List.getD_eq_getElem?_getD]

/-- The labels `(u, v)` of the letters `Δ_{uv}` of a word, from its first `Δ`, as in
`PkgExpr.ffacs`. -/
private def PG_E (w : List PkgLetter) : List (ℕ × ℕ) :=
  (w.rotate (w.findIdx PkgLetter.isEnt)).filterMap fun z => match z with
    | .ent u v => some (u, v)
    | _ => none

/-- A word with a letter `Δ` has as many pieces as letters `Δ`. -/
private lemma PG_len (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) :
    (pkgSegs w).length = (PG_E w).length := by
  obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent w hw
  have hrot : (P ++ .ent x y :: Q).rotate ((P ++ .ent x y :: Q).findIdx PkgLetter.isEnt) =
      .ent x y :: (Q ++ P) := by
    rw [show (P ++ .ent x y :: Q).findIdx PkgLetter.isEnt = P.length from findIdx_ent P Q x y hP]
    exact List.rotate_append_length_eq P (.ent x y :: Q)
  have hS : pkgSegs (P ++ .ent x y :: Q) = (Q ++ P).splitOnP isEntP := PB_segs_ent P Q x y hP
  have hE : PG_E (P ++ .ent x y :: Q) = (x, y) :: FF_ents (Q ++ P) := by
    unfold PG_E
    rw [hrot]
    rfl
  rw [hE, hS, FF_len]
  rfl

private lemma PG_wf (s pr : Fin 2 → Bool) (a' : Fin 2) (b : Bool) (w : List PkgLetter) :
    FF_wf (Function.update s a' b) pr w = (FF_wf s pr w).map (PG_mapL (PG_setF a' b)) := by
  unfold FF_wf
  split_ifs with hw
  · change FF_pk _ pr (pkgSegs w) (PG_E w) = (FF_pk s pr (pkgSegs w) (PG_E w)).map _
    rw [PG_pk _ _ _ _ (PG_len w hw), PG_pk _ _ _ _ (PG_len w hw), List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp [PG_mapL, PG_flet]
  · simp [PG_mapL, PG_flet]

/-- The factor list at the flag `b` of slot `a'` is the factor list with that flag on its
resolvents of slot `a'`. -/
private lemma PG_ffacs (R : PkgExpr) (s pr : Fin 2 → Bool) (a' : Fin 2) (b : Bool) :
    R.ffacs (Function.update s a' b) pr = (R.ffacs s pr).map (PG_mapL (PG_setF a' b)) := by
  rw [FF_ffacs, FF_ffacs, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun w _ => PG_wf s pr a' b w

/-! ### Counts of letters along the factor list -/

private lemma PG_flatMap_sum {α β : Type*} (F : α → List β) (c : β → ℕ) :
    ∀ L : List α, ((L.flatMap F).map c).sum = (L.map fun w => ((F w).map c).sum).sum
  | [] => by simp
  | a :: L => by simp [List.flatMap_cons, PG_flatMap_sum F c L]

/-- The count of a kind of letter over the factors of one word is its count in the word. -/
private lemma PG_cnt (s pr : Fin 2 → Bool) (p : FLet → Bool) (c : FFac → ℕ)
    (hent : ∀ x y w, c (.ent x y w) = w.countP p) (hloop : ∀ w, c (.loop w) = w.countP p)
    (w : List PkgLetter) :
    ((FF_wf s pr w).map c).sum =
      w.countP fun x => ((PkgLetter.flet s pr x).map p).getD false := by
  unfold FF_wf
  split_ifs with hw
  · change ((FF_pk s pr (pkgSegs w) (PG_E w)).map c).sum = _
    rw [PG_pk _ _ _ _ (PG_len w hw), List.map_map]
    calc _ = ((List.range (pkgSegs w).length).map fun t => (fun σ : List PkgLetter =>
          σ.countP fun x => ((PkgLetter.flet s pr x).map p).getD false)
            ((pkgSegs w).getD t [])).sum := by
          congr 1
          refine List.map_congr_left fun t _ => ?_
          simp [hent, List.countP_filterMap]
      _ = _ := by
          rw [PG_range_getD]
          exact (PB_segs_count (fun x => ((PkgLetter.flet s pr x).map p).getD false)
            (fun x hx => by rcases x with _ | _ <;> simp_all [isEntP, PkgLetter.flet]) w).1
  · simp [hloop, List.countP_filterMap]

/-- The count of a kind of letter over the factor list. -/
private lemma PG_tot (R : PkgExpr) (s pr : Fin 2 → Bool) (p : FLet → Bool) (c : FFac → ℕ)
    (hent : ∀ x y w, c (.ent x y w) = w.countP p) (hloop : ∀ w, c (.loop w) = w.countP p) :
    ((R.ffacs s pr).map c).sum = (R.weights.map fun q => c (.wt q.1 q.2)).sum +
      (R.loops.map fun w => w.countP fun x =>
        ((PkgLetter.flet s pr x).map p).getD false).sum := by
  rw [FF_ffacs, List.map_append, List.sum_append, List.map_map, PG_flatMap_sum]
  congr 2
  exact List.map_congr_left fun w _ => PG_cnt s pr p c hent hloop w

private lemma PG_cnt_res (s pr : Fin 2 → Bool) (a' : Fin 2) (w : List PkgLetter) :
    (w.countP fun x => ((PkgLetter.flet s pr x).map (PG_isR a')).getD false) =
      w.count (.lw (.res a')) := by
  rw [List.count_eq_countP]
  refine List.countP_congr fun x _ => ?_
  rcases x with ((a | a | y | o) | ⟨u, v⟩) <;> simp [PkgLetter.flet, PG_isR]

private lemma PG_cnt_det (s pr : Fin 2 → Bool) (a' : Fin 2) (w : List PkgLetter) :
    (w.countP fun x => ((PkgLetter.flet s pr x).map (PG_isD a')).getD false) =
      w.count (.lw (.det a')) := by
  rw [List.count_eq_countP]
  refine List.countP_congr fun x _ => ?_
  rcases x with ((a | a | y | o) | ⟨u, v⟩) <;> simp [PkgLetter.flet, PG_isD]

/-- `PkgExpr.onlyRes` as a proposition. -/
private lemma PG_onlyRes_iff (R : PkgExpr) (a' : Fin 2) :
    R.onlyRes a' = true ↔ ((∀ p ∈ R.weights, p.1 ≠ a') ∧
      (∀ w ∈ R.loops, PkgLetter.lw (.det a') ∉ w)) ∧
      (R.loops.map fun w => w.count (.lw (.res a'))).sum = 1 := by
  simp only [PkgExpr.onlyRes, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, beq_iff_eq]

/-! ### The values at the flag `b` of slot `a'` -/

private lemma PG_mat_set {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (b : Bool) (l : FLet) (hl : PG_isD a' l = false) :
    FLet.mat { e with s := Function.update e.s a' b } ι h (PG_setF a' b l) =
      PG_mX e ι h a' (FLet.mat e ι h (.res a' b)) l := by
  rcases l with ⟨a, f⟩ | ⟨a, p⟩ | x | _
  · by_cases ha : a = a'
    · subst ha
      simp [PG_setF, PG_isR, PG_mX, FLet.mat]
    · simp [PG_setF, PG_isR, PG_mX, FLet.mat, ha]
  · have ha : a ≠ a' := by simpa [PG_isD] using hl
    simp [PG_setF, PG_isR, PG_mX, FLet.mat, LoopEnv.M, Function.update_of_ne ha]
  · simp [PG_setF, PG_isR, PG_mX, FLet.mat, LoopEnv.E]
  · simp [PG_setF, PG_isR, PG_mX, FLet.mat, LoopEnv.Lt]

private lemma PG_val_set {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (b : Bool) (f : FFac)
    (hf : PG_bad a' f = 0) :
    FFac.val { e with s := Function.update e.s a' b } ι κ h (PG_mapL (PG_setF a' b) f) =
      PG_valX e ι κ h a' (FLet.mat e ι h (.res a' b)) f := by
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
  · have hw : ∀ l ∈ w, PG_isD a' l = false := fun l hl => by
      simpa using List.countP_eq_zero.1 hf l hl
    have hm : w.map (FLet.mat { e with s := Function.update e.s a' b } ι h ∘ PG_setF a' b) =
        w.map (PG_mX e ι h a' (FLet.mat e ι h (.res a' b))) :=
      List.map_congr_left fun l hl => PG_mat_set e ι h a' b l (hw l hl)
    simp only [PG_mapL, FFac.val, PG_valX, List.map_map, hm]
  · have hw : ∀ l ∈ w, PG_isD a' l = false := fun l hl => by
      simpa using List.countP_eq_zero.1 hf l hl
    have hm : w.map (FLet.mat { e with s := Function.update e.s a' b } ι h ∘ PG_setF a' b) =
        w.map (PG_mX e ι h a' (FLet.mat e ι h (.res a' b))) :=
      List.map_congr_left fun l hl => PG_mat_set e ι h a' b l (hw l hl)
    simp only [PG_mapL, FFac.val, PG_valX, List.map_map, hm]
  · have ha : a ≠ a' := by
      intro ha
      simp [PG_bad, ha] at hf
    simp [PG_mapL, FFac.val, PG_valX, LoopEnv.G, LoopEnv.M, LoopEnv.E,
      Function.update_of_ne ha]

private lemma PG_prod_set {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (b : Bool) :
    ∀ L : List FFac, (L.map (PG_bad a')).sum = 0 →
      ((L.map (PG_mapL (PG_setF a' b))).map
        (FFac.val { e with s := Function.update e.s a' b } ι κ h)).prod =
      (L.map (PG_valX e ι κ h a' (FLet.mat e ι h (.res a' b)))).prod
  | [], _ => by simp
  | f :: L, hL => by
    rw [List.map_cons, List.sum_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    rw [PG_val_set e ι κ h a' b f (by omega), PG_prod_set e ι κ h a' b L (by omega)]

/-! ### Linearity in the resolvent of slot `a'` -/

private lemma PG_word0 {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ)
    (w : List FLet) (hw : w.countP (PG_isR a') = 0) :
    w.map (PG_mX e ι h a' X) = w.map (PG_mX e ι h a' Y) :=
  List.map_congr_left fun l hl => by
    have : PG_isR a' l = false := by simpa using List.countP_eq_zero.1 hw l hl
    simp [PG_mX, this]

/-- A word with one resolvent of slot `a'` is `P X Q` in it. -/
private lemma PG_word1 {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) :
    ∀ w : List FLet, w.countP (PG_isR a') = 1 →
      ∃ P Q : Matrix (Idx D N) (Idx D N) ℂ, ∀ X, (w.map (PG_mX e ι h a' X)).prod = P * X * Q
  | [], hw => by simp at hw
  | l :: w, hw => by
    rw [List.countP_cons] at hw
    by_cases hl : PG_isR a' l = true
    · simp only [hl, ↓reduceIte] at hw
      refine ⟨1, (w.map (PG_mX e ι h a' 0)).prod, fun X => ?_⟩
      rw [List.map_cons, List.prod_cons, PG_word0 e ι h a' X 0 w (by omega)]
      simp [PG_mX, hl]
    · have hl' : PG_isR a' l = false := by simpa using hl
      simp only [hl', Bool.false_eq_true, ↓reduceIte, add_zero] at hw
      obtain ⟨P, Q, hPQ⟩ := PG_word1 e ι h a' w hw
      refine ⟨FLet.mat e ι h l * P, Q, fun X => ?_⟩
      rw [List.map_cons, List.prod_cons, hPQ]
      simp [PG_mX, hl', Matrix.mul_assoc]

private lemma PG_valX0 {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X Y : Matrix (Idx D N) (Idx D N) ℂ)
    (f : FFac) (hf : PG_cR a' f = 0) : PG_valX e ι κ h a' X f = PG_valX e ι κ h a' Y f := by
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
  · simp only [PG_valX, PG_word0 e ι h a' X Y w hf]
  · simp only [PG_valX, PG_word0 e ι h a' X Y w hf]
  · rfl

private lemma PG_valX1 {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (X : Matrix (Idx D N) (Idx D N) ℂ)
    (c : ℂ) (Y : Matrix (Idx D N) (Idx D N) ℂ) (f : FFac) (hf : PG_cR a' f = 1) :
    PG_valX e ι κ h a' (X + c • Y) f = PG_valX e ι κ h a' X f + c * PG_valX e ι κ h a' Y f := by
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
  · obtain ⟨P, Q, hPQ⟩ := PG_word1 e ι h a' w hf
    simp only [PG_valX, hPQ]
    simp [Matrix.mul_add, Matrix.add_mul]
  · obtain ⟨P, Q, hPQ⟩ := PG_word1 e ι h a' w hf
    simp only [PG_valX, hPQ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ntr,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  · simp [PG_cR] at hf

private lemma PG_prod0 {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2)
    (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ L : List FFac, (L.map (PG_cR a')).sum = 0 →
      (L.map (PG_valX e ι κ h a' X)).prod = (L.map (PG_valX e ι κ h a' Y)).prod
  | [], _ => rfl
  | f :: L, hL => by
    rw [List.map_cons, List.sum_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    rw [PG_valX0 e ι κ h a' X Y f (by omega), PG_prod0 e ι κ h a' X Y L (by omega)]

/-- The product of the factors is linear in the resolvent of slot `a'` when it occurs once. -/
private lemma PG_prod_lin {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (c : ℂ) (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ L : List FFac, (L.map (PG_cR a')).sum = 1 →
      (L.map (PG_valX e ι κ h a' (X + c • Y))).prod =
        (L.map (PG_valX e ι κ h a' X)).prod + c * (L.map (PG_valX e ι κ h a' Y)).prod
  | [], hL => by simp at hL
  | f :: L, hL => by
    rw [List.map_cons, List.sum_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    rcases Nat.eq_zero_or_pos (PG_cR a' f) with hf | hf
    · rw [PG_prod_lin e ι κ h a' X c Y L (by omega), PG_valX0 e ι κ h a' (X + c • Y) X f hf,
        PG_valX0 e ι κ h a' Y X f hf]
      ring
    · rw [PG_valX1 e ι κ h a' X c Y f (by omega), PG_prod0 e ι κ h a' (X + c • Y) X L (by omega),
        PG_prod0 e ι κ h a' Y X L (by omega)]
      ring

/-! ### The letter `𝒢_{a'}` doubled -/

private lemma PG_dup_word {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) :
    ∀ w : List FLet, ((w.flatMap (FLet.dupRes a')).map (FLet.mat e ι h)).prod =
      (w.map (PG_mX e ι h a' (FLet.mat e ι h (.res a' false) * FLet.mat e ι h (.res a' true)))).prod
  | [] => by simp
  | l :: w => by
    rw [List.flatMap_cons, List.map_append, List.prod_append, PG_dup_word e ι h a' w,
      List.map_cons, List.prod_cons]
    congr 1
    rcases l with ⟨a, f⟩ | ⟨a, p⟩ | x | _
    · by_cases ha : a = a'
      · subst ha
        simp [FLet.dupRes, PG_mX, PG_isR]
      · simp [FLet.dupRes, PG_mX, PG_isR, ha]
    all_goals simp [FLet.dupRes, PG_mX, PG_isR]

private lemma PG_dup_prod {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (a' : Fin 2) (L : List FFac) :
    (L.map (FFac.val e ι κ h ∘ FFac.dupRes a')).prod =
      (L.map (PG_valX e ι κ h a'
        (FLet.mat e ι h (.res a' false) * FLet.mat e ι h (.res a' true)))).prod := by
  congr 1
  refine List.map_congr_left fun f _ => ?_
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
  · simp only [Function.comp_apply, FFac.dupRes, FFac.val, PG_valX, PG_dup_word]
  · simp only [Function.comp_apply, FFac.dupRes, FFac.val, PG_valX, PG_dup_word]
  · rfl

/-! ### `𝒢 - 𝒢ᴴ = 2 i Im z 𝒢 𝒢ᴴ` -/

/-- `G(z) - G(z)ᴴ = 2 i Im z · G(z) G(z)ᴴ` for Hermitian `X` and `Im z > 0`. -/
private lemma PG_res_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    res X z - (res X z)ᴴ = (2 * Complex.I * (z.im : ℂ)) • (res X z * (res X z)ᴴ) := by
  obtain ⟨-, h2⟩ := res_mul_sub X hX z hz
  have h3 : (X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * (res X z)ᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hX.eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] at this
    exact this
  have hc : z - starRingEnd ℂ z = 2 * Complex.I * (z.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  have hB : X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) =
      (X - z • (1 : Matrix ι ι ℂ)) + (2 * Complex.I * (z.im : ℂ)) • (1 : Matrix ι ι ℂ) := by
    rw [← hc, sub_smul]
    abel
  have h4 : res X z * ((X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * (res X z)ᴴ) = res X z := by
    rw [h3, Matrix.mul_one]
  rw [hB, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, h2, Matrix.one_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul] at h4
  exact (eq_sub_of_add_eq' h4).symm

private lemma PG_herm {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (a : Fin 2) :
    (Matrix.of h + (e.c a : ℂ) • lam D N e.A).IsHermitian :=
  FF_herm e h hh a

/-- The pairing of companion case (8), exceptional subcase, in the proof of Lemma 5.5
[claim_estimate_remainder_terms], with (5.29) [expansion_of_im]: if slot `a'` enters only through
one resolvent, the signed sum over its flag turns it into `𝒢 - 𝒢ᴴ = 2 i η 𝒢 𝒢ᴴ`. -/
theorem pkg_pairG_ident {D N : ℕ} (R : PkgExpr) (a' : Fin 2) (hR : R.onlyRes a' = true)
    (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (pr : Fin 2 → Bool) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
        R.evalP { e with s := Function.update e.s a' b } pr κ h =
      2 * Complex.I * ((e.z a').im : ℂ) * ((R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) *
        ∑ ι : Fin R.nb → Fin D, (((R.ffacs e.s pr).map (FFac.dupRes a')).map
          (FFac.val e ι κ h)).prod) := by
  obtain ⟨⟨hw, hd⟩, hc⟩ := (PG_onlyRes_iff R a').1 hR
  set L := R.ffacs e.s pr with hL
  have hbad : (L.map (PG_bad a')).sum = 0 := by
    rw [hL, PG_tot R e.s pr (PG_isD a') (PG_bad a') (fun _ _ _ => rfl) (fun _ => rfl)]
    have h1 : (R.weights.map fun q => PG_bad a' (.wt q.1 q.2)) = R.weights.map fun _ => 0 :=
      List.map_congr_left fun q hq => by simp [PG_bad, hw q hq]
    have h2 : (R.loops.map fun w => w.countP fun x =>
        ((PkgLetter.flet e.s pr x).map (PG_isD a')).getD false) = R.loops.map fun _ => 0 :=
      List.map_congr_left fun w hwl => by
        rw [PG_cnt_det]
        exact List.count_eq_zero.2 (hd w hwl)
    rw [h1, h2]
    simp
  have hres : (L.map (PG_cR a')).sum = 1 := by
    rw [hL, PG_tot R e.s pr (PG_isR a') (PG_cR a') (fun _ _ _ => rfl) (fun _ => rfl)]
    have h1 : (R.weights.map fun q => PG_cR a' (.wt q.1 q.2)) = R.weights.map fun _ => 0 :=
      List.map_congr_left fun q _ => rfl
    have h2 : (R.loops.map fun w => w.countP fun x =>
        ((PkgLetter.flet e.s pr x).map (PG_isR a')).getD false) =
        R.loops.map fun w => w.count (.lw (.res a')) :=
      List.map_congr_left fun w _ => PG_cnt_res e.s pr a' w
    rw [h1, h2, hc]
    simp
  -- the value at the flag `b` of slot `a'`: every letter `𝒢_{a'}` is the matrix of flag `b`
  have hb : ∀ b : Bool, R.evalP { e with s := Function.update e.s a' b } pr κ h =
      (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) * ∑ ι : Fin R.nb → Fin D,
        (L.map (PG_valX e ι κ h a' (FLet.mat e ι h (.res a' b)))).prod := by
    intro b
    rw [pkg_evalP_ffacs R { e with s := Function.update e.s a' b } pr hz κ h hh]
    change _ * ∑ ι : Fin R.nb → Fin D,
      ((R.ffacs (Function.update e.s a' b) pr).map (FFac.val _ ι κ h)).prod = _
    rw [PG_ffacs]
    congr 1
    exact Finset.sum_congr rfl fun ι _ => PG_prod_set e ι κ h a' b L hbad
  -- the letter at the flag `true` is the adjoint of the letter at the flag `false`
  have hG : ∀ ι : Fin R.nb → Fin D, FLet.mat e ι h (.res a' true) =
      (FLet.mat e ι h (.res a' false))ᴴ := fun ι => by simp [FLet.mat]
  have hkey : ∀ ι : Fin R.nb → Fin D,
      FLet.mat e ι h (.res a' false) - FLet.mat e ι h (.res a' true) =
        (2 * Complex.I * ((e.z a').im : ℂ)) •
          (FLet.mat e ι h (.res a' false) * FLet.mat e ι h (.res a' true)) := fun ι => by
    rw [hG]
    simp only [FLet.mat, Bool.false_eq_true, ↓reduceIte]
    exact PG_res_sub _ (PG_herm e h hh a') _ (hz a')
  have hid : ∀ ι : Fin R.nb → Fin D,
      (L.map (PG_valX e ι κ h a' (FLet.mat e ι h (.res a' false)))).prod -
        (L.map (PG_valX e ι κ h a' (FLet.mat e ι h (.res a' true)))).prod =
      2 * Complex.I * ((e.z a').im : ℂ) *
        ((L.map (FFac.dupRes a')).map (FFac.val e ι κ h)).prod := by
    intro ι
    have h1 := PG_prod_lin e ι κ h a' (FLet.mat e ι h (.res a' false)) (-1)
      (FLet.mat e ι h (.res a' true)) L hres
    have h2 := PG_prod_lin e ι κ h a' 0 (2 * Complex.I * ((e.z a').im : ℂ))
      (FLet.mat e ι h (.res a' false) * FLet.mat e ι h (.res a' true)) L hres
    have h3 := PG_prod_lin e ι κ h a' 0 1 0 L hres
    rw [one_smul, add_zero] at h3
    have h0 : (L.map (PG_valX e ι κ h a' 0)).prod = 0 := by linear_combination -h3
    rw [neg_one_smul, ← sub_eq_add_neg, hkey, ← zero_add ((2 * Complex.I * ((e.z a').im : ℂ)) •
      (FLet.mat e ι h (.res a' false) * FLet.mat e ι h (.res a' true))), h2, h0] at h1
    rw [List.map_map, PG_dup_prod e ι κ h a' L]
    linear_combination -h1
  have hsum : (∑ ι : Fin R.nb → Fin D,
      (L.map (PG_valX e ι κ h a' (FLet.mat e ι h (.res a' false)))).prod) -
      (∑ ι : Fin R.nb → Fin D,
        (L.map (PG_valX e ι κ h a' (FLet.mat e ι h (.res a' true)))).prod) =
      2 * Complex.I * ((e.z a').im : ℂ) * ∑ ι : Fin R.nb → Fin D,
        ((L.map (FFac.dupRes a')).map (FFac.val e ι κ h)).prod := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ι _ => hid ι
  rw [Fintype.sum_bool, hb true, hb false]
  simp only [↓reduceIte, Bool.false_eq_true]
  linear_combination ((R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)) * hsum

end RBMTransitionEdge

end
