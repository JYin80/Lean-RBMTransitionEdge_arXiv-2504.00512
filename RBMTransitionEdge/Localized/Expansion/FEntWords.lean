module

public import RBMTransitionEdge.Localized.Expansion.FRule
public import RBMTransitionEdge.Localized.Expansion.PkgInv2
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.FFactor
public import RBMTransitionEdge.Localized.Expansion.PairG
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.FFactor
import all RBMTransitionEdge.Localized.Expansion.PairG
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgShape

@[expose] public section

/-!
# The entries of the factor list of the rules

For every expression of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the entries of `rfacs` are the package entries `(x, y, segment)`
of the heavy packages of (5.79) [further_expansion_expression_Type_1] in order, with the labels of
the segment and its resolvent counts between the letters `Λ̃` (at most one more by the pairing
through `𝒢`); the resolvent count against (5.86) [character_relation_further_expansion]; the sizes
of the paired letters; the sides `a₁, a₂, a₃` as parts; and the side that `ffocus` empties.
-/

namespace RBMTransitionEdge

/-- The package entries of an expression as `(x, y, segment)`, in the order of `ffacs`. -/
def PkgExpr.pents (X : PkgExpr) : List (ℕ × ℕ × List PkgLetter) :=
  X.loops.flatMap fun w => if w.any PkgLetter.isEnt then
    let E := (w.rotate (w.findIdx PkgLetter.isEnt)).filterMap fun z => match z with
      | .ent u v => some (u, v)
      | _ => none
    let S := pkgSegs w
    (List.range S.length).filterMap fun t => match S[t]?, E[t]?, E[(t + 1) % E.length]? with
      | some σ, some e₀, some e₁ => some (e₀.2, e₁.1, σ)
      | _, _, _ => none
  else []

/-- The factor of `rfacs` of a package entry. -/
def PkgExpr.rent (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) : FFac :=
  let f : FFac := .ent e.1 e.2.1 (e.2.2.filterMap (PkgLetter.flet (fun _ => false) X.fpm))
  if X.fpg 0 then f.dupRes 0 else if X.fpg 1 then f.dupRes 1 else f

/-- The loop words of a factor list. -/
def fLoops (F : List FFac) : List (List FLet) :=
  F.filterMap fun f => match f with
    | .loop w => some w
    | _ => none

/-- The number of resolvents of a factor word. -/
def fresN (w : List FLet) : ℕ :=
  w.countP fun x => match x with
    | .res _ _ => true
    | _ => false

/-- `1` if a resolvent is doubled by the pairing through `𝒢`, else `0`. -/
def PkgExpr.fpi (X : PkgExpr) : ℕ := if X.fpg 0 || X.fpg 1 then 1 else 0

/-- The resolvent counts between the letters `Λ̃` of a segment. -/
def pkgParts (σ : List PkgLetter) : List ℕ :=
  (σ.splitOnP PkgLetter.isLam).map fun s => s.countP PkgLetter.isRes

/-! ### The factors of one word -/

open private FF_pk FF_wf FF_ffacs from RBMTransitionEdge.Localized.Expansion.FFactor
open private PG_E PG_len PG_pk PG_range_getD PG_isR PG_tot PG_cnt_res PG_onlyRes_iff PG_flatMap_sum
  from RBMTransitionEdge.Localized.Expansion.PairG
open private PB_segs_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private isEntP isResP nfac from RBMTransitionEdge.Localized.Expansion.PkgWords

/-- The package entries of one word, as in `PkgExpr.pents`. -/
private def FW_pw (w : List PkgLetter) : List (ℕ × ℕ × List PkgLetter) :=
  if w.any PkgLetter.isEnt then
    (List.range (pkgSegs w).length).filterMap fun t =>
      match (pkgSegs w)[t]?, (PG_E w)[t]?, (PG_E w)[(t + 1) % (PG_E w).length]? with
      | some σ, some e₀, some e₁ => some (e₀.2, e₁.1, σ)
      | _, _, _ => none
  else []

private theorem FW_pents (X : PkgExpr) : X.pents = X.loops.flatMap FW_pw := rfl

/-- The factor of a package entry before the pairing through `𝒢`. -/
private def FW_mk (pr : Fin 2 → Bool) (e : ℕ × ℕ × List PkgLetter) : FFac :=
  .ent e.1 e.2.1 (e.2.2.filterMap (PkgLetter.flet (fun _ => false) pr))

/-- The pairing through `𝒢` of `rfacs`. -/
private def FW_g (X : PkgExpr) (f : FFac) : FFac :=
  if X.fpg 0 then f.dupRes 0 else if X.fpg 1 then f.dupRes 1 else f

private theorem FW_rfacs (X : PkgExpr) :
    X.rfacs = (X.ffacs (fun _ => false) X.fpm).map (FW_g X) := rfl

private theorem FW_rent (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) :
    X.rent e = FW_g X (FW_mk X.fpm e) := rfl

/-- The entries of one word with a `Δ`, as a map over its pieces. -/
private theorem FW_pw_eq (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) :
    FW_pw w = (List.range (pkgSegs w).length).map fun t =>
      (((PG_E w).getD t (0, 0)).2, ((PG_E w).getD ((t + 1) % (PG_E w).length) (0, 0)).1,
        (pkgSegs w).getD t []) := by
  unfold FW_pw
  simp only [hw, ↓reduceIte]
  rw [← List.filterMap_eq_map]
  refine List.filterMap_congr fun t ht => ?_
  have hlen := PG_len w hw
  have ht' : t < (pkgSegs w).length := List.mem_range.1 ht
  have h1 : t < (PG_E w).length := hlen ▸ ht'
  have h2 : (t + 1) % (PG_E w).length < (PG_E w).length := Nat.mod_lt _ (by omega)
  simp [List.getElem?_eq_getElem ht', List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    List.getD_eq_getElem?_getD]

/-- The segments of the entries of one word with a `Δ` are its packages. -/
private theorem FW_pw_segs (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) :
    (FW_pw w).map (fun e => e.2.2) = pkgSegs w := by
  rw [FW_pw_eq w hw, List.map_map]
  exact (PG_range_getD (pkgSegs w) [] id).trans (List.map_id _)

/-- The factors of one word with a `Δ` are the factors of its package entries. -/
private theorem FW_wf_ent (pr : Fin 2 → Bool) (w : List PkgLetter)
    (hw : w.any PkgLetter.isEnt = true) :
    FF_wf (fun _ => false) pr w = (FW_pw w).map (FW_mk pr) := by
  unfold FF_wf
  simp only [hw, ↓reduceIte]
  change FF_pk _ pr (pkgSegs w) (PG_E w) = _
  rw [PG_pk _ _ _ _ (PG_len w hw), FW_pw_eq w hw, List.map_map]
  rfl

private theorem FW_wf_free (pr : Fin 2 → Bool) (w : List PkgLetter)
    (hw : w.any PkgLetter.isEnt = false) :
    FF_wf (fun _ => false) pr w =
      [FFac.loop (w.filterMap (PkgLetter.flet (fun _ => false) pr))] := by
  unfold FF_wf
  simp only [hw, Bool.false_eq_true, ↓reduceIte]

private theorem FW_pw_free (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = false) :
    FW_pw w = [] := by
  unfold FW_pw
  simp only [hw, Bool.false_eq_true, ↓reduceIte]

private theorem FW_g_isSome (X : PkgExpr) (f : FFac) :
    (FW_g X f).entData.isSome = f.entData.isSome := by
  unfold FW_g
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> split_ifs <;> rfl

/-! ### Lists cut by `splitOnP` -/

/-- Letters that are no separators, put in front of a list, join its first piece. -/
private theorem FW_split_pre {α : Type*} (p : α → Bool) :
    ∀ (ys rest : List α), (∀ y ∈ ys, p y = false) →
      (ys ++ rest).splitOnP p = (rest.splitOnP p).modifyHead (ys ++ ·)
  | [], rest, _ => by
      obtain ⟨s, L, h⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p rest)
      simp [h]
  | y :: ys, rest, h => by
      have hy : p y = false := h y List.mem_cons_self
      rw [List.cons_append, List.splitOnP_cons_eq_ite_modifyHead,
        FW_split_pre p ys rest fun z hz => h z (List.mem_cons_of_mem _ hz)]
      obtain ⟨s, L, hs⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p rest)
      rw [hs]; simp [hy]

/-- `splitOnP` commutes with a letterwise map that keeps the separators and creates none. -/
private theorem FW_split_flatMap {α β : Type*} (p : α → Bool) (q : β → Bool) (h : α → List β)
    (hs : ∀ x, p x = true → ∃ y, h x = [y] ∧ q y = true)
    (hn : ∀ x, p x = false → ∀ y ∈ h x, q y = false) :
    ∀ l : List α, (l.flatMap h).splitOnP q = (l.splitOnP p).map (·.flatMap h)
  | [] => by simp
  | x :: l => by
      rw [List.flatMap_cons, List.splitOnP_cons_eq_ite_modifyHead]
      cases hx : p x
      · rw [FW_split_pre q (h x) _ (hn x hx), FW_split_flatMap p q h hs hn l]
        obtain ⟨s, L, hsL⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p l)
        rw [hsL]; simp
      · obtain ⟨y, hy, hq⟩ := hs x hx
        rw [hy, List.singleton_append, List.splitOnP_cons_eq_ite_modifyHead,
          FW_split_flatMap p q h hs hn l]
        simp [hq]

/-- The counts along the pieces of `splitOnP`, and their number. -/
private theorem FW_split_count {α : Type*} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = false) :
    ∀ l : List α, ((l.splitOnP p).map (List.countP q)).sum = l.countP q ∧
      (l.splitOnP p).length = l.countP p + 1
  | [] => by simp
  | x :: l => by
      obtain ⟨h1, h2⟩ := FW_split_count p q hpq l
      rw [List.splitOnP_cons_eq_ite_modifyHead]
      cases hx : p x
      · obtain ⟨s, L, he⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p l)
        rw [he] at h1 h2
        simp only [Bool.false_eq_true, ↓reduceIte, he, List.modifyHead_cons, List.map_cons,
          List.sum_cons, List.countP_cons, hx, List.length_cons] at h1 h2 ⊢
        constructor <;> omega
      · simp only [↓reduceIte, List.map_cons, List.sum_cons, List.countP_nil, h1,
          List.countP_cons, hpq x hx, hx, List.length_cons, h2]
        constructor <;> simp

/-- A count of a piece of `splitOnP` is at most the count of the list. -/
private theorem FW_split_le {α : Type*} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = false)
    (l s : List α) (hs : s ∈ l.splitOnP p) : s.countP q ≤ l.countP q := by
  rw [← (FW_split_count p q hpq l).1]
  exact List.le_sum_of_mem (List.mem_map_of_mem hs)

/-! ### The parts of an entry -/

/-- A factor letter is a resolvent. -/
private def FW_fres (x : FLet) : Bool := match x with
  | .res _ _ => true
  | _ => false

private theorem FW_piece_cnt (pr : Fin 2 → Bool) (a : Fin 2) :
    ∀ s : List PkgLetter, (((s.filterMap (PkgLetter.flet (fun _ => false) pr)).flatMap
      (FLet.dupRes a)).countP FW_fres) = s.countP PkgLetter.isRes + s.count (.lw (.res a))
  | [] => by simp
  | x :: s => by
      have ih := FW_piece_cnt pr a s
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;>
        simp only [List.filterMap_cons, PkgLetter.flet, List.flatMap_cons, FLet.dupRes,
          List.countP_cons, List.countP_append, List.count_cons, ih] <;>
        split_ifs <;> simp_all [FW_fres, PkgLetter.isRes, List.countP_cons] <;> omega

private theorem FW_piece_cnt0 (pr : Fin 2 → Bool) :
    ∀ s : List PkgLetter, (s.filterMap (PkgLetter.flet (fun _ => false) pr)).countP FW_fres =
      s.countP PkgLetter.isRes
  | [] => by simp
  | x :: s => by
      have ih := FW_piece_cnt0 pr s
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;>
        simp only [List.filterMap_cons, PkgLetter.flet, List.countP_cons, ih] <;>
        simp [FW_fres, PkgLetter.isRes]

/-- The pieces of the factor word of a segment at its letters `Λ̃`. -/
private theorem FW_split_flet (pr : Fin 2 → Bool) (σ : List PkgLetter) :
    (σ.filterMap (PkgLetter.flet (fun _ => false) pr)).splitOnP (fun x => x == .lamt) =
      (σ.splitOnP PkgLetter.isLam).map
        (fun s => s.filterMap (PkgLetter.flet (fun _ => false) pr)) := by
  simp only [List.filterMap_eq_flatMap_toList]
  refine FW_split_flatMap _ _ _ (fun x hx => ?_) (fun x hx y hy => ?_) σ
  · rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> simp_all [PkgLetter.isLam, PkgLetter.flet]
  · rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> simp_all [PkgLetter.isLam, PkgLetter.flet]

private theorem FW_split_dup (a : Fin 2) (W : List FLet) :
    (W.flatMap (FLet.dupRes a)).splitOnP (fun x => x == .lamt) =
      (W.splitOnP (fun x => x == .lamt)).map (fun s => s.flatMap (FLet.dupRes a)) := by
  refine FW_split_flatMap _ _ _ (fun x hx => ?_) (fun x hx y hy => ?_) W
  · rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y | _ <;> simp_all [FLet.dupRes]
  · have key : ∀ z ∈ FLet.dupRes a x, z ≠ .lamt := by
      rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y' | _
      · simp only [FLet.dupRes]; split_ifs <;> simp
      · simp [FLet.dupRes]
      · simp [FLet.dupRes]
      · simp at hx
    simpa using key y hy

/-- The parts of the entry of a segment, without and with the pairing through `𝒢_a`. -/
private theorem FW_parts (pr : Fin 2 → Bool) (σ : List PkgLetter) :
    FLet.parts (σ.filterMap (PkgLetter.flet (fun _ => false) pr)) = pkgParts σ := by
  unfold FLet.parts pkgParts
  rw [FW_split_flet, List.map_map]
  exact List.map_congr_left fun s _ => FW_piece_cnt0 pr s

private theorem FW_parts_dup (pr : Fin 2 → Bool) (a : Fin 2) (σ : List PkgLetter) :
    FLet.parts ((σ.filterMap (PkgLetter.flet (fun _ => false) pr)).flatMap (FLet.dupRes a)) =
      (σ.splitOnP PkgLetter.isLam).map
        (fun s => s.countP PkgLetter.isRes + s.count (.lw (.res a))) := by
  unfold FLet.parts
  rw [FW_split_dup, FW_split_flet, List.map_map, List.map_map]
  exact List.map_congr_left fun s _ => FW_piece_cnt pr a s

/-- A package entry comes from a package of a word with a `Δ`. -/
private theorem FW_mem_pents (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) :
    ∃ w ∈ X.loops, w.any PkgLetter.isEnt = true ∧ e.2.2 ∈ pkgSegs w := by
  rw [FW_pents, List.mem_flatMap] at he
  obtain ⟨w, hw, he⟩ := he
  cases hwE : w.any PkgLetter.isEnt
  · rw [FW_pw_free w hwE] at he; simp at he
  · refine ⟨w, hw, hwE, ?_⟩
    rw [← FW_pw_segs w hwE]
    exact List.mem_map_of_mem he

/-- The counts of a package are those of its word, for letters other than `Δ`. -/
private theorem FW_seg_le (q : PkgLetter → Bool) (hq : ∀ u v, q (.ent u v) = false)
    (w σ : List PkgLetter) (hσ : σ ∈ pkgSegs w) : σ.countP q ≤ w.countP q := by
  have h := (PB_segs_count q (fun x hx => by
    rcases x with _ | ⟨u, v⟩
    · simp [isEntP] at hx
    · exact hq u v) w).1
  rw [← h]
  exact List.le_sum_of_mem (List.mem_map_of_mem (f := List.countP q) hσ)

/-- Under `onlyRes a`, every piece of a segment has at most one resolvent of slot `a`. -/
private theorem FW_res_le_one (X : PkgExpr) (a : Fin 2) (hX : X.onlyRes a = true)
    (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (s : List PkgLetter)
    (hs : s ∈ e.2.2.splitOnP PkgLetter.isLam) : s.count (.lw (.res a)) ≤ 1 := by
  obtain ⟨w, hwL, -, hσ⟩ := FW_mem_pents X e he
  have h3 := ((PG_onlyRes_iff X a).1 hX).2
  have hw : w.count (.lw (.res a)) ≤ 1 := by
    rw [← h3]
    exact List.le_sum_of_mem
      (List.mem_map_of_mem (f := fun w => List.count (PkgLetter.lw (LoopLetter.res a)) w) hwL)
  simp only [List.count_eq_countP] at hw ⊢
  refine le_trans ?_ (le_trans (FW_seg_le _ (fun u v => rfl) w _ hσ) hw)
  exact FW_split_le _ _ (fun x hx => by rcases x with ((b | b | y | o) | ⟨u, v⟩) <;>
    simp_all [PkgLetter.isLam]) _ _ hs

/-- The bounds of `pkg_rent_parts` for parts `p + c` with `c ≤ p` and `c ≤ π`. -/
private theorem FW_parts_bound (L : List (List PkgLetter)) (c : List PkgLetter → ℕ) (π : ℕ)
    (hc : ∀ s ∈ L, c s ≤ s.countP PkgLetter.isRes ∧ c s ≤ π) :
    (L.map fun s => s.countP PkgLetter.isRes + c s).length =
        (L.map fun s => s.countP PkgLetter.isRes).length ∧
      ∀ t < (L.map fun s => s.countP PkgLetter.isRes).length,
        (L.map fun s => s.countP PkgLetter.isRes).getD t 0 ≤
          (L.map fun s => s.countP PkgLetter.isRes + c s).getD t 0 ∧
        (L.map fun s => s.countP PkgLetter.isRes + c s).getD t 0 ≤
          (L.map fun s => s.countP PkgLetter.isRes).getD t 0 + π ∧
        ((L.map fun s => s.countP PkgLetter.isRes).getD t 0 = 0 →
          (L.map fun s => s.countP PkgLetter.isRes + c s).getD t 0 = 0) := by
  refine ⟨by simp, fun t ht => ?_⟩
  rw [List.length_map] at ht
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getD_eq_getElem _ _ (by simpa using ht)]
  simp only [List.getElem_map]
  have := hc _ (List.getElem_mem ht)
  refine ⟨by omega, by omega, fun h => by omega⟩

/-- The entries of `rfacs` are the package entries, in order. -/
theorem pkg_rfacs_pents (X : PkgExpr) :
    X.rfacs.filter (fun f => f.entData.isSome) = X.pents.map X.rent := by
  rw [FW_rfacs, List.filter_map, FF_ffacs, FW_pents, List.map_flatMap]
  rw [show ((fun f : FFac => f.entData.isSome) ∘ FW_g X) = fun f => f.entData.isSome from
    funext (FW_g_isSome X), List.filter_append,
    List.filter_eq_nil_iff.2 (fun f hf => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hf; simp [FFac.entData]),
    List.nil_append, List.filter_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun w _ => ?_
  cases hw : w.any PkgLetter.isEnt
  · rw [FW_wf_free _ w hw, FW_pw_free w hw]
    rfl
  · rw [FW_wf_ent _ w hw, List.filter_eq_self.2 (fun f hf => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hf; rfl), List.map_map]
    rfl

/-- The data of the entry of a segment: its labels, and its parts, those of the segment with at
most `fpi` added to a nonzero part. -/
theorem pkg_rent_parts (X : PkgExpr) (e : ℕ × ℕ × List PkgLetter) (he : e ∈ X.pents) (d : FEnt)
    (hd : (X.rent e).entData = some d) :
    d.1 = e.1 ∧ d.2.1 = e.2.1 ∧ d.2.2.1.length = (pkgParts e.2.2).length ∧
      ∀ t < (pkgParts e.2.2).length, (pkgParts e.2.2).getD t 0 ≤ d.2.2.1.getD t 0 ∧
        d.2.2.1.getD t 0 ≤ (pkgParts e.2.2).getD t 0 + X.fpi ∧
        ((pkgParts e.2.2).getD t 0 = 0 → d.2.2.1.getD t 0 = 0) := by
  rw [FW_rent] at hd
  unfold FW_g FW_mk at hd
  split_ifs at hd with h0 h1
  · simp only [FFac.dupRes, FFac.entData, Option.some.injEq] at hd
    subst hd
    unfold pkgParts
    rw [FW_parts_dup]
    have hpi : X.fpi = 1 := by simp [PkgExpr.fpi, h0]
    have hX : X.onlyRes 0 = true := by
      simp only [PkgExpr.fpg, Bool.and_eq_true] at h0; exact h0.1
    refine ⟨rfl, rfl, FW_parts_bound _ _ _ fun s hs => ⟨?_, ?_⟩⟩
    · rw [List.count_eq_countP]
      exact List.countP_mono_left fun x _ hx => by
        simp only [beq_iff_eq] at hx; subst hx; rfl
    · rw [hpi]; exact FW_res_le_one X 0 hX e he s hs
  · simp only [FFac.dupRes, FFac.entData, Option.some.injEq] at hd
    subst hd
    unfold pkgParts
    rw [FW_parts_dup]
    have hpi : X.fpi = 1 := by simp [PkgExpr.fpi, h1]
    have hX : X.onlyRes 1 = true := by
      simp only [PkgExpr.fpg, Bool.and_eq_true] at h1; exact h1.1
    refine ⟨rfl, rfl, FW_parts_bound _ _ _ fun s hs => ⟨?_, ?_⟩⟩
    · rw [List.count_eq_countP]
      exact List.countP_mono_left fun x _ hx => by
        simp only [beq_iff_eq] at hx; subst hx; rfl
    · rw [hpi]; exact FW_res_le_one X 1 hX e he s hs
  · simp only [FFac.entData, Option.some.injEq] at hd
    subst hd
    rw [FW_parts]
    exact ⟨rfl, rfl, rfl, fun t _ => ⟨le_rfl, Nat.le_add_right _ _, id⟩⟩

/-! ### Sums over the factor list -/

open private charsP_eq from RBMTransitionEdge.Localized.Expansion.PkgWords

/-- The number of letters of a kind in the word of an entry or a loop. -/
private def FW_cntP (p : FLet → Bool) : FFac → ℕ
  | .ent _ _ w => w.countP p
  | .loop w => w.countP p
  | .wt _ _ => 0

/-- `1` for an entry or a loop, `0` for a light weight. -/
private def FW_one : FFac → ℕ
  | .wt _ _ => 0
  | _ => 1

/-- The summand of `pkg_rfacs_res` of a factor. -/
private def FW_val : FFac → ℤ
  | .ent _ _ w => ((FLet.parts w).sum : ℤ) - 1
  | .loop w => (fresN w : ℤ) - 1
  | .wt _ _ => 0

/-- The resolvents doubled by the pairing through `𝒢` in a factor. -/
private def FW_gain (X : PkgExpr) (f : FFac) : ℕ :=
  if X.fpg 0 then FW_cntP (PG_isR 0) f else if X.fpg 1 then FW_cntP (PG_isR 1) f else 0

private theorem FW_val_sum : ∀ F : List FFac,
    ((F.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum +
        ((fLoops F).map fun w => (fresN w : ℤ) - 1).sum = (F.map FW_val).sum
  | [] => by simp [fLoops]
  | f :: F => by
      have ih := FW_val_sum F
      simp only [fLoops] at ih ⊢
      rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
        simp only [List.filterMap_cons, FFac.entData, List.map_cons, List.sum_cons,
          FW_val] <;> linarith

private theorem FW_cnt_dup (a : Fin 2) : ∀ w : List FLet,
    (w.flatMap (FLet.dupRes a)).countP FW_fres = w.countP FW_fres + w.countP (PG_isR a)
  | [] => by simp
  | x :: w => by
      have ih := FW_cnt_dup a w
      rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y | _ <;>
        simp only [List.flatMap_cons, FLet.dupRes, List.countP_append, List.countP_cons, ih] <;>
        split_ifs <;> simp_all [FW_fres, PG_isR, List.countP_cons] <;> omega

private theorem FW_parts_sum (w : List FLet) : (FLet.parts w).sum = w.countP FW_fres := by
  unfold FLet.parts
  exact (FW_split_count (fun x => x == .lamt) FW_fres (fun x hx => by
    simp only [beq_iff_eq] at hx; subst hx; rfl) w).1

private theorem FW_fresN (w : List FLet) : fresN w = w.countP FW_fres := rfl

private theorem FW_val_g (X : PkgExpr) (f : FFac) :
    FW_val (FW_g X f) = (FW_cntP FW_fres f : ℤ) + FW_gain X f - FW_one f := by
  unfold FW_g FW_gain
  split_ifs <;> rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
    simp [FW_val, FFac.dupRes, FW_parts_sum, FW_cnt_dup, FW_cntP, FW_one, FW_fresN]

private theorem FW_sum3 (A B C : FFac → ℕ) : ∀ F : List FFac,
    (F.map fun f => (A f : ℤ) + B f - C f).sum =
      ((F.map A).sum : ℤ) + (F.map B).sum - (F.map C).sum
  | [] => by simp
  | f :: F => by simp only [List.map_cons, List.sum_cons, FW_sum3 A B C F]; push_cast; ring

private theorem FW_sum_one (X : PkgExpr) :
    ((X.ffacs (fun _ => false) X.fpm).map FW_one).sum = (X.loops.map nfac).sum := by
  rw [FF_ffacs, List.map_append, List.sum_append, List.map_map, PG_flatMap_sum]
  have h0 : (X.weights.map (FW_one ∘ fun p => FFac.wt p.1 p.2)).sum = 0 := by
    induction X.weights <;> simp_all [FW_one]
  rw [h0, zero_add]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  cases hw : w.any PkgLetter.isEnt
  · rw [FW_wf_free _ w hw]
    unfold nfac
    rw [show w.any isEntP = w.any PkgLetter.isEnt from rfl, hw]
    rfl
  · rw [FW_wf_ent _ w hw, List.map_map]
    have h1 : ((FW_pw w).map (FW_one ∘ FW_mk X.fpm)).sum = (FW_pw w).length := by
      clear hw; induction FW_pw w <;> simp_all [FW_one, FW_mk]; omega
    rw [h1, FW_pw_eq w hw, List.length_map, List.length_range]
    exact (PB_segs_count (fun _ => false) (fun _ _ => rfl) w).2.1

private theorem FW_sum_cnt (X : PkgExpr) (p : FLet → Bool) :
    ((X.ffacs (fun _ => false) X.fpm).map (FW_cntP p)).sum = (X.loops.map fun w =>
      w.countP fun x => ((PkgLetter.flet (fun _ => false) X.fpm x).map p).getD false).sum := by
  rw [PG_tot X _ _ p (FW_cntP p) (fun _ _ _ => rfl) (fun _ => rfl)]
  have h0 : (X.weights.map fun q => FW_cntP p (.wt q.1 q.2)).sum = 0 := by
    induction X.weights <;> simp_all [FW_cntP]
  rw [h0, zero_add]

private theorem FW_sum_res (X : PkgExpr) :
    ((X.ffacs (fun _ => false) X.fpm).map (FW_cntP FW_fres)).sum =
      (X.loops.map fun w => w.countP isResP).sum := by
  rw [FW_sum_cnt]
  congr 1
  refine List.map_congr_left fun w _ => List.countP_congr fun x _ => ?_
  rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> rfl

private theorem FW_sum_gain (X : PkgExpr) :
    ((X.ffacs (fun _ => false) X.fpm).map (FW_gain X)).sum = X.fpi := by
  by_cases h0 : X.fpg 0 = true
  · rw [show FW_gain X = FW_cntP (PG_isR 0) from funext fun f => by simp [FW_gain, h0],
      FW_sum_cnt]
    simp only [PG_cnt_res]
    have hX : X.onlyRes 0 = true := by
      simp only [PkgExpr.fpg, Bool.and_eq_true] at h0; exact h0.1
    rw [((PG_onlyRes_iff X 0).1 hX).2]
    simp [PkgExpr.fpi, h0]
  · by_cases h1 : X.fpg 1 = true
    · rw [show FW_gain X = FW_cntP (PG_isR 1) from funext fun f => by simp [FW_gain, h0, h1],
        FW_sum_cnt]
      simp only [PG_cnt_res]
      have hX : X.onlyRes 1 = true := by
        simp only [PkgExpr.fpg, Bool.and_eq_true] at h1; exact h1.1
      rw [((PG_onlyRes_iff X 1).1 hX).2]
      simp [PkgExpr.fpi, h1]
    · rw [show FW_gain X = fun _ => 0 from funext fun f => by simp [FW_gain, h0, h1]]
      simp [PkgExpr.fpi, h0, h1]

/-- Q2 (d1): `Σ_E (r - 1) + Σ_loops (res - 1) = m - n + π` for every expression. -/
theorem pkg_rfacs_res (X : PkgExpr) :
    ((X.rfacs.filterMap FFac.entData).map fun d => (d.2.2.1.sum : ℤ) - 1).sum +
        ((fLoops X.rfacs).map fun w => (fresN w : ℤ) - 1).sum =
      X.charsP.1 - X.charsP.2.1 + X.fpi := by
  rw [FW_val_sum, FW_rfacs, List.map_map, show (FW_val ∘ FW_g X) = fun f =>
    (FW_cntP FW_fres f : ℤ) + FW_gain X f - FW_one f from funext (FW_val_g X), FW_sum3,
    FW_sum_one, FW_sum_res, FW_sum_gain, charsP_eq]
  ring

/-- A factor letter is a paired `𝔐`. -/
private def FW_pd (z : FLet) : Bool := match z with
  | .det _ pr => pr
  | _ => false

/-- The summand of the extra `Im m` of `pkg_rfacs_ext` of a factor. -/
private def FW_iv : FFac → ℤ
  | .ent _ _ w => 2 * ((w.countP FW_pd : ℕ) : ℤ)
  | _ => 0

private theorem FW_iv_sum : ∀ F : List FFac,
    ((F.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum = (F.map FW_iv).sum
  | [] => by simp
  | f :: F => by
      have ih := FW_iv_sum F
      rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
        simp [List.filterMap_cons, FFac.entData, FW_iv, ih]; rfl

private theorem FW_pd_dup (a : Fin 2) : ∀ w : List FLet,
    (w.flatMap (FLet.dupRes a)).countP FW_pd = w.countP FW_pd
  | [] => by simp
  | x :: w => by
      have ih := FW_pd_dup a w
      rcases x with ⟨b, f⟩ | ⟨b, f⟩ | y | _ <;>
        simp only [List.flatMap_cons, FLet.dupRes, List.countP_append, List.countP_cons, ih] <;>
        split_ifs <;> simp_all [FW_pd]; omega

private theorem FW_iv_g (X : PkgExpr) (f : FFac) :
    FW_iv (FW_g X f) ≤ 2 * (FW_cntP FW_pd f : ℤ) := by
  unfold FW_g
  split_ifs <;> rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;>
    simp [FW_iv, FFac.dupRes, FW_pd_dup, FW_cntP]

private theorem FW_sum_pd (X : PkgExpr) :
    ((X.ffacs (fun _ => false) X.fpm).map (FW_cntP FW_pd)).sum ≤ 1 := by
  rw [FW_sum_cnt]
  have key : ∀ a : Fin 2, X.fpm a = true →
      (X.loops.map fun w => w.count (.lw (.det a))).sum = 1 := by
    intro a ha
    simp only [PkgExpr.fpm, PkgExpr.onlyDet, Bool.and_eq_true, beq_iff_eq] at ha
    exact ha.1.1.2
  by_cases h0 : X.fpm 0 = true
  · have h1 : X.fpm 1 = false := by
      have h0' := h0
      simp only [PkgExpr.fpm, Bool.and_eq_true] at h0'
      unfold PkgExpr.fpm
      rw [h0'.1.1, h0'.1.2]
      simp
    rw [← key 0 h0]
    refine le_of_eq (congrArg _ (List.map_congr_left fun w _ => ?_))
    rw [List.count_eq_countP]
    refine List.countP_congr fun x _ => ?_
    rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases b
    all_goals simp [PkgLetter.flet, FW_pd, h0, h1]
  · by_cases h1 : X.fpm 1 = true
    · rw [← key 1 h1]
      refine le_of_eq (congrArg _ (List.map_congr_left fun w _ => ?_))
      rw [List.count_eq_countP]
      refine List.countP_congr fun x _ => ?_
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases b
      all_goals simp_all [PkgLetter.flet, FW_pd]
    · refine le_of_eq_of_le (b := 0) ?_ zero_le_one
      refine List.sum_eq_zero fun n hn => ?_
      obtain ⟨w, _, rfl⟩ := List.mem_map.1 hn
      refine List.countP_eq_zero.2 fun x _ => ?_
      rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> try fin_cases b
      all_goals simp_all [PkgLetter.flet, FW_pd]

/-- Q2 (e), form: the extra size of an entry is `(Im m)^{2c}`, with at most one paired letter. -/
theorem pkg_rfacs_ext (X : PkgExpr) :
    (∀ d ∈ X.rfacs.filterMap FFac.entData, d.2.2.2.1.a = 0 ∧ d.2.2.2.1.l = 0 ∧
      d.2.2.2.1.d = 0 ∧ d.2.2.2.1.o = 0 ∧ 0 ≤ d.2.2.2.1.i) ∧
      ((X.rfacs.filterMap FFac.entData).map fun d => d.2.2.2.1.i).sum ≤ 2 := by
  refine ⟨fun d hd => ?_, ?_⟩
  · obtain ⟨f, _, hf⟩ := List.mem_filterMap.1 hd
    rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩ <;> simp only [FFac.entData, Option.some.injEq,
      reduceCtorEq] at hf
    subst hf
    simp
  · rw [FW_iv_sum, FW_rfacs, List.map_map]
    calc ((X.ffacs (fun _ => false) X.fpm).map (FW_iv ∘ FW_g X)).sum
        ≤ ((X.ffacs (fun _ => false) X.fpm).map fun f => 2 * (FW_cntP FW_pd f : ℤ)).sum :=
          List.sum_le_sum fun f _ => FW_iv_g X f
      _ = 2 * (((X.ffacs (fun _ => false) X.fpm).map (FW_cntP FW_pd)).sum : ℕ) := by
          rw [List.sum_map_mul_left, Nat.cast_list_sum, List.map_map]; rfl
      _ ≤ 2 := by have := FW_sum_pd X; omega

/-! ### The sides of a letter `Λ̃` in a cyclic word -/

/-- A letter that does not end a side: neither `Δ` nor `Λ̃`. -/
private def FW_go (x : PkgLetter) : Bool := !(x.isEnt || x.isLam)

/-- The number of resolvents of a list before its first `Δ` or `Λ̃`. -/
private def FW_run (l : List PkgLetter) : ℕ := (l.takeWhile FW_go).countP PkgLetter.isRes

/-- The side count of `Λ̃_o` in one word, as in `PkgExpr.lamSide`. -/
private def FW_wside (w : List PkgLetter) (o : Fin 2) (right : Bool) : ℕ :=
  let i := w.idxOf (.lw (.lamt o))
  (((List.range (w.length - 1)).map fun t =>
      if right then (i + 1 + t) % w.length else (i + w.length - 1 - t) % w.length).takeWhile
    fun r => match w[r]? with
      | some (PkgLetter.ent _ _) => false
      | some (PkgLetter.lw (LoopLetter.lamt _)) => false
      | _ => true).countP fun r => match w[r]? with
        | some (PkgLetter.lw (LoopLetter.res _)) => true
        | _ => false

private theorem FW_lamSide (R : PkgExpr) (o : Fin 2) (right : Bool) :
    R.lamSide o right = match R.loops.find? fun w => w.contains (.lw (.lamt o)) with
      | none => 0
      | some w => FW_wside w o right := rfl

/-- The stop test of `PkgExpr.lamSide` on an optional letter. -/
private def FW_goO (x : Option PkgLetter) : Bool := match x with
  | some (PkgLetter.ent _ _) => false
  | some (PkgLetter.lw (LoopLetter.lamt _)) => false
  | _ => true

/-- The count test of `PkgExpr.lamSide` on an optional letter. -/
private def FW_resO (x : Option PkgLetter) : Bool := match x with
  | some (PkgLetter.lw (LoopLetter.res _)) => true
  | _ => false

private theorem FW_goO_some : FW_goO ∘ some = FW_go := by
  funext x; rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> rfl

private theorem FW_resO_some : FW_resO ∘ some = PkgLetter.isRes := by
  funext x; rcases x with ((b | b | y | o) | ⟨u, v⟩) <;> rfl

/-- The scan of a side, read on the letters it visits. -/
private theorem FW_scan (L : List ℕ) (g : ℕ → Option PkgLetter) :
    (L.takeWhile fun r => FW_goO (g r)).countP (fun r => FW_resO (g r)) =
      ((L.map g).takeWhile FW_goO).countP FW_resO := by
  rw [List.takeWhile_map, List.countP_map]; rfl

private theorem FW_scan_some (V : List PkgLetter) :
    ((V.map some).takeWhile FW_goO).countP FW_resO = FW_run V := by
  rw [List.takeWhile_map, List.countP_map, FW_goO_some, FW_resO_some]; rfl

/-- The word read from just after position `|A|`. -/
private theorem FW_rot_split (A B : List PkgLetter) (y : PkgLetter) :
    (A ++ y :: B).rotate (A.length + 1) = B ++ A ++ [y] := by
  have := List.rotate_append_length_eq (A ++ [y]) B
  simp only [List.length_append, List.length_singleton, List.append_assoc,
    List.singleton_append] at this
  rw [this]; simp

/-- The positions visited by a side, to the right and to the left. -/
private theorem FW_pos_right (A B : List PkgLetter) (y : PkgLetter) :
    (List.range ((A ++ y :: B).length - 1)).map
        (fun t => (A ++ y :: B)[(A.length + 1 + t) % (A ++ y :: B).length]?) =
      (B ++ A).map some := by
  have hlen : ((List.range ((A ++ y :: B).length - 1)).map
      (fun t => (A ++ y :: B)[(A.length + 1 + t) % (A ++ y :: B).length]?)).length =
      ((B ++ A).map some).length := by simp; omega
  refine List.ext_getElem hlen fun t h1 h2 => ?_
  have ht : t < (B ++ A).length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  have hl : t < (A ++ y :: B).length := by simp at ht ⊢; omega
  have := List.getElem?_rotate (l := A ++ y :: B) (n := A.length + 1) hl
  rw [FW_rot_split, List.getElem?_append_left ht, List.getElem?_eq_getElem ht,
    show t + (A.length + 1) = A.length + 1 + t by omega] at this
  exact this.symm

private theorem FW_pos_left (A B : List PkgLetter) (y : PkgLetter) :
    (List.range ((A ++ y :: B).length - 1)).map
        (fun t => (A ++ y :: B)[(A.length + (A ++ y :: B).length - 1 - t) %
          (A ++ y :: B).length]?) =
      (B ++ A).reverse.map some := by
  have hlen : ((List.range ((A ++ y :: B).length - 1)).map
      (fun t => (A ++ y :: B)[(A.length + (A ++ y :: B).length - 1 - t) %
        (A ++ y :: B).length]?)).length = ((B ++ A).reverse.map some).length := by simp
  refine List.ext_getElem hlen fun t h1 h2 => ?_
  have ht : t < (B ++ A).length := by
    simp only [List.length_map, List.length_reverse] at h2; exact h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse]
  have hk : (B ++ A).length - 1 - t < (B ++ A).length := by omega
  have hl : (B ++ A).length - 1 - t < (A ++ y :: B).length := by
    simp at ht ⊢; omega
  have := List.getElem?_rotate (l := A ++ y :: B) (n := A.length + 1) hl
  rw [FW_rot_split, List.getElem?_append_left hk, List.getElem?_eq_getElem hk] at this
  rw [show A.length + (A ++ y :: B).length - 1 - t = (B ++ A).length - 1 - t + (A.length + 1) by
    simp at ht ⊢; omega]
  exact this.symm

/-- The two sides of `Λ̃_o` in `A Λ̃_o B`, `Λ̃_o ∉ A`: the runs of `B A` and of its reverse. -/
private theorem FW_wside_split (A B : List PkgLetter) (o : Fin 2)
    (hA : PkgLetter.lw (.lamt o) ∉ A) :
    FW_wside (A ++ .lw (.lamt o) :: B) o true = FW_run (B ++ A) ∧
      FW_wside (A ++ .lw (.lamt o) :: B) o false = FW_run (B ++ A).reverse := by
  have hi : (A ++ PkgLetter.lw (.lamt o) :: B).idxOf (.lw (.lamt o)) = A.length := by
    rw [List.idxOf_append_of_notMem hA, List.idxOf_cons_self, Nat.add_zero]
  constructor
  · unfold FW_wside
    simp only [hi, ↓reduceIte]
    rw [← FW_scan_some, ← FW_pos_right A B (.lw (.lamt o))]
    have := FW_scan ((List.range ((A ++ PkgLetter.lw (.lamt o) :: B).length - 1)).map fun t =>
      (A.length + 1 + t) % (A ++ PkgLetter.lw (.lamt o) :: B).length)
      (fun r => (A ++ PkgLetter.lw (.lamt o) :: B)[r]?)
    rw [List.map_map] at this
    exact this
  · unfold FW_wside
    simp only [hi, Bool.false_eq_true, ↓reduceIte]
    rw [← FW_scan_some, ← FW_pos_left A B (.lw (.lamt o))]
    have := FW_scan ((List.range ((A ++ PkgLetter.lw (.lamt o) :: B).length - 1)).map fun t =>
      (A.length + (A ++ PkgLetter.lw (.lamt o) :: B).length - 1 - t) %
        (A ++ PkgLetter.lw (.lamt o) :: B).length)
      (fun r => (A ++ PkgLetter.lw (.lamt o) :: B)[r]?)
    rw [List.map_map] at this
    exact this

/-- A rotation that fixes the head letter, which occurs once, fixes the word. -/
private theorem FW_rot_uniq {α : Type*} (x : α) (X Y : List α) (h : (x :: X) ~r (x :: Y))
    (hx : x ∉ X) : X = Y := by
  obtain ⟨k, hk⟩ := h
  rw [← List.rotate_mod] at hk
  have hlt : k % (x :: X).length < (x :: X).length := Nat.mod_lt _ (by simp)
  rcases hm : k % (x :: X).length with _ | m
  · rw [hm, List.rotate_zero] at hk; exact (List.cons.inj hk).2
  · rw [hm] at hk hlt
    simp only [List.length_cons] at hlt
    rw [List.rotate_eq_drop_append_take (by simp; omega)] at hk
    simp only [List.drop_succ_cons, List.take_succ_cons] at hk
    rw [List.drop_eq_getElem_cons (by omega), List.cons_append] at hk
    exact absurd ((List.cons.inj hk).1 ▸ List.getElem_mem _) hx

/-- The sides of `Λ̃_o` in a word that is a rotation of `Λ̃_o V`, `Λ̃_o ∉ V`. -/
private theorem FW_wside_cyc (w V : List PkgLetter) (o : Fin 2)
    (hw : w ~r (.lw (.lamt o) :: V)) (hV : PkgLetter.lw (.lamt o) ∉ V) :
    FW_wside w o true = FW_run V ∧ FW_wside w o false = FW_run V.reverse := by
  have hmem : PkgLetter.lw (.lamt o) ∈ w := hw.perm.symm.subset List.mem_cons_self
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hmem
  have hc := hw.perm.count_eq (.lw (.lamt o))
  rw [List.count_cons_self, List.count_eq_zero.2 hV, List.count_append,
    List.count_cons_self] at hc
  have hA : PkgLetter.lw (.lamt o) ∉ A := List.count_eq_zero.1 (by omega)
  have hB : PkgLetter.lw (.lamt o) ∉ B := List.count_eq_zero.1 (by omega)
  have hBA : B ++ A = V := by
    refine FW_rot_uniq _ _ _ ((List.isRotated_append.symm.trans hw).symm.trans ?_).symm ?_
    · simp only [List.cons_append]; exact List.IsRotated.refl _
    · simp [hA, hB]
  rw [← hBA]
  exact FW_wside_split A B o hA

/-- Two different members of a list with positive values add up to at least `2`. -/
private theorem FW_two_le {α : Type*} (f : α → ℕ) (a b : α) (hab : a ≠ b) (ha : 1 ≤ f a)
    (hb : 1 ≤ f b) : ∀ L : List α, a ∈ L → b ∈ L → 2 ≤ (L.map f).sum
  | [], h, _ => by simp at h
  | c :: L, h1, h2 => by
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 h1 with e1 | h1'
      · subst e1
        have : b ∈ L := (List.mem_cons.1 h2).resolve_left (Ne.symm hab)
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := f) this)
        omega
      · rcases List.mem_cons.1 h2 with e2 | h2'
        · subst e2
          have := List.le_sum_of_mem (List.mem_map_of_mem (f := f) h1')
          omega
        · have := FW_two_le f a b hab ha hb L h1' h2'
          omega

/-- With at most one `Λ̃_o` in the expression, its side counts are those of the word that holds
it. -/
private theorem FW_lamSide_mem (R : PkgExpr) (o : Fin 2) (right : Bool)
    (hc : (R.loops.map fun w => w.count (.lw (.lamt o))).sum ≤ 1) (w : List PkgLetter)
    (hw : w ∈ R.loops) (ho : PkgLetter.lw (.lamt o) ∈ w) :
    R.lamSide o right = FW_wside w o right := by
  rw [FW_lamSide]
  cases h : R.loops.find? fun w => w.contains (.lw (.lamt o)) with
  | none =>
      exact absurd (List.find?_eq_none.1 h w hw) (by simpa using ho)
  | some w' =>
      have h1 := List.mem_of_find?_eq_some h
      have h2 : PkgLetter.lw (.lamt o) ∈ w' := by simpa using List.find?_some h
      by_contra hne
      have hne' : w' ≠ w := fun e => hne (by subst e; rfl)
      have := FW_two_le (fun w => w.count (.lw (.lamt o))) w' w hne'
        (List.count_pos_iff.2 h2) (List.count_pos_iff.2 ho) R.loops h1 hw
      omega

/-- Under `wf`, each `Λ̃_o` occurs once in the expression. -/
private theorem FW_wf_count (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) :
    (R.loops.map fun w => w.count (.lw (.lamt o))).sum = 1 := by
  simp only [PkgExpr.wf, Bool.and_eq_true, beq_iff_eq] at hR
  fin_cases o
  · exact hR.1.1.1.1
  · exact hR.1.1.1.2

private theorem FW_count_le (R : PkgExpr) (hR : R.wf = true) (o : Fin 2) (w : List PkgLetter)
    (hw : w ∈ R.loops) : w.count (.lw (.lamt o)) ≤ 1 := by
  rw [← FW_wf_count R hR o]
  exact List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count (.lw (.lamt o))) hw)

/-! ### The runs of a side -/

private theorem FW_run_cons (x : PkgLetter) (Z : List PkgLetter) :
    FW_run (x :: Z) = if FW_go x then (if x.isRes then 1 else 0) + FW_run Z else 0 := by
  unfold FW_run
  cases h : FW_go x
  · simp [h]
  · simp only [List.takeWhile_cons, h, ↓reduceIte, List.countP_cons]
    split_ifs <;> omega

private theorem FW_run_nil : FW_run [] = 0 := rfl

/-- The run of `X Z` depends on `Z` only through the run of `Z`. -/
private theorem FW_run_congr (Z Z' : List PkgLetter) (h : FW_run Z = FW_run Z') :
    ∀ X : List PkgLetter, FW_run (X ++ Z) = FW_run (X ++ Z')
  | [] => h
  | x :: X => by
      simp only [List.cons_append, FW_run_cons, FW_run_congr Z Z' h X]

/-- A plain letter: neither `Δ`, `Λ̃` nor a resolvent. -/
private def FW_plain (x : PkgLetter) : Prop := FW_go x = true ∧ x.isRes = false

private theorem FW_run_plain (P : List PkgLetter) (hP : ∀ z ∈ P, FW_plain z) (Z : List PkgLetter) :
    FW_run (P ++ Z) = FW_run Z := by
  induction P with
  | nil => rfl
  | cons x P ih =>
      have hx := hP x List.mem_cons_self
      rw [List.cons_append, FW_run_cons, hx.1, hx.2,
        ih fun z hz => hP z (List.mem_cons_of_mem _ hz)]
      simp

private theorem FW_run_go (s : List PkgLetter) (hs : ∀ z ∈ s, FW_go z = true) (Z : List PkgLetter) :
    FW_run (s ++ Z) = s.countP PkgLetter.isRes + FW_run Z := by
  induction s with
  | nil => simp
  | cons x s ih =>
      rw [List.cons_append, FW_run_cons, hs x List.mem_cons_self,
        ih fun z hz => hs z (List.mem_cons_of_mem _ hz), List.countP_cons]
      split_ifs <;> simp_all; omega

/-! ### The packages of a word as cyclic stretches -/

open private PSh_exists_first_ent pkgSegs_first from RBMTransitionEdge.Localized.Expansion.PkgShape

/-- The first piece of `splitOnP`, and the place of every other piece between separators. -/
private theorem FW_split_struct {α : Type*} (p : α → Bool) : ∀ L : List α,
    ∃ s₀ rest, L.splitOnP p = s₀ :: rest ∧
      (∃ L₂, L = s₀ ++ L₂ ∧ (L₂ = [] ∨ ∃ y L₂', L₂ = y :: L₂' ∧ p y = true)) ∧
      (∀ z ∈ s₀, p z = false) ∧
      ∀ σ ∈ rest, ∃ L₁ L₂, L = L₁ ++ σ ++ L₂ ∧ (∃ L₁' y, L₁ = L₁' ++ [y] ∧ p y = true) ∧
        (L₂ = [] ∨ ∃ y L₂', L₂ = y :: L₂' ∧ p y = true) ∧ ∀ z ∈ σ, p z = false
  | [] => ⟨[], [], by simp, ⟨[], by simp⟩, by simp, by simp⟩
  | x :: L => by
      obtain ⟨s₀, rest, hs, ⟨L₂, hL, hL₂⟩, hs₀, hrest⟩ := FW_split_struct p L
      rw [List.splitOnP_cons_eq_ite_modifyHead, hs]
      cases hx : p x
      · refine ⟨x :: s₀, rest, by simp, ⟨L₂, by simp [hL], hL₂⟩, ?_, fun σ hσ => ?_⟩
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact hx
          · exact hs₀ z hz
        · obtain ⟨L₁, L₂', h1, ⟨L₁', y, rfl, hy⟩, h3, h4⟩ := hrest σ hσ
          exact ⟨x :: (L₁' ++ [y]), L₂', by simp [h1], ⟨x :: L₁', y, by simp, hy⟩, h3, h4⟩
      · refine ⟨[], s₀ :: rest, by simp, ⟨x :: L, by simp, Or.inr ⟨x, L, rfl, hx⟩⟩, by simp,
          fun σ hσ => ?_⟩
        rcases List.mem_cons.1 hσ with rfl | hσ
        · exact ⟨[x], L₂, by simp [hL], ⟨[], x, by simp, hx⟩, hL₂, hs₀⟩
        · obtain ⟨L₁, L₂', h1, ⟨L₁', y, rfl, hy⟩, h3, h4⟩ := hrest σ hσ
          exact ⟨x :: (L₁' ++ [y]), L₂', by simp [h1], ⟨x :: L₁', y, by simp, hy⟩, h3, h4⟩

/-- A piece of `splitOnP` lies between separators or the ends of the list. -/
private theorem FW_split_mem {α : Type*} (p : α → Bool) (L σ : List α)
    (hσ : σ ∈ L.splitOnP p) :
    ∃ L₁ L₂, L = L₁ ++ σ ++ L₂ ∧ (L₁ = [] ∨ ∃ L₁' y, L₁ = L₁' ++ [y] ∧ p y = true) ∧
      (L₂ = [] ∨ ∃ y L₂', L₂ = y :: L₂' ∧ p y = true) ∧ ∀ z ∈ σ, p z = false := by
  obtain ⟨s₀, rest, hs, ⟨L₂, hL, hL₂⟩, hs₀, hrest⟩ := FW_split_struct p L
  rw [hs] at hσ
  rcases List.mem_cons.1 hσ with rfl | hσ
  · exact ⟨[], L₂, by simp [hL], Or.inl rfl, hL₂, hs₀⟩
  · obtain ⟨L₁, L₂', h1, h2, h3, h4⟩ := hrest σ hσ
    exact ⟨L₁, L₂', h1, Or.inr h2, h3, h4⟩

/-- The last piece of `splitOnP` and what precedes it. -/
private theorem FW_split_last {α : Type*} (p : α → Bool) : ∀ l : List α,
    ∃ L sl L₁, l.splitOnP p = L ++ [sl] ∧ l = L₁ ++ sl ∧
      (L₁ = [] ∨ ∃ L₁' y, L₁ = L₁' ++ [y] ∧ p y = true) ∧ ∀ z ∈ sl, p z = false
  | [] => ⟨[], [], [], by simp, by simp, Or.inl rfl, by simp⟩
  | x :: l => by
      obtain ⟨L, sl, L₁, hs, hl, hL₁, hsl⟩ := FW_split_last p l
      have hcnt := (FW_split_count p (fun _ => false) (fun _ _ => rfl) l).2
      rw [hs] at hcnt
      have hsl0 : sl.countP p = 0 := List.countP_eq_zero.2 fun z hz => by simp [hsl z hz]
      rw [List.splitOnP_cons_eq_ite_modifyHead, hs]
      cases hx : p x
      · cases L with
        | nil =>
            have hL₁0 : L₁ = [] := by
              rcases hL₁ with h | ⟨L₁', y, rfl, hy⟩
              · exact h
              · exfalso
                simp only [hl, List.length_singleton, List.nil_append, List.countP_append,
                  List.countP_cons, hy] at hcnt
                simp at hcnt
            subst hL₁0
            refine ⟨[], x :: sl, [], by simp, by simp [hl], Or.inl rfl, fun z hz => ?_⟩
            rcases List.mem_cons.1 hz with rfl | hz
            · exact hx
            · exact hsl z hz
        | cons s L' =>
            rcases hL₁ with rfl | ⟨L₁', y, rfl, hy⟩
            · exfalso
              simp only [hl, List.nil_append, hsl0] at hcnt
              simp at hcnt
            · exact ⟨(x :: s) :: L', sl, x :: (L₁' ++ [y]), by simp, by simp [hl],
                Or.inr ⟨x :: L₁', y, by simp, hy⟩, hsl⟩
      · refine ⟨[] :: L, sl, x :: L₁, by simp, by simp [hl], ?_, hsl⟩
        rcases hL₁ with rfl | ⟨L₁', y, rfl, hy⟩
        · exact Or.inr ⟨[], x, by simp, hx⟩
        · exact Or.inr ⟨x :: L₁', y, by simp, hy⟩

/-- A package of a word with a `Δ` is free of `Δ`, and the word is a rotation of the package
followed by a stretch that starts and ends with a `Δ`. -/
private theorem FW_seg_cyc (w σ : List PkgLetter) (hw : w.any PkgLetter.isEnt = true)
    (hσ : σ ∈ pkgSegs w) :
    (∀ z ∈ σ, z.isEnt = false) ∧ ∃ M, w ~r (σ ++ M) ∧ (∃ u v M₁, M = .ent u v :: M₁) ∧
      (∃ u v M₂, M = M₂ ++ [.ent u v]) := by
  obtain ⟨P, x, y, Q, hP, rfl⟩ := PSh_exists_first_ent w hw
  rw [pkgSegs_first P Q x y hP] at hσ
  obtain ⟨L₁, L₂, hL, h1, h2, h3⟩ := FW_split_mem _ _ _ hσ
  refine ⟨h3, L₂ ++ .ent x y :: L₁, ?_, ?_, ?_⟩
  · have e1 : P ++ .ent x y :: Q ~r (.ent x y :: Q) ++ P := List.isRotated_append
    refine e1.trans ?_
    rw [List.cons_append, hL]
    have e2 : PkgLetter.ent x y :: (L₁ ++ σ ++ L₂) = (.ent x y :: L₁) ++ (σ ++ L₂) := by simp
    rw [e2]
    refine List.isRotated_append.trans ?_
    simp only [List.append_assoc]
    exact List.IsRotated.refl _
  · rcases h2 with rfl | ⟨z, L₂', rfl, hz⟩
    · exact ⟨x, y, L₁, by simp⟩
    · rcases z with _ | ⟨u, v⟩
      · simp [PkgLetter.isEnt] at hz
      · exact ⟨u, v, L₂' ++ .ent x y :: L₁, by simp⟩
  · rcases h1 with rfl | ⟨L₁', z, rfl, hz⟩
    · exact ⟨x, y, L₂, by simp⟩
    · rcases z with _ | ⟨u, v⟩
      · simp [PkgLetter.isEnt] at hz
      · exact ⟨u, v, L₂ ++ .ent x y :: L₁', by simp⟩

private theorem FW_go_ent (u v : ℕ) (Z : List PkgLetter) : FW_run (.ent u v :: Z) = 0 := by
  rw [FW_run_cons]; rfl

private theorem FW_go_lam (y : PkgLetter) (hy : y.isLam = true) (Z : List PkgLetter) :
    FW_run (y :: Z) = 0 := by
  rw [FW_run_cons]; simp [FW_go, hy]

/-- The parts of a list read at two consecutive pieces of `splitOnP`. -/
private theorem FW_getD_two (f : List PkgLetter → ℕ) (L : List (List PkgLetter))
    (a b : List PkgLetter) (R : List (List PkgLetter)) :
    ((L ++ [a] ++ b :: R).map f).getD L.length 0 = f a ∧
      ((L ++ [a] ++ b :: R).map f).getD (L.length + 1) 0 = f b := by
  constructor
  · rw [List.getD_eq_getElem _ _ (by simp)]; simp
  · rw [List.getD_eq_getElem _ _ (by simp)]
    simp [List.getElem_append_right]

/-- The sides of `Λ̃_o` are the parts of its segment on either side of it. -/
theorem pkg_pents_sides (X : PkgExpr) (hX : X.wf = true) (e : ℕ × ℕ × List PkgLetter)
    (he : e ∈ X.pents) (o : Fin 2) (ho : PkgLetter.lw (.lamt o) ∈ e.2.2) :
    (pkgParts e.2.2).getD ((e.2.2.takeWhile fun x => x != .lw (.lamt o)).countP PkgLetter.isLam)
        0 = X.lamSide o false ∧
      (pkgParts e.2.2).getD
        ((e.2.2.takeWhile fun x => x != .lw (.lamt o)).countP PkgLetter.isLam + 1) 0 =
        X.lamSide o true := by
  obtain ⟨w, hwL, hwE, hσ⟩ := FW_mem_pents X e he
  obtain ⟨hσE, M, hrot, ⟨u, v, M₁, hM₁⟩, ⟨u', v', M₂, hM₂⟩⟩ := FW_seg_cyc w e.2.2 hwE hσ
  obtain ⟨σ₁, σ₂, hσeq⟩ := List.append_of_mem ho
  have hc1 := FW_count_le X hX o w hwL
  have hcw := hrot.perm.count_eq (.lw (.lamt o))
  rw [hσeq] at hcw
  simp only [List.count_append, List.count_cons_self] at hcw
  have h1 : PkgLetter.lw (.lamt o) ∉ σ₁ := List.count_eq_zero.1 (by omega)
  have h2 : PkgLetter.lw (.lamt o) ∉ σ₂ := List.count_eq_zero.1 (by omega)
  have h3 : PkgLetter.lw (.lamt o) ∉ M := List.count_eq_zero.1 (by omega)
  have hmem : PkgLetter.lw (.lamt o) ∈ w := hrot.perm.symm.subset (by rw [hσeq]; simp)
  have hsum := (FW_wf_count X hX o).le
  rw [FW_lamSide_mem X o false hsum w hwL hmem, FW_lamSide_mem X o true hsum w hwL hmem]
  have hcyc : w ~r (.lw (.lamt o) :: (σ₂ ++ M ++ σ₁)) := by
    refine hrot.trans ?_
    rw [hσeq]
    have e1 : σ₁ ++ PkgLetter.lw (.lamt o) :: σ₂ ++ M = σ₁ ++ (.lw (.lamt o) :: (σ₂ ++ M)) := by
      simp
    rw [e1]
    refine List.isRotated_append.trans ?_
    simp only [List.cons_append, List.append_assoc]
    exact List.IsRotated.refl _
  obtain ⟨hR, hL⟩ := FW_wside_cyc w _ o hcyc (by simp [h1, h2, h3])
  rw [hR, hL]
  have htw : e.2.2.takeWhile (fun x => x != .lw (.lamt o)) = σ₁ := by
    rw [hσeq, List.takeWhile_append_of_pos (fun a ha => by
      simp only [bne_iff_ne, ne_eq]; rintro rfl; exact h1 ha), List.takeWhile_cons_of_neg (by simp)]
    simp
  rw [htw]
  unfold pkgParts
  rw [hσeq, List.splitOnP_append_cons _ _ (rfl : PkgLetter.isLam (.lw (.lamt o)) = true)]
  obtain ⟨Ls, sl, L₁, hs1, hσ₁, hL₁, hsl⟩ := FW_split_last PkgLetter.isLam σ₁
  have hlen : Ls.length = σ₁.countP PkgLetter.isLam := by
    have := (FW_split_count PkgLetter.isLam (fun _ => false) (fun _ _ => rfl) σ₁).2
    rw [hs1] at this; simpa using this
  obtain ⟨s₀, rest, hs2, ⟨L₂, hσ₂, hL₂⟩, hs₀, -⟩ := FW_split_struct PkgLetter.isLam σ₂
  rw [hs1, hs2, ← hlen]
  obtain ⟨hg1, hg2⟩ := FW_getD_two (fun s => s.countP PkgLetter.isRes) Ls sl s₀ rest
  rw [hg1, hg2]
  have hgo : ∀ z ∈ e.2.2, z.isLam = false → FW_go z = true := fun z hz hl => by
    simp [FW_go, hσE z hz, hl]
  rw [hσeq] at hgo
  constructor
  · rw [hσ₁]
    simp only [List.reverse_append, List.append_assoc]
    rw [FW_run_go _ (fun z hz => hgo z (by simp [hσ₁, List.mem_reverse.1 hz])
        (hsl z (List.mem_reverse.1 hz))), List.countP_reverse]
    suffices FW_run (L₁.reverse ++ (M.reverse ++ σ₂.reverse)) = 0 by rw [this, Nat.add_zero]
    rcases hL₁ with rfl | ⟨L₁', y, rfl, hy⟩
    · rw [hM₂]; simp [FW_go_ent]
    · simp [FW_go_lam y hy]
  · rw [hσ₂]
    simp only [List.append_assoc]
    rw [FW_run_go _ (fun z hz => hgo z (by simp [hσ₂, hz]) (hs₀ z hz))]
    suffices FW_run (L₂ ++ (M ++ σ₁)) = 0 by rw [this, Nat.add_zero]
    rcases hL₂ with rfl | ⟨y, L₂', rfl, hy⟩
    · rw [hM₁]; simp [FW_go_ent]
    · simp [FW_go_lam y hy]

/-- The `Λ̃` and the side chosen by the branches of `ffocus`. -/
def PkgExpr.ffocusSide (R : PkgExpr) : Option (Fin 2 × Bool) :=
  let ℓ₂ := R.loops.findIdx fun w => w.contains (.lw (.lamt 1))
  let ℓ₁ := R.loops.findIdx fun w => w.contains (.lw (.lamt 0))
  match R.loops[ℓ₂]?, R.loops[ℓ₁]? with
  | some w₂, some w₁ =>
    let i₂ := w₂.idxOf (.lw (.lamt 1))
    let i₁ := w₁.idxOf (.lw (.lamt 0))
    if w₂.any (fun x => match x with | .ent _ _ => true | _ => false) then
      match pkgSeek w₂ i₂ true with
      | some _ => some (1, true)
      | none => match pkgSeek w₁ i₁ true with
        | some _ => some (0, true)
        | none => match pkgSeek w₂ i₂ false with
          | some _ => some (1, false)
          | none => none
    else
      match pkgSeek w₂ i₂ false with
      | some _ => some (1, false)
      | none => match pkgSeek w₁ i₁ true with
        | some _ => some (0, true)
        | none => none
  | _, _ => none

/-! ### The branches of `ffocus` -/

private theorem FW_findIdx_mem (L : List (List PkgLetter)) (o : Fin 2) (w : List PkgLetter)
    (h : L[L.findIdx fun w => w.contains (.lw (.lamt o))]? = some w) :
    PkgLetter.lw (.lamt o) ∈ w := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 h
  have := List.findIdx_getElem (w := hlt)
  simpa using this

/-- The branch of `ffocus`: its word holds `Λ̃_o`, its resolvent is the first one found by
`pkgSeek` on its side, and `ffocusSide` names `o` and that side. -/
private theorem FW_focus (R : PkgExpr) (ℓ r : ℕ) (b : Bool) (h : R.ffocus = some (ℓ, r, b)) :
    ∃ o w, R.loops[ℓ]? = some w ∧ PkgLetter.lw (.lamt o) ∈ w ∧
      pkgSeek w (w.idxOf (.lw (.lamt o))) b = some r ∧ R.ffocusSide = some (o, b) := by
  unfold PkgExpr.ffocus at h
  unfold PkgExpr.ffocusSide
  rcases h₂ : R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt 1))]? with _ | w₂ <;>
    rcases h₁ : R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt 0))]? with _ | w₁ <;>
    simp only [h₂, h₁, reduceCtorEq] at h ⊢
  have m₂ := FW_findIdx_mem R.loops 1 w₂ h₂
  have m₁ := FW_findIdx_mem R.loops 0 w₁ h₁
  by_cases hE : w₂.any PkgLetter.isEnt = true
  · rw [ite_eq_left (by exact hE)] at h
    rw [ite_eq_left (by exact hE)]
    rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) true with _ | r₁ <;>
      simp only [s1, Option.some.injEq, Prod.mk.injEq] at h ⊢
    · rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂ <;>
        simp only [s2, Option.some.injEq, Prod.mk.injEq] at h ⊢
      · rcases s3 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₃ <;>
          simp only [s3, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨1, w₂, h₂, m₂, s3, rfl, rfl⟩
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨0, w₁, h₁, m₁, s2, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨1, w₂, h₂, m₂, s1, rfl, rfl⟩
  · rw [ite_eq_right (by exact hE)] at h
    rw [ite_eq_right (by exact hE)]
    rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₁ <;>
      simp only [s1, Option.some.injEq, Prod.mk.injEq] at h ⊢
    · rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂ <;>
        simp only [s2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨0, w₁, h₁, m₁, s2, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨1, w₂, h₂, m₂, s1, rfl, rfl⟩

private theorem FW_focus_none (R : PkgExpr) (h : R.ffocus = none) : R.ffocusSide = none := by
  unfold PkgExpr.ffocus at h
  unfold PkgExpr.ffocusSide
  rcases h₂ : R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt 1))]? with _ | w₂ <;>
    rcases h₁ : R.loops[R.loops.findIdx fun w => w.contains (.lw (.lamt 0))]? with _ | w₁ <;>
    simp only [h₂, h₁] at h ⊢
  by_cases hE : w₂.any PkgLetter.isEnt = true
  · rw [ite_eq_left (by exact hE)] at h
    rw [ite_eq_left (by exact hE)]
    rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) true with _ | r₁ <;>
      rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂ <;>
      rcases s3 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₃ <;>
      simp only [s1, s2, s3, reduceCtorEq] at h ⊢
  · rw [ite_eq_right (by exact hE)] at h
    rw [ite_eq_right (by exact hE)]
    rcases s1 : pkgSeek w₂ (w₂.idxOf (.lw (.lamt 1))) false with _ | r₁ <;>
      rcases s2 : pkgSeek w₁ (w₁.idxOf (.lw (.lamt 0))) true with _ | r₂ <;>
      simp only [s1, s2, reduceCtorEq] at h ⊢

/-- `ffocusSide` is defined iff `ffocus` is, with the same side. -/
theorem pkg_ffocusSide (R : PkgExpr) :
    R.ffocusSide.isSome = R.ffocus.isSome ∧
      ∀ ℓ r right, R.ffocus = some (ℓ, r, right) → ∃ o, R.ffocusSide = some (o, right) := by
  refine ⟨?_, fun ℓ r right h => ?_⟩
  · cases h : R.ffocus with
    | none => rw [FW_focus_none R h]; rfl
    | some f =>
        obtain ⟨ℓ, r, b⟩ := f
        obtain ⟨o, -, -, -, -, hs⟩ := FW_focus R ℓ r b h
        rw [hs]; rfl
  · obtain ⟨o, -, -, -, -, hs⟩ := FW_focus R ℓ r right h
    exact ⟨o, hs⟩

/-! ### The resolvent found by `pkgSeek` -/

/-- The scan of `pkgSeek` on the letters it visits: the first resolvent after a plain stretch. -/
private theorem FW_seek_gen (w : List PkgLetter) (pos : ℕ → ℕ) (Vb : List PkgLetter)
    (hmap : (List.range (w.length - 1)).map (fun t => w[pos t]?) = Vb.map some) (r : ℕ)
    (h : (((List.range (w.length - 1)).map pos).takeWhile fun r => FW_goO w[r]?).find?
      (fun r => FW_resO w[r]?) = some r) :
    ∃ P x Q, Vb = P ++ x :: Q ∧ (∀ z ∈ P, FW_plain z) ∧ x.isRes = true ∧
      r = pos P.length ∧ P.length < w.length - 1 := by
  obtain ⟨hr, as, bs, hT, has⟩ := List.find?_eq_some_iff_append.1 h
  have hmap' : ((List.range (w.length - 1)).map pos).map (fun r => w[r]?) = Vb.map some := by
    rw [List.map_map]; exact hmap
  have hT2 : (Vb.takeWhile FW_go).map some =
      as.map (fun r => w[r]?) ++ w[r]? :: bs.map (fun r => w[r]?) := by
    have e1 := List.takeWhile_map (f := fun r => w[r]?) (p := FW_goO)
      (l := (List.range (w.length - 1)).map pos)
    rw [hmap', List.takeWhile_map, FW_goO_some] at e1
    rw [e1]
    change ((((List.range (w.length - 1)).map pos).takeWhile fun r => FW_goO w[r]?).map
      fun r => w[r]?) = _
    rw [hT]; simp
  obtain ⟨l₁, l₂, hsplit, hl₁, hl₂⟩ := List.map_eq_append_iff.1 hT2
  obtain ⟨x, l₃, rfl, hx, -⟩ := List.map_eq_cons_iff.1 hl₂
  have hlen : l₁.length = as.length := by simpa using congrArg List.length hl₁
  have hpre : (List.range (w.length - 1)).map pos =
      as ++ r :: (bs ++ ((List.range (w.length - 1)).map pos).dropWhile
        (fun r => FW_goO w[r]?)) := by
    conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun r => FW_goO w[r]?)
      (l := (List.range (w.length - 1)).map pos)]
    rw [hT]; simp
  refine ⟨l₁, x, l₃ ++ Vb.dropWhile FW_go, ?_, fun z hz => ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.takeWhile_append_dropWhile (p := FW_go) (l := Vb)]
    rw [hsplit]; simp
  · have hz1 : z ∈ Vb.takeWhile FW_go := by rw [hsplit]; simp [hz]
    refine ⟨List.mem_takeWhile_imp hz1, ?_⟩
    have : some z ∈ as.map (fun r => w[r]?) := by rw [← hl₁]; exact List.mem_map_of_mem hz
    obtain ⟨a, ha, hga⟩ := List.mem_map.1 this
    have h1 := has a ha
    rw [hga] at h1
    have e := congrFun FW_resO_some z
    simp only [Function.comp] at e
    rw [← e]; simpa using h1
  · have e := congrFun FW_resO_some x
    simp only [Function.comp] at e
    rw [← e, hx]; exact hr
  · have hlt : as.length < ((List.range (w.length - 1)).map pos).length := by
      rw [hpre]; simp
    have hget : ((List.range (w.length - 1)).map pos)[as.length]? = some r := by
      rw [hpre]; simp
    rw [List.length_map, List.length_range] at hlt
    rw [List.getElem?_map, List.getElem?_range hlt] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    exact ⟨by rw [hlen]; exact hget.symm, by rw [hlen]; exact hlt⟩

/-- The resolvent of `pkgSeek` to the right of position `|A|` in `A y B`. -/
private theorem FW_seek_right (A B : List PkgLetter) (y : PkgLetter) (r : ℕ)
    (h : pkgSeek (A ++ y :: B) A.length true = some r) :
    ∃ P x Q, B ++ A = P ++ x :: Q ∧ (∀ z ∈ P, FW_plain z) ∧ x.isRes = true ∧
      (A ++ y :: B).rotate r = x :: (Q ++ y :: P) := by
  unfold pkgSeek at h
  simp only [↓reduceIte] at h
  obtain ⟨P, x, Q, hV, hP, hx, hr, -⟩ := FW_seek_gen _
    (fun t => (A.length + 1 + t) % (A ++ y :: B).length) (B ++ A) (FW_pos_right A B y) r h
  refine ⟨P, x, Q, hV, hP, hx, ?_⟩
  rw [hr, List.rotate_mod, ← List.rotate_rotate, FW_rot_split, hV]
  have := List.rotate_append_length_eq P (x :: (Q ++ [y]))
  simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
  rw [this]

/-- The resolvent of `pkgSeek` to the left of position `|A|` in `A y B`. -/
private theorem FW_seek_left (A B : List PkgLetter) (y : PkgLetter) (r : ℕ)
    (h : pkgSeek (A ++ y :: B) A.length false = some r) :
    ∃ P x Q, (B ++ A).reverse = P ++ x :: Q ∧ (∀ z ∈ P, FW_plain z) ∧ x.isRes = true ∧
      (A ++ y :: B).rotate r = x :: (P.reverse ++ y :: Q.reverse) := by
  unfold pkgSeek at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨P, x, Q, hV, hP, hx, hr, hlt⟩ := FW_seek_gen _
    (fun t => (A.length + (A ++ y :: B).length - 1 - t) % (A ++ y :: B).length)
    (B ++ A).reverse (FW_pos_left A B y) r h
  refine ⟨P, x, Q, hV, hP, hx, ?_⟩
  have hV' : B ++ A = Q.reverse ++ x :: P.reverse := by
    have := congrArg List.reverse hV
    simpa using this
  have hl := congrArg List.length hV'
  simp only [List.length_append, List.length_cons, List.length_reverse] at hl hlt
  rw [hr, show A.length + (A ++ y :: B).length - 1 - P.length = A.length + 1 + Q.reverse.length by
    simp only [List.length_append, List.length_cons, List.length_reverse]; omega,
    List.rotate_mod, ← List.rotate_rotate, FW_rot_split, hV']
  have := List.rotate_append_length_eq Q.reverse (x :: (P.reverse ++ [y]))
  simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
  rw [this]

/-! ### The sides after `fpkg` -/

open private sum_map_set from RBMTransitionEdge.Localized.Expansion.PkgShape

/-- Replacing the word `w` at position `ℓ` by a word `w'` with the same letters `Λ̃`: the sides of a
`Λ̃_o` of `w` are read in `w'`, the sides of every other `Λ̃_o` are kept. -/
private theorem FW_lamSide_set (R R' : PkgExpr) (hR : R.wf = true) (ℓ : ℕ) (w w' : List PkgLetter)
    (hw : R.loops[ℓ]? = some w) (hR' : R'.loops = R.loops.set ℓ w')
    (hc : ∀ o : Fin 2, w'.count (.lw (.lamt o)) = w.count (.lw (.lamt o))) (o : Fin 2)
    (side : Bool) :
    (PkgLetter.lw (.lamt o) ∈ w → R'.lamSide o side = FW_wside w' o side ∧
        R.lamSide o side = FW_wside w o side) ∧
      (PkgLetter.lw (.lamt o) ∉ w → R'.lamSide o side = R.lamSide o side) := by
  have hsum : (R'.loops.map fun w => w.count (.lw (.lamt o))).sum = 1 := by
    have := sum_map_set (fun w => w.count (PkgLetter.lw (.lamt o))) R.loops ℓ w w' hw
    rw [← hR', hc o, FW_wf_count R hR o] at this
    omega
  have hwL : w ∈ R.loops := List.mem_of_getElem? hw
  have hlt : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hw'L : w' ∈ R'.loops := by
    have h1 : (R.loops.set ℓ w')[ℓ]? = some w' := by simp [hlt]
    rw [hR']; exact List.mem_of_getElem? h1
  refine ⟨fun ho => ⟨?_, ?_⟩, fun ho => ?_⟩
  · exact FW_lamSide_mem R' o side hsum.le w' hw'L (List.count_pos_iff.1 (by
      rw [hc o]; exact List.count_pos_iff.2 ho))
  · exact FW_lamSide_mem R o side (FW_wf_count R hR o).le w hwL ho
  · obtain ⟨u, huL, hu⟩ : ∃ u ∈ R.loops, PkgLetter.lw (.lamt o) ∈ u := by
      by_contra hne
      simp only [not_exists, not_and] at hne
      have : (R.loops.map fun w => w.count (.lw (.lamt o))).sum = 0 :=
        List.sum_eq_zero fun n hn => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hn
          exact List.count_eq_zero.2 (hne v hv)
      rw [FW_wf_count R hR o] at this
      exact absurd this one_ne_zero
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 huL
    have hjℓ : ℓ ≠ j := by
      rintro rfl
      rw [hw] at hj
      exact ho (Option.some.inj hj ▸ hu)
    have huR' : u ∈ R'.loops := by
      rw [hR']; exact List.mem_of_getElem? (by rw [List.getElem?_set_ne hjℓ]; exact hj)
    rw [FW_lamSide_mem R' o side hsum.le u huR' hu,
      FW_lamSide_mem R o side (FW_wf_count R hR o).le u huL hu]

private theorem FW_rot_swap {α : Type*} (w A B C : List α) (h : w ~r (A ++ B)) (e : B ++ A = C) :
    w ~r C := e ▸ h.trans List.isRotated_append

private theorem FW_run_res (a : Fin 2) (Z : List PkgLetter) :
    FW_run (.lw (.res a) :: Z) = 1 + FW_run Z := by
  rw [FW_run_cons]; rfl

private theorem FW_run_det (a : Fin 2) (Z : List PkgLetter) :
    FW_run (.lw (.det a) :: Z) = FW_run Z := by
  rw [FW_run_cons]; simp [FW_go, PkgLetter.isEnt, PkgLetter.isLam, PkgLetter.isRes]

private theorem FW_plain_lam (P : List PkgLetter) (hP : ∀ z ∈ P, FW_plain z) (o : Fin 2) :
    PkgLetter.lw (.lamt o) ∉ P := fun h => by
  have := (hP _ h).1
  simp [FW_go, PkgLetter.isLam] at this

/-- The sides after `fpkg` with the focus to the right of `Λ̃_q`: `w` is a rotation of
`Λ̃_q P 𝒢_a Q` and the new word a rotation of `Λ̃_q P 𝔐_a Δ 𝒢_a Q`, `P` plain. -/
private theorem FW_shape (w w' P Q : List PkgLetter) (q a : Fin 2) (u v : ℕ)
    (hP : ∀ z ∈ P, FW_plain z)
    (hw : w ~r (.lw (.lamt q) :: (P ++ .lw (.res a) :: Q)))
    (hw' : w' ~r (.lw (.lamt q) :: (P ++ .lw (.det a) :: .ent u v :: .lw (.res a) :: Q)))
    (hc : ∀ o : Fin 2, w.count (.lw (.lamt o)) ≤ 1) (o : Fin 2) (side : Bool)
    (ho : PkgLetter.lw (.lamt o) ∈ w) :
    FW_wside w' o side = if (q, true) = (o, side) then 0 else FW_wside w o side := by
  have hcq := hw.perm.count_eq (.lw (.lamt q))
  have hq := hc q
  rw [List.count_cons_self] at hcq
  have hqU : PkgLetter.lw (.lamt q) ∉ P ++ .lw (.res a) :: Q := List.count_eq_zero.1 (by omega)
  have hqQ : PkgLetter.lw (.lamt q) ∉ Q := fun h => hqU (by simp [h])
  have hPr : ∀ z ∈ P.reverse, FW_plain z := fun z hz => hP z (List.mem_reverse.1 hz)
  by_cases hoq : o = q
  · subst hoq
    obtain ⟨h1, h2⟩ := FW_wside_cyc w _ o hw hqU
    obtain ⟨h3, h4⟩ := FW_wside_cyc w' _ o hw' (by simp [FW_plain_lam P hP o, hqQ])
    cases side
    · simp only [h2, h4, Prod.mk.injEq, Bool.true_eq_false, and_false, ↓reduceIte,
        List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      refine FW_run_congr _ _ ?_ Q.reverse
      have e := FW_run_plain _ hPr []
      rw [List.append_nil, FW_run_nil] at e
      rw [FW_run_res, FW_run_res, FW_go_ent, e]
    · rw [h3, ite_eq_left rfl, FW_run_plain _ hP, FW_run_det, FW_go_ent]
  · have hne : (q, true) ≠ (o, side) := fun h => hoq (Prod.mk.inj h).1.symm
    rw [ite_eq_right hne]
    have hoU : PkgLetter.lw (.lamt o) ∈ Q := by
      have := hw.perm.subset ho
      simp only [List.mem_cons, List.mem_append, PkgLetter.lw.injEq, LoopLetter.lamt.injEq,
        reduceCtorEq, false_or] at this
      rcases this with h | h | h
      · exact absurd h hoq
      · exact absurd h (FW_plain_lam P hP o)
      · exact h
    obtain ⟨Q₁, Q₂, rfl⟩ := List.append_of_mem hoU
    have r1 : w ~r (.lw (.lamt o) :: (Q₂ ++ .lw (.lamt q) :: (P ++ .lw (.res a) :: Q₁))) :=
      FW_rot_swap _ (.lw (.lamt q) :: (P ++ .lw (.res a) :: Q₁)) (.lw (.lamt o) :: Q₂) _
        (by simpa using hw) (by simp)
    have r2 : w' ~r (.lw (.lamt o) :: (Q₂ ++ .lw (.lamt q) ::
        (P ++ .lw (.det a) :: .ent u v :: .lw (.res a) :: Q₁))) :=
      FW_rot_swap _ (.lw (.lamt q) :: (P ++ .lw (.det a) :: .ent u v :: .lw (.res a) :: Q₁))
        (.lw (.lamt o) :: Q₂) _ (by simpa using hw') (by simp)
    have hco := r1.perm.count_eq (.lw (.lamt o))
    have hoo := hc o
    rw [List.count_cons_self] at hco
    have hoV : PkgLetter.lw (.lamt o) ∉ Q₂ ++ .lw (.lamt q) :: (P ++ .lw (.res a) :: Q₁) :=
      List.count_eq_zero.1 (by omega)
    have hoV' : PkgLetter.lw (.lamt o) ∉ Q₂ ++ .lw (.lamt q) ::
        (P ++ .lw (.det a) :: .ent u v :: .lw (.res a) :: Q₁) := by
      simp only [List.mem_append, List.mem_cons, not_or] at hoV ⊢
      refine ⟨hoV.1, hoV.2.1, hoV.2.2.1, by simp, by simp, hoV.2.2.2⟩
    obtain ⟨h1, h2⟩ := FW_wside_cyc w _ o r1 hoV
    obtain ⟨h3, h4⟩ := FW_wside_cyc w' _ o r2 hoV'
    cases side
    · rw [h2, h4]
      simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      refine FW_run_congr _ _ ?_ Q₁.reverse
      rw [FW_run_res, FW_run_res, FW_go_ent, FW_run_plain _ hPr, FW_go_lam _ rfl]
    · rw [h1, h3]
      refine FW_run_congr _ _ ?_ Q₂
      rw [FW_go_lam _ rfl, FW_go_lam _ rfl]

/-- Reversing a word swaps the two sides of its `Λ̃_o`. -/
private theorem FW_wside_rev (u : List PkgLetter) (o : Fin 2) (hu : PkgLetter.lw (.lamt o) ∈ u)
    (hc : u.count (.lw (.lamt o)) ≤ 1) (side : Bool) :
    FW_wside u.reverse o side = FW_wside u o (!side) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hu
  rw [List.count_append, List.count_cons_self] at hc
  have hA : PkgLetter.lw (.lamt o) ∉ A := List.count_eq_zero.1 (by omega)
  have hB : PkgLetter.lw (.lamt o) ∉ B := List.count_eq_zero.1 (by omega)
  have r1 : (A ++ .lw (.lamt o) :: B) ~r (.lw (.lamt o) :: (B ++ A)) :=
    FW_rot_swap _ A (.lw (.lamt o) :: B) _ (List.IsRotated.refl _) (by simp)
  have r2 : (A ++ .lw (.lamt o) :: B).reverse ~r (.lw (.lamt o) :: (B ++ A).reverse) :=
    FW_rot_swap _ (B ++ A).reverse [.lw (.lamt o)] _ (by simpa using r1.reverse) (by simp)
  have hV : PkgLetter.lw (.lamt o) ∉ B ++ A := by simp [hA, hB]
  obtain ⟨h1, h2⟩ := FW_wside_cyc _ _ o r1 hV
  obtain ⟨h3, h4⟩ := FW_wside_cyc _ _ o r2 (by simp [hA, hB])
  cases side
  · rw [Bool.not_false, h4, h1, List.reverse_reverse]
  · rw [Bool.not_true, h3, h2]

/-- Q3 (c1): `fpkg` empties the side of the focus and keeps every other side. -/
theorem pkg_fpkg_lamSide (R : PkgExpr) (hR : R.wf = true) (hf : R.ffocus.isSome = true)
    (o : Fin 2) (side : Bool) :
    R.fpkg.lamSide o side = if R.ffocusSide = some (o, side) then 0 else R.lamSide o side := by
  obtain ⟨⟨ℓ, r, b⟩, hfoc⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨q, w, hw, hqw, hseek, hside⟩ := FW_focus R ℓ r b hfoc
  simp only [hside, Option.some.injEq]
  have hwL : w ∈ R.loops := List.mem_of_getElem? hw
  have hc : ∀ o : Fin 2, w.count (.lw (.lamt o)) ≤ 1 := fun o => FW_count_le R hR o w hwL
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hqw
  have hcq := hc q
  rw [List.count_append, List.count_cons_self] at hcq
  have hA : PkgLetter.lw (.lamt q) ∉ A := List.count_eq_zero.1 (by omega)
  have hi : (A ++ PkgLetter.lw (.lamt q) :: B).idxOf (.lw (.lamt q)) = A.length := by
    rw [List.idxOf_append_of_notMem hA, List.idxOf_cons_self, Nat.add_zero]
  rw [hi] at hseek
  have hwrot : (A ++ PkgLetter.lw (.lamt q) :: B) ~r (.lw (.lamt q) :: (B ++ A)) :=
    FW_rot_swap _ A (.lw (.lamt q) :: B) _ (List.IsRotated.refl _) (by simp)
  have hfp : ∀ (a : Fin 2) (tl : List PkgLetter),
      (A ++ PkgLetter.lw (.lamt q) :: B).rotate r = .lw (.res a) :: tl →
      R.fpkg.loops = R.loops.set ℓ ((if b then .lw (.res a) :: tl ++ [.lw (.det a)]
        else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2]) := by
    intro a tl hrot
    unfold PkgExpr.fpkg
    rw [hfoc]
    simp only
    rw [hw]
    simp only
    rw [hrot]
  cases b
  · obtain ⟨P, x, Q, hV, hP, hx, hrot⟩ := FW_seek_left A B _ r hseek
    obtain ⟨a, rfl⟩ : ∃ a, x = .lw (.res a) := by
      rcases x with ((a | a | y | o') | ⟨u, v⟩) <;> simp_all [PkgLetter.isRes]
    have hfp' := hfp a _ hrot
    simp only [Bool.false_eq_true, ↓reduceIte] at hfp'
    set w' : List PkgLetter := (.lw (.det a) :: (P.reverse ++ .lw (.lamt q) :: Q.reverse) ++
      [.lw (.res a)]) ++ [.ent 3 2] with hw'
    have hBA : B ++ A = Q.reverse ++ .lw (.res a) :: P.reverse := by
      have := congrArg List.reverse hV
      simpa using this
    have hcount : ∀ o : Fin 2, w'.count (.lw (.lamt o)) =
        (A ++ PkgLetter.lw (.lamt q) :: B).count (.lw (.lamt o)) := by
      intro o'
      rw [hwrot.perm.count_eq, hBA, hw']
      simp [List.count_append, List.count_cons]
      omega
    have r1 : (A ++ PkgLetter.lw (.lamt q) :: B).reverse ~r
        (.lw (.lamt q) :: (P ++ .lw (.res a) :: Q)) := by
      have := hwrot.reverse
      rw [List.reverse_cons, hV] at this
      exact FW_rot_swap _ _ [.lw (.lamt q)] _ this (by simp)
    have r2 : w'.reverse ~r
        (.lw (.lamt q) :: (P ++ .lw (.det a) :: .ent 3 2 :: .lw (.res a) :: Q)) :=
      FW_rot_swap _ (.ent 3 2 :: .lw (.res a) :: Q) (.lw (.lamt q) :: (P ++ [.lw (.det a)])) _
        (by
          simp only [hw', List.cons_append, List.append_assoc, List.reverse_append,
            List.reverse_cons, List.reverse_reverse, List.nil_append, List.reverse_nil]
          exact List.IsRotated.refl _) (by simp)
    obtain ⟨hin, hout⟩ := FW_lamSide_set R R.fpkg hR ℓ _ w' hw hfp' hcount o side
    by_cases ho : PkgLetter.lw (.lamt o) ∈ A ++ PkgLetter.lw (.lamt q) :: B
    · obtain ⟨e1, e2⟩ := hin ho
      have hcr : ∀ o : Fin 2,
          (A ++ PkgLetter.lw (.lamt q) :: B).reverse.count (.lw (.lamt o)) ≤ 1 :=
        fun o => by rw [List.count_reverse]; exact hc o
      have ho' : PkgLetter.lw (.lamt o) ∈ w' := List.count_pos_iff.1 (by
        rw [hcount o]; exact List.count_pos_iff.2 ho)
      rw [e1, e2, ← List.reverse_reverse w', FW_wside_rev _ o (by simpa using ho')
        (by rw [List.count_reverse, hcount o]; exact hc o),
        FW_shape _ _ P Q q a 3 2 hP r1 r2 hcr o (!side) (List.mem_reverse.2 ho),
        FW_wside_rev _ o ho (hc o), Bool.not_not]
      cases side <;> simp
    · have hoq : o ≠ q := fun h => ho (h ▸ hqw)
      rw [hout ho, ite_eq_right (fun h => hoq (Prod.mk.inj h).1.symm)]
  · obtain ⟨P, x, Q, hV, hP, hx, hrot⟩ := FW_seek_right A B _ r hseek
    obtain ⟨a, rfl⟩ : ∃ a, x = .lw (.res a) := by
      rcases x with ((a | a | y | o') | ⟨u, v⟩) <;> simp_all [PkgLetter.isRes]
    have hfp' := hfp a _ hrot
    simp only [↓reduceIte] at hfp'
    set w' : List PkgLetter := (.lw (.res a) :: (Q ++ .lw (.lamt q) :: P) ++
      [.lw (.det a)]) ++ [.ent 3 2] with hw'
    have hcount : ∀ o : Fin 2, w'.count (.lw (.lamt o)) =
        (A ++ PkgLetter.lw (.lamt q) :: B).count (.lw (.lamt o)) := by
      intro o'
      rw [hwrot.perm.count_eq, hV, hw']
      simp [List.count_append, List.count_cons]
      omega
    have r1 : (A ++ PkgLetter.lw (.lamt q) :: B) ~r
        (.lw (.lamt q) :: (P ++ .lw (.res a) :: Q)) := by
      rw [← hV]; exact hwrot
    have r2 : w' ~r (.lw (.lamt q) :: (P ++ .lw (.det a) :: .ent 3 2 :: .lw (.res a) :: Q)) :=
      FW_rot_swap _ (.lw (.res a) :: Q) (.lw (.lamt q) :: (P ++ [.lw (.det a), .ent 3 2])) _
        (by
          simp only [hw', List.cons_append, List.append_assoc, List.nil_append]
          exact List.IsRotated.refl _) (by simp)
    obtain ⟨hin, hout⟩ := FW_lamSide_set R R.fpkg hR ℓ _ w' hw hfp' hcount o side
    by_cases ho : PkgLetter.lw (.lamt o) ∈ A ++ PkgLetter.lw (.lamt q) :: B
    · obtain ⟨e1, e2⟩ := hin ho
      rw [e1, e2, FW_shape _ _ P Q q a 3 2 hP r1 r2 hc o side ho]
    · have hoq : o ≠ q := fun h => ho (h ▸ hqw)
      rw [hout ho, ite_eq_right (fun h => hoq (Prod.mk.inj h).1.symm)]

end RBMTransitionEdge
