module

public import RBMTransitionEdge.Localized.Expansion.FEntWords
public import RBMTransitionEdge.Localized.Expansion.PkgLists
public import RBMTransitionEdge.Localized.Expansion.FHalves
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.PkgColl
public import RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgColl
import all RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.FHalves
import all RBMTransitionEdge.Localized.Expansion.PkgLists

@[expose] public section

/-!
# One step of the derivatives and of the further expansion on the package entries

The shared step of the counts and of the halves of the derivative structures in the proof of
Lemma 5.5 [claim_estimate_remainder_terms]: an expanded expression has a focus; one derivative of
(5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] and the expanded word keep the
well-formedness; a property carried by every derivative holds on every derivative structure; one
derivative and the expanded word on the package entries `(x, y, segment)`; and the exceptional
classes of the further expansion for every `ε`.
-/

namespace RBMTransitionEdge

open private dent_spec WfP WfP.mk wf_iff segOK isGoodP from RBMTransitionEdge.Localized.Expansion.PkgWords
open private dent_cases' from RBMTransitionEdge.Localized.Expansion.PkgColl
open private PSh_exists_first_ent PSh_findIdx_ent pkgSegs_first PSh_ent_split
  from RBMTransitionEdge.Localized.Expansion.PkgShape
open private FH_focus FH_shape from RBMTransitionEdge.Localized.Expansion.FHalves
open private plWalk_sound plStart_sound plNode plB1 plB2 plB3 plB4 plB5
  from RBMTransitionEdge.Localized.Expansion.PkgLists

/-! ### The package entries of one word, read from a letter `Δ` -/

/-- The package entries of one word, as in `PkgExpr.pents`. -/
private def RS_pw (w : List PkgLetter) : List (ℕ × ℕ × List PkgLetter) :=
  if w.any PkgLetter.isEnt then
    let E := (w.rotate (w.findIdx PkgLetter.isEnt)).filterMap fun z => match z with
      | .ent u v => some (u, v)
      | _ => none
    let S := pkgSegs w
    (List.range S.length).filterMap fun t => match S[t]?, E[t]?, E[(t + 1) % E.length]? with
      | some σ, some e₀, some e₁ => some (e₀.2, e₁.1, σ)
      | _, _, _ => none
  else []

private theorem RS_pents (X : PkgExpr) : X.pents = X.loops.flatMap RS_pw := rfl

/-- The labels `(u, v)` of the letters `Δ_{uv}` of a list. -/
private def RS_ents (Z : List PkgLetter) : List (ℕ × ℕ) :=
  Z.filterMap fun z => match z with
    | .ent u v => some (u, v)
    | _ => none

/-- The entries of a list read from a label `v` of a letter `Δ` onwards: the piece `acc` read so
far, closed at the next letter `Δ_{u v'}` as an entry `(v, u, acc)`, and the last piece closed by
the label `u₀`. -/
private def RS_chain (u₀ : ℕ) : ℕ → List PkgLetter → List PkgLetter →
    List (ℕ × ℕ × List PkgLetter)
  | v, acc, [] => [(v, u₀, acc)]
  | v, acc, .lw y :: Z => RS_chain u₀ v (acc ++ [.lw y]) Z
  | v, acc, .ent u v' :: Z => (v, u, acc) :: RS_chain u₀ v' [] Z

/-- The entries `(E_t.2, E_{t+1}.1, S_t)` of the pieces `S_t`, the last one closed by `u₀`. -/
private def RS_fp (u₀ : ℕ) (S : List (List PkgLetter)) (E : List (ℕ × ℕ)) :
    List (ℕ × ℕ × List PkgLetter) :=
  (List.range S.length).map fun t => ((E.getD t (0, 0)).2,
    (if t + 1 < E.length then (E.getD (t + 1) (0, 0)).1 else u₀), S.getD t [])

private theorem RS_pk_fp (S : List (List PkgLetter)) (E : List (ℕ × ℕ))
    (hlen : S.length = E.length) (hE : 0 < E.length) :
    ((List.range S.length).filterMap fun t => match S[t]?, E[t]?, E[(t + 1) % E.length]? with
      | some σ, some e₀, some e₁ => some (e₀.2, e₁.1, σ)
      | _, _, _ => none) = RS_fp (E.getD 0 (0, 0)).1 S E := by
  unfold RS_fp
  rw [← List.filterMap_eq_map]
  refine List.filterMap_congr fun t ht => ?_
  have ht' : t < S.length := List.mem_range.1 ht
  have h1 : t < E.length := hlen ▸ ht'
  have h2 : (t + 1) % E.length < E.length := Nat.mod_lt _ hE
  rw [List.getElem?_eq_getElem ht', List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
  by_cases hc : t + 1 < E.length
  · simp [Nat.mod_eq_of_lt hc, hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem ht']
  · have h3 : (t + 1) % E.length = 0 := by
      have h4 : t + 1 = E.length := by omega
      rw [h4, Nat.mod_self]
    simp [h3, hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem ht', List.getElem?_eq_getElem hE]

private theorem RS_fp_cons (u₀ : ℕ) (σ : List PkgLetter) (S : List (List PkgLetter))
    (x v u v' : ℕ) (E : List (ℕ × ℕ)) :
    RS_fp u₀ (σ :: S) ((x, v) :: (u, v') :: E) = (v, u, σ) :: RS_fp u₀ S ((u, v') :: E) := by
  unfold RS_fp
  have hl : (σ :: S).length = S.length + 1 := rfl
  rw [hl, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp

private theorem RS_fp_chain (u₀ : ℕ) :
    ∀ (Z acc : List PkgLetter), (∀ z ∈ acc, z.isEnt = false) → ∀ x v : ℕ,
      RS_fp u₀ ((acc ++ Z).splitOnP PkgLetter.isEnt) ((x, v) :: RS_ents Z) =
        RS_chain u₀ v acc Z
  | [], acc, hacc, x, v => by
    rw [List.append_nil, List.splitOnP_eq_singleton hacc]
    simp [RS_fp, RS_chain, RS_ents]
  | .lw y :: Z, acc, hacc, x, v => by
    have e : acc ++ .lw y :: Z = (acc ++ [PkgLetter.lw y]) ++ Z := by simp
    have hacc' : ∀ z ∈ acc ++ [.lw y], z.isEnt = false := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hacc z hz
      · rw [List.mem_singleton.1 hz]; rfl
    have hE : RS_ents (.lw y :: Z) = RS_ents Z := rfl
    rw [e, hE, RS_chain]
    exact RS_fp_chain u₀ Z (acc ++ [PkgLetter.lw y]) hacc' x v
  | .ent u v' :: Z, acc, hacc, x, v => by
    have hE : RS_ents (.ent u v' :: Z) = (u, v') :: RS_ents Z := rfl
    rw [List.splitOnP_append_cons_of_forall_mem hacc _ rfl Z, hE, RS_fp_cons, RS_chain]
    have := RS_fp_chain u₀ Z [] (by simp) u v'
    rw [List.nil_append] at this
    rw [this]

private theorem RS_len : ∀ Z : List PkgLetter,
    (Z.splitOnP PkgLetter.isEnt).length = (RS_ents Z).length + 1
  | [] => rfl
  | .lw y :: Z => by
    rw [List.splitOnP_cons_eq_ite_modifyHead]
    have hE : RS_ents (.lw y :: Z) = RS_ents Z := rfl
    simp only [PkgLetter.isEnt, Bool.false_eq_true, ↓reduceIte, List.length_modifyHead, hE]
    exact RS_len Z
  | .ent u v :: Z => by
    rw [List.splitOnP_cons_eq_ite_modifyHead]
    have hE : RS_ents (.ent u v :: Z) = (u, v) :: RS_ents Z := rfl
    simp only [PkgLetter.isEnt, ↓reduceIte, List.length_cons, hE]
    rw [RS_len Z]

/-- The entries of a word read from its first letter `Δ` (`P` without `Δ`). -/
private theorem RS_pw_first (P Q : List PkgLetter) (x y : ℕ)
    (hP : ∀ z ∈ P, z.isEnt = false) :
    RS_pw (P ++ .ent x y :: Q) = RS_chain x y [] (Q ++ P) := by
  have hw : (P ++ .ent x y :: Q).any PkgLetter.isEnt = true := by simp [PkgLetter.isEnt]
  have hrot : (P ++ .ent x y :: Q).rotate ((P ++ .ent x y :: Q).findIdx PkgLetter.isEnt) =
      .ent x y :: (Q ++ P) := by
    rw [PSh_findIdx_ent P Q x y hP]
    exact List.rotate_append_length_eq P (.ent x y :: Q)
  have hS : pkgSegs (P ++ .ent x y :: Q) = (Q ++ P).splitOnP PkgLetter.isEnt :=
    pkgSegs_first P Q x y hP
  have hE : ((.ent x y :: (Q ++ P) : List PkgLetter).filterMap fun z => match z with
      | .ent u v => some (u, v)
      | _ => none) = (x, y) :: RS_ents (Q ++ P) := rfl
  unfold RS_pw
  simp only [hw, ↓reduceIte]
  rw [hrot, hE, hS, RS_pk_fp _ _ (by rw [RS_len]; rfl) (by simp)]
  have := RS_fp_chain x (Q ++ P) [] (by simp) x y
  rw [List.nil_append] at this
  simpa using this

/-- A piece without `Δ` is one entry. -/
private theorem RS_chain_free (u₀ : ℕ) :
    ∀ (T acc : List PkgLetter) (v : ℕ), (∀ z ∈ T, z.isEnt = false) →
      RS_chain u₀ v acc T = [(v, u₀, acc ++ T)]
  | [], acc, v, _ => by simp [RS_chain]
  | .lw y :: T, acc, v, hT => by
    have := RS_chain_free u₀ T (acc ++ [PkgLetter.lw y]) v fun z hz =>
      hT z (List.mem_cons_of_mem _ hz)
    rw [RS_chain, this]
    simp
  | .ent u v' :: T, acc, v, hT => by
    have := hT (.ent u v') List.mem_cons_self
    simp [PkgLetter.isEnt] at this

/-- The entries of a list cut at one of its letters `Δ`. -/
private theorem RS_chain_split (u₀ : ℕ) :
    ∀ (Z₁ acc : List PkgLetter) (v u v' : ℕ) (Z₂ : List PkgLetter),
      RS_chain u₀ v acc (Z₁ ++ .ent u v' :: Z₂) =
        RS_chain u v acc Z₁ ++ RS_chain u₀ v' [] Z₂
  | [], acc, v, u, v', Z₂ => by simp [RS_chain]
  | .lw y :: Z₁, acc, v, u, v', Z₂ => by
    rw [List.cons_append, RS_chain, RS_chain,
      RS_chain_split u₀ Z₁ (acc ++ [PkgLetter.lw y]) v u v' Z₂]
  | .ent u₁ v₁ :: Z₁, acc, v, u, v', Z₂ => by
    rw [List.cons_append, RS_chain, RS_chain, RS_chain_split u₀ Z₁ [] v₁ u v' Z₂]
    rfl

/-- The last entry of a list that ends with a piece `T` without `Δ`: the entries before it and its
start do not depend on `T` and on the closing label `u₀`. -/
private theorem RS_chain_last :
    ∀ (Z acc : List PkgLetter) (v : ℕ), ∃ (L : List (ℕ × ℕ × List PkgLetter)) (vl : ℕ)
      (σ : List PkgLetter), ∀ (u₀ : ℕ) (T : List PkgLetter), (∀ z ∈ T, z.isEnt = false) →
        RS_chain u₀ v acc (Z ++ T) = L ++ [(vl, u₀, σ ++ T)]
  | [], acc, v => ⟨[], v, acc, fun u₀ T hT => by
      rw [List.nil_append, RS_chain_free u₀ T acc v hT]; rfl⟩
  | .lw y :: Z, acc, v => by
    obtain ⟨L, vl, σ, h⟩ := RS_chain_last Z (acc ++ [PkgLetter.lw y]) v
    exact ⟨L, vl, σ, fun u₀ T hT => by rw [List.cons_append, RS_chain]; exact h u₀ T hT⟩
  | .ent u v' :: Z, acc, v => by
    obtain ⟨L, vl, σ, h⟩ := RS_chain_last Z [] v'
    exact ⟨(v, u, acc) :: L, vl, σ, fun u₀ T hT => by
      rw [List.cons_append, RS_chain, h u₀ T hT]; rfl⟩

/-- The pieces of the entries read from a label are the pieces of the list cut at its letters
`Δ`. -/
private theorem RS_chain_segs (u₀ : ℕ) :
    ∀ (Z acc : List PkgLetter) (v : ℕ), (∀ z ∈ acc, z.isEnt = false) →
      (RS_chain u₀ v acc Z).map (fun e => e.2.2) = (acc ++ Z).splitOnP PkgLetter.isEnt
  | [], acc, v, hacc => by
    rw [List.append_nil, List.splitOnP_eq_singleton hacc]; rfl
  | .lw y :: Z, acc, v, hacc => by
    have e : acc ++ .lw y :: Z = (acc ++ [PkgLetter.lw y]) ++ Z := by simp
    rw [RS_chain, e]
    refine RS_chain_segs u₀ Z _ v fun z hz => ?_
    rcases List.mem_append.1 hz with hz | hz
    · exact hacc z hz
    · rw [List.mem_singleton.1 hz]; rfl
  | .ent u v' :: Z, acc, v, hacc => by
    rw [RS_chain, List.splitOnP_append_cons_of_forall_mem hacc _ rfl Z, List.map_cons]
    have := RS_chain_segs u₀ Z [] v' (by simp)
    rw [List.nil_append] at this
    rw [this]

/-- The pieces of the entries of a word with a `Δ` are its packages. -/
private theorem RS_pw_segs (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) :
    (RS_pw w).map (fun e => e.2.2) = pkgSegs w := by
  obtain ⟨P, x, y, Q, hP, rfl⟩ := PSh_exists_first_ent w hw
  rw [RS_pw_first P Q x y hP, pkgSegs_first P Q x y hP, RS_chain_segs x (Q ++ P) [] y (by simp),
    List.nil_append]

private theorem RS_pw_free (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = false) :
    RS_pw w = [] := by
  unfold RS_pw
  simp only [hw, Bool.false_eq_true, ↓reduceIte]

/-- The entries of a word read from any of its letters `Δ`, up to order. -/
private theorem RS_pw_any (A B : List PkgLetter) (u v : ℕ) :
    (RS_pw (A ++ .ent u v :: B)).Perm (RS_chain u v [] (B ++ A)) := by
  obtain ⟨P, x, y, Q, hP, hw⟩ := PSh_exists_first_ent (A ++ .ent u v :: B) (by simp [PkgLetter.isEnt])
  rw [hw, RS_pw_first P Q x y hP]
  rcases PSh_ent_split A B P Q u v x y hP hw with ⟨rfl, rfl⟩ | ⟨A', rfl, rfl⟩
  · have h := List.append_cancel_left hw
    simp only [List.cons.injEq, PkgLetter.ent.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact List.Perm.refl _
  · have e1 : (A' ++ .ent u v :: B) ++ P = A' ++ .ent u v :: (B ++ P) := by simp
    have e2 : B ++ (P ++ .ent x y :: A') = (B ++ P) ++ .ent x y :: A' := by simp
    rw [e1, e2, RS_chain_split, RS_chain_split]
    exact List.perm_append_comm

/-- The entries of a word with a `Δ` do not depend on where the cyclic word is cut. -/
private theorem RS_pw_comm (A B : List PkgLetter) (h : (A ++ B).any PkgLetter.isEnt = true) :
    (RS_pw (A ++ B)).Perm (RS_pw (B ++ A)) := by
  cases hB : B.any PkgLetter.isEnt
  · have hA : A.any PkgLetter.isEnt = true := by
      rw [List.any_append, hB, Bool.or_false] at h; exact h
    obtain ⟨A₁, p, q, A₂, -, rfl⟩ := PSh_exists_first_ent A hA
    have e1 : (A₁ ++ .ent p q :: A₂) ++ B = A₁ ++ .ent p q :: (A₂ ++ B) := by simp
    have e2 : B ++ (A₁ ++ .ent p q :: A₂) = (B ++ A₁) ++ .ent p q :: A₂ := by simp
    rw [e1, e2]
    refine (RS_pw_any _ _ p q).trans ?_
    refine List.Perm.trans ?_ (RS_pw_any _ _ p q).symm
    simp
  · obtain ⟨B₁, p, q, B₂, -, rfl⟩ := PSh_exists_first_ent B hB
    have e1 : A ++ (B₁ ++ .ent p q :: B₂) = (A ++ B₁) ++ .ent p q :: B₂ := by simp
    have e2 : (B₁ ++ .ent p q :: B₂) ++ A = B₁ ++ .ent p q :: (B₂ ++ A) := by simp
    rw [e1, e2]
    refine (RS_pw_any _ _ p q).trans ?_
    refine List.Perm.trans ?_ (RS_pw_any _ _ p q).symm
    simp

/-- The entries of a rotation of a word with a `Δ`, up to order. -/
private theorem RS_pw_rot (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) (n : ℕ) :
    (RS_pw (w.rotate n)).Perm (RS_pw w) := by
  rw [List.rotate_eq_drop_append_take_mod]
  have h := RS_pw_comm (w.take (n % w.length)) (w.drop (n % w.length))
    (by rw [List.take_append_drop]; exact hw)
  rw [List.take_append_drop] at h
  exact h.symm

/-- The step on a word `𝒢_a B Δ_{pq} Z P` (with `B` and `P` without `Δ`): the word
`d₁ B Δ_{pq} Z P d₂ Δ_{uv}` has the entries of the first word with the entry of `Z P 𝒢_a B`
replaced by its two pieces `(x, u, A d₂)` and `(v, p, d₁ B)`, where `A = σ P`. -/
private theorem RS_core (a : Fin 2) (d₁ d₂ : PkgLetter) (hd₁ : d₁.isEnt = false)
    (hd₂ : d₂.isEnt = false) (u v p q : ℕ) (B Z P : List PkgLetter)
    (hB : ∀ z ∈ B, z.isEnt = false) (hP : ∀ z ∈ P, z.isEnt = false) :
    ∃ (L : List (ℕ × ℕ × List PkgLetter)) (vl : ℕ) (σ : List PkgLetter),
      (RS_pw (.lw (.res a) :: (B ++ .ent p q :: (Z ++ P)))).Perm
        (L ++ [(vl, p, σ ++ P ++ .lw (.res a) :: B)]) ∧
      (RS_pw ((d₁ :: (B ++ .ent p q :: (Z ++ P))) ++ [d₂, .ent u v])).Perm
        (L ++ [(vl, u, σ ++ P ++ [d₂]), (v, p, d₁ :: B)]) := by
  obtain ⟨L, vl, σ, h⟩ := RS_chain_last Z [] q
  refine ⟨L, vl, σ, ?_, ?_⟩
  · have e : PkgLetter.lw (.res a) :: (B ++ .ent p q :: (Z ++ P)) =
        (.lw (.res a) :: B) ++ .ent p q :: (Z ++ P) := by simp
    rw [e]
    refine (RS_pw_any _ _ p q).trans ?_
    have e2 : (Z ++ P) ++ (PkgLetter.lw (.res a) :: B) = Z ++ (P ++ .lw (.res a) :: B) := by simp
    rw [e2, h p _ ?_]
    · simp
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hP z hz
      · rcases List.mem_cons.1 hz with rfl | hz
        · rfl
        · exact hB z hz
  · have e : (d₁ :: (B ++ .ent p q :: (Z ++ P))) ++ [d₂, .ent u v] =
        (d₁ :: B) ++ .ent p q :: (Z ++ P ++ [d₂, .ent u v]) := by simp
    rw [e]
    refine (RS_pw_any _ _ p q).trans ?_
    have e2 : (Z ++ P ++ [d₂, .ent u v]) ++ (d₁ :: B) =
        (Z ++ (P ++ [d₂])) ++ .ent u v :: (d₁ :: B) := by simp
    have hPd : ∀ z ∈ P ++ [d₂], z.isEnt = false := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hP z hz
      · rw [List.mem_singleton.1 hz]; exact hd₂
    have hdB : ∀ z ∈ d₁ :: B, z.isEnt = false := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hd₁
      · exact hB z hz
    rw [e2, RS_chain_split, h u _ hPd, RS_chain_free p (d₁ :: B) [] v hdB]
    simp

/-- A list with a `Δ`, ending with a stretch `P` without `Δ`: its first `Δ` and the stretch. -/
private theorem RS_cut (Y P : List PkgLetter) (hY : Y.any PkgLetter.isEnt = true) :
    ∃ (B : List PkgLetter) (p q : ℕ) (Z : List PkgLetter), (∀ z ∈ B, z.isEnt = false) ∧
      Y ++ P = B ++ .ent p q :: (Z ++ P) := by
  obtain ⟨B, p, q, Z, hB, rfl⟩ := PSh_exists_first_ent Y hY
  exact ⟨B, p, q, Z, hB, by simp⟩

private theorem RS_free (l : List PkgLetter) (h : l.any PkgLetter.isEnt = false) :
    ∀ z ∈ l, z.isEnt = false := by
  intro z hz
  have := List.any_eq_false.1 h z hz
  simpa using this

/-- The condition of `PkgExpr.wf` on the packages of one word, through `pkgSegs`. -/
private theorem RS_segOK (w : List PkgLetter) :
    segOK w = (pkgSegs w).all fun v => v.any isGoodP := rfl

/-- A word with a `Δ` whose entries all have a resolvent or a `Λ̃` satisfies the condition of
`PkgExpr.wf` on its packages. -/
private theorem RS_segs_good (N : List PkgLetter) (hN : N.any PkgLetter.isEnt = true)
    (M : List (ℕ × ℕ × List PkgLetter)) (hp : (RS_pw N).Perm M)
    (hg : ∀ t ∈ M, t.2.2.any isGoodP = true) : segOK N = true := by
  rw [RS_segOK, ← RS_pw_segs N hN, List.all_eq_true]
  intro σ hσ
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hσ
  exact hg t (hp.subset ht)

/-- The entries of a word with a `Δ` satisfying the condition of `PkgExpr.wf` all have a
resolvent or a `Λ̃`. -/
private theorem RS_pw_good (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true)
    (h : segOK w = true) : ∀ t ∈ RS_pw w, t.2.2.any isGoodP = true := by
  rw [RS_segOK, ← RS_pw_segs w hw, List.all_eq_true] at h
  exact fun t ht => h _ (List.mem_map_of_mem ht)

/-- Replacing one entry of a list keeps the sum of a function when the value is kept. -/
private theorem RS_sum_set {α : Type*} (l : List α) (f : α → ℕ) (ℓ : ℕ) (w N : α)
    (h : l[ℓ]? = some w) (hf : f N = f w) : ((l.set ℓ N).map f).sum = (l.map f).sum := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  have p1 := ((List.set_perm_cons_eraseIdx hlt N).map f).sum_eq
  have p2 := ((List.getElem_cons_eraseIdx_perm hlt).map f).sum_eq
  rw [hget] at p2
  rw [p1, ← p2]
  simp [hf]

/-- A letter `Λ̃` before the first `Δ` of a list lies in the stretch before that `Δ`. -/
private theorem RS_lam_mem (B Z X Y : List PkgLetter) (p q : ℕ) (o : Fin 2)
    (hX : ∀ z ∈ X, z.isEnt = false) (h : B ++ .ent p q :: Z = X ++ .lw (.lamt o) :: Y) :
    PkgLetter.lw (.lamt o) ∈ B := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases a' with _ | ⟨c, a''⟩
    · simp at h2
    · have hc : c = .ent p q := (List.cons.inj h2).1.symm
      have := hX c (by rw [h1]; simp)
      rw [hc] at this
      simp [PkgLetter.isEnt] at this
  · rcases c' with _ | ⟨c, c''⟩
    · simp at h2
    · have hc : c = .lw (.lamt o) := (List.cons.inj h2).1.symm
      rw [h1, hc]
      simp

/-! ### Replacing one loop -/

private theorem RS_flat {α β : Type*} (l : List α) (f : α → List β) (ℓ : ℕ) (w : α)
    (h : l[ℓ]? = some w) : (l.flatMap f).Perm (f w ++ (l.eraseIdx ℓ).flatMap f) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  have hp := (List.getElem_cons_eraseIdx_perm hlt).symm
  rw [hget] at hp
  have := hp.flatMap_right f
  simpa using this

private theorem RS_flat_set {α β : Type*} (l : List α) (f : α → List β) (ℓ : ℕ) (w w' : α)
    (h : l[ℓ]? = some w) :
    ((l.set ℓ w').flatMap f).Perm (f w' ++ (l.eraseIdx ℓ).flatMap f) := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h
  have := (List.set_perm_cons_eraseIdx hlt w').flatMap_right f
  simpa using this

/-- If the entries of one word are `L` and `e`, and become `L` and `M`, then the entries of the
expression are those with `e` removed and `M` added, up to order. -/
private theorem RS_swap (P P' L M R : List (ℕ × ℕ × List PkgLetter))
    (e : ℕ × ℕ × List PkgLetter) (hP : P.Perm ((L ++ [e]) ++ R)) (hP' : P'.Perm ((L ++ M) ++ R)) :
    e ∈ P ∧ P'.Perm (P.erase e ++ M) := by
  have h1 : P.Perm (e :: (L ++ R)) := hP.trans (by simp)
  refine ⟨h1.symm.subset List.mem_cons_self, ?_⟩
  have h2 : (P.erase e).Perm (L ++ R) := by
    have := h1.erase e
    simpa using this
  refine hP'.trans ?_
  refine List.Perm.trans ?_ (h2.symm.append_right M)
  simp only [List.append_assoc]
  exact List.Perm.append_left L List.perm_append_comm

/-- The loops, weights and block indices of `fpkg` at the focus `(ℓ, r, right)`. -/
private theorem RS_fpkg (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (w : List PkgLetter) (a : Fin 2)
    (tl : List PkgLetter) (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    R.fpkg.loops = R.loops.set ℓ ((if right then .lw (.res a) :: tl ++ [.lw (.det a)]
        else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2]) ∧
      R.fpkg.weights = R.weights ∧ R.fpkg.nb = R.nb := by
  unfold PkgExpr.fpkg
  rw [hf]
  dsimp only
  rw [hw]
  dsimp only
  rw [hrot]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The step -/

/-- An expression expanded in the further expansion of the proof of Lemma 5.5
[claim_estimate_remainder_terms] has a focus: one of the rules (i)–(iv) applies to it. -/
theorem pkg_fInner_focus (ε : ℝ) (j : ℕ) (L : List PkgExpr) (R : PkgExpr)
    (hR : R ∈ fInner ε j L) : R.ffocus.isSome = true := by
  classical
  induction j generalizing L with
  | zero => simp [fInner] at hR
  | succ j ih =>
    rw [fInner, List.mem_append] at hR
    rcases hR with hR | hR
    · rw [List.mem_filter] at hR
      have h := of_decide_eq_true hR.2
      unfold PkgExpr.FStopped at h
      rw [Option.isSome_iff_ne_none]
      exact fun hn => h (Or.inr hn)
    · exact ih _ hR

/-- One derivative of the derivative structures of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] keeps the well-formedness of an expression
of the further expansion, and adds to its counts `(m, n, u, S)` one of the three rows of a
resolvent of a word with `Δ`, of a word without `Δ`, or of a light weight. -/
theorem pkg_dent_wf (R R' : PkgExpr) (u v : ℕ) (hR : R.wf = true) (h : R' ∈ R.dent u v) :
    R'.wf = true ∧ (R'.charsP = R.charsP + (1, 1, 0, 0) ∨ R'.charsP = R.charsP + (1, 0, 0, 1) ∨
      R'.charsP = R.charsP + (2, 1, -1, 1)) := by
  exact dent_spec R R' u v hR h

/-- The expanded word of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms] keeps the well-formedness, when one of the rules (i)–(iv)
applies. -/
theorem pkg_fpkg_wf (R : PkgExpr) (hR : R.wf = true) (hf : R.ffocus.isSome = true) :
    R.fpkg.wf = true := by
  obtain ⟨⟨ℓ, r, right⟩, hf'⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨w, hw, i, o, hi, hs⟩ := FH_focus R ℓ r right hf'
  obtain ⟨a, tl, hrot, hR', hL'⟩ := FH_shape w i r right o hi hs
  obtain ⟨hl, hwt, hnb⟩ := RS_fpkg R ℓ r right w a tl hf' hw hrot
  rw [wf_iff] at hR ⊢
  obtain ⟨h0, h1, h2, h3, h4⟩ := hR
  have hwmem : w ∈ R.loops := List.mem_of_getElem? hw
  have hsub : ∀ z ∈ PkgLetter.lw (.res a) :: tl, z ∈ w := fun z hz =>
    List.mem_rotate.1 (by rw [hrot]; exact hz)
  obtain ⟨N, hN⟩ : ∃ N : List PkgLetter, N = (if right then .lw (.res a) :: tl ++ [.lw (.det a)]
      else .lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2] := ⟨_, rfl⟩
  rw [← hN] at hl
  have hNmem : ∀ z ∈ N, z ∈ PkgLetter.lw (.res a) :: tl ∨ z = .lw (.det a) ∨ z = .ent 3 2 := by
    intro z hz
    rw [hN] at hz
    simp only [List.mem_cons]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hz <;> tauto
  have hcount : ∀ o' : Fin 2, N.count (.lw (.lamt o')) = w.count (.lw (.lamt o')) := by
    intro o'
    rw [← (List.rotate_perm w r).count_eq, hrot, hN]
    cases right <;> simp [List.count_append]
  have hNE : N.any PkgLetter.isEnt = true := by
    rw [hN]; simp [PkgLetter.isEnt]
  have hres : ∀ (A B : List PkgLetter), (A ++ .lw (.res a) :: B).any isGoodP = true :=
    fun A B => List.any_eq_true.2 ⟨.lw (.res a), by simp, rfl⟩
  have hseg : segOK N = true := by
    cases hE : w.any PkgLetter.isEnt
    · have hrE : (w.rotate r).any PkgLetter.isEnt = false := by
        rw [(List.rotate_perm w r).any_eq]; exact hE
      rw [hrot] at hrE
      have hfr := RS_free _ hrE
      obtain ⟨W, hW⟩ : ∃ W : List PkgLetter, W = (if right then .lw (.res a) :: tl ++
          [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]) := ⟨_, rfl⟩
      rw [← hW] at hN
      have hWf : ∀ z ∈ W, z.isEnt = false := by
        intro z hz
        rw [hW] at hz
        cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        · rcases hz with (rfl | hz) | rfl
          · rfl
          · exact hfr z (List.mem_cons_of_mem _ hz)
          · rfl
        · rcases hz with (rfl | hz) | rfl
          · rfl
          · exact hfr z (List.mem_cons_of_mem _ hz)
          · rfl
      have hp := RS_pw_any W [] 3 2
      rw [List.nil_append, RS_chain_free 3 W [] 2 hWf, List.nil_append] at hp
      rw [hN]
      refine RS_segs_good _ (by rw [← hN]; exact hNE) _ hp fun t ht => ?_
      rw [List.mem_singleton.1 ht, hW]
      cases right
      · exact List.any_eq_true.2 ⟨.lw (.res a), by simp, rfl⟩
      · exact List.any_eq_true.2 ⟨.lw (.res a), by simp, rfl⟩
    · have hrE : (w.rotate r).any PkgLetter.isEnt = true := by
        rw [(List.rotate_perm w r).any_eq]; exact hE
      rw [hrot] at hrE
      have htl : tl.any PkgLetter.isEnt = true := by simpa [PkgLetter.isEnt] using hrE
      have hrw := RS_pw_rot w hE r
      rw [hrot] at hrw
      have hgw := RS_pw_good w hE (h2 w hwmem)
      cases right
      · obtain ⟨X, Y, hXY, hX⟩ := hL' rfl
        obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut tl [] htl
        rw [List.append_nil] at hcut
        obtain ⟨L, vl, σ, k1, k2⟩ := RS_core a (.lw (.det a)) (.lw (.res a)) rfl rfl 3 2 p q B Z []
          hB (by simp)
        simp only [List.append_nil] at k1 k2 hcut
        rw [← hcut] at k1 k2
        have eN : N = (.lw (.det a) :: tl) ++ [.lw (.res a), .ent 3 2] := by rw [hN]; simp
        have hlam : PkgLetter.lw (.lamt o) ∈ B :=
          RS_lam_mem B Z X Y p q o (fun z hz => (hX z hz).1) (hcut.symm.trans hXY)
        rw [eN]
        refine RS_segs_good _ (by rw [← eN]; exact hNE) _ k2 fun t ht => ?_
        rcases List.mem_append.1 ht with ht | ht
        · exact hgw t (hrw.subset (k1.symm.subset (List.mem_append_left _ ht)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hres σ []
          · exact List.any_eq_true.2 ⟨.lw (.lamt o), List.mem_cons_of_mem _ hlam, rfl⟩
      · obtain ⟨Y, X, hYX, hX⟩ := hR' rfl
        have hY : Y.any PkgLetter.isEnt = true := by
          rw [hYX, List.any_append] at htl
          have hX' : (PkgLetter.lw (.lamt o) :: X).any PkgLetter.isEnt = false :=
            List.any_eq_false.2 fun z hz => by
              rcases List.mem_cons.1 hz with rfl | hz
              · simp [PkgLetter.isEnt]
              · have h' : z.isEnt = false := (hX z hz).1
                simp [h']
          rw [hX', Bool.or_false] at htl
          exact htl
        have hPf : ∀ z ∈ PkgLetter.lw (.lamt o) :: X, z.isEnt = false := by
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · rfl
          · exact (hX z hz).1
        obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut Y (.lw (.lamt o) :: X) hY
        rw [← hYX] at hcut
        obtain ⟨L, vl, σ, k1, k2⟩ := RS_core a (.lw (.res a)) (.lw (.det a)) rfl rfl 3 2 p q B Z
          (.lw (.lamt o) :: X) hB hPf
        rw [← hcut] at k1 k2
        have eN : N = (.lw (.res a) :: tl) ++ [.lw (.det a), .ent 3 2] := by rw [hN]; simp
        rw [eN]
        refine RS_segs_good _ (by rw [← eN]; exact hNE) _ k2 fun t ht => ?_
        rcases List.mem_append.1 ht with ht | ht
        · exact hgw t (hrw.subset (k1.symm.subset (List.mem_append_left _ ht)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact List.any_eq_true.2 ⟨.lw (.lamt o), by simp, rfl⟩
          · exact hres [] B
  refine WfP.mk ?_ ?_ ?_ ?_ ?_
  · rw [hl, RS_sum_set _ (fun w => w.count (.lw (.lamt 0))) ℓ w N hw (hcount 0)]
    exact h0
  · rw [hl, RS_sum_set _ (fun w => w.count (.lw (.lamt 1))) ℓ w N hw (hcount 1)]
    exact h1
  · intro w' hw'
    rw [hl] at hw'
    rcases List.mem_or_eq_of_mem_set hw' with hw' | rfl
    · exact h2 w' hw'
    · exact hseg
  · intro w' hw' y hy
    rw [hnb]
    rw [hl] at hw'
    rcases List.mem_or_eq_of_mem_set hw' with hw' | rfl
    · exact h3 w' hw' y hy
    · rcases hNmem _ hy with h | h | h
      · exact h3 w hwmem y (hsub _ h)
      · simp at h
      · simp at h
  · rw [hwt, hnb]
    exact h4

/-- The derivative structures of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]: a
property of expressions with an index, carried from `k` to `k + 1` by every derivative
`dent u v` and every `dent v u`, holds at index `p + q` for every structure of `dwirt u v p q`. -/
theorem pkg_dwirt_iter (P : ℕ → PkgExpr → Prop) (u v : ℕ)
    (h₁ : ∀ k X, P k X → ∀ X' ∈ X.dent u v, P (k + 1) X')
    (h₂ : ∀ k X, P k X → ∀ X' ∈ X.dent v u, P (k + 1) X')
    (F : PkgExpr) (hF : P 0 F) (p q : ℕ) (R' : PkgExpr) (hR' : R' ∈ F.dwirt u v p q) :
    P (p + q) R' := by
  have key : ∀ (u v : ℕ), (∀ k X, P k X → ∀ X' ∈ X.dent u v, P (k + 1) X') →
      ∀ (m : ℕ) (L : List PkgExpr) (k₀ : ℕ), (∀ X ∈ L, P k₀ X) →
        ∀ X ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[m] L, P (k₀ + m) X := by
    intro u v h m
    induction m with
    | zero => intro L k₀ hL X hX; exact hL X hX
    | succ m ih =>
      intro L k₀ hL X hX
      rw [Function.iterate_succ_apply'] at hX
      obtain ⟨X₀, hX₀, hX⟩ := List.mem_flatMap.1 hX
      exact h _ X₀ (ih L k₀ hL X₀ hX₀) X hX
  have hq := key v u h₂ q [F] 0 (fun X hX => by rw [List.mem_singleton.1 hX]; exact hF)
  have := key u v h₁ p _ q (fun X hX => by simpa using hq X hX) R' hR'
  rwa [Nat.add_comm] at this

/-- One derivative of (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] on the package
entries `(x, y, segment)`: the letter `Δ_{uv}` inserted at a resolvent `𝒢_b` of a segment
`A 𝒢_b B` with labels `(x, y)` cuts it into `(x, u, A 𝒢_b)` and `(v, y, 𝒢_b B)`; inserted at a
resolvent of a loop `⟨A 𝒢_b B⟩` without `Δ` it makes the entry `(v, u, 𝒢_b B A 𝒢_b)`; at a light
weight `⟨(𝒢_b - 𝔐_b) E_y⟩` it makes the entry `(v, u, 𝒢_b E_y 𝒢_b)` and removes the weight. The
entries are listed up to order; the number of block indices is kept. -/
theorem pkg_dent_pents (X : PkgExpr) (u v : ℕ) (X' : PkgExpr) (hX' : X' ∈ X.dent u v) :
    X'.nb = X.nb ∧
    ((∃ e ∈ X.pents, ∃ (A : List PkgLetter) (b : Fin 2) (B : List PkgLetter),
        e.2.2 = A ++ .lw (.res b) :: B ∧ X'.weights = X.weights ∧
        X'.pents.Perm (X.pents.erase e ++
          [(e.1, u, A ++ [.lw (.res b)]), (v, e.2.1, .lw (.res b) :: B)])) ∨
      (∃ (A : List PkgLetter) (b : Fin 2) (B : List PkgLetter),
        A ++ .lw (.res b) :: B ∈ X.loops ∧ (A ++ .lw (.res b) :: B).any PkgLetter.isEnt = false ∧
        X'.weights = X.weights ∧
        X'.pents.Perm (X.pents ++ [(v, u, .lw (.res b) :: B ++ A ++ [.lw (.res b)])])) ∨
      (∃ (b : Fin 2) (y : ℕ), (b, y) ∈ X.weights ∧ X'.weights.Perm (X.weights.erase (b, y)) ∧
        X'.pents.Perm (X.pents ++ [(v, u, [.lw (.res b), .lw (.proj y), .lw (.res b)])]))) := by
  rcases dent_cases' X X' u v hX' with
    ⟨ℓ, A₀, B₀, a, hℓ, -, hnb, hwt, hl, -, -⟩ | ⟨j, b, y, hj, -, hnb, -, -, hwt, hl⟩
  · refine ⟨hnb, ?_⟩
    have hp := RS_flat X.loops RS_pw ℓ _ hℓ
    rw [← RS_pents] at hp
    have hp' : X'.pents.Perm
        (RS_pw (A₀ ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ B₀) ++
          (X.loops.eraseIdx ℓ).flatMap RS_pw) := by
      rw [RS_pents, hl]
      exact RS_flat_set _ _ ℓ _ _ hℓ
    cases hE : (A₀ ++ .lw (.res a) :: B₀).any PkgLetter.isEnt
    · right; left
      refine ⟨A₀, a, B₀, List.mem_of_getElem? hℓ, hE, hwt, ?_⟩
      rw [RS_pw_free _ hE, List.nil_append] at hp
      have e : A₀ ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ B₀ =
          (A₀ ++ [.lw (.res a)]) ++ .ent u v :: (.lw (.res a) :: B₀) := by simp
      have hfree : ∀ z ∈ (PkgLetter.lw (.res a) :: B₀) ++ (A₀ ++ [.lw (.res a)]),
          z.isEnt = false := by
        intro z hz
        refine RS_free _ hE z ?_
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        tauto
      rw [e] at hp'
      have h1 := RS_pw_any (A₀ ++ [.lw (.res a)]) (.lw (.res a) :: B₀) u v
      rw [RS_chain_free u _ [] v hfree, List.nil_append] at h1
      have e3 : (PkgLetter.lw (.res a) :: B₀) ++ (A₀ ++ [.lw (.res a)]) =
          .lw (.res a) :: B₀ ++ A₀ ++ [.lw (.res a)] := by simp
      rw [e3] at h1
      exact hp'.trans ((h1.append_right _).trans
        (List.perm_append_comm.trans (hp.symm.append_right _)))
    · left
      have hc1 := RS_pw_comm A₀ (.lw (.res a) :: B₀) hE
      have hc2 := RS_pw_comm (A₀ ++ [.lw (.res a), .ent u v]) (.lw (.res a) :: B₀)
        (by simp [PkgLetter.isEnt])
      have e1 : A₀ ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ B₀ =
          (A₀ ++ [.lw (.res a), .ent u v]) ++ (.lw (.res a) :: B₀) := by simp
      have e2 : (PkgLetter.lw (.res a) :: B₀) ++ (A₀ ++ [.lw (.res a), .ent u v]) =
          (.lw (.res a) :: (B₀ ++ A₀)) ++ [.lw (.res a), .ent u v] := by simp
      have e3 : (PkgLetter.lw (.res a) :: B₀) ++ A₀ = .lw (.res a) :: (B₀ ++ A₀) := by simp
      rw [e3] at hc1
      rw [← e1, e2] at hc2
      have htl : (B₀ ++ A₀).any PkgLetter.isEnt = true := by
        have : (B₀ ++ A₀).any PkgLetter.isEnt = (A₀ ++ .lw (.res a) :: B₀).any PkgLetter.isEnt := by
          simp only [List.any_append, List.any_cons, PkgLetter.isEnt, Bool.false_or]
          exact Bool.or_comm _ _
        rw [this, hE]
      obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut (B₀ ++ A₀) [] htl
      rw [List.append_nil] at hcut
      obtain ⟨L, vl, σ, h1, h2⟩ := RS_core a (.lw (.res a)) (.lw (.res a)) rfl rfl u v p q B Z []
        hB (by simp)
      simp only [List.append_nil] at h1 h2 hcut
      rw [← hcut] at h1 h2
      obtain ⟨hmem, hperm⟩ := RS_swap X.pents X'.pents L _ _ (vl, p, σ ++ .lw (.res a) :: B)
        (hp.trans ((hc1.trans h1).append_right _)) (hp'.trans ((hc2.trans h2).append_right _))
      exact ⟨_, hmem, σ, a, B, rfl, hwt, hperm⟩
  · refine ⟨hnb, Or.inr (Or.inr ⟨b, y, List.mem_of_getElem? hj, ?_, ?_⟩)⟩
    · rw [hwt]
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hj
      have h1 := List.getElem_cons_eraseIdx_perm hlt
      rw [hget] at h1
      have h2 := h1.symm.erase (b, y)
      rw [List.erase_cons_head] at h2
      exact h2.symm
    · rw [RS_pents, hl, List.flatMap_append, ← RS_pents, List.flatMap_singleton]
      refine List.Perm.append_left _ ?_
      have e : [PkgLetter.lw (.res b), .ent u v, .lw (.res b), .lw (.proj y)] =
          [.lw (.res b)] ++ .ent u v :: [.lw (.res b), .lw (.proj y)] := rfl
      rw [e]
      exact (RS_pw_any _ _ u v).trans (List.Perm.refl _)

/-- The expanded word of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms] on the package entries: if a rule applies at the resolvent
`𝒢_a` at position `r` of the loop `ℓ` (rotated to `𝒢_a tl`), a segment `A 𝒢_a B` with labels
`(x, y)` becomes `(x, 3, A 𝔐_a)` and `(2, y, 𝒢_a B)` (to the right of its `Λ̃`) or
`(x, 3, A 𝒢_a)` and `(2, y, 𝔐_a B)` (to the left), and a loop without `Δ` becomes the entry
`(2, 3, 𝒢_a tl 𝔐_a)` or `(2, 3, 𝔐_a tl 𝒢_a)`. The entries are listed up to order; the block
indices and the light weights are kept. -/
theorem pkg_fpkg_pents (R : PkgExpr) (ℓ r : ℕ) (right : Bool) (hf : R.ffocus = some (ℓ, r, right))
    (w : List PkgLetter) (hw : R.loops[ℓ]? = some w) (a : Fin 2) (tl : List PkgLetter)
    (hr : w.rotate r = .lw (.res a) :: tl) :
    R.fpkg.nb = R.nb ∧ R.fpkg.weights = R.weights ∧
    (w.any PkgLetter.isEnt = true → ∃ e ∈ R.pents, ∃ A B : List PkgLetter,
        e.2.2 = A ++ .lw (.res a) :: B ∧
        R.fpkg.pents.Perm (R.pents.erase e ++
          (if right then [(e.1, 3, A ++ [.lw (.det a)]), (2, e.2.1, .lw (.res a) :: B)]
           else [(e.1, 3, A ++ [.lw (.res a)]), (2, e.2.1, .lw (.det a) :: B)]))) ∧
    (w.any PkgLetter.isEnt = false → R.fpkg.pents.Perm (R.pents ++
        [(2, 3, if right then .lw (.res a) :: tl ++ [.lw (.det a)]
          else .lw (.det a) :: tl ++ [.lw (.res a)])])) := by
  obtain ⟨hl, hwt, hnb⟩ := RS_fpkg R ℓ r right w a tl hf hw hr
  refine ⟨hnb, hwt, fun hE => ?_, fun hE => ?_⟩
  · have hp := RS_flat R.loops RS_pw ℓ w hw
    rw [← RS_pents] at hp
    have hrE : (w.rotate r).any PkgLetter.isEnt = true := by
      rw [(List.rotate_perm w r).any_eq]; exact hE
    rw [hr] at hrE
    have htl : tl.any PkgLetter.isEnt = true := by simpa [PkgLetter.isEnt] using hrE
    have hrot := RS_pw_rot w hE r
    rw [hr] at hrot
    obtain ⟨B, p, q, Z, hB, hcut⟩ := RS_cut tl [] htl
    rw [List.append_nil] at hcut
    cases right
    · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
      have hp' : R.fpkg.pents.Perm
          (RS_pw ((.lw (.det a) :: tl) ++ [.lw (.res a), .ent 3 2]) ++
            (R.loops.eraseIdx ℓ).flatMap RS_pw) := by
        rw [RS_pents, hl]
        have e : (PkgLetter.lw (.det a) :: tl ++ [.lw (.res a)]) ++ [.ent 3 2] =
            (.lw (.det a) :: tl) ++ [.lw (.res a), .ent 3 2] := by simp
        rw [e]
        exact RS_flat_set _ _ ℓ _ _ hw
      obtain ⟨L, vl, σ, h1, h2⟩ := RS_core a (.lw (.det a)) (.lw (.res a)) rfl rfl 3 2 p q B Z []
        hB (by simp)
      simp only [List.append_nil] at h1 h2 hcut
      rw [← hcut] at h1 h2
      obtain ⟨hmem, hperm⟩ := RS_swap R.pents R.fpkg.pents L _ _ (vl, p, σ ++ .lw (.res a) :: B)
        (hp.trans ((hrot.symm.trans h1).append_right _)) (hp'.trans (h2.append_right _))
      exact ⟨_, hmem, σ, B, rfl, hperm⟩
    · simp only [↓reduceIte] at hl ⊢
      have hp' : R.fpkg.pents.Perm
          (RS_pw ((.lw (.res a) :: tl) ++ [.lw (.det a), .ent 3 2]) ++
            (R.loops.eraseIdx ℓ).flatMap RS_pw) := by
        rw [RS_pents, hl]
        have e : (PkgLetter.lw (.res a) :: tl ++ [.lw (.det a)]) ++ [.ent 3 2] =
            (.lw (.res a) :: tl) ++ [.lw (.det a), .ent 3 2] := by simp
        rw [e]
        exact RS_flat_set _ _ ℓ _ _ hw
      obtain ⟨L, vl, σ, h1, h2⟩ := RS_core a (.lw (.res a)) (.lw (.det a)) rfl rfl 3 2 p q B Z []
        hB (by simp)
      simp only [List.append_nil] at h1 h2 hcut
      rw [← hcut] at h1 h2
      obtain ⟨hmem, hperm⟩ := RS_swap R.pents R.fpkg.pents L _ _ (vl, p, σ ++ .lw (.res a) :: B)
        (hp.trans ((hrot.symm.trans h1).append_right _)) (hp'.trans (h2.append_right _))
      exact ⟨_, hmem, σ, B, rfl, hperm⟩
  · have hp := RS_flat R.loops RS_pw ℓ w hw
    rw [← RS_pents, RS_pw_free w hE, List.nil_append] at hp
    have hrE : (w.rotate r).any PkgLetter.isEnt = false := by
      rw [(List.rotate_perm w r).any_eq]; exact hE
    rw [hr] at hrE
    have hfr := RS_free _ hrE
    obtain ⟨W, hW, hWf⟩ : ∃ W : List PkgLetter, W = (if right then .lw (.res a) :: tl ++
        [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]) ∧ ∀ z ∈ W, z.isEnt = false := by
      refine ⟨_, rfl, fun z hz => ?_⟩
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hz
      · rcases hz with (rfl | hz) | rfl
        · rfl
        · exact hfr z (List.mem_cons_of_mem _ hz)
        · rfl
      · rcases hz with (rfl | hz) | rfl
        · rfl
        · exact hfr z (List.mem_cons_of_mem _ hz)
        · rfl
    rw [← hW] at hl ⊢
    have hp' : R.fpkg.pents.Perm (RS_pw (W ++ .ent 3 2 :: []) ++
        (R.loops.eraseIdx ℓ).flatMap RS_pw) := by
      rw [RS_pents, hl]
      exact RS_flat_set _ _ ℓ _ _ hw
    have h1 := RS_pw_any W [] 3 2
    rw [List.nil_append, RS_chain_free 3 W [] 2 hWf, List.nil_append] at h1
    exact hp'.trans ((h1.append_right _).trans
      (List.perm_append_comm.trans (hp.symm.append_right _)))

/-- The exceptional classes of the further expansion in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the leaves of case (ii) with `fR = 2` (after
(5.92) [eq:weak_further_expansion2]; `Σ = 1`: the loop `⟨𝔐₁ Λ̃₂ 𝔐₀ E_x⟩` and a package with two
resolvents; `Σ = 2`: one of them; `Σ = 0`: none), the leaf (5.94)
[expansion_result_type_3_fr_2_m_plus_u_2] (slot `1` only through one `𝔐₁`), and the exceptional
subcases of the companion cases (5), (6), (8); for every `ε`. -/
theorem pkg_lists' (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2)
    (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀] ∨ R ∈ fInner ε j [R₀]) :
    (R.ffocus = none → R.ptype = 2 → R.fR = 2 →
      (R.fsig = 1 → R.gainLam2 = true ∧ R.freeTwo = true) ∧
      (R.fsig = 2 → R.gainLam2 = true ∨ R.freeTwo = true)) ∧
    (R.ffocus = none → R.ptype = 3 → R.fR = 2 → R.fsig = 0 → R.onlyDet 1 = true) ∧
    (R.ffocus.isSome = true → R.ptype = 2 → R.fR = 0 → R.fsig = 1 →
      R.freeTwo = true ∨ 2 ≤ R.lamSide 0 true ∨ 2 ≤ R.lamSide 1 false) ∧
    (R.ffocus.isSome = true → R.ptype = 2 → R.lamSide 1 false = 0 → R.fR = 1 → R.fsig = 1 →
      R.gainLam2 = true) ∧
    (R.ffocus.isSome = true → R.ptype = 3 → R.fR = 0 → R.fsig = 0 →
      T = loopStart ∧ R = R₀ ∧ R.fpkg.onlyRes 1 = true) := by
  obtain ⟨hfR0, -, hs0, hge, hTt, hRt⟩ := pkg_inv_counts ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR
  have key : R.fR ≤ 2 → R.fsig ≤ 2 → plNode T R₀ R = true := fun h1 h2 =>
    plWalk_sound T R₀ _ R₀ (plStart_sound R₀.fsig.toNat (by omega) T hTt hR0 p₀ q₀ hpq R₀ hR₀ rfl)
      (R.fsig + R.fR - R₀.fsig).toNat (by omega) R hRt h1 h2
  have hb : ∀ h1 : R.fR ≤ 2, ∀ h2 : R.fsig ≤ 2, plB1 R = true ∧ plB2 R = true ∧ plB3 R = true ∧
      plB4 R = true ∧ plB5 T R₀ R = true := fun h1 h2 => by
    simpa only [plNode, Bool.and_eq_true, and_assoc] using key h1 h2
  refine ⟨fun hf hp hfr => ⟨fun hs => ?_, fun hs => ?_⟩, fun hf hp hfr hs => ?_,
    fun hf hp hfr hs => ?_, fun hf hp hl hfr hs => ?_, fun hf hp hfr hs => ?_⟩
  · exact (of_decide_eq_true (hb (by omega) (by omega)).1 hfr hp hf).1 hs
  · exact (of_decide_eq_true (hb (by omega) (by omega)).1 hfr hp hf).2 hs
  · exact of_decide_eq_true (hb (by omega) (by omega)).2.1 hfr hs hp hf
  · exact of_decide_eq_true (hb (by omega) (by omega)).2.2.1 hfr hs hp hf
  · exact of_decide_eq_true (hb (by omega) (by omega)).2.2.2.1 hfr hs hp hl hf
  · exact of_decide_eq_true (hb (by omega) (by omega)).2.2.2.2 hfr hs hp hf

end RBMTransitionEdge
