module

public import RBMTransitionEdge.Localized.Expansion.Reach

@[expose] public section

/-!
# The tree counts of the expansion of §5.3

The tree of (5.40) [expansion_for_integral_by_part_term] without the stopping rule, the parent
decomposition and the depth of the expressions reached, the counts (5.36) [eq:loop] and (5.37)
[number_of_G_type_1], and the exceptional words of the direct estimation in the proof of
Lemma 5.5 [claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- Type I of (5.34) [Gamma_Type_1]: `Λ̃₁` and `Λ̃₂` lie in one loop; otherwise Type II of (5.35)
[Gamma_Type_2]. -/
def LoopExpr.typeI (T : LoopExpr) : Bool :=
  T.loops.any fun w => w.contains (.lamt 0) && w.contains (.lamt 1)

/-- The expressions after `L` rounds of the expansion of §5.3 without the stopping rule: every
expression is replaced by the terms of (5.40) [expansion_for_integral_by_part_term]. -/
def loopTree : ℕ → List LoopExpr
  | 0 => [loopStart]
  | L + 1 => (loopTree L).flatMap LoopExpr.step

/-- `⟨𝔐₀ Λ̃₁ 𝒢₁ Λ̃₂⟩`, the expression of the exceptional case of (ii) in the direct estimation of
the proof of Lemma 5.5 [claim_estimate_remainder_terms], (5.75)
[direct_estimate_type_1_k_1_0_k_2_geq_1_sR_1_p_plus_q_2_m_plus_u_1]. -/
def loopWordII : LoopExpr := ⟨0, 0, 0, [], [[.det 0, .lamt 0, .res 1, .lamt 1]]⟩

/-- `D Σ_x ⟨𝔐₀ Λ̃₁ 𝔐₁ E_x⟩ ⟨E_x 𝒢₁ Λ̃₂ 𝒢₀⟩`, the first expression of the exceptional case of (iv)
in the direct estimation of the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def loopWordIV : LoopExpr :=
  ⟨1, 0, 1, [], [[.det 1, .proj 0, .det 0, .lamt 0], [.proj 0, .res 1, .lamt 1, .res 0]]⟩

/-- `D² Σ_{x,y} ⟨𝔐₀ Λ̃₁ 𝔐₁ E_x⟩ ⟨𝔐₁ Λ̃₂ 𝒢₀ E_y⟩ ⟨E_y 𝒢₀ E_x 𝒢₁⟩`, the second expression of the
exceptional case of (iv) in the direct estimation of the proof of Lemma 5.5
[claim_estimate_remainder_terms]. -/
def loopWordIVb : LoopExpr :=
  ⟨2, 0, 2, [], [[.det 1, .proj 0, .det 0, .lamt 0], [.det 1, .lamt 1, .res 0, .proj 1],
    [.proj 1, .res 0, .proj 0, .res 1]]⟩


/-! ## The counts `k₁`, `k₂` on words -/

/-- The letter is a resolvent. -/
private def rcR (x : LoopLetter) : Bool :=
  match x with | .res _ => true | _ => false

/-- The letter is not a `Λ̃`. -/
private def notLam (x : LoopLetter) : Bool :=
  match x with | .lamt _ => false | _ => true

/-- The number of resolvents in the maximal `Λ̃`-free suffix of a word. -/
private def lseg (l : List LoopLetter) : ℕ :=
  (l.reverse.takeWhile notLam).countP rcR

/-- The word contains no `Λ̃`. -/
private def NL (l : List LoopLetter) : Prop :=
  ∀ k : Fin 2, LoopLetter.lamt k ∉ l

/-- The summand of `LoopExpr.kk` (5.34) [Gamma_Type_1], (5.35) [Gamma_Type_2] for one loop. -/
private def kloop (o : Fin 2) (w : List LoopLetter) : ℕ :=
  if w.contains (.lamt o) then lseg ((w.rotate (w.idxOf (.lamt o))).drop 1) else 0

/-- `k_o` of an expression is the sum of the loop counts `kloop o`. -/
private theorem kk_eq (T : LoopExpr) (o : Fin 2) : T.kk o = (T.loops.map (kloop o)).sum := rfl

/-- Every letter of a `Λ̃`-free word is not a `Λ̃`. -/
private theorem notLam_of_nl {l : List LoopLetter} (h : NL l) : ∀ x ∈ l, notLam x = true := by
  intro x hx
  cases x with
  | lamt k => exact absurd hx (h k)
  | res _ => rfl
  | det _ => rfl
  | proj _ => rfl

/-- Appending a `Λ̃`-free word `Q` adds its resolvents to `lseg`. -/
private theorem lseg_append_free {P Q : List LoopLetter} (hQ : NL Q) :
    lseg (P ++ Q) = lseg P + Q.countP rcR := by
  unfold lseg
  rw [List.reverse_append, List.takeWhile_append_of_pos, List.countP_append, List.countP_reverse]
  · omega
  · intro x hx
    exact notLam_of_nl hQ x (List.mem_reverse.1 hx)

/-- After a `Λ̃` followed by a `Λ̃`-free word `Q`, `lseg` is the number of resolvents of `Q`. -/
private theorem lseg_append_lam {P Q : List LoopLetter} (k : Fin 2) (hQ : NL Q) :
    lseg (P ++ .lamt k :: Q) = Q.countP rcR := by
  unfold lseg
  rw [List.reverse_append, List.reverse_cons, List.append_assoc,
    List.takeWhile_append_of_pos, List.countP_append, List.countP_reverse]
  · simp [List.takeWhile_cons_of_neg, notLam]
  · intro x hx
    exact notLam_of_nl hQ x (List.mem_reverse.1 hx)

/-- The count of a loop `u Λ̃_o v` with `Λ̃_o` not in `u` is `lseg (v u)`: the cyclic word to the
left of `Λ̃_o`. -/
private theorem kloop_eq {u v : List LoopLetter} (o : Fin 2) (hu : LoopLetter.lamt o ∉ u) :
    kloop o (u ++ .lamt o :: v) = lseg (v ++ u) := by
  unfold kloop
  have h1 : (u ++ LoopLetter.lamt o :: v).contains (.lamt o) = true := by simp
  simp only [h1, ite_true]
  rw [List.idxOf_append_of_notMem hu, List.idxOf_cons_self, Nat.add_zero,
    List.rotate_append_length_eq]
  simp

/-- A loop without `Λ̃_o` contributes `0` to `k_o`. -/
private theorem kloop_of_not_mem {w : List LoopLetter} {o : Fin 2} (h : LoopLetter.lamt o ∉ w) :
    kloop o w = 0 := by
  unfold kloop
  have : (w.contains (.lamt o)) = false := by simpa using h
  rw [this]
  rfl

/-- One cyclic rotation of a loop with at most one `Λ̃_o` keeps its count. -/
private theorem kloop_rotate_one (o : Fin 2) (x : LoopLetter) (l : List LoopLetter)
    (h : (x :: l).count (.lamt o) ≤ 1) : kloop o (l ++ [x]) = kloop o (x :: l) := by
  by_cases hx : x = LoopLetter.lamt o
  · subst hx
    have hl : LoopLetter.lamt o ∉ l := by
      rw [← List.count_eq_zero]
      simp at h
      omega
    have e1 := kloop_eq (u := []) (v := l) o (by simp)
    have e2 := kloop_eq (u := l) (v := []) o hl
    simp only [List.nil_append] at e1
    rw [e1]
    simpa using e2
  · by_cases hm : LoopLetter.lamt o ∈ l
    · obtain ⟨u, v, rfl⟩ := List.append_of_mem hm
      have hu : LoopLetter.lamt o ∉ u := by
        rw [← List.count_eq_zero]
        simp [List.count_cons, List.count_append] at h
        omega
      have e1 := kloop_eq (u := u) (v := v ++ [x]) o hu
      have e2 := kloop_eq (u := x :: u) (v := v) o (by simp [hu, Ne.symm hx])
      simp only [List.append_assoc, List.cons_append] at e1 e2 ⊢
      rw [e1, e2]
      simp
    · rw [kloop_of_not_mem, kloop_of_not_mem]
      · simp [hm, Ne.symm hx]
      · simp [hm, Ne.symm hx]

/-- Cyclic rotation of a loop with at most one `Λ̃_o` keeps its count. -/
private theorem kloop_rotate (o : Fin 2) :
    ∀ (r : ℕ) (w : List LoopLetter), w.count (.lamt o) ≤ 1 → kloop o (w.rotate r) = kloop o w := by
  intro r
  induction r with
  | zero => intro w _; simp
  | succ r ih =>
    intro w hw
    cases w with
    | nil => simp
    | cons x l =>
      rw [List.rotate_cons_succ, ih (l ++ [x]), kloop_rotate_one o x l hw]
      rw [(List.perm_append_singleton x l).count_eq]
      exact hw

/-! ### Sums over the loops, uniqueness of the `Λ̃`, and the focused loop -/

/-- Replacing the entry `w` at position `i` of a list changes a sum of values by the difference of
the values. -/
private theorem sum_set {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (i : ℕ) (w x : α), l[i]? = some w →
      ((l.set i x).map f).sum + f w = (l.map f).sum + f x
  | [], i, w, x, h => by simp at h
  | y :: l, 0, w, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
  | y :: l, i + 1, w, x, h => by
      have := sum_set f l i w x (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- Erasing the entry `w` at position `i` of a list removes its value from a sum. -/
private theorem sum_eraseIdx {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (i : ℕ) (w : α), l[i]? = some w →
      ((l.eraseIdx i).map f).sum + f w = (l.map f).sum
  | [], i, w, h => by simp at h
  | y :: l, 0, w, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.eraseIdx_cons_zero, List.map_cons, List.sum_cons]
      omega
  | y :: l, i + 1, w, h => by
      have := sum_eraseIdx f l i w (by simpa using h)
      simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- The class `𝒯` has exactly one `Λ̃₁` and one `Λ̃₂`: the total count of each is `1`. -/
private theorem wf_counts {T : LoopExpr} (h : T.wf = true) (k : Fin 2) :
    (T.loops.map fun w => w.count (.lamt k)).sum = 1 := by
  unfold LoopExpr.wf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  fin_cases k
  · exact h.1.1.1.1
  · exact h.1.1.1.2

/-- Every loop contains each `Λ̃` at most once. -/
private theorem count_le_one {T : LoopExpr} (h : T.wf = true) {w : List LoopLetter}
    (hw : w ∈ T.loops) (k : Fin 2) : w.count (.lamt k) ≤ 1 := by
  have := wf_counts h k
  rw [← this]
  exact List.le_sum_of_mem (List.mem_map_of_mem hw)

/-- If one loop contains `Λ̃_k`, no other loop does. -/
private theorem uniq_loop {T : LoopExpr} (h : T.wf = true) (k : Fin 2) {ℓ : ℕ} {w : List LoopLetter}
    (hw : T.loops[ℓ]? = some w) (hk : LoopLetter.lamt k ∈ w) :
    ∀ j f, j ≠ ℓ → T.loops[j]? = some f → LoopLetter.lamt k ∉ f := by
  intro j f hj hf hkf
  have h1 := sum_eraseIdx (fun w => w.count (.lamt k)) T.loops ℓ w hw
  have h2 := wf_counts h k
  have h3 : 1 ≤ w.count (.lamt k) := List.count_pos_iff.2 hk
  have h4 : ((T.loops.eraseIdx ℓ).map fun w => w.count (.lamt k)).sum = 0 := by omega
  rw [List.sum_eq_zero_iff] at h4
  have h5 : f ∈ T.loops.eraseIdx ℓ := List.mem_eraseIdx_iff_getElem?.2 ⟨j, hj, hf⟩
  have := h4 _ (List.mem_map_of_mem h5)
  have := List.count_eq_zero.1 this
  exact this hkf

/-- `k_o` is the count in the unique loop that contains `Λ̃_o`. -/
private theorem kk_eq_kloop {T : LoopExpr} (h : T.wf = true) (o : Fin 2) {ℓ : ℕ}
    {w : List LoopLetter} (hw : T.loops[ℓ]? = some w) (ho : LoopLetter.lamt o ∈ w) :
    T.kk o = kloop o w := by
  rw [kk_eq]
  have h1 := sum_eraseIdx (kloop o) T.loops ℓ w hw
  have h4 : ((T.loops.eraseIdx ℓ).map (kloop o)).sum = 0 := by
    rw [List.sum_eq_zero_iff]
    intro x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, hjf⟩ := List.mem_eraseIdx_iff_getElem?.1 hf
    exact kloop_of_not_mem (uniq_loop h o hw ho j f hj hjf)
  omega

/-- The data returned by `focus`: the loop `w` at `ℓ` rotated by `r` is `𝒢_a · tl`, and `tl` has
`Λ̃_o` at a position `j₀`, with no resolvent before it; `o` is `0` when `k₁ ≥ 1`, else `1`, and
`k_o ≥ 1`. -/
private theorem focus_spec2 {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ (o : Fin 2) (w : List LoopLetter) (r j₀ : ℕ),
      ((o = 0 ∧ 1 ≤ T.kk 0) ∨ (o = 1 ∧ T.kk 0 = 0)) ∧ 1 ≤ T.kk o ∧
      T.loops[ℓ]? = some w ∧ w.rotate r = .res a :: tl ∧
      tl[j₀]? = some (.lamt o) ∧ ∀ k < j₀, ∀ x, tl[k]? = some x → rcR x = false := by
  unfold LoopExpr.focus at h
  dsimp only at h
  generalize ho : (if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = o at h
  have hoo : (o = 0 ∧ 1 ≤ T.kk 0) ∨ (o = 1 ∧ T.kk 0 = 0) := by
    by_cases hk : 1 ≤ T.kk 0
    · left
      simp only [hk, ↓reduceIte] at ho
      exact ⟨ho.symm, hk⟩
    · right
      simp only [hk, ↓reduceIte] at ho
      exact ⟨ho.symm, by omega⟩
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i a' tl' hrot
        split at h
        · rename_i hko
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hlt, hwe⟩ := List.getElem?_eq_some_iff.1 hw
          have h1 := List.findIdx_getElem (p := fun w => w.contains (LoopLetter.lamt o))
            (xs := T.loops) (w := hlt)
          rw [hwe] at h1
          have h2 : LoopLetter.lamt o ∈ w := by simpa using h1
          have hi : w.idxOf (LoopLetter.lamt o) < w.length := List.idxOf_lt_length_iff.2 h2
          have hwi := List.getElem_idxOf hi
          obtain ⟨hpr, j₁, hj₁, hLj, hpre⟩ := List.find?_eq_some_iff_getElem.1 hr
          have hj₁' : j₁ < w.length := by simpa using hj₁
          simp only [List.getElem_map, List.getElem_range] at hLj hpre
          have hj₂ : j₁ + 1 < w.length := by
            by_contra hc
            have : j₁ = w.length - 1 := by omega
            subst this
            have : r = w.idxOf (LoopLetter.lamt o) := by
              rw [← hLj, show w.idxOf (LoopLetter.lamt o) + w.length - 1 - (w.length - 1) =
                w.idxOf (LoopLetter.lamt o) by omega, Nat.mod_eq_of_lt hi]
            rw [this, List.getElem?_eq_getElem hi, hwi] at hpr
            simp at hpr
          have htl : ∀ k, k + 1 < w.length → tl'[k]? = w[(k + 1 + r) % w.length]? := by
            intro k hk
            have := List.getElem?_rotate (l := w) (n := r) (m := k + 1) hk
            rw [hrot] at this
            simpa using this
          refine ⟨o, w, r, j₁, hoo, hko, hw, hrot, ?_, ?_⟩
          · rw [htl j₁ hj₂, ← hLj, Nat.add_mod_mod]
            have : j₁ + 1 + (w.idxOf (LoopLetter.lamt o) + w.length - 1 - j₁) =
                w.idxOf (LoopLetter.lamt o) + w.length := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi, List.getElem?_eq_getElem hi, hwi]
          · intro k hk x hx
            rw [htl k (by omega), ← hLj, Nat.add_mod_mod] at hx
            have h3 := hpre (j₁ - 1 - k) (by omega)
            have : k + 1 + (w.idxOf (LoopLetter.lamt o) + w.length - 1 - j₁) =
                w.idxOf (LoopLetter.lamt o) + w.length - 1 - (j₁ - 1 - k) := by omega
            rw [this] at hx
            rw [hx] at h3
            cases x <;> simp_all [rcR]
        · cases h
      · cases h

/-! ### The focused loop in normal form -/

/-- The focused loop `w` of an expression, cyclically `𝒢_a B Λ̃_o Π`, with `B` free of resolvents
and of `Λ̃` (the guarantee `k_o ≥ 1` of (5.38) [explicit_cT]), and `o ≠ o'`. -/
private structure Foc (w : List LoopLetter) (a : Fin 2) (B Y : List LoopLetter) (o o' : Fin 2) :
    Prop where
  ne : o ≠ o'
  rot : ∃ r, w.rotate r = .res a :: (B ++ .lamt o :: Y)
  nlB : NL B
  rsB : B.countP rcR = 0
  cnt : ∀ k, w.count (.lamt k) ≤ 1

/-- Two distinct elements of `Fin 2` exhaust it. -/
private theorem fin2_cases {o o' : Fin 2} (h : o ≠ o') (k : Fin 2) : k = o ∨ k = o' := by
  revert o o' k
  decide

/-- The counts of `Λ̃` in the unrotated `tl = B Λ̃_o Y` are at most one. -/
private theorem Foc.cnt_tl {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter} {o o' : Fin 2}
    (F : Foc w a B Y o o') (k : Fin 2) : (B ++ .lamt o :: Y).count (.lamt k) ≤ 1 := by
  obtain ⟨r, hr⟩ := F.rot
  have h1 := F.cnt k
  rw [← (List.rotate_perm w r).count_eq, hr] at h1
  simpa using h1

/-- `Λ̃_o` occurs once in the focused loop, so not in `Π`. -/
private theorem Foc.not_mem_Pi {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') : LoopLetter.lamt o ∉ Y := by
  have := F.cnt_tl o
  rw [← List.count_eq_zero]
  simp [List.count_append] at this
  omega

/-- The count `k_o` of the focused loop `𝒢_a B Λ̃_o Π` is `lseg Π + 1`: the resolvents of the
`Λ̃`-free suffix of `Π`, and `𝒢_a`. -/
private theorem Foc.old_o {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter} {o o' : Fin 2}
    (F : Foc w a B Y o o') : kloop o w = lseg Y + 1 := by
  obtain ⟨r, hr⟩ := F.rot
  rw [← kloop_rotate o r w (F.cnt o), hr]
  have hB : LoopLetter.lamt o ∉ LoopLetter.res a :: B := by
    simp [F.nlB o]
  have := kloop_eq (u := LoopLetter.res a :: B) (v := Y) o hB
  simp only [List.cons_append] at this
  rw [this]
  have hn : NL (LoopLetter.res a :: B) := by
    intro k
    simpa using F.nlB k
  rw [lseg_append_free hn]
  simp [List.countP_cons, F.rsB, rcR]

/-- The word of the new focused loop of `𝔯`, `𝔠₁`, `𝔭₁`, `𝔭₂`: `k_o` becomes `lseg Π` plus the
resolvents of the appended letters `X`. -/
private theorem Foc.new_o {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter} {o o' : Fin 2}
    (F : Foc w a B Y o o') {X : List LoopLetter} (hX : NL X) :
    kloop o (.det a :: (B ++ .lamt o :: Y) ++ X) = lseg Y + X.countP rcR := by
  have hB : LoopLetter.lamt o ∉ LoopLetter.det a :: B := by
    simp [F.nlB o]
  have h1 : (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ X) =
      (LoopLetter.det a :: B) ++ LoopLetter.lamt o :: (Y ++ X) := by simp
  rw [h1, kloop_eq o hB]
  have hn : NL (X ++ LoopLetter.det a :: B) := by
    intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · exact hX k hk
    · rcases List.mem_cons.1 hk with hk | hk
      · cases hk
      · exact F.nlB k hk
  have h2 : (Y ++ X) ++ LoopLetter.det a :: B = Y ++ (X ++ LoopLetter.det a :: B) := by simp
  rw [h2, lseg_append_free hn]
  simp [List.countP_append, F.rsB, rcR]

/-- If a word `Y 𝒢_a B` with resolvent-free `B` has a resolvent in its `Λ̃`-free suffix, then `B`
contains no `Λ̃`. -/
private theorem nl_of_lseg_pos {B Y : List LoopLetter} {a : Fin 2} (hB : B.countP rcR = 0)
    (h : 1 ≤ lseg (Y ++ .res a :: B)) : NL B := by
  unfold lseg at h
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.takeWhile_append] at h
  split_ifs at h with hlen
  · have hpre := (List.takeWhile_prefix (l := B.reverse) notLam).eq_of_length hlen
    intro k hk
    have : notLam (LoopLetter.lamt k) = true := by
      have h2 : LoopLetter.lamt k ∈ List.takeWhile notLam B.reverse := by
        rw [hpre]; exact List.mem_reverse.2 hk
      exact List.mem_takeWhile_imp h2
    simp [notLam] at this
  · exfalso
    have h1 := (List.takeWhile_sublist (l := B.reverse) notLam).countP_le (p := rcR)
    rw [List.countP_reverse, hB] at h1
    omega

/-- If `Π = Π₁ Λ̃_{o'} Π₂`, the focused loop has `k_{o'} = ` the resolvents of `Π₁`, and `Π₁`,
`Π₂` are `Λ̃`-free. -/
private theorem Foc.old_o' {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') {Y₁ Y₂ : List LoopLetter}
    (hY : Y = Y₁ ++ .lamt o' :: Y₂) : NL Y₁ ∧ NL Y₂ ∧ kloop o' w = Y₁.countP rcR := by
  subst hY
  have hc := F.cnt_tl
  have h0 := hc o
  have h1 := hc o'
  have hne : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => F.ne (LoopLetter.lamt.inj h)
  have hnB := F.nlB
  have e0 : (B ++ LoopLetter.lamt o :: (Y₁ ++ LoopLetter.lamt o' :: Y₂)).count (.lamt o) =
      1 + Y₁.count (.lamt o) + Y₂.count (.lamt o) := by
    simp [List.count_append, List.count_eq_zero.2 (hnB o), hne.symm]
    omega
  have e1 : (B ++ LoopLetter.lamt o :: (Y₁ ++ LoopLetter.lamt o' :: Y₂)).count (.lamt o') =
      1 + Y₁.count (.lamt o') + Y₂.count (.lamt o') := by
    simp [List.count_append, List.count_eq_zero.2 (hnB o'), hne]
    omega
  have hn1 : NL Y₁ := by
    intro k hk
    rcases fin2_cases F.ne k with rfl | rfl
    · have := List.count_pos_iff.2 hk; omega
    · have := List.count_pos_iff.2 hk; omega
  have hn2 : NL Y₂ := by
    intro k hk
    rcases fin2_cases F.ne k with rfl | rfl
    · have := List.count_pos_iff.2 hk; omega
    · have := List.count_pos_iff.2 hk; omega
  refine ⟨hn1, hn2, ?_⟩
  obtain ⟨r, hr⟩ := F.rot
  rw [← kloop_rotate o' r w (F.cnt o'), hr]
  have hu : LoopLetter.lamt o' ∉ LoopLetter.res a :: (B ++ LoopLetter.lamt o :: Y₁) := by
    simp [hnB o', hne.symm, hn1 o']
  have h2 : LoopLetter.res a :: (B ++ LoopLetter.lamt o :: (Y₁ ++ LoopLetter.lamt o' :: Y₂)) =
      (LoopLetter.res a :: (B ++ LoopLetter.lamt o :: Y₁)) ++ LoopLetter.lamt o' :: Y₂ := by simp
  rw [h2, kloop_eq o' hu]
  have h3 : Y₂ ++ LoopLetter.res a :: (B ++ LoopLetter.lamt o :: Y₁) =
      (Y₂ ++ LoopLetter.res a :: B) ++ LoopLetter.lamt o :: Y₁ := by simp
  rw [h3, lseg_append_lam o hn1]

/-- The count at `Λ̃_{o'}` of a loop `𝔐_a B Λ̃_o Π₁ Λ̃_{o'} Z X` is the number of resolvents in the
`Λ̃`-free `Π₁`. -/
private theorem kloop_lam_form {a : Fin 2} {B Y₁ Z X : List LoopLetter} {o o' : Fin 2}
    (hne : o ≠ o') (hB : NL B) (hY₁ : NL Y₁) :
    kloop o' (.det a :: (B ++ .lamt o :: (Y₁ ++ .lamt o' :: Z)) ++ X) = Y₁.countP rcR := by
  have hne' : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => hne (LoopLetter.lamt.inj h)
  have hu : LoopLetter.lamt o' ∉ LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y₁) := by
    simp [hB o', hne'.symm, hY₁ o']
  have h2 : LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (Y₁ ++ LoopLetter.lamt o' :: Z)) ++ X =
      (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y₁)) ++ LoopLetter.lamt o' :: (Z ++ X) := by
    simp
  rw [h2, kloop_eq o' hu]
  have h3 : (Z ++ X) ++ LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y₁) =
      ((Z ++ X) ++ LoopLetter.det a :: B) ++ LoopLetter.lamt o :: Y₁ := by simp
  rw [h3, lseg_append_lam o hY₁]

/-- The count at `Λ̃_{o'}` of the new focused loop `𝔐_a B Λ̃_o Π X`. -/
private theorem Foc.new_o' {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') {Y₁ Y₂ : List LoopLetter}
    (hY : Y = Y₁ ++ .lamt o' :: Y₂) (X : List LoopLetter) :
    kloop o' (.det a :: (B ++ .lamt o :: Y) ++ X) = Y₁.countP rcR := by
  obtain ⟨hn1, -, -⟩ := F.old_o' hY
  subst hY
  exact kloop_lam_form F.ne F.nlB hn1

/-- `Λ̃_{o'}` is not in the focused loop when it is not in `Π`. -/
private theorem Foc.not_mem_w {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') (h : LoopLetter.lamt o' ∉ Y) :
    LoopLetter.lamt o' ∉ w := by
  obtain ⟨r, hr⟩ := F.rot
  intro hm
  have : LoopLetter.lamt o' ∈ w.rotate r := List.mem_rotate.2 hm
  rw [hr] at this
  have hne : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => F.ne (LoopLetter.lamt.inj h)
  simp [F.nlB o', hne.symm, h] at this

/-- The focused loop of an expression of the class `𝒯` in the normal form `Foc`, with the case of
(5.38) [explicit_cT]: `Λ̃₁` is focused when `k₁ ≥ 1`, else `Λ̃₂` and `k₁ = 0`. -/
private theorem focus_foc {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (h : T.focus = some (ℓ, a, tl)) :
    ∃ (o o' : Fin 2) (w B Y : List LoopLetter),
      ((o = 0 ∧ o' = 1 ∧ 1 ≤ T.kk 0) ∨ (o = 1 ∧ o' = 0 ∧ T.kk 0 = 0)) ∧
      T.loops[ℓ]? = some w ∧ tl = B ++ .lamt o :: Y ∧ Foc w a B Y o o' := by
  obtain ⟨o, w, r, j₀, hoo, hko, hw, hrot, hj₀, hpre⟩ := focus_spec2 h
  obtain ⟨o', hne, hoo'⟩ : ∃ o' : Fin 2, o ≠ o' ∧
      ((o = 0 ∧ o' = 1 ∧ 1 ≤ T.kk 0) ∨ (o = 1 ∧ o' = 0 ∧ T.kk 0 = 0)) := by
    rcases hoo with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
    · exact ⟨1, by decide, Or.inl ⟨rfl, rfl, h1⟩⟩
    · exact ⟨0, by decide, Or.inr ⟨rfl, rfl, h1⟩⟩
  obtain ⟨hj, hlam⟩ := List.getElem?_eq_some_iff.1 hj₀
  have hsplit : tl = tl.take j₀ ++ .lamt o :: tl.drop (j₀ + 1) := by
    conv_lhs => rw [← List.take_append_drop j₀ tl, List.drop_eq_getElem_cons hj, hlam]
  generalize hB : tl.take j₀ = B at hsplit
  generalize hY : tl.drop (j₀ + 1) = Y at hsplit
  have hrs : B.countP rcR = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    rw [← hB] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hx
    have hi' : i < j₀ := lt_of_lt_of_le hi (min_le_left _ _)
    have := hpre i hi' tl[i] (List.getElem?_eq_getElem (by omega))
    simp [this]
  have hwm : w ∈ T.loops := List.mem_of_getElem? hw
  have hcnt : ∀ k, w.count (.lamt k) ≤ 1 := count_le_one hT hwm
  have hlo : LoopLetter.lamt o ∈ w := by
    have : LoopLetter.lamt o ∈ w.rotate r := by
      rw [hrot]
      exact List.mem_cons_of_mem _ (List.mem_of_getElem? hj₀)
    exact List.mem_rotate.1 this
  have hc1 : (LoopLetter.res a :: tl).count (.lamt o) ≤ 1 := by
    have := hcnt o
    rwa [← (List.rotate_perm w r).count_eq, hrot] at this
  have hBo : LoopLetter.lamt o ∉ B := by
    rw [← List.count_eq_zero]
    have : (B ++ LoopLetter.lamt o :: Y).count (.lamt o) ≤ 1 := by
      rw [← hsplit]
      simpa using hc1
    simp [List.count_append] at this
    omega
  have hk1 : 1 ≤ kloop o w := by
    rw [← kk_eq_kloop hT o hw hlo]
    exact hko
  have hkl : kloop o w = lseg (Y ++ .res a :: B) := by
    rw [← kloop_rotate o r w (hcnt o), hrot, hsplit]
    have := kloop_eq (u := LoopLetter.res a :: B) (v := Y) o (by simp [hBo])
    simpa using this
  have hnl : NL B := nl_of_lseg_pos hrs (hkl ▸ hk1)
  exact ⟨o, o', w, B, Y, hoo', hw, hsplit, ⟨hne, ⟨r, by rw [hrot, hsplit]⟩, hnl, hrs, hcnt⟩⟩

/-- The count at `Λ̃_{o'}` is unchanged when letters `X` without `Λ̃` are appended to the focused
loop. -/
private theorem Foc.o'_same {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') {X : List LoopLetter} (hX : NL X) :
    kloop o' w = kloop o' (.det a :: (B ++ .lamt o :: Y) ++ X) := by
  by_cases hm : LoopLetter.lamt o' ∈ Y
  · obtain ⟨Y₁, Y₂, hY⟩ := List.append_of_mem hm
    rw [(F.old_o' hY).2.2, F.new_o' hY X]
  · have hne : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => F.ne (LoopLetter.lamt.inj h)
    rw [kloop_of_not_mem (F.not_mem_w hm), kloop_of_not_mem]
    simp [F.nlB o', hne.symm, hm, hX o']


/-! ## Type I and Type II -/

/-- Each `Λ̃_k` lies in one loop of the class `𝒯`: two loops that contain it are equal. -/
private theorem loop_unique {T : LoopExpr} (h : T.wf = true) (k : Fin 2) {w₁ w₂ : List LoopLetter}
    (h1 : w₁ ∈ T.loops) (h2 : w₂ ∈ T.loops) (k1 : LoopLetter.lamt k ∈ w₁)
    (k2 : LoopLetter.lamt k ∈ w₂) : w₁ = w₂ := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h2
  by_cases hij : j = i
  · subst hij
    rw [hi] at hj
    exact Option.some.inj hj
  · exact absurd k2 (uniq_loop h k hi k1 j w₂ hij hj)

/-- Type I of (5.34) [Gamma_Type_1]: for a loop `w` that contains `Λ̃_o`, the expression is of
Type I exactly when `w` also contains the other `Λ̃`. -/
private theorem typeI_iff {T : LoopExpr} (hT : T.wf = true) {w : List LoopLetter}
    (hw : w ∈ T.loops) {o o' : Fin 2} (hne : o ≠ o') (ho : LoopLetter.lamt o ∈ w) :
    T.typeI = true ↔ LoopLetter.lamt o' ∈ w := by
  unfold LoopExpr.typeI
  rw [List.any_eq_true]
  simp only [Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨w₀, hw₀, h0, h1⟩
    have hk : ∀ k : Fin 2, LoopLetter.lamt k ∈ w₀ := by
      intro k
      fin_cases k
      · exact h0
      · exact h1
    have := loop_unique hT o hw₀ hw (hk o) ho
    subst this
    exact hk o'
  · intro ho'
    have hk : ∀ k : Fin 2, LoopLetter.lamt k ∈ w := by
      intro k
      rcases fin2_cases hne k with rfl | rfl
      · exact ho
      · exact ho'
    exact ⟨w, hw, hk 0, hk 1⟩

/-- Two expressions of the class with loops `w`, `w'` that contain the same `Λ̃_o`, and the other
`Λ̃` in `w` exactly when in `w'`, have the same type. -/
private theorem typeI_eq {T T' : LoopExpr} (hT : T.wf = true) (hT' : T'.wf = true)
    {w w' : List LoopLetter} (hw : w ∈ T.loops) (hw' : w' ∈ T'.loops) {o o' : Fin 2}
    (hne : o ≠ o') (ho : LoopLetter.lamt o ∈ w) (ho' : LoopLetter.lamt o ∈ w')
    (hiff : LoopLetter.lamt o' ∈ w ↔ LoopLetter.lamt o' ∈ w') : T'.typeI = T.typeI := by
  have h1 := typeI_iff hT hw hne ho
  have h2 := typeI_iff hT' hw' hne ho'
  rw [Bool.eq_iff_iff, h2, h1]
  exact hiff.symm

/-- `Λ̃_{o'}` lies in the focused loop exactly when it lies in `Π`. -/
private theorem Foc.mem_iff {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') :
    LoopLetter.lamt o' ∈ w ↔ LoopLetter.lamt o' ∈ Y := by
  constructor
  · intro hm
    by_contra hc
    exact F.not_mem_w hc hm
  · intro hm
    obtain ⟨r, hr⟩ := F.rot
    have : LoopLetter.lamt o' ∈ w.rotate r := by rw [hr]; simp [hm]
    exact List.mem_rotate.1 this

/-- The new focused loop `𝔐_a B Λ̃_o Π X` with `Λ̃`-free `X` contains `Λ̃_{o'}` exactly when `Π`
does. -/
private theorem Foc.mem_new {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') {X : List LoopLetter} (hX : NL X) :
    LoopLetter.lamt o' ∈ (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ X) ↔
      LoopLetter.lamt o' ∈ Y := by
  have hne : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => F.ne (LoopLetter.lamt.inj h)
  simp [F.nlB o', hne.symm, hX o']

/-- The property that a Type II expression (`Λ̃₁`, `Λ̃₂` in different loops) with `k₁ ≥ 1` has
`k₂ ≥ 2`. -/
private def IT (T : LoopExpr) : Prop :=
  T.typeI = false → 1 ≤ T.kk 0 → 2 ≤ T.kk 1

/-- The facts on `k₁`, `k₂` and on the type carried by one step `T → T'`: `k₂ ≥ 1` stays when
`k₁ ≥ 1`; `k₂ ≥ 1` after a step other than `𝔯` (`nonrep`) from `k₁ = 0`; the property `IT`. -/
private def KStep (T T' : LoopExpr) (nonrep : Prop) : Prop :=
  (1 ≤ T.kk 0 → 1 ≤ T.kk 1 → 1 ≤ T'.kk 1) ∧ (nonrep → T.kk 0 = 0 → 1 ≤ T'.kk 1) ∧
    (IT T → IT T')

/-- `KStep` with the trivial side condition implies it for every side condition. -/
private theorem KStep.of_true {T T' : LoopExpr} (p : Prop) (h : KStep T T' True) : KStep T T' p :=
  ⟨h.1, fun _ => h.2.1 trivial, h.2.2⟩

/-- The steps `𝔯`, `𝔠₁`, `𝔭₁`, `𝔭₂` (with `Λ̃`-free `f`) replace the focused loop by
`𝔐_a tl X` with `Λ̃`-free `X`. -/
private theorem kstep_set {T T' : LoopExpr} (hT : T.wf = true) (hT' : T'.wf = true) {ℓ : ℕ}
    {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (X w' : List LoopLetter) (hX : NL X)
    (hw' : w' = .det a :: tl ++ X) (nonrep : Prop) (hres : nonrep → 1 ≤ X.countP rcR)
    (hL : ∀ o'', T'.kk o'' = ((T.loops.set ℓ w').map (kloop o'')).sum)
    (hmem : ℓ < T.loops.length → w' ∈ T'.loops) : KStep T T' nonrep := by
  obtain ⟨o, o', w, B, Y, hoo, hw, rfl, F⟩ := focus_foc hT hf
  subst hw'
  have h1 := fun o'' => sum_set (kloop o'') T.loops ℓ w (.det a :: (B ++ .lamt o :: Y) ++ X) hw
  have e1 := h1 o
  have e2 := h1 o'
  rw [← hL o, F.old_o, F.new_o hX] at e1
  rw [← hL o', ← F.o'_same hX] at e2
  have k1 := kk_eq T o
  have k2 := kk_eq T o'
  have hlo : LoopLetter.lamt o ∈ w := by
    obtain ⟨r, hr⟩ := F.rot
    have : LoopLetter.lamt o ∈ w.rotate r := by rw [hr]; simp
    exact List.mem_rotate.1 this
  have k3 := kk_eq_kloop hT o hw hlo
  rw [F.old_o] at k3
  have hwm : w ∈ T.loops := List.mem_of_getElem? hw
  have hlt : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hty : T'.typeI = T.typeI := by
    refine typeI_eq hT hT' hwm (hmem hlt) F.ne hlo (by simp) ?_
    rw [F.mem_iff, F.mem_new hX]
  rcases hoo with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
  · refine ⟨fun _ h => ?_, fun _ h => by omega, fun hI hty' h1' => ?_⟩
    · omega
    · have := hI (hty.symm.trans hty') hk
      omega
  · refine ⟨fun h => by omega, fun hn _ => ?_, fun _ _ h1' => ?_⟩
    · have := hres hn
      omega
    · omega

/-- A loop with a unique `Λ̃_{o'}`, no other `Λ̃`, and a resolvent has `k_{o'} ≥ 1`. -/
private theorem kloop_pos {f : List LoopLetter} {o' : Fin 2} (hm : LoopLetter.lamt o' ∈ f)
    (hc : f.count (.lamt o') ≤ 1) (ho : ∀ k, k ≠ o' → LoopLetter.lamt k ∉ f) {b : Fin 2}
    (hb : LoopLetter.res b ∈ f) : 1 ≤ kloop o' f := by
  obtain ⟨f₁, f₂, rfl⟩ := List.append_of_mem hm
  have hc' : f₁.count (.lamt o') + f₂.count (.lamt o') = 0 := by
    simp [List.count_append] at hc
    omega
  have hn1 : NL f₁ := by
    intro k hk
    by_cases hko : k = o'
    · subst hko
      have := List.count_pos_iff.2 hk
      omega
    · exact ho k hko (by simp [hk])
  have hn2 : NL f₂ := by
    intro k hk
    by_cases hko : k = o'
    · subst hko
      have := List.count_pos_iff.2 hk
      omega
    · exact ho k hko (by simp [hk])
  rw [kloop_eq o' (hn1 o'), lseg_append_free hn1]
  have h0 : lseg f₂ = f₂.countP rcR := by
    have := lseg_append_free (P := []) hn2
    simpa [lseg] using this
  rw [h0]
  have : 0 < (f₁ ++ f₂).countP rcR := by
    rw [List.countP_pos_iff]
    refine ⟨.res b, ?_, rfl⟩
    rcases List.mem_append.1 hb with h | h
    · exact List.mem_append_left _ h
    · rcases List.mem_cons.1 h with h | h
      · cases h
      · exact List.mem_append_right _ h
  rw [List.countP_append] at this
  omega

/-- If `Λ̃_{o'}` is not in the focused loop, `Π` has no `Λ̃`. -/
private theorem Foc.nl_Y {w : List LoopLetter} {a : Fin 2} {B Y : List LoopLetter}
    {o o' : Fin 2} (F : Foc w a B Y o o') (h : LoopLetter.lamt o' ∉ w) : NL Y := by
  intro k hk
  rcases fin2_cases F.ne k with rfl | rfl
  · exact F.not_mem_Pi hk
  · apply h
    obtain ⟨r, hr⟩ := F.rot
    have : LoopLetter.lamt k ∈ w.rotate r := by rw [hr]; simp [hk]
    exact List.mem_rotate.1 this

/-- A `Λ̃`-free word rotated stays `Λ̃`-free. -/
private theorem nl_rotate {f : List LoopLetter} (h : NL f) (q : ℕ) : NL (f.rotate q) := by
  intro k hk
  exact h k (List.mem_rotate.1 hk)

/-- Both sides of the unique `Λ̃_{o'}` of a word with no other `Λ̃` are `Λ̃`-free. -/
private theorem nl_split {g₁ g₂ : List LoopLetter} {o' : Fin 2}
    (hc : (g₁ ++ .lamt o' :: g₂).count (.lamt o') ≤ 1)
    (ho : ∀ k, k ≠ o' → LoopLetter.lamt k ∉ g₁ ++ .lamt o' :: g₂) : NL g₁ ∧ NL g₂ := by
  have hc' : g₁.count (.lamt o') + g₂.count (.lamt o') = 0 := by
    simp [List.count_append] at hc
    omega
  constructor
  · intro k hk
    by_cases hko : k = o'
    · subst hko
      have := List.count_pos_iff.2 hk
      omega
    · exact ho k hko (by simp [hk])
  · intro k hk
    by_cases hko : k = o'
    · subst hko
      have := List.count_pos_iff.2 hk
      omega
    · exact ho k hko (by simp [hk])

/-- Concatenation of `Λ̃`-free words is `Λ̃`-free. -/
private theorem nl_append {P Q : List LoopLetter} (hP : NL P) (hQ : NL Q) : NL (P ++ Q) := by
  intro k hk
  rcases List.mem_append.1 hk with h | h
  exacts [hP k h, hQ k h]

/-- A non-`Λ̃` letter in front of a `Λ̃`-free word. -/
private theorem nl_cons {x : LoopLetter} {l : List LoopLetter} (hx : ∀ k, x ≠ .lamt k)
    (h : NL l) : NL (x :: l) := by
  intro k hk
  rcases List.mem_cons.1 hk with h' | h'
  exacts [hx k h'.symm, h k h']

/-- The words `𝒢_c E_n` have no `Λ̃`. -/
private theorem nl_pair (c : Fin 2) (n : ℕ) : NL [LoopLetter.res c, LoopLetter.proj n] := by
  intro k hk
  simp at hk

/-- The step `𝔭₂` (5.46) [splug2_def]: the loop `f` of another position is rotated into the
focused loop. -/
private theorem kstep_plug2 {T T' : LoopExpr} (hT : T.wf = true) (hT' : T'.wf = true) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) {j : ℕ} (hj : j ≠ ℓ)
    {f : List LoopLetter} (hfj : T.loops[j]? = some f) {q : ℕ} {b : Fin 2}
    (hq : f[q]? = some (.res b)) (n : ℕ)
    (hloops : T'.loops = (T.loops.set ℓ (.det a :: tl ++ [.res a, .proj n] ++ f.rotate q ++
      [.res b, .proj n])).eraseIdx j) : KStep T T' True := by
  have hL : ∀ o'', T'.kk o'' = (((T.loops.set ℓ (.det a :: tl ++ [.res a, .proj n] ++
      f.rotate q ++ [.res b, .proj n])).eraseIdx j).map (kloop o'')).sum :=
    fun o'' => by rw [kk_eq, hloops]
  obtain ⟨o, o', w, B, Y, hoo, hw, rfl, F⟩ := focus_foc hT hf
  have hlo : LoopLetter.lamt o ∈ w := by
    obtain ⟨r, hr⟩ := F.rot
    have : LoopLetter.lamt o ∈ w.rotate r := by rw [hr]; simp
    exact List.mem_rotate.1 this
  have hfo : LoopLetter.lamt o ∉ f := uniq_loop hT o hw hlo j f hj hfj
  have hfm : f ∈ T.loops := List.mem_of_getElem? hfj
  have hfc : ∀ k, f.count (.lamt k) ≤ 1 := count_le_one hT hfm
  have hS : (T.loops.set ℓ (.det a :: (B ++ .lamt o :: Y) ++ ([.res a, .proj n] ++ f.rotate q ++
      [.res b, .proj n])))[j]? = some f :=
    (List.getElem?_set_ne (fun h => hj h.symm)).trans hfj
  have e1 := sum_set (kloop o) T.loops ℓ w (.det a :: (B ++ .lamt o :: Y) ++ ([.res a, .proj n] ++
    f.rotate q ++ [.res b, .proj n])) hw
  have e1' := sum_set (kloop o') T.loops ℓ w (.det a :: (B ++ .lamt o :: Y) ++ ([.res a, .proj n] ++
    f.rotate q ++ [.res b, .proj n])) hw
  have e2 := sum_eraseIdx (kloop o) _ j f hS
  have e2' := sum_eraseIdx (kloop o') _ j f hS
  have hw'eq : (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ ([LoopLetter.res a,
      LoopLetter.proj n] ++ f.rotate q ++ [LoopLetter.res b, LoopLetter.proj n])) =
      LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ [LoopLetter.res a, LoopLetter.proj n] ++
      f.rotate q ++ [LoopLetter.res b, LoopLetter.proj n] := by simp
  rw [hw'eq] at e1 e1' e2 e2'
  have hk := fun o'' => hL o''
  have hlt : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hmem : (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ [LoopLetter.res a,
      LoopLetter.proj n] ++ f.rotate q ++ [LoopLetter.res b, LoopLetter.proj n]) ∈ T'.loops := by
    rw [hloops, List.mem_eraseIdx_iff_getElem?]
    refine ⟨ℓ, fun h => hj h.symm, ?_⟩
    rw [List.getElem?_set_self hlt]
  by_cases hfl : ∃ k, LoopLetter.lamt k ∈ f
  · -- `f` carries the other `Λ̃`
    obtain ⟨k, hk0⟩ := hfl
    have hko : k = o' := by
      rcases fin2_cases F.ne k with rfl | rfl
      · exact absurd hk0 hfo
      · rfl
    subst hko
    have hTy : T'.typeI = true := by
      refine (typeI_iff hT' hmem F.ne (by simp)).2 ?_
      simp [hk0]
    have hwo' : LoopLetter.lamt k ∉ w :=
      uniq_loop hT k hfj hk0 ℓ w (Ne.symm hj) hw
    have hnY : NL Y := F.nl_Y hwo'
    have hfo2 : ∀ k', k' ≠ k → LoopLetter.lamt k' ∉ f := by
      intro k' hk'
      rcases fin2_cases F.ne k' with rfl | rfl
      · exact hfo
      · exact absurd rfl hk'
    have hmr : LoopLetter.lamt k ∈ f.rotate q := List.mem_rotate.2 hk0
    obtain ⟨g₁, g₂, hg⟩ := List.append_of_mem hmr
    have hcr : (f.rotate q).count (.lamt k) ≤ 1 := by
      rw [(List.rotate_perm f q).count_eq]
      exact hfc k
    have hnr : ∀ k', k' ≠ k → LoopLetter.lamt k' ∉ g₁ ++ LoopLetter.lamt k :: g₂ := by
      intro k' hk'
      rw [← hg]
      exact fun h => hfo2 k' hk' (List.mem_rotate.1 h)
    rw [hg] at hcr
    obtain ⟨hg1, hg2⟩ := nl_split hcr hnr
    have hrb : LoopLetter.res b ∈ f := List.mem_of_getElem? hq
    have hkpos := kloop_pos hk0 (hfc _) hfo2 hrb
    have hnQ : NL (g₂ ++ [LoopLetter.res b, LoopLetter.proj n] ++ LoopLetter.det a :: B) :=
      nl_append (nl_append hg2 (nl_pair b n)) (nl_cons (by simp) F.nlB)
    have hP1 : 1 ≤ kloop o (.det a :: (B ++ .lamt o :: Y) ++ [.res a, .proj n] ++
        f.rotate q ++ [.res b, .proj n]) := by
      have hu : LoopLetter.lamt o ∉ LoopLetter.det a :: B := by simp [F.nlB o]
      have h1 : (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ [LoopLetter.res a,
          LoopLetter.proj n] ++ f.rotate q ++ [LoopLetter.res b, LoopLetter.proj n]) =
          (LoopLetter.det a :: B) ++ LoopLetter.lamt o :: ((Y ++ [LoopLetter.res a,
            LoopLetter.proj n] ++ g₁) ++ LoopLetter.lamt k :: (g₂ ++ [LoopLetter.res b,
            LoopLetter.proj n])) := by
        rw [hg]; simp
      rw [h1, kloop_eq o hu]
      have h2 : ((Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁) ++ LoopLetter.lamt k ::
          (g₂ ++ [LoopLetter.res b, LoopLetter.proj n])) ++ LoopLetter.det a :: B =
          (Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁) ++ LoopLetter.lamt k ::
            (g₂ ++ [LoopLetter.res b, LoopLetter.proj n] ++ LoopLetter.det a :: B) := by simp
      rw [h2, lseg_append_lam k hnQ]
      have : 0 < (g₂ ++ [LoopLetter.res b, LoopLetter.proj n] ++ LoopLetter.det a :: B).countP
          rcR := by
        rw [List.countP_pos_iff]
        exact ⟨.res b, by simp, rfl⟩
      omega
    have hP2 : 1 ≤ kloop k (.det a :: (B ++ .lamt o :: Y) ++ [.res a, .proj n] ++
        f.rotate q ++ [.res b, .proj n]) := by
      have hne' : LoopLetter.lamt o ≠ LoopLetter.lamt k := fun h => F.ne (LoopLetter.lamt.inj h)
      have hnQ' : NL (Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁) :=
        nl_append (nl_append hnY (nl_pair a n)) hg1
      have hu : LoopLetter.lamt k ∉ LoopLetter.det a :: (B ++ LoopLetter.lamt o ::
          (Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁)) := by
        intro hm
        rcases List.mem_cons.1 hm with h | h
        · cases h
        · rcases List.mem_append.1 h with h | h
          · exact F.nlB k h
          · rcases List.mem_cons.1 h with h | h
            · exact hne' h.symm
            · exact hnQ' k h
      have h1 : (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: Y) ++ [LoopLetter.res a,
          LoopLetter.proj n] ++ f.rotate q ++ [LoopLetter.res b, LoopLetter.proj n]) =
          (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (Y ++ [LoopLetter.res a,
            LoopLetter.proj n] ++ g₁))) ++ LoopLetter.lamt k :: (g₂ ++ [LoopLetter.res b,
            LoopLetter.proj n]) := by
        rw [hg]; simp
      rw [h1, kloop_eq k hu]
      have h2 : (g₂ ++ [LoopLetter.res b, LoopLetter.proj n]) ++ LoopLetter.det a :: (B ++
          LoopLetter.lamt o :: (Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁)) =
          ((g₂ ++ [LoopLetter.res b, LoopLetter.proj n]) ++ LoopLetter.det a :: B) ++
            LoopLetter.lamt o :: (Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁) := by simp
      rw [h2, lseg_append_lam o hnQ']
      have : 0 < (Y ++ [LoopLetter.res a, LoopLetter.proj n] ++ g₁).countP rcR := by
        rw [List.countP_pos_iff]
        exact ⟨.res a, by simp, rfl⟩
      omega
    have hkf : kloop k f ≤ T.kk k := by
      rw [kk_eq]
      exact List.le_sum_of_mem (List.mem_map_of_mem hfm)
    have kw : kloop k w = 0 := kloop_of_not_mem hwo'
    have kf0 : kloop o f = 0 := kloop_of_not_mem hfo
    have kk0 := kk_eq_kloop hT o hw hlo
    have k0 := kk_eq T o
    have k1 := kk_eq T k
    have l0 := hk o
    have l1 := hk k
    rcases hoo with ⟨rfl, rfl, hk1⟩ | ⟨rfl, rfl, hk1⟩
    · refine ⟨fun _ _ => ?_, fun _ h => by omega, fun _ hty' _ => ?_⟩
      · omega
      · rw [hTy] at hty'
        simp at hty'
    · exfalso
      omega
  · -- `f` has no `Λ̃`
    have hnf : NL f := fun k hk => hfl ⟨k, hk⟩
    have hX : NL ([LoopLetter.res a, LoopLetter.proj n] ++ f.rotate q ++
        [LoopLetter.res b, LoopLetter.proj n]) :=
      nl_append (nl_append (nl_pair a n) (nl_rotate hnf q)) (nl_pair b n)
    refine kstep_set hT hT' hf _ (.det a :: (B ++ .lamt o :: Y) ++ [.res a, .proj n] ++
      f.rotate q ++ [.res b, .proj n]) hX (by simp) True (fun _ => ?_) ?_ (fun _ => hmem)
    · have : 0 < ([LoopLetter.res a, LoopLetter.proj n] ++ f.rotate q ++
          [LoopLetter.res b, LoopLetter.proj n]).countP rcR := by
        rw [List.countP_pos_iff]
        exact ⟨.res a, by simp, rfl⟩
      omega
    · intro o''
      have h3 : kloop o'' f = 0 := kloop_of_not_mem (hnf o'')
      have h4 := sum_eraseIdx (kloop o'') _ j f hS
      rw [hL o'']
      rw [hw'eq] at h4
      simp only [List.append_assoc] at h4 ⊢
      omega

/-- The step `𝔠₂` (5.44) [scut_2]: the focused loop is cut at the resolvent `tl[q] = 𝒢_b`
into two loops. -/
private theorem kstep_cut2 {T T' : LoopExpr} (hT : T.wf = true) (hT' : T'.wf = true) {ℓ : ℕ}
    {a : Fin 2} {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) {q : ℕ} {b : Fin 2}
    (hq : tl[q]? = some (LoopLetter.res b)) (n : ℕ)
    (hloops : T'.loops = (T.loops.set ℓ (LoopLetter.det a :: tl.take (q + 1) ++
      [LoopLetter.proj n])) ++ [LoopLetter.proj n :: tl.drop q ++ [LoopLetter.res a]]) :
    KStep T T' True := by
  have hL : ∀ o'', T'.kk o'' = (((T.loops.set ℓ (LoopLetter.det a :: tl.take (q + 1) ++
      [LoopLetter.proj n])) ++ [LoopLetter.proj n :: tl.drop q ++ [LoopLetter.res a]]).map
        (kloop o'')).sum := fun o'' => by rw [kk_eq, hloops]
  obtain ⟨o, o', w, B, Y, hoo, hw, rfl, F⟩ := focus_foc hT hf
  obtain ⟨hqlt, hqeq⟩ := List.getElem?_eq_some_iff.1 hq
  have e1 : (B ++ LoopLetter.lamt o :: Y).take (q + 1) =
      (B ++ LoopLetter.lamt o :: Y).take q ++ [LoopLetter.res b] := by
    rw [List.take_add_one, hq]; rfl
  have e2 : (B ++ LoopLetter.lamt o :: Y).drop q =
      LoopLetter.res b :: (B ++ LoopLetter.lamt o :: Y).drop (q + 1) := by
    rw [List.drop_eq_getElem_cons hqlt, hqeq]
  have e3 : B ++ LoopLetter.lamt o :: Y = (B ++ LoopLetter.lamt o :: Y).take q ++
      LoopLetter.res b :: (B ++ LoopLetter.lamt o :: Y).drop (q + 1) := by
    conv_lhs => rw [← List.take_append_drop q (B ++ LoopLetter.lamt o :: Y), e2]
  rw [e1, e2] at hL hloops
  generalize (B ++ LoopLetter.lamt o :: Y).take q = X₁ at hL hloops e3
  generalize (B ++ LoopLetter.lamt o :: Y).drop (q + 1) = X₂ at hL hloops e3
  obtain ⟨c', hX1, hYc⟩ : ∃ c', X₁ = B ++ LoopLetter.lamt o :: c' ∧
      Y = c' ++ LoopLetter.res b :: X₂ := by
    rcases List.append_eq_append_iff.1 e3 with ⟨as, hX1, hY'⟩ | ⟨bs, hB', hbs⟩
    · cases as with
      | nil => simp at hY'
      | cons c as' =>
        simp only [List.cons_append, List.cons.injEq] at hY'
        obtain ⟨rfl, hY'⟩ := hY'
        exact ⟨as', hX1, hY'⟩
    · exfalso
      cases bs with
      | nil => simp at hbs
      | cons c bs' =>
        simp only [List.cons_append, List.cons.injEq] at hbs
        obtain ⟨rfl, -⟩ := hbs
        have : LoopLetter.res b ∈ B := by rw [hB']; simp
        have h0 := List.countP_eq_zero.1 F.rsB _ this
        simp [rcR] at h0
  subst hX1
  subst hYc
  -- the two new loops
  have hsum : ∀ o'', T'.kk o'' + kloop o'' w = T.kk o'' +
      kloop o'' (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++ [LoopLetter.res b])) ++
        [LoopLetter.proj n]) +
      kloop o'' (LoopLetter.proj n :: (LoopLetter.res b :: X₂) ++ [LoopLetter.res a]) := by
    intro o''
    have h1 := sum_set (kloop o'') T.loops ℓ w
      (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: c' ++ [LoopLetter.res b]) ++
        [LoopLetter.proj n]) hw
    rw [hL o'', kk_eq]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at h1 ⊢
    simp only [List.append_assoc, List.cons_append] at h1 ⊢
    omega
  have hnB := F.nlB
  have hne' : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => F.ne (LoopLetter.lamt.inj h)
  have hwm : w ∈ T.loops := List.mem_of_getElem? hw
  have hkw : ∀ o'', kloop o'' w ≤ T.kk o'' := fun o'' => by
    rw [kk_eq]
    exact List.le_sum_of_mem (List.mem_map_of_mem hwm)
  have hlt : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hw1 : (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++ [LoopLetter.res b])) ++
      [LoopLetter.proj n]) ∈ T'.loops := by
    rw [hloops]
    apply List.mem_append_left
    have e : LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++ [LoopLetter.res b])) ++
        [LoopLetter.proj n] = LoopLetter.det a :: (B ++ LoopLetter.lamt o :: c' ++
        [LoopLetter.res b]) ++ [LoopLetter.proj n] := by simp
    rw [e]
    exact List.mem_of_getElem? (List.getElem?_set_self hlt)
  have hlo : LoopLetter.lamt o ∈ w := by
    obtain ⟨r, hr⟩ := F.rot
    have : LoopLetter.lamt o ∈ w.rotate r := by rw [hr]; simp
    exact List.mem_rotate.1 this
  have hty1 : T'.typeI = true ↔ LoopLetter.lamt o' ∈ c' := by
    rw [typeI_iff hT' hw1 F.ne (by simp)]
    simp [hnB o', Ne.symm hne']
  have hty0 : T.typeI = true ↔ LoopLetter.lamt o' ∈ c' ++ LoopLetter.res b :: X₂ := by
    rw [typeI_iff hT hwm F.ne hlo, F.mem_iff]
  have hP1 : 1 ≤ kloop o (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++
      [LoopLetter.res b])) ++ [LoopLetter.proj n]) := by
    have hu : LoopLetter.lamt o ∉ LoopLetter.det a :: B := by simp [hnB o]
    have h1 : LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++ [LoopLetter.res b])) ++
        [LoopLetter.proj n] = (LoopLetter.det a :: B) ++ LoopLetter.lamt o ::
          (c' ++ [LoopLetter.res b, LoopLetter.proj n]) := by simp
    rw [h1, kloop_eq o hu]
    have h2 : (c' ++ [LoopLetter.res b, LoopLetter.proj n]) ++ LoopLetter.det a :: B =
        c' ++ ([LoopLetter.res b, LoopLetter.proj n] ++ LoopLetter.det a :: B) := by simp
    rw [h2, lseg_append_free (nl_append (nl_pair b n) (nl_cons (by simp) hnB))]
    have : 0 < ([LoopLetter.res b, LoopLetter.proj n] ++ LoopLetter.det a :: B).countP rcR := by
      rw [List.countP_pos_iff]
      exact ⟨.res b, by simp, rfl⟩
    omega
  have hcase : (kloop o' w = kloop o' (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++
        [LoopLetter.res b])) ++ [LoopLetter.proj n]) ∧
      kloop o' (LoopLetter.proj n :: (LoopLetter.res b :: X₂) ++ [LoopLetter.res a]) = 0 ∧
      T'.typeI = T.typeI) ∨
      (kloop o' (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++ [LoopLetter.res b])) ++
        [LoopLetter.proj n]) = 0 ∧
      2 ≤ kloop o' (LoopLetter.proj n :: (LoopLetter.res b :: X₂) ++ [LoopLetter.res a]) ∧
      1 ≤ kloop o' w ∧ T'.typeI = false) := by
    by_cases hm : LoopLetter.lamt o' ∈ c' ++ LoopLetter.res b :: X₂
    · rcases List.mem_append.1 hm with hm | hm
      · -- `Λ̃_{o'}` before `𝒢_b`
        obtain ⟨Y₁, c'', rfl⟩ := List.append_of_mem hm
        have hY : (Y₁ ++ LoopLetter.lamt o' :: c'') ++ LoopLetter.res b :: X₂ =
            Y₁ ++ LoopLetter.lamt o' :: (c'' ++ LoopLetter.res b :: X₂) := by simp
        obtain ⟨hn1, hn2, hold⟩ := F.old_o' hY
        left
        refine ⟨?_, ?_, ?_⟩
        · rw [hold]
          have h1 : LoopLetter.det a :: (B ++ LoopLetter.lamt o :: ((Y₁ ++ LoopLetter.lamt o' ::
              c'') ++ [LoopLetter.res b])) ++ [LoopLetter.proj n] =
              LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (Y₁ ++ LoopLetter.lamt o' ::
                (c'' ++ [LoopLetter.res b]))) ++ [LoopLetter.proj n] := by simp
          rw [h1, kloop_lam_form F.ne hnB hn1]
        · have hX2 : LoopLetter.lamt o' ∉ X₂ := fun h => hn2 o' (by simp [h])
          exact kloop_of_not_mem (by simp [hX2])
        · rw [hty1.2 (by simp), hty0.2 (by simp)]
      · rcases List.mem_cons.1 hm with hm | hm
        · cases hm
        · -- `Λ̃_{o'}` after `𝒢_b`
          obtain ⟨d₁, d₂, rfl⟩ := List.append_of_mem hm
          have hY : c' ++ LoopLetter.res b :: (d₁ ++ LoopLetter.lamt o' :: d₂) =
              (c' ++ LoopLetter.res b :: d₁) ++ LoopLetter.lamt o' :: d₂ := by simp
          obtain ⟨hn1, hn2, hold⟩ := F.old_o' hY
          right
          have hc'n : NL c' := fun k hk => hn1 k (by simp [hk])
          have hd1 : NL d₁ := fun k hk => hn1 k (by simp [hk])
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact kloop_of_not_mem (by simp [hnB o', Ne.symm F.ne, hc'n o'])
          · have hu : LoopLetter.lamt o' ∉ LoopLetter.proj n :: LoopLetter.res b :: d₁ := by
              simp [hd1 o']
            have h1 : LoopLetter.proj n :: (LoopLetter.res b :: (d₁ ++ LoopLetter.lamt o' :: d₂)) ++
                [LoopLetter.res a] = (LoopLetter.proj n :: LoopLetter.res b :: d₁) ++
                  LoopLetter.lamt o' :: (d₂ ++ [LoopLetter.res a]) := by simp
            rw [h1, kloop_eq o' hu]
            have hQ : NL (LoopLetter.res a :: LoopLetter.proj n :: LoopLetter.res b :: d₁) :=
              nl_cons (by simp) (nl_cons (by simp) (nl_cons (by simp) hd1))
            have h2 : (d₂ ++ [LoopLetter.res a]) ++ LoopLetter.proj n :: LoopLetter.res b :: d₁ =
                d₂ ++ (LoopLetter.res a :: LoopLetter.proj n :: LoopLetter.res b :: d₁) := by
              simp
            rw [h2, lseg_append_free hQ]
            have : (LoopLetter.res a :: LoopLetter.proj n :: LoopLetter.res b :: d₁).countP
                rcR = d₁.countP rcR + 2 := by
              simp [List.countP_cons, rcR]
            omega
          · rw [hold]
            have : 0 < (c' ++ LoopLetter.res b :: d₁).countP rcR := by
              rw [List.countP_pos_iff]
              exact ⟨.res b, by simp, rfl⟩
            omega
          · exact Bool.eq_false_iff.2 fun hb => hc'n o' (hty1.1 hb)
    · left
      have hc : LoopLetter.lamt o' ∉ c' := fun h => hm (List.mem_append_left _ h)
      have hX2 : LoopLetter.lamt o' ∉ X₂ := fun h =>
        hm (List.mem_append_right _ (List.mem_cons_of_mem _ h))
      refine ⟨?_, ?_, ?_⟩
      · rw [kloop_of_not_mem (F.not_mem_w hm), kloop_of_not_mem]
        simp [hnB o', Ne.symm F.ne, hc]
      · exact kloop_of_not_mem (by simp [hX2])
      · rw [Bool.eq_false_iff.2 fun hb => hm (List.mem_append_left _ (hty1.1 hb)),
          Bool.eq_false_iff.2 fun hb => hm (hty0.1 hb)]
  have s0 := hsum o
  have s1 := hsum o'
  have kw0 := hkw o
  have kw1 := hkw o'
  rcases hoo with ⟨rfl, rfl, hk1⟩ | ⟨rfl, rfl, hk1⟩
  · refine ⟨fun _ hk2 => ?_, fun _ h => by omega, fun hI hty' h1' => ?_⟩
    · rcases hcase with h | h <;> omega
    · rcases hcase with ⟨h, h2, h3⟩ | ⟨h, h2, h3, h4⟩
      · have := hI (h3.symm.trans hty') hk1
        omega
      · omega
  · refine ⟨fun h => by omega, fun _ _ => ?_, fun _ _ h1' => ?_⟩
    · rcases hcase with h | h <;> omega
    · rcases hcase with h | h <;> omega

/-- Each of the five operations of (5.42)–(5.46) preserves the facts on `k₁`, `k₂` of `KStep`. -/
private theorem kstep_apply {T T' : LoopExpr} (hT : T.wf = true) (op : LoopOp)
    (h : T' ∈ T.apply op) : KStep T T' (op ≠ .rep) := by
  have hT' : T'.wf = true := loop_step_wf T hT T' (by
    simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨op, by cases op <;> simp, h⟩)
  cases op
  · -- `𝔯`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      simp only [List.mem_singleton] at h
      subst h
      exact kstep_set hT hT' hf [] (.det a :: tl) (fun k hk => by simp at hk) (by simp) _
        (fun hn => absurd rfl hn) (fun o'' => kk_eq _ o'')
        (fun hlt => List.mem_of_getElem? (List.getElem?_set_self hlt))
  · -- `𝔠₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      simp only [List.mem_singleton] at h
      subst h
      exact kstep_set hT hT' hf [.res a, .proj T.nb] _ (nl_pair a T.nb) rfl _
        (fun _ => by simp [rcR]) (fun o'' => kk_eq _ o'')
        (fun hlt => List.mem_of_getElem? (List.getElem?_set_self hlt))
  · -- `𝔠₂`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨q, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b hq
        simp only [Option.some.injEq] at h5
        subst h5
        have := kstep_cut2 hT hT' hf hq T.nb (T' := { T with
          dexp := T.dexp + 1, nb := T.nb + 1,
          loops := T.loops.set ℓ (.det a :: tl.take (q + 1) ++ [.proj T.nb]) ++
            [.proj T.nb :: tl.drop q ++ [.res a]] }) rfl
        exact this.of_true _
      · simp at h5
  · -- `𝔭₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨j, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b y hj
        simp only [Option.some.injEq] at h5
        subst h5
        exact kstep_set hT hT' hf [.res a, .proj T.nb, .res b, .proj y, .res b, .proj T.nb] _
          (fun k hk => by simp at hk) rfl _ (fun _ => by simp [rcR]) (fun o'' => kk_eq _ o'')
          (fun hlt => List.mem_of_getElem? (List.getElem?_set_self hlt))
      · simp at h5
  · -- `𝔭₂`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨j, -, h5⟩ := List.mem_flatMap.1 h
      split at h5
      · simp at h5
      · rename_i hjl
        split at h5
        · simp at h5
        · rename_i f hf2
          obtain ⟨q, -, h6⟩ := List.mem_filterMap.1 h5
          split at h6
          · rename_i b hq
            simp only [Option.some.injEq] at h6
            subst h6
            have := kstep_plug2 hT hT' hf hjl hf2 hq T.nb (T' := { T with
              dexp := T.dexp - 1, S := T.S + 2, nb := T.nb + 1,
              loops := (T.loops.set ℓ (.det a :: tl ++ [.res a, .proj T.nb] ++ f.rotate q ++
                [.res b, .proj T.nb])).eraseIdx j }) rfl
            exact this.of_true _
          · simp at h6

/-! ### The characters (5.50) and the invariants of the reachable expressions -/

/-- Every loop without `Λ̃` has at least two resolvents. -/
private def J0 (T : LoopExpr) : Prop :=
  ∀ w ∈ T.loops, NL w → 2 ≤ w.countP rcR

/-- The focused loop `𝒢_a tl` has `tl = B Λ̃_o Y` with `B` free of resolvents. -/
private theorem focus_mem {T : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) :
    ∃ o : Fin 2, LoopLetter.lamt o ∈ tl ∧ ∃ B Y, tl = B ++ .lamt o :: Y ∧ B.countP rcR = 0 := by
  obtain ⟨o, o', w, B, Y, -, -, rfl, F⟩ := focus_foc hT hf
  exact ⟨o, by simp, B, Y, rfl, F.rsB⟩

/-- Every operation keeps two resolvents in every loop without `Λ̃`. -/
private theorem j0_apply {T T' : LoopExpr} (hT : T.wf = true) (hJ : J0 T) (op : LoopOp)
    (h : T' ∈ T.apply op) : J0 T' := by
  have hset : ∀ {ℓ : ℕ} {w' : List LoopLetter}, (∃ o, LoopLetter.lamt o ∈ w') →
      ∀ w ∈ T.loops.set ℓ w', NL w → 2 ≤ w.countP rcR := by
    intro ℓ w' ⟨o, ho⟩ w hw hnl
    rcases List.mem_or_eq_of_mem_set hw with hw | rfl
    · exact hJ w hw hnl
    · exact absurd ho (hnl o)
  cases op
  · simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨o, ho, -⟩ := focus_mem hT hf
      exact hset ⟨o, by simp [ho]⟩
  · simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨o, ho, -⟩ := focus_mem hT hf
      exact hset ⟨o, by simp [ho]⟩
  · simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨q, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b hq
        simp only [Option.some.injEq] at h5
        subst h5
        obtain ⟨o, -, B, Y, rfl, hB⟩ := focus_mem hT hf
        obtain ⟨hqlt, hqeq⟩ := List.getElem?_eq_some_iff.1 hq
        intro w hw hnl
        rcases List.mem_append.1 hw with hw | hw
        · refine hset ⟨o, ?_⟩ w hw hnl
          have hBq : B.length < q := by
            by_contra hc
            rcases Nat.lt_or_ge q B.length with hlt | hge
            · have h1 : (B ++ LoopLetter.lamt o :: Y)[q]? = B[q]? := List.getElem?_append_left hlt
              rw [hq] at h1
              have h2 : LoopLetter.res b ∈ B := List.mem_of_getElem? h1.symm
              have h3 : 0 < B.countP rcR := List.countP_pos_iff.2 ⟨_, h2, rfl⟩
              omega
            · have hqe : q = B.length := by omega
              subst hqe
              simp at hq
          have h4 : (B ++ LoopLetter.lamt o :: Y).take (q + 1) =
              B ++ LoopLetter.lamt o :: Y.take (q - B.length) := by
            rw [List.take_append, List.take_of_length_le (by omega),
              show q + 1 - B.length = (q - B.length) + 1 by omega, List.take_succ_cons]
          rw [h4]
          simp
        · simp only [List.mem_singleton] at hw
          subst hw
          have e2 : (B ++ LoopLetter.lamt o :: Y).drop q =
              LoopLetter.res b :: (B ++ LoopLetter.lamt o :: Y).drop (q + 1) := by
            rw [List.drop_eq_getElem_cons hqlt, hqeq]
          rw [List.cons_append, e2]
          simp [List.countP_cons, List.countP_append, rcR]
      · simp at h5
  · simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨j, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b y hj
        simp only [Option.some.injEq] at h5
        subst h5
        obtain ⟨o, ho, -⟩ := focus_mem hT hf
        exact hset ⟨o, by simp [ho]⟩
      · simp at h5
  · simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨j, -, h5⟩ := List.mem_flatMap.1 h
      split at h5
      · simp at h5
      · split at h5
        · simp at h5
        · rename_i f hf2
          obtain ⟨q, -, h6⟩ := List.mem_filterMap.1 h5
          split at h6
          · rename_i b hq
            simp only [Option.some.injEq] at h6
            subst h6
            obtain ⟨o, ho, -⟩ := focus_mem hT hf
            intro w hw hnl
            exact hset ⟨o, by simp [ho]⟩ w (List.mem_of_mem_eraseIdx hw) hnl
          · simp at h6


/-- The only loop of the starting loop contains `Λ̃₁`: there is no loop without `Λ̃`. -/
private theorem j0_start : J0 loopStart := by
  intro w hw hnl
  simp only [loopStart, List.mem_singleton] at hw
  subst hw
  exact absurd (by simp) (hnl 0)

/-- A word with `Λ̃₁` and `Λ̃₂` excluded by the Boolean tests contains no `Λ̃`. -/
private theorem nl_of_contains {w : List LoopLetter} (h0 : w.contains (.lamt 0) = false)
    (h1 : w.contains (.lamt 1) = false) : NL w := by
  intro k
  fin_cases k
  · simpa using h0
  · simpa using h1

/-- A word with no `Λ̃` fails the Boolean tests. -/
private theorem contains_of_nl {w : List LoopLetter} (h : NL w) (k : Fin 2) :
    w.contains (.lamt k) = false := by
  simpa using h k

/-! ## The parent decomposition and the depth -/

/-- Each term of `step` is a term of one of the five operations. -/
private theorem mem_step_of_apply {P T : LoopExpr} {o : LoopOp} (h : T ∈ P.apply o) :
    T ∈ P.step := by
  simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨o, by cases o <;> simp, h⟩

/-- The terms of the operations are the terms of `step`. -/
private theorem apply_of_mem_step {P T : LoopExpr} (h : T ∈ P.step) :
    ∃ o : LoopOp, T ∈ P.apply o := by
  simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨o, -, h⟩ := h
  exact ⟨o, h⟩

/-- The expressions of the rounds and of the expanded lists are in the starting list or terms of
an expanded expression, for every starting list. -/
private theorem par_aux (ε : ℝ) :
    ∀ (n : ℕ) (L : List LoopExpr),
      (∀ T ∈ loopIter ε n L, T ∈ L ∨ ∃ P ∈ loopInner ε n L, ∃ o : LoopOp, T ∈ P.apply o) ∧
      (∀ T ∈ loopInner ε n L, T ∈ L ∨ ∃ P ∈ loopInner ε n L, ∃ o : LoopOp, T ∈ P.apply o)
  | 0, L => ⟨fun T hT => Or.inl hT, fun T hT => by simp [loopInner] at hT⟩
  | n + 1, L => by
    obtain ⟨ih1, ih2⟩ := par_aux ε n (L.flatMap fun T => if T.Stopped ε then [T] else T.step)
    have hnext : ∀ T ∈ L.flatMap (fun T => if T.Stopped ε then [T] else T.step),
        T ∈ L ∨ ∃ P ∈ loopInner ε (n + 1) L, ∃ o : LoopOp, T ∈ P.apply o := by
      intro T hT
      obtain ⟨S, hS, h⟩ := List.mem_flatMap.1 hT
      by_cases hs : S.Stopped ε
      · simp only [hs, ite_true, List.mem_singleton] at h
        subst h
        exact Or.inl hS
      · simp only [hs, ite_false] at h
        refine Or.inr ⟨S, ?_, apply_of_mem_step h⟩
        simp only [loopInner, List.mem_append, List.mem_filter]
        exact Or.inl ⟨hS, decide_eq_true hs⟩
    have hmono : ∀ P ∈ loopInner ε n (L.flatMap fun T => if T.Stopped ε then [T] else T.step),
        P ∈ loopInner ε (n + 1) L := by
      intro P hP
      simp only [loopInner, List.mem_append]
      exact Or.inr hP
    constructor
    · intro T hT
      rcases ih1 T hT with h | ⟨P, hP, o, hTP⟩
      · exact hnext T h
      · exact Or.inr ⟨P, hmono P hP, o, hTP⟩
    · intro T hT
      simp only [loopInner, List.mem_append, List.mem_filter] at hT
      rcases hT with ⟨hTL, -⟩ | hT
      · exact Or.inl hTL
      · rcases ih2 T hT with h | ⟨P, hP, o, hTP⟩
        · exact hnext T h
        · exact Or.inr ⟨P, hmono P hP, o, hTP⟩

/-- The number `m + u + 2R - 2` of operations on a path from the starting loop, for the characters
`(m, n, u, S)` of (5.37) [number_of_G_type_1] and `R` of (5.50) [counting_character_of_term]. -/
private def dep (T : LoopExpr) : ℤ :=
  T.charsZ.1 + T.charsZ.2.2.1 + 2 * T.rcount - 2

/-- Each operation raises `m + u + 2R - 2` by exactly one (Table 1
[table_effect_of_operations]). -/
private theorem dep_apply {T T' : LoopExpr} (op : LoopOp) (h : T' ∈ T.apply op) :
    dep T' = dep T + 1 := by
  have hz := loop_table1 T op T' h
  unfold dep LoopExpr.rcount
  rw [hz]
  generalize T.charsZ = c
  obtain ⟨m, n, u, S⟩ := c
  cases op <;> simp only [LoopOp.delta, Prod.mk_add_mk] <;> ring

/-- On the class (5.50) [counting_character_of_term] the number `m + u + 2R - 2` is
`R + C₁ + C₂ + P₁ + P₂ ≥ 0`. -/
private theorem dep_nonneg {T : LoopExpr}
    (h : ∃ R C₁ C₂ P₁ P₂ : ℕ, T.charsZ = ((2 : ℤ) - R + C₂ + 2 * P₁ + P₂, (1 : ℤ) + C₂ - P₂,
      (C₁ : ℤ) - P₁, 2 * (P₁ : ℤ) + 2 * P₂)) : 0 ≤ dep T := by
  obtain ⟨R, C₁, C₂, P₁, P₂, h⟩ := h
  unfold dep LoopExpr.rcount
  rw [h]
  simp only
  omega

/-- A property of the starting loop that passes from every expression of `loopInner` to its terms
holds on every expression reached or expanded; induction on the number of operations. -/
private theorem reach_induct (ε : ℝ) (n : ℕ) (Q : LoopExpr → Prop) (h0 : Q loopStart)
    (hs : ∀ P ∈ loopInner ε n [loopStart], Q P → ∀ (o : LoopOp) (T : LoopExpr),
      T ∈ P.apply o → Q T) :
    ∀ T, (T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) → Q T := by
  suffices h : ∀ k : ℕ, ∀ T, (T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) →
      (dep T).toNat = k → Q T from fun T hT => h _ T hT rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T hT hk
    obtain ⟨h1, h2⟩ := par_aux ε n [loopStart]
    have hpar : T = loopStart ∨ ∃ P ∈ loopInner ε n [loopStart], ∃ o : LoopOp, T ∈ P.apply o := by
      rcases hT with hT | hT
      · rcases h1 T hT with h | h
        · exact Or.inl (List.mem_singleton.1 h)
        · exact Or.inr h
      · rcases h2 T hT with h | h
        · exact Or.inl (List.mem_singleton.1 h)
        · exact Or.inr h
    rcases hpar with rfl | ⟨P, hP, o, hTP⟩
    · exact h0
    · have hd := dep_apply o hTP
      have hn := dep_nonneg (loop_reach ε n P (Or.inr hP)).2.2.2
      exact hs P hP (ih _ (by omega) P (Or.inr hP) rfl) o T hTP

/-- The tree without stopping rule after `k + 1` rounds contains the terms of every expression of
the tree after `k` rounds. -/
private theorem loopTree_step {P T : LoopExpr} {k : ℕ} (hP : P ∈ loopTree k) (h : T ∈ P.step) :
    T ∈ loopTree (k + 1) :=
  List.mem_flatMap.2 ⟨P, hP, h⟩


/-! ## The counts of resolvents -/

/-- The resolvents of the `Λ̃`-free suffix of a word are among its resolvents. -/
private theorem lseg_le (l : List LoopLetter) : lseg l ≤ l.countP rcR := by
  unfold lseg
  calc (l.reverse.takeWhile notLam).countP rcR ≤ l.reverse.countP rcR :=
        (List.takeWhile_sublist _).countP_le
    _ = l.countP rcR := List.countP_reverse

/-- The count `k_o` of a loop is at most its number of resolvents. -/
private theorem kloop_le (o : Fin 2) (w : List LoopLetter) : kloop o w ≤ w.countP rcR := by
  unfold kloop
  split_ifs
  · calc lseg ((w.rotate (w.idxOf (.lamt o))).drop 1)
        ≤ ((w.rotate (w.idxOf (.lamt o))).drop 1).countP rcR := lseg_le _
      _ ≤ (w.rotate (w.idxOf (.lamt o))).countP rcR := (List.drop_sublist _ _).countP_le
      _ = w.countP rcR := (List.rotate_perm _ _).countP_eq _
  · exact Nat.zero_le _

/-- In a loop with both `Λ̃`, the counts `k_o`, `k_{o'}` are the numbers of resolvents of the two
arcs between the `Λ̃`, so they add up to the number of resolvents of the loop. -/
private theorem kloop_two {w : List LoopLetter} (hc : ∀ k, w.count (.lamt k) ≤ 1) {o o' : Fin 2}
    (hne : o ≠ o') (ho : LoopLetter.lamt o ∈ w) (ho' : LoopLetter.lamt o' ∈ w) :
    kloop o w + kloop o' w = w.countP rcR := by
  have hne' : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => hne (LoopLetter.lamt.inj h)
  have ho2 : ∀ k, k = o ∨ k = o' := fin2_cases hne
  obtain ⟨u, v, rfl⟩ := List.append_of_mem ho
  have hco := hc o
  simp only [List.count_append, List.count_cons_self] at hco
  have hu : LoopLetter.lamt o ∉ u := fun hm => by
    have := List.count_pos_iff.2 hm
    omega
  have hv : LoopLetter.lamt o ∉ v := fun hm => by
    have := List.count_pos_iff.2 hm
    omega
  have e1 := kloop_eq (u := u) (v := v) o hu
  have hcount : (u ++ LoopLetter.lamt o :: v).countP rcR = (v ++ u).countP rcR := by
    simp [List.countP_append, rcR]
    omega
  have hm : LoopLetter.lamt o' ∈ v ++ u := by
    have h' : LoopLetter.lamt o' ∈ u ++ LoopLetter.lamt o :: v := ho'
    simp only [List.mem_append, List.mem_cons] at h' ⊢
    rcases h' with h' | h' | h'
    · exact Or.inr h'
    · exact absurd h'.symm hne'
    · exact Or.inl h'
  obtain ⟨g₁, g₂, hg⟩ := List.append_of_mem hm
  have hco' := hc o'
  have hperm : (u ++ LoopLetter.lamt o :: v).count (.lamt o') = (v ++ u).count (.lamt o') := by
    simp [List.count_append, hne']
    omega
  rw [hperm, hg] at hco'
  have hno : ∀ k, k ≠ o' → LoopLetter.lamt k ∉ g₁ ++ .lamt o' :: g₂ := by
    intro k hk hm'
    rcases ho2 k with rfl | rfl
    · rw [← hg] at hm'
      rcases List.mem_append.1 hm' with h' | h'
      · exact hv h'
      · exact hu h'
    · exact hk rfl
  obtain ⟨hn1, hn2⟩ := nl_split hco' hno
  have e2 := lseg_append_lam (P := g₁) o' hn2
  rw [← hg, ← e1] at e2
  have hrot : (u ++ LoopLetter.lamt o :: v).rotate u.length =
      LoopLetter.lamt o :: g₁ ++ LoopLetter.lamt o' :: g₂ := by
    rw [List.rotate_append_length_eq, List.cons_append, hg, List.cons_append]
  have e3 := kloop_rotate o' u.length (u ++ LoopLetter.lamt o :: v) (hc o')
  rw [hrot] at e3
  have hu' : LoopLetter.lamt o' ∉ LoopLetter.lamt o :: g₁ := by
    intro h'
    rcases List.mem_cons.1 h' with h' | h'
    · exact hne' h'.symm
    · exact hn1 o' h'
  have e4 := kloop_eq (u := LoopLetter.lamt o :: g₁) (v := g₂) o' hu'
  have e5 := lseg_append_lam (P := g₂) o hn1
  rw [e5] at e4
  rw [e2, ← e3, e4, hcount, hg]
  simp only [List.countP_append, List.countP_cons, rcR]
  simp only [Bool.false_eq_true, ite_false, add_zero]
  omega

/-- For every loop of the class `𝒯`, `k₁ + k₂` of the loop is at most its number of resolvents. -/
private theorem kloop_sum_le {T : LoopExpr} (hT : T.wf = true) {w : List LoopLetter}
    (hw : w ∈ T.loops) : kloop 0 w + kloop 1 w ≤ w.countP rcR := by
  by_cases h0 : LoopLetter.lamt 0 ∈ w <;> by_cases h1 : LoopLetter.lamt 1 ∈ w
  · exact (kloop_two (fun k => count_le_one hT hw k) (o := 0) (o' := 1) (by decide) h0 h1).le
  · rw [kloop_of_not_mem h1]
    simpa using kloop_le 0 w
  · rw [kloop_of_not_mem h0]
    simpa using kloop_le 1 w
  · rw [kloop_of_not_mem h0, kloop_of_not_mem h1]
    exact Nat.zero_le _

/-- A loop of the class `𝒯` contains each `Λ̃_k`. -/
private theorem exists_loop {T : LoopExpr} (h : T.wf = true) (k : Fin 2) :
    ∃ w ∈ T.loops, LoopLetter.lamt k ∈ w := by
  by_contra hc
  have h1 := wf_counts h k
  have h2 : (T.loops.map fun w => w.count (.lamt k)).sum = 0 := by
    rw [List.sum_eq_zero_iff]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact List.count_eq_zero.2 fun hm => hc ⟨w, hw, hm⟩
  omega

/-- A list of words that each have at least two resolvents has at least twice its length of
resolvents. -/
private theorem sum_two_le : ∀ l : List (List LoopLetter), (∀ x ∈ l, 2 ≤ x.countP rcR) →
    2 * l.length ≤ (l.map fun w => w.countP rcR).sum
  | [], _ => by simp
  | x :: l, h => by
      have h1 := sum_two_le l (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have h2 := h x List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Erasing the entry at a valid position shortens a list by one. -/
private theorem len_eraseIdx {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) :
    (l.eraseIdx i).length + 1 = l.length := by
  rw [List.length_eraseIdx]
  simp [h]
  omega

/-- Type I: the loop with both `Λ̃` and the `n - 1` loops without `Λ̃`, each with two resolvents:
`2n + k₁ + k₂ ≤ m + 2`. -/
private theorem count_type1 {T : LoopExpr} (hT : T.wf = true) (hJ : J0 T)
    (hI : T.typeI = true) :
    2 * T.loops.length + (T.kk 0 + T.kk 1) ≤ (T.loops.map fun w => w.countP rcR).sum + 2 := by
  have hI' : ∃ w ∈ T.loops, LoopLetter.lamt 0 ∈ w ∧ LoopLetter.lamt 1 ∈ w := by
    unfold LoopExpr.typeI at hI
    simpa [List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] using hI
  obtain ⟨w, hw, h0, h1⟩ := hI'
  obtain ⟨ℓ, hℓ⟩ := List.mem_iff_getElem?.1 hw
  have hk0 := kk_eq_kloop hT 0 hℓ h0
  have hk1 := kk_eq_kloop hT 1 hℓ h1
  have hcons := kloop_sum_le hT hw
  have e := sum_eraseIdx (fun w => w.countP rcR) T.loops ℓ w hℓ
  have hfree : ∀ x ∈ T.loops.eraseIdx ℓ, 2 ≤ x.countP rcR := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
    apply hJ x (List.mem_of_getElem? hjx)
    intro k
    fin_cases k
    · exact uniq_loop hT 0 hℓ h0 j x hj hjx
    · exact uniq_loop hT 1 hℓ h1 j x hj hjx
  have h2 := sum_two_le _ hfree
  have hlen := len_eraseIdx (List.getElem?_eq_some_iff.1 hℓ).1
  beta_reduce at e
  omega

/-- Type II: the two loops with one `Λ̃` each and the `n - 2` loops without `Λ̃`, each with two
resolvents: `2n + k₁ + k₂ ≤ m + 4`. -/
private theorem count_type2 {T : LoopExpr} (hT : T.wf = true) (hJ : J0 T)
    (hI : T.typeI = false) :
    2 * T.loops.length + (T.kk 0 + T.kk 1) ≤ (T.loops.map fun w => w.countP rcR).sum + 4 := by
  obtain ⟨w₀, hw₀, h0⟩ := exists_loop hT 0
  obtain ⟨w₁, hw₁, h1⟩ := exists_loop hT 1
  have hn0 : LoopLetter.lamt 1 ∉ w₀ := fun h => by
    have := (typeI_iff hT hw₀ (o := 0) (o' := 1) (by decide) h0).2 h
    rw [hI] at this
    simp at this
  have hn1 : LoopLetter.lamt 0 ∉ w₁ := fun h => by
    have := (typeI_iff hT hw₁ (o := 1) (o' := 0) (by decide) h1).2 h
    rw [hI] at this
    simp at this
  obtain ⟨ℓ₀, hℓ₀⟩ := List.mem_iff_getElem?.1 hw₀
  obtain ⟨ℓ₁, hℓ₁⟩ := List.mem_iff_getElem?.1 hw₁
  have hne : ℓ₁ ≠ ℓ₀ := fun h => by
    subst h
    have := Option.some.inj (hℓ₀.symm.trans hℓ₁)
    subst this
    exact hn0 h1
  have hk0 := kk_eq_kloop hT 0 hℓ₀ h0
  have hk1 := kk_eq_kloop hT 1 hℓ₁ h1
  have c0 := kloop_sum_le hT hw₀
  have c1 := kloop_sum_le hT hw₁
  have z0 := kloop_of_not_mem hn0
  have z1 := kloop_of_not_mem hn1
  have e0 := sum_eraseIdx (fun w => w.countP rcR) T.loops ℓ₀ w₀ hℓ₀
  have hw₁' : w₁ ∈ T.loops.eraseIdx ℓ₀ := List.mem_eraseIdx_iff_getElem?.2 ⟨ℓ₁, hne, hℓ₁⟩
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_getElem?.1 hw₁'
  have e1 := sum_eraseIdx (fun w => w.countP rcR) _ i₁ w₁ hi₁
  have hcount0 : ((T.loops.eraseIdx ℓ₀).map fun w => w.count (.lamt 0)).sum = 0 := by
    have a1 := sum_eraseIdx (fun w => w.count (.lamt 0)) T.loops ℓ₀ w₀ hℓ₀
    have a2 := wf_counts hT 0
    have a3 : 1 ≤ w₀.count (.lamt 0) := List.count_pos_iff.2 h0
    beta_reduce at a1
    omega
  have hcount0' : (((T.loops.eraseIdx ℓ₀).eraseIdx i₁).map fun w => w.count (.lamt 0)).sum = 0 := by
    have a1 := sum_eraseIdx (fun w => w.count (.lamt 0)) _ i₁ w₁ hi₁
    beta_reduce at a1
    omega
  have hcount1 : (((T.loops.eraseIdx ℓ₀).eraseIdx i₁).map fun w => w.count (.lamt 1)).sum = 0 := by
    have a1 := sum_eraseIdx (fun w => w.count (.lamt 1)) T.loops ℓ₀ w₀ hℓ₀
    have a2 := sum_eraseIdx (fun w => w.count (.lamt 1)) _ i₁ w₁ hi₁
    have a3 := wf_counts hT 1
    have a4 : w₀.count (.lamt 1) = 0 := List.count_eq_zero.2 hn0
    have a5 : 1 ≤ w₁.count (.lamt 1) := List.count_pos_iff.2 h1
    beta_reduce at a1 a2
    omega
  have hfree : ∀ x ∈ (T.loops.eraseIdx ℓ₀).eraseIdx i₁, 2 ≤ x.countP rcR := by
    intro x hx
    apply hJ x (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx hx))
    intro k
    fin_cases k
    · exact List.count_eq_zero.1 ((List.sum_eq_zero_iff.1 hcount0') _ (List.mem_map_of_mem hx))
    · exact List.count_eq_zero.1 ((List.sum_eq_zero_iff.1 hcount1) _ (List.mem_map_of_mem hx))
  have h2 := sum_two_le _ hfree
  have hlen0 := len_eraseIdx (List.getElem?_eq_some_iff.1 hℓ₀).1
  have hlen1 := len_eraseIdx (List.getElem?_eq_some_iff.1 hi₁).1
  beta_reduce at e0 e1
  omega

/-! ## The finite checks of the exceptional classes -/

/-- Case (ii): the expressions of the tree after one round with the hypotheses of the case are
`loopWordII`. -/
private abbrev chkII (T : LoopExpr) : Prop :=
  T.kk 0 = 0 → T.typeI = true → T.rcount = 1 → T.charsZ.1 + T.charsZ.2.2.1 = 1 → T = loopWordII

/-- Case (ii) by evaluation on the tree after one round. -/
private theorem chkII_all : ∀ T ∈ loopTree 1, chkII T := by decide

/-- Case (iv), `m + u ≤ 2`: the expressions with the hypotheses of the case are `loopWordIV`. -/
private abbrev chkIVa (T : LoopExpr) : Prop :=
  T.kk 0 = 0 → T.typeI = false → T.rcount = 1 → T.charsZ.1 + T.charsZ.2.2.1 ≤ 2 →
    T = loopWordIV

/-- Case (iv), `m + u ≤ 2`, by evaluation on the trees after at most two rounds. -/
private theorem chkIVa_all : ∀ j, j ≤ 2 → ∀ T ∈ loopTree j, chkIVa T := by
  intro j hj
  interval_cases j <;> decide

/-- Case (iv), `k₂ = 1` and `m + u ≤ 3`: the expressions with the hypotheses of the case are
`loopWordIVb`. -/
private abbrev chkIVb (T : LoopExpr) : Prop :=
  T.kk 0 = 0 → T.typeI = false → T.rcount = 1 → T.kk 1 = 1 → T.charsZ.1 + T.charsZ.2.2.1 ≤ 3 →
    T = loopWordIVb

/-- Case (iv), `k₂ = 1` and `m + u ≤ 3`, by evaluation on the trees after at most three
rounds. -/
private theorem chkIVb_all : ∀ j, j ≤ 3 → ∀ T ∈ loopTree j, chkIVb T := by
  intro j hj
  interval_cases j <;> decide

/-- Every expression reached or expanded by the expansion of §5.3 lies in the tree without
stopping rule after `m + u + 2R - 2` rounds, `(m, n, u, S)` the characters (5.37)
[number_of_G_type_1] and `R` the counting character of (5.50) [counting_character_of_term]. -/
theorem loop_depth (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) :
    T ∈ loopTree (T.charsZ.1 + T.charsZ.2.2.1 + 2 * T.rcount - 2).toNat := by
  refine reach_induct ε n (fun T => T ∈ loopTree (dep T).toNat) (by decide) ?_ T hT
  intro P hP hPQ o T' hT'
  have hd := dep_apply o hT'
  have hn := dep_nonneg (loop_reach ε n P (Or.inr hP)).2.2.2
  have h1 : (dep T').toNat = (dep P).toNat + 1 := by omega
  change T' ∈ loopTree (dep T').toNat
  rw [h1]
  exact loopTree_step hPQ (mem_step_of_apply hT')

/-- (5.37) [number_of_G_type_1] with (5.36) [eq:loop]: on the expansion of §5.3 every loop
without `Λ̃` has at least two resolvents. -/
theorem loop_free_two (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) :
    ∀ w ∈ T.loops, w.contains (.lamt 0) = false → w.contains (.lamt 1) = false →
      2 ≤ w.countP fun x => match x with | .res _ => true | _ => false := by
  have key := reach_induct ε n J0 j0_start (fun P hP hJ o T' hT' =>
    j0_apply (loop_reach ε n P (Or.inr hP)).1 hJ o hT') T hT
  intro w hw h0 h1
  exact key w hw (nl_of_contains h0 h1)

/-- The counts of (5.37) [number_of_G_type_1] used in (5.52)
[light_weight_cancel_imaginary_part]: `m - k₁ - k₂ ≥ 2(n - 1)` for Type I and
`m - k₁ - k₂ ≥ 2(n - 2)` for Type II. -/
theorem loop_count_res (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) :
    (T.typeI = true →
      2 * (T.charsZ.2.1 - 1) ≤ T.charsZ.1 - (T.kk 0 : ℤ) - (T.kk 1 : ℤ)) ∧
    (T.typeI = false →
      2 * (T.charsZ.2.1 - 2) ≤ T.charsZ.1 - (T.kk 0 : ℤ) - (T.kk 1 : ℤ)) := by
  have hw := (loop_reach ε n T hT).1
  have hJ : J0 T := fun w hw' hnl =>
    loop_free_two ε n T hT w hw' (contains_of_nl hnl 0) (contains_of_nl hnl 1)
  have hm : T.charsZ.1 = (((T.loops.map fun w => w.countP rcR).sum : ℕ) : ℤ) := rfl
  have hn : T.charsZ.2.1 = (T.loops.length : ℤ) := rfl
  constructor
  · intro hI
    have := count_type1 hw hJ hI
    rw [hm, hn]
    omega
  · intro hI
    have := count_type2 hw hJ hI
    rw [hm, hn]
    omega

/-- Case (iii) of the direct estimation in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: a Type II expression with `k₁ ≥ 1` has `k₂ ≥ 2`. -/
theorem loop_kk_typeII (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) :
    T.typeI = false → 1 ≤ T.kk 0 → 2 ≤ T.kk 1 := by
  exact reach_induct ε n IT (fun h => absurd h (by decide)) (fun P hP hI o T' hT' =>
    (kstep_apply (loop_reach ε n P (Or.inr hP)).1 o hT').2.2 hI) T hT

/-- The exceptional case of (ii) in the direct estimation of the proof of Lemma 5.5
[claim_estimate_remainder_terms]: the only expanded Type I expression with `k₁ = 0`, `R = 1` and
`m + u = 1` is `⟨𝔐₀ Λ̃₁ 𝒢₁ Λ̃₂⟩`. -/
theorem loop_word_ii (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hk : T.kk 0 = 0) (hI : T.typeI = true) (hR : T.rcount = 1)
    (hmu : T.charsZ.1 + T.charsZ.2.2.1 = 1) : T = loopWordII := by
  have hd := loop_depth ε n T (Or.inr hT)
  have h1 : (T.charsZ.1 + T.charsZ.2.2.1 + 2 * T.rcount - 2).toNat = 1 := by omega
  rw [h1] at hd
  exact chkII_all T hd hk hI hR hmu

/-- The exceptional cases of (iv) in the direct estimation of the proof of Lemma 5.5
[claim_estimate_remainder_terms]: an expanded Type II expression with `k₁ = 0` and `R = 1` is
`loopWordIV` when `m + u ≤ 2`, and `loopWordIVb` when `k₂ = 1` and `m + u ≤ 3`. -/
theorem loop_word_iv (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopInner ε n [loopStart])
    (hk : T.kk 0 = 0) (hII : T.typeI = false) (hR : T.rcount = 1) :
    (T.charsZ.1 + T.charsZ.2.2.1 ≤ 2 → T = loopWordIV) ∧
      (T.kk 1 = 1 → T.charsZ.1 + T.charsZ.2.2.1 ≤ 3 → T = loopWordIVb) := by
  have hd := loop_depth ε n T (Or.inr hT)
  have hn := dep_nonneg (loop_reach ε n T (Or.inr hT)).2.2.2
  unfold dep at hn
  constructor
  · intro hmu
    have h1 : (T.charsZ.1 + T.charsZ.2.2.1 + 2 * T.rcount - 2).toNat ≤ 2 := by omega
    exact chkIVa_all _ h1 T hd hk hII hR hmu
  · intro hk1 hmu
    have h1 : (T.charsZ.1 + T.charsZ.2.2.1 + 2 * T.rcount - 2).toNat ≤ 3 := by omega
    exact chkIVb_all _ h1 T hd hk hII hR hk1 hmu


end RBMTransitionEdge

end
