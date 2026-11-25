module

public import RBMTransitionEdge.Localized.Expansion.Reach

@[expose] public section

/-!
# The leaves of the expansion of §5.3 with no resolvent left next to `Λ̃`

The signed sum over the four starting loops of (5.29) [expansion_of_im] of the expectation of a
leaf with `k₁ = k₂ = 0` is `≺ N^{2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` at the slots of Lemma 5.2
[lemma_localized_eigenvector_local_law] and of Lemma 5.4 [lemma_localized_eigenvalue_local_law]
((5.50)–(5.64)).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

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

/-- The three facts on `k₁`, `k₂` carried by one step `T → T'`: `k₂ ≥ 1` stays when `k₁ ≥ 1`;
`k₁ ≥ 1` stays when `k₁ ≥ 1` and the step is not `𝔯` (`nonrep`); `k₁ = 0` stays. -/
private def KStep (T T' : LoopExpr) (nonrep : Prop) : Prop :=
  (1 ≤ T.kk 0 → 1 ≤ T.kk 1 → 1 ≤ T'.kk 1) ∧ (nonrep → 1 ≤ T.kk 0 → 1 ≤ T'.kk 0) ∧
    (T.kk 0 = 0 → T'.kk 0 = 0) ∧ (nonrep → T.kk 0 = 0 → 1 ≤ T'.kk 1)

/-- `KStep` with the trivial side condition implies it for every side condition. -/
private theorem KStep.of_true {T T' : LoopExpr} (p : Prop) (h : KStep T T' True) : KStep T T' p :=
  ⟨h.1, fun _ => h.2.1 trivial, h.2.2.1, fun _ => h.2.2.2 trivial⟩

/-- The steps `𝔯`, `𝔠₁`, `𝔭₁`, `𝔭₂` (with `Λ̃`-free `f`) replace the focused loop by
`𝔐_a tl X` with `Λ̃`-free `X`. -/
private theorem kstep_set {T T' : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) (X w' : List LoopLetter) (hX : NL X)
    (hw' : w' = .det a :: tl ++ X) (nonrep : Prop) (hres : nonrep → 1 ≤ X.countP rcR)
    (hL : ∀ o'', T'.kk o'' = ((T.loops.set ℓ w').map (kloop o'')).sum) :
    KStep T T' nonrep := by
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
  rcases hoo with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
  · refine ⟨fun _ h => ?_, fun hn _ => ?_, fun h => by omega, fun _ h => by omega⟩
    · omega
    · have := hres hn
      omega
  · refine ⟨fun h => by omega, fun _ h => by omega, fun _ => ?_, fun hn _ => ?_⟩
    · omega
    · have := hres hn
      omega

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
private theorem kstep_plug2 {T T' : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) {j : ℕ} (hj : j ≠ ℓ)
    {f : List LoopLetter} (hfj : T.loops[j]? = some f) {q : ℕ} {b : Fin 2}
    (hq : f[q]? = some (.res b)) (n : ℕ)
    (hL : ∀ o'', T'.kk o'' = (((T.loops.set ℓ (.det a :: tl ++ [.res a, .proj n] ++ f.rotate q ++
      [.res b, .proj n])).eraseIdx j).map (kloop o'')).sum) : KStep T T' True := by
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
  by_cases hfl : ∃ k, LoopLetter.lamt k ∈ f
  · -- `f` carries the other `Λ̃`
    obtain ⟨k, hk0⟩ := hfl
    have hko : k = o' := by
      rcases fin2_cases F.ne k with rfl | rfl
      · exact absurd hk0 hfo
      · rfl
    subst hko
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
    · refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun h => by omega, fun _ h => by omega⟩
      · omega
      · omega
    · exfalso
      omega
  · -- `f` has no `Λ̃`
    have hnf : NL f := fun k hk => hfl ⟨k, hk⟩
    have hX : NL ([LoopLetter.res a, LoopLetter.proj n] ++ f.rotate q ++
        [LoopLetter.res b, LoopLetter.proj n]) :=
      nl_append (nl_append (nl_pair a n) (nl_rotate hnf q)) (nl_pair b n)
    refine kstep_set hT hf _ (.det a :: (B ++ .lamt o :: Y) ++ [.res a, .proj n] ++ f.rotate q ++
      [.res b, .proj n]) hX (by simp) True (fun _ => ?_) ?_
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
private theorem kstep_cut2 {T T' : LoopExpr} (hT : T.wf = true) {ℓ : ℕ} {a : Fin 2}
    {tl : List LoopLetter} (hf : T.focus = some (ℓ, a, tl)) {q : ℕ} {b : Fin 2}
    (hq : tl[q]? = some (LoopLetter.res b)) (n : ℕ)
    (hL : ∀ o'', T'.kk o'' = (((T.loops.set ℓ (LoopLetter.det a :: tl.take (q + 1) ++
      [LoopLetter.proj n])) ++ [LoopLetter.proj n :: tl.drop q ++ [LoopLetter.res a]]).map
        (kloop o'')).sum) : KStep T T' True := by
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
  rw [e1, e2] at hL
  generalize (B ++ LoopLetter.lamt o :: Y).take q = X₁ at hL e3
  generalize (B ++ LoopLetter.lamt o :: Y).drop (q + 1) = X₂ at hL e3
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
      kloop o' (LoopLetter.proj n :: (LoopLetter.res b :: X₂) ++ [LoopLetter.res a]) = 0) ∨
      (kloop o' (LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (c' ++ [LoopLetter.res b])) ++
        [LoopLetter.proj n]) = 0 ∧
      1 ≤ kloop o' (LoopLetter.proj n :: (LoopLetter.res b :: X₂) ++ [LoopLetter.res a]) ∧
      1 ≤ kloop o' w) := by
    by_cases hm : LoopLetter.lamt o' ∈ c' ++ LoopLetter.res b :: X₂
    · rcases List.mem_append.1 hm with hm | hm
      · -- `Λ̃_{o'}` before `𝒢_b`
        obtain ⟨Y₁, c'', rfl⟩ := List.append_of_mem hm
        have hY : (Y₁ ++ LoopLetter.lamt o' :: c'') ++ LoopLetter.res b :: X₂ =
            Y₁ ++ LoopLetter.lamt o' :: (c'' ++ LoopLetter.res b :: X₂) := by simp
        obtain ⟨hn1, hn2, hold⟩ := F.old_o' hY
        left
        refine ⟨?_, ?_⟩
        · rw [hold]
          have h1 : LoopLetter.det a :: (B ++ LoopLetter.lamt o :: ((Y₁ ++ LoopLetter.lamt o' ::
              c'') ++ [LoopLetter.res b])) ++ [LoopLetter.proj n] =
              LoopLetter.det a :: (B ++ LoopLetter.lamt o :: (Y₁ ++ LoopLetter.lamt o' ::
                (c'' ++ [LoopLetter.res b]))) ++ [LoopLetter.proj n] := by simp
          rw [h1, kloop_lam_form F.ne hnB hn1]
        · have hX2 : LoopLetter.lamt o' ∉ X₂ := fun h => hn2 o' (by simp [h])
          exact kloop_of_not_mem (by simp [hX2])
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
          refine ⟨?_, ?_, ?_⟩
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
            have : 0 < (LoopLetter.res a :: LoopLetter.proj n :: LoopLetter.res b :: d₁).countP
                rcR := by
              rw [List.countP_pos_iff]
              exact ⟨.res a, by simp, rfl⟩
            omega
          · rw [hold]
            have : 0 < (c' ++ LoopLetter.res b :: d₁).countP rcR := by
              rw [List.countP_pos_iff]
              exact ⟨.res b, by simp, rfl⟩
            omega
    · left
      have hc : LoopLetter.lamt o' ∉ c' := fun h => hm (List.mem_append_left _ h)
      have hX2 : LoopLetter.lamt o' ∉ X₂ := fun h =>
        hm (List.mem_append_right _ (List.mem_cons_of_mem _ h))
      refine ⟨?_, ?_⟩
      · rw [kloop_of_not_mem (F.not_mem_w hm), kloop_of_not_mem]
        simp [hnB o', Ne.symm F.ne, hc]
      · exact kloop_of_not_mem (by simp [hX2])
  have s0 := hsum o
  have s1 := hsum o'
  have kw0 := hkw o
  have kw1 := hkw o'
  rcases hoo with ⟨rfl, rfl, hk1⟩ | ⟨rfl, rfl, hk1⟩
  · refine ⟨fun _ hk2 => ?_, fun _ _ => ?_, fun h => by omega, fun _ h => by omega⟩
    · rcases hcase with h | h <;> omega
    · omega
  · refine ⟨fun h => by omega, fun _ h => by omega, fun _ => ?_, fun _ _ => ?_⟩
    · rcases hcase with h | h <;> omega
    · rcases hcase with h | h <;> omega

/-- Each of the five operations of (5.42)–(5.46) preserves the facts on `k₁`, `k₂` of `KStep`. -/
private theorem kstep_apply {T T' : LoopExpr} (hT : T.wf = true) (op : LoopOp)
    (h : T' ∈ T.apply op) : KStep T T' (op ≠ .rep) := by
  cases op
  · -- `𝔯`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      simp only [List.mem_singleton] at h
      subst h
      exact kstep_set hT hf [] (.det a :: tl) (fun k hk => by simp at hk) (by simp) _
        (fun hn => absurd rfl hn) (fun o'' => kk_eq _ o'')
  · -- `𝔠₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      simp only [List.mem_singleton] at h
      subst h
      exact kstep_set hT hf [.res a, .proj T.nb] _ (nl_pair a T.nb) rfl _
        (fun _ => by simp [rcR]) (fun o'' => kk_eq _ o'')
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
        have := kstep_cut2 hT hf hq T.nb (T' := { T with
          dexp := T.dexp + 1, nb := T.nb + 1,
          loops := T.loops.set ℓ (.det a :: tl.take (q + 1) ++ [.proj T.nb]) ++
            [.proj T.nb :: tl.drop q ++ [.res a]] }) (fun o'' => kk_eq _ o'')
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
        exact kstep_set hT hf [.res a, .proj T.nb, .res b, .proj y, .res b, .proj T.nb] _
          (fun k hk => by simp at hk) rfl _ (fun _ => by simp [rcR]) (fun o'' => kk_eq _ o'')
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
            have := kstep_plug2 hT hf hjl hf2 hq T.nb (T' := { T with
              dexp := T.dexp - 1, S := T.S + 2, nb := T.nb + 1,
              loops := (T.loops.set ℓ (.det a :: tl ++ [.res a, .proj T.nb] ++ f.rotate q ++
                [.res b, .proj T.nb])).eraseIdx j }) (fun o'' => kk_eq _ o'')
            exact this.of_true _
          · simp at h6

/-! ### The characters (5.50) and the invariants of the reachable expressions -/

/-- The characters of (5.50) [counting_character_of_term] with the counts `R, C₁, C₂, P₁, P₂` of
the operations `𝔯, 𝔠₁, 𝔠₂, 𝔭₁, 𝔭₂`. -/
private def Cnt (T : LoopExpr) : Prop :=
  ∃ R C₁ C₂ P₁ P₂ : ℕ, T.charsZ = ((2 : ℤ) - R + C₂ + 2 * P₁ + P₂, (1 : ℤ) + C₂ - P₂,
    (C₁ : ℤ) - P₁, 2 * (P₁ : ℤ) + 2 * P₂)

/-- `R` is nonnegative on the class `Cnt`. -/
private theorem Cnt.rcount_nonneg {T : LoopExpr} (h : Cnt T) : 0 ≤ T.rcount := by
  obtain ⟨R, C₁, C₂, P₁, P₂, h⟩ := h
  simp only [LoopExpr.rcount, h]
  omega

/-- One operation keeps (5.50) [counting_character_of_term] and raises `R` by one exactly for `𝔯`
(Table 1 [table_effect_of_operations]). -/
private theorem cnt_apply {T T' : LoopExpr} (op : LoopOp) (h : T' ∈ T.apply op) (hC : Cnt T) :
    Cnt T' ∧ T'.rcount = T.rcount + (if op = .rep then 1 else 0) := by
  have hz := loop_table1 T op T' h
  obtain ⟨R, C₁, C₂, P₁, P₂, hc⟩ := hC
  rw [hc] at hz
  cases op
  · simp only [LoopOp.delta, Prod.mk_add_mk] at hz
    refine ⟨⟨R + 1, C₁, C₂, P₁, P₂, ?_⟩, ?_⟩
    · rw [hz]; simp only [Prod.mk.injEq]; push_cast; omega
    · simp only [LoopExpr.rcount, hz, hc]; simp; omega
  · simp only [LoopOp.delta, Prod.mk_add_mk] at hz
    refine ⟨⟨R, C₁ + 1, C₂, P₁, P₂, ?_⟩, ?_⟩
    · rw [hz]; simp only [Prod.mk.injEq]; push_cast; omega
    · simp only [LoopExpr.rcount, hz, hc]; simp
  · simp only [LoopOp.delta, Prod.mk_add_mk] at hz
    refine ⟨⟨R, C₁, C₂ + 1, P₁, P₂, ?_⟩, ?_⟩
    · rw [hz]; simp only [Prod.mk.injEq]; push_cast; omega
    · simp only [LoopExpr.rcount, hz, hc]; simp; omega
  · simp only [LoopOp.delta, Prod.mk_add_mk] at hz
    refine ⟨⟨R, C₁, C₂, P₁ + 1, P₂, ?_⟩, ?_⟩
    · rw [hz]; simp only [Prod.mk.injEq]; push_cast; omega
    · simp only [LoopExpr.rcount, hz, hc]; simp
  · simp only [LoopOp.delta, Prod.mk_add_mk] at hz
    refine ⟨⟨R, C₁, C₂, P₁, P₂ + 1, ?_⟩, ?_⟩
    · rw [hz]; simp only [Prod.mk.injEq]; push_cast; omega
    · simp only [LoopExpr.rcount, hz, hc]; simp; omega

/-! ### The deterministic limit at `Λ = 0` -/

/-- `M(0, z) = m_sc(z) · 1` for `Im z > 0` (the form of (A.5) [eq:msc] with `Λ = 0`, from
`eq_msc_traceless`): the slot `𝔐₀` of Lemma 5.2 [lemma_localized_eigenvector_local_law]. -/
private lemma Rch_MExt_zero (D N : ℕ) (hD : 0 < D) (hN : 0 < N) (z : ℂ) (hz : 0 < z.im) :
    MExt (0 : Matrix (Idx D N) (Idx D N) ℂ) z = msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨C, hC, hCs⟩ := eq_msc_traceless (‖z‖ + 1)⁻¹ (by positivity)
  have h := hCs (Idx D N) 0 Matrix.isHermitian_zero (by simp [opNorm]) (by simp [ntr]) z
    (by rw [inv_inv]; linarith) hz
  have h0 : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by simp [opNorm]
  rw [h0, mul_zero] at h
  have h1 : 0 ≤ ‖mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z - msc z‖ := norm_nonneg _
  have h2 : 0 ≤ opNorm (MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z -
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := norm_nonneg _
  have h3 : MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z =
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    ext i j
    have := norm_apply_le_opNorm (MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z -
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) i j
    have h4 : ‖(MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z -
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) i j‖ = 0 :=
      le_antisymm (this.trans (by linarith)) (norm_nonneg _)
    rw [norm_eq_zero] at h4
    exact sub_eq_zero.1 h4
  have h5 : mExt (0 : Matrix (Idx D N) (Idx D N) ℂ) z =
      mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z := by simp [mExt, hz]
  rw [← h3]
  simp [MExt, MSol, h5]

/-- The slot `𝔐₀` of Lemma 5.2 [lemma_localized_eigenvector_local_law] with its flag:
`m_sc(z₀) · 1`, or its conjugate for `𝒢₀ = G₀^*`. -/
private lemma Rch_slot_zero (D N : ℕ) (hD : 0 < D) (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (s : Bool) :
    MExt ((((0 : ℝ) : ℂ)) • lam D N A) (if s then star z else z) =
      (if s then star (msc z) else msc z) • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have h1 := Rch_MExt_zero D N hD hN z hz
  cases s
  · simpa using h1
  · have h2 := (mExt_conj (0 : Matrix (Idx D N) (Idx D N) ℂ) Matrix.isHermitian_zero z hz.ne').2
    simp only [Complex.ofReal_zero, zero_smul, ite_true]
    rw [h2, h1, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- The flag of a slot: `𝔐(z̄) = 𝔐(z)^*` for Hermitian `Λ` and `Im z ≠ 0` (Definition 2.7
[defn_Mm]), in the form `MExt Λ (if s then z̄ else z) = if s then 𝔐(z)^* else 𝔐(z)`. -/
private lemma Rch_flag {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (s : Bool) :
    MExt Λ (if s then star z else z) = if s then (MExt Λ z)ᴴ else MExt Λ z := by
  cases s
  · rfl
  · exact (mExt_conj Λ hΛ z hz).2

/-- The slot-dependent traces of `Λ̃`: `Λ̃ = Λ - δ` is Hermitian. -/
private lemma Rch_Lt_herm {D N : ℕ} (e : LoopEnv D N) : e.Lt.IsHermitian := by
  unfold LoopEnv.Lt
  refine (lam_isHermitian D N e.A).sub ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp


/-! ## The invariants of the expressions of the expansion -/

/-- The rounds of the expansion of the starting loop (5.30) [starting_point_of_expansion] in which
every expression with `k₁ + k₂ ≥ 1` is expanded. -/
private def allS : ℕ → List LoopExpr
  | 0 => [loopStart]
  | n + 1 => (allS n).flatMap fun T => if T.kk 0 = 0 ∧ T.kk 1 = 0 then [] else T.step

/-- The number `-m + 2n + u + 2S = R + C₁ + C₂ + P₁ + P₂` of operations on a path from the
starting loop, for the characters `(m, n, u, S)` of (5.37) [number_of_G_type_1]. -/
private def depth (T : LoopExpr) : ℤ :=
  match T.charsZ with
  | (m, n, u, S) => -m + 2 * n + u + 2 * S

/-- Every loop without `Λ̃` has at least two resolvents. -/
private def J0 (T : LoopExpr) : Prop :=
  ∀ w ∈ T.loops, NL w → 2 ≤ w.countP rcR

/-- The invariants of the reachable expressions used for the leaves: the class `𝒯`,
`k₁ ≥ 1 ⇒ k₂ ≥ 1`, `k₁ = 0 ⇒ R ≥ 1`, (5.50) [counting_character_of_term], two resolvents in every
loop without `Λ̃`, `R ≥ 2` when `k₁ = k₂ = 0`, and the number of operations. -/
private def Inv (T : LoopExpr) : Prop :=
  T.wf = true ∧ (1 ≤ T.kk 0 → 1 ≤ T.kk 1) ∧ (T.kk 0 = 0 → 1 ≤ T.rcount) ∧ Cnt T ∧ J0 T ∧
    (T.kk 0 = 0 → T.kk 1 = 0 → 2 ≤ T.rcount) ∧ ∃ j : ℕ, T ∈ allS j ∧ (j : ℤ) = depth T

/-- One operation raises the number of operations by one (Table 1
[table_effect_of_operations]). -/
private theorem depth_apply {T T' : LoopExpr} (op : LoopOp) (h : T' ∈ T.apply op) :
    depth T' = depth T + 1 := by
  have hz := loop_table1 T op T' h
  unfold depth
  rw [hz]
  generalize T.charsZ = c
  obtain ⟨m, n, u, S⟩ := c
  cases op <;> simp only [LoopOp.delta, Prod.mk_add_mk] <;> ring

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

/-- Every term of (5.40) [expansion_for_integral_by_part_term] of an expanded expression with the
invariants has them. -/
private theorem inv_step {T T' : LoopExpr} (hI : Inv T) (hk : ¬ (T.kk 0 = 0 ∧ T.kk 1 = 0))
    (h : T' ∈ T.step) : Inv T' := by
  obtain ⟨hw, h2, h3, hC, hJ, -, j, hj, hjd⟩ := hI
  have hwf := loop_step_wf T hw T' h
  have hmem := h
  simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨op, -, h⟩ := h
  have hK := kstep_apply hw op h
  obtain ⟨hC', hr⟩ := cnt_apply op h hC
  have hnn := hC.rcount_nonneg
  have hd := depth_apply op h
  refine ⟨hwf, ?_, ?_, hC', j0_apply hw hJ op h, ?_, j + 1, ?_, ?_⟩
  · intro h1'
    by_cases hk0 : 1 ≤ T.kk 0
    · exact hK.1 hk0 (h2 hk0)
    · exfalso
      have := hK.2.2.1 (by omega)
      omega
  · intro h0'
    by_cases hk0 : 1 ≤ T.kk 0
    · by_cases hrep : op = .rep
      · subst hrep
        simp at hr
        omega
      · have := hK.2.1 hrep hk0
        omega
    · have h5 := h3 (by omega)
      split_ifs at hr <;> omega
  · intro h0' h1'
    by_cases hk0 : 1 ≤ T.kk 0
    · have := hK.1 hk0 (h2 hk0)
      omega
    · have hk0' : T.kk 0 = 0 := by omega
      have h5 := h3 hk0'
      by_cases hrep : op = .rep
      · subst hrep
        simp at hr
        omega
      · have := hK.2.2.2 hrep hk0'
        omega
  · simp only [allS, List.mem_flatMap]
    exact ⟨T, hj, by rw [ite_eq_right_iff.2 (fun h => absurd h hk)]; exact hmem⟩
  · push_cast
    rw [hd, ← hjd]

/-- The invariants pass to every expression of the next round. -/
private theorem inv_next (ε : ℝ) {L : List LoopExpr} (hL : ∀ T ∈ L, Inv T) :
    ∀ T ∈ L.flatMap (fun T => if T.Stopped ε then [T] else T.step), Inv T := by
  intro T' hT'
  obtain ⟨T, hT, h⟩ := List.mem_flatMap.1 hT'
  by_cases hs : T.Stopped ε
  · simp only [hs, ite_true, List.mem_singleton] at h
    subst h
    exact hL _ hT
  · simp only [hs, ite_false] at h
    exact inv_step (hL _ hT) (fun hk => hs (Or.inr hk)) h

/-- The invariants hold on every expression of the rounds (5.49) [operation_sequence]. -/
private theorem inv_iter (ε : ℝ) :
    ∀ (n : ℕ) (L : List LoopExpr), (∀ T ∈ L, Inv T) → ∀ T ∈ loopIter ε n L, Inv T
  | 0, _, hL, T, hT => hL T hT
  | n + 1, _, hL, T, hT => inv_iter ε n _ (inv_next ε hL) T hT

/-- The starting loop (5.30) [starting_point_of_expansion] has the invariants. -/
private theorem inv_start : Inv loopStart := by
  refine ⟨by decide, fun _ => by decide, fun h => absurd h (by decide),
    ⟨0, 0, 0, 0, 0, by decide⟩, ?_, fun h => absurd h (by decide), 0, by simp [allS],
    by decide⟩
  intro w hw hnl
  simp only [loopStart, List.mem_singleton] at hw
  subst hw
  exact absurd (by simp) (hnl 0)

/-- The invariants hold on every expression of the rounds of the starting loop. -/
private theorem inv_of_mem {ε : ℝ} {n : ℕ} {T : LoopExpr} (hT : T ∈ loopIter ε n [loopStart]) :
    Inv T :=
  inv_iter ε n _ (fun T hT => by rw [List.mem_singleton.1 hT]; exact inv_start) T hT

/-! ## The structure of the leaves with `k₁ = k₂ = 0` -/

/-- At an expression of the class with `k₁ = k₂ = 0`, a loop containing a `Λ̃` contains no
resolvent. -/
private theorem leaf_lam_nores {T : LoopExpr} (hT : T.wf = true) (h0 : T.kk 0 = 0)
    (h1 : T.kk 1 = 0) {w : List LoopLetter} (hw : w ∈ T.loops) (o : Fin 2)
    (ho : LoopLetter.lamt o ∈ w) : w.countP rcR = 0 := by
  obtain ⟨ℓ, hℓ⟩ := List.mem_iff_getElem?.1 hw
  have hc := count_le_one hT hw
  have hk : ∀ k, LoopLetter.lamt k ∈ w → kloop k w = 0 := by
    intro k hk'
    rw [← kk_eq_kloop hT k hℓ hk']
    fin_cases k
    · exact h0
    · exact h1
  have hkw := hk o ho
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
  rw [hkw] at e1
  obtain ⟨o', hne, ho'⟩ : ∃ o' : Fin 2, o ≠ o' ∧ ∀ k, k = o ∨ k = o' := by
    fin_cases o
    · exact ⟨1, by decide, fun k => by fin_cases k <;> simp⟩
    · exact ⟨0, by decide, fun k => by fin_cases k <;> simp⟩
  have hcount : (u ++ LoopLetter.lamt o :: v).countP rcR = (v ++ u).countP rcR := by
    simp [List.countP_append, rcR]
    omega
  rw [hcount]
  by_cases hm : LoopLetter.lamt o' ∈ v ++ u
  · obtain ⟨g₁, g₂, hg⟩ := List.append_of_mem hm
    have hco' := hc o'
    have hperm : (u ++ LoopLetter.lamt o :: v).count (.lamt o') = (v ++ u).count (.lamt o') := by
      have hne' : LoopLetter.lamt o ≠ LoopLetter.lamt o' := fun h => hne (LoopLetter.lamt.inj h)
      simp [List.count_append, List.count_cons, hne']
      omega
    rw [hperm, hg] at hco'
    have hno : ∀ k, k ≠ o' → LoopLetter.lamt k ∉ g₁ ++ .lamt o' :: g₂ := by
      intro k hk hm'
      rcases ho' k with rfl | rfl
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
    have hm2 : LoopLetter.lamt o' ∈ u ++ LoopLetter.lamt o :: v := by
      rcases List.mem_append.1 hm with h' | h'
      · simp [h']
      · simp [h']
    have e3 := kloop_rotate o' u.length (u ++ LoopLetter.lamt o :: v) (hc o')
    rw [hrot, hk o' hm2] at e3
    have hu' : LoopLetter.lamt o' ∉ LoopLetter.lamt o :: g₁ := by
      intro h'
      rcases List.mem_cons.1 h' with h' | h'
      · exact hne (LoopLetter.lamt.inj h').symm
      · exact hn1 o' h'
    have e4 := kloop_eq (u := LoopLetter.lamt o :: g₁) (v := g₂) o' hu'
    have e3' : kloop o' (LoopLetter.lamt o :: g₁ ++ LoopLetter.lamt o' :: g₂) = 0 := e3
    rw [e3'] at e4
    have e5 := lseg_append_lam (P := g₂) o hn1
    rw [e5] at e4
    rw [hg]
    simp only [List.countP_append, List.countP_cons, rcR]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    omega
  · have hnl : NL (v ++ u) := by
      intro k hk'
      rcases ho' k with rfl | rfl
      · rcases List.mem_append.1 hk' with h' | h'
        · exact hv h'
        · exact hu h'
      · exact hm hk'
    have h7 : lseg (v ++ u) = (v ++ u).countP rcR := by
      have := lseg_append_free (P := []) hnl
      simpa [lseg] using this
    omega

/-! ## The leaves of small size -/

/-- Some loop contains both `Λ̃` (Type I, (5.34) [Gamma_Type_1]). -/
private def typeI (T : LoopExpr) : Bool :=
  T.loops.any fun w => w.contains (.lamt 0) && w.contains (.lamt 1)

/-- The leaves bounded flag by flag from their characters, (5.51) [estimate_loop_type_1] and the
Type II bound after (5.58) [eq:polar2]: Type I with `R ≥ 3` or `m + u ≥ 2`, Type II with `R ≥ 4`,
`R = 3, m + u ≥ 1` or `m + u ≥ 4`. -/
private def genB (T : LoopExpr) : Bool :=
  match T.charsZ with
  | (m, _, u, _) => if typeI T then decide (3 ≤ T.rcount ∨ (T.rcount = 2 ∧ 2 ≤ m + u))
      else decide (4 ≤ T.rcount ∨ (T.rcount = 3 ∧ 1 ≤ m + u) ∨ (T.rcount = 2 ∧ 4 ≤ m + u))

/-- The leaf (5.54) [expansion_result_R_2_C_0_P_0]: `⟨𝔐₁ Λ̃₂ 𝔐₀ Λ̃₁⟩`. -/
private abbrev lf54 : LoopExpr := ⟨0, 0, 0, [], [[.det 1, .lamt 1, .det 0, .lamt 0]]⟩

/-- The first leaf of (5.55) [expansion_result_R_2_C_1_P_0]:
`D Σ_x ⟨(𝒢₁ - 𝔐₁) E_x⟩ ⟨𝔐₁ E_x 𝔐₁ Λ̃₂ 𝔐₀ Λ̃₁⟩`. -/
private abbrev lf55a : LoopExpr :=
  ⟨1, 0, 1, [(1, 0)], [[.det 1, .proj 0, .det 1, .lamt 1, .det 0, .lamt 0]]⟩

/-- The second leaf of (5.55) [expansion_result_R_2_C_1_P_0]:
`D Σ_x ⟨(𝒢₀ - 𝔐₀) E_x⟩ ⟨𝔐₁ Λ̃₂ 𝔐₀ E_x 𝔐₀ Λ̃₁⟩`. -/
private abbrev lf55b : LoopExpr :=
  ⟨1, 0, 1, [(0, 0)], [[.det 1, .lamt 1, .det 0, .proj 0, .det 0, .lamt 0]]⟩

/-- The leaf (5.59) [sR_3_sC_2_2_sC_1_sP_1_sP_2_0]: `D Σ_x ⟨𝔐₁ E_x 𝔐₀ Λ̃₁⟩ ⟨𝔐₀ E_x 𝔐₁ Λ̃₂⟩`. -/
private abbrev lf59 : LoopExpr :=
  ⟨1, 0, 1, [], [[.det 1, .proj 0, .det 0, .lamt 0], [.det 0, .proj 0, .det 1, .lamt 1]]⟩

/-- The leaf (5.60) [sR_2_sC_2_2_sC_1_sP_1_sP_2_0]:
`D² Σ_{x,y} ⟨𝔐₁ E_x 𝔐₀ Λ̃₁⟩ ⟨𝔐₀ E_y 𝔐₁ Λ̃₂⟩ ⟨E_y 𝒢₀ E_x 𝒢₁⟩`. -/
private abbrev lf60 : LoopExpr :=
  ⟨2, 0, 2, [], [[.det 1, .proj 0, .det 0, .lamt 0], [.det 0, .proj 1, .det 1, .lamt 1],
    [.proj 1, .res 0, .proj 0, .res 1]]⟩

/-- The first term of (5.61) [sR_2_sC_2_2_sC_1_1_sP_1_sP_2_0]. -/
private abbrev lf61a : LoopExpr :=
  ⟨3, 0, 3, [(0, 0)], [[.det 1, .proj 1, .det 0, .proj 0, .det 0, .lamt 0],
    [.det 0, .proj 2, .det 1, .lamt 1], [.proj 2, .res 0, .proj 1, .res 1]]⟩

/-- The second term of (5.61) [sR_2_sC_2_2_sC_1_1_sP_1_sP_2_0]. -/
private abbrev lf61b : LoopExpr :=
  ⟨3, 0, 3, [(1, 1)], [[.det 1, .proj 0, .det 0, .lamt 0],
    [.det 0, .proj 2, .det 1, .proj 1, .det 1, .lamt 1], [.proj 2, .res 0, .proj 0, .res 1]]⟩

/-- The third term of (5.61) [sR_2_sC_2_2_sC_1_1_sP_1_sP_2_0]. -/
private abbrev lf61c : LoopExpr :=
  ⟨3, 0, 3, [(0, 2)], [[.det 1, .proj 0, .det 0, .lamt 0],
    [.det 0, .proj 2, .det 0, .proj 1, .det 1, .lamt 1], [.proj 1, .res 0, .proj 0, .res 1]]⟩

/-- The fourth term of (5.61) [sR_2_sC_2_2_sC_1_1_sP_1_sP_2_0]. -/
private abbrev lf61d : LoopExpr :=
  ⟨3, 0, 3, [(1, 1)], [[.det 1, .proj 1, .det 1, .proj 0, .det 0, .lamt 0],
    [.det 0, .proj 2, .det 1, .lamt 1], [.proj 2, .res 0, .proj 0, .res 1]]⟩

/-- The leaves of (5.54)–(5.61) that the characters alone do not bound. -/
private abbrev lfExc : List LoopExpr :=
  [lf54, lf55a, lf55b, lf59, lf60, lf61a, lf61b, lf61c, lf61d]

set_option maxRecDepth 100000 in
/-- The enumeration of the leaves with at most five operations: every leaf with `k₁ = k₂ = 0` is
bounded by its characters or is one of (5.54)–(5.61). -/
private theorem classify_comp : ((List.range 6).all fun j => (allS j).all fun T =>
    !(decide (T.kk 0 = 0 ∧ T.kk 1 = 0)) || genB T || lfExc.contains T) = true := by
  decide +kernel

/-- The characters `m` and `u` are nonnegative. -/
private theorem charsZ_nonneg (T : LoopExpr) : 0 ≤ T.charsZ.1 ∧ 0 ≤ T.charsZ.2.2.1 := by
  unfold LoopExpr.charsZ
  exact ⟨by positivity, by positivity⟩

/-- Every reachable leaf with `k₁ = k₂ = 0` is bounded by its characters or is one of the leaves
(5.54)–(5.61). -/
private theorem leaf_cases {T : LoopExpr} (hI : Inv T) (h0 : T.kk 0 = 0) (h1 : T.kk 1 = 0) :
    genB T = true ∨ T ∈ lfExc := by
  by_cases hg : genB T = true
  · exact Or.inl hg
  · right
    obtain ⟨-, -, -, hC, -, h6, j, hj, hjd⟩ := hI
    have hR := h6 h0 h1
    have hnn := charsZ_nonneg T
    have hj5 : j ≤ 5 := by
      obtain ⟨R, C₁, C₂, P₁, P₂, hc⟩ := hC
      have hRc : T.rcount = R := by
        unfold LoopExpr.rcount
        rw [hc]
        dsimp only
        ring
      have hdc : depth T = R + C₁ + C₂ + P₁ + P₂ := by
        unfold depth
        rw [hc]
        dsimp only
        ring
      unfold genB at hg
      rw [hc] at hg hnn
      dsimp only at hg hnn
      rw [hRc] at hg hR
      rw [hdc] at hjd
      split_ifs at hg <;> simp at hg <;> omega
    have h2 := List.all_eq_true.1 classify_comp j (List.mem_range.2 (by omega))
    have h3 := List.all_eq_true.1 h2 T hj
    simp only [h0, h1, and_self, decide_true, Bool.not_true, Bool.false_or, hg,
      List.elem_eq_mem, decide_eq_true_eq] at h3
    exact h3


/-! ## Norm facts -/

section Norms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma Bd_opNorm_nonneg (X : Matrix ι ι ℂ) : 0 ≤ opNorm X := norm_nonneg _

/-- `|⟨X⟩| ≤ ‖X‖`. -/
private lemma Bd_ntr_le (X : Matrix ι ι ℂ) : ‖ntr X‖ ≤ opNorm X := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [ntr, Matrix.trace, Bd_opNorm_nonneg]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, X.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm X := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm X i i)
      _ = opNorm X := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- `‖X^*‖ = ‖X‖`. -/
private lemma Bd_opNorm_conjTranspose (X : Matrix ι ι ℂ) : opNorm Xᴴ = opNorm X := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) X)

private lemma Bd_opNorm_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

omit [DecidableEq ι] in
/-- `⟨Λ²⟩ ≥ 0` for Hermitian `Λ`. -/
private lemma Bd_avgSq_nonneg (Λ : Matrix ι ι ℂ) (h : Λ.IsHermitian) : 0 ≤ avgSq Λ := by
  open ComplexOrder in
  have hp : (Λ * Λ).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Λ
    rwa [h.eq] at this
  open ComplexOrder in
  have ht : (0 : ℂ) ≤ (Λ * Λ).trace := hp.trace_nonneg
  have h0 : 0 ≤ ((Λ * Λ).trace).re := (Complex.nonneg_iff.mp ht).1
  unfold avgSq ntr
  have e : ((Fintype.card ι : ℂ))⁻¹ * (Λ * Λ).trace =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) * (Λ * Λ).trace := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) h0

/-- `⟨Λ²⟩ ≤ ‖Λ‖²`. -/
private lemma Bd_avgSq_le (Λ : Matrix ι ι ℂ) : avgSq Λ ≤ opNorm Λ ^ 2 := by
  unfold avgSq
  calc (ntr (Λ * Λ)).re ≤ ‖ntr (Λ * Λ)‖ := Complex.re_le_norm _
    _ ≤ opNorm (Λ * Λ) := Bd_ntr_le _
    _ ≤ opNorm Λ * opNorm Λ := opNorm_mul_le _ _
    _ = _ := by ring

/-- For Hermitian `X`, `G(z̄) = G(z)^*`. -/
private lemma Bd_res_star (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) :
    res X (star z) = (res X z)ᴴ := by
  unfold res
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hX.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- `‖G(z)‖ ≤ |Im z|⁻¹` for Hermitian `X` and `Im z ≠ 0`. -/
private lemma Bd_opNorm_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    opNorm (res X z) ≤ |z.im|⁻¹ := by
  rcases lt_or_gt_of_ne hz with h | h
  · have h' : 0 < (star z).im := by simpa using h
    have e : res X z = (res X (star z))ᴴ := by
      rw [← Bd_res_star X hX, star_star]
    rw [e, Bd_opNorm_conjTranspose, abs_of_neg h]
    simpa using opNorm_res_le X hX (star z) h'
  · rw [abs_of_pos h]
    exact opNorm_res_le X hX z h

end Norms

/-- The block projection `E_a` has norm `≤ 1`. -/
private lemma Bd_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `c Λ` is Hermitian for real `c`. -/
private lemma Bd_lamc_herm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    ((c : ℂ) • lam D N A).IsHermitian := by
  have h := lam_isHermitian D N A
  unfold Matrix.IsHermitian at h ⊢
  rw [Matrix.conjTranspose_smul, h]
  simp [Complex.conj_ofReal]

/-- `‖c Λ‖ ≤ 2 |c| ‖A‖`. -/
private lemma Bd_lamc_norm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    opNorm ((c : ℂ) • lam D N A) ≤ |c| * (2 * opNorm A) := by
  rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (opNorm_lam_le D N A) (abs_nonneg _)

/-- `‖M(z)‖ ≤ 5/4` for Hermitian `‖Λ‖ ≤ 1/10` and `Im z ≠ 0`, from `mSol_apriori` and
`M(z̄) = M(z)^*`. -/
private lemma Bd_MExt_norm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : z.im ≠ 0) :
    opNorm (MExt Λ z) ≤ 5 / 4 := by
  have key : ∀ w : ℂ, 0 < w.im → opNorm (MExt Λ w) ≤ 5 / 4 := by
    intro w hw
    have e : MExt Λ w = MSol Λ w := by
      have h : mExt Λ w = mSol Λ w := by unfold mExt; simp [hw]
      unfold MExt MSol
      rw [h]
    rw [e]
    have h1 := (mSol_apriori Λ hΛ hℓ w hw).2.2
    have h0 := Bd_opNorm_nonneg Λ
    have h2 : (1 - 2 * opNorm Λ)⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  rcases lt_or_gt_of_ne hz with h | h
  · have h' : 0 < (star z).im := by simpa using h
    have e := (mExt_conj Λ hΛ (star z) h'.ne').2
    rw [star_star] at e
    rw [e, Bd_opNorm_conjTranspose]
    exact key _ h'
  · exact key z h

/-- `Im m(z) < 1` for Hermitian `‖Λ‖ ≤ 1/10` and `Im z > 0`. -/
private lemma Bd_im_mSol_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    (mSol Λ z).im ≤ 1 :=
  ((Complex.im_le_norm _).trans (mSol_apriori Λ hΛ hℓ z hz).2.1.le)

/-! ## Large `N` -/

/-- `N^{-δ} ≤ x` for all large `N`. -/
private lemma Bd_small (δ x : ℝ) (hδ : 0 < δ) (hx : 0 < x) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-δ) ≤ x := by
  have h := ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually
    (Iio_mem_nhds hx)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, fun N hN => (hN₀ N hN).le⟩

/-- `X ≤ N^a` for all large `N`. -/
private lemma Bd_large (a X : ℝ) (ha : 0 < a) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → X ≤ (N : ℝ) ^ a := by
  have h := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop X)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, hN₀⟩
/-! ## Words as products of resolvents and deterministic factors -/

/-- Resolvent letters. -/
private def Bd_isRes : LoopLetter → Bool
  | .res _ => true
  | _ => false

/-- The letters `Λ̃₁`, `Λ̃₂`. -/
private def Bd_isL : LoopLetter → Bool
  | .lamt _ => true
  | _ => false

/-- The slot of a resolvent letter. -/
private def Bd_slotOf : LoopLetter → Fin 2
  | .res a => a
  | _ => 0

/-- The matrix of a letter. -/
private def Bd_let {ι : Type*} (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) : LoopLetter → Matrix ι ι ℂ
  | .res a => G a
  | .det a => M a
  | .proj y => E y
  | .lamt _ => L

private lemma Bd_wordMat_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (w : List LoopLetter) :
    loopWordMat G M E L w = (w.map (Bd_let G M E L)).prod := by
  rfl

private lemma Bd_isL_count (w : List LoopLetter) :
    w.countP Bd_isL = w.count (.lamt 0) + w.count (.lamt 1) := by
  induction w with
  | nil => simp
  | cons x t ih =>
    rw [List.countP_cons, List.count_cons, List.count_cons, ih]
    rcases x with a | a | y | o
    · simp [Bd_isL]
    · simp [Bd_isL]
    · simp [Bd_isL]
    · fin_cases o <;> simp [Bd_isL] <;> omega

/-- Non-resolvent letters do not see the resolvents. -/
private lemma Bd_let_nonres {ι : Type*} (G G' M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (x : LoopLetter) (hx : Bd_isRes x = false) :
    Bd_let G M E L x = Bd_let G' M E L x := by
  cases x <;> simp_all [Bd_isRes, Bd_let]

/-- Splitting a word at its resolvents: a prefix of deterministic letters, then blocks
`𝒢_a · (deterministic letters)`. -/
private def Bd_dec : List LoopLetter → List LoopLetter × List (Fin 2 × List LoopLetter)
  | [] => ([], [])
  | x :: w => if Bd_isRes x then ([], (Bd_slotOf x, (Bd_dec w).1) :: (Bd_dec w).2)
      else (x :: (Bd_dec w).1, (Bd_dec w).2)

private lemma Bd_dec_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (w : List LoopLetter) :
    (w.map (Bd_let G M E L)).prod = ((Bd_dec w).1.map (Bd_let G M E L)).prod *
      ((Bd_dec w).2.map fun q => G q.1 * (q.2.map (Bd_let G M E L)).prod).prod := by
  induction w with
  | nil => simp [Bd_dec]
  | cons x t ih =>
    by_cases hx : Bd_isRes x = true
    · have : x = .res (Bd_slotOf x) := by cases x <;> simp_all [Bd_isRes, Bd_slotOf]
      simp only [Bd_dec, hx, ite_true, List.map_cons, List.prod_cons, List.map_nil,
        List.prod_nil, one_mul]
      rw [ih, this]
      simp only [Bd_let, Bd_slotOf, Matrix.mul_assoc]
    · simp only [Bd_dec, hx, Bool.false_eq_true, ite_false, List.map_cons, List.prod_cons]
      rw [ih, Matrix.mul_assoc]

private lemma Bd_dec_len (w : List LoopLetter) : (Bd_dec w).2.length = w.countP Bd_isRes := by
  induction w with
  | nil => simp [Bd_dec]
  | cons x t ih =>
    by_cases hx : Bd_isRes x = true
    · simp [Bd_dec, hx, ih]
    · simp [Bd_dec, hx, ih]

/-- The letters of the deterministic segments are non-resolvent letters of the word, and each
segment is at most as long as the word. -/
private lemma Bd_dec_mem (w : List LoopLetter) :
    (∀ x ∈ (Bd_dec w).1, x ∈ w ∧ Bd_isRes x = false) ∧ (Bd_dec w).1.length ≤ w.length ∧
      ∀ q ∈ (Bd_dec w).2, (∀ x ∈ q.2, x ∈ w ∧ Bd_isRes x = false) ∧ q.2.length ≤ w.length := by
  induction w with
  | nil => simp [Bd_dec]
  | cons x t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases hx : Bd_isRes x = true
    · have e : Bd_dec (x :: t) = ([], (Bd_slotOf x, (Bd_dec t).1) :: (Bd_dec t).2) := by
        simp [Bd_dec, hx]
      rw [e]
      refine ⟨by simp, by simp, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨fun y hy => ⟨List.mem_cons_of_mem _ (h1 y hy).1, (h1 y hy).2⟩,
          by simp only [List.length_cons]; omega⟩
      · exact ⟨fun y hy => ⟨List.mem_cons_of_mem _ ((h3 q hq).1 y hy).1, ((h3 q hq).1 y hy).2⟩,
          by have := (h3 q hq).2; simp only [List.length_cons]; omega⟩
    · have e : Bd_dec (x :: t) = (x :: (Bd_dec t).1, (Bd_dec t).2) := by
        simp [Bd_dec, hx]
      rw [e]
      refine ⟨fun y hy => ?_, by simp only [List.length_cons]; omega, fun q hq => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨List.mem_cons_self .., by simpa using hx⟩
        · exact ⟨List.mem_cons_of_mem _ (h1 y hy).1, (h1 y hy).2⟩
      · exact ⟨fun y hy => ⟨List.mem_cons_of_mem _ ((h3 q hq).1 y hy).1, ((h3 q hq).1 y hy).2⟩,
          by have := (h3 q hq).2; simp only [List.length_cons]; omega⟩

/-- `‖Π f(x)‖ ≤ R^{len}` when every factor has norm `≤ R`. -/
private lemma Bd_prod_norm {ι α : Type*} [Fintype ι] [DecidableEq ι] (l : List α)
    (f : α → Matrix ι ι ℂ) (R : ℝ) (hR : 1 ≤ R) (h : ∀ x ∈ l, opNorm (f x) ≤ R) :
    opNorm ((l.map f).prod) ≤ R ^ l.length := by
  induction l with
  | nil => simpa using Bd_opNorm_one
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine (opNorm_mul_le _ _).trans ?_
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    rw [pow_succ']
    exact mul_le_mul h1 h2 (Bd_opNorm_nonneg _) (by linarith)

/-- `‖Π f(x)‖ ≤ R^{len} Q^{#Λ̃}` when letters `Λ̃` have norm `≤ Q` and the others `≤ R`. -/
private lemma Bd_prod_normL {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List LoopLetter)
    (f : LoopLetter → Matrix ι ι ℂ) (R Q : ℝ) (hR : 1 ≤ R) (hQ : 0 ≤ Q)
    (h : ∀ x ∈ l, opNorm (f x) ≤ if Bd_isL x then Q else R) :
    opNorm ((l.map f).prod) ≤ R ^ l.length * Q ^ (l.countP Bd_isL) := by
  induction l with
  | nil => simpa using Bd_opNorm_one
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.countP_cons]
    refine (opNorm_mul_le _ _).trans ?_
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    have hRp : 0 ≤ R ^ t.length * Q ^ (t.countP Bd_isL) := by positivity
    by_cases hx : Bd_isL x = true
    · simp only [hx, ite_true] at h1 ⊢
      calc opNorm (f x) * opNorm ((t.map f).prod) ≤ Q * (R ^ t.length * Q ^ (t.countP Bd_isL)) :=
            mul_le_mul h1 h2 (Bd_opNorm_nonneg _) hQ
        _ ≤ R ^ (t.length + 1) * Q ^ (t.countP Bd_isL + 1) := by
            rw [pow_succ, pow_succ]
            have : R ^ t.length ≤ R ^ t.length * R := le_mul_of_one_le_right (by positivity) hR
            have hq : 0 ≤ Q ^ (t.countP Bd_isL) * Q := by positivity
            nlinarith
    · simp only [hx, Bool.false_eq_true, ite_false, add_zero] at h1 ⊢
      calc opNorm (f x) * opNorm ((t.map f).prod) ≤ R * (R ^ t.length * Q ^ (t.countP Bd_isL)) :=
            mul_le_mul h1 h2 (Bd_opNorm_nonneg _) (by linarith)
        _ = R ^ (t.length + 1) * Q ^ (t.countP Bd_isL) := by ring

/-- `‖Π F(x)‖ ≤ Π G(x)` from factorwise bounds. -/
private lemma Bd_list_norm {α : Type*} (l : List α) (F : α → ℂ) (G : α → ℝ)
    (h : ∀ x ∈ l, ‖F x‖ ≤ G x) : ‖(l.map F).prod‖ ≤ (l.map G).prod := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- Cyclicity of the normalized trace. -/
private lemma Bd_ntr_comm {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) :
    ntr (X * Y) = ntr (Y * X) := by
  unfold ntr
  rw [Matrix.trace_mul_comm]

/-! ## Uniform forms of the estimates of Lemma A.4 -/

/-- The pairs `(μ, e)` at size `N` covered by `loop_generic_bound`, apart from the spectral
conditions: `μ ∈ LLClass D N C 1`, `‖A‖ ≤ N^{-δ_A}`, `2 C₀ ‖A‖ ≤ 1/10`, `|c_a| ≤ C₀` and
`|δ| ≤ K⟨Λ²⟩`. -/
private def Bd_Cl (D : ℕ) (δA C₀ K : ℝ) (C : ℕ → ℝ) (N : ℕ) :
    Set (Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N) :=
  {x | LLClass D N C 1 x.1 ∧ opNorm x.2.A ≤ (N : ℝ) ^ (-δA) ∧ 2 * C₀ * opNorm x.2.A ≤ 1 / 10 ∧
    (∀ a, |x.2.c a| ≤ C₀) ∧ |x.2.δ| ≤ K * avgSq (lam D N x.2.A)}

/-- The spectral conditions of Lemma A.4 [lemma_necessary_estimates] at the slot `a`:
`z_a ∈ 𝐃(τ)`, `Im z_a > 0` and `N Im z_a Im m_a ≥ c₀`. -/
private def Bd_zc (D : ℕ) (τ c₀ : ℝ) (N : ℕ) (e : LoopEnv D N) (a : Fin 2) : Prop :=
  e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
    c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im

/-- `η = min(Im z₀, Im z₁)`. -/
private def Bd_eta {D N : ℕ} (e : LoopEnv D N) : ℝ := min (e.z 0).im (e.z 1).im

private lemma Bd_lam_zero (D N : ℕ) : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
  ext p q
  simp [lam]

private lemma Bd_opNorm_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (0 : Matrix ι ι ℂ) = 0 := by
  unfold opNorm
  simp

/-- From sequences to uniform statements over `Bd_Cl`, by `uniform_of_seq` and `llClass_pad`. -/
private lemma Bd_unif (D : ℕ) (δA C₀ K : ℝ) (C : ℕ → ℝ) (hC₀ : 0 ≤ C₀)
    (good : ∀ N, Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N → Prop)
    (hseq : ∀ x : ∀ N, Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N,
      (∀ N, x N ∈ Bd_Cl D δA C₀ K C N) → ∀ᶠ N in atTop, good N (x N)) :
    ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N, good N x := by
  obtain ⟨N₀, hN₀⟩ := uniform_of_seq (Bd_Cl D δA C₀ K C) (fun N x => ¬ good N x)
    (fun N₁ hN₁ ⟨x₁, hx₁⟩ N => by
      obtain ⟨μ, hμ⟩ := llClass_pad D N₁ hN₁ C 1 x₁.1 hx₁.1 N
      refine ⟨(μ, ⟨0, 0, 0, fun _ => false, 0⟩), hμ, ?_, ?_, ?_, ?_⟩
      · simp only [Bd_opNorm_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · simp [Bd_opNorm_zero]
      · intro a
        simpa using hC₀
      · simp [Bd_lam_zero, avgSq, ntr])
    (fun x hx => by
      obtain ⟨N₀, h⟩ := Filter.eventually_atTop.mp (hseq x hx)
      exact ⟨N₀, fun N hN hb => hb (h N hN)⟩)
  exact Filter.eventually_atTop.mpr ⟨N₀, fun N hN x hx => not_not.mp (hN₀ N hN x hx)⟩

/-- (A.53) [entprodG] uniformly over `Bd_Cl`, for slots `σ i` of the factors. -/
private lemma Bd_ent_unif (D : ℕ) (hD : 1 ≤ D) (p : ℕ) (hp : 1 ≤ p) (σ : Fin p → Fin 2)
    (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀)
    (C : ℕ → ℝ) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
        x.1 {h | (N : ℝ) ^ τ'' *
              bndA4 (fun i => (mSol ((x.2.c (σ i) : ℂ) • lam D N x.2.A) (x.2.z (σ i))).im)
                (fun i => (x.2.z (σ i)).im) p <
            ‖ntr (resProd (fun i => res (Matrix.of h + (x.2.c (σ i) : ℂ) • lam D N x.2.A)
              (x.2.z (σ i))) s B)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ'' hτ'' D' hD'
  refine Bd_unif D δA C₀ K C (by linarith) _ fun x hx => ?_
  obtain ⟨N₀, hN₀⟩ := entprodG_local D p hp δA τ c₀ C₀ hτ hc₀ hC₀ C (fun _ => 1)
    (fun N => (x N).1) (fun N => (x N).2.A)
    ⟨hD, hδA, fun _ => ⟨zero_le_one, le_rfl⟩, fun N => (hx N).1, fun N => (hx N).2.1⟩
    (fun N => (hx N).2.2.1) (fun N i => (x N).2.c (σ i)) (fun N i => (hx N).2.2.2.1 (σ i))
    (fun N => {z | (∀ a, Bd_zc D τ c₀ N (x N).2 a) ∧ z = fun i => (x N).2.z (σ i)})
    (fun N z hz i => by
      obtain ⟨h1, rfl⟩ := hz
      exact h1 (σ i)) τ'' hτ'' D' hD'
  exact Filter.eventually_atTop.mpr ⟨N₀, fun N hN hz s B hB =>
    (hN₀ N hN _ ⟨hz, rfl⟩ s B hB).1⟩

/-- For `N ≥ C₀^{2/δ_A}`, `|c| a ≤ C₀ N^{-δ_A} ≤ N^{-δ_A/2}`. -/
private lemma Bd_csmall (δA C₀ c a : ℝ) (hδA : 0 < δA) (hC₀ : 1 ≤ C₀) (hc : |c| ≤ C₀)
    (N : ℕ) (hN : C₀ ^ (2 / δA) ≤ (N : ℝ)) (ha0 : 0 ≤ a) (ha : a ≤ (N : ℝ) ^ (-δA)) :
    |c| * a ≤ (N : ℝ) ^ (-(δA / 2)) := by
  have hC0 : 0 < C₀ := by linarith
  have hCp : 0 < C₀ ^ (2 / δA) := Real.rpow_pos_of_pos hC0 _
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hCp hN
  have h1 : C₀ ≤ (N : ℝ) ^ (δA / 2) := by
    calc C₀ = (C₀ ^ (2 / δA)) ^ (δA / 2) := by
          rw [← Real.rpow_mul hC0.le]; field_simp; simp
      _ ≤ (N : ℝ) ^ (δA / 2) := Real.rpow_le_rpow hCp.le hN (by positivity)
  have h2 : (N : ℝ) ^ (-δA) = (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(δA / 2)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have h3 : (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (δA / 2) = 1 := by
    rw [← Real.rpow_add hNpos]; simp
  have h4 : 0 < (N : ℝ) ^ (-(δA / 2)) := Real.rpow_pos_of_pos hNpos _
  have h5 : C₀ * (N : ℝ) ^ (-(δA / 2)) ≤ 1 := by
    calc C₀ * (N : ℝ) ^ (-(δA / 2)) ≤ (N : ℝ) ^ (δA / 2) * (N : ℝ) ^ (-(δA / 2)) :=
          mul_le_mul_of_nonneg_right h1 h4.le
      _ = 1 := by rw [mul_comm]; exact h3
  calc |c| * a ≤ C₀ * (N : ℝ) ^ (-δA) := mul_le_mul hc ha ha0 hC0.le
    _ = (C₀ * (N : ℝ) ^ (-(δA / 2))) * (N : ℝ) ^ (-(δA / 2)) := by rw [h2]; ring
    _ ≤ 1 * (N : ℝ) ^ (-(δA / 2)) := mul_le_mul_of_nonneg_right h5 h4.le
    _ = _ := one_mul _

/-- The parameter of the slot `a` of `e`: `z_a`, or `z̄_a` when the flag is set. -/
private lemma Bd_zs_dom {D N : ℕ} (e : LoopEnv D N) (τ : ℝ) (a : Fin 2) (h : e.z a ∈ specDom τ N) :
    (if e.s a then star (e.z a) else e.z a) ∈ specDom τ N ∧
      |(if e.s a then star (e.z a) else e.z a).im| = |(e.z a).im| := by
  by_cases hs : e.s a
  · simp only [hs, ite_true]
    refine ⟨⟨by simpa using h.1, by simpa using h.2⟩, by simp⟩
  · simp only [hs, Bool.false_eq_true, ite_false]
    exact ⟨h, trivial⟩

/-- (2.23) [eq:aver_local] for the light weights `⟨(𝒢_a - 𝔐_a) B⟩`, `‖B‖ ≤ 1`, uniformly. -/
private lemma Bd_weight (D : ℕ) (hD : 1 ≤ D) (δA τ C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop,
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N) →
      ∀ (a : Fin 2) (B : Matrix (Idx D N) (Idx D N) ℂ), opNorm B ≤ 1 →
        ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
          ∀ h, h ∉ bad → ‖ntr ((e.G h a - e.M a) * B)‖ ≤
            (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |(e.z a).im|)) := by
  intro τ'' hτ'' D' hD'
  obtain ⟨N₀, hN₀⟩ := aver_local D hD (δA / 2) τ (by linarith) hτ C τ'' hτ'' D' hD'
  refine Filter.eventually_atTop.mpr
    ⟨max N₀ ⌈C₀ ^ (2 / δA)⌉₊, fun N hN μ hμ e hA hc hz a B hB => ?_⟩
  have hN1 : C₀ ^ (2 / δA) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hsmall : opNorm ((e.c a : ℂ) • e.A) ≤ (N : ℝ) ^ (-(δA / 2)) := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact Bd_csmall δA C₀ (e.c a) _ hδA hC₀ (hc a) N hN1 (Bd_opNorm_nonneg _) hA
  refine ⟨_, hN₀ N (le_trans (le_max_left _ _) hN) 1 zero_le_one le_rfl μ hμ _ hsmall B hB,
    fun h hh => ?_⟩
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hh
  obtain ⟨hzd, hzi⟩ := Bd_zs_dom e τ a (hz a)
  have := hh _ hzd
  rw [← lam_smul, hzi] at this
  exact this

/-! ## Deterministic facts on the slots and on words -/

/-- `c_a Λ` is Hermitian with `‖c_a Λ‖ ≤ 1/10` on `Bd_Cl`. -/
private lemma Bd_slot_lam {D N : ℕ} {δA C₀ K : ℝ} {C : ℕ → ℝ}
    {x : Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N} (hx : x ∈ Bd_Cl D δA C₀ K C N)
    (a : Fin 2) :
    ((x.2.c a : ℂ) • lam D N x.2.A).IsHermitian ∧
      opNorm ((x.2.c a : ℂ) • lam D N x.2.A) ≤ 1 / 10 := by
  refine ⟨Bd_lamc_herm D N _ _, (Bd_lamc_norm D N _ _).trans ?_⟩
  have h1 := hx.2.2.2.1 a
  have h2 := hx.2.2.1
  have h0 := Bd_opNorm_nonneg x.2.A
  nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * opNorm x.2.A)]

/-- The deterministic bounds on `Bd_Cl` under the spectral conditions: `‖A‖ ≤ 1`, `‖𝔐_a‖ ≤ 5/4`,
`‖Λ̃‖ ≤ (2 + 4|K|) ‖A‖`, `0 < η ≤ Im z_a` and `Im m_a ≤ 1`. -/
private lemma Bd_facts {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) {δA C₀ K τ c₀ : ℝ} {C : ℕ → ℝ}
    (hC₀ : 1 ≤ C₀) {x : Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N}
    (hx : x ∈ Bd_Cl D δA C₀ K C N) (hz : ∀ a, Bd_zc D τ c₀ N x.2 a) :
    opNorm x.2.A ≤ 1 ∧ (∀ a, opNorm (x.2.M a) ≤ 5 / 4) ∧
      opNorm x.2.Lt ≤ (2 + 4 * |K|) * opNorm x.2.A ∧ 0 < Bd_eta x.2 ∧
      (∀ a, Bd_eta x.2 ≤ (x.2.z a).im) ∧
      (∀ a, (mSol ((x.2.c a : ℂ) • lam D N x.2.A) (x.2.z a)).im ≤ 1) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hA0 := Bd_opNorm_nonneg x.2.A
  have hA1 : opNorm x.2.A ≤ 1 := by nlinarith [hx.2.2.1]
  refine ⟨hA1, fun a => ?_, ?_, lt_min (hz 0).2.1 (hz 1).2.1, fun a => ?_, fun a => ?_⟩
  · obtain ⟨hh, hn⟩ := Bd_slot_lam hx a
    refine Bd_MExt_norm _ hh hn _ ?_
    have := (hz a).2.1
    by_cases hs : x.2.s a
    · simp only [hs, ite_true, Complex.star_def, Complex.conj_im]
      linarith
    · simp only [hs, Bool.false_eq_true, ite_false]
      linarith
  · unfold LoopEnv.Lt
    rw [sub_eq_add_neg, ← neg_smul]
    refine (opNorm_add_le _ _).trans ?_
    rw [opNorm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have h1 := opNorm_lam_le D N x.2.A
    have h2 := Bd_opNorm_one (ι := Idx D N)
    have h3 := hx.2.2.2.2
    have h4 := Bd_avgSq_le (lam D N x.2.A)
    have h5 := Bd_avgSq_nonneg _ (lam_isHermitian D N x.2.A)
    have h6 := Bd_opNorm_nonneg (lam D N x.2.A)
    have hK : K * avgSq (lam D N x.2.A) ≤ |K| * avgSq (lam D N x.2.A) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) h5
    have hl2 : opNorm (lam D N x.2.A) ^ 2 ≤ 4 * opNorm x.2.A := by nlinarith
    have hδ : |x.2.δ| ≤ 4 * |K| * opNorm x.2.A := by
      have := mul_le_mul_of_nonneg_left (h4.trans hl2) (abs_nonneg K)
      nlinarith
    have : |x.2.δ| * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ |x.2.δ| :=
      mul_le_of_le_one_right (abs_nonneg _) h2
    nlinarith
  · fin_cases a
    · exact min_le_left _ _
    · exact min_le_right _ _
  · obtain ⟨hh, hn⟩ := Bd_slot_lam hx a
    exact Bd_im_mSol_le _ hh hn _ (hz a).2.1

/-- For a Hermitian array, `𝒢_a` is `G_a` or `G_a^*` according to the flag. -/
private lemma Bd_G_eq {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    e.G h = fun a => if e.s a then (res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))ᴴ
      else res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a) := by
  funext a
  unfold LoopEnv.G
  by_cases hs : e.s a
  · simp only [hs, ite_true]
    exact Bd_res_star _ (hh.add (Bd_lamc_herm D N _ _)) _
  · simp [hs]

private lemma Bd_let_L {ι : Type*} (G M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (x : LoopLetter) (hx : Bd_isL x = true) : Bd_let G M E L x = L := by
  cases x <;> simp_all [Bd_isL, Bd_let]

/-- A word with a letter satisfying `P` splits at the first such letter. -/
private lemma Bd_split (P : LoopLetter → Bool) (w : List LoopLetter) (h : 0 < w.countP P) :
    ∃ a x b, w = a ++ x :: b ∧ a.countP P = 0 ∧ P x = true := by
  induction w with
  | nil => simp at h
  | cons y t ih =>
    by_cases hy : P y = true
    · exact ⟨[], y, t, rfl, rfl, hy⟩
    · have ht : 0 < t.countP P := by simpa [List.countP_cons, hy] using h
      obtain ⟨a, x, b, rfl, ha, hx⟩ := ih ht
      exact ⟨y :: a, x, b, rfl, by simp [hy, ha], hx⟩

/-- The slots and flags of the resolvent letters of a word. -/
private def Bd_wv (s : Fin 2 → Bool) (v : List LoopLetter) :
    Fin (Bd_dec v).2.length → Fin 2 × Bool :=
  fun j => (((Bd_dec v).2.get j).1, s ((Bd_dec v).2.get j).1)

/-- The deterministic factors of a word between its resolvent letters. -/
private def Bd_Bv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (v : List LoopLetter) :
    Fin ((Bd_dec v).2.length + 1) → Matrix ι ι ℂ :=
  Fin.cons (((Bd_dec v).1.map (Bd_let 0 M E L)).prod)
    fun j => (((Bd_dec v).2.get j).2.map (Bd_let 0 M E L)).prod

/-- The matrix of a word as a product `B₀ G B₁ ⋯ G B_l` of Lemma A.4
[lemma_necessary_estimates]. -/
private lemma Bd_mat_resWord {ι : Type*} [Fintype ι] [DecidableEq ι] (Gr : Fin 2 → Matrix ι ι ℂ)
    (s : Fin 2 → Bool) (M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v : List LoopLetter) :
    (v.map (Bd_let (fun a => if s a then (Gr a)ᴴ else Gr a) M E L)).prod =
      resWord Gr (Bd_wv s v) (Bd_Bv M E L v) := by
  set G : Fin 2 → Matrix ι ι ℂ := fun a => if s a then (Gr a)ᴴ else Gr a with hG
  have hseg : ∀ q : List LoopLetter, (∀ x ∈ q, x ∈ v ∧ Bd_isRes x = false) →
      (q.map (Bd_let G M E L)).prod = (q.map (Bd_let 0 M E L)).prod := by
    intro q hq
    congr 1
    exact List.map_congr_left fun x hx => Bd_let_nonres G 0 M E L x (hq x hx).2
  rw [Bd_dec_prod, hseg _ (Bd_dec_mem v).1]
  unfold resWord Bd_Bv Bd_wv
  rw [Fin.cons_zero]
  congr 1
  conv_lhs => rw [← List.ofFn_get (Bd_dec v).2, List.map_ofFn]
  congr 2
  funext j
  simp only [Function.comp, Fin.cons_succ]
  rw [hseg _ ((Bd_dec_mem v).2.2 _ (List.get_mem _ _)).1]

/-- A segment of deterministic letters `𝔐_a`, `E_x` has norm `≤ (5/4)^{len v}`. -/
private lemma Bd_seg_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (hM : ∀ a, opNorm (M a) ≤ 5 / 4)
    (hE : ∀ y, opNorm (E y) ≤ 1) (v q : List LoopLetter) (hv : v.countP Bd_isL = 0)
    (hq : ∀ x ∈ q, x ∈ v ∧ Bd_isRes x = false) (hlen : q.length ≤ v.length) :
    opNorm ((q.map (Bd_let 0 M E L)).prod) ≤ (5 / 4) ^ v.length := by
  refine (Bd_prod_norm q _ (5 / 4) (by norm_num) fun x hx => ?_).trans
    (pow_le_pow_right₀ (by norm_num) hlen)
  obtain ⟨hxv, hxr⟩ := hq x hx
  have hxl : Bd_isL x = false := by simpa using List.countP_eq_zero.mp hv x hxv
  cases x with
  | res a => simp [Bd_isRes] at hxr
  | det a => exact hM a
  | proj y => exact (hE y).trans (by norm_num)
  | lamt o => simp [Bd_isL] at hxl

private lemma Bd_Bv_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (hM : ∀ a, opNorm (M a) ≤ 5 / 4)
    (hE : ∀ y, opNorm (E y) ≤ 1) (v : List LoopLetter) (hv : v.countP Bd_isL = 0)
    (j : Fin ((Bd_dec v).2.length + 1)) : opNorm (Bd_Bv M E L v j) ≤ (5 / 4) ^ v.length := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Bd_Bv, Fin.cons_zero]
    exact Bd_seg_norm M E L hM hE v _ hv (Bd_dec_mem v).1 (Bd_dec_mem v).2.1
  · simp only [Bd_Bv, Fin.cons_succ]
    exact Bd_seg_norm M E L hM hE v _ hv ((Bd_dec_mem v).2.2 _ (List.get_mem _ _)).1
      ((Bd_dec_mem v).2.2 _ (List.get_mem _ _)).2

private lemma Bd_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (X : Matrix ι ι ℂ) :
    ntr (c • X) = c * ntr X := by
  unfold ntr
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

private lemma Bd_ofFn_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (X Y : Fin p → Matrix ι ι ℂ) (r : ℂ) :
    (List.ofFn fun i => X i * (r • Y i)).prod = r ^ p • (List.ofFn fun i => X i * Y i).prod := by
  induction p with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      ih (fun i => X i.succ) (fun i => Y i.succ)]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, pow_succ, mul_comm]

/-- The constant of the bound of one loop: `(5/4)^{L²} · 4D · (2 + 4|K|)²`. -/
private def Bd_cw (D : ℕ) (K : ℝ) (L : ℕ) : ℝ := (5 / 4) ^ (L * L) * (4 * D) * (2 + 4 * |K|) ^ 2

private lemma Bd_cw_ge (D : ℕ) (hD : 1 ≤ D) (K : ℝ) (L : ℕ) :
    (5 / 4 : ℝ) ^ (L * L) ≤ Bd_cw D K L ∧ 4 * (D : ℝ) ≤ Bd_cw D K L ∧
      (5 / 4 : ℝ) ^ L * (2 + 4 * |K|) ^ 2 ≤ Bd_cw D K L ∧ 1 ≤ Bd_cw D K L := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h1 : (1 : ℝ) ≤ (5 / 4) ^ (L * L) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (2 + 4 * |K|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg K])
  have h3 : (5 / 4 : ℝ) ^ L ≤ (5 / 4) ^ (L * L) := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · exact pow_le_pow_right₀ (by norm_num) (Nat.le_mul_self L)
  unfold Bd_cw
  set a : ℝ := (5 / 4) ^ (L * L)
  set c : ℝ := (2 + 4 * |K|) ^ 2
  have hb : (4 : ℝ) ≤ 4 * D := by linarith
  have hbc : 1 ≤ 4 * (D : ℝ) * c := by nlinarith
  have hac : 1 ≤ a * c := one_le_mul_of_one_le_of_one_le h1 h2
  have e1 : a * (4 * D) * c = a * (4 * D * c) := by ring
  have e2 : a * (4 * D) * c = 4 * D * (a * c) := by ring
  have e3 : a * (4 * D) * c = (a * c) * (4 * D) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact le_mul_of_one_le_right (by positivity) hbc
  · rw [e2]
    exact le_mul_of_one_le_right (by positivity) hac
  · rw [e3]
    have : (5 / 4 : ℝ) ^ L * c ≤ a * c := mul_le_mul_of_nonneg_right h3 (by positivity)
    exact this.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  · rw [e1]
    exact one_le_mul_of_one_le_of_one_le h1 hbc

private lemma Bd_cw_mono (D : ℕ) (K : ℝ) {L L' : ℕ} (h : L ≤ L') : Bd_cw D K L ≤ Bd_cw D K L' := by
  unfold Bd_cw
  gcongr
  norm_num

private lemma Bd_cyc0 {ι : Type*} [Fintype ι] (P G S : Matrix ι ι ℂ) :
    ntr (P * (G * S)) = ntr (G * (S * P)) := by
  rw [Bd_ntr_comm P (G * S), Matrix.mul_assoc]

private lemma Bd_cyc1 {ι : Type*} [Fintype ι] (P S L : Matrix ι ι ℂ) :
    ntr (P * (L * S)) = ntr (S * P * L) := by
  rw [Bd_ntr_comm P (L * S), Matrix.mul_assoc, Bd_ntr_comm L (S * P)]

private lemma Bd_cyc2 {ι : Type*} [Fintype ι] (P R S L : Matrix ι ι ℂ) :
    ntr (P * (L * (R * (L * S)))) = ntr (S * P * L * R * L) := by
  rw [show P * (L * (R * (L * S))) = (P * L * R * L) * S by simp only [Matrix.mul_assoc],
    Bd_ntr_comm (P * L * R * L) S]
  simp only [Matrix.mul_assoc]

private lemma Bd_mat_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (a b : List LoopLetter) (g : LoopLetter) :
    ntr (((a ++ g :: b).map (Bd_let G M E L)).prod) =
      ntr (((g :: (b ++ a)).map (Bd_let G M E L)).prod) := by
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  exact Bd_cyc0 _ _ _

private lemma Bd_mat_one {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (a b : List LoopLetter) (y : LoopLetter)
    (hy : Bd_isL y = true) :
    ntr (((a ++ y :: b).map (Bd_let G M E L)).prod) =
      ntr (((b ++ a).map (Bd_let G M E L)).prod * L) := by
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    Bd_let_L G M E L y hy]
  exact Bd_cyc1 _ _ _

private lemma Bd_mat_two {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (a c d : List LoopLetter) (y₁ y₂ : LoopLetter)
    (hy₁ : Bd_isL y₁ = true) (hy₂ : Bd_isL y₂ = true) :
    ntr (((a ++ y₁ :: (c ++ y₂ :: d)).map (Bd_let G M E L)).prod) =
      ntr (((d ++ a).map (Bd_let G M E L)).prod * L * (c.map (Bd_let G M E L)).prod * L) := by
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    Bd_let_L G M E L y₁ hy₁, Bd_let_L G M E L y₂ hy₂]
  exact Bd_cyc2 _ _ _ _

private lemma Bd_isL_notRes (x : LoopLetter) (hx : Bd_isL x = true) : Bd_isRes x = false := by
  cases x <;> simp_all [Bd_isL, Bd_isRes]

/-! ## The value of an expression from bounds on its factors -/

private lemma Bd_opNorm_E {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (x : ℕ) :
    opNorm (e.E ι x) ≤ 1 := by
  unfold LoopEnv.E
  split_ifs
  · exact Bd_opNorm_Ea D N _
  · exact Bd_opNorm_one

/-- `‖𝒢_a‖ ≤ |Im z_a|⁻¹` for a Hermitian array. -/
private lemma Bd_G_norm {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (a : Fin 2) (hz : (e.z a).im ≠ 0) :
    opNorm (e.G h a) ≤ |(e.z a).im|⁻¹ := by
  have hX := hh.add (Bd_lamc_herm D N e.A (e.c a))
  unfold LoopEnv.G
  by_cases hs : e.s a
  · simp only [hs, ite_true]
    have := Bd_opNorm_res _ hX (star (e.z a)) (by simpa using hz)
    simpa using this
  · simp only [hs, Bool.false_eq_true, ite_false]
    exact Bd_opNorm_res _ hX _ hz

private lemma Bd_opNorm_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) :
    opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  rw [sub_eq_add_neg, show -Y = (-1 : ℂ) • Y by simp]
  refine (opNorm_add_le _ _).trans ?_
  rw [opNorm_smul]
  simp



section Tools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma Tay_opNorm_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

private lemma Tay_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

private lemma Tay_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  have h3 : ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := by
    simp
  rw [h3] at h2
  exact h2.trans h

/-- `∑ᵢⱼ |Aᵢⱼ|²`. -/
private def Tay_S (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq ι] in
private lemma Tay_S_nonneg (A : Matrix ι ι ℂ) : 0 ≤ Tay_S A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq ι] in
private lemma Tay_ntr_mul_le [Nonempty ι] (X Y : Matrix ι ι ℂ) :
    ‖ntr (X * Y)‖ ≤ (Fintype.card ι : ℝ)⁻¹ * (Real.sqrt (Tay_S X) * Real.sqrt (Tay_S Y)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ‖(X * Y).trace‖ ≤ ∑ p : ι × ι, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    rw [Matrix.trace]
    calc ‖∑ i, (X * Y).diag i‖ ≤ ∑ i, ‖(X * Y).diag i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Matrix.diag, Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
      _ = _ := by rw [Fintype.sum_prod_type]
  refine h1.trans ?_
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖Y p.2 p.1‖)
  have e1 : ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2 = Tay_S X := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = Tay_S Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  exact h2

private lemma Tay_S_mul_le (U B : Matrix ι ι ℂ) : Tay_S (U * B) ≤ opNorm U ^ 2 * Tay_S B := by
  unfold Tay_S
  rw [Finset.sum_comm (f := fun i j => ‖(U * B) i j‖ ^ 2),
    Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := Matrix.l2_opNorm_mulVec U ((EuclideanSpace.equiv ι ℂ).symm (fun i => B i j))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  have e : ∀ i, ((EuclideanSpace.equiv ι ℂ).symm (U *ᵥ ((EuclideanSpace.equiv ι ℂ).symm
      (fun i => B i j)).ofLp)).ofLp i = (U * B) i j := fun i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [e] at h2
  simpa [Tay_opNorm_eq] using h2

omit [DecidableEq ι] in
/-- For Hermitian `Λ`, `∑ |Λᵢⱼ|² = |ι| ⟨Λ²⟩`. -/
private lemma Tay_S_herm [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    Tay_S Λ = Fintype.card ι * avgSq Λ := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  have e : (Λ * Λ).trace = ((Tay_S Λ : ℝ) : ℂ) := by
    rw [Matrix.trace, Tay_S]
    simp only [Matrix.diag, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Λ j i = star (Λ i j) := by rw [← hΛ.apply i j, star_star]
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  unfold avgSq ntr
  rw [e]
  have : ((Fintype.card ι : ℂ)⁻¹ * ((Tay_S Λ : ℝ) : ℂ)).re = (Fintype.card ι : ℝ)⁻¹ * Tay_S Λ := by
    rw [show ((Fintype.card ι : ℂ)⁻¹ : ℂ) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this]
  field_simp

/-- The key bound: `|⟨U Λ V Λ⟩| ≤ ‖U‖ ‖V‖ ⟨Λ²⟩`. -/
private lemma Tay_BL [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (U V : Matrix ι ι ℂ) :
    ‖ntr (U * Λ * V * Λ)‖ ≤ opNorm U * opNorm V * avgSq Λ := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h1 := Tay_ntr_mul_le (U * Λ) (V * Λ)
  have e : U * Λ * (V * Λ) = U * Λ * V * Λ := by simp only [mul_assoc]
  rw [e] at h1
  refine h1.trans ?_
  have a1 := Tay_S_mul_le U Λ
  have a2 := Tay_S_mul_le V Λ
  have b1 : Real.sqrt (Tay_S (U * Λ)) ≤ opNorm U * Real.sqrt (Tay_S Λ) := by
    rw [← Real.sqrt_sq (Tay_op_nonneg U), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt a1
  have b2 : Real.sqrt (Tay_S (V * Λ)) ≤ opNorm V * Real.sqrt (Tay_S Λ) := by
    rw [← Real.sqrt_sq (Tay_op_nonneg V), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt a2
  have hS : Real.sqrt (Tay_S Λ) * Real.sqrt (Tay_S Λ) = Fintype.card ι * avgSq Λ := by
    rw [Real.mul_self_sqrt (Tay_S_nonneg Λ), Tay_S_herm hΛ]
  calc (Fintype.card ι : ℝ)⁻¹ * (Real.sqrt (Tay_S (U * Λ)) * Real.sqrt (Tay_S (V * Λ)))
      ≤ (Fintype.card ι : ℝ)⁻¹ * ((opNorm U * Real.sqrt (Tay_S Λ)) *
          (opNorm V * Real.sqrt (Tay_S Λ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul b1 b2 (Real.sqrt_nonneg _)
          (mul_nonneg (Tay_op_nonneg U) (Real.sqrt_nonneg _))
    _ = opNorm U * opNorm V * ((Fintype.card ι : ℝ)⁻¹ *
          (Real.sqrt (Tay_S Λ) * Real.sqrt (Tay_S Λ))) := by ring
    _ = _ := by rw [hS]; field_simp


private lemma Tay_ntr_one [Nonempty ι] : ntr (1 : Matrix ι ι ℂ) = 1 := by
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  simp [ntr, Matrix.trace_one, this]

end Tools

/-- The diagonal entries of `lam D N A` vanish. -/
private lemma Tay_lam_diag (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (p : Idx D N) :
    lam D N A p p = 0 := by
  have h1 : ¬ ((p.1 : ℕ) = (p.1 : ℕ) + 1) := by omega
  have h2 : ¬ (3 ≤ D ∧ (p.1 : ℕ) + 1 = D ∧ (p.1 : ℕ) = 0) := by
    have := p.1.isLt
    omega
  simp [lam, fwd, h2]

/-- Every diagonal block of `lam D N A` is traceless: `⟨E_a Λ⟩ = 0`. -/
private lemma Tay_lam_blockTraceless (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (a : Fin D) :
    ntr (Ea D N a * lam D N A) = 0 := by
  unfold ntr Ea
  rw [Matrix.trace]
  simp [Matrix.diag, Matrix.diagonal_mul, Tay_lam_diag]

/-! ## The class (5.33): counting -/

private lemma Bd_countP_contains_le (L : List (List LoopLetter)) (x : LoopLetter) :
    L.countP (fun w => w.contains x) ≤ (L.map (List.count x)).sum := by
  induction L with
  | nil => simp
  | cons v t ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons]
    by_cases hv : v.contains x = true
    · have : 0 < v.count x := List.count_pos_iff.mpr (List.contains_iff_mem.mp hv)
      simp only [hv, ite_true]
      omega
    · simp only [hv, Bool.false_eq_true, ite_false]
      omega

/-- The term of `k_o` of one loop is at most its number of resolvents. -/
private lemma Bd_kk_term_le (w : List LoopLetter) (k : ℕ) (P : LoopLetter → Bool) :
    (((w.rotate k).drop 1).reverse.takeWhile P).countP Bd_isRes ≤ w.countP Bd_isRes := by
  refine ((List.takeWhile_sublist P).countP_le).trans ?_
  rw [List.countP_reverse]
  refine ((List.drop_sublist 1 _).countP_le).trans ?_
  rw [(List.rotate_perm w k).countP_eq]

private lemma Bd_sum_zero (L : List (List LoopLetter)) (x : LoopLetter)
    (F : List LoopLetter → ℕ) (hF : ∀ w, F w ≤ if w.contains x then w.countP Bd_isRes else 0)
    (hsum : (L.map (List.count x)).sum ≤ 1)
    (hw : ∃ w ∈ L, w.contains x = true ∧ w.countP Bd_isRes = 0) : (L.map F).sum = 0 := by
  induction L with
  | nil => simp
  | cons v t ih =>
    rw [List.map_cons, List.sum_cons] at hsum ⊢
    obtain ⟨w, hwL, hwx, hwr⟩ := hw
    rcases List.mem_cons.mp hwL with rfl | hwt
    · have hc : 0 < w.count x := List.count_pos_iff.mpr (List.contains_iff_mem.mp hwx)
      have ht0 : (t.map (List.count x)).sum = 0 := by omega
      have hF0 : ∀ u ∈ t, F u = 0 := by
        intro u hu
        have hcu : u.count x = 0 := by
          have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count x) hu)
          omega
        have hnu : u.contains x = false := by
          by_contra hcon
          have := List.count_pos_iff.mpr (by simpa using hcon)
          omega
        have := hF u
        simp only [hnu, Bool.false_eq_true, ite_false] at this
        omega
      have hFw := hF w
      simp only [hwx, ite_true, hwr] at hFw
      rw [List.sum_eq_zero (fun y hy => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
        exact hF0 u hu)]
      omega
    · have hcw : 0 < w.count x := List.count_pos_iff.mpr (List.contains_iff_mem.mp hwx)
      have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count x) hwt)
      have hnv : v.contains x = false := by
        by_contra hcon
        have := List.count_pos_iff.mpr (by simpa using hcon)
        omega
      have hFv := hF v
      simp only [hnv, Bool.false_eq_true, ite_false] at hFv
      have := ih (by omega) ⟨w, hwt, hwx, hwr⟩
      omega

/-- If a loop without resolvent contains `Λ̃_o`, then `k_o = 0`. -/
private lemma Bd_kk_zero (T : LoopExpr) (o : Fin 2)
    (hsum : (T.loops.map (List.count (.lamt o))).sum ≤ 1)
    (hw : ∃ w ∈ T.loops, w.contains (.lamt o) = true ∧ w.countP Bd_isRes = 0) : T.kk o = 0 := by
  unfold LoopExpr.kk
  refine Bd_sum_zero T.loops (.lamt o) _ (fun w => ?_) hsum hw
  split_ifs
  · exact Bd_kk_term_le w _ _
  · exact le_rfl

private lemma Bd_countP_or (L : List (List LoopLetter)) (p q r : List LoopLetter → Bool)
    (h : ∀ w ∈ L, p w = true → q w = true ∨ r w = true) :
    L.countP p ≤ L.countP q + L.countP r := by
  induction L with
  | nil => simp
  | cons v t ih =>
    simp only [List.countP_cons]
    have ih' := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    have hv := h v (List.mem_cons_self ..)
    by_cases hp : p v = true
    · rcases hv hp with hq | hr
      · simp only [hp, hq, ite_true]
        split_ifs <;> omega
      · simp only [hp, hr, ite_true]
        split_ifs <;> omega
    · simp only [hp, Bool.false_eq_true, ite_false]
      split_ifs <;> omega

/-- The counting facts for an expression of the class (5.33)
[definition_class_of_expression_loop]: each loop has at most two `Λ̃`, there are two in all, and
the number of loops without resolvent is at most `1(k₁ = 0) + 1(k₂ = 0)`. -/
private lemma Bd_wf_facts (T : LoopExpr) (hT : T.wf = true) :
    (∀ w ∈ T.loops, w.countP Bd_isL ≤ 2) ∧ (T.loops.map (List.countP Bd_isL)).sum = 2 ∧
      T.loops.countP (fun w => decide (w.countP Bd_isRes = 0)) ≤
        (if T.kk 0 = 0 then 1 else 0) + (if T.kk 1 = 0 then 1 else 0) := by
  simp only [LoopExpr.wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨h0, h1⟩, h3⟩, -⟩, -⟩ := hT
  have hsplit : (T.loops.map (List.countP Bd_isL)).sum =
      (T.loops.map (List.count (.lamt 0))).sum + (T.loops.map (List.count (.lamt 1))).sum := by
    rw [← List.sum_map_add]
    congr 1
    exact List.map_congr_left fun w _ => Bd_isL_count w
  refine ⟨fun w hw => ?_, by rw [hsplit, h0, h1], ?_⟩
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.countP Bd_isL) hw)
    rw [hsplit, h0, h1] at this
    exact this
  · have hor := Bd_countP_or T.loops (fun w => decide (w.countP Bd_isRes = 0))
      (fun w => decide (w.countP Bd_isRes = 0) && w.contains (.lamt 0))
      (fun w => decide (w.countP Bd_isRes = 0) && w.contains (.lamt 1)) (fun w hw hp => by
        have h3w := h3 w hw
        have hr : w.countP Bd_isRes = 0 := by simpa using hp
        simp only [Bool.or_eq_true] at h3w
        rcases h3w with (h | h) | h
        · left; simpa [hr] using List.contains_iff_mem.mp h
        · right; simpa [hr] using List.contains_iff_mem.mp h
        · exfalso
          obtain ⟨x, hx, hxr⟩ := List.any_eq_true.mp h
          have := List.countP_eq_zero.mp hr x hx
          cases x <;> simp_all [Bd_isRes])
    have hZ : ∀ o : Fin 2, (T.loops.map (List.count (.lamt o))).sum = 1 →
        T.loops.countP (fun w => decide (w.countP Bd_isRes = 0) && w.contains (.lamt o)) ≤
          if T.kk o = 0 then 1 else 0 := by
      intro o ho
      have hle : T.loops.countP (fun w => decide (w.countP Bd_isRes = 0) && w.contains (.lamt o))
          ≤ 1 := by
        refine le_trans ?_ (le_of_eq ho)
        refine le_trans ?_ (Bd_countP_contains_le T.loops (.lamt o))
        exact List.countP_mono_left fun w _ h => by simp_all
      split_ifs with hk
      · exact hle
      · by_contra hcon
        have hpos : 0 < T.loops.countP
            (fun w => decide (w.countP Bd_isRes = 0) && w.contains (.lamt o)) := by omega
        obtain ⟨w, hw, hpw⟩ := List.countP_pos_iff.mp hpos
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpw
        exact hk (Bd_kk_zero T o (le_of_eq ho) ⟨w, hw, hpw.2, hpw.1⟩)
    have := hZ 0 h0
    have := hZ 1 h1
    omega

/-! ## Integrability of the values -/

/-- The slot deformation `c_a Λ` is Hermitian. -/
private lemma GS_slot_herm {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) :
    ((e.c a : ℂ) • lam D N e.A).IsHermitian := by
  have := lam_isHermitian D N e.A
  unfold Matrix.IsHermitian at this ⊢
  rw [Matrix.conjTranspose_smul, this]
  simp

/-- The spectral parameter of the slot `a`, `z_a` or `z̄_a`, is not real. -/
private lemma GS_slot_im {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (a : Fin 2) :
    (if e.s a then star (e.z a) else e.z a).im ≠ 0 := by
  split_ifs
  · simpa using (hz a).ne'
  · exact (hz a).ne'

/-- The matrix of a word with one more letter in front. -/
private lemma GS_word_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (x : LoopLetter) (w : List LoopLetter) :
    loopWordMat G M E L (x :: w) = loopWordMat G M E L [x] * loopWordMat G M E L w := by
  simp [loopWordMat]

/-- The value of a light weight `⟨(𝒢_b - 𝔐_b) E_y⟩` at the array `h`. -/
private def GS_wv {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : Fin 2 × ℕ) : ℂ :=
  ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)

/-- On Hermitian arrays, `f` agrees with a continuous function and is bounded. -/
private def GS_nice {D N : ℕ} (f : (Idx D N → Idx D N → ℂ) → ℂ) : Prop :=
  (∃ g : (Idx D N → Idx D N → ℂ) → ℂ, Continuous g ∧
    ∀ h, (Matrix.of h).IsHermitian → f h = g h) ∧
  ∃ B : ℝ, ∀ h, (Matrix.of h).IsHermitian → ‖f h‖ ≤ B

/-- Constants are `GS_nice`. -/
private lemma GS_nice_const {D N : ℕ} (c : ℂ) : GS_nice (D := D) (N := N) fun _ => c :=
  ⟨⟨fun _ => c, continuous_const, fun _ _ => rfl⟩, ‖c‖, fun _ _ => le_rfl⟩

/-- Sums of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_add {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f)
    (hg : GS_nice g) : GS_nice fun h => f h + g h := by
  obtain ⟨⟨f', hf'c, hf'⟩, Bf, hBf⟩ := hf
  obtain ⟨⟨g', hg'c, hg'⟩, Bg, hBg⟩ := hg
  refine ⟨⟨fun h => f' h + g' h, hf'c.add hg'c, fun h hh => by
    beta_reduce; rw [hf' h hh, hg' h hh]⟩,
    Bf + Bg, fun h hh => (norm_add_le _ _).trans (add_le_add (hBf h hh) (hBg h hh))⟩

/-- Products of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_mul {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f)
    (hg : GS_nice g) : GS_nice fun h => f h * g h := by
  obtain ⟨⟨f', hf'c, hf'⟩, Bf, hBf⟩ := hf
  obtain ⟨⟨g', hg'c, hg'⟩, Bg, hBg⟩ := hg
  refine ⟨⟨fun h => f' h * g' h, hf'c.mul hg'c, fun h hh => by
    beta_reduce; rw [hf' h hh, hg' h hh]⟩,
    Bf * Bg, fun h hh => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hBf h hh) (hBg h hh) (norm_nonneg _) ((norm_nonneg _).trans (hBf h hh))

/-- Differences of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_sub {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f)
    (hg : GS_nice g) : GS_nice fun h => f h - g h := by
  have := GS_nice_add hf (GS_nice_mul (GS_nice_const (-1)) hg)
  simpa [sub_eq_add_neg] using this

/-- Finite sums of `GS_nice` functions are `GS_nice`. -/
private lemma GS_nice_sum {D N : ℕ} {κ : Type*} (S : Finset κ)
    {f : κ → (Idx D N → Idx D N → ℂ) → ℂ} (hf : ∀ k ∈ S, GS_nice (f k)) :
    GS_nice fun h => ∑ k ∈ S, f k h := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GS_nice_const (D := D) (N := N) 0
  | insert a S ha ih =>
    simpa [Finset.sum_insert ha] using GS_nice_add (hf a (Finset.mem_insert_self a S))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-- Every entry of the matrix function is `GS_nice`. -/
private def GS_niceM {D N : ℕ}
    (F : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  ∀ k l, GS_nice fun h => F h k l

/-- Products of `GS_niceM` matrix functions are `GS_niceM`. -/
private lemma GS_niceM_mul {D N : ℕ} {F G : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hF : GS_niceM F) (hG : GS_niceM G) : GS_niceM fun h => F h * G h := fun k l => by
  simpa [Matrix.mul_apply] using GS_nice_sum Finset.univ fun m _ => GS_nice_mul (hF k m) (hG m l)

/-- Constant matrices are `GS_niceM`. -/
private lemma GS_niceM_const {D N : ℕ} (A : Matrix (Idx D N) (Idx D N) ℂ) :
    GS_niceM fun _ => A := fun k l => GS_nice_const (A k l)

/-- Normalized traces of `GS_niceM` matrix functions are `GS_nice`. -/
private lemma GS_nice_ntr {D N : ℕ} {F : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hF : GS_niceM F) : GS_nice fun h => ntr (F h) := by
  simpa [ntr, Matrix.trace] using
    GS_nice_mul (GS_nice_const _) (GS_nice_sum Finset.univ fun k _ => hF k k)

/-- An entry is bounded by the operator norm. -/
private lemma GS_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : A i j = ((Matrix.toEuclideanCLM (𝕜 := ℂ) A) (EuclideanSpace.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec_single]
  rw [h3]
  exact (PiLp.norm_apply_le _ i).trans h1

/-- The operator norm of the adjoint. -/
private lemma GS_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- The resolvent of a slot is bounded entrywise by `(Im z_a)⁻¹` on Hermitian arrays and agrees
there with the continuous resolvent of the Hermitian part. -/
private lemma GS_niceM_G {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (a : Fin 2) :
    GS_niceM fun h => e.G h a := by
  intro k l
  refine ⟨⟨fun h => res (Matrix.of (symArr h) + (e.c a : ℂ) • lam D N e.A)
    (if e.s a then star (e.z a) else e.z a) k l,
    (contDiff_res_symArr _ (GS_slot_herm e a) _ (GS_slot_im e hz a) k l 0).continuous,
    fun h hh => by simp only [LoopEnv.G, symArr_of_isHermitian h hh]⟩, (e.z a).im⁻¹,
    fun h hh => ?_⟩
  have hX := hh.add (GS_slot_herm e a)
  refine (GS_entry_le _ k l).trans ?_
  simp only [LoopEnv.G]
  split_ifs
  · rw [show star (e.z a) = starRingEnd ℂ (e.z a) from rfl, res_conj _ hX _ (hz a),
      GS_opNorm_conjTranspose]
    exact opNorm_res_le _ hX _ (hz a)
  · exact opNorm_res_le _ hX _ (hz a)

/-- The matrices of words are `GS_niceM`. -/
private lemma GS_niceM_word {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) :
    ∀ w : List LoopLetter, GS_niceM fun h => loopWordMat (e.G h) e.M (e.E ι) e.Lt w
  | [] => by simpa [loopWordMat] using GS_niceM_const (D := D) (N := N) 1
  | x :: w => by
      have ih := GS_niceM_word e hz ι w
      have hx : GS_niceM fun h => loopWordMat (e.G h) e.M (e.E ι) e.Lt [x] := by
        cases x with
        | res a => simpa [loopWordMat] using GS_niceM_G e hz a
        | det a => simpa [loopWordMat] using GS_niceM_const (e.M a)
        | proj y => simpa [loopWordMat] using GS_niceM_const (e.E ι y)
        | lamt o => simpa [loopWordMat] using GS_niceM_const e.Lt
      simpa [GS_word_cons _ _ _ _ x w] using GS_niceM_mul hx ih

/-- A light weight `⟨(𝒢_b - 𝔐_b) E_y⟩` is `GS_nice`. -/
private lemma GS_nice_wv {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) (p : Fin 2 × ℕ) : GS_nice fun h => GS_wv e ι h p :=
  GS_nice_ntr (GS_niceM_mul (fun k l => by
    simpa using GS_nice_sub (GS_niceM_G e hz p.1 k l) (GS_nice_const (e.M p.1 k l)))
    (GS_niceM_const _))

/-- A product of light weights is `GS_nice`. -/
private lemma GS_nice_weights {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) : ∀ ws : List (Fin 2 × ℕ),
      GS_nice fun h => (ws.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod
  | [] => by simpa using GS_nice_const (D := D) (N := N) 1
  | p :: ws => by
      have := GS_nice_mul (GS_nice_wv e hz ι p) (GS_nice_weights e hz ι ws)
      simpa [GS_wv] using this

/-- A product of loops is `GS_nice`. -/
private lemma GS_nice_loops {D N nb : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (ι : Fin nb → Fin D) : ∀ ls : List (List LoopLetter),
      GS_nice fun h => (ls.map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod
  | [] => by simpa using GS_nice_const (D := D) (N := N) 1
  | w :: ls => by
      have := GS_nice_mul (GS_nice_ntr (GS_niceM_word e hz ι w)) (GS_nice_loops e hz ι ls)
      simpa using this

/-- The values of the expressions of the class are `GS_nice`. -/
private lemma GS_nice_evalH {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) : GS_nice fun h => T.evalH e h := by
  unfold LoopExpr.evalH
  exact GS_nice_mul (GS_nice_const _) (GS_nice_sum _ fun ι _ =>
    GS_nice_mul (GS_nice_weights e hz ι T.weights) (GS_nice_loops e hz ι T.loops))

/-- `GS_nice` functions are integrable for a law of almost surely Hermitian arrays. -/
private lemma GS_nice_integrable {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian)
    {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : GS_nice f) : Integrable f μ := by
  obtain ⟨⟨g, hgc, hg⟩, B, hB⟩ := hf
  refine Integrable.of_bound (hgc.aestronglyMeasurable.congr ?_) B ?_
  · filter_upwards [hμ] with h hh using (hg h hh).symm
  · filter_upwards [hμ] with h hh using hB h hh


private lemma Rg_avgSq_lam (D N : ℕ) (_hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    avgSq (lam D N A) ≤ 4 * D * hsNorm A ^ 2 / N := by
  have hH := lam_isHermitian D N A
  set Λ := lam D N A
  have hn : (Fintype.card (Idx D N) : ℝ) = D * N := by simp
  have hDN : (0 : ℝ) < D * N := by
    have : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  -- `⟨Λ²⟩ = (DN)⁻¹ Σ_{p,q} |Λ_pq|²`
  have e : avgSq Λ = ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 := by
    unfold avgSq ntr
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    have : ∀ p q : Idx D N, Λ p q * Λ q p = ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) := by
      intro p q
      have : Λ q p = star (Λ p q) := by
        have := congrFun (congrFun hH.eq q) p
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
        ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) = ((((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 : ℝ) : ℂ) by
      push_cast [Fintype.card_prod, Fintype.card_fin]; ring]
    rw [Complex.ofReal_re]
  -- each entry
  have hent : ∀ p q : Idx D N, ‖Λ p q‖ ^ 2 ≤ 2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
    intro p q
    simp only [Λ, lam]
    have h1 : ‖(if fwd D p.1 q.1 then A p.2 q.2 else 0)‖ ≤ ‖A p.2 q.2‖ := by
      split_ifs <;> simp
    have h2 : ‖(if fwd D q.1 p.1 then star (A q.2 p.2) else 0)‖ ≤ ‖A q.2 p.2‖ := by
      split_ifs <;> simp
    set x := (if fwd D p.1 q.1 then A p.2 q.2 else 0)
    set y := (if fwd D q.1 p.1 then star (A q.2 p.2) else 0)
    have hxy := norm_add_le x y
    have h3 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    have h1' : ‖x‖ ^ 2 ≤ ‖A p.2 q.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖y‖ ^ 2 ≤ ‖A q.2 p.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have key : ∀ g : Fin N → Fin N → ℝ, ∑ p : Idx D N, ∑ q : Idx D N, g p.2 q.2 =
      (D : ℝ) ^ 2 * ∑ i, ∑ j, g i j := by
    intro g
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsum : ∑ p : Idx D N, ∑ q : Idx D N, (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) =
      2 * (D : ℝ) ^ 2 * hsNorm A ^ 2 := by
    have hs : hsNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
      unfold hsNorm; rw [Real.sq_sqrt (by positivity)]
    simp only [Finset.sum_add_distrib]
    rw [key (fun i j => ‖A i j‖ ^ 2), key (fun i j => ‖A j i‖ ^ 2), hs,
      Finset.sum_comm (f := fun i j => ‖A j i‖ ^ 2)]
    ring
  rw [e]
  calc ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2
      ≤ ((D : ℝ) * N)⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
          2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
        gcongr with p _ q _; exact hent p q
    _ = 4 * D * hsNorm A ^ 2 / N := by
        simp only [← Finset.mul_sum]
        rw [hsum]
        field_simp
        ring

/-! ## Loops without `Λ̃`: the gain `Im m` of (A.53) -/

/-- The larger of the two `Im m_a`. -/
private def Lf_imax {D N : ℕ} (e : LoopEnv D N) : ℝ :=
  max (mSol ((e.c 0 : ℂ) • lam D N e.A) (e.z 0)).im (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im

private lemma Lf_imax_ge {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) :
    (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤ Lf_imax e := by
  fin_cases a
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- `bndA4 ≤ V η^{-(l-1)}` for `l ≥ 2`, `Im m_i ≤ V`, `η ≤ η_i`. -/
private lemma Lf_bndA4_le {p : ℕ} [Nonempty (Fin p)] (imm eta : Fin p → ℝ) (l : ℕ) (η V : ℝ)
    (hl : 2 ≤ l) (hη : 0 < η) (him : ∀ i, imm i ≤ V) (het : ∀ i, η ≤ eta i) (hV : 0 ≤ V) :
    bndA4 imm eta l ≤ V * η⁻¹ ^ (l - 1) := by
  unfold bndA4
  rw [if_pos hl]
  have hinf : η ≤ ⨅ i, eta i := le_ciInf het
  have hpos : 0 < (⨅ i, eta i) ^ (l - 1) := pow_pos (hη.trans_le hinf) _
  have hnum : (⨆ i, imm i) ≤ V := ciSup_le him
  calc (⨆ i, imm i) / (⨅ i, eta i) ^ (l - 1) ≤ V / (⨅ i, eta i) ^ (l - 1) :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ ≤ V / η ^ (l - 1) :=
        div_le_div_of_nonneg_left hV (pow_pos hη _) (pow_le_pow_left₀ hη.le hinf _)
    _ = V * η⁻¹ ^ (l - 1) := by rw [div_eq_mul_inv, inv_pow]

/-- A loop without `Λ̃` and with `r ≥ 2` resolvents, by (A.53) [entprodG]:
`|⟨Π⟩| ≺ Im m η^{-(r-1)}`. -/
private lemma Lf_loop_free (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hw : w.countP Bd_isL = 0) (hr : 2 ≤ w.countP Bd_isRes) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖ntr (loopWordMat (x.2.G h) x.2.M E x.2.Lt w)‖ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' *
            Lf_imax x.2 * (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) := by
  intro τ'' hτ'' D' hD'
  obtain ⟨a, g, b, rfl, -, hg⟩ := Bd_split Bd_isRes w (by omega)
  have hdec : (Bd_dec (g :: (b ++ a))).1 = [] := by simp [Bd_dec, hg]
  have hpr : (Bd_dec (g :: (b ++ a))).2.length = (a ++ g :: b).countP Bd_isRes := by
    rw [Bd_dec_len]
    simp only [List.countP_append, List.countP_cons]
    omega
  have hp1 : 1 ≤ (Bd_dec (g :: (b ++ a))).2.length := by omega
  have hvL : (g :: (b ++ a)).countP Bd_isL = 0 := by
    simp only [List.countP_append, List.countP_cons] at hw ⊢
    omega
  have hvlen : (g :: (b ++ a)).length = (a ++ g :: b).length := by simp; omega
  have hplen : (Bd_dec (g :: (b ++ a))).2.length ≤ (a ++ g :: b).length := by
    rw [Bd_dec_len, ← hvlen]
    exact List.countP_le_length
  set p := (Bd_dec (g :: (b ++ a))).2.length with hp
  set σ : Fin p → Fin 2 := fun j => ((Bd_dec (g :: (b ++ a))).2.get j).1 with hσ
  have hU := Bd_ent_unif D hD p hp1 σ δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C τ'' hτ'' D' hD'
  filter_upwards [hU, Filter.eventually_ge_atTop 1] with N hN hN1 x hx hz E hE
  obtain ⟨-, hM, -, hη, hηz, him⟩ := Bd_facts hD hN1 hC₀ hx hz
  set Rs : ℝ := (5 / 4) ^ (a ++ g :: b).length with hRs
  have hRs1 : 1 ≤ Rs := one_le_pow₀ (by norm_num)
  have hRs0 : 0 < Rs := by linarith
  set B' : Fin p → Matrix (Idx D N) (Idx D N) ℂ :=
    fun j => ((Rs⁻¹ : ℝ) : ℂ) • Bd_Bv x.2.M E x.2.Lt (g :: (b ++ a)) j.succ with hB'
  have hB'n : ∀ j, opNorm (B' j) ≤ 1 := by
    intro j
    simp only [hB']
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRs0)]
    have := Bd_Bv_norm x.2.M E x.2.Lt hM hE _ hvL j.succ
    rw [hvlen] at this
    rw [inv_mul_le_iff₀ hRs0, mul_one]
    exact this
  refine ⟨_, hN x hx hz (fun j => x.2.s (σ j)) B' hB'n, fun h hh hbad => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt] at hbad
  set Gr : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ :=
    fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i) with hGr
  have hkey1 : resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j)) B' =
      ((Rs⁻¹ : ℝ) : ℂ) ^ p • resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j))
        (fun j => Bd_Bv x.2.M E x.2.Lt (g :: (b ++ a)) j.succ) := by
    unfold resProd
    exact Bd_ofFn_smul _ _ _
  have h0 : Bd_Bv x.2.M E x.2.Lt (g :: (b ++ a)) 0 = 1 := by
    simp only [Bd_Bv, Fin.cons_zero, hdec, List.map_nil, List.prod_nil]
  have hkey2 : resWord Gr (Bd_wv x.2.s (g :: (b ++ a))) (Bd_Bv x.2.M E x.2.Lt (g :: (b ++ a))) =
      resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j))
        (fun j => Bd_Bv x.2.M E x.2.Lt (g :: (b ++ a)) j.succ) := by
    unfold resWord resProd
    rw [h0, Matrix.one_mul]
    rfl
  have hmat : ntr (loopWordMat (x.2.G h) x.2.M E x.2.Lt (a ++ g :: b)) =
      (Rs : ℂ) ^ p * ntr (resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j)) B') := by
    rw [Bd_wordMat_eq, Bd_mat_zero _ _ _ _ a b g, Bd_G_eq _ _ hh, Bd_mat_resWord Gr, hkey2,
      hkey1, Bd_ntr_smul, ← mul_assoc, ← mul_pow]
    have : (Rs : ℂ) * ((Rs⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast
      exact mul_inv_cancel₀ (by exact_mod_cast hRs0.ne')
    rw [this, one_pow, one_mul]
  rw [hmat, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRs0, ← hpr]
  have : Nonempty (Fin p) := ⟨⟨0, hp1⟩⟩
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hV0 : 0 ≤ Lf_imax x.2 := le_trans (mSol_spec _ (Bd_slot_lam hx 0).1 _ (hz 0).2.1).1.le
    (le_max_left _ _)
  have h2 := Lf_bndA4_le (fun i => (mSol ((x.2.c (σ i) : ℂ) • lam D N x.2.A) (x.2.z (σ i))).im)
    (fun i => (x.2.z (σ i)).im) p (Bd_eta x.2) (Lf_imax x.2) (by omega) hη
    (fun i => Lf_imax_ge x.2 (σ i)) (fun i => hηz (σ i)) hV0
  have hRp : Rs ^ p ≤ Bd_cw D K (a ++ g :: b).length := by
    refine le_trans ?_ (Bd_cw_ge D hD K (a ++ g :: b).length).1
    rw [hRs, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hplen)
  have hk : 0 ≤ Lf_imax x.2 * (Bd_eta x.2)⁻¹ ^ (p - 1) := by positivity
  have hNτ : 0 ≤ (N : ℝ) ^ τ'' := by positivity
  calc Rs ^ p * ‖ntr (resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j)) B')‖
      ≤ Rs ^ p * ((N : ℝ) ^ τ'' * (Lf_imax x.2 * (Bd_eta x.2)⁻¹ ^ (p - 1))) := by
        refine mul_le_mul_of_nonneg_left (hbad.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hNτ
    _ ≤ Bd_cw D K (a ++ g :: b).length * ((N : ℝ) ^ τ'' * (Lf_imax x.2 *
          (Bd_eta x.2)⁻¹ ^ (p - 1))) :=
        mul_le_mul_of_nonneg_right hRp (by positivity)
    _ = _ := by ring


/-! ## The bound of an expression flag by flag -/

/-- The word contains a `Λ̃`. -/
private def Lf_lamB (w : List LoopLetter) : Bool := decide (0 < w.countP Bd_isL)

/-- The number of loops without `Λ̃`. -/
private def Lf_nf (T : LoopExpr) : ℕ := (T.loops.filter fun w => !Lf_lamB w).length

/-- The number `m` of resolvents in the loops. -/
private def Lf_m (T : LoopExpr) : ℕ := (T.loops.map (List.countP Bd_isRes)).sum

/-- `Π (if p then f else g) = Π_{p} f · Π_{¬p} g`. -/
private lemma Lf_prod_ite {α : Type*} (l : List α) (p : α → Bool) (f g : α → ℝ) :
    (l.map fun x => if p x then f x else g x).prod =
      ((l.filter p).map f).prod * ((l.filter fun x => !p x).map g).prod := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hx : p x = true
    · simp only [List.map_cons, List.prod_cons, hx, ite_true, ih, List.filter_cons, Bool.not_true,
        Bool.false_eq_true]
      simp
      ring
    · simp only [List.map_cons, List.prod_cons, hx, ih, List.filter_cons]
      simp
      ring

/-- A sum splits along a predicate. -/
private lemma Lf_sum_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter fun x => !p x).map f).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hx : p x = true
    · simp [hx, ih, List.filter_cons]
      omega
    · simp [hx, ih, List.filter_cons]
      omega

/-- `length ≤ Σ f` when every `f ≥ 1`. -/
private lemma Lf_len_le {α : Type*} (l : List α) (f : α → ℕ) (h : ∀ x ∈ l, 1 ≤ f x) :
    l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- `Σ (f - 1) = Σ f - length` when every `f ≥ 1`. -/
private lemma Lf_sum_sub {α : Type*} (l : List α) (f : α → ℕ) (h : ∀ x ∈ l, 1 ≤ f x) :
    (l.map fun x => f x - 1).sum = (l.map f).sum - l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    have h3 := Lf_len_le t f fun y hy => h y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- `Π a b^{f x} = a^{len} b^{Σ f}`. -/
private lemma Lf_prod_pow {α : Type*} (l : List α) (a b : ℝ) (f : α → ℕ) :
    (l.map fun x => a * b ^ f x).prod = a ^ l.length * b ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, ih]
    rw [pow_succ, pow_add]
    ring

/-- `|D^{dexp} N^{-S} Σ_ι Π W Π ⟨Π⟩| ≤ D^{dexp} N^{-S} D^{nb} Wb^u Π b(w)`. -/
private lemma Lf_evalH_le {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) (Wb : ℝ) (hWb : 0 ≤ Wb) (b : List LoopLetter → ℝ)
    (hb : ∀ w, 0 ≤ b w)
    (hW : ∀ ι : Fin T.nb → Fin D, ∀ p ∈ T.weights,
      ‖ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)‖ ≤ Wb)
    (hL : ∀ ι : Fin T.nb → Fin D, ∀ w ∈ T.loops,
      ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤ b w) :
    ‖T.evalH e h‖ ≤ (D : ℝ) ^ T.dexp * ((N : ℝ) ^ T.S)⁻¹ * ((D : ℝ) ^ T.nb *
      (Wb ^ T.weights.length * (T.loops.map b).prod)) := by
  unfold LoopExpr.evalH
  rw [norm_mul, norm_mul, norm_zpow, Complex.norm_natCast, norm_inv, norm_pow,
    Complex.norm_natCast]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) ^ T.dexp := zpow_nonneg (Nat.cast_nonneg _) _
  have hP0 : 0 ≤ (T.loops.map b).prod := List.prod_nonneg fun x hx => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact hb w
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hD0 (by positivity))
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ι : Fin T.nb → Fin D,
      ‖(T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
        (T.loops.map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod‖ ≤
      Wb ^ T.weights.length * (T.loops.map b).prod := by
    intro ι
    rw [norm_mul]
    have h1 := Bd_list_norm T.weights (fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2))
      (fun _ => Wb) (hW ι)
    have h2 := Bd_list_norm T.loops (fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w))
      b (hL ι)
    rw [List.map_const', List.prod_replicate] at h1
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  refine (Finset.sum_le_sum fun ι _ => hterm ι).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  exact le_rfl

set_option maxHeartbeats 1000000 in
/-- The flag-by-flag bound of an expression of the class whose loops with a `Λ̃` carry no
resolvent and are bounded by `β`, and whose other loops have at least two resolvents:
`|E 𝒯| ≤ N^{τ'} N^{-S} (Nη)^{-u} (Im m)^{n_f} η^{-(m - n_f)} Π β`, with (2.23) [eq:aver_local]
for the light weights and (A.53) [entprodG] for the loops without `Λ̃`. -/
private lemma Lf_flag (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (C : ℕ → ℝ) (T : LoopExpr)
    (hfree : ∀ w ∈ T.loops, Lf_lamB w = false → 2 ≤ w.countP Bd_isRes)
    (hlam : ∀ w ∈ T.loops, Lf_lamB w = true → w.countP Bd_isRes = 0) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), ∀ e : LoopEnv D N, (μ, e) ∈ Bd_Cl D δA 1 K C N →
      (∀ a, Bd_zc D τ c₀ N e a) →
      ∀ β : List LoopLetter → ℝ, (∀ w, 0 ≤ β w) →
      (∀ (ι : Fin T.nb → Fin D) (h : Idx D N → Idx D N → ℂ), ∀ w ∈ T.loops, Lf_lamB w = true →
        ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤ β w) →
        ‖∫ h, T.evalH e h ∂μ‖ ≤ (N : ℝ) ^ τ' * (((N : ℝ) ^ T.S)⁻¹ *
          ((N : ℝ)⁻¹ * (Bd_eta e)⁻¹) ^ T.weights.length * Lf_imax e ^ Lf_nf T *
          (Bd_eta e)⁻¹ ^ (Lf_m T - Lf_nf T) * ((T.loops.filter Lf_lamB).map β).prod) := by
  intro τ' hτ'
  have hD1 : 1 ≤ D := by omega
  set u := T.weights.length with hu
  set F := T.loops.filter fun w => !Lf_lamB w with hF
  set nf := F.length with hnf
  rw [show Lf_nf T = nf from rfl]
  set Ltot := (T.loops.map List.length).sum with hLtot
  set Tt : ℝ := max 1 τ⁻¹ with hTt
  have hTt1 : 1 ≤ Tt := le_max_left _ _
  set Cbig : ℝ := Bd_cw D K Ltot with hCbig
  have hCbig0 : 0 ≤ Cbig := le_trans zero_le_one (Bd_cw_ge D hD1 K Ltot).2.2.2
  set τ'' : ℝ := τ' / (2 * ((u : ℝ) + nf + 1)) with hτ''def
  have hτ'' : 0 < τ'' := by positivity
  have hττ : τ'' * (u + nf) ≤ τ' / 2 := by
    rw [hτ''def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set Dn : ℕ := 2 * u + Ltot + nf + 1 with hDn
  have hDn0 : (0 : ℝ) < (Dn : ℝ) := by positivity
  have hFm : ∀ w ∈ F, w ∈ T.loops ∧ Lf_lamB w = false := by
    intro w hw
    rw [hF, List.mem_filter] at hw
    exact ⟨hw.1, by simpa using hw.2⟩
  have hFL : ∀ w ∈ F, w.countP Bd_isL = 0 := by
    intro w hw
    have := (hFm w hw).2
    simp only [Lf_lamB, decide_eq_false_iff_not, not_lt, Nat.le_zero] at this
    exact this
  have hW := Bd_weight D hD1 δA τ 1 hδA hτ le_rfl C τ'' hτ'' Dn hDn0
  have hL := (Filter.eventually_all_finset F.toFinset).mpr fun w hw =>
    Lf_loop_free D hD1 δA τ c₀ 1 K hδA hτ hc₀ le_rfl C w (hFL w (List.mem_toFinset.mp hw))
      (hfree w (hFm w (List.mem_toFinset.mp hw)).1 (hFm w (List.mem_toFinset.mp hw)).2) τ''
      hτ'' Dn hDn0
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hW.and hL)
  set C₁ : ℝ := (D : ℝ) ^ T.dexp * (D : ℝ) ^ T.nb * Cbig ^ nf with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  obtain ⟨N₂, hN₂⟩ := Bd_large (τ' / 2) (2 * C₁) (by positivity)
  set Cb : ℝ := (D : ℝ) ^ T.dexp * (D : ℝ) ^ T.nb * 2 ^ u * ((D : ℝ) ^ T.nb * (u + nf)) *
    Tt ^ (u + nf + (Lf_m T - nf)) * (c₀⁻¹) ^ nf with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  obtain ⟨N₃, hN₃⟩ := Bd_large 1 (2 * Cb) one_pos
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN μ e hx hz β hβ0 hβ => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hWN, hLN⟩ := hN₁ N hNa
  have hlarge1 := hN₂ N hNb
  have hlarge2 : 2 * Cb ≤ N := by simpa using hN₃ N hNc
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  obtain ⟨hμ, hA, hA2, hc, hδ⟩ := hx
  obtain ⟨hA1, hM, hLt, hη, hηz, -⟩ := Bd_facts hD1 (by omega) le_rfl ⟨hμ, hA, hA2, hc, hδ⟩ hz
  have := hμ.prob
  have hzN : ∀ a, (N : ℝ)⁻¹ ≤ |(e.z a).im| := by
    intro a
    refine le_trans ?_ (hz a).1.2
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hηT : Bd_eta e ≤ Tt := by
    refine (hηz 0).trans ((Complex.im_le_norm _).trans ((hz 0).1.1.trans ?_))
    exact le_max_right _ _
  have hz0T : (e.z 0).im ≤ Tt := (Complex.im_le_norm _).trans ((hz 0).1.1.trans (le_max_right _ _))
  -- the lower bound on `Im m`
  have hV0 : c₀ * (N : ℝ)⁻¹ * Tt⁻¹ ≤ Lf_imax e := by
    have h1 := (hz 0).2.2
    have h2 := (hz 0).2.1
    refine le_trans ?_ (Lf_imax_ge e 0)
    rw [mul_assoc, ← mul_inv]
    rw [mul_inv_le_iff₀ (by positivity)]
    calc c₀ ≤ (N : ℝ) * (e.z 0).im * (mSol ((e.c 0 : ℂ) • lam D N e.A) (e.z 0)).im := h1
      _ ≤ (N : ℝ) * Tt * (mSol ((e.c 0 : ℂ) • lam D N e.A) (e.z 0)).im := by
        have : 0 ≤ (mSol ((e.c 0 : ℂ) • lam D N e.A) (e.z 0)).im := by
          by_contra hneg
          push_neg at hneg
          have : (N : ℝ) * (e.z 0).im * (mSol ((e.c 0 : ℂ) • lam D N e.A) (e.z 0)).im < 0 :=
            mul_neg_of_pos_of_neg (by positivity) hneg
          linarith
        gcongr
      _ = _ := by ring
  have hVpos : 0 < Lf_imax e := lt_of_lt_of_le (by positivity) hV0
  -- the events
  have hWb : ∀ (ι : Fin T.nb → Fin D) (i : Fin u), ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Dn : ℝ))) ∧ ∀ h, h ∉ bad →
        ‖ntr ((e.G h (T.weights.get i).1 - e.M (T.weights.get i).1) *
          e.E ι (T.weights.get i).2)‖ ≤
          (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |(e.z (T.weights.get i).1).im|)) :=
    fun ι i => hWN μ hμ e hA hc (fun a => (hz a).1) _ _ (Bd_opNorm_E e ι _)
  choose bW hbW1 hbW2 using hWb
  have hLb : ∀ (ι : Fin T.nb → Fin D) (i : Fin nf), ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Dn : ℝ))) ∧ ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
        ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt (F.get i))‖ ≤
          Bd_cw D K (F.get i).length * (N : ℝ) ^ τ'' * Lf_imax e *
            (Bd_eta e)⁻¹ ^ ((F.get i).countP Bd_isRes - 1) :=
    fun ι i => hLN (F.get i) (List.mem_toFinset.mpr (List.get_mem _ _)) (μ, e)
      ⟨hμ, hA, hA2, hc, hδ⟩ hz (e.E ι) (Bd_opNorm_E e ι)
  choose bL hbL1 hbL2 using hLb
  set bad : Set (Idx D N → Idx D N → ℂ) := ⋃ ι, ((⋃ i, bW ι i) ∪ ⋃ i, bL ι i) with hbad
  have hNDn : 0 ≤ (N : ℝ) ^ (-(Dn : ℝ)) := by positivity
  have hmbad : μ.real bad ≤ (D : ℝ) ^ T.nb * (u + nf) * (N : ℝ) ^ (-(Dn : ℝ)) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    have hι : ∀ ι : Fin T.nb → Fin D, μ.real ((⋃ i, bW ι i) ∪ ⋃ i, bL ι i) ≤
        ((u : ℝ) + nf) * (N : ℝ) ^ (-(Dn : ℝ)) := by
      intro ι
      refine (measureReal_union_le _ _).trans ?_
      refine (add_le_add (measureReal_iUnion_fintype_le _)
        (measureReal_iUnion_fintype_le _)).trans ?_
      refine (add_le_add (Finset.sum_le_sum fun i _ =>
        ENNReal.toReal_le_of_le_ofReal hNDn (hbW1 ι i)) (Finset.sum_le_sum fun i _ =>
        ENNReal.toReal_le_of_le_ofReal hNDn (hbL1 ι i))).trans ?_
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
        Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
      ring_nf
      exact le_rfl
    refine (Finset.sum_le_sum fun ι _ => hι ι).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl
  -- notation
  set η := Bd_eta e with hηdef
  set V := Lf_imax e with hVdef
  set Pβ := ((T.loops.filter Lf_lamB).map β).prod with hPβ
  have hPβ0 : 0 ≤ Pβ := List.prod_nonneg fun x hx => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact hβ0 w
  have hm_eq : Lf_m T = (F.map (List.countP Bd_isRes)).sum := by
    rw [Lf_m, Lf_sum_filter T.loops Lf_lamB (List.countP Bd_isRes)]
    have : ((T.loops.filter Lf_lamB).map (List.countP Bd_isRes)).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_filter] at hw
      exact hlam w hw.1 hw.2
    rw [this, zero_add]
  have hsumF : (F.map fun w => w.countP Bd_isRes - 1).sum = Lf_m T - nf := by
    rw [hm_eq, Lf_sum_sub F _ fun w hw => by
      have := hfree w (hFm w hw).1 (hFm w hw).2
      omega]
  have hlenF : (F.map List.length).sum ≤ Ltot := by
    rw [hLtot, Lf_sum_filter T.loops (fun w => !Lf_lamB w) List.length]
    exact Nat.le_add_right _ _
  -- the pointwise bounds
  set RHS₀ : ℝ := ((N : ℝ) ^ T.S)⁻¹ * ((N : ℝ)⁻¹ * η⁻¹) ^ u * V ^ nf * η⁻¹ ^ (Lf_m T - nf) * Pβ
    with hRHS₀
  set Rb : ℝ := (D : ℝ) ^ T.dexp * ((N : ℝ) ^ T.S)⁻¹ * ((D : ℝ) ^ T.nb * ((2 * (N : ℝ)) ^ u *
      ((N : ℝ) ^ Ltot * Pβ))) with hRb
  have hG : ∀ (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian → ∀ a,
      opNorm (e.G h a) ≤ N := by
    intro h hh a
    refine (Bd_G_norm e h hh a (hz a).2.1.ne').trans ?_
    rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (hzN a)) (by positivity)]
    exact hzN a
  have hcrude : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ‖T.evalH e h‖ ≤ Rb := by
    intro h hh
    have h1 := Lf_evalH_le T e h (2 * N) (by positivity)
      (fun w => if Lf_lamB w then β w else (N : ℝ) ^ w.length)
      (fun w => by split_ifs <;> [exact hβ0 w; positivity])
      (fun ι p _ => by
        refine (Bd_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
        have h1 := Bd_opNorm_sub (e.G h p.1) (e.M p.1)
        have h2 := hG h hh p.1
        have h3 := hM p.1
        have h0 := Bd_opNorm_nonneg (e.G h p.1 - e.M p.1)
        calc opNorm (e.G h p.1 - e.M p.1) * opNorm (e.E ι p.2)
            ≤ opNorm (e.G h p.1 - e.M p.1) * 1 :=
              mul_le_mul_of_nonneg_left (Bd_opNorm_E e ι p.2) h0
          _ ≤ 2 * N := by linarith)
      (fun ι w hw => by
        by_cases hl : Lf_lamB w = true
        · simp only [hl, ↓reduceIte]
          exact hβ ι h w hw hl
        · simp only [hl, Bool.false_eq_true, ↓reduceIte]
          refine (Bd_ntr_le _).trans ?_
          have hl' : w.countP Bd_isL = 0 := by
            simp only [Lf_lamB, decide_eq_true_eq, not_lt, Nat.le_zero] at hl
            exact hl
          have := Bd_prod_normL w (Bd_let (e.G h) e.M (e.E ι) e.Lt) N 0 (by linarith) le_rfl
            fun y hy => by
              cases y with
              | res a => simpa [Bd_isL, Bd_let] using hG h hh a
              | det a => simpa [Bd_isL, Bd_let] using (hM a).trans (by linarith)
              | proj y => simpa [Bd_isL, Bd_let] using (Bd_opNorm_E e ι y).trans (by linarith)
              | lamt o =>
                exfalso
                have : 0 < w.countP Bd_isL := List.countP_pos_iff.2 ⟨_, hy, rfl⟩
                omega
          rw [hl', pow_zero, mul_one] at this
          exact this)
    refine h1.trans ?_
    rw [Lf_prod_ite]
    have hFp : (F.map fun w => (N : ℝ) ^ w.length).prod = (N : ℝ) ^ (F.map List.length).sum := by
      have := Lf_prod_pow F 1 (N : ℝ) List.length
      simpa using this
    rw [hFp, hRb, mul_comm Pβ]
    gcongr
  have hgood : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → h ∉ bad →
      ‖T.evalH e h‖ ≤ 1 / 2 * ((N : ℝ) ^ τ' * RHS₀) := by
    intro h hh hb
    have hbW : ∀ ι i, h ∉ bW ι i := fun ι i hm =>
      hb (Set.mem_iUnion.mpr ⟨ι, Or.inl (Set.mem_iUnion.mpr ⟨i, hm⟩)⟩)
    have hbL : ∀ ι i, h ∉ bL ι i := fun ι i hm =>
      hb (Set.mem_iUnion.mpr ⟨ι, Or.inr (Set.mem_iUnion.mpr ⟨i, hm⟩)⟩)
    have h1 := Lf_evalH_le T e h ((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * η⁻¹)) (by positivity)
      (fun w => if Lf_lamB w then β w else
        Cbig * (N : ℝ) ^ τ'' * V * η⁻¹ ^ (w.countP Bd_isRes - 1))
      (fun w => by split_ifs <;> [exact hβ0 w; positivity])
      (fun ι p hp => by
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
        refine (hbW2 ι i h (hbW ι i)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hzi := hηz (T.weights.get i).1
        have hzp := (hz (T.weights.get i).1).2.1
        rw [abs_of_pos hzp, one_div, mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hη hzi) (by positivity))
      (fun ι w hw => by
        by_cases hl : Lf_lamB w = true
        · simp only [hl, ↓reduceIte]
          exact hβ ι h w hw hl
        · simp only [hl, Bool.false_eq_true, ↓reduceIte]
          have hwF : w ∈ F := by
            rw [hF, List.mem_filter]
            exact ⟨hw, by simpa using hl⟩
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hwF
          refine (hbL2 ι i h hh (hbL ι i)).trans ?_
          have hlen : (F.get i).length ≤ Ltot :=
            le_trans (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem _ _))) hlenF
          have hcw := Bd_cw_mono D K hlen
          have h0 : 0 ≤ (N : ℝ) ^ τ'' * V * η⁻¹ ^ ((F.get i).countP Bd_isRes - 1) := by
            positivity
          calc Bd_cw D K (F.get i).length * (N : ℝ) ^ τ'' * V *
                η⁻¹ ^ ((F.get i).countP Bd_isRes - 1)
              = Bd_cw D K (F.get i).length * ((N : ℝ) ^ τ'' * V *
                η⁻¹ ^ ((F.get i).countP Bd_isRes - 1)) := by ring
            _ ≤ Cbig * ((N : ℝ) ^ τ'' * V * η⁻¹ ^ ((F.get i).countP Bd_isRes - 1)) :=
                mul_le_mul_of_nonneg_right hcw h0
            _ = _ := by ring)
    refine h1.trans ?_
    rw [Lf_prod_ite]
    have hFp : (F.map fun w => Cbig * (N : ℝ) ^ τ'' * V * η⁻¹ ^ (w.countP Bd_isRes - 1)).prod =
        (Cbig * (N : ℝ) ^ τ'' * V) ^ nf * η⁻¹ ^ (Lf_m T - nf) := by
      rw [Lf_prod_pow, hsumF]
    rw [hFp]
    have hPu : ((N : ℝ) ^ τ'') ^ u * ((N : ℝ) ^ τ'') ^ nf ≤ (N : ℝ) ^ (τ' / 2) := by
      rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith)
    have hhalf : C₁ * (N : ℝ) ^ (τ' / 2) ≤ 1 / 2 * (N : ℝ) ^ τ' := by
      have : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
        rw [← Real.rpow_add hNpos]; ring_nf
      rw [this]
      have h0 : 0 ≤ (N : ℝ) ^ (τ' / 2) := by positivity
      nlinarith
    have hR0 : 0 ≤ RHS₀ := by positivity
    calc (D : ℝ) ^ T.dexp * ((N : ℝ) ^ T.S)⁻¹ * ((D : ℝ) ^ T.nb *
          (((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * η⁻¹)) ^ u * (Pβ * ((Cbig * (N : ℝ) ^ τ'' * V) ^ nf *
            η⁻¹ ^ (Lf_m T - nf)))))
        = C₁ * (((N : ℝ) ^ τ'') ^ u * ((N : ℝ) ^ τ'') ^ nf) * RHS₀ := by
          rw [hRHS₀, hC₁]; ring
      _ ≤ C₁ * (N : ℝ) ^ (τ' / 2) * RHS₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPu hC₁0) hR0
      _ ≤ 1 / 2 * (N : ℝ) ^ τ' * RHS₀ := mul_le_mul_of_nonneg_right hhalf hR0
      _ = _ := mul_assoc _ _ _
  -- the bad event
  have hRb0 : 0 ≤ Rb := by positivity
  have hR0 : 0 ≤ RHS₀ := by positivity
  set L : ℕ := u + nf + (Lf_m T - nf) with hL
  have hlow : ((N : ℝ) ^ T.S)⁻¹ * Pβ * (c₀ ^ nf * (((N : ℝ) ^ (u + nf))⁻¹ * (Tt ^ L)⁻¹)) ≤
      RHS₀ := by
    have e1 : ((N : ℝ) ^ T.S)⁻¹ * Pβ * (c₀ ^ nf * (((N : ℝ) ^ (u + nf))⁻¹ * (Tt ^ L)⁻¹)) =
        ((N : ℝ) ^ T.S)⁻¹ * ((N : ℝ)⁻¹ * Tt⁻¹) ^ u * (c₀ * (N : ℝ)⁻¹ * Tt⁻¹) ^ nf *
          Tt⁻¹ ^ (Lf_m T - nf) * Pβ := by
      rw [hL, pow_add, pow_add, pow_add]
      simp only [mul_pow, inv_pow, mul_inv]
      ring
    rw [e1, hRHS₀]
    have hTi : Tt⁻¹ ≤ η⁻¹ := inv_anti₀ hη hηT
    gcongr
  have hbadb : μ.real bad * Rb ≤ 1 / 2 * ((N : ℝ) ^ τ' * RHS₀) := by
    have hNτ : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hN1r hτ'.le
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (le_trans hlow (le_mul_of_one_le_left hR0 hNτ)) (by norm_num))
    have hDnr : (N : ℝ) ^ (-(Dn : ℝ)) = ((N : ℝ) ^ Dn)⁻¹ := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_natCast]
    rw [hDnr] at hmbad
    have hP0 : 0 ≤ ((N : ℝ) ^ T.S)⁻¹ * Pβ := by positivity
    set P : ℝ := (D : ℝ) ^ T.dexp * (D : ℝ) ^ T.nb * 2 ^ u * ((D : ℝ) ^ T.nb * (u + nf)) with hP
    have hP0' : 0 ≤ P := by positivity
    have e2 : (D : ℝ) ^ T.nb * (u + nf) * ((N : ℝ) ^ Dn)⁻¹ * Rb =
        ((N : ℝ) ^ T.S)⁻¹ * Pβ * (P * ((N : ℝ) ^ (u + nf + 1))⁻¹) := by
      rw [hRb, hP, hDn]
      have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
      field_simp
      ring
    have e3 : P * ((N : ℝ) ^ (u + nf + 1))⁻¹ ≤ 1 / 2 * (c₀ ^ nf * (((N : ℝ) ^ (u + nf))⁻¹ *
        (Tt ^ L)⁻¹)) := by
      have hCbP : Cb = P * Tt ^ L * (c₀⁻¹) ^ nf := by
        rw [hCb, hP, hL]
      have hc0n : 0 < c₀ ^ nf := pow_pos hc₀ nf
      have hTL : 0 < Tt ^ L := by positivity
      have hNk : 0 < (N : ℝ) ^ (u + nf) := by positivity
      rw [pow_succ, mul_inv, ← mul_assoc]
      rw [show 1 / 2 * (c₀ ^ nf * (((N : ℝ) ^ (u + nf))⁻¹ * (Tt ^ L)⁻¹)) =
        ((N : ℝ) ^ (u + nf))⁻¹ * (c₀ ^ nf / (2 * Tt ^ L)) by ring]
      rw [mul_comm P, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← div_eq_mul_inv, div_le_div_iff₀ hNpos (by positivity)]
      have : 2 * (P * Tt ^ L * (c₀⁻¹) ^ nf) ≤ N := hCbP ▸ hlarge2
      have e4 : P * (2 * Tt ^ L) = 2 * (P * Tt ^ L * (c₀⁻¹) ^ nf) * c₀ ^ nf := by
        rw [inv_pow]
        field_simp
      rw [e4, mul_comm (c₀ ^ nf)]
      exact mul_le_mul_of_nonneg_right this hc0n.le
    calc μ.real bad * Rb ≤ (D : ℝ) ^ T.nb * (u + nf) * ((N : ℝ) ^ Dn)⁻¹ * Rb :=
          mul_le_mul_of_nonneg_right hmbad hRb0
      _ = ((N : ℝ) ^ T.S)⁻¹ * Pβ * (P * ((N : ℝ) ^ (u + nf + 1))⁻¹) := e2
      _ ≤ ((N : ℝ) ^ T.S)⁻¹ * Pβ * (1 / 2 * (c₀ ^ nf * (((N : ℝ) ^ (u + nf))⁻¹ *
          (Tt ^ L)⁻¹))) := mul_le_mul_of_nonneg_left e3 hP0
      _ = 1 / 2 * (((N : ℝ) ^ T.S)⁻¹ * Pβ * (c₀ ^ nf * (((N : ℝ) ^ (u + nf))⁻¹ *
          (Tt ^ L)⁻¹))) := by ring
  -- integrate
  have hpt : ∀ᵐ h ∂μ, ‖T.evalH e h‖ ≤
      1 / 2 * ((N : ℝ) ^ τ' * RHS₀) + (toMeasurable μ bad).indicator (fun _ => Rb) h := by
    filter_upwards [hμ.herm] with h hh
    by_cases hb : h ∈ toMeasurable μ bad
    · rw [Set.indicator_of_mem hb]
      have : 0 ≤ 1 / 2 * ((N : ℝ) ^ τ' * RHS₀) := by positivity
      exact (hcrude h hh).trans (by linarith)
    · rw [Set.indicator_of_notMem hb, add_zero]
      exact hgood h hh fun h' => hb (subset_toMeasurable _ _ h')
  have hint : Integrable (fun h => 1 / 2 * ((N : ℝ) ^ τ' * RHS₀) +
      (toMeasurable μ bad).indicator (fun _ => Rb) h) μ := (integrable_const _).add
        ((integrable_const Rb).indicator (measurableSet_toMeasurable _ _))
  refine (norm_integral_le_of_norm_le hint hpt).trans ?_
  rw [integral_add (integrable_const _)
    ((integrable_const Rb).indicator (measurableSet_toMeasurable _ _)), integral_const,
    integral_indicator_const _ (measurableSet_toMeasurable _ _), probReal_univ, one_smul,
    smul_eq_mul]
  have hreal : μ.real (toMeasurable μ bad) = μ.real bad := by
    simp only [Measure.real, measure_toMeasurable]
  rw [hreal]
  linarith

/-! ## Deterministic loops with one `Λ̃`: the expansion (A.7) -/

/-- A term `c (E_y or 1) Π_i P(s_i) E_{a_i}` of the normal form of a deterministic word. -/
private abbrev Lf_term (D : ℕ) := ℂ × Option (Fin D) × List (Bool × Fin D)

/-- The matrix of a term. -/
private def Lf_tm {D N : ℕ} (P : Bool → Matrix (Idx D N) (Idx D N) ℂ) (t : Lf_term D) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  t.1 • ((match t.2.1 with | none => 1 | some y => Ea D N y) *
    (t.2.2.map fun q => P q.1 * Ea D N q.2).prod)

/-- The normal form of a word of letters `𝔐_a` (a scalar `c` or `P(s)` by `κ a`) and `E_y`
(the block `ι' y`): `1 = Σ_x E_x` is inserted after every `P(s)`. -/
private def Lf_norm {D : ℕ} (κ : Fin 2 → ℂ ⊕ Bool) (ι' : ℕ → Fin D) :
    List LoopLetter → List (Lf_term D)
  | [] => [(1, none, [])]
  | .det a :: v => (Lf_norm κ ι' v).flatMap fun t => match κ a with
      | .inl c => [(c * t.1, t.2.1, t.2.2)]
      | .inr s => match t.2.1 with
        | some y => [(t.1, none, (s, y) :: t.2.2)]
        | none => (List.finRange D).map fun x => (t.1, none, (s, x) :: t.2.2)
  | .proj y :: v => (Lf_norm κ ι' v).flatMap fun t => match t.2.1 with
      | some y' => if ι' y = y' then [(t.1, some y', t.2.2)] else []
      | none => [(t.1, some (ι' y), t.2.2)]
  | _ :: v => Lf_norm κ ι' v

/-- A sum over a `flatMap`. -/
private lemma Lf_sum_flatMap {α β' : Type*} {γ : Type*} [AddCommMonoid γ] (l : List α)
    (f : α → List β') (g : β' → γ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x t ih => simp [List.flatMap_cons, ih]

/-- `Σ_x E_x = 1`. -/
private lemma Lf_Ea_sum (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

/-- `E_a E_b = δ_{ab} E_a`. -/
private lemma Lf_Ea_mul (D N : ℕ) (a b : Fin D) :
    Ea D N a * Ea D N b = if a = b then Ea D N a else 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    congr 1
    funext p
    by_cases hp : p.1 = a <;> simp [hp]
  · simp only [h, ↓reduceIte]
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p.1 = a
      · have : ¬ p.1 = b := fun e => h (hp.symm.trans e)
        simp [hp, h]
      · simp [hp]
    · simp [hpq]

/-- The normal form reproduces the matrix of the word. -/
private lemma Lf_norm_spec {D N : ℕ} (P : Bool → Matrix (Idx D N) (Idx D N) ℂ)
    (κ : Fin 2 → ℂ ⊕ Bool) (ι' : ℕ → Fin D) (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (hM : ∀ a, M a = match κ a with | .inl c => c • 1 | .inr s => P s) :
    ∀ v : List LoopLetter, (∀ x ∈ v, Bd_isRes x = false ∧ Bd_isL x = false) →
      (∀ y, LoopLetter.proj y ∈ v → E y = Ea D N (ι' y)) →
      (v.map (Bd_let G M E L)).prod = ((Lf_norm κ ι' v).map (Lf_tm P)).sum
  | [], _, _ => by simp [Lf_norm, Lf_tm]
  | x :: v, hv, hE => by
    have ih := Lf_norm_spec P κ ι' G M E L hM v (fun y hy => hv y (by simp [hy]))
      (fun y hy => hE y (by simp [hy]))
    rw [List.map_cons, List.prod_cons, ih, ← List.sum_map_mul_left]
    cases x with
    | res a => simp [Bd_isRes] at hv
    | lamt o => simp [Bd_isL] at hv
    | det a =>
      simp only [Lf_norm, Lf_sum_flatMap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp, Bd_let, hM a]
      rcases hk : κ a with c | s
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Lf_tm,
          smul_smul]
        rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      · rcases hy : t.2.1 with _ | y
        · simp only [Lf_tm, hy, List.map_map, Function.comp, List.map_cons, List.prod_cons]
          rw [← Fin.sum_univ_def]
          simp only [Function.comp, Lf_tm, List.map_cons, List.prod_cons, Matrix.one_mul,
            Matrix.mul_assoc]
          rw [← Finset.smul_sum, ← Finset.mul_sum, ← Finset.sum_mul, Lf_Ea_sum, Matrix.one_mul,
            Matrix.mul_smul]
        · simp only [Lf_tm, hy, List.map_cons, List.prod_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_assoc]
    | proj y =>
      simp only [Lf_norm, Lf_sum_flatMap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp, Bd_let, hE y (by simp)]
      rcases hy : t.2.1 with _ | y'
      · simp [Lf_tm, hy, Matrix.mul_smul]
      · by_cases h : ι' y = y'
        · simp only [Lf_tm, hy, h, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero, Matrix.mul_smul, ← Matrix.mul_assoc, Lf_Ea_mul]
        · simp only [Lf_tm, hy, h, ↓reduceIte, List.map_nil, List.sum_nil, Matrix.mul_smul,
            ← Matrix.mul_assoc, Lf_Ea_mul, Matrix.zero_mul, smul_zero]

/-- The sizes of the normal form: at most `D^{len}` terms, coefficients `≤ R^{len}`, at most
`len` factors `P(s) E`. -/
private lemma Lf_norm_size {D : ℕ} (hD : 1 ≤ D) (κ : Fin 2 → ℂ ⊕ Bool) (ι' : ℕ → Fin D) (R : ℝ)
    (hR : 1 ≤ R) (hκ : ∀ a c, κ a = .inl c → ‖c‖ ≤ R) :
    ∀ v : List LoopLetter, (Lf_norm κ ι' v).length ≤ D ^ v.length ∧
      ∀ t ∈ Lf_norm κ ι' v, ‖t.1‖ ≤ R ^ v.length ∧ t.2.2.length ≤ v.length
  | [] => by simp [Lf_norm]
  | x :: v => by
    obtain ⟨ih1, ih2⟩ := Lf_norm_size hD κ ι' R hR hκ v
    have hRp : ∀ k : ℕ, R ^ k ≤ R ^ (k + 1) := fun k => pow_le_pow_right₀ hR (Nat.le_succ k)
    cases x with
    | res a =>
      simp only [Lf_norm, List.length_cons]
      refine ⟨ih1.trans (Nat.pow_le_pow_right hD (Nat.le_succ _)), fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := ih2 t ht
      exact ⟨h1.trans (hRp _), by omega⟩
    | lamt o =>
      simp only [Lf_norm, List.length_cons]
      refine ⟨ih1.trans (Nat.pow_le_pow_right hD (Nat.le_succ _)), fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := ih2 t ht
      exact ⟨h1.trans (hRp _), by omega⟩
    | det a =>
      simp only [Lf_norm, List.length_cons]
      refine ⟨?_, fun t ht => ?_⟩
      · rw [List.length_flatMap]
        calc ((Lf_norm κ ι' v).map fun t => (match κ a with
              | .inl c => [(c * t.1, t.2.1, t.2.2)]
              | .inr s => match t.2.1 with
                | some y => [(t.1, none, (s, y) :: t.2.2)]
                | none => (List.finRange D).map fun x => (t.1, none, (s, x) :: t.2.2)).length).sum
            ≤ ((Lf_norm κ ι' v).map fun _ => D).sum := by
              apply List.sum_le_sum
              intro t _
              rcases κ a with c | s
              · simp only [List.length_singleton]; omega
              · rcases t.2.1 with _ | y <;> simp <;> omega
          _ = (Lf_norm κ ι' v).length * D := by simp
          _ ≤ D ^ v.length * D := Nat.mul_le_mul_right _ ih1
          _ = D ^ (v.length + 1) := (pow_succ _ _).symm
      · obtain ⟨t₀, ht₀, ht⟩ := List.mem_flatMap.1 ht
        obtain ⟨h1, h2⟩ := ih2 t₀ ht₀
        rcases hk : κ a with c | s
        · simp only [hk, List.mem_singleton] at ht
          subst ht
          refine ⟨?_, by simp; omega⟩
          rw [norm_mul, pow_succ, mul_comm (R ^ v.length)]
          exact mul_le_mul (hκ a c hk) h1 (norm_nonneg _) (by positivity)
        · simp only [hk] at ht
          rcases hy : t₀.2.1 with _ | y
          · simp only [hy, List.mem_map, List.mem_finRange, true_and] at ht
            obtain ⟨x, rfl⟩ := ht
            exact ⟨h1.trans (hRp _), by simp; omega⟩
          · simp only [hy, List.mem_singleton] at ht
            subst ht
            exact ⟨h1.trans (hRp _), by simp; omega⟩
    | proj y =>
      simp only [Lf_norm, List.length_cons]
      refine ⟨?_, fun t ht => ?_⟩
      · rw [List.length_flatMap]
        calc ((Lf_norm κ ι' v).map fun t => (match t.2.1 with
              | some y' => if ι' y = y' then [(t.1, some y', t.2.2)] else []
              | none => [(t.1, some (ι' y), t.2.2)]).length).sum
            ≤ ((Lf_norm κ ι' v).map fun _ => 1).sum := by
              apply List.sum_le_sum
              intro t _
              rcases t.2.1 with _ | y'
              · simp
              · by_cases h : ι' y = y' <;> simp [h]
          _ = (Lf_norm κ ι' v).length := by simp
          _ ≤ D ^ v.length := ih1
          _ ≤ D ^ (v.length + 1) := Nat.pow_le_pow_right hD (Nat.le_succ _)
      · obtain ⟨t₀, ht₀, ht⟩ := List.mem_flatMap.1 ht
        obtain ⟨h1, h2⟩ := ih2 t₀ ht₀
        rcases hy : t₀.2.1 with _ | y'
        · simp only [hy, List.mem_singleton] at ht
          subst ht
          exact ⟨h1.trans (hRp _), by simp; omega⟩
        · simp only [hy] at ht
          split_ifs at ht
          · simp only [List.mem_singleton] at ht
            subst ht
            exact ⟨h1.trans (hRp _), by simp; omega⟩
          · simp at ht

/-- `⟨(Σ X_i) Λ⟩ = Σ ⟨X_i Λ⟩`. -/
private lemma Lf_ntr_sum_mul {ι α : Type*} [Fintype ι] [DecidableEq ι] (l : List α)
    (f : α → Matrix ι ι ℂ) (Λ : Matrix ι ι ℂ) :
    ntr ((l.map f).sum * Λ) = (l.map fun x => ntr (f x * Λ)).sum := by
  induction l with
  | nil => simp [ntr]
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.add_mul]
    rw [← ih]
    simp [ntr, Matrix.trace_add, mul_add]

/-- `‖Σ‖ ≤ Σ ‖·‖` over a list. -/
private lemma Lf_norm_list_sum {α : Type*} (l : List α) (f : α → ℂ) :
    ‖(l.map f).sum‖ ≤ (l.map fun x => ‖f x‖).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- A product `Π (P(s) E_a)` over a list, as the product over `Fin n` of (A.7)
[add_one_more_Lambda]. -/
private lemma Lf_prod_ofFn (D N : ℕ) (P : Bool → Matrix (Idx D N) (Idx D N) ℂ)
    (ps : List (Bool × Fin D)) :
    (ps.map fun q => P q.1 * Ea D N q.2).prod =
      (List.ofFn fun i : Fin ps.length => P (ps.get i).1 * Ea D N (ps.get i).2).prod := by
  conv_lhs => rw [← List.ofFn_get ps, List.map_ofFn]
  rfl

/-- (A.7) [add_one_more_Lambda] for a deterministic word of `𝔐_a` and `E_y`:
`|⟨Π Λ⟩| ≤ D^{len} R^{len} D C ⟨Λ²⟩`, from its normal form. -/
private lemma Lf_A7_word {D N : ℕ} (hD : 1 ≤ D) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (P : Bool → Matrix (Idx D N) (Idx D N) ℂ) (κ : Fin 2 → ℂ ⊕ Bool) (ι' : ℕ → Fin D)
    (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ)
    (L : Matrix (Idx D N) (Idx D N) ℂ)
    (hM : ∀ a, M a = match κ a with | .inl c => c • 1 | .inr s => P s) (R C₇ : ℝ) (hR : 1 ≤ R)
    (hC₇ : 0 ≤ C₇) (hκ : ∀ a c, κ a = .inl c → ‖c‖ ≤ R) (n₀ : ℕ)
    (hA7 : ∀ n, n ≤ n₀ → ∀ (s : Fin n → Bool) (a : Fin n → Fin D) (b : Fin D),
      ‖ntr ((List.ofFn fun i => P (s i) * Ea D N (a i)).prod * Λ * Ea D N b)‖ ≤
        C₇ * avgSq Λ)
    (v : List LoopLetter) (hv : ∀ x ∈ v, Bd_isRes x = false ∧ Bd_isL x = false)
    (hE : ∀ y, LoopLetter.proj y ∈ v → E y = Ea D N (ι' y)) (hlen : v.length ≤ n₀)
    (hσ : 0 ≤ avgSq Λ) :
    ‖ntr ((v.map (Bd_let G M E L)).prod * Λ)‖ ≤
      (D : ℝ) ^ v.length * R ^ v.length * (D * C₇ * avgSq Λ) := by
  rw [Lf_norm_spec P κ ι' G M E L hM v hv hE, Lf_ntr_sum_mul]
  obtain ⟨hl, ht⟩ := Lf_norm_size hD κ ι' R hR hκ v
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hB0 : 0 ≤ C₇ * avgSq Λ := mul_nonneg hC₇ hσ
  have hterm : ∀ t ∈ Lf_norm κ ι' v,
      ‖ntr (Lf_tm P t * Λ)‖ ≤ R ^ v.length * (D * C₇ * avgSq Λ) := by
    intro t htm
    obtain ⟨h1, h2⟩ := ht t htm
    have hps := hA7 t.2.2.length (h2.trans hlen) (fun i => (t.2.2.get i).1)
      (fun i => (t.2.2.get i).2)
    unfold Lf_tm
    rw [Matrix.smul_mul, Bd_ntr_smul, norm_mul, Lf_prod_ofFn D N P t.2.2]
    refine mul_le_mul h1 ?_ (norm_nonneg _) (by positivity)
    set X := (List.ofFn fun i : Fin t.2.2.length =>
      P (t.2.2.get i).1 * Ea D N (t.2.2.get i).2).prod with hX
    rcases t.2.1 with _ | y
    · simp only [Matrix.one_mul]
      have e1 : X * Λ = ∑ b : Fin D, X * Λ * Ea D N b := by
        rw [← Matrix.mul_sum, Lf_Ea_sum, Matrix.mul_one]
      have e2 : ntr (X * Λ) = ∑ b : Fin D, ntr (X * Λ * Ea D N b) := by
        conv_lhs => rw [e1]
        simp [ntr, Matrix.trace_sum, Finset.mul_sum]
      rw [e2]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun b _ => hps b).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    · simp only
      rw [Matrix.mul_assoc, Bd_ntr_comm]
      refine (hps y).trans ?_
      rw [mul_assoc]
      exact le_mul_of_one_le_left hB0 hD1
  refine (Lf_norm_list_sum _ _).trans ?_
  have hsum := List.sum_le_card_nsmul ((Lf_norm κ ι' v).map fun t => ‖ntr (Lf_tm P t * Λ)‖)
    (R ^ v.length * (D * C₇ * avgSq Λ)) (fun x hx => by
      obtain ⟨t, htm, rfl⟩ := List.mem_map.1 hx
      exact hterm t htm)
  refine hsum.trans ?_
  rw [List.length_map, nsmul_eq_mul, ← mul_assoc]
  have hBB : 0 ≤ R ^ v.length * (D * C₇ * avgSq Λ) := by positivity
  have hlD : ((Lf_norm κ ι' v).length : ℝ) ≤ (D : ℝ) ^ v.length := by exact_mod_cast hl
  calc ((Lf_norm κ ι' v).length : ℝ) * R ^ v.length * (D * C₇ * avgSq Λ)
      = ((Lf_norm κ ι' v).length : ℝ) * (R ^ v.length * (D * C₇ * avgSq Λ)) := by ring
    _ ≤ (D : ℝ) ^ v.length * (R ^ v.length * (D * C₇ * avgSq Λ)) :=
        mul_le_mul_of_nonneg_right hlD hBB
    _ = _ := by ring

/-- `⟨(Λ - δ)²⟩ = ⟨Λ²⟩ + δ²` for `⟨Λ⟩ = 0`. -/
private lemma Lf_avgSq_shift {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (h0 : ntr Λ = 0) (δ : ℝ) :
    avgSq (Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ)) = avgSq Λ + δ ^ 2 := by
  unfold avgSq
  have h1 : ntr ((Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ)) * (Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ))) =
      ntr (Λ * Λ) - 2 * (δ : ℂ) * ntr Λ + (δ : ℂ) ^ 2 * ntr (1 : Matrix ι ι ℂ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, ntr, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [h1, h0, Tay_ntr_one]
  simp only [mul_zero, sub_zero, mul_one]
  rw [Complex.add_re]
  congr 1
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- `⟨Λ⟩ = 0` for traceless blocks. -/
private lemma Lf_ntr_zero (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (htr : ∀ a : Fin D, ntr (Ea D N a * Λ) = 0) : ntr Λ = 0 := by
  have h1 : Λ = ∑ a : Fin D, Ea D N a * Λ := by rw [← Finset.sum_mul, Lf_Ea_sum, Matrix.one_mul]
  have e2 : ntr (∑ a : Fin D, Ea D N a * Λ) = ∑ a : Fin D, ntr (Ea D N a * Λ) := by
    simp [ntr, Matrix.trace_sum, Finset.mul_sum]
  rw [h1, e2]
  simp [htr]

/-! ## The loops with `Λ̃` of a leaf -/

/-- A loop `⟨𝔐_b E_x 𝔐_a Λ̃⟩` with `a ≠ b`, the form of (5.5)
[regular_estimate_localized_eigenvector] and (5.22) [regular_estimate_localized_eigenvalue]. -/
private def Lf_rform : List LoopLetter → Bool
  | [.det b, .proj _, .det a, .lamt _] => a != b
  | _ => false

/-- The data of a slot used for the loops with `Λ̃`: `‖𝔐_a‖ ≤ 5/4`, `|δ| ≤ K⟨Λ²⟩`, `⟨Λ²⟩ ≤ 1`,
the gain (5.5) [regular_estimate_localized_eigenvector], (5.22)
[regular_estimate_localized_eigenvalue], and (A.7) [add_one_more_Lambda] for the matrices `𝔐_a`
(scalars or `P(s)`). -/
private structure Lf_SF {D N : ℕ} (e : LoopEnv D N) (K Kg C₇ R : ℝ) (n₀ : ℕ) : Prop where
  pos : 1 ≤ D ∧ 1 ≤ N
  hM : ∀ a, opNorm (e.M a) ≤ 5 / 4
  hδ : |e.δ| ≤ K * avgSq (lam D N e.A)
  hσ1 : avgSq (lam D N e.A) ≤ 1
  hgain : ∀ (a b : Fin 2) (x : Fin D), a ≠ b →
    ‖ntr (e.M a * e.Lt * e.M b * Ea D N x)‖ ≤
      Kg * ((mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im * avgSq (lam D N e.A))
  ha7 : ∃ (P : Bool → Matrix (Idx D N) (Idx D N) ℂ) (κ : Fin 2 → ℂ ⊕ Bool),
    (∀ a, e.M a = match κ a with | .inl c => c • 1 | .inr s => P s) ∧
    (∀ a c, κ a = .inl c → ‖c‖ ≤ R) ∧
    ∀ n, n ≤ n₀ → ∀ (s : Fin n → Bool) (a : Fin n → Fin D) (b : Fin D),
      ‖ntr ((List.ofFn fun i => P (s i) * Ea D N (a i)).prod * lam D N e.A * Ea D N b)‖ ≤
        C₇ * avgSq (lam D N e.A)

/-- The bound of a loop with `Λ̃` and no resolvent: `(5/4)^{2 len} (1 + K²) ⟨Λ²⟩` with two `Λ̃`,
`K_g Im m ⟨Λ²⟩` for `⟨𝔐_b E_x 𝔐_a Λ̃⟩`, and the bound of (A.7) [add_one_more_Lambda]
otherwise. -/
private def Lf_beta (D : ℕ) (K Kg C₇ R σ g : ℝ) (w : List LoopLetter) : ℝ :=
  if w.countP Bd_isL = 2 then (5 / 4 : ℝ) ^ (2 * w.length) * (1 + K ^ 2) * σ
  else if Lf_rform w then Kg * g * σ
  else ((D : ℝ) ^ w.length * R ^ w.length * (D * C₇) + |K| * (5 / 4 : ℝ) ^ w.length) * σ

/-- A product of letters other than resolvents and `Λ̃` has norm `≤ (5/4)^{len}`. -/
private lemma Lf_det_norm {D N : ℕ} (e : LoopEnv D N) (hM : ∀ a, opNorm (e.M a) ≤ 5 / 4)
    {nb : ℕ} (ι : Fin nb → Fin D) (G : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (v : List LoopLetter) (hv : ∀ x ∈ v, Bd_isRes x = false ∧ Bd_isL x = false) :
    opNorm ((v.map (Bd_let G e.M (e.E ι) e.Lt)).prod) ≤ (5 / 4 : ℝ) ^ v.length := by
  refine Bd_prod_norm v _ (5 / 4) (by norm_num) fun x hx => ?_
  have := hv x hx
  cases x with
  | res a => simp [Bd_isRes] at this
  | lamt o => simp [Bd_isL] at this
  | det a => exact hM a
  | proj y => exact (Bd_opNorm_E e ι y).trans (by norm_num)

/-- The letters of a word with no resolvent and no `Λ̃`. -/
private lemma Lf_noLR {v : List LoopLetter} (hr : v.countP Bd_isRes = 0)
    (hl : v.countP Bd_isL = 0) : ∀ x ∈ v, Bd_isRes x = false ∧ Bd_isL x = false := by
  intro x hx
  exact ⟨by simpa using List.countP_eq_zero.1 hr x hx, by simpa using List.countP_eq_zero.1 hl x hx⟩

/-- The shape of a loop `⟨𝔐_b E_x 𝔐_a Λ̃⟩`. -/
private lemma Lf_rform_eq {w : List LoopLetter} (h : Lf_rform w = true) :
    ∃ (b : Fin 2) (x : ℕ) (a o : Fin 2), w = [.det b, .proj x, .det a, .lamt o] ∧ a ≠ b := by
  unfold Lf_rform at h
  split at h
  · rename_i b x a o
    exact ⟨b, x, a, o, rfl, by simpa using h⟩
  · simp at h

/-- A split word `a y b` with `y` a `Λ̃`: the counts of the two sides. -/
private lemma Lf_split_counts {a rest : List LoopLetter} {y : LoopLetter} (hy : Bd_isL y = true)
    (hres : (a ++ y :: rest).countP Bd_isRes = 0) :
    a.countP Bd_isRes = 0 ∧ rest.countP Bd_isRes = 0 ∧
      (a ++ y :: rest).countP Bd_isL = a.countP Bd_isL + rest.countP Bd_isL + 1 := by
  have hyr : Bd_isRes y = false := Bd_isL_notRes y hy
  rw [List.countP_append, List.countP_cons, if_neg (by simp [hyr])] at hres
  rw [List.countP_append, List.countP_cons, if_pos hy]
  omega

/-- The bound `Lf_beta` of a loop with `Λ̃` and no resolvent. -/
private lemma Lf_lamloop {D N : ℕ} (e : LoopEnv D N) (K Kg C₇ R : ℝ) (n₀ : ℕ)
    (hK : 0 ≤ K) (hR : 1 ≤ R) (hC₇ : 0 ≤ C₇) (hS : Lf_SF e K Kg C₇ R n₀) {nb : ℕ}
    (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ) (w : List LoopLetter)
    (hres : w.countP Bd_isRes = 0) (hL1 : 1 ≤ w.countP Bd_isL) (hL2 : w.countP Bd_isL ≤ 2)
    (hproj : ∀ y, LoopLetter.proj y ∈ w → y < nb) (hlen : w.length ≤ n₀) :
    ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤
      Lf_beta D K Kg C₇ R (avgSq (lam D N e.A)) (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im
        w := by
  obtain ⟨⟨hD, hN⟩, hM, hδ, hσ1, hgain, P, κ, hMk, hκ, hA7⟩ := hS
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set σ := avgSq (lam D N e.A) with hσdef
  have hσ0 : 0 ≤ σ := Bd_avgSq_nonneg _ (lam_isHermitian D N e.A)
  have htr := Tay_lam_blockTraceless D N e.A
  have hntr := Lf_ntr_zero D N (lam D N e.A) htr
  have h54 : (1 : ℝ) ≤ 5 / 4 := by norm_num
  unfold Lf_beta
  by_cases h2 : w.countP Bd_isL = 2
  · -- two `Λ̃`: (A.6)-type bound `|⟨X Λ̃ Y Λ̃⟩| ≤ ‖X‖ ‖Y‖ ⟨Λ̃²⟩`
    rw [if_pos h2, Bd_wordMat_eq]
    obtain ⟨a, y₁, rest, rfl, ha, hy₁⟩ := Bd_split Bd_isL w (by omega)
    obtain ⟨har, hrr, hcnt⟩ := Lf_split_counts hy₁ hres
    have hr1 : 0 < rest.countP Bd_isL := by omega
    have hr1' : rest.countP Bd_isL = 1 := by omega
    obtain ⟨c, y₂, d, rfl, hc, hy₂⟩ := Bd_split Bd_isL rest hr1
    obtain ⟨hcr, hdr, hcnt2⟩ := Lf_split_counts hy₂ hrr
    have hd : d.countP Bd_isL = 0 := by omega
    rw [Bd_mat_two _ _ _ _ a c d y₁ y₂ hy₁ hy₂]
    have hX := Lf_det_norm e hM ι (e.G h) (d ++ a)
      (Lf_noLR (by rw [List.countP_append]; omega) (by rw [List.countP_append]; omega))
    have hY := Lf_det_norm e hM ι (e.G h) c (Lf_noLR hcr hc)
    have hLt : avgSq e.Lt = σ + e.δ ^ 2 := by
      unfold LoopEnv.Lt
      exact Lf_avgSq_shift _ hntr e.δ
    have hδ2 : e.δ ^ 2 ≤ K ^ 2 * σ := by
      have h1 : |e.δ| ^ 2 ≤ (K * σ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ 2
      rw [sq_abs] at h1
      have h3 : K ^ 2 * σ * σ ≤ K ^ 2 * σ * 1 := mul_le_mul_of_nonneg_left hσ1 (by positivity)
      nlinarith
    set len := (a ++ y₁ :: (c ++ y₂ :: d)).length with hlen'
    have hl1 : (d ++ a).length ≤ len := by simp [hlen']; omega
    have hl2 : c.length ≤ len := by simp [hlen']; omega
    have hX' := hX.trans (pow_le_pow_right₀ h54 hl1)
    have hY' := hY.trans (pow_le_pow_right₀ h54 hl2)
    have hLt' : avgSq e.Lt ≤ (1 + K ^ 2) * σ := by rw [hLt]; nlinarith
    calc _ ≤ _ := Tay_BL (Rch_Lt_herm e) _ _
      _ ≤ (5 / 4 : ℝ) ^ len * (5 / 4 : ℝ) ^ len * ((1 + K ^ 2) * σ) := by
          have h0X := Bd_opNorm_nonneg
            ((List.map (Bd_let (e.G h) e.M (e.E ι) e.Lt) (d ++ a)).prod)
          have h0Y := Bd_opNorm_nonneg ((List.map (Bd_let (e.G h) e.M (e.E ι) e.Lt) c).prod)
          have h0L : 0 ≤ avgSq e.Lt := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
          gcongr
      _ = _ := by rw [show 2 * len = len + len by ring, pow_add]; ring
  · rw [if_neg h2]
    by_cases hrf : Lf_rform w = true
    · -- the gain (5.5), (5.22)
      rw [if_pos hrf]
      obtain ⟨b, x, a, o, rfl, hab⟩ := Lf_rform_eq hrf
      have hx : x < nb := hproj x (by simp)
      have hE : e.E ι x = Ea D N (ι ⟨x, hx⟩) := by simp [LoopEnv.E, hx]
      have e1 : loopWordMat (e.G h) e.M (e.E ι) e.Lt [.det b, .proj x, .det a, .lamt o] =
          (e.M b * Ea D N (ι ⟨x, hx⟩)) * (e.M a * e.Lt) := by
        simp only [loopWordMat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          Matrix.mul_one, hE, Matrix.mul_assoc]
      rw [e1, Bd_ntr_comm]
      have := hgain a b (ι ⟨x, hx⟩) hab
      simp only [Matrix.mul_assoc] at this ⊢
      rw [mul_assoc Kg]
      exact this
    · -- (A.7)
      rw [if_neg hrf, Bd_wordMat_eq]
      obtain ⟨a, y₁, rest, rfl, ha, hy₁⟩ := Bd_split Bd_isL w (by omega)
      obtain ⟨har, hrr, hcnt⟩ := Lf_split_counts hy₁ hres
      have hrl : rest.countP Bd_isL = 0 := by omega
      rw [Bd_mat_one _ _ _ _ a rest y₁ hy₁]
      set v := rest ++ a with hv
      have hvl : ∀ x ∈ v, Bd_isRes x = false ∧ Bd_isL x = false :=
        Lf_noLR (by rw [hv, List.countP_append]; omega) (by rw [hv, List.countP_append]; omega)
      set ι' : ℕ → Fin D := fun y => if hy : y < nb then ι ⟨y, hy⟩ else ⟨0, by omega⟩ with hι'
      have hE : ∀ y, LoopLetter.proj y ∈ v → e.E ι y = Ea D N (ι' y) := by
        intro y hy
        have hy' : y < nb := hproj y (by
          rw [hv] at hy
          rcases List.mem_append.1 hy with h | h <;> simp [h])
        simp [LoopEnv.E, hι', hy']
      have hvlen : v.length ≤ (a ++ y₁ :: rest).length := by simp [hv]; omega
      have hA := Lf_A7_word hD (lam D N e.A) P κ ι' (e.G h) e.M (e.E ι) e.Lt hMk R C₇ hR hC₇
        hκ n₀ hA7 v hvl hE (hvlen.trans hlen) hσ0
      have hX := Lf_det_norm e hM ι (e.G h) v hvl
      have e1 : ntr ((v.map (Bd_let (e.G h) e.M (e.E ι) e.Lt)).prod * e.Lt) =
          ntr ((v.map (Bd_let (e.G h) e.M (e.E ι) e.Lt)).prod * lam D N e.A) -
            (e.δ : ℂ) * ntr ((v.map (Bd_let (e.G h) e.M (e.E ι) e.Lt)).prod) := by
        unfold LoopEnv.Lt
        rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
        simp [ntr, Matrix.trace_sub, Matrix.trace_smul]
        ring
      rw [e1]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have hDp : (D : ℝ) ^ v.length ≤ (D : ℝ) ^ (a ++ y₁ :: rest).length :=
        pow_le_pow_right₀ hD1 hvlen
      have hRp : R ^ v.length ≤ R ^ (a ++ y₁ :: rest).length := pow_le_pow_right₀ hR hvlen
      have h5p : (5 / 4 : ℝ) ^ v.length ≤ (5 / 4 : ℝ) ^ (a ++ y₁ :: rest).length :=
        pow_le_pow_right₀ h54 hvlen
      have hntrX := (Bd_ntr_le _).trans hX
      have hδ' : |e.δ| ≤ |K| * σ := hδ.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hσ0)
      calc _ ≤ (D : ℝ) ^ v.length * R ^ v.length * (D * C₇ * σ) + |K| * σ *
            (5 / 4 : ℝ) ^ v.length :=
            add_le_add hA (mul_le_mul hδ' hntrX (norm_nonneg _) (by positivity))
        _ ≤ (D : ℝ) ^ (a ++ y₁ :: rest).length * R ^ (a ++ y₁ :: rest).length * (D * C₇ * σ) +
            |K| * σ * (5 / 4 : ℝ) ^ (a ++ y₁ :: rest).length := by
            gcongr
        _ = _ := by ring

/-! ## The slots of Lemmas 5.2 and 5.4 -/

/-- `𝔯(k) = k` for `2k ≤ DN + 1`. -/
private lemma Lf_rk_eq (D N k : ℕ) (hk : 2 * k ≤ D * N + 1) : rk D N k = k := by
  unfold rk
  congr 1
  omega

/-- `Im m(z) ≤ C √(κ + η)` on both sides of the spectrum, by (A.1) [square_root_density]. -/
private lemma Lf_im_sqrt (C : ℝ) (hC : 0 < C) (κ η m : ℝ) (hκ : 0 ≤ κ) (hη : 0 < η)
    (h : (m ≤ C * Real.sqrt (κ + η)) ∨ (m ≤ C * (η / Real.sqrt (κ + η)))) :
    m ≤ C * Real.sqrt (κ + η) := by
  rcases h with h | h
  · exact h
  · refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have hs : 0 < Real.sqrt (κ + η) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hs, Real.mul_self_sqrt (by linarith)]
    linarith

/-- The upper bound `Im m(z_t) ≤ C N^{-1/3+ε/2} 𝔯(k)^{1/3}` at `z_t = γ_k(t) + iη` of (5.1)
[eq:z1] and (5.20) [eq:z1t], from (A.1) [square_root_density] and (2.21)
[eq:kappa_gamma_k]. -/
private lemma Lf_im_bound (D : ℕ) (hD : 2 ≤ D) (δA ε : ℝ) (hδA : 0 < δA) (hε : 0 < ε)
    (hε'' : ε ≤ 1 / 3) :
    ∃ CU : ℝ, 0 < CU ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖zOne ((t : ℂ) • lam D N A) k ε‖ ≤ (ε / 2)⁻¹ →
        (mSol ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε)).im ≤
          CU * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cs, hCs, hsq⟩ := square_root_density (ε / 2) (by positivity)
  obtain ⟨ck, Ck, hck, hCk, N₁, hN₁⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨N₂, hN₂⟩ := Bd_small δA (1 / 20) hδA (by norm_num)
  refine ⟨Cs * Real.sqrt (Ck + 1), by positivity, max (max N₁ N₂) 1, ?_⟩
  intro N hN A hA k hk hkN t ht hz
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hDN : k ≤ D * N := by
    have : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hN1)
    omega
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hA0 : 0 ≤ opNorm A := Bd_opNorm_nonneg A
  have htA : opNorm ((t : ℂ) • A) ≤ (N : ℝ) ^ (-δA) := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * opNorm A ≤ 1 * opNorm A := mul_le_mul_of_nonneg_right ht1 hA0
      _ ≤ _ := by rw [one_mul]; exact hA
  obtain ⟨-, hκu, -, -⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    ((t : ℂ) • A) htA k hk hDN
  rw [← lam_smul] at hκu
  set Λ := (t : ℂ) • lam D N A with hΛ
  have hΛh : Λ.IsHermitian := Bd_lamc_herm D N A t
  have hΛn : opNorm Λ ≤ 1 / 10 := by
    have h1 := opNorm_lam_le D N ((t : ℂ) • A)
    rw [← lam_smul] at h1
    have h2 := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
    linarith
  set z := zOne Λ k ε with hzdef
  have hη : 0 < etaK D N k ε := by
    have : (0 : ℝ) < rk D N k := by rw [Lf_rk_eq D N k hkN]; exact_mod_cast hk
    unfold etaK
    positivity
  have hzim : z.im = etaK D N k ε := by simp [hzdef, zOne]
  have hzre : z.re = quant (rho Λ) (D * N) k := by simp [hzdef, zOne]
  have hzpos : 0 < z.im := by rw [hzim]; exact hη
  obtain ⟨-, hm⟩ := hsq (Idx D N) Λ hΛh hΛn
  obtain ⟨hin, hout⟩ := hm z hz hzpos
  have hκ0 : 0 ≤ kappa Λ z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hmain : (mSol Λ z).im ≤ Cs * Real.sqrt (kappa Λ z.re + z.im) := by
    refine Lf_im_sqrt Cs hCs _ _ _ hκ0 hzpos ?_
    by_cases hre : z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ)
    · exact Or.inl (hin hre).2
    · exact Or.inr (hout hre).2
  refine hmain.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hCs.le
  have hr : rk D N k = k := Lf_rk_eq D N k hkN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hκb : kappa Λ z.re ≤ Ck * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
    refine (min_le_left _ _).trans ?_
    rw [hzre]
    have h0 : 0 ≤ Eplus Λ - quant (rho Λ) (D * N) k := by
      have := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
        ((t : ℂ) • A) htA k hk hDN
      rw [← lam_smul] at this
      exact le_trans (by positivity) this.1
    rw [abs_of_nonneg h0]
    exact hκu
  -- `κ + η ≤ (C_k + 1) N^{-2/3+ε} k^{2/3}`
  have hNε : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1r hε.le
  have hk23 : (1 : ℝ) ≤ (k : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
  have hkm13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by norm_num)
  set X : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (2 / 3 : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hNsplit : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) = (N : ℝ) ^ (-(2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]
  have h1 : (k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ X := by
    rw [hX, hNsplit]
    have : 0 ≤ (k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    nlinarith
  have h2 : z.im ≤ X := by
    rw [hzim, hX]
    unfold etaK
    rw [hr]
    have : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) := by positivity
    have h3 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (k : ℝ) ^ (2 / 3 : ℝ) := le_trans hkm13 hk23
    exact mul_le_mul_of_nonneg_left h3 this
  have hsum : kappa Λ z.re + z.im ≤ (Ck + 1) * X := by
    have := mul_le_mul_of_nonneg_left h1 hCk.le
    nlinarith
  have hsX : Real.sqrt X = (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) := by
    rw [hX, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hNpos.le, ← Real.rpow_mul (by positivity), hr]
    congr 1 <;> [congr 1; congr 1] <;> ring
  calc Real.sqrt (kappa Λ z.re + z.im) ≤ Real.sqrt ((Ck + 1) * X) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Ck + 1) * Real.sqrt X := Real.sqrt_mul (by linarith) _
    _ = _ := by rw [hsX]

/-- The constant of (A.7) [add_one_more_Lambda] for all products of at most `n₀` factors. -/
private lemma Lf_A7_const (τ : ℝ) (hτ : 0 < τ) (n₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, n ≤ n₀ → ∀ (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ), 1 ≤ N →
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → (∀ a : Fin D, ntr (Ea D N a * Λ) = 0) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      ∀ (s : Fin n → Bool) (a : Fin n → Fin D) (b : Fin D),
        ‖ntr ((List.ofFn fun i : Fin n =>
            (if s i then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i)).prod * Λ * Ea D N b)‖ ≤
          C * avgSq Λ := by
  choose C hC0 hC using fun n => add_one_more_Lambda τ hτ n
  refine ⟨∑ n ∈ Finset.range (n₀ + 1), C n, Finset.sum_nonneg fun n _ => (hC0 n).le, ?_⟩
  intro n hn D N Λ hN hΛ hℓ htr z hz hzi s a b
  refine (hC n D N Λ hN hΛ hℓ htr z hz hzi s a b).trans ?_
  have hσ : 0 ≤ avgSq Λ := Bd_avgSq_nonneg Λ hΛ
  refine mul_le_mul_of_nonneg_right ?_ hσ
  exact Finset.single_le_sum (fun i _ => (hC0 i).le) (Finset.mem_range.2 (by omega))

/-- `MExt = MSol` on the upper half plane. -/
private lemma Lf_ext_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) {z : ℂ}
    (hz : 0 < z.im) : MExt Λ z = MSol Λ z := by
  have h : mExt Λ z = mSol Λ z := by unfold mExt; simp [hz]
  unfold MExt MSol
  rw [h]

/-- A scalar matrix `c • 1` of norm `≤ R` has `‖c‖ ≤ R`. -/
private lemma Lf_scalar_norm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (c : ℂ)
    (R : ℝ) (h : opNorm (c • (1 : Matrix ι ι ℂ)) ≤ R) : ‖c‖ ≤ R := by
  obtain ⟨p⟩ := ‹Nonempty ι›
  have := Tay_entry_le (c • (1 : Matrix ι ι ℂ)) p p
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  exact this.trans h

/-- The slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law]: the admissibility of `loop_env_admissible`, the data
`Lf_SF` of the loops with `Λ̃`, and `Im m_a ≤ C N^{-1/3+ε/2} 𝔯(k)^{1/3}`. -/
private lemma Lf_slots (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (n₀ : ℕ) :
    ∃ c₀ K Kg C₇ CU : ℝ, 0 < c₀ ∧ 0 ≤ K ∧ 0 ≤ Kg ∧ 0 ≤ C₇ ∧ 0 < CU ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        2 * opNorm e.A ≤ 1 / 10 ∧ (∀ a, |e.c a| ≤ 1) ∧
        (∀ a, e.z a ∈ specDom (ε / 2) N ∧ 0 < (e.z a).im ∧ (e.z a).im = etaK D N k ε ∧
          c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) ∧
        |e.δ| ≤ K * avgSq (lam D N e.A) ∧ Lf_SF e K Kg C₇ (5 / 4) n₀ ∧ e.A = A ∧
        ∀ a, (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤
          CU * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) := by
  obtain ⟨c₀, K, hc₀, hK, N₁, hN₁⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨Kg, hKg, N₂, hN₂⟩ := loop_env_gain D hD δA εA ε hδA hεA hε hε'
  obtain ⟨C₇, hC₇, hA7c⟩ := Lf_A7_const (ε / 2) (by positivity) n₀
  obtain ⟨CU, hCU, N₃, hN₃⟩ := Lf_im_bound D hD δA ε hδA hε hε''
  obtain ⟨Cr, hCr, N₄, hN₄⟩ := regular_estimate_localized_eigenvector D hD δA εA ε hδA hεA hε hε'
  obtain ⟨C₆, hC₆, hmsc⟩ := eq_msc (ε / 2) (by positivity)
  refine ⟨c₀, K, Kg, C₇, max 1 Cr * CU, hc₀, hK, hKg.le, hC₇, by positivity,
    max (max N₁ N₂) (max (max N₃ N₄) 1), ?_⟩
  intro N hN A hA k hk hkN hhs e he
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hN
  have hNd : N₄ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hN
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hD0 : 0 < D := by omega
  have hkDN : k ≤ D * N := by
    have : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hN1)
    omega
  obtain ⟨hA2, hc, hz, hδ⟩ := hN₁ N hNa A hA k hk hkN hhs e he
  have hgain := hN₂ N hNb A hA k hk hkN hhs e he
  have heA : e.A = A := by rcases he with ⟨s, rfl⟩ | ⟨t, -, s, rfl⟩ <;> rfl
  have hA0 := Bd_opNorm_nonneg e.A
  have hlamn : ∀ a, opNorm ((e.c a : ℂ) • lam D N e.A) ≤ 1 / 10 := by
    intro a
    refine (Bd_lamc_norm D N e.A (e.c a)).trans ?_
    have := hc a
    nlinarith [abs_nonneg (e.c a)]
  have hM : ∀ a, opNorm (e.M a) ≤ 5 / 4 := by
    intro a
    unfold LoopEnv.M
    refine Bd_MExt_norm _ (Bd_lamc_herm D N e.A (e.c a)) (hlamn a) _ ?_
    have := (hz a).2.1
    by_cases hs : e.s a
    · simp only [hs, ite_true, Complex.star_def, Complex.conj_im]
      linarith
    · simp only [hs, Bool.false_eq_true, ite_false]
      linarith
  have hσ1 : avgSq (lam D N e.A) ≤ 1 := by
    have h1 := Bd_avgSq_le (lam D N e.A)
    have h2 := opNorm_lam_le D N e.A
    have h3 := Bd_opNorm_nonneg (lam D N e.A)
    nlinarith
  have hlh : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hln : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    rw [heA] at hA2
    linarith
  have htr := Tay_lam_blockTraceless D N A
  have hσ0 : 0 ≤ avgSq (lam D N A) := Bd_avgSq_nonneg _ hlh
  have hmaxU : CU ≤ max 1 Cr * CU := le_mul_of_one_le_left hCU.le (le_max_left _ _)
  have hrk0 : 0 ≤ rk D N k := by unfold rk; positivity
  have hX0 : 0 ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hrk0 _)
  refine ⟨hA2, hc, hz, hδ, ⟨⟨by omega, hN1⟩, hM, hδ, hσ1, hgain, ?_⟩, heA, ?_⟩
  · rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
    · -- the slots of Lemma 5.2
      set z₁ := zOne (lam D N A) k ε with hz₁
      set z₀ := z₁ - (shiftEv (lam D N A) z₁ : ℂ) with hz₀
      have hz0pos : 0 < z₀.im := by
        have := (hz 0).2.1
        simpa [evecEnv, hz₀, hz₁] using this
      have hz1pos : 0 < z₁.im := by
        have := (hz 1).2.1
        simpa [evecEnv, hz₁] using this
      have hz1n : ‖z₁‖ ≤ (ε / 2)⁻¹ := by
        have := (hz 1).1.1
        simpa [evecEnv, hz₁] using this
      have hMk : ∀ a, (evecEnv D N A k ε s).M a =
          match (![Sum.inl (if s 0 then star (msc z₀) else msc z₀), Sum.inr (s 1)] :
            Fin 2 → ℂ ⊕ Bool) a with
          | .inl c => c • 1
          | .inr b => (fun b => if b then (MSol (lam D N A) z₁)ᴴ else MSol (lam D N A) z₁) b := by
        intro a
        fin_cases a
        · exact Rch_slot_zero D N hD0 (by omega) A z₀ hz0pos (s 0)
        · have h2 := Rch_flag (lam D N A) hlh z₁ hz1pos.ne' (s 1)
          rw [Lf_ext_eq _ hz1pos] at h2
          have h1 : (((1 : ℝ) : ℂ) • lam D N A) = lam D N A := by simp
          change MExt (((1 : ℝ) : ℂ) • lam D N A) (if s 1 then star z₁ else z₁) = _
          rw [h1]
          exact h2
      refine ⟨fun b => if b then (MSol (lam D N A) z₁)ᴴ else MSol (lam D N A) z₁,
        ![Sum.inl (if s 0 then star (msc z₀) else msc z₀), Sum.inr (s 1)], hMk, ?_, ?_⟩
      · intro a c hac
        have h2 := hM a
        rw [hMk a, hac] at h2
        exact Lf_scalar_norm _ _ h2
      · intro n hn s' a b
        exact hA7c n hn D N (lam D N A) hN1 hlh hln htr z₁ hz1n hz1pos s' a b
    · -- the slots of Lemma 5.4
      set zt := zOne ((t : ℂ) • lam D N A) k ε with hzt
      have hztpos : 0 < zt.im := by
        have := (hz 0).2.1
        simpa [evalEnv, hzt] using this
      have hztn : ‖zt‖ ≤ (ε / 2)⁻¹ := by
        have := (hz 0).1.1
        simpa [evalEnv, hzt] using this
      have htl : ((t : ℂ) • lam D N A).IsHermitian := Bd_lamc_herm D N A t
      have htn : opNorm ((t : ℂ) • lam D N A) ≤ 1 / 10 := by
        have := hlamn 0
        simpa [evalEnv] using this
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · -- `t = 0`
        subst h0
        have hMk : ∀ a, (evalEnv D N A k ε 0 s).M a =
            match (fun a => Sum.inl (if s a then star (msc zt) else msc zt) :
              Fin 2 → ℂ ⊕ Bool) a with
            | .inl c => c • 1
            | .inr b => (fun _ => (0 : Matrix (Idx D N) (Idx D N) ℂ)) b := by
          intro a
          fin_cases a
          · exact Rch_slot_zero D N hD0 (by omega) A zt hztpos (s 0)
          · exact Rch_slot_zero D N hD0 (by omega) A zt hztpos (s 1)
        refine ⟨fun _ => 0, fun a => Sum.inl (if s a then star (msc zt) else msc zt), hMk,
          ?_, ?_⟩
        · intro a c hac
          have h2 := hM a
          rw [hMk a, hac] at h2
          exact Lf_scalar_norm _ _ h2
        · intro n hn s' a b
          simp only [show (evalEnv D N A k ε 0 s).A = A from rfl]
          rcases Nat.eq_zero_or_pos n with rfl | hn1
          · simp only [List.ofFn_zero, List.prod_nil, Matrix.one_mul]
            rw [Bd_ntr_comm, htr b, norm_zero]
            exact mul_nonneg hC₇ hσ0
          · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            simp only [List.ofFn_succ, List.prod_cons, Matrix.zero_mul]
            simp only [ntr, Matrix.trace_zero, mul_zero, norm_zero]
            exact mul_nonneg hC₇ hσ0
      · -- `t > 0`
        refine ⟨fun b => if b then (MSol ((t : ℂ) • lam D N A) zt)ᴴ else
          MSol ((t : ℂ) • lam D N A) zt, fun a => Sum.inr (s a), ?_, ?_, ?_⟩
        · intro a
          have h2 := Rch_flag ((t : ℂ) • lam D N A) htl zt hztpos.ne' (s a)
          rw [Lf_ext_eq _ hztpos] at h2
          fin_cases a <;> exact h2
        · intro a c hac
          simp at hac
        · intro n hn s' a b
          have htr' : ∀ a : Fin D, ntr (Ea D N a * ((t : ℂ) • lam D N A)) = 0 := by
            intro a
            rw [Matrix.mul_smul, Bd_ntr_smul, htr a, mul_zero]
          have h1 := hA7c n hn D N ((t : ℂ) • lam D N A) hN1 htl htn htr' zt hztn hztpos s' a b
          have hav : avgSq ((t : ℂ) • lam D N A) = t ^ 2 * avgSq (lam D N A) := by
            unfold avgSq
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Bd_ntr_smul]
            rw [show ((t : ℂ) * (t : ℂ)) = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring]
            rw [Complex.re_ofReal_mul]
          rw [hav, Matrix.mul_smul, Matrix.smul_mul, Bd_ntr_smul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hpos] at h1
          have h3 : t * ‖ntr ((List.ofFn fun i => (if s' i then
              (MSol ((t : ℂ) • lam D N A) zt)ᴴ else MSol ((t : ℂ) • lam D N A) zt) *
              Ea D N (a i)).prod * lam D N A * Ea D N b)‖ ≤ t * (C₇ * avgSq (lam D N A)) := by
            have : C₇ * (t ^ 2 * avgSq (lam D N A)) ≤ t * (C₇ * avgSq (lam D N A)) := by
              have : t ^ 2 ≤ t := by nlinarith [ht.2]
              nlinarith [mul_nonneg hC₇ hσ0]
            linarith
          exact le_of_mul_le_mul_left h3 hpos
  · intro a
    rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
    · set z₁ := zOne (lam D N A) k ε with hz₁
      have hz1pos : 0 < z₁.im := by
        have := (hz 1).2.1
        simpa [evecEnv, hz₁] using this
      have hz1n : ‖zOne (((1 : ℝ) : ℂ) • lam D N A) k ε‖ ≤ (ε / 2)⁻¹ := by
        have := (hz 1).1.1
        simpa [evecEnv, hz₁] using this
      have hU1 := hN₃ N hNc A hA k hk hkN 1 ⟨zero_le_one, le_rfl⟩ hz1n
      simp only [Complex.ofReal_one, one_smul] at hU1
      fin_cases a
      · -- `Im m_sc(z₀) ≤ C Im m(z₁)`
        obtain ⟨hr1, -, -, -⟩ := hN₄ N hNd A hA k hk hkDN hhs
        set z₀ := z₁ - (shiftEv (lam D N A) z₁ : ℂ) with hz₀
        have hz0pos : 0 < z₀.im := by simpa [hz₀] using hz1pos
        have hz0n : ‖z₀‖ ≤ (ε / 2)⁻¹ := by
          have := (hz 0).1.1
          simpa [evecEnv, hz₀, hz₁] using this
        have hm0 : mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z₀ = msc z₀ := by
          have h := (hmsc (Idx D N) 0 (by simp [Matrix.IsHermitian]) (by
            have : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by unfold opNorm; simp
            rw [this]; norm_num) z₀ hz0n hz0pos).1
          have : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by unfold opNorm; simp
          rw [this, Real.sqrt_zero, mul_zero] at h
          exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
        have hext : mExt (lam D N A) z₁ = mSol (lam D N A) z₁ := by unfold mExt; simp [hz1pos]
        rw [hext] at hr1
        have e0 : (mSol (((evecEnv D N A k ε s).c 0 : ℂ) • lam D N (evecEnv D N A k ε s).A)
            ((evecEnv D N A k ε s).z 0)).im = (msc z₀).im := by
          rw [← hm0]
          simp [evecEnv, hz₀, hz₁]
        simp only [Fin.zero_eta, Fin.isValue]
        rw [e0]
        have hCr' : 0 < Cr⁻¹ := inv_pos.2 hCr
        have h1 : (msc z₀).im ≤ Cr * (mSol (lam D N A) z₁).im := by
          rw [inv_mul_le_iff₀ hCr] at hr1
          exact hr1
        calc (msc z₀).im ≤ Cr * (mSol (lam D N A) z₁).im := h1
          _ ≤ max 1 Cr * (CU * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ))) := by
              have hm1 : 0 ≤ (mSol (lam D N A) z₁).im :=
                (mSol_spec _ hlh _ hz1pos).1.le
              exact mul_le_mul (le_max_right _ _) hU1 hm1 (by positivity)
          _ = _ := by ring
      · simp only [Fin.mk_one, Fin.isValue]
        have e1 : (mSol (((evecEnv D N A k ε s).c 1 : ℂ) • lam D N (evecEnv D N A k ε s).A)
            ((evecEnv D N A k ε s).z 1)).im = (mSol (lam D N A) z₁).im := by
          simp [evecEnv, hz₁]
        rw [e1]
        exact hU1.trans (mul_le_mul_of_nonneg_right hmaxU hX0)
    · have hztn : ‖zOne ((t : ℂ) • lam D N A) k ε‖ ≤ (ε / 2)⁻¹ := by
        have := (hz 0).1.1
        simpa [evalEnv] using this
      have hU := hN₃ N hNc A hA k hk hkN t ht hztn
      have e1 : (mSol (((evalEnv D N A k ε t s).c a : ℂ) • lam D N (evalEnv D N A k ε t s).A)
          ((evalEnv D N A k ε t s).z a)).im =
          (mSol ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε)).im := by
        fin_cases a <;> simp [evalEnv]
      rw [e1]
      exact hU.trans (mul_le_mul_of_nonneg_right hmaxU hX0)

/-! ## Exponent arithmetic -/

/-- `N^a r^b`. -/
private def Lf_P (N r a b : ℝ) : ℝ := N ^ a * r ^ b

private lemma Lf_P_mul {N r : ℝ} (hN : 0 < N) (hr : 0 < r) (a b a' b' : ℝ) :
    Lf_P N r a b * Lf_P N r a' b' = Lf_P N r (a + a') (b + b') := by
  unfold Lf_P
  rw [Real.rpow_add hN, Real.rpow_add hr]
  ring

private lemma Lf_P_pow {N r : ℝ} (hN : 0 < N) (hr : 0 < r) (a b : ℝ) (k : ℕ) :
    Lf_P N r a b ^ k = Lf_P N r (k * a) (k * b) := by
  unfold Lf_P
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (r ^ b), ← Real.rpow_mul hN.le,
    ← Real.rpow_mul hr.le, mul_comm a, mul_comm b]

private lemma Lf_P_inv {N r : ℝ} (hN : 0 < N) (hr : 0 < r) (a b : ℝ) :
    (Lf_P N r a b)⁻¹ = Lf_P N r (-a) (-b) := by
  unfold Lf_P
  rw [mul_inv, Real.rpow_neg hN.le, Real.rpow_neg hr.le]

private lemma Lf_P_pos {N r : ℝ} (hN : 0 < N) (hr : 0 < r) (a b : ℝ) : 0 < Lf_P N r a b := by
  unfold Lf_P
  positivity

/-- `N^a r^b ≤ max (D^b) 1` for `1 ≤ r ≤ DN` when `a + b ≤ 0` (`b ≥ 0`) or `a ≤ 0`
(`b < 0`). -/
private lemma Lf_P_le {N r D : ℝ} (hN : 1 ≤ N) (hr1 : 1 ≤ r) (hrD : r ≤ D * N) (hD : 1 ≤ D)
    (a b : ℝ) (h1 : 0 ≤ b → a + b ≤ 0) (h2 : b < 0 → a ≤ 0) :
    Lf_P N r a b ≤ max (D ^ b) 1 := by
  unfold Lf_P
  have hN0 : 0 < N := by linarith
  rcases le_or_gt 0 b with hb | hb
  · have hrb : r ^ b ≤ (D * N) ^ b := Real.rpow_le_rpow (by linarith) hrD hb
    rw [Real.mul_rpow (by linarith) hN0.le] at hrb
    have hab : N ^ a * N ^ b ≤ 1 := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (h1 hb)
    calc N ^ a * r ^ b ≤ N ^ a * (D ^ b * N ^ b) :=
          mul_le_mul_of_nonneg_left hrb (by positivity)
      _ = D ^ b * (N ^ a * N ^ b) := by ring
      _ ≤ D ^ b * 1 := mul_le_mul_of_nonneg_left hab (by positivity)
      _ ≤ _ := by rw [mul_one]; exact le_max_left _ _
  · have h3 : N ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (h2 hb)
    have h4 : r ^ b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 hb.le
    calc N ^ a * r ^ b ≤ 1 * 1 := mul_le_mul h3 h4 (by positivity) zero_le_one
      _ ≤ _ := by rw [mul_one]; exact le_max_right _ _

/-- The flag-by-flag bound in exponent form: with `η = N^{-2/3+ε} r^{-1/3}`,
`V ≤ C_U N^{-1/3+ε/2} r^{1/3}` and `Π β ≤ c N^{p} r^{q} ‖A‖²_HS`, the bound of `Lf_flag` is
`≤ C N^{τ'} N^{2ε-5/3} r^{2/3} ‖A‖²_HS` under the exponent conditions. -/
private lemma Lf_fin {N r D : ℝ} (hN : 1 ≤ N) (hr1 : 1 ≤ r) (hrD : r ≤ D * N) (hD : 1 ≤ D)
    (ε τ' CU cP p q hs V Pβ : ℝ) (S u nf m : ℕ) (hCU : 0 ≤ CU) (hcP : 0 ≤ cP) (hV0 : 0 ≤ V)
    (hV : V ≤ CU * Lf_P N r (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ))
    (hPβ : Pβ ≤ cP * Lf_P N r p q * hs ^ 2) (hPβ0 : 0 ≤ Pβ)
    (h1 : 0 ≤ (u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3 →
      -(S : ℝ) + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) +
        ((m - nf : ℕ) : ℝ) * (2 / 3 - ε) + p + 5 / 3 - 2 * ε +
        ((u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3) ≤ 0)
    (h2 : (u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3 < 0 →
      -(S : ℝ) + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) +
        ((m - nf : ℕ) : ℝ) * (2 / 3 - ε) + p + 5 / 3 - 2 * ε ≤ 0) :
    N ^ τ' * ((N ^ S)⁻¹ * (N⁻¹ * (Lf_P N r (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)))⁻¹) ^ u *
      V ^ nf * (Lf_P N r (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)))⁻¹ ^ (m - nf) * Pβ) ≤
      CU ^ nf * cP * max (D ^ ((u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3)) 1 *
        (N ^ τ' * (N ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) * hs ^ 2)) := by
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := by linarith
  set a' := -(S : ℝ) + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) +
    ((m - nf : ℕ) : ℝ) * (2 / 3 - ε) + p + 5 / 3 - 2 * ε with ha'
  set b' := (u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3 with hb'
  have hPle := Lf_P_le hN hr1 hrD hD a' b' h1 h2
  have eS : (N ^ S)⁻¹ = Lf_P N r (-(S : ℝ)) 0 := by
    unfold Lf_P
    rw [Real.rpow_zero, mul_one, Real.rpow_neg hN0.le, Real.rpow_natCast]
  have eNi : N⁻¹ = Lf_P N r (-1) 0 := by
    unfold Lf_P
    rw [Real.rpow_zero, mul_one, Real.rpow_neg_one]
  have hη : (Lf_P N r (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)))⁻¹ = Lf_P N r (2 / 3 - ε) (1 / 3) := by
    rw [Lf_P_inv hN0 hr0]
    congr 1 <;> ring
  have hW : N⁻¹ * (Lf_P N r (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)))⁻¹ =
      Lf_P N r (-(1 / 3 : ℝ) - ε) (1 / 3) := by
    rw [hη, eNi, Lf_P_mul hN0 hr0]
    congr 1 <;> ring
  have hVn : V ^ nf ≤ (CU * Lf_P N r (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) ^ nf :=
    pow_le_pow_left₀ hV0 hV nf
  rw [hW, hη]
  have hX0 : 0 ≤ (N ^ S)⁻¹ * Lf_P N r (-(1 / 3 : ℝ) - ε) (1 / 3) ^ u := by
    have := Lf_P_pos hN0 hr0 (-(1 / 3 : ℝ) - ε) (1 / 3)
    positivity
  have hY0 : 0 ≤ Lf_P N r (2 / 3 - ε) (1 / 3) ^ (m - nf) := by
    have := Lf_P_pos hN0 hr0 (2 / 3 - ε) (1 / 3)
    positivity
  have hNτ : 0 ≤ N ^ τ' := by positivity
  calc N ^ τ' * ((N ^ S)⁻¹ * Lf_P N r (-(1 / 3 : ℝ) - ε) (1 / 3) ^ u * V ^ nf *
        Lf_P N r (2 / 3 - ε) (1 / 3) ^ (m - nf) * Pβ)
      ≤ N ^ τ' * ((N ^ S)⁻¹ * Lf_P N r (-(1 / 3 : ℝ) - ε) (1 / 3) ^ u *
        (CU * Lf_P N r (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) ^ nf *
        Lf_P N r (2 / 3 - ε) (1 / 3) ^ (m - nf) * (cP * Lf_P N r p q * hs ^ 2)) := by
        have hU0 : 0 ≤ (CU * Lf_P N r (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) ^ nf := by
          have := Lf_P_pos hN0 hr0 (-(1 / 3 : ℝ) + ε / 2) (1 / 3)
          positivity
        have hV0n : 0 ≤ V ^ nf := by positivity
        gcongr
    _ = CU ^ nf * cP * (N ^ τ' * (Lf_P N r a' b' * Lf_P N r (2 * ε - 5 / 3) (2 / 3) *
          hs ^ 2)) := by
        rw [eS, mul_pow, Lf_P_pow hN0 hr0, Lf_P_pow hN0 hr0, Lf_P_pow hN0 hr0]
        have e1 : Lf_P N r a' b' * Lf_P N r (2 * ε - 5 / 3) (2 / 3) =
            Lf_P N r (-(S : ℝ)) 0 * Lf_P N r (u * (-(1 / 3 : ℝ) - ε)) (u * (1 / 3)) *
            Lf_P N r (nf * (-(1 / 3 : ℝ) + ε / 2)) (nf * (1 / 3)) *
            Lf_P N r (((m - nf : ℕ) : ℝ) * (2 / 3 - ε)) (((m - nf : ℕ) : ℝ) * (1 / 3)) *
            Lf_P N r p q := by
          simp only [Lf_P_mul hN0 hr0]
          rw [ha', hb']
          congr 1 <;> ring
        rw [e1]
        ring
    _ ≤ CU ^ nf * cP * (N ^ τ' * (max (D ^ b') 1 * Lf_P N r (2 * ε - 5 / 3) (2 / 3) *
          hs ^ 2)) := by
        have := Lf_P_pos hN0 hr0 (2 * ε - 5 / 3) (2 / 3)
        gcongr
    _ = _ := by unfold Lf_P; ring

/-! ## The leaves bounded flag by flag -/

private lemma Lf_countP_rcR (w : List LoopLetter) : w.countP rcR = w.countP Bd_isRes := by
  rfl

private lemma Lf_lamB_iff (w : List LoopLetter) : Lf_lamB w = true ↔ 0 < w.countP Bd_isL := by
  simp [Lf_lamB]

/-- The loops of a leaf with `k₁ = k₂ = 0`: two resolvents in every loop without `Λ̃`, none in a
loop with `Λ̃`. -/
private lemma Lf_leaf_loops {T : LoopExpr} (hI : Inv T) (h0 : T.kk 0 = 0) (h1 : T.kk 1 = 0) :
    (∀ w ∈ T.loops, Lf_lamB w = false → 2 ≤ w.countP Bd_isRes) ∧
    (∀ w ∈ T.loops, Lf_lamB w = true → w.countP Bd_isRes = 0) := by
  obtain ⟨hw, -, -, -, hJ, -⟩ := hI
  constructor
  · intro w hm hl
    have hl' : w.countP Bd_isL = 0 := by simpa [Lf_lamB] using hl
    rw [← Lf_countP_rcR]
    refine hJ w hm fun k hk => ?_
    have := List.countP_eq_zero.1 hl' _ hk
    simp [Bd_isL] at this
  · intro w hm hl
    obtain ⟨x, hx, hxL⟩ := List.countP_pos_iff.1 ((Lf_lamB_iff w).1 hl)
    cases x with
    | lamt o => rw [← Lf_countP_rcR]; exact leaf_lam_nores hw h0 h1 hm o hx
    | _ => simp [Bd_isL] at hxL

/-- The loops with `Λ̃`: one loop with both (Type I) or two loops with one each (Type II). -/
private lemma Lf_shape {T : LoopExpr} (hT : T.wf = true) :
    (∃ w, T.loops.filter Lf_lamB = [w] ∧ w.countP Bd_isL = 2) ∨
    (∃ w₁ w₂, T.loops.filter Lf_lamB = [w₁, w₂] ∧ w₁.countP Bd_isL = 1 ∧
      w₂.countP Bd_isL = 1) := by
  obtain ⟨h2, hsum, -⟩ := Bd_wf_facts T hT
  have hs := Lf_sum_filter T.loops Lf_lamB (List.countP Bd_isL)
  have h0 : ((T.loops.filter fun x => !Lf_lamB x).map (List.countP Bd_isL)).sum = 0 := by
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_filter] at hw
    simpa [Lf_lamB] using hw.2
  have hpos : ∀ w ∈ T.loops.filter Lf_lamB, 1 ≤ w.countP Bd_isL ∧ w.countP Bd_isL ≤ 2 := by
    intro w hw
    rw [List.mem_filter] at hw
    exact ⟨(Lf_lamB_iff w).1 hw.2, h2 w hw.1⟩
  rw [hsum, h0, add_zero] at hs
  generalize T.loops.filter Lf_lamB = LL at hs hpos ⊢
  match LL, hs, hpos with
  | [], hs, _ => simp at hs
  | [w], hs, _ => exact Or.inl ⟨w, rfl, by simpa using hs.symm⟩
  | [w₁, w₂], hs, hp =>
    have a1 := (hp w₁ (by simp)).1
    have a2 := (hp w₂ (by simp)).1
    simp at hs
    exact Or.inr ⟨w₁, w₂, rfl, by omega, by omega⟩
  | w₁ :: w₂ :: w₃ :: l, hs, hp =>
    have a1 := (hp w₁ (by simp)).1
    have a2 := (hp w₂ (by simp)).1
    have a3 := (hp w₃ (by simp)).1
    simp at hs
    omega

/-- The two shapes are Type I and Type II. -/
private lemma Lf_shape_typeI {T : LoopExpr} (hT : T.wf = true) :
    ((∃ w, T.loops.filter Lf_lamB = [w] ∧ w.countP Bd_isL = 2) → typeI T = true) ∧
    ((∃ w₁ w₂, T.loops.filter Lf_lamB = [w₁, w₂] ∧ w₁.countP Bd_isL = 1 ∧
      w₂.countP Bd_isL = 1) → typeI T = false) := by
  constructor
  · rintro ⟨w, hLL, hw⟩
    have hwm : w ∈ T.loops := (List.mem_filter.1 (hLL ▸ List.mem_singleton_self w)).1
    have hc0 := count_le_one hT hwm 0
    have hc1 := count_le_one hT hwm 1
    rw [Bd_isL_count] at hw
    unfold typeI
    rw [List.any_eq_true]
    refine ⟨w, hwm, ?_⟩
    simp only [Bool.and_eq_true, List.contains_iff_mem]
    exact ⟨List.count_pos_iff.1 (by omega), List.count_pos_iff.1 (by omega)⟩
  · rintro ⟨w₁, w₂, hLL, hw1, hw2⟩
    unfold typeI
    rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
    rintro ⟨w, hwm, hw⟩
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hw
    have h2 : 2 ≤ w.countP Bd_isL := by
      rw [Bd_isL_count]
      have := List.count_pos_iff.2 hw.1
      have := List.count_pos_iff.2 hw.2
      omega
    have hwL : w ∈ T.loops.filter Lf_lamB := List.mem_filter.2 ⟨hwm, (Lf_lamB_iff w).2 (by omega)⟩
    rw [hLL] at hwL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwL
    rcases hwL with rfl | rfl <;> omega

/-- The block indices of the projections of a loop are bound. -/
private lemma Lf_proj_lt {T : LoopExpr} (hT : T.wf = true) {w : List LoopLetter}
    (hw : w ∈ T.loops) {y : ℕ} (hy : LoopLetter.proj y ∈ w) : y < T.nb := by
  unfold LoopExpr.wf at hT
  simp only [Bool.and_eq_true, List.all_eq_true] at hT
  have := hT.1.2 w hw _ hy
  simpa using this

/-- The number of loops `⟨𝔐_b E_x 𝔐_a Λ̃⟩` among the loops with `Λ̃`. -/
private def Lf_rho (T : LoopExpr) : ℕ := ((T.loops.filter Lf_lamB).filter Lf_rform).length

/-- The leaves bounded flag by flag: Type I with `R ≥ 3` or `m + u ≥ 2`; Type II with
`m + u + ρ ≥ 4` or `3R + m + u + ρ ≥ 10`, `ρ` the number of loops `⟨𝔐_b E_x 𝔐_a Λ̃⟩`. -/
private def Lf_okB (T : LoopExpr) : Bool :=
  match T.charsZ with
  | (m, _, u, _) => if typeI T then decide (3 ≤ T.rcount ∨ 2 ≤ m + u) else
      decide (4 ≤ m + u + Lf_rho T ∨ 10 ≤ 3 * T.rcount + m + u + Lf_rho T)

/-- The generic leaves are bounded flag by flag. -/
private lemma Lf_okB_of_genB {T : LoopExpr} (h : genB T = true) : Lf_okB T = true := by
  have hnn := charsZ_nonneg T
  unfold genB at h
  unfold Lf_okB
  generalize T.charsZ = c at h hnn ⊢
  obtain ⟨m, n, u, S⟩ := c
  simp only at h hnn ⊢
  split_ifs at h ⊢ <;> simp at h ⊢ <;> omega

/-- The leaves (5.59)–(5.61) are bounded flag by flag. -/
private lemma Lf_okB_exc : Lf_okB lf59 = true ∧ Lf_okB lf60 = true ∧ Lf_okB lf61a = true ∧
    Lf_okB lf61b = true ∧ Lf_okB lf61c = true ∧ Lf_okB lf61d = true := by
  decide

/-- The free loops carry at least two resolvents each: `m ≥ 2 n_f`. -/
private lemma Lf_m_ge {T : LoopExpr}
    (hfree : ∀ w ∈ T.loops, Lf_lamB w = false → 2 ≤ w.countP Bd_isRes) :
    2 * Lf_nf T ≤ Lf_m T := by
  unfold Lf_nf Lf_m
  rw [Lf_sum_filter T.loops Lf_lamB (List.countP Bd_isRes)]
  have : ∀ l : List (List LoopLetter), (∀ w ∈ l, 2 ≤ w.countP Bd_isRes) →
      2 * l.length ≤ (l.map (List.countP Bd_isRes)).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons x t ih =>
      have := hl x (by simp)
      have := ih fun y hy => hl y (by simp [hy])
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  have h := this (T.loops.filter fun w => !Lf_lamB w) fun w hw => by
    rw [List.mem_filter] at hw
    exact hfree w hw.1 (by simpa using hw.2)
  omega

/-- The exponent conditions of `Lf_fin` for Type I. -/
private lemma Lf_condI (ε S u nf m R : ℝ) (hε : 0 < ε) (hu : 0 ≤ u) (hnf : 0 ≤ nf)
    (hm : 2 * nf ≤ m) (hR : R = S - m + (nf + 1) + 1) (hR2 : 2 ≤ R) (hok : 3 ≤ R ∨ 2 ≤ m + u) :
    (0 ≤ (u + nf + (m - nf)) / 3 + 0 - 2 / 3 →
      -S + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) + (m - nf) * (2 / 3 - ε) + -1 +
        5 / 3 - 2 * ε + ((u + nf + (m - nf)) / 3 + 0 - 2 / 3) ≤ 0) ∧
    ((u + nf + (m - nf)) / 3 + 0 - 2 / 3 < 0 →
      -S + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) + (m - nf) * (2 / 3 - ε) + -1 +
        5 / 3 - 2 * ε ≤ 0) := by
  have e1 : ε * (u + m - 3 / 2 * nf + 2) ≥ 0 := mul_nonneg hε.le (by linarith)
  constructor
  · intro _
    nlinarith
  · intro hb
    rcases hok with h | h
    · nlinarith
    · exfalso; linarith

/-- The exponent conditions of `Lf_fin` for Type II. -/
private lemma Lf_condII (ε εA S u nf m R ρ : ℝ) (hε : 0 < ε) (hεA : 0 < εA) (hu : 0 ≤ u)
    (hnf : 0 ≤ nf) (hρ2 : ρ ≤ 2) (hm : 2 * nf ≤ m)
    (hR : R = S - m + (nf + 2) + 1) (hR2 : 2 ≤ R)
    (hok : 4 ≤ m + u + ρ ∨ 10 ≤ 3 * R + m + u + ρ) :
    (0 ≤ (u + nf + (m - nf)) / 3 + (-(2 / 3 : ℝ) + ρ / 3) - 2 / 3 →
      -S + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) + (m - nf) * (2 / 3 - ε) +
        (-(4 / 3 : ℝ) - 2 * εA + ρ * (-(1 / 3 : ℝ) + ε / 2)) + 5 / 3 - 2 * ε +
        ((u + nf + (m - nf)) / 3 + (-(2 / 3 : ℝ) + ρ / 3) - 2 / 3) ≤ 0) ∧
    ((u + nf + (m - nf)) / 3 + (-(2 / 3 : ℝ) + ρ / 3) - 2 / 3 < 0 →
      -S + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) + (m - nf) * (2 / 3 - ε) +
        (-(4 / 3 : ℝ) - 2 * εA + ρ * (-(1 / 3 : ℝ) + ε / 2)) + 5 / 3 - 2 * ε ≤ 0) := by
  have e1 : ε * (u + m - 3 / 2 * nf - ρ / 2 + 2) ≥ 0 := mul_nonneg hε.le (by linarith)
  constructor
  · intro _
    nlinarith
  · intro hb
    rcases hok with h | h
    · exfalso; linarith
    · nlinarith

/-- The leaves bounded flag by flag: `|E 𝒯| ≤ ¼ N^{τ+2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` at every
slot, from (5.51) [estimate_loop_type_1], the Type II bound after (5.58) [eq:polar2], and (5.62)
[eq:polar3]–(5.64) [eq:polar5] for (5.59)–(5.61). -/
private lemma Lf_leaf_flag (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (T : LoopExpr)
    (hI : Inv T) (h0 : T.kk 0 = 0) (h1 : T.kk 1 = 0) (hok : Lf_okB T = true) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ‖∫ h, T.evalH e h ∂μ‖ ≤ 1 / 4 * ((N : ℝ) ^ (τ + 2 * ε) *
          ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) := by
  intro τ hτ
  have hIc := hI
  obtain ⟨hwf, -, -, -, -, hR2, -⟩ := hI
  have hR2' := hR2 h0 h1
  obtain ⟨hfree, hlam⟩ := Lf_leaf_loops hIc h0 h1
  obtain ⟨hL2, -, -⟩ := Bd_wf_facts T hwf
  set n₀ := (T.loops.map List.length).sum with hn₀
  obtain ⟨c₀, K, Kg, C₇, CU, hc₀, hK, hKg, hC₇, hCU, N₁, hN₁⟩ :=
    Lf_slots D hD δA εA ε hδA hεA hε hε' hε'' n₀
  obtain ⟨N₂, hN₂⟩ := Lf_flag D hD δA (ε / 2) c₀ K hδA (by positivity) hc₀ C T hfree hlam
    (τ / 2) (by positivity)
  set u := T.weights.length with hu
  set nf := Lf_nf T with hnf
  set m := Lf_m T with hm
  have hm2 : 2 * nf ≤ m := Lf_m_ge hfree
  have hcz : T.charsZ = ((m : ℤ), (T.loops.length : ℤ), (u : ℤ), (T.S : ℤ)) := rfl
  have hlen : T.loops.length = nf + (T.loops.filter Lf_lamB).length := by
    rw [List.length_eq_length_filter_add Lf_lamB, hnf, Lf_nf]
    omega
  have hRc : T.rcount = (T.S : ℤ) - m + T.loops.length + 1 := by
    unfold LoopExpr.rcount
    rw [hcz]
  have hmnf : ((m - nf : ℕ) : ℝ) = (m : ℝ) - nf := by
    rw [Nat.cast_sub (by omega)]
  -- the common part: from a bound on the loops with `Λ̃`
  have key : ∀ p q cP : ℝ, 0 ≤ cP →
      (0 ≤ (u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3 →
        -(T.S : ℝ) + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) +
          ((m - nf : ℕ) : ℝ) * (2 / 3 - ε) + p + 5 / 3 - 2 * ε +
          ((u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3) ≤ 0) →
      ((u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3 < 0 →
        -(T.S : ℝ) + u * (-(1 / 3 : ℝ) - ε) + nf * (-(1 / 3 : ℝ) + ε / 2) +
          ((m - nf : ℕ) : ℝ) * (2 / 3 - ε) + p + 5 / 3 - 2 * ε ≤ 0) →
      (∀ N : ℕ, N₁ ≤ N → 1 ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
          ((T.loops.filter Lf_lamB).map (Lf_beta D K Kg C₇ (5 / 4) (avgSq (lam D N e.A))
            (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im)).prod ≤
            cP * Lf_P N (rk D N k) p q * hsNorm A ^ 2) →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
        ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
            ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
          ‖∫ h, T.evalH e h ∂μ‖ ≤ 1 / 4 * ((N : ℝ) ^ (τ + 2 * ε) *
            ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) := by
    intro p q cP hcP hc1 hc2 hPβ
    set b' := (u + nf + ((m - nf : ℕ) : ℝ)) / 3 + q - 2 / 3 with hb'
    set Cst := CU ^ nf * cP * max ((D : ℝ) ^ b') 1 with hCst
    have hCst0 : 0 ≤ Cst := by positivity
    obtain ⟨N₃, hN₃⟩ := Bd_large (τ / 2) (4 * Cst) (by positivity)
    refine ⟨max (max N₁ N₂) (max N₃ 1), ?_⟩
    intro N hN μ hμ A hA k hk hkN hhs e he
    have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hNc : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < N := by linarith
    obtain ⟨hA2, hc, hz, hδ, hSF, heA, hU⟩ := hN₁ N hNa A hA k hk hkN hhs e he
    have hCl : (μ, e) ∈ Bd_Cl D δA 1 K C N :=
      ⟨hμ, heA ▸ hA, by rw [mul_one]; exact hA2, hc, hδ⟩
    have hzc : ∀ a, Bd_zc D (ε / 2) c₀ N e a := fun a => ⟨(hz a).1, (hz a).2.1, (hz a).2.2.2⟩
    set σ := avgSq (lam D N e.A) with hσ
    set g := (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im with hg
    have hσ0 : 0 ≤ σ := Bd_avgSq_nonneg _ (lam_isHermitian D N e.A)
    have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
    have hg0 : 0 ≤ g := (mSol_spec _ (Bd_lamc_herm D N e.A (e.c 1)) _ (hz 1).2.1).1.le
    have hβ0 : ∀ w, 0 ≤ Lf_beta D K Kg C₇ (5 / 4) σ g w := by
      intro w
      unfold Lf_beta
      split_ifs <;> positivity
    have hβ : ∀ (ι : Fin T.nb → Fin D) (h : Idx D N → Idx D N → ℂ), ∀ w ∈ T.loops,
        Lf_lamB w = true → ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤
          Lf_beta D K Kg C₇ (5 / 4) σ g w := by
      intro ι h w hw hl
      exact Lf_lamloop e K Kg C₇ (5 / 4) n₀ hK (by norm_num) hC₇ hSF ι h w (hlam w hw hl)
        ((Lf_lamB_iff w).1 hl) (hL2 w hw) (fun y hy => Lf_proj_lt hwf hw hy)
        (List.le_sum_of_mem (List.mem_map_of_mem hw))
    have hflag := hN₂ N hNb μ e hCl hzc _ hβ0 hβ
    -- the parameters of the slots
    set r := rk D N k with hr
    have hr1 : (1 : ℝ) ≤ r := by rw [hr, Lf_rk_eq D N k hkN]; exact_mod_cast hk
    have hrD : r ≤ (D : ℝ) * N := by
      rw [hr, Lf_rk_eq D N k hkN]
      have : k ≤ D * N := by
        have : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hN1)
        omega
      exact_mod_cast this
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
    have hηe : Bd_eta e = Lf_P N r (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)) := by
      unfold Bd_eta Lf_P
      rw [(hz 0).2.2.1, (hz 1).2.2.1, min_self]
      rfl
    have hV : Lf_imax e ≤ CU * Lf_P N r (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ) :=
      max_le (hU 0) (hU 1)
    have hV0 : 0 ≤ Lf_imax e := hg0.trans (Lf_imax_ge e 1)
    have hPβ' := hPβ N hNa hN1 A hA k hk hkN hhs e he
    have hPβ0 : 0 ≤ ((T.loops.filter Lf_lamB).map (Lf_beta D K Kg C₇ (5 / 4) σ g)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
        exact hβ0 w
    rw [hηe] at hflag
    have hfin := Lf_fin hN1r hr1 hrD hD1 ε (τ / 2) CU cP p q (hsNorm A) (Lf_imax e) _ T.S u nf m
      hCU.le hcP hV0 hV hPβ' hPβ0 hc1 hc2
    refine hflag.trans (hfin.trans ?_)
    have hbig : 4 * Cst ≤ (N : ℝ) ^ (τ / 2) := hN₃ N hNc
    have hX0 : 0 ≤ (N : ℝ) ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) * hsNorm A ^ 2 := by
      have : 0 ≤ r ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
      positivity
    have e1 : (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * r ^ (2 / 3 : ℝ) *
        hsNorm A ^ 2) = (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε - 5 / 3) *
          r ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) := by
      rw [show (N : ℝ) ^ (2 * ε - 5 / 3) = (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (-(5 / 3 : ℝ)) by
        rw [← Real.rpow_add hNpos]; ring_nf,
        show (N : ℝ) ^ (τ + 2 * ε) = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (2 * ε) by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; ring_nf]
      ring
    rw [e1]
    have hNτ : 0 ≤ (N : ℝ) ^ (τ / 2) := by positivity
    have : Cst * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) *
        hsNorm A ^ 2)) ≤ 1 / 4 * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) *
          ((N : ℝ) ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) * hsNorm A ^ 2))) := by
      have h3 : Cst ≤ 1 / 4 * (N : ℝ) ^ (τ / 2) := by linarith
      have h4 : 0 ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) *
          hsNorm A ^ 2) := by positivity
      calc Cst * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2)) ≤ (1 / 4 * (N : ℝ) ^ (τ / 2)) * ((N : ℝ) ^ (τ / 2) *
            ((N : ℝ) ^ (2 * ε - 5 / 3) * r ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) :=
            mul_le_mul_of_nonneg_right h3 h4
        _ = _ := by ring
    exact this
  have hRr : ∀ j : ℕ, T.loops.length = nf + j →
      (T.rcount : ℝ) = (T.S : ℝ) - m + (nf + j) + 1 := by
    intro j hj
    rw [hRc, hj]
    push_cast
    ring
  have hS4D : ∀ N : ℕ, 1 ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      avgSq (lam D N A) ≤ 4 * D * Lf_P N 1 (-1) 0 * hsNorm A ^ 2 := by
    intro N hN A
    have := Rg_avgSq_lam D N hD hN A
    unfold Lf_P
    rw [Real.rpow_neg_one, Real.rpow_zero, mul_one]
    calc _ ≤ 4 * D * hsNorm A ^ 2 / N := this
      _ = _ := by ring
  rcases Lf_shape hwf with ⟨w, hLL, hw2⟩ | ⟨w₁, w₂, hLL, hw1, hw2⟩
  · -- Type I
    have hty := (Lf_shape_typeI hwf).1 ⟨w, hLL, hw2⟩
    have hokI : 3 ≤ T.rcount ∨ 2 ≤ (m : ℤ) + u := by
      unfold Lf_okB at hok
      rw [hcz] at hok
      simpa only [hty, ↓reduceIte, decide_eq_true_eq] using hok
    have hR := hRr 1 (by rw [hlen, hLL]; rfl)
    have hokI' : (3 : ℝ) ≤ T.rcount ∨ (2 : ℝ) ≤ m + u := by
      rcases hokI with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    obtain ⟨hc1, hc2⟩ := Lf_condI ε T.S u nf m T.rcount hε (by positivity) (by positivity)
      (by exact_mod_cast hm2) (by rw [hR]; push_cast; ring) (by exact_mod_cast hR2') hokI'
    refine key (-1) 0 ((5 / 4 : ℝ) ^ (2 * w.length) * (1 + K ^ 2) * (4 * D)) (by positivity)
      (by rw [hmnf]; exact hc1) (by rw [hmnf]; exact hc2) ?_
    intro N hN1' hN1 A hA k hk hkN hhs e he
    obtain ⟨-, -, -, -, -, heA, -⟩ := hN₁ N hN1' A hA k hk hkN hhs e he
    rw [hLL]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold Lf_beta
    rw [if_pos hw2, heA]
    have h1 := hS4D N hN1 A
    have hP1 : Lf_P N 1 (-1) 0 = Lf_P N (rk D N k) (-1) 0 := by
      unfold Lf_P; simp
    rw [hP1] at h1
    have h0 : 0 ≤ (5 / 4 : ℝ) ^ (2 * w.length) * (1 + K ^ 2) := by positivity
    calc (5 / 4 : ℝ) ^ (2 * w.length) * (1 + K ^ 2) * avgSq (lam D N A)
        ≤ (5 / 4 : ℝ) ^ (2 * w.length) * (1 + K ^ 2) *
          (4 * D * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2) :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by ring
  · -- Type II
    have hty := (Lf_shape_typeI hwf).2 ⟨w₁, w₂, hLL, hw1, hw2⟩
    set ρ := Lf_rho T with hρ
    have hρeq : ρ = (if Lf_rform w₁ then 1 else 0) + (if Lf_rform w₂ then 1 else 0) := by
      rw [hρ, Lf_rho, hLL]
      by_cases h₁ : Lf_rform w₁ = true <;> by_cases h₂ : Lf_rform w₂ = true <;>
        simp [List.filter, h₁, h₂]
    have hρ2 : ρ ≤ 2 := by rw [hρeq]; split_ifs <;> omega
    have hokII : 4 ≤ (m : ℤ) + u + ρ ∨ 10 ≤ 3 * T.rcount + m + u + ρ := by
      unfold Lf_okB at hok
      rw [hcz] at hok
      simpa only [hty, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] using hok
    have hR := hRr 2 (by rw [hlen, hLL]; rfl)
    have hokII' : (4 : ℝ) ≤ m + u + ρ ∨ (10 : ℝ) ≤ 3 * T.rcount + m + u + ρ := by
      rcases hokII with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    obtain ⟨hc1, hc2⟩ := Lf_condII ε εA T.S u nf m T.rcount ρ hε hεA (by positivity)
      (by positivity) (by exact_mod_cast hρ2) (by exact_mod_cast hm2)
      (by rw [hR]; push_cast; ring) (by exact_mod_cast hR2') hokII'
    set cβ : List LoopLetter → ℝ := fun w => if Lf_rform w then Kg else
      ((D : ℝ) ^ w.length * (5 / 4 : ℝ) ^ w.length * (D * C₇) + |K| * (5 / 4 : ℝ) ^ w.length)
      with hcβ
    have hcβ0 : ∀ w, 0 ≤ cβ w := by
      intro w
      simp only [hcβ]
      split_ifs <;> positivity
    refine key (-(4 / 3 : ℝ) - 2 * εA + ρ * (-(1 / 3 : ℝ) + ε / 2)) (-(2 / 3 : ℝ) + ρ / 3)
      (cβ w₁ * cβ w₂ * (4 * D) ^ 2 * CU ^ ρ) (by have := hcβ0 w₁; have := hcβ0 w₂; positivity)
      (by rw [hmnf]; exact hc1) (by rw [hmnf]; exact hc2) ?_
    intro N hN1' hN1 A hA k hk hkN hhs e he
    obtain ⟨-, -, -, -, -, heA, hU⟩ := hN₁ N hN1' A hA k hk hkN hhs e he
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hrpos : (0 : ℝ) < rk D N k := by rw [Lf_rk_eq D N k hkN]; exact_mod_cast hk
    set σ := avgSq (lam D N e.A) with hσ
    set g := (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im with hg
    set U := CU * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ) with hUdef
    have hσ0 : 0 ≤ σ := Bd_avgSq_nonneg _ (lam_isHermitian D N e.A)
    have hgU : g ≤ U := hU 1
    have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
    have hU0 : 0 ≤ U := by
      have := Lf_P_pos hNpos hrpos (-(1 / 3 : ℝ) + ε / 2) (1 / 3)
      positivity
    have hβw : ∀ w, w.countP Bd_isL = 1 → Lf_beta D K Kg C₇ (5 / 4) σ g w ≤
        cβ w * σ * (if Lf_rform w then U else 1) := by
      intro w hw
      unfold Lf_beta
      rw [if_neg (by omega)]
      simp only [hcβ]
      by_cases hr : Lf_rform w = true
      · simp only [hr, ↓reduceIte]
        calc Kg * g * σ ≤ Kg * U * σ := by gcongr
          _ = _ := by ring
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, mul_one]
        apply le_of_eq
        ring
    rw [hLL]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hb1 := hβw w₁ hw1
    have hb2 := hβw w₂ hw2
    have hG : (if Lf_rform w₁ then U else 1) * (if Lf_rform w₂ then U else 1) = U ^ ρ := by
      rw [hρeq]
      split_ifs <;> ring
    have hβ0 : ∀ w, 0 ≤ Lf_beta D K Kg C₇ (5 / 4) σ g w := by
      intro w
      unfold Lf_beta
      have hg0 : 0 ≤ g := (mSol_spec _ (Bd_lamc_herm D N e.A (e.c 1)) _
        ((hN₁ N hN1' A hA k hk hkN hhs e he).2.2.1 1).2.1).1.le
      split_ifs <;> positivity
    have hGi : ∀ w, 0 ≤ (if Lf_rform w then U else 1) := fun w => by split_ifs <;> positivity
    have hP2 : Lf_beta D K Kg C₇ (5 / 4) σ g w₁ * Lf_beta D K Kg C₇ (5 / 4) σ g w₂ ≤
        cβ w₁ * cβ w₂ * σ * σ * U ^ ρ := by
      calc _ ≤ (cβ w₁ * σ * (if Lf_rform w₁ then U else 1)) *
            (cβ w₂ * σ * (if Lf_rform w₂ then U else 1)) :=
            mul_le_mul hb1 hb2 (hβ0 w₂) (by have := hcβ0 w₁; have := hGi w₁; positivity)
        _ = cβ w₁ * cβ w₂ * σ * σ * ((if Lf_rform w₁ then U else 1) *
            (if Lf_rform w₂ then U else 1)) := by ring
        _ = _ := by rw [hG]
    refine hP2.trans ?_
    -- `⟨Λ²⟩² ≤ (4D)² N^{-4/3-2ε_A} 𝔯(k)^{-2/3} ‖A‖²_HS`
    have hP1 : Lf_P N 1 (-1) 0 = Lf_P N (rk D N k) (-1) 0 := by unfold Lf_P; simp
    have hσ1 : σ ≤ 4 * D * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2 := by
      have := hS4D N hN1 A
      rw [hσ, heA, ← hP1]
      exact this
    have hhs2 : hsNorm A ^ 2 ≤ Lf_P N (rk D N k) (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ))) := by
      have h0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
      have := pow_le_pow_left₀ h0 hhs 2
      have e2 := Lf_P_pow hNpos hrpos ((1 / 3 : ℝ) - εA) (-(1 / 3 : ℝ)) 2
      unfold Lf_P at e2 ⊢
      rw [e2] at this
      simpa using this
    have hσ2 : σ ≤ 4 * D * (Lf_P N (rk D N k) (-1) 0 *
        Lf_P N (rk D N k) (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ)))) := by
      have h4 : 0 ≤ 4 * (D : ℝ) * Lf_P N (rk D N k) (-1) 0 := by
        have := Lf_P_pos hNpos hrpos (-1) 0
        positivity
      calc σ ≤ 4 * D * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2 := hσ1
        _ ≤ 4 * D * Lf_P N (rk D N k) (-1) 0 *
            Lf_P N (rk D N k) (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hhs2 h4
        _ = _ := by ring
    have hUρ : U ^ ρ = CU ^ ρ * Lf_P N (rk D N k) (ρ * (-(1 / 3 : ℝ) + ε / 2)) (ρ * (1 / 3)) := by
      rw [hUdef, mul_pow, Lf_P_pow hNpos hrpos]
    have hc0 : 0 ≤ cβ w₁ * cβ w₂ := mul_nonneg (hcβ0 w₁) (hcβ0 w₂)
    calc cβ w₁ * cβ w₂ * σ * σ * U ^ ρ
        ≤ cβ w₁ * cβ w₂ * (4 * D * (Lf_P N (rk D N k) (-1) 0 *
            Lf_P N (rk D N k) (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ))))) *
          (4 * D * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2) * U ^ ρ := by
          have hUρ0 : 0 ≤ U ^ ρ := by positivity
          have hq1 := Lf_P_pos hNpos hrpos (-1) 0
          have hq2 := Lf_P_pos hNpos hrpos (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ)))
          have hq3 : 0 ≤ cβ w₁ * cβ w₂ * (4 * D * (Lf_P N (rk D N k) (-1) 0 *
            Lf_P N (rk D N k) (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ))))) := by positivity
          gcongr
      _ = cβ w₁ * cβ w₂ * (4 * D) ^ 2 * CU ^ ρ * (Lf_P N (rk D N k) (-1) 0 *
            Lf_P N (rk D N k) (2 * ((1 / 3 : ℝ) - εA)) (2 * (-(1 / 3 : ℝ))) *
            Lf_P N (rk D N k) (-1) 0 *
            Lf_P N (rk D N k) (ρ * (-(1 / 3 : ℝ) + ε / 2)) (ρ * (1 / 3))) * hsNorm A ^ 2 := by
          rw [hUρ]; ring
      _ = _ := by
          simp only [Lf_P_mul hNpos hrpos]
          congr 3 <;> ring

/-! ## The leaves (5.54) and (5.55): the pairing over the flags -/

/-- The sum over the four flags. -/
private lemma Lf_sum_flags (f : (Fin 2 → Bool) → ℂ) :
    ∑ s : Fin 2 → Bool, f s = f ![false, false] + f ![false, true] + f ![true, false] +
      f ![true, true] := by
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Bool) f (fun p => f ![p.1, p.2]) (fun s => by
    congr 1
    funext i
    fin_cases i <;> rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The slot limits at a flag: `𝔐_a = M_a` or `M_a^*`, `M_a = M(c_a Λ, z_a)`. -/
private lemma Lf_M_flag {D N : ℕ} [Nonempty (Idx D N)] (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (s : Fin 2 → Bool) (a : Fin 2) :
    ({ e with s := s } : LoopEnv D N).M a =
      if s a then (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a))ᴴ
      else MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) :=
  Rch_flag _ (Bd_lamc_herm D N e.A (e.c a)) (e.z a) (hz a).ne' (s a)

/-- `‖M - M^*‖ ≤ 2 (η + Im m) ‖M‖²` by (A.3) [equation_z_im_m]. -/
private lemma Lf_imM {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hB : opNorm (MExt Λ z) ≤ B) :
    opNorm (MExt Λ z - (MExt Λ z)ᴴ) ≤ 2 * (z.im + (mSol Λ z).im) * B ^ 2 := by
  rw [Lf_ext_eq Λ hz] at hB ⊢
  rw [(equation_z_im_m Λ hΛ z hz).2, opNorm_smul]
  have hm : 0 ≤ (mSol Λ z).im := (mSol_spec Λ hΛ z hz).1.le
  have h1 : ‖(2 * Complex.I * ((z.im + (mSol Λ z).im : ℝ) : ℂ))‖ = 2 * (z.im + (mSol Λ z).im) := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    simp
  rw [h1]
  have h2 : opNorm (MSol Λ z * (MSol Λ z)ᴴ) ≤ B ^ 2 := by
    refine (opNorm_mul_le _ _).trans ?_
    rw [Bd_opNorm_conjTranspose, sq]
    have := Bd_opNorm_nonneg (MSol Λ z)
    exact mul_le_mul hB hB this (this.trans hB)
  exact mul_le_mul_of_nonneg_left h2 (by linarith)

/-- The value of the leaf (5.54) [expansion_result_R_2_C_0_P_0]: `⟨𝔐₁ Λ̃ 𝔐₀ Λ̃⟩`. -/
private lemma Lf_eval54 {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) :
    lf54.evalH e h = ntr (e.M 1 * e.Lt * e.M 0 * e.Lt) := by
  have : Unique (Fin lf54.nb → Fin D) := inferInstanceAs (Unique (Fin 0 → Fin D))
  unfold LoopExpr.evalH
  rw [Fintype.sum_unique]
  simp [lf54, loopWordMat, Matrix.mul_assoc]

/-- (5.54) [expansion_result_R_2_C_0_P_0] summed over the four flags: the pairing (5.56)
[eq:polar_cancel] gives `⟨(M₁ - M₁^*) Λ̃ (M₀ - M₀^*) Λ̃⟩`. -/
private lemma Lf_signed54 {D N : ℕ} [Nonempty (Idx D N)] (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ] :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, lf54.evalH { e with s := s } h ∂μ‖ ≤
      opNorm (MExt ((e.c 1 : ℂ) • lam D N e.A) (e.z 1) -
          (MExt ((e.c 1 : ℂ) • lam D N e.A) (e.z 1))ᴴ) *
        opNorm (MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0) -
          (MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0))ᴴ) * avgSq e.Lt := by
  set X₀ := MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0) with hX₀
  set X₁ := MExt ((e.c 1 : ℂ) • lam D N e.A) (e.z 1) with hX₁
  have hv : ∀ s : Fin 2 → Bool, ∫ h, lf54.evalH { e with s := s } h ∂μ =
      ntr ((if s 1 then X₁ᴴ else X₁) * e.Lt * (if s 0 then X₀ᴴ else X₀) * e.Lt) := by
    intro s
    simp only [Lf_eval54, integral_const, probReal_univ, one_smul]
    rw [Lf_M_flag e hz s 1, Lf_M_flag e hz s 0]
    rfl
  simp only [hv]
  rw [Lf_sum_flags]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Bool.false_eq_true,
    ↓reduceIte, ite_true]
  have e1 : (1 : ℂ) * ntr (X₁ * e.Lt * X₀ * e.Lt) + (-1) * ntr (X₁ᴴ * e.Lt * X₀ * e.Lt) +
      (-1) * ntr (X₁ * e.Lt * X₀ᴴ * e.Lt) + 1 * ntr (X₁ᴴ * e.Lt * X₀ᴴ * e.Lt) =
      ntr ((X₁ - X₁ᴴ) * e.Lt * (X₀ - X₀ᴴ) * e.Lt) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, ntr, Matrix.trace_sub]
    ring
  simp only [Bool.true_eq_false, ↓reduceIte]
  rw [e1]
  exact Tay_BL (Rch_Lt_herm e) _ _

/-- The value of the second leaf of (5.55) [expansion_result_R_2_C_1_P_0]:
`D Σ_x ⟨(𝒢₀ - 𝔐₀) E_x⟩ ⟨𝔐₁ Λ̃ (𝔐₀ E_x 𝔐₀) Λ̃⟩`. -/
private lemma Lf_eval55b {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) :
    lf55b.evalH e h = (D : ℂ) * ∑ x : Fin D, ntr ((e.G h 0 - e.M 0) * Ea D N x) *
      ntr (e.M 1 * e.Lt * (e.M 0 * Ea D N x * e.M 0) * e.Lt) := by
  unfold LoopExpr.evalH
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin D)) _ (fun x =>
    ntr ((e.G h 0 - e.M 0) * Ea D N x) * ntr (e.M 1 * e.Lt * (e.M 0 * Ea D N x * e.M 0) * e.Lt))
    (fun ι => by
      simp [lf55b, loopWordMat, LoopEnv.E, Matrix.mul_assoc])]
  simp

/-- The value of the first leaf of (5.55) [expansion_result_R_2_C_1_P_0]:
`D Σ_x ⟨(𝒢₁ - 𝔐₁) E_x⟩ ⟨(𝔐₁ E_x 𝔐₁) Λ̃ 𝔐₀ Λ̃⟩`. -/
private lemma Lf_eval55a {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) :
    lf55a.evalH e h = (D : ℂ) * ∑ x : Fin D, ntr ((e.G h 1 - e.M 1) * Ea D N x) *
      ntr ((e.M 1 * Ea D N x * e.M 1) * e.Lt * e.M 0 * e.Lt) := by
  unfold LoopExpr.evalH
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin D)) _ (fun x =>
    ntr ((e.G h 1 - e.M 1) * Ea D N x) * ntr ((e.M 1 * Ea D N x * e.M 1) * e.Lt * e.M 0 * e.Lt))
    (fun ι => by
      simp [lf55a, loopWordMat, LoopEnv.E, Matrix.mul_assoc])]
  simp

/-- (2.23) [eq:aver_local] in expectation for a sum of light weights with deterministic
coefficients: `|E Σ_x ⟨(𝒢_a - 𝔐_a) E_x⟩ c_x| ≤ N^{τ'} D B (N Im z_a)^{-1}` for `|c_x| ≤ B`. -/
private lemma Lf_wsum (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), ∀ e : LoopEnv D N, (μ, e) ∈ Bd_Cl D δA 1 K C N →
      (∀ a, Bd_zc D τ c₀ N e a) →
      ∀ (a : Fin 2) (B : ℝ) (c : Fin D → ℂ), 0 ≤ B → (∀ x, ‖c x‖ ≤ B) →
        ‖∫ h, ∑ x : Fin D, ntr ((e.G h a - e.M a) * Ea D N x) * c x ∂μ‖ ≤
          (N : ℝ) ^ τ' * (D * B * ((N : ℝ) * (e.z a).im)⁻¹) := by
  intro τ' hτ'
  have hD1 : 1 ≤ D := by omega
  have hW := Bd_weight D hD1 δA τ 1 hδA hτ le_rfl C (τ' / 2) (by positivity) 3 (by norm_num)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hW
  set Tt : ℝ := max 1 τ⁻¹ with hTt
  obtain ⟨N₂, hN₂⟩ := Bd_large (τ' / 2) 2 (by positivity)
  obtain ⟨N₃, hN₃⟩ := Bd_large 1 (4 * D * Tt) one_pos
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN μ e hx hz a B c hB hc => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hμ, hA, hA2, hcc, hδ⟩ := hx
  obtain ⟨-, hM, -, -, -, -⟩ := Bd_facts hD1 (by omega) le_rfl ⟨hμ, hA, hA2, hcc, hδ⟩ hz
  have := hμ.prob
  have hzp := (hz a).2.1
  have hzT : (e.z a).im ≤ Tt :=
    (Complex.im_le_norm _).trans ((hz a).1.1.trans (le_max_right _ _))
  have hzN : ∀ a, (N : ℝ)⁻¹ ≤ |(e.z a).im| := by
    intro a
    refine le_trans ?_ (hz a).1.2
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hb := fun x => hN₁ N hNa μ hμ e hA hcc (fun a => (hz a).1) a (Ea D N x) (Bd_opNorm_Ea D N x)
  choose bW hbW1 hbW2 using hb
  set bad := ⋃ x, bW x with hbad
  have hNDn : 0 ≤ (N : ℝ) ^ (-((3 : ℕ) : ℝ)) := by positivity
  have hmbad : μ.real bad ≤ D * (N : ℝ) ^ (-((3 : ℕ) : ℝ)) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    refine (Finset.sum_le_sum fun x _ => ENNReal.toReal_le_of_le_ofReal hNDn (hbW1 x)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set g := (N : ℝ) ^ (τ' / 2) * (1 / ((N : ℝ) * |(e.z a).im|)) with hg
  have hG : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → opNorm (e.G h a) ≤ N := by
    intro h hh
    refine (Bd_G_norm e h hh a (hz a).2.1.ne').trans ?_
    rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (hzN a)) (by positivity)]
    exact hzN a
  have hpt : ∀ᵐ h ∂μ, ‖∑ x : Fin D, ntr ((e.G h a - e.M a) * Ea D N x) * c x‖ ≤
      D * B * g + (toMeasurable μ bad).indicator (fun _ => D * B * (2 * N)) h := by
    filter_upwards [hμ.herm] with h hh
    have hcr : ∀ x, ‖ntr ((e.G h a - e.M a) * Ea D N x) * c x‖ ≤ 2 * N * B := by
      intro x
      rw [norm_mul]
      refine mul_le_mul ?_ (hc x) (norm_nonneg _) (by positivity)
      refine (Bd_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
      have h1 := Bd_opNorm_sub (e.G h a) (e.M a)
      have h2 := hG h hh
      have h3 := hM a
      have h0 := Bd_opNorm_nonneg (e.G h a - e.M a)
      calc opNorm (e.G h a - e.M a) * opNorm (Ea D N x) ≤ opNorm (e.G h a - e.M a) * 1 :=
            mul_le_mul_of_nonneg_left (Bd_opNorm_Ea D N x) h0
        _ ≤ 2 * N := by linarith
    by_cases hbm : h ∈ toMeasurable μ bad
    · rw [Set.indicator_of_mem hbm]
      have : ‖∑ x : Fin D, ntr ((e.G h a - e.M a) * Ea D N x) * c x‖ ≤ D * B * (2 * N) := by
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => hcr x).trans ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply le_of_eq; ring
      have : 0 ≤ D * B * g := by positivity
      linarith
    · rw [Set.indicator_of_notMem hbm, add_zero]
      have hgood : ∀ x, h ∉ bW x := fun x hm =>
        hbm (subset_toMeasurable _ _ (Set.mem_iUnion.mpr ⟨x, hm⟩))
      refine (norm_sum_le _ _).trans ?_
      have : ∀ x, ‖ntr ((e.G h a - e.M a) * Ea D N x) * c x‖ ≤ g * B := by
        intro x
        rw [norm_mul]
        exact mul_le_mul (hbW2 x h (hgood x)) (hc x) (norm_nonneg _) (by positivity)
      refine (Finset.sum_le_sum fun x _ => this x).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      apply le_of_eq; ring
  have hint : Integrable (fun h => D * B * g + (toMeasurable μ bad).indicator
      (fun _ => D * B * (2 * N)) h) μ := (integrable_const _).add
        ((integrable_const _).indicator (measurableSet_toMeasurable _ _))
  refine (norm_integral_le_of_norm_le hint hpt).trans ?_
  rw [integral_add (integrable_const _)
    ((integrable_const _).indicator (measurableSet_toMeasurable _ _)), integral_const,
    integral_indicator_const _ (measurableSet_toMeasurable _ _), probReal_univ, one_smul,
    smul_eq_mul]
  have hreal : μ.real (toMeasurable μ bad) = μ.real bad := by
    simp only [Measure.real, measure_toMeasurable]
  rw [hreal]
  rw [abs_of_pos hzp] at hg
  -- arithmetic
  have hq : 0 < ((N : ℝ) * (e.z a).im)⁻¹ := by positivity
  have hNτ2 : 2 ≤ (N : ℝ) ^ (τ' / 2) := hN₂ N hNb
  have hNτ : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hg' : g = (N : ℝ) ^ (τ' / 2) * ((N : ℝ) * (e.z a).im)⁻¹ := by rw [hg, one_div]
  have hbig : 4 * D * Tt ≤ N := by simpa using hN₃ N hNc
  have hTt1 : 1 ≤ Tt := le_max_left _ _
  have h3 : (N : ℝ) ^ (-((3 : ℕ) : ℝ)) = ((N : ℝ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast]
  rw [h3] at hmbad
  have hbad' : μ.real bad * (D * B * (2 * N)) ≤ 1 / 2 * (D * B * ((N : ℝ) * (e.z a).im)⁻¹) := by
    have h4 : μ.real bad * (D * B * (2 * N)) ≤ D * ((N : ℝ) ^ 3)⁻¹ * (D * B * (2 * N)) :=
      mul_le_mul_of_nonneg_right hmbad (by positivity)
    refine h4.trans ?_
    have h5 : ((N : ℝ) * (e.z a).im)⁻¹ ≥ ((N : ℝ) * Tt)⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hzT hNpos.le)
    have h6 : D * ((N : ℝ) ^ 3)⁻¹ * (D * B * (2 * N)) ≤
        1 / 2 * (D * B * ((N : ℝ) * Tt)⁻¹) := by
      have hDB : 0 ≤ (D : ℝ) * B := by positivity
      rw [show D * ((N : ℝ) ^ 3)⁻¹ * (D * B * (2 * N)) = (D * B) * (2 * D / N ^ 2) by
        field_simp]
      rw [show 1 / 2 * (D * B * ((N : ℝ) * Tt)⁻¹) = (D * B) * (1 / (2 * N * Tt)) by
        field_simp]
      refine mul_le_mul_of_nonneg_left ?_ hDB
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine h6.trans ?_
    have hDB : 0 ≤ (D : ℝ) * B := by positivity
    gcongr
  have hmain : D * B * g ≤ 1 / 2 * ((N : ℝ) ^ τ' * (D * B * ((N : ℝ) * (e.z a).im)⁻¹)) := by
    rw [hg', hNτ]
    have hY : 0 ≤ (D : ℝ) * B * ((N : ℝ) * (e.z a).im)⁻¹ := by positivity
    have hX0 : 0 ≤ (N : ℝ) ^ (τ' / 2) := by positivity
    have hXX : (N : ℝ) ^ (τ' / 2) ≤ 1 / 2 * ((N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2)) := by
      nlinarith
    calc D * B * ((N : ℝ) ^ (τ' / 2) * ((N : ℝ) * (e.z a).im)⁻¹)
        = (N : ℝ) ^ (τ' / 2) * (D * B * ((N : ℝ) * (e.z a).im)⁻¹) := by ring
      _ ≤ (1 / 2 * ((N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2))) *
          (D * B * ((N : ℝ) * (e.z a).im)⁻¹) := mul_le_mul_of_nonneg_right hXX hY
      _ = _ := by ring
  have hfin : 1 / 2 * (D * B * ((N : ℝ) * (e.z a).im)⁻¹) ≤
      1 / 2 * ((N : ℝ) ^ τ' * (D * B * ((N : ℝ) * (e.z a).im)⁻¹)) := by
    have h1 : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow (by linarith) hτ'.le
    have : 0 ≤ (D : ℝ) * B * ((N : ℝ) * (e.z a).im)⁻¹ := by positivity
    nlinarith
  linarith

/-- The resolvent of slot `a` at a flag depends on the flag of slot `a` only. -/
private lemma Lf_G_flag {D N : ℕ} (e : LoopEnv D N) (s s' : Fin 2 → Bool) (a : Fin 2)
    (h : Idx D N → Idx D N → ℂ) (hs : s a = s' a) :
    ({ e with s := s } : LoopEnv D N).G h a = ({ e with s := s' } : LoopEnv D N).G h a := by
  unfold LoopEnv.G
  simp only [hs]

/-- `‖𝔐 E 𝔐‖ ≤ (5/4)²`. -/
private lemma Lf_MEM {D N : ℕ} (P Q : Matrix (Idx D N) (Idx D N) ℂ) (hP : opNorm P ≤ 5 / 4)
    (hQ : opNorm Q ≤ 5 / 4) (x : Fin D) : opNorm (P * Ea D N x * Q) ≤ (5 / 4) ^ 2 := by
  refine (opNorm_mul_le _ _).trans ?_
  have h1 := (opNorm_mul_le P (Ea D N x)).trans
    (mul_le_mul hP (Bd_opNorm_Ea D N x) (Bd_opNorm_nonneg _) (by norm_num))
  have h0 := Bd_opNorm_nonneg (P * Ea D N x)
  calc opNorm (P * Ea D N x) * opNorm Q ≤ (5 / 4 * 1) * (5 / 4) :=
        mul_le_mul h1 hQ (Bd_opNorm_nonneg _) (by norm_num)
    _ = _ := by norm_num

/-- The pairing (5.58) [eq:polar2] for the leaves (5.55) [expansion_result_R_2_C_1_P_0]: a
difference of the expectations at two flags is the expectation of the difference of the
values. -/
private lemma Lf_pair {D N : ℕ} [Nonempty (Idx D N)] (T : LoopExpr) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (s s' : Fin 2 → Bool) (F : (Idx D N → Idx D N → ℂ) → ℂ)
    (hF : ∀ h, T.evalH { e with s := s } h - T.evalH { e with s := s' } h = F h) (B : ℝ)
    (hB : ‖∫ h, F h ∂μ‖ ≤ B) :
    ‖∫ h, T.evalH { e with s := s } h ∂μ - ∫ h, T.evalH { e with s := s' } h ∂μ‖ ≤ B := by
  have hi : ∀ s'' : Fin 2 → Bool, Integrable (fun h => T.evalH { e with s := s'' } h) μ :=
    fun s'' => GS_nice_integrable hμ (GS_nice_evalH T _ hz)
  rw [← integral_sub (hi s) (hi s')]
  simp only [hF]
  exact hB

/-- The second leaf of (5.55) summed over the four flags. -/
private lemma Lf_signed55b {D N : ℕ} [Nonempty (Idx D N)] (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Bw : ℝ)
    (hW : ∀ (s : Fin 2 → Bool) (B : ℝ) (c : Fin D → ℂ), 0 ≤ B → (∀ x, ‖c x‖ ≤ B) →
      ‖∫ h, ∑ x : Fin D, ntr ((({ e with s := s } : LoopEnv D N).G h 0 -
        ({ e with s := s } : LoopEnv D N).M 0) * Ea D N x) * c x ∂μ‖ ≤ Bw * B)
    (hM : ∀ (s : Fin 2 → Bool) a, opNorm (({ e with s := s } : LoopEnv D N).M a) ≤ 5 / 4) :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, lf55b.evalH { e with s := s } h ∂μ‖ ≤
      2 * (D * (Bw * (opNorm (MExt ((e.c 1 : ℂ) • lam D N e.A) (e.z 1) -
        (MExt ((e.c 1 : ℂ) • lam D N e.A) (e.z 1))ᴴ) * (5 / 4) ^ 2 * avgSq e.Lt))) := by
  set X₁ := MExt ((e.c 1 : ℂ) • lam D N e.A) (e.z 1) with hX₁
  set B := opNorm (X₁ - X₁ᴴ) * (5 / 4) ^ 2 * avgSq e.Lt with hB
  have hB0 : 0 ≤ B := by
    have := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
    have := Bd_opNorm_nonneg (X₁ - X₁ᴴ)
    positivity
  have key : ∀ s0 : Bool, ‖∫ h, lf55b.evalH { e with s := ![s0, false] } h ∂μ -
      ∫ h, lf55b.evalH { e with s := ![s0, true] } h ∂μ‖ ≤ D * (Bw * B) := by
    intro s0
    set e₀ : LoopEnv D N := { e with s := ![s0, false] } with he₀
    set c : Fin D → ℂ := fun x => ntr ((X₁ - X₁ᴴ) * e.Lt * (e₀.M 0 * Ea D N x * e₀.M 0) * e.Lt)
      with hc
    refine Lf_pair lf55b e hz μ hμ _ _ (fun h => (D : ℂ) * ∑ x : Fin D,
      ntr ((e₀.G h 0 - e₀.M 0) * Ea D N x) * c x) (fun h => ?_) _ ?_
    · rw [Lf_eval55b, Lf_eval55b]
      have hG : ({ e with s := ![s0, true] } : LoopEnv D N).G h 0 = e₀.G h 0 :=
        Lf_G_flag e _ _ 0 h rfl
      have hM0 : ({ e with s := ![s0, true] } : LoopEnv D N).M 0 = e₀.M 0 := by
        rw [Lf_M_flag e hz, he₀, Lf_M_flag e hz]
        rfl
      have hM1 : e₀.M 1 = X₁ := by rw [he₀, Lf_M_flag e hz]; rfl
      have hM1' : ({ e with s := ![s0, true] } : LoopEnv D N).M 1 = X₁ᴴ := by
        rw [Lf_M_flag e hz]; rfl
      rw [hG, hM0, hM1, hM1']
      have hLt : ∀ s' : Fin 2 → Bool, ({ e with s := s' } : LoopEnv D N).Lt = e.Lt :=
        fun _ => rfl
      simp only [hLt]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← mul_sub]
      congr 1
      simp only [hc, Matrix.sub_mul, ntr, Matrix.trace_sub, mul_sub]
      rfl
    · rw [integral_const_mul, norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine hW _ B c hB0 fun x => ?_
      refine (Tay_BL (Rch_Lt_herm e) _ _).trans ?_
      have h1 := Lf_MEM (e₀.M 0) (e₀.M 0) (hM _ 0) (hM _ 0) x
      have h0 := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
      have h2 := Bd_opNorm_nonneg (X₁ - X₁ᴴ)
      rw [hB]
      gcongr
  rw [Lf_sum_flags]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, one_mul, neg_one_mul]
  have e1 : ∫ h, lf55b.evalH { e with s := ![false, false] } h ∂μ +
      -∫ h, lf55b.evalH { e with s := ![false, true] } h ∂μ +
      -∫ h, lf55b.evalH { e with s := ![true, false] } h ∂μ +
      ∫ h, lf55b.evalH { e with s := ![true, true] } h ∂μ =
      (∫ h, lf55b.evalH { e with s := ![false, false] } h ∂μ -
        ∫ h, lf55b.evalH { e with s := ![false, true] } h ∂μ) -
      (∫ h, lf55b.evalH { e with s := ![true, false] } h ∂μ -
        ∫ h, lf55b.evalH { e with s := ![true, true] } h ∂μ) := by ring
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  have := key false
  have := key true
  linarith

/-- The first leaf of (5.55) summed over the four flags. -/
private lemma Lf_signed55a {D N : ℕ} [Nonempty (Idx D N)] (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Bw : ℝ)
    (hW : ∀ (s : Fin 2 → Bool) (B : ℝ) (c : Fin D → ℂ), 0 ≤ B → (∀ x, ‖c x‖ ≤ B) →
      ‖∫ h, ∑ x : Fin D, ntr ((({ e with s := s } : LoopEnv D N).G h 1 -
        ({ e with s := s } : LoopEnv D N).M 1) * Ea D N x) * c x ∂μ‖ ≤ Bw * B)
    (hM : ∀ (s : Fin 2 → Bool) a, opNorm (({ e with s := s } : LoopEnv D N).M a) ≤ 5 / 4) :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, lf55a.evalH { e with s := s } h ∂μ‖ ≤
      2 * (D * (Bw * (opNorm (MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0) -
        (MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0))ᴴ) * (5 / 4) ^ 2 * avgSq e.Lt))) := by
  set X₀ := MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0) with hX₀
  set B := opNorm (X₀ - X₀ᴴ) * (5 / 4) ^ 2 * avgSq e.Lt with hB
  have hB0 : 0 ≤ B := by
    have := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
    have := Bd_opNorm_nonneg (X₀ - X₀ᴴ)
    positivity
  have key : ∀ s1 : Bool, ‖∫ h, lf55a.evalH { e with s := ![false, s1] } h ∂μ -
      ∫ h, lf55a.evalH { e with s := ![true, s1] } h ∂μ‖ ≤ D * (Bw * B) := by
    intro s1
    set e₀ : LoopEnv D N := { e with s := ![false, s1] } with he₀
    set c : Fin D → ℂ := fun x => ntr ((e₀.M 1 * Ea D N x * e₀.M 1) * e.Lt * (X₀ - X₀ᴴ) * e.Lt)
      with hc
    refine Lf_pair lf55a e hz μ hμ _ _ (fun h => (D : ℂ) * ∑ x : Fin D,
      ntr ((e₀.G h 1 - e₀.M 1) * Ea D N x) * c x) (fun h => ?_) _ ?_
    · rw [Lf_eval55a, Lf_eval55a]
      have hG : ({ e with s := ![true, s1] } : LoopEnv D N).G h 1 = e₀.G h 1 :=
        Lf_G_flag e _ _ 1 h rfl
      have hM1 : ({ e with s := ![true, s1] } : LoopEnv D N).M 1 = e₀.M 1 := by
        rw [Lf_M_flag e hz, he₀, Lf_M_flag e hz]
        rfl
      have hM0 : e₀.M 0 = X₀ := by rw [he₀, Lf_M_flag e hz]; rfl
      have hM0' : ({ e with s := ![true, s1] } : LoopEnv D N).M 0 = X₀ᴴ := by
        rw [Lf_M_flag e hz]; rfl
      rw [hG, hM1, hM0, hM0']
      have hLt : ∀ s' : Fin 2 → Bool, ({ e with s := s' } : LoopEnv D N).Lt = e.Lt :=
        fun _ => rfl
      simp only [hLt]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← mul_sub]
      congr 1
      simp only [hc, Matrix.sub_mul, Matrix.mul_sub, ntr, Matrix.trace_sub, mul_sub]
      rfl
    · rw [integral_const_mul, norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine hW _ B c hB0 fun x => ?_
      refine (Tay_BL (Rch_Lt_herm e) _ _).trans ?_
      have h1 := Lf_MEM (e₀.M 1) (e₀.M 1) (hM _ 1) (hM _ 1) x
      have h0 := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
      have h2 := Bd_opNorm_nonneg (X₀ - X₀ᴴ)
      rw [hB, mul_comm (opNorm (X₀ - X₀ᴴ))]
      gcongr
  rw [Lf_sum_flags]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, one_mul, neg_one_mul]
  have e1 : ∫ h, lf55a.evalH { e with s := ![false, false] } h ∂μ +
      -∫ h, lf55a.evalH { e with s := ![false, true] } h ∂μ +
      -∫ h, lf55a.evalH { e with s := ![true, false] } h ∂μ +
      ∫ h, lf55a.evalH { e with s := ![true, true] } h ∂μ =
      (∫ h, lf55a.evalH { e with s := ![false, false] } h ∂μ -
        ∫ h, lf55a.evalH { e with s := ![true, false] } h ∂μ) -
      (∫ h, lf55a.evalH { e with s := ![false, true] } h ∂μ -
        ∫ h, lf55a.evalH { e with s := ![true, true] } h ∂μ) := by ring
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  have := key false
  have := key true
  linarith

/-! ## The four cases of the proof -/

/-- The slots are closed under a change of the flags. -/
private lemma Lf_slot_flag {D N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {k : ℕ} {ε : ℝ}
    {e : LoopEnv D N} (he : (∃ s, e = evecEnv D N A k ε s) ∨
      ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) (s : Fin 2 → Bool) :
    (∃ s', ({ e with s := s } : LoopEnv D N) = evecEnv D N A k ε s') ∨
      ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s', ({ e with s := s } : LoopEnv D N) = evalEnv D N A k ε t s' := by
  rcases he with ⟨s', rfl⟩ | ⟨t, ht, s', rfl⟩
  · exact Or.inl ⟨s, rfl⟩
  · exact Or.inr ⟨t, ht, s, rfl⟩

/-- A signed sum over the flags is bounded by four times a bound of its terms. -/
private lemma Lf_signed_le (I : (Fin 2 → Bool) → ℂ) (B : ℝ) (h : ∀ s, ‖I s‖ ≤ 1 / 4 * B) :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * I s‖ ≤ B := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ s : Fin 2 → Bool, ‖(if s 0 = s 1 then (1 : ℂ) else -1) * I s‖ ≤ 1 / 4 * B := by
    intro s
    rw [norm_mul]
    split_ifs <;> simpa using h s
  refine (Finset.sum_le_sum fun s _ => this s).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul]
  norm_num
  linarith

/-- The leaves bounded flag by flag, summed over the four flags. -/
private lemma Lf_core_flag (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (T : LoopExpr)
    (hI : Inv T) (h0 : T.kk 0 = 0) (h1 : T.kk 1 = 0) (hok : Lf_okB T = true) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            ∫ h, T.evalH { e with s := s } h ∂μ‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  intro τ hτ
  obtain ⟨N₀, hN₀⟩ := Lf_leaf_flag D hD δA εA ε hδA hεA hε hε' hε'' C T hI h0 h1 hok τ hτ
  exact ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs e he => Lf_signed_le _ _ fun s =>
    hN₀ N hN μ hμ A hA k hk hkN hhs _ (Lf_slot_flag he s)⟩

/-- The data of the slots used for the leaves (5.54) and (5.55): `‖M_a - M_a^*‖ ≲
N^{-1/3+ε/2} 𝔯(k)^{1/3}` by (A.3) [equation_z_im_m], and `⟨Λ̃²⟩ ≲ N^{-1} ‖A‖²_HS`. -/
private lemma Lf_slot_more (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) :
    ∃ c₀ K Cx Ca : ℝ, 0 < c₀ ∧ 0 ≤ Cx ∧ 0 ≤ Ca ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        (∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
          ∀ s : Fin 2 → Bool, (μ, ({ e with s := s } : LoopEnv D N)) ∈ Bd_Cl D δA 1 K C N) ∧
        (∀ (s : Fin 2 → Bool) a, Bd_zc D (ε / 2) c₀ N ({ e with s := s } : LoopEnv D N) a) ∧
        (∀ a, 0 < (e.z a).im ∧ (e.z a).im = etaK D N k ε) ∧
        (∀ a, opNorm (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) -
          (MExt ((e.c a : ℂ) • lam D N e.A) (e.z a))ᴴ) ≤
            Cx * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) ∧
        avgSq e.Lt ≤ Ca * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2 ∧
        (∀ (s : Fin 2 → Bool) a, opNorm (({ e with s := s } : LoopEnv D N).M a) ≤ 5 / 4) := by
  obtain ⟨c₀, K, Kg, C₇, CU, hc₀, hK, hKg, hC₇, hCU, N₁, hN₁⟩ :=
    Lf_slots D hD δA εA ε hδA hεA hε hε' hε'' 0
  refine ⟨c₀, K, 2 * (1 + CU) * (5 / 4) ^ 2, (1 + K ^ 2) * (4 * D), hc₀, by positivity,
    by positivity, max N₁ 1, ?_⟩
  intro N hN A hA k hk hkN hhs e he
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hrpos : (0 : ℝ) < rk D N k := by rw [Lf_rk_eq D N k hkN]; exact_mod_cast hk
  have hr1 : (1 : ℝ) ≤ rk D N k := by rw [Lf_rk_eq D N k hkN]; exact_mod_cast hk
  have hall := fun s => hN₁ N (le_trans (le_max_left _ _) hN) A hA k hk hkN hhs _
    (Lf_slot_flag he s)
  obtain ⟨hA2, hc, hz, hδ, hSF, heA, hU⟩ := hN₁ N (le_trans (le_max_left _ _) hN) A hA k hk hkN
    hhs e he
  have hσ0 : 0 ≤ avgSq (lam D N e.A) := Bd_avgSq_nonneg _ (lam_isHermitian D N e.A)
  refine ⟨fun μ hμ s => ?_, fun s a => ?_, fun a => ⟨(hz a).2.1, (hz a).2.2.1⟩, fun a => ?_, ?_,
    fun s a => (hall s).2.2.2.2.1.hM a⟩
  · obtain ⟨hA2', hc', -, hδ', -, heA', -⟩ := hall s
    exact ⟨hμ, heA' ▸ hA, by rw [mul_one]; exact hA2', hc', hδ'⟩
  · obtain ⟨-, -, hz', -⟩ := hall s
    exact ⟨(hz' a).1, (hz' a).2.1, (hz' a).2.2.2⟩
  · have hlamn : opNorm ((e.c a : ℂ) • lam D N e.A) ≤ 1 / 10 := by
      refine (Bd_lamc_norm D N e.A (e.c a)).trans ?_
      have := hc a
      have := Bd_opNorm_nonneg e.A
      nlinarith [abs_nonneg (e.c a)]
    have hMn := Bd_MExt_norm _ (Bd_lamc_herm D N e.A (e.c a)) hlamn (e.z a) (hz a).2.1.ne'
    refine (Lf_imM _ (Bd_lamc_herm D N e.A (e.c a)) (e.z a) (hz a).2.1 _ hMn).trans ?_
    have hη : (e.z a).im ≤ Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ) := by
      rw [(hz a).2.2.1]
      unfold etaK Lf_P
      refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith))
        (Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)) (by positivity) (by positivity)
    have hP := Lf_P_pos hNpos hrpos (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)
    have hsum : (e.z a).im + (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤
        (1 + CU) * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ) := by
      have := add_le_add hη (hU a)
      rw [heA] at this ⊢
      unfold Lf_P at this ⊢
      linarith
    calc 2 * ((e.z a).im + (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) * (5 / 4) ^ 2
        ≤ 2 * ((1 + CU) * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) * (5 / 4) ^ 2 := by
          gcongr
      _ = _ := by ring
  · have hntr := Lf_ntr_zero D N (lam D N e.A) (Tay_lam_blockTraceless D N e.A)
    have hLt : avgSq e.Lt = avgSq (lam D N e.A) + e.δ ^ 2 := by
      unfold LoopEnv.Lt
      exact Lf_avgSq_shift _ hntr e.δ
    have hσ1 := hSF.hσ1
    have hδ2 : e.δ ^ 2 ≤ K ^ 2 * avgSq (lam D N e.A) := by
      have h1 : |e.δ| ^ 2 ≤ (K * avgSq (lam D N e.A)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ 2
      rw [sq_abs] at h1
      have h3 : K ^ 2 * avgSq (lam D N e.A) * avgSq (lam D N e.A) ≤
          K ^ 2 * avgSq (lam D N e.A) * 1 := mul_le_mul_of_nonneg_left hσ1 (by positivity)
      nlinarith
    have h4 := Rg_avgSq_lam D N hD hN1 A
    rw [← heA] at h4
    have hP1 : Lf_P N (rk D N k) (-1) 0 = (N : ℝ)⁻¹ := by
      unfold Lf_P
      rw [Real.rpow_neg_one, Real.rpow_zero, mul_one]
    rw [hLt, hP1]
    have h5 : avgSq (lam D N e.A) ≤ 4 * D * (N : ℝ)⁻¹ * hsNorm A ^ 2 := by
      rw [heA] at h4 ⊢
      calc _ ≤ 4 * D * hsNorm A ^ 2 / N := h4
        _ = _ := by ring
    calc avgSq (lam D N e.A) + e.δ ^ 2 ≤ (1 + K ^ 2) * avgSq (lam D N e.A) := by nlinarith
      _ ≤ (1 + K ^ 2) * (4 * D * (N : ℝ)⁻¹ * hsNorm A ^ 2) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring

/-- The leaf (5.54) [expansion_result_R_2_C_0_P_0] summed over the four flags:
`≤ N^{τ+2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, by the pairing on both slots. -/
private lemma Lf_core54 (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            ∫ h, lf54.evalH { e with s := s } h ∂μ‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  intro τ hτ
  obtain ⟨c₀, K, Cx, Ca, hc₀, hCx, hCa, N₁, hN₁⟩ :=
    Lf_slot_more D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨N₂, hN₂⟩ := Bd_large (τ + ε) (Cx * Cx * Ca) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have := hμ.prob
  have hrpos : (0 : ℝ) < rk D N k := by rw [Lf_rk_eq D N k hkN]; exact_mod_cast hk
  obtain ⟨-, -, hz, hX, hav, -⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    hN) A hA k hk hkN hhs e he
  refine (Lf_signed54 e (fun a => (hz a).1) μ).trans ?_
  have hX0 := Bd_opNorm_nonneg (MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0) -
    (MExt ((e.c 0 : ℂ) • lam D N e.A) (e.z 0))ᴴ)
  have hav0 := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
  have hP := Lf_P_pos hNpos hrpos (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)
  have hbig := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  calc _ ≤ (Cx * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) *
        (Cx * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) *
        (Ca * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2) := by
        gcongr
        · exact hX 1
        · exact hX 0
    _ = Cx * Cx * Ca * ((N : ℝ) ^ (-(5 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ)) *
        hsNorm A ^ 2 := by
        have e1 := Lf_P_mul hNpos hrpos (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)
          (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)
        have e2 := Lf_P_mul hNpos hrpos (-(1 / 3 : ℝ) + ε / 2 + (-(1 / 3 : ℝ) + ε / 2))
          (1 / 3 + 1 / 3) (-1) 0
        have e3 : Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2 + (-(1 / 3 : ℝ) + ε / 2) + -1)
            (1 / 3 + 1 / 3 + 0) = (N : ℝ) ^ (-(5 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) := by
          unfold Lf_P; congr 2 <;> ring
        rw [← e3, ← e2, ← e1]
        ring
    _ ≤ (N : ℝ) ^ (τ + ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ)) *
        hsNorm A ^ 2 := by
        have : 0 ≤ (N : ℝ) ^ (-(5 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) := by positivity
        gcongr
    _ = _ := by
        rw [show (N : ℝ) ^ (τ + 2 * ε) = (N : ℝ) ^ (τ + ε) * (N : ℝ) ^ ε by
          rw [← Real.rpow_add hNpos]; ring_nf,
          show (N : ℝ) ^ (-(5 / 3 : ℝ) + ε) = (N : ℝ) ^ (-(5 / 3 : ℝ)) * (N : ℝ) ^ ε by
          rw [← Real.rpow_add hNpos]]
        ring

/-- The leaves (5.55) [expansion_result_R_2_C_1_P_0] summed over the four flags:
`≤ N^{τ+2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, from the pairing on the slot `b` and (2.23)
[eq:aver_local] for the light weight of the slot `a`. -/
private lemma Lf_core55 (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (T : LoopExpr) (a b : Fin 2)
    (hsig : ∀ (N : ℕ) [Nonempty (Idx D N)] (e : LoopEnv D N), (∀ a, 0 < (e.z a).im) →
      ∀ (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ],
      (∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) → ∀ Bw : ℝ,
      (∀ (s : Fin 2 → Bool) (B : ℝ) (c : Fin D → ℂ), 0 ≤ B → (∀ x, ‖c x‖ ≤ B) →
        ‖∫ h, ∑ x : Fin D, ntr ((({ e with s := s } : LoopEnv D N).G h a -
          ({ e with s := s } : LoopEnv D N).M a) * Ea D N x) * c x ∂μ‖ ≤ Bw * B) →
      (∀ (s : Fin 2 → Bool) a, opNorm (({ e with s := s } : LoopEnv D N).M a) ≤ 5 / 4) →
      ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
          ∫ h, T.evalH { e with s := s } h ∂μ‖ ≤
        2 * (D * (Bw * (opNorm (MExt ((e.c b : ℂ) • lam D N e.A) (e.z b) -
          (MExt ((e.c b : ℂ) • lam D N e.A) (e.z b))ᴴ) * (5 / 4) ^ 2 * avgSq e.Lt)))) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            ∫ h, T.evalH { e with s := s } h ∂μ‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  intro τ hτ
  obtain ⟨c₀, K, Cx, Ca, hc₀, hCx, hCa, N₁, hN₁⟩ :=
    Lf_slot_more D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨N₂, hN₂⟩ := Lf_wsum D hD δA (ε / 2) c₀ K hδA (by positivity) C (τ / 2) (by positivity)
  set Cst : ℝ := 2 * D * D * Cx * (5 / 4) ^ 2 * Ca with hCst
  obtain ⟨N₃, hN₃⟩ := Bd_large (τ / 2 + 5 * ε / 2) Cst (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have := hμ.prob
  have hrpos : (0 : ℝ) < rk D N k := by rw [Lf_rk_eq D N k hkN]; exact_mod_cast hk
  obtain ⟨hCl, hzc, hz, hX, hav, hM⟩ := hN₁ N hNa A hA k hk hkN hhs e he
  set Bw : ℝ := (N : ℝ) ^ (τ / 2) * (D * ((N : ℝ) * (e.z a).im)⁻¹) with hBw
  have hW : ∀ (s : Fin 2 → Bool) (B : ℝ) (c : Fin D → ℂ), 0 ≤ B → (∀ x, ‖c x‖ ≤ B) →
      ‖∫ h, ∑ x : Fin D, ntr ((({ e with s := s } : LoopEnv D N).G h a -
        ({ e with s := s } : LoopEnv D N).M a) * Ea D N x) * c x ∂μ‖ ≤ Bw * B := by
    intro s B c hB hc
    refine (hN₂ N hNb μ _ (hCl μ hμ s) (hzc s) a B c hB hc).trans (le_of_eq ?_)
    rw [hBw]
    ring
  refine (hsig N e (fun a => (hz a).1) μ hμ.herm Bw hW hM).trans ?_
  have hX0 := Bd_opNorm_nonneg (MExt ((e.c b : ℂ) • lam D N e.A) (e.z b) -
    (MExt ((e.c b : ℂ) • lam D N e.A) (e.z b))ᴴ)
  have hav0 := Bd_avgSq_nonneg _ (Rch_Lt_herm e)
  have hBw0 : 0 ≤ Bw := by
    have := (hz a).1
    positivity
  have hη : ((N : ℝ) * (e.z a).im)⁻¹ = Lf_P N (rk D N k) (-(1 / 3 : ℝ) - ε) (1 / 3 : ℝ) := by
    rw [(hz a).2, show etaK D N k ε = Lf_P N (rk D N k) (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)) from rfl]
    have e3 : Lf_P N (rk D N k) 1 0 = N := by unfold Lf_P; simp
    have e2 : (N : ℝ) * Lf_P N (rk D N k) (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)) =
        Lf_P N (rk D N k) (1 + (-(2 / 3 : ℝ) + ε)) (0 + -(1 / 3 : ℝ)) := by
      calc (N : ℝ) * Lf_P N (rk D N k) (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)) =
          Lf_P N (rk D N k) 1 0 * Lf_P N (rk D N k) (-(2 / 3 : ℝ) + ε) (-(1 / 3 : ℝ)) := by
            rw [e3]
        _ = _ := Lf_P_mul hNpos hrpos _ _ _ _
    rw [e2, Lf_P_inv hNpos hrpos]
    congr 1 <;> ring
  have hbig := hN₃ N hNc
  have hP0 := Lf_P_pos hNpos hrpos (-(5 / 3 : ℝ) - ε / 2) (2 / 3 : ℝ)
  calc 2 * (D * (Bw * (opNorm (MExt ((e.c b : ℂ) • lam D N e.A) (e.z b) -
        (MExt ((e.c b : ℂ) • lam D N e.A) (e.z b))ᴴ) * (5 / 4) ^ 2 * avgSq e.Lt)))
      ≤ 2 * (D * (Bw * ((Cx * Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)) *
        (5 / 4) ^ 2 * (Ca * Lf_P N (rk D N k) (-1) 0 * hsNorm A ^ 2)))) := by
        have hPa := Lf_P_pos hNpos hrpos (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ)
        have hPb := Lf_P_pos hNpos hrpos (-1) 0
        have hXb := hX b
        gcongr
    _ = Cst * (N : ℝ) ^ (τ / 2) * (Lf_P N (rk D N k) (-(1 / 3 : ℝ) - ε) (1 / 3 : ℝ) *
        Lf_P N (rk D N k) (-(1 / 3 : ℝ) + ε / 2) (1 / 3 : ℝ) * Lf_P N (rk D N k) (-1) 0) *
        hsNorm A ^ 2 := by
        rw [hBw, hη, hCst]
        ring
    _ = Cst * (N : ℝ) ^ (τ / 2) * Lf_P N (rk D N k) (-(5 / 3 : ℝ) - ε / 2) (2 / 3 : ℝ) *
        hsNorm A ^ 2 := by
        rw [Lf_P_mul hNpos hrpos, Lf_P_mul hNpos hrpos]
        congr 3 <;> ring
    _ ≤ (N : ℝ) ^ (τ / 2 + 5 * ε / 2) * (N : ℝ) ^ (τ / 2) *
        Lf_P N (rk D N k) (-(5 / 3 : ℝ) - ε / 2) (2 / 3 : ℝ) * hsNorm A ^ 2 := by
        gcongr
    _ = _ := by
        unfold Lf_P
        rw [show (N : ℝ) ^ (-(5 / 3 : ℝ) - ε / 2) = (N : ℝ) ^ (-(5 / 3 : ℝ)) *
            (N : ℝ) ^ (-(ε / 2)) by rw [← Real.rpow_add hNpos]; ring_nf]
        have e1 : (N : ℝ) ^ (τ / 2 + 5 * ε / 2) * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (-(ε / 2)) =
            (N : ℝ) ^ (τ + 2 * ε) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          ring_nf
        rw [← e1]
        ring

/-! ## The theorem -/

/-- The leaves with `k₁ = k₂ = 0` of the expansion of §5.3, (5.51)–(5.64): the signed sum over
the four starting loops of (5.29) [expansion_of_im] of the expectation of a leaf is at most
`N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemma 5.2
[lemma_localized_eigenvector_local_law] and, uniformly in `t ∈ [0, 1]`, of Lemma 5.4
[lemma_localized_eigenvalue_local_law]. -/
theorem loop_leaf_bound (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopIter ε n [loopStart]) (hk : T.kk 0 = 0 ∧ T.kk 1 = 0) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            ∫ h, T.evalH (evecEnv D N A k ε s) h ∂μ‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              ∫ h, T.evalH (evalEnv D N A k ε t s) h ∂μ‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  have hI := inv_of_mem hT
  obtain ⟨h0, h1⟩ := hk
  intro τ hτ
  have hmain : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            ∫ h, T.evalH { e with s := s } h ∂μ‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
    rcases leaf_cases hI h0 h1 with hg | hex
    · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C T hI h0 h1 (Lf_okB_of_genB hg) τ hτ
    · simp only [lfExc, List.mem_cons, List.not_mem_nil, or_false] at hex
      obtain ⟨h59, h60, h61a, h61b, h61c, h61d⟩ := Lf_okB_exc
      rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lf_core54 D hD δA εA ε hδA hεA hε hε' hε'' C τ hτ
      · exact Lf_core55 D hD δA εA ε hδA hεA hε hε' hε'' C lf55a 1 0
          (fun N _ e hz μ _ hμ Bw hW hM => Lf_signed55a e hz μ hμ Bw hW hM) τ hτ
      · exact Lf_core55 D hD δA εA ε hδA hεA hε hε' hε'' C lf55b 0 1
          (fun N _ e hz μ _ hμ Bw hW hM => Lf_signed55b e hz μ hμ Bw hW hM) τ hτ
      · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C _ hI h0 h1 h59 τ hτ
      · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C _ hI h0 h1 h60 τ hτ
      · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C _ hI h0 h1 h61a τ hτ
      · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C _ hI h0 h1 h61b τ hτ
      · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C _ hI h0 h1 h61c τ hτ
      · exact Lf_core_flag D hD δA εA ε hδA hεA hε hε' hε'' C _ hI h0 h1 h61d τ hτ
  obtain ⟨N₀, hN₀⟩ := hmain
  refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs => ⟨?_, fun t ht => ?_⟩⟩
  · exact hN₀ N hN μ hμ A hA k hk hkN hhs (evecEnv D N A k ε fun _ => false)
      (Or.inl ⟨_, rfl⟩)
  · exact hN₀ N hN μ hμ A hA k hk hkN hhs (evalEnv D N A k ε t fun _ => false)
      (Or.inr ⟨t, ht, _, rfl⟩)

end RBMTransitionEdge

end
