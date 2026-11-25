module

public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.Localized.Expansion.Terminate

@[expose] public section

/-!
# The reachable expressions of the expansion of §5.3 and the gain at the slots

The counting character `R` of (5.50) [counting_character_of_term], the invariants of the
expressions reached by the expansion, and the gain (5.5) [regular_estimate_localized_eigenvector],
(5.22) [regular_estimate_localized_eigenvalue] at the slots of Lemmas 5.2 and 5.4.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `R = S - m + n + 1` of (5.50) [counting_character_of_term], with `(m, n, u, S)` the characters
(5.37) [number_of_G_type_1]: on every path from the starting loop (5.30)
[starting_point_of_expansion] it is the number of operations `𝔯` (5.42) [sreplace_def]. -/
def LoopExpr.rcount (T : LoopExpr) : ℤ :=
  match T.charsZ with
  | (m, n, _, S) => S - m + n + 1

/-! ### The counts `k₁`, `k₂` on words -/

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
    (T.kk 0 = 0 → T'.kk 0 = 0)

/-- `KStep` with the trivial side condition implies it for every side condition. -/
private theorem KStep.of_true {T T' : LoopExpr} (p : Prop) (h : KStep T T' True) : KStep T T' p :=
  ⟨h.1, fun _ => h.2.1 trivial, h.2.2⟩

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
  rcases hoo with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
  · refine ⟨fun _ h => ?_, fun hn _ => ?_, fun h => by omega⟩
    · omega
    · have := hres hn
      omega
  · refine ⟨fun h => by omega, fun _ h => by omega, fun _ => ?_⟩
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
    · refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun h => by omega⟩
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
  · refine ⟨fun _ hk2 => ?_, fun _ _ => ?_, fun h => by omega⟩
    · rcases hcase with h | h <;> omega
    · omega
  · refine ⟨fun h => by omega, fun _ h => by omega, fun _ => ?_⟩
    rcases hcase with h | h <;> omega

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

/-- The invariants of the expressions reached by the expansion: in the class `𝒯`, `k₁ ≥ 1 ⇒ k₂ ≥ 1`,
`k₁ = 0 ⇒ R ≥ 1`, and the characters (5.50). -/
private def Reach (T : LoopExpr) : Prop :=
  T.wf = true ∧ (1 ≤ T.kk 0 → 1 ≤ T.kk 1) ∧ (T.kk 0 = 0 → 1 ≤ T.rcount) ∧ Cnt T

/-- The starting loop (5.30) [starting_point_of_expansion] has the invariants (`k₁ = k₂ = 1`,
`R = 0`). -/
private theorem reach_start : Reach loopStart :=
  ⟨by decide, fun _ => by decide, fun h => absurd h (by decide), 0, 0, 0, 0, 0, by decide⟩

/-- Every term of (5.40) [expansion_for_integral_by_part_term] of an expression with the
invariants has them. -/
private theorem reach_step {T T' : LoopExpr} (hR : Reach T) (h : T' ∈ T.step) : Reach T' := by
  obtain ⟨hw, h2, h3, hC⟩ := hR
  have hwf := loop_step_wf T hw T' h
  simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨op, -, h⟩ := h
  have hk := kstep_apply hw op h
  obtain ⟨hC', hr⟩ := cnt_apply op h hC
  have hnn := hC.rcount_nonneg
  refine ⟨hwf, ?_, ?_, hC'⟩
  · intro h1'
    by_cases hk0 : 1 ≤ T.kk 0
    · exact hk.1 hk0 (h2 hk0)
    · exfalso
      have := hk.2.2 (by omega)
      omega
  · intro h0'
    by_cases hk0 : 1 ≤ T.kk 0
    · by_cases hrep : op = .rep
      · subst hrep
        simp at hr
        omega
      · have := hk.2.1 hrep hk0
        omega
    · have h5 := h3 (by omega)
      split_ifs at hr <;> omega

/-- The invariants pass to every expression of the next round. -/
private theorem reach_next (ε : ℝ) {L : List LoopExpr} (hL : ∀ T ∈ L, Reach T) :
    ∀ T ∈ L.flatMap (fun T => if T.Stopped ε then [T] else T.step), Reach T := by
  intro T' hT'
  obtain ⟨T, hT, h⟩ := List.mem_flatMap.1 hT'
  by_cases hs : T.Stopped ε
  · simp only [hs, ite_true, List.mem_singleton] at h
    subst h
    exact hL _ hT
  · simp only [hs, ite_false] at h
    exact reach_step (hL _ hT) h

/-- The invariants hold on every expression of `loopIter` (5.49) [operation_sequence]. -/
private theorem reach_iter (ε : ℝ) :
    ∀ (n : ℕ) (L : List LoopExpr), (∀ T ∈ L, Reach T) → ∀ T ∈ loopIter ε n L, Reach T
  | 0, _, hL, T, hT => hL T hT
  | n + 1, _, hL, T, hT => reach_iter ε n _ (reach_next ε hL) T hT

/-- The invariants hold on every expression of `loopInner`. -/
private theorem reach_inner (ε : ℝ) :
    ∀ (n : ℕ) (L : List LoopExpr), (∀ T ∈ L, Reach T) → ∀ T ∈ loopInner ε n L, Reach T
  | 0, _, _, T, hT => by simp [loopInner] at hT
  | n + 1, _, hL, T, hT => by
    simp only [loopInner, List.mem_append, List.mem_filter] at hT
    rcases hT with hT | hT
    · exact hL T hT.1
    · exact reach_inner ε n _ (reach_next ε hL) T hT

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

/-- The conjugate transpose of the normalized trace: `⟨B^*⟩ = conj ⟨B⟩`. -/
private lemma Rch_ntr_conjTranspose {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) :
    ntr Bᴴ = star (ntr B) := by
  simp [ntr, Matrix.trace_conjTranspose, star_mul']

/-- Cyclicity of the normalized trace. -/
private lemma Rch_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  unfold ntr
  rw [Matrix.trace_mul_comm]

/-- Taking the adjoint swaps the order of a trace `⟨𝔐_b Λ̃ 𝔐_a E⟩` with Hermitian `Λ̃`, `E`: the
norm of `⟨M₁ L M₀ E⟩` is that of `⟨M₀^* L M₁^* E⟩`. -/
private lemma Rch_swap {ι : Type*} [Fintype ι] (M₀ M₁ L E : Matrix ι ι ℂ) (hL : L.IsHermitian)
    (hE : E.IsHermitian) : ‖ntr (M₁ * L * M₀ * E)‖ = ‖ntr (M₀ᴴ * L * M₁ᴴ * E)‖ := by
  have h1 : ntr (M₀ᴴ * L * M₁ᴴ * E) = star (ntr (M₁ * L * M₀ * E)) := by
    rw [← Rch_ntr_conjTranspose]
    simp only [Matrix.conjTranspose_mul, hL.eq, hE.eq]
    rw [Rch_ntr_comm]
    simp only [Matrix.mul_assoc]
  rw [h1, norm_star]

/-- `Ea` is Hermitian. -/
private lemma Rch_Ea_herm (D N : ℕ) (x : Fin D) : (Ea D N x).IsHermitian := by
  unfold Ea
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  ext p
  by_cases h : p.1 = x <;> simp [h]

/-- The slot-dependent traces of `Λ̃`: `Λ̃ = Λ - δ` is Hermitian. -/
private lemma Rch_Lt_herm {D N : ℕ} (e : LoopEnv D N) : e.Lt.IsHermitian := by
  unfold LoopEnv.Lt
  refine (lam_isHermitian D N e.A).sub ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- Every expression reached by the expansion of §5.3 or expanded in it lies in the class `𝒯` of
(5.33) [definition_class_of_expression_loop], has `k₂ ≥ 1` when `k₁ ≥ 1`, has `R ≥ 1` when
`k₁ = 0`, and its characters satisfy (5.50) [counting_character_of_term]. -/
theorem loop_reach (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) :
    T.wf = true ∧ (1 ≤ T.kk 0 → 1 ≤ T.kk 1) ∧ (T.kk 0 = 0 → 1 ≤ T.rcount) ∧
      ∃ R C₁ C₂ P₁ P₂ : ℕ, T.charsZ = ((2 : ℤ) - R + C₂ + 2 * P₁ + P₂, (1 : ℤ) + C₂ - P₂,
        (C₁ : ℤ) - P₁, 2 * (P₁ : ℤ) + 2 * P₂) := by
  have hs : ∀ T ∈ [loopStart], Reach T := by
    intro T hT
    rw [List.mem_singleton.1 hT]
    exact reach_start
  have hR : Reach T := by
    rcases hT with h | h
    · exact reach_iter ε n _ hs T h
    · exact reach_inner ε n _ hs T h
  obtain ⟨h1, h2, h3, R, C₁, C₂, P₁, P₂, h4⟩ := hR
  exact ⟨h1, h2, h3, R, C₁, C₂, P₁, P₂, h4⟩

/-- (5.5) [regular_estimate_localized_eigenvector] and (5.22)
[regular_estimate_localized_eigenvalue] at the slots: `⟨𝔐_a Λ̃ 𝔐_b E_x⟩ = O(Im m ⟨Λ²⟩)` for
`a ≠ b`, every flag and both orders, with `Im m` of slot `1`. -/
theorem loop_env_gain (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ (a b : Fin 2) (x : Fin D), a ≠ b →
        ‖ntr (e.M a * e.Lt * e.M b * Ea D N x)‖ ≤
          K * ((mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im * avgSq (lam D N e.A)) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := regular_estimate_localized_eigenvector D hD δA εA ε hδA hεA hε hε'
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := regular_estimate_localized_eigenvalue D hD δA εA ε hδA hεA hε hε'
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, max (max N₁ N₂) 1, ?_⟩
  intro N hN A hA k hk hkN hhs e he a b x hab
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hD0 : 0 < D := by omega
  have hDN : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hN1)
  have hkDN : k ≤ D * N := by omega
  have hrk : 0 < rk D N k := by
    unfold rk
    exact_mod_cast lt_min hk (by omega)
  have hη : 0 < etaK D N k ε := by
    unfold etaK
    positivity
  have hab' : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    fin_cases a <;> fin_cases b <;> simp_all
  have hEherm := Rch_Ea_herm D N x
  have hmax1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hmax2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  have : Nonempty (Idx D N) := ⟨(⟨0, hD0⟩, ⟨0, hN1⟩)⟩
  rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
  · -- the slots of Lemma 5.2
    obtain ⟨-, -, -, hmain⟩ := h₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
      A hA k hk hkDN hhs
    set z₁ := zOne (lam D N A) k ε with hz₁
    set Δ := shiftEv (lam D N A) z₁ with hΔ
    have hz1pos : 0 < z₁.im := by simp [hz₁, zOne, hη]
    have hz0pos : 0 < (z₁ - (Δ : ℂ)).im := by simpa using hz1pos
    have hext : mExt (lam D N A) z₁ = mSol (lam D N A) z₁ := by simp [mExt, hz1pos]
    have hrhs : (mSol ((((evecEnv D N A k ε s).c 1 : ℝ) : ℂ) • lam D N (evecEnv D N A k ε s).A)
        ((evecEnv D N A k ε s).z 1)).im = (mExt (lam D N A) z₁).im := by
      rw [hext]
      simp [evecEnv, hz₁]
    have hM0 : (evecEnv D N A k ε s).M 0 =
        (if s 0 then star (msc (z₁ - (Δ : ℂ))) else msc (z₁ - (Δ : ℂ))) •
          (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
      have := Rch_slot_zero D N hD0 hN1 A (z₁ - (Δ : ℂ)) hz0pos (s 0)
      simpa [LoopEnv.M, evecEnv, hz₁, hΔ] using this
    have hM1 : (evecEnv D N A k ε s).M 1 =
        if s 1 then (MExt (lam D N A) z₁)ᴴ else MExt (lam D N A) z₁ := by
      have h2 := Rch_flag (lam D N A) (lam_isHermitian D N A) z₁ hz1pos.ne' (s 1)
      rw [← h2]
      change MExt (((1 : ℝ) : ℂ) • lam D N A) _ = _
      rw [Complex.ofReal_one, one_smul]
      rfl
    have hLt : (evecEnv D N A k ε s).Lt =
        lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) := rfl
    have hP : 0 ≤ (mExt (lam D N A) z₁).im * avgSq (lam D N A) := by
      have := (norm_nonneg _).trans (hmain x false false)
      exact (mul_nonneg_iff_of_pos_left hC₁).1 this
    rw [hrhs]
    change _ ≤ max C₁ C₂ * ((mExt (lam D N A) z₁).im * avgSq (lam D N A))
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hmax1 hP)
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hM0, hM1, hLt]
      have := hmain x (s 0) (s 1)
      simpa only [Matrix.smul_mul, one_mul] using this
    · rw [Rch_swap _ _ _ _ (Rch_Lt_herm _) hEherm]
      have hM0h : ((evecEnv D N A k ε s).M 0)ᴴ =
          (if (!s 0) then star (msc (z₁ - (Δ : ℂ))) else msc (z₁ - (Δ : ℂ))) •
            (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
        cases h : s 0 <;> simp [hM0, h, Matrix.conjTranspose_smul]
      have hM1h : ((evecEnv D N A k ε s).M 1)ᴴ =
          if (!s 1) then (MExt (lam D N A) z₁)ᴴ else MExt (lam D N A) z₁ := by
        cases h : s 1 <;> simp [hM1, h]
      rw [hM0h, hM1h, hLt]
      have := hmain x (!s 0) (!s 1)
      simpa only [Matrix.smul_mul, one_mul] using this
  · -- the slots of Lemma 5.4
    obtain ⟨-, hmain⟩ := h₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
      A hA k hk hkDN hhs t ht
    set zt := zOne ((t : ℂ) • lam D N A) k ε with hzt
    have hztpos : 0 < zt.im := by simp [hzt, zOne, hη]
    have hext : mExt ((t : ℂ) • lam D N A) zt = mSol ((t : ℂ) • lam D N A) zt := by
      simp [mExt, hztpos]
    have hherm : ((t : ℂ) • lam D N A).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (lam_isHermitian D N A).eq]
      simp
    have hrhs : (mSol ((((evalEnv D N A k ε t s).c 1 : ℝ) : ℂ) •
        lam D N (evalEnv D N A k ε t s).A) ((evalEnv D N A k ε t s).z 1)).im =
        (mExt ((t : ℂ) • lam D N A) zt).im := by
      rw [hext]
      simp [evalEnv, hzt]
    have hM : ∀ a : Fin 2, (evalEnv D N A k ε t s).M a =
        if s a then (MExt ((t : ℂ) • lam D N A) zt)ᴴ else MExt ((t : ℂ) • lam D N A) zt := by
      intro a
      rw [← Rch_flag _ hherm zt hztpos.ne' (s a)]
      fin_cases a <;> rfl
    have hLt : (evalEnv D N A k ε t s).Lt = lam D N A -
        (shiftT (lam D N A) k ε t : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) := rfl
    have hP : 0 ≤ (mExt ((t : ℂ) • lam D N A) zt).im * avgSq (lam D N A) := by
      have := (norm_nonneg _).trans (hmain x false false)
      exact (mul_nonneg_iff_of_pos_left hC₂).1 this
    rw [hrhs]
    change _ ≤ max C₁ C₂ * ((mExt ((t : ℂ) • lam D N A) zt).im * avgSq (lam D N A))
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hmax2 hP)
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hM, hM, hLt]
      exact hmain x (s 0) (s 1)
    · rw [hM, hM, hLt]
      exact hmain x (s 1) (s 0)

end RBMTransitionEdge

end
