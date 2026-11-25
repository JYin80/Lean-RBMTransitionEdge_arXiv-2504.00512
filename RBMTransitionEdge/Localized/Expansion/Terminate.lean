module

public import RBMTransitionEdge.Localized.Expansion.Words

@[expose] public section

/-!
# Termination of the expansion of §5.3

The quantity `Ψ`, the stopping rule built from criterion (ii) above (5.49) [operation_sequence],
the rounds of the expansion of the starting loop (5.30) [starting_point_of_expansion], and the
statement that the expansion stops after a number of rounds that depends on `ε` only.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `Ψ(𝒯) = (size₁ - size₂) + ε (size₂ + 2)`; `Ψ ≥ 4` implies
`N^{-size₁} η^{-size₂-2} ≤ D^{(size₂+2)/3} N^{-2}` for `η ≥ D^{-1/3} N^{-1+ε}`, the bound of the
stopping criterion (i) above (5.49) [operation_sequence]. -/
def LoopExpr.psi (ε : ℝ) (T : LoopExpr) : ℝ :=
  ((T.size.1 - T.size.2 : ℤ) : ℝ) + ε * ((T.size.2 + 2 : ℤ) : ℝ)

/-- The stopping rule: `Ψ(𝒯) ≥ 4`, or criterion (ii) above (5.49) [operation_sequence],
`k₁ = k₂ = 0`. -/
def LoopExpr.Stopped (ε : ℝ) (T : LoopExpr) : Prop :=
  4 ≤ T.psi ε ∨ (T.kk 0 = 0 ∧ T.kk 1 = 0)

/-- The expressions after `n` rounds of the expansion: each expression that is not stopped is
replaced by the terms of (5.40) [expansion_for_integral_by_part_term]. -/
def loopIter (ε : ℝ) : ℕ → List LoopExpr → List LoopExpr
  | 0, L => L
  | n + 1, L => loopIter ε n (L.flatMap fun T => if T.Stopped ε then [T] else T.step)

/-- The expressions expanded during `n` rounds, each contributing its remainder (5.41)
[reminder_terms_expansion]. -/
def loopInner (ε : ℝ) : ℕ → List LoopExpr → List LoopExpr
  | 0, _ => []
  | n + 1, L => L.filter (fun T => decide (¬ T.Stopped ε)) ++
      loopInner ε n (L.flatMap fun T => if T.Stopped ε then [T] else T.step)

/-! ### Auxiliary facts on words -/

/-- The letter `x` is a resolvent `𝒢_a`. -/
private def resB (x : LoopLetter) : Bool :=
  match x with | .res _ => true | _ => false

/-- The letter `x` is one of `Λ̃₁`, `Λ̃₂`. -/
private def lamtB (x : LoopLetter) : Bool :=
  match x with | .lamt _ => true | _ => false

/-- The sum over the loops of the number of resolvents times the number of `Λ̃` in the loop. -/
private def phiL (T : LoopExpr) : ℕ :=
  (T.loops.map fun w => w.countP resB * w.countP lamtB).sum

/-- Replacing the entry `w` at position `i` of a list changes a sum of values by the difference of
the values. -/
private theorem sum_map_set' {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (i : ℕ) (w x : α), l[i]? = some w →
      ((l.set i x).map f).sum + f w = (l.map f).sum + f x
  | [], i, w, x, h => by simp at h
  | y :: l, 0, w, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
  | y :: l, i + 1, w, x, h => by
      have := sum_map_set' f l i w x (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- The prefix `tl[..q]` and the suffix `tl[q..]` of a word overlap exactly in the letter `tl[q]`,
for every count of letters. -/
private theorem countP_take_drop' (P : LoopLetter → Bool) (tl : List LoopLetter) (q : ℕ)
    (x : LoopLetter) (h : tl[q]? = some x) :
    (tl.take (q + 1)).countP P + (tl.drop q).countP P =
      tl.countP P + (if P x then 1 else 0) := by
  have h1 : tl.take (q + 1) = tl.take q ++ [x] := by rw [List.take_add_one, h]; rfl
  have h4 := congrArg (List.countP P) (List.take_append_drop q tl)
  rw [List.countP_append] at h4
  rw [h1, List.countP_append, ← h4]
  by_cases hx : P x = true
  · simp [hx]; omega
  · simp [hx]

/-- The data returned by `focus`: the focused loop `w` is a permutation of `𝒢_a · tl`, and `tl`
has a `Λ̃` at a position `j₀` before which it has no resolvent (`𝒢_a` is the first resolvent to the
left of `Λ̃_o`, (5.38) [explicit_cT]). -/
private theorem focus_spec' {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ w : List LoopLetter, T.loops[ℓ]? = some w ∧ w.Perm (.res a :: tl) ∧
      ∃ j₀ : ℕ, ∃ o : Fin 2, tl[j₀]? = some (.lamt o) ∧
        ∀ k < j₀, ∀ x, tl[k]? = some x → resB x = false := by
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
          refine ⟨w, hw, ?_, ?_⟩
          · rw [← hrot]; exact (List.rotate_perm w r).symm
          · obtain ⟨hlt, hwe⟩ := List.getElem?_eq_some_iff.1 hw
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
            refine ⟨j₁, o, ?_, ?_⟩
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
              cases x <;> simp_all [resB]
        · cases h
      · cases h

/-- Under `𝔠₂` (5.44) [scut_2] the sum over the loops of (resolvents) × (`Λ̃`) drops. -/
private theorem phiL_cut2 (T T' : LoopExpr) (h : T' ∈ T.apply .cut2) : phiL T' < phiL T := by
  simp only [LoopExpr.apply] at h
  split at h
  · simp at h
  · rename_i ℓ a tl hf
    obtain ⟨w, hw, hperm, j₀, o, hj₀, hpre⟩ := focus_spec' hf
    obtain ⟨q, -, h5⟩ := List.mem_filterMap.1 h
    split at h5
    · rename_i b hq
      simp only [Option.some.injEq] at h5
      subst h5
      have hq0 : j₀ < q := by
        rcases lt_trichotomy j₀ q with h | h | h
        · exact h
        · subst h; rw [hj₀] at hq; cases hq
        · have := hpre q h _ hq; simp [resB] at this
      have hl1 : 1 ≤ (tl.take (q + 1)).countP lamtB := by
        apply List.countP_pos_iff.2
        refine ⟨.lamt o, ?_, rfl⟩
        apply List.mem_of_getElem? (i := j₀)
        simp only [List.getElem?_take, show j₀ < q + 1 by omega, ite_true, hj₀]
      have hr1 : 1 ≤ (tl.take (q + 1)).countP resB := by
        apply List.countP_pos_iff.2
        refine ⟨.res b, ?_, rfl⟩
        rw [List.take_add_one, hq]; simp
      have hr2 : (tl.take (q + 1)).countP resB ≤ tl.countP resB :=
        (List.take_sublist _ _).countP_le
      have h6 := countP_take_drop' resB tl q _ hq
      have h7 := countP_take_drop' lamtB tl q _ hq
      simp only [resB, lamtB, ite_true, Bool.false_eq_true, ite_false, add_zero] at h6 h7
      have h1 := sum_map_set' (fun w => w.countP resB * w.countP lamtB) T.loops ℓ w
        (.det a :: tl.take (q + 1) ++ [.proj T.nb]) hw
      have h2 := hperm.countP_eq resB
      have h3 := hperm.countP_eq lamtB
      beta_reduce at h1
      simp only [phiL, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      simp only [List.countP_cons, List.countP_append, List.countP_nil, resB, lamtB] at h1 h2 h3 ⊢
      simp only [ite_true, Bool.false_eq_true, ite_false, add_zero, zero_add] at h1 h2 h3 ⊢
      rw [h2, h3] at h1
      set R := tl.countP resB
      set Λ := tl.countP lamtB
      set r₁ := (tl.take (q + 1)).countP resB
      set d := (tl.drop q).countP resB
      set l₁ := (tl.take (q + 1)).countP lamtB
      set l₂ := (tl.drop q).countP lamtB
      have hd : d + 1 ≤ R + 1 := by omega
      have e1 : r₁ * l₁ + l₁ ≤ (R + 1) * l₁ := by nlinarith
      have e2 : (d + 1) * l₂ ≤ (R + 1) * l₂ := Nat.mul_le_mul_right _ hd
      have e3 : (R + 1) * Λ = (R + 1) * l₁ + (R + 1) * l₂ := by rw [← h7, Nat.mul_add]
      omega
    · simp at h5

/-! ### Sizes along the operations -/

/-- The size (5.47) [eq:sizeT] read off the characters. -/
private theorem size_eq (T : LoopExpr) :
    T.size = (T.charsZ.2.2.2 + T.charsZ.2.2.1, T.charsZ.1 - T.charsZ.2.1 + T.charsZ.2.2.1) := by
  unfold LoopExpr.size
  generalize T.charsZ = c
  obtain ⟨m, n, u, S⟩ := c
  rfl

/-- The first component `S + u` of the size is nonnegative. -/
private theorem size_fst_nonneg (T : LoopExpr) : 0 ≤ T.size.1 := by
  rw [size_eq]
  change (0 : ℤ) ≤ ((T.S : ℕ) : ℤ) + ((T.weights.length : ℕ) : ℤ)
  positivity

/-- The change of `(size₁, size₁ - size₂)` under one operation, from Table 1
[table_effect_of_operations]. -/
private theorem apply_size (T T' : LoopExpr) (o : LoopOp) (h : T' ∈ T.apply o) :
    T'.size.1 = T.size.1 + (o.delta.2.2.2 + o.delta.2.2.1) ∧
      T'.size.1 - T'.size.2 = T.size.1 - T.size.2 + (o.delta.2.2.2 - o.delta.1 + o.delta.2.1) := by
  have h1 := loop_table1 T o T' h
  rw [size_eq, size_eq T, h1]
  simp only [Prod.fst_add, Prod.snd_add]
  constructor <;> ring

/-! ### Rounds of the expansion -/

/-- The rounds of the expansion split along a concatenation. -/
private theorem loopIter_append (ε : ℝ) :
    ∀ (n : ℕ) (L₁ L₂ : List LoopExpr),
      loopIter ε n (L₁ ++ L₂) = loopIter ε n L₁ ++ loopIter ε n L₂
  | 0, _, _ => rfl
  | n + 1, L₁, L₂ => by
      simp only [loopIter, List.flatMap_append]
      exact loopIter_append ε n _ _

/-- `m + k` rounds are `m` rounds followed by `k` rounds. -/
private theorem loopIter_add (ε : ℝ) :
    ∀ (m k : ℕ) (L : List LoopExpr), loopIter ε (m + k) L = loopIter ε k (loopIter ε m L)
  | 0, k, L => by simp [loopIter]
  | m + 1, k, L => by
      rw [show m + 1 + k = (m + k) + 1 by omega]
      simp only [loopIter]
      exact loopIter_add ε m k _

/-- A list of stopped expressions is unchanged by the rounds. -/
private theorem loopIter_of_stopped (ε : ℝ) :
    ∀ (k : ℕ) (L : List LoopExpr), (∀ T ∈ L, T.Stopped ε) → loopIter ε k L = L
  | 0, _, _ => rfl
  | k + 1, L, hL => by
      have : (L.flatMap fun T => if T.Stopped ε then [T] else T.step) = L := by
        clear k
        induction L with
        | nil => rfl
        | cons T L ih =>
          simp only [List.flatMap_cons, hL T List.mem_cons_self, ite_true]
          rw [ih (fun T' h => hL T' (List.mem_cons_of_mem _ h))]
          rfl
      simp only [loopIter]
      rw [this]
      exact loopIter_of_stopped ε k L hL

/-- Once all expressions are stopped, they stay stopped in later rounds. -/
private theorem loopIter_mono (ε : ℝ) {m k : ℕ} {L : List LoopExpr} (hmk : m ≤ k)
    (h : ∀ T ∈ loopIter ε m L, T.Stopped ε) : ∀ T ∈ loopIter ε k L, T.Stopped ε := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [loopIter_add, loopIter_of_stopped ε j _ h]
  exact h

/-- If the expansion of each member of a list stops, the expansion of the list stops. -/
private theorem loopIter_list (ε : ℝ) :
    ∀ L : List LoopExpr, (∀ c ∈ L, ∃ n, ∀ T ∈ loopIter ε n [c], T.Stopped ε) →
      ∃ n, ∀ T ∈ loopIter ε n L, T.Stopped ε
  | [], _ => ⟨0, by simp [loopIter]⟩
  | c :: L, h => by
      obtain ⟨n₁, h₁⟩ := h c List.mem_cons_self
      obtain ⟨n₂, h₂⟩ := loopIter_list ε L (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
      refine ⟨max n₁ n₂, ?_⟩
      rw [show c :: L = [c] ++ L from rfl, loopIter_append]
      intro T hT
      rcases List.mem_append.1 hT with hT | hT
      · exact loopIter_mono ε (le_max_left _ _) h₁ T hT
      · exact loopIter_mono ε (le_max_right _ _) h₂ T hT

/-- A round turns an expression that is not stopped into its terms (5.40)
[expansion_for_integral_by_part_term]. -/
private theorem loopIter_succ_single (ε : ℝ) (n : ℕ) (T : LoopExpr) (hs : ¬ T.Stopped ε) :
    loopIter ε (n + 1) [T] = loopIter ε n T.step := by
  simp [loopIter, hs]

/-! ### The measure -/

/-- An expression that is not stopped, with `size₁ - size₂ ≥ -1`, has `size₁ < 5/ε` and
`size₁ - size₂ + 1 < 5/(1 - ε)`. -/
private theorem bounds_of_not_stopped (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (T : LoopExpr)
    (hb : -1 ≤ T.size.1 - T.size.2) (hs : ¬ T.Stopped ε) :
    (T.size.1 : ℝ) < 5 / ε ∧ ((T.size.1 - T.size.2 + 1 : ℤ) : ℝ) < 5 / (1 - ε) := by
  have h4 : T.psi ε < 4 := by
    by_contra h
    exact hs (Or.inl (not_lt.1 h))
  have ha : (0 : ℝ) ≤ T.size.1 := by exact_mod_cast size_fst_nonneg T
  have hb' : (-1 : ℝ) ≤ (T.size.1 : ℝ) - T.size.2 := by exact_mod_cast hb
  unfold LoopExpr.psi at h4
  push_cast at h4 ⊢
  constructor
  · rw [lt_div_iff₀ hε]
    have hb1 : (0 : ℝ) ≤ T.size.1 - T.size.2 + 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hε'.le) hb1]
  · rw [lt_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hε.le ha]

/-- The expansion of every expression with `size₁ - size₂ ≥ -1` stops: induction on the
lexicographic measure (gains left, `𝔯` left, resolvents × `Λ̃` of the loops). -/
private theorem terminates_aux (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (A R : ℕ)
    (hA : 5 / ε < A) (hR : 5 / (1 - ε) < R) :
    ∀ x y z : ℕ, ∀ T : LoopExpr, -1 ≤ T.size.1 - T.size.2 →
      ((A : ℤ) - T.size.1).toNat = x → ((R : ℤ) - (T.size.1 - T.size.2 + 1)).toNat = y →
      phiL T = z → ∃ n, ∀ T' ∈ loopIter ε n [T], T'.Stopped ε := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x IHx =>
  intro y
  induction y using Nat.strong_induction_on with
  | _ y IHy =>
  intro z
  induction z using Nat.strong_induction_on with
  | _ z IHz =>
  intro T hb hx hy hz
  by_cases hs : T.Stopped ε
  · exact ⟨0, by simp [loopIter, hs]⟩
  obtain ⟨haA, hbR⟩ := bounds_of_not_stopped ε hε hε' T hb hs
  have haA' : T.size.1 < (A : ℤ) := by exact_mod_cast haA.trans hA
  have hbR' : T.size.1 - T.size.2 + 1 < (R : ℤ) := by exact_mod_cast hbR.trans hR
  have hch : ∀ c ∈ T.step, ∃ n, ∀ T' ∈ loopIter ε n [c], T'.Stopped ε := by
    intro c hc
    simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    obtain ⟨o, ho, hc⟩ := hc
    obtain ⟨e1, e2⟩ := apply_size T c o hc
    rcases ho with rfl | rfl | rfl | rfl | rfl <;>
      simp only [LoopOp.delta] at e1 e2 <;> norm_num at e1 e2
    · -- `𝔯`
      refine IHy _ ?_ _ c (by omega) ?_ rfl rfl
      · rw [← hy, Int.toNat_lt_toNat (by omega)]; omega
      · rw [← hx, e1]
    · -- `𝔠₁`
      exact IHx _ (by rw [← hx, Int.toNat_lt_toNat (by omega)]; omega) _ _ c (by omega)
        rfl rfl rfl
    · -- `𝔠₂`
      refine IHz _ ?_ c (by omega) ?_ ?_ rfl
      · rw [← hz]; exact phiL_cut2 T c hc
      · rw [← hx, e1]
      · rw [← hy]; congr 1; omega
    · -- `𝔭₁`
      exact IHx _ (by rw [← hx, Int.toNat_lt_toNat (by omega)]; omega) _ _ c (by omega)
        rfl rfl rfl
    · -- `𝔭₂`
      exact IHx _ (by rw [← hx, Int.toNat_lt_toNat (by omega)]; omega) _ _ c (by omega)
        rfl rfl rfl
  obtain ⟨n, hn⟩ := loopIter_list ε T.step hch
  exact ⟨n + 1, by rw [loopIter_succ_single ε n T hs]; exact hn⟩

/-- The expansion of the starting loop (5.30) [starting_point_of_expansion] stops after a number
of rounds that depends on `ε` only (the argument below (5.49) [operation_sequence], with the
quantity `k_#` of the expanded loop). -/
theorem loop_terminates (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ T₀ : ℕ, ∀ T ∈ loopIter ε T₀ [loopStart], T.Stopped ε := by
  obtain ⟨A, hA⟩ := exists_nat_gt (5 / ε)
  obtain ⟨R, hR⟩ := exists_nat_gt (5 / (1 - ε))
  have h0 : loopStart.size = (0, 1) := by decide
  exact terminates_aux ε hε hε' A R hA hR _ _ _ loopStart (by rw [h0]; norm_num) rfl rfl rfl

end RBMTransitionEdge

end
