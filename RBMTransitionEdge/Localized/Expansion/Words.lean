module

public import RBMTransitionEdge.Tools.Resolvent

@[expose] public section

/-!
# Words of the expansion of §5.3

The expressions (5.33) [definition_class_of_expression_loop] of the proof of Lemma 5.2
[lemma_localized_eigenvector_local_law] as words, their characters and size (5.47) [eq:sizeT],
and the five operations (5.42)–(5.46) with Table 1 [table_effect_of_operations].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A letter of the words of the expansion of §5.3: the resolvent `𝒢_a` of slot `a` (`G_a` or
`G_a^*` according to the flag of the slot), its deterministic limit `𝔐_a`, a block projection
`E_x` with a bound block index `x`, and `Λ̃_o` (`o = 0, 1` for `Λ̃₁, Λ̃₂`), as in (5.33)
[definition_class_of_expression_loop]. -/
inductive LoopLetter
  | res (a : Fin 2)
  | det (a : Fin 2)
  | proj (x : ℕ)
  | lamt (o : Fin 2)
  deriving DecidableEq

/-- An expression `c_𝒯 · 𝒲^{(u)} · Γ_n^{(m)}` of (5.33) [definition_class_of_expression_loop]
with `c_𝒯 = D^{dexp} N^{-S}`: `nb` bound block indices, each summed over `⟦1, D⟧`, the light
weights `⟨(𝒢_a - 𝔐_a) E_x⟩` listed by `(a, x)`, and the loops listed by their words. -/
structure LoopExpr where
  /-- The power of `D` in the coefficient. -/
  dexp : ℤ
  /-- The number `S` of factors `N⁻¹` in the coefficient. -/
  S : ℕ
  /-- The number of bound block indices. -/
  nb : ℕ
  /-- The light weights `⟨(𝒢_a - 𝔐_a) E_x⟩`, listed by `(a, x)`. -/
  weights : List (Fin 2 × ℕ)
  /-- The loops, each listed by its word. -/
  loops : List (List LoopLetter)
  deriving DecidableEq

/-- The characters `(m, n, u, S)` of (5.37) [number_of_G_type_1] and Table 1
[table_effect_of_operations]: resolvents in the loops, loops, light weights, factors `N⁻¹`. -/
def LoopExpr.charsZ (T : LoopExpr) : ℤ × ℤ × ℤ × ℤ :=
  (((T.loops.map fun w => w.countP fun x => match x with | .res _ => true | _ => false).sum : ℕ),
    T.loops.length, T.weights.length, T.S)

/-- The size `(S + u, m - n + u)` of (5.47) [eq:sizeT], first component `S + u`. -/
def LoopExpr.size (T : LoopExpr) : ℤ × ℤ :=
  match T.charsZ with
  | (m, n, u, S) => (S + u, m - n + u)

/-- `k₁` (`o = 0`) and `k₂` (`o = 1`) of (5.34) [Gamma_Type_1] and (5.35) [Gamma_Type_2]: the
number of resolvents cyclically to the left of `Λ̃_o` in its loop, up to the other `Λ̃`. -/
def LoopExpr.kk (T : LoopExpr) (o : Fin 2) : ℕ :=
  (T.loops.map fun w => if w.contains (.lamt o) then
    ((((w.rotate (w.idxOf (.lamt o))).drop 1).reverse.takeWhile fun x =>
        match x with | .lamt _ => false | _ => true).countP fun x =>
          match x with | .res _ => true | _ => false) else 0).sum

/-- An expression of the class `𝒯` of (5.33): exactly one `Λ̃₁` and one `Λ̃₂`, every other loop
contains a resolvent, every block index is bound. -/
def LoopExpr.wf (T : LoopExpr) : Bool :=
  (T.loops.map fun w => w.count (.lamt 0)).sum == 1 &&
  (T.loops.map fun w => w.count (.lamt 1)).sum == 1 &&
  T.loops.all (fun w => w.contains (.lamt 0) || w.contains (.lamt 1) ||
    w.any fun x => match x with | .res _ => true | _ => false) &&
  T.loops.all (fun w => w.all fun x => match x with | .proj y => decide (y < T.nb) | _ => true) &&
  T.weights.all fun p => decide (p.2 < T.nb)

/-- The starting loop `⟨𝒢₀ Λ̃₁ 𝒢₁ Λ̃₂⟩` of (5.30) [starting_point_of_expansion] and (5.32)
[eq;expT0]. -/
def loopStart : LoopExpr := ⟨0, 0, 0, [], [[.res 0, .lamt 0, .res 1, .lamt 1]]⟩

/-- The operations `𝔯, 𝔠₁, 𝔠₂, 𝔭₁, 𝔭₂` of (5.42) [sreplace_def]–(5.46) [splug2_def]. -/
inductive LoopOp
  | rep
  | cut1
  | cut2
  | plug1
  | plug2
  deriving DecidableEq

/-- The rows of Table 1 [table_effect_of_operations]: the change of `(m, n, u, S)`. -/
def LoopOp.delta : LoopOp → ℤ × ℤ × ℤ × ℤ
  | .rep => (-1, 0, 0, 0)
  | .cut1 => (0, 0, 1, 0)
  | .cut2 => (1, 1, 0, 0)
  | .plug1 => (2, 0, -1, 2)
  | .plug2 => (1, -1, 0, 2)

/-- The decomposition (5.38) [explicit_cT]: `Λ̃_o` is `Λ̃₁` if `k₁ ≥ 1`, else `Λ̃₂`; its loop
(at position `ℓ`) is rotated to `⟨𝒢_a B₁ Λ̃_o Π⟩`, `𝒢_a` the first resolvent to the left of
`Λ̃_o`, and returned as `(ℓ, a, B₁ Λ̃_o Π)`; `none` when `k₁ = k₂ = 0`. -/
def LoopExpr.focus (T : LoopExpr) : Option (ℕ × Fin 2 × List LoopLetter) :=
  let o : Fin 2 := if 1 ≤ T.kk 0 then 0 else 1
  let ℓ := T.loops.findIdx fun w => w.contains (.lamt o)
  match T.loops[ℓ]? with
  | none => none
  | some w =>
    let i := w.idxOf (.lamt o)
    let n := w.length
    match ((List.range n).map fun j => (i + n - 1 - j) % n).find? (fun r =>
        match w[r]? with
        | some (.res _) => true
        | _ => false) with
    | none => none
    | some r =>
      match w.rotate r with
      | .res a :: tl => if 1 ≤ T.kk o then some (ℓ, a, tl) else none
      | _ => none

/-- The terms of (5.40) [expansion_for_integral_by_part_term] produced by one operation, one per
cut position, light weight or resolvent of another loop: `𝔯` (5.42) [sreplace_def], `𝔠₁` (5.43)
[scut1_def], `𝔠₂` (5.44) [scut_2], `𝔭₁` (5.45) [splug1_def], `𝔭₂` (5.46) [splug2_def]; a new
block index is `nb`. -/
def LoopExpr.apply (T : LoopExpr) : LoopOp → List LoopExpr
  | .rep => match T.focus with
    | none => []
    | some (ℓ, a, tl) => [{ T with loops := T.loops.set ℓ (.det a :: tl) }]
  | .cut1 => match T.focus with
    | none => []
    | some (ℓ, a, tl) => [{ T with
        dexp := T.dexp + 1, nb := T.nb + 1, weights := T.weights ++ [(a, T.nb)],
        loops := T.loops.set ℓ (.det a :: tl ++ [.res a, .proj T.nb]) }]
  | .cut2 => match T.focus with
    | none => []
    | some (ℓ, a, tl) => (List.range tl.length).filterMap fun q =>
        match tl[q]? with
        | some (LoopLetter.res _) => some { T with
            dexp := T.dexp + 1, nb := T.nb + 1,
            loops := T.loops.set ℓ (.det a :: tl.take (q + 1) ++ [.proj T.nb]) ++
              [.proj T.nb :: tl.drop q ++ [.res a]] }
        | _ => none
  | .plug1 => match T.focus with
    | none => []
    | some (ℓ, a, tl) => (List.range T.weights.length).filterMap fun j =>
        match T.weights[j]? with
        | some (b, y) => some { T with
            dexp := T.dexp - 1, S := T.S + 2, nb := T.nb + 1, weights := T.weights.eraseIdx j,
            loops := T.loops.set ℓ (.det a :: tl ++
              [.res a, .proj T.nb, .res b, .proj y, .res b, .proj T.nb]) }
        | none => none
  | .plug2 => match T.focus with
    | none => []
    | some (ℓ, a, tl) => (List.range T.loops.length).flatMap fun j =>
        if j = ℓ then [] else
        match T.loops[j]? with
        | none => []
        | some f => (List.range f.length).filterMap fun q =>
          match f[q]? with
          | some (LoopLetter.res b) => some { T with
              dexp := T.dexp - 1, S := T.S + 2, nb := T.nb + 1,
              loops := (T.loops.set ℓ (.det a :: tl ++ [.res a, .proj T.nb] ++ f.rotate q ++
                [.res b, .proj T.nb])).eraseIdx j }
          | _ => none

/-- All terms of (5.40) [expansion_for_integral_by_part_term] other than the remainder. -/
def LoopExpr.step (T : LoopExpr) : List LoopExpr :=
  [LoopOp.rep, .cut1, .cut2, .plug1, .plug2].flatMap T.apply

/-! ### Auxiliary facts on lists and on `focus` -/

/-- The letter `x` is a resolvent `𝒢_a`. -/
private def isRes (x : LoopLetter) : Bool :=
  match x with | .res _ => true | _ => false

@[simp] private theorem isRes_res (a : Fin 2) : isRes (.res a) = true := rfl
@[simp] private theorem isRes_det (a : Fin 2) : isRes (.det a) = false := rfl
@[simp] private theorem isRes_proj (x : ℕ) : isRes (.proj x) = false := rfl

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

/-- The prefix `tl[..q]` and the suffix `tl[q..]` of a word overlap exactly in the letter `tl[q]`,
for every count of letters. -/
private theorem countP_take_drop (P : LoopLetter → Bool) (tl : List LoopLetter) (q : ℕ)
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

/-- The letter `tl[q]` lies in the prefix `tl[..q+1]`. -/
private theorem mem_take_succ {tl : List LoopLetter} {q : ℕ} {x : LoopLetter}
    (h : tl[q]? = some x) : x ∈ tl.take (q + 1) := by
  rw [List.take_add_one, h]; simp

/-- The data returned by `focus`: the focused loop `w` is a permutation of `𝒢_a · tl`, and `tl`
still contains one of the two `Λ̃`. -/
private theorem focus_spec {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ w : List LoopLetter, T.loops[ℓ]? = some w ∧ w.Perm (.res a :: tl) ∧
      ∃ o : Fin 2, LoopLetter.lamt o ∈ tl := by
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
          refine ⟨w, hw, ?_, o, ?_⟩
          · rw [← hrot]; exact (List.rotate_perm w r).symm
          · obtain ⟨hlt, hwe⟩ := List.getElem?_eq_some_iff.1 hw
            have h1 := List.findIdx_getElem (p := fun w => w.contains (LoopLetter.lamt o))
              (xs := T.loops) (w := hlt)
            rw [hwe] at h1
            have h2 : LoopLetter.lamt o ∈ w := by simpa using h1
            have h3 : LoopLetter.lamt o ∈ w.rotate r := List.mem_rotate.2 h2
            rw [hrot] at h3
            simpa using h3
        · cases h
      · cases h
/-- The first character of `charsZ`, the number of resolvents in the loops, as a sum over the
loops. -/
private theorem charsZ_eq (T : LoopExpr) :
    T.charsZ = ((((T.loops.map fun w => w.countP isRes).sum : ℕ) : ℤ),
      ((T.loops.length : ℕ) : ℤ), ((T.weights.length : ℕ) : ℤ), ((T.S : ℕ) : ℤ)) := rfl

/-- Table 1 [table_effect_of_operations]: each operation changes `(m, n, u, S)` by its row. -/
theorem loop_table1 (T : LoopExpr) (o : LoopOp) (T' : LoopExpr) (h : T' ∈ T.apply o) :
    T'.charsZ = T.charsZ + o.delta := by
  cases o
  · -- `𝔯`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, -⟩ := focus_spec hf
      simp only [List.mem_singleton] at h
      subst h
      have h1 := sum_map_set (fun w => w.countP isRes) T.loops ℓ w (.det a :: tl) hw
      have h2 := hperm.countP_eq isRes
      beta_reduce at h1
      have h3 : (LoopLetter.res a :: tl).countP isRes = tl.countP isRes + 1 := by
        simp [List.countP_cons]
      have h4 : (LoopLetter.det a :: tl).countP isRes = tl.countP isRes := by
        simp
      simp only [charsZ_eq, LoopOp.delta, Prod.mk_add_mk, Prod.mk.injEq, List.length_set]
      omega
  · -- `𝔠₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, -⟩ := focus_spec hf
      simp only [List.mem_singleton] at h
      subst h
      have h1 := sum_map_set (fun w => w.countP isRes) T.loops ℓ w
        (.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb]) hw
      have h2 := hperm.countP_eq isRes
      beta_reduce at h1
      have h3 : (LoopLetter.res a :: tl).countP isRes = tl.countP isRes + 1 := by
        simp [List.countP_cons]
      have h4 : (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb]).countP isRes =
          tl.countP isRes + 1 := by
        simp [List.countP_append, List.countP_cons]
      simp only [charsZ_eq, LoopOp.delta, Prod.mk_add_mk, Prod.mk.injEq, List.length_set,
        List.length_append, List.length_singleton]
      omega
  · -- `𝔠₂`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, -⟩ := focus_spec hf
      obtain ⟨q, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b hq
        simp only [Option.some.injEq] at h5
        subst h5
        have h1 := sum_map_set (fun w => w.countP isRes) T.loops ℓ w
          (.det a :: tl.take (q + 1) ++ [LoopLetter.proj T.nb]) hw
        have h2 := hperm.countP_eq isRes
        have h6 := countP_take_drop isRes tl q _ hq
        beta_reduce at h1
        have h3 : (LoopLetter.res a :: tl).countP isRes = tl.countP isRes + 1 := by
          simp [List.countP_cons]
        have h4 : (LoopLetter.det a :: tl.take (q + 1) ++ [LoopLetter.proj T.nb]).countP isRes =
            (tl.take (q + 1)).countP isRes := by
          simp [List.countP_append]
        have h7 : (LoopLetter.proj T.nb :: tl.drop q ++ [LoopLetter.res a]).countP isRes =
            (tl.drop q).countP isRes + 1 := by
          simp [List.countP_append, List.countP_cons]
        simp only [isRes_res, ite_true] at h6
        simp only [charsZ_eq, LoopOp.delta, Prod.mk_add_mk, Prod.mk.injEq, List.length_set,
          List.length_append, List.length_singleton, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
        omega
      · simp at h5
  · -- `𝔭₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, -⟩ := focus_spec hf
      obtain ⟨j, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b y hj
        simp only [Option.some.injEq] at h5
        subst h5
        have hjlt : j < T.weights.length := (List.getElem?_eq_some_iff.1 hj).1
        have h1 := sum_map_set (fun w => w.countP isRes) T.loops ℓ w
          (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb, LoopLetter.res b,
            LoopLetter.proj y, LoopLetter.res b, LoopLetter.proj T.nb]) hw
        have h2 := hperm.countP_eq isRes
        beta_reduce at h1
        have h3 : (LoopLetter.res a :: tl).countP isRes = tl.countP isRes + 1 := by
          simp [List.countP_cons]
        have h4 : (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb,
            LoopLetter.res b, LoopLetter.proj y, LoopLetter.res b,
            LoopLetter.proj T.nb]).countP isRes = tl.countP isRes + 3 := by
          simp [List.countP_append, List.countP_cons]
        simp only [charsZ_eq, LoopOp.delta, Prod.mk_add_mk, Prod.mk.injEq, List.length_set,
          List.length_eraseIdx, hjlt, ite_true]
        omega
      · simp at h5
  · -- `𝔭₂`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, -⟩ := focus_spec hf
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
            have hL : (T.loops.set ℓ (LoopLetter.det a :: tl ++ [LoopLetter.res a,
                LoopLetter.proj T.nb] ++ f.rotate q ++ [LoopLetter.res b,
                LoopLetter.proj T.nb]))[j]? = some f :=
              (List.getElem?_set_ne (fun h => hjl h.symm)).trans hf2
            have h1 := sum_map_set (fun w => w.countP isRes) T.loops ℓ w
              (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb] ++ f.rotate q ++
                [LoopLetter.res b, LoopLetter.proj T.nb]) hw
            have h8 := sum_map_eraseIdx (fun w => w.countP isRes) _ j f hL
            have hjlt := (List.getElem?_eq_some_iff.1 hL).1
            have h2 := hperm.countP_eq isRes
            have h9 := (List.rotate_perm f q).countP_eq isRes
            beta_reduce at h1 h8
            have h3 : (LoopLetter.res a :: tl).countP isRes = tl.countP isRes + 1 := by
              simp [List.countP_cons]
            have h4 : (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb] ++
                f.rotate q ++ [LoopLetter.res b, LoopLetter.proj T.nb]).countP isRes =
                tl.countP isRes + f.countP isRes + 2 := by
              simp [List.countP_append, List.countP_cons, h9]
              omega
            simp only [charsZ_eq, LoopOp.delta, Prod.mk_add_mk, Prod.mk.injEq, List.length_set,
              List.length_eraseIdx] at hjlt ⊢
            simp only [hjlt, ite_true]
            omega
          · simp at h6


/-- A word contains a resolvent exactly when the Boolean test `any` says so. -/
private theorem any_res_iff (w : List LoopLetter) :
    (w.any fun x => match x with | .res _ => true | _ => false) = true ↔
      ∃ a : Fin 2, LoopLetter.res a ∈ w := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x <;> simp at h
    exact ⟨_, hx⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha, rfl⟩

/-- The conditions of `wf` on one loop: it contains a `Λ̃` or a resolvent, and its block indices
are bound. -/
private abbrev Good (nb : ℕ) (w : List LoopLetter) : Prop :=
  ((∃ k : Fin 2, LoopLetter.lamt k ∈ w) ∨ ∃ a : Fin 2, LoopLetter.res a ∈ w) ∧
    ∀ y, LoopLetter.proj y ∈ w → y < nb

/-- `wf` as a conjunction of propositions: one `Λ̃₁`, one `Λ̃₂`, each loop is `Good`, every block
index of a light weight is bound. -/
private theorem wf_iff (T : LoopExpr) : T.wf = true ↔
    (∀ k : Fin 2, (T.loops.map fun w => w.count (LoopLetter.lamt k)).sum = 1) ∧
    (∀ w ∈ T.loops, Good T.nb w) ∧ (∀ p ∈ T.weights, p.2 < T.nb) := by
  have key : ∀ w : List LoopLetter, (∀ x ∈ w, (match x with
      | .proj y => decide (y < T.nb) | _ => true) = true) ↔
      ∀ y, LoopLetter.proj y ∈ w → y < T.nb := by
    intro w
    constructor
    · intro h y hy
      simpa using h _ hy
    · intro h x hx
      cases x with
      | proj y => exact decide_eq_true (h y hx)
      | res _ => rfl
      | det _ => rfl
      | lamt _ => rfl
  unfold LoopExpr.wf
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, any_res_iff,
    List.contains_iff_mem, decide_eq_true_eq, Fin.forall_fin_two, key, and_assoc,
    Fin.exists_fin_two, imp_and, forall_and]
  exact and_congr_right' (and_congr_right' (and_congr
    (forall₂_congr fun w _ => or_congr_right ((any_res_iff w).trans Fin.exists_fin_two))
    (and_congr_left' (forall₂_congr fun w _ => key w))))

/-- A family of `Good` loops stays `Good` when one entry is replaced by a `Good` one. -/
private theorem good_set {nb : ℕ} {l : List (List LoopLetter)} (hl : ∀ w ∈ l, Good nb w)
    (i : ℕ) {x : List LoopLetter} (hx : Good nb x) : ∀ w ∈ l.set i x, Good nb w := by
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with h | h
  · exact hl w h
  · exact h ▸ hx

/-- `Good` is monotone in the number of bound block indices. -/
private theorem good_mono {nb nb' : ℕ} (h : nb ≤ nb') {w : List LoopLetter} (hw : Good nb w) :
    Good nb' w :=
  ⟨hw.1, fun y hy => lt_of_lt_of_le (hw.2 y hy) h⟩

/-- The operations (5.42)–(5.46) map the class `𝒯` of (5.33)
[definition_class_of_expression_loop] into itself. -/
theorem loop_step_wf (T : LoopExpr) (hT : T.wf = true) (T' : LoopExpr) (h : T' ∈ T.step) :
    T'.wf = true := by
  rw [wf_iff] at hT ⊢
  obtain ⟨hA, hG, hE⟩ := hT
  simp only [LoopExpr.step, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨o, ho, h⟩ := h
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · -- `𝔯`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, o, hlo⟩ := focus_spec hf
      simp only [List.mem_singleton] at h
      subst h
      have hpw := (hG w (List.mem_of_getElem? hw)).2
      have hptl : ∀ y, LoopLetter.proj y ∈ tl → y < T.nb := fun y hy =>
        hpw y (hperm.mem_iff.2 (List.mem_cons_of_mem _ hy))
      refine ⟨fun k => ?_, good_set hG ℓ ⟨Or.inl ⟨o, by simp [hlo]⟩, by simpa using hptl⟩, hE⟩
      have h1 := sum_map_set (fun w => w.count (LoopLetter.lamt k)) T.loops ℓ w
        (.det a :: tl) hw
      have h2 := hperm.count_eq (LoopLetter.lamt k)
      have h3 : (LoopLetter.res a :: tl).count (LoopLetter.lamt k) = tl.count (LoopLetter.lamt k) :=
        by simp
      have h4 : (LoopLetter.det a :: tl).count (LoopLetter.lamt k) =
          tl.count (LoopLetter.lamt k) := by simp
      beta_reduce at h1
      have := hA k
      dsimp only
      omega
  · -- `𝔠₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, o, hlo⟩ := focus_spec hf
      simp only [List.mem_singleton] at h
      subst h
      have hpw := (hG w (List.mem_of_getElem? hw)).2
      have hptl : ∀ y, LoopLetter.proj y ∈ tl → y ≤ T.nb := fun y hy =>
        Nat.le_of_lt (hpw y (hperm.mem_iff.2 (List.mem_cons_of_mem _ hy)))
      refine ⟨fun k => ?_, good_set (fun w hw => good_mono (Nat.le_succ _) (hG w hw)) ℓ
        ⟨Or.inl ⟨o, by simp [hlo]⟩, by simp +contextual [or_imp, hptl]⟩, ?_⟩
      · have h1 := sum_map_set (fun w => w.count (LoopLetter.lamt k)) T.loops ℓ w
          (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb]) hw
        have h2 := hperm.count_eq (LoopLetter.lamt k)
        have h3 : (LoopLetter.res a :: tl).count (LoopLetter.lamt k) =
            tl.count (LoopLetter.lamt k) := by simp
        have h4 : (LoopLetter.det a :: tl ++ [LoopLetter.res a,
            LoopLetter.proj T.nb]).count (LoopLetter.lamt k) = tl.count (LoopLetter.lamt k) := by
          simp [List.count_append]
        beta_reduce at h1
        have := hA k
        dsimp only
        omega
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact Nat.lt_succ_of_lt (hE p hp)
        · rw [List.mem_singleton.1 hp]
          exact Nat.lt_succ_self _
  · -- `𝔠₂`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, o, hlo⟩ := focus_spec hf
      obtain ⟨q, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b hq
        simp only [Option.some.injEq] at h5
        subst h5
        have hpw := (hG w (List.mem_of_getElem? hw)).2
        have hptl : ∀ y, LoopLetter.proj y ∈ tl → y ≤ T.nb := fun y hy =>
          Nat.le_of_lt (hpw y (hperm.mem_iff.2 (List.mem_cons_of_mem _ hy)))
        have hrb : LoopLetter.res b ∈ tl.take (q + 1) := mem_take_succ hq
        have hpt : ∀ y, LoopLetter.proj y ∈ tl.take (q + 1) → y ≤ T.nb := fun y hy =>
          hptl y (List.mem_of_mem_take hy)
        have hpd : ∀ y, LoopLetter.proj y ∈ tl.drop q → y ≤ T.nb := fun y hy =>
          hptl y (List.mem_of_mem_drop hy)
        have hG' : ∀ w ∈ T.loops, Good (T.nb + 1) w := fun w hw =>
          good_mono (Nat.le_succ _) (hG w hw)
        refine ⟨fun k => ?_, fun w' hw' => ?_, fun p hp => Nat.lt_succ_of_lt (hE p hp)⟩
        · have h1 := sum_map_set (fun w => w.count (LoopLetter.lamt k)) T.loops ℓ w
            (LoopLetter.det a :: tl.take (q + 1) ++ [LoopLetter.proj T.nb]) hw
          have h2 := hperm.count_eq (LoopLetter.lamt k)
          have h3 : (LoopLetter.res a :: tl).count (LoopLetter.lamt k) =
              tl.count (LoopLetter.lamt k) := by simp
          have h4 : (LoopLetter.det a :: tl.take (q + 1) ++
              [LoopLetter.proj T.nb]).count (LoopLetter.lamt k) =
              (tl.take (q + 1)).count (LoopLetter.lamt k) := by
            simp [List.count_append]
          have h5 : (LoopLetter.proj T.nb :: tl.drop q ++ [LoopLetter.res a]).count
              (LoopLetter.lamt k) = (tl.drop q).count (LoopLetter.lamt k) := by
            simp [List.count_append]
          have h6 : (tl.take (q + 1)).count (LoopLetter.lamt k) +
              (tl.drop q).count (LoopLetter.lamt k) = tl.count (LoopLetter.lamt k) := by
            have := countP_take_drop (fun x => x == LoopLetter.lamt k) tl q _ hq
            simpa [List.count_eq_countP] using this
          beta_reduce at h1
          have := hA k
          simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]
          omega
        · rcases List.mem_append.1 hw' with hw' | hw'
          · exact good_set hG' ℓ ⟨Or.inr ⟨b, by simp [hrb]⟩, by simp +contextual [or_imp, hpt]⟩
              w' hw'
          · rw [List.mem_singleton.1 hw']
            exact ⟨Or.inr ⟨a, by simp⟩, by simp +contextual [or_imp, hpd]⟩
      · simp at h5
  · -- `𝔭₁`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, o, hlo⟩ := focus_spec hf
      obtain ⟨j, -, h5⟩ := List.mem_filterMap.1 h
      split at h5
      · rename_i b y hj
        simp only [Option.some.injEq] at h5
        subst h5
        have hpw := (hG w (List.mem_of_getElem? hw)).2
        have hptl : ∀ y, LoopLetter.proj y ∈ tl → y ≤ T.nb := fun y hy =>
          Nat.le_of_lt (hpw y (hperm.mem_iff.2 (List.mem_cons_of_mem _ hy)))
        have hy : y ≤ T.nb := Nat.le_of_lt (hE (b, y) (List.mem_of_getElem? hj))
        refine ⟨fun k => ?_, good_set (fun w hw => good_mono (Nat.le_succ _) (hG w hw)) ℓ
          ⟨Or.inl ⟨o, by simp [hlo]⟩, by simp +contextual [or_imp, hptl, hy]⟩,
          fun p hp => Nat.lt_succ_of_lt (hE p (List.mem_of_mem_eraseIdx hp))⟩
        have h1 := sum_map_set (fun w => w.count (LoopLetter.lamt k)) T.loops ℓ w
          (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb, LoopLetter.res b,
            LoopLetter.proj y, LoopLetter.res b, LoopLetter.proj T.nb]) hw
        have h2 := hperm.count_eq (LoopLetter.lamt k)
        have h3 : (LoopLetter.res a :: tl).count (LoopLetter.lamt k) =
            tl.count (LoopLetter.lamt k) := by simp
        have h4 : (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb,
            LoopLetter.res b, LoopLetter.proj y, LoopLetter.res b,
            LoopLetter.proj T.nb]).count (LoopLetter.lamt k) = tl.count (LoopLetter.lamt k) := by
          simp [List.count_append]
        beta_reduce at h1
        have := hA k
        dsimp only
        omega
      · simp at h5
  · -- `𝔭₂`
    simp only [LoopExpr.apply] at h
    split at h
    · simp at h
    · rename_i ℓ a tl hf
      obtain ⟨w, hw, hperm, o, hlo⟩ := focus_spec hf
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
            have hpw := (hG w (List.mem_of_getElem? hw)).2
            have hptl : ∀ y, LoopLetter.proj y ∈ tl → y ≤ T.nb := fun y hy =>
              Nat.le_of_lt (hpw y (hperm.mem_iff.2 (List.mem_cons_of_mem _ hy)))
            have hpf : ∀ y, LoopLetter.proj y ∈ f → y ≤ T.nb := fun y hy =>
              Nat.le_of_lt ((hG f (List.mem_of_getElem? hf2)).2 y hy)
            have hG' : ∀ w ∈ T.loops, Good (T.nb + 1) w := fun w hw =>
              good_mono (Nat.le_succ _) (hG w hw)
            have hL : (T.loops.set ℓ (LoopLetter.det a :: tl ++ [LoopLetter.res a,
                LoopLetter.proj T.nb] ++ f.rotate q ++ [LoopLetter.res b,
                LoopLetter.proj T.nb]))[j]? = some f :=
              (List.getElem?_set_ne (fun h => hjl h.symm)).trans hf2
            refine ⟨fun k => ?_, fun w' hw' => good_set hG' ℓ
              ⟨Or.inl ⟨o, by simp [hlo]⟩, by simp +contextual [or_imp, hptl, hpf]⟩ w'
              (List.mem_of_mem_eraseIdx hw'), fun p hp => Nat.lt_succ_of_lt (hE p hp)⟩
            have h1 := sum_map_set (fun w => w.count (LoopLetter.lamt k)) T.loops ℓ w
              (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb] ++ f.rotate q ++
                [LoopLetter.res b, LoopLetter.proj T.nb]) hw
            have h8 := sum_map_eraseIdx (fun w => w.count (LoopLetter.lamt k)) _ j f hL
            have h2 := hperm.count_eq (LoopLetter.lamt k)
            have h9 := (List.rotate_perm f q).count_eq (LoopLetter.lamt k)
            have h3 : (LoopLetter.res a :: tl).count (LoopLetter.lamt k) =
                tl.count (LoopLetter.lamt k) := by simp
            have h4 : (LoopLetter.det a :: tl ++ [LoopLetter.res a, LoopLetter.proj T.nb] ++
                f.rotate q ++ [LoopLetter.res b, LoopLetter.proj T.nb]).count
                (LoopLetter.lamt k) = tl.count (LoopLetter.lamt k) +
                f.count (LoopLetter.lamt k) := by
              simp [List.count_append, h9]
            beta_reduce at h1 h8
            have := hA k
            dsimp only
            omega
          · simp at h6

end RBMTransitionEdge

end
