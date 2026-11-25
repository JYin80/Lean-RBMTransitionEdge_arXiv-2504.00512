module

public import RBMTransitionEdge.Localized.Expansion.Gauss
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.PkgTerminate
public import RBMTransitionEdge.Localized.Expansion.Poly
public import RBMTransitionEdge.Localized.Expansion.PkgOps
import all RBMTransitionEdge.Localized.Expansion.PkgEval
import all RBMTransitionEdge.Localized.Expansion.Gauss
import all RBMTransitionEdge.Localized.Expansion.Poly
import all RBMTransitionEdge.Localized.Expansion.PkgOps

@[expose] public section

/-!
# The Gaussian step and the tree sum of the further expansion of Lemma 5.5

One step (5.83) [concrete_expansion_tl_2_heavy_package_right], (5.84)
[concrete_expansion_tl_2_loop] of the further expansion in expectation, at fixed entry labels,
and its iteration over the rounds of the further expansion, each up to `N^{-D'} ‖A‖²`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private PE_Op PE_op_dW PE_op_dWbar PE_Op.sum PE_Op.cmul PE_dval PE_dM PE_lm PE_wv PE_wt PE_val
  PE_coef PE_isEnt PE_evalH PE_wm_nil PE_wm_cons PE_wm_append PE_lm_res PE_lm_det PE_lm_proj
  PE_lm_lamt PE_hit PE_ins PE_wins PE_dent_eq PE_good PE_good_val PE_good_sum PE_good_slice
  PE_good_integrable PE_card PE_sum_flatMap PE_sum_filterMap PE_sum_getD PE_prod_set PE_lsum_comm
  PE_wv_any PE_integral_list PE_slot_herm PE_slot_im PE_mul_ent PE_setEntry_self PE_good_mul
  PE_good_const PE_trace_ent PE_dent_mem PE_good_prod PE_good_add
  from RBMTransitionEdge.Localized.Expansion.PkgEval
open private GS_sum_snoc GS_E_snoc GS_sum_block GS_sum_Ea GS_ccum_low GS_tri GS_offblock
  GS_sum_comm_tri GS_norms GS_event GS_Xi GS_V GS_num GS_sum_range GS_sum_filterMap GS_prod_list
  GS_prod_eraseIdx GS_getD_set GS_getD_mem GS_slot_herm GS_slot_im GS_m GS_m_id GS_trace_ntr
  GS_block_trace GS_block_entry GS_single_entry GS_prod_set GS_prod_set_eraseIdx
  from RBMTransitionEdge.Localized.Expansion.Gauss
open private PolySlot PolyRP PolyRP_mono PolyRP_congr PolyRP_const PolyRP_add PolyRP_mul
  PolyRP_sum PolyRP_prod PolyRP_res PolyX_entry_le PolyX_E_entry PolyX_step PolyX_ntr
  PolyX_weights PolyX_prod_pow PolyX_beta0 PolyX_prod_eraseIdx from RBMTransitionEdge.Localized.Expansion.Poly
open private sum_map_set from RBMTransitionEdge.Localized.Expansion.PkgOps

/-! ### The focus, the labels and the bound block indices -/

/-- The search of the rules (i)–(iv) ends at a resolvent. -/
private lemma PG_seek {w : List PkgLetter} {i r : ℕ} {right : Bool}
    (h : pkgSeek w i right = some r) : ∃ a, w[r]? = some (.lw (.res a)) := by
  unfold pkgSeek at h
  have hp := List.find?_some h
  split at hp
  · rename_i a ha
    exact ⟨a, ha⟩
  · simp at hp

/-- The resolvent chosen by `ffocus` heads a rotation of its word. -/
private lemma PG_focus {R : PkgExpr} {ℓ r : ℕ} {right : Bool}
    (hf : R.ffocus = some (ℓ, r, right)) :
    ∃ w, R.loops[ℓ]? = some w ∧ ∃ a tl, w.rotate r = .lw (.res a) :: tl := by
  have key : ∃ w, R.loops[ℓ]? = some w ∧ ∃ i, pkgSeek w i right = some r := by
    unfold PkgExpr.ffocus at hf
    dsimp only at hf
    split at hf
    · rename_i w₂ w₁ h₂ h₁
      split at hf
      · split at hf
        · rename_i r' hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl, rfl⟩ := hf
          exact ⟨w₂, h₂, _, hr'⟩
        · split at hf
          · rename_i r' hr'
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl, rfl⟩ := hf
            exact ⟨w₁, h₁, _, hr'⟩
          · split at hf
            · rename_i r' hr'
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl, rfl⟩ := hf
              exact ⟨w₂, h₂, _, hr'⟩
            · simp at hf
      · split at hf
        · rename_i r' hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl, rfl⟩ := hf
          exact ⟨w₂, h₂, _, hr'⟩
        · split at hf
          · rename_i r' hr'
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl, rfl⟩ := hf
            exact ⟨w₁, h₁, _, hr'⟩
          · simp at hf
    · simp at hf
  obtain ⟨w, hw, i, hs⟩ := key
  obtain ⟨a, ha⟩ := PG_seek hs
  have hr : r < w.length := (List.getElem?_eq_some_iff.1 ha).1
  refine ⟨w, hw, a, w.drop (r + 1) ++ w.take r, ?_⟩
  rw [List.rotate_eq_drop_append_take hr.le, List.drop_eq_getElem_cons hr]
  have : w[r] = .lw (.res a) := (List.getElem?_eq_some_iff.1 ha).2
  rw [this]
  rfl

/-- The entry labels of the letters `Δ_{uv}` of `R` are `0` or `1`. -/
def PG_lab (R : PkgExpr) : Prop :=
  ∀ w ∈ R.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2

/-- In the class every block index of a word or of a light weight is bound. -/
private lemma PG_wf_bound {R : PkgExpr} (hR : R.wf = true) :
    (∀ w ∈ R.loops, ∀ y, PkgLetter.lw (.proj y) ∈ w → y < R.nb) ∧ ∀ p ∈ R.weights, p.2 < R.nb := by
  simp only [PkgExpr.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨-, h4⟩, h5⟩ := hR
  refine ⟨fun w hw y hy => ?_, h5⟩
  simpa using h4 w hw _ hy

/-- The matrix of a word depends on the projections and on the labels only through its letters. -/
private lemma PG_wm_congr {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E E' : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (κ κ' : ℕ → Idx D N) : ∀ w : List PkgLetter,
    (∀ y, PkgLetter.lw (.proj y) ∈ w → E y = E' y) →
    (∀ u v, PkgLetter.ent u v ∈ w → κ u = κ' u ∧ κ v = κ' v) →
    pkgWordMat G M E L κ w = pkgWordMat G M E' L κ' w
  | [], _, _ => rfl
  | x :: w, hE, hκ => by
    rw [PE_wm_cons, PE_wm_cons, PG_wm_congr G M E E' L κ κ' w
      (fun y hy => hE y (List.mem_cons_of_mem _ hy))
      (fun u v h => hκ u v (List.mem_cons_of_mem _ h))]
    congr 1
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · rfl
    · rfl
    · simp only [PE_lm_proj, hE y List.mem_cons_self]
    · rfl
    · obtain ⟨h1, h2⟩ := hκ u v List.mem_cons_self
      simp only [PE_lm, h1, h2]

/-- Words whose letters `Δ` all occur in the words of `L` carry the labels of `L`. -/
private lemma PG_lab_of_sub {L L' : List (List PkgLetter)}
    (h : ∀ w' ∈ L', ∀ u v, PkgLetter.ent u v ∈ w' → ∃ w ∈ L, PkgLetter.ent u v ∈ w)
    (hL : ∀ w ∈ L, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2) :
    ∀ w ∈ L', ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2 := by
  intro w hw u v huv
  obtain ⟨w₀, hw₀, h₀⟩ := h w hw u v huv
  exact hL w₀ hw₀ u v h₀

/-- Replacing one word by a word whose letters `Δ` occur in `L`. -/
private lemma PG_sub_set (L : List (List PkgLetter)) (ℓ : ℕ) (X : List PkgLetter)
    (hX : ∀ u v, PkgLetter.ent u v ∈ X → ∃ w ∈ L, PkgLetter.ent u v ∈ w) :
    ∀ w' ∈ L.set ℓ X, ∀ u v, PkgLetter.ent u v ∈ w' → ∃ w ∈ L, PkgLetter.ent u v ∈ w := by
  intro w' hw' u v h
  rcases List.mem_or_eq_of_mem_set hw' with h1 | rfl
  · exact ⟨w', h1, h⟩
  · exact hX u v h

/-- The terms of `fstep` add no letter `Δ`, so they keep the labels in `{0, 1}`. -/
private lemma PG_step_lab (R : PkgExpr) (hR : PG_lab R) (R' : PkgExpr) (h : R' ∈ R.fstep) :
    PG_lab R' := by
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  unfold PkgExpr.fterms at hmem
  split at hmem
  · simp at hmem
  · rename_i ℓ r right hf
    split at hmem
    · simp at hmem
    · rename_i w hw
      split at hmem
      · rename_i a tl hrot
        have hwL : w ∈ R.loops := List.mem_of_getElem? hw
        have htl : ∀ u v, PkgLetter.ent u v ∈ tl → ∃ w ∈ R.loops, PkgLetter.ent u v ∈ w := by
          intro u v huv
          refine ⟨w, hwL, ?_⟩
          have : PkgLetter.ent u v ∈ w.rotate r := by
            rw [hrot]; exact List.mem_cons_of_mem _ huv
          exact List.mem_rotate.1 this
        set W : List PkgLetter := if right = true then
          PkgLetter.lw (.res a) :: tl ++ [PkgLetter.lw (.det a)]
          else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)] with hWdef
        have hW : ∀ u v, PkgLetter.ent u v ∈ W → ∃ w ∈ R.loops, PkgLetter.ent u v ∈ w := by
          intro u v huv
          rw [hWdef] at huv
          split_ifs at huv <;> simp only [List.cons_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, reduceCtorEq, false_or, or_false] at huv <;> exact htl u v huv
        apply PG_lab_of_sub _ hR
        dsimp only at hmem
        rcases List.mem_append.1 hmem with hmem | hmem
        · rcases List.mem_append.1 hmem with hmem | hmem
          · rcases List.mem_append.1 hmem with hmem | hmem
            · rcases List.mem_cons.1 hmem with hmem | hmem
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                exact PG_sub_set _ _ _ fun u v huv => htl u v (by simpa using huv)
              · rcases List.mem_cons.1 hmem with hmem | hmem
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                  refine PG_sub_set _ _ _ fun u v huv => hW u v ?_
                  split_ifs at huv <;> simpa using huv
                · simp at hmem
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hmem
              split at hq
              · simp at hq
              · split at hq
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  intro w' hw' u v huv
                  rcases List.mem_append.1 hw' with hw' | hw'
                  · exact PG_sub_set _ _ _ (fun u v huv => hW u v (by
                      simpa using List.mem_of_mem_take (by simpa using huv))) w' hw' u v huv
                  · simp only [List.mem_singleton] at hw'
                    subst hw'
                    exact hW u v (List.mem_of_mem_drop (by simpa using huv))
                · simp at hq
          · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hmem
            split at hj
            · rename_i b y hjb
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
              exact PG_sub_set _ _ _ fun u v huv => hW u v (by simpa using huv)
            · simp at hj
        · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hmem
          split at hj
          · simp at hj
          · split at hj
            · simp at hj
            · rename_i f hf'
              obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · rename_i b hqb
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                intro w' hw' u v huv
                refine PG_sub_set _ _ _ (fun u v huv => ?_) w' (List.mem_of_mem_eraseIdx hw') u v
                  huv
                simp only [List.append_assoc, List.mem_append, List.mem_cons, reduceCtorEq,
                  false_or, or_false, List.not_mem_nil] at huv
                rcases huv with huv | huv
                · exact hW u v huv
                · exact ⟨f, List.mem_of_getElem? hf', List.mem_rotate.1 huv⟩
              · simp at hq
      · simp at hmem

/-! ### Words, traces and the entries of a block -/

/-- The weight of the value of a word: `1` (trace) with a letter `Δ`, `(DN)⁻¹` (normalized trace)
without one. -/
private def PG_c (D N : ℕ) (w : List PkgLetter) : ℂ :=
  if w.any PE_isEnt then 1 else ((D : ℂ) * N)⁻¹

private lemma PG_wv_eq {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (w : List PkgLetter) :
    PE_wv e ι κ h w = PG_c D N w * (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w).trace := by
  unfold PE_wv PG_c ntr
  split_ifs
  · rw [one_mul]
  · rw [PE_card]

private lemma PG_any_rotate (p : PkgLetter → Bool) (w : List PkgLetter) (r : ℕ) :
    (w.rotate r).any p = w.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, List.mem_rotate.1 hx, hp⟩,
    fun ⟨x, hx, hp⟩ => ⟨x, List.mem_rotate.2 hx, hp⟩⟩

private lemma PG_c_rotate (D N : ℕ) (w : List PkgLetter) (r : ℕ) :
    PG_c D N (w.rotate r) = PG_c D N w := by
  unfold PG_c
  rw [PG_any_rotate]

private lemma PG_trace_rotate {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (w : List PkgLetter) (r : ℕ) :
    (pkgWordMat G M E L κ (w.rotate r)).trace = (pkgWordMat G M E L κ w).trace := by
  rw [List.rotate_eq_drop_append_take_mod, PE_wm_append, Matrix.trace_mul_comm, ← PE_wm_append,
    List.take_append_drop]

/-- `(P Δ_{uv} Q)_{kl} = P_{k, κ u} Q_{κ v, l}`. -/
private lemma PG_mul_ent {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (P Q : Matrix (Idx D N) (Idx D N) ℂ) (u v : ℕ) (k l : Idx D N) :
    (P * PE_lm G M E L κ (.ent u v) * Q) k l = P k (κ u) * Q (κ v) l := by
  simp only [Matrix.mul_apply, PE_lm, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq', ite_mul]

/-- `Tr(P Δ_{uv} Q Δ_{vu}) = P_{κu κu} Q_{κv κv}`. -/
private lemma PG_tr_ent2 {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (P Q : Matrix (Idx D N) (Idx D N) ℂ) (u v : ℕ) :
    (P * PE_lm G M E L κ (.ent u v) * Q * PE_lm G M E L κ (.ent v u)).trace =
      P (κ u) (κ u) * Q (κ v) (κ v) := by
  rw [PE_trace_ent, PG_mul_ent]

/-- `Tr(A Δ_{uv} B) = (B A)_{κv κu}`. -/
private lemma PG_tr_ent1 {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (A B : Matrix (Idx D N) (Idx D N) ℂ) (u v : ℕ) :
    (A * PE_lm G M E L κ (.ent u v) * B).trace = (B * A) (κ v) (κ u) := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, PE_trace_ent]

/-- `Σ_{i,j ∈ 𝓘_x} P_{ii} Q_{jj} = Tr(P E_x) Tr(Q E_x)`. -/
private lemma PG_block1 {D N : ℕ} (x : Fin D) (P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) * (P i i * Q j j) =
      (P * Ea D N x).trace * (Q * Ea D N x).trace := by
  simp only [Matrix.trace, Matrix.diag, Ea, Matrix.mul_diagonal, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diagonal_apply_eq]
  ring

/-- `Σ_{i,j ∈ 𝓘_x} Y_{ij} Z_{ji} = Tr(Y E_x Z E_x)`. -/
private lemma PG_block2 {D N : ℕ} (x : Fin D) (Y Z : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) * (Y i j * Z j i) =
      (Y * Ea D N x * Z * Ea D N x).trace := by
  simp only [Matrix.trace, Matrix.diag, Ea]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul]
  by_cases hi : i.1 = x <;> by_cases hj : j.1 = x <;> simp [hi, hj, mul_comm]

/-- The resolvent identity (2.43) [eq:id_G0G1] in a trace: `Tr(𝒢_a X) = Tr(𝔐_a X) - Σ_{ij}
h̄_{ij} Y_{ij} - 𝗆_a Tr Y` with `Y = 𝒢_a X 𝔐_a` (`𝒢 = 𝔐 - 𝔐(h + 𝗆)𝒢`) or `Y = 𝔐_a X 𝒢_a`
(`𝒢 = 𝔐 - 𝒢(h + 𝗆)𝔐`), for a Hermitian array. -/
private lemma PG_res_id {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (a : Fin 2) (X : Matrix (Idx D N) (Idx D N) ℂ) (right : Bool) :
    (e.G h a * X).trace = (e.M a * X).trace -
      (∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) *
        (if right then e.G h a * X * e.M a else e.M a * X * e.G h a) i j) -
      GS_m e a * (if right then e.G h a * X * e.M a else e.M a * X * e.G h a).trace := by
  set Λ := (e.c a : ℂ) • lam D N e.A with hΛ
  set ζ := if e.s a then star (e.z a) else e.z a with hζ
  set m := GS_m e a with hm
  set G := e.G h a with hG
  set M := e.M a with hM
  obtain ⟨-, hdy⟩ := def_M_scalar D hD N hN ((e.c a : ℂ) • e.A) _ (GS_slot_im e hz a)
  rw [← lam_smul] at hdy
  have hdy' : (Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M = 1 := by
    have : ((m + ζ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Λ) * M = -1 :=
      eq_neg_of_add_eq_zero_left hdy
    rw [show Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
      -((m + ζ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Λ) by rw [add_comm]; abel, Matrix.neg_mul,
      this, neg_neg]
  have hdy'' : M * (Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 :=
    mul_eq_one_comm.1 hdy'
  obtain ⟨hG1, hG2⟩ := res_mul_sub_of_im_ne (Matrix.of h + Λ) (hh.add (GS_slot_herm e a)) ζ
    (GS_slot_im e hz a)
  have hG1' : (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G = 1 := hG1
  have hG2' : G * (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 := hG2
  have htr : ∀ Y : Matrix (Idx D N) (Idx D N) ℂ, (Matrix.of h * Y).trace =
      ∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) * Y i j := by
    intro Y
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hh.apply i j
    simp only [Matrix.of_apply] at this
    rw [← this, Complex.star_def, Complex.conj_conj]
  cases right
  · have key : G = M - G * Matrix.of h * M - m • (G * M) := by
      calc G = G * ((Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M) := by
            rw [hdy', Matrix.mul_one]
        _ = (G * (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) - G * Matrix.of h -
            m • G) * M := by
            have e1 : G * (Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) =
                G * (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) - G * Matrix.of h -
                  m • G := by
              simp only [Matrix.mul_sub, Matrix.mul_add, add_smul, Matrix.mul_smul, Matrix.mul_one]
              abel
            rw [← Matrix.mul_assoc, e1]
        _ = M - G * Matrix.of h * M - m • (G * M) := by
            rw [hG2', Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    simp only [Bool.false_eq_true, ite_false]
    rw [← htr]
    conv_lhs => rw [key]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    rw [show G * Matrix.of h * M * X = G * (Matrix.of h * (M * X)) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm G,
      show Matrix.of h * (M * X) * G = Matrix.of h * (M * X * G) by simp only [Matrix.mul_assoc],
      show G * M * X = G * (M * X) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm G]
  · have key : G = M - M * Matrix.of h * G - m • (M * G) := by
      calc G = (M * (Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ))) * G := by
            rw [hdy'', Matrix.one_mul]
        _ = M * ((Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G -
            Matrix.of h * G - m • G) := by
            have e1 : (Λ - (ζ + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G =
                (Matrix.of h + Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G -
                  Matrix.of h * G - m • G := by
              simp only [Matrix.sub_mul, Matrix.add_mul, add_smul, Matrix.smul_mul, Matrix.one_mul]
              abel
            rw [Matrix.mul_assoc, e1]
        _ = M - M * Matrix.of h * G - m • (M * G) := by
            rw [hG1', Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
              Matrix.mul_assoc]
    simp only [ite_true]
    rw [← htr]
    conv_lhs => rw [key]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    have t1 : (M * Matrix.of h * G * X).trace = (Matrix.of h * (G * X * M)).trace := by
      rw [show M * Matrix.of h * G * X = M * (Matrix.of h * G * X) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm M]
      simp only [Matrix.mul_assoc]
    have t2 : (M * G * X).trace = (G * X * M).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm M]
    rw [t1, t2]

/-! ### The expanded word, the labels of `𝓔^{(2)}` and the words of the class -/

/-- The expanded word `𝒢_a tl 𝔐_a` (resolvent to the right of its `Λ̃`) or `𝔐_a tl 𝒢_a`. -/
private def PG_W (right : Bool) (a : Fin 2) (tl : List PkgLetter) : List PkgLetter :=
  if right then .lw (.res a) :: tl ++ [.lw (.det a)] else .lw (.det a) :: tl ++ [.lw (.res a)]

/-- The labels `2 ↦ i`, `3 ↦ j` of `𝓔^{(2)}`, the others those of `κ`. -/
private def PG_κ {D N : ℕ} (κ : ℕ → Idx D N) (i j : Idx D N) : ℕ → Idx D N :=
  fun l => if l = 2 then i else if l = 3 then j else κ l

private lemma PG_κ_lt {D N : ℕ} (κ : ℕ → Idx D N) (i j : Idx D N) (l : ℕ) (hl : l < 2) :
    PG_κ κ i j l = κ l := by
  simp [PG_κ, show l ≠ 2 by omega, show l ≠ 3 by omega]

/-- A word with bound block indices below `n` and labels in `{0, 1}`. -/
private def PG_ok (n : ℕ) (v : List PkgLetter) : Prop :=
  (∀ y, PkgLetter.lw (.proj y) ∈ v → y < n) ∧ ∀ u u', PkgLetter.ent u u' ∈ v → u < 2 ∧ u' < 2

private lemma PG_ok_of {n : ℕ} {v v' : List PkgLetter} (hv : PG_ok n v')
    (h : ∀ x ∈ v, x ∈ v' ∨ ∃ b, x = .lw (.res b) ∨ x = .lw (.det b)) : PG_ok n v := by
  refine ⟨fun y hy => ?_, fun u u' hu => ?_⟩
  · rcases h _ hy with h1 | ⟨b, h1 | h1⟩
    · exact hv.1 y h1
    · cases h1
    · cases h1
  · rcases h _ hu with h1 | ⟨b, h1 | h1⟩
    · exact hv.2 u u' h1
    · cases h1
    · cases h1

private lemma PG_ok_loops {R : PkgExpr} (hR : R.wf = true) (hlab : PG_lab R) {v : List PkgLetter}
    (hv : v ∈ R.loops) : PG_ok R.nb v :=
  ⟨(PG_wf_bound hR).1 v hv, hlab v hv⟩

private lemma PG_ok_wm {D N n m : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (ι' : Fin m → Fin D)
    (κ κ' : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) {v : List PkgLetter} (hv : PG_ok n v)
    (hE : ∀ y, y < n → e.E ι' y = e.E ι y) (hκ : ∀ l, l < 2 → κ' l = κ l) :
    pkgWordMat (e.G h) e.M (e.E ι') e.Lt κ' v = pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ v :=
  PG_wm_congr _ _ _ _ _ _ _ v (fun y hy => hE y (hv.1 y hy))
    (fun u u' hu => ⟨hκ u (hv.2 u u' hu).1, hκ u' (hv.2 u u' hu).2⟩)

private lemma PG_ok_wv {D N n m : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (ι' : Fin m → Fin D)
    (κ κ' : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) {v : List PkgLetter} (hv : PG_ok n v)
    (hE : ∀ y, y < n → e.E ι' y = e.E ι y) (hκ : ∀ l, l < 2 → κ' l = κ l) :
    PE_wv e ι' κ' h v = PE_wv e ι κ h v := by
  unfold PE_wv
  rw [PG_ok_wm e ι ι' κ κ' h hv hE hκ]

private lemma PG_E_snoc {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (x : Fin D) :
    ∀ y, y < n → e.E (Fin.snoc (α := fun _ => Fin D) ι x) y = e.E ι y :=
  (GS_E_snoc e ι x).1

/-- The letters of the expanded word are those of the focused word and `𝔐_a`. -/
private lemma PG_W_mem {w tl : List PkgLetter} {r : ℕ} {a : Fin 2}
    (hrot : w.rotate r = .lw (.res a) :: tl) (right : Bool) :
    ∀ x ∈ PG_W right a tl, x ∈ w ∨ ∃ b, x = .lw (.res b) ∨ x = .lw (.det b) := by
  have htl : ∀ x ∈ tl, x ∈ w := fun x hx => by
    have : x ∈ w.rotate r := by rw [hrot]; exact List.mem_cons_of_mem _ hx
    exact List.mem_rotate.1 this
  intro x hx
  unfold PG_W at hx
  split_ifs at hx <;> simp only [List.cons_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hx <;> rcases hx with hx | hx | hx
  all_goals first
    | exact Or.inr ⟨a, Or.inl hx⟩
    | exact Or.inr ⟨a, Or.inr hx⟩
    | exact Or.inl (htl x hx)

private lemma PG_isEnt_lw (x : LoopLetter) : PE_isEnt (.lw x) = false := rfl

private lemma PG_c_cons_lw (D N : ℕ) (x : LoopLetter) (v : List PkgLetter) :
    PG_c D N (.lw x :: v) = PG_c D N v := by
  simp [PG_c, List.any_cons, PG_isEnt_lw]

private lemma PG_any_W {w tl : List PkgLetter} {r : ℕ} {a : Fin 2}
    (hrot : w.rotate r = .lw (.res a) :: tl) (right : Bool) :
    (PG_W right a tl).any PE_isEnt = w.any PE_isEnt := by
  rw [← PG_any_rotate PE_isEnt w r, hrot]
  unfold PG_W
  split_ifs <;> simp [List.any_cons, List.any_append, PG_isEnt_lw]

private lemma PG_c_W (D N : ℕ) {w tl : List PkgLetter} {r : ℕ} {a : Fin 2}
    (hrot : w.rotate r = .lw (.res a) :: tl) (right : Bool) :
    PG_c D N (PG_W right a tl) = PG_c D N w := by
  unfold PG_c
  rw [PG_any_W hrot]

private lemma PG_c_tl (D N : ℕ) {w tl : List PkgLetter} {r : ℕ} {a : Fin 2}
    (hrot : w.rotate r = .lw (.res a) :: tl) : PG_c D N tl = PG_c D N w := by
  rw [← PG_c_rotate D N w r, hrot, PG_c_cons_lw]

/-- The matrix of the expanded word: `𝒢_a X 𝔐_a` or `𝔐_a X 𝒢_a`. -/
private lemma PG_wm_W {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (right : Bool) (a : Fin 2) (tl : List PkgLetter) :
    pkgWordMat G M E L κ (PG_W right a tl) = if right then G a * pkgWordMat G M E L κ tl * M a
      else M a * pkgWordMat G M E L κ tl * G a := by
  unfold PG_W
  cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.cons_append,
    PE_wm_cons, PE_wm_append, PE_lm_res, PE_lm_det, PE_wm_nil, Matrix.mul_one, Matrix.mul_assoc]

/-- `R.fpkg` at the focus: `-W_{ij} = -Tr(W Δ_{32})` in place of the focused word. -/
private lemma PG_fpkg_eq {R : PkgExpr} {ℓ r : ℕ} {right : Bool} {w tl : List PkgLetter} {a : Fin 2}
    (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) :
    R.fpkg = { R with
      cf := -R.cf, dexp := if w.any PE_isEnt then R.dexp else R.dexp - 1,
      S := if w.any PE_isEnt then R.S else R.S + 1,
      loops := R.loops.set ℓ (PG_W right a tl ++ [.ent 3 2]) } := by
  unfold PkgExpr.fpkg
  rw [hf]
  simp only [hw, hrot]
  rfl

/-! ### The values of the terms at fixed bound block indices -/

private lemma PG_ok_getD {R : PkgExpr} (hR : R.wf = true) (hlab : PG_lab R) (k : ℕ) :
    PG_ok R.nb (R.loops.getD k []) := by
  by_cases hk : k < R.loops.length
  · exact PG_ok_loops hR hlab (GS_getD_mem _ _ k hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨fun y hy => by simp at hy, fun u u' hu => by simp at hu⟩

/-- The other loops do not see the extra bound index nor the labels `2, 3`. -/
private lemma PG_prod_congr {D N m : ℕ} (e : LoopEnv D N) {R : PkgExpr} (hR : R.wf = true)
    (hlab : PG_lab R) (ι : Fin R.nb → Fin D) (ι' : Fin m → Fin D) (κ κ' : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (hE : ∀ y, y < R.nb → e.E ι' y = e.E ι y)
    (hκ : ∀ l, l < 2 → κ' l = κ l) (S : Finset ℕ) :
    ∏ k ∈ S, PE_wv e ι' κ' h (R.loops.getD k []) = ∏ k ∈ S, PE_wv e ι κ h (R.loops.getD k []) :=
  Finset.prod_congr rfl fun k _ => PG_ok_wv e ι ι' κ κ' h (PG_ok_getD hR hlab k) hE hκ

/-- The light weights do not see the extra bound index. -/
private lemma PG_wt_congr {D N m : ℕ} (e : LoopEnv D N) {R : PkgExpr} (hR : R.wf = true)
    (ι : Fin R.nb → Fin D) (ι' : Fin m → Fin D) (h : Idx D N → Idx D N → ℂ)
    (hE : ∀ y, y < R.nb → e.E ι' y = e.E ι y) (L : List (Fin 2 × ℕ))
    (hL : ∀ p ∈ L, p ∈ R.weights) :
    (L.map (PE_wt e ι' h)).prod = (L.map (PE_wt e ι h)).prod := by
  congr 1
  refine List.map_congr_left fun p hp => ?_
  unfold PE_wt
  rw [hE p.2 ((PG_wf_bound hR).2 p (hL p hp))]

/-- The coefficient `c D^{dexp + t} N^{-(S + 1 - t)}` is `c D^{dexp} N^{-S} N⁻¹ (DN)^t`. -/
private lemma PG_coef_shift {D N : ℕ} (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) (cf dexp S t : ℤ) :
    (cf : ℂ) * (D : ℂ) ^ (dexp + t) * (N : ℂ) ^ (-(S + 1 - t)) =
      (cf : ℂ) * (D : ℂ) ^ dexp * (N : ℂ) ^ (-S) * ((N : ℂ)⁻¹ * ((D : ℂ) * N) ^ t) := by
  rw [zpow_add₀ hD, show -(S + 1 - t) = -S + (t - 1) by ring, zpow_add₀ hN, zpow_sub₀ hN,
    zpow_one, mul_zpow]
  field_simp

private lemma PG_c_cut {D N : ℕ} (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) (b1 b2 bw : Bool) :
    ((D : ℂ) * N) ^ ((if (!b1) = true then 1 else 0) + (if (!b2) = true then 1 else 0) -
        (if (!bw) = true then 1 else 0) : ℤ) *
      ((if b1 then 1 else ((D : ℂ) * N)⁻¹) * (if b2 then 1 else ((D : ℂ) * N)⁻¹)) =
      if bw then 1 else ((D : ℂ) * N)⁻¹ := by
  have hκ : (D : ℂ) * N ≠ 0 := mul_ne_zero hD hN
  cases b1 <;> cases b2 <;> cases bw <;> simp <;> field_simp

private lemma PG_c_join {D N : ℕ} (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) (bw bf : Bool) :
    ((D : ℂ) * N) ^ ((if (!(bw || bf)) = true then 1 else 0) - (if (!bw) = true then 1 else 0) -
        (if (!bf) = true then 1 else 0) : ℤ) * (if bw || bf then 1 else ((D : ℂ) * N)⁻¹) =
      (if bw then 1 else ((D : ℂ) * N)⁻¹) * (if bf then 1 else ((D : ℂ) * N)⁻¹) := by
  have hκ : (D : ℂ) * N ≠ 0 := mul_ne_zero hD hN
  cases bw <;> cases bf <;> simp


private lemma PG_c_append_lw (D N : ℕ) (v : List PkgLetter) (x : LoopLetter) :
    PG_c D N (v ++ [.lw x]) = PG_c D N v := by
  simp [PG_c, List.any_append, PG_isEnt_lw]

private lemma PG_c_ent (D N : ℕ) (v : List PkgLetter) (u u' : ℕ) :
    PG_c D N (v ++ [.ent u u']) = 1 := by
  simp [PG_c, List.any_append, PE_isEnt]

/-- A product over a list after two `set`s at `ℓ ≠ j`. -/
private lemma PG_prod_set_set {α : Type*} (f : α → ℂ) (d : α) (l : List α) (ℓ j : ℕ)
    (hℓ : ℓ < l.length) (hj : j < l.length) (hjℓ : j ≠ ℓ) (X Y : α) :
    (((l.set ℓ X).set j Y).map f).prod =
      f Y * (f X * ∏ k ∈ ((Finset.range l.length).erase ℓ).erase j, f (l.getD k d)) := by
  rw [GS_prod_set f d _ j (by simpa using hj), List.length_set,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hjℓ, Finset.mem_range.2 hℓ⟩),
    Finset.erase_right_comm]
  congr 2
  · rw [GS_getD_set l ℓ hℓ X d]; simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [GS_getD_set l ℓ hℓ X d]; simp [Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)]

section Values

variable {D N : ℕ} (e : LoopEnv D N) {R : PkgExpr} (hR : R.wf = true) (hlab : PG_lab R)
  {ℓ r : ℕ} {w tl : List PkgLetter} {a : Fin 2} (hw : R.loops[ℓ]? = some w)
  (hrot : w.rotate r = .lw (.res a) :: tl) (ι : Fin R.nb → Fin D) (κ : ℕ → Idx D N)
  (h : Idx D N → Idx D N → ℂ)

include hw hrot in
/-- The value of `𝓡` at fixed bound indices, with the focused word as `Tr(𝒢_a X)`. -/
private lemma PG_val_R :
    PE_val e ι κ R h = PE_coef D N R * (R.weights.map (PE_wt e ι h)).prod *
      (PG_c D N w * (e.G h a * pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ tl).trace *
        ∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hwe : R.loops[ℓ] = w := (List.getElem?_eq_some_iff.1 hw).2
  have hset : R.loops.set ℓ w = R.loops := by rw [← hwe]; exact List.set_getElem_self hℓ
  have e1 : (R.loops.map (PE_wv e ι κ h)).prod = PE_wv e ι κ h w *
      ∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k []) := by
    conv_lhs => rw [← hset]
    exact GS_prod_set _ [] _ _ hℓ w
  have e2 : PE_wv e ι κ h w =
      PG_c D N w * (e.G h a * pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ tl).trace := by
    rw [PG_wv_eq, ← PG_trace_rotate _ _ _ _ _ w r, hrot, PE_wm_cons, PE_lm_res]
  unfold PE_val
  rw [e1, e2]
  ring

include hw hrot in
/-- The value of the replacement `𝔣𝔯`. -/
private lemma PG_val_rep (R' : PkgExpr) (hcf : R'.cf = R.cf) (hd : R'.dexp = R.dexp)
    (hS : R'.S = R.S) (hwt : R'.weights = R.weights)
    (hl : R'.loops = R.loops.set ℓ (.lw (.det a) :: tl)) :
    PE_val e ι κ R' h = PE_coef D N R * (R.weights.map (PE_wt e ι h)).prod *
      (PG_c D N w * (e.M a * pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ tl).trace *
        ∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  unfold PE_val PE_coef
  rw [hcf, hd, hS, hwt, hl, GS_prod_set _ [] _ _ hℓ, PG_wv_eq, PG_c_cons_lw, PG_c_tl D N hrot,
    PE_wm_cons, PE_lm_det]
  ring

include hR hlab hw hrot in
/-- The expanded word is a word of the class. -/
private lemma PG_ok_W (right : Bool) : PG_ok R.nb (PG_W right a tl) :=
  PG_ok_of (PG_ok_loops hR hlab (List.mem_of_getElem? hw)) (PG_W_mem hrot right)

include hR hlab hw hrot in
/-- The value of `fpkg`: `-c_𝓡 W_{ij}` times the other factors. -/
private lemma PG_val_fpkg {right : Bool} (hf : R.ffocus = some (ℓ, r, right)) (i j : Idx D N)
    (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) :
    PE_val e ι (PG_κ κ i j) R.fpkg h = -(PE_coef D N R * PG_c D N w) *
      (R.weights.map (PE_wt e ι h)).prod *
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) i j *
        ∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  rw [PG_fpkg_eq hf hw hrot]
  unfold PE_val PE_coef
  simp only
  rw [GS_prod_set _ [] _ _ hℓ, PG_prod_congr e hR hlab ι ι _ _ h (fun _ _ => rfl)
    (PG_κ_lt κ i j), PG_wv_eq, PG_c_ent, one_mul, PE_wm_append, PE_wm_cons, PE_wm_nil,
    Matrix.mul_one, PE_trace_ent,
    PG_ok_wm e ι ι κ (PG_κ κ i j) h (PG_ok_W hR hlab hw hrot right) (fun _ _ => rfl)
      (PG_κ_lt κ i j)]
  have h2 : PG_κ κ i j 2 = i := by simp [PG_κ]
  have h3 : PG_κ κ i j 3 = j := by simp [PG_κ]
  rw [h2, h3]
  unfold PG_c
  rcases hb : w.any PE_isEnt
  · simp only [Bool.false_eq_true, ite_false, Int.cast_neg]
    rw [zpow_sub_one₀ hD, show -(R.S + 1) = -R.S + -1 by ring, zpow_add₀ hN, _root_.zpow_neg_one]
    ring
  · simp only [ite_true, Int.cast_neg]
    ring

include hR hlab hw hrot in
/-- The value of the light weight term `𝔣𝔠₁` or `𝔰𝔩𝔞𝔰𝔥₁` at `(ι, x)`. -/
private lemma PG_val_slash (right : Bool) (x : Fin D) (R' : PkgExpr) (hcf : R'.cf = R.cf)
    (hd : R'.dexp = R.dexp + 1) (hS : R'.S = R.S) (hwt : R'.weights = R.weights ++ [(a, R.nb)])
    (hl : R'.loops = R.loops.set ℓ (if right then .lw (.proj R.nb) :: PG_W right a tl
      else PG_W right a tl ++ [.lw (.proj R.nb)])) (hD : (D : ℂ) ≠ 0) :
    PE_val e (Fin.snoc (α := fun _ => Fin D) ι x) κ R' h = PE_coef D N R * (D : ℂ) *
      (R.weights.map (PE_wt e ι h)).prod * ntr ((e.G h a - e.M a) * Ea D N x) *
      (PG_c D N w * (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) * Ea D N x).trace *
        ∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hE := PG_E_snoc e ι x
  have hEn := (GS_E_snoc e ι x).2
  have hWok := PG_ok_wm e ι (Fin.snoc (α := fun _ => Fin D) ι x) κ κ h
    (PG_ok_W hR hlab hw hrot right) hE (fun _ _ => rfl)
  unfold PE_val PE_coef
  rw [hcf, hd, hS, hwt, hl, GS_prod_set _ [] _ _ hℓ, PG_prod_congr e hR hlab ι _ κ κ h hE
    (fun _ _ => rfl), List.map_append, List.prod_append,
    PG_wt_congr e hR ι _ h hE R.weights (fun p hp => hp), PG_wv_eq, zpow_add_one₀ hD]
  have hwt1 : ([(a, R.nb)].map (PE_wt e (Fin.snoc (α := fun _ => Fin D) ι x) h)).prod =
      ntr ((e.G h a - e.M a) * Ea D N x) := by
    simp only [List.map_singleton, List.prod_singleton, PE_wt, hEn]
  rw [hwt1]
  have hc : PG_c D N (if right then .lw (.proj R.nb) :: PG_W right a tl
      else PG_W right a tl ++ [.lw (.proj R.nb)]) = PG_c D N w := by
    split_ifs
    · rw [PG_c_cons_lw, PG_c_W D N hrot]
    · rw [PG_c_append_lw, PG_c_W D N hrot]
  have htr : (pkgWordMat (e.G h) e.M (e.E (Fin.snoc (α := fun _ => Fin D) ι x)) e.Lt κ
      (if right then .lw (.proj R.nb) :: PG_W right a tl
        else PG_W right a tl ++ [.lw (.proj R.nb)])).trace =
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) * Ea D N x).trace := by
    split_ifs
    · rw [PE_wm_cons, PE_lm_proj, hEn, hWok, Matrix.trace_mul_comm]
    · rw [PE_wm_append, PE_wm_cons, PE_lm_proj, PE_wm_nil, Matrix.mul_one, hEn, hWok]
  rw [hc, htr]
  ring

include hR hlab hw hrot in
/-- The value of a cut `𝔣𝔠₂`, `𝔰𝔩𝔞𝔰𝔥₂` or `𝔢𝔵𝔠𝔥𝔞𝔫𝔤𝔢` of the expanded word at position `q`, at
`(ι, x)`. -/
private lemma PG_val_cut (right : Bool) (q : ℕ) (x : Fin D) (R' : PkgExpr) (t : ℤ)
    (hcf : R'.cf = R.cf) (hd : R'.dexp = R.dexp + t) (hS : R'.S = R.S + 1 - t)
    (hwt : R'.weights = R.weights)
    (hl : R'.loops = R.loops.set ℓ ((PG_W right a tl).take (q + 1) ++ [.lw (.proj R.nb)]) ++
      [.lw (.proj R.nb) :: (PG_W right a tl).drop q])
    (ht : t = (if (!(((PG_W right a tl).take (q + 1) ++
        [PkgLetter.lw (.proj R.nb)]).any PE_isEnt)) = true
        then 1 else 0) +
      (if (!((PkgLetter.lw (.proj R.nb) :: (PG_W right a tl).drop q).any PE_isEnt)) = true then 1
        else 0) -
      (if (!(w.any PE_isEnt)) = true then 1 else 0))
    (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) :
    PE_val e (Fin.snoc (α := fun _ => Fin D) ι x) κ R' h = PE_coef D N R * PG_c D N w *
      (N : ℂ)⁻¹ * (R.weights.map (PE_wt e ι h)).prod *
      (∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) *
      ((pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ ((PG_W right a tl).take (q + 1)) * Ea D N x).trace *
        (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ ((PG_W right a tl).drop q) * Ea D N x).trace) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hE := PG_E_snoc e ι x
  have hEn := (GS_E_snoc e ι x).2
  have hWok := PG_ok_W hR hlab hw hrot right
  have hok1 : PG_ok R.nb ((PG_W right a tl).take (q + 1)) :=
    PG_ok_of hWok fun y hy => Or.inl (List.mem_of_mem_take hy)
  have hok2 : PG_ok R.nb ((PG_W right a tl).drop q) :=
    PG_ok_of hWok fun y hy => Or.inl (List.mem_of_mem_drop hy)
  unfold PE_val PE_coef
  rw [hcf, hd, hS, hwt, hl, PG_coef_shift hD hN, List.map_append, List.prod_append,
    GS_prod_set _ [] _ _ hℓ, PG_prod_congr e hR hlab ι _ κ κ h hE (fun _ _ => rfl),
    PG_wt_congr e hR ι _ h hE R.weights (fun p hp => hp), List.map_singleton,
    List.prod_singleton, PG_wv_eq, PG_wv_eq, PE_wm_append, PE_wm_cons, PE_lm_proj, PE_wm_nil,
    Matrix.mul_one, PE_wm_cons, PE_lm_proj, hEn,
    PG_ok_wm e ι _ κ κ h hok1 hE (fun _ _ => rfl), PG_ok_wm e ι _ κ κ h hok2 hE (fun _ _ => rfl),
    Matrix.trace_mul_comm (Ea D N x)]
  have hc : ((D : ℂ) * N) ^ t *
      (PG_c D N ((PG_W right a tl).take (q + 1) ++ [PkgLetter.lw (.proj R.nb)]) *
        PG_c D N (PkgLetter.lw (.proj R.nb) :: (PG_W right a tl).drop q)) = PG_c D N w := by
    rw [ht]
    exact PG_c_cut hD hN _ _ _
  rw [← hc]
  ring

include hR hlab hw hrot in
/-- The value of a plug `𝔣𝔭₁` or `𝔦𝔫𝔰𝔢𝔯𝔱₁` of the light weight `k` at `(ι, x)`. -/
private lemma PG_val_plug (right : Bool) (k : ℕ) (b : Fin 2) (y : ℕ)
    (hk : R.weights[k]? = some (b, y)) (x : Fin D) (R' : PkgExpr) (hcf : R'.cf = R.cf)
    (hd : R'.dexp = R.dexp - 1) (hS : R'.S = R.S + 2) (hwt : R'.weights = R.weights.eraseIdx k)
    (hl : R'.loops = R.loops.set ℓ (PG_W right a tl ++ [.lw (.proj R.nb), .lw (.res b),
      .lw (.proj y), .lw (.res b), .lw (.proj R.nb)])) (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) :
    PE_val e (Fin.snoc (α := fun _ => Fin D) ι x) κ R' h = PE_coef D N R * PG_c D N w *
      (D : ℂ)⁻¹ * ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) * ((R.weights.eraseIdx k).map (PE_wt e ι h)).prod *
      (∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) *
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) * Ea D N x *
        (e.G h b * e.E ι y * e.G h b) * Ea D N x).trace := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hE := PG_E_snoc e ι x
  have hEn := (GS_E_snoc e ι x).2
  have hy : y < R.nb := (PG_wf_bound hR).2 (b, y) (List.mem_of_getElem? hk)
  have hWok := PG_ok_wm e ι (Fin.snoc (α := fun _ => Fin D) ι x) κ κ h
    (PG_ok_W hR hlab hw hrot right) hE (fun _ _ => rfl)
  unfold PE_val PE_coef
  rw [hcf, hd, hS, hwt, hl, GS_prod_set _ [] _ _ hℓ, PG_prod_congr e hR hlab ι _ κ κ h hE
    (fun _ _ => rfl), PG_wt_congr e hR ι _ h hE _ (fun p hp => List.mem_of_mem_eraseIdx hp),
    PG_wv_eq]
  have hc : PG_c D N (PG_W right a tl ++ [.lw (.proj R.nb), .lw (.res b), .lw (.proj y),
      .lw (.res b), .lw (.proj R.nb)]) = PG_c D N w := by
    rw [← PG_c_W D N hrot right]
    simp [PG_c, List.any_append, PG_isEnt_lw]
  rw [hc, PE_wm_append, PE_wm_cons, PE_wm_cons, PE_wm_cons, PE_wm_cons, PE_wm_cons, PE_wm_nil,
    PE_lm_proj, PE_lm_proj, PE_lm_res, hEn, hE y hy, hWok, zpow_sub_one₀ hD,
    show -(R.S + 2) = -R.S + -2 by ring, zpow_add₀ hN,
    show (N : ℂ) ^ (-2 : ℤ) = (N : ℂ)⁻¹ * (N : ℂ)⁻¹ by rw [_root_.zpow_neg, zpow_two, mul_inv]]
  simp only [Matrix.mul_one, Matrix.mul_assoc]
  ring

include hR hlab hw hrot in
/-- The value of a join `𝔣𝔭₂`, `𝔪𝔢𝔯𝔤𝔢`, `𝔦𝔫𝔰𝔢𝔯𝔱₂` or `𝔢𝔵𝔠𝔥𝔞𝔫𝔤𝔢` with the resolvent `q` of the
word `j` at `(ι, x)`. -/
private lemma PG_val_merge (right : Bool) (j : ℕ) (f : List PkgLetter)
    (hj : R.loops[j]? = some f) (hjℓ : j ≠ ℓ) (q : ℕ) (b : Fin 2) (x : Fin D) (R' : PkgExpr)
    (t : ℤ) (hcf : R'.cf = R.cf) (hd : R'.dexp = R.dexp + t) (hS : R'.S = R.S + 1 - t)
    (hwt : R'.weights = R.weights)
    (hl : R'.loops = (R.loops.set ℓ (PG_W right a tl ++ [.lw (.proj R.nb)] ++ f.rotate q ++
      [.lw (.res b), .lw (.proj R.nb)])).eraseIdx j)
    (ht : t = (if (!((PG_W right a tl ++ [PkgLetter.lw (.proj R.nb)] ++ f.rotate q ++
        [PkgLetter.lw (.res b), PkgLetter.lw (.proj R.nb)]).any PE_isEnt)) = true then 1 else 0) -
      (if (!(w.any PE_isEnt)) = true then 1 else 0) - (if (!(f.any PE_isEnt)) = true then 1 else 0))
    (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) :
    PE_val e (Fin.snoc (α := fun _ => Fin D) ι x) κ R' h = PE_coef D N R *
      (PG_c D N w * PG_c D N f) * (N : ℂ)⁻¹ * (R.weights.map (PE_wt e ι h)).prod *
      (∏ k ∈ ((Finset.range R.loops.length).erase ℓ).erase j,
        PE_wv e ι κ h (R.loops.getD k [])) *
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) * Ea D N x *
        (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.rotate q) * e.G h b) * Ea D N x).trace := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hjl : j < R.loops.length := (List.getElem?_eq_some_iff.1 hj).1
  have hE := PG_E_snoc e ι x
  have hEn := (GS_E_snoc e ι x).2
  have hWok := PG_ok_wm e ι (Fin.snoc (α := fun _ => Fin D) ι x) κ κ h
    (PG_ok_W hR hlab hw hrot right) hE (fun _ _ => rfl)
  have hfok : PG_ok R.nb (f.rotate q) :=
    PG_ok_of (PG_ok_loops hR hlab (List.mem_of_getElem? hj)) fun z hz =>
      Or.inl (List.mem_rotate.1 hz)
  have hFok := PG_ok_wm e ι (Fin.snoc (α := fun _ => Fin D) ι x) κ κ h hfok hE (fun _ _ => rfl)
  unfold PE_val PE_coef
  rw [hcf, hd, hS, hwt, hl, PG_coef_shift hD hN, GS_prod_set_eraseIdx _ [] _ _ _ hℓ hjl hjℓ,
    PG_prod_congr e hR hlab ι _ κ κ h hE (fun _ _ => rfl),
    PG_wt_congr e hR ι _ h hE R.weights (fun p hp => hp), PG_wv_eq]
  have hany : (PG_W right a tl ++ [PkgLetter.lw (.proj R.nb)] ++ f.rotate q ++
      [PkgLetter.lw (.res b), PkgLetter.lw (.proj R.nb)]).any PE_isEnt =
      (w.any PE_isEnt || f.any PE_isEnt) := by
    rw [← PG_any_W hrot right, ← PG_any_rotate PE_isEnt f q]
    simp [List.any_append, PG_isEnt_lw]
  have hc : ((D : ℂ) * N) ^ t * PG_c D N (PG_W right a tl ++ [PkgLetter.lw (.proj R.nb)] ++
      f.rotate q ++ [PkgLetter.lw (.res b), PkgLetter.lw (.proj R.nb)]) =
      PG_c D N w * PG_c D N f := by
    rw [ht]
    unfold PG_c
    rw [hany]
    exact PG_c_join hD hN _ _
  rw [← hc]
  simp only [PE_wm_append, PE_wm_cons, PE_wm_nil, PE_lm_proj, PE_lm_res, hEn, hWok, hFok,
    Matrix.mul_one, Matrix.mul_assoc]
  ring

include hR hlab hw hrot in
/-- The derivative structure of `fpkg` at the resolvent `q` of the expanded word, summed over the
entries of the block `x`. -/
private lemma PG_dent_W {right : Bool} (hf : R.ffocus = some (ℓ, r, right)) (q : ℕ) (b : Fin 2)
    (hqW : q < (PG_W right a tl).length) (hq : (PG_W right a tl)[q]? = some (.lw (.res b)))
    (x : Fin D) (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg ℓ (PG_W right a tl ++ [.ent 3 2]) q b 2 3) h =
      PE_coef D N R * PG_c D N w * (R.weights.map (PE_wt e ι h)).prod *
      (∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) *
      ((pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ ((PG_W right a tl).take (q + 1)) * Ea D N x).trace *
        (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ ((PG_W right a tl).drop q) * Ea D N x).trace) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hWok := PG_ok_W hR hlab hw hrot right
  have hok1 : PG_ok R.nb ((PG_W right a tl).take q) :=
    PG_ok_of hWok fun y hy => Or.inl (List.mem_of_mem_take hy)
  have hok2 : PG_ok R.nb ((PG_W right a tl).drop (q + 1)) :=
    PG_ok_of hWok fun y hy => Or.inl (List.mem_of_mem_drop hy)
  set K := PE_coef D N R * PG_c D N w * (R.weights.map (PE_wt e ι h)).prod *
    (∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) with hK
  set P := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ ((PG_W right a tl).take (q + 1)) with hP
  set Q := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ ((PG_W right a tl).drop q) with hQ
  have htake : (PG_W right a tl).take (q + 1) = (PG_W right a tl).take q ++ [.lw (.res b)] := by
    rw [List.take_add_one, hq]
    rfl
  have hdrop : (PG_W right a tl).drop q = .lw (.res b) :: (PG_W right a tl).drop (q + 1) := by
    rw [List.drop_eq_getElem_cons hqW, (List.getElem?_eq_some_iff.1 hq).2]
  have hval : ∀ i j : Idx D N,
      PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg ℓ (PG_W right a tl ++ [.ent 3 2]) q b 2 3) h =
        K * (P i i * Q j j) := by
    intro i j
    have h2 : PG_κ κ i j 2 = i := by simp [PG_κ]
    have h3 : PG_κ κ i j 3 = j := by simp [PG_κ]
    rw [PG_fpkg_eq hf hw hrot]
    unfold PE_ins PE_val PE_coef
    simp only [List.set_set]
    rw [GS_prod_set _ [] _ _ hℓ, PG_prod_congr e hR hlab ι ι _ _ h (fun _ _ => rfl)
      (PG_κ_lt κ i j), PG_wv_eq, List.take_append_of_le_length hqW.le,
      List.drop_append_of_le_length (by omega)]
    have hany : ((PG_W right a tl ++ [PkgLetter.ent 3 2]).any PE_isEnt) = true := by
      simp [List.any_append, PE_isEnt]
    have hc1 : PG_c D N ((PG_W right a tl).take q ++ [PkgLetter.lw (.res b), .ent 2 3,
        .lw (.res b)] ++ ((PG_W right a tl).drop (q + 1) ++ [.ent 3 2])) = 1 := by
      simp [PG_c, List.any_append, PE_isEnt]
    have hw2 : pkgWordMat (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i j)
        ((PG_W right a tl).take q ++ [PkgLetter.lw (.res b), .ent 2 3, .lw (.res b)] ++
          ((PG_W right a tl).drop (q + 1) ++ [.ent 3 2])) =
        P * PE_lm (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i j) (.ent 2 3) * Q *
          PE_lm (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i j) (.ent 3 2) := by
      rw [hP, hQ, htake, hdrop, PE_wm_append, PE_wm_append, PE_wm_append, PE_wm_cons, PE_wm_cons,
        PE_wm_cons, PE_wm_nil, PE_wm_cons, PE_wm_nil, PE_wm_append, PE_wm_cons, PE_wm_nil,
        PE_wm_cons, PE_lm_res,
        PG_ok_wm e ι ι κ (PG_κ κ i j) h hok1 (fun _ _ => rfl) (PG_κ_lt κ i j),
        PG_ok_wm e ι ι κ (PG_κ κ i j) h hok2 (fun _ _ => rfl) (PG_κ_lt κ i j)]
      simp only [PE_lm_res, Matrix.mul_one, Matrix.mul_assoc]
    rw [hc1, one_mul, hw2, PG_tr_ent2, h2, h3]
    simp only [hany, Bool.not_true, Bool.false_eq_true, ite_false, neg_neg]
    rw [hK]
    unfold PE_coef PG_c
    rcases hb : w.any PE_isEnt
    · simp only [Bool.false_eq_true, ite_false]
      rw [zpow_sub_one₀ hD, show -(R.S + 1) = -R.S + -1 by ring, zpow_add₀ hN,
        _root_.zpow_neg_one]
      ring
    · simp only [ite_true]
      ring
  simp only [hval]
  rw [← PG_block1 x P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

include hR hlab hw hrot in
/-- The derivative structure of `fpkg` at the light weight `k`, summed over the entries of the
block `x`. -/
private lemma PG_dent_wt {right : Bool} (hf : R.ffocus = some (ℓ, r, right)) (k : ℕ) (b : Fin 2)
    (y : ℕ) (x : Fin D) (hD : (D : ℂ) ≠ 0) (hN : (N : ℂ) ≠ 0) :
    ∑ i : Idx D N, ∑ j : Idx D N, (Ea D N x i i * Ea D N x j j) *
      PE_val e ι (PG_κ κ i j) (PE_wins R.fpkg k (b, y) 2 3) h =
      PE_coef D N R * PG_c D N w * (D : ℂ)⁻¹ * (N : ℂ)⁻¹ *
      ((R.weights.eraseIdx k).map (PE_wt e ι h)).prod *
      (∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) *
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) * Ea D N x *
        (e.G h b * e.E ι y * e.G h b) * Ea D N x).trace := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hWok := PG_ok_W hR hlab hw hrot right
  set K := PE_coef D N R * PG_c D N w * (D : ℂ)⁻¹ * (N : ℂ)⁻¹ *
    ((R.weights.eraseIdx k).map (PE_wt e ι h)).prod *
    (∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])) with hK
  set Y := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) with hY
  have hval : ∀ i j : Idx D N, PE_val e ι (PG_κ κ i j) (PE_wins R.fpkg k (b, y) 2 3) h =
      K * (Y i j * (e.G h b * e.E ι y * e.G h b) j i) := by
    intro i j
    have h2 : PG_κ κ i j 2 = i := by simp [PG_κ]
    have h3 : PG_κ κ i j 3 = j := by simp [PG_κ]
    rw [PG_fpkg_eq hf hw hrot]
    unfold PE_wins PE_val PE_coef
    simp only
    rw [List.map_append, List.prod_append, GS_prod_set _ [] _ _ hℓ,
      PG_prod_congr e hR hlab ι ι _ _ h (fun _ _ => rfl) (PG_κ_lt κ i j), List.map_singleton,
      List.prod_singleton, PG_wv_eq, PG_wv_eq, PG_c_ent]
    have hc1 : PG_c D N [PkgLetter.lw (.res b), .ent 2 3, .lw (.res b), .lw (.proj y)] = 1 := by
      simp [PG_c, PE_isEnt]
    rw [hc1, PE_wm_append, PE_wm_cons, PE_wm_nil, Matrix.mul_one, PE_trace_ent,
      PG_ok_wm e ι ι κ (PG_κ κ i j) h hWok (fun _ _ => rfl) (PG_κ_lt κ i j), h2, h3,
      ← hY]
    have hw2 : pkgWordMat (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i j)
        [PkgLetter.lw (.res b), .ent 2 3, .lw (.res b), .lw (.proj y)] =
        e.G h b * PE_lm (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i j) (.ent 2 3) * (e.G h b * e.E ι y) := by
      simp only [PE_wm_cons, PE_wm_nil, PE_lm_res, PE_lm_proj, Matrix.mul_one, Matrix.mul_assoc]
    rw [hw2, PG_tr_ent1, h2, h3, hK]
    unfold PE_coef PG_c
    rcases hb : w.any PE_isEnt
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true, neg_neg, neg_add, zpow_add₀ hN,
      zpow_sub₀ hD, zpow_one, _root_.zpow_neg_one]
    all_goals ring
  simp only [hval]
  rw [← PG_block2 x Y (e.G h b * e.E ι y * e.G h b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

include hR hlab hw hrot in
/-- The derivative structure of `fpkg` at the resolvent `q` of the word `j ≠ ℓ`, summed over the
entries of the block `x`. -/
private lemma PG_dent_f {right : Bool} (hf : R.ffocus = some (ℓ, r, right)) (j : ℕ)
    (f : List PkgLetter) (hj : R.loops[j]? = some f) (hjℓ : j ≠ ℓ) (q : ℕ) (b : Fin 2)
    (hqf : q < f.length) (hq : f[q]? = some (.lw (.res b))) (x : Fin D) (hD : (D : ℂ) ≠ 0)
    (hN : (N : ℂ) ≠ 0) :
    ∑ i : Idx D N, ∑ i' : Idx D N, (Ea D N x i i * Ea D N x i' i') *
      PE_val e ι (PG_κ κ i i') (PE_ins R.fpkg j f q b 2 3) h =
      PE_coef D N R * (PG_c D N w * PG_c D N f) * (R.weights.map (PE_wt e ι h)).prod *
      (∏ k ∈ ((Finset.range R.loops.length).erase ℓ).erase j,
        PE_wv e ι κ h (R.loops.getD k [])) *
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) * Ea D N x *
        (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.rotate q) * e.G h b) * Ea D N x).trace := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hjl : j < R.loops.length := (List.getElem?_eq_some_iff.1 hj).1
  have hWok := PG_ok_W hR hlab hw hrot right
  have hfok := PG_ok_loops hR hlab (List.mem_of_getElem? hj)
  have hok1 : PG_ok R.nb (f.take q) := PG_ok_of hfok fun y hy => Or.inl (List.mem_of_mem_take hy)
  have hok2 : PG_ok R.nb (f.drop (q + 1)) :=
    PG_ok_of hfok fun y hy => Or.inl (List.mem_of_mem_drop hy)
  set K := PE_coef D N R * (PG_c D N w * PG_c D N f) * (R.weights.map (PE_wt e ι h)).prod *
    (∏ k ∈ ((Finset.range R.loops.length).erase ℓ).erase j,
      PE_wv e ι κ h (R.loops.getD k [])) with hK
  set Y := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (PG_W right a tl) with hY
  set A := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.take q) with hA
  set B := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.drop (q + 1)) with hB
  have hrotf : f.rotate q = .lw (.res b) :: (f.drop (q + 1) ++ f.take q) := by
    rw [List.rotate_eq_drop_append_take hqf.le, List.drop_eq_getElem_cons hqf,
      (List.getElem?_eq_some_iff.1 hq).2]
    rfl
  have hZ : pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.rotate q) * e.G h b =
      e.G h b * B * A * e.G h b := by
    rw [hrotf, PE_wm_cons, PE_wm_append, PE_lm_res, hA, hB]
    simp only [Matrix.mul_assoc]
  have hval : ∀ i i' : Idx D N, PE_val e ι (PG_κ κ i i') (PE_ins R.fpkg j f q b 2 3) h =
      K * (Y i i' * (e.G h b * B * A * e.G h b) i' i) := by
    intro i i'
    have h2 : PG_κ κ i i' 2 = i := by simp [PG_κ]
    have h3 : PG_κ κ i i' 3 = i' := by simp [PG_κ]
    rw [PG_fpkg_eq hf hw hrot]
    unfold PE_ins PE_val PE_coef
    simp only
    have hWW : pkgWordMat (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i i')
        (PG_W right a tl ++ [PkgLetter.ent 3 2]) = pkgWordMat (e.G h) e.M (e.E ι) e.Lt
          (PG_κ κ i i') (PG_W right a tl) * PE_lm (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i i')
            (PkgLetter.ent 3 2) := by
      rw [PE_wm_append, PE_wm_cons, PE_wm_nil, Matrix.mul_one]
    rw [PG_prod_set_set _ [] _ _ _ hℓ hjl hjℓ, PG_prod_congr e hR hlab ι ι _ _ h (fun _ _ => rfl)
      (PG_κ_lt κ i i'), PG_wv_eq, PG_wv_eq, PG_c_ent, hWW, PE_trace_ent,
      PG_ok_wm e ι ι κ (PG_κ κ i i') h hWok (fun _ _ => rfl) (PG_κ_lt κ i i'), h2, h3, ← hY]
    have hc1 : PG_c D N (f.take q ++ [PkgLetter.lw (.res b), .ent 2 3, .lw (.res b)] ++
        f.drop (q + 1)) = 1 := by
      simp [PG_c, List.any_append, PE_isEnt]
    have hw2 : pkgWordMat (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i i')
        (f.take q ++ [PkgLetter.lw (.res b), .ent 2 3, .lw (.res b)] ++ f.drop (q + 1)) =
        (A * e.G h b) * PE_lm (e.G h) e.M (e.E ι) e.Lt (PG_κ κ i i') (.ent 2 3) *
          (e.G h b * B) := by
      rw [hA, hB, PE_wm_append, PE_wm_append, PE_wm_cons, PE_wm_cons, PE_wm_cons, PE_wm_nil,
        PG_ok_wm e ι ι κ (PG_κ κ i i') h hok1 (fun _ _ => rfl) (PG_κ_lt κ i i'),
        PG_ok_wm e ι ι κ (PG_κ κ i i') h hok2 (fun _ _ => rfl) (PG_κ_lt κ i i')]
      simp only [PE_lm_res, Matrix.mul_one, Matrix.mul_assoc]
    rw [hc1, one_mul, hw2, PG_tr_ent1, h2, h3, hK]
    have hany : (PG_W right a tl ++ [PkgLetter.ent 3 2]).any PE_isEnt = true := by
      simp [List.any_append, PE_isEnt]
    unfold PE_coef PG_c
    simp only [neg_neg]
    rcases hb : w.any PE_isEnt <;> rcases hbf : f.any PE_isEnt
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true,
      neg_add, zpow_add₀ hN, zpow_sub₀ hD, zpow_one, _root_.zpow_neg_one, Matrix.mul_assoc]
    all_goals ring
  simp only [hval]
  rw [← hZ, ← PG_block2 x Y (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.rotate q) * e.G h b),
    Finset.mul_sum, hZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

end Values

/-! ### The lists `fstep` and `dent` as sums -/

/-- The replacement `𝔣𝔯`. -/
private def PG_repR (R : PkgExpr) (ℓ : ℕ) (a : Fin 2) (tl : List PkgLetter) : PkgExpr :=
  { R with loops := R.loops.set ℓ (.lw (.det a) :: tl) }

/-- The light weight term `𝔣𝔠₁` or `𝔰𝔩𝔞𝔰𝔥₁`. -/
private def PG_slashR (R : PkgExpr) (ℓ : ℕ) (right : Bool) (a : Fin 2) (tl : List PkgLetter) :
    PkgExpr :=
  { R with
    dexp := R.dexp + 1, nb := R.nb + 1, weights := R.weights ++ [(a, R.nb)],
    loops := R.loops.set ℓ (if right then .lw (.proj R.nb) :: PG_W right a tl
      else PG_W right a tl ++ [.lw (.proj R.nb)]) }

/-- The change of the number of factors `⟨·⟩` of a cut at position `q` of the word `W`. -/
private def PG_dcut (R : PkgExpr) (w W : List PkgLetter) (q : ℕ) : ℤ :=
  (if (!((W.take (q + 1) ++ [PkgLetter.lw (.proj R.nb)]).any PE_isEnt)) = true then 1 else 0) +
    (if (!((PkgLetter.lw (.proj R.nb) :: W.drop q).any PE_isEnt)) = true then 1 else 0) -
    (if (!(w.any PE_isEnt)) = true then 1 else 0)

/-- The cut of the expanded word at its resolvent `q`. -/
private def PG_cutR (R : PkgExpr) (ℓ : ℕ) (w W : List PkgLetter) (q : ℕ) : PkgExpr :=
  { R with
    dexp := R.dexp + PG_dcut R w W q, S := R.S + 1 - PG_dcut R w W q, nb := R.nb + 1,
    loops := R.loops.set ℓ (W.take (q + 1) ++ [.lw (.proj R.nb)]) ++
      [.lw (.proj R.nb) :: W.drop q] }

/-- The plug of the light weight `k = (b, y)`. -/
private def PG_plugR (R : PkgExpr) (ℓ : ℕ) (W : List PkgLetter) (k : ℕ) (p : Fin 2 × ℕ) :
    PkgExpr :=
  { R with
    dexp := R.dexp - 1, S := R.S + 2, nb := R.nb + 1, weights := R.weights.eraseIdx k,
    loops := R.loops.set ℓ (W ++ [.lw (.proj R.nb), .lw (.res p.1), .lw (.proj p.2),
      .lw (.res p.1), .lw (.proj R.nb)]) }

/-- The change of the number of factors `⟨·⟩` of a join. -/
private def PG_djoin (R : PkgExpr) (w W f : List PkgLetter) (q : ℕ) (b : Fin 2) : ℤ :=
  (if (!((W ++ [PkgLetter.lw (.proj R.nb)] ++ f.rotate q ++
      [PkgLetter.lw (.res b), PkgLetter.lw (.proj R.nb)]).any PE_isEnt)) = true then 1 else 0) -
    (if (!(w.any PE_isEnt)) = true then 1 else 0) - (if (!(f.any PE_isEnt)) = true then 1 else 0)

/-- The join of the expanded word with the resolvent `q` of the word `j`. -/
private def PG_mergeR (R : PkgExpr) (ℓ : ℕ) (w W : List PkgLetter) (j : ℕ) (f : List PkgLetter)
    (q : ℕ) (b : Fin 2) : PkgExpr :=
  { R with
    dexp := R.dexp + PG_djoin R w W f q b, S := R.S + 1 - PG_djoin R w W f q b, nb := R.nb + 1,
    loops := (R.loops.set ℓ (W ++ [.lw (.proj R.nb)] ++ f.rotate q ++
      [.lw (.res b), .lw (.proj R.nb)])).eraseIdx j }

/-- The sum over the terms of `fstep` at the focus. -/
private lemma PG_fstep_sum {R : PkgExpr} {ℓ r : ℕ} {right : Bool} {w tl : List PkgLetter}
    {a : Fin 2} (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) (F : PkgExpr → ℂ) :
    (R.fstep.map F).sum = F (PG_repR R ℓ a tl) + F (PG_slashR R ℓ right a tl) +
      (∑ q ∈ Finset.range (PG_W right a tl).length,
        (if (right && q == 0) || (!right && q + 1 == (PG_W right a tl).length) then 0 else
          (PE_hit (PG_W right a tl) q).elim 0 fun _ => F (PG_cutR R ℓ w (PG_W right a tl) q))) +
      (∑ k ∈ Finset.range R.weights.length,
        (R.weights[k]?).elim 0 (fun p => F (PG_plugR R ℓ (PG_W right a tl) k p))) +
      ∑ j ∈ Finset.range R.loops.length, (if j = ℓ then 0 else
        (R.loops[j]?).elim 0 fun f => ∑ q ∈ Finset.range f.length,
          (PE_hit f q).elim 0 fun b => F (PG_mergeR R ℓ w (PG_W right a tl) j f q b)) := by
  unfold PkgExpr.fstep PkgExpr.fterms
  rw [hf]
  simp only [hw, hrot]
  have hWdef : (if right = true then PkgLetter.lw (LoopLetter.res a) :: tl ++
      [PkgLetter.lw (LoopLetter.det a)] else PkgLetter.lw (LoopLetter.det a) :: tl ++
      [PkgLetter.lw (LoopLetter.res a)]) = PG_W right a tl := rfl
  rw [hWdef, List.map_map, List.map_append, List.map_append, List.map_append, List.sum_append,
    List.sum_append, List.sum_append, GS_sum_filterMap, GS_sum_filterMap, PE_sum_flatMap,
    GS_sum_range, GS_sum_range, GS_sum_range]
  congr 1
  · congr 1
    · congr 1
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          Function.comp]
        rfl
      · refine Finset.sum_congr rfl fun q _ => ?_
        by_cases hc : (right && q == 0 || !right && q + 1 == (PG_W right a tl).length) = true
        · simp only [hc, ite_true, Option.elim_none]
        · simp only [hc, ite_false, Bool.false_eq_true]
          unfold PE_hit
          rcases (PG_W right a tl)[q]? with _ | ((b | b | y | o) | ⟨u, v⟩)
          all_goals simp only [Option.elim_none, Option.elim_some]
          rfl
    · refine Finset.sum_congr rfl fun k _ => ?_
      rcases R.weights[k]? with _ | ⟨b, y⟩
      all_goals simp only [Option.elim_none, Option.elim_some]
      rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = ℓ
    · simp only [hj, ite_true, List.map_nil, List.sum_nil]
    · simp only [hj, ite_false]
      rcases hf' : R.loops[j]? with _ | f
      · simp only [Option.elim_none, List.map_nil, List.sum_nil]
      · simp only [Option.elim_some]
        rw [GS_sum_filterMap, GS_sum_range]
        refine Finset.sum_congr rfl fun q _ => ?_
        unfold PE_hit
        rcases f[q]? with _ | ((b | b | y | o) | ⟨u, v⟩)
        all_goals simp only [Option.elim_none, Option.elim_some]
        rfl

private lemma PG_map_getD {α : Type*} (o : Option α) (f : α → ℂ) :
    (o.map f).getD 0 = o.elim 0 f := by
  cases o <;> rfl

/-- A sum over a range with one term singled out. -/
private lemma PG_sum_split (n ℓ : ℕ) (hℓ : ℓ < n) (g : ℕ → ℂ) :
    ∑ j ∈ Finset.range n, g j = g ℓ + ∑ j ∈ Finset.range n, (if j = ℓ then 0 else g j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hℓ)]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hℓ)]
  simp only [ite_true, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [Finset.ne_of_mem_erase hj]

private lemma PG_hit_ent (W : List PkgLetter) (u v : ℕ) (q : ℕ) :
    PE_hit (W ++ [PkgLetter.ent u v]) q = if q < W.length then PE_hit W q else none := by
  unfold PE_hit
  split_ifs with hq
  · rw [List.getElem?_append_left hq]
  · rcases Nat.lt_or_ge q (W.length + 1) with h1 | h1
    · have : q = W.length := by omega
      subst this
      rw [List.getElem?_append_right le_rfl]
      simp
    · rw [List.getElem?_eq_none (by simp; omega)]

/-- The sum over the derivative structures `dent` of `fpkg` at the focus: the resolvents of the
expanded word, of the other words and the light weights. -/
private lemma PG_dent_sum {R : PkgExpr} {ℓ r : ℕ} {right : Bool} {w tl : List PkgLetter}
    {a : Fin 2} (hf : R.ffocus = some (ℓ, r, right)) (hw : R.loops[ℓ]? = some w)
    (hrot : w.rotate r = .lw (.res a) :: tl) (F : PkgExpr → ℂ) :
    ((R.fpkg.dent 2 3).map F).sum =
      (∑ q ∈ Finset.range (PG_W right a tl).length, (PE_hit (PG_W right a tl) q).elim 0
        (fun b => F (PE_ins R.fpkg ℓ (PG_W right a tl ++ [.ent 3 2]) q b 2 3))) +
      (∑ j ∈ Finset.range R.loops.length, (if j = ℓ then 0 else
        (R.loops[j]?).elim 0 fun f => ∑ q ∈ Finset.range f.length,
          (PE_hit f q).elim 0 fun b => F (PE_ins R.fpkg j f q b 2 3))) +
      ∑ k ∈ Finset.range R.weights.length,
        (R.weights[k]?).elim 0 (fun p => F (PE_wins R.fpkg k p 2 3)) := by
  have hℓ : ℓ < R.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hL : R.fpkg.loops = R.loops.set ℓ (PG_W right a tl ++ [.ent 3 2]) := by
    rw [PG_fpkg_eq hf hw hrot]
  have hWt : R.fpkg.weights = R.weights := by
    rw [PG_fpkg_eq hf hw hrot]
  rw [PE_dent_eq, hL, hWt, List.map_append, List.sum_append, PE_sum_flatMap, PE_sum_filterMap,
    GS_sum_range, GS_sum_range, List.length_set, PG_sum_split _ ℓ hℓ]
  simp only [PE_sum_getD, PE_sum_filterMap, GS_sum_range, PG_map_getD]
  congr 1
  · congr 1
    · rw [List.getElem?_set_self hℓ]
      simp only [Option.elim_some]
      rw [List.length_append, List.length_singleton, Finset.sum_range_succ, PG_hit_ent]
      simp only [lt_irrefl, ite_false, Option.elim_none, add_zero]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp only [PG_hit_ent, Finset.mem_range.1 hq, ite_true]
    · refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rfl
      · rw [List.getElem?_set_ne (Ne.symm hj)]

/-! ### The expansion (5.83), (5.84) at a Hermitian array and fixed bound indices -/

/-- The part of the value of an expression of `fstep` at the bound indices `ι` of `𝓡`: the sum
over the new index `x` when the expression has one more bound index. -/
private def PG_SL {D N : ℕ} (e : LoopEnv D N) {R : PkgExpr} (ι : Fin R.nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) (R' : PkgExpr) : ℂ :=
  if R'.nb = R.nb + 1 then ∑ x : Fin D, PE_val e (Fin.snoc (α := fun _ => Fin D) ι x) κ R' h
  else PE_val e ι κ R' h

private lemma PG_SL_succ {D N : ℕ} (e : LoopEnv D N) {R : PkgExpr} (ι : Fin R.nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) {R' : PkgExpr} (hn : R'.nb = R.nb + 1) :
    PG_SL e ι κ h R' = ∑ x : Fin D, PE_val e (Fin.snoc (α := fun _ => Fin D) ι x) κ R' h := by
  simp [PG_SL, hn]

private lemma PG_SL_same {D N : ℕ} (e : LoopEnv D N) {R : PkgExpr} (ι : Fin R.nb → Fin D)
    (κ : ℕ → Idx D N) (h : Idx D N → Idx D N → ℂ) {R' : PkgExpr} (hn : R'.nb = R.nb) :
    PG_SL e ι κ h R' = PE_val e ι κ R' h := by
  simp [PG_SL, hn]

private lemma PG_blk_add {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (E : ι₁ → ι₂ → ι₃ → ℂ) (f g : ι₂ → ι₃ → ℂ) :
    ∑ x, ∑ i, ∑ j, E x i j * (f i j + g i j) =
      (∑ x, ∑ i, ∑ j, E x i j * f i j) + ∑ x, ∑ i, ∑ j, E x i j * g i j := by
  simp only [mul_add, Finset.sum_add_distrib]

private lemma PG_blk_sum {ι₁ ι₂ ι₃ β : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (E : ι₁ → ι₂ → ι₃ → ℂ) (S : Finset β) (f : β → ι₂ → ι₃ → ℂ) :
    ∑ x, ∑ i, ∑ j, E x i j * ∑ q ∈ S, f q i j = ∑ q ∈ S, ∑ x, ∑ i, ∑ j, E x i j * f q i j := by
  simp only [Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ q ∈ S, ∑ j, E x i j * f q i j :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x, ∑ q ∈ S, ∑ i, ∑ j, E x i j * f q i j :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma PG_blk_elim {ι₁ ι₂ ι₃ β : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (E : ι₁ → ι₂ → ι₃ → ℂ) (o : Option β) (f : β → ι₂ → ι₃ → ℂ) :
    ∑ x, ∑ i, ∑ j, E x i j * o.elim 0 (fun b => f b i j) =
      o.elim 0 (fun b => ∑ x, ∑ i, ∑ j, E x i j * f b i j) := by
  cases o <;> simp

private lemma PG_blk_ite {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (E : ι₁ → ι₂ → ι₃ → ℂ) (c : Prop) [Decidable c] (f : ι₂ → ι₃ → ℂ) :
    ∑ x, ∑ i, ∑ j, E x i j * (if c then 0 else f i j) =
      if c then 0 else ∑ x, ∑ i, ∑ j, E x i j * f i j := by
  split_ifs <;> simp

private lemma PG_elim_congr {β : Type*} (o : Option β) (f g : β → ℂ)
    (h : ∀ b, o = some b → f b = g b) : o.elim 0 f = o.elim 0 g := by
  cases o with
  | none => rfl
  | some b => exact h b rfl

private lemma PG_hit_spec {W : List PkgLetter} {q : ℕ} {b : Fin 2} (h : PE_hit W q = some b) :
    q < W.length ∧ W[q]? = some (.lw (.res b)) := by
  unfold PE_hit at h
  split at h
  · rename_i a ha
    cases h
    exact ⟨(List.getElem?_eq_some_iff.1 ha).1, ha⟩
  · cases h

/-- The expansion (5.83) [concrete_expansion_tl_2_heavy_package_right], (5.84)
[concrete_expansion_tl_2_loop] at a Hermitian array and fixed bound indices `ι`: the value of `𝓡`
minus the terms of `fstep` is `Σ_{ij} h̄_{ij} fpkg_{ij}` minus `N⁻¹ Σ_{i, j in one block}` of the
derivative structures `dent` of `fpkg`. -/
private lemma PG_step_one {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    {R : PkgExpr} (hR : R.wf = true) (hlab : PG_lab R) {ℓ r : ℕ} {right : Bool}
    {w tl : List PkgLetter} {a : Fin 2} (hf : R.ffocus = some (ℓ, r, right))
    (hw : R.loops[ℓ]? = some w) (hrot : w.rotate r = .lw (.res a) :: tl)
    (ι : Fin R.nb → Fin D) (κ : ℕ → Idx D N) :
    PE_val e ι κ R h - (R.fstep.map (PG_SL e ι κ h)).sum =
      (∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) * PE_val e ι (PG_κ κ i j) R.fpkg h) -
      (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
        ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum else 0) := by
  have hD0 : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set W := PG_W right a tl with hWdef
  set coefR := PE_coef D N R with hcoefR
  set cw := PG_c D N w with hcw
  set Wt := (R.weights.map (PE_wt e ι h)).prod with hWt
  set Lr := ∏ k ∈ (Finset.range R.loops.length).erase ℓ, PE_wv e ι κ h (R.loops.getD k [])
    with hLr
  set X := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ tl with hX
  set Y := pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ W with hY
  -- the values of the terms of `fstep`
  have hSLrep : PG_SL e ι κ h (PG_repR R ℓ a tl) = coefR * Wt * (cw * (e.M a * X).trace * Lr) := by
    rw [PG_SL_same e ι κ h (R' := PG_repR R ℓ a tl) rfl]
    exact PG_val_rep e hw hrot ι κ h _ rfl rfl rfl rfl rfl
  have hSLslash : PG_SL e ι κ h (PG_slashR R ℓ right a tl) = ∑ x : Fin D, coefR * (D : ℂ) * Wt *
      ntr ((e.G h a - e.M a) * Ea D N x) * (cw * (Y * Ea D N x).trace * Lr) := by
    rw [PG_SL_succ e ι κ h (R' := PG_slashR R ℓ right a tl) rfl]
    exact Finset.sum_congr rfl fun x _ =>
      PG_val_slash e hR hlab hw hrot ι κ h right x _ rfl rfl rfl rfl rfl hD0
  have hSLcut : ∀ q, PG_SL e ι κ h (PG_cutR R ℓ w W q) = ∑ x : Fin D, coefR * cw * (N : ℂ)⁻¹ *
      Wt * Lr * ((pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (W.take (q + 1)) * Ea D N x).trace *
        (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (W.drop q) * Ea D N x).trace) := by
    intro q
    rw [PG_SL_succ e ι κ h (R' := PG_cutR R ℓ w W q) rfl]
    exact Finset.sum_congr rfl fun x _ =>
      PG_val_cut e hR hlab hw hrot ι κ h right q x _ _ rfl rfl rfl rfl rfl rfl hD0 hN0
  have hSLplug : ∀ k b y, R.weights[k]? = some (b, y) →
      PG_SL e ι κ h (PG_plugR R ℓ W k (b, y)) = ∑ x : Fin D, coefR * cw * (D : ℂ)⁻¹ *
        ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) * ((R.weights.eraseIdx k).map (PE_wt e ι h)).prod * Lr *
        (Y * Ea D N x * (e.G h b * e.E ι y * e.G h b) * Ea D N x).trace := by
    intro k b y hk
    rw [PG_SL_succ e ι κ h (R' := PG_plugR R ℓ W k (b, y)) rfl]
    exact Finset.sum_congr rfl fun x _ =>
      PG_val_plug e hR hlab hw hrot ι κ h right k b y hk x _ rfl rfl rfl rfl rfl hD0 hN0
  have hSLmerge : ∀ j f, R.loops[j]? = some f → j ≠ ℓ → ∀ q b,
      PG_SL e ι κ h (PG_mergeR R ℓ w W j f q b) = ∑ x : Fin D, coefR * (cw * PG_c D N f) *
        (N : ℂ)⁻¹ * Wt * (∏ k ∈ ((Finset.range R.loops.length).erase ℓ).erase j,
          PE_wv e ι κ h (R.loops.getD k [])) *
        (Y * Ea D N x * (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (f.rotate q) * e.G h b) *
          Ea D N x).trace := by
    intro j f hj hjℓ q b
    rw [PG_SL_succ e ι κ h (R' := PG_mergeR R ℓ w W j f q b) rfl]
    exact Finset.sum_congr rfl fun x _ =>
      PG_val_merge e hR hlab hw hrot ι κ h right j f hj hjℓ q b x _ _ rfl rfl rfl rfl rfl rfl hD0
        hN0
  -- the derivative structures summed over the blocks
  set E : Fin D → Idx D N → Idx D N → ℂ := fun x i j => Ea D N x i i * Ea D N x j j with hE
  have hDSUM : ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
      ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum else 0) =
      (∑ q ∈ Finset.range W.length, (PE_hit W q).elim 0 (fun b => ∑ x, ∑ i, ∑ j, E x i j *
        PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg ℓ (W ++ [.ent 3 2]) q b 2 3) h)) +
      (∑ j' ∈ Finset.range R.loops.length, (if j' = ℓ then 0 else
        (R.loops[j']?).elim 0 fun f => ∑ q ∈ Finset.range f.length,
          (PE_hit f q).elim 0 fun b => ∑ x, ∑ i, ∑ j, E x i j *
            PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg j' f q b 2 3) h)) +
      ∑ k ∈ Finset.range R.weights.length, (R.weights[k]?).elim 0 (fun p => ∑ x, ∑ i, ∑ j,
        E x i j * PE_val e ι (PG_κ κ i j) (PE_wins R.fpkg k p 2 3) h) := by
    rw [GS_sum_block]
    simp only [PG_dent_sum hf hw hrot]
    simp only [hE, PG_blk_add, PG_blk_sum, PG_blk_elim, PG_blk_ite]
    rfl
  -- the plugs
  have e1 : ∑ k ∈ Finset.range R.weights.length,
      (R.weights[k]?).elim 0 (fun p => PG_SL e ι κ h (PG_plugR R ℓ W k p)) =
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range R.weights.length, (R.weights[k]?).elim 0 (fun p =>
        ∑ x, ∑ i, ∑ j, E x i j * PE_val e ι (PG_κ κ i j) (PE_wins R.fpkg k p 2 3) h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases hk : R.weights[k]? with _ | ⟨b, y⟩
    · simp
    · simp only [Option.elim_some]
      rw [hSLplug k b y hk, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [PG_dent_wt e hR hlab hw hrot ι κ h hf k b y x hD0 hN0]
      ring
  -- the joins
  have e2 : ∑ j ∈ Finset.range R.loops.length, (if j = ℓ then 0 else
      (R.loops[j]?).elim 0 fun f => ∑ q ∈ Finset.range f.length,
        (PE_hit f q).elim 0 fun b => PG_SL e ι κ h (PG_mergeR R ℓ w W j f q b)) =
      (N : ℂ)⁻¹ * ∑ j' ∈ Finset.range R.loops.length, (if j' = ℓ then 0 else
        (R.loops[j']?).elim 0 fun f => ∑ q ∈ Finset.range f.length,
          (PE_hit f q).elim 0 fun b => ∑ x, ∑ i, ∑ j, E x i j *
            PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg j' f q b 2 3) h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = ℓ
    · simp [hj]
    · simp only [hj, ite_false]
      rcases hf' : R.loops[j]? with _ | f
      · simp
      · simp only [Option.elim_some]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rcases hb : PE_hit f q with _ | b
        · simp
        · obtain ⟨hqf, hq⟩ := PG_hit_spec hb
          simp only [Option.elim_some]
          rw [hSLmerge j f hf' hj q b, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [PG_dent_f e hR hlab hw hrot ι κ h hf j f hf' hj q b hqf hq x hD0 hN0]
          ring
  -- the cuts of the expanded word and the resolvent it expands
  set t : ℕ → ℂ := fun q => ∑ x : Fin D, coefR * cw * Wt * Lr *
    ((pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (W.take (q + 1)) * Ea D N x).trace *
      (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (W.drop q) * Ea D N x).trace) with ht
  set T0 := ∑ x : Fin D, coefR * cw * Wt * Lr *
    ((e.G h a * Ea D N x).trace * (Y * Ea D N x).trace) with hT0
  have hq0 : ∃ q0, q0 < W.length ∧
      (∀ q, ((right && q == 0) || (!right && q + 1 == W.length)) = true ↔ q = q0) ∧
      PE_hit W q0 = some a ∧ t q0 = T0 := by
    have hG1 : pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ [.lw (.res a)] = e.G h a := by
      rw [PE_wm_cons, PE_lm_res, PE_wm_nil, Matrix.mul_one]
    cases right
    · refine ⟨tl.length + 1, by simp [hWdef, PG_W], fun q => ?_, ?_, ?_⟩
      · simp [hWdef, PG_W]
      · simp [PE_hit, hWdef, PG_W]
      · simp only [ht, hT0]
        have h1 : W.take (tl.length + 1 + 1) = W := List.take_of_length_le (by simp [hWdef, PG_W])
        have h2 : W.drop (tl.length + 1) = [.lw (.res a)] := by simp [hWdef, PG_W]
        rw [h1, h2, hG1]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    · refine ⟨0, by simp [hWdef, PG_W], fun q => ?_, ?_, ?_⟩
      · simp
      · simp [PE_hit, hWdef, PG_W]
      · simp only [ht, hT0]
        have h1 : W.take (0 + 1) = [.lw (.res a)] := by simp [hWdef, PG_W]
        rw [h1, hG1, List.drop_zero]
  obtain ⟨q0, hq0l, hq0e, hq0h, hq0t⟩ := hq0
  have e3 : (∑ q ∈ Finset.range W.length,
      (if (right && q == 0) || (!right && q + 1 == W.length) then 0 else
        (PE_hit W q).elim 0 fun _ => PG_SL e ι κ h (PG_cutR R ℓ w W q))) + (N : ℂ)⁻¹ * T0 =
      (N : ℂ)⁻¹ * ∑ q ∈ Finset.range W.length, (PE_hit W q).elim 0 (fun b =>
        ∑ x, ∑ i, ∑ j, E x i j *
          PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg ℓ (W ++ [.ent 3 2]) q b 2 3) h) := by
    have hDW : ∑ q ∈ Finset.range W.length, (PE_hit W q).elim 0 (fun b =>
        ∑ x, ∑ i, ∑ j, E x i j *
          PE_val e ι (PG_κ κ i j) (PE_ins R.fpkg ℓ (W ++ [.ent 3 2]) q b 2 3) h) =
        ∑ q ∈ Finset.range W.length, (PE_hit W q).elim 0 (fun _ => t q) := by
      refine Finset.sum_congr rfl fun q _ => PG_elim_congr _ _ _ fun b hb => ?_
      obtain ⟨hqW, hq⟩ := PG_hit_spec hb
      exact Finset.sum_congr rfl fun x _ =>
        PG_dent_W e hR hlab hw hrot ι κ h hf q b hqW hq x hD0 hN0
    rw [hDW]
    conv_rhs => rw [PG_sum_split _ q0 hq0l, hq0h, Option.elim_some, hq0t, mul_add]
    rw [add_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q = q0
    · subst hq
      simp only [(hq0e q).2 rfl, ite_true, mul_zero]
    · simp only [show ¬ ((right && q == 0 || !right && q + 1 == W.length) = true) from
        fun h' => hq ((hq0e q).1 h'), hq, Bool.false_eq_true, ite_false]
      cases PE_hit W q with
      | none => simp
      | some b =>
        simp only [Option.elim_some]
        rw [hSLcut q, ht, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
  -- the resolvent identity, the light weight term and `𝗆`
  have e4 : PE_val e ι κ R h - coefR * Wt * (cw * (e.M a * X).trace * Lr) -
      (∑ x : Fin D, coefR * (D : ℂ) * Wt * ntr ((e.G h a - e.M a) * Ea D N x) *
        (cw * (Y * Ea D N x).trace * Lr)) + (N : ℂ)⁻¹ * T0 =
      ∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) * PE_val e ι (PG_κ κ i j) R.fpkg h := by
    have hD' : D ≠ 0 := by omega
    have hN' : N ≠ 0 := by omega
    have hRv := PG_val_R e hw hrot ι κ h
    have hres := PG_res_id hD hN e hz h hh a X right
    have hYW : (if right then e.G h a * X * e.M a else e.M a * X * e.G h a) = Y := by
      rw [hY, hWdef, PG_wm_W]
    rw [hYW] at hres
    have hm := GS_m_id hD hN e hz a Y
    have hfp : ∀ i j, starRingEnd ℂ (h i j) * PE_val e ι (PG_κ κ i j) R.fpkg h =
        -(coefR * cw * Wt * Lr) * (starRingEnd ℂ (h i j) * Y i j) := by
      intro i j
      rw [PG_val_fpkg e hR hlab hw hrot ι κ h hf i j hD0 hN0]
      ring
    simp only [hfp, ← Finset.mul_sum]
    have hx : (∑ x : Fin D, coefR * (D : ℂ) * Wt * ntr ((e.G h a - e.M a) * Ea D N x) *
        (cw * (Y * Ea D N x).trace * Lr)) - (N : ℂ)⁻¹ * T0 =
        -(coefR * cw * Wt * Lr) * (((D : ℂ) * N) * ∑ x : Fin D,
          (D : ℂ) * ntr (e.M a * Ea D N x) * ntr (Y * Ea D N x)) := by
      rw [hT0, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GS_trace_ntr hD' hN' (e.G h a * Ea D N x), GS_trace_ntr hD' hN' (Y * Ea D N x)]
      have hs : ntr ((e.G h a - e.M a) * Ea D N x) =
          ntr (e.G h a * Ea D N x) - ntr (e.M a * Ea D N x) := by
        simp only [Matrix.sub_mul, ntr, Matrix.trace_sub, mul_sub]
      rw [hs]
      field_simp
      ring
    rw [hRv, hres, GS_trace_ntr hD' hN' Y]
    linear_combination (-(coefR * cw * Wt * Lr) * ((D : ℂ) * N)) * hm - hx
  -- the conclusion
  rw [PG_fstep_sum hf hw hrot, hSLrep, hSLslash, hDSUM, e1, e2]
  linear_combination e4 - e3

/-- The terms of `fstep` have the bound indices of `𝓡` or one more. -/
private lemma PG_step_nb (R : PkgExpr) (R' : PkgExpr) (h : R' ∈ R.fstep) :
    R'.nb = R.nb ∨ R'.nb = R.nb + 1 := by
  unfold PkgExpr.fstep at h
  obtain ⟨⟨o, R''⟩, hmem, rfl⟩ := List.mem_map.1 h
  unfold PkgExpr.fterms at hmem
  split at hmem
  · simp at hmem
  · rename_i ℓ r right hf
    split at hmem
    · simp at hmem
    · split at hmem
      · rename_i a tl hrot
        set W : List PkgLetter := if right = true then
          PkgLetter.lw (.res a) :: tl ++ [PkgLetter.lw (.det a)]
          else PkgLetter.lw (.det a) :: tl ++ [PkgLetter.lw (.res a)] with hWdef
        dsimp only at hmem
        rcases List.mem_append.1 hmem with hmem | hmem
        · rcases List.mem_append.1 hmem with hmem | hmem
          · rcases List.mem_append.1 hmem with hmem | hmem
            · rcases List.mem_cons.1 hmem with hmem | hmem
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                exact Or.inl rfl
              · rcases List.mem_cons.1 hmem with hmem | hmem
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
                  exact Or.inr rfl
                · simp at hmem
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hmem
              split at hq
              · simp at hq
              · split at hq
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                  exact Or.inr rfl
                · simp at hq
          · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hmem
            split at hj
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
              exact Or.inr rfl
            · simp at hj
        · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hmem
          split at hj
          · simp at hj
          · split at hj
            · simp at hj
            · obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hj
              split at hq
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq)
                exact Or.inr rfl
              · simp at hq
      · simp at hmem

private lemma PG_evalH_SL {D N : ℕ} (e : LoopEnv D N) {R : PkgExpr} (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (R' : PkgExpr) (hn : R'.nb = R.nb ∨ R'.nb = R.nb + 1) :
    R'.evalH e κ h = ∑ ι : Fin R.nb → Fin D, PG_SL e ι κ h R' := by
  rcases hn with hn | hn
  · rw [PE_evalH R' e κ h hn]
    exact Finset.sum_congr rfl fun ι _ => (PG_SL_same e ι κ h hn).symm
  · rw [PE_evalH R' e κ h hn, GS_sum_snoc]
    exact Finset.sum_congr rfl fun ι _ => (PG_SL_succ e ι κ h hn).symm

/-- The expansion (5.83) [concrete_expansion_tl_2_heavy_package_right], (5.84)
[concrete_expansion_tl_2_loop] at a Hermitian array: `𝓡 - Σ_{𝓡' ∈ fstep} 𝓡'` is
`Σ_{ij} h̄_{ij} fpkg_{ij}` minus `N⁻¹ Σ_{i, j in one block}` of the derivative structures of
`fpkg`. -/
private lemma PG_step_id {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (e : LoopEnv D N)
    (hz : ∀ a, 0 < (e.z a).im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    {R : PkgExpr} (hR : R.wf = true) (hlab : PG_lab R) {ℓ r : ℕ} {right : Bool}
    (hf : R.ffocus = some (ℓ, r, right)) (κ : ℕ → Idx D N) :
    R.evalH e κ h - (R.fstep.map fun R' => R'.evalH e κ h).sum =
      (∑ i : Idx D N, ∑ j : Idx D N, starRingEnd ℂ (h i j) * R.fpkg.evalH e (PG_κ κ i j) h) -
      (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
        ∑ ι : Fin R.nb → Fin D,
          ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum else 0) := by
  obtain ⟨w, hw, a, tl, hrot⟩ := PG_focus hf
  have hnb : R.fpkg.nb = R.nb := by rw [PG_fpkg_eq hf hw hrot]
  have hsum : (R.fstep.map fun R' => R'.evalH e κ h).sum =
      ∑ ι : Fin R.nb → Fin D, (R.fstep.map (PG_SL e ι κ h)).sum := by
    rw [← PE_lsum_comm]
    exact congrArg List.sum (List.map_congr_left fun R' hR' =>
      PG_evalH_SL e κ h R' (PG_step_nb R R' hR'))
  rw [hsum, PE_evalH R e κ h rfl, ← Finset.sum_sub_distrib]
  simp only [PG_step_one hD hN e hz h hh hR hlab hf hw hrot]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, PE_evalH _ e _ h hnb]
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp

/-! ### The terms `p + q ≤ 1` of Lemma 2.11 -/

/-- `∂_w 𝒢 = -c 𝒢 Δ_{uv} 𝒢` at labels with `κ u = i`, `κ v = j` (`res_dW`). -/
private lemma PG_hD_dW {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (κ : ℕ → Idx D N) (u v : ℕ) (hu : κ u = i) (hv : κ v = j)
    (a : Fin 2) (w0 : ℂ) :
    PE_dM dW (fun x => e.G (setEntry h i j x) a) w0 =
      (-(if i = j then (1 / 2 : ℂ) else 1)) • (e.G (setEntry h i j w0) a *
        PE_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) *
          e.G (setEntry h i j w0) a) := by
  ext k l
  rw [Matrix.smul_apply, PG_mul_ent, hu, hv, smul_eq_mul]
  have := congrFun (res_dW _ (PE_slot_herm e a) _ (PE_slot_im e he a) h hh i j k l).1 w0
  simp only [PE_dM, Matrix.of_apply]
  exact this.trans (by unfold LoopEnv.G; ring)

/-- `∂_w̄ 𝒢 = -c 𝒢 Δ_{vu} 𝒢` at labels with `κ u = i`, `κ v = j` (`res_dW`). -/
private lemma PG_hD_dWbar {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (κ : ℕ → Idx D N) (u v : ℕ) (hu : κ u = i) (hv : κ v = j)
    (a : Fin 2) (w0 : ℂ) :
    PE_dM dWbar (fun x => e.G (setEntry h i j x) a) w0 =
      (-(if i = j then (1 / 2 : ℂ) else 1)) • (e.G (setEntry h i j w0) a *
        PE_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent v u) *
          e.G (setEntry h i j w0) a) := by
  ext k l
  rw [Matrix.smul_apply, PG_mul_ent, hu, hv, smul_eq_mul]
  have := congrFun (res_dW _ (PE_slot_herm e a) _ (PE_slot_im e he a) h hh i j k l).2 w0
  simp only [PE_dM, Matrix.of_apply]
  exact this.trans (by unfold LoopEnv.G; ring)

/-- One derivative of the value of an expression along the slice `w ↦ setEntry h i j w`. -/
private lemma PG_d_evalH {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (i j : Idx D N) (he : ∀ a, (e.z a).im ≠ 0) (hh : (Matrix.of h).IsHermitian)
    (hD0 : (D : ℂ) ≠ 0) (hN0 : (N : ℂ) ≠ 0) {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : PE_Op Dop)
    (κ : ℕ → Idx D N) (u v : ℕ) (c : ℂ) (R' : PkgExpr) {n : ℕ} (hn : R'.nb = n)
    (hD : ∀ (ι : Fin n → Fin D) a w0, PE_dM Dop (fun x => e.G (setEntry h i j x) a) w0 =
      (-c) • (e.G (setEntry h i j w0) a *
        PE_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) *
          e.G (setEntry h i j w0) a)) (w0 : ℂ) :
    Dop (fun x => R'.evalH e κ (setEntry h i j x)) w0 =
      c * ∑ ι : Fin n → Fin D,
        ((R'.dent u v).map fun R'' => PE_val e ι κ R'' (setEntry h i j w0)).sum := by
  have e1 : (fun x => R'.evalH e κ (setEntry h i j x)) =
      fun x => ∑ ι : Fin n → Fin D, PE_val e ι κ R' (setEntry h i j x) :=
    funext fun x => PE_evalH R' e κ _ hn
  rw [e1, PE_Op.sum hO Finset.univ _ fun ι _ =>
    (PE_good_slice (PE_good_val e he ι κ R') h hh i j).differentiableAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ι _ => PE_dval e ι κ h i j he hh hD0 hN0 hO u v c w0 (hD ι · w0) R'

/-- The terms `p + q ≤ 1` of Lemma 2.11 [lem:complex_cumu] for `fpkg` and an entry in a
diagonal block: `N⁻¹ E` of the derivative structures `dent` of `fpkg`. -/
private lemma PG_low {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) {C : ℕ → ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) (R : PkgExpr)
    (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) (κ : ℕ → Idx D N) (i j : Idx D N)
    (hij : i.1 = j.1) {n : ℕ} (hn : R.fpkg.nb = n) :
    ccum (μ.map fun h => h i j) 0 1 / ((Nat.factorial 0 * Nat.factorial 0 : ℕ) : ℂ) *
        ∫ h, wirt 0 0 (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ +
      ccum (μ.map fun h => h i j) 1 1 / ((Nat.factorial 1 * Nat.factorial 0 : ℕ) : ℂ) *
        ∫ h, wirt 1 0 (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ +
      ccum (μ.map fun h => h i j) 0 2 / ((Nat.factorial 0 * Nat.factorial 1 : ℕ) : ℂ) *
        ∫ h, wirt 0 1 (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ =
      (N : ℂ)⁻¹ * ∫ h, ∑ ι : Fin n → Fin D,
        ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum ∂μ := by
  have hD0 : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have he : ∀ a, (e.z a).im ≠ 0 := fun a => (hz a).ne'
  have h2 : PG_κ κ i j 2 = i := by simp [PG_κ]
  have h3 : PG_κ κ i j 3 = j := by simp [PG_κ]
  obtain ⟨h01, h11, h02⟩ := GS_ccum_low hμ i j hij
  set Dsum : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ∑ ι : Fin n → Fin D,
    ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum with hDsum
  have hw10 : ∫ h, wirt 1 0 (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ =
      (if i = j then (1 / 2 : ℂ) else 1) * ∫ h, Dsum h ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one]
    rw [PG_d_evalH e h i j he hh hD0 hN0 PE_op_dW (PG_κ κ i j) 2 3 _ R.fpkg hn
      (fun ι a w0 => PG_hD_dW e ι h i j he hh _ 2 3 h2 h3 a w0), PE_setEntry_self h hh]
  have hw01 : i = j → ∫ h, wirt 0 1 (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w))
      (h i j) ∂μ = (if i = j then (1 / 2 : ℂ) else 1) * ∫ h, Dsum h ∂μ := by
    intro hd
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one]
    rw [PG_d_evalH e h i j he hh hD0 hN0 PE_op_dWbar (PG_κ κ i j) 2 3 _ R.fpkg hn
      (fun ι a w0 => PG_hD_dWbar e ι h i j he hh _ 3 2 (by rw [h3, hd]) (by rw [h2, hd]) a w0),
      PE_setEntry_self h hh]
  rw [h01, h11, h02, hw10]
  by_cases hd : i = j
  · rw [hw01 hd]
    simp only [hd, ite_true]
    simp
    ring
  · simp [hd]

/-- A `PE_good` function times `h̄_{ij}` is integrable for a member of the class. -/
private lemma PG_good_integrable_mul {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ)
    {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : PE_good f) (i j : Idx D N) :
    Integrable (fun h => f h * starRingEnd ℂ (h i j)) μ := by
  have := hμ.prob
  obtain ⟨hd, B, hB⟩ := hf
  have hm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ :=
    (Complex.continuous_conj.comp
      ((continuous_apply j).comp (continuous_apply i))).aestronglyMeasurable
  have hint : Integrable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ := by
    refine (integrable_norm_iff hm).1 ?_
    simpa using hμ.integrable 1 i j
  have hae : (fun h => f (symArr h)) =ᵐ[μ] f := by
    filter_upwards [hμ.herm] with h hh
    rw [symArr_of_isHermitian h hh]
  refine hint.bdd_mul (c := B) (hd.continuous.aestronglyMeasurable.congr hae) ?_
  filter_upwards [hμ.herm] with h hh using hB h hh

private lemma PG_good_evalH {D N : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0)
    (κ : ℕ → Idx D N) (R : PkgExpr) : PE_good fun h => R.evalH e κ h := by
  have e1 : (fun h => R.evalH e κ h) = fun h => ∑ ι : Fin R.nb → Fin D, PE_val e ι κ R h :=
    funext fun h => PE_evalH R e κ h rfl
  rw [e1]
  exact PE_good_sum _ _ fun ι _ => PE_good_val e he ι κ R

private lemma PG_good_lsum {D N n : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0)
    (ι : Fin n → Fin D) (κ : ℕ → Idx D N) :
    ∀ L : List PkgExpr, PE_good fun h => (L.map fun R => PE_val e ι κ R h).sum
  | [] => by simpa using PE_good_const (D := D) (N := N) 0
  | R :: L => by
    simp only [List.map_cons, List.sum_cons]
    exact PE_good_add (PE_good_val e he ι κ R) (PG_good_lsum e he ι κ L)

/-- The expansion (5.83) [concrete_expansion_tl_2_heavy_package_right], (5.84)
[concrete_expansion_tl_2_loop] in expectation with its exact remainder: `E 𝓡 - Σ_{𝓡'} E 𝓡' -
Σ_{2 ≤ p+q ≤ l} 𝓔^{(2)}_𝓡(p, q)` is the sum over the entries in the diagonal blocks of the
remainder of Lemma 2.11 [lem:complex_cumu] for `fpkg` at order `l`. -/
private lemma PG_exact {D N : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) {C : ℕ → ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) {R : PkgExpr}
    (hR : R.wf = true) (hlab : PG_lab R) {ℓ r : ℕ} {right : Bool}
    (hf : R.ffocus = some (ℓ, r, right)) (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (κ : ℕ → Idx D N) (l : ℕ) (hl : 1 ≤ l) :
    (∫ h, R.evalH e κ h ∂μ) - (R.fstep.map fun R' => ∫ h, R'.evalH e κ h ∂μ).sum -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0) =
      ∑ i : Idx D N, ∑ j : Idx D N,
        (if i.1 = j.1 then (∫ h, R.fpkg.evalH e (PG_κ κ i j) h * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
              ∫ h, wirt p q (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ
        else 0) := by
  have hprob := hμ.prob
  have he : ∀ a, (e.z a).im ≠ 0 := fun a => (hz a).ne'
  set A : Idx D N → Idx D N → ℂ :=
    fun i j => ∫ h, R.fpkg.evalH e (PG_κ κ i j) h * starRingEnd ℂ (h i j) ∂μ with hA
  set B : Idx D N → Idx D N → ℂ := fun i j => ∫ h, ∑ ι : Fin R.nb → Fin D,
    ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum ∂μ with hB
  set K : ℕ → ℕ → Idx D N → Idx D N → ℂ := fun p q i j =>
    ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
      ∫ h, wirt p q (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ with hK
  obtain ⟨w, hw, a, tl, hrot⟩ := PG_focus hf
  have hnb : R.fpkg.nb = R.nb := by rw [PG_fpkg_eq hf hw hrot]
  have hint : ∀ R' : PkgExpr, Integrable (fun h => R'.evalH e κ h) μ :=
    fun R' => PE_good_integrable hμ.herm (PG_good_evalH e he κ R')
  have hiA : ∀ i j : Idx D N,
      Integrable (fun h => starRingEnd ℂ (h i j) * R.fpkg.evalH e (PG_κ κ i j) h) μ := by
    intro i j
    simpa [mul_comm] using PG_good_integrable_mul hμ (PG_good_evalH e he (PG_κ κ i j) R.fpkg) i j
  have hiB : ∀ (i j : Idx D N), Integrable (fun h => if i.1 = j.1 then
      ∑ ι : Fin R.nb → Fin D, ((R.fpkg.dent 2 3).map fun R'' =>
        PE_val e ι (PG_κ κ i j) R'' h).sum else 0) μ := by
    intro i j
    split_ifs
    · exact PE_good_integrable hμ.herm
        (PE_good_sum _ _ fun ι _ => PG_good_lsum e he ι (PG_κ κ i j) _)
    · exact integrable_zero _ _ _
  -- the expectation of the identity at Hermitian arrays
  have h1 : (∫ h, R.evalH e κ h ∂μ) - (R.fstep.map fun R' => ∫ h, R'.evalH e κ h ∂μ).sum =
      (∑ i : Idx D N, ∑ j : Idx D N, A i j) -
        (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then B i j else 0) := by
    rw [← PE_integral_list (fun R' h => R'.evalH e κ h) hint,
      ← integral_sub (hint R) (by
        have : ∀ L : List PkgExpr,
            Integrable (fun h => (L.map fun R' => R'.evalH e κ h).sum) μ := by
          intro L
          induction L with
          | nil => simp
          | cons R' L ih =>
            simp only [List.map_cons, List.sum_cons]
            exact (hint R').add ih
        exact this _)]
    have hae : (fun h => R.evalH e κ h - (R.fstep.map fun R' => R'.evalH e κ h).sum) =ᵐ[μ]
        fun h => (∑ i : Idx D N, ∑ j : Idx D N,
          starRingEnd ℂ (h i j) * R.fpkg.evalH e (PG_κ κ i j) h) -
          (N : ℂ)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
            ∑ ι : Fin R.nb → Fin D,
              ((R.fpkg.dent 2 3).map fun R'' => PE_val e ι (PG_κ κ i j) R'' h).sum else 0) := by
      filter_upwards [hμ.herm] with h hh using PG_step_id hD hN e hz h hh hR hlab hf κ
    rw [integral_congr_ae hae, integral_sub (integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hiA i j)
      ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hiB i j).const_mul _),
      integral_const_mul, integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hiA i j,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hiB i j]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hiA i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hA, mul_comm]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hiB i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i.1 = j.1
      · simp only [hij, ite_true, hB]
      · simp [hij]
  -- the remainder terms `p + q ≥ 2`
  have h2 : ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0) =
      ∑ i : Idx D N, ∑ j : Idx D N,
        (if i.1 = j.1 then ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then K p q i j else 0) else 0) := by
    have e1 : ∀ p q, (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0) =
        ∑ i : Idx D N, ∑ j : Idx D N,
          (if 2 ≤ p + q then (if i.1 = j.1 then K p q i j else 0) else 0) := by
      intro p q
      by_cases hpq : 2 ≤ p + q
      · simp only [hpq, ite_true]
        rfl
      · simp [hpq]
    simp only [e1]
    rw [GS_sum_comm_tri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GS_sum_comm_tri]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i.1 = j.1 <;> simp [hij]
  rw [h1, h2]
  -- each entry in a diagonal block
  have h3 : ∀ i j : Idx D N, (if i.1 = j.1 then A i j -
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), K p q i j else 0) =
      A i j - (N : ℂ)⁻¹ * (if i.1 = j.1 then B i j else 0) -
        (if i.1 = j.1 then ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then K p q i j else 0) else 0) := by
    intro i j
    by_cases hij : i.1 = j.1
    · simp only [hij, ite_true]
      rw [GS_tri l hl, ← PG_low hD hN hμ R e hz κ i j hij hnb]
      simp only [hK, Nat.factorial_zero, Nat.factorial_one]
      ring
    · simp only [hij, ite_false, mul_zero, sub_zero]
      exact (GS_offblock hμ i j hij _).symm
  simp only [hA, hB, hK] at h3 ⊢
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h3 i j]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-! ### The values of the class as resolvent polynomials -/

/-- The letter is a resolvent. -/
private def PG_isRes (x : PkgLetter) : Bool :=
  match x with | .lw (.res _) => true | _ => false

/-- The letter is a limit `𝔐_a`. -/
private def PG_isDet (x : PkgLetter) : Bool :=
  match x with | .lw (.det _) => true | _ => false

/-- The letter is one of the two `Λ̃`. -/
private def PG_isLam (x : PkgLetter) : Bool :=
  match x with | .lw (.lamt _) => true | _ => false

/-- The entries of a word of the class are resolvent polynomials: degree the number of resolvents,
mass `(DN)^{|w|} β^{#𝔐} ‖Λ̃‖^{#Λ̃}`. -/
private lemma PG_word {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (κ : ℕ → Idx D N)
    (β : ℝ) (hβ : ∀ a, opNorm (e.M a) ≤ β) :
    ∀ (w : List PkgLetter) (i j : Idx D N),
      PolyRP e (w.countP PG_isRes)
        (((D : ℝ) * N) ^ w.length * β ^ (w.countP PG_isDet) * opNorm e.Lt ^ (w.countP PG_isLam))
        (fun h => pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w i j) := by
  intro w
  induction w with
  | nil =>
    intro i j
    refine PolyRP_mono le_rfl (by simp) (PolyRP_congr (fun h => ?_) (PolyRP_const e
      (if i = j then 1 else 0) 1 (by split_ifs <;> simp)))
    simp [PE_wm_nil, Matrix.one_apply]
  | cons x w ih =>
    intro i j
    have hstep : ∀ (X : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) (n : ℕ) (μ : ℝ),
        (∀ i k, PolyRP e n μ (fun h => X h i k)) →
        (∀ h, pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (x :: w) =
          X h * pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w) →
        PolyRP e (n + w.countP PG_isRes) (((D : ℝ) * N) * (μ * (((D : ℝ) * N) ^ w.length *
          β ^ (w.countP PG_isDet) * opNorm e.Lt ^ (w.countP PG_isLam))))
          (fun h => pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ (x :: w) i j) := by
      intro X n μ hX hXe
      exact PolyRP_congr (fun h => by rw [hXe h]) (PolyX_step e hX ih i j)
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · refine PolyRP_mono (le_of_eq (by simp [List.countP_cons, PG_isRes]; omega))
        (le_of_eq (by simp [PG_isDet, PG_isLam, pow_succ]; ring))
        (hstep (fun h => e.G h a) 1 1 (fun i k => PolyRP_res e a i k)
          (fun h => by rw [PE_wm_cons, PE_lm_res]))
    · refine PolyRP_mono (le_of_eq (by simp [PG_isRes]))
        (le_of_eq (by simp [List.countP_cons, PG_isDet, PG_isLam, pow_succ]; ring))
        (hstep (fun _ => e.M a) 0 β (fun i k => PolyRP_const e _ β
          ((PolyX_entry_le _ i k).trans (hβ a))) (fun h => by rw [PE_wm_cons, PE_lm_det]))
    · refine PolyRP_mono (le_of_eq (by simp [PG_isRes]))
        (le_of_eq (by simp [PG_isDet, PG_isLam, pow_succ]; ring))
        (hstep (fun _ => e.E ι y) 0 1 (fun i k => PolyRP_const e _ 1 (PolyX_E_entry e ι y i k))
          (fun h => by rw [PE_wm_cons, PE_lm_proj]))
    · refine PolyRP_mono (le_of_eq (by simp [PG_isRes]))
        (le_of_eq (by simp [List.countP_cons, PG_isDet, PG_isLam, pow_succ]; ring))
        (hstep (fun _ => e.Lt) 0 (opNorm e.Lt) (fun i k => PolyRP_const e _ _
          (PolyX_entry_le _ i k)) (fun h => by rw [PE_wm_cons, PE_lm_lamt]))
    · refine PolyRP_mono (le_of_eq (by simp [PG_isRes]))
        (le_of_eq (by simp [PG_isDet, PG_isLam, pow_succ]; ring))
        (hstep (fun _ => PE_lm (e.G 0) e.M (e.E ι) e.Lt κ (.ent u v)) 0 1
          (fun i k => PolyRP_const e _ 1
            (by simp only [PE_lm, Matrix.of_apply]; split_ifs <;> simp))
          (fun h => by rw [PE_wm_cons]; rfl))

/-- The factor of a word, trace or normalized trace, is a resolvent polynomial of mass
`(DN)^{|w| + 1} β^{#𝔐} ‖Λ̃‖^{#Λ̃}`, for `DN ≥ 1`. -/
private lemma PG_wv_poly {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (κ : ℕ → Idx D N)
    (hκ : 1 ≤ D * N) (β : ℝ) (hβ : ∀ a, opNorm (e.M a) ≤ β) (hβ0 : 0 ≤ β)
    (w : List PkgLetter) :
    PolyRP e (w.countP PG_isRes)
      (((D : ℝ) * N) ^ (w.length + 1) * β ^ (w.countP PG_isDet) * opNorm e.Lt ^ (w.countP PG_isLam))
      (fun h => PE_wv e ι κ h w) := by
  have hκ' : (1 : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hκ
  have hm0 : 0 ≤ ((D : ℝ) * N) ^ w.length * β ^ (w.countP PG_isDet) *
      opNorm e.Lt ^ (w.countP PG_isLam) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg hβ0 _))
      (pow_nonneg (norm_nonneg _) _)
  unfold PE_wv
  by_cases hb : w.any PE_isEnt = true
  · simp only [hb, ite_true]
    have h1 := PolyRP_sum e (Finset.univ : Finset (Idx D N))
      (F := fun i h => pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w i i)
      (fun i _ => PG_word e ι κ β hβ w i i)
    have hc : ((Finset.univ : Finset (Idx D N)).card : ℝ) = (D : ℝ) * N := by
      simp [Finset.card_univ, Fintype.card_prod]
    rw [hc] at h1
    refine PolyRP_congr (fun h => ?_) (PolyRP_mono le_rfl (le_of_eq ?_) h1)
    · simp [Matrix.trace]
    · ring
  · simp only [hb, Bool.false_eq_true, ite_false]
    refine PolyRP_mono le_rfl ?_ (PolyX_ntr e hκ fun i j => PG_word e ι κ β hβ w i j)
    rw [pow_succ]
    nlinarith

/-- The value of an expression of the class with two letters `Λ̃` is a resolvent polynomial over
the standard basis with the slots of `e`, of mass `|cf| (DN)^c (1 + ‖𝔐₀‖ + ‖𝔐₁‖)^c ‖Λ̃‖²`. -/
private lemma PG_poly (R : PkgExpr) (hlam : (R.loops.map fun w => w.countP PG_isLam).sum = 2) :
    ∃ c m : ℕ, ∀ (D N : ℕ) (e : LoopEnv D N) (κ : ℕ → Idx D N), 1 ≤ D * N →
      PolyRP e m (|(R.cf : ℝ)| * ((D : ℝ) * N) ^ c * (1 + opNorm (e.M 0) + opNorm (e.M 1)) ^ c *
        opNorm e.Lt ^ 2) (fun h => R.evalH e κ h) := by
  refine ⟨R.dexp.toNat + (-R.S).toNat + R.nb + 2 * R.weights.length +
      (R.loops.map fun w => w.length + 1).sum + (R.weights.length +
        (R.loops.map fun w => w.countP PG_isDet).sum),
    (R.loops.map fun w => w.countP PG_isRes).sum + R.weights.length, fun D N e κ hκ => ?_⟩
  have hD : 1 ≤ D := Nat.pos_of_mul_pos_right hκ
  have hN : 1 ≤ N := Nat.pos_of_mul_pos_left hκ
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hκ' : (1 : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hκ
  have hM0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
  have hM1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
  set β := 1 + opNorm (e.M 0) + opNorm (e.M 1) with hβdef
  have hβ1 : 1 ≤ β := by linarith
  have hβ : ∀ a, opNorm (e.M a) ≤ β := fun a => by linarith [PolyX_beta0 e a]
  have hLoop := fun ι : Fin R.nb → Fin D => PolyRP_prod e R.loops (fun w h => PE_wv e ι κ h w)
    (fun w => w.countP PG_isRes)
    (fun w => ((D : ℝ) * N) ^ (w.length + 1) * β ^ (w.countP PG_isDet) *
      opNorm e.Lt ^ (w.countP PG_isLam))
    (fun w _ => PG_wv_poly e ι κ hκ β hβ (by linarith) w)
  simp only [PolyX_prod_pow, hlam] at hLoop
  have hWt := fun ι : Fin R.nb → Fin D => PolyX_weights e ι hκ R.weights
  have hSum := PolyRP_sum e (Finset.univ : Finset (Fin R.nb → Fin D))
    (fun ι _ => PolyRP_mul (hWt ι) (hLoop ι))
  have hcard : ((Finset.univ : Finset (Fin R.nb → Fin D)).card : ℝ) = (D : ℝ) ^ R.nb := by
    simp [Finset.card_univ]
  rw [hcard] at hSum
  have hcoef : ‖((R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S))‖ ≤
      |(R.cf : ℝ)| * (((D : ℝ) * N) ^ R.dexp.toNat * ((D : ℝ) * N) ^ (-R.S).toNat) := by
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_intCast]
    have h1 : (D : ℝ) ^ R.dexp ≤ ((D : ℝ) * N) ^ R.dexp.toNat :=
      calc (D : ℝ) ^ R.dexp ≤ (D : ℝ) ^ (R.dexp.toNat : ℤ) :=
            zpow_le_zpow_right₀ hD' (Int.self_le_toNat _)
        _ = (D : ℝ) ^ R.dexp.toNat := zpow_natCast _ _
        _ ≤ ((D : ℝ) * N) ^ R.dexp.toNat :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h2 : (N : ℝ) ^ (-R.S) ≤ ((D : ℝ) * N) ^ (-R.S).toNat :=
      calc (N : ℝ) ^ (-R.S) ≤ (N : ℝ) ^ ((-R.S).toNat : ℤ) :=
            zpow_le_zpow_right₀ hN' (Int.self_le_toNat _)
        _ = (N : ℝ) ^ (-R.S).toNat := zpow_natCast _ _
        _ ≤ ((D : ℝ) * N) ^ (-R.S).toNat :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (-R.S) := zpow_nonneg (by positivity) _
    have h4 : (0 : ℝ) ≤ ((D : ℝ) * N) ^ R.dexp.toNat := by positivity
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 h3 h4) (abs_nonneg _)
  have hall := PolyRP_mul (PolyRP_const e ((R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)) _
    hcoef) hSum
  refine PolyRP_congr (fun h => ?_) (PolyRP_mono (le_of_eq (by omega)) ?_ hall)
  · rw [PE_evalH R e κ h rfl]
    unfold PE_val PE_coef
    rw [Finset.mul_sum]
    rfl
  · have hDκ : (D : ℝ) ≤ (D : ℝ) * N := by nlinarith
    have hLt0 : 0 ≤ opNorm e.Lt ^ 2 := sq_nonneg _
    calc |(R.cf : ℝ)| * (((D : ℝ) * N) ^ R.dexp.toNat * ((D : ℝ) * N) ^ (-R.S).toNat) *
          ((D : ℝ) ^ R.nb * ((((D : ℝ) * N) ^ 2 * (1 + opNorm (e.M 0) + opNorm (e.M 1))) ^
            R.weights.length * (((D : ℝ) * N) ^ (R.loops.map fun w => w.length + 1).sum *
              β ^ (R.loops.map fun w => w.countP PG_isDet).sum * opNorm e.Lt ^ 2)))
        ≤ |(R.cf : ℝ)| * (((D : ℝ) * N) ^ R.dexp.toNat * ((D : ℝ) * N) ^ (-R.S).toNat) *
          (((D : ℝ) * N) ^ R.nb * ((((D : ℝ) * N) ^ 2 * β) ^
            R.weights.length * (((D : ℝ) * N) ^ (R.loops.map fun w => w.length + 1).sum *
              β ^ (R.loops.map fun w => w.countP PG_isDet).sum * opNorm e.Lt ^ 2))) := by
          gcongr
      _ = |(R.cf : ℝ)| * ((D : ℝ) * N) ^ (R.dexp.toNat + (-R.S).toNat + R.nb +
            2 * R.weights.length + (R.loops.map fun w => w.length + 1).sum) *
          β ^ (R.weights.length + (R.loops.map fun w => w.countP PG_isDet).sum) *
          opNorm e.Lt ^ 2 := by ring_nf
      _ ≤ _ := by
          have hcf : 0 ≤ |(R.cf : ℝ)| := abs_nonneg _
          refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hκ' (Nat.le_add_right _ _)) hcf)
            (pow_le_pow_right₀ hβ1 (Nat.le_add_left _ _)) (pow_nonneg (by linarith) _)
            (mul_nonneg hcf (by positivity))) (sq_nonneg _)

private lemma PG_countP_lam (w : List PkgLetter) :
    w.countP PG_isLam = w.count (.lw (.lamt 0)) + w.count (.lw (.lamt 1)) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp [PG_isLam, ih]
    · simp [PG_isLam, ih]
    · simp [PG_isLam, ih]
    · fin_cases o <;> simp [List.countP_cons, PG_isLam, ih] <;> omega
    · simp [PG_isLam, ih]

/-- `fpkg` of an expression of the class has the two letters `Λ̃` of the class. -/
private lemma PG_lam_fpkg {R : PkgExpr} (hR : R.wf = true) {ℓ r : ℕ} {right : Bool}
    (hf : R.ffocus = some (ℓ, r, right)) :
    (R.fpkg.loops.map fun w => w.countP PG_isLam).sum = 2 := by
  obtain ⟨w, hw, a, tl, hrot⟩ := PG_focus hf
  have h2 : (R.loops.map fun w => w.countP PG_isLam).sum = 2 := by
    simp only [PkgExpr.wf, Bool.and_eq_true, beq_iff_eq] at hR
    obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := hR
    simp only [PG_countP_lam, List.sum_map_add, h0, h1]
  have hW : (PG_W right a tl ++ [PkgLetter.ent 3 2]).countP PG_isLam = w.countP PG_isLam := by
    rw [← (List.rotate_perm w r).countP_eq, hrot]
    unfold PG_W
    split_ifs <;> simp [List.countP_append, PG_isLam]
  have := sum_map_set (fun w : List PkgLetter => w.countP PG_isLam) R.loops ℓ w
    (PG_W right a tl ++ [PkgLetter.ent 3 2]) hw
  rw [PG_fpkg_eq hf hw hrot]
  simp only at this ⊢
  omega

/-! ### The remainder bound -/

/-- The expansion (5.83) [concrete_expansion_tl_2_heavy_package_right], (5.84)
[concrete_expansion_tl_2_loop] for every order `l ≥ l₀(𝓡, D')`: the remainder of Lemma 2.11
[lem:complex_cumu] at order `l`, summed over the entries, is at most `N^{-D'} ‖A‖²` for
`N ≥ N₀(l)`, uniformly in the class, the slots and the entry labels. -/
private lemma PG_gauss_all (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (R : PkgExpr) (hR : R.wf = true) (hlab : PG_lab R)
    (hf : R.ffocus.isSome = true) :
    ∀ D' : ℝ, 0 < D' → ∃ l₀ : ℕ, 1 ≤ l₀ ∧ ∀ l : ℕ, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) → ∀ κ : ℕ → Idx D N,
        ‖(∫ h, R.evalH e κ h ∂μ) - (R.fstep.map fun R' => ∫ h, R'.evalH e κ h ∂μ).sum -
            ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
              (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0)‖ ≤
          (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
  intro D' hD'
  obtain ⟨⟨ℓ, r, right⟩, hfoc⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨cP, m, hP⟩ := PG_poly R.fpkg (PG_lam_fpkg hR hfoc)
  set d := ⌈D'⌉₊ with hd
  refine ⟨2 * (cP + d + 4), by omega, fun l hl => ?_⟩
  set L := m + l + 1 with hL
  set E := cP + 1 + 1 + L + d + 2 with hE
  obtain ⟨Khp, hKhp0, hKhp⟩ := expansion_hp l m (8 * E) C
  obtain ⟨N₁, hN₁⟩ := GS_event D hD δA τ C₀ hδA hτ hC₀ C K ((2 * E + 2 : ℕ) : ℝ)
    (by positivity)
  set cf := |(R.fpkg.cf : ℝ)| with hcf
  set Q := (D : ℝ) ^ (cP + 2) * Khp * cf * 4 ^ cP * (2 + |K|) ^ 2 with hQ
  set s := Real.sqrt (2 * (D : ℝ) ^ 2 + 1) with hs
  refine ⟨max N₁ (max (72 ^ 4) ⌈Q * (18 ^ L + 2 ^ L * s)⌉₊), ?_⟩
  intro N hN μ hμ e hA hA2 hc hz hδ κ
  have hprob := hμ.prob
  have hNN₁ : N₁ ≤ N := le_of_max_le_left hN
  have hN72 : 72 ^ 4 ≤ N := le_of_max_le_left (le_of_max_le_right hN)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN72
  have hNQ : Q * (18 ^ L + 2 ^ L * s) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right (le_of_max_le_right hN))
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hDN : 1 ≤ D * N := Nat.mul_pos (by omega) (by omega)
  have hzpos : ∀ a, 0 < (e.z a).im := fun a => (hz a).2
  obtain ⟨-, hMn, -, hLt, -⟩ := GS_norms hD hN1 C₀ K hC₀ e hA2 hc hzpos hδ
  have hev := hN₁ N hNN₁ μ hμ e hA hA2 hc hz hδ
  set ε₀ := 2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-((2 * E + 2 : ℕ) : ℝ)) with hε₀
  set M := (N : ℝ) ^ (-(1 / 4 : ℝ)) with hM
  set η := min (e.z 0).im (e.z 1).im with hη
  have hη0 : 0 < η := lt_min (hzpos 0) (hzpos 1)
  have hηN : (N : ℝ) ^ (-1 + τ) ≤ η := by
    refine le_min ?_ ?_
    · have := (hz 0).1.2; rwa [abs_of_pos (hzpos 0)] at this
    · have := (hz 1).1.2; rwa [abs_of_pos (hzpos 1)] at this
  have hη1 : 1 + η⁻¹ ≤ 2 * N := by
    have h1 : η⁻¹ ≤ ((N : ℝ) ^ (-1 + τ))⁻¹ := inv_anti₀ (by positivity) hηN
    have h2 : ((N : ℝ) ^ (-1 + τ))⁻¹ ≤ N := by
      rw [← Real.rpow_neg hn0.le]
      calc (N : ℝ) ^ (-(-1 + τ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = N := Real.rpow_one _
    linarith
  have hM0 : 0 < M := by positivity
  have hM72 : 24 * M * 3 ≤ 1 := by
    have h1 : (72 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have := Real.rpow_le_rpow (by norm_num) (show ((72 : ℝ) ^ 4) ≤ N by exact_mod_cast hN72)
        (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      rwa [show ((72 : ℝ) ^ 4) = (72 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
        show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at this
    have h2 : M = ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hn0.le _
    rw [h2]
    have h3 : ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹ ≤ 1 / 72 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hε₀0 : 0 ≤ ε₀ := by positivity
  set Bnd := Khp * (cf * ((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2) *
    ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * 3) ^ (m + l + 1) +
      (2 * N) ^ (m + l + 1) * Real.sqrt (ε₀ + ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-((8 * E : ℕ) : ℝ))))
    with hBnd
  have hBnd0 : 0 ≤ Bnd := by positivity
  have herr : ∀ (i j : Idx D N), i.1 = j.1 →
      ‖(∫ h, R.fpkg.evalH e (PG_κ κ i j) h * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
            ∫ h, wirt p q (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ‖ ≤
        Bnd := by
    intro i j hij
    obtain ⟨P, hPe, hPt, hPm⟩ := hP D N e (PG_κ κ i j) hDN
    have hΞ : ∀ p ∈ GS_Xi e, p.1.IsHermitian ∧ η ≤ p.2.im := by
      intro p hp
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
      refine ⟨GS_slot_herm e b, ?_⟩
      fin_cases b
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hVn : ∀ x ∈ GS_V D N, ∑ r, ‖x r‖ ^ 2 ≤ 1 := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
      simp
    have hVi : ∀ k : Idx D N, Pi.single k (1 : ℂ) ∈ GS_V D N := fun k =>
      Finset.mem_image_of_mem _ (Finset.mem_univ k)
    have hP' : ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ GS_V D N ∧ f.2.1 ∈ GS_V D N ∧
        ∃ p ∈ GS_Xi e, f.2.2 = p ∨ f.2.2 = (p.1, starRingEnd ℂ p.2) := by
      intro t ht
      refine ⟨(hPt t ht).1, fun f hf => ?_⟩
      obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, b, hb⟩ := (hPt t ht).2 f hf
      refine ⟨hk ▸ hVi k, hk' ▸ hVi k', ((e.c b : ℂ) • lam D N e.A, e.z b),
        Finset.mem_image_of_mem _ (Finset.mem_univ b), ?_⟩
      rw [hb]
      by_cases hs : e.s b
      · right; simp [hs]
      · left; simp [hs]
    have key := hKhp D N 1 μ hμ (GS_Xi e) η hη0 hΞ i j (GS_V D N) (hVi i) (hVi j) hVn P hP'
      3 M ε₀ (by norm_num) hM0 hM72 hε₀0 hev
    have e1 : (fun h => R.fpkg.evalH e (PG_κ κ i j) h) = fun h => resPolyEval P h :=
      funext hPe
    have e2 : ∀ p q, (fun h => wirt p q (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w))
        (h i j)) = fun h => wirt p q (fun w => resPolyEval P (setEntry h i j w)) (h i j) := by
      intro p q
      funext h
      rw [show (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) =
        fun w => resPolyEval P (setEntry h i j w) from funext fun w => hPe _]
    simp only [e1]
    refine key.trans ?_
    have hmass : (P.map fun t => ‖t.1‖).sum ≤
        cf * ((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2 := by
      refine hPm.trans ?_
      have hM01 : 1 + opNorm (e.M 0) + opNorm (e.M 1) ≤ 4 := by
        linarith [hMn 0, hMn 1]
      have hLt0 : 0 ≤ opNorm e.Lt := norm_nonneg _
      have hm0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
      have hm1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
      have hcf0 : 0 ≤ cf := abs_nonneg _
      gcongr
    have hL1 : (1 + η⁻¹) ^ (m + l + 1) ≤ (2 * N) ^ (m + l + 1) :=
      pow_le_pow_left₀ (by positivity) hη1 _
    rw [hBnd]
    gcongr
  rw [PG_exact hD hN1 hμ hR hlab hfoc e hzpos κ l (by omega)]
  have hsum : ‖∑ i : Idx D N, ∑ j : Idx D N,
      (if i.1 = j.1 then (∫ h, R.fpkg.evalH e (PG_κ κ i j) h * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
            ∫ h, wirt p q (fun w => R.fpkg.evalH e (PG_κ κ i j) (setEntry h i j w)) (h i j) ∂μ
      else 0)‖ ≤ ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : Idx D N, ∑ _j : Idx D N, Bnd :=
          Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
            split_ifs with hij
            · exact herr i j hij
            · simpa using hBnd0)
      _ = ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  have hT1 : (N : ℝ) ^ (-((l : ℝ) + 2) / 2) ≤ ((N : ℝ) ^ (cP + 1 + d + 3))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn0.le]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have : (2 * ((cP + d + 4 : ℕ) : ℝ)) ≤ l := by exact_mod_cast hl
    push_cast at this ⊢
    linarith
  have hT2 : Real.sqrt (ε₀ + ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-((8 * E : ℕ) : ℝ))) =
      s * ((N : ℝ) ^ E)⁻¹ := by
    have h14 : (N : ℝ) ^ ((1 : ℝ) / 2) * M = (N : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hM, ← Real.rpow_add hn0]; norm_num
    have hk : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ (-((8 * E : ℕ) : ℝ)) = ((N : ℝ) ^ (2 * E))⁻¹ := by
      rw [← Real.rpow_mul hn0.le, ← Real.rpow_natCast, ← Real.rpow_neg hn0.le]
      congr 1
      push_cast
      ring
    have hε : ε₀ = 2 * (D : ℝ) ^ 2 * ((N : ℝ) ^ (2 * E))⁻¹ := by
      rw [hε₀, Real.rpow_neg hn0.le, Real.rpow_natCast]
      field_simp
      ring
    rw [h14, hk, hε, show 2 * (D : ℝ) ^ 2 * ((N : ℝ) ^ (2 * E))⁻¹ + ((N : ℝ) ^ (2 * E))⁻¹ =
      (2 * (D : ℝ) ^ 2 + 1) * (((N : ℝ) ^ E)⁻¹) ^ 2 by rw [pow_mul']; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hfin : ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd ≤ ((N : ℝ) ^ (d + 1))⁻¹ * opNorm e.A ^ 2 := by
    have hA0 : 0 ≤ opNorm e.A ^ 2 := sq_nonneg _
    have hK0 : 0 ≤ (2 + |K|) := by positivity
    have hcf0 : 0 ≤ cf := abs_nonneg _
    have hnum := GS_num (N : ℝ) hn1 Q s L (cP + 1) d E hE hNQ
    have hb1 : Bnd ≤ Khp * (cf * ((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2) *
        (((N : ℝ) ^ (cP + 1 + d + 3))⁻¹ * 18 ^ L +
          2 ^ L * (N : ℝ) ^ L * (s * ((N : ℝ) ^ E)⁻¹)) := by
      rw [hBnd, hT2, show (6 * 3 : ℝ) = 18 by norm_num]
      gcongr
      exact le_of_eq (mul_pow _ _ _)
    calc ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd
        ≤ ((D : ℝ) * N) * ((D : ℝ) * N) *
          (Khp * (cf * ((D : ℝ) * N) ^ cP * 4 ^ cP * ((2 + |K|) * opNorm e.A) ^ 2) *
          (((N : ℝ) ^ (cP + 1 + d + 3))⁻¹ * 18 ^ L + 2 ^ L * (N : ℝ) ^ L *
            (s * ((N : ℝ) ^ E)⁻¹))) :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (Q * (N : ℝ) ^ (cP + 1 + 1) * (((N : ℝ) ^ (cP + 1 + d + 3))⁻¹ * 18 ^ L +
          2 ^ L * (N : ℝ) ^ L * (s * ((N : ℝ) ^ E)⁻¹))) * opNorm e.A ^ 2 := by
          rw [hQ]; ring
      _ ≤ ((N : ℝ) ^ (d + 1))⁻¹ * opNorm e.A ^ 2 := mul_le_mul_of_nonneg_right hnum hA0
  have hD'd : ((N : ℝ) ^ (d + 1))⁻¹ ≤ (N : ℝ) ^ (-D') := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn0.le]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have := Nat.le_ceil D'
    push_cast
    linarith
  calc _ ≤ ((D : ℝ) * N) * ((D : ℝ) * N) * Bnd := hsum
    _ ≤ ((N : ℝ) ^ (d + 1))⁻¹ * opNorm e.A ^ 2 := hfin
    _ ≤ (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := mul_le_mul_of_nonneg_right hD'd (sq_nonneg _)

/-! ### The tree sum -/

/-- Bounds that hold for every `l ≥ l₀(𝓡)` and `N ≥ N₀(𝓡, l)`, for each expression of a list, add
up over the list with common `l₀` and `N₀`. -/
private lemma PG_combine (D : ℕ) (L : List PkgExpr)
    (Bd : PkgExpr → ℕ → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N →
      (ℕ → Idx D N) → ℝ)
    (Hyp : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → Prop)
    (X : (N : ℕ) → LoopEnv D N → ℝ)
    (h : ∀ R ∈ L, ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ μ e, Hyp N μ e →
      ∀ κ, Bd R l N μ e κ ≤ X N e) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ μ e, Hyp N μ e → 0 ≤ X N e → ∀ κ,
      (L.map fun R => Bd R l N μ e κ).sum ≤ L.length * X N e := by
  induction L with
  | nil => exact ⟨0, fun l _ => ⟨0, fun N _ μ e _ hX κ => by simp⟩⟩
  | cons R L ih =>
    obtain ⟨l₁, h₁⟩ := h R List.mem_cons_self
    obtain ⟨l₂, h₂⟩ := ih fun R' hR' => h R' (List.mem_cons_of_mem _ hR')
    refine ⟨max l₁ l₂, fun l hl => ?_⟩
    obtain ⟨N₁, hN₁⟩ := h₁ l (le_of_max_le_left hl)
    obtain ⟨N₂, hN₂⟩ := h₂ l (le_of_max_le_right hl)
    refine ⟨max N₁ N₂, fun N hN μ e hH hX κ => ?_⟩
    have a1 := hN₁ N (le_of_max_le_left hN) μ e hH κ
    have a2 := hN₂ N (le_of_max_le_right hN) μ e hH hX κ
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

/-- A sum over a list is bounded by the sum of the norms. -/
private lemma PG_norm_list_sum (L : List PkgExpr) (f : PkgExpr → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map fun R => ‖f R‖).sum := by
  induction L with
  | nil => simp
  | cons R L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

/-- One round of the further expansion: the expressions of the list minus those of the next round
minus the remainders of the expressions expanded is the sum over the list of the expansions of
the expressions that are not stopped. -/
private lemma PG_err_split (ε : ℝ) (E Rm : PkgExpr → ℂ) :
    ∀ L : List PkgExpr, (L.map E).sum -
        ((L.flatMap fun R => if R.FStopped ε then [R] else R.fstep).map E).sum -
        ((L.filter fun R => decide (¬ R.FStopped ε)).map Rm).sum =
      (L.map fun R => if R.FStopped ε then 0 else E R - (R.fstep.map E).sum - Rm R).sum
  | [] => by simp
  | R :: L => by
      have ih := PG_err_split ε E Rm L
      by_cases hR : R.FStopped ε
      · simp only [List.map_cons, List.sum_cons, List.flatMap_cons, hR, ite_true, List.map_append,
          List.sum_append, List.filter_cons, decide_not, decide_true, Bool.not_true,
          Bool.false_eq_true, ite_false, List.map_nil, List.sum_nil, add_zero] at ih ⊢
        linear_combination ih
      · simp only [List.map_cons, List.sum_cons, List.flatMap_cons, hR, ite_false, List.map_append,
          List.sum_append, List.filter_cons, decide_not, decide_false, Bool.not_false,
          ite_true] at ih ⊢
        linear_combination ih

/-- The tree sum of the further expansion for a list of expressions of the class with labels in
`{0, 1}`: after `n` rounds, for every `l ≥ l₀` and `N ≥ N₀(l)`. -/
private lemma PG_tree (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ K ε : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) :
    ∀ n : ℕ, ∀ L : List PkgExpr, (∀ R ∈ L, R.wf = true ∧ PG_lab R) → ∀ D' : ℝ, 0 < D' →
      ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) → ∀ κ : ℕ → Idx D N,
        ‖(L.map fun R => ∫ h, R.evalH e κ h ∂μ).sum -
            ((fIter ε n L).map fun R => ∫ h, R.evalH e κ h ∂μ).sum -
            ((fInner ε n L).map fun R =>
              ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
                (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0)).sum‖ ≤
          (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro L hL D' hD'
    refine ⟨0, fun l _ => ⟨0, fun N _ μ hμ e _ _ _ _ _ κ => ?_⟩⟩
    simp only [fIter, fInner, sub_self, List.map_nil, List.sum_nil, norm_zero]
    positivity
  | succ n ih =>
    intro L hL D' hD'
    set L' := L.flatMap fun R => if R.FStopped ε then [R] else R.fstep with hL'def
    have hL' : ∀ R ∈ L', R.wf = true ∧ PG_lab R := by
      intro R' hR'
      obtain ⟨R, hR, hR'R⟩ := List.mem_flatMap.1 hR'
      by_cases hs : R.FStopped ε
      · simp only [hs, ite_true, List.mem_singleton] at hR'R
        exact hR'R ▸ hL R hR
      · simp only [hs, ite_false] at hR'R
        exact ⟨pkg_step_wf R (hL R hR).1 R' hR'R, PG_step_lab R (hL R hR).2 R' hR'R⟩
    obtain ⟨l₁, hl₁⟩ := ih L' hL' (D' + 1) (by linarith)
    set Hyp : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → Prop :=
      fun N μ e => LLClass D N C 1 μ ∧ opNorm e.A ≤ (N : ℝ) ^ (-δA) ∧
        2 * C₀ * opNorm e.A ≤ 1 / 10 ∧ (∀ a, |e.c a| ≤ C₀) ∧
        (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) ∧ |e.δ| ≤ K * avgSq (lam D N e.A) with hHyp
    set Bd : PkgExpr → ℕ → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N →
        (ℕ → Idx D N) → ℝ :=
      fun R l N μ e κ => ‖if R.FStopped ε then 0 else (∫ h, R.evalH e κ h ∂μ) -
        (R.fstep.map fun R' => ∫ h, R'.evalH e κ h ∂μ).sum -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0)‖ with hBd
    set X : (N : ℕ) → LoopEnv D N → ℝ := fun N e => (N : ℝ) ^ (-(D' + 1)) * opNorm e.A ^ 2
      with hX
    have hT : ∀ R ∈ L, ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ μ e, Hyp N μ e →
        ∀ κ, Bd R l N μ e κ ≤ X N e := by
      intro R hRL
      by_cases hs : R.FStopped ε
      · refine ⟨0, fun l _ => ⟨0, fun N _ μ e _ κ => ?_⟩⟩
        simp only [hBd, hX, hs, ite_true, norm_zero]
        positivity
      · have hfs : R.ffocus.isSome = true := by
          simp only [PkgExpr.FStopped, not_or] at hs
          exact Option.ne_none_iff_isSome.1 hs.2
        obtain ⟨l₀, -, hl₀⟩ := PG_gauss_all D hD δA τ C₀ K hδA hτ hC₀ C R (hL R hRL).1
          (hL R hRL).2 hfs (D' + 1) (by linarith)
        refine ⟨l₀, fun l hl => ?_⟩
        obtain ⟨N₀, hN₀⟩ := hl₀ l hl
        refine ⟨N₀, fun N hN μ e ⟨hμ, hA, hA2, hc, hz, hδ⟩ κ => ?_⟩
        simp only [hBd, hX, hs, ite_false]
        exact hN₀ N hN μ hμ e hA hA2 hc hz hδ κ
    obtain ⟨l₂, hl₂⟩ := PG_combine D L Bd Hyp X hT
    refine ⟨max l₁ l₂, fun l hl => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hl₁ l (le_of_max_le_left hl)
    obtain ⟨N₂, hN₂⟩ := hl₂ l (le_of_max_le_right hl)
    refine ⟨max (max N₁ N₂) (L.length + 1), fun N hN μ hμ e hA hA2 hc hz hδ κ => ?_⟩
    have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
    have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
    have hNL : L.length + 1 ≤ N := le_of_max_le_right hN
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hX0 : 0 ≤ X N e := by simp only [hX]; positivity
    have b1 := hN₁ N hN1 μ hμ e hA hA2 hc hz hδ κ
    have b2 := hN₂ N hN2 μ e ⟨hμ, hA, hA2, hc, hz, hδ⟩ hX0 κ
    set E : PkgExpr → ℂ := fun R => ∫ h, R.evalH e κ h ∂μ with hE
    set Rm : PkgExpr → ℂ := fun R => ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0) with hRm
    have hsplit := PG_err_split ε E Rm L
    have e1 : (L.map E).sum - ((fIter ε (n + 1) L).map E).sum -
        ((fInner ε (n + 1) L).map Rm).sum =
        (L.map fun R => if R.FStopped ε then 0 else E R - (R.fstep.map E).sum - Rm R).sum +
        ((L'.map E).sum - ((fIter ε n L').map E).sum - ((fInner ε n L').map Rm).sum) := by
      simp only [fIter, fInner, List.map_append, List.sum_append]
      rw [← hsplit]
      ring
    rw [e1]
    have b3 : ‖(L.map fun R => if R.FStopped ε then 0 else E R - (R.fstep.map E).sum - Rm R).sum‖ ≤
        L.length * X N e := (PG_norm_list_sum L _).trans b2
    have hfin : ((L.length : ℝ) + 1) * X N e ≤ (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
      simp only [hX]
      rw [neg_add, Real.rpow_add hn0, Real.rpow_neg_one]
      have hL1 : ((L.length : ℝ) + 1) ≤ N := by exact_mod_cast hNL
      have h0 : 0 ≤ (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by positivity
      calc ((L.length : ℝ) + 1) * ((N : ℝ) ^ (-D') * (N : ℝ)⁻¹ * opNorm e.A ^ 2)
          = ((L.length : ℝ) + 1) * (N : ℝ)⁻¹ * ((N : ℝ) ^ (-D') * opNorm e.A ^ 2) := by ring
        _ ≤ 1 * ((N : ℝ) ^ (-D') * opNorm e.A ^ 2) := by
            gcongr
            rw [mul_inv_le_iff₀ hn0]; linarith
        _ = _ := one_mul _
    calc _ ≤ ‖(L.map fun R => if R.FStopped ε then 0 else E R - (R.fstep.map E).sum - Rm R).sum‖ +
          ‖(L'.map E).sum - ((fIter ε n L').map E).sum - ((fInner ε n L').map Rm).sum‖ :=
          norm_add_le _ _
      _ ≤ L.length * X N e + X N e := add_le_add b3 b1
      _ = ((L.length : ℝ) + 1) * X N e := by ring
      _ ≤ _ := hfin

/-- The tree sum of the further expansion: after `n` rounds, for `𝓡₀` of the class whose letters
`Δ_{uv}` have labels `u, v ∈ {0, 1}`, the expectation of `𝓡₀` is the sum of the expectations of
the expressions reached, plus the terms `(p, q)`, `2 ≤ p + q ≤ l`, of `𝓔^{(2)}` of the expanded
expressions, up to `N^{-D'} ‖A‖²`. -/
theorem pkg_tree_sum' (D : ℕ) (hD : 2 ≤ D) (δA τ C₀ K ε : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (n : ℕ) (R₀ : PkgExpr) (hR₀ : R₀.wf = true)
    (hlab : ∀ w ∈ R₀.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2) :
    ∀ D' : ℝ, 0 < D' → ∃ l : ℕ, 2 ≤ l ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) → (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) → ∀ κ : ℕ → Idx D N,
        ‖(∫ h, R₀.evalH e κ h ∂μ) - ((fIter ε n [R₀]).map fun R => ∫ h, R.evalH e κ h ∂μ).sum -
            ((fInner ε n [R₀]).map fun R =>
              ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
                (if 2 ≤ p + q then R.rem2PQ e μ κ p q else 0)).sum‖ ≤
          (N : ℝ) ^ (-D') * opNorm e.A ^ 2 := by
  intro D' hD'
  obtain ⟨l₀, hl⟩ := PG_tree D hD δA τ C₀ K ε hδA hτ hC₀ C n [R₀]
    (fun R hR => by
      rw [List.mem_singleton] at hR
      subst hR
      exact ⟨hR₀, hlab⟩) D' hD'
  obtain ⟨N₀, hN₀⟩ := hl (max l₀ 2) (le_max_left _ _)
  refine ⟨max l₀ 2, le_max_right _ _, N₀, fun N hN μ hμ e hA hA2 hc hz hδ κ => ?_⟩
  simpa using hN₀ N hN μ hμ e hA hA2 hc hz hδ κ

end RBMTransitionEdge

end
