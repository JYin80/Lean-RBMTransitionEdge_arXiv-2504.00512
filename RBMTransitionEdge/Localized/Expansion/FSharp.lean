module

public import RBMTransitionEdge.Localized.Expansion.FEntry
public import RBMTransitionEdge.Localized.Expansion.FOpts
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.Localized.Expansion.FOpts
import all RBMTransitionEdge.Localized.Expansion.FEntry
import all RBMTransitionEdge.Localized.Expansion.PkgSharp
import all RBMTransitionEdge.Localized.Expansion.Bound

@[expose] public section

/-!
# The bound of the further class

At the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law], for a list of factors (entries of packages, loops, light
weights) and a valid assignment of the four-label sum: outside an event of probability
`≤ N^{-D'}`, the sum over the labels and the block indices of `|Π factors|` is at most `N^{τ'}`
times the bound of the assignment; and the same sum of `|E Π factors|` is at most `N^τ` times
that bound plus `N^{-D'} ‖A‖²_HS`, as used in (5.68) [bound_factors]–(5.78)
[concrete_bound_type_2_2_1] and Example 5.7 [example_estimate_reminder_reminder_terms] in the
proof of Lemma 5.5 [claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private FO_fchosen FO_fchosen_single FO_fchosen_nil FO_fboundM FO_step FO_lab FO_prodL_cons
  FO_prodL_nil FO_evalR_nonneg FO_ext FO_rest FO_spl FO_fopts2 FO_isRes
  from RBMTransitionEdge.Localized.Expansion.FOpts
open private FE_parts_len FE_parts_sum FE_slot from RBMTransitionEdge.Localized.Expansion.FEntry
open private PS_bad_list PS_bad_fin PS_op_le_hs from RBMTransitionEdge.Localized.Expansion.PkgSharp
open private Bd_opNorm_nonneg Bd_opNorm_one Bd_opNorm_conjTranspose Bd_opNorm_E Bd_opNorm_sub
  Bd_ntr_le Bd_opNorm_res Bd_lamc_herm Bd_G_norm from RBMTransitionEdge.Localized.Expansion.Bound

/-! ### The order of summation of an assignment -/

/-- The position of each label in the order of summation of the ranks `rk`, ties broken by the
label. -/
private def FS_perm (rk : List ℕ) : Equiv.Perm (Fin 4) :=
  (Tuple.sort fun l : Fin 4 => rk.getD l 0).symm

/-- A label of lower rank is summed earlier. -/
private lemma FS_perm_lt (rk : List ℕ) {x y : Fin 4} (h : rk.getD x 0 < rk.getD y 0) :
    FS_perm rk x < FS_perm rk y := by
  by_contra hc
  have hm := Tuple.monotone_sort (fun l : Fin 4 => rk.getD l 0) (not_lt.1 hc)
  simp only [FS_perm, Function.comp_apply, Equiv.apply_symm_apply] at hm
  omega

/-- The position of a label `l < 4` in the order of summation. -/
private def FS_lab (rk : List ℕ) (l : ℕ) : Fin 4 := if hl : l < 4 then FS_perm rk ⟨l, hl⟩ else 0

private lemma FS_lab_eq (rk : List ℕ) {l : ℕ} (hl : l < 4) : FS_lab rk l = FS_perm rk ⟨l, hl⟩ :=
  dif_pos hl

private lemma FS_lab_inj (rk : List ℕ) {x y : ℕ} (hx : x < 4) (hy : y < 4) :
    FS_lab rk x = FS_lab rk y ↔ x = y := by
  rw [FS_lab_eq rk hx, FS_lab_eq rk hy, (FS_perm rk).injective.eq_iff]
  simp

/-! ### The factors of the label sum -/

/-- The modulus of an entry `(w)_{uv}`, set to `0` off the block of the sum when its labels lie in
one block. -/
private def FS_hat {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (x y : ℕ) (w : List FLet) (u v : Idx D N) : ℝ :=
  if fsameBlk x y = true ∧ u.1 ≠ v.1 then 0 else ‖((w.map (FLet.mat e ι h)).prod) u v‖

/-- The option of a factor paired with an index: the option of that index for an entry. -/
private def FS_opt (p : FFac × ℕ) : Option FOpt := p.1.entData.bind fun d => (FEnt.opts d)[p.2]?

/-- The option indices of a factor paired with an index: the index for an entry, none else. -/
private def FS_os (p : FFac × ℕ) : List ℕ := if p.1.entData.isSome then [p.2] else []

/-- The factors of the label sum of one factor with its option, in the order of summation `rk`:
an entry with distinct labels in its mixed norm, a diagonal entry in sup, in `ℓ²`, or as two
square roots in `ℓ²`, a loop or a light weight as a constant. -/
private def FS_one (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) : FFac → Option FOpt → List (FCSFac (Idx D N) 4)
  | .ent x y w, some o =>
    if x = y then
      (if o.cx = 0 then [⟨FS_lab rk x, FS_lab rk x, false, false, FS_hat e ι h x y w⟩]
       else if o.cx = 1 then [⟨FS_lab rk x, FS_lab rk x, true, false, FS_hat e ι h x y w⟩]
       else [⟨FS_lab rk x, FS_lab rk x, true, false, fun u v => Real.sqrt (FS_hat e ι h x y w u v)⟩,
         ⟨FS_lab rk x, FS_lab rk x, true, false, fun u v => Real.sqrt (FS_hat e ι h x y w u v)⟩])
    else [⟨FS_lab rk x, FS_lab rk y, o.cx == 1, o.cy == 1, FS_hat e ι h x y w⟩]
  | .ent _ _ _, none => []
  | .loop w, _ => [⟨0, 0, false, false, fun u _ => ‖(FFac.loop w).val e ι (fun _ => u) h‖⟩]
  | .wt a x, _ => [⟨0, 0, false, false, fun u _ => ‖(FFac.wt a x).val e ι (fun _ => u) h‖⟩]

/-- The norm of one factor with its option. -/
private def FS_n (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : FFac × ℕ) : ℝ :=
  ((FS_one rk e ι h p.1 (FS_opt p)).map FCSFac.norm).prod

/-- The size of one factor with its option: the sum of the monomials of the option of an entry,
the size `fixV` of a loop or a light weight. -/
private def FS_V (ev : FMono → ℝ) (p : FFac × ℕ) : ℝ :=
  match FS_opt p with
  | some o => (o.val.map ev).sum
  | none => ev p.1.fixV

/-- The labels `κ` of a sum over `Fin 4 → Idx D N` as labels indexed by `ℕ`. -/
private def FS_k {D N : ℕ} (κ : Fin 4 → Idx D N) (l : ℕ) : Idx D N :=
  if hl : l < 4 then κ ⟨l, hl⟩ else κ 0

/-- The block condition of the label sum. -/
private def FS_blk {D N : ℕ} (κ : Fin 4 → Idx D N) : Prop := (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1

/-- The conditions of a valid assignment on one factor with its option. -/
private def FS_ok (nb : ℕ) (rk : List ℕ) (p : FFac × ℕ) : Prop :=
  fvalidL nb [p.1] ⟨rk, FS_os p⟩ = true ∧ ∀ l, l < 4 → fuses [p.1] ⟨rk, FS_os p⟩ l ≤ 2


/-! ### The menu: uses and powers of `‖A‖` -/

private lemma FS_psi_do (r : ℕ) : (FMono.psi r).d = 0 ∧ (FMono.psi r).o = 0 := by
  unfold FMono.psi
  split_ifs <;> exact ⟨rfl, rfl⟩

private lemma FS_omega_do (r : ℕ) : (FMono.omega r).d = 0 ∧ (FMono.omega r).o = 0 := by
  unfold FMono.omega
  split_ifs <;> exact ⟨rfl, rfl⟩

private lemma FS_fhalf_do (n r : ℕ) (l2 : Bool) : (fhalf n r l2).d + (fhalf n r l2).o = n := by
  have h := FS_omega_do r
  unfold fhalf
  split_ifs <;> simp only [FMono.mul, h.1, h.2] <;> omega

/-- The options of an entry before `ext`: at most one use at each label; for an entry with a
resolvent, a nonempty size whose monomials carry at most `n_Λ̃` powers of `‖A‖_HS` and `‖A‖`. -/
private lemma FS_rest_do (x y : ℕ) (P : List ℕ) (det : Bool) (o : FOpt)
    (ho : o ∈ FO_rest x y P det) : o.cx ≤ 1 ∧ o.cy ≤ 1 ∧
      (1 ≤ P.sum → o.val ≠ [] ∧ ∀ q ∈ o.val, q.d + q.o ≤ P.length - 1) := by
  unfold FO_rest at ho
  simp only [List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · split_ifs at ho with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine ⟨?_, ?_, fun h => absurd hc.1.1.2 (by omega)⟩ <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
         rcases ho with rfl | rfl | rfl | rfl <;> simp)
    · simp at ho
  · split_ifs at ho with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      obtain ⟨mx, -, my, -, rfl⟩ := ho
      have hp := FS_psi_do (P.getD 1 0)
      refine ⟨by split_ifs <;> simp, by split_ifs <;> simp, fun _ => ⟨by simp, ?_⟩⟩
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp only [FMono.mul, hp.1, hp.2]
      cases mx <;> cases my <;> simp <;> omega
    · simp at ho
  · simp only [List.mem_flatMap, List.mem_range] at ho
    obtain ⟨k, hk, left, -, mx, -, my, -, ho⟩ := ho
    have hnL : (if left then k + 1 else k) ≤ P.length - 1 := by split_ifs <;> omega
    unfold FO_spl at ho
    simp only [List.mem_cons, List.mem_append] at ho
    rcases ho with rfl | ho | ho
    · refine ⟨by split_ifs <;> simp, by split_ifs <;> simp, fun _ => ⟨by simp, ?_⟩⟩
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp only [FMono.mul]
      have h1 := FS_fhalf_do (if left then k + 1 else k) (P.take (k + 1)).sum mx
      have h2 := FS_fhalf_do (P.length - 1 - (if left then k + 1 else k)) (P.drop (k + 1)).sum my
      omega
    · by_cases hc : (P.take (k + 1)).sum = 0
      · rw [if_pos hc] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        subst ho
        refine ⟨by cases mx <;> simp, by cases my <;> simp, fun _ => ⟨by simp, ?_⟩⟩
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have h1 := FS_fhalf_do (if left then k + 1 else k) 0 mx
        have hX : (if my then FMono.omega (P.drop (k + 1)).sum
            else FMono.psi (P.drop (k + 1)).sum).d = 0 ∧
            (if my then FMono.omega (P.drop (k + 1)).sum
              else FMono.psi (P.drop (k + 1)).sum).o = 0 := by
          cases my
          · exact FS_psi_do _
          · exact FS_omega_do _
        simp only [FMono.mul]
        omega
      · rw [if_neg hc] at ho
        simp at ho
    · by_cases hc : (P.drop (k + 1)).sum = 0
      · rw [if_pos hc] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        subst ho
        refine ⟨by cases mx <;> simp, by cases my <;> simp, fun _ => ⟨by simp, ?_⟩⟩
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have h1 := FS_fhalf_do (P.length - 1 - (if left then k + 1 else k)) 0 my
        have hX : (if mx then FMono.omega (P.take (k + 1)).sum
            else FMono.psi (P.take (k + 1)).sum).d = 0 ∧
            (if mx then FMono.omega (P.take (k + 1)).sum
              else FMono.psi (P.take (k + 1)).sum).o = 0 := by
          cases mx
          · exact FS_psi_do _
          · exact FS_omega_do _
        simp only [FMono.mul]
        omega
      · rw [if_neg hc] at ho
        simp at ho

/-- The options of `fopts2`: at most one use at each label; for an entry with a resolvent, a
nonempty size whose monomials carry at most `n_Λ̃` powers of `‖A‖_HS` and `‖A‖`. -/
private lemma FS_fopts2_do (x y : ℕ) (P : List ℕ) (ext : FMono) (det : Bool)
    (he : ext.d = 0 ∧ ext.o = 0) (o : FOpt) (ho : o ∈ fopts2 x y P ext det) : o.cx ≤ 1 ∧
      o.cy ≤ 1 ∧ (1 ≤ P.sum → o.val ≠ [] ∧ ∀ q ∈ o.val, q.d + q.o ≤ P.length - 1) := by
  rw [FO_fopts2] at ho
  obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ho
  have key : o₀.cx ≤ 1 ∧ o₀.cy ≤ 1 ∧
      (1 ≤ P.sum → o₀.val ≠ [] ∧ ∀ q ∈ o₀.val, q.d + q.o ≤ P.length - 1) := by
    rcases List.mem_append.1 ho₀ with hb | hr
    · have hp := FS_psi_do P.sum
      have hw := FS_omega_do P.sum
      have hf := FS_fhalf_do (P.length - 1) P.sum true
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;>
        refine ⟨by simp, by simp, fun _ => ⟨by simp, fun q hq => ?_⟩⟩ <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq <;> subst hq <;>
        (try simp only [FMono.mul, hp.1, hp.2, hw.1, hw.2]) <;> omega
    · exact FS_rest_do x y P det o₀ hr
  refine ⟨key.1, key.2.1, fun h => ⟨?_, fun q hq => ?_⟩⟩
  · simpa [FO_ext] using (key.2.2 h).1
  · simp only [FO_ext, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have := (key.2.2 h).2 q₀ hq₀
    simp only [FMono.mul, he.1, he.2]
    omega

/-- The options of an entry: at most one use at each of two distinct labels; for an entry with
a resolvent, a nonempty size whose monomials carry at most `n_Λ̃` powers of `‖A‖_HS` and
`‖A‖`. -/
private lemma FS_menu (x y : ℕ) (P : List ℕ) (ext : FMono) (det : Bool)
    (he : ext.d = 0 ∧ ext.o = 0) (o : FOpt) (ho : o ∈ fopts x y P ext det) :
    (x ≠ y → o.cx ≤ 1 ∧ o.cy ≤ 1) ∧
      (1 ≤ P.sum → o.val ≠ [] ∧ ∀ q ∈ o.val, q.d + q.o ≤ P.length - 1) := by
  unfold fopts at ho
  split_ifs at ho with hxy
  · subst hxy
    refine ⟨fun h => absurd rfl h, fun hr => ?_⟩
    rcases List.mem_append.1 ho with hb | hf
    · have hp := FS_psi_do P.sum
      have hh := FS_fhalf_do (P.length - 1) P.sum true
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> refine ⟨by simp, fun q hq => ?_⟩ <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq <;> subst hq <;>
        simp only [FMono.mul, hp.1, hp.2, he.1, he.2] <;> omega
    · obtain ⟨o', ho', hsome⟩ := List.mem_filterMap.1 hf
      split_ifs at hsome
      cases hsome
      exact (FS_fopts2_do x x P ext det he o' (List.mem_of_mem_drop ho')).2.2 hr
  · have := FS_fopts2_do x y P ext det he o ho
    exact ⟨fun _ => ⟨this.1, this.2.1⟩, this.2.2⟩

/-- The conditions of a valid assignment on an entry: labels below `4`, its option in the menu,
the order of the option compatible with the ranks, at most two uses of its row label. -/
private lemma FS_ok_ent {nb : ℕ} {rk : List ℕ} {x y i : ℕ} {w : List FLet}
    (hp : FS_ok nb rk (.ent x y w, i)) : x < 4 ∧ y < 4 ∧ ∃ o, FS_opt (.ent x y w, i) = some o ∧
      (∀ d, (FFac.ent x y w).entData = some d → o ∈ FEnt.opts d) ∧
      (o.ord = 1 → rk.getD x 0 < rk.getD y 0) ∧ (o.ord = -1 → rk.getD y 0 < rk.getD x 0) ∧
      o.cx ≤ 2 := by
  obtain ⟨h1, h2⟩ := hp
  have hos : FS_os (.ent x y w, i) = [i] := rfl
  rw [hos] at h1 h2
  unfold fvalidL at h1
  rw [FO_fchosen_single _ _ rfl] at h1
  rcases ho : (FEnt.opts ((FFac.ent x y w).entData.get rfl))[i]? with _ | o
  · simp [FFac.entData] at ho
    simp [ho] at h1
  · simp only [FFac.entData, Option.get_some] at ho
    simp only [ho, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
      Bool.and_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h1
    obtain ⟨⟨⟨-, -⟩, ⟨hx, hy⟩, -⟩, ho1, ho2⟩ := h1
    have hu := fuses_ent x y w rk i o ho x
    refine ⟨hx, hy, o, ?_, fun d hd => ?_, fun h => ?_, fun h => ?_, ?_⟩
    · simp only [FS_opt, FFac.entData, Option.bind_some]
      exact ho
    · simp only [FFac.entData, Option.some.injEq] at hd
      subst hd
      exact List.mem_of_getElem? ho
    · rcases ho1 with h' | h'
      · exact absurd h h'
      · simpa using h'
    · rcases ho2 with h' | h'
      · exact absurd h h'
      · simpa using h'
    · have := h2 x hx
      rw [hu] at this
      simp at this
      omega

/-! ### One factor in the label sum -/

/-- Two labels of one block of the sum carry block indices that agree under the block condition. -/
private lemma FS_blk_same {D N : ℕ} {κ : Fin 4 → Idx D N} (hb : FS_blk κ) {x y : ℕ} (hx : x < 4)
    (hy : y < 4) (hs : fsameBlk x y = true) : (FS_k κ x).1 = (FS_k κ y).1 := by
  obtain ⟨h01, h23⟩ := hb
  unfold FS_k
  interval_cases x <;> interval_cases y <;> simp_all [fsameBlk]

private lemma FS_k_perm {D N : ℕ} (rk : List ℕ) (lam : Fin 4 → Idx D N) {x : ℕ} (hx : x < 4) :
    FS_k (lam ∘ FS_perm rk) x = lam (FS_lab rk x) := by
  simp [FS_k, hx, FS_lab_eq rk hx]

private lemma FS_hat_nonneg {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (x y : ℕ) (w : List FLet) (u v : Idx D N) :
    0 ≤ FS_hat e ι h x y w u v := by
  unfold FS_hat
  split_ifs
  · exact le_rfl
  · exact norm_nonneg _

/-- The functions of the factors are nonnegative. -/
private lemma FS_one_nonneg (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ}
    (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ) (f : FFac) (o : Option FOpt) :
    ∀ g ∈ FS_one rk e ι h f o, ∀ u v, 0 ≤ g.f u v := by
  intro g hg u v
  rcases f with ⟨x, y, w⟩ | w | ⟨a, x⟩
  · rcases o with _ | o
    · simp [FS_one] at hg
    · simp only [FS_one] at hg
      split_ifs at hg <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hg <;>
        rcases hg with rfl | rfl <;>
        first | exact FS_hat_nonneg e ι h x y w u v | exact Real.sqrt_nonneg _
  · simp only [FS_one, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact norm_nonneg _
  · simp only [FS_one, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact norm_nonneg _

/-- The modulus of one factor at the labels `λ ∘ σ` is the product of its functions at `λ`,
under the block condition. -/
private lemma FS_val_le {nb : ℕ} {rk : List ℕ} {D N : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : FFac × ℕ) (hp : FS_ok nb rk p) (lam : Fin 4 → Idx D N)
    (hb : FS_blk (lam ∘ FS_perm rk)) :
    ‖p.1.val e ι (FS_k (lam ∘ FS_perm rk)) h‖ ≤
      ((FS_one rk e ι h p.1 (FS_opt p)).map fun g => g.f (lam g.a) (lam g.b)).prod := by
  obtain ⟨f, i⟩ := p
  rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩
  · obtain ⟨hx, hy, o, hop, -, -, -, -⟩ := FS_ok_ent hp
    rw [hop]
    have hm : FS_hat e ι h x y w (lam (FS_lab rk x)) (lam (FS_lab rk y)) =
        ‖((w.map (FLet.mat e ι h)).prod) (lam (FS_lab rk x)) (lam (FS_lab rk y))‖ := by
      unfold FS_hat
      rw [if_neg]
      rintro ⟨hs, hne⟩
      apply hne
      have := FS_blk_same hb hx hy hs
      rwa [FS_k_perm rk lam hx, FS_k_perm rk lam hy] at this
    simp only [FFac.val, FS_k_perm rk lam hx, FS_k_perm rk lam hy]
    simp only [FS_one]
    split_ifs with hxy h0 h1
    · subst hxy
      simp [hm]
    · subst hxy
      simp [hm]
    · subst hxy
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Real.sqrt_mul (FS_hat_nonneg e ι h x x w _ _), Real.sqrt_mul_self
        (FS_hat_nonneg e ι h x x w _ _), hm]
    · simp [hm]
  · simp [FS_one, FFac.val]
  · simp [FS_one, FFac.val]

/-- The uses of the labels by the factors of one factor are its uses `fuses`. -/
private lemma FS_use {nb : ℕ} {rk : List ℕ} {D N : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : FFac × ℕ) (hp : FS_ok nb rk p) (l : Fin 4) :
    ((FS_one rk e ι h p.1 (FS_opt p)).map fun g => g.use (FS_perm rk l)).sum =
      fuses [p.1] ⟨rk, FS_os p⟩ l := by
  obtain ⟨f, i⟩ := p
  rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩
  · obtain ⟨hx, hy, o, hop, hmem, -, -, hcx⟩ := FS_ok_ent hp
    have ho : (fopts x y (FLet.parts w)
        ⟨0, 2 * ((w.countP fun z => match z with | .det _ pr => pr | _ => false : ℕ) : ℤ),
          0, 0, 0⟩ (w.all fun z => match z with | .det _ pr => !pr | _ => true))[i]? = some o :=
      hop
    have hmenu := FS_menu _ _ _ _ _ ⟨rfl, rfl⟩ o (hmem _ rfl)
    change _ = fuses [.ent x y w] ⟨rk, [i]⟩ l
    rw [fuses_ent x y w rk i o ho l, hop]
    have hxl : FS_lab rk x = FS_perm rk l ↔ x = l.val := by
      rw [FS_lab_eq rk hx, (FS_perm rk).injective.eq_iff, Fin.ext_iff]
    have hyl : FS_lab rk y = FS_perm rk l ↔ y = l.val := by
      rw [FS_lab_eq rk hy, (FS_perm rk).injective.eq_iff, Fin.ext_iff]
    by_cases hxy : x = y
    · subst hxy
      have hc3 : o.cx = 0 ∨ o.cx = 1 ∨ o.cx = 2 := by omega
      simp only [← hxl, ne_eq, and_not_self, if_false, add_zero]
      rcases hc3 with h0 | h0 | h0 <;>
        by_cases h' : FS_lab rk x = FS_perm rk l <;> simp [FS_one, FCSFac.use, h', h0]
    · obtain ⟨hcx1, hcy1⟩ := hmenu.1 hxy
      have hab : FS_lab rk x ≠ FS_lab rk y := fun hh => hxy ((FS_lab_inj rk hx hy).1 hh)
      simp only [FS_one, if_neg hxy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, FCSFac.use]
      rw [if_neg (fun hh => hab (hh.1.trans hh.2.symm))]
      by_cases h' : x = l.val <;> by_cases h'' : y = l.val <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcx1 with hc | hc <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcy1 with hd | hd <;>
        simp_all
  · change _ = fuses [.loop w] ⟨rk, []⟩ l
    rw [fuses_fix _ rfl]
    simp [FS_one, FCSFac.use]
  · change _ = fuses [.wt a u] ⟨rk, []⟩ l
    rw [fuses_fix _ rfl]
    simp [FS_one, FCSFac.use]

/-! ### The norms of one factor -/

private lemma FS_norm_nonneg {ι : Type*} [Fintype ι] {L : ℕ} (g : FCSFac ι L)
    (hg : ∀ u v, 0 ≤ g.f u v) : 0 ≤ g.norm := by
  unfold FCSFac.norm
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact Real.iSup_nonneg fun x => hg x x
  · unfold fcsNorm
    rcases g.ma <;> rcases g.mb
    · exact Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => hg x y
    · exact Real.sqrt_nonneg _
    · exact Real.iSup_nonneg fun y => Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
  · unfold fcsNorm
    rcases g.ma <;> rcases g.mb
    · exact Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => hg y x
    · exact Real.iSup_nonneg fun y => Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _

private lemma FS_n_nonneg (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ}
    (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ) (p : FFac × ℕ) : 0 ≤ FS_n rk e ι h p :=
  List.prod_nonneg fun t ht => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
    exact FS_norm_nonneg g (FS_one_nonneg rk e ι h _ _ g hg)

/-- The norm of an entry is the mixed norm `foptNorm` of its option, in the order of summation. -/
private lemma FS_n_ent (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) {x y i : ℕ} {w : List FLet} {o : FOpt}
    (ho : FS_opt (.ent x y w, i) = some o) (hx : x < 4) (hy : y < 4) :
    FS_n rk e ι h (.ent x y w, i) = foptNorm (decide (x = y)) o
      (decide (FS_lab rk x < FS_lab rk y)) (FS_hat e ι h x y w) := by
  unfold FS_n
  rw [ho]
  by_cases hxy : x = y
  · subst hxy
    have hs : ∑ u, FS_hat e ι h x x w u u = Real.sqrt (∑ u, FS_hat e ι h x x w u u) *
        Real.sqrt (∑ u, FS_hat e ι h x x w u u) :=
      (Real.mul_self_sqrt (Finset.sum_nonneg fun u _ => FS_hat_nonneg e ι h x x w u u)).symm
    have hq : ∀ u, Real.sqrt (FS_hat e ι h x x w u u) ^ 2 = FS_hat e ι h x x w u u :=
      fun u => Real.sq_sqrt (FS_hat_nonneg e ι h x x w u u)
    simp only [FS_one, if_true, decide_true, foptNorm]
    rcases ho' : o.cx with _ | _ | c
    · simp [FCSFac.norm]
    · simp [FCSFac.norm]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_eq_right,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        FCSFac.norm, if_true, hq]
      exact hs.symm
  · have hab : FS_lab rk x ≠ FS_lab rk y := fun hh => hxy ((FS_lab_inj rk hx hy).1 hh)
    simp only [FS_one, if_neg hxy, foptNorm, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, FCSFac.norm, if_neg hab]
    by_cases hlt : FS_lab rk x < FS_lab rk y
    · simp [hlt, hxy]
    · simp [hlt, hxy]

/-- The norm of a loop or a light weight is at most its modulus. -/
private lemma FS_n_fix (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : FFac × ℕ) (hp : p.1.entData = none) (κ : ℕ → Idx D N) :
    FS_n rk e ι h p ≤ ‖p.1.val e ι κ h‖ := by
  obtain ⟨f, i⟩ := p
  rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩
  · simp [FFac.entData] at hp
  · simp only [FS_n, FS_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      FCSFac.norm, if_true, Bool.false_eq_true, if_false]
    exact Real.iSup_le (fun _ => le_rfl) (norm_nonneg _)
  · simp only [FS_n, FS_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      FCSFac.norm, if_true, Bool.false_eq_true, if_false]
    exact Real.iSup_le (fun _ => le_rfl) (norm_nonneg _)

/-! ### Lists of factors with their options -/

private lemma FS_os_len (p : FFac × ℕ) :
    (FS_os p).length = ([p.1].filterMap FFac.entData).length := by
  obtain ⟨f, i⟩ := p
  rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩ <;> rfl

/-- A factor list with one option index per entry is a list of factors paired with indices. -/
private lemma FS_pairs : ∀ (F : List FFac) (os : List ℕ),
    os.length = (F.filterMap FFac.entData).length →
    ∃ P : List (FFac × ℕ), P.map Prod.fst = F ∧ P.flatMap FS_os = os
  | [], os, h => ⟨[], rfl, by simp at h; simp [h]⟩
  | f :: F, os, h => by
    rcases hf : f.entData with _ | d
    · rw [List.filterMap_cons, hf] at h
      obtain ⟨P, h1, h2⟩ := FS_pairs F os h
      refine ⟨(f, 0) :: P, by simp [h1], ?_⟩
      rw [List.flatMap_cons, h2]
      simp [FS_os, hf]
    · rw [List.filterMap_cons, hf] at h
      obtain ⟨i, os', rfl⟩ : ∃ i os', os = i :: os' := by
        rcases os with _ | ⟨i, os'⟩
        · simp at h
        · exact ⟨i, os', rfl⟩
      obtain ⟨P, h1, h2⟩ := FS_pairs F os' (by simpa using h)
      refine ⟨(f, i) :: P, by simp [h1], ?_⟩
      rw [List.flatMap_cons, h2]
      simp [FS_os, hf]

private lemma FS_cons_fst (p : FFac × ℕ) (P : List (FFac × ℕ)) :
    (p :: P).map Prod.fst = [p.1] ++ P.map Prod.fst := rfl

private lemma FS_cons_os (p : FFac × ℕ) (P : List (FFac × ℕ)) :
    (p :: P).flatMap FS_os = FS_os p ++ P.flatMap FS_os := List.flatMap_cons

/-- The uses of a list are the sums of the uses of its factors. -/
private lemma FS_fuses_list (rk : List ℕ) (l : ℕ) : ∀ P : List (FFac × ℕ),
    fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l =
      (P.map fun p => fuses [p.1] ⟨rk, FS_os p⟩ l).sum
  | [] => rfl
  | p :: P => by
    rw [FS_cons_fst, FS_cons_os, fuses_append _ _ _ _ _ (FS_os_len p), FS_fuses_list rk l P]
    rfl

/-- The entries of a list with their options are those of its factors. -/
private lemma FS_fchosen_list (rk : List ℕ) : ∀ P : List (FFac × ℕ),
    fchosen (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ =
      P.flatMap fun p => fchosen [p.1] ⟨rk, FS_os p⟩
  | [] => rfl
  | p :: P => by
    rw [FS_cons_fst, FS_cons_os, fchosen_append _ _ _ _ _ (FS_os_len p), FS_fchosen_list rk P,
      List.flatMap_cons]

/-- A valid assignment is valid on each factor, with at most two uses per label. -/
private lemma FS_valid {nb : ℕ} {rk : List ℕ} (P : List (FFac × ℕ))
    (hv : fvalid nb (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ = true) :
    (∀ p ∈ P, FS_ok nb rk p) ∧ ∀ l, l < 4 → fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l ≤ 2 := by
  rw [fvalid_eq] at hv
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hv
  obtain ⟨hL, hcap⟩ := hv
  refine ⟨?_, hcap⟩
  have hL' : ∀ p ∈ P, fvalidL nb [p.1] ⟨rk, FS_os p⟩ = true := by
    clear hcap
    induction P with
    | nil => simp
    | cons p P ih =>
      rw [FS_cons_fst, FS_cons_os, fvalidL_append _ _ _ _ _ _ (FS_os_len p)] at hL
      simp only [Bool.and_eq_true] at hL
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hL.1
      · exact ih hL.2 q hq
  intro p hp
  refine ⟨hL' p hp, fun l hl => le_trans ?_ (hcap l hl)⟩
  rw [FS_fuses_list]
  exact List.le_sum_of_mem (List.mem_map_of_mem hp)

private lemma FS_prod_flatMap {α β : Type*} (f : β → ℝ) (φ : α → List β) : ∀ P : List α,
    ((P.flatMap φ).map f).prod = (P.map fun p => ((φ p).map f).prod).prod
  | [] => rfl
  | p :: P => by
    rw [List.flatMap_cons, List.map_append, List.prod_append, FS_prod_flatMap f φ P]
    rfl

private lemma FS_sum_flatMap {α β : Type*} (f : β → ℕ) (φ : α → List β) : ∀ P : List α,
    ((P.flatMap φ).map f).sum = (P.map fun p => ((φ p).map f).sum).sum
  | [] => rfl
  | p :: P => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, FS_sum_flatMap f φ P]
    rfl

/-- The factors of the label sum of a list. -/
private abbrev FS_G (rk : List ℕ) {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (P : List (FFac × ℕ)) : List (FCSFac (Idx D N) 4) :=
  P.flatMap fun p => FS_one rk e ι h p.1 (FS_opt p)

private lemma FS_val_list {nb : ℕ} {rk : List ℕ} {D N : ℕ} (e : LoopEnv D N)
    (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ) (lam : Fin 4 → Idx D N)
    (hb : FS_blk (lam ∘ FS_perm rk)) : ∀ P : List (FFac × ℕ), (∀ p ∈ P, FS_ok nb rk p) →
    ‖((P.map Prod.fst).map (FFac.val e ι (FS_k (lam ∘ FS_perm rk)) h)).prod‖ ≤
      ((FS_G rk e ι h P).map fun g => g.f (lam g.a) (lam g.b)).prod
  | [], _ => by simp
  | p :: P, hP => by
    rw [FS_G, List.flatMap_cons, List.map_append, List.prod_append]
    simp only [List.map_cons, List.prod_cons, norm_mul]
    have h1 := FS_val_le e ι h p (hP p List.mem_cons_self) lam hb
    have h2 := FS_val_list e ι h lam hb P fun q hq => hP q (List.mem_cons_of_mem _ hq)
    refine mul_le_mul h1 h2 (norm_nonneg _) (List.prod_nonneg fun t ht => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
    exact FS_one_nonneg rk e ι h _ _ g hg _ _

/-- The four-label step of (5.68) [bound_factors]–(5.71) [Cauchy_example_2]: the label sum of the
modulus of a product of factors is at most `|Idx|^{(2 - c_l)/2}` per label times the product of
the norms of the factors in the order of summation. -/
private lemma FS_det {nb : ℕ} {rk : List ℕ} {D N : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (P : List (FFac × ℕ)) (hP : ∀ p ∈ P, FS_ok nb rk p)
    (hcap : ∀ l, l < 4 → fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l ≤ 2) :
    ∑ κ : Fin 4 → Idx D N, (if FS_blk κ then
      ‖((P.map Prod.fst).map (FFac.val e ι (FS_k κ) h)).prod‖ else 0) ≤
    (∏ l : Fin 4, ((Fintype.card (Idx D N) : ℝ)) ^
      ((2 - (fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l : ℝ)) / 2)) *
      (P.map (FS_n rk e ι h)).prod := by
  have huse : ∀ l : Fin 4, ((FS_G rk e ι h P).map fun g => g.use (FS_perm rk l)).sum =
      fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l := by
    intro l
    rw [FS_G, FS_sum_flatMap (fun g : FCSFac (Idx D N) 4 => g.use (FS_perm rk l)), FS_fuses_list]
    congr 1
    exact List.map_congr_left fun p hp => FS_use e ι h p (hP p hp) l
  have hG : ∀ g ∈ FS_G rk e ι h P, ∀ x y, 0 ≤ g.f x y := fun g hg => by
    obtain ⟨p, -, hp⟩ := List.mem_flatMap.1 hg
    exact FS_one_nonneg rk e ι h _ _ g hp
  have hcapG : ∀ l, ((FS_G rk e ι h P).map fun g => g.use l).sum ≤ 2 := by
    intro l
    have := huse ((FS_perm rk).symm l)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact hcap _ ((FS_perm rk).symm l).isLt
  have hfcs := fcs_contract 4 (FS_G rk e ι h P) hG hcapG
  have hre : ∀ Φ : (Fin 4 → Idx D N) → ℝ, ∑ κ, Φ κ = ∑ lam, Φ (lam ∘ FS_perm rk) := fun Φ =>
    (Fintype.sum_equiv (Equiv.arrowCongr (FS_perm rk).symm (Equiv.refl _)) _ _
      fun lam => rfl).symm
  rw [hre]
  refine le_trans (Finset.sum_le_sum fun lam _ => ?_) (hfcs.trans (le_of_eq ?_))
  · split_ifs with hb
    · exact FS_val_list e ι h lam hb P hP
    · exact List.prod_nonneg fun t ht => by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
        exact hG g hg _ _
  · have hn : ((FS_G rk e ι h P).map FCSFac.norm).prod = (P.map (FS_n rk e ι h)).prod :=
      FS_prod_flatMap _ _ P
    rw [hn]
    refine congrArg (· * _) ?_
    refine (Equiv.prod_comp (FS_perm rk) (fun l => ((Fintype.card (Idx D N) : ℝ)) ^
      ((2 - (((FS_G rk e ι h P).map fun g => g.use l).sum : ℝ)) / 2))).symm.trans ?_
    exact Finset.prod_congr rfl fun l _ => by rw [← huse l, Nat.cast_list_sum, List.map_map]; rfl

/-- The label factor `|Idx|^{(2 - c_l)/2}` per label is at most `D⁴` times the label monomial of
`fboundM`. -/
private lemma FS_lab_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (u : ℕ → ℕ) (M η hs op : ℝ) :
    ∏ l : Fin 4, ((Fintype.card (Idx D N) : ℝ)) ^ ((2 - (u l : ℝ)) / 2) ≤
      (D : ℝ) ^ 4 * (⟨((List.range 4).map fun l => 2 - (u l : ℤ)).sum, 0, 0, 0, 0⟩ :
        FMono).evalR N M η hs op := by
  have hc : (Fintype.card (Idx D N) : ℝ) = D * N := by simp [Idx]
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ t : ℕ, ((D : ℝ) * N) ^ ((2 - (t : ℝ)) / 2) ≤ D * (N : ℝ) ^ ((2 - (t : ℝ)) / 2) :=
    fun t => by
      rw [Real.mul_rpow (by positivity) hN0.le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (D : ℝ) ^ ((2 - (t : ℝ)) / 2) ≤ (D : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hD1
              (by have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t); linarith)
        _ = D := Real.rpow_one _
  have hev : (⟨((List.range 4).map fun l => 2 - (u l : ℤ)).sum, 0, 0, 0, 0⟩ :
      FMono).evalR N M η hs op = (N : ℝ) ^ ((2 - (u 0 : ℝ)) / 2) * (N : ℝ) ^ ((2 - (u 1 : ℝ)) / 2) *
        (N : ℝ) ^ ((2 - (u 2 : ℝ)) / 2) * (N : ℝ) ^ ((2 - (u 3 : ℝ)) / 2) := by
    simp only [FMono.evalR, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.map_append, List.sum_append, List.sum_cons, List.sum_nil]
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    push_cast
    simp only [zero_div, Real.rpow_zero, neg_zero, pow_zero, mul_one]
    congr 1
    ring
  rw [hev, Fin.prod_univ_four, hc]
  have h0 := key (u 0)
  have h1 := key (u 1)
  have h2 := key (u 2)
  have h3 := key (u 3)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at *
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [e3]
  calc _ ≤ (D * (N : ℝ) ^ ((2 - (u 0 : ℝ)) / 2)) * (D * (N : ℝ) ^ ((2 - (u 1 : ℝ)) / 2)) *
        (D * (N : ℝ) ^ ((2 - (u 2 : ℝ)) / 2)) * (D * (N : ℝ) ^ ((2 - (u 3 : ℝ)) / 2)) := by
        gcongr
    _ = _ := by ring

/-! ### The bound of an assignment as a product -/

section Bound

variable (ev : FMono → ℝ) (hmul : ∀ p q, ev (p.mul q) = ev p * ev q)
  (hone : ev ⟨0, 0, 0, 0, 0⟩ = 1)

/-- The size of the chosen option of an entry (`1` without one). -/
private def FS_Vc (c : FEnt × Option FOpt) : ℝ :=
  match c.2 with
  | some o => (o.val.map ev).sum
  | none => 1

include hmul in
private lemma FS_fold_sum : ∀ (C : List (FEnt × Option FOpt)) (L : List FMono),
    ((C.foldl FO_step L).map ev).sum = (L.map ev).sum * (C.map (FS_Vc ev)).prod
  | [], L => by simp
  | c :: C, L => by
    rw [List.foldl_cons, FS_fold_sum C, List.map_cons, List.prod_cons, ← mul_assoc]
    congr 1
    rcases hc : c.2 with _ | o
    · simp [FO_step, FS_Vc, hc]
    · simp only [FO_step, hc, FS_Vc, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
      rw [← List.sum_map_mul_right]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp_apply, List.map_map]
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun q _ => hmul p q

include hmul hone in
private lemma FS_ev_prodL : ∀ L : List FMono, ev (FMono.prodL L) = (L.map ev).prod
  | [] => by rw [FO_prodL_nil, hone]; rfl
  | x :: L => by rw [FO_prodL_cons, hmul, FS_ev_prodL L]; rfl

include hone in
/-- The size of one factor with its option, by `fixV` and `fchosen`. -/
private lemma FS_V_eq (rk : List ℕ) (p : FFac × ℕ) :
    ev p.1.fixV * ((fchosen [p.1] ⟨rk, FS_os p⟩).map (FS_Vc ev)).prod = FS_V ev p := by
  obtain ⟨f, i⟩ := p
  rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩
  · change ev ⟨0, 0, 0, 0, 0⟩ * ((fchosen [.ent x y w] ⟨rk, [i]⟩).map (FS_Vc ev)).prod = _
    rw [FO_fchosen_single _ _ rfl, hone, one_mul]
    simp only [FS_V, FS_opt, FFac.entData, Option.bind_some, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, FS_Vc]
    rcases (FEnt.opts _)[i]? with _ | o
    · simp [FFac.fixV, hone]
    · rfl
  · rw [FO_fchosen_nil _ rfl]
    simp [FS_V, FS_opt, FFac.entData]
  · rw [FO_fchosen_nil _ rfl]
    simp [FS_V, FS_opt, FFac.entData]

include hmul hone in
/-- The bound of an assignment is the label monomial times the product of the sizes of the
factors with their options. -/
private lemma FS_bound_eq (rk : List ℕ) (P : List (FFac × ℕ)) :
    ((fboundM (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩).map ev).sum =
      ev ⟨((List.range 4).map fun l =>
        2 - (fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l : ℤ)).sum, 0, 0, 0, 0⟩ *
      (P.map (FS_V ev)).prod := by
  rw [FO_fboundM, FS_fold_sum ev hmul, List.map_singleton, List.sum_singleton, hmul,
    FS_ev_prodL ev hmul hone, mul_assoc]
  congr 1
  rw [FS_fchosen_list]
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
      List.prod_append]
    rw [← ih, ← FS_V_eq ev hone rk p]
    ring

end Bound

/-! ### The good event of one factor -/

/-- The slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law] at size `N`, for a member `μ` of the class. -/
private def FS_Slots (D : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ) (N : ℕ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (e : LoopEnv D N) : Prop :=
  LLClass D N C 1 μ ∧ opNorm A ≤ (N : ℝ) ^ (-δA) ∧ 1 ≤ k ∧ 2 * k ≤ D * N + 1 ∧
  hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) ∧
  ((∃ s, e = evecEnv D N A k ε s) ∨ ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s)

/-- A monomial at the slots: `Im m ≤ N^{-1/3+ε/2} 𝔯(k)^{1/3}`, `η = N^{-2/3+ε} 𝔯(k)^{-1/3}`. -/
private def FS_ev (D N k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (m : FMono) : ℝ :=
  m.evalR N ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
    (hsNorm A) (opNorm A)

/-- A loop or a light weight of a valid assignment satisfies the hypothesis of `pkg_ffix_good`. -/
private lemma FS_fix_valid {nb : ℕ} {rk : List ℕ} (f : FFac) (hf : f.entData = none)
    (h : fvalidL nb [f] ⟨rk, []⟩ = true) : fvalid nb [f] ⟨[0, 1, 2, 3], []⟩ = true := by
  rw [fvalid_eq]
  unfold fvalidL at h ⊢
  rw [FO_fchosen_nil _ (by simp [hf])] at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true] at h ⊢
  refine ⟨⟨⟨rfl, h.1.2⟩, h.2⟩, ?_⟩
  simp [fuses_fix f hf]

/-- One factor with its option is bounded by `N^{τ'}` times its size off an event of probability
`≤ N^{-D'}`: `pkg_fopt_good` for an entry, `pkg_ffix_good` for a loop or a light weight. -/
private lemma FS_good_one (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (rk : List ℕ)
    (p : FFac × ℕ) (hp : FS_ok nb rk p) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e → ∀ ι : Fin nb → Fin D,
      ∃ s : Set (Idx D N → Idx D N → ℂ), μ s ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h ∉ s, FS_n rk e ι h p ≤ (N : ℝ) ^ τ' * FS_V (FS_ev D N k ε A) p := by
  obtain ⟨f, i⟩ := p
  rcases hf : f.entData with _ | d
  · have hos : FS_os (f, i) = [] := by simp [FS_os, hf]
    have hv := FS_fix_valid (rk := rk) f hf (hos ▸ hp.1)
    obtain ⟨N₀, hN₀⟩ := pkg_ffix_good D hD δA εA ε hδA hεA hε hε' hε'' C nb f hv τ' hτ' D' hD'
    filter_upwards [Filter.eventually_ge_atTop (max N₀ 1)] with N hN
    intro μ A k e ⟨hμ, hA, hk, hkN, hhs, he⟩ ι
    have hN1 : 0 < N := by omega
    let κ₀ : ℕ → Idx D N := fun _ => (⟨0, by omega⟩, ⟨0, hN1⟩)
    refine ⟨_, hN₀ N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he ι κ₀, fun h hh => ?_⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hh
    have hV : FS_V (FS_ev D N k ε A) (f, i) = FS_ev D N k ε A f.fixV := by
      simp [FS_V, FS_opt, hf]
    rw [hV]
    exact (FS_n_fix rk e ι h (f, i) hf κ₀).trans hh
  · rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩
    · obtain ⟨hx, hy, o, hop, hmem, hord1, hord2, -⟩ := FS_ok_ent hp
      have hord : (o.ord = 1 → decide (FS_lab rk x < FS_lab rk y) = true) ∧
          (o.ord = -1 → decide (FS_lab rk x < FS_lab rk y) = false) := by
        refine ⟨fun h1 => ?_, fun h1 => ?_⟩
        · have := FS_perm_lt rk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (hord1 h1)
          rw [FS_lab_eq rk hx, FS_lab_eq rk hy]
          exact decide_eq_true this
        · have := FS_perm_lt rk (x := ⟨y, hy⟩) (y := ⟨x, hx⟩) (hord2 h1)
          rw [FS_lab_eq rk hx, FS_lab_eq rk hy]
          exact decide_eq_false (not_lt.2 this.le)
      obtain ⟨N₀, hN₀⟩ := pkg_fopt_good D hD δA εA ε hδA hεA hε hε' hε'' C nb x y w d hf o
        (hmem d hf) _ hord τ' hτ' D' hD'
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
      intro μ A k e ⟨hμ, hA, hk, hkN, hhs, he⟩ ι
      refine ⟨_, hN₀ N hN μ hμ A hA k hk hkN hhs e he ι, fun h hh => ?_⟩
      simp only [Set.mem_ofPred_eq, not_lt] at hh
      rw [FS_n_ent rk e ι h hop hx hy]
      have hV : FS_V (FS_ev D N k ε A) (.ent x y w, i) =
          (o.val.map (FS_ev D N k ε A)).sum := by
        simp only [FS_V, hop]
      rw [hV]
      exact hh
    · simp [FFac.entData] at hf
    · simp [FFac.entData] at hf

private lemma FS_ev_nonneg (D N k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (m : FMono) :
    0 ≤ FS_ev D N k ε A m := by
  have hrk : (0 : ℝ) ≤ rk D N k := by unfold rk; positivity
  exact FO_evalR_nonneg _ _ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (Real.rpow_nonneg hrk _)) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (Real.rpow_nonneg hrk _)) (Real.sqrt_nonneg _) (Bd_opNorm_nonneg A)

private lemma FS_V_nonneg (ev : FMono → ℝ) (hev : ∀ m, 0 ≤ ev m) (p : FFac × ℕ) :
    0 ≤ FS_V ev p := by
  unfold FS_V
  split
  · exact List.sum_nonneg fun t ht => by
      obtain ⟨m, -, rfl⟩ := List.mem_map.1 ht
      exact hev m
  · exact hev _

/-- The good event of a list of factors: the union of the good events of its factors. -/
private lemma FS_good_list (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (rk : List ℕ)
    (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') : ∀ P : List (FFac × ℕ),
    (∀ p ∈ P, FS_ok nb rk p) →
    ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e → ∀ ι : Fin nb → Fin D,
      ∃ s : Set (Idx D N → Idx D N → ℂ),
        μ s ≤ ENNReal.ofReal (P.length * (N : ℝ) ^ (-D')) ∧ ∀ h ∉ s,
          (P.map (FS_n rk e ι h)).prod ≤
            ((N : ℝ) ^ τ') ^ P.length * (P.map (FS_V (FS_ev D N k ε A))).prod
  | [], _ => Filter.Eventually.of_forall fun N μ A k e _ ι => ⟨∅, by simp, fun h _ => by simp⟩
  | p :: P, hP => by
    filter_upwards [FS_good_one D hD δA εA ε hδA hεA hε hε' hε'' C nb rk p
      (hP p List.mem_cons_self) τ' hτ' D' hD',
      FS_good_list D hD δA εA ε hδA hεA hε hε' hε'' C nb rk τ' hτ' D' hD' P
        fun q hq => hP q (List.mem_cons_of_mem _ hq)] with N h1 h2
    intro μ A k e hs ι
    obtain ⟨s₁, hs₁, hg₁⟩ := h1 μ A k e hs ι
    obtain ⟨s₂, hs₂, hg₂⟩ := h2 μ A k e hs ι
    have hb : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg N) _
    refine ⟨s₁ ∪ s₂, (measure_union_le _ _).trans ?_, fun h hh => ?_⟩
    · rw [List.length_cons, Nat.cast_succ, add_mul, one_mul,
        ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hb) hb, add_comm (μ s₁)]
      exact add_le_add hs₂ hs₁
    · simp only [Set.mem_union, not_or] at hh
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      have e1 := hg₁ h hh.1
      have e2 := hg₂ h hh.2
      have hn := FS_n_nonneg rk e ι h p
      have hpn : 0 ≤ (P.map (FS_n rk e ι h)).prod := List.prod_nonneg fun t ht => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
        exact FS_n_nonneg rk e ι h q
      have hV := FS_V_nonneg _ (FS_ev_nonneg D N k ε A) p
      have hτ0 : 0 ≤ (N : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg N) _
      calc FS_n rk e ι h p * (P.map (FS_n rk e ι h)).prod ≤
            ((N : ℝ) ^ τ' * FS_V (FS_ev D N k ε A) p) *
              (((N : ℝ) ^ τ') ^ P.length * (P.map (FS_V (FS_ev D N k ε A))).prod) :=
            mul_le_mul e1 e2 hpn (mul_nonneg hτ0 hV)
        _ = _ := by ring

/-- `1 ≤ 𝔯(k)`, and the bound on `Im m` and `η` are positive at the slots. -/
private lemma FS_pos {D N k : ℕ} (ε : ℝ) (hN : 1 ≤ N) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) :
    (1 : ℝ) ≤ rk D N k ∧ 0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ∧
      0 < etaK D N k ε := by
  have hrk : (1 : ℝ) ≤ rk D N k := by
    unfold rk
    exact_mod_cast (show 1 ≤ min k (D * N + 1 - k) by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨hrk, mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (by linarith) _),
    mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (by linarith) _)⟩

/-- The monomials at the slots multiply. -/
private lemma FS_ev_mul {D N k : ℕ} (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (hN : 1 ≤ N)
    (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) (p q : FMono) :
    FS_ev D N k ε A (p.mul q) = FS_ev D N k ε A p * FS_ev D N k ε A q := by
  obtain ⟨-, hM, hη⟩ := FS_pos ε hN hk hkN
  exact fmono_evalR_mul p q N hN _ _ _ _ hM hη

private lemma FS_ev_one {D N k : ℕ} (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    FS_ev D N k ε A ⟨0, 0, 0, 0, 0⟩ = 1 := by
  simp [FS_ev, FMono.evalR]

/-! ### Deterministic bounds at a Hermitian array -/

section Crude

variable {ι : Type*} [Fintype ι]

private lemma FS_sqrt_le {κ : Type*} [Fintype κ] (g : κ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg0 : ∀ x, 0 ≤ g x) (hg : ∀ x, g x ≤ c) :
    Real.sqrt (∑ x, g x ^ 2) ≤ (Fintype.card κ : ℝ) * c := by
  have hn : (Fintype.card κ : ℝ) ≤ (Fintype.card κ : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card κ) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast h
      nlinarith
  calc Real.sqrt (∑ x, g x ^ 2) ≤ Real.sqrt (((Fintype.card κ : ℝ) * c) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc ∑ x, g x ^ 2 ≤ ∑ _x : κ, c ^ 2 :=
              Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (hg0 x) (hg x) 2
          _ = (Fintype.card κ : ℝ) * c ^ 2 := by simp
          _ ≤ ((Fintype.card κ : ℝ) * c) ^ 2 := by
              rw [mul_pow]
              exact mul_le_mul_of_nonneg_right hn (sq_nonneg c)
    _ = (Fintype.card κ : ℝ) * c := Real.sqrt_sq (by positivity)

/-- Every mixed norm of a function with values in `[0, c]` is at most `(|ι| + 1)² c`. -/
private lemma FS_fopt_le (d : Bool) (o : FOpt) (rf : Bool) (f : ι → ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf0 : ∀ u v, 0 ≤ f u v) (hf : ∀ u v, f u v ≤ c) :
    foptNorm d o rf f ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * c := by
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h1 : c ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * c :=
    le_mul_of_one_le_left hc (by nlinarith)
  have h2 : (Fintype.card ι : ℝ) * c ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * c :=
    mul_le_mul_of_nonneg_right (by nlinarith) hc
  have hsq : ∀ g : ι → ι → ℝ, (∀ u v, 0 ≤ g u v) → (∀ u v, g u v ≤ c) →
      Real.sqrt (∑ x, ∑ y, g x y ^ 2) ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * c := by
    intro g hg0 hg
    have e : ∑ x, ∑ y, g x y ^ 2 = ∑ q : ι × ι, g q.1 q.2 ^ 2 := (Fintype.sum_prod_type' _).symm
    rw [e]
    refine (FS_sqrt_le (fun q : ι × ι => g q.1 q.2) c hc (fun q => hg0 _ _)
      (fun q => hg _ _)).trans (mul_le_mul_of_nonneg_right ?_ hc)
    simp only [Fintype.card_prod, Nat.cast_mul]
    nlinarith
  have hsup : ∀ g : ι → ℝ, (∀ x, g x ≤ c) → ⨆ x, g x ≤ c := fun g hg => Real.iSup_le hg hc
  have hcol : ∀ g : ι → ι → ℝ, (∀ u v, 0 ≤ g u v) → (∀ u v, g u v ≤ c) →
      ⨆ y, Real.sqrt (∑ x, g x y ^ 2) ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * c := fun g hg0 hg =>
    Real.iSup_le (fun y => (FS_sqrt_le (fun x => g x y) c hc (fun x => hg0 x y)
      (fun x => hg x y)).trans h2) (by positivity)
  have hrow : ∀ g : ι → ι → ℝ, (∀ u v, 0 ≤ g u v) → (∀ u v, g u v ≤ c) →
      Real.sqrt (∑ y, (⨆ x, g x y) ^ 2) ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 * c := fun g hg0 hg =>
    (FS_sqrt_le (fun y => ⨆ x, g x y) c hc (fun y => Real.iSup_nonneg fun x => hg0 x y)
      (fun y => hsup _ fun x => hg x y)).trans h2
  have hss : ∀ g : ι → ι → ℝ, (∀ u v, g u v ≤ c) → ⨆ x, ⨆ y, g x y ≤ c := fun g hg =>
    Real.iSup_le (fun x => hsup _ fun y => hg x y) hc
  unfold foptNorm
  split_ifs
  · split
    · exact (hsup _ fun x => hf x x).trans h1
    · exact (FS_sqrt_le (fun x => f x x) c hc (fun x => hf0 x x) (fun x => hf x x)).trans h2
    · exact (Finset.sum_le_sum (fun x _ => hf x x)).trans (by simpa using h2)
  · unfold fcsNorm
    split
    · exact hsq f hf0 hf
    · exact hcol f hf0 hf
    · exact hrow f hf0 hf
    · exact (hss f hf).trans h1
  · unfold fcsNorm
    split
    · exact hsq (fun y x => f x y) (fun u v => hf0 v u) (fun u v => hf v u)
    · exact hcol (fun y x => f x y) (fun u v => hf0 v u) (fun u v => hf v u)
    · exact hrow (fun y x => f x y) (fun u v => hf0 v u) (fun u v => hf v u)
    · exact (hss (fun y x => f x y) (fun u v => hf v u)).trans h1

end Crude

/-- `x^t ≥ N^{-c|t|}` for `x ∈ [N^{-c}, N^c]`. -/
private lemma FS_rpow_low {N : ℝ} (hN : 1 ≤ N) {c : ℝ} {x : ℝ} (hx1 : N ^ (-c) ≤ x)
    (hx2 : x ≤ N ^ c) (t : ℝ) : N ^ (-(c * |t|)) ≤ x ^ t := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hx1
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    calc N ^ (-(c * t)) = (N ^ (-c)) ^ t := by rw [← Real.rpow_mul hN0.le]; ring_nf
      _ ≤ x ^ t := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hx1 ht
  · rw [abs_of_neg ht]
    calc N ^ (-(c * -t)) = (N ^ c) ^ t := by rw [← Real.rpow_mul hN0.le]; ring_nf
      _ ≤ x ^ t := Real.rpow_le_rpow_of_nonpos hx0 hx2 ht.le

/-- The exponent of the lower bound of a monomial. -/
private def FS_Kq (q : FMono) : ℝ := |(q.a : ℝ) / 2| + 2 * |(q.i : ℝ) / 2| + 3 * |-(q.l : ℝ) / 2|

private lemma FS_Kq_nonneg (q : FMono) : 0 ≤ FS_Kq q := by unfold FS_Kq; positivity

/-- A monomial is at least `N^{-K} ‖A‖^{d + o}` for `Im m ∈ [N^{-2}, N²]`, `η ∈ [N^{-3}, N³]`,
`‖A‖ ≤ ‖A‖_HS`. -/
private lemma FS_ev_low {N : ℕ} (hN : 1 ≤ N) {M η hs op : ℝ} (hM1 : (N : ℝ) ^ (-(2 : ℝ)) ≤ M)
    (hM2 : M ≤ (N : ℝ) ^ (2 : ℝ)) (hη1 : (N : ℝ) ^ (-(3 : ℝ)) ≤ η) (hη2 : η ≤ (N : ℝ) ^ (3 : ℝ))
    (hop : 0 ≤ op) (hhs : op ≤ hs) (q : FMono) :
    (N : ℝ) ^ (-FS_Kq q) * op ^ (q.d + q.o) ≤ q.evalR N M η hs op := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have ha := FS_rpow_low hNr (c := 1) (x := N) (by
    rw [Real.rpow_neg_one]; exact (inv_le_one_of_one_le₀ hNr).trans hNr) (by rw [Real.rpow_one])
    ((q.a : ℝ) / 2)
  have hi := FS_rpow_low hNr hM1 hM2 ((q.i : ℝ) / 2)
  have hl := FS_rpow_low hNr hη1 hη2 (-(q.l : ℝ) / 2)
  have hK : (N : ℝ) ^ (-FS_Kq q) = (N : ℝ) ^ (-(1 * |(q.a : ℝ) / 2|)) *
      (N : ℝ) ^ (-(2 * |(q.i : ℝ) / 2|)) * (N : ℝ) ^ (-(3 * |-(q.l : ℝ) / 2|)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, FS_Kq]
    ring_nf
  rw [hK, pow_add, FMono.evalR]
  have hd : op ^ q.d ≤ hs ^ q.d := pow_le_pow_left₀ hop hhs _
  have hM0 : 0 ≤ M := (Real.rpow_nonneg hN0.le _).trans hM1
  have hη0 : 0 ≤ η := (Real.rpow_nonneg hN0.le _).trans hη1
  have h3 := mul_le_mul (mul_le_mul ha hi (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _))
    hl (Real.rpow_nonneg hN0.le _)
    (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hM0 _))
  rw [← mul_assoc]
  exact mul_le_mul (mul_le_mul h3 hd (pow_nonneg hop _) (mul_nonneg (mul_nonneg
    (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hM0 _)) (Real.rpow_nonneg hη0 _))) le_rfl
    (pow_nonneg hop _) (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _)
      (Real.rpow_nonneg hM0 _)) (Real.rpow_nonneg hη0 _)) (pow_nonneg (hop.trans hhs) _))

/-- The bound on `Im m` and `η` at the slots lie in `[N^{-2}, N²]` and `[N^{-3}, 1]`. -/
private lemma FS_slot_range {D N k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε'' : ε ≤ 1 / 3) (hN : 1 ≤ N)
    (hDN : D ≤ N) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) :
    (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ∧
    (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) ∧
    (N : ℝ) ^ (-(3 : ℝ)) ≤ etaK D N k ε ∧ etaK D N k ε ≤ 1 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hrk1 : (1 : ℝ) ≤ rk D N k := (FS_pos ε hN hk hkN).1
  have hrk2 : rk D N k ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    unfold rk
    have : min k (D * N + 1 - k) ≤ N * N := by
      have := Nat.mul_le_mul_right N hDN
      omega
    exact_mod_cast (show min k (D * N + 1 - k) ≤ N ^ 2 by rw [sq]; exact this)
  have hrk0 : (0 : ℝ) < rk D N k := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * 1 := by
          rw [mul_one]; exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_rpow hrk1 (by norm_num))
          (Real.rpow_nonneg hN0.le _)
  · calc _ ≤ 1 * rk D N k := by
          refine mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)) ?_
            (Real.rpow_nonneg hrk0.le _) zero_le_one
          exact Real.rpow_le_self_of_one_le hrk1 (by norm_num)
      _ ≤ _ := by rw [one_mul]; exact hrk2
  · unfold etaK
    have h1 : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have h2 : (N : ℝ) ^ (-(2 : ℝ)) ≤ rk D N k ^ (-(1 / 3 : ℝ)) := by
      calc (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ (2 : ℝ))⁻¹ := Real.rpow_neg hN0.le _
        _ ≤ (rk D N k)⁻¹ := inv_anti₀ hrk0 hrk2
        _ = rk D N k ^ (-(1 : ℝ)) := (Real.rpow_neg_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hrk1 (by norm_num)
    calc (N : ℝ) ^ (-(3 : ℝ)) = (N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_add hN0]; norm_num
      _ ≤ _ := mul_le_mul h1 h2 (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)
  · unfold etaK
    exact mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith))
      (Real.rpow_nonneg hrk0.le _) (Real.rpow_le_one_of_one_le_of_nonpos hrk1 (by norm_num))

/-- The facts at the slots used by the deterministic bounds, with one constant `K`. -/
private lemma FS_facts (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e →
      2 ≤ N ∧ D + 1 ≤ N ∧ 2 * K ≤ N ∧ (∀ a, (e.z a).im = etaK D N k ε) ∧
      0 < etaK D N k ε ∧ (N : ℝ) ^ (-(3 : ℝ)) ≤ etaK D N k ε ∧ etaK D N k ε ≤ 1 ∧
      (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) ∧
      (∀ a, opNorm (e.M a) ≤ K) ∧ opNorm e.Lt ≤ K * opNorm A ∧ opNorm A ≤ 1 ∧
      opNorm A ≤ hsNorm A := by
  obtain ⟨c₀, K, -, hK, N₁, hslot⟩ := FE_slot D hD δA εA ε hδA hεA hε hε' hε'' C
  refine ⟨K, hK, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max N₁ (D + 1)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * K)] with N hN hNK
  intro μ A k e ⟨hμ, hA, hk, hkN, hhs, he⟩
  obtain ⟨-, -, hN1, -, hz, hη, -, -, hM, -, hL, -, -, hA1, -, -⟩ :=
    hslot N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  have hDN : D + 1 ≤ N := le_of_max_le_right hN
  obtain ⟨h1, h2, h3, h4⟩ := FS_slot_range (D := D) hε hε'' hN1 (by omega) hk hkN
  exact ⟨by omega, hDN, hNK, hz, hη, h3, h4, h1, h2, hM, hL, hA1, PS_op_le_hs A⟩

/-- The norm of a letter at a Hermitian array: `K ‖A‖` for `Λ̃`, `2K + η⁻¹` for the others. -/
private lemma FS_let_le {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) {K η op : ℝ} (hK : 1 ≤ K)
    (hη : 0 < η) (hz : ∀ a, (e.z a).im = η) (hM : ∀ a, opNorm (e.M a) ≤ K)
    (hL : opNorm e.Lt ≤ K * op) (z : FLet) :
    opNorm (FLet.mat e ι h z) ≤ if z = .lamt then K * op else 2 * K + η⁻¹ := by
  have hηi : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  rcases z with ⟨a, f⟩ | ⟨a, pr⟩ | x | _
  · have hX := hh.add (Bd_lamc_herm D N e.A (e.c a))
    have hr := Bd_opNorm_res _ hX (e.z a) (by rw [hz a]; exact hη.ne')
    rw [hz a, abs_of_pos hη] at hr
    simp only [FLet.mat, reduceCtorEq, if_false]
    split_ifs
    · rw [Bd_opNorm_conjTranspose]; linarith
    · linarith
  · simp only [FLet.mat, reduceCtorEq, if_false]
    split_ifs
    · refine (Bd_opNorm_sub _ _).trans ?_
      rw [Bd_opNorm_conjTranspose]
      linarith [hM a]
    · linarith [hM a]
  · simp only [FLet.mat, reduceCtorEq, if_false]
    linarith [Bd_opNorm_E e ι x]
  · simpa [FLet.mat] using hL

/-- The norm of a word: `R` per letter and `Q` per `Λ̃`. -/
private lemma FS_word_le {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (f : FLet → Matrix ι' ι' ℂ)
    (R Q : ℝ) (hR : 1 ≤ R) (hQ : 0 ≤ Q) : ∀ l : List FLet,
    (∀ z ∈ l, opNorm (f z) ≤ if z = .lamt then Q else R) →
    opNorm (l.map f).prod ≤ R ^ l.length * Q ^ (l.countP (· == .lamt))
  | [], _ => by simpa using Bd_opNorm_one
  | z :: l, hl => by
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.countP_cons]
    refine (opNorm_mul_le _ _).trans ?_
    have h1 := hl z List.mem_cons_self
    have h2 := FS_word_le f R Q hR hQ l fun z' hz' => hl z' (List.mem_cons_of_mem _ hz')
    have hp : 0 ≤ R ^ l.length * Q ^ (l.countP (· == .lamt)) := by positivity
    have hR1 : 1 ≤ R ^ l.length := one_le_pow₀ hR
    by_cases hz : z = .lamt
    · subst hz
      simp only [if_true, beq_self_eq_true] at h1 ⊢
      calc opNorm (f .lamt) * opNorm (l.map f).prod ≤ Q * (R ^ l.length * Q ^ (l.countP
            (· == .lamt))) := mul_le_mul h1 h2 (Bd_opNorm_nonneg _) hQ
        _ ≤ R ^ (l.length + 1) * Q ^ (l.countP (· == .lamt) + 1) := by
          have := mul_le_mul_of_nonneg_left hR (mul_nonneg hp hQ)
          rw [pow_succ, pow_succ]
          linarith
    · have hz' : (z == FLet.lamt) = false := by simpa using hz
      simp only [hz, if_false, hz'] at h1 ⊢
      calc opNorm (f z) * opNorm (l.map f).prod ≤ R * (R ^ l.length * Q ^ (l.countP
            (· == .lamt))) := mul_le_mul h1 h2 (Bd_opNorm_nonneg _) (by linarith)
        _ = R ^ (l.length + 1) * Q ^ (l.countP (· == .lamt) + 0) := by ring

/-- A word at a Hermitian array: `‖w‖ ≤ N^{5|w|} ‖A‖^{n_Λ̃}`. -/
private lemma FS_word_N {N : ℕ} {K η op W : ℝ} (L c : ℕ) (hN2 : 2 ≤ N) (hNK : 2 * K ≤ N)
    (hK : 1 ≤ K) (hη : 0 < η) (hη3 : (N : ℝ) ^ (-(3 : ℝ)) ≤ η) (hop : 0 ≤ op)
    (hW : W ≤ (2 * K + η⁻¹) ^ L * (K * op) ^ c) (hc : c ≤ L) :
    W ≤ (N : ℝ) ^ (5 * L) * op ^ c := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hi : η⁻¹ ≤ (N : ℝ) ^ 3 := by
    have := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hη3
    rwa [Real.rpow_neg hN0.le, inv_inv, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at this
  have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have h4 : (N : ℝ) ^ 4 = N * (N : ℝ) ^ 3 := by ring
  have hR : 2 * K + η⁻¹ ≤ (N : ℝ) ^ 4 := by nlinarith
  have hQ : K * op ≤ N * op := mul_le_mul_of_nonneg_right (by linarith) hop
  calc W ≤ ((N : ℝ) ^ 4) ^ L * ((N : ℝ) * op) ^ c := by
        refine hW.trans (mul_le_mul (pow_le_pow_left₀ (by positivity) hR L)
          (pow_le_pow_left₀ (by nlinarith) hQ c) (by positivity) (by positivity))
    _ = (N : ℝ) ^ (4 * L) * (N : ℝ) ^ c * op ^ c := by rw [← pow_mul, mul_pow]; ring
    _ ≤ (N : ℝ) ^ (4 * L) * (N : ℝ) ^ L * op ^ c := by
        gcongr
        · exact_mod_cast (by omega : 1 ≤ N)
    _ = (N : ℝ) ^ (5 * L) * op ^ c := by rw [← pow_add]; ring_nf

/-- From `n ≤ N^a X` and `N^{-b} X ≤ V`: `n ≤ N^{a+b} V`. -/
private lemma FS_fin {N : ℝ} (hN : 0 < N) {a b n V X : ℝ} (h1 : n ≤ N ^ a * X)
    (h2 : N ^ (-b) * X ≤ V) : n ≤ N ^ (a + b) * V := by
  calc n ≤ N ^ a * X := h1
    _ = N ^ (a + b) * (N ^ (-b) * X) := by
        rw [← mul_assoc, ← Real.rpow_add hN]
        ring_nf
    _ ≤ N ^ (a + b) * V := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN.le _)

/-- A factor whose norm does not depend on the array is bounded by `N` times its size at every
array: its bad event is empty or everything. -/
private lemma FS_const (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (rk : List ℕ)
    (p : FFac × ℕ) (hp : FS_ok nb rk p) :
    ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e → ∀ ι : Fin nb → Fin D,
      (∀ h h', FS_n rk e ι h p = FS_n rk e ι h' p) →
      ∀ h, FS_n rk e ι h p ≤ (N : ℝ) ^ (1 : ℝ) * FS_V (FS_ev D N k ε A) p := by
  filter_upwards [FS_good_one D hD δA εA ε hδA hεA hε hε' hε'' C nb rk p hp 1 one_pos 1 one_pos,
    Filter.eventually_ge_atTop 2] with N h1 hN2
  intro μ A k e hs ι hc h
  obtain ⟨s, hs', hg⟩ := h1 μ A k e hs ι
  by_contra hlt
  push_neg at hlt
  have huniv : s = Set.univ := Set.eq_univ_of_forall fun h' => by
    by_contra hn
    have := hg h' hn
    rw [hc h' h] at this
    linarith
  have hprob := hs.1.prob
  rw [huniv, measure_univ] at hs'
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have h1' : (N : ℝ) ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have := ENNReal.one_le_ofReal.1 hs'
  linarith

/-- A word without a resolvent does not depend on the array. -/
private lemma FS_map_free {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (w : List FLet) (hw : w.countP FO_isRes = 0) (h h' : Idx D N → Idx D N → ℂ) :
    w.map (FLet.mat e ι h) = w.map (FLet.mat e ι h') := by
  refine List.map_congr_left fun z hz => ?_
  have := List.countP_eq_zero.1 hw z hz
  rcases z with ⟨a, f⟩ | ⟨a, pr⟩ | x | _
  · simp [FO_isRes] at this
  all_goals rfl

/-- A loop with a resolvent: at most `n_Λ̃` powers of `‖A‖_HS` and `‖A‖` in its size. -/
private lemma FS_fixV_do (w : List FLet) (hr : 1 ≤ w.countP FO_isRes) :
    (FFac.loop w).fixV.d + (FFac.loop w).fixV.o ≤ w.countP (· == .lamt) := by
  obtain ⟨z, hz, hzr⟩ := List.countP_pos_iff.1 hr
  rcases z with ⟨a, f⟩ | ⟨a, pr⟩ | x | _ <;> simp only [FO_isRes, Bool.false_eq_true] at hzr
  have hd : ∀ r, (FMono.psi r).d = 0 := fun r => (FS_psi_do r).1
  have ho : ∀ r, (FMono.psi r).o = 0 := fun r => (FS_psi_do r).2
  simp only [FFac.fixV]
  split_ifs <;>
    first
    | exact absurd ‹List.countP _ w = 0› (List.countP_pos_iff.2 ⟨_, hz, rfl⟩).ne'
    | (simp only [FMono.mul, hd, ho]; omega)

/-- The common bounds at a Hermitian array: words, resolvents, `𝔐_a`, and the monomials from
below. -/
private lemma FS_com (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) :
    ∃ Kf : ℝ, ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e →
      ∀ (ι : Fin nb → Fin D) h, (Matrix.of h).IsHermitian →
      (0 : ℝ) < N ∧ 2 ≤ N ∧ D + 1 ≤ N ∧ 0 ≤ opNorm A ∧ opNorm A ≤ 1 ∧
      (∀ w : List FLet, opNorm (w.map (FLet.mat e ι h)).prod ≤
        (N : ℝ) ^ (5 * w.length) * opNorm A ^ (w.countP (· == .lamt))) ∧
      (∀ a, opNorm (e.G h a) ≤ (N : ℝ) ^ 4 - Kf) ∧ (∀ a, opNorm (e.M a) ≤ Kf) ∧
      ∀ q : FMono, (N : ℝ) ^ (-FS_Kq q) * opNorm A ^ (q.d + q.o) ≤ FS_ev D N k ε A q := by
  obtain ⟨Kf, hKf, hF⟩ := FS_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  refine ⟨Kf, ?_⟩
  filter_upwards [hF] with N hN
  intro μ A k e hs ι h hh
  obtain ⟨hN2, hDN, hNK, hz, hη, hη3, hη1, hM1, hM2, hMK, hL, hA1, hAhs⟩ := hN μ A k e hs
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hop0 := Bd_opNorm_nonneg A
  have hi : (etaK D N k ε)⁻¹ ≤ (N : ℝ) ^ 3 := by
    have := inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hη3
    rwa [Real.rpow_neg (by linarith), inv_inv, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at this
  refine ⟨by linarith, hN2, hDN, hop0, hA1, fun w => ?_, fun a => ?_, hMK, fun q => ?_⟩
  · have hR1 : 1 ≤ 2 * Kf + (etaK D N k ε)⁻¹ := by linarith [inv_nonneg.2 hη.le]
    have hQ0 : 0 ≤ Kf * opNorm A := by positivity
    have hw := FS_word_le (FLet.mat e ι h) (2 * Kf + (etaK D N k ε)⁻¹) (Kf * opNorm A) hR1 hQ0
      w fun z _ => FS_let_le e ι h hh hKf hη hz hMK hL z
    have hc : w.countP (· == .lamt) ≤ w.length := List.countP_le_length
    exact FS_word_N w.length (w.countP (· == .lamt)) hN2 hNK hKf hη hη3 hop0 hw hc
  · have hG := Bd_G_norm e h hh a (by rw [hz a]; exact hη.ne')
    rw [hz a, abs_of_pos hη] at hG
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have h5 : 2 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := by
      rw [show (N : ℝ) ^ 4 = N * (N : ℝ) ^ 3 by ring]
      exact mul_le_mul_of_nonneg_right hNr (by positivity)
    linarith only [hG, hi, h3, h5, hNK, hKf]
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    exact FS_ev_low (by omega) hM1 hM2 hη3 (hη1.trans hN1) hop0 hAhs q

private lemma FS_card {D N : ℕ} (hN : D + 1 ≤ N) :
    ((Fintype.card (Idx D N) : ℝ) + 1) ^ 2 ≤ (N : ℝ) ^ 4 := by
  have : D * N + 1 ≤ N * N := by nlinarith
  have h' : ((Fintype.card (Idx D N) : ℝ) + 1) ≤ (N : ℝ) ^ 2 := by
    simp only [Idx, Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast (show D * N + 1 ≤ N ^ 2 by rw [sq]; exact this)
  calc _ ≤ ((N : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
    _ = (N : ℝ) ^ 4 := by ring

/-- At every Hermitian array, one factor with its option is bounded by `N^K` times its size, `K`
depending only on the factor and its option. -/
private lemma FS_crude_one (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (rk : List ℕ)
    (p : FFac × ℕ) (hp : FS_ok nb rk p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e →
      ∀ (ι : Fin nb → Fin D) h, (Matrix.of h).IsHermitian →
        FS_n rk e ι h p ≤ (N : ℝ) ^ K * FS_V (FS_ev D N k ε A) p := by
  obtain ⟨Kf, hcom⟩ := FS_com D hD δA εA ε hδA hεA hε hε' hε'' C nb
  have hconst := FS_const D hD δA εA ε hδA hεA hε hε' hε'' C nb rk p hp
  obtain ⟨f, i⟩ := p
  rcases f with ⟨x, y, w⟩ | w | ⟨a, u⟩
  · obtain ⟨hx, hy, o, hop, hmem, -, -, -⟩ := FS_ok_ent hp
    have hmenu := FS_menu _ _ _ _ _ ⟨rfl, rfl⟩ o (hmem _ rfl)
    by_cases hr : (FLet.parts w).sum = 0
    · refine ⟨1, zero_le_one, ?_⟩
      filter_upwards [hconst] with N hN
      intro μ A k e hs ι h _
      refine hN μ A k e hs ι (fun h h' => ?_) h
      rw [FE_parts_sum] at hr
      rw [FS_n_ent rk e ι h hop hx hy, FS_n_ent rk e ι h' hop hx hy]
      congr 1
      funext u v
      unfold FS_hat
      rw [FS_map_free e ι w hr h h']
    · obtain ⟨hne, hdo⟩ := hmenu.2 (Nat.pos_of_ne_zero hr)
      obtain ⟨q₀, hq₀⟩ := List.exists_mem_of_ne_nil _ hne
      refine ⟨((5 * w.length + 4 : ℕ) : ℝ) + FS_Kq q₀, by
        have := FS_Kq_nonneg q₀; positivity, ?_⟩
      filter_upwards [hcom] with N hN
      intro μ A k e hs ι h hh
      obtain ⟨hN0, -, hDN, hop0, hA1, hW, -, -, hlow⟩ := hN μ A k e hs ι h hh
      have hn : FS_n rk e ι h (.ent x y w, i) ≤ (N : ℝ) ^ (((5 * w.length + 4 : ℕ) : ℝ)) *
          opNorm A ^ (w.countP (· == .lamt)) := by
        rw [FS_n_ent rk e ι h hop hx hy, Real.rpow_natCast]
        refine (FS_fopt_le _ o _ _ (opNorm (w.map (FLet.mat e ι h)).prod) (Bd_opNorm_nonneg _)
          (FS_hat_nonneg e ι h x y w) (fun u v => ?_)).trans ?_
        · unfold FS_hat
          split_ifs
          · exact Bd_opNorm_nonneg _
          · exact norm_apply_le_opNorm _ _ _
        · calc _ ≤ (N : ℝ) ^ 4 * ((N : ℝ) ^ (5 * w.length) * opNorm A ^ (w.countP
                (· == .lamt))) := mul_le_mul (FS_card hDN) (hW w) (Bd_opNorm_nonneg _)
                  (by positivity)
            _ = _ := by ring
      refine FS_fin hN0 hn ((mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hop0 hA1 ?_)
        (Real.rpow_nonneg hN0.le _)).trans ((hlow q₀).trans ?_))
      · have := hdo q₀ hq₀
        rw [FE_parts_len] at this
        omega
      · simp only [FS_V, hop]
        exact List.single_le_sum (fun t ht => by
          obtain ⟨m, -, rfl⟩ := List.mem_map.1 ht
          exact FS_ev_nonneg D N k ε A m) _ (List.mem_map_of_mem hq₀)
  · by_cases hr : w.countP FO_isRes = 0
    · refine ⟨1, zero_le_one, ?_⟩
      filter_upwards [hconst] with N hN
      intro μ A k e hs ι h _
      refine hN μ A k e hs ι (fun h h' => ?_) h
      simp only [FS_n, FS_one, FFac.val, FS_map_free e ι w hr h h']
    · refine ⟨((5 * w.length : ℕ) : ℝ) + FS_Kq (FFac.loop w).fixV, by
        have := FS_Kq_nonneg (FFac.loop w).fixV; positivity, ?_⟩
      filter_upwards [hcom] with N hN
      intro μ A k e hs ι h hh
      obtain ⟨hN0, hN2, -, hop0, hA1, hW, -, -, hlow⟩ := hN μ A k e hs ι h hh
      let κ₀ : ℕ → Idx D N := fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)
      have hn : FS_n rk e ι h (.loop w, i) ≤ (N : ℝ) ^ (((5 * w.length : ℕ) : ℝ)) *
          opNorm A ^ (w.countP (· == .lamt)) := by
        rw [Real.rpow_natCast]
        exact (FS_n_fix rk e ι h _ rfl κ₀).trans ((Bd_ntr_le _).trans (hW w))
      refine FS_fin hN0 hn ((mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hop0 hA1
        (FS_fixV_do w (by omega))) (Real.rpow_nonneg hN0.le _)).trans ((hlow _).trans ?_))
      simp [FS_V, FS_opt, FFac.entData]
  · refine ⟨((4 : ℕ) : ℝ) + FS_Kq (FFac.wt a u).fixV, by
      have := FS_Kq_nonneg (FFac.wt a u).fixV; positivity, ?_⟩
    filter_upwards [hcom] with N hN
    intro μ A k e hs ι h hh
    obtain ⟨hN0, hN2, -, hop0, hA1, -, hG, hMK, hlow⟩ := hN μ A k e hs ι h hh
    let κ₀ : ℕ → Idx D N := fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)
    have hn : FS_n rk e ι h (.wt a u, i) ≤ (N : ℝ) ^ (((4 : ℕ) : ℝ)) *
        opNorm A ^ ((FFac.wt a u).fixV.d + (FFac.wt a u).fixV.o) := by
      rw [Real.rpow_natCast]
      refine (FS_n_fix rk e ι h _ rfl κ₀).trans ((Bd_ntr_le _).trans ?_)
      refine (opNorm_mul_le _ _).trans ?_
      have h1 := (Bd_opNorm_sub (e.G h a) (e.M a)).trans (add_le_add (hG a) (hMK a))
      have h2 := Bd_opNorm_E e ι u
      simp only [FFac.fixV, add_zero, pow_zero, mul_one]
      calc _ ≤ ((N : ℝ) ^ 4 - Kf + Kf) * 1 :=
            mul_le_mul h1 h2 (Bd_opNorm_nonneg _) (by ring_nf; positivity)
        _ = (N : ℝ) ^ 4 := by ring
    refine FS_fin hN0 hn ((hlow _).trans ?_)
    simp [FS_V, FS_opt, FFac.entData]

/-- At every Hermitian array, the product of the norms of a list of factors is at most `N^K`
times the product of their sizes. -/
private lemma FS_crude_list (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (rk : List ℕ) :
    ∀ P : List (FFac × ℕ), (∀ p ∈ P, FS_ok nb rk p) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N in atTop, ∀ μ A k e, FS_Slots D δA εA ε C N μ A k e →
      ∀ (ι : Fin nb → Fin D) h, (Matrix.of h).IsHermitian →
        (P.map (FS_n rk e ι h)).prod ≤ (N : ℝ) ^ K * (P.map (FS_V (FS_ev D N k ε A))).prod
  | [], _ => ⟨0, le_rfl, Filter.Eventually.of_forall fun N μ A k e _ ι h _ => by simp⟩
  | p :: P, hP => by
    obtain ⟨K₁, hK₁, h₁⟩ := FS_crude_one D hD δA εA ε hδA hεA hε hε' hε'' C nb rk p
      (hP p List.mem_cons_self)
    obtain ⟨K₂, hK₂, h₂⟩ := FS_crude_list D hD δA εA ε hδA hεA hε hε' hε'' C nb rk P
      fun q hq => hP q (List.mem_cons_of_mem _ hq)
    refine ⟨K₁ + K₂, by linarith, ?_⟩
    filter_upwards [h₁, h₂, Filter.eventually_ge_atTop 1] with N e₁ e₂ hN
    intro μ A k e hs ι h hh
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [List.map_cons, List.prod_cons]
    have hpn : 0 ≤ (P.map (FS_n rk e ι h)).prod := List.prod_nonneg fun t ht => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
      exact FS_n_nonneg rk e ι h q
    have hV := FS_V_nonneg _ (FS_ev_nonneg D N k ε A) p
    calc FS_n rk e ι h p * (P.map (FS_n rk e ι h)).prod ≤
          ((N : ℝ) ^ K₁ * FS_V (FS_ev D N k ε A) p) *
            ((N : ℝ) ^ K₂ * (P.map (FS_V (FS_ev D N k ε A))).prod) :=
          mul_le_mul (e₁ μ A k e hs ι h hh) (e₂ μ A k e hs ι h hh) hpn
            (mul_nonneg (Real.rpow_nonneg hN0.le _) hV)
      _ = _ := by rw [Real.rpow_add hN0]; ring

/-! ### The label sum of a valid assignment -/

/-- A valid assignment as a list of factors paired with option indices. -/
private lemma FS_setup {nb : ℕ} {F : List FFac} {g : FAsg} (hg : fvalid nb F g = true) :
    ∃ P : List (FFac × ℕ), F = P.map Prod.fst ∧ g = ⟨g.rk, P.flatMap FS_os⟩ ∧
      (∀ p ∈ P, FS_ok nb g.rk p) ∧
      ∀ l, l < 4 → fuses (P.map Prod.fst) ⟨g.rk, P.flatMap FS_os⟩ l ≤ 2 := by
  have hlen : g.opt.length = (F.filterMap FFac.entData).length := by
    unfold fvalid at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg.1.1.1.2
  obtain ⟨P, hPF, hPo⟩ := FS_pairs F g.opt hlen
  have hg' : g = ⟨g.rk, P.flatMap FS_os⟩ := by rw [hPo]
  rw [← hPF, hg'] at hg
  exact ⟨P, hPF.symm, hg', FS_valid P hg⟩

/-- The label sum and the block indices at one array: at most `D^{nb} D⁴` times the label
monomial times a bound on the product of the norms of the factors, uniform in the block
indices. -/
private lemma FS_sum_le {nb : ℕ} {rk : List ℕ} {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) (P : List (FFac × ℕ))
    (hP : ∀ p ∈ P, FS_ok nb rk p)
    (hcap : ∀ l, l < 4 → fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l ≤ 2) (M η hs op X : ℝ)
    (hX : ∀ ι : Fin nb → Fin D, (P.map (FS_n rk e ι h)).prod ≤ X) :
    ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
      ∑ ι : Fin nb → Fin D, ‖((P.map Prod.fst).map (FFac.val e ι
        (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod‖ else 0) ≤
    (D : ℝ) ^ nb * ((D : ℝ) ^ 4 * (⟨((List.range 4).map fun l =>
      2 - (fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l : ℤ)).sum, 0, 0, 0, 0⟩ :
        FMono).evalR N M η hs op * X) := by
  have hswap : (∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
      ∑ ι : Fin nb → Fin D, ‖((P.map Prod.fst).map (FFac.val e ι
        (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod‖ else 0)) =
      ∑ ι : Fin nb → Fin D, ∑ κ : Fin 4 → Idx D N, (if FS_blk κ then
        ‖((P.map Prod.fst).map (FFac.val e ι (FS_k κ) h)).prod‖ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    unfold FS_blk FS_k
    split_ifs <;> simp
  rw [hswap]
  have hcard : (Fintype.card (Fin nb → Fin D) : ℝ) = (D : ℝ) ^ nb := by simp
  have hlab := FS_lab_le D N hD hN (fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩) M η hs op
  have hlab0 : 0 ≤ ∏ l : Fin 4, ((Fintype.card (Idx D N) : ℝ)) ^
      ((2 - (fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l : ℝ)) / 2) :=
    Finset.prod_nonneg fun l _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc _ ≤ ∑ _ι : Fin nb → Fin D, ((D : ℝ) ^ 4 * (⟨((List.range 4).map fun l =>
        2 - (fuses (P.map Prod.fst) ⟨rk, P.flatMap FS_os⟩ l : ℤ)).sum, 0, 0, 0, 0⟩ :
          FMono).evalR N M η hs op * X) := by
        refine Finset.sum_le_sum fun ι _ => (FS_det e ι h P hP hcap).trans ?_
        have hn : 0 ≤ (P.map (FS_n rk e ι h)).prod := List.prod_nonneg fun t ht => by
          obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
          exact FS_n_nonneg rk e ι h q
        exact mul_le_mul hlab (hX ι) hn ((hlab0.trans hlab))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

/-- The bound of the further class on one good event: at the slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law], outside an
event of probability `≤ N^{-D'}`, the sum over the labels and the block indices of
`|Π factors|` is at most `N^{τ'}` times the bound of a valid assignment. -/
theorem pkg_fsharp_good (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (F : List FFac)
    (g : FAsg) (hg : fvalid nb F g = true) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        μ {h | (N : ℝ) ^ τ' * ((fboundM F g).map fun m => m.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A)).sum <
          ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
            ∑ ι : Fin nb → Fin D, ‖(F.map (FFac.val e ι
              (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod‖ else 0)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨P, rfl, hgP, hP, hcap⟩ := FS_setup hg
  obtain ⟨rks, opt⟩ := g
  simp only at hgP hP hcap
  cases hgP
  set n := P.length with hn
  have hτ'' : 0 < τ' / (2 * (n + 1)) := by positivity
  have hgl := FS_good_list D hD δA εA ε hδA hεA hε hε' hε'' C nb rks _ hτ'' (D' + 1) (by linarith)
    P hP
  have hev1 : ∀ᶠ N : ℕ in atTop, (D : ℝ) ^ nb * (D : ℝ) ^ 4 ≤ (N : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ' / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hev2 : ∀ᶠ N : ℕ in atTop, (D : ℝ) ^ nb * n ≤ N :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (hgl.and (hev1.and (hev2.and (Filter.eventually_ge_atTop 1))))
  refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  obtain ⟨hG, h1, h2, hN1⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨s, hs, hgood⟩ := PS_bad_fin μ (fun ι h => (P.map (FS_n rks e ι h)).prod ≤
      ((N : ℝ) ^ (τ' / (2 * (n + 1)))) ^ n * (P.map (FS_V (FS_ev D N k ε A))).prod)
    (n * (N : ℝ) ^ (-(D' + 1))) (by positivity) (hG μ A k e ⟨hμ, hA, hk, hkN, hhs, he⟩)
  have hB := FS_bound_eq (FS_ev D N k ε A) (FS_ev_mul ε A hN1 hk hkN) (FS_ev_one ε A) rks P
  have hV0 : 0 ≤ (P.map (FS_V (FS_ev D N k ε A))).prod := List.prod_nonneg fun t ht => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
    exact FS_V_nonneg _ (FS_ev_nonneg D N k ε A) q
  have hL0 : 0 ≤ FS_ev D N k ε A ⟨((List.range 4).map fun l =>
      2 - (fuses (P.map Prod.fst) ⟨rks, P.flatMap FS_os⟩ l : ℤ)).sum, 0, 0, 0, 0⟩ :=
    FS_ev_nonneg D N k ε A _
  refine le_trans (measure_mono fun h hh => ?_) (hs.trans (ENNReal.ofReal_le_ofReal ?_))
  · by_contra hns
    simp only [Set.mem_ofPred_eq] at hh
    refine absurd hh (not_lt.2 ?_)
    refine (FS_sum_le (by omega) hN1 e h P hP hcap ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) *
      rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε) (hsNorm A) (opNorm A) _
      fun ι => hgood h hns ι).trans ?_
    change _ ≤ _ * ((fboundM (P.map Prod.fst) ⟨rks, P.flatMap FS_os⟩).map
      (FS_ev D N k ε A)).sum
    rw [hB]
    have hpow : ((N : ℝ) ^ (τ' / (2 * (n + 1)))) ^ n ≤ (N : ℝ) ^ (τ' / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      refine Real.rpow_le_rpow_of_exponent_le hNr ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsplit : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
      rw [← Real.rpow_add hN0]
      ring_nf
    rw [hsplit]
    have hP0 : 0 ≤ ((N : ℝ) ^ (τ' / (2 * (n + 1)))) ^ n := by positivity
    calc (D : ℝ) ^ nb * ((D : ℝ) ^ 4 * FS_ev D N k ε A _ *
          (((N : ℝ) ^ (τ' / (2 * (n + 1)))) ^ n * (P.map (FS_V (FS_ev D N k ε A))).prod)) =
          ((D : ℝ) ^ nb * (D : ℝ) ^ 4) * ((N : ℝ) ^ (τ' / (2 * (n + 1)))) ^ n *
            (FS_ev D N k ε A _ * (P.map (FS_V (FS_ev D N k ε A))).prod) := by ring
      _ ≤ (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) *
            (FS_ev D N k ε A _ * (P.map (FS_V (FS_ev D N k ε A))).prod) := by
          gcongr
      _ = _ := by ring
  · rw [show (Fintype.card (Fin nb → Fin D) : ℝ) = (D : ℝ) ^ nb by simp, Real.rpow_neg hN0.le,
      Real.rpow_neg hN0.le, Real.rpow_add hN0, Real.rpow_one, mul_inv, ← mul_assoc, ← mul_assoc]
    have hi : 0 ≤ ((N : ℝ) ^ D')⁻¹ := by positivity
    calc (D : ℝ) ^ nb * n * ((N : ℝ) ^ D')⁻¹ * (N : ℝ)⁻¹ ≤ N * ((N : ℝ) ^ D')⁻¹ * (N : ℝ)⁻¹ := by
          gcongr
      _ = ((N : ℝ) ^ D')⁻¹ := by field_simp

/-- The bound of the further class in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law], for a list of factors with resolvent letters carrying
their own flags and a valid assignment, the sum over the labels `α, β` (one block) and `i, j`
(one block) and the block indices of `|E Π factors|` is at most `N^τ` times the bound of the
assignment at `Im m ≤ N^{-1/3+ε/2} 𝔯(k)^{1/3}`, `η = N^{-2/3+ε} 𝔯(k)^{-1/3}`, plus
`N^{-D'} ‖A‖²_HS`. -/
theorem pkg_fsharp_bound (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (F : List FFac)
    (g : FAsg) (hg : fvalid nb F g = true) (D' : ℝ) (hD' : 0 < D') :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
          ∑ ι : Fin nb → Fin D, ‖∫ h, (F.map (FFac.val e ι
            (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0) ≤
        (N : ℝ) ^ τ * ((fboundM F g).map fun m => m.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A)).sum + (N : ℝ) ^ (-D') * hsNorm A ^ 2 := by
  intro τ hτ
  have hg0 := hg
  obtain ⟨P, rfl, hgP, hP, hcap⟩ := FS_setup hg
  obtain ⟨rks, opt⟩ := g
  simp only at hgP hP hcap
  cases hgP
  obtain ⟨Kc, hKc0, hcr⟩ := FS_crude_list D hD δA εA ε hδA hεA hε hε' hε'' C nb rks P hP
  obtain ⟨Kf, -, hF⟩ := FS_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨N₁, hN₁⟩ := pkg_fsharp_good D hD δA εA ε hδA hεA hε hε' hε'' C nb _ _ hg0 (τ / 2)
    (by positivity) (Kc + 1) (by linarith)
  have hev1 : ∀ᶠ N : ℕ in atTop, (D : ℝ) ^ nb * (D : ℝ) ^ 4 ≤ N :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hcr.and (hF.and (hev1.and (hev2.and
    (Filter.eventually_ge_atTop (max N₁ 1))))))
  refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  obtain ⟨hC, hFN, h1, h2, hN1'⟩ := hN₀ N hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN1'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hsl : FS_Slots D δA εA ε C N μ A k e := ⟨hμ, hA, hk, hkN, hhs, he⟩
  obtain ⟨-, -, -, hz, hη, -⟩ := hFN μ A k e hsl
  have hz' : ∀ a, (e.z a).im ≠ 0 := fun a => by rw [hz a]; exact hη.ne'
  have hprob := hμ.prob
  set B := ((fboundM (P.map Prod.fst) ⟨rks, P.flatMap FS_os⟩).map fun m => m.evalR N
    ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
    (hsNorm A) (opNorm A)).sum with hBdef
  have hB : B = FS_ev D N k ε A ⟨((List.range 4).map fun l =>
      2 - (fuses (P.map Prod.fst) ⟨rks, P.flatMap FS_os⟩ l : ℤ)).sum, 0, 0, 0, 0⟩ *
      (P.map (FS_V (FS_ev D N k ε A))).prod :=
    FS_bound_eq (FS_ev D N k ε A) (FS_ev_mul ε A hN1 hk hkN) (FS_ev_one ε A) rks P
  have hV0 : 0 ≤ (P.map (FS_V (FS_ev D N k ε A))).prod := List.prod_nonneg fun t ht => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
    exact FS_V_nonneg _ (FS_ev_nonneg D N k ε A) q
  have hB0 : 0 ≤ B := by rw [hB]; exact mul_nonneg (FS_ev_nonneg D N k ε A _) hV0
  set S : (Idx D N → Idx D N → ℂ) → ℝ := fun h => ∑ κ : Fin 4 → Idx D N,
    (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then ∑ ι : Fin nb → Fin D,
      ‖((P.map Prod.fst).map (FFac.val e ι
        (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod‖ else 0) with hSdef
  have hS0 : ∀ h, 0 ≤ S h := fun h => Finset.sum_nonneg fun κ _ => by
    split_ifs
    · exact Finset.sum_nonneg fun ι _ => norm_nonneg _
    · exact le_rfl
  have hint : ∀ (ι : Fin nb → Fin D) (κ : Fin 4 → Idx D N), Integrable (fun h =>
      ((P.map Prod.fst).map (FFac.val e ι
        (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod) μ :=
    fun ι κ => fb_integrable C μ hμ e hz' ι _ _
  have hSint : Integrable S μ := by
    refine integrable_finsetSum _ fun κ _ => ?_
    split_ifs
    · exact integrable_finsetSum _ fun ι _ => (hint ι κ).norm
    · exact integrable_zero _ _ _
  -- the label sum of `‖E Π‖` is at most `E S`
  have hstep1 : ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
      ∑ ι : Fin nb → Fin D, ‖∫ h, ((P.map Prod.fst).map (FFac.val e ι
        (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0) ≤ ∫ h, S h ∂μ := by
    rw [hSdef, integral_finsetSum _ fun κ _ => ?_]
    · refine Finset.sum_le_sum fun κ _ => ?_
      split_ifs
      · rw [integral_finsetSum _ fun ι _ => (hint ι κ).norm]
        exact Finset.sum_le_sum fun ι _ => norm_integral_le_integral_norm _
      · simp
    · split_ifs
      · exact integrable_finsetSum _ fun ι _ => (hint ι κ).norm
      · exact integrable_zero _ _ _
  -- the bound at every Hermitian array
  have hpt : ∀ h, (Matrix.of h).IsHermitian → S h ≤ (N : ℝ) ^ (Kc + 1) * B := by
    intro h hh
    refine (FS_sum_le (by omega) hN1 e h P hP hcap ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) *
      rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε) (hsNorm A) (opNorm A) _
      fun ι => hC μ A k e hsl ι h hh).trans ?_
    rw [hB, Real.rpow_add hN0 Kc 1, Real.rpow_one]
    change _ * (_ * FS_ev D N k ε A _ * _) ≤ _
    have hL0 := FS_ev_nonneg D N k ε A ⟨((List.range 4).map fun l =>
      2 - (fuses (P.map Prod.fst) ⟨rks, P.flatMap FS_os⟩ l : ℤ)).sum, 0, 0, 0, 0⟩
    have hK0 : 0 ≤ (N : ℝ) ^ Kc := Real.rpow_nonneg hN0.le _
    calc (D : ℝ) ^ nb * ((D : ℝ) ^ 4 * FS_ev D N k ε A _ *
          ((N : ℝ) ^ Kc * (P.map (FS_V (FS_ev D N k ε A))).prod)) =
          ((D : ℝ) ^ nb * (D : ℝ) ^ 4) * ((N : ℝ) ^ Kc * (FS_ev D N k ε A _ *
            (P.map (FS_V (FS_ev D N k ε A))).prod)) := by ring
      _ ≤ N * ((N : ℝ) ^ Kc * (FS_ev D N k ε A _ * (P.map (FS_V (FS_ev D N k ε A))).prod)) := by
          gcongr
      _ = _ := by ring
  -- the expectation step
  set X : (Idx D N → Idx D N → ℂ) → ℂ := fun h =>
    ((if (Matrix.of h).IsHermitian then S h else 0 : ℝ) : ℂ) with hXdef
  have hXS : (fun h => ((S h : ℝ) : ℂ)) =ᵐ[μ] X := hμ.herm.mono fun h hh => by
    simp only [hXdef, if_pos hh]
  have hXint : Integrable X μ := hSint.ofReal.congr hXS
  have hXle : ∀ h, ‖X h‖ ≤ S h := fun h => by
    simp only [hXdef]
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS0 h)]
    · simpa using hS0 h
  have hexp := fb_expect μ X hXint ((N : ℝ) ^ (τ / 2) * B) ((N : ℝ) ^ (Kc + 1) * B)
    ((N : ℝ) ^ (-(Kc + 1))) (by positivity) (by positivity)
    (fun h => by
      simp only [hXdef]
      split_ifs with hh
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS0 h)]
        exact hpt h hh
      · simpa using mul_nonneg (Real.rpow_nonneg hN0.le _) hB0)
    ((measure_mono fun h hh => lt_of_lt_of_le hh (hXle h)).trans
      (hN₁ N (le_of_max_le_left hN1') μ hμ A hA k hk hkN hhs e he))
  have hIS : ∫ h, S h ∂μ ≤ ‖∫ h, X h ∂μ‖ := by
    rw [← integral_congr_ae hXS, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  have hfin : (N : ℝ) ^ (Kc + 1) * B * (N : ℝ) ^ (-(Kc + 1)) = B := by
    rw [mul_comm, ← mul_assoc, ← Real.rpow_add hN0]
    simp
  have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  have hτ2 : (N : ℝ) ^ (τ / 2) * B + B ≤ (N : ℝ) ^ τ * B := by
    rw [hsplit]
    have ht : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by nlinarith
    calc (N : ℝ) ^ (τ / 2) * B + B = ((N : ℝ) ^ (τ / 2) + 1) * B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ht hB0
  have hD0 : 0 ≤ (N : ℝ) ^ (-D') * hsNorm A ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (sq_nonneg _)
  calc _ ≤ ∫ h, S h ∂μ := hstep1
    _ ≤ ‖∫ h, X h ∂μ‖ := hIS
    _ ≤ (N : ℝ) ^ (τ / 2) * B + (N : ℝ) ^ (Kc + 1) * B * (N : ℝ) ^ (-(Kc + 1)) := hexp
    _ ≤ (N : ℝ) ^ τ * B := by rw [hfin]; exact hτ2
    _ ≤ _ := le_add_of_nonneg_right hD0

end RBMTransitionEdge

end
