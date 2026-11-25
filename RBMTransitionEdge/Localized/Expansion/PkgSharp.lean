module

public import RBMTransitionEdge.Localized.Expansion.DetLoop
public import RBMTransitionEdge.Localized.Expansion.FactorBound
public import RBMTransitionEdge.Localized.Expansion.IndexCS
public import RBMTransitionEdge.Localized.Expansion.Pairing
public import RBMTransitionEdge.Localized.Expansion.PkgColl
public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.LocalLaw.MultiRes
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.Det.Regular
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.LocalLaw.MultiRes
import all RBMTransitionEdge.Localized.Expansion.PkgEval
import all RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.Det.Regular
import all RBMTransitionEdge.Localized.Expansion.Pairing
import all RBMTransitionEdge.Localized.Expansion.PkgColl

@[expose] public section

/-!
# The sharp bound of a derivative structure of Lemma 5.5

The direct estimation (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1] in the proof of
Lemma 5.5 [claim_estimate_remainder_terms] for one derivative structure of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]: one factor per word or package, with
`Im m` per package, at the slots of Lemmas 5.2 and 5.4.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The kinds of factors of the bound (5.68) [bound_factors]–(5.78)
[concrete_bound_type_2_2_1]: a light weight; a loop or package without `Λ̃` with `r` resolvents;
a loop or package with one `Λ̃` and `r` resolvents; a loop with one `Λ̃` and no resolvent, with or
without the gain of (5.5) [regular_estimate_localized_eigenvector]; a package with both `Λ̃`, `a`
resolvents between them and `c` after the second; a paired letter `𝔐_a - 𝔐_a^*`. -/
inductive PkgFac
  | wt
  | free (r : ℕ)
  | lam1 (r : ℕ)
  | lam0 (g : Bool)
  | lam2 (a c : ℕ)
  | pair
  deriving DecidableEq

/-- `(Im m)^{1(r ≥ 2)} η^{1-r}`, the size of (A.53) [entprodG] for `r ≥ 1` resolvents. -/
def pkgPsi (η m : ℝ) (r : ℕ) : ℝ := (if 2 ≤ r then m else 1) / η ^ (r - 1)

/-- `1` for `a = 0`, and `(Im m)^{1/2} η^{1/2-a}` for `a ≥ 1`: the size of one side of a package
with both `Λ̃` in (5.74) [concrete_bound_type_1_2_3]. -/
def pkgHalf (η m : ℝ) (a : ℕ) : ℝ := if a = 0 then 1 else Real.sqrt (m / η) / η ^ (a - 1)

/-- The size of a factor, with `hs = ‖A‖_HS`. -/
def PkgFac.val (N : ℕ) (η m hs : ℝ) : PkgFac → ℝ
  | .wt => ((N : ℝ) * η)⁻¹
  | .free r => pkgPsi η m r
  | .lam1 r => (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs * pkgPsi η m r
  | .lam0 g => (if g then m else 1) * (hs ^ 2 / N)
  | .lam2 a c => hs ^ 2 / N * pkgHalf η m a * pkgHalf η m c
  | .pair => m

/-- The factor of one package. -/
def pkgSegFac (σ : List PkgLetter) : PkgFac :=
  match σ.countP PkgLetter.isLam with
  | 0 => .free (σ.countP PkgLetter.isRes)
  | 1 => .lam1 (σ.countP PkgLetter.isRes)
  | _ =>
    let t := (σ.dropWhile fun x => !x.isLam).drop 1
    .lam2 ((t.takeWhile fun x => !x.isLam).countP PkgLetter.isRes)
      (((t.dropWhile fun x => !x.isLam).drop 1).countP PkgLetter.isRes)

/-- The factors of one word: one per package and one per paired letter of a word with `Δ`; one
for a loop. -/
def pkgWordFac (pr : Fin 2 → Bool) (w : List PkgLetter) : List PkgFac :=
  if w.any PkgLetter.isEnt then
    (pkgSegs w).map pkgSegFac ++
      (w.filter fun x => match x with | .lw (.det a) => pr a | _ => false).map fun _ => .pair
  else
    match w.countP PkgLetter.isLam with
    | 0 => [.free (w.countP PkgLetter.isRes)]
    | 1 => if w.countP PkgLetter.isRes = 0 then [.lam0 (pkgGainLoop w)]
      else [.lam1 (w.countP PkgLetter.isRes)]
    | _ => [.lam2 0 (w.countP PkgLetter.isRes)]

/-- The factors of an expression of the class `𝓡`. -/
def PkgExpr.profile (R : PkgExpr) (pr : Fin 2 → Bool) : List PkgFac :=
  R.weights.map (fun _ => PkgFac.wt) ++ R.loops.flatMap (pkgWordFac pr)

/-- The bound of (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1] for one pair of labels:
`|c_𝓡| D^{nb}` times the product of the sizes of the factors. -/
def PkgExpr.sharpB (R : PkgExpr) (D N : ℕ) (η m hs : ℝ) (pr : Fin 2 → Bool) : ℝ :=
  |(R.cf : ℝ)| * (D : ℝ) ^ (R.dexp + R.nb) * (N : ℝ) ^ (-R.S) *
    ((R.profile pr).map (PkgFac.val N η m hs)).prod

/-- The paired letters `𝔐_a - 𝔐_a^*` lie only in words with a letter `Δ`, as in the pairing (P)
of (5.58) [eq:polar2] for case (ii) of the proof of Lemma 5.5 [claim_estimate_remainder_terms]. -/
def PkgExpr.pairIn (R : PkgExpr) (pr : Fin 2 → Bool) : Bool :=
  R.loops.all fun w => w.any PkgLetter.isEnt ||
    !(w.any fun x => match x with | .lw (.det a) => pr a | _ => false)

open private isEntP isResP isGoodP dent_spec pkgStart_wf wf_iff WfP segOK exists_first_ent
  findIdx_ent
  from RBMTransitionEdge.Localized.Expansion.PkgWords
open private PB_segs PB_segOK PB_segs_ent PB_segs_count PB_trace_ent PB_entry_ent PB_matL PB_toL
  PB_toL_eq
  PB_isL PB_isL_count from RBMTransitionEdge.Localized.Expansion.PkgBound
open private MultiRes_hs2 MultiRes_hs2_mul_left_le MultiRes_hs2_mul_right_le MultiRes_hsNorm_sq
  MultiRes_trace_mul_conjTranspose from RBMTransitionEdge.LocalLaw.MultiRes
open private PE_wm_lw PE_wm_append PE_wm_cons PE_wm_nil PE_lm PE_lm_lamt PE_lm_res PE_lm_det
  from RBMTransitionEdge.Localized.Expansion.PkgEval
open private Bd_weight Bd_G_eq Bd_G_norm Bd_opNorm_E Bd_ntr_le Bd_opNorm_nonneg
  Bd_opNorm_conjTranspose Bd_opNorm_one Bd_large Bd_lamc_herm Bd_avgSq_nonneg Bd_avgSq_le
  Bd_opNorm_sub Bd_prod_norm Bd_list_norm Bd_facts Bd_Cl Bd_zc Bd_eta
  from RBMTransitionEdge.Localized.Expansion.Bound
open private Rg_avgSq_lam from RBMTransitionEdge.Det.Regular
open private Pr_wm_congr from RBMTransitionEdge.Localized.Expansion.Pairing
open private pkgColl_free from RBMTransitionEdge.Localized.Expansion.PkgColl

/-! ## Products of resolvents and deterministic matrices -/

section Items

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A factor of a product of Lemma A.4 [lemma_necessary_estimates]: the resolvent of a slot, with
a flag for its adjoint, or a deterministic matrix. -/
private abbrev PS_It (ι : Type*) := (Fin 2 × Bool) ⊕ Matrix ι ι ℂ

/-- The matrix of a factor. -/
private def PS_it (G : Fin 2 → Matrix ι ι ℂ) : PS_It ι → Matrix ι ι ℂ
  | .inl t => if t.2 then (G t.1)ᴴ else G t.1
  | .inr B => B

/-- The product of a list of factors. -/
private def PS_v (G : Fin 2 → Matrix ι ι ℂ) (l : List (PS_It ι)) : Matrix ι ι ℂ :=
  (l.map (PS_it G)).prod

/-- The number of resolvent factors. -/
private def PS_nr (l : List (PS_It ι)) : ℕ := l.countP Sum.isLeft

/-- The adjoint of a factor. -/
private def PS_adj : PS_It ι → PS_It ι
  | .inl t => .inl (t.1, !t.2)
  | .inr B => .inr Bᴴ

private lemma PS_v_nil (G : Fin 2 → Matrix ι ι ℂ) : PS_v G [] = 1 := rfl

private lemma PS_v_append (G : Fin 2 → Matrix ι ι ℂ) (l₁ l₂ : List (PS_It ι)) :
    PS_v G (l₁ ++ l₂) = PS_v G l₁ * PS_v G l₂ := by
  simp [PS_v, List.map_append, List.prod_append]

omit [Fintype ι] [DecidableEq ι] in
private lemma PS_it_adj (G : Fin 2 → Matrix ι ι ℂ) (x : PS_It ι) :
    (PS_it G x)ᴴ = PS_it G (PS_adj x) := by
  rcases x with ⟨a, s⟩ | B
  · cases s <;> simp [PS_it, PS_adj]
  · rfl

/-- `(Π)^* = Π` of the adjoint factors in reverse order. -/
private lemma PS_v_adj (G : Fin 2 → Matrix ι ι ℂ) (l : List (PS_It ι)) :
    (PS_v G l)ᴴ = PS_v G (l.reverse.map PS_adj) := by
  induction l with
  | nil => simp [PS_v]
  | cons x l ih =>
    simp only [PS_v, List.map_cons, List.prod_cons, Matrix.conjTranspose_mul] at ih ⊢
    rw [ih, List.reverse_cons, List.map_append, List.map_append, List.prod_append,
      PS_it_adj]
    simp

omit [Fintype ι] [DecidableEq ι] in
private lemma PS_nr_adj (l : List (PS_It ι)) : PS_nr (l.reverse.map PS_adj) = PS_nr l := by
  unfold PS_nr
  rw [List.countP_map, List.countP_reverse]
  congr 1
  funext x
  rcases x with t | B <;> rfl

omit [Fintype ι] [DecidableEq ι] in
private lemma PS_nr_append (l₁ l₂ : List (PS_It ι)) : PS_nr (l₁ ++ l₂) = PS_nr l₁ + PS_nr l₂ := by
  simp [PS_nr, List.countP_append]

private lemma PS_adj_det (l : List (PS_It ι)) (K : ℝ)
    (h : ∀ B, Sum.inr B ∈ l → opNorm B ≤ K) : ∀ B, Sum.inr B ∈ l.reverse.map PS_adj →
      opNorm B ≤ K := by
  intro B hB
  obtain ⟨x, hx, hxB⟩ := List.mem_map.1 hB
  rcases x with t | B'
  · simp [PS_adj] at hxB
  · simp only [PS_adj, Sum.inr.injEq] at hxB
    subst hxB
    rw [Bd_opNorm_conjTranspose]
    exact h B' (List.mem_reverse.1 hx)

/-- A list of factors is a product `B₀ G B₁ ⋯ G B_l` of Lemma A.4 [lemma_necessary_estimates],
with `‖B_j‖ ≤ K^{len}` when every deterministic factor has norm `≤ K`, `K ≥ 1`. -/
private lemma PS_resWord (K : ℝ) (hK : 1 ≤ K) :
    ∀ l : List (PS_It ι), (∀ B, Sum.inr B ∈ l → opNorm B ≤ K) →
      ∃ n, ∃ w : Fin n → Fin 2 × Bool, ∃ B : Fin (n + 1) → Matrix ι ι ℂ, n = PS_nr l ∧
        (∀ G : Fin 2 → Matrix ι ι ℂ, PS_v G l = resWord G w B) ∧
        ∀ j, opNorm (B j) ≤ K ^ l.length
  | [], _ => ⟨0, Fin.elim0, fun _ => 1, rfl, fun G => by simp [PS_v, resWord], fun _ => by
      simpa using Bd_opNorm_one⟩
  | .inr X :: l, hB => by
    obtain ⟨n, w, B, hn, he, hb⟩ := PS_resWord K hK l fun B hB' => hB B (by simp [hB'])
    refine ⟨n, w, Fin.cons (X * B 0) fun j => B j.succ, by simpa [PS_nr] using hn, ?_, ?_⟩
    · intro G
      have he' := he G
      simp only [PS_v, List.map_cons, List.prod_cons] at he' ⊢
      rw [he']
      simp [resWord, PS_it, Matrix.mul_assoc]
    · intro j
      have hX := hB X (by simp)
      have hK0 : (0 : ℝ) ≤ K := by linarith
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_zero, List.length_cons, pow_succ']
        exact (opNorm_mul_le _ _).trans (mul_le_mul hX (hb 0) (Bd_opNorm_nonneg _) hK0)
      · simp only [Fin.cons_succ, List.length_cons]
        exact (hb k.succ).trans (pow_le_pow_right₀ hK (Nat.le_succ _))
  | .inl t :: l, hB => by
    obtain ⟨n, w, B, hn, he, hb⟩ := PS_resWord K hK l fun B hB' => hB B (by simp [hB'])
    refine ⟨n + 1, Fin.cons t w, Fin.cons 1 B, by simp [PS_nr, hn, List.countP_cons], ?_, ?_⟩
    · intro G
      have he' := he G
      simp only [PS_v, List.map_cons, List.prod_cons] at he' ⊢
      rw [he']
      simp only [resWord, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons, one_mul,
        Matrix.mul_assoc]
      rfl
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_zero]
        exact Bd_opNorm_one.trans (one_le_pow₀ hK)
      · simp only [Fin.cons_succ, List.length_cons]
        exact (hb k).trans (pow_le_pow_right₀ hK (Nat.le_succ _))

/-- The factors of a word of loop letters, for the flags `s`, limits `M`, projections `E` and
`Λ̃ = L`. -/
private def PS_ofL (s : Fin 2 → Bool) (M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) : LoopLetter → PS_It ι
  | .res a => .inl (a, s a)
  | .det a => .inr (M a)
  | .proj y => .inr (E y)
  | .lamt _ => .inr L

omit [Fintype ι] [DecidableEq ι] in
private lemma PS_ofL_nr (s : Fin 2 → Bool) (M : Fin 2 → Matrix ι ι ℂ) (E : ℕ → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (w : List LoopLetter) :
    PS_nr (w.map (PS_ofL s M E L)) =
      w.countP fun x => match x with | .res _ => true | _ => false := by
  unfold PS_nr
  rw [List.countP_map]
  congr 1
  funext x
  cases x <;> rfl

end Items

/-! ## The factor bounds on lists of factors -/

/-- The hypotheses of Lemma A.4 [lemma_necessary_estimates] on the slots of `e`, with `|c_a| ≤ 1`
and `|δ| ≤ K ⟨Λ²⟩`. -/
private def PS_Adm (D N : ℕ) (δA τ c₀ K : ℝ) (e : LoopEnv D N) : Prop :=
  opNorm e.A ≤ (N : ℝ) ^ (-δA) ∧ 2 * 1 * opNorm e.A ≤ 1 / 10 ∧ (∀ a, |e.c a| ≤ 1) ∧
    (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
      c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) ∧
    |e.δ| ≤ K * avgSq (lam D N e.A)

/-- The resolvents `(h + c_a Λ - z_a)⁻¹` of the slots. -/
private abbrev PS_Gr {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) (a : Fin 2) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a)

/-- `(Im m)^{1(l ≥ 2)} η^{1-l}` of (A.53) [entprodG] at the slots. -/
private abbrev PS_b {D N : ℕ} (e : LoopEnv D N) (l : ℕ) : ℝ :=
  bndA4 (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) (fun a => (e.z a).im) l

/-- (A.53) [entprodG] by `fb_word` for a list of factors. -/
private lemma PS_fbw (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ K₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hK₀ : 1 ≤ K₀) (C : ℕ → ℝ) (Lm r : ℕ) (hr : 1 ≤ r) (τ' : ℝ) (hτ' : 0 < τ')
    (D' : ℝ) (hD' : 0 < D') :
    ∀ᶠ N in atTop, ∀ μ, LLClass D N C 1 μ → ∀ K, ∀ e : LoopEnv D N, PS_Adm D N δA τ c₀ K e →
      ∀ l : List (PS_It (Idx D N)), PS_nr l = r → l.length ≤ Lm →
        (∀ B, Sum.inr B ∈ l → opNorm B ≤ K₀) →
        μ {h | (N : ℝ) ^ τ' * ((K₀ ^ Lm) ^ (r + 1) * PS_b e r) <
            ‖ntr (PS_v (PS_Gr e h) l)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
          μ {h | (N : ℝ) ^ τ' * ((K₀ ^ Lm) ^ (r + 1) * PS_b e r) <
            ‖star u ⬝ᵥ (PS_v (PS_Gr e h) l *ᵥ v)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := fb_word D hD δA τ c₀ 1 (K₀ ^ Lm) hδA hτ hc₀ le_rfl C r hr τ' hτ' D' hD'
  refine Filter.eventually_atTop.2 ⟨N₀, fun N hN μ hμ K e he l hl hlen hdet => ?_⟩
  obtain ⟨hA, hA2, hc, hz, -⟩ := he
  obtain ⟨n, w, B, hn, hv, hB⟩ := PS_resWord K₀ hK₀ l hdet
  subst hn
  subst hl
  obtain ⟨h1, h2⟩ := hN₀ N hN μ hμ e hA hA2 hc hz w B
    (fun j => (hB j).trans (pow_le_pow_right₀ hK₀ hlen))
  simp only [hv]
  exact ⟨h1, h2⟩

/-- (A.54) [one_loop_estimate] by `fb_lam_loop` for a list of factors. -/
private lemma PS_fbl (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ K₀ Kδ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hK₀ : 1 ≤ K₀) (C : ℕ → ℝ) (Lm r : ℕ) (hr : 1 ≤ r) (τ' : ℝ) (hτ' : 0 < τ')
    (D' : ℝ) (hD' : 0 < D') :
    ∀ᶠ N in atTop, ∀ μ, LLClass D N C 1 μ → ∀ e : LoopEnv D N, PS_Adm D N δA τ c₀ Kδ e →
      ∀ l : List (PS_It (Idx D N)), PS_nr l = r → l.length ≤ Lm →
        (∀ B, Sum.inr B ∈ l → opNorm B ≤ K₀) →
        μ {h | (N : ℝ) ^ τ' * (max (K₀ ^ Lm) Kδ ^ (r + 1) * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
            hsNorm (lam D N e.A) * PS_b e r)) < ‖ntr (PS_v (PS_Gr e h) l * e.Lt)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := fb_lam_loop D hD δA τ c₀ 1 (max (K₀ ^ Lm) Kδ) hδA hτ hc₀ le_rfl C r hr τ'
    hτ' D' hD'
  refine Filter.eventually_atTop.2 ⟨N₀, fun N hN μ hμ e he l hl hlen hdet => ?_⟩
  obtain ⟨hA, hA2, hc, hz, hδ⟩ := he
  obtain ⟨n, w, B, hn, hv, hB⟩ := PS_resWord K₀ hK₀ l hdet
  subst hn
  subst hl
  have h1 := hN₀ N hN μ hμ e hA hA2 hc hz
    (hδ.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Bd_avgSq_nonneg _ (lam_isHermitian D N _)))) w B
    (fun j => ((hB j).trans (pow_le_pow_right₀ hK₀ hlen)).trans (le_max_left _ _))
  simp only [hv]
  exact h1

/-- (A.55) [two_loop_estimate] by `fb_lam_two` for two lists of factors. -/
private lemma PS_fbt (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ K₀ Kδ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hK₀ : 1 ≤ K₀) (C : ℕ → ℝ) (Lm r₁ r₂ : ℕ) (hr : 1 ≤ r₁ + r₂) (τ' : ℝ)
    (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∀ᶠ N in atTop, ∀ μ, LLClass D N C 1 μ → ∀ e : LoopEnv D N, PS_Adm D N δA τ c₀ Kδ e →
      ∀ l₁ l₂ : List (PS_It (Idx D N)), PS_nr l₁ = r₁ → PS_nr l₂ = r₂ → l₁.length ≤ Lm →
        l₂.length ≤ Lm → (∀ B, Sum.inr B ∈ l₁ → opNorm B ≤ K₀) →
        (∀ B, Sum.inr B ∈ l₂ → opNorm B ≤ K₀) →
        μ {h | (N : ℝ) ^ τ' * (max (K₀ ^ Lm) Kδ ^ (r₁ + r₂ + 2) *
            (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (r₁ + r₂))) <
          ‖ntr (PS_v (PS_Gr e h) l₁ * e.Lt * PS_v (PS_Gr e h) l₂ * e.Lt)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := fb_lam_two D hD δA τ c₀ 1 (max (K₀ ^ Lm) Kδ) hδA hτ hc₀ le_rfl C r₁ r₂ hr
    τ' hτ' D' hD'
  refine Filter.eventually_atTop.2 ⟨N₀, fun N hN μ hμ e he l₁ l₂ hl₁ hl₂ hlen₁ hlen₂ hd₁ hd₂ =>
    ?_⟩
  obtain ⟨hA, hA2, hc, hz, hδ⟩ := he
  obtain ⟨n₁, w₁, B₁, hn₁, hv₁, hB₁⟩ := PS_resWord K₀ hK₀ l₁ hd₁
  obtain ⟨n₂, w₂, B₂, hn₂, hv₂, hB₂⟩ := PS_resWord K₀ hK₀ l₂ hd₂
  subst hn₁ hn₂
  subst hl₁ hl₂
  have h1 := hN₀ N hN μ hμ e hA hA2 hc hz
    (hδ.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Bd_avgSq_nonneg _ (lam_isHermitian D N _)))) w₁ w₂ B₁ B₂
    (fun j => ((hB₁ j).trans (pow_le_pow_right₀ hK₀ hlen₁)).trans (le_max_left _ _))
    (fun j => ((hB₂ j).trans (pow_le_pow_right₀ hK₀ hlen₂)).trans (le_max_left _ _))
  simp only [hv₁, hv₂]
  exact h1

/-! ## The sizes of the factors -/

private lemma PS_psi_nonneg {η m : ℝ} (hη : 0 < η) (hm : 0 ≤ m) (r : ℕ) : 0 ≤ pkgPsi η m r := by
  unfold pkgPsi
  split_ifs
  · exact div_nonneg hm (by positivity)
  · positivity

private lemma PS_half_nonneg {η : ℝ} (m : ℝ) (hη : 0 < η) (a : ℕ) :
    0 ≤ pkgHalf η m a := by
  unfold pkgHalf
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hη.le _)

private lemma PS_val_nonneg (N : ℕ) {η m hs : ℝ} (hη : 0 < η) (hm : 0 ≤ m) (hs0 : 0 ≤ hs) :
    ∀ f : PkgFac, 0 ≤ f.val N η m hs
  | .wt => by simp only [PkgFac.val]; positivity
  | .free r => PS_psi_nonneg hη hm r
  | .lam1 r => mul_nonneg (by positivity) (PS_psi_nonneg hη hm r)
  | .lam0 g => by
      simp only [PkgFac.val]
      split_ifs
      · exact mul_nonneg hm (by positivity)
      · positivity
  | .lam2 a c => mul_nonneg (mul_nonneg (by positivity) (PS_half_nonneg m hη a))
      (PS_half_nonneg m hη c)
  | .pair => hm

/-- `(Im m)^{1(l ≥ 2)} η^{1-l}` with the largest `Im m_a` and `η = η_a` is at most `K` times the
same with `Im m` when `Im m_a ≤ K Im m`. -/
private lemma PS_bnd {imm eta : Fin 2 → ℝ} {η m K : ℝ} (hη : 0 < η) (heta : ∀ a, eta a = η)
    (hK : 1 ≤ K) (him : ∀ a, imm a ≤ K * m) (l : ℕ) :
    bndA4 imm eta l ≤ K * pkgPsi η m l := by
  have hinf : (⨅ a, eta a) = η := by simp [heta]
  have hsup : (⨆ a, imm a) ≤ K * m := ciSup_le him
  unfold bndA4 pkgPsi
  rw [hinf]
  have hp : 0 < η ^ (l - 1) := pow_pos hη _
  split_ifs with h
  · rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hsup hp.le
  · rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hp.le

private lemma PS_psi_sq {η m : ℝ} (hη : 0 < η) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    pkgPsi η m (2 * p) * pkgPsi η m (2 * q) = pkgPsi η m (p + q) ^ 2 := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  unfold pkgPsi
  have h1 : 2 ≤ 2 * (p + 1) := by omega
  have h2 : 2 ≤ 2 * (q + 1) := by omega
  have h3 : 2 ≤ p + 1 + (q + 1) := by omega
  simp only [h1, h2, h3, ↓reduceIte]
  have e1 : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
  have e2 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have e3 : p + 1 + (q + 1) - 1 = p + q + 1 := by omega
  rw [e1, e2, e3]
  have hη0 := hη.ne'
  field_simp
  ring

private lemma PS_half_sq {η m : ℝ} (hη : 0 < η) (hm : 0 ≤ m) {c : ℕ} (hc : 1 ≤ c) :
    pkgPsi η m (2 * c) = pkgHalf η m c ^ 2 := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  unfold pkgPsi pkgHalf
  have h1 : 2 ≤ 2 * (c + 1) := by omega
  have h2 : c + 1 ≠ 0 := by omega
  simp only [h1, h2, ↓reduceIte]
  rw [div_pow, Real.sq_sqrt (div_nonneg hm hη.le)]
  have e1 : 2 * (c + 1) - 1 = 2 * c + 1 := by omega
  rw [e1, Nat.add_sub_cancel]
  have hη0 := hη.ne'
  field_simp
  ring

private lemma PS_psi_low {η m : ℝ} (hη : 0 < η) (hm1 : m ≤ 1) (r : ℕ) :
    m / η ^ (r - 1) ≤ pkgPsi η m r := by
  unfold pkgPsi
  split_ifs
  · exact le_rfl
  · exact div_le_div_of_nonneg_right hm1 (by positivity)

private lemma PS_half_low {η m : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (a : ℕ) : m * η / η ^ a ≤ pkgHalf η m a := by
  unfold pkgHalf
  split_ifs with ha
  · subst ha
    simp only [pow_zero, div_one]
    nlinarith
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h1 : m ≤ Real.sqrt (m / η) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hη]
      nlinarith
    have e : m * η / η ^ (a + 1) = m / η ^ a := by
      have := hη.ne'
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right h1 (by positivity)

/-! ## Bounds with factors in `ℓ²` over the labels -/

section L2

variable {D N : ℕ}

/-- Functions in `ℓ²` with their bounds: `φ ≥ 0`, `Σ φ² ≤ T²`, `T ≥ 0`. -/
private def PS_L2 (L : List ((Idx D N → ℝ) × ℝ)) : Prop :=
  ∀ t ∈ L, (∀ x, 0 ≤ t.1 x) ∧ ∑ x, t.1 x ^ 2 ≤ t.2 ^ 2 ∧ 0 ≤ t.2

/-- `F(i, j) ≤ c Π 2(φ(i) + φ(j))` over at most `k` functions `φ` in `ℓ²`, with `c Π T ≤ V N^{k/2}`:
the form of the bounds (5.68) [bound_factors]–(5.71) [Cauchy_example_2] before the label sums. -/
private def PS_FC (F : Idx D N → Idx D N → ℝ) (V : ℝ) (k : ℕ) : Prop :=
  ∃ c : ℝ, ∃ L : List ((Idx D N → ℝ) × ℝ), L.length ≤ k ∧ PS_L2 L ∧ 0 ≤ c ∧
    (∀ i j, F i j ≤ c * (L.map fun t => 2 * (t.1 i + t.1 j)).prod) ∧
    c * (L.map Prod.snd).prod ≤ V * Real.sqrt N ^ L.length

private lemma PS_L2_prod_nonneg (L : List ((Idx D N → ℝ) × ℝ)) (hL : PS_L2 L) (i j : Idx D N) :
    0 ≤ (L.map fun t => 2 * (t.1 i + t.1 j)).prod := by
  refine List.prod_nonneg fun y hy => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
  have := (hL t ht).1
  linarith [this i, this j]

private lemma PS_L2_prodT_nonneg (L : List ((Idx D N → ℝ) × ℝ)) (hL : PS_L2 L) :
    0 ≤ (L.map Prod.snd).prod := by
  refine List.prod_nonneg fun y hy => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
  exact (hL t ht).2.2

private lemma PS_FC_const (F : Idx D N → Idx D N → ℝ) (V : ℝ) (k : ℕ) (hV : 0 ≤ V)
    (hF : ∀ i j, F i j ≤ V) : PS_FC F V k :=
  ⟨V, [], Nat.zero_le _, fun t ht => by simp at ht, hV, fun i j => by simpa using hF i j,
    by simp⟩

private lemma PS_FC_mono {F F' : Idx D N → Idx D N → ℝ} {V V' : ℝ} {k k' : ℕ}
    (h : PS_FC F V k) (hF : ∀ i j, F' i j ≤ F i j) (hV : V ≤ V') (hk : k ≤ k') :
    PS_FC F' V' k' := by
  obtain ⟨c, L, hl, hL, hc, hb, hv⟩ := h
  exact ⟨c, L, hl.trans hk, hL, hc, fun i j => (hF i j).trans (hb i j),
    hv.trans (mul_le_mul_of_nonneg_right hV (by positivity))⟩

private lemma PS_FC_mul {F G : Idx D N → Idx D N → ℝ} {V W : ℝ} {k k' : ℕ}
    (hG0 : ∀ i j, 0 ≤ G i j) (hF : PS_FC F V k) (hG : PS_FC G W k') :
    PS_FC (fun i j => F i j * G i j) (V * W) (k + k') := by
  obtain ⟨c, L, hl, hL, hc, hb, hv⟩ := hF
  obtain ⟨c', L', hl', hL', hc', hb', hv'⟩ := hG
  refine ⟨c * c', L ++ L', by simp; omega, fun t ht => ?_, mul_nonneg hc hc', fun i j => ?_, ?_⟩
  · rcases List.mem_append.1 ht with ht | ht
    · exact hL t ht
    · exact hL' t ht
  · rw [List.map_append, List.prod_append]
    have e : c * c' * ((L.map fun t => 2 * (t.1 i + t.1 j)).prod *
        (L'.map fun t => 2 * (t.1 i + t.1 j)).prod) =
        (c * (L.map fun t => 2 * (t.1 i + t.1 j)).prod) *
          (c' * (L'.map fun t => 2 * (t.1 i + t.1 j)).prod) := by ring
    rw [e]
    exact mul_le_mul (hb i j) (hb' i j) (hG0 i j)
      (mul_nonneg hc (PS_L2_prod_nonneg L hL i j))
  · rw [List.map_append, List.prod_append, List.length_append, pow_add]
    have e : c * c' * ((L.map Prod.snd).prod * (L'.map Prod.snd).prod) =
        (c * (L.map Prod.snd).prod) * (c' * (L'.map Prod.snd).prod) := by ring
    rw [e]
    have h0 : 0 ≤ c * (L.map Prod.snd).prod := mul_nonneg hc (PS_L2_prodT_nonneg L hL)
    have h0' : 0 ≤ c' * (L'.map Prod.snd).prod := mul_nonneg hc' (PS_L2_prodT_nonneg L' hL')
    calc c * (L.map Prod.snd).prod * (c' * (L'.map Prod.snd).prod)
        ≤ (V * Real.sqrt N ^ L.length) * (W * Real.sqrt N ^ L'.length) :=
          mul_le_mul hv hv' h0' (h0.trans hv)
      _ = V * W * (Real.sqrt N ^ L.length * Real.sqrt N ^ L'.length) := by ring

/-- Products of bounds of the form `PS_FC` over a list. -/
private lemma PS_FC_prod {α : Type*} (F : α → Idx D N → Idx D N → ℝ) (V : α → ℝ) (k : α → ℕ) :
    ∀ l : List α, (∀ x ∈ l, ∀ i j, 0 ≤ F x i j) → (∀ x ∈ l, PS_FC (F x) (V x) (k x)) →
      PS_FC (fun i j => (l.map fun x => F x i j).prod) (l.map V).prod (l.map k).sum
  | [], _, _ => PS_FC_const _ 1 0 zero_le_one fun i j => by simp
  | x :: l, h0, h => by
    have ih := PS_FC_prod F V k l (fun y hy => h0 y (by simp [hy]))
      (fun y hy => h y (by simp [hy]))
    have := PS_FC_mul (fun i j => List.prod_nonneg fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact h0 z (by simp [hz]) i j) (h x (by simp)) ih
    simpa using this

/-- The label `i` or `j`. -/
private def PS_sel (s : Bool) (i j : Idx D N) : Idx D N := if s then i else j

/-- `Σ_j 1(i, j in one block) = N`. -/
private lemma PS_blk_card (i : Idx D N) :
    ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = N := by
  rw [Fintype.sum_prod_type]
  have e : ∀ b : Fin D, ∑ y : Fin N, (if i.1 = (b, y).1 then (1 : ℝ) else 0) =
      if i.1 = b then (N : ℝ) else 0 := by
    intro b
    split_ifs <;> simp_all
  simp only [e, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- `Σ_{i,j in one block} f(i)² = N Σ f²` and the same with `f(j)`. -/
private lemma PS_blk_sq (f : Idx D N → ℝ) (s : Bool) :
    ∑ i, ∑ j, (if i.1 = j.1 then f (PS_sel s i j) else 0) ^ 2 = N * ∑ x, f x ^ 2 := by
  have e : ∀ i j : Idx D N, (if i.1 = j.1 then f (PS_sel s i j) else 0) ^ 2 =
      (if i.1 = j.1 then (1 : ℝ) else 0) * f (PS_sel s i j) ^ 2 := by
    intro i j
    split_ifs <;> simp
  simp only [e]
  cases s
  · rw [Finset.sum_comm]
    simp only [PS_sel, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = N := by
      rw [← PS_blk_card j]
      exact Finset.sum_congr rfl fun i _ => by simp [eq_comm]
    rw [this]
  · simp only [PS_sel, ↓reduceIte]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, PS_blk_card i]

/-- The label Cauchy–Schwarz step of (5.70) [Cauchy_example_1] over the pairs in one block, by
`idxcs_pair`. -/
private lemma PS_blk_pair (f g : Idx D N → ℝ) (T T' : ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hT : ∑ x, f x ^ 2 ≤ T ^ 2) (hT' : ∑ x, g x ^ 2 ≤ T' ^ 2) (hT0 : 0 ≤ T) (hT0' : 0 ≤ T')
    (s s' : Bool) :
    ∑ i, ∑ j, (if i.1 = j.1 then f (PS_sel s i j) * g (PS_sel s' i j) else 0) ≤
      N * (T * T') := by
  have h := idxcs_pair (fun i j => if i.1 = j.1 then f (PS_sel s i j) else 0)
    (fun i j => if i.1 = j.1 then g (PS_sel s' i j) else 0) (fun _ _ => 1) 1
    (fun i j => by split_ifs <;> simp [hf]) (fun i j => by split_ifs <;> simp [hg])
    (fun _ _ => ⟨zero_le_one, le_rfl⟩)
  have e : ∀ i j : Idx D N, (if i.1 = j.1 then f (PS_sel s i j) else 0) *
      (if i.1 = j.1 then g (PS_sel s' i j) else 0) * 1 =
      if i.1 = j.1 then f (PS_sel s i j) * g (PS_sel s' i j) else 0 := by
    intro i j; split_ifs <;> simp
  simp only [e, PS_blk_sq, one_mul] at h
  refine h.trans ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : Real.sqrt (N * ∑ x, f x ^ 2) ≤ Real.sqrt N * T := by
    rw [Real.sqrt_mul hN]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hT |>.trans (Real.sqrt_sq hT0).le)
      (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (N * ∑ x, g x ^ 2) ≤ Real.sqrt N * T' := by
    rw [Real.sqrt_mul hN]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hT' |>.trans (Real.sqrt_sq hT0').le)
      (Real.sqrt_nonneg _)
  calc Real.sqrt (N * ∑ x, f x ^ 2) * Real.sqrt (N * ∑ x, g x ^ 2)
      ≤ (Real.sqrt N * T) * (Real.sqrt N * T') :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt N * Real.sqrt N) * (T * T') := by ring
    _ = N * (T * T') := by rw [Real.mul_self_sqrt hN]

/-- The label sum over the pairs in one block of a bound of the form `PS_FC` with at most two
functions in `ℓ²`: `≤ 16 D N² V`, as in (5.68) [bound_factors]–(5.71) [Cauchy_example_2]. -/
private lemma PS_FC_sum (hD : 1 ≤ D) {F : Idx D N → Idx D N → ℝ} {V : ℝ} (h : PS_FC F V 2) :
    ∑ i, ∑ j, (if i.1 = j.1 then F i j else 0) ≤ 16 * D * N ^ 2 * V := by
  obtain ⟨c, L, hl, hL, hc, hb, hv⟩ := h
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hsN := Real.sqrt_nonneg (N : ℝ)
  have hstep : ∑ i, ∑ j, (if i.1 = j.1 then F i j else 0) ≤
      c * ∑ i, ∑ j, (if i.1 = j.1 then (L.map fun t => 2 * (t.1 i + t.1 j)).prod else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact hb i j
    · simp
  refine hstep.trans ?_
  match L, hl, hL, hv with
  | [], _, _, hv =>
    simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, mul_one] at hv ⊢
    have e : ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = D * N * N := by
      simp only [PS_blk_card, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    have hV : 0 ≤ V := hc.trans hv
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D) hN) hN]
  | [t], _, hL, hv =>
    obtain ⟨ht0, ht2, hT0⟩ := hL t (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, zero_add, pow_one] at hv ⊢
    have e : ∀ i j : Idx D N, (if i.1 = j.1 then 2 * (t.1 i + t.1 j) else 0) =
        2 * (if i.1 = j.1 then t.1 (PS_sel true i j) * (fun _ => (1 : ℝ)) i else 0) +
        2 * (if i.1 = j.1 then t.1 (PS_sel false i j) * (fun _ => (1 : ℝ)) i else 0) := by
      intro i j
      simp only [PS_sel, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := PS_blk_pair t.1 (fun _ => (1 : ℝ)) t.2 (Real.sqrt (D * N)) ht0
      (fun _ => zero_le_one) ht2 (by
        rw [Real.sq_sqrt (by positivity)]
        simp [Fintype.card_prod]) hT0 (Real.sqrt_nonneg _) true true
    have h2 := PS_blk_pair t.1 (fun _ => (1 : ℝ)) t.2 (Real.sqrt (D * N)) ht0
      (fun _ => zero_le_one) ht2 (by
        rw [Real.sq_sqrt (by positivity)]
        simp [Fintype.card_prod]) hT0 (Real.sqrt_nonneg _) false true
    have hsD : Real.sqrt (D * N) = Real.sqrt D * Real.sqrt N := Real.sqrt_mul (by linarith) _
    have hsDD : Real.sqrt D ≤ D := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
    have hV : 0 ≤ V * Real.sqrt N := (mul_nonneg hc hT0).trans hv
    calc c * (2 * (∑ i, ∑ j, (if i.1 = j.1 then t.1 (PS_sel true i j) *
            (fun _ => (1 : ℝ)) i else 0)) + 2 * ∑ i, ∑ j, (if i.1 = j.1 then
            t.1 (PS_sel false i j) * (fun _ => (1 : ℝ)) i else 0))
        ≤ c * (2 * (N * (t.2 * Real.sqrt (D * N))) + 2 * (N * (t.2 * Real.sqrt (D * N)))) := by
          gcongr
      _ = 4 * N * Real.sqrt D * (c * t.2 * Real.sqrt N) := by rw [hsD]; ring
      _ ≤ 4 * N * Real.sqrt D * (V * Real.sqrt N * Real.sqrt N) := by gcongr
      _ = 4 * Real.sqrt D * N ^ 2 * V := by rw [mul_assoc V, hNN]; ring
      _ ≤ 16 * D * N ^ 2 * V := by
          have hVN : 0 ≤ V * N ^ 2 := by
            have e2 : (V * Real.sqrt N) * (Real.sqrt N * N) = V * N ^ 2 := by
              rw [show V * Real.sqrt N * (Real.sqrt N * N) =
                V * (Real.sqrt N * Real.sqrt N) * N by ring, hNN]
              ring
            rw [← e2]
            exact mul_nonneg hV (mul_nonneg hsN hN)
          have hD4 : 4 * Real.sqrt D ≤ 16 * D := by linarith
          nlinarith
  | [t, t'], _, hL, hv =>
    obtain ⟨ht0, ht2, hT0⟩ := hL t (by simp)
    obtain ⟨ht0', ht2', hT0'⟩ := hL t' (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, zero_add] at hv ⊢
    have e : ∀ i j : Idx D N, (if i.1 = j.1 then 2 * (t.1 i + t.1 j) *
        (2 * (t'.1 i + t'.1 j)) else 0) =
        4 * (if i.1 = j.1 then t.1 (PS_sel true i j) * t'.1 (PS_sel true i j) else 0) +
        4 * (if i.1 = j.1 then t.1 (PS_sel true i j) * t'.1 (PS_sel false i j)
          else 0) +
        4 * (if i.1 = j.1 then t.1 (PS_sel false i j) * t'.1 (PS_sel true i j)
          else 0) +
        4 * (if i.1 = j.1 then t.1 (PS_sel false i j) * t'.1 (PS_sel false i j)
          else 0) := by
      intro i j
      simp only [PS_sel, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hp := fun s s' => PS_blk_pair t.1 t'.1 t.2 t'.2 ht0 ht0' ht2 ht2' hT0 hT0' s s'
    have hNN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
    calc c * (4 * (∑ i, ∑ j, (if i.1 = j.1 then t.1 (PS_sel true i j) *
            t'.1 (PS_sel true i j) else 0)) +
          4 * (∑ i, ∑ j, (if i.1 = j.1 then t.1 (PS_sel true i j) *
            t'.1 (PS_sel false i j) else 0)) +
          4 * (∑ i, ∑ j, (if i.1 = j.1 then t.1 (PS_sel false i j) *
            t'.1 (PS_sel true i j) else 0)) +
          4 * ∑ i, ∑ j, (if i.1 = j.1 then t.1 (PS_sel false i j) *
            t'.1 (PS_sel false i j) else 0))
        ≤ c * (4 * (N * (t.2 * t'.2)) + 4 * (N * (t.2 * t'.2)) + 4 * (N * (t.2 * t'.2)) +
            4 * (N * (t.2 * t'.2))) := by
          gcongr
          · exact hp true true
          · exact hp true false
          · exact hp false true
          · exact hp false false
      _ = 16 * N * (c * (t.2 * t'.2)) := by ring
      _ ≤ 16 * N * (V * Real.sqrt N ^ 2) := by gcongr
      _ = 16 * N ^ 2 * V := by rw [hNN]; ring
      _ ≤ 16 * D * N ^ 2 * V := by
          have hV0 : 0 ≤ V * N := by
            rw [← hNN]; exact (mul_nonneg hc (mul_nonneg hT0 hT0')).trans hv
          nlinarith [mul_nonneg hN hV0]
  | _ :: _ :: _ :: _, hl, _, _ => simp at hl

end L2

/-! ## Bad events -/

/-- A union of bad events, one for each member of a list. -/
private lemma PS_bad_list {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : α → Ω → Prop)
    (b : α → ℝ) (hb : ∀ x, 0 ≤ b x) : ∀ l : List α,
      (∀ x ∈ l, ∃ s : Set Ω, μ s ≤ ENNReal.ofReal (b x) ∧ ∀ ω ∉ s, P x ω) →
      ∃ s : Set Ω, μ s ≤ ENNReal.ofReal (l.map b).sum ∧ ∀ ω ∉ s, ∀ x ∈ l, P x ω
  | [], _ => ⟨∅, by simp, fun ω _ x hx => by simp at hx⟩
  | x :: l, h => by
    obtain ⟨s₁, hs₁, hP₁⟩ := h x (by simp)
    obtain ⟨s₂, hs₂, hP₂⟩ := PS_bad_list μ P b hb l fun y hy => h y (by simp [hy])
    refine ⟨s₁ ∪ s₂, ?_, fun ω hω y hy => ?_⟩
    · refine (measure_union_le _ _).trans ?_
      rw [List.map_cons, List.sum_cons, ENNReal.ofReal_add (hb x)
        (List.sum_nonneg fun z hz => by obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz; exact hb w)]
      exact add_le_add hs₁ hs₂
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hP₁ ω fun h' => hω (Or.inl h')
      · exact hP₂ ω (fun h' => hω (Or.inr h')) y hy

/-- A union of bad events, one for each element of a finite type. -/
private lemma PS_bad_fin {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] (μ : Measure Ω)
    (P : α → Ω → Prop) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x, ∃ s : Set Ω, μ s ≤ ENNReal.ofReal b ∧ ∀ ω ∉ s, P x ω) :
    ∃ s : Set Ω, μ s ≤ ENNReal.ofReal (Fintype.card α * b) ∧ ∀ ω ∉ s, ∀ x, P x ω := by
  obtain ⟨s, hs, hP⟩ := PS_bad_list μ P (fun _ => b) (fun _ => hb) Finset.univ.toList
    fun x _ => h x
  refine ⟨s, ?_, fun ω hω x => hP ω hω x (by simp)⟩
  simpa [List.sum_replicate, Finset.length_toList, nsmul_eq_mul] using hs

/-! ## Entries, norms and traces -/

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖X‖ ≤ ‖X‖_HS`. -/
private lemma PS_op_le_hs (X : Matrix ι ι ℂ) : opNorm X ≤ hsNorm X := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ι → ℂ, v = WithLp.toLp 2 x := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp]
  have hsq : ‖(WithLp.toLp 2 (X *ᵥ x) : EuclideanSpace ℂ ι)‖ ^ 2 ≤
      (hsNorm X * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hsNorm,
      Real.sq_sqrt (by positivity), Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : ‖(X *ᵥ x) p‖ ≤ ∑ q, ‖X p q‖ * ‖x q‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖X p q‖) (fun q => ‖x q‖)
    calc ‖(X *ᵥ x) p‖ ^ 2 ≤ (Real.sqrt (∑ q, ‖X p q‖ ^ 2) * Real.sqrt (∑ q, ‖x q‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = (∑ q, ‖X p q‖ ^ 2) * ∑ q, ‖x q‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    two_ne_zero).1 hsq

omit [DecidableEq ι] in
/-- The Cauchy–Schwarz bound of an entry of a product by a row and a column. -/
private lemma PS_entry_cs (X Y : Matrix ι ι ℂ) (a b : ι) :
    ‖(X * Y) a b‖ ≤ Real.sqrt (∑ k, ‖X a k‖ ^ 2) * Real.sqrt (∑ k, ‖Y k b‖ ^ 2) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private lemma PS_dot_single (X : Matrix ι ι ℂ) (a b : ι) :
    star (Pi.single a (1 : ℂ) : ι → ℂ) ⬝ᵥ (X *ᵥ Pi.single b 1) = X a b := by
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

private lemma PS_single_sq (b : ι) : ∑ y, ‖(Pi.single b (1 : ℂ) : ι → ℂ) y‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single b (fun y _ hy => by simp [hy]) (by simp)]
  simp

omit [DecidableEq ι] in
/-- `Σ_{a,k} |X_{ak}|² = Re tr(X X^*)`. -/
private lemma PS_rows (X : Matrix ι ι ℂ) :
    ∑ a, ∑ k, ‖X a k‖ ^ 2 = ((X * Xᴴ).trace).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_sum]
  simp only [Complex.ofReal_re]

omit [DecidableEq ι] in
/-- `Re tr Y ≤ |ι| ‖⟨Y⟩‖`. -/
private lemma PS_tr_le (Y : Matrix ι ι ℂ) : (Y.trace).re ≤ Fintype.card ι * ‖ntr Y‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Matrix.trace]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have e : Y.trace = (Fintype.card ι : ℂ) * ntr Y := by
    unfold ntr
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hc.ne'), one_mul]
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  rw [e, norm_mul, Complex.norm_natCast]

omit [DecidableEq ι] in
/-- `Σ_a |Y_{aa}| = ⟨e_a, Y e_a⟩` is real and nonnegative for `Y = Q^* Q`. -/
private lemma PS_cols (Q : Matrix ι ι ℂ) (b : ι) :
    ∑ k, ‖Q k b‖ ^ 2 = ((Qᴴ * Q) b b).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_re]

end Mat

section Words

variable {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
  (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)

/-- The norm of a word without `Δ`: `≤ g^{#𝒢} K^{len} Q^{#Λ̃}`. -/
private lemma PS_mat_norm (g K Q : ℝ) (hg : 0 ≤ g) (hK : 1 ≤ K) (hQ : 0 ≤ Q)
    (hG : ∀ a, opNorm (G a) ≤ g) (hM : ∀ a, opNorm (M a) ≤ K) (hE : ∀ y, opNorm (E y) ≤ 1)
    (hL : opNorm L ≤ Q) : ∀ σ : List PkgLetter, (∀ x ∈ σ, PkgLetter.isEnt x = false) →
      opNorm (pkgWordMat G M E L κ σ) ≤
        g ^ σ.countP PkgLetter.isRes * K ^ σ.length * Q ^ σ.countP PkgLetter.isLam
  | [], _ => by simpa [PE_wm_nil] using Bd_opNorm_one
  | x :: σ, hσ => by
    have ih := PS_mat_norm g K Q hg hK hQ hG hM hE hL σ fun y hy => hσ y (by simp [hy])
    rw [PE_wm_cons]
    refine (opNorm_mul_le _ _).trans ?_
    have h0 := Bd_opNorm_nonneg (pkgWordMat G M E L κ σ)
    have hK0 : (0 : ℝ) ≤ K := by linarith
    have hKp : K ^ σ.length ≤ K ^ (σ.length + 1) := pow_le_pow_right₀ hK (Nat.le_succ _)
    have hP : 0 ≤ g ^ σ.countP PkgLetter.isRes * K ^ σ.length * Q ^ σ.countP PkgLetter.isLam :=
      by positivity
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp only [List.countP_cons, PkgLetter.isRes, PkgLetter.isLam, List.length_cons,
        ↓reduceIte, Bool.false_eq_true]
      have h1 : opNorm (PE_lm G M E L κ (.lw (.res a))) ≤ g := by
        simpa [PE_lm, loopWordMat] using hG a
      calc opNorm (PE_lm G M E L κ (.lw (.res a))) * opNorm (pkgWordMat G M E L κ σ)
          ≤ g * (g ^ σ.countP PkgLetter.isRes * K ^ σ.length * Q ^ σ.countP PkgLetter.isLam) :=
            mul_le_mul h1 ih h0 hg
        _ ≤ g ^ (σ.countP PkgLetter.isRes + 1) * K ^ (σ.length + 1) *
            Q ^ (σ.countP PkgLetter.isLam + 0) := by
            rw [pow_succ, add_zero]
            have := mul_le_mul_of_nonneg_left hKp
              (by positivity : 0 ≤ g ^ σ.countP PkgLetter.isRes * g)
            have := mul_le_mul_of_nonneg_right this
              (by positivity : 0 ≤ Q ^ σ.countP PkgLetter.isLam)
            nlinarith
    · simp only [List.countP_cons, PkgLetter.isRes, PkgLetter.isLam, List.length_cons,
        ↓reduceIte, Bool.false_eq_true, add_zero]
      have h1 : opNorm (PE_lm G M E L κ (.lw (.det a))) ≤ K := by
        simpa [PE_lm, loopWordMat] using hM a
      calc opNorm (PE_lm G M E L κ (.lw (.det a))) * opNorm (pkgWordMat G M E L κ σ)
          ≤ K * (g ^ σ.countP PkgLetter.isRes * K ^ σ.length * Q ^ σ.countP PkgLetter.isLam) :=
            mul_le_mul h1 ih h0 hK0
        _ = g ^ σ.countP PkgLetter.isRes * K ^ (σ.length + 1) * Q ^ σ.countP PkgLetter.isLam := by
            ring
    · simp only [List.countP_cons, PkgLetter.isRes, PkgLetter.isLam, List.length_cons,
        ↓reduceIte, Bool.false_eq_true, add_zero]
      have h1 : opNorm (PE_lm G M E L κ (.lw (.proj y))) ≤ K := by
        simpa [PE_lm, loopWordMat] using (hE y).trans hK
      calc opNorm (PE_lm G M E L κ (.lw (.proj y))) * opNorm (pkgWordMat G M E L κ σ)
          ≤ K * (g ^ σ.countP PkgLetter.isRes * K ^ σ.length * Q ^ σ.countP PkgLetter.isLam) :=
            mul_le_mul h1 ih h0 hK0
        _ = g ^ σ.countP PkgLetter.isRes * K ^ (σ.length + 1) * Q ^ σ.countP PkgLetter.isLam := by
            ring
    · simp only [List.countP_cons, PkgLetter.isRes, PkgLetter.isLam, List.length_cons,
        ↓reduceIte, Bool.false_eq_true, add_zero]
      have h1 : opNorm (PE_lm G M E L κ (.lw (.lamt o))) ≤ Q := by
        simpa [PE_lm, loopWordMat] using hL
      calc opNorm (PE_lm G M E L κ (.lw (.lamt o))) * opNorm (pkgWordMat G M E L κ σ)
          ≤ Q * (g ^ σ.countP PkgLetter.isRes * K ^ σ.length * Q ^ σ.countP PkgLetter.isLam) :=
            mul_le_mul h1 ih h0 hQ
        _ ≤ g ^ σ.countP PkgLetter.isRes * K ^ (σ.length + 1) *
            Q ^ (σ.countP PkgLetter.isLam + 1) := by
            rw [pow_succ Q]
            have := mul_le_mul_of_nonneg_left hKp
              (by positivity : 0 ≤ g ^ σ.countP PkgLetter.isRes)
            have := mul_le_mul_of_nonneg_right this
              (by positivity : 0 ≤ Q ^ σ.countP PkgLetter.isLam * Q)
            nlinarith
    · simp [PkgLetter.isEnt] at hσ

/-- An entry of a word with entries at labels in `S` from bounds of its packages on `S`. -/
private lemma PS_entry_le (S : Set (Idx D N)) (hκ : ∀ l, κ l ∈ S) (β : List PkgLetter → ℝ) :
    ∀ (n : ℕ) (l : List PkgLetter), l.length ≤ n → (∀ s ∈ l.splitOnP isEntP, 0 ≤ β s) →
      (∀ s ∈ l.splitOnP isEntP, ∀ a b, a ∈ S → b ∈ S → ‖pkgWordMat G M E L κ s a b‖ ≤ β s) →
      ∀ a b, a ∈ S → b ∈ S → ‖pkgWordMat G M E L κ l a b‖ ≤ ((l.splitOnP isEntP).map β).prod
  | n, l, hn, h0, h, a, b, ha, hb => by
    by_cases hl : l.any isEntP = true
    · obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent l hl
      have hs : (P ++ .ent x y :: Q).splitOnP isEntP = P :: Q.splitOnP isEntP := by
        rw [List.splitOnP_append_cons P Q (rfl : isEntP (.ent x y) = true),
          List.splitOnP_eq_singleton hP]
        rfl
      rw [hs] at h0 h ⊢
      rw [PB_entry_ent, norm_mul, List.map_cons, List.prod_cons]
      match n with
      | 0 => simp at hn
      | n + 1 =>
        have hQ : Q.length ≤ n := by simp at hn; omega
        have ih := PS_entry_le S hκ β n Q hQ (fun s hs => h0 s (List.mem_cons_of_mem _ hs))
          (fun s hs => h s (List.mem_cons_of_mem _ hs)) (κ y) b (hκ y) hb
        exact mul_le_mul (h P List.mem_cons_self _ _ ha (hκ x)) ih (norm_nonneg _)
          (h0 P List.mem_cons_self)
    · have hl' : ∀ y ∈ l, isEntP y = false := by simpa using hl
      rw [List.splitOnP_eq_singleton hl'] at h ⊢
      simpa using h l List.mem_cons_self a b ha hb

/-- The trace of a word with a letter `Δ` from bounds of its packages on the labels `S`. -/
private lemma PS_trace_le (S : Set (Idx D N)) (hκ : ∀ l, κ l ∈ S) (w : List PkgLetter)
    (hw : w.any PkgLetter.isEnt = true) (β : List PkgLetter → ℝ)
    (hβ : ∀ s ∈ pkgSegs w, 0 ≤ β s)
    (h : ∀ s ∈ pkgSegs w, ∀ a b, a ∈ S → b ∈ S → ‖pkgWordMat G M E L κ s a b‖ ≤ β s) :
    ‖(pkgWordMat G M E L κ w).trace‖ ≤ ((pkgSegs w).map β).prod := by
  obtain ⟨P, x, y, Q, hP, rfl⟩ := exists_first_ent w hw
  have e : pkgSegs (P ++ .ent x y :: Q) = (Q ++ P).splitOnP isEntP := PB_segs_ent P Q x y hP
  rw [e] at hβ h ⊢
  rw [PB_trace_ent]
  exact PS_entry_le G M E L κ S hκ β _ _ le_rfl hβ h _ _ (hκ y) (hκ x)

/-- The paired letters: `𝔐_a` scaled by `m` on the paired slots scales a word by `m` per paired
letter. -/
private lemma PS_wm_scale (pr : Fin 2 → Bool) (m : ℂ) : ∀ w : List PkgLetter,
    pkgWordMat G (fun a => (if pr a then m else 1) • M a) E L κ w =
      m ^ (w.filter fun x => match x with | .lw (.det a) => pr a | _ => false).length •
        pkgWordMat G M E L κ w
  | [] => by simp [PE_wm_nil]
  | x :: w => by
    rw [PE_wm_cons, PE_wm_cons, PS_wm_scale pr m w]
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp [PE_lm, loopWordMat]
    · by_cases ha : pr a
      · simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons, pow_succ]
        simp [PE_lm, loopWordMat, ha, smul_smul, mul_comm]
      · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte]
        simp [PE_lm, loopWordMat, ha]
    · simp [PE_lm, loopWordMat]
    · simp [PE_lm, loopWordMat]
    · simp [PE_lm]

end Words

/-! ## The factors of one package -/

section Pkg

variable {D N : ℕ}

/-- The factor of a letter of a word without `Δ`. -/
private def PS_pl (s : Fin 2 → Bool) (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) :
    PkgLetter → PS_It (Idx D N)
  | .lw y => PS_ofL s M E L y
  | .ent _ _ => .inr 1

private lemma PS_pl_mat (Gr : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (s : Fin 2 → Bool)
    (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ)
    (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N) : ∀ σ : List PkgLetter,
    (∀ x ∈ σ, PkgLetter.isEnt x = false) →
    pkgWordMat (fun a => if s a then (Gr a)ᴴ else Gr a) M E L κ σ = PS_v Gr (σ.map (PS_pl s M E L))
  | [], _ => by simp [PE_wm_nil, PS_v]
  | x :: σ, h => by
    rw [PE_wm_cons, PS_pl_mat Gr s M E L κ σ fun y hy => h y (by simp [hy])]
    simp only [PS_v, List.map_cons, List.prod_cons]
    congr 1
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp [PE_lm, loopWordMat, PS_pl, PS_ofL, PS_it]
    · simp [PE_lm, loopWordMat, PS_pl, PS_ofL, PS_it]
    · simp [PE_lm, loopWordMat, PS_pl, PS_ofL, PS_it]
    · simp [PE_lm, loopWordMat, PS_pl, PS_ofL, PS_it]
    · simp [PkgLetter.isEnt] at h

private lemma PS_pl_nr (s : Fin 2 → Bool) (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (σ : List PkgLetter) : PS_nr (σ.map (PS_pl s M E L)) = σ.countP PkgLetter.isRes := by
  unfold PS_nr
  rw [List.countP_map]
  congr 1
  funext x
  rcases x with ((a | a | y | o) | ⟨u, v⟩) <;> rfl

private lemma PS_pl_det (s : Fin 2 → Bool) (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (K : ℝ) (hK : 1 ≤ K)
    (hM : ∀ a, opNorm (M a) ≤ K) (hE : ∀ y, opNorm (E y) ≤ 1) (σ : List PkgLetter)
    (hσ : ∀ x ∈ σ, PkgLetter.isLam x = false) :
    ∀ B, Sum.inr B ∈ σ.map (PS_pl s M E L) → opNorm B ≤ K := by
  intro B hB
  obtain ⟨x, hx, hxB⟩ := List.mem_map.1 hB
  rcases x with ((a | a | y | o) | ⟨u, v⟩)
  · simp [PS_pl, PS_ofL] at hxB
  · simp only [PS_pl, PS_ofL, Sum.inr.injEq] at hxB
    exact hxB ▸ hM a
  · simp only [PS_pl, PS_ofL, Sum.inr.injEq] at hxB
    exact hxB ▸ (hE y).trans hK
  · exact absurd (hσ _ hx) (by simp [PkgLetter.isLam])
  · simp only [PS_pl, Sum.inr.injEq] at hxB
    exact hxB ▸ Bd_opNorm_one.trans hK

/-- A bound `‖X_{ab}‖ ≤ c Π (φ(a) + φ(b))` of the entries of a package over at most `k` functions
`φ` in `ℓ²`, with `c Π T ≤ V N^{k/2}`. -/
private def PS_PC (X : Matrix (Idx D N) (Idx D N) ℂ) (V : ℝ) (k : ℕ) : Prop :=
  ∃ c : ℝ, ∃ L : List ((Idx D N → ℝ) × ℝ), L.length ≤ k ∧ PS_L2 L ∧ 0 ≤ c ∧
    (∀ a b, ‖X a b‖ ≤ c * (L.map fun t => t.1 a + t.1 b).prod) ∧
    c * (L.map Prod.snd).prod ≤ V * Real.sqrt N ^ L.length

private lemma PS_PC_const (X : Matrix (Idx D N) (Idx D N) ℂ) (V : ℝ) (k : ℕ) (hV : 0 ≤ V)
    (h : ∀ a b, ‖X a b‖ ≤ V) : PS_PC X V k :=
  ⟨V, [], Nat.zero_le _, fun t ht => by simp at ht, hV, fun a b => by simpa using h a b,
    by simp⟩

/-- The facts on the slots, the deterministic letters `M` and the projections `E` at size `N`
used by the bounds of the factors, with one constant `K ≥ 1`. -/
private def PS_Ctx (D N : ℕ) (δA τ c₀ K η m : ℝ) (e : LoopEnv D N)
    (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  PS_Adm D N δA τ c₀ K e ∧ (∀ a, (e.z a).im = η) ∧ η ≤ 1 ∧ m ≤ 1 ∧
    1 ≤ K * ((N : ℝ) * η * m) ∧
    (∀ a, (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤ K * m) ∧
    hsNorm e.Lt ≤ K * hsNorm e.A ∧ hsNorm (lam D N e.A) ≤ K * hsNorm e.A ∧
    opNorm e.Lt ≤ K * hsNorm e.A ∧ (∀ a, opNorm (M a) ≤ K) ∧ (∀ y, opNorm (E y) ≤ 1) ∧
    (D : ℝ) ≤ K ∧ 1 ≤ N

private lemma PS_Ctx_pos {δA τ c₀ K η m : ℝ} {e : LoopEnv D N}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (hK : 1 ≤ K) : 0 < η ∧ 0 < m ∧ (η * m)⁻¹ ≤ K * N := by
  obtain ⟨⟨-, -, -, hz, -⟩, heta, -, -, h1, -⟩ := hc
  have hη : 0 < η := heta 0 ▸ (hz 0).2.1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hm : 0 < m := by
    by_contra hm
    have : K * ((N : ℝ) * η * m) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hN hη.le) (not_lt.1 hm))
    linarith
  refine ⟨hη, hm, ?_⟩
  rw [inv_le_iff_one_le_mul₀ (mul_pos hη hm)]
  calc (1 : ℝ) ≤ K * ((N : ℝ) * η * m) := h1
    _ = K * N * (η * m) := by ring

/-- For a Hermitian array, `‖𝒢_a‖ ≤ η⁻¹`. -/
private lemma PS_G_norm {δA τ c₀ K η m : ℝ} {e : LoopEnv D N}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (a : Fin 2) : opNorm (e.G h a) ≤ η⁻¹ := by
  have hη : 0 < (e.z a).im := (hc.1.2.2.2.1 a).2.1
  refine (Bd_G_norm e h hh a hη.ne').trans ?_
  rw [abs_of_pos hη, hc.2.1 a]

/-- For a Hermitian array, the matrix of a package is the product of its factors. -/
private lemma PS_mat (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ)
    (κ : ℕ → Idx D N) (σ : List PkgLetter) (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) :
    pkgWordMat (e.G h) M E e.Lt κ σ = PS_v (PS_Gr e h) (σ.map (PS_pl e.s M E e.Lt)) := by
  rw [Bd_G_eq e h hh]
  exact PS_pl_mat _ e.s M E e.Lt κ σ hσ

/-- `Λ̃ = Λ - δ` is Hermitian. -/
private lemma PS_Lt_herm (e : LoopEnv D N) : e.Ltᴴ = e.Lt := by
  unfold LoopEnv.Lt
  rw [Matrix.conjTranspose_sub, (lam_isHermitian D N e.A).eq, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one]
  simp

/-- The isotropic and averaged (A.53) [entprodG] at size `N`, for `1 ≤ r ≤ 2 Lm` resolvents. -/
private def PS_Iso (D N : ℕ) (δA τ c₀ K : ℝ) (C : ℕ → ℝ) (Lm : ℕ) (τ' D' : ℝ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 2 * Lm → ∀ μ, LLClass D N C 1 μ → ∀ e : LoopEnv D N,
    PS_Adm D N δA τ c₀ K e → ∀ l : List (PS_It (Idx D N)), PS_nr l = r → l.length ≤ 2 * Lm →
      (∀ B, Sum.inr B ∈ l → opNorm B ≤ K) →
      μ {h | (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * PS_b e r) <
          ‖ntr (PS_v (PS_Gr e h) l)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
      ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
        μ {h | (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * PS_b e r) <
          ‖star u ⬝ᵥ (PS_v (PS_Gr e h) l *ᵥ v)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))

/-- (A.54) [one_loop_estimate] at size `N`, for `1 ≤ r ≤ 2 Lm` resolvents. -/
private def PS_One (D N : ℕ) (δA τ c₀ K : ℝ) (C : ℕ → ℝ) (Lm : ℕ) (τ' D' : ℝ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 2 * Lm → ∀ μ, LLClass D N C 1 μ → ∀ e : LoopEnv D N,
    PS_Adm D N δA τ c₀ K e → ∀ l : List (PS_It (Idx D N)), PS_nr l = r → l.length ≤ 2 * Lm →
      (∀ B, Sum.inr B ∈ l → opNorm B ≤ K) →
      μ {h | (N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (r + 1) * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
          hsNorm (lam D N e.A) * PS_b e r)) < ‖ntr (PS_v (PS_Gr e h) l * e.Lt)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D'))

/-- (A.55) [two_loop_estimate] at size `N`, for `1 ≤ r ≤ 2 Lm` resolvents and a second word
without resolvent. -/
private def PS_Two (D N : ℕ) (δA τ c₀ K : ℝ) (C : ℕ → ℝ) (Lm : ℕ) (τ' D' : ℝ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 2 * Lm → ∀ μ, LLClass D N C 1 μ → ∀ e : LoopEnv D N,
    PS_Adm D N δA τ c₀ K e → ∀ l₁ l₂ : List (PS_It (Idx D N)), PS_nr l₁ = r → PS_nr l₂ = 0 →
      l₁.length ≤ 2 * Lm → l₂.length ≤ 2 * Lm → (∀ B, Sum.inr B ∈ l₁ → opNorm B ≤ K) →
      (∀ B, Sum.inr B ∈ l₂ → opNorm B ≤ K) →
      μ {h | (N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (r + 0 + 2) *
          (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (r + 0))) <
        ‖ntr (PS_v (PS_Gr e h) l₁ * e.Lt * PS_v (PS_Gr e h) l₂ * e.Lt)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D'))

private lemma PS_ev (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hK : 1 ≤ K) (C : ℕ → ℝ) (Lm : ℕ) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ)
    (hD' : 0 < D') : ∀ᶠ N in atTop, PS_Iso D N δA τ c₀ K C Lm τ' D' ∧
      PS_One D N δA τ c₀ K C Lm τ' D' ∧ PS_Two D N δA τ c₀ K C Lm τ' D' := by
  have h1 := (Filter.eventually_all_finset (Finset.Icc 1 (2 * Lm))).2 fun r hr =>
    PS_fbw D hD δA τ c₀ K hδA hτ hc₀ hK C (2 * Lm) r (Finset.mem_Icc.1 hr).1 τ' hτ' D' hD'
  have h2 := (Filter.eventually_all_finset (Finset.Icc 1 (2 * Lm))).2 fun r hr =>
    PS_fbl D hD δA τ c₀ K K hδA hτ hc₀ hK C (2 * Lm) r (Finset.mem_Icc.1 hr).1 τ' hτ' D' hD'
  have h3 := (Filter.eventually_all_finset (Finset.Icc 1 (2 * Lm))).2 fun r hr =>
    PS_fbt D hD δA τ c₀ K K hδA hτ hc₀ hK C (2 * Lm) r 0 (by simpa using (Finset.mem_Icc.1 hr).1)
      τ' hτ' D' hD'
  filter_upwards [h1, h2, h3] with N hN1 hN2 hN3
  refine ⟨fun r hr1 hr2 μ hμ e he l hl hlen hd => ?_, fun r hr1 hr2 μ hμ e he l hl hlen hd => ?_,
    fun r hr1 hr2 μ hμ e he l₁ l₂ hl₁ hl₂ hlen₁ hlen₂ hd₁ hd₂ => ?_⟩
  · exact hN1 r (Finset.mem_Icc.2 ⟨hr1, hr2⟩) μ hμ K e he l hl hlen hd
  · exact hN2 r (Finset.mem_Icc.2 ⟨hr1, hr2⟩) μ hμ e he l hl hlen hd
  · exact hN3 r (Finset.mem_Icc.2 ⟨hr1, hr2⟩) μ hμ e he l₁ l₂ hl₁ hl₂ hlen₁ hlen₂ hd₁ hd₂

end Pkg

/-! ## Packages: auxiliary facts -/

section PkgAux

variable {D N : ℕ}

/-- The constant of the factor bounds on the good event. -/
private def PS_Cg (K : ℝ) (Lm : ℕ) : ℝ := K ^ (8 * (2 * Lm + 2) ^ 2)

/-- The constant of the crude bounds. -/
private def PS_Cc (K : ℝ) (Lm : ℕ) : ℝ := K ^ (Lm + 4)

private lemma PS_Cg_ge (K : ℝ) (hK : 1 ≤ K) (Lm n : ℕ) (hn : n ≤ 8 * (2 * Lm + 2) ^ 2) :
    K ^ n ≤ PS_Cg K Lm :=
  pow_le_pow_right₀ hK hn

private lemma PS_Cg_one (K : ℝ) (hK : 1 ≤ K) (Lm : ℕ) : 1 ≤ PS_Cg K Lm := one_le_pow₀ hK

private lemma PS_Cc_one (K : ℝ) (hK : 1 ≤ K) (Lm : ℕ) : 1 ≤ PS_Cc K Lm := one_le_pow₀ hK

/-- A union over a finite type of events of probability `≤ b`. -/
private lemma PS_union_le {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] (μ : Measure Ω)
    (s : α → Set Ω) (b : ℝ) (h : ∀ x, μ (s x) ≤ ENNReal.ofReal b) :
    μ (⋃ x, s x) ≤ ENNReal.ofReal (Fintype.card α * b) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun x _ => h x).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- `(DN)² N^{-D'} ≤ 2 (DN)² N^{-D'}`, the bound of the bad events of one package. -/
private lemma PS_card2 (D' : ℝ) :
    (Fintype.card (Idx D N × Idx D N) : ℝ) * (N : ℝ) ^ (-D') ≤
      2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D') := by
  have hc : ((Fintype.card (Idx D N × Idx D N) : ℕ) : ℝ) = ((D : ℝ) * N) ^ 2 := by
    simp [Fintype.card_prod]; ring
  rw [hc]
  have := Real.rpow_nonneg (Nat.cast_nonneg N) (-D')
  nlinarith [sq_nonneg ((D : ℝ) * N)]

/-- A list with a letter `Λ̃` splits at its first one. -/
private lemma PS_split_lam : ∀ σ : List PkgLetter, 0 < σ.countP PkgLetter.isLam →
    ∃ P : List PkgLetter, ∃ o : Fin 2, ∃ Q : List PkgLetter,
      σ = P ++ .lw (.lamt o) :: Q ∧ ∀ y ∈ P, PkgLetter.isLam y = false
  | [], h => by simp at h
  | x :: σ, h => by
    by_cases hx : PkgLetter.isLam x = true
    · rcases x with ((a | a | y | o) | ⟨u, v⟩) <;> simp [PkgLetter.isLam] at hx
      exact ⟨[], o, σ, rfl, by simp⟩
    · have hx' : PkgLetter.isLam x = false := by simpa using hx
      have : 0 < σ.countP PkgLetter.isLam := by simpa [List.countP_cons, hx'] using h
      obtain ⟨P, o, Q, rfl, hP⟩ := PS_split_lam σ this
      refine ⟨x :: P, o, Q, rfl, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx'
      · exact hP y hy

private lemma PS_tw (P S : List PkgLetter) (x : PkgLetter) (hP : ∀ y ∈ P, PkgLetter.isLam y = false)
    (hx : PkgLetter.isLam x = true) :
    (P ++ x :: S).takeWhile (fun y => !y.isLam) = P ∧
      (P ++ x :: S).dropWhile (fun y => !y.isLam) = x :: S := by
  induction P with
  | nil => simp [hx]
  | cons y P ih =>
    have hy := hP y (by simp)
    obtain ⟨h1, h2⟩ := ih fun z hz => hP z (by simp [hz])
    simp [hy, h1, h2]

private lemma PS_lam_free (l : List PkgLetter) (h : l.countP PkgLetter.isLam = 0) :
    ∀ y ∈ l, PkgLetter.isLam y = false := by
  intro y hy
  simpa using List.countP_eq_zero.1 h y hy

/-- The last letter of `P Λ̃ Q` is a resolvent only if `Q` has a resolvent. -/
private lemma PS_last_res (P Q : List PkgLetter) (o : Fin 2)
    (h : (P ++ .lw (.lamt o) :: Q).getLast?.map PkgLetter.isRes = some true) :
    1 ≤ Q.countP PkgLetter.isRes := by
  rw [List.getLast?_append_cons] at h
  rcases Q with _ | ⟨y, Q⟩
  · simp [PkgLetter.isRes] at h
  · rw [List.getLast?_cons_of_ne_nil (by simp)] at h
    obtain ⟨z, hz, hzr⟩ := Option.map_eq_some_iff.1 h
    exact List.countP_pos_iff.2 ⟨z, List.mem_of_getLast? hz, hzr⟩

private lemma PS_last_res' (σ : List PkgLetter)
    (h : σ.getLast?.map PkgLetter.isRes = some true) : 1 ≤ σ.countP PkgLetter.isRes := by
  obtain ⟨z, hz, hzr⟩ := Option.map_eq_some_iff.1 h
  exact List.countP_pos_iff.2 ⟨z, List.mem_of_getLast? hz, hzr⟩

/-- The matrix of `P Λ̃ Q`. -/
private lemma PS_mat_lam (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (P Q : List PkgLetter) (o : Fin 2) :
    pkgWordMat G M E L κ (P ++ .lw (.lamt o) :: Q) =
      pkgWordMat G M E L κ P * L * pkgWordMat G M E L κ Q := by
  rw [PE_wm_append, PE_wm_cons, PE_lm_lamt, Matrix.mul_assoc]

/-- A word without resolvent does not depend on the resolvents. -/
private lemma PS_mat_det (G G' M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)
    (P : List PkgLetter) (hP : P.countP PkgLetter.isRes = 0) :
    pkgWordMat G M E L κ P = pkgWordMat G' M E L κ P := by
  refine Pr_wm_congr E L κ G G' M M P (fun c hc => ?_) (fun _ _ => rfl)
  have := List.countP_eq_zero.1 hP _ hc
  simp [PkgLetter.isRes] at this

/-- `√(x² y) ≤ x y` for `x ≥ 0`, `y ≥ 1`. -/
private lemma PS_sqrt_le (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) : Real.sqrt (x ^ 2 * y) ≤ x * y := by
  rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx]
  refine mul_le_mul_of_nonneg_left ?_ hx
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- `η^{-r} ≤ K N ψ(r)` for `r ≥ 1`, from `(η Im m)⁻¹ ≤ K N`. -/
private lemma PS_crude_psi {η m K : ℝ} (hη : 0 < η) (hm : 0 < m) (hm1 : m ≤ 1)
    (hηm : (η * m)⁻¹ ≤ K * N) {r : ℕ} (hr : 1 ≤ r) :
    η⁻¹ ^ r ≤ K * N * pkgPsi η m r := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e : η⁻¹ ^ (r + 1) = (η * m)⁻¹ * (m / η ^ (r + 1 - 1)) := by
    rw [Nat.add_sub_cancel, inv_pow]
    have := hη.ne'
    have := hm.ne'
    field_simp
    ring
  rw [e]
  exact mul_le_mul hηm (PS_psi_low hη hm1 _) (div_nonneg hm.le (by positivity))
    (le_trans (by positivity) hηm)

/-- `η^{-(a+c)} ≤ (K N)² ψ½(a) ψ½(c)`. -/
private lemma PS_crude_half {η m K : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hm : 0 < m) (hm1 : m ≤ 1)
    (hηm : (η * m)⁻¹ ≤ K * N) (a c : ℕ) :
    η⁻¹ ^ (a + c) ≤ (K * N) ^ 2 * (pkgHalf η m a * pkgHalf η m c) := by
  have e : η⁻¹ ^ (a + c) = ((η * m)⁻¹) ^ 2 * ((m * η / η ^ a) * (m * η / η ^ c)) := by
    rw [inv_pow]
    have := hη.ne'
    have := hm.ne'
    field_simp
    ring
  rw [e]
  have h0 : 0 ≤ (η * m)⁻¹ := by positivity
  exact mul_le_mul (pow_le_pow_left₀ h0 hηm 2)
    (mul_le_mul (PS_half_low hη hη1 hm.le hm1 a) (PS_half_low hη hη1 hm.le hm1 c)
      (by positivity) (PS_half_nonneg m hη a)) (by positivity) (by positivity)

end PkgAux

/-! ## The factors of one package: the bounds -/

section PkgBd

variable {D N : ℕ}

/-- The crude bound of the entries of a package: `η^{-r} K^{Lm} (K ‖A‖_HS)^{#Λ̃}`. -/
private lemma PS_crude_core {δA τ c₀ K η m : ℝ} {e : LoopEnv D N} {Lm : ℕ}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (hK : 1 ≤ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (κ : ℕ → Idx D N) (σ : List PkgLetter)
    (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) (hlen : σ.length ≤ Lm) (a b : Idx D N) :
    ‖pkgWordMat (e.G h) M E e.Lt κ σ a b‖ ≤
      η⁻¹ ^ σ.countP PkgLetter.isRes * K ^ Lm * (K * hsNorm e.A) ^ σ.countP PkgLetter.isLam := by
  obtain ⟨hη, -, -⟩ := PS_Ctx_pos hc hK
  have hLt := hc.2.2.2.2.2.2.2.2.1
  have hM := hc.2.2.2.2.2.2.2.2.2.1
  have hE := hc.2.2.2.2.2.2.2.2.2.2.1
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  refine (norm_apply_le_opNorm _ a b).trans ((PS_mat_norm (e.G h) M E e.Lt κ η⁻¹ K
    (K * hsNorm e.A) (by positivity) hK (by positivity) (PS_G_norm hc h hh) hM hE hLt σ hσ).trans
    ?_)
  gcongr

/-- A package without `Λ̃`, by the isotropic (A.53) [entprodG]: `|(Π)_{ab}| ≺ ψ(r)`. -/
private lemma PS_pkg_free {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 1 ≤ K)
    (hI : PS_Iso D N δA τ c₀ K C Lm τ' D') {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C 1 μ) {e : LoopEnv D N} {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ}
    {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ} (hc : PS_Ctx D N δA τ c₀ K η m e M E)
    (σ : List PkgLetter) (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) (hlen : σ.length ≤ Lm)
    (hr : 1 ≤ σ.countP PkgLetter.isRes) (hL : σ.countP PkgLetter.isLam = 0) (κ : ℕ → Idx D N) :
    (∀ h, (Matrix.of h).IsHermitian → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cc K Lm * N ^ 3 * pkgPsi η m (σ.countP PkgLetter.isRes)) 0) ∧
    ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) ∧
      ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cg K Lm * (N : ℝ) ^ τ' * pkgPsi η m (σ.countP PkgLetter.isRes)) 0 := by
  obtain ⟨hη, hm, hηm⟩ := PS_Ctx_pos hc hK
  have hc' := hc
  obtain ⟨hadm, heta, hη1, hm1, -, him, -, -, -, hM, hE, -, hN1⟩ := hc
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set r := σ.countP PkgLetter.isRes with hrdef
  have hψ := PS_psi_nonneg hη hm.le r
  have hrL : r ≤ 2 * Lm := List.countP_le_length.trans (by omega)
  refine ⟨fun h hh => PS_PC_const _ _ 0 (by have := PS_Cc_one K hK Lm; positivity)
    fun a b => ?_, ?_⟩
  · refine (PS_crude_core hc' hK h hh κ σ hσ hlen a b).trans ?_
    rw [hL, pow_zero, mul_one]
    have h1 := PS_crude_psi hη hm hm1 hηm hr
    have hN3 : (N : ℝ) ≤ N ^ 3 :=
      (pow_one (N : ℝ)).symm.le.trans (pow_le_pow_right₀ hNr (by norm_num))
    have hKp : K ^ (Lm + 1) ≤ K ^ (Lm + 4) := pow_le_pow_right₀ hK (by omega)
    calc η⁻¹ ^ r * K ^ Lm ≤ K * N * pkgPsi η m r * K ^ Lm :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K ^ (Lm + 1) * N * pkgPsi η m r := by ring
      _ ≤ K ^ (Lm + 4) * N ^ 3 * pkgPsi η m r :=
          mul_le_mul_of_nonneg_right (mul_le_mul hKp hN3 (by positivity) (by positivity)) hψ
  · set l := σ.map (PS_pl e.s M E e.Lt) with hl
    have hlr : PS_nr l = r := PS_pl_nr _ _ _ _ σ
    have hll : l.length ≤ 2 * Lm := by simp only [hl, List.length_map]; omega
    have hld := PS_pl_det e.s M E e.Lt K hK hM hE σ (PS_lam_free σ hL)
    have hiso := (hI r hr hrL μ hμ e hadm l hlr hll hld).2
    refine ⟨⋃ ab : Idx D N × Idx D N, {h | (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * PS_b e r) <
        ‖star (Pi.single ab.1 (1 : ℂ)) ⬝ᵥ (PS_v (PS_Gr e h) l *ᵥ Pi.single ab.2 1)‖},
      (PS_union_le μ _ _ fun ab => hiso _ _ (PS_single_sq _) (PS_single_sq _)).trans
        (ENNReal.ofReal_le_ofReal (PS_card2 D')), fun h hh hb => ?_⟩
    have hb' : PS_b e r ≤ K * pkgPsi η m r := PS_bnd hη heta hK him r
    refine PS_PC_const _ _ 0 (by have := PS_Cg_one K hK Lm; positivity) fun a b => ?_
    have hab : ¬ ((N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * PS_b e r) <
        ‖star (Pi.single a (1 : ℂ)) ⬝ᵥ (PS_v (PS_Gr e h) l *ᵥ Pi.single b 1)‖) :=
      fun hlt => hb (Set.mem_iUnion.2 ⟨(a, b), hlt⟩)
    rw [not_lt, ← PS_mat e h hh M E κ σ hσ, PS_dot_single] at hab
    refine hab.trans ?_
    have hNτ : 0 ≤ (N : ℝ) ^ τ' := by positivity
    calc (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * PS_b e r)
        ≤ (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * (K * pkgPsi η m r)) := by gcongr
      _ = K ^ (2 * Lm * (r + 1) + 1) * (N : ℝ) ^ τ' * pkgPsi η m r := by
          rw [pow_succ, pow_mul]; ring
      _ ≤ PS_Cg K Lm * (N : ℝ) ^ τ' * pkgPsi η m r := by
          gcongr
          refine PS_Cg_ge K hK Lm _ ?_
          nlinarith

end PkgBd

/-! ## Packages with `Λ̃`: auxiliary identities -/

section PkgAux2

variable {D N : ℕ}

private lemma PS_tr_gram (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ((X * Y) * (X * Y)ᴴ).trace = (Xᴴ * X * (Y * Yᴴ)).trace := by
  rw [Matrix.conjTranspose_mul]
  have e : X * Y * (Yᴴ * Xᴴ) = X * (Y * Yᴴ * Xᴴ) := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

private lemma PS_card : (Fintype.card (Idx D N) : ℝ) = D * N := by simp [Fintype.card_prod]

/-- `Σ_{a,k} |(X Λ̃)_{ak}|² = Re tr(X^* X Λ̃ Λ̃) ≤ D N ‖⟨X^* X Λ̃ 1 Λ̃⟩‖`. -/
private lemma PS_rows_lt (e : LoopEnv D N) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ a, ∑ k, ‖(X * e.Lt) a k‖ ^ 2 ≤ D * N * ‖ntr (Xᴴ * X * e.Lt * 1 * e.Lt)‖ := by
  rw [PS_rows, PS_tr_gram, PS_Lt_herm, ← PS_card]
  have e1 : Xᴴ * X * (e.Lt * e.Lt) = Xᴴ * X * e.Lt * 1 * e.Lt := by
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [e1]
  exact PS_tr_le _

/-- `Σ_{b,k} |(Λ̃ Q)_{kb}|² ≤ D N ‖⟨Q Q^* Λ̃ 1 Λ̃⟩‖`. -/
private lemma PS_cols_lt (e : LoopEnv D N) (Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ b, ∑ k, ‖(e.Lt * Q) k b‖ ^ 2 ≤ D * N * ‖ntr (Q * Qᴴ * e.Lt * 1 * e.Lt)‖ := by
  rw [Finset.sum_comm, PS_rows, PS_tr_gram, PS_Lt_herm, ← PS_card]
  have e1 : (e.Lt * e.Lt * (Q * Qᴴ)).trace = (Q * Qᴴ * e.Lt * 1 * e.Lt).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [e1]
  exact PS_tr_le _

/-- `Σ_{a,k} |(X Λ̃ Π)_{ak}|² ≤ D N ‖⟨Π Π^* Λ̃ X^* X Λ̃⟩‖`. -/
private lemma PS_rows_lt2 (e : LoopEnv D N) (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ a, ∑ k, ‖(X * e.Lt * Y) a k‖ ^ 2 ≤ D * N * ‖ntr (Y * Yᴴ * e.Lt * (Xᴴ * X) * e.Lt)‖ := by
  rw [PS_rows, PS_tr_gram, Matrix.conjTranspose_mul, PS_Lt_herm, ← PS_card]
  have e1 : (e.Lt * Xᴴ * (X * e.Lt) * (Y * Yᴴ)).trace =
      (Y * Yᴴ * e.Lt * (Xᴴ * X) * e.Lt).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1]
  exact PS_tr_le _

/-- The factors of `X^* X` and `X X^*`. -/
private lemma PS_v_gram (G : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (l : List (PS_It (Idx D N))) :
    PS_v G (l.reverse.map PS_adj ++ l) = (PS_v G l)ᴴ * PS_v G l ∧
      PS_v G (l ++ l.reverse.map PS_adj) = PS_v G l * (PS_v G l)ᴴ := by
  rw [PS_v_append, PS_v_append, PS_v_adj]
  exact ⟨rfl, rfl⟩

private lemma PS_gram_facts (l : List (PS_It (Idx D N))) (K : ℝ)
    (h : ∀ B, Sum.inr B ∈ l → opNorm B ≤ K) :
    PS_nr (l.reverse.map PS_adj ++ l) = 2 * PS_nr l ∧ PS_nr (l ++ l.reverse.map PS_adj) =
      2 * PS_nr l ∧ (l.reverse.map PS_adj ++ l).length = 2 * l.length ∧
      (l ++ l.reverse.map PS_adj).length = 2 * l.length ∧
      (∀ B, Sum.inr B ∈ l.reverse.map PS_adj ++ l → opNorm B ≤ K) ∧
      (∀ B, Sum.inr B ∈ l ++ l.reverse.map PS_adj → opNorm B ≤ K) := by
  have h1 := PS_adj_det l K h
  refine ⟨by rw [PS_nr_append, PS_nr_adj]; ring, by rw [PS_nr_append, PS_nr_adj]; ring,
    by simp; ring, by simp; ring, fun B hB => ?_, fun B hB => ?_⟩
  · rcases List.mem_append.1 hB with hB | hB
    · exact h1 B hB
    · exact h B hB
  · rcases List.mem_append.1 hB with hB | hB
    · exact h B hB
    · exact h1 B hB

end PkgAux2

/-! ## Packages with one `Λ̃` -/

section PkgLam1

variable {D N : ℕ}

private lemma PS_im_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) :
    0 ≤ (mSol Λ z).im := by
  unfold mSol
  split_ifs with h
  · exact h.choose_spec.1.le
  · simp

private lemma PS_b_nonneg {δA τ c₀ K : ℝ} {e : LoopEnv D N} (hadm : PS_Adm D N δA τ c₀ K e)
    (l : ℕ) : 0 ≤ PS_b e l := by
  obtain ⟨-, -, -, hz, -⟩ := hadm
  unfold PS_b bndA4
  refine div_nonneg ?_ (pow_nonneg (le_ciInf fun a => (hz a).2.1.le) _)
  split_ifs
  · exact (PS_im_nonneg _ _).trans (le_ciSup (f := fun a : Fin 2 =>
      (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) (Set.finite_range _).bddAbove 0)
  · exact zero_le_one

/-- `(N^{-1/2})⁻¹ = √N`, and `N ≤ N³ N^{-1/2}`. -/
private lemma PS_half_facts (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ ∧ (N : ℝ) ≤ N ^ 3 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by linarith)]
  refine ⟨h1, ?_⟩
  rw [h1]
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  calc (N : ℝ) * Real.sqrt N ≤ N * N := mul_le_mul_of_nonneg_left hsq (by linarith)
    _ ≤ N ^ 3 := by nlinarith

set_option maxHeartbeats 1000000 in
-- the bounds of the factors are combined in one proof
/-- A package with one `Λ̃`: `P Λ̃ Q` with `P` deterministic, by the isotropic (A.53) [entprodG]
with the row of `P Λ̃` in `ℓ²` ((5.71) [Cauchy_example_2]), or `P` with a resolvent, by (A.55)
[two_loop_estimate] for the row in `ℓ²` ((5.70) [Cauchy_example_1]) and (A.53) [entprodG] for the
column. -/
private lemma PS_pkg_lam1 {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 1 ≤ K)
    (hD : 1 ≤ D) (hI : PS_Iso D N δA τ c₀ K C Lm τ' D') (hT : PS_Two D N δA τ c₀ K C Lm τ' D')
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) {e : LoopEnv D N}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (σ : List PkgLetter)
    (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) (hlen : σ.length ≤ Lm)
    (hend : σ.getLast?.map PkgLetter.isRes = some true) (hL : σ.countP PkgLetter.isLam = 1)
    (κ : ℕ → Idx D N) :
    (∀ h, (Matrix.of h).IsHermitian → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cc K Lm * N ^ 3 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm e.A *
          pkgPsi η m (σ.countP PkgLetter.isRes))) 0) ∧
    ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) ∧
      ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cg K Lm * (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm e.A *
          pkgPsi η m (σ.countP PkgLetter.isRes))) 1 := by
  obtain ⟨hη, hm, hηm⟩ := PS_Ctx_pos hc hK
  have hc' := hc
  obtain ⟨hadm, heta, hη1, hm1, -, him, hsLt, hslam, hLt, hM, hE, hDK, hN1⟩ := hc
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  obtain ⟨hhalf, hN3⟩ := PS_half_facts hN1
  have hsq : Real.sqrt N * (Real.sqrt N)⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.2 hN0).ne'
  obtain ⟨P, o, Q, rfl, hP⟩ := PS_split_lam σ (by omega)
  have hσ' := hσ
  have hcnt : (P ++ .lw (.lamt o) :: Q).countP PkgLetter.isLam =
      P.countP PkgLetter.isLam + 1 + Q.countP PkgLetter.isLam := by
    simp [List.countP_append, List.countP_cons, PkgLetter.isLam]; ring
  have hP0 : P.countP PkgLetter.isLam = 0 := List.countP_eq_zero.2 fun y hy => by simp [hP y hy]
  have hQ0 : Q.countP PkgLetter.isLam = 0 := by omega
  have hQ := PS_lam_free Q hQ0
  have hq1 := PS_last_res P Q o hend
  have hPe : ∀ x ∈ P, PkgLetter.isEnt x = false := fun x hx => hσ x (by simp [hx])
  have hQe : ∀ x ∈ Q, PkgLetter.isEnt x = false := fun x hx => hσ x (by simp [hx])
  have hrr : (P ++ .lw (.lamt o) :: Q).countP PkgLetter.isRes =
      P.countP PkgLetter.isRes + Q.countP PkgLetter.isRes := by
    simp [List.countP_append, PkgLetter.isRes]
  have hlenPQ : P.length + Q.length + 1 ≤ Lm := by simp at hlen; omega
  set p := P.countP PkgLetter.isRes with hpdef
  set q := Q.countP PkgLetter.isRes with hqdef
  have hpL : p ≤ P.length := List.countP_le_length
  have hqL : q ≤ Q.length := List.countP_le_length
  rw [hrr]
  have hψ := PS_psi_nonneg hη hm.le (p + q)
  refine ⟨fun h hh => PS_PC_const _ _ 0 (by have := PS_Cc_one K hK Lm; positivity)
    fun a b => ?_, ?_⟩
  · -- the crude bound
    refine (PS_crude_core hc' hK h hh κ _ hσ hlen a b).trans ?_
    rw [hrr, hcnt, hP0, hQ0]
    simp only [zero_add, add_zero, pow_one]
    have h1 := PS_crude_psi hη hm hm1 hηm (show 1 ≤ p + q by omega)
    have hKp : K ^ (Lm + 2) ≤ K ^ (Lm + 4) := pow_le_pow_right₀ hK (by omega)
    calc η⁻¹ ^ (p + q) * K ^ Lm * (K * hsNorm e.A)
        ≤ K * N * pkgPsi η m (p + q) * K ^ Lm * (K * hsNorm e.A) := by gcongr
      _ = K ^ (Lm + 2) * N * (hsNorm e.A * pkgPsi η m (p + q)) := by ring
      _ ≤ K ^ (Lm + 4) * (N ^ 3 * (N : ℝ) ^ (-(1 / 2 : ℝ))) * (hsNorm e.A * pkgPsi η m (p + q)) :=
          by gcongr
      _ = _ := by rw [PS_Cc]; ring
  · set lP := P.map (PS_pl e.s M E e.Lt) with hlP
    set lQ := Q.map (PS_pl e.s M E e.Lt) with hlQ
    have hlPr : PS_nr lP = p := PS_pl_nr _ _ _ _ P
    have hlQr : PS_nr lQ = q := PS_pl_nr _ _ _ _ Q
    have hlPl : lP.length = P.length := by simp [hlP]
    have hlQl : lQ.length = Q.length := by simp [hlQ]
    have hlPd := PS_pl_det e.s M E e.Lt K hK hM hE P hP
    have hlQd := PS_pl_det e.s M E e.Lt K hK hM hE Q hQ
    have hmatσ : ∀ h, (Matrix.of h).IsHermitian →
        pkgWordMat (e.G h) M E e.Lt κ (P ++ .lw (.lamt o) :: Q) =
          PS_v (PS_Gr e h) lP * e.Lt * PS_v (PS_Gr e h) lQ := by
      intro h hh
      rw [PS_mat_lam, PS_mat e h hh M E κ P hPe, PS_mat e h hh M E κ Q hQe]
    have hbq := PS_bnd hη heta hK him q
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · -- `P` without resolvent: the row of `P Λ̃` is deterministic
      set Y : Matrix (Idx D N) (Idx D N) ℂ := pkgWordMat (fun _ => 0) M E e.Lt κ P * e.Lt
        with hY
      have hYeq : ∀ h, (Matrix.of h).IsHermitian →
          pkgWordMat (e.G h) M E e.Lt κ (P ++ .lw (.lamt o) :: Q) =
            Y * PS_v (PS_Gr e h) lQ := by
        intro h hh
        rw [PS_mat_lam, PS_mat_det (e.G h) (fun _ => 0) M E e.Lt κ P hp0,
          PS_mat e h hh M E κ Q hQe]
      set φ : Idx D N → ℝ := fun a => Real.sqrt (∑ k, ‖Y a k‖ ^ 2) with hφ
      have hφ2 : ∀ a, φ a ^ 2 = ∑ k, ‖Y a k‖ ^ 2 := fun a => Real.sq_sqrt (by positivity)
      have hPn : opNorm (pkgWordMat (fun _ => 0) M E e.Lt κ P) ≤ K ^ Lm := by
        have := PS_mat_norm (fun _ => 0) M E e.Lt κ 0 K (opNorm e.Lt) le_rfl hK
          (Bd_opNorm_nonneg _) (fun _ => by simp [opNorm]) hM hE le_rfl P hPe
        rw [← hpdef, hp0, hP0, pow_zero, pow_zero, one_mul, mul_one] at this
        exact this.trans (pow_le_pow_right₀ hK (by omega))
      set T : ℝ := K ^ Lm * (K * hsNorm e.A) with hT
      have hT0 : 0 ≤ T := by positivity
      have hφT : ∑ a, φ a ^ 2 ≤ T ^ 2 := by
        simp only [hφ2]
        have h1 := MultiRes_hs2_mul_left_le (pkgWordMat (fun _ => 0) M E e.Lt κ P) e.Lt
        have h2 : MultiRes_hs2 e.Lt ≤ (K * hsNorm e.A) ^ 2 := by
          rw [← MultiRes_hsNorm_sq]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsLt 2
        calc ∑ a, ∑ k, ‖Y a k‖ ^ 2 = MultiRes_hs2 Y := rfl
          _ ≤ opNorm (pkgWordMat (fun _ => 0) M E e.Lt κ P) ^ 2 * MultiRes_hs2 e.Lt := h1
          _ ≤ (K ^ Lm) ^ 2 * (K * hsNorm e.A) ^ 2 :=
              mul_le_mul (pow_le_pow_left₀ (Bd_opNorm_nonneg _) hPn 2) h2
                (by unfold MultiRes_hs2; positivity) (by positivity)
          _ = T ^ 2 := by rw [hT]; ring
      set u : Idx D N → Idx D N → ℂ := fun a k => ((φ a)⁻¹ : ℂ) * star (Y a k) with hu
      have hu1 : ∀ a, φ a ≠ 0 → ∑ k, ‖u a k‖ ^ 2 = 1 := by
        intro a ha
        have hpos : 0 < φ a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
        simp only [hu, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos, norm_star, mul_pow, ← Finset.mul_sum, ← hφ2, inv_pow]
        field_simp
      have hentry : ∀ a b (Z : Matrix (Idx D N) (Idx D N) ℂ), φ a ≠ 0 →
          (Y * Z) a b = (φ a : ℂ) * (star (u a) ⬝ᵥ (Z *ᵥ Pi.single b 1)) := by
        intro a b Z ha
        rw [Matrix.mulVec_single_one]
        simp only [hu, Matrix.mul_apply, dotProduct, Pi.star_apply, star_mul', star_star,
          Matrix.col_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : (φ a : ℂ) ≠ 0 := by exact_mod_cast ha
        rw [show star ((φ a : ℂ)⁻¹) = ((φ a : ℂ))⁻¹ by simp [Complex.conj_ofReal]]
        field_simp
      have hiso := (hI q hq1 (by omega) μ hμ e hadm lQ hlQr (by omega) hlQd).2
      set ev : Idx D N × Idx D N → Set (Idx D N → Idx D N → ℂ) := fun ab =>
        if φ ab.1 = 0 then ∅ else {h | (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (q + 1) * PS_b e q) <
          ‖star (u ab.1) ⬝ᵥ (PS_v (PS_Gr e h) lQ *ᵥ Pi.single ab.2 1)‖} with hev
      refine ⟨⋃ ab, ev ab, (PS_union_le μ _ _ fun ab => ?_).trans
        (ENNReal.ofReal_le_ofReal (PS_card2 D')), fun h hh hb => ?_⟩
      · simp only [hev]
        split_ifs with ha
        · simp
        · exact hiso _ _ (hu1 _ ha) (PS_single_sq _)
      · set c : ℝ := (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (q + 1) * (K * pkgPsi η m q)) with hcdef
        have hc0 : 0 ≤ c := by have := PS_psi_nonneg hη hm.le q; positivity
        refine ⟨c, [(φ, T)], le_rfl, fun t ht => ?_, hc0, fun a b => ?_, ?_⟩
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨fun x => Real.sqrt_nonneg _, hφT, hT0⟩
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [hYeq h hh]
          by_cases ha : φ a = 0
          · have hY0 : ∀ k, Y a k = 0 := by
              intro k
              have h1 : ∑ k, ‖Y a k‖ ^ 2 = 0 := by rw [← hφ2, ha]; ring
              have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h1 k
                (Finset.mem_univ _)
              simpa using this
            have : (Y * PS_v (PS_Gr e h) lQ) a b = 0 := by
              simp [Matrix.mul_apply, hY0]
            rw [this, norm_zero]
            exact mul_nonneg hc0 (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          · rw [hentry a b _ ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
            have hab : h ∉ ev (a, b) := fun hm' => hb (Set.mem_iUnion.2 ⟨(a, b), hm'⟩)
            simp only [hev, ha, ↓reduceIte, Set.mem_ofPred_eq, not_lt] at hab
            have h2 : ‖star (u a) ⬝ᵥ (PS_v (PS_Gr e h) lQ *ᵥ Pi.single b 1)‖ ≤ c :=
              hab.trans (by rw [hcdef]; gcongr)
            have h3 : 0 ≤ φ b := Real.sqrt_nonneg _
            nlinarith [Real.sqrt_nonneg (∑ k, ‖Y a k‖ ^ 2)]
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            List.length_cons, List.length_nil, zero_add, pow_one, hp0, zero_add]
          rw [hhalf]
          have hKe : (K ^ (2 * Lm)) ^ (q + 1) * K * K ^ Lm * K ≤ PS_Cg K Lm := by
            rw [← pow_mul, ← pow_succ, ← pow_add, ← pow_succ]
            refine PS_Cg_ge K hK Lm _ ?_
            nlinarith
          calc c * T = ((K ^ (2 * Lm)) ^ (q + 1) * K * K ^ Lm * K) * (N : ℝ) ^ τ' *
                (hsNorm e.A * pkgPsi η m q) := by rw [hcdef, hT]; ring
            _ ≤ PS_Cg K Lm * (N : ℝ) ^ τ' * (hsNorm e.A * pkgPsi η m q) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKe (by positivity))
                  (mul_nonneg hs0 (PS_psi_nonneg hη hm.le q))
            _ = PS_Cg K Lm * (N : ℝ) ^ τ' * ((Real.sqrt N)⁻¹ * hsNorm e.A * pkgPsi η m q) *
                Real.sqrt N := by
                rw [show PS_Cg K Lm * (N : ℝ) ^ τ' * ((Real.sqrt N)⁻¹ * hsNorm e.A *
                  pkgPsi η m q) * Real.sqrt N = PS_Cg K Lm * (N : ℝ) ^ τ' * (hsNorm e.A *
                  pkgPsi η m q) * (Real.sqrt N * (Real.sqrt N)⁻¹) by ring, hsq, mul_one]
    · -- `P` with a resolvent: (A.55) for the row of `P Λ̃`, (A.53) for the column of `Q`
      have hp1 : 1 ≤ p := hp0
      obtain ⟨g1, -, g3, -, g5, -⟩ := PS_gram_facts lP K hlPd
      obtain ⟨-, g2', -, g4', -, g6'⟩ := PS_gram_facts lQ K hlQd
      have g2 := (PS_gram_facts lQ K hlQd).1
      have g4 := (PS_gram_facts lQ K hlQd).2.2.1
      have g6 := (PS_gram_facts lQ K hlQd).2.2.2.2.1
      have htwo := hT (2 * p) (by omega) (by omega) μ hμ e hadm (lP.reverse.map PS_adj ++ lP) []
        (by rw [g1, hlPr]) rfl (by rw [g3]; omega) (by simp) g5 (by simp)
      have hiso := (hI (2 * q) (by omega) (by omega) μ hμ e hadm (lQ.reverse.map PS_adj ++ lQ)
        (by rw [g2, hlQr]) (by rw [g4]; omega) g6).2
      set E1 : Set (Idx D N → Idx D N → ℂ) := {h | (N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^
          (2 * p + 0 + 2) * (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * p + 0))) <
        ‖ntr (PS_v (PS_Gr e h) (lP.reverse.map PS_adj ++ lP) * e.Lt * PS_v (PS_Gr e h) [] *
          e.Lt)‖} with hE1
      set E2 : Idx D N → Set (Idx D N → Idx D N → ℂ) := fun b =>
        {h | (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (2 * q + 1) * PS_b e (2 * q)) <
          ‖star (Pi.single b (1 : ℂ)) ⬝ᵥ (PS_v (PS_Gr e h) (lQ.reverse.map PS_adj ++ lQ) *ᵥ
            Pi.single b 1)‖} with hE2
      have hDN : (1 : ℝ) ≤ D * N := by
        have : (1 : ℝ) ≤ D := by exact_mod_cast hD
        nlinarith
      refine ⟨E1 ∪ ⋃ b, E2 b, ?_, fun h hh hb => ?_⟩
      · refine (measure_union_le _ _).trans ?_
        have h2 := PS_union_le μ E2 _ fun b => hiso _ _ (PS_single_sq b) (PS_single_sq b)
        refine (add_le_add htwo h2).trans ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [PS_card]
        have := Real.rpow_nonneg (Nat.cast_nonneg N) (-D')
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D * N - 1)
          (by linarith : (0 : ℝ) ≤ D * N)) this]
      · have h1 : h ∉ E1 := fun hm' => hb (Or.inl hm')
        have h2 : ∀ b, h ∉ E2 b := fun b hm' => hb (Or.inr (Set.mem_iUnion.2 ⟨b, hm'⟩))
        simp only [hE1, Set.mem_ofPred_eq, not_lt] at h1
        simp only [hE2, Set.mem_ofPred_eq, not_lt] at h2
        obtain ⟨gP, -⟩ := PS_v_gram (PS_Gr e h) lP
        obtain ⟨gQ, -⟩ := PS_v_gram (PS_Gr e h) lQ
        rw [gP] at h1
        rw [gQ] at h2
        set X := PS_v (PS_Gr e h) lP
        set Z := PS_v (PS_Gr e h) lQ
        set φ : Idx D N → ℝ := fun a => Real.sqrt (∑ k, ‖(X * e.Lt) a k‖ ^ 2) with hφ
        set ψ : Idx D N → ℝ := fun b => Real.sqrt (∑ k, ‖Z k b‖ ^ 2) with hψdef
        set T₀ : ℝ := D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * p + 2) *
          ((K * hsNorm e.A) ^ 2 * (K * pkgPsi η m (2 * p))))) with hT₀
        set c₀ : ℝ := (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (2 * q + 1) * (K * pkgPsi η m (2 * q)))
          with hc₀
        have hbp := PS_bnd hη heta hK him (2 * p)
        have hbq2 := PS_bnd hη heta hK him (2 * q)
        have hψ2p := PS_psi_nonneg hη hm.le (2 * p)
        have hψ2q := PS_psi_nonneg hη hm.le (2 * q)
        have hslam0 : 0 ≤ hsNorm (lam D N e.A) := Real.sqrt_nonneg _
        have hφT : ∑ a, φ a ^ 2 ≤ Real.sqrt T₀ ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]
          have e1 : ∑ a, φ a ^ 2 = ∑ a, ∑ k, ‖(X * e.Lt) a k‖ ^ 2 :=
            Finset.sum_congr rfl fun a _ => Real.sq_sqrt (by positivity)
          rw [e1]
          refine (PS_rows_lt e X).trans ?_
          rw [add_zero, PS_v_nil] at h1
          calc (D : ℝ) * N * ‖ntr (Xᴴ * X * e.Lt * 1 * e.Lt)‖
              ≤ D * N * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * p + 2) *
                (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * p)))) := by gcongr
            _ = D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * p + 2) *
                (hsNorm (lam D N e.A) ^ 2 * PS_b e (2 * p)))) := by field_simp
            _ ≤ T₀ := by
                rw [hT₀]
                have := PS_b_nonneg hadm (2 * p)
                gcongr
        have hψc : ∀ b, ψ b ≤ Real.sqrt c₀ := by
          intro b
          refine Real.sqrt_le_sqrt ?_
          rw [PS_cols, ← PS_dot_single (Zᴴ * Z) b b]
          refine (Complex.re_le_norm _).trans ((h2 b).trans ?_)
          rw [hc₀]
          gcongr
        refine ⟨Real.sqrt c₀, [(φ, Real.sqrt T₀)], le_rfl, fun t ht => ?_, Real.sqrt_nonneg _,
          fun a b => ?_, ?_⟩
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨fun x => Real.sqrt_nonneg _, hφT, Real.sqrt_nonneg _⟩
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [hmatσ h hh]
          refine (PS_entry_cs (X * e.Lt) Z a b).trans ?_
          have h3 : 0 ≤ φ b := Real.sqrt_nonneg _
          have h4 : 0 ≤ φ a := Real.sqrt_nonneg _
          calc φ a * ψ b ≤ φ a * Real.sqrt c₀ := mul_le_mul_of_nonneg_left (hψc b) h4
            _ ≤ Real.sqrt c₀ * (φ a + φ b) := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h3) (Real.sqrt_nonneg _)
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            List.length_cons, List.length_nil, zero_add, pow_one]
          rw [hhalf, ← Real.sqrt_mul (by positivity)]
          have hKf : max (K ^ (2 * Lm)) K ≤ K ^ (2 * Lm + 1) :=
            max_le (pow_le_pow_right₀ hK (by omega))
              (le_trans (le_of_eq (pow_one K).symm) (pow_le_pow_right₀ hK (by omega)))
          set K₁ : ℝ := (K ^ (2 * Lm)) ^ (2 * q + 1) * K * (D * (max (K ^ (2 * Lm)) K ^
            (2 * p + 2) * (K ^ 2 * K))) with hK₁
          have hK₁1 : 1 ≤ K₁ := by
            have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
            rw [hK₁]
            refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
              (one_le_pow₀ (one_le_pow₀ hK)) hK) (one_le_mul_of_one_le_of_one_le hD1
              (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_of_le_right hK))
              (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) hK)))
          have hK₁g : K₁ ≤ PS_Cg K Lm := by
            have hK0 : (0 : ℝ) ≤ K := by linarith
            have hA2 : max (K ^ (2 * Lm)) K ^ (2 * p + 2) ≤ K ^ ((2 * Lm + 1) * (2 * p + 2)) := by
              rw [pow_mul K (2 * Lm + 1) (2 * p + 2)]
              exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_of_le_right hK)) hKf _
            have hpLm : p ≤ Lm := by omega
            have hqLm : q ≤ Lm := by omega
            calc K₁ ≤ K ^ (2 * Lm * (2 * q + 1)) * K * (K * (K ^ ((2 * Lm + 1) * (2 * p + 2)) *
                  (K ^ 2 * K))) := by
                  rw [hK₁, ← pow_mul]
                  refine mul_le_mul_of_nonneg_left (mul_le_mul hDK (mul_le_mul_of_nonneg_right hA2
                    (by positivity)) (by positivity) hK0) (by positivity)
              _ = K ^ (2 * Lm * (2 * q + 1) + 1 + 1 + (2 * Lm + 1) * (2 * p + 2) + 2 + 1) := by
                  ring
              _ ≤ PS_Cg K Lm := by
                  refine PS_Cg_ge K hK Lm _ ?_
                  have := Nat.mul_le_mul_left Lm hpLm
                  have := Nat.mul_le_mul_left Lm hqLm
                  nlinarith
          have hprod : c₀ * T₀ = ((N : ℝ) ^ τ' * (hsNorm e.A * pkgPsi η m (p + q))) ^ 2 * K₁ := by
            rw [hc₀, hT₀, hK₁]
            have := PS_psi_sq (m := m) hη hp1 hq1
            have hNτ : ((N : ℝ) ^ τ') ^ 2 = (N : ℝ) ^ τ' * (N : ℝ) ^ τ' := sq _
            calc (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (2 * q + 1) * (K * pkgPsi η m (2 * q))) *
                  (D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * p + 2) *
                  ((K * hsNorm e.A) ^ 2 * (K * pkgPsi η m (2 * p))))))
                = ((N : ℝ) ^ τ') ^ 2 * hsNorm e.A ^ 2 *
                    (pkgPsi η m (2 * p) * pkgPsi η m (2 * q)) * ((K ^ (2 * Lm)) ^ (2 * q + 1) *
                    K * (D * (max (K ^ (2 * Lm)) K ^ (2 * p + 2) * (K ^ 2 * K)))) := by ring
              _ = _ := by rw [this]; ring
          rw [hprod]
          refine (PS_sqrt_le _ _ (by positivity) hK₁1).trans ?_
          calc (N : ℝ) ^ τ' * (hsNorm e.A * pkgPsi η m (p + q)) * K₁
              ≤ (N : ℝ) ^ τ' * (hsNorm e.A * pkgPsi η m (p + q)) * PS_Cg K Lm := by gcongr
            _ = PS_Cg K Lm * (N : ℝ) ^ τ' * ((Real.sqrt N)⁻¹ * hsNorm e.A * pkgPsi η m (p + q)) *
                Real.sqrt N := by
                rw [show PS_Cg K Lm * (N : ℝ) ^ τ' * ((Real.sqrt N)⁻¹ * hsNorm e.A *
                  pkgPsi η m (p + q)) * Real.sqrt N = PS_Cg K Lm * (N : ℝ) ^ τ' * (hsNorm e.A *
                  pkgPsi η m (p + q)) * (Real.sqrt N * (Real.sqrt N)⁻¹) by ring, hsq, mul_one]
                ring

end PkgLam1

/-! ## The factor of a package -/

section PkgFac

variable {D N : ℕ}

private lemma PS_seg_free (σ : List PkgLetter) (h : σ.countP PkgLetter.isLam = 0) :
    pkgSegFac σ = .free (σ.countP PkgLetter.isRes) := by
  simp [pkgSegFac, h]

private lemma PS_seg_lam1 (σ : List PkgLetter) (h : σ.countP PkgLetter.isLam = 1) :
    pkgSegFac σ = .lam1 (σ.countP PkgLetter.isRes) := by
  simp [pkgSegFac, h]

private lemma PS_seg_lam2 (P W Q : List PkgLetter) (o o' : Fin 2)
    (hP : ∀ y ∈ P, PkgLetter.isLam y = false) (hW : ∀ y ∈ W, PkgLetter.isLam y = false)
    (h : (P ++ .lw (.lamt o) :: (W ++ .lw (.lamt o') :: Q)).countP PkgLetter.isLam = 2) :
    pkgSegFac (P ++ .lw (.lamt o) :: (W ++ .lw (.lamt o') :: Q)) =
      .lam2 (W.countP PkgLetter.isRes) (Q.countP PkgLetter.isRes) := by
  have h1 := (PS_tw P (W ++ .lw (.lamt o') :: Q) (.lw (.lamt o)) hP rfl).2
  have h2 := PS_tw W Q (.lw (.lamt o')) hW rfl
  unfold pkgSegFac
  rw [h]
  simp only [h1, List.drop_succ_cons, List.drop_zero, h2.1, h2.2]

end PkgFac

section PkgLam2

variable {D N : ℕ}

/-- `D ‖·‖^{2c+2} K³ ≤ K^{(2Lm+1)(2c+2)+4}`, the constant of (A.55) [two_loop_estimate] on a side
of a package. -/
private lemma PS_K3_le {K : ℝ} (hK : 1 ≤ K) (hDK : (D : ℝ) ≤ K) (Lm c : ℕ) :
    (D : ℝ) * (max (K ^ (2 * Lm)) K ^ (2 * c + 2) * (K ^ 2 * K)) ≤
      K ^ ((2 * Lm + 1) * (2 * c + 2) + 4) := by
  have hKf : max (K ^ (2 * Lm)) K ≤ K ^ (2 * Lm + 1) :=
    max_le (pow_le_pow_right₀ hK (by omega))
      (le_trans (le_of_eq (pow_one K).symm) (pow_le_pow_right₀ hK (by omega)))
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have h1 : max (K ^ (2 * Lm)) K ^ (2 * c + 2) ≤ K ^ ((2 * Lm + 1) * (2 * c + 2)) := by
    rw [pow_mul K (2 * Lm + 1) (2 * c + 2)]
    exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_of_le_right hK)) hKf _
  calc (D : ℝ) * (max (K ^ (2 * Lm)) K ^ (2 * c + 2) * (K ^ 2 * K))
      ≤ K * (K ^ ((2 * Lm + 1) * (2 * c + 2)) * (K ^ 2 * K)) := by
        refine mul_le_mul hDK (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity) hK0
    _ = K ^ ((2 * Lm + 1) * (2 * c + 2) + 4) := by ring

set_option maxHeartbeats 1000000 in
-- the bounds of the factors are combined in one proof
/-- A package with both `Λ̃`: `P Λ̃ Π_a Λ̃ Π_c` with `P` deterministic, split at the second `Λ̃` as
in (5.72) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_operator_norm_bound], both sides in `ℓ²` by (A.55)
[two_loop_estimate], the left one deterministic for `a = 0`, as in (5.74)
[concrete_bound_type_1_2_3]. -/
private lemma PS_pkg_lam2 {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 1 ≤ K)
    (hD : 1 ≤ D) (hτ' : 0 ≤ τ') (hT : PS_Two D N δA τ c₀ K C Lm τ' D')
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) {e : LoopEnv D N}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (σ : List PkgLetter)
    (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) (hlen : σ.length ≤ Lm)
    (hend : σ.getLast?.map PkgLetter.isRes = some true) (hL : σ.countP PkgLetter.isLam = 2)
    (hfirst : (σ.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0) (κ : ℕ → Idx D N) :
    (∀ h, (Matrix.of h).IsHermitian → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cc K Lm * N ^ 3 * (pkgSegFac σ).val N η m (hsNorm e.A)) 0) ∧
    ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) ∧
      ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cg K Lm * (N : ℝ) ^ τ' * (pkgSegFac σ).val N η m (hsNorm e.A)) 2 := by
  obtain ⟨hη, hm, hηm⟩ := PS_Ctx_pos hc hK
  have hc' := hc
  obtain ⟨hadm, heta, hη1, hm1, -, him, hsLt, hslam, hLt, hM, hE, hDK, hN1⟩ := hc
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨P, o, S, rfl, hPl⟩ := PS_split_lam σ (by omega)
  have hcnt : (P ++ .lw (.lamt o) :: S).countP PkgLetter.isLam =
      P.countP PkgLetter.isLam + 1 + S.countP PkgLetter.isLam := by
    simp [List.countP_append, List.countP_cons, PkgLetter.isLam]; ring
  have hP0 : P.countP PkgLetter.isLam = 0 := List.countP_eq_zero.2 fun y hy => by simp [hPl y hy]
  obtain ⟨W, o', Q, rfl, hWl⟩ := PS_split_lam S (by omega)
  have hcnt2 : (W ++ .lw (.lamt o') :: Q).countP PkgLetter.isLam =
      W.countP PkgLetter.isLam + 1 + Q.countP PkgLetter.isLam := by
    simp [List.countP_append, List.countP_cons, PkgLetter.isLam]; ring
  have hW0 : W.countP PkgLetter.isLam = 0 := List.countP_eq_zero.2 fun y hy => by simp [hWl y hy]
  have hQ0 : Q.countP PkgLetter.isLam = 0 := by omega
  have hQl := PS_lam_free Q hQ0
  have hPr : P.countP PkgLetter.isRes = 0 := by
    rw [(PS_tw P _ (.lw (.lamt o)) hPl rfl).1] at hfirst
    exact hfirst
  have hassoc : P ++ .lw (.lamt o) :: (W ++ .lw (.lamt o') :: Q) =
      (P ++ .lw (.lamt o) :: W) ++ .lw (.lamt o') :: Q := by simp
  have hc1 : 1 ≤ Q.countP PkgLetter.isRes := by
    rw [hassoc] at hend
    exact PS_last_res _ Q o' hend
  have hPe : ∀ x ∈ P, PkgLetter.isEnt x = false := fun x hx => hσ x (by simp [hx])
  have hWe : ∀ x ∈ W, PkgLetter.isEnt x = false := fun x hx => hσ x (by simp [hx])
  have hQe : ∀ x ∈ Q, PkgLetter.isEnt x = false := fun x hx => hσ x (by simp [hx])
  have hlens : P.length + W.length + Q.length + 2 ≤ Lm := by simp at hlen; omega
  set a := W.countP PkgLetter.isRes with hadef
  set c := Q.countP PkgLetter.isRes with hcdef
  have haL : a ≤ W.length := List.countP_le_length
  have hcL : c ≤ Q.length := List.countP_le_length
  have hrr : (P ++ .lw (.lamt o) :: (W ++ .lw (.lamt o') :: Q)).countP PkgLetter.isRes =
      a + c := by
    simp [List.countP_append, PkgLetter.isRes, hPr]
    rfl
  rw [PS_seg_lam2 P W Q o o' hPl hWl hL]
  simp only [PkgFac.val]
  have hha := PS_half_nonneg m hη a
  have hhc := PS_half_nonneg m hη c
  refine ⟨fun h hh => PS_PC_const _ _ 0 (by have := PS_Cc_one K hK Lm; positivity)
    fun x y => ?_, ?_⟩
  · -- the crude bound
    refine (PS_crude_core hc' hK h hh κ _ hσ hlen x y).trans ?_
    rw [hrr, hL]
    have h1 := PS_crude_half hη hη1 hm hm1 hηm a c
    calc η⁻¹ ^ (a + c) * K ^ Lm * (K * hsNorm e.A) ^ 2
        ≤ (K * N) ^ 2 * (pkgHalf η m a * pkgHalf η m c) * K ^ Lm * (K * hsNorm e.A) ^ 2 := by
          gcongr
      _ = K ^ (Lm + 4) * N ^ 3 * (hsNorm e.A ^ 2 / N * pkgHalf η m a * pkgHalf η m c) := by
          field_simp
          ring
      _ = _ := by rw [PS_Cc]
  · set lP := P.map (PS_pl e.s M E e.Lt) with hlP
    set lW := W.map (PS_pl e.s M E e.Lt) with hlW
    set lQ := Q.map (PS_pl e.s M E e.Lt) with hlQ
    have hlPr : PS_nr lP = 0 := by rw [PS_pl_nr]; exact hPr
    have hlWr : PS_nr lW = a := PS_pl_nr _ _ _ _ W
    have hlQr : PS_nr lQ = c := PS_pl_nr _ _ _ _ Q
    have hlPl : lP.length = P.length := by simp [hlP]
    have hlWl : lW.length = W.length := by simp [hlW]
    have hlQl : lQ.length = Q.length := by simp [hlQ]
    have hlPd := PS_pl_det e.s M E e.Lt K hK hM hE P hPl
    have hlWd := PS_pl_det e.s M E e.Lt K hK hM hE W hWl
    have hlQd := PS_pl_det e.s M E e.Lt K hK hM hE Q hQl
    have hmatσ : ∀ h, (Matrix.of h).IsHermitian →
        pkgWordMat (e.G h) M E e.Lt κ (P ++ .lw (.lamt o) :: (W ++ .lw (.lamt o') :: Q)) =
          (PS_v (PS_Gr e h) lP * e.Lt * PS_v (PS_Gr e h) lW) * (e.Lt * PS_v (PS_Gr e h) lQ) := by
      intro h hh
      rw [PS_mat_lam, PS_mat_lam, PS_mat e h hh M E κ P hPe, PS_mat e h hh M E κ W hWe,
        PS_mat e h hh M E κ Q hQe]
      simp only [Matrix.mul_assoc]
      rfl
    have hKf : max (K ^ (2 * Lm)) K ≤ K ^ (2 * Lm + 1) :=
      max_le (pow_le_pow_right₀ hK (by omega))
        (le_trans (le_of_eq (pow_one K).symm) (pow_le_pow_right₀ hK (by omega)))
    have hKf1 : 1 ≤ max (K ^ (2 * Lm)) K := le_max_of_le_right hK
    have hbc := PS_bnd hη heta hK him (2 * c)
    have hbc0 := PS_b_nonneg hadm (2 * c)
    have hψc := PS_half_sq hη hm.le hc1
    have hslam0 : 0 ≤ hsNorm (lam D N e.A) := Real.sqrt_nonneg _
    obtain ⟨-, gQ2, -, gQ4, -, gQ6⟩ := PS_gram_facts lQ K hlQd
    have hψev := hT (2 * c) (by omega) (by omega) μ hμ e hadm (lQ ++ lQ.reverse.map PS_adj) []
      (by rw [gQ2, hlQr]) rfl (by rw [gQ4]; omega) (by simp) gQ6 (by simp)
    set Eψ : Set (Idx D N → Idx D N → ℂ) := {h | (N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^
        (2 * c + 0 + 2) * (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * c + 0))) <
      ‖ntr (PS_v (PS_Gr e h) (lQ ++ lQ.reverse.map PS_adj) * e.Lt * PS_v (PS_Gr e h) [] *
        e.Lt)‖} with hEψ
    -- the column side, in `ℓ²` by (A.55)
    set K₃ : ℝ := D * (max (K ^ (2 * Lm)) K ^ (2 * c + 2) * (K ^ 2 * K)) with hK₃
    have hK₃1 : 1 ≤ K₃ := one_le_mul_of_one_le_of_one_le hD1 (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hKf1) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) hK))
    have hψbound : ∀ h, (Matrix.of h).IsHermitian → h ∉ Eψ →
        ∑ y, (Real.sqrt (∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k y‖ ^ 2)) ^ 2 ≤
          (hsNorm e.A * pkgHalf η m c) ^ 2 * ((N : ℝ) ^ τ' * K₃) := by
      intro h hh hb
      simp only [hEψ, Set.mem_ofPred_eq, not_lt] at hb
      rw [add_zero, (PS_v_gram (PS_Gr e h) lQ).2, PS_v_nil] at hb
      have e1 : ∑ y, (Real.sqrt (∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k y‖ ^ 2)) ^ 2 =
          ∑ y, ∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k y‖ ^ 2 :=
        Finset.sum_congr rfl fun y _ => Real.sq_sqrt (by positivity)
      rw [e1]
      refine (PS_cols_lt e _).trans ?_
      calc (D : ℝ) * N * ‖ntr (PS_v (PS_Gr e h) lQ * (PS_v (PS_Gr e h) lQ)ᴴ * e.Lt * 1 * e.Lt)‖
          ≤ D * N * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * c + 2) *
              (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * c)))) := by gcongr
        _ = D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * c + 2) *
              (hsNorm (lam D N e.A) ^ 2 * PS_b e (2 * c)))) := by field_simp
        _ ≤ D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * c + 2) *
              ((K * hsNorm e.A) ^ 2 * (K * pkgPsi η m (2 * c))))) := by
            gcongr
        _ = (hsNorm e.A * pkgHalf η m c) ^ 2 * ((N : ℝ) ^ τ' * K₃) := by
            rw [hψc, hK₃]; ring
    have hcs : ∀ h, (Matrix.of h).IsHermitian → ∀ x y,
        ‖pkgWordMat (e.G h) M E e.Lt κ (P ++ .lw (.lamt o) :: (W ++ .lw (.lamt o') :: Q)) x y‖ ≤
          (Real.sqrt (∑ k, ‖(PS_v (PS_Gr e h) lP * e.Lt * PS_v (PS_Gr e h) lW) x k‖ ^ 2) +
            Real.sqrt (∑ k, ‖(PS_v (PS_Gr e h) lP * e.Lt * PS_v (PS_Gr e h) lW) y k‖ ^ 2)) *
          (Real.sqrt (∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k x‖ ^ 2) +
            Real.sqrt (∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k y‖ ^ 2)) := by
      intro h hh x y
      rw [hmatσ h hh]
      refine (PS_entry_cs _ _ x y).trans ?_
      exact mul_le_mul (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
    have hNτ1 : (1 : ℝ) ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hNr hτ'
    rcases Nat.eq_zero_or_pos a with ha0 | ha1
    · -- `a = 0`: the left side `P Λ̃ Π₀` is deterministic
      have hWr : W.countP PkgLetter.isRes = 0 := ha0
      set Y : Matrix (Idx D N) (Idx D N) ℂ := pkgWordMat (fun _ => 0) M E e.Lt κ P * e.Lt *
        pkgWordMat (fun _ => 0) M E e.Lt κ W with hY
      have hYeq : ∀ h, (Matrix.of h).IsHermitian →
          PS_v (PS_Gr e h) lP * e.Lt * PS_v (PS_Gr e h) lW = Y := by
        intro h hh
        rw [← PS_mat e h hh M E κ P hPe, ← PS_mat e h hh M E κ W hWe,
          PS_mat_det (e.G h) (fun _ => 0) M E e.Lt κ P hPr,
          PS_mat_det (e.G h) (fun _ => 0) M E e.Lt κ W hWr]
      have hn : ∀ X : List PkgLetter, (∀ x ∈ X, PkgLetter.isEnt x = false) →
          X.countP PkgLetter.isRes = 0 → X.countP PkgLetter.isLam = 0 → X.length ≤ Lm →
          opNorm (pkgWordMat (fun _ => 0) M E e.Lt κ X) ≤ K ^ Lm := by
        intro X hXe hXr hXl hXL
        have := PS_mat_norm (fun _ => 0) M E e.Lt κ 0 K (opNorm e.Lt) le_rfl hK
          (Bd_opNorm_nonneg _) (fun _ => by simp [opNorm]) hM hE le_rfl X hXe
        rw [hXr, hXl, pow_zero, pow_zero, one_mul, mul_one] at this
        exact this.trans (pow_le_pow_right₀ hK hXL)
      have hnP := hn P hPe hPr hP0 (by omega)
      have hnW := hn W hWe hWr hW0 (by omega)
      set Tφ : ℝ := K ^ Lm * K ^ Lm * (K * hsNorm e.A) with hTφ
      have hφT : ∑ x, (Real.sqrt (∑ k, ‖Y x k‖ ^ 2)) ^ 2 ≤ Tφ ^ 2 := by
        have e1 : ∑ x, (Real.sqrt (∑ k, ‖Y x k‖ ^ 2)) ^ 2 = MultiRes_hs2 Y :=
          Finset.sum_congr rfl fun x _ => Real.sq_sqrt (by positivity)
        rw [e1]
        have h1 := MultiRes_hs2_mul_right_le (pkgWordMat (fun _ => 0) M E e.Lt κ P * e.Lt)
          (pkgWordMat (fun _ => 0) M E e.Lt κ W)
        have h2 := MultiRes_hs2_mul_left_le (pkgWordMat (fun _ => 0) M E e.Lt κ P) e.Lt
        have h3 : MultiRes_hs2 e.Lt ≤ (K * hsNorm e.A) ^ 2 := by
          rw [← MultiRes_hsNorm_sq]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsLt 2
        have h4 : (0 : ℝ) ≤ MultiRes_hs2 e.Lt := by unfold MultiRes_hs2; positivity
        calc MultiRes_hs2 Y ≤ MultiRes_hs2 (pkgWordMat (fun _ => 0) M E e.Lt κ P * e.Lt) *
              opNorm (pkgWordMat (fun _ => 0) M E e.Lt κ W) ^ 2 := h1
          _ ≤ (opNorm (pkgWordMat (fun _ => 0) M E e.Lt κ P) ^ 2 * MultiRes_hs2 e.Lt) *
              (K ^ Lm) ^ 2 := mul_le_mul h2 (pow_le_pow_left₀ (Bd_opNorm_nonneg _) hnW 2)
                (by positivity) (by positivity)
          _ ≤ ((K ^ Lm) ^ 2 * (K * hsNorm e.A) ^ 2) * (K ^ Lm) ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (Bd_opNorm_nonneg _) hnP 2)
                h3 h4 (by positivity)) (by positivity)
          _ = Tφ ^ 2 := by rw [hTφ]; ring
      refine ⟨Eψ, hψev.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh hb => ?_⟩
      · have := Real.rpow_nonneg (Nat.cast_nonneg N) (-D')
        have hDN : (1 : ℝ) ≤ D * N := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D * N - 1)
          (by linarith : (0 : ℝ) ≤ D * N + 1)) this]
      · set ψ : Idx D N → ℝ := fun y => Real.sqrt (∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k y‖ ^ 2)
          with hψd
        set φ : Idx D N → ℝ := fun x => Real.sqrt (∑ k, ‖Y x k‖ ^ 2) with hφd
        set Tψ : ℝ := Real.sqrt ((hsNorm e.A * pkgHalf η m c) ^ 2 * ((N : ℝ) ^ τ' * K₃))
          with hTψ
        have hψT : ∑ y, ψ y ^ 2 ≤ Tψ ^ 2 := by
          rw [hTψ, Real.sq_sqrt (by positivity)]
          exact hψbound h hh hb
        refine ⟨1, [(φ, Tφ), (ψ, Tψ)], le_rfl, fun t ht => ?_, zero_le_one, fun x y => ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact ⟨fun x => Real.sqrt_nonneg _, hφT, by positivity⟩
          · exact ⟨fun x => Real.sqrt_nonneg _, hψT, Real.sqrt_nonneg _⟩
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
          have := hcs h hh x y
          rw [hYeq h hh] at this
          exact this
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul,
            List.length_cons, List.length_nil, zero_add]
          rw [hsq]
          have hTψ' : Tψ ≤ hsNorm e.A * pkgHalf η m c * ((N : ℝ) ^ τ' * K₃) :=
            PS_sqrt_le _ _ (by positivity) (one_le_mul_of_one_le_of_one_le hNτ1 hK₃1)
          have hKe : K ^ Lm * K ^ Lm * K * K₃ ≤ PS_Cg K Lm := by
            refine (mul_le_mul_of_nonneg_left (PS_K3_le hK hDK Lm c) (by positivity)).trans ?_
            rw [← pow_add, ← pow_succ, ← pow_add]
            refine PS_Cg_ge K hK Lm _ ?_
            have := Nat.mul_le_mul_left (2 * Lm + 1) (show 2 * c + 2 ≤ 2 * Lm + 2 by omega)
            nlinarith
          have ha0' : pkgHalf η m a = 1 := by rw [ha0]; simp [pkgHalf]
          rw [ha0']
          calc Tφ * Tψ ≤ Tφ * (hsNorm e.A * pkgHalf η m c * ((N : ℝ) ^ τ' * K₃)) :=
                mul_le_mul_of_nonneg_left hTψ' (by positivity)
            _ = (K ^ Lm * K ^ Lm * K * K₃) * (N : ℝ) ^ τ' * (hsNorm e.A ^ 2 * pkgHalf η m c) := by
                rw [hTφ]; ring
            _ ≤ PS_Cg K Lm * (N : ℝ) ^ τ' * (hsNorm e.A ^ 2 * pkgHalf η m c) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKe (by positivity))
                  (mul_nonneg (by positivity) hhc)
            _ = PS_Cg K Lm * (N : ℝ) ^ τ' * (hsNorm e.A ^ 2 / N * 1 * pkgHalf η m c) * N := by
                field_simp
    · -- `a ≥ 1`: both sides in `ℓ²` by (A.55)
      obtain ⟨-, gW2, -, gW4, -, gW6⟩ := PS_gram_facts lW K hlWd
      obtain ⟨gP1, -, gP3, -, gP5, -⟩ := PS_gram_facts lP K hlPd
      have hφev := hT (2 * a) (by omega) (by omega) μ hμ e hadm (lW ++ lW.reverse.map PS_adj)
        (lP.reverse.map PS_adj ++ lP) (by rw [gW2, hlWr]) (by rw [gP1, hlPr])
        (by rw [gW4]; omega) (by rw [gP3]; omega) gW6 gP5
      set Eφ : Set (Idx D N → Idx D N → ℂ) := {h | (N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^
          (2 * a + 0 + 2) * (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * a + 0))) <
        ‖ntr (PS_v (PS_Gr e h) (lW ++ lW.reverse.map PS_adj) * e.Lt *
          PS_v (PS_Gr e h) (lP.reverse.map PS_adj ++ lP) * e.Lt)‖} with hEφ
      set K₄ : ℝ := D * (max (K ^ (2 * Lm)) K ^ (2 * a + 2) * (K ^ 2 * K)) with hK₄
      have hK₄1 : 1 ≤ K₄ := one_le_mul_of_one_le_of_one_le hD1 (one_le_mul_of_one_le_of_one_le
        (one_le_pow₀ hKf1) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) hK))
      have hba := PS_bnd hη heta hK him (2 * a)
      have hba0 := PS_b_nonneg hadm (2 * a)
      have hψa := PS_half_sq hη hm.le ha1
      refine ⟨Eψ ∪ Eφ, ?_, fun h hh hb => ?_⟩
      · refine (measure_union_le _ _).trans ((add_le_add hψev hφev).trans ?_)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := Real.rpow_nonneg (Nat.cast_nonneg N) (-D')
        have hDN : (1 : ℝ) ≤ D * N := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D * N - 1)
          (by linarith : (0 : ℝ) ≤ D * N + 1)) this]
      · have hbψ : h ∉ Eψ := fun hm' => hb (Or.inl hm')
        have hbφ : h ∉ Eφ := fun hm' => hb (Or.inr hm')
        simp only [hEφ, Set.mem_ofPred_eq, not_lt] at hbφ
        rw [add_zero, (PS_v_gram (PS_Gr e h) lW).2, (PS_v_gram (PS_Gr e h) lP).1] at hbφ
        set ψ : Idx D N → ℝ := fun y => Real.sqrt (∑ k, ‖(e.Lt * PS_v (PS_Gr e h) lQ) k y‖ ^ 2)
          with hψd
        set φ : Idx D N → ℝ := fun x => Real.sqrt (∑ k, ‖(PS_v (PS_Gr e h) lP * e.Lt *
          PS_v (PS_Gr e h) lW) x k‖ ^ 2) with hφd
        set Tψ : ℝ := Real.sqrt ((hsNorm e.A * pkgHalf η m c) ^ 2 * ((N : ℝ) ^ τ' * K₃))
          with hTψ
        set Tφ : ℝ := Real.sqrt ((hsNorm e.A * pkgHalf η m a) ^ 2 * ((N : ℝ) ^ τ' * K₄))
          with hTφ
        have hψT : ∑ y, ψ y ^ 2 ≤ Tψ ^ 2 := by
          rw [hTψ, Real.sq_sqrt (by positivity)]
          exact hψbound h hh hbψ
        have hφT : ∑ x, φ x ^ 2 ≤ Tφ ^ 2 := by
          rw [hTφ, Real.sq_sqrt (by positivity)]
          have e1 : ∑ x, φ x ^ 2 = ∑ x, ∑ k, ‖(PS_v (PS_Gr e h) lP * e.Lt *
              PS_v (PS_Gr e h) lW) x k‖ ^ 2 :=
            Finset.sum_congr rfl fun x _ => Real.sq_sqrt (by positivity)
          rw [e1]
          refine (PS_rows_lt2 e _ _).trans ?_
          calc (D : ℝ) * N * ‖ntr (PS_v (PS_Gr e h) lW * (PS_v (PS_Gr e h) lW)ᴴ * e.Lt *
                ((PS_v (PS_Gr e h) lP)ᴴ * PS_v (PS_Gr e h) lP) * e.Lt)‖
              ≤ D * N * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * a + 2) *
                  (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * a)))) := by gcongr
            _ = D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * a + 2) *
                  (hsNorm (lam D N e.A) ^ 2 * PS_b e (2 * a)))) := by field_simp
            _ ≤ D * ((N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (2 * a + 2) *
                  ((K * hsNorm e.A) ^ 2 * (K * pkgPsi η m (2 * a))))) := by
                gcongr
            _ = (hsNorm e.A * pkgHalf η m a) ^ 2 * ((N : ℝ) ^ τ' * K₄) := by
                rw [hψa, hK₄]; ring
        refine ⟨1, [(φ, Tφ), (ψ, Tψ)], le_rfl, fun t ht => ?_, zero_le_one, fun x y => ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact ⟨fun x => Real.sqrt_nonneg _, hφT, Real.sqrt_nonneg _⟩
          · exact ⟨fun x => Real.sqrt_nonneg _, hψT, Real.sqrt_nonneg _⟩
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
          exact hcs h hh x y
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul,
            List.length_cons, List.length_nil, zero_add]
          rw [hsq, hTφ, hTψ, ← Real.sqrt_mul (by positivity)]
          have hprod : (hsNorm e.A * pkgHalf η m a) ^ 2 * ((N : ℝ) ^ τ' * K₄) *
              ((hsNorm e.A * pkgHalf η m c) ^ 2 * ((N : ℝ) ^ τ' * K₃)) =
              ((N : ℝ) ^ τ' * (hsNorm e.A ^ 2 * pkgHalf η m a * pkgHalf η m c)) ^ 2 *
                (K₄ * K₃) := by ring
          rw [hprod]
          refine (PS_sqrt_le _ _ (by positivity) (one_le_mul_of_one_le_of_one_le hK₄1 hK₃1)).trans
            ?_
          have hKe : K₄ * K₃ ≤ PS_Cg K Lm := by
            refine (mul_le_mul (PS_K3_le hK hDK Lm a) (PS_K3_le hK hDK Lm c) (by positivity)
              (by positivity)).trans ?_
            rw [← pow_add]
            refine PS_Cg_ge K hK Lm _ ?_
            have := Nat.mul_le_mul_left (2 * Lm + 1) (show 2 * a + 2 + (2 * c + 2) ≤ 2 * Lm + 4 by
              omega)
            nlinarith
          calc (N : ℝ) ^ τ' * (hsNorm e.A ^ 2 * pkgHalf η m a * pkgHalf η m c) * (K₄ * K₃)
              ≤ (N : ℝ) ^ τ' * (hsNorm e.A ^ 2 * pkgHalf η m a * pkgHalf η m c) * PS_Cg K Lm :=
                mul_le_mul_of_nonneg_left hKe (mul_nonneg (by positivity)
                  (mul_nonneg (mul_nonneg (by positivity) hha) hhc))
            _ = PS_Cg K Lm * (N : ℝ) ^ τ' * (hsNorm e.A ^ 2 / N * pkgHalf η m a *
                pkgHalf η m c) * N := by
                field_simp

end PkgLam2

/-! ## Loops without `Δ` -/

section Loops

variable {D N : ℕ}

private lemma PS_ev1 (hD : 1 ≤ D) (hN : 1 ≤ N) (D' : ℝ) :
    ENNReal.ofReal ((N : ℝ) ^ (-D')) ≤
      ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.rpow_nonneg (Nat.cast_nonneg N) (-D')
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hDN : (1 : ℝ) ≤ D * N := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D * N - 1)
    (by linarith : (0 : ℝ) ≤ D * N + 1)) this]

/-- The factor of a word without `Δ`. -/
private def PS_lf (w : List PkgLetter) : PkgFac :=
  match w.countP PkgLetter.isLam with
  | 0 => .free (w.countP PkgLetter.isRes)
  | 1 => if w.countP PkgLetter.isRes = 0 then .lam0 (pkgGainLoop w)
    else .lam1 (w.countP PkgLetter.isRes)
  | _ => .lam2 0 (w.countP PkgLetter.isRes)

private lemma PS_lf_fac (pr : Fin 2 → Bool) (w : List PkgLetter)
    (hw : w.any PkgLetter.isEnt = false) : pkgWordFac pr w = [PS_lf w] := by
  unfold pkgWordFac PS_lf
  simp only [hw, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · split_ifs <;> rfl
  · rfl

set_option maxHeartbeats 1000000 in
-- the bounds of the factors are combined in one proof
/-- A loop `⟨·⟩` with at most one `Λ̃`: (A.53) [entprodG] averaged, (A.54) [one_loop_estimate], or
the deterministic bound (A.7) [add_one_more_Lambda] given by `h0` when it has no resolvent. -/
private lemma PS_loop {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 1 ≤ K)
    (hD : 1 ≤ D) (hτ' : 0 ≤ τ') (hI : PS_Iso D N δA τ c₀ K C Lm τ' D')
    (hO : PS_One D N δA τ c₀ K C Lm τ' D')
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) {e : LoopEnv D N}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (havg : avgSq (lam D N e.A) ≤ K * (hsNorm e.A ^ 2 / N))
    (w : List PkgLetter) (hw : ∀ x ∈ w, PkgLetter.isEnt x = false) (hlen : w.length ≤ Lm)
    (hL : w.countP PkgLetter.isLam ≤ 1) (hr : w.countP PkgLetter.isLam = 0 →
      1 ≤ w.countP PkgLetter.isRes) (κ : ℕ → Idx D N)
    (h0 : w.countP PkgLetter.isLam = 1 → w.countP PkgLetter.isRes = 0 →
      ∀ h, ‖ntr (pkgWordMat (e.G h) M E e.Lt κ w)‖ ≤
        K * ((if pkgGainLoop w then m else 1) * avgSq (lam D N e.A))) :
    (∀ h, (Matrix.of h).IsHermitian → ‖ntr (pkgWordMat (e.G h) M E e.Lt κ w)‖ ≤
        PS_Cc K Lm * N ^ 3 * (PS_lf w).val N η m (hsNorm e.A)) ∧
    ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) ∧
      ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → ‖ntr (pkgWordMat (e.G h) M E e.Lt κ w)‖ ≤
        PS_Cg K Lm * (N : ℝ) ^ τ' * (PS_lf w).val N η m (hsNorm e.A) := by
  obtain ⟨hη, hm, hηm⟩ := PS_Ctx_pos hc hK
  have hc' := hc
  obtain ⟨hadm, heta, hη1, hm1, -, him, hsLt, hslam, hLt, hM, hE, hDK, hN1⟩ := hc
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  have hNτ1 : (1 : ℝ) ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hNr hτ'
  have hN3 : (N : ℝ) ≤ N ^ 3 :=
    (pow_one (N : ℝ)).symm.le.trans (pow_le_pow_right₀ hNr (by norm_num))
  have hcrude : ∀ h, (Matrix.of h).IsHermitian → ‖ntr (pkgWordMat (e.G h) M E e.Lt κ w)‖ ≤
      η⁻¹ ^ w.countP PkgLetter.isRes * K ^ Lm * (K * hsNorm e.A) ^ w.countP PkgLetter.isLam := by
    intro h hh
    refine (Bd_ntr_le _).trans ((PS_mat_norm (e.G h) M E e.Lt κ η⁻¹ K (K * hsNorm e.A)
      (by positivity) hK (by positivity) (PS_G_norm hc' h hh) hM hE hLt w hw).trans ?_)
    gcongr
  have hdet : 1 ≤ PS_Cg K Lm := PS_Cg_one K hK Lm
  have hdetc : 1 ≤ PS_Cc K Lm := PS_Cc_one K hK Lm
  set r := w.countP PkgLetter.isRes with hrdef
  rcases Nat.eq_zero_or_pos (w.countP PkgLetter.isLam) with hl0 | hl1
  · -- no `Λ̃`
    have hr1 := hr hl0
    have hf : PS_lf w = .free r := by
      unfold PS_lf
      rw [hl0]
      rfl
    rw [hf]
    simp only [PkgFac.val]
    have hψ := PS_psi_nonneg hη hm.le r
    refine ⟨fun h hh => ?_, ?_⟩
    · refine (hcrude h hh).trans ?_
      rw [hl0, pow_zero, mul_one]
      have h1 := PS_crude_psi hη hm hm1 hηm hr1
      have hKp : K ^ (Lm + 1) ≤ K ^ (Lm + 4) := pow_le_pow_right₀ hK (by omega)
      calc η⁻¹ ^ r * K ^ Lm ≤ K * N * pkgPsi η m r * K ^ Lm :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = K ^ (Lm + 1) * N * pkgPsi η m r := by ring
        _ ≤ K ^ (Lm + 4) * N ^ 3 * pkgPsi η m r :=
            mul_le_mul_of_nonneg_right (mul_le_mul hKp hN3 (by positivity) (by positivity)) hψ
    · set l := w.map (PS_pl e.s M E e.Lt) with hl
      have hlr : PS_nr l = r := PS_pl_nr _ _ _ _ w
      have hll : l.length ≤ 2 * Lm := by simp only [hl, List.length_map]; omega
      have hld := PS_pl_det e.s M E e.Lt K hK hM hE w (PS_lam_free w hl0)
      have hrL : r ≤ 2 * Lm := List.countP_le_length.trans (by omega)
      refine ⟨_, (hI r hr1 hrL μ hμ e hadm l hlr hll hld).1.trans (PS_ev1 hD hN1 D'),
        fun h hh hb => ?_⟩
      simp only [Set.mem_ofPred_eq, not_lt] at hb
      rw [PS_mat e h hh M E κ w hw]
      refine hb.trans ?_
      have hb' : PS_b e r ≤ K * pkgPsi η m r := PS_bnd hη heta hK him r
      calc (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * PS_b e r)
          ≤ (N : ℝ) ^ τ' * ((K ^ (2 * Lm)) ^ (r + 1) * (K * pkgPsi η m r)) := by gcongr
        _ = K ^ (2 * Lm * (r + 1) + 1) * (N : ℝ) ^ τ' * pkgPsi η m r := by
            rw [pow_succ, pow_mul]; ring
        _ ≤ PS_Cg K Lm * (N : ℝ) ^ τ' * pkgPsi η m r := by
            gcongr
            refine PS_Cg_ge K hK Lm _ ?_
            nlinarith
  · have hl1' : w.countP PkgLetter.isLam = 1 := by omega
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · -- one `Λ̃` and no resolvent: the deterministic bound
      have hr0' : w.countP PkgLetter.isRes = 0 := hr0
      have hf : PS_lf w = .lam0 (pkgGainLoop w) := by
        unfold PS_lf
        rw [hl1']
        simp only [hr0', ↓reduceIte]
      rw [hf]
      simp only [PkgFac.val]
      have hb := h0 hl1' hr0
      have hg : 0 ≤ (if pkgGainLoop w then m else 1) := by split_ifs <;> linarith
      have hav : ∀ h, ‖ntr (pkgWordMat (e.G h) M E e.Lt κ w)‖ ≤
          K ^ 2 * ((if pkgGainLoop w then m else 1) * (hsNorm e.A ^ 2 / N)) := by
        intro h
        refine (hb h).trans ?_
        calc K * ((if pkgGainLoop w then m else 1) * avgSq (lam D N e.A))
            ≤ K * ((if pkgGainLoop w then m else 1) * (K * (hsNorm e.A ^ 2 / N))) := by gcongr
          _ = K ^ 2 * ((if pkgGainLoop w then m else 1) * (hsNorm e.A ^ 2 / N)) := by ring
      have hv0 : 0 ≤ (if pkgGainLoop w then m else 1) * (hsNorm e.A ^ 2 / N) := by positivity
      refine ⟨fun h _ => (hav h).trans ?_, ∅, by simp, fun h _ _ => (hav h).trans ?_⟩
      · have : K ^ 2 ≤ PS_Cc K Lm * N ^ 3 := by
          rw [PS_Cc]
          nlinarith [pow_le_pow_right₀ hK (show 2 ≤ Lm + 4 by omega),
            one_le_pow₀ (M₀ := ℝ) hNr (n := 3)]
        exact mul_le_mul_of_nonneg_right this hv0
      · have : K ^ 2 ≤ PS_Cg K Lm * (N : ℝ) ^ τ' := by
          have := PS_Cg_ge K hK Lm 2 (by nlinarith)
          nlinarith
        exact mul_le_mul_of_nonneg_right this hv0
    · -- one `Λ̃` and `r ≥ 1` resolvents: (A.54)
      have hr0' : w.countP PkgLetter.isRes ≠ 0 := by omega
      have hf : PS_lf w = .lam1 r := by
        unfold PS_lf
        rw [hl1']
        simp only [hr0', ↓reduceIte]
        rfl
      rw [hf]
      simp only [PkgFac.val]
      have hψ := PS_psi_nonneg hη hm.le r
      obtain ⟨hhalf, hN3'⟩ := PS_half_facts hN1
      refine ⟨fun h hh => ?_, ?_⟩
      · refine (hcrude h hh).trans ?_
        rw [hl1', pow_one]
        have h1 := PS_crude_psi hη hm hm1 hηm hr1
        have hKp : K ^ (Lm + 2) ≤ K ^ (Lm + 4) := pow_le_pow_right₀ hK (by omega)
        calc η⁻¹ ^ r * K ^ Lm * (K * hsNorm e.A)
            ≤ K * N * pkgPsi η m r * K ^ Lm * (K * hsNorm e.A) := by gcongr
          _ = K ^ (Lm + 2) * N * (hsNorm e.A * pkgPsi η m r) := by ring
          _ ≤ K ^ (Lm + 4) * (N ^ 3 * (N : ℝ) ^ (-(1 / 2 : ℝ))) * (hsNorm e.A * pkgPsi η m r) :=
              by gcongr
          _ = _ := by rw [PS_Cc]; ring
      · obtain ⟨P, o, Q, hwPQ, hP⟩ := PS_split_lam w (by omega)
        have hPe : ∀ x ∈ P, PkgLetter.isEnt x = false := fun x hx => hw x (by simp [hwPQ, hx])
        have hQe : ∀ x ∈ Q, PkgLetter.isEnt x = false := fun x hx => hw x (by simp [hwPQ, hx])
        have hcnt : w.countP PkgLetter.isLam =
            P.countP PkgLetter.isLam + 1 + Q.countP PkgLetter.isLam := by
          rw [hwPQ]; simp [List.countP_append, List.countP_cons, PkgLetter.isLam]; ring
        have hQ0 : Q.countP PkgLetter.isLam = 0 := by omega
        have hQ := PS_lam_free Q hQ0
        have hrr : r = Q.countP PkgLetter.isRes + P.countP PkgLetter.isRes := by
          rw [hrdef, hwPQ]; simp [List.countP_append, PkgLetter.isRes]; ring
        set l := Q.map (PS_pl e.s M E e.Lt) ++ P.map (PS_pl e.s M E e.Lt) with hl
        have hlr : PS_nr l = r := by rw [hl, PS_nr_append, PS_pl_nr, PS_pl_nr, hrr]
        have hll : l.length ≤ 2 * Lm := by
          have : w.length = P.length + 1 + Q.length := by rw [hwPQ]; simp; ring
          simp only [hl, List.length_append, List.length_map]; omega
        have hld : ∀ B, Sum.inr B ∈ l → opNorm B ≤ K := by
          intro B hB
          rcases List.mem_append.1 hB with hB | hB
          · exact PS_pl_det e.s M E e.Lt K hK hM hE Q hQ B hB
          · exact PS_pl_det e.s M E e.Lt K hK hM hE P hP B hB
        have hrL : r ≤ 2 * Lm := List.countP_le_length.trans (by omega)
        refine ⟨_, (hO r hr1 hrL μ hμ e hadm l hlr hll hld).trans (PS_ev1 hD hN1 D'),
          fun h hh hb => ?_⟩
        simp only [Set.mem_ofPred_eq, not_lt] at hb
        have hmat : ntr (pkgWordMat (e.G h) M E e.Lt κ w) = ntr (PS_v (PS_Gr e h) l * e.Lt) := by
          rw [hwPQ, PS_mat_lam, PS_mat e h hh M E κ P hPe, PS_mat e h hh M E κ Q hQe, hl,
            PS_v_append]
          unfold ntr
          congr 1
          rw [Matrix.trace_mul_comm (PS_v (PS_Gr e h) (P.map (PS_pl e.s M E e.Lt)) * e.Lt),
            Matrix.mul_assoc]
        rw [hmat]
        refine hb.trans ?_
        have hb' : PS_b e r ≤ K * pkgPsi η m r := PS_bnd hη heta hK him r
        have hKf : max (K ^ (2 * Lm)) K ≤ K ^ (2 * Lm + 1) :=
          max_le (pow_le_pow_right₀ hK (by omega))
            (le_trans (le_of_eq (pow_one K).symm) (pow_le_pow_right₀ hK (by omega)))
        have hKf0 : 0 ≤ max (K ^ (2 * Lm)) K := le_trans zero_le_one (le_max_of_le_right hK)
        have hslam0 : 0 ≤ hsNorm (lam D N e.A) := Real.sqrt_nonneg _
        have hb0 := PS_b_nonneg hadm r
        calc (N : ℝ) ^ τ' * (max (K ^ (2 * Lm)) K ^ (r + 1) * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
              hsNorm (lam D N e.A) * PS_b e r))
            ≤ (N : ℝ) ^ τ' * ((K ^ (2 * Lm + 1)) ^ (r + 1) * ((N : ℝ) ^ (-(1 / 2 : ℝ)) *
              (K * hsNorm e.A) * (K * pkgPsi η m r))) := by gcongr
          _ = K ^ ((2 * Lm + 1) * (r + 1) + 2) * (N : ℝ) ^ τ' *
              ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm e.A * pkgPsi η m r) := by
              ring
          _ ≤ PS_Cg K Lm * (N : ℝ) ^ τ' *
              ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm e.A * pkgPsi η m r) := by
              gcongr
              refine PS_Cg_ge K hK Lm _ ?_
              nlinarith

end Loops

/-! ## Words with `Δ`: from the packages to the trace -/

section WordFC

variable {D N : ℕ}

/-- The largest entry of `X` at the labels `i, j`. -/
private def PS_mx (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) : ℝ :=
  max (max ‖X i i‖ ‖X i j‖) (max ‖X j i‖ ‖X j j‖)

private lemma PS_mx_nonneg (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) :
    0 ≤ PS_mx X i j :=
  (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

private lemma PS_mx_ge (X : Matrix (Idx D N) (Idx D N) ℂ) (i j a b : Idx D N)
    (ha : a = i ∨ a = j) (hb : b = i ∨ b = j) : ‖X a b‖ ≤ PS_mx X i j := by
  unfold PS_mx
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

private lemma PS_PC_FC {X : Matrix (Idx D N) (Idx D N) ℂ} {V : ℝ} {k : ℕ} (h : PS_PC X V k) :
    PS_FC (PS_mx X) V k := by
  obtain ⟨c, L, hl, hL, hc, hbd, hv⟩ := h
  refine ⟨c, L, hl, hL, hc, fun i j => ?_, hv⟩
  have key : ∀ a b, (a = i ∨ a = j) → (b = i ∨ b = j) →
      ‖X a b‖ ≤ c * (L.map fun t => 2 * (t.1 i + t.1 j)).prod := by
    intro a b ha hb
    refine (hbd a b).trans (mul_le_mul_of_nonneg_left ?_ hc)
    refine List.prod_map_le_prod_map₀ _ _ (fun t ht => ?_) (fun t ht => ?_)
    · have := (hL t ht).1
      linarith [this a, this b]
    · have h0 := (hL t ht).1
      have h1 : t.1 a ≤ t.1 i + t.1 j := by
        rcases ha with ha | ha <;> rw [ha] <;> linarith [h0 i, h0 j]
      have h2 : t.1 b ≤ t.1 i + t.1 j := by
        rcases hb with hb | hb <;> rw [hb] <;> linarith [h0 i, h0 j]
      linarith
  unfold PS_mx
  exact max_le (max_le (key i i (Or.inl rfl) (Or.inl rfl)) (key i j (Or.inl rfl) (Or.inr rfl)))
    (max_le (key j i (Or.inr rfl) (Or.inl rfl)) (key j j (Or.inr rfl) (Or.inr rfl)))

private lemma PS_PC_mono {X : Matrix (Idx D N) (Idx D N) ℂ} {V : ℝ} {k k' : ℕ} (h : PS_PC X V k)
    (hk : k ≤ k') : PS_PC X V k' := by
  obtain ⟨c, L, hl, hL, hc, hb, hv⟩ := h
  exact ⟨c, L, hl.trans hk, hL, hc, hb, hv⟩

/-- The packages of a word have no letter `Δ`. -/
private lemma PS_segs_free (w : List PkgLetter) :
    ∀ σ ∈ pkgSegs w, ∀ x ∈ σ, PkgLetter.isEnt x = false :=
  (PB_segs_count (fun _ => false) (fun _ _ => rfl) w).2.2.1

/-- The packages of a word are not longer than it. -/
private lemma PS_segs_len (w : List PkgLetter) : ∀ σ ∈ pkgSegs w, σ.length ≤ w.length :=
  (PB_segs_count (fun _ => false) (fun _ _ => rfl) w).2.2.2

/-- The letters `Λ̃` of a word are those of its packages. -/
private lemma PS_segs_lam (w : List PkgLetter) :
    ((pkgSegs w).map (List.countP PkgLetter.isLam)).sum = w.countP PkgLetter.isLam :=
  (PB_segs_count PkgLetter.isLam (fun x hx => by
    rcases x with x | ⟨u, v⟩ <;> simp_all [isEntP, PkgLetter.isLam]) w).1

/-- A word without `Δ` does not depend on the entry labels. -/
private lemma PS_mat_kappa (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ κ' : ℕ → Idx D N)
    (σ : List PkgLetter) (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) :
    pkgWordMat G M E L κ σ = pkgWordMat G M E L κ' σ := by
  rw [PB_matL G M E L κ σ hσ, PB_matL G M E L κ' σ hσ]

/-- The trace of a word with `Δ` at the labels `0 ↦ i`, `1 ↦ j` from bounds on its packages. -/
private lemma PS_word_FC (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ₀ : ℕ → Idx D N)
    (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) (V : List PkgLetter → ℝ)
    (k : List PkgLetter → ℕ)
    (h : ∀ σ ∈ pkgSegs w, PS_PC (pkgWordMat G M E L κ₀ σ) (V σ) (k σ)) :
    PS_FC (fun i j => ‖(pkgWordMat G M E L (fun l => if l = 0 then i else j) w).trace‖)
      ((pkgSegs w).map V).prod ((pkgSegs w).map k).sum := by
  have hprod := PS_FC_prod (fun σ => PS_mx (pkgWordMat G M E L κ₀ σ)) V k (pkgSegs w)
    (fun σ _ i j => PS_mx_nonneg _ i j) (fun σ hσ => PS_PC_FC (h σ hσ))
  refine PS_FC_mono hprod (fun i j => ?_) le_rfl le_rfl
  refine PS_trace_le G M E L _ {i, j} (fun l => by by_cases hl : l = 0 <;> simp [hl]) w hw _
    (fun σ _ => PS_mx_nonneg _ i j) (fun σ hσ a b ha hb => ?_)
  rw [PS_mat_kappa G M E L _ κ₀ σ (PS_segs_free w σ hσ)]
  exact PS_mx_ge _ i j a b (by simpa using ha) (by simpa using hb)

end WordFC

/-! ## The factor of a package -/

section PkgAll

variable {D N : ℕ}

/-- The bounds of a package of a derivative structure: crude for every Hermitian array, and on a
good event `≤ C N^{τ'}` times the size of its factor `pkgSegFac`. -/
private lemma PS_pkg {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 1 ≤ K)
    (hD : 1 ≤ D) (hτ' : 0 ≤ τ') (hI : PS_Iso D N δA τ c₀ K C Lm τ' D')
    (hT : PS_Two D N δA τ c₀ K C Lm τ' D')
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) {e : LoopEnv D N}
    {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ} {E : ℕ → Matrix (Idx D N) (Idx D N) ℂ}
    (hc : PS_Ctx D N δA τ c₀ K η m e M E) (σ : List PkgLetter)
    (hσ : ∀ x ∈ σ, PkgLetter.isEnt x = false) (hlen : σ.length ≤ Lm)
    (hend : σ.getLast?.map PkgLetter.isRes = some true) (hL2 : σ.countP PkgLetter.isLam ≤ 2)
    (hfirst : 2 ≤ σ.countP PkgLetter.isLam →
      (σ.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0) (κ : ℕ → Idx D N) :
    (∀ h, (Matrix.of h).IsHermitian → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cc K Lm * N ^ 3 * (pkgSegFac σ).val N η m (hsNorm e.A)) 0) ∧
    ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) ∧
      ∀ h, (Matrix.of h).IsHermitian → h ∉ bad → PS_PC (pkgWordMat (e.G h) M E e.Lt κ σ)
        (PS_Cg K Lm * (N : ℝ) ^ τ' * (pkgSegFac σ).val N η m (hsNorm e.A))
        (σ.countP PkgLetter.isLam) := by
  rcases (show σ.countP PkgLetter.isLam = 0 ∨ σ.countP PkgLetter.isLam = 1 ∨
      σ.countP PkgLetter.isLam = 2 by omega) with h0 | h1 | h2
  · rw [PS_seg_free σ h0, h0]
    exact PS_pkg_free hK hI hμ hc σ hσ hlen (PS_last_res' σ hend) h0 κ
  · rw [PS_seg_lam1 σ h1, h1]
    exact PS_pkg_lam1 hK hD hI hT hμ hc σ hσ hlen hend h1 κ
  · rw [h2]
    exact PS_pkg_lam2 hK hD hτ' hT hμ hc σ hσ hlen hend h2 (hfirst (by omega)) κ

end PkgAll

/-! ## Measurability of the value -/

section Meas

variable {D N : ℕ}

/-- Every entry is a measurable function of the array. -/
private def PS_MM (X : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  ∀ k l, Measurable fun h => X h k l

private lemma PS_MM_mul {X Y : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hX : PS_MM X) (hY : PS_MM Y) : PS_MM fun h => X h * Y h := fun k l => by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun j _ => (hX k j).mul (hY j l)

private lemma PS_MM_res (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) :
    PS_MM fun h : Idx D N → Idx D N → ℂ => res (Matrix.of h + Λ) ξ := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ =>
      Matrix.of h + Λ - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) :=
    (continuous_id.add continuous_const).sub continuous_const
  have hdet := hc.matrix_det.measurable
  have hadj := hc.matrix_adjugate.measurable
  intro k l
  simp only [res, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp hadj))

private lemma PS_MM_word (e : LoopEnv D N) (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N) :
    ∀ w : List PkgLetter, PS_MM fun h => pkgWordMat (e.G h) M E L κ w
  | [] => fun _ _ => by simp only [PE_wm_nil]; exact measurable_const
  | x :: w => by
    have ih := PS_MM_word e M E L κ w
    have e1 : (fun h => pkgWordMat (e.G h) M E L κ (x :: w)) =
        fun h => PE_lm (e.G h) M E L κ x * pkgWordMat (e.G h) M E L κ w := by
      funext h; rw [PE_wm_cons]
    rw [e1]
    refine PS_MM_mul ?_ ih
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simp only [PE_lm_res]
      exact PS_MM_res _ _
    all_goals
      intro k l
      simp only [PE_lm, loopWordMat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      exact measurable_const

private lemma PS_meas_tr {X : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hX : PS_MM X) : Measurable fun h => (X h).trace :=
  Finset.measurable_sum _ fun i _ => hX i i

private lemma PS_meas_prod {α : Type*} (f : α → (Idx D N → Idx D N → ℂ) → ℂ) :
    ∀ l : List α, (∀ x ∈ l, Measurable (f x)) → Measurable fun h => (l.map fun x => f x h).prod
  | [], _ => measurable_const
  | x :: l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact (h x (by simp)).mul (PS_meas_prod f l fun y hy => h y (by simp [hy]))

/-- The value `evalP` is a measurable function of the array. -/
private lemma PS_meas_evalP (R : PkgExpr) (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (κ : ℕ → Idx D N) : Measurable fun h => R.evalP e pr κ h := by
  unfold PkgExpr.evalP
  refine Measurable.const_mul (Finset.measurable_sum _ fun ι _ => ?_) _
  refine (PS_meas_prod _ _ fun p _ => ?_).mul (PS_meas_prod _ _ fun w _ => ?_)
  · have : PS_MM fun h => (e.G h p.1 - e.M p.1) * e.E ι p.2 := by
      refine PS_MM_mul (fun k l => ?_) (fun _ _ => measurable_const)
      simp only [Matrix.sub_apply]
      exact (PS_MM_res _ _ k l).sub measurable_const
    exact (PS_meas_tr this).const_mul _
  · by_cases hw : w.any PkgLetter.isEnt = true
    · simp only [hw, ↓reduceIte]
      exact PS_meas_tr (PS_MM_word e _ _ _ κ w)
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      exact (PS_meas_tr (PS_MM_word e _ _ _ κ w)).const_mul _

end Meas

/-! ## The shape of the derivative structures -/

section Shape

/-- The derivatives keep the class `𝓡`. -/
private lemma PS_dwirt_wf (u v : ℕ) : ∀ (n : ℕ) (L : List PkgExpr), (∀ R ∈ L, R.wf = true) →
    ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R' => R'.dent u v)^[n] L, R.wf = true
  | 0, L, h => h
  | n + 1, L, h => by
    rw [Function.iterate_succ_apply]
    refine PS_dwirt_wf u v n _ fun R hR => ?_
    obtain ⟨R', hR', hR⟩ := List.mem_flatMap.1 hR
    exact (dent_spec R' R u v (h R' hR') hR).1

private lemma PS_sum_two {α : Type*} (l : List α) (x y : α) (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x ≠ y) (f : α → ℕ) : f x + f y ≤ (l.map f).sum := by
  have hp := List.perm_cons_erase hx
  rw [(hp.map f).sum_eq, List.map_cons, List.sum_cons]
  have : y ∈ l.erase x := (List.mem_erase_of_ne hxy.symm).2 hy
  exact Nat.add_le_add_left (List.le_sum_of_mem (List.mem_map_of_mem this)) _

private lemma PS_tw_le (p q r : PkgLetter → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ l : List PkgLetter, (l.takeWhile p).countP r ≤ (l.takeWhile q).countP r
  | [] => le_rfl
  | x :: l => by
    by_cases hp : p x = true
    · have ih := PS_tw_le p q r hpq l
      simp only [List.takeWhile_cons, hp, hpq x hp, ↓reduceIte, List.countP_cons]
      omega
    · simp [List.takeWhile_cons, hp]

private lemma PS_count_lam (l : List PkgLetter) :
    l.countP PkgLetter.isLam = l.count (.lw (.lamt 0)) + l.count (.lw (.lamt 1)) :=
  PB_isL_count l

private lemma PS_seg_count (x : PkgLetter) (hx : PkgLetter.isEnt x = false) (w : List PkgLetter) :
    ((pkgSegs w).map (List.count x)).sum = w.count x := by
  have := (PB_segs_count (· == x) (fun y hy => by
    rcases y with y | ⟨u, v⟩
    · simp [isEntP] at hy
    · rcases x with x | ⟨u', v'⟩
      · simp
      · simp [PkgLetter.isEnt] at hx) w).1
  have e : pkgSegs w = PB_segs w := rfl
  rw [e]
  simpa [List.count] using this

/-- The shape of a derivative structure of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] used by the bounds: two letters `Λ̃`;
every package ends with a resolvent and has at most two `Λ̃`, and none before its first `Λ̃` when it
has two; every loop without `Δ` is a loop of `𝒯` with at most one `Λ̃` and a resolvent when it has
none. -/
private lemma PS_shape (T : LoopExpr) (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ)
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) :
    (R.loops.map (List.countP PkgLetter.isLam)).sum = 2 ∧
    (∀ w ∈ R.loops, w.any PkgLetter.isEnt = true → ∀ σ ∈ pkgSegs w,
      σ.getLast?.map PkgLetter.isRes = some true ∧ σ.countP PkgLetter.isLam ≤ 2 ∧
      (2 ≤ σ.countP PkgLetter.isLam →
        (σ.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0)) ∧
    (∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → w.countP PkgLetter.isLam ≤ 1 ∧
      (w.countP PkgLetter.isLam = 0 → 1 ≤ w.countP PkgLetter.isRes) ∧
      ∃ w₀ : List LoopLetter, w = w₀.map PkgLetter.lw) := by
  obtain ⟨⟨ℓ, a, tl⟩, hfoc⟩ := Option.isSome_iff_exists.1 hf
  have hwf : R.wf = true := by
    unfold PkgExpr.dwirt at hR
    refine PS_dwirt_wf 0 1 p _ (PS_dwirt_wf 1 0 q _ ?_) R hR
    intro R' hR'
    rw [List.mem_singleton] at hR'
    subst hR'
    exact pkgStart_wf hT hfoc
  obtain ⟨hl0, hl1, hseg, -, -⟩ := (wf_iff R).1 hwf
  obtain ⟨-, ⟨w₀, hw₀, σ₀, hσ₀, -, hcont, htake⟩, -, hlast, -⟩ :=
    pkg_dwirt_shape T hT ℓ a tl hfoc 0 1 p q R hR
  obtain ⟨hcoll, -, -, -, hfree, -⟩ := pkg_dwirt_words T hT ℓ a tl hfoc 0 1 p q R hR
  set o : Fin 2 := if 1 ≤ T.kk 0 then 0 else 1 with ho
  set x : PkgLetter := .lw (.lamt o) with hx
  have hxe : PkgLetter.isEnt x = false := rfl
  have hsum2 : (R.loops.map (List.countP PkgLetter.isLam)).sum = 2 := by
    rw [show (List.countP PkgLetter.isLam) = fun l : List PkgLetter =>
      l.count (.lw (.lamt 0)) + l.count (.lw (.lamt 1)) from funext PS_count_lam,
      List.sum_map_add, hl0, hl1]
  have htot : (R.loops.map (List.count x)).sum = 1 := by
    rw [hx, ho]
    split_ifs
    · exact hl0
    · exact hl1
  have hle1 : ∀ y : Fin 2, ∀ w ∈ R.loops, w.count (.lw (.lamt y)) ≤ 1 := by
    intro y w hw
    have h := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count (.lw (.lamt y))) hw)
    fin_cases y
    · exact h.trans hl0.le
    · exact h.trans hl1.le
  obtain ⟨rest, hRl⟩ : ∃ rest, R.loops = w₀ :: rest := by
    rcases hRl : R.loops with _ | ⟨w, rest⟩
    · rw [hRl] at hw₀; simp at hw₀
    · rw [hRl] at hw₀
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw₀
      exact ⟨rest, by rw [hw₀]⟩
  have hw₀e : w₀.any PkgLetter.isEnt = true := by
    by_contra hne
    have hne' : ∀ z ∈ w₀, PkgLetter.isEnt z = false := by simpa using hne
    have hc := pkgColl_free w₀ hne'
    have hstart : T.pkgStart.loops = (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map
        PkgLetter.lw) ++ [PkgLetter.ent 1 0]) :: (T.loops.eraseIdx ℓ).map
          fun w => w.map PkgLetter.lw := by
      simp [LoopExpr.pkgStart, hfoc]
    rw [hstart, hRl] at hcoll
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq] at hcoll
    rw [hc] at hcoll
    have : w₀.any PkgLetter.isEnt = true := by rw [hcoll.1]; simp [PkgLetter.isEnt]
    exact hne this
  have hσ₀x : 1 ≤ σ₀.count x := List.count_pos_iff.2 (by simpa using hcont)
  -- the letter `Λ̃_o` lies only in the package `σ₀`
  have hcw : ∀ w, w.count x = ((pkgSegs w).map (List.count x)).sum := fun w =>
    (PS_seg_count x hxe w).symm
  have hw₀x : σ₀.count x ≤ w₀.count x := by
    rw [hcw w₀]; exact List.le_sum_of_mem (List.mem_map_of_mem hσ₀)
  have hrest : ∀ w ∈ rest, w.count x = 0 := by
    intro w hw
    have h1 : (R.loops.map (List.count x)).sum = w₀.count x + (rest.map (List.count x)).sum := by
      rw [hRl]; simp
    have h2 := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count x) hw)
    omega
  have huniq : ∀ w ∈ R.loops, ∀ σ ∈ pkgSegs w, 1 ≤ σ.count x → σ = σ₀ := by
    intro w hw σ hσ h1
    rw [hRl] at hw
    rcases List.mem_cons.1 hw with rfl | hw
    · by_contra hne
      have h2 := PS_sum_two (pkgSegs w) σ σ₀ hσ hσ₀ hne (List.count x)
      have h3 : w.count x ≤ 1 := by
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count x)
          (show w ∈ R.loops by rw [hRl]; simp))
        omega
      rw [hcw w] at h3
      omega
    · have h2 := hrest w hw
      rw [hcw w] at h2
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count x) hσ)
      omega
  have hx2 : ∀ l : List PkgLetter, 2 ≤ l.countP PkgLetter.isLam →
      l.count (.lw (.lamt 0)) ≤ 1 → l.count (.lw (.lamt 1)) ≤ 1 → 1 ≤ l.count x := by
    intro l h2 h0 h1
    rw [PS_count_lam] at h2
    rw [hx, ho]
    split_ifs <;> omega
  refine ⟨hsum2, fun w hw hwe σ hσ => ⟨hlast w hw hwe σ hσ, ?_, fun h2 => ?_⟩, fun w hw hwe => ?_⟩
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.countP PkgLetter.isLam) hσ)
    rw [PS_segs_lam] at this
    have h' := List.le_sum_of_mem (List.mem_map_of_mem (f := List.countP PkgLetter.isLam) hw)
    omega
  · have hc0 : ∀ y : Fin 2, σ.count (.lw (.lamt y)) ≤ 1 := by
      intro y
      refine le_trans ?_ (hle1 y w hw)
      rw [← PS_seg_count _ rfl w]
      exact List.le_sum_of_mem (List.mem_map_of_mem hσ)
    have hσx := hx2 σ h2 (hc0 0) (hc0 1)
    rw [huniq w hw σ hσ hσx]
    refine Nat.eq_zero_of_le_zero ?_
    refine (PS_tw_le (fun x => !x.isLam) (fun z => decide (z ≠ .lw (.lamt o))) PkgLetter.isRes
      (fun z hz => ?_) σ₀).trans htake.le
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hz
    simp only [decide_eq_true_eq]
    rintro rfl
    simp [PkgLetter.isLam] at hz
  · refine ⟨?_, fun h0 => ?_, ?_⟩
    rotate_left 2
    · obtain ⟨w₁, -, h⟩ := hfree w hw hwe
      exact ⟨w₁, h⟩
    · by_contra h2
      have hσx := hx2 w (by omega) (hle1 0 w hw) (hle1 1 w hw)
      rw [hRl] at hw
      rcases List.mem_cons.1 hw with rfl | hw'
      · rw [hw₀e] at hwe; exact absurd hwe (by simp)
      · have := hrest w hw'
        omega
    · have hs := hseg w hw
      rw [PB_segOK] at hs
      have hwe' : w.any isEntP = false := hwe
      have e : PB_segs w = [w] := by unfold PB_segs; rw [hwe']; rfl
      rw [e] at hs
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hs
      obtain ⟨y, hy, hyg⟩ := List.any_eq_true.1 hs
      refine List.countP_pos_iff.2 ⟨y, hy, ?_⟩
      have hyl : PkgLetter.isLam y = false := by simpa using List.countP_eq_zero.1 h0 y hy
      rcases y with ((b | b | z | o') | ⟨u, v⟩) <;> simp_all [isGoodP, PkgLetter.isLam,
        PkgLetter.isRes]

end Shape

/-! ## The slots of Lemmas 5.2 and 5.4 -/

section Slots

variable {D N : ℕ}

/-- `2 Im m ≤ ‖M - M^*‖` (`m = ⟨M⟩`). -/
private lemma PS_im_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    2 * (mSol Λ z).im ≤ opNorm (MExt Λ z - (MExt Λ z)ᴴ) := by
  obtain ⟨-, hm, -⟩ := mSol_spec Λ hΛ z hz
  have hME : MExt Λ z = MSol Λ z := by
    unfold MExt MSol mExt
    simp only [hz, ↓reduceIte]
  rw [hME]
  refine le_trans ?_ (Bd_ntr_le _)
  have e : ntr (MSol Λ z - (MSol Λ z)ᴴ) = mSol Λ z - star (mSol Λ z) := by
    rw [hm]
    unfold ntr
    rw [Matrix.trace_sub, Matrix.trace_conjTranspose, mul_sub, star_mul', star_inv₀]
    simp
  rw [e, Complex.star_def, Complex.sub_conj]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
  exact le_abs_self _

/-- `‖Λ‖²_HS = D N ⟨Λ²⟩` for Hermitian `Λ`. -/
private lemma PS_hs_avg (hD : 1 ≤ D) (hN : 1 ≤ N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) : hsNorm Λ ^ 2 = D * N * avgSq Λ := by
  rw [MultiRes_hsNorm_sq]
  unfold avgSq ntr
  have h1 : Λ * Λ = Λ * Λᴴ := by rw [hΛ.eq]
  rw [h1, MultiRes_trace_mul_conjTranspose]
  have hc : (Fintype.card (Idx D N) : ℂ) = ((D * N : ℕ) : ℝ) := by simp [Fintype.card_prod]
  rw [hc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have : (0 : ℝ) < D * N := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  push_cast
  field_simp

/-- `‖Λ̃‖²_HS ≤ (2 + 2K²) ‖Λ‖²_HS` when `|δ| ≤ K ⟨Λ²⟩`, `‖Λ‖ ≤ 1`. -/
private lemma PS_hs_Lt (hD : 1 ≤ D) (hN : 1 ≤ N) (e : LoopEnv D N) (K : ℝ)
    (hδ : |e.δ| ≤ K * avgSq (lam D N e.A)) (hl : opNorm (lam D N e.A) ≤ 1) :
    hsNorm e.Lt ^ 2 ≤ (2 + 2 * K ^ 2) * hsNorm (lam D N e.A) ^ 2 := by
  have hH := lam_isHermitian D N e.A
  have hav := PS_hs_avg hD hN _ hH
  have hav0 : 0 ≤ avgSq (lam D N e.A) := Bd_avgSq_nonneg _ hH
  have hav1 : avgSq (lam D N e.A) ≤ 1 :=
    (Bd_avgSq_le _).trans (by nlinarith [Bd_opNorm_nonneg (lam D N e.A)])
  rw [MultiRes_hsNorm_sq, MultiRes_hsNorm_sq]
  unfold MultiRes_hs2
  have hpt : ∀ x y : Idx D N, ‖e.Lt x y‖ ^ 2 ≤ 2 * ‖lam D N e.A x y‖ ^ 2 +
      2 * (if x = y then e.δ ^ 2 else 0) := by
    intro x y
    unfold LoopEnv.Lt
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    have h1 := norm_sub_le (lam D N e.A x y) ((e.δ : ℂ) • (if x = y then (1 : ℂ) else 0))
    have h2 : ‖(e.δ : ℂ) • (if x = y then (1 : ℂ) else 0)‖ ^ 2 = if x = y then e.δ ^ 2 else 0 := by
      split_ifs <;> simp [sq_abs]
    set A' := ‖lam D N e.A x y‖
    set B' := ‖(e.δ : ℂ) • (if x = y then (1 : ℂ) else 0)‖
    calc ‖lam D N e.A x y - (e.δ : ℂ) • (if x = y then (1 : ℂ) else 0)‖ ^ 2 ≤ (A' + B') ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 * A' ^ 2 + 2 * B' ^ 2 := by nlinarith [sq_nonneg (A' - B')]
      _ = _ := by rw [h2]
  have hdiag : ∑ x : Idx D N, ∑ y : Idx D N, (if x = y then e.δ ^ 2 else 0) = D * N * e.δ ^ 2 := by
    simp [Finset.sum_ite_eq, Fintype.card_prod]
  calc ∑ x, ∑ y, ‖e.Lt x y‖ ^ 2
      ≤ ∑ x : Idx D N, ∑ y : Idx D N, (2 * ‖lam D N e.A x y‖ ^ 2 +
          2 * (if x = y then e.δ ^ 2 else 0)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
    _ = 2 * (∑ x, ∑ y, ‖lam D N e.A x y‖ ^ 2) + 2 * (D * N * e.δ ^ 2) := by
        rw [← hdiag]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (∑ x, ∑ y, ‖lam D N e.A x y‖ ^ 2) +
        2 * (K ^ 2 * ∑ x, ∑ y, ‖lam D N e.A x y‖ ^ 2) := by
        refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)) _
        have hs : ∑ x, ∑ y, ‖lam D N e.A x y‖ ^ 2 = D * N * avgSq (lam D N e.A) := by
          rw [← hav, MultiRes_hsNorm_sq]; rfl
        rw [hs]
        have hδ2 : e.δ ^ 2 ≤ (K * avgSq (lam D N e.A)) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
        have hDN : (0 : ℝ) ≤ D * N := by positivity
        calc (D : ℝ) * N * e.δ ^ 2 ≤ D * N * (K * avgSq (lam D N e.A)) ^ 2 :=
              mul_le_mul_of_nonneg_left hδ2 hDN
          _ = K ^ 2 * (D * N * avgSq (lam D N e.A)) * avgSq (lam D N e.A) := by ring
          _ ≤ K ^ 2 * (D * N * avgSq (lam D N e.A)) * 1 := by gcongr
          _ = K ^ 2 * (D * N * avgSq (lam D N e.A)) := by ring
    _ = (2 + 2 * K ^ 2) * ∑ x, ∑ y, ‖lam D N e.A x y‖ ^ 2 := by ring

end Slots

/-! ## The facts at the slots -/

/-- `𝔯(k) ≥ 1` and `η = N^{-2/3+ε} 𝔯(k)^{-1/3} ≤ 1` for `1 ≤ k`, `2k ≤ DN + 1`, `ε ≤ 1/3`. -/
private lemma PS_eta_le (D N k : ℕ) (ε : ℝ) (hε'' : ε ≤ 1 / 3) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hkN : 2 * k ≤ D * N + 1) : etaK D N k ε ≤ 1 := by
  have hr : (1 : ℝ) ≤ rk D N k := by
    unfold rk
    exact_mod_cast (show 1 ≤ min k (D * N + 1 - k) by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold etaK
  have h1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  have h2 : rk D N k ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
  have h3 : 0 ≤ rk D N k ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-(2 / 3 : ℝ) + ε)]

set_option maxHeartbeats 1000000 in
-- the bounds of the factors are combined in one proof
/-- The slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law] satisfy the facts used by the bounds of the factors, with
`η = N^{-2/3+ε} 𝔯(k)^{-1/3}` and `Im m` of slot `1`, with one constant `K`. -/
private lemma PS_slot (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (K₁ : ℝ) :
    ∃ c₀ K : ℝ, 0 < c₀ ∧ 2 ≤ K ∧ K₁ ≤ K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        (∀ M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ, (∀ a, opNorm (M a) ≤ K) →
          ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
          PS_Ctx D N δA (ε / 2) c₀ K (etaK D N k ε)
            (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im e M E) ∧
        (∀ a, opNorm (e.M a) ≤ K) ∧
        (∀ a, opNorm (e.M a - (e.M a)ᴴ) ≤ K * (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im) ∧
        avgSq (lam D N e.A) ≤ K * (hsNorm e.A ^ 2 / N) ∧ e.A = A := by
  obtain ⟨c₀, Kδ, hc₀, hKδ, N₁, hadm⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨Kp, hKp, N₂, hpair⟩ := pkg_pair_norm D hD δA εA ε hδA hεA hε hε' hε''
  set K : ℝ := 2 + Kp + Kδ + c₀⁻¹ + (D : ℝ) * (8 + 8 * Kδ) + |K₁| with hKdef
  have hK₁ := abs_nonneg K₁
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hc0i : 0 < c₀⁻¹ := inv_pos.2 hc₀
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith
  have hKpK : Kp ≤ K := by rw [hKdef]; nlinarith
  have hKδK : Kδ ≤ K := by rw [hKdef]; nlinarith
  have hcK : c₀⁻¹ ≤ K := by rw [hKdef]; nlinarith
  have hDK : (D : ℝ) ≤ K := by rw [hKdef]; nlinarith
  have h4D : 4 * (D : ℝ) ≤ K := by rw [hKdef]; nlinarith
  have hMK : (5 / 4 : ℝ) ≤ K := by rw [hKdef]; nlinarith
  have hLK : 2 + 4 * Kδ ≤ K := by rw [hKdef]; nlinarith
  have hHK : (2 + 2 * Kδ) * (2 * D) ≤ K := by rw [hKdef]; nlinarith
  have h2DK : 2 * (D : ℝ) ≤ K := by rw [hKdef]; nlinarith
  have hK2 : 2 ≤ K := by rw [hKdef]; nlinarith
  have hK₁K : K₁ ≤ K := by rw [hKdef]; nlinarith [le_abs_self K₁]
  refine ⟨c₀, K, hc₀, hK2, hK₁K, max (max N₁ N₂) 1, fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨hA2, hc, hz, hδ⟩ := hadm N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    A hA k hk hkN hhs e he
  have hpn := hpair N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) A hA k hk
    hkN hhs
  have heA : e.A = A := by
    rcases he with ⟨s, rfl⟩ | ⟨t, -, s, rfl⟩ <;> rfl
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set η := etaK D N k ε with hηdef
  set m := (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im with hmdef
  have hη : 0 < η := (hz 1).2.2.1 ▸ (hz 1).2.1
  have hη1 : η ≤ 1 := PS_eta_le D N k ε hε'' hN1 hk hkN
  have hcl : (μ, e) ∈ Bd_Cl D δA 1 Kδ C N :=
    ⟨hμ, heA ▸ hA, by simpa using hA2, hc, hδ⟩
  obtain ⟨-, hM, hLt, -, -, him1⟩ := Bd_facts (D := D) (N := N) (by omega) hN1 (τ := ε / 2)
    (c₀ := c₀) le_rfl hcl fun a => ⟨(hz a).1, (hz a).2.1, (hz a).2.2.2⟩
  have hm1 : m ≤ 1 := him1 1
  have hNηm : c₀ ≤ N * η * m := by
    have := (hz 1).2.2.2
    rwa [(hz 1).2.2.1] at this
  have hm : 0 < m := by
    by_contra hm
    have : (N : ℝ) * η * m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hm)
    linarith
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  -- `Im m_a ≤ K Im m` from the pairing bound at the slots without flags
  have him : ∀ a, (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤ K * m := by
    intro a
    have he' : (∃ s, ({ e with s := fun _ => false } : LoopEnv D N) = evecEnv D N A k ε s) ∨
        ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, ({ e with s := fun _ => false } : LoopEnv D N) =
          evalEnv D N A k ε t s := by
      rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ⟨t, ht, _, rfl⟩
    have h1 := hpn _ he' a
    have h2 := PS_im_le ((e.c a : ℂ) • lam D N e.A) (Bd_lamc_herm D N _ _) (e.z a) (hz a).2.1
    have e1 : ({ e with s := fun _ => false } : LoopEnv D N).M a =
        MExt ((e.c a : ℂ) • lam D N e.A) (e.z a) := by simp [LoopEnv.M]
    have hmeq : (mSol ((({ e with s := fun _ => false } : LoopEnv D N).c 1 : ℂ) •
        lam D N ({ e with s := fun _ => false } : LoopEnv D N).A)
        (({ e with s := fun _ => false } : LoopEnv D N).z 1)).im = m := rfl
    rw [e1, hmeq] at h1
    have : Kp * m ≤ K * m := mul_le_mul_of_nonneg_right hKpK hm.le
    have h0 := PS_im_nonneg ((e.c a : ℂ) • lam D N e.A) (e.z a)
    have h3 : 0 ≤ Kp * m := by positivity
    linarith
  -- the Hilbert–Schmidt norms
  have havg : avgSq (lam D N e.A) ≤ 4 * D * hsNorm e.A ^ 2 / N := Rg_avgSq_lam D N hD hN1 e.A
  have hlam1 : opNorm (lam D N e.A) ≤ 1 := by
    have := opNorm_lam_le D N e.A
    have : 2 * opNorm e.A ≤ 1 / 10 := by simpa using hA2
    linarith
  have hhs_lam : hsNorm (lam D N e.A) ≤ 2 * D * hsNorm e.A := by
    have h1 := PS_hs_avg (by omega) hN1 _ (lam_isHermitian D N e.A)
    have h2 : hsNorm (lam D N e.A) ^ 2 ≤ (2 * D * hsNorm e.A) ^ 2 := by
      rw [h1]
      have hNp : (0 : ℝ) < N := by linarith
      calc (D : ℝ) * N * avgSq (lam D N e.A) ≤ D * N * (4 * D * hsNorm e.A ^ 2 / N) :=
            mul_le_mul_of_nonneg_left havg (by positivity)
        _ = (2 * D * hsNorm e.A) ^ 2 := by field_simp; ring
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 h2
  have hhs_Lt : hsNorm e.Lt ≤ (2 + 2 * Kδ) * (2 * D * hsNorm e.A) := by
    have h1 := PS_hs_Lt (by omega) hN1 e Kδ hδ hlam1
    have h2 : hsNorm e.Lt ^ 2 ≤ ((2 + 2 * Kδ) * (2 * D * hsNorm e.A)) ^ 2 := by
      refine h1.trans ?_
      have h3 : hsNorm (lam D N e.A) ^ 2 ≤ (2 * D * hsNorm e.A) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hhs_lam 2
      have h4 : 2 + 2 * Kδ ^ 2 ≤ (2 + 2 * Kδ) ^ 2 := by nlinarith
      calc (2 + 2 * Kδ ^ 2) * hsNorm (lam D N e.A) ^ 2
          ≤ (2 + 2 * Kδ) ^ 2 * (2 * D * hsNorm e.A) ^ 2 :=
            mul_le_mul h4 h3 (by positivity) (by positivity)
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 h2
  have hopLt : opNorm e.Lt ≤ K * hsNorm e.A := by
    refine hLt.trans ?_
    rw [abs_of_nonneg hKδ]
    refine mul_le_mul hLK (PS_op_le_hs _) (Bd_opNorm_nonneg _) (by linarith)
  have hη0 : 1 ≤ K * ((N : ℝ) * η * m) := by
    have : 1 ≤ c₀⁻¹ * (N * η * m) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hc₀]; linarith
    exact this.trans (mul_le_mul_of_nonneg_right hcK (by positivity))
  have havgK : avgSq (lam D N e.A) ≤ K * (hsNorm e.A ^ 2 / N) := by
    refine havg.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right h4D (by positivity)
  refine ⟨fun M hMK E hE => ⟨⟨heA ▸ hA, by simpa using hA2, hc, fun a => ⟨(hz a).1, (hz a).2.1,
    (hz a).2.2.2⟩, hδ.trans (mul_le_mul_of_nonneg_right hKδK
      (Bd_avgSq_nonneg _ (lam_isHermitian D N _)))⟩, fun a => (hz a).2.2.1, hη1, hm1, hη0, him,
    hhs_Lt.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hHK hs0),
    hhs_lam.trans (mul_le_mul_of_nonneg_right h2DK hs0), hopLt, hMK, hE, hDK, hN1⟩,
    fun a => (hM a).trans hMK, fun a => (hpn e he a).trans (mul_le_mul_of_nonneg_right hKpK hm.le),
    havgK, heA⟩

/-! ## The expression: lists of factors -/

section Expr

variable {D N : ℕ}

private lemma PS_prod_flatMap {α β : Type*} (f : α → List β) (g : β → ℝ) :
    ∀ L : List α, ((L.flatMap f).map g).prod = (L.map fun x => ((f x).map g).prod).prod
  | [] => by simp
  | x :: L => by
    rw [List.flatMap_cons, List.map_append, List.prod_append, PS_prod_flatMap f g L]
    simp

/-- The product over the profile: the light weights, then the factors of each word. -/
private lemma PS_profile_prod (R : PkgExpr) (pr : Fin 2 → Bool) (g : PkgFac → ℝ) :
    ((R.profile pr).map g).prod = (R.weights.map fun _ => g .wt).prod *
      (R.loops.map fun w => ((pkgWordFac pr w).map g).prod).prod := by
  unfold PkgExpr.profile
  rw [List.map_append, List.prod_append, List.map_map, PS_prod_flatMap]
  rfl

private lemma PS_profile_len (R : PkgExpr) (pr : Fin 2 → Bool) :
    (R.profile pr).length =
      R.weights.length + (R.loops.map fun w => (pkgWordFac pr w).length).sum := by
  unfold PkgExpr.profile
  rw [List.length_append, List.length_map, List.length_flatMap]

/-- The paired letters of a word: `pkgWordFac` of a word with `Δ`. -/
private lemma PS_fac_ent (pr : Fin 2 → Bool) (w : List PkgLetter)
    (hw : w.any PkgLetter.isEnt = true) (g : PkgFac → ℝ) :
    ((pkgWordFac pr w).map g).prod = ((pkgSegs w).map fun σ => g (pkgSegFac σ)).prod *
      g .pair ^ (w.filter fun x => match x with | .lw (.det a) => pr a | _ => false).length := by
  unfold pkgWordFac
  simp only [hw, ↓reduceIte, List.map_append, List.prod_append, List.map_map]
  congr 1
  simp [Function.comp_def, List.prod_replicate]
  rfl

/-- The weights of the expression, the deterministic letters `M` and the paired letters. -/
private lemma PS_pairM {D N : ℕ} (e : LoopEnv D N) (pr : Fin 2 → Bool) (m : ℝ) (hm : m ≠ 0) :
    e.pairM pr = fun a => (if pr a then (m : ℂ) else 1) •
      (if pr a then ((m : ℂ))⁻¹ • (e.M a - (e.M a)ᴴ) else e.M a) := by
  funext a
  unfold LoopEnv.pairM
  by_cases ha : pr a
  · simp only [ha, ↓reduceIte, smul_smul]
    rw [mul_inv_cancel₀ (by exact_mod_cast hm), one_smul]
  · simp [ha]

/-- The value at the labels from the terms of the sum over the bound block indices. -/
private lemma PS_evalP_le (R : PkgExpr) (e : LoopEnv D N) (pr : Fin 2 → Bool) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) :
    ‖R.evalP e pr κ h‖ ≤ |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) *
      ∑ ι : Fin R.nb → Fin D, (R.weights.map fun p =>
        ‖ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)‖).prod *
      (R.loops.map fun w => ‖if w.any PkgLetter.isEnt
        then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w).trace
        else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w)‖).prod := by
  unfold PkgExpr.evalP
  rw [norm_mul]
  have hc : ‖(R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)‖ =
      |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) := by
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_intCast]
  rw [hc]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_))
    (by positivity)
  rw [norm_mul, List.norm_prod, List.norm_prod, List.map_map, List.map_map]
  exact le_rfl

end Expr

/-! ## The factor of one word -/

section Word

variable {D N : ℕ}

/-- A word with `Δ`: its packages, with `𝔐_a - 𝔐_a^* = Im m · Y_a` on the paired slots. -/
private lemma PS_word_ent {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 2 ≤ K)
    (hD : 1 ≤ D) (hτ' : 0 ≤ τ') (hI : PS_Iso D N δA τ c₀ K C Lm τ' D')
    (hT : PS_Two D N δA τ c₀ K C Lm τ' D') {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C 1 μ) {e : LoopEnv D N} {M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ}
    {nb : ℕ} (ι : Fin nb → Fin D) (hc : PS_Ctx D N δA τ c₀ K η m e M (e.E ι)) (pr : Fin 2 → Bool)
    (hpairM : e.pairM pr = fun a => (if pr a then (m : ℂ) else 1) • M a)
    (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true) (hlen : w.length ≤ Lm)
    (hseg : ∀ σ ∈ pkgSegs w, σ.getLast?.map PkgLetter.isRes = some true ∧
      σ.countP PkgLetter.isLam ≤ 2 ∧ (2 ≤ σ.countP PkgLetter.isLam →
        (σ.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0)) :
    (∀ h, (Matrix.of h).IsHermitian → PS_FC (fun i j => ‖if w.any PkgLetter.isEnt
        then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w).trace
        else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w)‖)
      ((pkgWordFac pr w).map fun f => PS_Cc K Lm * N ^ 3 * f.val N η m (hsNorm e.A)).prod
      (w.countP PkgLetter.isLam)) ∧
    ∃ s : Set (Idx D N → Idx D N → ℂ),
      μ s ≤ ENNReal.ofReal ((pkgWordFac pr w).length * (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'))) ∧
      ∀ h, h ∉ s → (Matrix.of h).IsHermitian → PS_FC (fun i j => ‖if w.any PkgLetter.isEnt
        then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w).trace
        else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w)‖)
      ((pkgWordFac pr w).map fun f => PS_Cg K Lm * (N : ℝ) ^ τ' * f.val N η m (hsNorm e.A)).prod
      (w.countP PkgLetter.isLam) := by
  have hK1 : 1 ≤ K := by linarith
  obtain ⟨hη, hm, -⟩ := PS_Ctx_pos hc hK1
  have hN1 : 1 ≤ N := hc.2.2.2.2.2.2.2.2.2.2.2.2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set κ₀ : ℕ → Idx D N := fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩) with hκ₀
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  have hpk := fun σ (hσ : σ ∈ pkgSegs w) => PS_pkg hK1 hD hτ' hI hT hμ hc σ
    (PS_segs_free w σ hσ) ((PS_segs_len w σ hσ).trans hlen) (hseg σ hσ).1 (hseg σ hσ).2.1
    (hseg σ hσ).2.2 κ₀
  set np := (w.filter fun x => match x with | .lw (.det a) => pr a | _ => false).length with hnp
  have hscale : ∀ h (i j : Idx D N), ‖if w.any PkgLetter.isEnt
      then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j) w).trace
      else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j) w)‖ =
      m ^ np * ‖(pkgWordMat (e.G h) M (e.E ι) e.Lt (fun l => if l = 0 then i else j) w).trace‖ := by
    intro h i j
    simp only [hw, ↓reduceIte]
    rw [hpairM, PS_wm_scale, Matrix.trace_smul, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hm]
  have hval0 := PS_val_nonneg N hη hm.le hs0
  -- the bound of the paired letters
  have hpair : ∀ c : ℝ, 1 ≤ c → m ^ np * ((pkgSegs w).map fun σ => c * (pkgSegFac σ).val N η m
      (hsNorm e.A)).prod ≤ ((pkgWordFac pr w).map fun f => c * f.val N η m (hsNorm e.A)).prod := by
    intro c hc1
    rw [PS_fac_ent pr w hw]
    have h1 : 0 ≤ ((pkgSegs w).map fun σ => c * (pkgSegFac σ).val N η m (hsNorm e.A)).prod :=
      List.prod_nonneg fun y hy => by
        obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hy
        exact mul_nonneg (by linarith) (hval0 _)
    have h2 : m ^ np ≤ (c * PkgFac.val N η m (hsNorm e.A) .pair) ^ np := by
      refine pow_le_pow_left₀ hm.le ?_ _
      simp only [PkgFac.val]
      nlinarith
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h2 h1
  have hlenw : (pkgSegs w).length ≤ (pkgWordFac pr w).length := by
    unfold pkgWordFac; simp [hw]
  have hCc : 1 ≤ PS_Cc K Lm * (N : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (PS_Cc_one K hK1 Lm) (one_le_pow₀ hNr)
  have hCg : 1 ≤ PS_Cg K Lm * (N : ℝ) ^ τ' :=
    one_le_mul_of_one_le_of_one_le (PS_Cg_one K hK1 Lm) (Real.one_le_rpow hNr hτ')
  have hmp : 0 ≤ m ^ np := by positivity
  have key : ∀ (c : ℝ) (h : Idx D N → Idx D N → ℂ), 1 ≤ c →
      (∀ σ ∈ pkgSegs w, PS_PC (pkgWordMat (e.G h) M (e.E ι) e.Lt κ₀ σ)
        (c * (pkgSegFac σ).val N η m (hsNorm e.A)) (σ.countP PkgLetter.isLam)) →
      PS_FC (fun i j => ‖if w.any PkgLetter.isEnt
        then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w).trace
        else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w)‖)
      ((pkgWordFac pr w).map fun f => c * f.val N η m (hsNorm e.A)).prod
      (w.countP PkgLetter.isLam) := by
    intro c h hc1 hP
    have h1 := PS_word_FC (e.G h) M (e.E ι) e.Lt κ₀ w hw _ _ hP
    rw [PS_segs_lam] at h1
    have h2 := PS_FC_mul (fun i j => norm_nonneg _) (PS_FC_const (fun _ _ => m ^ np) (m ^ np) 0
      hmp fun _ _ => le_rfl) h1
    refine PS_FC_mono h2 (fun i j => le_of_eq (hscale h i j)) (hpair c hc1) (by omega)
  refine ⟨fun h hh => key _ h hCc fun σ hσ => PS_PC_mono ((hpk σ hσ).1 h hh) (Nat.zero_le _),
    ?_⟩
  have hb0 : (0 : ℝ) ≤ 2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D') := by positivity
  obtain ⟨s, hs, hP⟩ := PS_bad_list μ (fun σ h => (Matrix.of h).IsHermitian →
      PS_PC (pkgWordMat (e.G h) M (e.E ι) e.Lt κ₀ σ)
        (PS_Cg K Lm * (N : ℝ) ^ τ' * (pkgSegFac σ).val N η m (hsNorm e.A))
        (σ.countP PkgLetter.isLam)) (fun _ => 2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'))
    (fun _ => hb0) (pkgSegs w) fun σ hσ => by
      obtain ⟨bad, hbad, hgood⟩ := (hpk σ hσ).2
      exact ⟨bad, hbad, fun h hh hH => hgood h hH hh⟩
  refine ⟨s, hs.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh hH =>
    key _ h hCg fun σ hσ => hP h hh σ hσ hH⟩
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlenw) hb0

/-- A loop without `Δ`: its letters carry no paired slot. -/
private lemma PS_word_free {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ} (hK : 2 ≤ K)
    (hD : 1 ≤ D) (hτ' : 0 ≤ τ') (hI : PS_Iso D N δA τ c₀ K C Lm τ' D')
    (hO : PS_One D N δA τ c₀ K C Lm τ' D') {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C 1 μ) {e : LoopEnv D N} {nb : ℕ} (ι : Fin nb → Fin D)
    (hc : PS_Ctx D N δA τ c₀ K η m e e.M (e.E ι))
    (havg : avgSq (lam D N e.A) ≤ K * (hsNorm e.A ^ 2 / N)) (pr : Fin 2 → Bool)
    (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = false) (hlen : w.length ≤ Lm)
    (hL : w.countP PkgLetter.isLam ≤ 1)
    (hr : w.countP PkgLetter.isLam = 0 → 1 ≤ w.countP PkgLetter.isRes)
    (hpw : (w.any fun x => match x with | .lw (.det a) => pr a | _ => false) = false)
    (h0 : w.countP PkgLetter.isLam = 1 → w.countP PkgLetter.isRes = 0 →
      ∀ h (κ : ℕ → Idx D N), ‖ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w)‖ ≤
        K * ((if pkgGainLoop w then m else 1) * avgSq (lam D N e.A))) :
    (∀ h, (Matrix.of h).IsHermitian → PS_FC (fun i j => ‖if w.any PkgLetter.isEnt
        then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w).trace
        else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w)‖)
      ((pkgWordFac pr w).map fun f => PS_Cc K Lm * N ^ 3 * f.val N η m (hsNorm e.A)).prod
      (w.countP PkgLetter.isLam)) ∧
    ∃ s : Set (Idx D N → Idx D N → ℂ),
      μ s ≤ ENNReal.ofReal ((pkgWordFac pr w).length * (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'))) ∧
      ∀ h, h ∉ s → (Matrix.of h).IsHermitian → PS_FC (fun i j => ‖if w.any PkgLetter.isEnt
        then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w).trace
        else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j)
          w)‖)
      ((pkgWordFac pr w).map fun f => PS_Cg K Lm * (N : ℝ) ^ τ' * f.val N η m (hsNorm e.A)).prod
      (w.countP PkgLetter.isLam) := by
  have hK1 : 1 ≤ K := by linarith
  obtain ⟨hη, hm, -⟩ := PS_Ctx_pos hc hK1
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  have hwe : ∀ x ∈ w, PkgLetter.isEnt x = false := by simpa using hw
  have hcong : ∀ h κ, pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt κ w =
      pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w := by
    intro h κ
    refine Pr_wm_congr _ _ κ _ _ _ _ w (fun _ _ => rfl) fun c hc' => ?_
    unfold LoopEnv.pairM
    have : pr c = false := by
      by_contra hpc
      have : (w.any fun x => match x with | .lw (.det a) => pr a | _ => false) = true :=
        List.any_eq_true.2 ⟨_, hc', by simpa using hpc⟩
      rw [hpw] at this
      exact absurd this (by simp)
    simp [this]
  obtain ⟨hcr, bad, hbad, hgood⟩ := PS_loop hK1 hD hτ' hI hO hμ hc havg w hwe hlen hL hr
    (fun _ => (⟨0, by have := hc.2.2.2.2.2.2.2.2.2.2.2.2; have := hD; omega⟩, ⟨0, by
      have := hc.2.2.2.2.2.2.2.2.2.2.2.2; omega⟩)) (fun h1 h2 h => h0 h1 h2 h _)
  have hfac := PS_lf_fac pr w hw
  rw [hfac]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil, zero_add, Nat.cast_one, one_mul]
  have hκ : ∀ h (κ κ' : ℕ → Idx D N), ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w) =
      ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ' w) := by
    intro h κ κ'
    rw [PS_mat_kappa _ _ _ _ κ κ' w hwe]
  have hv0 := PS_val_nonneg N hη hm.le hs0 (PS_lf w)
  refine ⟨fun h hh => PS_FC_const _ _ _ (mul_nonneg (by
      have := PS_Cc_one K hK1 Lm; positivity) hv0) fun i j => ?_, bad, hbad, fun h hb hh =>
    PS_FC_const _ _ _ (mul_nonneg (by have := PS_Cg_one K hK1 Lm; positivity) hv0)
      fun i j => ?_⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [hcong, hκ h _ (fun _ => (⟨0, by have := hc.2.2.2.2.2.2.2.2.2.2.2.2; have := hD; omega⟩,
      ⟨0, by have := hc.2.2.2.2.2.2.2.2.2.2.2.2; omega⟩))]
    exact hcr h hh
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [hcong, hκ h _ (fun _ => (⟨0, by have := hc.2.2.2.2.2.2.2.2.2.2.2.2; have := hD; omega⟩,
      ⟨0, by have := hc.2.2.2.2.2.2.2.2.2.2.2.2; omega⟩))]
    exact hgood h hh hb

end Word

/-! ## The bound at size `N` -/

section Main

variable {D N : ℕ}

/-- The bound of the terms of the sum over the bound block indices from those of the weights and
the words. -/
private lemma PS_comb (R : PkgExpr) (pr : Fin 2 → Bool) (g : PkgFac → ℝ) (hg : 0 ≤ g .wt)
    (Fwt : Fin 2 × ℕ → ℝ) (Fw : List PkgLetter → Idx D N → Idx D N → ℝ)
    (hwt : ∀ p ∈ R.weights, 0 ≤ Fwt p ∧ Fwt p ≤ g .wt)
    (hw0 : ∀ w ∈ R.loops, ∀ i j, 0 ≤ Fw w i j)
    (hw : ∀ w ∈ R.loops, PS_FC (Fw w) ((pkgWordFac pr w).map g).prod (w.countP PkgLetter.isLam))
    (hk : (R.loops.map (List.countP PkgLetter.isLam)).sum ≤ 2) :
    PS_FC (fun i j => (R.weights.map Fwt).prod * (R.loops.map fun w => Fw w i j).prod)
      ((R.profile pr).map g).prod 2 := by
  have h1 := PS_FC_prod (fun p (_ : Idx D N) (_ : Idx D N) => Fwt p) (fun _ => g .wt) (fun _ => 0)
    R.weights (fun p hp _ _ => (hwt p hp).1)
    (fun p hp => PS_FC_const _ _ _ hg fun _ _ => (hwt p hp).2)
  have h2 := PS_FC_prod Fw (fun w => ((pkgWordFac pr w).map g).prod)
    (fun w => w.countP PkgLetter.isLam) R.loops hw0 hw
  have h3 := PS_FC_mul (fun i j => List.prod_nonneg fun y hy => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hy
    exact hw0 w hw' i j) h1 h2
  refine PS_FC_mono h3 (fun i j => le_rfl) (le_of_eq ?_) ?_
  · rw [PS_profile_prod]
  · simp only [List.map_const', List.sum_replicate, smul_zero, zero_add]
    exact hk

set_option maxHeartbeats 4000000 in
-- the bounds of the factors are combined in one proof
/-- The direct estimation at size `N`: the label sum of `‖E 𝓡‖` is at most
`(16 (C N^{τ'})^n + D^{nb} n 2 (DN)² N^{-D'} 16 (C N³)^n) D N² sharpB`, `n` the number of
factors. -/
private lemma PS_main_N (hD : 2 ≤ D) {δA τ c₀ K η m τ' D' : ℝ} {C : ℕ → ℝ} {Lm : ℕ}
    (hK : 2 ≤ K) (hτ' : 0 ≤ τ') (hI : PS_Iso D N δA τ c₀ K C Lm τ' D')
    (hO : PS_One D N δA τ c₀ K C Lm τ' D') (hT : PS_Two D N δA τ c₀ K C Lm τ' D')
    (T : LoopExpr) (hTw : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (pr : Fin 2 → Bool) (hpr : R.pairIn pr = true)
    (hLm : ∀ w ∈ R.loops, w.length ≤ Lm)
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C 1 μ) (e : LoopEnv D N)
    (hctx : ∀ M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ, (∀ a, opNorm (M a) ≤ K) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      PS_Ctx D N δA τ c₀ K η m e M E)
    (hMK : ∀ a, opNorm (e.M a) ≤ K) (hpairK : ∀ a, opNorm (e.M a - (e.M a)ᴴ) ≤ K * m)
    (havg : avgSq (lam D N e.A) ≤ K * (hsNorm e.A ^ 2 / N))
    (hW : ∀ (a : Fin 2) (B : Matrix (Idx D N) (Idx D N) ℂ), opNorm B ≤ 1 →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, h ∉ bad → ‖ntr ((e.G h a - e.M a) * B)‖ ≤
          (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |(e.z a).im|)))
    (hlam0 : ∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → w.countP PkgLetter.isLam = 1 →
      w.countP PkgLetter.isRes = 0 → ∀ (ι : Fin R.nb → Fin D) h (κ : ℕ → Idx D N),
      ‖ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w)‖ ≤
        K * ((if pkgGainLoop w then m else 1) * avgSq (lam D N e.A))) :
    ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
        ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ else 0) ≤
      (16 * (PS_Cg K Lm * (N : ℝ) ^ τ') ^ (R.profile pr).length +
        (D : ℝ) ^ R.nb * ((R.profile pr).length * (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'))) *
          (16 * (PS_Cc K Lm * (N : ℝ) ^ 3) ^ (R.profile pr).length)) *
      ((D : ℝ) * (N : ℝ) ^ 2 * R.sharpB D N η m (hsNorm e.A) pr) := by
  have hK1 : 1 ≤ K := by linarith
  have hD1 : 1 ≤ D := by omega
  have hc0 := hctx e.M hMK (fun _ => 1) (fun _ => Bd_opNorm_one)
  obtain ⟨hη, hm, -⟩ := PS_Ctx_pos hc0 hK1
  have hN1 : 1 ≤ N := hc0.2.2.2.2.2.2.2.2.2.2.2.2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have heta := hc0.2.1
  have hη1 := hc0.2.2.1
  have hs0 : 0 ≤ hsNorm e.A := Real.sqrt_nonneg _
  have hprob := hμ.prob
  obtain ⟨hsum2, hsh_ent, hsh_free⟩ := PS_shape T hTw hf p q R hR
  -- the paired letters `𝔐_a - 𝔐_a^* = Im m · Y_a`
  set M'' : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ := fun a =>
    if pr a then ((m : ℂ))⁻¹ • (e.M a - (e.M a)ᴴ) else e.M a with hM''def
  have hM'' : ∀ a, opNorm (M'' a) ≤ K := by
    intro a
    by_cases ha : pr a
    · simp only [hM''def, ha, ↓reduceIte]
      rw [opNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        inv_mul_le_iff₀ hm]
      linarith [hpairK a]
    · simp only [hM''def, ha, Bool.false_eq_true, ↓reduceIte]
      exact hMK a
  have hpairM := PS_pairM e pr m hm.ne'
  -- constants
  set n := (R.profile pr).length with hn
  set b0 : ℝ := 2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D') with hb0def
  have hb0 : 0 ≤ b0 := by positivity
  set Cg := PS_Cg K Lm * (N : ℝ) ^ τ' with hCgdef
  set Cc := PS_Cc K Lm * (N : ℝ) ^ 3 with hCcdef
  have hCg1 : 1 ≤ Cg := one_le_mul_of_one_le_of_one_le (PS_Cg_one K hK1 Lm)
    (Real.one_le_rpow hNr hτ')
  have hCc1 : 1 ≤ Cc := one_le_mul_of_one_le_of_one_le (PS_Cc_one K hK1 Lm) (one_le_pow₀ hNr)
  have hval0 := PS_val_nonneg N hη hm.le hs0
  -- the words
  set Fw : (Fin R.nb → Fin D) → (Idx D N → Idx D N → ℂ) → List PkgLetter → Idx D N → Idx D N → ℝ :=
    fun ι h w i j => ‖if w.any PkgLetter.isEnt
      then (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j) w).trace
      else ntr (pkgWordMat (e.G h) (e.pairM pr) (e.E ι) e.Lt (fun l => if l = 0 then i else j) w)‖
    with hFw
  have hwd : ∀ ι : Fin R.nb → Fin D, ∀ w ∈ R.loops,
      (∀ h, (Matrix.of h).IsHermitian → PS_FC (Fw ι h w)
        ((pkgWordFac pr w).map fun f => Cc * f.val N η m (hsNorm e.A)).prod
        (w.countP PkgLetter.isLam)) ∧
      ∃ s : Set (Idx D N → Idx D N → ℂ), μ s ≤ ENNReal.ofReal ((pkgWordFac pr w).length * b0) ∧
        ∀ h, h ∉ s → (Matrix.of h).IsHermitian → PS_FC (Fw ι h w)
          ((pkgWordFac pr w).map fun f => Cg * f.val N η m (hsNorm e.A)).prod
          (w.countP PkgLetter.isLam) := by
    intro ι w hw
    by_cases hwe : w.any PkgLetter.isEnt = true
    · exact PS_word_ent hK hD1 hτ' hI hT hμ ι (hctx M'' hM'' _ (Bd_opNorm_E e ι)) pr hpairM w hwe
        (hLm w hw) (hsh_ent w hw hwe)
    · have hwe' : w.any PkgLetter.isEnt = false := by simpa using hwe
      obtain ⟨hl1, hr1, -⟩ := hsh_free w hw hwe'
      have hpw : (w.any fun x => match x with | .lw (.det a) => pr a | _ => false) = false := by
        have := List.all_eq_true.1 hpr w hw
        simp [hwe'] at this ⊢
        exact this
      exact PS_word_free hK hD1 hτ' hI hO hμ ι (hctx e.M hMK _ (Bd_opNorm_E e ι)) havg pr w hwe'
        (hLm w hw) hl1 hr1 hpw fun h1 h2 h κ => hlam0 w hw hwe' h1 h2 ι h κ
  -- the light weights
  set Fwt : (Fin R.nb → Fin D) → (Idx D N → Idx D N → ℂ) → Fin 2 × ℕ → ℝ :=
    fun ι h p => ‖ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)‖ with hFwt
  have hwtc : ∀ ι h, (Matrix.of h).IsHermitian → ∀ p : Fin 2 × ℕ, Fwt ι h p ≤
      Cc * PkgFac.val N η m (hsNorm e.A) .wt := by
    intro ι h hh p
    simp only [hFwt, PkgFac.val]
    refine (Bd_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
    have h1 := Bd_opNorm_sub (e.G h p.1) (e.M p.1)
    have h2 := PS_G_norm hc0 h hh p.1
    have h3 := hMK p.1
    have h4 := Bd_opNorm_E e ι p.2
    have hηi : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.2 hη1
    have h5 : opNorm (e.G h p.1 - e.M p.1) * opNorm (e.E ι p.2) ≤ 2 * K * η⁻¹ := by
      calc opNorm (e.G h p.1 - e.M p.1) * opNorm (e.E ι p.2)
          ≤ (η⁻¹ + K) * 1 := mul_le_mul (h1.trans (add_le_add h2 h3)) h4 (Bd_opNorm_nonneg _)
            (by positivity)
        _ ≤ 2 * K * η⁻¹ := by nlinarith
    refine h5.trans ?_
    have hK2 : 2 * K ≤ PS_Cc K Lm := by
      rw [PS_Cc]
      calc 2 * K ≤ K * K := by nlinarith
        _ = K ^ 2 := by ring
        _ ≤ K ^ (Lm + 4) := pow_le_pow_right₀ hK1 (by omega)
    have hN3 : (N : ℝ) ≤ N ^ 3 :=
      (pow_one (N : ℝ)).symm.le.trans (pow_le_pow_right₀ hNr (by norm_num))
    calc 2 * K * η⁻¹ = 2 * K * N * ((N : ℝ) * η)⁻¹ := by field_simp
      _ ≤ PS_Cc K Lm * N ^ 3 * ((N : ℝ) * η)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul hK2 hN3 (by positivity)
            (by linarith [PS_Cc_one K hK1 Lm])) (by positivity)
  -- the terms of the sum over the bound block indices
  set F : (Fin R.nb → Fin D) → (Idx D N → Idx D N → ℂ) → Idx D N → Idx D N → ℝ :=
    fun ι h i j => (R.weights.map (Fwt ι h)).prod * (R.loops.map fun w => Fw ι h w i j).prod
    with hF
  have hcr : ∀ ι h, (Matrix.of h).IsHermitian →
      PS_FC (F ι h) ((R.profile pr).map fun f => Cc * f.val N η m (hsNorm e.A)).prod 2 :=
    fun ι h hh => PS_comb R pr _ (mul_nonneg (by linarith) (hval0 _)) (Fwt ι h) (Fw ι h)
      (fun p _ => ⟨norm_nonneg _, hwtc ι h hh p⟩) (fun w _ i j => norm_nonneg _)
      (fun w hw => (hwd ι w hw).1 h hh) hsum2.le
  have hgd : ∀ ι : Fin R.nb → Fin D, ∃ s : Set (Idx D N → Idx D N → ℂ),
      μ s ≤ ENNReal.ofReal (n * b0) ∧ ∀ h, h ∉ s → (Matrix.of h).IsHermitian →
        PS_FC (F ι h) ((R.profile pr).map fun f => Cg * f.val N η m (hsNorm e.A)).prod 2 := by
    intro ι
    obtain ⟨s₁, hs₁, hP₁⟩ := PS_bad_list μ (fun (p : Fin 2 × ℕ) h => Fwt ι h p ≤
        Cg * PkgFac.val N η m (hsNorm e.A) .wt) (fun _ => b0) (fun _ => hb0) R.weights
      fun p _ => by
        obtain ⟨bad, hbad, hgood⟩ := hW p.1 (e.E ι p.2) (Bd_opNorm_E e ι p.2)
        refine ⟨bad, hbad.trans (PS_ev1 hD1 hN1 D'), fun h hh => (hgood h hh).trans ?_⟩
        simp only [PkgFac.val]
        rw [heta p.1, abs_of_pos hη, one_div]
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity)
          (PS_Cg_one K hK1 Lm)) (by positivity)
    obtain ⟨s₂, hs₂, hP₂⟩ := PS_bad_list μ (fun w h => (Matrix.of h).IsHermitian →
        PS_FC (Fw ι h w) ((pkgWordFac pr w).map fun f => Cg * f.val N η m (hsNorm e.A)).prod
          (w.countP PkgLetter.isLam)) (fun w => (pkgWordFac pr w).length * b0)
      (fun _ => by positivity) R.loops fun w hw => by
        obtain ⟨s, hs, hP⟩ := (hwd ι w hw).2
        exact ⟨s, hs, fun h hh hH => hP h hh hH⟩
    refine ⟨s₁ ∪ s₂, (measure_union_le _ _).trans ((add_le_add hs₁ hs₂).trans ?_),
      fun h hh hH => ?_⟩
    · rw [← ENNReal.ofReal_add (List.sum_nonneg fun y hy => by
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact hb0)
        (List.sum_nonneg fun y hy => by obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hn, PS_profile_len, List.map_const', List.sum_replicate, nsmul_eq_mul]
      push_cast
      rw [add_mul]
      congr 1
      rw [List.sum_map_mul_right, List.map_map]
      rfl
    · exact PS_comb R pr _ (mul_nonneg (by linarith) (hval0 _)) (Fwt ι h) (Fw ι h)
        (fun p hp => ⟨norm_nonneg _, hP₁ h (fun h' => hh (Or.inl h')) p hp⟩)
        (fun w _ i j => norm_nonneg _)
        (fun w hw => hP₂ h (fun h' => hh (Or.inr h')) w hw hH) hsum2.le
  obtain ⟨bad, hbad, hgood⟩ := PS_bad_fin μ (fun ι h => h ∉ ({} : Set (Idx D N → Idx D N → ℂ)) →
      (Matrix.of h).IsHermitian → PS_FC (F ι h)
        ((R.profile pr).map fun f => Cg * f.val N η m (hsNorm e.A)).prod 2) (n * b0)
    (by positivity) fun ι => by
      obtain ⟨s, hs, hP⟩ := hgd ι
      exact ⟨s, hs, fun h hh _ hH => hP h hh hH⟩
  have hcard : (Fintype.card (Fin R.nb → Fin D) : ℝ) = (D : ℝ) ^ R.nb := by simp
  rw [hcard] at hbad
  -- the label sums
  set coef : ℝ := |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ (-R.S) with hcoef
  have hcoef0 : 0 ≤ coef := by positivity
  have hsum : ∀ h (V : ℝ), (∀ ι, PS_FC (F ι h) V 2) →
      ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
        ‖R.evalP e pr (fun l => if l = 0 then i else j) h‖ else 0) ≤
        coef * ((D : ℝ) ^ R.nb * (16 * D * N ^ 2 * V)) := by
    intro h V hV
    calc ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
          ‖R.evalP e pr (fun l => if l = 0 then i else j) h‖ else 0)
        ≤ ∑ i : Idx D N, ∑ j : Idx D N, coef * ∑ ι : Fin R.nb → Fin D,
            (if i.1 = j.1 then F ι h i j else 0) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact PS_evalP_le R e pr _ h
          · simp
      _ = coef * ∑ i : Idx D N, ∑ j : Idx D N, ∑ ι : Fin R.nb → Fin D,
            (if i.1 = j.1 then F ι h i j else 0) := by
          simp only [Finset.mul_sum]
      _ = coef * ∑ ι : Fin R.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
            (if i.1 = j.1 then F ι h i j else 0) := by
          congr 1
          exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
      _ ≤ coef * ∑ _ι : Fin R.nb → Fin D, 16 * D * N ^ 2 * V :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ι _ => PS_FC_sum hD1 (hV ι)) hcoef0
      _ = coef * ((D : ℝ) ^ R.nb * (16 * D * N ^ 2 * V)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  set Vg := ((R.profile pr).map fun f => Cg * f.val N η m (hsNorm e.A)).prod with hVg
  set Vc := ((R.profile pr).map fun f => Cc * f.val N η m (hsNorm e.A)).prod with hVc
  set bg := coef * ((D : ℝ) ^ R.nb * (16 * D * N ^ 2 * Vg)) with hbg
  set Bc := coef * ((D : ℝ) ^ R.nb * (16 * D * N ^ 2 * Vc)) with hBc
  have hVg0 : 0 ≤ Vg := List.prod_nonneg fun y hy => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hy; exact mul_nonneg (by linarith) (hval0 f)
  have hVc0 : 0 ≤ Vc := List.prod_nonneg fun y hy => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hy; exact mul_nonneg (by linarith) (hval0 f)
  have hbg0 : 0 ≤ bg := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  -- integration
  set G : Idx D N → Idx D N → (Idx D N → Idx D N → ℂ) → ℝ := fun i j h =>
    if i.1 = j.1 then ‖R.evalP e pr (fun l => if l = 0 then i else j) h‖ else 0 with hG
  have hGcr : ∀ h, (Matrix.of h).IsHermitian → ∑ i, ∑ j, G i j h ≤ Bc :=
    fun h hh => hsum h _ fun ι => hcr ι h hh
  have hG0 : ∀ i j h, 0 ≤ G i j h := fun i j h => by
    simp only [hG]; split_ifs <;> simp
  have hGle : ∀ i j h, (Matrix.of h).IsHermitian → G i j h ≤ Bc := by
    intro i j h hh
    refine le_trans ?_ (hGcr h hh)
    refine le_trans ?_ (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ =>
      hG0 i' j' h) (Finset.mem_univ i))
    exact Finset.single_le_sum (fun j' _ => hG0 i j' h) (Finset.mem_univ j)
  have hGm : ∀ i j, Measurable (G i j) := by
    intro i j
    simp only [hG]
    split_ifs
    · exact (PS_meas_evalP R e pr _).norm
    · exact measurable_const
  have hGi : ∀ i j, Integrable (G i j) μ := by
    intro i j
    refine Integrable.mono' (integrable_const Bc) (hGm i j).aestronglyMeasurable ?_
    filter_upwards [hμ.herm] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 i j h)]
    exact hGle i j h hh
  have hstep1 : ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
      ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ else 0) ≤
      ∑ i, ∑ j, ∫ h, G i j h ∂μ := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i.1 = j.1
    · simp only [hij, ↓reduceIte, hG]
      exact norm_integral_le_integral_norm _
    · simp [hij, hG]
  have hstep2 : ∑ i, ∑ j, ∫ h, G i j h ∂μ = ∫ h, ∑ i, ∑ j, G i j h ∂μ := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hGi i j]
    exact Finset.sum_congr rfl fun i _ =>
      (integral_finsetSum _ fun j _ => hGi i j).symm
  have hint : Integrable (fun h => bg + (toMeasurable μ bad).indicator (fun _ => Bc) h) μ :=
    (integrable_const _).add ((integrable_const Bc).indicator (measurableSet_toMeasurable _ _))
  have hstep3 : ∫ h, ∑ i, ∑ j, G i j h ∂μ ≤
      ∫ h, (bg + (toMeasurable μ bad).indicator (fun _ => Bc) h) ∂μ := by
    refine integral_mono_ae (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hGi i j) hint ?_
    filter_upwards [hμ.herm] with h hh
    by_cases hb : h ∈ toMeasurable μ bad
    · rw [Set.indicator_of_mem hb]
      exact (hGcr h hh).trans (by linarith)
    · rw [Set.indicator_of_notMem hb, add_zero]
      have hnb : h ∉ bad := fun h' => hb (subset_toMeasurable _ _ h')
      exact hsum h _ fun ι => hgood h hnb ι (by simp) hh
  have hstep4 : ∫ h, (bg + (toMeasurable μ bad).indicator (fun _ => Bc) h) ∂μ ≤
      bg + (D : ℝ) ^ R.nb * (n * b0) * Bc := by
    rw [integral_add (integrable_const _)
      ((integrable_const Bc).indicator (measurableSet_toMeasurable _ _)), integral_const,
      integral_indicator_const _ (measurableSet_toMeasurable _ _), probReal_univ, one_smul,
      smul_eq_mul]
    have hreal : μ.real (toMeasurable μ bad) ≤ (D : ℝ) ^ R.nb * (n * b0) := by
      rw [Measure.real, measure_toMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
    nlinarith
  -- the final value
  have hprod : ∀ c : ℝ, ((R.profile pr).map fun f => c * f.val N η m (hsNorm e.A)).prod =
      c ^ n * ((R.profile pr).map fun f => f.val N η m (hsNorm e.A)).prod := by
    intro c
    rw [List.prod_map_mul, List.map_const', List.prod_replicate]
  have hsharp : R.sharpB D N η m (hsNorm e.A) pr = coef * (D : ℝ) ^ R.nb *
      ((R.profile pr).map fun f => f.val N η m (hsNorm e.A)).prod := by
    unfold PkgExpr.sharpB
    rw [hcoef, zpow_add₀ (by positivity : (D : ℝ) ≠ 0), zpow_natCast]
    ring
  calc ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
        ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ else 0)
      ≤ bg + (D : ℝ) ^ R.nb * (n * b0) * Bc := hstep1.trans (hstep2.le.trans
        (hstep3.trans hstep4))
    _ = _ := by
        rw [hbg, hBc, hVg, hVc, hprod Cg, hprod Cc, hsharp]
        ring

end Main

/-! ## The loops with one `Λ̃` and no resolvent -/

/-- `pkg_lam0_bound` for all the loops of a list at once. -/
private lemma PS_lam0_all (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) :
    ∀ L : List (List PkgLetter), ∃ K₀ : ℝ, 0 < K₀ ∧ ∃ N₀ : ℕ, ∀ w ∈ L,
      (∃ w₀ : List LoopLetter, w = w₀.map PkgLetter.lw) → w.countP PkgLetter.isLam = 1 →
      w.countP PkgLetter.isRes = 0 → ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ) (κ : ℕ → Idx D N),
        ‖ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w)‖ ≤
          K₀ * ((if pkgGainLoop w then (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im else 1) *
            avgSq (lam D N e.A))
  | [] => ⟨1, one_pos, 0, fun w hw => by simp at hw⟩
  | w :: L => by
    obtain ⟨K₁, hK₁, N₁, h₁⟩ := PS_lam0_all D hD δA εA ε hδA hεA hε hε' hε'' L
    by_cases hc : (∃ w₀ : List LoopLetter, w = w₀.map PkgLetter.lw) ∧
        w.countP PkgLetter.isLam = 1 ∧ w.countP PkgLetter.isRes = 0
    · obtain ⟨⟨w₀, rfl⟩, hl, hr⟩ := hc
      have hl' : w₀.countP (fun x => match x with | .lamt _ => true | _ => false) = 1 := by
        rw [List.countP_map] at hl
        rw [← hl]
        congr 1
        funext x
        cases x <;> rfl
      have hr' : w₀.countP (fun x => match x with | .res _ => true | _ => false) = 0 := by
        rw [List.countP_map] at hr
        rw [← hr]
        congr 1
        funext x
        cases x <;> rfl
      obtain ⟨K₂, hK₂, N₂, h₂⟩ := pkg_lam0_bound D hD δA εA ε hδA hεA hε hε' hε'' w₀ hl' hr'
      refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, max N₁ N₂, fun w' hw' hc' hl'' hr'' N hN A hA k
        hk hkN hhs e he nb ι h κ => ?_⟩
      have hav : 0 ≤ (if pkgGainLoop w' then (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im
          else 1) * avgSq (lam D N e.A) := by
        refine mul_nonneg ?_ (Bd_avgSq_nonneg _ (lam_isHermitian D N _))
        split_ifs
        · exact PS_im_nonneg _ _
        · exact zero_le_one
      rcases List.mem_cons.1 hw' with rfl | hw'
      · rw [PE_wm_lw]
        exact (h₂ N (le_trans (le_max_right _ _) hN) A hA k hk hkN hhs e he nb ι h).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hav)
      · exact (h₁ w' hw' hc' hl'' hr'' N (le_trans (le_max_left _ _) hN) A hA k hk hkN hhs e he
          nb ι h κ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hav)
    · refine ⟨K₁, hK₁, N₁, fun w' hw' hc' hl'' hr'' => ?_⟩
      rcases List.mem_cons.1 hw' with rfl | hw'
      · exact absurd ⟨hc', hl'', hr''⟩ hc
      · exact h₁ w' hw' hc' hl'' hr''

/-! ## The final arithmetic -/

/-- `16 (C N^{τ'})^n + D^{nb} n 2 (DN)² N^{-(3n+3)} 16 (C' N³)^n ≤ N^τ` for
`τ' = τ / (2(n+1))` and `N` large. -/
private lemma PS_arith (D N n nb : ℕ) (τ Cg Cc : ℝ) (hτ : 0 < τ) (hN : 1 ≤ N) (hCg : 1 ≤ Cg)
    (h1 : 32 * Cg ^ n ≤ (N : ℝ) ^ (τ / 2))
    (h2 : 64 * n * (D : ℝ) ^ (nb + 2) * Cc ^ n ≤ N) :
    16 * (Cg * (N : ℝ) ^ (τ / (2 * (n + 1)))) ^ n +
      (D : ℝ) ^ nb * (n * (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(3 * (n : ℝ) + 3)))) *
        (16 * (Cc * (N : ℝ) ^ 3) ^ n) ≤ (N : ℝ) ^ τ := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hτ2 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hNr (by positivity)
  have hNτ : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  -- the first term
  have e1 : (Cg * (N : ℝ) ^ (τ / (2 * (n + 1)))) ^ n =
      Cg ^ n * (N : ℝ) ^ (n * (τ / (2 * (n + 1)))) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hN0.le, mul_comm (τ / (2 * ((n : ℝ) + 1))) (n : ℝ)]
  have e2 : (N : ℝ) ^ (n * (τ / (2 * (n + 1)))) ≤ (N : ℝ) ^ (τ / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hNr ?_
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have t1 : 16 * (Cg * (N : ℝ) ^ (τ / (2 * (n + 1)))) ^ n ≤ (N : ℝ) ^ τ / 2 := by
    rw [e1, hNτ]
    have : 0 ≤ Cg ^ n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e2 this]
  -- the second term
  have e3 : (N : ℝ) ^ (-(3 * (n : ℝ) + 3)) = ((N : ℝ) ^ (3 * n + 3))⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf
  have t2 : (D : ℝ) ^ nb * (n * (2 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(3 * (n : ℝ) + 3)))) *
      (16 * (Cc * (N : ℝ) ^ 3) ^ n) = 32 * n * (D : ℝ) ^ (nb + 2) * Cc ^ n * (N : ℝ)⁻¹ := by
    rw [e3]
    have hNne : (N : ℝ) ≠ 0 := hN0.ne'
    field_simp
    ring
  rw [t2]
  have t3 : 32 * n * (D : ℝ) ^ (nb + 2) * Cc ^ n * (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hN0]
    linarith
  have : (1 : ℝ) / 2 ≤ (N : ℝ) ^ τ / 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
    linarith
  linarith

/-! ## The direct estimation -/

set_option maxHeartbeats 2000000 in
-- the bounds of the factors are combined in one proof
/-- The direct estimation (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1] for one
derivative structure, the statement of `pkg_sharp_bound`. -/
private lemma PS_sharp (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (T : LoopExpr)
    (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (pr : Fin 2 → Bool)
    (hpr : R.pairIn pr = true) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
            ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ else 0) ≤
          (N : ℝ) ^ τ * ((D : ℝ) * (N : ℝ) ^ 2 * R.sharpB D N (etaK D N k ε)
            (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im (hsNorm A) pr) := by
  intro τ hτ
  obtain ⟨K₀, hK₀, N₂, hlam⟩ := PS_lam0_all D hD δA εA ε hδA hεA hε hε' hε'' R.loops
  obtain ⟨c₀, K, hc₀, hK, hK₀K, N₁, hslot⟩ := PS_slot D hD δA εA ε hδA hεA hε hε' hε'' C K₀
  obtain ⟨-, -, hfree⟩ := PS_shape T hT hf p q R hR
  set n := (R.profile pr).length with hn
  set Lm := (R.loops.map List.length).sum with hLmdef
  have hLm : ∀ w ∈ R.loops, w.length ≤ Lm := fun w hw =>
    List.le_sum_of_mem (List.mem_map_of_mem hw)
  set τ' : ℝ := τ / (2 * ((n : ℝ) + 1)) with hτ'def
  have hτ' : 0 < τ' := by positivity
  set D' : ℝ := 3 * (n : ℝ) + 3 with hD'def
  have hD' : 0 < D' := by positivity
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hev := PS_ev D hD δA (ε / 2) c₀ K hδA (by positivity) hc₀ hK1 C Lm τ' hτ' D' hD'
  have hW := Bd_weight D (by omega) δA (ε / 2) 1 hδA (by positivity) le_rfl C τ' hτ' D' hD'
  obtain ⟨N₃, hN₃⟩ := Bd_large (τ / 2) (32 * PS_Cg K Lm ^ n) (by positivity)
  obtain ⟨N₄, hN₄⟩ := Bd_large 1 (64 * n * (D : ℝ) ^ (R.nb + 2) * PS_Cc K Lm ^ n) one_pos
  obtain ⟨N₅, hN₅⟩ := Filter.eventually_atTop.1 (hev.and hW)
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 1)),
    fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNd : N₄ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNe : N₅ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  obtain ⟨hctx, hMK, hpairK, havg, heA⟩ := hslot N hNa μ hμ A hA k hk hkN hhs e he
  obtain ⟨⟨hI, hO, hT2⟩, hWN⟩ := hN₅ N hNe
  have hc0 := hctx e.M hMK (fun _ => 1) (fun _ => Bd_opNorm_one)
  obtain ⟨hη, hm, -⟩ := PS_Ctx_pos hc0 hK1
  have hW' : ∀ (a : Fin 2) (B : Matrix (Idx D N) (Idx D N) ℂ), opNorm B ≤ 1 →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, h ∉ bad → ‖ntr ((e.G h a - e.M a) * B)‖ ≤
          (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |(e.z a).im|)) :=
    fun a B hB => hWN μ hμ e hc0.1.1 hc0.1.2.2.1 (fun a => (hc0.1.2.2.2.1 a).1) a B hB
  have hlam0 : ∀ w ∈ R.loops, w.any PkgLetter.isEnt = false → w.countP PkgLetter.isLam = 1 →
      w.countP PkgLetter.isRes = 0 → ∀ (ι : Fin R.nb → Fin D) h (κ : ℕ → Idx D N),
      ‖ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w)‖ ≤
        K * ((if pkgGainLoop w then (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im else 1) *
          avgSq (lam D N e.A)) := by
    intro w hw hwe h1 h2 ι h κ
    have hav : 0 ≤ (if pkgGainLoop w then (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im
        else 1) * avgSq (lam D N e.A) := by
      refine mul_nonneg ?_ (Bd_avgSq_nonneg _ (lam_isHermitian D N _))
      split_ifs
      · exact PS_im_nonneg _ _
      · exact zero_le_one
    exact (hlam w hw (hfree w hw hwe).2.2 h1 h2 N hNb A hA k hk hkN hhs e he _ ι h κ).trans
      (mul_le_mul_of_nonneg_right hK₀K hav)
  have hmain := PS_main_N hD hK hτ'.le hI hO hT2 T hT hf p q R hR pr hpr hLm hμ e hctx hMK
    hpairK havg hW' hlam0
  rw [show hsNorm e.A = hsNorm A by rw [heA]] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine PS_arith D N n R.nb τ (PS_Cg K Lm) (PS_Cc K Lm) hτ hN1 (PS_Cg_one K hK1 Lm)
      (hN₃ N hNc) ?_
    simpa using hN₄ N hNd
  · have hs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
    unfold PkgExpr.sharpB
    refine mul_nonneg (by positivity) (mul_nonneg (by positivity) (List.prod_nonneg fun y hy => ?_))
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hy
    exact PS_val_nonneg N hη hm.le hs0 f

/-- The direct estimation (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1] in the proof
of Lemma 5.5 [claim_estimate_remainder_terms] for one derivative structure: at the slots of
Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law],
the sum over the label pairs of one block of `|E 𝓡|`, with paired letters `𝔐_a - 𝔐_a^*` in
words with `Δ`, is at most `N^τ D N² sharpB`, `η = N^{-2/3+ε} 𝔯(k)^{-1/3}`, `Im m` of slot `1`. -/
theorem pkg_sharp_bound (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (T : LoopExpr)
    (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (pr : Fin 2 → Bool)
    (hpr : R.pairIn pr = true) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
            ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ else 0) ≤
          (N : ℝ) ^ τ * ((D : ℝ) * (N : ℝ) ^ 2 * R.sharpB D N (etaK D N k ε)
            (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im (hsNorm A) pr) := by
  exact PS_sharp D hD δA εA ε hδA hεA hε hε' hε'' C T hT hf p q R hR pr hpr

end RBMTransitionEdge

end
