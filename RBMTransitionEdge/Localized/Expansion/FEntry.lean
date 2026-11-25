module

public import RBMTransitionEdge.Localized.Expansion.FOpts
public import RBMTransitionEdge.Localized.Expansion.FactorBound
public import RBMTransitionEdge.Localized.Expansion.Pairing
public import RBMTransitionEdge.Localized.Expansion.AddLambda
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.LocalLaw.MultiRes
import all RBMTransitionEdge.Localized.Expansion.PkgSharp
import all RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.LocalLaw.MultiRes
import all RBMTransitionEdge.Localized.Expansion.FactorBound
import all RBMTransitionEdge.Localized.Expansion.FOpts

@[expose] public section

/-!
# The value of one option of an entry

At the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law], outside an event of probability `≤ N^{-D'}`, the mixed
norm `foptNorm` of an entry factor under one option of its menu is at most `N^{τ'}` times the size
of the option: for an entry without `Λ̃` (isotropic (A.53) [entprodG], a Ward row or column, the
Hilbert–Schmidt norm), and for every entry ((5.90) [eq:addoneLambda], the double split, the splits
at one `Λ̃`), as used in (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Mixed norms of a nonnegative function of two labels -/

section Norms

variable {ι : Type*} [Fintype ι]

/-- The sup norm (`false`) or the `ℓ²` norm (`true`) of a function of one label. -/
private def FE_nrm (m : Bool) (a : ι → ℝ) : ℝ :=
  if m then Real.sqrt (∑ x, a x ^ 2) else ⨆ x, a x

omit [Fintype ι] in
private lemma FE_le_sup [Finite ι] (a : ι → ℝ) (x : ι) : a x ≤ ⨆ x, a x :=
  le_ciSup (Set.finite_range a).bddAbove x

private lemma FE_nrm_nonneg (m : Bool) (a : ι → ℝ) (ha : ∀ x, 0 ≤ a x) : 0 ≤ FE_nrm m a := by
  cases m
  · exact Real.iSup_nonneg ha
  · exact Real.sqrt_nonneg _

private lemma FE_sqrt_mul_sq (a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (∑ x, (a x * c) ^ 2) = Real.sqrt (∑ x, a x ^ 2) * c := by
  have e : ∑ x, (a x * c) ^ 2 = (∑ x, a x ^ 2) * c ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e, Real.sqrt_mul (Finset.sum_nonneg fun x _ => sq_nonneg _), Real.sqrt_sq hc]

private lemma FE_sqrt_mul_sq' (b : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (∑ y, (c * b y) ^ 2) = c * Real.sqrt (∑ y, b y ^ 2) := by
  rw [mul_comm c, ← FE_sqrt_mul_sq b c hc]
  simp only [mul_comm]

/-- The mixed norm of a function bounded by a product `a(x) b(y)`: the product of the norms. -/
private lemma FE_cs_prod (f : ι → ι → ℝ) (a b : ι → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hf0 : ∀ x y, 0 ≤ f x y) (hf : ∀ x y, f x y ≤ a x * b y) (m₁ m₂ : Bool) :
    fcsNorm f m₁ m₂ ≤ FE_nrm m₁ a * FE_nrm m₂ b := by
  have hsa := Real.iSup_nonneg ha
  have hsb := Real.iSup_nonneg hb
  cases m₁ <;> cases m₂ <;> simp only [fcsNorm, FE_nrm, Bool.false_eq_true, ↓reduceIte]
  · refine Real.iSup_le (fun x => Real.iSup_le (fun y => ?_) (mul_nonneg hsa hsb))
      (mul_nonneg hsa hsb)
    exact (hf x y).trans (mul_le_mul (FE_le_sup a x) (FE_le_sup b y) (hb y) hsa)
  · rw [← FE_sqrt_mul_sq' b _ hsa]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun y _ => ?_)
    refine pow_le_pow_left₀ (Real.iSup_nonneg fun x => hf0 x y) ?_ 2
    exact Real.iSup_le (fun x => (hf x y).trans (mul_le_mul_of_nonneg_right (FE_le_sup a x)
      (hb y))) (mul_nonneg hsa (hb y))
  · refine Real.iSup_le (fun y => ?_) (mul_nonneg (Real.sqrt_nonneg _) hsb)
    calc Real.sqrt (∑ x, f x y ^ 2) ≤ Real.sqrt (∑ x, (a x * b y) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (hf0 x y) (hf x y) 2)
      _ = Real.sqrt (∑ x, a x ^ 2) * b y := FE_sqrt_mul_sq a (b y) (hb y)
      _ ≤ Real.sqrt (∑ x, a x ^ 2) * ⨆ y, b y :=
          mul_le_mul_of_nonneg_left (FE_le_sup b y) (Real.sqrt_nonneg _)
  · have e : ∑ x, ∑ y, (a x * b y) ^ 2 = (∑ x, a x ^ 2) * ∑ y, b y ^ 2 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    calc Real.sqrt (∑ x, ∑ y, f x y ^ 2) ≤ Real.sqrt (∑ x, ∑ y, (a x * b y) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            pow_le_pow_left₀ (hf0 x y) (hf x y) 2)
      _ = _ := by
          rw [e, Real.sqrt_mul (Finset.sum_nonneg fun x _ => sq_nonneg _)]

/-- The mixed norm with the first label in `ℓ²` from a bound `b(y)` of the inner `ℓ²` norms. -/
private lemma FE_cs_inner (f : ι → ι → ℝ) (b : ι → ℝ) (hb : ∀ y, 0 ≤ b y)
    (hf : ∀ y, Real.sqrt (∑ x, f x y ^ 2) ≤ b y) (m₂ : Bool) :
    fcsNorm f true m₂ ≤ FE_nrm m₂ b := by
  cases m₂ <;> simp only [fcsNorm, FE_nrm, Bool.false_eq_true, ↓reduceIte]
  · exact Real.iSup_le (fun y => (hf y).trans (FE_le_sup b y)) (Real.iSup_nonneg hb)
  · rw [Finset.sum_comm]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun y _ => ?_)
    exact (Real.sqrt_le_left (hb y)).1 (hf y)

/-- The norm of an option of an entry with distinct labels, bounded by a product `a(x) b(y)`. -/
private lemma FE_opt_prod (o : FOpt) (rf : Bool) (f : ι → ι → ℝ) (a b : ι → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hf0 : ∀ x y, 0 ≤ f x y)
    (hf : ∀ x y, f x y ≤ a x * b y) :
    foptNorm false o rf f ≤ FE_nrm (o.cx == 1) a * FE_nrm (o.cy == 1) b := by
  unfold foptNorm
  cases rf
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mul_comm]
    exact FE_cs_prod _ b a hb ha (fun y x => hf0 x y) (fun y x => by
      rw [mul_comm]; exact hf x y) _ _
  · exact FE_cs_prod f a b ha hb hf0 hf _ _

/-- The norm of an option with the row label summed first in `ℓ²`. -/
private lemma FE_opt_col (o : FOpt) (hcx : o.cx = 1) (f : ι → ι → ℝ) (b : ι → ℝ)
    (hb : ∀ y, 0 ≤ b y) (hf : ∀ y, Real.sqrt (∑ x, f x y ^ 2) ≤ b y) :
    foptNorm false o true f ≤ FE_nrm (o.cy == 1) b := by
  unfold foptNorm
  simp only [Bool.false_eq_true, ↓reduceIte, hcx, beq_self_eq_true]
  exact FE_cs_inner f b hb hf _

/-- The norm of an option with the column label summed first in `ℓ²`. -/
private lemma FE_opt_row (o : FOpt) (hcy : o.cy = 1) (f : ι → ι → ℝ) (a : ι → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hf : ∀ x, Real.sqrt (∑ y, f x y ^ 2) ≤ a x) :
    foptNorm false o false f ≤ FE_nrm (o.cx == 1) a := by
  unfold foptNorm
  simp only [Bool.false_eq_true, ↓reduceIte, hcy, beq_self_eq_true]
  exact FE_cs_inner (fun y x => f x y) a ha hf _

/-- The norm of an option with both labels in `ℓ²`: the Hilbert–Schmidt norm. -/
private lemma FE_opt_hs (o : FOpt) (hcx : o.cx = 1) (hcy : o.cy = 1) (rf : Bool)
    (f : ι → ι → ℝ) (B : ℝ) (hf : Real.sqrt (∑ x, ∑ y, f x y ^ 2) ≤ B) :
    foptNorm false o rf f ≤ B := by
  unfold foptNorm
  cases rf <;> simp only [Bool.false_eq_true, ↓reduceIte, hcx, hcy, beq_self_eq_true, fcsNorm]
  · rw [Finset.sum_comm]
    exact hf
  · exact hf

/-- The norm of an option of a diagonal entry with its uses `cx + cy`, bounded by a product. -/
private lemma FE_opt_diag (cx cy : ℕ) (hcx : cx ≤ 1) (hcy : cy ≤ 1) (v : List FMono) (rf : Bool)
    (f : ι → ι → ℝ) (a b : ι → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hf0 : ∀ x y, 0 ≤ f x y) (hf : ∀ x y, f x y ≤ a x * b y) :
    foptNorm true ⟨cx + cy, 0, 0, v⟩ rf f ≤ FE_nrm (cx == 1) a * FE_nrm (cy == 1) b := by
  have hsa := Real.iSup_nonneg ha
  have hsb := Real.iSup_nonneg hb
  have hd : ∀ x, f x x ≤ a x * b x := fun x => hf x x
  have h1 : Real.sqrt (∑ x, f x x ^ 2) ≤ Real.sqrt (∑ x, (a x * b x) ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (hf0 x x) (hd x) 2)
  unfold foptNorm
  simp only [↓reduceIte]
  interval_cases cx <;> interval_cases cy <;>
    simp only [FE_nrm, Nat.reduceAdd, beq_self_eq_true, Nat.reduceBEq, Bool.false_eq_true,
      ↓reduceIte, zero_add, add_zero]
  · exact Real.iSup_le (fun x => (hd x).trans (mul_le_mul (FE_le_sup a x) (FE_le_sup b x)
      (hb x) hsa)) (mul_nonneg hsa hsb)
  · refine h1.trans ?_
    rw [← FE_sqrt_mul_sq' b _ hsa]
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => pow_le_pow_left₀
      (mul_nonneg (ha x) (hb x)) (mul_le_mul_of_nonneg_right (FE_le_sup a x) (hb x)) 2)
  · refine h1.trans ?_
    rw [← FE_sqrt_mul_sq a _ hsb]
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => pow_le_pow_left₀
      (mul_nonneg (ha x) (hb x)) (mul_le_mul_of_nonneg_left (FE_le_sup b x) (ha x)) 2)
  · exact (Finset.sum_le_sum fun x _ => hd x).trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

/-- The `ℓ²` norm of a diagonal entry is at most its Hilbert–Schmidt norm. -/
private lemma FE_opt_diag_hs (v : List FMono) (rf : Bool) (f : ι → ι → ℝ) (B : ℝ)
    (hf : Real.sqrt (∑ x, ∑ y, f x y ^ 2) ≤ B) :
    foptNorm true ⟨1, 0, 0, v⟩ rf f ≤ B := by
  unfold foptNorm
  simp only [↓reduceIte]
  refine le_trans (Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => ?_)) hf
  exact Finset.single_le_sum (f := fun y => f x y ^ 2) (fun y _ => sq_nonneg _)
    (Finset.mem_univ x)

end Norms

open private PS_It PS_it PS_v PS_nr PS_adj PS_v_append PS_v_adj PS_nr_adj PS_nr_append PS_adj_det
  PS_Adm PS_Gr PS_b PS_fbw PS_fbt PS_bnd PS_psi_nonneg PS_rows PS_tr_le PS_entry_cs PS_dot_single
  PS_single_sq PS_gram_facts PS_v_gram PS_rows_lt2 PS_card PS_bad_fin PS_b_nonneg PS_psi_sq
  PS_Lt_herm from RBMTransitionEdge.Localized.Expansion.PkgSharp
open private Bd_opNorm_nonneg Bd_opNorm_one Bd_opNorm_conjTranspose Bd_opNorm_E Bd_avgSq_le
  Bd_avgSq_nonneg Bd_opNorm_sub Bd_ntr_le from RBMTransitionEdge.Localized.Expansion.Bound
open private MultiRes_vn MultiRes_vn_sq MultiRes_vn_nonneg MultiRes_vn_smul MultiRes_vn_eq_zero
  MultiRes_vn_mulVec_le MultiRes_norm_dot_le MultiRes_hs2_mul_left_le MultiRes_hs2_mul_right_le
  MultiRes_hsNorm_sq MultiRes_vn_single MultiRes_hs2_cols MultiRes_hs2 MultiRes_vn_of_sum
  from RBMTransitionEdge.LocalLaw.MultiRes
open private FB_eq_zero from RBMTransitionEdge.Localized.Expansion.FactorBound
open private FO_facts FO_isRes FO_evalR_mul FO_evalR_nonneg FO_ev_psi FO_ext FO_spl FO_rest
  FO_fopts2 from RBMTransitionEdge.Localized.Expansion.FOpts

/-! ### The slots -/

/-- The bound `N^{-1/3+ε/2} 𝔯(k)^{1/3}` on `Im m` at the slots. -/
private abbrev FE_M (D N k : ℕ) (ε : ℝ) : ℝ :=
  (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)

/-- The facts at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law] for the bounds of the entries, with one constant `K`:
the hypotheses of Lemma A.4 [lemma_necessary_estimates], `Im z_a = η`, the bound on `Im m_a`, the
norms of `𝔐_a`, `𝔐_a - 𝔐_aᴴ`, `Λ`, `Λ̃` and the shift `δ`. -/
private def FE_Slot (D N : ℕ) (δA ε c₀ K : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (e : LoopEnv D N) : Prop :=
  PS_Adm D N δA (ε / 2) c₀ K e ∧ e.A = A ∧ 1 ≤ N ∧ 1 ≤ K ∧
  (∀ a, (e.z a).im = etaK D N k ε) ∧ 0 < etaK D N k ε ∧ 0 < FE_M D N k ε ∧
  (∀ a, (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤ K * FE_M D N k ε) ∧
  (∀ a, opNorm (e.M a) ≤ K) ∧ (∀ a, opNorm (e.M a - (e.M a)ᴴ) ≤ K * FE_M D N k ε) ∧
  opNorm e.Lt ≤ K * opNorm A ∧ hsNorm e.Lt ≤ K * hsNorm A ∧
  hsNorm (lam D N e.A) ≤ K * hsNorm A ∧ opNorm A ≤ 1 ∧ opNorm (lam D N e.A) ≤ K * opNorm A ∧
  |e.δ| ≤ K * (hsNorm A ^ 2 / N)

set_option maxHeartbeats 1000000 in
private lemma FE_slot (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) :
    ∃ c₀ K : ℝ, 0 < c₀ ∧ 1 ≤ K ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        FE_Slot D N δA ε c₀ K A k e := by
  obtain ⟨c₀, K, CU, hc₀, hK2, hCU, N₁, hfac⟩ := FO_facts D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨Kp, hKp, N₂, hpair⟩ := pkg_pair_norm D hD δA εA ε hδA hεA hε hε' hε''
  set K₀ : ℝ := K + CU + Kp * CU + K * K with hK₀
  have hKK : K ≤ K₀ := by rw [hK₀]; nlinarith
  have hCK : CU ≤ K₀ := by rw [hK₀]; nlinarith
  have hPK : Kp * CU ≤ K₀ := by rw [hK₀]; nlinarith
  have hK2K : 2 + K ≤ K₀ := by rw [hK₀]; nlinarith
  have hKKK : K * K ≤ K₀ := by rw [hK₀]; nlinarith
  refine ⟨c₀, K₀, hc₀, by linarith, max N₁ N₂, fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  obtain ⟨hadm, heA, hN1, heta, hη, hMb, hCU', hm1, hM, -, hsLt, hslam, havg⟩ :=
    hfac N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he
  have hpr := hpair N (le_of_max_le_right hN) A hA k hk hkN hhs e he
  obtain ⟨hAn, hA2, hc, hz, hδ⟩ := hadm
  have hav0 : 0 ≤ avgSq (lam D N e.A) := Bd_avgSq_nonneg _ (lam_isHermitian D N _)
  have hop0 : 0 ≤ opNorm A := Bd_opNorm_nonneg A
  have hop : opNorm A ≤ 1 / 20 := by rw [← heA]; linarith
  have hl : opNorm (lam D N e.A) ≤ 2 * opNorm A := heA ▸ opNorm_lam_le D N e.A
  have hl0 : 0 ≤ opNorm (lam D N e.A) := Bd_opNorm_nonneg _
  have hδ0 : |e.δ| ≤ K * (4 * opNorm A ^ 2) := hδ.trans (mul_le_mul_of_nonneg_left
    ((Bd_avgSq_le _).trans (by nlinarith)) (by linarith))
  have hLt : opNorm e.Lt ≤ K₀ * opNorm A := by
    unfold LoopEnv.Lt
    refine (Bd_opNorm_sub _ _).trans ?_
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := Bd_opNorm_one (ι := Idx D N)
    have h0 := Bd_opNorm_nonneg (1 : Matrix (Idx D N) (Idx D N) ℂ)
    have h2 : |e.δ| * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ K * opNorm A := by
      have : |e.δ| ≤ K * opNorm A :=
        hδ0.trans (mul_le_mul_of_nonneg_left (by nlinarith) (by linarith))
      nlinarith [abs_nonneg e.δ]
    nlinarith [mul_le_mul_of_nonneg_right hK2K hop0]
  refine ⟨⟨hAn, hA2, hc, hz, hδ.trans (mul_le_mul_of_nonneg_right hKK hav0)⟩, heA, hN1,
    by linarith, heta, hη, hMb, fun a => (hCU' a).trans (mul_le_mul_of_nonneg_right hCK hMb.le),
    fun a => (hM a).trans hKK, fun a => ?_, hLt, hsLt.trans (mul_le_mul_of_nonneg_right hKK
      (Real.sqrt_nonneg _)), hslam.trans (mul_le_mul_of_nonneg_right hKK (Real.sqrt_nonneg _)),
    by linarith, hl.trans (mul_le_mul_of_nonneg_right (by linarith) hop0), ?_⟩
  · refine (hpr a).trans ?_
    have := hCU' 1
    calc Kp * (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im ≤ Kp * (CU * FE_M D N k ε) :=
          mul_le_mul_of_nonneg_left this hKp.le
      _ = (Kp * CU) * FE_M D N k ε := by ring
      _ ≤ K₀ * FE_M D N k ε := mul_le_mul_of_nonneg_right hPK hMb.le
  · refine hδ.trans ?_
    rw [← heA] at havg ⊢
    have hs0 : 0 ≤ hsNorm e.A ^ 2 / N := by positivity
    calc K * avgSq (lam D N e.A) ≤ K * (K * (hsNorm e.A ^ 2 / N)) :=
          mul_le_mul_of_nonneg_left havg (by linarith)
      _ = (K * K) * (hsNorm e.A ^ 2 / N) := by ring
      _ ≤ K₀ * (hsNorm e.A ^ 2 / N) := mul_le_mul_of_nonneg_right hKKK hs0

/-! ### The letters as factors of a product of Lemma A.4 -/

/-- The letter is a paired `𝔐_a - 𝔐_aᴴ`. -/
private def FE_isPr : FLet → Bool
  | .det _ pr => pr
  | _ => false

/-- A factor letter as a factor of a product of Lemma A.4 [lemma_necessary_estimates], with `Λ̃`
divided by `op` and `𝔐_a - 𝔐_aᴴ` divided by `m`. -/
private def FE_hat {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (op m : ℝ) :
    FLet → PS_It (Idx D N)
  | .res a f => .inl (a, f)
  | .det a pr => .inr (if pr then ((m⁻¹ : ℝ) : ℂ) • (e.M a - (e.M a)ᴴ) else e.M a)
  | .proj x => .inr (e.E ι x)
  | .lamt => .inr (if op = 0 then 0 else ((op⁻¹ : ℝ) : ℂ) • e.Lt)

/-- The scale taken out of a letter by `FE_hat`. -/
private def FE_sc (op m : ℝ) : FLet → ℝ
  | .det _ pr => if pr then m else 1
  | .lamt => op
  | _ => 1

private lemma FE_mat_hat {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (op m : ℝ)
    (hm : m ≠ 0) (hL : op = 0 → e.Lt = 0) (h : Idx D N → Idx D N → ℂ) (z : FLet) :
    FLet.mat e ι h z = ((FE_sc op m z : ℝ) : ℂ) • PS_it (PS_Gr e h) (FE_hat e ι op m z) := by
  cases z with
  | res a f => simp [FLet.mat, FE_sc, FE_hat, PS_it, PS_Gr]
  | det a pr =>
    cases pr
    · simp [FLet.mat, FE_sc, FE_hat, PS_it]
    · simp only [FLet.mat, FE_sc, FE_hat, PS_it, ↓reduceIte, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hm, Complex.ofReal_one, one_smul]
  | proj x => simp [FLet.mat, FE_sc, FE_hat, PS_it]
  | lamt =>
    simp only [FLet.mat, FE_sc, FE_hat, PS_it]
    by_cases h0 : op = 0
    · simp [h0, hL h0]
    · rw [ite_eq_right h0, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one,
        one_smul]

private lemma FE_prod_hat {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (op m : ℝ)
    (hm : m ≠ 0) (hL : op = 0 → e.Lt = 0) (h : Idx D N → Idx D N → ℂ) (u : List FLet) :
    (u.map (FLet.mat e ι h)).prod =
      (((u.map (FE_sc op m)).prod : ℝ) : ℂ) • PS_v (PS_Gr e h) (u.map (FE_hat e ι op m)) := by
  induction u with
  | nil => simp [PS_v]
  | cons z u ih =>
    simp only [List.map_cons, List.prod_cons, PS_v] at ih ⊢
    rw [ih, FE_mat_hat e ι op m hm hL h z, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.ofReal_mul]

private lemma FE_sc_prod (op m : ℝ) (u : List FLet) :
    (u.map (FE_sc op m)).prod = op ^ u.countP (· == .lamt) * m ^ u.countP FE_isPr := by
  induction u with
  | nil => simp
  | cons z u ih =>
    rw [List.map_cons, List.prod_cons, ih]
    cases z with
    | res a f => simp [FE_sc, FE_isPr]
    | det a pr =>
      cases pr
      · simp [FE_sc, FE_isPr]
      · simp [FE_sc, FE_isPr, List.countP_cons, pow_succ]; ring
    | proj x => simp [FE_sc, FE_isPr]
    | lamt => simp [FE_sc, FE_isPr, pow_succ]; ring

private lemma FE_hat_nr {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (op m : ℝ)
    (u : List FLet) : PS_nr (u.map (FE_hat e ι op m)) = u.countP FO_isRes := by
  unfold PS_nr
  rw [List.countP_map]
  congr 1
  funext z
  cases z <;> rfl

private lemma FE_hat_det {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (op m K : ℝ)
    (hK : 1 ≤ K) (hm : 0 < m) (hop : 0 ≤ op) (hM : ∀ a, opNorm (e.M a) ≤ K)
    (hP : ∀ a, opNorm (e.M a - (e.M a)ᴴ) ≤ K * m) (hL : opNorm e.Lt ≤ K * op) (u : List FLet) :
    ∀ B, Sum.inr B ∈ u.map (FE_hat e ι op m) → opNorm B ≤ K := by
  intro B hB
  obtain ⟨z, -, hzB⟩ := List.mem_map.1 hB
  cases z with
  | res a f => cases hzB
  | det a pr =>
    cases hzB
    cases pr
    · exact hM a
    · simp only [↓reduceIte]
      rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hm),
        inv_mul_le_iff₀ hm, mul_comm]
      exact hP a
  | proj x =>
    cases hzB
    exact (Bd_opNorm_E e ι x).trans hK
  | lamt =>
    cases hzB
    split_ifs with h0
    · rw [show opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 by simp [opNorm]]
      linarith
    · have hop' : 0 < op := lt_of_le_of_ne hop (Ne.symm h0)
      rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hop'),
        inv_mul_le_iff₀ hop', mul_comm]
      exact hL

/-! ### Products, vectors and norms -/

section Vec

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product of Lemma A.4 [lemma_necessary_estimates] without resolvent: `‖Π‖ ≤ K^{len}`. -/
private lemma FE_det_norm (G : Fin 2 → Matrix ι ι ℂ) (K : ℝ) (hK : 1 ≤ K) :
    ∀ l : List (PS_It ι), PS_nr l = 0 → (∀ B, Sum.inr B ∈ l → opNorm B ≤ K) →
      opNorm (PS_v G l) ≤ K ^ l.length
  | [], _, _ => by simpa [PS_v] using Bd_opNorm_one
  | .inl t :: l, h0, _ => by simp [PS_nr, List.countP_cons] at h0
  | .inr X :: l, h0, hB => by
    have ih := FE_det_norm G K hK l (by simpa [PS_nr, List.countP_cons] using h0)
      fun B hB' => hB B (by simp [hB'])
    simp only [PS_v, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    refine (opNorm_mul_le _ _).trans ?_
    rw [pow_succ']
    exact mul_le_mul (hB X (by simp)) ih (Bd_opNorm_nonneg _) (by linarith)

omit [DecidableEq ι] in
private lemma FE_dot_adj (Y : Matrix ι ι ℂ) (v w : ι → ℂ) :
    star v ⬝ᵥ (Y *ᵥ w) = star (Yᴴ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

omit [DecidableEq ι] in
private lemma FE_dot_self (w : ι → ℂ) : star w ⬝ᵥ w = ((MultiRes_vn w ^ 2 : ℝ) : ℂ) := by
  rw [MultiRes_vn_sq]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
/-- `⟨v, Y Y^* v⟩ = ‖Y^* v‖²`. -/
private lemma FE_quad (Y : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ ((Y * Yᴴ) *ᵥ v) = ((MultiRes_vn (Yᴴ *ᵥ v) ^ 2 : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, FE_dot_adj, FE_dot_self]

/-- `|⟨u, X v⟩| ≤ ‖X‖ ‖u‖ ‖v‖`. -/
private lemma FE_dot_le (X : Matrix ι ι ℂ) (u v : ι → ℂ) :
    ‖star u ⬝ᵥ (X *ᵥ v)‖ ≤ opNorm X * MultiRes_vn u * MultiRes_vn v := by
  refine (MultiRes_norm_dot_le u (X *ᵥ v)).trans ?_
  have := MultiRes_vn_mulVec_le X v
  have h0 := MultiRes_vn_nonneg u
  nlinarith

/-- `‖X‖_HS ≤ |ι|^{1/2} ‖X‖`. -/
private lemma FE_hs_le_op (X : Matrix ι ι ℂ) :
    hsNorm X ≤ Real.sqrt (Fintype.card ι) * opNorm X := by
  have h1 : hsNorm X ^ 2 ≤ (Fintype.card ι : ℝ) * opNorm X ^ 2 := by
    rw [MultiRes_hsNorm_sq, MultiRes_hs2_cols]
    have hc : ∀ q, MultiRes_vn (fun p => X p q) ≤ opNorm X := fun q => by
      have e : (fun p => X p q) = X *ᵥ Pi.single q 1 := by
        ext p
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [e]
      refine (MultiRes_vn_mulVec_le _ _).trans ?_
      rw [MultiRes_vn_single, mul_one]
    calc ∑ q, MultiRes_vn (fun p => X p q) ^ 2 ≤ ∑ _q : ι, opNorm X ^ 2 :=
          Finset.sum_le_sum fun q _ => pow_le_pow_left₀ (MultiRes_vn_nonneg _) (hc q) 2
      _ = _ := by simp
  have h0 : 0 ≤ Real.sqrt (Fintype.card ι) * opNorm X :=
    mul_nonneg (Real.sqrt_nonneg _) (Bd_opNorm_nonneg _)
  refine (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) h0 two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h1

omit [DecidableEq ι] in
/-- The isotropic bound for unit vectors gives the bound `B ‖u‖ ‖v‖` for any `u`, `v` off one
event. -/
private lemma FE_iso_vec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Matrix ι ι ℂ)
    (B δ : ℝ) (hiso : ∀ u v : ι → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
      μ {h | B < ‖star u ⬝ᵥ (X h *ᵥ v)‖} ≤ ENNReal.ofReal δ) (u v : ι → ℂ) :
    ∃ s : Set Ω, μ s ≤ ENNReal.ofReal δ ∧
      ∀ h ∉ s, ‖star u ⬝ᵥ (X h *ᵥ v)‖ ≤ B * MultiRes_vn u * MultiRes_vn v := by
  by_cases hu : MultiRes_vn u = 0
  · refine ⟨∅, by simp, fun h _ => ?_⟩
    obtain rfl := MultiRes_vn_eq_zero hu
    simp [hu]
  by_cases hv : MultiRes_vn v = 0
  · refine ⟨∅, by simp, fun h _ => ?_⟩
    obtain rfl := MultiRes_vn_eq_zero hv
    simp [hv]
  have hu0 : 0 < MultiRes_vn u := lt_of_le_of_ne (MultiRes_vn_nonneg _) (Ne.symm hu)
  have hv0 : 0 < MultiRes_vn v := lt_of_le_of_ne (MultiRes_vn_nonneg _) (Ne.symm hv)
  set uh : ι → ℂ := (((MultiRes_vn u)⁻¹ : ℝ) : ℂ) • u with huh
  set vh : ι → ℂ := (((MultiRes_vn v)⁻¹ : ℝ) : ℂ) • v with hvh
  have hn : ∀ w : ι → ℂ, 0 < MultiRes_vn w →
      ∑ x, ‖((((MultiRes_vn w)⁻¹ : ℝ) : ℂ) • w) x‖ ^ 2 = 1 := fun w hw => by
    rw [← MultiRes_vn_sq, MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hw), inv_mul_cancel₀ hw.ne', one_pow]
  have hback : ∀ w : ι → ℂ, 0 < MultiRes_vn w →
      w = ((MultiRes_vn w : ℝ) : ℂ) • ((((MultiRes_vn w)⁻¹ : ℝ) : ℂ) • w) := fun w hw => by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_smul]
  refine ⟨{h | B < ‖star uh ⬝ᵥ (X h *ᵥ vh)‖}, hiso uh vh (hn u hu0) (hn v hv0), fun h hh => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt] at hh
  have e : star u ⬝ᵥ (X h *ᵥ v) =
      ((MultiRes_vn u : ℝ) : ℂ) * ((MultiRes_vn v : ℝ) : ℂ) * (star uh ⬝ᵥ (X h *ᵥ vh)) := by
    conv_lhs => rw [hback u hu0, hback v hv0]
    rw [← huh, ← hvh, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul]
    ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hu0, abs_of_pos hv0]
  nlinarith [norm_nonneg (star uh ⬝ᵥ (X h *ᵥ vh)), mul_pos hu0 hv0]

end Vec

/-! ### Events and powers of `N` -/

/-- Two bounds off two events hold together off their union. -/
private lemma FE_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {P Q : Ω → Prop}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h₁ : ∃ s : Set Ω, μ s ≤ ENNReal.ofReal a ∧ ∀ h ∉ s, P h)
    (h₂ : ∃ s : Set Ω, μ s ≤ ENNReal.ofReal b ∧ ∀ h ∉ s, Q h) :
    ∃ s : Set Ω, μ s ≤ ENNReal.ofReal (a + b) ∧ ∀ h ∉ s, P h ∧ Q h := by
  obtain ⟨s₁, hs₁, hP⟩ := h₁
  obtain ⟨s₂, hs₂, hQ⟩ := h₂
  refine ⟨s₁ ∪ s₂, (measure_union_le _ _).trans ?_, fun h hh =>
    ⟨hP h fun h' => hh (Or.inl h'), hQ h fun h' => hh (Or.inr h')⟩⟩
  rw [ENNReal.ofReal_add ha hb]
  exact add_le_add hs₁ hs₂

/-- `c N^{-(D'+j)} ≤ N^{-D'}` for `0 ≤ c ≤ N^j`. -/
private lemma FE_pow_le (N : ℕ) (hN : 1 ≤ N) (D' c : ℝ) (j : ℕ) (_hc0 : 0 ≤ c)
    (hc : c ≤ (N : ℝ) ^ j) : c * (N : ℝ) ^ (-(D' + j)) ≤ (N : ℝ) ^ (-D') := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ (-(D' + j)) = (N : ℝ) ^ (-D') * ((N : ℝ) ^ j)⁻¹ := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg hN0.le (j : ℝ), Real.rpow_natCast]
  rw [e]
  have hp : 0 < (N : ℝ) ^ j := pow_pos hN0 j
  have h1 : c * ((N : ℝ) ^ j)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hp, one_mul]
    exact hc
  have h2 := Real.rpow_nonneg hN0.le (-D')
  nlinarith

/-- `(D N)² ≤ N³` for `N ≥ D²`. -/
private lemma FE_card_le (D N : ℕ) (c : ℕ) (hN : c * D ^ 2 ≤ N) :
    (c : ℝ) * ((D : ℝ) * N) ^ 2 ≤ (N : ℝ) ^ 3 := by
  have h : ((c * D ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [sq_nonneg (N : ℝ), mul_le_mul_of_nonneg_right h (sq_nonneg (N : ℝ))]

private lemma FE_card (D N : ℕ) : (Fintype.card (Idx D N × Idx D N) : ℝ) = ((D : ℝ) * N) ^ 2 := by
  simp [Fintype.card_prod]
  ring

/-- `a ≤ √B b` from `a² ≤ B b²`, `a, b ≥ 0`. -/
private lemma FE_sqrt_of_sq (a b B : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ B * b * b) :
    a ≤ Real.sqrt B * b := by
  rcases le_or_gt 0 B with hB | hB
  · rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, ← Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · have : a ^ 2 ≤ 0 := h.trans (by nlinarith [mul_nonneg hb hb])
    have ha0 : a = 0 := by nlinarith
    rw [ha0]
    exact mul_nonneg (Real.sqrt_nonneg _) hb

/-- `√(t C x²) ≤ t √C x` for `t ≥ 1`. -/
private lemma FE_sqrt_le (t C x : ℝ) (ht : 1 ≤ t) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    Real.sqrt (t * (C * x ^ 2)) ≤ t * (Real.sqrt C * x) := by
  rw [Real.sqrt_mul (by linarith), Real.sqrt_mul hC, Real.sqrt_sq hx]
  have : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  exact mul_le_mul_of_nonneg_right this (mul_nonneg (Real.sqrt_nonneg _) hx)

/-! ### One word between vectors -/

/-- `(Im m)^{1/2} η^{1/2-r}` for `r ≥ 1` and `1` for `r = 0`, the value of `FMono.omega`. -/
private def FE_om (η m : ℝ) (r : ℕ) : ℝ := if 1 ≤ r then Real.sqrt (pkgPsi η m (2 * r)) else 1

private lemma FE_om_nonneg (η m : ℝ) (r : ℕ) : 0 ≤ FE_om η m r := by
  unfold FE_om
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact zero_le_one

/-- The bounds of a matrix `U` between the vectors of `V`: `|⟨v₁, U v₂⟩| ≤ Bi ‖v₁‖ ‖v₂‖`,
`‖U^* v₁‖ ≤ Br ‖v₁‖`, `‖U v₂‖ ≤ Br ‖v₂‖`. -/
private def FE_WV {D N : ℕ} (U : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (Bi Br : ℝ) : Prop :=
  (∀ j, ‖star (V j).1 ⬝ᵥ (U *ᵥ (V j).2)‖ ≤ Bi * MultiRes_vn (V j).1 * MultiRes_vn (V j).2) ∧
  (∀ j, MultiRes_vn (Uᴴ *ᵥ (V j).1) ≤ Br * MultiRes_vn (V j).1) ∧
  (∀ j, MultiRes_vn (U *ᵥ (V j).2) ≤ Br * MultiRes_vn (V j).2)

private lemma FE_WV_smul {D N : ℕ} (U : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (Bi Br c : ℝ) (hc : 0 ≤ c)
    (h : FE_WV U V Bi Br) : FE_WV ((c : ℂ) • U) V (c * Bi) (c * Br) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc]
    have := mul_le_mul_of_nonneg_left (h1 j) hc
    linarith
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mulVec,
      MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    have := mul_le_mul_of_nonneg_left (h2 j) hc
    linarith
  · rw [Matrix.smul_mulVec, MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc]
    have := mul_le_mul_of_nonneg_left (h3 j) hc
    linarith

private lemma FE_WV_mono {D N : ℕ} (U : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (Bi Br Bi' Br' : ℝ) (hi : Bi ≤ Bi')
    (hr : Br ≤ Br') (h : FE_WV U V Bi Br) : FE_WV U V Bi' Br' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).trans ?_, fun j => (h2 j).trans ?_, fun j => (h3 j).trans ?_⟩
  · have := MultiRes_vn_nonneg (V j).1
    have := MultiRes_vn_nonneg (V j).2
    gcongr
  · exact mul_le_mul_of_nonneg_right hr (MultiRes_vn_nonneg _)
  · exact mul_le_mul_of_nonneg_right hr (MultiRes_vn_nonneg _)

/-- The isotropic events of a word for every pair of vectors of a family. -/
private lemma FE_iso_fam {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ))
    (X : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) (B δ : ℝ) (hδ : 0 ≤ δ)
    (hiso : ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
      μ {h | B < ‖star u ⬝ᵥ (X h *ᵥ v)‖} ≤ ENNReal.ofReal δ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) :
    ∃ s, μ s ≤ ENNReal.ofReal (((D : ℝ) * N) ^ 2 * δ) ∧ ∀ h ∉ s, ∀ j,
      ‖star (V j).1 ⬝ᵥ (X h *ᵥ (V j).2)‖ ≤ B * MultiRes_vn (V j).1 * MultiRes_vn (V j).2 := by
  obtain ⟨s, hs, hP⟩ := PS_bad_fin μ (fun j h => ‖star (V j).1 ⬝ᵥ (X h *ᵥ (V j).2)‖ ≤
    B * MultiRes_vn (V j).1 * MultiRes_vn (V j).2) δ hδ
    fun j => FE_iso_vec μ X B δ hiso (V j).1 (V j).2
  exact ⟨s, hs.trans_eq (by rw [FE_card]), hP⟩

/-- The vector bounds of a word with resolvents: isotropic (A.53) [entprodG] between the vectors,
and the Ward bounds `‖U^* v‖² = ⟨v, U U^* v⟩`, `‖U v‖² = ⟨v, U^* U v⟩` by (A.53) with the doubled
word. -/
private lemma FE_vecs (D : ℕ) (hD : 2 ≤ D) (δA ε c₀ K : ℝ) (hδA : 0 < δA) (hε : 0 < ε)
    (hc₀ : 0 < c₀) (hK : 1 ≤ K) (C : ℕ → ℝ) (u : List FLet) (hr : 1 ≤ u.countP FO_isRes)
    (τ : ℝ) (hτ : 0 < τ) (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (e : LoopEnv D N), FE_Slot D N δA ε c₀ K A k e →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D) (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)),
      ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h ∉ bad, FE_WV ((u.map (FLet.mat e ι h)).prod) V
          (Cst * (N : ℝ) ^ τ * (pkgPsi (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
            (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr)))
          (Cst * (N : ℝ) ^ τ * (FE_om (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
            (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr))) := by
  set r := u.countP FO_isRes with hrdef
  set L := u.length with hL
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (PS_fbw D hD δA (ε / 2) c₀ K hδA (by positivity)
    hc₀ hK C (2 * L) r hr τ hτ (D' + 3) (by positivity))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (PS_fbw D hD δA (ε / 2) c₀ K hδA (by positivity)
    hc₀ hK C (2 * L) (2 * r) (by omega) τ hτ (D' + 3) (by positivity))
  set C₁ : ℝ := (K ^ (2 * L)) ^ (r + 1) * K with hC₁
  set C₂ : ℝ := (K ^ (2 * L)) ^ (2 * r + 1) * K with hC₂
  have hK0 : 0 ≤ K := by linarith
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + Real.sqrt C₂, by positivity, max (max N₁ N₂) (3 * D ^ 2 + 1),
    fun N hN μ hμ A k e hS nb ι V => ?_⟩
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 * D ^ 2 ≤ N := by have := le_trans (le_max_right _ _) hN; omega
  obtain ⟨hadm, -, hN1, -, heta, hη, hm, him, hM, hP, hLt, -, -, hop1, -, -⟩ := hS
  set η := etaK D N k ε
  set m := FE_M D N k ε
  set op := opNorm A
  have hop0 : 0 ≤ op := Bd_opNorm_nonneg A
  have hLz : op = 0 → e.Lt = 0 := fun h0 => by
    have : opNorm e.Lt ≤ 0 := hLt.trans (by rw [h0, mul_zero])
    exact FB_eq_zero _ this
  set l := u.map (FE_hat e ι op m) with hl
  have hlr : PS_nr l = r := FE_hat_nr e ι op m u
  have hll : l.length = L := by simp [hl, hL]
  have hld := FE_hat_det e ι op m K hK hm hop0 hM hP hLt u
  obtain ⟨hgr, hgr', hgl, hgl', hgd, hgd'⟩ := PS_gram_facts l K hld
  set sc := (u.map (FE_sc op m)).prod with hsc
  have hsc' : sc = op ^ u.countP (· == .lamt) * m ^ u.countP FE_isPr := FE_sc_prod op m u
  have hsc0 : 0 ≤ sc := by rw [hsc']; positivity
  have hU : ∀ h, (u.map (FLet.mat e ι h)).prod = (sc : ℂ) • PS_v (PS_Gr e h) l := fun h =>
    FE_prod_hat e ι op m hm.ne' hLz h u
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
  have hδ0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D' + 3)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- the three families of events
  have hI := FE_iso_fam μ (fun h => PS_v (PS_Gr e h) l) _ _ hδ0
    (hN₁ N hN1' μ hμ K e hadm l hlr (by omega) hld).2 V
  have hR := FE_iso_fam μ (fun h => PS_v (PS_Gr e h) (l ++ l.reverse.map PS_adj)) _ _ hδ0
    (hN₂ N hN2' μ hμ K e hadm _ (by rw [hgr', hlr]) (le_of_eq (by rw [hgl', hll])) hgd').2
    (fun j => ((V j).1, (V j).1))
  have hC := FE_iso_fam μ (fun h => PS_v (PS_Gr e h) (l.reverse.map PS_adj ++ l)) _ _ hδ0
    (hN₂ N hN2' μ hμ K e hadm _ (by rw [hgr, hlr]) (le_of_eq (by rw [hgl, hll])) hgd).2
    (fun j => ((V j).2, (V j).2))
  have hcnt : 0 ≤ ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(D' + 3)) := by positivity
  obtain ⟨bad, hbad, hgood⟩ := FE_union μ (by positivity) hcnt (FE_union μ hcnt hcnt hI hR) hC
  refine ⟨bad, hbad.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh => ?_⟩
  · have := FE_pow_le N hN1 D' (3 * (((D : ℝ) * N) ^ 2)) 3 (by positivity)
      (by exact_mod_cast FE_card_le D N 3 hN3)
    push_cast at this
    linarith
  obtain ⟨⟨hi, hr'⟩, hc⟩ := hgood h hh
  have hb1 := PS_bnd hη heta hK him r
  have hb2 := PS_bnd hη heta hK him (2 * r)
  have hψ1 := PS_psi_nonneg hη hm.le r
  have hψ2 := PS_psi_nonneg hη hm.le (2 * r)
  have hom : FE_om η m r ^ 2 = pkgPsi η m (2 * r) := by
    unfold FE_om
    rw [ite_eq_left hr, Real.sq_sqrt hψ2]
  have hom0 := FE_om_nonneg η m r
  -- the bound `√B₂ ≤ Cst N^τ ω(r)`
  have hB2 : Real.sqrt ((N : ℝ) ^ τ * ((K ^ (2 * L)) ^ (2 * r + 1) * PS_b e (2 * r))) ≤
      (C₁ + Real.sqrt C₂) * (N : ℝ) ^ τ * FE_om η m r := by
    have h1 : (N : ℝ) ^ τ * ((K ^ (2 * L)) ^ (2 * r + 1) * PS_b e (2 * r)) ≤
        (N : ℝ) ^ τ * (C₂ * FE_om η m r ^ 2) := by
      rw [hom, hC₂, mul_assoc]
      gcongr
    refine (Real.sqrt_le_sqrt h1).trans ((FE_sqrt_le _ _ _ hNτ hC₂0 hom0).trans ?_)
    have : Real.sqrt C₂ ≤ C₁ + Real.sqrt C₂ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ τ)
      hom0)]
  have hWV : FE_WV (PS_v (PS_Gr e h) l) V
      ((C₁ + Real.sqrt C₂) * (N : ℝ) ^ τ * pkgPsi η m r)
      ((C₁ + Real.sqrt C₂) * (N : ℝ) ^ τ * FE_om η m r) := by
    refine ⟨fun j => (hi j).trans ?_, fun j => ?_, fun j => ?_⟩
    · have hv := mul_nonneg (MultiRes_vn_nonneg (V j).1) (MultiRes_vn_nonneg (V j).2)
      rw [mul_assoc _ (MultiRes_vn _), mul_assoc _ (MultiRes_vn _)]
      refine mul_le_mul_of_nonneg_right ?_ hv
      calc (N : ℝ) ^ τ * ((K ^ (2 * L)) ^ (r + 1) * PS_b e r)
          ≤ (N : ℝ) ^ τ * ((K ^ (2 * L)) ^ (r + 1) * (K * pkgPsi η m r)) := by gcongr
        _ = C₁ * (N : ℝ) ^ τ * pkgPsi η m r := by rw [hC₁]; ring
        _ ≤ (C₁ + Real.sqrt C₂) * (N : ℝ) ^ τ * pkgPsi η m r := by
            gcongr
            linarith [Real.sqrt_nonneg C₂]
    · have hq := hr' j
      rw [(PS_v_gram _ l).2, FE_quad, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)] at hq
      refine (FE_sqrt_of_sq _ _ _ (MultiRes_vn_nonneg _) (MultiRes_vn_nonneg _) hq).trans ?_
      exact mul_le_mul_of_nonneg_right hB2 (MultiRes_vn_nonneg _)
    · have hq := hc j
      rw [(PS_v_gram _ l).1, show (PS_v (PS_Gr e h) l)ᴴ * PS_v (PS_Gr e h) l =
        (PS_v (PS_Gr e h) l)ᴴ * ((PS_v (PS_Gr e h) l)ᴴ)ᴴ by rw [Matrix.conjTranspose_conjTranspose],
        FE_quad, Matrix.conjTranspose_conjTranspose, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)] at hq
      refine (FE_sqrt_of_sq _ _ _ (MultiRes_vn_nonneg _) (MultiRes_vn_nonneg _) hq).trans ?_
      exact mul_le_mul_of_nonneg_right hB2 (MultiRes_vn_nonneg _)
  rw [hU h]
  refine FE_WV_mono _ V _ _ _ _ (le_of_eq ?_) (le_of_eq ?_) (FE_WV_smul _ V _ _ sc hsc0 hWV)
  · rw [hsc']; ring
  · rw [hsc']; ring

/-- The value of `fhalf`: the size of one row (`l2 = false`) or the Hilbert–Schmidt norm
(`l2 = true`) of a word with `n` letters `Λ̃` and `r` resolvents. -/
private def FE_half (N : ℕ) (η m hs op : ℝ) (n r : ℕ) (l2 : Bool) : ℝ :=
  if l2 then (if n = 0 then FE_om η m r * Real.sqrt N else FE_om η m r * hs * op ^ (n - 1))
  else FE_om η m r * op ^ n

private lemma FE_half_nonneg (N : ℕ) {η m hs op : ℝ} (hhs : 0 ≤ hs) (hop : 0 ≤ op) (n r : ℕ)
    (l2 : Bool) : 0 ≤ FE_half N η m hs op n r l2 := by
  have := FE_om_nonneg η m r
  unfold FE_half
  split_ifs <;> positivity

private lemma FE_hs_smul {ι : Type*} [Fintype ι] (c : ℝ) (X : Matrix ι ι ℂ) :
    hsNorm ((c : ℂ) • X) = |c| * hsNorm X := by
  unfold hsNorm
  have e : ∑ i, ∑ j, ‖((c : ℂ) • X) i j‖ ^ 2 = c ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private lemma FE_hs_sq {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    hsNorm X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  unfold hsNorm
  exact Real.sq_sqrt (by positivity)

/-- The Hilbert–Schmidt norm of a word with resolvents: (A.53) [entprodG] averaged on `U U^*`
without `Λ̃`, and (A.55) [two_loop_estimate] on `⟨Q Q^* Λ̃ P^* P Λ̃⟩` for `U = P Λ̃ Q`. -/
private lemma FE_hs (D : ℕ) (hD : 2 ≤ D) (δA ε c₀ K : ℝ) (hδA : 0 < δA) (hε : 0 < ε)
    (hc₀ : 0 < c₀) (hK : 1 ≤ K) (C : ℕ → ℝ) (u : List FLet) (hr : 1 ≤ u.countP FO_isRes)
    (τ : ℝ) (hτ : 0 < τ) (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (e : LoopEnv D N), FE_Slot D N δA ε c₀ K A k e →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D),
      ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h ∉ bad, hsNorm ((u.map (FLet.mat e ι h)).prod) ≤ Cst * (N : ℝ) ^ τ *
          (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A) (u.countP (· == .lamt))
            (u.countP FO_isRes) true * FE_M D N k ε ^ u.countP FE_isPr) := by
  set r := u.countP FO_isRes with hrdef
  set L := u.length with hL
  have hK0 : 0 ≤ K := by linarith
  rcases Nat.eq_zero_or_pos (u.countP (· == .lamt)) with hn | hn
  · -- no `Λ̃`: (A.53) averaged on `U U^*`
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (PS_fbw D hD δA (ε / 2) c₀ K hδA
      (by positivity) hc₀ hK C (2 * L) (2 * r) (by omega) τ hτ (D' + 1) (by positivity))
    set C₂ : ℝ := (K ^ (2 * L)) ^ (2 * r + 1) * K with hC₂
    have hC₂0 : 0 ≤ C₂ := by positivity
    refine ⟨Real.sqrt (D * C₂), Real.sqrt_nonneg _, max N₂ 1,
      fun N hN μ hμ A k e hS nb ι => ?_⟩
    obtain ⟨hadm, -, hN1, -, heta, hη, hm, him, hM, hP, hLt, -, -, -, -, -⟩ := hS
    set η := etaK D N k ε
    set m := FE_M D N k ε
    set op := opNorm A
    have hop0 : 0 ≤ op := Bd_opNorm_nonneg A
    have hLz : op = 0 → e.Lt = 0 := fun h0 => FB_eq_zero _ (hLt.trans (by rw [h0, mul_zero]))
    set l := u.map (FE_hat e ι op m) with hl
    have hlr : PS_nr l = r := FE_hat_nr e ι op m u
    have hll : l.length = L := by simp [hl, hL]
    have hld := FE_hat_det e ι op m K hK hm hop0 hM hP hLt u
    obtain ⟨-, hgr', -, hgl', -, hgd'⟩ := PS_gram_facts l K hld
    have hev := (hN₂ N (le_of_max_le_left hN) μ hμ K e hadm _ (by rw [hgr', hlr])
      (le_of_eq (by rw [hgl', hll])) hgd').1
    refine ⟨_, hev.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh => ?_⟩
    · have hN1' : 1 ≤ N := le_trans (le_max_right _ _) hN
      have := FE_pow_le N hN1' D' 1 1 zero_le_one (by simpa using (by exact_mod_cast hN1' :
        (1 : ℝ) ≤ N))
      simpa using this
    simp only [Set.mem_ofPred_eq, not_lt] at hh
    have hsc' : (u.map (FE_sc op m)).prod = m ^ u.countP FE_isPr := by
      rw [FE_sc_prod, hn, pow_zero, one_mul]
    rw [FE_prod_hat e ι op m hm.ne' hLz h u, hsc', FE_hs_smul, abs_of_nonneg (by positivity)]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
    have hb2 := PS_bnd hη heta hK him (2 * r)
    have hψ2 := PS_psi_nonneg hη hm.le (2 * r)
    have hom : FE_om η m r ^ 2 = pkgPsi η m (2 * r) := by
      unfold FE_om
      rw [ite_eq_left hr, Real.sq_sqrt hψ2]
    have hom0 := FE_om_nonneg η m r
    set X := PS_v (PS_Gr e h) l
    have h1 : hsNorm X ^ 2 ≤ D * N * ‖ntr (X * Xᴴ)‖ := by
      rw [FE_hs_sq, PS_rows, ← PS_card]
      exact PS_tr_le _
    rw [← (PS_v_gram _ l).2] at h1
    have h2 : hsNorm X ^ 2 ≤ (N : ℝ) ^ τ * ((D * C₂) * (FE_om η m r * Real.sqrt N) ^ 2) := by
      refine h1.trans ?_
      have hD0 : (0 : ℝ) ≤ D * N := by positivity
      calc (D : ℝ) * N * ‖ntr (PS_v (PS_Gr e h) (l ++ l.reverse.map PS_adj))‖
          ≤ D * N * ((N : ℝ) ^ τ * ((K ^ (2 * L)) ^ (2 * r + 1) * PS_b e (2 * r))) :=
            mul_le_mul_of_nonneg_left hh hD0
        _ ≤ D * N * ((N : ℝ) ^ τ * ((K ^ (2 * L)) ^ (2 * r + 1) * (K * pkgPsi η m (2 * r)))) := by
            gcongr
        _ = (N : ℝ) ^ τ * ((D * C₂) * (FE_om η m r * Real.sqrt N) ^ 2) := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hom, hC₂]
            ring
    have h3 := (Real.sqrt_le_sqrt h2).trans (FE_sqrt_le _ _ _ hNτ (by positivity)
      (mul_nonneg hom0 (Real.sqrt_nonneg _)))
    have hX0 : 0 ≤ hsNorm X := Real.sqrt_nonneg _
    rw [Real.sqrt_sq hX0] at h3
    have hm0 : 0 ≤ m ^ u.countP FE_isPr := by positivity
    unfold FE_half
    simp only [↓reduceIte, hn]
    calc m ^ u.countP FE_isPr * hsNorm X
        ≤ m ^ u.countP FE_isPr * ((N : ℝ) ^ τ * (Real.sqrt (D * C₂) *
          (FE_om η m r * Real.sqrt N))) := mul_le_mul_of_nonneg_left h3 hm0
      _ = _ := by ring
  · -- with `Λ̃`: `U = P Λ̃ Q` and (A.55)
    obtain ⟨P, Q, hPQ⟩ : ∃ P Q : List FLet, u = P ++ FLet.lamt :: Q := by
      obtain ⟨z, hz, hz'⟩ := List.countP_pos_iff.1 hn
      have : z = FLet.lamt := by simpa using hz'
      exact List.append_of_mem (this ▸ hz)
    have hcr : r = P.countP FO_isRes + Q.countP FO_isRes := by
      rw [hrdef, hPQ, List.countP_append, List.countP_cons]
      simp [FO_isRes]
    have hcl : u.countP (· == .lamt) = P.countP (· == .lamt) + Q.countP (· == .lamt) + 1 := by
      rw [hPQ, List.countP_append, List.countP_cons]
      simp
      ring
    have hcp : u.countP FE_isPr = P.countP FE_isPr + Q.countP FE_isPr := by
      rw [hPQ, List.countP_append, List.countP_cons]
      simp [FE_isPr]
    have hPL : P.length ≤ L := by
      rw [hL, hPQ, List.length_append, List.length_cons]; omega
    have hQL : Q.length ≤ L := by
      rw [hL, hPQ, List.length_append, List.length_cons]; omega
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (PS_fbt D hD δA (ε / 2) c₀ K K hδA
      (by positivity) hc₀ hK C (2 * L) (2 * Q.countP FO_isRes) (2 * P.countP FO_isRes)
      (by omega) τ hτ (D' + 1) (by positivity))
    set Cm : ℝ := max (K ^ (2 * L)) K ^ (2 * Q.countP FO_isRes + 2 * P.countP FO_isRes + 2)
      with hCm
    have hCm0 : 0 ≤ Cm := by positivity
    refine ⟨Real.sqrt (D * (Cm * K ^ 3)), Real.sqrt_nonneg _, max N₂ 1,
      fun N hN μ hμ A k e hS nb ι => ?_⟩
    obtain ⟨hadm, heA, hN1, -, heta, hη, hm, him, hM, hP, hLt, -, hslam, -, -, -⟩ := hS
    set η := etaK D N k ε
    set m := FE_M D N k ε
    set op := opNorm A
    have hop0 : 0 ≤ op := Bd_opNorm_nonneg A
    have hhs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
    have hLz : op = 0 → e.Lt = 0 := fun h0 => FB_eq_zero _ (hLt.trans (by rw [h0, mul_zero]))
    set lp := P.map (FE_hat e ι op m) with hlp
    set lq := Q.map (FE_hat e ι op m) with hlq
    have hpr : PS_nr lp = P.countP FO_isRes := FE_hat_nr e ι op m P
    have hqr : PS_nr lq = Q.countP FO_isRes := FE_hat_nr e ι op m Q
    have hpl : lp.length = P.length := by simp [hlp]
    have hql : lq.length = Q.length := by simp [hlq]
    obtain ⟨hpgr, -, hpgl, -, hpgd, -⟩ :=
      PS_gram_facts lp K (FE_hat_det e ι op m K hK hm hop0 hM hP hLt P)
    obtain ⟨-, hqgr', -, hqgl', -, hqgd'⟩ :=
      PS_gram_facts lq K (FE_hat_det e ι op m K hK hm hop0 hM hP hLt Q)
    have hev := hN₂ N (le_of_max_le_left hN) μ hμ e hadm _ _ (by rw [hqgr', hqr])
      (by rw [hpgr, hpr]) (by rw [hqgl', hql]; omega) (by rw [hpgl, hpl]; omega) hqgd' hpgd
    refine ⟨_, hev.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh => ?_⟩
    · have hN1' : 1 ≤ N := le_trans (le_max_right _ _) hN
      have := FE_pow_le N hN1' D' 1 1 zero_le_one (by simpa using (by exact_mod_cast hN1' :
        (1 : ℝ) ≤ N))
      simpa using this
    simp only [Set.mem_ofPred_eq, not_lt] at hh
    rw [(PS_v_gram _ lq).2, (PS_v_gram _ lp).1] at hh
    set Xp := PS_v (PS_Gr e h) lp
    set Xq := PS_v (PS_Gr e h) lq
    have hU : (u.map (FLet.mat e ι h)).prod =
        (((op ^ (u.countP (· == .lamt) - 1) * m ^ u.countP FE_isPr : ℝ)) : ℂ) •
          (Xp * e.Lt * Xq) := by
      rw [hPQ, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
        FE_prod_hat e ι op m hm.ne' hLz h P, FE_prod_hat e ι op m hm.ne' hLz h Q, FE_sc_prod,
        FE_sc_prod]
      have e1 : (P ++ FLet.lamt :: Q).countP (· == .lamt) - 1 =
          P.countP (· == .lamt) + Q.countP (· == .lamt) := by
        rw [← hPQ, hcl]; omega
      rw [e1, ← hPQ, hcp, pow_add, pow_add]
      simp only [FLet.mat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
        Matrix.mul_assoc]
      congr 2
      ring
    rw [hU, FE_hs_smul, abs_of_nonneg (by positivity)]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
    have hN0 : (0 : ℝ) < N := by linarith
    have hb2 := PS_bnd hη heta hK him (2 * r)
    have hψ2 := PS_psi_nonneg hη hm.le (2 * r)
    have hom : FE_om η m r ^ 2 = pkgPsi η m (2 * r) := by
      unfold FE_om
      rw [ite_eq_left hr, Real.sq_sqrt hψ2]
    have hom0 := FE_om_nonneg η m r
    have e2 : 2 * Q.countP FO_isRes + 2 * P.countP FO_isRes = 2 * r := by omega
    rw [e2] at hh
    have h1 := PS_rows_lt2 e Xp Xq
    rw [← FE_hs_sq, ← PS_card] at h1
    rw [PS_card] at h1
    have hlam : hsNorm (lam D N e.A) ^ 2 ≤ (K * hsNorm A) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hslam 2
    have hPb := PS_b_nonneg hadm (2 * r)
    have h2 : hsNorm (Xp * e.Lt * Xq) ^ 2 ≤
        (N : ℝ) ^ τ * ((D * (Cm * K ^ 3)) * (FE_om η m r * hsNorm A) ^ 2) := by
      refine h1.trans ?_
      have hD0 : (0 : ℝ) ≤ D * N := by positivity
      calc (D : ℝ) * N * ‖ntr (Xq * Xqᴴ * e.Lt * (Xpᴴ * Xp) * e.Lt)‖
          ≤ D * N * ((N : ℝ) ^ τ * (Cm * (hsNorm (lam D N e.A) ^ 2 / N * PS_b e (2 * r)))) :=
            mul_le_mul_of_nonneg_left hh hD0
        _ ≤ D * N * ((N : ℝ) ^ τ * (Cm * ((K * hsNorm A) ^ 2 / N * (K * pkgPsi η m (2 * r))))) := by
            gcongr
        _ = (N : ℝ) ^ τ * ((D * (Cm * K ^ 3)) * (FE_om η m r * hsNorm A) ^ 2) := by
            rw [mul_pow (FE_om η m r), hom]
            field_simp
    have h3 := (Real.sqrt_le_sqrt h2).trans (FE_sqrt_le _ _ _ hNτ (by positivity)
      (mul_nonneg hom0 hhs0))
    have hX0 : 0 ≤ hsNorm (Xp * e.Lt * Xq) := Real.sqrt_nonneg _
    rw [Real.sqrt_sq hX0] at h3
    have hn' : u.countP (· == .lamt) ≠ 0 := by omega
    unfold FE_half
    simp only [↓reduceIte, hn']
    have hc0 : 0 ≤ op ^ (u.countP (· == .lamt) - 1) * m ^ u.countP FE_isPr := by positivity
    calc op ^ (u.countP (· == .lamt) - 1) * m ^ u.countP FE_isPr * hsNorm (Xp * e.Lt * Xq)
        ≤ op ^ (u.countP (· == .lamt) - 1) * m ^ u.countP FE_isPr * ((N : ℝ) ^ τ *
          (Real.sqrt (D * (Cm * K ^ 3)) * (FE_om η m r * hsNorm A))) :=
          mul_le_mul_of_nonneg_left h3 hc0
      _ = _ := by ring

private lemma FE_hs_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι] (B Z : Matrix ι ι ℂ) :
    hsNorm (B * Z) ≤ opNorm B * hsNorm Z := by
  have h := MultiRes_hs2_mul_left_le B Z
  rw [← MultiRes_hsNorm_sq, ← MultiRes_hsNorm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Bd_opNorm_nonneg B) (Real.sqrt_nonneg _)) two_ne_zero).1 h

private lemma FE_hs_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι] (Z B : Matrix ι ι ℂ) :
    hsNorm (Z * B) ≤ hsNorm Z * opNorm B := by
  have h := MultiRes_hs2_mul_right_le Z B
  rw [← MultiRes_hsNorm_sq, ← MultiRes_hsNorm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Bd_opNorm_nonneg B)) two_ne_zero).1 h

/-- The word `P Λ̃ Q` with `Λ̃` kept and the other letters scaled by `FE_hat`. -/
private lemma FE_split_prod {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (op m : ℝ) (hm : m ≠ 0) (hL : op = 0 → e.Lt = 0) (h : Idx D N → Idx D N → ℂ)
    (P Q : List FLet) :
    ((P ++ FLet.lamt :: Q).map (FLet.mat e ι h)).prod =
      ((op ^ (P.countP (· == .lamt) + Q.countP (· == .lamt)) *
        m ^ (P.countP FE_isPr + Q.countP FE_isPr) : ℝ) : ℂ) •
        (PS_v (PS_Gr e h) (P.map (FE_hat e ι op m)) * e.Lt *
          PS_v (PS_Gr e h) (Q.map (FE_hat e ι op m))) := by
  rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    FE_prod_hat e ι op m hm hL h P, FE_prod_hat e ι op m hm hL h Q, FE_sc_prod, FE_sc_prod,
    pow_add, pow_add]
  simp only [FLet.mat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
    Matrix.mul_assoc]
  congr 2
  ring

private lemma FE_split_counts (P Q : List FLet) :
    (P ++ FLet.lamt :: Q).countP (· == .lamt) =
      P.countP (· == .lamt) + Q.countP (· == .lamt) + 1 ∧
    (P ++ FLet.lamt :: Q).countP FE_isPr = P.countP FE_isPr + Q.countP FE_isPr ∧
    (P ++ FLet.lamt :: Q).countP FO_isRes = P.countP FO_isRes + Q.countP FO_isRes := by
  simp only [List.countP_append, List.countP_cons]
  refine ⟨by simp; ring, by simp [FE_isPr], by simp [FO_isRes]⟩

private lemma FE_psi_zero (η m : ℝ) : pkgPsi η m 0 = 1 := by simp [pkgPsi]

private lemma FE_om_zero (η m : ℝ) : FE_om η m 0 = 1 := by simp [FE_om]

/-- The bounds of a word without resolvent: a product of bounded deterministic letters. -/
private lemma FE_word_det (D : ℕ) (δA ε c₀ K : ℝ) (hK : 1 ≤ K) (u : List FLet)
    (hr : u.countP FO_isRes = 0) (τ : ℝ) (hτ : 0 < τ) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ N : ℕ, ∀ (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (e : LoopEnv D N),
      FE_Slot D N δA ε c₀ K A k e →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D) (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ))
        (h : Idx D N → Idx D N → ℂ),
        FE_WV ((u.map (FLet.mat e ι h)).prod) V
          (Cst * (N : ℝ) ^ τ * (pkgPsi (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
            (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr)))
          (Cst * (N : ℝ) ^ τ * (FE_om (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
            (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr))) ∧
        hsNorm ((u.map (FLet.mat e ι h)).prod) ≤ Cst * (N : ℝ) ^ τ *
          (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A) (u.countP (· == .lamt))
            (u.countP FO_isRes) true * FE_M D N k ε ^ u.countP FE_isPr) := by
  have hK0 : 0 ≤ K := by linarith
  set L := u.length with hL
  refine ⟨K ^ L * (Real.sqrt D + 1), by positivity, fun N A k e hS nb ι V h => ?_⟩
  obtain ⟨-, -, hN1, -, -, hη, hm, -, hM, hP, hLt, hsLt, -, -, -, -⟩ := hS
  set η := etaK D N k ε
  set m := FE_M D N k ε
  set op := opNorm A
  have hop0 : 0 ≤ op := Bd_opNorm_nonneg A
  have hhs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  have hLz : op = 0 → e.Lt = 0 := fun h0 => FB_eq_zero _ (hLt.trans (by rw [h0, mul_zero]))
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
  have hKL : 0 ≤ K ^ L := by positivity
  have hC1 : K ^ L ≤ K ^ L * (Real.sqrt D + 1) * (N : ℝ) ^ τ := by
    have : K ^ L ≤ K ^ L * (Real.sqrt D + 1) := by nlinarith [Real.sqrt_nonneg (D : ℝ)]
    nlinarith
  have hC2 : K ^ L * Real.sqrt D ≤ K ^ L * (Real.sqrt D + 1) * (N : ℝ) ^ τ := by
    have : K ^ L * Real.sqrt D ≤ K ^ L * (Real.sqrt D + 1) := by nlinarith
    nlinarith [mul_nonneg hKL (Real.sqrt_nonneg (D : ℝ))]
  set l := u.map (FE_hat e ι op m) with hl
  have hlr : PS_nr l = 0 := by rw [FE_hat_nr, hr]
  have hll : l.length = L := by simp [hl, hL]
  have hld := FE_hat_det e ι op m K hK hm hop0 hM hP hLt u
  set X := PS_v (PS_Gr e h) l
  have hX : opNorm X ≤ K ^ L := hll ▸ FE_det_norm _ K hK l hlr hld
  have hsc' : (u.map (FE_sc op m)).prod = op ^ u.countP (· == .lamt) * m ^ u.countP FE_isPr :=
    FE_sc_prod op m u
  have hsc0 : 0 ≤ op ^ u.countP (· == .lamt) * m ^ u.countP FE_isPr := by positivity
  rw [hr, FE_psi_zero, FE_om_zero, one_mul]
  refine ⟨?_, ?_⟩
  · have hWV : FE_WV X V (K ^ L) (K ^ L) := by
      refine ⟨fun j => (FE_dot_le X _ _).trans ?_, fun j => (MultiRes_vn_mulVec_le _ _).trans ?_,
        fun j => (MultiRes_vn_mulVec_le _ _).trans ?_⟩
      · have := MultiRes_vn_nonneg (V j).1
        have := MultiRes_vn_nonneg (V j).2
        gcongr
      · rw [Bd_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right hX (MultiRes_vn_nonneg _)
      · exact mul_le_mul_of_nonneg_right hX (MultiRes_vn_nonneg _)
    rw [FE_prod_hat e ι op m hm.ne' hLz h u, hsc']
    refine FE_WV_mono _ V _ _ _ _ ?_ ?_ (FE_WV_smul _ V _ _ _ hsc0 hWV) <;>
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hC1 hsc0
  · rcases Nat.eq_zero_or_pos (u.countP (· == .lamt)) with hn | hn
    · rw [FE_prod_hat e ι op m hm.ne' hLz h u, hsc', FE_hs_smul, abs_of_nonneg hsc0]
      unfold FE_half
      simp only [↓reduceIte, hn, pow_zero, one_mul, FE_om_zero]
      have h1 := FE_hs_le_op X
      rw [PS_card, Real.sqrt_mul (Nat.cast_nonneg _)] at h1
      have h2 : hsNorm X ≤ K ^ L * Real.sqrt D * Real.sqrt N := by
        refine h1.trans ?_
        have := mul_le_mul_of_nonneg_left hX
          (mul_nonneg (Real.sqrt_nonneg (D : ℝ)) (Real.sqrt_nonneg (N : ℝ)))
        nlinarith
      have hm0 : 0 ≤ m ^ u.countP FE_isPr := by positivity
      calc m ^ u.countP FE_isPr * hsNorm X ≤ m ^ u.countP FE_isPr *
            (K ^ L * Real.sqrt D * Real.sqrt N) := mul_le_mul_of_nonneg_left h2 hm0
        _ ≤ m ^ u.countP FE_isPr * (K ^ L * (Real.sqrt D + 1) * (N : ℝ) ^ τ * Real.sqrt N) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)) hm0
        _ = _ := by ring
    · obtain ⟨P, Q, hPQ⟩ : ∃ P Q : List FLet, u = P ++ FLet.lamt :: Q := by
        obtain ⟨z, hz, hz'⟩ := List.countP_pos_iff.1 hn
        have : z = FLet.lamt := by simpa using hz'
        exact List.append_of_mem (this ▸ hz)
      obtain ⟨hcl, hcp, hcr⟩ := FE_split_counts P Q
      have hPr : P.countP FO_isRes = 0 := by rw [← hPQ] at hcr; omega
      have hQr : Q.countP FO_isRes = 0 := by rw [← hPQ] at hcr; omega
      have hLPQ : P.length + Q.length + 1 = L := by rw [hL, hPQ]; simp; ring
      have hXP := FE_det_norm (PS_Gr e h) K hK _ (by rw [FE_hat_nr, hPr])
        (FE_hat_det e ι op m K hK hm hop0 hM hP hLt P)
      have hXQ := FE_det_norm (PS_Gr e h) K hK _ (by rw [FE_hat_nr, hQr])
        (FE_hat_det e ι op m K hK hm hop0 hM hP hLt Q)
      simp only [List.length_map] at hXP hXQ
      have hsc1 : 0 ≤ op ^ (P.countP (· == .lamt) + Q.countP (· == .lamt)) *
          m ^ (P.countP FE_isPr + Q.countP FE_isPr) := by positivity
      rw [hPQ, FE_split_prod e ι op m hm.ne' hLz h P Q, FE_hs_smul, abs_of_nonneg hsc1, hcp, hcl]
      unfold FE_half
      simp only [↓reduceIte, Nat.add_one_ne_zero, FE_om_zero, one_mul, Nat.add_sub_cancel]
      set Xp := PS_v (PS_Gr e h) (P.map (FE_hat e ι op m))
      set Xq := PS_v (PS_Gr e h) (Q.map (FE_hat e ι op m))
      have h2 : hsNorm (Xp * e.Lt * Xq) ≤ K ^ L * hsNorm A := by
        rw [Matrix.mul_assoc]
        refine (FE_hs_mul_left _ _).trans ?_
        have h3 := FE_hs_mul_right e.Lt Xq
        have h4 : hsNorm (e.Lt * Xq) ≤ K * hsNorm A * K ^ Q.length :=
          h3.trans (mul_le_mul hsLt hXQ (Bd_opNorm_nonneg _) (by positivity))
        calc opNorm Xp * hsNorm (e.Lt * Xq) ≤ K ^ P.length * (K * hsNorm A * K ^ Q.length) :=
              mul_le_mul hXP h4 (Real.sqrt_nonneg _) (by positivity)
          _ = K ^ (P.length + Q.length + 1) * hsNorm A := by ring
          _ = K ^ L * hsNorm A := by rw [hLPQ]
      calc op ^ (P.countP (· == .lamt) + Q.countP (· == .lamt)) *
            m ^ (P.countP FE_isPr + Q.countP FE_isPr) * hsNorm (Xp * e.Lt * Xq)
          ≤ op ^ (P.countP (· == .lamt) + Q.countP (· == .lamt)) *
            m ^ (P.countP FE_isPr + Q.countP FE_isPr) * (K ^ L * hsNorm A) :=
            mul_le_mul_of_nonneg_left h2 hsc1
        _ ≤ op ^ (P.countP (· == .lamt) + Q.countP (· == .lamt)) *
            m ^ (P.countP FE_isPr + Q.countP FE_isPr) *
            (K ^ L * (Real.sqrt D + 1) * (N : ℝ) ^ τ * hsNorm A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC1 hhs0) hsc1
        _ = _ := by ring

/-- The bounds of one word, off one event: isotropic (A.53) [entprodG] between the vectors of a
family, the Ward bounds of `U^* v` and `U v`, and the Hilbert–Schmidt norm. -/
private lemma FE_word (D : ℕ) (hD : 2 ≤ D) (δA ε c₀ K : ℝ) (hδA : 0 < δA) (hε : 0 < ε)
    (hc₀ : 0 < c₀) (hK : 1 ≤ K) (C : ℕ → ℝ) (u : List FLet) (τ : ℝ) (hτ : 0 < τ)
    (D' : ℝ) (hD' : 0 < D') :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (e : LoopEnv D N), FE_Slot D N δA ε c₀ K A k e →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D) (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)),
      ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h ∉ bad, FE_WV ((u.map (FLet.mat e ι h)).prod) V
          (Cst * (N : ℝ) ^ τ * (pkgPsi (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
            (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr)))
          (Cst * (N : ℝ) ^ τ * (FE_om (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
            (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr))) ∧
        hsNorm ((u.map (FLet.mat e ι h)).prod) ≤ Cst * (N : ℝ) ^ τ *
          (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A) (u.countP (· == .lamt))
            (u.countP FO_isRes) true * FE_M D N k ε ^ u.countP FE_isPr) := by
  by_cases hr : u.countP FO_isRes = 0
  · obtain ⟨Cst, hC, hdet⟩ := FE_word_det D δA ε c₀ K hK u hr τ hτ
    exact ⟨Cst, hC, 0, fun N _ μ _ A k e hS nb ι V =>
      ⟨∅, by simp, fun h _ => hdet N A k e hS nb ι V h⟩⟩
  have hr1 : 1 ≤ u.countP FO_isRes := by omega
  obtain ⟨C₁, hC₁, N₁, hN₁⟩ := FE_vecs D hD δA ε c₀ K hδA hε hc₀ hK C u hr1 τ hτ (D' + 1)
    (by positivity)
  obtain ⟨C₂, hC₂, N₂, hN₂⟩ := FE_hs D hD δA ε c₀ K hδA hε hc₀ hK C u hr1 τ hτ (D' + 1)
    (by positivity)
  refine ⟨C₁ + C₂, by positivity, max (max N₁ N₂) 2, fun N hN μ hμ A k e hS nb ι V => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hδ : (0 : ℝ) ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨bad, hbad, hgood⟩ := FE_union μ hδ hδ (hN₁ N hN1 μ hμ A k e hS nb ι V)
    (hN₂ N hN2 μ hμ A k e hS nb ι)
  refine ⟨bad, hbad.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh => ?_⟩
  · have := FE_pow_le N (by omega) D' 2 1 (by norm_num) (by
      simpa using (by exact_mod_cast hN3 : (2 : ℝ) ≤ N))
    push_cast at this
    linarith
  obtain ⟨hv, hs⟩ := hgood h hh
  obtain ⟨-, -, -, -, -, hη, hm, -, -, -, -, -, -, -, -, -⟩ := hS
  have hNτ : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hop0 := Bd_opNorm_nonneg A
  have hs1 : 0 ≤ opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr := by
    positivity
  have hC : C₁ * (N : ℝ) ^ τ ≤ (C₁ + C₂) * (N : ℝ) ^ τ :=
    mul_le_mul_of_nonneg_right (by linarith) hNτ
  have hC' : C₂ * (N : ℝ) ^ τ ≤ (C₁ + C₂) * (N : ℝ) ^ τ :=
    mul_le_mul_of_nonneg_right (by linarith) hNτ
  refine ⟨FE_WV_mono _ V _ _ _ _ ?_ ?_ hv, hs.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hC
      (mul_nonneg (PS_psi_nonneg hη hm.le (u.countP FO_isRes)) hs1)
  · exact mul_le_mul_of_nonneg_right hC
      (mul_nonneg (FE_om_nonneg (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes)) hs1)
  · refine mul_le_mul_of_nonneg_right hC' (mul_nonneg ?_ (by positivity))
    exact FE_half_nonneg N (Real.sqrt_nonneg _) hop0 _ _ true

/-! ### The words between the letters `Λ̃` -/

private lemma FE_parts_app (P Q : List FLet) :
    FLet.parts (P ++ FLet.lamt :: Q) = FLet.parts P ++ FLet.parts Q := by
  unfold FLet.parts
  rw [List.splitOnP_append_cons P Q (by rfl), List.map_append]

private lemma FE_parts_free (P : List FLet) (hP : P.countP (· == .lamt) = 0) :
    FLet.parts P = [P.countP FO_isRes] := by
  unfold FLet.parts
  rw [List.splitOnP_eq_singleton fun z hz => by simpa using List.countP_eq_zero.1 hP z hz]
  rfl

/-- The first `Λ̃` of a word. -/
private lemma FE_first (w : List FLet) (h : 1 ≤ w.countP (· == .lamt)) :
    ∃ P Q : List FLet, w = P ++ FLet.lamt :: Q ∧ P.countP (· == .lamt) = 0 := by
  induction w with
  | nil => simp at h
  | cons z w ih =>
    by_cases hz : z = FLet.lamt
    · exact ⟨[], w, by simp [hz], rfl⟩
    · have hz' : (z == FLet.lamt) = false := by simpa using hz
      rw [List.countP_cons, hz'] at h
      obtain ⟨P, Q, rfl, hP⟩ := ih (by simpa using h)
      exact ⟨z :: P, Q, rfl, by rw [List.countP_cons, hz', hP]; rfl⟩

/-- The `(k+1)`-th `Λ̃` of a word. -/
private lemma FE_split_at : ∀ (k : ℕ) (w : List FLet), k < w.countP (· == .lamt) →
    ∃ P Q : List FLet, w = P ++ FLet.lamt :: Q ∧ P.countP (· == .lamt) = k
  | 0, w, h => by
    obtain ⟨P, Q, hw, hP⟩ := FE_first w (by omega)
    exact ⟨P, Q, hw, hP⟩
  | k + 1, w, h => by
    obtain ⟨P₀, Q₀, rfl, hP₀⟩ := FE_first w (by omega)
    obtain ⟨hc, -, -⟩ := FE_split_counts P₀ Q₀
    obtain ⟨P₁, Q₁, rfl, hP₁⟩ := FE_split_at k Q₀ (by omega)
    refine ⟨P₀ ++ FLet.lamt :: P₁, Q₁, by simp, ?_⟩
    rw [(FE_split_counts P₀ P₁).1, hP₀, hP₁]
    ring

private lemma FE_parts_len_sum : ∀ (n : ℕ) (w : List FLet), w.countP (· == .lamt) = n →
    (FLet.parts w).length = n + 1 ∧ (FLet.parts w).sum = w.countP FO_isRes
  | 0, w, h => by rw [FE_parts_free w h]; simp
  | n + 1, w, h => by
    obtain ⟨P, Q, rfl, hP⟩ := FE_first w (by omega)
    obtain ⟨hc, -, hr⟩ := FE_split_counts P Q
    obtain ⟨h1, h2⟩ := FE_parts_len_sum n Q (by omega)
    rw [FE_parts_app, FE_parts_free P hP, hr]
    simp only [List.length_append, List.length_singleton, List.sum_append, List.sum_singleton]
    exact ⟨by omega, by rw [h2]⟩

private lemma FE_parts_len (w : List FLet) :
    (FLet.parts w).length = w.countP (· == .lamt) + 1 :=
  (FE_parts_len_sum _ w rfl).1

private lemma FE_parts_sum (w : List FLet) : (FLet.parts w).sum = w.countP FO_isRes :=
  (FE_parts_len_sum _ w rfl).2

/-! ### The values of the monomials -/

section Mono

variable (N : ℕ) (M η hs op : ℝ)

private lemma FE_ev_ext (p : ℕ) :
    (⟨0, 2 * (p : ℤ), 0, 0, 0⟩ : FMono).evalR N M η hs op = M ^ p := by
  simp only [FMono.evalR]
  push_cast
  rw [show (2 * (p : ℝ)) / 2 = (p : ℝ) by ring, Real.rpow_natCast]
  simp

private lemma FE_ev_op (n : ℕ) : (⟨0, 0, 0, 0, n⟩ : FMono).evalR N M η hs op = op ^ n := by
  simp [FMono.evalR]

private lemma FE_ev_hsop (d n : ℕ) :
    (⟨0, 0, 0, d, n⟩ : FMono).evalR N M η hs op = hs ^ d * op ^ n := by
  simp [FMono.evalR]

private lemma FE_ev_om (_hM : 0 ≤ M) (hη : 0 < η) (r : ℕ) :
    (FMono.omega r).evalR N M η hs op = FE_om η M r := by
  unfold FMono.omega FE_om
  split_ifs with h
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have h2 : 2 ≤ 2 * (s + 1) := by omega
    simp only [FMono.evalR, pkgPsi, ite_eq_left h2, show 2 * (s + 1) - 1 = 2 * s + 1 by omega]
    have hc : (-(((2 * ((s + 1 : ℕ) : ℤ) - 1 : ℤ)) : ℝ) / 2) =
        -(((2 * s + 1 : ℕ) : ℝ) * (1 / 2)) := by
      push_cast; ring
    rw [hc, Real.rpow_neg hη.le, Real.sqrt_div' _ (pow_nonneg hη.le _), Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast η (2 * s + 1), ← Real.rpow_mul hη.le]
    simp only [Int.cast_zero, Int.cast_one, pow_zero, mul_one, div_eq_mul_inv, zero_mul,
      Real.rpow_zero, one_mul]
  · simp [FMono.evalR]

private lemma FE_ev_half (hM : 0 < M) (hη : 0 < η) (hN : 1 ≤ N) (n r : ℕ) (l2 : Bool) :
    (fhalf n r l2).evalR N M η hs op = FE_half N η M hs op n r l2 := by
  unfold fhalf FE_half
  cases l2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FE_ev_om N M η hs op hM.le hη, FE_ev_op]
  · split_ifs
    · rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FE_ev_om N M η hs op hM.le hη]
      simp [FMono.evalR, Real.sqrt_eq_rpow]
    · rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FE_ev_om N M η hs op hM.le hη, FE_ev_hsop]
      ring

end Mono

/-! ### Bounds at the slots off one event -/

/-- A bound `Q c`, `c = Cst N^τ`, at the slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law], off an
event of probability `≤ N^{-D'}`, for every `τ, D' > 0` and `N` large. -/
private def FE_OK (D : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ) (nb : ℕ)
    (Q : (N : ℕ) → Matrix (Fin N) (Fin N) ℂ → ℕ → LoopEnv D N → (Fin nb → Fin D) →
      (Idx D N → Idx D N → ℂ) → ℝ → Prop) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' → ∃ Cst : ℝ, 0 ≤ Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
    hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
    ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
        ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
    ∀ ι : Fin nb → Fin D, ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧ ∀ h ∉ bad, Q N A k e ι h (Cst * (N : ℝ) ^ τ)

/-- The constant of a bound off one event is absorbed by `N^{τ'/2}` for `N` large. -/
private lemma FE_absorb {D : ℕ} {δA εA ε : ℝ} {C : ℕ → ℝ} {nb : ℕ}
    (F : (N : ℕ) → Matrix (Fin N) (Fin N) ℂ → ℕ → LoopEnv D N → (Fin nb → Fin D) →
      (Idx D N → Idx D N → ℂ) → ℝ)
    (S : (N : ℕ) → Matrix (Fin N) (Fin N) ℂ → ℕ → ℝ)
    (hS : ∀ N A k, 0 ≤ S N A k)
    (h : FE_OK D δA εA ε C nb fun N A k e ι h c => F N A k e ι h ≤ c * S N A k) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ ι : Fin nb → Fin D,
        μ {h | (N : ℝ) ^ τ' * S N A k < F N A k e ι h} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨Cst, -, N₁, hN₁⟩ := h (τ' / 2) (by positivity) D' hD'
  have hev : ∀ᶠ N : ℕ in atTop, Cst ≤ (N : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ' / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop Cst
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max N₁ N₂) 1, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨bad, hbad, hb⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    μ hμ A hA k hk hkN hhs e he ι
  refine le_trans (measure_mono fun h hh => ?_) hbad
  by_contra hnot
  have h1 := hb h hnot
  have hC := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  simp only [Set.mem_ofPred_eq] at hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hsplit : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hN2 : 0 ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [hsplit] at hh
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN2) (hS N A k)
  linarith

/-! ### The bounds of up to three words -/

/-- The bounds of `FE_word` for the word `u` with matrix `U`, with constant `B`. -/
private def FE_WF {D N : ℕ} (k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (u : List FLet)
    (U : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (B : ℝ) : Prop :=
  FE_WV U V
    (B * (pkgPsi (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
      (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr)))
    (B * (FE_om (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
      (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr))) ∧
  hsNorm U ≤ B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
    (u.countP (· == .lamt)) (u.countP FO_isRes) true * FE_M D N k ε ^ u.countP FE_isPr)

private lemma FE_WF_mono {D N : ℕ} (k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (u : List FLet) (U : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (B B' : ℝ) (hB : B ≤ B')
    (hη : 0 < etaK D N k ε) (hm : 0 < FE_M D N k ε) (h : FE_WF k ε A u U V B) :
    FE_WF k ε A u U V B' := by
  obtain ⟨hv, hs⟩ := h
  have hop0 := Bd_opNorm_nonneg A
  have hs1 : 0 ≤ opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr := by
    positivity
  refine ⟨FE_WV_mono _ V _ _ _ _ ?_ ?_ hv, hs.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hB
      (mul_nonneg (PS_psi_nonneg hη hm.le (u.countP FO_isRes)) hs1)
  · exact mul_le_mul_of_nonneg_right hB
      (mul_nonneg (FE_om_nonneg (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes)) hs1)
  · refine mul_le_mul_of_nonneg_right hB (mul_nonneg ?_ (by positivity))
    exact FE_half_nonneg N (Real.sqrt_nonneg _) hop0 _ _ true

/-- The bounds of three words off one event, at the slots. -/
private lemma FE_words3 (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ)
    (u₁ u₂ u₃ : List FLet) (τ : ℝ) (hτ : 0 < τ) (D' : ℝ) (hD' : 0 < D') :
    ∃ c₀ K : ℝ, ∃ Cst : ℝ, 0 ≤ Cst ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      FE_Slot D N δA ε c₀ K A k e ∧
      ∀ (ι : Fin nb → Fin D) (V₁ V₂ V₃ : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)),
      ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h ∉ bad, FE_WF k ε A u₁ ((u₁.map (FLet.mat e ι h)).prod) V₁ (Cst * (N : ℝ) ^ τ) ∧
          FE_WF k ε A u₂ ((u₂.map (FLet.mat e ι h)).prod) V₂ (Cst * (N : ℝ) ^ τ) ∧
          FE_WF k ε A u₃ ((u₃.map (FLet.mat e ι h)).prod) V₃ (Cst * (N : ℝ) ^ τ) := by
  obtain ⟨c₀, K, hc₀, hK, N₁, hslot⟩ := FE_slot D hD δA εA ε hδA hεA hε hε' hε'' C
  obtain ⟨C₁, hC₁, M₁, hM₁⟩ := FE_word D hD δA ε c₀ K hδA hε hc₀ hK C u₁ τ hτ (D' + 1)
    (by positivity)
  obtain ⟨C₂, hC₂, M₂, hM₂⟩ := FE_word D hD δA ε c₀ K hδA hε hc₀ hK C u₂ τ hτ (D' + 1)
    (by positivity)
  obtain ⟨C₃, hC₃, M₃, hM₃⟩ := FE_word D hD δA ε c₀ K hδA hε hc₀ hK C u₃ τ hτ (D' + 1)
    (by positivity)
  refine ⟨c₀, K, C₁ + C₂ + C₃, by positivity, max (max N₁ (max M₁ M₂)) (max M₃ 3),
    fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  have h1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have h2 : M₁ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hN
  have h3 : M₂ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hN
  have h4 : M₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h5 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hS := hslot N h1 μ hμ A hA k hk hkN hhs e he
  refine ⟨hS, fun ι V₁ V₂ V₃ => ?_⟩
  have hδ : (0 : ℝ) ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨bad, hbad, hg⟩ := FE_union μ (by positivity) hδ
    (FE_union μ hδ hδ (hM₁ N h2 μ hμ A k e hS nb ι V₁) (hM₂ N h3 μ hμ A k e hS nb ι V₂))
    (hM₃ N h4 μ hμ A k e hS nb ι V₃)
  refine ⟨bad, hbad.trans (ENNReal.ofReal_le_ofReal ?_), fun h hh => ?_⟩
  · have := FE_pow_le N (by omega) D' 3 1 (by norm_num) (by
      simpa using (by exact_mod_cast h5 : (3 : ℝ) ≤ N))
    push_cast at this
    linarith
  obtain ⟨⟨g1, g2⟩, g3⟩ := hg h hh
  obtain ⟨-, -, -, -, -, hη, hm, -⟩ := hS
  have hNτ : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨FE_WF_mono k ε A u₁ _ V₁ _ _ ?_ hη hm g1, FE_WF_mono k ε A u₂ _ V₂ _ _ ?_ hη hm g2,
    FE_WF_mono k ε A u₃ _ V₃ _ _ ?_ hη hm g3⟩ <;>
  · refine mul_le_mul_of_nonneg_right ?_ hNτ
    linarith

/-! ### The norm of an entry under an option -/

/-- The modulus of an entry at the labels `x', y'`, set to `0` across blocks when the labels
`x, y` lie in one block. -/
private def FE_f {D N : ℕ} (x y : ℕ) (W : Matrix (Idx D N) (Idx D N) ℂ) (x' y' : Idx D N) : ℝ :=
  if fsameBlk x y = true ∧ x'.1 ≠ y'.1 then 0 else ‖W x' y'‖

private lemma FE_f_nonneg {D N : ℕ} (x y : ℕ) (W : Matrix (Idx D N) (Idx D N) ℂ)
    (x' y' : Idx D N) : 0 ≤ FE_f x y W x' y' := by
  unfold FE_f
  split_ifs
  · exact le_rfl
  · exact norm_nonneg _

private lemma FE_f_le {D N : ℕ} (x y : ℕ) (W : Matrix (Idx D N) (Idx D N) ℂ) (x' y' : Idx D N) :
    FE_f x y W x' y' ≤ ‖W x' y'‖ := by
  unfold FE_f
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

/-- A bound `f(x, y) ≤ a(x) b(y)` with the norms of `a`, `b` at the uses `cx`, `cy`. -/
private def FE_PC {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (cx cy : ℕ) (B : ℝ) : Prop :=
  ∃ a b : ι → ℝ, (∀ x, 0 ≤ a x) ∧ (∀ y, 0 ≤ b y) ∧ (∀ x y, f x y ≤ a x * b y) ∧
    FE_nrm (cx == 1) a * FE_nrm (cy == 1) b ≤ B

/-- A bound `(Σ_x f(x, y)²)^{1/2} ≤ b(y)` with the norm of `b` at the use `cy`. -/
private def FE_CC {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (cy : ℕ) (B : ℝ) : Prop :=
  ∃ b : ι → ℝ, (∀ y, 0 ≤ b y) ∧ (∀ y, Real.sqrt (∑ x, f x y ^ 2) ≤ b y) ∧
    FE_nrm (cy == 1) b ≤ B

/-- A bound `(Σ_y f(x, y)²)^{1/2} ≤ a(x)` with the norm of `a` at the use `cx`. -/
private def FE_RC {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (cx : ℕ) (B : ℝ) : Prop :=
  ∃ a : ι → ℝ, (∀ x, 0 ≤ a x) ∧ (∀ x, Real.sqrt (∑ y, f x y ^ 2) ≤ a x) ∧
    FE_nrm (cx == 1) a ≤ B

section Conv

variable {ι : Type*} [Fintype ι]

private lemma FE_PC_opt (o : FOpt) (rf : Bool) (f : ι → ι → ℝ) (B : ℝ) (hf : ∀ x y, 0 ≤ f x y)
    (h : FE_PC f o.cx o.cy B) : foptNorm false o rf f ≤ B := by
  obtain ⟨a, b, ha, hb, hab, hB⟩ := h
  exact (FE_opt_prod o rf f a b ha hb hf hab).trans hB

private lemma FE_PC_diag (cx cy : ℕ) (hcx : cx ≤ 1) (hcy : cy ≤ 1) (v : List FMono) (rf : Bool)
    (f : ι → ι → ℝ) (B : ℝ) (hf : ∀ x y, 0 ≤ f x y) (h : FE_PC f cx cy B) :
    foptNorm true ⟨cx + cy, 0, 0, v⟩ rf f ≤ B := by
  obtain ⟨a, b, ha, hb, hab, hB⟩ := h
  exact (FE_opt_diag cx cy hcx hcy v rf f a b ha hb hf hab).trans hB

private lemma FE_CC_opt (o : FOpt) (hcx : o.cx = 1) (f : ι → ι → ℝ) (B : ℝ)
    (h : FE_CC f o.cy B) : foptNorm false o true f ≤ B := by
  obtain ⟨b, hb, hfb, hB⟩ := h
  exact (FE_opt_col o hcx f b hb hfb).trans hB

private lemma FE_RC_opt (o : FOpt) (hcy : o.cy = 1) (f : ι → ι → ℝ) (B : ℝ)
    (h : FE_RC f o.cx B) : foptNorm false o false f ≤ B := by
  obtain ⟨a, ha, hfa, hB⟩ := h
  exact (FE_opt_row o hcy f a ha hfa).trans hB

private lemma FE_nrm_const (m : Bool) (c : ℝ) (hc : 0 ≤ c) (hm : m = false) :
    FE_nrm m (fun _ : ι => c) ≤ c := by
  subst hm
  exact Real.iSup_le (fun _ => le_rfl) hc

end Conv

section Ent

variable {D N : ℕ}

private lemma FE_vn_row (X : Matrix (Idx D N) (Idx D N) ℂ) (x : Idx D N) :
    MultiRes_vn (Xᴴ *ᵥ Pi.single x 1) = Real.sqrt (∑ k, ‖X x k‖ ^ 2) := by
  rw [← Real.sqrt_sq (MultiRes_vn_nonneg _), MultiRes_vn_sq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_single_one]
  simp [Matrix.conjTranspose_apply]

private lemma FE_vn_col (X : Matrix (Idx D N) (Idx D N) ℂ) (y : Idx D N) :
    MultiRes_vn (X *ᵥ Pi.single y 1) = Real.sqrt (∑ k, ‖X k y‖ ^ 2) := by
  rw [← Real.sqrt_sq (MultiRes_vn_nonneg _), MultiRes_vn_sq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_single_one]
  simp

private lemma FE_entry (X Y : Matrix (Idx D N) (Idx D N) ℂ) (x y : Idx D N) :
    (X * Y) x y = star (Xᴴ *ᵥ Pi.single x 1) ⬝ᵥ (Y *ᵥ Pi.single y 1) := by
  rw [← FE_dot_adj, Matrix.mulVec_mulVec, PS_dot_single]

/-- The sup or `ℓ²` norm of the rows of a word from its bounds with `V = (e_x, e_y)`. -/
private lemma FE_nrm_row (k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (u : List FLet)
    (X : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (B : ℝ) (hB : 0 ≤ B)
    (_hη : 0 < etaK D N k ε) (hm : 0 < FE_M D N k ε)
    (hV : ∀ j, (V j).1 = Pi.single j.1 1) (h : FE_WF k ε A u X V B) (mx : Bool) :
    FE_nrm mx (fun x => Real.sqrt (∑ k, ‖X x k‖ ^ 2)) ≤
      B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A) (u.countP (· == .lamt))
        (u.countP FO_isRes) mx * FE_M D N k ε ^ u.countP FE_isPr) := by
  obtain ⟨⟨-, hr, -⟩, hs⟩ := h
  cases mx
  · have h0 : 0 ≤ B * (FE_om (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
        (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr)) := by
      have := FE_om_nonneg (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes)
      have := Bd_opNorm_nonneg A
      positivity
    refine (Real.iSup_le (fun x => ?_) h0).trans (le_of_eq ?_)
    · have := hr (x, x)
      rw [hV, MultiRes_vn_single, mul_one, FE_vn_row] at this
      exact this
    · simp only [FE_half, Bool.false_eq_true, ↓reduceIte]
      ring
  · simp only [FE_nrm, ↓reduceIte]
    refine le_trans (le_of_eq ?_) hs
    unfold hsNorm
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.sq_sqrt (by positivity)]

/-- The sup or `ℓ²` norm of the columns of a word from its bounds with `V = (e_x, e_y)`. -/
private lemma FE_nrm_col (k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (u : List FLet)
    (X : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ)) (B : ℝ) (hB : 0 ≤ B)
    (_hη : 0 < etaK D N k ε) (hm : 0 < FE_M D N k ε)
    (hV : ∀ j, (V j).2 = Pi.single j.2 1) (h : FE_WF k ε A u X V B) (my : Bool) :
    FE_nrm my (fun y => Real.sqrt (∑ k, ‖X k y‖ ^ 2)) ≤
      B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A) (u.countP (· == .lamt))
        (u.countP FO_isRes) my * FE_M D N k ε ^ u.countP FE_isPr) := by
  obtain ⟨⟨-, -, hc⟩, hs⟩ := h
  cases my
  · have h0 : 0 ≤ B * (FE_om (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes) *
        (opNorm A ^ u.countP (· == .lamt) * FE_M D N k ε ^ u.countP FE_isPr)) := by
      have := FE_om_nonneg (etaK D N k ε) (FE_M D N k ε) (u.countP FO_isRes)
      have := Bd_opNorm_nonneg A
      positivity
    refine (Real.iSup_le (fun y => ?_) h0).trans (le_of_eq ?_)
    · have := hc (y, y)
      rw [hV, MultiRes_vn_single, mul_one, FE_vn_col] at this
      exact this
    · simp only [FE_half, Bool.false_eq_true, ↓reduceIte]
      ring
  · simp only [FE_nrm, ↓reduceIte]
    refine le_trans (le_of_eq ?_) hs
    unfold hsNorm
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Real.sq_sqrt (by positivity)]

end Ent

/-! ### The options without a split -/

private lemma FE_sq_sum_le {α : Type*} [Fintype α] (f g : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfg : ∀ i, f i ≤ g i) : Real.sqrt (∑ i, f i ^ 2) ≤ Real.sqrt (∑ i, g i ^ 2) :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hf i) (hfg i) 2)

/-- The entry, a Ward row or column, and the Hilbert–Schmidt norm of a word: (A.53) [entprodG]
isotropic, on `U^* U` and `U U^*`, and (A.53) averaged or (A.55) [two_loop_estimate]. -/
private lemma FE_base (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (w : List FLet) :
    FE_OK D δA εA ε C nb fun N A k e ι h c =>
      FE_PC (FE_f x y ((w.map (FLet.mat e ι h)).prod)) 0 0
        (c * (pkgPsi (etaK D N k ε) (FE_M D N k ε) (w.countP FO_isRes) *
          (opNorm A ^ w.countP (· == .lamt) * FE_M D N k ε ^ w.countP FE_isPr))) ∧
      FE_CC (FE_f x y ((w.map (FLet.mat e ι h)).prod)) 0
        (c * (FE_om (etaK D N k ε) (FE_M D N k ε) (w.countP FO_isRes) *
          (opNorm A ^ w.countP (· == .lamt) * FE_M D N k ε ^ w.countP FE_isPr))) ∧
      FE_RC (FE_f x y ((w.map (FLet.mat e ι h)).prod)) 0
        (c * (FE_om (etaK D N k ε) (FE_M D N k ε) (w.countP FO_isRes) *
          (opNorm A ^ w.countP (· == .lamt) * FE_M D N k ε ^ w.countP FE_isPr))) ∧
      Real.sqrt (∑ x', ∑ y', FE_f x y ((w.map (FLet.mat e ι h)).prod) x' y' ^ 2) ≤
        c * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
          (w.countP (· == .lamt)) (w.countP FO_isRes) true * FE_M D N k ε ^ w.countP FE_isPr) := by
  intro τ hτ D' hD'
  obtain ⟨c₀, K, Cst, hC, N₀, hN₀⟩ := FE_words3 D hD δA εA ε hδA hεA hε hε' hε'' C nb w [] []
    τ hτ D' hD'
  refine ⟨Cst, hC, N₀, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨hS, hg⟩ := hN₀ N hN μ hμ A hA k hk hkN hhs e he
  set V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (Pi.single j.1 1, Pi.single j.2 1) with hV
  obtain ⟨bad, hbad, hgood⟩ := hg ι V V V
  refine ⟨bad, hbad, fun h hh => ?_⟩
  obtain ⟨⟨⟨hi, hr, hc⟩, hs⟩, -, -⟩ := hgood h hh
  obtain ⟨-, -, -, -, -, hη, hm, -⟩ := hS
  set W := (w.map (FLet.mat e ι h)).prod
  set B := Cst * (N : ℝ) ^ τ
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hop0 := Bd_opNorm_nonneg A
  have hs1 : 0 ≤ opNorm A ^ w.countP (· == .lamt) * FE_M D N k ε ^ w.countP FE_isPr := by
    positivity
  have hiso0 : 0 ≤ B * (pkgPsi (etaK D N k ε) (FE_M D N k ε) (w.countP FO_isRes) *
      (opNorm A ^ w.countP (· == .lamt) * FE_M D N k ε ^ w.countP FE_isPr)) :=
    mul_nonneg hB (mul_nonneg (PS_psi_nonneg hη hm.le _) hs1)
  have hrow0 : 0 ≤ B * (FE_om (etaK D N k ε) (FE_M D N k ε) (w.countP FO_isRes) *
      (opNorm A ^ w.countP (· == .lamt) * FE_M D N k ε ^ w.countP FE_isPr)) :=
    mul_nonneg hB (mul_nonneg (FE_om_nonneg _ _ _) hs1)
  refine ⟨⟨fun _ => _, fun _ => 1, fun _ => hiso0, fun _ => zero_le_one, fun x' y' => ?_, ?_⟩,
    ⟨fun _ => _, fun _ => hrow0, fun y' => ?_, FE_nrm_const _ _ hrow0 rfl⟩,
    ⟨fun _ => _, fun _ => hrow0, fun x' => ?_, FE_nrm_const _ _ hrow0 rfl⟩, ?_⟩
  · refine (FE_f_le x y W x' y').trans ?_
    have := hi (x', y')
    simp only [hV, MultiRes_vn_single, mul_one, PS_dot_single] at this
    simpa using this
  · refine mul_le_mul (FE_nrm_const _ _ hiso0 rfl) (FE_nrm_const _ _ zero_le_one rfl)
      (FE_nrm_nonneg _ _ fun _ => zero_le_one) hiso0 |>.trans (le_of_eq (mul_one _))
  · refine (FE_sq_sum_le _ _ (fun x' => FE_f_nonneg x y W x' y')
      fun x' => FE_f_le x y W x' y').trans ?_
    have := hc (y', y')
    simp only [hV, MultiRes_vn_single, mul_one, FE_vn_col] at this
    exact this
  · refine (FE_sq_sum_le _ _ (fun y' => FE_f_nonneg x y W x' y')
      fun y' => FE_f_le x y W x' y').trans ?_
    have := hr (x', x')
    simp only [hV, MultiRes_vn_single, mul_one, FE_vn_row] at this
    exact this
  · refine le_trans ?_ hs
    unfold hsNorm
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun x' _ => Finset.sum_le_sum fun y' _ =>
      pow_le_pow_left₀ (FE_f_nonneg x y W x' y') (FE_f_le x y W x' y') 2)

/-! ### The options with a split -/

private lemma FE_beq (b : Bool) : ((if b then 1 else 0 : ℕ) == 1) = b := by cases b <;> rfl

private lemma FE_nrm_mul {ι : Type*} [Fintype ι] (m : Bool) (a : ι → ℝ) (c : ℝ)
    (ha : ∀ x, 0 ≤ a x) (hc : 0 ≤ c) : FE_nrm m (fun x => a x * c) ≤ FE_nrm m a * c := by
  cases m
  · exact Real.iSup_le (fun x => mul_le_mul_of_nonneg_right (FE_le_sup a x) hc)
      (mul_nonneg (Real.iSup_nonneg ha) hc)
  · simp only [FE_nrm, ↓reduceIte]
    rw [FE_sqrt_mul_sq a c hc]

private lemma FE_det_indep {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (h h' : Idx D N → Idx D N → ℂ) (u : List FLet) (hu : u.countP FO_isRes = 0) :
    (u.map (FLet.mat e ι h)).prod = (u.map (FLet.mat e ι h')).prod := by
  congr 1
  refine List.map_congr_left fun z hz => ?_
  cases z with
  | res a f =>
    have := List.countP_eq_zero.1 hu _ hz
    simp [FO_isRes] at this
  | det a pr => rfl
  | proj x => rfl
  | lamt => rfl

private lemma FE_rpow3 (N : ℕ) (τ : ℝ) :
    ((N : ℝ) ^ (τ / 3)) ^ 3 = (N : ℝ) ^ τ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

private lemma FE_rpow2 (N : ℕ) (τ : ℝ) :
    ((N : ℝ) ^ (τ / 2)) ^ 2 = (N : ℝ) ^ τ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- The word `X Y Z` with `X`, `Z` without resolvent: `|(X Y Z)_{xy}| ≤ ‖e_xᵀ X‖ ‖Z e_y‖
|⟨u_x, Y v_y⟩|` with deterministic `u_x`, `v_y`, by the isotropic (A.53) [entprodG] for `Y`
((5.68) [bound_factors], (5.71) [Cauchy_example_2]). -/
private lemma FE_sand (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (wX wY wZ : List FLet) (hX : wX.countP FO_isRes = 0) (hZ : wZ.countP FO_isRes = 0) :
    FE_OK D δA εA ε C nb fun N A k e ι h c => ∀ mx my : Bool,
      FE_PC (FE_f x y (((wX ++ wY ++ wZ).map (FLet.mat e ι h)).prod))
        (if mx then 1 else 0) (if my then 1 else 0)
        (c * ((FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wX.countP (· == .lamt)) 0 mx * FE_M D N k ε ^ wX.countP FE_isPr) *
          (pkgPsi (etaK D N k ε) (FE_M D N k ε) (wY.countP FO_isRes) *
            (opNorm A ^ wY.countP (· == .lamt) * FE_M D N k ε ^ wY.countP FE_isPr)) *
          (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wZ.countP (· == .lamt)) 0 my * FE_M D N k ε ^ wZ.countP FE_isPr))) := by
  intro τ hτ D' hD'
  obtain ⟨c₀, K, Cst, hC, N₀, hN₀⟩ := FE_words3 D hD δA εA ε hδA hεA hε hε' hε'' C nb wX wY wZ
    (τ / 3) (by positivity) D' hD'
  refine ⟨Cst ^ 3, by positivity, N₀, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨hS, hg⟩ := hN₀ N hN μ hμ A hA k hk hkN hhs e he
  set X₀ := (wX.map (FLet.mat e ι 0)).prod
  set Z₀ := (wZ.map (FLet.mat e ι 0)).prod
  set V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (Pi.single j.1 1, Pi.single j.2 1) with hV
  set VY : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (X₀ᴴ *ᵥ Pi.single j.1 1, Z₀ *ᵥ Pi.single j.2 1) with hVY
  obtain ⟨bad, hbad, hgood⟩ := hg ι V VY V
  refine ⟨bad, hbad, fun h hh mx my => ?_⟩
  obtain ⟨gX, ⟨⟨hiY, -, -⟩, -⟩, gZ⟩ := hgood h hh
  obtain ⟨-, -, -, -, -, hη, hm, -⟩ := hS
  rw [FE_det_indep e ι h 0 wX hX] at gX
  rw [FE_det_indep e ι h 0 wZ hZ] at gZ
  set B := Cst * (N : ℝ) ^ (τ / 3)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hop0 := Bd_opNorm_nonneg A
  set iY := pkgPsi (etaK D N k ε) (FE_M D N k ε) (wY.countP FO_isRes) *
    (opNorm A ^ wY.countP (· == .lamt) * FE_M D N k ε ^ wY.countP FE_isPr)
  have hiY0 : 0 ≤ iY := mul_nonneg (PS_psi_nonneg hη hm.le _) (by positivity)
  have hW : ((wX ++ wY ++ wZ).map (FLet.mat e ι h)).prod =
      X₀ * ((wY.map (FLet.mat e ι h)).prod * Z₀) := by
    rw [List.map_append, List.map_append, List.prod_append, List.prod_append,
      FE_det_indep e ι h 0 wX hX, FE_det_indep e ι h 0 wZ hZ, Matrix.mul_assoc]
  have hrowX := FE_nrm_row k ε A wX X₀ V B hB hη hm (fun _ => rfl) gX mx
  have hcolZ := FE_nrm_col k ε A wZ Z₀ V B hB hη hm (fun _ => rfl) gZ my
  rw [hX] at hrowX
  rw [hZ] at hcolZ
  have hra : ∀ x', 0 ≤ Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2) := fun _ => Real.sqrt_nonneg _
  have hcb : ∀ y', 0 ≤ Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2) := fun _ => Real.sqrt_nonneg _
  refine ⟨fun x' => Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2) * (B * iY),
    fun y' => Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2), fun x' => mul_nonneg (hra x') (mul_nonneg hB hiY0),
    hcb, fun x' y' => ?_, ?_⟩
  · refine (FE_f_le x y _ x' y').trans ?_
    rw [hW, FE_entry, ← Matrix.mulVec_mulVec]
    have := hiY (x', y')
    simp only [hVY] at this
    rw [FE_vn_row, FE_vn_col] at this
    refine this.trans (le_of_eq ?_)
    ring
  · rw [FE_beq, FE_beq]
    have h1 := FE_nrm_mul mx _ (B * iY) hra (mul_nonneg hB hiY0)
    have hX0 : 0 ≤ FE_nrm mx fun x' => Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2) := FE_nrm_nonneg _ _ hra
    have hZ0 : 0 ≤ FE_nrm my fun y' => Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2) := FE_nrm_nonneg _ _ hcb
    have hhX : 0 ≤ FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
        (wX.countP (· == .lamt)) 0 mx * FE_M D N k ε ^ wX.countP FE_isPr :=
      mul_nonneg (FE_half_nonneg N (Real.sqrt_nonneg _) hop0 _ _ _) (by positivity)
    calc FE_nrm mx (fun x' => Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2) * (B * iY)) *
          FE_nrm my (fun y' => Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2))
        ≤ (FE_nrm mx (fun x' => Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2)) * (B * iY)) *
          FE_nrm my (fun y' => Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 hZ0
      _ ≤ (B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wX.countP (· == .lamt)) 0 mx * FE_M D N k ε ^ wX.countP FE_isPr) * (B * iY)) *
          (B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wZ.countP (· == .lamt)) 0 my * FE_M D N k ε ^ wZ.countP FE_isPr)) := by
          gcongr
      _ = Cst ^ 3 * (N : ℝ) ^ τ * _ := by
          rw [← FE_rpow3 N τ]
          ring

/-- The word `X Y` split between `X` and `Y`: `|(X Y)_{xy}| ≤ ‖e_xᵀ X‖ ‖Y e_y‖`, each half in
sup or `ℓ²` ((5.68) [bound_factors], (5.70) [Cauchy_example_1], (5.72)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_operator_norm_bound]). -/
private lemma FE_plain (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (wL wR : List FLet) :
    FE_OK D δA εA ε C nb fun N A k e ι h c => ∀ mx my : Bool,
      FE_PC (FE_f x y (((wL ++ wR).map (FLet.mat e ι h)).prod))
        (if mx then 1 else 0) (if my then 1 else 0)
        (c * ((FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wL.countP (· == .lamt)) (wL.countP FO_isRes) mx * FE_M D N k ε ^ wL.countP FE_isPr) *
          (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wR.countP (· == .lamt)) (wR.countP FO_isRes) my *
              FE_M D N k ε ^ wR.countP FE_isPr))) := by
  intro τ hτ D' hD'
  obtain ⟨c₀, K, Cst, hC, N₀, hN₀⟩ := FE_words3 D hD δA εA ε hδA hεA hε hε' hε'' C nb wL wR []
    (τ / 2) (by positivity) D' hD'
  refine ⟨Cst ^ 2, by positivity, N₀, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨hS, hg⟩ := hN₀ N hN μ hμ A hA k hk hkN hhs e he
  set V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (Pi.single j.1 1, Pi.single j.2 1) with hV
  obtain ⟨bad, hbad, hgood⟩ := hg ι V V V
  refine ⟨bad, hbad, fun h hh mx my => ?_⟩
  obtain ⟨gL, gR, -⟩ := hgood h hh
  obtain ⟨-, -, -, -, -, hη, hm, -⟩ := hS
  set XL := (wL.map (FLet.mat e ι h)).prod
  set XR := (wR.map (FLet.mat e ι h)).prod
  set B := Cst * (N : ℝ) ^ (τ / 2)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hop0 := Bd_opNorm_nonneg A
  have hrowL := FE_nrm_row k ε A wL XL V B hB hη hm (fun _ => rfl) gL mx
  have hcolR := FE_nrm_col k ε A wR XR V B hB hη hm (fun _ => rfl) gR my
  have hra : ∀ x', 0 ≤ Real.sqrt (∑ k, ‖XL x' k‖ ^ 2) := fun _ => Real.sqrt_nonneg _
  have hcb : ∀ y', 0 ≤ Real.sqrt (∑ k, ‖XR k y'‖ ^ 2) := fun _ => Real.sqrt_nonneg _
  refine ⟨fun x' => Real.sqrt (∑ k, ‖XL x' k‖ ^ 2), fun y' => Real.sqrt (∑ k, ‖XR k y'‖ ^ 2),
    hra, hcb, fun x' y' => ?_, ?_⟩
  · refine (FE_f_le x y _ x' y').trans ?_
    rw [List.map_append, List.prod_append]
    exact PS_entry_cs XL XR x' y'
  · rw [FE_beq, FE_beq]
    calc FE_nrm mx (fun x' => Real.sqrt (∑ k, ‖XL x' k‖ ^ 2)) *
          FE_nrm my (fun y' => Real.sqrt (∑ k, ‖XR k y'‖ ^ 2))
        ≤ (B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wL.countP (· == .lamt)) (wL.countP FO_isRes) mx * FE_M D N k ε ^ wL.countP FE_isPr)) *
          (B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wR.countP (· == .lamt)) (wR.countP FO_isRes) my *
              FE_M D N k ε ^ wR.countP FE_isPr)) :=
          mul_le_mul hrowL hcolR (FE_nrm_nonneg _ _ hcb) (hrowL.trans' (FE_nrm_nonneg _ _ hra))
      _ = Cst ^ 2 * (N : ℝ) ^ τ * _ := by
          rw [← FE_rpow2 N τ]
          ring

/-- The word `X Y` with `X` without resolvent and the column label summed first in `ℓ²`:
`(Σ_y |(X Y)_{xy}|²)^{1/2} ≤ ‖e_xᵀ X‖ ‖Y^* u_x‖` with a deterministic unit `u_x`, by (A.53)
[entprodG] on `Y Y^*`. -/
private lemma FE_rowL (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (wL wR : List FLet) (hL : wL.countP FO_isRes = 0) :
    FE_OK D δA εA ε C nb fun N A k e ι h c => ∀ mx : Bool,
      FE_RC (FE_f x y (((wL ++ wR).map (FLet.mat e ι h)).prod)) (if mx then 1 else 0)
        (c * ((FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wL.countP (· == .lamt)) 0 mx * FE_M D N k ε ^ wL.countP FE_isPr) *
          (FE_om (etaK D N k ε) (FE_M D N k ε) (wR.countP FO_isRes) *
            (opNorm A ^ wR.countP (· == .lamt) * FE_M D N k ε ^ wR.countP FE_isPr)))) := by
  intro τ hτ D' hD'
  obtain ⟨c₀, K, Cst, hC, N₀, hN₀⟩ := FE_words3 D hD δA εA ε hδA hεA hε hε' hε'' C nb wL wR []
    (τ / 2) (by positivity) D' hD'
  refine ⟨Cst ^ 2, by positivity, N₀, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨hS, hg⟩ := hN₀ N hN μ hμ A hA k hk hkN hhs e he
  set X₀ := (wL.map (FLet.mat e ι 0)).prod
  set V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (Pi.single j.1 1, Pi.single j.2 1) with hV
  set VR : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (X₀ᴴ *ᵥ Pi.single j.1 1, Pi.single j.2 1) with hVR
  obtain ⟨bad, hbad, hgood⟩ := hg ι V VR V
  refine ⟨bad, hbad, fun h hh mx => ?_⟩
  obtain ⟨gL, ⟨⟨-, hrR, -⟩, -⟩, -⟩ := hgood h hh
  obtain ⟨-, -, -, -, -, hη, hm, -⟩ := hS
  rw [FE_det_indep e ι h 0 wL hL] at gL
  set XR := (wR.map (FLet.mat e ι h)).prod
  set B := Cst * (N : ℝ) ^ (τ / 2)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hop0 := Bd_opNorm_nonneg A
  set rR := FE_om (etaK D N k ε) (FE_M D N k ε) (wR.countP FO_isRes) *
    (opNorm A ^ wR.countP (· == .lamt) * FE_M D N k ε ^ wR.countP FE_isPr)
  have hrR0 : 0 ≤ rR := mul_nonneg (FE_om_nonneg _ _ _) (by positivity)
  have hrowL := FE_nrm_row k ε A wL X₀ V B hB hη hm (fun _ => rfl) gL mx
  rw [hL] at hrowL
  have hra : ∀ x', 0 ≤ Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2) := fun _ => Real.sqrt_nonneg _
  refine ⟨fun x' => Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2) * (B * rR),
    fun x' => mul_nonneg (hra x') (mul_nonneg hB hrR0), fun x' => ?_, ?_⟩
  · have hW : ((wL ++ wR).map (FLet.mat e ι h)).prod = X₀ * XR := by
      rw [List.map_append, List.prod_append, FE_det_indep e ι h 0 wL hL]
    refine (FE_sq_sum_le _ _ (fun y' => FE_f_nonneg x y _ x' y')
      fun y' => FE_f_le x y _ x' y').trans ?_
    rw [hW, ← FE_vn_row, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec]
    have := hrR (x', x')
    simp only [hVR] at this
    rw [FE_vn_row] at this
    refine this.trans (le_of_eq ?_)
    ring
  · rw [FE_beq]
    refine (FE_nrm_mul mx _ (B * rR) hra (mul_nonneg hB hrR0)).trans ?_
    calc FE_nrm mx (fun x' => Real.sqrt (∑ k, ‖X₀ x' k‖ ^ 2)) * (B * rR)
        ≤ (B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wL.countP (· == .lamt)) 0 mx * FE_M D N k ε ^ wL.countP FE_isPr)) * (B * rR) :=
          mul_le_mul_of_nonneg_right hrowL (mul_nonneg hB hrR0)
      _ = Cst ^ 2 * (N : ℝ) ^ τ * _ := by
          rw [← FE_rpow2 N τ]
          ring

/-- The word `X Y` with `Y` without resolvent and the row label summed first in `ℓ²`:
`(Σ_x |(X Y)_{xy}|²)^{1/2} ≤ ‖X v_y‖ ‖Y e_y‖` with a deterministic unit `v_y`, by (A.53)
[entprodG] on `X^* X`. -/
private lemma FE_colR (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (wL wR : List FLet) (hR : wR.countP FO_isRes = 0) :
    FE_OK D δA εA ε C nb fun N A k e ι h c => ∀ my : Bool,
      FE_CC (FE_f x y (((wL ++ wR).map (FLet.mat e ι h)).prod)) (if my then 1 else 0)
        (c * ((FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wR.countP (· == .lamt)) 0 my * FE_M D N k ε ^ wR.countP FE_isPr) *
          (FE_om (etaK D N k ε) (FE_M D N k ε) (wL.countP FO_isRes) *
            (opNorm A ^ wL.countP (· == .lamt) * FE_M D N k ε ^ wL.countP FE_isPr)))) := by
  intro τ hτ D' hD'
  obtain ⟨c₀, K, Cst, hC, N₀, hN₀⟩ := FE_words3 D hD δA εA ε hδA hεA hε hε' hε'' C nb wL wR []
    (τ / 2) (by positivity) D' hD'
  refine ⟨Cst ^ 2, by positivity, N₀, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨hS, hg⟩ := hN₀ N hN μ hμ A hA k hk hkN hhs e he
  set Z₀ := (wR.map (FLet.mat e ι 0)).prod
  set V : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (Pi.single j.1 1, Pi.single j.2 1) with hV
  set VL : Idx D N × Idx D N → (Idx D N → ℂ) × (Idx D N → ℂ) :=
    fun j => (Pi.single j.1 1, Z₀ *ᵥ Pi.single j.2 1) with hVL
  obtain ⟨bad, hbad, hgood⟩ := hg ι VL V V
  refine ⟨bad, hbad, fun h hh my => ?_⟩
  obtain ⟨⟨⟨-, -, hcL⟩, -⟩, gR, -⟩ := hgood h hh
  obtain ⟨-, -, -, -, -, hη, hm, -⟩ := hS
  rw [FE_det_indep e ι h 0 wR hR] at gR
  set XL := (wL.map (FLet.mat e ι h)).prod
  set B := Cst * (N : ℝ) ^ (τ / 2)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hop0 := Bd_opNorm_nonneg A
  set rL := FE_om (etaK D N k ε) (FE_M D N k ε) (wL.countP FO_isRes) *
    (opNorm A ^ wL.countP (· == .lamt) * FE_M D N k ε ^ wL.countP FE_isPr)
  have hrL0 : 0 ≤ rL := mul_nonneg (FE_om_nonneg _ _ _) (by positivity)
  have hcolR := FE_nrm_col k ε A wR Z₀ V B hB hη hm (fun _ => rfl) gR my
  rw [hR] at hcolR
  have hcb : ∀ y', 0 ≤ Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2) := fun _ => Real.sqrt_nonneg _
  refine ⟨fun y' => Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2) * (B * rL),
    fun y' => mul_nonneg (hcb y') (mul_nonneg hB hrL0), fun y' => ?_, ?_⟩
  · have hW : ((wL ++ wR).map (FLet.mat e ι h)).prod = XL * Z₀ := by
      rw [List.map_append, List.prod_append, FE_det_indep e ι h 0 wR hR]
    refine (FE_sq_sum_le _ _ (fun x' => FE_f_nonneg x y _ x' y')
      fun x' => FE_f_le x y _ x' y').trans ?_
    rw [hW, ← FE_vn_col, ← Matrix.mulVec_mulVec]
    have := hcL (y', y')
    simp only [hVL] at this
    rw [FE_vn_col] at this
    refine this.trans (le_of_eq ?_)
    ring
  · rw [FE_beq]
    refine (FE_nrm_mul my _ (B * rL) hcb (mul_nonneg hB hrL0)).trans ?_
    calc FE_nrm my (fun y' => Real.sqrt (∑ k, ‖Z₀ k y'‖ ^ 2)) * (B * rL)
        ≤ (B * (FE_half N (etaK D N k ε) (FE_M D N k ε) (hsNorm A) (opNorm A)
            (wR.countP (· == .lamt)) 0 my * FE_M D N k ε ^ wR.countP FE_isPr)) * (B * rL) :=
          mul_le_mul_of_nonneg_right hcolR (mul_nonneg hB hrL0)
      _ = Cst ^ 2 * (N : ℝ) ^ τ * _ := by
          rw [← FE_rpow2 N τ]
          ring

/-! ### (5.90) in one block -/

/-- The sizes of the options of (5.90) [eq:addoneLambda]: `‖A‖² + N^{-1} ‖A‖²_HS`,
`‖A‖_HS ‖A‖ + N^{-1/2} ‖A‖²_HS` with one `ℓ²`, `2 ‖A‖²_HS` with two. -/
private def FE_v590 (N : ℕ) (hs op : ℝ) (mx my : Bool) : ℝ :=
  if mx && my then hs ^ 2 + hs ^ 2
  else if mx || my then hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2
  else op ^ 2 + (N : ℝ)⁻¹ * hs ^ 2

set_option maxHeartbeats 1000000 in
-- the four uses of the option are bounded in one proof
/-- (5.90) [eq:addoneLambda] in one block: `|(u₁ Λ̃ u₂)_{xy}| ≤ K (‖Λ e_x‖ ‖Λ e_y‖ + |δ|)`
`≤ K (‖Λ e_x‖ + |δ|^{1/2}) (‖Λ e_y‖ + |δ|^{1/2})`, with `‖Λ e_x‖ ≤ 2 ‖A‖`, `Σ_x ‖Λ e_x‖² = ‖Λ‖²_HS`
and `|δ| ≤ K N^{-1} ‖A‖²_HS`. -/
private lemma FE_a590 (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (u₁ u₂ : List FLet) (hu : (u₁ ++ u₂).all FLet.isDetE = true) (hxy : fsameBlk x y = true) :
    FE_OK D δA εA ε C nb fun N A _k e ι h c => ∀ mx my : Bool,
      FE_PC (FE_f x y (((u₁ ++ FLet.lamt :: u₂).map (FLet.mat e ι h)).prod))
        (if mx then 1 else 0) (if my then 1 else 0)
        (c * FE_v590 N (hsNorm A) (opNorm A) mx my) := by
  intro τ hτ D' hD'
  obtain ⟨Ka, hKa, Na, hNa⟩ := pkg_add_lambda_slot D hD δA εA ε hδA hεA hε hε' hε'' u₁ u₂ hu
  obtain ⟨c₀, K, hc₀, hK, N₁, hslot⟩ := FE_slot D hD δA εA ε hδA hεA hε hε' hε'' C
  set T : ℝ := K + D + 2 with hT
  have hT1 : 1 ≤ T := by
    rw [hT]; have := (Nat.cast_nonneg D : (0 : ℝ) ≤ D); linarith
  refine ⟨2 * Ka * T ^ 2, by positivity, max Na N₁,
    fun N hN μ hμ A hA k hk hkN hhs e he ι => ⟨∅, by simp, fun h _ mx my => ?_⟩⟩
  have hS := hslot N (le_of_max_le_right hN) μ hμ A hA k hk hkN hhs e he
  obtain ⟨-, heA, hN1, -, -, -, -, -, -, -, -, -, hslam, -, hlop, hδ⟩ := hS
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
  set op := opNorm A
  set hs := hsNorm A
  have hop0 : 0 ≤ op := Bd_opNorm_nonneg A
  have hhs0 : 0 ≤ hs := Real.sqrt_nonneg _
  set Λ := lam D N e.A
  set cf : Idx D N → ℝ := fun x' => Real.sqrt (∑ i, ‖Λ i x'‖ ^ 2) with hcf
  set s := Real.sqrt |e.δ| with hs_def
  have hcf0 : ∀ x', 0 ≤ cf x' := fun _ => Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hcfs : ∀ x', 0 ≤ cf x' + s := fun x' => add_nonneg (hcf0 x') hs0
  -- the bound of the entries
  have hent : ∀ x' y', FE_f x y (((u₁ ++ FLet.lamt :: u₂).map (FLet.mat e ι h)).prod) x' y' ≤
      (cf x' + s) * Ka * (cf y' + s) := by
    intro x' y'
    unfold FE_f
    split_ifs with hb
    · exact mul_nonneg (mul_nonneg (hcfs x') hKa.le) (hcfs y')
    · have hb' : x'.1 = y'.1 := by
        by_contra hne
        exact hb ⟨hxy, hne⟩
      have h1 := hNa N (le_of_max_le_left hN) A hA k hk hkN hhs e he nb ι h x' y' hb'
      rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons]
      simp only [FLet.mat] at h1 ⊢
      rw [← Matrix.mul_assoc]
      refine h1.trans ?_
      have hδs : |e.δ| = s * s := by rw [hs_def, Real.mul_self_sqrt (abs_nonneg _)]
      rw [hδs]
      have := mul_nonneg (hcf0 x') hs0
      have := mul_nonneg (hcf0 y') hs0
      nlinarith [mul_nonneg hKa.le (mul_nonneg hs0 hs0)]
  -- the norms of `cf + s`
  have hcol : ∀ x', cf x' ≤ T * op := fun x' => by
    have h1 := MultiRes_vn_mulVec_le Λ (Pi.single x' 1)
    rw [MultiRes_vn_single, mul_one, FE_vn_col] at h1
    refine h1.trans (hlop.trans ?_)
    rw [heA] at *
    exact mul_le_mul_of_nonneg_right (by rw [hT]; linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
      hop0
  have hhalf : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hN0.le]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsb : s ≤ T * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hs) := by
    rw [hhalf]
    have hsq : s ^ 2 ≤ K * hs ^ 2 / N := by
      rw [hs_def, Real.sq_sqrt (abs_nonneg _)]
      refine hδ.trans (le_of_eq ?_)
      ring
    have hK' : K ≤ T ^ 2 := by rw [hT]; nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
    have h2 : s ^ 2 ≤ (T * ((Real.sqrt N)⁻¹ * hs)) ^ 2 := by
      rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hN0.le]
      calc s ^ 2 ≤ K * hs ^ 2 / N := hsq
        _ ≤ T ^ 2 * hs ^ 2 / N := by gcongr
        _ = T ^ 2 * ((N : ℝ)⁻¹ * hs ^ 2) := by ring
    exact (pow_le_pow_iff_left₀ hs0 (by positivity) two_ne_zero).1 h2
  have hsup : FE_nrm false (fun x' => cf x' + s) ≤ T * (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs) :=
    Real.iSup_le (fun x' => by nlinarith [hcol x']) (by positivity)
  have hl2 : FE_nrm true (fun x' => cf x' + s) ≤ 2 * T * hs := by
    simp only [FE_nrm, ↓reduceIte]
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : ∑ x', (cf x' + s) ^ 2 ≤ ∑ x', (2 * cf x' ^ 2 + 2 * s ^ 2) :=
      Finset.sum_le_sum fun x' _ => by nlinarith [sq_nonneg (cf x' - s)]
    have h2 : ∑ x', cf x' ^ 2 = hsNorm Λ ^ 2 := by
      rw [FE_hs_sq, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [hcf, Real.sq_sqrt (by positivity)]
    have h3 : hsNorm Λ ^ 2 ≤ (K * hs) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hslam 2
    have h4 : s ^ 2 ≤ K * hs ^ 2 / N := by
      rw [hs_def, Real.sq_sqrt (abs_nonneg _)]
      refine hδ.trans (le_of_eq ?_)
      ring
    have hcard : ∑ _x' : Idx D N, (2 * s ^ 2) = 2 * D * N * s ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h2, hcard] at h1
    have h5 : (N : ℝ) * s ^ 2 ≤ K * hs ^ 2 := by
      rw [le_div_iff₀ hN0] at h4
      linarith
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hKT : K ≤ T := by rw [hT]; linarith
    have hDT : (D : ℝ) ≤ T := by rw [hT]; linarith
    calc ∑ x', (cf x' + s) ^ 2 ≤ 2 * hsNorm Λ ^ 2 + 2 * D * N * s ^ 2 := h1
      _ ≤ 2 * (K * hs) ^ 2 + 2 * D * (K * hs ^ 2) := by nlinarith
      _ ≤ 2 * (T * T * hs ^ 2) + 2 * (T * T * hs ^ 2) := by
          have a1 : K * K ≤ T * T := mul_le_mul hKT hKT (by linarith) (by linarith)
          have a2 : (D : ℝ) * K ≤ T * T := mul_le_mul hDT hKT (by linarith) (by linarith)
          have b1 : (K * hs) ^ 2 ≤ T * T * hs ^ 2 := by
            rw [mul_pow, sq]
            exact mul_le_mul_of_nonneg_right a1 (sq_nonneg _)
          have b2 : (D : ℝ) * (K * hs ^ 2) ≤ T * T * hs ^ 2 := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right a2 (sq_nonneg _)
          linarith
      _ = (2 * T * hs) ^ 2 := by ring
  refine ⟨fun x' => (cf x' + s) * Ka, fun y' => cf y' + s,
    fun x' => mul_nonneg (hcfs x') hKa.le, hcfs, hent, ?_⟩
  rw [FE_beq, FE_beq]
  refine (mul_le_mul_of_nonneg_right (FE_nrm_mul mx _ Ka hcfs hKa.le)
    (FE_nrm_nonneg _ _ hcfs)).trans ?_
  have hσ : (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs) ^ 2 ≤
      2 * (op ^ 2 + (N : ℝ)⁻¹ * hs ^ 2) := by
    have e1 : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
      rw [hhalf, inv_pow, Real.sq_sqrt hN0.le]
    nlinarith [sq_nonneg (op - (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs)]
  have hC0 : 0 ≤ 2 * Ka * T ^ 2 := by positivity
  have hσ0 : 0 ≤ op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs := by positivity
  cases mx <;> cases my <;> simp only [FE_v590, Bool.and_false, Bool.and_true, Bool.or_false,
    Bool.or_true, Bool.false_eq_true, ↓reduceIte]
  · calc FE_nrm false (fun x' => cf x' + s) * Ka * FE_nrm false (fun y' => cf y' + s)
        ≤ T * (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs) * Ka *
          (T * (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs)) := by
          gcongr
          exact FE_nrm_nonneg _ _ hcfs
      _ = Ka * T ^ 2 * (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs) ^ 2 := by ring
      _ ≤ Ka * T ^ 2 * (2 * (op ^ 2 + (N : ℝ)⁻¹ * hs ^ 2)) := by gcongr
      _ = 2 * Ka * T ^ 2 * 1 * (op ^ 2 + (N : ℝ)⁻¹ * hs ^ 2) := by ring
      _ ≤ 2 * Ka * T ^ 2 * (N : ℝ) ^ τ * (op ^ 2 + (N : ℝ)⁻¹ * hs ^ 2) := by
          have : 0 ≤ op ^ 2 + (N : ℝ)⁻¹ * hs ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNτ hC0) this
  · calc FE_nrm false (fun x' => cf x' + s) * Ka * FE_nrm true (fun y' => cf y' + s)
        ≤ T * (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs) * Ka * (2 * T * hs) := by
          gcongr
          exact FE_nrm_nonneg _ _ hcfs
      _ = 2 * Ka * T ^ 2 * (hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2) := by ring
      _ = 2 * Ka * T ^ 2 * 1 * (hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2) := by ring
      _ ≤ 2 * Ka * T ^ 2 * (N : ℝ) ^ τ * (hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2) := by
          have : 0 ≤ hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNτ hC0) this
  · calc FE_nrm true (fun x' => cf x' + s) * Ka * FE_nrm false (fun y' => cf y' + s)
        ≤ 2 * T * hs * Ka * (T * (op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs)) := by
          gcongr
          exact FE_nrm_nonneg _ _ hcfs
      _ = 2 * Ka * T ^ 2 * (hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2) := by ring
      _ = 2 * Ka * T ^ 2 * 1 * (hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2) := by ring
      _ ≤ 2 * Ka * T ^ 2 * (N : ℝ) ^ τ * (hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2) := by
          have : 0 ≤ hs * op + (N : ℝ) ^ (-(1 / 2 : ℝ)) * hs ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNτ hC0) this
  · calc FE_nrm true (fun x' => cf x' + s) * Ka * FE_nrm true (fun y' => cf y' + s)
        ≤ 2 * T * hs * Ka * (2 * T * hs) := by
          gcongr
          exact FE_nrm_nonneg _ _ hcfs
      _ = 2 * Ka * T ^ 2 * (hs ^ 2 + hs ^ 2) := by ring
      _ = 2 * Ka * T ^ 2 * 1 * (hs ^ 2 + hs ^ 2) := by ring
      _ ≤ 2 * Ka * T ^ 2 * (N : ℝ) ^ τ * (hs ^ 2 + hs ^ 2) := by
          have : 0 ≤ hs ^ 2 + hs ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNτ hC0) this

/-! ### The values of the options of the menu -/

/-- The sizes of the options of (5.90) [eq:addoneLambda] as monomials. -/
private def FE_l590 (mx my : Bool) : List FMono :=
  if mx && my then [⟨0, 0, 0, 2, 0⟩, ⟨0, 0, 0, 2, 0⟩]
  else if mx || my then [⟨0, 0, 0, 1, 1⟩, ⟨-1, 0, 0, 2, 0⟩]
  else [⟨0, 0, 0, 0, 2⟩, ⟨-2, 0, 0, 2, 0⟩]

section Menu

variable (N : ℕ) (M η hs op : ℝ) (hN : 1 ≤ N) (hM : 0 < M) (hη : 0 < η)
include hN hM hη

private lemma FE_S_ext (o₀ : FOpt) (p : ℕ) :
    ((FO_ext ⟨0, 2 * (p : ℤ), 0, 0, 0⟩ o₀).val.map fun m => m.evalR N M η hs op).sum =
      (o₀.val.map fun m => m.evalR N M η hs op).sum * M ^ p := by
  simp only [FO_ext, List.map_map]
  rw [← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp_apply]
  rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FE_ev_ext]

private lemma FE_ev_iso (r n : ℕ) :
    ((FMono.psi r).mul ⟨0, 0, 0, 0, n⟩).evalR N M η hs op = pkgPsi η M r * op ^ n := by
  rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FO_ev_psi _ _ _ _ _ hη.le, FE_ev_op]

private lemma FE_ev_row (r n : ℕ) :
    ((FMono.omega r).mul ⟨0, 0, 0, 0, n⟩).evalR N M η hs op = FE_om η M r * op ^ n := by
  rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FE_ev_om _ _ _ _ _ hM.le hη, FE_ev_op]

private lemma FE_ev_dbl (r : ℕ) (mx my : Bool) :
    ((FMono.psi r).mul ⟨0, 0, 0, (if mx then 1 else 0) + (if my then 1 else 0),
      (if mx then 0 else 1) + (if my then 0 else 1)⟩).evalR N M η hs op =
      pkgPsi η M r * (FE_half N η M hs op 1 0 mx * FE_half N η M hs op 1 0 my) := by
  rw [FO_evalR_mul _ _ N hN M η hs op hM hη, FO_ev_psi _ _ _ _ _ hη.le, FE_ev_hsop]
  cases mx <;> cases my <;>
    simp only [FE_half, FE_om_zero, Bool.false_eq_true, ↓reduceIte, one_ne_zero] <;> ring

omit hN hM hη in
private lemma FE_ev_590 (mx my : Bool) :
    ((FE_l590 mx my).map fun m => m.evalR N M η hs op).sum = FE_v590 N hs op mx my := by
  unfold FE_l590
  cases mx <;> cases my <;>
    simp [FE_v590, FMono.evalR, Real.rpow_neg_one] <;> norm_num [Real.rpow_neg_one]

end Menu

/-! ### The words of the options -/

/-- The split of a word at its `(k+1)`-th `Λ̃`, with `Λ̃` on the left (`left`) or on the right. -/
private lemma FE_spl_words (w : List FLet) (k : ℕ) (hk : k < (FLet.parts w).length - 1)
    (left : Bool) : ∃ wL wR : List FLet, w = wL ++ wR ∧
      wL.countP (· == .lamt) = (if left then k + 1 else k) ∧
      wR.countP (· == .lamt) = (FLet.parts w).length - 1 - (if left then k + 1 else k) ∧
      wL.countP FO_isRes = ((FLet.parts w).take (k + 1)).sum ∧
      wR.countP FO_isRes = ((FLet.parts w).drop (k + 1)).sum ∧
      wL.countP FE_isPr + wR.countP FE_isPr = w.countP FE_isPr := by
  rw [FE_parts_len] at hk ⊢
  obtain ⟨W₁, W₂, rfl, h1⟩ := FE_split_at k w (by omega)
  obtain ⟨hc, hp, hr⟩ := FE_split_counts W₁ W₂
  have hl : (FLet.parts W₁).length = k + 1 := by rw [FE_parts_len, h1]
  rw [FE_parts_app, List.take_left' hl, List.drop_left' hl, FE_parts_sum, FE_parts_sum, hc, hp]
  cases left
  · refine ⟨W₁, FLet.lamt :: W₂, rfl, h1, ?_, rfl, ?_, ?_⟩
    · simp; omega
    · simp [FO_isRes]
    · simp [FE_isPr]
  · refine ⟨W₁ ++ [FLet.lamt], W₂, by simp, ?_, ?_, ?_, rfl, ?_⟩
    · simp [List.countP_append, h1]
    · simp only [↓reduceIte]; omega
    · simp [List.countP_append, FO_isRes]
    · simp [List.countP_append, FE_isPr]

/-- A word with two `Λ̃` and no resolvent outside them. -/
private lemma FE_dbl_words (w : List FLet)
    (h : ((FLet.parts w).length - 1 = 2 && (FLet.parts w).head? = some 0 &&
      (FLet.parts w).getLast? = some 0) = true) :
    ∃ wX wY wZ : List FLet, w = wX ++ wY ++ wZ ∧ wX.countP FO_isRes = 0 ∧
      wZ.countP FO_isRes = 0 ∧ wX.countP (· == .lamt) = 1 ∧ wY.countP (· == .lamt) = 0 ∧
      wZ.countP (· == .lamt) = 1 ∧ wY.countP FO_isRes = (FLet.parts w).getD 1 0 ∧
      wX.countP FE_isPr + wY.countP FE_isPr + wZ.countP FE_isPr = w.countP FE_isPr := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h2, hh⟩, hl⟩ := h
  rw [FE_parts_len] at h2
  obtain ⟨X₀, W, rfl, hX⟩ := FE_first w (by omega)
  obtain ⟨hc, hp, -⟩ := FE_split_counts X₀ W
  obtain ⟨Y, Z₀, rfl, hY⟩ := FE_first W (by omega)
  obtain ⟨hc', hp', -⟩ := FE_split_counts Y Z₀
  have hZ : Z₀.countP (· == .lamt) = 0 := by omega
  rw [FE_parts_app, FE_parts_app, FE_parts_free X₀ hX, FE_parts_free Y hY,
    FE_parts_free Z₀ hZ] at hh hl ⊢
  simp only [List.singleton_append, List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
    List.getLast?_singleton] at hh hl
  refine ⟨X₀ ++ [FLet.lamt], Y, FLet.lamt :: Z₀, by simp, ?_, ?_, ?_, hY, ?_, rfl, ?_⟩
  · simp [List.countP_append, FO_isRes, hh]
  · simp [FO_isRes, hl]
  · simp [List.countP_append, hX]
  · simp [hZ]
  · rw [hp, hp']
    simp [List.countP_append, FE_isPr]
    ring

/-- A word with one `Λ̃`, no resolvent and no paired letter. -/
private lemma FE_590_words (w : List FLet)
    (h : ((FLet.parts w).length - 1 = 1 && (FLet.parts w).sum = 0) = true)
    (hdet : (w.all fun z => match z with | .det _ pr => !pr | _ => true) = true) :
    ∃ u₁ u₂ : List FLet, w = u₁ ++ FLet.lamt :: u₂ ∧ (u₁ ++ u₂).all FLet.isDetE = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h0⟩ := h
  rw [FE_parts_len] at h1
  rw [FE_parts_sum] at h0
  obtain ⟨u₁, u₂, rfl, hu₁⟩ := FE_first w (by omega)
  obtain ⟨hc, -, hr⟩ := FE_split_counts u₁ u₂
  refine ⟨u₁, u₂, rfl, List.all_eq_true.2 fun z hz => ?_⟩
  have hz' : z ∈ u₁ ++ FLet.lamt :: u₂ := by
    rcases List.mem_append.1 hz with hz | hz
    · exact List.mem_append_left _ hz
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  have hd := List.all_eq_true.1 hdet z hz'
  have hnr : FO_isRes z = false := by
    by_contra hc'
    have : 0 < (u₁ ++ FLet.lamt :: u₂).countP FO_isRes :=
      List.countP_pos_iff.2 ⟨z, hz', by simpa using hc'⟩
    omega
  have hnl : z ≠ FLet.lamt := by
    rintro rfl
    rcases List.mem_append.1 hz with hz | hz
    · have : 0 < u₁.countP (· == FLet.lamt) := List.countP_pos_iff.2 ⟨_, hz, by simp⟩
      omega
    · have : 0 < u₂.countP (· == FLet.lamt) := List.countP_pos_iff.2 ⟨_, hz, by simp⟩
      omega
  cases z <;> simp_all [FO_isRes, FLet.isDetE]

/-! ### The menu, option by option -/

/-- The size of an option at the slots. -/
private abbrev FE_S (D N k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (o : FOpt) : ℝ :=
  (o.val.map fun m => m.evalR N (FE_M D N k ε) (etaK D N k ε) (hsNorm A) (opNorm A)).sum

/-- The letter is not a paired `𝔐_a - 𝔐_aᴴ`. -/
private def FE_isDetU : FLet → Bool
  | .det _ pr => !pr
  | _ => true

/-- The size `Im m` per paired letter of an entry. -/
private def FE_ext (w : List FLet) : FMono := ⟨0, 2 * ((w.countP FE_isPr : ℕ) : ℤ), 0, 0, 0⟩

/-- The letters `𝔐` of an entry are unpaired. -/
private def FE_det (w : List FLet) : Bool := w.all FE_isDetU

private lemma FE_entData (x y : ℕ) (w : List FLet) :
    (FFac.ent x y w).entData = some (x, y, FLet.parts w, FE_ext w, FE_det w) := by
  rw [(fentData_ent x y w).1]
  unfold FE_ext FE_det
  congr

private lemma FE_det_pr' (w : List FLet) (h : FE_det w = true) : w.countP FE_isPr = 0 := by
  rw [List.countP_eq_zero]
  intro z hz
  have := List.all_eq_true.1 h z hz
  cases z <;> simp_all [FE_isPr, FE_isDetU]

private lemma FE_pos (D N k : ℕ) (ε : ℝ) (hN : 1 ≤ N) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) :
    0 < FE_M D N k ε ∧ 0 < etaK D N k ε := by
  have hrk : (1 : ℝ) ≤ rk D N k := by
    unfold rk
    exact_mod_cast (show 1 ≤ min k (D * N + 1 - k) by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (by linarith) _),
    mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (by linarith) _)⟩

private lemma FE_OK_mono' {D : ℕ} {δA εA ε : ℝ} {C : ℕ → ℝ} {nb : ℕ}
    {Q Q' : (N : ℕ) → Matrix (Fin N) (Fin N) ℂ → ℕ → LoopEnv D N → (Fin nb → Fin D) →
      (Idx D N → Idx D N → ℂ) → ℝ → Prop}
    (hQ : ∀ N A k e ι h c, 1 ≤ N → 0 < FE_M D N k ε → 0 < etaK D N k ε → 0 ≤ c →
      Q N A k e ι h c → Q' N A k e ι h c)
    (h : FE_OK D δA εA ε C nb Q) : FE_OK D δA εA ε C nb Q' := by
  intro τ hτ D' hD'
  obtain ⟨Cst, hC, N₀, hN₀⟩ := h τ hτ D' hD'
  refine ⟨Cst, hC, max N₀ 1, fun N hN μ hμ A hA k hk hkN hhs e he ι => ?_⟩
  obtain ⟨bad, hbad, hg⟩ := hN₀ N (le_of_max_le_left hN) μ hμ A hA k hk hkN hhs e he ι
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  obtain ⟨hm, hη⟩ := FE_pos D N k ε hN1 hk hkN
  exact ⟨bad, hbad, fun h hh => hQ N A k e ι h _ hN1 hm hη (mul_nonneg hC
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hg h hh)⟩

private lemma FE_PC_mono {ι : Type*} [Fintype ι] {f : ι → ι → ℝ} {cx cy : ℕ} {B B' : ℝ}
    (hB : B ≤ B') (h : FE_PC f cx cy B) : FE_PC f cx cy B' := by
  obtain ⟨a, b, ha, hb, hab, h1⟩ := h
  exact ⟨a, b, ha, hb, hab, h1.trans hB⟩

private lemma FE_CC_mono {ι : Type*} [Fintype ι] {f : ι → ι → ℝ} {cy : ℕ} {B B' : ℝ}
    (hB : B ≤ B') (h : FE_CC f cy B) : FE_CC f cy B' := by
  obtain ⟨b, hb, hfb, h1⟩ := h
  exact ⟨b, hb, hfb, h1.trans hB⟩

private lemma FE_RC_mono {ι : Type*} [Fintype ι] {f : ι → ι → ℝ} {cx : ℕ} {B B' : ℝ}
    (hB : B ≤ B') (h : FE_RC f cx B) : FE_RC f cx B' := by
  obtain ⟨a, ha, hfa, h1⟩ := h
  exact ⟨a, ha, hfa, h1.trans hB⟩

/-- The options of a split at one `Λ̃`: plain, isotropic with the left half deterministic, or
with the right half deterministic. -/
private lemma FE_spl_cases (P : List ℕ) (k : ℕ) (left mx my : Bool) (o₀ : FOpt)
    (h : o₀ ∈ FO_spl P k left mx my) :
    o₀ = ⟨if mx then 1 else 0, if my then 1 else 0, 0,
      [(fhalf (if left then k + 1 else k) (P.take (k + 1)).sum mx).mul
        (fhalf (P.length - 1 - (if left then k + 1 else k)) (P.drop (k + 1)).sum my)]⟩ ∨
    ((P.take (k + 1)).sum = 0 ∧ o₀ = ⟨if mx then 1 else 0, if my then 1 else 0,
      if my then -1 else 0,
      [(fhalf (if left then k + 1 else k) 0 mx).mul
        ((if my then FMono.omega (P.drop (k + 1)).sum else FMono.psi (P.drop (k + 1)).sum).mul
          ⟨0, 0, 0, 0, P.length - 1 - (if left then k + 1 else k)⟩)]⟩) ∨
    ((P.drop (k + 1)).sum = 0 ∧ o₀ = ⟨if mx then 1 else 0, if my then 1 else 0,
      if mx then 1 else 0,
      [(fhalf (P.length - 1 - (if left then k + 1 else k)) 0 my).mul
        ((if mx then FMono.omega (P.take (k + 1)).sum else FMono.psi (P.take (k + 1)).sum).mul
          ⟨0, 0, 0, 0, if left then k + 1 else k⟩)]⟩) := by
  unfold FO_spl at h
  dsimp only at h
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  rcases List.mem_append.1 h with h | h
  · by_cases hr : (P.take (k + 1)).sum = 0
    · rw [ite_eq_left hr] at h
      exact Or.inr (Or.inl ⟨hr, List.mem_singleton.1 h⟩)
    · rw [ite_eq_right hr] at h
      simp at h
  · by_cases hr : (P.drop (k + 1)).sum = 0
    · rw [ite_eq_left hr] at h
      exact Or.inr (Or.inr ⟨hr, List.mem_singleton.1 h⟩)
    · rw [ite_eq_right hr] at h
      simp at h

/-- The options of `fopts2` after the four basic ones: (5.90), the double split, the splits. -/
private lemma FE_rest_cases (x y : ℕ) (P : List ℕ) (det : Bool) (o₀ : FOpt)
    (h : o₀ ∈ FO_rest x y P det) :
    ((P.length - 1 = 1 && P.sum = 0 && fsameBlk x y && det) = true ∧ ∃ mx my : Bool,
      o₀ = ⟨if mx then 1 else 0, if my then 1 else 0, 0, FE_l590 mx my⟩) ∨
    ((P.length - 1 = 2 && P.head? = some 0 && P.getLast? = some 0) = true ∧ ∃ mx my : Bool,
      o₀ = ⟨if mx then 1 else 0, if my then 1 else 0, 0,
        [(FMono.psi (P.getD 1 0)).mul ⟨0, 0, 0, (if mx then 1 else 0) + (if my then 1 else 0),
          (if mx then 0 else 1) + (if my then 0 else 1)⟩]⟩) ∨
    ∃ k < P.length - 1, ∃ left mx my : Bool, o₀ ∈ FO_spl P k left mx my := by
  unfold FO_rest at h
  dsimp only at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · split_ifs at h with hc
      · refine Or.inl ⟨hc, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl
        · exact ⟨false, false, rfl⟩
        · exact ⟨true, false, rfl⟩
        · exact ⟨false, true, rfl⟩
        · exact ⟨true, true, rfl⟩
      · simp at h
    · split_ifs at h with hc
      · refine Or.inr (Or.inl ⟨hc, ?_⟩)
        obtain ⟨mx, -, h⟩ := List.mem_flatMap.1 h
        obtain ⟨my, -, rfl⟩ := List.mem_map.1 h
        exact ⟨mx, my, rfl⟩
      · simp at h
  · obtain ⟨k, hk, h⟩ := List.mem_flatMap.1 h
    obtain ⟨left, -, h⟩ := List.mem_flatMap.1 h
    obtain ⟨mx, -, h⟩ := List.mem_flatMap.1 h
    obtain ⟨my, -, h⟩ := List.mem_flatMap.1 h
    exact Or.inr (Or.inr ⟨k, List.mem_range.1 hk, left, mx, my, h⟩)

set_option maxHeartbeats 1000000 in
-- the options after the four basic ones are treated in one proof
/-- Every option of `fopts2` after the four basic ones, with its size: (5.90) [eq:addoneLambda],
the double split and the splits at one `Λ̃` as bounds by a product (no order), the isotropic
splits with the deterministic half in `ℓ²` at the other label with the order they need. -/
private lemma FE_rest_all (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (w : List FLet) (o₀ : FOpt) (h : o₀ ∈ FO_rest x y (FLet.parts w) (FE_det w)) :
    (o₀.ord = 0 ∧ o₀.cx ≤ 1 ∧ o₀.cy ≤ 1 ∧ FE_OK D δA εA ε C nb fun N A k e ι h c =>
      FE_PC (FE_f x y ((w.map (FLet.mat e ι h)).prod)) o₀.cx o₀.cy
        (c * FE_S D N k ε A (FO_ext (FE_ext w) o₀))) ∨
    (o₀.ord = 1 ∧ o₀.cx = 1 ∧ FE_OK D δA εA ε C nb fun N A k e ι h c =>
      FE_CC (FE_f x y ((w.map (FLet.mat e ι h)).prod)) o₀.cy
        (c * FE_S D N k ε A (FO_ext (FE_ext w) o₀))) ∨
    (o₀.ord = -1 ∧ o₀.cy = 1 ∧ FE_OK D δA εA ε C nb fun N A k e ι h c =>
      FE_RC (FE_f x y ((w.map (FLet.mat e ι h)).prod)) o₀.cx
        (c * FE_S D N k ε A (FO_ext (FE_ext w) o₀))) := by
  have hb1 : ∀ b : Bool, (if b then 1 else 0 : ℕ) ≤ 1 := fun b => by cases b <;> simp
  rcases FE_rest_cases x y _ _ o₀ h with ⟨hc, mx, my, rfl⟩ | ⟨hc, mx, my, rfl⟩ |
    ⟨k, hk, left, mx, my, hs⟩
  · -- (5.90)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h0⟩, hfs⟩, hdet⟩ := hc
    have hdet' : (w.all fun z => match z with | .det _ pr => !pr | _ => true) = true := by
      rw [List.all_eq_true]
      intro z hz
      have := List.all_eq_true.1 hdet z hz
      cases z <;> simp_all [FE_isDetU]
    obtain ⟨u₁, u₂, hw, hu⟩ := FE_590_words w (by simp [h1, h0]) hdet'
    have hp := FE_det_pr' w hdet
    have K := FE_a590 D hD δA εA ε hδA hεA hε hε' hε'' C nb x y u₁ u₂ hu hfs
    rw [← hw] at K
    refine Or.inl ⟨rfl, hb1 mx, hb1 my, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
      FE_PC_mono (le_of_eq ?_) (hQ mx my)) K⟩
    congr 1
    simp only [FE_S, FE_ext]
    rw [FE_S_ext N _ _ _ _ hN hm hη, FE_ev_590 N _ _ _ _, hp, pow_zero, mul_one]
  · -- the double split
    obtain ⟨wX, wY, wZ, hw, hX, hZ, hXl, hYl, hZl, hYr, hp⟩ := FE_dbl_words w hc
    have K := FE_sand D hD δA εA ε hδA hεA hε hε' hε'' C nb x y wX wY wZ hX hZ
    rw [← hw] at K
    refine Or.inl ⟨rfl, hb1 mx, hb1 my, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
      FE_PC_mono (le_of_eq ?_) (hQ mx my)) K⟩
    congr 1
    simp only [FE_S, FE_ext]
    rw [FE_S_ext N _ _ _ _ hN hm hη, List.map_singleton, List.sum_singleton,
      FE_ev_dbl N _ _ _ _ hN hm hη, hXl, hYl, hZl, hYr, ← hp, pow_add, pow_add, pow_zero]
    ring
  · obtain ⟨wL, wR, hw, hnL, hnR, hrL, hrR, hp⟩ := FE_spl_words w k hk left
    rcases FE_spl_cases _ _ _ _ _ _ hs with rfl | ⟨hr0, rfl⟩ | ⟨hr0, rfl⟩
    · -- the plain split
      have K := FE_plain D hD δA εA ε hδA hεA hε hε' hε'' C nb x y wL wR
      rw [← hw] at K
      refine Or.inl ⟨rfl, hb1 mx, hb1 my, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
        FE_PC_mono (le_of_eq ?_) (hQ mx my)) K⟩
      congr 1
      simp only [FE_S, FE_ext]
      rw [FE_S_ext N _ _ _ _ hN hm hη, List.map_singleton, List.sum_singleton,
        FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN,
        FE_ev_half N _ _ _ _ hm hη hN, hnL, hnR, hrL, hrR, ← hp, pow_add]
      ring
    · -- the left half deterministic
      have hXr : wL.countP FO_isRes = 0 := hrL.trans hr0
      cases my
      · have K := FE_sand D hD δA εA ε hδA hεA hε hε' hε'' C nb x y wL wR [] hXr rfl
        rw [List.append_nil, ← hw] at K
        refine Or.inl ⟨rfl, hb1 mx, hb1 false, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
          FE_PC_mono (le_of_eq ?_) (hQ mx false)) K⟩
        congr 1
        simp only [FE_S, FE_ext, Bool.false_eq_true, ↓reduceIte]
        rw [FE_S_ext N _ _ _ _ hN hm hη, List.map_singleton, List.sum_singleton,
          FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN,
          FE_ev_iso N _ _ _ _ hN hm hη, hnL, hnR, hrR, ← hp, pow_add]
        simp only [List.countP_nil, FE_half, FE_om_zero, Bool.false_eq_true, ↓reduceIte, pow_zero]
        ring
      · have K := FE_rowL D hD δA εA ε hδA hεA hε hε' hε'' C nb x y wL wR hXr
        rw [← hw] at K
        refine Or.inr (Or.inr ⟨rfl, rfl, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
          FE_RC_mono (le_of_eq ?_) (hQ mx)) K⟩)
        congr 1
        simp only [FE_S, FE_ext, ↓reduceIte]
        rw [FE_S_ext N _ _ _ _ hN hm hη, List.map_singleton, List.sum_singleton,
          FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN,
          FE_ev_row N _ _ _ _ hN hm hη, hnL, hnR, hrR, ← hp, pow_add]
        ring
    · -- the right half deterministic
      have hZr : wR.countP FO_isRes = 0 := hrR.trans hr0
      cases mx
      · have K := FE_sand D hD δA εA ε hδA hεA hε hε' hε'' C nb x y [] wL wR rfl hZr
        rw [List.nil_append, ← hw] at K
        refine Or.inl ⟨rfl, hb1 false, hb1 my, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
          FE_PC_mono (le_of_eq ?_) (hQ false my)) K⟩
        congr 1
        simp only [FE_S, FE_ext, Bool.false_eq_true, ↓reduceIte]
        rw [FE_S_ext N _ _ _ _ hN hm hη, List.map_singleton, List.sum_singleton,
          FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN,
          FE_ev_iso N _ _ _ _ hN hm hη, hnL, hnR, hrL, ← hp, pow_add]
        simp only [List.countP_nil, FE_half, FE_om_zero, Bool.false_eq_true, ↓reduceIte, pow_zero]
        ring
      · have K := FE_colR D hD δA εA ε hδA hεA hε hε' hε'' C nb x y wL wR hZr
        rw [← hw] at K
        refine Or.inr (Or.inl ⟨rfl, rfl, FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
          FE_CC_mono (le_of_eq ?_) (hQ my)) K⟩)
        congr 1
        simp only [FE_S, FE_ext, ↓reduceIte]
        rw [FE_S_ext N _ _ _ _ hN hm hη, List.map_singleton, List.sum_singleton,
          FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN,
          FE_ev_row N _ _ _ _ hN hm hη, hnL, hnR, hrL, ← hp, pow_add]
        ring

set_option maxHeartbeats 1000000 in
-- the options of the menu are treated in one proof
/-- Every option of `fopts` of an entry, off one event: the norm `foptNorm` of the entry (`0`
across blocks for labels of one block) is at most `Cst N^τ` times the size of the option. -/
private lemma FE_main (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb x y : ℕ)
    (w : List FLet) (o : FOpt) (ho : o ∈ fopts x y (FLet.parts w) (FE_ext w) (FE_det w))
    (rf : Bool) (hord : (o.ord = 1 → rf = true) ∧ (o.ord = -1 → rf = false)) :
    FE_OK D δA εA ε C nb fun N A k e ι h c =>
      foptNorm (decide (x = y)) o rf (FE_f x y ((w.map (FLet.mat e ι h)).prod)) ≤
        c * FE_S D N k ε A o := by
  have hf0 : ∀ {N : ℕ} (W : Matrix (Idx D N) (Idx D N) ℂ), ∀ x' y', 0 ≤ FE_f x y W x' y' :=
    fun W x' y' => FE_f_nonneg x y W x' y'
  have KB := FE_base D hD δA εA ε hδA hεA hε hε' hε'' C nb x y w
  have hlen : (FLet.parts w).length - 1 = w.countP (· == .lamt) := by
    rw [FE_parts_len]; omega
  have hsum := FE_parts_sum w
  by_cases hxy : x = y
  · subst hxy
    simp only [decide_true]
    unfold fopts at ho
    rw [ite_eq_left rfl] at ho
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_filterMap] at ho
    rcases ho with (rfl | rfl) | ⟨a, ha, hao⟩
    · refine FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => ?_) KB
      obtain ⟨hiso, -, -, -⟩ := hQ
      refine (FE_PC_diag 0 0 (by norm_num) (by norm_num) _ rf _ _ (hf0 _) hiso).trans
        (le_of_eq ?_)
      congr 1
      simp only [FE_S, List.map_singleton, List.sum_singleton]
      rw [FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_iso N _ _ _ _ hN hm hη, FE_ext, FE_ev_ext,
        hlen, hsum]
      ring
    · refine FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => ?_) KB
      obtain ⟨-, -, -, hhs⟩ := hQ
      refine FE_opt_diag_hs _ rf _ _ (hhs.trans (le_of_eq ?_))
      congr 1
      simp only [FE_S, List.map_singleton, List.sum_singleton]
      rw [FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN, FE_ext, FE_ev_ext,
        hlen, hsum]
    · have hd : ∀ (a b c e : FOpt) (l : List FOpt), List.drop 4 ([a, b, c, e] ++ l) = l :=
        fun _ _ _ _ _ => rfl
      rw [FO_fopts2, ← List.map_drop, hd] at ha
      obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ha
      have hord' : (FO_ext (FE_ext w) o₀).ord = o₀.ord := rfl
      by_cases hord0 : o₀.ord = 0
      · rw [ite_eq_right (by rw [hord', hord0]; simp)] at hao
        obtain rfl := Option.some.inj hao
        rcases FE_rest_all D hD δA εA ε hδA hεA hε hε' hε'' C nb x x w o₀ ho₀ with
          ⟨-, hcx, hcy, K⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · exact FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
            FE_PC_diag o₀.cx o₀.cy hcx hcy _ rf _ _ (hf0 _) hQ) K
        · rw [h1] at hord0; exact absurd hord0 (by decide)
        · rw [h1] at hord0; exact absurd hord0 (by decide)
      · rw [ite_eq_left (by rw [hord']; exact hord0)] at hao
        exact absurd hao (by simp)
  · have hdec : decide (x = y) = false := decide_eq_false hxy
    rw [hdec]
    unfold fopts at ho
    rw [ite_eq_right hxy, FO_fopts2] at ho
    obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ho
    rcases List.mem_append.1 ho₀ with hb | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · refine FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => ?_) KB
        obtain ⟨hiso, -, -, -⟩ := hQ
        refine FE_PC_opt _ rf _ _ (hf0 _) (FE_PC_mono (le_of_eq ?_) hiso)
        congr 1
        simp only [FE_S, FO_ext, List.map_singleton, List.sum_singleton]
        rw [FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_iso N _ _ _ _ hN hm hη, FE_ext, FE_ev_ext,
          hlen, hsum]
        ring
      · have hrf : rf = true := hord.1 rfl
        subst hrf
        refine FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => ?_) KB
        obtain ⟨-, hcc, -, -⟩ := hQ
        refine FE_CC_opt _ rfl _ _ (FE_CC_mono (le_of_eq ?_) hcc)
        congr 1
        simp only [FE_S, FO_ext, List.map_singleton, List.sum_singleton]
        rw [FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_row N _ _ _ _ hN hm hη, FE_ext, FE_ev_ext,
          hlen, hsum]
        ring
      · have hrf : rf = false := hord.2 rfl
        subst hrf
        refine FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => ?_) KB
        obtain ⟨-, -, hrc, -⟩ := hQ
        refine FE_RC_opt _ rfl _ _ (FE_RC_mono (le_of_eq ?_) hrc)
        congr 1
        simp only [FE_S, FO_ext, List.map_singleton, List.sum_singleton]
        rw [FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_row N _ _ _ _ hN hm hη, FE_ext, FE_ev_ext,
          hlen, hsum]
        ring
      · refine FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => ?_) KB
        obtain ⟨-, -, -, hhs⟩ := hQ
        refine FE_opt_hs _ rfl rfl rf _ _ (hhs.trans (le_of_eq ?_))
        congr 1
        simp only [FE_S, FO_ext, List.map_singleton, List.sum_singleton]
        rw [FO_evalR_mul _ _ N hN _ _ _ _ hm hη, FE_ev_half N _ _ _ _ hm hη hN, FE_ext, FE_ev_ext,
          hlen, hsum]
    · rcases FE_rest_all D hD δA εA ε hδA hεA hε hε' hε'' C nb x y w o₀ hr with
        ⟨-, -, -, K⟩ | ⟨h1, hcx, K⟩ | ⟨h1, hcy, K⟩
      · exact FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ =>
          FE_PC_opt _ rf _ _ (hf0 _) hQ) K
      · have hrf : rf = true := hord.1 h1
        subst hrf
        exact FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => FE_CC_opt _ hcx _ _ hQ) K
      · have hrf : rf = false := hord.2 h1
        subst hrf
        exact FE_OK_mono' (fun N A k e ι h c hN hm hη _ hQ => FE_RC_opt _ hcy _ _ hQ) K

/-- The sizes of the options are nonnegative at the slots. -/
private lemma FE_S_nonneg (D N k : ℕ) (ε : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (o : FOpt) :
    0 ≤ FE_S D N k ε A o := by
  have hrk : (0 : ℝ) ≤ rk D N k := by unfold rk; positivity
  refine List.sum_nonneg fun z hz => ?_
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hz
  exact FO_evalR_nonneg m N (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hrk _)) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hrk _)) (Real.sqrt_nonneg _) (Bd_opNorm_nonneg A)

/-- The value of one option of an entry without `Λ̃` in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law]
and 5.4 [lemma_localized_eigenvalue_local_law], outside an event of probability `≤ N^{-D'}`, the
norm `foptNorm` of the entry, restricted to one block for labels of one block, is at most `N^{τ'}`
times the size of the option (isotropic (A.53) [entprodG], a Ward row or column, the
Hilbert–Schmidt norm), with `Im m` per paired letter. -/
theorem pkg_fopt_free (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (x y : ℕ)
    (w : List FLet) (hw : FLet.lamt ∉ w) (d : ℕ × ℕ × List ℕ × FMono × Bool)
    (hd : (FFac.ent x y w).entData = some d) (o : FOpt)
    (ho : o ∈ fopts d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2) (rowFirst : Bool)
    (hord : (o.ord = 1 → rowFirst = true) ∧ (o.ord = -1 → rowFirst = false)) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ ι : Fin nb → Fin D,
        μ {h | (N : ℝ) ^ τ' * (o.val.map fun m => m.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A)).sum <
          foptNorm (decide (x = y)) o rowFirst (fun x' y' : Idx D N =>
            if fsameBlk x y = true ∧ x'.1 ≠ y'.1 then 0
            else ‖((w.map (FLet.mat e ι h)).prod) x' y'‖)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain rfl : d = (x, y, FLet.parts w, FE_ext w, FE_det w) := by
    rw [FE_entData] at hd
    exact (Option.some.inj hd).symm
  exact FE_absorb (fun N A k e ι h => foptNorm (decide (x = y)) o rowFirst
      (FE_f x y ((w.map (FLet.mat e ι h)).prod))) (fun N A k => FE_S D N k ε A o)
    (fun N A k => FE_S_nonneg D N k ε A o)
    (FE_main D hD δA εA ε hδA hεA hε hε' hε'' C nb x y w o ho rowFirst hord)

/-- The value of one option of an entry in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
`pkg_fopt_free` for every entry, with the options of the entries with `Λ̃` ((5.90)
[eq:addoneLambda] in one block, the double split at both `Λ̃`, the splits at one `Λ̃` with each
half in sup or `ℓ²`, isotropic when one half is deterministic; (5.68) [bound_factors]–(5.71)
[Cauchy_example_2]). -/
theorem pkg_fopt_good (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (nb : ℕ) (x y : ℕ)
    (w : List FLet) (d : ℕ × ℕ × List ℕ × FMono × Bool)
    (hd : (FFac.ent x y w).entData = some d) (o : FOpt)
    (ho : o ∈ fopts d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2) (rowFirst : Bool)
    (hord : (o.ord = 1 → rowFirst = true) ∧ (o.ord = -1 → rowFirst = false)) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ ι : Fin nb → Fin D,
        μ {h | (N : ℝ) ^ τ' * (o.val.map fun m => m.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A)).sum <
          foptNorm (decide (x = y)) o rowFirst (fun x' y' : Idx D N =>
            if fsameBlk x y = true ∧ x'.1 ≠ y'.1 then 0
            else ‖((w.map (FLet.mat e ι h)).prod) x' y'‖)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  by_cases hw : FLet.lamt ∈ w
  · obtain rfl : d = (x, y, FLet.parts w, FE_ext w, FE_det w) := by
      rw [FE_entData] at hd
      exact (Option.some.inj hd).symm
    exact FE_absorb (fun N A k e ι h => foptNorm (decide (x = y)) o rowFirst
        (FE_f x y ((w.map (FLet.mat e ι h)).prod))) (fun N A k => FE_S D N k ε A o)
      (fun N A k => FE_S_nonneg D N k ε A o)
      (FE_main D hD δA εA ε hδA hεA hε hε' hε'' C nb x y w o ho rowFirst hord)
  · exact pkg_fopt_free D hD δA εA ε hδA hεA hε hε' hε'' C nb x y w hw d hd o ho rowFirst hord

end RBMTransitionEdge

end
