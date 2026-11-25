module

public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.LocalLaw.MultiRes
import all RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.LocalLaw.MultiRes

@[expose] public section

/-!
# The factor bounds of the further expansion

(A.53) [entprodG], (A.54) [one_loop_estimate] and (A.55) [two_loop_estimate] of Lemma A.4
[lemma_necessary_estimates] at slots satisfying its hypotheses, uniformly in the member of the
class and in the slots, and the step from a bound with high probability to a bound in expectation.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private Bd_Cl Bd_zc Bd_one_unif Bd_two_unif Bd_ent_unif Bd_avgSq_nonneg Bd_ofFn_smul
  Bd_opNorm_nonneg Bd_opNorm_one Bd_opNorm_conjTranspose from RBMTransitionEdge.Localized.Expansion.Bound
open private PB_iso_unif from RBMTransitionEdge.Localized.Expansion.PkgBound
open private MultiRes_vn MultiRes_vn_sq MultiRes_vn_nonneg MultiRes_vn_smul MultiRes_vn_eq_zero
  MultiRes_vn_mulVec_le MultiRes_vn_of_sum from RBMTransitionEdge.LocalLaw.MultiRes

/-! ## Facts on the products of Lemma A.4 [lemma_necessary_estimates] -/

section Facts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix of operator norm `≤ 0` is zero. -/
private lemma FB_eq_zero (X : Matrix ι ι ℂ) (h : opNorm X ≤ 0) : X = 0 := by
  have h0 : opNorm X = 0 := le_antisymm h (Bd_opNorm_nonneg X)
  unfold opNorm at h0
  rw [norm_eq_zero] at h0
  exact (map_eq_zero_iff (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (EquivLike.injective _)).1 h0

omit [DecidableEq ι] in
/-- `⟨r X⟩ = r ⟨X⟩`. -/
private lemma FB_ntr_smul (r : ℂ) (X : Matrix ι ι ℂ) : ntr (r • X) = r * ntr X := by
  unfold ntr
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

omit [DecidableEq ι] in
/-- `⟨0⟩ = 0`. -/
private lemma FB_ntr_zero : ntr (0 : Matrix ι ι ℂ) = 0 := by
  unfold ntr
  simp

/-- A product `Π_l` whose first factor `B₀` vanishes is zero. -/
private lemma FB_resWord_zero {p l : ℕ} (G : Fin p → Matrix ι ι ℂ) (w : Fin l → Fin p × Bool)
    (B : Fin (l + 1) → Matrix ι ι ℂ) (h : B 0 = 0) : resWord G w B = 0 := by
  unfold resWord
  rw [h, Matrix.zero_mul]

/-- `Π_l` is linear in each of its `l + 1` deterministic factors. -/
private lemma FB_resWord_smul {p l : ℕ} (G : Fin p → Matrix ι ι ℂ) (w : Fin l → Fin p × Bool)
    (B : Fin (l + 1) → Matrix ι ι ℂ) (r : ℂ) :
    resWord G w (fun j => r • B j) = r ^ (l + 1) • resWord G w B := by
  unfold resWord
  have h := Bd_ofFn_smul (fun j : Fin l => if (w j).2 then (G (w j).1)ᴴ else G (w j).1)
    (fun j => B j.succ) r
  simp only at h ⊢
  rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ, mul_comm]

/-- `Π_l(B) = K^{l+1} Π_l(B / K)` for `K ≠ 0`. -/
private lemma FB_resWord_unscale {p l : ℕ} (G : Fin p → Matrix ι ι ℂ) (w : Fin l → Fin p × Bool)
    (B : Fin (l + 1) → Matrix ι ι ℂ) (K : ℝ) (hK : K ≠ 0) :
    resWord G w B = ((K : ℝ) : ℂ) ^ (l + 1) • resWord G w (fun j => ((K⁻¹ : ℝ) : ℂ) • B j) := by
  rw [FB_resWord_smul, smul_smul, ← mul_pow, ← Complex.ofReal_mul, mul_inv_cancel₀ hK,
    Complex.ofReal_one, one_pow, one_smul]

/-- `‖B / K‖ ≤ 1` when `‖B‖ ≤ K`, `K > 0`. -/
private lemma FB_unscale_norm (X : Matrix ι ι ℂ) (K : ℝ) (hK : 0 < K) (h : opNorm X ≤ K) :
    opNorm (((K⁻¹ : ℝ) : ℂ) • X) ≤ 1 := by
  rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK),
    inv_mul_le_iff₀ hK, mul_one]
  exact h

/-- Moving the last factor `Z` into the last deterministic factor of a product. -/
private lemma FB_prod_snoc {n : ℕ} (X Y : Fin (n + 1) → Matrix ι ι ℂ) (Z : Matrix ι ι ℂ) :
    (List.ofFn fun i => X i * (if i = Fin.last n then Y i * Z else Y i)).prod =
      (List.ofFn fun i => X i * Y i).prod * Z := by
  rw [List.ofFn_succ', List.ofFn_succ' (fun i => X i * Y i), List.concat_eq_append,
    List.concat_eq_append, List.prod_append, List.prod_append]
  simp [Fin.castSucc_ne_last, Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- `(X^* u)^* (Y v) = u^* (X Y) v`. -/
private lemma FB_dot (X Y : Matrix ι ι ℂ) (u v : ι → ℂ) :
    star (Xᴴ *ᵥ u) ⬝ᵥ (Y *ᵥ v) = star u ⬝ᵥ ((X * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

end Facts

/-- If `t K b < K y` with `K > 0`, then `t b < y`. -/
private lemma FB_lt_of_scaled (t k b y : ℝ) (hk : 0 < k) (h : t * (k * b) < k * y) : t * b < y := by
  have : k * (t * b) < k * y := by linarith [show t * (k * b) = k * (t * b) by ring]
  exact lt_of_mul_lt_mul_left this hk.le

/-- `(Im m)^{1(l ≥ 2)} η^{1-l}` over the slots `σ i` is at most the same over both slots, for
positive `Im m_a` and `η_a`. -/
private lemma FB_bndA4_le {p : ℕ} [Nonempty (Fin p)] (σ : Fin p → Fin 2) (imm eta : Fin 2 → ℝ)
    (him : ∀ a, 0 < imm a) (het : ∀ a, 0 < eta a) (l : ℕ) :
    bndA4 (fun i => imm (σ i)) (fun i => eta (σ i)) l ≤ bndA4 imm eta l := by
  unfold bndA4
  have hnum : (if 2 ≤ l then ⨆ i, imm (σ i) else 1) ≤ (if 2 ≤ l then ⨆ a, imm a else 1) := by
    split_ifs
    · exact ciSup_le fun i => le_ciSup (Set.finite_range _).bddAbove (σ i)
    · exact le_rfl
  have hnum0 : 0 ≤ (if 2 ≤ l then ⨆ a, imm a else 1) := by
    split_ifs
    · exact (him 0).le.trans (le_ciSup (Set.finite_range _).bddAbove 0)
    · exact zero_le_one
  have hden : ⨅ a, eta a ≤ ⨅ i, eta (σ i) :=
    le_ciInf fun i => ciInf_le (Set.finite_range _).bddBelow (σ i)
  obtain ⟨a, ha⟩ := exists_eq_ciInf_of_finite (f := eta)
  have hden0 : 0 < ⨅ a, eta a := ha ▸ het a
  exact div_le_div₀ hnum0 hnum (pow_pos hden0 _) (pow_le_pow_left₀ hden0.le hden _)

/-- `(Im m)^{1(l ≥ 2)} η^{1-l} ≥ 0` for positive `Im m_a` and `η_a`. -/
private lemma FB_bndA4_nonneg (imm eta : Fin 2 → ℝ) (him : ∀ a, 0 < imm a)
    (het : ∀ a, 0 < eta a) (l : ℕ) : 0 ≤ bndA4 imm eta l := by
  unfold bndA4
  obtain ⟨a, ha⟩ := exists_eq_ciInf_of_finite (f := eta)
  have hden0 : 0 < ⨅ a, eta a := ha ▸ het a
  refine div_nonneg ?_ (pow_pos hden0 _).le
  split_ifs
  · exact (him 0).le.trans (le_ciSup (Set.finite_range _).bddAbove 0)
  · exact zero_le_one

/-- `Im m_a > 0` from `c₀ ≤ N η_a Im m_a`, `c₀ > 0`, `η_a > 0`. -/
private lemma FB_imm_pos (N : ℕ) (η m c₀ : ℝ) (hc₀ : 0 < c₀) (hη : 0 < η) (h : c₀ ≤ N * η * m) :
    0 < m := by
  by_contra hm
  push Not at hm
  have : (N : ℝ) * η * m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Nat.cast_nonneg _) hη.le) hm
  linarith

/-- (A.53) [entprodG] of Lemma A.4 [lemma_necessary_estimates] at slots satisfying its
hypotheses, uniformly in the member of the class and the slots: a product of `l ≥ 1` resolvents
and deterministic factors of norm `≤ K`, averaged and between unit vectors, is
`≤ N^{τ'} K^{l+1} (Im m)^{1(l ≥ 2)} η^{1-l}` outside an event of probability `≤ N^{-D'}`. -/
theorem fb_word (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (l : ℕ) (hl : 1 ≤ l) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
        c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) →
      ∀ (w : Fin l → Fin 2 × Bool) (B : Fin (l + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B j) ≤ K) →
        μ {h | (N : ℝ) ^ τ' * (K ^ (l + 1) *
              bndA4 (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im)
                (fun a => (e.z a).im) l) <
            ‖ntr (resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))
              w B)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
          μ {h | (N : ℝ) ^ τ' * (K ^ (l + 1) *
                bndA4 (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im)
                  (fun a => (e.z a).im) l) <
              ‖star u ⬝ᵥ (resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A)
                (e.z a)) w B *ᵥ v)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  intro τ' hτ' D' hD'
  rcases le_or_gt K 0 with hK | hK
  · refine ⟨0, fun N _ μ _ e _ _ _ _ w B hB => ?_⟩
    have hK0 : K = 0 := le_antisymm hK ((Bd_opNorm_nonneg (B 0)).trans (hB 0))
    have hB0 : B 0 = 0 := FB_eq_zero _ (hK0 ▸ hB 0)
    refine ⟨le_trans (measure_mono (t := ∅) fun h hh => ?_) (by simp),
      fun u v _ _ => le_trans (measure_mono (t := ∅) fun h hh => ?_) (by simp)⟩
    · simp only [Set.mem_ofPred_eq, FB_resWord_zero _ _ _ hB0, FB_ntr_zero, norm_zero, hK0,
        zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero, lt_irrefl] at hh
    · simp only [Set.mem_ofPred_eq, FB_resWord_zero _ _ _ hB0, Matrix.zero_mulVec,
        dotProduct_zero, norm_zero, hK0, zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero,
        lt_irrefl] at hh
  · have hE := Filter.eventually_all.2 fun σ : Fin (n + 1) → Fin 2 =>
      Bd_ent_unif D (by omega) (n + 1) (by omega) σ δA τ c₀ C₀ 0 hδA hτ hc₀ hC₀ C τ' hτ' D' hD'
    have hI := Filter.eventually_all.2 fun σ : Fin (n + 1) → Fin 2 =>
      PB_iso_unif D (by omega) (n + 1) (by omega) σ δA τ c₀ C₀ 0 hδA hτ hc₀ hC₀ C τ' hτ' D' hD'
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hE.and hI)
    refine ⟨N₀, fun N hN μ hμ e hA hA' hc hz w B hB => ?_⟩
    obtain ⟨hEN, hIN⟩ := hN₀ N hN
    have hx : (μ, ({ e with δ := 0 } : LoopEnv D N)) ∈ Bd_Cl D δA C₀ 0 C N :=
      ⟨hμ, hA, hA', hc, by simp⟩
    set σ : Fin (n + 1) → Fin 2 := fun j => (w j).1 with hσ
    set s : Fin (n + 1) → Bool := fun j => (w j).2 with hs
    set B' : Fin (n + 1 + 1) → Matrix (Idx D N) (Idx D N) ℂ :=
      fun j => ((K⁻¹ : ℝ) : ℂ) • B j with hB'def
    have hB' : ∀ j, opNorm (B' j) ≤ 1 := fun j => FB_unscale_norm _ K hK (hB j)
    set Bs : Fin (n + 1) → Matrix (Idx D N) (Idx D N) ℂ := fun i => B' i.succ with hBs
    set Bc : Fin (n + 1) → Matrix (Idx D N) (Idx D N) ℂ :=
      fun i => if i = Fin.last n then B' i.succ * B' 0 else B' i.succ with hBc
    have hBsn : ∀ i, opNorm (Bs i) ≤ 1 := fun i => hB' _
    have hBcn : ∀ i, opNorm (Bc i) ≤ 1 := by
      intro i
      simp only [hBc]
      split_ifs
      · refine (opNorm_mul_le _ _).trans ?_
        have h1 := hB' i.succ
        have h2 := hB' 0
        have h3 := Bd_opNorm_nonneg (B' i.succ)
        have h4 := Bd_opNorm_nonneg (B' 0)
        nlinarith
      · exact hB' _
    have himm : ∀ a, 0 < (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im := fun a =>
      FB_imm_pos N _ _ c₀ hc₀ (hz a).2.1 (hz a).2.2
    have hcmp := FB_bndA4_le σ (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im)
      (fun a => (e.z a).im) himm (fun a => (hz a).2.1) (n + 1)
    have hnn := FB_bndA4_nonneg (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im)
      (fun a => (e.z a).im) himm (fun a => (hz a).2.1) (n + 1)
    have hNτ : 0 ≤ (N : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hKp : 0 < K ^ (n + 1 + 1) := pow_pos hK _
    have hW : ∀ h : Idx D N → Idx D N → ℂ,
        resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a)) w B =
          ((K : ℝ) : ℂ) ^ (n + 1 + 1) • (B' 0 * resProd (fun i => res (Matrix.of h +
            (e.c (σ i) : ℂ) • lam D N e.A) (e.z (σ i))) s Bs) := fun h => by
      rw [FB_resWord_unscale _ w B K hK.ne']
      rfl
    have hC : ∀ h : Idx D N → Idx D N → ℂ,
        resProd (fun i => res (Matrix.of h + (e.c (σ i) : ℂ) • lam D N e.A) (e.z (σ i))) s Bs *
          B' 0 =
        resProd (fun i => res (Matrix.of h + (e.c (σ i) : ℂ) • lam D N e.A) (e.z (σ i))) s Bc :=
      fun h => by
        unfold resProd
        exact (FB_prod_snoc _ _ _).symm
    refine ⟨le_trans (measure_mono fun h hh => ?_) (hEN σ _ hx hz s Bc hBcn),
      fun u v hu hv => ?_⟩
    · simp only [Set.mem_ofPred_eq] at hh
      rw [hW h, FB_ntr_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hK, ntr, Matrix.trace_mul_comm, ← ntr, hC h] at hh
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcmp hNτ)
        (FB_lt_of_scaled _ _ _ _ hKp hh)
    · set u0 : Idx D N → ℂ := (B' 0)ᴴ *ᵥ u with hu0
      have hval : ∀ h : Idx D N → Idx D N → ℂ,
          star u ⬝ᵥ (resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))
            w B *ᵥ v) =
          ((K : ℝ) : ℂ) ^ (n + 1 + 1) * (star u0 ⬝ᵥ (resProd (fun i => res (Matrix.of h +
            (e.c (σ i) : ℂ) • lam D N e.A) (e.z (σ i))) s Bs *ᵥ v)) := fun h => by
        rw [hW h, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hu0, FB_dot]
      have hvu : MultiRes_vn u = 1 := MultiRes_vn_of_sum u hu
      have hu0n : MultiRes_vn u0 ≤ 1 := by
        refine (MultiRes_vn_mulVec_le _ _).trans ?_
        rw [hvu, mul_one, Bd_opNorm_conjTranspose]
        exact hB' 0
      by_cases hz0 : MultiRes_vn u0 = 0
      · have hu0' : u0 = 0 := MultiRes_vn_eq_zero hz0
        refine le_trans (measure_mono (t := ∅) fun h hh => ?_) (by simp)
        simp only [Set.mem_ofPred_eq] at hh
        rw [hval h, hu0', star_zero, zero_dotProduct, mul_zero, norm_zero] at hh
        exact absurd hh (not_lt.2 (mul_nonneg hNτ (mul_nonneg hKp.le hnn)))
      · have hu0p : 0 < MultiRes_vn u0 := lt_of_le_of_ne (MultiRes_vn_nonneg _) (Ne.symm hz0)
        set uh : Idx D N → ℂ := (((MultiRes_vn u0)⁻¹ : ℝ) : ℂ) • u0 with huh
        have huh1 : ∑ y, ‖uh y‖ ^ 2 = 1 := by
          rw [← MultiRes_vn_sq, huh, MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hu0p), inv_mul_cancel₀ hz0, one_pow]
        have hstar : star u0 = ((MultiRes_vn u0 : ℝ) : ℂ) • star uh := by
          rw [huh, star_smul, Complex.star_def, Complex.conj_ofReal, smul_smul,
            ← Complex.ofReal_mul, mul_inv_cancel₀ hz0, Complex.ofReal_one, one_smul]
        refine le_trans (measure_mono fun h hh => ?_) (hIN σ _ hx hz s Bs hBsn uh v huh1 hv)
        simp only [Set.mem_ofPred_eq] at hh
        rw [hval h, hstar, smul_dotProduct, smul_eq_mul, norm_mul, norm_mul, norm_pow,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hK, abs_of_pos hu0p] at hh
        have hle : K ^ (n + 1 + 1) * (MultiRes_vn u0 *
            ‖star uh ⬝ᵥ (resProd (fun i => res (Matrix.of h + (e.c (σ i) : ℂ) • lam D N e.A)
              (e.z (σ i))) s Bs *ᵥ v)‖) ≤
            K ^ (n + 1 + 1) * ‖star uh ⬝ᵥ (resProd (fun i => res (Matrix.of h +
              (e.c (σ i) : ℂ) • lam D N e.A) (e.z (σ i))) s Bs *ᵥ v)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hKp.le
          exact mul_le_of_le_one_left (norm_nonneg _) hu0n
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcmp hNτ)
          (FB_lt_of_scaled _ _ _ _ hKp (hh.trans_le hle))

/-- (A.54) [one_loop_estimate] of Lemma A.4 [lemma_necessary_estimates] at slots satisfying its
hypotheses, uniformly in the member of the class and the slots: a loop `⟨Π_l Λ̃⟩` with `l ≥ 1`
resolvents is `≤ N^{τ'} K^{l+1} N^{-1/2} ‖Λ‖_HS (Im m)^{1(l ≥ 2)} η^{1-l}` outside an event of
probability `≤ N^{-D'}`. -/
theorem fb_lam_loop (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (l : ℕ) (hl : 1 ≤ l) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
        c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
      ∀ (w : Fin l → Fin 2 × Bool) (B : Fin (l + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B j) ≤ K) →
        μ {h | (N : ℝ) ^ τ' * (K ^ (l + 1) * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N e.A) *
              bndA4 (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im)
                (fun a => (e.z a).im) l)) <
            ‖ntr (resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))
              w B * e.Lt)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  rcases le_or_gt K 0 with hK | hK
  · refine ⟨0, fun N _ μ _ e _ _ _ _ _ w B hB => ?_⟩
    have hK0 : K = 0 := le_antisymm hK ((Bd_opNorm_nonneg (B 0)).trans (hB 0))
    have hB0 : B 0 = 0 := FB_eq_zero _ (hK0 ▸ hB 0)
    refine le_trans (measure_mono (t := ∅) fun h hh => ?_) (by simp)
    simp only [Set.mem_ofPred_eq, FB_resWord_zero _ _ _ hB0, FB_ntr_zero,
      norm_zero, hK0, zero_pow (Nat.succ_ne_zero l), zero_mul, mul_zero, lt_irrefl] at hh
  · obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
      (Bd_one_unif D (by omega) l hl δA τ c₀ C₀ (max K 1) hδA hτ hc₀ hC₀ C τ' hτ' D' hD')
    refine ⟨N₀, fun N hN μ hμ e hA hA' hc hz hδ w B hB => ?_⟩
    have hx : (μ, e) ∈ Bd_Cl D δA C₀ (max K 1) C N :=
      ⟨hμ, hA, hA', hc, hδ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Bd_avgSq_nonneg _ (lam_isHermitian D N _)))⟩
    have h1 := hN₀ N hN (μ, e) hx hz w (fun j => ((K⁻¹ : ℝ) : ℂ) • B j)
      (fun j => (FB_unscale_norm _ K hK (hB j)).trans (le_max_right _ _))
    refine le_trans (measure_mono fun h hh => ?_) h1
    simp only [Set.mem_ofPred_eq] at hh ⊢
    rw [FB_resWord_unscale _ w B K hK.ne', Matrix.smul_mul, FB_ntr_smul, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK] at hh
    exact FB_lt_of_scaled _ _ _ _ (pow_pos hK _) hh

/-- (A.55) [two_loop_estimate] of Lemma A.4 [lemma_necessary_estimates] at slots satisfying its
hypotheses, uniformly in the member of the class and the slots: a loop `⟨Π_{l₁} Λ̃ Π_{l₂} Λ̃⟩` with
`l₁ + l₂ ≥ 1` resolvents is `≤ N^{τ'} K^{l₁+l₂+2} N^{-1} ‖Λ‖²_HS (Im m)^{1(l₁+l₂ ≥ 2)}
η^{1-l₁-l₂}` outside an event of probability `≤ N^{-D'}`; with `Π_{l₂} = 1` it gives the sums
`Σ_⋆ ‖e_⋆ᵀ Π Λ̃‖²` of (5.70) [Cauchy_example_1]. -/
theorem fb_lam_two (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (l₁ l₂ : ℕ) (hl : 1 ≤ l₁ + l₂) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
        c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
      ∀ (w₁ : Fin l₁ → Fin 2 × Bool) (w₂ : Fin l₂ → Fin 2 × Bool)
        (B₁ : Fin (l₁ + 1) → Matrix (Idx D N) (Idx D N) ℂ)
        (B₂ : Fin (l₂ + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B₁ j) ≤ K) → (∀ j, opNorm (B₂ j) ≤ K) →
        μ {h | (N : ℝ) ^ τ' * (K ^ (l₁ + l₂ + 2) * (hsNorm (lam D N e.A) ^ 2 / N *
              bndA4 (fun a => (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im)
                (fun a => (e.z a).im) (l₁ + l₂))) <
            ‖ntr (resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))
                w₁ B₁ * e.Lt *
              resWord (fun a => res (Matrix.of h + (e.c a : ℂ) • lam D N e.A) (e.z a))
                w₂ B₂ * e.Lt)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  rcases le_or_gt K 0 with hK | hK
  · refine ⟨0, fun N _ μ _ e _ _ _ _ _ w₁ w₂ B₁ B₂ hB₁ _ => ?_⟩
    have hK0 : K = 0 := le_antisymm hK ((Bd_opNorm_nonneg (B₁ 0)).trans (hB₁ 0))
    have hB0 : B₁ 0 = 0 := FB_eq_zero _ (hK0 ▸ hB₁ 0)
    refine le_trans (measure_mono (t := ∅) fun h hh => ?_) (by simp)
    simp only [Set.mem_ofPred_eq, FB_resWord_zero _ _ _ hB0, FB_ntr_zero,
      norm_zero, hK0, zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero, lt_irrefl] at hh
  · obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
      (Bd_two_unif D (by omega) l₁ l₂ hl δA τ c₀ C₀ (max K 1) hδA hτ hc₀ hC₀ C τ' hτ' D' hD')
    refine ⟨N₀, fun N hN μ hμ e hA hA' hc hz hδ w₁ w₂ B₁ B₂ hB₁ hB₂ => ?_⟩
    have hx : (μ, e) ∈ Bd_Cl D δA C₀ (max K 1) C N :=
      ⟨hμ, hA, hA', hc, hδ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Bd_avgSq_nonneg _ (lam_isHermitian D N _)))⟩
    have h1 := hN₀ N hN (μ, e) hx hz w₁ w₂ (fun j => ((K⁻¹ : ℝ) : ℂ) • B₁ j)
      (fun j => ((K⁻¹ : ℝ) : ℂ) • B₂ j)
      (fun j => (FB_unscale_norm _ K hK (hB₁ j)).trans (le_max_right _ _))
      (fun j => (FB_unscale_norm _ K hK (hB₂ j)).trans (le_max_right _ _))
    refine le_trans (measure_mono fun h hh => ?_) h1
    simp only [Set.mem_ofPred_eq] at hh ⊢
    rw [FB_resWord_unscale _ w₁ B₁ K hK.ne', FB_resWord_unscale _ w₂ B₂ K hK.ne'] at hh
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hh
    rw [FB_ntr_smul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hK, ← pow_add, show l₂ + 1 + (l₁ + 1) = l₁ + l₂ + 2 by ring] at hh
    exact FB_lt_of_scaled _ _ _ _ (pow_pos hK _) hh

/-- The expectation step: a bounded random variable whose modulus exceeds `b` only on an event of
probability `≤ δ` has expectation of modulus `≤ b + B δ`. -/
theorem fb_expect {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℂ) (hX : Integrable X μ) (b B δ : ℝ) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hB : ∀ ω, ‖X ω‖ ≤ B) (hbad : μ {ω | b < ‖X ω‖} ≤ ENNReal.ofReal δ) :
    ‖∫ ω, X ω ∂μ‖ ≤ b + B * δ := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ω₀)
  set T := toMeasurable μ {ω | b < ‖X ω‖} with hTdef
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hsub : {ω | b < ‖X ω‖} ⊆ T := subset_toMeasurable _ _
  have hμT : μ T = μ {ω | b < ‖X ω‖} := measure_toMeasurable _
  have hpt : ∀ ω, ‖X ω‖ ≤ b + T.indicator (fun _ => B) ω := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω]
      linarith [hB ω]
    · rw [Set.indicator_of_notMem hω]
      have h1 : ω ∉ {ω | b < ‖X ω‖} := fun h => hω (hsub h)
      simp only [Set.mem_ofPred_eq, not_lt] at h1
      linarith
  have hI : Integrable (fun ω => b + T.indicator (fun _ => B) ω) μ :=
    (integrable_const b).add ((integrable_const B).indicator hT)
  have hreal : μ.real T ≤ δ := by
    rw [Measure.real, hμT]
    exact ENNReal.toReal_le_of_le_ofReal hδ hbad
  calc ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (b + T.indicator (fun _ => B) ω) ∂μ := integral_mono hX.norm hI hpt
    _ = b + μ.real T * B := by
        rw [integral_add (integrable_const b) ((integrable_const B).indicator hT),
          integral_const, integral_indicator_const B hT]
        simp
    _ ≤ b + B * δ := by nlinarith

end RBMTransitionEdge

end
