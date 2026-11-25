module

public import RBMTransitionEdge.Det.Regular
public import RBMTransitionEdge.LocalLaw.MultiResLocal
public import RBMTransitionEdge.Localized.Expansion.Eval

@[expose] public section

/-!
# The generic bound of the expansion of §5.3

The slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law], their admissibility for the multi-resolvent estimates of
Lemma A.4 [lemma_necessary_estimates], and the generic bound (5.48) [eq:Tsmallthansize] for the
expressions of the class (5.33) [definition_class_of_expression_loop].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The slots of Lemma 5.2 [lemma_localized_eigenvector_local_law]: `(H, z₀)` and `(H + Λ, z₁)`,
`z₁ = γ_k + iη` of (5.1) [eq:z1], `z₀ = z₁ - Δ_ev`, `δ = Δ_ev` of (5.2)
[definition_shift_eigenvector], flags `s`. -/
def evecEnv (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ) (s : Fin 2 → Bool) :
    LoopEnv D N :=
  ⟨A, ![0, 1], ![zOne (lam D N A) k ε - (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ),
    zOne (lam D N A) k ε], s, shiftEv (lam D N A) (zOne (lam D N A) k ε)⟩

/-- The slots of Lemma 5.4 [lemma_localized_eigenvalue_local_law]: `(H + tΛ, z_t)` twice,
`z_t = γ_k(t) + iη` of (5.20) [eq:z1t], `δ = Δ(t)` of (5.19) [definition_shift_eigenvalue],
flags `s`. -/
def evalEnv (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε t : ℝ) (s : Fin 2 → Bool) :
    LoopEnv D N :=
  ⟨A, ![t, t], ![zOne ((t : ℂ) • lam D N A) k ε, zOne ((t : ℂ) • lam D N A) k ε], s,
    shiftT (lam D N A) k ε t⟩


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

/-- `‖X‖_HS² ≤ |ι| ‖X‖²`. -/
private lemma Bd_hsNorm_sq_le (X : Matrix ι ι ℂ) :
    hsNorm X ^ 2 ≤ (Fintype.card ι : ℝ) * opNorm X ^ 2 := by
  unfold hsNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  rw [Finset.sum_comm]
  have hcol : ∀ j : ι, ∑ i, ‖X i j‖ ^ 2 ≤ opNorm X ^ 2 := by
    intro j
    have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) X).le_opNorm (EuclideanSpace.single j (1 : ℂ))
    have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
    rw [h2, mul_one] at h1
    have h3 : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) X) (EuclideanSpace.single j (1 : ℂ))‖ ^ 2 =
        ∑ i, ‖X i j‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
      congr 1
      ext i
      simp [Matrix.mulVec_single]
    rw [← h3]
    unfold opNorm
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ j, ∑ i, ‖X i j‖ ^ 2 ≤ ∑ _j : ι, opNorm X ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

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

/-! ## The slots of Lemmas 5.2 and 5.4 -/

set_option maxHeartbeats 1000000 in
/-- At `z = γ_k + iη` of (5.1) [eq:z1] for `Λ = lam D N A`, `‖A‖ ≤ N^{-δ_A}`, `2k ≤ DN + 1`:
`|z| ≤ 3`, `Im z = η ≤ 1`, `η ≥ N^{-1+ε/2}`, and `N η Im m(z) ≥ c₀`, from (2.21)
[eq:kappa_gamma_k] at `k` and at `DN + 1 - k` and from (A.1) [square_root_density]. -/
private lemma Bd_slot (D : ℕ) (hD : 2 ≤ D) (δA ε : ℝ) (hδA : 0 < δA) (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
        ‖zOne (lam D N A) k ε‖ ≤ 3 ∧ (zOne (lam D N A) k ε).im = etaK D N k ε ∧
        0 < etaK D N k ε ∧ (N : ℝ) ^ (-1 + ε / 2) ≤ etaK D N k ε ∧ etaK D N k ε ≤ 1 / 2 ∧
        c₀ ≤ (N : ℝ) * etaK D N k ε * (mSol (lam D N A) (zOne (lam D N A) k ε)).im := by
  obtain ⟨c₃, C₃, hc₃, -, N₃, hN₃⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨C₄, hC₄, hsq⟩ := square_root_density (1 / 4) (by norm_num)
  obtain ⟨C₅, hC₅, hedge⟩ := edge_close_to_edge_sc
  obtain ⟨N₄, hN₄⟩ := Bd_small δA (1 / (20 * (C₅ + 1))) hδA (by positivity)
  obtain ⟨N₅, hN₅⟩ := Bd_small (1 / 3) (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨N₆, hN₆⟩ := Bd_large (ε / 2) (D : ℝ) (by linarith)
  refine ⟨C₄⁻¹ * Real.sqrt c₃, by positivity, max (max (max N₃ N₄) (max N₅ N₆)) 1, ?_⟩
  intro N hN A hA k hk hkN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hN4 : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hN5 : N₅ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)
  have hN6 : N₆ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hDN : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hN1)
  have hkDN : k ≤ D * N := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set Λ := lam D N A with hΛdef
  have hΛh : Λ.IsHermitian := lam_isHermitian D N A
  have hA0 := Bd_opNorm_nonneg A
  have hAx : opNorm A ≤ 1 / (20 * (C₅ + 1)) := hA.trans (hN₄ N hN4)
  have hx20 : 1 / (20 * (C₅ + 1)) ≤ 1 / 20 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hΛn : opNorm Λ ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  have hC5Λ : C₅ * opNorm Λ ≤ 1 / 10 := by
    have h1 := opNorm_lam_le D N A
    have h2 : C₅ * opNorm Λ ≤ C₅ * (2 * (1 / (20 * (C₅ + 1)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₅.le
    have h3 : C₅ * (2 * (1 / (20 * (C₅ + 1)))) ≤ 1 / 10 := by
      rw [show C₅ * (2 * (1 / (20 * (C₅ + 1)))) = C₅ / (10 * (C₅ + 1)) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  -- the quantile and the edges
  set γ := quant (rho Λ) (D * N) k with hγ
  set q : ℝ := (k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) with hq
  have hqpos : 0 < q := by positivity
  obtain ⟨h1, -, -, -⟩ := hN₃ N hN3 A hA k hk hkDN
  have hk' : 1 ≤ D * N + 1 - k := by omega
  have hk'N : D * N + 1 - k ≤ D * N := by omega
  obtain ⟨-, -, h2, -⟩ := hN₃ N hN3 A hA (D * N + 1 - k) hk' hk'N
  have hkk : D * N + 1 - (D * N + 1 - k) = k := by omega
  rw [hkk] at h2
  have hkle : (k : ℝ) ≤ ((D * N + 1 - k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : k ≤ D * N + 1 - k)
  have hq' : q ≤ ((D * N + 1 - k : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow hkpos.le hkle (by norm_num)
  have hup : c₃ * q ≤ Eplus Λ - γ := h1
  have hlo : c₃ * q ≤ γ - Eminus Λ := le_trans (mul_le_mul_of_nonneg_left hq' hc₃.le) h2
  have hcq : 0 < c₃ * q := mul_pos hc₃ hqpos
  have hγin : γ ∈ Set.Icc (Eminus Λ) (Eplus Λ) := ⟨by linarith, by linarith⟩
  have hκ : c₃ * q ≤ kappa Λ γ := by
    unfold kappa
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact le_min hup hlo
  have hedge' := hedge (Idx D N) Λ hΛh hΛn
  have hγabs : |γ| ≤ 21 / 10 := by
    have ha := abs_nonneg (2 - Eplus Λ)
    have hb := abs_nonneg (2 + Eminus Λ)
    have hc := le_abs_self (Eplus Λ - 2)
    have hd := neg_abs_le (2 + Eminus Λ)
    rw [abs_sub_comm] at ha
    rw [abs_le]
    constructor <;> nlinarith [abs_sub_comm (2 : ℝ) (Eplus Λ), hγin.1, hγin.2]
  -- the imaginary part
  have hrk : rk D N k = k := by
    unfold rk
    rw [Nat.min_eq_left (by omega)]
  have heta : etaK D N k ε = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    unfold etaK
    rw [hrk]
  have hetapos : 0 < etaK D N k ε := by rw [heta]; positivity
  have hetale : etaK D N k ε ≤ 1 / 2 := by
    rw [heta]
    have e1 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by norm_num)
    have e2 : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have e3 := hN₅ N hN5
    have e4 : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) := by positivity
    calc (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (-(1 / 3 : ℝ))
        ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * 1 := mul_le_mul_of_nonneg_left e1 e4
      _ ≤ 1 / 2 := by rw [mul_one]; linarith
  have hetalow : (N : ℝ) ^ (-1 + ε / 2) ≤ etaK D N k ε := by
    rw [heta]
    have hDr : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
    have e1 : ((D : ℝ) * N) ^ (-(1 / 3 : ℝ)) ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hkpos (by exact_mod_cast hkDN) (by norm_num)
    rw [Real.mul_rpow (by positivity) (by positivity)] at e1
    have e2 : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ)) =
        (N : ℝ) ^ (-1 + ε / 2) * (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    have e3 : (D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2) ≥ 1 := by
      have f1 := hN₆ N hN6
      have f2 : (D : ℝ) ^ (-(1 : ℝ)) ≤ (D : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hDr (by norm_num)
      have f3 : (D : ℝ) ^ (-(1 : ℝ)) * D = 1 := by
        rw [Real.rpow_neg_one]
        field_simp
      have f4 : 0 ≤ (D : ℝ) ^ (-(1 : ℝ)) := by positivity
      nlinarith
    have e4 : 0 < (N : ℝ) ^ (-1 + ε / 2) := by positivity
    calc (N : ℝ) ^ (-1 + ε / 2) = (N : ℝ) ^ (-1 + ε / 2) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ (-1 + ε / 2) * ((D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left e3 e4.le
      _ = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * ((D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
          rw [show (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * ((D : ℝ) ^ (-(1 / 3 : ℝ)) *
            (N : ℝ) ^ (-(1 / 3 : ℝ))) = (D : ℝ) ^ (-(1 / 3 : ℝ)) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + ε) *
            (N : ℝ) ^ (-(1 / 3 : ℝ))) by ring, e2]
          ring
      _ ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
  have hzre : (zOne Λ k ε).re = γ := by simp [zOne, hγ]
  have hzim : (zOne Λ k ε).im = etaK D N k ε := by simp [zOne]
  have hznorm : ‖zOne Λ k ε‖ ≤ 3 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hzre, hzim, abs_of_pos hetapos]
    linarith
  refine ⟨hznorm, hzim, hetapos, hetalow, hetale, ?_⟩
  -- `N η Im m ≥ c₀`
  have hsq' := (hsq (Idx D N) Λ hΛh hΛn).2 (zOne Λ k ε) (by norm_num; linarith)
    (by rw [hzim]; exact hetapos)
  have hm := (hsq'.1 (by rw [hzre]; exact hγin)).1
  rw [hzre, hzim] at hm
  have hsqrt : Real.sqrt c₃ * ((k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ))) ≤
      Real.sqrt (kappa Λ γ + etaK D N k ε) := by
    have e1 : Real.sqrt (c₃ * q) ≤ Real.sqrt (kappa Λ γ + etaK D N k ε) :=
      Real.sqrt_le_sqrt (by linarith)
    have e2 : Real.sqrt q = (k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [hq, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hkpos.le, ← Real.rpow_mul hNpos.le]
      norm_num
    rw [Real.sqrt_mul hc₃.le, e2] at e1
    exact e1
  have hprod : (N : ℝ) * etaK D N k ε * ((k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ))) =
      (N : ℝ) ^ ε := by
    rw [heta]
    have e1 : (k : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hkpos]; norm_num
    have e2 : (N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ)) =
        (N : ℝ) ^ ε := by
      rw [show (N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ)) =
        (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ)) by
        rw [Real.rpow_one], ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    calc (N : ℝ) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (-(1 / 3 : ℝ))) *
          ((k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)))
        = ((N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ))) *
          ((k : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ = (N : ℝ) ^ ε := by rw [e1, e2, mul_one]
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNr hε.le
  have hNη : 0 ≤ (N : ℝ) * etaK D N k ε := by positivity
  calc C₄⁻¹ * Real.sqrt c₃
      ≤ C₄⁻¹ * Real.sqrt c₃ * (N : ℝ) ^ ε := le_mul_of_one_le_right (by positivity) hNe
    _ = (N : ℝ) * etaK D N k ε *
          (C₄⁻¹ * (Real.sqrt c₃ * ((k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ))))) := by
        rw [← hprod]; ring
    _ ≤ (N : ℝ) * etaK D N k ε * (C₄⁻¹ * Real.sqrt (kappa Λ γ + etaK D N k ε)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hNη
    _ ≤ (N : ℝ) * etaK D N k ε * (mSol Λ (zOne Λ k ε)).im :=
        mul_le_mul_of_nonneg_left hm hNη

/-- The slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law] satisfy the hypotheses of the multi-resolvent estimates
(A.53)–(A.55) of Lemma A.4 [lemma_necessary_estimates]: `|c_a| ≤ 1`, `z_a ∈ 𝐃(ε/2)`,
`N η Im m_a ≥ c₀` (from (5.3) [sim_m_sc_and_m] and (A.1) [square_root_density]), `|δ| ≤ K⟨Λ²⟩`
((5.4) [shift_bound_localized_eigenvector]), and `2‖A‖ ≤ 1/10`. -/
theorem loop_env_admissible (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) :
    ∃ c₀ K : ℝ, 0 < c₀ ∧ 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        2 * opNorm e.A ≤ 1 / 10 ∧ (∀ a, |e.c a| ≤ 1) ∧
        (∀ a, e.z a ∈ specDom (ε / 2) N ∧ 0 < (e.z a).im ∧ (e.z a).im = etaK D N k ε ∧
          c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) ∧
        |e.δ| ≤ K * avgSq (lam D N e.A) := by
  obtain ⟨c₁, hc₁, N₁, hN₁⟩ := Bd_slot D hD δA ε hδA hε hε''
  obtain ⟨C₁, hC₁, N₂, hN₂⟩ := regular_estimate_localized_eigenvector D hD δA εA ε hδA hεA hε hε'
  obtain ⟨C₂, hC₂, N₃, hN₃⟩ := regular_estimate_localized_eigenvalue D hD δA εA ε hδA hεA hε hε'
  obtain ⟨C₆, hC₆, hmsc⟩ := eq_msc (1 / 4) (by norm_num)
  obtain ⟨N₄, hN₄⟩ := Bd_small δA (1 / (40 * (C₁ + 1))) hδA (by positivity)
  refine ⟨c₁ * (max 1 C₁)⁻¹, max C₁ C₂, by positivity, le_trans hC₁.le (le_max_left _ _),
    max (max N₁ N₂) (max (max N₃ N₄) 1), ?_⟩
  intro N hN A hA k hk hkN hhs e he
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3' : N₃ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hN
  have hN4' : N₄ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hN
  have hNone : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hDN : 2 ≤ D * N := le_trans (by norm_num) (Nat.mul_le_mul hD hNone)
  have hkDN : k ≤ D * N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hA0 := Bd_opNorm_nonneg A
  have hAx : opNorm A ≤ 1 / (40 * (C₁ + 1)) := hA.trans (hN₄ N hN4')
  have hx40 : 1 / (40 * (C₁ + 1)) ≤ 1 / 40 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hA2 : 2 * opNorm A ≤ 1 / 10 := by linarith
  have hΛh := lam_isHermitian D N A
  have hΛn : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  have hav0 := Bd_avgSq_nonneg (lam D N A) hΛh
  have hεd : (6 : ℝ) ≤ (ε / 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  have hmax1 : 0 < max 1 C₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hc₀1 : c₁ * (max 1 C₁)⁻¹ ≤ c₁ := by
    apply mul_le_of_le_one_right hc₁.le
    exact inv_le_one_of_one_le₀ (le_max_left _ _)
  rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
  · -- the slots of Lemma 5.2
    obtain ⟨hz3, hzim, hη, hηlow, hηle, hc⟩ := hN₁ N hN1' A hA k hk hkN
    obtain ⟨hr1, hr2, hr3, -⟩ := hN₂ N hN2' A hA k hk hkDN hhs
    set z₁ := zOne (lam D N A) k ε with hz₁
    set Δ := shiftEv (lam D N A) z₁ with hΔ
    have hz1pos : 0 < z₁.im := by rw [hzim]; exact hη
    have hext : mExt (lam D N A) z₁ = mSol (lam D N A) z₁ := by unfold mExt; simp [hz1pos]
    have hΔle : |Δ| ≤ 1 / 2 := by
      have e1 : C₁ * avgSq (lam D N A) ≤ C₁ * (1 / (20 * (C₁ + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        refine (Bd_avgSq_le _).trans ?_
        have h1 := opNorm_lam_le D N A
        have h0 := Bd_opNorm_nonneg (lam D N A)
        have h2 : 2 * (1 / (40 * (C₁ + 1))) = 1 / (20 * (C₁ + 1)) := by field_simp; ring
        have hl : opNorm (lam D N A) ≤ 1 / (20 * (C₁ + 1)) := by linarith
        have hl1 : opNorm (lam D N A) ≤ 1 := by linarith
        nlinarith
      have e2 : C₁ * (1 / (20 * (C₁ + 1))) ≤ 1 / 2 := by
        rw [show C₁ * (1 / (20 * (C₁ + 1))) = C₁ / (20 * (C₁ + 1)) by ring,
          div_le_iff₀ (by positivity)]
        linarith
      linarith
    have hz0im : (z₁ - (Δ : ℂ)).im = etaK D N k ε := by simp [hzim]
    have hz0norm : ‖z₁ - (Δ : ℂ)‖ ≤ 4 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hz0pos : 0 < (z₁ - (Δ : ℂ)).im := by rw [hz0im]; exact hη
    have hmsc0 : mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) (z₁ - (Δ : ℂ)) = msc (z₁ - (Δ : ℂ)) := by
      have h := (hmsc (Idx D N) 0 (by simp [Matrix.IsHermitian]) (by
        have : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by unfold opNorm; simp
        rw [this]; norm_num) (z₁ - (Δ : ℂ)) (by norm_num; linarith) hz0pos).1
      have : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by unfold opNorm; simp
      rw [this, Real.sqrt_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have hs0 : (evecEnv D N A k ε s).z 0 = z₁ - (Δ : ℂ) ∧ (evecEnv D N A k ε s).c 0 = 0 := by
      simp [evecEnv, hz₁, hΔ]
    have hs1 : (evecEnv D N A k ε s).z 1 = z₁ ∧ (evecEnv D N A k ε s).c 1 = 1 := by
      simp [evecEnv, hz₁]
    have hsA : (evecEnv D N A k ε s).A = A := rfl
    have hsδ : (evecEnv D N A k ε s).δ = Δ := rfl
    refine ⟨hA2, ?_, ?_, ?_⟩
    · intro a
      fin_cases a
      · simp [hs0.2]
      · simp [hs1.2]
    · intro a
      fin_cases a
      · simp only [Fin.zero_eta, Fin.isValue]
        rw [hs0.1, hs0.2, hsA, Complex.ofReal_zero, zero_smul]
        refine ⟨⟨by linarith, ?_⟩, hz0pos, hz0im, ?_⟩
        · rw [hz0im, abs_of_pos hη]; exact hηlow
        · rw [hmsc0, hz0im]
          rw [hext] at hr2
          have e1 : (mSol (lam D N A) z₁).im * (max 1 C₁)⁻¹ ≤ (msc (z₁ - (Δ : ℂ))).im := by
            rw [mul_inv_le_iff₀ hmax1]
            have hm0 : 0 ≤ (msc (z₁ - (Δ : ℂ))).im := by
              rw [← hmsc0]
              exact (mSol_spec _ (by simp [Matrix.IsHermitian]) _ hz0pos).1.le
            nlinarith [le_max_right 1 C₁]
          have hNη : 0 ≤ (N : ℝ) * etaK D N k ε := by positivity
          calc c₁ * (max 1 C₁)⁻¹ ≤ (N : ℝ) * etaK D N k ε * (mSol (lam D N A) z₁).im *
                (max 1 C₁)⁻¹ := mul_le_mul_of_nonneg_right hc (by positivity)
            _ = (N : ℝ) * etaK D N k ε * ((mSol (lam D N A) z₁).im * (max 1 C₁)⁻¹) := by ring
            _ ≤ (N : ℝ) * etaK D N k ε * (msc (z₁ - (Δ : ℂ))).im :=
                mul_le_mul_of_nonneg_left e1 hNη
      · simp only [Fin.mk_one, Fin.isValue]
        rw [hs1.1, hs1.2, hsA, Complex.ofReal_one, one_smul]
        refine ⟨⟨by linarith, ?_⟩, hz1pos, hzim, ?_⟩
        · rw [hzim, abs_of_pos hη]; exact hηlow
        · rw [hzim]; exact hc₀1.trans hc
    · rw [hsδ, hsA]
      exact hr3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hav0)
  · -- the slots of Lemma 5.4
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have htA : opNorm ((t : ℂ) • A) ≤ (N : ℝ) ^ (-δA) := by
      rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
      calc |t| * opNorm A ≤ 1 * opNorm A := mul_le_mul_of_nonneg_right ht1 hA0
        _ ≤ _ := by rw [one_mul]; exact hA
    obtain ⟨hz3, hzim, hη, hηlow, hηle, hc⟩ := hN₁ N hN1' ((t : ℂ) • A) htA k hk hkN
    rw [← lam_smul] at hz3 hzim hc
    have hzpos : 0 < (zOne ((t : ℂ) • lam D N A) k ε).im := by rw [hzim]; exact hη
    have hr := (hN₃ N hN3' A hA k hk hkDN hhs t ht).1
    refine ⟨hA2, ?_, ?_, ?_⟩
    · intro a
      fin_cases a <;> simp [evalEnv, ht1]
    · intro a
      have hslot : (evalEnv D N A k ε t s).z a = zOne ((t : ℂ) • lam D N A) k ε ∧
          (evalEnv D N A k ε t s).c a = t := by
        fin_cases a <;> simp [evalEnv]
      rw [hslot.1, hslot.2]
      refine ⟨⟨by linarith, ?_⟩, hzpos, hzim, ?_⟩
      · rw [hzim, abs_of_pos hη]; exact hηlow
      · rw [hzim]; exact hc₀1.trans hc
    · exact hr.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hav0)

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

private lemma Bd_list_prod_pow {α : Type*} (l : List α) (a b c : ℝ) (f g : α → ℕ) :
    (l.map fun x => a * b ^ f x * c ^ g x).prod =
      a ^ l.length * b ^ (l.map f).sum * c ^ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, ih]
    rw [pow_succ, pow_add, pow_add]
    ring

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

private lemma Bd_Cl_mono {D : ℕ} {δA C₀ K K' : ℝ} {C : ℕ → ℝ} {N : ℕ} (hK : K ≤ K')
    {x : Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N} (hx : x ∈ Bd_Cl D δA C₀ K C N) :
    x ∈ Bd_Cl D δA C₀ K' C N :=
  ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.trans
    (mul_le_mul_of_nonneg_right hK (Bd_avgSq_nonneg _ (lam_isHermitian D N _)))⟩

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

/-- (A.54) [one_loop_estimate] uniformly over `Bd_Cl`. -/
private lemma Bd_one_unif (D : ℕ) (hD : 1 ≤ D) (l : ℕ) (hl : 1 ≤ l)
    (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀)
    (C : ℕ → ℝ) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ (w : Fin l → Fin 2 × Bool) (B : Fin (l + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B j) ≤ K) →
        x.1 {h | (N : ℝ) ^ τ'' * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N x.2.A) *
              bndA4 (fun i => (mSol ((x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i)).im)
                (fun i => (x.2.z i).im) l) <
            ‖ntr (resWord (fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i))
              w B * x.2.Lt)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ'' hτ'' D' hD'
  refine Bd_unif D δA C₀ K C (by linarith) _ fun x hx => ?_
  obtain ⟨N₀, hN₀⟩ := one_loop_local D 2 l (by norm_num) hl δA τ c₀ C₀ K hτ hc₀ hC₀ C
    (fun _ => 1) (fun N => (x N).1) (fun N => (x N).2.A)
    ⟨hD, hδA, fun _ => ⟨zero_le_one, le_rfl⟩, fun N => (hx N).1, fun N => (hx N).2.1⟩
    (fun N => (hx N).2.2.1) (fun N => (x N).2.c) (fun N => (hx N).2.2.2.1)
    (fun N => (x N).2.δ) (fun N => (hx N).2.2.2.2)
    (fun N => {z | (∀ a, Bd_zc D τ c₀ N (x N).2 a) ∧ z = (x N).2.z})
    (fun N z hz i => by
      obtain ⟨h1, rfl⟩ := hz
      exact h1 i) τ'' hτ'' D' hD'
  exact Filter.eventually_atTop.mpr ⟨N₀, fun N hN hz w B hB => hN₀ N hN _ ⟨hz, rfl⟩ w B hB⟩

/-- (A.55) [two_loop_estimate] uniformly over `Bd_Cl`. -/
private lemma Bd_two_unif (D : ℕ) (hD : 1 ≤ D) (l₁ l₂ : ℕ) (hl : 1 ≤ l₁ + l₂)
    (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀)
    (C : ℕ → ℝ) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ (w₁ : Fin l₁ → Fin 2 × Bool) (w₂ : Fin l₂ → Fin 2 × Bool)
        (B₁ : Fin (l₁ + 1) → Matrix (Idx D N) (Idx D N) ℂ)
        (B₂ : Fin (l₂ + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B₁ j) ≤ K) → (∀ j, opNorm (B₂ j) ≤ K) →
        x.1 {h | (N : ℝ) ^ τ'' * (hsNorm (lam D N x.2.A) ^ 2 / N *
              bndA4 (fun i => (mSol ((x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i)).im)
                (fun i => (x.2.z i).im) (l₁ + l₂)) <
            ‖ntr (resWord (fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i))
                w₁ B₁ * x.2.Lt *
              resWord (fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i))
                w₂ B₂ * x.2.Lt)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ'' hτ'' D' hD'
  refine Bd_unif D δA C₀ K C (by linarith) _ fun x hx => ?_
  obtain ⟨N₀, hN₀⟩ := two_loop_local D 2 l₁ l₂ (by norm_num) hl δA τ c₀ C₀ K hτ hc₀ hC₀ C
    (fun _ => 1) (fun N => (x N).1) (fun N => (x N).2.A)
    ⟨hD, hδA, fun _ => ⟨zero_le_one, le_rfl⟩, fun N => (hx N).1, fun N => (hx N).2.1⟩
    (fun N => (hx N).2.2.1) (fun N => (x N).2.c) (fun N => (hx N).2.2.2.1)
    (fun N => (x N).2.δ) (fun N => (x N).2.δ) (fun N => (hx N).2.2.2.2)
    (fun N => (hx N).2.2.2.2)
    (fun N => {z | (∀ a, Bd_zc D τ c₀ N (x N).2 a) ∧ z = (x N).2.z})
    (fun N z hz i => by
      obtain ⟨h1, rfl⟩ := hz
      exact h1 i) τ'' hτ'' D' hD'
  exact Filter.eventually_atTop.mpr ⟨N₀, fun N hN hz w₁ w₂ B₁ B₂ hB₁ hB₂ =>
    hN₀ N hN _ ⟨hz, rfl⟩ w₁ w₂ B₁ B₂ hB₁ hB₂⟩

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

/-- `bndA4 ≤ η^{-(l-1)}` when `Im m_i ≤ 1` and `η ≤ η_i`. -/
private lemma Bd_bndA4_le {p : ℕ} [Nonempty (Fin p)] (imm eta : Fin p → ℝ) (l : ℕ) (η : ℝ)
    (hη : 0 < η) (him : ∀ i, imm i ≤ 1) (het : ∀ i, η ≤ eta i) :
    bndA4 imm eta l ≤ η⁻¹ ^ (l - 1) := by
  unfold bndA4
  have hinf : η ≤ ⨅ i, eta i := le_ciInf het
  have hpos : 0 < (⨅ i, eta i) ^ (l - 1) := pow_pos (hη.trans_le hinf) _
  have hnum : (if 2 ≤ l then ⨆ i, imm i else 1) ≤ 1 := by
    split_ifs
    · exact ciSup_le him
    · exact le_rfl
  calc _ ≤ 1 / (⨅ i, eta i) ^ (l - 1) := (div_le_div_iff_of_pos_right hpos).mpr hnum
    _ ≤ 1 / η ^ (l - 1) :=
        one_div_le_one_div_of_le (pow_pos hη _) (pow_le_pow_left₀ hη.le hinf _)
    _ = η⁻¹ ^ (l - 1) := by rw [one_div, inv_pow]

/-- `‖Λ‖²_HS ≤ D N ‖Λ‖² ≤ 4 D N ‖A‖²`. -/
private lemma Bd_hs_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    hsNorm (lam D N A) ^ 2 ≤ (D : ℝ) * N * (4 * opNorm A ^ 2) := by
  have h1 := Bd_hsNorm_sq_le (lam D N A)
  have h2 := opNorm_lam_le D N A
  have h3 := Bd_opNorm_nonneg (lam D N A)
  have hc : (Fintype.card (Idx D N) : ℝ) = D * N := by simp [Fintype.card_prod]
  rw [hc] at h1
  have : opNorm (lam D N A) ^ 2 ≤ 4 * opNorm A ^ 2 := by nlinarith
  calc _ ≤ (D : ℝ) * N * opNorm (lam D N A) ^ 2 := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

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

/-- `N^{-1/2} ‖Λ‖_HS ≤ 4 D ‖A‖`. -/
private lemma Bd_hs_half (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    (N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N A) ≤ 4 * D * opNorm A := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h := Bd_hs_lam D N A
  have hA := Bd_opNorm_nonneg A
  have hs2 : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    norm_num [Real.rpow_neg_one]
  have hsq : ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N A)) ^ 2 ≤ (4 * D * opNorm A) ^ 2 := by
    rw [mul_pow, hs2]
    have e : (N : ℝ)⁻¹ * hsNorm (lam D N A) ^ 2 ≤ (N : ℝ)⁻¹ * ((D : ℝ) * N * (4 * opNorm A ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have e2 : (N : ℝ)⁻¹ * ((D : ℝ) * N * (4 * opNorm A ^ 2)) = 4 * D * opNorm A ^ 2 := by
      field_simp
    rw [e2] at e
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D - 1) (by positivity : (0:ℝ) ≤ D))
      (sq_nonneg (opNorm A))]
  exact (pow_le_pow_iff_left₀ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.sqrt_nonneg _)) (by positivity) two_ne_zero).mp hsq

/-! ## The bound of one loop -/

/-- A loop without resolvent: `|⟨Π⟩| ≤ (5/4)^{len} ((2 + 4|K|) ‖A‖)^{#Λ̃}`. -/
private lemma Bd_loop_det {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) {δA τ c₀ C₀ K : ℝ} {C : ℕ → ℝ}
    (hC₀ : 1 ≤ C₀) {x : Measure (Idx D N → Idx D N → ℂ) × LoopEnv D N}
    (hx : x ∈ Bd_Cl D δA C₀ K C N) (hz : ∀ a, Bd_zc D τ c₀ N x.2 a)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (hE : ∀ y, opNorm (E y) ≤ 1) (w : List LoopLetter)
    (hw2 : w.countP Bd_isL ≤ 2) (hr : w.countP Bd_isRes = 0)
    (G : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (τ'' : ℝ) (hτ'' : 0 ≤ τ'') :
    ‖ntr (loopWordMat G x.2.M E x.2.Lt w)‖ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' *
      (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.A ^ (w.countP Bd_isL) := by
  obtain ⟨-, hM, hLt, -, -, -⟩ := Bd_facts hD hN hC₀ hx hz
  have hA0 := Bd_opNorm_nonneg x.2.A
  have hK0 : (1 : ℝ) ≤ 2 + 4 * |K| := by linarith [abs_nonneg K]
  have hQ : 0 ≤ (2 + 4 * |K|) * opNorm x.2.A := by positivity
  have hprod := Bd_prod_normL w (Bd_let G x.2.M E x.2.Lt) (5 / 4) ((2 + 4 * |K|) * opNorm x.2.A)
    (by norm_num) hQ (fun y hy => by
      have hyr : Bd_isRes y = false := by simpa using List.countP_eq_zero.mp hr y hy
      cases y with
      | res a => simp [Bd_isRes] at hyr
      | det a => simpa [Bd_isL, Bd_let] using hM a
      | proj y => simpa [Bd_isL, Bd_let] using (hE y).trans (by norm_num : (1 : ℝ) ≤ 5 / 4)
      | lamt o => simpa [Bd_isL, Bd_let] using hLt)
  rw [hr, Nat.zero_sub, pow_zero, mul_one]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ τ'' := Real.one_le_rpow (by exact_mod_cast hN) hτ''
  have hK2 : (2 + 4 * |K|) ^ (w.countP Bd_isL) ≤ (2 + 4 * |K|) ^ 2 :=
    pow_le_pow_right₀ hK0 hw2
  have hcw := (Bd_cw_ge D hD K w.length).2.2.1
  have hcw1 := (Bd_cw_ge D hD K w.length).2.2.2
  have hAc : 0 ≤ opNorm x.2.A ^ (w.countP Bd_isL) := by positivity
  calc ‖ntr (loopWordMat G x.2.M E x.2.Lt w)‖ ≤ opNorm (loopWordMat G x.2.M E x.2.Lt w) :=
        Bd_ntr_le _
    _ ≤ (5 / 4) ^ w.length * ((2 + 4 * |K|) * opNorm x.2.A) ^ (w.countP Bd_isL) := hprod
    _ = ((5 / 4) ^ w.length * (2 + 4 * |K|) ^ (w.countP Bd_isL)) *
          opNorm x.2.A ^ (w.countP Bd_isL) := by rw [mul_pow]; ring
    _ ≤ Bd_cw D K w.length * opNorm x.2.A ^ (w.countP Bd_isL) := by
        refine mul_le_mul_of_nonneg_right ?_ hAc
        exact (mul_le_mul_of_nonneg_left hK2 (by positivity)).trans hcw
    _ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' * opNorm x.2.A ^ (w.countP Bd_isL) := by
        refine mul_le_mul_of_nonneg_right ?_ hAc
        exact le_mul_of_one_le_right (by linarith) hN1

/-- A loop with both `Λ̃` and `r ≥ 1` resolvents (Type I, (5.34) [Gamma_Type_1]), by (A.55)
[two_loop_estimate]: `|⟨Π⟩| ≺ N⁻¹‖Λ‖²_HS η^{-(r-1)}`. -/
private lemma Bd_loop_two (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hw : w.countP Bd_isL = 2) (hr : 1 ≤ w.countP Bd_isRes) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖ntr (loopWordMat (x.2.G h) x.2.M E x.2.Lt w)‖ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.A ^ (w.countP Bd_isL) := by
  intro τ'' hτ'' D' hD'
  obtain ⟨a, y₁, b, rfl, ha, hy₁⟩ := Bd_split Bd_isL w (by omega)
  have hb : b.countP Bd_isL = 1 := by
    simp only [List.countP_append, List.countP_cons, hy₁, ite_true] at hw
    omega
  obtain ⟨c, y₂, d, rfl, hc, hy₂⟩ := Bd_split Bd_isL b (by omega)
  have hd : d.countP Bd_isL = 0 := by
    simp only [List.countP_append, List.countP_cons, hy₂, ite_true] at hb
    omega
  have hy₁r := Bd_isL_notRes y₁ hy₁
  have hy₂r := Bd_isL_notRes y₂ hy₂
  have hv₁ : (d ++ a).countP Bd_isL = 0 := by simp [List.countP_append, ha, hd]
  have hl : (Bd_dec (d ++ a)).2.length + (Bd_dec c).2.length =
      (a ++ y₁ :: (c ++ y₂ :: d)).countP Bd_isRes := by
    rw [Bd_dec_len, Bd_dec_len]
    simp only [List.countP_append, List.countP_cons, hy₁r, hy₂r]
    simp
    omega
  have hlen₁ : (d ++ a).length ≤ (a ++ y₁ :: (c ++ y₂ :: d)).length := by simp; omega
  have hlen₂ : c.length ≤ (a ++ y₁ :: (c ++ y₂ :: d)).length := by simp; omega
  set Kp := max K ((5 / 4 : ℝ) ^ (a ++ y₁ :: (c ++ y₂ :: d)).length) with hKp
  have hU := Bd_two_unif D hD (Bd_dec (d ++ a)).2.length (Bd_dec c).2.length (by omega) δA τ c₀
    C₀ Kp hδA hτ hc₀ hC₀ C τ'' hτ'' D' hD'
  filter_upwards [hU, Filter.eventually_ge_atTop 1] with N hN hN1 x hx hz E hE
  obtain ⟨-, hM, -, hη, hηz, him⟩ := Bd_facts hD hN1 hC₀ hx hz
  have hpow₁ : (5 / 4 : ℝ) ^ (d ++ a).length ≤ Kp :=
    (pow_le_pow_right₀ (by norm_num) hlen₁).trans (le_max_right _ _)
  have hpow₂ : (5 / 4 : ℝ) ^ c.length ≤ Kp :=
    (pow_le_pow_right₀ (by norm_num) hlen₂).trans (le_max_right _ _)
  refine ⟨_, hN x (Bd_Cl_mono (le_max_left _ _) hx) hz (Bd_wv x.2.s (d ++ a)) (Bd_wv x.2.s c)
    (Bd_Bv x.2.M E x.2.Lt (d ++ a)) (Bd_Bv x.2.M E x.2.Lt c)
    (fun j => (Bd_Bv_norm _ _ _ hM hE _ hv₁ j).trans hpow₁)
    (fun j => (Bd_Bv_norm _ _ _ hM hE _ hc j).trans hpow₂), fun h hh hbad => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt] at hbad
  rw [Bd_wordMat_eq, Bd_mat_two _ _ _ _ a c d y₁ y₂ hy₁ hy₂, Bd_G_eq _ _ hh,
    Bd_mat_resWord (fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i)),
    Bd_mat_resWord (fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i))]
  refine hbad.trans ?_
  rw [hw, ← hl]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hA0 := Bd_opNorm_nonneg x.2.A
  have h1 : hsNorm (lam D N x.2.A) ^ 2 / N ≤ 4 * D * opNorm x.2.A ^ 2 := by
    rw [div_le_iff₀ hNr]
    have := Bd_hs_lam D N x.2.A
    nlinarith
  have h2 := Bd_bndA4_le (fun i => (mSol ((x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i)).im)
    (fun i => (x.2.z i).im) ((Bd_dec (d ++ a)).2.length + (Bd_dec c).2.length) (Bd_eta x.2) hη
    him hηz
  have hcw := (Bd_cw_ge D hD K (a ++ y₁ :: (c ++ y₂ :: d)).length).2.1
  have hk : 0 ≤ (Bd_eta x.2)⁻¹ ^ ((Bd_dec (d ++ a)).2.length + (Bd_dec c).2.length - 1) := by
    positivity
  have hNτ : 0 ≤ (N : ℝ) ^ τ'' := by positivity
  calc (N : ℝ) ^ τ'' * (hsNorm (lam D N x.2.A) ^ 2 / N * bndA4 _ _ _)
      ≤ (N : ℝ) ^ τ'' * (4 * D * opNorm x.2.A ^ 2 *
          (Bd_eta x.2)⁻¹ ^ ((Bd_dec (d ++ a)).2.length + (Bd_dec c).2.length - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hNτ
        exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans
          (mul_le_mul_of_nonneg_right h1 hk)
    _ = 4 * D * ((N : ℝ) ^ τ'' *
          (Bd_eta x.2)⁻¹ ^ ((Bd_dec (d ++ a)).2.length + (Bd_dec c).2.length - 1) *
          opNorm x.2.A ^ 2) := by ring
    _ ≤ Bd_cw D K (a ++ y₁ :: (c ++ y₂ :: d)).length * ((N : ℝ) ^ τ'' *
          (Bd_eta x.2)⁻¹ ^ ((Bd_dec (d ++ a)).2.length + (Bd_dec c).2.length - 1) *
          opNorm x.2.A ^ 2) := mul_le_mul_of_nonneg_right hcw (by positivity)
    _ = _ := by ring

/-- A loop with one `Λ̃` and `r ≥ 1` resolvents (Type II, (5.35) [Gamma_Type_2]), by (A.54)
[one_loop_estimate]: `|⟨Π⟩| ≺ N^{-1/2}‖Λ‖_HS η^{-(r-1)}`. -/
private lemma Bd_loop_one (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hw : w.countP Bd_isL = 1) (hr : 1 ≤ w.countP Bd_isRes) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖ntr (loopWordMat (x.2.G h) x.2.M E x.2.Lt w)‖ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.A ^ (w.countP Bd_isL) := by
  intro τ'' hτ'' D' hD'
  obtain ⟨a, y, b, rfl, ha, hy⟩ := Bd_split Bd_isL w (by omega)
  have hb : b.countP Bd_isL = 0 := by
    simp only [List.countP_append, List.countP_cons, hy, ite_true] at hw
    omega
  have hyr := Bd_isL_notRes y hy
  have hv : (b ++ a).countP Bd_isL = 0 := by simp [List.countP_append, ha, hb]
  have hl : (Bd_dec (b ++ a)).2.length = (a ++ y :: b).countP Bd_isRes := by
    rw [Bd_dec_len]
    simp only [List.countP_append, List.countP_cons, hyr]
    simp
    omega
  have hlen : (b ++ a).length ≤ (a ++ y :: b).length := by simp; omega
  set Kp := max K ((5 / 4 : ℝ) ^ (a ++ y :: b).length) with hKp
  have hU := Bd_one_unif D hD (Bd_dec (b ++ a)).2.length (by omega) δA τ c₀ C₀ Kp hδA hτ hc₀ hC₀
    C τ'' hτ'' D' hD'
  filter_upwards [hU, Filter.eventually_ge_atTop 1] with N hN hN1 x hx hz E hE
  obtain ⟨-, hM, -, hη, hηz, him⟩ := Bd_facts hD hN1 hC₀ hx hz
  have hpow : (5 / 4 : ℝ) ^ (b ++ a).length ≤ Kp :=
    (pow_le_pow_right₀ (by norm_num) hlen).trans (le_max_right _ _)
  refine ⟨_, hN x (Bd_Cl_mono (le_max_left _ _) hx) hz (Bd_wv x.2.s (b ++ a))
    (Bd_Bv x.2.M E x.2.Lt (b ++ a)) (fun j => (Bd_Bv_norm _ _ _ hM hE _ hv j).trans hpow),
    fun h hh hbad => ?_⟩
  simp only [Set.mem_ofPred_eq, not_lt] at hbad
  rw [Bd_wordMat_eq, Bd_mat_one _ _ _ _ a b y hy, Bd_G_eq _ _ hh,
    Bd_mat_resWord (fun i => res (Matrix.of h + (x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i))]
  refine hbad.trans ?_
  rw [hw, ← hl]
  have hA0 := Bd_opNorm_nonneg x.2.A
  have h1 := Bd_hs_half D N hD hN1 x.2.A
  have h2 := Bd_bndA4_le (fun i => (mSol ((x.2.c i : ℂ) • lam D N x.2.A) (x.2.z i)).im)
    (fun i => (x.2.z i).im) (Bd_dec (b ++ a)).2.length (Bd_eta x.2) hη him hηz
  have hcw := (Bd_cw_ge D hD K (a ++ y :: b).length).2.1
  have hk : 0 ≤ (Bd_eta x.2)⁻¹ ^ ((Bd_dec (b ++ a)).2.length - 1) := by positivity
  have hNτ : 0 ≤ (N : ℝ) ^ τ'' := by positivity
  have hs0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N x.2.A) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)
  calc (N : ℝ) ^ τ'' * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N x.2.A) * bndA4 _ _ _)
      ≤ (N : ℝ) ^ τ'' * (4 * D * opNorm x.2.A *
          (Bd_eta x.2)⁻¹ ^ ((Bd_dec (b ++ a)).2.length - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hNτ
        exact (mul_le_mul_of_nonneg_left h2 hs0).trans (mul_le_mul_of_nonneg_right h1 hk)
    _ = 4 * D * ((N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ ((Bd_dec (b ++ a)).2.length - 1) *
          opNorm x.2.A ^ 1) := by ring
    _ ≤ Bd_cw D K (a ++ y :: b).length * ((N : ℝ) ^ τ'' *
          (Bd_eta x.2)⁻¹ ^ ((Bd_dec (b ++ a)).2.length - 1) * opNorm x.2.A ^ 1) :=
        mul_le_mul_of_nonneg_right hcw (by positivity)
    _ = _ := by ring

/-- A loop without `Λ̃` and with `r ≥ 1` resolvents, by (A.53) [entprodG]:
`|⟨Π⟩| ≺ η^{-(r-1)}`. -/
private lemma Bd_loop_zero (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hw : w.countP Bd_isL = 0) (hr : 1 ≤ w.countP Bd_isRes) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖ntr (loopWordMat (x.2.G h) x.2.M E x.2.Lt w)‖ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.A ^ (w.countP Bd_isL) := by
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
  rw [hmat, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRs0, hw,
    pow_zero, mul_one, ← hpr]
  have : Nonempty (Fin p) := ⟨⟨0, hp1⟩⟩
  have h2 := Bd_bndA4_le (fun i => (mSol ((x.2.c (σ i) : ℂ) • lam D N x.2.A) (x.2.z (σ i))).im)
    (fun i => (x.2.z (σ i)).im) p (Bd_eta x.2) hη (fun i => him (σ i)) (fun i => hηz (σ i))
  have hRp : Rs ^ p ≤ Bd_cw D K (a ++ g :: b).length := by
    refine le_trans ?_ (Bd_cw_ge D hD K (a ++ g :: b).length).1
    rw [hRs, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hplen)
  have hk : 0 ≤ (Bd_eta x.2)⁻¹ ^ (p - 1) := by positivity
  have hNτ : 0 ≤ (N : ℝ) ^ τ'' := by positivity
  calc Rs ^ p * ‖ntr (resProd (fun i => Gr (σ i)) (fun j => x.2.s (σ j)) B')‖
      ≤ Rs ^ p * ((N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (p - 1)) := by
        refine mul_le_mul_of_nonneg_left (hbad.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hNτ
    _ ≤ Bd_cw D K (a ++ g :: b).length * ((N : ℝ) ^ τ'' * (Bd_eta x.2)⁻¹ ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right hRp (by positivity)
    _ = _ := by ring

/-- The bound of one loop of an expression of the class (5.33)
[definition_class_of_expression_loop] off an event of probability `≤ N^{-D'}`:
`|⟨Π⟩| ≤ C N^{τ''} η^{-(r-1)₊} ‖A‖^{#Λ̃}`, `r` the number of resolvents. -/
private lemma Bd_loop (D : ℕ) (hD : 1 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (w : List LoopLetter)
    (hw2 : w.countP Bd_isL ≤ 2) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop, ∀ x ∈ Bd_Cl D δA C₀ K C N,
      (∀ a, Bd_zc D τ c₀ N x.2 a) →
      ∀ E : ℕ → Matrix (Idx D N) (Idx D N) ℂ, (∀ y, opNorm (E y) ≤ 1) →
      ∃ bad : Set (Idx D N → Idx D N → ℂ), x.1 bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
          ‖ntr (loopWordMat (x.2.G h) x.2.M E x.2.Lt w)‖ ≤ Bd_cw D K w.length * (N : ℝ) ^ τ'' *
            (Bd_eta x.2)⁻¹ ^ (w.countP Bd_isRes - 1) * opNorm x.2.A ^ (w.countP Bd_isL) := by
  intro τ'' hτ'' D' hD'
  rcases Nat.eq_zero_or_pos (w.countP Bd_isRes) with hr | hr
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN1 x hx hz E hE
    exact ⟨∅, by simp, fun h _ _ => Bd_loop_det hD hN1 hC₀ hx hz E hE w hw2 hr _ τ'' hτ''.le⟩
  · rcases (show w.countP Bd_isL = 0 ∨ w.countP Bd_isL = 1 ∨ w.countP Bd_isL = 2 by omega)
      with h0 | h1 | h2
    · exact Bd_loop_zero D hD δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C w h0 hr τ'' hτ'' D' hD'
    · exact Bd_loop_one D hD δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C w h1 hr τ'' hτ'' D' hD'
    · exact Bd_loop_two D hD δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C w h2 hr τ'' hτ'' D' hD'

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

/-- `Σ (r_w - 1)₊ = m - n + #{w : r_w = 0}`. -/
private lemma Bd_sum_sub (L : List (List LoopLetter)) :
    (((L.map fun w => w.countP Bd_isRes - 1).sum : ℕ) : ℤ) =
      ((L.map (List.countP Bd_isRes)).sum : ℤ) - L.length +
        L.countP (fun w => decide (w.countP Bd_isRes = 0)) := by
  induction L with
  | nil => simp
  | cons v t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.countP_cons, Nat.cast_add,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ih]
    split_ifs with h
    · simp only [decide_eq_true_eq] at h
      rw [h]
      push_cast
      ring
    · simp only [decide_eq_true_eq] at h
      have : 1 ≤ v.countP Bd_isRes := Nat.one_le_iff_ne_zero.mpr h
      push_cast [Nat.cast_sub this]
      ring

/-! ## The value of an expression from bounds on its factors -/

private lemma Bd_opNorm_E {D N : ℕ} (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (x : ℕ) :
    opNorm (e.E ι x) ≤ 1 := by
  unfold LoopEnv.E
  split_ifs
  · exact Bd_opNorm_Ea D N _
  · exact Bd_opNorm_one

/-- `|D^{dexp} N^{-S} Σ_ι Π W Π ⟨Π⟩| ≤ D^{dexp} N^{-S} D^{nb} Wb^u Π (Lc X^{a_w} Y^{b_w})`. -/
private lemma Bd_evalH_le {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (h : Idx D N → Idx D N → ℂ) (Wb Lc X Y : ℝ) (hWb : 0 ≤ Wb) (a b : List LoopLetter → ℕ)
    (hW : ∀ ι : Fin T.nb → Fin D, ∀ p ∈ T.weights,
      ‖ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)‖ ≤ Wb)
    (hL : ∀ ι : Fin T.nb → Fin D, ∀ w ∈ T.loops,
      ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤ Lc * X ^ a w * Y ^ b w) :
    ‖T.evalH e h‖ ≤ (D : ℝ) ^ T.dexp * ((N : ℝ) ^ T.S)⁻¹ * ((D : ℝ) ^ T.nb *
      (Wb ^ T.weights.length * (Lc ^ T.loops.length * X ^ (T.loops.map a).sum *
        Y ^ (T.loops.map b).sum))) := by
  unfold LoopExpr.evalH
  rw [norm_mul, norm_mul, norm_zpow, Complex.norm_natCast, norm_inv, norm_pow,
    Complex.norm_natCast]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) ^ T.dexp := zpow_nonneg (Nat.cast_nonneg _) _
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hD0 (by positivity))
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ι : Fin T.nb → Fin D,
      ‖(T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
        (T.loops.map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod‖ ≤
      Wb ^ T.weights.length * (Lc ^ T.loops.length * X ^ (T.loops.map a).sum *
        Y ^ (T.loops.map b).sum) := by
    intro ι
    rw [norm_mul]
    have h1 := Bd_list_norm T.weights (fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2))
      (fun _ => Wb) (hW ι)
    have h2 := Bd_list_norm T.loops (fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w))
      (fun w => Lc * X ^ a w * Y ^ b w) (hL ι)
    rw [List.map_const', List.prod_replicate] at h1
    rw [Bd_list_prod_pow] at h2
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  refine (Finset.sum_le_sum fun ι _ => hterm ι).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  exact le_rfl

/-! ## Arithmetic of the final bound -/

/-- For `N⁻¹ ≤ η ≤ T`, `η^k ≥ (T N)^{-|k|}`. -/
private lemma Bd_zpow_lower (η Tt Nr : ℝ) (hη : 0 < η) (hTt : 1 ≤ Tt) (hN : 1 ≤ Nr)
    (h1 : Nr⁻¹ ≤ η) (h2 : η ≤ Tt) (k : ℤ) : ((Tt * Nr) ^ k.natAbs)⁻¹ ≤ η ^ k := by
  have hTN : 1 ≤ Tt * Nr := one_le_mul_of_one_le_of_one_le hTt hN
  have hNr : 0 < Nr := by linarith
  obtain ⟨m, rfl | rfl⟩ : ∃ m : ℕ, k = m ∨ k = -m := ⟨k.natAbs, Int.natAbs_eq k⟩
  · rw [Int.natAbs_natCast, zpow_natCast, ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    refine le_trans ?_ h1
    exact inv_anti₀ hNr (le_mul_of_one_le_left hNr.le hTt)
  · rw [Int.natAbs_neg, Int.natAbs_natCast, _root_.zpow_neg, zpow_natCast]
    refine inv_anti₀ (pow_pos hη m) ?_
    exact pow_le_pow_left₀ hη.le (h2.trans (le_mul_of_one_le_right (by linarith) hN)) m

/-- The good-event part of the bound. -/
private lemma Bd_good_arith (D N : ℕ) (hN : 1 ≤ N) (dexp : ℤ) (S nb u n Sa d : ℕ)
    (Cbig Tt η τ' τ'' A : ℝ) (E : ℤ) (hd : d ≤ 2) (hE : E = ((u + Sa + d : ℕ) : ℤ))
    (hη : 0 < η) (hηT : η ≤ Tt) (hTt : 1 ≤ Tt) (hCbig : 0 ≤ Cbig) (hττ : τ'' * (u + n) ≤ τ' / 2)
    (hlarge : 2 * ((D : ℝ) ^ dexp * (D : ℝ) ^ nb * Cbig ^ n * Tt ^ 2) ≤ (N : ℝ) ^ (τ' / 2)) :
    (D : ℝ) ^ dexp * ((N : ℝ) ^ S)⁻¹ * ((D : ℝ) ^ nb * (((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * η⁻¹)) ^ u *
      ((Cbig * (N : ℝ) ^ τ'') ^ n * η⁻¹ ^ Sa * A ^ 2))) ≤
      1 / 2 * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-((S : ℤ) + u)) * η ^ (-E) * A ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set P := (N : ℝ) ^ τ'' with hP
  set K₀ := (D : ℝ) ^ dexp * (D : ℝ) ^ nb * Cbig ^ n with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hNz : (N : ℝ) ^ (-((S : ℤ) + u)) = ((N : ℝ) ^ S)⁻¹ * ((N : ℝ)⁻¹) ^ u := by
    rw [show ((S : ℤ) + u) = ((S + u : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg, zpow_natCast,
      pow_add, mul_inv, inv_pow]
  have hEz : η ^ (-E) = η⁻¹ ^ (u + Sa) * η⁻¹ ^ d := by
    rw [hE, _root_.zpow_neg, zpow_natCast, ← inv_pow, pow_add]
  have hPu : P ^ (u + n) ≤ (N : ℝ) ^ (τ' / 2) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hηd : η⁻¹ ^ (u + Sa) ≤ Tt ^ 2 * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := by
    have h1 : η ^ d ≤ Tt ^ 2 :=
      (pow_le_pow_left₀ hη.le hηT d).trans (pow_le_pow_right₀ hTt hd)
    have h2 : η⁻¹ ^ (u + Sa) = η ^ d * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := by
      rw [← mul_assoc, mul_comm (η ^ d), mul_assoc, ← mul_pow, mul_inv_cancel₀ hη.ne', one_pow,
        mul_one]
    calc η⁻¹ ^ (u + Sa) = η ^ d * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := h2
      _ ≤ Tt ^ 2 * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hhalf : K₀ * Tt ^ 2 * (N : ℝ) ^ (τ' / 2) ≤ 1 / 2 * (N : ℝ) ^ τ' := by
    have : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
      rw [← Real.rpow_add hNr]; ring_nf
    rw [this]
    have h0 : 0 ≤ (N : ℝ) ^ (τ' / 2) := by positivity
    nlinarith
  calc (D : ℝ) ^ dexp * ((N : ℝ) ^ S)⁻¹ * ((D : ℝ) ^ nb * ((P * ((N : ℝ)⁻¹ * η⁻¹)) ^ u *
        ((Cbig * P) ^ n * η⁻¹ ^ Sa * A ^ 2)))
      = K₀ * P ^ (u + n) * (((N : ℝ) ^ S)⁻¹ * ((N : ℝ)⁻¹) ^ u) * η⁻¹ ^ (u + Sa) * A ^ 2 := by
        rw [hK₀]; ring
    _ ≤ K₀ * (N : ℝ) ^ (τ' / 2) * (((N : ℝ) ^ S)⁻¹ * ((N : ℝ)⁻¹) ^ u) *
          (Tt ^ 2 * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d)) * A ^ 2 := by
        gcongr
    _ = (K₀ * Tt ^ 2 * (N : ℝ) ^ (τ' / 2)) *
          ((((N : ℝ) ^ S)⁻¹ * ((N : ℝ)⁻¹) ^ u) * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) * A ^ 2) := by ring
    _ ≤ (1 / 2 * (N : ℝ) ^ τ') *
          ((((N : ℝ) ^ S)⁻¹ * ((N : ℝ)⁻¹) ^ u) * (η⁻¹ ^ (u + Sa) * η⁻¹ ^ d) * A ^ 2) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
    _ = _ := by rw [hNz, hEz]; ring

/-- The bad-event part of the bound. -/
private lemma Bd_bad_arith (D N : ℕ) (hN : 1 ≤ N) (dexp : ℤ) (S nb u n Ltot Dn : ℕ)
    (QL Tt η τ' A m : ℝ) (E : ℤ) (hDn : Dn = u + Ltot + (S + u + E.natAbs) + 1)
    (hη : 0 < η) (hη1 : (N : ℝ)⁻¹ ≤ η) (hηT : η ≤ Tt) (hTt : 1 ≤ Tt) (hτ' : 0 < τ')
    (hm0 : 0 ≤ m)
    (hm : m ≤ (D : ℝ) ^ nb * (u + n) * (N : ℝ) ^ (-(Dn : ℝ)))
    (hlarge : 2 * ((D : ℝ) ^ dexp * (D : ℝ) ^ nb * 2 ^ u * QL ^ 2 * ((D : ℝ) ^ nb * (u + n))) *
      Tt ^ E.natAbs ≤ N) :
    (D : ℝ) ^ dexp * ((N : ℝ) ^ S)⁻¹ * ((D : ℝ) ^ nb * ((2 * (N : ℝ)) ^ u *
      (1 ^ n * (N : ℝ) ^ Ltot * (QL * A) ^ 2))) * m ≤
      1 / 2 * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-((S : ℤ) + u)) * η ^ (-E) * A ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Cb := (D : ℝ) ^ dexp * (D : ℝ) ^ nb * 2 ^ u * QL ^ 2 * ((D : ℝ) ^ nb * (u + n)) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set M₀ : ℝ := (N : ℝ) ^ (S + u + E.natAbs) with hM₀
  have hM₀0 : 0 < M₀ := by positivity
  have hDnr : (N : ℝ) ^ (-(Dn : ℝ)) = ((N : ℝ) ^ (u + Ltot) * M₀ * N)⁻¹ := by
    rw [Real.rpow_neg hNr.le, Real.rpow_natCast, hDn, hM₀, pow_add, pow_add, pow_one]
  have hNS : ((N : ℝ) ^ S)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hN1)
  have hlow : (M₀ * Tt ^ E.natAbs)⁻¹ ≤ (N : ℝ) ^ (-((S : ℤ) + u)) * η ^ (-E) := by
    have h1 := Bd_zpow_lower η Tt N hη hTt hN1 hη1 hηT (-E)
    rw [Int.natAbs_neg] at h1
    have h2 : (N : ℝ) ^ (-((S : ℤ) + u)) = ((N : ℝ) ^ (S + u))⁻¹ := by
      rw [show ((S : ℤ) + u) = ((S + u : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg,
        zpow_natCast]
    rw [h2]
    have h3 : (M₀ * Tt ^ E.natAbs)⁻¹ = ((N : ℝ) ^ (S + u))⁻¹ * ((Tt * N) ^ E.natAbs)⁻¹ := by
      rw [hM₀, ← mul_inv, mul_pow, pow_add]
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hRg : 1 / 2 * ((M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2) ≤
      1 / 2 * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-((S : ℤ) + u)) * η ^ (-E) * A ^ 2)) := by
    have hNτ : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
    have h0 : 0 ≤ (N : ℝ) ^ (-((S : ℤ) + u)) * η ^ (-E) * A ^ 2 :=
      mul_nonneg ((inv_nonneg.mpr (by positivity)).trans hlow) (by positivity)
    have : (M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2 ≤ (N : ℝ) ^ (-((S : ℤ) + u)) * η ^ (-E) * A ^ 2 :=
      mul_le_mul_of_nonneg_right hlow (by positivity)
    nlinarith
  refine le_trans ?_ hRg
  have hTt0 : 0 < Tt ^ E.natAbs := by positivity
  have hkey : Cb * (M₀ * N)⁻¹ ≤ 1 / 2 * (M₀ * Tt ^ E.natAbs)⁻¹ := by
    rw [mul_inv, mul_inv, ← mul_assoc, ← mul_assoc]
    rw [show Cb * M₀⁻¹ * (N : ℝ)⁻¹ = M₀⁻¹ * (Cb / N) by ring,
      show 1 / 2 * M₀⁻¹ * (Tt ^ E.natAbs)⁻¹ = M₀⁻¹ * (1 / (2 * Tt ^ E.natAbs)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_div_iff₀ hNr (by positivity)]
    linarith
  calc (D : ℝ) ^ dexp * ((N : ℝ) ^ S)⁻¹ * ((D : ℝ) ^ nb * ((2 * (N : ℝ)) ^ u *
        (1 ^ n * (N : ℝ) ^ Ltot * (QL * A) ^ 2))) * m
      ≤ (D : ℝ) ^ dexp * 1 * ((D : ℝ) ^ nb * ((2 * (N : ℝ)) ^ u *
        (1 ^ n * (N : ℝ) ^ Ltot * (QL * A) ^ 2))) *
          ((D : ℝ) ^ nb * (u + n) * ((N : ℝ) ^ (u + Ltot) * M₀ * N)⁻¹) := by
        rw [← hDnr]
        gcongr
    _ = Cb * ((M₀ * N)⁻¹) * A ^ 2 := by
        rw [hCb]
        have hu0 : (N : ℝ) ^ (u + Ltot) ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ 1 / 2 * (M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2 := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 1 / 2 * ((M₀ * Tt ^ E.natAbs)⁻¹ * A ^ 2) := by ring

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

/-- (5.48) [eq:Tsmallthansize] with the size `(S + u, m - n + u)` read as
`N^{-size₁} η^{-size₂ - 1(k₁=0) - 1(k₂=0)} ‖A‖²`, in expectation, for an expression of the class
`𝒯`, a member of the class with the block profile and slots satisfying the hypotheses of
Lemma A.4 [lemma_necessary_estimates]; `η = min(Im z₀, Im z₁)`. -/
theorem loop_generic_bound (D : ℕ) (hD : 2 ≤ D) (δA τ c₀ C₀ K : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (T : LoopExpr) (hT : T.wf = true) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → 2 * C₀ * opNorm e.A ≤ 1 / 10 →
      (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N ∧ 0 < (e.z a).im ∧
        c₀ ≤ (N : ℝ) * (e.z a).im * (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im) →
      |e.δ| ≤ K * avgSq (lam D N e.A) →
        ‖∫ h, T.evalH e h ∂μ‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-T.size.1) *
            min (e.z 0).im (e.z 1).im ^ (-(T.size.2 + (if T.kk 0 = 0 then 1 else 0) +
              (if T.kk 1 = 0 then 1 else 0))) * opNorm e.A ^ 2) := by
  intro τ' hτ'
  obtain ⟨hwf2, hsumL, hZ⟩ := Bd_wf_facts T hT
  have hD1 : 1 ≤ D := by omega
  set u := T.weights.length with hu
  set n := T.loops.length with hn
  set Ltot := (T.loops.map List.length).sum with hLtot
  set Sa := (T.loops.map fun w => w.countP Bd_isRes - 1).sum with hSa
  set E : ℤ := T.size.2 + (if T.kk 0 = 0 then 1 else 0) + (if T.kk 1 = 0 then 1 else 0) with hE
  have hs1 : T.size.1 = (T.S : ℤ) + u := rfl
  have hs2 : T.size.2 = ((T.loops.map (List.countP Bd_isRes)).sum : ℤ) - n + u := rfl
  obtain ⟨d, hd, hEd⟩ : ∃ d : ℕ, d ≤ 2 ∧ E = ((u + Sa + d : ℕ) : ℤ) := by
    have h1 := Bd_sum_sub T.loops
    refine ⟨(if T.kk 0 = 0 then 1 else 0) + (if T.kk 1 = 0 then 1 else 0) -
      T.loops.countP (fun w => decide (w.countP Bd_isRes = 0)), ?_, ?_⟩
    · split_ifs <;> omega
    · rw [hE, hs2]
      split_ifs at hZ ⊢ <;> omega
  set Tt : ℝ := max 1 τ⁻¹ with hTt
  have hTt1 : 1 ≤ Tt := le_max_left _ _
  set QL : ℝ := 2 + 4 * |K| with hQL
  set Cbig : ℝ := Bd_cw D K Ltot with hCbig
  have hCbig0 : 0 ≤ Cbig := le_trans zero_le_one (Bd_cw_ge D hD1 K Ltot).2.2.2
  set C₁ : ℝ := (D : ℝ) ^ T.dexp * (D : ℝ) ^ T.nb * Cbig ^ n * Tt ^ 2 with hC₁
  set Cb : ℝ := (D : ℝ) ^ T.dexp * (D : ℝ) ^ T.nb * 2 ^ u * QL ^ 2 * ((D : ℝ) ^ T.nb * (u + n))
    with hCb
  set τ'' : ℝ := τ' / (2 * ((u : ℝ) + n + 1)) with hτ''def
  have hτ'' : 0 < τ'' := by positivity
  have hττ : τ'' * (u + n) ≤ τ' / 2 := by
    rw [hτ''def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set Dn : ℕ := u + Ltot + (T.S + u + E.natAbs) + 1 with hDn
  have hDn0 : (0 : ℝ) < (Dn : ℝ) := by positivity
  have hW := Bd_weight D hD1 δA τ C₀ hδA hτ hC₀ C τ'' hτ'' Dn hDn0
  have hL := (Filter.eventually_all_finset T.loops.toFinset).mpr fun w hw =>
    Bd_loop D hD1 δA τ c₀ C₀ K hδA hτ hc₀ hC₀ C w (hwf2 w (List.mem_toFinset.mp hw)) τ'' hτ''
      Dn hDn0
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hW.and hL)
  obtain ⟨N₂, hN₂⟩ := Bd_large (τ' / 2) (2 * C₁) (by positivity)
  obtain ⟨N₃, hN₃⟩ := Bd_large 1 (2 * Cb * Tt ^ E.natAbs) one_pos
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN μ hμ e hA hA2 hc hz hδ => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hWN, hLN⟩ := hN₁ N hNa
  have hlarge1 := hN₂ N hNb
  have hlarge2 : 2 * Cb * Tt ^ E.natAbs ≤ N := by simpa using hN₃ N hNc
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hx : (μ, e) ∈ Bd_Cl D δA C₀ K C N := ⟨hμ, hA, hA2, hc, hδ⟩
  obtain ⟨hA1, hM, hLt, hη, hηz, -⟩ := Bd_facts hD1 (by omega) hC₀ hx hz
  have hM' : ∀ a, opNorm (e.M a) ≤ 5 / 4 := hM
  have hLt' : opNorm e.Lt ≤ QL * opNorm e.A := hLt
  have hη' : 0 < Bd_eta e := hη
  have hηz' : ∀ a, Bd_eta e ≤ (e.z a).im := hηz
  have hA0 := Bd_opNorm_nonneg e.A
  have := hμ.prob
  -- `|Im z_a| ≥ N⁻¹` and `η ≤ T`
  have hzN : ∀ a, (N : ℝ)⁻¹ ≤ |(e.z a).im| := by
    intro a
    refine le_trans ?_ (hz a).1.2
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hηT : Bd_eta e ≤ Tt := by
    refine (hηz' 0).trans ((Complex.im_le_norm _).trans ((hz 0).1.1.trans ?_))
    exact le_max_right _ _
  have hη1 : (N : ℝ)⁻¹ ≤ Bd_eta e := by
    unfold Bd_eta
    refine le_min ?_ ?_
    · have := hzN 0; rwa [abs_of_pos (hz 0).2.1] at this
    · have := hzN 1; rwa [abs_of_pos (hz 1).2.1] at this
  -- the events
  have hWb : ∀ (ι : Fin T.nb → Fin D) (i : Fin u), ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Dn : ℝ))) ∧ ∀ h, h ∉ bad →
        ‖ntr ((e.G h (T.weights.get i).1 - e.M (T.weights.get i).1) *
          e.E ι (T.weights.get i).2)‖ ≤
          (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |(e.z (T.weights.get i).1).im|)) :=
    fun ι i => hWN μ hμ e hA hc (fun a => (hz a).1) _ _ (Bd_opNorm_E e ι _)
  choose bW hbW1 hbW2 using hWb
  have hLb : ∀ (ι : Fin T.nb → Fin D) (i : Fin n), ∃ bad : Set (Idx D N → Idx D N → ℂ),
      μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(Dn : ℝ))) ∧ ∀ h, (Matrix.of h).IsHermitian → h ∉ bad →
        ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt (T.loops.get i))‖ ≤
          Bd_cw D K (T.loops.get i).length * (N : ℝ) ^ τ'' *
            (Bd_eta e)⁻¹ ^ ((T.loops.get i).countP Bd_isRes - 1) *
            opNorm e.A ^ ((T.loops.get i).countP Bd_isL) :=
    fun ι i => hLN (T.loops.get i) (List.mem_toFinset.mpr (List.get_mem _ _)) (μ, e) hx hz
      (e.E ι) (Bd_opNorm_E e ι)
  choose bL hbL1 hbL2 using hLb
  set bad : Set (Idx D N → Idx D N → ℂ) := ⋃ ι, ((⋃ i, bW ι i) ∪ ⋃ i, bL ι i) with hbad
  have hNDn : 0 ≤ (N : ℝ) ^ (-(Dn : ℝ)) := by positivity
  have hmbad : μ.real bad ≤ (D : ℝ) ^ T.nb * (u + n) * (N : ℝ) ^ (-(Dn : ℝ)) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    have hι : ∀ ι : Fin T.nb → Fin D, μ.real ((⋃ i, bW ι i) ∪ ⋃ i, bL ι i) ≤
        ((u : ℝ) + n) * (N : ℝ) ^ (-(Dn : ℝ)) := by
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
  -- the two pointwise bounds
  set RHS : ℝ := (N : ℝ) ^ τ' * ((N : ℝ) ^ (-T.size.1) *
    min (e.z 0).im (e.z 1).im ^ (-(T.size.2 + (if T.kk 0 = 0 then 1 else 0) +
      (if T.kk 1 = 0 then 1 else 0))) * opNorm e.A ^ 2) with hRHS
  have hRHS' : RHS = (N : ℝ) ^ τ' * ((N : ℝ) ^ (-((T.S : ℤ) + u)) * Bd_eta e ^ (-E) *
      opNorm e.A ^ 2) := by rw [hRHS, hs1]; rfl
  set Rb : ℝ := (D : ℝ) ^ T.dexp * ((N : ℝ) ^ T.S)⁻¹ * ((D : ℝ) ^ T.nb * ((2 * (N : ℝ)) ^ u *
      (1 ^ n * (N : ℝ) ^ Ltot * (QL * opNorm e.A) ^ 2))) with hRb
  have hcrude : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ‖T.evalH e h‖ ≤ Rb := by
    intro h hh
    have hG : ∀ a, opNorm (e.G h a) ≤ N := by
      intro a
      refine (Bd_G_norm e h hh a (hz a).2.1.ne').trans ?_
      rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (hzN a)) (by positivity)]
      exact hzN a
    have h1 := Bd_evalH_le T e h (2 * N) 1 N (QL * opNorm e.A) (by positivity)
      List.length (List.countP Bd_isL) (fun ι p _ => by
        refine (Bd_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
        have h1 := Bd_opNorm_sub (e.G h p.1) (e.M p.1)
        have h2 := hG p.1
        have h3 := hM' p.1
        have h0 := Bd_opNorm_nonneg (e.G h p.1 - e.M p.1)
        calc opNorm (e.G h p.1 - e.M p.1) * opNorm (e.E ι p.2)
            ≤ opNorm (e.G h p.1 - e.M p.1) * 1 :=
              mul_le_mul_of_nonneg_left (Bd_opNorm_E e ι p.2) h0
          _ ≤ 2 * N := by linarith)
      (fun ι w _ => by
        refine (Bd_ntr_le _).trans ?_
        rw [one_mul]
        exact Bd_prod_normL w _ N (QL * opNorm e.A) (by linarith) (by positivity) fun y _ => by
          cases y with
          | res a => simpa [Bd_isL, Bd_let] using hG a
          | det a => simpa [Bd_isL, Bd_let] using (hM' a).trans (by linarith)
          | proj y => simpa [Bd_isL, Bd_let] using (Bd_opNorm_E e ι y).trans (by linarith)
          | lamt o => simpa [Bd_isL, Bd_let] using hLt')
    rw [hsumL] at h1
    exact h1
  have hgood : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → h ∉ bad →
      ‖T.evalH e h‖ ≤ 1 / 2 * RHS := by
    intro h hh hb
    have hbW : ∀ ι i, h ∉ bW ι i := fun ι i hm =>
      hb (Set.mem_iUnion.mpr ⟨ι, Or.inl (Set.mem_iUnion.mpr ⟨i, hm⟩)⟩)
    have hbL : ∀ ι i, h ∉ bL ι i := fun ι i hm =>
      hb (Set.mem_iUnion.mpr ⟨ι, Or.inr (Set.mem_iUnion.mpr ⟨i, hm⟩)⟩)
    have h1 := Bd_evalH_le T e h ((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * (Bd_eta e)⁻¹))
      (Cbig * (N : ℝ) ^ τ'') (Bd_eta e)⁻¹ (opNorm e.A) (by positivity)
      (fun w => w.countP Bd_isRes - 1) (List.countP Bd_isL) (fun ι p hp => by
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
        refine (hbW2 ι i h (hbW ι i)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hzi := hηz' (T.weights.get i).1
        have hzp := (hz (T.weights.get i).1).2.1
        rw [abs_of_pos hzp, one_div, mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hη' hzi) (by positivity))
      (fun ι w hw => by
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
        refine (hbL2 ι i h hh (hbL ι i)).trans ?_
        have hlen : (T.loops.get i).length ≤ Ltot :=
          List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem _ _))
        have hcw := Bd_cw_mono D K hlen
        gcongr)
    rw [hsumL] at h1
    refine h1.trans ?_
    rw [hRHS']
    exact Bd_good_arith D N (by omega) T.dexp T.S T.nb u n Sa d Cbig Tt (Bd_eta e) τ' τ''
      (opNorm e.A) E hd hEd hη' hηT hTt1 hCbig0 hττ hlarge1
  have hRb0 : 0 ≤ Rb := by positivity
  have hRHS0 : 0 ≤ RHS := by
    rw [hRHS']
    have := Bd_zpow_lower (Bd_eta e) Tt N hη' hTt1 (by linarith) hη1 hηT (-E)
    have h2 : 0 ≤ (N : ℝ) ^ (-((T.S : ℤ) + u)) := by positivity
    have h3 : 0 ≤ Bd_eta e ^ (-E) := le_trans (by positivity) this
    positivity
  -- integrate
  have hpt : ∀ᵐ h ∂μ, ‖T.evalH e h‖ ≤
      1 / 2 * RHS + (toMeasurable μ bad).indicator (fun _ => Rb) h := by
    filter_upwards [hμ.herm] with h hh
    by_cases hb : h ∈ toMeasurable μ bad
    · rw [Set.indicator_of_mem hb]
      exact (hcrude h hh).trans (by linarith)
    · rw [Set.indicator_of_notMem hb, add_zero]
      exact hgood h hh fun h' => hb (subset_toMeasurable _ _ h')
  have hint : Integrable (fun h => 1 / 2 * RHS + (toMeasurable μ bad).indicator (fun _ => Rb) h)
      μ := (integrable_const _).add
        ((integrable_const Rb).indicator (measurableSet_toMeasurable _ _))
  refine (norm_integral_le_of_norm_le hint hpt).trans ?_
  rw [integral_add (integrable_const _)
    ((integrable_const Rb).indicator (measurableSet_toMeasurable _ _)), integral_const,
    integral_indicator_const _ (measurableSet_toMeasurable _ _), probReal_univ, one_smul,
    smul_eq_mul]
  have hreal : μ.real (toMeasurable μ bad) = μ.real bad := by
    simp only [Measure.real, measure_toMeasurable]
  rw [hreal]
  have hbadb : μ.real bad * Rb ≤ 1 / 2 * RHS := by
    rw [mul_comm, hRHS']
    exact Bd_bad_arith D N (by omega) T.dexp T.S T.nb u n Ltot Dn QL Tt (Bd_eta e) τ'
      (opNorm e.A) (μ.real bad) E hDn hη' hη1 hηT hTt1 hτ' measureReal_nonneg hmbad hlarge2
  linarith


end RBMTransitionEdge

end
