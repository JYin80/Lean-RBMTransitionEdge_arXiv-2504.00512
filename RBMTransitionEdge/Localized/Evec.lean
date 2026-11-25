module

public import RBMTransitionEdge.Localized.Pathwise
public import RBMTransitionEdge.Localized.QuantIncrement
public import RBMTransitionEdge.Localized.Reflect
public import RBMTransitionEdge.Localized.Repulsion
public import RBMTransitionEdge.Localized.LocalLaw

@[expose] public section

/-!
# Theorem 2.4 on the half range

Theorem 2.4 [theorem_localized_eigenvector_localization] for `2k ≤ DN + 1`: the eigenvector `u_k`
of `H_Λ` is localized in one block off an event of small probability, from Lemma 5.2
[lemma_localized_eigenvector_local_law], the pathwise mass bound off the block, rigidity and the
repulsion between the blocks (EI-2).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Im G = η G G^*` for `G = (X - z)⁻¹`, `X` Hermitian and `Im z = η > 0`. -/
private lemma Evec_imRes_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    imRes X z = (z.im : ℂ) • (res X z * (res X z)ᴴ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub X hX z hz
  set G := res X z
  have h3 : (X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * Gᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, Matrix.conjTranspose_sub,
      hX.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at this
    simpa using this
  have key : G - Gᴴ = (z - starRingEnd ℂ z) • (G * Gᴴ) := by
    have e1 : G * ((X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * Gᴴ) = G := by
      rw [h3, Matrix.mul_one]
    have e2 : G * ((X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * Gᴴ) =
        Gᴴ + (z - starRingEnd ℂ z) • (G * Gᴴ) := by
      have : X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) =
          (X - z • (1 : Matrix ι ι ℂ)) + (z - starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) := by
        rw [sub_smul]; abel
      rw [this, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, h2, Matrix.one_mul,
        Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
    calc G - Gᴴ = (Gᴴ + (z - starRingEnd ℂ z) • (G * Gᴴ)) - Gᴴ := by rw [← e2, e1]
      _ = (z - starRingEnd ℂ z) • (G * Gᴴ) := by abel
  unfold imRes
  rw [key, smul_smul]
  congr 1
  rw [Complex.sub_conj]
  push_cast
  field_simp

open scoped ComplexOrder in
/-- `Re ⟨Im G B Im G' B⟩ ≥ 0` for Hermitian `B`, `X`, `Y` and `Im z, Im z' > 0`, with
`G = (X - z)⁻¹`, `G' = (Y - z')⁻¹`. -/
private lemma Evec_re_ntr_nonneg (X Y B : Matrix ι ι ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hB : B.IsHermitian) (z z' : ℂ) (hz : 0 < z.im) (hz' : 0 < z'.im) :
    0 ≤ (ntr (imRes X z * B * imRes Y z' * B)).re := by
  rw [Evec_imRes_eq X hX z hz, Evec_imRes_eq Y hY z' hz']
  set G := res X z
  set G' := res Y z'
  set M := G'ᴴ * B * G
  have hM : Mᴴ * M = Gᴴ * B * G' * (G'ᴴ * B * G) := by
    simp only [M, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hB.eq,
      Matrix.mul_assoc]
  have htr : ((z.im : ℂ) • (G * Gᴴ) * B * ((z'.im : ℂ) • (G' * G'ᴴ)) * B).trace =
      ((z.im * z'.im : ℝ) : ℂ) * (Mᴴ * M).trace := by
    rw [hM]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have : (G * Gᴴ * B * (G' * G'ᴴ) * B).trace = (Gᴴ * B * G' * (G'ᴴ * B * G)).trace := by
      rw [show G * Gᴴ * B * (G' * G'ᴴ) * B = G * (Gᴴ * B * G' * (G'ᴴ * B)) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this]; push_cast; ring
  have hpos : 0 ≤ (Mᴴ * M).trace := (posSemidef_conjTranspose_mul_self M).trace_nonneg
  have hre : 0 ≤ (Mᴴ * M).trace.re := (Complex.nonneg_iff.mp hpos).1
  unfold ntr
  rw [htr, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hz.le hz'.le)) hre

/-- For a Hermitian `W` whose eigenvalues are all at distance `≥ w₀ ≥ 0` from `x`,
`‖(W - x) v‖² ≥ w₀² ‖v‖²` for every `v`. -/
private lemma Evec_sep_of_far (W : Matrix ι ι ℂ) (hW : W.IsHermitian) (x w₀ : ℝ) (hw₀ : 0 ≤ w₀)
    (h : ∀ j, w₀ ≤ |hW.eigenvalues₀ j - x|) (v : ι → ℂ) :
    w₀ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤ ∑ i, ‖((W - (x : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v) i‖ ^ 2 := by
  set hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hW
  set b := hT.eigenvectorBasis finrank_euclideanSpace
  set z : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hn1 : ∑ i, ‖v i‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have hTz : Matrix.toEuclideanLin W z - (x : ℂ) • z =
      WithLp.toLp 2 ((W - (x : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hn2 : ∑ i, ‖((W - (x : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v) i‖ ^ 2 =
      ‖Matrix.toEuclideanLin W z - (x : ℂ) • z‖ ^ 2 := by
    rw [hTz, EuclideanSpace.norm_sq_eq]
  rw [hn1, hn2, ← b.sum_sq_norm_inner_right z, ← b.sum_sq_norm_inner_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : inner ℂ (b j) (Matrix.toEuclideanLin W z - (x : ℂ) • z) =
      ((hW.eigenvalues₀ j - x : ℝ) : ℂ) * inner ℂ (b j) z := by
    rw [inner_sub_right, inner_smul_right, ← hT (b j), hT.apply_eigenvectorBasis, inner_smul_left]
    have : hT.eigenvalues finrank_euclideanSpace j = hW.eigenvalues₀ j := rfl
    rw [this, RCLike.conj_ofReal]
    change ((hW.eigenvalues₀ j : ℝ) : ℂ) * inner ℂ (b j) z - (x : ℂ) * inner ℂ (b j) z = _
    push_cast
    ring
  rw [hj, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h1 := h j
  have h2 : w₀ ^ 2 ≤ (hW.eigenvalues₀ j - x) ^ 2 := by
    rw [← sq_abs (hW.eigenvalues₀ j - x)]
    exact pow_le_pow_left₀ hw₀ h1 2
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

end Aux

/-- If `‖(W - x) v‖² < w₀² ‖v‖²` for a Hermitian `N × N` matrix `W` and some `v`, then some
eigenvalue `λ_i(W)`, `i ∈ ⟦1, N⟧`, satisfies `|λ_i(W) - x| < w₀`. -/
private lemma Evec_eig_near (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (x w₀ : ℝ) (hw₀ : 0 ≤ w₀) (v : Fin N → ℂ)
    (hv : ∑ i, ‖((W - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v) i‖ ^ 2 <
      w₀ ^ 2 * ∑ i, ‖v i‖ ^ 2) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧ |eigK W i - x| < w₀ := by
  by_contra hne
  push Not at hne
  refine absurd (Evec_sep_of_far W hW x w₀ hw₀ (fun j => ?_) v) (not_le.mpr hv)
  have hjN : j.val < N := by simpa using j.isLt
  have hj := hne (j.val + 1) (by omega) (by omega)
  have he : eigK W (j.val + 1) = hW.eigenvalues₀ j := by
    simp [eigK, eigs, hW, hjN]
  rwa [he] at hj

/-- The Wigner matrix `wig n w` is Hermitian. -/
private lemma Evec_wig_isHermitian (n : ℕ) (w : Coords n) : (wig n w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- The block-diagonal matrix `H` of (1.3) [matrix_H] is Hermitian. -/
private lemma Evec_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (Evec_wig_isHermitian N (w q.1)).apply p.2 q.2
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- `Λ - c` is Hermitian for real `c`. -/
private lemma Evec_shift_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    (lam D N A - (c : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)).IsHermitian := by
  have h1 : ((c : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp
  exact (lam_isHermitian D N A).sub h1

/-- The integrand `⟨Im G₀ Λ̃ Im G₁ Λ̃⟩` of (5.9) [estimate_localized_eigenvector_local_law] is
nonnegative at every point when `η > 0`. -/
private lemma Evec_loop_nonneg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ)
    (hη : 0 < etaK D N k ε) (w : Fin D → Coords N) : 0 ≤ evecLoop D N A k ε w := by
  unfold evecLoop
  refine Evec_re_ntr_nonneg _ _ _ (Evec_blockH_isHermitian D N w) (HLam_isHermitian D N A w)
    (Evec_shift_isHermitian D N A _) _ _ ?_ ?_
  · simpa [zOne] using hη
  · simpa [zOne] using hη

/-- The map from the block coordinates to the array of `H` is measurable. -/
private lemma Evec_meas_blockH (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
  have : Continuous fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
    refine continuous_pi fun p => continuous_pi fun q => ?_
    change Continuous fun w : Fin D → Coords N => blockH D N w p q
    simp only [blockH, wig]
    split_ifs <;> fun_prop
  exact this.measurable

/-- `N^a ≥ c` for all large `N`, when `a > 0`. -/
private lemma Evec_ev (c a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop c)

/-- `K N^{-a} ≤ N^{-e}/3` for `N ≥ 1`, `K ≥ 0`, `e + s ≤ a` and `3K ≤ N^s`. -/
private lemma Evec_small (N K a e s : ℝ) (hN : 1 ≤ N) (hK : 0 ≤ K) (hae : e + s ≤ a)
    (h3 : 3 * K ≤ N ^ s) : K * N ^ (-a) ≤ N ^ (-e) / 3 := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < N ^ s := Real.rpow_pos_of_pos hN0 s
  have h1 : N ^ (-a) ≤ N ^ (-e) * (N ^ s)⁻¹ := by
    rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h2 : K * (N ^ s)⁻¹ ≤ 1 / 3 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs]; linarith
  have he : 0 ≤ N ^ (-e) := (Real.rpow_pos_of_pos hN0 _).le
  calc K * N ^ (-a) ≤ K * (N ^ (-e) * (N ^ s)⁻¹) := mul_le_mul_of_nonneg_left h1 hK
    _ = N ^ (-e) * (K * (N ^ s)⁻¹) := by ring
    _ ≤ N ^ (-e) * (1 / 3) := mul_le_mul_of_nonneg_left h2 he
    _ = N ^ (-e) / 3 := by ring

/-- Under (2.8) [eq:condA2], the threshold of (2.9) [eq:main_evector2] at `ε = ε_A` is small:
`N^{-2/3+ε_A} 𝔯(k)^{2/3} ‖A‖²_HS ≤ N^{-ε_A}`. -/
private lemma Evec_theta_le (D N k : ℕ) (hN : 1 ≤ N) (hr : 0 < rk D N k) (εA : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (hhs : hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ))) :
    (N : ℝ) ^ (-(2 / 3 : ℝ) + εA) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 ≤ (N : ℝ) ^ (-εA) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set r := rk D N k
  have hs2 : hsNorm A ^ 2 ≤ ((N : ℝ) ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hhs 2
  have e1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + εA) * (N : ℝ) ^ ((1 / 3 : ℝ) - εA) *
      (N : ℝ) ^ ((1 / 3 : ℝ) - εA) = (N : ℝ) ^ (-εA) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  have e2 : r ^ (2 / 3 : ℝ) * r ^ (-(1 / 3 : ℝ)) * r ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]; norm_num
  have hpos : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εA) * r ^ (2 / 3 : ℝ) := by positivity
  calc (N : ℝ) ^ (-(2 / 3 : ℝ) + εA) * r ^ (2 / 3 : ℝ) * hsNorm A ^ 2
      ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εA) * r ^ (2 / 3 : ℝ) *
          ((N : ℝ) ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_left hs2 hpos
    _ = ((N : ℝ) ^ (-(2 / 3 : ℝ) + εA) * (N : ℝ) ^ ((1 / 3 : ℝ) - εA) *
          (N : ℝ) ^ ((1 / 3 : ℝ) - εA)) * (r ^ (2 / 3 : ℝ) * r ^ (-(1 / 3 : ℝ)) *
          r ^ (-(1 / 3 : ℝ))) := by ring
    _ = (N : ℝ) ^ (-εA) := by rw [e1, e2, mul_one]

/-- The first bound of Theorem 2.4 [theorem_localized_eigenvector_localization] for
`2k ≤ DN + 1`, for every `ε > 0`: off an event of probability at most `N^{-ε₀}`, every unit
eigenvector `u` of `λ_k` has `‖E_a u‖² ≥ 1 - N^{-2/3+ε} k^{2/3} ‖A‖²_HS` for some block `a`.
The exceptional event lies in the union of the failure of rigidity (2.24) [eq:rigidity], the event
(5.11) [eq:probab12] for some pair of blocks, and the event where the bound (5.18)
[localized_bound_eigenvector_general_D] of the off-block mass exceeds the threshold, whose
probability is bounded by Markov's inequality and (5.9)
[estimate_localized_eigenvector_local_law]. -/
private lemma Evec_first (hEI : ∀ C : ℕ → ℝ, EI2Hyp C) (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ)
    (hδA : 0 < δA) (hεA : 0 < εA) (C : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
          ∀ a : Fin D, blockMass u a <
            1 - (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ε₀)) := by
  -- the constants, all fixed before `N`
  obtain ⟨C₅, hC₅, ε₁, hε₁, hLL⟩ := localized_eigenvector_local_law D hD δA εA hδA hεA C
  set δ : ℝ := ε / 16 with hδ
  have hδ0 : 0 < δ := by positivity
  set εL : ℝ := min (min (ε / (8 * (C₅ + 2))) (ε₁ / 2)) (min (εA / 2) (1 / 2)) with hεL
  have hεL0 : 0 < εL :=
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by norm_num))
  have hεLa : εL ≤ ε / (8 * (C₅ + 2)) := (min_le_left _ _).trans (min_le_left _ _)
  have hεLb : εL < ε₁ := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hεLc : εL < εA := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεLd : εL < 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hεL5 : C₅ * εL + 2 * εL ≤ ε / 8 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (C₅ + 2))).mp hεLa
    have h8 : εL * (8 * (C₅ + 2)) = 8 * (C₅ * εL + 2 * εL) := by ring
    rw [h8] at h
    linarith
  obtain ⟨δ₀, hδ₀, τ₀, hτ₀, hBR⟩ := blocks_repulsion C (hEI C) D hD δ hδ0
  set τ' : ℝ := min εL τ₀ / 2 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'L : τ' ≤ εL := by
    have h1 := min_le_left εL τ₀
    have h2 : 0 < min εL τ₀ := lt_min hεL0 hτ₀
    linarith
  have hτ'τ : τ' ≤ τ₀ / 2 := by have := min_le_right εL τ₀; linarith
  set ε₀ : ℝ := min (ε / 2) (δ₀ / 2) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀a : ε₀ ≤ ε / 2 := min_le_left _ _
  have hε₀b : ε₀ ≤ δ₀ / 2 := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := hLL εL hεL0 hεLb (ε / 16) (by positivity)
  obtain ⟨N₂, hN₂⟩ := rigidity D (by omega) δA hδA C τ' hτ'0 ε hε
  obtain ⟨Csh, -, N₃, hN₃⟩ := modification_shift_eigenvector D hD δA εA εL hδA hεA hεL0 hεLd
  obtain ⟨N₄, hN₄⟩ := hBR τ₀ hτ₀ le_rfl
  obtain ⟨N₅, hN₅⟩ := Evec_ev (3 * (10 * D)) (3 * ε / 16) (by positivity)
  obtain ⟨N₆, hN₆⟩ := Evec_ev 3 (τ₀ / 2) (by positivity)
  obtain ⟨N₇, hN₇⟩ := Evec_ev (3 * ((D : ℝ) * D)) (δ₀ / 2) (by positivity)
  obtain ⟨N₈, hN₈⟩ := Evec_ev (3 * 1) (ε / 2) (by positivity)
  refine ⟨ε₀, hε₀0, max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max (max N₇ N₈) 1)),
    ?_⟩
  intro N hN L A hA k hk hkN hhs
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN₁', hN₂'⟩, hN₃', hN₄'⟩, ⟨hN₅', hN₆'⟩, ⟨hN₇', hN₈'⟩, hN1⟩ := hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hkDN : k ≤ D * N := by omega
  have hrk : rk D N k = (k : ℝ) := by
    unfold rk
    rw [min_eq_left (by omega)]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hrk0 : 0 ≤ rk D N k := by rw [hrk]; exact hk0.le
  set P := blockLaw D N L with hP
  have : IsProbabilityMeasure P := blockLaw_isProbabilityMeasure D N L
  set Λ := lam D N A with hΛ
  set γ := quant (rho Λ) (D * N) k with hγ
  set γsc := quant rhoSc (D * N) k with hγsc
  set η := etaK D N k εL with hη
  set Δ := shiftEv Λ (zOne Λ k εL) with hΔ
  set κ : ℝ := (k : ℝ) ^ (-(1 / 3 : ℝ)) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hk0 _
  set w₀ : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * κ with hw₀
  have hw₀0 : 0 < w₀ := mul_pos (Real.rpow_pos_of_pos hN0 _) hκ0
  set X : ℝ := (N : ℝ) ^ (εL + δ) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hX1 : 1 ≤ X := Real.one_le_rpow hNr (by linarith)
  have hηform : η = (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) * κ := by rw [hη, etaK, hrk]
  have hηX : η = X * w₀ := by
    have e : (N : ℝ) ^ (-(2 / 3 : ℝ) + εL) = X * (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) := by
      rw [hX, ← Real.rpow_add hN0]; ring_nf
    rw [hηform, e, hw₀]; ring
  have hη0 : 0 < η := by rw [hηX]; positivity
  set θ : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 with hθ
  set f := evecLoop D N A k εL with hf
  have hf0 : ∀ w, 0 ≤ f w := Evec_loop_nonneg D N A k εL hη0
  set c : ℝ := 10 * D * (N : ℝ) ^ (1 + 2 * (εL + δ)) with hc
  have hc0 : 0 < c := mul_pos (by positivity) (Real.rpow_pos_of_pos hN0 _)
  -- the three exceptional events
  set R : Set (Fin D → Coords N) := {w | ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ D * N ∧
      (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k' ^ (-(1 / 3 : ℝ))) <
        |eigK (HLam D N A w) k' - quant (rho Λ) (D * N) k'|} with hR
  set S : Fin D × Fin D → Set (Fin D → Coords N) := fun p => {w | p.1 ≠ p.2 ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i ≤ N ∧ 1 ≤ j ∧ j ≤ N ∧
        |eigK (wig N (w p.2)) j - γsc| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ₀) * κ ∧
        |eigK (wig N (w p.1)) i - eigK (wig N (w p.2)) j| ≤
          2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * κ} with hS
  set T : Set (Fin D → Coords N) := ⋃ p, S p with hT
  set M : Set (Fin D → Coords N) := {w | θ < c * f w} with hM
  -- rigidity, (2.24) [eq:rigidity]
  have hRb : P R ≤ ENNReal.ofReal ((N : ℝ) ^ (-ε)) := by
    refine le_trans (le_of_eq ?_) (le_trans (Measure.le_map_apply
      (Evec_meas_blockH D N).aemeasurable _)
      (hN₂ N hN₂' 1 zero_le_one le_rfl _ (llClass_blockH D N C L) A hA))
    rfl
  -- two blocks with nearby eigenvalues, (5.11) [eq:probab12]
  have hTb : P T ≤ ENNReal.ofReal ((D : ℝ) * D * (N : ℝ) ^ (-δ₀)) := by
    have hterm : ∀ p : Fin D × Fin D, P (S p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-δ₀)) := by
      intro p
      by_cases hp : p.1 = p.2
      · calc P (S p) ≤ P ∅ := measure_mono fun w hw => (hw.1 hp).elim
          _ = 0 := measure_empty
          _ ≤ _ := by simp
      · exact le_trans (measure_mono fun w hw => hw.2) (hN₄ N hN₄' L k hk hkDN p.1 p.2 hp)
    refine (measure_iUnion_fintype_le P S).trans ((Finset.sum_le_sum fun p _ => hterm p).trans
      (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    push_cast
    ring_nf
  -- Markov with Lemma 5.2 [lemma_localized_eigenvector_local_law]
  obtain ⟨hint, -, hEf⟩ := hN₁ N hN₁' L A hA k hk hkN hhs
  have hMb : P M ≤ ENNReal.ofReal (10 * D * (N : ℝ) ^ (-(11 * ε / 16))) := by
    rcases (show 0 ≤ θ from mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _)
        (Real.rpow_nonneg hrk0 _)) (sq_nonneg _)).lt_or_eq with hθ0 | hθ0
    · have hsub : M ⊆ {w | θ / c ≤ f w} := fun w hw => by
        have hw' : θ < c * f w := hw
        change θ / c ≤ f w
        rw [div_le_iff₀ hc0]
        linarith
      have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hf0) hint (θ / c)
      have e1 : (N : ℝ) ^ (ε / 16 + C₅ * εL) * (N : ℝ) ^ (-(5 / 3 : ℝ)) *
          (N : ℝ) ^ (1 + 2 * (εL + δ)) ≤
          (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(11 * ε / 16)) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by rw [hδ]; linarith)
      have hK : 0 ≤ 10 * D * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 :=
        mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hrk0 _)) (sq_nonneg _)
      have key : (N : ℝ) ^ (ε / 16 + C₅ * εL) *
          ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) * c ≤
          θ * (10 * D * (N : ℝ) ^ (-(11 * ε / 16))) := by
        calc (N : ℝ) ^ (ε / 16 + C₅ * εL) *
              ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) * c
            = (10 * D * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) *
              ((N : ℝ) ^ (ε / 16 + C₅ * εL) * (N : ℝ) ^ (-(5 / 3 : ℝ)) *
                (N : ℝ) ^ (1 + 2 * (εL + δ))) := by rw [hc]; ring
          _ ≤ (10 * D * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) *
              ((N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(11 * ε / 16))) :=
            mul_le_mul_of_nonneg_left e1 hK
          _ = θ * (10 * D * (N : ℝ) ^ (-(11 * ε / 16))) := by rw [hθ]; ring
      have hpos : 0 < θ / c := div_pos hθ0 hc0
      have hreal : P.real {w | θ / c ≤ f w} ≤ 10 * D * (N : ℝ) ^ (-(11 * ε / 16)) := by
        refine le_of_mul_le_mul_left ?_ hpos
        refine hmk.trans (hEf.trans ?_)
        rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
        linarith [key]
      calc P M ≤ P {w | θ / c ≤ f w} := measure_mono hsub
        _ = ENNReal.ofReal (P.real {w | θ / c ≤ f w}) := (ofReal_measureReal).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    · have hB0 : hsNorm A ^ 2 = 0 := by
        have h1 : (0 : ℝ) < (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) := by
          rw [hrk]
          exact mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hk0 _)
        rcases mul_eq_zero.mp hθ0.symm with h | h
        · exact absurd h h1.ne'
        · exact h
      have hint0 : ∫ w, f w ∂P = 0 :=
        le_antisymm (hEf.trans (by rw [hB0]; simp)) (integral_nonneg hf0)
      have hae := (integral_eq_zero_iff_of_nonneg hf0 hint).mp hint0
      have h0 : P M = 0 := by
        refine measure_mono_null (fun w hw => ?_) (ae_iff.mp hae)
        have hw' : θ < c * f w := hw
        change ¬ f w = (0 : (Fin D → Coords N) → ℝ) w
        intro h
        rw [h, ← hθ0] at hw'
        simp at hw'
      rw [h0]
      simp
  -- the event lies in the union of the three
  have hsubE : {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
      ∀ a : Fin D, blockMass u a < 1 - θ} ⊆ R ∪ T ∪ M := by
    rintro w ⟨u, hu, hmass⟩
    by_cases hwR : w ∈ R
    · exact Or.inl (Or.inl hwR)
    by_cases hwT : w ∈ T
    · exact Or.inl (Or.inr hwT)
    refine Or.inr ?_
    set μ := eigK (HLam D N A w) k with hμ
    have hrig : |μ - γ| ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * κ) := by
      by_contra hlt
      refine hwR ⟨k, hk, hkDN, ?_⟩
      rw [hrk]
      exact not_le.mp hlt
    have hμη : |μ - γ| ≤ η := by
      refine hrig.trans ?_
      rw [hηform, ← mul_assoc, ← Real.rpow_add hN0]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)) hκ0.le
    -- some block `a` is separated from `λ_k - Δ_ev` in every other block
    have hsep : ∃ a : Fin D, ∀ b : Fin D, b ≠ a → ∀ v : Fin N → ℂ,
        w₀ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
        ∑ i, ‖((wig N (w b) - ((μ - Δ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v) i‖ ^ 2 := by
      by_contra hns
      push Not at hns
      obtain ⟨b₁, hb₁, v₁, hv₁⟩ := hns ⟨0, by omega⟩
      obtain ⟨b₂, hb₂, v₂, hv₂⟩ := hns b₁
      obtain ⟨i, hi1, hiN, hi⟩ :=
        Evec_eig_near N _ (Evec_wig_isHermitian N (w b₁)) _ _ hw₀0.le v₁ hv₁
      obtain ⟨j, hj1, hjN, hj⟩ :=
        Evec_eig_near N _ (Evec_wig_isHermitian N (w b₂)) _ _ hw₀0.le v₂ hv₂
      have hsh := (hN₃ N hN₃' A hA k hk hkDN hhs).2.2 hεLc
      rw [hrk] at hsh
      have hwin : w₀ + (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * κ) +
          (N : ℝ) ^ (-(2 / 3 : ℝ) - εA) * κ ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ₀) * κ := by
        have hY : (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * κ) =
            (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) * κ := by
          rw [Real.rpow_add hN0]; ring
        have h1 : (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) ≤ (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
        have h2 : (N : ℝ) ^ (-(2 / 3 : ℝ) - εA) ≤ (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
        have h3 : 3 * (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ₀) := by
          have e : (N : ℝ) ^ (-(2 / 3 : ℝ) + τ₀) =
              (N : ℝ) ^ (τ₀ - τ') * (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) := by
            rw [← Real.rpow_add hN0]; ring_nf
          have h4 : 3 ≤ (N : ℝ) ^ (τ₀ - τ') :=
            (hN₆ N hN₆').trans (Real.rpow_le_rpow_of_exponent_le hNr (by linarith))
          rw [e]
          exact mul_le_mul_of_nonneg_right h4 (Real.rpow_pos_of_pos hN0 _).le
        have hsum : (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) + (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) +
            (N : ℝ) ^ (-(2 / 3 : ℝ) - εA) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ₀) := by linarith
        rw [hY, hw₀]
        calc (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * κ + (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) * κ +
              (N : ℝ) ^ (-(2 / 3 : ℝ) - εA) * κ
            = ((N : ℝ) ^ (-(2 / 3 : ℝ) - δ) + (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) +
              (N : ℝ) ^ (-(2 / 3 : ℝ) - εA)) * κ := by ring
          _ ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ₀) * κ := mul_le_mul_of_nonneg_right hsum hκ0.le
      apply hwT
      refine Set.mem_iUnion.mpr ⟨(b₁, b₂), fun h => hb₂ h.symm, i, j, hi1, hiN, hj1, hjN, ?_, ?_⟩
      · obtain ⟨hj₁, hj₂⟩ := abs_lt.mp hj
        obtain ⟨hr₁, hr₂⟩ := abs_le.mp hrig
        obtain ⟨hs₁, hs₂⟩ := abs_le.mp hsh
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · obtain ⟨hi₁, hi₂⟩ := abs_lt.mp hi
        obtain ⟨hj₁, hj₂⟩ := abs_lt.mp hj
        have : 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * κ = 2 * w₀ := by rw [hw₀]; ring
        rw [this]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    obtain ⟨a, ha⟩ := hsep
    have hoff := offblock_mass_le D N A w μ u hu Δ γ η w₀ hη0 hw₀0 hμη a ha
    -- the trace of (5.18) [localized_bound_eigenvector_general_D] is `DN` times the integrand
    have hz1 : zOne Λ k εL = (γ : ℂ) + (η : ℂ) * Complex.I := rfl
    have hz0 : zOne Λ k εL - (Δ : ℂ) = ((γ - Δ : ℝ) : ℂ) + (η : ℂ) * Complex.I := by
      rw [hz1]; push_cast; ring
    have hfw : f w = (ntr (imRes (blockH D N w) (((γ - Δ : ℝ) : ℂ) + (η : ℂ) * Complex.I) *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        imRes (HLam D N A w) ((γ : ℂ) + (η : ℂ) * Complex.I) *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re := by
      rw [← hz0, ← hz1]
      rfl
    have htr : (Matrix.trace (imRes (blockH D N w) (((γ - Δ : ℝ) : ℂ) + (η : ℂ) * Complex.I) *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        imRes (HLam D N A w) ((γ : ℂ) + (η : ℂ) * Complex.I) *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re = ((D : ℝ) * N) * f w := by
      rw [hfw]
      unfold ntr
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
      simp only [Fintype.card_prod, Fintype.card_fin]
      push_cast
      field_simp
    have hsum1 : ∑ b, blockMass u b = 1 := by
      have h := hu.2
      rw [Fintype.sum_prod_type] at h
      exact h
    have hsplit := Finset.add_sum_erase Finset.univ (fun b => blockMass u b) (Finset.mem_univ a)
    have hgt : θ < ∑ b ∈ Finset.univ.erase a, blockMass u b := by
      have := hmass a
      linarith
    have hX2 : 3 * η ^ 2 / w₀ ^ 2 = 3 * X ^ 2 := by
      rw [hηX, mul_pow]
      field_simp
    have hNX : (N : ℝ) ^ (1 + 2 * (εL + δ)) = N * X ^ 2 := by
      have e : X ^ 2 = (N : ℝ) ^ (2 * (εL + δ)) := by
        rw [sq, hX, ← Real.rpow_add hN0]; ring_nf
      rw [e, Real.rpow_add hN0, Real.rpow_one]
    have hDNf : 0 ≤ (D : ℝ) * N * f w := mul_nonneg (by positivity) (hf0 w)
    change θ < c * f w
    calc θ < _ := hgt
      _ ≤ _ := hoff
      _ = 2 * (2 + 3 * X ^ 2) * ((D : ℝ) * N * f w) := by rw [htr, hX2]
      _ ≤ 10 * X ^ 2 * ((D : ℝ) * N * f w) :=
        mul_le_mul_of_nonneg_right (by linarith [one_le_pow₀ (n := 2) hX1]) hDNf
      _ = c * f w := by rw [hc, hNX]; ring
  -- the total
  have s1 := Evec_small N 1 ε ε₀ (ε / 2) hNr zero_le_one (by linarith) (hN₈ N hN₈')
  have s2 := Evec_small N ((D : ℝ) * D) δ₀ ε₀ (δ₀ / 2) hNr (by positivity) (by linarith)
    (hN₇ N hN₇')
  have s3 := Evec_small N (10 * D) (11 * ε / 16) ε₀ (3 * ε / 16) hNr (by positivity)
    (by linarith) (hN₅ N hN₅')
  have hfinal : (N : ℝ) ^ (-ε) + (D : ℝ) * D * (N : ℝ) ^ (-δ₀) +
      10 * D * (N : ℝ) ^ (-(11 * ε / 16)) ≤ (N : ℝ) ^ (-ε₀) := by linarith
  calc P {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
        ∀ a : Fin D, blockMass u a < 1 - θ}
      ≤ P (R ∪ T ∪ M) := measure_mono hsubE
    _ ≤ P R + P T + P M :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-ε)) + ENNReal.ofReal ((D : ℝ) * D * (N : ℝ) ^ (-δ₀)) +
        ENNReal.ofReal (10 * D * (N : ℝ) ^ (-(11 * ε / 16))) :=
        add_le_add (add_le_add hRb hTb) hMb
    _ = ENNReal.ofReal ((N : ℝ) ^ (-ε) + (D : ℝ) * D * (N : ℝ) ^ (-δ₀) +
        10 * D * (N : ℝ) ^ (-(11 * ε / 16))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-ε₀)) := ENNReal.ofReal_le_ofReal hfinal

/-- Theorem 2.4 [theorem_localized_eigenvector_localization] for `2k ≤ DN + 1`, with the level
repulsion (5.14) [Wegner12] as an explicit hypothesis. -/
theorem localized_evec_half (hEI : ∀ C : ℕ → ℝ, EI2Hyp C) : LocalizedEvecHalf := by
  intro D hD δA εA hδA hεA C
  refine ⟨fun ε hε _ => Evec_first hEI D hD δA εA hδA hεA C ε hε, ?_⟩
  obtain ⟨ε₀, hε₀, N₀, hN₀⟩ := Evec_first hEI D hD δA εA hδA hεA C εA hεA
  refine ⟨min (εA / 2) ε₀, lt_min (by positivity) hε₀, max N₀ 2,
    fun N hN L A hA k hk hkN hhs => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hr : 0 < rk D N k := by
    unfold rk
    rw [min_eq_left (by omega)]
    exact_mod_cast hk
  have hθ := Evec_theta_le D N k (by omega) hr εA A hhs
  have hlt : (N : ℝ) ^ (-εA) < (N : ℝ) ^ (-min (εA / 2) ε₀) :=
    Real.rpow_lt_rpow_of_exponent_lt hNr (by have := min_le_left (εA / 2) ε₀; linarith)
  refine le_trans (measure_mono ?_) ((hN₀ N (le_trans (le_max_left _ _) hN) L A hA k hk hkN
    hhs).trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hNr.le
    (neg_le_neg (min_le_right _ _)))))
  rintro w ⟨u, hu, hm⟩
  exact ⟨u, hu, fun a => by linarith [hm a]⟩

end RBMTransitionEdge

end
