module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Edge
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Det.Density
public import RBMTransitionEdge.Tools.Resolvent
public import RBMTransitionEdge.Tools.ResolventIdentities
public import RBMTransitionEdge.Tools.MinMax

@[expose] public section

/-!
# Counting eigenvalues

The Poisson-smoothed count, counting from the averaged local law (2.23) [eq:aver_local], rigidity
(2.24) [eq:rigidity] from counting with (2.21) [eq:kappa_gamma_k], the block traces of the
resolvent of the block-diagonal matrix of (1.3) [matrix_H], and the quantile shift of (5.13)
[eq:gammak2].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The number of eigenvalues of `X` in `[a, b]`. -/
def evCount {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (a b : ℝ) : ℕ :=
  (Finset.univ.filter fun k : Fin (Fintype.card ι) => a ≤ eigs X k ∧ eigs X k ≤ b).card

section P1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sums over the eigenvalues indexed by `ι` and by `Fin (card ι)` agree. -/
private lemma Counting_sum_reindex (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (g : ℝ → ℝ) :
    ∑ i : ι, g (hX.eigenvalues i) = ∑ j : Fin (Fintype.card ι), g (hX.eigenvalues₀ j) :=
  Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ fun _ => rfl

/-- The normalized trace of the resolvent is the average of `(λ_k - z)⁻¹`. -/
private lemma Counting_ntr_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ntr (res X z) = ((Fintype.card ι : ℂ))⁻¹ * ∑ k, ((hX.eigenvalues k : ℂ) - z)⁻¹ := by
  unfold ntr
  congr 1
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, res_eq_sum_eig X hX z hz]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : star (hX.eigenvectorUnitary : Matrix ι ι ℂ) * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have h2 := congrFun (congrFun h1 k) k
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Matrix.one_apply_eq] at h2
  rw [← Finset.sum_div]
  have : ∑ i, (hX.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      starRingEnd ℂ ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) = 1 := by
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this, one_div]


/-- `Im (l - (x + i y))⁻¹ = y / ((l - x)² + y²)`. -/
private lemma Counting_im_inv (l x y : ℝ) :
    (((l : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹).im = y / ((l - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp
  ring

/-- The imaginary part of the normalized trace of the resolvent is the Poisson average. -/
private lemma Counting_im_ntr_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (x y : ℝ) (hy : 0 < y) :
    (ntr (res X ((x : ℂ) + (y : ℂ) * Complex.I))).im =
      ((Fintype.card ι : ℝ))⁻¹ * ∑ k, y / ((hX.eigenvalues k - x) ^ 2 + y ^ 2) := by
  rw [Counting_ntr_res X hX _ (by simpa using hy)]
  have : ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Counting_im_inv _ x y

/-- `∫_a^b y/((l - x)² + y²) dx = arctan((b - l)/y) - arctan((a - l)/y)`. -/
private lemma Counting_integral_poisson (l a b y : ℝ) (hy : 0 < y) :
    ∫ x in a..b, y / ((l - x) ^ 2 + y ^ 2) =
      Real.arctan ((b - l) / y) - Real.arctan ((a - l) / y) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.arctan ((x - l) / y))
      (y / ((l - x) ^ 2 + y ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x - l) / y) (1 / y) x :=
      ((hasDerivAt_id x).sub_const l).div_const y
    have h2 := (Real.hasDerivAt_arctan ((x - l) / y)).comp x h1
    refine h2.congr_deriv ?_
    have : (l - x) ^ 2 + y ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)]
  · have h : Continuous fun x : ℝ => (l - x) ^ 2 + y ^ 2 := by fun_prop
    have hc : Continuous fun x : ℝ => y / ((l - x) ^ 2 + y ^ 2) :=
      continuous_const.div h fun x => (by positivity : (l - x) ^ 2 + y ^ 2 ≠ 0)
    exact hc.intervalIntegrable _ _

/-- The Poisson-smoothed count (deterministic): for Hermitian `X` with eigenvalues `λ_k` and
`η > 0`, `∫_a^b Im⟨G(x + iη)⟩ dx = n⁻¹ Σ_k (arctan((b - λ_k)/η) - arctan((a - λ_k)/η))`,
`n = card ι`. -/
theorem integral_im_ntr_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (a b η : ℝ) (hη : 0 < η) :
    ∫ x in a..b, (ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I))).im =
      ((Fintype.card ι : ℝ))⁻¹ * ∑ k, (Real.arctan ((b - hX.eigenvalues k) / η) -
        Real.arctan ((a - hX.eigenvalues k) / η)) := by
  simp_rw [Counting_im_ntr_res X hX _ η hη]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Counting_integral_poisson (hX.eigenvalues k) a b η hη
    rw [← this]
  · intro k _
    have h : Continuous fun x : ℝ => (hX.eigenvalues k - x) ^ 2 + η ^ 2 := by fun_prop
    have hc : Continuous fun x : ℝ => η / ((hX.eigenvalues k - x) ^ 2 + η ^ 2) :=
      continuous_const.div h fun x => (by positivity : (hX.eigenvalues k - x) ^ 2 + η ^ 2 ≠ 0)
    exact hc.intervalIntegrable _ _

end P1

section P2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(X - z) G(z) = 1` for Hermitian `X` and `Im z ≠ 0`. -/
private lemma Counting_mul_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (X - z • (1 : Matrix ι ι ℂ)) * res X z = 1 := by
  rcases lt_or_gt_of_ne hz with h | h
  · set w := starRingEnd ℂ z with hw
    have hwim : 0 < w.im := by simp [hw]; exact h
    have h1 := (res_mul_sub X hX w hwim).2
    have h2 : res X z = (res X w)ᴴ := by
      rw [← res_conj X hX w hwim, hw, Complex.conj_conj]
    have h3 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hX.eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] at h3
    rw [h2]
    have h4 : star w = z := by rw [hw]; exact Complex.conj_conj z
    rw [h4] at h3
    exact h3
  · exact (res_mul_sub X hX z h).1

end P2

/-- The Wigner matrix `wig n w` is Hermitian. -/
private lemma Counting_wig_isHermitian (n : ℕ) (w : Coords n) : (wig n w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- The block-diagonal matrix of the block resolvents. -/
private def Counting_blockRes (D N : ℕ) (w : Fin D → Coords N) (z : ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  fun p q => if p.1 = q.1 then res (wig N (w p.1)) z p.2 q.2 else 0

/-- The block-diagonal matrix of the block resolvents is the right inverse of `blockH - z`. -/
private lemma Counting_blockH_mul (D N : ℕ) (w : Fin D → Coords N) (z : ℂ) (hz : z.im ≠ 0) :
    (blockH D N w - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Counting_blockRes D N w z = 1 := by
  have hW : ∀ a : Fin D, ((wig N (w a)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      res (wig N (w a)) z = 1 := fun a =>
    Counting_mul_res _ (Counting_wig_isHermitian N (w a)) z hz
  ext ⟨a, i⟩ ⟨b, k⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Counting_blockRes]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst hab
      have := congrFun (congrFun (hW a) i) k
      simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul] at this
      simp only [blockH, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        ite_true, Prod.mk.injEq, true_and]
      simpa using this
    · simp [hab, blockH, Matrix.one_apply]
  · intro c _ hc
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ a = c := fun e => hc e.symm
    simp [blockH, this]
  · simp

/-- The block traces of the resolvent of the block-diagonal `H` of (1.3) [matrix_H] are the
normalized traces of the resolvents of its blocks: `D⟨G E_a⟩ = N⁻¹ tr (H_a - z)⁻¹` for `Im z ≠ 0`. -/
theorem blockH_ntr_res_Ea (D N : ℕ) (w : Fin D → Coords N) (z : ℂ) (hz : z.im ≠ 0)
    (a : Fin D) :
    (D : ℂ) * ntr (res (blockH D N w) z * Ea D N a) = ntr (res (wig N (w a)) z) := by
  have hres : res (blockH D N w) z = Counting_blockRes D N w z :=
    Matrix.inv_eq_right_inv (Counting_blockH_mul D N w z hz)
  have htr : (res (blockH D N w) z * Ea D N a).trace = (res (wig N (w a)) z).trace := by
    rw [hres]
    simp only [Matrix.trace, Matrix.diag_apply, Ea, Matrix.mul_diagonal, Counting_blockRes,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  unfold ntr
  rw [htr]
  have hD : (D : ℂ) ≠ 0 := by
    have : 0 < D := Fin.pos a
    exact_mod_cast this.ne'
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [mul_inv, ← mul_assoc, ← mul_assoc, mul_comm (D : ℂ) (D : ℂ)⁻¹,
    inv_mul_cancel₀ hD, one_mul]

section P3

/-- `ρ` is a continuous probability density supported in `[a, b]` with square-root edges
(constants `c₀`, `C₀`) and `d ≤ b - a ≤ 6`. -/
private structure Counting_SqrtDens (ρ : ℝ → ℝ) (a b c₀ C₀ d : ℝ) : Prop where
  hc₀ : 0 < c₀
  hC₀ : 0 < C₀
  hd : 0 < d
  hlen : d ≤ b - a ∧ b - a ≤ 6
  nonneg : ∀ x, 0 ≤ ρ x
  cont : Continuous ρ
  zero_left : ∀ x, x ≤ a → ρ x = 0
  zero_right : ∀ x, b ≤ x → ρ x = 0
  mass : ∫ x, ρ x = 1
  lower : ∀ x ∈ Set.Icc a b, c₀ * Real.sqrt ((b - x) * (x - a)) ≤ ρ x
  upper : ∀ x ∈ Set.Icc a b, ρ x ≤ C₀ * Real.sqrt ((b - x) * (x - a))

/-- The mass to the right of `x`: `T x = ∫_x^b ρ`. -/
private def Counting_T (ρ : ℝ → ℝ) (b x : ℝ) : ℝ := ∫ t in x..b, ρ t

variable {ρ : ℝ → ℝ} {a b c₀ C₀ d : ℝ}

private lemma Counting_SqrtDens.intInt (h : Counting_SqrtDens ρ a b c₀ C₀ d) (u v : ℝ) :
    IntervalIntegrable ρ volume u v := h.cont.intervalIntegrable u v

private lemma Counting_SqrtDens.hab (h : Counting_SqrtDens ρ a b c₀ C₀ d) : a < b := by
  linarith [h.hlen.1, h.hd]

private lemma Counting_SqrtDens.pos (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    0 < ρ x := by
  have h1 : 0 < (b - x) * (x - a) := mul_pos (by linarith [hx.2]) (by linarith [hx.1])
  have := h.lower x ⟨hx.1.le, hx.2.le⟩
  have h2 : 0 < c₀ * Real.sqrt ((b - x) * (x - a)) := mul_pos h.hc₀ (Real.sqrt_pos.2 h1)
  linarith

/-- `ρ` vanishes outside `(a, b)`. -/
private lemma Counting_SqrtDens.integral_ab (h : Counting_SqrtDens ρ a b c₀ C₀ d) :
    ∫ t in a..b, ρ t = 1 := by
  rw [intervalIntegral.integral_of_le h.hab.le, ← h.mass]
  symm
  rw [← MeasureTheory.setIntegral_univ]
  refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (Set.subset_univ _) fun t ht => ?_
  simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_Ioc, true_and, not_and, not_le] at ht
  by_cases hta : a < t
  · exact h.zero_right t (ht hta).le
  · exact h.zero_left t (not_lt.1 hta)

private lemma Counting_SqrtDens.T_of_ge (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ} (hx : b ≤ x) :
    Counting_T ρ b x = 0 := by
  unfold Counting_T
  rw [intervalIntegral.integral_symm]
  have : ∫ t in b..x, ρ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact h.zero_right t ht.1
  rw [this, neg_zero]

private lemma Counting_SqrtDens.T_of_le (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ} (hx : x ≤ a) :
    Counting_T ρ b x = 1 := by
  unfold Counting_T
  rw [← intervalIntegral.integral_add_adjacent_intervals (h.intInt x a) (h.intInt a b),
    h.integral_ab]
  have : ∫ t in x..a, ρ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact h.zero_left t ht.2
  rw [this, zero_add]

private lemma Counting_SqrtDens.T_sub (h : Counting_SqrtDens ρ a b c₀ C₀ d) (x y : ℝ) :
    Counting_T ρ b x - Counting_T ρ b y = ∫ t in x..y, ρ t := by
  unfold Counting_T
  rw [← intervalIntegral.integral_add_adjacent_intervals (h.intInt x y) (h.intInt y b)]
  ring

private lemma Counting_SqrtDens.T_anti (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x y : ℝ} (hxy : x ≤ y) :
    Counting_T ρ b y ≤ Counting_T ρ b x := by
  have := h.T_sub x y
  have h2 : 0 ≤ ∫ t in x..y, ρ t := intervalIntegral.integral_nonneg hxy fun t _ => h.nonneg t
  linarith

private lemma Counting_SqrtDens.T_cont (h : Counting_SqrtDens ρ a b c₀ C₀ d) :
    Continuous (Counting_T ρ b) := by
  have : Counting_T ρ b = fun x => -∫ t in b..x, ρ t := by
    funext x
    unfold Counting_T
    rw [intervalIntegral.integral_symm]
  rw [this]
  exact (intervalIntegral.continuous_primitive h.intInt b).neg

private lemma Counting_SqrtDens.T_strict (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x y : ℝ} (hx : a ≤ x)
    (hxy : x < y) (hy : y ≤ b) : Counting_T ρ b y < Counting_T ρ b x := by
  have := h.T_sub x y
  have h2 : 0 < ∫ t in x..y, ρ t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (h.intInt x y) (fun t ht => ?_) hxy
    exact h.pos ⟨by linarith [ht.1], by linarith [ht.2]⟩
  linarith

/-- The quantile of level `p ∈ (0, 1)`: the unique `γ ∈ (a, b)` with `T γ = p`, and
`p ≤ T x ↔ x ≤ γ`. -/
private lemma Counting_SqrtDens.quantile (h : Counting_SqrtDens ρ a b c₀ C₀ d) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∃ γ : ℝ, a < γ ∧ γ < b ∧ Counting_T ρ b γ = p ∧ ∀ x, p ≤ Counting_T ρ b x ↔ x ≤ γ := by
  have hTa := h.T_of_le (le_refl a)
  have hTb := h.T_of_ge (le_refl b)
  obtain ⟨γ, hγ, hTγ⟩ := intermediate_value_Icc' h.hab.le h.T_cont.continuousOn
    (show p ∈ Set.Icc (Counting_T ρ b b) (Counting_T ρ b a) by rw [hTa, hTb]; exact ⟨hp0.le, hp1.le⟩)
  have hγa : a < γ := by
    rcases hγ.1.eq_or_lt with e | e
    · rw [← e, hTa] at hTγ; linarith
    · exact e
  have hγb : γ < b := by
    rcases hγ.2.eq_or_lt with e | e
    · rw [e, hTb] at hTγ; linarith
    · exact e
  refine ⟨γ, hγa, hγb, hTγ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · by_contra hxγ
    rw [not_le] at hxγ
    rcases le_or_gt b x with hb | hb
    · rw [h.T_of_ge hb] at hx; linarith
    · have := h.T_strict hγa.le hxγ hb.le
      linarith
  · rw [← hTγ]
    exact h.T_anti hx

/-- `∫_{(x, ∞)} ρ = T x`. -/
private lemma Counting_SqrtDens.setIntegral_Ioi (h : Counting_SqrtDens ρ a b c₀ C₀ d) (x : ℝ) :
    ∫ t in Set.Ioi x, ρ t = Counting_T ρ b x := by
  rcases le_or_gt x b with hx | hx
  · have : ∫ t in Set.Ioi x, ρ t = ∫ t in Set.Ioc x b, ρ t := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Set.Ioc_subset_Ioi_self fun t ht => ?_
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
      exact h.zero_right t (ht.2 ht.1).le
    rw [this, ← intervalIntegral.integral_of_le hx]
    rfl
  · rw [h.T_of_ge hx.le]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    exact h.zero_right t (by simp only [Set.mem_Ioi] at ht; linarith)

/-- The quantile `quant ρ Mc k` is the `γ` of `quantile`. -/
private lemma Counting_SqrtDens.quant_eq (h : Counting_SqrtDens ρ a b c₀ C₀ d) {Mc k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ Mc) :
    ∃ γ : ℝ, a < γ ∧ γ < b ∧ Counting_T ρ b γ = ((k : ℝ) - 1 / 2) / Mc ∧
      quant ρ Mc k = γ ∧ ∀ x, ((k : ℝ) - 1 / 2) / Mc ≤ Counting_T ρ b x ↔ x ≤ γ := by
  have hM : (0 : ℝ) < Mc := by
    have : 0 < Mc := by omega
    exact_mod_cast this
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ Mc := by exact_mod_cast hk2
  have hp0 : 0 < ((k : ℝ) - 1 / 2) / Mc := div_pos (by linarith) hM
  have hp1 : ((k : ℝ) - 1 / 2) / Mc < 1 := by
    rw [div_lt_one hM]; linarith
  obtain ⟨γ, h1, h2, h3, h4⟩ := h.quantile hp0 hp1
  refine ⟨γ, h1, h2, h3, ?_, h4⟩
  unfold quant
  simp_rw [h.setIntegral_Ioi, h4]
  exact csSup_Iic

private lemma Counting_SqrtDens.T_nonneg (h : Counting_SqrtDens ρ a b c₀ C₀ d) (x : ℝ) :
    0 ≤ Counting_T ρ b x := by
  rcases le_or_gt x b with hx | hx
  · exact intervalIntegral.integral_nonneg hx fun t _ => h.nonneg t
  · rw [h.T_of_ge hx.le]

/-- Upper bound: `T x ≤ 3 C₀ (b - x) √(b - x)` for `x ∈ [a, b]`. -/
private lemma Counting_SqrtDens.T_upper (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ} (hx : a ≤ x)
    (hxb : x ≤ b) : Counting_T ρ b x ≤ 3 * C₀ * ((b - x) * Real.sqrt (b - x)) := by
  unfold Counting_T
  have hle : ∀ t ∈ Set.Icc x b, ρ t ≤ 3 * C₀ * Real.sqrt (b - x) := by
    intro t ht
    have h1 := h.upper t ⟨by linarith [ht.1], ht.2⟩
    have h2 : Real.sqrt ((b - t) * (t - a)) ≤ 3 * Real.sqrt (b - x) := by
      have : (b - t) * (t - a) ≤ (b - x) * 9 := by
        have e1 : b - t ≤ b - x := by linarith [ht.1]
        have e2 : t - a ≤ 9 := by linarith [h.hlen.2, ht.2, ht.1]
        have e3 : 0 ≤ t - a := by linarith [ht.1]
        have e4 : 0 ≤ b - t := by linarith [ht.2]
        nlinarith
      calc Real.sqrt ((b - t) * (t - a)) ≤ Real.sqrt ((b - x) * 9) := Real.sqrt_le_sqrt this
        _ = 3 * Real.sqrt (b - x) := by
          rw [Real.sqrt_mul (by linarith), show (9 : ℝ) = 3 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num), mul_comm]
    calc ρ t ≤ C₀ * Real.sqrt ((b - t) * (t - a)) := h1
      _ ≤ C₀ * (3 * Real.sqrt (b - x)) := mul_le_mul_of_nonneg_left h2 h.hC₀.le
      _ = 3 * C₀ * Real.sqrt (b - x) := by ring
  calc ∫ t in x..b, ρ t ≤ ∫ t in x..b, 3 * C₀ * Real.sqrt (b - x) :=
        intervalIntegral.integral_mono_on hxb (h.intInt x b) (by simp) hle
    _ = 3 * C₀ * ((b - x) * Real.sqrt (b - x)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- Lower bound: `T x ≥ (c₀/4) √(d/8) (b - x) √(b - x)` for `x ∈ [a, b]`. -/
private lemma Counting_SqrtDens.T_lower (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ} (hx : a ≤ x)
    (hxb : x ≤ b) :
    c₀ / 4 * Real.sqrt (d / 8) * ((b - x) * Real.sqrt (b - x)) ≤ Counting_T ρ b x := by
  set δ := b - x with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hδ1 : δ ≤ b - a := by linarith
  set t₁ := b - δ / 2 with ht₁
  set t₂ := b - δ / 4 with ht₂
  have h12 : t₁ ≤ t₂ := by linarith
  have hxt : x ≤ t₁ := by linarith
  have hd0 := h.hd
  have hdl := h.hlen.1
  have hmin : ∀ t ∈ Set.Icc t₁ t₂, c₀ * Real.sqrt (d / 8) * Real.sqrt δ ≤ ρ t := by
    intro t ht
    have h1 := h.lower t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 : Real.sqrt (d / 8) * Real.sqrt δ ≤ Real.sqrt ((b - t) * (t - a)) := by
      have : δ * (d / 8) ≤ (b - t) * (t - a) := by
        have e1 : δ / 4 ≤ b - t := by linarith [ht.2]
        have e2 : d / 2 ≤ t - a := by linarith [ht.1]
        have e3 : 0 ≤ b - t := by linarith [ht.2]
        nlinarith
      rw [← Real.sqrt_mul (by positivity), mul_comm]
      exact Real.sqrt_le_sqrt this
    calc c₀ * Real.sqrt (d / 8) * Real.sqrt δ = c₀ * (Real.sqrt (d / 8) * Real.sqrt δ) := by ring
      _ ≤ c₀ * Real.sqrt ((b - t) * (t - a)) := mul_le_mul_of_nonneg_left h2 h.hc₀.le
      _ ≤ ρ t := h1
  have hint : (t₂ - t₁) * (c₀ * Real.sqrt (d / 8) * Real.sqrt δ) ≤ ∫ t in t₁..t₂, ρ t := by
    have := intervalIntegral.integral_mono_on h12
      (intervalIntegrable_const (c := c₀ * Real.sqrt (d / 8) * Real.sqrt δ))
      (h.intInt t₁ t₂) hmin
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  have hsub := h.T_sub t₁ t₂
  have a1 := h.T_anti hxt
  have a2 := h.T_nonneg t₂
  have e : (t₂ - t₁) * (c₀ * Real.sqrt (d / 8) * Real.sqrt δ) =
      c₀ / 4 * Real.sqrt (d / 8) * (δ * Real.sqrt δ) := by
    simp only [ht₁, ht₂]; ring
  rw [e] at hint
  linarith

/-- The reflected density. -/
private lemma Counting_SqrtDens.reflect (h : Counting_SqrtDens ρ a b c₀ C₀ d) :
    Counting_SqrtDens (fun x => ρ (-x)) (-b) (-a) c₀ C₀ d where
  hc₀ := h.hc₀
  hC₀ := h.hC₀
  hd := h.hd
  hlen := ⟨by linarith [h.hlen.1], by linarith [h.hlen.2]⟩
  nonneg x := h.nonneg _
  cont := h.cont.comp continuous_neg
  zero_left x hx := h.zero_right _ (by linarith)
  zero_right x hx := h.zero_left _ (by linarith)
  mass := by rw [integral_neg_eq_self (fun x => ρ x) volume]; exact h.mass
  lower x hx := by
    have := h.lower (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    convert this using 3
    ring
  upper x hx := by
    have := h.upper (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    convert this using 3
    ring

/-- `1 - T x = ∫_a^x ρ`, and it is the `T` of the reflected density at `-x`. -/
private lemma Counting_SqrtDens.one_sub_T (h : Counting_SqrtDens ρ a b c₀ C₀ d) (x : ℝ) :
    1 - Counting_T ρ b x = Counting_T (fun x => ρ (-x)) (-a) (-x) := by
  have h1 := h.T_sub a x
  rw [h.T_of_le (le_refl a)] at h1
  have h2 : Counting_T (fun x => ρ (-x)) (-a) (-x) = ∫ t in a..x, ρ t := by
    unfold Counting_T
    rw [intervalIntegral.integral_comp_neg (fun t => ρ t)]
    simp
  rw [h2]
  linarith

end P3

section P3b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖M‖ ≤ (‖w‖ - ‖Λ‖)⁻¹` when `(Λ - w) M = 1`. -/
private lemma Counting_opNorm_le_of_mul (Λ M : Matrix ι ι ℂ) (w : ℂ) (ℓ : ℝ) (hΛ : opNorm Λ ≤ ℓ)
    (hw : ℓ < ‖w‖) (h : (Λ - w • (1 : Matrix ι ι ℂ)) * M = 1) :
    opNorm M ≤ (‖w‖ - ℓ)⁻¹ := by
  have hpos : 0 < ‖w‖ - ℓ := by linarith
  have hT : ∀ y, (‖w‖ - ℓ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M y‖ ≤ ‖y‖ := by
    intro y
    set x := Matrix.toEuclideanCLM (𝕜 := ℂ) M y
    have hy : Matrix.toEuclideanCLM (𝕜 := ℂ) Λ x - w • x = y := by
      have := congrArg (fun A => Matrix.toEuclideanCLM (𝕜 := ℂ) A y) h
      simp only [map_mul, map_sub, map_smul, map_one] at this
      exact this
    have h1 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Λ x‖ ≤ opNorm Λ * ‖x‖ :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ) Λ).le_opNorm x
    have h2 : ‖w • x‖ - ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Λ x‖ ≤ ‖y‖ := by
      rw [← hy, ← norm_neg (_ - _), neg_sub]
      exact norm_sub_norm_le _ _
    rw [norm_smul] at h2
    have h3 : opNorm Λ * ‖x‖ ≤ ℓ * ‖x‖ := mul_le_mul_of_nonneg_right hΛ (norm_nonneg _)
    nlinarith
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hpos.le) fun y => ?_
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  exact hT y

/-- `‖⟨B⟩‖ ≤ ‖B‖`. -/
private lemma Counting_norm_ntr_le (B : Matrix ι ι ℂ) : ‖ntr B‖ ≤ opNorm B := by
  unfold ntr
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0]; simp [opNorm]
  · have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hn]
    calc ‖B.trace‖ = ‖∑ i, B i i‖ := rfl
      _ ≤ ∑ i, ‖B i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, opNorm B := Finset.sum_le_sum fun i _ => norm_apply_le_opNorm B i i
      _ = Fintype.card ι * opNorm B := by simp

variable [Nonempty ι]

/-- `‖mExt Λ E‖ ≤ 1` at a real point. -/
private lemma Counting_norm_mExt_le (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (E : ℝ) : ‖mExt Λ (E : ℂ)‖ ≤ 1 := by
  have hc := (mExt_boundary Λ hΛ hℓ).1
  have hmem : ((E : ℂ)) ∈ {z : ℂ | 0 ≤ z.im} := by simp
  have hcw := hc.continuousWithinAt hmem
  have hmaps : Tendsto (fun η : ℝ => (E : ℂ) + (η : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (E : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun η : ℝ => (E : ℂ) + (η : ℂ) * Complex.I := by fun_prop
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with η hη
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      simp only [Set.mem_Ioi] at hη
      linarith
  have ht := hcw.tendsto.comp hmaps
  refine le_of_tendsto ht.norm ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  simp only [Set.mem_Ioi] at hη
  have him : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  have : mExt Λ ((E : ℂ) + (η : ℂ) * Complex.I) = mSol Λ ((E : ℂ) + (η : ℂ) * Complex.I) := by
    simp only [mExt, him, ↓reduceIte]
  simp only [Function.comp, this]
  exact (mSol_apriori Λ hΛ hℓ _ him).2.1.le

/-- The support of `ρ_N` lies in `(-3, 3)`. -/
private lemma Counting_edge_bound (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    -3 < Eminus Λ ∧ Eplus Λ < 3 := by
  have hlt := (rho_support Λ hΛ hℓ).1
  have key : ∀ E : ℝ, 3 ≤ |E| → E ∉ Set.Icc (Eminus Λ) (Eplus Λ) := by
    intro E hE hmem
    have h1 := equation_E_in_spectrum Λ hΛ hℓ E hmem
    obtain ⟨hw0, -, hmul⟩ := (mExt_boundary Λ hΛ hℓ).2 E
    have hm := Counting_norm_mExt_le Λ hΛ hℓ E
    set w : ℂ := (E : ℂ) + mExt Λ E with hw
    set M := MExt Λ E with hM
    have hwn : 2 ≤ ‖w‖ := by
      have h2 : ‖(E : ℂ)‖ - ‖mExt Λ E‖ ≤ ‖w‖ := by
        have := norm_sub_norm_le (w) (mExt Λ E)
        have e : w - mExt Λ E = (E : ℂ) := by rw [hw]; ring
        rw [e] at this
        have := norm_sub_norm_le (-(mExt Λ E)) (-(E:ℂ))
        have h3 := norm_add_le (E : ℂ) (mExt Λ E)
        have h4 : ‖(E : ℂ)‖ ≤ ‖w‖ + ‖mExt Λ E‖ := by
          calc ‖(E : ℂ)‖ = ‖w - mExt Λ E‖ := by rw [hw]; congr 1; ring
            _ ≤ ‖w‖ + ‖mExt Λ E‖ := norm_sub_le _ _
        linarith
      have : ‖(E : ℂ)‖ = |E| := by simp
      linarith
    have hM1 : opNorm M ≤ (‖w‖ - 1 / 10)⁻¹ :=
      Counting_opNorm_le_of_mul Λ M w (1 / 10) hℓ (by linarith) hmul
    have hM2 : opNorm Mᴴ ≤ (‖star w‖ - 1 / 10)⁻¹ := by
      have h3 := mul_eq_one_comm.1 hmul
      have h4 := congrArg Matrix.conjTranspose h3
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hΛ.eq, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one] at h4
      have h5 : (Λ - star w • (1 : Matrix ι ι ℂ)) * Mᴴ = 1 := by
        simpa using h4
      exact Counting_opNorm_le_of_mul Λ Mᴴ (star w) (1 / 10) hℓ (by simp; linarith) h5
    have hn : ‖star w‖ = ‖w‖ := by simp
    rw [hn] at hM2
    have hinv : (‖w‖ - 1 / 10)⁻¹ ≤ 1 / 1.9 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      norm_num
      linarith
    have h5 : ‖ntr (M * Mᴴ)‖ ≤ opNorm M * opNorm Mᴴ :=
      (Counting_norm_ntr_le _).trans (opNorm_mul_le _ _)
    have h6 : opNorm M * opNorm Mᴴ ≤ 1 / 1.9 * (1 / 1.9) :=
      mul_le_mul (hM1.trans hinv) (hM2.trans hinv) (norm_nonneg _) (by norm_num)
    rw [h1, norm_one] at h5
    norm_num at h6
    linarith
  constructor
  · by_contra hc
    rw [not_lt] at hc
    exact key (Eminus Λ) (by rw [abs_of_nonpos (by linarith)]; linarith) ⟨le_refl _, hlt.le⟩
  · by_contra hc
    rw [not_lt] at hc
    exact key (Eplus Λ) (by rw [abs_of_nonneg (by linarith)]; exact hc) ⟨hlt.le, le_refl _⟩

end P3b

section P3c

/-- A density with the upper square-root profile has `b - a ≥ √(2/C₀)`. -/
private lemma Counting_len_lower {ρ : ℝ → ℝ} {a b C₀ : ℝ} (hab : a < b) (hC : 0 < C₀)
    (hcont : Continuous ρ) (_hnn : ∀ x, 0 ≤ ρ x) (hz1 : ∀ x, x ≤ a → ρ x = 0)
    (hz2 : ∀ x, b ≤ x → ρ x = 0) (hmass : ∫ x, ρ x = 1)
    (hup : ∀ x ∈ Set.Icc a b, ρ x ≤ C₀ * Real.sqrt ((b - x) * (x - a))) :
    Real.sqrt (2 / C₀) ≤ b - a := by
  have h1 : ∫ t in a..b, ρ t = 1 := by
    rw [intervalIntegral.integral_of_le hab.le, ← hmass]
    symm
    rw [← MeasureTheory.setIntegral_univ]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (Set.subset_univ _) fun t ht => ?_
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_Ioc, true_and, not_and, not_le] at ht
    by_cases hta : a < t
    · exact hz2 t (ht hta).le
    · exact hz1 t (not_lt.1 hta)
  have hle : ∀ t ∈ Set.Icc a b, ρ t ≤ C₀ * ((b - a) / 2) := by
    intro t ht
    refine (hup t ht).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
    nlinarith [sq_nonneg (b - t - (t - a))]
  have h2 : ∫ t in a..b, ρ t ≤ ∫ t in a..b, C₀ * ((b - a) / 2) :=
    intervalIntegral.integral_mono_on hab.le (hcont.intervalIntegrable _ _) (by simp) hle
  rw [intervalIntegral.integral_const, smul_eq_mul, h1] at h2
  have h3 : 2 / C₀ ≤ (b - a) ^ 2 := by
    rw [div_le_iff₀ hC]; nlinarith
  calc Real.sqrt (2 / C₀) ≤ Real.sqrt ((b - a) ^ 2) := Real.sqrt_le_sqrt h3
    _ = b - a := Real.sqrt_sq (by linarith)

/-- Uniform constants for the square-root profile of `ρ_N`, `‖Λ‖ ≤ 1/10`. -/
private lemma Counting_sqrtDens_exists :
    ∃ c₀ C₀ d : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ 0 < d ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
        Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
        Counting_SqrtDens (rho Λ) (Eminus Λ) (Eplus Λ) c₀ C₀ d := by
  obtain ⟨C, hC, hsq⟩ := square_root_density 1 one_pos
  refine ⟨C⁻¹, C, Real.sqrt (2 / C), inv_pos.2 hC, hC, Real.sqrt_pos.2 (by positivity), ?_⟩
  intro ι _ _ _ Λ hΛ hℓ
  obtain ⟨hnn, hcont, -, hmass, -⟩ := rho_stieltjes Λ hΛ hℓ
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  obtain ⟨hbd1, hbd2⟩ := Counting_edge_bound Λ hΛ hℓ
  obtain ⟨hprof, -⟩ := hsq ι Λ hΛ hℓ
  have hz : ∀ x, x ∉ Set.Ioo (Eminus Λ) (Eplus Λ) → rho Λ x = 0 := by
    intro x hx
    rw [← hsupp] at hx
    exact Function.notMem_support.1 hx
  have hz1 : ∀ x, x ≤ Eminus Λ → rho Λ x = 0 := fun x hx =>
    hz x (fun h => by linarith [h.1])
  have hz2 : ∀ x, Eplus Λ ≤ x → rho Λ x = 0 := fun x hx =>
    hz x (fun h => by linarith [h.2])
  have hup : ∀ x ∈ Set.Icc (Eminus Λ) (Eplus Λ), rho Λ x ≤
      C * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ)) := fun x hx => (hprof x hx).2
  exact
    { hc₀ := inv_pos.2 hC
      hC₀ := hC
      hd := Real.sqrt_pos.2 (by positivity)
      hlen := ⟨Counting_len_lower hlt hC hcont hnn hz1 hz2 hmass hup, by linarith⟩
      nonneg := hnn
      cont := hcont
      zero_left := hz1
      zero_right := hz2
      mass := hmass
      lower := fun x hx => (hprof x hx).1
      upper := hup }

end P3c

section P4

variable {ρ : ℝ → ℝ} {a b c₀ C₀ d : ℝ}

/-- `1 - T x ≤ 3 C₀ (x - a) √(x - a)` for `x ∈ [a, b]`. -/
private lemma Counting_SqrtDens.one_sub_T_upper (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ}
    (hx : a ≤ x) (hxb : x ≤ b) :
    1 - Counting_T ρ b x ≤ 3 * C₀ * ((x - a) * Real.sqrt (x - a)) := by
  rw [h.one_sub_T x]
  have := h.reflect.T_upper (x := -x) (by linarith) (by linarith)
  convert this using 3 <;> ring_nf

/-- `1 - T x ≥ (c₀/4) √(d/8) (x - a) √(x - a)` for `x ∈ [a, b]`. -/
private lemma Counting_SqrtDens.one_sub_T_lower (h : Counting_SqrtDens ρ a b c₀ C₀ d) {x : ℝ}
    (hx : a ≤ x) (hxb : x ≤ b) :
    c₀ / 4 * Real.sqrt (d / 8) * ((x - a) * Real.sqrt (x - a)) ≤ 1 - Counting_T ρ b x := by
  rw [h.one_sub_T x]
  have := h.reflect.T_lower (x := -x) (by linarith) (by linarith)
  convert this using 3 <;> ring_nf

/-- The cube root. -/
private def Counting_cbrt (x : ℝ) : ℝ := x ^ (1 / 3 : ℝ)

private lemma Counting_cbrt_cube {x : ℝ} (hx : 0 ≤ x) : Counting_cbrt x ^ 3 = x := by
  unfold Counting_cbrt
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma Counting_cbrt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Counting_cbrt x := Real.rpow_nonneg hx _

/-- Two quantiles `γ₁` (level `p₁`) and `γ₂` (level `p₂ ≥ p₁`) are close when the levels are. -/
private lemma Counting_SqrtDens.quant_diff (h : Counting_SqrtDens ρ a b c₀ C₀ d)
    {p₁ p₂ γ₁ γ₂ μ : ℝ} (hp : p₁ ≤ p₂)
    (h1b : γ₁ < b) (h1T : Counting_T ρ b γ₁ = p₁)
    (h1i : ∀ x, p₁ ≤ Counting_T ρ b x ↔ x ≤ γ₁)
    (h2a : a < γ₂) (h2T : Counting_T ρ b γ₂ = p₂)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ p₁) (hμ2 : μ ≤ 1 - p₂) (hmax : 1 / 2 ≤ p₁ + (1 - p₂)) :
    γ₂ ≤ γ₁ ∧ (γ₁ - γ₂) ^ 3 * (c₀ ^ 3 * (μ / (36 * C₀ ^ 2))) ≤ (p₂ - p₁) ^ 3 := by
  have hγ : γ₂ ≤ γ₁ := (h1i γ₂).1 (by rw [h2T]; exact hp)
  refine ⟨hγ, ?_⟩
  set W := Counting_cbrt (μ / (36 * C₀ ^ 2)) with hW
  have hC := h.hC₀
  have hc := h.hc₀
  have hq : 0 ≤ μ / (36 * C₀ ^ 2) := by positivity
  have hW3 : W ^ 3 = μ / (36 * C₀ ^ 2) := Counting_cbrt_cube hq
  have hW0 : 0 ≤ W := Counting_cbrt_nonneg hq
  have hρ : ∀ x ∈ Set.Icc γ₂ γ₁, c₀ * W ≤ ρ x := by
    intro x hx
    have hxa : a ≤ x := by linarith [hx.1]
    have hxb : x ≤ b := by linarith [hx.2]
    have hT1 : p₁ ≤ Counting_T ρ b x := (h1i x).2 hx.2
    have hT2 : Counting_T ρ b x ≤ p₂ := by
      have := h.T_anti hx.1
      linarith
    have hu := h.T_upper hxa hxb
    have hv := h.one_sub_T_upper hxa hxb
    set u := Real.sqrt (b - x) with hu_def
    set v := Real.sqrt (x - a) with hv_def
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hv0 : 0 ≤ v := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = b - x := Real.sq_sqrt (by linarith)
    have hv2 : v ^ 2 = x - a := Real.sq_sqrt (by linarith)
    have e1 : p₁ ≤ 3 * C₀ * u ^ 3 := by
      calc p₁ ≤ Counting_T ρ b x := hT1
        _ ≤ 3 * C₀ * ((b - x) * u) := hu
        _ = 3 * C₀ * u ^ 3 := by rw [← hu2]; ring
    have e2 : 1 - p₂ ≤ 3 * C₀ * v ^ 3 := by
      calc 1 - p₂ ≤ 1 - Counting_T ρ b x := by linarith
        _ ≤ 3 * C₀ * ((x - a) * v) := hv
        _ = 3 * C₀ * v ^ 3 := by rw [← hv2]; ring
    have hprod : μ / 4 ≤ p₁ * (1 - p₂) := by
      rcases le_total (1 / 4) p₁ with h4 | h4
      · nlinarith
      · have : 1 / 4 ≤ 1 - p₂ := by linarith
        nlinarith
    have huv : μ / (36 * C₀ ^ 2) ≤ (u * v) ^ 3 := by
      have h3 : p₁ * (1 - p₂) ≤ (3 * C₀ * u ^ 3) * (3 * C₀ * v ^ 3) :=
        mul_le_mul e1 e2 (by linarith) (by positivity)
      have : (3 * C₀ * u ^ 3) * (3 * C₀ * v ^ 3) = 9 * C₀ ^ 2 * (u * v) ^ 3 := by ring
      rw [this] at h3
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hWuv : W ≤ u * v := by
      refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
      rw [hW3]; exact huv
    have hl := h.lower x ⟨hxa, hxb⟩
    have : Real.sqrt ((b - x) * (x - a)) = u * v := by
      rw [Real.sqrt_mul (by linarith)]
    rw [this] at hl
    exact (mul_le_mul_of_nonneg_left hWuv hc.le).trans hl
  have hint : (γ₁ - γ₂) * (c₀ * W) ≤ ∫ t in γ₂..γ₁, ρ t := by
    have := intervalIntegral.integral_mono_on hγ
      (intervalIntegrable_const (c := c₀ * W)) (h.intInt γ₂ γ₁) hρ
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  have hsub := h.T_sub γ₂ γ₁
  rw [h1T, h2T] at hsub
  have hle : (γ₁ - γ₂) * (c₀ * W) ≤ p₂ - p₁ := by linarith
  have hnn : 0 ≤ (γ₁ - γ₂) * (c₀ * W) := by
    have : 0 ≤ γ₁ - γ₂ := by linarith
    positivity
  calc (γ₁ - γ₂) ^ 3 * (c₀ ^ 3 * (μ / (36 * C₀ ^ 2)))
      = ((γ₁ - γ₂) * (c₀ * W)) ^ 3 := by rw [mul_pow, mul_pow, hW3]
    _ ≤ (p₂ - p₁) ^ 3 := pow_le_pow_left₀ hnn hle 3

/-- `(N^{-2/3} r^{-1/3})³ = (N² r)⁻¹`. -/
private lemma Counting_Q_cube {N r : ℝ} (hN : 0 < N) (hr : 0 < r) :
    ((N ^ (-(2 / 3 : ℝ))) * r ^ (-(1 / 3 : ℝ))) ^ 3 = (N ^ 2 * r)⁻¹ := by
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (r ^ (-(1 / 3 : ℝ))),
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hr.le]
  have e1 : -(2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -(2 : ℝ) := by norm_num
  have e2 : -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -(1 : ℝ) := by norm_num
  rw [e1, e2, Real.rpow_neg hN.le, Real.rpow_neg hr.le, Real.rpow_two, Real.rpow_one, mul_inv]

/-- `0 ∈ Matrix` is Hermitian with operator norm `0`. -/
private lemma Counting_zero_opNorm (ι : Type*) [Fintype ι] [DecidableEq ι] :
    opNorm (0 : Matrix ι ι ℂ) ≤ 1 / 10 := by
  simp [opNorm]

/-- `K ≤ (1 + K)³` for `K ≥ 0`. -/
private lemma Counting_le_cube {K : ℝ} (hK : 0 ≤ K) : K ≤ (1 + K) ^ 3 := by
  nlinarith [pow_nonneg hK 2, pow_nonneg hK 3]

end P4

set_option maxHeartbeats 1000000 in
/-- The quantile shift of (5.13) [eq:gammak2]: the semicircle quantiles with `N` particles and the
quantiles `γ^sc_{Di}` with `DN` particles satisfy
`|γ^sc_i(N) - γ^sc_{Di}(DN)| ≤ C N^{-2/3} min(i, N+1-i)^{-1/3}`, `C` depending on `D` only. -/
theorem quant_shift (D : ℕ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ i : ℕ, 1 ≤ i → i ≤ N →
      |quant rhoSc N i - quant rhoSc (D * N) (D * i)| ≤
        C * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨c₀, C₀, d, hc₀, hC₀, hd, hall⟩ := Counting_sqrtDens_exists
  have hρ := hall (Fin 1) 0 Matrix.isHermitian_zero (Counting_zero_opNorm _)
  have hsc : rho (0 : Matrix (Fin 1) (Fin 1) ℂ) = rhoSc := (rho_zero (ι := Fin 1)).2.1
  rw [hsc] at hρ
  refine ⟨1 + 9 * C₀ ^ 2 * D / c₀ ^ 3, by positivity, ?_⟩
  intro N hN i hi1 hiN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hi1r : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hiNr : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hDN1 : 1 ≤ D * N := Nat.mul_pos hD hN
  have hDi1 : 1 ≤ D * i := Nat.mul_pos hD hi1
  have hDiN : D * i ≤ D * N := Nat.mul_le_mul_left D hiN
  obtain ⟨γ₁, h1a, h1b, h1T, h1q, h1i⟩ := hρ.quant_eq hi1 hiN
  obtain ⟨γ₂, h2a, h2b, h2T, h2q, h2i⟩ := hρ.quant_eq hDi1 hDiN
  rw [h1q, h2q]
  -- the ratio `r = rk 1 N i`
  set r : ℝ := rk 1 N i with hr
  have hr_eq : r = ((min i (1 * N + 1 - i) : ℕ) : ℝ) := rfl
  have hr1 : (1 : ℝ) ≤ r := by
    rw [hr_eq]; exact_mod_cast (le_min hi1 (by omega))
  have hri : r ≤ i := by
    rw [hr_eq]; exact_mod_cast (min_le_left _ _)
  have hrN : r ≤ N + 1 - i := by
    have : min i (1 * N + 1 - i) ≤ N + 1 - i := by omega
    have h' : ((min i (1 * N + 1 - i) : ℕ) : ℝ) ≤ ((N + 1 - i : ℕ) : ℝ) := by exact_mod_cast this
    rw [hr_eq]
    refine h'.trans (le_of_eq ?_)
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr0 : 0 < r := by linarith
  set p₁ : ℝ := ((i : ℝ) - 1 / 2) / N with hp₁
  set p₂ : ℝ := (((D * i : ℕ) : ℝ) - 1 / 2) / ((D * N : ℕ) : ℝ) with hp₂
  have hp₂' : p₂ = ((D : ℝ) * i - 1 / 2) / ((D : ℝ) * N) := by rw [hp₂]; push_cast; ring
  have hdiff : p₂ - p₁ = ((D : ℝ) - 1) / (2 * D * N) := by
    rw [hp₂', hp₁]; field_simp; ring
  have hdiff0 : 0 ≤ p₂ - p₁ := by rw [hdiff]; apply div_nonneg <;> nlinarith
  have hdiff1 : p₂ - p₁ ≤ 1 / (2 * N) := by
    rw [hdiff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set μ : ℝ := r / (2 * D * N) with hμ
  have hμ0 : 0 < μ := by positivity
  have hμ1 : μ ≤ p₁ := by
    rw [hμ, hp₁, div_le_div_iff₀ (by positivity) hNr]
    have h5 : (i : ℝ) ≤ (2 * i - 1) * D := by nlinarith
    have h6 : (r : ℝ) * N ≤ i * N := mul_le_mul_of_nonneg_right hri hNr.le
    have h7 : (i : ℝ) * N ≤ (2 * i - 1) * D * N := mul_le_mul_of_nonneg_right h5 hNr.le
    nlinarith
  have hμ2 : μ ≤ 1 - p₂ := by
    rw [hμ, hp₂', show 1 - (D * (i : ℝ) - 1 / 2) / (D * N) =
      ((D : ℝ) * N - D * i + 1 / 2) / (D * N) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ N - i := by linarith
    have h6 : r ≤ 2 * ((D : ℝ) * N - D * i + 1 / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hDr) h0]
    have h7 : (r : ℝ) * (D * N) ≤ 2 * ((D : ℝ) * N - D * i + 1 / 2) * (D * N) :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    nlinarith
  have hmax : 1 / 2 ≤ p₁ + (1 - p₂) := by
    have : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  obtain ⟨hγ, hcube⟩ := hρ.quant_diff (p₁ := p₁) (p₂ := p₂) (μ := μ) (by linarith) h1b h1T h1i h2a
    h2T hμ0 hμ1 hμ2 hmax
  rw [abs_of_nonneg (by linarith)]
  set Q : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ)) * r ^ (-(1 / 3 : ℝ)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQ3 : Q ^ 3 = (N ^ 2 * r)⁻¹ := Counting_Q_cube hNr hr0
  set K : ℝ := 9 * C₀ ^ 2 * D / c₀ ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity
  set Θ := γ₁ - γ₂ with hΘ
  have hΘ0 : 0 ≤ Θ := by linarith
  have hA : 0 < c₀ ^ 3 * (μ / (36 * C₀ ^ 2)) := by positivity
  have hp3 : (p₂ - p₁) ^ 3 ≤ (1 / (2 * (N : ℝ))) ^ 3 := pow_le_pow_left₀ hdiff0 hdiff1 3
  have h1 : Θ ^ 3 * (c₀ ^ 3 * (μ / (36 * C₀ ^ 2))) ≤ (1 / (2 * (N : ℝ))) ^ 3 := hcube.trans hp3
  have h2 : Θ ^ 3 ≤ K * (N ^ 2 * r)⁻¹ := by
    rw [← le_div_iff₀ hA] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hμ, hK]
    field_simp
    ring
  have h3 : K * (N ^ 2 * r)⁻¹ ≤ (1 + K) ^ 3 * (N ^ 2 * r)⁻¹ := by
    exact mul_le_mul_of_nonneg_right (Counting_le_cube hK0) (by positivity)
  have h4 : Θ ^ 3 ≤ ((1 + K) * Q) ^ 3 := by
    rw [mul_pow, hQ3]
    exact h2.trans h3
  have h5 : Θ ≤ (1 + K) * Q :=
    le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) h4
  calc Θ ≤ (1 + K) * Q := h5
    _ = (1 + 9 * C₀ ^ 2 * D / c₀ ^ 3) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) := rfl

section P5

variable {ρ : ℝ → ℝ} {a b c₀ C₀ d : ℝ}

set_option maxHeartbeats 1000000 in
/-- The geometry of the quantile `γ_k`: the cubes of the distances to the edges are of the order
`k/N` and `(N + 1 - k)/N`. -/
private lemma Counting_SqrtDens.quant_geom (h : Counting_SqrtDens ρ a b c₀ C₀ d) {N k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) :
    ∃ γ : ℝ, a < γ ∧ γ < b ∧ quant ρ N k = γ ∧
      Counting_T ρ b γ = ((k : ℝ) - 1 / 2) / N ∧
      (∀ x, ((k : ℝ) - 1 / 2) / N ≤ Counting_T ρ b x ↔ x ≤ γ) ∧
      (k : ℝ) / (2 * N * (3 * C₀)) ≤ (Real.sqrt (b - γ)) ^ 3 ∧
      (Real.sqrt (b - γ)) ^ 3 ≤ k / (N * (c₀ / 4 * Real.sqrt (d / 8))) ∧
      ((N : ℝ) + 1 - k) / (2 * N * (3 * C₀)) ≤ (Real.sqrt (γ - a)) ^ 3 ∧
      (Real.sqrt (γ - a)) ^ 3 ≤ ((N : ℝ) + 1 - k) / (N * (c₀ / 4 * Real.sqrt (d / 8))) := by
  obtain ⟨γ, hγa, hγb, hT, hq, hi⟩ := h.quant_eq hk1 hkN
  refine ⟨γ, hγa, hγb, hq, hT, hi, ?_⟩
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hC := h.hC₀
  have hc := h.hc₀
  have hd := h.hd
  set κ : ℝ := c₀ / 4 * Real.sqrt (d / 8) with hκ
  have hκ0 : 0 < κ := by positivity
  set u := Real.sqrt (b - γ) with hu
  set v := Real.sqrt (γ - a) with hv
  have hu2 : u ^ 2 = b - γ := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = γ - a := Real.sq_sqrt (by linarith)
  have hu3 : (b - γ) * u = u ^ 3 := by rw [← hu2]; ring
  have hv3 : (γ - a) * v = v ^ 3 := by rw [← hv2]; ring
  have hU := h.T_upper hγa.le hγb.le
  have hL := h.T_lower hγa.le hγb.le
  have hU' := h.one_sub_T_upper hγa.le hγb.le
  have hL' := h.one_sub_T_lower hγa.le hγb.le
  rw [hu3] at hU hL
  rw [hv3] at hU' hL'
  rw [hT] at hU hL
  have e1 : 1 - ((k : ℝ) - 1 / 2) / N = ((N : ℝ) + 1 - k - 1 / 2) / N := by
    field_simp; ring
  rw [hT, e1] at hU' hL'
  have hk3 : (k : ℝ) / (2 * N) ≤ ((k : ℝ) - 1 / 2) / N := by
    rw [div_le_div_iff₀ (by positivity) hNr]; nlinarith
  have hk4 : ((k : ℝ) - 1 / 2) / N ≤ k / N := by
    apply div_le_div_of_nonneg_right (by linarith) hNr.le
  have hk3' : ((N : ℝ) + 1 - k) / (2 * N) ≤ ((N : ℝ) + 1 - k - 1 / 2) / N := by
    rw [div_le_div_iff₀ (by positivity) hNr]; nlinarith
  have hk4' : ((N : ℝ) + 1 - k - 1 / 2) / N ≤ ((N : ℝ) + 1 - k) / N := by
    apply div_le_div_of_nonneg_right (by linarith) hNr.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have := hk3.trans hU
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    have := hL.trans hk4
    rw [le_div_iff₀ hNr] at this
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have := hk3'.trans hU'
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    have := hL'.trans hk4'
    rw [le_div_iff₀ hNr] at this
    nlinarith

/-- The mass window: if the counting inequalities hold and `N Δ ρm ≥ p` with `ρ ≥ ρm` on
`[γ - Δ, γ + Δ]`, then `|λ_k - γ| ≤ Δ`. -/
private lemma Counting_SqrtDens.mass_window (h : Counting_SqrtDens ρ a b c₀ C₀ d) {N k : ℕ}
    (hN : 0 < N) {γ Δ p ρm lamk : ℝ} (hγ : a < γ) (hΔ : 0 ≤ Δ) (hΔa : a ≤ γ - Δ)
    (hΔb : γ + Δ ≤ b) (hTγ : Counting_T ρ b γ = ((k : ℝ) - 1 / 2) / N)
    (hρm : ∀ x ∈ Set.Icc (γ - Δ) (γ + Δ), ρm ≤ ρ x) (hmass : p ≤ N * (Δ * ρm))
    (I1 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → E ≤ lamk → (k : ℝ) ≤ N * Counting_T ρ b E + p)
    (I2 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → lamk < E → N * Counting_T ρ b E - p ≤ k - 1) :
    |lamk - γ| ≤ Δ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNT : (N : ℝ) * Counting_T ρ b γ = k - 1 / 2 := by
    rw [hTγ]; field_simp
  rw [abs_le]
  constructor
  · by_contra hc
    rw [not_le] at hc
    have hI := I2 (γ - Δ) (by linarith) (by linarith) (by linarith)
    have hint : Δ * ρm ≤ ∫ t in (γ - Δ)..γ, ρ t := by
      have := intervalIntegral.integral_mono_on (by linarith : γ - Δ ≤ γ)
        (intervalIntegrable_const (c := ρm)) (h.intInt (γ - Δ) γ)
        (fun x hx => hρm x ⟨hx.1, by linarith [hx.2]⟩)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      have e : γ - (γ - Δ) = Δ := by ring
      rw [e] at this
      exact this
    have hsub := h.T_sub (γ - Δ) γ
    have : (N : ℝ) * (Δ * ρm) ≤ N * (Counting_T ρ b (γ - Δ) - Counting_T ρ b γ) := by
      rw [hsub]; exact mul_le_mul_of_nonneg_left hint hNr.le
    nlinarith
  · by_contra hc
    rw [not_le] at hc
    have hI := I1 (γ + Δ) (by linarith) (by linarith) (by linarith)
    have hint : Δ * ρm ≤ ∫ t in γ..(γ + Δ), ρ t := by
      have := intervalIntegral.integral_mono_on (by linarith : γ ≤ γ + Δ)
        (intervalIntegrable_const (c := ρm)) (h.intInt γ (γ + Δ))
        (fun x hx => hρm x ⟨by linarith [hx.1], hx.2⟩)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      have e : γ + Δ - γ = Δ := by ring
      rw [e] at this
      exact this
    have hsub := h.T_sub γ (γ + Δ)
    have : (N : ℝ) * (Δ * ρm) ≤ N * (Counting_T ρ b γ - Counting_T ρ b (γ + Δ)) := by
      rw [hsub]; exact mul_le_mul_of_nonneg_left hint hNr.le
    nlinarith

/-- Real arithmetic: `p² Q ≤ w²/2` when `w³ ≥ m/(2Nκ)`, `m ≥ r ≥ (1 + 32κ²) p²`. -/
private lemma Counting_delta_le {N r p Q κ w m : ℝ} (hN : 0 < N) (hκ : 0 < κ) (hp1 : 1 ≤ p)
    (hr : (1 + 32 * κ ^ 2) * p ^ 2 ≤ r) (_hQ0 : 0 ≤ Q) (hQ : Q ^ 3 = (N ^ 2 * r)⁻¹)
    (_hw : 0 ≤ w) (hrm : r ≤ m) (hm : m / (2 * N * κ) ≤ w ^ 3) : p ^ 2 * Q ≤ w ^ 2 / 2 := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by
    have : 0 < (1 + 32 * κ ^ 2) * p ^ 2 := by positivity
    linarith
  have key : 32 * κ ^ 2 * p ^ 6 ≤ r ^ 3 := by
    have h1 : ((1 + 32 * κ ^ 2) * p ^ 2) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by positivity) hr 3
    have hM3 : 1 + 32 * κ ^ 2 ≤ (1 + 32 * κ ^ 2) ^ 3 := by
      nlinarith [sq_nonneg (1 + 32 * κ ^ 2), sq_nonneg (32 * κ ^ 2), sq_nonneg κ]
    have h2 : (1 + 32 * κ ^ 2) * p ^ 6 ≤ ((1 + 32 * κ ^ 2) * p ^ 2) ^ 3 := by
      have : ((1 + 32 * κ ^ 2) * p ^ 2) ^ 3 = (1 + 32 * κ ^ 2) ^ 3 * p ^ 6 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hM3 (pow_nonneg hp0.le 6)
    have h3 : 32 * κ ^ 2 * p ^ 6 ≤ (1 + 32 * κ ^ 2) * p ^ 6 := by
      nlinarith [pow_nonneg hp0.le 6]
    linarith
  have hl : r / (2 * N * κ) ≤ w ^ 3 :=
    (div_le_div_of_nonneg_right hrm (by positivity)).trans hm
  have hl2 : (r / (2 * N * κ)) ^ 2 ≤ (w ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hl 2
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  have hΔ3 : (p ^ 2 * Q) ^ 3 = p ^ 6 * (N ^ 2 * r)⁻¹ := by
    rw [mul_pow, ← hQ]; ring
  rw [hΔ3, div_pow, show (w ^ 2) ^ 3 = (w ^ 3) ^ 2 by ring]
  have e1 : p ^ 6 * (N ^ 2 * r)⁻¹ = p ^ 6 / (N ^ 2 * r) := by rw [div_eq_mul_inv]
  have e2 : (r / (2 * N * κ)) ^ 2 / 8 = r ^ 2 / (32 * N ^ 2 * κ ^ 2) := by
    field_simp; ring
  have : p ^ 6 * (N ^ 2 * r)⁻¹ ≤ (r / (2 * N * κ)) ^ 2 / 8 := by
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    calc p ^ 6 * (32 * N ^ 2 * κ ^ 2) = (32 * κ ^ 2 * p ^ 6) * N ^ 2 := by ring
      _ ≤ r ^ 3 * N ^ 2 := mul_le_mul_of_nonneg_right key (sq_nonneg _)
      _ = r ^ 2 * (N ^ 2 * r) := by ring
  calc p ^ 6 * (N ^ 2 * r)⁻¹ ≤ (r / (2 * N * κ)) ^ 2 / 8 := this
    _ ≤ (w ^ 3) ^ 2 / 8 := by linarith
    _ = (w ^ 3) ^ 2 / 2 ^ 3 := by norm_num

/-- `k (N + 1 - k) ≥ r N / 2` when `r ≤ k`, `r ≤ N + 1 - k`. -/
private lemma Counting_kk {N k r : ℝ} (hk : k ≤ N) (hr0 : 0 ≤ r) (hrk : r ≤ k) (hrk' : r ≤ N + 1 - k) :
    r * N / 2 ≤ k * (N + 1 - k) := by
  rcases le_total k (N + 1 - k) with hh | hh
  · have : (N + 1) / 2 ≤ N + 1 - k := by linarith
    nlinarith
  · have : (N + 1) / 2 ≤ k := by linarith
    nlinarith

/-- Real arithmetic for the forced mass: `N Q u v ≥ (1 + 8κ²)⁻¹`. -/
private lemma Counting_Y_ge {N r k Q κ u v : ℝ} (hN : 0 < N) (hκ : 0 < κ) (hr0 : 0 < r) (hQ0 : 0 ≤ Q)
    (hQ : Q ^ 3 = (N ^ 2 * r) ⁻¹) (hkk : r * N / 2 ≤ k * (N + 1 - k)) (hk' : 0 ≤ N + 1 - k)
    (_hk0 : 0 ≤ k) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu1 : k / (2 * N * κ) ≤ u ^ 3)
    (hv1 : (N + 1 - k) / (2 * N * κ) ≤ v ^ 3) : 1 / (1 + 8 * κ ^ 2) ≤ N * Q * (u * v) := by
  have hY0 : 0 ≤ N * Q * (u * v) := by positivity
  have hprod : k * (N + 1 - k) / (2 * N * κ) ^ 2 ≤ u ^ 3 * v ^ 3 := by
    have := mul_le_mul hu1 hv1 (by positivity) (by positivity)
    rw [div_mul_div_comm, ← sq] at this
    exact this
  have hY3 : 1 / (8 * κ ^ 2) ≤ (N * Q * (u * v)) ^ 3 := by
    have e : (N * Q * (u * v)) ^ 3 = N ^ 3 * (N ^ 2 * r)⁻¹ * (u ^ 3 * v ^ 3) := by
      rw [mul_pow, mul_pow, hQ]; ring
    rw [e]
    have h1 : N ^ 3 * (N ^ 2 * r)⁻¹ * ((r * N / 2) / (2 * N * κ) ^ 2) ≤
        N ^ 3 * (N ^ 2 * r)⁻¹ * (u ^ 3 * v ^ 3) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (div_le_div_of_nonneg_right hkk (by positivity)).trans hprod
    refine le_trans (le_of_eq ?_) h1
    field_simp
    ring
  have hy0 : 1 / (1 + 8 * κ ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [sq_nonneg κ]
  have hy3 : (1 / (1 + 8 * κ ^ 2)) ^ 3 ≤ (N * Q * (u * v)) ^ 3 := by
    have hyy : 0 ≤ 1 / (1 + 8 * κ ^ 2) := by positivity
    have h1 : (1 / (1 + 8 * κ ^ 2)) ^ 3 ≤ 1 / (1 + 8 * κ ^ 2) := by
      calc (1 / (1 + 8 * κ ^ 2)) ^ 3 = (1 / (1 + 8 * κ ^ 2)) * (1 / (1 + 8 * κ ^ 2)) ^ 2 := by ring
        _ ≤ (1 / (1 + 8 * κ ^ 2)) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hyy
          exact pow_le_one₀ hyy hy0
        _ = _ := by ring
    have h2 : 1 / (1 + 8 * κ ^ 2) ≤ 1 / (8 * κ ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    linarith
  exact le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hY0 hy3

/-- Range 1: for `r ≥ M p²` the eigenvalue `λ_k` is within `p² Q` of `γ_k`. -/
private lemma Counting_range1 (h : Counting_SqrtDens ρ a b c₀ C₀ d) {N k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (lam : ℕ → ℝ) {p r Q : ℝ} (hp1 : 1 ≤ p)
    (hpM : 2 * (1 + 8 * (3 * C₀) ^ 2) / c₀ ≤ p)
    (hr : (1 + 32 * (3 * C₀) ^ 2) * p ^ 2 ≤ r) (hrk : r ≤ k) (hrk' : r ≤ (N : ℝ) + 1 - k)
    (hQ0 : 0 ≤ Q) (hQ : Q ^ 3 = ((N : ℝ) ^ 2 * r)⁻¹)
    (I1 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → E ≤ lam k → (k : ℝ) ≤ N * Counting_T ρ b E + p)
    (I2 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → lam k < E → N * Counting_T ρ b E - p ≤ k - 1) :
    |lam k - quant ρ N k| ≤ p ^ 2 * Q := by
  obtain ⟨γ, hγa, hγb, hq, hT, hi, hu1, -, hv1, -⟩ := h.quant_geom hk1 hkN
  rw [hq]
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hC := h.hC₀
  have hc := h.hc₀
  have hκ0 : 0 < 3 * C₀ := by positivity
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by
    have : 0 < (1 + 32 * (3 * C₀) ^ 2) * p ^ 2 := by positivity
    linarith
  have hu0 : 0 ≤ Real.sqrt (b - γ) := Real.sqrt_nonneg _
  have hv0 : 0 ≤ Real.sqrt (γ - a) := Real.sqrt_nonneg _
  have hu2 : Real.sqrt (b - γ) ^ 2 = b - γ := Real.sq_sqrt (by linarith)
  have hv2 : Real.sqrt (γ - a) ^ 2 = γ - a := Real.sq_sqrt (by linarith)
  have hΔu := Counting_delta_le hNr hκ0 hp1 hr hQ0 hQ hu0 hrk hu1
  have hΔv := Counting_delta_le hNr hκ0 hp1 hr hQ0 hQ hv0 hrk' hv1
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hY := Counting_Y_ge hNr hκ0 hr0 hQ0 hQ
    (Counting_kk hkR hr0.le hrk hrk') (by linarith) (by positivity) hu0 hv0 hu1 hv1
  set u := Real.sqrt (b - γ) with hu
  set v := Real.sqrt (γ - a) with hv
  have hρm : ∀ x ∈ Set.Icc (γ - p ^ 2 * Q) (γ + p ^ 2 * Q), c₀ / 2 * (u * v) ≤ ρ x := by
    intro x hx
    have hxa : a ≤ x := by linarith [hx.1, hv2, sq_nonneg v]
    have hxb : x ≤ b := by linarith [hx.2, hu2, sq_nonneg u]
    have h1 := h.lower x ⟨hxa, hxb⟩
    have hA : u ^ 2 / 2 ≤ b - x := by linarith [hx.2]
    have hB : v ^ 2 / 2 ≤ x - a := by linarith [hx.1]
    have h2 : u * v / 2 ≤ Real.sqrt ((b - x) * (x - a)) := by
      refine Real.le_sqrt_of_sq_le ?_
      have : (u * v / 2) ^ 2 = (u ^ 2 / 2) * (v ^ 2 / 2) := by ring
      rw [this]
      exact mul_le_mul hA hB (by positivity) (by linarith [sq_nonneg u])
    calc c₀ / 2 * (u * v) = c₀ * (u * v / 2) := by ring
      _ ≤ c₀ * Real.sqrt ((b - x) * (x - a)) := mul_le_mul_of_nonneg_left h2 hc.le
      _ ≤ ρ x := h1
  have hmass : p ≤ N * (p ^ 2 * Q * (c₀ / 2 * (u * v))) := by
    have h1 : 2 * (1 + 8 * (3 * C₀) ^ 2) / c₀ ≤ p := hpM
    rw [div_le_iff₀ hc] at h1
    have h2 : 1 ≤ (1 + 8 * (3 * C₀) ^ 2) * ((N : ℝ) * Q * (u * v)) := by
      have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 1 + 8 * (3 * C₀) ^ 2)
      rw [mul_one_div_cancel (by positivity)] at this
      exact this
    have hQ' : 0 ≤ (N : ℝ) * Q * (u * v) := by positivity
    have h3 : 1 ≤ p * (c₀ / 2) * ((N : ℝ) * Q * (u * v)) := by
      have : (1 + 8 * (3 * C₀) ^ 2) * ((N : ℝ) * Q * (u * v)) ≤
          p * (c₀ / 2) * ((N : ℝ) * Q * (u * v)) := by
        refine mul_le_mul_of_nonneg_right ?_ hQ'
        linarith
      linarith
    have h4 : p * 1 ≤ p * (p * (c₀ / 2) * ((N : ℝ) * Q * (u * v))) :=
      mul_le_mul_of_nonneg_left h3 hp0.le
    calc p = p * 1 := by ring
      _ ≤ p * (p * (c₀ / 2) * ((N : ℝ) * Q * (u * v))) := h4
      _ = N * (p ^ 2 * Q * (c₀ / 2 * (u * v))) := by ring
  exact h.mass_window (N := N) (k := k) (by omega) hγa (by positivity)
    (by linarith [hΔv, hv2, sq_nonneg v]) (by linarith [hΔu, hu2, sq_nonneg u]) hT hρm hmass I1 I2

/-- Real arithmetic of the edge range: `G + p² Q₀ + w ≤ p³ Q_j` for `j < M p²`. -/
private lemma Counting_range2_arith {N p j k₀ κ₁ M G Δ₀ Q₀ Qj w : ℝ} (hN : 0 < N) (hp3 : 3 ≤ p)
    (hM : 1 ≤ M) (hj1 : 1 ≤ j) (hj : j < M * p ^ 2) (hk₀ : k₀ ≤ 2 * M * p ^ 2) (hjk : j ≤ k₀)
    (hκ₁ : 0 < κ₁) (hκ₁p : 216 * M ^ 3 ≤ κ₁ ^ 2 * p ^ 3) (hp4 : 27 * M ≤ p ^ 4)
    (hG0 : 0 ≤ G) (hG : G ^ 3 ≤ (k₀ / (N * κ₁)) ^ 2) (hΔ₀ : Δ₀ ≤ p ^ 2 * Q₀)
    (_hQ₀0 : 0 ≤ Q₀) (hQ₀ : Q₀ ^ 3 = (N ^ 2 * k₀)⁻¹) (hQj0 : 0 ≤ Qj)
    (hQj : Qj ^ 3 = (N ^ 2 * j)⁻¹) (_hw0 : 0 ≤ w) (hw : w ^ 3 = p ^ 3 * (N ^ 2)⁻¹) :
    G + Δ₀ + w ≤ p ^ 3 * Qj := by
  have hp0 : 0 < p := by linarith
  have hj0 : 0 < j := by linarith
  have hk0 : 0 < k₀ := by linarith
  have hQj3 : (p ^ 3 * Qj / 3) ^ 3 = p ^ 9 * (N ^ 2 * j)⁻¹ / 27 := by
    rw [div_pow, mul_pow, hQj]; ring
  -- (i)
  have h1 : G ≤ p ^ 3 * Qj / 3 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    rw [hQj3]
    refine hG.trans ?_
    have e1 : p ^ 9 * (N ^ 2 * j)⁻¹ / 27 = p ^ 9 / (27 * (N ^ 2 * j)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
    rw [e1, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk2 : k₀ ≤ 2 * M * p ^ 2 := hk₀
    have hjk2 : j * k₀ ^ 2 ≤ (M * p ^ 2) * (2 * M * p ^ 2) ^ 2 := by
      refine mul_le_mul hj.le (pow_le_pow_left₀ hk0.le hk2 2) (by positivity) (by positivity)
    have h5 : 27 * (j * k₀ ^ 2) ≤ κ₁ ^ 2 * p ^ 9 := by
      calc 27 * (j * k₀ ^ 2) ≤ 27 * ((M * p ^ 2) * (2 * M * p ^ 2) ^ 2) := by linarith
        _ = 108 * M ^ 3 * p ^ 6 := by ring
        _ ≤ (216 * M ^ 3) * p ^ 6 := by nlinarith [pow_nonneg hp0.le 6, pow_nonneg (by linarith : (0 : ℝ) ≤ M) 3]
        _ ≤ (κ₁ ^ 2 * p ^ 3) * p ^ 6 := mul_le_mul_of_nonneg_right hκ₁p (pow_nonneg hp0.le 6)
        _ = κ₁ ^ 2 * p ^ 9 := by ring
    calc k₀ ^ 2 * (27 * (N ^ 2 * j)) = (27 * (j * k₀ ^ 2)) * N ^ 2 := by ring
      _ ≤ (κ₁ ^ 2 * p ^ 9) * N ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
      _ = p ^ 9 * (N * κ₁) ^ 2 := by ring
  -- (ii)
  have h2 : Δ₀ ≤ p ^ 3 * Qj / 3 := by
    have hQ : Q₀ ≤ Qj := by
      refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hQj0 ?_
      rw [hQ₀, hQj]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hjk (by positivity))
    calc Δ₀ ≤ p ^ 2 * Q₀ := hΔ₀
      _ ≤ p ^ 2 * Qj := mul_le_mul_of_nonneg_left hQ (by positivity)
      _ ≤ p ^ 3 * Qj / 3 := by nlinarith [mul_nonneg (sq_nonneg p) hQj0]
  -- (iii)
  have h3 : w ≤ p ^ 3 * Qj / 3 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    rw [hQj3, hw]
    have e1 : p ^ 9 * (N ^ 2 * j)⁻¹ / 27 = p ^ 9 / (27 * (N ^ 2 * j)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
    rw [e1, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    have h6 : 27 * j ≤ p ^ 6 := by
      calc 27 * j ≤ 27 * (M * p ^ 2) := by linarith
        _ = (27 * M) * p ^ 2 := by ring
        _ ≤ p ^ 4 * p ^ 2 := mul_le_mul_of_nonneg_right hp4 (sq_nonneg _)
        _ = p ^ 6 := by ring
    calc p ^ 3 * (27 * (N ^ 2 * j)) = (27 * j) * (p ^ 3 * N ^ 2) := by ring
      _ ≤ p ^ 6 * (p ^ 3 * N ^ 2) := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = p ^ 9 * N ^ 2 := by ring
  linarith

end P5

section P6

variable {ρ : ℝ → ℝ} {a b c₀ C₀ d : ℝ}

/-- `N^{-2/3} r^{-1/3}`. -/
private def Counting_Q (N r : ℝ) : ℝ := N ^ (-(2 / 3 : ℝ)) * r ^ (-(1 / 3 : ℝ))

private lemma Counting_Q_nonneg {N r : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r) : 0 ≤ Counting_Q N r := by
  unfold Counting_Q; positivity

private lemma Counting_Q_cube' {N r : ℝ} (hN : 0 < N) (hr : 0 < r) :
    Counting_Q N r ^ 3 = (N ^ 2 * r)⁻¹ := Counting_Q_cube hN hr

private lemma Counting_Q_anti {N r s : ℝ} (hN : 0 < N) (hr : 0 < r) (hrs : r ≤ s) :
    Counting_Q N s ≤ Counting_Q N r := by
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Counting_Q_nonneg hN.le hr.le) ?_
  rw [Counting_Q_cube' hN hr, Counting_Q_cube' hN (hr.trans_le hrs)]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hrs (by positivity))

/-- `(N^{-2/3})³ = N⁻²`. -/
private lemma Counting_nu_cube {N : ℝ} (hN : 0 < N) : (N ^ (-(2 / 3 : ℝ))) ^ 3 = (N ^ 2)⁻¹ := by
  have := Counting_Q_cube hN (one_pos : (0 : ℝ) < 1)
  simpa [Real.one_rpow] using this

/-- Eventually in `ℕ` from eventually in `ℝ`. -/
private lemma Counting_eventually_nat {P : ℝ → Prop} (h : ∀ᶠ x in atTop, P x) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P N := by
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  exact Filter.eventually_atTop.1 this

/-- The edge range at the right edge: `k < M p²`. -/
private lemma Counting_edge_right (h : Counting_SqrtDens ρ a b c₀ C₀ d) {N k k₀ : ℕ} (hk1 : 1 ≤ k)
    (hkk₀ : k ≤ k₀) (hk₀N : 2 * k₀ ≤ N) (lam : ℕ → ℝ) {p w : ℝ}
    (hp3 : 3 ≤ p) (hpM : 2 * (1 + 8 * (3 * C₀) ^ 2) / c₀ ≤ p)
    (hκ₁p : 216 * (1 + 32 * (3 * C₀) ^ 2) ^ 3 ≤ (c₀ / 4 * Real.sqrt (d / 8)) ^ 2 * p ^ 3)
    (hp4 : 27 * (1 + 32 * (3 * C₀) ^ 2) ≤ p ^ 4)
    (hk : (k : ℝ) < (1 + 32 * (3 * C₀) ^ 2) * p ^ 2)
    (hk₀a : (1 + 32 * (3 * C₀) ^ 2) * p ^ 2 ≤ k₀)
    (hk₀b : (k₀ : ℝ) ≤ 2 * (1 + 32 * (3 * C₀) ^ 2) * p ^ 2)
    (hw0 : 0 ≤ w) (hw : w ^ 3 = p ^ 3 * ((N : ℝ) ^ 2)⁻¹)
    (hanti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ N → lam j ≤ lam i)
    (hwin : lam 1 ≤ b + w)
    (I1 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N → E ≤ lam k →
      (k : ℝ) ≤ N * Counting_T ρ b E + p)
    (I2 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N → lam k < E →
      N * Counting_T ρ b E - p ≤ k - 1) :
    |lam k - quant ρ N k| ≤ p ^ 3 * Counting_Q N k := by
  have hk₀1 : 1 ≤ k₀ := le_trans hk1 hkk₀
  have hk₀N' : k₀ ≤ N := by omega
  have hkN : k ≤ N := le_trans hkk₀ hk₀N'
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hC := h.hC₀
  have hc := h.hc₀
  have hd := h.hd
  have hp0 : 0 < p := by linarith
  have hκ₂ : 0 < 3 * C₀ := by positivity
  have hM : (1 : ℝ) ≤ 1 + 32 * (3 * C₀) ^ 2 := by nlinarith [sq_nonneg (3 * C₀)]
  have hκ₁ : 0 < c₀ / 4 * Real.sqrt (d / 8) := by positivity
  have hk₀r : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀1
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkk₀r : (k : ℝ) ≤ k₀ := by exact_mod_cast hkk₀
  have hk₀Nr : (k₀ : ℝ) ≤ N := by exact_mod_cast hk₀N'
  have h2k₀ : (2 : ℝ) * k₀ ≤ N := by exact_mod_cast hk₀N
  -- Range 1 at `k₀`
  have hr1 := Counting_range1 h hk₀1 hk₀N' lam (p := p) (r := k₀) (Q := Counting_Q N k₀)
    (by linarith) hpM hk₀a le_rfl (by linarith)
    (Counting_Q_nonneg hNr.le (by linarith)) (Counting_Q_cube' hNr (by linarith))
    (fun E h1 h2 => I1 E h1 h2 k₀ hk₀1 hk₀N') (fun E h1 h2 => I2 E h1 h2 k₀ hk₀1 hk₀N')
  obtain ⟨γ₀, h0a, h0b, hq0, hT0, hi0, -, hu0, -, -⟩ := h.quant_geom hk₀1 hk₀N'
  obtain ⟨γ, hγa, hγb, hq, hT, hi, -⟩ := h.quant_geom hk1 hkN
  rw [hq0] at hr1
  rw [hq]
  have hmono : γ₀ ≤ γ := by
    refine (hi γ₀).1 ?_
    rw [hT0]
    exact div_le_div_of_nonneg_right (by linarith) hNr.le
  have hQ0nn : 0 ≤ Counting_Q N k₀ := Counting_Q_nonneg hNr.le (by linarith)
  have hΔ0 : 0 ≤ p ^ 2 * Counting_Q N k₀ := by positivity
  have hl0 := abs_le.1 hr1
  have hlk₀ : lam k₀ ≤ lam k := hanti k k₀ hk1 hkk₀ hk₀N'
  have hlk : lam k ≤ lam 1 := hanti 1 k le_rfl hk1 hkN
  have hG : (b - γ₀) ^ 3 ≤ ((k₀ : ℝ) / (N * (c₀ / 4 * Real.sqrt (d / 8)))) ^ 2 := by
    have hu2 : Real.sqrt (b - γ₀) ^ 2 = b - γ₀ := Real.sq_sqrt (by linarith)
    have hu3 : 0 ≤ Real.sqrt (b - γ₀) ^ 3 := by positivity
    calc (b - γ₀) ^ 3 = (Real.sqrt (b - γ₀) ^ 3) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul, hu2]
      _ ≤ _ := pow_le_pow_left₀ hu3 hu0 2
  have key := Counting_range2_arith (N := N) (p := p) (j := k) (k₀ := k₀)
    (κ₁ := c₀ / 4 * Real.sqrt (d / 8)) (M := 1 + 32 * (3 * C₀) ^ 2) (G := b - γ₀)
    (Δ₀ := p ^ 2 * Counting_Q N k₀) (Q₀ := Counting_Q N k₀) (Qj := Counting_Q N k) (w := w)
    hNr hp3 hM hkr hk hk₀b hkk₀r hκ₁ hκ₁p hp4 (by linarith) hG le_rfl hQ0nn
    (Counting_Q_cube' hNr (by linarith)) (Counting_Q_nonneg hNr.le (by linarith))
    (Counting_Q_cube' hNr (by linarith)) hw0 hw
  rw [abs_le]
  constructor <;> linarith [hl0.1, hl0.2]

/-- The edge range at the left edge: `N + 1 - k < M p²`. -/
private lemma Counting_edge_left (h : Counting_SqrtDens ρ a b c₀ C₀ d) {N k k₀ : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (hkk₀ : N + 1 - k₀ ≤ k) (hk₀1 : 1 ≤ k₀) (hk₀N : 2 * k₀ ≤ N) (lam : ℕ → ℝ)
    {p w : ℝ}
    (hp3 : 3 ≤ p) (hpM : 2 * (1 + 8 * (3 * C₀) ^ 2) / c₀ ≤ p)
    (hκ₁p : 216 * (1 + 32 * (3 * C₀) ^ 2) ^ 3 ≤ (c₀ / 4 * Real.sqrt (d / 8)) ^ 2 * p ^ 3)
    (hp4 : 27 * (1 + 32 * (3 * C₀) ^ 2) ≤ p ^ 4)
    (hk : (N : ℝ) + 1 - k < (1 + 32 * (3 * C₀) ^ 2) * p ^ 2)
    (hk₀a : (1 + 32 * (3 * C₀) ^ 2) * p ^ 2 ≤ k₀)
    (hk₀b : (k₀ : ℝ) ≤ 2 * (1 + 32 * (3 * C₀) ^ 2) * p ^ 2)
    (hw0 : 0 ≤ w) (hw : w ^ 3 = p ^ 3 * ((N : ℝ) ^ 2)⁻¹)
    (hanti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ N → lam j ≤ lam i)
    (hwin : a - w ≤ lam N)
    (I1 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N → E ≤ lam k →
      (k : ℝ) ≤ N * Counting_T ρ b E + p)
    (I2 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N → lam k < E →
      N * Counting_T ρ b E - p ≤ k - 1) :
    |lam k - quant ρ N k| ≤ p ^ 3 * Counting_Q N ((N : ℝ) + 1 - k) := by
  set k₁ : ℕ := N + 1 - k₀ with hk₁
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₁N : k₁ ≤ N := by omega
  have hk₁k : k₁ ≤ k := hkk₀
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hC := h.hC₀
  have hc := h.hc₀
  have hd := h.hd
  have hp0 : 0 < p := by linarith
  have hκ₂ : 0 < 3 * C₀ := by positivity
  have hM : (1 : ℝ) ≤ 1 + 32 * (3 * C₀) ^ 2 := by nlinarith [sq_nonneg (3 * C₀)]
  have hκ₁ : 0 < c₀ / 4 * Real.sqrt (d / 8) := by positivity
  have hk₀r : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀1
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkNr : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have h2k₀ : (2 : ℝ) * k₀ ≤ N := by exact_mod_cast hk₀N
  have hk₁r : (k₁ : ℝ) = N + 1 - k₀ := by
    rw [hk₁, Nat.cast_sub (by omega)]; push_cast; ring
  have hj1 : (1 : ℝ) ≤ (N : ℝ) + 1 - k := by linarith
  have hjk₀ : (N : ℝ) + 1 - k ≤ k₀ := by linarith
  -- Range 1 at `k₁`
  have hr1 := Counting_range1 h hk₁1 hk₁N lam (p := p) (r := k₀) (Q := Counting_Q N k₀)
    (by linarith) hpM hk₀a (by rw [hk₁r]; linarith) (by rw [hk₁r]; linarith)
    (Counting_Q_nonneg hNr.le (by linarith)) (Counting_Q_cube' hNr (by linarith))
    (fun E h1 h2 => I1 E h1 h2 k₁ hk₁1 hk₁N) (fun E h1 h2 => I2 E h1 h2 k₁ hk₁1 hk₁N)
  obtain ⟨γ₁, h1a, h1b, hq1, hT1, hi1, -, -, -, hv1⟩ := h.quant_geom hk₁1 hk₁N
  obtain ⟨γ, hγa, hγb, hq, hT, hi, -⟩ := h.quant_geom hk1 hkN
  rw [hq1] at hr1
  rw [hq]
  have hmono : γ ≤ γ₁ := by
    refine (hi1 γ).1 ?_
    rw [hT]
    refine div_le_div_of_nonneg_right ?_ hNr.le
    have : (k₁ : ℝ) ≤ k := by exact_mod_cast hk₁k
    linarith
  have hQ0nn : 0 ≤ Counting_Q N k₀ := Counting_Q_nonneg hNr.le (by linarith)
  have hΔ0 : 0 ≤ p ^ 2 * Counting_Q N k₀ := by positivity
  have hl0 := abs_le.1 hr1
  have hlk₁ : lam k ≤ lam k₁ := hanti k₁ k hk₁1 hk₁k hkN
  have hlk : lam N ≤ lam k := hanti k N hk1 hkN le_rfl
  have hG : (γ₁ - a) ^ 3 ≤ ((k₀ : ℝ) / (N * (c₀ / 4 * Real.sqrt (d / 8)))) ^ 2 := by
    have hv2 : Real.sqrt (γ₁ - a) ^ 2 = γ₁ - a := Real.sq_sqrt (by linarith)
    have hv3 : 0 ≤ Real.sqrt (γ₁ - a) ^ 3 := by positivity
    have hv1' : Real.sqrt (γ₁ - a) ^ 3 ≤ (k₀ : ℝ) / (N * (c₀ / 4 * Real.sqrt (d / 8))) := by
      have e : (N : ℝ) + 1 - k₁ = k₀ := by rw [hk₁r]; ring
      rw [e] at hv1
      exact hv1
    calc (γ₁ - a) ^ 3 = (Real.sqrt (γ₁ - a) ^ 3) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul, hv2]
      _ ≤ _ := pow_le_pow_left₀ hv3 hv1' 2
  have key := Counting_range2_arith (N := N) (p := p) (j := (N : ℝ) + 1 - k) (k₀ := k₀)
    (κ₁ := c₀ / 4 * Real.sqrt (d / 8)) (M := 1 + 32 * (3 * C₀) ^ 2) (G := γ₁ - a)
    (Δ₀ := p ^ 2 * Counting_Q N k₀) (Q₀ := Counting_Q N k₀)
    (Qj := Counting_Q N ((N : ℝ) + 1 - k)) (w := w)
    hNr hp3 hM hj1 hk hk₀b hjk₀ hκ₁ hκ₁p hp4 (by linarith) hG le_rfl hQ0nn
    (Counting_Q_cube' hNr (by linarith)) (Counting_Q_nonneg hNr.le (by linarith))
    (Counting_Q_cube' hNr (by linarith)) hw0 hw
  rw [abs_le]
  constructor <;> linarith [hl0.1, hl0.2]

set_option maxHeartbeats 1000000 in
/-- The abstract rigidity from counting: the counting inequalities, the monotone sequence `lam`
and the edge window give `|λ_k - γ_k| ≤ N^{3s} N^{-2/3} min(k, N+1-k)^{-1/3}`. -/
private lemma Counting_rigidity_core {c₀ C₀ d : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hd : 0 < d) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1 / 20) :
    ∃ N₀ : ℕ, ∀ (ρ : ℝ → ℝ) (a b : ℝ), Counting_SqrtDens ρ a b c₀ C₀ d → ∀ N : ℕ, N₀ ≤ N →
      ∀ lam : ℕ → ℝ, (∀ i j, 1 ≤ i → i ≤ j → j ≤ N → lam j ≤ lam i) →
      a - (N : ℝ) ^ (-(2 / 3 : ℝ) + s) ≤ lam N → lam 1 ≤ b + (N : ℝ) ^ (-(2 / 3 : ℝ) + s) →
      (∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N →
        (E ≤ lam k → (k : ℝ) ≤ N * Counting_T ρ b E + (N : ℝ) ^ s) ∧
        (lam k < E → N * Counting_T ρ b E - (N : ℝ) ^ s ≤ k - 1)) →
      ∀ k : ℕ, 1 ≤ k → k ≤ N →
        |lam k - quant ρ N k| ≤ (N : ℝ) ^ (3 * s) *
          ((N : ℝ) ^ (-(2 / 3 : ℝ)) * ((min k (N + 1 - k) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by
  set κ₂ : ℝ := 3 * C₀ with hκ₂
  set M : ℝ := 1 + 32 * κ₂ ^ 2 with hM
  set κ₁ : ℝ := c₀ / 4 * Real.sqrt (d / 8) with hκ₁
  have hκ₂0 : 0 < κ₂ := by positivity
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [sq_nonneg κ₂]
  have hκ₁0 : 0 < κ₁ := by positivity
  set P₀ : ℝ := 3 + 2 * (1 + 8 * κ₂ ^ 2) / c₀ + 216 * M ^ 3 / κ₁ ^ 2 + 27 * M with hP₀
  have hP₀3 : 3 ≤ P₀ := by
    have h1 : 0 ≤ 2 * (1 + 8 * κ₂ ^ 2) / c₀ := by positivity
    have h2 : 0 ≤ 216 * M ^ 3 / κ₁ ^ 2 := by positivity
    have h3 : 0 ≤ 27 * M := by positivity
    rw [hP₀]; linarith
  have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ P₀ ≤ x ^ s ∧ 4 * M * (x ^ s) ^ 2 ≤ x := by
    have e1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
    have e2 : ∀ᶠ x : ℝ in atTop, P₀ ≤ x ^ s := (tendsto_rpow_atTop hs).eventually_ge_atTop P₀
    have e3 : ∀ᶠ x : ℝ in atTop, 4 * M ≤ x ^ (1 - 2 * s) :=
      (tendsto_rpow_atTop (by linarith : 0 < 1 - 2 * s)).eventually_ge_atTop (4 * M)
    filter_upwards [e1, e2, e3] with x h1 h2 h3
    refine ⟨h1, h2, ?_⟩
    have hx : 0 < x := by linarith
    have : x = x ^ (1 - 2 * s) * (x ^ s) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      have : 1 - 2 * s + s * ((2 : ℕ) : ℝ) = 1 := by push_cast; ring
      rw [this, Real.rpow_one]
    calc 4 * M * (x ^ s) ^ 2 ≤ x ^ (1 - 2 * s) * (x ^ s) ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = x := this.symm
  obtain ⟨N₀, hN₀⟩ := Counting_eventually_nat hev
  refine ⟨N₀, fun ρ a b h N hN lam hanti hlo hhi hcount k hk1 hkN => ?_⟩
  obtain ⟨hN1, hP, h4⟩ := hN₀ N hN
  have hNr : (0 : ℝ) < N := by linarith
  set p : ℝ := (N : ℝ) ^ s with hp
  have hp3 : 3 ≤ p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hpM : 2 * (1 + 8 * κ₂ ^ 2) / c₀ ≤ p := by
    have : 0 ≤ 216 * M ^ 3 / κ₁ ^ 2 := by positivity
    have : 0 ≤ 27 * M := by positivity
    linarith
  have hκ₁p : 216 * M ^ 3 ≤ κ₁ ^ 2 * p ^ 3 := by
    have h1 : 216 * M ^ 3 / κ₁ ^ 2 ≤ p := by
      have : 0 ≤ 2 * (1 + 8 * κ₂ ^ 2) / c₀ := by positivity
      have : 0 ≤ 27 * M := by positivity
      linarith
    have h2 : p ≤ p ^ 3 := by nlinarith [sq_nonneg p]
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith [sq_nonneg κ₁]
  have hp4 : 27 * M ≤ p ^ 4 := by
    have h1 : 27 * M ≤ p := by
      have : 0 ≤ 2 * (1 + 8 * κ₂ ^ 2) / c₀ := by positivity
      have : 0 ≤ 216 * M ^ 3 / κ₁ ^ 2 := by positivity
      linarith
    have h2 : p ≤ p ^ 4 := by
      calc p = p * 1 := by ring
        _ ≤ p * p ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hp1) hp0.le
        _ = p ^ 4 := by ring
    linarith
  -- the window width `w`
  set w : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ)) * p with hw
  have hwe : (N : ℝ) ^ (-(2 / 3 : ℝ) + s) = w := by
    rw [Real.rpow_add hNr]
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw3 : w ^ 3 = p ^ 3 * ((N : ℝ) ^ 2)⁻¹ := by
    rw [hw, mul_pow, Counting_nu_cube hNr]; ring
  rw [hwe] at hlo hhi
  have h3s : (N : ℝ) ^ (3 * s) = p ^ 3 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    norm_num; ring_nf
  rw [h3s]
  -- the ratio `r`
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkNr : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hr_eq : (((min k (N + 1 - k) : ℕ)) : ℝ) = min (k : ℝ) ((N : ℝ) + 1 - k) := by
    rw [Nat.cast_min, Nat.cast_sub (by omega)]; push_cast; ring_nf
  rw [hr_eq]
  set r : ℝ := min (k : ℝ) ((N : ℝ) + 1 - k) with hr
  have hr1 : 1 ≤ r := le_min hkr (by linarith)
  have hr0 : 0 < r := by linarith
  have hrk : r ≤ k := min_le_left _ _
  have hrk' : r ≤ (N : ℝ) + 1 - k := min_le_right _ _
  have hQr0 : 0 ≤ Counting_Q N r := Counting_Q_nonneg hNr.le hr0.le
  have hI1 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N → E ≤ lam k →
      (k : ℝ) ≤ N * Counting_T ρ b E + p := fun E h1 h2 k hk1 hkN => (hcount E h1 h2 k hk1 hkN).1
  have hI2 : ∀ E, a - 1 ≤ E → E ≤ b + 1 → ∀ k : ℕ, 1 ≤ k → k ≤ N → lam k < E →
      N * Counting_T ρ b E - p ≤ k - 1 := fun E h1 h2 k hk1 hkN => (hcount E h1 h2 k hk1 hkN).2
  by_cases hrM : M * p ^ 2 ≤ r
  · have := Counting_range1 h hk1 hkN lam (p := p) (r := r) (Q := Counting_Q N r) hp1 hpM hrM hrk
      hrk' hQr0 (Counting_Q_cube' hNr hr0) (fun E h1 h2 => hI1 E h1 h2 k hk1 hkN)
      (fun E h1 h2 => hI2 E h1 h2 k hk1 hkN)
    refine this.trans ?_
    calc p ^ 2 * Counting_Q N r ≤ p ^ 3 * Counting_Q N r := by
          refine mul_le_mul_of_nonneg_right ?_ hQr0
          nlinarith
      _ = p ^ 3 * (N ^ (-(2 / 3 : ℝ)) * r ^ (-(1 / 3 : ℝ))) := rfl
  · -- the edge ranges
    rw [not_le] at hrM
    have hMp : (1 : ℝ) ≤ M * p ^ 2 := by nlinarith
    set k₀ : ℕ := ⌈M * p ^ 2⌉₊ with hk₀
    have hk₀a : M * p ^ 2 ≤ k₀ := Nat.le_ceil _
    have hk₀b : (k₀ : ℝ) ≤ 2 * M * p ^ 2 := by
      have := Nat.ceil_lt_add_one (by positivity : 0 ≤ M * p ^ 2)
      linarith
    have hk₀1 : 1 ≤ k₀ := by
      have : (1 : ℝ) ≤ k₀ := by linarith
      exact_mod_cast this
    have hk₀N : 2 * k₀ ≤ N := by
      have : (2 * k₀ : ℝ) ≤ N := by linarith
      exact_mod_cast this
    have hcast : (N : ℝ) * 1 = N := mul_one _
    rcases min_lt_iff.1 hrM with hlt | hlt
    · have hkk₀ : k ≤ k₀ := by
        have : (k : ℝ) ≤ k₀ := by linarith
        exact_mod_cast this
      have := Counting_edge_right h hk1 hkk₀ hk₀N lam hp3 hpM hκ₁p hp4 hlt hk₀a hk₀b hw0 hw3
        hanti hhi hI1 hI2
      refine this.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Counting_Q_anti hNr hr0 hrk
    · have hkk₀ : N + 1 - k₀ ≤ k := by
        have h1 : (N : ℝ) + 1 - k ≤ k₀ := by linarith
        have h2 : (N : ℝ) + 1 ≤ k + k₀ := by linarith
        have h3 : N + 1 ≤ k + k₀ := by exact_mod_cast h2
        omega
      have := Counting_edge_left h hk1 hkN hkk₀ hk₀1 hk₀N lam hp3 hpM hκ₁p hp4 hlt hk₀a hk₀b hw0
        hw3 hanti hlo hI1 hI2
      refine this.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Counting_Q_anti hNr hr0 hrk'

end P6

section P7

variable {ρ : ℝ → ℝ} {a b c₀ C₀ d : ℝ}

private lemma Counting_SqrtDens.integral_Eb1 (h : Counting_SqrtDens ρ a b c₀ C₀ d) (E : ℝ) :
    ∫ x in E..(b + 1), ρ x = Counting_T ρ b E := by
  unfold Counting_T
  rw [← intervalIntegral.integral_add_adjacent_intervals (h.intInt E b) (h.intInt b (b + 1))]
  have : ∫ x in b..(b + 1), ρ x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact h.zero_right t ht.1
  rw [this, add_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `eigK X k` is the `(k-1)`-th ordered eigenvalue. -/
private lemma Counting_eigK_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) :
    eigK X k = hX.eigenvalues₀ ⟨k - 1, by omega⟩ := by
  have h1 : k - 1 < Fintype.card ι := by omega
  simp only [eigK, eigs, h1, hX, ↓reduceDIte]

/-- The ordered eigenvalue `λ_k` is at least `E` iff at least `k` eigenvalues are `≥ E`. -/
private lemma Counting_evCount_iff (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (E bb : ℝ)
    (hb : ∀ j, hX.eigenvalues₀ j ≤ bb) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) :
    E ≤ eigK X k ↔ k ≤ evCount X E bb := by
  rw [Counting_eigK_eq X hX hk1 hk]
  have hS : evCount X E bb =
      (Finset.univ.filter fun j : Fin (Fintype.card ι) => E ≤ hX.eigenvalues₀ j).card := by
    unfold evCount eigs
    simp only [hX, ↓reduceDIte]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    intro _; exact hb j
  rw [hS]
  set j0 : Fin (Fintype.card ι) := ⟨k - 1, by omega⟩ with hj0
  have hanti := hX.eigenvalues₀_antitone
  constructor
  · intro hE
    have : Finset.Iic j0 ⊆ Finset.univ.filter fun j : Fin (Fintype.card ι) => E ≤ hX.eigenvalues₀ j := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hE.trans (hanti hi)
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    simp only [hj0] at this
    omega
  · intro hc
    by_contra hE
    rw [not_le] at hE
    have : (Finset.univ.filter fun j : Fin (Fintype.card ι) => E ≤ hX.eigenvalues₀ j) ⊆
        Finset.Iio j0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hij
      rw [not_lt] at hij
      have := hanti hij
      linarith
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this
    simp only [hj0] at this
    omega

end P7

/-- Rigidity from counting (deterministic), with (2.21) [eq:kappa_gamma_k] from the square-root
density: for `0 < s ≤ 1/20` and `n = card ι ≥ n₀(s)`, Hermitian `Λ` with `‖Λ‖ ≤ 1/10` and Hermitian
`X` whose eigenvalues lie in `[E⁻ - n^{-2/3+s}, E⁺ + n^{-2/3+s}]` and whose counts satisfy
`|#(X ∩ [E, E⁺+1]) - n ∫_E^{E⁺+1} ρ_N| ≤ n^s` for `E ∈ [E⁻ - 1, E⁺ + 1]`,
`|λ_k - γ_k| ≤ n^{3s} n^{-2/3} min(k, n+1-k)^{-1/3}` for every `k ∈ ⟦1, n⟧`, `γ_k` the quantile
(2.20) [eq:gammak] of `ρ_N` with `n` particles. -/
theorem rigidity_of_count (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1 / 20) :
    ∃ n₀ : ℕ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι], n₀ ≤ Fintype.card ι →
      ∀ Λ : Matrix ι ι ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ X : Matrix ι ι ℂ, X.IsHermitian →
      Eminus Λ - (Fintype.card ι : ℝ) ^ (-(2 / 3 : ℝ) + s) ≤ eigK X (Fintype.card ι) →
      eigK X 1 ≤ Eplus Λ + (Fintype.card ι : ℝ) ^ (-(2 / 3 : ℝ) + s) →
      (∀ E : ℝ, Eminus Λ - 1 ≤ E → E ≤ Eplus Λ + 1 →
        |(evCount X E (Eplus Λ + 1) : ℝ) -
            (Fintype.card ι : ℝ) * ∫ x in E..(Eplus Λ + 1), rho Λ x| ≤
          (Fintype.card ι : ℝ) ^ s) →
      ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι →
        |eigK X k - quant (rho Λ) (Fintype.card ι) k| ≤
          (Fintype.card ι : ℝ) ^ (3 * s) * ((Fintype.card ι : ℝ) ^ (-(2 / 3 : ℝ)) *
            rk 1 (Fintype.card ι) k ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨c₀, C₀, d, hc₀, hC₀, hd, hall⟩ := Counting_sqrtDens_exists
  obtain ⟨N₀, hcore⟩ := Counting_rigidity_core hc₀ hC₀ hd s hs hs1
  refine ⟨N₀, fun ι _ _ _ hn Λ hΛ hℓ X hX hlo hhi hcount k hk1 hkN => ?_⟩
  have hρ := hall ι Λ hΛ hℓ
  set N := Fintype.card ι with hN
  have hNr : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := Fintype.card_pos
    exact_mod_cast this
  have hanti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ N → eigK X j ≤ eigK X i := by
    intro i j hi hij hj
    rw [Counting_eigK_eq X hX hi (by omega), Counting_eigK_eq X hX (by omega) hj]
    exact hX.eigenvalues₀_antitone (Fin.mk_le_mk.2 (by omega))
  have hexp : (-(2 / 3 : ℝ) + s) ≤ 0 := by linarith
  have hw1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr hexp
  have hb : ∀ j, hX.eigenvalues₀ j ≤ Eplus Λ + 1 := by
    intro j
    have h1 : hX.eigenvalues₀ j ≤ hX.eigenvalues₀ ⟨0, by omega⟩ :=
      hX.eigenvalues₀_antitone (Fin.mk_le_mk.2 (Nat.zero_le _))
    have h2 := Counting_eigK_eq X hX (k := 1) le_rfl (by omega)
    have h5 : hX.eigenvalues₀ ⟨0, by omega⟩ = eigK X 1 := by rw [h2]
    linarith
  have hlam : ∀ E : ℝ, ∀ k : ℕ, 1 ≤ k → k ≤ N → (E ≤ eigK X k ↔ k ≤ evCount X E (Eplus Λ + 1)) :=
    fun E k hk1 hkN => Counting_evCount_iff X hX E _ hb hk1 hkN
  have hcore' := hcore (rho Λ) (Eminus Λ) (Eplus Λ) hρ N hn (eigK X) hanti hlo hhi ?_ k hk1 hkN
  · simpa only [rk, one_mul] using hcore'
  · intro E h1 h2 k hk1 hkN
    have hc := hcount E h1 h2
    rw [hρ.integral_Eb1 E, abs_le] at hc
    rw [hlam E k hk1 hkN]
    constructor
    · intro hk
      have : (k : ℝ) ≤ evCount X E (Eplus Λ + 1) := by exact_mod_cast hk
      linarith [hc.2]
    · intro hk
      have hk' : ¬ (k ≤ evCount X E (Eplus Λ + 1)) := fun h' =>
        absurd ((hlam E k hk1 hkN).2 h') (not_le.2 hk)
      have h3 : evCount X E (Eplus Λ + 1) + 1 ≤ k := by omega
      have : (evCount X E (Eplus Λ + 1) : ℝ) + 1 ≤ k := by exact_mod_cast h3
      linarith [hc.1]

section P8a

/-- `q_η(d) = (π/2 - arctan(|d|/η))/π`, the tail of the Poisson kernel. -/
private def Counting_q (η d : ℝ) : ℝ := (Real.pi / 2 - Real.arctan (|d| / η)) / Real.pi

/-- The Poisson kernel `P_y(d) = y/(d² + y²)`. -/
private def Counting_P (y d : ℝ) : ℝ := y / (d ^ 2 + y ^ 2)

/-- The Poisson-smoothed indicator of `[E, E₂]`. -/
private def Counting_f (η E E₂ t : ℝ) : ℝ :=
  (Real.arctan ((E₂ - t) / η) - Real.arctan ((E - t) / η)) / Real.pi

private lemma Counting_q_nonneg (η d : ℝ) : 0 ≤ Counting_q η d := by
  unfold Counting_q
  have := Real.arctan_lt_pi_div_two (|d| / η)
  have := Real.pi_pos
  positivity

private lemma Counting_q_le_half {η : ℝ} (hη : 0 < η) (d : ℝ) : Counting_q η d ≤ 1 / 2 := by
  unfold Counting_q
  have h0 : 0 ≤ Real.arctan (|d| / η) := Real.arctan_nonneg.2 (by positivity)
  rw [div_le_iff₀ Real.pi_pos]
  linarith

private lemma Counting_q_mul_le {η : ℝ} (hη : 0 < η) (d : ℝ) : Counting_q η d * |d| ≤ η / Real.pi := by
  unfold Counting_q
  rcases eq_or_ne d 0 with h | h
  · simp [h]; positivity
  · have hd : 0 < |d| := abs_pos.2 h
    have hx : 0 < |d| / η := by positivity
    have h1 : Real.pi / 2 - Real.arctan (|d| / η) = Real.arctan (|d| / η)⁻¹ := by
      rw [Real.arctan_inv_of_pos hx]
    rw [h1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right Real.pi_pos]
    have h2 := Real.arctan_le_self (inv_nonneg.2 hx.le)
    calc Real.arctan (|d| / η)⁻¹ * |d| ≤ (|d| / η)⁻¹ * |d| :=
          mul_le_mul_of_nonneg_right h2 hd.le
      _ = η := by field_simp

/-- Pointwise: `|1_{[E,E₂]} - f| ≤ q(t - E) + q(t - E₂)`. -/
private lemma Counting_ind_le {η E E₂ : ℝ} (hη : 0 < η) (hE : E ≤ E₂) (t : ℝ) :
    |(if t ∈ Set.Icc E E₂ then (1 : ℝ) else 0) - Counting_f η E E₂ t| ≤
      Counting_q η (t - E) + Counting_q η (t - E₂) := by
  have hπ := Real.pi_pos
  set u : ℝ := (E₂ - t) / η with hu
  set v : ℝ := (t - E) / η with hv
  have hEt : (E - t) / η = -v := by rw [hv]; field_simp; ring
  have hq1 : Counting_q η (t - E) = (Real.pi / 2 - Real.arctan |v|) / Real.pi := by
    unfold Counting_q; rw [hv, abs_div, abs_of_pos hη]
  have hq2 : Counting_q η (t - E₂) = (Real.pi / 2 - Real.arctan |u|) / Real.pi := by
    unfold Counting_q
    rw [hu, abs_div, abs_of_pos hη, abs_sub_comm]
  have hf : Counting_f η E E₂ t = (Real.arctan u + Real.arctan v) / Real.pi := by
    unfold Counting_f; rw [hEt, Real.arctan_neg, ← hu]; ring
  rw [hq1, hq2, hf]
  have hA := Real.arctan_lt_pi_div_two u
  have hB := Real.arctan_lt_pi_div_two v
  have hA' := Real.arctan_lt_pi_div_two |u|
  have hB' := Real.arctan_lt_pi_div_two |v|
  have hA0 : 0 ≤ Real.arctan |u| := Real.arctan_nonneg.2 (abs_nonneg _)
  have hB0 : 0 ≤ Real.arctan |v| := Real.arctan_nonneg.2 (abs_nonneg _)
  by_cases hI : t ∈ Set.Icc E E₂
  · simp only [hI, ↓reduceIte]
    have hu0 : 0 ≤ u := div_nonneg (by linarith [hI.2]) hη.le
    have hv0 : 0 ≤ v := div_nonneg (by linarith [hI.1]) hη.le
    rw [abs_of_nonneg hu0, abs_of_nonneg hv0]
    have : (1 : ℝ) - (Real.arctan u + Real.arctan v) / Real.pi =
        (Real.pi / 2 - Real.arctan v) / Real.pi + (Real.pi / 2 - Real.arctan u) / Real.pi := by
      field_simp; ring
    rw [this, abs_of_nonneg]
    have h1 : 0 ≤ (Real.pi / 2 - Real.arctan v) / Real.pi := div_nonneg (by linarith) hπ.le
    have h2 : 0 ≤ (Real.pi / 2 - Real.arctan u) / Real.pi := div_nonneg (by linarith) hπ.le
    linarith
  · simp only [hI, ↓reduceIte, zero_sub, abs_neg]
    have hqq1 : 0 ≤ (Real.pi / 2 - Real.arctan |v|) / Real.pi := div_nonneg (by linarith) hπ.le
    have hqq2 : 0 ≤ (Real.pi / 2 - Real.arctan |u|) / Real.pi := div_nonneg (by linarith) hπ.le
    rcases not_and_or.1 hI with h | h
    · -- `t < E`
      rw [not_le] at h
      have hv0 : v < 0 := div_neg_of_neg_of_pos (by linarith) hη
      have hle : -v ≤ u := by
        rw [← hEt, hu]; exact div_le_div_of_nonneg_right (by linarith) hη.le
      have h1 : Real.arctan (-v) ≤ Real.arctan u := Real.arctan_mono hle
      rw [Real.arctan_neg] at h1
      have e : Real.arctan |v| = -Real.arctan v := by
        rw [abs_of_neg hv0, Real.arctan_neg]
      rw [abs_of_nonneg (div_nonneg (by linarith) hπ.le)]
      have : (Real.arctan u + Real.arctan v) / Real.pi ≤
          (Real.pi / 2 - Real.arctan |v|) / Real.pi := by
        rw [div_le_div_iff_of_pos_right hπ, e]; linarith
      linarith
    · -- `E₂ < t`
      rw [not_le] at h
      have hu0 : u < 0 := div_neg_of_neg_of_pos (by linarith) hη
      have hle : -u ≤ v := by
        rw [hu, hv, ← neg_div]
        exact div_le_div_of_nonneg_right (by linarith) hη.le
      have h1 : Real.arctan (-u) ≤ Real.arctan v := Real.arctan_mono hle
      rw [Real.arctan_neg] at h1
      have e : Real.arctan |u| = -Real.arctan u := by
        rw [abs_of_neg hu0, Real.arctan_neg]
      rw [abs_of_nonneg (div_nonneg (by linarith) hπ.le)]
      have : (Real.arctan u + Real.arctan v) / Real.pi ≤
          (Real.pi / 2 - Real.arctan |u|) / Real.pi := by
        rw [div_le_div_iff_of_pos_right hπ, e]; linarith
      linarith

private lemma Counting_P_nonneg {y : ℝ} (hy : 0 < y) (d : ℝ) : 0 ≤ Counting_P y d := by
  unfold Counting_P; positivity

private lemma Counting_P_ge {y : ℝ} (hy : 0 < y) {d : ℝ} (hd : |d| ≤ y) : 1 / (2 * y) ≤ Counting_P y d := by
  unfold Counting_P
  have h1 : d ^ 2 ≤ y ^ 2 := by
    have := sq_abs d
    nlinarith [abs_nonneg d]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The dyadic bound of the Poisson tail by Poisson kernels at heights `2^j η`. -/
private lemma Counting_q_dyadic {η : ℝ} (hη : 0 < η) (J : ℕ) :
    ∀ d : ℝ, |d| ≤ 2 ^ J * η →
      Counting_q η d ≤ 2 * η * ∑ j ∈ Finset.range (J + 1), Counting_P (2 ^ j * η) d := by
  induction J with
  | zero =>
    intro d hd
    simp only [pow_zero, one_mul, zero_add, Finset.range_one, Finset.sum_singleton] at hd ⊢
    have h1 := Counting_P_ge hη hd
    have h2 := Counting_q_le_half hη d
    have : 1 ≤ 2 * η * Counting_P η d := by
      calc (1 : ℝ) = 2 * η * (1 / (2 * η)) := by field_simp
        _ ≤ 2 * η * Counting_P η d := mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  | succ J ih =>
    intro d hd
    rw [Finset.sum_range_succ, mul_add]
    have hP := Counting_P_nonneg (by positivity : 0 < 2 ^ (J + 1) * η) d
    by_cases hJ : |d| ≤ 2 ^ J * η
    · have := ih d hJ
      have h3 : 0 ≤ 2 * η * Counting_P (2 ^ (J + 1) * η) d := by positivity
      linarith
    · rw [not_le] at hJ
      have hc : 0 < 2 ^ J * η := by positivity
      have hq := Counting_q_mul_le hη d
      have hq0 := Counting_q_nonneg η d
      have h1 : Counting_q η d * (2 ^ J * η) ≤ η / Real.pi :=
        (mul_le_mul_of_nonneg_left hJ.le hq0).trans hq
      have h2 : Counting_q η d ≤ η / Real.pi / (2 ^ J * η) := by
        rw [le_div_iff₀ hc]; exact h1
      have h3 := Counting_P_ge (by positivity : 0 < 2 ^ (J + 1) * η) hd
      have hpi : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have h4 : η / Real.pi / (2 ^ J * η) ≤ 2 * η * (1 / (2 * (2 ^ (J + 1) * η))) := by
        rw [div_div, div_le_iff₀ (by positivity)]
        have : 2 * η * (1 / (2 * (2 ^ (J + 1) * η))) * (Real.pi * (2 ^ J * η)) =
            Real.pi * η / 2 := by
          rw [pow_succ]; field_simp
        rw [this]
        nlinarith
      have h5 : 2 * η * (1 / (2 * (2 ^ (J + 1) * η))) ≤ 2 * η * Counting_P (2 ^ (J + 1) * η) d :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have hs : 0 ≤ 2 * η * ∑ j ∈ Finset.range (J + 1), Counting_P (2 ^ j * η) d := by
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
        exact Counting_P_nonneg (by positivity) d
      linarith

/-- `q_η(d) ≤ η + 2η Σ_{j ≤ J} P_{2^j η}(d)` when `2^J η ≥ 1`. -/
private lemma Counting_q_le_ladder {η : ℝ} (hη : 0 < η) (J : ℕ) (hJ : 1 ≤ 2 ^ J * η) (d : ℝ) :
    Counting_q η d ≤ η + 2 * η * ∑ j ∈ Finset.range (J + 1), Counting_P (2 ^ j * η) d := by
  have hs : 0 ≤ 2 * η * ∑ j ∈ Finset.range (J + 1), Counting_P (2 ^ j * η) d := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
    exact Counting_P_nonneg (by positivity) d
  by_cases hd : |d| ≤ 2 ^ J * η
  · have := Counting_q_dyadic hη J d hd
    linarith
  · rw [not_le] at hd
    have hq := Counting_q_mul_le hη d
    have hq0 := Counting_q_nonneg η d
    have h1 : Counting_q η d * 1 ≤ η / Real.pi :=
      (mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ |d|) hq0).trans hq
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h2 : η / Real.pi ≤ η := div_le_self hη.le hpi
    linarith

end P8a

section P8b

private lemma Counting_P_cont {y : ℝ} (hy : 0 < y) : Continuous fun d : ℝ => Counting_P y d := by
  unfold Counting_P
  have h : Continuous fun d : ℝ => d ^ 2 + y ^ 2 := by fun_prop
  exact continuous_const.div h fun d => (by positivity : d ^ 2 + y ^ 2 ≠ 0)

private lemma Counting_P_le {y : ℝ} (hy : 0 < y) (d : ℝ) : Counting_P y d ≤ 1 / y := by
  unfold Counting_P
  rw [div_le_div_iff₀ (by positivity) hy]
  nlinarith [sq_nonneg d, sq_nonneg y]

/-- Fubini for the Poisson smoothing of a continuous integrable density. -/
private lemma Counting_fubini {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hint : Integrable ρ) {η : ℝ}
    (hη : 0 < η) {E E₂ : ℝ} (hE : E ≤ E₂) :
    ∫ x in E..E₂, ∫ t, ρ t * Counting_P η (t - x) =
      ∫ t, ρ t * (Real.arctan ((E₂ - t) / η) - Real.arctan ((E - t) / η)) := by
  rw [intervalIntegral.integral_of_le hE]
  have hF : Integrable (Function.uncurry fun (x t : ℝ) => ρ t * Counting_P η (t - x))
      ((volume.restrict (Set.Ioc E E₂)).prod volume) := by
    have hg : Integrable (fun z : ℝ × ℝ => (1 / η) * ‖ρ z.2‖)
        ((volume.restrict (Set.Ioc E E₂)).prod volume) :=
      (hint.norm.comp_snd (volume.restrict (Set.Ioc E E₂))).const_mul (1 / η)
    refine hg.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have : Continuous fun z : ℝ × ℝ => ρ z.2 * Counting_P η (z.2 - z.1) :=
        (hρ.comp continuous_snd).mul ((Counting_P_cont hη).comp (continuous_snd.sub continuous_fst))
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
      have h1 := Counting_P_le hη (z.2 - z.1)
      have h2 := Counting_P_nonneg hη (z.2 - z.1)
      rw [abs_of_nonneg h2, mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  rw [integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hE]
  congr 1
  exact Counting_integral_poisson t E E₂ η hη

private lemma Counting_q_cont {η : ℝ} (_hη : 0 < η) : Continuous fun d : ℝ => Counting_q η d := by
  unfold Counting_q
  have h1 : Continuous fun d : ℝ => |d| / η := continuous_abs.div_const η
  exact (continuous_const.sub (Real.continuous_arctan.comp h1)).div_const _

section Dens

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The Poisson representation of `Im m`. -/
private lemma Counting_im_mSol (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x y : ℝ) (hy : 0 < y) :
    (mSol Λ ((x : ℂ) + (y : ℂ) * Complex.I)).im = ∫ t, rho Λ t * Counting_P y (t - x) := by
  obtain ⟨hnn, hcont, hint, hmass, hrep⟩ := rho_stieltjes Λ hΛ hℓ
  have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [hrep _ hz]
  have hfi : Integrable (fun t : ℝ => (rho Λ t : ℂ) / ((t : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))) := by
    have h1 : Integrable (fun t : ℝ => (rho Λ t : ℂ)) := hint.ofReal
    have h2 : AEStronglyMeasurable (fun t : ℝ => (((t : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹))
        volume := by
      refine Continuous.aestronglyMeasurable ?_
      refine Continuous.inv₀ (by fun_prop) fun t h => ?_
      have := congrArg Complex.im h
      simp at this
      linarith
    have h3 := h1.mul_bdd (c := 1 / y) h2 (Filter.Eventually.of_forall fun t => ?_)
    · refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
      simp [div_eq_mul_inv]
    · rw [norm_inv]
      rw [inv_le_comm₀ (norm_pos_iff.2 ?_) (by positivity)]
      · have := Complex.abs_im_le_norm (((t : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)))
        simp at this
        rw [one_div, inv_inv]
        calc y = |y| := (abs_of_pos hy).symm
          _ ≤ _ := this
      · intro h
        have := congrArg Complex.im h
        simp at this
        linarith
  have := integral_im (𝕜 := ℂ) hfi
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Counting_im_inv t x y]
  rfl

private lemma Counting_f_cont {η : ℝ} (E E₂ : ℝ) : Continuous fun t : ℝ => Counting_f η E E₂ t := by
  unfold Counting_f
  have h1 : Continuous fun t : ℝ => (E₂ - t) / η := (continuous_const.sub continuous_id).div_const η
  have h2 : Continuous fun t : ℝ => (E - t) / η := (continuous_const.sub continuous_id).div_const η
  exact ((Real.continuous_arctan.comp h1).sub (Real.continuous_arctan.comp h2)).div_const _

private lemma Counting_f_bdd (η E E₂ t : ℝ) : |Counting_f η E E₂ t| ≤ 1 := by
  unfold Counting_f
  have h1 := Real.arctan_lt_pi_div_two ((E₂ - t) / η)
  have h2 := Real.arctan_lt_pi_div_two ((E - t) / η)
  have h3 := Real.neg_pi_div_two_lt_arctan ((E₂ - t) / η)
  have h4 := Real.neg_pi_div_two_lt_arctan ((E - t) / η)
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos, abs_le]
  constructor <;> linarith

/-- The smoothing error of a density: comparison of `∫ ρ (arctan - arctan)` with `π ∫_{[E,E₂]} ρ`. -/
private lemma Counting_dens_err {ρ : ℝ → ℝ} (_hρ : Continuous ρ) (hint : Integrable ρ)
    (hnn : ∀ x, 0 ≤ ρ x) {η : ℝ} (hη : 0 < η) {E E₂ : ℝ} (hE : E ≤ E₂) {B : ℝ}
    (hB1 : ∫ t, ρ t * Counting_q η (t - E) ≤ B) (hB2 : ∫ t, ρ t * Counting_q η (t - E₂) ≤ B) :
    |(∫ t, ρ t * (Real.arctan ((E₂ - t) / η) - Real.arctan ((E - t) / η))) -
        Real.pi * ∫ t in Set.Icc E E₂, ρ t| ≤ Real.pi * (2 * B) := by
  have hπ := Real.pi_pos
  set ind : ℝ → ℝ := fun t => if t ∈ Set.Icc E E₂ then (1 : ℝ) else 0 with hind
  have hind_meas : Measurable ind := by
    refine Measurable.ite measurableSet_Icc measurable_const measurable_const
  have hint1 : ∀ g : ℝ → ℝ, Continuous g → (∃ c, ∀ t, |g t| ≤ c) → Integrable (fun t => ρ t * g t) := by
    intro g hg ⟨c, hc⟩
    exact hint.mul_bdd (c := c) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      simpa using hc t)
  have hIcc : ∫ t in Set.Icc E E₂, ρ t = ∫ t, ρ t * ind t := by
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Set.indicator, hind]
    split_ifs <;> simp
  have hI : Integrable (fun t => ρ t * ind t) := by
    have : (fun t => ρ t * ind t) = Set.indicator (Set.Icc E E₂) ρ := by
      funext t; simp only [Set.indicator, hind]; split_ifs <;> simp
    rw [this]
    exact hint.indicator measurableSet_Icc
  have hA : Integrable (fun t => ρ t * Counting_f η E E₂ t) :=
    hint1 _ (Counting_f_cont E E₂) ⟨1, Counting_f_bdd η E E₂⟩
  have hq1 : Integrable (fun t => ρ t * Counting_q η (t - E)) :=
    hint1 (fun t => Counting_q η (t - E)) ((Counting_q_cont hη).comp (continuous_id.sub continuous_const))
      ⟨1 / 2, fun t => by
        rw [abs_of_nonneg (Counting_q_nonneg _ _)]; exact Counting_q_le_half hη _⟩
  have hq2 : Integrable (fun t => ρ t * Counting_q η (t - E₂)) :=
    hint1 (fun t => Counting_q η (t - E₂)) ((Counting_q_cont hη).comp (continuous_id.sub continuous_const))
      ⟨1 / 2, fun t => by
        rw [abs_of_nonneg (Counting_q_nonneg _ _)]; exact Counting_q_le_half hη _⟩
  have e1 : ∫ t, ρ t * (Real.arctan ((E₂ - t) / η) - Real.arctan ((E - t) / η)) =
      Real.pi * ∫ t, ρ t * Counting_f η E E₂ t := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Counting_f]
    field_simp
  rw [e1, hIcc, ← mul_sub, abs_mul, abs_of_pos hπ]
  refine mul_le_mul_of_nonneg_left ?_ hπ.le
  rw [← integral_sub hA hI]
  have hq12 : Integrable (fun t => ρ t * (Counting_q η (t - E) + Counting_q η (t - E₂))) := by
    refine (hq1.add hq2).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, mul_add]
  have h1 : |∫ t, (ρ t * Counting_f η E E₂ t - ρ t * ind t)| ≤
      ∫ t, ρ t * (Counting_q η (t - E) + Counting_q η (t - E₂)) := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _)
      hq12 (Filter.Eventually.of_forall fun t => ?_)
    show |ρ t * Counting_f η E E₂ t - ρ t * ind t| ≤
      ρ t * (Counting_q η (t - E) + Counting_q η (t - E₂))
    rw [← mul_sub, abs_mul, abs_of_nonneg (hnn t), abs_sub_comm]
    have := Counting_ind_le hη hE t
    exact mul_le_mul_of_nonneg_left (by simpa [hind] using this) (hnn t)
  have h2 : (∫ t, ρ t * (Counting_q η (t - E) + Counting_q η (t - E₂))) =
      (∫ t, ρ t * Counting_q η (t - E)) + ∫ t, ρ t * Counting_q η (t - E₂) := by
    simp_rw [mul_add]
    exact integral_add hq1 hq2
  linarith

/-- The density side of the smoothing: `∫ ρ q ≤ η + 2η (J + 1)` when `Im m ≤ 1`. -/
private lemma Counting_dens_q {ρ : ℝ → ℝ} (_hρ : Continuous ρ) (hint : Integrable ρ)
    (hnn : ∀ x, 0 ≤ ρ x) (hmass : ∫ t, ρ t = 1) {η : ℝ} (hη : 0 < η) (J : ℕ)
    (hJ : 1 ≤ 2 ^ J * η) (E' : ℝ)
    (hm : ∀ y : ℝ, 0 < y → ∫ t, ρ t * Counting_P y (t - E') ≤ 1) :
    ∫ t, ρ t * Counting_q η (t - E') ≤ η + 2 * η * (J + 1) := by
  have hint1 : ∀ g : ℝ → ℝ, Continuous g → (∃ c, ∀ t, |g t| ≤ c) → Integrable (fun t => ρ t * g t) := by
    intro g hg ⟨c, hc⟩
    exact hint.mul_bdd (c := c) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      simpa using hc t)
  have hPint : ∀ j : ℕ, Integrable (fun t => ρ t * Counting_P (2 ^ j * η) (t - E')) := by
    intro j
    have hy : 0 < 2 ^ j * η := by positivity
    refine hint1 _ ((Counting_P_cont hy).comp (continuous_id.sub continuous_const))
      ⟨1 / (2 ^ j * η), fun t => ?_⟩
    rw [abs_of_nonneg (Counting_P_nonneg hy _)]
    exact Counting_P_le hy _
  have hqint : Integrable (fun t => ρ t * Counting_q η (t - E')) :=
    hint1 (fun t => Counting_q η (t - E')) ((Counting_q_cont hη).comp (continuous_id.sub continuous_const))
      ⟨1 / 2, fun t => by
        rw [abs_of_nonneg (Counting_q_nonneg _ _)]; exact Counting_q_le_half hη _⟩
  have hsum : Integrable (fun t => ∑ j ∈ Finset.range (J + 1),
      ρ t * Counting_P (2 ^ j * η) (t - E')) := integrable_finsetSum _ fun j _ => hPint j
  have hrhs : Integrable (fun t => η * ρ t + 2 * η * ∑ j ∈ Finset.range (J + 1),
      ρ t * Counting_P (2 ^ j * η) (t - E')) := (hint.const_mul η).add (hsum.const_mul (2 * η))
  have hle : ∫ t, ρ t * Counting_q η (t - E') ≤ ∫ t, (η * ρ t + 2 * η * ∑ j ∈ Finset.range (J + 1),
      ρ t * Counting_P (2 ^ j * η) (t - E')) := by
    refine integral_mono hqint hrhs fun t => ?_
    have := Counting_q_le_ladder hη J hJ (t - E')
    have h2 := mul_le_mul_of_nonneg_left this (hnn t)
    calc ρ t * Counting_q η (t - E') ≤ ρ t * (η + 2 * η * ∑ j ∈ Finset.range (J + 1),
          Counting_P (2 ^ j * η) (t - E')) := h2
      _ = η * ρ t + 2 * η * ∑ j ∈ Finset.range (J + 1), ρ t * Counting_P (2 ^ j * η) (t - E') := by
          rw [← Finset.mul_sum]; ring
  refine hle.trans ?_
  rw [integral_add (hint.const_mul η) (hsum.const_mul (2 * η)), integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun j _ => hPint j, hmass]
  have : ∑ j ∈ Finset.range (J + 1), ∫ t, ρ t * Counting_P (2 ^ j * η) (t - E') ≤
      ∑ _j ∈ Finset.range (J + 1), (1 : ℝ) :=
    Finset.sum_le_sum fun j _ => hm _ (by positivity)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  have h3 : 2 * η * ∑ j ∈ Finset.range (J + 1), ∫ t, ρ t * Counting_P (2 ^ j * η) (t - E') ≤
      2 * η * ((J : ℝ) + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    push_cast at this; linarith
  linarith

end Dens

end P8b

section P8c

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
private lemma Counting_card_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
  have : 0 < Fintype.card ι := Fintype.card_pos
  exact_mod_cast this

/-- `Σ_k P_y(λ_k - x) = n Im⟨G(x + iy)⟩`. -/
private lemma Counting_sum_P (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (x y : ℝ) (hy : 0 < y) :
    ∑ k, Counting_P y (hX.eigenvalues k - x) =
      (Fintype.card ι : ℝ) * (ntr (res X ((x : ℂ) + (y : ℂ) * Complex.I))).im := by
  rw [Counting_im_ntr_res X hX x y hy, ← mul_assoc, mul_inv_cancel₀ Counting_card_pos.ne', one_mul]
  rfl

/-- `Im⟨G⟩ ≤ 2` at heights `y ≥ η`, from the averaged law and `|m| < 1`. -/
private lemma Counting_im_ntr_le (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {η : ℝ}
    (hLL : ∀ z : ℂ, |z.re| ≤ 4 → η ≤ z.im → z.im ≤ 1 → ‖ntr (res X z - MSol Λ z)‖ ≤ 1)
    (E' y : ℝ) (hE' : |E'| ≤ 4) (hy : η ≤ y) (hη : 0 < η) :
    (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I))).im ≤ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le hη hy
  have hz : 0 < ((E' : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy0
  by_cases h1 : y ≤ 1
  · have hl := hLL ((E' : ℂ) + (y : ℂ) * Complex.I) (by simpa using hE') (by simpa using hy)
      (by simpa using h1)
    obtain ⟨-, hmeq, -⟩ := mSol_spec Λ hΛ _ hz
    obtain ⟨-, hm1, -⟩ := mSol_apriori Λ hΛ hℓ _ hz
    have hsub : ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I) - MSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I)) =
        ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I)) - mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I) := by
      rw [hmeq]
      unfold ntr
      rw [Matrix.trace_sub, mul_sub]
    rw [hsub] at hl
    have h2 : (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I))).im =
        (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I)) - mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I)).im +
          (mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I)).im := by
      rw [Complex.sub_im]; ring
    rw [h2]
    have h3 := Complex.abs_im_le_norm
      (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I)) - mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I))
    have h4 := Complex.abs_im_le_norm (mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I))
    have h5 := le_abs_self (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I)) -
      mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I)).im
    have h6 := le_abs_self (mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I)).im
    linarith
  · rw [not_le] at h1
    have h2 := Counting_norm_ntr_le (res X ((E' : ℂ) + (y : ℂ) * Complex.I))
    have h3 := opNorm_res_le X hX _ hz
    have h4 := Complex.abs_im_le_norm (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I)))
    have h5 := le_abs_self (ntr (res X ((E' : ℂ) + (y : ℂ) * Complex.I))).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h3
    have h6 : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1.le
    linarith

/-- The spectral side of the smoothing: `Σ_k q(λ_k - E') ≤ nη + 4ηn(J + 1)`. -/
private lemma Counting_emp_q (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {η : ℝ} (hη : 0 < η) (J : ℕ) (hJ : 1 ≤ 2 ^ J * η)
    (hLL : ∀ z : ℂ, |z.re| ≤ 4 → η ≤ z.im → z.im ≤ 1 → ‖ntr (res X z - MSol Λ z)‖ ≤ 1)
    (E' : ℝ) (hE' : |E'| ≤ 4) :
    ∑ k, Counting_q η (hX.eigenvalues k - E') ≤
      (Fintype.card ι : ℝ) * η + 4 * η * (Fintype.card ι : ℝ) * (J + 1) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 < N := Counting_card_pos
  have h1 : ∑ k, Counting_q η (hX.eigenvalues k - E') ≤
      ∑ k, (η + 2 * η * ∑ j ∈ Finset.range (J + 1), Counting_P (2 ^ j * η) (hX.eigenvalues k - E')) :=
    Finset.sum_le_sum fun k _ => Counting_q_le_ladder hη J hJ _
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
    Finset.sum_comm]
  have h2 : ∀ j ∈ Finset.range (J + 1),
      ∑ k, Counting_P (2 ^ j * η) (hX.eigenvalues k - E') ≤ 2 * N := by
    intro j _
    have hy : 0 < 2 ^ j * η := by positivity
    rw [Counting_sum_P X hX E' _ hy]
    have := Counting_im_ntr_le Λ hΛ hℓ X hX hLL E' (2 ^ j * η) hE'
      (by nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)]) hη
    calc N * (ntr (res X ((E' : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I))).im ≤ N * 2 :=
          mul_le_mul_of_nonneg_left this hN0.le
      _ = 2 * N := by ring
  have h3 : ∑ j ∈ Finset.range (J + 1), ∑ k, Counting_P (2 ^ j * η) (hX.eigenvalues k - E') ≤
      ∑ _j ∈ Finset.range (J + 1), 2 * N := Finset.sum_le_sum h2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  have h4 : 2 * η * ∑ j ∈ Finset.range (J + 1), ∑ k, Counting_P (2 ^ j * η) (hX.eigenvalues k - E') ≤
      2 * η * (((J : ℝ) + 1) * (2 * N)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    push_cast at h3; linarith
  simp only [nsmul_eq_mul]
  nlinarith

omit [Nonempty ι] in
/-- The number of eigenvalues in `[E, E₂]` is the sum of the indicator over `ι`. -/
private lemma Counting_evCount_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (E E₂ : ℝ) :
    (evCount X E E₂ : ℝ) = ∑ k, (if hX.eigenvalues k ∈ Set.Icc E E₂ then (1 : ℝ) else 0) := by
  rw [Counting_sum_reindex X hX (fun l => if l ∈ Set.Icc E E₂ then (1 : ℝ) else 0)]
  unfold evCount eigs
  simp only [hX, ↓reduceDIte]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Set.mem_Icc]

omit [Nonempty ι] in
/-- The smoothing error of the count. -/
private lemma Counting_count_err (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {η E E₂ : ℝ} (hη : 0 < η)
    (hE : E ≤ E₂) :
    |(evCount X E E₂ : ℝ) - ∑ k, Counting_f η E E₂ (hX.eigenvalues k)| ≤
      (∑ k, Counting_q η (hX.eigenvalues k - E)) + ∑ k, Counting_q η (hX.eigenvalues k - E₂) := by
  rw [Counting_evCount_eq X hX, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  exact Counting_ind_le hη hE _

/-- The spectral side in terms of the integral of `Im⟨G⟩`. -/
private lemma Counting_sum_f (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {η : ℝ} (hη : 0 < η) (E E₂ : ℝ) :
    ∑ k, Counting_f η E E₂ (hX.eigenvalues k) =
      (Fintype.card ι : ℝ) / Real.pi *
        ∫ x in E..E₂, (ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I))).im := by
  rw [integral_im_ntr_res X hX E E₂ η hη]
  have hN := Counting_card_pos (ι := ι)
  unfold Counting_f
  rw [← Finset.sum_div]
  field_simp

omit [Nonempty ι] in
/-- `⟨G⟩` is analytic in the upper half plane. -/
private lemma Counting_diff_ntr (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    DifferentiableOn ℂ (fun z => ntr (res X z)) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  have : DifferentiableAt ℂ (fun z => ntr (res X z)) z := by
    have h1 : (fun z => ntr (res X z)) =
        fun z => ((Fintype.card ι : ℂ))⁻¹ * ∑ i, res X z i i := by
      funext z; rfl
    rw [h1]
    refine DifferentiableAt.const_mul ?_ _
    exact DifferentiableAt.fun_sum fun i _ => (hasDerivAt_res X hX z hz' i i).differentiableAt
  exact this.differentiableWithinAt

/-- `⟨G⟩ - m` is analytic in the upper half plane. -/
private lemma Counting_diff_F (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) :
    DifferentiableOn ℂ (fun z => ntr (res X z) - mSol Λ z) {z : ℂ | 0 < z.im} :=
  (Counting_diff_ntr X hX).sub (mSol_analyticOnNhd Λ hΛ).differentiableOn

end P8c

section P8d

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The Cauchy rectangle step: `|∫ Im(⟨G⟩ - m)(x + iη) dx| ≤ B (8 + 2 log(1/η))`. -/
private lemma Counting_cauchy (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (_hℓ : opNorm Λ ≤ 1 / 10)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {η E E₂ B : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hE : E ≤ E₂) (hE4 : |E| ≤ 4) (hE₂4 : |E₂| ≤ 4) (hw : E₂ - E ≤ 8) (hB : 0 ≤ B)
    (hlaw : ∀ z : ℂ, |z.re| ≤ 4 → η ≤ z.im → z.im ≤ 1 →
      ‖ntr (res X z - MSol Λ z)‖ ≤ B / z.im) :
    |(∫ x in E..E₂, (ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I))).im) -
      ∫ x in E..E₂, (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤
      B * (8 + 2 * -Real.log η) := by
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun z => ntr (res X z) - mSol Λ z := ⟨_, rfl⟩
  have hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := by
    rw [hF]; exact Counting_diff_F Λ hΛ X hX
  have hFc : ContinuousOn F {z : ℂ | 0 < z.im} := hFd.continuousOn
  have hFb : ∀ z : ℂ, |z.re| ≤ 4 → η ≤ z.im → z.im ≤ 1 → ‖F z‖ ≤ B / z.im := by
    intro z h1 h2 h3
    have hz : 0 < z.im := lt_of_lt_of_le hη h2
    have := hlaw z h1 h2 h3
    obtain ⟨-, hmeq, -⟩ := mSol_spec Λ hΛ _ hz
    have hsub : ntr (res X z - MSol Λ z) = F z := by
      rw [hF]; simp only [hmeq]
      unfold ntr
      rw [Matrix.trace_sub, mul_sub]
    rwa [hsub] at this
  -- continuity along horizontal and vertical segments
  have hcx : ∀ y : ℝ, 0 < y → Continuous fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro y hy
    refine hFc.comp_continuous (by fun_prop) fun x => ?_
    simpa using hy
  have hcy : ∀ x : ℝ, ContinuousOn (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
      (Set.uIcc η 1) := by
    intro x
    refine hFc.comp (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I).continuousOn
      fun y hy => ?_
    rw [Set.uIcc_of_le hη1] at hy
    simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    linarith [hy.1]
  -- the sides
  have hside : ∀ x : ℝ, |x| ≤ 4 →
      ‖∫ y in η..1, F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B * -Real.log η := by
    intro x hx
    have hint : IntervalIntegrable (fun y : ℝ => B / y) volume η 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div continuousOn_id fun y hy => ?_
      rw [Set.uIcc_of_le hη1] at hy
      exact (lt_of_lt_of_le hη hy.1).ne'
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hη1
      (f := fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) (g := fun y : ℝ => B / y)
      (Filter.Eventually.of_forall fun y hy => by
        have := hFb ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hx) (by simpa using hy.1.le)
          (by simpa using hy.2)
        simpa using this) hint
    refine h1.trans (le_of_eq ?_)
    have : ∫ y in η..1, B / y = B * ∫ y in η..1, y⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      simp only [div_eq_mul_inv]
    rw [this, integral_inv_of_pos hη one_pos, one_div, Real.log_inv]
  have htop : ‖∫ x in E..E₂, F ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ ≤ B * 8 := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => F ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)) (a := E) (b := E₂) (C := B)
      (fun x hx => by
        rw [Set.uIoc_of_le hE] at hx
        have := hFb ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)
          (by simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
              rw [abs_le] at hE4 hE₂4 ⊢
              constructor <;> linarith [hx.1, hx.2, hE4.1, hE₂4.2])
          (by simpa using hη1) (by simp)
        simpa using this)
    rw [abs_of_nonneg (by linarith)] at h1
    nlinarith
  have hd : DifferentiableOn ℂ F (Set.uIcc (⟨E, η⟩ : ℂ).re (⟨E₂, 1⟩ : ℂ).re ×ℂ
      Set.uIcc (⟨E, η⟩ : ℂ).im (⟨E₂, 1⟩ : ℂ).im) := by
    refine hFd.mono fun z hz => ?_
    rw [Complex.mem_reProdIm] at hz
    have := hz.2
    simp only [Set.uIcc_of_le hη1] at this
    simp only [Set.mem_ofPred_eq]
    exact lt_of_lt_of_le hη this.1
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F ⟨E, η⟩ ⟨E₂, 1⟩ hd
  simp only [smul_eq_mul] at hcauchy
  have hs1 := hside E hE4
  have hs2 := hside E₂ hE₂4
  have hT0 : (∫ x in E..E₂, F ((x : ℂ) + (η : ℂ) * Complex.I)) =
      (∫ x in E..E₂, F ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)) -
        Complex.I * (∫ y in η..1, F ((E₂ : ℂ) + (y : ℂ) * Complex.I)) +
        Complex.I * (∫ y in η..1, F ((E : ℂ) + (y : ℂ) * Complex.I)) := by
    linear_combination hcauchy
  have hnorm : ‖∫ x in E..E₂, F ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      B * (8 + 2 * -Real.log η) := by
    generalize (∫ x in E..E₂, F ((x : ℂ) + (η : ℂ) * Complex.I)) = T0 at hT0 ⊢
    generalize (∫ x in E..E₂, F ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)) = T1 at hT0 htop
    generalize (∫ y in η..1, F ((E₂ : ℂ) + (y : ℂ) * Complex.I)) = S2 at hT0 hs2
    generalize (∫ y in η..1, F ((E : ℂ) + (y : ℂ) * Complex.I)) = S1 at hT0 hs1
    have h1 : ‖Complex.I * S2‖ ≤ B * -Real.log η := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact hs2
    have h2 : ‖Complex.I * S1‖ ≤ B * -Real.log η := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact hs1
    have n1 : ‖T1 - Complex.I * S2 + Complex.I * S1‖ ≤
        ‖T1 - Complex.I * S2‖ + ‖Complex.I * S1‖ := norm_add_le _ _
    have n2 : ‖T1 - Complex.I * S2‖ ≤ ‖T1‖ + ‖Complex.I * S2‖ := norm_sub_le _ _
    rw [hT0]
    linarith
  -- take the imaginary part
  have hc1 : Continuous fun x : ℝ => ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I)) :=
    (Counting_diff_ntr X hX).continuousOn.comp_continuous (by fun_prop) fun x => by simpa using hη
  have hc2 : Continuous fun x : ℝ => mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I) :=
    (mSol_analyticOnNhd Λ hΛ).continuousOn.comp_continuous (by fun_prop) fun x => by simpa using hη
  have hcF : Continuous fun x : ℝ => F ((x : ℂ) + (η : ℂ) * Complex.I) := hcx η hη
  have e1 : (∫ x in E..E₂, (ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I))).im) -
      (∫ x in E..E₂, (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im) =
      (∫ x in E..E₂, F ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
    have h1 := Complex.imCLM.intervalIntegral_comp_comm (a := E) (b := E₂) (μ := volume)
      (hcF.intervalIntegrable E E₂)
    simp only [Complex.imCLM_apply] at h1
    have hi1 : IntervalIntegrable (fun x : ℝ => (ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I))).im)
        volume E E₂ := (Complex.continuous_im.comp hc1).intervalIntegrable E E₂
    have hi2 : IntervalIntegrable (fun x : ℝ => (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im)
        volume E E₂ := (Complex.continuous_im.comp hc2).intervalIntegrable E E₂
    rw [← h1, ← intervalIntegral.integral_sub hi1 hi2]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hF, Complex.sub_im]
  rw [e1]
  exact (Complex.abs_im_le_norm _).trans hnorm

end P8d

section P8e

/-- The dyadic ladder: `2^J η ≥ 1` and `J ≤ 2 log N + 1`. -/
private lemma Counting_ladder_J {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    ∃ J : ℕ, 1 ≤ 2 ^ J * (n : ℝ) ^ (-1 + s) ∧ (J : ℝ) ≤ 2 * Real.log n + 1 := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hN0 : (0 : ℝ) < n := by linarith
  refine ⟨Nat.clog 2 n, ?_, ?_⟩
  · have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
    have h2 : (n : ℝ) ≤ 2 ^ Nat.clog 2 n := by exact_mod_cast h1
    have h3 : (n : ℝ) * (n : ℝ) ^ (-1 + s) = (n : ℝ) ^ s := by
      calc (n : ℝ) * (n : ℝ) ^ (-1 + s) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-1 + s) := by
            rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((1 : ℝ) + (-1 + s)) := (Real.rpow_add hN0 _ _).symm
        _ = (n : ℝ) ^ s := by ring_nf
    have h4 : (1 : ℝ) ≤ (n : ℝ) ^ s := Real.one_le_rpow hN1 hs.le
    have h5 : 0 < (n : ℝ) ^ (-1 + s) := by positivity
    calc (1 : ℝ) ≤ (n : ℝ) ^ s := h4
      _ = (n : ℝ) * (n : ℝ) ^ (-1 + s) := h3.symm
      _ ≤ 2 ^ Nat.clog 2 n * (n : ℝ) ^ (-1 + s) := mul_le_mul_of_nonneg_right h2 h5.le
  · have hlt : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    have hlt' : (2 : ℝ) ^ (Nat.clog 2 n).pred < n := by exact_mod_cast hlt
    have h1 := Real.log_lt_log (by positivity) hlt'
    rw [Real.log_pow] at h1
    have hl2 := Real.log_two_gt_d9
    rcases Nat.eq_zero_or_pos (Nat.clog 2 n) with h0 | hpos
    · rw [h0]; simp
      have : 0 ≤ Real.log n := Real.log_nonneg hN1
      linarith
    · have h2 : ((Nat.clog 2 n).pred : ℝ) = (Nat.clog 2 n : ℝ) - 1 := by
        rw [Nat.pred_eq_sub_one, Nat.cast_sub hpos]; simp
      rw [h2] at h1
      have h3 : 0 ≤ (Nat.clog 2 n : ℝ) - 1 := by
        have : (1 : ℝ) ≤ Nat.clog 2 n := by exact_mod_cast hpos
        linarith
      nlinarith

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

set_option maxHeartbeats 1000000 in
/-- The count of eigenvalues in `[E, E⁺ + 1]` against `n ∫_E^{E⁺+1} ρ_N`, with the explicit
bound `n^s (31 + 25 log n)`. -/
private lemma Counting_count_main (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 5)
    (hN2 : 2 ≤ Fintype.card ι)
    (hLL : ∀ z : ℂ, |z.re| ≤ 4 → (Fintype.card ι : ℝ) ^ (-1 + s) ≤ z.im → z.im ≤ 1 →
      ‖ntr (res X z - MSol Λ z)‖ ≤
        (Fintype.card ι : ℝ) ^ s / ((Fintype.card ι : ℝ) * z.im))
    {E : ℝ} (hE1 : Eminus Λ - 1 ≤ E) (hE2 : E ≤ Eplus Λ + 1) :
    |(evCount X E (Eplus Λ + 1) : ℝ) -
        (Fintype.card ι : ℝ) * ∫ x in E..(Eplus Λ + 1), rho Λ x| ≤
      (Fintype.card ι : ℝ) ^ s * (31 + 25 * Real.log (Fintype.card ι : ℝ)) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNn : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN2
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set η : ℝ := N ^ (-1 + s) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hNη : N * η = N ^ s := by
    calc N * N ^ (-1 + s) = N ^ (1 : ℝ) * N ^ (-1 + s) := by rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + (-1 + s)) := (Real.rpow_add hN0 _ _).symm
      _ = N ^ s := by ring_nf
  have hS0 : 0 < N ^ s := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  -- the averaged law in two forms
  have hLL1 : ∀ z : ℂ, |z.re| ≤ 4 → η ≤ z.im → z.im ≤ 1 → ‖ntr (res X z - MSol Λ z)‖ ≤ 1 := by
    intro z h1 h2 h3
    refine (hLL z h1 h2 h3).trans ?_
    have hy : 0 < z.im := lt_of_lt_of_le hη0 h2
    rw [div_le_one (by positivity)]
    calc N ^ s = N * η := hNη.symm
      _ ≤ N * z.im := mul_le_mul_of_nonneg_left h2 hN0.le
  have hlaw : ∀ z : ℂ, |z.re| ≤ 4 → η ≤ z.im → z.im ≤ 1 →
      ‖ntr (res X z - MSol Λ z)‖ ≤ (N ^ s / N) / z.im := by
    intro z h1 h2 h3
    have := hLL z h1 h2 h3
    rwa [div_div]
  -- the region
  obtain ⟨ha, hb⟩ := Counting_edge_bound Λ hΛ hℓ
  have hEE : E ≤ Eplus Λ + 1 := hE2
  have hE4 : |E| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hE₂4 : |Eplus Λ + 1| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hwid : Eplus Λ + 1 - E ≤ 8 := by linarith
  obtain ⟨J, hJ, hJle⟩ := Counting_ladder_J hN2 hs
  have hJ' : 1 ≤ 2 ^ J * η := hJ
  -- (i) the count against the smoothed count
  have hcnt := Counting_count_err X hX hη0 hEE
  have hq1 := Counting_emp_q Λ hΛ hℓ X hX hη0 J hJ' hLL1 E hE4
  have hq2 := Counting_emp_q Λ hΛ hℓ X hX hη0 J hJ' hLL1 (Eplus Λ + 1) hE₂4
  -- (ii) the smoothed count against `Im m`
  have hsumf := Counting_sum_f X hX hη0 E (Eplus Λ + 1)
  have hcau := Counting_cauchy Λ hΛ hℓ X hX hη0 hη1 hEE hE4 hE₂4 hwid (B := N ^ s / N)
    (by positivity) hlaw
  -- (iii) `Im m` against the density
  obtain ⟨hnn, hcont, hint, hmass, -⟩ := rho_stieltjes Λ hΛ hℓ
  have himm : ∫ x in E..(Eplus Λ + 1), (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im =
      ∫ t, rho Λ t * (Real.arctan ((Eplus Λ + 1 - t) / η) - Real.arctan ((E - t) / η)) := by
    rw [← Counting_fubini hcont hint hη0 hEE]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact Counting_im_mSol Λ hΛ hℓ x η hη0
  have hmle : ∀ E' y : ℝ, 0 < y → ∫ t, rho Λ t * Counting_P y (t - E') ≤ 1 := by
    intro E' y hy
    rw [← Counting_im_mSol Λ hΛ hℓ E' y hy]
    have hz : 0 < ((E' : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    have h1 := (mSol_apriori Λ hΛ hℓ _ hz).2.1
    have h2 := Complex.abs_im_le_norm (mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I))
    have h3 := le_abs_self (mSol Λ ((E' : ℂ) + (y : ℂ) * Complex.I)).im
    linarith
  have hd1 := Counting_dens_q hcont hint hnn hmass hη0 J hJ' E (hmle E)
  have hd2 := Counting_dens_q hcont hint hnn hmass hη0 J hJ' (Eplus Λ + 1) (hmle _)
  have hderr := Counting_dens_err hcont hint hnn hη0 hEE hd1 hd2
  have hIcc : ∫ t in Set.Icc E (Eplus Λ + 1), rho Λ t = ∫ x in E..(Eplus Λ + 1), rho Λ x := by
    rw [intervalIntegral.integral_of_le hEE, integral_Icc_eq_integral_Ioc]
  rw [← himm, hIcc] at hderr
  have hπ3 : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hπ0 : 0 < Real.pi := Real.pi_pos
  -- the logarithm of `η`
  have hL : -Real.log η = (1 - s) * Real.log N := by
    rw [hη, Real.log_rpow hN0]; ring
  have hL' : -Real.log η ≤ Real.log N := by
    rw [hL]; nlinarith
  have hL0 : 0 ≤ -Real.log η := by rw [hL]; nlinarith
  -- abbreviations
  generalize (evCount X E (Eplus Λ + 1) : ℝ) = C at *
  generalize (∑ k, Counting_f η E (Eplus Λ + 1) (hX.eigenvalues k)) = Sf at *
  generalize (∑ k, Counting_q η (hX.eigenvalues k - E)) = Q1 at *
  generalize (∑ k, Counting_q η (hX.eigenvalues k - (Eplus Λ + 1))) = Q2 at *
  generalize (∫ x in E..(Eplus Λ + 1), (ntr (res X ((x : ℂ) + (η : ℂ) * Complex.I))).im) = Im1 at *
  generalize (∫ x in E..(Eplus Λ + 1), (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im) = Im2 at *
  generalize (∫ x in E..(Eplus Λ + 1), rho Λ x) = Iρ at *
  generalize N ^ s = S at *
  have hSN : N * η = S := hNη
  have e : C - N * Iρ = (C - Sf) + (N / Real.pi) * (Im1 - Im2) +
      (N / Real.pi) * (Im2 - Real.pi * Iρ) := by
    rw [hsumf]; field_simp; ring
  have t1 : |C - Sf| ≤ 2 * S * (1 + 4 * (J + 1)) := by
    refine hcnt.trans ?_
    have : Q1 + Q2 ≤ 2 * (N * η + 4 * η * N * (J + 1)) := by linarith
    refine this.trans (le_of_eq ?_)
    rw [← hSN]; ring
  have t2 : |(N / Real.pi) * (Im1 - Im2)| ≤ S * (8 + 2 * Real.log N) / 3 := by
    rw [abs_mul, abs_of_pos (div_pos hN0 hπ0)]
    have h1 : (N / Real.pi) * |Im1 - Im2| ≤ (N / Real.pi) * ((S / N) * (8 + 2 * -Real.log η)) :=
      mul_le_mul_of_nonneg_left hcau (div_pos hN0 hπ0).le
    refine h1.trans ?_
    have h2 : (N / Real.pi) * ((S / N) * (8 + 2 * -Real.log η)) = S * (8 + 2 * -Real.log η) / Real.pi := by
      field_simp
    rw [h2]
    have hpos : 0 ≤ S * (8 + 2 * -Real.log η) := by positivity
    calc S * (8 + 2 * -Real.log η) / Real.pi ≤ S * (8 + 2 * -Real.log η) / 3 :=
          div_le_div_of_nonneg_left hpos (by norm_num) hπ3
      _ ≤ S * (8 + 2 * Real.log N) / 3 := by
          have : S * (8 + 2 * -Real.log η) ≤ S * (8 + 2 * Real.log N) :=
            mul_le_mul_of_nonneg_left (by linarith) hS0.le
          linarith
  have t3 : |(N / Real.pi) * (Im2 - Real.pi * Iρ)| ≤ 2 * S * (2 * J + 3) := by
    rw [abs_mul, abs_of_pos (div_pos hN0 hπ0)]
    have h1 : (N / Real.pi) * |Im2 - Real.pi * Iρ| ≤
        (N / Real.pi) * (Real.pi * (2 * (η + 2 * η * (J + 1)))) :=
      mul_le_mul_of_nonneg_left hderr (div_pos hN0 hπ0).le
    refine h1.trans (le_of_eq ?_)
    field_simp
    rw [← hSN]; ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  have hJ2 : S * (J : ℝ) ≤ S * (2 * Real.log N + 1) := mul_le_mul_of_nonneg_left hJle hS0.le
  have hlogS : 0 ≤ S * Real.log N := by positivity
  nlinarith

end Main

/-- `31 + 25 log x ≤ x^s` for large `x`. -/
private lemma Counting_ev_log {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ 31 + 25 * Real.log x ≤ x ^ s := by
  have e1 : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have e2 : ∀ᶠ x : ℝ in atTop, 31 + 50 / s ≤ x ^ (s / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < s / 2)).eventually_ge_atTop (31 + 50 / s)
  filter_upwards [e1, e2] with x h1 h2
  refine ⟨h1, ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_le_rpow_div hx0.le (by positivity : 0 < s / 2)
  set t : ℝ := x ^ (s / 2) with ht
  have ht1 : 1 ≤ t := by
    have : 0 ≤ 50 / s := by positivity
    linarith
  have hts : t * t = x ^ s := by
    rw [ht, ← Real.rpow_add hx0]; ring_nf
  rw [← hts]
  have h3 : 25 * Real.log x ≤ 25 * (t / (s / 2)) := by linarith
  have h4 : 25 * (t / (s / 2)) = (50 / s) * t := by field_simp; ring
  have h5 : 0 ≤ 50 / s := by positivity
  nlinarith

end P8e

/-- Counting from the averaged law (deterministic): for `0 < s ≤ 1/5` and `n = card ι ≥ n₀(s)`,
Hermitian `Λ` with `‖Λ‖ ≤ 1/10` and Hermitian `X` with
`|⟨G(z) - M(z)⟩| ≤ n^s/(n Im z)` on `{|Re z| ≤ 4, n^{-1+s} ≤ Im z ≤ 1}`, the number of
eigenvalues of `X` in `[E, E⁺ + 1]` differs from `n ∫_E^{E⁺+1} ρ_N` by at most `n^{2s}`, for every
`E ∈ [E⁻ - 1, E⁺ + 1]`. -/
theorem count_of_aver (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1 / 5) :
    ∃ n₀ : ℕ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι], n₀ ≤ Fintype.card ι →
      ∀ Λ : Matrix ι ι ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ X : Matrix ι ι ℂ, X.IsHermitian →
      (∀ z : ℂ, |z.re| ≤ 4 → (Fintype.card ι : ℝ) ^ (-1 + s) ≤ z.im → z.im ≤ 1 →
        ‖ntr (res X z - MSol Λ z)‖ ≤
          (Fintype.card ι : ℝ) ^ s / ((Fintype.card ι : ℝ) * z.im)) →
      ∀ E : ℝ, Eminus Λ - 1 ≤ E → E ≤ Eplus Λ + 1 →
        |(evCount X E (Eplus Λ + 1) : ℝ) -
            (Fintype.card ι : ℝ) * ∫ x in E..(Eplus Λ + 1), rho Λ x| ≤
          (Fintype.card ι : ℝ) ^ (2 * s) := by
  obtain ⟨n₀, hn₀⟩ := Counting_eventually_nat (Counting_ev_log hs)
  refine ⟨max n₀ 2, fun ι _ _ _ hn Λ hΛ hℓ X hX hLL E hE1 hE2 => ?_⟩
  have hn' : n₀ ≤ Fintype.card ι := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ Fintype.card ι := le_trans (le_max_right _ _) hn
  obtain ⟨-, hlog⟩ := hn₀ (Fintype.card ι) hn'
  have hmain := Counting_count_main Λ hΛ hℓ X hX hs hs1 hn2 hLL hE1 hE2
  refine hmain.trans ?_
  have hN0 : (0 : ℝ) < Fintype.card ι := by
    have : 0 < Fintype.card ι := by omega
    exact_mod_cast this
  have h2s : (Fintype.card ι : ℝ) ^ (2 * s) = (Fintype.card ι : ℝ) ^ s * (Fintype.card ι : ℝ) ^ s := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [h2s]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

end RBMTransitionEdge

end
