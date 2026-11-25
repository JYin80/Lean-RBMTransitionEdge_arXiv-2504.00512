module

public import RBMTransitionEdge.Edge.Defs
public import RBMTransitionEdge.LocalLaw.Wigner

@[expose] public section

/-!
# The smoothing lemma of Lemma 4.2

The eigenvalue count above `E`, the edge count `A` as a sum of arctangents, the sandwich of the
count by the smoothed count ([Erds2017ADA, Lemma 17.2, Corollary 17.3] for `H_t`), and the
layer-cake identity for `n` eigenvalues (proof of Lemma 4.2 [CVtV] from Lemma 4.3).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `𝒩(E, ∞)`: the number of eigenvalues of `X` in `[E, ∞)`. -/
def eigCountAbove {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (E : ℝ) : ℕ :=
  ((Finset.Icc 1 (Fintype.card ι)).filter fun k => E ≤ eigK X k).card


/-- `Σ_i |v_k(i)|² = 1` for the columns of the eigenvector unitary. -/
private lemma Smoothing_col_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (k : ι) :
    ∑ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) = 1 := by
  have h := hX.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]
  rfl

/-- The trace of the resolvent of a Hermitian matrix: `Tr (X - z)⁻¹ = Σ_k (λ_k - z)⁻¹`. -/
private lemma Smoothing_trace_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (res X z).trace = ∑ k, 1 / ((hX.eigenvalues k : ℂ) - z) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, res_eq_sum_eig X hX z hz]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_div]
  congr 1
  have := Smoothing_col_norm hX k
  have h2 : ∑ i, (hX.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      starRingEnd ℂ ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) =
      ((∑ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj]
  rw [h2, this]
  simp

/-- A sum over the eigenvalues indexed by `ι` is the sum of `eigK X k`, `k ∈ ⟦1, card ι⟧`. -/
private lemma Smoothing_sum_eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (F : ℝ → ℝ) :
    ∑ k, F (hX.eigenvalues k) = ∑ j ∈ Finset.Icc 1 (Fintype.card ι), F (eigK X j) := by
  have e1 : ∑ k, F (hX.eigenvalues k) = ∑ j : Fin (Fintype.card ι), F (hX.eigenvalues₀ j) := by
    refine Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ fun k => ?_
    simp [Matrix.IsHermitian.eigenvalues]
  rw [e1]
  symm
  refine Finset.sum_bij (fun j hj => (⟨j - 1, by
      have := Finset.mem_Icc.mp hj; omega⟩ : Fin (Fintype.card ι))) (fun _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro a ha b hb h
    have h1 := Finset.mem_Icc.mp ha
    have h2 := Finset.mem_Icc.mp hb
    have := congrArg Fin.val h
    simp only at this
    omega
  · intro b _
    exact ⟨(b : ℕ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Fin.ext (by simp)⟩
  · intro a ha
    have h1 := Finset.mem_Icc.mp ha
    have h2 : a - 1 < Fintype.card ι := by omega
    simp [eigK, eigs, hX, h2]

/-- The imaginary part of `⟨(X - y - iη)⁻¹⟩` for Hermitian `X`, `η > 0`: the Poisson smoothing
`n⁻¹ Σ_k η / ((λ_k - y)² + η²)`. -/
private lemma Smoothing_im_ntr_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (y η : ℝ) (hη : 0 < η) :
    (ntr (res X ((y : ℂ) + (η : ℂ) * Complex.I))).im =
      ((Fintype.card ι : ℝ))⁻¹ *
        ∑ k ∈ Finset.Icc 1 (Fintype.card ι), η / ((eigK X k - y) ^ 2 + η ^ 2) := by
  have hz : 0 < ((y : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  unfold ntr
  rw [show ((Fintype.card ι : ℂ))⁻¹ = ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.im_ofReal_mul, Smoothing_trace_res X hX _ hz, Complex.im_sum]
  congr 1
  rw [Smoothing_sum_eigK X hX (fun l => (1 / ((l : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))).im)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- `∫_{E₁}^{E₂} η / ((λ - y)² + η²) dy = arctan((E₂ - λ)/η) - arctan((E₁ - λ)/η)` for `η > 0`
(the Poisson kernel `θ_η` integrated in closed form). -/
private lemma Smoothing_integral_poisson (η lam E₁ E₂ : ℝ) (hη : 0 < η) :
    ∫ y in E₁..E₂, η / ((lam - y) ^ 2 + η ^ 2) =
      Real.arctan ((E₂ - lam) / η) - Real.arctan ((E₁ - lam) / η) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => Real.arctan ((y - lam) / η))
      (η / ((lam - y) ^ 2 + η ^ 2)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y - lam) / η) (1 / η) y :=
      ((hasDerivAt_id y).sub_const lam).div_const η
    have h2 := (Real.hasDerivAt_arctan ((y - lam) / η)).comp y h1
    refine h2.congr_deriv ?_
    have : (lam - y) ^ 2 + η ^ 2 = η ^ 2 * (1 + ((y - lam) / η) ^ 2) := by
      field_simp
      ring
    rw [this]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  · refine Continuous.intervalIntegrable ?_ _ _
    have hc : Continuous (fun y : ℝ => (lam - y) ^ 2 + η ^ 2) := by fun_prop
    exact continuous_const.div hc fun y =>
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hη 2)).ne'

/-- `A = Σ_k (arctan((E₂ - λ_k)/η) - arctan((E₁ - λ_k)/η))` for a Hermitian array and `η > 0`:
the argument of `F` in (4.7) [2comVVt] is `π` times `Tr χ_{[E₁, E₂]} ⋆ θ_η`. -/
theorem edgeCount_eq_arctan (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    edgeCount D N A η E₁ E₂ h = ∑ k ∈ Finset.Icc 1 (D * N),
      (Real.arctan ((E₂ - eigK (Matrix.of h + lam D N A) k) / η) -
        Real.arctan ((E₁ - eigK (Matrix.of h + lam D N A) k) / η)) := by
  have hX : (Matrix.of h + lam D N A).IsHermitian := hh.add (lam_isHermitian D N A)
  have hc : Fintype.card (Idx D N) = D * N := by simp
  unfold edgeCount
  simp only [Smoothing_im_ntr_res _ hX _ η hη, hc]
  rw [intervalIntegral.integral_const_mul]
  rcases Nat.eq_zero_or_pos (D * N) with h0 | h0
  · rw [h0]
    simp
  have hint : ∀ k ∈ Finset.Icc 1 (D * N), IntervalIntegrable
      (fun x : ℝ => η / ((eigK (Matrix.of h + lam D N A) k - x) ^ 2 + η ^ 2)) volume E₁ E₂ := by
    intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    have hc : Continuous (fun y : ℝ => (eigK (Matrix.of h + lam D N A) k - y) ^ 2 + η ^ 2) := by
      fun_prop
    exact continuous_const.div hc fun y =>
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hη 2)).ne'
  rw [intervalIntegral.integral_finsetSum hint]
  simp only [Smoothing_integral_poisson _ _ _ _ hη]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast h0.ne'), one_mul]

/-- `arctan y ≤ y` for `y ≥ 0`. -/
private lemma Smoothing_arctan_le {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  have h := Real.le_tan (Real.arctan_nonneg.mpr hy) (Real.arctan_lt_pi_div_two y)
  rwa [Real.tan_arctan] at h

/-- `π/2 - 1/y ≤ arctan y` for `y > 0`. -/
private lemma Smoothing_arctan_ge {y : ℝ} (hy : 0 < y) : Real.pi / 2 - y⁻¹ ≤ Real.arctan y := by
  have h := Real.arctan_inv_of_pos hy
  have := Smoothing_arctan_le (inv_nonneg.mpr hy.le)
  linarith

/-- `arctan(a/η) - arctan(b/η) ≥ π - η/a - η/(-b)` for `a > 0 > b`, `η > 0`. -/
private lemma Smoothing_arctan_diff_ge {a b η : ℝ} (hη : 0 < η) (ha : 0 < a) (hb : b < 0) :
    Real.pi - η / a - η / (-b) ≤ Real.arctan (a / η) - Real.arctan (b / η) := by
  have h1 := Smoothing_arctan_ge (div_pos ha hη)
  have h2 := Smoothing_arctan_ge (div_pos (neg_pos.mpr hb) hη)
  rw [show b / η = -(-b / η) by ring, Real.arctan_neg]
  rw [inv_div] at h1 h2
  linarith

/-- `arctan(a/η) - arctan(b/η) ≤ η/b` for `b > 0`, `η > 0`. -/
private lemma Smoothing_arctan_diff_le {a b η : ℝ} (hη : 0 < η) (hb : 0 < b) :
    Real.arctan (a / η) - Real.arctan (b / η) ≤ η / b := by
  have h1 := Real.arctan_lt_pi_div_two (a / η)
  have h2 := Smoothing_arctan_ge (div_pos hb hη)
  rw [inv_div] at h2
  linarith

/-- `arctan(a/η) - arctan(b/η) ≤ η m / b²` for `b > 0`, `a - b ≤ m`, `0 ≤ m`, `η > 0`. -/
private lemma Smoothing_arctan_diff_le' {a b m η : ℝ} (hη : 0 < η) (hb : 0 < b) (hm0 : 0 ≤ m)
    (hm : a - b ≤ m) :
    Real.arctan (a / η) - Real.arctan (b / η) ≤ η * m / b ^ 2 := by
  by_cases hab : a ≤ b
  · have : Real.arctan (a / η) ≤ Real.arctan (b / η) :=
      Real.arctan_mono (div_le_div_of_nonneg_right hab hη.le)
    have h0 : 0 ≤ η * m / b ^ 2 := by positivity
    linarith
  · have hab := not_le.mp hab
    set u := a / η with hu
    set v := b / η with hv
    have hv0 : 0 < v := div_pos hb hη
    have huv : v < u := div_lt_div_of_pos_right hab hη
    have hprod : u * (-v) < 1 := by nlinarith
    have h1 : Real.arctan u - Real.arctan v = Real.arctan ((u - v) / (1 + u * v)) := by
      have h := Real.arctan_add hprod
      rw [Real.arctan_neg] at h
      rw [sub_eq_add_neg, h]
      congr 1
      ring
    rw [h1]
    refine (Smoothing_arctan_le (by apply div_nonneg <;> nlinarith)).trans ?_
    have h2 : (u - v) / (1 + u * v) ≤ (u - v) / v ^ 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    refine h2.trans ?_
    have e1 : (u - v) = (a - b) / η := by rw [hu, hv]; ring
    rw [e1, hv]
    have : (a - b) / η / (b / η) ^ 2 = η * (a - b) / b ^ 2 := by
      field_simp
    rw [this]
    have hb2 : 0 < b ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hb2]
    nlinarith

/-- A power of `s ≥ 1` dominates a smaller power. -/
private lemma Smoothing_pow_le {s : ℝ} (hs : 1 ≤ s) {a b : ℕ} (h : a ≤ b) : s ^ a ≤ s ^ b :=
  pow_le_pow_right₀ hs h

/-- The lower bound of a term near the edge: for `E ≤ λ ≤ E⁺ + N^{-2/3+ε'/2}`, the `k`-th term of
`A(E - ℓ, E₊)` is at least `π - 4 s^{-16}` (`s = N^{ε'/2}`, `r = N^{-2/3}`). -/
private lemma Smoothing_G_ge {r s η ℓ E Ep x : ℝ} (hr : 0 < r) (hs : 2 ≤ s)
    (hη : η = r / s ^ 18) (hℓ : ℓ = r / s ^ 2 / 2)
    (hx1 : E ≤ x) (hx2 : x ≤ Ep + r * s) :
    Real.pi - 4 / s ^ 16 ≤
      Real.arctan ((Ep + r * s ^ 2 - x) / η) - Real.arctan ((E - ℓ - x) / η) := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  have ha : r * s ^ 2 / 2 ≤ Ep + r * s ^ 2 - x := by
    have : r * s ≤ r * s ^ 2 / 2 := by nlinarith [mul_pos hr hs0]
    linarith
  have ha0 : 0 < Ep + r * s ^ 2 - x := lt_of_lt_of_le (by positivity) ha
  have hb : E - ℓ - x ≤ -ℓ := by linarith
  have hb0 : E - ℓ - x < 0 := by linarith
  have h1 := Smoothing_arctan_diff_ge hη0 ha0 hb0
  have e1 : η / (Ep + r * s ^ 2 - x) ≤ 2 / s ^ 16 := by
    calc η / (Ep + r * s ^ 2 - x) ≤ η / (r * s ^ 2 / 2) :=
          div_le_div_of_nonneg_left hη0.le (by positivity) ha
      _ = 2 / s ^ 20 := by rw [hη]; field_simp
      _ ≤ 2 / s ^ 16 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact Smoothing_pow_le hs1 (by norm_num)
  have e2 : η / (-(E - ℓ - x)) ≤ 2 / s ^ 16 := by
    calc η / (-(E - ℓ - x)) ≤ η / ℓ :=
          div_le_div_of_nonneg_left hη0.le hℓ0 (by linarith)
      _ = 2 / s ^ 16 := by rw [hη, hℓ]; field_simp
  have : 4 / s ^ 16 = 2 / s ^ 16 + 2 / s ^ 16 := by ring
  linarith

/-- Every eigenvalue index `k ∈ ⟦1, n⟧` with `E ≤ λ_k` is below the threshold `k₁`, and so there are
at most `k₁` of them. -/
private lemma Smoothing_count_le (n : ℕ) (lam : ℕ → ℝ) (E r c : ℝ) (k₁ : ℕ) (hr : 0 < r)
    (hc : 0 < c)
    (hgap : ∀ k ∈ Finset.Icc 1 n, k₁ ≤ k →
      3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) ≤ E - lam k) :
    (∀ k ∈ Finset.Icc 1 n, E ≤ lam k → k < k₁) ∧
      (((Finset.Icc 1 n).filter fun k => E ≤ lam k).card : ℝ) ≤ k₁ := by
  have hlt : ∀ k ∈ Finset.Icc 1 n, E ≤ lam k → k < k₁ := by
    intro k hk hEk
    by_contra hcon
    have h1 := hgap k hk (not_lt.mp hcon)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have : 0 < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have : 0 < 3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) := by positivity
    linarith
  refine ⟨hlt, ?_⟩
  have hsub : (Finset.Icc 1 n).filter (fun k => E ≤ lam k) ⊆ Finset.range k₁ := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Finset.mem_range.mpr (hlt k hk.1 hk.2)
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact_mod_cast this

/-- The upper half of the sandwich: `𝒩(E, ∞) ≤ A(E - ℓ, E₊)/π + N^{-ε'}`, on the deterministic
event, with `r = N^{-2/3}`, `s = N^{ε'/2}`. -/
private lemma Smoothing_upper (n : ℕ) (lam : ℕ → ℝ) (Ep E r s c K η ℓ : ℝ) (k₁ : ℕ)
    (hr : 0 < r) (hs : 2 ≤ s) (hc : 0 < c)
    (hη : η = r / s ^ 18) (hℓ : ℓ = r / s ^ 2 / 2)
    (hlarge : 2 * K + 2 ≤ s)
    (hk₁ : (k₁ : ℝ) ≤ K * s ^ 3)
    (hS : ∀ k ∈ Finset.Icc 1 n, lam k ≤ Ep + r * s)
    (hgap : ∀ k ∈ Finset.Icc 1 n, k₁ ≤ k →
      3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) ≤ E - lam k)
    (hE1 : E ≤ Ep + r * s ^ 2) :
    (((Finset.Icc 1 n).filter fun k => E ≤ lam k).card : ℝ) ≤
        (∑ k ∈ Finset.Icc 1 n, (Real.arctan ((Ep + r * s ^ 2 - lam k) / η) -
          Real.arctan ((E - ℓ - lam k) / η))) / Real.pi + (s ^ 2)⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  obtain ⟨hlt, hcnt⟩ := Smoothing_count_le n lam E r c k₁ hr hc hgap
  set cnt : ℝ := (((Finset.Icc 1 n).filter fun k => E ≤ lam k).card : ℝ) with hcntdef
  have hG : ∀ k ∈ Finset.Icc 1 n, (if E ≤ lam k then Real.pi - 4 / s ^ 16 else 0) ≤
      Real.arctan ((Ep + r * s ^ 2 - lam k) / η) - Real.arctan ((E - ℓ - lam k) / η) := by
    intro k hk
    split_ifs with hEk
    · exact Smoothing_G_ge hr hs hη hℓ hEk (hS k hk)
    · have : Real.arctan ((E - ℓ - lam k) / η) ≤ Real.arctan ((Ep + r * s ^ 2 - lam k) / η) :=
        Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hη0.le)
      linarith
  have hsum := Finset.sum_le_sum hG
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hs16 : 0 < s ^ 16 := by positivity
  have h1 : cnt * Real.pi ≤ (∑ k ∈ Finset.Icc 1 n, (Real.arctan ((Ep + r * s ^ 2 - lam k) / η) -
          Real.arctan ((E - ℓ - lam k) / η))) + 4 * K * s ^ 3 / s ^ 16 := by
    have h2 : cnt * (4 / s ^ 16) ≤ K * s ^ 3 * (4 / s ^ 16) :=
      mul_le_mul_of_nonneg_right (hcnt.trans hk₁) (by positivity)
    have : K * s ^ 3 * (4 / s ^ 16) = 4 * K * s ^ 3 / s ^ 16 := by ring
    nlinarith
  have h3 : 4 * K * s ^ 3 / s ^ 16 ≤ Real.pi / s ^ 2 := by
    rw [div_le_div_iff₀ hs16 (by positivity)]
    have h11 : s ≤ s ^ 11 := by simpa using Smoothing_pow_le hs1 (show 1 ≤ 11 by norm_num)
    have hK2 : 4 * K ≤ 2 * s := by linarith
    have : 4 * K * s ^ 3 * s ^ 2 ≤ Real.pi * s ^ 16 := by
      have e : Real.pi * s ^ 16 = Real.pi * s ^ 11 * s ^ 5 := by ring
      have e2 : 4 * K * s ^ 3 * s ^ 2 = 4 * K * s ^ 5 := by ring
      rw [e, e2]
      have : 4 * K ≤ Real.pi * s ^ 11 := by nlinarith
      nlinarith [pow_pos hs0 5]
    exact this
  have h4 : cnt ≤ (∑ k ∈ Finset.Icc 1 n, (Real.arctan ((Ep + r * s ^ 2 - lam k) / η) -
          Real.arctan ((E - ℓ - lam k) / η))) / Real.pi + (s ^ 2)⁻¹ := by
    rw [← mul_le_mul_iff_of_pos_right (show 0 < Real.pi by linarith)]
    rw [add_mul, div_mul_cancel₀ _ (by linarith : Real.pi ≠ 0), inv_mul_eq_div]
    linarith
  exact h4

/-- The lower half of the sandwich: `A(E + ℓ, E₊)/π ≤ 𝒩(E, ∞) + N^{-ε'}`, on the deterministic
event, with `r = N^{-2/3}`, `s = N^{ε'/2}`. -/
private lemma Smoothing_lower (n : ℕ) (lam : ℕ → ℝ) (Ep E r s c K Z η ℓ : ℝ) (k₁ : ℕ)
    (hr : 0 < r) (hs : 2 ≤ s) (hc : 0 < c) (hK0 : 0 ≤ K) (hZ0 : 0 ≤ Z)
    (hη : η = r / s ^ 18) (hℓ : ℓ = r / s ^ 2 / 2)
    (hlarge : 2 * K + 4 * Z / c ^ 2 + 2 ≤ s)
    (hk₁ : (k₁ : ℝ) ≤ K * s ^ 3)
    (hZ : ∑ k ∈ Finset.Icc 1 n, (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ ≤ Z)
    (hgap : ∀ k ∈ Finset.Icc 1 n, k₁ ≤ k →
      3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) ≤ E - lam k)
    (hE2 : Ep - r * s ^ 2 ≤ E) :
    (∑ k ∈ Finset.Icc 1 n, (Real.arctan ((Ep + r * s ^ 2 - lam k) / η) -
          Real.arctan ((E + ℓ - lam k) / η))) / Real.pi ≤
      (((Finset.Icc 1 n).filter fun k => E ≤ lam k).card : ℝ) + (s ^ 2)⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  obtain ⟨hlt, hcnt⟩ := Smoothing_count_le n lam E r c k₁ hr hc hgap
  set cnt : ℝ := (((Finset.Icc 1 n).filter fun k => E ≤ lam k).card : ℝ) with hcntdef
  have hs16 : 0 < s ^ 16 := by positivity
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hH : ∀ k ∈ Finset.Icc 1 n, Real.arctan ((Ep + r * s ^ 2 - lam k) / η) -
      Real.arctan ((E + ℓ - lam k) / η) ≤
      Real.pi * (if E ≤ lam k then 1 else 0) + (if k < k₁ then 2 / s ^ 16 else 0) +
        4 / (c ^ 2 * s ^ 16) * (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hκ : 0 < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hnn : 0 ≤ 4 / (c ^ 2 * s ^ 16) * (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ := by positivity
    have hnn2 : 0 ≤ 2 / s ^ 16 := by positivity
    by_cases hEk : E ≤ lam k
    · have hk' := hlt k hk hEk
      have h1 := Real.arctan_lt_pi_div_two ((Ep + r * s ^ 2 - lam k) / η)
      have h2 := Real.neg_pi_div_two_lt_arctan ((E + ℓ - lam k) / η)
      simp only [hEk, ite_true, hk', mul_one]
      linarith
    · have hEk' := not_le.mp hEk
      simp only [hEk, ite_false, mul_zero, zero_add]
      by_cases hk' : k < k₁
      · simp only [hk', ite_true]
        have hb : 0 < E + ℓ - lam k := by linarith
        have := Smoothing_arctan_diff_le (a := Ep + r * s ^ 2 - lam k) hη0 hb
        have h3 : η / (E + ℓ - lam k) ≤ η / ℓ := div_le_div_of_nonneg_left hη0.le hℓ0 (by linarith)
        have h4 : η / ℓ = 2 / s ^ 16 := by rw [hη, hℓ]; field_simp
        linarith
      · have hk'' := not_lt.mp hk'
        simp only [hk', ite_false, zero_add]
        have hβ := hgap k hk hk''
        have hβ0 : 0 < 3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) := by positivity
        have hb : 3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) ≤ E + ℓ - lam k := by linarith
        have hb0 : 0 < E + ℓ - lam k := lt_of_lt_of_le hβ0 hb
        have hm : (Ep + r * s ^ 2 - lam k) - (E + ℓ - lam k) ≤ 2 * (r * s ^ 2) := by linarith
        have h1 := Smoothing_arctan_diff_le' (a := Ep + r * s ^ 2 - lam k) hη0 hb0
          (by positivity) hm
        have h2 : η * (2 * (r * s ^ 2)) / (E + ℓ - lam k) ^ 2 ≤
            η * (2 * (r * s ^ 2)) / (3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hβ0.le hb 2)
        have h3 : η * (2 * (r * s ^ 2)) / (3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r)) ^ 2 =
            32 / 9 / (c ^ 2 * s ^ 16) * (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ := by
          rw [hη]
          field_simp
          ring
        have h5 : 32 / 9 / (c ^ 2 * s ^ 16) * (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ ≤
            4 / (c ^ 2 * s ^ 16) * (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
        linarith
  have hsum := Finset.sum_le_sum hH
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hc1 : (((Finset.Icc 1 n).filter fun k => k < k₁).card : ℝ) ≤ k₁ := by
    have : ((Finset.Icc 1 n).filter fun k => k < k₁) ⊆ Finset.range k₁ := by
      intro k hk
      rw [Finset.mem_filter] at hk
      exact Finset.mem_range.mpr hk.2
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hc2 : (((Finset.Icc 1 n).filter fun k => k < k₁).card : ℝ) * (2 / s ^ 16) ≤
      K * s ^ 3 * (2 / s ^ 16) :=
    mul_le_mul_of_nonneg_right (hc1.trans hk₁) (by positivity)
  have hc3 : 4 / (c ^ 2 * s ^ 16) * ∑ k ∈ Finset.Icc 1 n, (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ ≤
      4 / (c ^ 2 * s ^ 16) * Z := mul_le_mul_of_nonneg_left hZ (by positivity)
  have h11 : s ≤ s ^ 11 := by simpa using Smoothing_pow_le hs1 (show 1 ≤ 11 by norm_num)
  have h14 : s ≤ s ^ 14 := by simpa using Smoothing_pow_le hs1 (show 1 ≤ 14 by norm_num)
  have hP : 0 ≤ 4 * Z / c ^ 2 := by positivity
  have e1 : K * s ^ 3 * (2 / s ^ 16) ≤ (s ^ 2)⁻¹ := by
    have : K * s ^ 3 * (2 / s ^ 16) = (2 * K) / s ^ 13 := by field_simp
    rw [this, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * K ≤ s ^ 11 := by linarith
    nlinarith [pow_pos hs0 2]
  have e2 : 4 / (c ^ 2 * s ^ 16) * Z ≤ (s ^ 2)⁻¹ := by
    have : 4 / (c ^ 2 * s ^ 16) * Z = (4 * Z / c ^ 2) / s ^ 16 := by field_simp
    rw [this, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * Z / c ^ 2 ≤ s ^ 14 := by linarith
    nlinarith [pow_pos hs0 2]
  have e3 : 0 < (s ^ 2)⁻¹ := by positivity
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.pi)]
  nlinarith

/-- `N^a ≥ c` for all large `N`, when `a > 0`. -/
private lemma Smoothing_ev (c a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop c)

/-- The series `Σ_k k^{-4/3}`, written as `Σ_k ((k^{2/3})²)⁻¹`, converges. -/
private lemma Smoothing_summable :
    Summable (fun k : ℕ => (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹) := by
  have h := Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 4 / 3 by norm_num)
  refine h.congr fun k => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
  norm_num

/-- The index threshold `k₁ = ⌈(M + 1)² s³⌉`: for `k ≥ k₁`, `M s² ≤ k^{2/3}`; and `k₁ ≤ K s³` with
`K = (M + 1)² + 1`. -/
private lemma Smoothing_thresh (M s : ℝ) (hM : 0 < M) (hs : 1 ≤ s) :
    (∀ k : ℕ, ⌈(M + 1) ^ 2 * s ^ 3⌉₊ ≤ k → M * s ^ 2 ≤ (k : ℝ) ^ (2 / 3 : ℝ)) ∧
      ((⌈(M + 1) ^ 2 * s ^ 3⌉₊ : ℕ) : ℝ) ≤ ((M + 1) ^ 2 + 1) * s ^ 3 := by
  have hs0 : 0 < s := by linarith
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs
  refine ⟨fun k hk => ?_, ?_⟩
  · have hk' : (M + 1) ^ 2 * s ^ 3 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    set κ : ℝ := (k : ℝ) ^ (2 / 3 : ℝ) with hκ
    have hκ0 : 0 ≤ κ := Real.rpow_nonneg (Nat.cast_nonneg k) _
    have hκ3 : κ ^ 3 = (k : ℝ) ^ 2 := by
      rw [hκ, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
      norm_num
    by_contra hcon
    have hlt : κ < M * s ^ 2 := not_le.mp hcon
    have h1 : κ ^ 3 < (M * s ^ 2) ^ 3 := pow_lt_pow_left₀ hlt hκ0 (by norm_num)
    have h2 : ((M + 1) ^ 2 * s ^ 3) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hk' 2
    have h3 : (M * s ^ 2) ^ 3 ≤ ((M + 1) ^ 2 * s ^ 3) ^ 2 := by
      have e1 : (M * s ^ 2) ^ 3 = M ^ 3 * s ^ 6 := by ring
      have e2 : ((M + 1) ^ 2 * s ^ 3) ^ 2 = (M + 1) ^ 4 * s ^ 6 := by ring
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : M ^ 3 ≤ (M + 1) ^ 3 := pow_le_pow_left₀ hM.le (by linarith) 3
      have : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    linarith
  · have h := Nat.ceil_lt_add_one (show 0 ≤ (M + 1) ^ 2 * s ^ 3 by positivity)
    nlinarith

/-- `λ_k ≤ λ_1` for `k ∈ ⟦1, card ι⟧`. -/
private lemma Smoothing_eigK_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) :
    eigK X k ≤ eigK X 1 := by
  have h1 : k - 1 < Fintype.card ι := by omega
  have h0 : 1 - 1 < Fintype.card ι := by omega
  simp only [eigK, eigs, hX, h1, h0, dite_true]
  exact hX.eigenvalues₀_antitone (by simp [Fin.le_def])

set_option maxHeartbeats 1000000 in
/-- The counting function between two smoothed traces near `E⁺` ([Erds2017ADA, Corollary 17.3],
(17.5) there, after [Erds2017ADA, Lemma 17.2]): for `ε' ∈ (0, 1/100]`, `η = N^{-2/3-9ε'}`,
`ℓ = N^{-2/3-ε'}/2`, `E₊ = E⁺ + N^{-2/3+ε'}` and `|E - E⁺| ≤ N^{-2/3+ε'}`, outside probability
`N^{-D'}` and uniformly in `t ≥ 0`,
`A(E + ℓ, E₊)/π - N^{-ε'} ≤ 𝒩(E, ∞) ≤ A(E - ℓ, E₊)/π + N^{-ε'}`. -/
theorem edge_smoothing (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 / 100 → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ E : ℝ, |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε') →
        ouMatLaw D N L t {h |
          (eigCountAbove (Matrix.of h + lam D N A) E : ℝ) <
            edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε'))
              (E + (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2)
              (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi - (N : ℝ) ^ (-ε') ∨
          edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε'))
              (E - (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2)
              (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi + (N : ℝ) ^ (-ε') <
            (eigCountAbove (Matrix.of h + lam D N A) E : ℝ)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro ε' hε' _ D' hD'
  obtain ⟨c, C₀, hc, hC₀, Nκ, hκ⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨N₁, h₁⟩ := samefort_local D (by omega) δA (1 / 5) hδA (by norm_num) C ε' hε'
    (D' + 1) (by linarith)
  obtain ⟨N₂, h₂⟩ := spec_inclusion D (by omega) δA hδA C' (ε' / 2) (by positivity) (D' + 1)
    (by linarith)
  set M : ℝ := 8 / c with hM
  have hM0 : 0 < M := by positivity
  set K : ℝ := (M + 1) ^ 2 + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Z : ℝ := ∑' k : ℕ, (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun k => by positivity
  obtain ⟨N₃, h₃⟩ := Smoothing_ev (2 * K + 4 * Z / c ^ 2 + 2) (ε' / 2) (by positivity)
  refine ⟨max (max (max Nκ N₁) (max N₂ N₃)) 2, ?_⟩
  intro N hN L t ht A hA E hE
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hNκ, hN₁⟩, hN₂, hN₃⟩, hN2⟩ := hN
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  -- the parameters `r = N^{-2/3}`, `s = N^{ε'/2}`
  set r : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ)) with hr
  set s : ℝ := (N : ℝ) ^ (ε' / 2) with hs
  have hr0 : 0 < r := Real.rpow_pos_of_pos hN0 _
  have hlarge : 2 * K + 4 * Z / c ^ 2 + 2 ≤ s := h₃ N hN₃
  have hs2 : 2 ≤ s := by
    have : 0 ≤ 4 * Z / c ^ 2 := by positivity
    linarith
  have hs0 : 0 < s := by linarith
  have hspow : ∀ m : ℕ, s ^ m = (N : ℝ) ^ (ε' / 2 * m) := fun m => by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have hneg : ∀ m : ℕ, (N : ℝ) ^ (-(ε' / 2 * m)) = (s ^ m)⁻¹ := fun m => by
    rw [hspow, ← Real.rpow_neg hN0.le]
  have e1 : (N : ℝ) ^ (-ε') = (s ^ 2)⁻¹ := by
    rw [← hneg 2]
    congr 1
    push_cast
    ring
  have e2 : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε') = r * s ^ 2 := by
    rw [Real.rpow_add hN0, hspow]
    congr 2
    push_cast
    ring
  have e3 : (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2 = r / s ^ 2 / 2 := by
    rw [sub_eq_add_neg, Real.rpow_add hN0, e1, div_eq_mul_inv r]
  have e4 : (N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε') = r / s ^ 18 := by
    rw [sub_eq_add_neg, Real.rpow_add hN0, show -(9 * ε') = -(ε' / 2 * ((18 : ℕ) : ℝ)) by
      push_cast; ring, hneg, div_eq_mul_inv r]
  have e5 : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε' / 2) = r * s := by
    rw [Real.rpow_add hN0]
  have hpow2 : (N : ℝ) ^ ε' = s ^ 2 := by
    rw [hspow]
    congr 1
    push_cast
    ring
  have h2N : 2 * (N : ℝ) ^ (-(D' + 1)) ≤ (N : ℝ) ^ (-D') := by
    have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [show -(D' + 1) = -D' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hD'0 : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
    rw [e]
    have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2r
    nlinarith
  have hpos : 0 ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hN0.le _
  -- the three exceptional events
  set μ := ouMatLaw D N L t with hμ
  have hLL := hC' N L t ht
  set Rbad : Set (Idx D N → Idx D N → ℂ) := {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
    (N : ℝ) ^ ε' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
      |eigK (Matrix.of h + lam D N A) k - quant (rho (lam D N A)) (D * N) k|} with hRbad
  have hR : μ Rbad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := (h₁ N hN₁ L t ht A hA).2.2
  set Sbad : Set (Idx D N → Idx D N → ℂ) :=
    {h | Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε' / 2) <
          eigK (Matrix.of h + lam D N A) 1 ∨
        eigK (Matrix.of h + lam D N A) (D * N) <
          Eminus (lam D N A) - (N : ℝ) ^ (-(2 / 3 : ℝ) + ε' / 2)} with hSbad
  have hSb : μ Sbad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    h₂ N hN₂ (Real.exp (-t)) (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) μ hLL A hA
  have hNH : μ {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp hLL.herm
  -- the threshold index
  obtain ⟨hk₁κ, hk₁K⟩ := Smoothing_thresh M s hM0 (by linarith)
  set k₁ : ℕ := ⌈(M + 1) ^ 2 * s ^ 3⌉₊ with hk₁
  have hZsum : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2)⁻¹ ≤ Z := fun n =>
    Summable.sum_le_tsum _ (fun k _ => by positivity) Smoothing_summable
  have hcard : Fintype.card (Idx D N) = D * N := by simp
  have hE' := abs_le.mp (hE.trans_eq e2)
  have hsub : {h | (eigCountAbove (Matrix.of h + lam D N A) E : ℝ) <
            edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε'))
              (E + (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2)
              (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi - (N : ℝ) ^ (-ε') ∨
          edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε'))
              (E - (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2)
              (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi + (N : ℝ) ^ (-ε') <
            (eigCountAbove (Matrix.of h + lam D N A) E : ℝ)} ⊆
      Rbad ∪ Sbad ∪ {h | ¬ (Matrix.of h).IsHermitian} := by
    intro h hh
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨hR', hS'⟩, hNH'⟩ := hcon
    have hHerm : (Matrix.of h).IsHermitian := not_not.mp hNH'
    simp only [hRbad, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hR'
    simp only [hSbad, Set.mem_ofPred_eq, not_or, not_lt] at hS'
    simp only [Set.mem_ofPred_eq] at hh
    set X := Matrix.of h + lam D N A with hX
    have hXherm : X.IsHermitian := hHerm.add (lam_isHermitian D N A)
    have hS1 : eigK X 1 ≤ Eplus (lam D N A) + r * s := by rw [← e5]; exact hS'.1
    have hSall : ∀ k ∈ Finset.Icc 1 (D * N), eigK X k ≤ Eplus (lam D N A) + r * s := fun k hk => by
      have := Finset.mem_Icc.mp hk
      exact (Smoothing_eigK_le_one X hXherm k this.1 (by rw [hcard]; exact this.2)).trans hS1
    have hgap : ∀ k ∈ Finset.Icc 1 (D * N), k₁ ≤ k →
        3 * c / 4 * ((k : ℝ) ^ (2 / 3 : ℝ) * r) ≤ E - eigK X k := by
      intro k hk hkk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      obtain ⟨hκ1, -, -, -⟩ := hκ N hNκ A hA k hk1 hkn
      have hrig := hR' k hk1 hkn
      have hrk : rk D N k ^ (-(1 / 3 : ℝ)) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
        unfold rk
        have : 1 ≤ min k (D * N + 1 - k) := le_min hk1 (by omega)
        exact_mod_cast this
      have hrig' : |eigK X k - quant (rho (lam D N A)) (D * N) k| ≤ s ^ 2 * r := by
        refine hrig.trans ?_
        rw [hpow2]
        calc s ^ 2 * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) ≤
            s ^ 2 * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * 1) := by gcongr
          _ = s ^ 2 * r := by rw [mul_one]
      have hκs := hk₁κ k hkk
      have hκ0 : 0 < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        linarith) _
      have hs2' : s ^ 2 ≤ c / 8 * (k : ℝ) ^ (2 / 3 : ℝ) := by
        rw [hM, div_mul_eq_mul_div, div_le_iff₀ hc] at hκs
        linarith
      have h5 : r * s ^ 2 ≤ r * (c / 8 * (k : ℝ) ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hs2' hr0.le
      have h6 := abs_le.mp hrig'
      nlinarith [hE'.1, hE'.2]
    have hP : 0 ≤ 4 * Z / c ^ 2 := by positivity
    have hup := Smoothing_upper (D * N) (fun k => eigK X k) (Eplus (lam D N A)) E r s c K
      (r / s ^ 18) (r / s ^ 2 / 2) k₁ hr0 hs2 hc rfl rfl (by linarith) hk₁K hSall hgap
      (by linarith [hE'.2])
    have hlo := Smoothing_lower (D * N) (fun k => eigK X k) (Eplus (lam D N A)) E r s c K Z
      (r / s ^ 18) (r / s ^ 2 / 2) k₁ hr0 hs2 hc hK0 hZ0 rfl rfl hlarge hk₁K (hZsum _) hgap
      (by linarith [hE'.1])
    have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε') := Real.rpow_pos_of_pos hN0 _
    simp only [edgeCount_eq_arctan D N A _ _ _ hη0 h hHerm] at hh
    simp only [e1, e2, e3, e4, eigCountAbove, hcard] at hh
    rcases hh with hh | hh
    · linarith
    · linarith
  calc μ _ ≤ μ (Rbad ∪ Sbad ∪ {h | ¬ (Matrix.of h).IsHermitian}) := measure_mono hsub
    _ ≤ μ (Rbad ∪ Sbad) + μ {h | ¬ (Matrix.of h).IsHermitian} := measure_union_le _ _
    _ ≤ (μ Rbad + μ Sbad) + μ {h | ¬ (Matrix.of h).IsHermitian} :=
        add_le_add_left (measure_union_le _ _) _
    _ ≤ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) + 0 := by
        rw [hNH]
        exact add_le_add_left (add_le_add hR hSb) _
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D' + 1))) := by
        rw [add_zero, ← ENNReal.ofReal_add hpos hpos, two_mul]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal h2N

/-- The line `a ↦ (a, s')` in `ℝ^{n+1}` has derivative `e₀`. -/
private lemma Smoothing_hasDerivAt_cons (n : ℕ) (s' : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a : ℝ => (Fin.cons a s' : Fin (n + 1) → ℝ)) (Pi.single 0 1) a := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hasDerivAt_id' a
  · simpa using hasDerivAt_const a (s' j)

/-- The derivative of `a ↦ ∂₁⋯∂_n O(a, s')` in the first variable is `∂₀ ∂₁⋯∂_n O`. -/
private lemma Smoothing_hasDerivAt_G (n : ℕ) (O : (Fin (n + 1) → ℝ) → ℝ) (hO : ContDiff ℝ ∞ O)
    (s' : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a : ℝ => iteratedFDeriv ℝ n O (Fin.cons a s' : Fin (n + 1) → ℝ)
        (fun k : Fin n => Pi.single k.succ 1))
      (iteratedFDeriv ℝ (n + 1) O (Fin.cons a s' : Fin (n + 1) → ℝ)
        (fun k : Fin (n + 1) => Pi.single k 1)) a := by
  have hF : Differentiable ℝ (iteratedFDeriv ℝ n O) :=
    hO.differentiable_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
  set z : Fin (n + 1) → ℝ := Fin.cons a s' with hz
  have h1 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Fin (n + 1) → ℝ) ℝ
    (fun k : Fin n => Pi.single k.succ 1)).hasFDerivAt.comp z (hF z).hasFDerivAt)
  have h2 := h1.comp_hasDerivAt a (Smoothing_hasDerivAt_cons n s' a)
  refine h2.congr_deriv ?_
  rw [iteratedFDeriv_succ_apply_left]
  rfl

/-- A function on `ℝ^{n+1}` vanishing off a compact set has compact support along the line
`a ↦ (a, s')`. -/
private lemma Smoothing_cs_line {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} {K : Set (Fin (n + 1) → ℝ)}
    (hK : IsCompact K) (hF : ∀ z, z ∉ K → F z = 0) (s' : Fin n → ℝ) :
    ∃ R : ℝ, ∀ a : ℝ, R < |a| → F (Fin.cons a s' : Fin (n + 1) → ℝ) = 0 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨R, fun a ha => hF _ fun hmem => ?_⟩
  have h1 := mem_closedBall_zero_iff.mp (hR hmem)
  have h2 := norm_le_pi_norm (Fin.cons a s' : Fin (n + 1) → ℝ) 0
  simp only [Fin.cons_zero, Real.norm_eq_abs] at h2
  linarith

/-- FTC in the first variable: `∫_{a < x₀} ∂₀(∂₁⋯∂_n O)(a, s') da = ∂₁⋯∂_n O(x₀, s')`. -/
private lemma Smoothing_ftc (n : ℕ) (O : (Fin (n + 1) → ℝ) → ℝ) (hO : ContDiff ℝ ∞ O)
    (hOc : HasCompactSupport O) (s' : Fin n → ℝ) (x₀ : ℝ) :
    ∫ a in Set.Iio x₀, iteratedFDeriv ℝ (n + 1) O (Fin.cons a s' : Fin (n + 1) → ℝ)
        (fun k : Fin (n + 1) => Pi.single k 1) =
      iteratedFDeriv ℝ n O (Fin.cons x₀ s' : Fin (n + 1) → ℝ)
        (fun k : Fin n => Pi.single k.succ 1) := by
  have hd := Smoothing_hasDerivAt_G n O hO s'
  have hsupp : ∀ (i : ℕ) (w : Fin i → Fin (n + 1) → ℝ), ∀ z, z ∉ tsupport O →
      iteratedFDeriv ℝ i O z w = 0 := by
    intro i w z hz
    have : iteratedFDeriv ℝ i O z = 0 := by
      by_contra h
      exact hz (support_iteratedFDeriv_subset i (Function.mem_support.mpr h))
    simp [this]
  obtain ⟨R₁, hR₁⟩ := Smoothing_cs_line hOc (fun z hz => hsupp n _ z hz) s'
  obtain ⟨R₂, hR₂⟩ := Smoothing_cs_line hOc (fun z hz => hsupp (n + 1) _ z hz) s'
  have hcont : Continuous fun a : ℝ => iteratedFDeriv ℝ (n + 1) O
      (Fin.cons a s' : Fin (n + 1) → ℝ) (fun k : Fin (n + 1) => Pi.single k 1) := by
    have h1 : Continuous (iteratedFDeriv ℝ (n + 1) O) := hO.continuous_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)
    have h2 : Continuous fun a : ℝ => (Fin.cons a s' : Fin (n + 1) → ℝ) :=
      continuous_pi fun i => Fin.cases continuous_id (fun j => continuous_const) i
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) ℝ
      (fun k : Fin (n + 1) => Pi.single k 1)).continuous.comp (h1.comp h2)
  have hint : IntegrableOn (fun a : ℝ => iteratedFDeriv ℝ (n + 1) O
      (Fin.cons a s' : Fin (n + 1) → ℝ) (fun k : Fin (n + 1) => Pi.single k 1))
      (Set.Iic x₀) volume := by
    refine Integrable.integrableOn ?_
    refine hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -R₂) (b := R₂)) ?_)
    intro a ha
    refine hR₂ a ?_
    by_contra hcon
    exact ha ⟨by linarith [abs_le.mp (not_lt.mp hcon)], by linarith [abs_le.mp (not_lt.mp hcon)]⟩
  have htend : Tendsto (fun a : ℝ => iteratedFDeriv ℝ n O (Fin.cons a s' : Fin (n + 1) → ℝ)
      (fun k : Fin n => Pi.single k.succ 1)) atBot (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot (-|R₁| - 1)] with a ha
    symm
    refine hR₁ a ?_
    have : -|R₁| - 1 < -|R₁| := by linarith
    rw [abs_of_neg (by linarith [abs_nonneg R₁])]
    linarith [le_abs_self R₁]
  rw [← integral_Iic_eq_integral_Iio]
  have := integral_Iic_of_hasDerivAt_of_tendsto (hd x₀).continuousAt.continuousWithinAt
    (fun a _ => hd a) hint htend
  simpa using this

/-- The linear map `s' ↦ (0, s')` of `ℝ^n` into `ℝ^{n+1}`. -/
private def Smoothing_L (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun s' => Fin.cons 0 s'
      map_add' := fun a b => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun c a => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp }

/-- The restriction of `O` to the slice `s₀ = x₀` has the mixed partial `∂₁⋯∂_n` of `O`. -/
private lemma Smoothing_slice (n : ℕ) (O : (Fin (n + 1) → ℝ) → ℝ) (hO : ContDiff ℝ ∞ O) (x₀ : ℝ)
    (s' : Fin n → ℝ) :
    iteratedFDeriv ℝ n (fun s' : Fin n → ℝ => O (Fin.cons x₀ s')) s'
        (fun k : Fin n => Pi.single k 1) =
      iteratedFDeriv ℝ n O (Fin.cons x₀ s' : Fin (n + 1) → ℝ)
        (fun k : Fin n => Pi.single k.succ 1) := by
  set c : Fin (n + 1) → ℝ := Fin.cons x₀ 0 with hc
  have hL : ∀ w : Fin n → ℝ, Smoothing_L n w = Fin.cons 0 w := fun w => rfl
  have hfun : (fun s' : Fin n → ℝ => O (Fin.cons x₀ s')) =
      (fun z : Fin (n + 1) → ℝ => O (z + c)) ∘ (Smoothing_L n) := by
    funext w
    simp only [Function.comp, hL, hc]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hsm : ContDiff ℝ ∞ (fun z : Fin (n + 1) → ℝ => O (z + c)) :=
    hO.comp (contDiff_id.add contDiff_const)
  rw [hfun, (Smoothing_L n).iteratedFDeriv_comp_right hsm s'
    (by exact_mod_cast WithTop.coe_le_coe.mpr le_top), iteratedFDeriv_comp_add_right]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL]
  have e1 : (Fin.cons 0 s' : Fin (n + 1) → ℝ) + c = Fin.cons x₀ s' := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [hc]
  rw [e1]
  congr 1
  funext k
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.succ_ne_zero]
  · simp [Pi.single_apply]

/-- Fubini in the first coordinate: the integral over the orthant `{s < x}` of `ℝ^{n+1}` is the
integral over the orthant of `ℝ^n` of the integral over `(-∞, x₀)`. -/
private lemma Smoothing_split (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Continuous F)
    (hFc : HasCompactSupport F) (x : Fin (n + 1) → ℝ) :
    ∫ s in {s : Fin (n + 1) → ℝ | ∀ k, s k < x k}, F s =
      ∫ s' in {s' : Fin n → ℝ | ∀ k : Fin n, s' k < x k.succ},
        ∫ a in Set.Iio (x 0), F (Fin.cons a s' : Fin (n + 1) → ℝ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he_def
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hsymm : ∀ (a : ℝ) (s' : Fin n → ℝ), e.symm (a, s') = (Fin.cons a s' : Fin (n + 1) → ℝ) := by
    intro a s'
    simp [he_def, MeasurableEquiv.piFinSuccAbove]
  have hfwd : ∀ s : Fin (n + 1) → ℝ, e s = (s 0, fun j => s j.succ) := by
    intro s
    simp [he_def, MeasurableEquiv.piFinSuccAbove]
    rfl
  set B' : Set (Fin n → ℝ) := {s' | ∀ k : Fin n, s' k < x k.succ} with hB'
  have hS : {s : Fin (n + 1) → ℝ | ∀ k, s k < x k} = e ⁻¹' (Set.Iio (x 0) ×ˢ B') := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hfwd, Set.mem_prod, Set.mem_Iio, hB']
    exact ⟨fun h => ⟨h 0, fun k => h k.succ⟩, fun h k => Fin.cases h.1 h.2 k⟩
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e.symm p)) (volume.prod volume) := by
    have h1 : Integrable F volume := hF.integrable_of_hasCompactSupport hFc
    have h2 := (he.symm e).integrable_comp_emb e.symm.measurableEmbedding (g := F)
    exact h2.mpr h1
  have hrw : ∫ s in e ⁻¹' (Set.Iio (x 0) ×ˢ B'), F s =
      ∫ p in Set.Iio (x 0) ×ˢ B', F (e.symm p) ∂(volume : Measure (ℝ × (Fin n → ℝ))) := by
    have := he.setIntegral_preimage_emb e.measurableEmbedding (fun p => F (e.symm p))
      (Set.Iio (x 0) ×ˢ B')
    simpa using this
  rw [hS, hrw]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hint' : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e.symm p))
      ((volume.restrict (Set.Iio (x 0))).prod (volume.restrict B')) := by
    rw [Measure.prod_restrict]
    exact hint.restrict
  rw [integral_prod_symm _ hint']
  simp only [hsymm]

/-- The orthant integral of the mixed partial: for smooth compactly supported `O` on `ℝ^n`,
`∫_{s < x} ∂₁⋯∂_n O(s) ds = O(x)`. -/
private lemma Smoothing_orthant : ∀ (n : ℕ) (O : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ O →
    HasCompactSupport O → ∀ x : Fin n → ℝ,
    ∫ s in {s : Fin n → ℝ | ∀ k, s k < x k}, iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) =
      O x
  | 0, O, _, _, x => by
    have hu : {s : Fin 0 → ℝ | ∀ k, s k < x k} = Set.univ := by
      ext s
      simp
    rw [hu, Measure.restrict_univ, Measure.volume_pi_eq_dirac x, integral_dirac]
    rw [iteratedFDeriv_zero_apply]
  | n + 1, O, hO, hOc, x => by
    have hD : Continuous (fun s : Fin (n + 1) → ℝ =>
        iteratedFDeriv ℝ (n + 1) O s (fun k : Fin (n + 1) => Pi.single k 1)) := by
      have h1 : Continuous (iteratedFDeriv ℝ (n + 1) O) := hO.continuous_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) ℝ
        (fun k : Fin (n + 1) => Pi.single k 1)).continuous.comp h1
    have hDc : HasCompactSupport (fun s : Fin (n + 1) → ℝ =>
        iteratedFDeriv ℝ (n + 1) O s (fun k : Fin (n + 1) => Pi.single k 1)) :=
      (hOc.iteratedFDeriv (n + 1)).comp_left (g := fun T : ContinuousMultilinearMap ℝ
        (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) ℝ => T (fun k : Fin (n + 1) => Pi.single k 1))
        (by simp)
    rw [Smoothing_split n _ hD hDc x]
    simp only [Smoothing_ftc n O hO hOc]
    have hO₀ : ContDiff ℝ ∞ (fun s' : Fin n → ℝ => O (Fin.cons (x 0) s' : Fin (n + 1) → ℝ)) :=
      hO.comp (contDiff_pi.mpr fun i => Fin.cases (by simpa using contDiff_const)
        (fun j => by simpa only [Fin.cons_succ] using contDiff_apply ℝ (fun _ : Fin n => ℝ) j) i)
    have hO₀c : HasCompactSupport
        (fun s' : Fin n → ℝ => O (Fin.cons (x 0) s' : Fin (n + 1) → ℝ)) := by
      have hemb : Topology.IsClosedEmbedding
          (fun s' : Fin n → ℝ => (Fin.cons (x 0) s' : Fin (n + 1) → ℝ)) :=
        Function.LeftInverse.isClosedEmbedding
          (f := (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)))
          (g := fun s' : Fin n → ℝ => (Fin.cons (x 0) s' : Fin (n + 1) → ℝ))
          (fun s' => Fin.tail_cons (α := fun _ => ℝ) (x 0) s')
          (continuous_pi fun j => continuous_apply _)
          (continuous_pi fun i => Fin.cases continuous_const (fun j => continuous_apply j) i)
      exact hOc.comp_isClosedEmbedding hemb
    have ih := Smoothing_orthant n _ hO₀ hO₀c (Fin.tail x)
    simp only [Smoothing_slice n O hO (x 0)] at ih
    have ih' : ∫ s' in {s' : Fin n → ℝ | ∀ k : Fin n, s' k < x k.succ},
        iteratedFDeriv ℝ n O (Fin.cons (x 0) s' : Fin (n + 1) → ℝ)
          (fun k : Fin n => Pi.single k.succ 1) = O (Fin.cons (x 0) (Fin.tail x)) := ih
    rw [ih']
    exact congrArg O (Fin.cons_self_tail x)

/-- The layer-cake form of `E O(x)` for smooth compactly supported `O` on `ℝ^n`:
`E O(x) = ∫ ∂₁ ⋯ ∂_n O(s) P(x_k > s_k for all k) ds` (proof of Lemma 4.2 [CVtV]). -/
theorem integral_eq_survival (n : ℕ) (O : (Fin n → ℝ) → ℝ) (hO : ContDiff ℝ ∞ O)
    (hOc : HasCompactSupport O) (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] :
    ∫ x, O x ∂ν =
      ∫ s, iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) * (ν {x | ∀ k, s k < x k}).toReal := by
  set D : (Fin n → ℝ) → ℝ := fun s => iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) with hDdef
  have hD : Continuous D := by
    have h1 : Continuous (iteratedFDeriv ℝ n O) := hO.continuous_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Fin n → ℝ) ℝ
      (fun k : Fin n => Pi.single k 1)).continuous.comp h1
  have hDc : HasCompactSupport D :=
    (hOc.iteratedFDeriv n).comp_left (g := fun T : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => Fin n → ℝ) ℝ => T (fun k : Fin n => Pi.single k 1)) (by simp)
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {p | ∀ k, p.1 k < p.2 k} with hS
  have hSm : MeasurableSet S := by
    simp only [hS, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt
      ((measurable_pi_apply k).comp measurable_fst) ((measurable_pi_apply k).comp measurable_snd)
  set f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun s x => S.indicator (fun p => D p.1) (s, x) with hf
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    have h1 : Integrable D volume := hD.integrable_of_hasCompactSupport hDc
    have h2 := h1.mul_prod (integrable_const (1 : ℝ) (μ := ν))
    have h3 := h2.indicator hSm
    refine h3.congr (Eventually.of_forall fun p => ?_)
    simp [hf, Function.uncurry]
  have hA : ∀ s : Fin n → ℝ, MeasurableSet {x : Fin n → ℝ | ∀ k, s k < x k} := fun s => by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt measurable_const (measurable_pi_apply k)
  have h1 : ∀ s : Fin n → ℝ, ∫ x, f s x ∂ν = D s * (ν {x | ∀ k, s k < x k}).toReal := by
    intro s
    have : (fun x => f s x) = Set.indicator {x : Fin n → ℝ | ∀ k, s k < x k} (fun _ => D s) := by
      funext x
      simp [hf, hS, Set.indicator]
    rw [this, integral_indicator_const _ (hA s), smul_eq_mul, mul_comm]
    rfl
  have h2 : ∀ x : Fin n → ℝ, ∫ s, f s x = O x := by
    intro x
    have : (fun s => f s x) = Set.indicator {s : Fin n → ℝ | ∀ k, s k < x k} D := by
      funext s
      simp [hf, hS, Set.indicator]
    rw [this, integral_indicator]
    · exact Smoothing_orthant n O hO hOc x
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_lt (measurable_pi_apply k) measurable_const
  calc ∫ x, O x ∂ν = ∫ x, (∫ s, f s x) ∂ν :=
        integral_congr_ae (Eventually.of_forall fun x => (h2 x).symm)
    _ = ∫ s, (∫ x, f s x ∂ν) := (integral_integral_swap hint).symm
    _ = _ := by simp only [h1]; rfl

end RBMTransitionEdge

end
