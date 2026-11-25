module

public import RBMTransitionEdge.Det.MhatSpec
public import RBMTransitionEdge.LocalLaw.FarDet
public import RBMTransitionEdge.LocalLaw.OU
public import RBMTransitionEdge.Prob.GaussianIBP

@[expose] public section

/-!
# Preliminaries for Lemmas 3.6 and 3.7: entry cumulants and the cancellation

The additivity of the cumulants of Lemma 2.11 [lem:complex_cumu] under independent sums, the entry
cumulants of the law (4.3) [eq:eq_in_law_H] of `H_t` of (4.1) [defVt], and the cancellation after
(3.46) [estimate_1_minus_abs_m_2] in the proof of Lemma 3.7 [lemma_G_large_2].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Additivity of the cumulants -/

/-- The mixed moment `∫ z^a z̄^b dρ`. -/
private def lepMom (ρ : Measure ℂ) (a b : ℕ) : ℂ := ∫ z, z ^ a * starRingEnd ℂ z ^ b ∂ρ

/-- The binomial convolution `Σ_{i ≤ a, j ≤ b} C(a,i) C(b,j) f(i,j) g(a-i,b-j)` of two arrays. -/
private def lepBin (f g : ℕ → ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
    ((a.choose i * b.choose j : ℕ) : ℂ) * (f i j * g (a - i) (b - j))

/-- The exponential generating series `Σ f(a,b) X^a Y^b / (a! b!)` of an array, in `ℂ⟦X⟧⟦Y⟧`. -/
private def lepGen (f : ℕ → ℕ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun b => PowerSeries.mk fun a => f a b / ((a.factorial : ℂ) * (b.factorial : ℂ))

/-- The generating series turns the binomial convolution into a product. -/
private lemma lepGen_mul (f g : ℕ → ℕ → ℂ) : lepGen (lepBin f g) = lepGen f * lepGen g := by
  ext b a
  simp only [lepGen, PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold lepBin
  rw [Finset.sum_div]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 : ((a.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((a - i).factorial : ℂ) = a.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h2 : ((b.choose j : ℕ) : ℂ) * (j.factorial : ℂ) * ((b - j).factorial : ℂ) = b.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  have n1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have n2 : ((a - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n3 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have n4 : ((b - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n7 : ((a.choose i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi').ne'
  have n8 : ((b.choose j : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj').ne'
  rw [← h1, ← h2]
  push_cast
  field_simp

/-- The mixed monomials `z^i z̄^j` are integrable when all absolute moments are finite. -/
private lemma lep_int_mom (ρ : Measure ℂ) (hρ : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ρ)
    (i j : ℕ) : Integrable (fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j) ρ := by
  refine (hρ (i + j)).mono' ((continuous_pow i).mul
    (Complex.continuous_conj.pow j)).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  simp [norm_pow, pow_add]

/-- The mixed moments of `μ ∗ ν` are the binomial convolution of those of `μ` and `ν`. -/
private lemma lep_mom_conv (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) μ)
    (hν : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ν) (a b : ℕ) :
    lepMom (μ.conv ν) a b = lepBin (lepMom μ) (lepMom ν) a b := by
  unfold lepMom lepBin
  beta_reduce
  have hc : Continuous (fun z : ℂ => z ^ a * starRingEnd ℂ z ^ b) :=
    (continuous_pow a).mul (Complex.continuous_conj.pow b)
  rw [Measure.conv, integral_map (measurable_add.aemeasurable) hc.aestronglyMeasurable]
  have hexp : ∀ x : ℂ × ℂ, (x.1 + x.2) ^ a * starRingEnd ℂ (x.1 + x.2) ^ b =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i * b.choose j : ℕ) : ℂ) *
          ((x.1 ^ i * starRingEnd ℂ x.1 ^ j) * (x.2 ^ (a - i) * starRingEnd ℂ x.2 ^ (b - j))) := by
    intro x
    rw [map_add, add_pow, add_pow, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hint : ∀ i j : ℕ, Integrable (fun x : ℂ × ℂ =>
      ((a.choose i * b.choose j : ℕ) : ℂ) *
        ((x.1 ^ i * starRingEnd ℂ x.1 ^ j) * (x.2 ^ (a - i) * starRingEnd ℂ x.2 ^ (b - j))))
      (μ.prod ν) := fun i j =>
    ((lep_int_mom μ hμ i j).mul_prod (lep_int_mom ν hν (a - i) (b - j))).const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_prod_mul (μ := μ) (ν := ν) (fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j)
    (fun z : ℂ => z ^ (a - i) * starRingEnd ℂ z ^ (b - j))

/-- All absolute moments of `μ ∗ ν` are finite. -/
private lemma lep_conv_int (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) μ)
    (hν : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ν) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k) (μ.conv ν) := by
  have hc : Continuous (fun z : ℂ => ‖z‖ ^ k) := by fun_prop
  rw [Measure.conv, integrable_map_measure hc.aestronglyMeasurable measurable_add.aemeasurable]
  refine Integrable.mono' (g := fun x : ℂ × ℂ =>
    ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℝ) * (‖x.1‖ ^ i * ‖x.2‖ ^ (k - i))) ?_ ?_ ?_
  · refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
    exact (hμ i).mul_prod (hν (k - i))
  · exact (hc.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [Function.comp, norm_pow, norm_norm]
    calc ‖x.1 + x.2‖ ^ k ≤ (‖x.1‖ + ‖x.2‖) ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) k
      _ = ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℝ) * (‖x.1‖ ^ i * ‖x.2‖ ^ (k - i)) := by
          rw [add_pow]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

/-- The generating series is additive. -/
private lemma lepGen_add (f g : ℕ → ℕ → ℂ) :
    lepGen (fun a b => f a b + g a b) = lepGen f + lepGen g := by
  ext b a
  simp [lepGen, add_div]

/-- The Leibniz rule of the binomial convolution for the shift of the second index. -/
private lemma lepBin_succ (f g : ℕ → ℕ → ℂ) (a b : ℕ) :
    lepBin f g a (b + 1) =
      lepBin f (fun a b => g a (b + 1)) a b + lepBin (fun a b => f a (b + 1)) g a b := by
  unfold lepBin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Finset.sum_choose_succ_mul (R := ℂ) (fun j k => f i j * g (a - i) k) b
  have h2 : ∑ x ∈ Finset.range (b + 1), (b.choose x : ℂ) * (f i x * g (a - i) (b + 1 - x)) =
      ∑ x ∈ Finset.range (b + 1), (b.choose x : ℂ) * (f i x * g (a - i) (b - x + 1)) :=
    Finset.sum_congr rfl fun x hx => by
      have : x ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      rw [show b + 1 - x = b - x + 1 by omega]
  simp only [Nat.cast_mul] at h ⊢
  rw [h2] at h
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [show b + 1 + 1 = b + 2 from rfl, h, mul_add]

/-- The moment–cumulant recursion for the mixed moments, as an identity of arrays: the shifted
moments are the binomial convolution of the shifted cumulants with the moments. -/
private lemma lep_rec (ρ : Measure ℂ) [IsProbabilityMeasure ρ]
    (hρ : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ρ) :
    (fun a b => lepMom ρ a (b + 1)) = lepBin (fun a b => ccum ρ a (b + 1)) (lepMom ρ) := by
  funext a b
  unfold lepMom lepBin
  rw [moment_ccum_recursion ρ hρ a b]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- The generating series of the mixed moments of a probability measure is non-zero. -/
private lemma lep_gen_ne (ρ : Measure ℂ) [IsProbabilityMeasure ρ] : lepGen (lepMom ρ) ≠ 0 := by
  intro h
  have := congrArg (fun s => PowerSeries.coeff 0 (PowerSeries.coeff 0 s)) h
  simp [lepGen, lepMom] at this

/-- The cumulants `𝒞^{(p,q+1)}` of `μ ∗ ν` are the sums of those of `μ` and `ν`. -/
private lemma lep_key (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) μ)
    (hν : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ν) (p q : ℕ) :
    ccum (μ.conv ν) p (q + 1) = ccum μ p (q + 1) + ccum ν p (q + 1) := by
  have hc := lep_conv_int μ ν hμ hν
  have Mc : lepMom (μ.conv ν) = lepBin (lepMom μ) (lepMom ν) := by
    funext a b
    exact lep_mom_conv μ ν hμ hν a b
  have e1 : (fun a b => lepMom (μ.conv ν) a (b + 1)) = fun a b =>
      lepBin (lepMom μ) (lepBin (fun a b => ccum ν a (b + 1)) (lepMom ν)) a b +
        lepBin (lepBin (fun a b => ccum μ a (b + 1)) (lepMom μ)) (lepMom ν) a b := by
    funext a b
    rw [Mc, lepBin_succ, ← lep_rec ν hν, ← lep_rec μ hμ]
  have e2 := lep_rec (μ.conv ν) hc
  rw [e1, Mc] at e2
  have h1 := congrArg lepGen e2
  simp only [lepGen_add, lepGen_mul] at h1
  have h0 : (lepGen (fun a b => ccum (μ.conv ν) a (b + 1)) -
      lepGen (fun a b => ccum μ a (b + 1)) - lepGen (fun a b => ccum ν a (b + 1))) *
        (lepGen (lepMom μ) * lepGen (lepMom ν)) = 0 := by
    linear_combination -h1
  have hG := (mul_eq_zero.mp h0).resolve_right (mul_ne_zero (lep_gen_ne μ) (lep_gen_ne ν))
  have := congrArg (fun s => PowerSeries.coeff p (PowerSeries.coeff q s)) hG
  simp only [lepGen, map_sub, PowerSeries.coeff_mk, map_zero] at this
  have n1 : ((p.factorial : ℂ) * (q.factorial : ℂ)) ≠ 0 := by
    have h1 : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
    have h2 : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos q).ne'
    exact mul_ne_zero h1 h2
  rw [← sub_div, ← sub_div, div_eq_zero_iff] at this
  rcases this with h | h
  · linear_combination h
  · exact absurd h n1

/-- Conjugating every variable conjugates the joint cumulant. -/
private lemma lep_jointCum_conj {n : ℕ} (ρ : Measure ℂ) (X : Fin n → ℂ → ℂ) :
    jointCum ρ (fun i z => starRingEnd ℂ (X i z)) = starRingEnd ℂ (jointCum ρ X) := by
  unfold jointCum
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hB : ∀ B ∈ π.parts, ∫ z, ∏ i ∈ B, starRingEnd ℂ (X i z) ∂ρ =
      starRingEnd ℂ (∫ z, ∏ i ∈ B, X i z ∂ρ) := by
    intro B _
    rw [← integral_conj]
    simp only [map_prod]
  rw [Finset.prod_congr rfl hB, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_prod]

/-- The joint cumulant of `n` copies of one variable depends on `n` only through its value. -/
private lemma lep_jointCum_cast (ρ : Measure ℂ) {n m : ℕ} (h : n = m) (f : ℂ → ℂ) :
    jointCum ρ (fun _ : Fin n => f) = jointCum ρ (fun _ : Fin m => f) := by
  subst h
  rfl

/-- `𝒞^{(p,0)}` is the conjugate of `𝒞^{(0,p)}`. -/
private lemma lep_ccum_swap (ρ : Measure ℂ) (p : ℕ) :
    ccum ρ p 0 = starRingEnd ℂ (ccum ρ 0 p) := by
  have h1 : ccum ρ p 0 = jointCum ρ (fun (_ : Fin (p + 0)) (z : ℂ) =>
      starRingEnd ℂ (starRingEnd ℂ z)) := by
    unfold ccum
    congr 1
    funext i z
    simp
  have h2 : ccum ρ 0 p = jointCum ρ (fun (_ : Fin (0 + p)) (z : ℂ) => starRingEnd ℂ z) := by
    unfold ccum
    congr 1
  rw [h1, h2, lep_jointCum_conj ρ (fun (_ : Fin (p + 0)) (z : ℂ) => starRingEnd ℂ z),
    lep_jointCum_cast ρ (Nat.add_zero p) (starRingEnd ℂ), lep_jointCum_cast ρ (Nat.zero_add p)
      (starRingEnd ℂ)]

/-- Joint cumulants of independent sums: for probability measures `μ, ν` on `ℂ` with all
absolute moments finite and `p + q ≥ 1`, `𝒞^{(p,q)}(μ ∗ ν) = 𝒞^{(p,q)}(μ) + 𝒞^{(p,q)}(ν)` (the
cumulants of Lemma 2.11 [lem:complex_cumu]). -/
theorem ccum_conv (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) μ)
    (hν : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ν) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ccum (μ.conv ν) p q = ccum μ p q + ccum ν p q := by
  rcases q with _ | q
  · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [lep_ccum_swap (μ.conv ν), lep_ccum_swap μ, lep_ccum_swap ν,
      lep_key μ ν hμ hν 0 p', map_add]
  · exact lep_key μ ν hμ hν p q

/-! ### The complex Gaussian and conjugation -/

/-- The map `(x, y) ↦ x + y i` as a continuous linear map. -/
private def lepPair : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

/-- `lepPair (x, y) = x + y i`. -/
private lemma lepPair_apply (p : ℝ × ℝ) : lepPair p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  simp [lepPair, Complex.real_smul]

/-- `cGauss` is the image of `N(0, 1/2) ⊗ N(0, 1/2)` under `(x, y) ↦ x + y i`. -/
private lemma lep_cGauss_eq : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map lepPair := by
  have : (lepPair : ℝ × ℝ → ℂ) = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p; exact lepPair_apply p
  rw [this]
  rfl

/-- `cGauss` is a Gaussian law. -/
private instance lep_cGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  rw [lep_cGauss_eq]
  infer_instance

/-- Every absolute moment of `cGauss` is finite. -/
private lemma lep_cGauss_int (p : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ p) (cGauss : Measure ℂ) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact (IsGaussian.memLp_id (cGauss : Measure ℂ) (p : ENNReal) (by simp)).integrable_norm_pow
      hp.ne'

/-- The cumulants of the conjugate law are the conjugates of the cumulants. -/
private lemma lep_ccum_map_conj (ρ : Measure ℂ) (p q : ℕ) :
    ccum (ρ.map (starRingEnd ℂ)) p q = starRingEnd ℂ (ccum ρ p q) := by
  unfold ccum jointCum
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hB : ∀ B ∈ π.parts, ∫ z, ∏ i ∈ B, (fun i : Fin (p + q) =>
      if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) i z
        ∂(ρ.map (starRingEnd ℂ)) = starRingEnd ℂ (∫ z, ∏ i ∈ B, (fun i : Fin (p + q) =>
      if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) i z ∂ρ) := by
    intro B _
    have hc : Continuous (fun z : ℂ => ∏ i ∈ B, (fun i : Fin (p + q) =>
        if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) i z) := by
      refine continuous_finsetProd _ fun i _ => ?_
      by_cases h : (i : ℕ) < p
      · simp only [h, ite_true]; exact continuous_id
      · simp only [h, ite_false]; exact Complex.continuous_conj
    rw [integral_map Complex.continuous_conj.aemeasurable hc.aestronglyMeasurable,
      ← integral_conj]
    congr 1
    funext z
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < p <;> simp [h]
  rw [Finset.prod_congr rfl hB, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_prod]

/-- The cumulants of `a f(ω₁) + b g(ω₂)` under a product law: `a^{p+q} 𝒞^{(p,q)}(f) +
b^{p+q} 𝒞^{(p,q)}(g)` for `p + q ≥ 1`. -/
private lemma lep_sum_law {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P : Measure Ω₁) (Q : Measure Ω₂) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω₁ → ℂ) (g : Ω₂ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (P.map f))
    (hgi : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (Q.map g)) (a b : ℝ) (p q : ℕ)
    (hpq : 1 ≤ p + q) :
    ccum ((P.prod Q).map fun ω => (a : ℂ) * f ω.1 + (b : ℂ) * g ω.2) p q =
      (a : ℂ) ^ (p + q) * ccum (P.map f) p q + (b : ℂ) ^ (p + q) * ccum (Q.map g) p q := by
  have hsc : ∀ (ρ : Measure ℂ) (c : ℝ), (∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ρ) →
      ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (ρ.map fun z => (c : ℂ) * z) := by
    intro ρ c hρ k
    have hc : Continuous (fun z : ℂ => ‖z‖ ^ k) := by fun_prop
    have hm : Measurable (fun z : ℂ => (c : ℂ) * z) := measurable_id.const_mul _
    rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
    simpa [Function.comp_def, norm_mul, mul_pow] using (hρ k).const_mul (|c| ^ k)
  have hmap : (P.prod Q).map (fun ω => (a : ℂ) * f ω.1 + (b : ℂ) * g ω.2) =
      ((P.map f).map fun z => (a : ℂ) * z).conv ((Q.map g).map fun z => (b : ℂ) * z) := by
    have hma : Measurable (fun z : ℂ => (a : ℂ) * z) := measurable_id.const_mul _
    have hmb : Measurable (fun z : ℂ => (b : ℂ) * z) := measurable_id.const_mul _
    have h1 : (P.map f).map (fun z => (a : ℂ) * z) = P.map (fun x => (a : ℂ) * f x) :=
      Measure.map_map hma hf
    have h2 : (Q.map g).map (fun z => (b : ℂ) * z) = Q.map (fun x => (b : ℂ) * g x) :=
      Measure.map_map hmb hg
    rw [h1, h2, Measure.conv, Measure.map_prod_map _ _ (hf.const_mul (a : ℂ))
      (hg.const_mul (b : ℂ)), Measure.map_map (g := fun x : ℂ × ℂ => x.1 + x.2)
      (measurable_fst.add measurable_snd)
      ((hf.const_mul (a : ℂ)).prodMap (hg.const_mul (b : ℂ)))]
    rfl
  rw [hmap, ccum_conv _ _ (hsc _ a hfi) (hsc _ b hgi) p q hpq, ccum_map_smul, ccum_map_smul]

/-! ### The law of an entry of `H_t` -/

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma lep_meas_wig (n : ℕ) (i j : Fin n) :
    Measurable fun c : Coords n => wig n c i j := by
  unfold wig
  by_cases h1 : i = j
  · simp only [h1, ite_true]
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp measurable_fst))
  · by_cases h2 : i < j
    · simp only [h1, h2, ite_true, ite_false]
      exact measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
    · simp only [h1, h2, ite_false]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)))

/-- The array of coordinates `blockEmb D N w` is a measurable function of `w`. -/
private lemma lep_meas_blockEmb (D N : ℕ) : Measurable (blockEmb D N) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun k => ?_
    exact measurable_const.mul ((measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))
  · refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun l => ?_
    by_cases h : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · simp only [h, ↓reduceIte]
      exact measurable_const.mul ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (measurable_snd.comp (measurable_pi_apply _))))
    · simp only [h, ↓reduceIte]
      exact measurable_const

/-- The map `(w, W) ↦ e^{-t/2} blockEmb w + √(1 - e^{-t}) W` of the law (4.3) [eq:eq_in_law_H]
is measurable. -/
private lemma lep_meas_phi (D N : ℕ) (t : ℝ) :
    Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2 :=
  (((lep_meas_blockEmb D N).comp measurable_fst).const_smul (Real.exp (-t / 2))).add
    (measurable_snd.const_smul (Real.sqrt (1 - Real.exp (-t))))

/-- The array of the entries of `wig (DN) c`, indexed by `Idx D N`, is a measurable function of
the coordinates `c`. -/
private lemma lep_meas_psi (D N : ℕ) :
    Measurable fun c : Coords (D * N) => Matrix.of.symm
      ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    lep_meas_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)

/-- The law of the entry `(i, j)` of `H_t` under `ouMatLaw`: the image of `blockLaw ⊗ gueLaw (DN)`
under `e^{-t/2} (blockH w)_{ij} + √(1 - e^{-t}) (wig (DN) W)_{(fPFE i, fPFE j)}`. -/
private lemma lep_entry_law (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N) :
    (ouMatLaw D N L t).map (fun h => h i j) =
      ((blockLaw D N L).prod (gueLaw (D * N))).map fun ω =>
        ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 i j +
          ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
            wig (D * N) ω.2 (finProdFinEquiv i) (finProdFinEquiv j) := by
  have hev : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  unfold ouMatLaw ouLaw
  rw [Measure.map_map (lep_meas_psi D N) (lep_meas_phi D N t),
    Measure.map_map hev ((lep_meas_psi D N).comp (lep_meas_phi D N t))]
  congr 1
  funext ω
  change wig (D * N) (Real.exp (-t / 2) • blockEmb D N ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2)
      (finProdFinEquiv i) (finProdFinEquiv j) = _
  rw [wig_add, wig_smul, wig_smul]
  have h := congrFun (congrFun (wig_blockEmb D N ω.1) i) j
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h]

/-- The array coordinate `W.2 k l` of the GUE has law `cGauss`. -/
private lemma lep_mp_gue (n : ℕ) (k l : Fin n) :
    MeasurePreserving (fun W : Coords n => W.2 k l) (gueLaw n) (cGauss : Measure ℂ) := by
  unfold gueLaw
  have h4 : MeasurePreserving (fun z : Fin n → ℂ => z l)
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) (cGauss : Measure ℂ) :=
    measurePreserving_eval (fun _ : Fin n => (cGauss : Measure ℂ)) l
  have h3 : MeasurePreserving (fun z : Fin n → Fin n → ℂ => z k)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) :=
    measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) k
  exact h4.comp (h3.comp measurePreserving_snd)

/-- The array coordinate `(w c).2 k l` of the blocks has the law `νo`. -/
private lemma lep_mp_block (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (c : Fin D) (k l : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w c).2 k l) (blockLaw D N L)
      (L.νo : Measure ℂ) := by
  have h1 : MeasurePreserving (fun w : Fin D → Coords N => w c) (blockLaw D N L)
      (coordLaw N L) := by
    unfold blockLaw
    have : IsProbabilityMeasure (coordLaw N L) := by unfold coordLaw; infer_instance
    exact measurePreserving_eval (fun _ : Fin D => coordLaw N L) c
  have h2 : MeasurePreserving (Prod.snd : Coords N → Fin N → Fin N → ℂ) (coordLaw N L)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) := by
    unfold coordLaw
    exact measurePreserving_snd
  have h3 := measurePreserving_eval
    (fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) k
  have h4 := measurePreserving_eval (fun _ : Fin N => (L.νo : Measure ℂ)) l
  exact h4.comp (h3.comp (h2.comp h1))

/-- An entry of `wig n c` above the diagonal is `n^{-1/2}` times the array coordinate. -/
private lemma lep_wig_upper (n : ℕ) (c : Coords n) (k l : Fin n) (h : k < l) :
    wig n c k l = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * c.2 k l := by
  simp [wig, h.ne, h]

/-- The scalar of the block part of the entry `(i, j)`: `e^{-t/2} N^{-1/2}` in one block, else
`0`. -/
private def lepA (D N : ℕ) (t : ℝ) (i j : Idx D N) : ℝ :=
  if i.1 = j.1 then Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) else 0

/-- The scalar of the GUE part of an entry: `√(1 - e^{-t}) (DN)^{-1/2}`. -/
private def lepB (D N : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-t)) * ((D * N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

/-- The entry `(i, j)` of `Θ ω` for `(i, j)` above the diagonal. -/
private def lepF (D N : ℕ) (t : ℝ) (i j : Idx D N)
    (ω : (Fin D → Coords N) × Coords (D * N)) : ℂ :=
  ((lepA D N t i j : ℝ) : ℂ) * (ω.1 i.1).2 i.2 j.2 +
    ((lepB D N t : ℝ) : ℂ) * ω.2.2 (finProdFinEquiv i) (finProdFinEquiv j)

/-- `lepF` is measurable. -/
private lemma lep_meas_F (D N : ℕ) (t : ℝ) (i j : Idx D N) : Measurable (lepF D N t i j) := by
  unfold lepF
  refine (Measurable.const_mul ?_ _).add (Measurable.const_mul ?_ _)
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)))
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp measurable_snd))

/-- For `(i, j)` above the diagonal of `Fin (DN)`, the entry `(i, j)` of `H_t` of (4.1) [defVt]
is `lepF`. -/
private lemma lep_E_upper (D N : ℕ) (t : ℝ) (i j : Idx D N)
    (hkl : finProdFinEquiv i < finProdFinEquiv j) (ω : (Fin D → Coords N) × Coords (D * N)) :
    ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 i j +
      ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
        wig (D * N) ω.2 (finProdFinEquiv i) (finProdFinEquiv j) = lepF D N t i j ω := by
  rw [lep_wig_upper _ _ _ _ hkl]
  unfold lepF lepA lepB
  by_cases h : i.1 = j.1
  · have hij : i.2 < j.2 := by
      have h1 : (i.1 : ℕ) = j.1 := by rw [h]
      have h2 : (finProdFinEquiv i : ℕ) < finProdFinEquiv j := hkl
      simp only [finProdFinEquiv_apply_val] at h2
      rw [h1] at h2
      omega
    simp only [blockH, h, ite_true]
    rw [lep_wig_upper _ _ _ _ hij]
    push_cast
    ring
  · simp [blockH, h]
    ring

/-- The law of an entry above the diagonal is the image of the product law under `lepF`. -/
private lemma lep_entry_upper (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N)
    (hkl : finProdFinEquiv i < finProdFinEquiv j) :
    (ouMatLaw D N L t).map (fun h => h i j) =
      ((blockLaw D N L).prod (gueLaw (D * N))).map (lepF D N t i j) := by
  rw [lep_entry_law]
  congr 1
  funext ω
  exact lep_E_upper D N t i j hkl ω

/-- `wig n c` is Hermitian. -/
private lemma lep_wig_star (n : ℕ) (c : Coords n) (k l : Fin n) :
    star (wig n c l k) = wig n c k l := by
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy k l with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- `blockH D N w` is Hermitian. -/
private lemma lep_blockH_star (D N : ℕ) (w : Fin D → Coords N) (i j : Idx D N) :
    star (blockH D N w j i) = blockH D N w i j := by
  by_cases h : i.1 = j.1
  · have h' : j.1 = i.1 := h.symm
    simp only [blockH, h', ↓reduceIte]
    exact lep_wig_star N (w i.1) i.2 j.2
  · have h' : ¬ j.1 = i.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- The law of an entry below the diagonal is the conjugate of the law of the transposed entry. -/
private lemma lep_entry_lower (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N)
    (hlk : finProdFinEquiv j < finProdFinEquiv i) :
    (ouMatLaw D N L t).map (fun h => h i j) =
      ((ouMatLaw D N L t).map (fun h => h j i)).map (starRingEnd ℂ) := by
  rw [lep_entry_upper D N L t j i hlk, lep_entry_law,
    Measure.map_map Complex.continuous_conj.measurable (lep_meas_F D N t j i)]
  congr 1
  funext ω
  rw [Function.comp_apply, ← lep_E_upper D N t j i hlk ω]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  have h1 := lep_blockH_star D N ω.1 i j
  have h2 := lep_wig_star (D * N) ω.2 (finProdFinEquiv i) (finProdFinEquiv j)
  simp only [Complex.star_def] at h1 h2
  rw [h1, h2]

/-- The cumulants of an entry above the diagonal, for `p + q ≥ 1`: the independent sum of a
multiple of `νo` (in one block) and a multiple of `cGauss`. -/
private lemma lep_ccum_upper (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N)
    (hkl : finProdFinEquiv i < finProdFinEquiv j) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ccum ((ouMatLaw D N L t).map fun h => h i j) p q =
      ((lepA D N t i j : ℝ) : ℂ) ^ (p + q) * ccum (L.νo : Measure ℂ) p q +
        ((lepB D N t : ℝ) : ℂ) ^ (p + q) * ccum (cGauss : Measure ℂ) p q := by
  have := blockLaw_isProbabilityMeasure D N L
  have := gueLaw_isProbabilityMeasure (D * N)
  rw [lep_entry_upper D N L t i j hkl]
  have e1 := (lep_mp_block D N L i.1 i.2 j.2).map_eq
  have e2 := (lep_mp_gue (D * N) (finProdFinEquiv i) (finProdFinEquiv j)).map_eq
  have hf : Measurable fun w : Fin D → Coords N => (w i.1).2 i.2 j.2 :=
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp (measurable_pi_apply _)))
  have hg : Measurable fun W : Coords (D * N) => W.2 (finProdFinEquiv i) (finProdFinEquiv j) :=
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
  have := lep_sum_law (blockLaw D N L) (gueLaw (D * N)) _ _ hf hg
    (fun k => by rw [e1]; exact L.into k) (fun k => by rw [e2]; exact lep_cGauss_int k)
    (lepA D N t i j) (lepB D N t) p q hpq
  rw [e1, e2] at this
  exact this

/-- `𝒞^{(2,2)}(νo)` is real: it equals `E|z|⁴ - 2`. -/
private lemma lep_ccum_22_real {C : ℕ → ℝ} (L : EntryLaws C) :
    starRingEnd ℂ (ccum (L.νo : Measure ℂ) 2 2) = ccum (L.νo : Measure ℂ) 2 2 := by
  have h := moment_ccum_recursion (L.νo : Measure ℂ) L.into 2 1
  obtain ⟨-, c01, c11, -, c02, -, -, -⟩ := ccum_entry_low L
  have hmo : ∫ z, z ∂(L.νo : Measure ℂ) = 0 := L.meano
  have hmoc : ∫ z, starRingEnd ℂ z ∂(L.νo : Measure ℂ) = 0 := by
    rw [integral_conj, L.meano, map_zero]
  have hvo : ∫ z, z * starRingEnd ℂ z ∂(L.νo : Measure ℂ) = 1 := by
    have : (fun z : ℂ => z * starRingEnd ℂ z) = fun z => ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      funext z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, integral_complex_ofReal, L.varo]
    simp
  have h22 : ∫ z, z ^ 2 * starRingEnd ℂ z ^ (1 + 1) ∂(L.νo : Measure ℂ) =
      ((∫ z, ‖z‖ ^ 4 ∂(L.νo : Measure ℂ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext z
    have h2 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h4 : ((‖z‖ ^ 4 : ℝ) : ℂ) = ((‖z‖ : ℂ) ^ 2) ^ 2 := by push_cast; ring
    rw [h4, h2]
    ring
  rw [h22] at h
  norm_num [Finset.sum_range_succ, Nat.choose, c01, c02, c11, hmo, hmoc, hvo] at h
  have hc : ccum (L.νo : Measure ℂ) 2 2 =
      ((∫ z, ‖z‖ ^ 4 ∂(L.νo : Measure ℂ) : ℝ) : ℂ) - 2 := by linear_combination -h
  rw [hc, map_sub, Complex.conj_ofReal, map_ofNat]

/-- `(e^{-t/2} N^{-1/2})^4 = e^{-2t} / N²`. -/
private lemma lep_scale4 (N : ℕ) (t : ℝ) :
    (Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 4 = Real.exp (-(2 * t)) / (N : ℝ) ^ 2 := by
  have h1 : Real.exp (-t / 2) ^ 4 = Real.exp (-(2 * t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 4 = ((N : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      show (-(1 / 2 : ℝ)) * ((4 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]
  rw [mul_pow, h1, h2, div_eq_mul_inv]

/-- The entry cumulants of the law (4.3) [eq:eq_in_law_H] of `H_t` of (4.1) [defVt]: an entry
`h_{ij}` with `i, j` in different blocks has `𝒞^{(p,q)}(h_{ij}) = 0` for `p + q ≥ 3`; an
off-diagonal entry in one block has `𝒞^{(2,2)}(h_{ij}) = e^{-2t} N^{-2} 𝒞^{(2,2)}(νo)`, the
normalized `κ^{(2,2)}` of Lemma 3.14 [lem:fourthcumu1] times `e^{-2t}`. -/
theorem ouMatLaw_ccum (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N) :
    (i.1 ≠ j.1 → ∀ p q : ℕ, 3 ≤ p + q →
      ccum ((ouMatLaw D N L t).map fun h => h i j) p q = 0) ∧
    (i.1 = j.1 → i ≠ j → ccum ((ouMatLaw D N L t).map fun h => h i j) 2 2 =
      ((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2) := by
  refine ⟨fun h p q hpq => ?_, fun h hij => ?_⟩
  · have hne : finProdFinEquiv i ≠ finProdFinEquiv j := fun e =>
      h (by rw [finProdFinEquiv.injective e])
    have hX : ∀ x y : Idx D N, x.1 ≠ y.1 → finProdFinEquiv x < finProdFinEquiv y →
        ccum ((ouMatLaw D N L t).map fun h => h x y) p q = 0 := by
      intro x y hxy hlt
      have hA : lepA D N t x y = 0 := by simp [lepA, hxy]
      have hnp : ¬ (p = 1 ∧ q = 1) := by omega
      rw [lep_ccum_upper D N L t x y hlt p q (by omega), hA, ccum_cGauss p q (by omega)]
      simp only [hnp, ite_false, mul_zero, add_zero, Complex.ofReal_zero]
      rw [zero_pow (by omega), zero_mul]
    rcases lt_trichotomy (finProdFinEquiv i) (finProdFinEquiv j) with hlt | heq | hgt
    · exact hX i j h hlt
    · exact absurd heq hne
    · rw [lep_entry_lower D N L t i j hgt, lep_ccum_map_conj, hX j i h.symm hgt, map_zero]
  · have hne : finProdFinEquiv i ≠ finProdFinEquiv j := fun e =>
      hij (finProdFinEquiv.injective e)
    have hA : lepA D N t i j = Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simp [lepA, h]
    have hA' : lepA D N t j i = Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simp [lepA, h.symm]
    have hup : ∀ x y : Idx D N, lepA D N t x y = Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) →
        finProdFinEquiv x < finProdFinEquiv y →
        ccum ((ouMatLaw D N L t).map fun h => h x y) 2 2 =
          ((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 := by
      intro x y hx hlt
      rw [lep_ccum_upper D N L t x y hlt 2 2 (by norm_num), hx, ccum_cGauss 2 2 (by norm_num)]
      have : ((Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ (2 + 2) =
          ((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) := by
        rw [← lep_scale4 N t]
        push_cast
        ring
      rw [this]
      simp
    rcases lt_trichotomy (finProdFinEquiv i) (finProdFinEquiv j) with hlt | heq | hgt
    · exact hup i j hA hlt
    · exact absurd heq hne
    · rw [lep_entry_lower D N L t i j hgt, lep_ccum_map_conj, hup j i hA' hgt, map_mul,
        lep_ccum_22_real L, Complex.conj_ofReal]

/-- The elementary real inequality that closes the bound of the cancellation after (3.46)
[estimate_1_minus_abs_m_2]. -/
private lemma lep_real_final (r E w C₁ s : ℝ) (hr0 : 0 ≤ r) (hE0 : 0 ≤ E) (hw0 : 0 ≤ w)
    (hC₁ : 0 ≤ C₁) (hs : 1 ≤ s) (hws : w ≤ C₁ * s) :
    (3 * r + 2 * E) * (w * w) + 2 * E * w + 2 * E * w + r * (5 + w) ≤
      (5 + 4 * C₁ + 3 * C₁ ^ 2) * ((r + E) * s ^ 2) := by
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ≤ s ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hs0 hs
  have hw1 : w ≤ C₁ * s ^ 2 := hws.trans (mul_le_mul_of_nonneg_left hs2 hC₁)
  have hww : w * w ≤ C₁ ^ 2 * s ^ 2 := by
    have := mul_le_mul hws hws hw0 (mul_nonneg hC₁ hs0)
    nlinarith
  have h1 : (3 * r + 2 * E) * (w * w) ≤ (3 * r + 2 * E) * (C₁ ^ 2 * s ^ 2) :=
    mul_le_mul_of_nonneg_left hww (by positivity)
  have h2 : 4 * E * w ≤ 4 * E * (C₁ * s ^ 2) := mul_le_mul_of_nonneg_left hw1 (by positivity)
  have h3 : r * (5 + w) ≤ r * (5 * s ^ 2 + C₁ * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hr0
    have : (1 : ℝ) ≤ s ^ 2 := by nlinarith
    nlinarith
  have h4 : (3 * r + 2 * E) * (C₁ ^ 2 * s ^ 2) + 4 * E * (C₁ * s ^ 2) +
      r * (5 * s ^ 2 + C₁ * s ^ 2) + s ^ 2 * (3 * r * C₁ + E * (5 + C₁ ^ 2)) =
      (5 + 4 * C₁ + 3 * C₁ ^ 2) * ((r + E) * s ^ 2) := by ring
  have h5 : 0 ≤ s ^ 2 * (3 * r * C₁ + E * (5 + C₁ ^ 2)) := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The algebra of the cancellation after (3.46) [estimate_1_minus_abs_m_2] for numbers. -/
private lemma lep_alg (m a b : ℂ) (r E w C₁ y : ℝ)
    (hr : ‖m‖ ^ 2 = 1 - r) (hm1 : ‖m‖ ≤ 1) (hy : 0 < y) (hym : y ≤ ‖m‖)
    (hE0 : 0 ≤ E) (ha : ‖a - m ^ 2‖ ≤ E) (hb : ‖b - star m ^ 2‖ ≤ E)
    (hu : 1 - a ≠ 0) (hv : 1 - b ≠ 0) (hw : ‖1 - a‖⁻¹ ≤ w) (hw' : ‖1 - b‖⁻¹ ≤ w)
    (hC₁ : 0 ≤ C₁) (hwy : w ≤ C₁ / y) :
    ‖star m ^ 4 + ((‖m‖ ^ 4 : ℝ) : ℂ) + ((‖m‖ ^ 2 : ℝ) : ℂ) * m ^ 2 +
        ((‖m‖ ^ 2 : ℝ) : ℂ) * star m ^ 2 + m ^ 4 * ((‖m‖ ^ 2 : ℝ) : ℂ) / (1 - a) +
        star m ^ 6 / (1 - b)‖ ≤ (5 + 4 * C₁ + 3 * C₁ ^ 2) * ((r + E) / y ^ 2) := by
  set mb : ℂ := star m with hmb
  have hmbn : ‖mb‖ = ‖m‖ := norm_star m
  have hm0 : 0 ≤ ‖m‖ := norm_nonneg m
  have hr0 : 0 ≤ r := by nlinarith
  have hr1 : r ≤ 1 := by nlinarith
  have hρ : m * mb = 1 - (r : ℂ) := by
    have h1 : m * mb = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
      rw [hmb, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, hr]
    push_cast
    ring
  have hc2 : ((‖m‖ ^ 2 : ℝ) : ℂ) = 1 - (r : ℂ) := by rw [hr]; push_cast; ring
  have hc4 : ((‖m‖ ^ 4 : ℝ) : ℂ) = (1 - (r : ℂ)) ^ 2 := by
    rw [← hc2]; push_cast; ring
  set e₁ : ℂ := a - m ^ 2 with he₁
  set e₂ : ℂ := b - mb ^ 2 with he₂
  have key : mb ^ 4 + ((‖m‖ ^ 4 : ℝ) : ℂ) + ((‖m‖ ^ 2 : ℝ) : ℂ) * m ^ 2 +
        ((‖m‖ ^ 2 : ℝ) : ℂ) * mb ^ 2 + m ^ 4 * ((‖m‖ ^ 2 : ℝ) : ℂ) / (1 - a) +
        mb ^ 6 / (1 - b) =
      ((r : ℂ) * (2 - r) - e₂ - mb ^ 2 * e₁) / ((1 - a) * (1 - b)) -
        (1 + m ^ 2) * e₁ / (1 - a) - mb ^ 2 * (1 + mb ^ 2) * e₂ / (1 - b) +
        (-2 * r + r ^ 2 - r * m ^ 2 - r * mb ^ 2 - r * m ^ 4 / (1 - a)) := by
    rw [hc2, hc4, he₁, he₂]
    have hr' : (r : ℂ) = 1 - m * mb := by rw [hρ]; ring
    rw [hr']
    field_simp
    ring
  rw [key]
  -- the numerical bounds
  have hw0 : 0 ≤ w := (inv_nonneg.mpr (norm_nonneg _)).trans hw
  have hs : 1 ≤ 1 / y := by
    rw [le_div_iff₀ hy]; linarith
  have hws : w ≤ C₁ * (1 / y) := by rw [mul_one_div]; exact hwy
  have hdiv : ∀ (x u : ℂ) (W : ℝ), ‖u‖⁻¹ ≤ W → ‖x / u‖ ≤ ‖x‖ * W := by
    intro x u W hu'
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
  have hmb1 : ‖mb‖ ≤ 1 := hmbn ▸ hm1
  have hrc : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0]
  have hN : ‖(r : ℂ) * (2 - r) - e₂ - mb ^ 2 * e₁‖ ≤ 3 * r + 2 * E := by
    have h1 : ‖(2 : ℂ) - r‖ ≤ 3 := by
      calc ‖(2 : ℂ) - r‖ ≤ ‖(2 : ℂ)‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
        _ ≤ 3 := by rw [hrc]; norm_num; linarith
    have h2 : ‖mb ^ 2 * e₁‖ ≤ E := by
      rw [norm_mul, norm_pow]
      have : ‖mb‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg mb]
      calc ‖mb‖ ^ 2 * ‖e₁‖ ≤ 1 * E := mul_le_mul this ha (norm_nonneg _) zero_le_one
        _ = E := one_mul E
    calc ‖(r : ℂ) * (2 - r) - e₂ - mb ^ 2 * e₁‖
        ≤ ‖(r : ℂ) * (2 - r)‖ + ‖e₂‖ + ‖mb ^ 2 * e₁‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ r * 3 + E + E := by
          gcongr
          rw [norm_mul, hrc]
          exact mul_le_mul_of_nonneg_left h1 hr0
      _ = 3 * r + 2 * E := by ring
  have T1 : ‖((r : ℂ) * (2 - r) - e₂ - mb ^ 2 * e₁) / ((1 - a) * (1 - b))‖ ≤
      (3 * r + 2 * E) * (w * w) := by
    refine (hdiv _ _ (w * w) ?_).trans ?_
    · rw [norm_mul, mul_inv]; exact mul_le_mul hw hw' (by positivity) hw0
    · have : 0 ≤ w * w := mul_nonneg hw0 hw0
      nlinarith
  have T2 : ‖(1 + m ^ 2) * e₁ / (1 - a)‖ ≤ 2 * E * w := by
    refine (hdiv _ _ w hw).trans ?_
    have h1 : ‖(1 : ℂ) + m ^ 2‖ ≤ 2 := by
      calc ‖(1 : ℂ) + m ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖m ^ 2‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one, norm_pow]; nlinarith
    rw [norm_mul]
    have : ‖(1 : ℂ) + m ^ 2‖ * ‖e₁‖ ≤ 2 * E := mul_le_mul h1 ha (norm_nonneg _) (by norm_num)
    nlinarith
  have T3 : ‖mb ^ 2 * (1 + mb ^ 2) * e₂ / (1 - b)‖ ≤ 2 * E * w := by
    refine (hdiv _ _ w hw').trans ?_
    have h1 : ‖(1 : ℂ) + mb ^ 2‖ ≤ 2 := by
      calc ‖(1 : ℂ) + mb ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖mb ^ 2‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one, norm_pow]; nlinarith
    have h2 : ‖mb ^ 2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg mb]
    rw [norm_mul, norm_mul]
    have : ‖mb ^ 2‖ * ‖(1 : ℂ) + mb ^ 2‖ * ‖e₂‖ ≤ 1 * 2 * E :=
      mul_le_mul (mul_le_mul h2 h1 (norm_nonneg _) zero_le_one) hb (norm_nonneg _) (by norm_num)
    nlinarith
  have T4 : ‖-2 * (r : ℂ) + (r : ℂ) ^ 2 - (r : ℂ) * m ^ 2 - (r : ℂ) * mb ^ 2 -
      (r : ℂ) * m ^ 4 / (1 - a)‖ ≤ r * (5 + w) := by
    have h5 : ‖(r : ℂ) * m ^ 4 / (1 - a)‖ ≤ r * w := by
      refine (hdiv _ _ w hw).trans ?_
      rw [norm_mul, hrc, norm_pow]
      have : ‖m‖ ^ 4 ≤ 1 := pow_le_one₀ hm0 hm1
      have := mul_le_mul_of_nonneg_left this hr0
      nlinarith
    have h1 : ‖-2 * (r : ℂ)‖ ≤ 2 * r := by
      rw [norm_mul, hrc]; norm_num
    have h2 : ‖(r : ℂ) ^ 2‖ ≤ r := by
      rw [norm_pow, hrc]; nlinarith
    have h3 : ‖(r : ℂ) * m ^ 2‖ ≤ r := by
      rw [norm_mul, hrc, norm_pow]
      have : ‖m‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have h4 : ‖(r : ℂ) * mb ^ 2‖ ≤ r := by
      rw [norm_mul, hrc, norm_pow]
      have : ‖mb‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg mb]
      nlinarith
    calc _ ≤ ‖-2 * (r : ℂ)‖ + ‖(r : ℂ) ^ 2‖ + ‖(r : ℂ) * m ^ 2‖ + ‖(r : ℂ) * mb ^ 2‖ +
          ‖(r : ℂ) * m ^ 4 / (1 - a)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 2 * r + r + r + r + r * w := by gcongr
      _ = r * (5 + w) := by ring
  have hsum : ‖((r : ℂ) * (2 - r) - e₂ - mb ^ 2 * e₁) / ((1 - a) * (1 - b)) -
        (1 + m ^ 2) * e₁ / (1 - a) - mb ^ 2 * (1 + mb ^ 2) * e₂ / (1 - b) +
        (-2 * r + r ^ 2 - r * m ^ 2 - r * mb ^ 2 - r * m ^ 4 / (1 - a))‖ ≤
      (3 * r + 2 * E) * (w * w) + 2 * E * w + 2 * E * w + r * (5 + w) := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add T1 T2)) T3)) T4
  refine hsum.trans ?_
  have hys : (r + E) / y ^ 2 = (r + E) * (1 / y) ^ 2 := by field_simp
  rw [hys]
  exact lep_real_final r E w C₁ (1 / y) hr0 hE0 hw0 hC₁ hs hws

section Tools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operator norm is the `L²` operator norm of matrices. -/
private lemma lep_opNorm_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

/-- `‖A B‖ ≤ ‖A‖ ‖B‖`. -/
private lemma lep_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [lep_opNorm_eq] using norm_mul_le A B

/-- `|A_{ij}| ≤ ‖A‖`. -/
private lemma lep_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  have h3 : ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := by
    simp
  rw [h3] at h2
  exact h2.trans h

/-- `|⟨A⟩| ≤ ‖A‖`. -/
private lemma lep_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => lep_entry_le A i i
    _ = _ := by simp

/-- `⟨Λ²⟩ ≤ ‖Λ‖²`. -/
private lemma lep_avgSq_le [Nonempty ι] (Λ : Matrix ι ι ℂ) : avgSq Λ ≤ opNorm Λ ^ 2 := by
  unfold avgSq
  calc (ntr (Λ * Λ)).re ≤ ‖ntr (Λ * Λ)‖ := Complex.re_le_norm _
    _ ≤ opNorm (Λ * Λ) := lep_ntr_le _
    _ ≤ opNorm Λ * opNorm Λ := lep_op_mul _ _
    _ = _ := by ring

end Tools

/-- The interaction `Λ` has `⟨Λ⟩ = 0`: its diagonal vanishes. -/
private lemma lep_ntr_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ntr (lam D N A) = 0 := by
  have hf : ∀ a : Fin D, ¬ fwd D a a := fun a => by unfold fwd; omega
  have h : ∀ p : Idx D N, lam D N A p p = 0 := fun p => by simp [lam, hf]
  simp [ntr, Matrix.trace, Matrix.diag, h]

/-- The thresholds `N₀` of the rows B1 and B2 of the cancellation. -/
private lemma lep_N0 (δA C₂ : ℝ) (hδA : 0 < δA) (hC₂ : 0 < C₂) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → 1 ≤ N ∧ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 ∧
      4 * C₂ * ((N : ℝ) ^ (-δA)) ^ 2 ≤ (N : ℝ) ^ (-(δA / 2)) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-(3 * δA / 2))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have e1 := h1.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 20 by norm_num))
  have e2 := h2.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / (4 * C₂) by positivity))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (Filter.eventually_ge_atTop 1)))
  refine ⟨N₂, fun N hN => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hN₂ N hN
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr b3
  have b1' : (N : ℝ) ^ (-δA) ≤ 1 / 20 := b1
  have b2' : (N : ℝ) ^ (-(3 * δA / 2)) ≤ 1 / (4 * C₂) := b2
  refine ⟨b3, by linarith, ?_⟩
  have hNpos : (0 : ℝ) < N := by linarith
  have e : ((N : ℝ) ^ (-δA)) ^ 2 =
      (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(3 * δA / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  rw [e]
  have hp : 0 < (N : ℝ) ^ (-(δA / 2)) := Real.rpow_pos_of_pos hNpos _
  have : 4 * C₂ * (N : ℝ) ^ (-(3 * δA / 2)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left b2' (show (0 : ℝ) ≤ 4 * C₂ by positivity)
    rwa [mul_one_div_cancel (by positivity)] at this
  nlinarith

/-- The cancellation after (3.46) [estimate_1_minus_abs_m_2] in the proof of Lemma 3.7
[lemma_G_large_2]: for `η / Im m ∈ [c⁻¹ N^{-ε_g}, c N^{-ε_g}]`, `ε_g < δ_A/4`, the bracket of
(3.45) [pre_cancellation], `m̄⁴ + |m|⁴ + |m|²m² + |m|²m̄² + m⁴|m|²/(1 - ⟨M²⟩) + m̄⁶/(1 - ⟨(M^*)²⟩)`,
is at most `K (η (Im m)⁻³ + N^{-δ_A/2} (Im m)⁻²)`, with `1 - ⟨M²⟩ ≠ 0 ≠ 1 - ⟨(M^*)²⟩`. -/
theorem bracket_cancel (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
        1 - ntr (MExt (lam D N A) z * MExt (lam D N A) z) ≠ 0 ∧
        1 - ntr ((MExt (lam D N A) z)ᴴ * (MExt (lam D N A) z)ᴴ) ≠ 0 ∧
        ‖star (mExt (lam D N A) z) ^ 4 + ((‖mExt (lam D N A) z‖ ^ 4 : ℝ) : ℂ) +
            ((‖mExt (lam D N A) z‖ ^ 2 : ℝ) : ℂ) * mExt (lam D N A) z ^ 2 +
            ((‖mExt (lam D N A) z‖ ^ 2 : ℝ) : ℂ) * star (mExt (lam D N A) z) ^ 2 +
            mExt (lam D N A) z ^ 4 * ((‖mExt (lam D N A) z‖ ^ 2 : ℝ) : ℂ) /
              (1 - ntr (MExt (lam D N A) z * MExt (lam D N A) z)) +
            star (mExt (lam D N A) z) ^ 6 /
              (1 - ntr ((MExt (lam D N A) z)ᴴ * (MExt (lam D N A) z)ᴴ))‖ ≤
          K * (z.im * ((mExt (lam D N A) z).im ^ 3)⁻¹ +
            (N : ℝ) ^ (-(δA / 2)) * ((mExt (lam D N A) z).im ^ 2)⁻¹) := by
  obtain ⟨C₂, hC₂, hrep⟩ := estimate_replace_M_by_m τ hτ 2
  have hc0 : 0 < c⁻¹ := inv_pos.mpr (by linarith)
  have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  obtain ⟨C₁, hC₁, N₁, hN₁⟩ := one_minus_Mhat_same D hD δA εg c⁻¹ τ hδA hεg hεg' hc0 hc1 hτ
  obtain ⟨N₂, hN₂⟩ := lep_N0 δA C₂ hδA hC₂
  refine ⟨2 * (5 + 4 * C₁ + 3 * C₁ ^ 2), by positivity, max N₁ N₂,
    fun N hN A hA z hzs hz hw1 hw2 => ?_⟩
  obtain ⟨hz1, -⟩ := hzs
  obtain ⟨hNge, hB1, hB2⟩ := hN₂ N (le_trans (le_max_right _ _) hN)
  have hND : NeZero D := ⟨by omega⟩
  have hNN : NeZero N := ⟨by omega⟩
  have hne : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hopΛ : opNorm (lam D N A) ≤ 2 * (N : ℝ) ^ (-δA) := by
    have := opNorm_lam_le D N A
    linarith
  have hop : opNorm (lam D N A) ≤ 1 / 10 := hopΛ.trans hB1
  have htr := lep_ntr_lam D N A
  have hmx : mExt (lam D N A) z = mSol (lam D N A) z := by simp [mExt, hz]
  have hMx : MExt (lam D N A) z = MSol (lam D N A) z := by simp [MExt, MSol, hmx]
  rw [hmx] at hw1 hw2
  rw [hmx, hMx]
  set Λ := lam D N A with hΛdef
  obtain ⟨hy, hmn, hMM⟩ := mSol_spec Λ hΛ z hz
  obtain ⟨-, hmlt, -⟩ := mSol_apriori Λ hΛ hop z hz
  set m := mSol Λ z with hm
  set y : ℝ := m.im with hydef
  have hym : y ≤ ‖m‖ := (le_abs_self _).trans (Complex.abs_im_le_norm m)
  have h20 := hrep (Idx D N) Λ hΛ hop htr z hz1 hz 2 0 le_rfl (Nat.zero_le _)
  have h02 := hrep (Idx D N) Λ hΛ hop htr z hz1 hz 0 2 (Nat.zero_le _) le_rfl
  have h11 := hrep (Idx D N) Λ hΛ hop htr z hz1 hz 1 1 (by norm_num) (by norm_num)
  set E : ℝ := C₂ * avgSq Λ with hEdef
  have ha : ‖ntr (MSol Λ z * MSol Λ z) - m ^ 2‖ ≤ E := by simpa [sq] using h20
  have hb : ‖ntr ((MSol Λ z)ᴴ * (MSol Λ z)ᴴ) - star m ^ 2‖ ≤ E := by simpa [sq] using h02
  have hE0 : 0 ≤ E := (norm_nonneg _).trans ha
  have hav : avgSq Λ ≤ 4 * ((N : ℝ) ^ (-δA)) ^ 2 := by
    refine (lep_avgSq_le Λ).trans ?_
    have h0 := (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) Λ))
    have h0' : 0 ≤ opNorm Λ := h0
    nlinarith
  have hEle : E ≤ (N : ℝ) ^ (-(δA / 2)) := by
    have := mul_le_mul_of_nonneg_left hav hC₂.le
    linarith
  -- the size of `1 - |m|²`
  obtain ⟨hnt, -⟩ := equation_z_im_m Λ hΛ z hz
  have hmm : m * star m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h11' : |y / (y + z.im) - ‖m‖ ^ 2| ≤ E := by
    have : ‖((y / (y + z.im) - ‖m‖ ^ 2 : ℝ) : ℂ)‖ ≤ E := by
      have e : ((y / (y + z.im) - ‖m‖ ^ 2 : ℝ) : ℂ) =
          ntr (MSol Λ z * (MSol Λ z)ᴴ) - m ^ 1 * star m ^ 1 := by
        rw [hnt, pow_one, pow_one, hmm]; push_cast; ring
      rw [e]
      simpa using h11
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  set r : ℝ := 1 - ‖m‖ ^ 2 with hrdef
  have hr : ‖m‖ ^ 2 = 1 - r := by rw [hrdef]; ring
  have hrle : r ≤ z.im / y + E := by
    have h1 := (abs_le.mp h11').2
    have h2 : 1 - y / (y + z.im) = z.im / (y + z.im) := by field_simp; ring
    have h3 : z.im / (y + z.im) ≤ z.im / y := by
      refine div_le_div_of_nonneg_left hz.le hy (by linarith)
    linarith
  -- the denominators
  have hw1' : c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mSol Λ z).im := hw1
  have hw2' : z.im / (mSol Λ z).im ≤ c⁻¹⁻¹ * (N : ℝ) ^ (-εg) := by rw [inv_inv]; exact hw2
  obtain ⟨-, hu, -, hub⟩ := hN₁ N (le_trans (le_max_left _ _) hN) A hA z hz1 hz hw1' hw2' z
    (Or.inl rfl)
  obtain ⟨-, hv, -, hvb⟩ := hN₁ N (le_trans (le_max_left _ _) hN) A hA z hz1 hz hw1' hw2'
    (star z) (Or.inr rfl)
  have hconj := (mExt_conj Λ hΛ z hz.ne').2
  rw [hconj, hMx] at hv hvb
  rw [hMx] at hu hub
  have hub' : ‖1 - ntr (MSol Λ z * MSol Λ z)‖⁻¹ ≤ C₁ / y := by
    refine hub.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hC₁.le
  have hvb' : ‖1 - ntr ((MSol Λ z)ᴴ * (MSol Λ z)ᴴ)‖⁻¹ ≤ C₁ / y := by
    refine hvb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hC₁.le
  refine ⟨hu, hv, ?_⟩
  have key := lep_alg m _ _ r E (C₁ / y) C₁ y hr hmlt.le hy hym hE0 ha hb hu hv hub' hvb'
    hC₁.le le_rfl
  refine key.trans ?_
  have hK : 0 ≤ 5 + 4 * C₁ + 3 * C₁ ^ 2 := by positivity
  have hmain : (r + E) / y ^ 2 ≤
      2 * (z.im * (y ^ 3)⁻¹ + (N : ℝ) ^ (-(δA / 2)) * (y ^ 2)⁻¹) := by
    have e : (z.im * (y ^ 3)⁻¹ + (N : ℝ) ^ (-(δA / 2)) * (y ^ 2)⁻¹) * y ^ 2 =
        z.im / y + (N : ℝ) ^ (-(δA / 2)) := by field_simp
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ z.im / y := by positivity
    nlinarith [e]
  calc (5 + 4 * C₁ + 3 * C₁ ^ 2) * ((r + E) / y ^ 2)
      ≤ (5 + 4 * C₁ + 3 * C₁ ^ 2) *
        (2 * (z.im * (y ^ 3)⁻¹ + (N : ℝ) ^ (-(δA / 2)) * (y ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hmain hK
    _ = _ := by ring

end RBMTransitionEdge

end
