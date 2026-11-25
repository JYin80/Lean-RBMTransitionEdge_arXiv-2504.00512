module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Prob.Cumulant

@[expose] public section

/-!
# Moment matching

The four-moment matching construction used before Lemma 3.12: a law `L₀` such that the OU flow of
(3.12) [eq:Ht] started at `L₀` matches the first three moments of the given entry laws at a fixed
time, with the fourth moment bounded.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge


/-- The mixed moment `E h^a h̄^b`. -/
def mixMom (μ : Measure ℂ) (a b : ℕ) : ℂ := ∫ z, z ^ a * starRingEnd ℂ z ^ b ∂μ

/-- The law of `√(1-s) h + √s g` with `g` standard complex Gaussian independent of `h ∼ ν`. -/
def mixLaw (s : ℝ) (ν : Measure ℂ) : Measure ℂ :=
  (ν.prod (cGauss : Measure ℂ)).map fun p => (Real.sqrt (1 - s) : ℂ) * p.1 + (Real.sqrt s : ℂ) * p.2

/-- The law of `√(1-s) x + √s g` with `g` standard real Gaussian independent of `x ∼ ν`. -/
def mixLawR (s : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  (ν.prod (gaussianReal 0 1)).map fun p => Real.sqrt (1 - s) * p.1 + Real.sqrt s * p.2

private def MomentMatch_atoms {ι E : Type*} [Fintype ι] [MeasurableSpace E] (w : ι → ℝ) (z : ι → E) :
    Measure E :=
  ∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k)

private lemma MomentMatch_atoms_integral {ι E F : Type*} [Fintype ι] [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k) (z : ι → E) (f : E → F) :
    ∫ x, f x ∂(MomentMatch_atoms w z) = ∑ k, w k • f (z k) := by
  unfold MomentMatch_atoms
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw k)]
  · exact fun k _ => (integrable_dirac (by simp)).smul_measure (by simp)

private lemma MomentMatch_atoms_prob {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (z : ι → E) :
    IsProbabilityMeasure (MomentMatch_atoms w z) := by
  refine ⟨?_⟩
  unfold MomentMatch_atoms
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hw k), hs]
  simp

private lemma MomentMatch_atoms_ae {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (w : ι → ℝ) (z : ι → E) (P : E → Prop) (hP : MeasurableSet {x | P x}) (hz : ∀ k, P (z k)) :
    ∀ᵐ x ∂(MomentMatch_atoms w z), P x := by
  rw [ae_iff]
  unfold MomentMatch_atoms
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show {a | ¬P a} = {x | P x}ᶜ from rfl, Measure.dirac_apply' _ hP.compl]
  simp [hz k]

/-- Mixed moments are integrable when all absolute moments are. -/
private lemma MomentMatch_integrable_mom {μ : Measure ℂ}
    (h : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ) (i j : ℕ) :
    Integrable (fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j) μ := by
  refine (h (i + j)).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp [norm_pow, pow_add]

/-- The law of `c x + d y` for independent `x ∼ μ₁`, `y ∼ μ₂`: the shape of (3.34) [Gcom_a]. -/
private def MomentMatch_conv (c d : ℂ) (μ₁ μ₂ : Measure ℂ) : Measure ℂ :=
  (μ₁.prod μ₂).map fun p => c * p.1 + d * p.2

/-- The mixed moments `E z^p z̄^q` of the independent sum `c x + d y`, expanded by the binomial
theorem and independence. -/
private lemma MomentMatch_conv_mom {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₁)
    (h₂ : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₂) (c d : ℂ) (p q : ℕ) :
    mixMom (MomentMatch_conv c d μ₁ μ₂) p q =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ((p.choose i : ℂ) * (q.choose j : ℂ) *
          (c ^ i * starRingEnd ℂ c ^ j * d ^ (p - i) * starRingEnd ℂ d ^ (q - j))) *
        (mixMom μ₁ i j * mixMom μ₂ (p - i) (q - j)) := by
  unfold mixMom MomentMatch_conv
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hexp : ∀ x : ℂ × ℂ, (c * x.1 + d * x.2) ^ p * starRingEnd ℂ (c * x.1 + d * x.2) ^ q =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ((p.choose i : ℂ) * (q.choose j : ℂ) *
          (c ^ i * starRingEnd ℂ c ^ j * d ^ (p - i) * starRingEnd ℂ d ^ (q - j))) *
        ((x.1 ^ i * starRingEnd ℂ x.1 ^ j) * (x.2 ^ (p - i) * starRingEnd ℂ x.2 ^ (q - j))) := by
    intro x
    rw [map_add, map_mul, map_mul, add_pow, add_pow, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j : ℕ, Integrable (fun x : ℂ × ℂ =>
      ((x.1 ^ i * starRingEnd ℂ x.1 ^ j) * (x.2 ^ (p - i) * starRingEnd ℂ x.2 ^ (q - j))))
      (μ₁.prod μ₂) := fun i j =>
    Integrable.mul_prod (f := fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j)
      (g := fun z : ℂ => z ^ (p - i) * starRingEnd ℂ z ^ (q - j))
      (MomentMatch_integrable_mom h₁ i j) (MomentMatch_integrable_mom h₂ (p - i) (q - j))
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_prod_mul (μ := μ₁) (ν := μ₂)
        (fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j)
        (fun z : ℂ => z ^ (p - i) * starRingEnd ℂ z ^ (q - j))]
    · exact (hint i j).const_mul _
  · exact integrable_finsetSum _ fun j _ => (hint i j).const_mul _

/-- Powers are integrable when all absolute moments are. -/
private lemma MomentMatch_integrable_pow {μ : Measure ℝ}
    (h : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) μ) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) μ := by
  refine (h k).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- The law of `c x + d y` for independent real `x ∼ μ₁`, `y ∼ μ₂`. -/
private def MomentMatch_convR (c d : ℝ) (μ₁ μ₂ : Measure ℝ) : Measure ℝ :=
  (μ₁.prod μ₂).map fun p => c * p.1 + d * p.2

/-- The moments `E z^k` of the independent real sum `c x + d y`, expanded by the binomial theorem
and independence. -/
private lemma MomentMatch_convR_mom {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) μ₁)
    (h₂ : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) μ₂) (c d : ℝ) (k : ℕ) :
    ∫ x, x ^ k ∂(MomentMatch_convR c d μ₁ μ₂) =
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * (c ^ i * d ^ (k - i))) *
        ((∫ x, x ^ i ∂μ₁) * ∫ x, x ^ (k - i) ∂μ₂) := by
  unfold MomentMatch_convR
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hexp : ∀ x : ℝ × ℝ, (c * x.1 + d * x.2) ^ k =
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * (c ^ i * d ^ (k - i))) *
        (x.1 ^ i * x.2 ^ (k - i)) := by
    intro x
    rw [add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : ∀ i : ℕ, Integrable (fun x : ℝ × ℝ => x.1 ^ i * x.2 ^ (k - i)) (μ₁.prod μ₂) :=
    fun i => Integrable.mul_prod (f := fun z : ℝ => z ^ i) (g := fun z : ℝ => z ^ (k - i))
      (MomentMatch_integrable_pow h₁ i) (MomentMatch_integrable_pow h₂ (k - i))
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_prod_mul (μ := μ₁) (ν := μ₂) (fun z : ℝ => z ^ i)
    (fun z : ℝ => z ^ (k - i))]

/-- For `2 a ^ 2 = 1`, `a (X + Y)` is `N(0, v)` for independent `N(0, v)` variables `X`, `Y`. -/
private lemma MomentMatch_gauss_rot (v : NNReal) (a : ℝ) (ha : a ^ 2 + a ^ 2 = 1) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map (fun p => a * p.1 + a * p.2) =
      gaussianReal 0 v := by
  set P := (gaussianReal 0 v).prod (gaussianReal 0 v) with hP
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) (gaussianReal 0 v) P :=
    ⟨measurable_fst.aemeasurable, by simp [P, Measure.map_fst_prod]⟩
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) (gaussianReal 0 v) P :=
    ⟨measurable_snd.aemeasurable, by simp [P, Measure.map_snd_prod]⟩
  have hX' := gaussianReal_const_mul hX a
  have hY' := gaussianReal_const_mul hY a
  have hind : IndepFun (fun p : ℝ × ℝ => a * p.1) (fun p : ℝ × ℝ => a * p.2) P :=
    indepFun_prod (X := fun x : ℝ => a * x) (Y := fun y : ℝ => a * y) (by fun_prop) (by fun_prop)
  have := gaussianReal_add_gaussianReal_of_indepFun hind hX' hY'
  have hv : (NNReal.mk (a ^ 2) (sq_nonneg _) * v + NNReal.mk (a ^ 2) (sq_nonneg _) * v) = v := by
    rw [← add_mul]
    have : NNReal.mk (a ^ 2) (sq_nonneg _) + NNReal.mk (a ^ 2) (sq_nonneg _) = 1 := by
      ext; simpa using ha
    rw [this, one_mul]
  rw [hv, mul_zero, add_zero] at this
  exact this

/-- All absolute moments of `N(0, v)` are finite. -/
private lemma MomentMatch_gauss_int (v : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := (memLp_id_gaussianReal (μ := 0) (v := v) (n : NNReal)).integrable_norm_pow
      (p := n) (by simpa using hn.ne')
    simpa using this

/-- The moments of orders `0` to `4` of `N(0, v)`. -/
private lemma MomentMatch_gauss_mom (v : NNReal) :
    ∫ x, x ∂(gaussianReal 0 v) = 0 ∧ ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v ∧
    ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 ∧ ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h1 : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  have h2 : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
    have := variance_eq_sub (μ := gaussianReal 0 v) (X := id) (memLp_id_gaussianReal 2)
    rw [variance_id_gaussianReal] at this
    simp only [Pi.pow_apply, id_eq] at this
    rw [h1] at this
    simpa using this.symm
  set a : ℝ := Real.sqrt (1 / 2) with ha
  have ha2 : a ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have ha1 : a < 1 := by nlinarith
  have hrot := MomentMatch_gauss_rot v a (by linarith)
  have key : ∀ k : ℕ, ∫ x, x ^ k ∂(gaussianReal 0 v) =
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * (a ^ i * a ^ (k - i))) *
        ((∫ x, x ^ i ∂(gaussianReal 0 v)) * ∫ x, x ^ (k - i) ∂(gaussianReal 0 v)) := by
    intro k
    have := MomentMatch_convR_mom (MomentMatch_gauss_int v) (MomentMatch_gauss_int v) a a k
    unfold MomentMatch_convR at this
    rw [hrot] at this
    exact this
  have h3 : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
    have k3 := key 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, h2] at k3
    norm_num at k3
    have : a ^ 3 = a * (1 / 2) := by
      calc a ^ 3 = a * a ^ 2 := by ring
        _ = a * (1 / 2) := by rw [ha2]
    set m3 := ∫ x, x ^ 3 ∂(gaussianReal 0 v)
    have hm : m3 * (1 - a) = 0 := by nlinarith
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · linarith
  have h4 : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
    have k4 := key 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, h2, h3] at k4
    norm_num at k4
    have : a ^ 4 = 1 / 4 := by nlinarith
    rw [this, ha2] at k4
    nlinarith [k4]
  exact ⟨h1, h2, h3, h4⟩

/-- The law `N(0, 1/2)` of the real and imaginary parts of the standard complex Gaussian
`cGauss`, seen as a measure on `ℂ`. -/
private def MomentMatch_halfC : Measure ℂ :=
  (gaussianReal 0 (1 / 2 : NNReal)).map fun x : ℝ => (x : ℂ)

private instance : IsProbabilityMeasure MomentMatch_halfC :=
  by unfold MomentMatch_halfC; infer_instance

/-- All absolute moments of `MomentMatch_halfC` are finite. -/
private lemma MomentMatch_halfC_int (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n) MomentMatch_halfC := by
  unfold MomentMatch_halfC
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def] using MomentMatch_gauss_int (1 / 2) n

/-- The mixed moments of `MomentMatch_halfC`. -/
private lemma MomentMatch_halfC_mom (i j : ℕ) :
    mixMom MomentMatch_halfC i j = ((∫ x, x ^ (i + j) ∂(gaussianReal 0 (1 / 2 : NNReal)) : ℝ) : ℂ) := by
  unfold mixMom MomentMatch_halfC
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.conj_ofReal, pow_add]

/-- The standard complex Gaussian is the law of `x + i y` for independent `x, y ∼ N(0, 1/2)`. -/
private lemma MomentMatch_cGauss_eq :
    (cGauss : Measure ℂ) = MomentMatch_conv 1 Complex.I MomentMatch_halfC MomentMatch_halfC := by
  unfold MomentMatch_conv MomentMatch_halfC
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  change ((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))).map
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) = _
  congr 1
  funext p
  simp [mul_comm]

/-- All absolute moments of `cGauss` are finite. -/
private lemma MomentMatch_cGauss_int (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n) (cGauss : Measure ℂ) := by
  rw [MomentMatch_cGauss_eq]
  unfold MomentMatch_conv
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have h := MomentMatch_halfC_int n
  have hg : Integrable (fun p : ℂ × ℂ => 2 ^ n * (‖p.1‖ ^ n + ‖p.2‖ ^ n))
      (MomentMatch_halfC.prod MomentMatch_halfC) :=
    ((h.comp_fst _).add (h.comp_snd _)).const_mul _
  refine hg.mono' (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
  have h1 : ‖(1 : ℂ) * p.1 + Complex.I * p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
    simpa using norm_add_le p.1 (Complex.I * p.2)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 n
  have h3 := add_pow_le (norm_nonneg p.1) (norm_nonneg p.2) n
  have h4 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  have h5 : 0 ≤ ‖p.1‖ ^ n + ‖p.2‖ ^ n := by positivity
  simp only [Function.comp_apply, norm_pow, norm_norm]
  nlinarith

/-- The mixed moments `E g^k ḡ^l` of `cGauss` for `k + l ≤ 4`: `E|g|² = 1`, `E|g|⁴ = 2`, and all
others vanish. -/
private lemma MomentMatch_cGauss_mom :
    mixMom cGauss 0 0 = 1 ∧ mixMom cGauss 1 0 = 0 ∧ mixMom cGauss 0 1 = 0 ∧
    mixMom cGauss 2 0 = 0 ∧ mixMom cGauss 1 1 = 1 ∧ mixMom cGauss 0 2 = 0 ∧
    mixMom cGauss 3 0 = 0 ∧ mixMom cGauss 2 1 = 0 ∧ mixMom cGauss 1 2 = 0 ∧
    mixMom cGauss 0 3 = 0 ∧ mixMom cGauss 4 0 = 0 ∧ mixMom cGauss 3 1 = 0 ∧
    mixMom cGauss 2 2 = 2 ∧ mixMom cGauss 1 3 = 0 ∧ mixMom cGauss 0 4 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := MomentMatch_gauss_mom (1 / 2)
  have key : ∀ k l : ℕ, mixMom cGauss k l =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        ((k.choose i : ℂ) * (l.choose j : ℂ) *
          ((1 : ℂ) ^ i * starRingEnd ℂ 1 ^ j * Complex.I ^ (k - i) *
            starRingEnd ℂ Complex.I ^ (l - j))) *
        (mixMom MomentMatch_halfC i j * mixMom MomentMatch_halfC (k - i) (l - j)) := by
    intro k l
    rw [MomentMatch_cGauss_eq]
    exact MomentMatch_conv_mom MomentMatch_halfC_int MomentMatch_halfC_int _ _ k l
  simp only [MomentMatch_halfC_mom] at key
  have h2' : ∫ x, x ^ 2 ∂(gaussianReal 0 (1 / 2 : NNReal)) = 1 / 2 := by
    rw [h2]; norm_num
  have h4' : ∫ x, x ^ 4 ∂(gaussianReal 0 (1 / 2 : NNReal)) = 3 / 4 := by
    rw [h4]; norm_num
  have h0 : (gaussianReal 0 (1 / 2 : NNReal)).real Set.univ = 1 := by simp
  generalize gaussianReal 0 (1 / 2 : NNReal) = G at h0 h1 h2' h3 h4' key
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [key] <;>
    simp [Finset.sum_range_succ, Nat.choose, h0, h1, h2', h3, h4'] <;> norm_num <;>
    linear_combination (-(3 / 4) * (Complex.I ^ 2 - 1) : ℂ) * Complex.I_sq

/-- A bounded perturbation `φ (x, w)` of `x ∼ ν` by an independent `w ∼ τ`, `‖w‖ ≤ R`, has finite
absolute moments, controlled by those of `ν`. -/
private lemma MomentMatch_pert {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {ν τ : Measure E} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure τ] (hν : ∀ n : ℕ, Integrable (fun x : E => ‖x‖ ^ n) ν) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : ∀ᵐ w ∂τ, ‖w‖ ≤ R) (φ : E × E → E) (hφ : Continuous φ)
    (hb : ∀ p : E × E, ‖φ p‖ ≤ ‖p.1‖ + ‖p.2‖) (n : ℕ) :
    Integrable (fun y : E => ‖y‖ ^ n) ((ν.prod τ).map φ) ∧
      ∫ y, ‖y‖ ^ n ∂((ν.prod τ).map φ) ≤ 2 ^ n * (∫ x, ‖x‖ ^ n ∂ν + R ^ n) := by
  have hg : Integrable (fun p : E × E => 2 ^ n * (‖p.1‖ ^ n + R ^ n)) (ν.prod τ) :=
    (((hν n).comp_fst τ).add (integrable_const _)).const_mul _
  have hae : ∀ᵐ p ∂(ν.prod τ), ‖φ p‖ ^ n ≤ 2 ^ n * (‖p.1‖ ^ n + R ^ n) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hR] with p hp
    have h1 : ‖φ p‖ ≤ ‖p.1‖ + R := (hb p).trans (by linarith [show ‖p.2‖ ≤ R from hp])
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 n
    have h3 := add_pow_le (norm_nonneg p.1) hR0 n
    have h4 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
    have h5 : 0 ≤ ‖p.1‖ ^ n + R ^ n := by positivity
    nlinarith
  have hint : Integrable (fun p : E × E => ‖φ p‖ ^ n) (ν.prod τ) :=
    hg.mono' (by have := hφ.aestronglyMeasurable (μ := ν.prod τ); fun_prop)
      (hae.mono fun p hp => by simpa [norm_pow] using hp)
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure (by fun_prop) hφ.measurable.aemeasurable]
    exact hint
  · rw [integral_map hφ.measurable.aemeasurable (by fun_prop)]
    refine (integral_mono_ae hint hg hae).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add ((hν n).comp_fst τ) (integrable_const _)]
    have h1 : ∫ p : E × E, ‖p.1‖ ^ n ∂(ν.prod τ) = ∫ x, ‖x‖ ^ n ∂ν := by
      have := integral_prod_mul (μ := ν) (ν := τ) (fun x : E => ‖x‖ ^ n) (fun _ : E => (1 : ℝ))
      simpa using this
    rw [h1]
    simp

/-- `r = √(d² + 4 s)`, the sum of the two atoms of the two-point law of variance `s` and
third moment `s d`. -/
private def MomentMatch_r (s d : ℝ) : ℝ := Real.sqrt (d ^ 2 + 4 * s)

/-- The atoms `p = (d + r)/2` and `-q = (d - r)/2` of the two-point law. -/
private def MomentMatch_tpAtom (s d : ℝ) : Fin 2 → ℝ :=
  ![(d + MomentMatch_r s d) / 2, (d - MomentMatch_r s d) / 2]

/-- The weights `q / (p + q)` and `p / (p + q)` of the two-point law. -/
private def MomentMatch_tpW (s d : ℝ) : Fin 2 → ℝ :=
  ![(MomentMatch_r s d - d) / (2 * MomentMatch_r s d),
    (MomentMatch_r s d + d) / (2 * MomentMatch_r s d)]

/-- The centred two-point law with variance `s` and third moment `s d`. -/
private def MomentMatch_twoPt (s d : ℝ) : Measure ℝ :=
  MomentMatch_atoms (MomentMatch_tpW s d) (MomentMatch_tpAtom s d)

private lemma MomentMatch_r_sq {s : ℝ} (hs : 0 < s) (d : ℝ) :
    MomentMatch_r s d ^ 2 = d ^ 2 + 4 * s :=
  Real.sq_sqrt (by positivity)

private lemma MomentMatch_r_abs {s : ℝ} (hs : 0 < s) (d : ℝ) : |d| ≤ MomentMatch_r s d :=
  Real.abs_le_sqrt (by nlinarith)

private lemma MomentMatch_r_pos {s : ℝ} (hs : 0 < s) (d : ℝ) : 0 < MomentMatch_r s d :=
  Real.sqrt_pos.mpr (by positivity)

private lemma MomentMatch_r_le {s : ℝ} (hs1 : s ≤ 1) (d : ℝ) :
    MomentMatch_r s d ≤ |d| + 2 := by
  unfold MomentMatch_r
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [sq_abs d, abs_nonneg d]

private lemma MomentMatch_tpW_nonneg {s : ℝ} (hs : 0 < s) (d : ℝ) (k : Fin 2) :
    0 ≤ MomentMatch_tpW s d k := by
  have h1 := MomentMatch_r_abs hs d
  have h2 := MomentMatch_r_pos hs d
  have h3 := abs_le.mp h1
  fin_cases k
  · change 0 ≤ (MomentMatch_r s d - d) / (2 * MomentMatch_r s d)
    exact div_nonneg (by linarith [h3.2]) (by positivity)
  · change 0 ≤ (MomentMatch_r s d + d) / (2 * MomentMatch_r s d)
    exact div_nonneg (by linarith [h3.1]) (by positivity)

private lemma MomentMatch_tpW_sum {s : ℝ} (hs : 0 < s) (d : ℝ) :
    ∑ k, MomentMatch_tpW s d k = 1 := by
  have h2 := MomentMatch_r_pos hs d
  simp only [Fin.sum_univ_two, MomentMatch_tpW]
  simp
  field_simp
  ring

private lemma MomentMatch_twoPt_prob {s : ℝ} (hs : 0 < s) (d : ℝ) :
    IsProbabilityMeasure (MomentMatch_twoPt s d) :=
  MomentMatch_atoms_prob _ (MomentMatch_tpW_nonneg hs d) (MomentMatch_tpW_sum hs d) _

/-- The integral against the two-point law is the weighted sum over its two atoms. -/
private lemma MomentMatch_twoPt_integral {s : ℝ} (hs : 0 < s) (d : ℝ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : ℝ → F) :
    ∫ x, f x ∂(MomentMatch_twoPt s d) =
      ((MomentMatch_r s d - d) / (2 * MomentMatch_r s d)) • f ((d + MomentMatch_r s d) / 2) +
      ((MomentMatch_r s d + d) / (2 * MomentMatch_r s d)) • f ((d - MomentMatch_r s d) / 2) := by
  unfold MomentMatch_twoPt
  rw [MomentMatch_atoms_integral _ (MomentMatch_tpW_nonneg hs d), Fin.sum_univ_two]
  simp [MomentMatch_tpW, MomentMatch_tpAtom]

/-- The moments of orders `0` to `4` of the two-point law. -/
private lemma MomentMatch_twoPt_mom {s : ℝ} (hs : 0 < s) (d : ℝ) :
    ∫ x, x ∂(MomentMatch_twoPt s d) = 0 ∧ ∫ x, x ^ 2 ∂(MomentMatch_twoPt s d) = s ∧
    ∫ x, x ^ 3 ∂(MomentMatch_twoPt s d) = s * d ∧
    ∫ x, x ^ 4 ∂(MomentMatch_twoPt s d) = s * (d ^ 2 + s) := by
  have hr := MomentMatch_r_pos hs d
  have hr2 := MomentMatch_r_sq hs d
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [MomentMatch_twoPt_integral hs d]
    simp only [smul_eq_mul]
    generalize MomentMatch_r s d = r at hr hr2 ⊢
    have hs' : s = (r ^ 2 - d ^ 2) / 4 := by linarith
    subst hs'
    field_simp
    ring

private lemma MomentMatch_twoPt_ae {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (d : ℝ) :
    ∀ᵐ w ∂(MomentMatch_twoPt s d), |w| ≤ |d| + 1 := by
  refine MomentMatch_atoms_ae _ _ (fun w : ℝ => |w| ≤ |d| + 1)
    (measurableSet_le (by fun_prop) (by fun_prop)) fun k => ?_
  have h1 := MomentMatch_r_abs hs d
  have h2 := MomentMatch_r_le hs1 d
  have h3 := abs_le.mp h1
  fin_cases k
  · change |(d + MomentMatch_r s d) / 2| ≤ |d| + 1
    rw [abs_le]; constructor <;> linarith [le_abs_self d, neg_abs_le d]
  · change |(d - MomentMatch_r s d) / 2| ≤ |d| + 1
    rw [abs_le]; constructor <;> linarith [le_abs_self d, neg_abs_le d]

/-- `κ = (1 + a² + a⁴) / a³`, so that `a³ (a³ + (1 - a²) κ) = 1`. -/
private def MomentMatch_kappa (a : ℝ) : ℝ := (1 + a ^ 2 + a ^ 4) / a ^ 3

private lemma MomentMatch_kappa_id {a : ℝ} (ha : 0 < a) :
    a ^ 3 * (a ^ 3 + (1 - a ^ 2) * MomentMatch_kappa a) = 1 := by
  unfold MomentMatch_kappa
  field_simp
  ring

private lemma MomentMatch_kappa_bounds {a : ℝ} (ha : 7 / 10 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ MomentMatch_kappa a ∧ MomentMatch_kappa a ≤ 9 := by
  have h0 : 0 < a := by linarith
  have h3 : (1 : ℝ) / 3 ≤ a ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 10) ha 3]
  unfold MomentMatch_kappa
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pow_le_one₀ h0.le ha1 (n := 2), pow_le_one₀ h0.le ha1 (n := 4)]

/-- The elementary facts about `a = √(1 - s)` and `b = √s`. -/
private lemma MomentMatch_ab {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    0 < Real.sqrt (1 - s) ∧ Real.sqrt (1 - s) ≤ 1 ∧ 7 / 10 ≤ Real.sqrt (1 - s) ∧
      Real.sqrt (1 - s) ^ 2 = 1 - s ∧ 0 < Real.sqrt s ∧ Real.sqrt s ^ 2 = s := by
  have h1 : Real.sqrt (1 - s) ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have h0 : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨h0, ?_, ?_, h1, Real.sqrt_pos.mpr hs0, Real.sq_sqrt hs0.le⟩
  · nlinarith
  · nlinarith

/-- The elementary inequality behind the fourth-moment error of the real construction. -/
private lemma MomentMatch_real_bound (s M4 d B4 R : ℝ) (hs0 : 0 < s) (hs : s ≤ 1 / 2)
    (hB4 : |M4| ≤ B4) (hd2 : d ^ 2 ≤ R ^ 2) :
    |(1 - s) ^ 2 * ((1 - s) ^ 2 * M4 + 6 * (1 - s) * s + s * (d ^ 2 + s)) +
        6 * (1 - s) * s + 3 * s ^ 2 - M4| ≤ s * (4 * B4 + R ^ 2 + 16) := by
  have h0 : 0 ≤ 1 - s := by linarith
  have h4s : |(1 - s) ^ 4 - 1| ≤ 4 * s := by
    have h1 : (1 - s) ^ 4 ≤ 1 := pow_le_one₀ h0 (by linarith)
    have h2 : 1 - 4 * s ≤ (1 - s) ^ 4 := by
      have := one_add_mul_le_pow (a := -s) (by linarith) 4
      simpa [sub_eq_add_neg] using this
    rw [abs_le]; constructor <;> linarith
  have hΔ : (1 - s) ^ 2 * ((1 - s) ^ 2 * M4 + 6 * (1 - s) * s + s * (d ^ 2 + s)) +
      6 * (1 - s) * s + 3 * s ^ 2 - M4 = ((1 - s) ^ 4 - 1) * M4 +
      (1 - s) ^ 2 * (6 * (1 - s) * s + s * (d ^ 2 + s)) + 6 * (1 - s) * s + 3 * s ^ 2 := by
    ring
  rw [hΔ]
  have e1 : |((1 - s) ^ 4 - 1) * M4| ≤ 4 * s * B4 := by
    rw [abs_mul]
    exact mul_le_mul h4s hB4 (abs_nonneg _) (by positivity)
  have hP : 0 ≤ 6 * (1 - s) * s + s * (d ^ 2 + s) := by positivity
  have e2 : |(1 - s) ^ 2 * (6 * (1 - s) * s + s * (d ^ 2 + s))| ≤ 6 * s + s * (R ^ 2 + 1) := by
    have h1 : (1 - s) ^ 2 ≤ 1 := pow_le_one₀ h0 (by linarith)
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hP)]
    calc (1 - s) ^ 2 * (6 * (1 - s) * s + s * (d ^ 2 + s))
        ≤ 1 * (6 * (1 - s) * s + s * (d ^ 2 + s)) := mul_le_mul_of_nonneg_right h1 hP
      _ ≤ 6 * s + s * (R ^ 2 + 1) := by nlinarith
  have e3 : |6 * (1 - s) * s| ≤ 6 * s := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have e4 : |3 * s ^ 2| ≤ 2 * s := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have f1 := abs_le.mp e1
  have f2 := abs_le.mp e2
  have f3 := abs_le.mp e3
  have f4 := abs_le.mp e4
  rw [abs_le]
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- The diagonal part of (3.36) [comH0], (3.37) [comH]: `y = √(1-s) x + w` with `w` the two-point
law of variance `s` and third moment `s κ E x³`, `κ = ((1-s)^{-3/2} - (1-s)^{3/2}) / s`; then
`√(1-s) y + √s g` matches the moments of `x` up to order `3` exactly and the fourth up to
`K s`. -/
private lemma MomentMatch_diag (ν : ProbabilityMeasure ℝ)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) (ν : Measure ℝ))
    (h1 : ∫ x, x ∂(ν : Measure ℝ) = 0) (h2 : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = 1)
    (B3 B4 R : ℝ) (hB3 : |∫ x, x ^ 3 ∂(ν : Measure ℝ)| ≤ B3)
    (hB4 : |∫ x, x ^ 4 ∂(ν : Measure ℝ)| ≤ B4) (hR : 9 * B3 + 1 ≤ R)
    (s : ℝ) (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    ∃ ν' : ProbabilityMeasure ℝ,
      (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) (ν' : Measure ℝ)) ∧
      ∫ x, x ∂(ν' : Measure ℝ) = 0 ∧ ∫ x, x ^ 2 ∂(ν' : Measure ℝ) = 1 ∧
      (∀ n : ℕ, ∫ x, |x| ^ n ∂(ν' : Measure ℝ) ≤
        2 ^ n * (∫ x, |x| ^ n ∂(ν : Measure ℝ) + R ^ n)) ∧
      (∀ a : ℕ, a ≤ 3 → ∫ x, x ^ a ∂(mixLawR s (ν' : Measure ℝ)) = ∫ x, x ^ a ∂(ν : Measure ℝ)) ∧
      |(∫ x, x ^ 4 ∂(mixLawR s (ν' : Measure ℝ))) - ∫ x, x ^ 4 ∂(ν : Measure ℝ)| ≤
        s * (4 * B4 + R ^ 2 + 16) := by
  have : IsProbabilityMeasure (ν : Measure ℝ) := ν.prop
  obtain ⟨ha0, ha1, ha7, ha2, hb0, hb2⟩ := MomentMatch_ab hs0 hs
  have hB3' : 0 ≤ B3 := (abs_nonneg _).trans hB3
  have hR0 : 0 ≤ R := by linarith
  set a := Real.sqrt (1 - s) with ha
  set b := Real.sqrt s with hb
  set M3 := ∫ x, x ^ 3 ∂(ν : Measure ℝ) with hM3
  set M4 := ∫ x, x ^ 4 ∂(ν : Measure ℝ) with hM4
  obtain ⟨hκ0, hκ9⟩ := MomentMatch_kappa_bounds ha7 ha1
  have hκid := MomentMatch_kappa_id ha0
  set κ := MomentMatch_kappa a with hκ
  set d := κ * M3 with hd
  have hdabs : |d| ≤ 9 * B3 := by
    rw [hd, abs_mul, abs_of_nonneg hκ0]
    exact mul_le_mul hκ9 hB3 (abs_nonneg _) (by norm_num)
  set τ := MomentMatch_twoPt s d with hτ
  have : IsProbabilityMeasure τ := MomentMatch_twoPt_prob hs0 d
  have hτae : ∀ᵐ w ∂τ, |w| ≤ R := by
    filter_upwards [MomentMatch_twoPt_ae hs0 (by linarith) d] with w hw
    linarith
  have hτint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) τ := fun n => by
    refine (integrable_const (R ^ n)).mono' (by fun_prop) ?_
    filter_upwards [hτae] with w hw
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) hw n
  have hνint : ∀ n : ℕ, Integrable (fun x : ℝ => ‖x‖ ^ n) (ν : Measure ℝ) := fun n => by
    simpa using hint n
  have hpert := fun n => MomentMatch_pert (ν := (ν : Measure ℝ)) (τ := τ) hνint R hR0
    (by simpa using hτae) (fun p : ℝ × ℝ => a * p.1 + 1 * p.2) (by fun_prop)
    (fun p => by
      calc ‖a * p.1 + 1 * p.2‖ ≤ ‖a * p.1‖ + ‖1 * p.2‖ := norm_add_le _ _
        _ ≤ ‖p.1‖ + ‖p.2‖ := by
          rw [norm_mul, norm_mul, norm_one, one_mul, Real.norm_of_nonneg ha0.le]
          nlinarith [norm_nonneg p.1]) n
  obtain ⟨hτ1, hτ2, hτ3, hτ4⟩ : ∫ x, x ∂τ = 0 ∧ ∫ x, x ^ 2 ∂τ = s ∧ ∫ x, x ^ 3 ∂τ = s * d ∧
      ∫ x, x ^ 4 ∂τ = s * (d ^ 2 + s) := MomentMatch_twoPt_mom hs0 d
  set Y := MomentMatch_convR a 1 (ν : Measure ℝ) τ with hYdef
  have : IsProbabilityMeasure Y := by unfold Y MomentMatch_convR; infer_instance
  have hY := fun k => MomentMatch_convR_mom (μ₁ := (ν : Measure ℝ)) (μ₂ := τ) hint hτint a 1 k
  have hY1 : ∫ x, x ∂Y = 0 := by
    have := hY 1
    simp [Finset.sum_range_succ, h1, hτ1] at this
    exact this
  have hY2 : ∫ x, x ^ 2 ∂Y = 1 := by
    have := hY 2
    simp [Finset.sum_range_succ, h1, h2, hτ1, hτ2] at this
    rw [show Y = MomentMatch_convR a 1 (ν : Measure ℝ) τ from rfl, this]
    nlinarith
  have hY3 : ∫ x, x ^ 3 ∂Y = a ^ 3 * M3 + s * d := by
    have := hY 3
    simp [Finset.sum_range_succ, Nat.choose, h1, h2, ← hM3, hτ1, hτ2, hτ3] at this
    rw [show Y = MomentMatch_convR a 1 (ν : Measure ℝ) τ from rfl, this]
    ring
  have hY4 : ∫ x, x ^ 4 ∂Y = a ^ 4 * M4 + 6 * a ^ 2 * s + s * (d ^ 2 + s) := by
    have := hY 4
    simp [Finset.sum_range_succ, Nat.choose, h1, h2, ← hM3, ← hM4, hτ1, hτ2, hτ3, hτ4] at this
    rw [show Y = MomentMatch_convR a 1 (ν : Measure ℝ) τ from rfl, this]
    ring
  have hYint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) Y := fun n => by
    have h := (hpert n).1
    simp only [Real.norm_eq_abs] at h
    exact h
  obtain ⟨hg1, hg2, hg3, hg4⟩ := MomentMatch_gauss_mom 1
  simp only [NNReal.coe_one, one_pow, mul_one] at hg2 hg4
  have hX := fun k => MomentMatch_convR_mom (μ₁ := Y) (μ₂ := gaussianReal 0 1) hYint
    (MomentMatch_gauss_int 1) a b k
  have hmix : mixLawR s Y = MomentMatch_convR a b Y (gaussianReal 0 1) := rfl
  have : IsProbabilityMeasure (mixLawR s Y) := by unfold mixLawR; infer_instance
  have hX1 : ∫ x, x ∂(mixLawR s Y) = 0 := by
    have := hX 1
    simp [Finset.sum_range_succ, hY1, hg1] at this
    rw [hmix, this]
  have hX2 : ∫ x, x ^ 2 ∂(mixLawR s Y) = 1 := by
    have := hX 2
    simp [Finset.sum_range_succ, hY1, hY2, hg1, hg2] at this
    rw [hmix, this, hb2, ha2]
    ring
  have hX3 : ∫ x, x ^ 3 ∂(mixLawR s Y) = M3 := by
    have := hX 3
    simp [Finset.sum_range_succ, Nat.choose, hY1, hY2, hY3, hg1, hg2, hg3] at this
    rw [hmix, this]
    have h12 : (1 - a ^ 2) = s := by linarith
    rw [hd]
    linear_combination M3 * hκid - (a ^ 3 * κ * M3) * h12
  have hX4 : ∫ x, x ^ 4 ∂(mixLawR s Y) = a ^ 4 * (a ^ 4 * M4 + 6 * a ^ 2 * s + s * (d ^ 2 + s)) +
      6 * a ^ 2 * s + 3 * s ^ 2 := by
    have := hX 4
    simp [Finset.sum_range_succ, Nat.choose, hY1, hY2, hY4, hg1, hg2, hg3, hg4] at this
    have hb4 : b ^ 4 = s ^ 2 := by
      calc b ^ 4 = (b ^ 2) ^ 2 := by ring
        _ = s ^ 2 := by rw [hb2]
    rw [hmix, this, hb4, hb2]
    ring
  have hu : a ^ 4 = (1 - s) ^ 2 := by rw [← ha2]; ring
  have hu2 : a ^ 2 = 1 - s := ha2
  have h4s : |(1 - s) ^ 4 - 1| ≤ 4 * s := by
    have h1 : (1 - s) ^ 4 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : 1 - 4 * s ≤ (1 - s) ^ 4 := by
      have := one_add_mul_le_pow (a := -s) (by linarith) 4
      simpa [sub_eq_add_neg] using this
    rw [abs_le]; constructor <;> linarith
  have hd2 : d ^ 2 ≤ R ^ 2 := by
    have : |d| ≤ R := by linarith
    nlinarith [sq_abs d, abs_nonneg d]
  refine ⟨⟨Y, inferInstance⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hYint
  · exact hY1
  · exact hY2
  · intro n
    have := (hpert n).2
    simp only [Real.norm_eq_abs] at this
    exact this
  · intro k hk
    interval_cases k
    · simp
    · simpa [h1] using hX1
    · simpa [h2] using hX2
    · simpa [hM3] using hX3
  · change |∫ x, x ^ 4 ∂(mixLawR s Y) - M4| ≤ _
    rw [hX4, hu, hu2]
    exact MomentMatch_real_bound s M4 d B4 R hs0 hs hB4 hd2

/-- The mixed-moment formula of an independent sum, in terms of the moment tables. -/
private def MomentMatch_cvm (c d : ℂ) (m₁ m₂ : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
    ((p.choose i : ℂ) * (q.choose j : ℂ) *
      (c ^ i * starRingEnd ℂ c ^ j * d ^ (p - i) * starRingEnd ℂ d ^ (q - j))) *
    (m₁ i j * m₂ (p - i) (q - j))

/-- Order one to three of the first step `y = a x + w`. -/
private lemma MomentMatch_alg_y (a s κ : ℝ) (ha2 : a ^ 2 = 1 - s)
    (mν mτ : ℕ → ℕ → ℂ) (hν00 : mν 0 0 = 1) (hν10 : mν 1 0 = 0) (hν01 : mν 0 1 = 0)
    (hν20 : mν 2 0 = 0) (hν02 : mν 0 2 = 0) (hν11 : mν 1 1 = 1)
    (hτ00 : mτ 0 0 = 1) (hτ10 : mτ 1 0 = 0) (hτ01 : mτ 0 1 = 0)
    (hτ20 : mτ 2 0 = 0) (hτ02 : mτ 0 2 = 0) (hτ11 : mτ 1 1 = s)
    (hτ30 : mτ 3 0 = s * κ * mν 3 0) (hτ21 : mτ 2 1 = s * κ * mν 2 1)
    (hτ12 : mτ 1 2 = s * κ * mν 1 2) (hτ03 : mτ 0 3 = s * κ * mν 0 3) :
    MomentMatch_cvm a 1 mν mτ 0 0 = 1 ∧ MomentMatch_cvm a 1 mν mτ 1 0 = 0 ∧
    MomentMatch_cvm a 1 mν mτ 0 1 = 0 ∧ MomentMatch_cvm a 1 mν mτ 2 0 = 0 ∧
    MomentMatch_cvm a 1 mν mτ 0 2 = 0 ∧ MomentMatch_cvm a 1 mν mτ 1 1 = 1 ∧
    MomentMatch_cvm a 1 mν mτ 3 0 = (a ^ 3 + s * κ) * mν 3 0 ∧
    MomentMatch_cvm a 1 mν mτ 2 1 = (a ^ 3 + s * κ) * mν 2 1 ∧
    MomentMatch_cvm a 1 mν mτ 1 2 = (a ^ 3 + s * κ) * mν 1 2 ∧
    MomentMatch_cvm a 1 mν mτ 0 3 = (a ^ 3 + s * κ) * mν 0 3 := by
  have ha2' : (a : ℂ) ^ 2 = 1 - s := by exact_mod_cast ha2
  unfold MomentMatch_cvm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [Finset.sum_range_succ, Nat.choose, hν00, hν10, hν01, hν20, hν02, hν11, hτ00, hτ10, hτ01,
      hτ20, hτ02, hτ11, hτ30, hτ21, hτ12, hτ03] <;>
    first | linear_combination ha2' | ring1

/-- Order four of the first step `y = a x + w`. -/
private lemma MomentMatch_alg_y4 (a s : ℝ)
    (mν mτ : ℕ → ℕ → ℂ) (hν00 : mν 0 0 = 1) (hν10 : mν 1 0 = 0) (hν01 : mν 0 1 = 0)
    (hν20 : mν 2 0 = 0) (hν02 : mν 0 2 = 0) (hν11 : mν 1 1 = 1)
    (hτ00 : mτ 0 0 = 1) (hτ10 : mτ 1 0 = 0) (hτ01 : mτ 0 1 = 0)
    (hτ20 : mτ 2 0 = 0) (hτ02 : mτ 0 2 = 0) (hτ11 : mτ 1 1 = s) :
    MomentMatch_cvm a 1 mν mτ 4 0 = a ^ 4 * mν 4 0 + mτ 4 0 ∧
    MomentMatch_cvm a 1 mν mτ 3 1 = a ^ 4 * mν 3 1 + mτ 3 1 ∧
    MomentMatch_cvm a 1 mν mτ 2 2 = a ^ 4 * mν 2 2 + mτ 2 2 + 4 * a ^ 2 * s ∧
    MomentMatch_cvm a 1 mν mτ 1 3 = a ^ 4 * mν 1 3 + mτ 1 3 ∧
    MomentMatch_cvm a 1 mν mτ 0 4 = a ^ 4 * mν 0 4 + mτ 0 4 := by
  unfold MomentMatch_cvm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [Finset.sum_range_succ, Nat.choose, hν00, hν10, hν01, hν20, hν02, hν11, hτ00, hτ10, hτ01,
      hτ20, hτ02, hτ11] <;> ring1

/-- The second step `x̃ = a y + b g`, orders zero to three. -/
private lemma MomentMatch_alg_x (a b s κ : ℝ) (ha2 : a ^ 2 = 1 - s) (hb2 : b ^ 2 = s)
    (hκ : a ^ 3 * (a ^ 3 + s * κ) = 1)
    (mν my mg : ℕ → ℕ → ℂ) (hy00 : my 0 0 = 1) (hy10 : my 1 0 = 0) (hy01 : my 0 1 = 0)
    (hy20 : my 2 0 = 0) (hy02 : my 0 2 = 0) (hy11 : my 1 1 = 1)
    (hy30 : my 3 0 = (a ^ 3 + s * κ) * mν 3 0) (hy21 : my 2 1 = (a ^ 3 + s * κ) * mν 2 1)
    (hy12 : my 1 2 = (a ^ 3 + s * κ) * mν 1 2) (hy03 : my 0 3 = (a ^ 3 + s * κ) * mν 0 3)
    (hg00 : mg 0 0 = 1) (hg10 : mg 1 0 = 0) (hg01 : mg 0 1 = 0) (hg20 : mg 2 0 = 0)
    (hg11 : mg 1 1 = 1) (hg02 : mg 0 2 = 0) (hg30 : mg 3 0 = 0) (hg21 : mg 2 1 = 0)
    (hg12 : mg 1 2 = 0) (hg03 : mg 0 3 = 0) :
    MomentMatch_cvm a b my mg 0 0 = 1 ∧ MomentMatch_cvm a b my mg 1 0 = 0 ∧
    MomentMatch_cvm a b my mg 0 1 = 0 ∧ MomentMatch_cvm a b my mg 2 0 = 0 ∧
    MomentMatch_cvm a b my mg 0 2 = 0 ∧ MomentMatch_cvm a b my mg 1 1 = 1 ∧
    MomentMatch_cvm a b my mg 3 0 = mν 3 0 ∧ MomentMatch_cvm a b my mg 2 1 = mν 2 1 ∧
    MomentMatch_cvm a b my mg 1 2 = mν 1 2 ∧ MomentMatch_cvm a b my mg 0 3 = mν 0 3 := by
  have ha2' : (a : ℂ) ^ 2 = 1 - s := by exact_mod_cast ha2
  have hb2' : (b : ℂ) ^ 2 = s := by exact_mod_cast hb2
  have hκ' : (a : ℂ) ^ 3 * ((a : ℂ) ^ 3 + s * κ) = 1 := by exact_mod_cast hκ
  unfold MomentMatch_cvm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [Finset.sum_range_succ, Nat.choose, hy00, hy10, hy01, hy20, hy02, hy11, hy30, hy21, hy12,
      hy03, hg00, hg10, hg01, hg20, hg11, hg02, hg30, hg21, hg12, hg03] <;>
    first | linear_combination ha2' + hb2' | linear_combination (mν 3 0) * hκ' |
      linear_combination (mν 2 1) * hκ' | linear_combination (mν 1 2) * hκ' |
      linear_combination (mν 0 3) * hκ'

/-- The second step `x̃ = a y + b g`, order four. -/
private lemma MomentMatch_alg_x4 (a b s : ℝ) (hb2 : b ^ 2 = s)
    (my mg : ℕ → ℕ → ℂ) (hy00 : my 0 0 = 1) (hy10 : my 1 0 = 0) (hy01 : my 0 1 = 0)
    (hy20 : my 2 0 = 0) (hy02 : my 0 2 = 0) (hy11 : my 1 1 = 1)
    (hg00 : mg 0 0 = 1) (hg10 : mg 1 0 = 0) (hg01 : mg 0 1 = 0) (hg20 : mg 2 0 = 0)
    (hg11 : mg 1 1 = 1) (hg02 : mg 0 2 = 0) (hg30 : mg 3 0 = 0) (hg21 : mg 2 1 = 0)
    (hg12 : mg 1 2 = 0) (hg03 : mg 0 3 = 0) (hg40 : mg 4 0 = 0) (hg31 : mg 3 1 = 0)
    (hg22 : mg 2 2 = 2) (hg13 : mg 1 3 = 0) (hg04 : mg 0 4 = 0) :
    MomentMatch_cvm a b my mg 4 0 = a ^ 4 * my 4 0 ∧
    MomentMatch_cvm a b my mg 3 1 = a ^ 4 * my 3 1 ∧
    MomentMatch_cvm a b my mg 2 2 = a ^ 4 * my 2 2 + 4 * a ^ 2 * s + 2 * s ^ 2 ∧
    MomentMatch_cvm a b my mg 1 3 = a ^ 4 * my 1 3 ∧
    MomentMatch_cvm a b my mg 0 4 = a ^ 4 * my 0 4 := by
  have hb2' : (b : ℂ) ^ 2 = s := by exact_mod_cast hb2
  unfold MomentMatch_cvm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [Finset.sum_range_succ, Nat.choose, hy00, hy10, hy01, hy20, hy02, hy11,
      hg00, hg10, hg01, hg20, hg11, hg02, hg30, hg21, hg12, hg03, hg40, hg31, hg22, hg13, hg04] <;>
    first | (left; ring1) |
      linear_combination (2 * ((b : ℂ) ^ 2 + s) + 4 * (a : ℂ) ^ 2) * hb2'

/-- The unit complex number `(3 + 4 i) / 5`. -/
private def MomentMatch_w : ℂ := (3 + 4 * Complex.I) / 5

/-- The four directions `1, i, w, i w` of the rays of the off-diagonal construction. -/
private def MomentMatch_u : Fin 4 → ℂ := ![1, Complex.I, MomentMatch_w, Complex.I * MomentMatch_w]

private lemma MomentMatch_w_re : MomentMatch_w.re = 3 / 5 := by
  simp [MomentMatch_w]

private lemma MomentMatch_w_im : MomentMatch_w.im = 4 / 5 := by
  simp [MomentMatch_w]

private lemma MomentMatch_u_norm (k : Fin 4) : ‖MomentMatch_u k‖ = 1 := by
  have hw : ‖MomentMatch_w‖ = 1 := by
    have h : ‖MomentMatch_w‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, MomentMatch_w_re, MomentMatch_w_im]; norm_num
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  fin_cases k <;> simp [MomentMatch_u, hw]

/-- Real coefficients `d₁, …, d₄` with `Σ uₖ³ dₖ = 4 A` and `Σ uₖ dₖ = 4 B`. -/
private lemma MomentMatch_solve (A B : ℂ) (M : ℝ) (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) :
    ∃ d : Fin 4 → ℝ, (∑ k, MomentMatch_u k ^ 3 * (d k : ℂ)) = 4 * A ∧
      (∑ k, MomentMatch_u k * (d k : ℂ)) = 4 * B ∧ ∀ k, |d k| ≤ 13 * M := by
  set d3 : ℝ := 5 / 12 * (4 * (B.re - A.re) + 3 * (B.im + A.im)) with hd3
  set d4 : ℝ := 5 / 12 * (4 * (B.im + A.im) - 3 * (B.re - A.re)) with hd4
  set d1 : ℝ := 4 * B.re - (3 * d3 - 4 * d4) / 5 with hd1
  set d2 : ℝ := 4 * B.im - (4 * d3 + 3 * d4) / 5 with hd2
  have hAre := (Complex.abs_re_le_norm A).trans hA
  have hAim := (Complex.abs_im_le_norm A).trans hA
  have hBre := (Complex.abs_re_le_norm B).trans hB
  have hBim := (Complex.abs_im_le_norm B).trans hB
  refine ⟨![d1, d2, d3, d4], ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp [Fin.sum_univ_four, MomentMatch_u, pow_succ, MomentMatch_w_re, MomentMatch_w_im]
      linarith
    · simp [Fin.sum_univ_four, MomentMatch_u, pow_succ, MomentMatch_w_re, MomentMatch_w_im]
      linarith
  · apply Complex.ext
    · simp [Fin.sum_univ_four, MomentMatch_u, MomentMatch_w_re, MomentMatch_w_im]
      linarith
    · simp [Fin.sum_univ_four, MomentMatch_u, MomentMatch_w_re, MomentMatch_w_im]
      linarith
  · intro k
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
      rw [abs_le] <;> constructor <;>
      nlinarith [abs_le.mp hAre, abs_le.mp hAim, abs_le.mp hBre, abs_le.mp hBim]

/-- The mixture of the four rays `u_k · (two-point law)` with equal weights. -/
private def MomentMatch_tauO (s : ℝ) (d : Fin 4 → ℝ) : Measure ℂ :=
  MomentMatch_atoms (fun kj : Fin 4 × Fin 2 => (1 / 4 : ℝ) * MomentMatch_tpW s (d kj.1) kj.2)
    (fun kj : Fin 4 × Fin 2 =>
      MomentMatch_u kj.1 * ((MomentMatch_tpAtom s (d kj.1) kj.2 : ℝ) : ℂ))

private lemma MomentMatch_tauO_prob {s : ℝ} (hs : 0 < s) (d : Fin 4 → ℝ) :
    IsProbabilityMeasure (MomentMatch_tauO s d) := by
  refine MomentMatch_atoms_prob _ (fun kj => ?_) ?_ _
  · exact mul_nonneg (by norm_num) (MomentMatch_tpW_nonneg hs _ _)
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, MomentMatch_tpW_sum hs, Fin.sum_univ_four]
    norm_num

private lemma MomentMatch_tauO_ae {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (d : Fin 4 → ℝ) (R : ℝ)
    (hd : ∀ k, |d k| + 1 ≤ R) : ∀ᵐ z ∂(MomentMatch_tauO s d), ‖z‖ ≤ R := by
  refine MomentMatch_atoms_ae _ _ (fun z : ℂ => ‖z‖ ≤ R)
    (measurableSet_le (by fun_prop) (by fun_prop)) fun kj => ?_
  obtain ⟨k, j⟩ := kj
  have h1 : ∀ j, |MomentMatch_tpAtom s (d k) j| ≤ |d k| + 1 := by
    intro j
    have := MomentMatch_twoPt_ae hs hs1 (d k)
    have h1 := MomentMatch_r_abs hs (d k)
    have h2 := MomentMatch_r_le hs1 (d k)
    have h3 := abs_le.mp h1
    fin_cases j
    · change |((d k) + MomentMatch_r s (d k)) / 2| ≤ |d k| + 1
      rw [abs_le]; constructor <;> linarith [le_abs_self (d k), neg_abs_le (d k)]
    · change |((d k) - MomentMatch_r s (d k)) / 2| ≤ |d k| + 1
      rw [abs_le]; constructor <;> linarith [le_abs_self (d k), neg_abs_le (d k)]
  change ‖MomentMatch_u k * ((MomentMatch_tpAtom s (d k) j : ℝ) : ℂ)‖ ≤ R
  rw [norm_mul, MomentMatch_u_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (h1 j).trans (hd k)

private lemma MomentMatch_ray_pow (u : ℂ) (x : ℝ) (p q : ℕ) :
    (u * (x : ℂ)) ^ p * starRingEnd ℂ (u * (x : ℂ)) ^ q =
      (u ^ p * starRingEnd ℂ u ^ q) * ((x ^ (p + q) : ℝ) : ℂ) := by
  rw [map_mul, Complex.conj_ofReal, mul_pow, mul_pow, pow_add]
  push_cast
  ring

/-- The mixed moments of the ray mixture. -/
private lemma MomentMatch_tauO_mom {s : ℝ} (hs : 0 < s) (d : Fin 4 → ℝ) (p q : ℕ) :
    mixMom (MomentMatch_tauO s d) p q = ∑ k : Fin 4, (1 / 4 : ℂ) * (MomentMatch_u k ^ p *
      starRingEnd ℂ (MomentMatch_u k) ^ q) *
        ((∫ x, x ^ (p + q) ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) := by
  unfold mixMom MomentMatch_tauO
  rw [MomentMatch_atoms_integral _ (fun kj => mul_nonneg (by norm_num)
    (MomentMatch_tpW_nonneg hs _ _)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MomentMatch_twoPt_integral hs (d k)]
  simp only [Fin.sum_univ_two, MomentMatch_ray_pow]
  simp only [MomentMatch_tpW, MomentMatch_tpAtom, Complex.real_smul]
  simp
  ring

private lemma MomentMatch_u_mul_conj (k : Fin 4) :
    MomentMatch_u k * starRingEnd ℂ (MomentMatch_u k) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, MomentMatch_u_norm]
  simp

private lemma MomentMatch_u_sq_sum : ∑ k, MomentMatch_u k ^ 2 = 0 := by
  have hw : MomentMatch_w ^ 2 = MomentMatch_w ^ 2 := rfl
  simp [Fin.sum_univ_four, MomentMatch_u, mul_pow]

private lemma MomentMatch_tauO_mom_n {s : ℝ} (hs : 0 < s) (d : Fin 4 → ℝ) (n p q : ℕ)
    (h : p + q = n) :
    mixMom (MomentMatch_tauO s d) p q = ∑ k : Fin 4, (1 / 4 : ℂ) * (MomentMatch_u k ^ p *
      starRingEnd ℂ (MomentMatch_u k) ^ q) *
        ((∫ x, x ^ n ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) := by
  rw [MomentMatch_tauO_mom hs, h]

/-- The moment table of the ray mixture. -/
private lemma MomentMatch_tauO_table {s : ℝ} (hs : 0 < s) (d : Fin 4 → ℝ) (A B : ℂ)
    (h3 : ∑ k, MomentMatch_u k ^ 3 * (d k : ℂ) = 4 * A)
    (h1 : ∑ k, MomentMatch_u k * (d k : ℂ) = 4 * B) :
    mixMom (MomentMatch_tauO s d) 0 0 = 1 ∧ mixMom (MomentMatch_tauO s d) 1 0 = 0 ∧
    mixMom (MomentMatch_tauO s d) 0 1 = 0 ∧ mixMom (MomentMatch_tauO s d) 2 0 = 0 ∧
    mixMom (MomentMatch_tauO s d) 0 2 = 0 ∧ mixMom (MomentMatch_tauO s d) 1 1 = s ∧
    mixMom (MomentMatch_tauO s d) 3 0 = s * A ∧ mixMom (MomentMatch_tauO s d) 2 1 = s * B ∧
    mixMom (MomentMatch_tauO s d) 1 2 = s * starRingEnd ℂ B ∧
    mixMom (MomentMatch_tauO s d) 0 3 = s * starRingEnd ℂ A := by
  have hp : ∀ k, IsProbabilityMeasure (MomentMatch_twoPt s (d k)) := fun k =>
    MomentMatch_twoPt_prob hs (d k)
  have hm0 : ∀ k, ∫ x, x ^ 0 ∂(MomentMatch_twoPt s (d k)) = 1 := fun k => by
    have := hp k; simp
  have hm1 : ∀ k, ∫ x, x ^ 1 ∂(MomentMatch_twoPt s (d k)) = 0 := fun k => by
    simpa using (MomentMatch_twoPt_mom hs (d k)).1
  have hm2 : ∀ k, ∫ x, x ^ 2 ∂(MomentMatch_twoPt s (d k)) = s := fun k =>
    (MomentMatch_twoPt_mom hs (d k)).2.1
  have hm3 : ∀ k, ∫ x, x ^ 3 ∂(MomentMatch_twoPt s (d k)) = s * d k := fun k =>
    (MomentMatch_twoPt_mom hs (d k)).2.2.1
  have hm1' : ∀ k, ∫ x, x ∂(MomentMatch_twoPt s (d k)) = 0 := fun k =>
    (MomentMatch_twoPt_mom hs (d k)).1
  have hmc := MomentMatch_u_mul_conj
  have hc : ∀ (f : Fin 4 → ℂ), starRingEnd ℂ (∑ k, f k) = ∑ k, starRingEnd ℂ (f k) :=
    fun f => map_sum _ _ _
  have hcB : ∑ k, starRingEnd ℂ (MomentMatch_u k) * (d k : ℂ) = 4 * starRingEnd ℂ B := by
    have := congrArg (starRingEnd ℂ) h1
    rw [hc] at this
    simpa [map_mul, Complex.conj_ofReal, map_ofNat] using this
  have hcA : ∑ k, starRingEnd ℂ (MomentMatch_u k) ^ 3 * (d k : ℂ) = 4 * starRingEnd ℂ A := by
    have := congrArg (starRingEnd ℂ) h3
    rw [hc] at this
    simpa [map_mul, map_pow, Complex.conj_ofReal, map_ofNat] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MomentMatch_tauO_mom_n hs d 0 0 0 rfl]
    simp
  · rw [MomentMatch_tauO_mom_n hs d 1 1 0 rfl]
    simp [hm1']
  · rw [MomentMatch_tauO_mom_n hs d 1 0 1 rfl]
    simp [hm1']
  · rw [MomentMatch_tauO_mom_n hs d 2 2 0 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 2 * starRingEnd ℂ (MomentMatch_u k) ^ 0) *
        ((∫ x, x ^ 2 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) = (s / 4 : ℂ) * MomentMatch_u k ^ 2 :=
      fun k => by rw [hm2]; ring
    simp only [this, ← Finset.mul_sum, MomentMatch_u_sq_sum, mul_zero]
  · rw [MomentMatch_tauO_mom_n hs d 2 0 2 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 0 * starRingEnd ℂ (MomentMatch_u k) ^ 2) *
        ((∫ x, x ^ 2 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) =
          (s / 4 : ℂ) * starRingEnd ℂ (MomentMatch_u k ^ 2) :=
      fun k => by rw [hm2, map_pow]; ring
    simp only [this, ← Finset.mul_sum, ← hc, MomentMatch_u_sq_sum, map_zero, mul_zero]
  · rw [MomentMatch_tauO_mom_n hs d 2 1 1 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 1 * starRingEnd ℂ (MomentMatch_u k) ^ 1) *
        ((∫ x, x ^ 2 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) = (s / 4 : ℂ) :=
      fun k => by rw [hm2, pow_one, pow_one, hmc]; ring
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
    ring
  · rw [MomentMatch_tauO_mom_n hs d 3 3 0 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 3 * starRingEnd ℂ (MomentMatch_u k) ^ 0) *
        ((∫ x, x ^ 3 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) =
          (s / 4 : ℂ) * (MomentMatch_u k ^ 3 * (d k : ℂ)) :=
      fun k => by rw [hm3]; push_cast; ring
    simp only [this, ← Finset.mul_sum, h3]
    ring
  · rw [MomentMatch_tauO_mom_n hs d 3 2 1 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 2 * starRingEnd ℂ (MomentMatch_u k) ^ 1) *
        ((∫ x, x ^ 3 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) =
          (s / 4 : ℂ) * (MomentMatch_u k * (d k : ℂ)) :=
      fun k => by
        rw [hm3]; push_cast
        linear_combination ((1 / 4 : ℂ) * MomentMatch_u k * s * (d k : ℂ)) * hmc k
    simp only [this, ← Finset.mul_sum, h1]
    ring
  · rw [MomentMatch_tauO_mom_n hs d 3 1 2 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 1 * starRingEnd ℂ (MomentMatch_u k) ^ 2) *
        ((∫ x, x ^ 3 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) =
          (s / 4 : ℂ) * (starRingEnd ℂ (MomentMatch_u k) * (d k : ℂ)) :=
      fun k => by
        rw [hm3]; push_cast
        linear_combination ((1 / 4 : ℂ) * starRingEnd ℂ (MomentMatch_u k) * s * (d k : ℂ)) * hmc k
    simp only [this, ← Finset.mul_sum, hcB]
    ring
  · rw [MomentMatch_tauO_mom_n hs d 3 0 3 rfl]
    have : ∀ k, (1 / 4 : ℂ) * (MomentMatch_u k ^ 0 * starRingEnd ℂ (MomentMatch_u k) ^ 3) *
        ((∫ x, x ^ 3 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ) =
          (s / 4 : ℂ) * (starRingEnd ℂ (MomentMatch_u k) ^ 3 * (d k : ℂ)) :=
      fun k => by
        rw [hm3]; push_cast; ring
    simp only [this, ← Finset.mul_sum, hcA]
    ring

/-- The fourth mixed moments of the ray mixture are `O(s)`. -/
private lemma MomentMatch_tauO_four {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (d : Fin 4 → ℝ) (D : ℝ)
    (hD : ∀ k, |d k| ≤ D) (p q : ℕ) (h : p + q = 4) :
    ‖mixMom (MomentMatch_tauO s d) p q‖ ≤ s * (D ^ 2 + 1) := by
  rw [MomentMatch_tauO_mom_n hs d 4 p q h]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k : Fin 4, ‖(1 / 4 : ℂ) * (MomentMatch_u k ^ p * starRingEnd ℂ (MomentMatch_u k) ^ q) *
      ((∫ x, x ^ 4 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ)‖ ≤ s * (D ^ 2 + 1) / 4 := by
    intro k
    rw [(MomentMatch_twoPt_mom hs (d k)).2.2.2, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      Complex.norm_conj, MomentMatch_u_norm, Complex.norm_real, Real.norm_eq_abs]
    have h1 : d k ^ 2 ≤ D ^ 2 := by
      have := hD k
      nlinarith [sq_abs (d k), abs_nonneg (d k)]
    rw [abs_of_nonneg (by positivity)]
    simp only [one_pow, one_mul, norm_div, norm_one]
    norm_num
    nlinarith
  calc ∑ k : Fin 4, ‖(1 / 4 : ℂ) * (MomentMatch_u k ^ p * starRingEnd ℂ (MomentMatch_u k) ^ q) *
      ((∫ x, x ^ 4 ∂(MomentMatch_twoPt s (d k)) : ℝ) : ℂ)‖
      ≤ ∑ _k : Fin 4, s * (D ^ 2 + 1) / 4 := Finset.sum_le_sum fun k _ => hk k
    _ = s * (D ^ 2 + 1) := by simp; ring

/-- Complex conjugation exchanges the two exponents of a mixed moment. -/
private lemma MomentMatch_mixMom_conj (μ : Measure ℂ) (p q : ℕ) :
    mixMom μ q p = starRingEnd ℂ (mixMom μ p q) := by
  unfold mixMom
  rw [← integral_conj]
  congr 1
  ext z
  simp [mul_comm]

/-- `mixMom μ 0 0 = 1` for a probability measure. -/
private lemma MomentMatch_mixMom_zero (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    mixMom μ 0 0 = 1 := by
  simp [mixMom]

/-- The fourth-order error estimate, from the two steps. -/
private lemma MomentMatch_bound4 (a s B4 T4 : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ha2 : a ^ 2 = 1 - s)
    (hs0 : 0 < s) (hs : s ≤ 1 / 2) (mν mτ f e : ℂ) (hν : ‖mν‖ ≤ B4) (hτ : ‖mτ‖ ≤ s * T4)
    (hf : ‖f‖ ≤ 4 * s) (he : ‖e‖ ≤ 5 * s) :
    ‖(a : ℂ) ^ 4 * ((a : ℂ) ^ 4 * mν + mτ + f) + e - mν‖ ≤ s * (4 * B4 + T4 + 9) := by
  have hB4 : 0 ≤ B4 := (norm_nonneg _).trans hν
  have h4 : a ^ 4 ≤ 1 := pow_le_one₀ ha ha1
  have h4' : 0 ≤ a ^ 4 := by positivity
  have h8 : ‖(a : ℂ) ^ 8 - 1‖ ≤ 4 * s := by
    have e1 : ((a : ℂ) ^ 8 - 1) = (((1 - s) ^ 4 - 1 : ℝ) : ℂ) := by
      have : a ^ 8 = (1 - s) ^ 4 := by rw [← ha2]; ring
      push_cast
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ) - 1) this
    rw [e1, Complex.norm_real, Real.norm_eq_abs]
    have h1 : (1 - s) ^ 4 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : 1 - 4 * s ≤ (1 - s) ^ 4 := by
      have := one_add_mul_le_pow (a := -s) (by linarith) 4
      simpa [sub_eq_add_neg] using this
    rw [abs_le]; constructor <;> linarith
  have e2 : (a : ℂ) ^ 4 * ((a : ℂ) ^ 4 * mν + mτ + f) + e - mν =
      ((a : ℂ) ^ 8 - 1) * mν + (a : ℂ) ^ 4 * mτ + (a : ℂ) ^ 4 * f + e := by ring
  rw [e2]
  have n1 : ‖((a : ℂ) ^ 8 - 1) * mν‖ ≤ 4 * s * B4 := by
    rw [norm_mul]
    exact mul_le_mul h8 hν (norm_nonneg _) (by positivity)
  have n2 : ‖(a : ℂ) ^ 4 * mτ‖ ≤ s * T4 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    calc a ^ 4 * ‖mτ‖ ≤ 1 * (s * T4) := mul_le_mul h4 hτ (norm_nonneg _) zero_le_one
      _ = s * T4 := one_mul _
  have n3 : ‖(a : ℂ) ^ 4 * f‖ ≤ 4 * s := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    calc a ^ 4 * ‖f‖ ≤ 1 * (4 * s) := mul_le_mul h4 hf (norm_nonneg _) zero_le_one
      _ = 4 * s := one_mul _
  calc ‖((a : ℂ) ^ 8 - 1) * mν + (a : ℂ) ^ 4 * mτ + (a : ℂ) ^ 4 * f + e‖
      ≤ ‖((a : ℂ) ^ 8 - 1) * mν‖ + ‖(a : ℂ) ^ 4 * mτ‖ + ‖(a : ℂ) ^ 4 * f‖ + ‖e‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ s * (4 * B4 + T4 + 9) := by nlinarith

/-- The wrapper of `MomentMatch_bound4` in terms of the two steps. -/
private lemma MomentMatch_bound4' (a s B4 T4 : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ha2 : a ^ 2 = 1 - s) (hs0 : 0 < s) (hs : s ≤ 1 / 2) (mν mτ f e mx my : ℂ)
    (hν : ‖mν‖ ≤ B4) (hτ : ‖mτ‖ ≤ s * T4) (hf : ‖f‖ ≤ 4 * s) (he : ‖e‖ ≤ 5 * s)
    (hx : mx = (a : ℂ) ^ 4 * my + e) (hy : my = (a : ℂ) ^ 4 * mν + mτ + f) :
    ‖mx - mν‖ ≤ s * (4 * B4 + T4 + 9) := by
  subst hx hy
  exact MomentMatch_bound4 a s B4 T4 ha ha1 ha2 hs0 hs mν mτ f e hν hτ hf he

/-- The correction terms at `(2, 2)`. -/
private lemma MomentMatch_fe (a s : ℝ) (ha2 : a ^ 2 = 1 - s) (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    ‖(4 * (a : ℂ) ^ 2 * (s : ℂ))‖ ≤ 4 * s ∧
      ‖(4 * (a : ℂ) ^ 2 * (s : ℂ) + 2 * (s : ℂ) ^ 2)‖ ≤ 5 * s := by
  have e1 : (4 * (a : ℂ) ^ 2 * (s : ℂ)) = ((4 * (1 - s) * s : ℝ) : ℂ) := by
    rw [← ha2]; push_cast; ring
  have e2 : (4 * (a : ℂ) ^ 2 * (s : ℂ) + 2 * (s : ℂ) ^ 2) =
      ((4 * (1 - s) * s + 2 * s ^ 2 : ℝ) : ℂ) := by
    rw [← ha2]; push_cast; ring
  have h0 : 0 ≤ 1 - s := by linarith
  constructor
  · rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith

/-- The off-diagonal part of (3.36) [comH0], (3.37) [comH]: `y = √(1-s) x + w` with `w` the
mixture of four rays `u_k ξ_k` (`ξ_k` two-point of variance `s`) with `E w² = 0`, `E|w|² = s`,
and third moments `E w³ = s κ E x³`, `E w² w̄ = s κ E x² x̄`; then `√(1-s) y + √s g` matches
the mixed moments of `x` up to order `3` exactly and those of order `4` up to `K s`. -/
private lemma MomentMatch_offdiag (ν : ProbabilityMeasure ℂ)
    (hint : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) (ν : Measure ℂ))
    (h10 : mixMom ν 1 0 = 0) (h20 : mixMom ν 2 0 = 0) (h11 : mixMom ν 1 1 = 1)
    (B3 B4 R : ℝ) (h30 : ‖mixMom ν 3 0‖ ≤ B3) (h21 : ‖mixMom ν 2 1‖ ≤ B3)
    (h4 : ∀ p q : ℕ, p + q = 4 → ‖mixMom ν p q‖ ≤ B4) (hR : 117 * B3 + 1 ≤ R)
    (s : ℝ) (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    ∃ ν' : ProbabilityMeasure ℂ,
      (∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) (ν' : Measure ℂ)) ∧
      mixMom ν' 1 0 = 0 ∧ mixMom ν' 2 0 = 0 ∧ mixMom ν' 1 1 = 1 ∧
      (∀ n : ℕ, ∫ z, ‖z‖ ^ n ∂(ν' : Measure ℂ) ≤
        2 ^ n * (∫ z, ‖z‖ ^ n ∂(ν : Measure ℂ) + R ^ n)) ∧
      (∀ p q : ℕ, p + q ≤ 3 → mixMom (mixLaw s ν') p q = mixMom ν p q) ∧
      (∀ p q : ℕ, p + q = 4 →
        ‖mixMom (mixLaw s ν') p q - mixMom ν p q‖ ≤ s * (4 * B4 + R ^ 2 + 16)) := by
  have : IsProbabilityMeasure (ν : Measure ℂ) := ν.prop
  obtain ⟨ha0, ha1, ha7, ha2, hb0, hb2⟩ := MomentMatch_ab hs0 hs
  have hB3 : 0 ≤ B3 := (norm_nonneg _).trans h30
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨hκ0, hκ9⟩ := MomentMatch_kappa_bounds ha7 ha1
  have hκid := MomentMatch_kappa_id ha0
  set a := Real.sqrt (1 - s) with ha
  set b := Real.sqrt s with hb
  set κ := MomentMatch_kappa a with hκ
  set A : ℂ := (κ : ℂ) * mixMom ν 3 0 with hAdef
  set B : ℂ := (κ : ℂ) * mixMom ν 2 1 with hBdef
  have hA : ‖A‖ ≤ 9 * B3 := by
    rw [hAdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0]
    exact mul_le_mul hκ9 h30 (norm_nonneg _) (by norm_num)
  have hB : ‖B‖ ≤ 9 * B3 := by
    rw [hBdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0]
    exact mul_le_mul hκ9 h21 (norm_nonneg _) (by norm_num)
  obtain ⟨d, hd3, hd1, hdb⟩ := MomentMatch_solve A B (9 * B3) hA hB
  have hdR : ∀ k, |d k| + 1 ≤ R := fun k => by have := hdb k; linarith
  have hdR' : ∀ k, |d k| ≤ R := fun k => by have := hdR k; linarith [abs_nonneg (d k)]
  set τ := MomentMatch_tauO s d with hτ
  have : IsProbabilityMeasure τ := MomentMatch_tauO_prob hs0 d
  have hτae : ∀ᵐ z ∂τ, ‖z‖ ≤ R := MomentMatch_tauO_ae hs0 (by linarith) d R hdR
  have hτint : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) τ := fun n => by
    refine (integrable_const (R ^ n)).mono' (by fun_prop) ?_
    filter_upwards [hτae] with w hw
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) hw n
  obtain ⟨t00, t10, t01, t20, t02, t11, t30, t21, t12, t03⟩ :=
    MomentMatch_tauO_table hs0 d A B hd3 hd1
  have t4 := fun p q (h : p + q = 4) => MomentMatch_tauO_four hs0 (by linarith) d R hdR' p q h
  -- the tables of `ν`
  have hν00 : mixMom ν 0 0 = 1 := MomentMatch_mixMom_zero _
  have hν01 : mixMom ν 0 1 = 0 := by rw [MomentMatch_mixMom_conj ν 1 0, h10, map_zero]
  have hν02 : mixMom ν 0 2 = 0 := by rw [MomentMatch_mixMom_conj ν 2 0, h20, map_zero]
  have hν12 : mixMom ν 1 2 = starRingEnd ℂ (mixMom ν 2 1) := MomentMatch_mixMom_conj ν 2 1
  have hν03 : mixMom ν 0 3 = starRingEnd ℂ (mixMom ν 3 0) := MomentMatch_mixMom_conj ν 3 0
  -- the first step
  set y := MomentMatch_conv (a : ℂ) 1 (ν : Measure ℂ) τ with hy
  have : IsProbabilityMeasure y := by unfold y MomentMatch_conv; infer_instance
  have hYf := fun p q => MomentMatch_conv_mom (μ₁ := (ν : Measure ℂ)) (μ₂ := τ) hint hτint
    (a : ℂ) 1 p q
  have hκ' : (κ : ℂ) = ((κ : ℝ) : ℂ) := rfl
  obtain ⟨y00, y10, y01, y20, y02, y11, y30, y21, y12, y03⟩ :=
    MomentMatch_alg_y a s κ ha2 (mixMom ν) (mixMom τ) hν00 h10 hν01 h20 hν02 h11 t00 t10 t01 t20
      t02 t11 (by rw [t30, hAdef]; ring) (by rw [t21, hBdef]; ring)
      (by rw [t12, hBdef, hν12]; simp [map_mul, Complex.conj_ofReal]; ring)
      (by rw [t03, hAdef, hν03]; simp [map_mul, Complex.conj_ofReal]; ring)
  obtain ⟨y40, y31, y22, y13, y04⟩ :=
    MomentMatch_alg_y4 a s (mixMom ν) (mixMom τ) hν00 h10 hν01 h20 hν02 h11 t00 t10 t01 t20 t02 t11
  -- the second step
  have hpert := fun n => MomentMatch_pert (E := ℂ) (ν := (ν : Measure ℂ)) (τ := τ) hint R hR0 hτae
    (fun p : ℂ × ℂ => (a : ℂ) * p.1 + 1 * p.2) (by fun_prop)
    (fun p => by
      calc ‖(a : ℂ) * p.1 + 1 * p.2‖ ≤ ‖(a : ℂ) * p.1‖ + ‖1 * p.2‖ := norm_add_le _ _
        _ ≤ ‖p.1‖ + ‖p.2‖ := by
          rw [norm_mul, norm_mul, norm_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ha0.le]
          nlinarith [norm_nonneg p.1]) n
  have hyint : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) y := fun n => (hpert n).1
  have hXf := fun p q => MomentMatch_conv_mom (μ₁ := y) (μ₂ := (cGauss : Measure ℂ)) hyint
    MomentMatch_cGauss_int (a : ℂ) (b : ℂ) p q
  obtain ⟨g00, g10, g01, g20, g11, g02, g30, g21, g12, g03, g40, g31, g22, g13, g04⟩ :=
    MomentMatch_cGauss_mom
  have hκ3 : a ^ 3 * (a ^ 3 + s * κ) = 1 := by
    have h12 : (1 - a ^ 2) = s := by linarith
    rw [h12] at hκid
    exact hκid
  have my00 : mixMom y 0 0 = 1 := (hYf 0 0).trans y00
  have my10 : mixMom y 1 0 = 0 := (hYf 1 0).trans y10
  have my01 : mixMom y 0 1 = 0 := (hYf 0 1).trans y01
  have my20 : mixMom y 2 0 = 0 := (hYf 2 0).trans y20
  have my02 : mixMom y 0 2 = 0 := (hYf 0 2).trans y02
  have my11 : mixMom y 1 1 = 1 := (hYf 1 1).trans y11
  have my30 : mixMom y 3 0 = ((a : ℂ) ^ 3 + s * κ) * mixMom ν 3 0 := (hYf 3 0).trans y30
  have my21 : mixMom y 2 1 = ((a : ℂ) ^ 3 + s * κ) * mixMom ν 2 1 := (hYf 2 1).trans y21
  have my12 : mixMom y 1 2 = ((a : ℂ) ^ 3 + s * κ) * mixMom ν 1 2 := (hYf 1 2).trans y12
  have my03 : mixMom y 0 3 = ((a : ℂ) ^ 3 + s * κ) * mixMom ν 0 3 := (hYf 0 3).trans y03
  obtain ⟨x00, x10, x01, x20, x02, x11, x30, x21, x12, x03⟩ :=
    MomentMatch_alg_x a b s κ ha2 hb2 hκ3 (mixMom ν) (mixMom y) (mixMom (cGauss : Measure ℂ))
      my00 my10 my01 my20 my02 my11 my30 my21 my12 my03 g00 g10 g01 g20 g11 g02 g30 g21 g12 g03
  obtain ⟨x40, x31, x22, x13, x04⟩ :=
    MomentMatch_alg_x4 a b s hb2 (mixMom y) (mixMom (cGauss : Measure ℂ)) my00 my10 my01 my20 my02
      my11 g00 g10 g01 g20 g11 g02 g30 g21 g12 g03 g40 g31 g22 g13 g04
  have hfe := MomentMatch_fe a s ha2 hs0 hs
  have hmix : ∀ p q, mixMom (mixLaw s y) p q =
      MomentMatch_cvm a b (mixMom y) (mixMom (cGauss : Measure ℂ)) p q := hXf
  have hT : ∀ p q, p + q = 4 → ‖mixMom τ p q‖ ≤ s * (R ^ 2 + 1) := t4
  refine ⟨⟨y, inferInstance⟩, hyint, my10, my20, my11, ?_, ?_, ?_⟩
  · intro n
    have := (hpert n).2
    exact this
  · intro p q hpq
    change mixMom (mixLaw s y) p q = mixMom ν p q
    have hp : p ≤ 3 := by omega
    have hq : q ≤ 3 := by omega
    rw [hmix]
    interval_cases p <;> interval_cases q <;>
    first | omega | (rw [hν00]; exact x00) | (rw [h10]; exact x10) | (rw [hν01]; exact x01) |
      (rw [h20]; exact x20) | (rw [h11]; exact x11) | (rw [hν02]; exact x02) | exact x30 |
      exact x21 | exact x12 | exact x03
  · intro p q hpq
    change ‖mixMom (mixLaw s y) p q - mixMom ν p q‖ ≤ _
    have hp : p ≤ 4 := by omega
    have hq : q ≤ 4 := by omega
    have hfin : ∀ (mx my f e : ℂ), ‖f‖ ≤ 4 * s → ‖e‖ ≤ 5 * s →
        mx = (a : ℂ) ^ 4 * my + e → (my = (a : ℂ) ^ 4 * mixMom ν p q + mixMom τ p q + f) →
        ‖mx - mixMom ν p q‖ ≤ s * (4 * B4 + R ^ 2 + 16) := by
      intro mx my f e hf he hx hy
      have := MomentMatch_bound4' a s B4 (R ^ 2 + 1) ha0.le ha1 ha2 hs0 hs (mixMom ν p q)
        (mixMom τ p q) f e mx my (h4 p q hpq) (hT p q hpq) hf he hx hy
      nlinarith [this]
    rw [hmix]
    interval_cases p <;> interval_cases q <;> first | omega | skip
    · exact hfin _ (mixMom y 0 4) 0 0 (by rw [norm_zero]; positivity)
        (by rw [norm_zero]; positivity) (by rw [x04]; ring) (by rw [(hYf 0 4).trans y04]; ring)
    · exact hfin _ (mixMom y 1 3) 0 0 (by rw [norm_zero]; positivity)
        (by rw [norm_zero]; positivity) (by rw [x13]; ring) (by rw [(hYf 1 3).trans y13]; ring)
    · exact hfin _ (mixMom y 2 2) _ _ hfe.1 hfe.2 (by rw [x22]; ring) (by rw [(hYf 2 2).trans y22])
    · exact hfin _ (mixMom y 3 1) 0 0 (by rw [norm_zero]; positivity)
        (by rw [norm_zero]; positivity) (by rw [x31]; ring) (by rw [(hYf 3 1).trans y31]; ring)
    · exact hfin _ (mixMom y 4 0) 0 0 (by rw [norm_zero]; positivity)
        (by rw [norm_zero]; positivity) (by rw [x40]; ring) (by rw [(hYf 4 0).trans y40]; ring)

/-- The moment `‖E z^p z̄^q‖` is bounded by the absolute moment of order `p + q`. -/
private lemma MomentMatch_mom_norm_le (μ : Measure ℂ) (p q : ℕ) :
    ‖mixMom μ p q‖ ≤ ∫ z, ‖z‖ ^ (p + q) ∂μ := by
  unfold mixMom
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [norm_pow, pow_add]

/-- The bound `R = 117 max (C 3) 0 + 1` on the size of the added independent term of the
construction, from the third absolute moments `≤ C 3` of (2.3) [eq:highmoment]. -/
private def MomentMatch_R (C : ℕ → ℝ) : ℝ := 117 * max (C 3) 0 + 1

/-- The moment constants `C' p = 2 ^ p (C p + 2 R ^ p)` of (2.3) [eq:highmoment] for the
constructed laws. -/
private def MomentMatch_C' (C : ℕ → ℝ) : ℕ → ℝ := fun p =>
  2 ^ p * (C p + 2 * MomentMatch_R C ^ p)

/-- The constant `K = 4 max (C 4) 0 + R ^ 2 + 16` of the fourth-moment error in (3.37) [comH]. -/
private def MomentMatch_K (C : ℕ → ℝ) : ℝ := 4 * max (C 4) 0 + MomentMatch_R C ^ 2 + 16

/-- The moment matching of (3.36) [comH0] and (3.37) [comH] for one set of entry laws and one
`s ∈ (0, 1/2]`, with the constants of `MomentMatch_C'` and `MomentMatch_K`. -/
private lemma MomentMatch_main (C : ℕ → ℝ) (L : EntryLaws C) (s : ℝ) (hs0 : 0 < s)
    (hs : s ≤ 1 / 2) :
    ∃ L₀ : EntryLaws (MomentMatch_C' C),
      (∀ a b : ℕ, a + b ≤ 3 → mixMom (mixLaw s L₀.νo) a b = mixMom L.νo a b) ∧
      (∀ a b : ℕ, a + b = 4 → ‖mixMom (mixLaw s L₀.νo) a b - mixMom L.νo a b‖ ≤
        MomentMatch_K C * s) ∧
      (∀ a : ℕ, a ≤ 3 → ∫ x, x ^ a ∂(mixLawR s L₀.νd) = ∫ x, x ^ a ∂(L.νd : Measure ℝ)) ∧
      |(∫ x, x ^ 4 ∂(mixLawR s L₀.νd)) - ∫ x, x ^ 4 ∂(L.νd : Measure ℝ)| ≤
        MomentMatch_K C * s := by
  -- the bounds on the third and fourth moments
  have hd3 : ∀ p : ℕ, ∫ x, |x| ^ p ∂(L.νd : Measure ℝ) ≤ C p := fun p => by
    have := L.moments p
    have h0 : 0 ≤ ∫ z, ‖z‖ ^ p ∂(L.νo : Measure ℂ) := integral_nonneg fun z => by positivity
    linarith
  have ho3 : ∀ p : ℕ, ∫ z, ‖z‖ ^ p ∂(L.νo : Measure ℂ) ≤ C p := fun p => by
    have := L.moments p
    have h0 : 0 ≤ ∫ x, |x| ^ p ∂(L.νd : Measure ℝ) := integral_nonneg fun z => by positivity
    linarith
  have hB3 : 0 ≤ max (C 3) 0 := le_max_right _ _
  have hR : 117 * max (C 3) 0 + 1 ≤ MomentMatch_R C := le_refl _
  obtain ⟨νd, hd1, hd2, hd3', hd4, hd5, hd6⟩ := MomentMatch_diag L.νd L.intd L.meand L.vard
    (max (C 3) 0) (max (C 4) 0) (MomentMatch_R C)
    (by
      refine (abs_integral_le_integral_abs).trans ?_
      simp only [abs_pow]
      exact (hd3 3).trans (le_max_left _ _))
    (by
      refine (abs_integral_le_integral_abs).trans ?_
      simp only [abs_pow]
      exact (hd3 4).trans (le_max_left _ _))
    (by linarith) s hs0 hs
  have hνo : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) (L.νo : Measure ℂ) := L.into
  obtain ⟨νo, ho1, ho2, ho3', ho4, ho5, ho6, ho7⟩ := MomentMatch_offdiag L.νo hνo
    (by simpa [mixMom] using L.meano) (by simpa [mixMom] using L.pseudo)
    (by
      unfold mixMom
      have : ∀ z : ℂ, z ^ 1 * starRingEnd ℂ z ^ 1 = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
        rw [pow_one, pow_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [this]
      rw [integral_complex_ofReal, L.varo]
      simp)
    (max (C 3) 0) (max (C 4) 0) (MomentMatch_R C)
    ((MomentMatch_mom_norm_le _ 3 0).trans ((ho3 3).trans (le_max_left _ _)))
    ((MomentMatch_mom_norm_le _ 2 1).trans ((ho3 3).trans (le_max_left _ _)))
    (fun p q h => (MomentMatch_mom_norm_le _ p q).trans (by
      rw [h]; exact (ho3 4).trans (le_max_left _ _)))
    (by linarith) s hs0 hs
  have hmeano : ∫ z, z ∂(νo : Measure ℂ) = 0 := by simpa [mixMom] using ho2
  have hpseudo : ∫ z, z ^ 2 ∂(νo : Measure ℂ) = 0 := by simpa [mixMom] using ho3'
  have hvaro : ∫ z, ‖z‖ ^ 2 ∂(νo : Measure ℂ) = 1 := by
    have h := ho4
    unfold mixMom at h
    have : ∀ z : ℂ, z ^ 1 * starRingEnd ℂ z ^ 1 = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [pow_one, pow_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  have hmom : ∀ p : ℕ, (∫ x, |x| ^ p ∂(νd : Measure ℝ)) + (∫ z, ‖z‖ ^ p ∂(νo : Measure ℂ)) ≤
      MomentMatch_C' C p := by
    intro p
    have h1 := hd4 p
    have h2 := ho5 p
    have h3 := L.moments p
    have h4 : (0 : ℝ) ≤ 2 ^ p := by positivity
    have h5 := mul_le_mul_of_nonneg_left h3 h4
    unfold MomentMatch_C'
    nlinarith [h5]
  obtain ⟨L₀, hL₀d, hL₀o⟩ : ∃ L₀ : EntryLaws (MomentMatch_C' C), L₀.νd = νd ∧ L₀.νo = νo :=
    ⟨{ νd := νd, νo := νo, intd := hd1, into := ho1, meand := hd2, vard := hd3',
       meano := hmeano, varo := hvaro, pseudo := hpseudo, moments := hmom }, rfl, rfl⟩
  refine ⟨L₀, ?_, ?_, ?_, ?_⟩
  · rw [hL₀o]; exact ho6
  · rw [hL₀o]; exact fun a b h => (ho7 a b h).trans_eq (mul_comm _ _)
  · rw [hL₀d]; exact hd5
  · rw [hL₀d]; exact hd6.trans_eq (mul_comm _ _)

/-- Moment matching for (3.36) [comH0], (3.37) [comH] with `s = N^{-ε_g}` (scaled entries): for
every Assumption 1 [main_assm] law there is another one, with constants depending only on `C`, whose
Gaussian mixture matches all moments of order `≤ 3` exactly and those of order `4` up to `K s`. -/
theorem moment_matching (C : ℕ → ℝ) :
    ∃ (C' : ℕ → ℝ) (K : ℝ), ∀ (L : EntryLaws C) (s : ℝ), 0 < s → s ≤ 1 / 2 →
      ∃ L₀ : EntryLaws C',
        (∀ a b : ℕ, a + b ≤ 3 → mixMom (mixLaw s L₀.νo) a b = mixMom L.νo a b) ∧
        (∀ a b : ℕ, a + b = 4 → ‖mixMom (mixLaw s L₀.νo) a b - mixMom L.νo a b‖ ≤ K * s) ∧
        (∀ a : ℕ, a ≤ 3 → ∫ x, x ^ a ∂(mixLawR s L₀.νd) = ∫ x, x ^ a ∂(L.νd : Measure ℝ)) ∧
        |(∫ x, x ^ 4 ∂(mixLawR s L₀.νd)) - ∫ x, x ^ 4 ∂(L.νd : Measure ℝ)| ≤ K * s := by
  exact ⟨MomentMatch_C' C, MomentMatch_K C, fun L s hs0 hs => MomentMatch_main C L s hs0 hs⟩


end RBMTransitionEdge

end
