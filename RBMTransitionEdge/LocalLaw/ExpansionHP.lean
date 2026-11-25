module

public import RBMTransitionEdge.LocalLaw.ResPolyDer
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

/-!
# The one-entry expansion with a high-probability remainder

Lemma 2.11 [lem:complex_cumu], (2.26) [5.16], for one entry of a member of the class, with the
derivative bounds required only where a smooth cutoff, constant along the entry, is nonzero, and
the probability that the cutoff differs from `1` entering through a square root: first for a
general function of the array, then for resolvent polynomials over a finite family of pairs
`(Λ, ξ)`, with the cutoff built from the forms of the resolvents of the array whose entry `(i, j)`
is set to `0`.
-/

open MeasureTheory ProbabilityTheory Matrix

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The smooth cutoff `ψ(t)`, equal to `1` for `t ≤ 1` and to `0` for `t ≥ 2`, with values in
`[0, 1]`. -/
def cutoffFn (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

/-- The cutoff of the one-entry expansion in the entry `(i, j)` for a family `Ξ` of pairs
`(Λ, ξ)`: `χ(h) = Π_{(Λ, ξ) ∈ Ξ} Π_{x, y ∈ V} ψ(|x^* (ĥ + Λ - ξ)⁻¹ y|² / (2Γ)²)`, where `ĥ` is the
Hermitian part of `h` with the entry `(i, j)` set to `0`. -/
def hpCut {D N : ℕ} (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (V : Finset (Idx D N → ℂ))
    (Γ : ℝ) (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℝ :=
  ∏ p ∈ Ξ, ∏ x ∈ V, ∏ y ∈ V, cutoffFn
    (‖resFactorEval (x, y, p.1, p.2) (symArr (setEntry h i j 0))‖ ^ 2 / (2 * Γ) ^ 2)

/-! ### The one-entry substitution, the Hermitian part and the forms -/

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma EH_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      rw [hk, hl]
      have hre : (((h i i).re : ℝ) : ℂ) = h i i := Complex.conj_eq_iff_re.mp (h1 i i)
      simp [setEntry, hre]
    · simp [setEntry, hkl]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd, h1 k l]
      · simp [setEntry, hd, h1', h2]

/-- For a Hermitian array `h`, the substituted array `setEntry h i j w` is its own Hermitian
part. -/
private lemma EH_symArr_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    symArr (setEntry h i j w) = setEntry h i j w := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- A substitution in a Hermitian array is Hermitian. -/
private lemma EH_setEntry_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  rw [← EH_symArr_slice h hh i j w]
  exact symArr_isHermitian _

/-- The entry `(i, j)` of `setEntry h i j 0` is `0`. -/
private lemma EH_setEntry_zero_apply {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    setEntry h i j 0 i j = 0 := by
  by_cases hd : i = j
  · simp [setEntry, hd]
  · simp [setEntry, hd]

/-- The array `setEntry h i j w` is a smooth function of `(h, w)`. -/
private lemma EH_contDiff_setEntry {D N : ℕ} (i j : Idx D N) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hre : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => ((p.2.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
  have hw : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => p.2) := contDiff_snd
  have hcw : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => starRingEnd ℂ p.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  have hf : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => p.1 k l) :=
    (contDiff_apply_apply ℝ k l).comp contDiff_fst
  simp only [setEntry]
  split_ifs <;> assumption

/-- The Hermitian part `h ↦ (h + hᴴ)/2` is a smooth function of the array. -/
private lemma EH_contDiff_symArr {D N : ℕ} (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => symArr h) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  simp only [symArr]
  exact ((contDiff_apply_apply ℝ k l).add
    (Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ l k))).div_const 2

/-- A form `x^* (h + Λ - ξ)⁻¹ y` with Hermitian `Λ` and `Im ξ ≠ 0` is a smooth function of the
array through its Hermitian part. -/
private lemma EH_contDiff_factor {D N : ℕ} (f : ResFactor D N)
    (hf : f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => resFactorEval f (symArr h)) := by
  have e : ∀ h : Idx D N → Idx D N → ℂ, resFactorEval f (symArr h) = ∑ k, ∑ l, star (f.1 k) *
      (res (Matrix.of (symArr h) + f.2.2.1) f.2.2.2 k l * f.2.1 l) := by
    intro h
    simp only [resFactorEval, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  simp only [e]
  exact ContDiff.sum fun k _ => ContDiff.sum fun l _ => contDiff_const.mul
    ((contDiff_res_symArr _ hf.1 _ hf.2 k l n).mul contDiff_const)

/-- `|x^* A y| ≤ ‖A‖` for vectors `x`, `y` of norm `≤ 1`. -/
private lemma EH_form_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x y : ι → ℂ) (hx : ∑ r, ‖x r‖ ^ 2 ≤ 1) (hy : ∑ r, ‖y r‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ≤ opNorm A := by
  have e : star x ⬝ᵥ (A *ᵥ y) = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanCLM_toLp]
    simp [dotProduct_comm]
  have hxn : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact (Real.sqrt_le_sqrt hx).trans_eq Real.sqrt_one
  have hyn : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact (Real.sqrt_le_sqrt hy).trans_eq Real.sqrt_one
  rw [e]
  unfold opNorm
  calc ‖inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * 1) :=
        mul_le_mul hxn ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm_of_le hyn)
          (norm_nonneg _) zero_le_one
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by ring

/-- For Hermitian `h` and `Λ` and `Im ξ > 0`: `|x^* (h + Λ - ξ̄)⁻¹ y| = |y^* (h + Λ - ξ)⁻¹ x|`. -/
private lemma EH_form_conj {D N : ℕ} (x y : Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (ξ : ℂ) (hξ : 0 < ξ.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    ‖resFactorEval (x, y, Λ, starRingEnd ℂ ξ) h‖ = ‖resFactorEval (y, x, Λ, ξ) h‖ := by
  have hG := res_conj (Matrix.of h + Λ) (hh.add hΛ) ξ hξ
  have e : resFactorEval (x, y, Λ, starRingEnd ℂ ξ) h =
      starRingEnd ℂ (resFactorEval (y, x, Λ, ξ) h) := by
    simp only [resFactorEval, hG, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
      Pi.star_apply, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [e, Complex.norm_conj]

/-- A finite product of numbers in `[0, 1]` lies in `[0, 1]`. -/
private lemma EH_prod_mem_Icc {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ a ∈ s, f a ∈ Set.Icc (0 : ℝ) 1) : ∏ a ∈ s, f a ∈ Set.Icc (0 : ℝ) 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    exact ⟨mul_nonneg h1.1 h2.1, (mul_le_mul h1.2 h2.2 h2.1 zero_le_one).trans_eq (one_mul 1)⟩

/-- `x ≤ c √s` when `x ≤ c` and `x ≤ c s`, for `c, s ≥ 0`: the form `min(1, s) ≤ s^{1/2}`. -/
private lemma EH_le_sqrt {x c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (h1 : x ≤ c) (h2 : x ≤ c * s) :
    x ≤ c * Real.sqrt s := by
  rcases le_or_gt 1 s with h | h
  · exact h1.trans (le_mul_of_one_le_right hc (Real.one_le_sqrt.mpr h))
  · refine h2.trans (mul_le_mul_of_nonneg_left ?_ hc)
    have hr := Real.sq_sqrt hs
    have hr0 := Real.sqrt_nonneg s
    have hr1 : Real.sqrt s < 1 := by
      rw [Real.sqrt_lt' one_pos]; simpa using h
    nlinarith

/-- `N^{-k/2} M^{-k} = (N^{1/2} M)^{-k}` for `N, M > 0`. -/
private lemma EH_rpow_eq {N M : ℝ} (hN : 0 < N) (hM : 0 < M) (k : ℕ) :
    N ^ (-((k : ℝ) / 2)) / M ^ k = (N ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) hM.le, ← Real.rpow_mul hN.le, Real.rpow_neg hM.le,
    Real.rpow_natCast, div_eq_mul_inv]
  congr 2
  ring

/-- Markov's inequality for an entry of a member of the class with the moment `k` of (2.3)
[eq:highmoment]: `P(|h_{ij}| > M) ≤ C_k (N^{1/2} M)^{-k}`. -/
private lemma EH_markov {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) (k : ℕ) (M : ℝ) (hM : 0 < M) :
    μ.real {h | M < ‖h i j‖} ≤ C k * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) := by
  have := hμ.prob
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos i.2
  have hMk : 0 < M ^ k := pow_pos hM k
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun h => ‖h i j‖ ^ k)
    (ae_of_all _ fun h => by simp only [Pi.zero_apply]; positivity) (hμ.integrable k i j) (M ^ k)
  have h2 : μ.real {h : Idx D N → Idx D N → ℂ | M < ‖h i j‖} ≤
      μ.real {h : Idx D N → Idx D N → ℂ | M ^ k ≤ ‖h i j‖ ^ k} :=
    measureReal_mono (fun h hh => pow_le_pow_left₀ hM.le (le_of_lt hh) k)
  have h3 := hμ.moments k i j
  rw [← EH_rpow_eq hN hM k, ← mul_div_assoc, le_div_iff₀ hMk]
  nlinarith

/-- The cutoff does not depend on the entry `(i, j)`. -/
theorem hpCut_setEntry {D N : ℕ} (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (V : Finset (Idx D N → ℂ)) (Γ : ℝ) (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) (w : ℂ) :
    hpCut Ξ V Γ i j (setEntry h i j w) = hpCut Ξ V Γ i j h := by
  unfold hpCut
  rw [setEntry_setEntry]

/-- The cutoff takes values in `[0, 1]`. -/
theorem hpCut_mem_Icc {D N : ℕ} (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (V : Finset (Idx D N → ℂ)) (Γ : ℝ) (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) :
    hpCut Ξ V Γ i j h ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hpCut cutoffFn
  exact EH_prod_mem_Icc _ _ fun p _ => EH_prod_mem_Icc _ _ fun x _ => EH_prod_mem_Icc _ _
    fun y _ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The cutoff is of class `C^n` on all arrays when every pair has a Hermitian `Λ` and
`Im ξ ≠ 0`. -/
theorem hpCut_contDiff {D N : ℕ} (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hΞ : ∀ p ∈ Ξ, p.1.IsHermitian ∧ p.2.im ≠ 0) (V : Finset (Idx D N → ℂ)) (Γ : ℝ)
    (i j : Idx D N) (n : ℕ) :
    ContDiff ℝ n (hpCut Ξ V Γ i j) := by
  have hS : ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => setEntry h i j 0) :=
    (EH_contDiff_setEntry i j n).comp (contDiff_id.prodMk contDiff_const)
  unfold hpCut cutoffFn
  refine contDiff_prod fun p hp => contDiff_prod fun x _ => contDiff_prod fun y _ => ?_
  have hf := (EH_contDiff_factor (x, y, p.1, p.2) (hΞ p hp) n).comp hS
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((hf.norm_sq ℝ).div_const _))

/-- The cutoff equals `1` on the good event: for Hermitian `h`, pairs with Hermitian `Λ` and
`Im ξ > 0`, `e_i, e_j ∈ V`, `|h_{ij}| ≤ M`, `4 M Γ ≤ 1/2` and `|x^* (h + Λ - ξ)⁻¹ y| ≤ Γ` for
`x, y ∈ V` and every pair. -/
theorem hpCut_eq_one {D N : ℕ} (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hΞ : ∀ p ∈ Ξ, p.1.IsHermitian ∧ 0 < p.2.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (V : Finset (Idx D N → ℂ))
    (hi : Pi.single i 1 ∈ V) (hj : Pi.single j 1 ∈ V) (M Γ : ℝ) (hM : ‖h i j‖ ≤ M)
    (hMΓ : 4 * M * Γ ≤ 1 / 2)
    (hG : ∀ p ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, p.1, p.2) h‖ ≤ Γ) :
    hpCut Ξ V Γ i j h = 1 := by
  unfold hpCut
  refine Finset.prod_eq_one fun p hp => Finset.prod_eq_one fun x hx =>
    Finset.prod_eq_one fun y hy => ?_
  obtain ⟨hΛ, hξ⟩ := hΞ p hp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hG' : ∀ x' ∈ ({x, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
      ∀ y' ∈ ({y, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
        ‖star x' ⬝ᵥ (res (Matrix.of h + p.1) p.2 *ᵥ y')‖ ≤ Γ := by
    intro x' hx' y' hy'
    have hx'V : x' ∈ V := by rcases hx' with rfl | rfl | rfl <;> assumption
    have hy'V : y' ∈ V := by rcases hy' with rfl | rfl | rfl <;> assumption
    exact hG p hp x' hx'V y' hy'V
  have key := res_setEntry_le D N h p.1 hh hΛ p.2 hξ i j 0 M Γ (by simpa using hM0) hM hMΓ x y
    hG' x (by simp) y (by simp)
  have hfe : ‖resFactorEval (x, y, p.1, p.2) (setEntry h i j 0)‖ ≤ 2 * Γ := key
  rw [EH_symArr_slice h hh i j 0]
  unfold cutoffFn
  apply Real.smoothTransition.one_of_one_le
  have : ‖resFactorEval (x, y, p.1, p.2) (setEntry h i j 0)‖ ^ 2 / (2 * Γ) ^ 2 ≤ 1 :=
    div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) hfe 2) (sq_nonneg _)
  linarith

/-- Where the cutoff is nonzero, the forms stay below `6Γ` after any substitution `|w| ≤ M` in
the entry `(i, j)`: for Hermitian `h`, pairs with Hermitian `Λ` and `Im ξ > 0`, `e_i, e_j ∈ V`,
`0 < Γ` and `24 M Γ ≤ 1`. -/
theorem hpCut_ne_zero_le {D N : ℕ} (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hΞ : ∀ p ∈ Ξ, p.1.IsHermitian ∧ 0 < p.2.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (V : Finset (Idx D N → ℂ))
    (hi : Pi.single i 1 ∈ V) (hj : Pi.single j 1 ∈ V) (M Γ : ℝ) (hΓ : 0 < Γ)
    (hMΓ : 24 * M * Γ ≤ 1) (hχ : hpCut Ξ V Γ i j h ≠ 0) (w : ℂ) (hw : ‖w‖ ≤ M) :
    ∀ p ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V,
      ‖resFactorEval (x, y, p.1, p.2) (setEntry h i j w)‖ ≤ 6 * Γ := by
  intro p hp x hx y hy
  obtain ⟨hΛ, hξ⟩ := hΞ p hp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hw
  have hĥ : (Matrix.of (setEntry h i j 0)).IsHermitian := EH_setEntry_herm h hh i j 0
  unfold hpCut at hχ
  have hfac : ∀ x' ∈ V, ∀ y' ∈ V,
      ‖resFactorEval (x', y', p.1, p.2) (setEntry h i j 0)‖ ≤ 3 * Γ := by
    intro x' hx' y' hy'
    have h1 := (Finset.prod_ne_zero_iff.mp hχ) p hp
    have h2 := (Finset.prod_ne_zero_iff.mp h1) x' hx'
    have h3 := (Finset.prod_ne_zero_iff.mp h2) y' hy'
    rw [EH_symArr_slice h hh i j 0] at h3
    unfold cutoffFn at h3
    have ht : ‖resFactorEval (x', y', p.1, p.2) (setEntry h i j 0)‖ ^ 2 / (2 * Γ) ^ 2 < 2 := by
      by_contra hc
      exact h3 (Real.smoothTransition.zero_of_nonpos (by linarith [not_lt.mp hc]))
    rw [div_lt_iff₀ (by positivity)] at ht
    by_contra hc
    have hc' := not_le.mp hc
    have := mul_le_mul hc'.le hc'.le (by positivity) (norm_nonneg _)
    nlinarith
  have hG' : ∀ x' ∈ ({x, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
      ∀ y' ∈ ({y, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
        ‖star x' ⬝ᵥ (res (Matrix.of (setEntry h i j 0) + p.1) p.2 *ᵥ y')‖ ≤ 3 * Γ := by
    intro x' hx' y' hy'
    have hx'V : x' ∈ V := by rcases hx' with rfl | rfl | rfl <;> assumption
    have hy'V : y' ∈ V := by rcases hy' with rfl | rfl | rfl <;> assumption
    exact hfac x' hx'V y' hy'V
  have hMΓ' : 4 * M * (3 * Γ) ≤ 1 / 2 := by nlinarith
  have key := res_setEntry_le D N (setEntry h i j 0) p.1 hĥ hΛ p.2 hξ i j w M (3 * Γ) hw
    (by rw [EH_setEntry_zero_apply]; simpa using hM0) hMΓ' x y hG' x (by simp) y (by simp)
  rw [setEntry_setEntry] at key
  have e : (2 : ℝ) * (3 * Γ) = 6 * Γ := by ring
  rw [e] at key
  exact key

/-- The cutoff differs from `1` with probability at most `ε₀ + K (N^{1/2} M)^{-k}` when the forms
of the resolvents of the Hermitian part exceed `Γ` with probability at most `ε₀`; `K` depends on
`k` and `C` only. -/
theorem hpCut_ne_one_le (k : ℕ) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → ∀ Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ p ∈ Ξ, p.1.IsHermitian ∧ 0 < p.2.im) →
      ∀ (i j : Idx D N) (V : Finset (Idx D N → ℂ)),
      Pi.single i 1 ∈ V → Pi.single j 1 ∈ V →
      ∀ Γ M ε₀ : ℝ, 0 < M → 4 * M * Γ ≤ 1 / 2 → 0 ≤ ε₀ →
      μ {h | ∃ p ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V,
          Γ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ≤ ENNReal.ofReal ε₀ →
      μ {h | hpCut Ξ V Γ i j h ≠ 1} ≤
        ENNReal.ofReal (ε₀ + K * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))) := by
  refine ⟨max (C k) 0, le_max_right _ _, ?_⟩
  intro D N θ μ hμ Ξ hΞ i j V hi hj Γ M ε₀ hM hMΓ hε₀ hbad
  have := hμ.prob
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos i.2
  have hσ0 : 0 ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) hM.le) _
  have hsub : {h : Idx D N → Idx D N → ℂ | hpCut Ξ V Γ i j h ≠ 1} ⊆
      {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} ∪
        {h | ∃ p ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V, Γ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ∪
        {h | M < ‖h i j‖} := by
    intro h hh1
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_exists, not_and,
      not_lt] at hc
    obtain ⟨⟨hherm, hgood⟩, hsmall⟩ := hc
    apply hh1
    refine hpCut_eq_one Ξ hΞ h hherm i j V hi hj M Γ hsmall hMΓ fun p hp x hx y hy => ?_
    have := hgood p hp x hx y hy
    rwa [symArr_of_isHermitian h hherm] at this
  have hherm0 : μ {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} = 0 :=
    ae_iff.mp hμ.herm
  have hmk : μ {h : Idx D N → Idx D N → ℂ | M < ‖h i j‖} ≤
      ENNReal.ofReal (max (C k) 0 * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
    exact (EH_markov hμ i j k M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hσ0)
  calc μ {h | hpCut Ξ V Γ i j h ≠ 1}
      ≤ μ ({h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} ∪
        {h | ∃ p ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V, Γ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ∪
        {h | M < ‖h i j‖}) := measure_mono hsub
    _ ≤ μ {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} +
        μ {h | ∃ p ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V, Γ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} +
        μ {h | M < ‖h i j‖} :=
      (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal ε₀ +
        ENNReal.ofReal (max (C k) 0 * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))) := by
      rw [hherm0]
      gcongr
    _ = ENNReal.ofReal (ε₀ + max (C k) 0 * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))) := by
      rw [zero_add, ENNReal.ofReal_add hε₀ (by positivity)]

/-! ### Derivatives in the entry along a parameter -/

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Wirtinger derivative `∂_w` of a function of `(r, w)` in the variable `w`. -/
private def EH_pdW (G : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun x => (fderiv ℝ G x (0, 1) - Complex.I * fderiv ℝ G x (0, Complex.I)) / 2

/-- The Wirtinger derivative `∂_{w̄}` of a function of `(r, w)` in the variable `w`. -/
private def EH_pdWbar (G : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun x => (fderiv ℝ G x (0, 1) + Complex.I * fderiv ℝ G x (0, Complex.I)) / 2

/-- The real derivative of `w ↦ G (r, w)` is the derivative of `G` along `(0, v)`. -/
private lemma EH_fderiv_slice (G : E × ℂ → ℂ) (r : E) (w : ℂ)
    (hG : DifferentiableAt ℝ G (r, w)) (v : ℂ) :
    fderiv ℝ (fun w' => G (r, w')) w v = fderiv ℝ G (r, w) (0, v) := by
  have h1 : HasFDerivAt (fun w' : ℂ => (r, w')) (ContinuousLinearMap.inr ℝ E ℂ) w :=
    hasFDerivAt_prodMk_right r w
  have h2 := hG.hasFDerivAt.comp w h1
  have h3 : fderiv ℝ (fun w' => G (r, w')) w = _ := h2.fderiv
  rw [h3]
  simp

/-- `∂_w` of a slice `w ↦ G (r, w)` is the slice of the partial derivative `EH_pdW G`. -/
private lemma EH_dW_slice (G : E × ℂ → ℂ) (hG : Differentiable ℝ G) (r : E) :
    dW (fun w => G (r, w)) = fun w => EH_pdW G (r, w) := by
  funext w
  simp only [dW, EH_pdW]
  rw [EH_fderiv_slice G r w (hG _), EH_fderiv_slice G r w (hG _)]

/-- `∂_{w̄}` of a slice `w ↦ G (r, w)` is the slice of the partial derivative `EH_pdWbar G`. -/
private lemma EH_dWbar_slice (G : E × ℂ → ℂ) (hG : Differentiable ℝ G) (r : E) :
    dWbar (fun w => G (r, w)) = fun w => EH_pdWbar G (r, w) := by
  funext w
  simp only [dWbar, EH_pdWbar]
  rw [EH_fderiv_slice G r w (hG _), EH_fderiv_slice G r w (hG _)]

/-- `EH_pdW G` is `C^n` if `G` is `C^{n+1}`. -/
private lemma EH_pdW_contDiff {G : E × ℂ → ℂ} {n : ℕ}
    (hG : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (n : WithTop ℕ∞) (EH_pdW G) := by
  have hd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ G) :=
    hG.fderiv_right (by push_cast; exact le_rfl)
  unfold EH_pdW
  exact ((hd.clm_apply contDiff_const).sub
    (contDiff_const.mul (hd.clm_apply contDiff_const))).div_const 2

/-- `EH_pdWbar G` is `C^n` if `G` is `C^{n+1}`. -/
private lemma EH_pdWbar_contDiff {G : E × ℂ → ℂ} {n : ℕ}
    (hG : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (n : WithTop ℕ∞) (EH_pdWbar G) := by
  have hd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ G) :=
    hG.fderiv_right (by push_cast; exact le_rfl)
  unfold EH_pdWbar
  exact ((hd.clm_apply contDiff_const).add
    (contDiff_const.mul (hd.clm_apply contDiff_const))).div_const 2

/-- Iterating a derivative operator that commutes with taking slices. -/
private lemma EH_iter (pd : (E × ℂ → ℂ) → (E × ℂ → ℂ)) (d : (ℂ → ℂ) → (ℂ → ℂ))
    (h1 : ∀ (n : ℕ) (G : E × ℂ → ℂ), ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G →
      ContDiff ℝ (n : WithTop ℕ∞) (pd G))
    (h2 : ∀ (G : E × ℂ → ℂ), ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) G → ∀ r : E,
      d (fun w => G (r, w)) = fun w => pd G (r, w)) :
    ∀ (q n : ℕ) (G : E × ℂ → ℂ), ContDiff ℝ ((n + q : ℕ) : WithTop ℕ∞) G →
      ContDiff ℝ (n : WithTop ℕ∞) (pd^[q] G) ∧
        ∀ r : E, d^[q] (fun w => G (r, w)) = fun w => (pd^[q] G) (r, w) := by
  intro q
  induction q with
  | zero =>
    intro n G hG
    exact ⟨hG, fun r => rfl⟩
  | succ q ih =>
    intro n G hG
    have hG' : ContDiff ℝ ((n + q + 1 : ℕ) : WithTop ℕ∞) G := hG
    have hpd : ContDiff ℝ ((n + q : ℕ) : WithTop ℕ∞) (pd G) := h1 (n + q) G hG'
    obtain ⟨c, e⟩ := ih n (pd G) hpd
    refine ⟨by simpa [Function.iterate_succ_apply] using c, fun r => ?_⟩
    have hG1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) G :=
      hG'.of_le (by exact_mod_cast Nat.le_add_left 1 (n + q))
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h2 G hG1 r]
    exact e r

/-- The Wirtinger derivatives `F^{(p,q)}(r, ·)(w)` of Lemma 2.11 [lem:complex_cumu] of a
`C^{l+1}` function of `(r, w)` are jointly continuous in `(r, w)` for `p + q ≤ l + 1`. -/
private lemma EH_wirt_continuous (G : E × ℂ → ℂ) (l : ℕ)
    (hG : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) G) (p q : ℕ) (hpq : p + q ≤ l + 1) :
    Continuous (fun x : E × ℂ => wirt p q (fun w => G (x.1, w)) x.2) := by
  have hq : (l + 1 - q) + q = l + 1 := by omega
  have hG1 : ContDiff ℝ ((l + 1 - q + q : ℕ) : WithTop ℕ∞) G := by rw [hq]; exact hG
  obtain ⟨c1, e1⟩ := EH_iter EH_pdWbar dWbar (fun n G hG => EH_pdWbar_contDiff hG)
    (fun G hG r => EH_dWbar_slice G (hG.differentiable (by simp)) r) q (l + 1 - q) G hG1
  have hp : (l + 1 - q - p) + p = l + 1 - q := by omega
  have hc1 : ContDiff ℝ ((l + 1 - q - p + p : ℕ) : WithTop ℕ∞) (EH_pdWbar^[q] G) := by
    rw [hp]; exact c1
  obtain ⟨c2, e2⟩ := EH_iter EH_pdW dW (fun n G hG => EH_pdW_contDiff hG)
    (fun G hG r => EH_dW_slice G (hG.differentiable (by simp)) r) p (l + 1 - q - p)
    (EH_pdWbar^[q] G) hc1
  have : (fun x : E × ℂ => wirt p q (fun w => G (x.1, w)) x.2) =
      EH_pdW^[p] (EH_pdWbar^[q] G) := by
    funext x
    unfold wirt
    rw [e1 x.1, e2 x.1]
  rw [this]
  exact c2.continuous

end Param

/-- The Wirtinger derivatives `F^{(p,q)}` of Lemma 2.11 [lem:complex_cumu] commute with
multiplication by a constant. -/
private lemma EH_wirt_const_mul (c : ℂ) (f : ℂ → ℂ) (p q : ℕ) :
    wirt p q (fun w => c * f w) = fun w => c * wirt p q f w := by
  have hd : ∀ g : ℂ → ℂ, dW (fun w => c * g w) = fun w => c * dW g w := by
    intro g
    have e : (fun w => c * g w) = c • g := rfl
    funext w
    simp only [dW, e, fderiv_const_smul_field, Pi.smul_apply, _root_.smul_apply,
      smul_eq_mul]
    ring
  have hdb : ∀ g : ℂ → ℂ, dWbar (fun w => c * g w) = fun w => c * dWbar g w := by
    intro g
    have e : (fun w => c * g w) = c • g := rfl
    funext w
    simp only [dWbar, e, fderiv_const_smul_field, Pi.smul_apply, _root_.smul_apply,
      smul_eq_mul]
    ring
  have hb : ∀ (n : ℕ) (g : ℂ → ℂ), dWbar^[n] (fun w => c * g w) = fun w => c * dWbar^[n] g w := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, hdb, ih, Function.iterate_succ_apply]
  have ha : ∀ (n : ℕ) (g : ℂ → ℂ), dW^[n] (fun w => c * g w) = fun w => c * dW^[n] g w := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, hd, ih, Function.iterate_succ_apply]
  unfold wirt
  rw [hb, ha]

/-- `x ≤ 1/s + s x²` for `s > 0`, `x ≥ 0`. -/
private lemma EH_amgm {x s : ℝ} (hs : 0 < s) (hx : 0 ≤ x) : x ≤ 1 / s + s * x ^ 2 := by
  rw [div_add' _ _ _ hs.ne', le_div_iff₀ hs]
  nlinarith [sq_nonneg (s * x - 1), mul_nonneg hs.le hx]

/-- Lemma 2.11 [lem:complex_cumu], (2.26) [5.16], for one entry of a member of the class with a
high-probability remainder, for a general function `F`: let `χ` be a cutoff with values in
`[0, 1]`, constant along the entry `(i, j)`, with `χ ≠ 1` on an event of probability `≤ ε₁`, and
let `F ∘ symArr`, `χ ∘ symArr` be of class `C^{l+1}`. If the derivatives of order `l + 1` of
`w ↦ F(setEntry h i j w)` are bounded by `A` for Hermitian `h` with `χ(h) ≠ 0` and `|w| ≤ M`, and
those of order `≤ l + 1` by `B` for all Hermitian `h`, then the expansion of `E F(h) h̄_{ij}` to
order `l` holds with the remainder `K (N^{-(l+2)/2} A + B (ε₁ + (N^{1/2} M)^{-k})^{1/2})`, `K`
depending on `l`, `k` and `C` only. -/
theorem expansion_hp_gen (l k : ℕ) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → ∀ (i j : Idx D N) (F : (Idx D N → Idx D N → ℂ) → ℂ)
      (χ : (Idx D N → Idx D N → ℂ) → ℝ) (M A B ε₁ : ℝ),
      ContDiff ℝ (l + 1 : ℕ) (fun h => F (symArr h)) →
      ContDiff ℝ (l + 1 : ℕ) (fun h => χ (symArr h)) →
      (∀ h, χ h ∈ Set.Icc (0 : ℝ) 1) → (∀ h (w : ℂ), χ (setEntry h i j w) = χ h) →
      0 < M → 0 ≤ A → 0 ≤ ε₁ →
      (∀ p q : ℕ, p + q = l + 1 → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        χ h ≠ 0 → ∀ w : ℂ, ‖w‖ ≤ M → ‖wirt p q (fun w' => F (setEntry h i j w')) w‖ ≤ A) →
      (∀ p q : ℕ, p + q ≤ l + 1 → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        ∀ w : ℂ, ‖wirt p q (fun w' => F (setEntry h i j w')) w‖ ≤ B) →
      μ {h | χ h ≠ 1} ≤ ENNReal.ofReal ε₁ →
      ‖(∫ h, F h * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
              ∫ h, wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ‖ ≤
        K * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A +
          B * Real.sqrt (ε₁ + ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)))) := by
  obtain ⟨K₀, hK₀⟩ := llClass_expansion_sym l
  choose Kc hKc using fun p q => llClass_ccum_le C p q
  have hCp : ∀ n, 0 ≤ max (C n) 0 := fun n => le_max_right _ _
  have hKs : 0 ≤ ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      max (Kc p (q + 1)) 0 :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => le_max_right _ _
  have hK₀0 : 0 ≤ max K₀ 0 := le_max_right _ _
  refine ⟨max K₀ 0 * max (C (l + 2)) 0 +
      max K₀ 0 * (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) + (1 + max (C 2) 0) +
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), max (Kc p (q + 1)) 0,
    by have := hCp (l + 2); have := hCp (l + 2 + k); have := hCp 2; positivity, ?_⟩
  intro D N θ μ hμ i j F χ M A B ε₁ hF hχ hχI hχc hM hA0 hε₁ hA hB hS
  have hprob := hμ.prob
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Fin.pos i.2
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0 (by omega) 0 Matrix.isHermitian_zero 0)
  -- the scales `σ = (N^{1/2} M)^{-k}` and `v = ε₁ + σ`
  have hσ0 : 0 < ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) :=
    Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hN0 _) hM) _
  set σ := ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) with hσ
  have hv : 0 < ε₁ + σ := by linarith
  have hsv : 0 < Real.sqrt (ε₁ + σ) := Real.sqrt_pos.mpr hv
  set sv := Real.sqrt (ε₁ + σ) with hsvdef
  have hpow : ∀ x : ℝ, x ≤ 0 → (N : ℝ) ^ x ≤ 1 := fun x hx =>
    Real.rpow_le_one_of_one_le_of_nonpos hN hx
  -- a measurable event outside which `χ = 1`
  set T := toMeasurable μ {h | χ h ≠ 1} with hTdef
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hTc : ∀ h, h ∉ T → χ h = 1 := fun h hh => by
    by_contra hc
    exact hh (subset_toMeasurable _ _ hc)
  have hTε : μ.real T ≤ ε₁ := by
    rw [measureReal_def, hTdef, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε₁ hS
  have hTsv : μ.real T ≤ sv := by
    have := EH_le_sqrt zero_le_one hv.le (measureReal_le_one (μ := μ) (s := T))
      (by linarith)
    simpa using this
  -- almost every array is Hermitian
  have hherm := hμ.herm
  have hFslice : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      (fun w => F (setEntry h i j w)) = fun w => F (symArr (setEntry h i j w)) := by
    intro h hh
    funext w
    rw [EH_symArr_slice h hh i j w]
  have hFb : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ‖F h‖ ≤ B := by
    intro h hh
    have := hB 0 0 (by omega) h hh (h i j)
    simp only [wirt, Function.iterate_zero, id, EH_setEntry_self h hh] at this
    exact this
  have hwb : ∀ p q : ℕ, p + q ≤ l + 1 → ∀ h : Idx D N → Idx D N → ℂ,
      (Matrix.of h).IsHermitian → ‖wirt p q (fun w' => F (setEntry h i j w')) (h i j)‖ ≤ B :=
    fun p q hpq h hh => hB p q hpq h hh (h i j)
  have hχn : ∀ h, ‖(χ h : ℂ)‖ ≤ 1 := by
    intro h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hχI h).1, (hχI h).2]
  have hχn' : ∀ h, ‖(1 : ℂ) - (χ h : ℂ)‖ ≤ 1 := by
    intro h
    have e : (1 : ℂ) - (χ h : ℂ) = ((1 - χ h : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hχI h).1, (hχI h).2]
  -- measurability
  have hFm : AEStronglyMeasurable F μ :=
    hF.continuous.aestronglyMeasurable.congr (by
      filter_upwards [hherm] with h hh
      rw [symArr_of_isHermitian h hh])
  have hχm : AEStronglyMeasurable χ μ :=
    hχ.continuous.aestronglyMeasurable.congr (by
      filter_upwards [hherm] with h hh
      rw [symArr_of_isHermitian h hh])
  have hχm' : AEStronglyMeasurable (fun h => (χ h : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hχm
  have hent : Continuous fun h : Idx D N → Idx D N → ℂ => h i j :=
    (continuous_apply j).comp (continuous_apply i)
  have hconjm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ :=
    (Complex.continuous_conj.comp hent).aestronglyMeasurable
  have hH : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞)
      (fun x : (Idx D N → Idx D N → ℂ) × ℂ => F (symArr (setEntry x.1 i j x.2))) :=
    hF.comp (EH_contDiff_setEntry i j _)
  have hwm : ∀ p q : ℕ, p + q ≤ l + 1 → AEStronglyMeasurable
      (fun h : Idx D N → Idx D N → ℂ => wirt p q (fun w' => F (setEntry h i j w')) (h i j)) μ := by
    intro p q hpq
    have hc := (EH_wirt_continuous _ l hH p q hpq).comp (continuous_id.prodMk hent)
    refine hc.aestronglyMeasurable.congr ?_
    filter_upwards [hherm] with h hh
    simp only [Function.comp_apply, id]
    rw [hFslice h hh]
  -- integrability
  have hhint : Integrable (fun h : Idx D N → Idx D N → ℂ => ‖h i j‖) μ := by
    simpa using hμ.integrable 1 i j
  have hI1 : Integrable (fun h => F h * starRingEnd ℂ (h i j)) μ := by
    refine (hhint.const_mul B).mono' (hFm.mul hconjm) ?_
    filter_upwards [hherm] with h hh
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hFb h hh) (norm_nonneg _)
  have hI2 : Integrable (fun h => (χ h : ℂ) * F h * starRingEnd ℂ (h i j)) μ := by
    refine (hhint.const_mul B).mono' ((hχm'.mul hFm).mul hconjm) ?_
    filter_upwards [hherm] with h hh
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (hχn h)).trans (hFb h hh)) (norm_nonneg _)
  have hI3 : ∀ p q : ℕ, p + q ≤ l + 1 → Integrable
      (fun h : Idx D N → Idx D N → ℂ => wirt p q (fun w' => F (setEntry h i j w')) (h i j)) μ := by
    intro p q hpq
    refine (integrable_const B).mono' (hwm p q hpq) ?_
    filter_upwards [hherm] with h hh
    exact hwb p q hpq h hh
  have hI4 : ∀ p q : ℕ, p + q ≤ l + 1 → Integrable
      (fun h : Idx D N → Idx D N → ℂ =>
        (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) (h i j)) μ := by
    intro p q hpq
    refine (integrable_const B).mono' (hχm'.mul (hwm p q hpq)) ?_
    filter_upwards [hherm] with h hh
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn h)).trans (hwb p q hpq h hh)
  -- the expansion for `Φ = χ F`
  have hΦslice : ∀ (h : Idx D N → Idx D N → ℂ) (p q : ℕ),
      wirt p q (fun w' => (χ (setEntry h i j w') : ℂ) * F (setEntry h i j w')) =
        fun w => (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) w := by
    intro h p q
    have e : (fun w' => (χ (setEntry h i j w') : ℂ) * F (setEntry h i j w')) =
        fun w' => (χ h : ℂ) * F (setEntry h i j w') := by
      funext w'
      rw [hχc h w']
    rw [e, EH_wirt_const_mul]
  have hΦcd : ContDiff ℝ (l + 1 : ℕ) (fun h => (χ (symArr h) : ℂ) * F (symArr h)) :=
    (Complex.ofRealCLM.contDiff.comp hχ).mul hF
  have key := hK₀ D N C θ μ hμ i j (fun h => (χ h : ℂ) * F h) M A B hΦcd hM
    (fun p q hpq h hh w hw => by
      rw [hΦslice, norm_mul]
      by_cases h0 : χ h = 0
      · simp [h0, hA0]
      · exact (mul_le_of_le_one_left (norm_nonneg _) (hχn h)).trans (hA p q hpq h hh h0 w hw))
    (fun p q hpq h hh w => by
      rw [hΦslice, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχn h)).trans (hB p q hpq h hh w))
  simp only [hΦslice] at key
  -- the moment and tail terms
  have hE2 : ∫ h, ‖h i j‖ ^ (l + 2) ∂μ ≤ max (C (l + 2)) 0 * (N : ℝ) ^ (-((l : ℝ) + 2) / 2) := by
    have e : -((((l + 2 : ℕ)) : ℝ) / 2) = -((l : ℝ) + 2) / 2 := by push_cast; ring
    have := hμ.moments (l + 2) i j
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _))
  have hE20 : 0 ≤ ∫ h, ‖h i j‖ ^ (l + 2) ∂μ := integral_nonneg fun h => by positivity
  have hmom : ∀ n : ℕ, ∫ h, ‖h i j‖ ^ n ∂μ ≤ max (C n) 0 := by
    intro n
    refine (hμ.moments n i j).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left (C n) 0) (Real.rpow_nonneg hN0.le _)).trans ?_
    exact mul_le_of_le_one_right (le_max_right _ _) (hpow _ (by
      have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      linarith))
  set Tl := ∫ h, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ∂μ with hTl
  have hind0 : ∀ h : Idx D N → Idx D N → ℂ,
      0 ≤ Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) :=
    fun h => Set.indicator_nonneg (fun w _ => by positivity) _
  have hTl0 : 0 ≤ Tl := integral_nonneg hind0
  have hTl1 : Tl ≤ max (C (l + 2)) 0 := by
    refine (integral_mono_of_nonneg (ae_of_all _ hind0) (hμ.integrable (l + 2) i j)
      (ae_of_all _ fun h => ?_)).trans (hmom (l + 2))
    exact Set.indicator_le_self' (fun w _ => by positivity) (h i j)
  have hTl2 : Tl ≤ max (C (l + 2 + k)) 0 * σ := by
    have hMk : 0 < M ^ k := pow_pos hM k
    have hpt : ∀ h : Idx D N → Idx D N → ℂ,
        Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ≤
          ‖h i j‖ ^ (l + 2 + k) / M ^ k := by
      intro h
      by_cases hm : M < ‖h i j‖
      · rw [Set.indicator_of_mem (by exact hm)]
        rw [le_div_iff₀ hMk, pow_add ‖h i j‖ (l + 2) k]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le hm.le k) (by positivity)
      · rw [Set.indicator_of_notMem (by exact hm)]
        positivity
    have h1 : Tl ≤ (∫ h, ‖h i j‖ ^ (l + 2 + k) ∂μ) / M ^ k := by
      rw [← integral_div]
      exact integral_mono_of_nonneg (ae_of_all _ hind0)
        ((hμ.integrable (l + 2 + k) i j).div_const _) (ae_of_all _ hpt)
    refine h1.trans ?_
    rw [div_le_iff₀ hMk]
    have h2 := hμ.moments (l + 2 + k) i j
    have h3 : (N : ℝ) ^ (-(((l + 2 + k : ℕ) : ℝ) / 2)) ≤ (N : ℝ) ^ (-((k : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by
        push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
    have h4 : σ * M ^ k = (N : ℝ) ^ (-((k : ℝ) / 2)) := by
      rw [hσ, ← EH_rpow_eq hN0 hM k, div_mul_cancel₀ _ hMk.ne']
    calc ∫ h, ‖h i j‖ ^ (l + 2 + k) ∂μ
        ≤ C (l + 2 + k) * (N : ℝ) ^ (-(((l + 2 + k : ℕ) : ℝ) / 2)) := h2
      _ ≤ max (C (l + 2 + k)) 0 * (N : ℝ) ^ (-(((l + 2 + k : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _)
      _ ≤ max (C (l + 2 + k)) 0 * (N : ℝ) ^ (-((k : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h3 (hCp _)
      _ = max (C (l + 2 + k)) 0 * σ * M ^ k := by rw [mul_assoc, h4]
  have hTl : Tl ≤ (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) * sv := by
    have h1 := EH_le_sqrt (add_nonneg (hCp (l + 2)) (hCp (l + 2 + k))) hσ0.le
      (hTl1.trans (le_add_of_nonneg_right (hCp _)))
      (hTl2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hCp _)) hσ0.le))
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (add_nonneg (hCp _) (hCp _)))
    exact Real.sqrt_le_sqrt (by linarith)
  have hkey : ‖(∫ h, (χ h : ℂ) * F h * starRingEnd ℂ (h i j) ∂μ) -
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          ∫ h, (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ‖ ≤
      max K₀ 0 * (max (C (l + 2)) 0 * (N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A +
        (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) * sv * B) := by
    refine key.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) (by positivity)).trans ?_
    gcongr
  have hTi : Integrable (fun h => T.indicator (1 : (Idx D N → Idx D N → ℂ) → ℝ) h) μ :=
    (integrable_indicator_iff hTm).mpr (integrable_const (1 : ℝ)).integrableOn
  -- removing the cutoff from the main term
  have hmain : ‖(∫ h, F h * starRingEnd ℂ (h i j) ∂μ) -
      ∫ h, (χ h : ℂ) * F h * starRingEnd ℂ (h i j) ∂μ‖ ≤ (1 + max (C 2) 0) * sv * B := by
    rw [← integral_sub hI1 hI2]
    have hg : Integrable (fun h : Idx D N → Idx D N → ℂ =>
        B * (T.indicator 1 h * (1 / sv) + sv * ‖h i j‖ ^ 2)) μ :=
      (hTi.mul_const _
        |>.add ((hμ.integrable 2 i j).const_mul _)).const_mul _
    refine (norm_integral_le_of_norm_le hg ?_).trans ?_
    · filter_upwards [hherm] with h hh
      have e : F h * starRingEnd ℂ (h i j) - (χ h : ℂ) * F h * starRingEnd ℂ (h i j) =
          (1 - (χ h : ℂ)) * F h * starRingEnd ℂ (h i j) := by ring
      rw [e, norm_mul, norm_mul, Complex.norm_conj]
      by_cases hT : h ∈ T
      · rw [Set.indicator_of_mem hT, Pi.one_apply, one_mul]
        calc ‖1 - (χ h : ℂ)‖ * ‖F h‖ * ‖h i j‖ ≤ 1 * B * ‖h i j‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul (hχn' h) (hFb h hh) (norm_nonneg _)
                zero_le_one) (norm_nonneg _)
          _ ≤ B * (1 / sv + sv * ‖h i j‖ ^ 2) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left (EH_amgm hsv (norm_nonneg _)) hB0
      · rw [hTc h hT]
        simp only [Complex.ofReal_one, sub_self, norm_zero, zero_mul, Set.indicator_of_notMem hT]
        positivity
    · rw [integral_const_mul, integral_add
        (hTi.mul_const _)
        ((hμ.integrable 2 i j).const_mul _), integral_mul_const, integral_indicator_one hTm,
        integral_const_mul]
      have h2 := hmom 2
      have h3 : μ.real T * (1 / sv) ≤ sv := by
        rw [mul_one_div, div_le_iff₀ hsv, hsvdef, Real.mul_self_sqrt hv.le]
        linarith
      have h4 : sv * ∫ h, ‖h i j‖ ^ 2 ∂μ ≤ sv * max (C 2) 0 :=
        mul_le_mul_of_nonneg_left h2 hsv.le
      nlinarith
  -- removing the cutoff from the cumulant terms
  have hcum : ∀ p ∈ Finset.range (l + 1), ∀ q ∈ Finset.range (l + 1 - p),
      ‖ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          ((∫ h, wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ) -
            ∫ h, (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ)‖ ≤
        max (Kc p (q + 1)) 0 * (sv * B) := by
    intro p hp q hq
    have hpq : p + q ≤ l + 1 := by
      have := Finset.mem_range.mp hp
      have := Finset.mem_range.mp hq
      omega
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (le_max_right _ _)
    · rw [norm_div]
      have hf : (1 : ℝ) ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
        rw [Complex.norm_natCast]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero p)
          (Nat.factorial_ne_zero q))
      refine (div_le_self (norm_nonneg _) hf).trans ?_
      refine (hKc p (q + 1) D N θ μ hμ i j).trans ?_
      refine (mul_le_mul_of_nonneg_right (le_max_left (Kc p (q + 1)) 0)
        (Real.rpow_nonneg hN0.le _)).trans ?_
      exact mul_le_of_le_one_right (le_max_right _ _) (hpow _ (by
        have : (0 : ℝ) ≤ (((p + (q + 1) : ℕ) : ℝ)) / 2 := by positivity
        linarith))
    · rw [← integral_sub (hI3 p q hpq) (hI4 p q hpq)]
      have hg : Integrable (fun h : Idx D N → Idx D N → ℂ => B * T.indicator 1 h) μ :=
        hTi.const_mul _
      refine (norm_integral_le_of_norm_le hg ?_).trans ?_
      · filter_upwards [hherm] with h hh
        have e : wirt p q (fun w' => F (setEntry h i j w')) (h i j) -
            (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) (h i j) =
            (1 - (χ h : ℂ)) * wirt p q (fun w' => F (setEntry h i j w')) (h i j) := by ring
        rw [e, norm_mul]
        by_cases hT : h ∈ T
        · rw [Set.indicator_of_mem hT, Pi.one_apply, mul_one]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hχn' h)).trans (hwb p q hpq h hh)
        · rw [hTc h hT, Set.indicator_of_notMem hT]
          simp
      · rw [integral_const_mul, integral_indicator_one hTm, mul_comm]
        exact mul_le_mul_of_nonneg_right hTsv hB0
  -- assembling the three errors
  have hsplit : ∀ (a b : ℂ) (u v : ℕ → ℕ → ℂ),
      a - ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) * u p q =
      (b - ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) * v p q) +
        (a - b) - ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
            (u p q - v p q) := by
    intro a b u v
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit _ (∫ h, (χ h : ℂ) * F h * starRingEnd ℂ (h i j) ∂μ) _
    (fun p q => ∫ h, (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ)]
  have hsum : ‖∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          ((∫ h, wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ) -
            ∫ h, (χ h : ℂ) * wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ)‖ ≤
      (∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), max (Kc p (q + 1)) 0) *
        (sv * B) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => hcum p hp q hq)
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hX : 0 ≤ (N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) hA0
  have hY : 0 ≤ B * sv := mul_nonneg hB0 hsv.le
  have e1 : max K₀ 0 * (max (C (l + 2)) 0 * (N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A +
      (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) * sv * B) =
      max K₀ 0 * max (C (l + 2)) 0 * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A) +
        max K₀ 0 * (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) * (B * sv) := by ring
  have hfin := add_le_add (add_le_add hkey hmain) hsum
  rw [e1] at hfin
  refine hfin.trans (le_of_sub_nonneg ?_)
  have hc1 := mul_nonneg (mul_nonneg hK₀0 (hCp (l + 2))) hY
  have hc2 := mul_nonneg (mul_nonneg hK₀0 (add_nonneg (hCp (l + 2)) (hCp (l + 2 + k)))) hX
  have hc3 := mul_nonneg (add_nonneg zero_le_one (hCp 2)) hX
  have hc4 := mul_nonneg hKs hX
  have e2 : (max K₀ 0 * max (C (l + 2)) 0 +
      max K₀ 0 * (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) + (1 + max (C 2) 0) +
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), max (Kc p (q + 1)) 0) *
        ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A + B * sv) -
      (max K₀ 0 * max (C (l + 2)) 0 * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A) +
        max K₀ 0 * (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) * (B * sv) +
        (1 + max (C 2) 0) * sv * B +
        (∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), max (Kc p (q + 1)) 0) *
          (sv * B)) =
      max K₀ 0 * max (C (l + 2)) 0 * (B * sv) +
        max K₀ 0 * (max (C (l + 2)) 0 + max (C (l + 2 + k)) 0) *
          ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A) +
        (1 + max (C 2) 0) * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A) +
        (∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), max (Kc p (q + 1)) 0) *
          ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * A) := by ring
  rw [e2]
  positivity

/-- Lemma 2.11 [lem:complex_cumu], (2.26) [5.16], for a resolvent polynomial `P` of degree `≤ m`
over a finite set `V ∋ e_i, e_j` of vectors of norm `≤ 1` and a finite family `Ξ` of pairs
`(Λ, ξ)` with `Λ` Hermitian and `Im ξ ≥ η > 0`, every factor carrying a pair of `Ξ` or its
conjugate `(Λ, ξ̄)`, with a high-probability remainder: if `|x^* (h + Λ - ξ)⁻¹ y| ≤ Γ` (`Γ ≥ 1`) for
`x, y ∈ V` and every pair off an event of probability `≤ ε₀`, and `24 M Γ ≤ 1`, then the expansion
of `E P(h) h̄_{ij}` to order `l` holds with the remainder `K (Σ_t |c_t|) (N^{-(l+2)/2} (6Γ)^{m+l+1}
+ (1 + η⁻¹)^{m+l+1} (ε₀ + (N^{1/2} M)^{-k})^{1/2})`, `K` depending on `l`, `m`, `k` and `C`
only. -/
theorem expansion_hp (l m k : ℕ) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → ∀ (Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (η : ℝ), 0 < η →
      (∀ p ∈ Ξ, p.1.IsHermitian ∧ η ≤ p.2.im) →
      ∀ (i j : Idx D N) (V : Finset (Idx D N → ℂ)),
      Pi.single i 1 ∈ V → Pi.single j 1 ∈ V → (∀ x ∈ V, ∑ r, ‖x r‖ ^ 2 ≤ 1) →
      ∀ P : ResPoly D N, (∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧
        ∃ p ∈ Ξ, f.2.2 = p ∨ f.2.2 = (p.1, starRingEnd ℂ p.2)) →
      ∀ Γ M ε₀ : ℝ, 1 ≤ Γ → 0 < M → 24 * M * Γ ≤ 1 → 0 ≤ ε₀ →
      μ {h | ∃ p ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V,
          Γ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ≤ ENNReal.ofReal ε₀ →
      ‖(∫ h, resPolyEval P h * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
              ∫ h, wirt p q (fun w => resPolyEval P (setEntry h i j w)) (h i j) ∂μ‖ ≤
        K * (P.map fun t => ‖t.1‖).sum *
          ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * Γ) ^ (m + l + 1) +
            (1 + η⁻¹) ^ (m + l + 1) *
              Real.sqrt (ε₀ + ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)))) := by
  obtain ⟨Kg, hKg0, hKg⟩ := expansion_hp_gen l k C
  obtain ⟨Kk, hKk0, hKk⟩ := hpCut_ne_one_le k C
  have hc0 : (0 : ℝ) ≤ ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) := by positivity
  refine ⟨Kg * ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * Real.sqrt (1 + Kk), by positivity, ?_⟩
  intro D N θ μ hμ Ξ η hη hΞ i j V hi hj hV P hP Γ M ε₀ hΓ hM hMΓ hε₀ hbad
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Fin.pos i.2
  have hΞpos : ∀ p ∈ Ξ, p.1.IsHermitian ∧ 0 < p.2.im :=
    fun p hp => ⟨(hΞ p hp).1, hη.trans_le (hΞ p hp).2⟩
  have hΞne : ∀ p ∈ Ξ, p.1.IsHermitian ∧ p.2.im ≠ 0 :=
    fun p hp => ⟨(hΞpos p hp).1, (hΞpos p hp).2.ne'⟩
  -- the pairs of `Ξ` and their conjugates
  set Ξ' : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
    {q | ∃ p ∈ Ξ, q = p ∨ q = (p.1, starRingEnd ℂ p.2)} with hΞ'def
  have hΞ' : ∀ q ∈ Ξ', q.1.IsHermitian ∧ q.2.im ≠ 0 := by
    rintro q ⟨p, hp, hq | hq⟩ <;> rw [hq]
    · exact hΞne p hp
    · exact ⟨(hΞpos p hp).1, by simp [(hΞpos p hp).2.ne']⟩
  have hP' : ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ (V : Set (Idx D N → ℂ)) ∧
      f.2.1 ∈ (V : Set (Idx D N → ℂ)) ∧ f.2.2 ∈ Ξ' := by
    intro t ht
    refine ⟨(hP t ht).1, fun f hf => ?_⟩
    obtain ⟨h1, h2, p, hp, h3⟩ := (hP t ht).2 f hf
    exact ⟨Finset.mem_coe.mpr h1, Finset.mem_coe.mpr h2, p, hp, h3⟩
  have hPf : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 :=
    fun t ht f hf => hΞ' _ ((hP' t ht).2 f hf).2.2
  have hconj : ∀ h' : Idx D N → Idx D N → ℂ, (Matrix.of h').IsHermitian → ∀ b : ℝ,
      (∀ p ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, p.1, p.2) h'‖ ≤ b) →
      ∀ q ∈ Ξ', ∀ x ∈ (V : Set (Idx D N → ℂ)), ∀ y ∈ (V : Set (Idx D N → ℂ)),
        ‖resFactorEval (x, y, q.1, q.2) h'‖ ≤ b := by
    rintro h' hh' b hb q ⟨p, hp, hq | hq⟩ x hx y hy <;> rw [hq]
    · exact hb p hp x hx y hy
    · rw [EH_form_conj x y p.1 (hΞpos p hp).1 p.2 (hΞpos p hp).2 h' hh']
      exact hb p hp y hy x hx
  have hL0 : 0 ≤ (P.map fun t => ‖t.1‖).sum := List.sum_nonneg fun x hx => by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hη1 : 1 ≤ 1 + η⁻¹ := by linarith [inv_nonneg.mpr hη.le]
  have hMΓ' : 4 * M * Γ ≤ 1 / 2 := by nlinarith
  have hS := hKk D N θ μ hμ Ξ hΞpos i j V hi hj Γ M ε₀ hM hMΓ' hε₀ hbad
  have hσ0 : 0 ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) hM.le) _
  set σ := ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) with hσ
  have key := hKg D N θ μ hμ i j (resPolyEval P) (hpCut Ξ V Γ i j) M
    (((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (6 * Γ) ^ (m + l + 1))
    (((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (1 + η⁻¹) ^ (m + l + 1))
    (ε₀ + Kk * σ) (contDiff_resPoly_symArr P hPf (l + 1))
    ((hpCut_contDiff Ξ hΞne V Γ i j (l + 1)).comp (EH_contDiff_symArr _))
    (hpCut_mem_Icc Ξ V Γ i j) (hpCut_setEntry Ξ V Γ i j) hM
    (by have : (0 : ℝ) ≤ Γ := by linarith
        positivity)
    (by positivity)
    (fun a b hab h hh hχ w hw => by
      have hfo := hpCut_ne_zero_le Ξ hΞpos h hh i j V hi hj M Γ (by linarith) hMΓ hχ w hw
      have := resPoly_wirt_le h hh i j (V : Set (Idx D N → ℂ)) Ξ' (Finset.mem_coe.mpr hi)
        (Finset.mem_coe.mpr hj) hΞ' P m hP' (6 * Γ) (by linarith) w
        (hconj (setEntry h i j w) (EH_setEntry_herm h hh i j w) (6 * Γ) hfo) a b
      rw [show m + a + b = m + l + 1 by omega, hab] at this
      exact this)
    (fun a b hab h hh w => by
      have hh' := EH_setEntry_herm h hh i j w
      have hfo : ∀ p ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V,
          ‖resFactorEval (x, y, p.1, p.2) (setEntry h i j w)‖ ≤ 1 + η⁻¹ := by
        intro p hp x hx y hy
        have h1 := EH_form_le_opNorm (res (Matrix.of (setEntry h i j w) + p.1) p.2) x y
          (hV x hx) (hV y hy)
        have h2 := opNorm_res_le _ (hh'.add (hΞpos p hp).1) p.2 (hΞpos p hp).2
        have h3 : p.2.im⁻¹ ≤ η⁻¹ := inv_anti₀ hη (hΞ p hp).2
        exact h1.trans (h2.trans (h3.trans (by linarith)))
      have := resPoly_wirt_le h hh i j (V : Set (Idx D N → ℂ)) Ξ' (Finset.mem_coe.mpr hi)
        (Finset.mem_coe.mpr hj) hΞ' P m hP' (1 + η⁻¹) hη1 w (hconj _ hh' _ hfo) a b
      refine this.trans ?_
      have hc : ((m + a + b : ℕ) : ℝ) ^ (a + b) ≤ ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) :=
        calc ((m + a + b : ℕ) : ℝ) ^ (a + b) ≤ ((m + l + 1 : ℕ) : ℝ) ^ (a + b) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega)) _
          _ ≤ ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) :=
              pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ m + l + 1)) hab
      have hp : (1 + η⁻¹) ^ (m + a + b) ≤ (1 + η⁻¹) ^ (m + l + 1) :=
        pow_le_pow_right₀ hη1 (by omega)
      gcongr)
    hS
  refine key.trans ?_
  have hsq : Real.sqrt (ε₀ + Kk * σ + σ) ≤ Real.sqrt (1 + Kk) * Real.sqrt (ε₀ + σ) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs1 : 1 ≤ Real.sqrt (1 + Kk) := Real.one_le_sqrt.mpr (by linarith)
  have hX : 0 ≤ (N : ℝ) ^ (-((l : ℝ) + 2) / 2) := Real.rpow_nonneg hN0.le _
  have hY : 0 ≤ (6 * Γ) ^ (m + l + 1) := by
    have : (0 : ℝ) ≤ Γ := by linarith
    positivity
  have hZ : 0 ≤ (1 + η⁻¹) ^ (m + l + 1) := by positivity
  have hW : 0 ≤ Real.sqrt (ε₀ + σ) := Real.sqrt_nonneg _
  calc Kg * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) *
          (((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (6 * Γ) ^ (m + l + 1)) +
        ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (1 + η⁻¹) ^ (m + l + 1) *
          Real.sqrt (ε₀ + Kk * σ + σ))
      ≤ Kg * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) *
          (((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (6 * Γ) ^ (m + l + 1)) +
        ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (1 + η⁻¹) ^ (m + l + 1) *
          (Real.sqrt (1 + Kk) * Real.sqrt (ε₀ + σ))) := by gcongr
    _ ≤ Kg * ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * Real.sqrt (1 + Kk) *
          (P.map fun t => ‖t.1‖).sum *
          ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * Γ) ^ (m + l + 1) +
            (1 + η⁻¹) ^ (m + l + 1) * Real.sqrt (ε₀ + σ)) := by
      have e : Kg * ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * Real.sqrt (1 + Kk) *
          (P.map fun t => ‖t.1‖).sum *
          ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * Γ) ^ (m + l + 1) +
            (1 + η⁻¹) ^ (m + l + 1) * Real.sqrt (ε₀ + σ)) -
          Kg * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) *
          (((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (6 * Γ) ^ (m + l + 1)) +
        ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum * (1 + η⁻¹) ^ (m + l + 1) *
          (Real.sqrt (1 + Kk) * Real.sqrt (ε₀ + σ))) =
          Kg * ((m + l + 1 : ℕ) : ℝ) ^ (l + 1) * (P.map fun t => ‖t.1‖).sum *
            ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * Γ) ^ (m + l + 1)) *
            (Real.sqrt (1 + Kk) - 1) := by ring
      have hs1' : 0 ≤ Real.sqrt (1 + Kk) - 1 := by linarith
      refine le_of_sub_nonneg ?_
      rw [e]
      positivity

end RBMTransitionEdge

end
