module

public import RBMTransitionEdge.Flow.Chain
public import RBMTransitionEdge.Flow.TOp
public import RBMTransitionEdge.Prob.GridAFlow

@[expose] public section

/-!
# Regularity of the resolvent loops along the characteristic flow

The Hermitian part of an array, the loops `⟨B₁G₁⋯B_pG_p⟩` along the flow (3.10)
[eq:deterflow], their global `C⁴` bounds on all arrays, and their joint regularity in the time and
the array, as inputs of the single-step expansion of the flow (3.12) [eq:Ht].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The Hermitian part `(h + h^*)/2` of an array; it is the identity on Hermitian arrays and
extends the resolvent loops smoothly to all arrays. -/
def hermPart {ι : Type*} (h : ι → ι → ℂ) : ι → ι → ℂ :=
  fun i j => (h i j + star (h j i)) / 2

/-- The loop `⟨B₁G₁⋯B_pG_p⟩` along the flow (3.10) [eq:deterflow] at time `s`, listed as
`(B_r, z_r)`: `G_r = (h + Λ_s - z_{r,s})⁻¹` with `Λ_s = e^{-s/2} Λ` and `z_{r,s}` the closed-form
flow of `z_r`, at the Hermitian part of the array `h`. -/
def flowLoop {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (s : ℝ) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ntr (chainB (hermPart h)
    (l.map fun f => (f.1, ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ, charFlowZ Λ f.2 s)))

section Abstract

variable {E 𝒜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝒜]
  [NormedAlgebra ℝ 𝒜]

/-- The bilinear map `(a, b) ↦ (v ↦ -(a · L v · b))`, the derivative of the inverse composed
with the linear map `L`. -/
private def LR_bilLin (L : E →L[ℝ] 𝒜) : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] (E →L[ℝ] 𝒜) :=
  LinearMap.mk₂ ℝ (fun a b => -((ContinuousLinearMap.mulLeftRight ℝ 𝒜 a b).comp L))
      (fun a a' b => by ext v; simp [add_comm])
      (fun c a b => by ext v; simp)
      (fun a b b' => by ext v; simp [add_comm])
      (fun c a b => by ext v; simp)

private lemma LR_bilLin_bound (L : E →L[ℝ] 𝒜) (a b : 𝒜) :
    ‖LR_bilLin L a b‖ ≤ ‖L‖ * ‖a‖ * ‖b‖ := by
  change ‖-((ContinuousLinearMap.mulLeftRight ℝ 𝒜 a b).comp L)‖ ≤ ‖L‖ * ‖a‖ * ‖b‖
  rw [norm_neg]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply]
  calc ‖a * L v * b‖ ≤ ‖a * L v‖ * ‖b‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * ‖L v‖ * ‖b‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖a‖ * (‖L‖ * ‖v‖) * ‖b‖ := by gcongr; exact L.le_opNorm v
    _ = ‖L‖ * ‖a‖ * ‖b‖ * ‖v‖ := by ring

/-- The continuous bilinear map `LR_bilLin`. -/
private def LR_bil (L : E →L[ℝ] 𝒜) : 𝒜 →L[ℝ] 𝒜 →L[ℝ] (E →L[ℝ] 𝒜) :=
  LinearMap.mkContinuous₂ (LR_bilLin L) ‖L‖ (LR_bilLin_bound L)

private lemma LR_bil_apply (L : E →L[ℝ] 𝒜) (a b : 𝒜) (v : E) :
    LR_bil L a b v = -(a * L v * b) := rfl

/-- The inverse of an affine family of invertible elements is smooth, and its derivatives satisfy
`‖D^j‖ ≤ j! K^j η^{-(j+1)}` when `‖L‖ ≤ K` and `‖(L w + c)⁻¹‖ ≤ η⁻¹`. -/
private lemma LR_inv_affine [CompleteSpace 𝒜] (L : E →L[ℝ] 𝒜) (c : 𝒜) (K η : ℝ)
    (hK : ‖L‖ ≤ K) (hη : 0 < η) (hu : ∀ w, IsUnit (L w + c))
    (hb : ∀ w, ‖Ring.inverse (L w + c)‖ ≤ η⁻¹) :
    (∀ n : ℕ, ContDiff ℝ n (fun w => Ring.inverse (L w + c))) ∧
    ∀ (j : ℕ) (w : E), ‖iteratedFDeriv ℝ j (fun w => Ring.inverse (L w + c)) w‖ ≤
      j.factorial * K ^ j * (η ^ (j + 1))⁻¹ := by
  set G : E → 𝒜 := fun w => Ring.inverse (L w + c) with hGdef
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hGd : ∀ w, HasFDerivAt G (LR_bil L (G w) (G w)) w := by
    intro w
    have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) (hu w).unit
    rw [IsUnit.unit_spec] at h1
    have h2 := h1.comp w (L.hasFDerivAt.add_const c)
    have h3 : ((hu w).unit⁻¹ : 𝒜ˣ).val = G w := by
      rw [← Ring.inverse_unit, IsUnit.unit_spec]
    rw [h3] at h2
    have h4 : (-((ContinuousLinearMap.mulLeftRight ℝ 𝒜) (G w)) (G w)).comp L =
        LR_bil L (G w) (G w) := by
      ext v
      simp [LR_bil_apply]
    rw [h4] at h2
    exact h2
  have hsm : ∀ n : ℕ, ContDiff ℝ n G := by
    intro n
    induction n with
    | zero =>
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun w => (hGd w).continuousAt)
    | succ n ih =>
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨fun w => LR_bil L (G w) (G w), ?_, hGd⟩
      exact ((LR_bil L).contDiff.comp ih).clm_apply ih
  refine ⟨hsm, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro w
  rcases j with _ | j
  · simp only [norm_iteratedFDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul,
      zero_add, pow_one]
    exact hb w
  · have hfd : fderiv ℝ G = fun w => LR_bil L (G w) (G w) := funext fun w => (hGd w).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (LR_bil L) (hsm j)
      (hsm j) w (n := j) le_rfl
    have h2 := LinearMap.mkContinuous₂_norm_le (LR_bilLin L) (norm_nonneg L)
      (LR_bilLin_bound L)
    have h3 := mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg
      (fun i (_ : i ∈ Finset.range (j + 1)) =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)) :
      0 ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i G w‖ *
        ‖iteratedFDeriv ℝ (j - i) G w‖)
    refine h1.trans (h3.trans ?_)
    have hterm : ∀ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i G w‖ *
        ‖iteratedFDeriv ℝ (j - i) G w‖ ≤ (j.factorial : ℝ) * K ^ j * (η ^ (j + 2))⁻¹ := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have b1 := ih i (by omega) w
      have b2 := ih (j - i) (by omega) w
      have hc : ((j.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((j - i).factorial : ℝ) =
          j.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
      have e1 : K ^ i * K ^ (j - i) = K ^ j := by rw [← pow_add]; congr 1; omega
      have e2 : (η ^ (i + 1))⁻¹ * (η ^ (j - i + 1))⁻¹ = (η ^ (j + 2))⁻¹ := by
        rw [← mul_inv, ← pow_add]; congr 2; omega
      calc ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i G w‖ * ‖iteratedFDeriv ℝ (j - i) G w‖
          ≤ ((j.choose i : ℕ) : ℝ) * ((i.factorial : ℝ) * K ^ i * (η ^ (i + 1))⁻¹) *
            (((j - i).factorial : ℝ) * K ^ (j - i) * (η ^ (j - i + 1))⁻¹) := by gcongr
        _ = (((j.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((j - i).factorial : ℝ)) *
            (K ^ i * K ^ (j - i)) * ((η ^ (i + 1))⁻¹ * (η ^ (j - i + 1))⁻¹) := by ring
        _ = (j.factorial : ℝ) * K ^ j * (η ^ (j + 2))⁻¹ := by rw [hc, e1, e2]
    calc ‖L‖ * ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i G w‖ *
          ‖iteratedFDeriv ℝ (j - i) G w‖
        ≤ K * ∑ i ∈ Finset.range (j + 1), (j.factorial : ℝ) * K ^ j * (η ^ (j + 2))⁻¹ :=
          mul_le_mul hK (Finset.sum_le_sum hterm) (Finset.sum_nonneg fun i _ => by positivity)
            hK0
      _ = ((j + 1).factorial : ℝ) * K ^ (j + 1) * (η ^ (j + 1 + 1))⁻¹ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.factorial_succ]
          push_cast
          ring

/-- The constants of the derivative bounds of a chain of `p` factors: `c(0, j) = δ_{j0}` and
`c(p + 1, j) = Σ_i C(j, i) i! c(p, j - i)`. -/
private def LR_cc : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | p + 1, j => ∑ i ∈ Finset.range (j + 1), j.choose i * i.factorial * LR_cc p (j - i)

/-- Derivative bounds of a product of factors `B_f G_f(w)`, by the Leibniz rule. -/
private lemma LR_prod_bound {α : Type*} (hone : ‖(1 : 𝒜)‖ ≤ 1) (K η : ℝ) (hK0 : 0 ≤ K)
    (hη : 0 < η) (Bf : α → 𝒜) (Gf : α → E → 𝒜) (l : List α)
    (hsm : ∀ f ∈ l, ∀ n : ℕ, ContDiff ℝ n (Gf f))
    (hbd : ∀ f ∈ l, ∀ (j : ℕ) (w : E), ‖iteratedFDeriv ℝ j (Gf f) w‖ ≤
      j.factorial * K ^ j * (η ^ (j + 1))⁻¹) :
    (∀ n : ℕ, ContDiff ℝ n (fun w => (l.map fun f => Bf f * Gf f w).prod)) ∧
    ∀ (j : ℕ) (w : E), ‖iteratedFDeriv ℝ j (fun w => (l.map fun f => Bf f * Gf f w).prod) w‖ ≤
      (LR_cc l.length j : ℝ) * K ^ j * (l.map fun f => ‖Bf f‖).prod *
        (η ^ (l.length + j))⁻¹ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    refine ⟨fun n => contDiff_const, fun j w => ?_⟩
    rcases j with _ | j
    · simp only [norm_iteratedFDeriv_zero, LR_cc, ↓reduceIte, Nat.cast_one, pow_zero,
        mul_one, add_zero, inv_one]
      exact hone
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
      simp [LR_cc]
  | cons f t ih =>
    have ih' := ih (fun g hg => hsm g (by simp [hg])) (fun g hg => hbd g (by simp [hg]))
    have hGf := hsm f (by simp)
    have hbf := hbd f (by simp)
    have heq : (fun w => ((f :: t).map fun f => Bf f * Gf f w).prod) =
        fun w => (Bf f * Gf f w) * (t.map fun f => Bf f * Gf f w).prod := by
      funext w; simp only [List.map_cons, List.prod_cons]
    rw [heq]
    have hP : ∀ n : ℕ, ContDiff ℝ n (fun w => Bf f * Gf f w) := fun n => contDiff_const.mul (hGf n)
    refine ⟨fun n => (hP n).mul (ih'.1 n), fun j w => ?_⟩
    refine (norm_iteratedFDeriv_mul_le (hP j) (ih'.1 j) w (n := j) le_rfl).trans ?_
    have hPb : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun w => Bf f * Gf f w) w‖ ≤
        ‖Bf f‖ * ‖iteratedFDeriv ℝ i (Gf f) w‖ := by
      intro i
      have h1 : ‖iteratedFDeriv ℝ i (fun w => Bf f * Gf f w) w‖ ≤
          ‖ContinuousLinearMap.mul ℝ 𝒜 (Bf f)‖ * ‖iteratedFDeriv ℝ i (Gf f) w‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.mul ℝ 𝒜 (Bf f))
          (f := Gf f) (x := w) (N := i) (n := i) ((hGf i).contDiffAt) le_rfl
      exact h1.trans (mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_mul_apply_le ℝ 𝒜 (Bf f)) (norm_nonneg _))
    have hprod : 0 ≤ (t.map fun f => ‖Bf f‖).prod := by
      refine List.prod_nonneg ?_
      intro x hx
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg _
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i (fun w => Bf f * Gf f w) w‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun w => (t.map fun f => Bf f * Gf f w).prod) w‖ ≤
        ((j.choose i * i.factorial * LR_cc t.length (j - i) : ℕ) : ℝ) * K ^ j *
          (‖Bf f‖ * (t.map fun f => ‖Bf f‖).prod) * (η ^ (t.length + 1 + j))⁻¹ := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have b1 := (hPb i).trans (mul_le_mul_of_nonneg_left (hbf i w) (norm_nonneg (Bf f)))
      have b2 := ih'.2 (j - i) w
      have e1 : K ^ i * K ^ (j - i) = K ^ j := by rw [← pow_add]; congr 1; omega
      have e2 : (η ^ (i + 1))⁻¹ * (η ^ (t.length + (j - i)))⁻¹ = (η ^ (t.length + 1 + j))⁻¹ := by
        rw [← mul_inv, ← pow_add]; congr 2; omega
      have hKp : 0 ≤ K ^ (j - i) := pow_nonneg hK0 _
      have hC : (0 : ℝ) ≤ ((j.choose i : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i (fun w => Bf f * Gf f w) w‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun w => (t.map fun f => Bf f * Gf f w).prod) w‖
          ≤ ((j.choose i : ℕ) : ℝ) * (‖Bf f‖ * ((i.factorial : ℝ) * K ^ i * (η ^ (i + 1))⁻¹)) *
            ((LR_cc t.length (j - i) : ℝ) * K ^ (j - i) * (t.map fun f => ‖Bf f‖).prod *
              (η ^ (t.length + (j - i)))⁻¹) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left b1 hC) b2 (norm_nonneg _) ?_
            positivity
        _ = ((j.choose i * i.factorial * LR_cc t.length (j - i) : ℕ) : ℝ) *
            (K ^ i * K ^ (j - i)) *
            (‖Bf f‖ * (t.map fun f => ‖Bf f‖).prod) *
            ((η ^ (i + 1))⁻¹ * (η ^ (t.length + (j - i)))⁻¹) := by push_cast; ring
        _ = ((j.choose i * i.factorial * LR_cc t.length (j - i) : ℕ) : ℝ) * K ^ j *
            (‖Bf f‖ * (t.map fun f => ‖Bf f‖).prod) * (η ^ (t.length + 1 + j))⁻¹ := by
            rw [e1, e2]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    simp only [List.length_cons, List.map_cons, List.prod_cons, LR_cc, Nat.cast_sum]

end Abstract
/-- The algebra of operators on `ℂ^{DN}`, in which the operator norm of matrices lives. -/
private abbrev LR_Alg (D N : ℕ) :=
  EuclideanSpace ℂ (Idx D N) →L[ℂ] EuclideanSpace ℂ (Idx D N)

private lemma LR_opNorm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (e : ℝ)
    (he0 : 0 ≤ e) (he : ∀ p q, ‖A p q‖ ≤ e) : opNorm A ≤ Fintype.card ι * e := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have hAu : ∀ p, ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) A u) p‖ ≤ e * ∑ q, ‖u q‖ := by
    intro p
    have : (Matrix.toEuclideanCLM (𝕜 := ℂ) A u) p = ∑ q, A p q * u q := rfl
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (he p q) (norm_nonneg _)
  have hsum : (∑ q, ‖u q‖) ^ 2 ≤ Fintype.card ι * ‖u‖ ^ 2 := by
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun q => ‖u q‖)).trans ?_
    rw [Finset.card_univ, PiLp.norm_sq_eq_of_L2]
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A u‖ ^ 2 ≤ (Fintype.card ι * e * ‖u‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ p, ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) A u) p‖ ^ 2
        ≤ ∑ p : ι, (e * ∑ q, ‖u q‖) ^ 2 :=
          Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hAu p) 2
      _ = Fintype.card ι * (e ^ 2 * (∑ q, ‖u q‖) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ Fintype.card ι * (e ^ 2 * (Fintype.card ι * ‖u‖ ^ 2)) := by gcongr
      _ = (Fintype.card ι * e * ‖u‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- The operator norm of a matrix is unchanged by the conjugate transpose. -/
private lemma LR_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

/-- `‖G(ξ)‖ ≤ η⁻¹` for a Hermitian `X` and `|Im ξ| ≥ η > 0`. -/
private lemma LR_opNorm_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ξ : ℂ) (η : ℝ) (hη : 0 < η) (hξ : η ≤ |ξ.im|) :
    opNorm (res X ξ) ≤ η⁻¹ := by
  have hne : ξ.im ≠ 0 := fun h => by rw [h, abs_zero] at hξ; linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (starRingEnd ℂ ξ).im := by rw [Complex.conj_im]; linarith
    have h2 := res_conj X hX (starRingEnd ℂ ξ) h1
    rw [Complex.conj_conj] at h2
    rw [h2, LR_opNorm_conjTranspose]
    refine (opNorm_res_le X hX _ h1).trans ?_
    rw [Complex.conj_im]
    refine inv_anti₀ hη ?_
    rw [abs_of_neg hneg] at hξ
    linarith
  · refine (opNorm_res_le X hX ξ hpos).trans ?_
    refine inv_anti₀ hη ?_
    rw [abs_of_pos hpos] at hξ
    exact hξ

/-- The modulus of a normalized trace is at most the operator norm. -/
private lemma LR_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖ntr A‖ ≤ opNorm A := by
  by_cases h : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
    simp only [ntr, Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, norm_zero]
    exact norm_nonneg _
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero h
    unfold ntr
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖A.trace‖ ≤ Fintype.card ι * opNorm A := by
      unfold Matrix.trace
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖A.diag i‖ ≤ ∑ _i : ι, opNorm A :=
            Finset.sum_le_sum fun i _ => norm_apply_le_opNorm A i i
        _ = Fintype.card ι * opNorm A := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖A.trace‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι * opNorm A) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
      _ = opNorm A := by field_simp

/-- The normalized trace as a continuous real-linear functional on the algebra of operators, of
norm at most one. -/
private def LR_ntr (D N : ℕ) : LR_Alg D N →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => ntr ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Idx D N)).symm a)
      map_add' := fun a b => by
        simp only [map_add, ntr, Matrix.trace_add, mul_add]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul c a, map_smul, ntr, ntr, Matrix.trace_smul, smul_eq_mul,
          Complex.real_smul]
        ring }
    1 (fun a => by
      obtain ⟨A, rfl⟩ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Idx D N)).surjective a
      change ‖ntr ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Idx D N)).symm
        (Matrix.toEuclideanCLM (𝕜 := ℂ) A))‖ ≤ 1 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
      rw [StarAlgEquiv.symm_apply_apply, one_mul]
      exact LR_ntr_le A)

private lemma LR_ntr_apply (D N : ℕ) (A : Matrix (Idx D N) (Idx D N) ℂ) :
    LR_ntr D N (Matrix.toEuclideanCLM (𝕜 := ℂ) A) = ntr A := by
  change ntr ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Idx D N)).symm
    (Matrix.toEuclideanCLM (𝕜 := ℂ) A)) = ntr A
  rw [StarAlgEquiv.symm_apply_apply]

private lemma LR_ntr_norm (D N : ℕ) : ‖LR_ntr D N‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- For Hermitian `X` and `Im ξ ≠ 0`, the operator `X - ξ` is invertible, and its inverse is the
operator of the resolvent. -/
private lemma LR_inverse_eq {D N : ℕ} (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian)
    (ξ : ℂ) (hξ : ξ.im ≠ 0) :
    IsUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (X - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ))) ∧
    Ring.inverse (Matrix.toEuclideanCLM (𝕜 := ℂ) (X - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ))) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (res X ξ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub_of_im_ne X hX ξ hξ
  have e1 : Matrix.toEuclideanCLM (𝕜 := ℂ) (X - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (res X ξ) = 1 := by rw [← map_mul, h1, map_one]
  have e2 : Matrix.toEuclideanCLM (𝕜 := ℂ) (res X ξ) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (X - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 := by
    rw [← map_mul, h2, map_one]
  let u : (LR_Alg D N)ˣ := ⟨_, _, e1, e2⟩
  refine ⟨u.isUnit, ?_⟩
  exact Ring.inverse_unit u

/-- `hermPart` is the Hermitian part `symArr` of the local-law files. -/
private lemma LR_hermPart_eq {D N : ℕ} (h : Idx D N → Idx D N → ℂ) : hermPart h = symArr h := by
  funext i j
  simp [hermPart, symArr]

/-- The Hermitian part of an array is a Hermitian matrix. -/
private lemma LR_hermPart_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ) :
    (Matrix.of (hermPart h)).IsHermitian := by
  rw [LR_hermPart_eq]
  exact symArr_isHermitian h

private lemma LR_hermPart_add {D N : ℕ} (h h' : Idx D N → Idx D N → ℂ) :
    hermPart (h + h') = hermPart h + hermPart h' := by
  funext i j
  simp only [hermPart, Pi.add_apply, star_add]
  ring

private lemma LR_hermPart_smul {D N : ℕ} (c : ℝ) (h : Idx D N → Idx D N → ℂ) :
    hermPart (c • h) = (c : ℂ) • hermPart h := by
  funext i j
  simp only [hermPart, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
    Complex.conj_ofReal, smul_eq_mul]
  ring

/-- The entries of the Hermitian part of an array are at most the sup norm of the array. -/
private lemma LR_hermPart_entry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    ‖hermPart h i j‖ ≤ ‖h‖ := by
  have h1 : ‖h i j‖ ≤ ‖h‖ := (norm_le_pi_norm (h i) j).trans (norm_le_pi_norm h i)
  have h2 : ‖h j i‖ ≤ ‖h‖ := (norm_le_pi_norm (h j) i).trans (norm_le_pi_norm h j)
  simp only [hermPart]
  rw [norm_div]
  have h3 : ‖h i j + star (h j i)‖ ≤ 2 * ‖h‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.star_def, Complex.norm_conj]
    linarith
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

local notation "TT" => (Matrix.toEuclideanCLM (𝕜 := ℂ))

/-- The real-linear map `h ↦ operator of the Hermitian part of h`. -/
private def LR_Lin (D N : ℕ) : (Idx D N → Idx D N → ℂ) →ₗ[ℝ] LR_Alg D N where
  toFun h := Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of (hermPart h))
  map_add' h h' := by
    rw [LR_hermPart_add, ← map_add]
    rfl
  map_smul' c h := by
    rw [LR_hermPart_smul, RingHom.id_apply]
    have : Matrix.of ((c : ℂ) • hermPart h) = (c : ℂ) • Matrix.of (hermPart h) := rfl
    rw [this, map_smul]
    exact Complex.coe_smul c (Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of (hermPart h)))

private lemma LR_Lin_apply (D N : ℕ) (h : Idx D N → Idx D N → ℂ) :
    LR_Lin D N h = Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of (hermPart h)) := rfl

/-- The continuous real-linear map `h ↦ operator of the Hermitian part of h`, of norm at most
`DN`. -/
private def LR_L (D N : ℕ) : (Idx D N → Idx D N → ℂ) →L[ℝ] LR_Alg D N :=
  LinearMap.mkContinuous (LR_Lin D N) (D * N : ℕ) (fun h => by
    rw [LR_Lin_apply]
    have h0 : 0 ≤ ‖h‖ := norm_nonneg _
    have := LR_opNorm_le (Matrix.of (hermPart h)) ‖h‖ h0 (fun p q => LR_hermPart_entry h p q)
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    exact this.trans (le_of_eq (by ring)))

private lemma LR_L_apply (D N : ℕ) (h : Idx D N → Idx D N → ℂ) :
    LR_L D N h = Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of (hermPart h)) := rfl

private lemma LR_L_norm (D N : ℕ) : ‖LR_L D N‖ ≤ ((D * N : ℕ) : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (Nat.cast_nonneg _) _

/-- The factors `(B, Λ, ξ)` of a chain. -/
private abbrev LR_T (D N : ℕ) :=
  Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ


/-! ### The closed-form flow and its derivatives -/

/-- The derivative `dz_s/ds` of the closed-form flow `s ↦ charFlowZ Λ w s` of (3.10)
[eq:deterflow]. -/
private def LR_dz {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (w : ℂ) (s : ℝ) :
    ℂ :=
  -(1 / 2 : ℂ) * (((Real.exp (-s / 2) : ℝ) : ℂ) * (w + mExt Λ w)) -
    (1 / 2 : ℂ) * (((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ w)

/-- The derivative of `LR_dz`. -/
private def LR_ddz {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (w : ℂ) (s : ℝ) :
    ℂ :=
  (1 / 4 : ℂ) * (((Real.exp (-s / 2) : ℝ) : ℂ) * (w + mExt Λ w)) -
    (1 / 4 : ℂ) * (((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ w)

private lemma LR_hasDerivAt_ea (s : ℝ) :
    HasDerivAt (fun y : ℝ => ((Real.exp (-y / 2) : ℝ) : ℂ))
      (-(1 / 2 : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ)) s := by
  have h : HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (Real.exp (-s / 2) * (-1 / 2)) s := by
    have := (((hasDerivAt_id s).neg).div_const 2).exp
    simpa using this
  have h2 := h.ofReal_comp
  convert h2 using 1
  push_cast
  ring

private lemma LR_hasDerivAt_eb (s : ℝ) :
    HasDerivAt (fun y : ℝ => ((Real.exp (y / 2) : ℝ) : ℂ))
      ((1 / 2 : ℂ) * ((Real.exp (s / 2) : ℝ) : ℂ)) s := by
  have h : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (s / 2) * (1 / 2)) s := by
    have := (((hasDerivAt_id s)).div_const 2).exp
    simpa using this
  have h2 := h.ofReal_comp
  convert h2 using 1
  push_cast
  ring

private lemma LR_hasDerivAt_flowZ {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (w : ℂ) (s : ℝ) : HasDerivAt (charFlowZ Λ w) (LR_dz Λ w s) s := by
  have h1 := (LR_hasDerivAt_ea s).mul_const (w + mExt Λ w)
  have h2 := (LR_hasDerivAt_eb s).mul_const (mExt Λ w)
  have h3 := h1.sub h2
  have e : charFlowZ Λ w = (fun y : ℝ => ((Real.exp (-y / 2) : ℝ) : ℂ) * (w + mExt Λ w)) -
      fun y : ℝ => ((Real.exp (y / 2) : ℝ) : ℂ) * mExt Λ w := by
    funext y; rfl
  rw [e]
  convert h3 using 1
  simp only [LR_dz]
  ring

private lemma LR_hasDerivAt_dz {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (w : ℂ) (s : ℝ) : HasDerivAt (LR_dz Λ w) (LR_ddz Λ w s) s := by
  have h1 := ((LR_hasDerivAt_ea s).mul_const (w + mExt Λ w)).const_mul (-(1 / 2 : ℂ))
  have h2 := ((LR_hasDerivAt_eb s).mul_const (mExt Λ w)).const_mul ((1 / 2 : ℂ))
  have h3 := h1.sub h2
  have e : LR_dz Λ w = (fun y : ℝ => -(1 / 2 : ℂ) * (((Real.exp (-y / 2) : ℝ) : ℂ) *
      (w + mExt Λ w))) - fun y : ℝ => (1 / 2 : ℂ) * (((Real.exp (y / 2) : ℝ) : ℂ) *
        mExt Λ w) := by
    funext y; rfl
  rw [e]
  convert h3 using 1
  simp only [LR_ddz]
  ring

/-- `‖dz_s/ds‖ ≤ e^{s/2} (‖w‖ + 2 ‖m‖)/2` for `s ≥ 0`. -/
private lemma LR_dz_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (w : ℂ)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖LR_dz Λ w s‖ ≤ Real.exp (s / 2) * ((‖w‖ + 2 * ‖mExt Λ w‖) / 2) := by
  have hab : Real.exp (-s / 2) ≤ Real.exp (s / 2) := Real.exp_le_exp.2 (by linarith)
  have ha0 := Real.exp_pos (-s / 2)
  have hb0 := Real.exp_pos (s / 2)
  unfold LR_dz
  have e1 : ‖(-(1 / 2 : ℂ) * (((Real.exp (-s / 2) : ℝ) : ℂ) * (w + mExt Λ w)))‖ ≤
      (1 / 2) * (Real.exp (-s / 2) * (‖w‖ + ‖mExt Λ w‖)) := by
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    gcongr
    exact norm_add_le _ _
  have e2 : ‖((1 / 2 : ℂ) * (((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ w))‖ ≤
      (1 / 2) * (Real.exp (s / 2) * ‖mExt Λ w‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
  refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans ?_)
  have := norm_nonneg w
  have := norm_nonneg (mExt Λ w)
  nlinarith [mul_le_mul_of_nonneg_right hab (by positivity : 0 ≤ ‖w‖ + ‖mExt Λ w‖)]

/-- `‖d²z_s/ds²‖ ≤ e^{s/2} (‖w‖ + 2 ‖m‖)/4` for `s ≥ 0`. -/
private lemma LR_ddz_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (w : ℂ)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖LR_ddz Λ w s‖ ≤ Real.exp (s / 2) * ((‖w‖ + 2 * ‖mExt Λ w‖) / 4) := by
  have hab : Real.exp (-s / 2) ≤ Real.exp (s / 2) := Real.exp_le_exp.2 (by linarith)
  have ha0 := Real.exp_pos (-s / 2)
  have hb0 := Real.exp_pos (s / 2)
  unfold LR_ddz
  have e1 : ‖((1 / 4 : ℂ) * (((Real.exp (-s / 2) : ℝ) : ℂ) * (w + mExt Λ w)))‖ ≤
      (1 / 4) * (Real.exp (-s / 2) * (‖w‖ + ‖mExt Λ w‖)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le]
    have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [this]
    gcongr
    exact norm_add_le _ _
  have e2 : ‖((1 / 4 : ℂ) * (((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ w))‖ ≤
      (1 / 4) * (Real.exp (s / 2) * ‖mExt Λ w‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [this]
  refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans ?_)
  have := norm_nonneg w
  have := norm_nonneg (mExt Λ w)
  nlinarith [mul_le_mul_of_nonneg_right hab (by positivity : 0 ≤ ‖w‖ + ‖mExt Λ w‖)]

/-- The closed-form flow of the conjugate start is the conjugate of the flow, and `m` is
conjugated. -/
private lemma LR_mExt_star {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : mExt Λ (star z) = star (mExt Λ z) := by
  have hz' : (star z).im < 0 := by simpa using hz
  have h1 : ¬ 0 < (star z).im := not_lt.2 hz'.le
  simp only [mExt, h1, hz', hz, ↓reduceIte, star_star]

/-! ### The derivative of the loop in the flow time -/

/-- A real multiple of a Hermitian matrix is Hermitian. -/
private lemma LR_herm_smul {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-- The list `(B_r, Λ_s, z_{r,s})` of factors of the loop `flowLoop` at time `s`. -/
private def LR_fl {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (s : ℝ)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) : List (LR_T D N) :=
  L.map fun f => (f.1, ((Real.exp (-s / 2) : ℝ) : ℂ) • Λ, charFlowZ Λ f.2 s)

/-- The product of the operators `B_r (Y + e^{-s/2} Λ - z_{r,s})⁻¹` of the factors of `L`. -/
private def LR_Q {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (Y : LR_Alg D N) (s : ℝ)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) : LR_Alg D N :=
  (L.map fun f => Matrix.toEuclideanCLM (𝕜 := ℂ) f.1 *
    Ring.inverse (Y + ((Real.exp (-s / 2) : ℝ) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) Λ -
      charFlowZ Λ f.2 s • (1 : LR_Alg D N))).prod

/-- The operator of the chain at the Hermitian array `h` is the product `LR_Q`. -/
private lemma LR_Q_eq {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (s : ℝ)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (hL : ∀ f ∈ L, (charFlowZ Λ f.2 s).im ≠ 0) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (chainB h (LR_fl Λ s L)) =
      LR_Q Λ (Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of h)) s L := by
  unfold chainB LR_fl LR_Q
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun f hf => ?_
  simp only [Function.comp, map_mul]
  congr 1
  have hX : (Matrix.of h + (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ)).IsHermitian :=
    hh.add (LR_herm_smul Λ hΛ _)
  have := (LR_inverse_eq _ hX (charFlowZ Λ f.2 s) (hL f hf)).2
  rw [← this]
  congr 1
  simp only [map_sub, map_add, map_smul, map_one]

/-- The derivative of the inverse of a differentiable family of units. -/
private lemma LR_hasDerivAt_inverse {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℝ 𝒜]
    [CompleteSpace 𝒜] (A : ℝ → 𝒜) (A' : 𝒜) (s : ℝ) (hA : HasDerivAt A A' s)
    (hu : IsUnit (A s)) :
    HasDerivAt (fun y => Ring.inverse (A y))
      (-(Ring.inverse (A s) * A' * Ring.inverse (A s))) s := by
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [IsUnit.unit_spec] at h1
  have h2 := h1.comp_hasDerivAt s hA
  have h3 : ((hu.unit⁻¹ : 𝒜ˣ) : 𝒜) = Ring.inverse (A s) := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec]
  rw [h3] at h2
  refine (h2.congr_deriv ?_ : HasDerivAt (fun y => Ring.inverse (A y)) _ s)
  simp

/-- The terms of the time derivative of the loop `flowLoop`, as pairs (coefficient function in
`s`, list of factors): `∂_s G = G (e^{-s/2} Λ/2 + dz_s/ds) G` inserts after each factor `(B, w)` of
the list the factor `(Λ, w)` with the coefficient `e^{-s/2}/2` and the factor `(1, w)` with the
coefficient `dz_s/ds`. -/
private def LR_insF {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) :
    List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) →
      List ((ℝ → ℂ) × List (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
  | [] => []
  | f :: t => ((fun s => (1 / 2 : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ)), f :: (Λ, f.2) :: t) ::
      ((fun s => LR_dz Λ f.2 s), f :: ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) :: t) ::
        (LR_insF Λ t).map fun cm => (cm.1, f :: cm.2)

/-- The time derivative of the loop `flowLoop`: the sum over the terms of `LR_insF`. -/
private def LR_dloop {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (s : ℝ) (v : Idx D N → Idx D N → ℂ) : ℂ :=
  ((LR_insF Λ L).map fun cm => cm.1 s * flowLoop Λ cm.2 s v).sum

/-- The algebraic identity behind the product rule for `B G` with `G' = G (c Λ + d) G`. -/
private lemma LR_alg_identity {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜] (B G L Q S : 𝒜) (α dz : ℂ) :
    B * -(G * ((-(1 / 2 : ℂ) * α) • L - dz • (1 : 𝒜)) * G) * Q + (B * G) * S =
      (1 / 2 * α) • (B * G * (L * G * Q)) + (dz • (B * G * (1 * G * Q)) + (B * G) * S) := by
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    mul_assoc]
  module

/-- The derivative of the product `LR_Q` in the flow time. -/
private lemma LR_hasDerivAt_Q {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (Y : LR_Alg D N)
    (s0 : ℝ) [CompleteSpace (LR_Alg D N)] :
    ∀ L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ L, IsUnit (Y + ((Real.exp (-s0 / 2) : ℝ) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) Λ -
        charFlowZ Λ f.2 s0 • (1 : LR_Alg D N))) →
      HasDerivAt (fun s => LR_Q Λ Y s L)
        ((LR_insF Λ L).map fun cm => cm.1 s0 • LR_Q Λ Y s0 cm.2).sum s0 := by
  intro L
  induction L with
  | nil =>
    intro _
    simp only [LR_Q, LR_insF, List.map_nil, List.prod_nil, List.sum_nil]
    exact hasDerivAt_const _ _
  | cons f t ih =>
    intro hL
    have hf := hL f (by simp)
    have ht := ih (fun g hg => hL g (by simp [hg]))
    set Gf : LR_Alg D N := Ring.inverse (Y + ((Real.exp (-s0 / 2) : ℝ) : ℂ) • TT Λ -
      charFlowZ Λ f.2 s0 • (1 : LR_Alg D N)) with hGf
    have hA : HasDerivAt (fun s => Y + ((Real.exp (-s / 2) : ℝ) : ℂ) • TT Λ -
        charFlowZ Λ f.2 s • (1 : LR_Alg D N))
        ((-(1 / 2 : ℂ) * ((Real.exp (-s0 / 2) : ℝ) : ℂ)) • TT Λ -
          LR_dz Λ f.2 s0 • (1 : LR_Alg D N)) s0 :=
      (((LR_hasDerivAt_ea s0).smul_const (TT Λ)).const_add Y).sub
        ((LR_hasDerivAt_flowZ Λ f.2 s0).smul_const (1 : LR_Alg D N))
    have hG := LR_hasDerivAt_inverse _ _ s0 hA hf
    have hP := (hG.const_mul (TT f.1)).mul ht
    have e : (fun s => LR_Q Λ Y s (f :: t)) = fun s => (TT f.1 * Ring.inverse (Y +
        ((Real.exp (-s / 2) : ℝ) : ℂ) • TT Λ - charFlowZ Λ f.2 s • (1 : LR_Alg D N))) *
          LR_Q Λ Y s t := by
      funext s
      simp only [LR_Q, List.map_cons, List.prod_cons]
    rw [e]
    refine hP.congr_deriv ?_
    have hcons : ∀ (g : Matrix (Idx D N) (Idx D N) ℂ × ℂ)
        (m : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)), g.2 = f.2 →
        LR_Q Λ Y s0 (g :: m) = (TT g.1 * Gf) * LR_Q Λ Y s0 m := by
      intro g m hg
      simp only [LR_Q, List.map_cons, List.prod_cons, hGf, hg]
    simp only [LR_insF, List.map_cons, List.sum_cons, List.map_map]
    have h1 : LR_Q Λ Y s0 (f :: (Λ, f.2) :: t) =
        (TT f.1 * Gf) * ((TT Λ * Gf) * LR_Q Λ Y s0 t) := by
      rw [hcons f _ rfl, hcons (Λ, f.2) _ rfl]
    have h2 : LR_Q Λ Y s0 (f :: ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) :: t) =
        (TT f.1 * Gf) * ((1 * Gf) * LR_Q Λ Y s0 t) := by
      rw [hcons f _ rfl, hcons (1, f.2) _ rfl]
      simp
    have h3 : ∀ cm : (ℝ → ℂ) × List (Matrix (Idx D N) (Idx D N) ℂ × ℂ),
        cm.1 s0 • LR_Q Λ Y s0 (f :: cm.2) = (TT f.1 * Gf) * (cm.1 s0 • LR_Q Λ Y s0 cm.2) := by
      intro cm
      rw [hcons f _ rfl, mul_smul_comm]
    have h4 : ((fun cm : (ℝ → ℂ) × List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) =>
        cm.1 s0 • LR_Q Λ Y s0 cm.2) ∘ fun cm : (ℝ → ℂ) × List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) =>
          (cm.1, f :: cm.2)) =
        fun cm : (ℝ → ℂ) × List (Matrix (Idx D N) (Idx D N) ℂ × ℂ) =>
          (TT f.1 * Gf) * (cm.1 s0 • LR_Q Λ Y s0 cm.2) := by
      funext cm
      exact h3 cm
    rw [h1, h2, h4, List.sum_map_mul_left]
    simp only [← hGf]
    exact LR_alg_identity _ _ _ _ _ _ _

/-- The normalized trace is homogeneous: `⟨c B⟩ = c ⟨B⟩`. -/
private lemma LR_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (B : Matrix ι ι ℂ) :
    ntr (c • B) = c * ntr B := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The coefficient `e^{-s/2}/2` of the inserted factor `(Λ, w)`. -/
private def LR_alpha (s : ℝ) : ℂ := (1 / 2 : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ)

private lemma LR_insF_length {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ), (LR_insF Λ L).length = 2 * L.length := by
  intro L
  induction L with
  | nil => simp [LR_insF]
  | cons f t ih => simp only [LR_insF, List.length_cons, List.length_map, ih]; ring

/-- The terms of `LR_insF` have `L.length + 1` factors, their flow points are those of `L`, and
the product of the operator norms of their matrices is that of `L` times the norm of the inserted
matrix. -/
private lemma LR_insF_mem {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ), ∀ cm ∈ LR_insF Λ L,
      cm.2.length = L.length + 1 ∧ (∀ f ∈ cm.2, ∃ g ∈ L, f.2 = g.2) ∧
      ((cm.1 = LR_alpha ∧ (cm.2.map fun f => opNorm f.1).prod =
          (L.map fun f => opNorm f.1).prod * opNorm Λ) ∨
        (∃ g ∈ L, cm.1 = (fun s => LR_dz Λ g.2 s) ∧ (cm.2.map fun f => opNorm f.1).prod =
          (L.map fun f => opNorm f.1).prod *
            opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ))) := by
  intro L
  induction L with
  | nil => intro cm hcm; simp [LR_insF] at hcm
  | cons f t ih =>
    intro cm hcm
    simp only [LR_insF, List.mem_cons, List.mem_map] at hcm
    rcases hcm with rfl | rfl | ⟨cm', hcm', rfl⟩
    · refine ⟨by simp, ?_, Or.inl ⟨rfl, ?_⟩⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | rfl | hg
        · exact ⟨g, by simp, rfl⟩
        · exact ⟨f, by simp, rfl⟩
        · exact ⟨g, by simp [hg], rfl⟩
      · simp only [List.map_cons, List.prod_cons]; ring
    · refine ⟨by simp, ?_, Or.inr ⟨f, by simp, rfl, ?_⟩⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | rfl | hg
        · exact ⟨g, by simp, rfl⟩
        · exact ⟨f, by simp, rfl⟩
        · exact ⟨g, by simp [hg], rfl⟩
      · simp only [List.map_cons, List.prod_cons]; ring
    · obtain ⟨h1, h2, h3⟩ := ih cm' hcm'
      refine ⟨by simp [h1], ?_, ?_⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨g, by simp, rfl⟩
        · obtain ⟨g', hg', hgg⟩ := h2 g hg
          exact ⟨g', by simp [hg'], hgg⟩
      · rcases h3 with ⟨h4, h5⟩ | ⟨g, hg, h4, h5⟩
        · refine Or.inl ⟨h4, ?_⟩
          simp only [List.map_cons, List.prod_cons, h5]; ring
        · refine Or.inr ⟨g, by simp [hg], h4, ?_⟩
          simp only [List.map_cons, List.prod_cons, h5]; ring

/-- `Im m > 0` for `m = m(z, Λ)` at `Im z > 0` ((2.16) [self_m]). -/
private lemma LR_im_m_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) : 0 < (mExt Λ z).im := by
  obtain ⟨-, -, h⟩ := MExt_spec Λ hΛ z hz.ne'
  exact (mul_pos_iff_of_pos_right hz).1 h

/-- The imaginary part of the closed-form flow decreases in the time. -/
private lemma LR_im_mono {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s S : ℝ) (hsS : s ≤ S) :
    (charFlowZ Λ z S).im ≤ (charFlowZ Λ z s).im := by
  have hm := LR_im_m_pos Λ hΛ z hz
  have e : ∀ x : ℝ, (charFlowZ Λ z x).im = Real.exp (-x / 2) * (z.im + (mExt Λ z).im) -
      Real.exp (x / 2) * (mExt Λ z).im := by
    intro x
    simp only [charFlowZ, Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  rw [e, e]
  have h1 : Real.exp (-S / 2) ≤ Real.exp (-s / 2) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (s / 2) ≤ Real.exp (S / 2) := Real.exp_le_exp.2 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ z.im + (mExt Λ z).im),
    mul_le_mul_of_nonneg_right h2 hm.le]

/-- For a start `w ∈ {z, z̄}` the flow keeps `|Im w_s|` equal to `Im z_s`. -/
private lemma LR_abs_im {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) (w : ℂ) (hw : w = z ∨ w = star z) (s : ℝ) :
    |(charFlowZ Λ w s).im| = |(charFlowZ Λ z s).im| := by
  rcases hw with rfl | rfl
  · rfl
  · rw [charFlowZ_conj Λ z hz s]
    simp

/-- The norms of the start and of `m` do not depend on `w ∈ {z, z̄}`. -/
private lemma LR_norm_start {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) (w : ℂ) (hw : w = z ∨ w = star z) :
    ‖w‖ = ‖z‖ ∧ ‖mExt Λ w‖ = ‖mExt Λ z‖ := by
  rcases hw with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [LR_mExt_star Λ z hz]
    simp

/-- The flowed point of a start `w ∈ {z, z̄}` is off the real axis before `t_c`. -/
private lemma LR_im_ne {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (w : ℂ) (hw : w = z ∨ w = star z) (s : ℝ)
    (hs : s < flowTc Λ z) : (charFlowZ Λ w s).im ≠ 0 := by
  have h := (charFlow_M Λ hΛ z hz s hs).1
  intro h0
  have := LR_abs_im Λ z hz w hw s
  rw [h0, abs_zero, abs_of_pos h] at this
  linarith

private lemma LR_hasDerivAt_listsum {ι : Type*} (I : List ι) (g : ι → ℝ → ℂ) (g' : ι → ℂ) (s : ℝ)
    (h : ∀ i ∈ I, HasDerivAt (g i) (g' i) s) :
    HasDerivAt (fun x => (I.map fun i => g i x).sum) (I.map g').sum s := by
  induction I with
  | nil => simpa using hasDerivAt_const s (0 : ℂ)
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

/-- The conclusion of `loopA_deriv_le` for a given family of constants `c`. -/
private def LR_LB (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ (D N : ℕ) (η₀ : ℝ),
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
    0 < η₀ → (∀ f ∈ l, f.2.1.IsHermitian ∧ η₀ ≤ |f.2.2.im|) →
      ContDiff ℝ 4 (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) ∧
      ∀ j : ℕ, j ≤ 4 → ∀ v : Idx D N → Idx D N → ℂ,
        ‖iteratedFDeriv ℝ j (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) v‖ ≤
          c l.length j * ((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
            (η₀ ^ (l.length + j))⁻¹

/-- The constants of `LR_LB` may be replaced by their absolute values. -/
private lemma LR_LB_abs (c : ℕ → ℕ → ℝ) (hc : LR_LB c) : LR_LB (fun p j => |c p j|) := by
  intro D N η₀ l hη hl
  obtain ⟨h1, h2⟩ := hc D N η₀ l hη hl
  refine ⟨h1, fun j hj v => (h2 j hj v).trans ?_⟩
  have hp : 0 ≤ ((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
      (η₀ ^ (l.length + j))⁻¹ := by
    have : 0 ≤ (l.map fun f => opNorm f.1).prod := by
      refine List.prod_nonneg ?_
      intro x hx
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg _
    positivity
  have := mul_le_mul_of_nonneg_right (le_abs_self (c l.length j)) hp
  calc c l.length j * ((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
        (η₀ ^ (l.length + j))⁻¹
      = c l.length j * (((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
        (η₀ ^ (l.length + j))⁻¹) := by ring
    _ ≤ |c l.length j| * (((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
        (η₀ ^ (l.length + j))⁻¹) := this
    _ = _ := by ring

/-- The time derivative of the loop `flowLoop` before `t_c`: `LR_dloop`. -/
private lemma LR_hasDerivAt_flowLoop {D N : ℕ} [Nonempty (Idx D N)]
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (hL : ∀ f ∈ L, f.2 = z ∨ f.2 = star z)
    (s0 : ℝ) (hs0 : s0 < flowTc Λ z) (v : Idx D N → Idx D N → ℂ) :
    HasDerivAt (fun s => flowLoop Λ L s v) (LR_dloop Λ L s0 v) s0 := by
  have : CompleteSpace (LR_Alg D N) := FiniteDimensional.complete ℂ _
  have hh := LR_hermPart_herm v
  set Y : LR_Alg D N := Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of (hermPart v)) with hY
  have hne : ∀ s < flowTc Λ z, ∀ f ∈ L, (charFlowZ Λ f.2 s).im ≠ 0 := fun s hs f hf =>
    LR_im_ne Λ hΛ z hz f.2 (hL f hf) s hs
  have hunit : ∀ f ∈ L, IsUnit (Y + ((Real.exp (-s0 / 2) : ℝ) : ℂ) •
      Matrix.toEuclideanCLM (𝕜 := ℂ) Λ - charFlowZ Λ f.2 s0 • (1 : LR_Alg D N)) := by
    intro f hf
    have hX : (Matrix.of (hermPart v) + (((Real.exp (-s0 / 2) : ℝ) : ℂ) • Λ)).IsHermitian :=
      hh.add (LR_herm_smul Λ hΛ _)
    have := (LR_inverse_eq _ hX (charFlowZ Λ f.2 s0) (hne s0 hs0 f hf)).1
    convert this using 1
    simp only [map_sub, map_add, map_smul, map_one, hY]
  have hQ := LR_hasDerivAt_Q Λ Y s0 L hunit
  have hN := (LR_ntr D N).hasFDerivAt.comp_hasDerivAt s0 hQ
  have hev : (fun s => flowLoop Λ L s v) =ᶠ[nhds s0] (LR_ntr D N) ∘ fun s => LR_Q Λ Y s L := by
    filter_upwards [Iio_mem_nhds hs0] with s hs
    have := LR_Q_eq Λ hΛ (hermPart v) hh s L (hne s hs)
    simp only [Function.comp]
    rw [← this, LR_ntr_apply]
    rfl
  refine (hN.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [map_list_sum, List.map_map]
  unfold LR_dloop
  congr 1
  refine List.map_congr_left fun cm hcm => ?_
  obtain ⟨-, hsnd, -⟩ := LR_insF_mem Λ L cm hcm
  have hne' : ∀ f ∈ cm.2, (charFlowZ Λ f.2 s0).im ≠ 0 := by
    intro f hf
    obtain ⟨g, hg, hgg⟩ := hsnd f hf
    rw [hgg]
    exact hne s0 hs0 g hg
  have := LR_Q_eq Λ hΛ (hermPart v) hh s0 cm.2 hne'
  simp only [Function.comp]
  rw [← this, ← map_smul, LR_ntr_apply, LR_ntr_smul]
  rfl

/-- Smoothness and the derivative norm of a finite sum of functions. -/
private lemma LR_listsum_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (n : ℕ) (I : List ι) (F : ι → E → ℂ) (hF : ∀ i ∈ I, ContDiff ℝ n (F i)) (x : E) :
    ContDiff ℝ n (fun v => (I.map fun i => F i v).sum) ∧
      ‖iteratedFDeriv ℝ n (fun v => (I.map fun i => F i v).sum) x‖ ≤
        (I.map fun i => ‖iteratedFDeriv ℝ n (F i) x‖).sum := by
  induction I with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    refine ⟨contDiff_const, ?_⟩
    rw [iteratedFDeriv_fun_zero]
    simp
  | cons a t ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hF i (by simp [hi])
    have ha := hF a (by simp)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨ha.add ih1, ?_⟩
    have e : iteratedFDeriv ℝ n (fun v => F a v + (t.map fun i => F i v).sum) x =
        iteratedFDeriv ℝ n (F a) x + iteratedFDeriv ℝ n (fun v => (t.map fun i => F i v).sum) x :=
      iteratedFDeriv_add_apply ha.contDiffAt ih1.contDiffAt
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih2)

/-- The loops of `L` along the flow are `C⁴` in the array with the bounds of `loopA_deriv_le` at
`η₀ = min 1 η_S`, for `0 ≤ s ≤ S < t_c`. -/
private lemma LR_flowLoop_reg {D N : ℕ} [Nonempty (Idx D N)] (cA : ℕ → ℕ → ℝ) (hcA : LR_LB cA)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hSt : S < flowTc Λ z) (s : ℝ) (hs : s ∈ Set.Icc 0 S)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (hL : ∀ f ∈ L, f.2 = z ∨ f.2 = star z) :
    ContDiff ℝ 4 (flowLoop Λ L s) ∧ ∀ j : ℕ, j ≤ 4 → ∀ v,
      ‖iteratedFDeriv ℝ j (flowLoop Λ L s) v‖ ≤ cA L.length j * ((D : ℝ) * N + 1) ^ j *
        (L.map fun f => opNorm f.1).prod *
        ((min 1 (charFlowZ Λ z S).im) ^ (L.length + j))⁻¹ := by
  have hηS : 0 < (charFlowZ Λ z S).im := (charFlow_M Λ hΛ z hz S hSt).1
  have hη : 0 < min 1 (charFlowZ Λ z S).im := lt_min one_pos hηS
  have hmono := LR_im_mono Λ hΛ z hz s S hs.2
  have hpos : 0 < (charFlowZ Λ z s).im := hηS.trans_le hmono
  have hl : ∀ f ∈ LR_fl Λ s L, f.2.1.IsHermitian ∧ min 1 (charFlowZ Λ z S).im ≤ |f.2.2.im| := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    refine ⟨LR_herm_smul Λ hΛ _, ?_⟩
    simp only
    rw [LR_abs_im Λ z hz g.2 (hL g hg) s, abs_of_pos hpos]
    exact (min_le_right _ _).trans hmono
  obtain ⟨h1, h2⟩ := hcA D N _ (LR_fl Λ s L) hη hl
  have e : flowLoop Λ L s = fun h => ntr (chainB (hermPart h) (LR_fl Λ s L)) := rfl
  have hlen : (LR_fl Λ s L).length = L.length := by simp [LR_fl]
  have hpr : ((LR_fl Λ s L).map fun f => opNorm f.1).prod = (L.map fun f => opNorm f.1).prod := by
    simp [LR_fl, List.map_map, Function.comp_def]
  rw [e]
  refine ⟨h1, fun j hj v => ?_⟩
  have := h2 j hj v
  rwa [hlen, hpr] at this

/-- The derivatives of order `0, …, 4` of the time derivative `LR_dloop` of the loops along the
flow, in the array. -/
private lemma LR_dloop_reg {D N : ℕ} [Nonempty (Idx D N)] (cA : ℕ → ℕ → ℝ) (hcA : LR_LB cA)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hSt : S < flowTc Λ z) (s : ℝ) (hs : s ∈ Set.Icc 0 S)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (hL : ∀ f ∈ L, f.2 = z ∨ f.2 = star z)
    (Q : ℝ) (hQ1 : ‖LR_alpha s‖ * opNorm Λ ≤ Q) (hQ2 : ∀ g ∈ L, ‖LR_dz Λ g.2 s‖ ≤ Q) :
    ContDiff ℝ 4 (LR_dloop Λ L s) ∧ ∀ j : ℕ, j ≤ 4 → ∀ v,
      ‖iteratedFDeriv ℝ j (LR_dloop Λ L s) v‖ ≤ 2 * (L.length : ℝ) *
        (|cA (L.length + 1) j| * ((D : ℝ) * N + 1) ^ j * (L.map fun f => opNorm f.1).prod * Q *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + j))⁻¹) := by
  have hcA' := LR_LB_abs cA hcA
  have hη : 0 < min 1 (charFlowZ Λ z S).im :=
    lt_min one_pos (charFlow_M Λ hΛ z hz S hSt).1
  have hone : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 := by
    unfold opNorm
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  have hprL : 0 ≤ (L.map fun f => opNorm f.1).prod := by
    refine List.prod_nonneg ?_
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hmem := LR_insF_mem Λ L
  have hLcm : ∀ cm ∈ LR_insF Λ L, ∀ f ∈ cm.2, f.2 = z ∨ f.2 = star z := by
    intro cm hcm f hf
    obtain ⟨-, hsnd, -⟩ := hmem cm hcm
    obtain ⟨g, hg, hgg⟩ := hsnd f hf
    rw [hgg]
    exact hL g hg
  have e : LR_dloop Λ L s = fun v => ((LR_insF Λ L).map fun cm => cm.1 s *
      flowLoop Λ cm.2 s v).sum := rfl
  have hcd : ∀ cm ∈ LR_insF Λ L, ContDiff ℝ 4 (fun v => cm.1 s * flowLoop Λ cm.2 s v) :=
    fun cm hcm => contDiff_const.mul (LR_flowLoop_reg _ hcA' Λ hΛ z hz S hSt s hs cm.2
      (hLcm cm hcm)).1
  rw [e]
  refine ⟨(LR_listsum_iter 4 _ _ hcd 0).1, fun j hj v => ?_⟩
  have hcdj : ∀ cm ∈ LR_insF Λ L, ContDiff ℝ j (fun v => cm.1 s * flowLoop Λ cm.2 s v) :=
    fun cm hcm => (hcd cm hcm).of_le (by exact_mod_cast hj)
  refine ((LR_listsum_iter j _ _ hcdj v).2).trans ?_
  have hterm : ∀ x ∈ (LR_insF Λ L).map fun cm =>
      ‖iteratedFDeriv ℝ j (fun v => cm.1 s * flowLoop Λ cm.2 s v) v‖,
      x ≤ |cA (L.length + 1) j| * ((D : ℝ) * N + 1) ^ j * (L.map fun f => opNorm f.1).prod * Q *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + j))⁻¹ := by
    intro x hx
    obtain ⟨cm, hcm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hlen, -, hform⟩ := hmem cm hcm
    have hreg := LR_flowLoop_reg _ hcA' Λ hΛ z hz S hSt s hs cm.2 (hLcm cm hcm)
    have h1 := hreg.2 j hj v
    have hfd : ContDiffAt ℝ j (flowLoop Λ cm.2 s) v :=
      (hreg.1.of_le (by exact_mod_cast hj)).contDiffAt
    have hsm : ‖iteratedFDeriv ℝ j (fun v => cm.1 s * flowLoop Λ cm.2 s v) v‖ =
        ‖cm.1 s‖ * ‖iteratedFDeriv ℝ j (flowLoop Λ cm.2 s) v‖ := by
      have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := cm.1 s) hfd
      simp only [smul_eq_mul] at this
      rw [this, norm_smul]
    rw [hsm]
    rw [hlen] at h1
    have hw : ‖cm.1 s‖ * (cm.2.map fun f => opNorm f.1).prod ≤
        (L.map fun f => opNorm f.1).prod * Q := by
      rcases hform with ⟨h4, h5⟩ | ⟨g, hg, h4, h5⟩
      · rw [h4, h5]
        calc ‖LR_alpha s‖ * ((L.map fun f => opNorm f.1).prod * opNorm Λ)
            = (L.map fun f => opNorm f.1).prod * (‖LR_alpha s‖ * opNorm Λ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hQ1 hprL
      · rw [h4, h5]
        have := hQ2 g hg
        calc ‖LR_dz Λ g.2 s‖ * ((L.map fun f => opNorm f.1).prod *
              opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ))
            ≤ Q * ((L.map fun f => opNorm f.1).prod * 1) :=
              mul_le_mul this (mul_le_mul_of_nonneg_left hone hprL)
                (mul_nonneg hprL (norm_nonneg _)) ((norm_nonneg _).trans this)
          _ = _ := by ring
    have hy : 0 ≤ |cA (L.length + 1) j| * ((D : ℝ) * N + 1) ^ j *
        ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + j))⁻¹ :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (inv_nonneg.2 (pow_nonneg hη.le _))
    calc ‖cm.1 s‖ * ‖iteratedFDeriv ℝ j (flowLoop Λ cm.2 s) v‖
        ≤ ‖cm.1 s‖ * (|cA (L.length + 1) j| * ((D : ℝ) * N + 1) ^ j *
          (cm.2.map fun f => opNorm f.1).prod *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + j))⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (|cA (L.length + 1) j| * ((D : ℝ) * N + 1) ^ j *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + j))⁻¹) *
          (‖cm.1 s‖ * (cm.2.map fun f => opNorm f.1).prod) := by ring
      _ ≤ (|cA (L.length + 1) j| * ((D : ℝ) * N + 1) ^ j *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + j))⁻¹) *
          ((L.map fun f => opNorm f.1).prod * Q) := mul_le_mul_of_nonneg_left hw hy
      _ = _ := by ring
  have hsum := List.sum_le_length_nsmul _ _ hterm
  rw [List.length_map, LR_insF_length, nsmul_eq_mul] at hsum
  refine hsum.trans (le_of_eq ?_)
  push_cast
  ring

/-- The derivative of `LR_alpha`. -/
private def LR_dalpha (s : ℝ) : ℂ := -(1 / 4 : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ)

private lemma LR_hasDerivAt_alpha (s : ℝ) : HasDerivAt LR_alpha (LR_dalpha s) s := by
  have h := (LR_hasDerivAt_ea s).const_mul (1 / 2 : ℂ)
  refine h.congr_deriv ?_
  simp only [LR_dalpha]
  ring

/-- The second time derivative of the loop `flowLoop`. -/
private def LR_d2 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (s : ℝ) (v : Idx D N → Idx D N → ℂ) : ℂ :=
  ((LR_insF Λ L).map fun cm => deriv cm.1 s * flowLoop Λ cm.2 s v +
    cm.1 s * LR_dloop Λ cm.2 s v).sum

/-- The coefficients of `LR_insF` are differentiable, with derivative `LR_dalpha` or `LR_ddz`. -/
private lemma LR_coef_deriv {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (cm : (ℝ → ℂ) × List (Matrix (Idx D N)
      (Idx D N) ℂ × ℂ)) (hcm : cm ∈ LR_insF Λ L) (s : ℝ) :
    HasDerivAt cm.1 (deriv cm.1 s) s ∧
      (deriv cm.1 s = LR_dalpha s ∨ ∃ g ∈ L, deriv cm.1 s = LR_ddz Λ g.2 s) := by
  obtain ⟨-, -, hform⟩ := LR_insF_mem Λ L cm hcm
  rcases hform with ⟨h4, -⟩ | ⟨g, hg, h4, -⟩
  · rw [h4]
    exact ⟨(LR_hasDerivAt_alpha s).differentiableAt.hasDerivAt,
      Or.inl (LR_hasDerivAt_alpha s).deriv⟩
  · rw [h4]
    exact ⟨(LR_hasDerivAt_dz Λ g.2 s).differentiableAt.hasDerivAt,
      Or.inr ⟨g, hg, (LR_hasDerivAt_dz Λ g.2 s).deriv⟩⟩

/-- The derivative of the time derivative of the loop in the flow time. -/
private lemma LR_hasDerivAt_dloop {D N : ℕ} [Nonempty (Idx D N)]
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (hL : ∀ f ∈ L, f.2 = z ∨ f.2 = star z)
    (s0 : ℝ) (hs0 : s0 < flowTc Λ z) (v : Idx D N → Idx D N → ℂ) :
    HasDerivAt (fun s => LR_dloop Λ L s v) (LR_d2 Λ L s0 v) s0 := by
  have e : (fun s => LR_dloop Λ L s v) = fun s => ((LR_insF Λ L).map fun cm => cm.1 s *
      flowLoop Λ cm.2 s v).sum := rfl
  rw [e]
  refine LR_hasDerivAt_listsum (LR_insF Λ L) (fun cm s => cm.1 s * flowLoop Λ cm.2 s v)
    (fun cm => deriv cm.1 s0 * flowLoop Λ cm.2 s0 v + cm.1 s0 * LR_dloop Λ cm.2 s0 v) s0
    ?_
  intro cm hcm
  obtain ⟨-, hsnd, -⟩ := LR_insF_mem Λ L cm hcm
  have hLcm : ∀ f ∈ cm.2, f.2 = z ∨ f.2 = star z := by
    intro f hf
    obtain ⟨g, hg, hgg⟩ := hsnd f hf
    rw [hgg]
    exact hL g hg
  exact (LR_coef_deriv Λ L cm hcm s0).1.mul (LR_hasDerivAt_flowLoop Λ hΛ z hz cm.2 hLcm s0 hs0 v)

private lemma LR_norm_listsum_le {ι : Type*} (I : List ι) (g : ι → ℂ) :
    ‖(I.map g).sum‖ ≤ (I.map fun i => ‖g i‖).sum := by
  induction I with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The bound of the second time derivative `LR_d2`, from the bounds of the loops with `p + 1` and
`p + 2` factors. -/
private lemma LR_d2_le {D N : ℕ} [Nonempty (Idx D N)] (cA : ℕ → ℕ → ℝ) (hcA : LR_LB cA)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (S : ℝ)
    (hSt : S < flowTc Λ z) (s : ℝ) (hs : s ∈ Set.Icc 0 S)
    (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) (hL : ∀ f ∈ L, f.2 = z ∨ f.2 = star z)
    (Q : ℝ) (hQ1 : ‖LR_alpha s‖ * opNorm Λ ≤ Q) (hQ2 : ∀ g ∈ L, ‖LR_dz Λ g.2 s‖ ≤ Q)
    (hQ3 : ‖LR_dalpha s‖ * opNorm Λ ≤ Q) (hQ4 : ∀ g ∈ L, ‖LR_ddz Λ g.2 s‖ ≤ Q)
    (v : Idx D N → Idx D N → ℂ) :
    ‖LR_d2 Λ L s v‖ ≤ 2 * (L.length : ℝ) *
      (|cA (L.length + 1) 0| * (L.map fun f => opNorm f.1).prod * Q *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1))⁻¹ +
        2 * ((L.length : ℝ) + 1) * (|cA (L.length + 1 + 1) 0| * (L.map fun f => opNorm f.1).prod *
          Q * Q * ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + 1))⁻¹)) := by
  have hcA' := LR_LB_abs cA hcA
  have hη : 0 < min 1 (charFlowZ Λ z S).im :=
    lt_min one_pos (charFlow_M Λ hΛ z hz S hSt).1
  have hone : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 := by
    unfold opNorm
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  have hprL : 0 ≤ (L.map fun f => opNorm f.1).prod := by
    refine List.prod_nonneg ?_
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hmem := LR_insF_mem Λ L
  have hLcm : ∀ cm ∈ LR_insF Λ L, ∀ f ∈ cm.2, f.2 = z ∨ f.2 = star z := by
    intro cm hcm f hf
    obtain ⟨-, hsnd, -⟩ := hmem cm hcm
    obtain ⟨g, hg, hgg⟩ := hsnd f hf
    rw [hgg]
    exact hL g hg
  have hterm : ∀ x ∈ (LR_insF Λ L).map fun cm => ‖deriv cm.1 s * flowLoop Λ cm.2 s v +
      cm.1 s * LR_dloop Λ cm.2 s v‖,
      x ≤ |cA (L.length + 1) 0| * (L.map fun f => opNorm f.1).prod * Q *
          ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1))⁻¹ +
        2 * ((L.length : ℝ) + 1) * (|cA (L.length + 1 + 1) 0| * (L.map fun f => opNorm f.1).prod *
          Q * Q * ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + 1))⁻¹) := by
    intro x hx
    obtain ⟨cm, hcm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hlen, hsnd, hform⟩ := hmem cm hcm
    have hLc := hLcm cm hcm
    have hreg := LR_flowLoop_reg _ hcA' Λ hΛ z hz S hSt s hs cm.2 hLc
    have h1 := hreg.2 0 (by norm_num) v
    rw [norm_iteratedFDeriv_zero, hlen] at h1
    simp only [pow_zero, mul_one] at h1
    have hQ2' : ∀ g ∈ cm.2, ‖LR_dz Λ g.2 s‖ ≤ Q := by
      intro g hg
      obtain ⟨g', hg', hgg⟩ := hsnd g hg
      rw [hgg]
      exact hQ2 g' hg'
    have hdl := (LR_dloop_reg _ hcA' Λ hΛ z hz S hSt s hs cm.2 hLc Q hQ1 hQ2').2 0
      (by norm_num) v
    rw [norm_iteratedFDeriv_zero, hlen] at hdl
    simp only [pow_zero, mul_one, Nat.add_zero, abs_abs] at hdl
    have hd := (LR_coef_deriv Λ L cm hcm s).2
    have hwd : ‖deriv cm.1 s‖ * (cm.2.map fun f => opNorm f.1).prod ≤
        (L.map fun f => opNorm f.1).prod * Q := by
      rcases hform with ⟨h4, h5⟩ | ⟨g, hg, h4, h5⟩
      · rw [h5]
        have : deriv cm.1 s = LR_dalpha s := by
          rw [h4]; exact (LR_hasDerivAt_alpha s).deriv
        rw [this]
        calc ‖LR_dalpha s‖ * ((L.map fun f => opNorm f.1).prod * opNorm Λ)
            = (L.map fun f => opNorm f.1).prod * (‖LR_dalpha s‖ * opNorm Λ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hQ3 hprL
      · rw [h5]
        have : deriv cm.1 s = LR_ddz Λ g.2 s := by
          rw [h4]; exact (LR_hasDerivAt_dz Λ g.2 s).deriv
        rw [this]
        have := hQ4 g hg
        calc ‖LR_ddz Λ g.2 s‖ * ((L.map fun f => opNorm f.1).prod *
              opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ))
            ≤ Q * ((L.map fun f => opNorm f.1).prod * 1) :=
              mul_le_mul this (mul_le_mul_of_nonneg_left hone hprL)
                (mul_nonneg hprL (norm_nonneg _)) ((norm_nonneg _).trans this)
          _ = _ := by ring
    have hwc : ‖cm.1 s‖ * (cm.2.map fun f => opNorm f.1).prod ≤
        (L.map fun f => opNorm f.1).prod * Q := by
      rcases hform with ⟨h4, h5⟩ | ⟨g, hg, h4, h5⟩
      · rw [h4, h5]
        calc ‖LR_alpha s‖ * ((L.map fun f => opNorm f.1).prod * opNorm Λ)
            = (L.map fun f => opNorm f.1).prod * (‖LR_alpha s‖ * opNorm Λ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hQ1 hprL
      · rw [h4, h5]
        have := hQ2 g hg
        calc ‖LR_dz Λ g.2 s‖ * ((L.map fun f => opNorm f.1).prod *
              opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ))
            ≤ Q * ((L.map fun f => opNorm f.1).prod * 1) :=
              mul_le_mul this (mul_le_mul_of_nonneg_left hone hprL)
                (mul_nonneg hprL (norm_nonneg _)) ((norm_nonneg _).trans this)
          _ = _ := by ring
    have hp1 : 0 ≤ ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1))⁻¹ :=
      inv_nonneg.2 (pow_nonneg hη.le _)
    have hp2 : 0 ≤ ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + 1))⁻¹ :=
      inv_nonneg.2 (pow_nonneg hη.le _)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc ‖deriv cm.1 s‖ * ‖flowLoop Λ cm.2 s v‖
          ≤ ‖deriv cm.1 s‖ * (|cA (L.length + 1) 0| * (cm.2.map fun f => opNorm f.1).prod *
            ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1))⁻¹) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = (|cA (L.length + 1) 0| * ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1))⁻¹) *
            (‖deriv cm.1 s‖ * (cm.2.map fun f => opNorm f.1).prod) := by ring
        _ ≤ (|cA (L.length + 1) 0| * ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1))⁻¹) *
            ((L.map fun f => opNorm f.1).prod * Q) :=
            mul_le_mul_of_nonneg_left hwd (mul_nonneg (abs_nonneg _) hp1)
        _ = _ := by ring
    · rw [norm_mul]
      calc ‖cm.1 s‖ * ‖LR_dloop Λ cm.2 s v‖
          ≤ ‖cm.1 s‖ * (2 * ((L.length : ℝ) + 1) * (|cA (L.length + 1 + 1) 0| *
            (cm.2.map fun f => opNorm f.1).prod * Q *
            ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + 1))⁻¹)) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine hdl.trans (le_of_eq ?_)
            push_cast
            ring
        _ = (2 * ((L.length : ℝ) + 1) * (|cA (L.length + 1 + 1) 0| * Q *
            ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + 1))⁻¹)) *
            (‖cm.1 s‖ * (cm.2.map fun f => opNorm f.1).prod) := by ring
        _ ≤ (2 * ((L.length : ℝ) + 1) * (|cA (L.length + 1 + 1) 0| * Q *
            ((min 1 (charFlowZ Λ z S).im) ^ (L.length + 1 + 1))⁻¹)) *
            ((L.map fun f => opNorm f.1).prod * Q) :=
            mul_le_mul_of_nonneg_left hwc (by
              have : 0 ≤ Q := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hQ1
              positivity)
        _ = _ := by ring
  have hsum := List.sum_le_length_nsmul _ _ hterm
  rw [List.length_map, LR_insF_length, nsmul_eq_mul] at hsum
  unfold LR_d2
  refine (LR_norm_listsum_le _ _).trans (hsum.trans (le_of_eq ?_))
  push_cast
  ring

private lemma LR_norm_alpha (s : ℝ) : ‖LR_alpha s‖ = (1 / 2) * Real.exp (-s / 2) := by
  unfold LR_alpha
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

private lemma LR_norm_dalpha (s : ℝ) : ‖LR_dalpha s‖ = (1 / 4) * Real.exp (-s / 2) := by
  unfold LR_dalpha
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_neg]
  simp

/-- The coefficients of the derivatives of the loops are at most `e^{S/2} K` on `[0, S]`. -/
private lemma LR_Q_facts {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (hz : 0 < z.im)
    (S s : ℝ) (hs : s ∈ Set.Icc 0 S) (L : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hL : ∀ f ∈ L, f.2 = z ∨ f.2 = star z) (K : ℝ)
    (hK : K = 1 + ‖z‖ + 2 * ‖mExt Λ z‖ + opNorm Λ) :
    ‖LR_alpha s‖ * opNorm Λ ≤ Real.exp (S / 2) * K ∧
      (∀ g ∈ L, ‖LR_dz Λ g.2 s‖ ≤ Real.exp (S / 2) * K) ∧
      ‖LR_dalpha s‖ * opNorm Λ ≤ Real.exp (S / 2) * K ∧
      (∀ g ∈ L, ‖LR_ddz Λ g.2 s‖ ≤ Real.exp (S / 2) * K) := by
  obtain ⟨hs0, hsS⟩ := hs
  have hz0 := norm_nonneg z
  have hm0 := norm_nonneg (mExt Λ z)
  have ho0 : 0 ≤ opNorm Λ := norm_nonneg _
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hE1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp (by linarith)
  have hea : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hea0 := Real.exp_pos (-s / 2)
  have hES : Real.exp (s / 2) ≤ Real.exp (S / 2) := Real.exp_le_exp.2 (by linarith)
  have hKo : opNorm Λ ≤ K := by rw [hK]; linarith
  have hKz : (‖z‖ + 2 * ‖mExt Λ z‖) / 2 ≤ K := by rw [hK]; linarith
  have hEK : K ≤ Real.exp (S / 2) * K := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LR_norm_alpha]
    nlinarith [mul_le_mul hea hKo ho0 zero_le_one]
  · intro g hg
    obtain ⟨h1, h2⟩ := LR_norm_start Λ z hz g.2 (hL g hg)
    refine (LR_dz_norm Λ g.2 s hs0).trans ?_
    rw [h1, h2]
    have : (‖z‖ + 2 * ‖mExt Λ z‖) / 2 ≥ 0 := by positivity
    calc Real.exp (s / 2) * ((‖z‖ + 2 * ‖mExt Λ z‖) / 2)
        ≤ Real.exp (S / 2) * ((‖z‖ + 2 * ‖mExt Λ z‖) / 2) :=
          mul_le_mul_of_nonneg_right hES this
      _ ≤ Real.exp (S / 2) * K := mul_le_mul_of_nonneg_left hKz (by positivity)
  · rw [LR_norm_dalpha]
    nlinarith [mul_le_mul hea hKo ho0 zero_le_one]
  · intro g hg
    obtain ⟨h1, h2⟩ := LR_norm_start Λ z hz g.2 (hL g hg)
    refine (LR_ddz_norm Λ g.2 s hs0).trans ?_
    rw [h1, h2]
    have : (‖z‖ + 2 * ‖mExt Λ z‖) / 4 ≥ 0 := by positivity
    calc Real.exp (s / 2) * ((‖z‖ + 2 * ‖mExt Λ z‖) / 4)
        ≤ Real.exp (S / 2) * ((‖z‖ + 2 * ‖mExt Λ z‖) / 4) :=
          mul_le_mul_of_nonneg_right hES this
      _ ≤ Real.exp (S / 2) * K := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Collecting the factors of the final bound. -/
private lemma LR_big_le {a n1 pr Qq EK η : ℝ} {j m q r : ℕ} (ha : 0 ≤ a) (hn1 : 1 ≤ n1)
    (hpr : 0 ≤ pr) (hQ : 1 ≤ Qq) (hQEK : Qq ^ 2 ≤ EK) (hη : 0 < η) (hη1 : η ≤ 1) (hj : j ≤ 4)
    (hm : m ≤ 2) (hq : q ≤ r) :
    a * n1 ^ j * pr * Qq ^ m * (η ^ q)⁻¹ ≤ a * (n1 ^ 4 * EK * pr * (η ^ r)⁻¹) := by
  have h1 : n1 ^ j ≤ n1 ^ 4 := pow_le_pow_right₀ hn1 hj
  have h2 : Qq ^ m ≤ EK := (pow_le_pow_right₀ hQ hm).trans hQEK
  have h3 : (η ^ q)⁻¹ ≤ (η ^ r)⁻¹ := by
    rw [inv_le_inv₀ (pow_pos hη _) (pow_pos hη _)]
    exact pow_le_pow_of_le_one hη.le hη1 hq
  have hn0 : 0 ≤ n1 := by linarith
  have hQ0 : 0 ≤ Qq := by linarith
  have hEK0 : 0 ≤ EK := (sq_nonneg Qq).trans hQEK
  calc a * n1 ^ j * pr * Qq ^ m * (η ^ q)⁻¹
      ≤ a * n1 ^ 4 * pr * EK * (η ^ r)⁻¹ := by
        gcongr
    _ = a * (n1 ^ 4 * EK * pr * (η ^ r)⁻¹) := by ring
/-- Global bounds for the loops `⟨B₁G₁⋯B_pG_p⟩` at the Hermitian part of an array, as inputs of
`gaussStepA_expansion`: the loop is `C⁴` on all arrays and its `j`-th derivative, `j ≤ 4`, is at
most `c_{p,j} (DN + 1)^j Π‖B_r‖ η₀^{-(p+j)}` when `|Im ξ_r| ≥ η₀ > 0`. -/
theorem loopA_deriv_le :
    ∃ c : ℕ → ℕ → ℝ, ∀ (D N : ℕ) (η₀ : ℝ),
      ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      0 < η₀ → (∀ f ∈ l, f.2.1.IsHermitian ∧ η₀ ≤ |f.2.2.im|) →
        ContDiff ℝ 4 (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) ∧
        ∀ j : ℕ, j ≤ 4 → ∀ v : Idx D N → Idx D N → ℂ,
          ‖iteratedFDeriv ℝ j (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) v‖ ≤
            c l.length j * ((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
              (η₀ ^ (l.length + j))⁻¹ := by
  refine ⟨fun p j => (LR_cc p j : ℝ), ?_⟩
  intro D N η₀ l hη hl
  have : CompleteSpace (LR_Alg D N) := FiniteDimensional.complete ℂ _
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Idx D N) with hT
  set L := LR_L D N with hLdef
  have hone : ‖(1 : LR_Alg D N)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hne : ∀ f ∈ l, f.2.2.im ≠ 0 := fun f hf h0 => by
    have := (hl f hf).2
    rw [h0, abs_zero] at this
    linarith
  let Bf : LR_T D N → LR_Alg D N := fun f => T f.1
  let Gf : LR_T D N → (Idx D N → Idx D N → ℂ) → LR_Alg D N :=
    fun f h => Ring.inverse (L h + (T f.2.1 - f.2.2 • 1))
  have hLc : ∀ (f : LR_T D N) (h : Idx D N → Idx D N → ℂ), L h + (T f.2.1 - f.2.2 • 1) =
      T ((Matrix.of (hermPart h) + f.2.1) - f.2.2 • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
    intro f h
    rw [map_sub, map_add, map_smul, map_one, LR_L_apply]
    abel
  have hX : ∀ f ∈ l, ∀ h : Idx D N → Idx D N → ℂ,
      (Matrix.of (hermPart h) + f.2.1).IsHermitian := fun f hf h =>
    (LR_hermPart_herm h).add (hl f hf).1
  have hunit : ∀ f ∈ l, ∀ h : Idx D N → Idx D N → ℂ, IsUnit (L h + (T f.2.1 - f.2.2 • 1)) := by
    intro f hf h
    rw [hLc]
    exact (LR_inverse_eq _ (hX f hf h) f.2.2 (hne f hf)).1
  have hGeq : ∀ f ∈ l, ∀ h : Idx D N → Idx D N → ℂ,
      Gf f h = T (res (Matrix.of (hermPart h) + f.2.1) f.2.2) := by
    intro f hf h
    change Ring.inverse (L h + (T f.2.1 - f.2.2 • 1)) = _
    rw [hLc]
    exact (LR_inverse_eq _ (hX f hf h) f.2.2 (hne f hf)).2
  have hbound : ∀ f ∈ l, ∀ h : Idx D N → Idx D N → ℂ,
      ‖Ring.inverse (L h + (T f.2.1 - f.2.2 • 1))‖ ≤ η₀⁻¹ := by
    intro f hf h
    change ‖Gf f h‖ ≤ _
    rw [hGeq f hf h]
    exact LR_opNorm_res _ (hX f hf h) f.2.2 η₀ hη (hl f hf).2
  have hK0 : (0 : ℝ) ≤ ((D * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hinv : ∀ f ∈ l,
      (∀ n : ℕ, ContDiff ℝ n (Gf f)) ∧
      ∀ (j : ℕ) (h : Idx D N → Idx D N → ℂ), ‖iteratedFDeriv ℝ j (Gf f) h‖ ≤
        j.factorial * ((D * N : ℕ) : ℝ) ^ j * (η₀ ^ (j + 1))⁻¹ := fun f hf =>
    LR_inv_affine L (T f.2.1 - f.2.2 • 1) ((D * N : ℕ) : ℝ) η₀ (LR_L_norm D N) hη
      (hunit f hf) (hbound f hf)
  obtain ⟨hsm, hbd⟩ := LR_prod_bound hone ((D * N : ℕ) : ℝ) η₀ hK0 hη Bf Gf l
    (fun f hf => (hinv f hf).1) (fun f hf => (hinv f hf).2)
  have hTchain : ∀ h : Idx D N → Idx D N → ℂ, T (chainB (hermPart h) l) =
      (l.map fun f => Bf f * Gf f h).prod := by
    intro h
    unfold chainB
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    simp only [Function.comp, map_mul]
    rw [hGeq f hf h]
  have hFeq : (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (hermPart h) l)) =
      fun h => LR_ntr D N ((l.map fun f => Bf f * Gf f h).prod) := by
    funext h
    rw [← hTchain h, LR_ntr_apply]
  rw [hFeq]
  refine ⟨?_, fun j hj h => ?_⟩
  · exact (LR_ntr D N).contDiff.comp (by exact_mod_cast hsm 4)
  · have h1 : ‖iteratedFDeriv ℝ j
          (fun h => LR_ntr D N ((l.map fun f => Bf f * Gf f h).prod)) h‖ ≤
        ‖LR_ntr D N‖ *
          ‖iteratedFDeriv ℝ j (fun h => (l.map fun f => Bf f * Gf f h).prod) h‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left (LR_ntr D N)
        (f := fun h => (l.map fun f => Bf f * Gf f h).prod) (x := h) (N := j) (n := j)
        ((hsm j).contDiffAt) le_rfl
    refine h1.trans ?_
    have h2 := hbd j h
    have hnn : 0 ≤ ‖iteratedFDeriv ℝ j (fun h => (l.map fun f => Bf f * Gf f h).prod) h‖ :=
      norm_nonneg _
    have hprod : 0 ≤ (l.map fun f => opNorm f.1).prod := by
      refine List.prod_nonneg ?_
      intro x hx
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg _
    have hKj : (((D * N : ℕ) : ℝ)) ^ j ≤ ((D : ℝ) * N + 1) ^ j := by
      refine pow_le_pow_left₀ hK0 ?_ j
      push_cast
      linarith
    calc ‖LR_ntr D N‖ * ‖iteratedFDeriv ℝ j (fun h => (l.map fun f => Bf f * Gf f h).prod) h‖
        ≤ 1 * ‖iteratedFDeriv ℝ j (fun h => (l.map fun f => Bf f * Gf f h).prod) h‖ :=
          mul_le_mul_of_nonneg_right (LR_ntr_norm D N) hnn
      _ ≤ (LR_cc l.length j : ℝ) * ((D * N : ℕ) : ℝ) ^ j * (l.map fun f => opNorm f.1).prod *
          (η₀ ^ (l.length + j))⁻¹ := by rw [one_mul]; exact h2
      _ ≤ (LR_cc l.length j : ℝ) * ((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
          (η₀ ^ (l.length + j))⁻¹ := by gcongr


/-- Joint regularity of the loops along the flow, as inputs of `gaussStepA_expansion_t`: on
`[0, S]`, `S < t_c - t₀`, the loop `F(s, h)` of `flowLoop` has a time derivative `F_t`; `F(s, ·)`
and `F_t(s, ·)` are `C⁴` with derivatives of orders `1, …, 4` at most `B`, and `F_t` is
`B`-Lipschitz in `s`, for
`B = c_p (DN + 1)⁴ e^{t_c - t₀} (1 + |z| + 2|m| + ‖Λ‖)² Π‖B_r‖ (η_S ∧ 1)^{-(p+6)}`. -/
theorem flowLoop_regular :
    ∃ c : ℕ → ℝ, ∀ (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian →
      ∀ z : ℂ, 0 < z.im → ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ l, f.2 = z ∨ f.2 = star z) → ∀ S : ℝ, 0 ≤ S → S < flowTc Λ z →
      ∃ Ft : ℝ → (Idx D N → Idx D N → ℂ) → ℂ,
        (∀ s ∈ Set.Icc 0 S, ∀ v,
          HasDerivWithinAt (fun r => flowLoop Λ l r v) (Ft s v) (Set.Icc 0 S) s) ∧
        ∀ s ∈ Set.Icc 0 S, ContDiff ℝ 4 (flowLoop Λ l s) ∧ ContDiff ℝ 4 (Ft s) ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v,
            ‖iteratedFDeriv ℝ j (flowLoop Λ l s) v‖ ≤ c l.length * ((D : ℝ) * N + 1) ^ 4 *
                Real.exp (flowTc Λ z) * (1 + ‖z‖ + 2 * ‖mExt Λ z‖ + opNorm Λ) ^ 2 *
                (l.map fun f => opNorm f.1).prod *
                ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹ ∧
              ‖iteratedFDeriv ℝ j (Ft s) v‖ ≤ c l.length * ((D : ℝ) * N + 1) ^ 4 *
                Real.exp (flowTc Λ z) * (1 + ‖z‖ + 2 * ‖mExt Λ z‖ + opNorm Λ) ^ 2 *
                (l.map fun f => opNorm f.1).prod *
                ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹) ∧
          ∀ s' ∈ Set.Icc 0 S, ∀ v, ‖Ft s v - Ft s' v‖ ≤
            c l.length * ((D : ℝ) * N + 1) ^ 4 * Real.exp (flowTc Λ z) *
              (1 + ‖z‖ + 2 * ‖mExt Λ z‖ + opNorm Λ) ^ 2 * (l.map fun f => opNorm f.1).prod *
              ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹ * |s - s'| := by
  obtain ⟨cA, hcA0⟩ := loopA_deriv_le
  have hcA : LR_LB cA := hcA0
  have hcA' := LR_LB_abs cA hcA
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun p => 1 + (∑ j ∈ Finset.range 5, |cA p j|) +
      (∑ j ∈ Finset.range 5, 2 * (p : ℝ) * |cA (p + 1) j|) + 2 * (p : ℝ) * |cA (p + 1) 0| +
      4 * (p : ℝ) * ((p : ℝ) + 1) * |cA (p + 1 + 1) 0| := ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  intro D N Λ hΛ z hz l hl S hS hSt
  -- the index set is nonempty
  have hne : Nonempty (Idx D N) := by
    by_contra h
    have hemp : IsEmpty (Idx D N) := not_nonempty_iff.mp h
    have hno : ¬ ∃ w : ℂ, 0 < w.im ∧
        w = ntr (Λ - (z + w) • (1 : Matrix (Idx D N) (Idx D N) ℂ))⁻¹ := by
      rintro ⟨w, hw, hw2⟩
      have h0 : ntr ((Λ - (z + w) • (1 : Matrix (Idx D N) (Idx D N) ℂ))⁻¹) = 0 := by
        simp [ntr, Matrix.trace]
      rw [h0] at hw2
      rw [hw2] at hw
      simp at hw
    have hm0 : mExt Λ z = 0 := by
      simp only [mExt, hz, ↓reduceIte, mSol, hno, dite_false]
    have : flowTc Λ z = 0 := by simp [flowTc, hm0]
    linarith
  have := hne
  have hηS : 0 < (charFlowZ Λ z S).im := (charFlow_M Λ hΛ z hz S hSt).1
  have hη : 0 < min 1 (charFlowZ Λ z S).im := lt_min one_pos hηS
  have hη1 : min 1 (charFlowZ Λ z S).im ≤ 1 := min_le_left _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + ‖z‖ + 2 * ‖mExt Λ z‖ + opNorm Λ := ⟨_, rfl⟩
  rw [← hK]
  have hz0 := norm_nonneg z
  have hm0 := norm_nonneg (mExt Λ z)
  have ho0 : 0 ≤ opNorm Λ := norm_nonneg _
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hE1 : 1 ≤ Real.exp (S / 2) := Real.one_le_exp (by linarith)
  have hQ1 : 1 ≤ Real.exp (S / 2) * K := by nlinarith
  have hQ2 : (Real.exp (S / 2) * K) ^ 2 ≤ Real.exp (flowTc Λ z) * K ^ 2 := by
    have e : Real.exp (S / 2) ^ 2 = Real.exp S := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, e]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hSt.le) (by positivity)
  have hn1 : 1 ≤ (D : ℝ) * N + 1 := by
    have : 0 ≤ (D : ℝ) * N := by positivity
    linarith
  have hpr : 0 ≤ (l.map fun f => opNorm f.1).prod := by
    refine List.prod_nonneg ?_
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hBig : 0 ≤ ((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
      (l.map fun f => opNorm f.1).prod * ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹ := by
    have := Real.exp_pos (flowTc Λ z)
    have := inv_nonneg.2 (pow_nonneg hη.le (l.length + 6))
    positivity
  have hB : ∀ (a : ℝ) (j m q : ℕ), 0 ≤ a → j ≤ 4 → m ≤ 2 → q ≤ l.length + 6 →
      a * ((D : ℝ) * N + 1) ^ j * (l.map fun f => opNorm f.1).prod *
        (Real.exp (S / 2) * K) ^ m * ((min 1 (charFlowZ Λ z S).im) ^ q)⁻¹ ≤
      a * (((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
        (l.map fun f => opNorm f.1).prod *
        ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹) :=
    fun a j m q ha hj hm hq => LR_big_le ha hn1 hpr hQ1 hQ2 hη hη1 hj hm hq
  -- the constants
  have hcF : ∀ j, j ≤ 4 → |cA l.length j| ≤ c l.length := by
    intro j hj
    rw [hc]
    have h1 : |cA l.length j| ≤ ∑ j ∈ Finset.range 5, |cA l.length j| :=
      Finset.single_le_sum (f := fun j => |cA l.length j|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have h2 : 0 ≤ ∑ j ∈ Finset.range 5, 2 * (l.length : ℝ) * |cA (l.length + 1) j| :=
      Finset.sum_nonneg fun i _ => by positivity
    have h3 : 0 ≤ 2 * (l.length : ℝ) * |cA (l.length + 1) 0| := by positivity
    have h4 : 0 ≤ 4 * (l.length : ℝ) * ((l.length : ℝ) + 1) * |cA (l.length + 1 + 1) 0| := by
      positivity
    simp only
    linarith
  have hcT : ∀ j, j ≤ 4 → 2 * (l.length : ℝ) * |cA (l.length + 1) j| ≤ c l.length := by
    intro j hj
    rw [hc]
    have h1 : 2 * (l.length : ℝ) * |cA (l.length + 1) j| ≤
        ∑ j ∈ Finset.range 5, 2 * (l.length : ℝ) * |cA (l.length + 1) j| :=
      Finset.single_le_sum (f := fun j => 2 * (l.length : ℝ) * |cA (l.length + 1) j|)
        (fun i _ => by positivity) (Finset.mem_range.2 (by omega))
    have h2 : 0 ≤ ∑ j ∈ Finset.range 5, |cA l.length j| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have h3 : 0 ≤ 2 * (l.length : ℝ) * |cA (l.length + 1) 0| := by positivity
    have h4 : 0 ≤ 4 * (l.length : ℝ) * ((l.length : ℝ) + 1) * |cA (l.length + 1 + 1) 0| := by
      positivity
    simp only
    linarith
  have hcL : 2 * (l.length : ℝ) * |cA (l.length + 1) 0| +
      4 * (l.length : ℝ) * ((l.length : ℝ) + 1) * |cA (l.length + 1 + 1) 0| ≤ c l.length := by
    rw [hc]
    have h2 : 0 ≤ ∑ j ∈ Finset.range 5, |cA l.length j| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have h3 : 0 ≤ ∑ j ∈ Finset.range 5, 2 * (l.length : ℝ) * |cA (l.length + 1) j| :=
      Finset.sum_nonneg fun i _ => by positivity
    simp only
    linarith
  refine ⟨LR_dloop Λ l, fun s hs v =>
    (LR_hasDerivAt_flowLoop Λ hΛ z hz l hl s (hs.2.trans_lt hSt) v).hasDerivWithinAt, ?_⟩
  intro s hs
  obtain ⟨hQa, hQb, hQc, hQd⟩ := LR_Q_facts Λ z hz S s hs l hl K hK
  obtain ⟨hF4, hFb⟩ := LR_flowLoop_reg _ hcA' Λ hΛ z hz S hSt s hs l hl
  obtain ⟨hD4, hDb⟩ := LR_dloop_reg cA hcA Λ hΛ z hz S hSt s hs l hl _ hQa hQb
  refine ⟨hF4, hD4, fun j hj1 hj4 v => ⟨?_, ?_⟩, fun s' hs' v => ?_⟩
  · have h1 := hFb j hj4 v
    have h2 := hB (|cA l.length j|) j 0 (l.length + j) (abs_nonneg _) hj4 (by norm_num)
      (by omega)
    simp only [pow_zero, mul_one] at h2
    have h3 := h2.trans (mul_le_mul_of_nonneg_right (hcF j hj4) hBig)
    exact (h1.trans h3).trans_eq (by ring)
  · have h1 := hDb j hj4 v
    have h2 := hB (2 * (l.length : ℝ) * |cA (l.length + 1) j|) j 1 (l.length + 1 + j)
      (by positivity) hj4 (by norm_num) (by omega)
    have h3 := h2.trans (mul_le_mul_of_nonneg_right (hcT j hj4) hBig)
    refine (h1.trans (le_trans (le_of_eq ?_) h3)).trans_eq (by ring)
    ring
  · -- the Lipschitz bound
    have hderiv : ∀ x ∈ Set.Icc 0 S, HasDerivWithinAt (fun r => LR_dloop Λ l r v)
        (LR_d2 Λ l x v) (Set.Icc 0 S) x := fun x hx =>
      (LR_hasDerivAt_dloop Λ hΛ z hz l hl x (hx.2.trans_lt hSt) v).hasDerivWithinAt
    have hbd : ∀ x ∈ Set.Icc 0 S, ‖LR_d2 Λ l x v‖ ≤
        c l.length * (((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
          (l.map fun f => opNorm f.1).prod *
          ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹) := by
      intro x hx
      obtain ⟨hQa, hQb, hQc, hQd⟩ := LR_Q_facts Λ z hz S x hx l hl K hK
      refine (LR_d2_le cA hcA Λ hΛ z hz S hSt x hx l hl _ hQa hQb hQc hQd v).trans ?_
      have t1 := hB (|cA (l.length + 1) 0|) 0 1 (l.length + 1) (abs_nonneg _) (by norm_num)
        (by norm_num) (by omega)
      have t2 := hB (|cA (l.length + 1 + 1) 0|) 0 2 (l.length + 1 + 1) (abs_nonneg _)
        (by norm_num) (by norm_num) (by omega)
      simp only [pow_zero, mul_one, pow_one] at t1 t2
      have u2 : |cA (l.length + 1 + 1) 0| * (l.map fun f => opNorm f.1).prod *
          (Real.exp (S / 2) * K) * (Real.exp (S / 2) * K) *
            ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 1 + 1))⁻¹ ≤
          |cA (l.length + 1 + 1) 0| * (((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
            (l.map fun f => opNorm f.1).prod *
            ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹) :=
        le_trans (le_of_eq (by ring)) t2
      have hp0 : (0 : ℝ) ≤ (l.length : ℝ) := Nat.cast_nonneg _
      calc 2 * (l.length : ℝ) *
          (|cA (l.length + 1) 0| * (l.map fun f => opNorm f.1).prod * (Real.exp (S / 2) * K) *
            ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 1))⁻¹ +
          2 * ((l.length : ℝ) + 1) * (|cA (l.length + 1 + 1) 0| *
            (l.map fun f => opNorm f.1).prod * (Real.exp (S / 2) * K) * (Real.exp (S / 2) * K) *
            ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 1 + 1))⁻¹))
          ≤ 2 * (l.length : ℝ) *
            (|cA (l.length + 1) 0| * (((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
              (l.map fun f => opNorm f.1).prod *
              ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹) +
            2 * ((l.length : ℝ) + 1) * (|cA (l.length + 1 + 1) 0| *
              (((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
              (l.map fun f => opNorm f.1).prod *
              ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹))) :=
            mul_le_mul_of_nonneg_left (add_le_add t1
              (mul_le_mul_of_nonneg_left u2 (by positivity))) (by positivity)
        _ = (2 * (l.length : ℝ) * |cA (l.length + 1) 0| +
            4 * (l.length : ℝ) * ((l.length : ℝ) + 1) * |cA (l.length + 1 + 1) 0|) *
            (((D : ℝ) * N + 1) ^ 4 * (Real.exp (flowTc Λ z) * K ^ 2) *
              (l.map fun f => opNorm f.1).prod *
              ((min 1 (charFlowZ Λ z S).im) ^ (l.length + 6))⁻¹) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcL hBig
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd (convex_Icc 0 S) hs' hs
    rw [Real.norm_eq_abs] at this
    exact this.trans_eq (by ring)


end RBMTransitionEdge

end
