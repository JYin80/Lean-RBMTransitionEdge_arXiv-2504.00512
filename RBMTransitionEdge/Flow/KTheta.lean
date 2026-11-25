module

public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Det.EdgeStability
public import RBMTransitionEdge.Det.MhatSpec
public import RBMTransitionEdge.LocalLaw.Class

@[expose] public section

/-!
# `K_θ`

The matrices `P_θ`, `K_θ = (1 - M̂P_θ)⁻¹M̂` of (3.2) [def_K] and Definition 3.2 [defLK3]
with the class parameter `θ`, their Riccati equations (3.18) [eq:whMK], (3.19) [eq:whMK3],
and the bounds (A.8)–(A.11).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `P_θ = θ I + (1 - θ) J / D` on the block indices: the profile `S_θ` of `LLClass` acts as
`S_θ(X) = Σ_{x,c} (P_θ)_{xc} D ⟨X E_c⟩ E_x`. -/
def PTheta (D : ℕ) (θ : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (θ : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) +
    (((1 - θ) / D : ℝ) : ℂ) • Matrix.of fun _ _ => (1 : ℂ)

/-- `K_θ(z₁, z₂) = (1 - M̂ P_θ)⁻¹ M̂`; at `θ = 1` this is `K` of (3.2) [def_K]. -/
def KTheta {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * Mhat Λ z₁ z₂

/-- The contraction `Σ_{b₁b₂b₃} R¹_{a₁b₁} R²_{a₂b₂} R³_{a₃b₃} T_{b₁b₂b₃}` of Definition 3.2
[defLK3]. -/
def ten3Contr {D : ℕ} (R₁ R₂ R₃ : Matrix (Fin D) (Fin D) ℂ) (T : Fin D → Fin D → Fin D → ℂ) :
    Fin D → Fin D → Fin D → ℂ :=
  fun a₁ a₂ a₃ => ∑ b₁, ∑ b₂, ∑ b₃, R₁ a₁ b₁ * R₂ a₂ b₂ * R₃ a₃ b₃ * T b₁ b₂ b₃

/-- The tensor `K(z₁, z₂, z₃)` of Definition 3.2 [defLK3] with each `(1 - M̂_{(i,j)})⁻¹` replaced
by `(1 - M̂_{(i,j)} P_θ)⁻¹`; at `θ = 1` it is the tensor `K` of Definition 3.2 [defLK3]. -/
def KTheta3 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ z₃ : ℂ) :
    Fin D → Fin D → Fin D → ℂ :=
  ten3Contr (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ (1 - Mhat Λ z₂ z₃ * PTheta D θ)⁻¹
    (1 - Mhat Λ z₃ z₁ * PTheta D θ)⁻¹ fun b₁ b₂ b₃ => (D : ℂ) *
      ntr (MExt Λ z₁ * Ea D N b₁ * MExt Λ z₂ * Ea D N b₂ * MExt Λ z₃ * Ea D N b₃)

/-! ### Entrywise derivatives of matrix-valued functions of a real variable -/

section KT_Deriv

variable {n : Type*}

/-- `f' ` is the entrywise derivative at `s` of the matrix-valued function `f`. -/
private def KT_MHD (f : ℝ → Matrix n n ℂ) (f' : Matrix n n ℂ) (s : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun r => f r i j) (f' i j) s

private lemma KT_MHD_congr {f : ℝ → Matrix n n ℂ} {f' g' : Matrix n n ℂ} {s : ℝ}
    (h : KT_MHD f f' s) (e : g' = f') : KT_MHD f g' s := e ▸ h

private lemma KT_MHD_const (c : Matrix n n ℂ) (s : ℝ) : KT_MHD (fun _ => c) 0 s :=
  fun i j => by simpa using hasDerivAt_const s (c i j)

private lemma KT_MHD_add {f g : ℝ → Matrix n n ℂ} {f' g' : Matrix n n ℂ} {s : ℝ}
    (hf : KT_MHD f f' s) (hg : KT_MHD g g' s) : KT_MHD (fun r => f r + g r) (f' + g') s :=
  fun i j => (hf i j).add (hg i j)

private lemma KT_MHD_sub {f g : ℝ → Matrix n n ℂ} {f' g' : Matrix n n ℂ} {s : ℝ}
    (hf : KT_MHD f f' s) (hg : KT_MHD g g' s) : KT_MHD (fun r => f r - g r) (f' - g') s :=
  fun i j => (hf i j).sub (hg i j)

private lemma KT_MHD_smul {c : ℝ → ℂ} {c' : ℂ} {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ}
    {s : ℝ} (hc : HasDerivAt c c' s) (hf : KT_MHD f f' s) :
    KT_MHD (fun r => c r • f r) (c' • f s + c s • f') s :=
  fun i j => hc.mul (hf i j)

private lemma KT_MHD_mul [Fintype n] {f g : ℝ → Matrix n n ℂ} {f' g' : Matrix n n ℂ} {s : ℝ}
    (hf : KT_MHD f f' s) (hg : KT_MHD g g' s) :
    KT_MHD (fun r => f r * g r) (f' * g s + f s * g') s := by
  intro i j
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset n))
    (fun k _ => (hf i k).mul (hg k j))
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  rw [Finset.sum_add_distrib]

private lemma KT_det_diff [Fintype n] [DecidableEq n] {f : ℝ → Matrix n n ℂ}
    {f' : Matrix n n ℂ} {s : ℝ} (hf : KT_MHD f f' s) :
    DifferentiableAt ℝ (fun r => (f r).det) s := by
  have e : (fun r => (f r).det) = fun r => ∑ σ : Equiv.Perm n,
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f r (σ i) i := by
    funext r
    exact Matrix.det_apply' (f r)
  rw [e]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  exact (differentiableAt_const _).mul
    (HasDerivAt.fun_finsetProd (fun i _ => hf (σ i) i)).differentiableAt

private lemma KT_MHD_updateRow [DecidableEq n] {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ}
    {s : ℝ} (hf : KT_MHD f f' s) (j : n) (v : n → ℂ) :
    KT_MHD (fun r => (f r).updateRow j v) (f'.updateRow j 0) s := by
  intro a b
  by_cases h : a = j
  · subst h
    simpa [Matrix.updateRow_apply] using hasDerivAt_const s (v b)
  · simpa [Matrix.updateRow_apply, h] using hf a b

private lemma KT_inv_diff [Fintype n] [DecidableEq n] {f : ℝ → Matrix n n ℂ}
    {f' : Matrix n n ℂ} {s : ℝ} (hf : KT_MHD f f' s) (hdet : (f s).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun r => (f r)⁻¹ i j) s := by
  have e : ∀ r, (f r)⁻¹ i j =
      ((f r).det)⁻¹ * ((f r).updateRow j (Pi.single i 1)).det := by
    intro r
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv',
      smul_eq_mul]
  simp_rw [e]
  exact ((KT_det_diff hf).fun_inv hdet).mul (KT_det_diff (KT_MHD_updateRow hf j _))

/-- The derivative of the matrix inverse: `(f⁻¹)' = -f⁻¹ f' f⁻¹` where `det f ≠ 0`. -/
private lemma KT_MHD_inv [Fintype n] [DecidableEq n] {f : ℝ → Matrix n n ℂ}
    {f' : Matrix n n ℂ} {s : ℝ} (hf : KT_MHD f f' s) (hdet : (f s).det ≠ 0) :
    KT_MHD (fun r => (f r)⁻¹) (-((f s)⁻¹ * f' * (f s)⁻¹)) s := by
  set Rd : Matrix n n ℂ := Matrix.of fun i j => deriv (fun r => (f r)⁻¹ i j) s with hRd
  have hR : KT_MHD (fun r => (f r)⁻¹) Rd s := fun i j => (KT_inv_diff hf hdet i j).hasDerivAt
  have hev : ∀ᶠ r in nhds s, (f r).det ≠ 0 :=
    (KT_det_diff hf).continuousAt.eventually_ne hdet
  have hprod := KT_MHD_mul hR hf
  have hu : IsUnit (f s).det := isUnit_iff_ne_zero.2 hdet
  have key : Rd * f s + (f s)⁻¹ * f' = 0 := by
    ext i j
    have h1 : HasDerivAt (fun r => ((f r)⁻¹ * f r) i j) ((Rd * f s + (f s)⁻¹ * f') i j) s :=
      hprod i j
    have h2 : HasDerivAt (fun r => ((f r)⁻¹ * f r) i j) 0 s := by
      refine (hasDerivAt_const s ((1 : Matrix n n ℂ) i j)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with r hr
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hr)]
    simpa using h1.unique h2
  have key' : Rd * f s = -((f s)⁻¹ * f') := eq_neg_of_add_eq_zero_left key
  have hRd' : Rd = -((f s)⁻¹ * f' * (f s)⁻¹) := by
    calc Rd = Rd * (f s * (f s)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (Rd * f s) * (f s)⁻¹ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [key', Matrix.neg_mul]
  rw [← hRd']
  exact hR

end KT_Deriv

/-- With `θ_r = 1 - e^{-r}(1 - θ₀)` one has `d P_{θ_r}/dr = 1 - P_{θ_r}`, entrywise. -/
private lemma KT_P_deriv (D : ℕ) (θ₀ s : ℝ) :
    KT_MHD (fun r : ℝ => PTheta D (1 - Real.exp (-r) * (1 - θ₀)))
      (1 - PTheta D (1 - Real.exp (-s) * (1 - θ₀))) s := by
  have hu : HasDerivAt (fun r : ℝ => Real.exp (-r) * (1 - θ₀))
      (-(Real.exp (-s)) * (1 - θ₀)) s := by
    have := ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).mul_const (1 - θ₀)
    simpa using this
  have h1 : HasDerivAt (fun r : ℝ => ((1 - Real.exp (-r) * (1 - θ₀) : ℝ) : ℂ))
      ((Real.exp (-s) * (1 - θ₀) : ℝ) : ℂ) s := by
    have := ((hasDerivAt_const s (1 : ℝ)).sub hu).ofReal_comp
    simpa using this
  have h2 : HasDerivAt (fun r : ℝ => (((1 - (1 - Real.exp (-r) * (1 - θ₀))) / D : ℝ) : ℂ))
      ((-(Real.exp (-s) * (1 - θ₀)) / D : ℝ) : ℂ) s := by
    have := (((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_const s (1 : ℝ)).sub hu)).div_const
      (D : ℝ)).ofReal_comp
    simpa using this
  have h := KT_MHD_add (KT_MHD_smul h1 (KT_MHD_const (1 : Matrix (Fin D) (Fin D) ℂ) s))
    (KT_MHD_smul h2 (KT_MHD_const (Matrix.of fun _ _ => (1 : ℂ)) s))
  refine KT_MHD_congr h ?_
  ext i j
  simp only [PTheta, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  push_cast
  split_ifs <;> ring

/-- `d(e^r X)/dr = e^r X`, entrywise. -/
private lemma KT_X_deriv (D : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) (s : ℝ) :
    KT_MHD (fun r : ℝ => ((Real.exp r : ℝ) : ℂ) • X) (((Real.exp s : ℝ) : ℂ) • X) s := by
  have hE : HasDerivAt (fun r : ℝ => ((Real.exp r : ℝ) : ℂ)) ((Real.exp s : ℝ) : ℂ) s :=
    (Real.hasDerivAt_exp s).ofReal_comp
  refine KT_MHD_congr (KT_MHD_smul hE (KT_MHD_const X s)) ?_
  simp

/-- The Riccati step `R' = R (e^s X) R` for `R_r = (1 - e^r X P_{θ_r})⁻¹`, entrywise. -/
private lemma KT_R_deriv (D : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) (θ₀ s : ℝ)
    (hU : (1 - ((Real.exp s : ℝ) : ℂ) • X *
      PTheta D (1 - Real.exp (-s) * (1 - θ₀))).det ≠ 0) :
    KT_MHD (fun r : ℝ => (1 - ((Real.exp r : ℝ) : ℂ) • X *
        PTheta D (1 - Real.exp (-r) * (1 - θ₀)))⁻¹)
      ((1 - ((Real.exp s : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-s) * (1 - θ₀)))⁻¹ *
        (((Real.exp s : ℝ) : ℂ) • X) *
        (1 - ((Real.exp s : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-s) * (1 - θ₀)))⁻¹) s := by
  have hY := KT_MHD_mul (KT_X_deriv D X s) (KT_P_deriv D θ₀ s)
  have hW := KT_MHD_sub (KT_MHD_const (1 : Matrix (Fin D) (Fin D) ℂ) s) hY
  refine KT_MHD_congr (KT_MHD_inv hW hU) ?_
  set P := PTheta D (1 - Real.exp (-s) * (1 - θ₀))
  set Xs := ((Real.exp s : ℝ) : ℂ) • X
  have e1 : (0 : Matrix (Fin D) (Fin D) ℂ) - (Xs * P + Xs * (1 - P)) = -Xs := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [e1]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]

/-- (3.18) [eq:whMK], second equation, with the class parameter: for `θ_r = 1 - e^{-r}(1 - θ₀)`
(the parameter of the block-OU law) and `M̂_r = e^r X`, `K_r = (1 - M̂_r P_{θ_r})⁻¹ M̂_r`
satisfies `dK_r/dr = K_r² + K_r`, entrywise. -/
theorem kTheta_riccati (D : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) (θ₀ s : ℝ)
    (hU : (1 - ((Real.exp s : ℝ) : ℂ) • X *
      PTheta D (1 - Real.exp (-s) * (1 - θ₀))).det ≠ 0) (a b : Fin D) :
    HasDerivAt (fun r : ℝ => ((1 - ((Real.exp r : ℝ) : ℂ) • X *
        PTheta D (1 - Real.exp (-r) * (1 - θ₀)))⁻¹ * (((Real.exp r : ℝ) : ℂ) • X)) a b)
      ((((1 - ((Real.exp s : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-s) * (1 - θ₀)))⁻¹ *
          (((Real.exp s : ℝ) : ℂ) • X)) * ((1 - ((Real.exp s : ℝ) : ℂ) • X *
          PTheta D (1 - Real.exp (-s) * (1 - θ₀)))⁻¹ * (((Real.exp s : ℝ) : ℂ) • X)) +
        (1 - ((Real.exp s : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-s) * (1 - θ₀)))⁻¹ *
          (((Real.exp s : ℝ) : ℂ) • X)) a b) s := by
  have hX := KT_X_deriv D X s
  have hK := KT_MHD_mul (KT_R_deriv D X θ₀ s hU) hX
  refine (KT_MHD_congr hK ?_) a b
  simp only [Matrix.mul_assoc]

section KT_Ten3

variable {D : ℕ}

private lemma KT_sum4 (f : Fin D → Fin D → Fin D → Fin D → ℂ) :
    ∑ b₁, ∑ b₂, ∑ b₃, ∑ a, f a b₁ b₂ b₃ = ∑ a, ∑ b₁, ∑ b₂, ∑ b₃, f a b₁ b₂ b₃ := by
  calc ∑ b₁, ∑ b₂, ∑ b₃, ∑ a, f a b₁ b₂ b₃
      = ∑ b₁, ∑ b₂, ∑ a, ∑ b₃, f a b₁ b₂ b₃ :=
        Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => Finset.sum_comm
    _ = ∑ b₁, ∑ a, ∑ b₂, ∑ b₃, f a b₁ b₂ b₃ :=
        Finset.sum_congr rfl fun b₁ _ => Finset.sum_comm
    _ = ∑ a, ∑ b₁, ∑ b₂, ∑ b₃, f a b₁ b₂ b₃ := Finset.sum_comm

private lemma KT_ten3_slot₁ (K R₁ R₂ R₃ : Matrix (Fin D) (Fin D) ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (a₁ a₂ a₃ : Fin D) :
    ten3Contr (K * R₁) R₂ R₃ T a₁ a₂ a₃ = ∑ a, K a₁ a * ten3Contr R₁ R₂ R₃ T a a₂ a₃ := by
  unfold ten3Contr
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine (KT_sum4 (fun a b₁ b₂ b₃ => K a₁ a * R₁ a b₁ * R₂ a₂ b₂ * R₃ a₃ b₃ *
    T b₁ b₂ b₃)).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
    Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₃ _ => ?_
  ring

private lemma KT_ten3_slot₂ (K R₁ R₂ R₃ : Matrix (Fin D) (Fin D) ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (a₁ a₂ a₃ : Fin D) :
    ten3Contr R₁ (K * R₂) R₃ T a₁ a₂ a₃ = ∑ a, K a₂ a * ten3Contr R₁ R₂ R₃ T a₁ a a₃ := by
  unfold ten3Contr
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine (KT_sum4 (fun a b₁ b₂ b₃ => R₁ a₁ b₁ * (K a₂ a * R₂ a b₂) * R₃ a₃ b₃ *
    T b₁ b₂ b₃)).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
    Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₃ _ => ?_
  ring

private lemma KT_ten3_slot₃ (K R₁ R₂ R₃ : Matrix (Fin D) (Fin D) ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (a₁ a₂ a₃ : Fin D) :
    ten3Contr R₁ R₂ (K * R₃) T a₁ a₂ a₃ = ∑ a, K a₃ a * ten3Contr R₁ R₂ R₃ T a₁ a₂ a := by
  unfold ten3Contr
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine (KT_sum4 (fun a b₁ b₂ b₃ => R₁ a₁ b₁ * R₂ a₂ b₂ * (K a₃ a * R₃ a b₃) *
    T b₁ b₂ b₃)).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b₁ _ =>
    Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₃ _ => ?_
  ring

private lemma KT_ten3_scale (R₁ R₂ R₃ : Matrix (Fin D) (Fin D) ℂ) (c : ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (a₁ a₂ a₃ : Fin D) :
    ten3Contr R₁ R₂ R₃ (fun b₁ b₂ b₃ => c * T b₁ b₂ b₃) a₁ a₂ a₃ =
      c * ten3Contr R₁ R₂ R₃ T a₁ a₂ a₃ := by
  unfold ten3Contr
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ =>
    Finset.sum_congr rfl fun b₃ _ => ?_
  ring

/-- Leibniz rule for the contraction `ten3Contr` along matrix-valued curves and a scalar weight. -/
private lemma KT_ten3_deriv {R₁ R₂ R₃ : ℝ → Matrix (Fin D) (Fin D) ℂ}
    {R₁' R₂' R₃' : Matrix (Fin D) (Fin D) ℂ} {c : ℝ → ℂ} {c' : ℂ} {s : ℝ}
    (T : Fin D → Fin D → Fin D → ℂ) (a₁ a₂ a₃ : Fin D)
    (h₁ : KT_MHD R₁ R₁' s) (h₂ : KT_MHD R₂ R₂' s) (h₃ : KT_MHD R₃ R₃' s)
    (hc : HasDerivAt c c' s) :
    HasDerivAt (fun r => ten3Contr (R₁ r) (R₂ r) (R₃ r)
        (fun b₁ b₂ b₃ => c r * T b₁ b₂ b₃) a₁ a₂ a₃)
      (ten3Contr R₁' (R₂ s) (R₃ s) (fun b₁ b₂ b₃ => c s * T b₁ b₂ b₃) a₁ a₂ a₃ +
        ten3Contr (R₁ s) R₂' (R₃ s) (fun b₁ b₂ b₃ => c s * T b₁ b₂ b₃) a₁ a₂ a₃ +
        ten3Contr (R₁ s) (R₂ s) R₃' (fun b₁ b₂ b₃ => c s * T b₁ b₂ b₃) a₁ a₂ a₃ +
        ten3Contr (R₁ s) (R₂ s) (R₃ s) (fun b₁ b₂ b₃ => c' * T b₁ b₂ b₃) a₁ a₂ a₃) s := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin D))) fun b₁ _ =>
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin D))) fun b₂ _ =>
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin D))) fun b₃ _ =>
      ((((h₁ a₁ b₁).mul (h₂ a₂ b₂)).mul (h₃ a₃ b₃)).mul (hc.mul_const (T b₁ b₂ b₃)))
  refine h.congr_deriv ?_
  unfold ten3Contr
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ =>
    Finset.sum_congr rfl fun b₃ _ => ?_
  simp only [Pi.mul_apply]
  ring

end KT_Ten3

/-- (3.19) [eq:whMK3] with the class parameter: for `R^{ij}_r = (1 - e^r X_{ij} P_{θ_r})⁻¹`,
`K^{ij}_r = R^{ij}_r e^r X_{ij}` and `K_r = Σ R¹² R²³ R³¹ (e^{3r/2} T)`, entrywise
`dK_r/dr = (3/2) K_r + Σ_a (K¹²_{a₁a} K_{a a₂ a₃} + K²³_{a₂a} K_{a₁ a a₃}`
`+ K³¹_{a₃a} K_{a₁ a₂ a})`. -/
theorem kTheta3_riccati (D : ℕ) (X₁₂ X₂₃ X₃₁ : Matrix (Fin D) (Fin D) ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (θ₀ s : ℝ)
    (hU : ∀ X ∈ ({X₁₂, X₂₃, X₃₁} : Set (Matrix (Fin D) (Fin D) ℂ)),
      (1 - ((Real.exp s : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-s) * (1 - θ₀))).det ≠ 0)
    (a₁ a₂ a₃ : Fin D) :
    HasDerivAt (fun r : ℝ => ten3Contr
        (1 - ((Real.exp r : ℝ) : ℂ) • X₁₂ * PTheta D (1 - Real.exp (-r) * (1 - θ₀)))⁻¹
        (1 - ((Real.exp r : ℝ) : ℂ) • X₂₃ * PTheta D (1 - Real.exp (-r) * (1 - θ₀)))⁻¹
        (1 - ((Real.exp r : ℝ) : ℂ) • X₃₁ * PTheta D (1 - Real.exp (-r) * (1 - θ₀)))⁻¹
        (fun b₁ b₂ b₃ => ((Real.exp (3 * r / 2) : ℝ) : ℂ) * T b₁ b₂ b₃) a₁ a₂ a₃)
      (let R : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ := fun X =>
          (1 - ((Real.exp s : ℝ) : ℂ) • X * PTheta D (1 - Real.exp (-s) * (1 - θ₀)))⁻¹
        let K₃ := ten3Contr (R X₁₂) (R X₂₃) (R X₃₁)
          (fun b₁ b₂ b₃ => ((Real.exp (3 * s / 2) : ℝ) : ℂ) * T b₁ b₂ b₃)
        let K : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ := fun X =>
          R X * (((Real.exp s : ℝ) : ℂ) • X)
        (3 / 2 : ℂ) * K₃ a₁ a₂ a₃ + ∑ a, (K X₁₂ a₁ a * K₃ a a₂ a₃ + K X₂₃ a₂ a * K₃ a₁ a a₃ +
          K X₃₁ a₃ a * K₃ a₁ a₂ a)) s := by
  have hc : HasDerivAt (fun r : ℝ => ((Real.exp (3 * r / 2) : ℝ) : ℂ))
      (((Real.exp (3 * s / 2) : ℝ) : ℂ) * (3 / 2)) s := by
    have h0 : HasDerivAt (fun r : ℝ => 3 * r / 2) (3 / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul 3).div_const 2
    have := ((Real.hasDerivAt_exp (3 * s / 2)).comp s h0).ofReal_comp
    refine this.congr_deriv ?_
    push_cast
    ring
  have h := KT_ten3_deriv T a₁ a₂ a₃ (KT_R_deriv D X₁₂ θ₀ s (hU X₁₂ (by simp)))
    (KT_R_deriv D X₂₃ θ₀ s (hU X₂₃ (by simp))) (KT_R_deriv D X₃₁ θ₀ s (hU X₃₁ (by simp))) hc
  refine h.congr_deriv ?_
  dsimp only
  simp only [KT_ten3_slot₁, KT_ten3_slot₂, KT_ten3_slot₃, KT_ten3_scale, Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  ring_nf

/-! ### The Fourier basis of `ℂ^D` and circulant matrices -/

section KT_Fourier

open scoped Matrix.Norms.L2Operator

private lemma KT_op_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm A = ‖A‖ := rfl

open scoped Matrix.Norms.L2Operator

/-- The primitive root `ζ = e^{2πi/D}`. -/
private def KT_zeta (D : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / D)

private lemma KT_zeta_prim (D : ℕ) (hD : D ≠ 0) : IsPrimitiveRoot (KT_zeta D) D :=
  Complex.isPrimitiveRoot_exp D hD

private lemma KT_norm_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) : ‖KT_zeta D ^ k‖ = 1 := by
  rw [norm_pow, (KT_zeta_prim D hD).norm'_eq_one hD, one_pow]

private lemma KT_star_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) :
    star (KT_zeta D ^ k) * KT_zeta D ^ k = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    KT_norm_zeta_pow D hD]
  simp

private lemma KT_fourierVec_eq (D : ℕ) (l a : Fin D) :
    fourierVec D l a = ((Real.sqrt D : ℂ))⁻¹ * KT_zeta D ^ ((l : ℕ) * (a : ℕ)) := by
  unfold fourierVec KT_zeta
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The unitary matrix whose columns are the Fourier vectors `u_l`. -/
private def KT_F (D : ℕ) : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun a l => fourierVec D l a

private lemma KT_sqrt_inv_sq (D : ℕ) :
    star ((Real.sqrt D : ℂ))⁻¹ * ((Real.sqrt D : ℂ))⁻¹ = (D : ℂ)⁻¹ := by
  have h : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt h]
  simp

private lemma KT_F_unitary (D : ℕ) (hD : D ≠ 0) : (KT_F D)ᴴ * KT_F D = 1 := by
  have hζ := KT_zeta_prim D hD
  ext l l'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, KT_F, Matrix.of_apply,
    KT_fourierVec_eq, Matrix.one_apply]
  have e : ∀ a : Fin D, star (((Real.sqrt D : ℂ))⁻¹ * KT_zeta D ^ ((l : ℕ) * (a : ℕ))) *
      (((Real.sqrt D : ℂ))⁻¹ * KT_zeta D ^ ((l' : ℕ) * (a : ℕ))) =
      (D : ℂ)⁻¹ * (star (KT_zeta D ^ (l : ℕ)) * KT_zeta D ^ (l' : ℕ)) ^ (a : ℕ) := by
    intro a
    rw [star_mul', mul_pow, ← star_pow, ← pow_mul, ← pow_mul, ← KT_sqrt_inv_sq D]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (star (KT_zeta D ^ (l : ℕ)) * KT_zeta D ^ (l' : ℕ)) ^ a)]
  by_cases hll : l = l'
  · subst hll
    rw [KT_star_zeta_pow D hD]
    simp [hD]
  · simp only [hll, ↓reduceIte]
    set r := star (KT_zeta D ^ (l : ℕ)) * KT_zeta D ^ (l' : ℕ) with hr
    have hrD : r ^ D = 1 := by
      rw [hr, mul_pow, ← star_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ), mul_comm (l' : ℕ),
        pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, star_one, one_mul]
    have hr1 : r ≠ 1 := by
      intro h1
      have : KT_zeta D ^ (l' : ℕ) = KT_zeta D ^ (l : ℕ) := by
        have h2 := congrArg (fun x => KT_zeta D ^ (l : ℕ) * x) h1
        simp only [mul_one] at h2
        rw [hr, ← mul_assoc, mul_comm (KT_zeta D ^ (l : ℕ)), KT_star_zeta_pow D hD, one_mul] at h2
        exact h2
      exact hll (Fin.ext (hζ.pow_inj l.isLt l'.isLt this.symm))
    have hg := geom_sum_mul r D
    rw [hrD, sub_self] at hg
    have : ∑ i ∈ Finset.range D, r ^ i = 0 :=
      (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)
    rw [this, mul_zero]

private lemma KT_F_unitary' (D : ℕ) (hD : D ≠ 0) : KT_F D * (KT_F D)ᴴ = 1 :=
  mul_eq_one_comm.mp (KT_F_unitary D hD)

private lemma KT_F_norm (D : ℕ) (hD : D ≠ 0) : ‖KT_F D‖ ≤ 1 := by
  have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (KT_F D)
  rw [KT_F_unitary D hD, norm_one] at h1
  nlinarith [norm_nonneg (KT_F D)]

/-- A matrix with eigenvectors `u_l` and eigenvalues `μ_l` is `F diag(μ) F^*`. -/
private lemma KT_circ (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) :
    B = KT_F D * diagonal μ * (KT_F D)ᴴ := by
  have h1 : B * KT_F D = KT_F D * diagonal μ := by
    ext a l
    have := congrFun (hB l) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, KT_F, Matrix.of_apply]
    rw [this, mul_comm]
  calc B = B * (KT_F D * (KT_F D)ᴴ) := by rw [KT_F_unitary' D hD, Matrix.mul_one]
    _ = KT_F D * diagonal μ * (KT_F D)ᴴ := by rw [← Matrix.mul_assoc, h1]

private lemma KT_conjF_norm (D : ℕ) (hD : D ≠ 0) (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖KT_F D * X * (KT_F D)ᴴ‖ = ‖X‖ := by
  have hF := KT_F_norm D hD
  have hF' : ‖(KT_F D)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hF
  apply le_antisymm
  · calc ‖KT_F D * X * (KT_F D)ᴴ‖ ≤ ‖KT_F D‖ * ‖X‖ * ‖(KT_F D)ᴴ‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  · have e : X = (KT_F D)ᴴ * (KT_F D * X * (KT_F D)ᴴ) * KT_F D := by
      simp only [← Matrix.mul_assoc, KT_F_unitary D hD, Matrix.one_mul]
      rw [Matrix.mul_assoc, KT_F_unitary D hD, Matrix.mul_one]
    calc ‖X‖ = ‖(KT_F D)ᴴ * (KT_F D * X * (KT_F D)ᴴ) * KT_F D‖ := by rw [← e]
      _ ≤ ‖(KT_F D)ᴴ‖ * ‖KT_F D * X * (KT_F D)ᴴ‖ * ‖KT_F D‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖KT_F D * X * (KT_F D)ᴴ‖ * 1 := by gcongr
      _ = _ := by ring

/-- For `B` with eigenvectors `u_l` and eigenvalues `μ_l ≠ 1`: `1 - B` is invertible,
`(1 - B)⁻¹ = F diag((1 - μ)⁻¹) F^*`, and `‖(1 - B)⁻¹‖ = max_l |1 - μ_l|⁻¹`. -/
private lemma KT_circ_inv (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) (hμ : ∀ l, 1 - μ l ≠ 0) :
    (1 - B).det ≠ 0 ∧
      (1 - B)⁻¹ = KT_F D * diagonal (fun l => (1 - μ l)⁻¹) * (KT_F D)ᴴ ∧
      opNorm ((1 - B)⁻¹) = ‖fun l => (1 - μ l)⁻¹‖ := by
  have hc := KT_circ D hD B μ hB
  have h1 : 1 - B = KT_F D * diagonal (fun l => 1 - μ l) * (KT_F D)ᴴ := by
    have : diagonal (fun l => 1 - μ l) = 1 - diagonal μ := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, KT_F_unitary' D hD, ← hc]
  have hinv : (1 - B)⁻¹ = KT_F D * diagonal (fun l => (1 - μ l)⁻¹) * (KT_F D)ᴴ := by
    rw [h1]
    apply Matrix.inv_eq_right_inv
    have e : KT_F D * diagonal (fun l => 1 - μ l) * (KT_F D)ᴴ *
        (KT_F D * diagonal (fun l => (1 - μ l)⁻¹) * (KT_F D)ᴴ) =
        KT_F D * (diagonal (fun l => 1 - μ l) * ((KT_F D)ᴴ * KT_F D) *
          diagonal (fun l => (1 - μ l)⁻¹)) * (KT_F D)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, KT_F_unitary D hD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    have : (fun l => (1 - μ l) * (1 - μ l)⁻¹) = fun _ => (1 : ℂ) := by
      funext l; exact mul_inv_cancel₀ (hμ l)
    rw [this, Matrix.diagonal_one, Matrix.mul_one, KT_F_unitary' D hD]
  refine ⟨?_, hinv, ?_⟩
  · rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hdet : (KT_F D).det * ((KT_F D)ᴴ).det = 1 := by
      rw [← Matrix.det_mul, KT_F_unitary' D hD, Matrix.det_one]
    have : (KT_F D).det * (∏ l, (1 - μ l)) * ((KT_F D)ᴴ).det = ∏ l, (1 - μ l) := by
      linear_combination (∏ l, (1 - μ l)) * hdet
    rw [this]
    exact Finset.prod_ne_zero_iff.2 fun l _ => hμ l
  · rw [hinv, KT_op_eq, KT_conjF_norm D hD, Matrix.l2_opNorm_diagonal]

/-- The entries of `F diag(κ) F^*` differ by at most `2 max_{l ≠ 0} |κ_l|`. -/
private lemma KT_entry_diff (D : ℕ) [NeZero D] (κ : Fin D → ℂ) (Kb : ℝ) (hKb : 0 ≤ Kb)
    (hκ : ∀ l : Fin D, (l : ℕ) ≠ 0 → ‖κ l‖ ≤ Kb) (a b a' b' : Fin D) :
    ‖(KT_F D * diagonal κ * (KT_F D)ᴴ) a b - (KT_F D * diagonal κ * (KT_F D)ᴴ) a' b'‖ ≤
      2 * Kb := by
  have hD : D ≠ 0 := NeZero.ne D
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have happ : ∀ x y : Fin D, (KT_F D * diagonal κ * (KT_F D)ᴴ) x y =
      ∑ l : Fin D, κ l * (KT_F D x l * star (KT_F D y l)) := by
    intro x y
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring
  have hF : ∀ x y l : Fin D, KT_F D x l * star (KT_F D y l) =
      (D : ℂ)⁻¹ * (KT_zeta D ^ ((l : ℕ) * (x : ℕ)) * star (KT_zeta D ^ ((l : ℕ) * (y : ℕ)))) := by
    intro x y l
    simp only [KT_F, Matrix.of_apply, KT_fourierVec_eq, star_mul']
    rw [← KT_sqrt_inv_sq D]
    ring
  have hFn : ∀ x y l : Fin D, ‖KT_F D x l * star (KT_F D y l)‖ = (D : ℝ)⁻¹ := by
    intro x y l
    rw [hF, norm_mul, norm_mul, norm_star, KT_norm_zeta_pow D hD, KT_norm_zeta_pow D hD, norm_inv,
      Complex.norm_natCast]
    ring
  rw [happ, happ, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l : Fin D, ‖κ l * (KT_F D a l * star (KT_F D b l)) -
        κ l * (KT_F D a' l * star (KT_F D b' l))‖ ≤ ∑ _l : Fin D, 2 * Kb / D := by
        refine Finset.sum_le_sum fun l _ => ?_
        by_cases hl : (l : ℕ) = 0
        · rw [hF, hF, hl]
          simp only [zero_mul, pow_zero, star_one, mul_one, sub_self, norm_zero]
          positivity
        · rw [← mul_sub, norm_mul]
          have h2 : ‖KT_F D a l * star (KT_F D b l) - KT_F D a' l * star (KT_F D b' l)‖ ≤
              2 / D := by
            refine (norm_sub_le _ _).trans ?_
            rw [hFn, hFn]; ring_nf; rfl
          calc ‖κ l‖ * ‖KT_F D a l * star (KT_F D b l) - KT_F D a' l * star (KT_F D b' l)‖
              ≤ Kb * (2 / D) := mul_le_mul (hκ l hl) h2 (norm_nonneg _) hKb
            _ = 2 * Kb / D := by ring
    _ = 2 * Kb := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- A vector `u_l` is an eigenvector of `B` with eigenvalue `μ`: `μ = Σ_b B_{0b} ζ^{lb}`. -/
private lemma KT_row (D : ℕ) [NeZero D] (B : Matrix (Fin D) (Fin D) ℂ) (l : Fin D) (μ : ℂ)
    (hB : B *ᵥ fourierVec D l = μ • fourierVec D l) :
    μ = ∑ b : Fin D, B 0 b * KT_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
  have hD : D ≠ 0 := NeZero.ne D
  have := congrFun hB 0
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, KT_fourierVec_eq,
    Fin.val_zero, mul_zero, pow_zero, mul_one] at this
  have hs : ((Real.sqrt D : ℂ))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast Nat.pos_of_ne_zero hD
  have e : ∑ x : Fin D, B 0 x * (((Real.sqrt D : ℂ))⁻¹ * KT_zeta D ^ ((l : ℕ) * (x : ℕ))) =
      ((Real.sqrt D : ℂ))⁻¹ * ∑ b : Fin D, B 0 b * KT_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [e] at this
  rw [mul_comm μ] at this
  exact (mul_left_cancel₀ hs this).symm

/-- `Σ_b ζ^{lb} = 0` for `l ≠ 0`. -/
private lemma KT_sum_zeta (D : ℕ) (hD : D ≠ 0) (l : Fin D) (hl : (l : ℕ) ≠ 0) :
    ∑ b : Fin D, KT_zeta D ^ ((l : ℕ) * (b : ℕ)) = 0 := by
  have hζ := KT_zeta_prim D hD
  set r := KT_zeta D ^ (l : ℕ) with hr
  have e : ∀ b : Fin D, KT_zeta D ^ ((l : ℕ) * (b : ℕ)) = r ^ (b : ℕ) := fun b => by
    rw [hr, ← pow_mul]
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun b => r ^ b) D]
  have hrD : r ^ D = 1 := by
    rw [hr, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hr1 : r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hl l.isLt
  have hg := geom_sum_mul r D
  rw [hrD, sub_self] at hg
  exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)

/-- The block profile `P_θ` acts on `u_0` as the identity and on `u_l`, `l ≠ 0`, as `θ`. -/
private lemma KT_P_eig (D : ℕ) (hD : D ≠ 0) (θ : ℝ) (l : Fin D) :
    PTheta D θ *ᵥ fourierVec D l =
      (if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ)) • fourierVec D l := by
  have : NeZero D := ⟨hD⟩
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have hJ : ∀ a : Fin D, ((Matrix.of fun _ _ => (1 : ℂ)) *ᵥ fourierVec D l) a =
      ∑ b, fourierVec D l b := fun a => by simp [Matrix.mulVec, dotProduct]
  have hsum : ∑ b, fourierVec D l b =
      ((Real.sqrt D : ℂ))⁻¹ * ∑ b : Fin D, KT_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => KT_fourierVec_eq D l b
  ext a
  simp only [PTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hJ, hsum]
  by_cases hl : (l : ℕ) = 0
  · simp only [hl, ↓reduceIte, zero_mul, pow_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [KT_fourierVec_eq, hl]
    simp only [zero_mul, pow_zero, mul_one]
    push_cast
    field_simp
    ring
  · simp only [hl, ↓reduceIte, KT_sum_zeta D hD l hl, mul_zero, add_zero]

/-- For `|μ| ≤ 1` and `θ ∈ [0, 1]`: `|1 - μ| ≤ 2 |1 - θ μ|`. -/
private lemma KT_scalar (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖1 - μ‖ ≤ 2 * ‖1 - (θ : ℂ) * μ‖ := by
  have e : 1 - μ = (1 - (θ : ℂ) * μ) - ((1 - θ : ℝ) : ℂ) * μ := by push_cast; ring
  have hn : ‖((1 - θ : ℝ) : ℂ) * μ‖ ≤ 1 - θ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg μ]
  by_cases hc : 2 * (1 - θ) ≤ ‖1 - μ‖
  · have h2 := norm_sub_le (1 - (θ : ℂ) * μ) (((1 - θ : ℝ) : ℂ) * μ)
    rw [← e] at h2
    linarith
  · have hc := not_le.1 hc
    have h2 : 1 - θ ≤ ‖1 - (θ : ℂ) * μ‖ := by
      have h3 := norm_sub_norm_le (1 : ℂ) ((θ : ℂ) * μ)
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h3
      nlinarith [norm_nonneg μ]
    linarith

/-- `(1 - B')⁻¹ B = F diag((1 - ν)⁻¹ μ) F^*` for `B`, `B'` with the Fourier eigenvectors and
eigenvalues `μ`, `ν`, `1 - ν_l ≠ 0`. -/
private lemma KT_K_form (D : ℕ) (hD : D ≠ 0) (B B' : Matrix (Fin D) (Fin D) ℂ)
    (μ ν : Fin D → ℂ) (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l)
    (hB' : ∀ l, B' *ᵥ fourierVec D l = ν l • fourierVec D l) (hν : ∀ l, 1 - ν l ≠ 0) :
    (1 - B')⁻¹ * B = KT_F D * diagonal (fun l => (1 - ν l)⁻¹ * μ l) * (KT_F D)ᴴ := by
  obtain ⟨-, hinv, -⟩ := KT_circ_inv D hD B' ν hB' hν
  rw [hinv, KT_circ D hD B μ hB]
  have e : KT_F D * diagonal (fun l => (1 - ν l)⁻¹) * (KT_F D)ᴴ *
      (KT_F D * diagonal μ * (KT_F D)ᴴ) =
      KT_F D * (diagonal (fun l => (1 - ν l)⁻¹) * ((KT_F D)ᴴ * KT_F D) * diagonal μ) *
        (KT_F D)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e, KT_F_unitary D hD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

/-- `K = F diag(κ) F^*` has the Fourier vectors as eigenvectors with eigenvalues `κ`. -/
private lemma KT_eig_of_form (D : ℕ) (hD : D ≠ 0) (κ : Fin D → ℂ) (l : Fin D) :
    (KT_F D * diagonal κ * (KT_F D)ᴴ) *ᵥ fourierVec D l = κ l • fourierVec D l := by
  have h1 : (KT_F D * diagonal κ * (KT_F D)ᴴ) * KT_F D = KT_F D * diagonal κ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, KT_F_unitary D hD, Matrix.mul_one]
  ext a
  have h2 := congrFun (congrFun h1 a) l
  rw [Matrix.mul_diagonal] at h2
  have h3 : ((KT_F D * diagonal κ * (KT_F D)ᴴ) * KT_F D) a l =
      ((KT_F D * diagonal κ * (KT_F D)ᴴ) *ᵥ fourierVec D l) a := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, KT_F]
  rw [← h3, h2]
  simp only [Pi.smul_apply, smul_eq_mul, KT_F, Matrix.of_apply]
  ring

/-- The spectral facts for a matrix `B` with the Fourier eigenvectors `u_l`, eigenvalues `μ_l`
with `|μ_l| ≤ 1` and `det(1 - B) ≠ 0`, and the profile `P_θ`, `θ ∈ [0, 1]`:
`1 - B P_θ` is invertible, `‖(1 - B P_θ)⁻¹‖ ≤ 2 ‖(1 - B)⁻¹‖`, and
`(1 - B P_θ)⁻¹ B = F diag(κ) F^*` with `|κ_l| ≤ 2 |(1 - μ_l)⁻¹ μ_l|`. -/
private lemma KT_spec (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) (hμ : ∀ l, ‖μ l‖ ≤ 1)
    (hdet : (1 - B).det ≠ 0) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (1 - B * PTheta D θ).det ≠ 0 ∧
      opNorm ((1 - B * PTheta D θ)⁻¹) ≤ 2 * opNorm ((1 - B)⁻¹) ∧
      (1 - B)⁻¹ * B = KT_F D * diagonal (fun l => (1 - μ l)⁻¹ * μ l) * (KT_F D)ᴴ ∧
      ∃ κ : Fin D → ℂ, (1 - B * PTheta D θ)⁻¹ * B = KT_F D * diagonal κ * (KT_F D)ᴴ ∧
        ∀ l, ‖κ l‖ ≤ 2 * ‖(1 - μ l)⁻¹ * μ l‖ := by
  have hB1 : 1 - B = KT_F D * diagonal (fun l => 1 - μ l) * (KT_F D)ᴴ := by
    have hc := KT_circ D hD B μ hB
    have : diagonal (fun l => 1 - μ l) = 1 - diagonal μ := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, KT_F_unitary' D hD, ← hc]
  have hne : ∀ l, 1 - μ l ≠ 0 := by
    intro l hl
    apply hdet
    rw [hB1, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ l) hl]
    simp
  set ν : Fin D → ℂ := fun l => (if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ)) * μ l with hν
  have hBP : ∀ l, (B * PTheta D θ) *ᵥ fourierVec D l = ν l • fourierVec D l := by
    intro l
    rw [← Matrix.mulVec_mulVec, KT_P_eig D hD, Matrix.mulVec_smul, hB l, smul_smul]
  have hle : ∀ l, ‖1 - μ l‖ ≤ 2 * ‖1 - ν l‖ := by
    intro l
    by_cases hl : (l : ℕ) = 0
    · simp only [hν, hl, ↓reduceIte, one_mul]
      have := norm_nonneg (1 - μ l)
      linarith
    · simp only [hν, hl, ↓reduceIte]
      exact KT_scalar (μ l) (hμ l) θ h0 h1
  have hpos : ∀ l, 0 < ‖1 - μ l‖ := fun l => norm_pos_iff.2 (hne l)
  have hne' : ∀ l, 1 - ν l ≠ 0 := by
    intro l hl
    have := hle l
    rw [hl, norm_zero, mul_zero] at this
    exact absurd this (not_le.2 (hpos l))
  obtain ⟨hdet', -, hn'⟩ := KT_circ_inv D hD (B * PTheta D θ) ν hBP hne'
  obtain ⟨-, -, hn⟩ := KT_circ_inv D hD B μ hB hne
  have hpt : ∀ l, ‖(1 - ν l)⁻¹‖ ≤ 2 * ‖(1 - μ l)⁻¹‖ := by
    intro l
    rw [norm_inv, norm_inv]
    have hp2 : 0 < 2 * ‖1 - ν l‖ := by
      have := hpos l
      have := hle l
      linarith
    calc ‖1 - ν l‖⁻¹ = 2 * (2 * ‖1 - ν l‖)⁻¹ := by field_simp
      _ ≤ 2 * ‖1 - μ l‖⁻¹ := by
        have : (2 * ‖1 - ν l‖)⁻¹ ≤ ‖1 - μ l‖⁻¹ := inv_anti₀ (hpos l) (hle l)
        linarith
  refine ⟨hdet', ?_, KT_K_form D hD B B μ μ hB hB hne, fun l => (1 - ν l)⁻¹ * μ l,
    KT_K_form D hD B (B * PTheta D θ) μ ν hB hBP hne', fun l => ?_⟩
  · rw [hn', hn]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
    exact (hpt l).trans (by
      have := norm_le_pi_norm (fun l => (1 - μ l)⁻¹) l
      linarith)
  · rw [norm_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hpt l) (norm_nonneg _)).trans (by linarith)

end KT_Fourier

/-! ### The eigenvalues of `M̂(z₁, z₂)` lie in the closed unit disc -/

section KT_Bound

variable {ι : Type*} [Fintype ι]

/-- `∑ᵢⱼ |Aᵢⱼ|²`. -/
private def KT_S (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma KT_S_conj (A : Matrix ι ι ℂ) : KT_S Aᴴ = KT_S A := by
  unfold KT_S
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- Cauchy–Schwarz for the trace pairing: `|tr(XY)|² ≤ (∑|X_{ij}|²)(∑|Y_{ij}|²)`. -/
private lemma KT_tr_mul_le (X Y : Matrix ι ι ℂ) :
    ‖(X * Y).trace‖ ≤ Real.sqrt (KT_S X) * Real.sqrt (KT_S Y) := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ p : ι × ι, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    rw [Matrix.trace]
    calc ‖∑ i, (X * Y).diag i‖ ≤ ∑ i, ‖(X * Y).diag i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Matrix.diag, Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
      _ = _ := by rw [Fintype.sum_prod_type]
  refine h1.trans ?_
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖Y p.2 p.1‖)
  have e1 : ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2 = KT_S X := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = KT_S Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  exact h2

private lemma KT_trace_mul_conj (Z : Matrix ι ι ℂ) : (Z * Zᴴ).trace = (KT_S Z : ℂ) := by
  unfold KT_S
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `D ⟨X⟩ = N⁻¹ tr X` on `Idx D N`. -/
private lemma KT_D_ntr (D N : ℕ) (hD : D ≠ 0) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    (D : ℂ) * ntr X = (N : ℂ)⁻¹ * X.trace := by
  unfold ntr
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  by_cases hN : (N : ℂ) = 0
  · simp [hN]
  · field_simp

/-- For `Im z > 0`, `z₁ ∈ {z, z̄}`: `∑ |M(z₁)_{pq}|² ≤ D N`, by (A.3) [equation_z_im_m]. -/
private lemma KT_S_MExt (D N : ℕ) (hD : D ≠ 0) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) :
    KT_S (MExt (lam D N A) z₁) ≤ D * N := by
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hm : mExt (lam D N A) z = mSol (lam D N A) z := by simp only [mExt, hz, ↓reduceIte]
  have hM : MExt (lam D N A) z = MSol (lam D N A) z := by rw [MExt, MSol, hm]
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  have h1 := (equation_z_im_m (lam D N A) hΛ z hz).1
  set y := (mSol (lam D N A) z).im
  have hS : KT_S (MExt (lam D N A) z) ≤ D * N := by
    have hcard : ((D * N : ℕ) : ℂ) ≠ 0 := by
      have := (Fintype.card_pos (α := Idx D N)).ne'
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      exact_mod_cast this
    have e : (KT_S (MSol (lam D N A) z) : ℂ) =
        ((D * N : ℕ) : ℂ) * ((y / (y + z.im) : ℝ) : ℂ) := by
      rw [← KT_trace_mul_conj, ← h1]
      unfold ntr
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    have e' : KT_S (MSol (lam D N A) z) = ((D * N : ℕ) : ℝ) * (y / (y + z.im)) := by
      exact_mod_cast e
    rw [hM, e']
    have hd : y / (y + z.im) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have : (0 : ℝ) ≤ ((D * N : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at this ⊢
    nlinarith
  rcases h₁ with rfl | rfl
  · exact hS
  · rw [(mExt_conj (lam D N A) hΛ z hz.ne').2, KT_S_conj]
    exact hS

/-- Every eigenvalue `λ̂_l` of `M̂(z₁, z₂)`, `z₁, z₂ ∈ {z, z̄}`, `Im z > 0`, lies in the closed
unit disc: `λ̂_l = ⟨M(z₁) V^* M(z₂) V⟩` for the diagonal unitary `V = diag(e^{2πi l a / D})`,
and Cauchy–Schwarz with (A.3) [equation_z_im_m] bounds it by `√(⟨M₁M₁^*⟩⟨M₂^*M₂⟩) ≤ 1`. -/
private lemma KT_circEig_le (D N : ℕ) (hD : D ≠ 0) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (l : Fin D) :
    ‖circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤ 1 := by
  have : NeZero D := ⟨hD⟩
  set M₁ := MExt (lam D N A) z₁
  set M₂ := MExt (lam D N A) z₂
  set u := fourierVec D l with hu
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hun : ∀ a : Fin D, ‖u a‖ = (Real.sqrt D)⁻¹ := by
    intro a
    rw [hu, KT_fourierVec_eq, norm_mul, KT_norm_zeta_pow D hD, mul_one, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hV₁ : (Matrix.diagonal fun p : Idx D N => star (u p.1)) =
      ∑ a, star (u a) • Ea D N a := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [hpq]
  have hV₂ : (Matrix.diagonal fun p : Idx D N => u p.1) = ∑ b, u b • Ea D N b := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [hpq]
  have hc : circEig (Mhat (lam D N A) z₁ z₂) l =
      (N : ℂ)⁻¹ * (M₁ * (Matrix.diagonal fun p : Idx D N => star (u p.1)) * M₂ *
        (Matrix.diagonal fun p : Idx D N => u p.1)).trace := by
    unfold circEig Mhat
    simp only [KT_D_ntr D N hD]
    rw [hV₁, hV₂]
    simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hu]
    ring
  have hS₁ := KT_S_MExt D N hD hN A z hz z₁ h₁
  have hS₂ := KT_S_MExt D N hD hN A z hz z₂ h₂
  set V₁ : Matrix (Idx D N) (Idx D N) ℂ := Matrix.diagonal fun p : Idx D N => star (u p.1)
  set V₂ : Matrix (Idx D N) (Idx D N) ℂ := Matrix.diagonal fun p : Idx D N => u p.1
  have hq : ((Real.sqrt D)⁻¹) ^ 2 = (D : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hDpos.le]
  have hS : KT_S (V₁ * M₂ * V₂) = ((D : ℝ)⁻¹) ^ 2 * KT_S M₂ := by
    unfold KT_S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [V₁, V₂, Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_star, hun]
    rw [← hq]
    ring
  have htr := KT_tr_mul_le M₁ (V₁ * M₂ * V₂)
  have e : M₁ * V₁ * M₂ * V₂ = M₁ * (V₁ * M₂ * V₂) := by simp only [Matrix.mul_assoc]
  have hsq : Real.sqrt (KT_S (V₁ * M₂ * V₂)) = (D : ℝ)⁻¹ * Real.sqrt (KT_S M₂) := by
    rw [hS, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have h1 : Real.sqrt (KT_S M₁) ≤ Real.sqrt (D * N) := Real.sqrt_le_sqrt hS₁
  have h2 : Real.sqrt (KT_S M₂) ≤ Real.sqrt (D * N) := Real.sqrt_le_sqrt hS₂
  have hDN : Real.sqrt (D * N) * Real.sqrt (D * N) = D * N :=
    Real.mul_self_sqrt (by positivity)
  rw [hc, e, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hsq] at htr
  calc (N : ℝ)⁻¹ * ‖(M₁ * (V₁ * M₂ * V₂)).trace‖
      ≤ (N : ℝ)⁻¹ * (Real.sqrt (KT_S M₁) * ((D : ℝ)⁻¹ * Real.sqrt (KT_S M₂))) := by
        gcongr
    _ ≤ (N : ℝ)⁻¹ * (Real.sqrt (D * N) * ((D : ℝ)⁻¹ * Real.sqrt (D * N))) := by
        gcongr
    _ = 1 := by
        have : (N : ℝ)⁻¹ * (Real.sqrt (D * N) * ((D : ℝ)⁻¹ * Real.sqrt (D * N))) =
            (N : ℝ)⁻¹ * (D : ℝ)⁻¹ * (Real.sqrt (D * N) * Real.sqrt (D * N)) := by ring
        rw [this, hDN]
        field_simp

end KT_Bound

/-- The class-parameter bounds behind (A.8) [1-M] – (A.10) at every `θ ∈ [0, 1]`:
`1 - M̂ P_θ` is invertible and `‖(1 - M̂ P_θ)⁻¹‖ ≤ 2 ‖(1 - M̂)⁻¹‖`, for `z₁, z₂ ∈ {z, z̄}`. -/
theorem oneSubMhatP_inv_le (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) →
      (z₂ = z ∨ z₂ = star z) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ ≤
          2 * opNorm (1 - Mhat (lam D N A) z₁ z₂)⁻¹ := by
  obtain ⟨_, _, Nf, hflat⟩ := flat_M D hD δA τ hδA hτ
  refine ⟨max Nf 1, fun N hN A hA z hzn hz z₁ z₂ h₁ h₂ θ h0 h1 => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNf : Nf ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hdet, -⟩ := hflat N hNf A hA z hzn hz z₁ z₂ h₁ h₂
  have hD0 : D ≠ 0 := by omega
  have him : ∀ z' : ℂ, (z' = z ∨ z' = star z) → z'.im ≠ 0 := by
    rintro z' (rfl | rfl)
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  have hev := Mhat_eigvec D hD N A z₁ z₂ (him z₁ h₁) (him z₂ h₂)
  obtain ⟨hd, hn, -⟩ := KT_spec D hD0 (Mhat (lam D N A) z₁ z₂)
    (fun l => circEig (Mhat (lam D N A) z₁ z₂) l) hev
    (fun l => KT_circEig_le D N hD0 hN1 A z hz z₁ z₂ h₁ h₂ l) hdet θ h0 h1
  exact ⟨hd, hn⟩

/-- (A.11) [flat_M] for `K_θ`, every `θ ∈ [0, 1]`: `1 - M̂ P_θ` is invertible and
`‖A‖²_HS |(K_θ)_{ab} - (K_θ)_{a'b'}| ≤ C N` for `z₁, z₂ ∈ {z, z̄}`. -/
theorem flat_KTheta (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        ∀ a b a' b' : Fin D,
          hsNorm A ^ 2 * ‖KTheta (lam D N A) θ z₁ z₂ a b - KTheta (lam D N A) θ z₁ z₂ a' b'‖ ≤
            C * N := by
  obtain ⟨Cf, hCf, Nf, hflat⟩ := flat_M D hD δA τ hδA hτ
  have hD0 : D ≠ 0 := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD0
  refine ⟨4 * D * Cf, by positivity, max Nf 1, fun N hN A hA z hzn hz z₁ z₂ h₁ h₂ θ h0 h1 => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNf : Nf ≤ N := (le_max_left _ _).trans hN
  have : NeZero D := ⟨hD0⟩
  obtain ⟨hdet, hK⟩ := hflat N hNf A hA z hzn hz z₁ z₂ h₁ h₂
  have him : ∀ z' : ℂ, (z' = z ∨ z' = star z) → z'.im ≠ 0 := by
    rintro z' (rfl | rfl)
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  have hev := Mhat_eigvec D hD N A z₁ z₂ (him z₁ h₁) (him z₂ h₂)
  obtain ⟨hd, -, hK1, κ, hκ, hκb⟩ := KT_spec D hD0 (Mhat (lam D N A) z₁ z₂)
    (fun l => circEig (Mhat (lam D N A) z₁ z₂) l) hev
    (fun l => KT_circEig_le D N hD0 hN1 A z hz z₁ z₂ h₁ h₂ l) hdet θ h0 h1
  refine ⟨hd, fun a b a' b' => ?_⟩
  have hKT : KTheta (lam D N A) θ z₁ z₂ = KT_F D * diagonal κ * (KT_F D)ᴴ := hκ
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnn : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  rcases hnn.eq_or_lt with hs0 | hs
  · rw [← hs0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  · have hs2 : 0 < hsNorm A ^ 2 := by positivity
    -- the eigenvalues of `K = K_1` are controlled by the flatness of `K`
    have hK1' : Kmat (lam D N A) z₁ z₂ = KT_F D * diagonal
        (fun l => (1 - circEig (Mhat (lam D N A) z₁ z₂) l)⁻¹ *
          circEig (Mhat (lam D N A) z₁ z₂) l) * (KT_F D)ᴴ := hK1
    have hrow := fun l => KT_row D (Kmat (lam D N A) z₁ z₂) l _
      (by rw [hK1']; exact KT_eig_of_form D hD0 _ l)
    have hflat' : ∀ b : Fin D, ‖Kmat (lam D N A) z₁ z₂ 0 b - Kmat (lam D N A) z₁ z₂ 0 0‖ ≤
        Cf * N / hsNorm A ^ 2 := fun b => by
      rw [le_div_iff₀ hs2, mul_comm]
      exact hK 0 b 0 0
    have hbd : ∀ l : Fin D, (l : ℕ) ≠ 0 →
        ‖(1 - circEig (Mhat (lam D N A) z₁ z₂) l)⁻¹ * circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤
          D * (Cf * N / hsNorm A ^ 2) := by
      intro l hl
      rw [hrow l]
      have e : ∑ b : Fin D, Kmat (lam D N A) z₁ z₂ 0 b * KT_zeta D ^ ((l : ℕ) * (b : ℕ)) =
          ∑ b : Fin D, (Kmat (lam D N A) z₁ z₂ 0 b - Kmat (lam D N A) z₁ z₂ 0 0) *
            KT_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, KT_sum_zeta D hD0 l hl,
          mul_zero, sub_zero]
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b : Fin D, ‖(Kmat (lam D N A) z₁ z₂ 0 b - Kmat (lam D N A) z₁ z₂ 0 0) *
              KT_zeta D ^ ((l : ℕ) * (b : ℕ))‖
          ≤ ∑ _b : Fin D, Cf * N / hsNorm A ^ 2 := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [norm_mul, KT_norm_zeta_pow D hD0, mul_one]
            exact hflat' b
        _ = D * (Cf * N / hsNorm A ^ 2) := by simp
    have hKb : 0 ≤ 2 * (2 * (D * (Cf * N / hsNorm A ^ 2))) := by positivity
    have hent := KT_entry_diff D κ (2 * (D * (Cf * N / hsNorm A ^ 2))) (by positivity)
      (fun l hl => (hκb l).trans (by linarith [hbd l hl])) a b a' b'
    rw [hKT]
    calc hsNorm A ^ 2 * ‖(KT_F D * diagonal κ * (KT_F D)ᴴ) a b -
          (KT_F D * diagonal κ * (KT_F D)ᴴ) a' b'‖
        ≤ hsNorm A ^ 2 * (2 * (2 * (D * (Cf * N / hsNorm A ^ 2)))) :=
          mul_le_mul_of_nonneg_left hent hs2.le
      _ = 4 * D * Cf * N := by field_simp; ring

end RBMTransitionEdge

end
