module

public import RBMTransitionEdge.Tools.Resolvent

@[expose] public section

/-!
# Resolvent polynomials

Polynomials in the forms `x^* (h + Λ - ξ)⁻¹ y` of resolvents (2.12) [def_resolv], in which every
factor carries its own deformation `Λ` and spectral parameter `ξ`: their values at an array, their
products and their conjugates. They are the functions to which the one-entry expansion of
Lemma 2.11 [lem:complex_cumu] is applied in the fluctuation bounds of Lemma 2.9 [lem_loc].
-/

open Matrix

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A factor `x^* (h + Λ - ξ)⁻¹ y` of a resolvent monomial, listed as `(x, y, Λ, ξ)`. -/
abbrev ResFactor (D N : ℕ) :=
  (Idx D N → ℂ) × (Idx D N → ℂ) × Matrix (Idx D N) (Idx D N) ℂ × ℂ

/-- A resolvent monomial `Π_k x_k^* (h + Λ_k - ξ_k)⁻¹ y_k`, listed by its factors. -/
abbrev ResMono (D N : ℕ) := List (ResFactor D N)

/-- A resolvent polynomial `Σ_t c_t Π_k x_{tk}^* (h + Λ_{tk} - ξ_{tk})⁻¹ y_{tk}`, listed by its
terms. -/
abbrev ResPoly (D N : ℕ) := List (ℂ × ResMono D N)

/-- The value `x^* (h + Λ - ξ)⁻¹ y` of a factor at the array `h`. -/
def resFactorEval {D N : ℕ} (f : ResFactor D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  star f.1 ⬝ᵥ (res (Matrix.of h + f.2.2.1) f.2.2.2 *ᵥ f.2.1)

/-- The value of a resolvent monomial at the array `h`. -/
def resMonoEval {D N : ℕ} (m : ResMono D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (m.map fun f => resFactorEval f h).prod

/-- The value of a resolvent polynomial at the array `h`. -/
def resPolyEval {D N : ℕ} (P : ResPoly D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (P.map fun t => t.1 * resMonoEval t.2 h).sum

/-- The product of two resolvent polynomials, term by term. -/
def resPolyMul {D N : ℕ} (P Q : ResPoly D N) : ResPoly D N :=
  P.flatMap fun s => Q.map fun t => (s.1 * t.1, s.2 ++ t.2)

/-- The conjugate resolvent polynomial: `c ↦ c̄` and `x^* (h + Λ - ξ)⁻¹ y ↦ y^* (h + Λ - ξ̄)⁻¹ x`. -/
def resPolyStar {D N : ℕ} (P : ResPoly D N) : ResPoly D N :=
  P.map fun t => (starRingEnd ℂ t.1,
    t.2.map fun f => (f.2.1, f.1, f.2.2.1, starRingEnd ℂ f.2.2.2))

/-- A factor with a Hermitian deformation at a Hermitian array: the conjugate of its value is the
value of the conjugate factor `y^* (h + Λ - ξ̄)⁻¹ x`. -/
private lemma ResPoly_factor_star {D N : ℕ} (f : ResFactor D N) (hf : f.2.2.1.IsHermitian)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    starRingEnd ℂ (resFactorEval f h)
      = resFactorEval (f.2.1, f.1, f.2.2.1, starRingEnd ℂ f.2.2.2) h := by
  obtain ⟨x, y, L, ξ⟩ := f
  have hX : (Matrix.of h + L).IsHermitian := hh.add hf
  have hG : (res (Matrix.of h + L) ξ)ᴴ = res (Matrix.of h + L) (starRingEnd ℂ ξ) := by
    unfold res
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hX.eq]
    rfl
  have h1 : starRingEnd ℂ (star x ⬝ᵥ (res (Matrix.of h + L) ξ *ᵥ y))
      = star y ⬝ᵥ ((res (Matrix.of h + L) ξ)ᴴ *ᵥ x) := by
    rw [← Complex.star_def, Matrix.star_dotProduct, Matrix.star_mulVec, star_star]
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
  simp only [resFactorEval]
  rw [h1, hG]

/-- The conjugate of a monomial at a Hermitian array. -/
private lemma ResPoly_mono_star {D N : ℕ} (m : ResMono D N)
    (hm : ∀ f ∈ m, f.2.2.1.IsHermitian) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    resMonoEval (m.map fun f => (f.2.1, f.1, f.2.2.1, starRingEnd ℂ f.2.2.2)) h
      = starRingEnd ℂ (resMonoEval m h) := by
  induction m with
  | nil => simp [resMonoEval]
  | cons f m ih =>
    have ih' := ih fun g hg => hm g (List.mem_cons_of_mem _ hg)
    simp only [resMonoEval, List.map_cons, List.prod_cons, map_mul] at ih' ⊢
    rw [ih', ← ResPoly_factor_star f (hm f List.mem_cons_self) h hh]

/-- The value of a concatenation of resolvent polynomials is the sum of the values. -/
theorem resPolyEval_append {D N : ℕ} (P Q : ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (P ++ Q) h = resPolyEval P h + resPolyEval Q h := by
  simp [resPolyEval, List.map_append, List.sum_append]

/-- The value of a product of resolvent polynomials is the product of the values. -/
theorem resPolyEval_mul {D N : ℕ} (P Q : ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (resPolyMul P Q) h = resPolyEval P h * resPolyEval Q h := by
  induction P with
  | nil => simp [resPolyMul, resPolyEval]
  | cons s P ih =>
    have hrow : ∀ R : ResPoly D N,
        resPolyEval (R.map fun t => (s.1 * t.1, s.2 ++ t.2)) h
          = s.1 * resMonoEval s.2 h * resPolyEval R h := by
      intro R
      induction R with
      | nil => simp [resPolyEval]
      | cons t R ihR =>
        simp only [List.map_cons, resPolyEval, List.sum_cons, resMonoEval, List.map_append,
          List.prod_append] at ihR ⊢
        rw [ihR]
        ring
    have hsplit : resPolyMul (s :: P) Q
        = (Q.map fun t => (s.1 * t.1, s.2 ++ t.2)) ++ resPolyMul P Q := by
      simp [resPolyMul]
    rw [hsplit, resPolyEval_append, ih, hrow]
    simp only [resPolyEval, List.map_cons, List.sum_cons]
    ring

/-- For a Hermitian array `h` and Hermitian deformations `Λ` in every factor, the conjugate
polynomial takes the conjugate value, since `((h + Λ - ξ)⁻¹)ᴴ = (h + Λ - ξ̄)⁻¹`. -/
theorem resPolyEval_star {D N : ℕ} (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    resPolyEval (resPolyStar P) h = starRingEnd ℂ (resPolyEval P h) := by
  induction P with
  | nil => simp [resPolyEval, resPolyStar]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    have hm := ResPoly_mono_star t.2 (hP t List.mem_cons_self) h hh
    simp only [resPolyEval, resPolyStar, List.map_cons, List.sum_cons, map_add, map_mul] at ih' hm ⊢
    rw [ih', hm]

end RBMTransitionEdge

end
