module

public import RBMTransitionEdge.LocalLaw.CumulantClass
public import RBMTransitionEdge.Tools.Resolvent
public import RBMTransitionEdge.Tools.ResolventIdentities

@[expose] public section

/-!
# Smoothness through the Hermitian part

The Hermitian part `(h + hᴴ)/2` of an array, the smoothness of resolvent entries composed with it,
the product and conjugation rules of the Wirtinger derivatives, and the cumulant expansion of
Lemma 2.11 [lem:complex_cumu] for `Φ ∘ symArr` with the derivative bounds required only at
Hermitian arrays.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The Hermitian part `(h + hᴴ)/2` of an array: every array is mapped to a Hermitian matrix,
and a Hermitian array to itself. -/
def symArr {D N : ℕ} (h : Idx D N → Idx D N → ℂ) : Idx D N → Idx D N → ℂ :=
  fun k l => (h k l + starRingEnd ℂ (h l k)) / 2

/-- `(h + hᴴ)/2` is Hermitian for every array `h`. -/
theorem symArr_isHermitian {D N : ℕ} (h : Idx D N → Idx D N → ℂ) :
    (Matrix.of (symArr h)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun k l => ?_
  simp only [Matrix.of_apply, symArr, Complex.star_def, map_div₀, map_add, Complex.conj_conj]
  have : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
  rw [this, add_comm]

/-- A Hermitian array is its own Hermitian part. -/
theorem symArr_of_isHermitian {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) : symArr h = h := by
  funext k l
  have h1 : starRingEnd ℂ (h l k) = h k l := by
    simpa [Complex.star_def] using hh.apply k l
  simp only [symArr, h1]
  ring

/-- The Hermitian part commutes with the one-entry substitution of Lemma 2.11
[lem:complex_cumu]. -/
theorem symArr_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w : ℂ) :
    symArr (setEntry h i j w) = setEntry (symArr h) i j w := by
  funext k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨rfl, rfl⟩ := hkl
      simp only [symArr, setEntry, and_self, ite_true, Complex.conj_ofReal]
      ring
    · have hlk : ¬ (l = i ∧ k = i) := fun h' => hkl ⟨h'.2, h'.1⟩
      simp only [symArr, setEntry, hkl, hlk, ite_true, ite_false]
  · by_cases h1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [symArr, setEntry, hd, Ne.symm hd, and_self, ite_true, ite_false, and_false,
        Complex.conj_conj]
      ring
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp only [symArr, setEntry, hd, Ne.symm hd, and_self, ite_true, ite_false, and_false]
        ring
      · have e1 : ¬ (l = i ∧ k = j) := fun h' => h2 ⟨h'.2, h'.1⟩
        have e2 : ¬ (l = j ∧ k = i) := fun h' => h1 ⟨h'.2, h'.1⟩
        simp only [symArr, setEntry, hd, h1, h2, e1, e2, ite_false]

/-- Substituting the entry `(i, j)` twice keeps the second value. -/
theorem setEntry_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w w' : ℂ) :
    setEntry (setEntry h i j w) i j w' = setEntry h i j w' := by
  funext k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i <;> simp [setEntry, hkl]
  · by_cases h1 : k = i ∧ l = j
    · simp [setEntry, hd, h1]
    · by_cases h2 : k = j ∧ l = i
      · simp [setEntry, hd, h2]
      · simp [setEntry, hd, h1, h2]

/-- The determinant of a matrix whose entries are of class `C^n` is of class `C^n`. -/
private lemma RS_contDiff_det {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    [DecidableEq ι] (M : E → Matrix ι ι ℂ) (n : WithTop ℕ∞)
    (hM : ∀ a b, ContDiff ℝ n (fun x => M x a b)) : ContDiff ℝ n (fun x => (M x).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)

/-- Every entry of `(h + hᴴ)/2 + Λ - z` is of class `C^n` in the array `h`. -/
private lemma RS_contDiff_entry {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (a b : Idx D N) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ =>
      (Matrix.of (symArr h) + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) a b) := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, symArr, Matrix.smul_apply]
  have h1 : ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => h a b) :=
    contDiff_apply_apply ℝ a b
  have h2 : ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h b a)) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ b a)
  exact (((h1.add h2).div_const 2).add contDiff_const).sub contDiff_const

/-- For Hermitian `Λ` and `Im z ≠ 0`, every entry of the resolvent (2.12) [def_resolv] of the
Hermitian part, `h ↦ ((h + hᴴ)/2 + Λ - z)⁻¹_{kl}`, is of class `C^n` on all arrays, for every
`n`. -/
theorem contDiff_res_symArr {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (k l : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h) + Λ) z k l) := by
  set T : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ :=
    fun h => Matrix.of (symArr h) + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) with hT
  have hdet : ContDiff ℝ n (fun h => (T h).det) :=
    RS_contDiff_det T n fun a b => RS_contDiff_entry Λ z a b n
  have hne : ∀ h, (T h).det ≠ 0 := by
    intro h h0
    have h1 := (res_mul_sub_of_im_ne (Matrix.of (symArr h) + Λ)
      ((symArr_isHermitian h).add hΛ) z hz).1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    have h0' : Matrix.det (Matrix.of (symArr h) + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 0 :=
      h0
    rw [h0', zero_mul] at h2
    exact zero_ne_one h2
  have hadj : ContDiff ℝ n (fun h => (T h).adjugate k l) := by
    simp only [Matrix.adjugate_apply]
    refine RS_contDiff_det _ n fun a b => ?_
    by_cases ha : a = l
    · simp only [Matrix.updateRow_apply, ha, ite_true]
      exact contDiff_const
    · simp only [Matrix.updateRow_apply, ha, ite_false]
      exact RS_contDiff_entry Λ z a b n
  have e : ∀ h, res (Matrix.of (symArr h) + Λ) z k l = ((T h).det)⁻¹ * (T h).adjugate k l := by
    intro h
    rw [res, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  exact (hdet.inv hne).mul hadj

/-- The product rule for the Wirtinger derivatives `∂_w`, `∂_{w̄}` of Lemma 2.11
[lem:complex_cumu] at a point where both factors are real-differentiable. -/
theorem dW_mul {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    dW (fun x => f x * g x) w = dW f w * g w + f w * dW g w ∧
      dWbar (fun x => f x * g x) w = dWbar f w * g w + f w * dWbar g w := by
  have e : fderiv ℝ (fun x => f x * g x) w = f w • fderiv ℝ g w + g w • fderiv ℝ f w :=
    fderiv_mul hf hg
  constructor
  · simp only [dW, e, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  · simp only [dWbar, e, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul]
    ring

/-- The Wirtinger derivatives of a complex conjugate: `∂_w f̄ = conj(∂_{w̄} f)` and
`∂_{w̄} f̄ = conj(∂_w f)` at a point where `f` is real-differentiable. -/
theorem dW_conj {f : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) :
    dW (fun x => starRingEnd ℂ (f x)) w = starRingEnd ℂ (dWbar f w) ∧
      dWbar (fun x => starRingEnd ℂ (f x)) w = starRingEnd ℂ (dW f w) := by
  have _ := hf
  have e : ∀ v : ℂ, fderiv ℝ (fun x => starRingEnd ℂ (f x)) w v =
      starRingEnd ℂ (fderiv ℝ f w v) := by
    intro v
    have := Complex.conjCLE.comp_fderiv (f := f) (x := w)
    exact congrArg (fun L => L v) this
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
  constructor
  · simp only [dW, dWbar, e, map_div₀, map_add, map_mul, Complex.conj_I, h2]
    ring
  · simp only [dW, dWbar, e, map_div₀, map_sub, map_mul, Complex.conj_I, h2]
    ring

/-- Lemma 2.11 [lem:complex_cumu], (2.26) [5.16], for one entry of a member of `LLClass`, applied
to `Φ ∘ symArr`: if `h ↦ Φ((h + hᴴ)/2)` is of class `C^{l+1}` and the Wirtinger derivatives of
`w ↦ Φ(setEntry h i j w)` are bounded by `A` (order `l + 1`, `|w| ≤ M`) and `B` (orders
`≤ l + 1`) for Hermitian `h` only, then the expansion of `E Φ(h) h̄_{ij}` holds with the remainder
`K (E|h_{ij}|^{l+2} A + E[|h_{ij}|^{l+2} 1(|h_{ij}| > M)] B)`, `K` depending on `l` only. -/
theorem llClass_expansion_sym (l : ℕ) :
    ∃ K : ℝ, ∀ (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → ∀ (i j : Idx D N) (Φ : (Idx D N → Idx D N → ℂ) → ℂ) (M A B : ℝ),
      ContDiff ℝ (l + 1 : ℕ) (fun h => Φ (symArr h)) → 0 < M →
      (∀ p q : ℕ, p + q = l + 1 → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        ∀ w : ℂ, ‖w‖ ≤ M → ‖wirt p q (fun w' => Φ (setEntry h i j w')) w‖ ≤ A) →
      (∀ p q : ℕ, p + q ≤ l + 1 → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        ∀ w : ℂ, ‖wirt p q (fun w' => Φ (setEntry h i j w')) w‖ ≤ B) →
      ‖(∫ h, Φ h * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
              ∫ h, wirt p q (fun w' => Φ (setEntry h i j w')) (h i j) ∂μ‖ ≤
        K * ((∫ h, ‖h i j‖ ^ (l + 2) ∂μ) * A +
          (∫ h, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ∂μ) * B) := by
  obtain ⟨K, hK⟩ := llClass_cumulant_expansion l
  refine ⟨K, ?_⟩
  intro D N C θ μ hμ i j Φ M A B hF hM hA hB
  -- the slice of `Φ ∘ symArr` through `h` is the slice of `Φ` through the Hermitian `symArr h`
  have hslice : ∀ h : Idx D N → Idx D N → ℂ,
      (fun w' => Φ (symArr (setEntry h i j w'))) = fun w' => Φ (setEntry (symArr h) i j w') := by
    intro h
    funext w'
    rw [symArr_setEntry]
  have hA' : ∀ p q : ℕ, p + q = l + 1 → ∀ (h : Idx D N → Idx D N → ℂ) (w : ℂ), ‖w‖ ≤ M →
      ‖wirt p q (fun w' => (fun h => Φ (symArr h)) (setEntry h i j w')) w‖ ≤ A := by
    intro p q hpq h w hw
    change ‖wirt p q (fun w' => Φ (symArr (setEntry h i j w'))) w‖ ≤ A
    rw [hslice h]
    exact hA p q hpq (symArr h) (symArr_isHermitian h) w hw
  have hB' : ∀ p q : ℕ, p + q ≤ l + 1 → ∀ (h : Idx D N → Idx D N → ℂ) (w : ℂ),
      ‖wirt p q (fun w' => (fun h => Φ (symArr h)) (setEntry h i j w')) w‖ ≤ B := by
    intro p q hpq h w
    change ‖wirt p q (fun w' => Φ (symArr (setEntry h i j w'))) w‖ ≤ B
    rw [hslice h]
    exact hB p q hpq (symArr h) (symArr_isHermitian h) w
  have key := hK D N C θ μ hμ i j (fun h => Φ (symArr h)) M A B hF hM hA' hB'
  -- almost surely `symArr h = h`, so the two sides of the expansion have the same integrals
  have e1 : (∫ h, Φ (symArr h) * starRingEnd ℂ (h i j) ∂μ) =
      ∫ h, Φ h * starRingEnd ℂ (h i j) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    simp only [symArr_of_isHermitian h hh]
  have e2 : ∀ p q : ℕ, (∫ h, wirt p q (fun w' => Φ (symArr (setEntry h i j w'))) (h i j) ∂μ) =
      ∫ h, wirt p q (fun w' => Φ (setEntry h i j w')) (h i j) ∂μ := by
    intro p q
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    simp only [hslice h, symArr_of_isHermitian h hh]
  simp only [e2] at key
  rw [e1] at key
  exact key

end RBMTransitionEdge

end
