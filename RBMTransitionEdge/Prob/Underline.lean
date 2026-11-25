module

public import RBMTransitionEdge.Prob.GaussianIBP
public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# The identity of (2.30)

The identity `Ẽ[H̃ G H̃] = Σ_a D⟨G E_a⟩ E_a` of (2.30) [eq:HGline], entrywise, for `H̃` an
independent copy of the block matrix `H` of (1.3) [matrix_H] with general entry laws (under
`blockLaw`), as used in the underline of Definition 2.12 [def:underline].
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The map `(x, y) ↦ x + y i` as a continuous linear map. -/
private def Underline_realPairToC : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

private lemma Underline_realPairToC_apply (p : ℝ × ℝ) :
    Underline_realPairToC p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  simp [Underline_realPairToC, Complex.real_smul]

/-- `cGauss` is the image of `N(0, 1/2) ⊗ N(0, 1/2)` under `(x, y) ↦ x + y i`. -/
private lemma Underline_cGauss_eq_map : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map
      Underline_realPairToC := by
  have : (Underline_realPairToC : ℝ × ℝ → ℂ) =
      fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p; exact Underline_realPairToC_apply p
  rw [this]
  rfl

/-- `cGauss` is a Gaussian law. -/
private instance Underline_cGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  rw [Underline_cGauss_eq_map]
  infer_instance

/-! ### The real coordinates of the blocks, indexed by one finite type -/

/-- The `(x, y)` entry of a triple product as a double sum. -/
private lemma Underline_mul3_apply {ι : Type*} [Fintype ι] (P Q R : Matrix ι ι ℂ) (x y : ι) :
    (P * Q * R) x y = ∑ p, ∑ q, P x p * Q p q * R q y := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-! ### The entries of `blockH` under `blockLaw` -/

/-- The entry `(i, j)` of a block as one complex coordinate: the real diagonal coordinate if
`i = j`, the array entry otherwise. -/
private def Underline_Y {n : ℕ} (u : Coords n) (i j : Fin n) : ℂ :=
  if i = j then ((u.1 i : ℝ) : ℂ) else u.2 i j

/-- The Hermitian entry `(i, j)` of a block, before the scaling by `n^{-1/2}`. -/
private def Underline_T {n : ℕ} (u : Coords n) (i j : Fin n) : ℂ :=
  if i ≤ j then Underline_Y u i j else star (Underline_Y u j i)

/-- `wig n u` is `n^{-1/2}` times the Hermitian entries `Underline_T`. -/
private lemma Underline_wig_eq (n : ℕ) (u : Coords n) (i j : Fin n) :
    wig n u i j = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Underline_T u i j := by
  unfold wig Underline_T Underline_Y
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.le]
  · subst h
    simp
  · simp [h.ne', h.not_ge, h.not_gt, h.ne]

private lemma Underline_measurable_Y (n : ℕ) (i j : Fin n) :
    Measurable (fun u : Coords n => Underline_Y u i j) := by
  by_cases h : i = j
  · simp only [Underline_Y, h, ite_true]
    fun_prop
  · simp only [Underline_Y, h, ite_false]
    fun_prop

private instance Underline_coordLaw_prob (n : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    IsProbabilityMeasure (coordLaw n L) := by
  unfold coordLaw
  infer_instance

section Marginals

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)

/-- The marginal of `blockLaw` on the block `a` is `coordLaw`. -/
private lemma Underline_mp_coord (a : Fin D) :
    MeasurePreserving (fun w : Fin D → Coords N => w a) (blockLaw D N L) (coordLaw N L) :=
  measurePreserving_eval (fun _ : Fin D => coordLaw N L) a

/-- The marginal of a diagonal coordinate is `νd`. -/
private lemma Underline_mp_D (a : Fin D) (i : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w a).1 i) (blockLaw D N L)
      (L.νd : Measure ℝ) := by
  have h1 : MeasurePreserving (Prod.fst : Coords N → Fin N → ℝ) (coordLaw N L)
      (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)) := measurePreserving_fst
  exact (measurePreserving_eval (fun _ : Fin N => (L.νd : Measure ℝ)) i).comp
    (h1.comp (Underline_mp_coord D N L a))

/-- The marginal of an array coordinate is `νo`. -/
private lemma Underline_mp_A (a : Fin D) (i j : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w a).2 i j) (blockLaw D N L)
      (L.νo : Measure ℂ) := by
  have h2 : MeasurePreserving (Prod.snd : Coords N → Fin N → Fin N → ℂ) (coordLaw N L)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) :=
    measurePreserving_snd
  have h3 := measurePreserving_eval
    (fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) i
  have h4 := measurePreserving_eval (fun _ : Fin N => (L.νo : Measure ℂ)) j
  exact h4.comp (h3.comp (h2.comp (Underline_mp_coord D N L a)))

end Marginals

/-- Integrals are transported along a measure preserving map. -/
private lemma Underline_integral_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {π : Ω → Ω'} (hπ : MeasurePreserving π μ ν) (h : Ω' → ℂ)
    (hh : Measurable h) : ∫ ω, h (π ω) ∂μ = ∫ y, h y ∂ν := by
  have := integral_map (μ := μ) (φ := π) hπ.measurable.aemeasurable (f := h)
    (by rw [hπ.map_eq]; exact hh.aestronglyMeasurable)
  rw [hπ.map_eq] at this
  exact this.symm

/-- Independence passes to a measure preserving image. -/
private lemma Underline_indepFun_comp {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {π : Ω → Ω'}
    (hπ : MeasurePreserving π μ ν) {f : Ω' → α} {g : Ω' → β} (hf : Measurable f)
    (hg : Measurable g) (h : IndepFun f g ν) :
    IndepFun (fun ω => f (π ω)) (fun ω => g (π ω)) μ := by
  change IndepFun (f ∘ π) (g ∘ π) μ
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.comp hπ.measurable).aemeasurable
    (hg.comp hπ.measurable).aemeasurable]
  have h' := (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).1 h
  have e1 : μ.map (fun ω => (f (π ω), g (π ω))) = ν.map (fun p => (f p, g p)) := by
    rw [← hπ.map_eq, Measure.map_map (hf.prodMk hg) hπ.measurable]
    rfl
  have e2 : μ.map (f ∘ π) = ν.map f := by
    rw [← hπ.map_eq, Measure.map_map hf hπ.measurable]
  have e3 : μ.map (g ∘ π) = ν.map g := by
    rw [← hπ.map_eq, Measure.map_map hg hπ.measurable]
  rw [e2, e3]
  exact e1.trans h'

section Indep

variable {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C)

/-- Two distinct coordinates of one block are independent under `coordLaw`. -/
private lemma Underline_Y_indep_coord (i j k l : Fin N) (hne : ¬ (i = k ∧ j = l)) :
    IndepFun (fun u : Coords N => Underline_Y u i j) (fun u : Coords N => Underline_Y u k l)
      (coordLaw N L) := by
  have hpd := iIndepFun_pi (μ := fun _ : Fin N => (L.νd : Measure ℝ))
    (X := fun _ => (fun x : ℝ => ((x : ℝ) : ℂ))) (fun _ => by fun_prop)
  have hpo := iIndepFun_pi (μ := fun _ : Fin N => (L.νo : Measure ℂ))
    (X := fun _ => (id : ℂ → ℂ)) (fun _ => aemeasurable_id)
  have hpr := iIndepFun_pi (μ := fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
    (X := fun _ => (id : (Fin N → ℂ) → (Fin N → ℂ))) (fun _ => aemeasurable_id)
  by_cases hij : i = j <;> by_cases hkl : k = l
  · -- diagonal and diagonal
    subst hij hkl
    have hik : i ≠ k := fun h => hne ⟨h, h⟩
    have h1 := hpd.indepFun hik
    have h2 := Underline_indepFun_comp (π := Prod.fst) (μ := coordLaw N L)
      (ν := Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)) measurePreserving_fst
      (f := fun d : Fin N → ℝ => ((d i : ℝ) : ℂ)) (g := fun d : Fin N → ℝ => ((d k : ℝ) : ℂ))
      (by fun_prop) (by fun_prop) h1
    simpa [Underline_Y] using h2
  · -- diagonal and array
    subst hij
    have h2 : IndepFun (fun u : Coords N => ((u.1 i : ℝ) : ℂ)) (fun u : Coords N => u.2 k l)
        (coordLaw N L) :=
      indepFun_prod (μ := Measure.pi fun _ : Fin N => (L.νd : Measure ℝ))
        (ν := Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
        (X := fun d : Fin N → ℝ => ((d i : ℝ) : ℂ))
        (Y := fun r : Fin N → Fin N → ℂ => r k l) (by fun_prop) (by fun_prop)
    simpa [Underline_Y, hkl] using h2
  · -- array and diagonal
    subst hkl
    have h2 : IndepFun (fun u : Coords N => ((u.1 k : ℝ) : ℂ)) (fun u : Coords N => u.2 i j)
        (coordLaw N L) :=
      indepFun_prod (μ := Measure.pi fun _ : Fin N => (L.νd : Measure ℝ))
        (ν := Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
        (X := fun d : Fin N → ℝ => ((d k : ℝ) : ℂ))
        (Y := fun r : Fin N → Fin N → ℂ => r i j) (by fun_prop) (by fun_prop)
    simpa [Underline_Y, hij] using h2.symm
  · -- array and array
    by_cases hik : i = k
    · subst hik
      have hjl : j ≠ l := fun h => hne ⟨rfl, h⟩
      have h1 := hpo.indepFun hjl
      have hmp : MeasurePreserving (fun u : Coords N => u.2 i) (coordLaw N L)
          (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) :=
        (measurePreserving_eval (fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
          i).comp measurePreserving_snd
      have h2 := Underline_indepFun_comp hmp (f := fun r : Fin N → ℂ => r j)
        (g := fun r : Fin N → ℂ => r l) (measurable_pi_apply j) (measurable_pi_apply l) h1
      simpa [Underline_Y, hij, hkl] using h2
    · have h1 := hpr.indepFun hik
      have mj : Measurable (fun r : Fin N → ℂ => r j) := measurable_pi_apply j
      have ml : Measurable (fun r : Fin N → ℂ => r l) := measurable_pi_apply l
      have h1' := h1.comp (φ := fun r : Fin N → ℂ => r j) (ψ := fun r : Fin N → ℂ => r l) mj ml
      have h2 := Underline_indepFun_comp (π := Prod.snd) (μ := coordLaw N L)
        (ν := Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
        measurePreserving_snd
        (f := fun r : Fin N → Fin N → ℂ => r i j) (g := fun r : Fin N → Fin N → ℂ => r k l)
        (by fun_prop) (by fun_prop) h1'
      simpa [Underline_Y, hij, hkl] using h2

/-- Two distinct coordinates of the blocks are independent under `blockLaw`. -/
private lemma Underline_Y_indep (a b : Fin D) (i j k l : Fin N)
    (hne : ¬ (a = b ∧ i = k ∧ j = l)) :
    IndepFun (fun w : Fin D → Coords N => Underline_Y (w a) i j)
      (fun w : Fin D → Coords N => Underline_Y (w b) k l) (blockLaw D N L) := by
  by_cases hab : a = b
  · subst hab
    have h1 := Underline_Y_indep_coord L i j k l (fun h => hne ⟨rfl, h⟩)
    exact Underline_indepFun_comp (Underline_mp_coord D N L a) (Underline_measurable_Y N i j)
      (Underline_measurable_Y N k l) h1
  · have h1 := (iIndepFun_pi (μ := fun _ : Fin D => coordLaw N L)
      (X := fun _ => (id : Coords N → Coords N)) (fun _ => aemeasurable_id)).indepFun hab
    exact h1.comp (Underline_measurable_Y N i j) (Underline_measurable_Y N k l)

end Indep

section Moments

variable {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C)

/-- The integral of a measurable function of a coordinate against `blockLaw`. -/
private lemma Underline_Y_marg (a : Fin D) (i j : Fin N) (h : ℂ → ℂ) (hh : Measurable h) :
    ∫ w, h (Underline_Y (w a) i j) ∂(blockLaw D N L) =
      if i = j then ∫ x : ℝ, h (x : ℂ) ∂(L.νd : Measure ℝ) else ∫ z, h z ∂(L.νo : Measure ℂ) := by
  by_cases hij : i = j
  · subst hij
    simp only [Underline_Y, ite_true]
    exact Underline_integral_comp (Underline_mp_D D N L a i) (fun x : ℝ => h (x : ℂ))
      (hh.comp Complex.measurable_ofReal)
  · simp only [Underline_Y, hij, ite_false]
    exact Underline_integral_comp (Underline_mp_A D N L a i j) h hh

/-- A coordinate has mean zero. -/
private lemma Underline_Y_mean (φ : ℂ → ℂ) (hφ : φ = id ∨ φ = star) (a : Fin D) (i j : Fin N) :
    ∫ w, φ (Underline_Y (w a) i j) ∂(blockLaw D N L) = 0 := by
  have hφm : Measurable φ := by rcases hφ with rfl | rfl <;> fun_prop
  rw [Underline_Y_marg L a i j φ hφm]
  split_ifs
  · rcases hφ with rfl | rfl
    · simp only [id_eq]
      rw [integral_complex_ofReal, L.meand]
      simp
    · simp only [Complex.star_def, Complex.conj_ofReal]
      rw [integral_complex_ofReal, L.meand]
      simp
  · rcases hφ with rfl | rfl
    · simpa using L.meano
    · simp only [Complex.star_def]
      rw [integral_conj, L.meano]
      simp

/-- `z * z̄ = |z|²`. -/
private lemma Underline_mul_star (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Complex conjugation is not the identity. -/
private lemma Underline_id_ne_star : (id : ℂ → ℂ) ≠ star := fun h => by
  have h1 := congrFun h Complex.I
  simp only [id_eq, Complex.star_def, Complex.conj_I] at h1
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination h1
  exact Complex.I_ne_zero ((mul_eq_zero.1 h2).resolve_left two_ne_zero)

/-- The second moments of a coordinate: `E Y² = δ_{ij}`, `E |Y|² = 1`. -/
private lemma Underline_Y_moment (φ ψ : ℂ → ℂ) (hφ : φ = id ∨ φ = star) (hψ : ψ = id ∨ ψ = star)
    (a : Fin D) (i j : Fin N) :
    ∫ w, φ (Underline_Y (w a) i j) * ψ (Underline_Y (w a) i j) ∂(blockLaw D N L) =
      if φ = ψ then (if i = j then 1 else 0) else 1 := by
  have hφm : Measurable φ := by rcases hφ with rfl | rfl <;> fun_prop
  have hψm : Measurable ψ := by rcases hψ with rfl | rfl <;> fun_prop
  rw [Underline_Y_marg L a i j (fun z => φ z * ψ z) (hφm.mul hψm)]
  have hdiag : ∫ x : ℝ, ((x : ℂ) * (x : ℂ)) ∂(L.νd : Measure ℝ) = 1 := by
    have : ∀ x : ℝ, ((x : ℂ) * (x : ℂ)) = (((x ^ 2 : ℝ)) : ℂ) := fun x => by push_cast; ring
    simp only [this]
    rw [integral_complex_ofReal, L.vard]
    simp
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  have hoff : ∫ z : ℂ, z * z ∂(L.νo : Measure ℂ) = 0 := by
    simpa [sq] using L.pseudo
  have hnorm : ∫ z : ℂ, z * star z ∂(L.νo : Measure ℂ) = 1 := by
    simp only [Underline_mul_star]
    rw [integral_complex_ofReal, L.varo]
    simp
  have hstar : ∫ z : ℂ, star z * star z ∂(L.νo : Measure ℂ) = 0 := by
    have : ∀ z : ℂ, star z * star z = starRingEnd ℂ (z * z) := fun z => by
      simp
    simp only [this]
    rw [integral_conj, hoff]
    simp
  have hnorm' : ∫ z : ℂ, star z * z ∂(L.νo : Measure ℂ) = 1 := by
    simpa only [mul_comm (star _ : ℂ) _] using hnorm
  have hne1 : ((id : ℂ → ℂ) = star) = False := eq_false Underline_id_ne_star
  have hne2 : ((star : ℂ → ℂ) = id) = False := eq_false Underline_id_ne_star.symm
  rcases hφ with rfl | rfl <;> rcases hψ with rfl | rfl <;> by_cases h : i = j <;>
    simp only [h, hne1, hne2, ite_true, ite_false]
  · simpa using hdiag
  · simpa using hoff
  · simpa [hs] using hdiag
  · simpa using hnorm
  · simpa [hs] using hdiag
  · simpa using hnorm'
  · simpa [hs] using hdiag
  · simpa using hstar

/-- The covariance of two coordinates under `blockLaw`. -/
private lemma Underline_cov_Y (φ ψ : ℂ → ℂ) (hφ : φ = id ∨ φ = star) (hψ : ψ = id ∨ ψ = star)
    (a b : Fin D) (i j k l : Fin N) :
    ∫ w, φ (Underline_Y (w a) i j) * ψ (Underline_Y (w b) k l) ∂(blockLaw D N L) =
      if a = b ∧ i = k ∧ j = l then (if φ = ψ then (if i = j then 1 else 0) else 1) else 0 := by
  have hφm : Measurable φ := by rcases hφ with rfl | rfl <;> fun_prop
  have hψm : Measurable ψ := by rcases hψ with rfl | rfl <;> fun_prop
  by_cases hkey : a = b ∧ i = k ∧ j = l
  · obtain ⟨rfl, rfl, rfl⟩ := hkey
    simp only [and_self, ite_true]
    exact Underline_Y_moment L φ ψ hφ hψ a i j
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hkey)]
    have hind := (Underline_Y_indep L a b i j k l hkey).comp hφm hψm
    have := hind.integral_fun_mul_eq_mul_integral
      (hφm.comp (Underline_measurable_Y N i j |>.comp (measurable_pi_apply a))).aestronglyMeasurable
      (hψm.comp (Underline_measurable_Y N k l |>.comp (measurable_pi_apply b))).aestronglyMeasurable
    simp only [Function.comp_def] at this
    rw [this, Underline_Y_mean L φ hφ, zero_mul]

end Moments

section Entries

variable {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C)

/-- The covariance of two Hermitian entries: `E T_{ij} T_{kl} = δ_{il} δ_{jk}`, for entries in
the same block, and `0` across different blocks. -/
private lemma Underline_cov_T (a b : Fin D) (i j k l : Fin N) :
    ∫ w, Underline_T (w a) i j * Underline_T (w b) k l ∂(blockLaw D N L) =
      if a = b ∧ i = l ∧ j = k then 1 else 0 := by
  have hne1 : ((id : ℂ → ℂ) = star) = False := eq_false Underline_id_ne_star
  have hne2 : ((star : ℂ → ℂ) = id) = False := eq_false Underline_id_ne_star.symm
  unfold Underline_T
  by_cases h1 : i ≤ j <;> by_cases h2 : k ≤ l <;> simp only [h1, h2, ite_true, ite_false]
  · have := Underline_cov_Y L id id (Or.inl rfl) (Or.inl rfl) a b i j k l
    simp only [id_eq] at this
    rw [this]
    split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.le_def] at *; omega)
  · have := Underline_cov_Y L id star (Or.inl rfl) (Or.inr rfl) a b i j l k
    simp only [id_eq, hne1, ite_false] at this
    rw [this]
  · have := Underline_cov_Y L star id (Or.inr rfl) (Or.inl rfl) a b j i k l
    simp only [id_eq, hne2, ite_false] at this
    rw [this]
    split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.le_def] at *; omega)
  · have := Underline_cov_Y L star star (Or.inr rfl) (Or.inr rfl) a b j i l k
    rw [this]
    simp only [ite_true]
    split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.le_def] at *; omega)

/-- Each Hermitian entry is square integrable under `blockLaw`. -/
private lemma Underline_memLp_T (a : Fin D) (i j : Fin N) :
    MemLp (fun w : Fin D → Coords N => Underline_T (w a) i j) 2 (blockLaw D N L) := by
  have hY : ∀ i j : Fin N,
      MemLp (fun w : Fin D → Coords N => Underline_Y (w a) i j) 2 (blockLaw D N L) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h : MemLp (fun x : ℝ => (x : ℂ)) 2 (L.νd : Measure ℝ) := by
        rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
        simpa using L.intd 2
      have e : (fun w : Fin D → Coords N => Underline_Y (w a) i i) =
          (fun x : ℝ => (x : ℂ)) ∘ (fun w : Fin D → Coords N => (w a).1 i) := by
        funext w
        simp [Underline_Y]
      rw [e]
      exact h.comp_measurePreserving (Underline_mp_D D N L a i)
    · have h : MemLp (id : ℂ → ℂ) 2 (L.νo : Measure ℂ) := by
        rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
        simpa using L.into 2
      have e : (fun w : Fin D → Coords N => Underline_Y (w a) i j) =
          (id : ℂ → ℂ) ∘ (fun w : Fin D → Coords N => (w a).2 i j) := by
        funext w
        simp [Underline_Y, hij]
      rw [e]
      exact h.comp_measurePreserving (Underline_mp_A D N L a i j)
  unfold Underline_T
  by_cases h : i ≤ j
  · simpa [h] using hY i j
  · simp only [h, ite_false]
    exact (hY j i).star

/-- The entries of `blockH` through the Hermitian entries. -/
private lemma Underline_blockH_apply (w : Fin D → Coords N) (p q : Idx D N) :
    blockH D N w p q =
      if p.1 = q.1 then (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Underline_T (w p.1) p.2 q.2
      else 0 := by
  simp only [blockH, Underline_wig_eq]

/-- Each entry of `blockH` is square integrable under `blockLaw`. -/
private lemma Underline_memLp_blockH (p q : Idx D N) :
    MemLp (fun w : Fin D → Coords N => blockH D N w p q) 2 (blockLaw D N L) := by
  simp only [Underline_blockH_apply]
  by_cases h : p.1 = q.1
  · simp only [eq_true h, ite_true]
    have := (Underline_memLp_T L p.1 p.2 q.2).const_mul
      (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    exact this
  · simp only [eq_false h, ite_false]
    exact memLp_const 0

/-- The covariance of two entries of `blockH`: `E H_{pq} H_{rt} = N⁻¹ δ_{pt} δ_{qr}` within a
block (2.1) [eq:meanvar], (2.2) [eq:meanvar2]. -/
private lemma Underline_cov_blockH (p q r t : Idx D N) :
    ∫ w, blockH D N w p q * blockH D N w r t ∂(blockLaw D N L) =
      if p.1 = q.1 ∧ p = t ∧ q = r then ((N : ℂ))⁻¹ else 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos p.2
  have hs : (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((N : ℂ))⁻¹ := by
    have h : ((N : ℝ) ^ (-(1 / 2 : ℝ))) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) = (N : ℝ)⁻¹ := by
      rw [← Real.rpow_add hN]
      norm_num [Real.rpow_neg_one]
    rw [← Complex.ofReal_mul, h]
    push_cast
    rfl
  simp only [Underline_blockH_apply]
  by_cases hpq : p.1 = q.1
  · by_cases hrt : r.1 = t.1
    · have hiff : (p.1 = r.1 ∧ p.2 = t.2 ∧ q.2 = r.2) ↔ (p = t ∧ q = r) := by
        simp only [Prod.ext_iff]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1.trans hrt, h2⟩, ⟨hpq.symm.trans h1, h3⟩⟩
        · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
          exact ⟨h1.trans hrt.symm, h2, h4⟩
      have hrhs : (if p.1 = q.1 ∧ p = t ∧ q = r then ((N : ℂ))⁻¹ else 0) =
          if p = t ∧ q = r then ((N : ℂ))⁻¹ else 0 := by
        simp only [eq_true hpq, true_and]
      have e : ∀ w : Fin D → Coords N,
          (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Underline_T (w p.1) p.2 q.2 *
            ((((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Underline_T (w r.1) r.2 t.2) =
          ((N : ℂ))⁻¹ * (Underline_T (w p.1) p.2 q.2 * Underline_T (w r.1) r.2 t.2) := fun w => by
        rw [← hs]; ring
      rw [hrhs]
      simp only [eq_true hpq, eq_true hrt, ite_true, e]
      rw [integral_const_mul, Underline_cov_T L p.1 r.1 p.2 q.2 r.2 t.2]
      by_cases hd : p = t ∧ q = r
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 hd)),
          ite_eq_left_of_eq_true _ _ (eq_true hd), mul_one]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hd (hiff.1 h)),
          ite_eq_right_of_eq_false _ _ (eq_false hd), mul_zero]
    · have hc' : ¬ (p.1 = q.1 ∧ p = t ∧ q = r) := by
        rintro ⟨-, h2, h3⟩
        exact hrt (by rw [← h3, ← h2]; exact hpq.symm)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc')]
      simp only [eq_true hpq, eq_false hrt, ite_true, ite_false, mul_zero, integral_zero]
  · have hc' : ¬ (p.1 = q.1 ∧ p = t ∧ q = r) := fun h => hpq h.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc')]
    simp only [eq_false hpq, ite_false, zero_mul, integral_zero]

end Entries

/-- (2.30) [eq:HGline]: `Ẽ[H̃ G H̃] = Σ_a D⟨G E_a⟩ E_a`, entrywise: the `(x, y)` entry is
`δ_{xy} N⁻¹ Σ_j G_{(a, j), (a, j)}` with `a` the block of `x`. -/
theorem integral_blockH_mul_blockH (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (G : Matrix (Idx D N) (Idx D N) ℂ) (x y : Idx D N) :
    ∫ w, (blockH D N w * G * blockH D N w) x y ∂(blockLaw D N L) =
      if x = y then ((N : ℂ))⁻¹ * ∑ j : Fin N, G (x.1, j) (x.1, j) else 0 := by
  have e : ∀ w : Fin D → Coords N, (blockH D N w * G * blockH D N w) x y =
      ∑ p, ∑ q, G p q * (blockH D N w x p * blockH D N w q y) := fun w => by
    rw [Underline_mul3_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  have hint : ∀ p q : Idx D N, Integrable
      (fun w => G p q * (blockH D N w x p * blockH D N w q y)) (blockLaw D N L) := fun p q =>
    (((Underline_memLp_blockH L x p).integrable_mul (Underline_memLp_blockH L q y))).const_mul _
  simp only [e]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  have e2 : ∀ p : Idx D N, ∫ w, ∑ q, G p q * (blockH D N w x p * blockH D N w q y)
      ∂(blockLaw D N L) = ∑ q, G p q *
        if x.1 = p.1 ∧ x = y ∧ p = q then ((N : ℂ))⁻¹ else 0 := fun p => by
    rw [integral_finsetSum _ fun q _ => hint p q]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul, Underline_cov_blockH L x p q y]
  simp only [e2]
  by_cases hxy : x = y
  · subst hxy
    simp only [true_and, ite_true]
    have h1 : ∀ p : Idx D N, ∑ q, G p q * (if x.1 = p.1 ∧ p = q then ((N : ℂ))⁻¹ else 0) =
        if x.1 = p.1 then ((N : ℂ))⁻¹ * G p p else 0 := by
      intro p
      by_cases hp : x.1 = p.1
      · rw [Finset.sum_eq_single p]
        · simp [hp, mul_comm]
        · intro q _ hq
          simp [hq.symm]
        · simp
      · simp [hp]
    simp only [h1]
    rw [Fintype.sum_prod_type]
    have h2 : ∀ b : Fin D, ∑ j : Fin N,
        (if x.1 = b then ((N : ℂ))⁻¹ * G (b, j) (b, j) else 0) =
        if x.1 = b then ∑ j : Fin N, ((N : ℂ))⁻¹ * G (b, j) (b, j) else 0 := fun b => by
      split_ifs <;> simp
    simp only [h2]
    rw [Finset.sum_ite_eq]
    simp [Finset.mul_sum]
  · simp [hxy]

end RBMTransitionEdge

end
