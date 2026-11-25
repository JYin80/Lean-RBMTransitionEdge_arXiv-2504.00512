module

public import RBMTransitionEdge.LocalLaw.FluctIsoDer
public import RBMTransitionEdge.LocalLaw.ExpansionHP

@[expose] public section

/-!
# The order-one terms of the isotropic moment inequality

The order-one part of the expansion of
`E (H̲G)_{uv}^p conj((H̲G)_{uv})^p` for (2.30) [eq:HGline] in the class: the second cumulants
cancel `E (S_θ(G) G)_{uv} f` exactly, Lemma 2.11 [lem:complex_cumu] with a high-probability
remainder bounds the rest.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### `(H̲G)_{xy}` and its derivative as functions of the resolvent -/

/-- The diagonal form `S_θ(R) = diag(Σ_r s_{kr} R_{rr})` of the profile map. -/
private lemma FIO_sTheta_diag (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ R = Matrix.diagonal (fun k : Idx D N =>
      ∑ r, ((varProf D N θ k r : ℝ) : ℂ) * R r r) := by
  ext p q
  by_cases h : p = q
  · subst h
    have h1 : sTheta D N θ R p p = (θ : ℂ) * ((D : ℂ) * ntr (R * Ea D N p.1)) +
        ((1 - θ : ℝ) : ℂ) * ntr R := by
      simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea]
    rw [h1, Matrix.diagonal_apply_eq]
    have hD : (D : ℂ) ≠ 0 := by
      have := p.1.pos
      exact_mod_cast this.ne'
    have hN : (N : ℂ) ≠ 0 := by
      have := p.2.pos
      exact_mod_cast this.ne'
    simp only [ntr, Matrix.trace, Matrix.diag, Matrix.mul_apply, Ea, Matrix.diagonal_apply,
      Fintype.card_prod, Fintype.card_fin, varProf]
    push_cast
    simp only [mul_ite, mul_zero, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : (∑ x : Idx D N, ∑ x_1 : Idx D N,
        if x_1 = x then if x_1.1 = p.1 then R x x_1 * 1 else 0 else 0) =
        ∑ x : Idx D N, if x.1 = p.1 then R x x else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x.1 = p.1 <;> simp [hx]
    have e2 : ∀ x : Idx D N, (θ : ℂ) * ((if p.1 = x.1 then ((N : ℝ)⁻¹ : ℝ) else 0 : ℝ) : ℂ) *
        R x x = (θ : ℂ) * (N : ℂ)⁻¹ * (if x.1 = p.1 then R x x else 0) := by
      intro x
      by_cases hx : x.1 = p.1
      · simp [hx]
      · have : ¬ p.1 = x.1 := fun h => hx h.symm
        simp [hx, this]
    rw [e1]
    simp only [e2, ← Finset.mul_sum]
    field_simp
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

/-- `H̲G = 1 - (Λ - z) G + S_θ(G) G` written for an arbitrary matrix `M` in place of `G`,
(2.30) [eq:HGline] with `H G = 1 - (Λ - z) G`. -/
private def FIO_hg (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (M : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M +
    Matrix.diagonal (fun k => ∑ r, ((varProf D N θ k r : ℝ) : ℂ) * M r r) * M

/-- The form `u^* (H̲G) y` of `FIO_hg`. -/
private def FIO_d (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) (y : Idx D N → ℂ) : ℂ :=
  star u ⬝ᵥ (FIO_hg D N θ Λ z M *ᵥ y)

/-- The derivative `hgDer` of (2.30) [eq:HGline] in the direction `E_{ab}`, with `M` in place of
`G`. -/
private def FIO_der (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) (a b : Idx D N) : ℂ :=
  starRingEnd ℂ (u a) * (M *ᵥ v) b - FIO_d D N θ Λ z u M (Pi.single a 1) * (M *ᵥ v) b -
    (N : ℂ)⁻¹ * ∑ r, M r a * M b r * (star (tiltV D N θ u r) ⬝ᵥ (M *ᵥ v))

/-- The sum `T₁ = Σ_{ij} ū_i s_{ij} (M v)_j ∂_{E_{ji}} (H̲G)_{uv}`. -/
private def FIO_T1 (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * (M *ᵥ v) j *
    FIO_der D N θ Λ z u v M j i

/-- The sum `T₂ = Σ_{ij} ū_i s_{ij} (M v)_j conj(∂_{E_{ij}} (H̲G)_{uv})`. -/
private def FIO_T2 (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * (M *ᵥ v) j *
    starRingEnd ℂ (FIO_der D N θ Λ z u v M i j)

/-- The remainder of the order-one term,
`(p - 1) 𝒟^{p-2} conj(𝒟)^p T₁ + p 𝒟^{p-1} conj(𝒟)^{p-1} T₂` with `𝒟 = (H̲G)_{uv}`. -/
private def FIO_R (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ((p - 1 : ℕ) : ℂ) * FIO_d D N θ Λ z u M v ^ (p - 2) *
      starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ p * FIO_T1 D N θ Λ z u v M +
    (p : ℂ) * FIO_d D N θ Λ z u M v ^ (p - 1) *
      starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ (p - 1) * FIO_T2 D N θ Λ z u v M

/-- The value of `∂_w f` on the slice `(j, i)`, `f = G_{jv} 𝒟^{p-1} conj(𝒟)^p`. -/
private def FIO_E1 (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) : ℂ :=
  (-(if j = i then (1 / 2 : ℂ) else 1) * (M j j * (M *ᵥ v) i) *
        FIO_d D N θ Λ z u M v ^ (p - 1) +
      (M *ᵥ v) j * (((p - 1 : ℕ) : ℂ) * FIO_d D N θ Λ z u M v ^ (p - 1 - 1) *
        ((if j = i then (1 / 2 : ℂ) else 1) * FIO_der D N θ Λ z u v M j i))) *
      starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ p +
    (M *ᵥ v) j * FIO_d D N θ Λ z u M v ^ (p - 1) *
      ((p : ℂ) * starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ (p - 1) *
        starRingEnd ℂ ((if j = i then (1 / 2 : ℂ) else 1) * FIO_der D N θ Λ z u v M i j))

/-- The value of `∂_{w̄} f` on the slice `(j, i)`, `f = G_{jv} 𝒟^{p-1} conj(𝒟)^p`. -/
private def FIO_E0 (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) : ℂ :=
  (-(if j = i then (1 / 2 : ℂ) else 1) * (M j i * (M *ᵥ v) j) *
        FIO_d D N θ Λ z u M v ^ (p - 1) +
      (M *ᵥ v) j * (((p - 1 : ℕ) : ℂ) * FIO_d D N θ Λ z u M v ^ (p - 1 - 1) *
        ((if j = i then (1 / 2 : ℂ) else 1) * FIO_der D N θ Λ z u v M i j))) *
      starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ p +
    (M *ᵥ v) j * FIO_d D N θ Λ z u M v ^ (p - 1) *
      ((p : ℂ) * starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ (p - 1) *
        starRingEnd ℂ ((if j = i then (1 / 2 : ℂ) else 1) * FIO_der D N θ Λ z u v M j i))

/-- The term `(S_θ(M) M)_{uv} 𝒟^{p-1} conj(𝒟)^p`. -/
private def FIO_Q (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  (star u ⬝ᵥ ((Matrix.diagonal (fun k => ∑ r, ((varProf D N θ k r : ℝ) : ℂ) * M r r) * M) *ᵥ v)) *
    FIO_d D N θ Λ z u M v ^ (p - 1) * starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ p

/-- The profile is symmetric, `s_{ij} = s_{ji}`. -/
private lemma FIO_prof_symm (D N : ℕ) (θ : ℝ) (i j : Idx D N) :
    varProf D N θ i j = varProf D N θ j i := by
  unfold varProf
  by_cases h : i.1 = j.1
  · simp [h]
  · have h' : ¬ j.1 = i.1 := fun e => h e.symm
    simp [h, h']

/-- The exact cancellation: the second-cumulant terms of the slices `(j, i)` and
`(S_θ(M) M)_{uv} 𝒟^{p-1} conj(𝒟)^p` add up to the remainder `FIO_R`. -/
private lemma FIO_alg (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (u i) *
        ((if j = i then ((varProf D N θ j i : ℝ) : ℂ) else 0) * FIO_E0 D N θ Λ z u v p M i j +
          ((varProf D N θ j i : ℝ) : ℂ) * FIO_E1 D N θ Λ z u v p M i j)) +
      FIO_Q D N θ Λ z u v p M = FIO_R D N θ Λ z u v p M := by
  set d := FIO_d D N θ Λ z u M v with hd
  have hterm : ∀ i j, starRingEnd ℂ (u i) *
      ((if j = i then ((varProf D N θ j i : ℝ) : ℂ) else 0) * FIO_E0 D N θ Λ z u v p M i j +
        ((varProf D N θ j i : ℝ) : ℂ) * FIO_E1 D N θ Λ z u v p M i j) =
      starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) *
        (-(M j j * (M *ᵥ v) i) * d ^ (p - 1) * starRingEnd ℂ d ^ p +
          (M *ᵥ v) j * (((p - 1 : ℕ) : ℂ) * d ^ (p - 2) * FIO_der D N θ Λ z u v M j i) *
            starRingEnd ℂ d ^ p +
          (M *ᵥ v) j * d ^ (p - 1) * ((p : ℂ) * starRingEnd ℂ d ^ (p - 1) *
            starRingEnd ℂ (FIO_der D N θ Λ z u v M i j))) := by
    intro i j
    have e2 : p - 1 - 1 = p - 2 := by omega
    rw [FIO_prof_symm D N θ j i]
    by_cases hji : j = i
    · subst hji
      simp only [FIO_E0, FIO_E1, ite_true, e2, map_mul, map_div₀, map_one, map_ofNat, ← hd]
      ring
    · simp only [FIO_E1, hji, ite_false, e2, one_mul, ← hd]
      ring
  have hQ : FIO_Q D N θ Λ z u v p M = ∑ i, ∑ j, starRingEnd ℂ (u i) *
      ((varProf D N θ i j : ℝ) : ℂ) * (M j j * (M *ᵥ v) i) * d ^ (p - 1) *
        starRingEnd ℂ d ^ p := by
    unfold FIO_Q
    rw [← hd, ← Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j, hQ]
  unfold FIO_R FIO_T1 FIO_T2
  rw [← hd]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The order-one term on Hermitian arrays -/

/-- On Hermitian arrays `H̲G` of (2.30) [eq:HGline] is `FIO_hg` at `G = (h + Λ - z)⁻¹`. -/
private lemma FIO_hgUnder_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    hgUnder D N θ (Matrix.of h) Λ z = FIO_hg D N θ Λ z (res (Matrix.of h + Λ) z) := by
  have hres := (res_mul_sub (Matrix.of h + Λ) (hh.add hΛ) z hz).1
  unfold hgUnder FIO_hg
  rw [FIO_sTheta_diag]
  congr 1
  calc Matrix.of h * res (Matrix.of h + Λ) z =
      (Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z -
        (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z := by
        rw [← Matrix.sub_mul]
        congr 1
        abel
    _ = _ := by rw [hres]

/-- On Hermitian arrays `hgDer` is `FIO_der` at `G = (h + Λ - z)⁻¹`. -/
private lemma FIO_hgDer_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (u v : Idx D N → ℂ) (a b : Idx D N) :
    hgDer D N θ (Matrix.of h) Λ z u v a b =
      FIO_der D N θ Λ z u v (res (Matrix.of h + Λ) z) a b := by
  unfold hgDer FIO_der FIO_d
  rw [FIO_hgUnder_eq D N θ Λ hΛ z hz h hh]

/-- On Hermitian arrays `u^* (H̲G) y` is `FIO_d` at `G = (h + Λ - z)⁻¹`. -/
private lemma FIO_d_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (u y : Idx D N → ℂ) :
    star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) =
      FIO_d D N θ Λ z u (res (Matrix.of h + Λ) z) y := by
  unfold FIO_d
  rw [FIO_hgUnder_eq D N θ Λ hΛ z hz h hh]

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma FIO_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
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

/-- Every point of a Hermitian slice is Hermitian. -/
private lemma FIO_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

/-- The slice `w ↦ setEntry h i j w` is real-differentiable. -/
private lemma FIO_diff_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    Differentiable ℝ (fun w : ℂ => setEntry h i j w) := by
  refine differentiable_pi.2 fun k => differentiable_pi.2 fun l => ?_
  have hre : Differentiable ℝ (fun w : ℂ => ((w.re : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp Complex.reCLM).differentiable
  have hconj : Differentiable ℝ (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.differentiable
  by_cases hd : i = j
  · by_cases hkl : k = i ∧ l = i
    · simp only [setEntry, eq_true hd, eq_true hkl, ite_true]
      exact hre
    · simp only [setEntry, eq_true hd, eq_false hkl, ite_true, ite_false]
      exact differentiable_const _
  · by_cases h1 : k = i ∧ l = j
    · simp only [setEntry, eq_false hd, eq_true h1, ite_true, ite_false]
      exact differentiable_id
    · by_cases h2 : k = j ∧ l = i
      · simp only [setEntry, eq_false hd, eq_false h1, eq_true h2, ite_true, ite_false]
        exact hconj
      · simp only [setEntry, eq_false hd, eq_false h1, eq_false h2, ite_false]
        exact differentiable_const _

/-- The resolvent entries are real-differentiable along a Hermitian slice. -/
private lemma FIO_diff_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (a b k l : Idx D N) (w : ℂ) :
    DifferentiableAt ℝ (fun w => res (Matrix.of (setEntry h a b w) + Λ) z k l) w := by
  have e : (fun w => res (Matrix.of (setEntry h a b w) + Λ) z k l) =
      (fun h' => res (Matrix.of (symArr h') + Λ) z k l) ∘ (fun w => setEntry h a b w) := by
    funext w
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact ((contDiff_res_symArr Λ hΛ z hz.ne' k l 1).differentiable
    (by norm_num)).differentiableAt.comp w ((FIO_diff_setEntry h a b) w)

/-- `(H̲G)_{uv}` of (2.30) [eq:HGline] is real-differentiable along a Hermitian slice. -/
private lemma FIO_diff_hg (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (a b : Idx D N) (w : ℂ) :
    DifferentiableAt ℝ (fun w => star u ⬝ᵥ
      (hgUnder D N θ (Matrix.of (setEntry h a b w)) Λ z *ᵥ v)) w := by
  obtain ⟨P, hP, -, hev⟩ := hgUnder_resPoly D N θ hθ0 hθ1 Λ hΛ z hz u v hu hv
  have hP' : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t ht f hf
    rw [((hP t ht).2 f hf).2.2]
    exact ⟨hΛ, hz.ne'⟩
  have e : (fun w => star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h a b w)) Λ z *ᵥ v)) =
      (fun h' => resPolyEval P (symArr h')) ∘ (fun w => setEntry h a b w) := by
    funext w
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
    exact (hev _ (FIO_slice_herm h hh a b w)).symm
  rw [e]
  exact ((contDiff_resPoly_symArr P hP' 1).differentiable (by norm_num)).differentiableAt.comp
    w ((FIO_diff_setEntry h a b) w)

/-- The Wirtinger derivatives of a constant vanish. -/
private lemma FIO_dW_const (c w : ℂ) : dW (fun _ => c) w = 0 ∧ dWbar (fun _ => c) w = 0 := by
  simp [dW, dWbar]

/-- The Wirtinger derivatives of a power: `∂ (f^n) = n f^{n-1} ∂ f`. -/
private lemma FIO_dW_pow {f : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (n : ℕ) :
    dW (fun x => f x ^ n) w = (n : ℂ) * f w ^ (n - 1) * dW f w ∧
      dWbar (fun x => f x ^ n) w = (n : ℂ) * f w ^ (n - 1) * dWbar f w := by
  induction n with
  | zero => simp [dW, dWbar]
  | succ n ih =>
    have e : (fun x => f x ^ (n + 1)) = fun x => f x ^ n * f x := funext fun x => pow_succ _ _
    rw [e]
    obtain ⟨h1, h2⟩ := dW_mul (f := fun x => f x ^ n) (g := f) (hf.pow n) hf
    rw [h1, h2, ih.1, ih.2]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      constructor <;> ring

/-- The Wirtinger derivatives of a finite sum. -/
private lemma FIO_dW_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) w) :
    dW (fun x => ∑ i ∈ s, F i x) w = ∑ i ∈ s, dW (F i) w ∧
      dWbar (fun x => ∑ i ∈ s, F i x) w = ∑ i ∈ s, dWbar (F i) w := by
  refine ⟨?_, ?_⟩ <;>
  simp only [dW, dWbar, fderiv_fun_sum hF, _root_.sum_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]

/-- The Wirtinger derivatives of `(G v)_j` along the slice `(j, i)`: `∂_w = -c G_{jj} (G v)_i`,
`∂_{w̄} = -c G_{ji} (G v)_j`, with `c = 1/2` for `i = j` and `c = 1` otherwise. -/
private lemma FIO_dW_g {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (v : Idx D N → ℂ) (w : ℂ) :
    dW (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j) w =
        -(if j = i then (1 / 2 : ℂ) else 1) * (res (Matrix.of (setEntry h j i w) + Λ) z j j *
          (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) i) ∧
      dWbar (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j) w =
        -(if j = i then (1 / 2 : ℂ) else 1) * (res (Matrix.of (setEntry h j i w) + Λ) z j i *
          (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j) := by
  set G := fun w => res (Matrix.of (setEntry h j i w) + Λ) z with hG
  have e : (fun w => (G w *ᵥ v) j) = fun w => ∑ l, G w j l * v l := rfl
  have hdl : ∀ l ∈ Finset.univ, DifferentiableAt ℝ (fun w => G w j l * v l) w :=
    fun l _ => (FIO_diff_res Λ hΛ z hz h hh j i j l w).mul_const _
  have hterm : ∀ l, dW (fun w => G w j l * v l) w =
        -(if j = i then (1 / 2 : ℂ) else 1) * (G w j j * G w i l) * v l ∧
      dWbar (fun w => G w j l * v l) w =
        -(if j = i then (1 / 2 : ℂ) else 1) * (G w j i * G w j l) * v l := by
    intro l
    obtain ⟨m1, m2⟩ := dW_mul (FIO_diff_res Λ hΛ z hz h hh j i j l w)
      (differentiableAt_const (v l))
    obtain ⟨c1, c2⟩ := FIO_dW_const (v l) w
    obtain ⟨r1, r2⟩ := res_dW Λ hΛ z hz.ne' h hh j i j l
    refine ⟨?_, ?_⟩
    · rw [m1, c1, congrFun r1 w]
      ring
    · rw [m2, c2, congrFun r2 w]
      ring
  obtain ⟨s1, s2⟩ := FIO_dW_sum Finset.univ (fun l w => G w j l * v l) hdl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [s1, Finset.sum_congr rfl fun l _ => (hterm l).1]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [s2, Finset.sum_congr rfl fun l _ => (hterm l).2]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- The first Wirtinger derivatives of `f = G_{jv} 𝒟^{p-1} conj(𝒟)^p` along the slice `(j, i)`
at a Hermitian array, `𝒟 = (H̲G)_{uv}` of (2.30) [eq:HGline]. -/
private lemma FIO_deriv (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (p : ℕ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    dW (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i) = FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j ∧
      dWbar (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i) = FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j := by
  set w₀ := h j i with hw₀
  set g := fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j with hg
  set d := fun w => star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v) with hd
  have hgD : DifferentiableAt ℝ g w₀ := by
    have e : g = fun w => ∑ l, res (Matrix.of (setEntry h j i w) + Λ) z j l * v l := rfl
    rw [e]
    exact DifferentiableAt.fun_sum fun l _ => (FIO_diff_res Λ hΛ z hz h hh j i j l w₀).mul_const _
  have hdD : DifferentiableAt ℝ d w₀ := FIO_diff_hg D N θ hθ0 hθ1 Λ hΛ z hz u v hu hv h hh j i w₀
  have hcD : DifferentiableAt ℝ (fun w => starRingEnd ℂ (d w)) w₀ := hdD.star
  obtain ⟨m1, m1'⟩ := dW_mul (f := fun w => g w * d w ^ (p - 1))
    (g := fun w => starRingEnd ℂ (d w) ^ p) (hgD.mul (hdD.pow _)) (hcD.pow _)
  obtain ⟨m2, m2'⟩ := dW_mul (f := g) (g := fun w => d w ^ (p - 1)) hgD (hdD.pow (p - 1))
  obtain ⟨q1, q1'⟩ := FIO_dW_pow hdD (p - 1)
  obtain ⟨q2, q2'⟩ := FIO_dW_pow hcD p
  obtain ⟨c1, c1'⟩ := dW_conj hdD
  have d1 : dW d w₀ = _ := (hgUnder_dW D N θ Λ hΛ z hz h hh j i u v w₀).1
  have d2 : dWbar d w₀ = _ := (hgUnder_dW D N θ Λ hΛ z hz h hh j i u v w₀).2
  have g1 : dW g w₀ = _ := (FIO_dW_g Λ hΛ z hz h hh i j v w₀).1
  have g2 : dWbar g w₀ = _ := (FIO_dW_g Λ hΛ z hz h hh i j v w₀).2
  have hself : setEntry h j i w₀ = h := FIO_setEntry_self h hh j i
  have hg0 : g w₀ = (res (Matrix.of h + Λ) z *ᵥ v) j := by simp only [hg, hself]
  have hd0 : d w₀ = FIO_d D N θ Λ z u (res (Matrix.of h + Λ) z) v := by
    simp only [hd, hself]
    exact FIO_d_eq D N θ Λ hΛ z hz h hh u v
  rw [hself, FIO_hgDer_eq D N θ Λ hΛ z hz h hh] at d1 d2
  rw [hself] at g1 g2
  refine ⟨?_, ?_⟩
  · rw [m1, m2, q1, q2, c1, d1, d2, g1, hg0, hd0]
    unfold FIO_E1
    ring
  · rw [m1', m2', q1', q2', c1', d1, d2, g2, hg0, hd0]
    unfold FIO_E0
    ring

/-- The order-one term of the isotropic expansion with the cumulants of the class inserted:
`𝒞^{(1,1)}(h_{ji}) = s_{ji}`, `𝒞^{(0,2)}(h_{ji}) = s_{ji} δ_{ij}` (the display before
(2.27) [eq:bdd_cumu]) and the derivatives of `FIO_deriv`. -/
private lemma FIO_iso (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (u v : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (p : ℕ) :
    isoTerm D N θ μ Λ z u v p 1 = ∑ i, ∑ j, starRingEnd ℂ (u i) *
      ((if j = i then ((varProf D N θ j i : ℝ) : ℂ) else 0) *
          ∫ h, FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j ∂μ +
        ((varProf D N θ j i : ℝ) : ℂ) *
          ∫ h, FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j ∂μ) := by
  unfold isoTerm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨-, c11, -, c02⟩ := llClass_ccum_low D N C θ μ hμ j i
  have e0 : ∫ h, wirt 0 1 (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
      (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
      starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
      (h j i) ∂μ = ∫ h, FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    exact (FIO_deriv D N θ hθ0 hθ1 Λ hΛ z hz u v hu hv p h hh i j).2
  have e1 : ∫ h, wirt 1 0 (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
      (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
      starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
      (h j i) ∂μ = ∫ h, FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    exact (FIO_deriv D N θ hθ0 hθ1 Λ hΛ z hz u v hu hv p h hh i j).1
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (1 - 0 + 1 : ℕ) = 2 from rfl, show (1 - 1 + 1 : ℕ) = 1 from rfl,
    show (1 - 0 : ℕ) = 1 from rfl, show (1 - 1 : ℕ) = 0 from rfl, e0, e1, c11, c02]
  simp only [Nat.factorial_zero, Nat.factorial_one, mul_one, Nat.cast_one, div_one]

/-- A continuous function of the resolvent `G = (h + Λ - z)⁻¹` is integrable for a law of
Hermitian arrays: `|G_{kl}| ≤ η⁻¹` confines `G` to a compact set. -/
private lemma FIO_int {D N : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (Idx D N → Idx D N → ℂ)) [IsFiniteMeasure μ]
    (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (Φ : Matrix (Idx D N) (Idx D N) ℂ → E)
    (hΦ : Continuous Φ) :
    Integrable (fun h => Φ (res (Matrix.of h + Λ) z)) μ := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h) + Λ) z) :=
    continuous_pi fun k => continuous_pi fun l =>
      (contDiff_res_symArr Λ hΛ z hz.ne' k l 0).continuous
  have hm : AEStronglyMeasurable (fun h => Φ (res (Matrix.of h + Λ) z)) μ :=
    (hΦ.comp hc).aestronglyMeasurable.congr (by
      filter_upwards [hherm] with h hh
      simp only [Function.comp, symArr_of_isHermitian h hh])
  set S : Set (Matrix (Idx D N) (Idx D N) ℂ) :=
    Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) z.im⁻¹)) with hS
  have hSc : IsCompact S :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn hΦ.continuousOn
  refine Integrable.of_bound hm B ?_
  filter_upwards [hherm] with h hh
  refine hB _ fun k _ l _ => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_apply_le_opNorm _ k l).trans (opNorm_res_le _ (hh.add hΛ) z hz)

/-- The order-one term plus `E (S_θ(G) G)_{uv} 𝒟^{p-1} conj(𝒟)^p` is `E FIO_R(G)`: the exact
cancellation of the second cumulants against `E (S_θ(G) G)_{uv} f` (with `𝒥 = 0` in the class). -/
private lemma FIO_main_eq (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (u v : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (p : ℕ) :
    isoTerm D N θ μ Λ z u v p 1 +
        ∫ h, (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) *
            res (Matrix.of h + Λ) z) *ᵥ v)) *
          (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
          starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ =
      ∫ h, FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z) ∂μ := by
  have hprob := hμ.prob
  have hE0 : ∀ i j, Integrable (fun h => FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j)
      μ := fun i j => FIO_int μ hμ.herm Λ hΛ z hz (fun M => FIO_E0 D N θ Λ z u v p M i j)
        (by unfold FIO_E0 FIO_der FIO_d FIO_hg; fun_prop)
  have hE1 : ∀ i j, Integrable (fun h => FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j)
      μ := fun i j => FIO_int μ hμ.herm Λ hΛ z hz (fun M => FIO_E1 D N θ Λ z u v p M i j)
        (by unfold FIO_E1 FIO_der FIO_d FIO_hg; fun_prop)
  have hQ : Integrable (fun h => FIO_Q D N θ Λ z u v p (res (Matrix.of h + Λ) z)) μ :=
    FIO_int μ hμ.herm Λ hΛ z hz (fun M => FIO_Q D N θ Λ z u v p M)
      (by unfold FIO_Q FIO_d FIO_hg; fun_prop)
  have hterm : ∀ i j, Integrable (fun h => starRingEnd ℂ (u i) *
      ((if j = i then ((varProf D N θ j i : ℝ) : ℂ) else 0) *
          FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j +
        ((varProf D N θ j i : ℝ) : ℂ) * FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j))
      μ := fun i j => (((hE0 i j).const_mul _).add ((hE1 i j).const_mul _)).const_mul _
  have hrow : ∀ i, Integrable (fun h => ∑ j, starRingEnd ℂ (u i) *
      ((if j = i then ((varProf D N θ j i : ℝ) : ℂ) else 0) *
          FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j +
        ((varProf D N θ j i : ℝ) : ℂ) * FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j))
      μ := fun i => integrable_finsetSum _ fun j _ => hterm i j
  have hQeq : ∫ h, (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) *
          res (Matrix.of h + Λ) z) *ᵥ v)) *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ =
      ∫ h, FIO_Q D N θ Λ z u v p (res (Matrix.of h + Λ) z) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    simp only [FIO_Q, FIO_d_eq D N θ Λ hΛ z hz h hh, FIO_sTheta_diag]
  have hReq : (fun h => FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z)) = fun h =>
      (∑ i, ∑ j, starRingEnd ℂ (u i) *
        ((if j = i then ((varProf D N θ j i : ℝ) : ℂ) else 0) *
            FIO_E0 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j +
          ((varProf D N θ j i : ℝ) : ℂ) *
            FIO_E1 D N θ Λ z u v p (res (Matrix.of h + Λ) z) i j)) +
        FIO_Q D N θ Λ z u v p (res (Matrix.of h + Λ) z) :=
    funext fun h => (FIO_alg D N θ Λ z u v p _).symm
  rw [hQeq, hReq, integral_add (integrable_finsetSum _ fun i _ => hrow i) hQ,
    integral_finsetSum _ fun i _ => hrow i, FIO_iso D N C θ μ hμ hθ0 hθ1 Λ hΛ z hz u v hu hv p]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hterm i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_add ((hE0 i j).const_mul _) ((hE1 i j).const_mul _),
    integral_const_mul, integral_const_mul]

/-! ### Bounds on the remainder -/

/-- `0 ≤ s_{kr} ≤ N⁻¹` for `θ ∈ [0, 1]`. -/
private lemma FIO_prof_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k r : Idx D N) :
    0 ≤ varProf D N θ k r ∧ varProf D N θ k r ≤ (N : ℝ)⁻¹ := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast k.1.pos
  have hN : (0 : ℝ) < N := by exact_mod_cast k.2.pos
  have h1 : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
    have h2 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    nlinarith
  have h3 : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  unfold varProf
  split_ifs
  · constructor <;> nlinarith [inv_nonneg.mpr hN.le]
  · constructor <;> nlinarith

/-- The tilted vectors give `N⁻¹ t^r(x)^* w = Σ_k x̄_k s_{kr} w_k`. -/
private lemma FIO_tilt_dot (D N : ℕ) (θ : ℝ) (x w : Idx D N → ℂ) (r : Idx D N) :
    (N : ℂ)⁻¹ * (star (tiltV D N θ x r) ⬝ᵥ w) =
      ∑ k, starRingEnd ℂ (x k) * ((varProf D N θ k r : ℝ) : ℂ) * w k := by
  have hN : (N : ℂ) ≠ 0 := by
    have := r.2.pos
    exact_mod_cast this.ne'
  simp only [dotProduct, Pi.star_apply, tiltV, Complex.star_def, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  field_simp

/-- The unconjugated tilted vectors give `N⁻¹ Σ_k t^r(x)_k w_k = Σ_k x_k s_{kr} w_k`. -/
private lemma FIO_tilt_dot' (D N : ℕ) (θ : ℝ) (x w : Idx D N → ℂ) (r : Idx D N) :
    (N : ℂ)⁻¹ * ∑ k, w k * tiltV D N θ x r k =
      ∑ k, x k * ((varProf D N θ k r : ℝ) : ℂ) * w k := by
  have hN : (N : ℂ) ≠ 0 := by
    have := r.2.pos
    exact_mod_cast this.ne'
  simp only [tiltV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  field_simp

/-- A form `x^* A y` is linear in `y`: `x^* A y = Σ_i (x^* A e_i) y_i`. -/
private lemma FIO_form_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x y : ι → ℂ) : star x ⬝ᵥ (A *ᵥ y) = ∑ i, (star x ⬝ᵥ (A *ᵥ Pi.single i 1)) * y i := by
  simp only [Matrix.mulVec_single_one]
  simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.col_apply, Pi.star_apply]
  ring

/-- `Σ_k |f_k| ≤ N √D ζ` when `Σ_k |f_k|² ≤ N ζ²` on `DN` indices. -/
private lemma FIO_l1_le (D N : ℕ) (f : Idx D N → ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ) (hf : ∀ k, 0 ≤ f k)
    (h2 : ∑ k, f k ^ 2 ≤ N * ζ ^ 2) : ∑ k, f k ≤ N * Real.sqrt D * ζ := by
  have hs : (∑ k, f k) ^ 2 ≤ (N * Real.sqrt D * ζ) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Idx D N))) (f := f)
    have hc : ((Finset.univ : Finset (Idx D N)).card : ℝ) = D * N := by
      simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [hc] at h1
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc (∑ k, f k) ^ 2 ≤ D * N * ∑ k, f k ^ 2 := h1
      _ ≤ D * N * (N * ζ ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (N * Real.sqrt D * ζ) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hD]
        ring
  have h0 : 0 ≤ ∑ k, f k := Finset.sum_nonneg fun k _ => hf k
  have h0' : 0 ≤ (N : ℝ) * Real.sqrt D * ζ := by positivity
  nlinarith [sq_nonneg ((∑ k, f k) - N * Real.sqrt D * ζ),
    sq_nonneg ((∑ k, f k) + N * Real.sqrt D * ζ)]

/-- The regrouped form of `T₁`: with `σ_r = Σ_i ū_i s_{ir} (M v)_i`,
`T₁ = Σ_j (M v)_j (ū_j - (H̲G)_{u e_j}) σ_j - Σ_{j,r} (M v)_j M_{rj} σ_r Σ_i ū_i s_{ij} M_{ir}`. -/
private lemma FIO_T1_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) (σ : Idx D N → ℂ)
    (hσ : ∀ r, σ r = ∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i r : ℝ) : ℂ) * (M *ᵥ v) i) :
    FIO_T1 D N θ Λ z u v M =
      (∑ j, (M *ᵥ v) j * (starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)) *
          (∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * (M *ᵥ v) i)) -
        ∑ j, ∑ r, (M *ᵥ v) j * M r j * σ r *
          (∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * M i r) := by
  have hτ : ∀ a b, (N : ℂ)⁻¹ * ∑ r, M r a * M b r * (star (tiltV D N θ u r) ⬝ᵥ (M *ᵥ v)) =
      ∑ r, M r a * M b r * σ r := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hσ, ← FIO_tilt_dot]
    ring
  unfold FIO_T1 FIO_der
  simp only [hτ]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (M *ᵥ v) j * (starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)) *
        (∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * (M *ᵥ v) i) -
      ∑ r, (M *ᵥ v) j * M r j * σ r *
        (∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * M i r) =
      ∑ i, (starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * (M *ᵥ v) j *
        ((starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)) * (M *ᵥ v) i) -
        ∑ r, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * (M *ᵥ v) j *
          (M r j * M i r * σ r)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
      ring
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  ring

/-- The regrouped form of `T₂`: with `σ_r = Σ_i ū_i s_{ir} (M v)_i`,
`T₂ = Σ_j |(M v)_j|² (Σ_i |u_i|² s_{ij} - conj(Σ_i u_i s_{ij} (H̲G)_{u e_i})) -
Σ_{j,r} (M v)_j conj(M_{jr}) conj(σ_r) conj(Σ_i u_i s_{ij} M_{ri})`. -/
private lemma FIO_T2_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) (σ : Idx D N → ℂ)
    (hσ : ∀ r, σ r = ∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i r : ℝ) : ℂ) * (M *ᵥ v) i) :
    FIO_T2 D N θ Λ z u v M =
      (∑ j, (M *ᵥ v) j * starRingEnd ℂ ((M *ᵥ v) j) *
          ((∑ i, starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * u i) -
            starRingEnd ℂ (∑ i, u i * ((varProf D N θ i j : ℝ) : ℂ) *
              FIO_d D N θ Λ z u M (Pi.single i 1)))) -
        ∑ j, ∑ r, (M *ᵥ v) j * starRingEnd ℂ (M j r) * starRingEnd ℂ (σ r) *
          starRingEnd ℂ (∑ i, u i * ((varProf D N θ i j : ℝ) : ℂ) * M r i) := by
  have hτ : ∀ a b, (N : ℂ)⁻¹ * ∑ r, M r a * M b r * (star (tiltV D N θ u r) ⬝ᵥ (M *ᵥ v)) =
      ∑ r, M r a * M b r * σ r := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hσ, ← FIO_tilt_dot]
    ring
  unfold FIO_T2 FIO_der
  simp only [hτ]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_sub, map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun r i => (M *ᵥ v) j * starRingEnd ℂ (M j r) * starRingEnd ℂ (σ r) *
      (starRingEnd ℂ (u i) * ((varProf D N θ i j : ℝ) : ℂ) * starRingEnd ℂ (M r i)))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun r _ => ?_
    ring

/-- The double-sum bound `|Σ_{j,r} a_j b_{jr} c_r e_{jr}| ≤ K² A B` for `|c_r|, |e_{jr}| ≤ K`,
`Σ_j |a_j| ≤ A`, `Σ_r |b_{jr}| ≤ B`. -/
private lemma FIO_dsum_le {ι : Type*} [Fintype ι] (a c : ι → ℂ) (b e : ι → ι → ℂ)
    (A B K : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (ha : ∑ j, ‖a j‖ ≤ A) (hb : ∀ j, ∑ r, ‖b j r‖ ≤ B)
    (hc : ∀ r, ‖c r‖ ≤ K) (he : ∀ j r, ‖e j r‖ ≤ K) :
    ‖∑ j, ∑ r, a j * b j r * c r * e j r‖ ≤ K ^ 2 * A * B := by
  calc ‖∑ j, ∑ r, a j * b j r * c r * e j r‖ ≤ ∑ j, ∑ r, ‖a j‖ * ‖b j r‖ * (K * K) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, mul_assoc (‖a j‖ * ‖b j r‖)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hc r) (he j r) (norm_nonneg _) hK)
          (by positivity)
    _ = ∑ j, ‖a j‖ * (∑ r, ‖b j r‖) * (K * K) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ j, ‖a j‖ * B * (K * K) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb j) (norm_nonneg _))
          (by positivity)
    _ = (∑ j, ‖a j‖) * B * (K * K) := by rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ A * B * (K * K) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha hB) (by positivity)
    _ = K ^ 2 * A * B := by ring

/-- The bounds on `T₁` and `T₂` from Ward-type bounds `Σ |(M v)_k|², Σ_r |M_{rj}|²,
Σ_r |M_{jr}|² ≤ N ζ²`, the forms `|t^r(u)^* M v|, |t^j(u)^* M e_r|, |e_r^* M t^j(u)| ≤ Γ`,
`|(H̲G)_{u e_j}| ≤ λ` and `|(H̲G)_{u t^j(u)}| ≤ L`:
`|T₁| ≤ ζ² + √D Γ λ ζ + D Γ² ζ²`, `|T₂| ≤ ζ² + L ζ² + D Γ² ζ²`. -/
private lemma FIO_T_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN : 0 < N)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1)
    (M : Matrix (Idx D N) (Idx D N) ℂ) (ζ Γ lb L : ℝ) (hζ : 0 ≤ ζ) (hΓ : 0 ≤ Γ) (hlb : 0 ≤ lb)
    (hL : 0 ≤ L)
    (hW1 : ∑ k, ‖(M *ᵥ v) k‖ ^ 2 ≤ N * ζ ^ 2)
    (hW2 : ∀ j, ∑ r, ‖M r j‖ ^ 2 ≤ N * ζ ^ 2)
    (hW3 : ∀ j, ∑ r, ‖M j r‖ ^ 2 ≤ N * ζ ^ 2)
    (hF1 : ∀ r, ‖star (tiltV D N θ u r) ⬝ᵥ (M *ᵥ v)‖ ≤ Γ)
    (hF2 : ∀ j r, ‖star (tiltV D N θ u j) ⬝ᵥ (M *ᵥ Pi.single r 1)‖ ≤ Γ)
    (hF3 : ∀ j r, ‖(M *ᵥ tiltV D N θ u j) r‖ ≤ Γ)
    (hL1 : ∀ j, ‖FIO_d D N θ Λ z u M (Pi.single j 1)‖ ≤ lb)
    (hL2 : ∀ j, ‖FIO_d D N θ Λ z u M (tiltV D N θ u j)‖ ≤ L) :
    ‖FIO_T1 D N θ Λ z u v M‖ ≤ ζ ^ 2 + Real.sqrt D * Γ * lb * ζ + D * Γ ^ 2 * ζ ^ 2 ∧
      ‖FIO_T2 D N θ Λ z u v M‖ ≤ ζ ^ 2 + L * ζ ^ 2 + D * Γ ^ 2 * ζ ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnN : ‖((N : ℂ))⁻¹‖ = (N : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hsD := Real.sqrt_nonneg (D : ℝ)
  set s : Idx D N → Idx D N → ℂ := fun i j => ((varProf D N θ i j : ℝ) : ℂ) with hs
  have hsn : ∀ i j, ‖s i j‖ ≤ (N : ℝ)⁻¹ := fun i j => by
    rw [hs, Complex.norm_real, Real.norm_of_nonneg (FIO_prof_le D N θ hθ0 hθ1 i j).1]
    exact (FIO_prof_le D N θ hθ0 hθ1 i j).2
  set w := M *ᵥ v with hw
  set σ : Idx D N → ℂ := fun r => ∑ i, starRingEnd ℂ (u i) * s i r * w i with hσ
  -- the sums of the tilted vectors
  have hσΓ : ∀ r, ‖σ r‖ ≤ Γ / N := fun r => by
    have e : σ r = (N : ℂ)⁻¹ * (star (tiltV D N θ u r) ⬝ᵥ w) := (FIO_tilt_dot D N θ u w r).symm
    rw [e, norm_mul, hnN, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hF1 r) (by positivity)
  have hω : ∀ j r, ‖∑ i, starRingEnd ℂ (u i) * s i j * M i r‖ ≤ Γ / N := fun j r => by
    have e : ∑ i, starRingEnd ℂ (u i) * s i j * M i r =
        (N : ℂ)⁻¹ * (star (tiltV D N θ u j) ⬝ᵥ (M *ᵥ Pi.single r 1)) := by
      rw [FIO_tilt_dot]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_single_one]
      rfl
    rw [e, norm_mul, hnN, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hF2 j r) (by positivity)
  have hπ : ∀ j r, ‖∑ i, u i * s i j * M r i‖ ≤ Γ / N := fun j r => by
    have e : ∑ i, u i * s i j * M r i = (N : ℂ)⁻¹ * (M *ᵥ tiltV D N θ u j) r := by
      rw [← FIO_tilt_dot' D N θ u (fun i => M r i) j]
      rfl
    rw [e, norm_mul, hnN, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hF3 j r) (by positivity)
  have hκ : ∀ j, ‖∑ i, u i * s i j * FIO_d D N θ Λ z u M (Pi.single i 1)‖ ≤ L / N := fun j => by
    have e : ∑ i, u i * s i j * FIO_d D N θ Λ z u M (Pi.single i 1) =
        (N : ℂ)⁻¹ * FIO_d D N θ Λ z u M (tiltV D N θ u j) := by
      rw [← FIO_tilt_dot' D N θ u (fun i => FIO_d D N θ Λ z u M (Pi.single i 1)) j]
      unfold FIO_d
      rw [FIO_form_sum]
    rw [e, norm_mul, hnN, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hL2 j) (by positivity)
  -- the `ℓ¹` bounds
  have hSV : ∑ j, ‖w j‖ ≤ N * Real.sqrt D * ζ :=
    FIO_l1_le D N (fun j => ‖w j‖) ζ hζ (fun _ => norm_nonneg _) hW1
  have hSC : ∀ j, ∑ r, ‖M r j‖ ≤ N * Real.sqrt D * ζ := fun j =>
    FIO_l1_le D N (fun r => ‖M r j‖) ζ hζ (fun _ => norm_nonneg _) (hW2 j)
  have hSR : ∀ j, ∑ r, ‖starRingEnd ℂ (M j r)‖ ≤ N * Real.sqrt D * ζ := fun j => by
    simp only [Complex.norm_conj]
    exact FIO_l1_le D N (fun r => ‖M j r‖) ζ hζ (fun _ => norm_nonneg _) (hW3 j)
  have hS2 : (∑ i, ‖u i‖ * ‖w i‖) ^ 2 ≤ N * ζ ^ 2 := by
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    have h0 : 0 ≤ ∑ i, ‖w i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    calc (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖w i‖ ^ 2 ≤ 1 * ∑ i, ‖w i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hu h0
      _ ≤ N * ζ ^ 2 := by rw [one_mul]; exact hW1
  have hσS : ∀ j, ‖σ j‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖u i‖ * ‖w i‖ := fun j => by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := hsn i j
    calc ‖u i‖ * ‖s i j‖ * ‖w i‖ ≤ ‖u i‖ * (N : ℝ)⁻¹ * ‖w i‖ := by gcongr
      _ = _ := by ring
  have hND : (N : ℝ) * Real.sqrt D * ζ * ((N : ℝ) * Real.sqrt D * ζ) = N ^ 2 * (D * ζ ^ 2) := by
    have e : (N : ℝ) * Real.sqrt D * ζ * ((N : ℝ) * Real.sqrt D * ζ) =
        N ^ 2 * (Real.sqrt D ^ 2 * ζ ^ 2) := by ring
    rw [e, Real.sq_sqrt hD0]
  -- `T₁`
  refine ⟨?_, ?_⟩
  · rw [FIO_T1_eq D N θ Λ z u v M σ fun r => rfl]
    have hA : ‖∑ j, w j * (starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)) * σ j‖ ≤
        ζ ^ 2 + Real.sqrt D * Γ * lb * ζ := by
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∀ j, ‖w j * (starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)) * σ j‖ ≤
          ‖w j‖ * ‖u j‖ * ((N : ℝ)⁻¹ * ∑ i, ‖u i‖ * ‖w i‖) + ‖w j‖ * lb * (Γ / N) := fun j => by
        rw [norm_mul, norm_mul]
        have h2 : ‖starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)‖ ≤ ‖u j‖ + lb :=
          (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith [hL1 j])
        calc ‖w j‖ * ‖starRingEnd ℂ (u j) - FIO_d D N θ Λ z u M (Pi.single j 1)‖ * ‖σ j‖
            ≤ ‖w j‖ * (‖u j‖ + lb) * ‖σ j‖ := by gcongr
          _ = ‖w j‖ * ‖u j‖ * ‖σ j‖ + ‖w j‖ * lb * ‖σ j‖ := by ring
          _ ≤ _ := by gcongr; exacts [hσS j, hσΓ j]
      refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      have e1 : (∑ j, ‖w j‖ * ‖u j‖) = ∑ i, ‖u i‖ * ‖w i‖ :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [e1]
      have h3 : (∑ i, ‖u i‖ * ‖w i‖) * ((N : ℝ)⁻¹ * ∑ i, ‖u i‖ * ‖w i‖) ≤ ζ ^ 2 := by
        rw [← mul_assoc, mul_comm _ (N : ℝ)⁻¹, mul_assoc, ← sq]
        calc (N : ℝ)⁻¹ * (∑ i, ‖u i‖ * ‖w i‖) ^ 2 ≤ (N : ℝ)⁻¹ * (N * ζ ^ 2) :=
              mul_le_mul_of_nonneg_left hS2 (by positivity)
          _ = ζ ^ 2 := by field_simp
      have h4 : (∑ j, ‖w j‖) * lb * (Γ / N) ≤ Real.sqrt D * Γ * lb * ζ := by
        calc (∑ j, ‖w j‖) * lb * (Γ / N) ≤ (N * Real.sqrt D * ζ) * lb * (Γ / N) := by gcongr
          _ = Real.sqrt D * Γ * lb * ζ := by field_simp
      linarith
    have hB : ‖∑ j, ∑ r, w j * M r j * σ r *
        (∑ i, starRingEnd ℂ (u i) * s i j * M i r)‖ ≤ D * Γ ^ 2 * ζ ^ 2 := by
      refine (FIO_dsum_le w σ (fun j r => M r j)
        (fun j r => ∑ i, starRingEnd ℂ (u i) * s i j * M i r) _ _ (Γ / N) (by positivity)
        (by positivity) hSV hSC (fun r => hσΓ r) hω).trans (le_of_eq ?_)
      rw [div_pow, mul_assoc (Γ ^ 2 / (N : ℝ) ^ 2), hND]
      field_simp
    exact (norm_sub_le _ _).trans (by linarith)
  -- `T₂`
  · rw [FIO_T2_eq D N θ Λ z u v M σ fun r => rfl]
    have hA : ‖∑ j, w j * starRingEnd ℂ (w j) *
        ((∑ i, starRingEnd ℂ (u i) * s i j * u i) -
          starRingEnd ℂ (∑ i, u i * s i j * FIO_d D N θ Λ z u M (Pi.single i 1)))‖ ≤
        ζ ^ 2 + L * ζ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∀ j, ‖w j * starRingEnd ℂ (w j) *
          ((∑ i, starRingEnd ℂ (u i) * s i j * u i) -
            starRingEnd ℂ (∑ i, u i * s i j * FIO_d D N θ Λ z u M (Pi.single i 1)))‖ ≤
          ‖w j‖ ^ 2 * ((N : ℝ)⁻¹ + L / N) := fun j => by
        rw [norm_mul, norm_mul, Complex.norm_conj, ← sq]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
          (by positivity)
        · refine (norm_sum_le _ _).trans ?_
          calc ∑ i, ‖starRingEnd ℂ (u i) * s i j * u i‖ ≤ ∑ i, (N : ℝ)⁻¹ * ‖u i‖ ^ 2 :=
                Finset.sum_le_sum fun i _ => by
                  rw [norm_mul, norm_mul, Complex.norm_conj]
                  have := hsn i j
                  calc ‖u i‖ * ‖s i j‖ * ‖u i‖ ≤ ‖u i‖ * (N : ℝ)⁻¹ * ‖u i‖ := by gcongr
                    _ = _ := by ring
            _ = (N : ℝ)⁻¹ * ∑ i, ‖u i‖ ^ 2 := by rw [Finset.mul_sum]
            _ ≤ (N : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hu (by positivity)
            _ = (N : ℝ)⁻¹ := mul_one _
        · rw [Complex.norm_conj]
          exact hκ j
      refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
      rw [← Finset.sum_mul]
      calc (∑ j, ‖w j‖ ^ 2) * ((N : ℝ)⁻¹ + L / N) ≤ (N * ζ ^ 2) * ((N : ℝ)⁻¹ + L / N) :=
            mul_le_mul_of_nonneg_right hW1 (by positivity)
        _ = ζ ^ 2 + L * ζ ^ 2 := by field_simp
    have hB : ‖∑ j, ∑ r, w j * starRingEnd ℂ (M j r) * starRingEnd ℂ (σ r) *
        starRingEnd ℂ (∑ i, u i * s i j * M r i)‖ ≤ D * Γ ^ 2 * ζ ^ 2 := by
      refine (FIO_dsum_le w (fun r => starRingEnd ℂ (σ r)) (fun j r => starRingEnd ℂ (M j r))
        (fun j r => starRingEnd ℂ (∑ i, u i * s i j * M r i)) _ _ (Γ / N) (by positivity)
        (by positivity) hSV hSR (fun r => by rw [Complex.norm_conj]; exact hσΓ r)
        (fun j r => by rw [Complex.norm_conj]; exact hπ j r)).trans (le_of_eq ?_)
      rw [div_pow, mul_assoc (Γ ^ 2 / (N : ℝ) ^ 2), hND]
      field_simp
    exact (norm_sub_le _ _).trans (by linarith)

/-- `|FIO_R| ≤ 2p |𝒟|^{2p-2} X` when `|T₁|, |T₂| ≤ X` and `p ≥ 1`. -/
private lemma FIO_R_le (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (hp : 1 ≤ p) (M : Matrix (Idx D N) (Idx D N) ℂ) (X : ℝ)
    (h1 : ‖FIO_T1 D N θ Λ z u v M‖ ≤ X) (h2 : ‖FIO_T2 D N θ Λ z u v M‖ ≤ X) :
    ‖FIO_R D N θ Λ z u v p M‖ ≤ 2 * p * ‖FIO_d D N θ Λ z u M v‖ ^ (2 * p - 2) * X := by
  set A := ‖FIO_d D N θ Λ z u M v‖ with hA
  have hX : 0 ≤ X := (norm_nonneg _).trans h1
  have hA0 : 0 ≤ A := norm_nonneg _
  unfold FIO_R
  refine (norm_add_le _ _).trans ?_
  have e2 : ‖(p : ℂ) * FIO_d D N θ Λ z u M v ^ (p - 1) *
      starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ (p - 1) * FIO_T2 D N θ Λ z u v M‖ =
      p * A ^ (2 * p - 2) * ‖FIO_T2 D N θ Λ z u v M‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_natCast,
      ← hA, mul_assoc (p : ℝ), ← pow_add]
    congr 3
    omega
  have e1 : ‖((p - 1 : ℕ) : ℂ) * FIO_d D N θ Λ z u M v ^ (p - 2) *
      starRingEnd ℂ (FIO_d D N θ Λ z u M v) ^ p * FIO_T1 D N θ Λ z u v M‖ ≤
      p * A ^ (2 * p - 2) * ‖FIO_T1 D N θ Λ z u v M‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_natCast,
      ← hA]
    rcases Nat.lt_or_ge p 2 with hp2 | hp2
    · have : p - 1 = 0 := by omega
      rw [this]
      simp only [Nat.cast_zero, zero_mul]
      positivity
    · rw [mul_assoc ((p - 1 : ℕ) : ℝ), ← pow_add]
      have e : p - 2 + p = 2 * p - 2 := by omega
      rw [e]
      have : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
      gcongr
  rw [e2]
  have h3 : (p : ℝ) * A ^ (2 * p - 2) * ‖FIO_T1 D N θ Λ z u v M‖ ≤ p * A ^ (2 * p - 2) * X :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (p : ℝ) * A ^ (2 * p - 2) * ‖FIO_T2 D N θ Λ z u v M‖ ≤ p * A ^ (2 * p - 2) * X :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-! ### The remainder on the good event and off it -/

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma FIO_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (x y : ι → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤ opNorm T := by
  have e : star x ⬝ᵥ (T *ᵥ y) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 y)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hx
  have hy' : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hy
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 y) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ ≤ opNorm T * 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by unfold opNorm; gcongr)
  rw [e, h1]
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (opNorm T * 1) := mul_le_mul hx' h2 (norm_nonneg _) zero_le_one
    _ = opNorm T := by ring

/-- `e_k^* w = w_k`. -/
private lemma FIO_single_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) (w : ι → ℂ) :
    star (Pi.single k (1 : ℂ)) ⬝ᵥ w = w k := by
  have : star (Pi.single k (1 : ℂ) : ι → ℂ) = Pi.single k 1 := by
    funext r
    by_cases h : r = k <;> simp [h]
  rw [this, single_one_dotProduct]

/-- The standard basis vectors have norm `1`. -/
private lemma FIO_single_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    ∑ k', ‖(Pi.single k (1 : ℂ) : ι → ℂ) k'‖ ^ 2 = 1 := by
  have : ∀ k' : ι, ‖(Pi.single k (1 : ℂ) : ι → ℂ) k'‖ ^ 2 = if k' = k then 1 else 0 := by
    intro k'
    by_cases h : k' = k <;> simp [h]
  simp [this]

/-- The tilted vectors have `|t^r(u)| ≤ |u|`, since `0 ≤ N s_{kr} ≤ 1`. -/
private lemma FIO_tilt_norm (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (r : Idx D N) : ∑ k, ‖tiltV D N θ u r k‖ ^ 2 ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hu
  have h0 := (FIO_prof_le D N θ hθ0 hθ1 k r).1
  have h1 := (FIO_prof_le D N θ hθ0 hθ1 k r).2
  have hN : (0 : ℝ) < N := by exact_mod_cast r.2.pos
  have e0 : 0 ≤ (N : ℝ) * varProf D N θ k r := by positivity
  have e1 : (N : ℝ) * varProf D N θ k r ≤ 1 := by
    calc (N : ℝ) * varProf D N θ k r ≤ N * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h1 hN.le
      _ = 1 := by field_simp
  simp only [tiltV, norm_mul, Complex.norm_real, Real.norm_of_nonneg e0]
  have : ((N : ℝ) * varProf D N θ k r) ^ 2 ≤ 1 := by nlinarith
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_left this (sq_nonneg _)).trans (le_of_eq (mul_one _))

private lemma FIO_mem_u (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) : u ∈ isoVecs D N θ Λ u v := by
  simp [isoVecs]

private lemma FIO_mem_v (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) : v ∈ isoVecs D N θ Λ u v := by
  simp [isoVecs]

private lemma FIO_mem_L (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) : Λᴴ *ᵥ u ∈ isoVecs D N θ Λ u v := by
  simp [isoVecs]

private lemma FIO_mem_E (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) (a : Fin D) : (Ea D N a)ᴴ *ᵥ u ∈ isoVecs D N θ Λ u v := by
  unfold isoVecs
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))))

private lemma FIO_mem_e (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) (k : Idx D N) : Pi.single k 1 ∈ isoVecs D N θ Λ u v := by
  unfold isoVecs
  refine Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))))

private lemma FIO_mem_t (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) (r : Idx D N) : tiltV D N θ u r ∈ isoVecs D N θ Λ u v := by
  unfold isoVecs
  exact Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ r)))

/-- The remainder on the good event: `|FIO_R(G)| ≤ 6p ζ̂ λ |(H̲G)_{uv}|^{2p-2}` with
`ζ̂ = (√D + 3)(1 + |z|) Γ³ (Υ/(Nη))^{1/2} ≤ λ`. -/
private lemma FIO_good (D N : ℕ) (hN : 0 < N) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (p : ℕ) (hp : 1 ≤ p) (Γ Υ lb : ℝ)
    (hΓ : 1 ≤ Γ) (hΥ : z.im ≤ Υ)
    (hlb : (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ≤ lb)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : h ∈ isoGood D N θ Λ z u v Γ Υ lb) :
    ‖FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z)‖ ≤
      6 * p * ((Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im))) * lb *
        ‖FIO_d D N θ Λ z u (res (Matrix.of h + Λ) z) v‖ ^ (2 * p - 2) := by
  set M := res (Matrix.of h + Λ) z with hM
  set V := isoVecs D N θ Λ u v with hV
  have hHΛ : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  obtain ⟨hG, hD⟩ := hg
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set ζ := Real.sqrt (Υ / ((N : ℝ) * z.im)) with hζ
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  have hΥ0 : 0 ≤ Υ := hz.le.trans hΥ
  have hζ2 : (N : ℝ) * ζ ^ 2 = Υ / z.im := by
    rw [hζ, Real.sq_sqrt (by positivity)]
    field_simp
  have hΓ0 : 0 ≤ Γ := by linarith
  -- Ward-type bounds
  have hWv : ∀ y ∈ V, ∑ k, ‖(M *ᵥ y) k‖ ^ 2 ≤ N * ζ ^ 2 := fun y hy => by
    rw [hζ2, hM, ward_vec _ hHΛ z hz y]
    exact div_le_div_of_nonneg_right (hG y hy y hy).2 hz.le
  have hdiag : ∀ j, (M j j).im ≤ Υ := fun j => by
    have := (hG _ (FIO_mem_e D N θ Λ u v j) _ (FIO_mem_e D N θ Λ u v j)).2
    rwa [FIO_single_dot, Matrix.mulVec_single_one] at this
  have hW2 : ∀ j, ∑ r, ‖M r j‖ ^ 2 ≤ N * ζ ^ 2 := fun j => by
    rw [hζ2, hM, (ward_diag _ hHΛ z hz j).1]
    exact div_le_div_of_nonneg_right (hdiag j) hz.le
  have hW3 : ∀ j, ∑ r, ‖M j r‖ ^ 2 ≤ N * ζ ^ 2 := fun j => by
    rw [hζ2, hM, (ward_diag _ hHΛ z hz j).2]
    exact div_le_div_of_nonneg_right (hdiag j) hz.le
  -- the forms
  have hF1 : ∀ r, ‖star (tiltV D N θ u r) ⬝ᵥ (M *ᵥ v)‖ ≤ Γ := fun r =>
    (hG _ (FIO_mem_t D N θ Λ u v r) _ (FIO_mem_v D N θ Λ u v)).1
  have hF2 : ∀ j r, ‖star (tiltV D N θ u j) ⬝ᵥ (M *ᵥ Pi.single r 1)‖ ≤ Γ := fun j r =>
    (hG _ (FIO_mem_t D N θ Λ u v j) _ (FIO_mem_e D N θ Λ u v r)).1
  have hF3 : ∀ j r, ‖(M *ᵥ tiltV D N θ u j) r‖ ≤ Γ := fun j r => by
    have := (hG _ (FIO_mem_e D N θ Λ u v r) _ (FIO_mem_t D N θ Λ u v j)).1
    rwa [FIO_single_dot] at this
  have hL1 : ∀ j, ‖FIO_d D N θ Λ z u M (Pi.single j 1)‖ ≤ lb := fun j => by
    rw [hM, ← FIO_d_eq D N θ Λ hΛ z hz h hh]
    exact hD _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  -- the bound on `(H̲G)_{u t^j(u)}` from its resolvent-polynomial form
  have hL2 : ∀ j, ‖FIO_d D N θ Λ z u M (tiltV D N θ u j)‖ ≤
      ((D : ℝ) + 3) * (1 + ‖z‖) * Γ ^ 2 := fun j => by
    obtain ⟨P, hP, hwt, hev⟩ := hgUnder_resPoly D N θ hθ0 hθ1 Λ hΛ z hz u (tiltV D N θ u j) hu
      (FIO_tilt_norm D N θ hθ0 hθ1 u hu j)
    have hΞ : ∀ q ∈ ({(Λ, z)} : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
        q.1.IsHermitian ∧ q.2.im ≠ 0 := by
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨hΛ, hz.ne'⟩
    have hP' : ∀ t ∈ P, t.2.length ≤ 2 ∧ ∀ f ∈ t.2, f.1 ∈ (↑V : Set (Idx D N → ℂ)) ∧
        f.2.1 ∈ (↑V : Set (Idx D N → ℂ)) ∧
        f.2.2 ∈ ({(Λ, z)} : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)) := by
      intro t ht
      refine ⟨(hP t ht).1, fun f hf => ?_⟩
      obtain ⟨h1, h2, h3⟩ := (hP t ht).2 f hf
      refine ⟨?_, ?_, by rw [h3]; rfl⟩
      · rcases h1 with e | e | ⟨a, e⟩ | ⟨k, e⟩ <;> rw [e]
        · exact FIO_mem_u D N θ Λ u v
        · exact FIO_mem_L D N θ Λ u v
        · exact FIO_mem_E D N θ Λ u v a
        · exact FIO_mem_e D N θ Λ u v k
      · rcases h2 with e | ⟨k, e⟩ <;> rw [e]
        · exact FIO_mem_t D N θ Λ u v j
        · exact FIO_mem_e D N θ Λ u v k
    have hGb : ∀ q ∈ ({(Λ, z)} : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
        ∀ x ∈ (↑V : Set (Idx D N → ℂ)), ∀ y ∈ (↑V : Set (Idx D N → ℂ)),
        ‖resFactorEval (x, y, q.1, q.2) (setEntry h j j (h j j))‖ ≤ Γ := by
      intro q hq x hx y hy
      rw [Set.mem_singleton_iff] at hq
      subst hq
      rw [FIO_setEntry_self h hh]
      exact (hG x hx y hy).1
    have hb := resPoly_wirt_le h hh j j (↑V) _ (FIO_mem_e D N θ Λ u v j)
      (FIO_mem_e D N θ Λ u v j) hΞ P 2 hP' Γ hΓ (h j j) hGb 0 0
    simp only [wirt, Function.iterate_zero, id, FIO_setEntry_self h hh, add_zero, pow_zero,
      one_mul] at hb
    rw [hev h hh, FIO_d_eq D N θ Λ hΛ z hz h hh] at hb
    refine hb.trans (mul_le_mul_of_nonneg_right hwt (by positivity))
  have hlb0 : 0 ≤ lb := (by positivity : (0 : ℝ) ≤ (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 *
    Real.sqrt (Υ / ((N : ℝ) * z.im))).trans hlb
  have hL0 : 0 ≤ ((D : ℝ) + 3) * (1 + ‖z‖) * Γ ^ 2 := by positivity
  obtain ⟨hT1, hT2⟩ := FIO_T_le D N θ hθ0 hθ1 hN Λ z u v hu M ζ Γ lb _ hζ0 hΓ0 hlb0 hL0
    (hWv v (FIO_mem_v D N θ Λ u v)) hW2 hW3 hF1 hF2 hF3 hL1 hL2
  -- the normalization by `ζ̂ λ`
  set c := Real.sqrt D + 3 with hc
  set zh := c * (1 + ‖z‖) * Γ ^ 3 * ζ with hzh
  have hsD := Real.sqrt_nonneg (D : ℝ)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hc3 : 3 ≤ c := by rw [hc]; linarith
  have hz1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hΓ3 : Γ ≤ Γ ^ 3 := by nlinarith
  have hΓ2 : Γ ^ 2 ≤ Γ ^ 3 := by nlinarith
  have hΓ1 : 1 ≤ Γ ^ 3 := by nlinarith
  have hzΓ : 1 ≤ (1 + ‖z‖) * Γ ^ 3 := one_le_mul_of_one_le_of_one_le hz1 hΓ1
  have hc1 : c ≤ c * (1 + ‖z‖) * Γ ^ 3 := by
    rw [mul_assoc]
    exact le_mul_of_one_le_right (by linarith) hzΓ
  have hcwΓ : 1 ≤ c * (1 + ‖z‖) * Γ ^ 3 := by linarith
  have hzh0 : 0 ≤ zh := by positivity
  have hζzh : ζ ≤ zh := by
    rw [hzh]
    nlinarith
  have hzhlb : zh ≤ lb := hlb
  have h1 : ζ ^ 2 ≤ zh * lb := by
    rw [sq]
    exact mul_le_mul hζzh (hζzh.trans hzhlb) hζ0 hzh0
  have hDζ : Real.sqrt D * Γ * ζ ≤ zh := by
    rw [hzh]
    have e1 : Real.sqrt D ≤ c := by rw [hc]; linarith
    have e2 : Real.sqrt D * Γ ≤ c * (1 + ‖z‖) * Γ ^ 3 := by
      calc Real.sqrt D * Γ ≤ c * Γ ^ 3 := mul_le_mul e1 hΓ3 hΓ0 (by linarith)
        _ ≤ c * (1 + ‖z‖) * Γ ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right e2 hζ0
  have h2 : Real.sqrt D * Γ * lb * ζ ≤ zh * lb := by
    calc Real.sqrt D * Γ * lb * ζ = Real.sqrt D * Γ * ζ * lb := by ring
      _ ≤ zh * lb := mul_le_mul_of_nonneg_right hDζ hlb0
  have h3 : (D : ℝ) * Γ ^ 2 * ζ ^ 2 ≤ zh * lb := by
    have e : (D : ℝ) * Γ ^ 2 * ζ ^ 2 = (Real.sqrt D * Γ * ζ) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hD0]
    rw [e, sq]
    have h0 : 0 ≤ Real.sqrt D * Γ * ζ := by positivity
    exact mul_le_mul hDζ (hDζ.trans hzhlb) h0 hzh0
  have h4 : ((D : ℝ) + 3) * (1 + ‖z‖) * Γ ^ 2 * ζ ^ 2 ≤ zh * lb := by
    have e1 : (D : ℝ) + 3 ≤ c ^ 2 := by
      rw [hc]
      nlinarith [Real.sq_sqrt hD0]
    have e2 : c * (1 + ‖z‖) * Γ ^ 2 * ζ ≤ zh := by
      rw [hzh]
      have : c * (1 + ‖z‖) * Γ ^ 2 ≤ c * (1 + ‖z‖) * Γ ^ 3 :=
        mul_le_mul_of_nonneg_left hΓ2 (by positivity)
      exact mul_le_mul_of_nonneg_right this hζ0
    have e3 : c * ζ ≤ zh := by
      rw [hzh]
      exact mul_le_mul_of_nonneg_right hc1 hζ0
    calc ((D : ℝ) + 3) * (1 + ‖z‖) * Γ ^ 2 * ζ ^ 2 ≤ c ^ 2 * (1 + ‖z‖) * Γ ^ 2 * ζ ^ 2 := by
          gcongr
      _ = (c * (1 + ‖z‖) * Γ ^ 2 * ζ) * (c * ζ) := by ring
      _ ≤ zh * lb := mul_le_mul e2 (e3.trans hzhlb) (by positivity) hzh0
  have hX1 : ‖FIO_T1 D N θ Λ z u v M‖ ≤ 3 * (zh * lb) := by linarith
  have hX2 : ‖FIO_T2 D N θ Λ z u v M‖ ≤ 3 * (zh * lb) := by
    have : (((D : ℝ) + 3) * (1 + ‖z‖) * Γ ^ 2) * ζ ^ 2 ≤ zh * lb := h4
    linarith
  have hR := FIO_R_le D N θ Λ z u v p hp M _ hX1 hX2
  calc ‖FIO_R D N θ Λ z u v p M‖ ≤ 2 * p * ‖FIO_d D N θ Λ z u M v‖ ^ (2 * p - 2) *
        (3 * (zh * lb)) := hR
    _ = 6 * p * zh * lb * ‖FIO_d D N θ Λ z u M v‖ ^ (2 * p - 2) := by ring

/-- The remainder off the good event, deterministically on Hermitian arrays (`η ≥ N⁻¹`,
`|z| ≤ N^{1/9}`, `‖Λ‖ ≤ 1/10`): `|FIO_R(G)| ≤ 2p 4^{2p-2} (5 + 4√D + D) N^{4p}`. -/
private lemma FIO_bad (D N : ℕ) (hN : 0 < N) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10) (z : ℂ)
    (hzN : ((N : ℝ))⁻¹ ≤ z.im) (hzn : ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9)) (u v : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (p : ℕ) (hp : 1 ≤ p)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ‖FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z)‖ ≤
      2 * p * 4 ^ (2 * p - 2) * (5 + 4 * Real.sqrt D + D) * (N : ℝ) ^ (4 * p) := by
  set M := res (Matrix.of h + Λ) z with hM
  have hHΛ : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 0 < z.im := (inv_pos.mpr hNr).trans_le hzN
  have hηN : z.im⁻¹ ≤ N := inv_le_of_inv_le₀ hNr hzN
  have hMn : opNorm M ≤ N := (opNorm_res_le _ hHΛ z hz).trans hηN
  have hform : ∀ x y : Idx D N → ℂ, ∑ k, ‖x k‖ ^ 2 ≤ 1 → ∑ k, ‖y k‖ ^ 2 ≤ 1 →
      ‖star x ⬝ᵥ (M *ᵥ y)‖ ≤ N := fun x y hx hy => (FIO_form_le M x y hx hy).trans hMn
  have hzN' : ‖z‖ ≤ N := by
    refine hzn.trans ?_
    calc (N : ℝ) ^ ((1 : ℝ) / 9) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hB : ∀ y : Idx D N → ℂ, ∑ k, ‖y k‖ ^ 2 ≤ 1 →
      ‖FIO_d D N θ Λ z u M y‖ ≤ 4 * (N : ℝ) ^ 2 := fun y hy => by
    rw [hM, ← FIO_d_eq D N θ Λ hΛ z hz h hh]
    refine (hgUnder_form_le D N θ hθ0 hθ1 _ Λ hh hΛ z hz u y hu hy).trans ?_
    have hi0 : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hz.le
    have e1 : (opNorm Λ + ‖z‖) / z.im ≤ 2 * (N : ℝ) ^ 2 := by
      rw [div_eq_mul_inv]
      calc (opNorm Λ + ‖z‖) * z.im⁻¹ ≤ (N + N) * N := by
            refine mul_le_mul (add_le_add (by linarith) hzN') hηN hi0 (by positivity)
        _ = 2 * (N : ℝ) ^ 2 := by ring
    have e2 : 1 / z.im ^ 2 ≤ (N : ℝ) ^ 2 := by
      rw [one_div, ← inv_pow]
      exact pow_le_pow_left₀ hi0 hηN 2
    have e3 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    linarith
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
  have hWv : ∑ k, ‖(M *ᵥ v) k‖ ^ 2 ≤ N * Real.sqrt N ^ 2 := by
    rw [hsN, hM, ward_vec _ hHΛ z hz v, div_eq_mul_inv]
    have h1 := (Complex.im_le_norm _).trans (hform v v hv hv)
    calc (star v ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ v)).im * z.im⁻¹ ≤ N * N :=
          mul_le_mul h1 hηN (inv_nonneg.mpr hz.le) hNr.le
      _ = N * N := rfl
  have hdiag : ∀ j, (M j j).im * z.im⁻¹ ≤ N * N := fun j =>
    mul_le_mul ((Complex.im_le_norm _).trans ((norm_apply_le_opNorm M j j).trans hMn)) hηN
      (inv_nonneg.mpr hz.le) hNr.le
  have hW2 : ∀ j, ∑ r, ‖M r j‖ ^ 2 ≤ N * Real.sqrt N ^ 2 := fun j => by
    rw [hsN, hM, (ward_diag _ hHΛ z hz j).1, div_eq_mul_inv]
    exact hdiag j
  have hW3 : ∀ j, ∑ r, ‖M j r‖ ^ 2 ≤ N * Real.sqrt N ^ 2 := fun j => by
    rw [hsN, hM, (ward_diag _ hHΛ z hz j).2, div_eq_mul_inv]
    exact hdiag j
  have ht := FIO_tilt_norm D N θ hθ0 hθ1 u hu
  have hF1 : ∀ r, ‖star (tiltV D N θ u r) ⬝ᵥ (M *ᵥ v)‖ ≤ N := fun r => hform _ _ (ht r) hv
  have hF2 : ∀ j r, ‖star (tiltV D N θ u j) ⬝ᵥ (M *ᵥ Pi.single r 1)‖ ≤ N := fun j r =>
    hform _ _ (ht j) (FIO_single_norm r).le
  have hF3 : ∀ j r, ‖(M *ᵥ tiltV D N θ u j) r‖ ≤ N := fun j r => by
    have := hform _ _ (FIO_single_norm r).le (ht j)
    rwa [FIO_single_dot] at this
  obtain ⟨hT1, hT2⟩ := FIO_T_le D N θ hθ0 hθ1 hN Λ z u v hu M (Real.sqrt N) N (4 * (N : ℝ) ^ 2)
    (4 * (N : ℝ) ^ 2) (Real.sqrt_nonneg _) hNr.le (by positivity) (by positivity) hWv hW2 hW3
    hF1 hF2 hF3 (fun j => hB _ (FIO_single_norm j).le) (fun j => hB _ (ht j))
  have hsD := Real.sqrt_nonneg (D : ℝ)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hsle : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left hNr.le]
    nlinarith
  have hN2 : (N : ℝ) ≤ N ^ 2 := by nlinarith
  have hN3 : (N : ℝ) ^ 2 ≤ N ^ 3 := by nlinarith
  have hN4 : (N : ℝ) ^ 3 ≤ N ^ 4 := by nlinarith
  set X := (5 + 4 * Real.sqrt D + D) * (N : ℝ) ^ 4 with hX
  have hX1 : ‖FIO_T1 D N θ Λ z u v M‖ ≤ X := by
    refine hT1.trans ?_
    rw [hsN]
    have e : Real.sqrt D * N * (4 * N ^ 2) * Real.sqrt N ≤ 4 * Real.sqrt D * N ^ 4 := by
      have : Real.sqrt D * N * (4 * N ^ 2) * Real.sqrt N ≤ Real.sqrt D * N * (4 * N ^ 2) * N :=
        mul_le_mul_of_nonneg_left hsle (by positivity)
      nlinarith
    have e2 : (D : ℝ) * N ^ 2 * N ≤ D * N ^ 4 := by
      have : (N : ℝ) ^ 2 * N = N ^ 3 := by ring
      rw [mul_assoc, this]
      exact mul_le_mul_of_nonneg_left hN4 hD0
    rw [hX]
    nlinarith
  have hX2 : ‖FIO_T2 D N θ Λ z u v M‖ ≤ X := by
    refine hT2.trans ?_
    rw [hsN]
    have e2 : (D : ℝ) * N ^ 2 * N ≤ D * N ^ 4 := by
      have : (N : ℝ) ^ 2 * N = N ^ 3 := by ring
      rw [mul_assoc, this]
      exact mul_le_mul_of_nonneg_left hN4 hD0
    have e3 : 4 * (N : ℝ) ^ 2 * N ≤ 4 * N ^ 4 := by nlinarith
    rw [hX]
    nlinarith
  have hR := FIO_R_le D N θ Λ z u v p hp M X hX1 hX2
  have hA : ‖FIO_d D N θ Λ z u M v‖ ^ (2 * p - 2) ≤ (4 * (N : ℝ) ^ 2) ^ (2 * p - 2) :=
    pow_le_pow_left₀ (norm_nonneg _) (hB v hv) _
  have e : (4 * (N : ℝ) ^ 2) ^ (2 * p - 2) * N ^ 4 = 4 ^ (2 * p - 2) * N ^ (4 * p) := by
    rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
    congr 2
    omega
  have hX0 : 0 ≤ X := by positivity
  calc ‖FIO_R D N θ Λ z u v p M‖ ≤ 2 * p * ‖FIO_d D N θ Λ z u M v‖ ^ (2 * p - 2) * X := hR
    _ ≤ 2 * p * (4 * (N : ℝ) ^ 2) ^ (2 * p - 2) * X := by gcongr
    _ = 2 * p * ((4 * (N : ℝ) ^ 2) ^ (2 * p - 2) * N ^ 4) * (5 + 4 * Real.sqrt D + D) := by
        rw [hX]; ring
    _ = _ := by rw [e]; ring

/-! ### The order-one part of the isotropic moment inequality -/

/-- The order-one part of the isotropic moment inequality: the second cumulants cancel
`E (S_θ(G) G)_{uv} f` exactly, and the rest is `≤ K ζ̂ λ E|(H̲G)_{uv}|^{2p-2}` plus the bad-event
term, with `ζ̂ = (√D + 3)(1 + |z|) Γ³ (Υ/(Nη))^{1/2}`. -/
theorem iso_order_one (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ u v : Idx D N → ℂ, ∑ k, ‖u k‖ ^ 2 ≤ 1 → ∑ k, ‖v k‖ ^ 2 ≤ 1 →
      ∀ Γ Υ lb ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im →
        (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ≤ lb →
        μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ≤ ENNReal.ofReal ε₀ →
        ‖isoTerm D N θ μ Λ z u v p 1 +
            ∫ h, (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) *
                res (Matrix.of h + Λ) z) *ᵥ v)) *
              (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
              starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ‖ ≤
          K * ((Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im))) * lb *
              ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ +
            K * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
  set K₂ : ℝ := 2 * p * 4 ^ (2 * p - 2) * (5 + 4 * Real.sqrt D + D) with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨max (6 * (p : ℝ)) K₂, le_max_of_le_right hK₂0, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv Γ Υ lb ε₀ hΓ1 hΓN hΥ1 _ hlb hbad
  have hprob := hμ.prob
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have : ((0 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by norm_num)
      linarith
    · exact h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 0 < z.im := (inv_pos.mpr hNr).trans_le hzN
  rw [FIO_main_eq D N C θ μ hμ hθ0 hθ1 Λ hΛ z hz u v hu hv p]
  set zh := (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) with hzh
  set E := (N : ℝ) ^ (21 * (p : ℝ) + 18) with hE
  set T := toMeasurable μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hTsub : (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ⊆ T := subset_toMeasurable _ _
  have hΓ0 : 0 ≤ Γ := by linarith
  have hzh0 : 0 ≤ zh := by positivity
  have hlb0 : 0 ≤ lb := hzh0.trans hlb
  have hE0 : 0 ≤ E := by positivity
  have hE4 : (N : ℝ) ^ (4 * p) ≤ E := by
    rw [hE, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  -- the pointwise bound: on the good event and off it
  have hpt : ∀ᵐ h ∂μ, ‖FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z)‖ ≤
      6 * p * zh * lb * ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) +
        K₂ * E * T.indicator 1 h := by
    filter_upwards [hμ.herm] with h hh
    have hA0 : 0 ≤ ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) :=
      pow_nonneg (norm_nonneg _) _
    by_cases hTh : h ∈ T
    · rw [Set.indicator_of_mem hTh, Pi.one_apply, mul_one]
      have hb := FIO_bad D N hN θ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv p hp h hh
      rw [← hK₂] at hb
      have h1 : K₂ * (N : ℝ) ^ (4 * p) ≤ K₂ * E := mul_le_mul_of_nonneg_left hE4 hK₂0
      have h2 : 0 ≤ 6 * p * zh * lb *
          ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) := by positivity
      linarith
    · rw [Set.indicator_of_notMem hTh, mul_zero, add_zero,
        FIO_d_eq D N θ Λ hΛ z hz h hh]
      have hg : h ∈ isoGood D N θ Λ z u v Γ Υ lb := by
        by_contra hc
        exact hTh (hTsub hc)
      exact FIO_good D N hN θ hθ0 hθ1 Λ hΛ z hz u v hu p hp Γ Υ lb hΓ1 hΥ1 hlb h hh hg
  have hAint : Integrable (fun h =>
      ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2)) μ :=
    (FIO_int μ hμ.herm Λ hΛ z hz (fun M => ‖FIO_d D N θ Λ z u M v‖ ^ (2 * p - 2))
      (by unfold FIO_d FIO_hg; fun_prop)).congr (by
        filter_upwards [hμ.herm] with h hh
        simp only [FIO_d_eq D N θ Λ hΛ z hz h hh])
  have hIint : Integrable (T.indicator (1 : (Idx D N → Idx D N → ℂ) → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hTm
  -- the probability of the bad event
  have hmT : μ.real T ≤ Real.sqrt ε₀ := by
    have hμT : μ T ≤ ENNReal.ofReal ε₀ := by rw [hT, measure_toMeasurable]; exact hbad
    by_cases hε : 0 ≤ ε₀
    · have h1 : μ.real T ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal hε hμT
      have h2 : μ.real T ≤ 1 := measureReal_le_one
      have h0 : 0 ≤ μ.real T := measureReal_nonneg
      rw [Real.le_sqrt h0 hε]
      nlinarith
    · push Not at hε
      rw [ENNReal.ofReal_of_nonpos hε.le] at hμT
      have : μ T = 0 := le_antisymm hμT zero_le
      rw [measureReal_def, this, ENNReal.toReal_zero]
      exact Real.sqrt_nonneg _
  have hI0 : 0 ≤ ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ :=
    integral_nonneg fun h => pow_nonneg (norm_nonneg _) _
  calc ‖∫ h, FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z) ∂μ‖
      ≤ ∫ h, ‖FIO_R D N θ Λ z u v p (res (Matrix.of h + Λ) z)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ h, (6 * p * zh * lb *
          ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) +
          K₂ * E * T.indicator 1 h) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun h => norm_nonneg _)
          ((hAint.const_mul _).add (hIint.const_mul _)) hpt
    _ = 6 * p * zh * lb *
          ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ +
        K₂ * E * μ.real T := by
        rw [integral_add (hAint.const_mul _) (hIint.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator_one hTm]
    _ ≤ max (6 * (p : ℝ)) K₂ * zh * lb *
          ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ +
        max (6 * (p : ℝ)) K₂ * E * Real.sqrt ε₀ := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _

end RBMTransitionEdge

end
