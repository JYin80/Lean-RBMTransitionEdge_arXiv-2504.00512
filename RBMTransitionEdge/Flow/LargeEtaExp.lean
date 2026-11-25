module

public import RBMTransitionEdge.Flow.FourthCumulant

@[expose] public section

/-!
# Lemma 3.7 for the law of `H_t` at large `η`

Lemma 3.7 [lemma_G_large_2] for the law of `H_t` of (4.1) [defVt], `θ = e^{-t}`, `t ∈ [0, 1]`:
(3.24) [largG_1G] and (3.25) [largG_Ex], from (3.40) [ELK] with Lemmas 3.14 [lem:fourthcumu1] and
3.15 [lem:fourthcumu2].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

section LX_util

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem LX_op_nonneg (X : Matrix ι ι ℂ) : 0 ≤ opNorm X := by
  unfold opNorm; exact norm_nonneg _

private theorem LX_op_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

private theorem LX_op_sub_le (A B : Matrix ι ι ℂ) : opNorm (A - B) ≤ opNorm A + opNorm B := by
  rw [sub_eq_add_neg]
  refine (opNorm_add_le _ _).trans (le_of_eq ?_)
  rw [show -B = (-1 : ℂ) • B by simp, opNorm_smul]; simp

private theorem LX_op_conj (X : Matrix ι ι ℂ) : opNorm Xᴴ = opNorm X := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) X)

private theorem LX_op_scal (c : ℂ) : opNorm (c • (1 : Matrix ι ι ℂ)) ≤ ‖c‖ := by
  rw [opNorm_smul]
  have := LX_op_one (ι := ι)
  nlinarith [norm_nonneg c]

/-- Approximation of products: if `X_i, Y_i` have norm at most `β ≥ 1` and `‖X_i - Y_i‖ ≤ ε`, then
the products differ by at most `len * ε * β ^ len`. -/
private theorem LX_prod_approx (β ε : ℝ) (hβ : 1 ≤ β) (hε : 0 ≤ ε) :
    ∀ l l' : List (Matrix ι ι ℂ),
      List.Forall₂ (fun X Y => opNorm X ≤ β ∧ opNorm Y ≤ β ∧ opNorm (X - Y) ≤ ε) l l' →
      opNorm l.prod ≤ β ^ l.length ∧ opNorm l'.prod ≤ β ^ l.length ∧
        opNorm (l.prod - l'.prod) ≤ l.length * ε * β ^ l.length := by
  intro l l' h
  induction h with
  | nil =>
    simp only [List.prod_nil, List.length_nil, pow_zero, Nat.cast_zero, zero_mul, sub_self]
    refine ⟨LX_op_one, LX_op_one, ?_⟩
    unfold opNorm; simp
  | @cons X Y l l' hXY _ ih =>
    obtain ⟨hX, hY, hXY⟩ := hXY
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.prod_cons, List.length_cons]
    set k := l.length
    have hβ0 : 0 ≤ β := by linarith
    have hpow : 0 ≤ β ^ k := pow_nonneg hβ0 k
    have hk : (1 : ℝ) ≤ β ^ k := one_le_pow₀ hβ
    refine ⟨?_, ?_, ?_⟩
    · calc opNorm (X * l.prod) ≤ opNorm X * opNorm l.prod := opNorm_mul_le _ _
        _ ≤ β * β ^ k := mul_le_mul hX i1 (LX_op_nonneg _) hβ0
        _ = β ^ (k + 1) := by ring
    · calc opNorm (Y * l'.prod) ≤ opNorm Y * opNorm l'.prod := opNorm_mul_le _ _
        _ ≤ β * β ^ k := mul_le_mul hY i2 (LX_op_nonneg _) hβ0
        _ = β ^ (k + 1) := by ring
    · have e : X * l.prod - Y * l'.prod = (X - Y) * l.prod + Y * (l.prod - l'.prod) := by
        rw [sub_mul, mul_sub]; abel
      rw [e]
      calc opNorm ((X - Y) * l.prod + Y * (l.prod - l'.prod))
          ≤ opNorm ((X - Y) * l.prod) + opNorm (Y * (l.prod - l'.prod)) := opNorm_add_le _ _
        _ ≤ opNorm (X - Y) * opNorm l.prod + opNorm Y * opNorm (l.prod - l'.prod) :=
            add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
        _ ≤ ε * β ^ k + β * (k * ε * β ^ k) := by
            refine add_le_add (mul_le_mul hXY i1 (LX_op_nonneg _) hε) ?_
            exact mul_le_mul hY i3 (LX_op_nonneg _) hβ0
        _ ≤ ((k + 1 : ℕ) : ℝ) * ε * β ^ (k + 1) := by
            push_cast
            have e : ((k : ℝ) + 1) * ε * β ^ (k + 1) - (ε * β ^ k + β * (k * ε * β ^ k)) =
                ε * β ^ k * (β - 1) := by ring
            have : 0 ≤ ε * β ^ k * (β - 1) :=
              mul_nonneg (mul_nonneg hε hpow) (sub_nonneg.2 hβ)
            linarith

private theorem LX_ntr_le (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [ntr, Matrix.trace]; exact LX_op_nonneg A
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => norm_apply_le_opNorm A i i
    _ = _ := by simp

end LX_util

section LX_ntr

variable {ι : Type*} [Fintype ι]

private theorem LX_ntr_add (A B : Matrix ι ι ℂ) : ntr (A + B) = ntr A + ntr B := by
  unfold ntr; rw [Matrix.trace_add, mul_add]

private theorem LX_ntr_sub (A B : Matrix ι ι ℂ) : ntr (A - B) = ntr A - ntr B := by
  unfold ntr; rw [Matrix.trace_sub, mul_sub]

private theorem LX_ntr_smul (c : ℂ) (A : Matrix ι ι ℂ) : ntr (c • A) = c * ntr A := by
  unfold ntr; rw [Matrix.trace_smul, smul_eq_mul]; ring

private theorem LX_ntr_cyc (A B : Matrix ι ι ℂ) : ntr (A * B) = ntr (B * A) := by
  unfold ntr; rw [Matrix.trace_mul_comm]

private theorem LX_ntr_one [DecidableEq ι] [Nonempty ι] : ntr (1 : Matrix ι ι ℂ) = 1 := by
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [ntr, Matrix.trace, this]

end LX_ntr

section LX_Ea

variable {D N : ℕ}

private theorem LX_Ea_mul (x a : Fin D) :
    Ea D N x * Ea D N a = if x = a then Ea D N a else 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  by_cases h : x = a
  · subst h
    simp only [↓reduceIte]
    congr 1
    funext p
    by_cases hp : p.1 = x <;> simp [hp]
  · simp only [h, ↓reduceIte]
    rw [show (0 : Matrix (Idx D N) (Idx D N) ℂ) = Matrix.diagonal fun _ => 0 by simp]
    congr 1
    funext p
    by_cases hp : p.1 = x
    · have : p.1 ≠ a := fun e => h (hp ▸ e)
      simp [hp, h]
    · simp [hp]

private theorem LX_op_Ea (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

private theorem LX_sum_Ea : ∑ y, Ea D N y = (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

private theorem LX_ntr_sum_Ea (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ y, ntr (Y * Ea D N y) = ntr Y := by
  unfold ntr
  rw [← Finset.mul_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, LX_sum_Ea, Matrix.mul_one]

private theorem LX_ntr_Ea (R : Matrix (Idx D N) (Idx D N) ℂ) (c : Fin D) :
    ntr (R * Ea D N c) = (((D : ℂ) * N))⁻¹ * ∑ i, (if i.1 = c then R i i else 0) := by
  unfold ntr Ea
  simp only [Fintype.card_prod, Fintype.card_fin, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

private theorem LX_Dntr_Ea (hN : 1 ≤ N) (y : Fin D) : (D : ℂ) * ntr (Ea D N y) = 1 := by
  have h := LX_ntr_Ea (D := D) (N := N) 1 y
  rw [Matrix.one_mul] at h
  rw [h]
  have hD0 : (D : ℂ) ≠ 0 := by have := y.pos; exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : ∑ i : Idx D N, (if i.1 = y then (1 : Matrix (Idx D N) (Idx D N) ℂ) i i else 0) = N := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.one_apply_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e]
  field_simp

/-- Replacing `M` by `diag M` does not increase the distance to a scalar multiple of `1`. -/
private theorem LX_dg_le (M : Matrix (Idx D N) (Idx D N) ℂ) (m : ℂ) :
    opNorm (diagonal (diag M) - m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤
        opNorm (M - m • 1) ∧ opNorm (diagonal (diag M)) ≤ opNorm M := by
  have e : diagonal (diag M) - m • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
      diagonal fun i => M i i - m := by
    ext i j; by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply, h]
  have hnorm : ∀ v : Idx D N → ℂ, opNorm (diagonal v) = ‖v‖ := fun v => by
    unfold opNorm; rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  constructor
  · rw [e, hnorm]
    refine (pi_norm_le_iff_of_nonneg (LX_op_nonneg _)).2 fun i => ?_
    have := norm_apply_le_opNorm (M - m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) i i
    simpa using this
  · rw [hnorm]
    refine (pi_norm_le_iff_of_nonneg (LX_op_nonneg _)).2 fun i => ?_
    exact norm_apply_le_opNorm M i i

end LX_Ea

section LX_prob

private theorem LX_int_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (f : Ω → ℂ) (hf : AEStronglyMeasurable f μ) (S : Set Ω) (Bg Bc ε : ℝ) (hBg : 0 ≤ Bg)
    (hBc : 0 ≤ Bc) (hgood : ∀ᵐ x ∂μ, x ∈ S → ‖f x‖ ≤ Bg) (hcrude : ∀ᵐ x ∂μ, ‖f x‖ ≤ Bc)
    (hbad : μ Sᶜ ≤ ENNReal.ofReal ε) (hε : 0 ≤ ε) :
    ‖∫ x, f x ∂μ‖ ≤ Bg + Bc * ε := by
  set T := toMeasurable μ Sᶜ with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hμT : μ T ≤ ENNReal.ofReal ε := by rw [hT, measure_toMeasurable]; exact hbad
  have hfi : Integrable (fun x => ‖f x‖) μ :=
    (integrable_const Bc).mono' hf.norm (by
      filter_upwards [hcrude] with x hx; rw [norm_norm]; exact hx)
  have hgi : Integrable (fun x => Bg + T.indicator (fun _ => Bc) x) μ :=
    (integrable_const Bg).add ((integrable_const Bc).indicator hTm)
  have hle : ∀ᵐ x ∂μ, ‖f x‖ ≤ Bg + T.indicator (fun _ => Bc) x := by
    filter_upwards [hgood, hcrude] with x hg hc
    by_cases hx : x ∈ S
    · have := hg hx
      have : 0 ≤ T.indicator (fun _ => Bc) x := Set.indicator_nonneg (fun _ _ => hBc) x
      linarith
    · have hxT : x ∈ T := subset_toMeasurable μ Sᶜ hx
      rw [Set.indicator_of_mem hxT]
      linarith
  calc ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (Bg + T.indicator (fun _ => Bc) x) ∂μ := integral_mono_ae hfi hgi hle
    _ = Bg + Bc * (μ T).toReal := by
        rw [integral_add (integrable_const _) ((integrable_const Bc).indicator hTm),
          integral_const, integral_indicator hTm, setIntegral_const]
        simp [measureReal_def]
        ring
    _ ≤ Bg + Bc * ε := by
        have : (μ T).toReal ≤ ε := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμT
          rwa [ENNReal.toReal_ofReal hε] at this
        nlinarith

private theorem LX_box_compact {ι : Type*} [Fintype ι] (r : ℝ) :
    IsCompact {G : Matrix ι ι ℂ | ∀ i j, ‖G i j‖ ≤ r} := by
  have : {G : Matrix ι ι ℂ | ∀ i j, ‖G i j‖ ≤ r} =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => Metric.closedBall (0 : ℂ) r)) := by
    ext G
    constructor
    · intro hG i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using hG i j
    · intro hG i j
      have := hG i (Set.mem_univ _) j (Set.mem_univ _)
      simpa [Metric.mem_closedBall, dist_zero_right] using this
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _

private theorem LX_op_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z) : opNorm (res X ξ) ≤ (z.im)⁻¹ := by
  rcases hξ with rfl | rfl
  · exact opNorm_res_le X hX ξ hz
  · rw [show star z = starRingEnd ℂ z from rfl, res_conj X hX z hz, LX_op_conj]
    exact opNorm_res_le X hX z hz

private theorem LX_int_G {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ₁ ξ₂ : ℂ) (h₁ : ξ₁ = z ∨ ξ₁ = star z)
    (h₂ : ξ₂ = z ∨ ξ₂ = star z)
    (f : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hf : Continuous f) :
    Integrable (fun h => f (res (Matrix.of h + Λ) ξ₁, res (Matrix.of h + Λ) ξ₂)) μ := by
  have him : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ξ.im ≠ 0 := by
    rintro ξ (rfl | rfl)
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  obtain ⟨K, hK⟩ := ((LX_box_compact (ι := Idx D N) (z.im)⁻¹).prod
    (LX_box_compact (ι := Idx D N) (z.im)⁻¹)).exists_bound_of_continuousOn hf.continuousOn
  have hc : ∀ ξ : ℂ, ξ.im ≠ 0 → Continuous (fun h : Idx D N → Idx D N → ℂ =>
      res (Matrix.of (symArr h) + Λ) ξ) := fun ξ hξ =>
    continuous_pi fun x => continuous_pi fun y =>
      (contDiff_res_symArr Λ hΛ ξ hξ x y 0).continuous
  have hm : AEStronglyMeasurable (fun h => f (res (Matrix.of h + Λ) ξ₁,
      res (Matrix.of h + Λ) ξ₂)) μ := by
    refine (hf.comp ((hc ξ₁ (him ξ₁ h₁)).prodMk (hc ξ₂ (him ξ₂ h₂)))).aestronglyMeasurable.congr ?_
    filter_upwards [hμh] with h hh
    simp only [Function.comp, symArr_of_isHermitian h hh]
  refine (integrable_const K).mono' hm ?_
  filter_upwards [hμh] with h hh
  exact hK _ ⟨fun x y => (norm_apply_le_opNorm _ x y).trans
    (LX_op_res _ (hh.add hΛ) z hz ξ₁ h₁), fun x y => (norm_apply_le_opNorm _ x y).trans
    (LX_op_res _ (hh.add hΛ) z hz ξ₂ h₂)⟩

/-- The functions `h ↦ f (G₁(h), G₂(h))`, `f` continuous, form a subalgebra. -/
private def LX_alg {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) :
    Subalgebra ℂ ((Idx D N → Idx D N → ℂ) → ℂ) where
  carrier := {F | ∃ f : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ → ℂ,
    Continuous f ∧ F = fun h => f (res (Matrix.of h + Λ) z₁, res (Matrix.of h + Λ) z₂)}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun p => f p * g p, hf.mul hg, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun p => f p + g p, hf.add hg, rfl⟩
  algebraMap_mem' := fun c => ⟨fun _ => algebraMap ℂ ℂ c, continuous_const, rfl⟩

end LX_prob

section LX_expid

/-- Taking expectations in the pairing identity (3.40) [ELK]: an algebraic identity for the
expectations, in which the fluctuation terms are separated from the deterministic ones. -/
private theorem LX_exp_identity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : ℕ} (S : Subalgebra ℂ (Ω → ℂ)) (hS : ∀ f ∈ S, Integrable f μ)
    (L X1 : Fin D → Fin D → Ω → ℂ) (Zv : Ω → ℂ) (W Q : Fin D → Ω → ℂ)
    (hL : ∀ x b, L x b ∈ S) (hX1 : ∀ a c, X1 a c ∈ S) (hZ : Zv ∈ S) (hW : ∀ c, W c ∈ S)
    (hQ : ∀ x, Q x ∈ S) (Mh P K : Matrix (Fin D) (Fin D) ℂ) (Kt : Fin D → ℂ) (a b : Fin D)
    (hid : ∀ᵐ ω ∂μ, L a b ω = Mh a b + X1 a b ω - (D : ℂ) * Zv ω +
      (∑ x, ∑ c, P x c * (Mh a c + X1 a c ω) * L x b ω) + ∑ x, ∑ c, P x c * W c ω * Q x ω) :
    (∫ ω, L a b ω ∂μ) - K a b =
      (Mh a b + (∑ x, ∑ c, P x c * Mh a c * K x b) - K a b) +
      (∑ x, ∑ c, P x c * Mh a c * ((∫ ω, L x b ω ∂μ) - K x b)) +
      ((∫ ω, X1 a b ω ∂μ) - (D : ℂ) * (∫ ω, Zv ω ∂μ) +
        (∑ x, ∑ c, P x c * K x b * (∫ ω, X1 a c ω ∂μ)) +
        ∑ x, ∑ c, P x c * Kt x * (∫ ω, W c ω ∂μ)) +
      (∑ x, ∑ c, P x c * (∫ ω, X1 a c ω * (L x b ω - K x b) ∂μ)) +
      ∑ x, ∑ c, P x c * (∫ ω, W c ω * (Q x ω - Kt x) ∂μ) := by
  have cst : ∀ c : ℂ, algebraMap ℂ (Ω → ℂ) c = fun _ => c := fun c => rfl
  have hc : ∀ c : ℂ, (fun _ : Ω => c) ∈ S := fun c => by
    rw [← cst]; exact S.algebraMap_mem c
  have iL : ∀ x b, Integrable (L x b) μ := fun x b => hS _ (hL x b)
  have iX : ∀ a c, Integrable (X1 a c) μ := fun a c => hS _ (hX1 a c)
  have iW : ∀ c, Integrable (W c) μ := fun c => hS _ (hW c)
  have iZ : Integrable Zv μ := hS _ hZ
  have iY : ∀ x b : Fin D, ∀ k : ℂ, Integrable (fun ω => L x b ω - k) μ := fun x b k =>
    (iL x b).sub (integrable_const k)
  have iXY : ∀ a c x b : Fin D, ∀ k : ℂ, Integrable (fun ω => X1 a c ω * (L x b ω - k)) μ :=
    fun a c x b k => hS _ (S.mul_mem (hX1 a c) (S.sub_mem (hL x b) (hc k)))
  have iWV : ∀ c x : Fin D, ∀ k : ℂ, Integrable (fun ω => W c ω * (Q x ω - k)) μ :=
    fun c x k => hS _ (S.mul_mem (hW c) (S.sub_mem (hQ x) (hc k)))
  -- pointwise decomposition
  have hpt : ∀ ω, Mh a b + X1 a b ω - (D : ℂ) * Zv ω +
      (∑ x, ∑ c, P x c * (Mh a c + X1 a c ω) * L x b ω) + ∑ x, ∑ c, P x c * W c ω * Q x ω =
      Mh a b + X1 a b ω - (D : ℂ) * Zv ω +
      (∑ x, ∑ c, (P x c * Mh a c * K x b + P x c * Mh a c * (L x b ω - K x b) +
        P x c * K x b * X1 a c ω + P x c * (X1 a c ω * (L x b ω - K x b)))) +
      ∑ x, ∑ c, (P x c * Kt x * W c ω + P x c * (W c ω * (Q x ω - Kt x))) := by
    intro ω
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
      ring
  obtain ⟨s1, hs1⟩ : ∃ s1 : Ω → ℂ, s1 = fun ω => ∑ x, ∑ c, (P x c * Mh a c * K x b +
      P x c * Mh a c * (L x b ω - K x b) + P x c * K x b * X1 a c ω +
      P x c * (X1 a c ω * (L x b ω - K x b))) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2 : Ω → ℂ, s2 = fun ω => ∑ x, ∑ c, (P x c * Kt x * W c ω +
      P x c * (W c ω * (Q x ω - Kt x))) := ⟨_, rfl⟩
  have h1 : ∫ ω, L a b ω ∂μ = ∫ ω, (Mh a b + X1 a b ω - (D : ℂ) * Zv ω + s1 ω + s2 ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hid] with ω hω
    rw [hω, hpt, hs1, hs2]
  -- integrability of the pieces
  have iT1 : ∀ x c : Fin D, Integrable (fun ω => P x c * Mh a c * K x b + P x c * Mh a c *
      (L x b ω - K x b) + P x c * K x b * X1 a c ω + P x c * (X1 a c ω * (L x b ω - K x b))) μ := by
    intro x c
    exact (((integrable_const _).add ((iY x b (K x b)).const_mul _)).add
      ((iX a c).const_mul _)).add ((iXY a c x b (K x b)).const_mul _)
  have iT2 : ∀ x c : Fin D, Integrable (fun ω => P x c * Kt x * W c ω +
      P x c * (W c ω * (Q x ω - Kt x))) μ := fun x c =>
    ((iW c).const_mul _).add ((iWV c x (Kt x)).const_mul _)
  have iS1 : Integrable s1 μ := by
    rw [hs1]; exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun c _ => iT1 x c
  have iS2 : Integrable s2 μ := by
    rw [hs2]; exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun c _ => iT2 x c
  have iA : Integrable (fun ω => Mh a b + X1 a b ω - (D : ℂ) * Zv ω) μ :=
    ((integrable_const _).add (iX a b)).sub (iZ.const_mul _)
  have iA1 : Integrable (fun ω => Mh a b + X1 a b ω - (D : ℂ) * Zv ω + s1 ω) μ := iA.add iS1
  have eA : ∫ ω, (Mh a b + X1 a b ω - (D : ℂ) * Zv ω) ∂μ =
      Mh a b + (∫ ω, X1 a b ω ∂μ) - (D : ℂ) * (∫ ω, Zv ω ∂μ) := by
    have iAA : Integrable (fun ω => Mh a b + X1 a b ω) μ := (integrable_const _).add (iX a b)
    have iDZ : Integrable (fun ω => (D : ℂ) * Zv ω) μ := iZ.const_mul _
    rw [integral_sub iAA iDZ, integral_add (integrable_const _) (iX a b), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
  have e1 : ∀ x, ∫ ω, ∑ c, (P x c * Mh a c * K x b + P x c * Mh a c * (L x b ω - K x b) +
      P x c * K x b * X1 a c ω + P x c * (X1 a c ω * (L x b ω - K x b))) ∂μ =
      ∑ c, (P x c * Mh a c * K x b + P x c * Mh a c * ((∫ ω, L x b ω ∂μ) - K x b) +
        P x c * K x b * (∫ ω, X1 a c ω ∂μ) + P x c * (∫ ω, X1 a c ω * (L x b ω - K x b) ∂μ)) := by
    intro x
    rw [integral_finsetSum _ fun c _ => iT1 x c]
    refine Finset.sum_congr rfl fun c _ => ?_
    have j1 : Integrable (fun _ : Ω => P x c * Mh a c * K x b) μ := integrable_const _
    have j2 : Integrable (fun ω => P x c * Mh a c * (L x b ω - K x b)) μ :=
      (iY x b (K x b)).const_mul _
    have j3 : Integrable (fun ω => P x c * K x b * X1 a c ω) μ := (iX a c).const_mul _
    have j4 : Integrable (fun ω => P x c * (X1 a c ω * (L x b ω - K x b))) μ :=
      (iXY a c x b (K x b)).const_mul _
    have j12 : Integrable (fun ω => P x c * Mh a c * K x b +
        P x c * Mh a c * (L x b ω - K x b)) μ := j1.add j2
    have j123 : Integrable (fun ω => P x c * Mh a c * K x b +
        P x c * Mh a c * (L x b ω - K x b) + P x c * K x b * X1 a c ω) μ := j12.add j3
    rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub (iL x b) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  have e2 : ∀ x, ∫ ω, ∑ c, (P x c * Kt x * W c ω + P x c * (W c ω * (Q x ω - Kt x))) ∂μ =
      ∑ c, (P x c * Kt x * (∫ ω, W c ω ∂μ) + P x c * (∫ ω, W c ω * (Q x ω - Kt x) ∂μ)) := by
    intro x
    rw [integral_finsetSum _ fun c _ => iT2 x c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_add ((iW c).const_mul _) ((iWV c x (Kt x)).const_mul _), integral_const_mul,
      integral_const_mul]
  have eS1 : ∫ ω, s1 ω ∂μ = ∑ x, ∑ c, (P x c * Mh a c * K x b +
      P x c * Mh a c * ((∫ ω, L x b ω ∂μ) - K x b) +
      P x c * K x b * (∫ ω, X1 a c ω ∂μ) + P x c * (∫ ω, X1 a c ω * (L x b ω - K x b) ∂μ)) := by
    rw [hs1, integral_finsetSum _ fun x _ => integrable_finsetSum _ fun c _ => iT1 x c]
    exact Finset.sum_congr rfl fun x _ => e1 x
  have eS2 : ∫ ω, s2 ω ∂μ = ∑ x, ∑ c, (P x c * Kt x * (∫ ω, W c ω ∂μ) +
      P x c * (∫ ω, W c ω * (Q x ω - Kt x) ∂μ)) := by
    rw [hs2, integral_finsetSum _ fun x _ => integrable_finsetSum _ fun c _ => iT2 x c]
    exact Finset.sum_congr rfl fun x _ => e2 x
  rw [h1, integral_add iA1 iS2, integral_add iA iS1, eA, eS1, eS2]
  simp only [Finset.sum_add_distrib]
  ring

end LX_expid

section LX_vars

variable {D N : ℕ}

/-- `D ⟨(G₁ - M₁) E_a M₂ E_c⟩`, the fluctuation `U₁` of the proof of Lemma 3.7
[lemma_G_large_2]. -/
private def LX_X1 (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a c : Fin D)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (D : ℂ) * ntr ((res (Matrix.of h + Λ) z₁ - MExt Λ z₁) * Ea D N a * MExt Λ z₂ * Ea D N c)

/-- `D ⟨(G₂ - M₂) E_c⟩`. -/
private def LX_W (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) (c : Fin D)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (D : ℂ) * ntr ((res (Matrix.of h + Λ) z₂ - MExt Λ z₂) * Ea D N c)

/-- `D ⟨G₁ E_a M₂ E_x G₂ E_b⟩`. -/
private def LX_Q (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a b x : Fin D)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * Ea D N x *
    res (Matrix.of h + Λ) z₂ * Ea D N b)

/-- The term `⟨\underline{G₁E_aM₂HG₂}E_b⟩`, written through (3.39) [eq:aftertrace] as a function of
`G₁, G₂` only. -/
private def LX_Zv (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (a b : Fin D)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * Ea D N b) -
    ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * res (Matrix.of h + Λ) z₂ * Ea D N b) +
    (∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N a *
      MExt Λ z₂ * Ea D N c)) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N x *
      res (Matrix.of h + Λ) z₂ * Ea D N b)) +
    (∑ x, ∑ c, PTheta D θ x c *
      ((D : ℂ) * ntr ((res (Matrix.of h + Λ) z₂ - MExt Λ z₂) * Ea D N c)) *
      ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * Ea D N x *
        res (Matrix.of h + Λ) z₂ * Ea D N b))

private theorem LX_cont_ntr {ι X : Type*} [Fintype ι] [TopologicalSpace X] (Y : X → Matrix ι ι ℂ)
    (hY : Continuous Y) : Continuous (fun p => ntr (Y p)) := by
  unfold ntr; exact continuous_const.mul hY.matrix_trace

private theorem LX_mem1 (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    (fun h : Idx D N → Idx D N → ℂ => ntr (res (Matrix.of h + Λ) z₁ * Y)) ∈ LX_alg Λ z₁ z₂ :=
  ⟨fun p => ntr (p.1 * Y), LX_cont_ntr _ (continuous_fst.matrix_mul continuous_const), rfl⟩

private theorem LX_mem1' (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    (fun h : Idx D N → Idx D N → ℂ => ntr (res (Matrix.of h + Λ) z₂ * Y)) ∈ LX_alg Λ z₁ z₂ :=
  ⟨fun p => ntr (p.2 * Y), LX_cont_ntr _ (continuous_snd.matrix_mul continuous_const), rfl⟩

private theorem LX_mem2 (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (Y Y' : Matrix (Idx D N) (Idx D N) ℂ) :
    (fun h : Idx D N → Idx D N → ℂ =>
      ntr (res (Matrix.of h + Λ) z₁ * Y * res (Matrix.of h + Λ) z₂ * Y')) ∈ LX_alg Λ z₁ z₂ :=
  ⟨fun p => ntr (p.1 * Y * p.2 * Y'), LX_cont_ntr _ (((continuous_fst.matrix_mul continuous_const).matrix_mul
    continuous_snd).matrix_mul continuous_const), rfl⟩

private theorem LX_const_mem (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ c : ℂ) :
    (fun _ : Idx D N → Idx D N → ℂ => c) ∈ LX_alg Λ z₁ z₂ :=
  (LX_alg Λ z₁ z₂).algebraMap_mem c

end LX_vars

section LX_inst

variable {D N : ℕ}

private theorem LX_sum_mem {Ω κ : Type*} (S : Subalgebra ℂ (Ω → ℂ)) (s : Finset κ)
    (f : κ → Ω → ℂ) (hf : ∀ k ∈ s, f k ∈ S) : (fun ω => ∑ k ∈ s, f k ω) ∈ S := by
  have := S.sum_mem hf
  convert this using 1
  ext ω
  simp [Finset.sum_apply]

private theorem LX_Lmat_eq (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (x b : Fin D)
    (h : Idx D N → Idx D N → ℂ) :
    Lmat Λ h z₁ z₂ x b = (D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N x *
      res (Matrix.of h + Λ) z₂ * Ea D N b) := rfl

private theorem LX_MhX1 (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a c : Fin D)
    (h : Idx D N → Idx D N → ℂ) :
    Mhat Λ z₁ z₂ a c + LX_X1 Λ z₁ z₂ a c h = (D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ *
      Ea D N a * MExt Λ z₂ * Ea D N c) := by
  unfold Mhat LX_X1
  rw [← mul_add, ← LX_ntr_add, sub_mul, sub_mul, sub_mul]
  congr 2
  abel


private theorem LX_mem_L (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (x b : Fin D) :
    (fun h => Lmat Λ h z₁ z₂ x b) ∈ LX_alg Λ z₁ z₂ :=
  (LX_alg Λ z₁ z₂).mul_mem (LX_const_mem Λ z₁ z₂ _) (LX_mem2 Λ z₁ z₂ (Ea D N x) (Ea D N b))

private theorem LX_mem_X1 (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a c : Fin D) :
    LX_X1 Λ z₁ z₂ a c ∈ LX_alg Λ z₁ z₂ := by
  have hc := LX_const_mem Λ z₁ z₂
  have e : LX_X1 Λ z₁ z₂ a c = fun h => (D : ℂ) * (ntr (res (Matrix.of h + Λ) z₁ *
      (Ea D N a * MExt Λ z₂ * Ea D N c)) - ntr (MExt Λ z₁ * (Ea D N a * MExt Λ z₂ *
        Ea D N c))) := by
    funext h
    simp only [LX_X1, sub_mul, LX_ntr_sub, Matrix.mul_assoc]
  rw [e]
  exact (LX_alg Λ z₁ z₂).mul_mem (hc _) ((LX_alg Λ z₁ z₂).sub_mem (LX_mem1 Λ z₁ z₂ _) (hc _))

private theorem LX_mem_W (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (c : Fin D) :
    LX_W Λ z₂ c ∈ LX_alg Λ z₁ z₂ := by
  have hc := LX_const_mem Λ z₁ z₂
  have e : LX_W Λ z₂ c = fun h => (D : ℂ) * (ntr (res (Matrix.of h + Λ) z₂ * Ea D N c) -
      ntr (MExt Λ z₂ * Ea D N c)) := by
    funext h
    simp only [LX_W, sub_mul, LX_ntr_sub]
  rw [e]
  exact (LX_alg Λ z₁ z₂).mul_mem (hc _) ((LX_alg Λ z₁ z₂).sub_mem (LX_mem1' Λ z₁ z₂ _) (hc _))

private theorem LX_mem_Q (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a b x : Fin D) :
    LX_Q Λ z₁ z₂ a b x ∈ LX_alg Λ z₁ z₂ := by
  have e : LX_Q Λ z₁ z₂ a b x = fun h => (D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ *
      (Ea D N a * MExt Λ z₂ * Ea D N x) * res (Matrix.of h + Λ) z₂ * Ea D N b) := by
    funext h
    simp only [LX_Q, Matrix.mul_assoc]
  rw [e]
  exact (LX_alg Λ z₁ z₂).mul_mem (LX_const_mem Λ z₁ z₂ _) (LX_mem2 Λ z₁ z₂ _ _)

private theorem LX_mem_Zv (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (a b : Fin D) :
    LX_Zv Λ θ z₁ z₂ a b ∈ LX_alg Λ z₁ z₂ := by
  set S := LX_alg Λ z₁ z₂ with hS
  have hc := LX_const_mem Λ z₁ z₂
  have hW := LX_mem_W Λ z₁ z₂
  have e : LX_Zv Λ θ z₁ z₂ a b = fun h => (ntr (res (Matrix.of h + Λ) z₁ *
      (Ea D N a * MExt Λ z₂ * Ea D N b)) -
      ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * res (Matrix.of h + Λ) z₂ * Ea D N b) +
      (∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ *
        (Ea D N a * MExt Λ z₂ * Ea D N c))) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N x *
        res (Matrix.of h + Λ) z₂ * Ea D N b)) +
      (∑ x, ∑ c, PTheta D θ x c * LX_W Λ z₂ c h * ntr (res (Matrix.of h + Λ) z₁ *
        (Ea D N a * MExt Λ z₂ * Ea D N x) * res (Matrix.of h + Λ) z₂ * Ea D N b))) := by
    funext h
    simp only [LX_Zv, LX_W, Matrix.mul_assoc]
  rw [e]
  refine S.add_mem (S.add_mem (S.sub_mem (LX_mem1 Λ z₁ z₂ _) (LX_mem2 Λ z₁ z₂ _ _))
    (LX_sum_mem S _ _ fun x _ => LX_sum_mem S _ _ fun c _ => ?_))
    (LX_sum_mem S _ _ fun x _ => LX_sum_mem S _ _ fun c _ => ?_)
  · exact S.mul_mem (S.mul_mem (hc _) (S.mul_mem (hc _) (LX_mem1 Λ z₁ z₂ _)))
      (LX_mem2 Λ z₁ z₂ _ _)
  · exact S.mul_mem (S.mul_mem (hc _) (hW c)) (LX_mem2 Λ z₁ z₂ _ _)

private theorem LX_alg_int (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    ∀ f ∈ LX_alg (lam D N A) z₁ z₂, Integrable f μ := by
  rintro _ ⟨f, hf, rfl⟩
  exact LX_int_G hμh (lam D N A) (lam_isHermitian D N A) z hz z₁ z₂ h₁ h₂ f hf

private theorem LX_pair_identity (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) :
    ELmat μ (lam D N A) z₁ z₂ a b - KTheta (lam D N A) θ z₁ z₂ a b =
      (Mhat (lam D N A) z₁ z₂ a b + (∑ x, ∑ c, PTheta D θ x c * Mhat (lam D N A) z₁ z₂ a c *
          KTheta (lam D N A) θ z₁ z₂ x b) - KTheta (lam D N A) θ z₁ z₂ a b) +
      (∑ x, ∑ c, PTheta D θ x c * Mhat (lam D N A) z₁ z₂ a c *
        (ELmat μ (lam D N A) z₁ z₂ x b - KTheta (lam D N A) θ z₁ z₂ x b)) +
      ((∫ h, LX_X1 (lam D N A) z₁ z₂ a b h ∂μ) - (D : ℂ) *
          (∫ h, underTwoB (lam D N A) θ h z₁ z₂ a (Ea D N b) ∂μ) +
        (∑ x, ∑ c, PTheta D θ x c * KTheta (lam D N A) θ z₁ z₂ x b *
          (∫ h, LX_X1 (lam D N A) z₁ z₂ a c h ∂μ)) +
        ∑ x, ∑ c, PTheta D θ x c *
          KThetaB (lam D N A) θ z₂ z₁ (MExt (lam D N A) z₂ * Ea D N x) b a *
          (∫ h, LX_W (lam D N A) z₂ c h ∂μ)) +
      (∑ x, ∑ c, PTheta D θ x c * (∫ h, LX_X1 (lam D N A) z₁ z₂ a c h *
        (Lmat (lam D N A) h z₁ z₂ x b - KTheta (lam D N A) θ z₁ z₂ x b) ∂μ)) +
      ∑ x, ∑ c, PTheta D θ x c * (∫ h, LX_W (lam D N A) z₂ c h *
        (LX_Q (lam D N A) z₁ z₂ a b x h -
          KThetaB (lam D N A) θ z₂ z₁ (MExt (lam D N A) z₂ * Ea D N x) b a) ∂μ) := by
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  have him : z₂.im ≠ 0 := by
    rcases h₂ with rfl | rfl
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  set S := LX_alg Λ z₁ z₂ with hS
  have hSint := LX_alg_int μ hμh A z hz z₁ z₂ h₁ h₂
  have hL := LX_mem_L Λ z₁ z₂
  have hX1 := LX_mem_X1 Λ z₁ z₂
  have hW := LX_mem_W Λ z₁ z₂
  have hQ := LX_mem_Q Λ z₁ z₂ a b
  have hZ := LX_mem_Zv Λ θ z₁ z₂ a b
  -- the pointwise identity
  have hid : ∀ h, Lmat Λ h z₁ z₂ a b = Mhat Λ z₁ z₂ a b + LX_X1 Λ z₁ z₂ a b h -
      (D : ℂ) * LX_Zv Λ θ z₁ z₂ a b h +
      (∑ x, ∑ c, PTheta D θ x c * (Mhat Λ z₁ z₂ a c + LX_X1 Λ z₁ z₂ a c h) * Lmat Λ h z₁ z₂ x b) +
      ∑ x, ∑ c, PTheta D θ x c * LX_W Λ z₂ c h * LX_Q Λ z₁ z₂ a b x h := by
    intro h
    have e3 : ∑ x, ∑ c, PTheta D θ x c * (Mhat Λ z₁ z₂ a c + LX_X1 Λ z₁ z₂ a c h) *
        Lmat Λ h z₁ z₂ x b = (D : ℂ) * ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) *
        ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * Ea D N c)) *
        ntr (res (Matrix.of h + Λ) z₁ * Ea D N x * res (Matrix.of h + Λ) z₂ * Ea D N b) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
      rw [LX_MhX1, LX_Lmat_eq]; ring
    have e4 : ∑ x, ∑ c, PTheta D θ x c * LX_W Λ z₂ c h * LX_Q Λ z₁ z₂ a b x h =
        (D : ℂ) * ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + Λ) z₂ -
          MExt Λ z₂) * Ea D N c)) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ *
          Ea D N x * res (Matrix.of h + Λ) z₂ * Ea D N b) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [LX_W, LX_Q]; ring
    have e1 := LX_MhX1 Λ z₁ z₂ a b h
    rw [e3, e4, e1, LX_Lmat_eq]
    simp only [LX_Zv]
    ring
  have hmain := LX_exp_identity S hSint (fun x b h => Lmat Λ h z₁ z₂ x b)
    (fun a c => LX_X1 Λ z₁ z₂ a c) (LX_Zv Λ θ z₁ z₂ a b) (fun c => LX_W Λ z₂ c)
    (fun x => LX_Q Λ z₁ z₂ a b x) hL hX1 hZ hW hQ (Mhat Λ z₁ z₂) (PTheta D θ)
    (KTheta Λ θ z₁ z₂) (fun x => KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a) a b
    (Filter.Eventually.of_forall fun h => hid h)
  have hZae : ∫ h, LX_Zv Λ θ z₁ z₂ a b h ∂μ = ∫ h, underTwoB Λ θ h z₁ z₂ a (Ea D N b) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμh] with h hh
    have := resPair_aftertrace θ A h hh z₁ z₂ him a (Ea D N b)
    simp only [LX_Zv]
    rw [← hΛdef] at this
    linear_combination (-1 : ℂ) * this
  rw [hZae] at hmain
  exact hmain

end LX_inst

section LX_prob2

private theorem LX_prod_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (f g : Ω → ℂ) (hm : AEStronglyMeasurable (fun ω => f ω * g ω) μ)
    (bf bg Bf Bg ε₁ ε₂ : ℝ) (hbf : 0 ≤ bf) (hbg : 0 ≤ bg) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (h1 : 0 ≤ ε₁) (h2 : 0 ≤ ε₂) (hf : μ {ω | bf < ‖f ω‖} ≤ ENNReal.ofReal ε₁)
    (hg : μ {ω | bg < ‖g ω‖} ≤ ENNReal.ofReal ε₂) (hBf' : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ Bf)
    (hBg' : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ Bg) :
    ‖∫ ω, f ω * g ω ∂μ‖ ≤ bf * bg + Bf * Bg * (ε₁ + ε₂) := by
  refine LX_int_split (fun ω => f ω * g ω) hm {ω | ‖f ω‖ ≤ bf ∧ ‖g ω‖ ≤ bg} (bf * bg) (Bf * Bg)
    (ε₁ + ε₂) (mul_nonneg hbf hbg) (mul_nonneg hBf hBg) ?_ ?_ ?_ (add_nonneg h1 h2)
  · refine Filter.Eventually.of_forall fun ω hω => ?_
    rw [norm_mul]
    exact mul_le_mul hω.1 hω.2 (norm_nonneg _) hbf
  · filter_upwards [hBf', hBg'] with ω h3 h4
    rw [norm_mul]
    exact mul_le_mul h3 h4 (norm_nonneg _) hBf
  · have hsub : {ω | ‖f ω‖ ≤ bf ∧ ‖g ω‖ ≤ bg}ᶜ ⊆ {ω | bf < ‖f ω‖} ∪ {ω | bg < ‖g ω‖} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
      exact hω
    calc μ {ω | ‖f ω‖ ≤ bf ∧ ‖g ω‖ ≤ bg}ᶜ ≤ μ ({ω | bf < ‖f ω‖} ∪ {ω | bg < ‖g ω‖}) :=
          measure_mono hsub
      _ ≤ μ {ω | bf < ‖f ω‖} + μ {ω | bg < ‖g ω‖} := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε₁ + ENNReal.ofReal ε₂ := add_le_add hf hg
      _ = ENNReal.ofReal (ε₁ + ε₂) := (ENNReal.ofReal_add h1 h2).symm

private theorem LX_event_scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (β b : ℝ)
    (hβ : 0 < β) (F G : Ω → ℂ) (hFG : ∀ ω, F ω = (β : ℂ) * G ω) {ε : ENNReal}
    (h : μ {ω | b < ‖G ω‖} ≤ ε) : μ {ω | β * b < ‖F ω‖} ≤ ε := by
  refine le_trans (measure_mono ?_) h
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hFG ω, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ] at hω
  exact lt_of_mul_lt_mul_left hω hβ.le

private theorem LX_entry_le_hs {n : Type*} [Fintype n] (X : Matrix n n ℂ) (i j : n) :
    ‖X i j‖ ≤ hsNorm X := by
  unfold hsNorm
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖X i j‖ ^ 2 ≤ ∑ l, ‖X i l‖ ^ 2 :=
        Finset.single_le_sum (f := fun l => ‖X i l‖ ^ 2) (fun l _ => sq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ k, ∑ l, ‖X k l‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ∑ l, ‖X k l‖ ^ 2)
          (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)

private theorem LX_hs_le {n : Type*} [Fintype n] (X : Matrix n n ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (h : ∀ i j, ‖X i j‖ ≤ β) : hsNorm X ≤ Fintype.card n * β := by
  unfold hsNorm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ _i : n, ∑ _j : n, β ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (Fintype.card n * β) ^ 2 := by simp; ring

end LX_prob2

section LX_crude

variable {D N : ℕ}

private theorem LX_op3 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C : Matrix ι ι ℂ) (a b c : ℝ)
    (ha : opNorm A ≤ a) (hb : opNorm B ≤ b) (hc : opNorm C ≤ c) :
    opNorm (A * B * C) ≤ a * b * c := by
  have h0a := LX_op_nonneg A
  have h0b := LX_op_nonneg B
  have h0c := LX_op_nonneg C
  calc opNorm (A * B * C) ≤ opNorm (A * B) * opNorm C := opNorm_mul_le _ _
    _ ≤ (opNorm A * opNorm B) * opNorm C := mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) h0c
    _ ≤ a * b * c := by
        have ha0 : 0 ≤ a := h0a.trans ha
        have hb0 : 0 ≤ b := h0b.trans hb
        exact mul_le_mul (mul_le_mul ha hb h0b ha0) hc h0c (mul_nonneg ha0 hb0)

private theorem LX_op4 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C E : Matrix ι ι ℂ)
    (a b c e : ℝ) (ha : opNorm A ≤ a) (hb : opNorm B ≤ b) (hc : opNorm C ≤ c)
    (he : opNorm E ≤ e) : opNorm (A * B * C * E) ≤ a * b * c * e := by
  have h0e := LX_op_nonneg E
  calc opNorm (A * B * C * E) ≤ opNorm (A * B * C) * opNorm E := opNorm_mul_le _ _
    _ ≤ (a * b * c) * e := mul_le_mul (LX_op3 A B C a b c ha hb hc) he h0e
        ((LX_op_nonneg _).trans (LX_op3 A B C a b c ha hb hc))

private theorem LX_Dn_ntr (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖(D : ℂ) * ntr Y‖ ≤ D * opNorm Y := by
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (LX_ntr_le Y) (Nat.cast_nonneg (α := ℝ) D)

/-- Crude bounds on the random variables, for a Hermitian array. -/
private theorem LX_crude (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (hM₁ : opNorm (MExt Λ z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt Λ z₂) ≤ 5 / 4)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (a b c x : Fin D) :
    ‖LX_X1 Λ z₁ z₂ a c h‖ ≤ D * (((z.im)⁻¹ + 5 / 4) * (5 / 4)) ∧
    ‖Lmat Λ h z₁ z₂ x b‖ ≤ D * ((z.im)⁻¹ * (z.im)⁻¹) ∧
    ‖LX_W Λ z₂ c h‖ ≤ D * ((z.im)⁻¹ + 5 / 4) ∧
    ‖LX_Q Λ z₁ z₂ a b x h‖ ≤ D * ((z.im)⁻¹ * (5 / 4) * (z.im)⁻¹) := by
  have g₁ := LX_op_res _ (hh.add hΛ) z hz z₁ h₁
  have g₂ := LX_op_res _ (hh.add hΛ) z hz z₂ h₂
  have e1 : ∀ y : Fin D, opNorm (Ea D N y) ≤ 1 := fun y => LX_op_Ea y
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (LX_Dn_ntr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) D)
    have := LX_op4 (res (Matrix.of h + Λ) z₁ - MExt Λ z₁) (Ea D N a) (MExt Λ z₂) (Ea D N c)
      ((z.im)⁻¹ + 5 / 4) 1 (5 / 4) 1 ((LX_op_sub_le _ _).trans (add_le_add g₁ hM₁)) (e1 a) hM₂
      (e1 c)
    simpa using this
  · refine (LX_Dn_ntr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) D)
    have := LX_op4 (res (Matrix.of h + Λ) z₁) (Ea D N x) (res (Matrix.of h + Λ) z₂) (Ea D N b)
      (z.im)⁻¹ 1 (z.im)⁻¹ 1 g₁ (e1 x) g₂ (e1 b)
    simpa using this
  · refine (LX_Dn_ntr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) D)
    have := opNorm_mul_le (res (Matrix.of h + Λ) z₂ - MExt Λ z₂) (Ea D N c)
    have h3 := (LX_op_sub_le (res (Matrix.of h + Λ) z₂) (MExt Λ z₂)).trans (add_le_add g₂ hM₂)
    have h4 := e1 c
    have h5 := LX_op_nonneg (res (Matrix.of h + Λ) z₂ - MExt Λ z₂)
    nlinarith [LX_op_nonneg (Ea D N c)]
  · refine (LX_Dn_ntr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) D)
    have := LX_op4 (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂) (Ea D N x)
      (res (Matrix.of h + Λ) z₂) (Ea D N b) ((z.im)⁻¹ * 1 * (5 / 4)) 1 (z.im)⁻¹ 1
      (LX_op3 _ _ _ _ _ _ g₁ (e1 a) hM₂) (e1 x) g₂ (e1 b)
    simpa using this

end LX_crude

section LX_E

variable {D N : ℕ}

private theorem LX_KB_bound (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (a b : Fin D)
    (hM₁ : opNorm (MExt Λ z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt Λ z₂) ≤ 5 / 4) :
    ‖KThetaB Λ θ z₁ z₂ B a b‖ ≤
      D * opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * ((25 / 16) * opNorm B)) := by
  unfold KThetaB
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x : Fin D, ‖(1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x *
      ((D : ℂ) * ntr (MExt Λ z₁ * Ea D N x * MExt Λ z₂ * Ea D N b * B))‖ ≤
      opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * ((25 / 16) * opNorm B)) := by
    intro x
    rw [norm_mul]
    refine mul_le_mul (norm_apply_le_opNorm _ a x) ?_ (norm_nonneg _) (LX_op_nonneg _)
    refine (LX_Dn_ntr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) D)
    have := LX_op4 (MExt Λ z₁ * Ea D N x * MExt Λ z₂ * Ea D N b) B (1 : Matrix (Idx D N) (Idx D N) ℂ)
      (1 : Matrix (Idx D N) (Idx D N) ℂ) ((5 / 4) * 1 * (5 / 4) * 1) (opNorm B) 1 1
      (LX_op4 _ _ _ _ _ _ _ _ hM₁ (LX_op_Ea x) hM₂ (LX_op_Ea b)) le_rfl LX_op_one LX_op_one
    simp only [Matrix.mul_one] at this
    nlinarith [LX_op_nonneg B]
  calc ∑ x, ‖(1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x *
        ((D : ℂ) * ntr (MExt Λ z₁ * Ea D N x * MExt Λ z₂ * Ea D N b * B))‖
      ≤ ∑ _x : Fin D, opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * ((25 / 16) * opNorm B)) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = _ := by simp; ring

private theorem LX_K_bound (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (a b : Fin D)
    (hM₁ : opNorm (MExt Λ z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt Λ z₂) ≤ 5 / 4) :
    ‖KTheta Λ θ z₁ z₂ a b‖ ≤
      D * opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * (25 / 16)) := by
  unfold KTheta
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x : Fin D, ‖(1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x * Mhat Λ z₁ z₂ x b‖ ≤
      opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * (25 / 16)) := by
    intro x
    rw [norm_mul]
    refine mul_le_mul (norm_apply_le_opNorm _ a x) ?_ (norm_nonneg _) (LX_op_nonneg _)
    unfold Mhat
    refine (LX_Dn_ntr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) D)
    have := LX_op4 (MExt Λ z₁) (Ea D N x) (MExt Λ z₂) (Ea D N b) (5 / 4) 1 (5 / 4) 1 hM₁
      (LX_op_Ea x) hM₂ (LX_op_Ea b)
    linarith
  calc ∑ x, ‖(1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x * Mhat Λ z₁ z₂ x b‖
      ≤ ∑ _x : Fin D, opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * (25 / 16)) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = _ := by simp; ring

end LX_E


section LX_BE

/-- The bound for the first fluctuation product of (3.40) [ELK]. -/
private def LX_BE1 (D N : ℕ) (τ₁ η r ε : ℝ) : ℝ :=
  ((D * (5 / 4)) * ((N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * η)))) *
    ((N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * r)) +
  (D * ((η⁻¹ + 5 / 4) * (5 / 4))) * (D * (η⁻¹ * η⁻¹) + D * r * (D * (25 / 16))) * (ε + ε)

/-- The bound for the second fluctuation product of (3.40) [ELK]. -/
private def LX_BE2 (D N : ℕ) (τ₁ η r ε : ℝ) : ℝ :=
  ((D : ℝ) * ((N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * η)))) *
    ((D * (5 / 4)) * ((N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * r))) +
  (D * (η⁻¹ + 5 / 4)) * (D * (η⁻¹ * (5 / 4) * η⁻¹) + D * r * (D * ((25 / 16) * (5 / 4)))) *
    (ε + ε)

end LX_BE

section LX_E12

variable {D N : ℕ}

private theorem LX_E1 (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (hD : 1 ≤ D) (θ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (hM₁ : opNorm (MExt (lam D N A) z₁) ≤ 5 / 4)
    (hM₂ : opNorm (MExt (lam D N A) z₂) ≤ 5 / 4)
    (hdet : (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0) (τ₁ ε : ℝ) (hε : 0 ≤ ε)
    (hAv : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      μ {h | (N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |z₁.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * B)‖} ≤
        ENNReal.ofReal ε)
    (hTwo : μ {h | (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
        hsNorm (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂)} ≤ ENNReal.ofReal ε)
    (a c x b : Fin D) :
    ‖∫ h, LX_X1 (lam D N A) z₁ z₂ a c h *
        (Lmat (lam D N A) h z₁ z₂ x b - KTheta (lam D N A) θ z₁ z₂ x b) ∂μ‖ ≤
      LX_BE1 D N τ₁ z.im (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) ε := by
  unfold LX_BE1
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hi1 : |z₁.im| = z.im := by
    rcases h₁ with rfl | rfl
    · exact abs_of_pos hz
    · simp [abs_of_pos hz]
  have hrn := LX_op_nonneg (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹
  have hη : 0 < (z.im)⁻¹ := inv_pos.mpr hz
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ τ₁ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hmem : (fun h => LX_X1 Λ z₁ z₂ a c h *
      (Lmat Λ h z₁ z₂ x b - KTheta Λ θ z₁ z₂ x b)) ∈ LX_alg Λ z₁ z₂ :=
    (LX_alg Λ z₁ z₂).mul_mem (LX_mem_X1 Λ z₁ z₂ a c) ((LX_alg Λ z₁ z₂).sub_mem
      (LX_mem_L Λ z₁ z₂ x b) (LX_const_mem Λ z₁ z₂ _))
  have hm := (LX_alg_int μ hμh A z hz z₁ z₂ h₁ h₂ _ hmem).aestronglyMeasurable
  have hKb := LX_K_bound Λ θ z₁ z₂ x b hM₁ hM₂
  have hKb0 : 0 ≤ D * opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * (25 / 16)) := by positivity
  refine LX_prod_bound (LX_X1 Λ z₁ z₂ a c)
    (fun h => Lmat Λ h z₁ z₂ x b - KTheta Λ θ z₁ z₂ x b) hm _ _ _ _ ε ε (by positivity)
    (by positivity) (by positivity) (by positivity) hε hε ?_ ?_ ?_ ?_
  · -- the event for the first factor
    set B₀ := Ea D N a * MExt Λ z₂ * Ea D N c with hB₀
    have hB₀n : opNorm B₀ ≤ 5 / 4 := by
      have := LX_op3 (Ea D N a) (MExt Λ z₂) (Ea D N c) 1 (5 / 4) 1 (LX_op_Ea a) hM₂ (LX_op_Ea c)
      linarith
    have hB' : opNorm (((4 / 5 : ℝ) : ℂ) • B₀) ≤ 1 := by
      rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith
    have := LX_event_scale (μ := μ) ((D : ℝ) * (5 / 4))
      ((N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |z₁.im|))) (by positivity)
      (fun h => LX_X1 Λ z₁ z₂ a c h)
      (fun h => ntr ((res (Matrix.of h + Λ) z₁ - MExt Λ z₁) * (((4 / 5 : ℝ) : ℂ) • B₀)))
      (fun h => by
        simp only [LX_X1, hB₀, Matrix.mul_smul, LX_ntr_smul, Matrix.mul_assoc]
        push_cast
        ring) (hAv _ hB')
    rw [hi1] at this
    exact this
  · refine le_trans (measure_mono ?_) hTwo
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    refine lt_of_lt_of_le hh ?_
    have := LX_entry_le_hs (Lmat Λ h z₁ z₂ - KTheta Λ θ z₁ z₂) x b
    simpa [Matrix.sub_apply] using this
  · filter_upwards [hμh] with h hh
    exact (LX_crude Λ hΛ z hz z₁ z₂ h₁ h₂ hM₁ hM₂ h hh a b c x).1
  · filter_upwards [hμh] with h hh
    have := (LX_crude Λ hΛ z hz z₁ z₂ h₁ h₂ hM₁ hM₂ h hh a b c x).2.1
    calc ‖Lmat Λ h z₁ z₂ x b - KTheta Λ θ z₁ z₂ x b‖ ≤
          ‖Lmat Λ h z₁ z₂ x b‖ + ‖KTheta Λ θ z₁ z₂ x b‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add this hKb

end LX_E12

section LX_E22

variable {D N : ℕ}

private theorem LX_E2 (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (hD : 1 ≤ D) (θ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (hM₁ : opNorm (MExt (lam D N A) z₁) ≤ 5 / 4)
    (hM₂ : opNorm (MExt (lam D N A) z₂) ≤ 5 / 4)
    (hdet : (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ).det ≠ 0) (τ₁ ε : ℝ) (hε : 0 ≤ ε)
    (hAv : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      μ {h | (N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |z₂.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) * B)‖} ≤
        ENNReal.ofReal ε)
    (hBB : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 → ∀ a' : Fin D,
      μ {h | (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹) <
        ‖ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N a' * res (Matrix.of h + lam D N A) z₁ *
          B) - ∑ x, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ a' x *
          ntr (MExt (lam D N A) z₂ * Ea D N x * MExt (lam D N A) z₁ * B)‖} ≤ ENNReal.ofReal ε)
    (a b c x : Fin D) :
    ‖∫ h, LX_W (lam D N A) z₂ c h * (LX_Q (lam D N A) z₁ z₂ a b x h -
        KThetaB (lam D N A) θ z₂ z₁ (MExt (lam D N A) z₂ * Ea D N x) b a) ∂μ‖ ≤
      LX_BE2 D N τ₁ z.im (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹) ε := by
  unfold LX_BE2
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hi2 : |z₂.im| = z.im := by
    rcases h₂ with rfl | rfl
    · exact abs_of_pos hz
    · simp [abs_of_pos hz]
  have hrn := LX_op_nonneg (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹
  have hη : 0 < (z.im)⁻¹ := inv_pos.mpr hz
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ τ₁ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hmem : (fun h => LX_W Λ z₂ c h * (LX_Q Λ z₁ z₂ a b x h -
      KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a)) ∈ LX_alg Λ z₁ z₂ :=
    (LX_alg Λ z₁ z₂).mul_mem (LX_mem_W Λ z₁ z₂ c) ((LX_alg Λ z₁ z₂).sub_mem
      (LX_mem_Q Λ z₁ z₂ a b x) (LX_const_mem Λ z₁ z₂ _))
  have hm := (LX_alg_int μ hμh A z hz z₁ z₂ h₁ h₂ _ hmem).aestronglyMeasurable
  have hMx : opNorm (MExt Λ z₂ * Ea D N x) ≤ 5 / 4 := by
    have := opNorm_mul_le (MExt Λ z₂) (Ea D N x)
    have := LX_op_Ea (D := D) (N := N) x
    nlinarith [LX_op_nonneg (MExt Λ z₂), LX_op_nonneg (Ea D N x)]
  have hKt := LX_KB_bound Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a hM₂ hM₁
  have hKt' : ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
      D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * (5 / 4))) := by
    refine hKt.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hMx (by norm_num)
  refine LX_prod_bound (LX_W Λ z₂ c)
    (fun h => LX_Q Λ z₁ z₂ a b x h - KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a) hm _ _ _ _ ε ε
    (by positivity) (by positivity) (by positivity) (by positivity) hε hε ?_ ?_ ?_ ?_
  · have := LX_event_scale (μ := μ) (D : ℝ) ((N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |z₂.im|)))
      hDr (fun h => LX_W Λ z₂ c h)
      (fun h => ntr ((res (Matrix.of h + Λ) z₂ - MExt Λ z₂) * Ea D N c))
      (fun h => rfl) (hAv _ (LX_op_Ea c))
    rw [hi2] at this
    exact this
  · set B₀ := Ea D N a * MExt Λ z₂ * Ea D N x with hB₀
    have hB₀n : opNorm B₀ ≤ 5 / 4 := by
      have := LX_op3 (Ea D N a) (MExt Λ z₂) (Ea D N x) 1 (5 / 4) 1 (LX_op_Ea a) hM₂ (LX_op_Ea x)
      linarith
    have hB' : opNorm (((4 / 5 : ℝ) : ℂ) • B₀) ≤ 1 := by
      rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith
    have := LX_event_scale (μ := μ) ((D : ℝ) * (5 / 4))
      ((N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹)) (by positivity)
      (fun h => LX_Q Λ z₁ z₂ a b x h - KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a)
      (fun h => ntr (res (Matrix.of h + Λ) z₂ * Ea D N b * res (Matrix.of h + Λ) z₁ *
          (((4 / 5 : ℝ) : ℂ) • B₀)) - ∑ y, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b y *
          ntr (MExt Λ z₂ * Ea D N y * MExt Λ z₁ * (((4 / 5 : ℝ) : ℂ) • B₀)))
      (fun h => by
        have hcyc : ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * Ea D N x *
            res (Matrix.of h + Λ) z₂ * Ea D N b) =
            ntr (res (Matrix.of h + Λ) z₂ * Ea D N b * res (Matrix.of h + Λ) z₁ * B₀) := by
          rw [show res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * Ea D N x *
              res (Matrix.of h + Λ) z₂ * Ea D N b =
              (res (Matrix.of h + Λ) z₁ * B₀) * (res (Matrix.of h + Λ) z₂ * Ea D N b) by
            simp only [hB₀, Matrix.mul_assoc], LX_ntr_cyc]
          simp only [Matrix.mul_assoc]
        have hsum : ∑ y, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b y *
            ((D : ℂ) * ntr (MExt Λ z₂ * Ea D N y * MExt Λ z₁ * Ea D N a *
              (MExt Λ z₂ * Ea D N x))) =
            (D : ℂ) * ∑ y, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b y *
              ntr (MExt Λ z₂ * Ea D N y * MExt Λ z₁ * B₀) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          simp only [hB₀, Matrix.mul_assoc]
          ring
        simp only [LX_Q, KThetaB, Matrix.mul_smul, LX_ntr_smul]
        have hs2 : ∑ y, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b y *
            (((4 / 5 : ℝ) : ℂ) * ntr (MExt Λ z₂ * Ea D N y * MExt Λ z₁ * B₀)) =
            ((4 / 5 : ℝ) : ℂ) * ∑ y, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b y *
              ntr (MExt Λ z₂ * Ea D N y * MExt Λ z₁ * B₀) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [hcyc, hsum, hs2]
        push_cast
        ring) (hBB _ hB' b)
    exact this
  · filter_upwards [hμh] with h hh
    exact (LX_crude Λ hΛ z hz z₁ z₂ h₁ h₂ hM₁ hM₂ h hh a b c x).2.2.1
  · filter_upwards [hμh] with h hh
    have := (LX_crude Λ hΛ z hz z₁ z₂ h₁ h₂ hM₁ hM₂ h hh a b c x).2.2.2
    calc ‖LX_Q Λ z₁ z₂ a b x h - KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
          ‖LX_Q Λ z₁ z₂ a b x h‖ + ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ :=
          norm_sub_le _ _
      _ ≤ _ := add_le_add this hKt'

end LX_E22

section LX_P

private theorem LX_P_real (D : ℕ) (θ : ℝ) (x c : Fin D) :
    PTheta D θ x c = (((if x = c then θ else 0) + (1 - θ) / D : ℝ) : ℂ) := by
  simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private theorem LX_P_norm_le (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (x c : Fin D) : ‖PTheta D θ x c‖ ≤ 1 := by
  rw [LX_P_real, Complex.norm_real, Real.norm_eq_abs]
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h2 : 0 ≤ (1 - θ) / D := div_nonneg (by linarith) (by linarith)
  have h3 : (1 - θ) / D ≤ 1 - θ := div_le_self (by linarith) hDr
  rw [abs_of_nonneg (by split_ifs <;> linarith)]
  split_ifs <;> linarith

private theorem LX_P_symm (D : ℕ) (θ : ℝ) (x c : Fin D) : PTheta D θ x c = PTheta D θ c x := by
  simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
  by_cases h : x = c
  · subst h; rfl
  · simp [h, Ne.symm h]

private theorem LX_P_row (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (x : Fin D) :
    ∑ c, PTheta D θ x c = 1 := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hP : ∀ c, PTheta D θ x c = (if x = c then (θ : ℂ) else 0) + ((1 - θ : ℝ) : ℂ) / D := by
    intro c
    simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  simp only [hP, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

end LX_P

section LX_alg2

variable {D N : ℕ}

private theorem LX_dsum (f : Fin D → Fin D → ℂ) (β : ℝ) (h : ∀ x c, ‖f x c‖ ≤ β) :
    ‖∑ x, ∑ c, f x c‖ ≤ (D : ℝ) ^ 2 * β := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖∑ c, f x c‖ ≤ ∑ _x : Fin D, (D : ℝ) * β :=
        Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (by
          calc ∑ c, ‖f x c‖ ≤ ∑ _c : Fin D, β := Finset.sum_le_sum fun c _ => h x c
            _ = D * β := by simp)
    _ = _ := by simp; ring

private theorem LX_mulPX_apply (Mh P X : Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ x c, P x c = P c x) (a b : Fin D) :
    (Mh * P * X) a b = ∑ x, ∑ c, P x c * Mh a c * X x b := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hP x c]; ring

private theorem LX_K_eq (Mh P : Matrix (Fin D) (Fin D) ℂ) (hP : ∀ x c, P x c = P c x)
    (hdet : (1 - Mh * P).det ≠ 0) (a b : Fin D) :
    Mh a b + (∑ x, ∑ c, P x c * Mh a c * ((1 - Mh * P)⁻¹ * Mh) x b) - ((1 - Mh * P)⁻¹ * Mh) a b = 0 := by
  have hu : IsUnit (1 - Mh * P) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have h1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  set K := (1 - Mh * P)⁻¹ * Mh with hK
  have h2 : (1 - Mh * P) * K = Mh := by rw [hK, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2' : K - Mh * P * K = Mh := by
    have := h2
    rwa [Matrix.sub_mul, Matrix.one_mul] at this
  have h3 : K = Mh + Mh * P * K := sub_eq_iff_eq_add.mp h2'
  have h4 := congrFun (congrFun h3 a) b
  rw [Matrix.add_apply, LX_mulPX_apply Mh P K hP] at h4
  rw [← h4]; ring

private theorem LX_solve (Mh P X Dm : Matrix (Fin D) (Fin D) ℂ) (hP : ∀ x c, P x c = P c x)
    (hdet : (1 - Mh * P).det ≠ 0)
    (hX : ∀ a b, X a b = (∑ x, ∑ c, P x c * Mh a c * X x b) + Dm a b) :
    X = (1 - Mh * P)⁻¹ * Dm := by
  have hu : IsUnit (1 - Mh * P) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have h1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have h2 : X = Mh * P * X + Dm := by
    ext a b
    rw [Matrix.add_apply, LX_mulPX_apply Mh P X hP]
    exact hX a b
  have h3 : (1 - Mh * P) * X = Dm := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    exact (sub_eq_iff_eq_add').mpr h2
  rw [← h3, ← Matrix.mul_assoc, h1, Matrix.one_mul]

private theorem LX_lead15_smul (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (c : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) : lead15 Λ z (c • B) = c * lead15 Λ z B := by
  unfold lead15
  simp only [Matrix.mul_smul, Matrix.smul_mul, LX_ntr_smul]
  ring

end LX_alg2

section LX_decomp

variable {D N : ℕ}

/-- The coefficient of `θ² κ₀ / N` in the main terms of `𝒟` of (3.40) [ELK]:
`D lead15(E_a M₂ E_b) + D lead14 + Σ_{x,c} (P_θ)_{xc} (K_θ)_{xb} D lead15(E_a M₂ E_c)
+ Σ_{x,c} (P_θ)_{xc} K̃_{θ,ba}(M₂ E_x) D lead15(z₂, E_c)`. -/
private def LX_Main (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (a b : Fin D) : ℂ :=
  (D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b) + (D : ℂ) * lead14 Λ θ z₁ z₂ a b +
    (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
      ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c))) +
    ∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
      ((D : ℂ) * lead15 Λ z₂ (Ea D N c))

/-- The bound for the remainder of `𝒟`. -/
private def LX_ErrBd (D : ℕ) (r r₂₁ ε₁₅ ε₁₄ BE1 BE2 : ℝ) : ℝ :=
  D * (5 / 4) * ε₁₅ + ε₁₄ + (D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) * (D * (5 / 4) * ε₁₅) +
    (D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * ε₁₅) +
    (D : ℝ) ^ 2 * BE1 + (D : ℝ) ^ 2 * BE2

private theorem LX_P15_scale (μ : Measure (Idx D N → Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (κ : ℂ) (ε : ℝ) (H : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * B) ∂μ) - κ * lead15 Λ z B‖ ≤ ε)
    (β : ℝ) (hβ : 0 < β) (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ β) :
    ‖(∫ h, ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * B) ∂μ) - κ * lead15 Λ z B‖ ≤ β * ε := by
  have hB' : opNorm (((β⁻¹ : ℝ) : ℂ) • B) ≤ 1 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
    calc β⁻¹ * opNorm B ≤ β⁻¹ * β := mul_le_mul_of_nonneg_left hB (inv_pos.mpr hβ).le
      _ = 1 := inv_mul_cancel₀ hβ.ne'
  have h := H _ hB'
  have e1 : (∫ h, ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * (((β⁻¹ : ℝ) : ℂ) • B)) ∂μ) =
      ((β⁻¹ : ℝ) : ℂ) * ∫ h, ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * B) ∂μ := by
    simp only [Matrix.mul_smul, LX_ntr_smul]
    exact integral_const_mul _ _
  rw [e1, LX_lead15_smul] at h
  have e2 : (∫ h, ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * B) ∂μ) - κ * lead15 Λ z B =
      ((β : ℝ) : ℂ) * (((β⁻¹ : ℝ) : ℂ) * (∫ h, ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * B) ∂μ) -
        κ * (((β⁻¹ : ℝ) : ℂ) * lead15 Λ z B)) := by
    have : ((β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
    push_cast
    field_simp
  rw [e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  exact mul_le_mul_of_nonneg_left h hβ.le

end LX_decomp

section LX_decomp2

variable {D N : ℕ}

private theorem LX_Kt_bound (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (a b x : Fin D)
    (hM₁ : opNorm (MExt Λ z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt Λ z₂) ≤ 5 / 4) :
    ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
      D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * (5 / 4))) := by
  have hMx : opNorm (MExt Λ z₂ * Ea D N x) ≤ 5 / 4 := by
    have := opNorm_mul_le (MExt Λ z₂) (Ea D N x)
    have := LX_op_Ea (D := D) (N := N) x
    nlinarith [LX_op_nonneg (MExt Λ z₂), LX_op_nonneg (Ea D N x)]
  have hKt := LX_KB_bound Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a hM₂ hM₁
  refine hKt.trans ?_
  have h0 := LX_op_nonneg (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left hMx (by norm_num)

set_option maxHeartbeats 800000 in
private theorem LX_pair_decomp (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (hD : 1 ≤ D) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (hM₁ : opNorm (MExt (lam D N A) z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt (lam D N A) z₂) ≤ 5 / 4)
    (hdet : (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0)
    (κ : ℂ) (ε₁₅ ε₁₄ BE1 BE2 : ℝ) (he15 : 0 ≤ ε₁₅) (he14 : 0 ≤ ε₁₄)
    (H15₁ : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * B) ∂μ) -
        κ * lead15 (lam D N A) z₁ B‖ ≤ ε₁₅)
    (H15₂ : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) * B) ∂μ) -
        κ * lead15 (lam D N A) z₂ B‖ ≤ ε₁₅)
    (H14 : ∀ a b : Fin D, ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) θ h z₁ z₂ a (Ea D N b) ∂μ) -
      ((D : ℂ) * κ) * lead14 (lam D N A) θ z₁ z₂ a b‖ ≤ ε₁₄)
    (hE1 : ∀ a c x b : Fin D, ‖∫ h, LX_X1 (lam D N A) z₁ z₂ a c h *
      (Lmat (lam D N A) h z₁ z₂ x b - KTheta (lam D N A) θ z₁ z₂ x b) ∂μ‖ ≤ BE1)
    (hE2 : ∀ a b c x : Fin D, ‖∫ h, LX_W (lam D N A) z₂ c h * (LX_Q (lam D N A) z₁ z₂ a b x h -
      KThetaB (lam D N A) θ z₂ z₁ (MExt (lam D N A) z₂ * Ea D N x) b a) ∂μ‖ ≤ BE2) :
    ∀ a b : Fin D, ‖(ELmat μ (lam D N A) z₁ z₂ a b - KTheta (lam D N A) θ z₁ z₂ a b) -
      ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a x *
        (κ * LX_Main (lam D N A) θ z₁ z₂ x b)‖ ≤
      D * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ *
        LX_ErrBd D (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)
          (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹) ε₁₅ ε₁₄ BE1 BE2 := by
  set Λ := lam D N A with hΛdef
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hP : ∀ x c, PTheta D θ x c = PTheta D θ c x := LX_P_symm D θ
  have hPn : ∀ x c, ‖PTheta D θ x c‖ ≤ 1 := LX_P_norm_le D hD θ hθ0 hθ1
  have hKdef : KTheta Λ θ z₁ z₂ = (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * Mhat Λ z₁ z₂ := rfl
  set r := opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ with hr
  set r₂₁ := opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ with hr₂₁
  have hr0 : 0 ≤ r := LX_op_nonneg _
  have hr₂₁0 : 0 ≤ r₂₁ := LX_op_nonneg _
  have hBE1 : 0 ≤ BE1 := (norm_nonneg _).trans (hE1 ⟨0, hD⟩ ⟨0, hD⟩ ⟨0, hD⟩ ⟨0, hD⟩)
  have hBE2 : 0 ≤ BE2 := (norm_nonneg _).trans (hE2 ⟨0, hD⟩ ⟨0, hD⟩ ⟨0, hD⟩ ⟨0, hD⟩)
  have hErr0 : 0 ≤ LX_ErrBd D r r₂₁ ε₁₅ ε₁₄ BE1 BE2 := by
    unfold LX_ErrBd; positivity
  -- the two first-order inputs in integrated form
  have hI1 : ∀ a c : Fin D, ‖(∫ h, LX_X1 Λ z₁ z₂ a c h ∂μ) -
      ((D : ℂ) * κ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c)‖ ≤ D * (5 / 4) * ε₁₅ := by
    intro a c
    have hB₀ : opNorm (Ea D N a * MExt Λ z₂ * Ea D N c) ≤ 5 / 4 := by
      have := LX_op3 (Ea D N a) (MExt Λ z₂) (Ea D N c) 1 (5 / 4) 1 (LX_op_Ea a) hM₂ (LX_op_Ea c)
      linarith
    have h := LX_P15_scale μ Λ z₁ κ ε₁₅ H15₁ (5 / 4) (by norm_num) _ hB₀
    have e : (∫ h, LX_X1 Λ z₁ z₂ a c h ∂μ) = (D : ℂ) * ∫ h, ntr ((res (Matrix.of h + Λ) z₁ -
        MExt Λ z₁) * (Ea D N a * MExt Λ z₂ * Ea D N c)) ∂μ := by
      simp only [LX_X1, Matrix.mul_assoc]
      exact integral_const_mul _ _
    rw [e, show ((D : ℂ) * (∫ h, ntr ((res (Matrix.of h + Λ) z₁ - MExt Λ z₁) *
        (Ea D N a * MExt Λ z₂ * Ea D N c)) ∂μ) - (D : ℂ) * κ *
        lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c)) = (D : ℂ) * ((∫ h, ntr ((res (Matrix.of h + Λ) z₁ -
        MExt Λ z₁) * (Ea D N a * MExt Λ z₂ * Ea D N c)) ∂μ) -
        κ * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c)) by ring, norm_mul,
      Complex.norm_natCast]
    calc (D : ℝ) * ‖_‖ ≤ D * (5 / 4 * ε₁₅) := mul_le_mul_of_nonneg_left h hDr.le
      _ = _ := by ring
  have hIW : ∀ c : Fin D, ‖(∫ h, LX_W Λ z₂ c h ∂μ) -
      ((D : ℂ) * κ) * lead15 Λ z₂ (Ea D N c)‖ ≤ D * ε₁₅ := by
    intro c
    have h := H15₂ _ (LX_op_Ea c)
    have e : (∫ h, LX_W Λ z₂ c h ∂μ) = (D : ℂ) * ∫ h, ntr ((res (Matrix.of h + Λ) z₂ -
        MExt Λ z₂) * Ea D N c) ∂μ := by
      simp only [LX_W]
      exact integral_const_mul _ _
    rw [e, show ((D : ℂ) * (∫ h, ntr ((res (Matrix.of h + Λ) z₂ - MExt Λ z₂) * Ea D N c) ∂μ) -
        (D : ℂ) * κ * lead15 Λ z₂ (Ea D N c)) = (D : ℂ) * ((∫ h, ntr ((res (Matrix.of h + Λ) z₂ -
        MExt Λ z₂) * Ea D N c) ∂μ) - κ * lead15 Λ z₂ (Ea D N c)) by ring, norm_mul,
      Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h hDr.le
  -- the remainder, entrywise
  set X : Matrix (Fin D) (Fin D) ℂ := ELmat μ Λ z₁ z₂ - KTheta Λ θ z₁ z₂ with hXdef
  set Dm : Matrix (Fin D) (Fin D) ℂ := fun a b =>
    X a b - ∑ x, ∑ c, PTheta D θ x c * Mhat Λ z₁ z₂ a c * X x b with hDm
  have hDmb : ∀ a b : Fin D, ‖Dm a b - κ * LX_Main Λ θ z₁ z₂ a b‖ ≤
      LX_ErrBd D r r₂₁ ε₁₅ ε₁₄ BE1 BE2 := by
    intro a b
    have hid := LX_pair_identity μ hμh θ A z hz z₁ z₂ h₁ h₂ a b
    have hK0 := LX_K_eq (Mhat Λ z₁ z₂) (PTheta D θ) hP hdet a b
    rw [← hKdef] at hK0
    have hXab : ∀ a b : Fin D, X a b = ELmat μ Λ z₁ z₂ a b - KTheta Λ θ z₁ z₂ a b := fun a b => by
      simp [hXdef, Matrix.sub_apply]
    have hu3 : (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
          (∫ h, LX_X1 Λ z₁ z₂ a c h ∂μ)) - κ * ∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
          ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c)) =
        ∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b * ((∫ h, LX_X1 Λ z₁ z₂ a c h ∂μ) -
          ((D : ℂ) * κ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hu4 : (∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
          (∫ h, LX_W Λ z₂ c h ∂μ)) - κ * ∑ x, ∑ c, PTheta D θ x c *
          KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a * ((D : ℂ) * lead15 Λ z₂ (Ea D N c)) =
        ∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
          ((∫ h, LX_W Λ z₂ c h ∂μ) - ((D : ℂ) * κ) * lead15 Λ z₂ (Ea D N c)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hsplit : Dm a b - κ * LX_Main Λ θ z₁ z₂ a b =
        ((∫ h, LX_X1 Λ z₁ z₂ a b h ∂μ) - ((D : ℂ) * κ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b)) +
        (-(D : ℂ) * (∫ h, underTwoB Λ θ h z₁ z₂ a (Ea D N b) ∂μ) -
          ((D : ℂ) * κ) * lead14 Λ θ z₁ z₂ a b) +
        (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b * ((∫ h, LX_X1 Λ z₁ z₂ a c h ∂μ) -
          ((D : ℂ) * κ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c))) +
        (∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
          ((∫ h, LX_W Λ z₂ c h ∂μ) - ((D : ℂ) * κ) * lead15 Λ z₂ (Ea D N c))) +
        (∑ x, ∑ c, PTheta D θ x c * (∫ h, LX_X1 Λ z₁ z₂ a c h *
          (Lmat Λ h z₁ z₂ x b - KTheta Λ θ z₁ z₂ x b) ∂μ)) +
        ∑ x, ∑ c, PTheta D θ x c * (∫ h, LX_W Λ z₂ c h * (LX_Q Λ z₁ z₂ a b x h -
          KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a) ∂μ) := by
      simp only [hDm, hXab]
      unfold LX_Main
      linear_combination hid + hK0 + hu3 + hu4
    rw [hsplit]
    have n1 := hI1 a b
    have n2 := H14 a b
    have n3 : ‖∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b * ((∫ h, LX_X1 Λ z₁ z₂ a c h ∂μ) -
          ((D : ℂ) * κ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c))‖ ≤
        (D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) * (D * (5 / 4) * ε₁₅) := by
      rw [mul_assoc]
      refine LX_dsum _ _ fun x c => ?_
      rw [norm_mul, norm_mul]
      have hk := LX_K_bound Λ θ z₁ z₂ x b hM₁ hM₂
      rw [← hr] at hk
      have hI := hI1 a c
      have h0 : 0 ≤ (D : ℝ) * r * (D * (25 / 16)) := by positivity
      have hPK : ‖PTheta D θ x c‖ * ‖KTheta Λ θ z₁ z₂ x b‖ ≤ D * r * (D * (25 / 16)) := by
        calc ‖PTheta D θ x c‖ * ‖KTheta Λ θ z₁ z₂ x b‖ ≤ 1 * (D * r * (D * (25 / 16))) :=
              mul_le_mul (hPn x c) hk (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      exact mul_le_mul hPK hI (norm_nonneg _) h0
    have n4 : ‖∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
          ((∫ h, LX_W Λ z₂ c h ∂μ) - ((D : ℂ) * κ) * lead15 Λ z₂ (Ea D N c))‖ ≤
        (D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * ε₁₅) := by
      rw [mul_assoc]
      refine LX_dsum _ _ fun x c => ?_
      rw [norm_mul, norm_mul]
      have hk := LX_Kt_bound Λ θ z₁ z₂ a b x hM₁ hM₂
      rw [← hr₂₁] at hk
      have hI := hIW c
      have h0 : 0 ≤ (D : ℝ) * r₂₁ * (D * ((25 / 16) * (5 / 4))) := by positivity
      have hPK : ‖PTheta D θ x c‖ * ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
          D * r₂₁ * (D * ((25 / 16) * (5 / 4))) := by
        calc ‖PTheta D θ x c‖ * ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
              1 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) :=
              mul_le_mul (hPn x c) hk (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      exact mul_le_mul hPK hI (norm_nonneg _) h0
    have n5 : ‖∑ x, ∑ c, PTheta D θ x c * (∫ h, LX_X1 Λ z₁ z₂ a c h *
          (Lmat Λ h z₁ z₂ x b - KTheta Λ θ z₁ z₂ x b) ∂μ)‖ ≤ (D : ℝ) ^ 2 * BE1 := by
      refine LX_dsum _ _ fun x c => ?_
      rw [norm_mul]
      calc ‖PTheta D θ x c‖ * _ ≤ 1 * BE1 := mul_le_mul (hPn x c) (hE1 a c x b) (norm_nonneg _)
            zero_le_one
        _ = BE1 := one_mul _
    have n6 : ‖∑ x, ∑ c, PTheta D θ x c * (∫ h, LX_W Λ z₂ c h * (LX_Q Λ z₁ z₂ a b x h -
          KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a) ∂μ)‖ ≤ (D : ℝ) ^ 2 * BE2 := by
      refine LX_dsum _ _ fun x c => ?_
      rw [norm_mul]
      calc ‖PTheta D θ x c‖ * _ ≤ 1 * BE2 := mul_le_mul (hPn x c) (hE2 a b c x) (norm_nonneg _)
            zero_le_one
        _ = BE2 := one_mul _
    unfold LX_ErrBd
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) n6
    refine add_le_add ((norm_add_le _ _).trans ?_) n5
    refine add_le_add ((norm_add_le _ _).trans ?_) n4
    refine add_le_add ((norm_add_le _ _).trans ?_) n3
    linarith
  have hX : ∀ a b : Fin D, X a b = (∑ x, ∑ c, PTheta D θ x c * Mhat Λ z₁ z₂ a c * X x b) +
      Dm a b := fun a b => by simp [hDm]
  have hsol := LX_solve (Mhat Λ z₁ z₂) (PTheta D θ) X Dm hP hdet hX
  intro a b
  have e1 : X a b = ∑ x, (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x * Dm x b := by
    rw [hsol, Matrix.mul_apply]
  have e2 : X a b - ∑ x, (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x * (κ * LX_Main Λ θ z₁ z₂ x b) =
      ∑ x, (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x * (Dm x b - κ * LX_Main Λ θ z₁ z₂ x b) := by
    rw [e1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  show ‖X a b - _‖ ≤ _
  rw [e2]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖(1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x * (Dm x b - κ * LX_Main Λ θ z₁ z₂ x b)‖
      ≤ ∑ _x : Fin D, r * LX_ErrBd D r r₂₁ ε₁₅ ε₁₄ BE1 BE2 := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul]
        exact mul_le_mul (norm_apply_le_opNorm _ a x) (hDmb x b) (norm_nonneg _) hr0
    _ = _ := by simp; ring

end LX_decomp2

section LX_Mf

private theorem LX_MExt_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z ∧ MExt Λ z = MSol Λ z := by
  have hm : mExt Λ z = mSol Λ z := by simp only [mExt, hz, ↓reduceIte]
  exact ⟨hm, by rw [MExt, MSol, hm]⟩

private theorem LX_ntr_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ntr (lam D N A) = 0 := by
  have hf : ∀ a : Fin D, ¬ fwd D a a := fun a => by unfold fwd; omega
  have h : ∀ p : Idx D N, lam D N A p p = 0 := fun p => by simp [lam, hf]
  simp [ntr, Matrix.trace, Matrix.diag, h]

private theorem LX_Mfacts (τ : ℝ) (hτ : 0 < τ) : ∃ Cm : ℝ, 0 < Cm ∧ ∀ (D N : ℕ), 1 ≤ D → 1 ≤ N →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm (lam D N A) ≤ 1 / 10 →
    ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ : ℂ, (z₁ = z ∨ z₁ = star z) →
      opNorm (MExt (lam D N A) z₁) ≤ 5 / 4 ∧ ‖mExt (lam D N A) z₁‖ ≤ 1 ∧
        opNorm (MExt (lam D N A) z₁ - mExt (lam D N A) z₁ • 1) ≤ Cm * opNorm (lam D N A) := by
  obtain ⟨Cm, hCm, hmsc⟩ := eq_msc_traceless τ hτ
  refine ⟨Cm, hCm, fun D N hD hN A hA z hzn hz z₁ h₁ => ?_⟩
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨hm, hM⟩ := LX_MExt_pos (lam D N A) z hz
  obtain ⟨a1, a2, a3⟩ := mSol_apriori (lam D N A) hΛ hA z hz
  have hL0 := LX_op_nonneg (lam D N A)
  have hb : opNorm (MExt (lam D N A) z) ≤ 5 / 4 := by
    rw [hM]
    refine a3.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hsm : ‖mExt (lam D N A) z‖ ≤ 1 := by rw [hm]; exact a2.le
  have hk : opNorm (MExt (lam D N A) z - mExt (lam D N A) z • 1) ≤ Cm * opNorm (lam D N A) := by
    have h := hmsc (Idx D N) (lam D N A) hΛ hA (LX_ntr_lam D N A) z hzn hz
    rw [hm, hM]
    have e : MSol (lam D N A) z - mSol (lam D N A) z • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
        (MSol (lam D N A) z - msc z • 1) + (msc z - mSol (lam D N A) z) • 1 := by
      rw [sub_smul]; abel
    rw [e]
    refine (opNorm_add_le _ _).trans ?_
    rw [opNorm_smul]
    have := LX_op_one (ι := Idx D N)
    have h0 := norm_nonneg (msc z - mSol (lam D N A) z)
    rw [norm_sub_rev] at h0 ⊢
    nlinarith
  rcases h₁ with rfl | rfl
  · exact ⟨hb, hsm, hk⟩
  · obtain ⟨c1, c2⟩ := mExt_conj (lam D N A) hΛ z hz.ne'
    rw [c1, c2]
    refine ⟨by rw [LX_op_conj]; exact hb, by rw [norm_star]; exact hsm, ?_⟩
    have e : (MExt (lam D N A) z)ᴴ - star (mExt (lam D N A) z) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ) =
        (MExt (lam D N A) z - mExt (lam D N A) z • 1)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rw [e, LX_op_conj]
    exact hk

private theorem LX_Dntr_le (D N : ℕ) (Y : Matrix (Idx D N) (Idx D N) ℂ) (y : Fin D) :
    ‖(D : ℂ) * ntr (Y * Ea D N y)‖ ≤ opNorm Y := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [ntr, Matrix.trace]; exact LX_op_nonneg Y
  have hD0 : (D : ℝ) ≠ 0 := by have := y.pos; exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [LX_ntr_Ea, ← mul_assoc, norm_mul]
  have e : ‖(D : ℂ) * ((D : ℂ) * N)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [mul_inv, ← mul_assoc, norm_mul, norm_mul, Complex.norm_natCast, norm_inv, norm_inv,
      Complex.norm_natCast, Complex.norm_natCast, mul_inv_cancel₀ hD0, one_mul]
  rw [e]
  have hs : ‖∑ i, (if i.1 = y then Y i i else 0)‖ ≤ N * opNorm Y := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(if i.1 = y then Y i i else 0)‖ ≤ ∑ i : Idx D N, (if i.1 = y then opNorm Y else 0) :=
          Finset.sum_le_sum fun i _ => by
            split_ifs
            · exact norm_apply_le_opNorm Y i i
            · simp
      _ = N * opNorm Y := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          rw [Finset.sum_eq_single y]
          · simp
          · intro b _ hb; simp [hb]
          · simp
  calc (N : ℝ)⁻¹ * ‖∑ i, (if i.1 = y then Y i i else 0)‖ ≤ (N : ℝ)⁻¹ * (N * opNorm Y) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = opNorm Y := by field_simp

end LX_Mf

section LX_frozen

variable {D N : ℕ}

/-- `X` and `Y` are within `ε` of each other and both of norm at most `2`. -/
private def LX_Ap (ε : ℝ) (X Y : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  opNorm X ≤ 2 ∧ opNorm Y ≤ 2 ∧ opNorm (X - Y) ≤ ε

private theorem LX_Ap_refl (ε : ℝ) (hε : 0 ≤ ε) (X : Matrix (Idx D N) (Idx D N) ℂ)
    (hX : opNorm X ≤ 2) : LX_Ap ε X X := by
  refine ⟨hX, hX, ?_⟩
  rw [sub_self]
  unfold opNorm
  simpa using hε

private theorem LX_apx_ntr (ε : ℝ) (hε : 0 ≤ ε) (l l' : List (Matrix (Idx D N) (Idx D N) ℂ))
    (h : List.Forall₂ (LX_Ap ε) l l') :
    ‖ntr l.prod - ntr l'.prod‖ ≤ l.length * ε * 2 ^ l.length := by
  have := LX_prod_approx 2 ε (by norm_num) hε l l' h
  rw [← LX_ntr_sub]
  exact (LX_ntr_le _).trans this.2.2

/-- Frozen model: `M = m + Δ`. -/
private structure LX_Fz (M : Matrix (Idx D N) (Idx D N) ℂ) (m : ℂ) (ε : ℝ) : Prop where
  hM : opNorm M ≤ 5 / 4
  hm : ‖m‖ ≤ 1
  hΔ : opNorm (M - m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ ε
  hε : 0 ≤ ε

private theorem LX_Fz.apM {M : Matrix (Idx D N) (Idx D N) ℂ} {m : ℂ} {ε : ℝ} (h : LX_Fz M m ε) :
    LX_Ap ε M (m • 1) :=
  ⟨by linarith [h.hM], (LX_op_scal m).trans (by linarith [h.hm]), h.hΔ⟩

private theorem LX_Fz.apD {M : Matrix (Idx D N) (Idx D N) ℂ} {m : ℂ} {ε : ℝ} (h : LX_Fz M m ε) :
    LX_Ap ε (diagonal (diag M)) (m • 1) := by
  obtain ⟨h1, h2⟩ := LX_dg_le M m
  exact ⟨(h2.trans h.hM).trans (by norm_num), (LX_op_scal m).trans (by linarith [h.hm]),
    h1.trans h.hΔ⟩

private theorem LX_Ap_Ea {ε : ℝ} (hε : 0 ≤ ε) (a : Fin D) : LX_Ap ε (Ea D N a) (Ea D N a) :=
  LX_Ap_refl ε hε _ ((LX_op_Ea a).trans (by norm_num))

/-- Approximation of the normalized trace of a product by that of a frozen product. -/
private theorem LX_apx (ε : ℝ) (hε : 0 ≤ ε) (l l' : List (Matrix (Idx D N) (Idx D N) ℂ))
    (h : List.Forall₂ (LX_Ap ε) l l') (X v : ℂ) (K : ℝ) (hX : ntr l.prod = X) (hv : ntr l'.prod = v)
    (hK : (l.length : ℝ) * 2 ^ l.length ≤ K) : ‖X - v‖ ≤ K * ε := by
  have := LX_apx_ntr ε hε l l' h
  rw [hX, hv] at this
  refine this.trans ?_
  calc (l.length : ℝ) * ε * 2 ^ l.length = ((l.length : ℝ) * 2 ^ l.length) * ε := by ring
    _ ≤ K * ε := mul_le_mul_of_nonneg_right hK hε

/-- The same for matrices: `‖Π X_i - Π Y_i‖ ≤ K ε`. -/
private theorem LX_apx_mat (ε : ℝ) (hε : 0 ≤ ε) (l l' : List (Matrix (Idx D N) (Idx D N) ℂ))
    (h : List.Forall₂ (LX_Ap ε) l l') (X Y : Matrix (Idx D N) (Idx D N) ℂ) (K : ℝ)
    (hX : l.prod = X) (hY : l'.prod = Y) (hK : (l.length : ℝ) * 2 ^ l.length ≤ K) :
    opNorm (X - Y) ≤ K * ε := by
  have := (LX_prod_approx 2 ε (by norm_num) hε l l' h).2.2
  rw [hX, hY] at this
  refine this.trans ?_
  calc (l.length : ℝ) * ε * 2 ^ l.length = ((l.length : ℝ) * 2 ^ l.length) * ε := by ring
    _ ≤ K * ε := mul_le_mul_of_nonneg_right hK hε

/-- The algebra behind `lead15` (3.42) [eq:Exp_G1-M1] with `M = m + Δ`. -/
private theorem LX_cplx_frozen (s₁ s₂ s₃ s₄ s₅ m t : ℂ) (ε Cd : ℝ) (hε : 0 ≤ ε) (hm : ‖m‖ ≤ 1)
    (ht : ‖t‖ ≤ 2) (b₁ : ‖s₁‖ ≤ 2) (b₂ : ‖s₂‖ ≤ 4) (b₃ : ‖s₃‖ ≤ 2) (b₄ : ‖s₄‖ ≤ 4)
    (b₅ : ‖s₅‖ ≤ 2) (h1 : ‖s₁ - m ^ 2‖ ≤ 8 * ε) (h2 : ‖s₂ - m ^ 3 * t‖ ≤ 64 * ε)
    (h3 : ‖s₃ - m ^ 3‖ ≤ 24 * ε) (h4 : ‖s₄ - m ^ 2 * t‖ ≤ 24 * ε) (h5 : ‖s₅ - m ^ 2‖ ≤ 8 * ε)
    (hd : 1 - s₅ ≠ 0) (hC : ‖1 - s₅‖⁻¹ ≤ Cd) :
    ‖s₁ * (s₂ + s₃ * s₄ / (1 - s₅)) - m ^ 5 * t / (1 - s₅)‖ ≤ 500 * Cd * ε := by
  have hm2 : ‖m ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  have hm3 : ‖m ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  have hm5 : ‖m ^ 5‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  have hd0 : 0 < ‖1 - s₅‖ := norm_pos_iff.mpr hd
  have hdb : ‖1 - s₅‖ ≤ 3 := by
    have := norm_sub_le (1 : ℂ) s₅
    rw [norm_one] at this; linarith
  have hA : ‖s₁ * s₂ - m ^ 5 * t‖ ≤ 96 * ε := by
    have e : s₁ * s₂ - m ^ 5 * t = (s₁ - m ^ 2) * s₂ + m ^ 2 * (s₂ - m ^ 3 * t) := by ring
    have t1 : ‖(s₁ - m ^ 2) * s₂‖ ≤ 32 * ε := by
      rw [norm_mul]
      calc ‖s₁ - m ^ 2‖ * ‖s₂‖ ≤ (8 * ε) * 4 :=
            mul_le_mul h1 b₂ (norm_nonneg _) (by linarith)
        _ = 32 * ε := by ring
    have t2 : ‖m ^ 2 * (s₂ - m ^ 3 * t)‖ ≤ 64 * ε := by
      rw [norm_mul]
      calc ‖m ^ 2‖ * ‖s₂ - m ^ 3 * t‖ ≤ 1 * (64 * ε) :=
            mul_le_mul hm2 h2 (norm_nonneg _) zero_le_one
        _ = 64 * ε := one_mul _
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 96 * ε := by linarith
  have hB : ‖s₁ * s₃ * s₄ - m ^ 7 * t‖ ≤ 184 * ε := by
    have e : s₁ * s₃ * s₄ - m ^ 7 * t = (s₁ - m ^ 2) * (s₃ * s₄) + m ^ 2 * (s₃ - m ^ 3) * s₄ +
        m ^ 5 * (s₄ - m ^ 2 * t) := by ring
    have t1 : ‖(s₁ - m ^ 2) * (s₃ * s₄)‖ ≤ 64 * ε := by
      rw [norm_mul, norm_mul]
      calc ‖s₁ - m ^ 2‖ * (‖s₃‖ * ‖s₄‖) ≤ (8 * ε) * (2 * 4) :=
            mul_le_mul h1 (mul_le_mul b₃ b₄ (norm_nonneg _) (by norm_num)) (by positivity)
              (by linarith)
        _ = 64 * ε := by ring
    have t2 : ‖m ^ 2 * (s₃ - m ^ 3) * s₄‖ ≤ 96 * ε := by
      rw [norm_mul, norm_mul]
      calc ‖m ^ 2‖ * ‖s₃ - m ^ 3‖ * ‖s₄‖ ≤ (1 * (24 * ε)) * 4 :=
            mul_le_mul (mul_le_mul hm2 h3 (norm_nonneg _) zero_le_one) b₄ (norm_nonneg _)
              (by linarith)
        _ = 96 * ε := by ring
    have t3 : ‖m ^ 5 * (s₄ - m ^ 2 * t)‖ ≤ 24 * ε := by
      rw [norm_mul]
      calc ‖m ^ 5‖ * ‖s₄ - m ^ 2 * t‖ ≤ 1 * (24 * ε) :=
            mul_le_mul hm5 h4 (norm_nonneg _) zero_le_one
        _ = 24 * ε := one_mul _
    rw [e]
    calc _ ≤ _ := norm_add₃_le
      _ ≤ 184 * ε := by linarith
  have hN : ‖s₁ * s₂ * (1 - s₅) + s₁ * s₃ * s₄ - m ^ 5 * t‖ ≤ 500 * ε := by
    have e : s₁ * s₂ * (1 - s₅) + s₁ * s₃ * s₄ - m ^ 5 * t = (s₁ * s₂ - m ^ 5 * t) * (1 - s₅) +
        (s₁ * s₃ * s₄ - m ^ 7 * t) - m ^ 5 * t * (s₅ - m ^ 2) := by ring
    have t1 : ‖(s₁ * s₂ - m ^ 5 * t) * (1 - s₅)‖ ≤ 288 * ε := by
      rw [norm_mul]
      calc ‖s₁ * s₂ - m ^ 5 * t‖ * ‖1 - s₅‖ ≤ (96 * ε) * 3 :=
            mul_le_mul hA hdb (norm_nonneg _) (by linarith)
        _ = 288 * ε := by ring
    have t3 : ‖m ^ 5 * t * (s₅ - m ^ 2)‖ ≤ 16 * ε := by
      rw [norm_mul, norm_mul]
      calc ‖m ^ 5‖ * ‖t‖ * ‖s₅ - m ^ 2‖ ≤ (1 * 2) * (8 * ε) :=
            mul_le_mul (mul_le_mul hm5 ht (norm_nonneg _) zero_le_one) h5 (norm_nonneg _)
              (by norm_num)
        _ = 16 * ε := by ring
    rw [e]
    calc _ ≤ ‖(s₁ * s₂ - m ^ 5 * t) * (1 - s₅) + (s₁ * s₃ * s₄ - m ^ 7 * t)‖ +
          ‖m ^ 5 * t * (s₅ - m ^ 2)‖ := norm_sub_le _ _
      _ ≤ ‖(s₁ * s₂ - m ^ 5 * t) * (1 - s₅)‖ + ‖s₁ * s₃ * s₄ - m ^ 7 * t‖ +
          ‖m ^ 5 * t * (s₅ - m ^ 2)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 500 * ε := by linarith
  have e : s₁ * (s₂ + s₃ * s₄ / (1 - s₅)) - m ^ 5 * t / (1 - s₅) =
      (s₁ * s₂ * (1 - s₅) + s₁ * s₃ * s₄ - m ^ 5 * t) / (1 - s₅) := by
    rw [eq_div_iff hd]
    field_simp
  rw [e, norm_div, div_eq_mul_inv]
  calc ‖s₁ * s₂ * (1 - s₅) + s₁ * s₃ * s₄ - m ^ 5 * t‖ * ‖1 - s₅‖⁻¹ ≤ (500 * ε) * Cd :=
        mul_le_mul hN hC (inv_nonneg.mpr hd0.le) (by linarith)
    _ = 500 * Cd * ε := by ring

end LX_frozen

section LX_lead15

variable {D N : ℕ}

private theorem LX_lead15_crude (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (β Cd : ℝ) (hM : opNorm (MExt Λ z) ≤ 5 / 4)
    (hB : opNorm B ≤ β) (hd : 1 - ntr (MExt Λ z * MExt Λ z) ≠ 0)
    (hC : ‖1 - ntr (MExt Λ z * MExt Λ z)‖⁻¹ ≤ Cd) :
    ‖lead15 Λ z B‖ ≤ 2 * (2 * β + 2 * (2 * β) * Cd) := by
  have hβ : 0 ≤ β := (LX_op_nonneg B).trans hB
  have hd0 : 0 < ‖1 - ntr (MExt Λ z * MExt Λ z)‖ := norm_pos_iff.mpr hd
  have hC0 : 0 ≤ Cd := (inv_nonneg.mpr hd0.le).trans hC
  set M := MExt Λ z with hMdef
  have hdM : opNorm (diagonal (diag M)) ≤ 5 / 4 := (LX_dg_le M 0).2.trans hM
  have s1 : ‖ntr (diagonal (diag M) * diagonal (diag M))‖ ≤ 2 := by
    refine (LX_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
    nlinarith [LX_op_nonneg (diagonal (diag M))]
  have s2 : ‖ntr (M * B * M * diagonal (diag M))‖ ≤ 2 * β := by
    refine (LX_ntr_le _).trans ((LX_op4 M B M _ (5 / 4) β (5 / 4) (5 / 4) hM hB hM hdM).trans ?_)
    nlinarith
  have s3 : ‖ntr (M * M * diagonal (diag M))‖ ≤ 2 := by
    refine (LX_ntr_le _).trans ((LX_op3 M M _ (5 / 4) (5 / 4) (5 / 4) hM hM hdM).trans ?_)
    norm_num
  have s4 : ‖ntr (M * M * B)‖ ≤ 2 * β := by
    refine (LX_ntr_le _).trans ((LX_op3 M M B (5 / 4) (5 / 4) β hM hM hB).trans ?_)
    nlinarith
  have hinv : ‖(1 - ntr (M * M))⁻¹‖ ≤ Cd := by rwa [norm_inv]
  unfold lead15
  rw [← hMdef, norm_mul]
  have t : ‖ntr (M * B * M * diagonal (diag M)) + ntr (M * M * diagonal (diag M)) *
      ntr (M * M * B) / (1 - ntr (M * M))‖ ≤ 2 * β + 2 * (2 * β) * Cd := by
    refine (norm_add_le _ _).trans (add_le_add s2 ?_)
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul s3 s4 (norm_nonneg _) (by norm_num)) hinv (norm_nonneg _)
      (by positivity)
  exact mul_le_mul s1 t (norm_nonneg _) (by norm_num)

private theorem LX_lead15_frozen [Nonempty (Idx D N)] (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z m : ℂ)
    (ε Cd : ℝ) (hF : LX_Fz (MExt Λ z) m ε) (hd : 1 - ntr (MExt Λ z * MExt Λ z) ≠ 0)
    (hC : ‖1 - ntr (MExt Λ z * MExt Λ z)‖⁻¹ ≤ Cd) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (hB : opNorm B ≤ 2) :
    ‖lead15 Λ z B - m ^ 5 * ntr B / (1 - ntr (MExt Λ z * MExt Λ z))‖ ≤ 500 * Cd * ε := by
  have hM := hF.hM
  have hε := hF.hε
  set M := MExt Λ z with hMdef
  have hdM : opNorm (diagonal (diag M)) ≤ 5 / 4 := (LX_dg_le M 0).2.trans hM
  have apM := hF.apM
  have apD := hF.apD
  have apB : LX_Ap ε B B := LX_Ap_refl ε hε B hB
  have simpset : True := trivial
  have a1 := LX_apx ε hε [diagonal (diag M), diagonal (diag M)] [m • 1, m • 1]
    (List.Forall₂.cons apD (List.Forall₂.cons apD List.Forall₂.nil))
    (ntr (diagonal (diag M) * diagonal (diag M))) (m ^ 2) 8
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one])
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, LX_ntr_smul, LX_ntr_one]; ring)
    (by norm_num)
  have a2 := LX_apx ε hε [M, B, M, diagonal (diag M)] [m • 1, B, m • 1, m • 1]
    (List.Forall₂.cons apM (List.Forall₂.cons apB (List.Forall₂.cons apM
      (List.Forall₂.cons apD List.Forall₂.nil))))
    (ntr (M * B * M * diagonal (diag M))) (m ^ 3 * ntr B) 64
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul, LX_ntr_smul]; ring)
    (by norm_num)
  have a3 := LX_apx ε hε [M, M, diagonal (diag M)] [m • 1, m • 1, m • 1]
    (List.Forall₂.cons apM (List.Forall₂.cons apM (List.Forall₂.cons apD List.Forall₂.nil)))
    (ntr (M * M * diagonal (diag M))) (m ^ 3) 24
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul, LX_ntr_smul, LX_ntr_one]; ring)
    (by norm_num)
  have a4 := LX_apx ε hε [M, M, B] [m • 1, m • 1, B]
    (List.Forall₂.cons apM (List.Forall₂.cons apM (List.Forall₂.cons apB List.Forall₂.nil)))
    (ntr (M * M * B)) (m ^ 2 * ntr B) 24
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul, LX_ntr_smul]; ring)
    (by norm_num)
  have a5 := LX_apx ε hε [M, M] [m • 1, m • 1]
    (List.Forall₂.cons apM (List.Forall₂.cons apM List.Forall₂.nil))
    (ntr (M * M)) (m ^ 2) 8
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one])
    (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, LX_ntr_smul, LX_ntr_one]; ring)
    (by norm_num)
  have s1 : ‖ntr (diagonal (diag M) * diagonal (diag M))‖ ≤ 2 := by
    refine (LX_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
    nlinarith [LX_op_nonneg (diagonal (diag M))]
  have s2 : ‖ntr (M * B * M * diagonal (diag M))‖ ≤ 4 := by
    refine (LX_ntr_le _).trans ((LX_op4 M B M _ (5 / 4) 2 (5 / 4) (5 / 4) hM hB hM hdM).trans ?_)
    norm_num
  have s3 : ‖ntr (M * M * diagonal (diag M))‖ ≤ 2 := by
    refine (LX_ntr_le _).trans ((LX_op3 M M _ (5 / 4) (5 / 4) (5 / 4) hM hM hdM).trans ?_)
    norm_num
  have s4 : ‖ntr (M * M * B)‖ ≤ 4 := by
    refine (LX_ntr_le _).trans ((LX_op3 M M B (5 / 4) (5 / 4) 2 hM hM hB).trans ?_)
    norm_num
  have s5 : ‖ntr (M * M)‖ ≤ 2 := by
    refine (LX_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
    nlinarith [LX_op_nonneg M]
  have ht : ‖ntr B‖ ≤ 2 := (LX_ntr_le _).trans hB
  unfold lead15
  rw [← hMdef]
  exact LX_cplx_frozen _ _ _ _ _ m (ntr B) ε Cd hε hF.hm ht s1 s2 s3 s4 s5 a1 a2 a3 a4 a5 hd hC

end LX_lead15

section LX_lead14

variable {D N : ℕ}

private theorem LX_KB_sub (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (B B' : Matrix (Idx D N) (Idx D N) ℂ) (a b : Fin D) :
    KThetaB Λ θ z₁ z₂ (B - B') a b = KThetaB Λ θ z₁ z₂ B a b - KThetaB Λ θ z₁ z₂ B' a b := by
  unfold KThetaB
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_sub, LX_ntr_sub]
  ring

private theorem LX_KB_smul (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (c : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (a b : Fin D) :
    KThetaB Λ θ z₁ z₂ (c • B) a b = c * KThetaB Λ θ z₁ z₂ B a b := by
  unfold KThetaB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_smul, LX_ntr_smul]
  ring

/-- One term of `lead14`: a scalar `D ⟨Y E_x⟩` times an entry of `K̃_θ(B)`, against the frozen term. -/
private theorem LX_term (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (hM₁ : opNorm (MExt Λ z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt Λ z₂) ≤ 5 / 4)
    (Y Y₀ B B₀ : Matrix (Idx D N) (Idx D N) ℂ) (x a' b' : Fin D) (eY eB : ℝ)
    (hY : opNorm (Y - Y₀) ≤ eY) (hY₀ : opNorm Y₀ ≤ 1) (hB : opNorm B ≤ 2)
    (hBB : opNorm (B - B₀) ≤ eB) :
    ‖((D : ℂ) * ntr (Y * Ea D N x)) * KThetaB Λ θ z₂ z₁ B a' b' -
      ((D : ℂ) * ntr (Y₀ * Ea D N x)) * KThetaB Λ θ z₂ z₁ B₀ a' b'‖ ≤
      eY * (D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * 2))) +
        D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * eB)) := by
  have e : ((D : ℂ) * ntr (Y * Ea D N x)) * KThetaB Λ θ z₂ z₁ B a' b' -
      ((D : ℂ) * ntr (Y₀ * Ea D N x)) * KThetaB Λ θ z₂ z₁ B₀ a' b' =
      ((D : ℂ) * ntr ((Y - Y₀) * Ea D N x)) * KThetaB Λ θ z₂ z₁ B a' b' +
      ((D : ℂ) * ntr (Y₀ * Ea D N x)) * KThetaB Λ θ z₂ z₁ (B - B₀) a' b' := by
    rw [LX_KB_sub, Matrix.sub_mul, LX_ntr_sub]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    have h1 := (LX_Dntr_le D N (Y - Y₀) x).trans hY
    have h2 := (LX_KB_bound Λ θ z₂ z₁ B a' b' hM₂ hM₁).trans (le_of_eq rfl)
    have h3 : ‖KThetaB Λ θ z₂ z₁ B a' b'‖ ≤
        D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * 2)) := by
      refine h2.trans ?_
      have := LX_op_nonneg (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hB (by norm_num)
    exact mul_le_mul h1 h3 (norm_nonneg _) ((norm_nonneg _).trans h1)
  · rw [norm_mul]
    have h1 := (LX_Dntr_le D N Y₀ x).trans hY₀
    have h2 := LX_KB_bound Λ θ z₂ z₁ (B - B₀) a' b' hM₂ hM₁
    have h3 : ‖KThetaB Λ θ z₂ z₁ (B - B₀) a' b'‖ ≤
        D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * eB)) := by
      refine h2.trans ?_
      have := LX_op_nonneg (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hBB (by norm_num)
    calc _ ≤ 1 * (D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * eB))) :=
          mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end LX_lead14

section LX_lead14b

variable {D N : ℕ}

private theorem LX_DntrEE [Nonempty (Idx D N)] (hN : 1 ≤ N) (a x : Fin D) :
    (D : ℂ) * ntr (Ea D N a * Ea D N x) = if a = x then 1 else 0 := by
  rw [LX_Ea_mul]
  split_ifs
  · exact LX_Dntr_Ea hN x
  · simp [ntr]

private theorem LX_lead14_frozen [Nonempty (Idx D N)] (hN : 1 ≤ N)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ m₁ m₂ : ℂ) (ε : ℝ)
    (hF₁ : LX_Fz (MExt Λ z₁) m₁ ε) (hF₂ : LX_Fz (MExt Λ z₂) m₂ ε)
    (hc3 : ∀ a b x : Fin D, KThetaB Λ θ z₂ z₁ (Ea D N a) b x =
      if x = a then KTheta Λ θ z₁ z₂ a b else 0)
    (hc4 : ∀ b x : Fin D, KThetaB Λ θ z₂ z₁ 1 b x = KTheta Λ θ z₁ z₂ x b) (a b : Fin D) :
    ‖(D : ℂ) * lead14 Λ θ z₁ z₂ a b -
      (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b‖ ≤
      4 * D * (64 * ε * (D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * 2))) +
        D * opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ * (D * ((25 / 16) * (24 * ε)))) := by
  have hε := hF₁.hε
  have hM₁ := hF₁.hM
  have hM₂ := hF₂.hM
  have hm₁ := hF₁.hm
  have hm₂ := hF₂.hm
  set M₁ := MExt Λ z₁ with hM₁def
  set M₂ := MExt Λ z₂ with hM₂def
  have apM₁ := hF₁.apM
  have apM₂ := hF₂.apM
  have apD₁ := hF₁.apD
  have apD₂ := hF₂.apD
  have apE : ∀ x : Fin D, LX_Ap ε (Ea D N x) (Ea D N x) := LX_Ap_Ea hε
  have hdM₁ : opNorm (diagonal (diag M₁)) ≤ 5 / 4 := (LX_dg_le M₁ 0).2.trans hM₁
  have hdM₂ : opNorm (diagonal (diag M₂)) ≤ 5 / 4 := (LX_dg_le M₂ 0).2.trans hM₂
  have hmm : ∀ c : ℂ, ‖c‖ ≤ 1 → opNorm (c • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 1 :=
    fun c hc => (LX_op_scal c).trans hc
  have hmE : ∀ (c : ℂ), ‖c‖ ≤ 1 → ∀ x : Fin D, opNorm (c • Ea D N x) ≤ 1 := by
    intro c hc x
    rw [opNorm_smul]
    have := LX_op_Ea (D := D) (N := N) x
    nlinarith [norm_nonneg c, LX_op_nonneg (Ea D N x)]
  have hn1 : ‖m₁ * m₂‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg m₁, norm_nonneg m₂]
  have hn2 : ‖m₂ * m₂‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg m₂]
  have hn3 : ‖m₁ * m₂ * m₁‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg m₁, norm_nonneg (m₁ * m₂)]
  have hn4 : ‖m₁ * m₂ * m₂‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg m₂, norm_nonneg (m₁ * m₂)]
  -- the matrix approximations
  have mY1 : opNorm (diagonal (diag M₂) * diagonal (diag M₂) - (m₂ * m₂) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 8 * ε :=
    LX_apx_mat ε hε [diagonal (diag M₂), diagonal (diag M₂)] [m₂ • 1, m₂ • 1]
      (List.Forall₂.cons apD₂ (List.Forall₂.cons apD₂ List.Forall₂.nil)) _ _ 8
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one])
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
        smul_smul]) (by norm_num)
  have mY2 : opNorm (M₁ * diagonal (diag M₂) - (m₁ * m₂) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 8 * ε :=
    LX_apx_mat ε hε [M₁, diagonal (diag M₂)] [m₁ • 1, m₂ • 1]
      (List.Forall₂.cons apM₁ (List.Forall₂.cons apD₂ List.Forall₂.nil)) _ _ 8
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one])
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
        smul_smul]) (by norm_num)
  have mY3 : opNorm (M₁ * Ea D N a * M₂ * diagonal (diag M₁) - (m₁ * m₂ * m₁) • Ea D N a) ≤ 64 * ε :=
    LX_apx_mat ε hε [M₁, Ea D N a, M₂, diagonal (diag M₁)] [m₁ • 1, Ea D N a, m₂ • 1, m₁ • 1]
      (List.Forall₂.cons apM₁ (List.Forall₂.cons (apE a) (List.Forall₂.cons apM₂
        (List.Forall₂.cons apD₁ List.Forall₂.nil)))) _ _ 64
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, smul_smul]; try (congr 1; ring)) (by norm_num)
  have mY4 : opNorm (M₁ * Ea D N a * M₂ * diagonal (diag M₂) - (m₁ * m₂ * m₂) • Ea D N a) ≤ 64 * ε :=
    LX_apx_mat ε hε [M₁, Ea D N a, M₂, diagonal (diag M₂)] [m₁ • 1, Ea D N a, m₂ • 1, m₂ • 1]
      (List.Forall₂.cons apM₁ (List.Forall₂.cons (apE a) (List.Forall₂.cons apM₂
        (List.Forall₂.cons apD₂ List.Forall₂.nil)))) _ _ 64
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, smul_smul]; try (congr 1; ring)) (by norm_num)
  have mB1 : ∀ x : Fin D, opNorm (M₂ * diagonal (diag M₂) * Ea D N x - (m₂ * m₂) • Ea D N x) ≤
      24 * ε := fun x =>
    LX_apx_mat ε hε [M₂, diagonal (diag M₂), Ea D N x] [m₂ • 1, m₂ • 1, Ea D N x]
      (List.Forall₂.cons apM₂ (List.Forall₂.cons apD₂ (List.Forall₂.cons (apE x)
        List.Forall₂.nil))) _ _ 24
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
      (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, smul_smul]) (by norm_num)
  have mB2 : opNorm (diagonal (diag (M₁ * Ea D N a * M₂)) - (m₁ * m₂) • Ea D N a) ≤ 24 * ε := by
    have h1 : opNorm (M₁ * Ea D N a * M₂ - (m₁ * m₂) • Ea D N a) ≤ 24 * ε :=
      LX_apx_mat ε hε [M₁, Ea D N a, M₂] [m₁ • 1, Ea D N a, m₂ • 1]
        (List.Forall₂.cons apM₁ (List.Forall₂.cons (apE a) (List.Forall₂.cons apM₂
          List.Forall₂.nil))) _ _ 24
        (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc])
        (by simp only [List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.one_mul, smul_smul]; try (congr 1; ring)) (by norm_num)
    have e : diagonal (diag (M₁ * Ea D N a * M₂)) - (m₁ * m₂) • Ea D N a =
        diagonal (diag (M₁ * Ea D N a * M₂ - (m₁ * m₂) • Ea D N a)) := by
      ext p q
      by_cases hpq : p = q
      · subst hpq; simp [Ea, Matrix.diagonal_apply]
      · simp [hpq, Ea, Matrix.diagonal_apply]
    rw [e]
    exact (LX_dg_le _ 0).2.trans h1
  have hE1 := LX_Dntr_Ea (D := D) (N := N) hN
  have hEE := LX_DntrEE (D := D) (N := N) hN
  have hMn1 : opNorm (M₁ * Ea D N a * M₂) ≤ 2 := by
    have := LX_op3 M₁ (Ea D N a) M₂ (5 / 4) 1 (5 / 4) hM₁ (LX_op_Ea a) hM₂
    linarith
  have hB1 : ∀ x : Fin D, opNorm (M₂ * diagonal (diag M₂) * Ea D N x) ≤ 2 := fun x => by
    have := LX_op3 M₂ (diagonal (diag M₂)) (Ea D N x) (5 / 4) (5 / 4) 1 hM₂ hdM₂ (LX_op_Ea x)
    linarith
  have hB2 : opNorm (diagonal (diag (M₁ * Ea D N a * M₂))) ≤ 2 := (LX_dg_le _ 0).2.trans hMn1
  have hB3 : opNorm (diagonal (diag M₁)) ≤ 2 := hdM₁.trans (by norm_num)
  have hB4 : opNorm (diagonal (diag M₂)) ≤ 2 := hdM₂.trans (by norm_num)
  have hd3 : opNorm (diagonal (diag M₁) - m₁ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 24 * ε := by
    have := apD₁.2.2; linarith
  have hd4 : opNorm (diagonal (diag M₂) - m₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 24 * ε := by
    have := apD₂.2.2; linarith
  set r := opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ with hr
  set Eb : ℝ := 64 * ε * (D * r * (D * ((25 / 16) * 2))) + D * r * (D * ((25 / 16) * (24 * ε)))
    with hEb
  obtain ⟨T1, hT1⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ (M₂ * diagonal (diag M₂) * Ea D N x) b a := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (M₁ * diagonal (diag M₂) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ (diagonal (diag (M₁ * Ea D N a * M₂))) b x := ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (M₁ * Ea D N a * M₂ * diagonal (diag M₁) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ (diagonal (diag M₁)) b x := ⟨_, rfl⟩
  obtain ⟨T4, hT4⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (M₁ * Ea D N a * M₂ * diagonal (diag M₂) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ (diagonal (diag M₂)) b x := ⟨_, rfl⟩
  obtain ⟨F1, hF1⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (((m₂ * m₂) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ ((m₂ * m₂) • Ea D N x) b a := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (((m₁ * m₂) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ ((m₁ * m₂) • Ea D N a) b x := ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (((m₁ * m₂ * m₁) • Ea D N a) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ (m₁ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) b x := ⟨_, rfl⟩
  obtain ⟨F4, hF4⟩ : ∃ T : Fin D → ℂ, T = fun x =>
      ((D : ℂ) * ntr (((m₁ * m₂ * m₂) • Ea D N a) * Ea D N x)) *
        KThetaB Λ θ z₂ z₁ (m₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) b x := ⟨_, rfl⟩
  have t1 : ∀ x, ‖T1 x - F1 x‖ ≤ Eb := fun x => by
    rw [hT1, hF1]
    exact LX_term Λ θ z₁ z₂ hM₁ hM₂ _ _ _ _ x b a (64 * ε) (24 * ε) (mY1.trans (by linarith))
      (hmm _ hn2) (hB1 x) (mB1 x)
  have t2 : ∀ x, ‖T2 x - F2 x‖ ≤ Eb := fun x => by
    rw [hT2, hF2]
    exact LX_term Λ θ z₁ z₂ hM₁ hM₂ _ _ _ _ x b x (64 * ε) (24 * ε) (mY2.trans (by linarith))
      (hmm _ hn1) hB2 mB2
  have t3 : ∀ x, ‖T3 x - F3 x‖ ≤ Eb := fun x => by
    rw [hT3, hF3]
    exact LX_term Λ θ z₁ z₂ hM₁ hM₂ _ _ _ _ x b x (64 * ε) (24 * ε) mY3 (hmE _ hn3 a) hB3 hd3
  have t4 : ∀ x, ‖T4 x - F4 x‖ ≤ Eb := fun x => by
    rw [hT4, hF4]
    exact LX_term Λ θ z₁ z₂ hM₁ hM₂ _ _ _ _ x b x (64 * ε) (24 * ε) mY4 (hmE _ hn4 a) hB4 hd4
  have hdec : (D : ℂ) * lead14 Λ θ z₁ z₂ a b = ∑ x, (T1 x + T2 x + T3 x + T4 x) := by
    unfold lead14
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hT1, hT2, hT3, hT4]
    ring
  have hs1 : ∑ x, F1 x = m₂ ^ 4 * KTheta Λ θ z₁ z₂ a b := by
    have : ∀ x, F1 x = m₂ ^ 4 * (if a = x then KTheta Λ θ z₁ z₂ x b else 0) := by
      intro x
      rw [hF1]
      simp only [Matrix.smul_mul, Matrix.one_mul, LX_ntr_smul, LX_KB_smul, hc3 x b a]
      have := hE1 x
      calc (D : ℂ) * (m₂ * m₂ * ntr (Ea D N x)) * (m₂ * m₂ * (if a = x then KTheta Λ θ z₁ z₂ x b else 0)) =
          (m₂ * m₂) * ((D : ℂ) * ntr (Ea D N x)) * (m₂ * m₂ * (if a = x then KTheta Λ θ z₁ z₂ x b else 0)) := by ring
        _ = _ := by rw [this]; ring
    simp only [this, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hs2 : ∑ x, F2 x = m₁ ^ 2 * m₂ ^ 2 * KTheta Λ θ z₁ z₂ a b := by
    have : ∀ x, F2 x = m₁ ^ 2 * m₂ ^ 2 * (if x = a then KTheta Λ θ z₁ z₂ a b else 0) := by
      intro x
      rw [hF2]
      simp only [Matrix.smul_mul, Matrix.one_mul, LX_ntr_smul, LX_KB_smul, hc3 a b x]
      have := hE1 x
      calc (D : ℂ) * (m₁ * m₂ * ntr (Ea D N x)) *
          (m₁ * m₂ * (if x = a then KTheta Λ θ z₁ z₂ a b else 0)) =
          (m₁ * m₂) * ((D : ℂ) * ntr (Ea D N x)) *
          (m₁ * m₂ * (if x = a then KTheta Λ θ z₁ z₂ a b else 0)) := by ring
        _ = _ := by rw [this]; ring
    simp only [this, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hs3 : ∑ x, F3 x = m₁ ^ 3 * m₂ * KTheta Λ θ z₁ z₂ a b := by
    have : ∀ x, F3 x = m₁ ^ 3 * m₂ * (if a = x then KTheta Λ θ z₁ z₂ x b else 0) := by
      intro x
      rw [hF3]
      simp only [Matrix.smul_mul, LX_ntr_smul, LX_KB_smul, hc4]
      have := hEE a x
      calc (D : ℂ) * (m₁ * m₂ * m₁ * ntr (Ea D N a * Ea D N x)) * (m₁ * KTheta Λ θ z₁ z₂ x b) =
          (m₁ * m₂ * m₁) * ((D : ℂ) * ntr (Ea D N a * Ea D N x)) * (m₁ * KTheta Λ θ z₁ z₂ x b) := by ring
        _ = _ := by rw [this]; split_ifs <;> ring
    simp only [this, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hs4 : ∑ x, F4 x = m₁ * m₂ ^ 3 * KTheta Λ θ z₁ z₂ a b := by
    have : ∀ x, F4 x = m₁ * m₂ ^ 3 * (if a = x then KTheta Λ θ z₁ z₂ x b else 0) := by
      intro x
      rw [hF4]
      simp only [Matrix.smul_mul, LX_ntr_smul, LX_KB_smul, hc4]
      have := hEE a x
      calc (D : ℂ) * (m₁ * m₂ * m₂ * ntr (Ea D N a * Ea D N x)) * (m₂ * KTheta Λ θ z₁ z₂ x b) =
          (m₁ * m₂ * m₂) * ((D : ℂ) * ntr (Ea D N a * Ea D N x)) * (m₂ * KTheta Λ θ z₁ z₂ x b) := by ring
        _ = _ := by rw [this]; split_ifs <;> ring
    simp only [this, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hsum : ∑ x, (F1 x + F2 x + F3 x + F4 x) =
      (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b := by
    simp only [Finset.sum_add_distrib, hs1, hs2, hs3, hs4]
    ring
  rw [hdec, ← hsum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖T1 x + T2 x + T3 x + T4 x - (F1 x + F2 x + F3 x + F4 x)‖ ≤ ∑ _x : Fin D, 4 * Eb := by
        refine Finset.sum_le_sum fun x _ => ?_
        have e : T1 x + T2 x + T3 x + T4 x - (F1 x + F2 x + F3 x + F4 x) =
            (T1 x - F1 x) + (T2 x - F2 x) + (T3 x - F3 x) + (T4 x - F4 x) := by ring
        rw [e]
        have := norm_add_le (T1 x - F1 x + (T2 x - F2 x) + (T3 x - F3 x)) (T4 x - F4 x)
        have h2 := norm_add_le (T1 x - F1 x + (T2 x - F2 x)) (T3 x - F3 x)
        have h3 := norm_add_le (T1 x - F1 x) (T2 x - F2 x)
        linarith [t1 x, t2 x, t3 x, t4 x]
    _ = 4 * D * Eb := by simp; ring

end LX_lead14b

section LX_conj

variable {D N : ℕ}

private theorem LX_KB_sum (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (M : Matrix (Idx D N) (Idx D N) ℂ) (a b : Fin D) :
    ∑ x, KThetaB Λ θ z₁ z₂ (M * Ea D N x) a b = KThetaB Λ θ z₁ z₂ M a b := by
  unfold KThetaB
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  have hin : ∀ W : Matrix (Idx D N) (Idx D N) ℂ,
      ∑ x, ntr (W * (M * Ea D N x)) = ntr (W * M) := fun W => by
    simp only [← Matrix.mul_assoc]
    exact LX_ntr_sum_Ea _
  exact hin _

private theorem LX_DntrB0 [Nonempty (Idx D N)] (hN : 1 ≤ N) (M : Matrix (Idx D N) (Idx D N) ℂ)
    (m : ℂ) (ε : ℝ) (hΔ : opNorm (M - m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ ε) (a c : Fin D) :
    ‖(D : ℂ) * ntr (Ea D N a * M * Ea D N c) - if a = c then m else 0‖ ≤ ε := by
  have e : ntr (Ea D N a * M * Ea D N c) = ntr (M * (Ea D N c * Ea D N a)) := by
    rw [LX_ntr_cyc, ← Matrix.mul_assoc, LX_ntr_cyc]
  rw [e, LX_Ea_mul]
  by_cases h : c = a
  · subst h
    simp only [↓reduceIte]
    have h1 := LX_Dntr_le D N (M - m • 1) c
    have h2 : (D : ℂ) * ntr (M * Ea D N c) - m = (D : ℂ) * ntr ((M - m • 1) * Ea D N c) := by
      rw [Matrix.sub_mul, LX_ntr_sub, Matrix.smul_mul, Matrix.one_mul, LX_ntr_smul, mul_sub]
      have := LX_Dntr_Ea hN c
      rw [mul_left_comm, this]
      ring
    rw [h2]
    exact h1.trans hΔ
  · have h' : ¬ a = c := fun e => h e.symm
    simp [h, h', ntr]
    exact (LX_op_nonneg _).trans hΔ

end LX_conj

section LX_conj2

variable {D N : ℕ}

private theorem LX_lead15_B0 [Nonempty (Idx D N)] (hN : 1 ≤ N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z₁ z₂ m₁ m₂ : ℂ) (ε Cd₁ : ℝ) (hF₁ : LX_Fz (MExt Λ z₁) m₁ ε) (hF₂ : LX_Fz (MExt Λ z₂) m₂ ε)
    (hd₁ : 1 - ntr (MExt Λ z₁ * MExt Λ z₁) ≠ 0)
    (hC₁ : ‖1 - ntr (MExt Λ z₁ * MExt Λ z₁)‖⁻¹ ≤ Cd₁) (a c : Fin D) :
    ‖(D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) -
      (if a = c then m₁ ^ 5 * m₂ / (1 - ntr (MExt Λ z₁ * MExt Λ z₁)) else 0)‖ ≤
      D * (500 * Cd₁ * ε) + Cd₁ * ε := by
  have hε := hF₁.hε
  have hB₀ : opNorm (Ea D N a * MExt Λ z₂ * Ea D N c) ≤ 2 := by
    have := LX_op3 (Ea D N a) (MExt Λ z₂) (Ea D N c) 1 (5 / 4) 1 (LX_op_Ea a) hF₂.hM (LX_op_Ea c)
    linarith
  have h1 := LX_lead15_frozen Λ z₁ m₁ ε Cd₁ hF₁ hd₁ hC₁ _ hB₀
  have h2 := LX_DntrB0 hN (MExt Λ z₂) m₂ ε hF₂.hΔ a c
  have hd0 : 0 < ‖1 - ntr (MExt Λ z₁ * MExt Λ z₁)‖ := norm_pos_iff.mpr hd₁
  have hCd : ‖(1 - ntr (MExt Λ z₁ * MExt Λ z₁))⁻¹‖ ≤ Cd₁ := by rwa [norm_inv]
  set s := 1 - ntr (MExt Λ z₁ * MExt Λ z₁) with hs
  have e : (D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) -
      (if a = c then m₁ ^ 5 * m₂ / s else 0) =
      (D : ℂ) * (lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) -
        m₁ ^ 5 * ntr (Ea D N a * MExt Λ z₂ * Ea D N c) / s) +
      m₁ ^ 5 / s * ((D : ℂ) * ntr (Ea D N a * MExt Λ z₂ * Ea D N c) - if a = c then m₂ else 0) := by
    split_ifs <;> ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg D)
  · rw [norm_mul, div_eq_mul_inv, norm_mul, norm_pow]
    have hm : ‖m₁‖ ^ 5 ≤ 1 := pow_le_one₀ (norm_nonneg _) hF₁.hm
    have : ‖m₁‖ ^ 5 * ‖s⁻¹‖ ≤ Cd₁ := by
      calc ‖m₁‖ ^ 5 * ‖s⁻¹‖ ≤ 1 * Cd₁ := mul_le_mul hm hCd (norm_nonneg _) zero_le_one
        _ = Cd₁ := one_mul _
    calc ‖m₁‖ ^ 5 * ‖s⁻¹‖ * ‖(D : ℂ) * ntr (Ea D N a * MExt Λ z₂ * Ea D N c) -
          if a = c then m₂ else 0‖ ≤ Cd₁ * ε := mul_le_mul this h2 (norm_nonneg _)
            ((norm_nonneg _).trans hCd)
      _ = _ := by ring

private theorem LX_lead15_E [Nonempty (Idx D N)] (hN : 1 ≤ N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z₂ m₂ : ℂ) (ε Cd₂ : ℝ) (hF₂ : LX_Fz (MExt Λ z₂) m₂ ε)
    (hd₂ : 1 - ntr (MExt Λ z₂ * MExt Λ z₂) ≠ 0)
    (hC₂ : ‖1 - ntr (MExt Λ z₂ * MExt Λ z₂)‖⁻¹ ≤ Cd₂) (c : Fin D) :
    ‖(D : ℂ) * lead15 Λ z₂ (Ea D N c) - m₂ ^ 5 / (1 - ntr (MExt Λ z₂ * MExt Λ z₂))‖ ≤
      D * (500 * Cd₂ * ε) := by
  have hB : opNorm (Ea D N c) ≤ 2 := (LX_op_Ea c).trans (by norm_num)
  have h1 := LX_lead15_frozen Λ z₂ m₂ ε Cd₂ hF₂ hd₂ hC₂ _ hB
  have e : (D : ℂ) * lead15 Λ z₂ (Ea D N c) - m₂ ^ 5 / (1 - ntr (MExt Λ z₂ * MExt Λ z₂)) =
      (D : ℂ) * (lead15 Λ z₂ (Ea D N c) - m₂ ^ 5 * ntr (Ea D N c) /
        (1 - ntr (MExt Λ z₂ * MExt Λ z₂))) := by
    have := LX_Dntr_Ea (D := D) (N := N) hN c
    calc _ = (D : ℂ) * lead15 Λ z₂ (Ea D N c) - m₂ ^ 5 * ((D : ℂ) * ntr (Ea D N c)) /
          (1 - ntr (MExt Λ z₂ * MExt Λ z₂)) := by rw [this]; ring
      _ = _ := by ring
  rw [e, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg D)

end LX_conj2

section LX_conj3

variable {D N : ℕ}

/-- The remainder in the evaluation of the main terms of `𝒟` for a pair `(z₁, z₂)`. -/
private def LX_RemB (D : ℕ) (r r₂₁ ε Cd₁ Cd₂ : ℝ) : ℝ :=
  D * (5 + 10 * Cd₁) +
    4 * D * (64 * ε * (D * r₂₁ * (D * ((25 / 16) * 2))) + D * r₂₁ * (D * ((25 / 16) * (24 * ε)))) +
    Cd₁ + (D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) * (D * (500 * Cd₁ * ε) + Cd₁ * ε) +
    Cd₂ * (D * r₂₁ * (D * ((25 / 16) * ε))) +
    (D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * (500 * Cd₂ * ε))

set_option maxHeartbeats 800000 in
private theorem LX_conj_Main [Nonempty (Idx D N)] (hD : 1 ≤ D) (hN : 1 ≤ N)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (z₁ z₂ m₁ m₂ : ℂ) (ε Cd₁ Cd₂ : ℝ) (hF₁ : LX_Fz (MExt Λ z₁) m₁ ε)
    (hF₂ : LX_Fz (MExt Λ z₂) m₂ ε) (hd₁ : 1 - ntr (MExt Λ z₁ * MExt Λ z₁) ≠ 0)
    (hC₁ : ‖1 - ntr (MExt Λ z₁ * MExt Λ z₁)‖⁻¹ ≤ Cd₁) (hd₂ : 1 - ntr (MExt Λ z₂ * MExt Λ z₂) ≠ 0)
    (hC₂ : ‖1 - ntr (MExt Λ z₂ * MExt Λ z₂)‖⁻¹ ≤ Cd₂)
    (hc3 : ∀ a b x : Fin D, KThetaB Λ θ z₂ z₁ (Ea D N a) b x =
      if x = a then KTheta Λ θ z₁ z₂ a b else 0)
    (hc4 : ∀ b x : Fin D, KThetaB Λ θ z₂ z₁ 1 b x = KTheta Λ θ z₁ z₂ x b)
    (hc6 : opNorm (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) ≤ 1) (a b : Fin D) :
    ‖LX_Main Λ θ z₁ z₂ a b - ((m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) +
      m₁ ^ 5 * m₂ / (1 - ntr (MExt Λ z₁ * MExt Λ z₁)) +
      m₂ ^ 6 / (1 - ntr (MExt Λ z₂ * MExt Λ z₂))) * KTheta Λ θ z₁ z₂ a b‖ ≤
      LX_RemB D (opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹)
        (opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹) ε Cd₁ Cd₂ := by
  have hε := hF₁.hε
  have hM₁ := hF₁.hM
  have hM₂ := hF₂.hM
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hP : ∀ x c, PTheta D θ x c = PTheta D θ c x := LX_P_symm D θ
  have hPn : ∀ x c, ‖PTheta D θ x c‖ ≤ 1 := LX_P_norm_le D hD θ hθ0 hθ1
  have hd₁0 : 0 < ‖1 - ntr (MExt Λ z₁ * MExt Λ z₁)‖ := norm_pos_iff.mpr hd₁
  have hd₂0 : 0 < ‖1 - ntr (MExt Λ z₂ * MExt Λ z₂)‖ := norm_pos_iff.mpr hd₂
  have hC₁0 : 0 ≤ Cd₁ := (inv_nonneg.mpr hd₁0.le).trans hC₁
  have hC₂0 : 0 ≤ Cd₂ := (inv_nonneg.mpr hd₂0.le).trans hC₂
  set r := opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ with hr
  set r₂₁ := opNorm (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ with hr₂₁
  have hr0 : 0 ≤ r := LX_op_nonneg _
  have hr₂₁0 : 0 ≤ r₂₁ := LX_op_nonneg _
  set σ₁ : ℂ := m₁ ^ 5 * m₂ / (1 - ntr (MExt Λ z₁ * MExt Λ z₁)) with hσ₁
  set σ₂ : ℂ := m₂ ^ 5 / (1 - ntr (MExt Λ z₂ * MExt Λ z₂)) with hσ₂
  have hσ₁n : ‖σ₁‖ ≤ Cd₁ := by
    rw [hσ₁, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_inv]
    have h1 : ‖m₁‖ ^ 5 ≤ 1 := pow_le_one₀ (norm_nonneg _) hF₁.hm
    have : ‖m₁‖ ^ 5 * ‖m₂‖ ≤ 1 := by nlinarith [norm_nonneg m₂, pow_nonneg (norm_nonneg m₁) 5, hF₂.hm]
    calc ‖m₁‖ ^ 5 * ‖m₂‖ * ‖1 - ntr (MExt Λ z₁ * MExt Λ z₁)‖⁻¹ ≤ 1 * Cd₁ :=
          mul_le_mul this hC₁ (inv_nonneg.mpr hd₁0.le) zero_le_one
      _ = Cd₁ := one_mul _
  have hσ₂n : ‖σ₂‖ ≤ Cd₂ := by
    rw [hσ₂, div_eq_mul_inv, norm_mul, norm_pow, norm_inv]
    have h1 : ‖m₂‖ ^ 5 ≤ 1 := pow_le_one₀ (norm_nonneg _) hF₂.hm
    calc ‖m₂‖ ^ 5 * ‖1 - ntr (MExt Λ z₂ * MExt Λ z₂)‖⁻¹ ≤ 1 * Cd₂ :=
          mul_le_mul h1 hC₂ (inv_nonneg.mpr hd₂0.le) zero_le_one
      _ = Cd₂ := one_mul _
  -- the four pieces
  have p1 : ‖(D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b)‖ ≤ D * (5 + 10 * Cd₁) := by
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg D)
    have hB : opNorm (Ea D N a * MExt Λ z₂ * Ea D N b) ≤ 5 / 4 := by
      have := LX_op3 (Ea D N a) (MExt Λ z₂) (Ea D N b) 1 (5 / 4) 1 (LX_op_Ea a) hM₂ (LX_op_Ea b)
      linarith
    have := LX_lead15_crude Λ z₁ _ (5 / 4) Cd₁ hM₁ hB hd₁ hC₁
    linarith
  have p2 := LX_lead14_frozen hN Λ θ z₁ z₂ m₁ m₂ ε hF₁ hF₂ hc3 hc4 a b
  have eB : ∀ a c : Fin D, ‖(D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) -
      (if a = c then σ₁ else 0)‖ ≤ D * (500 * Cd₁ * ε) + Cd₁ * ε := fun a c =>
    LX_lead15_B0 hN Λ z₁ z₂ m₁ m₂ ε Cd₁ hF₁ hF₂ hd₁ hC₁ a c
  have eE : ∀ c : Fin D, ‖(D : ℂ) * lead15 Λ z₂ (Ea D N c) - σ₂‖ ≤ D * (500 * Cd₂ * ε) := fun c =>
    LX_lead15_E hN Λ z₂ m₂ ε Cd₂ hF₂ hd₂ hC₂ c
  -- sum (3)
  have s3 : ∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
      ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c)) =
      σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂) a b + ∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
        ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) - (if a = c then σ₁ else 0)) := by
    have h1 : ∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b * (if a = c then σ₁ else 0) =
        σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂) a b := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [hP x a]; ring
    rw [← h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  -- sum (4)
  have s4 : ∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
      ((D : ℂ) * lead15 Λ z₂ (Ea D N c)) =
      σ₂ * (m₂ * KTheta Λ θ z₁ z₂ a b + KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a) +
      ∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
        ((D : ℂ) * lead15 Λ z₂ (Ea D N c) - σ₂) := by
    have h1 : ∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a * σ₂ =
        σ₂ * (m₂ * KTheta Λ θ z₁ z₂ a b + KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a) := by
      have e1 : KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a =
          KThetaB Λ θ z₂ z₁ (MExt Λ z₂) b a - m₂ * KTheta Λ θ z₁ z₂ a b := by
        rw [LX_KB_sub, LX_KB_smul, hc4]
      have e2 : ∀ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a * σ₂ =
          σ₂ * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a := by
        intro x
        rw [← Finset.sum_mul, ← Finset.sum_mul, LX_P_row D hD θ x]
        ring
      simp only [e2]
      rw [← Finset.mul_sum, LX_KB_sum, e1]
      ring
    rw [← h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  -- the bounds
  have n3 : ‖∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
        ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) - (if a = c then σ₁ else 0))‖ ≤
      (D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) * (D * (500 * Cd₁ * ε) + Cd₁ * ε) := by
    rw [mul_assoc]
    refine LX_dsum _ _ fun x c => ?_
    rw [norm_mul, norm_mul]
    have hk := LX_K_bound Λ θ z₁ z₂ x b hM₁ hM₂
    rw [← hr] at hk
    have hPK : ‖PTheta D θ x c‖ * ‖KTheta Λ θ z₁ z₂ x b‖ ≤ D * r * (D * (25 / 16)) := by
      calc ‖PTheta D θ x c‖ * ‖KTheta Λ θ z₁ z₂ x b‖ ≤ 1 * (D * r * (D * (25 / 16))) :=
            mul_le_mul (hPn x c) hk (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    exact mul_le_mul hPK (eB a c) (norm_nonneg _) (by positivity)
  have n4 : ‖∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
        ((D : ℂ) * lead15 Λ z₂ (Ea D N c) - σ₂)‖ ≤
      (D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * (500 * Cd₂ * ε)) := by
    rw [mul_assoc]
    refine LX_dsum _ _ fun x c => ?_
    rw [norm_mul, norm_mul]
    have hk := LX_Kt_bound Λ θ z₁ z₂ a b x hM₁ hM₂
    rw [← hr₂₁] at hk
    have hPK : ‖PTheta D θ x c‖ * ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
        D * r₂₁ * (D * ((25 / 16) * (5 / 4))) := by
      calc ‖PTheta D θ x c‖ * ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a‖ ≤
            1 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) :=
            mul_le_mul (hPn x c) hk (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    exact mul_le_mul hPK (eE c) (norm_nonneg _) (by positivity)
  have n5 : ‖KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a‖ ≤
      D * r₂₁ * (D * ((25 / 16) * ε)) := by
    have := LX_KB_bound Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a hM₂ hM₁
    rw [← hr₂₁] at this
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hF₂.hΔ (by norm_num)
  have n6 : ‖(PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b‖ ≤ 1 :=
    (norm_apply_le_opNorm _ a b).trans hc6
  -- assemble
  have hS : (m₂ ^ 6 / (1 - ntr (MExt Λ z₂ * MExt Λ z₂))) = σ₂ * m₂ := by rw [hσ₂]; ring
  have hsplit : LX_Main Λ θ z₁ z₂ a b - ((m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) +
      m₁ ^ 5 * m₂ / (1 - ntr (MExt Λ z₁ * MExt Λ z₁)) +
      m₂ ^ 6 / (1 - ntr (MExt Λ z₂ * MExt Λ z₂))) * KTheta Λ θ z₁ z₂ a b =
      (D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b) +
      ((D : ℂ) * lead14 Λ θ z₁ z₂ a b -
        (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b) +
      σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b +
      (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
        ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) - (if a = c then σ₁ else 0))) +
      σ₂ * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a +
      (∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
        ((D : ℂ) * lead15 Λ z₂ (Ea D N c) - σ₂)) := by
    unfold LX_Main
    rw [s3, s4, hS, Matrix.sub_apply]
    simp only [hσ₁]
    ring
  rw [hsplit]
  have q1 : ‖σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b‖ ≤ Cd₁ := by
    rw [norm_mul]
    calc ‖σ₁‖ * ‖(PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b‖ ≤ Cd₁ * 1 :=
          mul_le_mul hσ₁n n6 (norm_nonneg _) hC₁0
      _ = Cd₁ := mul_one _
  have q2 : ‖σ₂ * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a‖ ≤
      Cd₂ * (D * r₂₁ * (D * ((25 / 16) * ε))) := by
    rw [norm_mul]
    exact mul_le_mul hσ₂n n5 (norm_nonneg _) hC₂0
  unfold LX_RemB
  have h1 := norm_add_le ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b) +
    ((D : ℂ) * lead14 Λ θ z₁ z₂ a b -
        (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b) +
      σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b +
      (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
        ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) - (if a = c then σ₁ else 0))) +
      σ₂ * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a)
    (∑ x, ∑ c, PTheta D θ x c * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * Ea D N x) b a *
        ((D : ℂ) * lead15 Λ z₂ (Ea D N c) - σ₂))
  have h2 := norm_add_le ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b) +
    ((D : ℂ) * lead14 Λ θ z₁ z₂ a b -
        (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b) +
      σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b +
      (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
        ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) - (if a = c then σ₁ else 0))))
    (σ₂ * KThetaB Λ θ z₂ z₁ (MExt Λ z₂ - m₂ • 1) b a)
  have h3 := norm_add_le ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b) +
    ((D : ℂ) * lead14 Λ θ z₁ z₂ a b -
        (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b) +
      σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b)
    (∑ x, ∑ c, PTheta D θ x c * KTheta Λ θ z₁ z₂ x b *
        ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N c) - (if a = c then σ₁ else 0)))
  have h4 := norm_add_le ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b) +
    ((D : ℂ) * lead14 Λ θ z₁ z₂ a b -
        (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b))
    (σ₁ * (PTheta D θ * KTheta Λ θ z₁ z₂ - KTheta Λ θ z₁ z₂) a b)
  have h5 := norm_add_le ((D : ℂ) * lead15 Λ z₁ (Ea D N a * MExt Λ z₂ * Ea D N b))
    ((D : ℂ) * lead14 Λ θ z₁ z₂ a b -
        (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) * KTheta Λ θ z₁ z₂ a b)
  rw [← hr₂₁] at p2
  linarith

end LX_conj3

section LX_comb

private theorem LX_combine {D : ℕ} (X R Main K : Fin D → Fin D → ℂ) (κ S : ℂ)
    (r E RemB Sb Kb kap : ℝ) (hr : 0 ≤ r) (hSb : 0 ≤ Sb) (hKb : 0 ≤ Kb) (hkap : 0 ≤ kap)
    (hdec : ∀ a b, ‖X a b - ∑ x, R a x * (κ * Main x b)‖ ≤ D * r * E)
    (hR : ∀ a x, ‖R a x‖ ≤ r) (hmain : ∀ x b, ‖Main x b - S * K x b‖ ≤ RemB)
    (hS : ‖S‖ ≤ Sb) (hK : ∀ x b, ‖K x b‖ ≤ Kb) (hκ : ‖κ‖ ≤ kap) (a b : Fin D) :
    ‖X a b‖ ≤ D * r * E + kap * (D * r * (Sb * Kb + RemB)) := by
  have hM : ∀ x, ‖Main x b‖ ≤ Sb * Kb + RemB := fun x => by
    have h1 := norm_add_le (Main x b - S * K x b) (S * K x b)
    rw [sub_add_cancel] at h1
    have h2 : ‖S * K x b‖ ≤ Sb * Kb := by
      rw [norm_mul]; exact mul_le_mul hS (hK x b) (norm_nonneg _) hSb
    linarith [hmain x b]
  have h3 : ‖∑ x, R a x * (κ * Main x b)‖ ≤ kap * (D * r * (Sb * Kb + RemB)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ x : Fin D, ‖R a x * (κ * Main x b)‖ ≤ kap * (r * (Sb * Kb + RemB)) := fun x => by
      rw [norm_mul, norm_mul]
      have hn : 0 ≤ Sb * Kb + RemB := (norm_nonneg _).trans (hM x)
      calc ‖R a x‖ * (‖κ‖ * ‖Main x b‖) ≤ r * (kap * (Sb * Kb + RemB)) :=
            mul_le_mul (hR a x) (mul_le_mul hκ (hM x) (norm_nonneg _) hkap) (by positivity) hr
        _ = _ := by ring
    calc ∑ x, ‖R a x * (κ * Main x b)‖ ≤ ∑ _x : Fin D, kap * (r * (Sb * Kb + RemB)) :=
          Finset.sum_le_sum fun x _ => this x
      _ = _ := by simp; ring
  have h4 := norm_add_le (X a b - ∑ x, R a x * (κ * Main x b)) (∑ x, R a x * (κ * Main x b))
  rw [sub_add_cancel] at h4
  linarith [hdec a b]

end LX_comb

section LX_num

private theorem LX_num_err (D : ℕ) (c₁ c₂ Cr P u σ m x r r₂₁ ε₁₅ ε₁₄ BE1 BE2 tl Y : ℝ) (hD : 1 ≤ D)
    (hP : 1 ≤ P) (hu : 1 ≤ u) (hσ : 0 ≤ σ) (hY : 0 ≤ Y) (hr : 0 ≤ r) (hr₂ : 0 ≤ r₂₁)
    (h15 : 0 ≤ ε₁₅) (h14 : 0 ≤ ε₁₄) (hB1 : 0 ≤ BE1) (hB2 : 0 ≤ BE2) (htl0 : 0 ≤ tl)
    (hCr : 0 ≤ Cr) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hmx : 0 ≤ m * x)
    (Q1 : u ^ 4 * σ ≤ c₁) (Q2 : u ^ 3 * (m * x) ≤ c₂) (hrr : r ≤ Cr * u) (hrr₂ : r₂₁ ≤ Cr * u)
    (e15 : ε₁₅ ≤ u * σ * Y) (e14 : ε₁₄ ≤ σ * (1 + Cr * u) * Y)
    (eB1 : BE1 ≤ D * (5 / 4) * P * Cr * u * (m * x) * Y + tl)
    (eB2 : BE2 ≤ D ^ 2 * (5 / 4) * P * Cr * u * (m * x) * Y + tl)
    (htl : tl * u ^ 2 ≤ Y) (hPY : Y ≤ P * Y) :
    D * r * LX_ErrBd D r r₂₁ ε₁₅ ε₁₄ BE1 BE2 * u ≤
      (D * Cr * (D * (5 / 4) * c₁ + (1 + Cr) * c₁ + 2 * D ^ 5 * (125 / 64) * Cr * c₁ +
        (D ^ 3 + D ^ 4) * (5 / 4) * Cr * c₂ + 2 * D ^ 2)) * (P * Y) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hu2 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have hu3 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have hu0 : 0 ≤ u := by linarith
  have hσ4 : u ^ 3 * σ ≤ c₁ := (mul_le_mul_of_nonneg_right hu3 hσ).trans Q1
  have hσ2 : u ^ 2 * σ ≤ c₁ := (mul_le_mul_of_nonneg_right hu2 hσ).trans Q1
  unfold LX_ErrBd
  -- the six terms, multiplied by u²
  have t1 : u ^ 2 * (D * (5 / 4) * ε₁₅) ≤ D * (5 / 4) * c₁ * Y := by
    calc u ^ 2 * (D * (5 / 4) * ε₁₅) ≤ u ^ 2 * (D * (5 / 4) * (u * σ * Y)) := by gcongr
      _ = D * (5 / 4) * (u ^ 3 * σ) * Y := by ring
      _ ≤ D * (5 / 4) * c₁ * Y := by gcongr
  have t2 : u ^ 2 * ε₁₄ ≤ (1 + Cr) * c₁ * Y := by
    calc u ^ 2 * ε₁₄ ≤ u ^ 2 * (σ * (1 + Cr * u) * Y) := by gcongr
      _ = ((u ^ 2 * σ) + Cr * (u ^ 3 * σ)) * Y := by ring
      _ ≤ (c₁ + Cr * c₁) * Y := by gcongr
      _ = (1 + Cr) * c₁ * Y := by ring
  have t3 : u ^ 2 * ((D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) * (D * (5 / 4) * ε₁₅)) ≤
      D ^ 5 * (125 / 64) * Cr * c₁ * Y := by
    calc u ^ 2 * ((D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) * (D * (5 / 4) * ε₁₅)) ≤
          u ^ 2 * ((D : ℝ) ^ 2 * (D * (Cr * u) * (D * (25 / 16))) * (D * (5 / 4) * (u * σ * Y))) := by
            gcongr
      _ = D ^ 5 * (125 / 64) * Cr * (u ^ 4 * σ) * Y := by ring
      _ ≤ D ^ 5 * (125 / 64) * Cr * c₁ * Y := by gcongr
  have t4 : u ^ 2 * ((D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * ε₁₅)) ≤
      D ^ 5 * (125 / 64) * Cr * c₁ * Y := by
    calc u ^ 2 * ((D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * ε₁₅)) ≤
          u ^ 2 * ((D : ℝ) ^ 2 * (D * (Cr * u) * (D * ((25 / 16) * (5 / 4)))) *
            (D * (u * σ * Y))) := by gcongr
      _ = D ^ 5 * (125 / 64) * Cr * (u ^ 4 * σ) * Y := by ring
      _ ≤ D ^ 5 * (125 / 64) * Cr * c₁ * Y := by gcongr
  have t5 : u ^ 2 * ((D : ℝ) ^ 2 * BE1) ≤ D ^ 3 * (5 / 4) * Cr * c₂ * (P * Y) + D ^ 2 * Y := by
    calc u ^ 2 * ((D : ℝ) ^ 2 * BE1) ≤
          u ^ 2 * ((D : ℝ) ^ 2 * (D * (5 / 4) * P * Cr * u * (m * x) * Y + tl)) := by gcongr
      _ = D ^ 3 * (5 / 4) * Cr * (u ^ 3 * (m * x)) * (P * Y) + D ^ 2 * (tl * u ^ 2) := by ring
      _ ≤ D ^ 3 * (5 / 4) * Cr * c₂ * (P * Y) + D ^ 2 * Y := by gcongr
  have t6 : u ^ 2 * ((D : ℝ) ^ 2 * BE2) ≤ D ^ 4 * (5 / 4) * Cr * c₂ * (P * Y) + D ^ 2 * Y := by
    calc u ^ 2 * ((D : ℝ) ^ 2 * BE2) ≤
          u ^ 2 * ((D : ℝ) ^ 2 * (D ^ 2 * (5 / 4) * P * Cr * u * (m * x) * Y + tl)) := by gcongr
      _ = D ^ 4 * (5 / 4) * Cr * (u ^ 3 * (m * x)) * (P * Y) + D ^ 2 * (tl * u ^ 2) := by ring
      _ ≤ D ^ 4 * (5 / 4) * Cr * c₂ * (P * Y) + D ^ 2 * Y := by gcongr
  set Eb := D * (5 / 4) * ε₁₅ + ε₁₄ + (D : ℝ) ^ 2 * (D * r * (D * (25 / 16))) *
      (D * (5 / 4) * ε₁₅) + (D : ℝ) ^ 2 * (D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (D * ε₁₅) +
      (D : ℝ) ^ 2 * BE1 + (D : ℝ) ^ 2 * BE2 with hEb
  have hEb0 : 0 ≤ Eb := by rw [hEb]; positivity
  have c1 : (D * (5 / 4) * c₁ + (1 + Cr) * c₁ + 2 * D ^ 5 * (125 / 64) * Cr * c₁ + 2 * D ^ 2) * Y ≤
      (D * (5 / 4) * c₁ + (1 + Cr) * c₁ + 2 * D ^ 5 * (125 / 64) * Cr * c₁ + 2 * D ^ 2) * (P * Y) :=
    mul_le_mul_of_nonneg_left hPY (by positivity)
  have hsum : u ^ 2 * Eb ≤
      (D * (5 / 4) * c₁ + (1 + Cr) * c₁ + 2 * D ^ 5 * (125 / 64) * Cr * c₁ +
        (D ^ 3 + D ^ 4) * (5 / 4) * Cr * c₂ + 2 * D ^ 2) * (P * Y) := by
    rw [hEb]
    nlinarith [t1, t2, t3, t4, t5, t6, c1]
  calc D * r * Eb * u ≤ D * (Cr * u) * Eb * u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrr hD0) hEb0) hu0
    _ = D * Cr * (u ^ 2 * Eb) := by ring
    _ ≤ D * Cr * ((D * (5 / 4) * c₁ + (1 + Cr) * c₁ + 2 * D ^ 5 * (125 / 64) * Cr * c₁ +
        (D ^ 3 + D ^ 4) * (5 / 4) * Cr * c₂ + 2 * D ^ 2) * (P * Y)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end LX_num

section LX_num2

private theorem LX_RemB_mono (D : ℕ) {r r' r₂ r₂' e e' a a' b b' : ℝ} (hr : 0 ≤ r) (hr₂ : 0 ≤ r₂)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : r ≤ r') (h2 : r₂ ≤ r₂') (h3 : e ≤ e') (h4 : a ≤ a')
    (h5 : b ≤ b') : LX_RemB D r r₂ e a b ≤ LX_RemB D r' r₂' e' a' b' := by
  unfold LX_RemB
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hr' : 0 ≤ r' := hr.trans h1
  have hr₂' : 0 ≤ r₂' := hr₂.trans h2
  have he' : 0 ≤ e' := he.trans h3
  have ha' : 0 ≤ a' := ha.trans h4
  have hb' : 0 ≤ b' := hb.trans h5
  gcongr

private theorem LX_RemB_eq (D : ℕ) (R ε ρ C : ℝ) :
    LX_RemB D R R ε (C * ρ) (C * ρ) = 5 * D + (10 * D * C + C) * ρ + 950 * (D : ℝ) ^ 3 * R * ε +
      (C * ((D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
        (D : ℝ) ^ 5 * (62500 / 64))) * (R * ρ * ε) := by
  unfold LX_RemB
  ring

/-- Conjugate pair: the bracket and the leftover of the main terms. -/
private theorem LX_num_conj (D : ℕ) (c Kc Kb C₁ Cr CΔ u z x m w w₂ ρ ε r r₂₁ Cd₁ Cd₂ η : ℝ)
    (hD : 1 ≤ D) (hc : 1 ≤ c) (hKc : 0 ≤ Kc) (hKb : 0 ≤ Kb) (hC₁ : 0 ≤ C₁) (hCr : 0 ≤ Cr)
    (hCΔ : 0 ≤ CΔ) (hu : 1 ≤ u) (hz : 1 ≤ z) (hx : 0 < x) (hm : 0 ≤ m) (hw : 0 ≤ w)
    (hw₂ : 0 ≤ w₂) (hρ : 1 ≤ ρ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr₂ : 0 ≤ r₂₁) (hCd₁ : 0 ≤ Cd₁)
    (hCd₂ : 0 ≤ Cd₂) (hη : 0 < η) (hηx : η * x = 1)
    (R6 : u * z ≤ c * x) (R3 : u ^ 4 * w ≤ 1) (R7 : u ^ 2 * w₂ ≤ 1) (R5 : 1 ≤ c * x)
    (hρu : ρ ≤ u) (hρz : ρ ≤ z) (hrr : r ≤ Cr * u) (hrr₂ : r₂₁ ≤ Cr * u)
    (hCd₁' : Cd₁ ≤ C₁ * ρ) (hCd₂' : Cd₂ ≤ C₁ * ρ) (hεw : ε ≤ CΔ * w) :
    (Kc * m * (D * r * (Kb * (η * z ^ 3 + w₂ * z ^ 2) * (D * r * (D * (25 / 16)))) +
      D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂)) * u ≤
      (Kc * (D * Cr * (Kb * (c ^ 3 + c ^ 2) * (D * Cr * (D * (25 / 16))) +
        (5 * D + 10 * D * C₁ + C₁) * c ^ 2 + 950 * (D : ℝ) ^ 3 * Cr * CΔ * c ^ 2 +
        C₁ * ((D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
          (D : ℝ) ^ 5 * (62500 / 64)) * Cr * CΔ * c ^ 2))) * (m * x ^ 2) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hx0 : 0 ≤ x := hx.le
  have hcx : 1 ≤ (c * x) ^ 2 := one_le_pow₀ R5
  have hCru : 0 ≤ Cr * u := by positivity
  -- the bracket part
  have e1 : u ^ 3 * η * z ^ 3 ≤ c ^ 3 * x ^ 2 := by
    calc u ^ 3 * η * z ^ 3 = η * (u * z) ^ 3 := by ring
      _ ≤ η * (c * x) ^ 3 := by gcongr
      _ = c ^ 3 * x ^ 2 * (η * x) := by ring
      _ = c ^ 3 * x ^ 2 := by rw [hηx]; ring
  have huw : u * w₂ ≤ 1 := by
    have : u ≤ u ^ 2 := le_self_pow₀ hu (by norm_num)
    exact (mul_le_mul_of_nonneg_right this hw₂).trans R7
  have e2 : u ^ 3 * w₂ * z ^ 2 ≤ c ^ 2 * x ^ 2 := by
    calc u ^ 3 * w₂ * z ^ 2 = (u * w₂) * (u * z) ^ 2 := by ring
      _ ≤ 1 * (c * x) ^ 2 := by gcongr
      _ = c ^ 2 * x ^ 2 := by ring
  have hS1 : (Kc * m * (D * r * (Kb * (η * z ^ 3 + w₂ * z ^ 2) * (D * r * (D * (25 / 16)))))) * u ≤
      (Kc * (D * Cr * (Kb * (c ^ 3 + c ^ 2) * (D * Cr * (D * (25 / 16)))))) * (m * x ^ 2) := by
    have hr2 : r ^ 2 ≤ (Cr * u) ^ 2 := by gcongr
    calc (Kc * m * (D * r * (Kb * (η * z ^ 3 + w₂ * z ^ 2) * (D * r * (D * (25 / 16)))))) * u
        = (Kc * Kb * D ^ 3 * (25 / 16) * m) * (r ^ 2 * u * (η * z ^ 3 + w₂ * z ^ 2)) := by ring
      _ ≤ (Kc * Kb * D ^ 3 * (25 / 16) * m) * ((Cr * u) ^ 2 * u * (η * z ^ 3 + w₂ * z ^ 2)) := by
          gcongr
      _ = (Kc * Kb * D ^ 3 * (25 / 16) * Cr ^ 2 * m) * (u ^ 3 * η * z ^ 3 + u ^ 3 * w₂ * z ^ 2) := by
          ring
      _ ≤ (Kc * Kb * D ^ 3 * (25 / 16) * Cr ^ 2 * m) * (c ^ 3 * x ^ 2 + c ^ 2 * x ^ 2) := by gcongr
      _ = _ := by ring
  -- the remainder
  have hRem : LX_RemB D r r₂₁ ε Cd₁ Cd₂ ≤ LX_RemB D (Cr * u) (Cr * u) (CΔ * w) (C₁ * ρ) (C₁ * ρ) :=
    LX_RemB_mono D hr hr₂ hε hCd₁ hCd₂ hrr hrr₂ hεw hCd₁' hCd₂'
  rw [LX_RemB_eq] at hRem
  have hA : 5 * (D : ℝ) + (10 * D * C₁ + C₁) * ρ ≤ (5 * D + 10 * D * C₁ + C₁) * z := by
    have h1 : (10 * D * C₁ + C₁) * ρ ≤ (10 * D * C₁ + C₁) * z :=
      mul_le_mul_of_nonneg_left hρz (by positivity)
    have h2 : 5 * (D : ℝ) ≤ 5 * D * z := by nlinarith [mul_le_mul_of_nonneg_left hz hD0]
    linarith
  set A₃ : ℝ := (D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
    (D : ℝ) ^ 5 * (62500 / 64) with hA₃
  have hA₃0 : 0 ≤ A₃ := by rw [hA₃]; positivity
  set Bd : ℝ := 5 * D + (10 * D * C₁ + C₁) * ρ + 950 * (D : ℝ) ^ 3 * (Cr * u) * (CΔ * w) +
    (C₁ * A₃) * ((Cr * u) * ρ * (CΔ * w)) with hBd
  have hBd0 : 0 ≤ Bd := by rw [hBd]; positivity
  have hu_cx : u ≤ c * x := by
    calc u = u * 1 := (mul_one u).symm
      _ ≤ u * z := mul_le_mul_of_nonneg_left hz hu0
      _ ≤ c * x := R6
  have hw1 : u ^ 3 * w ≤ 1 := by
    have : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
    exact (mul_le_mul_of_nonneg_right this hw).trans R3
  have hw2 : u ^ 3 * ρ * w ≤ 1 := by
    have : u ^ 3 * ρ ≤ u ^ 3 * u := mul_le_mul_of_nonneg_left hρu (by positivity)
    calc u ^ 3 * ρ * w ≤ u ^ 3 * u * w := mul_le_mul_of_nonneg_right this hw
      _ = u ^ 4 * w := by ring
      _ ≤ 1 := R3
  have q0 : u ^ 2 * (5 * (D : ℝ) + (10 * D * C₁ + C₁) * ρ) ≤ (5 * D + 10 * D * C₁ + C₁) * c ^ 2 * x ^ 2 := by
    calc u ^ 2 * (5 * (D : ℝ) + (10 * D * C₁ + C₁) * ρ) ≤ u ^ 2 * ((5 * D + 10 * D * C₁ + C₁) * z) := by
          gcongr
      _ = (5 * D + 10 * D * C₁ + C₁) * (u * (u * z)) := by ring
      _ ≤ (5 * D + 10 * D * C₁ + C₁) * ((c * x) * (c * x)) := by gcongr
      _ = _ := by ring
  have q1 : u ^ 2 * (950 * (D : ℝ) ^ 3 * (Cr * u) * (CΔ * w)) ≤
      950 * (D : ℝ) ^ 3 * Cr * CΔ * c ^ 2 * x ^ 2 := by
    calc u ^ 2 * (950 * (D : ℝ) ^ 3 * (Cr * u) * (CΔ * w)) =
        (950 * (D : ℝ) ^ 3 * Cr * CΔ) * (u ^ 3 * w) := by ring
      _ ≤ (950 * (D : ℝ) ^ 3 * Cr * CΔ) * 1 := by gcongr
      _ ≤ (950 * (D : ℝ) ^ 3 * Cr * CΔ) * (c * x) ^ 2 := by gcongr
      _ = _ := by ring
  have q2 : u ^ 2 * ((C₁ * A₃) * ((Cr * u) * ρ * (CΔ * w))) ≤
      C₁ * A₃ * Cr * CΔ * c ^ 2 * x ^ 2 := by
    calc u ^ 2 * ((C₁ * A₃) * ((Cr * u) * ρ * (CΔ * w))) =
        (C₁ * A₃ * Cr * CΔ) * (u ^ 3 * ρ * w) := by ring
      _ ≤ (C₁ * A₃ * Cr * CΔ) * 1 := by gcongr
      _ ≤ (C₁ * A₃ * Cr * CΔ) * (c * x) ^ 2 := by gcongr
      _ = _ := by ring
  have hS2 : (Kc * m * (D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂)) * u ≤
      (Kc * (D * Cr * ((5 * D + 10 * D * C₁ + C₁) * c ^ 2 + 950 * (D : ℝ) ^ 3 * Cr * CΔ * c ^ 2 +
        C₁ * A₃ * Cr * CΔ * c ^ 2))) * (m * x ^ 2) := by
    have h1 : D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂ ≤ D * (Cr * u) * Bd := by
      calc D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂ ≤ D * r * Bd :=
            mul_le_mul_of_nonneg_left hRem (by positivity)
        _ ≤ D * (Cr * u) * Bd :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrr hD0) hBd0
    calc (Kc * m * (D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂)) * u ≤ (Kc * m * (D * (Cr * u) * Bd)) * u := by
          gcongr
      _ = (Kc * D * Cr * m) * (u ^ 2 * Bd) := by ring
      _ ≤ (Kc * D * Cr * m) * ((5 * D + 10 * D * C₁ + C₁) * c ^ 2 * x ^ 2 +
            950 * (D : ℝ) ^ 3 * Cr * CΔ * c ^ 2 * x ^ 2 + C₁ * A₃ * Cr * CΔ * c ^ 2 * x ^ 2) := by
          have : u ^ 2 * Bd = u ^ 2 * (5 * (D : ℝ) + (10 * D * C₁ + C₁) * ρ) +
              u ^ 2 * (950 * (D : ℝ) ^ 3 * (Cr * u) * (CΔ * w)) +
              u ^ 2 * ((C₁ * A₃) * ((Cr * u) * ρ * (CΔ * w))) := by rw [hBd]; ring
          rw [this]
          gcongr
      _ = _ := by ring
  have hsplit : (Kc * m * (D * r * (Kb * (η * z ^ 3 + w₂ * z ^ 2) * (D * r * (D * (25 / 16)))) +
      D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂)) * u =
      (Kc * m * (D * r * (Kb * (η * z ^ 3 + w₂ * z ^ 2) * (D * r * (D * (25 / 16)))))) * u +
      (Kc * m * (D * r * LX_RemB D r r₂₁ ε Cd₁ Cd₂)) * u := by ring
  rw [hsplit]
  calc _ ≤ (Kc * (D * Cr * (Kb * (c ^ 3 + c ^ 2) * (D * Cr * (D * (25 / 16)))))) * (m * x ^ 2) +
      (Kc * (D * Cr * ((5 * D + 10 * D * C₁ + C₁) * c ^ 2 + 950 * (D : ℝ) ^ 3 * Cr * CΔ * c ^ 2 +
        C₁ * A₃ * Cr * CΔ * c ^ 2))) * (m * x ^ 2) := add_le_add hS1 hS2
    _ = _ := by rw [hA₃]; ring

end LX_num2

section LX_num3

set_option maxHeartbeats 1000000 in
/-- Equal pair: the crude bound of the main terms. -/
private theorem LX_num_eq (D : ℕ) (c Kc C₁ Ce u z x m ρ r r₂₁ Cd₁ Cd₂ : ℝ)
    (hD : 1 ≤ D) (hc : 1 ≤ c) (hKc : 0 ≤ Kc) (hC₁ : 0 ≤ C₁) (hCe : 0 ≤ Ce) (hu : 1 ≤ u)
    (hz : 1 ≤ z) (hx : 0 < x) (hm : 0 ≤ m) (hρ : 1 ≤ ρ) (hr : 0 ≤ r) (hr₂ : 0 ≤ r₂₁)
    (hCd₁ : 0 ≤ Cd₁) (hCd₂ : 0 ≤ Cd₂) (R6 : u * z ≤ c * x) (hρu : ρ ≤ u) (hρz : ρ ≤ z)
    (hrr : r ≤ Ce * ρ) (hrr₂ : r₂₁ ≤ Ce * ρ) (hCd₁' : Cd₁ ≤ C₁ * ρ) (hCd₂' : Cd₂ ≤ C₁ * ρ) :
    (Kc * m * (D * r * ((4 + Cd₁ + Cd₂) * (D * r * (D * (25 / 16))) +
      LX_RemB D r r₂₁ 3 Cd₁ Cd₂))) * u ≤
      (Kc * (D * Ce * (((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) +
        (5 * D + (10 * D * C₁ + C₁) + 2850 * (D : ℝ) ^ 3 * Ce +
          3 * C₁ * ((D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
            (D : ℝ) ^ 5 * (62500 / 64)) * Ce)) * c ^ 2)) * (m * x ^ 2) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : ρ ≤ ρ ^ 2 := le_self_pow₀ hρ (by norm_num)
  have hRem : LX_RemB D r r₂₁ 3 Cd₁ Cd₂ ≤ LX_RemB D (Ce * ρ) (Ce * ρ) 3 (C₁ * ρ) (C₁ * ρ) :=
    LX_RemB_mono D hr hr₂ (by norm_num) hCd₁ hCd₂ hrr hrr₂ le_rfl hCd₁' hCd₂'
  rw [LX_RemB_eq] at hRem
  set A₃ : ℝ := (D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
    (D : ℝ) ^ 5 * (62500 / 64) with hA₃
  have hA₃0 : 0 ≤ A₃ := by rw [hA₃]; positivity
  set Aeq : ℝ := 5 * D + (10 * D * C₁ + C₁) + 2850 * (D : ℝ) ^ 3 * Ce + 3 * C₁ * A₃ * Ce with hAeq
  have hAeq0 : 0 ≤ Aeq := by rw [hAeq]; positivity
  have hR1 : LX_RemB D r r₂₁ 3 Cd₁ Cd₂ ≤ Aeq * ρ ^ 2 := by
    refine hRem.trans ?_
    have h1 : 5 * (D : ℝ) ≤ 5 * D * ρ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (one_le_pow₀ hρ : 1 ≤ ρ ^ 2) hD0]
    have h2 : (10 * D * C₁ + C₁) * ρ ≤ (10 * D * C₁ + C₁) * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left hρ2 (by positivity)
    have h3 : 950 * (D : ℝ) ^ 3 * (Ce * ρ) * 3 ≤ 2850 * (D : ℝ) ^ 3 * Ce * ρ ^ 2 := by
      have : ρ ≤ ρ ^ 2 := hρ2
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2850 * (D : ℝ) ^ 3 * Ce)]
    have h4 : (C₁ * A₃) * ((Ce * ρ) * ρ * 3) = 3 * C₁ * A₃ * Ce * ρ ^ 2 := by ring
    rw [hAeq]
    nlinarith [h1, h2, h3, h4]
  have hS : (4 + Cd₁ + Cd₂) * (D * r * (D * (25 / 16))) ≤
      ((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) * ρ ^ 2 := by
    have hs : 4 + Cd₁ + Cd₂ ≤ (4 + 2 * C₁) * ρ := by nlinarith
    calc (4 + Cd₁ + Cd₂) * (D * r * (D * (25 / 16))) ≤
        ((4 + 2 * C₁) * ρ) * (D * (Ce * ρ) * (D * (25 / 16))) := by gcongr
      _ = ((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) * ρ ^ 2 := by ring
  have hρ3 : ρ ^ 3 * u ≤ (c * x) ^ 2 := by
    have h1 : ρ ^ 3 ≤ ρ * z ^ 2 := by
      calc ρ ^ 3 = ρ * ρ ^ 2 := by ring
        _ ≤ ρ * z ^ 2 := by gcongr
    calc ρ ^ 3 * u ≤ (ρ * z ^ 2) * u := by gcongr
      _ ≤ (u * z ^ 2) * u := by gcongr
      _ = (u * z) ^ 2 := by ring
      _ ≤ (c * x) ^ 2 := by gcongr
  have hT : (4 + Cd₁ + Cd₂) * (D * r * (D * (25 / 16))) + LX_RemB D r r₂₁ 3 Cd₁ Cd₂ ≤
      (((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) + Aeq) * ρ ^ 2 := by
    nlinarith [hS, hR1]
  have hsum0 : 0 ≤ (4 + Cd₁ + Cd₂) * (D * r * (D * (25 / 16))) + LX_RemB D r r₂₁ 3 Cd₁ Cd₂ := by
    unfold LX_RemB; positivity
  have hB0 : 0 ≤ (((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) + Aeq) := by positivity
  calc (Kc * m * (D * r * ((4 + Cd₁ + Cd₂) * (D * r * (D * (25 / 16))) +
        LX_RemB D r r₂₁ 3 Cd₁ Cd₂))) * u ≤
      (Kc * m * (D * (Ce * ρ) * ((((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) + Aeq) * ρ ^ 2))) * u := by
        gcongr
    _ = (Kc * D * Ce * (((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) + Aeq) * m) * (ρ ^ 3 * u) := by
        ring
    _ ≤ (Kc * D * Ce * (((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) + Aeq) * m) * (c * x) ^ 2 := by
        gcongr
    _ = _ := by simp only [hAeq, hA₃]; ring

end LX_num3

section LX_real

private theorem LX_pow_ge (K a : ℝ) (ha : 0 < a) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K ≤ (N : ℝ) ^ a := by
  have := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := (this.eventually_ge_atTop K).exists_forall_of_atTop
  exact ⟨N₀, fun N hN => h N hN⟩

private theorem LX_rp (n a : ℝ) (k : ℕ) (hn : 0 < n) : (n ^ a) ^ k = n ^ (a * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]

/-- The relations among the scales `u = n^{ε_g}`, `s = n^{-1/2}`, `m = n⁻¹`, `w = n^{-δ_A}`,
`x = η⁻¹`, `z = (Im m)⁻¹`. -/
private theorem LX_real (n εg δA τe c η y : ℝ) (hn : 1 ≤ n) (hεg : 0 < εg) (hεg1 : εg < 1 / 8)
    (hεg2 : εg < δA / 4) (hδA : 0 < δA) (hτe : 0 < τe) (hc : 1 ≤ c) (hη : 0 < η) (hy : 0 < y)
    (hy1 : y ≤ 1) (h13 : c⁻¹ * n ^ (-(1 / 3 : ℝ) + τe) ≤ η) (hq2 : η / y ≤ c * n ^ (-εg)) :
    1 ≤ n ^ εg ∧ (n ^ εg) ^ 4 * n ^ (-(1 / 2 : ℝ)) ≤ 1 ∧ (n ^ εg) ^ 4 * n⁻¹ ≤ 1 ∧
      (n ^ εg) ^ 4 * n ^ (-δA) ≤ 1 ∧ (n ^ εg) ^ 2 * n ^ (-(δA / 2)) ≤ 1 ∧
      (n ^ εg) ^ 3 * (n⁻¹ * η⁻¹) ≤ c ∧ 1 ≤ c * η⁻¹ ∧ n ^ εg * y⁻¹ ≤ c * η⁻¹ ∧
      η⁻¹ ≤ c * n ^ (1 / 3 : ℝ) ∧ η * η⁻¹ = 1 ∧ 1 ≤ y⁻¹ ∧ n ^ (-εg) ≤ 1 := by
  have hn0 : 0 < n := by linarith
  have hu : 1 ≤ n ^ εg := Real.one_le_rpow hn hεg.le
  have hu0 : 0 < n ^ εg := by linarith
  have hnm : ∀ e : ℝ, e ≤ 0 → n ^ e ≤ 1 := fun e he => Real.rpow_le_one_of_one_le_of_nonpos hn he
  have hηx : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  have hc0 : 0 < c := by linarith
  -- η⁻¹ ≤ c n^{1/3}
  have h4 : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hx3 : η⁻¹ ≤ c * n ^ (1 / 3 : ℝ) := by
    have h1 : n ^ (-(1 / 3 : ℝ)) ≤ n ^ (-(1 / 3 : ℝ) + τe) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    have h2 : c⁻¹ * n ^ (-(1 / 3 : ℝ)) ≤ η := (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h13
    rw [Real.rpow_neg hn0.le] at h2
    have := inv_anti₀ (by positivity) h2
    rwa [mul_inv, inv_inv, inv_inv] at this
  -- η ≤ c n^{-εg} y
  have hη1 : η ≤ c * n ^ (-εg) * y := (div_le_iff₀ hy).mp hq2
  have hηc : η ≤ c := by
    have : n ^ (-εg) ≤ 1 := hnm _ (by linarith)
    calc η ≤ c * n ^ (-εg) * y := hη1
      _ ≤ c * 1 * 1 := by gcongr
      _ = c := by ring
  have hnu : n ^ (-εg) * n ^ εg = 1 := by
    rw [← Real.rpow_add hn0]; simp
  have e1 : (n ^ εg) ^ 4 * n ^ (-(1 / 2 : ℝ)) = n ^ (4 * εg - 1 / 2) := by
    rw [LX_rp n εg 4 hn0, ← Real.rpow_add hn0]; congr 1; push_cast; ring
  have e2 : (n ^ εg) ^ 4 * n⁻¹ = n ^ (4 * εg - 1) := by
    rw [LX_rp n εg 4 hn0, ← Real.rpow_neg_one, ← Real.rpow_add hn0]; congr 1; push_cast; ring
  have e3 : (n ^ εg) ^ 4 * n ^ (-δA) = n ^ (4 * εg - δA) := by
    rw [LX_rp n εg 4 hn0, ← Real.rpow_add hn0]; congr 1; push_cast; ring
  have e4 : (n ^ εg) ^ 2 * n ^ (-(δA / 2)) = n ^ (2 * εg - δA / 2) := by
    rw [LX_rp n εg 2 hn0, ← Real.rpow_add hn0]; congr 1; push_cast; ring
  have e5 : (n ^ εg) ^ 3 * n⁻¹ * n ^ (1 / 3 : ℝ) = n ^ (3 * εg - 2 / 3) := by
    rw [LX_rp n εg 3 hn0, ← Real.rpow_neg_one, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  refine ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx3, hηx, ?_, hnm _ (by linarith)⟩
  · rw [e1]; exact hnm _ (by linarith)
  · rw [e2]; exact hnm _ (by linarith)
  · rw [e3]; exact hnm _ (by linarith)
  · rw [e4]; exact hnm _ (by linarith)
  · have h1 : (n ^ εg) ^ 3 * n⁻¹ * n ^ (1 / 3 : ℝ) ≤ 1 := by rw [e5]; exact hnm _ (by linarith)
    calc (n ^ εg) ^ 3 * (n⁻¹ * η⁻¹) = ((n ^ εg) ^ 3 * n⁻¹) * η⁻¹ := by ring
      _ ≤ ((n ^ εg) ^ 3 * n⁻¹) * (c * n ^ (1 / 3 : ℝ)) := by gcongr
      _ = c * ((n ^ εg) ^ 3 * n⁻¹ * n ^ (1 / 3 : ℝ)) := by ring
      _ ≤ c * 1 := by gcongr
      _ = c := mul_one c
  · have : c⁻¹ ≤ η⁻¹ := inv_anti₀ hη hηc
    calc 1 = c * c⁻¹ := (mul_inv_cancel₀ hc0.ne').symm
      _ ≤ c * η⁻¹ := by gcongr
  · have h1 : n ^ εg * η ≤ c * y := by
      calc n ^ εg * η ≤ n ^ εg * (c * n ^ (-εg) * y) := by gcongr
        _ = c * y * (n ^ (-εg) * n ^ εg) := by ring
        _ = c * y := by rw [hnu]; ring
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hy hη]
    linarith
  · rw [← one_div, le_div_iff₀ hy]; linarith

end LX_real

section LX_pair

variable {D N : ℕ}

/-- The estimate of `ELmat - KTheta` entrywise for one pair `(z₁, z₂)`, with the explicit remainders
of the main terms (conjugate pair: `Sb`, equal pair: crude). -/
private theorem LX_pair_core [Nonempty (Idx D N)] (hD : 1 ≤ D) (hN : 1 ≤ N)
    (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (m₁ m₂ : ℂ) (ε₀ Cd₁ Cd₂ : ℝ) (hF₁ : LX_Fz (MExt (lam D N A) z₁) m₁ ε₀)
    (hF₂ : LX_Fz (MExt (lam D N A) z₂) m₂ ε₀)
    (hd₁ : 1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) ≠ 0)
    (hC₁ : ‖1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁)‖⁻¹ ≤ Cd₁)
    (hd₂ : 1 - ntr (MExt (lam D N A) z₂ * MExt (lam D N A) z₂) ≠ 0)
    (hC₂ : ‖1 - ntr (MExt (lam D N A) z₂ * MExt (lam D N A) z₂)‖⁻¹ ≤ Cd₂)
    (hdet : (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0)
    (hdet₂ : (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ).det ≠ 0)
    (hc3 : ∀ a b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ (Ea D N a) b x =
      if x = a then KTheta (lam D N A) θ z₁ z₂ a b else 0)
    (hc4 : ∀ b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ 1 b x = KTheta (lam D N A) θ z₁ z₂ x b)
    (hc6 : opNorm (PTheta D θ * KTheta (lam D N A) θ z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ 1)
    (κ : ℂ) (kap : ℝ) (hκ : ‖κ‖ ≤ kap) (hkap : 0 ≤ kap)
    (τ₁ ε ε₁₅ ε₁₄ : ℝ) (hε : 0 ≤ ε) (he15 : 0 ≤ ε₁₅) (he14 : 0 ≤ ε₁₄)
    (H15₁ : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * B) ∂μ) -
        κ * lead15 (lam D N A) z₁ B‖ ≤ ε₁₅)
    (H15₂ : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) * B) ∂μ) -
        κ * lead15 (lam D N A) z₂ B‖ ≤ ε₁₅)
    (H14 : ∀ a b : Fin D, ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) θ h z₁ z₂ a (Ea D N b) ∂μ) -
      ((D : ℂ) * κ) * lead14 (lam D N A) θ z₁ z₂ a b‖ ≤ ε₁₄)
    (hAv₁ : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      μ {h | (N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |z₁.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * B)‖} ≤
        ENNReal.ofReal ε)
    (hAv₂ : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      μ {h | (N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |z₂.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) * B)‖} ≤
        ENNReal.ofReal ε)
    (hTwo : μ {h | (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
        hsNorm (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂)} ≤ ENNReal.ofReal ε)
    (hBB : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 → ∀ a' : Fin D,
      μ {h | (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹) <
        ‖ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N a' * res (Matrix.of h + lam D N A) z₁ *
          B) - ∑ x, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ a' x *
          ntr (MExt (lam D N A) z₂ * Ea D N x * MExt (lam D N A) z₁ * B)‖} ≤ ENNReal.ofReal ε)
    (S : ℂ) (Sb RemB : ℝ) (hSb : 0 ≤ Sb) (hS : ‖S‖ ≤ Sb)
    (hmain : ∀ a b : Fin D, ‖LX_Main (lam D N A) θ z₁ z₂ a b - S * KTheta (lam D N A) θ z₁ z₂ a b‖ ≤
      RemB) :
    ∀ a b : Fin D, ‖(ELmat μ (lam D N A) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) a b‖ ≤
      D * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ *
        LX_ErrBd D (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)
          (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹) ε₁₅ ε₁₄
          (LX_BE1 D N τ₁ z.im (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) ε)
          (LX_BE2 D N τ₁ z.im (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹) ε) +
      kap * (D * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ *
        (Sb * (D * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ * (D * (25 / 16))) + RemB)) := by
  set Λ := lam D N A with hΛdef
  have hM₁ := hF₁.hM
  have hM₂ := hF₂.hM
  have hdec := LX_pair_decomp μ hμh hD θ hθ0 hθ1 A z hz z₁ z₂ h₁ h₂ hM₁ hM₂ hdet κ ε₁₅ ε₁₄ _ _ he15
    he14 H15₁ H15₂ H14
    (fun a c x b => LX_E1 μ hμh hD θ A z hz z₁ z₂ h₁ h₂ hM₁ hM₂ hdet τ₁ ε hε hAv₁ hTwo a c x b)
    (fun a b c x => LX_E2 μ hμh hD θ A z hz z₁ z₂ h₁ h₂ hM₁ hM₂ hdet₂ τ₁ ε hε hAv₂ hBB a b c x)
  intro a b
  have hK : ∀ x b : Fin D, ‖KTheta Λ θ z₁ z₂ x b‖ ≤
      D * opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ * (D * (25 / 16)) :=
    fun x b => LX_K_bound Λ θ z₁ z₂ x b hM₁ hM₂
  have hRn : ∀ a x : Fin D, ‖(1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x‖ ≤
      opNorm (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ := fun a x => norm_apply_le_opNorm _ a x
  have := LX_combine (fun a b => (ELmat μ Λ z₁ z₂ - KTheta Λ θ z₁ z₂) a b)
    (fun a x => (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x) (fun x b => LX_Main Λ θ z₁ z₂ x b)
    (fun x b => KTheta Λ θ z₁ z₂ x b) κ S _ _ _ Sb _ kap (LX_op_nonneg _) hSb
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg D) (LX_op_nonneg _)) (by positivity)) hkap (by
      intro a b
      have := hdec a b
      simpa [Matrix.sub_apply] using this) hRn
    (fun x b => hmain x b) hS hK hκ a b
  simpa using this

end LX_pair

section LX_aux3

/-- The bracket of (3.45) [pre_cancellation] at `(z, z̄)` is the scalar of the main terms. -/
private theorem LX_S_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (m : ℂ) :
    ((star m) ^ 4 + m ^ 2 * (star m) ^ 2 + m ^ 3 * star m + m * (star m) ^ 3 +
        m ^ 5 * star m / (1 - ntr (M * M)) + (star m) ^ 6 / (1 - ntr (Mᴴ * Mᴴ))) =
      star m ^ 4 + ((‖m‖ ^ 4 : ℝ) : ℂ) + ((‖m‖ ^ 2 : ℝ) : ℂ) * m ^ 2 +
        ((‖m‖ ^ 2 : ℝ) : ℂ) * star m ^ 2 + m ^ 4 * ((‖m‖ ^ 2 : ℝ) : ℂ) / (1 - ntr (M * M)) +
        star m ^ 6 / (1 - ntr (Mᴴ * Mᴴ)) := by
  have h2 : ((‖m‖ ^ 2 : ℝ) : ℂ) = m * star m := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h4 : ((‖m‖ ^ 4 : ℝ) : ℂ) = (m * star m) ^ 2 := by
    rw [← h2]; push_cast; try ring
  rw [h2, h4]
  ring

private theorem LX_S_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (m : ℂ) :
    (m ^ 4 + (star m) ^ 2 * m ^ 2 + (star m) ^ 3 * m + star m * m ^ 3 +
        (star m) ^ 5 * m / (1 - ntr (Mᴴ * Mᴴ)) + m ^ 6 / (1 - ntr (M * M))) =
      star ((star m) ^ 4 + m ^ 2 * (star m) ^ 2 + m ^ 3 * star m + m * (star m) ^ 3 +
        m ^ 5 * star m / (1 - ntr (M * M)) + (star m) ^ 6 / (1 - ntr (Mᴴ * Mᴴ))) := by
  have e1 : star (ntr (M * M)) = ntr (Mᴴ * Mᴴ) := by
    have h : star (M * M).trace = (Mᴴ * Mᴴ).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
    unfold ntr
    rw [star_mul', h, star_inv₀, star_natCast]
  have e2 : star (ntr (Mᴴ * Mᴴ)) = ntr (M * M) := by
    rw [← e1, star_star]
  simp only [star_add, star_mul, star_pow, star_div₀, star_sub, star_one, star_star, e1, e2]
  ring

private theorem LX_tail (D n c Cr u x r r₂₁ ε : ℝ) (hD : 1 ≤ D) (hn : 1 ≤ n) (hc : 1 ≤ c)
    (hCr : 0 ≤ Cr) (hu : u ≤ n) (hx : x ≤ c * n) (hx0 : 0 ≤ x) (hr : 0 ≤ r) (hr₂ : 0 ≤ r₂₁)
    (hrr : r ≤ Cr * u) (hrr₂ : r₂₁ ≤ Cr * u) (hu1 : 1 ≤ u) (hε : 0 ≤ ε) :
    (D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) * (ε + ε) +
      (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) + D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) *
        (ε + ε) ≤ (6 * D * (c + 2) * (D * c ^ 2 + 2 * D ^ 2 * Cr) * (ε + ε)) * n ^ 3 := by
  have hn0 : 0 ≤ n := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hx1 : x + 5 / 4 ≤ (c + 2) * n := by nlinarith
  have hx2 : x * x ≤ c ^ 2 * n ^ 2 := by nlinarith
  have hr1 : r ≤ Cr * n := hrr.trans (by gcongr)
  have hr2 : r₂₁ ≤ Cr * n := hrr₂.trans (by gcongr)
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hB1 : D * (x * x) + D * r * (D * (25 / 16)) ≤ (D * c ^ 2 + 2 * D ^ 2 * Cr) * n ^ 2 := by
    have : D * r * (D * (25 / 16)) ≤ D ^ 2 * (25 / 16) * (Cr * n) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ D),
      mul_le_mul_of_nonneg_left hn2 (by positivity : (0 : ℝ) ≤ D ^ 2 * Cr)]
  have hB2 : D * (x * (5 / 4) * x) + D * r₂₁ * (D * ((25 / 16) * (5 / 4))) ≤
      (2 * D * c ^ 2 + 3 * D ^ 2 * Cr) * n ^ 2 := by
    have : D * r₂₁ * (D * ((25 / 16) * (5 / 4))) ≤ D ^ 2 * (125 / 64) * (Cr * n) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ D),
      mul_le_mul_of_nonneg_left hn2 (by positivity : (0 : ℝ) ≤ D ^ 2 * Cr)]
  have hε2 : 0 ≤ ε + ε := by linarith
  have hDn : (0 : ℝ) ≤ D := by linarith
  have t1 : (D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) ≤
      (D * ((c + 2) * n * (5 / 4))) * ((D * c ^ 2 + 2 * D ^ 2 * Cr) * n ^ 2) :=
    mul_le_mul (by gcongr) hB1 (by positivity) (by positivity)
  have t2 : (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) + D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) ≤
      (D * ((c + 2) * n)) * ((2 * D * c ^ 2 + 3 * D ^ 2 * Cr) * n ^ 2) :=
    mul_le_mul (by gcongr) hB2 (by positivity) (by positivity)
  have t3 : (D * ((c + 2) * n * (5 / 4))) * ((D * c ^ 2 + 2 * D ^ 2 * Cr) * n ^ 2) +
      (D * ((c + 2) * n)) * ((2 * D * c ^ 2 + 3 * D ^ 2 * Cr) * n ^ 2) ≤
      (6 * D * (c + 2) * (D * c ^ 2 + 2 * D ^ 2 * Cr)) * n ^ 3 := by
    have h1 : 0 ≤ D * (c + 2) * n ^ 3 * (D * c ^ 2) := by positivity
    have h2 : 0 ≤ D * (c + 2) * n ^ 3 * (D ^ 2 * Cr) := by positivity
    nlinarith [h1, h2]
  calc (D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) * (ε + ε) +
        (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) + D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) *
          (ε + ε) =
      ((D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) +
        (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) + D * r₂₁ * (D * ((25 / 16) * (5 / 4))))) *
          (ε + ε) := by ring
    _ ≤ ((6 * D * (c + 2) * (D * c ^ 2 + 2 * D ^ 2 * Cr)) * n ^ 3) * (ε + ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hε2
    _ = _ := by ring

end LX_aux3

section LX_mainN

variable {D N : ℕ}

/-- The constant of the error terms. -/
private def LX_Kerr (D : ℕ) (c Cr : ℝ) : ℝ :=
  D * Cr * (D * (5 / 4) * (c + 1 + c ^ 2) + (1 + Cr) * (c + 1 + c ^ 2) +
    2 * D ^ 5 * (125 / 64) * Cr * (c + 1 + c ^ 2) + (D ^ 3 + D ^ 4) * (5 / 4) * Cr * c +
    2 * D ^ 2)

/-- The constant of the main terms for a conjugate pair. -/
private def LX_Kconj (D : ℕ) (c Cr C₁ CΔ Kc Kb : ℝ) : ℝ :=
  Kc * (D * Cr * (Kb * (c ^ 3 + c ^ 2) * (D * Cr * (D * (25 / 16))) +
    (5 * D + 10 * D * C₁ + C₁) * c ^ 2 + 950 * (D : ℝ) ^ 3 * Cr * CΔ * c ^ 2 +
    C₁ * ((D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
      (D : ℝ) ^ 5 * (62500 / 64)) * Cr * CΔ * c ^ 2))

/-- The constant of the main terms for an equal pair. -/
private def LX_Keq (D : ℕ) (c Ce C₁ Kc : ℝ) : ℝ :=
  Kc * (D * Ce * (((4 + 2 * C₁) * ((D : ℝ) ^ 2 * Ce * (25 / 16))) +
    (5 * D + (10 * D * C₁ + C₁) + 2850 * (D : ℝ) ^ 3 * Ce +
      3 * C₁ * ((D : ℝ) ^ 4 * (25 / 16) * (500 * D + 1) + (25 / 16) * (D : ℝ) ^ 2 +
        (D : ℝ) ^ 5 * (62500 / 64)) * Ce)) * c ^ 2)

/-- The total constant. -/
private def LX_Kfin (D : ℕ) (c Cr Ce C₁ CΔ Kc Kb : ℝ) : ℝ :=
  LX_Kerr D c Cr + LX_Kconj D c Cr C₁ CΔ Kc Kb + LX_Keq D c Ce C₁ Kc

private theorem LX_Kerr_nonneg (D : ℕ) (c Cr : ℝ) (hc : 0 ≤ c) (hCr : 0 ≤ Cr) :
    0 ≤ LX_Kerr D c Cr := by unfold LX_Kerr; positivity

private theorem LX_Kconj_nonneg (D : ℕ) (c Cr C₁ CΔ Kc Kb : ℝ) (hc : 0 ≤ c) (hCr : 0 ≤ Cr)
    (hC₁ : 0 ≤ C₁) (hCΔ : 0 ≤ CΔ) (hKc : 0 ≤ Kc) (hKb : 0 ≤ Kb) :
    0 ≤ LX_Kconj D c Cr C₁ CΔ Kc Kb := by unfold LX_Kconj; positivity

private theorem LX_Keq_nonneg (D : ℕ) (c Ce C₁ Kc : ℝ) (hc : 0 ≤ c) (hCe : 0 ≤ Ce)
    (hC₁ : 0 ≤ C₁) (hKc : 0 ≤ Kc) : 0 ≤ LX_Keq D c Ce C₁ Kc := by unfold LX_Keq; positivity

private theorem LX_S_crude (m₁ m₂ : ℂ) (s₁ s₂ : ℂ) (Cd₁ Cd₂ : ℝ) (hm₁ : ‖m₁‖ ≤ 1) (hm₂ : ‖m₂‖ ≤ 1)
    (hs₁ : 1 - s₁ ≠ 0) (hs₂ : 1 - s₂ ≠ 0)
    (hC₁ : ‖1 - s₁‖⁻¹ ≤ Cd₁) (hC₂ : ‖1 - s₂‖⁻¹ ≤ Cd₂) :
    ‖(m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3) + m₁ ^ 5 * m₂ / (1 - s₁) +
      m₂ ^ 6 / (1 - s₂)‖ ≤ 4 + Cd₁ + Cd₂ := by
  have p : ∀ (k : ℕ) (m : ℂ), ‖m‖ ≤ 1 → ‖m ^ k‖ ≤ 1 := fun k m h => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h
  have n1 : ‖m₂ ^ 4‖ ≤ 1 := p 4 m₂ hm₂
  have n2 : ‖m₁ ^ 2 * m₂ ^ 2‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [p 2 m₁ hm₁, p 2 m₂ hm₂, norm_nonneg (m₁ ^ 2), norm_nonneg (m₂ ^ 2)]
  have n3 : ‖m₁ ^ 3 * m₂‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [p 3 m₁ hm₁, norm_nonneg (m₁ ^ 3), norm_nonneg m₂]
  have n4 : ‖m₁ * m₂ ^ 3‖ ≤ 1 := by
    rw [norm_mul]; nlinarith [p 3 m₂ hm₂, norm_nonneg (m₂ ^ 3), norm_nonneg m₁]
  have n5 : ‖m₁ ^ 5 * m₂ / (1 - s₁)‖ ≤ Cd₁ := by
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_inv]
    have h0 : 0 ≤ ‖1 - s₁‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have : ‖m₁ ^ 5‖ * ‖m₂‖ ≤ 1 := by nlinarith [p 5 m₁ hm₁, norm_nonneg (m₁ ^ 5), norm_nonneg m₂]
    calc ‖m₁ ^ 5‖ * ‖m₂‖ * ‖1 - s₁‖⁻¹ ≤ 1 * Cd₁ := mul_le_mul this hC₁ h0 zero_le_one
      _ = Cd₁ := one_mul _
  have n6 : ‖m₂ ^ 6 / (1 - s₂)‖ ≤ Cd₂ := by
    rw [div_eq_mul_inv, norm_mul, norm_inv]
    have h0 : 0 ≤ ‖1 - s₂‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    calc ‖m₂ ^ 6‖ * ‖1 - s₂‖⁻¹ ≤ 1 * Cd₂ := mul_le_mul (p 6 m₂ hm₂) hC₂ h0 zero_le_one
      _ = Cd₂ := one_mul _
  have := norm_add₃_le (a := (m₂ ^ 4 + m₁ ^ 2 * m₂ ^ 2 + m₁ ^ 3 * m₂ + m₁ * m₂ ^ 3))
    (b := m₁ ^ 5 * m₂ / (1 - s₁)) (c := m₂ ^ 6 / (1 - s₂))
  have h4 := norm_add₄_le (a := m₂ ^ 4) (b := m₁ ^ 2 * m₂ ^ 2) (c := m₁ ^ 3 * m₂) (d := m₁ * m₂ ^ 3)
  linarith

end LX_mainN

section LX_mainN2

variable {D N : ℕ}

set_option maxHeartbeats 3000000 in
private theorem LX_main_N [Nonempty (Idx D N)] (hD : 2 ≤ D) (hN : 1 ≤ N)
    (δA τe εg c Cr Ce C₁ CΔ Kc Kb τ₁ : ℝ) (hδA : 0 < δA) (hτe : 0 < τe) (hεg : 0 < εg)
    (hεg1 : εg < 1 / 8) (hεg2 : εg < δA / 4) (hc : 1 ≤ c) (hCr : 0 ≤ Cr) (hCe : 0 ≤ Ce)
    (hC₁ : 0 ≤ C₁) (hCΔ : 0 ≤ CΔ) (hKc : 0 ≤ Kc) (hKb : 0 ≤ Kb) (hCeCr : Ce ≤ Cr)
    (hCr4 : 4 * c ≤ Cr) (hτ₁ : 0 < τ₁)
    (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (κ : ℂ)
    (hκ : ‖κ‖ ≤ Kc * (N : ℝ)⁻¹) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm A ≤ (N : ℝ) ^ (-δA)) (z : ℂ) (hz : 0 < z.im)
    (hη : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im)
    (hq2 : z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg))
    (hy0 : 0 < (mExt (lam D N A) z).im) (hy1 : (mExt (lam D N A) z).im ≤ 1)
    (hFz : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) →
      LX_Fz (MExt (lam D N A) ξ) (mExt (lam D N A) ξ) (CΔ * (N : ℝ) ^ (-δA)))
    (hFz3 : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → LX_Fz (MExt (lam D N A) ξ) (mExt (lam D N A) ξ) 3)
    (hden : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) →
      1 - ntr (MExt (lam D N A) ξ * MExt (lam D N A) ξ) ≠ 0 ∧
      ‖1 - ntr (MExt (lam D N A) ξ * MExt (lam D N A) ξ)‖⁻¹ ≤
        C₁ * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg))
    (hRb : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
      opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ ≤ Cr * (N : ℝ) ^ εg ∧
      (z₂ = z₁ → opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ ≤
        Ce * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)))
    (hcirc : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (∀ a b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ (Ea D N a) b x =
        if x = a then KTheta (lam D N A) θ z₁ z₂ a b else 0) ∧
      (∀ b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ 1 b x = KTheta (lam D N A) θ z₁ z₂ x b) ∧
      opNorm (PTheta D θ * KTheta (lam D N A) θ z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ 1)
    (hbr : ‖star (mExt (lam D N A) z) ^ 4 + ((‖mExt (lam D N A) z‖ ^ 4 : ℝ) : ℂ) +
            ((‖mExt (lam D N A) z‖ ^ 2 : ℝ) : ℂ) * mExt (lam D N A) z ^ 2 +
            ((‖mExt (lam D N A) z‖ ^ 2 : ℝ) : ℂ) * star (mExt (lam D N A) z) ^ 2 +
            mExt (lam D N A) z ^ 4 * ((‖mExt (lam D N A) z‖ ^ 2 : ℝ) : ℂ) /
              (1 - ntr (MExt (lam D N A) z * MExt (lam D N A) z)) +
            star (mExt (lam D N A) z) ^ 6 /
              (1 - ntr ((MExt (lam D N A) z)ᴴ * (MExt (lam D N A) z)ᴴ))‖ ≤
          Kb * (z.im * ((mExt (lam D N A) z).im ^ 3)⁻¹ +
            (N : ℝ) ^ (-(δA / 2)) * ((mExt (lam D N A) z).im ^ 2)⁻¹))
    (h15 : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B) ∂μ) -
        κ * lead15 (lam D N A) ξ B‖ ≤ (N : ℝ) ^ τ₁ * (min ((mExt (lam D N A) z).im)⁻¹
          ((N : ℝ) ^ εg) * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ +
            (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ)⁻¹ * opNorm A)))
    (h14 : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
      ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) θ h z₁ z₂ a (Ea D N b) ∂μ) -
        ((D : ℂ) * κ) * lead14 (lam D N A) θ z₁ z₂ a b‖ ≤
      (N : ℝ) ^ τ₁ * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) *
        (z.im ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹))
    (hAv : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      μ {h | (N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * |ξ.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))))
    (hTwo : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      μ {h | (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
        hsNorm (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))))
    (hBB : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 → ∀ a' : Fin D,
      μ {h | (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a' * res (Matrix.of h + lam D N A) z₂ *
          B) - ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a' x *
          ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * B)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))))
    (htail : 12 * (D : ℝ) * (c + 2) * (D * c ^ 2 + 2 * (D : ℝ) ^ 2 * Cr) * c ^ 2 ≤ (N : ℝ) ^ 4)
    (hτ₁1 : 1 ≤ (N : ℝ) ^ τ₁) :
    ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
      ‖(ELmat μ (lam D N A) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) a b‖ ≤
        LX_Kfin D c Cr Ce C₁ CΔ Kc Kb *
          (((N : ℝ) ^ τ₁) ^ 2 * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * ((N : ℝ) ^ εg)⁻¹)) := by
  intro z₁ z₂ h₁ h₂ a b
  have hD1 : 1 ≤ D := by omega
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hc0 : 0 < c := by linarith
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  obtain ⟨hu1, R1, R2, R3, R7, R4, R5, R6, hx3, hηx, hz1, hnu⟩ :=
    LX_real (N : ℝ) εg δA τe c z.im (mExt (lam D N A) z).im hn1 hεg hεg1 hεg2 hδA hτe hc hz hy0
      hy1 hη hq2
  -- the scales
  have hs0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
  have hw0 : 0 ≤ (N : ℝ) ^ (-δA) := Real.rpow_nonneg hn0.le _
  have hw₂0 : 0 ≤ (N : ℝ) ^ (-(δA / 2)) := Real.rpow_nonneg hn0.le _
  have hm0 : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hn0
  have hx0 : 0 < (z.im)⁻¹ := inv_pos.mpr hz
  have hy0' : 0 < ((mExt (lam D N A) z).im)⁻¹ := inv_pos.mpr hy0
  have rp32 : (N : ℝ) ^ (-(3 / 2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show (-(3 / 2 : ℝ)) = -1 + -(1 / 2) by norm_num, Real.rpow_add hn0, Real.rpow_neg_one]
  have rp2 : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ)⁻¹) ^ 2 := by
    rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have hρ1 : 1 ≤ min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) := le_min hz1 hu1
  have hρu : min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) ≤ (N : ℝ) ^ εg := min_le_right _ _
  have hρz : min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) ≤ ((mExt (lam D N A) z).im)⁻¹ :=
    min_le_left _ _
  have hux : (N : ℝ) ^ εg ≤ c * (z.im)⁻¹ := by
    have := R6
    calc (N : ℝ) ^ εg = (N : ℝ) ^ εg * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ εg * ((mExt (lam D N A) z).im)⁻¹ := mul_le_mul_of_nonneg_left hz1 (by linarith)
      _ ≤ c * (z.im)⁻¹ := this
  -- pair data
  obtain ⟨hdet, hr, hreq⟩ := hRb z₁ z₂ h₁ h₂
  obtain ⟨hdet₂, hr₂, -⟩ := hRb z₂ z₁ h₂ h₁
  obtain ⟨hc3, hc4, hc6⟩ := hcirc z₁ z₂ h₁ h₂
  obtain ⟨hd₁, hC₁'⟩ := hden z₁ h₁
  obtain ⟨hd₂, hC₂'⟩ := hden z₂ h₂
  set ρ := min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) with hρdef
  set r := opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ with hrdef
  set r₂₁ := opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ with hr₂₁def
  have hr0 : 0 ≤ r := LX_op_nonneg _
  have hr₂0 : 0 ≤ r₂₁ := LX_op_nonneg _
  set n : ℝ := (N : ℝ) with hn
  set u : ℝ := n ^ εg with hu
  set P : ℝ := n ^ τ₁ with hP
  set s : ℝ := n ^ (-(1 / 2 : ℝ)) with hs
  set m : ℝ := n⁻¹ with hm
  set w : ℝ := n ^ (-δA) with hw
  set x : ℝ := (z.im)⁻¹ with hxdef
  set eps : ℝ := n ^ (-(10 : ℝ)) with hepsdef
  have heps0 : 0 ≤ eps := Real.rpow_nonneg hn0.le _
  have hP1 : 1 ≤ P := hτ₁1
  have hx2 : (z.im ^ 2)⁻¹ = x ^ 2 := by rw [hxdef, inv_pow]
  have hcx : 1 ≤ c * x := R5
  have hxx : x ≤ c * x ^ 2 := by
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * (c * x) := mul_le_mul_of_nonneg_left hcx hx0.le
      _ = c * x ^ 2 := by ring
  have hcx2 : 1 ≤ (c * x) ^ 2 := one_le_pow₀ hcx
  set σ : ℝ := c * s + m + c ^ 2 * w with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  set Y : ℝ := P * (m * x ^ 2) with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hrr : r ≤ Cr * u := hr
  have hrr₂ : r₂₁ ≤ Cr * u := hr₂
  have hQ1 : u ^ 4 * σ ≤ c + 1 + c ^ 2 := by
    have e : u ^ 4 * σ = c * (u ^ 4 * s) + u ^ 4 * m + c ^ 2 * (u ^ 4 * w) := by rw [hσdef]; ring
    rw [e]
    have h1 : c * (u ^ 4 * s) ≤ c * 1 := mul_le_mul_of_nonneg_left R1 (by linarith)
    have h3 : c ^ 2 * (u ^ 4 * w) ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left R3 (by positivity)
    linarith
  have hQ2 : u ^ 3 * (m * x) ≤ c := by
    have : m * x = n⁻¹ * (z.im)⁻¹ := rfl
    rw [this]; exact R4
  -- the first-order error terms
  set ε₁₅ : ℝ := n ^ τ₁ * (ρ * (n ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ + n ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ +
    n⁻¹ * opNorm A)) with hε₁₅def
  set ε₁₄ : ℝ := n ^ τ₁ * (n ^ (-(3 / 2 : ℝ)) * (z.im ^ 2)⁻¹ + n ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ * r)
    with hε₁₄def
  have he15 : 0 ≤ ε₁₅ := by
    rw [hε₁₅def]
    have : 0 ≤ opNorm A := LX_op_nonneg A
    have : 0 ≤ ρ := by linarith
    positivity
  have he14 : 0 ≤ ε₁₄ := by rw [hε₁₄def]; positivity
  have hu0 : 0 ≤ u := by linarith
  have hsσ : s ≤ σ := by
    have h1 : s ≤ c * s := le_mul_of_one_le_left hs0 hc
    have h2 : 0 ≤ m := hm0.le
    have h3 : 0 ≤ c ^ 2 * w := by positivity
    rw [hσdef]; linarith
  have hmσ : m ≤ σ := by
    have h1 : 0 ≤ c * s := by positivity
    have h3 : 0 ≤ c ^ 2 * w := by positivity
    rw [hσdef]; linarith
  have e15 : ε₁₅ ≤ u * σ * Y := by
    have hA0 := LX_op_nonneg A
    have t1 : m * s * x ≤ m * x ^ 2 * (c * s) := by
      calc m * s * x ≤ m * s * (c * x ^ 2) := mul_le_mul_of_nonneg_left hxx (by positivity)
        _ = m * x ^ 2 * (c * s) := by ring
    have t3 : m * w ≤ m * x ^ 2 * (c ^ 2 * w) := by
      calc m * w = m * w * 1 := (mul_one _).symm
        _ ≤ m * w * (c * x) ^ 2 := mul_le_mul_of_nonneg_left hcx2 (by positivity)
        _ = m * x ^ 2 * (c ^ 2 * w) := by ring
    have hin : m * s * x + m ^ 2 * x ^ 2 + m * opNorm A ≤
        m * x ^ 2 * (c * s) + m * x ^ 2 * m + m * x ^ 2 * (c ^ 2 * w) := by
      have : m * opNorm A ≤ m * w := mul_le_mul_of_nonneg_left hA hm0.le
      have e2 : m ^ 2 * x ^ 2 = m * x ^ 2 * m := by ring
      linarith
    have hin0 : 0 ≤ m * s * x + m ^ 2 * x ^ 2 + m * opNorm A := by positivity
    calc ε₁₅ = P * (ρ * (m * s * x + m ^ 2 * x ^ 2 + m * opNorm A)) := by
          rw [hε₁₅def, rp32, rp2, hx2]
      _ ≤ P * (u * (m * x ^ 2 * (c * s) + m * x ^ 2 * m + m * x ^ 2 * (c ^ 2 * w))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hρu hin hin0 hu0
      _ = u * σ * Y := by rw [hσdef, hYdef]; ring
  have e14 : ε₁₄ ≤ σ * (1 + Cr * u) * Y := by
    have t1 : m * s * x ^ 2 ≤ m * x ^ 2 * σ := by
      calc m * s * x ^ 2 = m * x ^ 2 * s := by ring
        _ ≤ m * x ^ 2 * σ := mul_le_mul_of_nonneg_left hsσ (by positivity)
    have t2 : m ^ 2 * x ^ 2 * (Cr * u) ≤ m * x ^ 2 * (σ * (Cr * u)) := by
      calc m ^ 2 * x ^ 2 * (Cr * u) = m * x ^ 2 * (m * (Cr * u)) := by ring
        _ ≤ m * x ^ 2 * (σ * (Cr * u)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmσ (by positivity))
              (by positivity)
    have hin : m * s * x ^ 2 + m ^ 2 * x ^ 2 * r ≤
        m * x ^ 2 * σ + m * x ^ 2 * (σ * (Cr * u)) := by
      have : m ^ 2 * x ^ 2 * r ≤ m ^ 2 * x ^ 2 * (Cr * u) :=
        mul_le_mul_of_nonneg_left hrr (by positivity)
      linarith
    calc ε₁₄ = P * (m * s * x ^ 2 + m ^ 2 * x ^ 2 * r) := by
          rw [hε₁₄def, rp32, rp2, hx2]
      _ ≤ P * (m * x ^ 2 * σ + m * x ^ 2 * (σ * (Cr * u))) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = σ * (1 + Cr * u) * Y := by rw [hYdef]; ring
  -- the second-order error terms
  set tl : ℝ := (D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) *
      (eps + eps) + (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) +
      D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (eps + eps) with htldef
  have hx00 : 0 ≤ x := hx0.le
  have htl0 : 0 ≤ tl := by rw [htldef]; positivity
  have e1 : (N : ℝ) ^ τ₁ * (1 / ((N : ℝ) * z.im)) = P * (m * x) := by
    rw [hP, hm, hxdef, hn, one_div, mul_inv]
  have e2 : ∀ q : ℝ, (N : ℝ) ^ τ₁ * ((N : ℝ)⁻¹ * (z.im ^ 2) ⁻¹ * q) = P * (m * x ^ 2 * q) := by
    intro q; rw [hP, hm, hx2, hn]
  have hBE1 : LX_BE1 D N τ₁ z.im r eps ≤ D * (5 / 4) * P * Cr * u * (m * x) * Y + tl := by
    unfold LX_BE1
    rw [e1, e2, ← hxdef]
    have hmain : (D * (5 / 4) * (P * (m * x))) * (P * (m * x ^ 2 * r)) ≤
        D * (5 / 4) * P * Cr * u * (m * x) * Y := by
      calc (D * (5 / 4) * (P * (m * x))) * (P * (m * x ^ 2 * r)) ≤
          (D * (5 / 4) * (P * (m * x))) * (P * (m * x ^ 2 * (Cr * u))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrr (by positivity)) (by positivity)) (by positivity)
        _ = D * (5 / 4) * P * Cr * u * (m * x) * Y := by rw [hYdef]; ring
    have htail : (D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) *
        (eps + eps) ≤ tl := by
      rw [htldef]
      have : 0 ≤ (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) +
          D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (eps + eps) := by positivity
      linarith
    linarith
  have hBE2 : LX_BE2 D N τ₁ z.im r₂₁ eps ≤ D ^ 2 * (5 / 4) * P * Cr * u * (m * x) * Y + tl := by
    unfold LX_BE2
    rw [e1, e2, ← hxdef]
    have hmain : ((D : ℝ) * (P * (m * x))) * ((D * (5 / 4)) * (P * (m * x ^ 2 * r₂₁))) ≤
        D ^ 2 * (5 / 4) * P * Cr * u * (m * x) * Y := by
      calc ((D : ℝ) * (P * (m * x))) * ((D * (5 / 4)) * (P * (m * x ^ 2 * r₂₁))) ≤
          ((D : ℝ) * (P * (m * x))) * ((D * (5 / 4)) * (P * (m * x ^ 2 * (Cr * u)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrr₂ (by positivity)) (by positivity)) (by positivity))
              (by positivity)
        _ = D ^ 2 * (5 / 4) * P * Cr * u * (m * x) * Y := by rw [hYdef]; ring
    have htail : (D * (x + 5 / 4)) * (D * (x * (5 / 4) * x) +
        D * r₂₁ * (D * ((25 / 16) * (5 / 4)))) * (eps + eps) ≤ tl := by
      rw [htldef]
      have : 0 ≤ (D * ((x + 5 / 4) * (5 / 4))) * (D * (x * x) + D * r * (D * (25 / 16))) *
          (eps + eps) := by positivity
      linarith
    linarith
  have hun : u ≤ n := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 (show εg ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hxn : x ≤ c * n := by
    have h1 : n ^ (1 / 3 : ℝ) ≤ n := by
      have := Real.rpow_le_rpow_of_exponent_le hn1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    calc x ≤ c * n ^ (1 / 3 : ℝ) := hx3
      _ ≤ c * n := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hε10 : eps * n ^ 10 = 1 := by
    rw [hepsdef, Real.rpow_neg hn0.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    exact inv_mul_cancel₀ (by positivity)
  have hε9 : eps * n ^ 9 = m := by
    have : (eps * n ^ 9) * n = 1 := by rw [← hε10]; ring
    exact eq_inv_of_mul_eq_one_left this
  have htl_le := LX_tail D n c Cr u x r r₂₁ eps hDr hn1 hc hCr hun hxn hx00 hr0 hr₂0 hrr hrr₂ hu1
    heps0
  have htl : tl * u ^ 2 ≤ Y := by
    set K : ℝ := 6 * (D : ℝ) * (c + 2) * (D * c ^ 2 + 2 * (D : ℝ) ^ 2 * Cr) with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have h1 : tl ≤ (K * (eps + eps)) * n ^ 3 := by rw [htldef]; exact htl_le
    have h2 : tl * u ^ 2 ≤ ((K * (eps + eps)) * n ^ 3) * n ^ 2 :=
      mul_le_mul h1 (pow_le_pow_left₀ hu0 hun 2) (by positivity) (by positivity)
    have h3 : (((K * (eps + eps)) * n ^ 3) * n ^ 2) * c ^ 2 ≤ m := by
      have h4 : 2 * K * c ^ 2 ≤ n ^ 4 := by
        have := htail
        calc 2 * K * c ^ 2 = 12 * (D : ℝ) * (c + 2) * (D * c ^ 2 + 2 * (D : ℝ) ^ 2 * Cr) * c ^ 2 := by
              rw [hK]; ring
          _ ≤ n ^ 4 := this
      calc (((K * (eps + eps)) * n ^ 3) * n ^ 2) * c ^ 2 = (2 * K * c ^ 2) * (eps * n ^ 5) := by ring
        _ ≤ n ^ 4 * (eps * n ^ 5) := by gcongr
        _ = eps * n ^ 9 := by ring
        _ = m := hε9
    have h5 : m ≤ m * x ^ 2 * c ^ 2 := by
      calc m = m * 1 := (mul_one m).symm
        _ ≤ m * (c * x) ^ 2 := mul_le_mul_of_nonneg_left hcx2 hm0.le
        _ = m * x ^ 2 * c ^ 2 := by ring
    have h6 : (tl * u ^ 2) * c ^ 2 ≤ (m * x ^ 2) * c ^ 2 := by
      calc (tl * u ^ 2) * c ^ 2 ≤ (((K * (eps + eps)) * n ^ 3) * n ^ 2) * c ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ m := h3
        _ ≤ m * x ^ 2 * c ^ 2 := h5
    have h7 := le_of_mul_le_mul_right h6 (by positivity)
    calc tl * u ^ 2 ≤ m * x ^ 2 := h7
      _ ≤ P * (m * x ^ 2) := le_mul_of_one_le_left (by positivity) hP1
  have hPY : Y ≤ P * Y := le_mul_of_one_le_left hY0 hP1
  have hc₁ : (0 : ℝ) ≤ c + 1 + c ^ 2 := by positivity
  have herr := LX_num_err D (c + 1 + c ^ 2) c Cr P u σ m x r r₂₁ ε₁₅ ε₁₄ _ _ tl Y hD1 hP1 hu1 hσ0
    hY0 hr0 hr₂0 he15 he14 (by unfold LX_BE1; positivity) (by unfold LX_BE2; positivity) htl0 hCr
    hc₁ (by linarith) (by positivity) hQ1 hQ2 hrr hrr₂ e15 e14 hBE1 hBE2 htl hPY
  have hKerr : LX_Kerr D c Cr = D * Cr * (D * (5 / 4) * (c + 1 + c ^ 2) + (1 + Cr) * (c + 1 + c ^ 2) +
    2 * D ^ 5 * (125 / 64) * Cr * (c + 1 + c ^ 2) + (D ^ 3 + D ^ 4) * (5 / 4) * Cr * c +
    2 * D ^ 2) := rfl
  have hgen : ∀ (ε' : ℝ) (S : ℂ) (Sb RemB Kmain : ℝ),
      LX_Fz (MExt (lam D N A) z₁) (mExt (lam D N A) z₁) ε' →
      LX_Fz (MExt (lam D N A) z₂) (mExt (lam D N A) z₂) ε' → 0 ≤ Sb → ‖S‖ ≤ Sb →
      (∀ a b : Fin D, ‖LX_Main (lam D N A) θ z₁ z₂ a b -
        S * KTheta (lam D N A) θ z₁ z₂ a b‖ ≤ RemB) →
      (Kc * m * (D * r * (Sb * (D * r * (D * (25 / 16))) + RemB))) * u ≤ Kmain * (m * x ^ 2) →
      0 ≤ Kmain → LX_Kerr D c Cr + Kmain ≤ LX_Kfin D c Cr Ce C₁ CΔ Kc Kb →
      ‖(ELmat μ (lam D N A) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) a b‖ ≤
        LX_Kfin D c Cr Ce C₁ CΔ Kc Kb * (P ^ 2 * (n⁻¹ * (z.im ^ 2)⁻¹ * u⁻¹)) := by
    intro ε' S Sb RemB Kmain hF₁ hF₂ hSb hS hmain hnum hKm0 hKsum
    have hkap : 0 ≤ Kc * m := by positivity
    have hcore := LX_pair_core hD1 hN μ hμh θ hθ0 hθ1 A z hz z₁ z₂ h₁ h₂ _ _ ε' (C₁ * ρ) (C₁ * ρ)
      hF₁ hF₂ hd₁ hC₁' hd₂ hC₂' hdet hdet₂ hc3 hc4 hc6 κ (Kc * m) hκ hkap τ₁ eps ε₁₅ ε₁₄ heps0 he15
      he14 (fun B hB => h15 z₁ h₁ B hB) (fun B hB => h15 z₂ h₂ B hB) (h14 z₁ z₂ h₁ h₂)
      (hAv z₁ h₁) (hAv z₂ h₂) (hTwo z₁ z₂ h₁ h₂) (hBB z₂ z₁ h₂ h₁) S Sb RemB hSb hS hmain a b
    have h1 : ‖(ELmat μ (lam D N A) z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) a b‖ * u ≤
        LX_Kerr D c Cr * (P * Y) + Kmain * (m * x ^ 2) := by
      calc _ ≤ (D * r * LX_ErrBd D r r₂₁ ε₁₅ ε₁₄ (LX_BE1 D N τ₁ z.im r eps) (LX_BE2 D N τ₁ z.im r₂₁ eps) +
          Kc * m * (D * r * (Sb * (D * r * (D * (25 / 16))) + RemB))) * u :=
            mul_le_mul_of_nonneg_right hcore hu0
        _ = D * r * LX_ErrBd D r r₂₁ ε₁₅ ε₁₄ (LX_BE1 D N τ₁ z.im r eps) (LX_BE2 D N τ₁ z.im r₂₁ eps) * u +
          (Kc * m * (D * r * (Sb * (D * r * (D * (25 / 16))) + RemB))) * u := by ring
        _ ≤ LX_Kerr D c Cr * (P * Y) + Kmain * (m * x ^ 2) := by
            rw [hKerr]; exact add_le_add herr hnum
    have h2 : LX_Kerr D c Cr * (P * Y) + Kmain * (m * x ^ 2) ≤
        LX_Kfin D c Cr Ce C₁ CΔ Kc Kb * (P ^ 2 * (m * x ^ 2)) := by
      have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP1
      have hmx2 : 0 ≤ m * x ^ 2 := by positivity
      calc LX_Kerr D c Cr * (P * Y) + Kmain * (m * x ^ 2) = LX_Kerr D c Cr * (P ^ 2 * (m * x ^ 2)) +
          Kmain * (m * x ^ 2) := by rw [hYdef]; ring
        _ ≤ LX_Kerr D c Cr * (P ^ 2 * (m * x ^ 2)) + Kmain * (P ^ 2 * (m * x ^ 2)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left hmx2 hP2) hKm0)
        _ = (LX_Kerr D c Cr + Kmain) * (P ^ 2 * (m * x ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKsum (by positivity)
    have hu0' : 0 < u := by linarith
    have h3 := h1.trans h2
    rw [← le_div_iff₀ hu0'] at h3
    calc _ ≤ LX_Kfin D c Cr Ce C₁ CΔ Kc Kb * (P ^ 2 * (m * x ^ 2)) / u := h3
      _ = _ := by rw [hx2, div_eq_mul_inv, hm]; ring
  have hΛ := lam_isHermitian D N A
  have hcase : z₂ = star z₁ ∨ z₂ = z₁ := by
    rcases h₁ with e1 | e1 <;> rcases h₂ with e2 | e2
    · right; rw [e1, e2]
    · left; rw [e1, e2]
    · left; rw [e1, e2, star_star]
    · right; rw [e1, e2]
  have hFeq : (z₂ = z₁) → True := fun _ => trivial
  have hyz : ((mExt (lam D N A) z).im) ^ 3 ≠ 0 := by positivity
  rcases hcase with hc12 | hc12
  · -- conjugate pair
    have hF₁ := hFz z₁ h₁
    have hF₂ := hFz z₂ h₂
    have hcb := (mExt_conj (lam D N A) hΛ z hz.ne')
    have hSb0 : 0 ≤ Kb * (z.im * ((mExt (lam D N A) z).im ^ 3)⁻¹ +
        (N : ℝ) ^ (-(δA / 2)) * ((mExt (lam D N A) z).im ^ 2)⁻¹) := by positivity
    have hnum : (Kc * m * (D * r * (Kb * (z.im * ((mExt (lam D N A) z).im ^ 3)⁻¹ +
        (N : ℝ) ^ (-(δA / 2)) * ((mExt (lam D N A) z).im ^ 2)⁻¹) * (D * r * (D * (25 / 16))) +
        LX_RemB D r r₂₁ (CΔ * w) (C₁ * ρ) (C₁ * ρ)))) * u ≤ LX_Kconj D c Cr C₁ CΔ Kc Kb * (m * x ^ 2) := by
      have := LX_num_conj D c Kc Kb C₁ Cr CΔ u ((mExt (lam D N A) z).im)⁻¹ x m w
        ((N : ℝ) ^ (-(δA / 2))) ρ (CΔ * w) r r₂₁ (C₁ * ρ) (C₁ * ρ) z.im hD1 hc hKc hKb hC₁ hCr hCΔ
        hu1 hz1 hx0 hm0.le hw0 hw₂0 hρ1 (by positivity) hr0 hr₂0 (by positivity) (by positivity) hz
        hηx R6 R3 R7 R5 hρu hρz hrr hrr₂ le_rfl le_rfl le_rfl
      simp only [inv_pow] at this
      exact (le_of_eq (by ring)).trans this
    have hmain := fun a b => LX_conj_Main hD1 hN (lam D N A) θ hθ0 hθ1 z₁ z₂ _ _ (CΔ * w)
      (C₁ * ρ) (C₁ * ρ) hF₁ hF₂ hd₁ hC₁' hd₂ hC₂' hc3 hc4 hc6 a b
    have hbr' := hbr
    refine hgen (CΔ * w) _ _ _ _ hF₁ hF₂ hSb0 ?_ hmain hnum
      (LX_Kconj_nonneg D c Cr C₁ CΔ Kc Kb (by linarith) hCr hC₁ hCΔ hKc hKb)
      (by unfold LX_Kfin; have := LX_Keq_nonneg D c Ce C₁ Kc (by linarith) hCe hC₁ hKc; linarith)
    rcases h₁ with e1 | e1
    · have e2 : z₂ = star z := by rw [hc12, e1]
      rw [e1, e2, hcb.1, hcb.2, LX_S_conj]
      exact hbr'
    · have e2 : z₂ = z := by rw [hc12, e1, star_star]
      rw [e1, e2, hcb.1, hcb.2, LX_S_swap, norm_star, LX_S_conj]
      exact hbr'
  · -- equal pair
    subst hc12
    have hF := hFz3 z₂ h₂
    have hreq' : r ≤ Ce * ρ := hreq rfl
    have hr₂eq : r₂₁ ≤ Ce * ρ := hreq rfl
    have hSb0 : 0 ≤ 4 + C₁ * ρ + C₁ * ρ := by positivity
    have hnum := LX_num_eq D c Kc C₁ Ce u ((mExt (lam D N A) z).im)⁻¹ x m ρ r r₂₁ (C₁ * ρ) (C₁ * ρ)
      hD1 hc hKc hC₁ hCe hu1 hz1 hx0 hm0.le hρ1 hr0 hr₂0 (by positivity) (by positivity) R6 hρu
      hρz hreq' hr₂eq le_rfl le_rfl
    have hmain := fun a b => LX_conj_Main hD1 hN (lam D N A) θ hθ0 hθ1 z₂ z₂ _ _ 3
      (C₁ * ρ) (C₁ * ρ) hF hF hd₁ hC₁' hd₂ hC₂' hc3 hc4 hc6 a b
    refine hgen 3 _ _ _ _ hF hF hSb0 ?_ hmain hnum
      (LX_Keq_nonneg D c Ce C₁ Kc (by linarith) hCe hC₁ hKc)
      (by unfold LX_Kfin LX_Keq; have := LX_Kconj_nonneg D c Cr C₁ CΔ Kc Kb (by linarith) hCr hC₁
            hCΔ hKc hKb; linarith)
    exact LX_S_crude _ _ _ _ _ _ hF.hm hF.hm hd₁ hd₂ hC₁' hC₂'

end LX_mainN2

section LX_real24

private theorem LX_real24 (n c x : ℝ) (hn : 1 ≤ n) (hc : 1 ≤ c) (hx0 : 0 ≤ x)
    (hx : x ≤ c * n ^ (1 / 3 : ℝ)) :
    n ^ (-(1 / 2 : ℝ)) * x ≤ c ∧ n⁻¹ * x ^ 2 ≤ c ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hnm : ∀ e : ℝ, e ≤ 0 → n ^ e ≤ 1 := fun e he => Real.rpow_le_one_of_one_le_of_nonpos hn he
  constructor
  · calc n ^ (-(1 / 2 : ℝ)) * x ≤ n ^ (-(1 / 2 : ℝ)) * (c * n ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hn0.le _)
      _ = c * n ^ (-(1 / 2 : ℝ) + 1 / 3) := by rw [Real.rpow_add hn0]; ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left (hnm _ (by norm_num)) (by linarith)
      _ = c := mul_one c
  · have h1 : x ^ 2 ≤ (c * n ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    calc n⁻¹ * x ^ 2 ≤ n⁻¹ * (c * n ^ (1 / 3 : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn0.le)
      _ = c ^ 2 * n ^ (-1 + 2 / 3 : ℝ) := by
          rw [mul_pow, LX_rp n (1 / 3) 2 hn0, Real.rpow_add hn0, Real.rpow_neg_one]
          push_cast; ring_nf
      _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left (hnm _ (by norm_num)) (by positivity)
      _ = c ^ 2 := mul_one _

end LX_real24

set_option maxHeartbeats 8000000 in
private theorem LX_final (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
        (∀ a : Fin D, ‖∫ h, ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *
            Ea D N a) ∂(ouMatLaw D N L t)‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * ((mExt (lam D N A) z).im)⁻¹)) ∧
        ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
          hsNorm (ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ -
              KTheta (lam D N A) (Real.exp (-t)) z₁ z₂) ≤
            (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * (N : ℝ) ^ (-min τe εg)) := by
  intro τ' hτ'
  have hD1 : 1 ≤ D := by omega
  have hc0 : 0 < c := by linarith
  have hτ₁0 : 0 < τ' / 4 := by positivity
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨N₁, h15⟩ := lem_fourthcumu2_theta' D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C
    (τ' / 4) hτ₁0
  obtain ⟨N₂, h14⟩ := lem_fourthcumu1_theta D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C
    (τ' / 4) hτ₁0
  obtain ⟨N₃, hcirc⟩ := KTheta_circ D hD δA τ hδA hτ
  obtain ⟨N₄, hav⟩ := aver_local D hD1 δA τ hδA hτ C' (τ' / 4) hτ₁0 10 (by norm_num)
  obtain ⟨N₅, htwo⟩ := lemma_G_large_two D hD δA τ εg c hδA hτ hεg hεg₂ hc C' (τ' / 4) hτ₁0 10
    (by norm_num)
  obtain ⟨N₆, hbb⟩ := lemma_G_large_BB D hD δA τ εg c hδA hτ hεg hεg₂ hc C' (τ' / 4) hτ₁0 10
    (by norm_num)
  obtain ⟨Cm, hCm, hMf⟩ := LX_Mfacts τ hτ
  obtain ⟨C₁, hC₁, N₇, hsame⟩ := one_minus_Mhat_same D hD δA εg c⁻¹ τ hδA hεg hεg₂
    (inv_pos.mpr hc0) (inv_le_one_of_one_le₀ hc) hτ
  obtain ⟨Cc, hCc, N₈, hconj⟩ := one_minus_Mhat_conj D hD δA τ hδA hτ
  obtain ⟨N₉, hPinv⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  obtain ⟨Kb, hKb, N₁₀, hbr⟩ := bracket_cancel D hD δA τ εg c hδA hτ hεg hεg₂ hc
  obtain ⟨Kc, hKc⟩ := ccum_entry_le C 2 2
  have hKc₀ : ∀ L : EntryLaws C, ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤ max Kc 0 := fun L =>
    ((hKc L).1).trans (le_max_left _ _)
  set Kc₀ : ℝ := max Kc 0 with hKc₀def
  have hKc₀0 : 0 ≤ Kc₀ := le_max_right _ _
  have hC₁0 : 0 ≤ C₁ := hC₁.le
  have hCr0 : 0 ≤ 2 * C₁ + 4 * c := by positivity
  have hCΔ0 : 0 ≤ 2 * Cm := by positivity
  have hCe0 : 0 ≤ 2 * C₁ := by positivity
  have hCeCr : 2 * C₁ ≤ 2 * C₁ + 4 * c := by linarith
  obtain ⟨N₁₁, hN₁₁⟩ := LX_pow_ge 20 δA hδA
  obtain ⟨N₁₂, hN₁₂⟩ := LX_pow_ge (12 * (D : ℝ) * (c + 2) * (D * c ^ 2 +
    2 * (D : ℝ) ^ 2 * (2 * C₁ + 4 * c)) * c ^ 2) 4 (by norm_num)
  obtain ⟨N₁₃, hN₁₃⟩ := LX_pow_ge ((D : ℝ) * LX_Kfin D c (2 * C₁ + 4 * c) (2 * C₁) C₁ (2 * Cm)
    Kc₀ Kb) (τ' / 2) (by positivity)
  obtain ⟨N₁₄, hN₁₄⟩ := LX_pow_ge (Kc₀ * (4 + 8 * C₁) + (c + c ^ 2 + 1)) (3 * τ' / 4)
    (by positivity)
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + N₉ + N₁₀ + N₁₁ + N₁₂ + N₁₃ + N₁₄ + 1,
    fun N hN L t ht0 ht1 A hA z hzs hzim hη hq1 hq2 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  haveI : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨hzn, hzim'⟩ := hzs
  have hzs : z ∈ specDom τ N := ⟨hzn, hzim'⟩
  have hθ0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hθ1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hLL : LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t) := hC' N L t ht0
  haveI := hLL.prob
  have hμh := hLL.herm
  have hopΛ : opNorm (lam D N A) ≤ 2 * (N : ℝ) ^ (-δA) := (opNorm_lam_le D N A).trans (by linarith)
  have hwl : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    have h20 := hN₁₁ N (by omega)
    have hpos : 0 < (N : ℝ) ^ δA := Real.rpow_pos_of_pos hn0 _
    rw [Real.rpow_neg hn0.le, inv_le_comm₀ hpos (by norm_num)]
    norm_num
    exact h20
  have hΛ1 : opNorm (lam D N A) ≤ 1 / 10 := by linarith
  have hmx : mExt (lam D N A) z = mSol (lam D N A) z := (LX_MExt_pos (lam D N A) z hzim).1
  have hy0 : 0 < (mExt (lam D N A) z).im := by
    rw [hmx]; exact (mSol_spec (lam D N A) hΛ z hzim).1
  have hy1 : (mExt (lam D N A) z).im ≤ 1 := by
    rw [hmx]
    have h1 := (mSol_apriori (lam D N A) hΛ hΛ1 z hzim).2.1
    have h2 := Complex.abs_im_le_norm (mSol (lam D N A) z)
    linarith [le_abs_self (mSol (lam D N A) z).im]
  have hq1' := hq1
  rw [hmx] at hq1'
  have hq2' : z.im / (mSol (lam D N A) z).im ≤ c⁻¹⁻¹ * (N : ℝ) ^ (-εg) := by
    rw [inv_inv, ← hmx]; exact hq2
  have hη' : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (by positivity)).trans hη
  have hspec : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ξ ∈ specDom τ N := by
    rintro ξ (rfl | rfl)
    · exact hzs
    · refine ⟨by simpa using hzn, ?_⟩
      simpa using hzim'
  have h15N := h15 N (by omega) L t ht0 ht1 A hA z hzs hzim hη hq1 hq2
  have h14N := h14 N (by omega) L t ht0 ht1 A hA z hzs hzim hη hq1 hq2
  have hcircN := hcirc N (by omega) A hA z hzn hzim
  have havN := hav N (by omega) (Real.exp (-t)) hθ0 hθ1 (ouMatLaw D N L t) hLL A hA
  have htwoN := htwo N (by omega) (Real.exp (-t)) hθ0 hθ1 (ouMatLaw D N L t) hLL A hA z hzs hzim
    hη' hq1 hq2
  have hbbN := hbb N (by omega) (Real.exp (-t)) hθ0 hθ1 (ouMatLaw D N L t) hLL A hA z hzs hzim
    hη' hq1 hq2
  have hsameN := hsame N (by omega) A hA z hzn hzim hq1' hq2'
  have hconjN := hconj N (by omega) A hA z hzn hzim
  have hbrN := hbr N (by omega) A hA z hzs hzim hq1 hq2
  have hMfN := hMf D N hD1 hN1 A hΛ1 z hzn hzim
  -- the scalar κ
  set κ : ℂ := ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 with hκdef
  have hκ : ‖κ‖ ≤ Kc₀ * (N : ℝ)⁻¹ := by
    rw [hκdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hE : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hE0 : 0 ≤ Real.exp (-(2 * t)) := (Real.exp_pos _).le
    rw [abs_of_nonneg (div_nonneg hE0 hn0.le)]
    calc Real.exp (-(2 * t)) / N * ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤ (1 / (N : ℝ)) * Kc₀ :=
          mul_le_mul (div_le_div_of_nonneg_right hE hn0.le) (hKc₀ L) (norm_nonneg _)
            (by positivity)
      _ = Kc₀ * (N : ℝ)⁻¹ := by ring
  have hFz : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) →
      LX_Fz (MExt (lam D N A) ξ) (mExt (lam D N A) ξ) (2 * Cm * (N : ℝ) ^ (-δA)) := by
    intro ξ hξ
    obtain ⟨h1, h2, h3⟩ := hMfN ξ hξ
    refine ⟨h1, h2, h3.trans ?_, by positivity⟩
    calc Cm * opNorm (lam D N A) ≤ Cm * (2 * (N : ℝ) ^ (-δA)) :=
          mul_le_mul_of_nonneg_left hopΛ hCm.le
      _ = 2 * Cm * (N : ℝ) ^ (-δA) := by ring
  have hFz3 : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) →
      LX_Fz (MExt (lam D N A) ξ) (mExt (lam D N A) ξ) 3 := by
    intro ξ hξ
    obtain ⟨h1, h2, -⟩ := hMfN ξ hξ
    refine ⟨h1, h2, ?_, by norm_num⟩
    have := LX_op_scal (ι := Idx D N) (mExt (lam D N A) ξ)
    have h4 := LX_op_sub_le (MExt (lam D N A) ξ) (mExt (lam D N A) ξ • 1)
    linarith
  have hden : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) →
      1 - ntr (MExt (lam D N A) ξ * MExt (lam D N A) ξ) ≠ 0 ∧
      ‖1 - ntr (MExt (lam D N A) ξ * MExt (lam D N A) ξ)‖⁻¹ ≤
        C₁ * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) := by
    intro ξ hξ
    refine ⟨(hsameN ξ hξ).2.1, ?_⟩
    have := (hsameN ξ hξ).2.2.2
    rw [hmx]; exact this
  have hrEq : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) →
      opNorm (1 - Mhat (lam D N A) ξ ξ * PTheta D (Real.exp (-t)))⁻¹ ≤
        (2 * C₁) * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) := by
    intro ξ hξ
    obtain ⟨-, hb⟩ := hPinv N (by omega) A hA z hzn hzim ξ ξ hξ hξ (Real.exp (-t)) hθ0 hθ1
    have h2 := (hsameN ξ hξ).2.2.1
    rw [← hmx] at h2
    calc _ ≤ 2 * opNorm (1 - Mhat (lam D N A) ξ ξ)⁻¹ := hb
      _ ≤ 2 * (C₁ * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)) := by gcongr
      _ = _ := by ring
  have hyη : (mSol (lam D N A) z).im / z.im ≤ c * (N : ℝ) ^ εg := by
    have hpos : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    have := inv_anti₀ hpos hq1'
    rw [mul_inv, inv_inv, Real.rpow_neg hn0.le, inv_inv, inv_div] at this
    exact this
  have hu1' : 1 ≤ (N : ℝ) ^ εg := Real.one_le_rpow hn1 hεg.le
  have hcj : ∀ (e : opNorm (1 - Mhat (lam D N A) z (star z))⁻¹ = ((mSol (lam D N A) z).im + z.im) / z.im),
      ((mSol (lam D N A) z).im + z.im) / z.im ≤ 1 + c * (N : ℝ) ^ εg := by
    intro _
    rw [add_div, div_self hzim.ne']
    linarith
  have hconjb : ∀ r0 : ℝ, r0 = ((mSol (lam D N A) z).im + z.im) / z.im → 2 * r0 ≤
      (2 * C₁ + 4 * c) * (N : ℝ) ^ εg := by
    intro r0 hr0
    rw [hr0, add_div, div_self hzim.ne']
    have h1 : 1 ≤ c * (N : ℝ) ^ εg := by nlinarith
    nlinarith [mul_nonneg hC₁0 (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ εg)]
  have hcj1 : opNorm (1 - Mhat (lam D N A) z (star z) * PTheta D (Real.exp (-t)))⁻¹ ≤
      (2 * C₁ + 4 * c) * (N : ℝ) ^ εg := by
    obtain ⟨-, hb⟩ := hPinv N (by omega) A hA z hzn hzim z (star z) (Or.inl rfl) (Or.inr rfl)
      (Real.exp (-t)) hθ0 hθ1
    exact (hb.trans (by rw [(hconjN).1]; exact hconjb _ rfl)).trans le_rfl
  have hcj2 : opNorm (1 - Mhat (lam D N A) (star z) z * PTheta D (Real.exp (-t)))⁻¹ ≤
      (2 * C₁ + 4 * c) * (N : ℝ) ^ εg := by
    obtain ⟨-, hb⟩ := hPinv N (by omega) A hA z hzn hzim (star z) z (Or.inr rfl) (Or.inl rfl)
      (Real.exp (-t)) hθ0 hθ1
    exact (hb.trans (by rw [(hconjN).2.1]; exact hconjb _ rfl)).trans le_rfl
  have hρu : min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) ≤ (N : ℝ) ^ εg := min_le_right _ _
  have hRb : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t))).det ≠ 0 ∧
      opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹ ≤
        (2 * C₁ + 4 * c) * (N : ℝ) ^ εg ∧
      (z₂ = z₁ → opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹ ≤
        (2 * C₁) * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)) := by
    intro z₁ z₂ h₁ h₂
    obtain ⟨hdet, -⟩ := hPinv N (by omega) A hA z hzn hzim z₁ z₂ h₁ h₂ (Real.exp (-t)) hθ0 hθ1
    have hcase : z₂ = star z₁ ∨ z₂ = z₁ := by
      rcases h₁ with e1 | e1 <;> rcases h₂ with e2 | e2
      · right; rw [e1, e2]
      · left; rw [e1, e2]
      · left; rw [e1, e2, star_star]
      · right; rw [e1, e2]
    refine ⟨hdet, ?_, fun he => by rw [he]; exact hrEq z₁ h₁⟩
    rcases hcase with he | he
    · rcases h₁ with e1 | e1
      · rw [he, e1]; exact hcj1
      · rw [he, e1, star_star]; exact hcj2
    · rw [he]
      refine (hrEq z₁ h₁).trans ?_
      calc 2 * C₁ * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) ≤ (2 * C₁) * (N : ℝ) ^ εg :=
            mul_le_mul_of_nonneg_left hρu (by positivity)
        _ ≤ (2 * C₁ + 4 * c) * (N : ℝ) ^ εg :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hcirc' : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (∀ a b x : Fin D, KThetaB (lam D N A) (Real.exp (-t)) z₂ z₁ (Ea D N a) b x =
        if x = a then KTheta (lam D N A) (Real.exp (-t)) z₁ z₂ a b else 0) ∧
      (∀ b x : Fin D, KThetaB (lam D N A) (Real.exp (-t)) z₂ z₁ 1 b x =
        KTheta (lam D N A) (Real.exp (-t)) z₁ z₂ x b) ∧
      opNorm (PTheta D (Real.exp (-t)) * KTheta (lam D N A) (Real.exp (-t)) z₁ z₂ -
        KTheta (lam D N A) (Real.exp (-t)) z₁ z₂) ≤ 1 := by
    intro z₁ z₂ h₁ h₂
    obtain ⟨-, -, a3, a4, -, a6⟩ := hcircN z₁ z₂ h₁ h₂ (Real.exp (-t)) hθ0 hθ1
    exact ⟨a3, a4, a6⟩
  have h15' : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B)
          ∂(ouMatLaw D N L t)) - κ * lead15 (lam D N A) ξ B‖ ≤ (N : ℝ) ^ (τ' / 4) *
        (min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ +
          (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ)⁻¹ * opNorm A)) :=
    fun ξ hξ B hB => (h15N ξ hξ B hB).2
  have h14' : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
      ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) (Real.exp (-t)) h z₁ z₂ a (Ea D N b)
          ∂(ouMatLaw D N L t)) - ((D : ℂ) * κ) * lead14 (lam D N A) (Real.exp (-t)) z₁ z₂ a b‖ ≤
        (N : ℝ) ^ (τ' / 4) * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) *
          (z.im ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹) := by
    intro z₁ z₂ h₁ h₂ a b
    have := (h14N z₁ z₂ h₁ h₂ a b).2.2
    have e : ((D * Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 =
        (D : ℂ) * κ := by rw [hκdef]; push_cast; ring
    rw [e] at this
    exact this
  have hAv' : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      (ouMatLaw D N L t) {h | (N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * |ξ.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) :=
    fun ξ hξ B hB => by
      refine le_trans (measure_mono ?_) (havN B hB)
      intro h hh
      exact ⟨ξ, hspec ξ hξ, hh⟩
  have hTwo' : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (ouMatLaw D N L t) {h | (N : ℝ) ^ (τ' / 4) * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹) <
        hsNorm (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) (Real.exp (-t)) z₁ z₂)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) :=
    fun z₁ z₂ h₁ h₂ => (htwoN z₁ z₂ h₁ h₂).2
  have hBB' : ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 → ∀ a' : Fin D,
      (ouMatLaw D N L t) {h | (N : ℝ) ^ (τ' / 4) * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹) <
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a' * res (Matrix.of h + lam D N A) z₂ *
          B) - ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹ a' x *
          ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * B)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) :=
    fun z₁ z₂ h₁ h₂ B hB a' => (hbbN z₁ z₂ h₁ h₂ B hB a').2
  have htail : 12 * (D : ℝ) * (c + 2) * (D * c ^ 2 + 2 * (D : ℝ) ^ 2 * (2 * C₁ + 4 * c)) * c ^ 2 ≤
      (N : ℝ) ^ 4 := by
    have := hN₁₂ N (by omega)
    rwa [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hτ₁1 : 1 ≤ (N : ℝ) ^ (τ' / 4) := Real.one_le_rpow hn1 hτ₁0.le
  have hmainN := LX_main_N hD hN1 δA τe εg c (2 * C₁ + 4 * c) (2 * C₁) C₁ (2 * Cm) Kc₀ Kb (τ' / 4)
    hδA hτe hεg hεg₁ hεg₂ hc hCr0 hCe0 hC₁0 hCΔ0 hKc₀0 hKb.le hCeCr (by linarith) hτ₁0
    (ouMatLaw D N L t) hμh (Real.exp (-t)) hθ0 hθ1 κ hκ A hA z hzim hη hq2 hy0 hy1 hFz hFz3 hden
    hRb hcirc' hbrN.2.2 h15' h14' hAv' hTwo' hBB' htail hτ₁1
  -- scales for the conclusion
  have hP2 : ((N : ℝ) ^ (τ' / 4)) ^ 2 = (N : ℝ) ^ (τ' / 2) := by
    rw [LX_rp _ _ 2 hn0]; congr 1; push_cast; ring
  have hP4 : ((N : ℝ) ^ (τ' / 4)) ^ 4 = (N : ℝ) ^ τ' := by
    rw [LX_rp _ _ 4 hn0]; congr 1; push_cast; ring
  have hP3 : ((N : ℝ) ^ (τ' / 4)) ^ 3 = (N : ℝ) ^ (3 * τ' / 4) := by
    rw [LX_rp _ _ 3 hn0]; congr 1; push_cast; ring
  have hx00 : 0 ≤ (z.im)⁻¹ := (inv_pos.mpr hzim).le
  have hx3 : (z.im)⁻¹ ≤ c * (N : ℝ) ^ (1 / 3 : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, -, hx3, -⟩ := LX_real (N : ℝ) εg δA τe c z.im
      (mExt (lam D N A) z).im hn1 hεg hεg₁ hεg₂ hδA hτe hc hzim hy0 hy1 hη hq2
    exact hx3
  refine ⟨?_, ?_⟩
  · -- (3.24)
    intro a
    have hB : opNorm (Ea D N a) ≤ 1 := LX_op_Ea a
    have hI := h15' z (Or.inl rfl) (Ea D N a) hB
    obtain ⟨hd1, hd2⟩ := hden z (Or.inl rfl)
    have hl := LX_lead15_crude (lam D N A) z (Ea D N a) 1
      (C₁ * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)) (hMfN z (Or.inl rfl)).1 hB hd1 hd2
    set ρ := min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) with hρdef
    set P := (N : ℝ) ^ (τ' / 4) with hPdef
    have hρ1 : 1 ≤ ρ := le_min (by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hz1, -⟩ := LX_real (N : ℝ) εg δA τe c z.im
        (mExt (lam D N A) z).im hn1 hεg hεg₁ hεg₂ hδA hτe hc hzim hy0 hy1 hη hq2
      exact hz1) hu1'
    have hρz : ρ ≤ ((mExt (lam D N A) z).im)⁻¹ := min_le_left _ _
    have hρ0 : 0 ≤ ρ := by linarith
    obtain ⟨hr1, hr2⟩ := LX_real24 (N : ℝ) c (z.im)⁻¹ hn1 hc hx00 hx3
    have hs0 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
    have rp32 : (N : ℝ) ^ (-(3 / 2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(3 / 2 : ℝ)) = -1 + -(1 / 2) by norm_num, Real.rpow_add hn0, Real.rpow_neg_one]
    have rp2 : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ)⁻¹) ^ 2 := by
      rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        inv_pow]
    have hm0 : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hn0
    have hw1 : opNorm A ≤ 1 := hA.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
    have hP0 : 0 ≤ P := by positivity
    -- ε₁₅ ≤ P ρ m (c + c² + 1)
    have hε : (N : ℝ) ^ (τ' / 4) * (ρ * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ +
        (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ)⁻¹ * opNorm A)) ≤
        P * (ρ * ((N : ℝ)⁻¹ * (c + c ^ 2 + 1))) := by
      rw [rp32, rp2, ← inv_pow]
      have e1 : (N : ℝ)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (z.im)⁻¹ ≤ (N : ℝ)⁻¹ * c := by
        calc (N : ℝ)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (z.im)⁻¹ =
            (N : ℝ)⁻¹ * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (z.im)⁻¹) := by ring
          _ ≤ (N : ℝ)⁻¹ * c := mul_le_mul_of_nonneg_left hr1 hm0.le
      have e2 : ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 2 ≤ (N : ℝ)⁻¹ * c ^ 2 := by
        calc ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 2 = (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ((z.im)⁻¹) ^ 2) := by ring
          _ ≤ (N : ℝ)⁻¹ * c ^ 2 := mul_le_mul_of_nonneg_left hr2 hm0.le
      have e3 : (N : ℝ)⁻¹ * opNorm A ≤ (N : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hw1 hm0.le
      have : (N : ℝ) ^ (-(1 / 2 : ℝ)) * 0 = 0 := by ring
      have hsum : (N : ℝ)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (z.im)⁻¹ + ((N : ℝ)⁻¹) ^ 2 * ((z.im)⁻¹) ^ 2 +
          (N : ℝ)⁻¹ * opNorm A ≤ (N : ℝ)⁻¹ * (c + c ^ 2 + 1) := by linarith
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hρ0) hP0
    have hκl : ‖κ‖ * ‖lead15 (lam D N A) z (Ea D N a)‖ ≤
        Kc₀ * (N : ℝ)⁻¹ * (2 * (2 * 1 + 2 * (2 * 1) * (C₁ * ρ))) :=
      mul_le_mul hκ hl (norm_nonneg _) (by positivity)
    have hI2 : ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * Ea D N a)
          ∂(ouMatLaw D N L t))‖ ≤ ‖κ * lead15 (lam D N A) z (Ea D N a)‖ +
        (N : ℝ) ^ (τ' / 4) * (ρ * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ +
          (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ)⁻¹ * opNorm A)) := by
      have := norm_add_le ((∫ h, ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *
        Ea D N a) ∂(ouMatLaw D N L t)) - κ * lead15 (lam D N A) z (Ea D N a))
        (κ * lead15 (lam D N A) z (Ea D N a))
      rw [sub_add_cancel] at this
      linarith
    rw [norm_mul] at hI2
    have hK24 : Kc₀ * (4 + 8 * C₁) + (c + c ^ 2 + 1) ≤ P ^ 3 := by rw [hP3]; exact hN₁₄ N (by omega)
    have hρm : ρ ≤ ((mExt (lam D N A) z).im)⁻¹ := hρz
    have hmρ : 0 ≤ (N : ℝ)⁻¹ := hm0.le
    calc _ ≤ _ := hI2
      _ ≤ Kc₀ * (N : ℝ)⁻¹ * (2 * (2 * 1 + 2 * (2 * 1) * (C₁ * ρ))) + P * (ρ * ((N : ℝ)⁻¹ * (c + c ^ 2 + 1))) :=
          add_le_add hκl hε
      _ ≤ (Kc₀ * (4 + 8 * C₁) + (c + c ^ 2 + 1)) * P * (ρ * (N : ℝ)⁻¹) := by
          have hP1 : 1 ≤ P := hτ₁1
          have h0 : 0 ≤ Kc₀ * (4 + 8 * C₁) * (ρ * (N : ℝ)⁻¹) := by positivity
          have h1 : Kc₀ * (N : ℝ)⁻¹ * (2 * (2 * 1 + 2 * (2 * 1) * (C₁ * ρ))) ≤
              Kc₀ * (4 + 8 * C₁) * P * (ρ * (N : ℝ)⁻¹) := by
            have h4 : 2 * (2 * 1 + 2 * (2 * 1) * (C₁ * ρ)) ≤ (4 + 8 * C₁) * ρ := by linarith
            calc Kc₀ * (N : ℝ)⁻¹ * (2 * (2 * 1 + 2 * (2 * 1) * (C₁ * ρ))) ≤
                Kc₀ * (N : ℝ)⁻¹ * ((4 + 8 * C₁) * ρ) :=
                  mul_le_mul_of_nonneg_left h4 (by positivity)
              _ = Kc₀ * (4 + 8 * C₁) * (ρ * (N : ℝ)⁻¹) := by ring
              _ = (Kc₀ * (4 + 8 * C₁) * (ρ * (N : ℝ)⁻¹)) * 1 := (mul_one _).symm
              _ ≤ (Kc₀ * (4 + 8 * C₁) * (ρ * (N : ℝ)⁻¹)) * P := mul_le_mul_of_nonneg_left hP1 h0
              _ = Kc₀ * (4 + 8 * C₁) * P * (ρ * (N : ℝ)⁻¹) := by ring
          have h2 : P * (ρ * ((N : ℝ)⁻¹ * (c + c ^ 2 + 1))) =
              (c + c ^ 2 + 1) * P * (ρ * (N : ℝ)⁻¹) := by ring
          calc _ ≤ Kc₀ * (4 + 8 * C₁) * P * (ρ * (N : ℝ)⁻¹) +
                (c + c ^ 2 + 1) * P * (ρ * (N : ℝ)⁻¹) := by rw [← h2]; exact add_le_add h1 le_rfl
            _ = _ := by ring
      _ ≤ P ^ 3 * P * (((mExt (lam D N A) z).im)⁻¹ * (N : ℝ)⁻¹) := by
          have : 0 ≤ P * (ρ * (N : ℝ)⁻¹) := by positivity
          calc (Kc₀ * (4 + 8 * C₁) + (c + c ^ 2 + 1)) * P * (ρ * (N : ℝ)⁻¹) =
              (Kc₀ * (4 + 8 * C₁) + (c + c ^ 2 + 1)) * (P * (ρ * (N : ℝ)⁻¹)) := by ring
            _ ≤ P ^ 3 * (P * (((mExt (lam D N A) z).im)⁻¹ * (N : ℝ)⁻¹)) :=
                mul_le_mul hK24 (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρm hmρ) hP0)
                  this (by positivity)
            _ = _ := by ring
      _ = (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * ((mExt (lam D N A) z).im)⁻¹) := by
          rw [← hP4]; ring
  · -- (3.25)
    intro z₁ z₂ h₁ h₂
    have hent := hmainN z₁ z₂ h₁ h₂
    set T₀ : ℝ := (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * ((N : ℝ) ^ εg)⁻¹ with hT₀
    have hKfin0 : 0 ≤ LX_Kfin D c (2 * C₁ + 4 * c) (2 * C₁) C₁ (2 * Cm) Kc₀ Kb := by
      unfold LX_Kfin
      have := LX_Kerr_nonneg D c (2 * C₁ + 4 * c) (by linarith) hCr0
      have := LX_Kconj_nonneg D c (2 * C₁ + 4 * c) C₁ (2 * Cm) Kc₀ Kb (by linarith) hCr0 hC₁0 hCΔ0
        hKc₀0 hKb.le
      have := LX_Keq_nonneg D c (2 * C₁) C₁ Kc₀ (by linarith) hCe0 hC₁0 hKc₀0
      linarith
    have hhs := LX_hs_le (ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ -
      KTheta (lam D N A) (Real.exp (-t)) z₁ z₂) _ (by positivity)
      (fun i j => hent i j)
    rw [Fintype.card_fin] at hhs
    have hP2' : (D : ℝ) * LX_Kfin D c (2 * C₁ + 4 * c) (2 * C₁) C₁ (2 * Cm) Kc₀ Kb ≤
        ((N : ℝ) ^ (τ' / 4)) ^ 2 := by rw [hP2]; exact hN₁₃ N (by omega)
    have hT₀pos : 0 ≤ T₀ := by rw [hT₀]; positivity
    have hT : T₀ ≤ (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * (N : ℝ) ^ (-min τe εg) := by
      rw [hT₀]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Real.rpow_neg hn0.le]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [min_le_right τe εg])
    calc _ ≤ _ := hhs
      _ = ((D : ℝ) * LX_Kfin D c (2 * C₁ + 4 * c) (2 * C₁) C₁ (2 * Cm) Kc₀ Kb) *
          (((N : ℝ) ^ (τ' / 4)) ^ 2 * T₀) := by ring
      _ ≤ ((N : ℝ) ^ (τ' / 4)) ^ 2 * (((N : ℝ) ^ (τ' / 4)) ^ 2 * T₀) :=
          mul_le_mul_of_nonneg_right hP2' (by positivity)
      _ = ((N : ℝ) ^ (τ' / 4)) ^ 4 * T₀ := by ring
      _ ≤ (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * (N : ℝ) ^ (-min τe εg)) := by
          rw [hP4]; exact mul_le_mul_of_nonneg_left hT (by positivity)

/-- Lemma 3.7 [lemma_G_large_2] for the law of `H_t` of (4.1) [defVt], `θ = e^{-t}`,
`t ∈ [0, 1]`: (3.24) [largG_1G] `|E⟨(G - M) E_a⟩| ≤ N^{τ'} N^{-1} (Im m)⁻¹` and (3.25)
[largG_Ex] `‖E L - K_θ‖₂ ≤ N^{τ'} N^{-1} η^{-2} N^{-(τ_e ∧ ε_g)}`, for `η ≥ c⁻¹ N^{-1/3+τ_e}`
and `η / Im m ∈ [c⁻¹ N^{-ε_g}, c N^{-ε_g}]`, `ε_g < 1/8 ∧ δ_A/4`. -/
theorem lemma_G_large_2_theta (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
        (∀ a : Fin D, ‖∫ h, ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *
            Ea D N a) ∂(ouMatLaw D N L t)‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * ((mExt (lam D N A) z).im)⁻¹)) ∧
        ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
          hsNorm (ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ -
              KTheta (lam D N A) (Real.exp (-t)) z₁ z₂) ≤
            (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * (N : ℝ) ^ (-min τe εg)) := by
  exact LX_final D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C

end RBMTransitionEdge

end
