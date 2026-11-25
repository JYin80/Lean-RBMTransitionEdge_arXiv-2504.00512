module

public import RBMTransitionEdge.Flow.LargeEtaFluct3

@[expose] public section

/-!
# Lemma 3.6: the two- and three-resolvent loops at large `η`

(3.20) [largG_Ent], (3.23) [largG_Ent_BB], (3.21) [largG_3G_1] and (3.22) [largG_3G_2] of
Lemma 3.6 [lemma_G_large] for every member of the class `LLClass C θ`, uniformly in
`θ ∈ [0, 1]`, with `K_θ` in place of `K`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A sum of `D` terms of norm at most `b` has norm at most `D b`. -/
private lemma LE_sum_le {D : ℕ} {f : Fin D → ℂ} {b : ℝ} (h : ∀ i, ‖f i‖ ≤ b) :
    ‖∑ i, f i‖ ≤ D * b := by
  calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin D, b := Finset.sum_le_sum fun i _ => h i
    _ = D * b := by simp

/-- `P_θ` is symmetric. -/
private lemma LE_P_symm (D : ℕ) (θ : ℝ) (x c : Fin D) : PTheta D θ x c = PTheta D θ c x := by
  simp [PTheta, Matrix.one_apply, eq_comm]

/-- The entries of `P_θ = θ I + (1 - θ) J / D`, `θ ∈ [0, 1]`, have modulus at most `1`. -/
private lemma LE_P_le (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x c : Fin D) :
    ‖PTheta D θ x c‖ ≤ 1 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have e : PTheta D θ x c = ((if x = c then θ else 0) + (1 - θ) / D : ℝ) := by
    by_cases h : x = c <;> simp [PTheta, h]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 ≤ (1 - θ) / D := div_nonneg (by linarith) (by linarith)
  have hle : (1 - θ) / D ≤ 1 - θ := div_le_self (by linarith) hD'
  rw [abs_of_nonneg (by split_ifs <;> linarith)]
  split_ifs <;> linarith

/-- If `v = g + M̂ P v` and `1 - M̂ P` is invertible then `v = (1 - M̂ P)⁻¹ g`. -/
private lemma LE_solve {D : ℕ} (Mh P : Matrix (Fin D) (Fin D) ℂ) (hdet : (1 - Mh * P).det ≠ 0)
    (v g : Fin D → ℂ) (h : ∀ a, v a = g a + ∑ c, Mh a c * ∑ x, P c x * v x) (a : Fin D) :
    v a = ∑ x, (1 - Mh * P)⁻¹ a x * g x := by
  have hu : IsUnit (1 - Mh * P).det := isUnit_iff_ne_zero.mpr hdet
  have e0 : (1 - Mh * P) *ᵥ v = v - Mh *ᵥ (P *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  have e1 : (1 - Mh * P) *ᵥ v = g := by
    funext b
    rw [e0]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    rw [h b]
    ring
  have e2 : v = (1 - Mh * P)⁻¹ *ᵥ g := by
    rw [← e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  conv_lhs => rw [e2]
  rfl


/-- The triangle inequality for four terms. -/
private lemma LE_norm4 (a b c d : ℂ) : ‖a - b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖a - b + c + d‖ ≤ ‖a - b + c‖ + ‖d‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _

/-- The triangle inequality for five terms. -/
private lemma LE_norm5 (a b c d e : ℂ) :
    ‖a + b - c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  calc ‖a + b - c + d + e‖ ≤ ‖a + b - c + d‖ + ‖e‖ := norm_add_le _ _
    _ ≤ ‖a + b - c‖ + ‖d‖ + ‖e‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by gcongr; exact norm_add_le _ _

/-- The normalized trace is additive. -/
private lemma LE_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- (3.39) [eq:aftertrace] solved for `v_a = ⟨G₁E_aG₂B⟩`. -/
private lemma LE_two_alg {D N : ℕ} (hD : 1 ≤ D) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (G₁ G₂ M₁ M₂ B : Matrix (Idx D N) (Idx D N) ℂ) (Z : Fin D → ℂ)
    (Mh : Matrix (Fin D) (Fin D) ℂ)
    (hMh : ∀ a c, Mh a c = (D : ℂ) * ntr (M₁ * Ea D N a * M₂ * Ea D N c))
    (hdet : (1 - Mh * PTheta D θ).det ≠ 0)
    (hid : ∀ a, ntr (G₁ * Ea D N a * G₂ * B) = ntr (G₁ * Ea D N a * M₂ * B) - Z a +
        (∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr (G₁ * Ea D N a * M₂ * Ea D N c)) *
          ntr (G₁ * Ea D N x * G₂ * B)) +
        (∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((G₂ - M₂) * Ea D N c)) *
          ntr (G₁ * Ea D N a * M₂ * Ea D N x * G₂ * B)))
    (e₀ a₀ q₀ Ψ T rn : ℝ) (he₀ : 1 ≤ e₀) (ha₀ : 0 ≤ a₀) (hΨ : 0 ≤ Ψ) (hT : 0 ≤ T)
    (hrel : a₀ ≤ T * Ψ) (hrel' : a₀ * q₀ ≤ Ψ)
    (hZ : ∀ x, ‖Z x‖ ≤ e₀ * Ψ)
    (hAw : ∀ x, ‖ntr ((G₁ - M₁) * (Ea D N x * M₂ * B))‖ ≤ 2 * e₀ * a₀)
    (hAW : ∀ a c, ‖ntr ((G₁ - M₁) * (Ea D N a * M₂ * Ea D N c))‖ ≤ 2 * e₀ * a₀)
    (hAc : ∀ c, ‖ntr ((G₂ - M₂) * Ea D N c)‖ ≤ e₀ * a₀)
    (hPv : ∀ x, ‖ntr (G₁ * Ea D N x * G₂ * B)‖ ≤ e₀ * q₀)
    (hPv' : ∀ a x, ‖ntr (G₁ * Ea D N a * M₂ * Ea D N x * G₂ * B)‖ ≤ 2 * e₀ * q₀)
    (hR : ∀ a x, ‖(1 - Mh * PTheta D θ)⁻¹ a x‖ ≤ rn) (a : Fin D) :
    ‖ntr (G₁ * Ea D N a * G₂ * B) -
        ∑ x, (1 - Mh * PTheta D θ)⁻¹ a x * ntr (M₁ * Ea D N x * M₂ * B)‖ ≤
      D * rn * ((1 + 4 * D ^ 3 + 2 * T) * e₀ ^ 2 * Ψ) := by
  set P := PTheta D θ with hP
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hP1 : ∀ x c, ‖P x c‖ ≤ 1 := LE_P_le D hD θ hθ0 hθ1
  have hPs : ∀ x c, P x c = P c x := LE_P_symm D θ
  set v : Fin D → ℂ := fun x => ntr (G₁ * Ea D N x * G₂ * B) with hv
  set m : Fin D → ℂ := fun x => ntr (M₁ * Ea D N x * M₂ * B) with hm
  set w : Fin D → ℂ := fun x => ntr (G₁ * Ea D N x * M₂ * B) with hw
  set W : Fin D → Fin D → ℂ := fun a c => (D : ℂ) * ntr (G₁ * Ea D N a * M₂ * Ea D N c) with hW
  set U : Fin D → ℂ := fun c => (D : ℂ) * ntr ((G₂ - M₂) * Ea D N c) with hU
  set Y : Fin D → Fin D → ℂ := fun a x => ntr (G₁ * Ea D N a * M₂ * Ea D N x * G₂ * B) with hY
  set Pv : Fin D → ℂ := fun c => ∑ x, P c x * v x with hPv_def
  set E₂ : Fin D → ℂ := fun a => ∑ x, ∑ c, P x c * U c * Y a x with hE₂
  set g : Fin D → ℂ := fun a => w a - Z a + (∑ c, (W a c - Mh a c) * Pv c) + E₂ a with hg
  have hsol : ∀ a, v a = g a + ∑ c, Mh a c * ∑ x, P c x * v x := by
    intro a
    have h1 := hid a
    have h2 : ∑ x, ∑ c, P x c * W a c * v x = ∑ c, W a c * Pv c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Pv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hPs x c]
      ring
    have h3 : ∑ c, W a c * Pv c = (∑ c, (W a c - Mh a c) * Pv c) + ∑ c, Mh a c * Pv c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    change v a = w a - Z a + (∑ x, ∑ c, P x c * W a c * v x) + E₂ a at h1
    rw [h2, h3] at h1
    rw [h1]
    simp only [hg]
    ring
  have hsol2 := LE_solve Mh P hdet v g hsol a
  -- the bound on `g x - m x`
  have hwm : ∀ x, ‖w x - m x‖ ≤ 2 * e₀ * a₀ := by
    intro x
    have : w x - m x = ntr ((G₁ - M₁) * (Ea D N x * M₂ * B)) := by
      simp only [hw, hm, Matrix.sub_mul, LE_ntr_sub, mul_assoc]
    rw [this]; exact hAw x
  have hWM : ∀ a c, ‖W a c - Mh a c‖ ≤ D * (2 * e₀ * a₀) := by
    intro a c
    have : W a c - Mh a c = (D : ℂ) * ntr ((G₁ - M₁) * (Ea D N a * M₂ * Ea D N c)) := by
      rw [hMh]
      simp only [hW, Matrix.sub_mul, LE_ntr_sub, mul_assoc, mul_sub]
    rw [this, norm_mul]
    have hn : ‖(D : ℂ)‖ = D := by simp
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hAW a c) (by linarith)
  have hPvb : ∀ c, ‖Pv c‖ ≤ D * (e₀ * q₀) := by
    intro c
    refine LE_sum_le fun x => ?_
    rw [norm_mul]
    calc ‖P c x‖ * ‖v x‖ ≤ 1 * (e₀ * q₀) :=
          mul_le_mul (hP1 c x) (hPv x) (norm_nonneg _) zero_le_one
      _ = e₀ * q₀ := one_mul _
  have hUb : ∀ c, ‖U c‖ ≤ D * (e₀ * a₀) := by
    intro c
    simp only [hU]
    rw [norm_mul]
    have hn : ‖(D : ℂ)‖ = D := by simp
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hAc c) (by linarith)
  have hE₂b : ∀ a, ‖E₂ a‖ ≤ D * (D * (1 * (D * (e₀ * a₀)) * (2 * e₀ * q₀))) := by
    intro a
    refine LE_sum_le fun x => LE_sum_le fun c => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hP1 x c) (hUb c) (norm_nonneg _) zero_le_one) (hPv' a x)
      (norm_nonneg _) (by positivity)
  have hgm : ∀ x, ‖g x - m x‖ ≤ (1 + 4 * D ^ 3 + 2 * T) * e₀ ^ 2 * Ψ := by
    intro x
    have e : g x - m x = (w x - m x) - Z x + (∑ c, (W x c - Mh x c) * Pv c) + E₂ x := by
      simp only [hg]; ring
    rw [e]
    have hmid : ‖∑ c, (W x c - Mh x c) * Pv c‖ ≤ D * ((D * (2 * e₀ * a₀)) * (D * (e₀ * q₀))) :=
      LE_sum_le fun c => by
        rw [norm_mul]
        exact mul_le_mul (hWM x c) (hPvb c) (norm_nonneg _) (by positivity)
    have h4 := LE_norm4 (w x - m x) (Z x) (∑ c, (W x c - Mh x c) * Pv c) (E₂ x)
    have X1 : 2 * e₀ * a₀ ≤ 2 * T * e₀ ^ 2 * Ψ := by
      have : e₀ * a₀ ≤ e₀ * (T * Ψ) := mul_le_mul_of_nonneg_left hrel (by linarith)
      nlinarith [mul_nonneg hT hΨ, mul_nonneg (mul_nonneg hT hΨ) (by linarith : 0 ≤ e₀ - 1),
        mul_nonneg (mul_nonneg (mul_nonneg hT hΨ) (by linarith : 0 ≤ e₀ - 1))
          (by linarith : 0 ≤ e₀)]
    have X2 : e₀ * Ψ ≤ e₀ ^ 2 * Ψ := by nlinarith [mul_nonneg hΨ (by linarith : 0 ≤ e₀ - 1)]
    have X3 : (D : ℝ) * ((D * (2 * e₀ * a₀)) * (D * (e₀ * q₀))) ≤ 2 * D ^ 3 * e₀ ^ 2 * Ψ := by
      have : (D : ℝ) * ((D * (2 * e₀ * a₀)) * (D * (e₀ * q₀))) =
          2 * D ^ 3 * e₀ ^ 2 * (a₀ * q₀) := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hrel' (by positivity)
    have X4 : (D : ℝ) * (D * (1 * (D * (e₀ * a₀)) * (2 * e₀ * q₀))) ≤ 2 * D ^ 3 * e₀ ^ 2 * Ψ := by
      have : (D : ℝ) * (D * (1 * (D * (e₀ * a₀)) * (2 * e₀ * q₀))) =
          2 * D ^ 3 * e₀ ^ 2 * (a₀ * q₀) := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hrel' (by positivity)
    have h5 := hwm x
    have h6 := hZ x
    have h7 := hE₂b x
    linarith
  have hfin : ‖∑ x, (1 - Mh * P)⁻¹ a x * (g x - m x)‖ ≤
      D * (rn * ((1 + 4 * D ^ 3 + 2 * T) * e₀ ^ 2 * Ψ)) :=
    LE_sum_le fun x => by
      rw [norm_mul]
      exact mul_le_mul (hR a x) (hgm x) (norm_nonneg _) ((norm_nonneg _).trans (hR a x))
  have e : ntr (G₁ * Ea D N a * G₂ * B) - ∑ x, (1 - Mh * P)⁻¹ a x * ntr (M₁ * Ea D N x * M₂ * B) =
      ∑ x, (1 - Mh * P)⁻¹ a x * (g x - m x) := by
    rw [show ntr (G₁ * Ea D N a * G₂ * B) = v a from rfl, hsol2]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rfl
  rw [e]
  calc _ ≤ _ := hfin
    _ = _ := by ring

/-- `I + K_θ P_θ = R` for `K_θ = R M̂` and `R = (1 - M̂ P_θ)⁻¹` (the identity `I + K_θP_θ = R₃₁` of
Lemma 3.6 [lemma_G_large]). -/
private lemma LE_one_add_KP {D : ℕ} (Mh P : Matrix (Fin D) (Fin D) ℂ)
    (hdet : (1 - Mh * P).det ≠ 0) :
    1 + (1 - Mh * P)⁻¹ * Mh * P = (1 - Mh * P)⁻¹ := by
  have hu : IsUnit (1 - Mh * P).det := isUnit_iff_ne_zero.mpr hdet
  have h := Matrix.nonsing_inv_mul _ hu
  calc 1 + (1 - Mh * P)⁻¹ * Mh * P = (1 - Mh * P)⁻¹ * (1 - Mh * P) + (1 - Mh * P)⁻¹ * Mh * P := by
        rw [h]
    _ = (1 - Mh * P)⁻¹ := by noncomm_ring

/-- The sum defining `ten3Contr`, with the sums reordered. -/
private lemma LE_ten3Contr_eq {D : ℕ} (R₁ R₂ R₃ : Matrix (Fin D) (Fin D) ℂ)
    (T : Fin D → Fin D → Fin D → ℂ) (a₁ a₂ a₃ : Fin D) :
    ten3Contr R₁ R₂ R₃ T a₁ a₂ a₃ =
      ∑ b, R₂ a₂ b * ∑ c, R₃ a₃ c * ∑ x, R₁ a₁ x * T x b c := by
  unfold ten3Contr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The algebra of the three-resolvent expansion of Lemma 3.6 [lemma_G_large]: the identity of
`resTriple_aftertrace`, with `L₍₃,₁₎` and `T` replaced by `K^{(3,1)}_θ` and `R₁₂ ⊗ M`, solved in
the second slot. -/
private lemma LE_three_alg {D : ℕ} (hD : 1 ≤ D) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (L T Zt : Fin D → Fin D → Fin D → ℂ)
    (L31 : Matrix (Fin D) (Fin D) ℂ) (L13 : Fin D → Fin D → ℂ)
    (hcyc : ∀ x a, L13 x a = L31 a x)
    (Wt Mh23 Mh31 R12 : Matrix (Fin D) (Fin D) ℂ) (U : Fin D → ℂ)
    (V : Fin D → Fin D → Fin D → Fin D → ℂ) (Tm : Fin D → Fin D → Fin D → ℂ)
    (hdet23 : (1 - Mh23 * PTheta D θ).det ≠ 0) (hdet31 : (1 - Mh31 * PTheta D θ).det ≠ 0)
    (hid : ∀ a₁ a₂ a₃, L a₁ a₂ a₃ = T a₁ a₂ a₃ - Zt a₁ a₂ a₃ +
        (∑ x, ∑ c, PTheta D θ x c * T a₁ a₂ c * L13 x a₃) +
        (∑ x, ∑ c, PTheta D θ x c * Wt a₂ c * L a₁ x a₃) +
        (∑ x, ∑ c, PTheta D θ x c * U c * V a₁ a₂ a₃ x))
    (z₀ u₀ v₀ w₀ l₀ t₀ tt₀ k₀ r₂₃ r₃₁ : ℝ)
    (hZ : ∀ a₁ a₂ a₃, ‖Zt a₁ a₂ a₃‖ ≤ z₀) (hU : ∀ c, ‖U c‖ ≤ u₀)
    (hV : ∀ a₁ a₂ a₃ x, ‖V a₁ a₂ a₃ x‖ ≤ v₀)
    (hWd : ∀ a c, ‖Wt a c - Mh23 a c‖ ≤ w₀) (hL : ∀ a₁ a₂ a₃, ‖L a₁ a₂ a₃‖ ≤ l₀)
    (hT : ∀ a₁ a₂ c, ‖T a₁ a₂ c‖ ≤ t₀)
    (hTT : ∀ a₁ a₂ c, ‖T a₁ a₂ c - ∑ x, R12 a₁ x * Tm x a₂ c‖ ≤ tt₀)
    (hLK : ∀ a x, ‖L31 a x - ((1 - Mh31 * PTheta D θ)⁻¹ * Mh31) a x‖ ≤ k₀)
    (hR23 : ∀ a b, ‖(1 - Mh23 * PTheta D θ)⁻¹ a b‖ ≤ r₂₃)
    (hR31 : ∀ a b, ‖(1 - Mh31 * PTheta D θ)⁻¹ a b‖ ≤ r₃₁) (a₁ a₂ a₃ : Fin D) :
    ‖L a₁ a₂ a₃ - ten3Contr R12 (1 - Mh23 * PTheta D θ)⁻¹ (1 - Mh31 * PTheta D θ)⁻¹ Tm a₁ a₂ a₃‖ ≤
      D * r₂₃ * (D * r₃₁ * tt₀ + D * D * k₀ * t₀ + z₀ + D * D * u₀ * v₀ + D * D * w₀ * l₀) := by
  set P := PTheta D θ with hP
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hP1 : ∀ x c, ‖P x c‖ ≤ 1 := LE_P_le D hD θ hθ0 hθ1
  have hPs : ∀ x c, P x c = P c x := LE_P_symm D θ
  set R23 := (1 - Mh23 * P)⁻¹ with hR23def
  set R31 := (1 - Mh31 * P)⁻¹ with hR31def
  set K31 := R31 * Mh31 with hK31
  have h0 : Fin D := ⟨0, hD⟩
  have hr₃₁ : 0 ≤ r₃₁ := (norm_nonneg _).trans (hR31 h0 h0)
  have hr₂₃ : 0 ≤ r₂₃ := (norm_nonneg _).trans (hR23 h0 h0)
  have htt : 0 ≤ tt₀ := (norm_nonneg _).trans (hTT h0 h0 h0)
  have hk : 0 ≤ k₀ := (norm_nonneg _).trans (hLK h0 h0)
  have ht : 0 ≤ t₀ := (norm_nonneg _).trans (hT h0 h0 h0)
  have hz : 0 ≤ z₀ := (norm_nonneg _).trans (hZ h0 h0 h0)
  have hu : 0 ≤ u₀ := (norm_nonneg _).trans (hU h0)
  have hv : 0 ≤ v₀ := (norm_nonneg _).trans (hV h0 h0 h0 h0)
  have hw : 0 ≤ w₀ := (norm_nonneg _).trans (hWd h0 h0)
  have hl : 0 ≤ l₀ := (norm_nonneg _).trans (hL h0 h0 h0)
  have hone : 1 + K31 * P = R31 := LE_one_add_KP Mh31 P hdet31
  -- `(I + L₃₁ P) = R₃₁ + (L₃₁ - K₃₁) P`
  have hIL : ∀ a c, ((1 : Matrix (Fin D) (Fin D) ℂ) + L31 * P) a c =
      R31 a c + ((L31 - K31) * P) a c := by
    intro a c
    have : (1 : Matrix (Fin D) (Fin D) ℂ) + L31 * P = R31 + (L31 - K31) * P := by
      calc (1 : Matrix (Fin D) (Fin D) ℂ) + L31 * P = (1 + K31 * P) + (L31 - K31) * P := by
            rw [Matrix.sub_mul]; abel
        _ = R31 + (L31 - K31) * P := by rw [hone]
    rw [this]
    rfl
  set v : Fin D → ℂ := fun x => L a₁ x a₃ with hv_def
  set Pv : Fin D → ℂ := fun c => ∑ x, P c x * v x with hPv_def
  set E₅ : Fin D → ℂ := fun b => ∑ x, ∑ c, P x c * U c * V a₁ b a₃ x with hE₅
  set g : Fin D → ℂ := fun b => (∑ c, (R31 a₃ c + ((L31 - K31) * P) a₃ c) * T a₁ b c) -
    Zt a₁ b a₃ + (∑ c, (Wt b c - Mh23 b c) * Pv c) + E₅ b with hg
  have hsol : ∀ b, v b = g b + ∑ c, Mh23 b c * ∑ x, P c x * v x := by
    intro b
    have h1 := hid a₁ b a₃
    have e1 : ∑ x, ∑ c, P x c * T a₁ b c * L13 x a₃ = ∑ c, T a₁ b c * (L31 * P) a₃ c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hcyc]
      ring
    have e2 : ∑ x, ∑ c, P x c * Wt b c * L a₁ x a₃ = ∑ c, Wt b c * Pv c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Pv, v, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hPs x c]
      ring
    have e3 : ∑ c, Wt b c * Pv c = (∑ c, (Wt b c - Mh23 b c) * Pv c) + ∑ c, Mh23 b c * Pv c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have e4 : T a₁ b a₃ + ∑ c, T a₁ b c * (L31 * P) a₃ c =
        ∑ c, (R31 a₃ c + ((L31 - K31) * P) a₃ c) * T a₁ b c := by
      have : T a₁ b a₃ = ∑ c, (1 : Matrix (Fin D) (Fin D) ℂ) a₃ c * T a₁ b c := by
        simp [Matrix.one_apply]
      rw [this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← hIL, Matrix.add_apply]
      ring
    rw [e1, e2, e3] at h1
    change v b = _ at h1
    rw [h1]
    simp only [hg, hE₅]
    have : T a₁ b a₃ - Zt a₁ b a₃ + ∑ c, T a₁ b c * (L31 * P) a₃ c =
        (T a₁ b a₃ + ∑ c, T a₁ b c * (L31 * P) a₃ c) - Zt a₁ b a₃ := by ring
    rw [this, e4]
    ring
  have hsol2 := LE_solve Mh23 P hdet23 v g hsol a₂
  -- the main term
  set g0 : Fin D → ℂ := fun b => ∑ c, R31 a₃ c * ∑ x, R12 a₁ x * Tm x b c with hg0
  have hK : ten3Contr R12 R23 R31 Tm a₁ a₂ a₃ = ∑ b, R23 a₂ b * g0 b :=
    LE_ten3Contr_eq R12 R23 R31 Tm a₁ a₂ a₃
  have hPvb : ∀ c, ‖Pv c‖ ≤ D * (1 * l₀) := by
    intro c
    refine LE_sum_le fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hP1 c x) (hL a₁ x a₃) (norm_nonneg _) zero_le_one
  have hLKP : ∀ c, ‖((L31 - K31) * P) a₃ c‖ ≤ D * k₀ := by
    intro c
    simp only [Matrix.mul_apply]
    have : ∀ x, ‖(L31 - K31) a₃ x * P x c‖ ≤ k₀ * 1 := fun x => by
      rw [norm_mul]
      exact mul_le_mul (hLK a₃ x) (hP1 x c) (norm_nonneg _) hk
    have := LE_sum_le this
    rwa [mul_one] at this
  have hΔ : ∀ b, ‖g b - g0 b‖ ≤ D * (r₃₁ * tt₀) + D * ((D * k₀) * t₀) + z₀ +
      D * (w₀ * (D * (1 * l₀))) + D * (D * (1 * u₀ * v₀)) := by
    intro b
    have e : g b - g0 b = (∑ c, R31 a₃ c * (T a₁ b c - ∑ x, R12 a₁ x * Tm x b c)) +
        (∑ c, ((L31 - K31) * P) a₃ c * T a₁ b c) - Zt a₁ b a₃ +
        (∑ c, (Wt b c - Mh23 b c) * Pv c) + E₅ b := by
      simp only [hg, hg0, add_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    rw [e]
    have s1 : ‖∑ c, R31 a₃ c * (T a₁ b c - ∑ x, R12 a₁ x * Tm x b c)‖ ≤ D * (r₃₁ * tt₀) :=
      LE_sum_le fun c => by
        rw [norm_mul]
        exact mul_le_mul (hR31 a₃ c) (hTT a₁ b c) (norm_nonneg _) hr₃₁
    have s2 : ‖∑ c, ((L31 - K31) * P) a₃ c * T a₁ b c‖ ≤ D * ((D * k₀) * t₀) :=
      LE_sum_le fun c => by
        rw [norm_mul]
        exact mul_le_mul (hLKP c) (hT a₁ b c) (norm_nonneg _) (by positivity)
    have s4 : ‖∑ c, (Wt b c - Mh23 b c) * Pv c‖ ≤ D * (w₀ * (D * (1 * l₀))) :=
      LE_sum_le fun c => by
        rw [norm_mul]
        exact mul_le_mul (hWd b c) (hPvb c) (norm_nonneg _) hw
    have s5 : ‖E₅ b‖ ≤ D * (D * (1 * u₀ * v₀)) :=
      LE_sum_le fun x => LE_sum_le fun c => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hP1 x c) (hU c) (norm_nonneg _) zero_le_one) (hV a₁ b a₃ x)
          (norm_nonneg _) (by positivity)
    have h5 := LE_norm5 (∑ c, R31 a₃ c * (T a₁ b c - ∑ x, R12 a₁ x * Tm x b c))
      (∑ c, ((L31 - K31) * P) a₃ c * T a₁ b c) (Zt a₁ b a₃) (∑ c, (Wt b c - Mh23 b c) * Pv c)
      (E₅ b)
    have := hZ a₁ b a₃
    linarith
  have hfin : ‖∑ b, R23 a₂ b * (g b - g0 b)‖ ≤ D * (r₂₃ * (D * (r₃₁ * tt₀) + D * ((D * k₀) * t₀) +
      z₀ + D * (w₀ * (D * (1 * l₀))) + D * (D * (1 * u₀ * v₀)))) :=
    LE_sum_le fun b => by
      rw [norm_mul]
      exact mul_le_mul (hR23 a₂ b) (hΔ b) (norm_nonneg _) hr₂₃
  have e : L a₁ a₂ a₃ - ten3Contr R12 R23 R31 Tm a₁ a₂ a₃ = ∑ b, R23 a₂ b * (g b - g0 b) := by
    rw [hK]
    have : L a₁ a₂ a₃ = v a₂ := rfl
    rw [this, hsol2]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rfl
  rw [e]
  calc _ ≤ _ := hfin
    _ = _ := by ring

/-! ### Events of high probability -/

/-- `P` holds outside an event of measure at most `k ε`. -/
private def LE_HP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ε : ENNReal) (k : ℕ)
    (P : Ω → Prop) : Prop :=
  μ {ω | ¬ P ω} ≤ k * ε

section LE_HPlemmas

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ENNReal}

/-- Two properties that hold outside events of measure `k₁ ε` and `k₂ ε` hold together outside
an event of measure `(k₁ + k₂) ε`. -/
private lemma LE_HP.and {k₁ k₂ : ℕ} {P Q : Ω → Prop} (hP : LE_HP μ ε k₁ P) (hQ : LE_HP μ ε k₂ Q) :
    LE_HP μ ε (k₁ + k₂) (fun ω => P ω ∧ Q ω) := by
  unfold LE_HP at *
  refine le_trans (measure_mono (t := {ω | ¬ P ω} ∪ {ω | ¬ Q ω}) ?_) ?_
  · intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
    exact hω ⟨not_not.mp hcon.1, not_not.mp hcon.2⟩
  · refine (measure_union_le _ _).trans ?_
    push_cast
    rw [add_mul]
    exact add_le_add hP hQ

/-- A consequence of a property holds outside the same events. -/
private lemma LE_HP.mono {k : ℕ} {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) (hP : LE_HP μ ε k P) :
    LE_HP μ ε k Q := by
  unfold LE_HP at *
  exact (measure_mono (s := {ω | ¬ Q ω}) (t := {ω | ¬ P ω})
    (fun ω (hω : ¬ Q ω) (hp : P ω) => hω (hPQ ω hp))).trans hP

/-- The number of events may be enlarged. -/
private lemma LE_HP.mono_k {k k' : ℕ} {P : Ω → Prop} (hk : k ≤ k') (hP : LE_HP μ ε k P) :
    LE_HP μ ε k' P := by
  unfold LE_HP at *
  refine hP.trans ?_
  gcongr

/-- A property indexed by a finite type holds outside the union of the exceptional events. -/
private lemma LE_HP.forall {ι : Type*} [Fintype ι] {k : ℕ} {P : ι → Ω → Prop}
    (hP : ∀ i, LE_HP μ ε k (P i)) : LE_HP μ ε (Fintype.card ι * k) (fun ω => ∀ i, P i ω) := by
  unfold LE_HP at *
  refine le_trans (measure_mono (t := ⋃ i, {ω | ¬ P i ω}) ?_) ?_
  · intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ i, μ {ω | ¬ P i ω} ≤ ∑ _i : ι, (k : ENNReal) * ε := Finset.sum_le_sum fun i _ => hP i
      _ = (((Fintype.card ι * k : ℕ)) : ENNReal) * ε := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-- A property that holds almost surely holds outside an event of measure `0`. -/
private lemma LE_HP.of_ae {P : Ω → Prop} (h : ∀ᵐ ω ∂μ, P ω) : LE_HP μ ε 0 P := by
  unfold LE_HP
  rw [ae_iff] at h
  simp [h]

/-- An event of measure at most `ε`. -/
private lemma LE_HP.of_le {P : Ω → Prop} (h : μ {ω | ¬ P ω} ≤ ε) : LE_HP μ ε 1 P := by
  unfold LE_HP
  simpa using h

end LE_HPlemmas

/-- The final count: `k` events of measure `N^{-(D'+1)}` have measure at most `N^{-D'}`. -/
private lemma LE_count {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (N k : ℕ) (hN : 1 ≤ N)
    (hk : k ≤ N) (D' : ℝ) (P : Ω → Prop)
    (hP : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) k P) :
    μ {ω | ¬ P ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  refine hP.trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ((k : ℝ)) * (N : ℝ) ^ (-(D' + 1)) ≤ (N : ℝ) ^ (-D') := by
    have h1 : (N : ℝ) ^ (-D') = (N : ℝ) * (N : ℝ) ^ (-(D' + 1)) := by
      have : (-D' : ℝ) = 1 + -(D' + 1) := by ring
      rw [this, Real.rpow_add hN0, Real.rpow_one]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Real.rpow_nonneg hN0.le _)
  calc (k : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) =
      ENNReal.ofReal ((k : ℝ) * (N : ℝ) ^ (-(D' + 1))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal e

/-! ### The local-law estimates in the form used here -/

/-- The normalized trace is homogeneous. -/
private lemma LE_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `star z ∈ 𝐃(τ)` along with `z`. -/
private lemma LE_specDom_star {τ : ℝ} {N : ℕ} {z : ℂ} (h : z ∈ specDom τ N) :
    star z ∈ specDom τ N := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rwa [norm_star], ?_⟩
  simpa [Complex.star_def, Complex.conj_im, abs_neg] using h2

/-- (2.23) [eq:aver_local] for a finite family of deterministic matrices of norm `≤ κ`. -/
private lemma LE_aver (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (C : ℕ → ℝ)
    (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ (ι : Type) [Fintype ι] (Bf : ι → Matrix (Idx D N) (Idx D N) ℂ) (κ : ℝ), 0 < κ →
        (∀ i, opNorm (Bf i) ≤ κ) →
        LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-D'))) (Fintype.card ι) (fun h =>
          ∀ i, ∀ z ∈ specDom τ N,
            ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * Bf i)‖ ≤
              κ * ((N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)))) := by
  obtain ⟨N₀, hN₀⟩ := aver_local D hD δA τ hδA hτ C τ' hτ' D' hD'
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ hμ A hA ι _ Bf κ hκ hB => ?_⟩
  have := LE_HP.forall (μ := μ) (ε := ENNReal.ofReal ((N : ℝ) ^ (-D')))
    (P := fun (i : ι) (h : Idx D N → Idx D N → ℂ) => ∀ z ∈ specDom τ N,
      ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * Bf i)‖ ≤
        κ * ((N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)))) (k := 1) (fun i => ?_)
  · simpa using this
  refine LE_HP.of_le ?_
  have hB1 : opNorm (((κ⁻¹ : ℝ) : ℂ) • Bf i) ≤ 1 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ)]
    calc κ⁻¹ * opNorm (Bf i) ≤ κ⁻¹ * κ := mul_le_mul_of_nonneg_left (hB i) (inv_pos.mpr hκ).le
      _ = 1 := inv_mul_cancel₀ hκ.ne'
  refine le_trans (measure_mono ?_) (hN₀ N hN θ hθ0 hθ1 μ hμ A hA _ hB1)
  intro h hh
  simp only [Set.mem_ofPred_eq, not_forall, not_le] at hh
  obtain ⟨z, hz, hlt⟩ := hh
  refine ⟨z, hz, ?_⟩
  rw [Matrix.mul_smul, LE_ntr_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hκ)]
  calc (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)) = κ⁻¹ * (κ * ((N : ℝ) ^ τ' *
        (1 / ((N : ℝ) * |z.im|)))) := by field_simp
    _ < κ⁻¹ * ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * Bf i)‖ :=
        mul_lt_mul_of_pos_left hlt (inv_pos.mpr hκ)

/-- `G(z̄) = G(z)^*` as a flag of `resProd`: for `z₁ ∈ {z, z̄}` and Hermitian `X`. -/
private lemma LE_flag {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) {z z₁ : ℂ} (hz : 0 < z.im) (h₁ : z₁ = z ∨ z₁ = star z) :
    res X z₁ = if decide (z₁ = star z) then (res X z)ᴴ else res X z := by
  by_cases h : z₁ = star z
  · rw [ite_eq_left (by simpa using h), h]
    exact res_conj X hX z hz
  · rw [ite_eq_right (by simpa using h)]
    rcases h₁ with rfl | h'
    · rfl
    · exact absurd h' h

/-- (A.53) [entprodG] with two resolvents, `z₁, z₂ ∈ {z, z̄}` and deterministic matrices of norm
`≤ κ₁, κ₂`: `|⟨G₁ B₁ G₂ B₂⟩| ≤ κ₁ κ₂ N^{τ'} Im m / η` outside probability `N^{-D'}`. -/
private lemma LE_entprod2 (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (C : ℕ → ℝ) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → 1 ≤ (N : ℝ) * z.im * (mExt (lam D N A) z).im →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ (B₁ B₂ : Matrix (Idx D N) (Idx D N) ℂ) (κ₁ κ₂ : ℝ), 0 < κ₁ → 0 < κ₂ →
        opNorm B₁ ≤ κ₁ → opNorm B₂ ≤ κ₂ →
        LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-D'))) 1 (fun h => (Matrix.of h).IsHermitian →
          ‖ntr (res (Matrix.of h + lam D N A) z₁ * B₁ * res (Matrix.of h + lam D N A) z₂ * B₂)‖ ≤
            κ₁ * κ₂ * ((N : ℝ) ^ τ' * ((mExt (lam D N A) z).im / z.im))) := by
  obtain ⟨N₀, hN₀⟩ := entprodG_unif D 2 hD (by norm_num) δA τ 1 hδA hτ one_pos C τ' hτ' D' hD'
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hNz z₁ z₂ h₁ h₂ B₁ B₂ κ₁ κ₂ hκ₁ hκ₂ hB₁
    hB₂ => ?_⟩
  have hB₁' : opNorm (((κ₁⁻¹ : ℝ) : ℂ) • B₁) ≤ 1 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ₁)]
    calc κ₁⁻¹ * opNorm B₁ ≤ κ₁⁻¹ * κ₁ := mul_le_mul_of_nonneg_left hB₁ (inv_pos.mpr hκ₁).le
      _ = 1 := inv_mul_cancel₀ hκ₁.ne'
  have hB₂' : opNorm (((κ₂⁻¹ : ℝ) : ℂ) • B₂) ≤ 1 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ₂)]
    calc κ₂⁻¹ * opNorm B₂ ≤ κ₂⁻¹ * κ₂ := mul_le_mul_of_nonneg_left hB₂ (inv_pos.mpr hκ₂).le
      _ = 1 := inv_mul_cancel₀ hκ₂.ne'
  have hev := (hN₀ N hN θ hθ0 hθ1 μ hμ A hA (fun _ => z) (fun _ => ⟨hz, hzim, hNz⟩)
    ![decide (z₁ = star z), decide (z₂ = star z)]
    ![((κ₁⁻¹ : ℝ) : ℂ) • B₁, ((κ₂⁻¹ : ℝ) : ℂ) • B₂]
    (Fin.forall_fin_two.mpr ⟨hB₁', hB₂'⟩)).1
  refine LE_HP.of_le (le_trans (measure_mono ?_) hev)
  intro h hh
  simp only [Set.mem_ofPred_eq, not_imp, not_le] at hh
  obtain ⟨hH, hlt⟩ := hh
  simp only [Set.mem_ofPred_eq]
  have hX : (Matrix.of h + lam D N A).IsHermitian := hH.add (lam_isHermitian D N A)
  have hf₁ := LE_flag _ hX hzim h₁
  have hf₂ := LE_flag _ hX hzim h₂
  have hprod : resProd (fun _ => res (Matrix.of h + lam D N A) z)
      ![decide (z₁ = star z), decide (z₂ = star z)]
      ![((κ₁⁻¹ : ℝ) : ℂ) • B₁, ((κ₂⁻¹ : ℝ) : ℂ) • B₂] =
      (((κ₁⁻¹ * κ₂⁻¹ : ℝ)) : ℂ) • (res (Matrix.of h + lam D N A) z₁ * B₁ *
        res (Matrix.of h + lam D N A) z₂ * B₂) := by
    simp only [resProd, List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      List.ofFn_zero, List.prod_cons, List.prod_nil, Matrix.mul_one, Fin.succ_zero_eq_one]
    rw [hf₁, hf₂]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, Complex.ofReal_mul]
    congr 1
    ring
  have hbnd : bndA4 (fun _ : Fin 2 => (mExt (lam D N A) z).im) (fun _ : Fin 2 => z.im) 2 =
      (mExt (lam D N A) z).im / z.im := by simp [bndA4]
  simp only [hprod, hbnd, LE_ntr_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr hκ₁), abs_of_pos (inv_pos.mpr hκ₂)]
  have : (N : ℝ) ^ τ' * ((mExt (lam D N A) z).im / z.im) =
      (κ₁⁻¹ * κ₂⁻¹) * (κ₁ * κ₂ * ((N : ℝ) ^ τ' * ((mExt (lam D N A) z).im / z.im))) := by
    field_simp
  rw [this]
  exact mul_lt_mul_of_pos_left hlt (mul_pos (inv_pos.mpr hκ₁) (inv_pos.mpr hκ₂))

/-- Rescaling a matrix of norm at most `κ` gives a matrix of norm at most `1`. -/
private lemma LE_scale_le {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (κ : ℝ)
    (hκ : 0 < κ) (hB : opNorm B ≤ κ) : opNorm (((κ⁻¹ : ℝ) : ℂ) • B) ≤ 1 := by
  rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ)]
  calc κ⁻¹ * opNorm B ≤ κ⁻¹ * κ := mul_le_mul_of_nonneg_left hB (inv_pos.mpr hκ).le
    _ = 1 := inv_mul_cancel₀ hκ.ne'

/-- (A.53) [entprodG] with three resolvents, `z₁, z₂, z₃ ∈ {z, z̄}` and deterministic matrices of
norm `≤ κ₁, κ₂, κ₃`: `|⟨G₁ B₁ G₂ B₂ G₃ B₃⟩| ≤ κ₁ κ₂ κ₃ N^{τ'} Im m / η²` outside probability
`N^{-D'}`. -/
private lemma LE_entprod3 (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (C : ℕ → ℝ) (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → 1 ≤ (N : ℝ) * z.im * (mExt (lam D N A) z).im →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → (z₃ = z ∨ z₃ = star z) →
      ∀ (B₁ B₂ B₃ : Matrix (Idx D N) (Idx D N) ℂ) (κ₁ κ₂ κ₃ : ℝ), 0 < κ₁ → 0 < κ₂ → 0 < κ₃ →
        opNorm B₁ ≤ κ₁ → opNorm B₂ ≤ κ₂ → opNorm B₃ ≤ κ₃ →
        LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-D'))) 1 (fun h => (Matrix.of h).IsHermitian →
          ‖ntr (res (Matrix.of h + lam D N A) z₁ * B₁ * res (Matrix.of h + lam D N A) z₂ * B₂ *
              res (Matrix.of h + lam D N A) z₃ * B₃)‖ ≤
            κ₁ * κ₂ * κ₃ * ((N : ℝ) ^ τ' * ((mExt (lam D N A) z).im / z.im ^ 2))) := by
  obtain ⟨N₀, hN₀⟩ := entprodG_unif D 3 hD (by norm_num) δA τ 1 hδA hτ one_pos C τ' hτ' D' hD'
  refine ⟨N₀, fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hNz z₁ z₂ z₃ h₁ h₂ h₃ B₁ B₂ B₃ κ₁ κ₂ κ₃
    hκ₁ hκ₂ hκ₃ hB₁ hB₂ hB₃ => ?_⟩
  have hB' : ∀ i : Fin 3, opNorm (![((κ₁⁻¹ : ℝ) : ℂ) • B₁, ((κ₂⁻¹ : ℝ) : ℂ) • B₂,
      ((κ₃⁻¹ : ℝ) : ℂ) • B₃] i) ≤ 1 := by
    intro i
    fin_cases i
    · exact LE_scale_le B₁ κ₁ hκ₁ hB₁
    · exact LE_scale_le B₂ κ₂ hκ₂ hB₂
    · exact LE_scale_le B₃ κ₃ hκ₃ hB₃
  have hev := (hN₀ N hN θ hθ0 hθ1 μ hμ A hA (fun _ => z) (fun _ => ⟨hz, hzim, hNz⟩)
    ![decide (z₁ = star z), decide (z₂ = star z), decide (z₃ = star z)]
    ![((κ₁⁻¹ : ℝ) : ℂ) • B₁, ((κ₂⁻¹ : ℝ) : ℂ) • B₂, ((κ₃⁻¹ : ℝ) : ℂ) • B₃] hB').1
  refine LE_HP.of_le (le_trans (measure_mono ?_) hev)
  intro h hh
  simp only [Set.mem_ofPred_eq, not_imp, not_le] at hh
  obtain ⟨hH, hlt⟩ := hh
  simp only [Set.mem_ofPred_eq]
  have hX : (Matrix.of h + lam D N A).IsHermitian := hH.add (lam_isHermitian D N A)
  have hf₁ := LE_flag _ hX hzim h₁
  have hf₂ := LE_flag _ hX hzim h₂
  have hf₃ := LE_flag _ hX hzim h₃
  have hprod : resProd (fun _ => res (Matrix.of h + lam D N A) z)
      ![decide (z₁ = star z), decide (z₂ = star z), decide (z₃ = star z)]
      ![((κ₁⁻¹ : ℝ) : ℂ) • B₁, ((κ₂⁻¹ : ℝ) : ℂ) • B₂, ((κ₃⁻¹ : ℝ) : ℂ) • B₃] =
      (((κ₁⁻¹ * κ₂⁻¹ * κ₃⁻¹ : ℝ)) : ℂ) • (res (Matrix.of h + lam D N A) z₁ * B₁ *
        res (Matrix.of h + lam D N A) z₂ * B₂ * res (Matrix.of h + lam D N A) z₃ * B₃) := by
    simp only [resProd, List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      List.ofFn_zero, List.prod_cons, List.prod_nil, Matrix.mul_one, Fin.succ_zero_eq_one,
      Matrix.cons_val, Fin.succ_one_eq_two]
    rw [hf₁, hf₂, hf₃]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, Complex.ofReal_mul]
    congr 1
    ring
  have hbnd : bndA4 (fun _ : Fin 3 => (mExt (lam D N A) z).im) (fun _ : Fin 3 => z.im) 3 =
      (mExt (lam D N A) z).im / z.im ^ 2 := by simp [bndA4]
  simp only [hprod, hbnd, LE_ntr_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr hκ₁), abs_of_pos (inv_pos.mpr hκ₂), abs_of_pos (inv_pos.mpr hκ₃)]
  have : (N : ℝ) ^ τ' * ((mExt (lam D N A) z).im / z.im ^ 2) =
      (κ₁⁻¹ * κ₂⁻¹ * κ₃⁻¹) * (κ₁ * κ₂ * κ₃ *
        ((N : ℝ) ^ τ' * ((mExt (lam D N A) z).im / z.im ^ 2))) := by
    field_simp
  rw [this]
  exact mul_lt_mul_of_pos_left hlt (mul_pos (mul_pos (inv_pos.mpr hκ₁) (inv_pos.mpr hκ₂))
    (inv_pos.mpr hκ₃))

/-! ### The numerical facts of the setting of Lemma 3.6 -/

/-- `‖A^*‖ = ‖A‖` for the operator norm. -/
private lemma LE_opNorm_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- For `N ≥ 20^{1/δ_A}`, `N^{-δ_A} ≤ 1/20`. -/
private lemma LE_pow_le (δA : ℝ) (hδA : 0 < δA) (N : ℕ) (hN : (20 : ℝ) ^ (1 / δA) ≤ N) :
    (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
  have h20 : (0 : ℝ) < 20 ^ (1 / δA) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (20 : ℝ) ≤ (N : ℝ) ^ δA := by
    have := Real.rpow_le_rpow h20.le hN hδA.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδA.ne', Real.rpow_one] at this
  rw [Real.rpow_neg (by linarith [h20, hN]), one_div]
  exact inv_anti₀ (by norm_num) h1

/-- `‖M(z₁)‖ ≤ 5/4` for `z₁ ∈ {z, z̄}`, `‖Λ‖ ≤ 1/10`. -/
private lemma LE_opNorm_MExt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z z₁ : ℂ} (hz : 0 < z.im)
    (h₁ : z₁ = z ∨ z₁ = star z) : opNorm (MExt Λ z₁) ≤ 5 / 4 := by
  obtain ⟨-, -, hM⟩ := mSol_apriori Λ hΛ hℓ z hz
  have h54 : opNorm (MSol Λ z) ≤ 5 / 4 := by
    refine hM.le.trans ?_
    rw [inv_le_comm₀ (by have : 0 ≤ opNorm Λ := norm_nonneg _; linarith) (by norm_num)]
    linarith
  have hpos : MExt Λ z = MSol Λ z := by
    simp only [MExt, MSol, mExt, hz, ↓reduceIte]
  rcases h₁ with rfl | rfl
  · rw [hpos]; exact h54
  · rw [(mExt_conj Λ hΛ z hz.ne').2, LE_opNorm_conj, hpos]; exact h54

/-- The numerical consequences of the window of Lemma 3.6 [lemma_G_large]. -/
private lemma LE_num (D : ℕ) (hD : 1 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA)
    (hεg : 0 < εg) (hc : 1 ≤ c) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      opNorm (lam D N A) ≤ 1 / 10 ∧ 0 < (mExt (lam D N A) z).im ∧
        (mExt (lam D N A) z).im ≤ 1 ∧ z.im ≤ τ⁻¹ ∧
        1 ≤ (N : ℝ) * z.im * (mExt (lam D N A) z).im ∧
        (mExt (lam D N A) z).im / z.im ≤ c * (N : ℝ) ^ εg := by
  refine ⟨max 1 (max ⌈(20 : ℝ) ^ (1 / δA)⌉₊ ⌈c ^ 9⌉₊), le_max_left _ _,
    fun N hN A hA z hz hzim hη hq1 hq2 => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN20 : (20 : ℝ) ^ (1 / δA) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hNc : c ^ 9 ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hN)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    have h2 := LE_pow_le δA hδA N hN20
    linarith
  obtain ⟨hι0, -, -⟩ := mSol_spec (lam D N A) hΛ z hzim
  obtain ⟨-, hm1, -⟩ := mSol_apriori (lam D N A) hΛ hℓ z hzim
  have hmE : mExt (lam D N A) z = mSol (lam D N A) z := by simp only [mExt, hzim, ↓reduceIte]
  rw [hmE] at hq1 hq2 ⊢
  set ι := (mSol (lam D N A) z).im with hι
  have hι1 : ι ≤ 1 := (Complex.im_le_norm _).trans hm1.le
  have hητ : z.im ≤ τ⁻¹ := (Complex.im_le_norm z).trans hz.1
  -- `N = t³` with `t = N^{1/3} ≥ c³`
  set t : ℝ := (N : ℝ) ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hN3 : (N : ℝ) = t ^ 3 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have htc : c ^ 3 ≤ t := by
    have h1 : (c ^ 3) ^ 3 ≤ t ^ 3 := by
      rw [← hN3, ← pow_mul]; exact hNc
    exact le_of_pow_le_pow_left₀ (by norm_num) ht0.le h1
  have hc0 : 0 < c := by linarith
  have hηlow : (c * t)⁻¹ ≤ z.im := by
    have : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) = (c * t)⁻¹ := by
      rw [Real.rpow_neg hN0.le, ← ht, mul_inv]
    rwa [this] at hη
  have hNeg : (N : ℝ) ^ (-εg) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  have hq2' : z.im / ι ≤ c := hq2.trans (by nlinarith)
  have hιlow : z.im / c ≤ ι := by
    rw [div_le_iff₀ hc0]
    rw [div_le_iff₀ hι0] at hq2'
    linarith
  refine ⟨hℓ, hι0, hι1, hητ, ?_, ?_⟩
  · -- `N η Im m ≥ N η² / c ≥ t / c³ ≥ 1`
    have h1 : (N : ℝ) * z.im * ι ≥ (N : ℝ) * z.im * (z.im / c) :=
      mul_le_mul_of_nonneg_left hιlow (by positivity)
    have h2 : (c * t)⁻¹ * (c * t)⁻¹ ≤ z.im * z.im := mul_le_mul hηlow hηlow (by positivity) hzim.le
    have h3 : (N : ℝ) * z.im * (z.im / c) = (N : ℝ) * (z.im * z.im) / c := by ring
    have h4 : (N : ℝ) * ((c * t)⁻¹ * (c * t)⁻¹) / c = t / c ^ 3 := by
      rw [hN3]; field_simp
    have h5 : (N : ℝ) * ((c * t)⁻¹ * (c * t)⁻¹) / c ≤ (N : ℝ) * (z.im * z.im) / c :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hN0.le) hc0.le
    have h6 : 1 ≤ t / c ^ 3 := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · -- `Im m / η ≤ c N^{εg}`
    have hq1' : c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / ι := hq1
    have : ι / z.im = (z.im / ι)⁻¹ := (inv_div _ _).symm
    rw [this]
    have hpos : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    calc (z.im / ι)⁻¹ ≤ (c⁻¹ * (N : ℝ) ^ (-εg))⁻¹ := inv_anti₀ hpos hq1'
      _ = c * (N : ℝ) ^ εg := by
        rw [mul_inv, inv_inv, Real.rpow_neg hN0.le, inv_inv]

open scoped Matrix.Norms.L2Operator in
/-- `‖E_a‖ ≤ 1`. -/
private lemma LE_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- The operator norm of a product of three matrices. -/
private lemma LE_opNorm_mul3 {n : Type*} [Fintype n] [DecidableEq n] (X Y Z : Matrix n n ℂ)
    (a b c : ℝ) (hX : opNorm X ≤ a) (hY : opNorm Y ≤ b) (hZ : opNorm Z ≤ c) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : opNorm (X * Y * Z) ≤ a * b * c := by
  refine (opNorm_mul_le _ _).trans ?_
  have h1 : opNorm (X * Y) ≤ a * b :=
    (opNorm_mul_le _ _).trans (mul_le_mul hX hY (norm_nonneg _) ha)
  exact mul_le_mul h1 hZ (norm_nonneg _) (mul_nonneg ha hb)

/-- For `z₁ ∈ {z, z̄}`, `|Im z₁| = Im z`. -/
private lemma LE_abs_im {z z₁ : ℂ} (hz : 0 < z.im) (h₁ : z₁ = z ∨ z₁ = star z) :
    |z₁.im| = z.im := by
  rcases h₁ with rfl | rfl
  · exact abs_of_pos hz
  · simp [Complex.conj_im, abs_of_pos hz]

/-- `z₁ ∈ {z, z̄}` lies in `𝐃(τ)` along with `z`. -/
private lemma LE_mem_specDom {τ : ℝ} {N : ℕ} {z z₁ : ℂ} (hz : z ∈ specDom τ N)
    (h₁ : z₁ = z ∨ z₁ = star z) : z₁ ∈ specDom τ N := by
  rcases h₁ with rfl | rfl
  · exact hz
  · exact LE_specDom_star hz

/-- `Im z₁ ≠ 0` for `z₁ ∈ {z, z̄}` and `Im z > 0`. -/
private lemma LE_im_ne {z z₁ : ℂ} (hz : 0 < z.im) (h₁ : z₁ = z ∨ z₁ = star z) : z₁.im ≠ 0 := by
  intro h
  have := LE_abs_im hz h₁
  rw [h] at this
  simp at this
  linarith

/-- There are arbitrarily large powers: for `s > 0`, `K ≤ N^s` for large `N`. -/
private lemma LE_exists_pow_ge (K s : ℝ) (hs : 0 < s) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K ≤ (N : ℝ) ^ s := by
  have h := ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

/-! ### The two-resolvent loop -/

/-- The core of `lemma_G_large_two` and `lemma_G_large_BB`: for a fixed deterministic `‖B‖ ≤ 1`,
outside probability `k N^{-(D'+1)}`, `|⟨G₁E_aG₂B⟩ - Σ_x ((1 - M̂P_θ)⁻¹)_{ax} ⟨M₁E_xM₂B⟩| ≤
N^{τ'} N⁻¹η⁻² ‖(1 - M̂P_θ)⁻¹‖` for every `a`. -/
private lemma LE_two_core (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) (τ' : ℝ) (hτ' : 0 < τ')
    (D' : ℝ) (hD' : 0 < D') :
    ∃ k : ℕ, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) k (fun h => ∀ a : Fin D,
          ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a * res (Matrix.of h + lam D N A) z₂ *
              B) - ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a x *
              ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * B)‖ ≤
            (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
              opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)) := by
  have hD1 : 1 ≤ D := by omega
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hε : 0 < τ' / 4 := by linarith
  have hD'1 : 0 < D' + 1 := by linarith
  obtain ⟨N₁, hN₁pos, hnum⟩ := LE_num D hD1 δA τ εg c hδA hεg hc
  obtain ⟨N₂, h2⟩ := underTwo_fluct D hD δA τ εg c hδA hτ hεg hεg' hc C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₃, h3⟩ := LE_aver D hD1 δA τ hδA hτ C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₄, h4⟩ := LE_entprod2 D hD1 δA τ hδA hτ C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₅, h5⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  obtain ⟨N₆, h6⟩ := LE_exists_pow_ge (D * (1 + 4 * D ^ 3 + 2 * τ⁻¹)) (τ' / 2) (by linarith)
  refine ⟨10 * D ^ 2, N₁ + N₂ + N₃ + N₄ + N₅ + N₆, by omega,
    fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂ B hB => ?_⟩
  have hN1' : N₁ ≤ N := by omega
  have hN2' : N₂ ≤ N := by omega
  have hN3' : N₃ ≤ N := by omega
  have hN4' : N₄ ≤ N := by omega
  have hN5' : N₅ ≤ N := by omega
  have hN6' : N₆ ≤ N := by omega
  obtain ⟨hℓ, hι0, hι1, hητ, hNηι, hιη⟩ := hnum N hN1' A hA z hz hzim hη hq1 hq2
  have hN1 : 1 ≤ N := hN₁pos.trans hN1'
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hz₁ : z₁ ∈ specDom τ N := LE_mem_specDom hz h₁
  have hz₂ : z₂ ∈ specDom τ N := LE_mem_specDom hz h₂
  have hM₁ : opNorm (MExt (lam D N A) z₁) ≤ 5 / 4 := LE_opNorm_MExt _ hΛ hℓ hzim h₁
  have hM₂ : opNorm (MExt (lam D N A) z₂) ≤ 5 / 4 := LE_opNorm_MExt _ hΛ hℓ hzim h₂
  obtain ⟨hdet, -⟩ := h5 N hN5' A hA z hz.1 hzim z₁ z₂ h₁ h₂ θ hθ0 hθ1
  refine ⟨hdet, ?_⟩
  set e₀ : ℝ := (N : ℝ) ^ (τ' / 4) with he₀def
  have he₀ : 1 ≤ e₀ := Real.one_le_rpow hNr hε.le
  set η := z.im with hη_def
  set ι := (mExt (lam D N A) z).im with hι_def
  -- the events
  have E1 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D) * 1)
      (fun h => ∀ x : Fin D, ‖underTwoB (lam D N A) θ h z₁ z₂ x B‖ ≤
        e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹)) := by
    refine LE_HP.forall (fun x => LE_HP.of_le ?_)
    have := h2 N hN2' θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂ B hB x
    simpa only [not_le] using this
  have E2 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D))
      (fun h => ∀ x : Fin D, ∀ z' ∈ specDom τ N,
        ‖ntr ((res (Matrix.of h + lam D N A) z' - MExt (lam D N A) z') *
          (Ea D N x * MExt (lam D N A) z₂ * B))‖ ≤
        (5 / 4 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * |z'.im|)))) :=
    h3 N hN3' θ hθ0 hθ1 μ hμ A hA (Fin D) (fun x => Ea D N x * MExt (lam D N A) z₂ * B) (5 / 4)
      (by norm_num) (fun x => by
        have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N x) hM₂ hB (by norm_num)
          (by norm_num)
        simpa using this)
  have E3 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D × Fin D))
      (fun h => ∀ p : Fin D × Fin D, ∀ z' ∈ specDom τ N,
        ‖ntr ((res (Matrix.of h + lam D N A) z' - MExt (lam D N A) z') *
          (Ea D N p.1 * MExt (lam D N A) z₂ * Ea D N p.2))‖ ≤
        (5 / 4 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * |z'.im|)))) :=
    h3 N hN3' θ hθ0 hθ1 μ hμ A hA (Fin D × Fin D)
      (fun p => Ea D N p.1 * MExt (lam D N A) z₂ * Ea D N p.2) (5 / 4)
      (by norm_num) (fun p => by
        have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N p.1) hM₂
          (LE_opNorm_Ea D N p.2) (by norm_num) (by norm_num)
        simpa using this)
  have E4 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D))
      (fun h => ∀ c : Fin D, ∀ z' ∈ specDom τ N,
        ‖ntr ((res (Matrix.of h + lam D N A) z' - MExt (lam D N A) z') * Ea D N c)‖ ≤
        (1 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * |z'.im|)))) :=
    h3 N hN3' θ hθ0 hθ1 μ hμ A hA (Fin D) (fun c => Ea D N c) 1 one_pos
      (fun c => LE_opNorm_Ea D N c)
  have E5 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D) * 1)
      (fun h => ∀ x : Fin D, (Matrix.of h).IsHermitian →
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N x * res (Matrix.of h + lam D N A) z₂ * B)‖ ≤
        1 * 1 * ((N : ℝ) ^ (τ' / 4) * (ι / η))) :=
    LE_HP.forall (fun x => h4 N hN4' θ hθ0 hθ1 μ hμ A hA z hz hzim hNηι z₁ z₂ h₁ h₂
      (Ea D N x) B 1 1 one_pos one_pos (LE_opNorm_Ea D N x) hB)
  have E6 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D × Fin D) * 1)
      (fun h => ∀ p : Fin D × Fin D, (Matrix.of h).IsHermitian →
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * (Ea D N p.1 * MExt (lam D N A) z₂ * Ea D N p.2) *
            res (Matrix.of h + lam D N A) z₂ * B)‖ ≤
        (5 / 4 : ℝ) * 1 * ((N : ℝ) ^ (τ' / 4) * (ι / η))) :=
    LE_HP.forall (fun p => h4 N hN4' θ hθ0 hθ1 μ hμ A hA z hz hzim hNηι z₁ z₂ h₁ h₂
      (Ea D N p.1 * MExt (lam D N A) z₂ * Ea D N p.2) B (5 / 4) 1 (by norm_num) one_pos
      (by
        have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N p.1) hM₂
          (LE_opNorm_Ea D N p.2) (by norm_num) (by norm_num)
        simpa using this) hB)
  have hall := (LE_HP.of_ae (ε := ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) hμ.herm).and
    (E1.and (E2.and (E3.and (E4.and (E5.and E6)))))
  -- the numerical parameters
  set a₀ : ℝ := 1 / ((N : ℝ) * η) with ha₀def
  set q₀ : ℝ := ι / η with hq₀def
  set Ψ : ℝ := (N : ℝ)⁻¹ * (η ^ 2)⁻¹ with hΨdef
  have hη0 : 0 < η := hzim
  have ha₀ : 0 ≤ a₀ := by positivity
  have hq₀ : 0 ≤ q₀ := by positivity
  have hΨ : 0 ≤ Ψ := by positivity
  have hrel : a₀ ≤ τ⁻¹ * Ψ := by
    have : a₀ = η * Ψ := by simp only [ha₀def, hΨdef]; field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right hητ hΨ
  have hrel' : a₀ * q₀ ≤ Ψ := by
    have : a₀ * q₀ = ι * Ψ := by simp only [ha₀def, hq₀def, hΨdef]; field_simp
    rw [this]; nlinarith
  have hrn : 0 ≤ opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ := by
    unfold opNorm; exact norm_nonneg _
  have hΨrn : 0 ≤ Ψ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ := mul_nonneg hΨ hrn
  have hpow : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have he2 : e₀ ^ 2 = (N : ℝ) ^ (τ' / 2) := by
    rw [he₀def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  refine LE_HP.mono_k (k' := 10 * D ^ 2) ?_ (LE_HP.mono ?_ hall)
  · simp only [Fintype.card_fin, Fintype.card_prod]
    have h1 : D ≤ D * D := Nat.le_mul_self D
    nlinarith
  intro h hh a
  obtain ⟨hH, b1, b2, b3, b4, b5, b6⟩ := hh
  have hAw : ∀ x : Fin D, ‖ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) *
      (Ea D N x * MExt (lam D N A) z₂ * B))‖ ≤ 2 * e₀ * a₀ := by
    intro x
    have := b2 x z₁ hz₁
    rw [LE_abs_im hzim h₁] at this
    refine this.trans ?_
    have h0 : 0 ≤ e₀ * a₀ := mul_nonneg (by linarith) ha₀
    have : (5 / 4 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * η))) = (5 / 4) * (e₀ * a₀) := by
      simp only [ha₀def, he₀def]
    rw [this]; linarith
  have hAW : ∀ a c : Fin D, ‖ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) *
      (Ea D N a * MExt (lam D N A) z₂ * Ea D N c))‖ ≤ 2 * e₀ * a₀ := by
    intro a c
    have := b3 (a, c) z₁ hz₁
    rw [LE_abs_im hzim h₁] at this
    refine this.trans ?_
    have h0 : 0 ≤ e₀ * a₀ := mul_nonneg (by linarith) ha₀
    have : (5 / 4 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * η))) = (5 / 4) * (e₀ * a₀) := by
      simp only [ha₀def, he₀def]
    rw [this]; linarith
  have hAc : ∀ c : Fin D, ‖ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) *
      Ea D N c)‖ ≤ e₀ * a₀ := by
    intro c
    have := b4 c z₂ hz₂
    rw [LE_abs_im hzim h₂] at this
    refine this.trans (le_of_eq ?_)
    simp only [ha₀def, he₀def, one_mul]
    rfl
  have hPv : ∀ x : Fin D, ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N x *
      res (Matrix.of h + lam D N A) z₂ * B)‖ ≤ e₀ * q₀ := by
    intro x
    refine (b5 x hH).trans (le_of_eq ?_)
    simp only [hq₀def, he₀def, one_mul]
  have hPv' : ∀ a x : Fin D, ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a *
      MExt (lam D N A) z₂ * Ea D N x * res (Matrix.of h + lam D N A) z₂ * B)‖ ≤ 2 * e₀ * q₀ := by
    intro a x
    have := b6 (a, x) hH
    simp only [Matrix.mul_assoc] at this ⊢
    refine this.trans ?_
    have h0 : 0 ≤ e₀ * q₀ := mul_nonneg (by linarith) hq₀
    have e : (5 / 4 : ℝ) * 1 * ((N : ℝ) ^ (τ' / 4) * (ι / η)) = (5 / 4) * (e₀ * q₀) := by
      simp only [hq₀def, he₀def]; ring
    rw [e]; linarith
  have hR : ∀ a x : Fin D, ‖(1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a x‖ ≤
      opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ := fun a x => norm_apply_le_opNorm _ a x
  have key := LE_two_alg hD1 θ hθ0 hθ1 (res (Matrix.of h + lam D N A) z₁)
    (res (Matrix.of h + lam D N A) z₂) (MExt (lam D N A) z₁) (MExt (lam D N A) z₂) B
    (fun x => underTwoB (lam D N A) θ h z₁ z₂ x B) (Mhat (lam D N A) z₁ z₂) (fun a c => rfl) hdet
    (fun a => resPair_aftertrace θ A h hH z₁ z₂ (LE_im_ne hzim h₂) a B) e₀ a₀ q₀ Ψ τ⁻¹
    (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) he₀ ha₀ hΨ (by positivity) hrel hrel'
    b1 hAw hAW hAc hPv hPv' hR a
  calc _ ≤ D * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ *
        ((1 + 4 * D ^ 3 + 2 * τ⁻¹) * e₀ ^ 2 * Ψ) := key
    _ = (D * (1 + 4 * D ^ 3 + 2 * τ⁻¹)) * e₀ ^ 2 *
        (Ψ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) := by ring
    _ ≤ (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) *
        (Ψ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) := by
      rw [he2]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h6 N hN6')
        (Real.rpow_nonneg hN0.le _)) hΨrn
    _ = _ := by rw [hpow]

/-- Entrywise bounds give a Hilbert–Schmidt bound. -/
private lemma LE_hsNorm_le {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (h : ∀ a b, ‖X a b‖ ≤ β) : hsNorm X ≤ D * β := by
  unfold hsNorm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ _i : Fin D, ∑ _j : Fin D, β ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (D * β) ^ 2 := by simp; ring

/-- Entrywise bounds give a bound for the `ℓ²` norm of a `D³` tensor. -/
private lemma LE_ten3Norm_le {D : ℕ} (hD : 1 ≤ D) (T : Fin D → Fin D → Fin D → ℂ) (β : ℝ)
    (hβ : 0 ≤ β) (h : ∀ a b c, ‖T a b c‖ ≤ β) : ten3Norm T ≤ D ^ 2 * β := by
  unfold ten3Norm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  calc ∑ a, ∑ b, ∑ c, ‖T a b c‖ ^ 2 ≤ ∑ _a : Fin D, ∑ _b : Fin D, ∑ _c : Fin D, β ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h a b c) 2
    _ = (D : ℝ) ^ 3 * β ^ 2 := by simp; ring
    _ ≤ (D : ℝ) ^ 4 * β ^ 2 := by
        have : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 4 := pow_le_pow_right₀ hDr (by norm_num)
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = ((D : ℝ) ^ 2 * β) ^ 2 := by ring

/-- (3.20) [largG_Ent] of Lemma 3.6 [lemma_G_large] for the class, uniformly in `θ ∈ [0, 1]`,
with `K_θ`: for `η ≥ c⁻¹ N^{-1/3}` and `η / Im m ∈ [c⁻¹ N^{-ε_g}, c N^{-ε_g}]`,
`‖L - K_θ‖₂ ≤ N^{τ'} N^{-1} η^{-2} ‖(1 - M̂ P_θ)⁻¹‖` outside probability `N^{-D'}`. -/
theorem lemma_G_large_two (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        μ {h | (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
            opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
          hsNorm (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  have hD1 : 1 ≤ D := by omega
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  obtain ⟨k, N₀, hN₀pos, hcore⟩ := LE_two_core D hD δA τ εg c hδA hτ hεg hεg' hc C (τ' / 2)
    (by linarith) D' hD'
  obtain ⟨N₁, h1⟩ := LE_exists_pow_ge ((D : ℝ) ^ 2) (τ' / 2) (by linarith)
  refine ⟨N₀ + D * k + N₁, fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hb := fun b : Fin D => hcore N (by omega) θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂
    h₁ h₂ (Ea D N b) (LE_opNorm_Ea D N b)
  refine ⟨(hb ⟨0, hD1⟩).1, ?_⟩
  have hHP := LE_HP.forall (fun b => (hb b).2)
  have hDk : Fintype.card (Fin D) * k ≤ N := by simp; omega
  have hcount := LE_count N _ hN1 hDk D' _ hHP
  refine le_trans (measure_mono ?_) hcount
  intro h hh
  simp only [Set.mem_ofPred_eq] at hh ⊢
  intro hall
  refine absurd hh (not_lt.mpr ?_)
  set rn := opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ with hrn_def
  set Ψ : ℝ := (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ with hΨdef
  have hrn : 0 ≤ rn := norm_nonneg _
  have hΨrn : 0 ≤ Ψ * rn := mul_nonneg (by positivity) hrn
  have hent : ∀ a b : Fin D, ‖(Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) a b‖ ≤
      D * ((N : ℝ) ^ (τ' / 2) * (Ψ * rn)) := by
    intro a b
    have e : (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) a b =
        (D : ℂ) * (ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a *
          res (Matrix.of h + lam D N A) z₂ * Ea D N b) -
          ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a x *
            ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * Ea D N b)) := by
      simp only [Matrix.sub_apply, KTheta, Matrix.mul_apply, Mhat, Lmat, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e, norm_mul]
    have hn : ‖(D : ℂ)‖ = D := by simp
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hall b a) (by linarith)
  have hHS := LE_hsNorm_le _ _ (by positivity) hent
  have hpow : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hNp : 0 ≤ (N : ℝ) ^ (τ' / 2) := Real.rpow_nonneg hN0.le _
  calc hsNorm (Lmat (lam D N A) h z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤
        D * (D * ((N : ℝ) ^ (τ' / 2) * (Ψ * rn))) := hHS
    _ = (D : ℝ) ^ 2 * (N : ℝ) ^ (τ' / 2) * (Ψ * rn) := by ring
    _ ≤ (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) * (Ψ * rn) := by
      refine mul_le_mul_of_nonneg_right ?_ hΨrn
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (h1 N (by omega)) hNp
    _ = (N : ℝ) ^ τ' * (Ψ * rn) := by rw [hpow]

/-- (3.23) [largG_Ent_BB] of Lemma 3.6 [lemma_G_large] for the class, uniformly in
`θ ∈ [0, 1]`: for deterministic `‖B‖ ≤ 1`,
`⟨G₁ E_a G₂ B⟩ = Σ_x ((1 - M̂ P_θ)⁻¹)_{ax} ⟨M₁ E_x M₂ B⟩ + O(N^{τ'} N^{-1} η^{-2} ‖(1 - M̂ P_θ)⁻¹‖)`
outside probability `N^{-D'}`. -/
theorem lemma_G_large_BB (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 → ∀ a : Fin D,
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        μ {h | (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ *
            opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) <
          ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a * res (Matrix.of h + lam D N A) z₂ *
              B) - ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a x *
              ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨k, N₀, hN₀pos, hcore⟩ := LE_two_core D hD δA τ εg c hδA hτ hεg hεg' hc C τ' hτ' D' hD'
  refine ⟨N₀ + k, fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂ B hB a => ?_⟩
  obtain ⟨hdet, hHP⟩ := hcore N (by omega) θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂
    B hB
  refine ⟨hdet, ?_⟩
  have := LE_count N k (by omega) (by omega) D' _ (LE_HP.mono (fun h hh => hh a) hHP)
  simpa only [not_le] using this

/-! ### The three-resolvent loop -/

/-- The bounds (A.8) [1-M], (A.9) [1-M-2] for `‖(1 - M̂ P_θ)⁻¹‖`, `θ ∈ [0, 1]`, in the window of
Lemma 3.6 [lemma_G_large]. -/
private lemma LE_Rb (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        (z₂ = star z₁ → opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ ≤
          C₀ * ((mExt (lam D N A) z).im / z.im)) ∧
        (z₂ = z₁ → opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ ≤
          C₁ * min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨Cc, hCc, Nc, hconj⟩ := one_minus_Mhat_conj D hD δA τ hδA hτ
  obtain ⟨Cs, hCs, Ns, hsame⟩ := one_minus_Mhat_same D hD δA εg c⁻¹ τ hδA hεg hεg'
    (inv_pos.mpr hc0) (inv_le_one_of_one_le₀ hc) hτ
  obtain ⟨N5, h5⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  refine ⟨2 * Cc, 2 * Cs, by positivity, by positivity, Nc + Ns + N5,
    fun N hN A hA z hzn hz hq1 hq2 θ hθ0 hθ1 z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hdet, hnorm⟩ := h5 N (by omega) A hA z hzn hz z₁ z₂ h₁ h₂ θ hθ0 hθ1
  refine ⟨hdet, fun hconj' => ?_, fun hsame' => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hconj N (by omega) A hA z hzn hz
    have hmE : mExt (lam D N A) z = mSol (lam D N A) z := by simp only [mExt, hz, ↓reduceIte]
    rw [hmE]
    have hb : opNorm (1 - Mhat (lam D N A) z₁ z₂)⁻¹ ≤ Cc * ((mSol (lam D N A) z).im / z.im) := by
      rcases h₁ with rfl | rfl
      · have : z₂ = star z₁ := hconj'
        rw [this]; rw [e1] ; exact e3
      · have : z₂ = z := by rw [hconj']; simp
        rw [this, e2]; exact e3
    calc _ ≤ 2 * opNorm (1 - Mhat (lam D N A) z₁ z₂)⁻¹ := hnorm
      _ ≤ 2 * (Cc * ((mSol (lam D N A) z).im / z.im)) := by linarith
      _ = _ := by ring
  · have hmE : mExt (lam D N A) z = mSol (lam D N A) z := by simp only [mExt, hz, ↓reduceIte]
    rw [hmE] at hq1 hq2 ⊢
    obtain ⟨-, -, e3, -⟩ := hsame N (by omega) A hA z hzn hz hq1 (by rwa [inv_inv]) z₁ h₁
    have : z₂ = z₁ := hsame'
    subst this
    calc _ ≤ 2 * opNorm (1 - Mhat (lam D N A) z₂ z₂)⁻¹ := hnorm
      _ ≤ 2 * (Cs * min ((mSol (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)) := by linarith
      _ = _ := by ring

/-- An entry of a matrix is bounded by its Hilbert–Schmidt norm. -/
private lemma LE_entry_le_hsNorm {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    ‖X a b‖ ≤ hsNorm X := by
  unfold hsNorm
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖X a b‖ ^ 2 ≤ ∑ j, ‖X a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖X a j‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)

/-- Cyclicity of the normalized trace. -/
private lemma LE_ntr_comm {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) :
    ntr (X * Y) = ntr (Y * X) := by
  simp only [ntr, Matrix.trace_mul_comm X Y]

/-- Cyclicity of the normalized trace for a product of four matrices. -/
private lemma LE_ntr_rot4 {ι : Type*} [Fintype ι] (G₁ E₁ G₂ E₂ : Matrix ι ι ℂ) :
    ntr (G₁ * E₁ * G₂ * E₂) = ntr (G₂ * E₂ * G₁ * E₁) := by
  calc ntr (G₁ * E₁ * G₂ * E₂) = ntr ((G₁ * E₁) * (G₂ * E₂)) := by simp only [Matrix.mul_assoc]
    _ = ntr ((G₂ * E₂) * (G₁ * E₁)) := LE_ntr_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Cyclicity of the normalized trace for a product of six matrices. -/
private lemma LE_ntr_rot6 {ι : Type*} [Fintype ι] (G₁ E₁ G₂ E₂ G₃ E₃ : Matrix ι ι ℂ) :
    ntr (G₁ * E₁ * G₂ * E₂ * G₃ * E₃) = ntr (G₂ * E₂ * G₃ * E₃ * G₁ * E₁) := by
  calc ntr (G₁ * E₁ * G₂ * E₂ * G₃ * E₃) = ntr ((G₁ * E₁) * (G₂ * E₂ * G₃ * E₃)) := by
        simp only [Matrix.mul_assoc]
    _ = ntr ((G₂ * E₂ * G₃ * E₃) * (G₁ * E₁)) := LE_ntr_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Trace cyclicity: `L₍₁,₂,₃₎` and `L₍₂,₃,₁₎` have the same entries up to rotation. -/
private lemma LE_Lten3_rot {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
    (z₁ z₂ z₃ : ℂ) (a₁ a₂ a₃ : Fin D) :
    Lten3 Λ h z₁ z₂ z₃ a₁ a₂ a₃ = Lten3 Λ h z₂ z₃ z₁ a₂ a₃ a₁ := by
  unfold Lten3
  rw [LE_ntr_rot6]

/-- Trace cyclicity: `K_{θ,3}` is invariant under rotation of the three slots. -/
private lemma LE_KTheta3_rot {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ)
    (z₁ z₂ z₃ : ℂ) (a₁ a₂ a₃ : Fin D) :
    KTheta3 Λ θ z₁ z₂ z₃ a₁ a₂ a₃ = KTheta3 Λ θ z₂ z₃ z₁ a₂ a₃ a₁ := by
  unfold KTheta3 ten3Contr
  have e : ∀ b₁ b₂ b₃ : Fin D, ntr (MExt Λ z₁ * Ea D N b₁ * MExt Λ z₂ * Ea D N b₂ *
      MExt Λ z₃ * Ea D N b₃) = ntr (MExt Λ z₂ * Ea D N b₂ * MExt Λ z₃ * Ea D N b₃ *
      MExt Λ z₁ * Ea D N b₁) := fun b₁ b₂ b₃ => LE_ntr_rot6 _ _ _ _ _ _
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₃ _ => ?_
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  ring

/-- The sum of the five error terms of the three-resolvent expansion, in terms of `Ψ₃`. -/
private lemma LE_S_bound (Dr e₀ η ι N r₁₂ r₂₃ r₃₁ : ℝ) (hDr : 1 ≤ Dr) (he₀ : 1 ≤ e₀) (hη : 0 < η)
    (hι0 : 0 ≤ ι) (hι1 : ι ≤ 1) (hN : 0 < N) (hr₁₂ : 0 ≤ r₁₂) (hr₂₃ : 0 ≤ r₂₃) (hr₃₁ : 0 ≤ r₃₁) :
    Dr * r₂₃ * (Dr * r₃₁ * (Dr * (2 * e₀ * (N⁻¹ * (η ^ 2)⁻¹ * r₁₂))) +
      Dr * Dr * (e₀ * (N⁻¹ * (η ^ 2)⁻¹ * r₃₁)) * (Dr * (2 * e₀ * (ι / η))) +
      Dr * (e₀ * (N⁻¹ * (η ^ 3)⁻¹)) +
      Dr * Dr * (Dr * (e₀ * (1 / (N * η)))) * (Dr * (2 * e₀ * (ι / η ^ 2))) +
      Dr * Dr * (Dr * (2 * e₀ * (1 / (N * η)))) * (Dr * (e₀ * (ι / η ^ 2)))) ≤
    Dr * r₂₃ * (e₀ ^ 2 * (N⁻¹ * (η ^ 3)⁻¹) *
      (2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr + 4 * Dr ^ 4)) := by
  have hΨ : 0 ≤ N⁻¹ * (η ^ 3)⁻¹ := by positivity
  have hS : (Dr * r₃₁ * (Dr * (2 * e₀ * (N⁻¹ * (η ^ 2)⁻¹ * r₁₂))) +
      Dr * Dr * (e₀ * (N⁻¹ * (η ^ 2)⁻¹ * r₃₁)) * (Dr * (2 * e₀ * (ι / η))) +
      Dr * (e₀ * (N⁻¹ * (η ^ 3)⁻¹)) +
      Dr * Dr * (Dr * (e₀ * (1 / (N * η)))) * (Dr * (2 * e₀ * (ι / η ^ 2))) +
      Dr * Dr * (Dr * (2 * e₀ * (1 / (N * η)))) * (Dr * (e₀ * (ι / η ^ 2)))) =
      (N⁻¹ * (η ^ 3)⁻¹) * (2 * Dr ^ 2 * e₀ * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * e₀ ^ 2 * ι * r₃₁ +
        Dr * e₀ + 4 * Dr ^ 4 * e₀ ^ 2 * ι) := by
    field_simp
    ring
  have h1 : 2 * Dr ^ 2 * e₀ * η * r₁₂ * r₃₁ ≤ 2 * Dr ^ 2 * e₀ ^ 2 * η * r₁₂ * r₃₁ := by
    have : 0 ≤ 2 * Dr ^ 2 * η * r₁₂ * r₃₁ := by positivity
    nlinarith [mul_nonneg this (by linarith : 0 ≤ e₀ - 1),
      mul_nonneg (mul_nonneg this (by linarith : 0 ≤ e₀ - 1)) (by linarith : 0 ≤ e₀)]
  have h2 : 2 * Dr ^ 3 * e₀ ^ 2 * ι * r₃₁ ≤ 2 * Dr ^ 3 * e₀ ^ 2 * (ι * r₃₁) := by
    have : ι * r₃₁ ≥ 0 := by positivity
    linarith
  have h3 : Dr * e₀ ≤ Dr * e₀ ^ 2 := by
    have : e₀ ≤ e₀ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have h4 : 4 * Dr ^ 4 * e₀ ^ 2 * ι ≤ 4 * Dr ^ 4 * e₀ ^ 2 := by
    have : 0 ≤ 4 * Dr ^ 4 * e₀ ^ 2 := by positivity
    nlinarith
  rw [hS]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have : (N⁻¹ * (η ^ 3)⁻¹) * (2 * Dr ^ 2 * e₀ * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * e₀ ^ 2 * ι * r₃₁ +
        Dr * e₀ + 4 * Dr ^ 4 * e₀ ^ 2 * ι) ≤ (N⁻¹ * (η ^ 3)⁻¹) *
        (e₀ ^ 2 * (2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr + 4 * Dr ^ 4)) := by
    refine mul_le_mul_of_nonneg_left ?_ hΨ
    nlinarith
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The error terms of the three-resolvent expansion of Lemma 3.6 [lemma_G_large] when `z₁, z₂, z₃`
are not all equal: two conjugate pairs and one equal pair give `N^{ε_g}`. -/
private lemma LE_caseA (Dr e₀ η ι Ψ₃ X c C₀ C₁ r₁₂ r₂₃ r₃₁ : ℝ) (hDr : 1 ≤ Dr) (he₀ : 1 ≤ e₀)
    (hη : 0 < η) (hι : 0 < ι) (hΨ : 0 ≤ Ψ₃) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hr₁₂ : 0 ≤ r₁₂) (hr₃₁ : 0 ≤ r₃₁)
    (h12 : r₁₂ ≤ C₀ * (ι / η)) (h23 : r₂₃ ≤ C₀ * (ι / η)) (h31 : r₃₁ ≤ C₁ * ι⁻¹)
    (hX : ι / η ≤ c * X) :
    Dr * r₂₃ * (e₀ ^ 2 * Ψ₃ * (2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr +
      4 * Dr ^ 4)) ≤
    (Dr * (C₀ * c) * (2 * Dr ^ 2 * (C₀ * C₁) + 2 * Dr ^ 3 * C₁ + Dr + 4 * Dr ^ 4)) *
      (e₀ ^ 2 * Ψ₃ * X) := by
  have hb1 : η * r₁₂ * r₃₁ ≤ C₀ * C₁ := by
    calc η * r₁₂ * r₃₁ ≤ η * (C₀ * (ι / η)) * (C₁ * ι⁻¹) := by gcongr
      _ = C₀ * C₁ := by field_simp
  have hb2 : ι * r₃₁ ≤ C₁ := by
    calc ι * r₃₁ ≤ ι * (C₁ * ι⁻¹) := by gcongr
      _ = C₁ := by field_simp
  have hbr : 2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr + 4 * Dr ^ 4 ≤
      2 * Dr ^ 2 * (C₀ * C₁) + 2 * Dr ^ 3 * C₁ + Dr + 4 * Dr ^ 4 := by
    have e : 2 * Dr ^ 2 * η * r₁₂ * r₃₁ = 2 * Dr ^ 2 * (η * r₁₂ * r₃₁) := by ring
    rw [e]
    have h1 : 2 * Dr ^ 2 * (η * r₁₂ * r₃₁) ≤ 2 * Dr ^ 2 * (C₀ * C₁) :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    have h2 : 2 * Dr ^ 3 * (ι * r₃₁) ≤ 2 * Dr ^ 3 * C₁ :=
      mul_le_mul_of_nonneg_left hb2 (by positivity)
    linarith
  have hr : r₂₃ ≤ C₀ * c * X := by
    calc r₂₃ ≤ C₀ * (ι / η) := h23
      _ ≤ C₀ * (c * X) := mul_le_mul_of_nonneg_left hX hC₀
      _ = C₀ * c * X := by ring
  have hP : 0 ≤ e₀ ^ 2 * Ψ₃ := by positivity
  calc Dr * r₂₃ * (e₀ ^ 2 * Ψ₃ * (2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr +
        4 * Dr ^ 4)) ≤ Dr * (C₀ * c * X) * (e₀ ^ 2 * Ψ₃ * (2 * Dr ^ 2 * (C₀ * C₁) +
        2 * Dr ^ 3 * C₁ + Dr + 4 * Dr ^ 4)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hr (by linarith)) ?_ ?_ ?_
        · exact mul_le_mul_of_nonneg_left hbr hP
        · have : 0 ≤ 2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr + 4 * Dr ^ 4 := by
            positivity
          exact mul_nonneg hP this
        · have : 0 ≤ X := by
            by_contra hneg
            rw [not_le] at hneg
            have : c * X < 0 := mul_neg_of_pos_of_neg hc hneg
            have : 0 < ι / η := by positivity
            linarith
          positivity
    _ = _ := by ring

/-- The error terms of the three-resolvent expansion of Lemma 3.6 [lemma_G_large] when `z₁, z₂, z₃`
are all equal: three equal pairs give `ρ = (Im m)⁻¹ ∧ N^{ε_g}`, with `ρ² ≤ c / η`. -/
private lemma LE_caseB (Dr e₀ η ι Ψ₃ ρ c C₁ r₁₂ r₂₃ r₃₁ : ℝ) (hDr : 1 ≤ Dr) (he₀ : 1 ≤ e₀)
    (hη : 0 < η) (hι : 0 < ι) (hΨ : 0 ≤ Ψ₃) (hρ : 0 ≤ ρ) (hC₁ : 0 ≤ C₁)
    (hr₁₂ : 0 ≤ r₁₂) (hr₃₁ : 0 ≤ r₃₁)
    (h12 : r₁₂ ≤ C₁ * ρ) (h23 : r₂₃ ≤ C₁ * ρ) (h31 : r₃₁ ≤ C₁ * ρ)
    (hρι : ρ * ι ≤ 1) (hρ2 : ρ ^ 2 * η ≤ c) :
    Dr * r₂₃ * (e₀ ^ 2 * Ψ₃ * (2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr +
      4 * Dr ^ 4)) ≤
    (Dr * C₁ * (2 * Dr ^ 2 * (C₁ ^ 2 * c) + 2 * Dr ^ 3 * C₁ + Dr + 4 * Dr ^ 4)) *
      (e₀ ^ 2 * Ψ₃ * ρ) := by
  have hb1 : η * r₁₂ * r₃₁ ≤ C₁ ^ 2 * c := by
    calc η * r₁₂ * r₃₁ ≤ η * (C₁ * ρ) * (C₁ * ρ) := by gcongr
      _ = C₁ ^ 2 * (ρ ^ 2 * η) := by ring
      _ ≤ C₁ ^ 2 * c := mul_le_mul_of_nonneg_left hρ2 (by positivity)
  have hb2 : ι * r₃₁ ≤ C₁ := by
    calc ι * r₃₁ ≤ ι * (C₁ * ρ) := by gcongr
      _ = C₁ * (ρ * ι) := by ring
      _ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left hρι hC₁
      _ = C₁ := mul_one _
  have hbr : 2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr + 4 * Dr ^ 4 ≤
      2 * Dr ^ 2 * (C₁ ^ 2 * c) + 2 * Dr ^ 3 * C₁ + Dr + 4 * Dr ^ 4 := by
    have e : 2 * Dr ^ 2 * η * r₁₂ * r₃₁ = 2 * Dr ^ 2 * (η * r₁₂ * r₃₁) := by ring
    rw [e]
    have h1 : 2 * Dr ^ 2 * (η * r₁₂ * r₃₁) ≤ 2 * Dr ^ 2 * (C₁ ^ 2 * c) :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    have h2 : 2 * Dr ^ 3 * (ι * r₃₁) ≤ 2 * Dr ^ 3 * C₁ :=
      mul_le_mul_of_nonneg_left hb2 (by positivity)
    linarith
  have hP : 0 ≤ e₀ ^ 2 * Ψ₃ := by positivity
  have hcpos : 0 ≤ c := by nlinarith [sq_nonneg ρ, mul_nonneg (sq_nonneg ρ) hη.le]
  calc Dr * r₂₃ * (e₀ ^ 2 * Ψ₃ * (2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr +
        4 * Dr ^ 4)) ≤ Dr * (C₁ * ρ) * (e₀ ^ 2 * Ψ₃ * (2 * Dr ^ 2 * (C₁ ^ 2 * c) +
        2 * Dr ^ 3 * C₁ + Dr + 4 * Dr ^ 4)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h23 (by linarith)) ?_ ?_ ?_
        · exact mul_le_mul_of_nonneg_left hbr hP
        · have : 0 ≤ 2 * Dr ^ 2 * η * r₁₂ * r₃₁ + 2 * Dr ^ 3 * (ι * r₃₁) + Dr + 4 * Dr ^ 4 := by
            positivity
          exact mul_nonneg hP this
        · positivity
    _ = _ := by ring

/-- Rescaling the deterministic matrix in the two-resolvent estimate: the expression is linear in
`B`. -/
private lemma LE_unscale {D N : ℕ} (U Bc : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Fin D → Matrix (Idx D N) (Idx D N) ℂ) (r : Fin D → ℂ) (κ β : ℝ) (hκ : 0 < κ)
    (h : ‖ntr (U * (((κ⁻¹ : ℝ) : ℂ) • Bc)) -
      ∑ x, r x * ntr (V x * (((κ⁻¹ : ℝ) : ℂ) • Bc))‖ ≤ β) :
    ‖ntr (U * Bc) - ∑ x, r x * ntr (V x * Bc)‖ ≤ κ * β := by
  have e : ntr (U * (((κ⁻¹ : ℝ) : ℂ) • Bc)) - ∑ x, r x * ntr (V x * (((κ⁻¹ : ℝ) : ℂ) • Bc)) =
      ((κ⁻¹ : ℝ) : ℂ) * (ntr (U * Bc) - ∑ x, r x * ntr (V x * Bc)) := by
    simp only [Matrix.mul_smul, LE_ntr_smul, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ)] at h
  have := mul_le_mul_of_nonneg_left h hκ.le
  rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at this
  exact this

/-- The core of `lemma_G_large_three`: for `z₃ = z₁`, outside probability `k N^{-(D'+1)}`, every
entry of `L₍₁,₂,₁₎ - K_{θ,(1,2,1)}` is at most `N^{τ'} N⁻¹η⁻³ ρ`, with `ρ = (Im m)⁻¹ ∧ N^{ε_g}`
if `z₁ = z₂` and `ρ = N^{ε_g}` otherwise. -/
private lemma LE_three_core (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) (τ' : ℝ) (hτ' : 0 < τ')
    (D' : ℝ) (hD' : 0 < D') :
    ∃ k : ℕ, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) k (fun h => ∀ a₁ a₂ a₃ : Fin D,
          ‖Lten3 (lam D N A) h z₁ z₂ z₁ a₁ a₂ a₃ - KTheta3 (lam D N A) θ z₁ z₂ z₁ a₁ a₂ a₃‖ ≤
            (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
              (if z₁ = z₂ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
                else (N : ℝ) ^ εg))) := by
  have hD1 : 1 ≤ D := by omega
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hε : 0 < τ' / 4 := by linarith
  have hD'1 : 0 < D' + 1 := by linarith
  obtain ⟨N₁, hN₁pos, hnum⟩ := LE_num D hD1 δA τ εg c hδA hεg hc
  obtain ⟨N₂, h2⟩ := underThree_fluct D hD δA τ εg c hδA hτ hεg hεg' hc C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₃, h3⟩ := LE_aver D hD1 δA τ hδA hτ C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₄, h4⟩ := LE_entprod2 D hD1 δA τ hδA hτ C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₅, h5⟩ := LE_entprod3 D hD1 δA τ hδA hτ C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₆, h6⟩ := lemma_G_large_BB D hD δA τ εg c hδA hτ hεg hεg' hc C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨N₇, h7⟩ := lemma_G_large_two D hD δA τ εg c hδA hτ hεg hεg' hc C (τ' / 4) hε (D' + 1) hD'1
  obtain ⟨C₀, C₁, hC₀, hC₁, N₈, h8⟩ := LE_Rb D hD δA τ εg c hδA hτ hεg hεg' hc
  obtain ⟨N₉, h9⟩ := LE_exists_pow_ge
    ((D : ℝ) * (C₀ * c) *
        (2 * (D : ℝ) ^ 2 * (C₀ * C₁) + 2 * (D : ℝ) ^ 3 * C₁ + D + 4 * (D : ℝ) ^ 4) +
      (D : ℝ) * C₁ * (2 * (D : ℝ) ^ 2 * (C₁ ^ 2 * c) + 2 * (D : ℝ) ^ 3 * C₁ + D + 4 * (D : ℝ) ^ 4))
    (τ' / 2) (by linarith)
  refine ⟨10 * D ^ 4, N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + N₉, by omega,
    fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂ => ?_⟩
  have hN1' : N₁ ≤ N := by omega
  have hN2' : N₂ ≤ N := by omega
  have hN3' : N₃ ≤ N := by omega
  have hN4' : N₄ ≤ N := by omega
  have hN5' : N₅ ≤ N := by omega
  have hN6' : N₆ ≤ N := by omega
  have hN7' : N₇ ≤ N := by omega
  have hN8' : N₈ ≤ N := by omega
  have hN9' : N₉ ≤ N := by omega
  obtain ⟨hℓ, hι0, hι1, hητ, hNηι, hιη⟩ := hnum N hN1' A hA z hz hzim hη hq1 hq2
  have hN1 : 1 ≤ N := hN₁pos.trans hN1'
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hz₁ : z₁ ∈ specDom τ N := LE_mem_specDom hz h₁
  have hz₂ : z₂ ∈ specDom τ N := LE_mem_specDom hz h₂
  have hM₁ : opNorm (MExt (lam D N A) z₁) ≤ 5 / 4 := LE_opNorm_MExt _ hΛ hℓ hzim h₁
  have hM₂ : opNorm (MExt (lam D N A) z₂) ≤ 5 / 4 := LE_opNorm_MExt _ hΛ hℓ hzim h₂
  have hηpos : 0 < z.im := hzim
  set e₀ : ℝ := (N : ℝ) ^ (τ' / 4) with he₀def
  have he₀ : 1 ≤ e₀ := Real.one_le_rpow hNr hε.le
  set η := z.im with hη_def
  set ι := (mExt (lam D N A) z).im with hι_def
  -- the determinants and the norms of `R₁₂`, `R₂₃`, `R₃₁`
  obtain ⟨det12, c12, s12⟩ := h8 N hN8' A hA z hz.1 hzim hq1 hq2 θ hθ0 hθ1 z₁ z₂ h₁ h₂
  obtain ⟨det23, c23, s23⟩ := h8 N hN8' A hA z hz.1 hzim hq1 hq2 θ hθ0 hθ1 z₂ z₁ h₂ h₁
  obtain ⟨det31, c31, s31⟩ := h8 N hN8' A hA z hz.1 hzim hq1 hq2 θ hθ0 hθ1 z₁ z₁ h₁ h₁
  -- the events
  have F1 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))))
      (Fintype.card (Fin D × Fin D × Fin D) * 1)
      (fun h => ∀ p : Fin D × Fin D × Fin D,
        ‖underThree (lam D N A) θ h z₁ z₂ z₁ p.1 p.2.1 p.2.2‖ ≤
          e₀ * ((N : ℝ)⁻¹ * (η ^ 3)⁻¹)) := by
    refine LE_HP.forall (fun p => LE_HP.of_le ?_)
    have := h2 N hN2' θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ z₁ h₁ h₂ h₁ p.1 p.2.1 p.2.2
    simpa only [not_le] using this
  have F2 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D))
      (fun h => ∀ c : Fin D, ∀ z' ∈ specDom τ N,
        ‖ntr ((res (Matrix.of h + lam D N A) z' - MExt (lam D N A) z') * Ea D N c)‖ ≤
        (1 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * |z'.im|)))) :=
    h3 N hN3' θ hθ0 hθ1 μ hμ A hA (Fin D) (fun c => Ea D N c) 1 one_pos
      (fun c => LE_opNorm_Ea D N c)
  have F3 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) (Fintype.card (Fin D × Fin D))
      (fun h => ∀ p : Fin D × Fin D, ∀ z' ∈ specDom τ N,
        ‖ntr ((res (Matrix.of h + lam D N A) z' - MExt (lam D N A) z') *
          (Ea D N p.1 * MExt (lam D N A) z₁ * Ea D N p.2))‖ ≤
        (5 / 4 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * |z'.im|)))) :=
    h3 N hN3' θ hθ0 hθ1 μ hμ A hA (Fin D × Fin D)
      (fun p => Ea D N p.1 * MExt (lam D N A) z₁ * Ea D N p.2) (5 / 4)
      (by norm_num) (fun p => by
        have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N p.1) hM₁
          (LE_opNorm_Ea D N p.2) (by norm_num) (by norm_num)
        simpa using this)
  have F4 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))))
      (Fintype.card (Fin D × Fin D × Fin D) * 1)
      (fun h => ∀ p : Fin D × Fin D × Fin D, (Matrix.of h).IsHermitian →
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N p.1 * res (Matrix.of h + lam D N A) z₂ *
          Ea D N p.2.1 * res (Matrix.of h + lam D N A) z₁ * Ea D N p.2.2)‖ ≤
        1 * 1 * 1 * ((N : ℝ) ^ (τ' / 4) * (ι / η ^ 2))) :=
    LE_HP.forall (fun p => h5 N hN5' θ hθ0 hθ1 μ hμ A hA z hz hzim hNηι z₁ z₂ z₁ h₁ h₂ h₁
      (Ea D N p.1) (Ea D N p.2.1) (Ea D N p.2.2) 1 1 1 one_pos one_pos one_pos
      (LE_opNorm_Ea D N p.1) (LE_opNorm_Ea D N p.2.1) (LE_opNorm_Ea D N p.2.2))
  have F5 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))))
      (Fintype.card (Fin D × Fin D × Fin D × Fin D) * 1)
      (fun h => ∀ q : Fin D × Fin D × Fin D × Fin D, (Matrix.of h).IsHermitian →
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N q.1 * res (Matrix.of h + lam D N A) z₂ *
          (Ea D N q.2.1 * MExt (lam D N A) z₁ * Ea D N q.2.2.2) *
          res (Matrix.of h + lam D N A) z₁ * Ea D N q.2.2.1)‖ ≤
        1 * (5 / 4) * 1 * ((N : ℝ) ^ (τ' / 4) * (ι / η ^ 2))) :=
    LE_HP.forall (fun q => h5 N hN5' θ hθ0 hθ1 μ hμ A hA z hz hzim hNηι z₁ z₂ z₁ h₁ h₂ h₁
      (Ea D N q.1) (Ea D N q.2.1 * MExt (lam D N A) z₁ * Ea D N q.2.2.2) (Ea D N q.2.2.1)
      1 (5 / 4) 1 one_pos (by norm_num) one_pos (LE_opNorm_Ea D N q.1)
      (by
        have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N q.2.1) hM₁
          (LE_opNorm_Ea D N q.2.2.2) (by norm_num) (by norm_num)
        simpa using this) (LE_opNorm_Ea D N q.2.2.1))
  have F6 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))))
      (Fintype.card (Fin D × Fin D × Fin D) * 1)
      (fun h => ∀ p : Fin D × Fin D × Fin D, (Matrix.of h).IsHermitian →
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N p.1 * res (Matrix.of h + lam D N A) z₂ *
          (Ea D N p.2.1 * MExt (lam D N A) z₁ * Ea D N p.2.2))‖ ≤
        1 * (5 / 4) * ((N : ℝ) ^ (τ' / 4) * (ι / η))) :=
    LE_HP.forall (fun p => h4 N hN4' θ hθ0 hθ1 μ hμ A hA z hz hzim hNηι z₁ z₂ h₁ h₂
      (Ea D N p.1) (Ea D N p.2.1 * MExt (lam D N A) z₁ * Ea D N p.2.2) 1 (5 / 4) one_pos
      (by norm_num) (LE_opNorm_Ea D N p.1)
      (by
        have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N p.2.1) hM₁
          (LE_opNorm_Ea D N p.2.2) (by norm_num) (by norm_num)
        simpa using this))
  have F7 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))))
      (Fintype.card (Fin D × Fin D × Fin D) * 1)
      (fun h => ∀ p : Fin D × Fin D × Fin D,
        ‖ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N p.1 * res (Matrix.of h + lam D N A) z₂ *
            ((((5 / 4 : ℝ)⁻¹ : ℝ) : ℂ) • (Ea D N p.2.1 * MExt (lam D N A) z₁ * Ea D N p.2.2))) -
          ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ p.1 x *
            ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ *
              ((((5 / 4 : ℝ)⁻¹ : ℝ) : ℂ) • (Ea D N p.2.1 * MExt (lam D N A) z₁ * Ea D N p.2.2)))‖ ≤
          e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)) := by
    refine LE_HP.forall (fun p => LE_HP.of_le ?_)
    have hBc : opNorm (Ea D N p.2.1 * MExt (lam D N A) z₁ * Ea D N p.2.2) ≤ 5 / 4 := by
      have := LE_opNorm_mul3 _ _ _ 1 (5 / 4) 1 (LE_opNorm_Ea D N p.2.1) hM₁
        (LE_opNorm_Ea D N p.2.2) (by norm_num) (by norm_num)
      simpa using this
    have := (h6 N hN6' θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂
      ((((5 / 4 : ℝ)⁻¹ : ℝ) : ℂ) • (Ea D N p.2.1 * MExt (lam D N A) z₁ * Ea D N p.2.2))
      (LE_scale_le _ _ (by norm_num) hBc) p.1).2
    simpa only [not_le] using this
  have F8 : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) 1
      (fun h => hsNorm (Lmat (lam D N A) h z₁ z₁ - KTheta (lam D N A) θ z₁ z₁) ≤
        e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹)) := by
    refine LE_HP.of_le ?_
    have := (h7 N hN7' θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₁ h₁ h₁).2
    simpa only [not_le] using this
  have hall := (LE_HP.of_ae (ε := ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) hμ.herm).and
    (F1.and (F2.and (F3.and (F4.and (F5.and (F6.and (F7.and F8)))))))
  -- the numerical parameters
  have hη0 : 0 < η := hzim
  have hnD : ‖(D : ℂ)‖ = D := by simp
  refine LE_HP.mono_k (k' := 10 * D ^ 4) ?_ (LE_HP.mono ?_ hall)
  · simp only [Fintype.card_prod, Fintype.card_fin]
    have h1 : D ≤ D * D := Nat.le_mul_self D
    have h2 : D * D ≤ D * D * D := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : D * D * D ≤ D * D * D * D := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : 1 ≤ D * D * D * D := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  intro h hh a₁ a₂ a₃
  obtain ⟨hH, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hh
  have hX : (Matrix.of h + lam D N A).IsHermitian := hH.add hΛ
  have hid := fun a₁ a₂ a₃ => resTriple_aftertrace θ A h hH z₁ z₂ z₁ (LE_im_ne hzim h₁) a₁ a₂ a₃
  have hcyc : ∀ x a : Fin D, Lmat (lam D N A) h z₁ z₁ x a = Lmat (lam D N A) h z₁ z₁ a x := by
    intro x a
    unfold Lmat
    rw [LE_ntr_rot4]
  have hr12 : 0 ≤ opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ := norm_nonneg _
  have hr23 : 0 ≤ opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ := norm_nonneg _
  have hr31 : 0 ≤ opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ := norm_nonneg _
  have hZ : ∀ a₁ a₂ a₃ : Fin D, ‖(D : ℂ) * underThree (lam D N A) θ h z₁ z₂ z₁ a₁ a₂ a₃‖ ≤
      D * (e₀ * ((N : ℝ)⁻¹ * (η ^ 3)⁻¹)) := fun a₁ a₂ a₃ => by
    rw [norm_mul, hnD]
    exact mul_le_mul_of_nonneg_left (b1 (a₁, a₂, a₃)) (by linarith)
  have hU : ∀ c : Fin D, ‖(D : ℂ) * ntr ((res (Matrix.of h + lam D N A) z₁ -
      MExt (lam D N A) z₁) * Ea D N c)‖ ≤ D * (e₀ * (1 / ((N : ℝ) * η))) := fun c => by
    rw [norm_mul, hnD]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := b2 c z₁ hz₁
    rw [LE_abs_im hzim h₁] at this
    refine this.trans (le_of_eq ?_)
    simp only [he₀def, one_mul]
    rfl
  have hV : ∀ a₁ a₂ a₃ x : Fin D, ‖(D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
      res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N x *
      res (Matrix.of h + lam D N A) z₁ * Ea D N a₃)‖ ≤ D * (2 * e₀ * (ι / η ^ 2)) :=
    fun a₁ a₂ a₃ x => by
    rw [norm_mul, hnD]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := b5 (a₁, a₂, a₃, x) hH
    simp only [Matrix.mul_assoc] at this ⊢
    refine this.trans ?_
    have h0 : 0 ≤ e₀ * (ι / η ^ 2) := by positivity
    have e : (1 : ℝ) * (5 / 4) * 1 * ((N : ℝ) ^ (τ' / 4) * (ι / η ^ 2)) =
        (5 / 4) * (e₀ * (ι / η ^ 2)) := by simp only [he₀def]; ring
    rw [e]; linarith
  have hWd : ∀ a c : Fin D, ‖(fun a c : Fin D => (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₂ *
      Ea D N a * MExt (lam D N A) z₁ * Ea D N c)) a c - Mhat (lam D N A) z₂ z₁ a c‖ ≤
      D * (2 * e₀ * (1 / ((N : ℝ) * η))) := fun a c => by
    have e : (fun a c : Fin D => (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N a *
        MExt (lam D N A) z₁ * Ea D N c)) a c - Mhat (lam D N A) z₂ z₁ a c =
        (D : ℂ) * ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) *
          (Ea D N a * MExt (lam D N A) z₁ * Ea D N c)) := by
      simp only [Mhat, Matrix.sub_mul, LE_ntr_sub, mul_assoc, mul_sub]
    rw [e, norm_mul, hnD]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := b3 (a, c) z₂ hz₂
    rw [LE_abs_im hzim h₂] at this
    refine this.trans ?_
    have h0 : 0 ≤ e₀ * (1 / ((N : ℝ) * η)) := by positivity
    have e2 : (5 / 4 : ℝ) * ((N : ℝ) ^ (τ' / 4) * (1 / ((N : ℝ) * η))) =
        (5 / 4) * (e₀ * (1 / ((N : ℝ) * η))) := by simp only [he₀def]
    rw [e2]; linarith
  have hL : ∀ a₁ a₂ a₃ : Fin D, ‖Lten3 (lam D N A) h z₁ z₂ z₁ a₁ a₂ a₃‖ ≤
      D * (e₀ * (ι / η ^ 2)) := fun a₁ a₂ a₃ => by
    unfold Lten3
    rw [norm_mul, hnD]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine (b4 (a₁, a₂, a₃) hH).trans (le_of_eq ?_)
    simp only [he₀def, one_mul]
  have hT : ∀ a₁ a₂ c : Fin D, ‖(D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
      res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c)‖ ≤
      D * (2 * e₀ * (ι / η)) := fun a₁ a₂ c => by
    rw [norm_mul, hnD]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := b6 (a₁, a₂, c) hH
    simp only [Matrix.mul_assoc] at this ⊢
    refine this.trans ?_
    have h0 : 0 ≤ e₀ * (ι / η) := by positivity
    have e : (1 : ℝ) * (5 / 4) * ((N : ℝ) ^ (τ' / 4) * (ι / η)) =
        (5 / 4) * (e₀ * (ι / η)) := by simp only [he₀def]; ring
    rw [e]; linarith
  have hTT : ∀ a₁ a₂ c : Fin D, ‖(D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
      res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c) -
      ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a₁ x *
        ((D : ℂ) * ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * Ea D N a₂ *
          MExt (lam D N A) z₁ * Ea D N c))‖ ≤
      D * (2 * e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)) := fun a₁ a₂ c => by
    have hun := LE_unscale (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
      res (Matrix.of h + lam D N A) z₂)
      (Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c)
      (fun x => MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂)
      (fun x => (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a₁ x) (5 / 4)
      (e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹))
      (by norm_num) (b7 (a₁, a₂, c))
    have e : (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
        res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c) -
        ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a₁ x *
        ((D : ℂ) * ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ * Ea D N a₂ *
          MExt (lam D N A) z₁ * Ea D N c)) =
        (D : ℂ) * (ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
          res (Matrix.of h + lam D N A) z₂ * (Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c)) -
          ∑ x, (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ a₁ x *
          ntr (MExt (lam D N A) z₁ * Ea D N x * MExt (lam D N A) z₂ *
            (Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c))) := by
      simp only [Matrix.mul_assoc, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e, norm_mul, hnD]
    refine mul_le_mul_of_nonneg_left (hun.trans ?_) (by linarith)
    have h0 : 0 ≤ e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ *
        opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹) := by positivity
    linarith
  have hLK : ∀ a x : Fin D, ‖Lmat (lam D N A) h z₁ z₁ a x -
      ((1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ * Mhat (lam D N A) z₁ z₁) a x‖ ≤
      e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹) :=
    fun a x => by
    have := LE_entry_le_hsNorm (Lmat (lam D N A) h z₁ z₁ - KTheta (lam D N A) θ z₁ z₁) a x
    exact this.trans b8
  have hR23 : ∀ a b : Fin D, ‖(1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ a b‖ ≤
      opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ := fun a b => norm_apply_le_opNorm _ a b
  have hR31 : ∀ a b : Fin D, ‖(1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ a b‖ ≤
      opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ := fun a b => norm_apply_le_opNorm _ a b
  have key := LE_three_alg hD1 θ hθ0 hθ1 (Lten3 (lam D N A) h z₁ z₂ z₁)
    (fun a₁ a₂ c => (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
      res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N c))
    (fun a₁ a₂ a₃ => (D : ℂ) * underThree (lam D N A) θ h z₁ z₂ z₁ a₁ a₂ a₃)
    (Lmat (lam D N A) h z₁ z₁) (Lmat (lam D N A) h z₁ z₁) hcyc
    (fun a c => (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N a *
      MExt (lam D N A) z₁ * Ea D N c))
    (Mhat (lam D N A) z₂ z₁) (Mhat (lam D N A) z₁ z₁)
    ((1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)
    (fun c => (D : ℂ) * ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * Ea D N c))
    (fun a₁ a₂ a₃ x => (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
      res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₁ * Ea D N x *
      res (Matrix.of h + lam D N A) z₁ * Ea D N a₃))
    (fun b₁ b₂ b₃ => (D : ℂ) * ntr (MExt (lam D N A) z₁ * Ea D N b₁ * MExt (lam D N A) z₂ *
      Ea D N b₂ * MExt (lam D N A) z₁ * Ea D N b₃))
    det23 det31 hid
    (D * (e₀ * ((N : ℝ)⁻¹ * (η ^ 3)⁻¹))) (D * (e₀ * (1 / ((N : ℝ) * η))))
    (D * (2 * e₀ * (ι / η ^ 2))) (D * (2 * e₀ * (1 / ((N : ℝ) * η))))
    (D * (e₀ * (ι / η ^ 2))) (D * (2 * e₀ * (ι / η)))
    (D * (2 * e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)))
    (e₀ * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹))
    (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹)
    (opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹)
    hZ hU hV hWd hL hT hTT hLK hR23 hR31 a₁ a₂ a₃
  have hbound := LE_S_bound (D : ℝ) e₀ η ι (N : ℝ)
    (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)
    (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹)
    (opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹) hDr he₀ hη0 hι0.le hι1 hN0 hr12 hr23 hr31
  have hmain := key.trans hbound
  have hΨ3 : 0 ≤ (N : ℝ)⁻¹ * (η ^ 3)⁻¹ := by positivity
  have hpow : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have he2 : e₀ ^ 2 = (N : ℝ) ^ (τ' / 2) := by
    rw [he₀def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hX0 : 0 ≤ (N : ℝ) ^ εg := Real.rpow_nonneg hN0.le _
  have hKA : 0 ≤ (D : ℝ) * (C₀ * c) * (2 * (D : ℝ) ^ 2 * (C₀ * C₁) + 2 * (D : ℝ) ^ 3 * C₁ + D +
      4 * (D : ℝ) ^ 4) := by
    have : 0 < c := by linarith
    positivity
  have hKB : 0 ≤ (D : ℝ) * C₁ * (2 * (D : ℝ) ^ 2 * (C₁ ^ 2 * c) + 2 * (D : ℝ) ^ 3 * C₁ + D +
      4 * (D : ℝ) ^ 4) := by
    have : 0 < c := by linarith
    positivity
  have hKN := h9 N hN9'
  by_cases hz12 : z₁ = z₂
  · -- all three equal: row L5
    rw [ite_eq_left hz12]
    have hρ0 : 0 ≤ min ι⁻¹ ((N : ℝ) ^ εg) := le_min (inv_nonneg.mpr hι0.le) hX0
    have hρι : min ι⁻¹ ((N : ℝ) ^ εg) * ι ≤ 1 := by
      calc min ι⁻¹ ((N : ℝ) ^ εg) * ι ≤ ι⁻¹ * ι :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hι0.le
        _ = 1 := inv_mul_cancel₀ hι0.ne'
    have hρ2 : min ι⁻¹ ((N : ℝ) ^ εg) ^ 2 * η ≤ c := by
      have h1 : min ι⁻¹ ((N : ℝ) ^ εg) ^ 2 ≤ ι⁻¹ * (N : ℝ) ^ εg := by
        rw [sq]
        exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hρ0 (inv_nonneg.mpr hι0.le)
      have h2 : η / ι ≤ c * (N : ℝ) ^ (-εg) := hq2
      have h3 : (N : ℝ) ^ (-εg) * (N : ℝ) ^ εg = 1 := by
        rw [← Real.rpow_add hN0]; simp
      calc min ι⁻¹ ((N : ℝ) ^ εg) ^ 2 * η ≤ ι⁻¹ * (N : ℝ) ^ εg * η :=
            mul_le_mul_of_nonneg_right h1 hη0.le
        _ = (η / ι) * (N : ℝ) ^ εg := by field_simp
        _ ≤ c * (N : ℝ) ^ (-εg) * (N : ℝ) ^ εg := mul_le_mul_of_nonneg_right h2 hX0
        _ = c := by rw [mul_assoc, h3, mul_one]
    have hc4 := LE_caseB (D : ℝ) e₀ η ι ((N : ℝ)⁻¹ * (η ^ 3)⁻¹) (min ι⁻¹ ((N : ℝ) ^ εg)) c C₁
      (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)
      (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹)
      (opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹) hDr he₀ hη0 hι0 hΨ3 hρ0 hC₁.le
      hr12 hr31 (s12 hz12.symm) (s23 hz12) (s31 rfl) hρι hρ2
    calc _ ≤ _ := hmain
      _ ≤ _ := hc4
      _ ≤ (N : ℝ) ^ (τ' / 2) * (e₀ ^ 2 * ((N : ℝ)⁻¹ * (η ^ 3)⁻¹) * min ι⁻¹ ((N : ℝ) ^ εg)) := by
        exact mul_le_mul_of_nonneg_right (le_trans (le_add_of_nonneg_left hKA) hKN)
          (mul_nonneg (mul_nonneg (sq_nonneg _) hΨ3) hρ0)
      _ = _ := by rw [he2, hpow]; ring
  · -- not all equal: row L4
    rw [ite_eq_right hz12]
    have hz2 : z₂ = star z₁ := by
      rcases h₁ with e1 | e1 <;> rcases h₂ with e2 | e2
      · exact absurd (e1.trans e2.symm) hz12
      · rw [e2, e1]
      · rw [e2, e1, star_star]
      · exact absurd (e1.trans e2.symm) hz12
    have hz1 : z₁ = star z₂ := by rw [hz2, star_star]
    have h31 : opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ ≤ C₁ * ι⁻¹ :=
      (s31 rfl).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC₁.le)
    have hc4 := LE_caseA (D : ℝ) e₀ η ι ((N : ℝ)⁻¹ * (η ^ 3)⁻¹) ((N : ℝ) ^ εg) c C₀ C₁
      (opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹)
      (opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹)
      (opNorm (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹) hDr he₀ hη0 hι0 hΨ3 (by linarith)
      hC₀.le hr12 hr31 (c12 hz2) (c23 hz1) h31 hιη
    calc _ ≤ _ := hmain
      _ ≤ _ := hc4
      _ ≤ (N : ℝ) ^ (τ' / 2) * (e₀ ^ 2 * ((N : ℝ)⁻¹ * (η ^ 3)⁻¹) * (N : ℝ) ^ εg) := by
        exact mul_le_mul_of_nonneg_right (le_trans (le_add_of_nonneg_right hKB) hKN)
          (mul_nonneg (mul_nonneg (sq_nonneg _) hΨ3) hX0)
      _ = _ := by rw [he2, hpow]; ring

/-- Entrywise bounds for the rotated tensors give entrywise bounds for the original ones. -/
private lemma LE_rot_entry {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ)
    (h : Idx D N → Idx D N → ℂ) (z₁ z₂ z₃ : ℂ) (β : ℝ)
    (H : ∀ b₁ b₂ b₃ : Fin D, ‖Lten3 Λ h z₂ z₃ z₁ b₁ b₂ b₃ - KTheta3 Λ θ z₂ z₃ z₁ b₁ b₂ b₃‖ ≤ β) :
    ∀ a₁ a₂ a₃ : Fin D, ‖Lten3 Λ h z₁ z₂ z₃ a₁ a₂ a₃ - KTheta3 Λ θ z₁ z₂ z₃ a₁ a₂ a₃‖ ≤ β := by
  intro a₁ a₂ a₃
  rw [LE_Lten3_rot Λ h z₁ z₂ z₃, LE_KTheta3_rot Λ θ z₁ z₂ z₃]
  exact H a₂ a₃ a₁

/-- For `p = q ∧ q = p` and `p = q` the same branch is taken. -/
private lemma LE_if_and_symm (p q : ℂ) (X Y : ℝ) :
    (if p = q ∧ q = p then X else Y) = (if p = q then X else Y) :=
  if_congr ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩ rfl rfl

/-- (3.21) [largG_3G_1] and (3.22) [largG_3G_2] of Lemma 3.6 [lemma_G_large] for the class,
uniformly in `θ ∈ [0, 1]`, with `K_θ`: `‖L₍₁,₂,₃₎ - K_θ₍₁,₂,₃₎‖₂ ≤ N^{τ'} N^{-1} η^{-3} N^{ε_g}`
when `z₁, z₂, z₃` are not all equal, and with `(Im m)⁻¹ ∧ N^{ε_g}` in place of `N^{ε_g}` when
they are equal, outside probability `N^{-D'}`. -/
theorem lemma_G_large_three (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) →
        μ {h | (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
            (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
              else (N : ℝ) ^ εg)) <
          ten3Norm (Lten3 (lam D N A) h z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  have hD1 : 1 ≤ D := by omega
  obtain ⟨k, N₀, hN₀pos, hcore⟩ := LE_three_core D hD δA τ εg c hδA hτ hεg hεg' hc C (τ' / 2)
    (by linarith) D' hD'
  obtain ⟨N₁, h1⟩ := LE_exists_pow_ge ((D : ℝ) ^ 2) (τ' / 2) (by linarith)
  refine ⟨N₀ + k + N₁, fun N hN θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 z₁ z₂ z₃ h₁ h₂ h₃ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hent : LE_HP μ (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1)))) k (fun h => ∀ a₁ a₂ a₃ : Fin D,
      ‖Lten3 (lam D N A) h z₁ z₂ z₃ a₁ a₂ a₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃ a₁ a₂ a₃‖ ≤
        (N : ℝ) ^ (τ' / 2) * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
          (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
            else (N : ℝ) ^ εg))) := by
    by_cases h3 : z₃ = z₁
    · subst h3
      have hc := hcore N (by omega) θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 _ _ h₁ h₂
      refine LE_HP.mono (fun h hh a₁ a₂ a₃ => ?_) hc
      refine (hh a₁ a₂ a₃).trans (le_of_eq ?_)
      rw [LE_if_and_symm]
    · by_cases hz12 : z₁ = z₂
      · subst hz12
        have hc := hcore N (by omega) θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 _ _ h₂ h₃
        refine LE_HP.mono (fun h hh => LE_rot_entry _ _ _ _ _ _ _ fun b₁ b₂ b₃ => ?_) hc
        refine (hh b₁ b₂ b₃).trans (le_of_eq ?_)
        rw [ite_eq_right (fun e => h3 e.symm), ite_eq_right (fun e => h3 e.2.symm)]
      · have hz23 : z₂ = z₃ := by
          rcases h₁ with e1 | e1 <;> rcases h₂ with e2 | e2 <;> rcases h₃ with e3 | e3
          all_goals first
            | exact e2.trans e3.symm
            | exact absurd (e1.trans e2.symm) hz12
            | exact absurd (e3.trans e1.symm) h3
        subst hz23
        have hc := hcore N (by omega) θ hθ0 hθ1 μ hμ A hA z hz hzim hη hq1 hq2 _ _ h₃ h₁
        refine LE_HP.mono (fun h hh => LE_rot_entry _ _ _ _ _ _ _ fun b₁ b₂ b₃ =>
          LE_rot_entry _ _ _ _ _ _ _ (fun c₁ c₂ c₃ => ?_) b₁ b₂ b₃) hc
        refine (hh c₁ c₂ c₃).trans (le_of_eq ?_)
        rw [ite_eq_right (fun e => h3 e), ite_eq_right (fun e => hz12 e.1)]
  have hcount := LE_count N k hN1 (by omega) D' _ hent
  refine le_trans (measure_mono ?_) hcount
  intro h hh
  simp only [Set.mem_ofPred_eq] at hh ⊢
  intro hall
  refine absurd hh (not_lt.mpr ?_)
  have hβ : 0 ≤ (N : ℝ) ^ (τ' / 2) * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
      (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
        else (N : ℝ) ^ εg)) :=
    (norm_nonneg _).trans (hall ⟨0, hD1⟩ ⟨0, hD1⟩ ⟨0, hD1⟩)
  have hpow : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  calc ten3Norm (Lten3 (lam D N A) h z₁ z₂ z₃ - KTheta3 (lam D N A) θ z₁ z₂ z₃) ≤
        (D : ℝ) ^ 2 * ((N : ℝ) ^ (τ' / 2) * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
          (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
            else (N : ℝ) ^ εg))) := LE_ten3Norm_le hD1 _ _ hβ hall
    _ ≤ (N : ℝ) ^ (τ' / 2) * ((N : ℝ) ^ (τ' / 2) * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹ *
          (if z₁ = z₂ ∧ z₂ = z₃ then min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg)
            else (N : ℝ) ^ εg))) := mul_le_mul_of_nonneg_right (h1 N (by omega)) hβ
    _ = _ := by rw [hpow]; ring

end RBMTransitionEdge

end
