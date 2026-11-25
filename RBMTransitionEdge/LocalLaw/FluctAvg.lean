module

public import RBMTransitionEdge.LocalLaw.FluctIso
public import RBMTransitionEdge.LocalLaw.FluctAvgQSI
public import RBMTransitionEdge.LocalLaw.FluctAvgMom

@[expose] public section

/-!
# The averaged fluctuation bounds

The averaged high-moment and `≺` bounds for `⟨B H̲G⟩` of (2.30) [eq:HGline] (fluctuation
averaging) behind Lemma 2.9 [lem_loc], with an a priori bound up to `N^{δ₀}` on spectral sets that
may grow with `N`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Norms of the vectors and of the interaction -/

open scoped Matrix.Norms.L2Operator in
/-- `|T u|² ≤ ‖T‖² |u|²`. -/
private lemma FA_mulVec_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (u : ι → ℂ) : ∑ k, ‖(T *ᵥ u) k‖ ^ 2 ≤ opNorm T ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec T (WithLp.toLp 2 u)
  have h1 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have h2 : ‖(EuclideanSpace.equiv ι ℂ).symm (T *ᵥ (WithLp.toLp 2 u).ofLp)‖ ^ 2 =
      ∑ k, ‖(T *ᵥ u) k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h3 : ‖(EuclideanSpace.equiv ι ℂ).symm (T *ᵥ (WithLp.toLp 2 u).ofLp)‖ ^ 2 ≤
      (‖T‖ * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [h2, mul_pow, h1] at h3
  exact h3

open scoped Matrix.Norms.L2Operator in
/-- `‖T^*‖ = ‖T‖`. -/
private lemma FA_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) : opNorm Tᴴ = opNorm T := by
  change ‖Tᴴ‖ = ‖T‖
  exact Matrix.l2_opNorm_conjTranspose T


/-- The vectors of `avgVecs` have norm `≤ 1` for `‖Λ‖ ≤ 1/10` and `‖B‖ ≤ 1`. -/
private lemma FA_avgVecs_norm {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛn : opNorm Λ ≤ 1 / 10) (hB : opNorm B ≤ 1) : ∀ x ∈ avgVecs D N Λ B, ∑ r, ‖x r‖ ^ 2 ≤ 1 := by
  have he : ∀ p : Idx D N, ∑ r, ‖(Pi.single p (1 : ℂ) : Idx D N → ℂ) r‖ ^ 2 = 1 := fun p => by
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hT : ∀ (T : Matrix (Idx D N) (Idx D N) ℂ), opNorm T ≤ 1 → ∀ p : Idx D N,
      ∑ r, ‖(T *ᵥ Pi.single p 1) r‖ ^ 2 ≤ 1 := fun T hT p => by
    refine (FA_mulVec_sq T _).trans ?_
    rw [he p, mul_one]
    have := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) T)
    have h0 : 0 ≤ opNorm T := this
    nlinarith
  intro x hx
  unfold avgVecs at hx
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · rw [he p]
  · exact hT B hB p
  · exact hT Bᴴ (by rw [FA_opNorm_conjTranspose]; exact hB) p
  · exact hT Λ (hΛn.trans (by norm_num)) p

/-- `|avgVecs| ≤ 4DN`. -/
private lemma FA_card_avgVecs (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) :
    ((avgVecs D N Λ B).card : ℝ) ≤ 4 * ((D : ℝ) * N) := by
  have h : (avgVecs D N Λ B).card ≤ 4 * (D * N) := by
    unfold avgVecs
    have e : ∀ f : Idx D N → Idx D N → ℂ, (Finset.univ.image f).card ≤ D * N := fun f =>
      (Finset.card_image_le).trans (by simp)
    have h1 := Finset.card_union_le
      (Finset.univ.image (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun k => B *ᵥ Pi.single k 1) ∪
        Finset.univ.image (fun k => Bᴴ *ᵥ Pi.single k 1))
      (Finset.univ.image (fun k => Λ *ᵥ Pi.single k 1))
    have h2 := Finset.card_union_le
      (Finset.univ.image (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun k => B *ᵥ Pi.single k 1))
      (Finset.univ.image (fun k => Bᴴ *ᵥ Pi.single k 1))
    have h3 := Finset.card_union_le
      (Finset.univ.image (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)))
      (Finset.univ.image (fun k => B *ᵥ Pi.single k 1))
    have := e (fun k => Pi.single k 1); have := e (fun k => B *ᵥ Pi.single k 1)
    have := e (fun k => Bᴴ *ᵥ Pi.single k 1); have := e (fun k => Λ *ᵥ Pi.single k 1)
    omega
  exact_mod_cast h

section FA_Lam

open scoped Matrix.Norms.L2Operator

/-- The embedding `J_a` of `ℂ^N` as the block `a` of `Idx D N`. -/
private def FA_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

/-- `J_a^* J_a = 1`. -/
private lemma FA_J_conj_mul (D N : ℕ) (a : Fin D) :
    (FA_J D N a)ᴴ * FA_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, FA_J, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `‖J_a‖ ≤ 1`. -/
private lemma FA_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) :
    ‖FA_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (FA_J D N a)
  rw [FA_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖FA_J D N a‖ := norm_nonneg _
  nlinarith

/-- `‖J_a M J_b^*‖ ≤ ‖M‖`. -/
private lemma FA_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖FA_J D N a * M * (FA_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := FA_J_norm D N hN a
  have hb := FA_J_norm D N hN b
  calc ‖FA_J D N a * M * (FA_J D N b)ᴴ‖
      ≤ ‖FA_J D N a * M‖ * ‖(FA_J D N b)ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖FA_J D N a‖ * ‖M‖) * ‖(FA_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

/-- The entries of the block embedding `J_a M J_b^*`. -/
private lemma FA_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (FA_J D N a * M * (FA_J D N b)ᴴ) p q =
      if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, FA_J, Prod.ext_iff, h1, h2]

/-- `Λ` as the sum of the embedded blocks `A` and `A^*`. -/
private lemma FA_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then FA_J D N a * A * (FA_J D N b)ᴴ else 0) +
        (if fwd D b a then FA_J D N a * Aᴴ * (FA_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D,
      (if fwd D a b then FA_J D N a * A * (FA_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, FA_block_apply]
  have e2 : ∀ a b : Fin D,
      (if fwd D b a then FA_J D N a * Aᴴ * (FA_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, FA_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖Λ‖ ≤ 2 D² ‖A‖` for the interaction `Λ = lam D N A` of (1.3) [matrix_H]. -/
private lemma FA_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [FA_lam_eq]
  have hb : ∀ a b : Fin D,
      ‖(if fwd D a b then FA_J D N a * A * (FA_J D N b)ᴴ else 0) +
      (if fwd D b a then FA_J D N a * Aᴴ * (FA_J D N b)ᴴ else 0)‖ ≤
        2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then FA_J D N a * A * (FA_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact FA_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then FA_J D N a * Aᴴ * (FA_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact (FA_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end FA_Lam

/-! ### Integrability of the moments of `⟨B H̲G⟩` -/

/-- `H̲G = 1 - (Λ - z) M + S_θ(M) M` for a matrix `M` in place of `G` ((2.30) [eq:HGline] with
`H G = 1 - (Λ - z) G`). -/
private def FA_hg (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (M : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M + sTheta D N θ M * M

/-- `M ↦ ⟨M⟩` is continuous. -/
private lemma FA_ntr_cont {ι : Type*} [Fintype ι] :
    Continuous (fun M : Matrix ι ι ℂ => ntr M) := by
  unfold ntr
  exact continuous_const.mul (Continuous.matrix_trace continuous_id)

/-- `R ↦ S_θ(R)` is continuous. -/
private lemma FA_sTheta_cont (D N : ℕ) (θ : ℝ) :
    Continuous (fun M : Matrix (Idx D N) (Idx D N) ℂ => sTheta D N θ M) := by
  have h1 : Continuous fun M : Matrix (Idx D N) (Idx D N) ℂ =>
      ∑ a : Fin D, ((D : ℂ) * ntr (M * Ea D N a)) • Ea D N a := by
    refine continuous_finsetSum _ fun a _ => ?_
    exact (continuous_const.mul
      (FA_ntr_cont.comp (continuous_id.matrix_mul continuous_const))).smul continuous_const
  have h2 : Continuous fun M : Matrix (Idx D N) (Idx D N) ℂ =>
      ntr M • (1 : Matrix (Idx D N) (Idx D N) ℂ) := FA_ntr_cont.smul continuous_const
  unfold sTheta
  exact (h1.const_smul (θ : ℂ)).add (h2.const_smul ((1 - θ : ℝ) : ℂ))

/-- `M ↦ H̲G` of `FA_hg` is continuous. -/
private lemma FA_hg_cont (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    Continuous (FA_hg D N θ Λ z) := by
  unfold FA_hg
  exact (continuous_const.sub (continuous_const.matrix_mul continuous_id)).add
    ((FA_sTheta_cont D N θ).matrix_mul continuous_id)

/-- On Hermitian arrays `H̲G` of (2.30) [eq:HGline] is `FA_hg` at `G = (h + Λ - z)⁻¹`. -/
private lemma FA_hg_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    hgUnder D N θ (Matrix.of h) Λ z = FA_hg D N θ Λ z (res (Matrix.of h + Λ) z) := by
  have hres := (res_mul_sub (Matrix.of h + Λ) (hh.add hΛ) z hz).1
  have hHG : Matrix.of h * res (Matrix.of h + Λ) z =
      1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z := by
    have : Matrix.of h * res (Matrix.of h + Λ) z =
        (Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z -
          (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z := by
      rw [← Matrix.sub_mul]
      congr 1
      abel
    rw [this, hres]
  unfold hgUnder FA_hg
  rw [hHG]

/-- A continuous function of the resolvent `G = (h + Λ - z)⁻¹` is a.e. strongly measurable and
a.e. bounded for a law of Hermitian arrays: `|G_{kl}| ≤ η⁻¹` confines `G` to a compact set. -/
private lemma FA_bdd {D N : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (Idx D N → Idx D N → ℂ))
    (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (Φ : Matrix (Idx D N) (Idx D N) ℂ → E)
    (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun h => Φ (res (Matrix.of h + Λ) z)) μ ∧
      ∃ B : ℝ, ∀ᵐ h ∂μ, ‖Φ (res (Matrix.of h + Λ) z)‖ ≤ B := by
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
  refine ⟨hm, B, ?_⟩
  filter_upwards [hherm] with h hh
  refine hB _ fun k _ l _ => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_apply_le_opNorm _ k l).trans (opNorm_res_le _ (hh.add hΛ) z hz)

/-- The moments `‖⟨B H̲G⟩‖^q` are integrable for a finite law of Hermitian arrays. -/
private lemma FA_pow_int {D N : ℕ} (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    [IsFiniteMeasure μ] (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (q : ℕ) :
    Integrable (fun h => ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ q) μ := by
  obtain ⟨hm, B', hB'⟩ := FA_bdd μ hherm Λ hΛ z hz
    (fun M => ‖ntr (B * FA_hg D N θ Λ z M)‖ ^ q)
    (((FA_ntr_cont.comp (continuous_const.matrix_mul (FA_hg_cont D N θ Λ z))).norm).pow q)
  refine (Integrable.of_bound hm B' hB').congr ?_
  filter_upwards [hherm] with h hh
  simp only [FA_hg_eq D N θ Λ hΛ z hz h hh]

/-! ### Young's inequality and the closing arithmetic -/

/-- `y^{m-n} ≤ a^{m-n} + a^{-n} y^m` for `y ≥ 0`, `a > 0`, `n ≤ m`. -/
private lemma FA_split_pow {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) {n m : ℕ} (hnm : n ≤ m) :
    y ^ (m - n) ≤ a ^ (m - n) + (a ^ n)⁻¹ * y ^ m := by
  rcases le_or_gt y a with h | h
  · have h1 : y ^ (m - n) ≤ a ^ (m - n) := pow_le_pow_left₀ hy h _
    have h2 : 0 ≤ (a ^ n)⁻¹ * y ^ m := by positivity
    linarith
  · have han : 0 < a ^ n := pow_pos ha n
    have h1 : a ^ n ≤ y ^ n := pow_le_pow_left₀ ha.le h.le n
    have h2 : y ^ (m - n) * a ^ n ≤ y ^ m := by
      calc y ^ (m - n) * a ^ n ≤ y ^ (m - n) * y ^ n := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = y ^ m := by rw [← pow_add, Nat.sub_add_cancel hnm]
    have h3 : y ^ (m - n) ≤ (a ^ n)⁻¹ * y ^ m := by
      rw [le_inv_mul_iff₀ han, mul_comm]
      exact h2
    have h4 : 0 ≤ a ^ (m - n) := by positivity
    linarith

/-- Young's inequality for the moments of a nonnegative variable: if
`E|f|^{2p} ≤ K Σ_{n=1}^{2p} ϑ^n E|f|^{2p-n} + K R` for a probability measure, then
`E|f|^{2p} ≤ (8 p max(K, 1) ϑ)^{2p} + 2 K R`. -/
private lemma FA_young {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) (hint : ∀ q : ℕ, Integrable (fun ω => f ω ^ q) μ)
    (p : ℕ) (hp : 1 ≤ p) (K ϑ R : ℝ) (hK : 0 ≤ K) (hϑ : 0 ≤ ϑ) (hR : 0 ≤ R)
    (h : ∫ ω, f ω ^ (2 * p) ∂μ ≤ K * (∑ n ∈ Finset.Icc 1 (2 * p),
      ϑ ^ n * ∫ ω, f ω ^ (2 * p - n) ∂μ) + K * R) :
    ∫ ω, f ω ^ (2 * p) ∂μ ≤ (8 * p * max K 1 * ϑ) ^ (2 * p) + 2 * (K * R) := by
  set E : ℝ := ∫ ω, f ω ^ (2 * p) ∂μ with hE
  have hE0 : 0 ≤ E := integral_nonneg fun ω => pow_nonneg (hf0 ω) _
  have hK' : 1 ≤ max K 1 := le_max_right _ _
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hrest : 0 ≤ (8 * p * max K 1 * ϑ) ^ (2 * p) + 2 * (K * R) := by positivity
  rcases hE0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hrest
  set x : ℝ := E ^ ((1 : ℝ) / (2 * p : ℕ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hpos _
  have hxE : x ^ (2 * p) = E := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    have : (2 * p : ℕ) ≠ 0 := by omega
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast this), Real.rpow_one]
  have hEn : ∀ n ∈ Finset.Icc 1 (2 * p), ∫ ω, f ω ^ (2 * p - n) ∂μ ≤ 2 * x ^ (2 * p - n) := by
    intro n hn
    have hn2 : n ≤ 2 * p := (Finset.mem_Icc.mp hn).2
    have hI := integral_mono_of_nonneg (μ := μ) (f := fun ω => f ω ^ (2 * p - n))
      (Eventually.of_forall fun ω => pow_nonneg (hf0 ω) _)
      ((integrable_const (x ^ (2 * p - n))).add ((hint (2 * p)).const_mul (x ^ n)⁻¹))
      (Eventually.of_forall fun ω => FA_split_pow (hf0 ω) hx0 hn2)
    simp only [Pi.add_apply] at hI
    rw [integral_add (integrable_const _) ((hint (2 * p)).const_mul _), integral_const,
      integral_const_mul, probReal_univ, one_smul] at hI
    have e : (x ^ n)⁻¹ * ∫ ω, f ω ^ (2 * p) ∂μ = x ^ (2 * p - n) := by
      rw [← hE, ← hxE, pow_sub₀ _ hx0.ne' hn2, mul_comm]
    rw [e] at hI
    linarith
  set K' : ℝ := max K 1 with hK'def
  set b : ℕ → ℝ := fun n => if n = 0 then 0 else 2 * K * ϑ ^ n with hb
  have hbn : ∀ n, b n ≤ (2 * K' * ϑ) ^ n := by
    intro n
    by_cases hn : n = 0
    · simp [hb, hn]
    · simp only [hb, hn, ite_false]
      rw [mul_pow, mul_pow]
      have h1 : 2 * K ≤ (2 * K') ^ n := by
        have : 2 * K ≤ 2 * K' := by have := le_max_left K 1; linarith
        exact this.trans (le_self_pow₀ (by linarith) hn)
      calc 2 * K * ϑ ^ n ≤ (2 * K') ^ n * ϑ ^ n :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg hϑ n)
        _ = _ := by ring
  have hsum : E ≤ (∑ n ∈ Finset.Icc 1 (2 * p), b n * x ^ (2 * p - n)) + K * R := by
    refine h.trans ?_
    have : K * (∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n * ∫ ω, f ω ^ (2 * p - n) ∂μ) ≤
        ∑ n ∈ Finset.Icc 1 (2 * p), b n * x ^ (2 * p - n) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      simp only [hb, hn0, ite_false]
      calc K * (ϑ ^ n * ∫ ω, f ω ^ (2 * p - n) ∂μ) ≤ K * (ϑ ^ n * (2 * x ^ (2 * p - n))) := by
            gcongr
            exact hEn n hn
        _ = 2 * K * ϑ ^ n * x ^ (2 * p - n) := by ring
    linarith
  have hy := young_moment p hp x (2 * K' * ϑ) (K * R) b hx0.le (by positivity) hbn
    (by rw [hxE]; exact hsum)
  rw [hxE] at hy
  calc E ≤ (4 * p * (2 * K' * ϑ)) ^ (2 * p) + 2 * (K * R) := hy
    _ = (8 * p * max K 1 * ϑ) ^ (2 * p) + 2 * (K * R) := by
        rw [show 4 * (p : ℝ) * (2 * K' * ϑ) = 8 * p * max K 1 * ϑ by rw [hK'def]; ring]

/-- The real-number closing of the averaged moment bound: the main term `(8 p max(K, 1) ϑ)^{2p}`
with `ϑ ≤ 22 n^{17ε/40} Y` and the remainder `2 K R` with `R ≤ (1 + 5D) n^{-(2p+1)}` add up to at
most `(n^ε Y)^{2p}` once `n` is large, for `Y ≥ (2n)⁻¹`. -/
private lemma FA_arith (p : ℕ) (hp : 1 ≤ p) (Ka Dd n ε Y ϑ R₀ : ℝ) (hKa : 0 ≤ Ka) (hD : 1 ≤ Dd)
    (hn : 1 ≤ n) (hε : 0 < ε) (hY : (2 * n)⁻¹ ≤ Y) (hϑ0 : 0 ≤ ϑ)
    (hϑ : ϑ ≤ 22 * n ^ (17 * ε / 40) * Y) (hR : R₀ ≤ (1 + 5 * Dd) * n ^ (-(2 * (p : ℝ) + 1)))
    (hc1 : 352 * p * max Ka 1 ≤ n ^ (23 * ε / 40)) (hc2 : 12 * 4 ^ p * Ka * (1 + 5 * Dd) ≤ n) :
    (8 * p * max Ka 1 * ϑ) ^ (2 * p) + 2 * (Ka * R₀) ≤ (n ^ ε * Y) ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set K' := max Ka 1 with hK'
  have hK1 : 1 ≤ K' := le_max_right _ _
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have hnε : 1 ≤ n ^ ε := Real.one_le_rpow hn hε.le
  set W := n ^ ε * Y with hW
  have hW0 : 0 < W := by positivity
  have hsplit : n ^ ε = n ^ (17 * ε / 40) * n ^ (23 * ε / 40) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have h1 : 8 * p * K' * ϑ ≤ W / 2 := by
    have hq0 : 0 ≤ n ^ (17 * ε / 40) := Real.rpow_nonneg hn0.le _
    calc 8 * p * K' * ϑ ≤ 8 * p * K' * (22 * n ^ (17 * ε / 40) * Y) := by gcongr
      _ = (176 * p * K') * n ^ (17 * ε / 40) * Y := by ring
      _ ≤ (n ^ (23 * ε / 40) / 2) * n ^ (17 * ε / 40) * Y := by gcongr; linarith
      _ = W / 2 := by rw [hW, hsplit]; ring
  have h2 : (8 * p * K' * ϑ) ^ (2 * p) ≤ (W / 2) ^ (2 * p) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (W / 2) ^ (2 * p) ≤ W ^ (2 * p) / 4 := by
    rw [div_pow]
    have : (4 : ℝ) ≤ 2 ^ (2 * p) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hWp : 0 ≤ W ^ (2 * p) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hYW : Y ≤ W := by
    rw [hW]; nlinarith
  have hWlow : ((2 * n) ^ (2 * p))⁻¹ ≤ W ^ (2 * p) := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (hY.trans hYW) _
  have hnr : n ^ (-(2 * (p : ℝ) + 1)) = ((n ^ (2 * p)) * n)⁻¹ := by
    rw [Real.rpow_neg hn0.le, show (2 * (p : ℝ) + 1) = ((2 * p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_succ]
  have h4 : 2 * (Ka * R₀) ≤ 3 / 4 * ((2 * n) ^ (2 * p))⁻¹ := by
    have ha0 : 0 < n ^ (2 * p) := pow_pos hn0 _
    have e1 : (2 * n) ^ (2 * p) = 4 ^ p * n ^ (2 * p) := by
      rw [mul_pow, pow_mul]; norm_num
    have h5 : 2 * (Ka * R₀) ≤ 2 * Ka * ((1 + 5 * Dd) * ((n ^ (2 * p)) * n)⁻¹) := by
      rw [← hnr]; nlinarith
    refine h5.trans ?_
    rw [e1]
    have h4p : (0 : ℝ) < 4 ^ p := by positivity
    rw [show 2 * Ka * ((1 + 5 * Dd) * ((n ^ (2 * p)) * n)⁻¹) =
      (2 * Ka * (1 + 5 * Dd)) / ((n ^ (2 * p)) * n) by field_simp,
      show 3 / 4 * (4 ^ p * n ^ (2 * p))⁻¹ = 3 / (4 * (4 ^ p * n ^ (2 * p))) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * Ka * (1 + 5 * Dd) * (4 * (4 ^ p * n ^ (2 * p))) =
        (8 * 4 ^ p * Ka * (1 + 5 * Dd)) * n ^ (2 * p) := by ring
    rw [this]
    have h6 : 8 * 4 ^ p * Ka * (1 + 5 * Dd) ≤ 3 * n := by
      have : 0 ≤ 4 ^ p * Ka * (1 + 5 * Dd) := by positivity
      nlinarith
    calc (8 * 4 ^ p * Ka * (1 + 5 * Dd)) * n ^ (2 * p) ≤ (3 * n) * n ^ (2 * p) :=
          mul_le_mul_of_nonneg_right h6 ha0.le
      _ = 3 * (n ^ (2 * p) * n) := by ring
  have hWp : 0 ≤ W ^ (2 * p) := by positivity
  nlinarith [h2, h3, h4, hWlow]

/-! ### The control `Y` and the coefficient `ϑ` -/

/-- `Ψ_φ² ≥ (Im m + φ)/(Nη)`. -/
private lemma FA_psi_sq_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ)
    (z : ℂ) (φ : ℝ) (hN : 0 < (N : ℝ)) (hz : 0 < z.im) (hm : 0 ≤ (mExt Λ z).im + φ) :
    ((mExt Λ z).im + φ) / ((N : ℝ) * z.im) ≤ psiPhi Λ N z φ ^ 2 := by
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hN hz
  unfold psiPhi
  have h0 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
  have h1 := Real.sq_sqrt (div_nonneg hm hNη.le)
  nlinarith [Real.sqrt_nonneg (((mExt Λ z).im + φ) / ((N : ℝ) * z.im))]

/-- `Ψ_φ > 0`. -/
private lemma FA_psi_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ)
    (z : ℂ) (φ : ℝ) (hN : 0 < (N : ℝ)) (hz : 0 < z.im) :
    0 < psiPhi Λ N z φ := by
  unfold psiPhi
  have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  have := Real.sqrt_nonneg (((mExt Λ z).im + φ) / ((N : ℝ) * z.im))
  linarith

/-- The control `(1 + |z|)^{20} (1 + φ)⁶ Ψ_φ²` is at least `(2N)⁻¹` for `‖Λ‖ ≤ 1/10`, from
`Ψ_φ² ≥ Im m/(Nη)` and `η ≤ (11/10 + |z|)² Im m`. -/
private lemma FA_Y_lower (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (z : ℂ) (hz : 0 < z.im) (φ : ℝ) (hφ : 0 ≤ φ) :
    ((2 : ℝ) * N)⁻¹ ≤ (1 + ‖z‖) ^ 20 * (1 + φ) ^ 6 * psiPhi Λ N z φ ^ 2 := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hme : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  have hI : 0 < (mSol Λ z).im := (mSol_spec Λ hΛ z hz).1
  have hz0 : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    rintro rfl
    simp at hz
  have hlow := (im_mSol_lower Λ hΛ hΛn ‖z‖⁻¹ (inv_pos.mpr hz0) z hz (by rw [inv_inv])).1
  rw [inv_inv] at hlow
  set m := (mSol Λ z).im with hmdef
  set η := z.im with hη
  set t := ‖z‖ with ht
  set P := psiPhi Λ N z φ ^ 2 with hP
  have hu : 1 ≤ 1 + t := by linarith
  have hη' : η ≤ 121 / 100 * (1 + t) ^ 2 * m := by
    refine hlow.trans ?_
    have : (11 / 10 + t) ^ 2 ≤ 121 / 100 * (1 + t) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hI.le
  have hNη : 0 < (N : ℝ) * η := mul_pos hN0 hz
  have hPg : (m + φ) / ((N : ℝ) * η) ≤ P := by
    have := FA_psi_sq_ge Λ N z φ hN0 hz (by rw [hme]; linarith)
    rwa [hme] at this
  have h1 : m ≤ P * ((N : ℝ) * η) := by
    have : m / ((N : ℝ) * η) ≤ P :=
      (div_le_div_of_nonneg_right (by linarith) hNη.le).trans hPg
    rwa [div_le_iff₀ hNη] at this
  have h2 : P * ((N : ℝ) * η) ≤ P * ((N : ℝ) * (121 / 100 * (1 + t) ^ 2 * m)) := by
    have hP0 : 0 ≤ P := by positivity
    gcongr
  have h3 : 1 ≤ P * (N : ℝ) * (121 / 100 * (1 + t) ^ 2) := by
    have h4 : 1 * m ≤ (P * (N : ℝ) * (121 / 100 * (1 + t) ^ 2)) * m := by
      calc 1 * m = m := one_mul m
        _ ≤ P * ((N : ℝ) * η) := h1
        _ ≤ P * ((N : ℝ) * (121 / 100 * (1 + t) ^ 2 * m)) := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_right h4 hI
  have hP0 : 0 ≤ P := by positivity
  have h5 : (1 + t) ^ 2 ≤ (1 + t) ^ 20 * (1 + φ) ^ 6 := by
    have a1 : (1 + t) ^ 2 ≤ (1 + t) ^ 20 := pow_le_pow_right₀ hu (by norm_num)
    have a2 : 1 ≤ (1 + φ) ^ 6 := one_le_pow₀ (by linarith)
    calc (1 + t) ^ 2 ≤ (1 + t) ^ 20 := a1
      _ = (1 + t) ^ 20 * 1 := (mul_one _).symm
      _ ≤ (1 + t) ^ 20 * (1 + φ) ^ 6 :=
          mul_le_mul_of_nonneg_left a2 (pow_nonneg (by linarith) 20)
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have h6 : (1 + t) ^ 2 * P * N ≤ ((1 + t) ^ 20 * (1 + φ) ^ 6 * P) * N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 hP0) hN0.le
  have e : P * (N : ℝ) * (121 / 100 * (1 + t) ^ 2) = 121 / 100 * ((1 + t) ^ 2 * P * N) := by ring
  rw [e] at h3
  generalize ((1 + t) ^ 20 * (1 + φ) ^ 6 * P) = Yv at h6 ⊢
  generalize ((1 + t) ^ 2 * P * N) = Qv at h3 h6
  linarith

/-- The size of the coefficient `ϑ = a (1 + |z|)² Γ⁶ Υ/(Nη)` of the averaged moment inequality:
with `Γ = 5/4 + u φ`, `u, v ≥ 1`, and `X ≤ (144/25)(1 + t)² u Ψ²` it is at most
`22 v u⁷ (1 + t)⁴ (1 + φ)⁶ Ψ²`. -/
private lemma FA_theta_le (t φ u v X Ψsq : ℝ) (ht : 0 ≤ t) (hφ : 0 ≤ φ) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hX0 : 0 ≤ X) (hX : X ≤ 144 / 25 * (1 + t) ^ 2 * u * Ψsq) (hΨ : 0 ≤ Ψsq) :
    v * (1 + t) ^ 2 * (5 / 4 + u * φ) ^ 6 * X ≤
      22 * (v * u ^ 7) * ((1 + t) ^ 4 * ((1 + φ) ^ 6 * Ψsq)) := by
  have hΓ : 5 / 4 + u * φ ≤ 5 / 4 * u * (1 + φ) := by nlinarith
  have hΓ6 : (5 / 4 + u * φ) ^ 6 ≤ (5 / 4 * u * (1 + φ)) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hΓ 6
  have h1 : v * (1 + t) ^ 2 * (5 / 4 + u * φ) ^ 6 * X ≤
      v * (1 + t) ^ 2 * (5 / 4 * u * (1 + φ)) ^ 6 * (144 / 25 * (1 + t) ^ 2 * u * Ψsq) := by
    have : 0 ≤ v * (1 + t) ^ 2 := by positivity
    gcongr
  calc _ ≤ _ := h1
    _ = ((5 / 4) ^ 6 * (144 / 25)) * (v * u ^ 7) * ((1 + t) ^ 4 * ((1 + φ) ^ 6 * Ψsq)) := by ring
    _ ≤ 22 * (v * u ^ 7) * ((1 + t) ^ 4 * ((1 + φ) ^ 6 * Ψsq)) := by
      gcongr
      norm_num

/-- The good event `avgGood` fails with probability at most `17 D² N² N^{-D''}`: the a priori bound
on the vectors `avgVecs` (at most `4DN` of them) and the bound on each of the `(DN)²` entries of
`Q`. -/
private lemma FA_event {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (θ : ℝ)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (Γ Υ bQ D'' : ℝ)
    (hg : μ (goodSet Λ z (avgVecs D N Λ B) Γ Υ)ᶜ ≤
      ENNReal.ofReal (((avgVecs D N Λ B).card : ℝ) ^ 2 * (N : ℝ) ^ (-D'')))
    (hq : ∀ k l : Idx D N, μ {h | bQ < ‖qMat D N θ (Matrix.of h) Λ B z k l‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D''))) :
    μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ≤
      ENNReal.ofReal (17 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-D'')) := by
  have hNd : 0 ≤ (N : ℝ) ^ (-D'') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ⊆
      (goodSet Λ z (avgVecs D N Λ B) Γ Υ)ᶜ ∪
      ⋃ kl : Idx D N × Idx D N, {h | bQ < ‖qMat D N θ (Matrix.of h) Λ B z kl.1 kl.2‖} := by
    intro h hh
    by_cases h1 : h ∈ goodSet Λ z (avgVecs D N Λ B) Γ Υ
    · right
      have h2 : ¬ ∀ k' l', ‖qMat D N θ (Matrix.of h) Λ B z k' l'‖ ≤ bQ := fun h2 => hh ⟨h1, h2⟩
      push Not at h2
      obtain ⟨k', l', hlt⟩ := h2
      exact Set.mem_iUnion.2 ⟨(k', l'), hlt⟩
    · left; exact h1
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hU : μ (⋃ kl : Idx D N × Idx D N, {h | bQ < ‖qMat D N θ (Matrix.of h) Λ B z kl.1 kl.2‖}) ≤
      ENNReal.ofReal (((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'')) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun kl _ => hq kl.1 kl.2).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hNd)]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  refine (add_le_add hg hU).trans ?_
  have hn1 : 0 ≤ ((avgVecs D N Λ B).card : ℝ) ^ 2 * (N : ℝ) ^ (-D'') := by positivity
  have hn2 : 0 ≤ ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'') := by positivity
  rw [← ENNReal.ofReal_add hn1 hn2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard := FA_card_avgVecs D N Λ B
  have hc2 : ((avgVecs D N Λ B).card : ℝ) ^ 2 ≤ 16 * ((D : ℝ) * N) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((avgVecs D N Λ B).card : ℝ) := Nat.cast_nonneg _
    calc ((avgVecs D N Λ B).card : ℝ) ^ 2 ≤ (4 * ((D : ℝ) * N)) ^ 2 := pow_le_pow_left₀ h0 hcard 2
      _ = 16 * ((D : ℝ) * N) ^ 2 := by ring
  have h3 := mul_le_mul_of_nonneg_right hc2 hNd
  have e : 17 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-D'') =
      16 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'') + ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'') := by ring
  rw [e]
  exact add_le_add h3 le_rfl

/-! ### Parameters and the a priori bound -/

/-- The remainder of the averaged moment inequality with `ε₀ = 17 D² N² N^{-D''}` and
`D'' = 52 p + 40`: `N^{-(2p+1)} + N^{21p+18} ε₀^{1/2} ≤ (1 + 5D) N^{-(2p+1)}`. -/
private lemma FA_rem (p : ℕ) (hp : 1 ≤ p) (Dd n D'' : ℝ) (hD : 0 ≤ Dd) (hn : 1 ≤ n)
    (hD'' : D'' = 52 * (p : ℝ) + 40) :
    n ^ (-(2 * (p : ℝ) + 1)) + n ^ (21 * (p : ℝ) + 18) *
        Real.sqrt (17 * Dd ^ 2 * n ^ 2 * n ^ (-D'')) ≤ (1 + 5 * Dd) * n ^ (-(2 * (p : ℝ) + 1)) := by
  have hn0 : 0 < n := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set q : ℝ := n ^ (-(26 * (p : ℝ) + 19)) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hn0.le _
  have hqq : q ^ 2 = n ^ 2 * n ^ (-D'') := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_natCast n 2,
      ← Real.rpow_add hn0, hD'']
    congr 1
    push_cast
    ring
  have h1 : 17 * Dd ^ 2 * n ^ 2 * n ^ (-D'') ≤ (5 * Dd * q) ^ 2 := by
    have : (5 * Dd * q) ^ 2 = 25 * Dd ^ 2 * (n ^ 2 * n ^ (-D'')) := by
      rw [mul_pow, mul_pow, hqq]; ring
    rw [this]
    have : 0 ≤ Dd ^ 2 * (n ^ 2 * n ^ (-D'')) := by positivity
    nlinarith
  have h2 : Real.sqrt (17 * Dd ^ 2 * n ^ 2 * n ^ (-D'')) ≤ 5 * Dd * q := by
    calc _ ≤ Real.sqrt ((5 * Dd * q) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 5 * Dd * q := Real.sqrt_sq (by positivity)
  have h3 : n ^ (21 * (p : ℝ) + 18) * (5 * Dd * q) = 5 * Dd * n ^ (-(5 * (p : ℝ) + 1)) := by
    rw [hq, show n ^ (21 * (p : ℝ) + 18) * (5 * Dd * n ^ (-(26 * (p : ℝ) + 19))) =
      5 * Dd * (n ^ (21 * (p : ℝ) + 18) * n ^ (-(26 * (p : ℝ) + 19))) by ring, ← Real.rpow_add hn0]
    congr 2
    ring
  have h4 : n ^ (-(5 * (p : ℝ) + 1)) ≤ n ^ (-(2 * (p : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  calc n ^ (-(2 * (p : ℝ) + 1)) + n ^ (21 * (p : ℝ) + 18) *
        Real.sqrt (17 * Dd ^ 2 * n ^ 2 * n ^ (-D'')) ≤
      n ^ (-(2 * (p : ℝ) + 1)) + n ^ (21 * (p : ℝ) + 18) * (5 * Dd * q) := by
        gcongr
    _ = n ^ (-(2 * (p : ℝ) + 1)) + 5 * Dd * n ^ (-(5 * (p : ℝ) + 1)) := by rw [h3]
    _ ≤ n ^ (-(2 * (p : ℝ) + 1)) + 5 * Dd * n ^ (-(2 * (p : ℝ) + 1)) := by gcongr
    _ = (1 + 5 * Dd) * n ^ (-(2 * (p : ℝ) + 1)) := by ring

/-- `N^a ≥ C` for all large `N`, when `a > 0`. -/
private lemma FA_ev_le (C a : ℝ) (ha : 0 < a) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop C)

/-- The a priori bound restricted to the points of positive imaginary part. -/
private lemma FA_apriori_restrict {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)}
    {A : ∀ N, Matrix (Fin N) (Fin N) ℂ} {Z : ℕ → Set ℂ} {φ : ℕ → ℂ → ℝ}
    (hLL : aprioriLL D μ A Z φ) : aprioriLL D μ A (fun N => {z | z ∈ Z N ∧ 0 < z.im}) φ := by
  intro τ hτ D' hD'
  obtain ⟨N₀, hN₀⟩ := hLL τ hτ D' hD'
  refine ⟨N₀, fun N hN u => ?_⟩
  obtain ⟨⟨z, hz⟩, r⟩ := u
  exact hN₀ N hN ⟨⟨z, hz.1⟩, r⟩

/-- The averaged high-moment bound (fluctuation averaging) with a priori bound up to `N^{δ₀}` on
spectral sets that may grow with `N`, under `LLSeq`, `K δ₀ ≤ τ` and `aprioriLL`:
`E|⟨B H̲G⟩|^{2p} ≤ (N^ε (1 + |z|)^{2K} (1 + φ)⁶ Ψ_φ²)^{2p}` for deterministic `‖B‖ ≤ 1`. -/
theorem fluct_avg_moment' : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → K * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ →
    ∀ (p : ℕ) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
        ∫ h, ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖ ^ (2 * p) ∂(μ N) ≤
          ((N : ℝ) ^ ε * ((1 + ‖z‖) ^ (2 * K) * (1 + φ N z) ^ 6 *
            psiPhi (lam D N (A N)) N z (φ N z) ^ 2)) ^ (2 * p) := by
  refine ⟨10, by norm_num, ?_⟩
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL p ε hε
  have hprob : ∀ N, IsProbabilityMeasure (μ N) := fun N => (hseq.mem N).prob
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨0, fun N _ z _ B _ => by simp⟩
  have hD1 : 1 ≤ D := hseq.one_le_D
  by_cases hδ9 : δ₀ ≤ 1 / 9
  swap
  · refine ⟨2, fun N hN z hzZ B hB => ?_⟩
    exfalso
    have h1 := hZ N z hzZ
    have h2 : (N : ℝ) ^ (-1 + τ) ≤ (N : ℝ) ^ δ₀ :=
      h1.2.trans ((Complex.im_le_norm z).trans h1.1)
    rw [Real.rpow_le_rpow_left_iff (by exact_mod_cast (by omega : 1 < N))] at h2
    linarith
  obtain ⟨Ka, hKa0, hKa⟩ := avg_moment_ineq D p hp C
  set ε₂ : ℝ := ε / 4 with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  set ε₁ := min (ε / 40) (min (τ / 20) (1 / 36)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hε₁a : ε₁ ≤ ε / 40 := min_le_left _ _
  have hε₁b : ε₁ ≤ τ / 20 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁c : ε₁ ≤ 1 / 36 := (min_le_right _ _).trans (min_le_right _ _)
  clear_value ε₁ ε₂
  set D'' : ℝ := 52 * (p : ℝ) + 40 with hD''
  have hD''0 : 0 < D'' := by positivity
  obtain ⟨N₁, hN₁⟩ := apriori_good D δA C θ μ A hseq (fun N => {z | z ∈ Z N ∧ 0 < z.im})
    (fun N z hz => hz.2) φ (FA_apriori_restrict hLL) ε₁ D'' hε₁0 hD''0
  obtain ⟨N₂, hN₂⟩ := q_prec D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL ε₂ hε₂0 D'' hD''0
  obtain ⟨N₃, hN₃⟩ := FA_ev_le 2 (1 / 36) (by norm_num)
  obtain ⟨N₄, hN₄⟩ := FA_ev_le 6 (τ / 2) (by positivity)
  obtain ⟨N₅, hN₅⟩ := FA_ev_le (20 * (D : ℝ) ^ 2) δA hseq.pos
  obtain ⟨N₆, hN₆⟩ := FA_ev_le (352 * p * max Ka 1) (23 * ε / 40) (by positivity)
  obtain ⟨N₇, hN₇⟩ := FA_ev_le (12 * 4 ^ p * Ka * (1 + 5 * (D : ℝ))) 1 one_pos
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ 2)),
    fun N hN z hzZ B hB => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hN3, hN4⟩, ⟨hN5, hN6⟩, hN7, hN8⟩ := hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr0 : (0 : ℝ) < N := by linarith
  obtain ⟨hzn0, hzim0⟩ := hZ N z hzZ
  have hz : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hzim0
  have hΛ : (lam D N (A N)).IsHermitian := lam_isHermitian D N (A N)
  have hΛn : opNorm (lam D N (A N)) ≤ 1 / 10 := by
    have h1 := FA_opNorm_lam D N (by omega) (A N)
    have h2 := hseq.small N
    have h3 := hN₅ N hN5
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have hD0 : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
    have hpos : 0 < (N : ℝ) ^ δA := Real.rpow_pos_of_pos hNr0 _
    calc opNorm (lam D N (A N)) ≤ 2 * (D : ℝ) ^ 2 * opNorm (A N) := h1
      _ ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) := by gcongr
      _ ≤ 1 / 10 := by
        rw [Real.rpow_neg hNr0.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
        linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, by omega⟩)⟩
  have hmS := mSol_spec (lam D N (A N)) hΛ z hz
  have hmA := mSol_apriori (lam D N (A N)) hΛ hΛn z hz
  have hme : mExt (lam D N (A N)) z = mSol (lam D N (A N)) z := by simp [mExt, hz]
  have him0 : 0 ≤ (mExt (lam D N (A N)) z).im := by rw [hme]; exact hmS.1.le
  have him1 : (mExt (lam D N (A N)) z).im ≤ 1 := by
    rw [hme]; exact (Complex.im_le_norm _).trans hmA.2.1.le
  obtain ⟨hφ1, hφ2⟩ := hφ N z hzZ
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) hφ1
  have hNε1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hNr1 hε₁0.le
  have hNφ : (N : ℝ) ^ ε₁ * φ N z ≤ (N : ℝ) ^ (δ₀ + ε₁) := by
    rw [Real.rpow_add hNr0, mul_comm ((N : ℝ) ^ δ₀)]
    exact mul_le_mul_of_nonneg_left hφ2 (by positivity)
  have hδε : δ₀ + ε₁ ≤ τ / 2 := by linarith
  -- the hypotheses of the moment inequality
  have hzN : ((N : ℝ))⁻¹ ≤ z.im := by
    rw [← Real.rpow_neg_one]
    exact (Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)).trans hzim0
  have hzn : ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) :=
    hzn0.trans (Real.rpow_le_rpow_of_exponent_le hNr1 hδ9)
  have hΓ1 : 1 ≤ 5 / 4 + (N : ℝ) ^ ε₁ * φ N z := by
    have : 0 ≤ (N : ℝ) ^ ε₁ * φ N z := by positivity
    linarith
  have hΓN : 5 / 4 + (N : ℝ) ^ ε₁ * φ N z ≤ (N : ℝ) ^ ((1 : ℝ) / 6) := by
    have a1 : (N : ℝ) ^ (δ₀ + ε₁) ≤ (N : ℝ) ^ ((5 : ℝ) / 36) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
    have a2 : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 36) := hN₃ N hN3
    have a3 : (N : ℝ) ^ ((1 : ℝ) / 36) ≤ (N : ℝ) ^ ((5 : ℝ) / 36) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
    have a4 : (N : ℝ) ^ ((1 : ℝ) / 6) = (N : ℝ) ^ ((5 : ℝ) / 36) * (N : ℝ) ^ ((1 : ℝ) / 36) := by
      rw [← Real.rpow_add hNr0]; norm_num
    have a5 : (N : ℝ) ^ ((5 : ℝ) / 36) * 2 ≤ (N : ℝ) ^ ((5 : ℝ) / 36) * (N : ℝ) ^ ((1 : ℝ) / 36) :=
      mul_le_mul_of_nonneg_left a2 (Real.rpow_nonneg hNr0.le _)
    rw [a4]; linarith
  have hΥ1 : z.im ≤ 41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
      (N : ℝ) ^ ε₁ * φ N z := by
    have : 0 ≤ (N : ℝ) ^ ε₁ * φ N z := by positivity
    linarith
  have hΥ2 : 41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
      (N : ℝ) ^ ε₁ * φ N z ≤ (N : ℝ) * z.im := by
    have b1 : z.im ≤ (N : ℝ) ^ (δ₀ + ε₁) := (Complex.im_le_norm z).trans
      (hzn0.trans (Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)))
    have b2 : 1 ≤ (N : ℝ) ^ (δ₀ + ε₁) := Real.one_le_rpow hNr1 (by positivity)
    have b3 : (N : ℝ) ^ (δ₀ + ε₁) ≤ (N : ℝ) ^ (τ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 hδε
    have b4 : 6 ≤ (N : ℝ) ^ (τ / 2) := hN₄ N hN4
    have b5 : (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
      have : (N : ℝ) ^ τ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := by
        rw [← Real.rpow_one_add' hNr0.le (by linarith)]; ring_nf
      rw [this]; exact mul_le_mul_of_nonneg_left hzim0 hNr0.le
    have b6 : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hNr0]; ring_nf
    have b7 : 6 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
      mul_le_mul_of_nonneg_right b4 (Real.rpow_nonneg hNr0.le _)
    linarith
  -- the control, the coefficient and the bad event
  set u : ℝ := (N : ℝ) ^ ε₁ with hu
  set v : ℝ := (N : ℝ) ^ ε₂ with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hNr1 hε₂0.le
  have hv0 : 0 ≤ v := by linarith
  set Ψ := psiPhi (lam D N (A N)) N z (φ N z) with hΨ
  set Γ : ℝ := 5 / 4 + u * φ N z with hΓ
  set Υ : ℝ := 41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + u * φ N z with hΥ
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hNr0 hz
  have hX0 : 0 ≤ Υ / ((N : ℝ) * z.im) := div_nonneg (by linarith) hNη.le
  have hzp := zeta_le_psi D N hD1 (by omega) (lam D N (A N)) hΛ hΛn z hz (φ N z) u hφ0 hNε1
  have hS : ((mExt (lam D N (A N)) z).im + φ N z) / ((N : ℝ) * z.im) ≤ Ψ ^ 2 :=
    FA_psi_sq_ge _ N z (φ N z) hNr0 hz (by linarith)
  have hS0 : 0 ≤ ((mExt (lam D N (A N)) z).im + φ N z) / ((N : ℝ) * z.im) :=
    div_nonneg (by linarith) hNη.le
  have hXs : Υ / ((N : ℝ) * z.im) ≤ 144 / 25 * (1 + ‖z‖) ^ 2 * u * Ψ ^ 2 := by
    calc Υ / ((N : ℝ) * z.im) = Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 2 := (Real.sq_sqrt hX0).symm
      _ ≤ (12 / 5 * (1 + ‖z‖) * Real.sqrt u * Real.sqrt (((mExt (lam D N (A N)) z).im +
          φ N z) / ((N : ℝ) * z.im))) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hzp 2
      _ = 144 / 25 * (1 + ‖z‖) ^ 2 * u * (((mExt (lam D N (A N)) z).im + φ N z) /
          ((N : ℝ) * z.im)) := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hS0]; ring
      _ ≤ 144 / 25 * (1 + ‖z‖) ^ 2 * u * Ψ ^ 2 := by gcongr
  have hϑ := FA_theta_le ‖z‖ (φ N z) u v _ (Ψ ^ 2) (norm_nonneg z) hφ0 hNε1 hv1 hX0 hXs
    (by positivity)
  have hvu : v * u ^ 7 ≤ (N : ℝ) ^ (17 * ε / 40) := by
    have e : v * u ^ 7 = (N : ℝ) ^ (ε₂ + 7 * ε₁) := by
      rw [hv, hu, ← Real.rpow_natCast, ← Real.rpow_mul hNr0.le, ← Real.rpow_add hNr0]
      congr 1; push_cast; ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hϑY : v * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im)) ≤
      22 * (N : ℝ) ^ (17 * ε / 40) * ((1 + ‖z‖) ^ 20 * (1 + φ N z) ^ 6 * Ψ ^ 2) := by
    refine hϑ.trans ?_
    have h4 : (1 + ‖z‖) ^ 4 ≤ (1 + ‖z‖) ^ 20 :=
      pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by norm_num)
    have hq0 : 0 ≤ (1 + φ N z) ^ 6 * Ψ ^ 2 := by positivity
    calc 22 * (v * u ^ 7) * ((1 + ‖z‖) ^ 4 * ((1 + φ N z) ^ 6 * Ψ ^ 2)) ≤
        22 * (N : ℝ) ^ (17 * ε / 40) * ((1 + ‖z‖) ^ 20 * ((1 + φ N z) ^ 6 * Ψ ^ 2)) := by gcongr
      _ = _ := by ring
  have hϑ0 : 0 ≤ v * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im)) := by positivity
  set W : ℝ := (1 + ‖z‖) ^ 2 * (1 + φ N z) ^ 4 *
    Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ^ 3 with hW
  have hbQ : v * W ≤ v * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3) := by
    have h1 : 1 + φ N z ≤ Γ := by
      change 1 + φ N z ≤ 5 / 4 + u * φ N z
      linarith [mul_nonneg (sub_nonneg.mpr hNε1) hφ0]
    have h2 : (mExt (lam D N (A N)) z).im + φ N z + z.im ≤ Υ := by
      change (mExt (lam D N (A N)) z).im + φ N z + z.im ≤ 41 / 16 * z.im +
        25 / 16 * (mExt (lam D N (A N)) z).im + u * φ N z
      linarith [mul_nonneg (sub_nonneg.mpr hNε1) hφ0, him0, hz]
    have h3 : Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ≤
        Real.sqrt (Υ / ((N : ℝ) * z.im)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h2 hNη.le)
    rw [hW]
    gcongr
  have hq : ∀ k l : Idx D N, μ N {h | v * W <
      ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) B z k l‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D'')) := fun k l => hN₂ N hN2 (⟨z, hzZ⟩, ⟨B, hB⟩, k, l)
  have hg := hN₁ N hN1 z ⟨hzZ, hz⟩ (avgVecs D N (lam D N (A N)) B)
    (FA_avgVecs_norm _ B hΛn hB)
  have hbad := FA_event (μ N) (θ N) (lam D N (A N)) B z Γ Υ (v * W) D'' hg hq
  have hmom := hKa N (θ N) (μ N) (hseq.mem N) (hseq.theta N).1 (hseq.theta N).2 _ hΛ hΛn B hB z
    hzN hzn Γ Υ v (v * W) _ hΓ1 hΓN hΥ1 hΥ2 hv1 hbQ hbad
  -- Young's inequality and the closing arithmetic
  have := hprob N
  have hR0 : 0 ≤ (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) + (N : ℝ) ^ (21 * (p : ℝ) + 18) *
      Real.sqrt (17 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-D'')) := by positivity
  have hyoung := FA_young (μ N)
    (fun h => ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖)
    (fun _ => norm_nonneg _)
    (fun q => FA_pow_int (θ N) (μ N) (hseq.mem N).herm _ hΛ z hz B q) p hp Ka _ _ hKa0 hϑ0 hR0
    hmom
  have hRle := FA_rem p hp (D : ℝ) (N : ℝ) D'' (by positivity) hNr1 hD''
  have hc1 := hN₆ N hN6
  have hc2 := hN₇ N hN7
  rw [Real.rpow_one] at hc2
  have hfin := FA_arith p hp Ka (D : ℝ) (N : ℝ) ε ((1 + ‖z‖) ^ 20 * (1 + φ N z) ^ 6 * Ψ ^ 2) _ _
    hKa0 (by exact_mod_cast hD1) hNr1 hε
    (FA_Y_lower D N hD1 (by omega) _ hΛ hΛn z hz (φ N z) hφ0) hϑ0 hϑY hRle hc1 hc2
  have e20 : (1 + ‖z‖) ^ (2 * (10 : ℝ)) = (1 + ‖z‖) ^ 20 := by
    rw [show (2 * (10 : ℝ)) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e20]
  exact hyoung.trans hfin


/-- `⟨B H̲G⟩ ≺ (1 + |z|)^{2K} (1 + φ)⁶ Ψ_φ²` in sup form over `z ∈ Z_N` and deterministic
`‖B‖ ≤ 1`, under `LLSeq`, `K δ₀ ≤ τ` and `aprioriLL`. -/
theorem fluct_avg_prec' : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → K * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ →
    PrecS μ (U := fun N => {z // z ∈ Z N} × {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
      (fun N w h => ‖ntr (w.2.1 * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1)‖)
      (fun N w _ => (1 + ‖w.1.1‖) ^ (2 * K) * (1 + φ N w.1.1) ^ 6 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2) := by
  obtain ⟨K, hK1, hK⟩ := fluct_avg_moment'
  refine ⟨K, hK1, ?_⟩
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL τ' hτ' D' hD'
  have hD1 : 1 ≤ D := hseq.one_le_D
  set p : ℕ := ⌈D' / τ'⌉₊ + 1 with hpdef
  have hp : 1 ≤ p := by omega
  have hpτ : D' ≤ p * τ' := by
    have h1 : D' / τ' ≤ ⌈D' / τ'⌉₊ := Nat.le_ceil _
    have h2 : (⌈D' / τ'⌉₊ : ℝ) ≤ p := by rw [hpdef]; push_cast; linarith
    rw [div_le_iff₀ hτ'] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hτ'.le)
  clear_value p
  obtain ⟨N₀, hN₀⟩ := hK D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL p (τ' / 2) (by positivity)
  refine ⟨max N₀ 1, fun N hN w => ?_⟩
  obtain ⟨⟨z, hzZ⟩, ⟨B, hB⟩⟩ := w
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNr0 : (0 : ℝ) < N := by linarith
  obtain ⟨-, hzim0⟩ := hZ N z hzZ
  have hz : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hzim0
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) (hφ N z hzZ).1
  have hΛ : (lam D N (A N)).IsHermitian := lam_isHermitian D N (A N)
  have hprob : IsProbabilityMeasure (μ N) := (hseq.mem N).prob
  have hmom := hN₀ N hN0 z hzZ B hB
  set Y : ℝ := (1 + ‖z‖) ^ (2 * K) * (1 + φ N z) ^ 6 *
    psiPhi (lam D N (A N)) N z (φ N z) ^ 2 with hY
  have hΨ := FA_psi_pos (lam D N (A N)) N z (φ N z) hNr0 hz
  have hK0 : 0 ≤ 2 * K := by linarith
  have hY0 : 0 < Y := by
    have h1 : 0 < (1 + ‖z‖) ^ (2 * K) := Real.rpow_pos_of_pos (by positivity) _
    have h2 : 0 < (1 + φ N z) ^ 6 := pow_pos (by linarith) 6
    positivity
  set a : ℝ := (N : ℝ) ^ (τ' / 2) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hNr0 _
  have hNτ : (N : ℝ) ^ τ' = a * a := by
    rw [ha, ← Real.rpow_add hNr0]; ring_nf
  set s : ℝ := (N : ℝ) ^ τ' * Y with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs2 : 0 < s ^ (2 * p) := pow_pos hs0 _
  have hint := FA_pow_int (θ N) (μ N) (hseq.mem N).herm _ hΛ z hz B (2 * p)
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := μ N)
    (f := fun h => ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖ ^ (2 * p))
    (Eventually.of_forall fun h => by positivity) hint (s ^ (2 * p))
  have hsub : {ω | (N : ℝ) ^ τ' * Y <
      ‖ntr (B * hgUnder D N (θ N) (Matrix.of ω) (lam D N (A N)) z)‖} ⊆
      {h | s ^ (2 * p) ≤
        ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖ ^ (2 * p)} :=
    fun h hh => pow_le_pow_left₀ hs0.le (le_of_lt hh) _
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (μ N).real {h | s ^ (2 * p) ≤
      ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖ ^ (2 * p)} ≤
      (s ^ (2 * p))⁻¹ * ∫ h, ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖ ^
        (2 * p) ∂(μ N) := by
    rw [le_inv_mul_iff₀ hs2]
    exact hmk
  refine h1.trans ?_
  have key : ∀ a Y : ℝ, 0 < a → 0 < Y →
      ((a * a * Y) ^ (2 * p))⁻¹ * (a * Y) ^ (2 * p) = (a ^ (2 * p))⁻¹ := by
    intro a Y ha hY
    rw [← inv_pow, ← mul_pow, ← inv_pow]
    congr 1
    field_simp
  have h2 : (s ^ (2 * p))⁻¹ * ((N : ℝ) ^ (τ' / 2) * Y) ^ (2 * p) = (a ^ (2 * p))⁻¹ := by
    rw [hs, hNτ, ← ha]
    exact key a Y ha0 hY0
  have h3 : (a ^ (2 * p))⁻¹ ≤ (N : ℝ) ^ (-D') := by
    have e : a ^ (2 * p) = (N : ℝ) ^ (τ' * p) := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]
      congr 1; push_cast; ring
    rw [e, Real.rpow_neg hNr0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hNr0 _)
      (Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith))
  calc (s ^ (2 * p))⁻¹ * ∫ h, ‖ntr (B * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z)‖ ^
        (2 * p) ∂(μ N) ≤ (s ^ (2 * p))⁻¹ * ((N : ℝ) ^ (τ' / 2) * Y) ^ (2 * p) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)
    _ ≤ _ := by rw [h2]; exact h3

end RBMTransitionEdge

end
