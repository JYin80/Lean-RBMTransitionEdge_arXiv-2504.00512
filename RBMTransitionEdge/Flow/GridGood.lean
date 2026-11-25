module

public import RBMTransitionEdge.Flow.LargeEtaId
public import RBMTransitionEdge.Flow.TOp
public import RBMTransitionEdge.Prob.GridA
public import RBMTransitionEdge.Prob.GridAFlow

@[expose] public section

/-!
# The good event along the flow on the grid

The event on which the averaged local law (2.23) [eq:aver_local] and the bounds (A.53) [entprodG]
hold at the flowed spectral parameter, and its probability at all times of one grid, as used in
Lemmas 3.8–3.11.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The good event at flow time `s` for the state `H`, with the loss `N^{τ'}`: the averaged local
law (2.23) [eq:aver_local] for `E_a` at `z_s`, the bounds (A.53) [entprodG] for the products of
at most eight resolvents `G(z_s)` or `G(z_s)^* = G(z̄_s)` with factors `E_a`, and `|H_{ij}| ≤ 1`. -/
def flowGoodAt {D N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (τ' s : ℝ)
    (H : Idx D N → Idx D N → ℂ) : Prop :=
  (∀ a : Fin D, ‖ntr ((res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
      (charFlowZ (lam D N A) z s) - MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
        (charFlowZ (lam D N A) z s)) * Ea D N a)‖ ≤
      (N : ℝ) ^ τ' / (N * (charFlowZ (lam D N A) z s).im)) ∧
    (∀ p : ℕ, 1 ≤ p → p ≤ 8 → ∀ (b : Fin p → Bool) (a : Fin p → Fin D),
      ‖ntr (resProd (fun _ => res (Matrix.of H + ((Real.exp (-s / 2) : ℝ) : ℂ) • lam D N A)
          (charFlowZ (lam D N A) z s)) b (fun i => Ea D N (a i)))‖ ≤
        (N : ℝ) ^ τ' * bndA4 (fun _ : Fin p => flowIm (lam D N A) z s)
          (fun _ : Fin p => (charFlowZ (lam D N A) z s).im) p) ∧
    ∀ i j, ‖H i j‖ ≤ 1



/-- `t • lam D N A = lam D N (t • A)` for real `t`. -/
private lemma GridGood_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- A real scalar multiple of a Hermitian matrix is Hermitian. -/
private lemma GridGood_herm {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-- Along the closed-form flow (3.10) [eq:deterflow] up to the horizon `S`: `Im z_s > 0`,
`|z_s| ≤ |z| + 1`, `0 < Im m_s < 1`, and `N η_s Im m_s ≥ N^e` whenever it holds at `s = S`. -/
private lemma GridGood_flow (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (e : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im)
    (S : ℝ) (hS : S < flowTc (lam D N A) z)
    (hadm : (N : ℝ) ^ e ≤ N * (charFlowZ (lam D N A) z S).im * flowIm (lam D N A) z S)
    (s : ℝ) (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    0 < (charFlowZ (lam D N A) z s).im ∧ ‖charFlowZ (lam D N A) z s‖ ≤ ‖z‖ + 1 ∧
      0 < flowIm (lam D N A) z s ∧ flowIm (lam D N A) z s < 1 ∧
      (N : ℝ) ^ e ≤ N * (charFlowZ (lam D N A) z s).im * flowIm (lam D N A) z s := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  have hι : 0 < (mExt Λ z).im := by
    have : mExt Λ z = mSol Λ z := by simp [mExt, hz]
    rw [this]
    exact (mSol_spec Λ hΛ z hz).1
  set m := mExt Λ z with hmdef
  have hflow : ∀ r, r ≤ S → 0 < (charFlowZ Λ z r).im ∧
      mExt (((Real.exp (-r / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z r) =
        ((Real.exp (r / 2) : ℝ) : ℂ) * m := fun r hr =>
    ⟨(charFlow_M Λ hΛ z hz r (lt_of_le_of_lt hr hS)).1,
      (charFlow_M Λ hΛ z hz r (lt_of_le_of_lt hr hS)).2.2⟩
  have hIm : ∀ r, (charFlowZ Λ z r).im =
      Real.exp (-r / 2) * (z.im + m.im) - Real.exp (r / 2) * m.im := by
    intro r
    simp only [charFlowZ, Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rfl
  have hflowIm : ∀ r, r ≤ S → flowIm Λ z r = Real.exp (r / 2) * m.im := by
    intro r hr
    unfold flowIm
    rw [(hflow r hr).2]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hee : ∀ r : ℝ, Real.exp (-r / 2) * Real.exp (r / 2) = 1 := fun r => by
    rw [← Real.exp_add, show -r / 2 + r / 2 = 0 by ring, Real.exp_zero]
  have hprod : ∀ r, r ≤ S → (charFlowZ Λ z r).im * flowIm Λ z r =
      m.im * (z.im + m.im) - m.im ^ 2 * Real.exp (r / 2) ^ 2 := by
    intro r hr
    rw [hIm, hflowIm r hr]
    linear_combination (m.im * (z.im + m.im)) * hee r
  -- the a priori bound
  have hnorm : opNorm (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) ≤ 1 / 10 := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h0 : 0 ≤ opNorm Λ := norm_nonneg _
    nlinarith
  have hpos := (hflow s hsS).1
  have hapr := mSol_apriori _ (GridGood_herm Λ hΛ (Real.exp (-s / 2))) hnorm _ hpos
  have hms : ‖((Real.exp (s / 2) : ℝ) : ℂ) * m‖ < 1 := by
    have h1 : mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) =
        mSol (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) := by simp [mExt, hpos]
    rw [← (hflow s hsS).2, h1]
    exact hapr.2.1
  have hms' : Real.exp (s / 2) * ‖m‖ < 1 := by
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hms
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · -- the size of `z_s`
    have e1 : charFlowZ Λ z s = ((Real.exp (-s / 2) : ℝ) : ℂ) * z +
        (((Real.exp (-s / 2) - Real.exp (s / 2) : ℝ)) : ℂ) * m := by
      simp only [charFlowZ]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : |Real.exp (-s / 2) - Real.exp (s / 2)| ≤ Real.exp (s / 2) := by
      have h5 : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
      rw [abs_le]
      constructor <;> nlinarith [Real.exp_pos (-s / 2), Real.exp_pos (s / 2)]
    have h3 : Real.exp (-s / 2) * ‖z‖ ≤ ‖z‖ := by
      nlinarith [norm_nonneg z]
    have h4 : |Real.exp (-s / 2) - Real.exp (s / 2)| * ‖m‖ ≤ Real.exp (s / 2) * ‖m‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith
  · rw [hflowIm s hsS]
    exact mul_pos (Real.exp_pos _) hι
  · rw [hflowIm s hsS]
    have : m.im ≤ ‖m‖ := (Complex.im_le_norm m)
    have h5 : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
    nlinarith [Real.exp_pos (s / 2), norm_nonneg m]
  · have h6 : (charFlowZ Λ z S).im * flowIm Λ z S ≤ (charFlowZ Λ z s).im * flowIm Λ z s := by
      rw [hprod S le_rfl, hprod s hsS]
      have : Real.exp (s / 2) ^ 2 ≤ Real.exp (S / 2) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) 2
      nlinarith [sq_nonneg m.im]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) ^ e ≤ N * (charFlowZ Λ z S).im * flowIm Λ z S := hadm
      _ = N * ((charFlowZ Λ z S).im * flowIm Λ z S) := by ring
      _ ≤ N * ((charFlowZ Λ z s).im * flowIm Λ z s) := mul_le_mul_of_nonneg_left h6 hN0
      _ = _ := by ring


/-- A union over a finite index type of sets of measure at most `ofReal δ` has measure at most
`ofReal (card · δ)`. -/
private lemma GridGood_union {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (E : ι → Set Ω) (δ : ℝ) (h : ∀ i, μ (E i) ≤ ENNReal.ofReal δ) :
    μ (⋃ i, E i) ≤ ENNReal.ofReal (Fintype.card ι * δ) := by
  refine (measure_iUnion_fintype_le μ E).trans ?_
  calc ∑ i, μ (E i) ≤ ∑ _i : ι, ENNReal.ofReal δ := Finset.sum_le_sum fun i _ => h i
    _ = ENNReal.ofReal (Fintype.card ι * δ) := by
      rw [Finset.sum_const, Finset.card_univ, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, nsmul_eq_mul]

/-- `‖E_a‖ ≤ 1` for the block projection. -/
private lemma GridGood_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- The moment bound (2.3) [eq:highmoment] with Markov's inequality: an entry exceeds `1` with
probability at most `C_q N^{-q/2}`, so some entry does so with probability at most
`(DN)² C_q N^{-q/2}`. -/
private lemma GridGood_sup (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (q : ℕ) :
    μ {h | ∃ i j, 1 < ‖h i j‖} ≤
      ENNReal.ofReal (((D * N : ℕ) : ℝ) ^ 2 * (C q * (N : ℝ) ^ (-((q : ℝ) / 2)))) := by
  have := hμ.prob
  have hent : ∀ i j : Idx D N, μ {h | 1 < ‖h i j‖} ≤
      ENNReal.ofReal (C q * (N : ℝ) ^ (-((q : ℝ) / 2))) := by
    intro i j
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (f := fun h : Idx D N → Idx D N → ℂ => ‖h i j‖ ^ q)
      (ae_of_all _ fun h => by positivity) (hμ.integrable q i j) 1
    have h2 : μ {h | 1 < ‖h i j‖} ≤ μ {h | 1 ≤ ‖h i j‖ ^ q} :=
      measure_mono fun h (hh : 1 < ‖h i j‖) => (one_le_pow₀ hh.le : (1 : ℝ) ≤ ‖h i j‖ ^ q)
    refine h2.trans ?_
    rw [← ofReal_measureReal (μ := μ) (s := {h | 1 ≤ ‖h i j‖ ^ q})]
    exact ENNReal.ofReal_le_ofReal (by simpa using h1.trans (hμ.moments q i j))
  have hU : {h : Idx D N → Idx D N → ℂ | ∃ i j, 1 < ‖h i j‖} =
      ⋃ p : Idx D N × Idx D N, {h | 1 < ‖h p.1 p.2‖} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Prod.exists]
  rw [hU]
  have := GridGood_union μ (fun p : Idx D N × Idx D N => {h | 1 < ‖h p.1 p.2‖})
    (C q * (N : ℝ) ^ (-((q : ℝ) / 2))) fun p => hent p.1 p.2
  simpa [Fintype.card_prod, Fintype.card_fin, sq, mul_assoc] using this

/-- The index set of the words `(p, b, a)` of (A.53) [entprodG] with `1 ≤ p ≤ 8` resolvents, flags
`b` and block indices `a`. -/
private abbrev GridGood_Idx (D : ℕ) : Type :=
  Σ p : Fin 8, (Fin (p.val + 1) → Bool) × (Fin (p.val + 1) → Fin D)

/-- The number of events at one grid time: `D` for (2.23), the words of (A.53), and the sup norm. -/
private def GridGood_M (D : ℕ) : ℕ := D + Fintype.card (GridGood_Idx D) + 1

/-- The averaged local law (2.23) [eq:aver_local] at size `N`, as given by Lemma 2.9 [lem_loc]
uniformly over the class: for every `θ`, class member `μ`, `‖A‖ ≤ N^{-δ_A}` and `‖B‖ ≤ 1`. -/
private def GridGood_AL (D N : ℕ) (δA τ₀ τ' D'' : ℝ) (C : ℕ → ℝ) : Prop :=
  ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      μ {h | ∃ z ∈ specDom τ₀ N, (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)) <
          ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * B)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D''))

/-- The averaged bound of (A.53) [entprodG] at size `N` for `1 ≤ p ≤ 8` resolvents at one
`z ∈ 𝐃(τ₀)`, uniformly over the class, for `N η Im m ≥ 1`. -/
private def GridGood_EP (D N : ℕ) (δA τ₀ τ' D'' : ℝ) (C : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → p ≤ 8 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ z : Fin p → ℂ, (∀ i, z i ∈ specDom τ₀ N ∧ 0 < (z i).im ∧
      1 ≤ (N : ℝ) * (z i).im * (mExt (lam D N A) (z i)).im) →
    ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
      μ {h | (N : ℝ) ^ τ' * bndA4 (fun i => (mExt (lam D N A) (z i)).im) (fun i => (z i).im) p <
          ‖ntr (resProd (fun i => res (Matrix.of h + lam D N A) (z i)) s B)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D''))

/-- Lemma 2.9 [lem_loc], (2.23) [eq:aver_local], for all large `N`, at the size-`N` form of the
averaged local law above. -/
private lemma GridGood_AL_ex (D : ℕ) (hD : 1 ≤ D) (δA τ₀ τ' D'' : ℝ) (hδA : 0 < δA)
    (hτ₀ : 0 < τ₀) (C : ℕ → ℝ) (hτ' : 0 < τ') (hD'' : 0 < D'') :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → GridGood_AL D N δA τ₀ τ' D'' C := by
  obtain ⟨N₁, h⟩ := aver_local D hD δA τ₀ hδA hτ₀ C τ' hτ' D'' hD''
  exact ⟨N₁, h⟩

/-- (A.53) [entprodG] of Lemma A.4 [lemma_necessary_estimates] for `p ≤ 8`, for all large `N`, at
the size-`N` form of the averaged bound above. -/
private lemma GridGood_EP_ex (D : ℕ) (hD : 1 ≤ D) (δA τ₀ τ' D'' : ℝ) (hδA : 0 < δA)
    (hτ₀ : 0 < τ₀) (C : ℕ → ℝ) (hτ' : 0 < τ') (hD'' : 0 < D'') :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → GridGood_EP D N δA τ₀ τ' D'' C := by
  let N₂ : ℕ → ℕ := fun p => if hp : 1 ≤ p then
    Classical.choose (entprodG_unif D p hD hp δA τ₀ 1 hδA hτ₀ one_pos C τ' hτ' D'' hD'') else 0
  refine ⟨(Finset.range 9).sup N₂, fun N hN p hp1 hp8 θ hθ0 hθ1 μ hμ A hA z hz s B hB => ?_⟩
  have hle : N₂ p ≤ N :=
    (Finset.le_sup (f := N₂) (Finset.mem_range.2 (by omega : p < 9))).trans hN
  have hspec := Classical.choose_spec
    (entprodG_unif D p hD hp1 δA τ₀ 1 hδA hτ₀ one_pos C τ' hτ' D'' hD'')
  simp only [N₂, hp1, ↓reduceDIte] at hle
  exact (hspec N hle θ hθ0 hθ1 μ hμ A hA z hz s B hB).1

/-- One grid time: if the law of the state is a member of the class, and the local-law bounds
(2.23) [eq:aver_local] and (A.53) [entprodG] hold at size `N`, then the good event fails with
probability at most `M N^{-D''}`. -/
private lemma GridGood_single (D N : ℕ) (hD : 2 ≤ D) (hN : 2 ≤ N)
    (δA τ τe εg c C₀ τ₀ τ' D'' : ℝ) (C : ℕ → ℝ) (q : ℕ)
    (hτ₀ : 0 < τ₀) (hτ₀e : τ₀ ≤ C₀ * εg) (hτ₀z : τ⁻¹ + 1 ≤ τ₀⁻¹)
    (hΛ : 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10)
    (hmom : ((D * N : ℕ) : ℝ) ^ 2 * (C q * (N : ℝ) ^ (-((q : ℝ) / 2))) ≤ (N : ℝ) ^ (-D''))
    (hAL : GridGood_AL D N δA τ₀ τ' D'' C)
    (hEP : GridGood_EP D N δA τ₀ τ' D'' C)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ)
    (hadm : flowAdm D N δA τ τe εg c C₀ A z S) (s : ℝ) (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    μ {H | ¬ flowGoodAt A z τ' s H} ≤ ENNReal.ofReal ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D'')) := by
  obtain ⟨hA, hzdom, hz, -, -, -, -, hS, hSadm⟩ := hadm
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hΛ' : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  obtain ⟨hηpos, hzs, hιpos, hι1, hprod⟩ :=
    GridGood_flow D N (by omega) hN1 (C₀ * εg) A hΛ' z hz S hS hSadm s hs0 hsS
  set t : ℝ := Real.exp (-s / 2) with ht
  set zs := charFlowZ (lam D N A) z s with hzsdef
  set ιs := flowIm (lam D N A) z s with hιsdef
  have hee : 0 ≤ C₀ * εg := hτ₀.le.trans hτ₀e
  have hone : 1 ≤ (N : ℝ) * zs.im * ιs :=
    (Real.one_le_rpow hN1r hee).trans hprod
  have hηs : (N : ℝ) ^ (C₀ * εg - 1) ≤ zs.im := by
    rw [Real.rpow_sub_one hNpos.ne', div_le_iff₀ hNpos]
    have : (N : ℝ) * zs.im * ιs ≤ N * zs.im * 1 :=
      mul_le_mul_of_nonneg_left hι1.le (by positivity)
    linarith
  have hdom : zs ∈ specDom τ₀ N := by
    refine ⟨?_, ?_⟩
    · have := hzdom.1
      linarith
    · rw [abs_of_pos hηpos]
      refine le_trans ?_ hηs
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hA' : opNorm ((t : ℂ) • A) ≤ (N : ℝ) ^ (-δA) := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have h0 : 0 ≤ opNorm A := norm_nonneg _
    nlinarith
  have hlam : (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := GridGood_lam_smul D N A t
  have hmI : (mExt (lam D N ((t : ℂ) • A)) zs).im = ιs := by
    rw [← hlam]
    rfl
  set δ : ℝ := (N : ℝ) ^ (-D'') with hδ
  -- clause 1: the averaged local law (2.23) [eq:aver_local]
  have h1 : ∀ a : Fin D, μ {H | (N : ℝ) ^ τ' / (N * zs.im) <
      ‖ntr ((res (Matrix.of H + (t : ℂ) • lam D N A) zs -
        MExt ((t : ℂ) • lam D N A) zs) * Ea D N a)‖} ≤ ENNReal.ofReal δ := by
    intro a
    refine le_trans (measure_mono ?_)
      (hAL θ hθ0 hθ1 μ hμ _ hA' (Ea D N a) (GridGood_opNorm_Ea D N a))
    intro H hH
    refine ⟨zs, hdom, ?_⟩
    rw [abs_of_pos hηpos, mul_one_div, ← hlam]
    exact hH
  -- clause 2: (A.53) [entprodG] for the words of at most eight resolvents
  have h2 : ∀ idx : GridGood_Idx D, μ {H | (N : ℝ) ^ τ' *
      bndA4 (fun _ : Fin (idx.1.val + 1) => ιs) (fun _ : Fin (idx.1.val + 1) => zs.im)
        (idx.1.val + 1) <
      ‖ntr (resProd (fun _ => res (Matrix.of H + (t : ℂ) • lam D N A) zs) idx.2.1
        (fun i => Ea D N (idx.2.2 i)))‖} ≤ ENNReal.ofReal δ := by
    intro idx
    have hz' : ∀ i : Fin (idx.1.val + 1), (fun _ : Fin (idx.1.val + 1) => zs) i ∈ specDom τ₀ N ∧
        0 < ((fun _ : Fin (idx.1.val + 1) => zs) i).im ∧
        1 ≤ (N : ℝ) * ((fun _ : Fin (idx.1.val + 1) => zs) i).im *
          (mExt (lam D N ((t : ℂ) • A)) ((fun _ : Fin (idx.1.val + 1) => zs) i)).im := by
      intro i
      refine ⟨hdom, hηpos, ?_⟩
      change 1 ≤ (N : ℝ) * zs.im * (mExt (lam D N ((t : ℂ) • A)) zs).im
      rw [hmI]
      exact hone
    refine le_trans (measure_mono ?_) (hEP (idx.1.val + 1) (by omega) (by have := idx.1.isLt; omega)
      θ hθ0 hθ1 μ hμ _ hA' (fun _ => zs) hz' idx.2.1 (fun i => Ea D N (idx.2.2 i))
      fun i => GridGood_opNorm_Ea D N _)
    intro H hH
    have e1 : (fun i : Fin (idx.1.val + 1) =>
        (mExt (lam D N ((t : ℂ) • A)) ((fun _ : Fin (idx.1.val + 1) => zs) i)).im) =
        fun _ => ιs := by
      funext i
      exact hmI
    change (N : ℝ) ^ τ' * bndA4 (fun i : Fin (idx.1.val + 1) =>
        (mExt (lam D N ((t : ℂ) • A)) ((fun _ : Fin (idx.1.val + 1) => zs) i)).im)
        (fun i : Fin (idx.1.val + 1) => ((fun _ : Fin (idx.1.val + 1) => zs) i).im)
        (idx.1.val + 1) <
      ‖ntr (resProd (fun i : Fin (idx.1.val + 1) => res (Matrix.of H + lam D N ((t : ℂ) • A))
        ((fun _ : Fin (idx.1.val + 1) => zs) i)) idx.2.1 (fun i => Ea D N (idx.2.2 i)))‖
    rw [e1, ← hlam]
    exact hH
  -- clause 3: the sup norm
  have h3 : μ {h | ∃ i j, 1 < ‖h i j‖} ≤ ENNReal.ofReal δ :=
    (GridGood_sup D N C θ μ hμ q).trans (ENNReal.ofReal_le_ofReal hmom)
  -- the union
  have hsub : {H | ¬ flowGoodAt A z τ' s H} ⊆
      ((⋃ a : Fin D, {H | (N : ℝ) ^ τ' / (N * zs.im) <
        ‖ntr ((res (Matrix.of H + (t : ℂ) • lam D N A) zs -
          MExt ((t : ℂ) • lam D N A) zs) * Ea D N a)‖}) ∪
      (⋃ idx : GridGood_Idx D, {H | (N : ℝ) ^ τ' *
        bndA4 (fun _ : Fin (idx.1.val + 1) => ιs) (fun _ : Fin (idx.1.val + 1) => zs.im)
          (idx.1.val + 1) <
        ‖ntr (resProd (fun _ => res (Matrix.of H + (t : ℂ) • lam D N A) zs) idx.2.1
          (fun i => Ea D N (idx.2.2 i)))‖})) ∪ {h | ∃ i j, 1 < ‖h i j‖} := by
    intro H hH
    change ¬ flowGoodAt A z τ' s H at hH
    unfold flowGoodAt at hH
    rw [not_and_or, not_and_or] at hH
    rcases hH with h | h | h
    · simp only [not_forall, not_le] at h
      obtain ⟨a, ha⟩ := h
      exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨a, ha⟩))
    · simp only [not_forall, not_le] at h
      obtain ⟨p, hp1, hp8, b, a, hab⟩ := h
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨⟨⟨p', by omega⟩, b, a⟩, hab⟩))
    · simp only [not_forall, not_le] at h
      obtain ⟨i, j, hij⟩ := h
      exact Or.inr ⟨i, j, hij⟩
  have hU1 := GridGood_union μ _ δ h1
  have hU2 := GridGood_union μ _ δ h2
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hNpos.le _
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add hU1 hU2)) h3).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) hδ0]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  simp only [GridGood_M, Fintype.card_fin]
  push_cast
  ring

/-- The pull-back step: the bad event of the state at grid time `k` has probability at most the
probability of the bad set under the block-OU law (3.13) [eq:Gauss_div]. -/
private lemma GridGood_time (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (hk : k ≤ K)
    (B : Set (Idx D N → Idx D N → ℂ)) (ε : ENNReal) (hB : blockOULaw D N μ₀ (k * h) B ≤ ε) :
    gridLawA D N K μ₀ ((fun ω => gridStateA D N K h ω k) ⁻¹' B) ≤ ε := by
  have hmeas : Measurable (fun ω => gridStateA D N K h ω k) :=
    (gridStateA_adapted D N K h k).mono ((gridFiltrationA D N K).le k) le_rfl
  calc gridLawA D N K μ₀ ((fun ω => gridStateA D N K h ω k) ⁻¹' B)
      ≤ ((gridLawA D N K μ₀).map (fun ω => gridStateA D N K h ω k)) B :=
        Measure.le_map_apply hmeas.aemeasurable B
    _ = blockOULaw D N μ₀ (k * h) B := by rw [gridStateA_law D N K μ₀ h hh k hk]
    _ ≤ ε := hB

/-- The moment condition `(DN)² C_q N^{-q/2} ≤ N^{-D''}` for `q = 2(⌈D''⌉ + 4)`, `N² ≥ D² |C_q|`. -/
private lemma GridGood_mom (D N : ℕ) (hN : 2 ≤ N) (D'' : ℝ) (C : ℕ → ℝ)
    (hNC : (D : ℝ) ^ 2 * |C (2 * (⌈D''⌉₊ + 4))| ≤ N) :
    ((D * N : ℕ) : ℝ) ^ 2 * (C (2 * (⌈D''⌉₊ + 4)) * (N : ℝ) ^ (-(((2 * (⌈D''⌉₊ + 4) : ℕ) : ℝ) / 2)))
      ≤ (N : ℝ) ^ (-D'') := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  set q := 2 * (⌈D''⌉₊ + 4) with hq
  have hr : D'' + 4 ≤ (q : ℝ) / 2 := by
    have := Nat.le_ceil D''
    simp only [hq]
    push_cast
    linarith
  have h1 : (N : ℝ) ^ (-((q : ℝ) / 2)) ≤ (N : ℝ) ^ (-D'') / (N : ℝ) ^ 4 := by
    calc (N : ℝ) ^ (-((q : ℝ) / 2)) ≤ (N : ℝ) ^ (-D'' - 4) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ = (N : ℝ) ^ (-D'') / (N : ℝ) ^ (4 : ℝ) := Real.rpow_sub hNpos _ _
      _ = (N : ℝ) ^ (-D'') / (N : ℝ) ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hu : 0 < (N : ℝ) ^ (-D'') := Real.rpow_pos_of_pos hNpos _
  have h2 : C q * (N : ℝ) ^ (-((q : ℝ) / 2)) ≤ |C q| * ((N : ℝ) ^ (-D'') / (N : ℝ) ^ 4) := by
    calc C q * (N : ℝ) ^ (-((q : ℝ) / 2)) ≤ |C q| * (N : ℝ) ^ (-((q : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hNpos.le _)
      _ ≤ |C q| * ((N : ℝ) ^ (-D'') / (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 : ((D * N : ℕ) : ℝ) ^ 2 * (|C q| * ((N : ℝ) ^ (-D'') / (N : ℝ) ^ 4)) ≤
      (N : ℝ) ^ (-D'') := by
    have e : ((D * N : ℕ) : ℝ) ^ 2 * (|C q| * ((N : ℝ) ^ (-D'') / (N : ℝ) ^ 4)) =
        ((D : ℝ) ^ 2 * |C q|) * (N : ℝ) ^ (-D'') / (N : ℝ) ^ 2 := by
      push_cast
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : (D : ℝ) ^ 2 * |C q| ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hu.le]
  calc ((D * N : ℕ) : ℝ) ^ 2 * (C q * (N : ℝ) ^ (-((q : ℝ) / 2)))
      ≤ ((D * N : ℕ) : ℝ) ^ 2 * (|C q| * ((N : ℝ) ^ (-D'') / (N : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (N : ℝ) ^ (-D'') := h3

/-- The good event holds at all grid times of one grid with at most `N^{C_g+1}` steps, outside
probability `N^{-D'}`, uniformly over class members, `A` and admissible `(z, S)`. -/
theorem flowGood_grid (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4) (hC₀ : 6 < C₀)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∀ Cg : ℝ, 0 < Cg → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ₀ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ₀ →
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ), flowAdm D N δA τ τe εg c C₀ A z S →
      ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ (N : ℝ) ^ (Cg + 1) →
        gridLawA D N K μ₀ {ω | ∃ k : ℕ, k ≤ K ∧
          ¬ flowGoodAt A z τ' (k * (S / K)) (gridStateA D N K (S / K) ω k)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD' Cg hCg
  obtain ⟨C', hC'⟩ := llClass_blockOU D C
  -- the spectral domain along the flow is contained in `𝐃(τ₀)`
  set τ₀ : ℝ := min (τ / (1 + τ)) (C₀ * εg) with hτ₀def
  have hCε : 0 < C₀ * εg := mul_pos (by linarith) hεg
  have hτ₀ : 0 < τ₀ := lt_min (div_pos hτ (by linarith)) hCε
  have hτ₀e : τ₀ ≤ C₀ * εg := min_le_right _ _
  have hτ₀z : τ⁻¹ + 1 ≤ τ₀⁻¹ := by
    have h1 : τ₀ ≤ τ / (1 + τ) := min_le_left _ _
    have h2 : (τ / (1 + τ))⁻¹ ≤ τ₀⁻¹ := inv_anti₀ hτ₀ h1
    have h3 : (τ / (1 + τ))⁻¹ = τ⁻¹ + 1 := by
      field_simp
    linarith
  set D'' : ℝ := D' + Cg + 2 with hD''def
  have hD'' : 0 < D'' := by linarith
  have hD1 : 1 ≤ D := by omega
  obtain ⟨N₁, hN₁⟩ := GridGood_AL_ex D hD1 δA τ₀ τ' D'' hδA hτ₀ C' hτ' hD''
  obtain ⟨N₂, hN₂⟩ := GridGood_EP_ex D hD1 δA τ₀ τ' D'' hδA hτ₀ C' hτ' hD''
  set q : ℕ := 2 * (⌈D''⌉₊ + 4) with hq
  set N₃ : ℕ := ⌈(D : ℝ) ^ 2 * |C' q|⌉₊ with hN₃
  have hT : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.1
    (hT.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 20 by norm_num)))
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max 2 (2 * GridGood_M D)), ?_⟩
  intro N hN θ hθ0 hθ1 μ₀ hμ₀ A z S hadm K hK1 hK
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : 2 ≤ N := by omega
  have hN6 : 2 * GridGood_M D ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have := hμ₀.prob
  have hS0 : 0 ≤ S := hadm.2.2.2.2.2.2.1
  have hΛ : 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 := by
    have := hN₄ N hN4
    linarith
  have hNC : (D : ℝ) ^ 2 * |C' q| ≤ N := by
    have h1 := Nat.le_ceil ((D : ℝ) ^ 2 * |C' q|)
    have h2 : ((N₃ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hmom := GridGood_mom D N hN5 D'' C' hNC
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  -- one grid time
  have hone : ∀ k : ℕ, k ≤ K →
      gridLawA D N K μ₀ ((fun ω => gridStateA D N K (S / K) ω k) ⁻¹'
        {H | ¬ flowGoodAt A z τ' (k * (S / K)) H}) ≤
        ENNReal.ofReal ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D'')) := by
    intro k hk
    have hs0 : 0 ≤ (k : ℝ) * (S / K) := mul_nonneg (Nat.cast_nonneg k) (div_nonneg hS0 hKr.le)
    have hsS : (k : ℝ) * (S / K) ≤ S := by
      calc (k : ℝ) * (S / K) ≤ K * (S / K) :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) (div_nonneg hS0 hKr.le)
        _ = S := by field_simp
    have hcl := hC' N θ μ₀ ((k : ℝ) * (S / K)) hθ0 hθ1 hs0 hμ₀
    have he0 : 0 < Real.exp (-((k : ℝ) * (S / K))) := Real.exp_pos _
    have he1 : Real.exp (-((k : ℝ) * (S / K))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    refine GridGood_time D N K μ₀ (S / K) (div_nonneg hS0 hKr.le) k hk _ _ ?_
    exact GridGood_single D N hD hN5 δA τ τe εg c C₀ τ₀ τ' D'' C' q hτ₀ hτ₀e hτ₀z hΛ hmom
      (hN₁ N hN1) (hN₂ N hN2) _ (by nlinarith [mul_nonneg he0.le hθ0])
      (by nlinarith [mul_le_mul_of_nonneg_left hθ1 he0.le]) _ hcl A z S hadm _ hs0 hsS
  -- the union over the grid times
  have hsub : {ω | ∃ k : ℕ, k ≤ K ∧
      ¬ flowGoodAt A z τ' (k * (S / K)) (gridStateA D N K (S / K) ω k)} ⊆
      ⋃ k ∈ Finset.range (K + 1), (fun ω => gridStateA D N K (S / K) ω k) ⁻¹'
        {H | ¬ flowGoodAt A z τ' (k * (S / K)) H} := by
    intro ω hω
    obtain ⟨k, hk, hbad⟩ := hω
    simp only [Set.mem_iUnion]
    exact ⟨k, Finset.mem_range.2 (by omega), hbad⟩
  have hP : (1 : ℝ) ≤ (N : ℝ) ^ (Cg + 1) := Real.one_le_rpow hN1r (by linarith)
  have hkey : (N : ℝ) ^ (Cg + 1) * (N : ℝ) ^ (-D'') = (N : ℝ) ^ (-D') / N := by
    rw [← Real.rpow_add hNpos, show Cg + 1 + -D'' = -D' - 1 by rw [hD''def]; ring,
      Real.rpow_sub_one hNpos.ne']
  have hM : (2 * (GridGood_M D : ℝ)) ≤ N := by exact_mod_cast hN6
  have hu : 0 ≤ (N : ℝ) ^ (-D'') := Real.rpow_nonneg hNpos.le _
  have hv : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hNpos.le _
  have hfin : ((K : ℝ) + 1) * ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D'')) ≤ (N : ℝ) ^ (-D') := by
    calc ((K : ℝ) + 1) * ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D''))
        ≤ (2 * (N : ℝ) ^ (Cg + 1)) * ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D'')) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * (GridGood_M D : ℝ) * ((N : ℝ) ^ (Cg + 1) * (N : ℝ) ^ (-D'')) := by ring
      _ = 2 * (GridGood_M D : ℝ) * ((N : ℝ) ^ (-D') / N) := by rw [hkey]
      _ ≤ (N : ℝ) ^ (-D') := by
        rw [← mul_div_assoc, div_le_iff₀ hNpos]
        nlinarith [mul_le_mul_of_nonneg_right hM hv]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ k ∈ Finset.range (K + 1), gridLawA D N K μ₀ ((fun ω => gridStateA D N K (S / K) ω k) ⁻¹'
        {H | ¬ flowGoodAt A z τ' (k * (S / K)) H})
      ≤ ∑ _k ∈ Finset.range (K + 1),
        ENNReal.ofReal ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D'')) :=
        Finset.sum_le_sum fun k hk => hone k (by simpa [Nat.lt_succ_iff] using hk)
    _ = ENNReal.ofReal (((K : ℝ) + 1) * ((GridGood_M D : ℝ) * (N : ℝ) ^ (-D''))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal hfin

end RBMTransitionEdge

end
