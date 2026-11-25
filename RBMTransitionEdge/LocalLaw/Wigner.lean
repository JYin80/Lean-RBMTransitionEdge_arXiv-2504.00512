module

public import RBMTransitionEdge.LocalLaw.OU
public import RBMTransitionEdge.LocalLaw.Rigidity

@[expose] public section

/-!
# The local laws for `H_t` and the rigidity of the Wigner blocks

The local-law part of Lemma 4.4 [lem:samefort] ((2.22) [eq:aniso_local], (2.23) [eq:aver_local]
and (2.24) [eq:rigidity] for `H_Λ(t)`), and (5.12) [rigidity12] for each block `H_a` of (1.3)
[matrix_H] with the quantiles (5.13) [eq:gammak2].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section

open Classical

namespace RBMTransitionEdge

/-- `N^a ≥ c` for all large `N`, when `a > 0`. -/
private lemma Wigner_ev (c a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop c)

/-- The Wigner matrix `wig n w` is Hermitian. -/
private lemma Wigner_wig_isHermitian (n : ℕ) (w : Coords n) : (wig n w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- The block-diagonal matrix `blockH D N w` is Hermitian. -/
private lemma Wigner_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (Wigner_wig_isHermitian N (w q.1)).apply p.2 q.2
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- `Λ = lam D N 0` is the zero matrix. -/
private lemma Wigner_lam_zero (D N : ℕ) : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
  ext p q
  simp [lam]

/-- `‖0‖ = 0`. -/
private lemma Wigner_opNorm_zero (N : ℕ) : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
  unfold opNorm
  rw [map_zero, norm_zero]

open scoped Matrix.Norms.L2Operator in
/-- `‖E_a‖ ≤ 1`. -/
private lemma Wigner_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have e : opNorm (Ea D N a) = ‖(Ea D N a : Matrix (Idx D N) (Idx D N) ℂ)‖ := rfl
  rw [e, Ea, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
  by_cases h : p.1 = a <;> simp [h]

/-- The vector on the blocks that is `x` on the block `a` and `0` elsewhere. -/
private def Wigner_emb (D N : ℕ) (a : Fin D) (x : Fin N → ℂ) : Idx D N → ℂ :=
  fun p => if p.1 = a then x p.2 else 0

/-- `⟨x̃, ỹ⟩ = ⟨x, y⟩` for the extensions by zero to the block `a`. -/
private lemma Wigner_emb_dot (D N : ℕ) (a : Fin D) (x y : Fin N → ℂ) :
    star (Wigner_emb D N a x) ⬝ᵥ Wigner_emb D N a y = star x ⬝ᵥ y := by
  simp only [dotProduct, Wigner_emb, Pi.star_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- `H x̃ = (H_a x)~` for the block-diagonal `H = blockH D N w` and `H_a = wig N (w a)`. -/
private lemma Wigner_blockH_mulVec_emb (D N : ℕ) (w : Fin D → Coords N) (a : Fin D)
    (x : Fin N → ℂ) :
    blockH D N w *ᵥ Wigner_emb D N a x = Wigner_emb D N a (wig N (w a) *ᵥ x) := by
  ext p
  simp only [Matrix.mulVec, dotProduct, Wigner_emb, blockH, Fintype.sum_prod_type]
  by_cases h : p.1 = a
  · simp only [h, ↓reduceIte]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hb : p.1 = b
    · subst hb
      simp [h]
    · simp [hb]

/-- The quadratic forms of a scalar multiple of `x`. -/
private lemma Wigner_form_smul {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (c : ℂ) (x : ι → ℂ) :
    (star (c • x) ⬝ᵥ (M *ᵥ (c • x))).re = Complex.normSq c * (star x ⬝ᵥ (M *ᵥ x)).re ∧
      (star (c • x) ⬝ᵥ (c • x)).re = Complex.normSq c * (star x ⬝ᵥ x).re := by
  have hc : star c * c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  constructor
  · rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hc, Complex.re_ofReal_mul]
  · rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hc,
      Complex.re_ofReal_mul]

/-- `⟨x, M x⟩ ≤ λ_1(M) ‖x‖²` (Courant–Fischer, `k = 1`). -/
private lemma Wigner_rayleigh_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ eigK M 1 * (star x ⬝ᵥ x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨y, hyV, hy0, hy⟩ := (eigK_minmax M hM 1 le_rfl Fintype.card_pos).2
      (Submodule.span ℂ {x}) (finrank_span_singleton hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyV
    have hc : c ≠ 0 := fun h => hy0 (by simp [h])
    have hn : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
    obtain ⟨h1, h2⟩ := Wigner_form_smul M c x
    rw [h1, h2] at hy
    nlinarith

/-- `λ_{card ι}(M) ‖x‖² ≤ ⟨x, M x⟩` (Courant–Fischer, `k = card ι`). -/
private lemma Wigner_rayleigh_ge {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (x : ι → ℂ) :
    eigK M (Fintype.card ι) * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
  obtain ⟨V, hV, hV'⟩ := (eigK_minmax M hM (Fintype.card ι) Fintype.card_pos le_rfl).1
  have : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hV, Module.finrank_fintype_fun_eq_card])
  exact hV' x (this ▸ Submodule.mem_top)

/-- Some nonzero `x` has `⟨x, M x⟩ ≥ λ_1(M) ‖x‖²`. -/
private lemma Wigner_exists_ge {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    ∃ x : ι → ℂ, x ≠ 0 ∧ eigK M 1 * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
  obtain ⟨V, hV, hV'⟩ := (eigK_minmax M hM 1 le_rfl Fintype.card_pos).1
  have h : 0 < Module.finrank ℂ V := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  exact ⟨x, fun h => hx0 (by simp [h]), hV' x hx⟩

/-- Some nonzero `x` has `⟨x, M x⟩ ≤ λ_{card ι}(M) ‖x‖²`. -/
private lemma Wigner_exists_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    ∃ x : ι → ℂ, x ≠ 0 ∧ (star x ⬝ᵥ (M *ᵥ x)).re ≤ eigK M (Fintype.card ι) * (star x ⬝ᵥ x).re := by
  obtain ⟨x, -, hx0, hx⟩ := (eigK_minmax M hM (Fintype.card ι) Fintype.card_pos le_rfl).2 ⊤
    (by rw [finrank_top, Module.finrank_fintype_fun_eq_card])
  exact ⟨x, hx0, hx⟩

/-- `‖x‖² > 0` for `x ≠ 0`. -/
private lemma Wigner_norm_pos {ι : Type*} [Fintype ι] {x : ι → ℂ} (hx : x ≠ 0) :
    0 < (star x ⬝ᵥ x).re := by
  have h : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [h]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := by simpa using hi
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi') 2) (Finset.single_le_sum
    (f := fun i => ‖x i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))

/-- The extreme eigenvalues of the block `H_a` are inside the spectrum of the block-diagonal `H`:
`λ_{DN}(H) ≤ λ_N(H_a)` and `λ_1(H_a) ≤ λ_1(H)`. -/
private lemma Wigner_block_edges (D N : ℕ) (hN : 1 ≤ N) (w : Fin D → Coords N) (a : Fin D) :
    eigK (blockH D N w) (D * N) ≤ eigK (wig N (w a)) N ∧
      eigK (wig N (w a)) 1 ≤ eigK (blockH D N w) 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Idx D N) := ⟨(a, ⟨0, hN⟩)⟩
  have hH := Wigner_blockH_isHermitian D N w
  have hX := Wigner_wig_isHermitian N (w a)
  have hcard : Fintype.card (Idx D N) = D * N := by simp
  have e1 : eigK (blockH D N w) (D * N) = eigK (blockH D N w) (Fintype.card (Idx D N)) := by
    rw [hcard]
  have e2 : eigK (wig N (w a)) N = eigK (wig N (w a)) (Fintype.card (Fin N)) := by
    rw [Fintype.card_fin]
  constructor
  · rw [e1, e2]
    obtain ⟨x, hx0, hx⟩ := Wigner_exists_le (wig N (w a)) hX
    have h1 := Wigner_rayleigh_ge (blockH D N w) hH (Wigner_emb D N a x)
    rw [Wigner_blockH_mulVec_emb, Wigner_emb_dot, Wigner_emb_dot] at h1
    exact le_of_mul_le_mul_right (h1.trans hx) (Wigner_norm_pos hx0)
  · obtain ⟨x, hx0, hx⟩ := Wigner_exists_ge (wig N (w a)) hX
    have h1 := Wigner_rayleigh_le (blockH D N w) hH (Wigner_emb D N a x)
    rw [Wigner_blockH_mulVec_emb, Wigner_emb_dot, Wigner_emb_dot] at h1
    exact le_of_mul_le_mul_right (hx.trans h1) (Wigner_norm_pos hx0)

/-- The normalized trace of a difference. -/
private lemma Wigner_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- `⟨c B⟩ = c ⟨B⟩`. -/
private lemma Wigner_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (B : Matrix ι ι ℂ) :
    ntr (c • B) = c * ntr B := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `⟨c I⟩ = c`. -/
private lemma Wigner_ntr_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (c : ℂ) :
    ntr (c • (1 : Matrix ι ι ℂ)) = c := by
  have h : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [ntr, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  field_simp

/-- `m_sc(z) I` is the solution `M = (Λ - z - m)⁻¹` of Definition 2.7 [defn_Mm] for `Λ = 0`: for
`Im z > 0`, `MExt 0 z = MSol 0 z = m_sc(z) I`, from `m_sc² + z m_sc + 1 = 0`
(`rho_zero`). -/
private lemma Wigner_M_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (z : ℂ)
    (hz : 0 < z.im) :
    MExt (0 : Matrix ι ι ℂ) z = msc z • (1 : Matrix ι ι ℂ) ∧
      MSol (0 : Matrix ι ι ℂ) z = msc z • (1 : Matrix ι ι ℂ) := by
  have hq := ((rho_zero (ι := Fin 1)).2.2.2.2.2.2 z hz).1
  have hm : mExt (0 : Matrix ι ι ℂ) z = msc z := (rho_zero (ι := ι)).1 z
  have hmS : mSol (0 : Matrix ι ι ℂ) z = msc z := by
    rw [← hm]
    simp [mExt, hz]
  have key : (0 - (z + msc z) • (1 : Matrix ι ι ℂ)) * (msc z • (1 : Matrix ι ι ℂ)) = 1 := by
    have e : (-(z + msc z)) * msc z = 1 := by linear_combination -hq
    have e' : (0 - (z + msc z) • (1 : Matrix ι ι ℂ)) = (-(z + msc z)) • (1 : Matrix ι ι ℂ) := by
      rw [zero_sub, neg_smul]
    rw [e', Matrix.smul_mul, Matrix.one_mul, smul_smul, e, one_smul]
  exact ⟨by rw [MExt, hm]; exact Matrix.inv_eq_right_inv key,
    by rw [MSol, hmS]; exact Matrix.inv_eq_right_inv key⟩

/-- `D⟨(G - M) E_a⟩ = ⟨G_a - m_sc⟩` for `H = blockH D N w`, `Λ = 0` and `Im z > 0`: the block
trace identity of `blockH_ntr_res_Ea` and `M = m_sc I`, `⟨E_a⟩ = 1/D`. -/
private lemma Wigner_aver_eq (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (w : Fin D → Coords N) (a : Fin D)
    (z : ℂ) (hz : 0 < z.im) :
    (D : ℂ) * ntr ((res (blockH D N w) z - MExt (0 : Matrix (Idx D N) (Idx D N) ℂ) z) * Ea D N a) =
      ntr (res (wig N (w a)) z - MSol (0 : Matrix (Fin N) (Fin N) ℂ) z) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Idx D N) := ⟨(a, ⟨0, hN⟩)⟩
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hEa : ntr (Ea D N a) = (D : ℂ)⁻¹ := by
    have : (Ea D N a).trace = N := by
      simp only [Ea, Matrix.trace_diagonal, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    simp only [ntr, this, Fintype.card_prod, Fintype.card_fin]
    push_cast
    field_simp
  have hM := (Wigner_M_zero (ι := Idx D N) z hz).1
  have hMS := (Wigner_M_zero (ι := Fin N) z hz).2
  rw [Matrix.sub_mul, Wigner_ntr_sub, hM, Matrix.smul_mul, Matrix.one_mul, Wigner_ntr_smul, hEa,
    mul_sub, blockH_ntr_res_Ea D N w z hz.ne' a, hMS, Wigner_ntr_sub, Wigner_ntr_smul_one]
  field_simp

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma Wigner_measurable_wig (n : ℕ) (i j : Fin n) :
    Measurable fun c : Coords n => wig n c i j := by
  unfold wig
  by_cases h1 : i = j
  · simp only [h1, ite_true]
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp measurable_fst))
  · by_cases h2 : i < j
    · simp only [h1, h2, ite_true, ite_false]
      exact measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
    · simp only [h1, h2, ite_false]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)))

/-- The map `w ↦ blockH D N w`, read as an array, is measurable. -/
private lemma Wigner_measurable_map (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  by_cases h : p.1 = q.1
  · simp only [Matrix.of_symm_apply, blockH, h, ↓reduceIte]
    exact (Wigner_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
  · simp only [Matrix.of_symm_apply, blockH, h, ↓reduceIte]
    exact measurable_const

/-- Lemma 4.4 [lem:samefort], local-law part: (2.22) [eq:aniso_local], (2.23)
[eq:aver_local] and (2.24) [eq:rigidity] for `H_Λ(t)`, `H_t` with the law (4.3)
[eq:eq_in_law_H], uniformly in `t ≥ 0` (in particular `t ∈ [0, 𝔱]`) and in the entry laws
with moment constants `C`. -/
theorem samefort_local (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        (∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
          ouMatLaw D N L t {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * psiIso (lam D N A) N z <
              ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
        (∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
          ouMatLaw D N L t {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * (1 / ((N : ℝ) * |z.im|)) <
              ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * B)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D'))) ∧
        ouMatLaw D N L t {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
            (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
              |eigK (Matrix.of h + lam D N A) k - quant (rho (lam D N A)) (D * N) k|} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨N₁, h₁⟩ := aniso_local D hD δA τ hδA hτ C' τ' hτ' D' hD'
  obtain ⟨N₂, h₂⟩ := aver_local D hD δA τ hδA hτ C' τ' hτ' D' hD'
  obtain ⟨N₃, h₃⟩ := rigidity D hD δA hδA C' τ' hτ' D' hD'
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN L t ht A hA
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN₁, hN₂⟩, hN₃⟩ := hN
  have hθ := hC' N L t ht
  have h0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact ⟨fun u v hu hv => h₁ N hN₁ _ h0 h1 _ hθ A hA u v hu hv,
    fun B hB => h₂ N hN₂ _ h0 h1 _ hθ A hA B hB, h₃ N hN₃ _ h0 h1 _ hθ A hA⟩

/-- (5.12) [rigidity12]: under Assumption 1 [main_assm] each block `H_a` of (1.3) [matrix_H]
satisfies `|λ_i(H_a) - γ^sc_{i,N}| ≤ N^{τ'} N^{-2/3} min(i, N+1-i)^{-1/3}` for all
`i ∈ ⟦1, N⟧` outside an event of probability `≤ N^{-D'}`, with `γ^sc_{i,N} = γ^sc_{Di}` the
quantile (5.13) [eq:gammak2]. -/
theorem rigidity12 (D : ℕ) (hD : 1 ≤ D) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (a : Fin D),
        blockLaw D N L {w | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
            (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) <
              |eigK (wig N (w a)) i - quant rhoSc (D * N) (D * i)|} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  set s : ℝ := min τ' (1 / 5) / 8 with hs_def
  have hs0 : 0 < s := by positivity
  have hsτ : s ≤ τ' / 8 := by
    have := min_le_left τ' (1 / 5); rw [hs_def]; linarith
  have hs1 : s ≤ 1 / 40 := by
    have := min_le_right τ' (1 / 5); rw [hs_def]; linarith
  obtain ⟨N₁, h₁⟩ := aver_local D hD 1 (s / 2) one_pos (by positivity) C (s / 2) (by positivity)
    (D' + 1) (by linarith)
  obtain ⟨N₂, h₂⟩ := spec_inclusion D hD 1 one_pos C (2 * s) (by positivity) (D' + 1) (by linarith)
  obtain ⟨n₃, h₃⟩ := count_of_aver s hs0 (by linarith)
  obtain ⟨n₄, h₄⟩ := rigidity_of_count (2 * s) (by linarith) (by linarith)
  obtain ⟨C₁, hC₁0, hC₁⟩ := quant_shift D hD
  obtain ⟨N₅, h₅⟩ := Wigner_ev (D : ℝ) (s / 2) (by positivity)
  obtain ⟨N₆, h₆⟩ := Wigner_ev 2 (τ' / 4) (by positivity)
  obtain ⟨N₇, h₇⟩ := Wigner_ev C₁ (3 * τ' / 4) (by positivity)
  refine ⟨max (max (max N₁ N₂) (max n₃ n₄)) (max (max N₅ N₆) (max N₇ 2)), ?_⟩
  intro N hN L a
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN₁, hN₂⟩, hn₃, hn₄⟩, ⟨hN₅, hN₆⟩, hN₇, hN2⟩ := hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Idx D N) := ⟨(a, ⟨0, by omega⟩)⟩
  have hn₃' : n₃ ≤ Fintype.card (Fin N) := by rw [Fintype.card_fin]; exact hn₃
  have hn₄' : n₄ ≤ Fintype.card (Fin N) := by rw [Fintype.card_fin]; exact hn₄
  -- the block law of (1.3) as a member of the class
  set f : (Fin D → Coords N) → (Idx D N → Idx D N → ℂ) :=
    fun w => Matrix.of.symm (blockH D N w) with hf_def
  have hμH : LLClass D N C 1 ((blockLaw D N L).map f) := llClass_blockH D N C L
  have hae : AEMeasurable f (blockLaw D N L) := (Wigner_measurable_map D N).aemeasurable
  have hA : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [Wigner_opNorm_zero]; exact Real.rpow_nonneg hN0.le _
  have hΛn : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ 1 / 10 := by
    rw [Wigner_opNorm_zero]; norm_num
  -- the two bad events of the class
  set S₁ : Set (Idx D N → Idx D N → ℂ) := {h | ∃ z ∈ specDom (s / 2) N,
      (N : ℝ) ^ (s / 2) * (1 / ((N : ℝ) * |z.im|)) <
        ‖ntr ((res (Matrix.of h + lam D N (0 : Matrix (Fin N) (Fin N) ℂ)) z -
          MExt (lam D N (0 : Matrix (Fin N) (Fin N) ℂ)) z) * Ea D N a)‖} with hS₁
  set S₂ : Set (Idx D N → Idx D N → ℂ) := {h | Eplus (lam D N (0 : Matrix (Fin N) (Fin N) ℂ)) +
        (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s) <
        eigK (Matrix.of h + lam D N (0 : Matrix (Fin N) (Fin N) ℂ)) 1 ∨
      eigK (Matrix.of h + lam D N (0 : Matrix (Fin N) (Fin N) ℂ)) (D * N) <
        Eminus (lam D N (0 : Matrix (Fin N) (Fin N) ℂ)) - (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s)}
    with hS₂
  have hμ₁ : ((blockLaw D N L).map f) S₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    h₁ N hN₁ 1 zero_le_one le_rfl _ hμH 0 hA (Ea D N a) (Wigner_opNorm_Ea D N a)
  have hμ₂ : ((blockLaw D N L).map f) S₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    h₂ N hN₂ 1 zero_le_one le_rfl _ hμH 0 hA
  -- on the good event, the rigidity bound holds for every `i`
  have hsub : {w : Fin D → Coords N | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
      (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) <
        |eigK (wig N (w a)) i - quant rhoSc (D * N) (D * i)|} ⊆ f ⁻¹' S₁ ∪ f ⁻¹' S₂ := by
    intro w ⟨i, hi1, hiN, hlt⟩
    by_contra hgood
    simp only [Set.mem_union, not_or] at hgood
    obtain ⟨hg₁, hg₂⟩ := hgood
    have hfw : Matrix.of (f w) = blockH D N w := Matrix.of.apply_symm_apply _
    have hg₁' : ¬ (f w ∈ S₁) := hg₁
    have hg₂' : ¬ (f w ∈ S₂) := hg₂
    simp only [hS₁, hS₂, Set.mem_ofPred_eq, hfw, Wigner_lam_zero, add_zero, not_exists, not_and,
      not_lt, not_or] at hg₁' hg₂'
    have hE0 : Eplus (0 : Matrix (Idx D N) (Idx D N) ℂ) = 2 := (rho_zero (ι := Idx D N)).2.2.1
    have hE0' : Eminus (0 : Matrix (Idx D N) (Idx D N) ℂ) = -2 :=
      (rho_zero (ι := Idx D N)).2.2.2.1
    have hE1 : Eplus (0 : Matrix (Fin N) (Fin N) ℂ) = 2 := (rho_zero (ι := Fin N)).2.2.1
    have hE1' : Eminus (0 : Matrix (Fin N) (Fin N) ℂ) = -2 := (rho_zero (ι := Fin N)).2.2.2.1
    rw [hE0, hE0'] at hg₂'
    set X := wig N (w a) with hX_def
    have hXH : X.IsHermitian := Wigner_wig_isHermitian N (w a)
    obtain ⟨hedge_lo, hedge_hi⟩ := Wigner_block_edges D N hN1 w a
    -- the averaged law of the block on `{|Re z| ≤ 4, N^{-1+s} ≤ Im z ≤ 1}`
    have hLL : ∀ z : ℂ, |z.re| ≤ 4 → (N : ℝ) ^ (-1 + s) ≤ z.im → z.im ≤ 1 →
        ‖ntr (res X z - MSol (0 : Matrix (Fin N) (Fin N) ℂ) z)‖ ≤
          (N : ℝ) ^ s / ((N : ℝ) * z.im) := by
      intro z hre him1 him2
      have hηpos : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) him1
      have hNs : (N : ℝ) ^ (-1 + s / 2) ≤ (N : ℝ) ^ (-1 + s) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      have hz : z ∈ specDom (s / 2) N := by
        refine ⟨?_, ?_⟩
        · have h1 := Complex.norm_le_abs_re_add_abs_im z
          have h2 : |z.im| ≤ 1 := by rw [abs_of_pos hηpos]; exact him2
          have h3 : (80 : ℝ) ≤ (s / 2)⁻¹ := by
            rw [le_inv_comm₀ (by norm_num) (by positivity)]; linarith
          linarith
        · rw [abs_of_pos hηpos]; exact hNs.trans him1
      have hb := hg₁' z hz
      rw [abs_of_pos hηpos] at hb
      rw [← Wigner_aver_eq D N hD hN1 w a z hηpos, norm_mul, Complex.norm_natCast]
      have hDs : (D : ℝ) ≤ (N : ℝ) ^ (s / 2) := h₅ N hN₅
      have hDr : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      have e : (N : ℝ) ^ s = (N : ℝ) ^ (s / 2) * (N : ℝ) ^ (s / 2) := by
        rw [← Real.rpow_add hN0]; ring_nf
      calc (D : ℝ) * ‖ntr ((res (blockH D N w) z - MExt (0 : Matrix (Idx D N) (Idx D N) ℂ) z) *
              Ea D N a)‖
          ≤ (N : ℝ) ^ (s / 2) * ((N : ℝ) ^ (s / 2) * (1 / ((N : ℝ) * z.im))) := by
            gcongr
        _ = (N : ℝ) ^ s / ((N : ℝ) * z.im) := by rw [e]; ring
    have hcount := h₃ (Fin N) hn₃' 0 Matrix.isHermitian_zero hΛn X hXH
      (by simpa only [Fintype.card_fin] using hLL)
    have hlo : Eminus (0 : Matrix (Fin N) (Fin N) ℂ) -
        (Fintype.card (Fin N) : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s) ≤ eigK X (Fintype.card (Fin N)) := by
      rw [Fintype.card_fin, hE1']
      have := hg₂'.2
      linarith
    have hhi : eigK X 1 ≤ Eplus (0 : Matrix (Fin N) (Fin N) ℂ) +
        (Fintype.card (Fin N) : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s) := by
      rw [Fintype.card_fin, hE1]
      have := hg₂'.1
      linarith
    have hrig := h₄ (Fin N) hn₄' 0 Matrix.isHermitian_zero hΛn X hXH hlo hhi hcount i hi1
      (by rw [Fintype.card_fin]; exact hiN)
    rw [(rho_zero (ι := Fin N)).2.1] at hrig
    simp only [Fintype.card_fin] at hrig
    have hshift := hC₁ N hN1 i hi1 hiN
    have hY : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg (by simp [rk]) _)
    -- `N^{6s} + C₁ ≤ N^{3τ'/4} + C₁ ≤ N^{τ'}`
    have hp1 : (N : ℝ) ^ (3 * (2 * s)) ≤ (N : ℝ) ^ (3 * τ' / 4) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have hp2 : (N : ℝ) ^ τ' = (N : ℝ) ^ (3 * τ' / 4) * (N : ℝ) ^ (τ' / 4) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hp3 : 2 ≤ (N : ℝ) ^ (τ' / 4) := h₆ N hN₆
    have hp4 : C₁ ≤ (N : ℝ) ^ (3 * τ' / 4) := h₇ N hN₇
    have hp5 : 0 ≤ (N : ℝ) ^ (3 * τ' / 4) := Real.rpow_nonneg hN0.le _
    have hsum : (N : ℝ) ^ (3 * (2 * s)) + C₁ ≤ (N : ℝ) ^ τ' := by
      rw [hp2]; nlinarith
    have htot : |eigK X i - quant rhoSc (D * N) (D * i)| ≤
        (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) := by
      calc |eigK X i - quant rhoSc (D * N) (D * i)|
          ≤ |eigK X i - quant rhoSc N i| + |quant rhoSc N i - quant rhoSc (D * N) (D * i)| := by
            have := abs_sub_le (eigK X i) (quant rhoSc N i) (quant rhoSc (D * N) (D * i))
            exact this
        _ ≤ (N : ℝ) ^ (3 * (2 * s)) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) +
              C₁ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) := add_le_add hrig hshift
        _ = ((N : ℝ) ^ (3 * (2 * s)) + C₁) *
              ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) := by ring
        _ ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_right hsum hY
    exact (not_le.mpr hlt) htot
  -- the union bound
  have hpos : 0 ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hN0.le _
  have h2N : 2 * (N : ℝ) ^ (-(D' + 1)) ≤ (N : ℝ) ^ (-D') := by
    have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [show -(D' + 1) = -D' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hD'0 : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
    rw [e]
    have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2r
    nlinarith
  calc blockLaw D N L _ ≤ blockLaw D N L (f ⁻¹' S₁ ∪ f ⁻¹' S₂) := measure_mono hsub
    _ ≤ blockLaw D N L (f ⁻¹' S₁) + blockLaw D N L (f ⁻¹' S₂) := measure_union_le _ _
    _ ≤ (blockLaw D N L).map f S₁ + (blockLaw D N L).map f S₂ :=
        add_le_add (Measure.le_map_apply hae _) (Measure.le_map_apply hae _)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
        add_le_add hμ₁ hμ₂
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D' + 1))) := by
        rw [← ENNReal.ofReal_add hpos hpos, two_mul]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal h2N

end RBMTransitionEdge

end
