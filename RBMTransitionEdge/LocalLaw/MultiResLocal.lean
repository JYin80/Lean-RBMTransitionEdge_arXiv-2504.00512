module

public import RBMTransitionEdge.LocalLaw.LocalLaw
public import RBMTransitionEdge.LocalLaw.MultiRes
public import RBMTransitionEdge.LocalLaw.FarDet

@[expose] public section

/-!
# Lemma A.4 for the class

The multi-resolvent estimates (A.53)–(A.55) of Lemma A.4 [lemma_necessary_estimates] for a sequence
of members of the class, with the local-law hypothesis discharged by Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `Λ(tA) = t Λ(A)` for real `t`, for the interaction `Λ = lam D N A` of (1.3) [matrix_H]. -/
private lemma MRL_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

/-- On the upper half plane `m(z)` and `M(z)` of Definition 2.7 [defn_Mm] extended to both half
planes agree with `mSol` and `MSol`. -/
private lemma MRL_ext_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) {z : ℂ}
    (hz : 0 < z.im) : MExt Λ z = MSol Λ z := by
  have h : mExt Λ z = mSol Λ z := by unfold mExt; simp [hz]
  unfold MExt MSol
  rw [h]

/-- For `N ≥ C₀^{2/δ_A}`, `‖c A_N‖ ≤ C₀ N^{-δ_A} ≤ N^{-δ_A/2}`: the smallness hypothesis of
Lemma 2.9 [lem_loc] with `δ_A / 2` for `c A_N`. -/
private lemma MRL_small (δA C₀ c a : ℝ) (hδA : 0 < δA) (hC₀ : 1 ≤ C₀) (hc : |c| ≤ C₀)
    (N : ℕ) (hN : C₀ ^ (2 / δA) ≤ (N : ℝ)) (ha0 : 0 ≤ a) (ha : a ≤ (N : ℝ) ^ (-δA)) :
    |c| * a ≤ (N : ℝ) ^ (-(δA / 2)) := by
  have hC0 : 0 < C₀ := by linarith
  have hCp : 0 < C₀ ^ (2 / δA) := Real.rpow_pos_of_pos hC0 _
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hCp hN
  have h1 : C₀ ≤ (N : ℝ) ^ (δA / 2) := by
    calc C₀ = (C₀ ^ (2 / δA)) ^ (δA / 2) := by
          rw [← Real.rpow_mul hC0.le]; field_simp; simp
      _ ≤ (N : ℝ) ^ (δA / 2) := Real.rpow_le_rpow hCp.le hN (by positivity)
  have h2 : (N : ℝ) ^ (-δA) = (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(δA / 2)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have h3 : (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (δA / 2) = 1 := by
    rw [← Real.rpow_add hNpos]; simp
  have h4 : 0 < (N : ℝ) ^ (-(δA / 2)) := Real.rpow_pos_of_pos hNpos _
  have h5 : C₀ * (N : ℝ) ^ (-(δA / 2)) ≤ 1 := by
    calc C₀ * (N : ℝ) ^ (-(δA / 2)) ≤ (N : ℝ) ^ (δA / 2) * (N : ℝ) ^ (-(δA / 2)) :=
          mul_le_mul_of_nonneg_right h1 h4.le
      _ = 1 := by rw [mul_comm]; exact h3
  calc |c| * a ≤ C₀ * (N : ℝ) ^ (-δA) :=
        mul_le_mul hc ha ha0 hC0.le
    _ = (C₀ * (N : ℝ) ^ (-(δA / 2))) * (N : ℝ) ^ (-(δA / 2)) := by rw [h2]; ring
    _ ≤ 1 * (N : ℝ) ^ (-(δA / 2)) := mul_le_mul_of_nonneg_right h5 h4.le
    _ = _ := one_mul _

/-- The local-law hypothesis of the conditional pins of Lemma A.4 [lemma_necessary_estimates]
(`entprodG`, `one_loop_estimate`, `two_loop_estimate`), for `Λ_i = c_i Λ`, from (2.22)
[eq:aniso_local] of Lemma 2.9 [lem_loc] applied to `c_i A_N`. -/
private lemma MRL_hLL (D : ℕ) (δA τ C₀ : ℝ) (hτ : 0 < τ) (hC₀ : 1 ≤ C₀) (p : ℕ) (C : ℕ → ℝ)
    (θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (c : ℕ → Fin p → ℝ) (hc : ∀ N i, |c N i| ≤ C₀)
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ Z N, ∀ i, ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
        μ N {ω | (N : ℝ) ^ τ' * psiIso ((c N i : ℂ) • lam D N (A N)) N (z i) <
            ‖star u ⬝ᵥ ((res (Matrix.of ω + (c N i : ℂ) • lam D N (A N)) (z i) -
              MSol ((c N i : ℂ) • lam D N (A N)) (z i)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  have hδA := hs.pos
  obtain ⟨N₀, hN₀⟩ := aniso_local D hs.one_le_D (δA / 2) τ (by linarith) hτ C τ' hτ' D' hD'
  refine ⟨max ⌈C₀ ^ (2 / δA)⌉₊ N₀, fun N hN z hz i u v hu hv => ?_⟩
  have hN1 : C₀ ^ (2 / δA) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) hN)
  have hN2 : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hsmall : opNorm (((c N i : ℝ) : ℂ) • A N) ≤ (N : ℝ) ^ (-(δA / 2)) := by
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h0 : 0 ≤ opNorm (A N) := by unfold opNorm; exact norm_nonneg _
    exact MRL_small δA C₀ (c N i) _ hδA hC₀ (hc N i) N hN1 h0 (hs.small N)
  have h := hN₀ N hN2 (θ N) (hs.theta N).1 (hs.theta N).2 (μ N) (hs.mem N) _ hsmall u v hu hv
  refine le_trans (measure_mono ?_) h
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨hzs, hzpos⟩ := hZ N z hz i
  refine ⟨z i, hzs, ?_⟩
  rw [← MRL_lam_smul, MRL_ext_eq _ hzpos]
  exact hω

/-- `Λ_i = c_i Λ` is Hermitian with `‖Λ_i‖ ≤ 2 C₀ ‖A_N‖ ≤ 1/10`, by `opNorm_lam_le`: the
hypothesis on `Λ_i` of the conditional pins of Lemma A.4 [lemma_necessary_estimates]. -/
private lemma MRL_hΛ (D p : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N, 2 * C₀ * opNorm (A N) ≤ 1 / 10) (c : ℕ → Fin p → ℝ)
    (hc : ∀ N i, |c N i| ≤ C₀) (N : ℕ) (i : Fin p) :
    (((c N i : ℝ) : ℂ) • lam D N (A N)).IsHermitian ∧
      opNorm (((c N i : ℝ) : ℂ) • lam D N (A N)) ≤ 1 / 10 := by
  refine ⟨?_, ?_⟩
  · have h := lam_isHermitian D N (A N)
    unfold Matrix.IsHermitian at h ⊢
    rw [Matrix.conjTranspose_smul, h]
    simp [Complex.conj_ofReal]
  · rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := opNorm_lam_le D N (A N)
    have h2 : 0 ≤ opNorm (A N) := by unfold opNorm; exact norm_nonneg _
    have h3 := hA N
    have h4 := hc N i
    have h5 : 0 ≤ opNorm (lam D N (A N)) := by unfold opNorm; exact norm_nonneg _
    nlinarith [mul_le_mul h4 h1 h5 (by linarith : (0 : ℝ) ≤ C₀)]

/-- (A.53) [entprodG] of Lemma A.4 [lemma_necessary_estimates] for a sequence of members
(`LLSeq`), with `Λ_i = c_i Λ`, `Λ = lam D N A_N`, `|c_i| ≤ C₀`, `2 C₀ ‖A_N‖ ≤ 1/10`, and spectral
tuples with `z_i ∈ 𝐃(τ)` of Definition 3.1 [def_wtM], `Im z_i > 0`, `N η_i Im m_i ≥ c₀`: the
local-law hypothesis (2.22) [eq:aniso_local] is discharged by Lemma 2.9 [lem_loc] for the class. -/
theorem entprodG_local (D p : ℕ) (hp : 1 ≤ p) (δA τ c₀ C₀ : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (θ : ℕ → ℝ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hs : LLSeq D δA C θ μ A)
    (hA : ∀ N, 2 * C₀ * opNorm (A N) ≤ 1 / 10) (c : ℕ → Fin p → ℝ) (hc : ∀ N i, |c N i| ≤ C₀)
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
        μ N {h | (N : ℝ) ^ τ' * bndA4 (fun i => (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
              (fun i => (z i).im) p <
            ‖ntr (resProd (fun i => res (Matrix.of h + (c N i : ℂ) • lam D N (A N)) (z i)) s B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
          μ N {h | (N : ℝ) ^ τ' *
                bndA4 (fun i => (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
                  (fun i => (z i).im) p <
              ‖star u ⬝ᵥ (resProd (fun i => res (Matrix.of h + (c N i : ℂ) • lam D N (A N)) (z i))
                s B *ᵥ v)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  haveI : ∀ N, IsProbabilityMeasure (μ N) := fun N => (hs.mem N).prob
  exact entprodG D p hp τ c₀ hτ hc₀ μ (fun _ ω => Matrix.of ω) (fun N => (hs.mem N).herm)
    (fun N i => ((c N i : ℝ) : ℂ) • lam D N (A N)) (MRL_hΛ D p C₀ hC₀ A hA c hc) Z
    (fun N z hz i => ⟨(hZ N z hz i).2.1, (hZ N z hz i).1.1, (hZ N z hz i).2.2⟩)
    (MRL_hLL D δA τ C₀ hτ hC₀ p C θ μ A hs c hc Z fun N z hz i => ⟨(hZ N z hz i).1,
      (hZ N z hz i).2.1⟩)

/-- (A.54) [one_loop_estimate] of Lemma A.4 [lemma_necessary_estimates], `l ≥ 1`, for a sequence of
members (`LLSeq`), in the setting of `entprodG_local`, with deterministic factors of norm `≤ K` and
`Λ` replaced by `Λ - δ`, `|δ| ≤ K⟨Λ²⟩`: the local-law hypothesis is discharged by Lemma 2.9
[lem_loc] for the class. -/
theorem one_loop_local (D p l : ℕ) (hp : 1 ≤ p) (hl : 1 ≤ l) (δA τ c₀ C₀ K : ℝ) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (hA : ∀ N, 2 * C₀ * opNorm (A N) ≤ 1 / 10)
    (c : ℕ → Fin p → ℝ) (hc : ∀ N i, |c N i| ≤ C₀)
    (δ : ℕ → ℝ) (hδ : ∀ N, |δ N| ≤ K * avgSq (lam D N (A N)))
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ (w : Fin l → Fin p × Bool) (B : Fin (l + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B j) ≤ K) →
        μ N {h | (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N (A N)) *
              bndA4 (fun i => (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
                (fun i => (z i).im) l) <
            ‖ntr (resWord (fun i => res (Matrix.of h + (c N i : ℂ) • lam D N (A N)) (z i)) w B *
              (lam D N (A N) - (δ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  haveI : ∀ N, IsProbabilityMeasure (μ N) := fun N => (hs.mem N).prob
  exact one_loop_estimate D p l hp hl τ c₀ C₀ K hτ hc₀ hC₀ μ (fun _ ω => Matrix.of ω)
    (fun N => (hs.mem N).herm) A hA c hc δ hδ Z
    (fun N z hz i => ⟨(hZ N z hz i).2.1, (hZ N z hz i).1.1, (hZ N z hz i).2.2⟩)
    (MRL_hLL D δA τ C₀ hτ hC₀ p C θ μ A hs c hc Z fun N z hz i => ⟨(hZ N z hz i).1,
      (hZ N z hz i).2.1⟩)

/-- (A.55) [two_loop_estimate] of Lemma A.4 [lemma_necessary_estimates], `l₁ + l₂ ≥ 1`, for a
sequence of members (`LLSeq`), in the setting of `one_loop_local`: the local-law hypothesis is
discharged by Lemma 2.9 [lem_loc] for the class. -/
theorem two_loop_local (D p l₁ l₂ : ℕ) (hp : 1 ≤ p) (hl : 1 ≤ l₁ + l₂) (δA τ c₀ C₀ K : ℝ)
    (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hs : LLSeq D δA C θ μ A) (hA : ∀ N, 2 * C₀ * opNorm (A N) ≤ 1 / 10)
    (c : ℕ → Fin p → ℝ) (hc : ∀ N i, |c N i| ≤ C₀)
    (δ₁ δ₂ : ℕ → ℝ) (hδ₁ : ∀ N, |δ₁ N| ≤ K * avgSq (lam D N (A N)))
    (hδ₂ : ∀ N, |δ₂ N| ≤ K * avgSq (lam D N (A N)))
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ (w₁ : Fin l₁ → Fin p × Bool) (w₂ : Fin l₂ → Fin p × Bool)
        (B₁ : Fin (l₁ + 1) → Matrix (Idx D N) (Idx D N) ℂ)
        (B₂ : Fin (l₂ + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B₁ j) ≤ K) → (∀ j, opNorm (B₂ j) ≤ K) →
        μ N {h | (N : ℝ) ^ τ' * (hsNorm (lam D N (A N)) ^ 2 / N *
              bndA4 (fun i => (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
                (fun i => (z i).im) (l₁ + l₂)) <
            ‖ntr (resWord (fun i => res (Matrix.of h + (c N i : ℂ) • lam D N (A N)) (z i)) w₁ B₁ *
              (lam D N (A N) - (δ₁ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
              resWord (fun i => res (Matrix.of h + (c N i : ℂ) • lam D N (A N)) (z i)) w₂ B₂ *
              (lam D N (A N) - (δ₂ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  haveI : ∀ N, IsProbabilityMeasure (μ N) := fun N => (hs.mem N).prob
  exact two_loop_estimate D p l₁ l₂ hp hl τ c₀ C₀ K hτ hc₀ hC₀ μ (fun _ ω => Matrix.of ω)
    (fun N => (hs.mem N).herm) A hA c hc δ₁ δ₂ hδ₁ hδ₂ Z
    (fun N z hz i => ⟨(hZ N z hz i).2.1, (hZ N z hz i).1.1, (hZ N z hz i).2.2⟩)
    (MRL_hLL D δA τ C₀ hτ hC₀ p C θ μ A hs c hc Z fun N z hz i => ⟨(hZ N z hz i).1,
      (hZ N z hz i).2.1⟩)

end RBMTransitionEdge

end
