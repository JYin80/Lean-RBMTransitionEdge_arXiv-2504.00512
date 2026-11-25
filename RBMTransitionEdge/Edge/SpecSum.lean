module

public import RBMTransitionEdge.Edge.Defs
public import RBMTransitionEdge.Localized.Pathwise
public import RBMTransitionEdge.Tools.ResolventIdentities
public import RBMTransitionEdge.LocalLaw.FarDet

@[expose] public section

/-!
# The spectral sums of the proof of Lemma 4.3

The traces `X` and `Y` of (4.17) [GEaD1] and (4.18) [GEaD2], their eigenbasis form, the gap below
the window behind (4.19) [GEaD3] (with `ε ≥ 2σ`, E30), and the bounds (4.19)–(4.20) under
rigidity and the eigenvector bound.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `⟨Im G(z₁) (D⁻¹ - E_a) Im G(z₂) E_a⟩`, the trace in `X(i, j; a)` of the proof of Lemma 4.3
[rescomY] and the left side of (4.17) [GEaD1]. -/
def edgeXterm (D N : ℕ) (X : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a : Fin D) : ℂ :=
  ntr (imRes X z₁ * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *
    imRes X z₂ * Ea D N a)

/-- `⟨Im G(z) (D⁻¹ - E_a)⟩`, the left side of (4.18) [GEaD2]. -/
def edgeYterm (D N : ℕ) (X : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (a : Fin D) : ℂ :=
  ntr (imRes X z * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a))

section Part1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma SpecSum_imRes_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    imRes X z = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun k => ((z.im / ‖(hX.eigenvalues k : ℂ) - z‖ ^ 2 : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix ι ι ℂ) := by
  ext i j
  have h := imRes_eq_sum_eig X hX z hz i j
  change ((2 * Complex.I)⁻¹ • (res X z - (res X z)ᴴ)) i j = _
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  simp only [Complex.star_def]
  ring

omit [DecidableEq ι] in
private lemma SpecSum_sandwich (U M : Matrix ι ι ℂ) (r s : ι) :
    (star U * M * U) r s = star (fun x => U x r) ⬝ᵥ (M *ᵥ fun x => U x s) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

private lemma SpecSum_trace4 (U B E : Matrix ι ι ℂ) (d₁ d₂ : ι → ℂ) :
    ((U * Matrix.diagonal d₁ * star U) * B * (U * Matrix.diagonal d₂ * star U) * E).trace =
      ∑ r, ∑ s, d₁ r * (star U * B * U) r s * (d₂ s * (star U * E * U) s r) := by
  have h1 : ((U * Matrix.diagonal d₁ * star U) * B * (U * Matrix.diagonal d₂ * star U) * E) =
      U * ((Matrix.diagonal d₁ * (star U * B * U)) *
        (Matrix.diagonal d₂ * (star U * E))) := by
    simp only [Matrix.mul_assoc]
  have h2 : ((Matrix.diagonal d₁ * (star U * B * U)) * (Matrix.diagonal d₂ * (star U * E))) * U =
      (Matrix.diagonal d₁ * (star U * B * U)) * (Matrix.diagonal d₂ * (star U * E * U)) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, h2]
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul]

private lemma SpecSum_trace2 (U B : Matrix ι ι ℂ) (d : ι → ℂ) :
    ((U * Matrix.diagonal d * star U) * B).trace = ∑ r, d r * (star U * B * U) r r := by
  have h1 : ((U * Matrix.diagonal d * star U) * B) = U * (Matrix.diagonal d * (star U * B)) := by
    simp only [Matrix.mul_assoc]
  have h2 : (Matrix.diagonal d * (star U * B)) * U = Matrix.diagonal d * (star U * B * U) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, h2]
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.diagonal_mul]
end Part1

/-- (4.17) [GEaD1] and (4.18) [GEaD2]: the spectral decompositions of the two traces in an
orthonormal eigenbasis `(v_r)` of a Hermitian `X`, for `Im z₁, Im z₂ > 0`. -/
theorem edgeTerm_eq_sum {D N : ℕ} (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (a : Fin D) :
    edgeXterm D N X z₁ z₂ a = (((D * N : ℕ) : ℂ))⁻¹ * ∑ r, ∑ s,
        (((z₁.im / ‖(hX.eigenvalues r : ℂ) - z₁‖ ^ 2) *
          (z₂.im / ‖(hX.eigenvalues s : ℂ) - z₂‖ ^ 2) : ℝ) : ℂ) *
        (star (fun x => (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ) x r) ⬝ᵥ
          ((((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *ᵥ
            fun x => (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ) x s)) *
        (star (fun x => (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ) x s) ⬝ᵥ
          (Ea D N a *ᵥ fun x => (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ) x r)) ∧
    edgeYterm D N X z₁ a = (((D * N : ℕ) : ℂ))⁻¹ * ∑ r,
        ((z₁.im / ‖(hX.eigenvalues r : ℂ) - z₁‖ ^ 2 : ℝ) : ℂ) *
        (star (fun x => (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ) x r) ⬝ᵥ
          ((((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *ᵥ
            fun x => (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ) x r)) := by
  have hcard : Fintype.card (Idx D N) = D * N := by simp [Idx]
  refine ⟨?_, ?_⟩
  · unfold edgeXterm ntr
    rw [SpecSum_imRes_eq X hX z₁ hz₁, SpecSum_imRes_eq X hX z₂ hz₂]
    rw [SpecSum_trace4 (hX.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ)]
    rw [hcard]
    refine congrArg (fun t => (((D * N : ℕ) : ℂ))⁻¹ * t) ?_
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [SpecSum_sandwich, SpecSum_sandwich]
    push_cast
    ring
  · unfold edgeYterm ntr
    rw [SpecSum_imRes_eq X hX z₁ hz₁, SpecSum_trace2, hcard]
    refine congrArg (fun t => (((D * N : ℕ) : ℂ))⁻¹ * t) ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [SpecSum_sandwich]

section Part2

private lemma SpecSum_gap_core {cs σ τ' n ρ rk : ℝ} (hcs : 0 < cs) (hσ : 0 < σ) (hn : 1 ≤ n)
    (hρ : n ^ (2 * σ) < ρ) (hrk : ρ ≤ 2 * rk)
    (h1 : n ^ (-(σ / 3)) ≤ cs / 4) (h2 : n ^ (τ' - 2 * σ) ≤ cs / 8) :
    n ^ (-(2 / 3 : ℝ) + σ) + n ^ τ' * (n ^ (-(2 / 3 : ℝ)) * rk ^ (-(1 / 3 : ℝ))) ≤
      cs / 2 * (ρ ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ))) := by
  have hn0 : 0 < n := by linarith
  have hnσ : 1 ≤ n ^ (2 * σ) := Real.one_le_rpow hn (by linarith)
  have hρ0 : 0 < ρ := by linarith
  set s := ρ ^ (-(1 / 3 : ℝ)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hρ0 _
  have hρ23 : ρ ^ (2 / 3 : ℝ) = ρ * s := by
    rw [hs, ← Real.rpow_one_add' hρ0.le (by norm_num)]
    norm_num
  have hnm : 0 < n ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hρ23' : n ^ (4 * σ / 3) < ρ ^ (2 / 3 : ℝ) := by
    have := Real.rpow_lt_rpow (by positivity) hρ (by norm_num : (0 : ℝ) < 2 / 3)
    rwa [← Real.rpow_mul hn0.le, show 2 * σ * (2 / 3) = 4 * σ / 3 by ring] at this
  have hT1 : n ^ (-(2 / 3 : ℝ) + σ) ≤ cs / 4 * (ρ ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ))) := by
    have e : n ^ (-(2 / 3 : ℝ) + σ) = n ^ (-(σ / 3)) * n ^ (4 * σ / 3) * n ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring
    rw [e]
    have a1 : n ^ (-(σ / 3)) * n ^ (4 * σ / 3) ≤ cs / 4 * ρ ^ (2 / 3 : ℝ) :=
      calc _ ≤ (cs / 4) * n ^ (4 * σ / 3) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hρ23'.le (by positivity)
    calc _ ≤ (cs / 4 * ρ ^ (2 / 3 : ℝ)) * n ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right a1 hnm.le
      _ = _ := by ring
  have hT2 : n ^ τ' * (n ^ (-(2 / 3 : ℝ)) * rk ^ (-(1 / 3 : ℝ))) ≤
      cs / 4 * (ρ ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ))) := by
    have hrk' : rk ^ (-(1 / 3 : ℝ)) ≤ 2 * s := by
      have a : rk ^ (-(1 / 3 : ℝ)) ≤ (ρ / 2) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      refine a.trans ?_
      rw [Real.div_rpow hρ0.le (by norm_num), ← hs]
      have b : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-1 : ℝ) ≤ -(1 / 3))
        simpa [Real.rpow_neg_one] using this
      have c2 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
      rw [div_le_iff₀ c2]
      nlinarith
    have hnt : n ^ τ' ≤ cs / 8 * ρ := by
      have : n ^ τ' = n ^ (τ' - 2 * σ) * n ^ (2 * σ) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      rw [this]
      calc _ ≤ (cs / 8) * n ^ (2 * σ) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hρ.le (by positivity)
    calc n ^ τ' * (n ^ (-(2 / 3 : ℝ)) * rk ^ (-(1 / 3 : ℝ)))
        ≤ n ^ τ' * (n ^ (-(2 / 3 : ℝ)) * (2 * s)) := by gcongr
      _ = (2 * n ^ τ') * (n ^ (-(2 / 3 : ℝ)) * s) := by ring
      _ ≤ (cs / 4 * ρ) * (n ^ (-(2 / 3 : ℝ)) * s) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [hρ23]; ring
  linarith

/-- `λ_k` decreases in `k ∈ ⟦1, card ι⟧` (a non-Hermitian matrix has `λ_k = 0`). -/
private lemma SpecSum_eigK_anti {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    {j k : ℕ} (hjk : j ≤ k) (hj : 1 ≤ j) (hk : k ≤ Fintype.card ι) : eigK X k ≤ eigK X j := by
  have hj' : j - 1 < Fintype.card ι := by omega
  have hk' : k - 1 < Fintype.card ι := by omega
  unfold eigK
  simp only [hj', hk', ↓reduceDIte]
  unfold eigs
  by_cases h : X.IsHermitian
  · simp only [h, ↓reduceDIte]
    exact h.eigenvalues₀_antitone (Fin.mk_le_mk.2 (by omega))
  · simp [h]

/-- The index `k ∈ ⟦1, DN⟧` with `2k ≤ DN + 2` has `𝔯(k) ≥ k/2` and `𝔯(k) > 0`. -/
private lemma SpecSum_rk_ge (D N k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ D * N) (h2 : 2 * k ≤ D * N + 2) :
    0 < rk D N k ∧ (k : ℝ) ≤ 2 * rk D N k := by
  unfold rk
  have h : 1 ≤ min k (D * N + 1 - k) ∧ k ≤ 2 * min k (D * N + 1 - k) := by
    generalize D * N = m at hk2 h2
    omega
  obtain ⟨h1, h3⟩ := h
  refine ⟨by exact_mod_cast h1, ?_⟩
  exact_mod_cast h3

/-- The one-index gap: for `N^{2σ} < k`, `2k ≤ DN + 2`, with the lower constant `c_*` of (2.21)
[eq:kappa_gamma_k], rigidity with loss `N^{τ'}` and `E` in the window,
`E - λ_k ≥ (c_*/2)(k/N)^{2/3}`. -/
private lemma SpecSum_gap_idx {D N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {τ' σ cs E : ℝ}
    {X : Matrix (Idx D N) (Idx D N) ℂ} (hrig : IsRigid D N A τ' X) (hcs : 0 < cs) (hσ : 0 < σ)
    (hN : 1 ≤ (N : ℝ))
    (hwin : |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ D * N) (h2k : 2 * k ≤ D * N + 2)
    (hk : (N : ℝ) ^ (2 * σ) < k)
    (hkg : cs * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      Eplus (lam D N A) - quant (rho (lam D N A)) (D * N) k)
    (h1 : (N : ℝ) ^ (-(σ / 3)) ≤ cs / 4) (h2 : (N : ℝ) ^ (τ' - 2 * σ) ≤ cs / 8) :
    cs / 2 * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ E - eigK X k := by
  obtain ⟨hrk0, hrk⟩ := SpecSum_rk_ge D N k hk1 hk2 h2k
  have hcore := SpecSum_gap_core (cs := cs) (σ := σ) (τ' := τ') (n := (N : ℝ)) (ρ := (k : ℝ))
    (rk := rk D N k) hcs hσ hN hk hrk h1 h2
  have hr := hrig k hk1 hk2
  have hw := (abs_le.1 hwin).1
  have hr' := (abs_le.1 hr).2
  linarith

end Part2

/-- The gap used in (4.19) [GEaD3]: if the eigenvalues satisfy (2.24) [eq:rigidity] with loss
`N^{τ'}`, `τ' < 2σ`, and `|E - E⁺| ≤ N^{-2/3+σ}`, then `E - λ_r ≥ c₀ (r/N)^{2/3}` for every
`r > N^{2σ}`, with `c₀` from (2.21) [eq:kappa_gamma_k]. -/
theorem edge_gap_lower (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ σ τ' : ℝ, 0 < σ → 0 < τ' → τ' < 2 * σ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ X : Matrix (Idx D N) (Idx D N) ℂ, IsRigid D N A τ' X →
      ∀ E : ℝ, |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) →
      ∀ r : ℕ, (N : ℝ) ^ (2 * σ) < r → r ≤ D * N →
        c₀ * ((r : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ E - eigK X r := by
  obtain ⟨cs, C, hcs, -, N₁, hN₁⟩ := kappa_gamma_k D hD δA hδA
  refine ⟨cs / 4, by positivity, fun σ τ' hσ hτ' hτσ => ?_⟩
  have hev : ∀ᶠ N : ℕ in atTop, N₁ ≤ N ∧ 1 ≤ N ∧ (N : ℝ) ^ (-(σ / 3)) ≤ cs / 4 ∧
      (N : ℝ) ^ (τ' - 2 * σ) ≤ cs / 8 ∧ (1 / 2 < σ → (D : ℝ) * N ≤ (N : ℝ) ^ (2 * σ)) := by
    refine (eventually_ge_atTop N₁).and ((eventually_ge_atTop 1).and ?_)
    refine Eventually.and ?_ (Eventually.and ?_ ?_)
    · exact ((tendsto_rpow_neg_atTop (by positivity : 0 < σ / 3)).comp
        tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds (by positivity))
    · have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * σ - τ')).comp
        tendsto_natCast_atTop_atTop
      refine (h.eventually (ge_mem_nhds (by positivity : 0 < cs / 8))).mono fun N hN => ?_
      have e : τ' - 2 * σ = -(2 * σ - τ') := by ring
      rw [e]
      exact hN
    · by_cases hσ2 : 1 / 2 < σ
      · have h := (tendsto_rpow_atTop (by linarith : 0 < 2 * σ - 1)).comp
          tendsto_natCast_atTop_atTop
        refine ((h.eventually_ge_atTop (D : ℝ)).and (eventually_ge_atTop 1)).mono
          fun N hN _ => ?_
        obtain ⟨hN1, hN2⟩ := hN
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hN2
        have e : (N : ℝ) ^ (2 * σ) = (N : ℝ) ^ (2 * σ - 1) * N := by
          rw [← Real.rpow_add_one hN0.ne']
          congr 1
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right hN1 hN0.le
      · exact Eventually.of_forall fun N h => absurd h hσ2
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
  refine ⟨N₂, fun N hN A hA X hrig E hE r hr hrN => ?_⟩
  obtain ⟨hN1, hN1', h1, h2, h3⟩ := hN₂ N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNpos : (0 : ℝ) < N := by linarith
  have hcard : Fintype.card (Idx D N) = D * N := by simp [Idx]
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_le_of_lt (by positivity) hr
    exact_mod_cast this
  have hkg := fun k (hk1 : 1 ≤ k) (hk2 : k ≤ D * N) => (hN₁ N hN1 A hA k hk1 hk2).1
  have hσ2 : σ ≤ 1 / 2 := by
    by_contra hcon
    have := h3 (lt_of_not_ge hcon)
    have hrle : (r : ℝ) ≤ D * N := by exact_mod_cast hrN
    linarith
  have hDN : 2 * N ≤ D * N := Nat.mul_le_mul_right N hD
  have hpow : (N : ℝ) ^ (2 * σ) ≤ N := by
    calc (N : ℝ) ^ (2 * σ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = N := Real.rpow_one _
  by_cases hrr : r ≤ D * N / 2 + 1
  · have := SpecSum_gap_idx (hrig := hrig) hcs hσ hNr hE hr1 hrN (by omega) hr (hkg r hr1 hrN) h1 h2
    have hP : 0 ≤ (r : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    nlinarith
  · replace hrr := not_le.1 hrr
    set r₁ := D * N / 2 + 1 with hr₁
    have hr₁1 : 1 ≤ r₁ := by omega
    have hr₁2 : r₁ ≤ D * N := by omega
    have hr₁σ : (N : ℝ) ^ (2 * σ) < r₁ := by
      have : (N : ℝ) + 1 ≤ r₁ := by exact_mod_cast (by omega : N + 1 ≤ r₁)
      linarith
    have h5 := SpecSum_gap_idx (hrig := hrig) hcs hσ hNr hE hr₁1 hr₁2 (by omega) hr₁σ
      (hkg r₁ hr₁1 hr₁2) h1 h2
    have h6 : eigK X r ≤ eigK X r₁ := SpecSum_eigK_anti X hrr.le hr₁1 (by rw [hcard]; exact hrN)
    have h7 : (r : ℝ) ^ (2 / 3 : ℝ) ≤ 2 * (r₁ : ℝ) ^ (2 / 3 : ℝ) := by
      have h8 : (r : ℝ) ≤ 2 * r₁ := by exact_mod_cast (by omega : r ≤ 2 * r₁)
      calc (r : ℝ) ^ (2 / 3 : ℝ) ≤ (2 * (r₁ : ℝ)) ^ (2 / 3 : ℝ) :=
            Real.rpow_le_rpow (by positivity) h8 (by norm_num)
        _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (r₁ : ℝ) ^ (2 / 3 : ℝ) :=
            Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * (r₁ : ℝ) ^ (2 / 3 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one _
    have hnn : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    have h9 : cs / 4 * ((r : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
        cs / 2 * ((r₁ : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
      have : (r : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          2 * ((r₁ : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
        nlinarith
      nlinarith
    linarith

section Part3a

/-- `Σ_{k ≥ 1} k^{-4/3}`, the constant of the sum of the weights. -/
private def SpecSum_Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (4 / 3 : ℝ))⁻¹

private lemma SpecSum_Z_summable : Summable fun n : ℕ => ((n : ℝ) ^ (4 / 3 : ℝ))⁻¹ :=
  Real.summable_nat_rpow_inv.2 (by norm_num)

private lemma SpecSum_Z_nonneg : 0 ≤ SpecSum_Z :=
  tsum_nonneg fun n => by positivity

/-- The partial sums of `k^{-4/3}` over `⟦1, M⟧` are at most `SpecSum_Z`. -/
private lemma SpecSum_Z_le (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ ≤ SpecSum_Z := by
  refine (Summable.sum_le_tsum (Finset.Icc 1 M) (fun n _ => by positivity)
    SpecSum_Z_summable)

/-- The one-step estimate behind the tail bound: `(x+1)^{-4/3} ≤ 3 (x^{-1/3} - (x+1)^{-1/3})`. -/
private lemma SpecSum_step (x : ℝ) (hx : 1 ≤ x) :
    (x + 1) ^ (4 / 3 : ℝ) ≠ 0 ∧ (((x + 1) ^ (4 / 3 : ℝ))⁻¹) ≤
      3 * ((x ^ (1 / 3 : ℝ))⁻¹ - ((x + 1) ^ (1 / 3 : ℝ))⁻¹) := by
  have hx0 : 0 < x := by linarith
  set a := x ^ (1 / 3 : ℝ) with ha
  set b := (x + 1) ^ (1 / 3 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by linarith) _
  have hab : a ≤ b := Real.rpow_le_rpow hx0.le (by linarith) (by norm_num)
  have ha3 : a ^ 3 = x := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hb3 : b ^ 3 = x + 1 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hb4 : (x + 1) ^ (4 / 3 : ℝ) = b ^ 4 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  rw [hb4]
  refine ⟨by positivity, ?_⟩
  have h1 : (b - a) * (b ^ 2 + a * b + a ^ 2) = 1 := by nlinarith
  have h2 : a ≤ 3 * (b - a) * b ^ 3 := by
    calc a = a * ((b - a) * (b ^ 2 + a * b + a ^ 2)) := by rw [h1, mul_one]
      _ = (b - a) * (a * (b ^ 2 + a * b + a ^ 2)) := by ring
      _ ≤ (b - a) * (3 * b ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        nlinarith [mul_pos ha0 hb0, mul_nonneg (sub_nonneg.2 hab) ha0.le,
          mul_nonneg (sub_nonneg.2 hab) hb0.le, mul_pos hb0 hb0]
      _ = 3 * (b - a) * b ^ 3 := by ring
  have e : 3 * (a⁻¹ - b⁻¹) = 3 * (b - a) / (a * b) := by field_simp
  rw [e, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hb0.le]

/-- The tail of `Σ k^{-4/3}`: `Σ_{m < k ≤ M} k^{-4/3} ≤ 3 m^{-1/3}` for `m ≥ 1`. -/
private lemma SpecSum_tail (m : ℕ) (hm : 1 ≤ m) (M : ℕ) :
    ∑ k ∈ Finset.Ioc m M, ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ ≤ 3 * ((m : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  rcases lt_or_ge M m with hlt | hge
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have key : ∑ k ∈ Finset.Ioc m M, ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ ≤
        3 * (((m : ℝ) ^ (1 / 3 : ℝ))⁻¹ - ((M : ℝ) ^ (1 / 3 : ℝ))⁻¹) := by
      induction M, hge using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        have := (SpecSum_step (M : ℝ) (by exact_mod_cast (hm.trans hM))).2
        push_cast
        linarith
    have : 0 ≤ ((M : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by positivity
    linarith

/-- A weight is at most `η⁻¹`. -/
private lemma SpecSum_wt_le_inv (l E : ℝ) {η : ℝ} (hη : 0 < η) :
    η / ((l - E) ^ 2 + η ^ 2) ≤ η⁻¹ := by
  calc η / ((l - E) ^ 2 + η ^ 2) ≤ η / η ^ 2 :=
        div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith [sq_nonneg (l - E)])
    _ = η⁻¹ := by field_simp

/-- A weight at distance at least `g > 0` from the spectral point is at most `η / g²`. -/
private lemma SpecSum_wt_far {l E η g : ℝ} (hη : 0 < η) (hg : 0 < g) (h : g ≤ E - l) :
    η / ((l - E) ^ 2 + η ^ 2) ≤ η / g ^ 2 := by
  have h1 : g ^ 2 ≤ (l - E) ^ 2 := by
    have := pow_le_pow_left₀ hg.le h 2
    nlinarith
  exact div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith [sq_nonneg η])

/-- `η / (c₀ (k^{2/3} n^{-2/3}))² = η (c₀²)⁻¹ n^{4/3} (k^{4/3})⁻¹`. -/
private lemma SpecSum_inv_sq {c₀ n : ℝ} {k : ℕ} (hc₀ : 0 < c₀) (hn0 : 0 < n) (hk : 1 ≤ k)
    (η : ℝ) :
    η / (c₀ * ((k : ℝ) ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ)))) ^ 2 =
      η * (c₀ ^ 2)⁻¹ * n ^ (4 / 3 : ℝ) * ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have e1 : ((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (k : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have e2 : (n ^ (-(2 / 3 : ℝ))) ^ 2 = (n ^ (4 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, show -(2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(4 / 3) by
      norm_num, Real.rpow_neg hn0.le]
  have p1 : 0 < (k : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hk0 _
  have p2 : 0 < n ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hn0 _
  rw [mul_pow, mul_pow, e1, e2]
  field_simp


/-- The pointwise bound used in both sums: for `N^{2σ} < k ≤ DN`, the weight is at most
`η (c₀²)⁻¹ N^{4/3} (k^{4/3})⁻¹`. -/
private lemma SpecSum_wt_pt {N : ℕ} {ev : ℕ → ℝ} {c₀ E η : ℝ} {k : ℕ} (hc₀ : 0 < c₀)
    (hN : 1 ≤ (N : ℝ)) (hη : 0 < η) (hk : 1 ≤ k)
    (hgap : c₀ * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ E - ev k) :
    η / ((ev k - E) ^ 2 + η ^ 2) ≤
      η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) * ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < N := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hg : 0 < c₀ * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by positivity
  rw [← SpecSum_inv_sq hc₀ hn0 hk η]
  exact SpecSum_wt_far hη hg hgap

/-- The sum of all weights: `Σ_k η/((λ_k - E)² + η²) ≤ (1 + c₀⁻² Z) N^{2/3+σ+ε}` for `ε ≥ 2σ`,
`η = N^{-2/3-σ}`, when `E - λ_k ≥ c₀ (k/N)^{2/3}` for `k > N^{2σ}`. -/
private lemma SpecSum_wsum_all {N M : ℕ} {ev : ℕ → ℝ} {c₀ σ ε E η : ℝ} (hc₀ : 0 < c₀)
    (hσ : 0 < σ) (hσε : 2 * σ ≤ ε) (hN : 1 ≤ (N : ℝ))
    (hη : η = (N : ℝ) ^ (-(2 / 3 : ℝ) - σ))
    (hgap : ∀ k : ℕ, (N : ℝ) ^ (2 * σ) < k → k ≤ M →
      c₀ * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ E - ev k) :
    ∑ k ∈ Finset.Icc 1 M, η / ((ev k - E) ^ 2 + η ^ 2) ≤
      (1 + (c₀ ^ 2)⁻¹ * SpecSum_Z) * (N : ℝ) ^ (2 / 3 + σ + ε) := by
  have hn0 : (0 : ℝ) < N := by linarith
  have hηp : 0 < η := by rw [hη]; positivity
  have hinv : η⁻¹ = (N : ℝ) ^ (2 / 3 + σ) := by
    rw [hη, ← Real.rpow_neg hn0.le]
    congr 1
    ring
  have hprod : η * (N : ℝ) ^ (4 / 3 : ℝ) = (N : ℝ) ^ (2 / 3 - σ) := by
    rw [hη, ← Real.rpow_add hn0]
    congr 1
    ring
  have hpt : ∀ k ∈ Finset.Icc 1 M, η / ((ev k - E) ^ 2 + η ^ 2) ≤
      (if (k : ℝ) ≤ (N : ℝ) ^ ε then η⁻¹ else 0) +
        η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) * ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
    intro k hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.1 hk
    have hpos : 0 ≤ η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) * ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
      positivity
    by_cases hkε : (k : ℝ) ≤ (N : ℝ) ^ ε
    · simp only [hkε, ↓reduceIte]
      linarith [SpecSum_wt_le_inv (ev k) E hηp]
    · simp only [hkε, ↓reduceIte, zero_add]
      have hlt : (N : ℝ) ^ (2 * σ) < k :=
        lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hN hσε) (not_le.1 hkε)
      exact SpecSum_wt_pt hc₀ hN hηp hk1 (hgap k hlt hkM)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcard : ∑ k ∈ Finset.Icc 1 M, (if (k : ℝ) ≤ (N : ℝ) ^ ε then η⁻¹ else 0) ≤
      (N : ℝ) ^ ε * η⁻¹ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hsub : (Finset.Icc 1 M).filter (fun k : ℕ => (k : ℝ) ≤ (N : ℝ) ^ ε) ⊆
        Finset.Icc 1 ⌊(N : ℝ) ^ ε⌋₊ := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      exact Finset.mem_Icc.2 ⟨hk.1.1, Nat.le_floor hk.2⟩
    calc (((Finset.Icc 1 M).filter (fun k : ℕ => (k : ℝ) ≤ (N : ℝ) ^ ε)).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊(N : ℝ) ^ ε⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = ⌊(N : ℝ) ^ ε⌋₊ := by simp
      _ ≤ (N : ℝ) ^ ε := Nat.floor_le (by positivity)
  have hZ := SpecSum_Z_le M
  have hc : 0 ≤ η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) := by positivity
  have h2 : η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) *
      ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ ≤
      (c₀ ^ 2)⁻¹ * SpecSum_Z * (N : ℝ) ^ (2 / 3 - σ) := by
    calc _ ≤ η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) * SpecSum_Z :=
          mul_le_mul_of_nonneg_left hZ hc
      _ = (c₀ ^ 2)⁻¹ * SpecSum_Z * (η * (N : ℝ) ^ (4 / 3 : ℝ)) := by ring
      _ = _ := by rw [hprod]
  have h3 : (N : ℝ) ^ ε * η⁻¹ = (N : ℝ) ^ (2 / 3 + σ + ε) := by
    rw [hinv, mul_comm, ← Real.rpow_add hn0]
  have h4 : (N : ℝ) ^ (2 / 3 - σ) ≤ (N : ℝ) ^ (2 / 3 + σ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h5 : 0 ≤ (c₀ ^ 2)⁻¹ * SpecSum_Z := by
    have := SpecSum_Z_nonneg
    positivity
  calc _ ≤ (N : ℝ) ^ ε * η⁻¹ + (c₀ ^ 2)⁻¹ * SpecSum_Z * (N : ℝ) ^ (2 / 3 - σ) := by
        linarith
    _ ≤ (N : ℝ) ^ (2 / 3 + σ + ε) + (c₀ ^ 2)⁻¹ * SpecSum_Z * (N : ℝ) ^ (2 / 3 + σ + ε) := by
        rw [h3]
        have := mul_le_mul_of_nonneg_left h4 h5
        linarith
    _ = _ := by ring

/-- The sum of the weights of the indices `k > N^c + 1`: at most `3 c₀⁻² N^{2/3-σ-c/3}`. -/
private lemma SpecSum_wsum_far {N M : ℕ} {ev : ℕ → ℝ} {c₀ σ ε c E η : ℝ} (hc₀ : 0 < c₀)
    (hσε : 2 * σ ≤ ε) (hεc : ε < c) (hN : 1 ≤ (N : ℝ))
    (hη : η = (N : ℝ) ^ (-(2 / 3 : ℝ) - σ))
    (hgap : ∀ k : ℕ, (N : ℝ) ^ (2 * σ) < k → k ≤ M →
      c₀ * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ E - ev k) :
    ∑ k ∈ (Finset.Icc 1 M).filter (fun k : ℕ => (N : ℝ) ^ c + 1 < k),
        η / ((ev k - E) ^ 2 + η ^ 2) ≤ 3 * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (2 / 3 - σ - c / 3) := by
  have hn0 : (0 : ℝ) < N := by linarith
  have hηp : 0 < η := by rw [hη]; positivity
  have hprod : η * (N : ℝ) ^ (4 / 3 : ℝ) = (N : ℝ) ^ (2 / 3 - σ) := by
    rw [hη, ← Real.rpow_add hn0]
    congr 1
    ring
  have hNc : (N : ℝ) ^ (2 * σ) ≤ (N : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hpt : ∀ k ∈ (Finset.Icc 1 M).filter (fun k : ℕ => (N : ℝ) ^ c + 1 < k),
      η / ((ev k - E) ^ 2 + η ^ 2) ≤
        η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) * ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkM⟩, hkc⟩ := hk
    exact SpecSum_wt_pt hc₀ hN hηp hk1 (hgap k (by linarith) hkM)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  set m := ⌊(N : ℝ) ^ c⌋₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmN : (N : ℝ) ^ c < m := by
    rw [hm]
    push_cast
    exact Nat.lt_floor_add_one _
  have hsub : (Finset.Icc 1 M).filter (fun k : ℕ => (N : ℝ) ^ c + 1 < k) ⊆ Finset.Ioc m M := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkM⟩, hkc⟩ := hk
    refine Finset.mem_Ioc.2 ⟨?_, hkM⟩
    have h1 : (m : ℝ) < k := by
      have : (⌊(N : ℝ) ^ c⌋₊ : ℝ) ≤ (N : ℝ) ^ c := Nat.floor_le (by positivity)
      rw [hm]
      push_cast
      linarith
    exact_mod_cast h1
  have h1 : ∑ k ∈ (Finset.Icc 1 M).filter (fun k : ℕ => (N : ℝ) ^ c + 1 < k),
      ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ ≤ ∑ k ∈ Finset.Ioc m M, ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
  have h2 := SpecSum_tail m hm1 M
  have h3 : ((m : ℝ) ^ (1 / 3 : ℝ))⁻¹ ≤ (N : ℝ) ^ (-(c / 3)) := by
    have hNc0 : 0 < (N : ℝ) ^ c := Real.rpow_pos_of_pos hn0 _
    have : (N : ℝ) ^ (c / 3) ≤ (m : ℝ) ^ (1 / 3 : ℝ) := by
      calc (N : ℝ) ^ (c / 3) = ((N : ℝ) ^ c) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_mul hn0.le]; congr 1; ring
        _ ≤ (m : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hNc0.le hmN.le (by norm_num)
    rw [Real.rpow_neg hn0.le]
    exact inv_anti₀ (by positivity) this
  have hc1 : 0 ≤ η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) := by positivity
  calc η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) *
        ∑ k ∈ (Finset.Icc 1 M).filter (fun k : ℕ => (N : ℝ) ^ c + 1 < k),
          ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹
      ≤ η * (c₀ ^ 2)⁻¹ * (N : ℝ) ^ (4 / 3 : ℝ) * (3 * (N : ℝ) ^ (-(c / 3))) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans (by linarith))) hc1
    _ = 3 * (c₀ ^ 2)⁻¹ * (η * (N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (-(c / 3))) := by ring
    _ = _ := by
        rw [hprod, ← Real.rpow_add hn0]
        congr 2

end Part3a

section Part3b

/-- Cauchy–Schwarz for unit vectors. -/
private lemma SpecSum_dot_le {ι : Type*} [Fintype ι] (u w : ι → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1)
    (hw : ∑ i, ‖w i‖ ^ 2 ≤ 1) : ‖star u ⬝ᵥ w‖ ≤ 1 := by
  have h1 : ‖star u ⬝ᵥ w‖ ≤ ∑ i, ‖u i‖ * ‖w i‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have h2 : ∑ i, ‖u i‖ * ‖w i‖ ≤ ∑ i, (‖u i‖ ^ 2 + ‖w i‖ ^ 2) / 2 :=
    Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (‖u i‖ - ‖w i‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hu] at h2
  linarith

/-- `‖u^* E_a w‖ ≤ 1` for unit vectors. -/
private lemma SpecSum_dotE_le (D N : ℕ) (a : Fin D) (u w : Idx D N → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hw : ∑ i, ‖w i‖ ^ 2 = 1) :
    ‖star u ⬝ᵥ (Ea D N a *ᵥ w)‖ ≤ 1 := by
  have e : Ea D N a *ᵥ w = fun p => if p.1 = a then w p else 0 := by
    funext p
    simp [Ea, Matrix.mulVec_diagonal]
  rw [e]
  refine SpecSum_dot_le u _ hu ?_
  refine le_of_le_of_eq (Finset.sum_le_sum fun p _ => ?_) hw
  by_cases h : p.1 = a <;> simp [h]

/-- `‖u^* (D⁻¹ - E_a) w‖ ≤ 2` for unit vectors. -/
private lemma SpecSum_dotB_le (D N : ℕ) (hD : 2 ≤ D) (a : Fin D) (u w : Idx D N → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hw : ∑ i, ‖w i‖ ^ 2 = 1) :
    ‖star u ⬝ᵥ ((((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *ᵥ w)‖ ≤ 2 := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(D : ℂ)⁻¹ • (star u ⬝ᵥ w)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
    have := SpecSum_dot_le u w hu hw.le
    calc (D : ℝ)⁻¹ * ‖star u ⬝ᵥ w‖ ≤ 1 * 1 := by
          refine mul_le_mul (inv_le_one_of_one_le₀ hD1) this (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h2 := SpecSum_dotE_le D N a u w hu hw
  linarith

section Eig

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The columns of the eigenvector unitary are unit vectors. -/
private lemma SpecSum_col_unit (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (r : ι) :
    ∑ x, ‖(hX.eigenvectorUnitary : Matrix ι ι ℂ) x r‖ ^ 2 = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.1 (hX.eigenvectorUnitary).property
  have h1 := congrFun (congrFun h r) r
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h1
  have h2 : ((∑ x, ‖(hX.eigenvectorUnitary : Matrix ι ι ℂ) x r‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast h2

/-- The columns of the eigenvector unitary are eigenvectors for the eigenvalues
`hX.eigenvalues r`. -/
private lemma SpecSum_col_eig (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (r : ι) :
    X *ᵥ (fun x => (hX.eigenvectorUnitary : Matrix ι ι ℂ) x r) =
      ((hX.eigenvalues r : ℝ) : ℂ) • fun x => (hX.eigenvectorUnitary : Matrix ι ι ℂ) x r := by
  have e : (fun x => (hX.eigenvectorUnitary : Matrix ι ι ℂ) x r) = ⇑(hX.eigenvectorBasis r) := by
    funext x
    exact hX.eigenvectorUnitary_apply x r
  rw [e]
  have := hX.mulVec_eigenvectorBasis r
  rw [this]
  funext x
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

omit [DecidableEq ι] in
/-- The position of `r` in the decreasing order of the eigenvalues, `k ∈ ⟦1, card ι⟧`. -/
private def SpecSum_kap (r : ι) : ℕ :=
  ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm r :
    Fin (Fintype.card ι)).val + 1

omit [DecidableEq ι] in
private lemma SpecSum_kap_ge (r : ι) : 1 ≤ SpecSum_kap r := Nat.le_add_left 1 _

omit [DecidableEq ι] in
private lemma SpecSum_kap_le (r : ι) : SpecSum_kap r ≤ Fintype.card ι :=
  ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm r).isLt

omit [DecidableEq ι] in
private lemma SpecSum_kap_inj : Function.Injective (SpecSum_kap (ι := ι)) := by
  intro r s h
  have h1 : ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm r :
      Fin (Fintype.card ι)).val = ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
        s : Fin (Fintype.card ι)).val := by
    unfold SpecSum_kap at h
    omega
  exact (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm.injective
    (Fin.ext h1)

/-- `hX.eigenvalues r = λ_{k(r)}`. -/
private lemma SpecSum_eig_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (r : ι) :
    hX.eigenvalues r = eigK X (SpecSum_kap r) := by
  have hk : SpecSum_kap r - 1 < Fintype.card ι := by
    have := SpecSum_kap_le r
    have := SpecSum_kap_ge r
    omega
  unfold eigK
  simp only [hk, ↓reduceDIte]
  unfold eigs
  simp only [hX, ↓reduceDIte]
  rfl

omit [DecidableEq ι] in
/-- Sums over the eigenvector index are bounded by the sums over `⟦1, card ι⟧`. -/
private lemma SpecSum_sum_kap (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∑ r : ι, g (SpecSum_kap r) ≤ ∑ k ∈ Finset.Icc 1 (Fintype.card ι), g k := by
  calc ∑ r : ι, g (SpecSum_kap r)
      = ∑ k ∈ Finset.univ.image (SpecSum_kap (ι := ι)), g k :=
        (Finset.sum_image (fun r _ s _ h => SpecSum_kap_inj h)).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hg k
        intro k hk
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_Icc.2 ⟨SpecSum_kap_ge r, SpecSum_kap_le r⟩

end Eig

end Part3b

section Part3c

/-- The double sum `Σ_{r,s} a_r b_s (δ + 2 f_r + 2 f_s)` in terms of the single sums. -/
private lemma SpecSum_dsum {ι : Type*} [Fintype ι] (a b f : ι → ℝ) (δ : ℝ) :
    ∑ r, ∑ s, a r * b s * (δ + 2 * f r + 2 * f s) =
      δ * (∑ r, a r) * (∑ s, b s) + 2 * (∑ r, a r * f r) * (∑ s, b s) +
        2 * (∑ r, a r) * (∑ s, b s * f s) := by
  have e1 : δ * (∑ r, a r) * (∑ s, b s) = ∑ r, ∑ s, δ * (a r * b s) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
  have e2 : 2 * (∑ r, a r * f r) * (∑ s, b s) = ∑ r, ∑ s, 2 * (a r * f r * b s) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
  have e3 : 2 * (∑ r, a r) * (∑ s, b s * f s) = ∑ r, ∑ s, 2 * (a r * (b s * f s)) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
  rw [e1, e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The weight `Im z / |λ - z|²` at `z = E + iη`. -/
private lemma SpecSum_wt_eq (E η l : ℝ) :
    ((E : ℂ) + (η : ℂ) * Complex.I).im / ‖(l : ℂ) - ((E : ℂ) + (η : ℂ) * Complex.I)‖ ^ 2 =
      η / ((l - E) ^ 2 + η ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.sub_im,
    Complex.add_im, Complex.mul_im, zero_add, zero_sub]
  congr 1
  ring

end Part3c

/-- (4.19) [GEaD3] with `ε ≥ 2σ`, and the bound of (4.20) [GEaD4] on the event, for a Hermitian
`X` whose eigenvalues satisfy (2.24) [eq:rigidity] with loss `N^{τ'}`, `τ' < 2σ`, and whose unit
eigenvectors of indices in `⟦1, N^c⟧` satisfy (3.4) [eq:extend:main_evector1] with `N^{-c}`;
`η = N^{-2/3-σ}`, `E₁, E₂` within `N^{-2/3+σ}` of `E⁺`. -/
theorem edgeSpec_le (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ K : ℝ, 0 < K ∧ ∀ c σ ε τ' : ℝ, 0 < c → c ≤ 1 → 0 < σ → σ < 1 / 12 → 2 * σ ≤ ε →
      ε < c → 0 < τ' → τ' < 2 * σ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian → IsRigid D N A τ' X →
      (∀ i j : ℕ, 1 ≤ i → i ≤ D * N → 1 ≤ j → j ≤ D * N → |(i : ℝ) - 1| ≤ (N : ℝ) ^ c →
        |(j : ℝ) - 1| ≤ (N : ℝ) ^ c → ∀ u w : Idx D N → ℂ, IsUnitEigvec X (eigK X i) u →
        IsUnitEigvec X (eigK X j) w → ∀ a : Fin D,
          ‖star u ⬝ᵥ ((Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ w)‖ <
            (N : ℝ) ^ (-c)) →
      ∀ E₁ E₂ : ℝ, |E₁ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) →
        |E₂ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) → ∀ a : Fin D,
        ‖edgeXterm D N X ((E₁ : ℂ) + (((N : ℝ) ^ (-(2 / 3 : ℝ) - σ) : ℝ) : ℂ) * Complex.I)
            ((E₂ : ℂ) + (((N : ℝ) ^ (-(2 / 3 : ℝ) - σ) : ℝ) : ℂ) * Complex.I) a‖ ≤
          K * (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) ∧
        ‖edgeYterm D N X ((E₁ : ℂ) + (((N : ℝ) ^ (-(2 / 3 : ℝ) - σ) : ℝ) : ℂ) * Complex.I) a‖ ≤
          K * (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) := by
  obtain ⟨c₀, hc₀, hgapall⟩ := edge_gap_lower D hD δA hδA
  have hZ := SpecSum_Z_nonneg
  have hK₁1 : 1 ≤ 1 + (c₀ ^ 2)⁻¹ * SpecSum_Z := by
    have : 0 ≤ (c₀ ^ 2)⁻¹ * SpecSum_Z := by positivity
    linarith
  set K₁ : ℝ := 1 + (c₀ ^ 2)⁻¹ * SpecSum_Z with hK₁
  set K₂ : ℝ := 3 * (c₀ ^ 2)⁻¹ with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨K₁ ^ 2 + 4 * K₁ * K₂, by positivity,
    fun c σ ε τ' hc0 hc1 hσ hσ12 hσε hεc hτ0 hττ => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hgapall σ τ' hσ hτ0 hττ
  refine ⟨max N₀ 1, fun N hN A hA X hXH hrig hev E₁ E₂ hE₁ hE₂ a => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  set η : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) with hη
  have hηp : 0 < η := by positivity
  have hcard : Fintype.card (Idx D N) = D * N := by simp [Idx]
  have hDN : (0 : ℝ) < ((D * N : ℕ) : ℝ) := by
    have : 0 < D * N := Nat.mul_pos (by omega) hN1
    exact_mod_cast this
  have hDNN : (((D * N : ℕ) : ℝ))⁻¹ ≤ (N : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    refine inv_anti₀ hn0 ?_
    push_cast
    have : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
    nlinarith
  -- the weights, the near/far indicator and the sums
  have hS : ∀ E : ℝ, |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) →
      ∑ r : Idx D N, η / ((hXH.eigenvalues r - E) ^ 2 + η ^ 2) ≤
        K₁ * (N : ℝ) ^ (2 / 3 + σ + ε) := by
    intro E hE
    simp_rw [SpecSum_eig_eq X hXH]
    refine (SpecSum_sum_kap (fun k => η / ((eigK X k - E) ^ 2 + η ^ 2))
      (fun k => by positivity)).trans ?_
    rw [hcard]
    exact SpecSum_wsum_all hc₀ hσ hσε hNr hη
      (fun k hk hkM => hN₀ N hN0 A hA X hrig E hE k hk hkM)
  have hF : ∀ E : ℝ, |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) →
      ∑ r : Idx D N, η / ((hXH.eigenvalues r - E) ^ 2 + η ^ 2) *
        (if (N : ℝ) ^ c + 1 < (SpecSum_kap r : ℕ) then (1 : ℝ) else 0) ≤
        K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3) := by
    intro E hE
    simp_rw [SpecSum_eig_eq X hXH]
    have h1 := SpecSum_sum_kap (ι := Idx D N)
      (fun k => η / ((eigK X k - E) ^ 2 + η ^ 2) *
        (if (N : ℝ) ^ c + 1 < (k : ℕ) then (1 : ℝ) else 0)) (fun k => by positivity)
    refine h1.trans ?_
    rw [hcard]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    exact SpecSum_wsum_far hc₀ hσε hεc hNr hη
      (fun k hk hkM => hN₀ N hN0 A hA X hrig E hE k hk hkM)
  have hz : ∀ E : ℝ, 0 < (((E : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I).im := fun E => by
    simpa using hηp
  set U : Matrix (Idx D N) (Idx D N) ℂ := (hXH.eigenvectorUnitary : Matrix (Idx D N) (Idx D N) ℂ)
    with hU
  set f : Idx D N → ℝ := fun r => if (N : ℝ) ^ c + 1 < (SpecSum_kap r : ℕ) then (1 : ℝ) else 0
    with hf
  have hf0 : ∀ r, 0 ≤ f r := fun r => by simp only [hf]; split_ifs <;> norm_num
  have hNc : 0 ≤ (N : ℝ) ^ (-c) := by positivity
  have hbnd : ∀ r s : Idx D N,
      ‖star (fun x => U x r) ⬝ᵥ ((((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *ᵥ
        fun x => U x s)‖ ≤ (N : ℝ) ^ (-c) + 2 * f r + 2 * f s := by
    intro r s
    have hu := SpecSum_col_unit X hXH r
    have hw := SpecSum_col_unit X hXH s
    have hb := SpecSum_dotB_le D N hD a (fun x => U x r) (fun x => U x s) hu hw
    by_cases hr : (N : ℝ) ^ c + 1 < (SpecSum_kap r : ℕ)
    · have : f r = 1 := by simp [hf, hr]
      rw [this]
      linarith [hf0 s]
    by_cases hs : (N : ℝ) ^ c + 1 < (SpecSum_kap s : ℕ)
    · have : f s = 1 := by simp [hf, hs]
      rw [this]
      linarith [hf0 r]
    have hfr : f r = 0 := by simp [hf, hr]
    have hfs : f s = 0 := by simp [hf, hs]
    rw [hfr, hfs]
    have hr' : |((SpecSum_kap r : ℕ) : ℝ) - 1| ≤ (N : ℝ) ^ c := by
      rw [abs_of_nonneg (by
        have := SpecSum_kap_ge r
        have : (1 : ℝ) ≤ (SpecSum_kap r : ℕ) := by exact_mod_cast this
        linarith)]
      linarith [not_lt.1 hr]
    have hs' : |((SpecSum_kap s : ℕ) : ℝ) - 1| ≤ (N : ℝ) ^ c := by
      rw [abs_of_nonneg (by
        have := SpecSum_kap_ge s
        have : (1 : ℝ) ≤ (SpecSum_kap s : ℕ) := by exact_mod_cast this
        linarith)]
      linarith [not_lt.1 hs]
    have hcol : ∀ t : Idx D N, IsUnitEigvec X (eigK X (SpecSum_kap t)) (fun x => U x t) :=
      fun t => ⟨by rw [← SpecSum_eig_eq X hXH t]; exact SpecSum_col_eig X hXH t,
        SpecSum_col_unit X hXH t⟩
    have hq := hev (SpecSum_kap r) (SpecSum_kap s) (SpecSum_kap_ge r)
      (by have := SpecSum_kap_le r; rwa [hcard] at this) (SpecSum_kap_ge s)
      (by have := SpecSum_kap_le s; rwa [hcard] at this) hr' hs' _ _ (hcol r) (hcol s) a
    rw [← neg_sub, Matrix.neg_mulVec, dotProduct_neg, norm_neg]
    linarith
  have hpt : ∀ r s : Idx D N,
      ‖star (fun x => U x r) ⬝ᵥ ((((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *ᵥ
        fun x => U x s)‖ *
      ‖star (fun x => U x s) ⬝ᵥ (Ea D N a *ᵥ fun x => U x r)‖ ≤
        (N : ℝ) ^ (-c) + 2 * f r + 2 * f s := by
    intro r s
    have he := SpecSum_dotE_le D N a (fun x => U x s) (fun x => U x r)
      (SpecSum_col_unit X hXH s) (SpecSum_col_unit X hXH r)
    calc _ ≤ _ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hbnd r s
  have hw0 : ∀ (E : ℝ) (r : Idx D N), 0 ≤ η / ((hXH.eigenvalues r - E) ^ 2 + η ^ 2) :=
    fun E r => by positivity
  have hSn : ∀ E : ℝ, 0 ≤ ∑ r : Idx D N, η / ((hXH.eigenvalues r - E) ^ 2 + η ^ 2) :=
    fun E => Finset.sum_nonneg fun r _ => hw0 E r
  have hFn : ∀ E : ℝ, 0 ≤ ∑ r : Idx D N, η / ((hXH.eigenvalues r - E) ^ 2 + η ^ 2) * f r :=
    fun E => Finset.sum_nonneg fun r _ => mul_nonneg (hw0 E r) (hf0 r)
  have hK₁0 : 0 ≤ K₁ := by linarith
  refine ⟨?_, ?_⟩
  · -- the bound (4.19) [GEaD3]
    rw [(edgeTerm_eq_sum X hXH _ _ (hz E₁) (hz E₂) a).1, norm_mul, norm_inv,
      Complex.norm_natCast]
    refine le_trans (mul_le_mul_of_nonneg_left
      (c := (N : ℝ) ^ (-c) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) +
        2 * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) +
        2 * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)))
      ?_ (by positivity)) ?_
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun r _ => norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => (?_ :
        _ ≤ (η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) *
            (η / ((hXH.eigenvalues s - E₂) ^ 2 + η ^ 2)) *
            ((N : ℝ) ^ (-c) + 2 * f r + 2 * f s))).trans ?_
      · rw [norm_mul, norm_mul, Complex.norm_real, SpecSum_wt_eq, SpecSum_wt_eq,
          Real.norm_of_nonneg (mul_nonneg (hw0 E₁ r) (hw0 E₂ s))]
        calc _ = (η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) *
            (η / ((hXH.eigenvalues s - E₂) ^ 2 + η ^ 2)) * (_ * _) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hpt r s) (mul_nonneg (hw0 E₁ r) (hw0 E₂ s))
      · rw [SpecSum_dsum]
        have hS₁ := hS E₁ hE₁
        have hS₂ := hS E₂ hE₂
        have hF₁ := hF E₁ hE₁
        have hF₂ := hF E₂ hE₂
        have hS₁0 := hSn E₁
        have hS₂0 := hSn E₂
        have hF₁0 := hFn E₁
        have hF₂0 := hFn E₂
        have hnn1 : 0 ≤ K₁ * (N : ℝ) ^ (2 / 3 + σ + ε) := by positivity
        have hnn2 : 0 ≤ K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3) := by positivity
        have t1 : (N : ℝ) ^ (-c) * (∑ r, η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) *
            (∑ s, η / ((hXH.eigenvalues s - E₂) ^ 2 + η ^ 2)) ≤
            (N : ℝ) ^ (-c) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) *
              (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hS₁ hNc) hS₂ hS₂0 (by positivity)
        have t2 : 2 * (∑ r, η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2) * f r) *
            (∑ s, η / ((hXH.eigenvalues s - E₂) ^ 2 + η ^ 2)) ≤
            2 * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hF₁ (by norm_num)) hS₂ hS₂0 (by positivity)
        have t3 : 2 * (∑ r, η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) *
            (∑ s, η / ((hXH.eigenvalues s - E₂) ^ 2 + η ^ 2) * f s) ≤
            2 * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hS₁ (by norm_num)) hF₂ hF₂0 (by positivity)
        linarith
    · have hB0 : 0 ≤ (N : ℝ) ^ (-c) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) *
          (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) +
          2 * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) +
          2 * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)) := by
        positivity
      have hA : (N : ℝ) ^ (-1 : ℝ) * ((N : ℝ) ^ (-c) *
          ((N : ℝ) ^ (2 / 3 + σ + ε) * (N : ℝ) ^ (2 / 3 + σ + ε))) ≤
          (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      have hB : (N : ℝ) ^ (-1 : ℝ) * ((N : ℝ) ^ (2 / 3 - σ - c / 3) *
          (N : ℝ) ^ (2 / 3 + σ + ε)) ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      have hT : 0 ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) := by positivity
      calc (((D * N : ℕ) : ℝ))⁻¹ * _ ≤ (N : ℝ) ^ (-1 : ℝ) * _ :=
            mul_le_mul_of_nonneg_right hDNN hB0
        _ = K₁ ^ 2 * ((N : ℝ) ^ (-1 : ℝ) * ((N : ℝ) ^ (-c) *
              ((N : ℝ) ^ (2 / 3 + σ + ε) * (N : ℝ) ^ (2 / 3 + σ + ε)))) +
            4 * K₁ * K₂ * ((N : ℝ) ^ (-1 : ℝ) * ((N : ℝ) ^ (2 / 3 - σ - c / 3) *
              (N : ℝ) ^ (2 / 3 + σ + ε))) := by ring
        _ ≤ K₁ ^ 2 * (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) +
            4 * K₁ * K₂ * (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) := by
            gcongr
        _ = _ := by ring
  · -- the bound (4.20) [GEaD4]
    rw [(edgeTerm_eq_sum X hXH _ _ (hz E₁) (hz E₂) a).2, norm_mul, norm_inv,
      Complex.norm_natCast]
    refine le_trans (mul_le_mul_of_nonneg_left
      (c := (N : ℝ) ^ (-c) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) +
        4 * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3))) ?_ (by positivity)) ?_
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun r _ => (?_ :
        _ ≤ (η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) * ((N : ℝ) ^ (-c) + 4 * f r))).trans ?_
      · rw [norm_mul, Complex.norm_real, SpecSum_wt_eq, Real.norm_of_nonneg (hw0 E₁ r)]
        exact mul_le_mul_of_nonneg_left (by have := hbnd r r; linarith) (hw0 E₁ r)
      · have e : ∑ r : Idx D N, (η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) *
            ((N : ℝ) ^ (-c) + 4 * f r) =
            (N : ℝ) ^ (-c) * (∑ r : Idx D N, η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2)) +
            4 * ∑ r : Idx D N, η / ((hXH.eigenvalues r - E₁) ^ 2 + η ^ 2) * f r := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun r _ => by ring
        rw [e]
        have hS₁ := hS E₁ hE₁
        have hF₁ := hF E₁ hE₁
        have := mul_le_mul_of_nonneg_left hS₁ hNc
        linarith
    · have hB0 : 0 ≤ (N : ℝ) ^ (-c) * (K₁ * (N : ℝ) ^ (2 / 3 + σ + ε)) +
          4 * (K₂ * (N : ℝ) ^ (2 / 3 - σ - c / 3)) := by positivity
      have hC : (N : ℝ) ^ (-1 : ℝ) * ((N : ℝ) ^ (-c) * (N : ℝ) ^ (2 / 3 + σ + ε)) ≤
          (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      have hD' : (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (2 / 3 - σ - c / 3) ≤
          (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) := by
        rw [← Real.rpow_add hn0]
        exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      calc (((D * N : ℕ) : ℝ))⁻¹ * _ ≤ (N : ℝ) ^ (-1 : ℝ) * _ :=
            mul_le_mul_of_nonneg_right hDNN hB0
        _ = K₁ * ((N : ℝ) ^ (-1 : ℝ) * ((N : ℝ) ^ (-c) * (N : ℝ) ^ (2 / 3 + σ + ε))) +
            4 * K₂ * ((N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (2 / 3 - σ - c / 3)) := by ring
        _ ≤ K₁ * (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) +
            4 * K₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) := by gcongr
        _ ≤ (K₁ ^ 2 + 4 * K₁ * K₂) * (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) := by
            have hT : 0 ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) - c / 3 + σ + ε) := by positivity
            have h1 : K₁ ≤ K₁ ^ 2 := by nlinarith
            have h2 : 4 * K₂ ≤ 4 * K₁ * K₂ := by nlinarith
            nlinarith

end RBMTransitionEdge

end
