module

public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Tools.ResolventIdentities

@[expose] public section

/-!
# The self-consistent identity and the vector equation

The profile map `S_θ`, the underline (2.30) [eq:HGline] for `S_θ`, the identity (2.25) [eq:G-M] with the underline,
and the objects of the vector equation of the block traces of `G − M`: `q_{abc}`, its quadratic map, the
fluctuation vector `r` and the norm on `ℂ^D`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `S_θ(R) = θ Σ_a D⟨R E_a⟩ E_a + (1 - θ)⟨R⟩ I`, the map `R ↦ E[H R H]` for the variance profile
`S_θ`; at `θ = 1` it is `Ẽ[H̃ R H̃] = Σ_a D⟨R E_a⟩ E_a` of (2.30) [eq:HGline]. -/
def sTheta (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  (θ : ℂ) • (∑ a : Fin D, ((D : ℂ) * ntr (R * Ea D N a)) • Ea D N a) +
    ((1 - θ : ℝ) : ℂ) • (ntr R • (1 : Matrix (Idx D N) (Idx D N) ℂ))

/-- `σ_θ = θ I + (1 - θ) J / D` on `ℂ^D`, so that `S_θ(R) = Σ_a (σ_θ x)_a E_a` for the block
traces `x_a = D⟨E_a R⟩`. -/
def sigTheta (D : ℕ) (θ : ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (θ : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) +
    ((1 - θ : ℝ) : ℂ) • ((D : ℂ)⁻¹ • Matrix.of fun _ _ => (1 : ℂ))

/-- `H̲G = H G + S_θ(G) G` for `G = (H + Λ - z)⁻¹`: (2.30) [eq:HGline] with the profile `S_θ`,
which is Definition 2.12 [def:underline] with `g = I`, `f = G`. -/
def hgUnder (D N : ℕ) (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  H * res (H + Λ) z + sTheta D N θ (res (H + Λ) z) * res (H + Λ) z

/-- The block traces `x_a = D⟨E_a R⟩ = N⁻¹ tr(E_a R)`. -/
def blockTr (D N : ℕ) (R : Matrix (Idx D N) (Idx D N) ℂ) : Fin D → ℂ :=
  fun a => (D : ℂ) * ntr (Ea D N a * R)

/-- `q_{abc} = D⟨E_a M E_b M E_c M⟩ = N⁻¹ tr(E_a M E_b M E_c M)`, `M = M(z)` of (2.17) [def_G0]. -/
def qTensor {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (a b c : Fin D) : ℂ :=
  (D : ℂ) * ntr (Ea D N a * MExt Λ z * Ea D N b * MExt Λ z * Ea D N c * MExt Λ z)

/-- The quadratic map `Q(y)_a = Σ_{b,c} q_{abc} y_b y_c` on `ℂ^D`. -/
def quadForm {D : ℕ} (q : Fin D → Fin D → Fin D → ℂ) (y : Fin D → ℂ) : Fin D → ℂ :=
  fun a => ∑ b, ∑ c, q a b c * y b * y c

/-- The fluctuation vector `r_a = -D⟨E_a M H̲G⟩`. -/
def rVec (D N : ℕ) (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) : Fin D → ℂ :=
  fun a => -((D : ℂ) * ntr (Ea D N a * MExt Λ z * hgUnder D N θ H Λ z))

/-- The Euclidean norm `|x| = (Σ_a |x_a|²)^{1/2}` on `ℂ^D`. -/
def vnorm {D : ℕ} (x : Fin D → ℂ) : ℝ := Real.sqrt (∑ a, ‖x a‖ ^ 2)

/-- The normalized trace is compatible with subtraction. -/
private lemma Dyson_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- The normalized trace of a finite sum is the sum of the normalized traces. -/
private lemma Dyson_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (P : κ → Matrix ι ι ℂ) :
    ntr (∑ b ∈ s, P b) = ∑ b ∈ s, ntr (P b) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- The normalized trace is cyclic. -/
private lemma Dyson_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  simp [ntr, Matrix.trace_mul_comm P Q]

/-- The block projections sum to the identity. -/
private lemma Dyson_sum_Ea (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- `S_θ(R) = Σ_a (σ_θ x)_a E_a` with `x_a = D⟨E_a R⟩`: `S_θ` sees `R` only through its block
traces. -/
theorem sTheta_blockTr (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ R = ∑ a, (sigTheta D θ *ᵥ blockTr D N R) a • Ea D N a := by
  have hsig : ∀ (x : Fin D → ℂ) (a : Fin D), (sigTheta D θ *ᵥ x) a =
      (θ : ℂ) * x a + ((1 - θ : ℝ) : ℂ) * ((D : ℂ)⁻¹ * ∑ b, x b) := by
    intro x a
    have hJ : (Matrix.of fun (_ _ : Fin D) => (1 : ℂ)) *ᵥ x = fun _ => ∑ b, x b := by
      ext
      simp [Matrix.mulVec, dotProduct]
    simp only [sigTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hntr : ntr R = (D : ℂ)⁻¹ * ∑ b, blockTr D N R b := by
    have h1 : ∑ b, blockTr D N R b = (D : ℂ) * ntr R := by
      unfold blockTr
      rw [← Finset.mul_sum, ← Dyson_ntr_sum, ← Finset.sum_mul, Dyson_sum_Ea, Matrix.one_mul]
    rw [h1]
    by_cases hD : D = 0
    · subst hD
      simp [ntr, Matrix.trace]
    · have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
      field_simp
  have hx : ∀ a, (D : ℂ) * ntr (R * Ea D N a) = blockTr D N R a := fun a => by
    unfold blockTr
    rw [Dyson_ntr_comm]
  unfold sTheta
  simp only [hx, hsig, add_smul, Finset.sum_add_distrib, ← Finset.smul_sum, smul_smul]
  rw [Dyson_sum_Ea, ← hntr, Finset.smul_sum]
  simp only [smul_smul]

/-- `S_θ(M) = m I` for `Λ = lam D N A` and `z ∉ ℝ`, for every `θ`: (2.13) [def_M] holds with
`S_θ` in place of `𝒮`, because `D⟨M E_a⟩ = m` for every block `a`. -/
theorem sTheta_MExt (D N : ℕ) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    sTheta D N θ (MExt (lam D N A) z) =
      mExt (lam D N A) z • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  by_cases hDN : D = 0 ∨ N = 0
  · ext p q
    rcases hDN with h | h
    · subst h
      exact p.1.elim0
    · subst h
      exact p.2.elim0
  rw [not_or] at hDN
  obtain ⟨hD, hN⟩ := hDN
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, Nat.pos_of_ne_zero hN⟩)⟩
  obtain ⟨hm, -, -⟩ := MExt_spec (lam D N A) (lam_isHermitian D N A) z hz
  have hblk : ∀ a : Fin D,
      (D : ℂ) * ntr (MExt (lam D N A) z * Ea D N a) = mExt (lam D N A) z := by
    by_cases h2 : 2 ≤ D
    · exact (def_M_scalar D h2 N (Nat.pos_of_ne_zero hN) A z hz).1
    · obtain rfl : D = 1 := by omega
      intro a
      have hE : Ea 1 N a = 1 := by
        ext p q
        have : p.1 = a := Subsingleton.elim _ _
        simp [Ea, Matrix.diagonal_apply, Matrix.one_apply, this]
      rw [hE, Matrix.mul_one, ← hm]
      simp
  unfold sTheta
  simp only [hblk, ← Finset.smul_sum, Dyson_sum_Ea, ← hm, smul_smul]
  rw [← add_smul]
  congr 1
  push_cast
  ring

/-- `S_θ` is compatible with subtraction (it is linear). -/
private lemma Dyson_sTheta_sub (D N : ℕ) (θ : ℝ) (R S : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ (R - S) = sTheta D N θ R - sTheta D N θ S := by
  unfold sTheta
  simp only [Matrix.sub_mul, Dyson_ntr_sub, mul_sub, sub_smul, Finset.sum_sub_distrib, smul_sub]
  abel

/-- (2.25) [eq:G-M] with (2.30) [eq:HGline] for the profile `S_θ`: for every Hermitian `H`,
`Λ = lam D N A` and `Im z > 0`, `G - M = -M H̲G + M S_θ(G - M) G`, with `G = (H + Λ - z)⁻¹` and
`M = M(z)` of (2.17) [def_G0]. -/
theorem hgUnder_identity (D N : ℕ) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    res (H + lam D N A) z - MExt (lam D N A) z =
      -(MExt (lam D N A) z * hgUnder D N θ H (lam D N A) z) +
        MExt (lam D N A) z * sTheta D N θ (res (H + lam D N A) z - MExt (lam D N A) z) *
          res (H + lam D N A) z := by
  by_cases hDN : D = 0 ∨ N = 0
  · ext p q
    rcases hDN with h | h
    · subst h
      exact p.1.elim0
    · subst h
      exact p.2.elim0
  rw [not_or] at hDN
  obtain ⟨hD, hN⟩ := hDN
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, Nat.pos_of_ne_zero hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨-, -, hmim⟩ := MExt_spec (lam D N A) hΛ z hz.ne'
  have hm0 : 0 ≤ (mExt (lam D N A) z).im := by
    by_contra h
    have h' := not_le.mp h
    nlinarith [mul_pos (neg_pos.mpr h') hz]
  obtain ⟨-, h2⟩ := res_sub_dyson H (lam D N A) hH hΛ z (mExt (lam D N A) z) hz hm0
  have hMdef : MExt (lam D N A) z =
      (lam D N A - (z + mExt (lam D N A) z) • (1 : Matrix (Idx D N) (Idx D N) ℂ))⁻¹ := rfl
  rw [← hMdef] at h2
  unfold hgUnder
  rw [Dyson_sTheta_sub, sTheta_MExt D N θ A z hz.ne']
  refine h2.trans ?_
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

end RBMTransitionEdge

end
