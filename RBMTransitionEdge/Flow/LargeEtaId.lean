module

public import RBMTransitionEdge.Flow.Endpoint
public import RBMTransitionEdge.Flow.KTheta
public import RBMTransitionEdge.LocalLaw.MultiResLocal
public import RBMTransitionEdge.LocalLaw.OU

@[expose] public section

/-!
# Identities for the expansion of Lemmas 3.6 and 3.7 with the class parameter

The fluctuation terms of (3.39) [eq:aftertrace] and of its three-resolvent analogue for the profile
`S_θ`, the identities themselves at every Hermitian array, and (A.53) [entprodG] uniformly over the
class.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

private lemma LargeEtaId_ntr_add {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P + Q) = ntr P + ntr Q := by
  simp [ntr, Matrix.trace_add, mul_add]

private lemma LargeEtaId_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

private lemma LargeEtaId_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

private lemma LargeEtaId_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (P : κ → Matrix ι ι ℂ) :
    ntr (∑ k ∈ s, P k) = ∑ k ∈ s, ntr (P k) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- The block projections sum to the identity. -/
private lemma LargeEtaId_sum_Ea (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- `S_θ` is linear. -/
private lemma LargeEtaId_sTheta_sub (D N : ℕ) (θ : ℝ) (R S : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ (R - S) = sTheta D N θ R - sTheta D N θ S := by
  unfold sTheta
  simp only [Matrix.sub_mul, LargeEtaId_ntr_sub, mul_sub, sub_smul, Finset.sum_sub_distrib,
    smul_sub]
  abel

/-- `S_θ(R) = Σ_{x,c} (P_θ)_{xc} D⟨R E_c⟩ E_x`. -/
private lemma LargeEtaId_sTheta_eq (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ R = ∑ x : Fin D, ∑ c : Fin D,
      (PTheta D θ x c * ((D : ℂ) * ntr (R * Ea D N c))) • Ea D N x := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · ext p
    exact p.1.elim0
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  set t : Fin D → ℂ := fun c => (D : ℂ) * ntr (R * Ea D N c) with ht
  have h2 : ∑ c, t c = (D : ℂ) * ntr R := by
    simp only [ht, ← Finset.mul_sum, ← LargeEtaId_ntr_sum,
      LargeEtaId_sum_Ea, Matrix.mul_one]
  have h1 : ∀ x : Fin D, ∑ c, PTheta D θ x c * t c =
      (θ : ℂ) * t x + (((1 - θ) / D : ℝ) : ℂ) * ∑ c, t c := by
    intro x
    simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp
  have e1 : ∑ x : Fin D, ∑ c : Fin D, (PTheta D θ x c * t c) • Ea D N x =
      ∑ x : Fin D, ((θ : ℂ) * t x + (((1 - θ) / D : ℝ) : ℂ) * ((D : ℂ) * ntr R)) • Ea D N x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul, h1, h2]
  have e2 : ∑ x : Fin D, ((θ : ℂ) * t x) • Ea D N x = (θ : ℂ) • ∑ x : Fin D, t x • Ea D N x := by
    simp [Finset.smul_sum, smul_smul]
  have e3 : ∑ x : Fin D, ((((1 - θ) / D : ℝ) : ℂ) * ((D : ℂ) * ntr R)) • Ea D N x =
      ((1 - θ : ℝ) : ℂ) • (ntr R • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
    rw [← Finset.smul_sum, LargeEtaId_sum_Ea, smul_smul]
    congr 1
    push_cast
    field_simp
  change _ = ∑ x : Fin D, ∑ c : Fin D, (PTheta D θ x c * t c) • Ea D N x
  rw [e1]
  simp only [add_smul, Finset.sum_add_distrib, e2, e3]
  rfl

/-- The expansion `G = M - M H̲G + M S_θ(G - M) G` for every Hermitian `h` and `Im z ≠ 0`. -/
private lemma LargeEtaId_key (D N : ℕ) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    res (H + lam D N A) z = MExt (lam D N A) z -
      MExt (lam D N A) z * hgUnder D N θ H (lam D N A) z +
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
  obtain ⟨-, hB, -⟩ := MExt_spec (lam D N A) hΛ z hz
  obtain ⟨hA1, -⟩ := res_mul_sub_of_im_ne (H + lam D N A) (hH.add hΛ) z hz
  set G := res (H + lam D N A) z with hG
  set M := MExt (lam D N A) z with hM
  set m := mExt (lam D N A) z with hm
  have hB' : M * (lam D N A - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 :=
    mul_eq_one_comm.mp hB
  have e1 : G - M = M * (-(H + m • (1 : Matrix (Idx D N) (Idx D N) ℂ))) * G := by
    have hd : (lam D N A - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) -
        ((H + lam D N A) - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) =
        -(H + m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
      rw [add_smul]; abel
    rw [← hd, Matrix.mul_sub, Matrix.sub_mul, hB', Matrix.one_mul, Matrix.mul_assoc M
      ((H + lam D N A) - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) G, hA1, Matrix.mul_one]
  unfold hgUnder
  rw [LargeEtaId_sTheta_sub, sTheta_MExt D N θ A z hz]
  have e2 : G = M + (G - M) := by abel
  conv_lhs => rw [e2, e1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- If `G = M - M U + M V G` then `X G W = X M W - X M U W + X M V G W`. -/
private lemma LargeEtaId_expand {ι : Type*} [Fintype ι]
    (G M U V X W : Matrix ι ι ℂ) (hG : G = M - M * U + M * V * G) :
    X * G * W = X * M * W - X * M * U * W + X * M * V * G * W := by
  conv_lhs => rw [hG]
  noncomm_ring

/-- `mSol (1 • Λ) z = mExt Λ z` for `Im z > 0`. -/
private lemma LargeEtaId_mSol_one {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (z : ℂ) (hz : 0 < z.im) : mSol ((((1 : ℝ) : ℂ)) • Λ) z = mExt Λ z := by
  rw [Complex.ofReal_one, one_smul]
  simp [mExt, hz]

/-- For `N ≥ 20^{1/δ_A}`, `N^{-δ_A} ≤ 1/20`. -/
private lemma LargeEtaId_pow_le (δA : ℝ) (hδA : 0 < δA) (N : ℕ)
    (hN : (20 : ℝ) ^ (1 / δA) ≤ N) : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
  have h20 : (0 : ℝ) < 20 ^ (1 / δA) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (20 : ℝ) ≤ (N : ℝ) ^ δA := by
    have := Real.rpow_le_rpow h20.le hN hδA.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδA.ne', Real.rpow_one] at this
  rw [Real.rpow_neg (by linarith [h20, hN]), one_div]
  exact inv_anti₀ (by norm_num) h1

/-- `⟨X S_θ(R) Y W⟩ = Σ_{x,c} (P_θ)_{xc} D⟨R E_c⟩ ⟨X E_x Y W⟩`. -/
private lemma LargeEtaId_ntr_sTheta {D N : ℕ} (θ : ℝ) (X R Y W : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (X * sTheta D N θ R * Y * W) = ∑ x : Fin D, ∑ c : Fin D,
      PTheta D θ x c * ((D : ℂ) * ntr (R * Ea D N c)) * ntr (X * Ea D N x * Y * W) := by
  rw [LargeEtaId_sTheta_eq]
  simp only [Matrix.mul_sum, Matrix.sum_mul, LargeEtaId_ntr_sum, Matrix.mul_smul,
    Matrix.smul_mul, LargeEtaId_ntr_smul]

/-- `D⟨X S_θ(R) Y W⟩ = Σ_{x,c} (P_θ)_{xc} D⟨R E_c⟩ D⟨X E_x Y W⟩`. -/
private lemma LargeEtaId_ntr_sTheta' {D N : ℕ} (θ : ℝ)
    (X R Y W : Matrix (Idx D N) (Idx D N) ℂ) :
    (D : ℂ) * ntr (X * sTheta D N θ R * Y * W) = ∑ x : Fin D, ∑ c : Fin D,
      PTheta D θ x c * ((D : ℂ) * ntr (R * Ea D N c)) *
        ((D : ℂ) * ntr (X * Ea D N x * Y * W)) := by
  rw [LargeEtaId_ntr_sTheta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The fluctuation term `⟨\underline{G₁ E_a M₂ H G₂} B⟩` of (3.39) [eq:aftertrace] for the
profile `S_θ` (Definition 2.12 [def:underline] with the pairing `S_θ`):
`⟨G₁ E_a M₂ H̲G₂ B⟩ + ⟨G₁ S_θ(G₁ E_a M₂) G₂ B⟩`, with `H̲G₂ = H G₂ + S_θ(G₂) G₂` of (2.30)
[eq:HGline], `G_i = (h + Λ - z_i)⁻¹` and `M₂ = M(z₂)`. -/
def underTwoB {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (h : Idx D N → Idx D N → ℂ)
    (z₁ z₂ : ℂ) (a : Fin D) (B : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂ * hgUnder D N θ (Matrix.of h) Λ z₂ * B) +
    ntr (res (Matrix.of h + Λ) z₁ *
      sTheta D N θ (res (Matrix.of h + Λ) z₁ * Ea D N a * MExt Λ z₂) * res (Matrix.of h + Λ) z₂ *
        B)

/-- The fluctuation term `⟨\underline{G₁ E_{a₁} G₂ E_{a₂} M₃ H G₃} E_{a₃}⟩` of the expansion of
`L₍₁,₂,₃₎` of Definition 3.2 [defLK3] for the profile `S_θ`: with `g = G₁ E_{a₁} G₂ E_{a₂} M₃`,
`⟨g H̲G₃ E_{a₃}⟩ + ⟨G₁ S_θ(g) G₃ E_{a₃}⟩ + ⟨G₁ E_{a₁} G₂ S_θ(G₂ E_{a₂} M₃) G₃ E_{a₃}⟩`. -/
def underThree {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (h : Idx D N → Idx D N → ℂ)
    (z₁ z₂ z₃ : ℂ) (a₁ a₂ a₃ : Fin D) : ℂ :=
  ntr (res (Matrix.of h + Λ) z₁ * Ea D N a₁ * res (Matrix.of h + Λ) z₂ * Ea D N a₂ * MExt Λ z₃ *
      hgUnder D N θ (Matrix.of h) Λ z₃ * Ea D N a₃) +
    ntr (res (Matrix.of h + Λ) z₁ *
      sTheta D N θ (res (Matrix.of h + Λ) z₁ * Ea D N a₁ * res (Matrix.of h + Λ) z₂ * Ea D N a₂ *
        MExt Λ z₃) * res (Matrix.of h + Λ) z₃ * Ea D N a₃) +
    ntr (res (Matrix.of h + Λ) z₁ * Ea D N a₁ * res (Matrix.of h + Λ) z₂ *
      sTheta D N θ (res (Matrix.of h + Λ) z₂ * Ea D N a₂ * MExt Λ z₃) * res (Matrix.of h + Λ) z₃ *
        Ea D N a₃)

/-- (3.39) [eq:aftertrace] for the profile `S_θ`, with a general deterministic `B`, for every
Hermitian `h`, `Λ = lam D N A` and `Im z₂ ≠ 0`:
`⟨G₁E_aG₂B⟩ = ⟨G₁E_aM₂B⟩ - ⟨\underline{G₁E_aM₂HG₂}B⟩ + Σ_{x,c} (P_θ)_{xc} D⟨G₁E_aM₂E_c⟩⟨G₁E_xG₂B⟩
+ Σ_{x,c} (P_θ)_{xc} D⟨(G₂ - M₂)E_c⟩⟨G₁E_aM₂E_xG₂B⟩`; `B = D E_b` gives (3.39). -/
theorem resPair_aftertrace {D N : ℕ} (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (z₁ z₂ : ℂ) (hz₂ : z₂.im ≠ 0)
    (a : Fin D) (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a * res (Matrix.of h + lam D N A) z₂ * B) =
      ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ * B) -
        underTwoB (lam D N A) θ h z₁ z₂ a B +
        (∑ x, ∑ c, PTheta D θ x c *
          ((D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ *
            Ea D N c)) *
          ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N x *
            res (Matrix.of h + lam D N A) z₂ * B)) +
        (∑ x, ∑ c, PTheta D θ x c *
          ((D : ℂ) * ntr ((res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) * Ea D N c)) *
          ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ * Ea D N x *
            res (Matrix.of h + lam D N A) z₂ * B)) := by
  have hkey := LargeEtaId_key D N θ A (Matrix.of h) hh z₂ hz₂
  have hex := LargeEtaId_expand _ _ _ _ (res (Matrix.of h + lam D N A) z₁ * Ea D N a)
    B hkey
  have e : res (Matrix.of h + lam D N A) z₁ * Ea D N a * res (Matrix.of h + lam D N A) z₂ * B =
      res (Matrix.of h + lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ * B -
        res (Matrix.of h + lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ *
          hgUnder D N θ (Matrix.of h) (lam D N A) z₂ * B +
        res (Matrix.of h + lam D N A) z₁ * Ea D N a * MExt (lam D N A) z₂ *
          sTheta D N θ (res (Matrix.of h + lam D N A) z₂ - MExt (lam D N A) z₂) *
            res (Matrix.of h + lam D N A) z₂ * B := hex
  rw [e, LargeEtaId_ntr_add, LargeEtaId_ntr_sub, LargeEtaId_ntr_sTheta, underTwoB,
    LargeEtaId_ntr_sTheta]
  ring

/-- The analogue of (3.39) [eq:aftertrace] for `L₍₁,₂,₃₎` of Definition 3.2 [defLK3], expanding
`G₃` with the profile `S_θ`, for every Hermitian `h`, `Λ = lam D N A` and `Im z₃ ≠ 0`:
`L_{a₁a₂a₃} = T_{a₁a₂a₃} - D Z₃ + Σ_{x,c} (P_θ)_{xc} T_{a₁a₂c} L₍₁,₃₎_{xa₃}
+ Σ_{x,c} (P_θ)_{xc} D⟨G₂E_{a₂}M₃E_c⟩ L_{a₁xa₃} + Σ_{x,c} (P_θ)_{xc} D⟨(G₃ - M₃)E_c⟩
D⟨G₁E_{a₁}G₂E_{a₂}M₃E_xG₃E_{a₃}⟩`, with `T_{a₁a₂c} = D⟨G₁E_{a₁}G₂E_{a₂}M₃E_c⟩` and `Z₃` the
term `underThree`. -/
theorem resTriple_aftertrace {D N : ℕ} (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (z₁ z₂ z₃ : ℂ)
    (hz₃ : z₃.im ≠ 0) (a₁ a₂ a₃ : Fin D) :
    Lten3 (lam D N A) h z₁ z₂ z₃ a₁ a₂ a₃ =
      (D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
          res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₃ * Ea D N a₃) -
        (D : ℂ) * underThree (lam D N A) θ h z₁ z₂ z₃ a₁ a₂ a₃ +
        (∑ x, ∑ c, PTheta D θ x c *
          ((D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
            res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₃ * Ea D N c)) *
          Lmat (lam D N A) h z₁ z₃ x a₃) +
        (∑ x, ∑ c, PTheta D θ x c *
          ((D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₃ *
            Ea D N c)) *
          Lten3 (lam D N A) h z₁ z₂ z₃ a₁ x a₃) +
        (∑ x, ∑ c, PTheta D θ x c *
          ((D : ℂ) * ntr ((res (Matrix.of h + lam D N A) z₃ - MExt (lam D N A) z₃) * Ea D N c)) *
          ((D : ℂ) * ntr (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
            res (Matrix.of h + lam D N A) z₂ * Ea D N a₂ * MExt (lam D N A) z₃ * Ea D N x *
            res (Matrix.of h + lam D N A) z₃ * Ea D N a₃))) := by
  have hkey := LargeEtaId_key D N θ A (Matrix.of h) hh z₃ hz₃
  have hex := LargeEtaId_expand _ _ _ _ (res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ *
    res (Matrix.of h + lam D N A) z₂ * Ea D N a₂) (Ea D N a₃) hkey
  have e : res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ * res (Matrix.of h + lam D N A) z₂ *
      Ea D N a₂ * res (Matrix.of h + lam D N A) z₃ * Ea D N a₃ =
      res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ * res (Matrix.of h + lam D N A) z₂ *
        Ea D N a₂ * MExt (lam D N A) z₃ * Ea D N a₃ -
      res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ * res (Matrix.of h + lam D N A) z₂ *
        Ea D N a₂ * MExt (lam D N A) z₃ * hgUnder D N θ (Matrix.of h) (lam D N A) z₃ *
          Ea D N a₃ +
      res (Matrix.of h + lam D N A) z₁ * Ea D N a₁ * res (Matrix.of h + lam D N A) z₂ *
        Ea D N a₂ * MExt (lam D N A) z₃ *
        sTheta D N θ (res (Matrix.of h + lam D N A) z₃ - MExt (lam D N A) z₃) *
          res (Matrix.of h + lam D N A) z₃ * Ea D N a₃ := hex
  unfold Lten3 Lmat underThree
  rw [e, LargeEtaId_ntr_add, LargeEtaId_ntr_sub, mul_add, mul_sub, mul_add, mul_add,
    LargeEtaId_ntr_sTheta', LargeEtaId_ntr_sTheta', LargeEtaId_ntr_sTheta']
  ring

/-- (A.53) [entprodG] of Lemma A.4 [lemma_necessary_estimates] uniformly over the class, with
`Λ_i = Λ = lam D N A`: for `z_i ∈ 𝐃(τ)`, `Im z_i > 0`, `N η_i Im m_i ≥ c₀`, and deterministic
`‖B_i‖ ≤ 1`, the averaged and the isotropic bounds hold outside probability `N^{-D'}`, uniformly
in `θ ∈ [0, 1]`, the member and `A`. -/
theorem entprodG_unif (D p : ℕ) (hD : 1 ≤ D) (hp : 1 ≤ p) (δA τ c₀ : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hc₀ : 0 < c₀) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : Fin p → ℂ, (∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im ∧
        c₀ ≤ (N : ℝ) * (z i).im * (mExt (lam D N A) (z i)).im) →
      ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
        μ {h | (N : ℝ) ^ τ' * bndA4 (fun i => (mExt (lam D N A) (z i)).im) (fun i => (z i).im) p <
            ‖ntr (resProd (fun i => res (Matrix.of h + lam D N A) (z i)) s B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
          μ {h | (N : ℝ) ^ τ' *
                bndA4 (fun i => (mExt (lam D N A) (z i)).im) (fun i => (z i).im) p <
              ‖star u ⬝ᵥ (resProd (fun i => res (Matrix.of h + lam D N A) (z i)) s B *ᵥ v)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  -- the set of the class `Cl_N` of triples `(θ, μ, A)` and the statement `Good_N` on it
  let Cl : ∀ N : ℕ, Set (ℝ × Measure (Idx D N → Idx D N → ℂ) × Matrix (Fin N) (Fin N) ℂ) :=
    fun N => {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ LLClass D N C x.1 x.2.1 ∧
      opNorm x.2.2 ≤ (N : ℝ) ^ (-δA) ∧ 20 * opNorm x.2.2 ≤ 1}
  let Good : ∀ N : ℕ, ℝ × Measure (Idx D N → Idx D N → ℂ) × Matrix (Fin N) (Fin N) ℂ → Prop :=
    fun N x => ∀ z : Fin p → ℂ, (∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im ∧
        c₀ ≤ (N : ℝ) * (z i).im * (mExt (lam D N x.2.2) (z i)).im) →
      ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
        x.2.1 {h | (N : ℝ) ^ τ' * bndA4 (fun i => (mExt (lam D N x.2.2) (z i)).im)
            (fun i => (z i).im) p <
            ‖ntr (resProd (fun i => res (Matrix.of h + lam D N x.2.2) (z i)) s B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
          x.2.1 {h | (N : ℝ) ^ τ' *
                bndA4 (fun i => (mExt (lam D N x.2.2) (z i)).im) (fun i => (z i).im) p <
              ‖star u ⬝ᵥ (resProd (fun i => res (Matrix.of h + lam D N x.2.2) (z i)) s B *ᵥ v)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D'))
  have hpad : ∀ N₁ : ℕ, 2 ≤ N₁ → (Cl N₁).Nonempty → ∀ N, (Cl N).Nonempty := by
    rintro N₁ hN₁ ⟨x₁, h0, h1, hcl, -, -⟩ N
    obtain ⟨μ, hμ⟩ := llClass_pad D N₁ hN₁ C x₁.1 x₁.2.1 hcl N
    refine ⟨(x₁.1, μ, 0), h0, h1, hμ, ?_, ?_⟩
    · have : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
        unfold opNorm
        simp
      change opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ _
      rw [this]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · have : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
        unfold opNorm
        simp
      change 20 * opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ 1
      rw [this]
      norm_num
  have hseq : ∀ x : ∀ N, ℝ × Measure (Idx D N → Idx D N → ℂ) × Matrix (Fin N) (Fin N) ℂ,
      (∀ N, x N ∈ Cl N) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ¬ ¬ Good N (x N) := by
    intro x hx
    have hs : LLSeq D δA C (fun N => (x N).1) (fun N => (x N).2.1) (fun N => (x N).2.2) :=
      ⟨hD, hδA, fun N => ⟨(hx N).1, (hx N).2.1⟩, fun N => (hx N).2.2.1, fun N => (hx N).2.2.2.1⟩
    obtain ⟨N₀, hN₀⟩ := entprodG_local D p hp δA τ c₀ 1 hτ hc₀ le_rfl C (fun N => (x N).1)
      (fun N => (x N).2.1) (fun N => (x N).2.2) hs
      (fun N => by have := (hx N).2.2.2.2; linarith) (fun _ _ => 1) (fun _ _ => by simp)
      (fun N => {z | ∀ i, z i ∈ specDom τ N ∧ 0 < (z i).im ∧
        c₀ ≤ (N : ℝ) * (z i).im * (mExt (lam D N (x N).2.2) (z i)).im})
      (fun N z hz i => by
        refine ⟨(hz i).1, (hz i).2.1, ?_⟩
        rw [LargeEtaId_mSol_one _ _ (hz i).2.1]
        exact (hz i).2.2) τ' hτ' D' hD'
    refine ⟨N₀, fun N hN hbad => hbad ?_⟩
    intro z hz s B hB
    have hmS : (fun i => (mSol (lam D N (x N).2.2) (z i)).im) =
        fun i => (mExt (lam D N (x N).2.2) (z i)).im :=
      funext fun i => by
        have := LargeEtaId_mSol_one (lam D N (x N).2.2) (z i) (hz i).2.1
        rw [Complex.ofReal_one, one_smul] at this
        rw [this]
    have := hN₀ N hN z hz s B hB
    simp only [Complex.ofReal_one, one_smul] at this
    rw [hmS] at this
    exact this
  obtain ⟨N₁, hN₁⟩ := uniform_of_seq Cl (fun N x => ¬ Good N x) hpad hseq
  refine ⟨max N₁ ⌈(20 : ℝ) ^ (1 / δA)⌉₊, fun N hN θ hθ0 hθ1 μ hμ A hA z hz s B hB => ?_⟩
  have hN20 : (20 : ℝ) ^ (1 / δA) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hA20 : 20 * opNorm A ≤ 1 := by
    have := LargeEtaId_pow_le δA hδA N hN20
    linarith
  have hmem : (θ, μ, A) ∈ Cl N := ⟨hθ0, hθ1, hμ, hA, hA20⟩
  have hgood : Good N (θ, μ, A) :=
    not_not.mp (hN₁ N ((le_max_left _ _).trans hN) _ hmem)
  exact hgood z hz s B hB

end RBMTransitionEdge


end
