module

public import RBMTransitionEdge.MainDefs
public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic

@[expose] public section

/-!
# The four main results as statements

Theorem 2.1 [mix], Theorem 2.2 [MixEV], Theorem 2.4
[theorem_localized_eigenvector_localization] and Theorem 2.5 [theorem_localized_eigenvalue] under
Assumption 1 [main_assm], complex Hermitian case, each in the uniform form: the constants are
chosen before `N`, then the bound holds for every `N ≥ N₀`, every entry law, every admissible `A`
and every `k`. Events about the eigenvector `v_k` ask for some unit eigenvector of `λ_k`, so the
bounds hold for every choice of `v_k`. The events of Theorem 2.4 and of (2.10)
[eq:local_eigenvalue_perturb] are strict, so that `A = 0` is not a counterexample; for `D = 2`,
`Λ = [[0, A], [A*, 0]]`. The correlation comparison of Theorem 2.5 is stated for the correlation
functions `ρ^(n)`, through `corrPairing`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff

noncomputable section

namespace RBMTransitionEdge

/-- Theorem 2.2 [MixEV]: if (2.4) [eq:condA1] holds for `k = 1`, the `n` largest eigenvalues,
rescaled by `γ₊ (DN)^{2/3}` at `E⁺`, have the law of the `n` largest eigenvalues of a `DN × DN`
GUE up to `N^{-c}` against any smooth compactly supported `O`; the same at the left edge. -/
def MixEVStatement : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    ∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    (N : ℝ) ^ ((1 / 3 : ℝ) + εA) ≤ hsNorm A →
    |(∫ w, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (Eplus (lam D N A) - eigK (HLam D N A w) ((i : ℕ) + 1))) ∂(blockLaw D N L)) -
      (∫ w, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (2 - eigK (wig (D * N) w) ((i : ℕ) + 1))) ∂(gueLaw (D * N)))| ≤ (N : ℝ) ^ (-c) ∧
    |(∫ w, O (fun i => gammaMinus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (eigK (HLam D N A w) (D * N - (i : ℕ)) - Eminus (lam D N A))) ∂(blockLaw D N L)) -
      (∫ w, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (eigK (wig (D * N) w) (D * N - (i : ℕ)) + 2)) ∂(gueLaw (D * N)))| ≤ (N : ℝ) ^ (-c)

/-- Theorem 2.4 [theorem_localized_eigenvector_localization]: under (2.8) [eq:condA2], the first
bound with the strict inequality in the event, and its consequence (2.9) [eq:main_evector2]. -/
def LocalizedEvecStatement : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    (∀ ε : ℝ, 0 < ε → ε < 2 * εA → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
          ∀ a : Fin D, blockMass u a <
            1 - (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ε₀))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
          ∀ a : Fin D, blockMass u a ≤ 1 - (N : ℝ) ^ (-c)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-c)))

/-- The norm of the scalar `N^a` as a complex number. -/
private lemma Statements_norm (N : ℕ) (a : ℝ) : ‖((((N : ℝ) ^ a : ℝ) : ℂ))‖ = (N : ℝ) ^ a := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) a)]

/-- The Hilbert–Schmidt norm of `N^a I_N` is `N^{a + 1/2}`. -/
private lemma Statements_hs (N : ℕ) (hN : 1 ≤ N) (a : ℝ) :
    hsNorm ((((N : ℝ) ^ a : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = (N : ℝ) ^ (a + 1 / 2) := by
  rw [hsNorm_smul_one, Statements_norm N, Real.sqrt_eq_rpow,
    ← Real.rpow_add (Nat.cast_pos.mpr hN)]

/-- A smooth compactly supported function on `Fin n → ℝ` with value `1` at the origin. -/
private lemma Statements_bump (n : ℕ) :
    ∃ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 := by
  let f : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨f, f.contDiff, f.hasCompactSupport, f.one_of_mem_closedBall (by simp [f])⟩

/-- An admissible coupling for Theorems 2.1 [mix] and 2.2 [MixEV]: for `D = 3`,
`δ_A = ε_A = 1/100` and `k = 1`, the matrix `A = N^{-1/10} I_N` satisfies `‖A‖ ≤ N^{-δ_A}` of
Assumption 1 [main_assm] and (2.4) [eq:condA1]. -/
theorem admissible_delocalized (N : ℕ) (hN : 1 ≤ N) :
    opNorm ((((N : ℝ) ^ (-(1 / 10 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤
        (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤
        hsNorm ((((N : ℝ) ^ (-(1 / 10 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  refine ⟨?_, ?_⟩
  · rw [opNorm_smul_one N hN, Statements_norm N]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  · rw [rk_one 3 N (by omega), Real.one_rpow, mul_one, Statements_hs N hN]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

/-- An admissible coupling for Theorems 2.4 [theorem_localized_eigenvector_localization] and
2.5 [theorem_localized_eigenvalue]: for `D = 3`, `δ_A = ε_A = 1/100` and `k = 1`, the matrix
`A = N^{-1/4} I_N` satisfies `‖A‖ ≤ N^{-δ_A}` of Assumption 1 [main_assm] and (2.8)
[eq:condA2]. -/
theorem admissible_localized (N : ℕ) (hN : 1 ≤ N) :
    opNorm ((((N : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤
        (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      hsNorm ((((N : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤
        (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  refine ⟨?_, ?_⟩
  · rw [opNorm_smul_one N hN, Statements_norm N]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  · rw [rk_one 3 N (by omega), Real.one_rpow, mul_one, Statements_hs N hN]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

/-- The operator norm of `2 I_3` is `2`. -/
example : opNorm ((2 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 2 := by
  simpa using opNorm_smul_one 3 (by norm_num) 2

/-- `𝔯(1) = 1` for `D = 3`, `N = 5`. -/
example : rk 3 5 1 = 1 := rk_one 3 5 (by norm_num)

/-- `blockLaw 3 4` is a probability measure for the entry laws of `entryLaws_nonempty`. -/
example : IsProbabilityMeasure (blockLaw 3 4 (Classical.choice entryLaws_nonempty)) :=
  blockLaw_isProbabilityMeasure 3 4 _

/-- `gueLaw 12`, the GUE law of size `DN = 12`, is a probability measure. -/
example : IsProbabilityMeasure (gueLaw 12) := gueLaw_isProbabilityMeasure 12

/-- `H_Λ` is Hermitian for `D = 3`, `N = 4`, a coupling `A` and a configuration `w`. -/
example (A : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 3 → Coords 4) : (HLam 3 4 A w).IsHermitian :=
  HLam_isHermitian 3 4 A w

/-- The hypotheses of `MixStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`, `k = 1`,
with `C p = 2` and `A = N^{-1/10} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧ (1 : ℕ) ≤ 1 ∧ 1 ≤ 3 * N ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤ hsNorm A := by
  obtain ⟨L⟩ := entryLaws_nonempty
  exact ⟨L, _, blockLaw_isProbabilityMeasure 3 N L, by norm_num, by norm_num, by norm_num,
    (admissible_delocalized N hN).1, le_rfl, by omega, (admissible_delocalized N hN).2⟩

/-- The hypotheses of `MixEVStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`, with a
smooth compactly supported `O` on `Fin 2 → ℝ` that is nonzero at the origin, `C p = 2` and
`A = N^{-1/10} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ O : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) ≤ hsNorm A := by
  obtain ⟨L⟩ := entryLaws_nonempty
  obtain ⟨O, h1, h2, h3⟩ := Statements_bump 2
  refine ⟨O, h1, h2, h3, L, _, blockLaw_isProbabilityMeasure 3 N L, by norm_num, by norm_num,
    by norm_num, (admissible_delocalized N hN).1, ?_⟩
  have h := (admissible_delocalized N hN).2
  rwa [rk_one 3 N (by omega), Real.one_rpow, mul_one] at h

/-- The hypotheses of `LocalizedEvecStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`,
`ε = 1/100`, `k = 1`, with `C p = 2` and `A = N^{-1/4} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      (0 : ℝ) < 1 / 100 ∧ (1 / 100 : ℝ) < 2 * (1 / 100) ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧ (1 : ℕ) ≤ 1 ∧ 1 ≤ 3 * N ∧
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨L⟩ := entryLaws_nonempty
  exact ⟨L, _, blockLaw_isProbabilityMeasure 3 N L, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, (admissible_localized N hN).1, le_rfl, by omega,
    (admissible_localized N hN).2⟩

/-- The hypotheses of `LocalizedEvalStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`,
`ε = ε₀ = 1/100`, `k = 1`, with a smooth compactly supported `O` on `Fin 2 → ℝ` that is nonzero
at the origin, `C p = 2` and `A = N^{-1/4} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ O : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧ (1 / 100 : ℝ) < 2 * (1 / 100) ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧ (1 : ℕ) ≤ 1 ∧ 1 ≤ 3 * N ∧
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨L⟩ := entryLaws_nonempty
  obtain ⟨O, h1, h2, h3⟩ := Statements_bump 2
  exact ⟨O, h1, h2, h3, L, _, blockLaw_isProbabilityMeasure 3 N L, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, (admissible_localized N hN).1, le_rfl,
    by omega, (admissible_localized N hN).2⟩

#print axioms blockLaw_isProbabilityMeasure
#print axioms gueLaw_isProbabilityMeasure
#print axioms HLam_isHermitian
#print axioms opNorm_smul_one
#print axioms hsNorm_smul_one
#print axioms rk_one
#print axioms entryLaws_nonempty
#print axioms admissible_delocalized
#print axioms admissible_localized

end RBMTransitionEdge

end
