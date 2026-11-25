module

public import RBMTransitionEdge.Main.Statements
public import RBMTransitionEdge.Flow.Mix
public import RBMTransitionEdge.Edge.MixEV
public import RBMTransitionEdge.Localized.Repulsion
public import RBMTransitionEdge.Localized.Reflect
public import RBMTransitionEdge.Localized.Evec
public import RBMTransitionEdge.Localized.Eval

@[expose] public section

/-!
# The main results

Theorem 2.1 [mix] and Theorem 2.2 [MixEV] (the delocalized phase), Theorem 2.4
[theorem_localized_eigenvector_localization] and Theorem 2.5 [theorem_localized_eigenvalue] (the
localized phase) for every `k ≤ DN`, from their half ranges `2k ≤ DN + 1` and the reflection
`h ↦ -h`, `A ↦ -A`; the external inputs (the edge universality of the Wigner block for
Theorem 2.2, the level repulsion (5.14) [Wegner12] for Theorem 2.4) are explicit hypotheses.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff

namespace RBMTransitionEdge

/-- Theorem 2.4 [theorem_localized_eigenvector_localization], with the level repulsion (5.14)
[Wegner12] as an explicit hypothesis. -/
theorem localized_evec (hEI : ∀ C : ℕ → ℝ, EI2Hyp C) : LocalizedEvecStatement :=
  localized_evec_reflect (localized_evec_half hEI)

/-- Theorem 2.5 [theorem_localized_eigenvalue]. -/
theorem localized_eval : LocalizedEvalStatement :=
  localized_eval_reflect localized_eval_half

/-- The four main results: Theorem 2.1 [mix], Theorem 2.2 [MixEV] with the edge universality of
the Wigner block (Landon–Yau) as an explicit hypothesis, Theorem 2.4
[theorem_localized_eigenvector_localization] with the level repulsion (5.14) [Wegner12] as an
explicit hypothesis, and Theorem 2.5 [theorem_localized_eigenvalue]. -/
theorem main_theorems (hEI1 : LandonYauEdge) (hEI2 : ∀ C : ℕ → ℝ, EI2Hyp C) :
    MixStatement ∧ MixEVStatement ∧ LocalizedEvecStatement ∧ LocalizedEvalStatement :=
  ⟨mix, mixEV hEI1, localized_evec hEI2, localized_eval⟩

/-! ### Checks: the four statements applied at `D = 3`, `δ_A = ε_A = 1/100`, `C p = 2`, `k = 1` -/

/-- A smooth compactly supported function on `Fin n → ℝ` with value `1` at the origin. -/
private lemma Main_bump (n : ℕ) :
    ∃ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 := by
  let f : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨f, f.contDiff, f.hasCompactSupport, f.one_of_mem_closedBall (by simp [f])⟩

/-- Theorem 2.1 [mix] applied at `D = 3`, `δ_A = ε_A = 1/100`, `C p = 2`, `k = 1` and
`A = N^{-1/10} I_N`: every hypothesis holds for all `N ≥ 1`, and the conclusion is the bound for
the event of (2.5) [eq:main_evector1]. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤ hsNorm A ∧
      blockLaw 3 N L {w | ∃ u, IsUnitEigvec (HLam 3 N A w) (eigK (HLam 3 N A w) 1) u ∧
        ∃ a : Fin 3, (N : ℝ) ^ (-c) ≤ |blockMass u a - ((3 : ℕ) : ℝ)⁻¹|} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-c)) := by
  obtain ⟨c, hc, N₀, h⟩ := mix 3 (by norm_num) (1 / 100) (1 / 100) (by norm_num) (by norm_num)
    (fun _ => 2)
  obtain ⟨L⟩ := entryLaws_nonempty
  refine ⟨c, hc, max N₀ 1, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := admissible_delocalized N (le_trans (le_max_right _ _) hN)
  exact ⟨L, _, h1, h2, h N (le_trans (le_max_left _ _) hN) L _ h1 1 le_rfl
    (by have := le_trans (le_max_right N₀ 1) hN; omega) h2⟩

/-- Theorem 2.2 [MixEV] with `LandonYauEdge` as hypothesis, applied at `D = 3`,
`δ_A = ε_A = 1/100`, `C p = 2`, `n = 2`, a bump `O` with `O 0 = 1`, and `A = N^{-1/10} I_N`:
every hypothesis holds for all `N ≥ 1`, and the conclusion is the two edge comparisons. -/
example (hEI1 : LandonYauEdge) :
    ∃ O : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧ (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) ≤ hsNorm A ∧
      |(∫ w, O (fun i => gammaPlus (lam 3 N A) * ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (Eplus (lam 3 N A) - eigK (HLam 3 N A w) ((i : ℕ) + 1))) ∂(blockLaw 3 N L)) -
      (∫ w, O (fun i => ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (2 - eigK (wig (3 * N) w) ((i : ℕ) + 1))) ∂(gueLaw (3 * N)))| ≤ (N : ℝ) ^ (-c) ∧
      |(∫ w, O (fun i => gammaMinus (lam 3 N A) * ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (eigK (HLam 3 N A w) (3 * N - (i : ℕ)) - Eminus (lam 3 N A))) ∂(blockLaw 3 N L)) -
      (∫ w, O (fun i => ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (eigK (wig (3 * N) w) (3 * N - (i : ℕ)) + 2)) ∂(gueLaw (3 * N)))| ≤ (N : ℝ) ^ (-c) := by
  obtain ⟨O, hO1, hO2, hO3⟩ := Main_bump 2
  obtain ⟨c, hc, N₀, h⟩ := mixEV hEI1 3 (by norm_num) (1 / 100) (1 / 100) (by norm_num)
    (by norm_num) (fun _ => 2) 2 O hO1 hO2
  obtain ⟨L⟩ := entryLaws_nonempty
  refine ⟨O, hO1, hO2, hO3, c, hc, max N₀ 1, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := admissible_delocalized N (le_trans (le_max_right _ _) hN)
  have h2' := h2
  rw [rk_one 3 N (by have := le_trans (le_max_right N₀ 1) hN; omega), Real.one_rpow,
    mul_one] at h2'
  exact ⟨L, _, h1, h2', h N (le_trans (le_max_left _ _) hN) L _ h1 h2'⟩

/-- Theorem 2.4 [theorem_localized_eigenvector_localization] with the level repulsion as
hypothesis, applied at `D = 3`, `δ_A = ε_A = 1/100`, `ε = 1/100 < 2ε_A`, `C p = 2`, `k = 1` and
`A = N^{-1/4} I_N`: both bounds, with every hypothesis holding for all `N ≥ 1`. -/
example (hEI2 : ∀ C : ℕ → ℝ, EI2Hyp C) :
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
        opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ∧
        blockLaw 3 N L {w | ∃ u, IsUnitEigvec (HLam 3 N A w) (eigK (HLam 3 N A w) 1) u ∧
            ∀ a : Fin 3, blockMass u a <
              1 - (N : ℝ) ^ (-(2 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (2 / 3 : ℝ) * hsNorm A ^ 2} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-ε₀))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
        opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ∧
        blockLaw 3 N L {w | ∃ u, IsUnitEigvec (HLam 3 N A w) (eigK (HLam 3 N A w) 1) u ∧
            ∀ a : Fin 3, blockMass u a ≤ 1 - (N : ℝ) ^ (-c)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-c))) := by
  obtain ⟨h₁, h₂⟩ := localized_evec hEI2 3 (by norm_num) (1 / 100) (1 / 100) (by norm_num)
    (by norm_num) (fun _ => 2)
  obtain ⟨L⟩ := entryLaws_nonempty
  refine ⟨?_, ?_⟩
  · obtain ⟨ε₀, hε₀, N₀, h⟩ := h₁ (1 / 100) (by norm_num) (by norm_num)
    refine ⟨ε₀, hε₀, max N₀ 1, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := admissible_localized N (le_trans (le_max_right _ _) hN)
    exact ⟨L, _, h1, h2, h N (le_trans (le_max_left _ _) hN) L _ h1 1 le_rfl
      (by have := le_trans (le_max_right N₀ 1) hN; omega) h2⟩
  · obtain ⟨c, hc, N₀, h⟩ := h₂
    refine ⟨c, hc, max N₀ 1, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := admissible_localized N (le_trans (le_max_right _ _) hN)
    exact ⟨L, _, h1, h2, h N (le_trans (le_max_left _ _) hN) L _ h1 1 le_rfl
      (by have := le_trans (le_max_right N₀ 1) hN; omega) h2⟩

/-- Theorem 2.5 [theorem_localized_eigenvalue] applied at `D = 3`, `δ_A = ε_A = 1/100`,
`ε = ε₀ = 1/100` (so `ε₀ < 2ε`), `C p = 2`, `k = 1`, a bump `O` with `O 0 = 1` and
`A = N^{-1/4} I_N`: the bounds (2.10) [eq:local_eigenvalue_perturb] and (2.11) [eq:main_perurb] and
the correlation comparison, with every hypothesis holding for all `N ≥ 1`. -/
example :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
        opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ∧
        blockLaw 3 N L {w | (N : ℝ) ^ (-1 + 1 / 100 : ℝ) * hsNorm A < |shiftX 3 N A 1 w|} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-(1 / 100 : ℝ)))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
        opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ∧
        blockLaw 3 N L {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤
            |shiftX 3 N A 1 w|} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c))) ∧
    (∃ O : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
        opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
        hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ∧
        |(∫ w, corrPairing (3 * N) 2 (((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk 3 N 1 ^ (1 / 3 : ℝ))
            (quant (rho (lam 3 N A)) (3 * N) 1) O (eigK (HLam 3 N A w)) ∂(blockLaw 3 N L)) -
          (∫ w, corrPairing (3 * N) 2 (((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk 3 N 1 ^ (1 / 3 : ℝ))
            (quant rhoSc (3 * N) 1) O (eigK (blockH 3 N w)) ∂(blockLaw 3 N L))| ≤
          (N : ℝ) ^ (-c)) := by
  obtain ⟨h₁, h₂, h₃⟩ := localized_eval 3 (by norm_num) (1 / 100) (1 / 100) (by norm_num)
    (by norm_num) (fun _ => 2)
  obtain ⟨L⟩ := entryLaws_nonempty
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨N₀, h⟩ := h₁ (1 / 100) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := admissible_localized N (le_trans (le_max_right _ _) hN)
    exact ⟨L, _, h1, h2, h N (le_trans (le_max_left _ _) hN) L _ h1 1 le_rfl
      (by have := le_trans (le_max_right N₀ 1) hN; omega) h2⟩
  · obtain ⟨c, hc, N₀, h⟩ := h₂
    refine ⟨c, hc, max N₀ 1, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := admissible_localized N (le_trans (le_max_right _ _) hN)
    exact ⟨L, _, h1, h2, h N (le_trans (le_max_left _ _) hN) L _ h1 1 le_rfl
      (by have := le_trans (le_max_right N₀ 1) hN; omega) h2⟩
  · obtain ⟨O, hO1, hO2, hO3⟩ := Main_bump 2
    obtain ⟨c, hc, N₀, h⟩ := h₃ 2 O hO1 hO2
    refine ⟨O, hO1, hO2, hO3, c, hc, max N₀ 1, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := admissible_localized N (le_trans (le_max_right _ _) hN)
    exact ⟨L, _, h1, h2, h N (le_trans (le_max_left _ _) hN) L _ h1 1 le_rfl
      (by have := le_trans (le_max_right N₀ 1) hN; omega) h2⟩

/-- `main_theorems` gives each of the four statements, so each instance above applies to the
corresponding component. -/
example (hEI1 : LandonYauEdge) (hEI2 : ∀ C : ℕ → ℝ, EI2Hyp C) :
    MixStatement ∧ MixEVStatement ∧ LocalizedEvecStatement ∧ LocalizedEvalStatement :=
  main_theorems hEI1 hEI2

#print axioms main_theorems

end RBMTransitionEdge
