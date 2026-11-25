module

public import RBMTransitionEdge.Localized.Expansion.Rem2Bridge
public import RBMTransitionEdge.Localized.Expansion.Direct
public import RBMTransitionEdge.Localized.Expansion.PkgGauss
public import RBMTransitionEdge.Localized.Expansion.PkgInv
public import RBMTransitionEdge.Localized.Expansion.Rem2OneRule
public import RBMTransitionEdge.Localized.Expansion.Rem2TwoRule
public import RBMTransitionEdge.Localized.Expansion.Rem2ThreeRule
public import RBMTransitionEdge.Localized.Expansion.PkgLeafRule
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.PkgBound
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.Direct
import all RBMTransitionEdge.Localized.Expansion.PkgSharp
import all RBMTransitionEdge.Localized.Expansion.PkgBound
import all RBMTransitionEdge.Localized.Expansion.PkgWords

@[expose] public section

/-!
# The remainder terms of Lemma 5.5

Lemma 5.5 [claim_estimate_remainder_terms] for the signed sum over the four starting loops of
(5.29) [expansion_of_im], at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and
5.4 [lemma_localized_eigenvalue_local_law]: the further terminal cases (i)–(iii), the terms
`𝓔^{(2)}_𝓡(p, q)` of the expressions of Types I, II, III of the further expansion, and the
remainder `𝓡_𝒯(p, q)` of every expression of the expansion of §5.3 with `p + q ≥ 2`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The further terminal cases (i)–(iii) in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: for `R = 0`, `p₀ + q₀ = 2`, a derivative structure `𝓡₀` and an
expression of its further expansion to which no rule applies, the signed sum over the four starting
loops of (5.29) [expansion_of_im] of the cumulant sum `outer` is at most
`N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemmas 5.2 and 5.4. -/
theorem pkg_leaf_bound (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2)
    (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fIter ε j [R₀]) (hf : R.ffocus = none) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer (evecEnv D N A k ε s) μ p₀ q₀‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              R.outer (evalEnv D N A k ε t s) μ p₀ q₀‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  obtain ⟨hlab, hrule⟩ := pkg_rule_leaf ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hf
  exact pkg_leaf_bridge D hD δA εA ε hδA hεA hε hε' hε'' C R p₀ q₀ hpq hlab ⟨_, hrule⟩

/-- Example 5.7 [example_estimate_reminder_reminder_terms] and the companion cases (1)–(4), Type I:
for `R = 0`, `p₀ + q₀ = 2`, a derivative structure `𝓡₀`, an expression of Type 1 expanded in its
further expansion and `p + q ≥ 2`, the signed sum over the four starting loops of (5.29)
[expansion_of_im] of `𝓔^{(2)}(p, q)` inside the cumulant sum is at most `N^{τ + 2ε} N^{-5/3}
𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemmas 5.2 and 5.4. -/
theorem pkg_rem2_one (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2)
    (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 1) (p q : ℕ) (hpq' : 2 ≤ p + q) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer2 (evecEnv D N A k ε s) μ p₀ q₀ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              R.outer2 (evalEnv D N A k ε t s) μ p₀ q₀ p q‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  exact pkg_rem2_bridge D hD δA εA ε hδA hεA hε hε' hε'' C R p₀ q₀ hpq p q fun R' hR' =>
    ⟨_, pkg_rule_one ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q hpq' R' hR'⟩

/-- Example 5.7 [example_estimate_reminder_reminder_terms] and the companion cases (5)–(7), Type II:
for `R = 0`, `p₀ + q₀ = 2`, a derivative structure `𝓡₀`, an expression of Type 2 expanded in its
further expansion and `p + q ≥ 2`, the signed sum over the four starting loops of (5.29)
[expansion_of_im] of `𝓔^{(2)}(p, q)` inside the cumulant sum is at most `N^{τ + 2ε} N^{-5/3}
𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemmas 5.2 and 5.4. -/
theorem pkg_rem2_two (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2)
    (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 2) (p q : ℕ) (hpq' : 2 ≤ p + q) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer2 (evecEnv D N A k ε s) μ p₀ q₀ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              R.outer2 (evalEnv D N A k ε t s) μ p₀ q₀ p q‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  exact pkg_rem2_bridge D hD δA εA ε hδA hεA hε hε' hε'' C R p₀ q₀ hpq p q fun R' hR' =>
    ⟨_, pkg_rule_two ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q hpq' R' hR'⟩

/-- Example 5.7 [example_estimate_reminder_reminder_terms] and the companion cases (8)–(10), Type
III: for `R = 0`, `p₀ + q₀ = 2`, a derivative structure `𝓡₀`, an expression of Type 3 expanded in
its further expansion and `p + q ≥ 2`, the signed sum over the four starting loops of (5.29)
[expansion_of_im] of `𝓔^{(2)}(p, q)` inside the cumulant sum is at most `N^{τ + 2ε} N^{-5/3}
𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemmas 5.2 and 5.4. -/
theorem pkg_rem2_three (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2)
    (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (j : ℕ) (R : PkgExpr)
    (hR : R ∈ fInner ε j [R₀]) (hty : R.ptype = 3) (p q : ℕ) (hpq' : 2 ≤ p + q) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer2 (evecEnv D N A k ε s) μ p₀ q₀ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              R.outer2 (evalEnv D N A k ε t s) μ p₀ q₀ p q‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  exact pkg_rem2_bridge D hD δA εA ε hδA hεA hε hε' hε'' C R p₀ q₀ hpq p q fun R' hR' =>
    ⟨_, pkg_rule_three ε n T hT hR0 p₀ q₀ hpq R₀ hR₀ j R hR hty p q hpq' R' hR'⟩

/-! ### Signed sums over the four starting loops of (5.29) [expansion_of_im] -/

open private Dr_slot Dr_T Dr_T_nonneg Dr_Bd Dr_rk Dr_large Dr_final
  from RBMTransitionEdge.Localized.Expansion.Direct
open private PS_op_le_hs from RBMTransitionEdge.Localized.Expansion.PkgSharp
open private PB_counts from RBMTransitionEdge.Localized.Expansion.PkgBound
open private charsP_eq isResP from RBMTransitionEdge.Localized.Expansion.PkgWords

/-- The four slots of Lemma 5.2 [lemma_localized_eigenvector_local_law], or the four slots of
Lemma 5.4 [lemma_localized_eigenvalue_local_law] at one `t ∈ [0, 1]`, as a function of the flags. -/
private def LR_kind (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ)
    (E : (Fin 2 → Bool) → LoopEnv D N) : Prop :=
  E = evecEnv D N A k ε ∨ ∃ t ∈ Set.Icc (0 : ℝ) 1, E = evalEnv D N A k ε t

/-- The signed sum over the four starting loops of (5.29) [expansion_of_im] of `G` is
`≺ N^{2ε} 𝔗` uniformly at the slots. -/
private def LR_Bd (D : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ)
    (G : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
    hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
    ∀ E : (Fin 2 → Bool) → LoopEnv D N, LR_kind D N A k ε E →
      ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * G N μ (E s)‖ ≤
        K * (N : ℝ) ^ τ * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k)

/-- The form of the conclusions of the five theorems of this file, for the quantity `G`. -/
private def LR_pin (D : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ)
    (G : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
    hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
          G N μ (evecEnv D N A k ε s)‖ ≤
        (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
          hsNorm A ^ 2) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            G N μ (evalEnv D N A k ε t s)‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2)

section Bd

variable {D : ℕ} {δA εA ε : ℝ} {C : ℕ → ℝ}

private lemma LR_of_pin {G : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ}
    (h : LR_pin D δA εA ε C G) : LR_Bd D δA εA ε C G := by
  intro τ hτ
  obtain ⟨N₀, hN₀⟩ := h τ hτ
  refine ⟨1, zero_le_one, max N₀ 1, fun N hN μ hμ A hA k hk hkN hhs E hE => ?_⟩
  have hN0 : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have he : (N : ℝ) ^ (τ + 2 * ε) * Dr_T D N A k =
      1 * (N : ℝ) ^ τ * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k) := by
    rw [Real.rpow_add hN0]
    ring
  obtain ⟨h1, h2⟩ := hN₀ N (le_trans (le_max_left _ _) hN) μ hμ A hA k hk hkN hhs
  rw [← he]
  rcases hE with rfl | ⟨t, ht, rfl⟩
  · exact h1
  · exact h2 t ht

private lemma LR_to_pin {G : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ}
    (h : LR_Bd D δA εA ε C G) : LR_pin D δA εA ε C G := by
  intro τ hτ
  obtain ⟨K, hK, N₁, hN₁⟩ := h (τ / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Dr_large K (τ / 2) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN μ hμ A hA k hk hkN hhs => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hb : ∀ E : (Fin 2 → Bool) → LoopEnv D N, LR_kind D N A k ε E →
      ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * G N μ (E s)‖ ≤
        (N : ℝ) ^ (τ + 2 * ε) * Dr_T D N A k := by
    intro E hE
    refine (hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) μ hμ A hA k hk
      hkN hhs E hE).trans ?_
    have := Dr_final N hN1 τ ε 1 K (Dr_T D N A k) (Dr_T_nonneg D N A k)
      (by rw [one_mul]; exact hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN))
      (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    simpa only [one_mul] using this
  exact ⟨hb (evecEnv D N A k ε) (Or.inl rfl),
    fun t ht => hb (evalEnv D N A k ε t) (Or.inr ⟨t, ht, rfl⟩)⟩

private lemma LR_zero : LR_Bd D δA εA ε C fun _ _ _ => 0 :=
  fun _ _ => ⟨0, le_rfl, 0, fun N _ μ _ A _ k _ _ _ E _ => by simp⟩

private lemma LR_add {G₁ G₂ : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ}
    (h₁ : LR_Bd D δA εA ε C G₁) (h₂ : LR_Bd D δA εA ε C G₂) :
    LR_Bd D δA εA ε C fun N μ e => G₁ N μ e + G₂ N μ e := by
  intro τ hτ
  obtain ⟨K₁, hK₁, N₁, a₁⟩ := h₁ τ hτ
  obtain ⟨K₂, hK₂, N₂, a₂⟩ := h₂ τ hτ
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, max N₁ N₂, fun N hN μ hμ A hA k hk hkN hhs E hE => ?_⟩
  have b₁ := a₁ N (le_trans (le_max_left _ _) hN) μ hμ A hA k hk hkN hhs E hE
  have b₂ := a₂ N (le_trans (le_max_right _ _) hN) μ hμ A hA k hk hkN hhs E hE
  simp only [mul_add, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans ?_
  linarith

private lemma LR_list {α : Type*}
    (G : α → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ) :
    ∀ L : List α, (∀ x ∈ L, LR_Bd D δA εA ε C (G x)) →
      LR_Bd D δA εA ε C fun N μ e => (L.map fun x => G x N μ e).sum
  | [], _ => fun _ _ => ⟨0, le_rfl, 0, fun N _ μ _ A _ k _ _ _ E _ => by simp⟩
  | x :: L, h => by
    have := LR_add (h x List.mem_cons_self)
      (LR_list G L fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa using this

private lemma LR_fsum {α : Type*}
    (G : α → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ) (s : Finset α)
    (h : ∀ x ∈ s, LR_Bd D δA εA ε C (G x)) :
    LR_Bd D δA εA ε C fun N μ e => ∑ x ∈ s, G x N μ e := by
  have := LR_list G s.toList fun x hx => h x (Finset.mem_toList.1 hx)
  simpa only [Finset.sum_map_toList] using this

/-- A bound at each slot gives a bound of the signed sum. -/
private lemma LR_of_env {G : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℂ}
    (h : Dr_Bd D δA εA ε C fun N μ e => ‖G N μ e‖) : LR_Bd D δA εA ε C G := by
  intro τ hτ
  obtain ⟨K, hK, N₀, hN₀⟩ := h τ hτ
  refine ⟨4 * K, mul_nonneg (by norm_num) hK, N₀,
    fun N hN μ hμ A hA k hk hkN hhs E hE => ?_⟩
  have hs : ∀ s, Dr_slot D N A k ε (E s) := by
    intro s
    rcases hE with rfl | ⟨t, ht, rfl⟩
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr ⟨t, ht, s, rfl⟩
  have hb : ∀ s : Fin 2 → Bool, ‖(if s 0 = s 1 then (1 : ℂ) else -1) * G N μ (E s)‖ ≤
      K * (N : ℝ) ^ τ * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k) := by
    intro s
    rw [norm_mul, show ‖(if s 0 = s 1 then (1 : ℂ) else -1)‖ = 1 by split_ifs <;> simp, one_mul]
    exact hN₀ N hN μ hμ A hA k hk hkN hhs (E s) (hs s)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s _ => hb s).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin 2 → Bool) : ℝ) = 4 := by simp
  rw [hcard]
  ring

end Bd

/-! ### The cumulant sum `outer` as a linear map of the function of the labels -/

/-- The cumulant sum of `outer`, with a function `F` of the labels `α, β` in place of `E 𝓡`. -/
private def LR_O {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) :
    (Idx D N → Idx D N → ℂ) →+ ℂ where
  toFun F := -((D : ℂ) * N)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
    if i.1 = j.1 then
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) * F i j
    else 0
  map_zero' := by simp
  map_add' F G := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [mul_add]

private lemma LR_O_apply {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ)
    (F : Idx D N → Idx D N → ℂ) :
    LR_O μ p q F = -((D : ℂ) * N)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
      if i.1 = j.1 then
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) * F i j
      else 0 := rfl

/-- `outer` is the cumulant sum of the function `E 𝓡` of the labels `α, β`. -/
private lemma LR_outer {D N : ℕ} (e : LoopEnv D N) (μ : Measure (Idx D N → Idx D N → ℂ))
    (p q : ℕ) (R : PkgExpr) :
    R.outer e μ p q =
      LR_O μ p q (fun i j => ∫ h, R.evalH e (fun l => if l = 0 then i else j) h ∂μ) := by
  rw [LR_O_apply]
  rfl

/-- `outer2` is the cumulant sum of the function `𝓔^{(2)}(p, q)` of the labels `α, β`. -/
private lemma LR_outer2 {D N : ℕ} (e : LoopEnv D N) (μ : Measure (Idx D N → Idx D N → ℂ))
    (p₀ q₀ p q : ℕ) (R : PkgExpr) :
    R.outer2 e μ p₀ q₀ p q =
      LR_O μ p₀ q₀ (fun i j => R.rem2PQ e μ (fun l => if l = 0 then i else j) p q) := by
  rw [LR_O_apply]
  rfl

private lemma LR_O_list {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) {α : Type*}
    (f : α → Idx D N → Idx D N → ℂ) :
    ∀ L : List α, (L.map fun x => LR_O μ p q (f x)).sum =
      LR_O μ p q (fun i j => (L.map fun x => f x i j).sum)
  | [] => by
    simp only [List.map_nil, List.sum_nil]
    exact (map_zero (LR_O μ p q)).symm
  | x :: L => by
    simp only [List.map_cons, List.sum_cons]
    rw [LR_O_list μ p q f L, ← map_add]
    rfl

private lemma LR_O_list' {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) {α : Type*}
    (g : α → ℂ) (f : α → Idx D N → Idx D N → ℂ) (hg : ∀ x, g x = LR_O μ p q (f x))
    (L : List α) :
    (L.map g).sum = LR_O μ p q (fun i j => (L.map fun x => f x i j).sum) := by
  rw [← LR_O_list μ p q f L]
  exact congrArg List.sum (List.map_congr_left fun x _ => hg x)

private lemma LR_O_fsum {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) {α : Type*}
    (s : Finset α) (f : α → Idx D N → Idx D N → ℂ) :
    LR_O μ p q (fun i j => ∑ x ∈ s, f x i j) = ∑ x ∈ s, LR_O μ p q (f x) := by
  rw [← map_sum]
  congr 1
  funext i j
  simp [Finset.sum_apply]

/-- The inner sum over `(p', q')` of the cumulant sums `outer2` of one expression. -/
private lemma LR_O_inner {D N : ℕ} (e : LoopEnv D N) (μ : Measure (Idx D N → Idx D N → ℂ))
    (p q m : ℕ) (R : PkgExpr) :
    (∑ p' ∈ Finset.range (m + 1), ∑ q' ∈ Finset.range (m + 1 - p'),
      if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0) =
    LR_O μ p q (fun i j => ∑ p' ∈ Finset.range (m + 1), ∑ q' ∈ Finset.range (m + 1 - p'),
      if 2 ≤ p' + q' then R.rem2PQ e μ (fun l => if l = 0 then i else j) p' q' else 0) := by
  rw [LR_O_fsum]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [LR_O_fsum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  split_ifs
  · exact LR_outer2 e μ p q p' q' R
  · exact (map_zero _).symm

/-- `outer` minus the leaves minus the inner nodes, as one cumulant sum. -/
private lemma LR_err_eq {D N : ℕ} (e : LoopEnv D N) (μ : Measure (Idx D N → Idx D N → ℂ))
    (p q m : ℕ) (R₀ : PkgExpr) (L₁ L₂ : List PkgExpr) :
    R₀.outer e μ p q - (L₁.map fun R => R.outer e μ p q).sum -
      (L₂.map fun R => ∑ p' ∈ Finset.range (m + 1), ∑ q' ∈ Finset.range (m + 1 - p'),
        if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0).sum =
    LR_O μ p q (fun i j => (∫ h, R₀.evalH e (fun l => if l = 0 then i else j) h ∂μ) -
      (L₁.map fun R => ∫ h, R.evalH e (fun l => if l = 0 then i else j) h ∂μ).sum -
      (L₂.map fun R => ∑ p' ∈ Finset.range (m + 1), ∑ q' ∈ Finset.range (m + 1 - p'),
        (if 2 ≤ p' + q' then R.rem2PQ e μ (fun l => if l = 0 then i else j) p' q'
          else 0)).sum) := by
  have h1 : (L₁.map fun R => R.outer e μ p q).sum = LR_O μ p q (fun i j =>
      (L₁.map fun R => ∫ h, R.evalH e (fun l => if l = 0 then i else j) h ∂μ).sum) := by
    exact LR_O_list' μ p q _ _ (fun R => LR_outer e μ p q R) L₁
  have h2 : (L₂.map fun R => ∑ p' ∈ Finset.range (m + 1), ∑ q' ∈ Finset.range (m + 1 - p'),
        if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0).sum =
      LR_O μ p q (fun i j => (L₂.map fun R => ∑ p' ∈ Finset.range (m + 1),
        ∑ q' ∈ Finset.range (m + 1 - p'),
          (if 2 ≤ p' + q' then R.rem2PQ e μ (fun l => if l = 0 then i else j) p' q'
            else 0)).sum) := by
    exact LR_O_list' μ p q _ _ (fun R => LR_O_inner e μ p q m R) L₂
  rw [h1, h2, LR_outer e μ p q R₀, ← map_sub, ← map_sub]
  congr 1

/-- (2.27) [eq:bdd_cumu] in the cumulant sum: `|outer| ≤ D N K M` when every cumulant is at most
`K` and the function of the labels is at most `M`. -/
private lemma LR_O_le {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (μ : Measure (Idx D N → Idx D N → ℂ))
    (p q : ℕ) (Kc M : ℝ) (hKc : 0 ≤ Kc) (hM : 0 ≤ M)
    (hc : ∀ i j : Idx D N, ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤ Kc)
    (F : Idx D N → Idx D N → ℂ) (hF : ∀ i j, ‖F i j‖ ≤ M) :
    ‖LR_O μ p q F‖ ≤ D * N * Kc * M := by
  have hDN : (0 : ℝ) < (D : ℝ) * N := by
    have h1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hterm : ∀ i j : Idx D N, ‖(if i.1 = j.1 then
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) * F i j else 0 : ℂ)‖ ≤ Kc * M := by
    intro i j
    by_cases hij : i.1 = j.1
    · simp only [hij, ↓reduceIte]
      rw [norm_mul, norm_mul, norm_div, norm_pow]
      have h1 : 1 ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
        rw [Complex.norm_natCast]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero p)
          (Nat.factorial_ne_zero q))
      have h2 : ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ^ (p + q) ≤ 1 := by
        refine pow_le_one₀ (norm_nonneg _) ?_
        by_cases h : i = j
        · simp only [h, ↓reduceIte]
          norm_num
        · simp only [h, ↓reduceIte, norm_one, le_refl]
      have h3 : ‖ccum (μ.map fun h => h i j) p (q + 1)‖ /
          ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ ≤ Kc :=
        (div_le_self (norm_nonneg _) h1).trans (hc i j)
      calc _ ≤ Kc * 1 * M :=
            mul_le_mul (mul_le_mul h3 h2 (by positivity) hKc) (hF i j) (norm_nonneg _)
              (by positivity)
        _ = Kc * M := by ring
    · simp only [hij, ↓reduceIte, norm_zero]
      exact mul_nonneg hKc hM
  have hS : ∀ g : Idx D N → Idx D N → ℂ, (∀ i j, ‖g i j‖ ≤ Kc * M) →
      ‖∑ i : Idx D N, ∑ j : Idx D N, g i j‖ ≤ ((D : ℝ) * N) ^ 2 * (Kc * M) := by
    intro g hg
    calc ‖∑ i : Idx D N, ∑ j : Idx D N, g i j‖ ≤ ∑ i : Idx D N, ‖∑ j : Idx D N, g i j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Idx D N, ∑ j : Idx D N, Kc * M :=
          Finset.sum_le_sum fun i _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hg i j)
      _ = ((D : ℝ) * N) ^ 2 * (Kc * M) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  rw [LR_O_apply, norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (hS _ hterm) (inv_nonneg.2 hDN.le)).trans (le_of_eq ?_)
  field_simp

/-! ### Exponents -/

/-- `N · N^{-3/2} · N^{-2} ‖A‖² ≤ N^{2ε} 𝔗`, from `‖A‖ ≤ ‖A‖_HS` and `𝔯(k) ≥ 1`. -/
private lemma LR_tail (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (hrk : 1 ≤ rk D N k) (ε : ℝ) (hε : 0 ≤ ε) :
    (N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2) ≤
      (N : ℝ) ^ (2 * ε) * Dr_T D N A k := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : (N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N : ℝ) ^ (-(2 : ℝ)) =
      (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
    calc (N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N : ℝ) ^ (-(2 : ℝ)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N : ℝ) ^ (-(2 : ℝ)) := by
          rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + -(3 / 2 : ℝ) + -(2 : ℝ)) := by
          rw [Real.rpow_add hN0, Real.rpow_add hN0]
      _ = (N : ℝ) ^ (-(5 / 2 : ℝ)) := by norm_num
  have hop : opNorm A ^ 2 ≤ hsNorm A ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (PS_op_le_hs A) 2
  have h52 : (N : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hr : 1 ≤ rk D N k ^ (2 / 3 : ℝ) := Real.one_le_rpow hrk (by norm_num)
  have hε1 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have h53 : 0 ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hT0 := Dr_T_nonneg D N A k
  calc (N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2) =
        (N : ℝ) ^ (-(5 / 2 : ℝ)) * opNorm A ^ 2 := by rw [← e1]; ring
    _ ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) * (1 * hsNorm A ^ 2) := by
        rw [one_mul]
        exact mul_le_mul h52 hop (sq_nonneg _) h53
    _ ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) * (rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr (sq_nonneg _)) h53
    _ = 1 * Dr_T D N A k := by unfold Dr_T; ring
    _ ≤ (N : ℝ) ^ (2 * ε) * Dr_T D N A k := mul_le_mul_of_nonneg_right hε1 hT0

/-- At `η = N^{-2/3+ε} 𝔯^{-1/3}`, `1 ≤ 𝔯 ≤ D N`, `E ≥ 0` and `a ≥ 2 + (1 - ε) E` (that is,
`Ψ′ ≥ 4`): `N^{-a} η^{-E} ≤ D^{E/3} N^{-2}`. -/
private lemma LR_psi_exp (D N : ℕ) (hN : 1 ≤ N) (r ε : ℝ) (hr : 1 ≤ r) (hrD : r ≤ D * N)
    (a E : ℤ) (hE : 0 ≤ E) (ha : 2 + (E : ℝ) * (1 - ε) ≤ a) :
    (N : ℝ) ^ (-a) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * r ^ (-(1 / 3 : ℝ))) ^ (-E) ≤
      (D : ℝ) ^ ((E : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr0 : 0 < r := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hE' : (0 : ℝ) ≤ E := by exact_mod_cast hE
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hN0.le, ← Real.rpow_mul hr0.le]
  push_cast
  have h1 : (N : ℝ) ^ (-(a : ℝ)) ≤ (N : ℝ) ^ (-(2 + (E : ℝ) * (1 - ε))) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : r ^ (-(1 / 3 : ℝ) * -(E : ℝ)) ≤ ((D : ℝ) * N) ^ (-(1 / 3 : ℝ) * -(E : ℝ)) :=
    Real.rpow_le_rpow hr0.le hrD (by nlinarith)
  rw [Real.mul_rpow hD0 hN0.le] at h2
  have h3 : (N : ℝ) ^ (-(2 + (E : ℝ) * (1 - ε))) * (N : ℝ) ^ ((-(2 / 3 : ℝ) + ε) * -(E : ℝ)) *
      (N : ℝ) ^ (-(1 / 3 : ℝ) * -(E : ℝ)) = (N : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have hD3 : (D : ℝ) ^ (-(1 / 3 : ℝ) * -(E : ℝ)) = (D : ℝ) ^ ((E : ℝ) / 3) := by
    congr 1
    ring
  calc (N : ℝ) ^ (-(a : ℝ)) * ((N : ℝ) ^ ((-(2 / 3 : ℝ) + ε) * -(E : ℝ)) *
        r ^ (-(1 / 3 : ℝ) * -(E : ℝ))) ≤
        (N : ℝ) ^ (-(2 + (E : ℝ) * (1 - ε))) * ((N : ℝ) ^ ((-(2 / 3 : ℝ) + ε) * -(E : ℝ)) *
          ((D : ℝ) ^ (-(1 / 3 : ℝ) * -(E : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ) * -(E : ℝ)))) := by
        gcongr
    _ = (D : ℝ) ^ ((E : ℝ) / 3) * ((N : ℝ) ^ (-(2 + (E : ℝ) * (1 - ε))) *
          (N : ℝ) ^ ((-(2 / 3 : ℝ) + ε) * -(E : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ) * -(E : ℝ))) := by
        rw [hD3]
        ring
    _ = (D : ℝ) ^ ((E : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ)) := by rw [h3]

private lemma LR_ptype_le (R : PkgExpr) : R.ptype ≤ 3 := by
  unfold PkgExpr.ptype
  split
  · omega
  · split_ifs <;> omega

/-- `𝔯(k) ≤ D N` under `2 k ≤ D N + 1`. -/
private lemma LR_rk_le (D N k : ℕ) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) :
    rk D N k ≤ (D : ℝ) * N := by
  unfold rk
  have : min k (D * N + 1 - k) ≤ D * N := by omega
  exact_mod_cast this

/-! ### The leaves stopped by `Ψ′ ≥ 4` and one derivative structure -/

/-- A leaf of the further expansion stopped by `Ψ′ ≥ 4`: the generic bound of the class `𝓡` in
the cumulant sum `outer`, at `p + q = 2`, is `≺ N^{-5/2} ‖A‖²`, below `N^{2ε} 𝔗`. -/
private lemma LR_psi (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (R : PkgExpr)
    (hR : R.wf = true) (hψ : 4 ≤ R.psiP ε) (p q : ℕ) (hpq : p + q = 2) :
    Dr_Bd D δA εA ε C fun _ μ e => ‖R.outer e μ p q‖ := by
  intro τ hτ
  obtain ⟨c₀, K, hc₀, -, N₁, hN₁⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨Kc, hKc⟩ := llClass_ccum_le C p (q + 1)
  obtain ⟨N₂, hN₂⟩ := pkg_generic_bound D hD δA (ε / 2) c₀ 1 K hδA (by positivity) hc₀ le_rfl C R
    hR τ hτ
  obtain ⟨-, -, -, z, hz2, hSaz⟩ := PB_counts R hR
  have hch := charsP_eq R
  have hE0 : 0 ≤ R.charsP.1 - R.charsP.2.1 + R.charsP.2.2.1 + 2 := by
    have e1 : (R.loops.map fun w => w.countP isResP).sum =
        (R.loops.map (List.countP isResP)).sum := rfl
    rw [hch]
    simp only
    rw [e1]
    omega
  have hψ' : 2 + ((R.charsP.1 - R.charsP.2.1 + R.charsP.2.2.1 + 2 : ℤ) : ℝ) * (1 - ε) ≤
      ((R.charsP.2.2.2 + R.charsP.2.2.1 : ℤ) : ℝ) := by
    unfold PkgExpr.psiP at hψ
    rcases hc : R.charsP with ⟨m, n, u, S⟩
    rw [hc] at hψ
    simp only at hψ ⊢
    push_cast at hψ ⊢
    nlinarith
  set E : ℤ := R.charsP.1 - R.charsP.2.1 + R.charsP.2.2.1 + 2 with hE_def
  set a : ℤ := R.charsP.2.2.2 + R.charsP.2.2.1 with ha_def
  set Kc' : ℝ := max Kc 0 with hKc'
  have hKc0 : 0 ≤ Kc' := le_max_right _ _
  refine ⟨D * Kc' * (D : ℝ) ^ ((E : ℝ) / 3), by positivity, max (max N₁ N₂) 1,
    fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  dsimp only
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨h2A, hc, hz, hδ⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    A hA k hk hkN hhs e he
  have hEA : e.A = A := by rcases he with ⟨s, rfl⟩ | ⟨t, -, s, rfl⟩ <;> rfl
  have hg := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) μ hμ e
    (hEA ▸ hA) (by rw [mul_one]; exact h2A) hc
    (fun a => ⟨(hz a).1, (hz a).2.1, (hz a).2.2.2⟩) hδ
  have hmin : min (e.z 0).im (e.z 1).im = etaK D N k ε := by
    rw [(hz 0).2.2.1, (hz 1).2.2.1, min_self]
  rw [hmin, hEA] at hg
  have hX := LR_psi_exp D N hN1 (rk D N k) ε (Dr_rk D N k hk hkN) (LR_rk_le D N k hk hkN) a E
    hE0 hψ'
  have hM : ∀ κ : ℕ → Idx D N, ‖∫ h, R.evalH e κ h ∂μ‖ ≤
      (N : ℝ) ^ τ * ((D : ℝ) ^ ((E : ℝ) / 3) * ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2)) := by
    intro κ
    refine (hg κ).trans ?_
    rw [← mul_assoc ((D : ℝ) ^ ((E : ℝ) / 3))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
    exact mul_le_mul_of_nonneg_right hX (sq_nonneg _)
  have hcum : ∀ i j : Idx D N, ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤
      Kc' * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro i j
    have h := hKc D N 1 μ hμ i j
    have h3 : (((p + (q + 1) : ℕ) : ℝ) / 2) = 3 / 2 := by
      rw [show p + (q + 1) = 3 by omega]
      norm_num
    rw [h3] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _))
  have hb := LR_O_le (by omega) hN1 μ p q _ _ (mul_nonneg hKc0 (Real.rpow_nonneg hN0.le _))
    (by positivity) hcum _ fun i j => hM (fun l => if l = 0 then i else j)
  have hT := LR_tail D N hN1 A k (Dr_rk D N k hk hkN) ε hε.le
  have hτ1 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
  have hX0 : 0 ≤ (N : ℝ) ^ (2 * ε) * Dr_T D N A k :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (Dr_T_nonneg D N A k)
  have hc0 : 0 ≤ (D : ℝ) * Kc' * (D : ℝ) ^ ((E : ℝ) / 3) := by positivity
  calc ‖R.outer e μ p q‖ ≤ (D : ℝ) * N * (Kc' * (N : ℝ) ^ (-(3 / 2 : ℝ))) *
        ((N : ℝ) ^ τ * ((D : ℝ) ^ ((E : ℝ) / 3) * ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2))) := hb
    _ = ((D : ℝ) * Kc' * (D : ℝ) ^ ((E : ℝ) / 3)) * (N : ℝ) ^ τ *
        ((N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2)) := by ring
    _ ≤ ((D : ℝ) * Kc' * (D : ℝ) ^ ((E : ℝ) / 3)) * (N : ℝ) ^ τ *
        ((N : ℝ) ^ (2 * ε) * Dr_T D N A k) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg hc0 (Real.rpow_nonneg hN0.le _))

/-- One derivative structure `𝓡₀` of `𝓡_𝒯(p, q)`, `R = 0`, `p + q = 2`: the identity of the further
expansion of Lemma 5.5 [claim_estimate_remainder_terms] inside the cumulant sum, its leaves
(`pkg_leaf_bound`, or `Ψ′ ≥ 4`), its inner nodes (`pkg_rem2_one`, `pkg_rem2_two`,
`pkg_rem2_three` by the Type) and its error `N^{-2} ‖A‖²`. -/
private lemma LR_one (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (hR0 : T.rcount = 0) (h1 : 1 ≤ T.kk 0) (p q : ℕ)
    (hpq : p + q = 2) (R₀ : PkgExpr) (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p q) :
    LR_Bd D δA εA ε C fun _ μ e => R₀.outer e μ p q := by
  obtain ⟨T₀, hT₀⟩ := pkg_terminates ε hε (by linarith) n T hT h1 p q hpq R₀ hR₀
  have hmem0 : R₀ ∈ fIter ε 0 [R₀] := by simp [fIter]
  have hwf0 := pkg_inv_wf ε n T hT hR0 p q hpq R₀ hR₀ 0 R₀ (Or.inl hmem0)
  have hlab0 := (pkg_inv_lab ε n T hT hR0 p q hpq R₀ hR₀ 0 R₀ (Or.inl hmem0)).2.2
  obtain ⟨c₀, K, -, -, N₁, hN₁⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨m, -, N₂, hN₂⟩ := pkg_tree_sum' D hD δA (ε / 2) 1 K ε hδA (by positivity) le_rfl C T₀
    R₀ hwf0 hlab0 2 (by norm_num)
  have hL : LR_Bd D δA εA ε C fun N μ e =>
      ((fIter ε T₀ [R₀]).map fun R => R.outer e μ p q).sum := by
    refine LR_list (D := D) (δA := δA) (εA := εA) (ε := ε) (C := C) (α := PkgExpr)
      (fun R N μ e => R.outer e μ p q) _ fun R hR => ?_
    by_cases hf : R.ffocus = none
    · exact LR_of_pin (G := fun _ μ e => R.outer e μ p q) (pkg_leaf_bound D hD δA εA ε hδA
        hεA hε hε' hε'' C n T hT hR0 p q hpq R₀ hR₀ T₀ R hR hf)
    · have hs := hT₀ R hR
      unfold PkgExpr.FStopped at hs
      exact LR_of_env (LR_psi D hD δA εA ε hδA hεA hε hε' hε'' C R
        (pkg_inv_wf ε n T hT hR0 p q hpq R₀ hR₀ T₀ R (Or.inl hR)) (hs.resolve_right hf) p q hpq)
  have hI : LR_Bd D δA εA ε C fun N μ e =>
      ((fInner ε T₀ [R₀]).map fun R => ∑ p' ∈ Finset.range (m + 1),
        ∑ q' ∈ Finset.range (m + 1 - p'),
          if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0).sum := by
    refine LR_list (D := D) (δA := δA) (εA := εA) (ε := ε) (C := C) (α := PkgExpr)
      (fun R N μ e => ∑ p' ∈ Finset.range (m + 1), ∑ q' ∈ Finset.range (m + 1 - p'),
        if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0) _ fun R hR => ?_
    refine LR_fsum (D := D) (δA := δA) (εA := εA) (ε := ε) (C := C) (α := ℕ)
      (fun p' N μ e => ∑ q' ∈ Finset.range (m + 1 - p'),
        if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0) _ fun p' _ => ?_
    refine LR_fsum (D := D) (δA := δA) (εA := εA) (ε := ε) (C := C) (α := ℕ)
      (fun q' N μ e => if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0) _ fun q' _ => ?_
    by_cases h2 : 2 ≤ p' + q'
    · simp only [h2, ↓reduceIte]
      have hwf := pkg_inv_wf ε n T hT hR0 p q hpq R₀ hR₀ T₀ R (Or.inr hR)
      have h0 := pkg_ptype_pos R hwf
      have h3 := LR_ptype_le R
      obtain h | h | h : R.ptype = 1 ∨ R.ptype = 2 ∨ R.ptype = 3 := by omega
      · exact LR_of_pin (G := fun _ μ e => R.outer2 e μ p q p' q') (pkg_rem2_one D hD δA εA ε hδA
          hεA hε hε' hε'' C n T hT hR0 p q hpq R₀ hR₀ T₀ R hR h p' q'
          h2)
      · exact LR_of_pin (G := fun _ μ e => R.outer2 e μ p q p' q') (pkg_rem2_two D hD δA εA ε hδA
          hεA hε hε' hε'' C n T hT hR0 p q hpq R₀ hR₀ T₀ R hR h p' q'
          h2)
      · exact LR_of_pin (G := fun _ μ e => R.outer2 e μ p q p' q') (pkg_rem2_three D hD δA εA ε hδA
          hεA hε hε' hε'' C n T hT hR0 p q hpq R₀ hR₀ T₀ R hR h p' q'
          h2)
    · simp only [h2, ↓reduceIte]
      exact LR_zero
  have hE : LR_Bd D δA εA ε C fun N μ e => R₀.outer e μ p q -
      ((fIter ε T₀ [R₀]).map fun R => R.outer e μ p q).sum -
      ((fInner ε T₀ [R₀]).map fun R => ∑ p' ∈ Finset.range (m + 1),
        ∑ q' ∈ Finset.range (m + 1 - p'),
          if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0).sum := by
    refine LR_of_env fun τ hτ => ?_
    obtain ⟨Kc, hKc⟩ := llClass_ccum_le C p (q + 1)
    set Kc' : ℝ := max Kc 0 with hKc'
    have hKc0 : 0 ≤ Kc' := le_max_right _ _
    refine ⟨D * Kc', by positivity, max (max N₁ N₂) 1,
      fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
    dsimp only
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    obtain ⟨h2A, hc, hz, hδ⟩ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
      A hA k hk hkN hhs e he
    have hEA : e.A = A := by rcases he with ⟨s, rfl⟩ | ⟨t, -, s, rfl⟩ <;> rfl
    have ht := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) μ hμ e
      (hEA ▸ hA) (by rw [mul_one]; exact h2A) hc (fun a => ⟨(hz a).1, (hz a).2.1⟩) hδ
    rw [hEA] at ht
    have hcum : ∀ i j : Idx D N, ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤
        Kc' * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro i j
      have h := hKc D N 1 μ hμ i j
      have h3 : (((p + (q + 1) : ℕ) : ℝ) / 2) = 3 / 2 := by
        rw [show p + (q + 1) = 3 by omega]
        norm_num
      rw [h3] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _))
    rw [LR_err_eq]
    have hb := LR_O_le (by omega) hN1 μ p q _ _ (mul_nonneg hKc0 (Real.rpow_nonneg hN0.le _))
      (by positivity) hcum _ fun i j => ht (fun l => if l = 0 then i else j)
    have hT := LR_tail D N hN1 A k (Dr_rk D N k hk hkN) ε hε.le
    have hτ1 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ.le
    have hX0 : 0 ≤ (N : ℝ) ^ (2 * ε) * Dr_T D N A k :=
      mul_nonneg (Real.rpow_nonneg hN0.le _) (Dr_T_nonneg D N A k)
    have hc0 : 0 ≤ (D : ℝ) * Kc' := by positivity
    calc _ ≤ (D : ℝ) * N * (Kc' * (N : ℝ) ^ (-(3 / 2 : ℝ))) *
          ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2) := hb
      _ = ((D : ℝ) * Kc') * ((N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) *
          ((N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2)) := by ring
      _ ≤ ((D : ℝ) * Kc') * (1 * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hT hc0
      _ ≤ ((D : ℝ) * Kc') * ((N : ℝ) ^ τ * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hτ1 hX0) hc0
      _ = (D : ℝ) * Kc' * (N : ℝ) ^ τ * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k) := by ring
  have hsum := LR_add (LR_add hL hI) hE
  have heq : (fun (N : ℕ) (μ : Measure (Idx D N → Idx D N → ℂ)) (e : LoopEnv D N) =>
      R₀.outer e μ p q) = fun N μ e =>
      ((fIter ε T₀ [R₀]).map fun R => R.outer e μ p q).sum +
      ((fInner ε T₀ [R₀]).map fun R => ∑ p' ∈ Finset.range (m + 1),
        ∑ q' ∈ Finset.range (m + 1 - p'),
          if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0).sum +
      (R₀.outer e μ p q - ((fIter ε T₀ [R₀]).map fun R => R.outer e μ p q).sum -
      ((fInner ε T₀ [R₀]).map fun R => ∑ p' ∈ Finset.range (m + 1),
        ∑ q' ∈ Finset.range (m + 1 - p'),
          if 2 ≤ p' + q' then R.outer2 e μ p q p' q' else 0).sum) := by
    funext N μ e
    ring
  rw [heq]
  exact hsum

/-- Lemma 5.5 [claim_estimate_remainder_terms] for the signed sum over the four starting loops of
(5.29) [expansion_of_im]: for every expression expanded in the expansion of §5.3 and every
`p + q ≥ 2`, the signed sum of `𝓡_𝒯(p, q)` is at most `N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`,
at the slots of Lemma 5.2 [lemma_localized_eigenvector_local_law] and, uniformly in
`t ∈ [0, 1]`, of Lemma 5.4 [lemma_localized_eigenvalue_local_law]. -/
theorem loop_rem_bound (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (p q : ℕ) (hpq : 2 ≤ p + q) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            T.remPQ (evecEnv D N A k ε s) μ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              T.remPQ (evalEnv D N A k ε t s) μ p q‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  by_cases hd : 3 ≤ p + q ∨ 1 ≤ T.rcount
  · exact loop_rem_direct D hD δA εA ε hδA hεA hε hε' hε'' C n T hT p q hpq hd
  push Not at hd
  obtain ⟨hd1, hd2⟩ := hd
  have hpq2 : p + q = 2 := by omega
  obtain ⟨-, -, hk0, Rr, C₁, C₂, P₁, P₂, hch⟩ := loop_reach ε n T (Or.inr hT)
  have hR0 : T.rcount = 0 := by
    have : T.rcount = Rr := by
      simp only [LoopExpr.rcount, hch]
      ring
    omega
  have h1 : 1 ≤ T.kk 0 := by
    by_contra h
    have := hk0 (by omega)
    omega
  have hsum : LR_Bd D δA εA ε C fun N μ e =>
      ((T.pkgStart.dwirt 0 1 p q).map fun R₀ => R₀.outer e μ p q).sum :=
    LR_list (D := D) (δA := δA) (εA := εA) (ε := ε) (C := C) (α := PkgExpr)
      (fun R₀ N μ e => R₀.outer e μ p q) _ fun R₀ hR₀ =>
      LR_one D hD δA εA ε hδA hεA hε hε' hε'' C n T hT hR0 h1 p q hpq2 R₀ hR₀
  obtain ⟨c₀, K, -, -, N₁, hN₁⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  refine LR_to_pin (G := fun N μ e => T.remPQ e μ p q) fun τ hτ => ?_
  obtain ⟨K', hK', N₂, hN₂⟩ := hsum τ hτ
  refine ⟨K', hK', max N₁ N₂, fun N hN μ hμ A hA k hk hkN hhs E hE => ?_⟩
  have hexp : ∀ s, T.remPQ (E s) μ p q =
      ((T.pkgStart.dwirt 0 1 p q).map fun R₀ => R₀.outer (E s) μ p q).sum := by
    intro s
    have hs : (∃ s', E s = evecEnv D N A k ε s') ∨
        ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s', E s = evalEnv D N A k ε t s' := by
      rcases hE with rfl | ⟨t, ht, rfl⟩
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr ⟨t, ht, s, rfl⟩
    obtain ⟨-, -, hz, -⟩ := hN₁ N (le_trans (le_max_left _ _) hN) A hA k hk hkN hhs (E s) hs
    exact loop_rem_expand D N C T (E s) (fun a => ((hz a).2.1).ne') μ hμ p q
  simp only [hexp]
  exact hN₂ N (le_trans (le_max_right _ _) hN) μ hμ A hA k hk hkN hhs E hE

end RBMTransitionEdge

end
