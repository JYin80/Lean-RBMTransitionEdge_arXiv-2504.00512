module

public import Mathlib

@[expose] public section

/-!
# Localization–delocalization transition for a random block matrix model

Statements of Theorems 2.1 and 2.5 of J. Fan, B. Stone, F. Yang and J. Yin,
*Localization-delocalization transition for a random block matrix model*, arXiv:2504.00512, with the
definitions they use. This file imports Mathlib and nothing else; the proofs are in the library
`RBMTransitionEdge`, and `Solution.lean` connects each statement to the theorem of the library that proves it.

The model is `H_Λ = H + Λ` of (1.2)–(1.4), complex Hermitian case: `H` has `D` independent `N × N`
Wigner blocks on the diagonal, with entry laws under Assumption 1 [main_assm] (all moments bounded
by given constants), and `Λ` places a deterministic `A` and `A*` on the cyclic off-diagonal blocks
(for `D = 2`, `Λ = [[0, A], [A*, 0]]`). The two statements are the closed propositions
`RBMTransitionEdge.MixStatement` (Theorem 2.1 [mix], under `‖A‖ ≤ N^{-δ_A}` and (2.4) [eq:condA1]) and
`RBMTransitionEdge.LocalizedEvalStatement` (Theorem 2.5 [theorem_localized_eigenvalue], under (2.8)
[eq:condA2]). The constants are chosen before `N`, and the bounds hold for every `N ≥ N₀`, every
entry law with the given moment constants, every admissible `A` and every `k`; there are no other
hypotheses. `docs/PAPER-VS-LEAN.md` lists every difference from the printed statements; in
particular (2.10) has a strict inequality and the correlation comparison of Theorem 2.5 is stated
for the correlation functions `ρ^(n)`. Theorems 2.2 [MixEV] and 2.4
[theorem_localized_eigenvector_localization], which the library proves from one external input each,
are not stated here.
-/

section
open MeasureTheory ProbabilityTheory Matrix
noncomputable section
open Classical
namespace RBMTransitionEdge
/-- The index set of (1.3) [matrix_H]: a block index `a` and a position `i` within the block. -/
abbrev Idx (D N : ℕ) := Fin D × Fin N

/-- Assumption 1 [main_assm] after scaling by `√N`: `νd` is the law of `√N (H_a)_{ii}` (real)
and `νo` the law of `√N (H_a)_{ij}`, `i < j` (complex), with (2.1) [eq:meanvar], (2.2)
[eq:meanvar2] and the moment bounds (2.3) [eq:highmoment] with constants `C p`. -/
structure EntryLaws (C : ℕ → ℝ) where
  /-- The law of a scaled diagonal entry. -/
  νd : ProbabilityMeasure ℝ
  /-- The law of a scaled entry above the diagonal. -/
  νo : ProbabilityMeasure ℂ
  /-- Every absolute moment of `νd` is finite. -/
  intd : ∀ p : ℕ, Integrable (fun x : ℝ => |x| ^ p) (νd : Measure ℝ)
  /-- Every absolute moment of `νo` is finite. -/
  into : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) (νo : Measure ℂ)
  /-- (2.1) [eq:meanvar]: mean zero on the diagonal. -/
  meand : ∫ x, x ∂(νd : Measure ℝ) = 0
  /-- (2.1) [eq:meanvar]: variance one on the diagonal. -/
  vard : ∫ x, x ^ 2 ∂(νd : Measure ℝ) = 1
  /-- (2.1) [eq:meanvar]: mean zero off the diagonal. -/
  meano : ∫ z, z ∂(νo : Measure ℂ) = 0
  /-- (2.1) [eq:meanvar]: `E|h|² = 1` off the diagonal. -/
  varo : ∫ z, ‖z‖ ^ 2 ∂(νo : Measure ℂ) = 1
  /-- (2.2) [eq:meanvar2]: `E h² = 0` off the diagonal. -/
  pseudo : ∫ z, z ^ 2 ∂(νo : Measure ℂ) = 0
  /-- (2.3) [eq:highmoment]: `E|h_{11}|^p + E|h_{12}|^p ≤ C p`. -/
  moments : ∀ p : ℕ,
    (∫ x, |x| ^ p ∂(νd : Measure ℝ)) + (∫ z, ‖z‖ ^ p ∂(νo : Measure ℂ)) ≤ C p

/-- Coordinates of one Wigner block of size `n`: the diagonal entries, and an array whose entries
`i < j` are the entries above the diagonal (the others are not used). -/
abbrev Coords (n : ℕ) := (Fin n → ℝ) × (Fin n → Fin n → ℂ)

/-- The product law of the coordinates of one block. -/
def coordLaw (n : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) : Measure (Coords n) :=
  (Measure.pi fun _ : Fin n => (L.νd : Measure ℝ)).prod
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (L.νo : Measure ℂ))

/-- The law of the `D` independent blocks `H_1, …, H_D` of (1.3) [matrix_H]. -/
def blockLaw (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) : Measure (Fin D → Coords N) :=
  Measure.pi fun _ : Fin D => coordLaw N L

/-- The `n × n` Wigner matrix `n^{-1/2} (x_{ij})` with Hermitian symmetry. -/
def wig (n : ℕ) (w : Coords n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (if i = j then ((w.1 i : ℝ) : ℂ) else if i < j then w.2 i j else star (w.2 j i))

/-- The block-diagonal matrix `H` of (1.3) [matrix_H]. -/
def blockH (D N : ℕ) (w : Fin D → Coords N) : Matrix (Idx D N) (Idx D N) ℂ :=
  fun p q => if p.1 = q.1 then wig N (w p.1) p.2 q.2 else 0

/-- The neighbour relation of the cycle of blocks in (1.3) [matrix_H]: `b = a + 1`, and the wrap
`D - 1 → 0` when `D ≥ 3`; for `D = 2` the single edge `0 → 1`, so that `Λ = [[0, A], [A*, 0]]` as
in (2.15) [eq:MD=2]. -/
def fwd (D : ℕ) (a b : Fin D) : Prop :=
  (b : ℕ) = (a : ℕ) + 1 ∨ (3 ≤ D ∧ (a : ℕ) + 1 = D ∧ (b : ℕ) = 0)

/-- The interaction `Λ` of (1.3) [matrix_H]: block `(a, a+1)` is `A`, block `(a+1, a)` is `A*`. -/
def lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  fun p q => (if fwd D p.1 q.1 then A p.2 q.2 else 0) +
    (if fwd D q.1 p.1 then star (A q.2 p.2) else 0)

/-- The model `H_Λ = H + Λ` of (1.2) [eq:def_model]. -/
def HLam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin D → Coords N) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  blockH D N w + lam D N A

/-- The eigenvalues in decreasing order (zero for a non-Hermitian matrix). -/
def eigs {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    Fin (Fintype.card ι) → ℝ :=
  if h : M.IsHermitian then h.eigenvalues₀ else 0

/-- `λ_k`, `k ∈ ⟦1, card ι⟧`: the `k`-th largest eigenvalue. -/
def eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (k : ℕ) : ℝ :=
  if h : k - 1 < Fintype.card ι then eigs M ⟨k - 1, h⟩ else 0

/-- `u` is a unit eigenvector of `M` for the eigenvalue `μ`. -/
def IsUnitEigvec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (μ : ℝ) (u : ι → ℂ) : Prop :=
  M *ᵥ u = (μ : ℂ) • u ∧ ∑ i, ‖u i‖ ^ 2 = 1

/-- `u^* E_a u = ‖E_a u‖²`, the mass of `u` on the block `I_a` (Theorem 2.1 [mix]). -/
def blockMass {D N : ℕ} (u : Idx D N → ℂ) (a : Fin D) : ℝ :=
  ∑ j : Fin N, ‖u (a, j)‖ ^ 2

/-- The operator norm `‖A‖`. -/
def opNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

/-- The Hilbert–Schmidt norm `‖A‖_HS`. -/
def hsNorm {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- `𝔯(k) = k ∧ (DN + 1 - k)` of (1.4) [eq:rk]. -/
def rk (D N k : ℕ) : ℝ := (min k (D * N + 1 - k) : ℕ)

/-- The normalized trace `⟨B⟩`. -/
def ntr {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) : ℂ := ((Fintype.card ι : ℂ))⁻¹ * B.trace

/-- The `n`-point correlation pairing of Theorem 2.5 [theorem_localized_eigenvalue] in the
normalization of the correlation function `ρ^(n) = Mc!/(Mc - n)! · p^(n)`: the sum over distinct
indices `Σ O(s(λ_{i_1} - γ), …, s(λ_{i_n} - γ))` of the eigenvalues `ev 1, …, ev Mc`. Its
expectation equals `s^{-n} ∫ O(α) ρ^(n)(γ + α/s) dα` whenever the joint eigenvalue density exists;
no density is needed here. -/
def corrPairing (Mc n : ℕ) (s γ : ℝ) (O : (Fin n → ℝ) → ℝ) (ev : ℕ → ℝ) : ℝ :=
  ∑ f : Fin n ↪ Fin Mc, O fun j => s * (ev ((f j : ℕ) + 1) - γ)
end RBMTransitionEdge
end
end
section
open MeasureTheory Matrix Filter Topology
noncomputable section
open Classical
namespace RBMTransitionEdge
/-- Definition 2.7 [defn_Mm], (2.16) [self_m]: the solution `m(z)` with `Im m(z) > 0`, chosen
for each `z`; it is `0` when there is no such solution. -/
def mSol {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  if h : ∃ w : ℂ, 0 < w.im ∧ w = ntr (Λ - (z + w) • (1 : Matrix ι ι ℂ))⁻¹ then h.choose else 0

/-- `ρ_N(x) = π⁻¹ lim_{η↓0} Im m(x + iη)` of (2.19) [eq:density_rhoN]. -/
def rho {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (x : ℝ) : ℝ :=
  (limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im) / Real.pi

/-- The semicircle density (2.18) [eq:semidensity]. -/
def rhoSc (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (-2 : ℝ) 2 then Real.sqrt (4 - x ^ 2) / (2 * Real.pi) else 0

/-- The quantile `γ_k` of (2.20) [eq:gammak] of a density `ρ` with `Mc` particles. -/
def quant (ρ : ℝ → ℝ) (Mc k : ℕ) : ℝ :=
  sSup {x : ℝ | ((k : ℝ) - 1 / 2) / Mc ≤ ∫ E in Set.Ioi x, ρ E}
end RBMTransitionEdge
end
end
section
open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff
noncomputable section
namespace RBMTransitionEdge
/-- The eigenvalue shift `X = (λ_k - γ_k) - (λ_k(H) - γ_k^{sc})` of Theorem 2.5
[theorem_localized_eigenvalue]. -/
def shiftX (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (w : Fin D → Coords N) : ℝ :=
  (eigK (HLam D N A w) k - quant (rho (lam D N A)) (D * N) k) -
    (eigK (blockH D N w) k - quant rhoSc (D * N) k)

/-- Theorem 2.1 [mix]: under (2.4) [eq:condA1], (2.5) [eq:main_evector1] holds for every unit
eigenvector of `λ_k`. -/
def MixStatement : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
    (N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ hsNorm A →
    blockLaw D N L {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
        ∃ a : Fin D, (N : ℝ) ^ (-c) ≤ |blockMass u a - (D : ℝ)⁻¹|} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-c))

/-- Theorem 2.5 [theorem_localized_eigenvalue]: under (2.8) [eq:condA2], (2.10)
[eq:local_eigenvalue_perturb] with the strict inequality in the event, (2.11) [eq:main_perurb],
and the comparison of the `n`-point correlation functions `ρ^(n)` of `H_Λ` at `γ_k` and of `H` at
`γ_k^{sc}` on the scale `s = (DN)^{2/3} 𝔯(k)^{1/3}`. -/
def LocalizedEvalStatement : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    (∀ ε ε₀ : ℝ, 0 < ε → 0 < ε₀ → ε₀ < 2 * ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-1 + ε) * hsNorm A < |shiftX D N A k w|} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ε₀))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N k ^ (-(1 / 3 : ℝ)) ≤
          |shiftX D N A k w|} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c))) ∧
    (∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      |(∫ w, corrPairing (D * N) n (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ))
            (quant (rho (lam D N A)) (D * N) k) O (eigK (HLam D N A w)) ∂(blockLaw D N L)) -
        (∫ w, corrPairing (D * N) n (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ))
            (quant rhoSc (D * N) k) O (eigK (blockH D N w)) ∂(blockLaw D N L))| ≤
        (N : ℝ) ^ (-c))
end RBMTransitionEdge
end
end

/-! ## The statements -/

section
noncomputable section
namespace RBMTransitionEdge
open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff

/-- Theorem 2.1 [mix], (2.5); the statement is `RBMTransitionEdge.MixStatement`. -/
theorem theorem_2_1 : MixStatement := by
  sorry

/-- Theorem 2.5 [theorem_localized_eigenvalue]: `LocalizedEvalStatement`. -/
theorem theorem_2_5 : LocalizedEvalStatement := by
  sorry

end RBMTransitionEdge
end
