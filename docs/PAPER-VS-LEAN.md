# The paper and the Lean code

This document states what the Lean code in `RBMTransitionEdge/` proves, and how its statements relate to the results of

> J. Fan, B. Stone, F. Yang and J. Yin, *Localization-delocalization transition for a random block matrix model*, arXiv:2504.00512 (version 2).

Theorem, lemma, assumption, definition, section and equation numbers are those of the compiled arXiv version. The theorem-like environments of a section share one counter, so Theorem 2.1, Remark 2.3 and Definition 2.7 are numbered in one sequence in §2; displayed equations have their own counter. The TeX label of an item is given in brackets the first time it appears, for example Theorem 2.1 [mix], Assumption 1 [main_assm] and (2.4) [eq:condA1]. The corrected version in `paper/` keeps all theorem, equation and section numbers; it incorporates the corrections of §3 (b) and the statement changes of §3 (a) that the authors adopted.

All declarations lie in namespace RBMTransitionEdge; names are written below without this prefix. The library is `RBMTransitionEdge.lean` with the modules under `RBMTransitionEdge/`; the files `Challenge.lean`, `Solution.lean` and `comparator.json` at the root are the Palomar statement surface (§1). The Lean code blocks are copied verbatim from the source files, with the docstring; for theorems and examples the proof after := is omitted, definitions are quoted whole.

## 1. What is proved

The library proves the four main results of the paper, Theorem 2.1 [mix], Theorem 2.2 [MixEV], Theorem 2.4 [theorem_localized_eigenvector_localization] and Theorem 2.5 [theorem_localized_eigenvalue], under Assumption 1 [main_assm] in the complex Hermitian case. **Theorems 2.1 and 2.5 are proved unconditionally.** Theorem 2.2 is proved under the explicit hypothesis `LandonYauEdge` (the edge universality of Dyson Brownian motion that the paper cites in the proof of Lemma 4.1 [CVtG]), and Theorem 2.4 under the explicit hypothesis that `EI2Hyp` C holds for every C (the Wigner level repulsion (5.14) [Wegner12] that the paper cites in the proof of Theorem 2.4). These are the only two hypotheses that stand for results of other works (§5).

### Common objects

**The model.** `Idx` D N = Fin D × Fin N is the index set of (1.3) [matrix_H]: a block index and a position in the block. `EntryLaws` C encodes Assumption 1 after scaling the entries by √N: a law νd on ℝ for the diagonal entries and a law νo on ℂ for the entries above the diagonal, with mean zero, E|h|² = 1, E h² = 0 off the diagonal ((2.1) [eq:meanvar], (2.2) [eq:meanvar2]), all moments finite, and the moment bounds (2.3) [eq:highmoment] with the constants C p. `Coords` n is the coordinate space of one n × n Wigner block (the diagonal entries and an array whose entries i < j are the entries above the diagonal); `coordLaw` n L is the product law of these coordinates, and `blockLaw` D N L is the law of D independent blocks H_1, …, H_D. `wig` n w is the Hermitian matrix n^{−1/2}(x_ij) built from coordinates w, and `blockH` D N w is the block-diagonal matrix H of (1.3). `lam` D N A is the interaction Λ of (1.3), built from the neighbour relation `fwd` of the cycle of blocks, and `HLam` D N A w is H_Λ = H + Λ of (1.2) [eq:def_model]. `eigs` lists the eigenvalues of a Hermitian matrix in decreasing order, and `eigK` M k is λ_k, the k-th largest one (both are 0 outside their range or for a non-Hermitian matrix, which does not occur in the statements). `IsUnitEigvec` M μ u says that u is a unit eigenvector of M for μ, and `blockMass` u a = Σ_j |u(a, j)|² is v*E_a v of Theorem 2.1. `opNorm` and `hsNorm` are the operator and Hilbert–Schmidt norms, and `rk` D N k is 𝔯(k) = k ∧ (DN + 1 − k) of (1.4) [eq:rk].

```lean
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
```

```lean
/-- The law of the `D` independent blocks `H_1, …, H_D` of (1.3) [matrix_H]. -/
def blockLaw (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) : Measure (Fin D → Coords N) :=
  Measure.pi fun _ : Fin D => coordLaw N L
```

```lean
/-- The neighbour relation of the cycle of blocks in (1.3) [matrix_H]: `b = a + 1`, and the wrap
`D - 1 → 0` when `D ≥ 3`; for `D = 2` the single edge `0 → 1`, so that `Λ = [[0, A], [A*, 0]]` as
in (2.15) [eq:MD=2]. -/
def fwd (D : ℕ) (a b : Fin D) : Prop :=
  (b : ℕ) = (a : ℕ) + 1 ∨ (3 ≤ D ∧ (a : ℕ) + 1 = D ∧ (b : ℕ) = 0)
```

```lean
/-- The interaction `Λ` of (1.3) [matrix_H]: block `(a, a+1)` is `A`, block `(a+1, a)` is `A*`. -/
def lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  fun p q => (if fwd D p.1 q.1 then A p.2 q.2 else 0) +
    (if fwd D q.1 p.1 then star (A q.2 p.2) else 0)
```

```lean
/-- The model `H_Λ = H + Λ` of (1.2) [eq:def_model]. -/
def HLam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin D → Coords N) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  blockH D N w + lam D N A
```

```lean
/-- `λ_k`, `k ∈ ⟦1, card ι⟧`: the `k`-th largest eigenvalue. -/
def eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (k : ℕ) : ℝ :=
  if h : k - 1 < Fintype.card ι then eigs M ⟨k - 1, h⟩ else 0
```

```lean
/-- `u^* E_a u = ‖E_a u‖²`, the mass of `u` on the block `I_a` (Theorem 2.1 [mix]). -/
def blockMass {D N : ℕ} (u : Idx D N → ℂ) (a : Fin D) : ℝ :=
  ∑ j : Fin N, ‖u (a, j)‖ ^ 2
```

```lean
/-- `𝔯(k) = k ∧ (DN + 1 - k)` of (1.4) [eq:rk]. -/
def rk (D N k : ℕ) : ℝ := (min k (D * N + 1 - k) : ℕ)
```

**The deterministic objects.** `mSol` Λ z is m(z) of Definition 2.7 [defn_Mm]: a solution of (2.16) [self_m] with Im m > 0, chosen for each z (0 if there is none); that there is exactly one such solution for Im z > 0 is the theorem `mSol_existsUnique`. `MSol` Λ z is M(z) of (2.17) [def_G0]. `rho` Λ is the density ρ_N of (2.19) [eq:density_rhoN], π⁻¹ times the limit of Im m(x + iη) as η ↓ 0; `Eplus` Λ and `Eminus` Λ are the supremum and the infimum of its support, and `gammaPlus`, `gammaMinus` are γ_± of (2.6) [eq:def_gamma], defined by the two limits there. That ρ_N is a probability density whose Stieltjes transform is m, that its support is the single interval [E⁻, E⁺] and that the limits of (2.6) exist with γ_± ∈ [1/2, 2] are theorems (`rho_stieltjes`, `rho_support`, `def_gamma_limits`). `rhoSc` is the semicircle density (2.18) [eq:semidensity], and `quant` ρ Mc k is the quantile γ_k of (2.20) [eq:gammak] of a density ρ with Mc particles; γ_k is `quant` (`rho` Λ) (DN) k and γ_k^sc is `quant` `rhoSc` (DN) k.

```lean
/-- Definition 2.7 [defn_Mm], (2.16) [self_m]: the solution `m(z)` with `Im m(z) > 0`, chosen
for each `z`; it is `0` when there is no such solution. -/
def mSol {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  if h : ∃ w : ℂ, 0 < w.im ∧ w = ntr (Λ - (z + w) • (1 : Matrix ι ι ℂ))⁻¹ then h.choose else 0
```

```lean
/-- `ρ_N(x) = π⁻¹ lim_{η↓0} Im m(x + iη)` of (2.19) [eq:density_rhoN]. -/
def rho {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (x : ℝ) : ℝ :=
  (limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im) / Real.pi
```

```lean
/-- The quantile `γ_k` of (2.20) [eq:gammak] of a density `ρ` with `Mc` particles. -/
def quant (ρ : ℝ → ℝ) (Mc k : ℕ) : ℝ :=
  sSup {x : ℝ | ((k : ℝ) - 1 / 2) / Mc ≤ ∫ E in Set.Ioi x, ρ E}
```

**The comparison laws.** `gueLaw` Mc is the law of the coordinates of a GUE of size Mc read through `wig` Mc: standard real Gaussian diagonal coordinates and standard complex Gaussian coordinates (`cGauss`) above the diagonal, so that E|W_ij|² = 1/Mc. Theorem 2.2 uses Mc = DN. `corrPairing` Mc n s γ O ev is the sum, over n-tuples of distinct indices, of O(s(λ_{i_1} − γ), …, s(λ_{i_n} − γ)) for the eigenvalues ev 1, …, ev Mc; its expectation is the integral of O against the n-point correlation function ρ^(n) at the scale s (§3 (a) 4).

```lean
/-- The coordinate law of the GUE of size `Mc` used in Theorem 2.2 [MixEV]: through `wig Mc`,
`E|W_{ij}|² = 1/Mc` off the diagonal and real diagonal entries of variance `1/Mc`, the
normalization of (4.1) [defVt] and (4.3) [eq:eq_in_law_H]. -/
def gueLaw (Mc : ℕ) : Measure (Coords Mc) :=
  (Measure.pi fun _ : Fin Mc => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin Mc => Measure.pi fun _ : Fin Mc => (cGauss : Measure ℂ))
```

```lean
/-- The `n`-point correlation pairing of Theorem 2.5 [theorem_localized_eigenvalue] in the
normalization of the correlation function `ρ^(n) = Mc!/(Mc - n)! · p^(n)`: the sum over distinct
indices `Σ O(s(λ_{i_1} - γ), …, s(λ_{i_n} - γ))` of the eigenvalues `ev 1, …, ev Mc`. Its
expectation equals `s^{-n} ∫ O(α) ρ^(n)(γ + α/s) dα` whenever the joint eigenvalue density exists;
no density is needed here. -/
def corrPairing (Mc n : ℕ) (s γ : ℝ) (O : (Fin n → ℝ) → ℝ) (ev : ℕ → ℝ) : ℝ :=
  ∑ f : Fin n ↪ Fin Mc, O fun j => s * (ev ((f j : ℕ) + 1) - γ)
```

### The four main results

The statements are closed propositions in `RBMTransitionEdge/MainDefs.lean` (Theorems 2.1 and 2.5, which Palomar uses) and `RBMTransitionEdge/Main/Statements.lean` (Theorems 2.2 and 2.4). Each is in the uniform form: D ≥ 2, δ_A, ε_A > 0 and the moment constants C are fixed first; the constants c, ε₀, N₀ of the conclusion are chosen next; then the bound holds for every N ≥ N₀, every entry law L with the moment constants C (the law may depend on N), every A with ‖A‖ ≤ N^{−δ_A} satisfying the condition of the theorem, and every k ∈ ⟦1, DN⟧.

```lean
/-- The eigenvalue shift `X = (λ_k - γ_k) - (λ_k(H) - γ_k^{sc})` of Theorem 2.5
[theorem_localized_eigenvalue]. -/
def shiftX (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (w : Fin D → Coords N) : ℝ :=
  (eigK (HLam D N A w) k - quant (rho (lam D N A)) (D * N) k) -
    (eigK (blockH D N w) k - quant rhoSc (D * N) k)
```

```lean
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
```

```lean
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
```

```lean
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
```

```lean
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
```

The theorems (`RBMTransitionEdge/Flow/Mix.lean`, `RBMTransitionEdge/Edge/MixEV.lean`, `RBMTransitionEdge/Main/Main.lean`):

```lean
/-- Theorem 2.1 [mix]. -/
theorem mix : MixStatement :=
```

```lean
/-- Theorem 2.2 [MixEV], under the external input of Lemma 4.1 [CVtG]. -/
theorem mixEV (hEI : LandonYauEdge) : MixEVStatement :=
```

```lean
/-- Theorem 2.4 [theorem_localized_eigenvector_localization], with the level repulsion (5.14)
[Wegner12] as an explicit hypothesis. -/
theorem localized_evec (hEI : ∀ C : ℕ → ℝ, EI2Hyp C) : LocalizedEvecStatement :=
```

```lean
/-- Theorem 2.5 [theorem_localized_eigenvalue]. -/
theorem localized_eval : LocalizedEvalStatement :=
```

```lean
/-- The four main results: Theorem 2.1 [mix], Theorem 2.2 [MixEV] with the edge universality of
the Wigner block (Landon–Yau) as an explicit hypothesis, Theorem 2.4
[theorem_localized_eigenvector_localization] with the level repulsion (5.14) [Wegner12] as an
explicit hypothesis, and Theorem 2.5 [theorem_localized_eigenvalue]. -/
theorem main_theorems (hEI1 : LandonYauEdge) (hEI2 : ∀ C : ℕ → ℝ, EI2Hyp C) :
    MixStatement ∧ MixEVStatement ∧ LocalizedEvecStatement ∧ LocalizedEvalStatement :=
```

`mix` and `localized_eval` have no hypothesis. `mixEV` has the single hypothesis `LandonYauEdge`, `localized_evec` the single hypothesis ∀ C, `EI2Hyp` C, and `main_theorems` has exactly these two.

**Theorem 2.1 [mix]** (`MixStatement`). For every D ≥ 2, δ_A, ε_A > 0 and moment constants C there are c > 0 and N₀ such that for every N ≥ N₀, every entry law with constants C, every A with ‖A‖ ≤ N^{−δ_A} and every k ∈ ⟦1, DN⟧ with ‖A‖_HS ≥ N^{1/3+ε_A}𝔯(k)^{−1/3} ((2.4) [eq:condA1]), the probability that some unit eigenvector u of λ_k has |u*E_a u − D⁻¹| ≥ N^{−c} for some block a is at most N^{−c}. This is (2.5) [eq:main_evector1], for every choice of the eigenvector v_k at once.

**Theorem 2.2 [MixEV]** (`MixEVStatement`, under `LandonYauEdge`). For every D ≥ 2, δ_A, ε_A > 0, moment constants C, n and smooth compactly supported O on ℝ^n there are c > 0 and N₀ such that for every N ≥ N₀, every entry law with constants C and every A with ‖A‖ ≤ N^{−δ_A} and ‖A‖_HS ≥ N^{1/3+ε_A} ((2.4) at k = 1, where 𝔯(1) = 1), the expectation of O(γ₊(DN)^{2/3}(E⁺ − λ_i))_{i ≤ n} differs from that of O((DN)^{2/3}(2 − μ_i))_{i ≤ n} by at most N^{−c}, where μ_1 ≥ μ_2 ≥ … are the eigenvalues of a DN × DN GUE; and the same at the left edge, for O(γ₋(DN)^{2/3}(λ_{DN−i} − E⁻))_{0 ≤ i < n} against O((DN)^{2/3}(μ_{DN−i} + 2))_{0 ≤ i < n}.

**Theorem 2.4 [theorem_localized_eigenvector_localization]** (`LocalizedEvecStatement`, under ∀ C, `EI2Hyp` C). For every D ≥ 2, δ_A, ε_A > 0 and moment constants C: (i) for every ε ∈ (0, 2ε_A) there are ε₀ > 0 and N₀ such that for every N ≥ N₀, every entry law with constants C, every A with ‖A‖ ≤ N^{−δ_A} and every k with ‖A‖_HS ≤ N^{1/3−ε_A}𝔯(k)^{−1/3} ((2.8) [eq:condA2]), the probability that some unit eigenvector u of λ_k has ‖E_a u‖² < 1 − N^{−2/3+ε}𝔯(k)^{2/3}‖A‖²_HS for every block a is at most N^{−ε₀}; (ii) there are c > 0 and N₀ such that, under the same hypotheses, the probability that some unit eigenvector u of λ_k has ‖E_a u‖² ≤ 1 − N^{−c} for every a is at most N^{−c}. Part (ii) is (2.9) [eq:main_evector2].

**Theorem 2.5 [theorem_localized_eigenvalue]** (`LocalizedEvalStatement`). For every D ≥ 2, δ_A, ε_A > 0 and moment constants C, under (2.8) at k, with X = (λ_k − γ_k) − (λ_k(H) − γ_k^sc) (`shiftX`): (i) for every ε > 0 and ε₀ ∈ (0, 2ε) there is N₀ such that P(|X| > N^{−1+ε}‖A‖_HS) ≤ N^{−ε₀} for N ≥ N₀, uniformly in the law, A and k ((2.10) [eq:local_eigenvalue_perturb]); (ii) there are c > 0 and N₀ with P(|X| ≥ N^{−2/3−c}𝔯(k)^{−1/3}) ≤ N^{−c} ((2.11) [eq:main_perurb]); (iii) for every n and smooth compactly supported O on ℝ^n there are c > 0 and N₀ such that, with s = (DN)^{2/3}𝔯(k)^{1/3}, the expectation of the sum of O(s(λ_{i_1} − γ_k), …, s(λ_{i_n} − γ_k)) over distinct indices for H_Λ differs from the same sum for the eigenvalues of H at γ_k^sc by at most N^{−c}. Part (iii) is the comparison of the n-point correlation functions in the normalization of ρ^(n) (§3 (a) 4).

### Palomar

`Challenge.lean` imports Mathlib only. It contains the definitions of `RBMTransitionEdge/MainDefs.lean` and states `theorem_2_1` : `MixStatement` and `theorem_2_5` : `LocalizedEvalStatement` without proof. `Solution.lean` imports the library and proves `theorem_2_1` by `mix` and `theorem_2_5` by `localized_eval`. `comparator.json` names these two theorems and permits the axioms `propext`, `Quot.sound` and `Classical.choice`. Theorems 2.2 and 2.4 are not in the Palomar files, because they rest on the external hypotheses of §5.

## 2. Index of the paper's results

Every public theorem whose docstring begins with Lemma n.m, Theorem n.m, Proposition n.m, Corollary n.m or a displayed-equation number (n.m), sorted by paper number (statements before equations of the same number). The first column is the beginning of the docstring. The table is generated from the source. Several Lean statements may belong to one item: the halves and the reflection of a main result, a general form and the paper's form (§3 (c)), or variants for the different laws used in the proof. Items whose docstring begins otherwise are not in the table, among them Lemma 2.13 [lem-Ward] (in the table through (2.31) [eq_Ward0] and (2.32) [eq_Ward]), Lemma 3.6 [lemma_G_large] (through (3.20)–(3.23)), Lemma A.3 [lemma_modification_of_shift] (through (A.34) and (A.35)) and Lemma A.4 [lemma_necessary_estimates] (through (A.53)–(A.55)).

| Paper item | Lean name | File |
|---|---|---|
| Theorem 2.1 [mix] | `mix` | `RBMTransitionEdge/Flow/Mix.lean` |
| Theorem 2.2 [MixEV] | `mixEV` | `RBMTransitionEdge/Edge/MixEV.lean` |
| Theorem 2.2 [MixEV] | `mixEV_reflect` | `RBMTransitionEdge/Edge/MixEV.lean` |
| Theorem 2.2 [MixEV] | `mixEV_right` | `RBMTransitionEdge/Edge/MixEV.lean` |
| Theorem 2.4 [theorem_localized_eigenvector_localization] | `localized_evec` | `RBMTransitionEdge/Main/Main.lean` |
| Theorem 2.4 [theorem_localized_eigenvector_localization] | `localized_evec_half` | `RBMTransitionEdge/Localized/Evec.lean` |
| Theorem 2.5 [theorem_localized_eigenvalue] | `localized_eval` | `RBMTransitionEdge/Main/Main.lean` |
| Theorem 2.5 [theorem_localized_eigenvalue] | `localized_eval_half` | `RBMTransitionEdge/Localized/Eval.lean` |
| (2.6) [eq:def_gamma] | `def_gamma_limits` | `RBMTransitionEdge/Det/Edge.lean` |
| Lemma 2.9 [lem_loc] | `local_law_seq` | `RBMTransitionEdge/LocalLaw/LocalLaw.lean` |
| Lemma 2.11 [lem:complex_cumu] | `cumulant_expansion` | `RBMTransitionEdge/Prob/CumulantExpansion.lean` |
| Lemma 2.11 [lem:complex_cumu] | `expansion_hp` | `RBMTransitionEdge/LocalLaw/ExpansionHP.lean` |
| Lemma 2.11 [lem:complex_cumu] | `expansion_hp_gen` | `RBMTransitionEdge/LocalLaw/ExpansionHP.lean` |
| Lemma 2.11 [lem:complex_cumu] | `llClass_cumulant_expansion` | `RBMTransitionEdge/LocalLaw/CumulantClass.lean` |
| Lemma 2.11 [lem:complex_cumu] | `llClass_expansion_sym` | `RBMTransitionEdge/LocalLaw/ResSmooth.lean` |
| (2.13) [def_M] | `def_M_scalar` | `RBMTransitionEdge/Det/Block.lean` |
| (2.15) [eq:MD=2] | `eq_MD2` | `RBMTransitionEdge/Det/Block.lean` |
| (2.17) [def_G0] | `MExt_far` | `RBMTransitionEdge/LocalLaw/FarDet.lean` |
| (2.21) [eq:kappa_gamma_k] | `kappa_gamma_k` | `RBMTransitionEdge/Det/Density.lean` |
| (2.22) [eq:aniso_local] | `aniso_local` | `RBMTransitionEdge/LocalLaw/LocalLaw.lean` |
| (2.23) [eq:aver_local] | `aver_local` | `RBMTransitionEdge/LocalLaw/LocalLaw.lean` |
| (2.23) [eq:aver_local] | `fb_weight` | `RBMTransitionEdge/Localized/Expansion/FSlots.lean` |
| (2.24) [eq:rigidity] | `rigidity` | `RBMTransitionEdge/LocalLaw/Rigidity.lean` |
| (2.25) [eq:G-M] | `hgUnder_identity` | `RBMTransitionEdge/LocalLaw/Dyson.lean` |
| (2.25) [eq:G-M] | `res_sub_dyson` | `RBMTransitionEdge/Tools/ResolventIdentities.lean` |
| (2.27) [eq:bdd_cumu] | `ccum_entry_le` | `RBMTransitionEdge/Prob/Cumulant.lean` |
| (2.27) [eq:bdd_cumu] | `llClass_ccum_le` | `RBMTransitionEdge/LocalLaw/CumulantClass.lean` |
| (2.30) [eq:HGline] | `integral_blockH_mul_blockH` | `RBMTransitionEdge/Prob/Underline.lean` |
| (2.31) [eq_Ward0] | `ward_sum` | `RBMTransitionEdge/Tools/ResolventIdentities.lean` |
| (2.32) [eq_Ward] | `ward_diag` | `RBMTransitionEdge/Tools/ResolventIdentities.lean` |
| Lemma 3.3 [key_lemma_delocalized_eigenvector] | `key_lemma_theta` | `RBMTransitionEdge/Flow/KeyLemma.lean` |
| (3.4) [eq:extend:main_evector1] | `evec_window` | `RBMTransitionEdge/Flow/Mix.lean` |
| Lemma 3.5 [lem_prop_flow] | `charFlow_M` | `RBMTransitionEdge/Flow/CharFlow.lean` |
| Lemma 3.7 [lemma_G_large_2] | `lemma_G_large_2_theta` | `RBMTransitionEdge/Flow/LargeEtaExp.lean` |
| Lemma 3.8 [lem_flow_1] | `flowL2_grid` | `RBMTransitionEdge/Flow/LemFlow1.lean` |
| Lemma 3.8 [lem_flow_1] | `flowL2_grid_paper` | `RBMTransitionEdge/Flow/LemFlowExp.lean` |
| Lemma 3.9 [lem_flow_2] | `flowL3_grid` | `RBMTransitionEdge/Flow/LemFlow2.lean` |
| Lemma 3.9 [lem_flow_2] | `flowL3_grid_paper` | `RBMTransitionEdge/Flow/LemFlowExp.lean` |
| Lemma 3.10 [lem_flow_1.5] | `flowG1_exp` | `RBMTransitionEdge/Flow/LemFlowExp.lean` |
| Lemma 3.10 [lem_flow_1.5] | `flowG1_exp_paper` | `RBMTransitionEdge/Flow/LemFlowExp.lean` |
| (3.10) [eq:deterflow] | `charFlow_deriv` | `RBMTransitionEdge/Flow/CharFlow.lean` |
| Lemma 3.11 [lem_flow_3] | `flowL2_exp` | `RBMTransitionEdge/Flow/LemFlow3.lean` |
| Lemma 3.11 [lem_flow_3] | `flowL2_exp_paper` | `RBMTransitionEdge/Flow/LemFlow3.lean` |
| Lemma 3.12 [main_lemma_G] | `main_lemma_G_theta` | `RBMTransitionEdge/Flow/MainG.lean` |
| Lemma 3.13 [main_lemma_com] | `main_lemma_com_theta` | `RBMTransitionEdge/Flow/Comparison.lean` |
| (3.13) [eq:Gauss_div] | `gridState_law` | `RBMTransitionEdge/Prob/Grid.lean` |
| Lemma 3.14 [lem:fourthcumu1] | `lem_fourthcumu1_theta` | `RBMTransitionEdge/Flow/FourthCumulant.lean` |
| (3.14) [t_eta] | `charFlow_teta` | `RBMTransitionEdge/Flow/CharFlow.lean` |
| (3.14) [t_eta] | `flowTc_flow` | `RBMTransitionEdge/Flow/TOp.lean` |
| Lemma 3.15 [lem:fourthcumu2] | `lem_fourthcumu2_theta'` | `RBMTransitionEdge/Flow/FourthCumulant.lean` |
| (3.18) [eq:whMK] | `Mhat_flow` | `RBMTransitionEdge/Flow/CharFlow.lean` |
| (3.18) [eq:whMK] | `kTheta_riccati` | `RBMTransitionEdge/Flow/KTheta.lean` |
| (3.19) [eq:whMK3] | `kTheta3_riccati` | `RBMTransitionEdge/Flow/KTheta.lean` |
| (3.20) [largG_Ent] | `lemma_G_large_two` | `RBMTransitionEdge/Flow/LargeEta.lean` |
| (3.21) [largG_3G_1] | `lemma_G_large_three` | `RBMTransitionEdge/Flow/LargeEta.lean` |
| (3.23) [largG_Ent_BB] | `lemma_G_large_BB` | `RBMTransitionEdge/Flow/LargeEta.lean` |
| (3.39) [eq:aftertrace] | `resPair_aftertrace` | `RBMTransitionEdge/Flow/LargeEtaId.lean` |
| (3.48) | `gen_loop1` | `RBMTransitionEdge/Flow/Generator.lean` |
| (3.48) | `gen_loop2` | `RBMTransitionEdge/Flow/Generator.lean` |
| (3.48) | `gen_loop3` | `RBMTransitionEdge/Flow/Generator.lean` |
| Lemma 4.1 [CVtG] | `CVtG` | `RBMTransitionEdge/Edge/CVtG.lean` |
| Lemma 4.2 [CVtV] | `CVtV` | `RBMTransitionEdge/Edge/Comparison.lean` |
| Lemma 4.2 [CVtV] | `cvtv_of_rescomY` | `RBMTransitionEdge/Edge/Sandwich.lean` |
| Lemma 4.3 [rescomY] | `rescomY` | `RBMTransitionEdge/Edge/Comparison.lean` |
| (4.3) [eq:eq_in_law_H] | `ouMatLaw_eq_map` | `RBMTransitionEdge/Edge/Defs.lean` |
| (4.3) [eq:eq_in_law_H] | `ouMatLaw_integral_ouPoint` | `RBMTransitionEdge/Edge/CountFlow.lean` |
| Lemma 4.4 [lem:samefort] | `samefort_local` | `RBMTransitionEdge/LocalLaw/Wigner.lean` |
| (4.8) [rough_estimate_A_t] | `edgeCount_rough` | `RBMTransitionEdge/Edge/CountBounds.lean` |
| (4.9) [eq:prodnGt] | `edgeDeriv_sub_F2_le` | `RBMTransitionEdge/Edge/CountExpand.lean` |
| (4.10) [partial_xy_F_A_t] | `edgeCount_hasDerivAt` | `RBMTransitionEdge/Edge/CountCalc.lean` |
| (4.12) [single_resolvent_local_law_bound] | `edgeRes_entry_le` | `RBMTransitionEdge/Edge/CountBounds.lean` |
| (4.16) [eq:roughXY] | `edgeXterm_rough_le` | `RBMTransitionEdge/Edge/CountBounds.lean` |
| (4.17) [GEaD1] | `edgeTerm_eq_sum` | `RBMTransitionEdge/Edge/SpecSum.lean` |
| (4.19) [GEaD3] | `edgeSpec_le` | `RBMTransitionEdge/Edge/SpecSum.lean` |
| (4.21) [eq:F2] | `edgeF2_expect_le` | `RBMTransitionEdge/Edge/Comparison.lean` |
| Lemma 5.1 [lem_regular_estimate_localized_eigenvector] | `regular_estimate_localized_eigenvector` | `RBMTransitionEdge/Det/Regular.lean` |
| Lemma 5.2 [lemma_localized_eigenvector_local_law] | `localized_eigenvector_local_law` | `RBMTransitionEdge/Localized/LocalLaw.lean` |
| Lemma 5.3 [lem_regular_estimate_localized_eigenvalue] | `regular_estimate_localized_eigenvalue` | `RBMTransitionEdge/Det/Regular.lean` |
| Lemma 5.4 [lemma_localized_eigenvalue_local_law] | `localized_eigenvalue_local_law` | `RBMTransitionEdge/Localized/LocalLaw.lean` |
| Lemma 5.5 [claim_estimate_remainder_terms] | `loop_rem_bound` | `RBMTransitionEdge/Localized/Expansion/LoopRem.lean` |
| (5.5) [regular_estimate_localized_eigenvector] | `loop_env_gain` | `RBMTransitionEdge/Localized/Expansion/Reach.lean` |
| (5.11) [eq:probab12] | `blocks_repulsion` | `RBMTransitionEdge/Localized/Repulsion.lean` |
| (5.12) [rigidity12] | `rigidity12` | `RBMTransitionEdge/LocalLaw/Wigner.lean` |
| (5.37) [number_of_G_type_1] | `loop_free_two` | `RBMTransitionEdge/Localized/Expansion/Counts.lean` |
| (5.37) [number_of_G_type_1] | `pkg_ffree_two` | `RBMTransitionEdge/Localized/Expansion/PkgCounts.lean` |
| (5.48) [eq:Tsmallthansize] | `loop_generic_bound` | `RBMTransitionEdge/Localized/Expansion/Bound.lean` |
| (5.90) [eq:addoneLambda] | `pkg_add_lambda` | `RBMTransitionEdge/Localized/Expansion/AddLambda.lean` |
| (5.90) [eq:addoneLambda] | `pkg_add_lambda_slot` | `RBMTransitionEdge/Localized/Expansion/FSlots.lean` |
| Lemma A.1 [lemma_usual_properties_of_m_and_mu] | `Mhat_translation` | `RBMTransitionEdge/Det/Block.lean` |
| (A.1) [square_root_density] | `square_root_density` | `RBMTransitionEdge/Det/Edge.lean` |
| (A.2) [edge_close_to_edge_sc] | `edge_close_to_edge_sc` | `RBMTransitionEdge/Det/Edge.lean` |
| (A.3) [equation_z_im_m] | `equation_z_im_m` | `RBMTransitionEdge/Det/Core.lean` |
| (A.3) [equation_z_im_m] | `pkg_pair_norm` | `RBMTransitionEdge/Localized/Expansion/Pairing.lean` |
| (A.4) [equation_E_in_spectrum] | `equation_E_in_spectrum` | `RBMTransitionEdge/Det/Density.lean` |
| (A.5) [eq:msc] | `eq_msc` | `RBMTransitionEdge/Det/Taylor.lean` |
| (A.6) [estimate_replace_M_by_m] | `estimate_replace_M_by_m` | `RBMTransitionEdge/Det/Taylor.lean` |
| (A.7) [add_one_more_Lambda] | `add_one_more_Lambda` | `RBMTransitionEdge/Det/Taylor.lean` |
| (A.7) [add_one_more_Lambda] | `pkg_lam0_bound` | `RBMTransitionEdge/Localized/Expansion/DetLoop.lean` |
| (A.8) [1-M] | `one_minus_Mhat_conj` | `RBMTransitionEdge/Det/MhatSpec.lean` |
| (A.9) [1-M-2] | `one_minus_Mhat_same` | `RBMTransitionEdge/Det/MhatSpec.lean` |
| (A.11) [flat_M] | `flat_KTheta` | `RBMTransitionEdge/Flow/KTheta.lean` |
| (A.11) [flat_M] | `flat_M` | `RBMTransitionEdge/Det/MhatSpec.lean` |
| (A.12) [de_ir_0] | `de_ir_0` | `RBMTransitionEdge/Det/Taylor.lean` |
| (A.17) [eq:otherM2] | `otherM2` | `RBMTransitionEdge/Det/MhatSpec.lean` |
| (A.25) [eq_lambdak] | `Mhat_eigvec` | `RBMTransitionEdge/Det/Block.lean` |
| (A.34) [modification_shift_eigenvector] | `modification_shift_eigenvector` | `RBMTransitionEdge/Det/Shift.lean` |
| (A.35) [modification_shift_eigenvalue] | `modification_shift_eigenvalue` | `RBMTransitionEdge/Det/Shift.lean` |
| (A.43) [derivative_m_t_z_with_t_and_z] | `derivative_m_t_z` | `RBMTransitionEdge/Det/Core.lean` |
| (A.53) [entprodG] | `entprodG` | `RBMTransitionEdge/LocalLaw/MultiRes.lean` |
| (A.53) [entprodG] | `entprodG_local` | `RBMTransitionEdge/LocalLaw/MultiResLocal.lean` |
| (A.53) [entprodG] | `entprodG_unif` | `RBMTransitionEdge/Flow/LargeEtaId.lean` |
| (A.53) [entprodG] | `fb_word` | `RBMTransitionEdge/Localized/Expansion/FactorBound.lean` |
| (A.54) [one_loop_estimate] | `fb_lam_loop` | `RBMTransitionEdge/Localized/Expansion/FactorBound.lean` |
| (A.54) [one_loop_estimate] | `one_loop_estimate` | `RBMTransitionEdge/LocalLaw/MultiRes.lean` |
| (A.54) [one_loop_estimate] | `one_loop_local` | `RBMTransitionEdge/LocalLaw/MultiResLocal.lean` |
| (A.55) [two_loop_estimate] | `fb_lam_two` | `RBMTransitionEdge/Localized/Expansion/FactorBound.lean` |
| (A.55) [two_loop_estimate] | `two_loop_estimate` | `RBMTransitionEdge/LocalLaw/MultiRes.lean` |
| (A.55) [two_loop_estimate] | `two_loop_local` | `RBMTransitionEdge/LocalLaw/MultiResLocal.lean` |

## 3. Differences from the printed statements

### (a) Model and endpoints

1. **The interaction for D = 2.** Paper: Λ of (1.3) [matrix_H] with periodic boundary conditions, so that blocks 1 and D are neighbours. For D = 2 this reading puts both A and A* into block (1, 2), Λ = [[0, A + A*], [A + A*, 0]]; at A = iλI_N with λ = N^{−1/10} this gives Λ = 0 while (2.4) holds at k = 1, and then H_Λ = H is block diagonal and Theorem 2.1 fails. Lean: `fwd` has the wrap D − 1 → 0 only for D ≥ 3, so for D = 2 one has Λ = [[0, A], [A*, 0]], the form used in (2.15) [eq:MD=2] and in the proof of Theorem 2.4. For D ≥ 3, `lam` is (1.3) entry by entry.
2. **Strict inequality in the first bound of Theorem 2.4.** Paper: the event max_a ‖E_a v_k‖² ≤ 1 − N^{−2/3+ε}𝔯(k)^{2/3}‖A‖²_HS. With ≤, A = 0 satisfies all hypotheses, the threshold is 1 and the event is certain. Lean: strict <. (2.9) is as printed.
3. **Strict inequality in (2.10) [eq:local_eigenvalue_perturb].** Paper: P(|X| ≥ N^{−1+ε}‖A‖_HS). With ≥, A = 0 gives the threshold 0 and probability 1. Lean: strict >. (2.11) is as printed.
4. **The correlation comparison of Theorem 2.5 in the ρ^(n) normalization.** Paper: the integrals of O(α) against p^(n)(γ + α/s), s = (DN)^{2/3}𝔯(k)^{1/3}, where p^(n) is the marginal of the symmetrized joint eigenvalue density (each p^(n) has integral 1). Lean: the expectation of the sum of O(s(λ_{i_1} − γ), …) over distinct n-tuples (`corrPairing`), which equals s^{−n}∫ O(α)ρ^(n)(γ + α/s) dα for the correlation function ρ^(n) = (DN)!/(DN − n)! · p^(n) whenever the joint density exists, and needs no density. The printed integrals are the Lean sums times s^n (DN − n)!/(DN)!, a factor below 1 for large N; so the Lean bound implies the printed one, and is a strengthening. In the printed normalization both integrals are of order (𝔯(k)/N)^{n/3}, so near the edge the printed bound is close to trivial. The paper does not write out the step from (2.11) to the correlation comparison; the library proves it (`quant_increment`, `localized_eval_half`).
5. **The left-edge tuple of Theorem 2.2.** Paper: γ₋(DN)^{2/3}(λ_{DN} − E⁻, …, λ_{DN−n} − E⁻), which has n + 1 entries and cannot be an argument of O ∈ C_c^∞(ℝ^n). Lean: the n entries λ_{DN}, …, λ_{DN−n+1}, compared with (DN)^{2/3}(μ_{DN−i} + 2), which has the same law as (DN)^{2/3}(2 − μ_{i+1}) (W ↦ −W).
6. **Every unit eigenvector.** Paper: v_k, the eigenvector of λ_k, in Theorems 2.1 and 2.4. Lean: the events ask for some unit eigenvector of λ_k, so the bounds hold for every choice of v_k, also when λ_k is not simple. The probability of an event that is not shown to be measurable is its outer measure (`blockLaw` is a measure, applied to a set), which only strengthens the bound.
7. **The uniform form of the constants.** Paper: for a given model, there is a constant c (or ε₀). Lean: c, ε₀ and N₀ are chosen after D, δ_A, ε_A, C (and after n and O where these occur, and after ε in Theorem 2.4 (i) and Theorem 2.5 (i)), before N, and the bound holds for all N ≥ N₀, all entry laws with the constants C, all admissible A and all k. This implies the reading along a fixed sequence of models, and is equivalent to it by a diagonal argument.
8. **The GUE.** Paper: "a DN × DN GUE". Lean: `gueLaw` (DN) read through `wig` (DN), with E|W_ij|² = 1/(DN) and real diagonal entries of variance 1/(DN), the normalization of (4.1) [defVt] and (4.3) [eq:eq_in_law_H], whose spectrum has the edges ±2.
9. **m, ρ_N, E^±, γ_±.** Paper: m is "the unique solution of (2.16) with Im m(z) > 0", ρ_N is given by (2.19), E^± are the ends of its support and γ_± are defined by the limits (2.6). Lean: `mSol` chooses a solution with Im m > 0, and `rho`, `Eplus`, `Eminus`, `gammaPlus`, `gammaMinus` are defined by `Filter.limUnder`, by the supremum and infimum of the support and by the limits of (2.6). Existence and uniqueness of m, the single-interval support and the existence of the limits are separate theorems (§1).
10. **The quantiles.** `quant` is (2.20) literally: the supremum of the x with ∫_x^∞ ρ ≥ (k − 1/2)/(DN), for ρ_N and for ρ_sc.
11. **The range k > DN/2.** Paper: the proofs of §5 treat 𝔯(k) = k and say that "the other case can be treated analogously". Lean: the statements are for every k ∈ ⟦1, DN⟧; the case 2k > DN + 1 is obtained from the case 2k ≤ DN + 1 by the reflection h ↦ −h, A ↦ −A, k ↦ DN + 1 − k (and O ↦ O(−·) for the correlation comparison): `LocalizedEvecHalf`, `LocalizedEvalHalf`, `localized_evec_reflect`, `localized_eval_reflect`. The left edge of Theorem 2.2 is obtained from the right edge in the same way (`mixEV_reflect`).
12. **The quantifiers of ε, ε₀ and c in Theorem 2.4.** Paper: "for any small constant ε ∈ (0, 2ε_A), there exists ε₀ = ε₀(ε)", and in (2.9) "a constant c > 0 depending on ε_A". Lean: the first bound for every ε ∈ (0, 2ε_A), with ε₀ depending on ε and on the fixed D, δ_A, ε_A, C; in (2.9), c depends on D, δ_A, ε_A and C. In Theorem 2.5, (2.10) holds for every ε > 0 and ε₀ ∈ (0, 2ε), as printed.
13. **Assumption 1.** The laws of the entries are encoded by the laws of the scaled entries √N H_ij (`EntryLaws`): one law for the diagonal, one for the entries above the diagonal, the same for all D blocks, as in the paper (i.i.d. diagonal and i.i.d. off-diagonal entries). The law may depend on N, since it is chosen after N.
14. **The complex Hermitian case only.** The paper states the real symmetric case "can be proved in the same way"; it is not formalized (§7).

### (b) Corrections in the proofs

The items below are places where a step of a proof in the arXiv version fails, is incomplete or has a missing case; the Lean proof does the step as described. None of them changes the conclusion of Theorem 2.1, 2.2, 2.4 or 2.5, and the corrected version in `paper/` carries all of them. Misprints that cannot mislead are corrected in the same version and are not listed here.

1. **Lemma 2.9 [lem_loc]: from (2.23) [eq:aver_local] to the rigidity (2.24) [eq:rigidity].** Step: (2.24) is derived from (2.23) with B = I. The error N^τ/(Nη) cannot exclude an eigenvalue near E⁺ + N^{−2/3+τ}, since one eigenvalue contributes only 1/(DNη) to Im⟨G⟩. Lean: an improved averaged bound outside the spectrum, N^{τ′}(1/(N(κ + |η|)) + 1/((N|η|)²√(κ + |η|))) for B in the span of the E_a; the spectral inclusion λ_1 ≤ E⁺ + N^{−2/3+τ′}, λ_{DN} ≥ E⁻ − N^{−2/3+τ′}; no eigenvalue of modulus ≥ 4, from trace moments; then counting. Names: `aver_local_outside`, `spec_inclusion`, `far_no_eigenvalue`, `opNorm_noise_le`, `count_of_aver`, `rigidity_of_count`, `rigidity`.
2. **Theorem 2.4, the proof for general D, (5.18) [localized_bound_eigenvector_general_D].** Step: the event 𝓔_(a) controls dist(λ_k − Δ_ev, spec H_b) for b ≠ a, while (5.18) estimates ‖E_a v_k‖² on 𝓔_(a); the argument for a = 1 needs the distance to spec H_1. Lean: the bound is for Σ_{b≠a} ‖E_b v_k‖² on 𝓔_(a), pathwise, for every unit eigenvector and with an explicit constant, followed by Markov's inequality. Names: `offblock_mass_le`, `localized_evec_half`.
3. **Definition 2.7 [defn_Mm] and Definition 2.10 [def_moving_Lambda]: m in the lower half plane and on the real axis.** Step: "the unique solution with Im m(z) > 0 for z ∈ ℂ₊" does not say which solution is taken for Im z < 0, where (2.16) has several (for Λ = 0, z = −i: m ≈ 1.618i and m ≈ −0.618i; only the second satisfies m(z̄) = conj m(z)); m(E) and M(E) for real E, used in (A.4) [equation_E_in_spectrum] and in Appendix A, are not defined. Lean: m on ℂ₊ as above, extended by m(z̄) = conj m(z) to the lower half plane and by the vertical limit to the real axis. Names: `mSol`, `mExt`, `MExt`, `mSol_existsUnique`, `mExt_conj`, `mExt_boundary`.
4. **(A.9) [1-M-2] of Lemma A.1 [lemma_usual_properties_of_m_and_mu], proof.** Step: a lower bound ‖1 − M̂‖ ≳ N^{−ε_g} does not give ‖(1 − M̂)^{−1}‖ ≲ N^{ε_g}. Lean: M̂(z, z) is a symmetric circulant matrix, hence normal, so ‖(1 − M̂)^{−1}‖ = max_l |1 − λ̂_l|^{−1}, and each |1 − λ̂_l| ≳ N^{−ε_g}. Names: `one_minus_Mhat_same`, `Mhat_eigvec`.
5. **Lemma A.3 [lemma_modification_of_shift]: large η.** Step: ε ∈ (0, 1) allows η = N^{−2/3+ε}k^{−1/3} > τ^{−1} (ε > 2/3, k = 1), outside the region |z| ≤ τ^{−1} of Lemma A.1 that the proof uses; the conclusion still holds there. Lean: the case η ≥ 1 is proved separately, and the statements hold for every ε ∈ (0, 1) and every k ∈ ⟦1, DN⟧ with 𝔯(k). Names: `modification_shift_eigenvector`, `modification_shift_eigenvalue`.
6. **(3.36) [comH0], (3.37) [comH] in Lemma 3.13 [main_lemma_com].** Step: the moments are written E(H_ij)^l (H*_ij)^κ; since H is Hermitian, (H*)_ij = H_ij, so the condition literally matches only the moments E H_ij^{l+κ}, while the Lindeberg replacement needs all mixed moments E H_ij^l conj(H_ij)^κ. Lean: matching of all mixed moments E h^a h̄^b of the scaled laws, exactly for a + b ≤ 3 and up to K N^{−δ} for a + b = 4. Names: `main_lemma_com_theta`, `moment_matching`.
7. **Lemma 3.8 [lem_flow_1], proof: the a priori bound.** Step: "|[L_xy]_t| ≤ N" from ‖G‖ ≤ η^{−1} does not follow; (3.56) [eq:quad_var] with six resolvents gives a bound of order N^{−2}η^{−6}, which is of order N^4 at η = N^{−1}. Only some bound N^C is needed. Lean: a polynomial bound. Names: `flowL2_grid`.
8. **(5.12) [rigidity12]: rigidity of the Wigner blocks.** Step: the rigidity is quoted as "(2.24) in the case of D = 1", but Lemma 2.9 is stated under Assumption 1 (D ≥ 2), and the quantiles (5.13) [eq:gammak2] use the mass (i − 1/(2D))/N, not (i − 1/2)/N of a single Wigner block. Lean: (2.23) at A = 0 with B = E_a, through D⟨G E_a⟩ = N⁻¹ tr (H_a − z)⁻¹, and the quantile shift |γ^sc_i(N) − γ^sc_{Di}(DN)| ≤ C N^{−2/3} min(i, N + 1 − i)^{−1/3}. Names: `rigidity12`, `blockH_ntr_res_Ea`, `quant_shift`.
9. **(A.33) [derivative_of_eq_of_m_E_t] in the proof of (A.32) [derivative_of_edge] (Lemma A.2).** Step: the equation m_t(E_t^+) = ⟨(Λ_t − E_t^+ − m_t(E_t^+))^{−1}⟩ is differentiated in t without showing that t ↦ E_t^+ and t ↦ m_t(E_t^+) are differentiable, and the chain rule through E ↦ m_t(E) is not available at the edge, where ∂_E m_t = ⟨M²⟩/(1 − ⟨M²⟩) diverges (⟨M_t(E_t^+)²⟩ = 1). The fix: w_t = E_t^+ + m_t(E_t^+) is the unique root above the spectrum of Λ_t of ⟨(w − Λ_t)^{−2}⟩ = 1, whose w-derivative does not vanish, so the implicit function theorem applies. Lean: the edges are written through this root, E⁺ = w₊ + ⟨(w₊ − Λ)^{−1}⟩, and (A.2) [edge_close_to_edge_sc], the use of (A.32) in the paper, is proved from this formula without differentiating in t. Names: `edge_close_to_edge_sc`.
10. **(2.13) [def_M], Remark 2.6 and Lemma A.1 (vi): D = 2.** Step: 𝒮(M) = mI and the translation invariance of M̂ are derived from the block translation symmetry of M, which fails for D = 2 and non-normal A (M_(11) ≠ M_(22); for A = [[0, 1/20], [0, 0]] and z = i, M_(11) = diag(0.617526i, 0.618116i) and M_(22) = diag(0.618116i, 0.617526i)). Both conclusions hold. Lean: for D = 2, from (2.15) [eq:MD=2] and the trace identities tr f(AA*) = tr f(A*A), A(A*A − w²)^{−1} = (AA* − w²)^{−1}A. Names: `def_M_scalar`, `Mhat_translation`, `eq_MD2`.
11. **Lemma 2.11 [lem:complex_cumu]: the definition of 𝒞^{(p,q)}.** Step: 𝒞^{(p,q)} = (−i)^{p+q}∂_s^p∂_t^q log E e^{ish+ith̄} at s = t = 0 for real s, t. Since Re(ish + ith̄) = (t − s) Im h, the expectation may be +∞ for every t ≠ s when only the moments are finite (h = iX with X log-normal), which (2.3) allows. Lean: 𝒞^{(p,q)} is the joint cumulant of p copies of h and q copies of h̄, by the moment–cumulant formula over set partitions; the derivatives are Wirtinger derivatives. Both readings give the numbers the paper uses. Names: `ccum`, `wirt`, `cumulant_expansion`.
12. **(A.11) [flat_M], proof, (A.29) [eq:whlambdal].** Step: the first inequality, 1 − |Re λ̂_l| ≥ Σ_{b∈{2,D}} |Re M̂_1b|(1 − |cos θ_b|), does not follow from (A.28) [sum_wh_M_bound]: it drops the terms Im M̂_1b sin θ_b, which do not vanish near the edge (D = 3, A = 0.05·I, z = E⁺ − 10⁻³ + 10⁻⁸i: Im M̂_12 ≈ −3.5·10⁻⁴, Re M̂_12 ≈ 2.7·10⁻³). The dropped terms are O((Im m + η)‖A‖²_HS/N) and are absorbed. Lean: the proof splits according to |1 − ⟨M²⟩| ≥ 1/10 or < 1/10 and absorbs these terms; the statement is in multiplicative form for every η > 0. Names: `flat_M`, `flat_KTheta`.
13. **Lemma A.1 (xii), proof of (A.17) [eq:otherM2], (A.18) [eq:akbk2].** Step: "d̂_1 = 1 + o(1) when κ + η = o(1) by (A.12)", but (A.12) [de_ir_0] is stated for E ∈ [E⁻, E⁺] only; outside the spectrum the step is missing. Lean: |1 − ⟨M²⟩| ≤ (1 − ⟨MM*⟩) + C(η + Im m) together with η/(Im m + η) ≲ √(κ + η) from (A.1) [square_root_density], inside and outside the spectrum. Names: `otherM2`.
14. **Lemma A.3, proof: (A.46) [equation_derivative_gamma_k_t] and (A.52) [derivative_f_t_minus_gamma_k_t].** Step: (A.45) [def_gamma_k_t] is differentiated in t without showing that γ_k(t) and t ↦ m_t(z_t) are differentiable, and ∂_t is passed through an integral with a moving upper limit and an integrand ∂_t m_t(x) that is unbounded like (E_t^+ − x)^{−1/2}. Lean: the proof works with a quantile regularized at height h > 0 (defined with Im m_t(x + ih)), which is differentiated by the implicit function theorem and is uniformly close to γ_k(t). Names: `modification_shift_eigenvector`, `modification_shift_eigenvalue`, `derivative_m_t_z`.
15. **(5.47) [eq:sizeT], (5.48) [eq:Tsmallthansize] in the proof of Lemma 5.2 [lemma_localized_eigenvector_local_law].** Step: the text calls the first and second components of size(𝒯) = (S + u, m − n + u) size₂ and size₁; read literally, (5.48) gives ⟨G₀Λ̃G₁Λ̃⟩ ≺ N^{−1}‖A‖², which is false for A = cI_N (the expectation is of order ⟨Λ²⟩ ≍ c²). Lean: size₁ = S + u, size₂ = m − n + u. Names: `LoopExpr.size`, `loop_generic_bound`.
16. **After (5.49) [operation_sequence]: termination of the expansion.** Step: the bound on the number of steps between two gains uses that "each 𝔯 or 𝔠₂ reduces the number of 𝒢 in the loops containing Λ̃₁, Λ̃₂", which fails for 𝔠₂: ⟨G₀Λ̃₁G₁Λ̃₂⟩ ↦ DΣ_x⟨M₀Λ̃₁G₁E_x⟩⟨E_xG₁Λ̃₂G₀⟩ raises that number from 2 to 3. Lean: the quantity that decreases is k_# of the expanded loop, which gives the bound 2m + 1; the number of rounds still depends on ε only. Names: `loop_terminates`.
17. **(5.11) [eq:probab12] in the proof of Theorem 2.4: the index window.** Step: the union is taken over i, j ∈ ⟦k₀ − N^τ, k₀ + N^τ⟧; near the edge (k ≲ N^{3τ/2}) up to N^{3τ/2} indices j can have λ_j^{(2)} in the window A_{j,τ}. Lean: the indices are counted with (5.12) [rigidity12] and the spacing of the semicircle quantiles, and τ is taken small compared with δ₀; the statement is for any two different blocks of D ≥ 2. Names: `blocks_repulsion`, `quant_spacing_sc`.
18. **Lemma 3.3 [key_lemma_delocalized_eigenvector], proof: the constant c_L.** Step: "choosing c_L = ε_g" does not follow, since the bounds used are ≺-bounds on deterministic quantities (Definition 2.8 [stoch_domination] (ii)), which give N^{−1−ε_g+τ}η^{−2} for each τ > 0. Lean: c_L = ε_g/2; the proof of Theorem 2.1 only needs some c_L > 0. Names: `key_lemma_theta`.
19. **Lemma 5.5 [claim_estimate_remainder_terms], proof: termination of the further expansion.** Step: the termination is quoted from "the same argument as below (5.49)", whose reason fails (item 16) and fails in the same way in the classes (5.79)–(5.81). Lean: a termination measure (the number of remaining gains, then the count of resolvents weighted by the occurrences of Λ̃), with the operation 𝔣𝔯 counted as a gain; the number of rounds depends on ε and the starting expression only. Names: `pkg_terminates`, `PkgExpr.psiP`, `PkgExpr.FStopped`.
20. **Lemma 5.5 [claim_estimate_remainder_terms]: the signed sum.** Step: the lemma bounds E𝓡 for each admissible sequence and each starting expression 𝒯₀ of (5.32), but the proof bounds three families of terms only after summing over the four signed choices of (5.29) [expansion_of_im]; without the pairing, a term of the direct case (ii) is of size N^{−4/3−ε/4}‖A‖²_HS at k = 1, above the claimed N^{−5/3+Cε}‖A‖²_HS. Lean: Lemma 5.5 for the signed sum over the four starting loops, which is the form used in the proof of Lemma 5.2. Names: `loop_rem_bound`.
21. **Lemma 3.8 [lem_flow_1], proof, (3.71) [eq:wtKt].** Step: ‖K̃_t‖ is bounded at the flow time t by (A.9) [1-M-2], which is stated only for η/Im m ∼ N^{−ε_g}; along the flow η_t/Im m_t = e^{t_c−t} − 1 falls below N^{−ε_g}. Lean: the eigenvalues of M̂_{(1,2),t} have modulus at most Im m_t/(Im m_t + η_t) = e^{−(t_c−t)}, so (t_c − t)K_t has its eigenvalues in a disc with real diameter [−(t_c − t), 1], which gives ‖𝒯_t‖ ≤ 1 + (t_c − t) without (A.9). Names: `tOp_norm_le`.
22. **Lemma 3.9 [lem_flow_2] and Lemma 3.10 [lem_flow_1.5]: the "analogous adaptation".** Step: the adaptation of [stone2024randommatrixmodelquantum, Lemmas 4.7, 4.8] needs ‖𝒯^{(3)}_t‖ ≤ 3/2 + o(1) and ‖T_t‖ ≤ 1/2 + o(1), which are derived there from ‖K̃_{(i,i),t}‖ = o(1), true only for Im m ∼ 1; at the edge it fails (D = 2, Λ = 0, z = 2 + 10^{−4}i, t_c − t = 0.014142: (t_c − t)K_{(1,1)} ≈ 0.49295 − 0.49998i). Lean: from the disc of item 21, ‖𝒯^{(3)}_t‖ ≤ (3/2)(1 + t_c − t) and ‖T_t‖ ≤ (1/2)(1 + t_c − t). Names: `tOp3_norm_le`, `tOp1_norm_le`.
23. **Lemma 3.11 [lem_flow_3]: the bound on K_{(1,2,1),t}.** Step: the adaptation of [stone2024randommatrixmodelquantum, Lemma 4.9] needs |K_{(1,2,1),t}| ≲ Im m_t/η_t² at every flow time, while (A.9) is not available along the flow (item 21), and the disc bound alone loses a factor Im m_t/(t_c − t). Lean: K_{(1,2,1),t} is deterministic, and on an event of positive probability where (A.53) [entprodG] and (3.29) [flow_3G_res_2] hold, |K| ≤ |L| + |L − K| ≤ 2N^τ Im m_t/η_t². Names: `flowL2_exp`, `flowL2_exp_paper`, `flowL3_grid_paper`.
24. **Lemma 5.5, companion case (6): the exceptional subcase.** Step: the subcase fR = 1, m + u = 4 is said to be empty ("a direct enumeration … shows that no such term exists"); it is not (an explicit term arises from the starting expression of Example 5.7 [example_estimate_reminder_reminder_terms]), and the rough bound of case (6) gives only N^{−4/3−ε/2−ε_A}‖A‖²_HS for it. Lean: in this subcase the loop containing Λ̃₂ is always ⟨𝔐₁Λ̃₂𝔐₀E_x⟩, and (5.5) [regular_estimate_localized_eigenvector] gives an extra factor Im m, hence N^{−5/3−ε_A}k^{2/3}‖A‖²_HS. Names: `pkg_rem2_two`, `pkg_rule_two`.
25. **Lemma 5.5, further terminal case (ii), m + u = 4.** Step: the loop containing Λ̃₂ is said to remain ⟨𝔐₀Λ̃₂𝔐₁E_x⟩ because a third 𝔐 would need a third replacement, but every term of (5.83) turns the expanded 𝒢 into 𝔐 and the gain operations also produce 𝔐; there are leaves whose Λ̃₂-loop has three 𝔐 and is not of the form of (5.5). Lean: when that loop is produced by 𝔰𝔩𝔞𝔰𝔥₂, the extra Im m is taken from the cut package (which keeps at least two resolvents, (A.53)); when it is produced by 𝔠₂, it is ⟨𝔐₁Λ̃₂𝔐₀E_y⟩ and (5.5) applies. Names: `pkg_leaf_bound`, `pkg_rule_leaf`.
26. **(4.19) [GEaD3] in the proof of Lemma 4.3 [rescomY].** Step: the sum over N^ε < r ≤ N^c uses (λ_r − E_i)² ≳ (r/N)^{4/3}, which needs ε > 3σ/2; the condition 0 < σ + ε < c/6 does not give it (the window |E_i − E⁺| ≤ N^{−2/3+σ} contains about N^{3σ/2} eigenvalues). Lean: the condition ε ≥ 2σ, which is compatible with the other conditions. Names: `edgeSpec_le`, `edge_gap_lower`, `rescomY`.
27. **(4.13) [single_resolvent_local_law_bound2]: complex Hermitian polarization.** Step: the resolvent of a complex Hermitian matrix is not symmetric, so polarization with e_x ± e_y controls only Im(G_xy + G_yx), and the factors of ∂^m_xy ∂^n_yx F(A_t) are not of the form Im(G⋯G) (for H = [[0, i], [−i, 0]] and z = 3 + iη, Im G_12 → −1/8 while Im G_{uu} = O(η) for u = e_1 ± e_2). Lean: G_ax G_yb − G*_ax G*_yb = 2i[(Im G)_ax G_yb + G*_ax (Im G)_yb], so that each monomial carries a factor (Im G)_ab controlled by (4.12) [single_resolvent_local_law_bound]. Names: `edgeFn_wirt_le`, `edgeRes_entry_le`.
28. **Theorem 2.2 [MixEV]: "follows immediately from Lemmas 4.1 and 4.2".** Step: this applies (4.5) [ls_CVtV] to the test function O(γ₊ ·), which depends on N and A through γ₊, while (4.5) is stated for one fixed O. Lean: Lemma 4.2 [CVtV] uniformly in the scale γ ∈ [1/2, 2], which contains γ₊. Names: `CVtV`, `def_gamma_limits`, `mixEV_right`.
29. **Lemma 3.13 [main_lemma_com] on the whole domain 𝐃(τ).** Step: the proof is said to be that of [stone2024randommatrixmodelquantum, Lemma 3.4], which is in the bulk and bounds traces of resolvent products by (A.53), whose hypothesis Nη Im m ≳ 1 fails on parts of 𝐃(τ) (D = 1, Λ = 0, z = 3 + iN^{−1+τ}: Nη Im m ≈ 0.171N^{−1+2τ}). Lean: Ward's identity (2.32) [eq_Ward] at both ends with (2.22) [eq:aniso_local], |u*G₁B₁⋯G_q v| ≤ ‖G₁*u‖‖G_q v‖|η|^{−(q−2)}, which needs no condition on Im m. Names: `main_lemma_com_theta`.
30. **Lemma 4.1 [CVtG], proof: the cited edge universality.** Step: the proof applies [landon2017edgestatisticsdysonbrownian, Theorem 2.2] to V + √t W with W a GUE; the citation should name the result for the GUE (complex Hermitian) case. Lean: the GUE form is the explicit hypothesis `LandonYauEdge` (§5). Names: `LandonYauEdge`, `CVtG`.
31. **(3.42) [eq:Exp_G1-M1] of Lemma 3.15 [lem:fourthcumu2] for D = 2.** Step: the cited proof uses the block translation symmetry of M₁ to make the block sums of (M₁)²_{ββ} independent of the block; for D = 2 and Λ = [[0, A], [A*, 0]] this fails ((2.15) gives M_(11) = w(AA* − w²)^{−1} ≠ M_(22) = w(A*A − w²)^{−1}), and the leading coefficient of (3.42) is wrong by a term of order ‖A‖⁴, which exceeds the stated error for small δ_A and ε_g. Lean: (3.42) with an additional error term N^{−1}‖A‖ inside the error ρ, for every D ≥ 2; Lemma 3.7 [lemma_G_large_2] absorbs it with a margin N^{−δ_A/2}. For D ≥ 3 the paper's form without this term is not stated separately. Names: `lem_fourthcumu2_theta'`, `lead15`, `lemma_G_large_2_theta`.
32. **Lemma 3.14 [lem:fourthcumu1] and Lemma 3.15, proofs: third-order cumulants.** Step: the proofs write the (1, 2)-cumulant of each ordered pair as N^{−3/2}(κ^{(1,2)} + uδ_{αβ}) and bound the sum by ‖u‖‖G₂‖‖v‖; under Assumption 1 the entries below the diagonal are the conjugates of those above, so the cumulant at (β, α) is the conjugate of that at (α, β), and κ^{(1,2)} = E[x²x̄] need not be real (x = X + iY with X, Y independent, centred, of variance 1/2, E X³ = 0, E Y³ ≠ 0). The sum splits into α < β and α > β with different coefficients, and |Σ_{α<β} u_β G_βα v_α| ≤ ⌈log₂(DN)⌉‖u‖‖G‖‖v‖ (dyadic decomposition of the strict lower triangle); the logarithm is absorbed by ≺. Lean: the cumulant of each entry is written with its own coefficient (κ above the diagonal, its conjugate below); the statements are unchanged. Names: `lem_fourthcumu1_theta`, `lem_fourthcumu2_theta'`, `ouMatLaw_ccum`.

### (c) Rate forms and paper forms

For four lemmas of §3 the library has a general form, with the initial term of the flow or a conditional form on the grid, and the paper's form under the names X and X_paper. They are listed below (generated from the source).

| General form | Paper form | File |
|---|---|---|
| `flowG1_exp` | `flowG1_exp_paper` | `RBMTransitionEdge/Flow/LemFlowExp.lean` |
| `flowL2_exp` | `flowL2_exp_paper` | `RBMTransitionEdge/Flow/LemFlow3.lean` |
| `flowL2_grid` | `flowL2_grid_paper` | `RBMTransitionEdge/Flow/LemFlow1.lean`, `RBMTransitionEdge/Flow/LemFlowExp.lean` |
| `flowL3_grid` | `flowL3_grid_paper` | `RBMTransitionEdge/Flow/LemFlow2.lean`, `RBMTransitionEdge/Flow/LemFlowExp.lean` |

### (d) Steps the paper sketches, completed in the library

- **The cited local laws.** Lemma 2.9 [lem_loc] is quoted from [stone2024randommatrixmodelquantum, Lemma 2.9], and the local law of Lemma 4.4 [lem:samefort] from Lemma 6.4 there; both are proved in the library for a class of noises (`LLClass`) that contains the block matrix H (`llClass_blockH`) and the law (4.3) of H_t (`llClass_ouLaw`), including the edges and the region outside the spectrum (§3 (b) 1): `local_law_seq`, `aniso_local`, `aver_local`, `rigidity`, `samefort_local`. (5.12), quoted from [erdHos2012rigidity, Theorem 2.2], is `rigidity12`.
- **Lemmas quoted with "minor modifications" or "a similar approach".** Lemmas 3.5–3.11 and 3.13–3.15 adapt lemmas of [stone2024randommatrixmodelquantum]; the library proves them for the law of H_t with the class parameter θ = e^{−t}: `charFlow_M`, `lemma_G_large_two`, `lemma_G_large_three`, `lemma_G_large_BB`, `lemma_G_large_2_theta`, `flowL2_grid`, `flowL3_grid`, `flowG1_exp`, `flowL2_exp`, `main_lemma_com_theta`, `lem_fourthcumu1_theta`, `lem_fourthcumu2_theta'`. The moment matching quoted from [erdHos2012bulk, Lemma 6.5] is `moment_matching`, and the cumulant expansion quoted from [He:2017wm, Lemma 7.1] is `cumulant_expansion`.
- **Lemma 4.1 [CVtG] and Lemma 4.2 [CVtV].** "By a similar argument as that in [CorrelatedBandAOP, Section 6.1]": the regularity of V and the comparison of E_fc, γ_fc with E⁺, γ₊ are `CVtG_regular`, `fc_close`, `fcDet_eq`, `mSol_subord`, `fcMom_rigid`. Lemma 4.2 from Lemma 4.3, following [Erds2017ADA, Section 17] and extended to n eigenvalues and smooth O: `cvtv_of_rescomY`, `edge_smoothing`, `edge_joint_sandwich`, `integral_eq_survival`.
- **Omitted proofs.** Lemma 4.4 (`samefort_local`, with the Gaussian-divisible form `ouMatLaw_mix_eq`); (A.55) [two_loop_estimate] for l₁l₂ = 0 (`two_loop_estimate`); the stability of (2.16) near the edge and the facts on 1 − M̂ (`one_minus_Mhat_stability`, `one_minus_Mhat_same`); the existence, uniqueness and analyticity of m and its Stieltjes representation (`mSol_existsUnique`, `mSol_analyticOnNhd`, `rho_stieltjes`); the square-root behaviour quoted from [lee2015edge, Lemma 4.3] (`square_root_density`, `rho_support`, `def_gamma_limits`); the derivative of λ_k(H + tΛ) in (5.24) [ygfyz] (`eigK_line_deriv`, `eigK_line_ftc`); the step from (2.11) to the correlation comparison (`quant_increment`).
- **The left edge and k > DN/2.** By reflection (§3 (a) 5, 11): `mixEV_reflect`, `edge_neg`, `HLam_neg`, `localized_evec_reflect`, `localized_eval_reflect`.
- **General D.** The proof of Theorem 2.4 is written for D = 2 and then sketched for general D (with the correction of §3 (b) 2); the library proves the pathwise bound and the level repulsion between any two different blocks for every D ≥ 2 (`offblock_mass_le`, `blocks_repulsion`). The facts that the paper derives from the block translation symmetry are proved for D = 2 separately (§3 (b) 10, 31).

### (e) Route

- **The stochastic flows.** The Ornstein–Uhlenbeck flows (3.12) [eq:Ht] and (4.1) [defVt] are true paths on a fine discrete time grid (step N^{−C}): exact Gaussian steps, stopping times on the grid, the Azuma–Hoeffding inequality and Doob's maximal inequality in place of the Itô calculus, the quadratic variation (3.56) and the Burkholder–Davis–Gundy inequality before (3.59) [CIest]; a discrete Duhamel formula in place of the Peano–Baker series of (3.65) [eq:PBintegral]–(3.68) [Phinorm]; and an induction on the grid in place of the stopping time and the continuity argument after (3.70) [eq:self_imp]. Names: `gridState_law`, `gaussStepA_expansion`, `gridAzumaA_stopped`, `gridMartA_max`, `gridDoobA_max`, `doob_sq_maximal`, `discrete_duhamel`, `propag`, `norm_propag_le`, `riemann_inv_le_log`, `duhamel_quad_boot`. Lemmas 3.8 and 3.9 hold at the grid times of one grid (not at all real times at once); their uses need only one time, which is a grid time of a suitable grid.
- **One-time laws.** Where only an expectation at one time is used (Lemma 3.10, Lemma 3.11 [lem_flow_3], Lemma 4.3 [rescomY]), the library uses the law (3.13) [eq:Gauss_div], (4.3) of the flow at that time and differentiates its expectation by Gaussian integration by parts: `ouLaw`, `ouMatLaw`, `blockOULaw`, `hasDerivAt_ouExpect`, `gueBlocks_ibp`.
- **The class parameter.** Lemma 3.3 and the lemmas of §3 that feed it are proved for the law of H_t of (4.1) with K replaced by K_θ, θ = e^{−t} (`KTheta`, `key_lemma_theta`), so that one proof serves Theorem 2.1 and the eigenvector input (3.4) [eq:extend:main_evector1] of Lemma 4.3 (`evec_window`).
- **The characteristic flow.** The flow of Definition 3.4 [flow] is given in closed form and shown to solve (3.10) [eq:deterflow] (`charFlow_deriv`, `charFlowZ_conj`).
- **Counting and the far region.** Eigenvalues are counted from the averaged law with Poisson smoothing on rectangles, not with the Helffer–Sjöstrand formula (`integral_im_ntr_res`, `count_of_aver`, `rigidity_of_count`); the region far from the spectrum is handled with trace moments (`trace_moment_le`, `opNorm_noise_le`, `far_aver_seq`).
- **The expansion of §5.3.** The expressions of (5.33) and (5.79)–(5.81) are finite data (`LoopExpr`, `PkgExpr`), the expansions are trees with the stopping rule Ψ ≥ 4 in place of stopping criterion (i) above (5.49) (`LoopExpr.Stopped`, `loop_tree_sum`, `pkg_tree_sum'`), and the many cases of the estimates in the proof of Lemma 5.5 are handled by four rule lemmas (`pkg_rule_one`, `pkg_rule_two`, `pkg_rule_three`, `pkg_rule_leaf`).
- **The eigenvector step of Theorem 2.1.** The spectral step does not use an eigenbasis (`evec_proj_le`), and the expectation of η² tr(Im G B Im G B) is computed by an exact identity (`trImGB_eq`).

## 4. Consistency of the hypotheses

The hypotheses of each main result hold together at a concrete nondegenerate point, and the conclusions are not trivially true there.

- **Entry laws.** `entryLaws_nonempty` gives an entry law with moment constants C p = 2: the Rademacher law on the diagonal and the uniform law on {1, i, −1, −i} above it.
- **Admissible couplings.** For D = 3, δ_A = ε_A = 1/100 and k = 1 (so 𝔯(1) = 1), A = N^{−1/10}I_N satisfies ‖A‖ ≤ N^{−δ_A} and (2.4) (‖A‖_HS = N^{2/5} ≥ N^{1/3+1/100}), and A = N^{−1/4}I_N satisfies ‖A‖ ≤ N^{−δ_A} and (2.8) (‖A‖_HS = N^{1/4} ≤ N^{1/3−1/100}), for every N ≥ 1:

```lean
/-- An admissible coupling for Theorems 2.1 [mix] and 2.2 [MixEV]: for `D = 3`,
`δ_A = ε_A = 1/100` and `k = 1`, the matrix `A = N^{-1/10} I_N` satisfies `‖A‖ ≤ N^{-δ_A}` of
Assumption 1 [main_assm] and (2.4) [eq:condA1]. -/
theorem admissible_delocalized (N : ℕ) (hN : 1 ≤ N) :
    opNorm ((((N : ℝ) ^ (-(1 / 10 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤
        (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤
        hsNorm ((((N : ℝ) ^ (-(1 / 10 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
```

```lean
/-- An admissible coupling for Theorems 2.4 [theorem_localized_eigenvector_localization] and
2.5 [theorem_localized_eigenvalue]: for `D = 3`, `δ_A = ε_A = 1/100` and `k = 1`, the matrix
`A = N^{-1/4} I_N` satisfies `‖A‖ ≤ N^{-δ_A}` of Assumption 1 [main_assm] and (2.8)
[eq:condA2]. -/
theorem admissible_localized (N : ℕ) (hN : 1 ≤ N) :
    opNorm ((((N : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤
        (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      hsNorm ((((N : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤
        (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) :=
```

- **The hypotheses together** (`RBMTransitionEdge/Main/Statements.lean`). The compiled checks at the end of the statement file: the norms of a scalar matrix, 𝔯(1) = 1, `blockLaw` and `gueLaw` are probability measures, H_Λ is Hermitian, and each statement's hypotheses hold together at D = 3, δ_A = ε_A = 1/100, k = 1, C p = 2, with A = N^{−1/10}I_N (delocalized regime) or A = N^{−1/4}I_N (localized regime), ε = ε₀ = 1/100, and a bump O on ℝ² with O(0) = 1:

```lean
/-- The operator norm of `2 I_3` is `2`. -/
example : opNorm ((2 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 2 :=
```

```lean
/-- `𝔯(1) = 1` for `D = 3`, `N = 5`. -/
example : rk 3 5 1 = 1 := rk_one 3 5 (by norm_num)

/-- `blockLaw 3 4` is a probability measure for the entry laws of `entryLaws_nonempty`. -/
example : IsProbabilityMeasure (blockLaw 3 4 (Classical.choice entryLaws_nonempty)) :=
```

```lean
/-- `blockLaw 3 4` is a probability measure for the entry laws of `entryLaws_nonempty`. -/
example : IsProbabilityMeasure (blockLaw 3 4 (Classical.choice entryLaws_nonempty)) :=
```

```lean
/-- `gueLaw 12`, the GUE law of size `DN = 12`, is a probability measure. -/
example : IsProbabilityMeasure (gueLaw 12) := gueLaw_isProbabilityMeasure 12

/-- `H_Λ` is Hermitian for `D = 3`, `N = 4`, a coupling `A` and a configuration `w`. -/
example (A : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 3 → Coords 4) : (HLam 3 4 A w).IsHermitian :=
```

```lean
/-- `H_Λ` is Hermitian for `D = 3`, `N = 4`, a coupling `A` and a configuration `w`. -/
example (A : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 3 → Coords 4) : (HLam 3 4 A w).IsHermitian :=
```

```lean
/-- The hypotheses of `MixStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`, `k = 1`,
with `C p = 2` and `A = N^{-1/10} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧ (1 : ℕ) ≤ 1 ∧ 1 ≤ 3 * N ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤ hsNorm A :=
```

```lean
/-- The hypotheses of `MixEVStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`, with a
smooth compactly supported `O` on `Fin 2 → ℝ` that is nonzero at the origin, `C p = 2` and
`A = N^{-1/10} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ O : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
      ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) ≤ hsNorm A :=
```

```lean
/-- The hypotheses of `LocalizedEvecStatement` hold together at `D = 3`, `δ_A = ε_A = 1/100`,
`ε = 1/100`, `k = 1`, with `C p = 2` and `A = N^{-1/4} I_N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      IsProbabilityMeasure (blockLaw 3 N L) ∧
      (2 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 / 100 ∧
      (0 : ℝ) < 1 / 100 ∧ (1 / 100 : ℝ) < 2 * (1 / 100) ∧
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧ (1 : ℕ) ≤ 1 ∧ 1 ≤ 3 * N ∧
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) :=
```

```lean
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
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) :=
```

- **The main results applied** (`RBMTransitionEdge/Main/Main.lean`). Each theorem is applied at the same point; every hypothesis holds for all N ≥ 1, and the conclusion is the bound of the theorem at that point:

```lean
/-- Theorem 2.1 [mix] applied at `D = 3`, `δ_A = ε_A = 1/100`, `C p = 2`, `k = 1` and
`A = N^{-1/10} I_N`: every hypothesis holds for all `N ≥ 1`, and the conclusion is the bound for
the event of (2.5) [eq:main_evector1]. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ L : EntryLaws (fun _ => (2 : ℝ)), ∃ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 100) * rk 3 N 1 ^ (-(1 / 3 : ℝ)) ≤ hsNorm A ∧
      blockLaw 3 N L {w | ∃ u, IsUnitEigvec (HLam 3 N A w) (eigK (HLam 3 N A w) 1) u ∧
        ∃ a : Fin 3, (N : ℝ) ^ (-c) ≤ |blockMass u a - ((3 : ℕ) : ℝ)⁻¹|} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-c)) :=
```

```lean
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
          (eigK (wig (3 * N) w) (3 * N - (i : ℕ)) + 2)) ∂(gueLaw (3 * N)))| ≤ (N : ℝ) ^ (-c) :=
```

```lean
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
          ENNReal.ofReal ((N : ℝ) ^ (-c))) :=
```

```lean
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
          (N : ℝ) ^ (-c)) :=
```

```lean
/-- `main_theorems` gives each of the four statements, so each instance above applies to the
corresponding component. -/
example (hEI1 : LandonYauEdge) (hEI2 : ∀ C : ℕ → ℝ, EI2Hyp C) :
    MixStatement ∧ MixEVStatement ∧ LocalizedEvecStatement ∧ LocalizedEvalStatement :=
```

- **Nothing vacuous.** At these points A ≠ 0, so the strict inequalities of §3 (a) 2, 3 are not what makes the statements nontrivial: in the localized regime with ε = 1/100 the threshold of Theorem 2.4 (i) is 1 − N^{−2/3+1/100}N^{1/2} < 1 and that of (2.10) is N^{−99/100}N^{1/4} > 0. The test function O with O(0) = 1 is not zero. The two hypotheses of §5 are closed propositions: they mention no A, k or entry law of the theorems they feed, so they cannot conflict with the other hypotheses; whether they hold is a question about the cited results (§5).

## 5. External inputs

There are two, each an explicit hypothesis of one main result and of nothing else. `mix` and `localized_eval` take no hypothesis, and the library declares no axiom, so neither input can enter Theorems 2.1 and 2.5.

**`LandonYauEdge`** (`RBMTransitionEdge/Edge/Defs.lean`), the hypothesis of `mixEV`. It is the input that the paper cites as [landon2017edgestatisticsdysonbrownian, Definition 2.1, Theorem 2.2, Lemma 2.3] in the proof of Lemma 4.1 [CVtG], used for Theorem 2.2. In words: for D ≥ 2, 𝔠 ∈ (0, 1/10), a ∈ (0, 2𝔠), regularity constants c_V, C_V > 0, n and a smooth compactly supported O, there are c > 0 and N₀ such that for every N ≥ N₀ and every deterministic Hermitian V of size DN that is η_*-regular at some E₀ with η_* = N^{−2/3+a} (`etaRegular`: two-sided bounds of Im⟨(V − z)⁻¹⟩ on both sides of E₀ for η ∈ [η_*, 10], no eigenvalue above E₀ + η_*, ‖V‖ ≤ N^{C_V}), the n largest eigenvalues of V + √t′ W, with W a DN × DN GUE and t′ = 1 − e^{−𝔱}, 𝔱 = N^{−1/3+𝔠}, rescaled by γ_fc(DN)^{2/3} at the edge E_fc of the free convolution (`fcEdge`, `fcGamma`), have the law of the n largest eigenvalues of a GUE up to N^{−c} against O. The constants depend on D, 𝔠, a, c_V, C_V, n and O, and not on V: the hypothesis is asked uniformly over all regular V.

```lean
/-- `η_*`-regularity of `X` at `E₀`, `η_* = N^{-2/3+a}`, constants `c_V`, `C_V` (proof of
Lemma 4.1 [CVtG]): `Im ⟨(X - z)⁻¹⟩ ∼ √(κ+η)` for `E ∈ [E₀ - c_V, E₀]` and `∼ η/√(κ+η)` for
`E ∈ [E₀, E₀ + c_V]`, `z = E + iη`, `η ∈ [η_*, 10]`, `κ = |E - E₀|`; no eigenvalue above
`E₀ + η_*`; `‖X‖ ≤ N^{C_V}`. -/
def etaRegular {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (a cV CV : ℝ)
    (X : Matrix ι ι ℂ) (E₀ : ℝ) : Prop :=
  (∀ E η : ℝ, E₀ - cV ≤ E → E ≤ E₀ → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η → η ≤ 10 →
    CV⁻¹ * Real.sqrt (|E - E₀| + η) ≤ (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ∧
      (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ≤ CV * Real.sqrt (|E - E₀| + η)) ∧
  (∀ E η : ℝ, E₀ ≤ E → E ≤ E₀ + cV → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η → η ≤ 10 →
    CV⁻¹ * (η / Real.sqrt (|E - E₀| + η)) ≤ (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ∧
      (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ≤ CV * (η / Real.sqrt (|E - E₀| + η))) ∧
  eigK X 1 ≤ E₀ + (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ∧
  opNorm X ≤ (N : ℝ) ^ CV
```

```lean
/-- The external input of Lemma 4.1 [CVtG] ([landon2017edgestatisticsdysonbrownian,
Definition 2.1, Theorem 2.2, Lemma 2.3]): for `D ≥ 2`, `𝔠 ∈ (0, 1/10)`, `a ∈ (0, 2𝔠)`,
`c_V, C_V > 0` and a smooth compactly supported `O`, there are `c > 0` and `N₀` such that for
`N ≥ N₀`, every Hermitian `V` of size `DN` that is `N^{-2/3+a}`-regular at some `E₀`, and
`t' = 1 - e^{-𝔱}`, `𝔱 = N^{-1/3+𝔠}`, the `n` largest eigenvalues of `V + √t' W`, `W` a GUE,
rescaled by `γ_fc (DN)^{2/3}` at `E_fc`, have the law of the `n` largest eigenvalues of a GUE up
to `N^{-c}` against `O`. -/
def LandonYauEdge : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ ct : ℝ, 0 < ct → ct < 1 / 10 → ∀ a : ℝ, 0 < a → a < 2 * ct →
    ∀ cV CV : ℝ, 0 < cV → 0 < CV →
    ∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ V : Matrix (Idx D N) (Idx D N) ℂ, V.IsHermitian → ∀ E₀ : ℝ, etaRegular N a cV CV V E₀ →
      |(∫ x, O (fun i => fcGamma V (1 - Real.exp (-edgeTime N ct)) *
            ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (fcEdge V (1 - Real.exp (-edgeTime N ct)) -
              eigK (V + ((Real.sqrt (1 - Real.exp (-edgeTime N ct)) : ℝ) : ℂ) • gueIdx D N x)
                ((i : ℕ) + 1))) ∂(gueLaw (D * N))) -
        (∫ x, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (2 - eigK (wig (D * N) x) ((i : ℕ) + 1))) ∂(gueLaw (D * N)))| ≤ (N : ℝ) ^ (-c)
```

**`EI2Hyp`** (`RBMTransitionEdge/Localized/Repulsion.lean`); ∀ C, `EI2Hyp` C is the hypothesis of `localized_evec`. It is the Wigner level repulsion (5.14) [Wegner12], which the paper cites from [BENIGNI2022108109, Lemmas B.1, B.12] and [Bourgade_JEMS, Proposition 2.10], used for Theorem 2.4. In words: for one N × N Wigner block under Assumption 1 with moment constants C, for every D ≥ 1 and δ > 0 there are δ₀, τ₀ > 0 such that for every τ ∈ (0, τ₀] there is N₀ with: for N ≥ N₀, every entry law with the constants C, every k ∈ ⟦1, DN⟧ and every deterministic x within N^{−2/3+τ}k^{−1/3} of the semicircle quantile γ_k^sc (with DN particles), the probability that the block has an eigenvalue within 2N^{−2/3−δ}k^{−1/3} of x is at most N^{−2δ₀}. The paper's (5.14) has x = λ_j(H_2) for an independent block H_2; conditioning on H_2 gives this form, and the library does this step by Fubini in `blocks_repulsion`.

```lean
/-- The level repulsion (5.14) [Wegner12] for one `N × N` block of (1.3) [matrix_H] under
Assumption 1 [main_assm] with moment constants `C`: for every `D ≥ 1` and `δ > 0` there are
`δ₀, τ₀ > 0` such that for `τ ∈ (0, τ₀]`, `N ≥ N₀`, `k ∈ ⟦1, DN⟧` and every deterministic `x`
with `|x - γ_k^{sc}| ≤ N^{-2/3+τ} k^{-1/3}` (`γ_k^{sc}` the quantile (2.20) [eq:gammak] of the
semicircle law with `DN` particles), the block has an eigenvalue within
`2 N^{-2/3-δ} k^{-1/3}` of `x` with probability at most `N^{-2δ₀}`. -/
def EI2Hyp (C : ℕ → ℝ) : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ δ : ℝ, 0 < δ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
    ∀ k : ℕ, 1 ≤ k → k ≤ D * N → ∀ x : ℝ,
      |x - quant rhoSc (D * N) k| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) →
      coordLaw N L {w | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
          |eigK (wig N w) i - x| ≤ 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * (k : ℝ) ^ (-(1 / 3 : ℝ))} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(2 * δ₀)))
```

Three remarks on how the two hypotheses relate to the cited results.

- **Uniformity.** Both hypotheses are asked uniformly: `EI2Hyp` C over all entry laws with the given moment constants C, `LandonYauEdge` over all regular V with given regularity constants. The cited theorems are stated for one ensemble at a time, with constants that depend only on the moment bounds, resp. on the regularity constants; the uniform form is how the library reads them.
- **The range of k in `EI2Hyp`.** The hypothesis is asked for all k ∈ ⟦1, DN⟧ with the factor k^{−1/3}, while the paper uses it for k ≤ DN/2. For k > DN/2 this asks no more than the cited result: there k^{−1/3} ≤ 𝔯(k)^{−1/3}, so the window for x and the interval around x are smaller than in the reflected statement, which implies it.
- **What the hypotheses are.** Both are closed propositions; they do not mention the A, k or entry law of the theorems they feed, so they cannot conflict with the other hypotheses, and only their truth is in question. That rests on the cited literature, which is not formalized here, and on the limit checks below.

**Compiled checks.** At the end of `RBMTransitionEdge/Edge/CVtG.lean`, Lemma 4.1 is applied at D = 3, δ_A = 1/100, 𝔠 = 1/20, n = 1, C p = 2, a bump O and A = N^{−1/10}I_N, as a function of the hypothesis; and the limit check of `LandonYauEdge`: for the regular choice V = e^{−𝔱/2}W₀ with W₀ a GUE independent of W, V + √(1 − e^{−𝔱})W is again a GUE, so both sides of the hypothesis compare the same law (compiled at size DN = 6 and 𝔱 = 1/10).

```lean
/-- `CVtG` at the nondegenerate point `D = 3`, `δ_A = 1/100`, `𝔠 = 1/20`, `n = 1`, `C p = 2`, a
bump `O` with `O 0 = 1`, and `A = N^{-1/10} I_N` (nonzero, with `‖A‖ ≤ N^{-1/100}`), as a function
of the external input `hEI` (which has no instance), for every `N ≥ N₀`: for some entry laws (which
exist since `entryLaws_nonempty`) the two expectations of (4.2) [ls_CVtG] differ by at most
`N^{-c}`. -/
example (hEI : LandonYauEdge) :
    ∃ O : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        ∃ L : EntryLaws (fun _ => (2 : ℝ)), CVtG_A N ≠ 0 ∧
          opNorm (CVtG_A N) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
          |(∫ h, O (fun i => gammaPlus (lam 3 N (CVtG_A N)) * ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
                (Eplus (lam 3 N (CVtG_A N)) -
                  eigK (Matrix.of h + lam 3 N (CVtG_A N)) ((i : ℕ) + 1)))
                ∂(ouMatLaw 3 N L (edgeTime N (1 / 20)))) -
            (∫ x, O (fun i => ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
                (2 - eigK (wig (3 * N) x) ((i : ℕ) + 1))) ∂(gueLaw (3 * N)))| ≤
            (N : ℝ) ^ (-c) :=
```

```lean
/-- The limit check of `LandonYauEdge` (`V = e^{-𝔱/2} W₀`, `W₀` a GUE independent of `W`):
`e^{-𝔱/2} W₀ + √(1 - e^{-𝔱}) W` is again a GUE, here of size `DN = 6` at `𝔱 = 1/10`. -/
example : ((gueLaw 6).prod (gueLaw 6)).map (fun p => Real.exp (-(1 / 10 : ℝ) / 2) • p.1 +
    Real.sqrt (1 - Real.exp (-(1 / 10 : ℝ))) • p.2) = gueLaw 6 :=
```

At the end of `RBMTransitionEdge/Localized/Repulsion.lean`, (5.11) [eq:probab12] in the form `blocks_repulsion` is applied with `EI2Hyp` as a parameter at D = 3, δ = 1/10, C p = 2, in the edge window k = 1 and in the window k = N. The limit check of (5.14) is the computation for a GUE block: the expected number of eigenvalues in an interval of length 4N^{−2/3−δ}k^{−1/3} near γ_k^sc is of order N^{−δ}, so the probability is O(N^{−δ}) by Markov's inequality, consistent with δ₀ ≤ δ/2; this computation is not compiled.

```lean
/-- `blocks_repulsion` with the level repulsion (5.14) [Wegner12] as a parameter, at `D = 3`,
`δ = 1/10`, `C p = 2`, `k = 1` (the edge window) and the blocks `b = 0`, `b' = 1`. -/
example (hEI : EI2Hyp (fun _ => (2 : ℝ))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      ∀ L : EntryLaws (fun _ => (2 : ℝ)),
        blockLaw 3 N L {w | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ N ∧ 1 ≤ j ∧ j ≤ N ∧
            |eigK (wig N (w 1)) j - quant rhoSc (3 * N) 1| ≤
              (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * ((1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
            |eigK (wig N (w 0)) i - eigK (wig N (w 1)) j| ≤
              2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - 1 / 10) * ((1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-δ₀)) :=
```

```lean
/-- The same at `D = 3`, `δ = 1/10`, `C p = 2`, `k = N` (the bulk index of block size, `N ≤ 3N`),
`b = 0`, `b' = 1`, so that the window is not only the edge one. -/
example (hEI : EI2Hyp (fun _ => (2 : ℝ))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      ∀ L : EntryLaws (fun _ => (2 : ℝ)),
        blockLaw 3 N L {w | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ N ∧ 1 ≤ j ∧ j ≤ N ∧
            |eigK (wig N (w 1)) j - quant rhoSc (3 * N) N| ≤
              (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) ∧
            |eigK (wig N (w 0)) i - eigK (wig N (w 1)) j| ≤
              2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - 1 / 10) * (N : ℝ) ^ (-(1 / 3 : ℝ))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-δ₀)) :=
```

**Everything else the paper cites is proved in the library.** The main items:

- the local laws and the rigidity, Lemma 2.9 and the local-law part of Lemma 4.4 ([stone2024randommatrixmodelquantum, Lemmas 2.9, 6.4]): `aniso_local`, `aver_local`, `rigidity`, `aver_local_outside`, `spec_inclusion`, `samefort_local`; Lemma A.4: `entprodG`, `one_loop_estimate`, `two_loop_estimate`, `entprodG_local`, `one_loop_local`, `two_loop_local`;
- the Wigner rigidity (5.12) ([erdHos2012rigidity, Theorem 2.2]): `rigidity12`;
- the cumulant expansion, Lemma 2.11 ([He:2017wm, Lemma 7.1]): `cumulant_expansion`, `llClass_cumulant_expansion`, `expansion_hp`, with the cumulants `ccum` and the bounds `ccum_entry_le`, `llClass_ccum_le`;
- the Gaussian integration by parts and the one-time laws of the flows: `gueBlocks_ibp`, `hasDerivAt_ouExpect`, `gueLaw_map_add`, `gridState_law`;
- the comparison lemmas: Lemma 3.13 ([stone2024randommatrixmodelquantum, Lemma 3.4]) `main_lemma_com_theta`, with the moment matching ([erdHos2012bulk, Lemma 6.5]) `moment_matching`; Lemma 4.3 `rescomY`; Lemma 4.2 from Lemma 4.3 ([Erds2017ADA, Section 17]) `cvtv_of_rescomY`; the free-convolution comparison ([CorrelatedBandAOP, Section 6.1]) `fc_close`;
- the deterministic facts ([lee2015edge, Lemma 4.3] and the standard properties of the free convolution): `square_root_density`, `rho_support`, `def_gamma_limits`, `rho_stieltjes`, `mSol_existsUnique`, `edge_close_to_edge_sc`, `kappa_gamma_k`;
- the linear algebra: Courant–Fischer `eigK_minmax`, the derivative of eigenvalues `eigK_line_deriv`, Ward's identity `ward_sum`, `ward_diag`.

## 6. Proof route

- **The deterministic analysis** (§2.2, Appendix A: Definition 2.7, (2.13)–(2.21), Lemmas A.1–A.3). `RBMTransitionEdge/Det/`: `Core.lean` (m and M), `Density.lean` (ρ_N, quantiles), `Edge.lean` (edges, square-root behaviour), `Block.lean` (the block structure, (2.13), (2.15), M̂), `MhatSpec.lean` and `EdgeStability.lean` (1 − M̂, (A.8)–(A.18)), `Taylor.lean`, `Shift.lean` (Lemma A.3), `Regular.lean` (Lemmas 5.1, 5.3), `QuantSpacing.lean`.
- **The local laws and the probabilistic tools** (§2.3, Lemma 2.9, Lemma 4.4, (5.12), Lemma A.4). `RBMTransitionEdge/LocalLaw/` (the class `LLClass`, the fluctuation bounds, the bootstrap, the far region, counting, rigidity, the multi-resolvent bounds), with `RBMTransitionEdge/Prob/` (cumulants, the cumulant expansion, Gaussian laws and integration by parts, the grid flows and martingales, moment matching) and `RBMTransitionEdge/Tools/` (resolvents, min–max, eigenvalue derivatives, discrete Duhamel).
- **The delocalized phase, eigenvectors** (§3, Theorem 2.1). `RBMTransitionEdge/Flow/`: `CharFlow.lean` (Lemma 3.5), `KTheta.lean`, `LargeEta*.lean` (Lemmas 3.6, 3.7), `FourthCumulant.lean` (Lemmas 3.14, 3.15), `LemFlow1.lean`–`LemFlow3.lean` and `LemFlowExp.lean` (Lemmas 3.8–3.11), `TOp.lean`, `Duhamel.lean`, `MainG.lean` (Lemma 3.12), `Comparison.lean` (Lemma 3.13), `KeyLemma.lean` (Lemma 3.3), `Endpoint.lean` and `Mix.lean` (Theorem 2.1).
- **The delocalized phase, eigenvalues** (§4, Theorem 2.2). `RBMTransitionEdge/Edge/`: `Defs.lean`, `Regular.lean`, `FcDet.lean`, `FcClose.lean`, `FcRigid.lean` and `CVtG.lean` (Lemma 4.1), `Count*.lean`, `SpecSum.lean` and `Comparison.lean` (Lemma 4.3, Lemma 4.2), `Smoothing.lean`, `Sandwich.lean`, `MixEV.lean` (Theorem 2.2).
- **The localized phase** (§5, Theorems 2.4, 2.5). `RBMTransitionEdge/Localized/`: `Pathwise.lean` ((5.16)–(5.26)), `Repulsion.lean` ((5.11)–(5.14)), `Expansion/` (the expansion of §5.3 and Lemma 5.5), `LocalLaw.lean` (Lemmas 5.2, 5.4), `QuantIncrement.lean`, `Evec.lean`, `Eval.lean`, `Reflect.lean`.
- **The statements and the main theorems.** `RBMTransitionEdge/MainDefs.lean`, `RBMTransitionEdge/Model/`, `RBMTransitionEdge/Main/`.

## 7. Not formalized

- The real symmetric case, which the paper says "can be proved in the same way with some minor changes in notations".
- The left-edge parts of Lemma 4.1 [CVtG] and Lemma 4.2 [CVtV] as statements: the library states them at the right edge, and obtains the left edge of Theorem 2.2 by reflection (§3 (a) 11).
- (A.32) [derivative_of_edge] of Lemma A.2 as a statement: the library proves (A.2) without it (§3 (b) 9).
- Remark 2.3 [rmk_only_edge] (universality in the bulk, from [stone2024randommatrixmodelquantum], and the open transition regime), Remark 2.6 beyond (2.15) (in the table as `eq_MD2`), Remark 5.6 (the Gaussian and symmetric cases of Lemma 5.5), the heuristics of §1 (including (1.1) [eq;Anderson] and (1.5) [eq:intro_delocal]), the proof ideas of §2.4 and the numerical figures: background and comments, not results.
- Lemma 5.5 is formalized in the corrected form for the signed sum (§3 (b) 20); its form for a single starting expression, whose proof covers only the signed sum, is not.

## 8. Axioms and build

The main theorems, the Palomar theorems and the theorems of §4 depend only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. To reproduce the check, build the library with `lake build` and run `lake env lean` on a scratch file outside the source tree:

```
import RBMTransitionEdge
import Solution

#print axioms RBMTransitionEdge.main_theorems
#print axioms RBMTransitionEdge.mix
#print axioms RBMTransitionEdge.mixEV
#print axioms RBMTransitionEdge.localized_evec
#print axioms RBMTransitionEdge.localized_eval
#print axioms RBMTransitionEdge.theorem_2_1
#print axioms RBMTransitionEdge.theorem_2_5
```

Each line prints `'RBMTransitionEdge.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`. The Palomar check compares `Solution.lean` with `Challenge.lean`: `lake env lean` on a file that imports `Solution.lean` checks the two proofs, and `scripts/verify-comparator.sh` runs `lake comparator` with the kernels of the Lean toolchain, as Palomar does.
