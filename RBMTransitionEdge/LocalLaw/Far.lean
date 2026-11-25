module

public import RBMTransitionEdge.LocalLaw.FarStage
public import RBMTransitionEdge.LocalLaw.NormBound

@[expose] public section

/-!
# The far region of Lemma 2.9

The averaged bound on `{4 ≤ |E| ≤ N^{δ₁}, N^{-1+τ} ≤ η ≤ 2}` along a sequence of members, and the
absence of eigenvalues of modulus `≥ 4`, for Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The far spectral domain `{4 ≤ |E| ≤ N^{δ₁}, N^{-1+τ} ≤ η ≤ 2}`. -/
def farDom (τ δ₁ : ℝ) (N : ℕ) : Set ℂ :=
  {z | 4 ≤ |z.re| ∧ |z.re| ≤ (N : ℝ) ^ δ₁ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 2}

/-! ### Stochastic domination with a change of bound -/

/-- If `ξ ≺ ζ_j` for every `j` in the sup form of Definition 2.8 [stoch_domination], `ξ' ≤ ξ`,
and for every `ε > 0` some `ζ_j` is eventually at most `N^ε ζ'`, then `ξ' ≺ ζ'`. -/
private lemma Far_precS_le {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) {U : ℕ → Type*} (ξ ξ' ζ' : ∀ N, U N → Ω N → ℝ)
    (ζ : ℕ → ∀ N, U N → Ω N → ℝ) (h : ∀ j, PrecS P ξ (ζ j))
    (hξ : ∀ N u ω, ξ' N u ω ≤ ξ N u ω)
    (hle : ∀ ε : ℝ, 0 < ε → ∃ (j : ℕ) (N₁ : ℕ), ∀ N : ℕ, N₁ ≤ N → ∀ u ω,
      ζ j N u ω ≤ (N : ℝ) ^ ε * ζ' N u ω) :
    PrecS P ξ' ζ' := by
  intro τ hτ D' hD'
  obtain ⟨j, N₁, hN₁⟩ := hle (τ / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h j (τ / 2) (by linarith) D' hD'
  refine ⟨max N₁ N₂, fun N hN u =>
    le_trans (measure_mono fun ω hω => ?_) (hN₂ N (le_trans (le_max_right _ _) hN) u)⟩
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN) u ω
  have hω' : (N : ℝ) ^ τ * ζ' N u ω < ξ' N u ω := hω
  show (N : ℝ) ^ (τ / 2) * ζ j N u ω < ξ N u ω
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have e : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by linarith)]
    ring_nf
  calc (N : ℝ) ^ (τ / 2) * ζ j N u ω ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ζ' N u ω) :=
        mul_le_mul_of_nonneg_left h1 hN0
    _ = (N : ℝ) ^ τ * ζ' N u ω := by rw [← mul_assoc, e]
    _ < ξ' N u ω := hω'
    _ ≤ ξ N u ω := hξ N u ω

/-! ### Elementary facts -/

/-- A nonempty far level has `N ≥ 1`, since `N^{δ₁} ≥ 4`. -/
private lemma Far_one_le {δ₁ : ℝ} {ℓ : ℕ → ℝ} {N : ℕ} {z : ℂ} (hz : z ∈ farLev δ₁ ℓ N) :
    (1 : ℝ) ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exfalso
    have h1 : (4 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ δ₁ := hz.1.trans hz.2.1
    rw [Nat.cast_zero] at h1
    have := Real.zero_rpow_le_one δ₁
    linarith
  · exact_mod_cast hN

/-- On a far level with `δ₁ ≤ 1`: `N ≥ 4`, since `4 ≤ N^{δ₁} ≤ N`. -/
private lemma Far_four_le {δ₁ : ℝ} {ℓ : ℕ → ℝ} {N : ℕ} {z : ℂ} (hz : z ∈ farLev δ₁ ℓ N)
    (hδ1 : δ₁ ≤ 1) : (4 : ℝ) ≤ N := by
  have hN := Far_one_le hz
  have h1 : (N : ℝ) ^ δ₁ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hδ1
  rw [Real.rpow_one] at h1
  linarith [hz.1.trans hz.2.1]

/-- `N^a ≥ C` for all large `N`, when `a > 0`. -/
private lemma Far_ev (C a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop C)

/-- `x ≤ y` from `x² ≤ y²` for `y ≥ 0`. -/
private lemma Far_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hcon
  have hcon := lt_of_not_ge hcon
  nlinarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private lemma Far_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x)
    (Real.sqrt_nonneg y)]

/-- The operator norm of a difference. -/
private lemma Far_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma Far_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (x y : ι → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤ opNorm T := by
  have e : star x ⬝ᵥ (T *ᵥ y) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 y)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hx
  have hy' : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hy
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 y) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ ≤ opNorm T * 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by unfold opNorm; gcongr)
  rw [e, h1]
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (opNorm T * 1) := mul_le_mul hx' h2 (norm_nonneg _) zero_le_one
    _ = opNorm T := by ring

/-- The normalized trace of a finite sum is the sum of the normalized traces. -/
private lemma Far_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (P : κ → Matrix ι ι ℂ) : ntr (∑ b ∈ s, P b) = ∑ b ∈ s, ntr (P b) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- The normalized trace of a difference. -/
private lemma Far_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- `|⟨B⟩| ≤ |D⟨E_a B⟩|_∞` for `D ≥ 1`, since `⟨B⟩ = D⁻¹ Σ_a D⟨E_a B⟩`. -/
private lemma Far_ntr_le_blockTr (D N : ℕ) (hD : 1 ≤ D)
    (B : Matrix (Idx D N) (Idx D N) ℂ) : ‖ntr B‖ ≤ ‖blockTr D N B‖ := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hsumE : ∑ a : Fin D, Ea D N a = 1 := by
    ext p q
    simp [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have e : ntr B = (D : ℂ)⁻¹ * ∑ a, blockTr D N B a := by
    unfold blockTr
    rw [← Finset.mul_sum, ← Far_ntr_sum, ← Finset.sum_mul, hsumE, Matrix.one_mul]
    field_simp
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ a, blockTr D N B a‖ ≤ D * ‖blockTr D N B‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖blockTr D N B a‖ ≤ ∑ _a : Fin D, ‖blockTr D N B‖ :=
          Finset.sum_le_sum fun a _ => norm_le_pi_norm (blockTr D N B) a
      _ = D * ‖blockTr D N B‖ := by simp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  calc (D : ℝ)⁻¹ * ‖∑ a, blockTr D N B a‖ ≤ (D : ℝ)⁻¹ * (D * ‖blockTr D N B‖) := by gcongr
    _ = ‖blockTr D N B‖ := by field_simp

/-- `|⟨B⟩| ≤ ‖B‖` for `D ≥ 1`. -/
private lemma Far_ntr_le_opNorm (D N : ℕ) (hD : 1 ≤ D) (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖ntr B‖ ≤ opNorm B :=
  (Far_ntr_le_blockTr D N hD B).trans (blockTr_norm_le D N B)

/-- `M(z) = MSol(z)` for `Im z > 0`. -/
private lemma Far_MExt_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (z : ℂ) (hz : 0 < z.im) : MExt Λ z = MSol Λ z := by
  simp [MExt, MSol, mExt, hz]

/-- Along a sequence of members, `‖Λ_N‖ ≤ 1/10` and `N ≥ 1` for all large `N`. -/
private lemma Far_lam_small {D : ℕ} {δA : ℝ} {C : ℕ → ℝ} {θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hseq : LLSeq D δA C θ μ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 : ℝ) ≤ N ∧ opNorm (lam D N (A N)) ≤ 1 / 10 := by
  obtain ⟨NΛ, hNΛ⟩ := Far_ev 20 δA hseq.pos
  refine ⟨max NΛ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 := opNorm_lam_le D N (A N)
  have h2 := hseq.small N
  have h3 : (20 : ℝ) ≤ (N : ℝ) ^ δA := hNΛ N (le_trans (le_max_left _ _) hN)
  have h4 : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hN0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  exact ⟨hN1, by linarith⟩

/-- A union bound over `k ≤ N^m` events of probability `≤ N^{-(D'+m)}`. -/
private lemma Far_count (N k m : ℕ) (hN : (1 : ℝ) ≤ N) (hk : (k : ℝ) ≤ (N : ℝ) ^ m)
    (D' : ℝ) : (k : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + m))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN0 : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (N : ℝ) ^ (-(D' + m)) = (N : ℝ) ^ (-D') * ((N : ℝ) ^ m)⁻¹ := by
    rw [show -(D' + (m : ℝ)) = -D' + -(m : ℝ) by ring, Real.rpow_add hN0,
      Real.rpow_neg hN0.le (m : ℝ), Real.rpow_natCast]
  rw [e]
  have hp : 0 < (N : ℝ) ^ m := by positivity
  have hq : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
  calc (k : ℝ) * ((N : ℝ) ^ (-D') * ((N : ℝ) ^ m)⁻¹)
      = (N : ℝ) ^ (-D') * ((k : ℝ) / (N : ℝ) ^ m) := by ring
    _ ≤ (N : ℝ) ^ (-D') * 1 := mul_le_mul_of_nonneg_left ((div_le_one hp).mpr hk) hq
    _ = (N : ℝ) ^ (-D') := mul_one _

/-- The number `J + 1` of dyadic heights between `N⁻¹` and `2` is `≤ N^δ/10` for large `N`: if
`2^J ≤ 2N` then `10 (J + 1) ≤ N^δ`. -/
private lemma Far_log (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ J : ℕ, (2 : ℝ) ^ J ≤ 2 * N →
      10 * ((J : ℝ) + 1) ≤ (N : ℝ) ^ δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 20 + 20 / (δ * Real.log 2) with hc
  obtain ⟨N₁, hN₁⟩ := Far_ev c (δ / 2) (by positivity)
  refine ⟨max N₁ 1, fun N hN J hJ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hcN := hN₁ N (le_trans (le_max_left _ _) hN)
  have hlogJ : (J : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log N := by
    have h1 := Real.log_le_log (by positivity) hJ
    rw [Real.log_pow, Real.log_mul (by norm_num) hN0.ne'] at h1
    exact h1
  have hlogN : Real.log N ≤ (N : ℝ) ^ (δ / 2) / (δ / 2) := Real.log_le_rpow_div hN0.le (by positivity)
  have hw1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow hN1 (by positivity)
  have hsq : (N : ℝ) ^ δ = (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  have hcl : c * Real.log 2 = 20 * Real.log 2 + 20 / δ := by
    rw [hc]
    field_simp
  have key : 10 * ((J : ℝ) + 1) * Real.log 2 ≤ c * (N : ℝ) ^ (δ / 2) * Real.log 2 := by
    have h2 : 10 * Real.log N ≤ 20 / δ * (N : ℝ) ^ (δ / 2) := by
      have : (N : ℝ) ^ (δ / 2) / (δ / 2) = 2 / δ * (N : ℝ) ^ (δ / 2) := by field_simp
      rw [this] at hlogN
      have := mul_le_mul_of_nonneg_left hlogN (by norm_num : (0 : ℝ) ≤ 10)
      have e : 10 * (2 / δ * (N : ℝ) ^ (δ / 2)) = 20 / δ * (N : ℝ) ^ (δ / 2) := by ring
      linarith
    have h3 : c * (N : ℝ) ^ (δ / 2) * Real.log 2 =
        (20 * Real.log 2 + 20 / δ) * (N : ℝ) ^ (δ / 2) := by
      rw [← hcl]
      ring
    rw [h3]
    have h4 : 0 ≤ 20 / δ := by positivity
    nlinarith
  have key' : 10 * ((J : ℝ) + 1) ≤ c * (N : ℝ) ^ (δ / 2) := le_of_mul_le_mul_right key hl2
  rw [hsq]
  exact key'.trans (mul_le_mul_of_nonneg_right hcN (by positivity))

/-! ### The levels of the continuity argument -/

/-- The lower cut-off `max(2 N^{-k δ₁}, N^{-1+τ})` of the `k`-th level. -/
private def Far_lev (τ δ₁ : ℝ) (k N : ℕ) : ℝ :=
  max (2 * (N : ℝ) ^ (-((k : ℝ) * δ₁))) ((N : ℝ) ^ (-1 + τ))

/-- The a priori bound on level `k + 1`: `1` above the cut-off of level `k`, and `N^{2δ₁}`
below it. -/
private def Far_phi0 (τ δ₁ : ℝ) (k N : ℕ) (z : ℂ) : ℝ :=
  if Far_lev τ δ₁ k N ≤ z.im then 1 else (N : ℝ) ^ (2 * δ₁)

/-- `0 < ℓ_k ≤ 2` for `N ≥ 1`, `τ ≤ 1`, `δ₁ ≥ 0`, and `ℓ_k ≥ N⁻¹` for `τ ≥ 0`. -/
private lemma Far_lev_bounds (τ δ₁ : ℝ) (k N : ℕ) (hN : (1 : ℝ) ≤ N) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ₁) :
    ((N : ℝ))⁻¹ ≤ Far_lev τ δ₁ k N ∧ 0 < Far_lev τ δ₁ k N ∧ Far_lev τ δ₁ k N ≤ 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 : ((N : ℝ))⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h2 : (N : ℝ) ^ (-1 + τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have h3 : (N : ℝ) ^ (-((k : ℝ) * δ₁)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by have := Nat.cast_nonneg (α := ℝ) k; nlinarith)
  have h4 : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hN0
  refine ⟨h1.trans (le_max_right _ _), lt_of_lt_of_le h4 (h1.trans (le_max_right _ _)), ?_⟩
  exact max_le (by linarith) (by linarith)

/-- `ℓ_k ≤ N^{δ₁} ℓ_{k+1}` for `N ≥ 1`, `δ₁ ≥ 0`. -/
private lemma Far_lev_ratio (τ δ₁ : ℝ) (k N : ℕ) (hN : (1 : ℝ) ≤ N) (hδ : 0 ≤ δ₁) :
    Far_lev τ δ₁ k N ≤ (N : ℝ) ^ δ₁ * Far_lev τ δ₁ (k + 1) N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hd : (1 : ℝ) ≤ (N : ℝ) ^ δ₁ := Real.one_le_rpow hN hδ
  have e : (N : ℝ) ^ δ₁ * (2 * (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * δ₁))) =
      2 * (N : ℝ) ^ (-((k : ℝ) * δ₁)) := by
    rw [mul_left_comm, ← Real.rpow_add hN0]
    push_cast
    ring_nf
  unfold Far_lev
  refine max_le ?_ ?_
  · rw [← e]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  · have h0 : 0 ≤ (N : ℝ) ^ (-1 + τ) := Real.rpow_nonneg hN0.le _
    calc (N : ℝ) ^ (-1 + τ) ≤ (N : ℝ) ^ δ₁ * (N : ℝ) ^ (-1 + τ) := le_mul_of_one_le_left h0 hd
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-- The top level: `ℓ_0 ≥ 2` for `N ≥ 1`. -/
private lemma Far_lev_zero (τ δ₁ : ℝ) (N : ℕ) : 2 ≤ Far_lev τ δ₁ 0 N := by
  unfold Far_lev
  refine le_trans (le_of_eq ?_) (le_max_left _ _)
  simp

/-- The far domain lies in the level `k = ⌈(1 - τ)/δ₁⌉ + 1`: there `2 N^{-kδ₁} ≤ N^{-1+τ}`,
since `N^{δ₁} ≥ 4` on a nonempty far domain. -/
private lemma Far_lev_top (τ δ₁ : ℝ) (hδ : 0 < δ₁) (N : ℕ) (z : ℂ) (hz : z ∈ farDom τ δ₁ N) :
    z ∈ farLev δ₁ (Far_lev τ δ₁ (⌈(1 - τ) / δ₁⌉₊ + 1)) N := by
  have hz' : z ∈ farLev δ₁ (fun N => (N : ℝ) ^ (-1 + τ)) N := hz
  have hN := Far_one_le hz'
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨h4, hE, hη, h2⟩ := hz
  refine ⟨h4, hE, max_le ?_ hη, h2⟩
  have hc := Nat.le_ceil ((1 - τ) / δ₁)
  have hk : 1 - τ ≤ (⌈(1 - τ) / δ₁⌉₊ : ℝ) * δ₁ := by
    rw [div_le_iff₀ hδ] at hc
    exact hc
  have hd : 2 ≤ (N : ℝ) ^ δ₁ := by linarith
  have e : (N : ℝ) ^ δ₁ * (N : ℝ) ^ (-(((⌈(1 - τ) / δ₁⌉₊ + 1 : ℕ) : ℝ) * δ₁)) =
      (N : ℝ) ^ (-((⌈(1 - τ) / δ₁⌉₊ : ℝ) * δ₁)) := by
    rw [← Real.rpow_add hN0]
    push_cast
    ring_nf
  have h5 : (N : ℝ) ^ (-((⌈(1 - τ) / δ₁⌉₊ : ℝ) * δ₁)) ≤ (N : ℝ) ^ (-1 + τ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h6 : 0 ≤ (N : ℝ) ^ (-(((⌈(1 - τ) / δ₁⌉₊ + 1 : ℕ) : ℝ) * δ₁)) := Real.rpow_nonneg hN0.le _
  calc 2 * (N : ℝ) ^ (-(((⌈(1 - τ) / δ₁⌉₊ + 1 : ℕ) : ℝ) * δ₁))
      ≤ (N : ℝ) ^ δ₁ * (N : ℝ) ^ (-(((⌈(1 - τ) / δ₁⌉₊ + 1 : ℕ) : ℝ) * δ₁)) :=
        mul_le_mul_of_nonneg_right hd h6
    _ = _ := e
    _ ≤ _ := h5.trans hη

/-- The top level `η = 2`: `|s^*(G - M)t| ≤ ‖G‖ + ‖M‖ ≤ 1/2 + 10/29 < 1` for Hermitian arrays,
so the a priori bound `1` holds there. -/
private lemma Far_base {D : ℕ} {δA : ℝ} {C : ℕ → ℝ} {θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hseq : LLSeq D δA C θ μ A) (τ δ₁ : ℝ) :
    aprioriLL D μ A (farLev δ₁ (Far_lev τ δ₁ 0)) (fun _ _ => 1) := by
  intro τ'' hτ'' D'' hD''
  obtain ⟨NΛ, hNΛ⟩ := Far_lam_small hseq
  refine ⟨NΛ, fun N hN u => ?_⟩
  obtain ⟨⟨z, hz⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ := u
  obtain ⟨hN1, hΛ1⟩ := hNΛ N hN
  have hz2 : 2 ≤ z.im := (Far_lev_zero τ δ₁ N).trans hz.2.2.1
  have hz0 : 0 < z.im := by linarith
  have hD := hseq.one_le_D
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by exact_mod_cast hN1⟩)⟩
  have hΛh := lam_isHermitian D N (A N)
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
  refine le_trans (measure_mono_null (t := {h | ¬ (Matrix.of h).IsHermitian}) ?_ hnull).le
    bot_le
  intro h hh hherm
  have hG : opNorm (res (Matrix.of h + lam D N (A N)) z) ≤ 1 / 2 := by
    refine (opNorm_res_le _ (hherm.add hΛh) _ hz0).trans ?_
    rw [one_div]
    exact inv_anti₀ (by norm_num) hz2
  have hM := (MExt_far (lam D N (A N)) hΛh hΛ1 z hz0 hz.1).2.1
  have hform := Far_form_le (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) s t
    hs.le ht.le
  have hsub := Far_opNorm_sub_le (res (Matrix.of h + lam D N (A N)) z)
    (MExt (lam D N (A N)) z)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ τ'' := Real.one_le_rpow hN1 hτ''.le
  have hh' : (N : ℝ) ^ τ'' * 1 < ‖star s ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
      MExt (lam D N (A N)) z) *ᵥ t)‖ := hh
  linarith

/-- The arithmetic of the transfer: with `d ≥ 10 (J + 1)`, `d, q ≥ 1`,
`d (1 + 4 (J + 1)(q + 1)) + 1 ≤ d² q`. -/
private lemma Far_transfer_arith (d q : ℝ) (J : ℕ) (hd1 : 1 ≤ d) (hq1 : 1 ≤ q)
    (hJlog : 10 * ((J : ℝ) + 1) ≤ d) :
    d * (1 + 4 * ((J : ℝ) + 1) * (q + 1)) + 1 ≤ d * d * q := by
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hJq : 1 ≤ ((J : ℝ) + 1) * q := by nlinarith
  have hB : 1 + 4 * ((J : ℝ) + 1) * (q + 1) ≤ 9 * (((J : ℝ) + 1) * q) := by nlinarith
  have h1 : d * (1 + 4 * ((J : ℝ) + 1) * (q + 1)) ≤ d * (9 * (((J : ℝ) + 1) * q)) :=
    mul_le_mul_of_nonneg_left hB (by linarith)
  have h2 : 1 ≤ d * (((J : ℝ) + 1) * q) := by nlinarith
  have h3 : d * (10 * (((J : ℝ) + 1) * q)) ≤ d * (d * q) := by
    have : 10 * (((J : ℝ) + 1) * q) ≤ d * q := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by linarith)
  nlinarith

/-- The transfer from level `k` to level `k + 1` (`res_transfer`): from the a priori bound `1` on
level `k`, the bound `N^{2δ₁}` holds on the part of level `k + 1` below the cut-off of level `k`.
There `|s^* G(E + iη') t| ≤ (ℓ_k/η') (A_s A_t)^{1/2}` with `ℓ_k/η' ≤ N^{δ₁}`, and
`|A_s| ≤ 1 + 4 (J + 1)(N^{ε} + 1)` with `J + 1 ≤ N^{δ₁}/10` dyadic heights. -/
private lemma Far_transfer {D : ℕ} {δA : ℝ} {C : ℕ → ℝ} {θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hseq : LLSeq D δA C θ μ A) {τ δ₁ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ₁)
    (hδ1 : δ₁ ≤ 1) (k : ℕ)
    (hP : aprioriLL D μ A (farLev δ₁ (Far_lev τ δ₁ k)) (fun _ _ => 1)) :
    aprioriLL D μ A (farLev δ₁ (Far_lev τ δ₁ (k + 1))) (Far_phi0 τ δ₁ k) := by
  intro τ'' hτ'' D'' hD''
  obtain ⟨N₁, hN₁⟩ := hP (τ'' / 2) (by linarith) (D'' + 1) (by linarith)
  obtain ⟨NΛ, hNΛ⟩ := Far_lam_small hseq
  obtain ⟨N₃, hN₃⟩ := Far_log δ₁ hδ
  refine ⟨max (max N₁ NΛ) N₃, fun N hN u => ?_⟩
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNΛ' : NΛ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3' : N₃ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨⟨z, hz⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ := u
  obtain ⟨hN1, hΛ1⟩ := hNΛ N hNΛ'
  have hN0 : (0 : ℝ) < N := by linarith
  have hD := hseq.one_le_D
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by exact_mod_cast hN1⟩)⟩
  have hΛh := lam_isHermitian D N (A N)
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
  obtain ⟨hE4, hEN, hℓη, hη2⟩ := hz
  obtain ⟨hlow, -, -⟩ := Far_lev_bounds τ δ₁ (k + 1) N hN1 hτ.le hτ1 hδ.le
  have hzim0 : 0 < z.im := lt_of_lt_of_le (inv_pos.mpr hN0) (hlow.trans hℓη)
  have hτ2 : (N : ℝ) ^ (τ'' / 2) ≤ (N : ℝ) ^ τ'' :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hτ21 : (1 : ℝ) ≤ (N : ℝ) ^ (τ'' / 2) := Real.one_le_rpow hN1 (by positivity)
  have hD2 : ENNReal.ofReal ((N : ℝ) ^ (-(D'' + 1))) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'')) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  show μ N {h | (N : ℝ) ^ τ'' * Far_phi0 τ δ₁ k N z < ‖star s ⬝ᵥ
    ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ t)‖} ≤ _
  by_cases hη : Far_lev τ δ₁ k N ≤ z.im
  · have hφ : Far_phi0 τ δ₁ k N z = 1 := by simp [Far_phi0, hη]
    have hzk : z ∈ farLev δ₁ (Far_lev τ δ₁ k) N := ⟨hE4, hEN, hη, hη2⟩
    refine le_trans (measure_mono fun h hh => ?_)
      ((hN₁ N hN1' (⟨z, hzk⟩, ⟨s, hs⟩, ⟨t, ht⟩)).trans hD2)
    have hh' : (N : ℝ) ^ τ'' * Far_phi0 τ δ₁ k N z < ‖star s ⬝ᵥ
        ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ t)‖ := hh
    rw [hφ] at hh'
    show (N : ℝ) ^ (τ'' / 2) * 1 < ‖star s ⬝ᵥ
      ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ t)‖
    linarith
  -- below the cut-off of level `k`: the transfer
  have hφ : Far_phi0 τ δ₁ k N z = (N : ℝ) ^ (2 * δ₁) := by simp [Far_phi0, hη]
  obtain ⟨hℓlow, hℓ0, hℓ2⟩ := Far_lev_bounds τ δ₁ k N hN1 hτ.le hτ1 hδ.le
  set ℓ := Far_lev τ δ₁ k N with hℓdef
  have hex : ∃ J : ℕ, 1 ≤ 2 ^ J * ℓ := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (ℓ⁻¹) (by norm_num : (1 : ℝ) < 2)
    refine ⟨J, ?_⟩
    have := mul_le_mul_of_nonneg_right hJ.le hℓ0.le
    rwa [inv_mul_cancel₀ hℓ0.ne'] at this
  set J := Nat.find hex with hJdef
  have hJ : 1 ≤ 2 ^ J * ℓ := Nat.find_spec hex
  have hJ2 : 2 ^ J * ℓ ≤ 2 ∧ (2 : ℝ) ^ J ≤ 2 * N := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [h0]
      simp only [pow_zero, one_mul]
      exact ⟨hℓ2, by linarith⟩
    · have hmin := Nat.find_min hex (show J - 1 < J by omega)
      have hmin' : 2 ^ (J - 1) * ℓ < 1 := lt_of_not_ge hmin
      have e : (2 : ℝ) ^ J = 2 * 2 ^ (J - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hNℓ : 1 ≤ (N : ℝ) * ℓ := by
        have := mul_le_mul_of_nonneg_left hℓlow hN0.le
        rwa [mul_inv_cancel₀ hN0.ne'] at this
      constructor
      · rw [e]
        linarith
      · rw [e]
        have h1 : (2 : ℝ) ^ (J - 1) * ℓ * N < N := by nlinarith
        have h2 : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ (J - 1) * ℓ * N := by
          have := mul_le_mul_of_nonneg_left hNℓ (by positivity : (0 : ℝ) ≤ 2 ^ (J - 1))
          nlinarith
        linarith
  have hJlog := hN₃ N hN3' J hJ2.2
  set E := z.re with hEdef
  set w : ℕ → ℂ := fun j => (E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I with hwdef
  have hwim : ∀ j, (w j).im = 2 ^ j * ℓ := fun j => by
    simp only [hwdef, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hwre : ∀ j, (w j).re = E := fun j => by
    simp only [hwdef, Complex.add_re, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hw : ∀ j ≤ J, w j ∈ farLev δ₁ (Far_lev τ δ₁ k) N := by
    intro j hj
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
    refine ⟨by rw [hwre]; exact hE4, by rw [hwre]; exact hEN, ?_, ?_⟩
    · rw [hwim]
      nlinarith
    · rw [hwim]
      nlinarith
  have hwim0 : ∀ j, 0 < (w j).im := fun j => by rw [hwim]; positivity
  set Es : Fin (J + 1) → Set (Idx D N → Idx D N → ℂ) := fun j =>
    {h | (N : ℝ) ^ (τ'' / 2) * 1 < ‖star s ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
      MExt (lam D N (A N)) (w j)) *ᵥ s)‖} with hEsdef
  set Et : Fin (J + 1) → Set (Idx D N → Idx D N → ℂ) := fun j =>
    {h | (N : ℝ) ^ (τ'' / 2) * 1 < ‖star t ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
      MExt (lam D N (A N)) (w j)) *ᵥ t)‖} with hEtdef
  have hEs : ∀ j, μ N (Es j) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D'' + 1))) := fun j =>
    hN₁ N hN1' (⟨w j, hw j (Nat.lt_succ_iff.mp j.isLt)⟩, ⟨s, hs⟩, ⟨s, hs⟩)
  have hEt : ∀ j, μ N (Et j) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D'' + 1))) := fun j =>
    hN₁ N hN1' (⟨w j, hw j (Nat.lt_succ_iff.mp j.isLt)⟩, ⟨t, ht⟩, ⟨t, ht⟩)
  refine le_trans (measure_mono (t := {h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ j, (Es j ∪ Et j))
    ?_) ?_
  · intro h hh
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq, not_not,
      hEsdef, hEtdef, not_lt] at hcon
    obtain ⟨hHerm, hgood⟩ := hcon
    have hX : (Matrix.of h + lam D N (A N)).IsHermitian := hHerm.add hΛh
    -- the bounds at the dyadic heights
    have hdy : ∀ (v : Idx D N → ℂ), ∑ i, ‖v i‖ ^ 2 = 1 → (∀ j : Fin (J + 1),
        ‖star v ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
          MExt (lam D N (A N)) (w j)) *ᵥ v)‖ ≤ (N : ℝ) ^ (τ'' / 2) * 1) →
        |1 + 4 * ∑ j ∈ Finset.range (J + 1),
          (star v ⬝ᵥ (res (Matrix.of h + lam D N (A N))
            ((E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I) *ᵥ v)).im| ≤
          1 + 4 * ((J : ℝ) + 1) * ((N : ℝ) ^ (τ'' / 2) + 1) := by
      intro v hv hvb
      have hterm : ∀ j ∈ Finset.range (J + 1),
          |(star v ⬝ᵥ (res (Matrix.of h + lam D N (A N))
            ((E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I) *ᵥ v)).im| ≤
            (N : ℝ) ^ (τ'' / 2) + 1 := by
        intro j hj
        have hj' := hvb ⟨j, Finset.mem_range.mp hj⟩
        show |(star v ⬝ᵥ (res (Matrix.of h + lam D N (A N)) (w j) *ᵥ v)).im| ≤ _
        have hM := (MExt_far (lam D N (A N)) hΛh hΛ1 (w j) (hwim0 j)
          (by rw [hwre]; exact hE4)).2.1
        have hMf := Far_form_le (MExt (lam D N (A N)) (w j)) v v hv.le hv.le
        have e : star v ⬝ᵥ (res (Matrix.of h + lam D N (A N)) (w j) *ᵥ v) =
            star v ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
              MExt (lam D N (A N)) (w j)) *ᵥ v) +
            star v ⬝ᵥ (MExt (lam D N (A N)) (w j) *ᵥ v) := by
          rw [Matrix.sub_mulVec, dotProduct_sub]
          ring
        have h1 := Complex.abs_im_le_norm
          (star v ⬝ᵥ (res (Matrix.of h + lam D N (A N)) (w j) *ᵥ v))
        have h2 := norm_add_le (star v ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
              MExt (lam D N (A N)) (w j)) *ᵥ v)) (star v ⬝ᵥ (MExt (lam D N (A N)) (w j) *ᵥ v))
        rw [← e] at h2
        have hj'' : ‖star v ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) (w j) -
            MExt (lam D N (A N)) (w j)) *ᵥ v)‖ ≤ (N : ℝ) ^ (τ'' / 2) := by
          have := hj'
          simp only [mul_one] at this
          exact this
        linarith
      have hsum : |∑ j ∈ Finset.range (J + 1),
          (star v ⬝ᵥ (res (Matrix.of h + lam D N (A N))
            ((E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I) *ᵥ v)).im| ≤
          ((J : ℝ) + 1) * ((N : ℝ) ^ (τ'' / 2) + 1) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      have := abs_add_le (1 : ℝ) (4 * ∑ j ∈ Finset.range (J + 1),
          (star v ⬝ᵥ (res (Matrix.of h + lam D N (A N))
            ((E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I) *ᵥ v)).im)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_one] at this
      linarith
    have hAs := hdy s hs fun j => hgood j |>.1
    have hAt := hdy t ht fun j => hgood j |>.2
    set B : ℝ := 1 + 4 * ((J : ℝ) + 1) * ((N : ℝ) ^ (τ'' / 2) + 1) with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hT := res_transfer (Matrix.of h + lam D N (A N)) hX s t hs ht E ℓ z.im hzim0
      (le_of_lt (lt_of_not_ge hη)) J hJ
    rw [Complex.re_add_im] at hT
    have hsq : Real.sqrt
        ((1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star s ⬝ᵥ (res (Matrix.of h + lam D N (A N))
              ((E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I) *ᵥ s)).im) *
          (1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star t ⬝ᵥ (res (Matrix.of h + lam D N (A N))
              ((E : ℂ) + ((2 ^ j * ℓ : ℝ) : ℂ) * Complex.I) *ᵥ t)).im)) ≤ B := by
      rw [Real.sqrt_le_left hB0]
      refine (le_abs_self _).trans ?_
      rw [abs_mul, sq]
      exact mul_le_mul hAs hAt (abs_nonneg _) hB0
    have hratio : ℓ / z.im ≤ (N : ℝ) ^ δ₁ := by
      rw [div_le_iff₀ hzim0]
      exact (Far_lev_ratio τ δ₁ k N hN1 hδ.le).trans
        (mul_le_mul_of_nonneg_left hℓη (Real.rpow_nonneg hN0.le _))
    have hG : ‖star s ⬝ᵥ (res (Matrix.of h + lam D N (A N)) z *ᵥ t)‖ ≤ (N : ℝ) ^ δ₁ * B :=
      hT.trans (mul_le_mul hratio hsq (Real.sqrt_nonneg _) (Real.rpow_nonneg hN0.le _))
    have hMz := (MExt_far (lam D N (A N)) hΛh hΛ1 z hzim0 hE4).2.1
    have hMf := Far_form_le (MExt (lam D N (A N)) z) s t hs.le ht.le
    have e : star s ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ t) =
        star s ⬝ᵥ (res (Matrix.of h + lam D N (A N)) z *ᵥ t) -
          star s ⬝ᵥ (MExt (lam D N (A N)) z *ᵥ t) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    have hfin : ‖star s ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ
        t)‖ ≤ (N : ℝ) ^ δ₁ * B + 1 := by
      rw [e]
      have := norm_sub_le (star s ⬝ᵥ (res (Matrix.of h + lam D N (A N)) z *ᵥ t))
        (star s ⬝ᵥ (MExt (lam D N (A N)) z *ᵥ t))
      linarith
    have hh' : (N : ℝ) ^ τ'' * Far_phi0 τ δ₁ k N z < ‖star s ⬝ᵥ
        ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ t)‖ := hh
    rw [hφ] at hh'
    -- `N^{δ₁} B + 1 ≤ N^{2δ₁} N^{τ''/2} ≤ N^{τ''} N^{2δ₁}`
    have hd2 : (N : ℝ) ^ (2 * δ₁) = (N : ℝ) ^ δ₁ * (N : ℝ) ^ δ₁ := by
      rw [← Real.rpow_add hN0]
      ring_nf
    have hfin2 := Far_transfer_arith ((N : ℝ) ^ δ₁) ((N : ℝ) ^ (τ'' / 2)) J
      (Real.one_le_rpow hN1 hδ.le) hτ21 hJlog
    rw [hd2] at hh'
    have h4 : (N : ℝ) ^ δ₁ * (N : ℝ) ^ δ₁ * (N : ℝ) ^ (τ'' / 2) ≤
        (N : ℝ) ^ τ'' * ((N : ℝ) ^ δ₁ * (N : ℝ) ^ δ₁) := by
      rw [mul_comm ((N : ℝ) ^ τ'')]
      exact mul_le_mul_of_nonneg_left hτ2 (by positivity)
    linarith
  · have hcard : (((2 * (J + 1) : ℕ)) : ℝ) ≤ (N : ℝ) ^ (1 : ℕ) := by
      push_cast
      have : (N : ℝ) ^ δ₁ ≤ N := by
        have := Real.rpow_le_rpow_of_exponent_le hN1 hδ1
        rwa [Real.rpow_one] at this
      linarith
    calc μ N ({h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ j, (Es j ∪ Et j))
        ≤ μ N {h | ¬ (Matrix.of h).IsHermitian} + μ N (⋃ j, (Es j ∪ Et j)) :=
          measure_union_le _ _
      _ ≤ 0 + ∑ j : Fin (J + 1), (ENNReal.ofReal ((N : ℝ) ^ (-(D'' + 1))) +
            ENNReal.ofReal ((N : ℝ) ^ (-(D'' + 1)))) := by
          refine add_le_add (le_of_eq hnull) ((measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans (add_le_add (hEs j) (hEt j))))
      _ = (((2 * (J + 1) : ℕ)) : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D'' + ((1 : ℕ) : ℝ)))) := by
          rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'')) := Far_count N _ 1 hN1 hcard D''

/-! ### One step of the continuity argument on a level -/

/-- `ψ_F ≥ 0`. -/
private lemma Far_psiFar_nonneg (N : ℕ) (z : ℂ) (φ : ℝ) (hz : 0 < z.im) :
    0 ≤ psiFar N z φ := by
  unfold psiFar
  have : 0 ≤ 1 / ((N : ℝ) * z.im) := by
    have := Nat.cast_nonneg (α := ℝ) N
    positivity
  exact add_nonneg (Real.sqrt_nonneg _) this

/-- The size of the bound far from the spectrum: for `N ≥ 1`, `0 ≤ τ ≤ 1`, `0 ≤ δ₁`, `k ≥ 0`
with `(k + 14) δ₁ ≤ τ/2`, `η ≥ N^{-1+τ}` and `0 ≤ φ ≤ N^{2δ₁}`:
`N^{kδ₁} (1 + φ)⁶ ψ_F² ≤ 384 N^{-τ/2}`. -/
private lemma Far_bound (N : ℕ) (hN : (1 : ℝ) ≤ N) (τ δ₁ k : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hδ₁ : 0 ≤ δ₁) (hk : (k + 14) * δ₁ ≤ τ / 2) (z : ℂ) (hη : (N : ℝ) ^ (-1 + τ) ≤ z.im)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ : φ ≤ (N : ℝ) ^ (2 * δ₁)) :
    (N : ℝ) ^ (k * δ₁) * (1 + φ) ^ 6 * psiFar N z φ ^ 2 ≤ 384 * (N : ℝ) ^ (-τ / 2) := by
  have hN0 : (0 : ℝ) < N := by linarith
  set u : ℝ := (N : ℝ) ^ δ₁ with hu
  set v : ℝ := (N : ℝ) ^ (-τ) with hv
  have hu1 : 1 ≤ u := Real.one_le_rpow hN hδ₁
  have hv0 : 0 < v := Real.rpow_pos_of_pos hN0 _
  have hv1 : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hu2 : (N : ℝ) ^ (2 * δ₁) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    ring_nf
  have hNη : 1 / ((N : ℝ) * z.im) ≤ v := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = v⁻¹ := by
      rw [hv, ← Real.rpow_neg hN0.le, neg_neg]
      conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hN0]
      ring_nf
    have h2 : v⁻¹ ≤ (N : ℝ) * z.im := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_left hη hN0.le
    rw [one_div]
    calc ((N : ℝ) * z.im)⁻¹ ≤ (v⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hv0) h2
      _ = v := inv_inv v
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hη
  have hd0 : 0 < (N : ℝ) * z.im := mul_pos hN0 hzim
  have hN1 : 1 / (N : ℝ) ≤ v := by
    rw [hv, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hφη : φ / ((N : ℝ) * z.im) ≤ u ^ 2 * v := by
    rw [div_eq_mul_one_div]
    rw [hu2] at hφ
    exact mul_le_mul hφ hNη (by positivity) (by positivity)
  set X : ℝ := 1 / (N : ℝ) + φ / ((N : ℝ) * z.im) with hX
  set Y : ℝ := 1 / ((N : ℝ) * z.im) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hpsi : psiFar N z φ ^ 2 ≤ 6 * u ^ 2 * v := by
    have e : psiFar N z φ = Real.sqrt X + Y := rfl
    rw [e]
    have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
    have h1 : (Real.sqrt X + Y) ^ 2 ≤ 2 * X + 2 * Y ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt X - Y)]
    have h2 : Y ^ 2 ≤ v := by nlinarith
    have hu2' : 1 ≤ u ^ 2 := by nlinarith
    nlinarith
  have hφ6 : (1 + φ) ^ 6 ≤ 64 * u ^ 12 := by
    rw [hu2] at hφ
    have h1 : 1 + φ ≤ 2 * u ^ 2 := by nlinarith
    calc (1 + φ) ^ 6 ≤ (2 * u ^ 2) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
      _ = 64 * u ^ 12 := by ring
  have hpow : (N : ℝ) ^ (k * δ₁) * u ^ 14 * v ≤ (N : ℝ) ^ (-τ / 2) := by
    have e : (N : ℝ) ^ (k * δ₁) * u ^ 14 * v = (N : ℝ) ^ ((k + 14) * δ₁ - τ) := by
      rw [hu, hv, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      ring_nf
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hNk : 0 ≤ (N : ℝ) ^ (k * δ₁) := Real.rpow_nonneg hN0.le _
  calc (N : ℝ) ^ (k * δ₁) * (1 + φ) ^ 6 * psiFar N z φ ^ 2
      ≤ (N : ℝ) ^ (k * δ₁) * (64 * u ^ 12) * (6 * u ^ 2 * v) := by
        gcongr
    _ = 384 * ((N : ℝ) ^ (k * δ₁) * u ^ 14 * v) := by ring
    _ ≤ 384 * (N : ℝ) ^ (-τ / 2) := by gcongr

/-- One step of the continuity argument on the far level `farLev δ₁ ℓ` along a fixed sequence,
with the constant `K`: the conclusion of `far_stage` for every admissible `ℓ` and `φ`. -/
private def Far_Stage (K : ℝ) (D : ℕ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (τ δ₁ : ℝ) : Prop :=
  ∀ ℓ : ℕ → ℝ, (∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) →
    ∀ φ : ℕ → ℂ → ℝ,
      (∀ N, ∀ z ∈ farLev δ₁ ℓ N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ (2 * δ₁)) →
      (∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N → η ≤ η' →
        η' ≤ 2 → φ N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤ φ N ((E : ℂ) + (η : ℂ) * Complex.I)) →
      aprioriLL D μ A (farLev δ₁ ℓ) φ →
    PrecS μ (U := fun N => {z // z ∈ farLev δ₁ ℓ N})
        (fun N w h => ‖blockTr D N (res (Matrix.of h + lam D N (A N)) w.1 -
          MExt (lam D N (A N)) w.1)‖)
        (fun N w _ => (N : ℝ) ^ (K * δ₁ / 2) * (1 + φ N w.1) ^ 6 *
          psiFar N w.1 (φ N w.1) ^ 2) ∧
      aprioriLL D μ A (farLev δ₁ ℓ)
        (fun N z => (N : ℝ) ^ (K * δ₁ / 4) * (1 + φ N z) ^ 3 * psiFar N z (φ N z) +
          (N : ℝ) ^ (K * δ₁ / 2) * (1 + φ N z) ^ 6 * psiFar N z (φ N z) ^ 2)

/-- `(N^{a/4})² = N^{a/2}` and `(N^{a/4})⁴ = N^{a}`. -/
private lemma Far_rpow_quarter (N : ℕ) (a : ℝ) :
    ((N : ℝ) ^ (a / 4)) ^ 2 = (N : ℝ) ^ (a / 2) ∧ ((N : ℝ) ^ (a / 4)) ^ 4 = (N : ℝ) ^ a := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf

/-- One level of the continuity argument: from the a priori bound `1` on level `k`, the transfer
and one step give the a priori bound `1` on level `k + 1`; the step maps `φ ≤ N^{2δ₁}` to
`N^{Kδ₁/4}(1+φ)³ψ_F + N^{Kδ₁/2}(1+φ)⁶ψ_F² ≤ √(384 N^{-τ/2}) + 384 N^{-τ/2} ≤ 1`. -/
private lemma Far_step {D : ℕ} {δA : ℝ} {C : ℕ → ℝ} {θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hseq : LLSeq D δA C θ μ A) {K τ δ₁ : ℝ} (hst : Far_Stage K D μ A τ δ₁) (hK1 : 1 ≤ K)
    (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) (hδ : 0 < δ₁) (hKδ : (K + 28) * δ₁ ≤ τ) (k : ℕ)
    (hP : aprioriLL D μ A (farLev δ₁ (Far_lev τ δ₁ k)) (fun _ _ => 1)) :
    aprioriLL D μ A (farLev δ₁ (Far_lev τ δ₁ (k + 1))) (fun _ _ => 1) := by
  have hδ1 : δ₁ ≤ 1 := by nlinarith
  have h0 := Far_transfer hseq hτ (by linarith) hδ hδ1 k hP
  have hb : ∀ N, ∀ z ∈ farLev δ₁ (Far_lev τ δ₁ (k + 1)) N,
      ((N : ℝ))⁻¹ ≤ Far_phi0 τ δ₁ k N z ∧ Far_phi0 τ δ₁ k N z ≤ (N : ℝ) ^ (2 * δ₁) := by
    intro N z hz
    have hN := Far_one_le hz
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ₁) := Real.one_le_rpow hN (by linarith)
    have h2 : ((N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
    unfold Far_phi0
    split_ifs <;> constructor <;> linarith
  have hm : ∀ (N : ℕ) (E η η' : ℝ),
      ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ (Far_lev τ δ₁ (k + 1)) N → η ≤ η' → η' ≤ 2 →
      Far_phi0 τ δ₁ k N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤
        Far_phi0 τ δ₁ k N ((E : ℂ) + (η : ℂ) * Complex.I) := by
    intro N E η η' hz hηη _
    have hN := Far_one_le hz
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ₁) := Real.one_le_rpow hN (by linarith)
    unfold Far_phi0
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    split_ifs with ha hb' <;> linarith
  have h1 := (hst (Far_lev τ δ₁ (k + 1)) (fun N => le_max_right _ _) (Far_phi0 τ δ₁ k) hb hm h0).2
  obtain ⟨N₁, hN₁⟩ := Far_ev 1536 (τ / 2) (by positivity)
  unfold aprioriLL at h1 ⊢
  refine Far_precS_le μ _ _ _ (fun _ => _) (fun _ => h1) (fun _ _ _ => le_rfl) fun ε hε => ⟨0, N₁,
    fun N hN u _ => ?_⟩
  obtain ⟨⟨z, hz⟩, -, -⟩ := u
  have hN1 := Far_one_le hz
  have hN0 : (0 : ℝ) < N := by linarith
  simp only
  set φ := Far_phi0 τ δ₁ k N z with hφdef
  have hφ0 : 0 ≤ φ := (inv_nonneg.mpr hN0.le).trans (hb N z hz).1
  have hη : (N : ℝ) ^ (-1 + τ) ≤ z.im := (le_max_right _ _).trans hz.2.2.1
  have hQ := Far_bound N hN1 τ δ₁ (K / 2) hτ.le (by linarith) hδ.le (by nlinarith) z hη φ hφ0
    (hb N z hz).2
  have e2 : (N : ℝ) ^ (K / 2 * δ₁) = (N : ℝ) ^ (K * δ₁ / 2) := by ring_nf
  rw [e2] at hQ
  have hq : 384 * (N : ℝ) ^ (-τ / 2) ≤ 1 / 4 := by
    have h1536 := hN₁ N hN
    have hpos : 0 < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
    rw [show -τ / 2 = -(τ / 2) by ring, Real.rpow_neg hN0.le]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  set T := (N : ℝ) ^ (K * δ₁ / 4) * (1 + φ) ^ 3 * psiFar N z φ with hT
  set Q := (N : ℝ) ^ (K * δ₁ / 2) * (1 + φ) ^ 6 * psiFar N z φ ^ 2 with hQdef
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hη
  have hT0 : 0 ≤ T := by
    have := Far_psiFar_nonneg N z φ hzim
    positivity
  have hTQ : T ^ 2 = Q := by
    rw [hT, hQdef, mul_pow, mul_pow, (Far_rpow_quarter N (K * δ₁)).1]
    ring
  have hT2 : T ≤ 1 / 2 := Far_le_of_sq_le (by norm_num) (by rw [hTQ]; linarith)
  have hε1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  show T + Q ≤ (N : ℝ) ^ ε * 1
  linarith

/-- Every level carries the a priori bound `1`. -/
private lemma Far_levels {D : ℕ} {δA : ℝ} {C : ℕ → ℝ} {θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hseq : LLSeq D δA C θ μ A) {K τ δ₁ : ℝ} (hst : Far_Stage K D μ A τ δ₁) (hK1 : 1 ≤ K)
    (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) (hδ : 0 < δ₁) (hKδ : (K + 28) * δ₁ ≤ τ) (k : ℕ) :
    aprioriLL D μ A (farLev δ₁ (Far_lev τ δ₁ k)) (fun _ _ => 1) := by
  induction k with
  | zero => exact Far_base hseq τ δ₁
  | succ k ih => exact Far_step hseq hst hK1 hτ hτ4 hδ hKδ k ih

/-! ### The iteration on the last level -/

set_option maxHeartbeats 1000000 in
/-- One step of the iteration (deterministic): with `r = N^{-1/2}`, `a = p (r + Y)`, `b = p² Y`
and `Â = 1024 (a + b)`, if `p ≤ e`, `r e² ≤ 1`, `Y e⁴ ≤ 1`, `e ≥ 48`, and
`0 ≤ φ ≤ min(1, Â N^s)`, then `p (1+φ)³ ψ + p² (1+φ)⁶ ψ² ≤ min(1, Â N^{s/2})` for
`ψ = √(1/N + φ Y) + Y`. -/
private lemma Far_fix (n p Y e φ s : ℝ) (hn : 1 ≤ n) (hp : 1 ≤ p) (hpe : p ≤ e) (he : 48 ≤ e)
    (hr : Real.sqrt (1 / n) * e ^ 2 ≤ 1) (hY0 : 0 ≤ Y) (hY : Y * e ^ 4 ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hs : 0 ≤ s)
    (hφ : φ ≤ 1024 * (p * (Real.sqrt (1 / n) + Y) + p ^ 2 * Y) * n ^ s) :
    p * (1 + φ) ^ 3 * (Real.sqrt (1 / n + φ * Y) + Y) +
        p ^ 2 * (1 + φ) ^ 6 * (Real.sqrt (1 / n + φ * Y) + Y) ^ 2 ≤
      min 1 (1024 * (p * (Real.sqrt (1 / n) + Y) + p ^ 2 * Y) * n ^ (s / 2)) := by
  set r := Real.sqrt (1 / n) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hn0 : 0 < n := by linarith
  have hφY0 : 0 ≤ φ * Y := mul_nonneg hφ0 hY0
  set q := Real.sqrt (φ * Y) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q ^ 2 = φ * Y := Real.sq_sqrt hφY0
  set sy := Real.sqrt Y with hsydef
  have hsy0 : 0 ≤ sy := Real.sqrt_nonneg _
  have hsysq : sy ^ 2 = Y := Real.sq_sqrt hY0
  have hq_le : q ≤ sy := Real.sqrt_le_sqrt (by nlinarith)
  have hsq : Real.sqrt (1 / n + φ * Y) ≤ r + q := Far_sqrt_add_le (by positivity) hφY0
  have hpr : p * r ≤ 1 / 48 := by
    have h1 : 48 * (e * r) ≤ e * (e * r) := mul_le_mul_of_nonneg_right he (by positivity)
    have h2 : e * r ≤ 1 / 48 := by nlinarith
    nlinarith
  have hsye : sy * e ^ 2 ≤ 1 := by
    apply Far_le_of_sq_le zero_le_one
    calc (sy * e ^ 2) ^ 2 = Y * e ^ 4 := by rw [mul_pow, hsysq]; ring
      _ ≤ 1 ^ 2 := by rw [one_pow]; exact hY
  have hpsy : p * sy ≤ 1 / 48 := by
    have h1 : 48 * (e * sy) ≤ e * (e * sy) := mul_le_mul_of_nonneg_right he (by positivity)
    have h2 : e * sy ≤ 1 / 48 := by nlinarith
    nlinarith
  have hpY : p * Y ≤ 1 / 48 := by
    have he1 : 1 ≤ e := by linarith
    have h1 : e ^ 2 ≤ e ^ 4 := pow_le_pow_right₀ he1 (by norm_num)
    have h2 : Y * e ^ 2 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left h1 hY0) hY
    have h3 : 48 * (e * Y) ≤ e * (e * Y) := mul_le_mul_of_nonneg_right he (by positivity)
    have h4 : e * Y ≤ 1 / 48 := by nlinarith
    nlinarith
  have hpq : p * q ≤ p * sy := mul_le_mul_of_nonneg_left hq_le (by linarith)
  set v := p * (Real.sqrt (1 / n + φ * Y) + Y) with hvdef
  have hv0 : 0 ≤ v := by positivity
  have hv : v ≤ p * r + p * q + p * Y := by
    have := mul_le_mul_of_nonneg_left (add_le_add_left hsq Y) (by linarith : 0 ≤ p)
    rw [hvdef]
    nlinarith
  have hv16 : v ≤ 1 / 16 := by linarith
  set w3 := (1 + φ) ^ 3 with hw3
  have hw1 : 1 ≤ w3 := one_le_pow₀ (by linarith)
  have hw8 : w3 ≤ 8 := by
    have : (1 + φ) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    linarith
  have hLHS : p * (1 + φ) ^ 3 * (Real.sqrt (1 / n + φ * Y) + Y) +
      p ^ 2 * (1 + φ) ^ 6 * (Real.sqrt (1 / n + φ * Y) + Y) ^ 2 = w3 * v + (w3 * v) ^ 2 := by
    rw [hw3, hvdef]
    ring
  have hL : w3 * v + (w3 * v) ^ 2 ≤ 16 * v := by
    have h1 : w3 * v ≤ 8 * v := mul_le_mul_of_nonneg_right hw8 hv0
    have h2 : (w3 * v) ^ 2 ≤ (8 * v) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  rw [hLHS]
  refine le_min (by linarith) ?_
  set a := p * (r + Y) with hadef
  set b := p ^ 2 * Y with hbdef
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set w := n ^ (s / 2) with hwdef
  have hw1' : 1 ≤ w := Real.one_le_rpow hn (by linarith)
  have hww : n ^ s = w ^ 2 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring_nf
  rw [hww] at hφ
  have hpq2 : p * q ≤ 32 * (a + b) * w := by
    apply Far_le_of_sq_le (by positivity)
    calc (p * q) ^ 2 = p ^ 2 * (φ * Y) := by rw [mul_pow, hqsq]
      _ ≤ p ^ 2 * (1024 * (a + b) * w ^ 2 * Y) := by gcongr
      _ = 1024 * (a + b) * b * w ^ 2 := by rw [hbdef]; ring
      _ ≤ 1024 * (a + b) * (a + b) * w ^ 2 := by gcongr; linarith
      _ = (32 * (a + b) * w) ^ 2 := by ring
  have hva : v ≤ a + p * q := by rw [hadef]; linarith
  have haw : a ≤ (a + b) * w := by nlinarith
  linarith

/-- The final bound of the iteration (deterministic): under `0 ≤ φ ≤ min(1, Â N^s)`,
`p² (1+φ)⁶ ψ² ≤ 400000 p⁴ N^s (1/N + Y²)`, using `r Y ≤ (1/N + Y²)/2`. -/
private lemma Far_fin (n p Y φ s : ℝ) (hn : 1 ≤ n) (hp : 1 ≤ p) (hY0 : 0 ≤ Y)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hs : 0 ≤ s)
    (hφ : φ ≤ 1024 * (p * (Real.sqrt (1 / n) + Y) + p ^ 2 * Y) * n ^ s) :
    p ^ 2 * (1 + φ) ^ 6 * (Real.sqrt (1 / n + φ * Y) + Y) ^ 2 ≤
      400000 * p ^ 4 * n ^ s * (1 / n + Y ^ 2) := by
  have hn0 : 0 < n := by linarith
  set r := Real.sqrt (1 / n) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 1 / n := Real.sq_sqrt (by positivity)
  have hφY0 : 0 ≤ φ * Y := mul_nonneg hφ0 hY0
  set x := Real.sqrt (1 / n + φ * Y) with hxdef
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = 1 / n + φ * Y := Real.sq_sqrt (by positivity)
  set m := n ^ s with hmdef
  have hm1 : 1 ≤ m := Real.one_le_rpow hn hs
  set P := p ^ 2 with hPdef
  have hP1 : 1 ≤ P := by nlinarith
  have hpP : p ≤ P := by nlinarith
  set Z := 1 / n + Y ^ 2 with hZdef
  have hZ0 : 0 ≤ Z := by positivity
  have hψ : (x + Y) ^ 2 ≤ 2 * (1 / n + φ * Y) + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (x - Y)]
  have h6 : (1 + φ) ^ 6 ≤ 64 := by
    have : (1 + φ) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    linarith
  have hrY : r * Y ≤ Z / 2 := by
    rw [hZdef, ← hrsq]
    nlinarith [sq_nonneg (r - Y)]
  have hφY : φ * Y ≤ 2560 * P * m * Z := by
    have h1 : φ * Y ≤ 1024 * (p * (r + Y) + P * Y) * m * Y := mul_le_mul_of_nonneg_right hφ hY0
    have h2 : p * (r + Y) * Y + P * Y * Y ≤ P * (r * Y + 2 * Y ^ 2) := by
      have : p * (r * Y + Y * Y) ≤ P * (r * Y + Y * Y) :=
        mul_le_mul_of_nonneg_right hpP (by positivity)
      nlinarith
    have h3 : P * (r * Y + 2 * Y ^ 2) ≤ P * ((5 / 2) * Z) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [hZdef] at hrY ⊢
      have : 0 ≤ 1 / n := by positivity
      nlinarith
    have h4 : (p * (r + Y) + P * Y) * Y ≤ P * ((5 / 2) * Z) := by nlinarith
    calc φ * Y ≤ 1024 * (p * (r + Y) + P * Y) * m * Y := h1
      _ = 1024 * m * ((p * (r + Y) + P * Y) * Y) := by ring
      _ ≤ 1024 * m * (P * ((5 / 2) * Z)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2560 * P * m * Z := by ring
  have hp4 : p ^ 4 = P * P := by rw [hPdef]; ring
  rw [hp4]
  have hQ : (x + Y) ^ 2 ≤ 2 * Z + 2 * (2560 * P * m * Z) := by
    rw [hZdef] at hφY ⊢
    linarith
  calc P * (1 + φ) ^ 6 * (x + Y) ^ 2 ≤ P * 64 * (2 * Z + 2 * (2560 * P * m * Z)) := by
        gcongr
    _ = 128 * P * Z + 327680 * (P * P) * m * Z := by ring
    _ ≤ 400000 * (P * P) * m * Z := by
        have h1 : P * Z ≤ (P * P) * m * Z := by
          have : P ≤ P * P * m := by nlinarith
          exact mul_le_mul_of_nonneg_right this hZ0
        nlinarith

/-- `Â = 1024 (p (N^{-1/2} + (Nη)⁻¹) + p² (Nη)⁻¹)` with `p = N^{Kδ₁/4}`, the size of the fixed
point of one step. -/
private def Far_hat (K δ₁ : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  1024 * ((N : ℝ) ^ (K * δ₁ / 4) * (Real.sqrt (1 / (N : ℝ)) + 1 / ((N : ℝ) * z.im)) +
    ((N : ℝ) ^ (K * δ₁ / 4)) ^ 2 * (1 / ((N : ℝ) * z.im)))

/-- The bound `min(1, Â N^{2^{-n}})` after `n` steps of the iteration. -/
private def Far_psi (K δ₁ : ℝ) (n N : ℕ) (z : ℂ) : ℝ :=
  min 1 (Far_hat K δ₁ N z * (N : ℝ) ^ ((1 / 2 : ℝ) ^ n))

/-- On a far level: `Â ≥ 512/N`, hence `N⁻¹ ≤ min(1, Â N^{2^{-n}}) ≤ 1`, and `Â` is
non-increasing in `η`. -/
private lemma Far_psi_bounds {K δ₁ : ℝ} (hKδ : 0 ≤ K * δ₁) {ℓ : ℕ → ℝ} {N : ℕ} {z : ℂ}
    (hz : z ∈ farLev δ₁ ℓ N) (hz0 : 0 < z.im) (n : ℕ) :
    512 * ((N : ℝ))⁻¹ ≤ Far_hat K δ₁ N z ∧ ((N : ℝ))⁻¹ ≤ Far_psi K δ₁ n N z ∧
      Far_psi K δ₁ n N z ≤ 1 := by
  have hN := Far_one_le hz
  have hN0 : (0 : ℝ) < N := by linarith
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ (K * δ₁ / 4) := Real.one_le_rpow hN (by linarith)
  have hY : 1 / 2 * ((N : ℝ))⁻¹ ≤ 1 / ((N : ℝ) * z.im) := by
    rw [show 1 / 2 * ((N : ℝ))⁻¹ = 1 / (2 * N) by field_simp]
    exact one_div_le_one_div_of_le (mul_pos hN0 hz0) (by nlinarith [hz.2.2.2])
  have hY0 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
  have hr0 : 0 ≤ Real.sqrt (1 / (N : ℝ)) := Real.sqrt_nonneg _
  have hhat : 512 * ((N : ℝ))⁻¹ ≤ Far_hat K δ₁ N z := by
    unfold Far_hat
    have h1 : 1 / ((N : ℝ) * z.im) ≤ (N : ℝ) ^ (K * δ₁ / 4) *
        (Real.sqrt (1 / (N : ℝ)) + 1 / ((N : ℝ) * z.im)) := by nlinarith
    have h2 : 0 ≤ ((N : ℝ) ^ (K * δ₁ / 4)) ^ 2 * (1 / ((N : ℝ) * z.im)) := by positivity
    linarith
  have hs1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 / 2 : ℝ) ^ n) := Real.one_le_rpow hN (by positivity)
  have hinv : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hN0
  refine ⟨hhat, le_min (inv_le_one_of_one_le₀ hN) ?_, min_le_left _ _⟩
  have : Far_hat K δ₁ N z ≤ Far_hat K δ₁ N z * (N : ℝ) ^ ((1 / 2 : ℝ) ^ n) :=
    le_mul_of_one_le_right (by linarith) hs1
  linarith

/-- `min(1, Â N^{2^{-n}})` is non-increasing in `η` on vertical lines. -/
private lemma Far_psi_mono (K δ₁ : ℝ) (n N : ℕ) (E η η' : ℝ) (hN : (1 : ℝ) ≤ N) (hη : 0 < η)
    (hηη : η ≤ η') :
    Far_psi K δ₁ n N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤
      Far_psi K δ₁ n N ((E : ℂ) + (η : ℂ) * Complex.I) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have him : ∀ y : ℝ, ((E : ℂ) + (y : ℂ) * Complex.I).im = y := fun y => by simp
  have hY : 1 / ((N : ℝ) * η') ≤ 1 / ((N : ℝ) * η) :=
    one_div_le_one_div_of_le (mul_pos hN0 hη) (mul_le_mul_of_nonneg_left hηη hN0.le)
  unfold Far_psi Far_hat
  rw [him, him]
  have hp : 0 ≤ (N : ℝ) ^ (K * δ₁ / 4) := Real.rpow_nonneg hN0.le _
  have hs : 0 ≤ (N : ℝ) ^ ((1 / 2 : ℝ) ^ n) := Real.rpow_nonneg hN0.le _
  refine min_le_min_left _ (mul_le_mul_of_nonneg_right ?_ hs)
  gcongr

/-- The bounds `min(1, Â N^{2^{-n}})` are admissible a priori bounds on a far level with
`ℓ ≥ N^{-1+τ}`: they lie in `[N⁻¹, N^{2δ₁}]` and are non-increasing in `η`. -/
private lemma Far_psi_adm {K τ δ₁ : ℝ} (hδ : 0 ≤ δ₁) (hKδ0 : 0 ≤ K * δ₁) (ℓ : ℕ → ℝ)
    (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) (n : ℕ) :
    (∀ N, ∀ z ∈ farLev δ₁ ℓ N, (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ 0 < z.im) ∧
    (∀ N, ∀ z ∈ farLev δ₁ ℓ N, ((N : ℝ))⁻¹ ≤ Far_psi K δ₁ n N z ∧
      Far_psi K δ₁ n N z ≤ (N : ℝ) ^ (2 * δ₁)) ∧
    (∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ farLev δ₁ ℓ N →
      η ≤ η' → η' ≤ 2 → Far_psi K δ₁ n N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤
        Far_psi K δ₁ n N ((E : ℂ) + (η : ℂ) * Complex.I)) := by
  have hzim : ∀ N, ∀ z ∈ farLev δ₁ ℓ N, (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ 0 < z.im := by
    intro N z hz
    have hN0 : (0 : ℝ) < N := by linarith [Far_one_le hz]
    exact ⟨(hℓ N).trans hz.2.2.1,
      lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) ((hℓ N).trans hz.2.2.1)⟩
  refine ⟨hzim, fun N z hz => ?_, fun N E η η' hz hηη _ => ?_⟩
  · obtain ⟨-, h2, h3⟩ := Far_psi_bounds hKδ0 hz (hzim N z hz).2 n
    exact ⟨h2, h3.trans (Real.one_le_rpow (Far_one_le hz) (by linarith))⟩
  · have := (hzim N _ hz).2
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
    exact Far_psi_mono K δ₁ n N E η η' (Far_one_le hz) this hηη

/-- The facts of `Far_fix` on a far level with `ℓ ≥ N^{-1+τ}` and `K δ₁ ≤ τ ≤ 1`, with
`e = N^{τ/4}`: `p ≤ e`, `N^{-1/2} e² ≤ 1`, `(Nη)⁻¹ e⁴ ≤ 1`. -/
private lemma Far_e_facts {K τ δ₁ : ℝ} (hτ1 : τ ≤ 1) (hKδ : K * δ₁ ≤ τ) {N : ℕ} (hN : (1 : ℝ) ≤ N) {z : ℂ} (hη : (N : ℝ) ^ (-1 + τ) ≤ z.im) :
    (N : ℝ) ^ (K * δ₁ / 4) ≤ (N : ℝ) ^ (τ / 4) ∧
      Real.sqrt (1 / (N : ℝ)) * ((N : ℝ) ^ (τ / 4)) ^ 2 ≤ 1 ∧
      1 / ((N : ℝ) * z.im) * ((N : ℝ) ^ (τ / 4)) ^ 4 ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨e2, e4⟩ := Far_rpow_quarter N τ
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN (by linarith), ?_, ?_⟩
  · rw [e2]
    have h1 : (N : ℝ) ^ (τ / 2) ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have h2 : Real.sqrt (1 / (N : ℝ)) * Real.sqrt N = 1 := by
      rw [← Real.sqrt_mul (by positivity), one_div, inv_mul_cancel₀ hN0.ne', Real.sqrt_one]
    calc Real.sqrt (1 / (N : ℝ)) * (N : ℝ) ^ (τ / 2) ≤ Real.sqrt (1 / (N : ℝ)) * Real.sqrt N :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = 1 := h2
  · rw [e4]
    have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hη
    have h1 : (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
      have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
        conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
        rw [← Real.rpow_add hN0]
        ring_nf
      rw [← e]
      exact mul_le_mul_of_nonneg_left hη hN0.le
    rw [one_div_mul_eq_div, div_le_one (mul_pos hN0 hzim)]
    exact h1

/-- The iteration on a level that carries the a priori bound `1`: after `n` steps the a priori
bound `min(1, Â N^{2^{-n}})` holds. -/
private lemma Far_iter {D : ℕ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    {K τ δ₁ : ℝ} (hst : Far_Stage K D μ A τ δ₁) (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4)
    (hδ : 0 ≤ δ₁) (hKδ0 : 0 ≤ K * δ₁) (hKδ : K * δ₁ ≤ τ) (ℓ : ℕ → ℝ)
    (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N)
    (h1 : aprioriLL D μ A (farLev δ₁ ℓ) (fun _ _ => 1)) (n : ℕ) :
    aprioriLL D μ A (farLev δ₁ ℓ) (Far_psi K δ₁ n) := by
  have hzim := (Far_psi_adm (K := K) hδ hKδ0 ℓ hℓ 0).1
  induction n with
  | zero =>
    unfold aprioriLL at h1 ⊢
    refine Far_precS_le μ _ _ _ (fun _ => _) (fun _ => h1) (fun _ _ _ => le_rfl)
      fun ε hε => ⟨0, 0, fun N _ u _ => ?_⟩
    obtain ⟨⟨z, hz⟩, -, -⟩ := u
    have hN1 := Far_one_le hz
    have hN0 : (0 : ℝ) < N := by linarith
    obtain ⟨hhat, -, -⟩ := Far_psi_bounds hKδ0 hz (hzim N z hz).2 0
    have hψ : Far_psi K δ₁ 0 N z = 1 := by
      unfold Far_psi
      rw [pow_zero, Real.rpow_one]
      refine min_eq_left ?_
      have : 512 * ((N : ℝ))⁻¹ * N ≤ Far_hat K δ₁ N z * N :=
        mul_le_mul_of_nonneg_right hhat hN0.le
      rw [mul_assoc, inv_mul_cancel₀ hN0.ne'] at this
      linarith
    show 1 ≤ (N : ℝ) ^ ε * Far_psi K δ₁ 0 N z
    rw [hψ, mul_one]
    exact Real.one_le_rpow hN1 hε.le
  | succ n ih =>
    obtain ⟨-, hb, hm⟩ := Far_psi_adm (K := K) hδ hKδ0 ℓ hℓ n
    have hF := (hst ℓ hℓ (Far_psi K δ₁ n) hb hm ih).2
    obtain ⟨N₁, hN₁⟩ := Far_ev 48 (τ / 4) (by positivity)
    unfold aprioriLL at hF ⊢
    refine Far_precS_le μ _ _ _ (fun _ => _) (fun _ => hF) (fun _ _ _ => le_rfl)
      fun ε hε => ⟨0, N₁, fun N hN u _ => ?_⟩
    obtain ⟨⟨z, hz⟩, -, -⟩ := u
    have hN1 := Far_one_le hz
    have hN0 : (0 : ℝ) < N := by linarith
    obtain ⟨hη, hz0⟩ := hzim N z hz
    obtain ⟨hpe, hre, hYe⟩ := Far_e_facts (by linarith) hKδ hN1 hη
    obtain ⟨-, hψ0, hψ1⟩ := Far_psi_bounds hKδ0 hz hz0 n
    have hp : (1 : ℝ) ≤ (N : ℝ) ^ (K * δ₁ / 4) := Real.one_le_rpow hN1 (by linarith)
    have hfix := Far_fix N ((N : ℝ) ^ (K * δ₁ / 4)) (1 / ((N : ℝ) * z.im)) ((N : ℝ) ^ (τ / 4))
      (Far_psi K δ₁ n N z) ((1 / 2 : ℝ) ^ n) hN1 hp hpe (hN₁ N hN) hre (by positivity) hYe
      ((inv_nonneg.mpr hN0.le).trans hψ0) hψ1 (by positivity) (min_le_right _ _)
    have e1 : Far_psi K δ₁ n N z / ((N : ℝ) * z.im) =
        Far_psi K δ₁ n N z * (1 / ((N : ℝ) * z.im)) := div_eq_mul_one_div _ _
    have e2 : ((N : ℝ) ^ (K * δ₁ / 4)) ^ 2 = (N : ℝ) ^ (K * δ₁ / 2) :=
      (Far_rpow_quarter N (K * δ₁)).1
    have e3 : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n / 2 := by rw [pow_succ]; ring
    have hψn1 := (Far_psi_bounds hKδ0 hz hz0 (n + 1)).2.1
    have hinv : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hN0
    have hψ' : Far_psi K δ₁ (n + 1) N z ≤ (N : ℝ) ^ ε * Far_psi K δ₁ (n + 1) N z :=
      le_mul_of_one_le_left (by linarith) (Real.one_le_rpow hN1 hε.le)
    refine le_trans ?_ hψ'
    show (N : ℝ) ^ (K * δ₁ / 4) * (1 + Far_psi K δ₁ n N z) ^ 3 *
        psiFar N z (Far_psi K δ₁ n N z) + (N : ℝ) ^ (K * δ₁ / 2) *
        (1 + Far_psi K δ₁ n N z) ^ 6 * psiFar N z (Far_psi K δ₁ n N z) ^ 2 ≤
      Far_psi K δ₁ (n + 1) N z
    unfold psiFar
    rw [e1, ← e2]
    unfold Far_psi Far_hat
    rw [e3]
    exact hfix

/-- The averaged bound on a level that carries the a priori bound `1`:
`|⟨G - M⟩| ≤ |x|_∞ ≺ N^{Kδ₁/2}(1+φ_j)⁶ψ_F² ≤ 400000 N^{Kδ₁} N^{2^{-j}} (1/N + (Nη)⁻²)`, and
`2^{-j}` is arbitrarily small. -/
private lemma Far_sharp {D : ℕ} {δA : ℝ} {C : ℕ → ℝ} {θ : ℕ → ℝ}
    {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)} {A : ∀ N, Matrix (Fin N) (Fin N) ℂ}
    (hseq : LLSeq D δA C θ μ A) {K τ δ₁ : ℝ} (hst : Far_Stage K D μ A τ δ₁) (hτ : 0 < τ)
    (hτ4 : τ ≤ 1 / 4) (hδ : 0 ≤ δ₁) (hKδ0 : 0 ≤ K * δ₁) (hKδ : K * δ₁ ≤ τ) (L : ℝ)
    (hKL : K * δ₁ ≤ L * δ₁) (ℓ : ℕ → ℝ) (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N)
    (h1 : aprioriLL D μ A (farLev δ₁ ℓ) (fun _ _ => 1)) :
    PrecS μ (U := fun N => {z // z ∈ farLev δ₁ ℓ N})
      (fun N w h => ‖ntr (res (Matrix.of h + lam D N (A N)) w.1 - MExt (lam D N (A N)) w.1)‖)
      (fun N w _ => (N : ℝ) ^ (L * δ₁) * (1 / N + 1 / ((N : ℝ) * w.1.im) ^ 2)) := by
  have hzim := (Far_psi_adm (K := K) hδ hKδ0 ℓ hℓ 0).1
  have hS := fun n => (hst ℓ hℓ (Far_psi K δ₁ n) (Far_psi_adm hδ hKδ0 ℓ hℓ n).2.1
    (Far_psi_adm hδ hKδ0 ℓ hℓ n).2.2
    (Far_iter hst hτ hτ4 hδ hKδ0 hKδ ℓ hℓ h1 n)).1
  refine Far_precS_le μ _ _ _ _ hS
    (fun N w h => Far_ntr_le_blockTr D N hseq.one_le_D _) fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < ε / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Far_ev 400000 (ε / 2) (by positivity)
  refine ⟨j, N₁, fun N hN u _ => ?_⟩
  obtain ⟨z, hz⟩ := u
  have hN1 := Far_one_le hz
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hη, hz0⟩ := hzim N z hz
  obtain ⟨-, hψ0, hψ1⟩ := Far_psi_bounds hKδ0 hz hz0 j
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ (K * δ₁ / 4) := Real.one_le_rpow hN1 (by linarith)
  have hfin := Far_fin N ((N : ℝ) ^ (K * δ₁ / 4)) (1 / ((N : ℝ) * z.im))
    (Far_psi K δ₁ j N z) ((1 / 2 : ℝ) ^ j) hN1 hp (by positivity)
    ((inv_nonneg.mpr hN0.le).trans hψ0) hψ1 (by positivity) (min_le_right _ _)
  obtain ⟨e2, e4⟩ := Far_rpow_quarter N (K * δ₁)
  have e1 : Far_psi K δ₁ j N z / ((N : ℝ) * z.im) =
      Far_psi K δ₁ j N z * (1 / ((N : ℝ) * z.im)) := div_eq_mul_one_div _ _
  have eY : (1 / ((N : ℝ) * z.im)) ^ 2 = 1 / ((N : ℝ) * z.im) ^ 2 := by rw [div_pow, one_pow]
  rw [e2, e4, eY] at hfin
  show (N : ℝ) ^ (K * δ₁ / 2) * (1 + Far_psi K δ₁ j N z) ^ 6 *
      psiFar N z (Far_psi K δ₁ j N z) ^ 2 ≤
    (N : ℝ) ^ ε * ((N : ℝ) ^ (L * δ₁) * (1 / N + 1 / ((N : ℝ) * z.im) ^ 2))
  unfold psiFar
  rw [e1]
  refine hfin.trans ?_
  have hc := hN₁ N hN
  have hs : (N : ℝ) ^ ((1 / 2 : ℝ) ^ j) ≤ (N : ℝ) ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hj.le
  have hKL' : (N : ℝ) ^ (K * δ₁) ≤ (N : ℝ) ^ (L * δ₁) := Real.rpow_le_rpow_of_exponent_le hN1 hKL
  have hεε : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  have h0 : 0 ≤ (N : ℝ) ^ ((1 / 2 : ℝ) ^ j) := Real.rpow_nonneg hN0.le _
  have h0' : 0 ≤ (N : ℝ) ^ (K * δ₁) := Real.rpow_nonneg hN0.le _
  generalize (N : ℝ) ^ (K * δ₁) = a at hKL' h0' ⊢
  generalize (N : ℝ) ^ ((1 / 2 : ℝ) ^ j) = b at hs h0 ⊢
  generalize (N : ℝ) ^ (L * δ₁) = l at hKL' ⊢
  rw [hεε]
  generalize (N : ℝ) ^ (ε / 2) = c at hc hs ⊢
  have hZ : 0 ≤ 1 / (N : ℝ) + 1 / ((N : ℝ) * z.im) ^ 2 := by positivity
  generalize 1 / (N : ℝ) + 1 / ((N : ℝ) * z.im) ^ 2 = Z at hZ ⊢
  have h1 : 400000 * b ≤ c * c := mul_le_mul hc hs h0 (by linarith)
  have h2 : a * Z ≤ l * Z := mul_le_mul_of_nonneg_right hKL' hZ
  calc 400000 * a * b * Z = (400000 * b) * (a * Z) := by ring
    _ ≤ (c * c) * (l * Z) := mul_le_mul h1 h2 (by positivity) (by nlinarith)

/-! ### The union over the spectral parameter -/

/-- `x² + (25/16)(1 + x) ≤ x⁴` for `x ≥ 3`. -/
private lemma Far_poly3 (x : ℝ) (hx : 3 ≤ x) : x ^ 2 + 25 / 16 * (1 + x) ≤ x ^ 4 := by
  have h9 : 9 ≤ x ^ 2 := by nlinarith
  have e : x ^ 4 = x ^ 2 * x ^ 2 := by ring
  nlinarith

/-- `2x² ≤ x⁴` for `x ≥ 4`. -/
private lemma Far_poly4 (x : ℝ) (hx : 4 ≤ x) : 2 * x ^ 2 ≤ x ^ 4 := by
  have h16 : 16 ≤ x ^ 2 := by nlinarith
  have e : x ^ 4 = x ^ 2 * x ^ 2 := by ring
  nlinarith

/-- `|1/(Na)² - 1/(Nb)²| ≤ 2N |a - b|` for `a, b ≥ N⁻¹`. -/
private lemma Far_inv_sq_lip (N a b : ℝ) (hN : 1 ≤ N) (ha : N⁻¹ ≤ a) (hb : N⁻¹ ≤ b) :
    |1 / (N * a) ^ 2 - 1 / (N * b) ^ 2| ≤ 2 * N * |a - b| := by
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (inv_pos.mpr hN0) ha
  have hb0 : 0 < b := lt_of_lt_of_le (inv_pos.mpr hN0) hb
  set x := 1 / a with hx
  set y := 1 / b with hy
  have hx0 : 0 < x := by positivity
  have hy0 : 0 < y := by positivity
  have hxN : x ≤ N := by
    rw [hx, one_div]
    calc a⁻¹ ≤ (N⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hN0) ha
      _ = N := inv_inv N
  have hyN : y ≤ N := by
    rw [hy, one_div]
    calc b⁻¹ ≤ (N⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hN0) hb
      _ = N := inv_inv N
  have e1 : 1 / (N * a) ^ 2 - 1 / (N * b) ^ 2 = (x - y) * (x + y) / N ^ 2 := by
    rw [hx, hy]
    field_simp
    ring
  have e2 : x - y = (b - a) * x * y := by
    rw [hx, hy]
    field_simp
  rw [e1, e2, abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hx0, abs_of_pos hy0,
    abs_of_pos (by positivity : 0 < x + y), abs_of_pos (by positivity : (0 : ℝ) < N ^ 2),
    abs_sub_comm b a, div_le_iff₀ (by positivity)]
  have h1 : x * y ≤ N * N := mul_le_mul hxN hyN hy0.le hN0.le
  have h2 : x + y ≤ 2 * N := by linarith
  have h3 : 0 ≤ |a - b| := abs_nonneg _
  calc |a - b| * x * y * (x + y) = |a - b| * (x * y) * (x + y) := by ring
    _ ≤ |a - b| * (N * N) * (2 * N) := by gcongr
    _ = 2 * N * |a - b| * N ^ 2 := by ring

/-- The averaged bound far from the spectrum along one sequence of members: there is `L ≥ 1` such
that for `0 < τ ≤ 1/4`, `0 ≤ δ₁` and `L δ₁ ≤ τ`, outside an event of probability `≤ N^{-D'}`,
`|⟨G - M⟩| ≤ N^{τ'} N^{L δ₁} (N⁻¹ + (Nη)⁻²)` for all `z ∈ farDom τ δ₁ N` at once. -/
theorem far_aver_seq : ∃ L : ℝ, 1 ≤ L ∧
    ∀ (D : ℕ) (δA τ δ₁ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → τ ≤ 1 / 4 → 0 ≤ δ₁ → L * δ₁ ≤ τ →
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      μ N {h | ∃ z ∈ farDom τ δ₁ N,
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (L * δ₁) * (1 / N + 1 / ((N : ℝ) * z.im) ^ 2)) <
            ‖ntr (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨K, hK1, hK⟩ := far_stage
  refine ⟨K + 28, by linarith, ?_⟩
  intro D δA τ δ₁ C θ μ A hseq hτ hτ4 hδ₁ hLδ τ' hτ' D' hD'
  rcases hδ₁.lt_or_eq with hδ | hδ
  swap
  · -- `δ₁ = 0`: the far domain is empty
    refine ⟨0, fun N _ => le_trans (le_of_eq (measure_mono_null (t := ∅) ?_ measure_empty))
      bot_le⟩
    rintro h ⟨z, hz, -⟩
    exfalso
    have h1 := hz.1.trans hz.2.1
    rw [← hδ, Real.rpow_zero] at h1
    norm_num at h1
  have hKδ0 : 0 ≤ K * δ₁ := by positivity
  have hKδ : K * δ₁ ≤ τ := by nlinarith
  have hδ29 : 29 * δ₁ ≤ τ := by nlinarith
  have hst : Far_Stage K D μ A τ δ₁ := hK D δA τ δ₁ C θ μ A hseq hτ hτ4 hδ₁ hKδ
  have hlev := Far_levels hseq hst hK1 hτ hτ4 hδ hLδ (⌈(1 - τ) / δ₁⌉₊ + 1)
  have hsharp := Far_sharp hseq hst hτ hτ4 hδ₁ hKδ0 hKδ (K + 28) (by nlinarith)
    (Far_lev τ δ₁ (⌈(1 - τ) / δ₁⌉₊ + 1)) (fun N => le_max_right _ _) hlev
  obtain ⟨NΛ, hNΛ⟩ := Far_lam_small hseq
  have hD := hseq.one_le_D
  have hdom : ∀ N, ∀ z ∈ farDom τ δ₁ N, (1 : ℝ) ≤ N ∧ (4 : ℝ) ≤ N ∧ ((N : ℝ))⁻¹ ≤ z.im ∧
      0 < z.im ∧ z.im ≤ 2 := by
    intro N z hz
    have hz' : z ∈ farLev δ₁ (fun N => (N : ℝ) ^ (-1 + τ)) N := hz
    have hN1 := Far_one_le hz'
    have hN0 : (0 : ℝ) < N := by linarith
    have h1 : ((N : ℝ))⁻¹ ≤ (N : ℝ) ^ (-1 + τ) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    exact ⟨hN1, Far_four_le hz' (by linarith), h1.trans hz.2.2.1,
      lt_of_lt_of_le (inv_pos.mpr hN0) (h1.trans hz.2.2.1), hz.2.2.2⟩
  set ξ : ∀ N, ℂ → (Idx D N → Idx D N → ℂ) → ℝ := fun N z h =>
    if max NΛ 3 ≤ N ∧ (Matrix.of h).IsHermitian then
      ‖ntr (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖ else 0 with hξ
  set ζ : ∀ N, ℂ → (Idx D N → Idx D N → ℂ) → ℝ := fun N z _ =>
    (N : ℝ) ^ ((K + 28) * δ₁) * (1 / N + 1 / ((N : ℝ) * z.im) ^ 2) with hζ
  have hS : ∀ N, 1 ≤ N → farDom τ δ₁ N ⊆ Metric.closedBall 0 ((N : ℝ) ^ (1 : ℝ)) := by
    intro N _ z hz
    obtain ⟨hN1, -, -, hz0, hz2⟩ := hdom N z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (farZ_norm_le δ₁ N z hz.1 hz.2.1 (by rw [abs_of_pos hz0]; exact hz2)).1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hLξ : ∀ N ω, 1 ≤ N → ∀ u ∈ farDom τ δ₁ N, ∀ v ∈ farDom τ δ₁ N,
      |ξ N u ω - ξ N v ω| ≤ (N : ℝ) ^ (4 : ℝ) * ‖u - v‖ := by
    intro N ω _ u hu v hv
    have h4 : (N : ℝ) ^ (4 : ℝ) = (N : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [h4]
    simp only [hξ]
    split_ifs with hc
    · obtain ⟨hNc, hherm⟩ := hc
      obtain ⟨hN1, -, hu1, hu0, -⟩ := hdom N u hu
      obtain ⟨-, -, hv1, hv0, -⟩ := hdom N v hv
      have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hNc
      have hN0 : (0 : ℝ) < N := by linarith
      have hΛ1 := (hNΛ N (le_trans (le_max_left _ _) hNc)).2
      have hΛh := lam_isHermitian D N (A N)
      have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by exact_mod_cast hN1⟩)⟩
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [← Far_ntr_sub, Far_MExt_eq _ u hu0, Far_MExt_eq _ v hv0]
      have e : res (Matrix.of ω + lam D N (A N)) u - MSol (lam D N (A N)) u -
          (res (Matrix.of ω + lam D N (A N)) v - MSol (lam D N (A N)) v) =
          (res (Matrix.of ω + lam D N (A N)) u - res (Matrix.of ω + lam D N (A N)) v) -
            (MSol (lam D N (A N)) u - MSol (lam D N (A N)) v) := by abel
      rw [e]
      refine (Far_ntr_le_opNorm D N hD _).trans ((Far_opNorm_sub_le _ _).trans ?_)
      have hG := opNorm_res_sub_le _ (hherm.add hΛh) u v hu0 hv0
      have hM := (MSol_lipschitz _ hΛh hΛ1 ((N : ℝ))⁻¹ (inv_pos.mpr hN0) u v hu1 hv1).2
      rw [inv_inv] at hM
      have hG' : ‖u - v‖ / (u.im * v.im) ≤ (N : ℝ) ^ 2 * ‖u - v‖ := by
        rw [div_le_iff₀ (mul_pos hu0 hv0)]
        have h1 : ((N : ℝ))⁻¹ * ((N : ℝ))⁻¹ ≤ u.im * v.im :=
          mul_le_mul hu1 hv1 (inv_nonneg.mpr hN0.le) hu0.le
        have h2 : (N : ℝ) ^ 2 * (((N : ℝ))⁻¹ * ((N : ℝ))⁻¹) = 1 := by field_simp
        have h3 : 0 ≤ ‖u - v‖ := norm_nonneg _
        calc ‖u - v‖ = ‖u - v‖ * ((N : ℝ) ^ 2 * (((N : ℝ))⁻¹ * ((N : ℝ))⁻¹)) := by
              rw [h2, mul_one]
          _ ≤ ‖u - v‖ * ((N : ℝ) ^ 2 * (u.im * v.im)) := by gcongr
          _ = (N : ℝ) ^ 2 * ‖u - v‖ * (u.im * v.im) := by ring
      have hc4 := Far_poly3 N hN3
      have h3 : 0 ≤ ‖u - v‖ := norm_nonneg _
      nlinarith
    · simp only [sub_self, abs_zero]
      positivity
  have hLζ : ∀ N ω, 1 ≤ N → ∀ u ∈ farDom τ δ₁ N, ∀ v ∈ farDom τ δ₁ N,
      |ζ N u ω - ζ N v ω| ≤ (N : ℝ) ^ (4 : ℝ) * ‖u - v‖ := by
    intro N ω _ u hu v hv
    have h4 : (N : ℝ) ^ (4 : ℝ) = (N : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [h4]
    obtain ⟨hN1, hN4, hu1, -, -⟩ := hdom N u hu
    obtain ⟨-, -, hv1, -, -⟩ := hdom N v hv
    simp only [hζ]
    have hp0 : 0 ≤ (N : ℝ) ^ ((K + 28) * δ₁) := Real.rpow_nonneg (by linarith) _
    have hpN : (N : ℝ) ^ ((K + 28) * δ₁) ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 (show (K + 28) * δ₁ ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have e : (N : ℝ) ^ ((K + 28) * δ₁) * (1 / N + 1 / ((N : ℝ) * u.im) ^ 2) -
        (N : ℝ) ^ ((K + 28) * δ₁) * (1 / N + 1 / ((N : ℝ) * v.im) ^ 2) =
        (N : ℝ) ^ ((K + 28) * δ₁) * (1 / ((N : ℝ) * u.im) ^ 2 - 1 / ((N : ℝ) * v.im) ^ 2) := by
      ring
    rw [e, abs_mul, abs_of_nonneg hp0]
    have hl := Far_inv_sq_lip N u.im v.im hN1 hu1 hv1
    have him : |u.im - v.im| ≤ ‖u - v‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have h3 : 0 ≤ ‖u - v‖ := norm_nonneg _
    have h5 : |1 / ((N : ℝ) * u.im) ^ 2 - 1 / ((N : ℝ) * v.im) ^ 2| ≤ 2 * N * ‖u - v‖ :=
      hl.trans (mul_le_mul_of_nonneg_left him (by linarith))
    calc (N : ℝ) ^ ((K + 28) * δ₁) * |1 / ((N : ℝ) * u.im) ^ 2 - 1 / ((N : ℝ) * v.im) ^ 2|
        ≤ N * (2 * N * ‖u - v‖) := mul_le_mul hpN h5 (abs_nonneg _) (by linarith)
      _ = (2 * (N : ℝ) ^ 2) * ‖u - v‖ := by ring
      _ ≤ (N : ℝ) ^ 4 * ‖u - v‖ := by
          have := Far_poly4 N hN4
          exact mul_le_mul_of_nonneg_right this h3
  have hζ0 : ∀ N ω, 1 ≤ N → ∀ u ∈ farDom τ δ₁ N, (N : ℝ) ^ (-(1 : ℝ)) ≤ ζ N u ω := by
    intro N ω hN u hu
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    simp only [hζ]
    rw [Real.rpow_neg_one, ← one_div]
    have hp : (1 : ℝ) ≤ (N : ℝ) ^ ((K + 28) * δ₁) := Real.one_le_rpow hN1 (by positivity)
    have h0 : 0 ≤ 1 / ((N : ℝ) * u.im) ^ 2 := by positivity
    have h1 : 0 ≤ 1 / (N : ℝ) := by positivity
    nlinarith
  have hPS : PrecS μ (fun N (u : farDom τ δ₁ N) => ξ N u) (fun N u => ζ N u) := by
    intro τ'' hτ'' D'' hD''
    obtain ⟨N₃, hN₃⟩ := hsharp τ'' hτ'' D'' hD''
    refine ⟨N₃, fun N hN u => le_trans (measure_mono fun h hh => ?_)
      (hN₃ N hN ⟨u.1, Far_lev_top τ δ₁ hδ N u.1 u.2⟩)⟩
    have hh' : (N : ℝ) ^ τ'' * ζ N u h < ξ N u h := hh
    have hle : ξ N u h ≤ ‖ntr (res (Matrix.of h + lam D N (A N)) u -
        MExt (lam D N (A N)) u)‖ := by
      simp only [hξ]
      split_ifs
      · exact le_rfl
      · exact norm_nonneg _
    show (N : ℝ) ^ τ'' * ((N : ℝ) ^ ((K + 28) * δ₁) * (1 / N + 1 / ((N : ℝ) * u.1.im) ^ 2)) <
      ‖ntr (res (Matrix.of h + lam D N (A N)) u.1 - MExt (lam D N (A N)) u.1)‖
    exact lt_of_lt_of_le hh' hle
  obtain ⟨N₀, hN₀⟩ := precS_precU_net μ (farDom τ δ₁) 1 4 1 hS ξ ζ hLξ hLζ hζ0 hPS τ' hτ' D'
    hD'
  refine ⟨max N₀ (max NΛ 3), fun N hN => ?_⟩
  have hU := hN₀ N (le_trans (le_max_left _ _) hN)
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
  refine le_trans (measure_mono (t := {ω | ∃ u : farDom τ δ₁ N,
      (N : ℝ) ^ τ' * ζ N u ω < ξ N u ω} ∪ {h | ¬ (Matrix.of h).IsHermitian}) ?_)
    ((measure_union_le _ _).trans (le_trans (add_le_add hU (le_of_eq hnull))
      (le_of_eq (add_zero _))))
  rintro h ⟨z, hz, hlt⟩
  by_cases hH : (Matrix.of h).IsHermitian
  · refine Or.inl ⟨⟨z, hz⟩, ?_⟩
    have hc : max NΛ 3 ≤ N ∧ (Matrix.of h).IsHermitian := ⟨le_trans (le_max_right _ _) hN, hH⟩
    show (N : ℝ) ^ τ' * ζ N z h < ξ N z h
    simp only [hξ, hζ, hc, and_self, ↓reduceIte]
    exact hlt
  · exact Or.inr hH

/-! ### Eigenvalues far from the spectrum -/

/-- The eigenvectors of a Hermitian matrix are unit vectors: `Σ_i |v_k(i)|² = 1`. -/
private lemma Far_col_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (k : ι) : ∑ i, ‖(hX.eigenvectorBasis k) i‖ ^ 2 = 1 := by
  have h := hX.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

/-- A nonzero `λ_k(X)` is an eigenvalue of the Hermitian matrix `X`. -/
private lemma Far_eigK_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (k : ℕ)
    (h : eigK X k ≠ 0) : ∃ (hX : X.IsHermitian) (i : ι), hX.eigenvalues i = eigK X k := by
  unfold eigK at h ⊢
  split_ifs at h ⊢ with hk
  · unfold eigs at h ⊢
    split_ifs at h ⊢ with hX
    · exact ⟨hX, (Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨k - 1, hk⟩,
        by simp [Matrix.IsHermitian.eigenvalues]⟩
    · exact absurd rfl h
  · exact absurd rfl h

/-- `|λ_i| ≤ ‖X‖` for an eigenvalue of a Hermitian matrix. -/
private lemma Far_eig_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (i : ι) : |hX.eigenvalues i| ≤ opNorm X := by
  rw [hX.eigenvalues_eq i]
  exact (Complex.abs_re_le_norm _).trans
    (Far_form_le X _ _ (Far_col_norm hX i).le (Far_col_norm hX i).le)

/-- `Im⟨G(λ + iη)⟩ ≥ (nη)⁻¹` for an eigenvalue `λ` of a Hermitian matrix of size `n`
(`res_eq_sum_eig`: `Im G_{ii} = Σ_k |v_k(i)|² η/|λ_k - z|²`). -/
private lemma Far_im_ntr {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (i₀ : ι) (η : ℝ) (hη : 0 < η) :
    1 / ((Fintype.card ι : ℝ) * η) ≤
      (ntr (res X ((hX.eigenvalues i₀ : ℂ) + (η : ℂ) * Complex.I))).im := by
  set z : ℂ := (hX.eigenvalues i₀ : ℂ) + (η : ℂ) * Complex.I with hz
  have hz0 : 0 < z.im := by simp [hz, hη]
  have key : ∀ i k, ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k * starRingEnd ℂ ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) / ((hX.eigenvalues k : ℂ) - z)).im =
      Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) * (η / Complex.normSq ((hX.eigenvalues k : ℂ) - z)) := by
    intro i k
    rw [Complex.mul_conj, div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im]
    simp [hz]
  have hn : ∀ i k, 0 ≤ Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i k) * (η / Complex.normSq ((hX.eigenvalues k : ℂ) - z)) :=
    fun i k => mul_nonneg (Complex.normSq_nonneg _) (div_nonneg hη.le (Complex.normSq_nonneg _))
  have hw : Complex.normSq ((hX.eigenvalues i₀ : ℂ) - z) = η ^ 2 := by
    rw [hz, Complex.normSq_apply]
    simp
    ring
  have hdiag : ∀ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i i₀) / η ≤ (res X z i i).im := by
    intro i
    rw [res_eq_sum_eig X hX z hz0 i i, Complex.im_sum]
    simp only [key]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ i₀))
    rw [hw]
    field_simp
  have hcol : ∑ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i i₀) = 1 := by
    rw [← Far_col_norm hX i₀]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]
    rfl
  have htr : (ntr (res X z)).im = ((Fintype.card ι : ℝ))⁻¹ * ∑ i, (res X z i i).im := by
    unfold ntr Matrix.trace
    rw [show ((Fintype.card ι : ℂ))⁻¹ = ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      Complex.im_ofReal_mul, Complex.im_sum]
    rfl
  rw [htr]
  have hsum : 1 / η ≤ ∑ i, (res X z i i).im := by
    calc 1 / η = ∑ i, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i i₀) / η := by rw [← Finset.sum_div, hcol]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hdiag i
  have e : 1 / ((Fintype.card ι : ℝ) * η) = ((Fintype.card ι : ℝ))⁻¹ * (1 / η) := by
    rw [one_div, mul_inv, one_div]
  rw [e]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The exclusion inequality at `η = N^{-3/4}` with the loss `N^{1/16} N^{1/16}`:
`N^{1/8}(1/N + (Nη)⁻²) + η/7 < (DNη)⁻¹` once `N^{1/8} ≥ 3D`. -/
private lemma Far_R7 (N D : ℝ) (hD : 1 ≤ D) (hN : 0 < N) (ht : 3 * D ≤ N ^ (1 / 8 : ℝ)) :
    N ^ (1 / 16 : ℝ) * (N ^ (1 / 16 : ℝ) * (1 / N + 1 / (N * N ^ (-1 + 1 / 4 : ℝ)) ^ 2)) +
      N ^ (-1 + 1 / 4 : ℝ) / 7 < 1 / (D * N * N ^ (-1 + 1 / 4 : ℝ)) := by
  have h16 : N ^ (1 / 16 : ℝ) * (N ^ (1 / 16 : ℝ) * (1 / N + 1 / (N * N ^ (-1 + 1 / 4 : ℝ)) ^ 2)) =
      N ^ (1 / 8 : ℝ) * (1 / N + 1 / (N * N ^ (-1 + 1 / 4 : ℝ)) ^ 2) := by
    rw [← mul_assoc, ← Real.rpow_add hN]
    norm_num
  have hN8 : N = (N ^ (1 / 8 : ℝ)) ^ 8 := by
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num
  have hη : N ^ (-1 + 1 / 4 : ℝ) = 1 / (N ^ (1 / 8 : ℝ)) ^ 6 := by
    rw [show (-1 + 1 / 4 : ℝ) = -((1 / 8) * ((6 : ℕ) : ℝ)) by norm_num, Real.rpow_neg hN.le,
      Real.rpow_mul_natCast hN.le]
    ring
  rw [h16, hη]
  generalize N ^ (1 / 8 : ℝ) = t at ht hN8 ⊢
  subst hN8
  have ht3 : 3 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have key : t * (1 / t ^ 8 + 1 / (t ^ 8 * (1 / t ^ 6)) ^ 2) + 1 / t ^ 6 / 7 =
      (7 + 7 * t ^ 4 + t) / (7 * t ^ 7) := by
    field_simp
  have key2 : 1 / (D * t ^ 8 * (1 / t ^ 6)) = 1 / (D * t ^ 2) := by
    field_simp
  rw [key, key2, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h2 : 9 ≤ t ^ 2 := by nlinarith
  have h4 : 81 ≤ t ^ 4 := by nlinarith
  have h3 : 1 ≤ t ^ 3 := by nlinarith
  have h5 : t ≤ t ^ 4 := by nlinarith
  have h6 : 3 * D * t ^ 4 ≤ t ^ 5 := by
    have := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ t ^ 4)
    nlinarith
  have h7 : D * (7 + 7 * t ^ 4 + t) < 7 * t ^ 5 := by nlinarith
  have h8 : 0 < t ^ 2 := by positivity
  have := mul_lt_mul_of_pos_right h7 h8
  nlinarith

/-- No eigenvalue of `X = H' + Λ` has modulus `≥ 4`, outside an event of probability `≤ N^{-D'}`,
uniformly over the class with `θ ∈ [0, 1]` and `‖A‖ ≤ N^{-δ_A}`. -/
theorem far_no_eigenvalue (D : ℕ) (hD : 1 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        μ {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧ 4 ≤ |eigK (Matrix.of h + lam D N A) k|} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro D' hD'
  obtain ⟨L, hL1, hL⟩ := far_aver_seq
  have hL0 : 0 < L := by linarith
  set δ₁ : ℝ := 1 / (16 * L) with hδ₁
  have hδ : 0 < δ₁ := by positivity
  have hLδ : L * δ₁ = 1 / 16 := by
    rw [hδ₁]
    field_simp
  obtain ⟨Nn, hNn⟩ := opNorm_noise_le D C (δ₁ / 2) (by positivity) (D' + 1) (by linarith)
  refine (uniform_of_seq
    (X := fun N => ℝ × Measure (Idx D N → Idx D N → ℂ) × Matrix (Fin N) (Fin N) ℂ)
    (fun N => {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ LLClass D N C x.1 x.2.1 ∧
      opNorm x.2.2 ≤ (N : ℝ) ^ (-δA)})
    (fun N x => ¬ x.2.1 {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
      4 ≤ |eigK (Matrix.of h + lam D N x.2.2) k|} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')))
    ?hpad ?hseq).imp fun N₀ hN₀ N hN θ hθ0 hθ1 μ hμ A hA =>
      not_not.mp (hN₀ N hN (θ, μ, A) ⟨hθ0, hθ1, hμ, hA⟩)
  case hpad =>
    rintro N₁ hN₁ ⟨⟨θ, μ₁, A₁⟩, hθ0, hθ1, hμ₁, -⟩ N
    obtain ⟨μ, hμ⟩ := llClass_pad D N₁ hN₁ C θ μ₁ hμ₁ N
    refine ⟨(θ, μ, 0), hθ0, hθ1, hμ, ?_⟩
    have h0 : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
      unfold opNorm
      rw [map_zero, norm_zero]
    show opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ (N : ℝ) ^ (-δA)
    rw [h0]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  case hseq =>
    intro x hx
    have hs : LLSeq D δA C (fun N => (x N).1) (fun N => (x N).2.1) (fun N => (x N).2.2) :=
      ⟨hD, hδA, fun N => ⟨(hx N).1, (hx N).2.1⟩, fun N => (hx N).2.2.1, fun N => (hx N).2.2.2⟩
    obtain ⟨N₁, hN₁⟩ := hL D δA (1 / 4) δ₁ C _ _ _ hs (by norm_num) le_rfl hδ.le
      (by rw [hLδ]; norm_num) (1 / 16) (by norm_num) (D' + 1) (by linarith)
    obtain ⟨NΛ, hNΛ⟩ := Far_lam_small hs
    obtain ⟨N₂, hN₂⟩ := Far_ev 2 (δ₁ / 2) (by positivity)
    obtain ⟨N₃, hN₃⟩ := Far_ev (3 * D) (1 / 8) (by norm_num)
    refine ⟨max (max N₁ NΛ) (max (max N₂ N₃) (max Nn 2)), fun N hN => ?_⟩
    have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNΛ' : NΛ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN2' : N₂ ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hN
    have hN3' : N₃ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hN
    have hNn' : Nn ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
    have hN2 : (2 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_max_right _ _))) hN
    obtain ⟨hN1, hΛ1⟩ := hNΛ N hNΛ'
    have hN0 : (0 : ℝ) < N := by linarith
    have hΛh := lam_isHermitian D N (x N).2.2
    have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, by exact_mod_cast hN1⟩)⟩
    have hnorm := hNn N hNn' (x N).1 (x N).2.1 (hx N).2.2.1
    have haver := hN₁ N hN1'
    have htwo : ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
      have h2 := Far_count N 2 1 hN1 (by push_cast; linarith) D'
      rw [← two_mul]
      simpa using h2
    show ¬¬ _
    rw [not_not]
    refine le_trans (measure_mono (t := {h | ∃ z ∈ farDom (1 / 4) δ₁ N,
        (N : ℝ) ^ (1 / 16 : ℝ) * ((N : ℝ) ^ (L * δ₁) * (1 / N + 1 / ((N : ℝ) * z.im) ^ 2)) <
          ‖ntr (res (Matrix.of h + lam D N (x N).2.2) z - MExt (lam D N (x N).2.2) z)‖} ∪
        {h | (N : ℝ) ^ (δ₁ / 2) < opNorm (Matrix.of h)}) ?_)
      ((measure_union_le _ _).trans ((add_le_add haver hnorm).trans htwo))
    rintro h ⟨k, -, -, hk4⟩
    by_cases hb : (N : ℝ) ^ (δ₁ / 2) < opNorm (Matrix.of h)
    · exact Or.inr hb
    refine Or.inl ?_
    have hne : eigK (Matrix.of h + lam D N (x N).2.2) k ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hk4
      norm_num at hk4
    obtain ⟨hX, i, hi⟩ := Far_eigK_mem _ k hne
    set η : ℝ := (N : ℝ) ^ (-1 + 1 / 4 : ℝ) with hηdef
    have hη0 : 0 < η := Real.rpow_pos_of_pos hN0 _
    set z : ℂ := (hX.eigenvalues i : ℂ) + (η : ℂ) * Complex.I with hzdef
    have hzre : z.re = hX.eigenvalues i := by simp [hzdef]
    have hzim : z.im = η := by simp [hzdef]
    have h4 : 4 ≤ |z.re| := by rw [hzre, hi]; exact hk4
    -- the location: `|λ| ≤ ‖H'‖ + ‖Λ‖ ≤ N^{δ₁/2} + 1/10 ≤ N^{δ₁}`
    have hloc : |z.re| ≤ (N : ℝ) ^ δ₁ := by
      rw [hzre]
      have h1 := Far_eig_le hX i
      have h2 := opNorm_add_le (Matrix.of h) (lam D N (x N).2.2)
      have h3 := hN₂ N hN2'
      have h5 : (N : ℝ) ^ δ₁ = (N : ℝ) ^ (δ₁ / 2) * (N : ℝ) ^ (δ₁ / 2) := by
        rw [← Real.rpow_add hN0]
        ring_nf
      have hb' := le_of_not_gt hb
      nlinarith
    have hzD : z ∈ farDom (1 / 4) δ₁ N := by
      refine ⟨h4, hloc, by rw [hzim], ?_⟩
      rw [hzim]
      have : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
      linarith
    refine ⟨z, hzD, ?_⟩
    have hz0 : 0 < z.im := by rw [hzim]; exact hη0
    -- `Im⟨G⟩ ≥ (DNη)⁻¹` and `Im⟨M⟩ = Im m ≤ η/7`
    have hIm := Far_im_ntr hX i η hη0
    have hcard : (Fintype.card (Idx D N) : ℝ) = D * N := by
      simp [Fintype.card_prod, Fintype.card_fin]
    rw [hcard] at hIm
    have hm := (MExt_far (lam D N (x N).2.2) hΛh hΛ1 z hz0 h4).2.2
    rw [(MExt_spec (lam D N (x N).2.2) hΛh z hz0.ne').1, hzim] at hm
    have hlow : 1 / ((D : ℝ) * N * η) - η / 7 ≤
        ‖ntr (res (Matrix.of h + lam D N (x N).2.2) z - MExt (lam D N (x N).2.2) z)‖ := by
      rw [Far_ntr_sub]
      refine le_trans ?_ (Complex.abs_im_le_norm _ |>.trans' (le_abs_self _))
      rw [Complex.sub_im]
      linarith
    have hR := Far_R7 N D (by exact_mod_cast hD) hN0 (hN₃ N hN3')
    rw [← hηdef] at hR
    rw [hLδ, hzim]
    linarith


end RBMTransitionEdge

end
