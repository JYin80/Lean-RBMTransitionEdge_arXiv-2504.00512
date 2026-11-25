module

public import RBMTransitionEdge.Det.QuantSpacing
public import RBMTransitionEdge.LocalLaw.Wigner

@[expose] public section

/-!
# Two blocks rarely have nearby eigenvalues

The level repulsion (5.14) [Wegner12] for one block, as a hypothesis (external input EI-2), and
(5.11) [eq:probab12] for two different blocks of (1.3) [matrix_H], from (5.12) [rigidity12].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

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

/-- The map `h ↦ ‖h - B‖` from arrays to the operator norm is continuous. -/
private lemma Repulsion_cont_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    Continuous fun h : ι → ι → ℂ => opNorm (Matrix.of h - B) := by
  have h1 : Continuous fun h : ι → ι → ℂ => (Matrix.of h - B : Matrix ι ι ℂ) := by
    fun_prop
  have h2 : Continuous fun X : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) X :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toLinearMap
  exact continuous_norm.comp (h2.comp h1)

/-- The `k`-th largest eigenvalue is a measurable function of the array of entries: it is `0` off
the closed set of Hermitian arrays and `1`-Lipschitz on it (Weyl's inequality). -/
private lemma Repulsion_meas_eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Measurable fun h : ι → ι → ℂ => eigK (Matrix.of h) k := by
  set S : Set (ι → ι → ℂ) := {h | (Matrix.of h).IsHermitian} with hS
  have hSc : IsClosed S := by
    have : S = ⋂ i, ⋂ j, {h : ι → ι → ℂ | star (h j i) = h i j} := by
      ext h
      simp only [hS, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hh i j
        exact hh.apply i j
      · intro hh
        exact Matrix.IsHermitian.ext fun i j => hh i j
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact isClosed_eq (continuous_star.comp ((continuous_apply i).comp (continuous_apply j)))
      ((continuous_apply j).comp (continuous_apply i))
  have hzero : ∀ h : ι → ι → ℂ, h ∉ S → eigK (Matrix.of h) k = 0 := by
    intro h hh
    have : ¬ (Matrix.of h).IsHermitian := hh
    simp [eigK, eigs, this]
  have hcont : ContinuousOn (fun h : ι → ι → ℂ => eigK (Matrix.of h) k) S := by
    intro h₀ hh₀
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have hg : Filter.Tendsto (fun h : ι → ι → ℂ => opNorm (Matrix.of h - Matrix.of h₀))
        (𝓝[S] h₀) (𝓝 0) := by
      have := ((Repulsion_cont_opNorm (Matrix.of h₀)).tendsto h₀).mono_left
        (nhdsWithin_le_nhds (s := S))
      have h0 : opNorm (Matrix.of h₀ - Matrix.of h₀) = 0 := by
        rw [sub_self]; unfold opNorm; rw [map_zero, norm_zero]
      rwa [h0] at this
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hg
    refine eventually_nhdsWithin_of_forall fun h hh => ?_
    rw [Real.dist_eq]
    have := eigK_add_sub_le (Matrix.of h₀) (Matrix.of h - Matrix.of h₀) hh₀
      (Matrix.IsHermitian.sub hh hh₀) k
    rwa [add_sub_cancel] at this
  have hpw : (fun h : ι → ι → ℂ => eigK (Matrix.of h) k) =
      S.piecewise (fun h : ι → ι → ℂ => eigK (Matrix.of h) k) (fun _ => 0) := by
    funext h
    by_cases hh : h ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ hh]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hh, hzero h hh]
  rw [hpw]
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const hSc.measurableSet

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma Repulsion_meas_wig (n : ℕ) (i j : Fin n) :
    Measurable fun c : Coords n => wig n c i j := by
  unfold wig
  by_cases h1 : i = j
  · simp only [h1, ite_true]
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp measurable_fst))
  · by_cases h2 : i < j
    · simp only [h1, h2, ite_true, ite_false]
      exact measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
    · simp only [h1, h2, ite_false]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)))

/-- The `i`-th largest eigenvalue of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma Repulsion_meas_eig (n i : ℕ) : Measurable fun c : Coords n => eigK (wig n c) i := by
  have h1 : Measurable fun c : Coords n => Matrix.of.symm (wig n c) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => Repulsion_meas_wig n p q
  have h2 := (Repulsion_meas_eigK (ι := Fin n) i).comp h1
  convert h2 using 2 with c
  rfl

/-- The semicircle density `ρ_sc` of (2.18) [eq:semidensity] has total mass one (the case `Λ = 0`
of Definition 2.7 [defn_Mm]). -/
private lemma Repulsion_rhoSc_total : ∫ t, rhoSc t = 1 := by
  have h0 : opNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 1 / 10 := by
    unfold opNorm; simp
  have := (rho_stieltjes (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero h0).2.2.2.1
  rwa [(rho_zero (ι := Fin 1)).2.1] at this

/-- `ρ_sc` vanishes outside `(-2, 2)`. -/
private lemma Repulsion_rhoSc_zero (t : ℝ) (ht : t ∉ Set.Ioo (-2 : ℝ) 2) : rhoSc t = 0 := by
  unfold rhoSc
  by_cases h : t ∈ Set.Icc (-2 : ℝ) 2
  · simp only [h, ↓reduceIte]
    have : t ^ 2 = 4 := by
      rcases h with ⟨h1, h2⟩
      have : t = -2 ∨ t = 2 := by
        by_contra hne
        have hne' := not_or.1 hne
        exact ht ⟨lt_of_le_of_ne h1 (Ne.symm hne'.1), lt_of_le_of_ne h2 hne'.2⟩
      rcases this with rfl | rfl <;> norm_num
    rw [this]; simp
  · simp [h]

/-- The quantiles `γ_k^{sc}` of (2.20) [eq:gammak] of the semicircle law with `n` particles
decrease in `k ∈ ⟦1, n⟧`. -/
private lemma Repulsion_quant_anti {n k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n) :
    quant rhoSc n m ≤ quant rhoSc n k := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (hk.trans (hkm.trans hmn))
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  unfold quant
  refine csSup_le_csSup ?_ ?_ ?_
  · refine ⟨2, fun x hx => ?_⟩
    by_contra hlt
    have hlt := lt_of_not_ge hlt
    have h0 : ∫ t in Set.Ioi x, rhoSc t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
        Repulsion_rhoSc_zero t fun hm => absurd hm.2 (not_lt.2 (hlt.trans ht).le)
    have : ((k : ℝ) - 1 / 2) / n ≤ 0 := h0 ▸ hx
    have : 0 < ((k : ℝ) - 1 / 2) / n := by apply div_pos <;> linarith
    linarith
  · refine ⟨-2 - 1, ?_⟩
    have h1 : ∫ t in Set.Ioi (-2 - 1 : ℝ), rhoSc t = 1 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero, Repulsion_rhoSc_total]
      intro t ht
      exact Repulsion_rhoSc_zero t fun hm => ht (by simp only [Set.mem_Ioi]; linarith [hm.1])
    change ((m : ℝ) - 1 / 2) / n ≤ ∫ t in Set.Ioi (-2 - 1 : ℝ), rhoSc t
    rw [h1, div_le_one (by linarith)]
    linarith
  · intro x hx
    have hx' : ((m : ℝ) - 1 / 2) / n ≤ ∫ t in Set.Ioi x, rhoSc t := hx
    change ((k : ℝ) - 1 / 2) / n ≤ ∫ t in Set.Ioi x, rhoSc t
    refine le_trans ?_ hx'
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `𝔯(k) ≤ k` of (1.4) [eq:rk]. -/
private lemma Repulsion_rk_le (D N k : ℕ) : rk D N k ≤ k := by
  unfold rk
  exact_mod_cast min_le_left _ _

/-- `𝔯(k) ≥ 1` of (1.4) [eq:rk] for `k ∈ ⟦1, DN⟧`. -/
private lemma Repulsion_one_le_rk (D N k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ D * N) : 1 ≤ rk D N k := by
  unfold rk
  have : 1 ≤ min k (D * N + 1 - k) := le_min hk (by omega)
  exact_mod_cast this

/-- `𝔯_{DN}(Dj) ≤ D 𝔯_N(j)` of (1.4) [eq:rk]: the index `Dj` of (5.13) [eq:gammak2] is at most
`D` times as close to the edge as `j` is. -/
private lemma Repulsion_rk_mul_le (D N j : ℕ) (hD : 1 ≤ D) (hj : j ≤ N) :
    rk D N (D * j) ≤ (D : ℝ) * rk 1 N j := by
  unfold rk
  have key : min (D * j) (D * N + 1 - D * j) ≤ D * min j (1 * N + 1 - j) := by
    rcases le_total j (1 * N + 1 - j) with h | h
    · rw [min_eq_left h]
      exact min_le_left _ _
    · rw [min_eq_right h]
      refine le_trans (min_le_right _ _) ?_
      obtain ⟨u, hu⟩ : ∃ u, 1 * N + 1 = j + u := ⟨1 * N + 1 - j, by omega⟩
      have hu' : 1 * N + 1 - j = u := by omega
      rw [hu']
      have e : D * N + D = D * j + D * u := by
        rw [← mul_add]
        have : N + 1 = j + u := by omega
        rw [← mul_add_one, this]
      omega
  exact_mod_cast key

/-- `t ^ (-1/3)` cubed is `t⁻¹`. -/
private lemma Repulsion_cube (t : ℝ) (ht : 0 ≤ t) : (t ^ (-(1 / 3 : ℝ))) ^ 3 = t⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num
  exact Real.rpow_neg_one t

/-- The arithmetic of the separation: for `G = x ^ 6 ≥ 1`, `g ≥ G / 2`, `4 K < c x` and `ρ ≥ 1`,
`K x³ ρ^{-1/3} < c g (ρ + G)^{-1/3}`. -/
private lemma Repulsion_arith {K c x ρ G : ℝ} {g : ℕ} (hc : 0 < c) (hx : 0 < x)
    (hρ : 1 ≤ ρ) (hG : G = x ^ 6) (hG1 : 1 ≤ G) (hg : G / 2 ≤ g) (hKx : 4 * K < c * x) :
    K * x ^ 3 * ρ ^ (-(1 / 3 : ℝ)) < c * g * (ρ + G) ^ (-(1 / 3 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hρG : 0 < ρ + G := by linarith
  set t : ℝ := ρ ^ (-(1 / 3 : ℝ)) with ht_def
  set s : ℝ := (ρ + G) ^ (-(1 / 3 : ℝ)) with hs_def
  have ht : 0 < t := Real.rpow_pos_of_pos hρ0 _
  have hs : 0 < s := Real.rpow_pos_of_pos hρG _
  have ht3 : t ^ 3 = ρ⁻¹ := Repulsion_cube ρ hρ0.le
  have hs3 : s ^ 3 = (ρ + G)⁻¹ := Repulsion_cube (ρ + G) hρG.le
  have hxs : t ≤ 2 * x ^ 2 * s := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    have e : (2 * x ^ 2 * s) ^ 3 = 8 * G * (ρ + G)⁻¹ := by
      rw [mul_pow, mul_pow, hs3, hG]; ring
    rw [ht3, e]
    have hρi : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
    have e2 : (ρ + G) * ρ⁻¹ = 1 + G * ρ⁻¹ := by field_simp
    have h1 : (ρ + G) * ρ⁻¹ ≤ 8 * G := by nlinarith [inv_pos.2 hρ0]
    calc ρ⁻¹ = (ρ + G)⁻¹ * ((ρ + G) * ρ⁻¹) := by field_simp
      _ ≤ (ρ + G)⁻¹ * (8 * G) := by gcongr
      _ = 8 * G * (ρ + G)⁻¹ := by ring
  have h1 : c * (G / 2) * s ≤ c * g * s := by gcongr
  have h2 : c * x ^ 4 * t / 4 ≤ c * (G / 2) * s := by
    have e : c * (G / 2) * s = c * x ^ 4 * (2 * x ^ 2 * s) / 4 := by rw [hG]; ring
    rw [e]
    have : c * x ^ 4 * t ≤ c * x ^ 4 * (2 * x ^ 2 * s) := by gcongr
    linarith
  have h3 : K * x ^ 3 * t < c * x ^ 4 * t / 4 := by
    have : 0 < x ^ 3 * (c * x - 4 * K) * t :=
      mul_pos (mul_pos (pow_pos hx 3) (sub_pos.2 hKx)) ht
    nlinarith
  linarith

/-- The tolerance of the first condition and of (5.12) [rigidity12] is at most
`(1 + D^{1/3}) N^{τ-2/3} 𝔯(c)^{-1/3}` for any index `c` that is at least as close to an edge as
`k` and `Dj` are. -/
private lemma Repulsion_tol (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (τ : ℝ) (j k c : ℕ) (hj : j ≤ N)
    (hρc : 0 < rk D N c) (hc1 : rk D N c ≤ rk D N k) (hc2 : rk D N c ≤ rk D N (D * j)) :
    (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) +
        (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N j ^ (-(1 / 3 : ℝ))) ≤
      (1 + (D : ℝ) ^ (1 / 3 : ℝ)) * ((N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ))) *
        rk D N c ^ (-(1 / 3 : ℝ)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hk : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ rk D N c ^ (-(1 / 3 : ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos hρc ?_ (by norm_num)
    exact hc1.trans (Repulsion_rk_le D N k)
  have hrj : rk 1 N j ^ (-(1 / 3 : ℝ)) ≤ (D : ℝ) ^ (1 / 3 : ℝ) * rk D N c ^ (-(1 / 3 : ℝ)) := by
    have hle : rk D N c / D ≤ rk 1 N j := by
      rw [div_le_iff₀ hDpos, mul_comm]
      exact (hc2.trans (Repulsion_rk_mul_le D N j hD hj))
    have hpos : 0 < rk D N c / D := div_pos hρc hDpos
    have := Real.rpow_le_rpow_of_nonpos hpos hle (show -(1 / 3 : ℝ) ≤ 0 by norm_num)
    refine this.trans (le_of_eq ?_)
    rw [Real.div_rpow hρc.le hDpos.le, Real.rpow_neg hDpos.le, div_eq_mul_inv, inv_inv, mul_comm]
  have hNa : (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) = (N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [add_comm]
    exact Real.rpow_add (by exact_mod_cast hN) _ _
  have ha : 0 ≤ (N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  rw [hNa]
  calc (N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) +
        (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N j ^ (-(1 / 3 : ℝ)))
      = ((N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ))) * ((k : ℝ) ^ (-(1 / 3 : ℝ)) +
          rk 1 N j ^ (-(1 / 3 : ℝ))) := by ring
    _ ≤ ((N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ))) * (rk D N c ^ (-(1 / 3 : ℝ)) +
          (D : ℝ) ^ (1 / 3 : ℝ) * rk D N c ^ (-(1 / 3 : ℝ))) := by gcongr
    _ = (1 + (D : ℝ) ^ (1 / 3 : ℝ)) * ((N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ))) *
        rk D N c ^ (-(1 / 3 : ℝ)) := by ring

/-- Between the indices `c` and `o` at distance at least `g` there is an index `m` at distance
exactly `g` from `c` whose quantile is at least as close to `γ_c` as `γ_o` is. -/
private lemma Repulsion_far_point {n c o g : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n) (ho : 1 ≤ o)
    (hon : o ≤ n) (hg : (g : ℝ) ≤ |(o : ℝ) - c|) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ |(m : ℝ) - c| = g ∧
      |quant rhoSc n m - quant rhoSc n c| ≤ |quant rhoSc n o - quant rhoSc n c| := by
  rcases le_total c o with h | h
  · have hco : (c : ℝ) ≤ o := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)] at hg
    have hgo : c + g ≤ o := by
      have : (c : ℝ) + g ≤ o := by linarith
      exact_mod_cast this
    refine ⟨c + g, by omega, by omega, ?_, ?_⟩
    · push_cast
      rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg g)]
    · have h1 := Repulsion_quant_anti (n := n) hc (Nat.le_add_right c g) (by omega)
      have h2 := Repulsion_quant_anti (n := n) (by omega : 1 ≤ c + g) hgo hon
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · have hco : (o : ℝ) ≤ c := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)] at hg
    have hgo : o + g ≤ c := by
      have : (o : ℝ) + g ≤ c := by linarith
      exact_mod_cast this
    refine ⟨c - g, by omega, by omega, ?_, ?_⟩
    · have : ((c - g : ℕ) : ℝ) = (c : ℝ) - g := by
        rw [Nat.cast_sub (by omega)]
      rw [this, sub_sub_cancel_left, abs_neg, abs_of_nonneg (Nat.cast_nonneg g)]
    · have h1 := Repulsion_quant_anti (n := n) ho (by omega : o ≤ c - g) (by omega)
      have h2 := Repulsion_quant_anti (n := n) (by omega : 1 ≤ c - g) (by omega : c - g ≤ c) hcn
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- The separation: for `N` large, indices `c, o ∈ ⟦1, DN⟧` with `|o - c| ≥ N^{2τ}` have
quantiles `γ_o, γ_c` farther apart than `(1 + D^{1/3}) N^{τ-2/3} 𝔯(c)^{-1/3}`, from the lower
bound of `quant_spacing_sc` centred at `c` and the monotonicity of the quantile. -/
private lemma Repulsion_far (D : ℕ) (hD : 2 ≤ D) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1 / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ c o : ℕ, 1 ≤ c → c ≤ D * N → 1 ≤ o → o ≤ D * N →
      (N : ℝ) ^ (2 * τ) ≤ |(o : ℝ) - c| →
        (1 + (D : ℝ) ^ (1 / 3 : ℝ)) * ((N : ℝ) ^ τ * (N : ℝ) ^ (-(2 / 3 : ℝ))) *
            rk D N c ^ (-(1 / 3 : ℝ)) <
          |quant rhoSc (D * N) o - quant rhoSc (D * N) c| := by
  obtain ⟨c', C', hc', hC', N₁, h⟩ := quant_spacing_sc D hD (2 * τ) (by positivity) (by linarith)
  set K : ℝ := 1 + (D : ℝ) ^ (1 / 3 : ℝ) with hK
  have hev : ∀ᶠ N : ℕ in atTop, 4 * K / c' < (N : ℝ) ^ (τ / 3) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 3)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max N₁ N₂) 1, fun N hN c o hc1 hcn ho1 hon hdist => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hx := hN₂ N hN2
  set x : ℝ := (N : ℝ) ^ (τ / 3) with hx_def
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hxτ : x ^ 3 = (N : ℝ) ^ τ := by
    rw [hx_def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hG : (N : ℝ) ^ (2 * τ) = x ^ 6 := by
    rw [hx_def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  set G : ℝ := (N : ℝ) ^ (2 * τ) with hGdef
  have hG1 : 1 ≤ G := Real.one_le_rpow hNr (by linarith)
  set g : ℕ := ⌊G⌋₊ with hg_def
  have hg1 : 1 ≤ g := (Nat.one_le_floor_iff G).2 hG1
  have hgG : (g : ℝ) ≤ G := Nat.floor_le (by linarith)
  have hgG2 : G / 2 ≤ g := by
    have := Nat.lt_floor_add_one G
    have hg1' : (1 : ℝ) ≤ g := by exact_mod_cast hg1
    linarith
  obtain ⟨m, hm1, hmn, hmd, hmq⟩ := Repulsion_far_point hc1 hcn ho1 hon (hgG.trans hdist)
  have hlow := (h N hN1 m c hm1 hmn hc1 hcn (by rw [hmd]; exact hgG)).2
  rw [hmd] at hlow
  have hρ := Repulsion_one_le_rk D N c hc1 hcn
  have hKx : 4 * K < c' * x := by
    have := hx
    rw [div_lt_iff₀ hc'] at this
    linarith
  have hK0 : 0 ≤ K := by positivity
  have key := Repulsion_arith hc' hx0 hρ hG hG1 hgG2 hKx
  have hmul := mul_lt_mul_of_pos_right key (Real.rpow_pos_of_pos hN0 (-(2 / 3 : ℝ)))
  refine lt_of_lt_of_le ?_ (hlow.trans hmq)
  rw [← hxτ]
  calc K * (x ^ 3 * (N : ℝ) ^ (-(2 / 3 : ℝ))) * rk D N c ^ (-(1 / 3 : ℝ))
      = K * x ^ 3 * rk D N c ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
    _ < c' * g * (rk D N c + G) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := hmul
    _ = c' * (g : ℝ) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
          (rk D N c + (N : ℝ) ^ (2 * τ)) ^ (-(1 / 3 : ℝ))) := by
      rw [hGdef]; ring

/-- If the quantile `γ_{Dj}` of (5.13) [eq:gammak2] is within the tolerance of the first
condition of (5.11) [eq:probab12] and of (5.12) [rigidity12] of `γ_k`, then `|Dj - k| < N^{2τ}`:
this bounds the deterministic set of indices `j` in the union bound of (5.11). -/
private lemma Repulsion_index_close (D : ℕ) (hD : 2 ≤ D) (τ : ℝ) (hτ : 0 < τ)
    (hτ1 : τ < 1 / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ j k : ℕ, 1 ≤ j → j ≤ N → 1 ≤ k → k ≤ D * N →
      |quant rhoSc (D * N) (D * j) - quant rhoSc (D * N) k| ≤
          (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) +
            (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N j ^ (-(1 / 3 : ℝ))) →
        |((D * j : ℕ) : ℝ) - k| < (N : ℝ) ^ (2 * τ) := by
  obtain ⟨N₁, h⟩ := Repulsion_far D hD τ hτ hτ1
  refine ⟨max N₁ 1, fun N hN j k hj1 hjN hk1 hkN htol => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 1 ≤ N := le_trans (le_max_right _ _) hN
  by_contra hge
  have hge := not_lt.1 hge
  have hDj1 : 1 ≤ D * j := Nat.mul_pos (by omega) hj1
  have hDjN : D * j ≤ D * N := Nat.mul_le_mul_left D hjN
  have hρ1 := Repulsion_one_le_rk D N (D * j) hDj1 hDjN
  have hρ2 := Repulsion_one_le_rk D N k hk1 hkN
  rcases le_total (rk D N (D * j)) (rk D N k) with hle | hle
  · have hfar := h N hN1 (D * j) k hDj1 hDjN hk1 hkN (by rwa [abs_sub_comm])
    have htol' := Repulsion_tol D N (by omega) hN2 τ j k (D * j) hjN (by linarith) hle le_rfl
    rw [abs_sub_comm] at hfar
    linarith
  · have hfar := h N hN1 k (D * j) hk1 hkN hDj1 hDjN hge
    have htol' := Repulsion_tol D N (by omega) hN2 τ j k k hjN (by linarith) le_rfl hle
    linarith

/-- At most `2 G` indices `j` satisfy `|Dj - k| < G`, for `D ≥ 2` and `G ≥ 1`. -/
private lemma Repulsion_card (D : ℕ) (hD : 2 ≤ D) (N k : ℕ) (G : ℝ) (hG : 1 ≤ G) :
    (((Finset.Icc 1 N).filter fun j => |((D * j : ℕ) : ℝ) - k| < G).card : ℝ) ≤ 2 * G := by
  set J : Finset ℕ := (Finset.Icc 1 N).filter fun j => |((D * j : ℕ) : ℝ) - k| < G with hJ
  rcases J.eq_empty_or_nonempty with he | hne
  · rw [he]; simp; linarith
  · set j₀ := J.min' hne with hj₀
    have hj₀J : j₀ ∈ J := Finset.min'_mem J hne
    have hsub : J ⊆ Finset.Icc j₀ (j₀ + ⌊G⌋₊) := by
      intro j hj
      rw [Finset.mem_Icc]
      have hjle : j₀ ≤ j := Finset.min'_le J j hj
      refine ⟨hjle, ?_⟩
      simp only [hJ, Finset.mem_filter] at hj hj₀J
      have h1 := abs_lt.1 hj.2
      have h2 := abs_lt.1 hj₀J.2
      have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
      have hjj : (j₀ : ℝ) ≤ j := by exact_mod_cast hjle
      have hmul : (D : ℝ) * ((j : ℝ) - j₀) < 2 * G := by
        push_cast at h1 h2
        nlinarith
      have hlt : ((j - j₀ : ℕ) : ℝ) ≤ G := by
        rw [Nat.cast_sub hjle]
        nlinarith
      have := Nat.le_floor hlt
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have : J.card ≤ ⌊G⌋₊ + 1 := by omega
    have hfl : (⌊G⌋₊ : ℝ) ≤ G := Nat.floor_le (by linarith)
    have : (J.card : ℝ) ≤ ⌊G⌋₊ + 1 := by exact_mod_cast this
    linarith

/-- The law of the pair `(H_{b'}, H_b)` of two different blocks of (1.3) [matrix_H] is the
product `coordLaw ⊗ coordLaw`: the blocks are independent. -/
private lemma Repulsion_pair_law (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) {b b' : Fin D}
    (hb : b' ≠ b) :
    (blockLaw D N L).map (fun w : Fin D → Coords N => (w b', w b)) =
      (coordLaw N L).prod (coordLaw N L) := by
  have : IsProbabilityMeasure (coordLaw N L) := by unfold coordLaw; infer_instance
  have hind : iIndepFun (fun (i : Fin D) (w : Fin D → Coords N) => w i) (blockLaw D N L) :=
    iIndepFun_pi (μ := fun _ : Fin D => coordLaw N L) (X := fun _ => id)
      (fun _ => aemeasurable_id)
  have h := hind.indepFun hb
  have : IsProbabilityMeasure (blockLaw D N L) := blockLaw_isProbabilityMeasure D N L
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply b').aemeasurable
    (measurable_pi_apply b).aemeasurable] at h
  rw [h]
  have e : ∀ i : Fin D, (blockLaw D N L).map (fun w => w i) = coordLaw N L := fun i =>
    (measurePreserving_eval (fun _ : Fin D => coordLaw N L) i).map_eq
  rw [e, e]

/-- Fubini for two different blocks: if every section `{x | (y, x) ∈ T}` of a measurable set `T`
has `coordLaw` at most `ε`, then `{w | (w b', w b) ∈ T}` has `blockLaw` at most `ε`. -/
private lemma Repulsion_fubini (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) {b b' : Fin D}
    (hb : b' ≠ b) {T : Set (Coords N × Coords N)} (hT : MeasurableSet T) {ε : ENNReal}
    (h : ∀ y : Coords N, coordLaw N L {x | (y, x) ∈ T} ≤ ε) :
    blockLaw D N L {w | (w b', w b) ∈ T} ≤ ε := by
  have : IsProbabilityMeasure (coordLaw N L) := by unfold coordLaw; infer_instance
  have hm : Measurable fun w : Fin D → Coords N => (w b', w b) :=
    (measurable_pi_apply b').prodMk (measurable_pi_apply b)
  have e : {w : Fin D → Coords N | (w b', w b) ∈ T} =
      (fun w : Fin D → Coords N => (w b', w b)) ⁻¹' T := rfl
  rw [e, ← Measure.map_apply hm hT, Repulsion_pair_law D N L hb, Measure.prod_apply hT]
  calc ∫⁻ y, coordLaw N L (Prod.mk y ⁻¹' T) ∂coordLaw N L
      ≤ ∫⁻ _y, ε ∂coordLaw N L := lintegral_mono fun y => h y
    _ = ε := by simp

/-- The set of pairs `(y, x)` of block coordinates such that `λ_j(y)` lies within `W` of `γ` and
some eigenvalue `λ_i(x)`, `i ∈ ⟦1, N⟧`, lies within `w₀` of `λ_j(y)`: the event of (5.11)
[eq:probab12] for a fixed index `j` of the block `H_{b'}` and the block `H_b`. -/
private def Repulsion_T (N j : ℕ) (γ W w₀ : ℝ) : Set (Coords N × Coords N) :=
  {p | |eigK (wig N p.1) j - γ| ≤ W ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
    |eigK (wig N p.2) i - eigK (wig N p.1) j| ≤ w₀}

/-- `Repulsion_T` is measurable. -/
private lemma Repulsion_meas_T (N j : ℕ) (γ W w₀ : ℝ) : MeasurableSet (Repulsion_T N j γ W w₀) := by
  have h1 : Measurable fun p : Coords N × Coords N => eigK (wig N p.1) j :=
    (Repulsion_meas_eig N j).comp measurable_fst
  have hA : MeasurableSet {p : Coords N × Coords N | |eigK (wig N p.1) j - γ| ≤ W} :=
    measurableSet_le (continuous_abs.measurable.comp (h1.sub_const γ)) measurable_const
  have hB : MeasurableSet {p : Coords N × Coords N | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
      |eigK (wig N p.2) i - eigK (wig N p.1) j| ≤ w₀} := by
    have e : {p : Coords N × Coords N | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
        |eigK (wig N p.2) i - eigK (wig N p.1) j| ≤ w₀} =
        ⋃ i : ℕ, ⋃ (_ : 1 ≤ i ∧ i ≤ N),
          {p : Coords N × Coords N | |eigK (wig N p.2) i - eigK (wig N p.1) j| ≤ w₀} := by
      ext p; simp [and_assoc]
    rw [e]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => ?_
    have h2 : Measurable fun p : Coords N × Coords N => eigK (wig N p.2) i :=
      (Repulsion_meas_eig N i).comp measurable_snd
    exact measurableSet_le (continuous_abs.measurable.comp (h2.sub h1)) measurable_const
  exact hA.inter hB

/-- (5.11) [eq:probab12] in the form used for every `D ≥ 2`, from (5.12) [rigidity12] and the
level repulsion (5.14) [Wegner12]: for two blocks `b ≠ b'`, the probability that an eigenvalue
of `H_{b'}` lies within `N^{-2/3+τ} k^{-1/3}` of `γ_k^{sc}` and an eigenvalue of `H_b` lies
within `2 N^{-2/3-δ} k^{-1/3}` of it is at most `N^{-δ₀}`. -/
theorem blocks_repulsion (C : ℕ → ℝ) (hEI : EI2Hyp C) (D : ℕ) (hD : 2 ≤ D) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C, ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      ∀ b b' : Fin D, b ≠ b' →
        blockLaw D N L {w | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ N ∧ 1 ≤ j ∧ j ≤ N ∧
            |eigK (wig N (w b')) j - quant rhoSc (D * N) k| ≤
              (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) ∧
            |eigK (wig N (w b)) i - eigK (wig N (w b')) j| ≤
              2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * (k : ℝ) ^ (-(1 / 3 : ℝ))} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-δ₀)) := by
  obtain ⟨δ₀, hδ₀, τE, hτE, hEI'⟩ := hEI D (by omega) δ hδ
  refine ⟨δ₀, hδ₀, min (min τE (δ₀ / 4)) (1 / 4), by positivity, fun τ hτ hττ => ?_⟩
  have hττE : τ ≤ τE := hττ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hττδ : τ ≤ δ₀ / 4 := hττ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ14 : τ ≤ 1 / 4 := hττ.trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hEI' τ hτ hττE
  obtain ⟨N₂, hN₂⟩ := rigidity12 D (by omega) C τ hτ (2 * δ₀) (by positivity)
  obtain ⟨N₃, hN₃⟩ := Repulsion_index_close D hD τ hτ (by linarith)
  have hev : ∀ᶠ N : ℕ in atTop, 3 ≤ (N : ℝ) ^ (δ₀ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < δ₀ / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) 1), fun N hN L k hk1 hkN b b' hbb => ?_⟩
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN₃ : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hNN₄ : N₄ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have h3 : 3 ≤ (N : ℝ) ^ (δ₀ / 2) := hN₄ N hNN₄
  -- the deterministic set `J` of indices `j` whose `γ_{Dj}` can lie in the window of `γ_k`
  set G : ℝ := (N : ℝ) ^ (2 * τ) with hG
  have hG1 : 1 ≤ G := Real.one_le_rpow hNr (by linarith)
  set J : Finset ℕ := (Finset.Icc 1 N).filter fun j => |((D * j : ℕ) : ℝ) - k| < G with hJ
  have hcard : (J.card : ℝ) ≤ 2 * G := Repulsion_card D hD N k G hG1
  set γk : ℝ := quant rhoSc (D * N) k with hγk
  set W : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) with hW
  set w₀ : ℝ := 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) - δ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) with hw₀
  set a : ℝ := (N : ℝ) ^ (-(2 * δ₀)) with ha
  -- the rigidity event of (5.12) [rigidity12] for the block `b'`
  have hBad := hN₂ N hNN₂ L b'
  -- the event on which block `b'` has `λ_j` in `A_{j,τ}` and block `b` an eigenvalue nearby
  have hE : ∀ j : ℕ, blockLaw D N L {w | (w b', w b) ∈ Repulsion_T N j γk W w₀} ≤
      ENNReal.ofReal a := by
    intro j
    refine Repulsion_fubini D N L hbb.symm (Repulsion_meas_T N j γk W w₀) fun y => ?_
    by_cases hy : |eigK (wig N y) j - γk| ≤ W
    · have := hN₁ N hNN₁ L k hk1 hkN (eigK (wig N y) j) hy
      refine le_trans (le_of_eq ?_) this
      congr 1
      ext x
      simp only [Repulsion_T, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
    · have : {x : Coords N | (y, x) ∈ Repulsion_T N j γk W w₀} = ∅ := by
        ext x
        simp only [Repulsion_T, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hy
      rw [this]
      simp
  have hsub : {w : Fin D → Coords N | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ N ∧ 1 ≤ j ∧ j ≤ N ∧
        |eigK (wig N (w b')) j - γk| ≤ W ∧ |eigK (wig N (w b)) i - eigK (wig N (w b')) j| ≤ w₀} ⊆
      {w : Fin D → Coords N | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
        (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) <
          |eigK (wig N (w b')) i - quant rhoSc (D * N) (D * i)|} ∪
        ⋃ j ∈ J, {w : Fin D → Coords N | (w b', w b) ∈ Repulsion_T N j γk W w₀} := by
    rintro w ⟨i, j, hi1, hiN, hj1, hjN, hA, hB⟩
    by_cases hbad : ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
        (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N i ^ (-(1 / 3 : ℝ))) <
          |eigK (wig N (w b')) i - quant rhoSc (D * N) (D * i)|
    · exact Or.inl hbad
    · refine Or.inr ?_
      have hrig : |eigK (wig N (w b')) j - quant rhoSc (D * N) (D * j)| ≤
          (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N j ^ (-(1 / 3 : ℝ))) := by
        by_contra hlt
        exact hbad ⟨j, hj1, hjN, not_le.1 hlt⟩
      have hclose : |quant rhoSc (D * N) (D * j) - γk| ≤
          (N : ℝ) ^ (-(2 / 3 : ℝ) + τ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) +
            (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk 1 N j ^ (-(1 / 3 : ℝ))) := by
        calc |quant rhoSc (D * N) (D * j) - γk|
            = |(eigK (wig N (w b')) j - γk) -
                (eigK (wig N (w b')) j - quant rhoSc (D * N) (D * j))| := by
              congr 1; ring
          _ ≤ |eigK (wig N (w b')) j - γk| +
              |eigK (wig N (w b')) j - quant rhoSc (D * N) (D * j)| := abs_sub _ _
          _ ≤ _ := add_le_add hA hrig
      have hjJ : j ∈ J := by
        rw [hJ, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hj1, hjN⟩, hN₃ N hNN₃ j k hj1 hjN hk1 hkN hclose⟩
      exact Set.mem_biUnion hjJ ⟨hA, i, hi1, hiN, hB⟩
  have hreal : a + J.card * a ≤ (N : ℝ) ^ (-δ₀) := by
    have ha0 : 0 ≤ a := by positivity
    have h1 : a + J.card * a ≤ 3 * (a * G) := by
      nlinarith [mul_le_mul_of_nonneg_left hcard ha0]
    have h2 : a * G ≤ (N : ℝ) ^ (-(3 * δ₀ / 2)) := by
      rw [ha, hG, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have h4 : (N : ℝ) ^ (-(3 * δ₀ / 2)) = (N : ℝ) ^ (-δ₀) * ((N : ℝ) ^ (δ₀ / 2))⁻¹ := by
      rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]
      ring_nf
    have h5 : ((N : ℝ) ^ (δ₀ / 2))⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) h3
    have h6 : 0 < (N : ℝ) ^ (-δ₀) := Real.rpow_pos_of_pos hN0 _
    nlinarith [mul_le_mul_of_nonneg_left h5 h6.le]
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add hBad (measure_biUnion_finset_le J _)) ?_
  refine le_trans (add_le_add_right (Finset.sum_le_card_nsmul J _ _ fun j _ => hE j) _) ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

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
          ENNReal.ofReal ((N : ℝ) ^ (-δ₀)) := by
  obtain ⟨δ₀, hδ₀, τ₀, hτ₀, h⟩ := blocks_repulsion _ hEI 3 (by norm_num) (1 / 10) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h τ₀ hτ₀ le_rfl
  exact ⟨δ₀, hδ₀, τ₀, hτ₀, N₀, fun N hN hN1 L =>
    hN₀ N hN L 1 le_rfl (by omega) 0 1 (by decide)⟩

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
          ENNReal.ofReal ((N : ℝ) ^ (-δ₀)) := by
  obtain ⟨δ₀, hδ₀, τ₀, hτ₀, h⟩ := blocks_repulsion _ hEI 3 (by norm_num) (1 / 10) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h τ₀ hτ₀ le_rfl
  exact ⟨δ₀, hδ₀, τ₀, hτ₀, N₀, fun N hN hN1 L =>
    hN₀ N hN L N hN1 (by omega) 0 1 (by decide)⟩

end RBMTransitionEdge

end
