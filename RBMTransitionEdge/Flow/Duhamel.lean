module

public import RBMTransitionEdge.Tools.Flow

@[expose] public section

/-!
# Discrete Duhamel bounds on the grid of the characteristic flow

The left Riemann sums of `s ↦ (t_c - s)^{-β}`, the propagator bound behind (3.68) [Phinorm], the
linear discrete Duhamel bound, and the bootstrap by induction on the grid that replaces the
stopping time and the continuity argument after (3.70) [eq:self_imp] in the proof of Lemma 3.8
[lem_flow_1].
-/

open MeasureTheory

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- One cell of `riemann_rpow_le`: `(a - b) a^{-β} ≤ (b^{1-β} - a^{1-β}) / (β - 1)` for
`0 < b ≤ a`, `β > 1` (the integrand `x ↦ x^{-β}` is at least `a^{-β}` on `[b, a]`). -/
private lemma Duhamel_cell_rpow (a b β : ℝ) (hb : 0 < b) (hba : b ≤ a) (hβ : 1 < β) :
    (a - b) * a ^ (-β) ≤ (b ^ (1 - β) - a ^ (1 - β)) / (β - 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc b a := by
    rw [Set.uIcc_of_le hba]
    exact fun h => absurd h.1 (not_le.mpr hb)
  have hint := integral_rpow (a := b) (b := a) (r := -β) (Or.inr ⟨by linarith, h0⟩)
  have hmono : ∫ _ in b..a, a ^ (-β) ≤ ∫ x in b..a, x ^ (-β) := by
    refine intervalIntegral.integral_mono_on hba intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)) ?_
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2 (by linarith)
  rw [hint, intervalIntegral.integral_const, smul_eq_mul, show -β + 1 = 1 - β by ring] at hmono
  have e : (a ^ (1 - β) - b ^ (1 - β)) / (1 - β) = (b ^ (1 - β) - a ^ (1 - β)) / (β - 1) := by
    rw [← neg_div_neg_eq]
    ring_nf
  rw [e] at hmono
  exact hmono

/-- The left Riemann sum of the increasing `s ↦ (t_c - s)^{-β}`, `β > 1`, on the grid
`u_i = u₀ + i h`: `Σ_{j ≤ i < k} h (t_c - u_i)^{-β} ≤ (t_c - u_k)^{1-β} / (β - 1)`. -/
theorem riemann_rpow_le (u₀ h tc β : ℝ) (hh : 0 < h) (hβ : 1 < β) (j k : ℕ) (hjk : j ≤ k)
    (hk : u₀ + k * h < tc) :
    ∑ i ∈ Finset.Ico j k, h * (tc - (u₀ + i * h)) ^ (-β) ≤
      (tc - (u₀ + k * h)) ^ (1 - β) / (β - 1) := by
  have key : ∑ i ∈ Finset.Ico j k, h * (tc - (u₀ + i * h)) ^ (-β) ≤
      ((tc - (u₀ + k * h)) ^ (1 - β) - (tc - (u₀ + j * h)) ^ (1 - β)) / (β - 1) := by
    induction k, hjk using Nat.le_induction with
    | base => simp
    | succ k hjk ih =>
      have hid : tc - (u₀ + ((k + 1 : ℕ) : ℝ) * h) = (tc - (u₀ + k * h)) - h := by
        push_cast; ring
      have hk' : u₀ + (k : ℝ) * h < tc := by
        have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * h - k * h := by push_cast; nlinarith
        linarith
      have hpos' : 0 < (tc - (u₀ + k * h)) - h := by rw [← hid]; linarith
      rw [Finset.sum_Ico_succ_top hjk, hid]
      have cell := Duhamel_cell_rpow (tc - (u₀ + k * h)) ((tc - (u₀ + k * h)) - h) β hpos'
        (by linarith) hβ
      have e : (tc - (u₀ + k * h)) - ((tc - (u₀ + k * h)) - h) = h := by ring
      rw [e] at cell
      have ih' := ih hk'
      have : ((tc - (u₀ + k * h)) ^ (1 - β) - (tc - (u₀ + j * h)) ^ (1 - β)) / (β - 1) +
          (((tc - (u₀ + k * h)) - h) ^ (1 - β) - (tc - (u₀ + k * h)) ^ (1 - β)) / (β - 1) =
          (((tc - (u₀ + k * h)) - h) ^ (1 - β) - (tc - (u₀ + j * h)) ^ (1 - β)) / (β - 1) := by
        ring
      linarith
  have hpos : ∀ i : ℕ, i ≤ k → 0 < tc - (u₀ + i * h) := fun i hi => by
    have : (i : ℝ) * h ≤ k * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le
    linarith
  have hj0 : 0 ≤ (tc - (u₀ + j * h)) ^ (1 - β) :=
    Real.rpow_nonneg (hpos j hjk).le _
  have hβ' : 0 < β - 1 := by linarith
  refine key.trans ?_
  exact div_le_div_of_nonneg_right (by linarith) hβ'.le

/-- The propagator bound behind (3.68) [Phinorm]: for `A_i = 1 + (h / (t_c - u_i)) T_i` with
`‖T_i‖ ≤ c`, `‖Φ(k, j)‖ ≤ ((t_c - u_j) / (t_c - u_k))^c`. -/
theorem propag_rpow_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (u₀ h tc c : ℝ) (hh : 0 < h) (hc : 0 ≤ c)
    (hT : ∀ i, ‖T i‖ ≤ c) (j k : ℕ) (hjk : j ≤ k) (hk : u₀ + k * h < tc) :
    ‖propag (fun i => ContinuousLinearMap.id ℂ E +
        ((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i) j k‖ ≤
      ((tc - (u₀ + j * h)) / (tc - (u₀ + k * h))) ^ c := by
  have hq : ∀ i : ℕ, i ≤ k → 0 < tc - (u₀ + i * h) := fun i hi => by
    have : (i : ℝ) * h ≤ k * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le
    linarith
  have hqk := hq k le_rfl
  have hqj := hq j hjk
  have hfac : ∀ i ∈ Finset.Ico j k,
      ‖ContinuousLinearMap.id ℂ E + ((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i‖ ≤
        Real.exp (c * (h / (tc - (u₀ + i * h)))) := by
    intro i hi
    have hik : i ≤ k := (Finset.mem_Ico.mp hi).2.le
    have hqi := hq i hik
    have hnn : 0 ≤ h / (tc - (u₀ + i * h)) := div_nonneg hh.le hqi.le
    calc ‖ContinuousLinearMap.id ℂ E + ((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i‖
        ≤ ‖ContinuousLinearMap.id ℂ E‖ + ‖((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i‖ :=
          norm_add_le _ _
      _ ≤ 1 + h / (tc - (u₀ + i * h)) * c := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hnn]
          exact add_le_add ContinuousLinearMap.norm_id_le
            (mul_le_mul_of_nonneg_left (hT i) hnn)
      _ ≤ Real.exp (c * (h / (tc - (u₀ + i * h)))) := by
          rw [mul_comm c]
          linarith [Real.add_one_le_exp (h / (tc - (u₀ + i * h)) * c)]
  calc ‖propag (fun i => ContinuousLinearMap.id ℂ E +
        ((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i) j k‖
      ≤ ∏ i ∈ Finset.Ico j k, ‖ContinuousLinearMap.id ℂ E +
        ((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i‖ := norm_propag_le _ j k
    _ ≤ ∏ i ∈ Finset.Ico j k, Real.exp (c * (h / (tc - (u₀ + i * h)))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac
    _ = Real.exp (c * ∑ i ∈ Finset.Ico j k, h / (tc - (u₀ + i * h))) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (c * Real.log ((tc - (u₀ + j * h)) / (tc - (u₀ + k * h)))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (riemann_inv_le_log u₀ h tc hh j k hjk hk) hc)
    _ = ((tc - (u₀ + j * h)) / (tc - (u₀ + k * h))) ^ c := by
        rw [Real.rpow_def_of_pos (div_pos hqj hqk), mul_comm]

/-- The linear discrete Duhamel bound: if
`x_{k+1} = x_k + (h / (t_c - u_k)) T_k x_k + b_k` with `‖T_k‖ ≤ c`, then
`‖x_k‖ ≤ ((t_c - u₀)/(t_c - u_k))^c ‖x_0‖ + Σ_{j<k} ((t_c - u_{j+1})/(t_c - u_k))^c ‖b_j‖`. -/
theorem duhamel_lin_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (u₀ h tc c : ℝ) (hh : 0 < h) (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c)
    (x b : ℕ → E)
    (hx : ∀ k, x (k + 1) = x k + ((h / (tc - (u₀ + k * h)) : ℝ) : ℂ) • T k (x k) + b k)
    (k : ℕ) (hk : u₀ + k * h < tc) :
    ‖x k‖ ≤ ((tc - u₀) / (tc - (u₀ + k * h))) ^ c * ‖x 0‖ +
      ∑ j ∈ Finset.range k,
        ((tc - (u₀ + ((j + 1 : ℕ) : ℝ) * h)) / (tc - (u₀ + k * h))) ^ c * ‖b j‖ := by
  set A : ℕ → E →L[ℂ] E := fun i => ContinuousLinearMap.id ℂ E +
    ((h / (tc - (u₀ + i * h)) : ℝ) : ℂ) • T i with hA
  have hx' : ∀ n, x (n + 1) = A n (x n) + b n := fun n => by
    rw [hx n]
    simp only [hA, add_apply, ContinuousLinearMap.id_apply, smul_apply]
  have hd := discrete_duhamel A x b hx' k
  have h0 : ‖propag A 0 k‖ ≤ ((tc - u₀) / (tc - (u₀ + k * h))) ^ c := by
    have := propag_rpow_le T u₀ h tc c hh hc hT 0 k (Nat.zero_le k) hk
    rw [Nat.cast_zero, zero_mul, add_zero] at this
    exact this
  rw [hd]
  calc ‖propag A 0 k (x 0) + ∑ j ∈ Finset.range k, propag A (j + 1) k (b j)‖
      ≤ ‖propag A 0 k (x 0)‖ + ‖∑ j ∈ Finset.range k, propag A (j + 1) k (b j)‖ :=
        norm_add_le _ _
    _ ≤ ((tc - u₀) / (tc - (u₀ + k * h))) ^ c * ‖x 0‖ +
        ∑ j ∈ Finset.range k, ‖propag A (j + 1) k (b j)‖ := by
        refine add_le_add ?_ (norm_sum_le _ _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
    _ ≤ _ := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
        have hj' : j + 1 ≤ k := Finset.mem_range.mp hj
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (propag_rpow_le T u₀ h tc c hh hc hT (j + 1) k hj' hk) (norm_nonneg _))

/-- The bootstrap of the proof of Lemma 3.8 [lem_flow_1] by strong induction on the grid, in place
of the stopping time `T` and the continuity argument after (3.70) [eq:self_imp]: for
`Δ_{k+1} - ℰ_{k+1} = Δ_k - ℰ_k + (h/q_k)(T_k Δ_k + Q(Δ_k))`, `q_k = t_c - u_k`, `ℰ_0 = 0`,
`‖T_k‖ ≤ 1 + ω`, `‖Q v‖ ≤ ‖v‖²` and weights `Ψ_k = ρ_k q_k` with `ρ` nondecreasing and
`ρ_k ≤ r ρ_j` (`j ≤ k ≤ K`): if `Ψ_k ‖ℰ_k‖ ≤ ε_*`, `Ψ_0 ‖Δ_0‖ ≤ δ_*`, `Ψ_k ≥ Ψ_min > 0` and
`ε_* + γ r δ_* + γ (1 + ω) r ε_* log(q_0/q_K) + γ r² Θ² / Ψ_min < Θ` with
`γ = (q_0/q_K)^ω`, then `Ψ_k ‖Δ_k‖ < Θ` for all `k ≤ K`. -/
theorem duhamel_quad_boot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (Q : E → E) (u₀ h tc ω r εs δs Θ Ψmin : ℝ) (K : ℕ)
    (hh : 0 < h) (hω : 0 ≤ ω) (hr : 1 ≤ r) (hK : u₀ + K * h < tc)
    (hT : ∀ k, k < K → ‖T k‖ ≤ 1 + ω) (hQ : ∀ v, ‖Q v‖ ≤ ‖v‖ ^ 2)
    (ρ : ℕ → ℝ) (hρ₀ : 0 < ρ 0) (hρ : ∀ j k, j ≤ k → k ≤ K → ρ j ≤ ρ k ∧ ρ k ≤ r * ρ j)
    (Δ ℰ : ℕ → E) (hℰ₀ : ℰ 0 = 0)
    (hrec : ∀ k, k < K → Δ (k + 1) - ℰ (k + 1) =
      Δ k - ℰ k + ((h / (tc - (u₀ + k * h)) : ℝ) : ℂ) • (T k (Δ k) + Q (Δ k)))
    (hℰ : ∀ k, k ≤ K → ρ k * (tc - (u₀ + k * h)) * ‖ℰ k‖ ≤ εs)
    (hΔ₀ : ρ 0 * (tc - u₀) * ‖Δ 0‖ ≤ δs)
    (hΨ : ∀ k, k ≤ K → Ψmin ≤ ρ k * (tc - (u₀ + k * h))) (hΨmin : 0 < Ψmin)
    (hΘ : εs + ((tc - u₀) / (tc - (u₀ + K * h))) ^ ω * r * δs +
        ((tc - u₀) / (tc - (u₀ + K * h))) ^ ω * (1 + ω) * r * εs *
          Real.log ((tc - u₀) / (tc - (u₀ + K * h))) +
        ((tc - u₀) / (tc - (u₀ + K * h))) ^ ω * r ^ 2 * Θ ^ 2 / Ψmin < Θ) :
    ∀ k, k ≤ K → ρ k * (tc - (u₀ + k * h)) * ‖Δ k‖ < Θ := by
  -- the grid `q_n = t_c - u_n`
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ n : ℕ, q n = tc - (u₀ + n * h) := ⟨_, fun _ => rfl⟩
  have hq0 : tc - u₀ = q 0 := by rw [hq]; simp
  have hqK : 0 < q K := by rw [hq]; linarith
  have hqanti : ∀ a n : ℕ, a ≤ n → q n ≤ q a := fun a n han => by
    rw [hq, hq]
    have : (a : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right (by exact_mod_cast han) hh.le
    linarith
  have hqpos : ∀ n, n ≤ K → 0 < q n := fun n hn => lt_of_lt_of_le hqK (hqanti n K hn)
  have hgrid : ∀ n, n ≤ K → u₀ + n * h < tc := fun n hn => by
    have := hqpos n hn
    rw [hq] at this
    linarith
  have hRinv : ∀ n, n ≤ K → ∑ i ∈ Finset.range n, h / q i ≤ Real.log (q 0 / q n) := by
    intro n hn
    have := riemann_inv_le_log u₀ h tc hh 0 n (Nat.zero_le n) (hgrid n hn)
    simp only [← hq] at this
    rwa [← Finset.range_eq_Ico] at this
  have hRsq : ∀ n, n ≤ K → ∑ i ∈ Finset.range n, h * (q i ^ 2)⁻¹ ≤ (q n)⁻¹ := by
    intro n hn
    have := riemann_rpow_le u₀ h tc 2 hh (by norm_num) 0 n (Nat.zero_le n) (hgrid n hn)
    simp only [← hq] at this
    rw [← Finset.range_eq_Ico] at this
    have e1 : ∀ i, q i ^ (-(2 : ℝ)) = (q i ^ 2)⁻¹ := fun i => by
      rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      simp [zpow_neg]
    have e2 : q n ^ (1 - (2 : ℝ)) / (2 - 1) = (q n)⁻¹ := by
      rw [show (1 - (2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      norm_num
    simp only [e1, e2] at this
    exact this
  simp only [← hq] at hrec hℰ hΨ hΘ ⊢
  rw [hq0] at hΔ₀ hΘ
  have hr0 : 0 ≤ r := by linarith
  have hρpos : ∀ n, n ≤ K → 0 < ρ n := fun n hn => by
    by_contra hcon
    have hcon' := not_lt.mp hcon
    nlinarith [hΨ n hn, hqpos n hn]
  have hεs : 0 ≤ εs :=
    le_trans (mul_nonneg (mul_nonneg (hρpos 0 (Nat.zero_le K)).le (hqpos 0 (Nat.zero_le K)).le)
      (norm_nonneg _)) (hℰ 0 (Nat.zero_le K))
  have hδs : 0 ≤ δs :=
    le_trans (mul_nonneg (mul_nonneg (hρpos 0 (Nat.zero_le K)).le (hqpos 0 (Nat.zero_le K)).le)
      (norm_nonneg _)) hΔ₀
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (q 0 / q K) ^ ω := ⟨_, rfl⟩
  rw [← hγ] at hΘ
  have hq0K : 1 ≤ q 0 / q K := by
    rw [le_div_iff₀ hqK]
    linarith [hqanti 0 K (Nat.zero_le K)]
  have hγ1 : 1 ≤ γ := by rw [hγ]; exact Real.one_le_rpow hq0K hω
  have hγ0 : 0 ≤ γ := by linarith
  -- the linear reduction: `Δ̂ = Δ - ℰ` satisfies `Δ̂_{n+1} = A_n Δ̂_n + b_n` for `n < K`
  obtain ⟨T', hT'⟩ : ∃ T' : ℕ → E →L[ℂ] E, ∀ n, T' n = if n < K then T n else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Dh, hDh⟩ : ∃ Dh : ℕ → E, ∀ n, Dh n = Δ n - ℰ n := ⟨_, fun _ => rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℕ → E, ∀ n, b' n = Dh (n + 1) - Dh n -
      ((h / (tc - (u₀ + n * h)) : ℝ) : ℂ) • T' n (Dh n) := ⟨_, fun _ => rfl⟩
  have hT'le : ∀ n, ‖T' n‖ ≤ 1 + ω := fun n => by
    rw [hT' n]
    split_ifs with hn
    · exact hT n hn
    · rw [norm_zero]; linarith
  have hx' : ∀ n, Dh (n + 1) =
      Dh n + ((h / (tc - (u₀ + n * h)) : ℝ) : ℂ) • T' n (Dh n) + b' n := fun n => by
    rw [hb' n]; abel
  have hD0 : Dh 0 = Δ 0 := by rw [hDh, hℰ₀, sub_zero]
  have hb'le : ∀ n, n < K → ‖b' n‖ ≤ h / q n * ((1 + ω) * ‖ℰ n‖ + ‖Δ n‖ ^ 2) := by
    intro n hn
    have hrn := hrec n hn
    have hnn : 0 ≤ h / q n := div_nonneg hh.le (hqpos n hn.le).le
    have hb : b' n = ((h / q n : ℝ) : ℂ) • (T n (ℰ n) + Q (Δ n)) := by
      have hTn : T' n = T n := by simp [hT', hn]
      rw [hb' n, ← hq n, hTn, hDh (n + 1), hDh n, hrn]
      simp only [map_sub, smul_add, smul_sub]
      abel
    rw [hb, norm_smul, Complex.norm_real, Real.norm_of_nonneg hnn]
    refine mul_le_mul_of_nonneg_left ?_ hnn
    calc ‖T n (ℰ n) + Q (Δ n)‖ ≤ ‖T n (ℰ n)‖ + ‖Q (Δ n)‖ := norm_add_le _ _
      _ ≤ (1 + ω) * ‖ℰ n‖ + ‖Δ n‖ ^ 2 :=
        add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hT n hn) (norm_nonneg _))) (hQ _)
  -- the weights
  have hw : ∀ a n : ℕ, a ≤ n → n ≤ K →
      ρ n * q n * (q a / q n) ^ (1 + ω) ≤ γ * (ρ n * q a) := by
    intro a n han hnK
    have hqa := hqpos a (han.trans hnK)
    have hqn := hqpos n hnK
    have hρn := hρpos n hnK
    have hratio : 0 < q a / q n := div_pos hqa hqn
    have hle : (q a / q n) ^ ω ≤ γ := by
      rw [hγ]
      refine Real.rpow_le_rpow hratio.le ?_ hω
      exact div_le_div₀ (hqpos 0 (Nat.zero_le K)).le (hqanti 0 a (Nat.zero_le a)) hqK
        (hqanti n K hnK)
    rw [Real.rpow_add hratio, Real.rpow_one]
    have hqn' := hqn.ne'
    calc ρ n * q n * (q a / q n * (q a / q n) ^ ω) = ρ n * q a * (q a / q n) ^ ω := by
          field_simp
      _ ≤ ρ n * q a * γ := mul_le_mul_of_nonneg_left hle (mul_nonneg hρn.le hqa.le)
      _ = γ * (ρ n * q a) := by ring
  -- strong induction on the grid
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hkK
  have hqk := hqpos k hkK
  have hρk := hρpos k hkK
  have hq00 := hqpos 0 (Nat.zero_le K)
  have hPnn : 0 ≤ ρ k * q k := (mul_pos hρk hqk).le
  have hlin := duhamel_lin_le T' u₀ h tc (1 + ω) hh (by linarith) hT'le Dh b' hx' k
    (hgrid k hkK)
  simp only [← hq] at hlin
  rw [hq0, hD0] at hlin
  have hΔk : ‖Δ k‖ ≤ ‖ℰ k‖ + ‖Dh k‖ := by
    have : Δ k = ℰ k + Dh k := by rw [hDh]; abel
    calc ‖Δ k‖ = ‖ℰ k + Dh k‖ := congrArg norm this
      _ ≤ _ := norm_add_le _ _
  -- the term of `Δ_0`
  have hT2 : ρ k * q k * ((q 0 / q k) ^ (1 + ω) * ‖Δ 0‖) ≤ γ * r * δs := by
    have h1 := hw 0 k (Nat.zero_le k) hkK
    have h2 := (hρ 0 k (Nat.zero_le k) hkK).2
    calc ρ k * q k * ((q 0 / q k) ^ (1 + ω) * ‖Δ 0‖)
        = (ρ k * q k * (q 0 / q k) ^ (1 + ω)) * ‖Δ 0‖ := by ring
      _ ≤ γ * (ρ k * q 0) * ‖Δ 0‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ γ * (r * ρ 0 * q 0) * ‖Δ 0‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2 hq00.le) hγ0) (norm_nonneg _)
      _ = γ * r * (ρ 0 * q 0 * ‖Δ 0‖) := by ring
      _ ≤ γ * r * δs := mul_le_mul_of_nonneg_left hΔ₀ (mul_nonneg hγ0 hr0)
  -- the terms of `ℰ_j` and `Q Δ_j`, `j < k`
  have hterm : ∀ j ∈ Finset.range k,
      ρ k * q k * ((q (j + 1) / q k) ^ (1 + ω) * ‖b' j‖) ≤
        γ * r * (1 + ω) * εs * (h / q j) +
          γ * r ^ 2 * Θ ^ 2 / ρ k * (h * (q j ^ 2)⁻¹) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjK : j < K := lt_of_lt_of_le hjk hkK
    have hqj := hqpos j hjK.le
    have hρj := hρpos j hjK.le
    have hqj1 : q (j + 1) ≤ q j := hqanti j (j + 1) (Nat.le_succ j)
    have hw' := hw (j + 1) k (Nat.succ_le_of_lt hjk) hkK
    have hB := hb'le j hjK
    have hρjk := (hρ j k hjk.le hkK).2
    have hej : ρ j * q j * ‖Δ j‖ < Θ := ih j hjk hjK.le
    have hej0 : 0 ≤ ρ j * q j * ‖Δ j‖ := mul_nonneg (mul_pos hρj hqj).le (norm_nonneg _)
    have hEj := hℰ j hjK.le
    have e1 : ρ k * ‖ℰ j‖ ≤ r * εs / q j := by
      rw [le_div_iff₀ hqj]
      calc ρ k * ‖ℰ j‖ * q j ≤ r * ρ j * ‖ℰ j‖ * q j :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρjk (norm_nonneg _)) hqj.le
        _ = r * (ρ j * q j * ‖ℰ j‖) := by ring
        _ ≤ r * εs := mul_le_mul_of_nonneg_left hEj hr0
    have e2 : ρ k * ‖Δ j‖ ^ 2 ≤ r ^ 2 * Θ ^ 2 / ρ k * (q j ^ 2)⁻¹ := by
      have h1 : ρ k * q j * ‖Δ j‖ ≤ r * (ρ j * q j * ‖Δ j‖) := by
        calc ρ k * q j * ‖Δ j‖ ≤ r * ρ j * q j * ‖Δ j‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρjk hqj.le)
                (norm_nonneg _)
          _ = _ := by ring
      have hsq : (ρ k * q j * ‖Δ j‖) ^ 2 ≤ r ^ 2 * Θ ^ 2 := by
        calc (ρ k * q j * ‖Δ j‖) ^ 2 ≤ (r * (ρ j * q j * ‖Δ j‖)) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (mul_pos hρk hqj).le (norm_nonneg _)) h1 2
          _ = r ^ 2 * (ρ j * q j * ‖Δ j‖) ^ 2 := by ring
          _ ≤ r ^ 2 * Θ ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hej0 hej.le 2) (sq_nonneg r)
      have hqj' := hqj.ne'
      have hρk' := hρk.ne'
      have e : r ^ 2 * Θ ^ 2 / ρ k * (q j ^ 2)⁻¹ = r ^ 2 * Θ ^ 2 / (ρ k * q j ^ 2) := by
        field_simp
      rw [e, le_div_iff₀ (mul_pos hρk (pow_pos hqj 2))]
      calc ρ k * ‖Δ j‖ ^ 2 * (ρ k * q j ^ 2) = (ρ k * q j * ‖Δ j‖) ^ 2 := by ring
        _ ≤ _ := hsq
    have hW : ρ k * q k * (q (j + 1) / q k) ^ (1 + ω) ≤ γ * (ρ k * q j) :=
      hw'.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqj1 hρk.le) hγ0)
    have hWnn : 0 ≤ γ * (ρ k * q j) := mul_nonneg hγ0 (mul_pos hρk hqj).le
    have hqj' := hqj.ne'
    calc ρ k * q k * ((q (j + 1) / q k) ^ (1 + ω) * ‖b' j‖)
        = (ρ k * q k * (q (j + 1) / q k) ^ (1 + ω)) * ‖b' j‖ := by ring
      _ ≤ (γ * (ρ k * q j)) * (h / q j * ((1 + ω) * ‖ℰ j‖ + ‖Δ j‖ ^ 2)) :=
          mul_le_mul hW hB (norm_nonneg _) hWnn
      _ = γ * h * ((1 + ω) * (ρ k * ‖ℰ j‖) + ρ k * ‖Δ j‖ ^ 2) := by field_simp
      _ ≤ γ * h * ((1 + ω) * (r * εs / q j) + r ^ 2 * Θ ^ 2 / ρ k * (q j ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left e1 (by linarith)) e2)
            (mul_nonneg hγ0 hh.le)
      _ = _ := by ring
  have hS1 : ∑ j ∈ Finset.range k, h / q j ≤ Real.log (q 0 / q K) :=
    (hRinv k hkK).trans (Real.log_le_log (div_pos hq00 hqk)
      (div_le_div_of_nonneg_left hq00.le hqK (hqanti k K hkK)))
  have hS2 := hRsq k hkK
  have hcA : 0 ≤ γ * r * (1 + ω) * εs :=
    mul_nonneg (mul_nonneg (mul_nonneg hγ0 hr0) (by linarith)) hεs
  have hcB : 0 ≤ γ * r ^ 2 * Θ ^ 2 / ρ k :=
    div_nonneg (mul_nonneg (mul_nonneg hγ0 (sq_nonneg r)) (sq_nonneg Θ)) hρk.le
  have hsum : ρ k * q k * ∑ j ∈ Finset.range k, (q (j + 1) / q k) ^ (1 + ω) * ‖b' j‖ ≤
      γ * r * (1 + ω) * εs * Real.log (q 0 / q K) + γ * r ^ 2 * Θ ^ 2 / Ψmin := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range k, ρ k * q k * ((q (j + 1) / q k) ^ (1 + ω) * ‖b' j‖)
        ≤ ∑ j ∈ Finset.range k, (γ * r * (1 + ω) * εs * (h / q j) +
          γ * r ^ 2 * Θ ^ 2 / ρ k * (h * (q j ^ 2)⁻¹)) := Finset.sum_le_sum hterm
      _ = γ * r * (1 + ω) * εs * (∑ j ∈ Finset.range k, h / q j) +
          γ * r ^ 2 * Θ ^ 2 / ρ k * (∑ j ∈ Finset.range k, h * (q j ^ 2)⁻¹) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ γ * r * (1 + ω) * εs * Real.log (q 0 / q K) +
          γ * r ^ 2 * Θ ^ 2 / ρ k * (q k)⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left hS1 hcA) (mul_le_mul_of_nonneg_left hS2 hcB)
      _ ≤ _ := by
        refine add_le_add le_rfl ?_
        have hqk' := hqk.ne'
        have hρk' := hρk.ne'
        have e : γ * r ^ 2 * Θ ^ 2 / ρ k * (q k)⁻¹ = γ * r ^ 2 * Θ ^ 2 / (ρ k * q k) := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg hγ0 (sq_nonneg r)) (sq_nonneg Θ)) hΨmin (hΨ k hkK)
  have h4 : ρ k * q k * ‖Δ k‖ ≤ εs + γ * r * δs +
      (γ * r * (1 + ω) * εs * Real.log (q 0 / q K) + γ * r ^ 2 * Θ ^ 2 / Ψmin) := by
    calc ρ k * q k * ‖Δ k‖ ≤ ρ k * q k * (‖ℰ k‖ + ‖Dh k‖) :=
          mul_le_mul_of_nonneg_left hΔk hPnn
      _ = ρ k * q k * ‖ℰ k‖ + ρ k * q k * ‖Dh k‖ := by ring
      _ ≤ εs + ρ k * q k * ((q 0 / q k) ^ (1 + ω) * ‖Δ 0‖ +
            ∑ j ∈ Finset.range k, (q (j + 1) / q k) ^ (1 + ω) * ‖b' j‖) :=
          add_le_add (hℰ k hkK) (mul_le_mul_of_nonneg_left hlin hPnn)
      _ = εs + (ρ k * q k * ((q 0 / q k) ^ (1 + ω) * ‖Δ 0‖) +
            ρ k * q k * ∑ j ∈ Finset.range k, (q (j + 1) / q k) ^ (1 + ω) * ‖b' j‖) := by
          rw [mul_add]
      _ ≤ _ := by
          rw [← add_assoc]
          exact add_le_add (add_le_add le_rfl hT2) hsum |>.trans_eq (by ring)
  exact lt_of_le_of_lt h4 (by linarith)

end RBMTransitionEdge

end
