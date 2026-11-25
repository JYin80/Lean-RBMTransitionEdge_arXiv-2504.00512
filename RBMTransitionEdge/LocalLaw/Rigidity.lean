module

public import RBMTransitionEdge.LocalLaw.Counting
public import RBMTransitionEdge.LocalLaw.Outside

@[expose] public section

/-!
# Rigidity of the eigenvalues

(2.24) [eq:rigidity] of Lemma 2.9 [lem_loc] for the class `LLClass`: the eigenvalue counting that
follows from the averaged local law (2.23) [eq:aver_local], together with the spectral inclusion,
gives `|λ_k - γ_k| ≤ N^{τ'} N^{-2/3} 𝔯(k)^{-1/3}` for all `k` at once.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `N^a ≥ c` for all large `N`, when `a > 0`. -/
private lemma Rig_ev (c a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop c)

/-- `N^a ≤ (DN)^b` for `1 ≤ D ≤ N^{b-a}`, `N ≥ 1`, `a ≤ b` and `b ≥ -1`. -/
private lemma Rig_cmp (D N a b : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hb : 0 ≤ b + 1)
    (hDN : D ≤ N ^ (b - a)) : N ^ a ≤ (D * N) ^ b := by
  have hD0 : 0 < D := by linarith
  have hN0 : 0 < N := by linarith
  rw [Real.mul_rpow hD0.le hN0.le]
  have e1 : N ^ b = N ^ (b - a) * N ^ a := by rw [← Real.rpow_add hN0]; ring_nf
  have e2 : D ^ b * D = D ^ (b + 1) := by rw [Real.rpow_add hD0, Real.rpow_one]
  have h1 : 1 ≤ D ^ (b + 1) := Real.one_le_rpow hD hb
  have hDb : 0 ≤ D ^ b := Real.rpow_nonneg hD0.le _
  have hNa : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le _
  calc N ^ a ≤ D ^ (b + 1) * N ^ a := le_mul_of_one_le_left hNa h1
    _ = D ^ b * D * N ^ a := by rw [e2]
    _ ≤ D ^ b * N ^ (b - a) * N ^ a := by gcongr
    _ = D ^ b * N ^ b := by rw [e1]; ring

/-- `‖I‖ ≤ 1`. -/
private lemma Rig_opNorm_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- (2.24) [eq:rigidity] of Lemma 2.9 [lem_loc] for the class `LLClass`, uniformly in
`θ ∈ [0, 1]` and in `k ∈ ⟦1, DN⟧`: outside an event of probability `≤ N^{-D'}`,
`|λ_k - γ_k| ≤ N^{τ'} N^{-2/3} 𝔯(k)^{-1/3}` for every `k`, `γ_k` the quantile (2.20)
[eq:gammak] of `ρ_N`. -/
theorem rigidity (D : ℕ) (hD : 1 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        μ {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
            (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
              |eigK (Matrix.of h + lam D N A) k - quant (rho (lam D N A)) (D * N) k|} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  set s : ℝ := min τ' (1 / 5) / 8 with hs_def
  have hs0 : 0 < s := by positivity
  have hsτ : s ≤ τ' / 8 := by
    have := min_le_left τ' (1 / 5); rw [hs_def]; linarith
  have hs1 : s ≤ 1 / 40 := by
    have := min_le_right τ' (1 / 5); rw [hs_def]; linarith
  obtain ⟨N₁, h₁⟩ := aver_local D hD δA (s / 2) hδA (by positivity) C (s / 2) (by positivity)
    (D' + 1) (by linarith)
  obtain ⟨N₂, h₂⟩ := spec_inclusion D hD δA hδA C s hs0 (D' + 1) (by linarith)
  obtain ⟨n₃, h₃⟩ := count_of_aver s hs0 (by linarith)
  obtain ⟨n₄, h₄⟩ := rigidity_of_count (2 * s) (by linarith) (by linarith)
  obtain ⟨N₅, h₅⟩ := Rig_ev (D : ℝ) (s / 2) (by positivity)
  obtain ⟨N₆, h₆⟩ := Rig_ev 20 δA hδA
  refine ⟨max (max (max N₁ N₂) (max n₃ n₄)) (max (max N₅ N₆) 2), ?_⟩
  intro N hN θ hθ0 hθ1 μ hμ A hA
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN₁, hN₂⟩, hn₃, hn₄⟩, ⟨hN₅, hN₆⟩, hN2⟩ := hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set Λ := lam D N A with hΛ_def
  set n := Fintype.card (Idx D N) with hn_def
  have hcard : n = D * N := by simp [hn_def]
  have hnr : (n : ℝ) = (D : ℝ) * N := by rw [hcard]; push_cast; ring
  have hNn : (N : ℝ) ≤ n := by rw [hnr]; nlinarith
  have hn₃' : n₃ ≤ n := by rw [hcard]; nlinarith
  have hn₄' : n₄ ≤ n := by rw [hcard]; nlinarith
  -- `‖Λ‖ ≤ 1/10`
  have hΛH : Λ.IsHermitian := lam_isHermitian D N A
  have hΛn : opNorm Λ ≤ 1 / 10 := by
    have h1 := opNorm_lam_le D N A
    have h4 : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
      rw [Real.rpow_neg hN0.le, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (h₆ N hN₆)
    linarith
  -- the exponent comparisons `D^{1-s} ≤ N^{s/2}` and `D^{2/3-2s} ≤ N^s`
  have hDs2 : (D : ℝ) ≤ (N : ℝ) ^ (s / 2) := h₅ N hN₅
  have hDs : (D : ℝ) ≤ (N : ℝ) ^ s :=
    hDs2.trans (Real.rpow_le_rpow_of_exponent_le hNr (by linarith))
  have hE1 : (N : ℝ) ^ (-1 + s / 2) ≤ (n : ℝ) ^ (-1 + s) := by
    rw [hnr]
    exact Rig_cmp D N _ _ hDr hNr (by linarith) (by convert hDs2 using 2; ring)
  have hE2 : (N : ℝ) ^ (-(2 / 3 : ℝ) + s) ≤ (n : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s) := by
    rw [hnr]
    exact Rig_cmp D N _ _ hDr hNr (by linarith) (by convert hDs using 2; ring)
  -- the three bad events
  set S₁ : Set (Idx D N → Idx D N → ℂ) := {h | ∃ z ∈ specDom (s / 2) N,
      (N : ℝ) ^ (s / 2) * (1 / ((N : ℝ) * |z.im|)) <
        ‖ntr ((res (Matrix.of h + Λ) z - MExt Λ z) * 1)‖} with hS₁
  set S₂ : Set (Idx D N → Idx D N → ℂ) := {h | Eplus Λ + (N : ℝ) ^ (-(2 / 3 : ℝ) + s) <
        eigK (Matrix.of h + Λ) 1 ∨
      eigK (Matrix.of h + Λ) (D * N) < Eminus Λ - (N : ℝ) ^ (-(2 / 3 : ℝ) + s)} with hS₂
  set S₃ : Set (Idx D N → Idx D N → ℂ) := {h | ¬ (Matrix.of h).IsHermitian} with hS₃
  have hμ₁ : μ S₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    h₁ N hN₁ θ hθ0 hθ1 μ hμ A hA 1 Rig_opNorm_one
  have hμ₂ : μ S₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := h₂ N hN₂ θ hθ0 hθ1 μ hμ A hA
  have hμ₃ : μ S₃ = 0 := ae_iff.mp hμ.herm
  -- on the good event, the rigidity bound holds for every `k`
  have hsub : {h : Idx D N → Idx D N → ℂ | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
      (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
        |eigK (Matrix.of h + Λ) k - quant (rho Λ) (D * N) k|} ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro h ⟨k, hk1, hkn, hlt⟩
    by_contra hgood
    simp only [Set.mem_union, not_or] at hgood
    obtain ⟨⟨hg₁, hg₂⟩, hg₃⟩ := hgood
    simp only [hS₁, hS₂, hS₃, Set.mem_ofPred_eq, not_exists, not_and, not_lt, not_or,
      not_not] at hg₁ hg₂ hg₃
    set X := Matrix.of h + Λ with hX_def
    have hXH : X.IsHermitian := hg₃.add hΛH
    -- the averaged law on `{|Re z| ≤ 4, n^{-1+s} ≤ Im z ≤ 1}`
    have hLL : ∀ z : ℂ, |z.re| ≤ 4 → (n : ℝ) ^ (-1 + s) ≤ z.im → z.im ≤ 1 →
        ‖ntr (res X z - MSol Λ z)‖ ≤ (n : ℝ) ^ s / ((n : ℝ) * z.im) := by
      intro z hre him1 him2
      have hn0 : (0 : ℝ) < n := by linarith
      have hηpos : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) him1
      have hz : z ∈ specDom (s / 2) N := by
        refine ⟨?_, ?_⟩
        · have h1 := Complex.norm_le_abs_re_add_abs_im z
          have h2 : |z.im| ≤ 1 := by rw [abs_of_pos hηpos]; exact him2
          have h3 : (80 : ℝ) ≤ (s / 2)⁻¹ := by
            rw [le_inv_comm₀ (by norm_num) (by positivity)]; linarith
          linarith
        · rw [abs_of_pos hηpos]; exact hE1.trans him1
      have hb := hg₁ z hz
      have hM : MExt Λ z = MSol Λ z := by simp [MExt, MSol, mExt, hηpos]
      rw [hM, mul_one, abs_of_pos hηpos] at hb
      refine hb.trans ?_
      have eN : (N : ℝ) ^ (s / 2) * (1 / ((N : ℝ) * z.im)) = (N : ℝ) ^ (-1 + s / 2) / z.im := by
        rw [Real.rpow_add hN0, Real.rpow_neg_one]; field_simp
      have en : (n : ℝ) ^ s / ((n : ℝ) * z.im) = (n : ℝ) ^ (-1 + s) / z.im := by
        rw [Real.rpow_add hn0, Real.rpow_neg_one]; field_simp
      rw [eN, en]
      exact div_le_div_of_nonneg_right hE1 hηpos.le
    have hcount := h₃ (Idx D N) hn₃' Λ hΛH hΛn X hXH hLL
    have hlo : Eminus Λ - (n : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s) ≤ eigK X n := by
      have heig : eigK X n = eigK X (D * N) := by rw [hcard]
      linarith [hg₂.2]
    have hhi : eigK X 1 ≤ Eplus Λ + (n : ℝ) ^ (-(2 / 3 : ℝ) + 2 * s) := by
      linarith [hg₂.1]
    have hkn' : k ≤ n := by rw [hcard]; exact hkn
    have hrig := h₄ (Idx D N) hn₄' Λ hΛH hΛn X hXH hlo hhi hcount k hk1 hkn'
    rw [← hn_def] at hrig
    have hrk : rk 1 n k = rk D N k := by rw [hcard]; simp [rk]
    have hq : quant (rho Λ) n k = quant (rho Λ) (D * N) k := by rw [hcard]
    rw [hrk, hq] at hrig
    -- `n^{6s} n^{-2/3} ≤ N^{τ'} N^{-2/3}`
    have hpow : (n : ℝ) ^ (3 * (2 * s)) * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤
        (N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have hn0 : (0 : ℝ) < n := by linarith
      rw [← Real.rpow_add hn0, ← Real.rpow_add hN0]
      calc (n : ℝ) ^ (3 * (2 * s) + -(2 / 3 : ℝ))
          ≤ (N : ℝ) ^ (3 * (2 * s) + -(2 / 3 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hN0 hNn (by linarith)
        _ ≤ (N : ℝ) ^ (τ' + -(2 / 3 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have hrk0 : 0 ≤ rk D N k ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by simp [rk]) _
    have hfin : (n : ℝ) ^ (3 * (2 * s)) * ((n : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ)))
        ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) := by
      rw [← mul_assoc ((n : ℝ) ^ (3 * (2 * s))), ← mul_assoc ((N : ℝ) ^ τ')]
      exact mul_le_mul_of_nonneg_right hpow hrk0
    exact (not_le.mpr hlt) (hrig.trans hfin)
  -- the union bound
  have hpos : 0 ≤ (N : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hN0.le _
  have h2N : 2 * (N : ℝ) ^ (-(D' + 1)) ≤ (N : ℝ) ^ (-D') := by
    have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [show -(D' + 1) = -D' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hD'0 : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
    rw [e]
    have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2r
    nlinarith
  calc μ _ ≤ μ (S₁ ∪ S₂ ∪ S₃) := measure_mono hsub
    _ ≤ μ S₁ + μ S₂ + μ S₃ := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + 0 := by
        rw [hμ₃]; gcongr
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D' + 1))) := by
        rw [add_zero, ← ENNReal.ofReal_add hpos hpos, two_mul]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal h2N

end RBMTransitionEdge

end
