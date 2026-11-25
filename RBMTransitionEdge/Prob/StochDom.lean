module

public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# Stochastic domination (Definition 2.8)

The union form `PrecU` and the sup form `PrecS` of Definition 2.8 [stoch_domination], and the net
argument for a parameter in a compact set of `ℂ`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]

/-- Definition 2.8 [stoch_domination], union form: `P(∪_u {ξ(u) > N^τ ζ(u)}) ≤ N^{-D'}` for
`N ≥ N₀(τ, D')`. -/
def PrecU (P : ∀ N, Measure (Ω N)) {U : ℕ → Type*} (ξ ζ : ∀ N, U N → Ω N → ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    P N {ω | ∃ u, (N : ℝ) ^ τ * ζ N u ω < ξ N u ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))

/-- Definition 2.8 [stoch_domination], sup form: `sup_u P(ξ(u) > N^τ ζ(u)) ≤ N^{-D'}` for
`N ≥ N₀(τ, D')`. -/
def PrecS (P : ∀ N, Measure (Ω N)) {U : ℕ → Type*} (ξ ζ : ∀ N, U N → Ω N → ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ u,
    P N {ω | (N : ℝ) ^ τ * ζ N u ω < ξ N u ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D'))

/-- `A x^K x^{-(D+K+1)} ≤ x^{-D}` for `0 < x` and `A ≤ x`. -/
private lemma rpow_tail {x A K D : ℝ} (hx : 0 < x) (hA : A ≤ x) :
    A * x ^ K * x ^ (-(D + K + 1)) ≤ x ^ (-D) := by
  have h1 : x ^ K * x ^ (-(D + K + 1)) = x ^ (-D) * x⁻¹ := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring
  have h2 : 0 ≤ x ^ (-D) := Real.rpow_nonneg hx.le _
  have h3 : A * x⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hx).mpr hA
  calc A * x ^ K * x ^ (-(D + K + 1)) = x ^ (-D) * (A * x⁻¹) := by rw [mul_assoc, h1]; ring
    _ ≤ x ^ (-D) * 1 := mul_le_mul_of_nonneg_left h3 h2
    _ = x ^ (-D) := mul_one _

/-- `N^τ ≥ c` for all large `N`, when `τ > 0`. -/
private lemma exists_rpow_ge {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → c ≤ (N : ℝ) ^ τ :=
  eventually_atTop.mp
    (((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c)

/-- A finite subset of `S ⊆ closedBall 0 R` with at most `(2R/h + 1)²` points whose
`2h`-neighbourhoods cover `S`. -/
private lemma exists_net (S : Set ℂ) {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hS : S ⊆ Metric.closedBall 0 R) :
    ∃ F : Finset ℂ, (↑F ⊆ S) ∧ (F.card : ℝ) ≤ (2 * R / h + 1) ^ 2 ∧
      ∀ u ∈ S, ∃ v ∈ F, ‖u - v‖ < 2 * h := by
  classical
  let q : ℂ → ℕ × ℕ := fun u => (⌊(u.re + R) / h⌋₊, ⌊(u.im + R) / h⌋₊)
  let M := ⌊2 * R / h⌋₊
  let B := (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter (fun g => ∃ u ∈ S, q u = g)
  let r : ℕ × ℕ → ℂ := fun g => if hg : ∃ u ∈ S, q u = g then hg.choose else 0
  have hr : ∀ g, (hg : ∃ u ∈ S, q u = g) → r g ∈ S ∧ q (r g) = g := fun g hg => by
    simp only [r, hg, ↓reduceDIte]
    exact hg.choose_spec
  have hnorm : ∀ u ∈ S, -R ≤ u.re ∧ u.re ≤ R ∧ -R ≤ u.im ∧ u.im ≤ R := by
    intro u hu
    have hu' : ‖u‖ ≤ R := by simpa using hS hu
    have hre := (abs_le.mp ((Complex.abs_re_le_norm u).trans hu'))
    have him := (abs_le.mp ((Complex.abs_im_le_norm u).trans hu'))
    exact ⟨hre.1, hre.2, him.1, him.2⟩
  have cell : ∀ x y : ℝ, -R ≤ x → -R ≤ y → ⌊(x + R) / h⌋₊ = ⌊(y + R) / h⌋₊ → |x - y| < h := by
    intro x y hx hy hxy
    have ax := Nat.floor_le (div_nonneg (by linarith : 0 ≤ x + R) hh.le)
    have bx := Nat.lt_floor_add_one ((x + R) / h)
    have ay := Nat.floor_le (div_nonneg (by linarith : 0 ≤ y + R) hh.le)
    have by' := Nat.lt_floor_add_one ((y + R) / h)
    rw [hxy] at ax bx
    have h1 : |(x + R) / h - (y + R) / h| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have e : x - y = h * ((x + R) / h - (y + R) / h) := by field_simp; ring
    rw [e, abs_mul, abs_of_pos hh]
    calc h * |(x + R) / h - (y + R) / h| < h * 1 := mul_lt_mul_of_pos_left h1 hh
      _ = h := mul_one h
  refine ⟨B.image r, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨g, hg, rfl⟩ := hv
    exact (hr g (Finset.mem_filter.mp hg).2).1
  · have h1 : (B.image r).card ≤ (M + 1) * (M + 1) :=
      Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (by simp))
    have h2 : (M : ℝ) ≤ 2 * R / h := Nat.floor_le (by positivity)
    calc ((B.image r).card : ℝ) ≤ ((M + 1) * (M + 1) : ℕ) := by exact_mod_cast h1
      _ = ((M : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ (2 * R / h + 1) ^ 2 := by gcongr
  · intro u hu
    obtain ⟨hu1, hu2, hu3, hu4⟩ := hnorm u hu
    have hqmem : q u ∈ B := by
      refine Finset.mem_filter.mpr ⟨?_, u, hu, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff, q, M]
      constructor <;> apply Nat.floor_le_floor <;> apply div_le_div_of_nonneg_right _ hh.le <;>
        linarith
    obtain ⟨hvS, hqv⟩ := hr (q u) ⟨u, hu, rfl⟩
    refine ⟨r (q u), Finset.mem_image_of_mem r hqmem, ?_⟩
    obtain ⟨hv1, -, hv3, -⟩ := hnorm _ hvS
    simp only [q, Prod.mk.injEq] at hqv
    calc ‖u - r (q u)‖ ≤ |(u - r (q u)).re| + |(u - r (q u)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ < h + h := by
          rw [Complex.sub_re, Complex.sub_im]
          exact add_lt_add (cell _ _ hu1 hv1 hqv.1.symm) (cell _ _ hu3 hv3 hqv.2.symm)
      _ = 2 * h := by ring

/-- The net argument: on parameter sets in `ℂ` of polynomial size, a quantity that is
`N^{C_L}`-Lipschitz in the parameter, dominated by a `N^{C_L}`-Lipschitz `ζ ≥ N^{-C_ζ}` in sup form,
is dominated in union form. -/
theorem precS_precU_net (P : ∀ N, Measure (Ω N)) (S : ℕ → Set ℂ) (CR CL Cζ : ℝ)
    (hS : ∀ N, 1 ≤ N → S N ⊆ Metric.closedBall 0 ((N : ℝ) ^ CR)) (ξ ζ : ∀ N, ℂ → Ω N → ℝ)
    (hLξ : ∀ N ω, 1 ≤ N → ∀ u ∈ S N, ∀ v ∈ S N, |ξ N u ω - ξ N v ω| ≤ (N : ℝ) ^ CL * ‖u - v‖)
    (hLζ : ∀ N ω, 1 ≤ N → ∀ u ∈ S N, ∀ v ∈ S N, |ζ N u ω - ζ N v ω| ≤ (N : ℝ) ^ CL * ‖u - v‖)
    (hζ : ∀ N ω, 1 ≤ N → ∀ u ∈ S N, (N : ℝ) ^ (-Cζ) ≤ ζ N u ω)
    (h : PrecS P (fun N (u : S N) => ξ N u) fun N (u : S N) => ζ N u) :
    PrecU P (fun N (u : S N) => ξ N u) fun N (u : S N) => ζ N u := by
  intro τ hτ D' hD
  set K := max (CR + CL + Cζ) 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  obtain ⟨N₁, hN₁⟩ := h (τ / 2) (by linarith) (D' + (K + K) + 1) (by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_rpow_ge (by linarith : 0 < τ / 2) 3
  refine ⟨max (max N₁ N₂) 25, fun N hN => ?_⟩
  have hN1' : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2' : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN25 : (25 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hN1 : 1 ≤ N := by have := (le_max_right _ _).trans hN; omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hR : 0 ≤ (N : ℝ) ^ CR := Real.rpow_nonneg hNpos.le _
  have hh : 0 < (N : ℝ) ^ (-(CL + Cζ)) / 2 := by
    have := Real.rpow_pos_of_pos hNpos (-(CL + Cζ))
    linarith
  obtain ⟨F, hFS, hFcard, hFnet⟩ := exists_net (S N) hR hh (hS N hN1)
  have hRh : 2 * (N : ℝ) ^ CR / ((N : ℝ) ^ (-(CL + Cζ)) / 2) = 4 * (N : ℝ) ^ (CR + CL + Cζ) := by
    rw [show CR + CL + Cζ = CR + (CL + Cζ) by ring, Real.rpow_add hNpos, Real.rpow_neg hNpos.le]
    have : (0 : ℝ) < (N : ℝ) ^ (CL + Cζ) := Real.rpow_pos_of_pos hNpos _
    field_simp
    ring
  have hcard : (F.card : ℝ) ≤ 25 * (N : ℝ) ^ (K + K) := by
    have e1 : (N : ℝ) ^ (CR + CL + Cζ) ≤ (N : ℝ) ^ K :=
      Real.rpow_le_rpow_of_exponent_le hNr (le_max_left _ _)
    have e2 : (1 : ℝ) ≤ (N : ℝ) ^ K := Real.one_le_rpow hNr hK
    have e0 : 0 ≤ (N : ℝ) ^ (CR + CL + Cζ) := Real.rpow_nonneg hNpos.le _
    calc (F.card : ℝ) ≤ (4 * (N : ℝ) ^ (CR + CL + Cζ) + 1) ^ 2 := by rw [← hRh]; exact hFcard
      _ ≤ (5 * (N : ℝ) ^ K) ^ 2 := by gcongr; linarith
      _ = 25 * (N : ℝ) ^ (K + K) := by rw [Real.rpow_add hNpos]; ring
  have hsub : {ω | ∃ u : S N, (N : ℝ) ^ τ * ζ N u ω < ξ N u ω} ⊆
      ⋃ v ∈ F, {ω | (N : ℝ) ^ (τ / 2) * ζ N v ω < ξ N v ω} := by
    rintro ω ⟨⟨u, hu⟩, hlt⟩
    obtain ⟨v, hvF, huv⟩ := hFnet u hu
    have hv : v ∈ S N := hFS hvF
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨v, hvF, ?_⟩
    have ha : (3 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := hN₂ N hN2'
    have hsq : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hNpos]
      ring_nf
    have he : (N : ℝ) ^ CL * ‖u - v‖ ≤ (N : ℝ) ^ (-Cζ) :=
      calc (N : ℝ) ^ CL * ‖u - v‖ ≤ (N : ℝ) ^ CL * (2 * ((N : ℝ) ^ (-(CL + Cζ)) / 2)) :=
            mul_le_mul_of_nonneg_left huv.le (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ (-Cζ) := by
            rw [mul_div_cancel₀ _ (two_ne_zero), ← Real.rpow_add hNpos]
            ring_nf
    have hζu : (N : ℝ) ^ (-Cζ) ≤ ζ N u ω := hζ N ω hN1 u hu
    have he0 : 0 ≤ (N : ℝ) ^ (-Cζ) := Real.rpow_nonneg hNpos.le _
    have h1 := abs_le.mp (hLξ N ω hN1 u hu v hv)
    have h2 := abs_le.mp (hLζ N ω hN1 u hu v hv)
    simp only at hlt
    rw [hsq] at hlt
    have hζv : ζ N v ω ≤ ζ N u ω + (N : ℝ) ^ (-Cζ) := by linarith
    have key : (N : ℝ) ^ (τ / 2) * (ζ N u ω + (N : ℝ) ^ (-Cζ)) ≤
        (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) * ζ N u ω - (N : ℝ) ^ (-Cζ) := by
      nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) -
          (N : ℝ) ^ (τ / 2)) (by linarith : (0 : ℝ) ≤ ζ N u ω - (N : ℝ) ^ (-Cζ)),
        mul_nonneg (by nlinarith : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) -
          2 * (N : ℝ) ^ (τ / 2) - 1) he0]
    have h3 : (N : ℝ) ^ (τ / 2) * ζ N v ω ≤ (N : ℝ) ^ (τ / 2) * (ζ N u ω + (N : ℝ) ^ (-Cζ)) :=
      mul_le_mul_of_nonneg_left hζv (by linarith)
    linarith
  calc P N {ω | ∃ u : S N, (N : ℝ) ^ τ * ζ N u ω < ξ N u ω}
      ≤ P N (⋃ v ∈ F, {ω | (N : ℝ) ^ (τ / 2) * ζ N v ω < ξ N v ω}) := measure_mono hsub
    _ ≤ ∑ v ∈ F, P N {ω | (N : ℝ) ^ (τ / 2) * ζ N v ω < ξ N v ω} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ F, ENNReal.ofReal ((N : ℝ) ^ (-(D' + (K + K) + 1))) :=
        Finset.sum_le_sum fun v hv => hN₁ N hN1' ⟨v, hFS hv⟩
    _ = ENNReal.ofReal ((F.card : ℝ) * (N : ℝ) ^ (-(D' + (K + K) + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
        apply ENNReal.ofReal_le_ofReal
        calc (F.card : ℝ) * (N : ℝ) ^ (-(D' + (K + K) + 1))
            ≤ 25 * (N : ℝ) ^ (K + K) * (N : ℝ) ^ (-(D' + (K + K) + 1)) :=
              mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hNpos.le _)
          _ ≤ (N : ℝ) ^ (-D') := rpow_tail hNpos hN25

end RBMTransitionEdge

end
