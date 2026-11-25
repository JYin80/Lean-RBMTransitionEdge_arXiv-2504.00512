module

public import RBMTransitionEdge.Prob.Grid
public import RBMTransitionEdge.Prob.GaussianIBP

@[expose] public section

/-!
# Martingale tools on the discrete grid

Standard Borel space instances for the coordinate spaces of the grid, and Doob's `L²` maximal
inequality, used in the stopping argument after (3.70) [eq:self_imp].
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The coordinates of one block form a standard Borel space. -/
instance GridMartingale_sbsCoords (n : ℕ) : StandardBorelSpace (Coords n) := inferInstance

/-- The block arrays form a standard Borel space. -/
instance GridMartingale_sbsBlocks (D N : ℕ) : StandardBorelSpace (Fin D → Coords N) := inferInstance

/-- The increments of the grid form a standard Borel space. -/
instance GridMartingale_sbsIncr (D K N : ℕ) : StandardBorelSpace (Fin K → Fin D → Coords N) :=
  inferInstance

/-! ### Doob's `L²` maximal inequality -/

/-- The square of a square-integrable martingale is a submartingale. -/
private theorem gmSq_submartingale {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ (inferInstance : MeasurableSpace Ω'))
    (M : ℕ → Ω' → ℝ) (hM : Martingale M 𝓕 μ) (hM2 : ∀ k, MemLp (M k) 2 μ) :
    Submartingale (fun k ω => M k ω ^ 2) 𝓕 μ := by
  refine ⟨fun k => ?_, fun i j hij => ?_, fun k => (hM2 k).integrable_sq⟩
  · exact ((hM.stronglyAdapted k).measurable.pow_const 2).stronglyMeasurable
  · have hJ := ConvexOn.map_condExp_le_univ (μ := μ) (𝓕.le i) (φ := fun x : ℝ => x ^ 2)
      (even_two.convexOn_pow) (continuous_pow 2).lowerSemicontinuous
      ((hM2 j).integrable one_le_two) (hM2 j).integrable_sq
    filter_upwards [hJ, hM.condExp_ae_eq hij] with ω h1 h2
    simp only [Function.comp] at h1
    rw [h2] at h1
    exact h1

/-- Doob's `L²` maximal inequality for a square-integrable martingale:
`P(max_{k ≤ n} |M_k| ≥ ε) ≤ E M_n² / ε²`. -/
theorem doob_sq_maximal {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ (inferInstance : MeasurableSpace Ω')) (M : ℕ → Ω' → ℝ)
    (hM : Martingale M 𝓕 μ) (hM2 : ∀ k, MemLp (M k) 2 μ) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|} ≤
      (∫ ω, M n ω ^ 2 ∂μ) / ε ^ 2 := by
  have hsub := gmSq_submartingale μ 𝓕 M hM hM2
  have hmax := maximal_ineq hsub (fun k ω => sq_nonneg (M k ω)) (ε := ⟨ε ^ 2, by positivity⟩) n
  have hset : {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |M k ω|} = {ω | ((⟨ε ^ 2, by positivity⟩ : ℝ≥0) : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => M k ω ^ 2} := by
    ext ω
    simp only [Finset.le_sup'_iff]
    refine exists_congr fun k => and_congr_right fun _ => ?_
    rw [sq_le_sq, abs_of_pos hε]
  have key := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (setIntegral_nonneg_of_ae (ae_of_all _ fun ω => sq_nonneg _))] at key
  have hint := setIntegral_le_integral (s := {ω | ((⟨ε ^ 2, by positivity⟩ : ℝ≥0) : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => M k ω ^ 2})
    (hM2 n).integrable_sq (ae_of_all _ fun ω => sq_nonneg _)
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  rw [le_div_iff₀ hε2, hset, mul_comm]
  exact key.trans hint


end RBMTransitionEdge

end
