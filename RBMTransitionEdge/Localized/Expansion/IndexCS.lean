module

public import Mathlib

@[expose] public section

/-!
# The label Cauchy–Schwarz step of the direct estimation of Lemma 5.5

The deterministic step of (5.70) [Cauchy_example_1] and (5.71) [Cauchy_example_2] in the proof of
Lemma 5.5 [claim_estimate_remainder_terms]: a sum over two labels of a product of nonnegative
factors, with two factors in `ℓ²` and the other bounded.

The statement is a deterministic inequality on finite sums; the paper uses this step inline in
(5.70) and (5.71).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The Cauchy–Schwarz step of (5.70) [Cauchy_example_1] and (5.71) [Cauchy_example_2]: two
factors in `ℓ²` over both labels, the others bounded by their supremum `B`. -/
theorem idxcs_pair {ι : Type*} [Fintype ι] (a b c : ι → ι → ℝ) (B : ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hb : ∀ i j, 0 ≤ b i j) (hc : ∀ i j, 0 ≤ c i j ∧ c i j ≤ B) :
    ∑ i, ∑ j, a i j * b i j * c i j ≤
      B * Real.sqrt (∑ i, ∑ j, a i j ^ 2) * Real.sqrt (∑ i, ∑ j, b i j ^ 2) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp
  · have hB : 0 ≤ B := (hc i₀ i₀).1.trans (hc i₀ i₀).2
    have h1 : ∑ i, ∑ j, a i j * b i j * c i j ≤ ∑ i, ∑ j, B * (a i j * b i j) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      have := mul_nonneg (ha i j) (hb i j)
      nlinarith [(hc i j).2]
    have h2 : ∑ i, ∑ j, B * (a i j * b i j) = B * ∑ p : ι × ι, a p.1 p.2 * b p.1 p.2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
    have h3 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
      (fun p => a p.1 p.2) (fun p => b p.1 p.2)
    simp only [Fintype.sum_prod_type] at h3
    calc ∑ i, ∑ j, a i j * b i j * c i j ≤ _ := h1
      _ = _ := h2
      _ ≤ B * (Real.sqrt (∑ i, ∑ j, a i j ^ 2) * Real.sqrt (∑ i, ∑ j, b i j ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hB
        simpa [Fintype.sum_prod_type] using h3
      _ = _ := by ring

end RBMTransitionEdge

end
