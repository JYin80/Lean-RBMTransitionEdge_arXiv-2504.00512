module

public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# The discrete Duhamel formula

The discrete propagator, the discrete Duhamel formula and its norm bound, which replace (3.65)
[eq:PBintegral]–(3.68) [Phinorm] on the grid; the Riemann-sum bound for `s ↦ (t_c − s)⁻¹`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The discrete propagator `Φ(k, j) = A_{k-1} ∘ ⋯ ∘ A_j` (identity for `k ≤ j`). -/
def propag (A : ℕ → E →L[ℂ] E) (j : ℕ) : ℕ → E →L[ℂ] E
  | 0 => ContinuousLinearMap.id ℂ E
  | k + 1 => if k + 1 ≤ j then ContinuousLinearMap.id ℂ E else (A k).comp (propag A j k)

/-- `Φ(k + 1, j) = id` when `k + 1 ≤ j`. -/
private lemma Flow_propag_succ_of_le {A : ℕ → E →L[ℂ] E} {j k : ℕ} (h : k + 1 ≤ j) :
    propag A j (k + 1) = ContinuousLinearMap.id ℂ E := by
  simp [propag, h]

/-- `Φ(k + 1, j) = A_k ∘ Φ(k, j)` when `j ≤ k`. -/
private lemma Flow_propag_succ_of_lt {A : ℕ → E →L[ℂ] E} {j k : ℕ} (h : j ≤ k) :
    propag A j (k + 1) = (A k).comp (propag A j k) := by
  have : ¬ k + 1 ≤ j := by omega
  simp [propag, this]

/-- Discrete Duhamel: `x_{k+1} = A_k x_k + b_k` gives `x_k = Φ(k, 0) x_0 + Σ_{j<k} Φ(k, j+1) b_j`. -/
theorem discrete_duhamel (A : ℕ → E →L[ℂ] E) (x b : ℕ → E)
    (hx : ∀ k, x (k + 1) = A k (x k) + b k) (k : ℕ) :
    x k = propag A 0 k (x 0) + ∑ j ∈ Finset.range k, propag A (j + 1) k (b j) := by
  induction k with
  | zero => simp [propag]
  | succ k ih =>
    have h2 : ∀ j ∈ Finset.range k,
        propag A (j + 1) (k + 1) (b j) = A k (propag A (j + 1) k (b j)) := by
      intro j hj
      rw [Flow_propag_succ_of_lt (Nat.succ_le_of_lt (Finset.mem_range.mp hj))]
      rfl
    rw [hx k, ih, Finset.sum_range_succ, Finset.sum_congr rfl h2,
      Flow_propag_succ_of_lt (Nat.zero_le k), Flow_propag_succ_of_le (le_refl (k + 1))]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_add, map_sum]
    abel

/-- `‖Φ(k, j)‖ ≤ Π_{j ≤ i < k} ‖A_i‖`. -/
theorem norm_propag_le (A : ℕ → E →L[ℂ] E) (j k : ℕ) :
    ‖propag A j k‖ ≤ ∏ i ∈ Finset.Ico j k, ‖A i‖ := by
  induction k with
  | zero => simpa [propag] using ContinuousLinearMap.norm_id_le
  | succ k ih =>
    by_cases h : j ≤ k
    · rw [Flow_propag_succ_of_lt h, Finset.prod_Ico_succ_top h]
      calc ‖(A k).comp (propag A j k)‖ ≤ ‖A k‖ * ‖propag A j k‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A k‖ * ∏ i ∈ Finset.Ico j k, ‖A i‖ :=
            mul_le_mul_of_nonneg_left ih (norm_nonneg _)
        _ = _ := mul_comm _ _
    · have h' : k + 1 ≤ j := by omega
      rw [Flow_propag_succ_of_le h', Finset.Ico_eq_empty_of_le h', Finset.prod_empty]
      exact ContinuousLinearMap.norm_id_le

/-- One cell: `h / a ≤ log (a / (a - h))` for `0 < h < a`. -/
private lemma Flow_riemann_step (a h : ℝ) (hh : 0 < h) (ha : 0 < a - h) :
    h / a ≤ Real.log (a / (a - h)) := by
  have ha0 : 0 < a := by linarith
  have := Real.log_le_sub_one_of_pos (div_pos ha ha0)
  rw [Real.log_div ha.ne' ha0.ne'] at this
  rw [Real.log_div ha0.ne' ha.ne']
  have e : (a - h) / a - 1 = -(h / a) := by field_simp; ring
  linarith

/-- The left Riemann sum of the increasing `s ↦ (t_c - s)⁻¹` on the grid `u_i = u₀ + i h` is at most
its integral: `Σ_{j ≤ i < k} h / (t_c - u_i) ≤ log((t_c - u_j) / (t_c - u_k))`. -/
theorem riemann_inv_le_log (u₀ h tc : ℝ) (hh : 0 < h) (j k : ℕ) (hjk : j ≤ k)
    (hk : u₀ + k * h < tc) :
    ∑ i ∈ Finset.Ico j k, h / (tc - (u₀ + i * h)) ≤
      Real.log ((tc - (u₀ + j * h)) / (tc - (u₀ + k * h))) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have hid : tc - (u₀ + ((k + 1 : ℕ) : ℝ) * h) = (tc - (u₀ + k * h)) - h := by
      push_cast; ring
    have hpos : 0 < (tc - (u₀ + k * h)) - h := by rw [← hid]; linarith
    rw [hid]
    have ha : 0 < tc - (u₀ + k * h) := by linarith
    have hj : 0 < tc - (u₀ + j * h) := by
      have : (j : ℝ) ≤ k := by exact_mod_cast hjk
      nlinarith
    rw [Finset.sum_Ico_succ_top hjk]
    have key := Flow_riemann_step (tc - (u₀ + k * h)) h hh hpos
    have ih' := ih (by linarith)
    have e2 : Real.log ((tc - (u₀ + j * h)) / ((tc - (u₀ + k * h)) - h)) =
        Real.log ((tc - (u₀ + j * h)) / (tc - (u₀ + k * h))) +
        Real.log ((tc - (u₀ + k * h)) / ((tc - (u₀ + k * h)) - h)) := by
      rw [← Real.log_mul (div_pos hj ha).ne' (div_pos ha hpos).ne']
      congr 1
      exact (div_mul_div_cancel₀ ha.ne').symm
    linarith

end RBMTransitionEdge

end
