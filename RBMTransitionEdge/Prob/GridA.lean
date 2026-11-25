module

public import RBMTransitionEdge.Prob.BlockOU
public import RBMTransitionEdge.Prob.Grid

@[expose] public section

/-!
# The grid of the flow from an arbitrary initial law

The discrete grid of the flow (3.12) [eq:Ht] with the drift on all entries, started from a full
array with an arbitrary law: the probability space, the grid state, its filtration, and the
single-time law (3.13) [eq:Gauss_div] of the state at grid times.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The sample space of the grid with a full initial array and `K` block-GUE increments. -/
abbrev GridΩA (D N K : ℕ) := (Idx D N → Idx D N → ℂ) × (Fin K → Fin D → Coords N)

/-- The law `μ₀ ⊗ (⊗_{k<K} gueBlocks)` of the grid with initial law `μ₀`. -/
def gridLawA (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ)) : Measure (GridΩA D N K) :=
  μ₀.prod (Measure.pi fun _ : Fin K => gueBlocks D N)

/-- `gridLawA D N K μ₀` is a probability measure when `μ₀` is. -/
instance gridLawA_isProbabilityMeasure (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] : IsProbabilityMeasure (gridLawA D N K μ₀) := by
  unfold gridLawA
  infer_instance

/-- The exact step of the flow (3.12) [eq:Ht] with the drift on all entries:
`H_{k+1} = e^{-h/2} H_k + √(1 - e^{-h}) X_{k+1}` with `X_{k+1}` block-diagonal GUE. -/
def gridStateA (D N K : ℕ) (h : ℝ) (ω : GridΩA D N K) : ℕ → Idx D N → Idx D N → ℂ
  | 0 => ω.1
  | k + 1 => Real.exp (-h / 2) • gridStateA D N K h ω k +
      Real.sqrt (1 - Real.exp (-h)) •
        (if hk : k < K then Matrix.of.symm (blockH D N (ω.2 ⟨k, hk⟩)) else 0)

/-- The grid filtration `σ(H₀, X₁, …, X_k)` with a full initial array. -/
@[instance_reducible]
def gridFiltrA (D N K : ℕ) (k : ℕ) : MeasurableSpace (GridΩA D N K) :=
  MeasurableSpace.comap
    (fun ω : GridΩA D N K => (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0))
    inferInstance

/-- The array `Matrix.of.symm (blockH D N w)` of a block-GUE coordinate vector `w`. -/
private abbrev GridA_arr (D N : ℕ) (w : Fin D → Coords N) : Idx D N → Idx D N → ℂ :=
  Matrix.of.symm (blockH D N w)

/-- `GridA_arr` is additive (`wig_add` entrywise). -/
private theorem GridA_arr_add (D N : ℕ) (v w : Fin D → Coords N) :
    GridA_arr D N (v + w) = GridA_arr D N v + GridA_arr D N w := by
  ext p q
  simp only [GridA_arr, blockH, Pi.add_apply, wig_add, Matrix.add_apply, Matrix.of_symm_apply]
  split_ifs <;> simp

/-- `GridA_arr` is real-homogeneous (`wig_smul` entrywise). -/
private theorem GridA_arr_smul (D N : ℕ) (c : ℝ) (w : Fin D → Coords N) :
    GridA_arr D N (c • w) = c • GridA_arr D N w := by
  ext p q
  simp only [GridA_arr, blockH, Pi.smul_apply, wig_smul, Matrix.smul_apply, Matrix.of_symm_apply]
  split_ifs <;> simp [Complex.real_smul]

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private theorem GridA_measurable_wig (n : ℕ) (i j : Fin n) :
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

/-- `GridA_arr` is measurable. -/
private theorem GridA_arr_measurable (D N : ℕ) : Measurable (GridA_arr D N) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  by_cases h : p.1 = q.1
  · simp only [GridA_arr, blockH, h, ↓reduceIte, Matrix.of_symm_apply]
    exact (GridA_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
  · simp only [GridA_arr, blockH, h, ↓reduceIte, Matrix.of_symm_apply]
    exact measurable_const

/-- Scalar multiples of a measurable array-valued map are measurable. -/
private theorem GridA_meas_smul {α : Type*} [MeasurableSpace α] {D N : ℕ} (c : ℝ)
    {f : α → Idx D N → Idx D N → ℂ} (hf : Measurable f) : Measurable fun x => c • f x :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b =>
    (((measurable_pi_apply b).comp (measurable_pi_apply a)).comp hf).const_smul c

/-- Scalar multiples of a measurable block-valued map are measurable. -/
private theorem GridA_meas_smulB {α : Type*} [MeasurableSpace α] {D N : ℕ} (c : ℝ)
    {f : α → Fin D → Coords N} (hf : Measurable f) : Measurable fun x => c • f x :=
  measurable_pi_iff.2 fun a => ((measurable_pi_apply a).comp hf).const_smul c

/-- Measurability of a linear combination of two block-valued maps. -/
private theorem GridA_measB_comb {D N : ℕ} (a b : ℝ) :
    Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) => a • p.1 + b • p.2 :=
  (GridA_meas_smulB a measurable_fst).add (GridA_meas_smulB b measurable_snd)

/-- Measurability of `(a, w) ↦ c a + s A(w)` into the array. -/
private theorem GridA_meas_comb {D N : ℕ} (c s : ℝ) :
    Measurable fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      c • p.1 + s • GridA_arr D N p.2 :=
  (GridA_meas_smul c measurable_fst).add
    (GridA_meas_smul s ((GridA_arr_measurable D N).comp measurable_snd))

/-- The generating map of `gridFiltrA D N K k`: the initial array and the increments `X_{j+1}`,
`j < k`, with the others set to `0`. -/
private def GridA_mask (D N K k : ℕ) (ω : GridΩA D N K) : GridΩA D N K :=
  (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0)

private theorem GridA_mask_measurable (D N K k : ℕ) : Measurable (GridA_mask D N K k) := by
  unfold GridA_mask
  refine measurable_fst.prodMk (measurable_pi_iff.mpr fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simp [hj]

private theorem GridA_mask_mask {D N K k k' : ℕ} (hkk' : k ≤ k') (ω : GridΩA D N K) :
    GridA_mask D N K k (GridA_mask D N K k' ω) = GridA_mask D N K k ω := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp [GridA_mask, hj, lt_of_lt_of_le hj hkk']
  · simp [GridA_mask, hj]

/-- `H_k` is a measurable function of the generating map of `𝓕_k`. -/
private theorem GridA_state_factor (D N K : ℕ) (h : ℝ) (k : ℕ) :
    ∃ g : GridΩA D N K → Idx D N → Idx D N → ℂ, Measurable g ∧
      ∀ ω, gridStateA D N K h ω k = g (GridA_mask D N K k ω) := by
  induction k with
  | zero => exact ⟨Prod.fst, measurable_fst, fun ω => rfl⟩
  | succ k ih =>
    obtain ⟨g, hg, hgk⟩ := ih
    by_cases hk : k < K
    · refine ⟨fun p => Real.exp (-h / 2) • g (GridA_mask D N K k p) +
        Real.sqrt (1 - Real.exp (-h)) • GridA_arr D N (p.2 ⟨k, hk⟩), ?_, fun ω => ?_⟩
      · exact (GridA_meas_smul _ (hg.comp (GridA_mask_measurable D N K k))).add
          (GridA_meas_smul _ ((GridA_arr_measurable D N).comp
            ((measurable_pi_apply (⟨k, hk⟩ : Fin K)).comp measurable_snd)))
      · beta_reduce
        rw [GridA_mask_mask (Nat.le_succ k)]
        simp [gridStateA, hk, hgk, GridA_mask, GridA_arr]
    · refine ⟨fun p => Real.exp (-h / 2) • g (GridA_mask D N K k p), ?_, fun ω => ?_⟩
      · exact GridA_meas_smul _ (hg.comp (GridA_mask_measurable D N K k))
      · beta_reduce
        rw [GridA_mask_mask (Nat.le_succ k)]
        simp [gridStateA, hk, hgk]

/-- `H_k` is measurable for the product σ-algebra. -/
private theorem GridA_state_measurable (D N K : ℕ) (h : ℝ) (k : ℕ) :
    Measurable fun ω : GridΩA D N K => gridStateA D N K h ω k := by
  obtain ⟨g, hg, hgk⟩ := GridA_state_factor D N K h k
  have : (fun ω : GridΩA D N K => gridStateA D N K h ω k) = g ∘ GridA_mask D N K k := funext hgk
  rw [this]
  exact hg.comp (GridA_mask_measurable D N K k)

/-- One step of the grid: for `k < K`, `H_{k+1} = e^{-h/2} H_k + √(1 - e^{-h}) A(X_{k+1})`. -/
private theorem GridA_state_succ (D N K : ℕ) (h : ℝ) (k : ℕ) (hk : k < K) (ω : GridΩA D N K) :
    gridStateA D N K h ω (k + 1) = Real.exp (-h / 2) • gridStateA D N K h ω k +
      Real.sqrt (1 - Real.exp (-h)) • GridA_arr D N (ω.2 ⟨k, hk⟩) := by
  simp [gridStateA, hk, GridA_arr]

/-- Coordinates of a product measure that are functions of disjoint sets of factors are
independent. -/
private theorem GridA_pi_indep (K : ℕ) {E : Type*} [MeasurableSpace E] [Zero E] (ν : Measure E)
    [IsProbabilityMeasure ν] (k : ℕ) (hk : k < K) :
    IndepFun (fun x : Fin K → E => fun j : Fin K => if (j : ℕ) < k then x j else 0)
      (fun x : Fin K → E => x ⟨k, hk⟩) (Measure.pi fun _ : Fin K => ν) := by
  have hind : iIndepFun (fun (j : Fin K) (x : Fin K → E) => x j) (Measure.pi fun _ : Fin K => ν) :=
    iIndepFun_pi (X := fun _ => (id : E → E)) (fun _ => aemeasurable_id)
  set S : Finset (Fin K) := Finset.univ.filter fun j => (j : ℕ) < k with hS
  set T : Finset (Fin K) := {⟨k, hk⟩} with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro j hj hjT
    simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hj hjT
    subst hjT
    exact lt_irrefl _ hj
  have h1 := hind.indepFun_finset S T hST fun j => measurable_pi_apply j
  have hφ1 : Measurable fun y : S → E => fun j : Fin K => if h : j ∈ S then y ⟨j, h⟩ else 0 := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [hj, ↓reduceDIte]
      exact measurable_const
  have hφ2 : Measurable fun y : T → E => y ⟨⟨k, hk⟩, Finset.mem_singleton_self _⟩ :=
    measurable_pi_apply _
  have h2 := h1.comp hφ1 hφ2
  have e1 : (fun x : Fin K → E => fun j : Fin K => if (j : ℕ) < k then x j else 0) =
      (fun y : S → E => fun j : Fin K => if h : j ∈ S then y ⟨j, h⟩ else 0) ∘
        fun (a : Fin K → E) (i : S) => a i := by
    funext x j
    by_cases hj : (j : ℕ) < k
    · simp [hj, hS]
    · simp [hj, hS]
  have e2 : (fun x : Fin K → E => x ⟨k, hk⟩) =
      (fun y : T → E => y ⟨⟨k, hk⟩, Finset.mem_singleton_self _⟩) ∘
        fun (a : Fin K → E) (i : T) => a i := rfl
  rw [e1, e2]
  exact h2

/-- If `U` and `V` are independent under `ν`, then `(a, b) ↦ (a, U b)` and `(a, b) ↦ V b` are
independent under `P ⊗ ν`. -/
private theorem GridA_prod_indepFun {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (P : Measure α) (ν : Measure β)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] {U : β → γ} {V : β → δ}
    (hU : Measurable U) (hV : Measurable V) (h : IndepFun U V ν) :
    IndepFun (fun p : α × β => (p.1, U p.2)) (fun p : α × β => V p.2) (P.prod ν) := by
  have hg : Measurable fun b => (U b, V b) := hU.prodMk hV
  have hUV : ν.map (fun b => (U b, V b)) = (ν.map U).prod (ν.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  have m1 : (P.prod ν).map (fun p : α × β => (p.1, U p.2)) = P.prod (ν.map U) := by
    have := Measure.map_prod_map P ν (f := id) (g := U) measurable_id hU
    rw [Measure.map_id] at this
    exact this.symm
  have m2 : (P.prod ν).map (fun p : α × β => V p.2) = ν.map V := by
    have : (fun p : α × β => V p.2) = V ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map hV measurable_snd, Measure.map_snd_prod]
    simp
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), m1, m2]
  have m3 : (P.prod ν).map (fun p : α × β => ((p.1, U p.2), V p.2)) =
      (P.prod (ν.map fun b => (U b, V b))).map MeasurableEquiv.prodAssoc.symm := by
    have := Measure.map_prod_map P ν (f := id) (g := fun b => (U b, V b)) measurable_id hg
    rw [Measure.map_id] at this
    rw [this, Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hg)]
    rfl
  rw [m3, hUV]
  exact (MeasurePreserving.symm _ (measurePreserving_prodAssoc P (ν.map U) (ν.map V))).map_eq

/-- The generating map of `𝓕_k` is independent of the increment `X_{k+1}`, for every law `P`
of the initial array. -/
private theorem GridA_prior_indepFun (D N K : ℕ) (P : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure P] (k : ℕ) (hk : k < K) :
    IndepFun (GridA_mask D N K k) (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩)
      (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)) := by
  have hU : Measurable fun x : Fin K → Fin D → Coords N =>
      fun j : Fin K => if (j : ℕ) < k then x j else 0 := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : (j : ℕ) < k
    · simp only [hj, ↓reduceIte]
      exact measurable_pi_apply _
    · simp only [hj, ↓reduceIte]
      exact measurable_const
  exact GridA_prod_indepFun P (Measure.pi fun _ : Fin K => gueBlocks D N) hU
    (measurable_pi_apply _) (GridA_pi_indep K (gueBlocks D N) k hk)

/-- The increment `X_{k+1}` has the law `gueBlocks D N`. -/
private theorem GridA_prior_map_incr (D N K : ℕ) (P : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure P] (k : ℕ) (hk : k < K) :
    (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)).map
      (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) = gueBlocks D N := by
  have : (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) =
      (fun x : Fin K → Fin D → Coords N => x ⟨k, hk⟩) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact (measurePreserving_eval (fun _ : Fin K => gueBlocks D N) ⟨k, hk⟩).map_eq

/-- If `g` maps `μ ⊗ μ` to `μ`, then the coordinatewise `g` maps `(⊗ᵢ μ) ⊗ (⊗ᵢ μ)` to `⊗ᵢ μ`. -/
private theorem GridA_pi_pair_map {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E × E → E) (hg : Measurable g)
    (h : (μ.prod μ).map g = μ) :
    ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)).map
      (fun p i => g (p.1 i, p.2 i)) = Measure.pi fun _ : ι => μ := by
  have hmp := measurePreserving_arrowProdEquivProdArrow E E ι (fun _ => μ) (fun _ => μ)
  have e := (MeasurePreserving.symm _ hmp).map_eq
  have hf : (fun p : (ι → E) × (ι → E) => fun i => g (p.1 i, p.2 i)) =
      (fun x : ι → E × E => fun i => g (x i)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow E E ι).symm := by
    funext p i; rfl
  rw [hf, ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), e,
    Measure.pi_map_pi (fun _ => hg.aemeasurable)]
  simp [h]

/-- Invariance of the `D` GUE blocks: `a X + b Y` is distributed as `gueBlocks D N` for independent
`X`, `Y` of that law and `a² + b² = 1`. -/
private theorem GridA_blocks_map_add (D N : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gueBlocks D N).prod (gueBlocks D N)).map (fun p => a • p.1 + b • p.2) = gueBlocks D N := by
  unfold gueBlocks
  exact GridA_pi_pair_map (ι := Fin D) (gueLaw N) (fun q : Coords N × Coords N => a • q.1 + b • q.2)
    ((measurable_fst.const_smul a).add (measurable_snd.const_smul b)) (gueLaw_map_add N a b hab)

/-- For `c² + d² = s²` with `s ≥ 0`, `c X + d Y` has the law of `s X` for independent GUE blocks. -/
private theorem GridA_blocks_map_comb (D N : ℕ) (c d s : ℝ) (hs : 0 ≤ s)
    (h : c ^ 2 + d ^ 2 = s ^ 2) :
    ((gueBlocks D N).prod (gueBlocks D N)).map (fun p => c • p.1 + d • p.2) =
      (gueBlocks D N).map (fun w => s • w) := by
  rcases hs.eq_or_lt with hs0 | hspos
  · subst hs0
    have hc : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    subst hc hd
    simp [Measure.map_const]
  · have hab : (c / s) ^ 2 + (d / s) ^ 2 = 1 := by
      field_simp
      linarith
    have key := GridA_blocks_map_add D N (c / s) (d / s) hab
    have e : (fun p : (Fin D → Coords N) × (Fin D → Coords N) => c • p.1 + d • p.2) =
        (fun w : Fin D → Coords N => s • w) ∘
          (fun p : (Fin D → Coords N) × (Fin D → Coords N) => (c / s) • p.1 + (d / s) • p.2) := by
      funext p
      simp only [Function.comp, smul_add, smul_smul]
      rw [mul_div_cancel₀ _ hspos.ne', mul_div_cancel₀ _ hspos.ne']
    have hsm : Measurable fun w : Fin D → Coords N => s • w := GridA_meas_smulB s measurable_id
    rw [e, ← Measure.map_map hsm (GridA_measB_comb (c / s) (d / s)), key]

/-- The grid filtration with a full initial array is increasing and below the product
σ-algebra. -/
theorem gridFiltrA_mono (D N K : ℕ) : Monotone (gridFiltrA D N K) ∧
    ∀ k, gridFiltrA D N K k ≤ (inferInstance : MeasurableSpace (GridΩA D N K)) := by
  refine ⟨fun k k' hkk' => ?_, fun k => (GridA_mask_measurable D N K k).comap_le⟩
  have h1 : GridA_mask D N K k = (fun p : GridΩA D N K => (p.1, fun j : Fin K =>
      if (j : ℕ) < k then p.2 j else 0)) ∘ GridA_mask D N K k' := by
    funext ω
    simp only [GridA_mask, Function.comp]
    refine Prod.ext rfl (funext fun j => ?_)
    by_cases hj : (j : ℕ) < k
    · simp [hj, lt_of_lt_of_le hj hkk']
    · simp [hj]
  have h2 : gridFiltrA D N K k = MeasurableSpace.comap (GridA_mask D N K k')
      (MeasurableSpace.comap (fun p : GridΩA D N K => (p.1, fun j : Fin K =>
        if (j : ℕ) < k then p.2 j else 0)) inferInstance) := by
    rw [MeasurableSpace.comap_comp, ← h1]
    rfl
  rw [h2]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

/-- The grid filtration with a full initial array, as a Mathlib `Filtration`. -/
def gridFiltrationA (D N K : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (GridΩA D N K)) :=
  ⟨gridFiltrA D N K, (gridFiltrA_mono D N K).1, (gridFiltrA_mono D N K).2⟩

/-- The one-step recursion for the joint law of `(H₀, H_k)`: if `(H₀, H_k)` has the law of
`(a, c₁ a + s₁ A(w))` with `(a, w) ∼ P ⊗ GUE`, and `X` is an independent GUE block, then
`(H₀, r H_k + σ A(X))` has the law of `(a, c₂ a + s₂ A(w))`, when `r c₁ = c₂` and
`r² s₁² + σ² = s₂²`. -/
private theorem GridA_step_law (D N : ℕ) (P : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure P] (c₁ s₁ c₂ s₂ r σ : ℝ) (hs₂ : 0 ≤ s₂) (hc : r * c₁ = c₂)
    (hs : r ^ 2 * s₁ ^ 2 + σ ^ 2 = s₂ ^ 2) :
    (((P.prod (gueBlocks D N)).map fun p => (p.1, c₁ • p.1 + s₁ • GridA_arr D N p.2)).prod
        (gueBlocks D N)).map (fun q => (q.1.1, r • q.1.2 + σ • GridA_arr D N q.2)) =
      (P.prod (gueBlocks D N)).map fun p => (p.1, c₂ • p.1 + s₂ • GridA_arr D N p.2) := by
  set ν := gueBlocks D N with hν
  have hF : ∀ c s : ℝ, Measurable fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      (p.1, c • p.1 + s • GridA_arr D N p.2) := fun c s =>
    measurable_fst.prodMk (GridA_meas_comb c s)
  have hΨ : Measurable fun q : ((Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) ×
      (Fin D → Coords N) => (q.1.1, r • q.1.2 + σ • GridA_arr D N q.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((GridA_meas_smul r (measurable_snd.comp measurable_fst)).add
        (GridA_meas_smul σ ((GridA_arr_measurable D N).comp measurable_snd)))
  have hsm : Measurable fun w : Fin D → Coords N => s₂ • w := GridA_meas_smulB s₂ measurable_id
  have hcomb : Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      (r * s₁) • p.1 + σ • p.2 := GridA_measB_comb _ _
  have hΘ : Measurable fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      (p.1, c₂ • p.1 + GridA_arr D N p.2) :=
    measurable_fst.prodMk ((GridA_meas_smul c₂ measurable_fst).add
      ((GridA_arr_measurable D N).comp measurable_snd))
  -- left side
  have l1 : ((P.prod ν).map fun p => (p.1, c₁ • p.1 + s₁ • GridA_arr D N p.2)).prod ν =
      ((P.prod ν).prod ν).map
        (Prod.map (fun p => (p.1, c₁ • p.1 + s₁ • GridA_arr D N p.2)) id) := by
    have := Measure.map_prod_map (P.prod ν) ν
      (f := fun p => (p.1, c₁ • p.1 + s₁ • GridA_arr D N p.2))
      (g := id) (hF c₁ s₁) measurable_id
    rwa [Measure.map_id] at this
  rw [l1, Measure.map_map hΨ ((hF c₁ s₁).prodMap measurable_id)]
  -- right side
  have r1 : ν.map (fun w => s₂ • w) = (ν.prod ν).map fun p => (r * s₁) • p.1 + σ • p.2 := by
    refine (GridA_blocks_map_comb D N (r * s₁) σ s₂ hs₂ ?_).symm
    nlinarith [hs]
  have r2 : P.prod (ν.map fun w => s₂ • w) = (P.prod ν).map (Prod.map id fun w => s₂ • w) := by
    have := Measure.map_prod_map P ν (f := id) (g := fun w => s₂ • w) measurable_id hsm
    rwa [Measure.map_id] at this
  have r3 : P.prod ((ν.prod ν).map fun p => (r * s₁) • p.1 + σ • p.2) =
      (P.prod (ν.prod ν)).map (Prod.map id fun p => (r * s₁) • p.1 + σ • p.2) := by
    have := Measure.map_prod_map P (ν.prod ν) (f := id)
      (g := fun p => (r * s₁) • p.1 + σ • p.2) measurable_id hcomb
    rwa [Measure.map_id] at this
  have r4 : (P.prod ν).map (fun p => (p.1, c₂ • p.1 + s₂ • GridA_arr D N p.2)) =
      ((P.prod ν).map (Prod.map id fun w => s₂ • w)).map
        fun p => (p.1, c₂ • p.1 + GridA_arr D N p.2) := by
    rw [Measure.map_map hΘ (measurable_id.prodMap hsm)]
    congr 1
    funext p
    simp [GridA_arr_smul]
  rw [r4, ← r2, r1, r3, ← (measurePreserving_prodAssoc P ν ν).map_eq,
    Measure.map_map (measurable_id.prodMap hcomb) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map hΘ ((measurable_id.prodMap hcomb).comp MeasurableEquiv.prodAssoc.measurable)]
  congr 1
  funext q
  obtain ⟨⟨a, w⟩, x⟩ := q
  simp only [Function.comp, Prod.map, id, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_apply, GridA_arr_add, GridA_arr_smul, smul_add, smul_smul, hc]
  rw [add_assoc]

/-- The joint law of `(H₀, H_k)` for an arbitrary law `P` of the initial array:
`(a, e^{-kh/2} a + √(1 - e^{-kh}) A(w))` with `(a, w) ∼ P ⊗ GUE`, `0 ≤ h`, `k ≤ K`. -/
private theorem GridA_law_joint (D N K : ℕ) (P : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (hk : k ≤ K) :
    (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)).map
        (fun ω => (ω.1, gridStateA D N K h ω k)) =
      (P.prod (gueBlocks D N)).map fun p => (p.1, Real.exp (-(k * h) / 2) • p.1 +
        Real.sqrt (1 - Real.exp (-(k * h))) • GridA_arr D N p.2) := by
  induction k with
  | zero =>
    simp only [gridStateA, Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero, one_smul,
      sub_self, Real.sqrt_zero, zero_smul, add_zero]
    have e1 : (fun ω : GridΩA D N K => (ω.1, ω.1)) =
        (fun a : Idx D N → Idx D N → ℂ => (a, a)) ∘ Prod.fst := rfl
    have e2 : (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) => (p.1, p.1)) =
        (fun a : Idx D N → Idx D N → ℂ => (a, a)) ∘ Prod.fst := rfl
    rw [e1, e2, ← Measure.map_map (by fun_prop) measurable_fst,
      ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, Measure.map_fst_prod]
    simp
  | succ k ih =>
    have hk' : k < K := hk
    have ih := ih hk'.le
    set μ := P.prod (Measure.pi fun _ : Fin K => gueBlocks D N) with hμ
    obtain ⟨g, hg, hgk⟩ := GridA_state_factor D N K h k
    have hind : IndepFun (fun ω : GridΩA D N K => (ω.1, gridStateA D N K h ω k))
        (fun ω : GridΩA D N K => ω.2 ⟨k, hk'⟩) μ := by
      have := (GridA_prior_indepFun D N K P k hk').comp
        (φ := fun p : GridΩA D N K => (p.1, g p)) (ψ := id)
        (measurable_fst.prodMk hg) measurable_id
      convert this using 2 <;> simp [hgk, GridA_mask]
    have hH := GridA_state_measurable D N K h k
    have hV : Measurable fun ω : GridΩA D N K => ω.2 ⟨k, hk'⟩ :=
      (measurable_pi_apply _).comp measurable_snd
    have hmV := GridA_prior_map_incr D N K P k hk'
    have hpair := (indepFun_iff_map_prod_eq_prod_map_map (measurable_fst.prodMk hH).aemeasurable
      hV.aemeasurable).1 hind
    rw [hmV, ih] at hpair
    have hfun : (fun ω : GridΩA D N K => (ω.1, gridStateA D N K h ω (k + 1))) =
        (fun q : ((Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) × (Fin D → Coords N) =>
          (q.1.1, Real.exp (-h / 2) • q.1.2 +
            Real.sqrt (1 - Real.exp (-h)) • GridA_arr D N q.2)) ∘
        fun ω : GridΩA D N K => ((ω.1, gridStateA D N K h ω k), ω.2 ⟨k, hk'⟩) := by
      funext ω
      simp [GridA_state_succ D N K h k hk' ω]
    have hΨ : Measurable fun q : ((Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) ×
        (Fin D → Coords N) => (q.1.1, Real.exp (-h / 2) • q.1.2 +
          Real.sqrt (1 - Real.exp (-h)) • GridA_arr D N q.2) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((GridA_meas_smul _ (measurable_snd.comp measurable_fst)).add
          (GridA_meas_smul _ ((GridA_arr_measurable D N).comp measurable_snd)))
    rw [hfun, ← Measure.map_map hΨ ((measurable_fst.prodMk hH).prodMk hV), hpair]
    have hkh : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
    have hu : Real.exp (-(k * h)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hu' : Real.exp (-((k + 1 : ℕ) * h)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by push_cast; nlinarith)
    refine GridA_step_law D N P _ _ _ _ _ _ (Real.sqrt_nonneg _) ?_ ?_
    · rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    · have hσ : 0 ≤ 1 - Real.exp (-h) := by
        linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 hh)]
      rw [Real.sq_sqrt hσ, Real.sq_sqrt (sub_nonneg.2 hu), Real.sq_sqrt (sub_nonneg.2 hu'), sq,
        ← Real.exp_add]
      have e1 : Real.exp (-h / 2 + -h / 2) = Real.exp (-h) := by congr 1; ring
      have e2 : Real.exp (-h) * Real.exp (-(k * h)) = Real.exp (-((k + 1 : ℕ) * h)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [e1]
      nlinarith [e2]

/-- At grid times the state has the block-OU law (3.13) [eq:Gauss_div] of its initial law. -/
theorem gridStateA_law (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (hk : k ≤ K) :
    (gridLawA D N K μ₀).map (fun ω => gridStateA D N K h ω k) = blockOULaw D N μ₀ (k * h) := by
  have hj := GridA_law_joint D N K μ₀ h hh k hk
  have hF : Measurable fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) • GridA_arr D N p.2 :=
    GridA_meas_comb _ _
  have e1 : (fun ω : GridΩA D N K => gridStateA D N K h ω k) =
      Prod.snd ∘ fun ω : GridΩA D N K => (ω.1, gridStateA D N K h ω k) := rfl
  have e2 : (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) • GridA_arr D N p.2) =
      Prod.snd ∘ fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) => (p.1,
        Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) •
          GridA_arr D N p.2) := rfl
  unfold gridLawA blockOULaw
  rw [e2, ← Measure.map_map measurable_snd (measurable_fst.prodMk hF), ← hj,
    Measure.map_map measurable_snd
      ((measurable_fst).prodMk (GridA_state_measurable D N K h k)), ← e1]

end RBMTransitionEdge

end
