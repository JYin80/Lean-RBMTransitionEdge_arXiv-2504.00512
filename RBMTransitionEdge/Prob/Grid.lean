module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Prob.Gaussian

@[expose] public section

/-!
# The discrete grid of the OU flow

The probability space of `K` independent GUE increments, the grid state `H_k` of the OU flow
(3.12) [eq:Ht] at times `kh`, and the law (3.13) [eq:Gauss_div] of the grid state.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The sample space of the grid: the initial blocks and `K` block-GUE increments. -/
abbrev GridΩ (D N K : ℕ) := (Fin D → Coords N) × (Fin K → Fin D → Coords N)

/-- The law of the grid: `blockLaw ⊗ (⊗_{k<K} gueBlocks)`. -/
def gridLaw (D N K : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) : Measure (GridΩ D N K) :=
  (blockLaw D N L).prod (Measure.pi fun _ : Fin K => gueBlocks D N)

/-- The exact Ornstein–Uhlenbeck step of mesh `h`: `H_{k+1} = e^{-h/2} H_k + √(1 - e^{-h}) X_{k+1}`
(and `X_{k+1} = 0` beyond `K`). -/
def gridState (D N K : ℕ) (h : ℝ) (ω : GridΩ D N K) : ℕ → Fin D → Coords N
  | 0 => ω.1
  | k + 1 => Real.exp (-h / 2) • gridState D N K h ω k +
      Real.sqrt (1 - Real.exp (-h)) • (if hk : k < K then ω.2 ⟨k, hk⟩ else 0)

/-- Scalar multiples of a measurable block-valued map are measurable. -/
private theorem gridMeas_smul {α : Type*} [MeasurableSpace α] {D N : ℕ} (c : ℝ)
    {f : α → Fin D → Coords N} (hf : Measurable f) : Measurable fun x => c • f x :=
  measurable_pi_iff.2 fun a => ((measurable_pi_apply a).comp hf).const_smul c

/-- The generating map of the σ-algebra at step `k`: the initial blocks and the increments `X_{j+1}`,
`j < k`, with the others set to `0`. -/
private def gridMask (D N K k : ℕ) (ω : GridΩ D N K) : GridΩ D N K :=
  (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0)

private theorem gridMask_measurable (D N K k : ℕ) : Measurable (gridMask D N K k) := by
  unfold gridMask
  refine measurable_fst.prodMk (measurable_pi_iff.mpr fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simp [hj]

private theorem gridMask_mask {D N K k k' : ℕ} (hkk' : k ≤ k') (ω : GridΩ D N K) :
    gridMask D N K k (gridMask D N K k' ω) = gridMask D N K k ω := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp [gridMask, hj, lt_of_lt_of_le hj hkk']
  · simp [gridMask, hj]

/-- `H_k` is a measurable function of the generating map of `𝓕_k`. -/
private theorem gridState_factor (D N K : ℕ) (h : ℝ) (k : ℕ) :
    ∃ g : GridΩ D N K → Fin D → Coords N, Measurable g ∧
      ∀ ω, gridState D N K h ω k = g (gridMask D N K k ω) := by
  induction k with
  | zero => exact ⟨Prod.fst, measurable_fst, fun ω => rfl⟩
  | succ k ih =>
    obtain ⟨g, hg, hgk⟩ := ih
    by_cases hk : k < K
    · refine ⟨fun p => Real.exp (-h / 2) • g (gridMask D N K k p) +
        Real.sqrt (1 - Real.exp (-h)) • p.2 ⟨k, hk⟩, ?_, fun ω => ?_⟩
      · exact (gridMeas_smul _ (hg.comp (gridMask_measurable D N K k))).add
          (gridMeas_smul _ ((measurable_pi_apply (⟨k, hk⟩ : Fin K)).comp measurable_snd))
      · beta_reduce
        rw [gridMask_mask (Nat.le_succ k)]
        simp [gridState, hk, hgk, gridMask]
    · refine ⟨fun p => Real.exp (-h / 2) • g (gridMask D N K k p), ?_, fun ω => ?_⟩
      · exact gridMeas_smul _ (hg.comp (gridMask_measurable D N K k))
      · beta_reduce
        rw [gridMask_mask (Nat.le_succ k)]
        simp [gridState, hk, hgk]

/-- The product of the `K` increment laws is s-finite. -/
instance gridPi_instSFinite (D N K : ℕ) :
    SFinite (Measure.pi fun _ : Fin K => gueBlocks D N) := by
  have : IsFiniteMeasure (Measure.pi fun _ : Fin K => gueBlocks D N) := inferInstance
  infer_instance

/-- Coordinates of a product measure that are functions of disjoint sets of factors are
independent. -/
private theorem gridPi_indep (K : ℕ) {E : Type*} [MeasurableSpace E] [Zero E] (ν : Measure E)
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
private theorem gridProd_indepFun {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
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
of the initial blocks. -/
private theorem gridPrior_indepFun (D N K : ℕ) (P : Measure (Fin D → Coords N))
    [IsProbabilityMeasure P] (k : ℕ) (hk : k < K) :
    IndepFun (gridMask D N K k) (fun ω : GridΩ D N K => ω.2 ⟨k, hk⟩)
      (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)) := by
  have hU : Measurable fun x : Fin K → Fin D → Coords N =>
      fun j : Fin K => if (j : ℕ) < k then x j else 0 := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : (j : ℕ) < k
    · simp only [hj, ↓reduceIte]
      exact measurable_pi_apply _
    · simp only [hj, ↓reduceIte]
      exact measurable_const
  exact gridProd_indepFun P (Measure.pi fun _ : Fin K => gueBlocks D N) hU
    (measurable_pi_apply _) (gridPi_indep K (gueBlocks D N) k hk)

/-- If `g` maps `μ ⊗ μ` to `μ`, then the coordinatewise `g` maps `(⊗ᵢ μ) ⊗ (⊗ᵢ μ)` to `⊗ᵢ μ`. -/
private theorem gridPi_pair_map {ι E : Type*} [Fintype ι] [MeasurableSpace E]
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

/-- Measurability of a linear combination of two block-valued maps. -/
private theorem gridMeas_comb {D N : ℕ} (a b : ℝ) :
    Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) => a • p.1 + b • p.2 :=
  (gridMeas_smul a measurable_fst).add (gridMeas_smul b measurable_snd)

/-- Invariance of the `D` GUE blocks: `a X + b Y` is distributed as `gueBlocks D N` for independent
`X`, `Y` of that law and `a² + b² = 1`. -/
private theorem gridBlocks_map_add (D N : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gueBlocks D N).prod (gueBlocks D N)).map (fun p => a • p.1 + b • p.2) = gueBlocks D N := by
  unfold gueBlocks
  exact gridPi_pair_map (ι := Fin D) (gueLaw N) (fun q : Coords N × Coords N => a • q.1 + b • q.2)
    ((measurable_fst.const_smul a).add (measurable_snd.const_smul b)) (gueLaw_map_add N a b hab)

/-- For `c² + d² = s²` with `s ≥ 0`, `c X + d Y` has the law of `s X` for independent GUE blocks. -/
private theorem gridBlocks_map_comb (D N : ℕ) (c d s : ℝ) (hs : 0 ≤ s) (h : c ^ 2 + d ^ 2 = s ^ 2) :
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
    have key := gridBlocks_map_add D N (c / s) (d / s) hab
    have e : (fun p : (Fin D → Coords N) × (Fin D → Coords N) => c • p.1 + d • p.2) =
        (fun w : Fin D → Coords N => s • w) ∘
          (fun p : (Fin D → Coords N) × (Fin D → Coords N) => (c / s) • p.1 + (d / s) • p.2) := by
      funext p
      simp only [Function.comp, smul_add, smul_smul]
      rw [mul_div_cancel₀ _ hspos.ne', mul_div_cancel₀ _ hspos.ne']
    have hsm : Measurable fun w : Fin D → Coords N => s • w := gridMeas_smul s measurable_id
    rw [e, ← Measure.map_map hsm (gridMeas_comb (c / s) (d / s)), key]

/-- The one-step recursion for the joint law of `(H₀, H_k)`: if `(H₀, H_k)` has the law of
`(a, c₁ a + s₁ w)` with `(a, w) ∼ P ⊗ GUE`, and `X` is an independent GUE block, then
`(H₀, r H_k + σ X)` has the law of `(a, c₂ a + s₂ w)`, when `r c₁ = c₂` and `r² s₁² + σ² = s₂²`. -/
private theorem gridStep_law (D N : ℕ) (P : Measure (Fin D → Coords N)) [IsProbabilityMeasure P]
    (c₁ s₁ c₂ s₂ r σ : ℝ) (hs₂ : 0 ≤ s₂) (hc : r * c₁ = c₂)
    (hs : r ^ 2 * s₁ ^ 2 + σ ^ 2 = s₂ ^ 2) :
    (((P.prod (gueBlocks D N)).map fun p => (p.1, c₁ • p.1 + s₁ • p.2)).prod
        (gueBlocks D N)).map (fun q => (q.1.1, r • q.1.2 + σ • q.2)) =
      (P.prod (gueBlocks D N)).map fun p => (p.1, c₂ • p.1 + s₂ • p.2) := by
  set ν := gueBlocks D N with hν
  have hF : ∀ c s : ℝ, Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      (p.1, c • p.1 + s • p.2) := fun c s => measurable_fst.prodMk (gridMeas_comb c s)
  have hΨ : Measurable fun q : ((Fin D → Coords N) × (Fin D → Coords N)) × (Fin D → Coords N) =>
      (q.1.1, r • q.1.2 + σ • q.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((gridMeas_smul r (measurable_snd.comp measurable_fst)).add
        (gridMeas_smul σ measurable_snd))
  have hsm : Measurable fun w : Fin D → Coords N => s₂ • w := gridMeas_smul s₂ measurable_id
  have hcomb : Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      (r * s₁) • p.1 + σ • p.2 := gridMeas_comb _ _
  have hΘ : Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      (p.1, c₂ • p.1 + p.2) :=
    measurable_fst.prodMk ((gridMeas_smul c₂ measurable_fst).add measurable_snd)
  -- left side
  have l1 : ((P.prod ν).map fun p => (p.1, c₁ • p.1 + s₁ • p.2)).prod ν =
      ((P.prod ν).prod ν).map (Prod.map (fun p => (p.1, c₁ • p.1 + s₁ • p.2)) id) := by
    have := Measure.map_prod_map (P.prod ν) ν (f := fun p => (p.1, c₁ • p.1 + s₁ • p.2))
      (g := id) (hF c₁ s₁) measurable_id
    rwa [Measure.map_id] at this
  rw [l1, Measure.map_map hΨ ((hF c₁ s₁).prodMap measurable_id)]
  -- right side
  have r1 : ν.map (fun w => s₂ • w) = (ν.prod ν).map fun p => (r * s₁) • p.1 + σ • p.2 := by
    refine (gridBlocks_map_comb D N (r * s₁) σ s₂ hs₂ ?_).symm
    nlinarith [hs]
  have r2 : P.prod (ν.map fun w => s₂ • w) = (P.prod ν).map (Prod.map id fun w => s₂ • w) := by
    have := Measure.map_prod_map P ν (f := id) (g := fun w => s₂ • w) measurable_id hsm
    rwa [Measure.map_id] at this
  have r3 : P.prod ((ν.prod ν).map fun p => (r * s₁) • p.1 + σ • p.2) =
      (P.prod (ν.prod ν)).map (Prod.map id fun p => (r * s₁) • p.1 + σ • p.2) := by
    have := Measure.map_prod_map P (ν.prod ν) (f := id)
      (g := fun p => (r * s₁) • p.1 + σ • p.2) measurable_id hcomb
    rwa [Measure.map_id] at this
  have r4 : (P.prod ν).map (fun p => (p.1, c₂ • p.1 + s₂ • p.2)) =
      ((P.prod ν).map (Prod.map id fun w => s₂ • w)).map fun p => (p.1, c₂ • p.1 + p.2) := by
    rw [Measure.map_map hΘ (measurable_id.prodMap hsm)]
    rfl
  rw [r4, ← r2, r1, r3, ← (measurePreserving_prodAssoc P ν ν).map_eq,
    Measure.map_map (measurable_id.prodMap hcomb) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map hΘ ((measurable_id.prodMap hcomb).comp MeasurableEquiv.prodAssoc.measurable)]
  congr 1
  funext q
  obtain ⟨⟨a, w⟩, x⟩ := q
  simp only [Function.comp, Prod.map, id, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_apply, smul_add, smul_smul, hc]
  rw [add_assoc]

/-- `H_k` is measurable for the product σ-algebra. -/
private theorem gridState_measurable (D N K : ℕ) (h : ℝ) (k : ℕ) :
    Measurable fun ω : GridΩ D N K => gridState D N K h ω k := by
  obtain ⟨g, hg, hgk⟩ := gridState_factor D N K h k
  have : (fun ω : GridΩ D N K => gridState D N K h ω k) = g ∘ gridMask D N K k := funext hgk
  rw [this]
  exact hg.comp (gridMask_measurable D N K k)

/-- One step of the grid: for `k < K`, `H_{k+1} = e^{-h/2} H_k + √(1 - e^{-h}) X_{k+1}`. -/
private theorem gridState_succ (D N K : ℕ) (h : ℝ) (k : ℕ) (hk : k < K) (ω : GridΩ D N K) :
    gridState D N K h ω (k + 1) = Real.exp (-h / 2) • gridState D N K h ω k +
      Real.sqrt (1 - Real.exp (-h)) • ω.2 ⟨k, hk⟩ := by
  simp [gridState, hk]

/-- The increment `X_{k+1}` has the law `gueBlocks D N`. -/
private theorem gridPrior_map_incr (D N K : ℕ) (P : Measure (Fin D → Coords N))
    [IsProbabilityMeasure P] (k : ℕ) (hk : k < K) :
    (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)).map
      (fun ω : GridΩ D N K => ω.2 ⟨k, hk⟩) = gueBlocks D N := by
  have : (fun ω : GridΩ D N K => ω.2 ⟨k, hk⟩) =
      (fun x : Fin K → Fin D → Coords N => x ⟨k, hk⟩) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact (measurePreserving_eval (fun _ : Fin K => gueBlocks D N) ⟨k, hk⟩).map_eq

/-- The joint law of `(H₀, H_k)` for an arbitrary law `P` of the initial blocks:
`(a, e^{-kh/2} a + √(1 - e^{-kh}) w)` with `(a, w) ∼ P ⊗ GUE`, `0 ≤ h`, `k ≤ K`. -/
private theorem gridLaw_joint (D N K : ℕ) (P : Measure (Fin D → Coords N))
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (hk : k ≤ K) :
    (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)).map
        (fun ω => (ω.1, gridState D N K h ω k)) =
      (P.prod (gueBlocks D N)).map fun p => (p.1, Real.exp (-(k * h) / 2) • p.1 +
        Real.sqrt (1 - Real.exp (-(k * h))) • p.2) := by
  induction k with
  | zero =>
    simp only [gridState, Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero, one_smul,
      sub_self, Real.sqrt_zero, zero_smul, add_zero]
    have e1 : (fun ω : GridΩ D N K => (ω.1, ω.1)) =
        (fun a : Fin D → Coords N => (a, a)) ∘ Prod.fst := rfl
    have e2 : (fun p : (Fin D → Coords N) × (Fin D → Coords N) => (p.1, p.1)) =
        (fun a : Fin D → Coords N => (a, a)) ∘ Prod.fst := rfl
    rw [e1, e2, ← Measure.map_map (by fun_prop) measurable_fst,
      ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, Measure.map_fst_prod]
    simp
  | succ k ih =>
    have hk' : k < K := hk
    have ih := ih hk'.le
    set μ := P.prod (Measure.pi fun _ : Fin K => gueBlocks D N) with hμ
    obtain ⟨g, hg, hgk⟩ := gridState_factor D N K h k
    have hind : IndepFun (fun ω : GridΩ D N K => (ω.1, gridState D N K h ω k))
        (fun ω : GridΩ D N K => ω.2 ⟨k, hk'⟩) μ := by
      have := (gridPrior_indepFun D N K P k hk').comp
        (φ := fun p : GridΩ D N K => (p.1, g p)) (ψ := id)
        (measurable_fst.prodMk hg) measurable_id
      convert this using 2 <;> simp [hgk, gridMask]
    have hH := gridState_measurable D N K h k
    have hV : Measurable fun ω : GridΩ D N K => ω.2 ⟨k, hk'⟩ :=
      (measurable_pi_apply _).comp measurable_snd
    have hmV := gridPrior_map_incr D N K P k hk'
    have hpair := (indepFun_iff_map_prod_eq_prod_map_map (measurable_fst.prodMk hH).aemeasurable
      hV.aemeasurable).1 hind
    rw [hmV, ih] at hpair
    have hfun : (fun ω : GridΩ D N K => (ω.1, gridState D N K h ω (k + 1))) =
        (fun q : ((Fin D → Coords N) × (Fin D → Coords N)) × (Fin D → Coords N) =>
          (q.1.1, Real.exp (-h / 2) • q.1.2 + Real.sqrt (1 - Real.exp (-h)) • q.2)) ∘
        fun ω : GridΩ D N K => ((ω.1, gridState D N K h ω k), ω.2 ⟨k, hk'⟩) := by
      funext ω
      simp [gridState_succ D N K h k hk' ω]
    have hΨ : Measurable fun q : ((Fin D → Coords N) × (Fin D → Coords N)) × (Fin D → Coords N) =>
        (q.1.1, Real.exp (-h / 2) • q.1.2 + Real.sqrt (1 - Real.exp (-h)) • q.2) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((gridMeas_smul _ (measurable_snd.comp measurable_fst)).add
          (gridMeas_smul _ measurable_snd))
    rw [hfun, ← Measure.map_map hΨ ((measurable_fst.prodMk hH).prodMk hV), hpair]
    have hkh : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
    have hu : Real.exp (-(k * h)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hu' : Real.exp (-((k + 1 : ℕ) * h)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by push_cast; nlinarith)
    refine gridStep_law D N P _ _ _ _ _ _ (Real.sqrt_nonneg _) ?_ ?_
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

/-- (3.13) [eq:Gauss_div] at grid times: `H_k` has the law of `e^{-kh/2} H₀ + √(1 - e^{-kh}) H^{(g)}`. -/
theorem gridState_law (D N K : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (h : ℝ) (hh : 0 ≤ h) (k : ℕ)
    (hk : k ≤ K) :
    (gridLaw D N K L).map (fun ω => gridState D N K h ω k) =
      ((blockLaw D N L).prod (gueBlocks D N)).map fun p =>
        Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) • p.2 := by
  have hj := gridLaw_joint D N K (blockLaw D N L) h hh k hk
  have hF : Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) • p.2 :=
    gridMeas_comb _ _
  have e1 : (fun ω : GridΩ D N K => gridState D N K h ω k) =
      Prod.snd ∘ fun ω : GridΩ D N K => (ω.1, gridState D N K h ω k) := rfl
  have e2 : (fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) • p.2) =
      Prod.snd ∘ fun p : (Fin D → Coords N) × (Fin D → Coords N) => (p.1,
        Real.exp (-(k * h) / 2) • p.1 + Real.sqrt (1 - Real.exp (-(k * h))) • p.2) := rfl
  rw [e2, ← Measure.map_map measurable_snd (measurable_fst.prodMk hF), ← hj,
    Measure.map_map measurable_snd ((measurable_fst).prodMk (gridState_measurable D N K h k)), ← e1]
  rfl

end RBMTransitionEdge

end
