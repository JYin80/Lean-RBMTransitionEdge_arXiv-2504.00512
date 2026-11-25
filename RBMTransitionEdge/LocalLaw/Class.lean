module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Tools.Resolvent

@[expose] public section

/-!
# The local-law model class, the spectral domain and the true inverses

The variance profile `S_θ` and the class `LLClass` of noises covered by Lemma 2.9 [lem_loc]; Assumption 1
[main_assm] is in the class; the domain `𝐃(τ)` of Definition 3.1 [def_wtM]; the control parameter of (2.22)
[eq:aniso_local]; the resolvent (2.12) [def_resolv] and `M` of Definition 2.7 [defn_Mm] as true inverses on both half
planes.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The variance profile `S_θ = θ S + (1 - θ)(DN)⁻¹ J`: `S` is the block profile (2.14) [eq:sij]
(`θ = 1`), and `θ = e^{-t}` gives the profile of the law (4.3) [eq:eq_in_law_H]. -/
def varProf (D N : ℕ) (θ : ℝ) (p q : Idx D N) : ℝ :=
  θ * (if p.1 = q.1 then ((N : ℝ))⁻¹ else 0) + (1 - θ) * (((D : ℝ) * N))⁻¹

/-- The class of noises `H′` of `X = H′ + Λ` covered by Lemma 2.9 [lem_loc]: a law on
`DN × DN` arrays, almost surely Hermitian, whose entries on and above the diagonal (in the
lexicographic order of `Idx D N`) are independent, with mean zero, `E|h_{ij}|² = (S_θ)_{ij}`,
`E h_{ij}² = 0` for `i ≠ j` as in (2.2) [eq:meanvar2], and `E|h_{ij}|^p ≤ C_p N^{-p/2}` as in
(2.3) [eq:highmoment]. The entries need not be identically distributed (last sentence of
Lemma 2.9 [lem_loc]). -/
structure LLClass (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)) :
    Prop where
  /-- `μ` is a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- The array is almost surely a Hermitian matrix (so its diagonal is real). -/
  herm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian
  /-- The entries `h_{ij}` with `i ≤ j` lexicographically are independent. -/
  indep : iIndepFun (fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2})
    (h : Idx D N → Idx D N → ℂ) => h q.1.1 q.1.2) μ
  /-- Every absolute moment of every entry is finite. -/
  integrable : ∀ (p : ℕ) (i j : Idx D N),
    Integrable (fun h : Idx D N → Idx D N → ℂ => ‖h i j‖ ^ p) μ
  /-- Mean zero. -/
  mean : ∀ i j : Idx D N, ∫ h, h i j ∂μ = 0
  /-- `E|h_{ij}|² = (S_θ)_{ij}`. -/
  var : ∀ i j : Idx D N, ∫ h, ‖h i j‖ ^ 2 ∂μ = varProf D N θ i j
  /-- `E h_{ij}² = 0` for `i ≠ j`, (2.2) [eq:meanvar2]. -/
  pseudo : ∀ i j : Idx D N, i ≠ j → ∫ h, h i j ^ 2 ∂μ = 0
  /-- `E|h_{ij}|^p ≤ C_p N^{-p/2}`, (2.3) [eq:highmoment]. -/
  moments : ∀ (p : ℕ) (i j : Idx D N), ∫ h, ‖h i j‖ ^ p ∂μ ≤ C p * (N : ℝ) ^ (-((p : ℝ) / 2))

/-- Two independent families of independent complex random variables form one independent
family, indexed by the disjoint sum. -/
private lemma Class_iIndepFun_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι κ : Type*} {u : ι → Ω → ℂ} {v : κ → Ω → ℂ}
    (h1 : iIndepFun u P) (h2 : iIndepFun v P)
    (h3 : IndepFun (fun ω i => u i ω) (fun ω k => v k ω) P) :
    iIndepFun (Sum.elim u v) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h1 h2 ⊢
  intro S A hA
  have e : (⋂ s ∈ S, Sum.elim u v s ⁻¹' A s) =
      (fun ω i => u i ω) ⁻¹' (Set.pi (S.toLeft : Set ι) fun i => A (Sum.inl i)) ∩
      (fun ω k => v k ω) ⁻¹' (Set.pi (S.toRight : Set κ) fun k => A (Sum.inr k)) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h _ hi, fun k hk => h _ hk⟩
    · rintro ⟨hl, hr⟩ s hs
      cases s with
      | inl i => exact hl i hs
      | inr k => exact hr k hs
  have m1 : MeasurableSet (Set.pi (S.toLeft : Set ι) fun i => A (Sum.inl i)) :=
    MeasurableSet.pi S.toLeft.countable_toSet fun i hi => hA _ (by simpa using hi)
  have m2 : MeasurableSet (Set.pi (S.toRight : Set κ) fun k => A (Sum.inr k)) :=
    MeasurableSet.pi S.toRight.countable_toSet fun i hi => hA _ (by simpa using hi)
  rw [e, h3.measure_inter_preimage_eq_mul _ _ m1 m2]
  have p1 : P ((fun ω i => u i ω) ⁻¹' (Set.pi (S.toLeft : Set ι) fun i => A (Sum.inl i))) =
      ∏ i ∈ S.toLeft, P (u i ⁻¹' A (Sum.inl i)) := by
    have := h1 S.toLeft (sets := fun i => A (Sum.inl i)) (fun i hi => hA _ (by simpa using hi))
    rw [← this]
    congr 1
    ext ω
    simp
  have p2 : P ((fun ω k => v k ω) ⁻¹' (Set.pi (S.toRight : Set κ) fun k => A (Sum.inr k))) =
      ∏ k ∈ S.toRight, P (v k ⁻¹' A (Sum.inr k)) := by
    have := h2 S.toRight (sets := fun k => A (Sum.inr k)) (fun i hi => hA _ (by simpa using hi))
    rw [← this]
    congr 1
    ext ω
    simp
  rw [p1, p2]
  conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := S), Finset.prod_disjSum]
  simp

/-- A family whose members outside a predicate are constants is independent as soon as its
restriction to the predicate is. -/
private lemma Class_iIndepFun_of_const {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : I → Prop) (g : I → Ω → ℂ)
    (hc : ∀ q, ¬ p q → ∃ c : ℂ, ∀ ω, g q ω = c)
    (h : iIndepFun (fun q : {q : I // p q} => g q.1) P) : iIndepFun g P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S A hA
  by_cases hbad : ∃ q ∈ S, ¬ p q ∧ g q ⁻¹' A q = ∅
  · obtain ⟨q0, hq0S, -, hq0⟩ := hbad
    have h1 : P (⋂ q ∈ S, g q ⁻¹' A q) = 0 := by
      refine measure_mono_null (t := (∅ : Set Ω)) ?_ measure_empty
      intro ω hω
      have := Set.mem_iInter₂.mp hω q0 hq0S
      rw [hq0] at this
      exact this
    have h2 : ∏ q ∈ S, P (g q ⁻¹' A q) = 0 :=
      Finset.prod_eq_zero hq0S (by rw [hq0]; simp)
    rw [h1, h2]
  · have hbad' : ∀ q ∈ S, ¬ p q → (g q ⁻¹' A q).Nonempty := by
      intro q hq hpq
      by_contra hne
      exact hbad ⟨q, hq, hpq, Set.not_nonempty_iff_eq_empty.mp hne⟩
    have huniv : ∀ q ∈ S, ¬ p q → g q ⁻¹' A q = Set.univ := by
      intro q hq hpq
      obtain ⟨c, hc'⟩ := hc q hpq
      obtain ⟨ω, hω⟩ := hbad' q hq hpq
      ext ω'
      simp only [Set.mem_preimage, Set.mem_univ, iff_true] at hω ⊢
      rw [hc' ω']
      rw [hc' ω] at hω
      exact hω
    have e1 : (⋂ q ∈ S, g q ⁻¹' A q) = ⋂ q ∈ S.filter p, g q ⁻¹' A q := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_filter]
      constructor
      · intro hω q hq
        exact hω q hq.1
      · intro hω q hq
        by_cases hpq : p q
        · exact hω q ⟨hq, hpq⟩
        · have := huniv q hq hpq
          have h' : ω ∈ g q ⁻¹' A q := by rw [this]; trivial
          exact h'
    have e2 : ∏ q ∈ S, P (g q ⁻¹' A q) = ∏ q ∈ S.filter p, P (g q ⁻¹' A q) := by
      rw [← Finset.prod_filter_mul_prod_filter_not S p]
      rw [Finset.prod_eq_one (s := S.filter fun q => ¬ p q)]
      · simp
      · intro q hq
        rw [Finset.mem_filter] at hq
        rw [huniv q hq.1 hq.2]
        simp
    rw [e1, e2]
    have := h (S.subtype p) (sets := fun q => A q.1)
      (fun q hq => hA q.1 (Finset.mem_subtype.mp hq))
    rw [Finset.prod_subtype_eq_prod_filter (f := fun q => P (g q ⁻¹' A q))] at this
    have e3 : (⋂ q ∈ S.subtype p, g q.1 ⁻¹' A q.1) = ⋂ q ∈ S.filter p, g q ⁻¹' A q := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_subtype, Set.mem_preimage]
      constructor
      · intro hω q hq
        exact hω ⟨q, hq.2⟩ hq.1
      · intro hω q hq
        exact hω q.1 ⟨hq, q.2⟩
    rw [e3] at this
    exact this

/-- Independence of a family transfers along a measure-preserving map. -/
private lemma Class_iIndepFun_comp_mp {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] {P : Measure Ω} {ν : Measure Ω'} {e : Ω → Ω'}
    (he : MeasurePreserving e P ν) {f : ι → Ω' → β} (hf : ∀ q, Measurable (f q))
    (h : iIndepFun f ν) : iIndepFun (fun q ω => f q (e ω)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S A hA
  have e1 : (⋂ q ∈ S, (fun ω => f q (e ω)) ⁻¹' A q) = e ⁻¹' (⋂ q ∈ S, f q ⁻¹' A q) := by
    ext ω
    simp
  have m1 : MeasurableSet (⋂ q ∈ S, f q ⁻¹' A q) :=
    MeasurableSet.biInter S.countable_toSet fun q hq => hf q (hA q hq)
  rw [e1, he.measure_preimage m1.nullMeasurableSet, h S hA]
  refine Finset.prod_congr rfl fun q hq => ?_
  exact (he.measure_preimage (hf q (hA q hq)).nullMeasurableSet).symm

/-- Independence of the family `g q ∘ e` under `P` gives independence of `g` under the image law `P.map e`. -/
private lemma Class_iIndepFun_map {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] {P : Measure Ω} {e : Ω → Ω'} (he : Measurable e)
    {g : ι → Ω' → β} (hg : ∀ q, Measurable (g q))
    (h : iIndepFun (fun q ω => g q (e ω)) P) : iIndepFun g (P.map e) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S A hA
  have e1 : (⋂ q ∈ S, (fun ω => g q (e ω)) ⁻¹' A q) = e ⁻¹' (⋂ q ∈ S, g q ⁻¹' A q) := by
    ext ω
    simp
  have m1 : MeasurableSet (⋂ q ∈ S, g q ⁻¹' A q) :=
    MeasurableSet.biInter S.countable_toSet fun q hq => hg q (hA q hq)
  rw [Measure.map_apply he m1, ← e1, h S hA]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [Measure.map_apply he (hg q (hA q hq))]
  rfl

/-- `coordLaw N L` is a probability measure. -/
private lemma Class_isProb_coordLaw (N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    IsProbabilityMeasure (coordLaw N L) := by
  unfold coordLaw
  infer_instance

/-- The block `w a` has law `coordLaw N L` under `blockLaw D N L`. -/
private lemma Class_mp_eval (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (a : Fin D) :
    MeasurePreserving (fun w : Fin D → Coords N => w a) (blockLaw D N L) (coordLaw N L) := by
  unfold blockLaw
  have := Class_isProb_coordLaw N L
  exact measurePreserving_eval (fun _ : Fin D => coordLaw N L) a

/-- The diagonal coordinates of one block have law `Measure.pi νd`. -/
private lemma Class_mp_fst (N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    MeasurePreserving (fun c : Coords N => c.1) (coordLaw N L)
      (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)) := by
  unfold coordLaw
  exact measurePreserving_fst

/-- The array coordinates of one block have law `Measure.pi (Measure.pi νo)`. -/
private lemma Class_mp_snd (N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    MeasurePreserving (fun c : Coords N => c.2) (coordLaw N L)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) := by
  unfold coordLaw
  exact measurePreserving_snd

/-- The coordinates of a block: the `N` diagonal entries (as complex numbers) and the `N²`
array entries are independent. -/
private lemma Class_iIndep_block (N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    iIndepFun (Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
      (fun (p : Fin N × Fin N) (c : Coords N) => c.2 p.1 p.2)) (coordLaw N L) := by
  have := Class_isProb_coordLaw N L
  have hx : iIndepFun (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ)) (coordLaw N L) := by
    have h0 : iIndepFun (fun (i : Fin N) (x : Fin N → ℝ) => x i)
        (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)) :=
      iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)
    have h1 := Class_iIndepFun_comp_mp (Class_mp_fst N L)
      (f := fun (i : Fin N) (x : Fin N → ℝ) => x i) (fun i => measurable_pi_apply i) h0
    exact h1.comp (fun _ => fun x : ℝ => (x : ℂ)) (fun _ => Complex.measurable_ofReal)
  have hy : iIndepFun (fun (p : Fin N × Fin N) (c : Coords N) => c.2 p.1 p.2) (coordLaw N L) := by
    have h1 : iIndepFun (fun (i : Fin N) (z : Fin N → Fin N → ℂ) => z i)
        (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) :=
      iIndepFun_pi (X := fun _ (z : Fin N → ℂ) => z) (fun _ => measurable_id.aemeasurable)
    have h2 : ∀ i : Fin N, iIndepFun (fun (j : Fin N) (z : Fin N → Fin N → ℂ) => z i j)
        (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) := by
      intro i
      have : IsProbabilityMeasure (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) := inferInstance
      have h0 : iIndepFun (fun (j : Fin N) (z : Fin N → ℂ) => z j)
          (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) :=
        iIndepFun_pi (X := fun _ (x : ℂ) => x) (fun _ => measurable_id.aemeasurable)
      exact Class_iIndepFun_comp_mp
        (measurePreserving_eval (fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) i)
        (f := fun (j : Fin N) (z : Fin N → ℂ) => z j) (fun j => measurable_pi_apply j) h0
    have h3 := iIndepFun_uncurry' (X := fun (i j : Fin N) (z : Fin N → Fin N → ℂ) => z i j)
      (fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)) h1 h2
    exact Class_iIndepFun_comp_mp (Class_mp_snd N L)
      (f := fun (p : Fin N × Fin N) (z : Fin N → Fin N → ℂ) => z p.1 p.2)
      (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)) h3
  have hp : IndepFun (fun (c : Coords N) (i : Fin N) => ((c.1 i : ℝ) : ℂ))
      (fun (c : Coords N) (p : Fin N × Fin N) => c.2 p.1 p.2) (coordLaw N L) := by
    unfold coordLaw
    exact indepFun_prod (μ := Measure.pi fun _ : Fin N => (L.νd : Measure ℝ))
      (ν := Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
      (X := fun (x : Fin N → ℝ) (i : Fin N) => ((x i : ℝ) : ℂ))
      (Y := fun (z : Fin N → Fin N → ℂ) (p : Fin N × Fin N) => z p.1 p.2)
      (measurable_pi_iff.mpr fun i => Complex.measurable_ofReal.comp (measurable_pi_apply i))
      (measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  exact Class_iIndepFun_sum hx hy hp

/-- The coordinates of all blocks are independent. -/
private lemma Class_iIndep_all (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    iIndepFun (fun (p : Fin D × (Fin N ⊕ (Fin N × Fin N))) (w : Fin D → Coords N) =>
      Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
        (fun (r : Fin N × Fin N) (c : Coords N) => c.2 r.1 r.2) p.2 (w p.1))
      (blockLaw D N L) := by
  have hm : ∀ k : Fin N ⊕ (Fin N × Fin N), Measurable
      (Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
        (fun (r : Fin N × Fin N) (c : Coords N) => c.2 r.1 r.2) k) := by
    intro k
    cases k with
    | inl i => exact Complex.measurable_ofReal.comp (measurable_pi_apply i |>.comp measurable_fst)
    | inr r => exact (measurable_pi_apply r.2).comp ((measurable_pi_apply r.1).comp measurable_snd)
  have h1 : iIndepFun (fun (a : Fin D) (w : Fin D → Coords N) =>
      fun k : Fin N ⊕ (Fin N × Fin N) =>
        Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
          (fun (r : Fin N × Fin N) (c : Coords N) => c.2 r.1 r.2) k (w a)) (blockLaw D N L) := by
    have := Class_isProb_coordLaw N L
    unfold blockLaw
    exact iIndepFun_pi (μ := fun _ : Fin D => coordLaw N L)
      (X := fun _ (c : Coords N) (k : Fin N ⊕ (Fin N × Fin N)) =>
        Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
          (fun (r : Fin N × Fin N) (c : Coords N) => c.2 r.1 r.2) k c)
      (fun _ => (measurable_pi_iff.mpr hm).aemeasurable)
  have h2 : ∀ a : Fin D, iIndepFun (fun (k : Fin N ⊕ (Fin N × Fin N)) (w : Fin D → Coords N) =>
      Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
        (fun (r : Fin N × Fin N) (c : Coords N) => c.2 r.1 r.2) k (w a)) (blockLaw D N L) :=
    fun a => Class_iIndepFun_comp_mp (Class_mp_eval D N L a) hm (Class_iIndep_block N L)
  exact iIndepFun_uncurry' (X := fun (a : Fin D) (k : Fin N ⊕ (Fin N × Fin N))
    (w : Fin D → Coords N) =>
      Sum.elim (fun (i : Fin N) (c : Coords N) => ((c.1 i : ℝ) : ℂ))
        (fun (r : Fin N × Fin N) (c : Coords N) => c.2 r.1 r.2) k (w a))
    (fun a k => (hm k).comp (measurable_pi_apply a)) h1 h2

/-- The scaling `N^{-1/2}` of `wig N`. -/
private abbrev Class_c (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ))

/-- Off the blocks the entry of `blockH` vanishes. -/
private lemma Class_blockH_off (D N : ℕ) (w : Fin D → Coords N) (p q : Idx D N)
    (h : p.1 ≠ q.1) : blockH D N w p q = 0 := by
  simp [blockH, h]

/-- The diagonal entry of `blockH`: `N^{-1/2}` times a diagonal coordinate. -/
private lemma Class_blockH_diag (D N : ℕ) (w : Fin D → Coords N) (p : Idx D N) :
    blockH D N w p p = (Class_c N : ℂ) * (((w p.1).1 p.2 : ℝ) : ℂ) := by
  simp [blockH, wig, Class_c]

/-- The entry of `blockH` above the diagonal of a block: `N^{-1/2}` times an array coordinate. -/
private lemma Class_blockH_up (D N : ℕ) (w : Fin D → Coords N) (p q : Idx D N)
    (h : p.1 = q.1) (hij : p.2 < q.2) :
    blockH D N w p q = (Class_c N : ℂ) * (w p.1).2 p.2 q.2 := by
  simp [blockH, wig, Class_c, h, hij.ne, hij]

/-- The entry of `blockH` below the diagonal of a block: `N^{-1/2}` times the conjugate of an array coordinate. -/
private lemma Class_blockH_low (D N : ℕ) (w : Fin D → Coords N) (p q : Idx D N)
    (h : p.1 = q.1) (hij : q.2 < p.2) :
    blockH D N w p q = (Class_c N : ℂ) * star ((w p.1).2 q.2 p.2) := by
  simp [blockH, wig, Class_c, h, hij.ne', hij.not_gt]

/-- Every entry of `blockH D N w` is a measurable function of `w`. -/
private lemma Class_measurable_entry (D N : ℕ) (p q : Idx D N) :
    Measurable fun w : Fin D → Coords N => blockH D N w p q := by
  by_cases h : p.1 = q.1
  · rcases lt_trichotomy p.2 q.2 with hij | hij | hij
    · have : (fun w : Fin D → Coords N => blockH D N w p q) =
          fun w => (Class_c N : ℂ) * (w p.1).2 p.2 q.2 :=
        funext fun w => Class_blockH_up D N w p q h hij
      rw [this]
      exact measurable_const.mul
        ((measurable_pi_apply q.2).comp ((measurable_pi_apply p.2).comp
          (measurable_snd.comp (measurable_pi_apply p.1))))
    · have hpq : p = q := Prod.ext h hij
      subst hpq
      have : (fun w : Fin D → Coords N => blockH D N w p p) =
          fun w => (Class_c N : ℂ) * (((w p.1).1 p.2 : ℝ) : ℂ) :=
        funext fun w => Class_blockH_diag D N w p
      rw [this]
      exact measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_pi_apply p.2).comp (measurable_fst.comp (measurable_pi_apply p.1))))
    · have : (fun w : Fin D → Coords N => blockH D N w p q) =
          fun w => (Class_c N : ℂ) * star ((w p.1).2 q.2 p.2) :=
        funext fun w => Class_blockH_low D N w p q h hij
      rw [this]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply p.2).comp ((measurable_pi_apply q.2).comp
          (measurable_snd.comp (measurable_pi_apply p.1)))))
  · have : (fun w : Fin D → Coords N => blockH D N w p q) = fun _ => 0 :=
      funext fun w => Class_blockH_off D N w p q h
    rw [this]
    exact measurable_const

/-- The map `w ↦ blockH D N w`, read as an array, is measurable. -/
private lemma Class_measurable_map (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => Class_measurable_entry D N p q

/-- The entries `h_{pq}` of `blockH` with `toLex p ≤ toLex q` are independent. -/
private lemma Class_iIndep_entries (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    iIndepFun (fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2})
      (w : Fin D → Coords N) => blockH D N w q.1.1 q.1.2) (blockLaw D N L) := by
  have hprob : IsProbabilityMeasure (blockLaw D N L) := blockLaw_isProbabilityMeasure D N L
  refine Class_iIndepFun_of_const (fun q => q.1.1.1 = q.1.2.1)
    (fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}) (w : Fin D → Coords N) =>
      blockH D N w q.1.1 q.1.2) ?_ ?_
  · intro q hq
    exact ⟨0, fun w => Class_blockH_off D N w _ _ hq⟩
  · let κ : {q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2} // q.1.1.1 = q.1.2.1} →
        Fin D × (Fin N ⊕ (Fin N × Fin N)) :=
      fun q => (q.1.1.1.1, if q.1.1.1.2 = q.1.1.2.2 then Sum.inl q.1.1.1.2
        else Sum.inr (q.1.1.1.2, q.1.1.2.2))
    have hκ : Function.Injective κ := by
      rintro ⟨⟨⟨⟨a, i⟩, ⟨b, j⟩⟩, hle⟩, hab⟩ ⟨⟨⟨⟨a', i'⟩, ⟨b', j'⟩⟩, hle'⟩, hab'⟩ h
      simp only at hab hab'
      subst hab hab'
      simp only [κ, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      by_cases h1 : i = j <;> by_cases h1' : i' = j' <;> simp [h1, h1'] at h2
      · subst h1 h1'; simp [h2]
      · obtain ⟨rfl, rfl⟩ := h2; rfl
    have h := ((Class_iIndep_all D N L).precomp hκ).comp
      (fun _ => fun z : ℂ => (Class_c N : ℂ) * z) (fun _ => measurable_const.mul measurable_id)
    convert h using 1
    funext q w
    obtain ⟨⟨⟨⟨a, i⟩, ⟨b, j⟩⟩, hle⟩, hab⟩ := q
    simp only at hab
    subst hab
    have hij : i ≤ j := by
      rcases Prod.Lex.toLex_le_toLex.mp hle with h1 | ⟨-, h1⟩
      · exact absurd h1 (lt_irrefl _)
      · exact h1
    by_cases h1 : i = j
    · subst h1
      have := Class_blockH_diag D N w (a, i)
      simpa [κ] using this
    · have h2 : i < j := lt_of_le_of_ne hij h1
      have := Class_blockH_up D N w (a, i) (a, j) rfl h2
      simpa [κ, h1] using this

/-- The four moment facts of a unit-variance noise `Z`, with the moment constants `C`. -/
private structure Class_Unit {Ω : Type*} [MeasurableSpace Ω] (C : ℕ → ℝ) (P : Measure Ω)
    (Z : Ω → ℂ) : Prop where
  integrable : ∀ k : ℕ, Integrable (fun w => ‖Z w‖ ^ k) P
  mean : ∫ w, Z w ∂P = 0
  var : ∫ w, ‖Z w‖ ^ 2 ∂P = 1
  moments : ∀ k : ℕ, ∫ w, ‖Z w‖ ^ k ∂P ≤ C k

/-- The four moment facts of the scaled noise `X = N^{-1/2} Z`: finiteness, mean `0`, variance `s`
and `E|X|^k ≤ C_k N^{-k/2}`. -/
private structure Class_Mom {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (C : ℕ → ℝ) (s : ℝ)
    (P : Measure Ω) (X : Ω → ℂ) : Prop where
  integrable : ∀ k : ℕ, Integrable (fun w => ‖X w‖ ^ k) P
  mean : ∫ w, X w ∂P = 0
  var : ∫ w, ‖X w‖ ^ 2 ∂P = s
  moments : ∀ k : ℕ, ∫ w, ‖X w‖ ^ k ∂P ≤ C k * (N : ℝ) ^ (-((k : ℝ) / 2))

/-- `N^{-1/2} ≥ 0`. -/
private lemma Class_c_nonneg (N : ℕ) : 0 ≤ Class_c N := Real.rpow_nonneg (Nat.cast_nonneg N) _

/-- `(N^{-1/2})² = N⁻¹`. -/
private lemma Class_c_sq (N : ℕ) : Class_c N ^ 2 = (N : ℝ)⁻¹ := by
  rw [Class_c, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num [Real.rpow_neg_one]

/-- `(N^{-1/2})^k = N^{-k/2}`. -/
private lemma Class_c_pow (N k : ℕ) : Class_c N ^ k = (N : ℝ) ^ (-((k : ℝ) / 2)) := by
  rw [Class_c, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- The norm of a real scalar multiple `N^{-1/2} z`. -/
private lemma Class_norm_scale (N : ℕ) (z : ℂ) : ‖(Class_c N : ℂ) * z‖ = Class_c N * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Class_c_nonneg N)]

/-- Scaling a unit-variance noise by `N^{-1/2}` gives variance `N⁻¹` and the moment bounds of (2.3) [eq:highmoment]. -/
private lemma Class_Mom_of_unit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : ℕ)
    {C : ℕ → ℝ} {Z : Ω → ℂ} (h : Class_Unit C P Z) :
    Class_Mom N C (N : ℝ)⁻¹ P (fun w => (Class_c N : ℂ) * Z w) := by
  refine ⟨fun k => ?_, ?_, ?_, fun k => ?_⟩
  · simp only [Class_norm_scale, mul_pow]
    exact (h.integrable k).const_mul _
  · rw [integral_const_mul, h.mean, mul_zero]
  · simp only [Class_norm_scale, mul_pow]
    rw [integral_const_mul, h.var, mul_one, Class_c_sq]
  · simp only [Class_norm_scale, mul_pow]
    rw [integral_const_mul, Class_c_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (h.moments k) (by positivity)

/-- Integrals against a measure-preserving image. -/
private lemma Class_integral_comp {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Measure Ω} {ν : Measure α} {cd : Ω → α}
    (hcd : MeasurePreserving cd P ν) {G : α → E} (hG : AEStronglyMeasurable G ν) :
    ∫ w, G (cd w) ∂P = ∫ a, G a ∂ν := by
  rw [← hcd.map_eq] at hG ⊢
  exact (integral_map hcd.measurable.aemeasurable hG).symm

/-- The moment facts of a noise transfer along a measure-preserving coordinate map. -/
private lemma Class_Unit.comp {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {ν : Measure α} {cd : Ω → α} (hcd : MeasurePreserving cd P ν)
    {C : ℕ → ℝ} {Z : α → ℂ} (hZ : Measurable Z) (h : Class_Unit C ν Z) :
    Class_Unit C P (fun w => Z (cd w)) := by
  have hn : ∀ k : ℕ, Measurable fun a => ‖Z a‖ ^ k := fun k => hZ.norm.pow_const k
  refine ⟨fun k => ?_, ?_, ?_, fun k => ?_⟩
  · exact (hcd.integrable_comp (hn k).aestronglyMeasurable).mpr (h.integrable k)
  · rw [Class_integral_comp hcd hZ.aestronglyMeasurable, h.mean]
  · rw [Class_integral_comp hcd (hn 2).aestronglyMeasurable (G := fun a => ‖Z a‖ ^ 2), h.var]
  · rw [Class_integral_comp hcd (hn k).aestronglyMeasurable (G := fun a => ‖Z a‖ ^ k)]
    exact h.moments k

/-- The absolute moments of `νd` and `νo` are nonnegative. -/
private lemma Class_nonneg_moment {C : ℕ → ℝ} (L : EntryLaws C) (k : ℕ) :
    0 ≤ ∫ x, |x| ^ k ∂(L.νd : Measure ℝ) ∧ 0 ≤ ∫ z, ‖z‖ ^ k ∂(L.νo : Measure ℂ) :=
  ⟨integral_nonneg fun x => by positivity, integral_nonneg fun z => by positivity⟩

/-- The diagonal law `νd` has the moment facts of (2.1) [eq:meanvar] and (2.3) [eq:highmoment]. -/
private lemma Class_unit_d {C : ℕ → ℝ} (L : EntryLaws C) :
    Class_Unit C (L.νd : Measure ℝ) (fun x : ℝ => (x : ℂ)) := by
  refine ⟨fun k => ?_, ?_, ?_, fun k => ?_⟩
  · simpa [Complex.norm_real] using L.intd k
  · rw [integral_complex_ofReal (f := fun x : ℝ => x), L.meand]
    simp
  · simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact L.vard
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith [L.moments k, (Class_nonneg_moment L k).2]

/-- The off-diagonal law `νo` has the moment facts of (2.1) [eq:meanvar] and (2.3) [eq:highmoment]. -/
private lemma Class_unit_o {C : ℕ → ℝ} (L : EntryLaws C) :
    Class_Unit C (L.νo : Measure ℂ) (fun z : ℂ => z) := by
  refine ⟨fun k => L.into k, L.meano, L.varo, fun k => ?_⟩
  linarith [L.moments k, (Class_nonneg_moment L k).1]

/-- The conjugate of an off-diagonal entry has the moment facts of (2.1) [eq:meanvar] and (2.3) [eq:highmoment]. -/
private lemma Class_unit_ostar {C : ℕ → ℝ} (L : EntryLaws C) :
    Class_Unit C (L.νo : Measure ℂ) (fun z : ℂ => star z) := by
  refine ⟨fun k => ?_, ?_, ?_, fun k => ?_⟩
  · simpa using L.into k
  · have : ∫ z : ℂ, star z ∂(L.νo : Measure ℂ) = star (∫ z : ℂ, z ∂(L.νo : Measure ℂ)) := by
      simpa [Complex.star_def] using integral_conj (f := fun z : ℂ => z) (μ := (L.νo : Measure ℂ))
    rw [this, L.meano, star_zero]
  · simpa using L.varo
  · simp only [norm_star]
    linarith [L.moments k, (Class_nonneg_moment L k).1]

/-- The diagonal coordinate `x_a(i)` of block `a` has law `νd`. -/
private lemma Class_mp_x (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (a : Fin D) (i : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w a).1 i) (blockLaw D N L)
      (L.νd : Measure ℝ) := by
  have h3 : MeasurePreserving (fun x : Fin N → ℝ => x i)
      (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)) (L.νd : Measure ℝ) :=
    measurePreserving_eval (fun _ : Fin N => (L.νd : Measure ℝ)) i
  exact h3.comp ((Class_mp_fst N L).comp (Class_mp_eval D N L a))

/-- The array coordinate `y_a(i, j)` of block `a` has law `νo`. -/
private lemma Class_mp_y (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (a : Fin D) (i j : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w a).2 i j) (blockLaw D N L)
      (L.νo : Measure ℂ) := by
  have h4 : MeasurePreserving (fun z : Fin N → ℂ => z j)
      (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) (L.νo : Measure ℂ) :=
    measurePreserving_eval (fun _ : Fin N => (L.νo : Measure ℂ)) j
  have h3 : MeasurePreserving (fun z : Fin N → Fin N → ℂ => z i)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
      (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) :=
    measurePreserving_eval (fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) i
  exact h4.comp (h3.comp ((Class_mp_snd N L).comp (Class_mp_eval D N L a)))

/-- The moment constants satisfy `C_k ≥ 0`, and `C_0 ≥ 1`. -/
private lemma Class_C_facts {C : ℕ → ℝ} (L : EntryLaws C) (k : ℕ) :
    0 ≤ C k ∧ (k = 0 → 1 ≤ C k) := by
  have h := L.moments k
  have hn := Class_nonneg_moment L k
  refine ⟨by linarith [hn.1, hn.2], ?_⟩
  rintro rfl
  simp at h
  linarith

/-- The entry `(p, q)` of `blockH` has the moment facts of `Class_Mom`, with the variance
`varProf D N 1 p q`. -/
private lemma Class_entry_mom (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (p q : Idx D N) :
    Class_Mom N C (varProf D N 1 p q) (blockLaw D N L) (fun w => blockH D N w p q) := by
  have hprob : IsProbabilityMeasure (blockLaw D N L) := blockLaw_isProbabilityMeasure D N L
  by_cases h : p.1 = q.1
  · rcases lt_trichotomy p.2 q.2 with hij | hij | hij
    · have hv : varProf D N 1 p q = (N : ℝ)⁻¹ := by simp [varProf, h]
      rw [hv]
      have := Class_Mom_of_unit N
        ((Class_unit_o L).comp (Class_mp_y D N L p.1 p.2 q.2) measurable_id)
      have e : (fun w : Fin D → Coords N => blockH D N w p q) =
          fun w => (Class_c N : ℂ) * (w p.1).2 p.2 q.2 :=
        funext fun w => Class_blockH_up D N w p q h hij
      rw [e]
      exact this
    · have hpq : p = q := Prod.ext h hij
      subst hpq
      have hv : varProf D N 1 p p = (N : ℝ)⁻¹ := by simp [varProf]
      rw [hv]
      have := Class_Mom_of_unit N
        ((Class_unit_d L).comp (Class_mp_x D N L p.1 p.2) Complex.measurable_ofReal)
      have e : (fun w : Fin D → Coords N => blockH D N w p p) =
          fun w => (Class_c N : ℂ) * (((w p.1).1 p.2 : ℝ) : ℂ) :=
        funext fun w => Class_blockH_diag D N w p
      rw [e]
      exact this
    · have hv : varProf D N 1 p q = (N : ℝ)⁻¹ := by simp [varProf, h]
      rw [hv]
      have := Class_Mom_of_unit N
        ((Class_unit_ostar L).comp (Class_mp_y D N L p.1 q.2 p.2)
          (continuous_star (R := ℂ)).measurable)
      have e : (fun w : Fin D → Coords N => blockH D N w p q) =
          fun w => (Class_c N : ℂ) * star ((w p.1).2 q.2 p.2) :=
        funext fun w => Class_blockH_low D N w p q h hij
      rw [e]
      exact this
  · have hv : varProf D N 1 p q = 0 := by simp [varProf, h]
    rw [hv]
    have e : (fun w : Fin D → Coords N => blockH D N w p q) = fun _ => 0 :=
      funext fun w => Class_blockH_off D N w p q h
    rw [e]
    refine ⟨fun k => ?_, ?_, ?_, fun k => ?_⟩
    · simp
    · simp
    · simp
    · have h0 : ∫ w : Fin D → Coords N, ‖(0 : ℂ)‖ ^ k ∂(blockLaw D N L) = (0 : ℝ) ^ k := by
        simp
      rw [h0]
      obtain ⟨h1, h2⟩ := Class_C_facts L k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using h2 rfl
      · rw [zero_pow hk.ne']
        exact mul_nonneg h1 (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The entries `(p, q)`, `p ≠ q`, of `blockH` have vanishing pseudo-variance `E h² = 0`. -/
private lemma Class_entry_pseudo (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (p q : Idx D N)
    (hpq : p ≠ q) : ∫ w, (blockH D N w p q) ^ 2 ∂(blockLaw D N L) = 0 := by
  have hprob : IsProbabilityMeasure (blockLaw D N L) := blockLaw_isProbabilityMeasure D N L
  by_cases h : p.1 = q.1
  · have hne : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
    rcases lt_or_gt_of_ne hne with hij | hij
    · have e : (fun w : Fin D → Coords N => blockH D N w p q ^ 2) =
          fun w => (Class_c N : ℂ) ^ 2 * (((w p.1).2 p.2 q.2) ^ 2) :=
        funext fun w => by rw [Class_blockH_up D N w p q h hij, mul_pow]
      rw [e, integral_const_mul]
      have h1 : ∫ w : Fin D → Coords N, ((w p.1).2 p.2 q.2) ^ 2 ∂(blockLaw D N L) = 0 :=
        (Class_integral_comp (Class_mp_y D N L p.1 p.2 q.2) (G := fun z : ℂ => z ^ 2)
          (continuous_pow 2).aestronglyMeasurable).trans L.pseudo
      rw [h1, mul_zero]
    · have e : (fun w : Fin D → Coords N => blockH D N w p q ^ 2) =
          fun w => (Class_c N : ℂ) ^ 2 * star (((w p.1).2 q.2 p.2) ^ 2) :=
        funext fun w => by rw [Class_blockH_low D N w p q h hij, mul_pow, star_pow]
      rw [e, integral_const_mul]
      have h1 : ∫ w : Fin D → Coords N, star (((w p.1).2 q.2 p.2) ^ 2) ∂(blockLaw D N L) = 0 := by
        refine (Class_integral_comp (Class_mp_y D N L p.1 q.2 p.2)
          (G := fun z : ℂ => star (z ^ 2))
          (continuous_star.comp (continuous_pow 2)).aestronglyMeasurable).trans ?_
        have : ∫ z : ℂ, star (z ^ 2) ∂(L.νo : Measure ℂ) =
            star (∫ z : ℂ, z ^ 2 ∂(L.νo : Measure ℂ)) := by
          exact integral_conj (f := fun z : ℂ => z ^ 2) (μ := (L.νo : Measure ℂ))
        rw [this, L.pseudo, star_zero]
      rw [h1, mul_zero]
  · have e : (fun w : Fin D → Coords N => blockH D N w p q ^ 2) = fun _ => 0 :=
      funext fun w => by rw [Class_blockH_off D N w p q h]; simp
    rw [e]
    simp

/-- The Wigner matrix `wig n c` is Hermitian. -/
private lemma Class_wig_isHermitian (n : ℕ) (c : Coords n) : (wig n c).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- `blockH D N w` is Hermitian. -/
private lemma Class_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (Class_wig_isHermitian N (w q.1)).apply p.2 q.2
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- The set of Hermitian arrays is measurable. -/
private lemma Class_measurableSet_herm (D N : ℕ) :
    MeasurableSet {h : Idx D N → Idx D N → ℂ | (Matrix.of h).IsHermitian} := by
  have : {h : Idx D N → Idx D N → ℂ | (Matrix.of h).IsHermitian} =
      ⋂ i, ⋂ j, {h | star (h j i) = h i j} := by
    ext h
    simp [Matrix.IsHermitian.ext_iff]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_eq_fun ((continuous_star (R := ℂ)).measurable.comp
      ((measurable_pi_apply i).comp (measurable_pi_apply j))) 
      ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- Integrals of a continuous function of the entry `(i, j)` against the law of the array
`blockH D N w` equal the integrals of the same function of `blockH D N w i j` against `blockLaw`. -/
private lemma Class_integral_map (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i j : Idx D N) (F : ℂ → E) (hF : Continuous F) :
    ∫ h, F (h i j) ∂((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) =
      ∫ w, F (blockH D N w i j) ∂(blockLaw D N L) :=
  integral_map (Class_measurable_map D N).aemeasurable
    (hF.comp ((continuous_apply j).comp (continuous_apply i))).aestronglyMeasurable

/-- Assumption 1 [main_assm]: the block matrix `H` of (1.3) [matrix_H] is in the class with
`θ = 1` and the same moment constants, for every `D ≥ 1`. -/
theorem llClass_blockH (D N : ℕ) (C : ℕ → ℝ) (L : EntryLaws C) :
    LLClass D N C 1 ((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) := by
  have hprob : IsProbabilityMeasure (blockLaw D N L) := blockLaw_isProbabilityMeasure D N L
  have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    Class_measurable_map D N
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ae_map_iff hf.aemeasurable (Class_measurableSet_herm D N)]
    exact Eventually.of_forall fun w => Class_blockH_isHermitian D N w
  · exact Class_iIndepFun_map hf
      (g := fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2})
        (h : Idx D N → Idx D N → ℂ) => h q.1.1 q.1.2)
      (fun q => (measurable_pi_apply q.1.2).comp (measurable_pi_apply q.1.1))
      (Class_iIndep_entries D N L)
  · intro k i j
    have hm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => ‖h i j‖ ^ k)
        ((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) :=
      (((continuous_norm.comp ((continuous_apply j).comp (continuous_apply i))).pow k)
        ).aestronglyMeasurable
    exact (integrable_map_measure hm hf.aemeasurable).mpr ((Class_entry_mom D N L i j).integrable k)
  · intro i j
    rw [Class_integral_map D N L i j (fun z : ℂ => z) continuous_id]
    exact (Class_entry_mom D N L i j).mean
  · intro i j
    rw [Class_integral_map D N L i j (fun z : ℂ => ‖z‖ ^ 2) (continuous_norm.pow 2)]
    exact (Class_entry_mom D N L i j).var
  · intro i j hij
    rw [Class_integral_map D N L i j (fun z : ℂ => z ^ 2) (continuous_pow 2)]
    exact Class_entry_pseudo D N L i j hij
  · intro k i j
    rw [Class_integral_map D N L i j (fun z : ℂ => ‖z‖ ^ k) (continuous_norm.pow k)]
    exact (Class_entry_mom D N L i j).moments k

/-- The spectral domain `𝐃(τ) = {z : |z| ≤ τ⁻¹, |Im z| ≥ N^{-1+τ}}` of Definition 3.1 [def_wtM]. -/
def specDom (τ : ℝ) (N : ℕ) : Set ℂ :=
  {z | ‖z‖ ≤ τ⁻¹ ∧ (N : ℝ) ^ (-1 + τ) ≤ |z.im|}

/-- The control parameter `√(Im m/(Nη)) + 1/(Nη)` of (2.22) [eq:aniso_local], written with
`|Im m|` and `|η|` so that it applies on both half planes. -/
def psiIso {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ) (z : ℂ) : ℝ :=
  Real.sqrt (|(mExt Λ z).im| / ((N : ℝ) * |z.im|)) + 1 / ((N : ℝ) * |z.im|)

/-- The resolvent `G(z) = (X - z)⁻¹` of (2.12) [def_resolv] is a true inverse for Hermitian `X`
and `Im z ≠ 0`. -/
theorem res_mul_sub_of_im_ne {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (X - z • (1 : Matrix ι ι ℂ)) * res X z = 1 ∧ res X z * (X - z • (1 : Matrix ι ι ℂ)) = 1 := by
  rcases lt_or_gt_of_ne hz with h | h
  · set z' : ℂ := starRingEnd ℂ z with hz'
    have hz'im : 0 < z'.im := by simpa [hz'] using h
    obtain ⟨h1, h2⟩ := res_mul_sub X hX z' hz'im
    have hc := res_conj X hX z' hz'im
    have e : X - z • (1 : Matrix ι ι ℂ) = (X - z' • (1 : Matrix ι ι ℂ))ᴴ := by
      rw [conjTranspose_sub, hX.eq, conjTranspose_smul, conjTranspose_one]
      simp [hz']
    have e2 : res X z = (res X z')ᴴ := by
      rw [← hc]
      simp [hz']
    rw [e2, e]
    exact ⟨by rw [← conjTranspose_mul, h2, conjTranspose_one],
      by rw [← conjTranspose_mul, h1, conjTranspose_one]⟩
  · exact res_mul_sub X hX z h

/-- Definition 2.7 [defn_Mm] on both half planes: for `Im z ≠ 0`, `m(z) = ⟨M(z)⟩` as in
(2.16) [self_m], `M(z) = (Λ - z - m(z))⁻¹` of (2.17) [def_G0] is a true inverse, and
`Im m(z)` has the sign of `Im z`. -/
theorem MExt_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    mExt Λ z = ntr (MExt Λ z) ∧ (Λ - (z + mExt Λ z) • (1 : Matrix ι ι ℂ)) * MExt Λ z = 1 ∧
      0 < (mExt Λ z).im * z.im := by
  rcases lt_or_gt_of_ne hz with h | h
  · set z' : ℂ := star z with hz'
    have hz'im : 0 < z'.im := by simpa [hz'] using h
    obtain ⟨hc1, hc2⟩ := mExt_conj Λ hΛ z' hz'im.ne'
    have e1 : mExt Λ z' = mSol Λ z' := by simp [mExt, hz'im]
    have e2 : MExt Λ z' = MSol Λ z' := by simp [MExt, MSol, e1]
    obtain ⟨s1, s2, s3⟩ := mSol_spec Λ hΛ z' hz'im
    have hzz : star z' = z := by simp [hz']
    rw [hzz] at hc1 hc2
    rw [hc1, hc2, e1, e2]
    refine ⟨?_, ?_, ?_⟩
    · rw [s2]
      simp [ntr, trace_conjTranspose, star_mul']
    · have hA : Λ - (z + star (mSol Λ z')) • (1 : Matrix ι ι ℂ) =
          (Λ - (z' + mSol Λ z') • (1 : Matrix ι ι ℂ))ᴴ := by
        rw [conjTranspose_sub, hΛ.eq, conjTranspose_smul, conjTranspose_one, star_add, hzz]
      rw [hA, ← conjTranspose_mul, mul_eq_one_comm.mp s3, conjTranspose_one]
    · simp only [Complex.star_def, Complex.conj_im]
      nlinarith [mul_pos s1 hz'im, show z'.im = -z.im by simp [hz']]
  · have e1 : mExt Λ z = mSol Λ z := by simp [mExt, h]
    have e2 : MExt Λ z = MSol Λ z := by simp [MExt, MSol, e1]
    obtain ⟨s1, s2, s3⟩ := mSol_spec Λ hΛ z h
    rw [e1, e2]
    exact ⟨s2, s3, mul_pos s1 h⟩

end RBMTransitionEdge

end
