module

public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.Prob.StochDom
public import RBMTransitionEdge.Tools.Resolvent
public import RBMTransitionEdge.Det.Core

@[expose] public section

/-!
# Sequences of class members and uniform statements

The setting of Lemma 2.9 [lem_loc] along a sequence of members of `LLClass`, the a priori bound
`|(G - M)_{st}| ≺ φ` in the sense of Definition 2.8 [stoch_domination], padding of the class, and
the passage from sequences to statements uniform over the class.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A sequence of members of `LLClass` in the setting of Lemma 2.9 [lem_loc]: fixed `D ≥ 1`,
`δ_A > 0` and moment constants `C`; `θ_N ∈ [0, 1]`; `μ_N` in `LLClass D N C θ_N`;
`‖A_N‖ ≤ N^{-δ_A}`. -/
structure LLSeq (D : ℕ) (δA : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) : Prop where
  /-- `D ≥ 1`. -/
  one_le_D : 1 ≤ D
  /-- `δ_A > 0`. -/
  pos : 0 < δA
  /-- `θ_N ∈ [0, 1]`. -/
  theta : ∀ N, 0 ≤ θ N ∧ θ N ≤ 1
  /-- `μ_N` is a member of the class. -/
  mem : ∀ N, LLClass D N C (θ N) (μ N)
  /-- `‖A_N‖ ≤ N^{-δ_A}`. -/
  small : ∀ N, opNorm (A N) ≤ (N : ℝ) ^ (-δA)

/-- The a priori bound `|(G - M)_{st}| ≺ φ_N(z)`, in sup form (Definition 2.8 [stoch_domination])
over `z ∈ Z_N` and deterministic unit `s, t`, for `G = (H + Λ - z)⁻¹`, `Λ = lam D N A_N`. -/
def aprioriLL (D : ℕ) (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ))
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (Z : ℕ → Set ℂ) (φ : ℕ → ℂ → ℝ) : Prop :=
  PrecS μ (U := fun N => {z // z ∈ Z N} × {s : Idx D N → ℂ // ∑ i, ‖s i‖ ^ 2 = 1} ×
      {t : Idx D N → ℂ // ∑ i, ‖t i‖ ^ 2 = 1})
    (fun N w h => ‖star w.2.1.1 ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) w.1.1 -
      MExt (lam D N (A N)) w.1.1) *ᵥ w.2.2.1)‖)
    (fun N w _ => φ N w.1.1)

/-! ### Arrays with independent entries on and above the diagonal -/

/-- The index set of the independent entries of an array: the pairs `(i, j)` with `i ≤ j` in the
lexicographic order of `Idx D N`. -/
private abbrev Uniform_Ix (D N : ℕ) := {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}

/-- The coordinate carrying the entry `(i, j)`: the pair `(i, j)` if `i ≤ j`, else `(j, i)`. -/
private def Uniform_key {D N : ℕ} (i j : Idx D N) : Uniform_Ix D N :=
  if h : toLex i ≤ toLex j then ⟨(i, j), h⟩ else ⟨(j, i), (not_le.mp h).le⟩

/-- Identity on and above the diagonal, complex conjugation below it. -/
private def Uniform_kap {D N : ℕ} (i j : Idx D N) (z : ℂ) : ℂ :=
  if toLex i ≤ toLex j then z else star z

/-- The array whose entries on and above the diagonal are `ω`, completed below the diagonal by
complex conjugation. -/
private def Uniform_arr {D N : ℕ} (ω : Uniform_Ix D N → ℂ) : Idx D N → Idx D N → ℂ :=
  fun i j => Uniform_kap i j (ω (Uniform_key i j))

private lemma Uniform_arr_of_le {D N : ℕ} (ω : Uniform_Ix D N → ℂ) {i j : Idx D N}
    (h : toLex i ≤ toLex j) : Uniform_arr ω i j = ω ⟨(i, j), h⟩ := by
  simp [Uniform_arr, Uniform_kap, Uniform_key, h]

private lemma Uniform_arr_of_not_le {D N : ℕ} (ω : Uniform_Ix D N → ℂ) {i j : Idx D N}
    (h : ¬ toLex i ≤ toLex j) :
    Uniform_arr ω i j = star (ω ⟨(j, i), (not_le.mp h).le⟩) := by
  simp [Uniform_arr, Uniform_kap, Uniform_key, h]

private lemma Uniform_kap_cases {D N : ℕ} (i j : Idx D N) :
    (∀ z, Uniform_kap i j z = z) ∨ (∀ z, Uniform_kap i j z = star z) := by
  by_cases h : toLex i ≤ toLex j
  · exact Or.inl fun z => by simp [Uniform_kap, h]
  · exact Or.inr fun z => by simp [Uniform_kap, h]

private lemma Uniform_continuous_kap {D N : ℕ} (i j : Idx D N) : Continuous (Uniform_kap i j) := by
  rcases Uniform_kap_cases i j with h | h
  · have : Uniform_kap i j = fun z => z := funext h
    rw [this]
    exact continuous_id
  · have : Uniform_kap i j = fun z => star z := funext h
    rw [this]
    exact continuous_star

private lemma Uniform_norm_kap {D N : ℕ} (i j : Idx D N) (z : ℂ) : ‖Uniform_kap i j z‖ = ‖z‖ := by
  rcases Uniform_kap_cases i j with h | h <;> simp [h]

private lemma Uniform_kap_sq {D N : ℕ} (i j : Idx D N) (z : ℂ) :
    Uniform_kap i j z ^ 2 = Uniform_kap i j (z ^ 2) := by
  rcases Uniform_kap_cases i j with h | h <;> simp [h, star_pow]

private lemma Uniform_kap_zero {D N : ℕ} (i j : Idx D N) : Uniform_kap i j 0 = 0 := by
  rcases Uniform_kap_cases i j with h | h <;> simp [h]

/-- Conjugation commutes with the integral. -/
private lemma Uniform_integral_kap {D N : ℕ} (i j : Idx D N) (ν : Measure ℂ) (f : ℂ → ℂ) :
    ∫ x, Uniform_kap i j (f x) ∂ν = Uniform_kap i j (∫ x, f x ∂ν) := by
  rcases Uniform_kap_cases i j with h | h
  · simp [h]
  · simp only [h, Complex.star_def]
    exact integral_conj

private lemma Uniform_key_cases {D N : ℕ} (i j : Idx D N) :
    (Uniform_key i j).val = (i, j) ∨ (Uniform_key i j).val = (j, i) := by
  by_cases h : toLex i ≤ toLex j <;> simp [Uniform_key, h]

private lemma Uniform_key_ne {D N : ℕ} {i j : Idx D N} (hij : i ≠ j) :
    (Uniform_key i j).val.1 ≠ (Uniform_key i j).val.2 := by
  rcases Uniform_key_cases i j with h | h <;> rw [h]
  · simpa using hij
  · simpa using hij.symm

private lemma Uniform_varProf_key (D N : ℕ) (θ : ℝ) (i j : Idx D N) :
    varProf D N θ (Uniform_key i j).val.1 (Uniform_key i j).val.2 = varProf D N θ i j := by
  rcases Uniform_key_cases i j with h | h <;> rw [h]
  have : (j.1 = i.1) ↔ (i.1 = j.1) := eq_comm
  simp [varProf, this]

private lemma Uniform_measurable_arr (D N : ℕ) :
    Measurable (Uniform_arr : (Uniform_Ix D N → ℂ) → Idx D N → Idx D N → ℂ) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  change Measurable fun ω : Uniform_Ix D N → ℂ => Uniform_arr ω i j
  by_cases h : toLex i ≤ toLex j
  · have : (fun ω : Uniform_Ix D N → ℂ => Uniform_arr ω i j) = fun ω => ω ⟨(i, j), h⟩ :=
      funext fun ω => Uniform_arr_of_le ω h
    rw [this]
    exact measurable_pi_apply _
  · have : (fun ω : Uniform_Ix D N → ℂ => Uniform_arr ω i j) =
        fun ω => star (ω ⟨(j, i), (not_le.mp h).le⟩) :=
      funext fun ω => Uniform_arr_of_not_le ω h
    rw [this]
    exact (continuous_star (R := ℂ)).measurable.comp (measurable_pi_apply _)

/-- The set of Hermitian arrays is measurable. -/
private lemma Uniform_measurableSet_herm (D N : ℕ) :
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

/-- Independence of the family `g q ∘ e` under `P` gives independence of `g` under the image law
`P.map e`. -/
private lemma Uniform_iIndepFun_map {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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

/-! ### The product law of the entries -/

/-- The data of one entry of the padded array: a probability law on `ℂ`, with all moments, mean
zero, `E|z|² = (S_θ)_{ab}`, `E z² = 0` for `a ≠ b`, `E|z|^p ≤ C_p N^{-p/2}`, and real almost surely
on the diagonal. -/
private structure Uniform_Ent (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (a b : Idx D N) (ν : Measure ℂ) :
    Prop where
  prob : IsProbabilityMeasure ν
  integrable : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) ν
  mean : ∫ z, z ∂ν = 0
  var : ∫ z, ‖z‖ ^ 2 ∂ν = varProf D N θ a b
  pseudo : a ≠ b → ∫ z, z ^ 2 ∂ν = 0
  moments : ∀ p : ℕ, ∫ z, ‖z‖ ^ p ∂ν ≤ C p * (N : ℝ) ^ (-((p : ℝ) / 2))
  real : a = b → ∀ᵐ z ∂ν, star z = z

/-- Integrals of a continuous function of the entry `(i, j)` against the law of the array
`Uniform_arr` under the product law. -/
private lemma Uniform_integral_entry {D N : ℕ} (ν : Uniform_Ix D N → Measure ℂ)
    [∀ q, IsProbabilityMeasure (ν q)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Idx D N) (F : ℂ → E) (hF : Continuous F) :
    ∫ h, F (h i j) ∂((Measure.pi ν).map Uniform_arr) =
      ∫ x, F (Uniform_kap i j x) ∂(ν (Uniform_key i j)) := by
  have hF' : Continuous fun h : Idx D N → Idx D N → ℂ => F (h i j) :=
    hF.comp ((continuous_apply j).comp (continuous_apply i))
  have hk : Continuous fun x => F (Uniform_kap i j x) := hF.comp (Uniform_continuous_kap i j)
  rw [integral_map (Uniform_measurable_arr D N).aemeasurable hF'.aestronglyMeasurable,
    ← (measurePreserving_eval ν (Uniform_key i j)).map_eq,
    integral_map (measurable_pi_apply _).aemeasurable hk.aestronglyMeasurable]
  rfl

/-- Integrability of a continuous function of the entry `(i, j)`. -/
private lemma Uniform_integrable_entry {D N : ℕ} (ν : Uniform_Ix D N → Measure ℂ)
    [∀ q, IsProbabilityMeasure (ν q)] (i j : Idx D N) (F : ℂ → ℝ) (hF : Continuous F)
    (hi : Integrable (fun x => F (Uniform_kap i j x)) (ν (Uniform_key i j))) :
    Integrable (fun h : Idx D N → Idx D N → ℂ => F (h i j)) ((Measure.pi ν).map Uniform_arr) := by
  have hF' : Continuous fun h : Idx D N → Idx D N → ℂ => F (h i j) :=
    hF.comp ((continuous_apply j).comp (continuous_apply i))
  refine (integrable_map_measure (g := fun h : Idx D N → Idx D N → ℂ => F (h i j))
    hF'.aestronglyMeasurable (Uniform_measurable_arr D N).aemeasurable).mpr ?_
  exact (measurePreserving_eval ν (Uniform_key i j)).integrable_comp_of_integrable
    (g := fun x => F (Uniform_kap i j x)) hi

/-- A product of entry laws satisfying the entry conditions, completed to a Hermitian array by
conjugation, is a member of `LLClass`. -/
private lemma Uniform_class_of_ent (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (ν : Uniform_Ix D N → Measure ℂ)
    (hν : ∀ q, Uniform_Ent D N C θ q.val.1 q.val.2 (ν q)) :
    LLClass D N C θ ((Measure.pi ν).map Uniform_arr) := by
  have : ∀ q, IsProbabilityMeasure (ν q) := fun q => (hν q).prob
  have hm : Measurable (Uniform_arr : (Uniform_Ix D N → ℂ) → Idx D N → Idx D N → ℂ) :=
    Uniform_measurable_arr D N
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hreal : ∀ᵐ ω ∂(Measure.pi ν), ∀ i : Idx D N,
        star (ω ⟨(i, i), le_rfl⟩) = ω ⟨(i, i), le_rfl⟩ :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval ν (⟨(i, i), le_rfl⟩ : Uniform_Ix D N)).quasiMeasurePreserving.ae
          (p := fun z : ℂ => star z = z) ((hν _).real rfl)
    rw [ae_map_iff hm.aemeasurable (Uniform_measurableSet_herm D N)]
    refine hreal.mono fun ω hω => ?_
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rcases lt_trichotomy (toLex i) (toLex j) with hlt | heq | hgt
    · rw [Uniform_arr_of_le ω hlt.le, Uniform_arr_of_not_le ω (not_le.mpr hlt), star_star]
    · have hij : i = j := toLex.injective heq
      subst hij
      rw [Uniform_arr_of_le ω le_rfl]
      exact hω i
    · rw [Uniform_arr_of_le ω hgt.le, Uniform_arr_of_not_le ω (not_le.mpr hgt)]
  · refine Uniform_iIndepFun_map hm
      (g := fun (q : Uniform_Ix D N) (h : Idx D N → Idx D N → ℂ) => h q.val.1 q.val.2)
      (fun q => (measurable_pi_apply q.val.2).comp (measurable_pi_apply q.val.1)) ?_
    have e : (fun (q : Uniform_Ix D N) (ω : Uniform_Ix D N → ℂ) =>
        Uniform_arr ω q.val.1 q.val.2) = fun q ω => ω q :=
      funext fun q => funext fun ω => Uniform_arr_of_le ω q.property
    have hind : iIndepFun (fun (q : Uniform_Ix D N) (ω : Uniform_Ix D N → ℂ) => ω q)
        (Measure.pi ν) :=
      iIndepFun_pi (μ := ν) (X := fun _ (x : ℂ) => x) (fun _ => measurable_id.aemeasurable)
    change iIndepFun (fun (q : Uniform_Ix D N) (ω : Uniform_Ix D N → ℂ) =>
      Uniform_arr ω q.val.1 q.val.2) (Measure.pi ν)
    rw [e]
    exact hind
  · intro p i j
    refine Uniform_integrable_entry ν i j (fun z : ℂ => ‖z‖ ^ p) (continuous_norm.pow p) ?_
    simp only [Uniform_norm_kap]
    exact (hν _).integrable p
  · intro i j
    refine (Uniform_integral_entry ν i j (fun z : ℂ => z) continuous_id).trans ?_
    rw [Uniform_integral_kap i j _ (fun x => x), (hν _).mean, Uniform_kap_zero]
  · intro i j
    refine (Uniform_integral_entry ν i j (fun z : ℂ => ‖z‖ ^ 2) (continuous_norm.pow 2)).trans ?_
    simp only [Uniform_norm_kap]
    rw [(hν _).var, Uniform_varProf_key]
  · intro i j hij
    refine (Uniform_integral_entry ν i j (fun z : ℂ => z ^ 2) (continuous_pow 2)).trans ?_
    simp only [Uniform_kap_sq]
    rw [Uniform_integral_kap i j _ (fun x => x ^ 2), (hν _).pseudo (Uniform_key_ne hij),
      Uniform_kap_zero]
  · intro p i j
    refine (Uniform_integral_entry ν i j (fun z : ℂ => ‖z‖ ^ p) (continuous_norm.pow p)).trans_le ?_
    simp only [Uniform_norm_kap]
    exact (hν _).moments p

/-! ### Rescaling one entry type -/

/-- The rescaling factor `√(N₁/N)`. -/
private def Uniform_c (N₁ N : ℕ) : ℝ := Real.sqrt ((N₁ : ℝ) / N)

private lemma Uniform_c_nonneg (N₁ N : ℕ) : 0 ≤ Uniform_c N₁ N := Real.sqrt_nonneg _

private lemma Uniform_c_sq (N₁ N : ℕ) : Uniform_c N₁ N ^ 2 = (N₁ : ℝ) / N :=
  Real.sq_sqrt (by positivity)

private lemma Uniform_c_pow {N₁ N : ℕ} (hN₁ : 0 < N₁) (hN : 0 < N) (k : ℕ) :
    Uniform_c N₁ N ^ k * (N₁ : ℝ) ^ (-((k : ℝ) / 2)) = (N : ℝ) ^ (-((k : ℝ) / 2)) := by
  have h1 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have h2 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : Uniform_c N₁ N ^ k = ((N₁ : ℝ) / N) ^ ((k : ℝ) / 2) := by
    rw [Uniform_c, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [e, Real.div_rpow h1.le h2.le, Real.rpow_neg h1.le, Real.rpow_neg h2.le]
  have : (0 : ℝ) < (N₁ : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos h1 _
  field_simp

private lemma Uniform_norm_scale (N₁ N : ℕ) (z : ℂ) :
    ‖(Uniform_c N₁ N : ℂ) * z‖ = Uniform_c N₁ N * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Uniform_c_nonneg N₁ N)]

/-- The representative pair at size `N₁` of the entry type of `(a, b)` at size `N`: diagonal,
same block off the diagonal, or off block (the block indices of `a` and `b` are kept). -/
private def Uniform_rep {D N₁ N : ℕ} (hN₁ : 2 ≤ N₁) (a b : Idx D N) : Idx D N₁ × Idx D N₁ :=
  if a = b then ((a.1, ⟨0, by omega⟩), (a.1, ⟨0, by omega⟩))
  else if a.1 = b.1 then ((a.1, ⟨0, by omega⟩), (a.1, ⟨1, by omega⟩))
  else ((a.1, ⟨0, by omega⟩), (b.1, ⟨0, by omega⟩))

private lemma Uniform_rep_fst {D N₁ N : ℕ} (hN₁ : 2 ≤ N₁) (a b : Idx D N) :
    (Uniform_rep hN₁ a b).1.1 = a.1 := by
  unfold Uniform_rep
  split_ifs <;> rfl

private lemma Uniform_rep_snd {D N₁ N : ℕ} (hN₁ : 2 ≤ N₁) (a b : Idx D N) :
    (Uniform_rep hN₁ a b).2.1 = b.1 := by
  unfold Uniform_rep
  split_ifs with h1 h2
  · simp [h1]
  · exact h2
  · rfl

private lemma Uniform_rep_diag {D N₁ N : ℕ} (hN₁ : 2 ≤ N₁) (a : Idx D N) :
    (Uniform_rep hN₁ a a).2 = (Uniform_rep hN₁ a a).1 := by
  simp [Uniform_rep]

private lemma Uniform_rep_ne {D N₁ N : ℕ} (hN₁ : 2 ≤ N₁) {a b : Idx D N} (hab : a ≠ b) :
    (Uniform_rep hN₁ a b).1 ≠ (Uniform_rep hN₁ a b).2 := by
  unfold Uniform_rep
  split_ifs with h1 h2
  · exact absurd h1 hab
  · intro h
    have := congrArg (fun p : Idx D N₁ => (p.2 : ℕ)) h
    simp at this
  · intro h
    exact h2 (by simpa using congrArg (fun p : Idx D N₁ => p.1) h)

/-- The law of the rescaled representative entry: the image of `μ₁` under
`h ↦ √(N₁/N) h_{rs}`, for the representative pair `(r, s)` of the type of `(a, b)`. -/
private def Uniform_nu {D N₁ : ℕ} (hN₁ : 2 ≤ N₁) (N : ℕ)
    (μ₁ : Measure (Idx D N₁ → Idx D N₁ → ℂ)) (a b : Idx D N) : Measure ℂ :=
  μ₁.map fun h => (Uniform_c N₁ N : ℂ) *
    h (Uniform_rep hN₁ a b).1 (Uniform_rep hN₁ a b).2

/-- The rescaled representative entry satisfies the entry conditions at size `N`. -/
private lemma Uniform_Ent_nu (D N₁ N : ℕ) (hN₁ : 2 ≤ N₁) (C : ℕ → ℝ) (θ : ℝ)
    (μ₁ : Measure (Idx D N₁ → Idx D N₁ → ℂ)) (h : LLClass D N₁ C θ μ₁) (a b : Idx D N) :
    Uniform_Ent D N C θ a b (Uniform_nu hN₁ N μ₁ a b) := by
  have hD : 0 < D := Fin.pos a.1
  have hN : 0 < N := Fin.pos a.2
  have hN₁' : 0 < N₁ := by omega
  have hc0 := Uniform_c_nonneg N₁ N
  have hg : Measurable fun h₁ : Idx D N₁ → Idx D N₁ → ℂ =>
      (Uniform_c N₁ N : ℂ) * h₁ (Uniform_rep hN₁ a b).1 (Uniform_rep hN₁ a b).2 :=
    measurable_const.mul ((measurable_pi_apply _).comp (measurable_pi_apply _))
  have := h.prob
  have hint : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E), Continuous F →
      ∫ z, F z ∂(Uniform_nu hN₁ N μ₁ a b) = ∫ h₁, F ((Uniform_c N₁ N : ℂ) *
        h₁ (Uniform_rep hN₁ a b).1 (Uniform_rep hN₁ a b).2) ∂μ₁ :=
    fun F hF => integral_map hg.aemeasurable hF.aestronglyMeasurable
  refine ⟨inferInstanceAs (IsProbabilityMeasure (μ₁.map _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    have hcp : Continuous fun z : ℂ => ‖z‖ ^ p := continuous_norm.pow p
    refine (integrable_map_measure (g := fun z : ℂ => ‖z‖ ^ p) hcp.aestronglyMeasurable
      hg.aemeasurable).mpr ?_
    simp only [Function.comp_def, Uniform_norm_scale, mul_pow]
    exact (h.integrable p _ _).const_mul _
  · rw [hint (fun z : ℂ => z) continuous_id, integral_const_mul, h.mean, mul_zero]
  · rw [hint (fun z : ℂ => ‖z‖ ^ 2) (continuous_norm.pow 2)]
    simp only [Uniform_norm_scale, mul_pow]
    rw [integral_const_mul, h.var]
    unfold varProf
    rw [Uniform_rep_fst, Uniform_rep_snd, Uniform_c_sq]
    split_ifs
    · field_simp
    · field_simp
      ring
  · intro hab
    rw [hint (fun z : ℂ => z ^ 2) (continuous_pow 2)]
    simp only [mul_pow]
    rw [integral_const_mul, h.pseudo _ _ (Uniform_rep_ne hN₁ hab), mul_zero]
  · intro p
    rw [hint (fun z : ℂ => ‖z‖ ^ p) (continuous_norm.pow p)]
    simp only [Uniform_norm_scale, mul_pow]
    rw [integral_const_mul]
    calc Uniform_c N₁ N ^ p * _ ≤ Uniform_c N₁ N ^ p * (C p * (N₁ : ℝ) ^ (-((p : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (h.moments p _ _) (pow_nonneg hc0 p)
      _ = C p * (N : ℝ) ^ (-((p : ℝ) / 2)) := by
          rw [← Uniform_c_pow hN₁' hN p]
          ring
  · intro hab
    subst hab
    have hs : MeasurableSet {z : ℂ | star z = z} :=
      (isClosed_eq continuous_star continuous_id).measurableSet
    refine (ae_map_iff (p := fun z : ℂ => star z = z) hg.aemeasurable hs).mpr ?_
    refine h.herm.mono fun h₁ hh => ?_
    rw [Uniform_rep_diag]
    have h2 := hh.apply (Uniform_rep hN₁ a a).1 (Uniform_rep hN₁ a a).1
    simp only [Matrix.of_apply] at h2
    change star ((Uniform_c N₁ N : ℂ) * _) = (Uniform_c N₁ N : ℂ) * _
    rw [star_mul', h2, Complex.star_def, Complex.conj_ofReal]

/-- Padding of the class: a member at size `N₁ ≥ 2` gives a member at every size `N` with the same
`θ` and the same moment constants (each entry type rescaled by `√(N₁/N)`, independent entries). -/
theorem llClass_pad (D N₁ : ℕ) (hN₁ : 2 ≤ N₁) (C : ℕ → ℝ) (θ : ℝ)
    (μ₁ : Measure (Idx D N₁ → Idx D N₁ → ℂ)) (h : LLClass D N₁ C θ μ₁) (N : ℕ) :
    ∃ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ :=
  ⟨_, Uniform_class_of_ent D N C θ (fun q => Uniform_nu hN₁ N μ₁ q.val.1 q.val.2)
    fun q => Uniform_Ent_nu D N₁ N hN₁ C θ μ₁ h q.val.1 q.val.2⟩

/-- From sequences to uniform statements: if every sequence of members eventually avoids `bad`, and
a member at one size `N₁ ≥ 2` gives members at every size, then `bad` fails for every member at
every large size. -/
theorem uniform_of_seq {X : ℕ → Type*} (Cl : ∀ N, Set (X N)) (bad : ∀ N, X N → Prop)
    (hpad : ∀ N₁ : ℕ, 2 ≤ N₁ → (Cl N₁).Nonempty → ∀ N, (Cl N).Nonempty)
    (hseq : ∀ x : ∀ N, X N, (∀ N, x N ∈ Cl N) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ¬ bad N (x N)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x ∈ Cl N, ¬ bad N x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨N₁, hN₁, x₁, hx₁, hb₁⟩ := hcon 2
  have hne : ∀ N, (Cl N).Nonempty := hpad N₁ hN₁ ⟨x₁, hx₁⟩
  let y : ∀ N, X N := fun N =>
    if hN : ∃ x ∈ Cl N, bad N x then Classical.choose hN else (hne N).some
  have hy : ∀ N, y N ∈ Cl N := fun N => by
    by_cases hN : ∃ x ∈ Cl N, bad N x
    · simp only [y, hN, ↓reduceDIte]
      exact (Classical.choose_spec hN).1
    · simp only [y, hN, ↓reduceDIte]
      exact (hne N).some_mem
  obtain ⟨N₀, hN₀⟩ := hseq y hy
  obtain ⟨N, hN, x, hx, hb⟩ := hcon N₀
  have hbad : ∃ x ∈ Cl N, bad N x := ⟨x, hx, hb⟩
  refine hN₀ N hN ?_
  simp only [y, hbad, ↓reduceDIte]
  exact (Classical.choose_spec hbad).2

end RBMTransitionEdge

end
