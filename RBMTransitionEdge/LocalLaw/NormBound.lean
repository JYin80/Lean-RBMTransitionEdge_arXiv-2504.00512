module

public import RBMTransitionEdge.LocalLaw.Class

@[expose] public section

/-!
# The norm of the noise

Trace moments of a member of the class `LLClass` and the bound `‖H′‖ ≤ N^{δ₁}` outside an event of
probability `N^{-D'}`, which exclude eigenvalues far from the spectrum in Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The trace of a power of a Hermitian matrix is the sum of the powers of its eigenvalues. -/
private lemma NormBound_trace_pow_herm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : ℕ) :
    (A ^ m).trace = ((∑ j, hA.eigenvalues j ^ m : ℝ) : ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    diagonal_pow, trace_diagonal]
  simp

set_option synthInstance.maxHeartbeats 400000 in
-- The instances `CompleteSpace` and `HasSummableGeomSeries` for the algebra of operators on
-- `EuclideanSpace ℂ n` need a larger search budget than the default.
/-- A nonempty Hermitian matrix has an eigenvalue of absolute value `‖A‖`. -/
private lemma NormBound_opNorm_eq_eig {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : ∃ j, opNorm A = |hA.eigenvalues j| := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) A with hT
  have hsa : IsSelfAdjoint T := by
    have : IsSelfAdjoint A := hA
    exact this.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n))
  have hrad := hsa.spectralRadius_eq_nnnorm
  obtain ⟨k, hk, hkn⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  rw [hT, AlgEquiv.spectrum_eq] at hk
  rw [hA.spectrum_eq_image_range] at hk
  obtain ⟨-, ⟨j, rfl⟩, rfl⟩ := hk
  refine ⟨j, ?_⟩
  rw [hrad] at hkn
  have h2 := congrArg ENNReal.toReal hkn
  simp only [ENNReal.coe_toReal, coe_nnnorm] at h2
  unfold opNorm
  rw [← hT]
  rw [← h2]
  simp

/-- The entries of a matrix power are sums over walks. -/
private lemma NormBound_pow_apply {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (m : ℕ) (i j : n) :
    (A ^ m) i j = ∑ w : Fin (m + 1) → n,
      if w 0 = i ∧ w (Fin.last m) = j then ∏ t : Fin m, A (w t.castSucc) (w t.succ) else 0 := by
  induction m generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    simp only [Fin.last_zero, Finset.univ_eq_empty, Finset.prod_empty]
    rw [← (Equiv.funUnique (Fin 1) n).symm.sum_comp]
    by_cases h : i = j
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      refine (Finset.sum_eq_zero fun x _ => ?_).symm
      have hx : ¬ ((Equiv.funUnique (Fin 1) n).symm x 0 = i ∧
          (Equiv.funUnique (Fin 1) n).symm x 0 = j) := fun h12 => h (h12.1.symm.trans h12.2)
      simp only [hx, ↓reduceIte]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => n)).sum_comp]
    rw [Fintype.sum_prod_type]
    have hc : ∀ (x : n) (y : Fin (m + 1) → n),
        (Fin.consEquiv (fun _ : Fin (m + 2) => n)) (x, y) = Fin.cons x y := fun x y => rfl
    simp only [hc, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ, Fin.castSucc_zero]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hl : ∀ (x : n) (y : Fin (m + 1) → n), (Fin.cons x y : Fin (m + 2) → n) (Fin.last (m + 1)) =
        y (Fin.last m) := fun x y => by rw [← Fin.succ_last, Fin.cons_succ]
    have hp : ∀ (x : n) (y : Fin (m + 1) → n), ∏ t : Fin m, A ((Fin.cons x y : Fin (m + 2) → n)
        t.succ.castSucc) (y t.succ) = ∏ t : Fin m, A (y t.castSucc) (y t.succ) := fun x y =>
      Finset.prod_congr rfl fun t _ => by rw [← Fin.succ_castSucc, Fin.cons_succ]
    simp only [hl, hp]
    rw [Finset.sum_comm (s := Finset.univ (α := n))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (y 0), Finset.sum_eq_single i]
    · by_cases hj : y (Fin.last m) = j <;> simp [hj]
    · intro b _ hb
      simp [hb]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp

/-- The trace of a matrix power is the sum over closed walks. -/
private lemma NormBound_trace_pow_walk {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (m : ℕ) :
    (A ^ m).trace = ∑ w : Fin (m + 1) → n,
      if w 0 = w (Fin.last m) then ∏ t : Fin m, A (w t.castSucc) (w t.succ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, NormBound_pow_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single (w 0)]
  · by_cases h : w 0 = w (Fin.last m)
    · simp [h]
    · have h' : ¬ w (Fin.last m) = w 0 := fun e => h e.symm
      simp [h, h']
  · intro b _ hb
    simp [hb.symm]
  · simp

/-- The independent coordinates: ordered pairs `(a, b)` with `a ≤ b` in the lexicographic order. -/
private abbrev NormBound_Q (D N : ℕ) := {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}

/-- The ordered pair carrying the unordered pair `{a, b}`. -/
private def NormBound_sortQ {D N : ℕ} (a b : Idx D N) : NormBound_Q D N :=
  if h : toLex a ≤ toLex b then ⟨(a, b), h⟩ else ⟨(b, a), (not_le.mp h).le⟩

/-- The two ends of the ordered pair carrying `{a, b}` are `a` and `b`, in some order. -/
private lemma NormBound_sortQ_ends {D N : ℕ} (a b : Idx D N) :
    ((NormBound_sortQ a b).val.1 = a ∧ (NormBound_sortQ a b).val.2 = b) ∨
      ((NormBound_sortQ a b).val.1 = b ∧ (NormBound_sortQ a b).val.2 = a) := by
  unfold NormBound_sortQ
  split_ifs <;> simp

/-- Along a walk, the number of distinct vertices is at most one more than the number of distinct
unordered pairs used by its steps. -/
private lemma NormBound_card_image_le {D N : ℕ} (w : ℕ → Idx D N) (m : ℕ) :
    ((Finset.range (m + 1)).image w).card ≤
      1 + ((Finset.range m).image fun t => NormBound_sortQ (w t) (w (t + 1))).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : (Finset.range (m + 1 + 1)).image w =
        insert (w (m + 1)) ((Finset.range (m + 1)).image w) := by
      rw [Finset.range_add_one (n := m + 1), Finset.image_insert]
    have e2 : (Finset.range (m + 1)).image (fun t => NormBound_sortQ (w t) (w (t + 1))) =
        insert (NormBound_sortQ (w m) (w (m + 1)))
          ((Finset.range m).image fun t => NormBound_sortQ (w t) (w (t + 1))) := by
      rw [Finset.range_add_one (n := m), Finset.image_insert]
    rw [e1, e2]
    by_cases hmem : w (m + 1) ∈ (Finset.range (m + 1)).image w
    · rw [Finset.insert_eq_of_mem hmem]
      exact ih.trans (by gcongr; exact Finset.subset_insert _ _)
    · have hnew : NormBound_sortQ (w m) (w (m + 1)) ∉
          (Finset.range m).image fun t => NormBound_sortQ (w t) (w (t + 1)) := by
        intro hq
        obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hq
        have h1 := congrArg (fun q : NormBound_Q D N => q.val.1) hteq
        have h2 := congrArg (fun q : NormBound_Q D N => q.val.2) hteq
        have hr := Finset.mem_range.mp ht
        have hwt : w t ∈ (Finset.range (m + 1)).image w :=
          Finset.mem_image_of_mem w (Finset.mem_range.mpr (by omega))
        have hwt1 : w (t + 1) ∈ (Finset.range (m + 1)).image w :=
          Finset.mem_image_of_mem w (Finset.mem_range.mpr (by omega))
        apply hmem
        rcases NormBound_sortQ_ends (w t) (w (t + 1)) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rcases NormBound_sortQ_ends (w m) (w (m + 1)) with ⟨f1, f2⟩ | ⟨f1, f2⟩
        all_goals grind
      rw [Finset.card_insert_of_notMem hmem, Finset.card_insert_of_notMem hnew]
      omega


/-- The same count for walks given as `Fin (m + 1) → V`. -/
private lemma NormBound_card_image_le_fin {D N m : ℕ} (w : Fin (m + 1) → Idx D N) :
    (Finset.univ.image w).card ≤
      1 + (Finset.univ.image
        (fun t : Fin m => NormBound_sortQ (w t.castSucc) (w t.succ))).card := by
  set wn : ℕ → Idx D N := fun t => w ⟨min t m, by omega⟩ with hwn
  have h := NormBound_card_image_le wn m
  have e1 : (Finset.range (m + 1)).image wn = Finset.univ.image w := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i.val, i.isLt, ?_⟩
      have : (⟨min i.val m, by omega⟩ : Fin (m + 1)) = i := Fin.ext (by simp; omega)
      simp only [hwn, this]
  have e2 : (Finset.range m).image (fun t => NormBound_sortQ (wn t) (wn (t + 1))) ⊆
      Finset.univ.image (fun t : Fin m => NormBound_sortQ (w t.castSucc) (w t.succ)) := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    have ht' := Finset.mem_range.mp ht
    refine Finset.mem_image.mpr ⟨⟨t, ht'⟩, Finset.mem_univ _, ?_⟩
    have a1 : (⟨min t m, by omega⟩ : Fin (m + 1)) = (⟨t, ht'⟩ : Fin m).castSucc :=
      Fin.ext (by simp; omega)
    have a2 : (⟨min (t + 1) m, by omega⟩ : Fin (m + 1)) = (⟨t, ht'⟩ : Fin m).succ :=
      Fin.ext (by simp; omega)
    simp only [hwn, a1, a2]
  rw [e1] at h
  exact h.trans (by gcongr)

/-- The number of sequences of length `m` in `V` with at most `r` distinct values is at most
`r ^ m * |V| ^ r`. -/
private lemma NormBound_card_few_values {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (m r : ℕ) :
    (Finset.univ.filter fun w : Fin m → V => (Finset.univ.image w).card ≤ r).card ≤
      r ^ m * (Fintype.card V) ^ r := by
  have hsub : (Finset.univ.filter fun w : Fin m → V => (Finset.univ.image w).card ≤ r) ⊆
      (Finset.univ : Finset ((Fin m → Fin r) × (Fin r → V))).image
        (fun p => p.2 ∘ p.1) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hcard : Fintype.card (↥(Finset.univ.image w)) ≤ Fintype.card (Fin r) := by
      rw [Fintype.card_coe, Fintype.card_fin]
      exact hw.2
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine Finset.mem_image.mpr ⟨(fun t => g ⟨w t, Finset.mem_image_of_mem w (Finset.mem_univ t)⟩,
      Function.extend g (fun x : ↥(Finset.univ.image w) => x.val)
        (fun _ => Classical.arbitrary V)), Finset.mem_univ _, ?_⟩
    funext t
    simp only [Function.comp_apply]
    exact g.injective.extend_apply _ _ _
  calc _ ≤ ((Finset.univ : Finset ((Fin m → Fin r) × (Fin r → V))).image
        (fun p => p.2 ∘ p.1)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin m → Fin r) × (Fin r → V))).card := Finset.card_image_le
    _ = r ^ m * (Fintype.card V) ^ r := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun]
      simp only [Fintype.card_fin]


/-- If every unordered pair is used `0` or at least `2` times by the `2k` steps of a walk, the
walk uses at most `k` distinct pairs. -/
private lemma NormBound_pairs_card_le {D N k : ℕ} (w : Fin (2 * k + 1) → Idx D N)
    (hgood : ∀ q : NormBound_Q D N, (Finset.univ.filter (fun t : Fin (2 * k) =>
          NormBound_sortQ (w t.castSucc) (w t.succ) = q)).card ≠ 1) :
    (Finset.univ.image
      (fun t : Fin (2 * k) => NormBound_sortQ (w t.castSucc) (w t.succ))).card ≤ k := by
  set p : Fin (2 * k) → NormBound_Q D N := fun t => NormBound_sortQ (w t.castSucc) (w t.succ)
    with hp
  have hge : ∀ q ∈ Finset.univ.image p,
      2 ≤ (Finset.univ.filter (fun t : Fin (2 * k) => p t = q)).card := by
    intro q hq
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hq
    have h2 : 0 < (Finset.univ.filter (fun t : Fin (2 * k) => p t = q)).card :=
      Finset.card_pos.mpr ⟨t, by simp [ht]⟩
    have : (Finset.univ.filter (fun t : Fin (2 * k) => p t = q)).card ≠ 1 := hgood q
    omega
  have hsum : ∑ q ∈ Finset.univ.image p,
      (Finset.univ.filter (fun t : Fin (2 * k) => p t = q)).card = 2 * k := by
    have := Finset.card_eq_sum_card_fiberwise (f := p)
      (s := (Finset.univ : Finset (Fin (2 * k)))) (t := Finset.univ.image p)
      (fun t _ => Finset.mem_image_of_mem p (Finset.mem_univ t))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have := Finset.card_nsmul_le_sum (Finset.univ.image p)
    (fun q => (Finset.univ.filter (fun t : Fin (2 * k) => p t = q)).card) 2 hge
  rw [hsum, smul_eq_mul] at this
  omega

/-- A walk of `2k` steps that uses every unordered pair `0` or at least `2` times visits at most
`k + 1` distinct vertices. -/
private lemma NormBound_good_card {D N k : ℕ} (w : Fin (2 * k + 1) → Idx D N)
    (hgood : ∀ q : NormBound_Q D N, (Finset.univ.filter (fun t : Fin (2 * k) =>
          NormBound_sortQ (w t.castSucc) (w t.succ) = q)).card ≠ 1) :
    (Finset.univ.image w).card ≤ k + 1 := by
  have h1 := NormBound_card_image_le_fin w
  have h2 := NormBound_pairs_card_le w hgood
  omega

/-- The upper-triangular representative of an array: the entry `(a, b)` with `b < a` is the
conjugate of the entry `(b, a)`. -/
private def NormBound_U {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a b : Idx D N) : ℂ :=
  if toLex a ≤ toLex b then h a b else starRingEnd ℂ (h b a)

/-- The map applied to the coordinate of the pair `{a, b}` to recover the entry `(a, b)`. -/
private def NormBound_phi {D N : ℕ} (a b : Idx D N) : ℂ → ℂ :=
  if toLex a ≤ toLex b then id else starRingEnd ℂ

/-- The map `NormBound_phi a b` is the identity or the complex conjugation. -/
private lemma NormBound_phi_cases {D N : ℕ} (a b : Idx D N) :
    NormBound_phi a b = id ∨ NormBound_phi a b = starRingEnd ℂ := by
  unfold NormBound_phi
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The entry `(a, b)` of the representative is a function of the coordinate of `{a, b}`. -/
private lemma NormBound_U_eq {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a b : Idx D N) :
    NormBound_U h a b = NormBound_phi a b
      (h (NormBound_sortQ a b).val.1 (NormBound_sortQ a b).val.2) := by
  unfold NormBound_U NormBound_phi NormBound_sortQ
  by_cases hab : toLex a ≤ toLex b <;> simp [hab]

variable {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}

/-- A Hermitian array agrees with its upper-triangular representative. -/
private lemma NormBound_of_U {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) :
    Matrix.of h = Matrix.of (NormBound_U h) := by
  ext a b
  simp only [Matrix.of_apply, NormBound_U]
  split_ifs with hab
  · rfl
  · exact (hh.apply a b).symm.trans (by simp)

/-- Factorization of the expectation of a walk product over the independent coordinates. -/
private lemma NormBound_integral_walk (hLL : LLClass D N C θ μ) {m : ℕ}
    (w : Fin (m + 1) → Idx D N) :
    ∫ h, ∏ t : Fin m, NormBound_U h (w t.castSucc) (w t.succ) ∂μ =
      ∏ q : NormBound_Q D N, ∫ h, ∏ t ∈ Finset.univ.filter (fun t : Fin m =>
          NormBound_sortQ (w t.castSucc) (w t.succ) = q),
        NormBound_phi (w t.castSucc) (w t.succ) (h q.val.1 q.val.2) ∂μ := by
  have hprob := hLL.prob
  have h1 : ∀ h : Idx D N → Idx D N → ℂ, ∏ t : Fin m, NormBound_U h (w t.castSucc) (w t.succ) =
      ∏ q : NormBound_Q D N, ∏ t ∈ Finset.univ.filter (fun t : Fin m =>
          NormBound_sortQ (w t.castSucc) (w t.succ) = q),
        NormBound_phi (w t.castSucc) (w t.succ) (h q.val.1 q.val.2) := by
    intro h
    rw [← Finset.prod_fiberwise Finset.univ
      (fun t : Fin m => NormBound_sortQ (w t.castSucc) (w t.succ))]
    refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun t ht => ?_
    rw [NormBound_U_eq]
    rw [(Finset.mem_filter.mp ht).2]
  simp_rw [h1]
  refine iIndepFun.integral_fun_prod_comp (X := fun (q : NormBound_Q D N)
    (h : Idx D N → Idx D N → ℂ) => h q.val.1 q.val.2)
    (f := fun q z => ∏ t ∈ Finset.univ.filter (fun t : Fin m =>
          NormBound_sortQ (w t.castSucc) (w t.succ) = q),
        NormBound_phi (w t.castSucc) (w t.succ) z) hLL.indep ?_ ?_
  · intro q
    exact ((measurable_pi_apply _).comp (measurable_pi_apply _)).aemeasurable
  · intro q
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_finsetProd _ fun t _ => ?_
    rcases NormBound_phi_cases (w t.castSucc) (w t.succ) with h | h <;> rw [h]
    · exact continuous_id
    · exact Complex.continuous_conj


/-- Bounds on the expectation of the part of a walk product that lives on one coordinate: a
bound by the moment `C_c N^{-c/2}` of the multiplicity `c`, and vanishing for `c = 1`. -/
private lemma NormBound_factor {ι : Type*} (hLL : LLClass D N C θ μ) (q : NormBound_Q D N)
    (s : Finset ι) (φ : ι → ℂ → ℂ) (hφ : ∀ t ∈ s, φ t = id ∨ φ t = starRingEnd ℂ) :
    ‖∫ h, ∏ t ∈ s, φ t (h q.val.1 q.val.2) ∂μ‖ ≤ C s.card * (N : ℝ) ^ (-((s.card : ℝ) / 2)) ∧
      (s.card = 1 → ∫ h, ∏ t ∈ s, φ t (h q.val.1 q.val.2) ∂μ = 0) := by
  have hn : ∀ t ∈ s, ∀ z, ‖φ t z‖ = ‖z‖ := by
    intro t ht z
    rcases hφ t ht with h | h <;> simp [h]
  constructor
  · refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ h : Idx D N → Idx D N → ℂ,
        ‖∏ t ∈ s, φ t (h q.val.1 q.val.2)‖ = ‖h q.val.1 q.val.2‖ ^ s.card := by
      intro h
      rw [norm_prod, Finset.prod_congr rfl (fun t ht => hn t ht _), Finset.prod_const]
    simp_rw [this]
    exact hLL.moments s.card q.val.1 q.val.2
  · intro hc
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hc
    simp only [Finset.prod_singleton]
    rcases hφ t (Finset.mem_singleton_self t) with h | h <;> rw [h]
    · exact hLL.mean _ _
    · simp only [integral_conj, hLL.mean, map_zero]


/-- The expectation of the product along a walk of `2k` steps vanishes unless every unordered pair
is used `0` or at least `2` times, and is then at most `M^k N^{-k}`. -/
private lemma NormBound_term_bound (hLL : LLClass D N C θ μ) (hN : 1 ≤ N) {k : ℕ} {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ p ≤ 2 * k, C p ≤ M) (w : Fin (2 * k + 1) → Idx D N) :
    ‖∫ h, ∏ t : Fin (2 * k), NormBound_U h (w t.castSucc) (w t.succ) ∂μ‖ ≤
      if (∀ q : NormBound_Q D N, (Finset.univ.filter (fun t : Fin (2 * k) =>
          NormBound_sortQ (w t.castSucc) (w t.succ) = q)).card ≠ 1)
      then M ^ k * (N : ℝ) ^ (-(k : ℝ)) else 0 := by
  have hprob := hLL.prob
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [NormBound_integral_walk hLL w]
  set p : Fin (2 * k) → NormBound_Q D N := fun t => NormBound_sortQ (w t.castSucc) (w t.succ)
    with hp
  set fib : NormBound_Q D N → Finset (Fin (2 * k)) :=
    fun q => Finset.univ.filter (fun t : Fin (2 * k) => p t = q) with hfib
  set img : Finset (NormBound_Q D N) := Finset.univ.image p with himg
  have hI : ∀ q : NormBound_Q D N,
      ‖∫ h, ∏ t ∈ fib q, NormBound_phi (w t.castSucc) (w t.succ) (h q.val.1 q.val.2) ∂μ‖ ≤
        C (fib q).card * (N : ℝ) ^ (-(((fib q).card : ℝ) / 2)) ∧
      ((fib q).card = 1 → ∫ h, ∏ t ∈ fib q,
        NormBound_phi (w t.castSucc) (w t.succ) (h q.val.1 q.val.2) ∂μ = 0) := fun q =>
    NormBound_factor hLL q (fib q) (fun t => NormBound_phi (w t.castSucc) (w t.succ))
      (fun t _ => NormBound_phi_cases _ _)
  have hone : ∀ q ∈ (Finset.univ : Finset (NormBound_Q D N)), q ∉ img →
      ∫ h, ∏ t ∈ fib q, NormBound_phi (w t.castSucc) (w t.succ) (h q.val.1 q.val.2) ∂μ = 1 := by
    intro q _ hq
    have hemp : fib q = ∅ := by
      rw [hfib, Finset.filter_eq_empty_iff]
      intro t _ ht
      exact hq (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
    rw [hemp]
    simp
  rw [← Finset.prod_subset (Finset.subset_univ img) hone]
  have hmem : ∀ q : NormBound_Q D N, q ∈ img ↔ (fib q).Nonempty := by
    intro q
    rw [himg, Finset.mem_image]
    constructor
    · rintro ⟨t, -, ht⟩
      exact ⟨t, by simp [hfib, ht]⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, Finset.mem_univ t, (Finset.mem_filter.mp ht).2⟩
  split_ifs with hgood
  · have hsum : ∑ q ∈ img, (fib q).card = 2 * k := by
      have := Finset.card_eq_sum_card_fiberwise (f := p) (s := (Finset.univ : Finset (Fin (2 * k))))
        (t := img) (fun t _ => Finset.mem_image_of_mem p (Finset.mem_univ t))
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact this.symm
    have himgk : img.card ≤ k := NormBound_pairs_card_le w hgood
    rw [norm_prod]
    calc ∏ q ∈ img, ‖∫ h, ∏ t ∈ fib q, NormBound_phi (w t.castSucc) (w t.succ)
            (h q.val.1 q.val.2) ∂μ‖
        ≤ ∏ q ∈ img, (M * (N : ℝ) ^ (-(((fib q).card : ℝ) / 2))) := by
          refine Finset.prod_le_prod₀ (fun q _ => norm_nonneg _) fun q hq => ?_
          refine (hI q).1.trans ?_
          have hc : (fib q).card ≤ 2 * k := by
            have := Finset.card_filter_le (Finset.univ : Finset (Fin (2 * k)))
              (fun t => p t = q)
            simpa using this
          exact mul_le_mul_of_nonneg_right (hM _ hc) (Real.rpow_nonneg hNpos.le _)
      _ = M ^ img.card * (N : ℝ) ^ (-(k : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_sum_of_pos hNpos]
          congr 2
          rw [Finset.sum_neg_distrib, ← Finset.sum_div]
          have : ∑ q ∈ img, ((fib q).card : ℝ) = 2 * k := by exact_mod_cast hsum
          rw [this]
          ring
      _ ≤ M ^ k * (N : ℝ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 himgk) (Real.rpow_nonneg hNpos.le _)
  · obtain ⟨q, hq⟩ := not_forall.mp hgood
    have hq' : (fib q).card = 1 := not_not.mp hq
    have hqimg : q ∈ img := (hmem q).mpr (Finset.card_pos.mp (by omega))
    rw [norm_prod]
    refine le_of_eq (Finset.prod_eq_zero hqimg ?_)
    rw [(hI q).2 hq', norm_zero]

/-- The norm of an entry of the representative. -/
private lemma NormBound_U_norm (h : Idx D N → Idx D N → ℂ) (a b : Idx D N) :
    ‖NormBound_U h a b‖ = ‖h (NormBound_sortQ a b).val.1 (NormBound_sortQ a b).val.2‖ := by
  rw [NormBound_U_eq]
  rcases NormBound_phi_cases a b with e | e <;> rw [e] <;> simp

/-- An entry of the representative is a measurable function of the array. -/
private lemma NormBound_U_measurable (a b : Idx D N) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => NormBound_U h a b) := by
  have e : (fun h : Idx D N → Idx D N → ℂ => NormBound_U h a b) =
      fun h => NormBound_phi a b
        (h (NormBound_sortQ a b).val.1 (NormBound_sortQ a b).val.2) :=
    funext fun h => NormBound_U_eq h a b
  rw [e]
  have hc : Continuous (NormBound_phi a b) := by
    rcases NormBound_phi_cases a b with e | e <;> rw [e]
    exacts [continuous_id, Complex.continuous_conj]
  exact hc.measurable.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

/-- A product of nonnegative numbers is at most one plus the sum of their `m`-th powers. -/
private lemma NormBound_prod_le {m : ℕ} (x : Fin m → ℝ) (hx : ∀ t, 0 ≤ x t) :
    ∏ t, x t ≤ 1 + ∑ t, x t ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨t0, -, ht0⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
    calc ∏ t, x t ≤ ∏ _t : Fin m, x t0 :=
          Finset.prod_le_prod₀ (fun t _ => hx t) fun t _ => ht0 t (Finset.mem_univ t)
      _ = x t0 ^ m := by simp
      _ ≤ ∑ t, x t ^ m := Finset.single_le_sum (f := fun t => x t ^ m)
          (fun t _ => pow_nonneg (hx t) m) (Finset.mem_univ t0)
      _ ≤ 1 + ∑ t, x t ^ m := by linarith

/-- The product of the entries of the representative along a walk is integrable. -/
private lemma NormBound_integrable_walk (hLL : LLClass D N C θ μ) {m : ℕ}
    (w : Fin (m + 1) → Idx D N) :
    Integrable (fun h => ∏ t : Fin m, NormBound_U h (w t.castSucc) (w t.succ)) μ := by
  have hprob := hLL.prob
  refine Integrable.mono' (g := fun h => 1 + ∑ t : Fin m,
    ‖h (NormBound_sortQ (w t.castSucc) (w t.succ)).val.1
      (NormBound_sortQ (w t.castSucc) (w t.succ)).val.2‖ ^ m) ?_ ?_ ?_
  · have h2 : Integrable (fun h : Idx D N → Idx D N → ℂ => ∑ t : Fin m,
        ‖h (NormBound_sortQ (w t.castSucc) (w t.succ)).val.1
          (NormBound_sortQ (w t.castSucc) (w t.succ)).val.2‖ ^ m) μ :=
      integrable_finsetSum Finset.univ fun t _ => hLL.integrable m _ _
    exact (integrable_const (1 : ℝ)).add h2
  · exact (Finset.measurable_prod _ fun t _ => NormBound_U_measurable _ _).aestronglyMeasurable
  · refine Eventually.of_forall fun h => ?_
    rw [norm_prod]
    simp_rw [NormBound_U_norm]
    exact NormBound_prod_le _ (fun t => norm_nonneg _)

/-- The trace of a power of the representative is integrable. -/
private lemma NormBound_integrable_trace (hLL : LLClass D N C θ μ) (m : ℕ) :
    Integrable (fun h => ((Matrix.of (NormBound_U h)) ^ m).trace) μ := by
  simp_rw [NormBound_trace_pow_walk]
  refine integrable_finsetSum _ fun w _ => ?_
  by_cases hw : w 0 = w (Fin.last m)
  · simpa [hw] using NormBound_integrable_walk hLL w
  · simp [hw]

/-- The trace of an even power of a Hermitian matrix is real and nonnegative. -/
private lemma NormBound_trace_pow_norm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    ‖(A ^ (2 * k)).trace‖ = ((A ^ (2 * k)).trace).re := by
  rw [NormBound_trace_pow_herm hA, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg fun j _ => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) k)

/-- For a Hermitian matrix, `‖A‖^{2k} ≤ tr A^{2k}` (`k ≥ 1`). -/
private lemma NormBound_opNorm_pow_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {k : ℕ} (hk : 0 < k) :
    opNorm A ^ (2 * k) ≤ ‖(A ^ (2 * k)).trace‖ := by
  rw [NormBound_trace_pow_norm hA k, NormBound_trace_pow_herm hA, Complex.ofReal_re]
  rcases isEmpty_or_nonempty n with hn | hn
  · have hA0 : A = 0 := Matrix.ext fun i => isEmptyElim i
    have h0 : opNorm A = 0 := by
      rw [hA0]
      unfold opNorm
      rw [map_zero, norm_zero]
    rw [h0, zero_pow (by omega)]
    simp
  · obtain ⟨j, hj⟩ := NormBound_opNorm_eq_eig hA
    rw [hj, Even.pow_abs ⟨k, by ring⟩]
    exact Finset.single_le_sum (f := fun i => hA.eigenvalues i ^ (2 * k))
      (fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) (Finset.mem_univ j)

/-- The moment bound with explicit constants: `E tr H^{2k} ≤ (k+1)^{2k+1} (DN)^{k+1} M^k N^{-k}`
for `M ≥ 1` dominating `C_p`, `p ≤ 2k`. -/
private lemma NormBound_moment_bound (hLL : LLClass D N C θ μ) [hV : Nonempty (Idx D N)] {k : ℕ}
    {M : ℝ} (hM1 : 1 ≤ M) (hM : ∀ p ≤ 2 * k, C p ≤ M) :
    ∫ h, ‖((Matrix.of h) ^ (2 * k)).trace‖ ∂μ ≤
      ((k : ℝ) + 1) ^ (2 * k + 1) * ((D : ℝ) * N) ^ (k + 1) *
        (M ^ k * (N : ℝ) ^ (-(k : ℝ))) := by
  have hN : 1 ≤ N := hV.some.2.pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set T : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ((Matrix.of (NormBound_U h)) ^ (2 * k)).trace
    with hT
  have hTint : Integrable T μ := NormBound_integrable_trace hLL (2 * k)
  have hae : ∀ᵐ h ∂μ, ‖((Matrix.of h) ^ (2 * k)).trace‖ = (T h).re := by
    filter_upwards [hLL.herm] with h hh
    have e := NormBound_of_U hh
    have h2 := NormBound_trace_pow_norm hh k
    rw [e] at h2 ⊢
    exact h2
  set B : ℝ := M ^ k * (N : ℝ) ^ (-(k : ℝ)) with hB
  have hBnn : 0 ≤ B := by positivity
  have hg : ∀ w : Fin (2 * k + 1) → Idx D N,
      ‖∫ h, (if w 0 = w (Fin.last (2 * k)) then
        ∏ t : Fin (2 * k), NormBound_U h (w t.castSucc) (w t.succ) else 0) ∂μ‖ ≤
      if (Finset.univ.image w).card ≤ k + 1 then B else 0 := by
    intro w
    by_cases hc : w 0 = w (Fin.last (2 * k))
    · simp only [hc, ↓reduceIte]
      refine (NormBound_term_bound hLL hN hM1 hM w).trans ?_
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (NormBound_good_card w h1) h2
      · exact hBnn
      · exact le_rfl
    · simp only [hc, ↓reduceIte, integral_zero, norm_zero]
      split_ifs <;> simp [hBnn]
  calc ∫ h, ‖((Matrix.of h) ^ (2 * k)).trace‖ ∂μ = ∫ h, (T h).re ∂μ := integral_congr_ae hae
    _ = (∫ h, T h ∂μ).re := integral_re hTint
    _ ≤ ‖∫ h, T h ∂μ‖ := Complex.re_le_norm _
    _ = ‖∑ w : Fin (2 * k + 1) → Idx D N, ∫ h, (if w 0 = w (Fin.last (2 * k)) then
          ∏ t : Fin (2 * k), NormBound_U h (w t.castSucc) (w t.succ) else 0) ∂μ‖ := by
        congr 1
        have hint : ∀ w ∈ (Finset.univ : Finset (Fin (2 * k + 1) → Idx D N)),
            Integrable (fun h : Idx D N → Idx D N → ℂ => if w 0 = w (Fin.last (2 * k)) then
              ∏ t : Fin (2 * k), NormBound_U h (w t.castSucc) (w t.succ) else 0) μ := by
          intro w _
          by_cases hc : w 0 = w (Fin.last (2 * k))
          · simpa [hc] using NormBound_integrable_walk hLL w
          · simp [hc]
        simp_rw [hT, NormBound_trace_pow_walk]
        simp only [Matrix.of_apply]
        exact integral_finsetSum _ hint
    _ ≤ ∑ w : Fin (2 * k + 1) → Idx D N, ‖∫ h, (if w 0 = w (Fin.last (2 * k)) then
          ∏ t : Fin (2 * k), NormBound_U h (w t.castSucc) (w t.succ) else 0) ∂μ‖ :=
        norm_sum_le _ _
    _ ≤ ∑ w : Fin (2 * k + 1) → Idx D N, (if (Finset.univ.image w).card ≤ k + 1 then B else 0) :=
        Finset.sum_le_sum fun w _ => hg w
    _ = ((Finset.univ.filter fun w : Fin (2 * k + 1) → Idx D N =>
          (Finset.univ.image w).card ≤ k + 1).card : ℝ) * B := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((k + 1) ^ (2 * k + 1) * (Fintype.card (Idx D N)) ^ (k + 1) : ℕ) : ℝ) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hBnn
        exact_mod_cast NormBound_card_few_values (V := Idx D N) (2 * k + 1) (k + 1)
    _ = ((k : ℝ) + 1) ^ (2 * k + 1) * ((D : ℝ) * N) ^ (k + 1) * B := by
        simp only [Fintype.card_prod, Fintype.card_fin]
        push_cast
        ring

/-- `‖tr H^m‖` is integrable. -/
private lemma NormBound_integrable_norm_trace (hLL : LLClass D N C θ μ) (m : ℕ) :
    Integrable (fun h : Idx D N → Idx D N → ℂ => ‖((Matrix.of h) ^ m).trace‖) μ := by
  refine (NormBound_integrable_trace hLL m).norm.congr ?_
  filter_upwards [hLL.herm] with h hh
  rw [NormBound_of_U hh]

/-- The trace moments of the class: for fixed `k`, `E tr H'^{2k} ≤ K N`, with `K` depending on `D`,
`C` and `k` only. -/
theorem trace_moment_le (D : ℕ) (C : ℕ → ℝ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → ∫ h, ‖((Matrix.of h) ^ (2 * k)).trace‖ ∂μ ≤ K * N := by
  set M : ℝ := 1 + ∑ p ∈ Finset.range (2 * k + 1), |C p| with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ p ∈ Finset.range (2 * k + 1), |C p| := Finset.sum_nonneg fun p _ => abs_nonneg _
    linarith
  have hMC : ∀ p ≤ 2 * k, C p ≤ M := by
    intro p hp
    have h1 : |C p| ≤ ∑ p ∈ Finset.range (2 * k + 1), |C p| :=
      Finset.single_le_sum (f := fun p => |C p|) (fun p _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have h2 := le_abs_self (C p)
    linarith
  refine ⟨((k : ℝ) + 1) ^ (2 * k + 1) * ((D : ℝ) + 1) ^ (k + 1) * M ^ k, by positivity, ?_⟩
  intro N θ μ hLL
  rcases isEmpty_or_nonempty (Idx D N) with hV | hV
  · have h0 : ∀ h : Idx D N → Idx D N → ℂ, ((Matrix.of h) ^ (2 * k)).trace = 0 := fun h => by
      simp [Matrix.trace]
    simp only [h0, norm_zero, integral_zero]
    positivity
  · have hN : 1 ≤ N := hV.some.2.pos
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    refine (NormBound_moment_bound hLL hM1 hMC).trans ?_
    have hrw : (N : ℝ) ^ (-(k : ℝ)) = ((N : ℝ) ^ k)⁻¹ := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_natCast]
    have hD : ((D : ℝ)) ^ (k + 1) ≤ ((D : ℝ) + 1) ^ (k + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg D) (by linarith) _
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    calc ((k : ℝ) + 1) ^ (2 * k + 1) * ((D : ℝ) * N) ^ (k + 1) * (M ^ k * (N : ℝ) ^ (-(k : ℝ)))
        = ((k : ℝ) + 1) ^ (2 * k + 1) * (D : ℝ) ^ (k + 1) * M ^ k * N := by
          rw [hrw, mul_pow, pow_succ (N : ℝ) k]
          field_simp
      _ ≤ ((k : ℝ) + 1) ^ (2 * k + 1) * ((D : ℝ) + 1) ^ (k + 1) * M ^ k * N := by
          gcongr

/-- The norm of the noise: for every `δ₁ > 0`, outside an event of probability `≤ N^{-D'}`,
`‖H'‖ ≤ N^{δ₁}`, uniformly over the class. -/
theorem opNorm_noise_le (D : ℕ) (C : ℕ → ℝ) :
    ∀ δ₁ : ℝ, 0 < δ₁ → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)), LLClass D N C θ μ →
        μ {h | (N : ℝ) ^ δ₁ < opNorm (Matrix.of h)} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro δ₁ hδ D' hD'
  set k : ℕ := ⌈(D' + 2) / (2 * δ₁)⌉₊ with hk
  have hkpos : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have hk2 : D' + 2 ≤ δ₁ * ((2 * k : ℕ) : ℝ) := by
    have := Nat.le_ceil ((D' + 2) / (2 * δ₁))
    rw [div_le_iff₀ (by positivity)] at this
    push_cast
    linarith
  obtain ⟨K, hK, hKb⟩ := trace_moment_le D C k
  refine ⟨⌈K⌉₊ + 1, fun N hN θ μ hLL => ?_⟩
  have hNge : K ≤ N := (Nat.le_ceil K).trans (by exact_mod_cast (Nat.le_succ _).trans hN)
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hprob := hLL.prob
  set f : (Idx D N → Idx D N → ℂ) → ℝ := fun h => ‖((Matrix.of h) ^ (2 * k)).trace‖ with hf
  have hfint : Integrable f μ := NormBound_integrable_norm_trace hLL (2 * k)
  have hf0 : 0 ≤ᵐ[μ] f := Eventually.of_forall fun h => norm_nonneg _
  set ε : ℝ := ((N : ℝ) ^ δ₁) ^ (2 * k) with hε
  have hmark := mul_meas_ge_le_integral_of_nonneg hf0 hfint ε
  have hKN := hKb N θ μ hLL
  have hsub : μ {h | (N : ℝ) ^ δ₁ < opNorm (Matrix.of h)} ≤ μ {h | ε ≤ f h} := by
    refine measure_mono_ae ?_
    filter_upwards [hLL.herm] with h hh hs
    have h1 : ε ≤ opNorm (Matrix.of h) ^ (2 * k) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) (le_of_lt hs) _
    exact h1.trans (NormBound_opNorm_pow_le hh hkpos)
  have hεge : (N : ℝ) ^ (D' + 2) ≤ ε := by
    rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1' hk2
  have hr0 : 0 ≤ μ.real {h | ε ≤ f h} := measureReal_nonneg
  have hmain : μ.real {h | ε ≤ f h} ≤ (N : ℝ) ^ (-D') := by
    have h1 : (N : ℝ) ^ (D' + 2) * μ.real {h | ε ≤ f h} ≤ (N : ℝ) * N := by
      calc (N : ℝ) ^ (D' + 2) * μ.real {h | ε ≤ f h} ≤ ε * μ.real {h | ε ≤ f h} :=
            mul_le_mul_of_nonneg_right hεge hr0
        _ ≤ K * N := hmark.trans hKN
        _ ≤ N * N := mul_le_mul_of_nonneg_right hNge hNpos.le
    rw [Real.rpow_add hNpos, Real.rpow_two] at h1
    rw [Real.rpow_neg hNpos.le]
    have hpos : 0 < (N : ℝ) ^ D' := Real.rpow_pos_of_pos hNpos _
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have h2 : μ.real {h | ε ≤ f h} * (N : ℝ) ^ D' ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hN2
      nlinarith
    calc μ.real {h | ε ≤ f h}
        = μ.real {h | ε ≤ f h} * (N : ℝ) ^ D' * ((N : ℝ) ^ D')⁻¹ := by field_simp
      _ ≤ 1 * ((N : ℝ) ^ D')⁻¹ := by gcongr
      _ = ((N : ℝ) ^ D')⁻¹ := one_mul _
  calc μ {h | (N : ℝ) ^ δ₁ < opNorm (Matrix.of h)} ≤ μ {h | ε ≤ f h} := hsub
    _ = ENNReal.ofReal (μ.real {h | ε ≤ f h}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal hmain

end RBMTransitionEdge

end
