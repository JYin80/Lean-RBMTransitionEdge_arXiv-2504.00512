module

public import RBMTransitionEdge.Edge.CountBounds

@[expose] public section

/-!
# The cumulant expansion of the drift of the edge count in Lemma 4.3

The cutoff of the one-entry expansion with a factor that controls the edge count `A`, its
properties and its probability, and (4.9) [eq:prodnGt] with the bound (4.14) [eq:Fk] of the
higher-order terms (proof of Lemma 4.3 [rescomY]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The cutoff of the one-entry expansion of the drift in the proof of Lemma 4.3 [rescomY]:
`hpCut` over the pairs `(Λ, E_e(m) + iη)` and the vectors `e_i, e_j`, times
`Π_m ψ(A_m(ĥ)² / R²)`, where `ĥ` is the Hermitian part of `h` with the entry `(i, j)` set to `0`
and `ψ = cutoffFn`. -/
def edgeCut (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ} (E₁ E₂ : Fin n → ℝ)
    (Γ R : ℝ) (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℝ :=
  hpCut (Finset.univ.image fun r : Fin n × Fin 2 => (lam D N A, edgePt η E₁ E₂ r))
      {Pi.single i 1, Pi.single j 1} Γ i j h *
    ∏ m, cutoffFn (edgeCount D N A η (E₁ m) (E₂ m) (symArr (setEntry h i j 0)) ^ 2 / R ^ 2)

/-! ### Substitutions, forms and the segment bound for `A` -/

/-- `e_a^* G e_b = G_{ab}`. -/
private lemma CE_form_single {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (a b : ι) : star (Pi.single a (1 : ℂ)) ⬝ᵥ (G *ᵥ Pi.single b 1) = G a b := by
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

/-- A substitution in a Hermitian array is Hermitian. -/
private lemma CE_setEntry_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

/-- For a Hermitian array, a substitution is its own Hermitian part. -/
private lemma CE_symArr_setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    symArr (setEntry h i j w) = setEntry h i j w := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma CE_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      rw [hk, hl]
      have hre : (((h i i).re : ℝ) : ℂ) = h i i := Complex.conj_eq_iff_re.mp (h1 i i)
      simp [setEntry, hre]
    · simp [setEntry, hkl]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd, h1 k l]
      · simp [setEntry, hd, h1', h2]

/-- The substitution of `s w`, `s` real, is the line `ĥ + s V_w`, `V_w = setEntry 0 i j w`. -/
private lemma CE_line {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w : ℂ) (s : ℝ) :
    setEntry h i j ((s : ℂ) * w) = setEntry h i j 0 + s • setEntry 0 i j w := by
  funext k l
  simp only [setEntry, Pi.add_apply, Pi.smul_apply, Pi.zero_apply]
  split_ifs <;> simp [Complex.real_smul]

/-- `tr(B V_w)` for `V_w = setEntry 0 i j w`. -/
private lemma CE_trace_setEntry {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N)
    (w : ℂ) : (B * Matrix.of (setEntry 0 i j w)).trace =
      if i = j then B i i * ((w.re : ℝ) : ℂ) else B j i * w + B i j * starRingEnd ℂ w := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, setEntry,
    Pi.zero_apply]
  by_cases hij : i = j
  · subst hij
    simp [ite_and]
  · have e : ∀ x y : Idx D N, B x y * (if y = i ∧ x = j then w else
        if y = j ∧ x = i then starRingEnd ℂ w else 0) =
        (if x = j then (if y = i then B j i * w else 0) else 0) +
          (if x = i then (if y = j then B i j * starRingEnd ℂ w else 0) else 0) := by
      intro x y
      by_cases h1 : y = i ∧ x = j
      · obtain ⟨rfl, rfl⟩ := h1
        simp [Ne.symm hij]
      · by_cases h2 : y = j ∧ x = i
        · obtain ⟨rfl, rfl⟩ := h2
          simp [hij]
        · simp only [h1, h2, ↓reduceIte, mul_zero]
          split_ifs <;> simp_all
    simp only [hij, ↓reduceIte, e, Finset.sum_add_distrib]
    simp

/-- `|(Im G)_{ab}| ≤ (|G_{ab}| + |G_{ba}|)/2`. -/
private lemma CE_imRes_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (a b : ι) : ‖imRes X z a b‖ ≤ (‖res X z a b‖ + ‖res X z b a‖) / 2 := by
  have e : imRes X z a b = (2 * Complex.I)⁻¹ * (res X z a b - star (res X z b a)) := by
    simp [imRes, Matrix.conjTranspose_apply]
  rw [e, norm_mul, norm_inv]
  have h2 : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  rw [h2]
  have := norm_sub_le (res X z a b) (star (res X z b a))
  rw [norm_star] at this
  linarith

/-- Along the segment from `ĥ = setEntry h i j 0` to `setEntry h i j w`, if the entries `G_{ab}`,
`a, b ∈ {i, j}`, at the two points `E_e + iη` are at most `c`, then `A` changes by at most
`4 c |w|` (by (4.10) [partial_xy_F_A_t], two entries change). -/
private lemma CE_seg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η) (E₁ E₂ : ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) (c : ℝ)
    (hc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ E : ℝ, (E = E₁ ∨ E = E₂) → ∀ a b : Idx D N,
      (a = i ∨ a = j) → (b = i ∨ b = j) →
      ‖res (Matrix.of (setEntry h i j ((s : ℂ) * w)) + lam D N A)
        ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ≤ c) :
    |edgeCount D N A η E₁ E₂ (setEntry h i j w) - edgeCount D N A η E₁ E₂ (setEntry h i j 0)| ≤
      4 * c * ‖w‖ := by
  set V : Idx D N → Idx D N → ℂ := setEntry 0 i j w with hV
  set h0 : Idx D N → Idx D N → ℂ := setEntry h i j 0 with hh0
  have hVh : (Matrix.of V).IsHermitian := CE_setEntry_herm 0 (by simp) i j w
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 le_rfl zero_le_one E₁ (Or.inl rfl) i i
    (Or.inl rfl) (Or.inl rfl))
  have hline : ∀ s : ℝ, h0 + s • V = setEntry h i j ((s : ℂ) * w) := fun s =>
    (CE_line h i j w s).symm
  set f : ℝ → ℝ := fun s => edgeCount D N A η E₁ E₂ (h0 + s • V) with hf
  set d : ℝ → ℝ := fun s => -((imRes (Matrix.of (h0 + s • V) + lam D N A)
      ((E₂ : ℂ) + (η : ℂ) * Complex.I) - imRes (Matrix.of (h0 + s • V) + lam D N A)
        ((E₁ : ℂ) + (η : ℂ) * Complex.I)) * Matrix.of V).trace.re with hd
  have hder : ∀ s : ℝ, HasDerivAt f (d s) s := by
    intro s
    have hs : (Matrix.of (h0 + s • V)).IsHermitian := by
      rw [hline s]; exact CE_setEntry_herm h hh i j _
    have h1 := edgeCount_hasDerivAt D N A η E₁ E₂ hη (h0 + s • V) V hs hVh
    have h2 : HasDerivAt (fun s' : ℝ => edgeCount D N A η E₁ E₂ (h0 + s • V + s' • V)) (d s)
        (s - s) := by rw [sub_self]; exact h1
    have h3 := h2.comp_sub_const s s
    have e : (fun x : ℝ => edgeCount D N A η E₁ E₂ (h0 + s • V + (x - s) • V)) = f := by
      funext x
      simp only [hf]
      congr 1
      rw [add_assoc, ← add_smul]
      congr 2
      ring
    rwa [e] at h3
  have hbd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖d s‖ ≤ 4 * c * ‖w‖ := by
    intro s hs
    set B := imRes (Matrix.of (h0 + s • V) + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) -
      imRes (Matrix.of (h0 + s • V) + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I) with hB
    have hBab : ∀ a b : Idx D N, (a = i ∨ a = j) → (b = i ∨ b = j) → ‖B a b‖ ≤ 2 * c := by
      intro a b ha hb
      have k1 := CE_imRes_le (Matrix.of (h0 + s • V) + lam D N A)
        ((E₂ : ℂ) + (η : ℂ) * Complex.I) a b
      have k2 := CE_imRes_le (Matrix.of (h0 + s • V) + lam D N A)
        ((E₁ : ℂ) + (η : ℂ) * Complex.I) a b
      rw [hline s] at k1 k2
      have g1 := hc s hs.1 hs.2.le E₂ (Or.inr rfl) a b ha hb
      have g2 := hc s hs.1 hs.2.le E₂ (Or.inr rfl) b a hb ha
      have g3 := hc s hs.1 hs.2.le E₁ (Or.inl rfl) a b ha hb
      have g4 := hc s hs.1 hs.2.le E₁ (Or.inl rfl) b a hb ha
      have := norm_sub_le
        (imRes (Matrix.of (h0 + s • V) + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) a b)
        (imRes (Matrix.of (h0 + s • V) + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I) a b)
      rw [hline s] at this
      simp only [hB, Matrix.sub_apply]
      rw [hline s]
      linarith
    have ht : (B * Matrix.of V).trace = _ := CE_trace_setEntry B i j w
    simp only [hd, Real.norm_eq_abs, abs_neg]
    refine (Complex.abs_re_le_norm _).trans ?_
    change ‖(B * Matrix.of V).trace‖ ≤ _
    rw [ht]
    have hw0 := norm_nonneg w
    split_ifs with hij
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hBab i i (Or.inl rfl) (Or.inl rfl)
      have hre := Complex.abs_re_le_norm w
      have := mul_le_mul this hre (abs_nonneg _) (by positivity)
      nlinarith
    · refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have k1 := hBab j i (Or.inr rfl) (Or.inl rfl)
      have k2 := hBab i j (Or.inl rfl) (Or.inr rfl)
      have := mul_le_mul_of_nonneg_right k1 hw0
      have := mul_le_mul_of_nonneg_right k2 hw0
      nlinarith
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := 1)
    (fun x _ => (hder x).hasDerivWithinAt) hbd 1 ⟨zero_le_one, le_rfl⟩
  have e1 : f 1 = edgeCount D N A η E₁ E₂ (setEntry h i j w) := by
    simp only [hf]; rw [hline 1]; simp
  have e0 : f 0 = edgeCount D N A η E₁ E₂ (setEntry h i j 0) := by
    simp only [hf]; simp [hh0]
  rw [e1, e0, Real.norm_eq_abs] at hmvt
  simpa using hmvt

/-- A finite product of numbers in `[0, 1]` lies in `[0, 1]`. -/
private lemma CE_prod_mem_Icc {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ a ∈ s, f a ∈ Set.Icc (0 : ℝ) 1) : ∏ a ∈ s, f a ∈ Set.Icc (0 : ℝ) 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    exact ⟨mul_nonneg h1.1 h2.1, (mul_le_mul h1.2 h2.2 h2.1 zero_le_one).trans_eq (one_mul 1)⟩

/-- `ψ = cutoffFn` takes values in `[0, 1]`. -/
private lemma CE_cutoff_mem (t : ℝ) : cutoffFn t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- `ψ(t) ≠ 0` forces `t < 2`. -/
private lemma CE_cutoff_ne_zero {t : ℝ} (ht : cutoffFn t ≠ 0) : t < 2 := by
  by_contra hc
  exact ht (Real.smoothTransition.zero_of_nonpos (by linarith [not_lt.mp hc]))

/-- `ψ(t) = 1` for `t ≤ 1`. -/
private lemma CE_cutoff_one {t : ℝ} (ht : t ≤ 1) : cutoffFn t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The array `setEntry h i j w` is a smooth function of `(h, w)`. -/
private lemma CE_contDiff_setEntry {D N : ℕ} (i j : Idx D N) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hre : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => ((p.2.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
  have hw : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => p.2) := contDiff_snd
  have hcw : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => starRingEnd ℂ p.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  have hf : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => p.1 k l) :=
    (contDiff_apply_apply ℝ k l).comp contDiff_fst
  simp only [setEntry]
  split_ifs <;> assumption

/-- The Hermitian part `h ↦ (h + hᴴ)/2` is a smooth function of the array. -/
private lemma CE_contDiff_symArr {D N : ℕ} (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => symArr h) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  simp only [symArr]
  exact ((contDiff_apply_apply ℝ k l).add
    (Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ l k))).div_const 2

/-- The pairs `(Λ, E_e(m) + iη)` of `edgeCut` have Hermitian `Λ` and `Im ξ = η > 0`. -/
private lemma CE_Xi (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η) {n : ℕ}
    (E₁ E₂ : Fin n → ℝ) :
    ∀ p ∈ (Finset.univ.image fun r : Fin n × Fin 2 => (lam D N A, edgePt η E₁ E₂ r)),
      p.1.IsHermitian ∧ 0 < p.2.im := by
  intro p hp
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
  obtain ⟨r, rfl⟩ := hp
  exact ⟨lam_isHermitian D N A, by simp [edgePt, hη]⟩

/-- The point `E_e(m) + iη` for `r = (m, e)`. -/
private lemma CE_edgePt {n : ℕ} (η : ℝ) (E₁ E₂ : Fin n → ℝ) (m : Fin n) :
    edgePt η E₁ E₂ (m, 0) = ((E₁ m : ℝ) : ℂ) + (η : ℂ) * Complex.I ∧
      edgePt η E₁ E₂ (m, 1) = ((E₂ m : ℝ) : ℂ) + (η : ℂ) * Complex.I := by
  simp [edgePt]

/-- `a² < 2R²`, `R ≥ 2` and `|b - a| ≤ 1` give `|b| ≤ 2R`. -/
private lemma CE_levels {a b R : ℝ} (hR : 2 ≤ R) (ha : a ^ 2 < 2 * R ^ 2) (hab : |b - a| ≤ 1) :
    |b| ≤ 2 * R := by
  have h1 : |a| ≤ 2 * R - 1 := by
    by_contra hc
    have hc' := not_le.mp hc
    have h0 : 0 ≤ 2 * R - 1 := by linarith
    have := mul_lt_mul'' hc' hc' h0 h0
    rw [abs_mul_abs_self a] at this
    nlinarith
  have h2 : |b| ≤ |a| + |b - a| := by
    have := abs_add_le a (b - a)
    simp only [add_sub_cancel] at this
    linarith
  linarith

/-- The cutoff `edgeCut` takes values in `[0, 1]`, does not depend on the entry `(i, j)`, is
smooth on the Hermitian parts of arrays, and where it is nonzero, for every substitution
`|w| ≤ M` with `24 M Γ ≤ 1`, `|A_m| ≤ 2R` (`R ≥ 2`) and the entries `G_{ab}`, `a, b ∈ {i, j}`,
at the `2n` points are at most `6Γ`. -/
theorem edgeCut_spec (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η) {n : ℕ}
    (E₁ E₂ : Fin n → ℝ) (Γ R : ℝ) (i j : Idx D N) :
    (∀ h, edgeCut D N A η E₁ E₂ Γ R i j h ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ h (w : ℂ), edgeCut D N A η E₁ E₂ Γ R i j (setEntry h i j w) =
      edgeCut D N A η E₁ E₂ Γ R i j h) ∧
    (∀ k : ℕ, ContDiff ℝ k (fun h => edgeCut D N A η E₁ E₂ Γ R i j (symArr h))) ∧
    ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ M : ℝ, 0 < Γ → 2 ≤ R →
      24 * M * Γ ≤ 1 → edgeCut D N A η E₁ E₂ Γ R i j h ≠ 0 → ∀ w : ℂ, ‖w‖ ≤ M →
        (∀ m, |edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w)| ≤ 2 * R) ∧
        ∀ (r : Fin n × Fin 2) (a b : Idx D N), (a = i ∨ a = j) → (b = i ∨ b = j) →
          ‖res (Matrix.of (setEntry h i j w) + lam D N A) (edgePt η E₁ E₂ r) a b‖ ≤ 6 * Γ := by
  set Ξ := (Finset.univ.image fun r : Fin n × Fin 2 => (lam D N A, edgePt η E₁ E₂ r)) with hΞdef
  have hΞ := CE_Xi D N A η hη E₁ E₂
  set V : Finset (Idx D N → ℂ) := {Pi.single i 1, Pi.single j 1} with hVdef
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := hpCut_mem_Icc Ξ V Γ i j h
    have h2 := CE_prod_mem_Icc Finset.univ (fun m => cutoffFn
      (edgeCount D N A η (E₁ m) (E₂ m) (symArr (setEntry h i j 0)) ^ 2 / R ^ 2))
      fun m _ => CE_cutoff_mem _
    exact ⟨mul_nonneg h1.1 h2.1, (mul_le_mul h1.2 h2.2 h2.1 zero_le_one).trans_eq (one_mul 1)⟩
  · intro h w
    simp only [edgeCut]
    rw [hpCut_setEntry, setEntry_setEntry]
  · intro k
    simp only [edgeCut]
    refine ContDiff.mul ((hpCut_contDiff Ξ (fun p hp => ⟨(hΞ p hp).1, (hΞ p hp).2.ne'⟩) V Γ i j
      k).comp (CE_contDiff_symArr k)) ?_
    refine contDiff_prod fun m _ => ?_
    have hS : ContDiff ℝ k (fun h : Idx D N → Idx D N → ℂ => setEntry (symArr h) i j 0) :=
      (CE_contDiff_setEntry i j k).comp ((CE_contDiff_symArr k).prodMk contDiff_const)
    have hA : ContDiff ℝ k (fun h : Idx D N → Idx D N → ℂ =>
        edgeCount D N A η (E₁ m) (E₂ m) (symArr (setEntry (symArr h) i j 0))) :=
      ((edgeCount_contDiff D N A η (E₁ m) (E₂ m) hη).of_le (by exact_mod_cast le_top)).comp hS
    exact Real.smoothTransition.contDiff.comp (contDiff_const.sub ((hA.pow 2).div_const _))
  · intro h hh M hΓ hR hMΓ hχ w hw
    have hpc : hpCut Ξ V Γ i j h ≠ 0 := left_ne_zero_of_mul hχ
    have hA0 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hχ)
    have hiV : Pi.single i (1 : ℂ) ∈ V := by simp [hVdef]
    have hjV : Pi.single j (1 : ℂ) ∈ V := by simp [hVdef]
    have hG6 := hpCut_ne_zero_le Ξ hΞ h hh i j V hiV hjV M Γ hΓ hMΓ hpc
    have hG : ∀ w' : ℂ, ‖w'‖ ≤ M → ∀ (r : Fin n × Fin 2) (a b : Idx D N), (a = i ∨ a = j) →
        (b = i ∨ b = j) →
        ‖res (Matrix.of (setEntry h i j w') + lam D N A) (edgePt η E₁ E₂ r) a b‖ ≤ 6 * Γ := by
      intro w' hw' r a b ha hb
      have hp : (lam D N A, edgePt η E₁ E₂ r) ∈ Ξ := by simp [hΞdef]
      have haV : Pi.single a (1 : ℂ) ∈ V := by rcases ha with rfl | rfl <;> assumption
      have hbV : Pi.single b (1 : ℂ) ∈ V := by rcases hb with rfl | rfl <;> assumption
      have := hG6 w' hw' _ hp _ haV _ hbV
      simp only [resFactorEval] at this
      rwa [CE_form_single] at this
    refine ⟨fun m => ?_, hG w hw⟩
    have hm := CE_cutoff_ne_zero (hA0 m (Finset.mem_univ m))
    rw [CE_symArr_setEntry h hh] at hm
    have hR0 : 0 < R ^ 2 := by positivity
    rw [div_lt_iff₀ hR0] at hm
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hw
    have hseg := CE_seg D N A η hη (E₁ m) (E₂ m) h hh i j w (6 * Γ) (by
      intro s hs0 hs1 E hE a b ha hb
      have hsw : ‖(s : ℂ) * w‖ ≤ M := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
        nlinarith [norm_nonneg w]
      rcases hE with rfl | rfl
      · have := hG _ hsw (m, 0) a b ha hb
        rwa [(CE_edgePt η E₁ E₂ m).1] at this
      · have := hG _ hsw (m, 1) a b ha hb
        rwa [(CE_edgePt η E₁ E₂ m).2] at this)
    have h1 : 4 * (6 * Γ) * ‖w‖ ≤ 1 := by nlinarith
    exact CE_levels hR (by linarith) (hseg.trans h1)

/-! ### The probability that the cutoff differs from `1` -/

/-- Markov's inequality for an entry with the moment `k` of (2.3) [eq:highmoment]:
`P(|h_{ij}| > M) ≤ |C_k| (N^{1/2} M)^{-k}`. -/
private lemma CE_markov {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) (k : ℕ) (M : ℝ) (hM : 0 < M) :
    μ {h | M < ‖h i j‖} ≤
      ENNReal.ofReal (|C k| * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))) := by
  have := hμ.prob
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos i.2
  have hMk : 0 < M ^ k := pow_pos hM k
  have hσ0 : 0 ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) hM.le) _
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun h => ‖h i j‖ ^ k)
    (ae_of_all _ fun h => by simp only [Pi.zero_apply]; positivity) (hμ.integrable k i j) (M ^ k)
  have h2 : μ.real {h : Idx D N → Idx D N → ℂ | M < ‖h i j‖} ≤
      μ.real {h : Idx D N → Idx D N → ℂ | M ^ k ≤ ‖h i j‖ ^ k} :=
    measureReal_mono (fun h hh => pow_le_pow_left₀ hM.le (le_of_lt hh) k)
  have h3 := hμ.moments k i j
  have e : (N : ℝ) ^ (-((k : ℝ) / 2)) / M ^ k = ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) hM.le, ← Real.rpow_mul hN.le,
      Real.rpow_neg hM.le, Real.rpow_natCast, div_eq_mul_inv]
    congr 2
    ring
  have hmk : μ.real {h : Idx D N → Idx D N → ℂ | M < ‖h i j‖} ≤
      C k * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) := by
    rw [← e, ← mul_div_assoc, le_div_iff₀ hMk]
    nlinarith
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
  exact hmk.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hσ0)

/-- `(x^{1/2}/48)^{-k} ≤ 48^k x^{-e}` for `x ≥ 1` and `e ≤ k/2`. -/
private lemma CE_sigma_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) {e : ℝ} (he : e ≤ (k : ℝ) / 2) :
    (x ^ ((1 : ℝ) / 2) * (1 / 48)) ^ (-(k : ℝ)) ≤ 48 ^ k * x ^ (-e) := by
  have hx0 : 0 ≤ x := by linarith
  rw [Real.mul_rpow (Real.rpow_nonneg hx0 _) (by norm_num), ← Real.rpow_mul hx0,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 48), Real.rpow_natCast]
  have e : ((1 / 48 : ℝ) ^ k)⁻¹ = 48 ^ k := by rw [one_div, inv_pow, inv_inv]
  rw [e, mul_comm]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    (by positivity)

/-- The probability that `edgeCut` differs from `1` is at most `N^{-D'}`, with the constant `K ≥ 2`,
so that `R = K N^{2σ+τ'} ≥ 2`. -/
private lemma CE_ne_one (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ σ : ℝ, 0 < σ → σ < 1 / 12 → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ (n : ℕ) (E₁ E₂ : Fin n → ℝ),
      (∀ m, |E₁ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      (∀ m, |E₂ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) → ∀ i j : Idx D N,
        ouMatLaw D N L t {h | edgeCut D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ 2
            (K * (N : ℝ) ^ (2 * σ + τ')) i j h ≠ 1} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨KG, hKG, HG⟩ := edgeRes_entry_le D hD δA hδA C
  obtain ⟨KA, hKA, HA⟩ := edgeCount_rough D hD δA hδA C
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  refine ⟨KA + 2, by linarith, ?_⟩
  intro σ hσ0 hσ1 τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := HG σ hσ0 hσ1 τ' hτ' (D' + 1) (by linarith)
  obtain ⟨N₂, hN₂⟩ := HA σ hσ0 hσ1 τ' hτ' (D' + 1) (by linarith)
  set k : ℕ := ⌈2 * (D' + 1)⌉₊ with hk
  obtain ⟨Kh, hKh0, Hh⟩ := hpCut_ne_one_le k C'
  set c₀ : ℝ := 3 + (Kh + |C' k|) * 48 ^ k with hc₀
  refine ⟨max (max N₁ N₂) (⌈c₀⌉₊ + 1), ?_⟩
  intro N hN L t ht A hA n E₁ E₂ hE₁ hE₂ i j
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : ⌈c₀⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNc : c₀ ≤ (N : ℝ) := (Nat.le_ceil c₀).trans (by exact_mod_cast (by omega : ⌈c₀⌉₊ ≤ N))
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hx0 : (0 : ℝ) < N := by linarith
  set μ := ouMatLaw D N L t with hμdef
  have hμ := hC' N L t ht
  have := hμ.prob
  set η : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos hx0 _
  have hΛ := lam_isHermitian D N A
  set ε : ℝ := (N : ℝ) ^ (-(D' + 1)) with hεdef
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hx0.le _
  set y : ℝ := (N : ℝ) ^ (2 * σ + τ') with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by linarith)
  set SG : Set (Idx D N → Idx D N → ℂ) := {h | ∃ E : ℝ,
      |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧ ∃ a b : Idx D N,
        2 < ‖res (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ∨
        KG * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + τ') <
          ‖imRes (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖} with hSGdef
  have hSG : μ SG ≤ ENNReal.ofReal ε := hN₁ N hN1 L t ht A hA
  set SA : Set (Idx D N → Idx D N → ℂ) := {h | ∃ E₁ E₂ : ℝ,
      |E₁ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
      |E₂ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
      KA * y < |edgeCount D N A η E₁ E₂ h|} with hSAdef
  have hSA : μ SA ≤ ENNReal.ofReal ε := hN₂ N hN2 L t ht A hA
  set SM : Set (Idx D N → Idx D N → ℂ) := {h | 1 / 48 < ‖h i j‖} with hSMdef
  have hSM := CE_markov hμ i j k (1 / 48) (by norm_num)
  set SN : Set (Idx D N → Idx D N → ℂ) := {h | ¬ (Matrix.of h).IsHermitian} with hSNdef
  have hSN : μ SN = 0 := ae_iff.mp hμ.herm
  set Ξ := (Finset.univ.image fun r : Fin n × Fin 2 => (lam D N A, edgePt η E₁ E₂ r)) with hΞdef
  have hΞ := CE_Xi D N A η hη E₁ E₂
  set V : Finset (Idx D N → ℂ) := {Pi.single i 1, Pi.single j 1} with hVdef
  have hiV : Pi.single i (1 : ℂ) ∈ V := by simp [hVdef]
  have hjV : Pi.single j (1 : ℂ) ∈ V := by simp [hVdef]
  have hwin : ∀ (r : Fin n × Fin 2), ∃ E : ℝ, |E - Eplus (lam D N A)| ≤
      (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧ edgePt η E₁ E₂ r = (E : ℂ) + (η : ℂ) * Complex.I := by
    rintro ⟨m, e⟩
    fin_cases e
    · exact ⟨E₁ m, hE₁ m, (CE_edgePt η E₁ E₂ m).1⟩
    · exact ⟨E₂ m, hE₂ m, (CE_edgePt η E₁ E₂ m).2⟩
  -- the forms at the Hermitian part are at most `2` outside `SN ∪ SG`
  have hbad : μ {h | ∃ p ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V,
      2 < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ≤ ENNReal.ofReal ε := by
    refine (measure_mono (t := SN ∪ SG) ?_).trans ?_
    · intro h hh
      obtain ⟨p, hp, x, hx, y', hy', hlt⟩ := hh
      by_cases hH : (Matrix.of h).IsHermitian
      · right
        simp only [hΞdef, Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨r, rfl⟩ := hp
        obtain ⟨E, hE, hEr⟩ := hwin r
        have hxa : ∃ a, (a = i ∨ a = j) ∧ x = Pi.single a 1 := by
          simp only [hVdef, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨i, Or.inl rfl, rfl⟩
          · exact ⟨j, Or.inr rfl, rfl⟩
        have hyb : ∃ b, (b = i ∨ b = j) ∧ y' = Pi.single b 1 := by
          simp only [hVdef, Finset.mem_insert, Finset.mem_singleton] at hy'
          rcases hy' with rfl | rfl
          · exact ⟨i, Or.inl rfl, rfl⟩
          · exact ⟨j, Or.inr rfl, rfl⟩
        obtain ⟨a, -, rfl⟩ := hxa
        obtain ⟨b, -, rfl⟩ := hyb
        simp only [resFactorEval, symArr_of_isHermitian h hH, CE_form_single, hEr] at hlt
        exact ⟨E, hE, a, b, Or.inl hlt⟩
      · exact Or.inl hH
    · refine (measure_union_le _ _).trans ?_
      rw [hSN, zero_add]
      exact hSG
  have hSH := Hh D N (Real.exp (-t)) μ hμ Ξ hΞ i j V hiV hjV 2 (1 / 48) ε (by norm_num)
    (by norm_num) hε0 hbad
  -- the event inclusion
  have hsub : {h | edgeCut D N A η E₁ E₂ 2 ((KA + 2) * y) i j h ≠ 1} ⊆
      {h | hpCut Ξ V 2 i j h ≠ 1} ∪ SN ∪ SG ∪ SA ∪ SM := by
    intro h hh1
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨⟨⟨hp1', hH'⟩, hgG⟩, hgA⟩, hgM⟩ := hc
    have hp1 : hpCut Ξ V 2 i j h = 1 := by
      by_contra hc'
      exact hp1' hc'
    have hH : (Matrix.of h).IsHermitian := by
      by_contra hc'
      exact hH' hc'
    have hM : ‖h i j‖ ≤ 1 / 48 := by
      by_contra hc'
      exact hgM (not_le.mp hc')
    apply hh1
    simp only [edgeCut]
    rw [hp1, one_mul]
    refine Finset.prod_eq_one fun m _ => CE_cutoff_one ?_
    rw [CE_symArr_setEntry h hH]
    have hA1 : |edgeCount D N A η (E₁ m) (E₂ m) h| ≤ KA * y := by
      by_contra hc'
      exact hgA ⟨E₁ m, E₂ m, hE₁ m, hE₂ m, not_le.mp hc'⟩
    have hseg := CE_seg D N A η hη (E₁ m) (E₂ m) h hH i j (h i j) 4 (by
      intro s hs0 hs1 E hE a b ha hb
      have hEw : |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) := by
        rcases hE with rfl | rfl
        · exact hE₁ m
        · exact hE₂ m
      have hz : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
      have hsw : ‖(s : ℂ) * h i j‖ ≤ 1 / 48 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
        nlinarith [norm_nonneg (h i j)]
      have hG2 : ∀ x ∈ ({Pi.single i 1, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
          ∀ y ∈ ({Pi.single j 1, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
            ‖star x ⬝ᵥ (res (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) *ᵥ y)‖ ≤
              2 := by
        have key : ∀ a b : Idx D N,
            ‖res (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ≤ 2 := by
          intro a b
          by_contra hc'
          exact hgG ⟨E, hEw, a, b, Or.inl (not_le.mp hc')⟩
        intro x hx y' hy'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy'
        rcases hx with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
          (rw [CE_form_single]; exact key _ _)
      have hxa : Pi.single a (1 : ℂ) ∈
          ({Pi.single i 1, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)) := by
        rcases ha with rfl | rfl <;> simp
      have hyb : Pi.single b (1 : ℂ) ∈
          ({Pi.single j 1, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)) := by
        rcases hb with rfl | rfl <;> simp
      have := res_setEntry_le D N h (lam D N A) hH hΛ _ hz i j ((s : ℂ) * h i j) (1 / 48) 2 hsw
        hM (by norm_num) (Pi.single i 1) (Pi.single j 1) hG2 _ hxa _ hyb
      rw [CE_form_single] at this
      linarith)
    rw [CE_setEntry_self h hH] at hseg
    have hR : |edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j 0)| ≤ (KA + 2) * y := by
      have h1 := abs_sub_abs_le_abs_sub (edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j 0))
        (edgeCount D N A η (E₁ m) (E₂ m) h)
      rw [abs_sub_comm] at h1
      nlinarith
    have hR0 : 0 < ((KA + 2) * y) ^ 2 := by positivity
    rw [div_le_one hR0, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hR 2
  -- the sum of the five probabilities
  have hσk := CE_sigma_le hx1 k (e := D' + 1) (by
    have := Nat.le_ceil (2 * (D' + 1))
    rw [← hk] at this
    linarith)
  set σk := ((N : ℝ) ^ ((1 : ℝ) / 2) * (1 / 48)) ^ (-(k : ℝ)) with hσkdef
  have hσk0 : 0 ≤ σk := Real.rpow_nonneg (by positivity) _
  have htot : ε + Kh * σk + ε + ε + |C' k| * σk ≤ (N : ℝ) ^ (-D') := by
    have e1 : ε = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [hεdef, neg_add, Real.rpow_add hx0, Real.rpow_neg_one]
    have h1 : ε + Kh * σk + ε + ε + |C' k| * σk ≤ c₀ * ε := by
      have := mul_le_mul_of_nonneg_left hσk (add_nonneg hKh0 (abs_nonneg (C' k)))
      rw [hc₀]
      nlinarith
    have h2 : c₀ * ε ≤ (N : ℝ) ^ (-D') := by
      rw [e1]
      have hD0 : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hx0.le _
      calc c₀ * ((N : ℝ) ^ (-D') * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D') * (c₀ / N) := by ring
        _ ≤ (N : ℝ) ^ (-D') * 1 := by
          gcongr
          exact (div_le_one hx0).mpr hNc
        _ = (N : ℝ) ^ (-D') := mul_one _
    linarith
  calc μ {h | edgeCut D N A η E₁ E₂ 2 ((KA + 2) * y) i j h ≠ 1}
      ≤ μ ({h | hpCut Ξ V 2 i j h ≠ 1} ∪ SN ∪ SG ∪ SA ∪ SM) := measure_mono hsub
    _ ≤ μ {h | hpCut Ξ V 2 i j h ≠ 1} + μ SN + μ SG + μ SA + μ SM := by
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε + Kh * σk) + 0 + ENNReal.ofReal ε + ENNReal.ofReal ε +
        ENNReal.ofReal (|C' k| * σk) := by
      rw [hSN]
      gcongr
    _ = ENNReal.ofReal (ε + Kh * σk + ε + ε + |C' k| * σk) := by
      have a1 : 0 ≤ Kh * σk := mul_nonneg hKh0 hσk0
      have a2 : 0 ≤ |C' k| * σk := mul_nonneg (abs_nonneg _) hσk0
      rw [add_zero, ENNReal.ofReal_add (by linarith) a2, ENNReal.ofReal_add (by linarith) hε0,
        ENNReal.ofReal_add (by linarith) hε0]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal htot

/-! ### The cumulants and the derivatives in one entry -/

/-- `𝒞^{(0,1)}(h_{ij}) = E h̄_{ij} = 0` for the class. -/
private lemma CE_ccum01 {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h i j) 0 1 = 0 := by
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have e1 : ∫ z, starRingEnd ℂ z ∂(μ.map fun h => h i j) = 0 := by
    rw [integral_map hmeas.aemeasurable Complex.continuous_conj.aestronglyMeasurable,
      integral_conj, hμ.mean i j, map_zero]
  unfold ccum jointCum
  refine Finset.sum_eq_zero fun π _ => ?_
  have hne : (Finset.univ : Finset (Fin (0 + 1))) ≠ ⊥ := by simp
  obtain ⟨B, hB⟩ := π.parts_nonempty hne
  have hBu : B = Finset.univ := by
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hB
    ext y
    simp only [Finset.mem_univ, iff_true]
    have : y = x := Fin.ext (by have := y.isLt; have := x.isLt; omega)
    rw [this]
    exact hx
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hB ?_)
  rw [hBu]
  simpa using e1

/-- `F^{(p,q)}` of `∂_{w̄} g` is `F^{(p,q+1)}` of `g`. -/
private lemma CE_wirt_comp (p q : ℕ) (g : ℂ → ℂ) : wirt p q (wirt 0 1 g) = wirt p (q + 1) g := by
  simp only [wirt, Function.iterate_zero, id, Function.iterate_one]
  rw [Function.iterate_succ_apply]

/-- The derivative of a differentiable function of `Re w` only. -/
private lemma CE_re_fderiv (g : ℂ → ℂ) (hg : Differentiable ℝ g)
    (hre : ∀ w, g w = g ((w.re : ℝ) : ℂ)) (w v : ℂ) :
    fderiv ℝ g w v = fderiv ℝ g ((w.re : ℝ) : ℂ) ((v.re : ℝ) : ℂ) := by
  set P : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM with hP
  have e : g = fun w => g (P w) := funext fun w => by simpa [hP] using hre w
  have h1 : HasFDerivAt (fun w => g (P w)) ((fderiv ℝ g (P w)).comp P) w :=
    (hg (P w)).hasFDerivAt.comp w P.hasFDerivAt
  conv_lhs => rw [e, h1.fderiv]
  simp [hP]

/-- For a differentiable function of `Re w` only, `∂_w g = ∂_{w̄} g`, and `∂_{w̄} g` is again a
function of `Re w` only. -/
private lemma CE_re_dW (g : ℂ → ℂ) (hg : Differentiable ℝ g)
    (hre : ∀ w, g w = g ((w.re : ℝ) : ℂ)) :
    dW g = dWbar g ∧ ∀ w, dWbar g w = dWbar g ((w.re : ℝ) : ℂ) := by
  have hI : ∀ w, fderiv ℝ g w Complex.I = 0 := fun w => by
    rw [CE_re_fderiv g hg hre]; simp
  refine ⟨funext fun w => ?_, fun w => ?_⟩
  · simp only [dW, dWbar, hI, mul_zero, sub_zero, add_zero]
  · simp only [dWbar, hI, mul_zero, add_zero]
    rw [CE_re_fderiv g hg hre w 1, CE_re_fderiv g hg hre ((w.re : ℝ) : ℂ) 1]
    simp

/-- `∂_{w̄} g` of a smooth `g` is smooth. -/
private lemma CE_dWbar_contDiff {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dWbar g) := by
  have hd := (contDiff_infty_iff_fderiv.mp hg).2
  unfold dWbar
  exact ((hd.clm_apply contDiff_const).add (contDiff_const.mul
    (hd.clm_apply contDiff_const))).div_const 2

/-- For a smooth function of `Re w` only, `F^{(0,2)} = F^{(1,1)}`. -/
private lemma CE_re_wirt02 (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hre : ∀ w, g w = g ((w.re : ℝ) : ℂ)) : wirt 0 2 g = wirt 1 1 g := by
  have h1 := CE_re_dW g (hg.differentiable (by simp)) hre
  have h2 := CE_re_dW (dWbar g) ((CE_dWbar_contDiff hg).differentiable (by simp)) h1.2
  simp only [wirt, Function.iterate_zero, id, Function.iterate_one]
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply, Function.iterate_one, h2.1]

/-- `F(A(h))` composed with the Hermitian part is smooth. -/
private lemma CE_edgeFn_contDiff (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η)
    {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun h : Idx D N → Idx D N → ℂ => edgeFn D N A η F E₁ E₂ (symArr h)) :=
  hF.comp (contDiff_pi.2 fun m => edgeCount_contDiff D N A η (E₁ m) (E₂ m) hη)

/-- For a Hermitian array, `w ↦ F(A(setEntry h i j w))` is smooth. -/
private lemma CE_slice_contDiff (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η)
    {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    ContDiff ℝ ∞ (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) := by
  have e : (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) =
      fun w => ((edgeFn D N A η F E₁ E₂ (symArr (setEntry h i j w)) : ℝ) : ℂ) := by
    funext w; rw [CE_symArr_setEntry h hh]
  rw [e]
  exact Complex.ofRealCLM.contDiff.comp ((CE_edgeFn_contDiff D N A η hη F hF E₁ E₂).comp
    ((CE_contDiff_setEntry i j ∞).comp (contDiff_const.prodMk contDiff_id)))

/-- The integrand `∂_{w̄} F(A(setEntry h i j w))|_{w = h_{ij}}` of the drift, composed with the
Hermitian part, is smooth. -/
private lemma CE_drift_contDiff (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η)
    {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ) (i j : Idx D N) :
    ContDiff ℝ ∞ (fun h : Idx D N → Idx D N → ℂ =>
      wirt 0 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry (symArr h) i j w) : ℂ))
        (symArr h i j)) := by
  set Φ : (Idx D N → Idx D N → ℂ) × ℂ → ℂ := fun p =>
    ((edgeFn D N A η F E₁ E₂ (symArr (setEntry (symArr p.1) i j p.2)) : ℝ) : ℂ) with hΦ
  have hΦc : ContDiff ℝ ∞ Φ :=
    Complex.ofRealCLM.contDiff.comp ((CE_edgeFn_contDiff D N A η hη F hF E₁ E₂).comp
      ((CE_contDiff_setEntry i j ∞).comp
        (((CE_contDiff_symArr ∞).comp contDiff_fst).prodMk contDiff_snd)))
  have hd := (contDiff_infty_iff_fderiv.mp hΦc).2
  have hslice : ∀ (r : Idx D N → Idx D N → ℂ) (w v : ℂ),
      fderiv ℝ (fun w' => Φ (r, w')) w v = fderiv ℝ Φ (r, w) (0, v) := by
    intro r w v
    have h2 := ((hΦc.differentiable (by simp)) (r, w)).hasFDerivAt.comp w
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) r w)
    have h3 : fderiv ℝ (fun w' => Φ (r, w')) w = _ := h2.fderiv
    rw [h3]
    simp
  have e : (fun h : Idx D N → Idx D N → ℂ =>
      wirt 0 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry (symArr h) i j w) : ℂ))
        (symArr h i j)) = fun h => (fderiv ℝ Φ (h, symArr h i j) (0, 1) +
          Complex.I * fderiv ℝ Φ (h, symArr h i j) (0, Complex.I)) / 2 := by
    funext h
    have e2 : (fun w => (edgeFn D N A η F E₁ E₂ (setEntry (symArr h) i j w) : ℂ)) =
        fun w => Φ (h, w) := by
      funext w
      simp only [hΦ]
      rw [CE_symArr_setEntry (symArr h) (symArr_isHermitian h)]
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one, dWbar, e2, hslice]
  rw [e]
  have hp : ContDiff ℝ ∞ (fun h : Idx D N → Idx D N → ℂ => (h, symArr h i j)) :=
    contDiff_id.prodMk ((contDiff_apply_apply ℝ i j).comp (CE_contDiff_symArr ∞))
  exact (((hd.comp hp).clm_apply contDiff_const).add (contDiff_const.mul
    ((hd.comp hp).clm_apply contDiff_const))).div_const 2

/-- For a Hermitian array, the restriction of the drift integrand to the entry `(i, j)` is
`∂_{w̄}` of `w ↦ F(A(setEntry h i j w))`; on the diagonal this uses that the substitution sees
`Re w` only. -/
private lemma CE_drift_slice (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η)
    {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (p q : ℕ) :
    wirt p q (fun w' => wirt 0 1 (fun w => (edgeFn D N A η F E₁ E₂
        (setEntry (setEntry h i j w') i j w) : ℂ)) (setEntry h i j w' i j)) =
      wirt p (q + 1) (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) := by
  rw [← CE_wirt_comp]
  suffices key : (fun w' => wirt 0 1 (fun w => (edgeFn D N A η F E₁ E₂
      (setEntry (setEntry h i j w') i j w) : ℂ)) (setEntry h i j w' i j)) =
      wirt 0 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) by rw [key]
  funext w'
  simp only [setEntry_setEntry]
  by_cases hij : i = j
  · subst hij
    have hre : ∀ w, (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i i w) : ℂ)) w =
        (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i i w) : ℂ)) ((w.re : ℝ) : ℂ) := by
      intro w
      have : setEntry h i i w = setEntry h i i ((w.re : ℝ) : ℂ) := by
        funext k l; simp [setEntry]
      simp only [this]
    have h1 := CE_re_dW _ ((CE_slice_contDiff D N A η hη F hF E₁ E₂ h hh i i).differentiable
      (by simp)) hre
    have hv : setEntry h i i w' i i = ((w'.re : ℝ) : ℂ) := by simp [setEntry]
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one, hv]
    exact (h1.2 w').symm
  · have hv : setEntry h i j w' i j = w' := by simp [setEntry, hij]
    rw [hv]

/-- The bound of `edgeFn_wirt_le` for the orders `1, …, 6` with `B_F` from (4.6)
[derivative_bound_F] at `l = 6`: if `|A_m| ≤ a` at the substituted array and the entries `G_{ab}`,
`(Im G)_{ab}`, `a, b ∈ {i, j}`, are at most `Γ ≥ 1` and `Γ_I ≤ Γ`, then
`|∂_w^p ∂_{w̄}^{q+1} F(A)| ≤ K C_* (1 + a)^{C_*} Γ_I Γ^5`, `C_* = max(C_6, 1)`, `p + q ≤ 5`. -/
private lemma CE_wirt_le (n : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (CF : ℕ → ℝ)
    (hCF : ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p q : ℕ, p + q ≤ 5 → ∀ (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ),
      0 < η → ∀ (E₁ E₂ : Fin n → ℝ) (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (w : ℂ) (a Γ ΓI : ℝ), 0 ≤ a → 1 ≤ Γ → 0 ≤ ΓI → ΓI ≤ Γ →
      (∀ m, |edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w)| ≤ a) →
      (∀ (r : Fin n × Fin 2) (a' b' : Idx D N), (a' = i ∨ a' = j) → (b' = i ∨ b' = j) →
        ‖res (Matrix.of (setEntry h i j w) + lam D N A) (edgePt η E₁ E₂ r) a' b'‖ ≤ Γ ∧
          ‖imRes (Matrix.of (setEntry h i j w) + lam D N A) (edgePt η E₁ E₂ r) a' b'‖ ≤ ΓI) →
      ‖wirt p (q + 1) (fun w' => (edgeFn D N A η F E₁ E₂ (setEntry h i j w') : ℂ)) w‖ ≤
        K * (max (CF 6) 1 * (1 + a) ^ max (CF 6) 1) * ΓI * Γ ^ 5 := by
  choose Kw hKw0 hKw using fun p q : ℕ => edgeFn_wirt_le n p (q + 1) (by omega)
  have hK0 : 0 ≤ ∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 6, Kw p q :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => (hKw0 p q).le
  refine ⟨∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 6, Kw p q, hK0, ?_⟩
  intro p q hpq D N A η hη E₁ E₂ h hh i j w a Γ ΓI ha hΓ hΓI hle hA hG
  set Cs : ℝ := max (CF 6) 1 with hCs
  have hCs1 : 1 ≤ Cs := le_max_right _ _
  have hBF0 : 0 ≤ Cs * (1 + a) ^ Cs := by positivity
  have hBF : ∀ k : ℕ, 1 ≤ k → k ≤ p + (q + 1) →
      ‖iteratedFDeriv ℝ k F (fun m => edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w))‖ ≤
        Cs * (1 + a) ^ Cs := by
    intro k hk1 hk2
    refine (hCF 6 k hk1 (by omega) _).trans ?_
    set x : Fin n → ℝ := fun m => edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w)
    have hx : ‖x‖ ≤ a := (pi_norm_le_iff_of_nonneg ha).2 fun m => by
      rw [Real.norm_eq_abs]; exact hA m
    have hb1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rcases le_or_gt (CF 6) 0 with hc | hc
    · have : CF 6 * (1 + ‖x‖) ^ CF 6 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (Real.rpow_nonneg (by linarith) _)
      linarith
    · have h1 : (1 + ‖x‖) ^ CF 6 ≤ (1 + a) ^ CF 6 :=
        Real.rpow_le_rpow (by linarith) (by linarith) hc.le
      have h2 : (1 + a) ^ CF 6 ≤ (1 + a) ^ Cs :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
      exact mul_le_mul (le_max_left _ _) (h1.trans h2) (Real.rpow_nonneg (by linarith) _)
        (by linarith)
  have hmain := hKw p q D N A η hη F hF E₁ E₂ h hh i j w (Cs * (1 + a) ^ Cs) Γ ΓI hΓ hΓI hle
    hBF hG
  have hK : Kw p q ≤ ∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 6, Kw p q := by
    have h1 : Kw p q ≤ ∑ q ∈ Finset.range 6, Kw p q :=
      Finset.single_le_sum (f := fun q => Kw p q) (fun q _ => (hKw0 p q).le)
        (Finset.mem_range.mpr (by omega))
    have h2 : ∑ q ∈ Finset.range 6, Kw p q ≤
        ∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 6, Kw p q :=
      Finset.single_le_sum (f := fun p => ∑ q ∈ Finset.range 6, Kw p q)
        (fun p _ => Finset.sum_nonneg fun q _ => (hKw0 p q).le) (Finset.mem_range.mpr (by omega))
    linarith
  have hΓp : Γ ^ (p + (q + 1) - 1) ≤ Γ ^ 5 := pow_le_pow_right₀ hΓ (by omega)
  refine hmain.trans ?_
  have hΓ0 : 0 ≤ Γ ^ (p + (q + 1) - 1) := by positivity
  calc Kw p q * (Cs * (1 + a) ^ Cs) * ΓI * Γ ^ (p + (q + 1) - 1)
      ≤ (∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 6, Kw p q) * (Cs * (1 + a) ^ Cs) * ΓI *
          Γ ^ (p + (q + 1) - 1) := by gcongr
    _ ≤ (∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 6, Kw p q) * (Cs * (1 + a) ^ Cs) * ΓI *
          Γ ^ 5 := by gcongr

/-- `‖E f‖ ≤ X + B ε` when `|f| ≤ B` almost surely, `|f| ≤ X` almost surely off `T`, and
`P(T) ≤ ε`. -/
private lemma CE_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℂ) (T : Set α) (X B ε : ℝ) (hX : 0 ≤ X) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hT : μ T ≤ ENNReal.ofReal ε) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ B ∧ (x ∉ T → ‖f x‖ ≤ X)) :
    ‖∫ x, f x ∂μ‖ ≤ X + B * ε := by
  set T' := toMeasurable μ T with hT'
  have hT'm : MeasurableSet T' := measurableSet_toMeasurable μ T
  have hT'r : μ.real T' ≤ ε := by
    rw [measureReal_def, hT', measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε hT
  have hind : Integrable (fun x => T'.indicator (1 : α → ℝ) x) μ :=
    (integrable_const (1 : ℝ)).indicator hT'm
  have hint : Integrable (fun x => X + B * T'.indicator (1 : α → ℝ) x) μ :=
    (integrable_const X).add (hind.const_mul B)
  calc ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (X + B * T'.indicator (1 : α → ℝ) x) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hint ?_
      filter_upwards [hf] with x hx
      by_cases hxT : x ∈ T'
      · simp only [Set.indicator_of_mem hxT, Pi.one_apply, mul_one]
        linarith [hx.1]
      · simp only [Set.indicator_of_notMem hxT, mul_zero, add_zero]
        exact hx.2 fun h => hxT (subset_toMeasurable μ T h)
    _ = X + B * μ.real T' := by
      rw [integral_add (integrable_const X) (hind.const_mul B), integral_const,
        integral_const_mul, integral_indicator_one hT'm]
      simp
    _ ≤ X + B * ε := by gcongr

/-- For `δ > 0`, eventually `c ≤ N^δ`. -/
private lemma CE_eventually (c δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ δ := by
  have h := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, hN₀⟩

/-- For `e < x`, eventually `c N^e ≤ N^x / 4`. -/
private lemma CE_absorb (c e x : ℝ) (he : e < x) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c * (N : ℝ) ^ e ≤ (N : ℝ) ^ x / 4 := by
  obtain ⟨N₁, h⟩ := CE_eventually (4 * c) (x - e) (by linarith)
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 := h N (le_trans (le_max_left _ _) hN)
  have e1 : (N : ℝ) ^ x = (N : ℝ) ^ (x - e) * (N : ℝ) ^ e := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [e1]
  have := Real.rpow_pos_of_pos hN0 e
  nlinarith

/-- `(1 + K y)^c ≤ (1 + K)^c y^c` for `K ≥ 0`, `y ≥ 1`, `c ≥ 0`. -/
private lemma CE_pow_le {K y c : ℝ} (hK : 0 ≤ K) (hy : 1 ≤ y) (hc : 0 ≤ c) :
    (1 + K * y) ^ c ≤ (1 + K) ^ c * y ^ c := by
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  exact Real.rpow_le_rpow (by positivity) (by nlinarith) hc

/-- The terms of the expansion to order `l = 4` with `p + q ≤ 1` and the others. -/
private lemma CE_split (T : ℕ → ℕ → ℂ) :
    ∑ p ∈ Finset.range (4 + 1), ∑ q ∈ Finset.range (4 + 1 - p), T p q =
      T 0 0 + T 1 0 + T 0 1 + ∑ p ∈ Finset.range (4 + 1), ∑ q ∈ Finset.range (4 + 1 - p),
        (if 2 ≤ p + q then T p q else 0) := by
  simp [Finset.sum_range_succ]
  ring

/-- `Σ_{p ≤ 4} Σ_{q ≤ 4 - p} c = 15 c`. -/
private lemma CE_count (c : ℝ) :
    ∑ p ∈ Finset.range (4 + 1), ∑ _q ∈ Finset.range (4 + 1 - p), c = 15 * c := by
  simp [Finset.sum_range_succ]
  ring

/-- The second-order terms of the expansion recombine with the generator into `(e^{-t}/2) ℱ₂`
(the step from the display before (4.9) [eq:prodnGt] to (4.9)): if the drift integrand of the
entry `(i, j)` equals
`err_{ij} + (S_θ)_{ij} E ∂_w ∂_{w̄} G + δ_{ij} (S_θ)_{ij} E ∂_{w̄}² G + H_{ij}`
and `E ∂_{w̄}² G = E ∂_w ∂_{w̄} G` on the diagonal, then
`entryDeriv - (θ/2) entryF2 = -½ Σ κ_{ij} (err_{ij} + H_{ij})`. -/
private lemma CE_algebra {D N : ℕ} (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (θ : ℝ) (err H I01 : Idx D N → Idx D N → ℂ)
    (hdrift : ∀ i j, ∫ h, starRingEnd ℂ (h i j) *
        wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ =
      err i j + (varProf D N θ i j : ℂ) *
        (∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) +
        (if i = j then (varProf D N θ i j : ℂ) else 0) * I01 i j + H i j)
    (hdiag : ∀ i, I01 i i = ∫ h, wirt 1 1 (fun w => (G (setEntry h i i w) : ℂ)) (h i i) ∂μ) :
    entryDeriv G μ - (1 / 2 : ℂ) * (θ : ℂ) * entryF2 G μ =
      ∑ i, ∑ j, (-(1 / 2 : ℂ)) * driftWt i j * (err i j + H i j) := by
  have key : ∀ i j : Idx D N,
      -(1 / 2 : ℂ) * (driftWt i j * (err i j + (varProf D N θ i j : ℂ) *
        (∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) +
        (if i = j then (varProf D N θ i j : ℂ) else 0) * I01 i j + H i j)) +
      (1 / 2 : ℂ) * (((D * N : ℕ) : ℂ))⁻¹ * (genWt i j *
        ∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) -
      (1 / 2 : ℂ) * (θ : ℂ) * (genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        ∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) =
      (-(1 / 2 : ℂ)) * driftWt i j * (err i j + H i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [driftWt, genWt, ↓reduceIte, hdiag, varProf]
      push_cast
      ring
    · simp only [driftWt, genWt, hij, ↓reduceIte, varProf]
      push_cast
      ring
  unfold entryDeriv entryDrift entryGen entryF2
  simp only [hdrift]
  rw [← Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

set_option maxHeartbeats 1000000 in -- elaboration of the expansion over all entries
/-- The bound of `edgeDeriv_sub_F2_le`: the expansion of each entry by `expansion_hp_gen` at
`l = 4` with the cutoff `edgeCut`, the second-order terms recombined by `CE_algebra`, and the
orders `3, 4, 5` and the remainder bounded on the event of (2.22) [eq:aniso_local] and
(4.8) [rough_estimate_A_t]. -/
private lemma CE_deriv_main (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) (n : ℕ)
    (F : (Fin n → ℝ) → ℝ) (CF : ℕ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hCF : ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) :
    ∀ σ : ℝ, 0 < σ → σ < 1 / 12 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) → ∀ E₁ E₂ : Fin n → ℝ,
      (∀ m, |E₁ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      (∀ m, |E₂ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
        ‖entryDeriv (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂) (ouMatLaw D N L t) -
            (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) *
              entryF2 (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂) (ouMatLaw D N L t)‖ ≤
          (N : ℝ) ^ ((1 / 6 : ℝ) + (3 * max (CF 6) 1 + 3) * σ) := by
  set Cs : ℝ := max (CF 6) 1 with hCs
  have hCs1 : 1 ≤ Cs := le_max_right _ _
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨Kw, hKw0, HW⟩ := CE_wirt_le n F hF CF hCF
  choose Kc hKc using fun p q => llClass_ccum_le C' p q
  set Kcm : ℝ := ∑ p ∈ Finset.range 6, ∑ q ∈ Finset.range 7, |Kc p q| with hKcm
  have hKcm0 : 0 ≤ Kcm := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _
  have hKcle : ∀ p q, p < 6 → q < 7 → |Kc p q| ≤ Kcm := by
    intro p q hp hq
    have h1 : |Kc p q| ≤ ∑ q ∈ Finset.range 7, |Kc p q| :=
      Finset.single_le_sum (f := fun q => |Kc p q|) (fun q _ => abs_nonneg _)
        (Finset.mem_range.mpr hq)
    have h2 : ∑ q ∈ Finset.range 7, |Kc p q| ≤ Kcm :=
      Finset.single_le_sum (f := fun p => ∑ q ∈ Finset.range 7, |Kc p q|)
        (fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _) (Finset.mem_range.mpr hp)
    linarith
  set b : ℝ := 2 * Cs + 5 with hb
  set D'' : ℝ := 2 * b + 6 with hD''
  have hD''0 : 0 < D'' := by rw [hD'', hb]; linarith
  set k : ℕ := ⌈2 * D''⌉₊ with hk
  have hk2 : D'' ≤ (k : ℝ) / 2 := by
    have := Nat.le_ceil (2 * D'')
    rw [← hk] at this
    linarith
  obtain ⟨Ke, hKe0, HE⟩ := expansion_hp_gen 4 k C'
  obtain ⟨KG, hKG, HG⟩ := edgeRes_entry_le D hD δA hδA C
  obtain ⟨KA, hKA, HA⟩ := edgeCount_rough D hD δA hδA C
  obtain ⟨Kχ, hKχ, Hχ⟩ := CE_ne_one D hD δA hδA C
  intro σ hσ0 hσ1
  have hτ : 0 < σ / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := HG σ hσ0 hσ1 (σ / 2) hτ D'' hD''0
  obtain ⟨N₂, hN₂⟩ := HA σ hσ0 hσ1 (σ / 2) hτ D'' hD''0
  obtain ⟨N₃, hN₃⟩ := Hχ σ hσ0 hσ1 (σ / 2) hτ D'' hD''0
  set x₀ : ℝ := (1 / 6 : ℝ) + (3 * Cs + 3) * σ with hx₀
  set KB : ℝ := Kw * (Cs * (1 + 2 * D) ^ Cs) with hKB
  set c₁ : ℝ := (D : ℝ) ^ 2 * Ke * (Kw * (Cs * (1 + 2 * Kχ) ^ Cs) * 12 * 12 ^ 5) with hc₁
  set e₁ : ℝ := 2 + -3 + (2 * σ + σ / 2) * Cs with he₁
  set c₂ : ℝ := (D : ℝ) ^ 2 * Ke * KB * Real.sqrt (1 + 48 ^ k) with hc₂
  set e₂ : ℝ := 2 + b + -D'' / 2 with he₂
  set c₃ : ℝ := (D : ℝ) ^ 2 * (15 * Kcm) * (Kw * (Cs * (1 + KA) ^ Cs) * KG * 2 ^ 5) with hc₃
  set e₃ : ℝ := 2 + -(3 / 2) + ((2 * σ + σ / 2) * Cs + (-(1 / 3 : ℝ) + σ + σ / 2)) with he₃
  set c₄ : ℝ := (D : ℝ) ^ 2 * (15 * Kcm) * (KB * 2) with hc₄
  set e₄ : ℝ := 2 + -(3 / 2) + (b + -D'') with he₄
  obtain ⟨M₁, hM₁⟩ := CE_absorb c₁ e₁ x₀ (by rw [he₁, hx₀]; nlinarith)
  obtain ⟨M₂, hM₂⟩ := CE_absorb c₂ e₂ x₀ (by rw [he₂, hx₀, hD'']; nlinarith)
  obtain ⟨M₃, hM₃⟩ := CE_absorb c₃ e₃ x₀ (by rw [he₃, hx₀]; nlinarith)
  obtain ⟨M₄, hM₄⟩ := CE_absorb c₄ e₄ x₀ (by rw [he₄, hx₀, hD'', hb]; nlinarith)
  refine ⟨N₁ + N₂ + N₃ + M₁ + M₂ + M₃ + M₄ + 1, ?_⟩
  intro N hN L t ht A hA E₁ E₂ hE₁ hE₂
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hx0 : (0 : ℝ) < N := by linarith
  set μ := ouMatLaw D N L t with hμdef
  have hμ := hC' N L t ht
  have := hμ.prob
  set θ : ℝ := Real.exp (-t) with hθ
  set η : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) with hηdef
  have hη0 : 0 < η := Real.rpow_pos_of_pos hx0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hΛ := lam_isHermitian D N A
  set y : ℝ := (N : ℝ) ^ (2 * σ + σ / 2) with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by linarith)
  set R : ℝ := Kχ * y with hRdef
  have hR2 : 2 ≤ R := hKχ.trans (le_mul_of_one_le_right (by linarith) hy1)
  set ε : ℝ := (N : ℝ) ^ (-D'') with hεdef
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hx0.le _
  set G := edgeFn D N A η F E₁ E₂ with hGdef
  have hpt : ∀ r : Fin n × Fin 2, (edgePt η E₁ E₂ r).im = η := by
    intro r; simp [edgePt]
  have hwin : ∀ r : Fin n × Fin 2, ∃ E : ℝ, |E - Eplus (lam D N A)| ≤
      (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧ edgePt η E₁ E₂ r = (E : ℂ) + (η : ℂ) * Complex.I := by
    rintro ⟨m, e⟩
    fin_cases e
    · exact ⟨E₁ m, hE₁ m, (CE_edgePt η E₁ E₂ m).1⟩
    · exact ⟨E₂ m, hE₂ m, (CE_edgePt η E₁ E₂ m).2⟩
  -- the deterministic bound of all derivatives of orders `1, …, 6`
  set aD : ℝ := ((D * N : ℕ) : ℝ) * (2 * (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) / η with haD
  have haD0 : 0 ≤ aD := by positivity
  set Bdet : ℝ := Kw * (Cs * (1 + aD) ^ Cs) * η⁻¹ * η⁻¹ ^ 5 with hBdet
  have hBdet0 : 0 ≤ Bdet := by positivity
  have hBd : ∀ p q : ℕ, p + q ≤ 5 → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (w : ℂ),
        ‖wirt p (q + 1) (fun w' => (G (setEntry h i j w') : ℂ)) w‖ ≤ Bdet := by
    intro p q hpq h hh i j w
    have hX := CE_setEntry_herm h hh i j w
    refine HW p q hpq D N A η hη0 E₁ E₂ h hh i j w aD η⁻¹ η⁻¹ haD0 ((one_le_inv₀ hη0).mpr hη1)
      (inv_nonneg.mpr hη0.le) le_rfl ?_ ?_
    · intro m
      refine (edgeCount_abs_le D N A η (E₁ m) (E₂ m) hη0 _ hX).trans ?_
      have hw : |E₂ m - E₁ m| ≤ 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) := by
        have h1 := abs_le.mp (hE₁ m)
        have h2 := abs_le.mp (hE₂ m)
        rw [abs_le]
        constructor <;> linarith
      rw [haD]
      gcongr
    · intro r a' b' _ _
      have hop : ∀ a b : Idx D N, ‖res (Matrix.of (setEntry h i j w) + lam D N A)
          (edgePt η E₁ E₂ r) a b‖ ≤ η⁻¹ := fun a b =>
        (norm_apply_le_opNorm _ a b).trans ((opNorm_res_le _ (hX.add hΛ) _
          (by rw [hpt r]; exact hη0)).trans_eq (by rw [hpt r]))
      refine ⟨hop a' b', (CE_imRes_le _ _ a' b').trans ?_⟩
      linarith [hop a' b', hop b' a']
  -- the bound on the good event
  set ΓI : ℝ := KG * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) with hΓI
  have hΓI0 : 0 ≤ ΓI := by positivity
  set Xg : ℝ := Kw * (Cs * (1 + KA * y) ^ Cs) * ΓI * 2 ^ 5 with hXg
  have hXg0 : 0 ≤ Xg := by positivity
  set SG : Set (Idx D N → Idx D N → ℂ) := {h | ∃ E : ℝ,
      |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧ ∃ a b : Idx D N,
        2 < ‖res (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ∨
        KG * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) <
          ‖imRes (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖} with hSGdef
  have hSG : μ SG ≤ ENNReal.ofReal ε := hN₁ N (by omega) L t ht A hA
  set SA : Set (Idx D N → Idx D N → ℂ) := {h | ∃ E₁ E₂ : ℝ,
      |E₁ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
      |E₂ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
      KA * y < |edgeCount D N A η E₁ E₂ h|} with hSAdef
  have hSA : μ SA ≤ ENNReal.ofReal ε := hN₂ N (by omega) L t ht A hA
  set SN : Set (Idx D N → Idx D N → ℂ) := {h | ¬ (Matrix.of h).IsHermitian} with hSNdef
  have hSN : μ SN = 0 := ae_iff.mp hμ.herm
  set T := SN ∪ SG ∪ SA with hTdef
  have hT : μ T ≤ ENNReal.ofReal (2 * ε) := by
    calc μ T ≤ μ SN + μ SG + μ SA :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ ≤ 0 + ENNReal.ofReal ε + ENNReal.ofReal ε := by rw [hSN]; gcongr
      _ = ENNReal.ofReal (2 * ε) := by
        rw [zero_add, ← ENNReal.ofReal_add hε0 hε0, two_mul]
  have hgood : ∀ p q : ℕ, p + q ≤ 5 → ∀ h : Idx D N → Idx D N → ℂ, h ∉ T → ∀ i j : Idx D N,
      ‖wirt p (q + 1) (fun w' => (G (setEntry h i j w') : ℂ)) (h i j)‖ ≤ Xg := by
    intro p q hpq h hT' i j
    have hH : (Matrix.of h).IsHermitian := by
      by_contra hc
      exact hT' (Or.inl (Or.inl hc))
    have hnG : h ∉ SG := fun hc => hT' (Or.inl (Or.inr hc))
    have hnA : h ∉ SA := fun hc => hT' (Or.inr hc)
    have hself := CE_setEntry_self h hH i j
    have key := HW p q hpq D N A η hη0 E₁ E₂ h hH i j (h i j) (KA * y) 2 (min ΓI 2)
      (by positivity) (by norm_num) (le_min hΓI0 (by norm_num)) (min_le_right _ _) (by
        intro m
        rw [hself]
        by_contra hc
        exact hnA ⟨E₁ m, E₂ m, hE₁ m, hE₂ m, not_le.mp hc⟩) (by
        intro r a' b' _ _
        rw [hself]
        obtain ⟨E, hE, hEr⟩ := hwin r
        rw [hEr]
        have k1 : ∀ a b : Idx D N, ‖res (Matrix.of h + lam D N A)
            ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ≤ 2 := fun a b => by
          by_contra hc
          exact hnG ⟨E, hE, a, b, Or.inl (not_le.mp hc)⟩
        have k2 : ∀ a b : Idx D N, ‖imRes (Matrix.of h + lam D N A)
            ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ≤ ΓI := fun a b => by
          by_contra hc
          exact hnG ⟨E, hE, a, b, Or.inr (not_le.mp hc)⟩
        refine ⟨k1 a' b', le_min (k2 a' b') ?_⟩
        have := CE_imRes_le (Matrix.of h + lam D N A) ((E : ℂ) + (η : ℂ) * Complex.I) a' b'
        linarith [k1 a' b', k1 b' a'])
    refine key.trans ?_
    rw [hXg]
    gcongr
    exact min_le_left _ _
  have hI : ∀ p q : ℕ, p + q ≤ 5 → ∀ i j : Idx D N,
      ‖∫ h, wirt p (q + 1) (fun w' => (G (setEntry h i j w') : ℂ)) (h i j) ∂μ‖ ≤
        Xg + Bdet * (2 * ε) := by
    intro p q hpq i j
    refine CE_int_le μ _ T Xg Bdet (2 * ε) hXg0 hBdet0 (by positivity) hT ?_
    filter_upwards [hμ.herm] with h hh
    exact ⟨hBd p q hpq h hh i j (h i j), fun hT' => hgood p q hpq h hT' i j⟩
  -- the expansion of the drift in each entry
  set Aerr : ℝ := Kw * (Cs * (1 + 2 * R) ^ Cs) * 12 * 12 ^ 5 with hAerr
  have hAerr0 : 0 ≤ Aerr := by positivity
  set σk : ℝ := ((N : ℝ) ^ ((1 : ℝ) / 2) * (1 / 48)) ^ (-(k : ℝ)) with hσk
  have hslice : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ (i j : Idx D N)
      (p q : ℕ), wirt p q (fun w' => (fun h' : Idx D N → Idx D N → ℂ =>
        wirt 0 1 (fun w => (G (setEntry h' i j w) : ℂ)) (h' i j)) (setEntry h i j w')) =
      wirt p (q + 1) (fun w => (G (setEntry h i j w) : ℂ)) :=
    fun h hh i j p q => CE_drift_slice D N A η hη0 F hF E₁ E₂ h hh i j p q
  have herr : ∀ i j : Idx D N, ‖(∫ h, wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) *
      starRingEnd ℂ (h i j) ∂μ) - ∑ p ∈ Finset.range (4 + 1), ∑ q ∈ Finset.range (4 + 1 - p),
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          ∫ h, wirt p (q + 1) (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ‖ ≤
      Ke * ((N : ℝ) ^ (-((4 : ℕ) + 2 : ℝ) / 2) * Aerr + Bdet * Real.sqrt (ε + σk)) := by
    intro i j
    have hspec := edgeCut_spec D N A η hη0 E₁ E₂ 2 R i j
    have hFs : ContDiff ℝ (4 + 1 : ℕ) (fun h => (fun h' : Idx D N → Idx D N → ℂ =>
        wirt 0 1 (fun w => (G (setEntry h' i j w) : ℂ)) (h' i j)) (symArr h)) :=
      (CE_drift_contDiff D N A η hη0 F hF E₁ E₂ i j).of_le (by simp)
    have H := HE D N θ μ hμ i j (fun h' : Idx D N → Idx D N → ℂ =>
        wirt 0 1 (fun w => (G (setEntry h' i j w) : ℂ)) (h' i j))
      (edgeCut D N A η E₁ E₂ 2 R i j) (1 / 48) Aerr Bdet ε hFs (hspec.2.2.1 (4 + 1)) hspec.1
      hspec.2.1 (by norm_num) hAerr0 hε0 (by
        intro p q hpq h hh hχ w hw
        rw [hslice h hh i j p q]
        obtain ⟨hA1, hG1⟩ := hspec.2.2.2 h hh (1 / 48) (by norm_num) hR2 (by norm_num) hχ w hw
        refine (HW p q (by omega) D N A η hη0 E₁ E₂ h hh i j w (2 * R) 12 12 (by positivity)
          (by norm_num) (by norm_num) le_rfl hA1 fun r a b ha hb => ⟨(hG1 r a b ha hb).trans
            (by norm_num), (CE_imRes_le _ _ a b).trans ?_⟩).trans_eq rfl
        have := hG1 r a b ha hb
        have := hG1 r b a hb ha
        linarith) (by
        intro p q hpq h hh w
        rw [hslice h hh i j p q]
        exact hBd p q (by omega) h hh i j w)
      (hN₃ N (by omega) L t ht A hA n E₁ E₂ hE₁ hE₂ i j)
    have hsum : ∀ p q : ℕ, (∫ h, wirt p q (fun w' => (fun h' : Idx D N → Idx D N → ℂ =>
        wirt 0 1 (fun w => (G (setEntry h' i j w) : ℂ)) (h' i j)) (setEntry h i j w')) (h i j) ∂μ) =
        ∫ h, wirt p (q + 1) (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ := by
      intro p q
      refine integral_congr_ae ?_
      filter_upwards [hμ.herm] with h hh
      rw [hslice h hh i j p q]
    simp only [hsum] at H
    exact H
  -- the terms of the expansion and the recombination of the second order
  obtain ⟨T, hT⟩ : ∃ T : Idx D N → Idx D N → ℕ → ℕ → ℂ, T = fun i j p q =>
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        ∫ h, wirt p (q + 1) (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ := ⟨_, rfl⟩
  obtain ⟨err, herrdef⟩ : ∃ err : Idx D N → Idx D N → ℂ, err = fun i j =>
      (∫ h, wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (4 + 1), ∑ q ∈ Finset.range (4 + 1 - p), T i j p q := ⟨_, rfl⟩
  obtain ⟨Hh, hHdef⟩ : ∃ Hh : Idx D N → Idx D N → ℂ, Hh = fun i j =>
      ∑ p ∈ Finset.range (4 + 1), ∑ q ∈ Finset.range (4 + 1 - p),
        (if 2 ≤ p + q then T i j p q else 0) := ⟨_, rfl⟩
  have hdrift : ∀ i j : Idx D N, ∫ h, starRingEnd ℂ (h i j) *
        wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ =
      err i j + (varProf D N θ i j : ℂ) *
        (∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) +
        (if i = j then (varProf D N θ i j : ℂ) else 0) *
          (∫ h, wirt 0 2 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) + Hh i j := by
    intro i j
    obtain ⟨-, h11, -, h02⟩ := llClass_ccum_low D N C' θ μ hμ i j
    have e1 : ∫ h, starRingEnd ℂ (h i j) *
        wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ =
        ∫ h, wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) * starRingEnd ℂ (h i j) ∂μ :=
      integral_congr_ae (ae_of_all _ fun h => mul_comm _ _)
    have e2 := CE_split (T i j)
    have h01 : ccum (μ.map fun h => h i j) 0 1 = 0 := CE_ccum01 hμ i j
    have t00 : T i j 0 0 = 0 := by rw [hT]; simp [h01]
    have t10 : T i j 1 0 = (varProf D N θ i j : ℂ) *
        (∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) := by
      rw [hT]; simp [h11]
    have t01 : T i j 0 1 = (if i = j then (varProf D N θ i j : ℂ) else 0) *
        (∫ h, wirt 0 2 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) := by
      rw [hT]; simp [h02]
    rw [e1, herrdef, hHdef]
    simp only []
    rw [e2, t00, t10, t01]
    ring
  have hdiag : ∀ i : Idx D N,
      (∫ h, wirt 0 2 (fun w => (G (setEntry h i i w) : ℂ)) (h i i) ∂μ) =
        ∫ h, wirt 1 1 (fun w => (G (setEntry h i i w) : ℂ)) (h i i) ∂μ := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have hre : ∀ w, (fun w => (G (setEntry h i i w) : ℂ)) w =
        (fun w => (G (setEntry h i i w) : ℂ)) ((w.re : ℝ) : ℂ) := by
      intro w
      have : setEntry h i i w = setEntry h i i ((w.re : ℝ) : ℂ) := by
        funext k l; simp [setEntry]
      simp only [this]
    rw [CE_re_wirt02 _ (CE_slice_contDiff D N A η hη0 F hF E₁ E₂ h hh i i) hre]
  have halg := CE_algebra G μ θ err Hh
    (fun i j => ∫ h, wirt 0 2 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ) hdrift hdiag
  rw [halg]
  -- the bounds of the error terms
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ, Eb = Ke * ((N : ℝ) ^ (-((4 : ℕ) + 2 : ℝ) / 2) * Aerr +
      Bdet * Real.sqrt (ε + σk)) := ⟨_, rfl⟩
  obtain ⟨Tb, hTb⟩ : ∃ Tb : ℝ, Tb = Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (Xg + Bdet * (2 * ε)) :=
    ⟨_, rfl⟩
  have hTb0 : 0 ≤ Tb := by rw [hTb]; positivity
  have herr' : ∀ i j, ‖err i j‖ ≤ Eb := by
    intro i j
    rw [herrdef, hT, hEb]
    exact herr i j
  have hH' : ∀ i j, ‖Hh i j‖ ≤ 15 * Tb := by
    intro i j
    rw [hHdef]
    refine (norm_sum_le _ _).trans ?_
    rw [← CE_count Tb]
    refine Finset.sum_le_sum fun p hp => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun q hq => ?_)
    simp only [Finset.mem_range] at hp hq
    split_ifs with h2
    · rw [hT]
      simp only []
      rw [norm_mul, norm_div]
      have hfac : (1 : ℝ) ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
        rw [Complex.norm_natCast]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Nat.factorial_ne_zero p) (Nat.factorial_ne_zero q))
      have hc := hKc p (q + 1) D N θ μ hμ i j
      have hKcp := (le_abs_self (Kc p (q + 1))).trans (hKcle p (q + 1) (by omega) (by omega))
      have hNp : (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hx1
        have : (3 : ℝ) ≤ ((p + (q + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ p + (q + 1))
        linarith
      have hcc : ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤ Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
        hc.trans (mul_le_mul hKcp hNp (Real.rpow_nonneg hx0.le _) hKcm0)
      have hII := hI p q (by omega) i j
      have hdiv : ‖ccum (μ.map fun h => h i j) p (q + 1)‖ /
          ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ ≤ Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
        (div_le_self (norm_nonneg _) hfac).trans hcc
      rw [hTb]
      exact mul_le_mul hdiv hII (norm_nonneg _) (by positivity)
    · rw [norm_zero]; exact hTb0
  have hsum : ‖∑ i : Idx D N, ∑ j : Idx D N, (-(1 / 2 : ℂ)) * driftWt i j * (err i j + Hh i j)‖ ≤
      ((D : ℝ) * N) ^ 2 * (Eb + 15 * Tb) := by
    have hpt : ∀ i j : Idx D N,
        ‖(-(1 / 2 : ℂ)) * driftWt i j * (err i j + Hh i j)‖ ≤ Eb + 15 * Tb := by
      intro i j
      have hw : ‖(-(1 / 2 : ℂ)) * driftWt i j‖ ≤ 1 := by
        simp only [driftWt]
        split_ifs <;> norm_num
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hw).trans ?_
      exact (norm_add_le _ _).trans (add_le_add (herr' i j) (hH' i j))
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => hpt i j)).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl
  refine hsum.trans ?_
  -- the four pieces as powers of `N`
  clear_value c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ x₀ D'' b ε
  have hyC : y ^ Cs = (N : ℝ) ^ ((2 * σ + σ / 2) * Cs) := by
    rw [hydef, ← Real.rpow_mul hx0.le]
  have hηinv : η⁻¹ = (N : ℝ) ^ ((2 / 3 : ℝ) + σ) := by
    rw [hηdef, ← Real.rpow_neg hx0.le]; ring_nf
  have hA1 : Aerr ≤ Kw * (Cs * (1 + 2 * Kχ) ^ Cs) * 12 * 12 ^ 5 *
      (N : ℝ) ^ ((2 * σ + σ / 2) * Cs) := by
    have h1 : (1 + 2 * R) ^ Cs ≤ (1 + 2 * Kχ) ^ Cs * y ^ Cs := by
      have := CE_pow_le (K := 2 * Kχ) (y := y) (c := Cs) (by linarith) hy1 (by linarith)
      rwa [hRdef, ← mul_assoc]
    rw [hAerr, ← hyC]
    have : 0 ≤ Kw * Cs * 12 * 12 ^ 5 := by positivity
    calc Kw * (Cs * (1 + 2 * R) ^ Cs) * 12 * 12 ^ 5 =
          (Kw * Cs * 12 * 12 ^ 5) * (1 + 2 * R) ^ Cs := by ring
      _ ≤ (Kw * Cs * 12 * 12 ^ 5) * ((1 + 2 * Kχ) ^ Cs * y ^ Cs) := by gcongr
      _ = Kw * (Cs * (1 + 2 * Kχ) ^ Cs) * 12 * 12 ^ 5 * y ^ Cs := by ring
  have haD1 : aD ≤ 2 * D * (N : ℝ) ^ (2 : ℝ) := by
    have e : (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) / η = (N : ℝ) ^ (2 * σ) := by
      rw [div_eq_mul_inv, hηinv, ← Real.rpow_add hx0]; ring_nf
    have h2 : (N : ℝ) ^ (2 * σ) ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 2 * σ ≤ 1)
      simpa using this
    calc aD = 2 * D * N * ((N : ℝ) ^ (-(2 / 3 : ℝ) + σ) / η) := by
          rw [haD]; push_cast; ring
      _ = 2 * D * N * (N : ℝ) ^ (2 * σ) := by rw [e]
      _ ≤ 2 * D * N * N := by gcongr
      _ = 2 * D * (N : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
  have hB1 : Bdet ≤ KB * (N : ℝ) ^ b := by
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have h1 : (1 + aD) ^ Cs ≤ (1 + 2 * D) ^ Cs * ((N : ℝ) ^ (2 : ℝ)) ^ Cs :=
      (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)).trans
        (CE_pow_le (by positivity) hN2 (by linarith))
    have h2 : ((N : ℝ) ^ (2 : ℝ)) ^ Cs = (N : ℝ) ^ (2 * Cs) := by
      rw [← Real.rpow_mul hx0.le]
    have h3 : η⁻¹ * η⁻¹ ^ 5 ≤ (N : ℝ) ^ (5 : ℝ) := by
      rw [← pow_succ', hηinv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; nlinarith)
    have h4 : 0 ≤ Kw * Cs := by positivity
    calc Bdet = Kw * Cs * (1 + aD) ^ Cs * (η⁻¹ * η⁻¹ ^ 5) := by rw [hBdet]; ring
      _ ≤ Kw * Cs * ((1 + 2 * D) ^ Cs * ((N : ℝ) ^ (2 : ℝ)) ^ Cs) * (N : ℝ) ^ (5 : ℝ) := by
          gcongr
      _ = KB * (N : ℝ) ^ b := by
          rw [h2, hKB, hb, Real.rpow_add hx0]; ring
  have hS1 : Real.sqrt (ε + σk) ≤ Real.sqrt (1 + 48 ^ k) * (N : ℝ) ^ (-D'' / 2) := by
    have h1 : σk ≤ 48 ^ k * ε := by rw [hεdef]; exact CE_sigma_le hx1 k hk2
    have h2 : ε + σk ≤ (1 + 48 ^ k) * ε := by linarith
    have h3 : Real.sqrt ε = (N : ℝ) ^ (-D'' / 2) := by
      rw [Real.sqrt_eq_rpow, hεdef, ← Real.rpow_mul hx0.le]; ring_nf
    calc Real.sqrt (ε + σk) ≤ Real.sqrt ((1 + 48 ^ k) * ε) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (1 + 48 ^ k) * Real.sqrt ε := Real.sqrt_mul (by positivity) _
      _ = _ := by rw [h3]
  have hX1 : Xg ≤ Kw * (Cs * (1 + KA) ^ Cs) * KG * 2 ^ 5 *
      ((N : ℝ) ^ ((2 * σ + σ / 2) * Cs) * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) := by
    have h1 : (1 + KA * y) ^ Cs ≤ (1 + KA) ^ Cs * y ^ Cs := CE_pow_le hKA.le hy1 (by linarith)
    rw [hXg, hΓI, ← hyC]
    have : 0 ≤ Kw * Cs * KG * 2 ^ 5 * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) := by positivity
    calc Kw * (Cs * (1 + KA * y) ^ Cs) * (KG * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) * 2 ^ 5 =
          (Kw * Cs * KG * 2 ^ 5 * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) * (1 + KA * y) ^ Cs := by
          ring
      _ ≤ (Kw * Cs * KG * 2 ^ 5 * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) *
          ((1 + KA) ^ Cs * y ^ Cs) := by gcongr
      _ = _ := by ring
  have h43 : (N : ℝ) ^ (-((4 : ℕ) + 2 : ℝ) / 2) = (N : ℝ) ^ (-3 : ℝ) := by norm_num
  have hDN : ((D : ℝ) * N) ^ 2 = (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
  have hpos : ∀ e : ℝ, 0 ≤ (N : ℝ) ^ e := fun e => Real.rpow_nonneg hx0.le e
  have hP1 : (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * ((N : ℝ) ^ (-3 : ℝ) * Aerr)) ≤
      c₁ * (N : ℝ) ^ e₁ := by
    have := hpos (2 : ℝ); have := hpos (-3 : ℝ)
    calc (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * ((N : ℝ) ^ (-3 : ℝ) * Aerr)) ≤
          (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * ((N : ℝ) ^ (-3 : ℝ) *
            (Kw * (Cs * (1 + 2 * Kχ) ^ Cs) * 12 * 12 ^ 5 *
              (N : ℝ) ^ ((2 * σ + σ / 2) * Cs)))) := by gcongr
      _ = c₁ * (N : ℝ) ^ e₁ := by
          rw [hc₁, he₁, Real.rpow_add hx0 (2 + -3) ((2 * σ + σ / 2) * Cs),
            Real.rpow_add hx0 2 (-3)]
          ring
  have hP2 : (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * (Bdet * Real.sqrt (ε + σk))) ≤
      c₂ * (N : ℝ) ^ e₂ := by
    have := hpos (2 : ℝ); have := hpos b
    calc (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * (Bdet * Real.sqrt (ε + σk))) ≤
          (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * ((KB * (N : ℝ) ^ b) *
            (Real.sqrt (1 + 48 ^ k) * (N : ℝ) ^ (-D'' / 2)))) := by
          gcongr
      _ = c₂ * (N : ℝ) ^ e₂ := by
          rw [hc₂, he₂, Real.rpow_add hx0 (2 + b) (-D'' / 2), Real.rpow_add hx0 2 b]
          ring
  have hP3 : (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * Xg)) ≤
      c₃ * (N : ℝ) ^ e₃ := by
    have := hpos (2 : ℝ); have := hpos (-(3 / 2 : ℝ))
    calc (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * Xg)) ≤
          (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) *
            (Kw * (Cs * (1 + KA) ^ Cs) * KG * 2 ^ 5 *
              ((N : ℝ) ^ ((2 * σ + σ / 2) * Cs) * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2))))) := by
          gcongr
      _ = c₃ * (N : ℝ) ^ e₃ := by
          rw [hc₃, he₃, Real.rpow_add hx0 (2 + -(3 / 2))
              ((2 * σ + σ / 2) * Cs + (-(1 / 3 : ℝ) + σ + σ / 2)),
            Real.rpow_add hx0 2 (-(3 / 2)),
            Real.rpow_add hx0 ((2 * σ + σ / 2) * Cs) (-(1 / 3 : ℝ) + σ + σ / 2)]
          ring
  have hP4 : (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) *
      (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (Bdet * (2 * ε)))) ≤ c₄ * (N : ℝ) ^ e₄ := by
    have := hpos (2 : ℝ); have := hpos (-(3 / 2 : ℝ))
    calc (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) *
          (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (Bdet * (2 * ε)))) ≤
          (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) *
          (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ((KB * (N : ℝ) ^ b) * (2 * ε)))) := by
          gcongr
      _ = c₄ * (N : ℝ) ^ e₄ := by
          rw [hc₄, he₄, hεdef, Real.rpow_add hx0 (2 + -(3 / 2)) (b + -D''),
            Real.rpow_add hx0 2 (-(3 / 2)), Real.rpow_add hx0 b (-D'')]
          ring
  have hm1 := hM₁ N (by omega)
  have hm2 := hM₂ N (by omega)
  have hm3 := hM₃ N (by omega)
  have hm4 := hM₄ N (by omega)
  calc ((D : ℝ) * N) ^ 2 * (Eb + 15 * Tb) =
        (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * ((N : ℝ) ^ (-3 : ℝ) * Aerr)) +
        (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (Ke * (Bdet * Real.sqrt (ε + σk))) +
        (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) * (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * Xg)) +
        (D : ℝ) ^ 2 * (N : ℝ) ^ (2 : ℝ) *
          (15 * (Kcm * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (Bdet * (2 * ε)))) := by
        rw [hDN, hEb, hTb, h43]; ring
    _ ≤ c₁ * (N : ℝ) ^ e₁ + c₂ * (N : ℝ) ^ e₂ + c₃ * (N : ℝ) ^ e₃ + c₄ * (N : ℝ) ^ e₄ := by
        linarith
    _ ≤ (N : ℝ) ^ x₀ := by linarith

/-- (4.9) [eq:prodnGt] with (4.14) [eq:Fk] at `l = 4`: uniformly in `t ≥ 0`, `L`, `A` and the
windows within `N^{-2/3+σ}` of `E⁺`, the derivative of `t ↦ E_{H_t} F(A_t)` differs from
`(e^{-t}/2) E ℱ₂` by at most `N^{1/6 + (3C_* + 3)σ}`, `C_* = max(C_6, 1)`, `η = N^{-2/3-σ}`. -/
theorem edgeDeriv_sub_F2_le (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) (n : ℕ)
    (F : (Fin n → ℝ) → ℝ) (CF : ℕ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hCF : ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) :
    ∀ σ : ℝ, 0 < σ → σ < 1 / 12 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) → ∀ E₁ E₂ : Fin n → ℝ,
      (∀ m, |E₁ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      (∀ m, |E₂ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
        ‖entryDeriv (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂) (ouMatLaw D N L t) -
            (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) *
              entryF2 (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂) (ouMatLaw D N L t)‖ ≤
          (N : ℝ) ^ ((1 / 6 : ℝ) + (3 * max (CF 6) 1 + 3) * σ) := by
  exact CE_deriv_main D hD δA hδA C n F CF hF hCF

end RBMTransitionEdge

end
