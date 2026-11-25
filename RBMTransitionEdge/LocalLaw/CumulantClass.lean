module

public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.Prob.Cumulant
public import RBMTransitionEdge.Prob.CumulantExpansion
public import RBMTransitionEdge.Tools.Resolvent

@[expose] public section

/-!
# Cumulants of the class and the one-entry expansion

(2.27) [eq:bdd_cumu] and the low cumulants for the class `LLClass`, the expansion of Lemma 2.11
[lem:complex_cumu] in one entry, and the stability of resolvent entries under a one-entry substitution.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The array `h` with the entry `(i, j)` replaced by `w` and `(j, i)` by `w̄` when `i ≠ j`, and
with the diagonal entry `(i, i)` replaced by `Re w` when `i = j`: the one-entry substitution of
Lemma 2.11 [lem:complex_cumu] for a Hermitian array. -/
def setEntry {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w : ℂ) :
    Idx D N → Idx D N → ℂ :=
  fun k l => if i = j then (if k = i ∧ l = i then ((w.re : ℝ) : ℂ) else h k l)
    else if k = i ∧ l = j then w else if k = j ∧ l = i then starRingEnd ℂ w else h k l

/-! ### Substituting one entry -/

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma CC_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
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

/-- `setEntry` only depends on the array outside the pair `{(i, j), (j, i)}`. -/
private lemma CC_setEntry_congr {D N : ℕ} {a b : Idx D N → Idx D N → ℂ} (i j : Idx D N) (w : ℂ)
    (hab : ∀ k l, ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) → a k l = b k l) :
    setEntry a i j w = setEntry b i j w := by
  funext k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · simp [setEntry, hkl]
    · simp only [setEntry, hkl, ↓reduceIte]
      exact hab k l (by tauto)
  · by_cases h1 : k = i ∧ l = j
    · simp [setEntry, hd, h1]
    · by_cases h2 : k = j ∧ l = i
      · simp [setEntry, hd, h2]
      · simp only [setEntry, hd, h1, h2, ↓reduceIte]
        exact hab k l (by tauto)

/-! ### The entries on and above the diagonal -/

/-- The index pairs on and above the diagonal in the lexicographic order. -/
private abbrev CC_U (D N : ℕ) := {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}

/-- The Hermitian array whose entries on and above the diagonal are the given family. -/
private def CC_fill {D N : ℕ} (c : CC_U D N → ℂ) : Idx D N → Idx D N → ℂ :=
  fun k l => if hkl : toLex k ≤ toLex l then c ⟨(k, l), hkl⟩
    else starRingEnd ℂ (c ⟨(l, k), (not_le.mp hkl).le⟩)

/-- The upper-triangular representative of the pair `{(i, j), (j, i)}`. -/
private def CC_q0 {D N : ℕ} (i j : Idx D N) : CC_U D N :=
  if hij : toLex i ≤ toLex j then ⟨(i, j), hij⟩ else ⟨(j, i), (not_le.mp hij).le⟩

/-- The representative `CC_q0 i j` is one of the pairs `(i, j)`, `(j, i)`. -/
private lemma CC_q0_mem {D N : ℕ} (i j : Idx D N) :
    (CC_q0 i j).1 = (i, j) ∨ (CC_q0 i j).1 = (j, i) := by
  unfold CC_q0
  split_ifs <;> simp

/-- The family of the entries on and above the diagonal, with the entry of the pair set to `0`. -/
private def CC_R {D N : ℕ} (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : CC_U D N → ℂ :=
  fun q => if q = CC_q0 i j then 0 else h q.1.1 q.1.2

/-- Filling in a Hermitian array from its entries on and above the diagonal gives the array back. -/
private lemma CC_fill_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    CC_fill (fun q : CC_U D N => h q.1.1 q.1.2) = h := by
  funext k l
  unfold CC_fill
  split_ifs with hkl
  · rfl
  · simpa [Complex.star_def] using hh.apply k l

/-- A pair outside `{(i, j), (j, i)}` is not the representative `CC_q0 i j`. -/
private lemma CC_ne_q0 {D N : ℕ} (i j a b : Idx D N) (hle : toLex a ≤ toLex b)
    (hab : ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i))) :
    (⟨(a, b), hle⟩ : CC_U D N) ≠ CC_q0 i j := by
  intro heq
  have h1 : (a, b) = (CC_q0 i j).1 := congrArg Subtype.val heq
  rcases CC_q0_mem i j with h2 | h2
  · rw [h2] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact hab (Or.inl ⟨rfl, rfl⟩)
  · rw [h2] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact hab (Or.inr ⟨rfl, rfl⟩)

/-- For a Hermitian array, the entry-`(i, j)` substitution is determined by the family `CC_R`. -/
private lemma CC_setEntry_eq {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    setEntry h i j w = setEntry (CC_fill (CC_R i j h)) i j w := by
  have hfill := CC_fill_self h hh
  calc setEntry h i j w = setEntry (CC_fill (fun q : CC_U D N => h q.1.1 q.1.2)) i j w := by
        rw [hfill]
    _ = setEntry (CC_fill (CC_R i j h)) i j w := by
      refine CC_setEntry_congr i j w fun k l hkl => ?_
      unfold CC_fill
      split_ifs with hle
      · simp only [CC_R]
        simp only [CC_ne_q0 i j k l hle hkl, ↓reduceIte]
      · simp only [CC_R]
        simp only [CC_ne_q0 i j l k (not_le.mp hle).le (by tauto), ↓reduceIte]

/-- The family `CC_R` is independent of the entry `h_{ij}`. -/
private lemma CC_indep {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) :
    IndepFun (CC_R i j) (fun h => h i j) μ := by
  have := hμ.prob
  set q₀ := CC_q0 i j with hq₀
  set S : Finset (CC_U D N) := {q₀} with hS
  set T : Finset (CC_U D N) := Finset.univ.erase q₀ with hT
  have hdisj : Disjoint S T := by simp [S, T]
  have hmeas : ∀ q : CC_U D N, Measurable fun h : Idx D N → Idx D N → ℂ => h q.1.1 q.1.2 :=
    fun q => (measurable_pi_apply _).comp (measurable_pi_apply _)
  have h1 := hμ.indep.indepFun_finset S T hdisj hmeas
  have hq₀S : q₀ ∈ S := by simp [S]
  let ψ : (↥T → ℂ) → CC_U D N → ℂ := fun c q => if hq : q ∈ T then c ⟨q, hq⟩ else 0
  let φ : (↥S → ℂ) → ℂ := fun c =>
    if toLex i ≤ toLex j then c ⟨q₀, hq₀S⟩ else starRingEnd ℂ (c ⟨q₀, hq₀S⟩)
  have hψ : Measurable ψ := by
    refine measurable_pi_iff.mpr fun q => ?_
    by_cases hq : q ∈ T
    · simp only [ψ, hq, dite_true]
      exact measurable_pi_apply _
    · simp only [ψ, hq, dite_false]
      exact measurable_const
  have hφ : Measurable φ := by
    by_cases hij : toLex i ≤ toLex j
    · simp only [φ, hij, ↓reduceIte]
      exact measurable_pi_apply _
    · simp only [φ, hij, ↓reduceIte]
      exact Complex.continuous_conj.measurable.comp (measurable_pi_apply _)
  have h2 := h1.symm.comp hψ hφ
  refine h2.congr (Eventually.of_forall fun h => ?_) ?_
  · funext q
    by_cases hq : q = q₀
    · simp [ψ, T, CC_R, hq, Function.comp, ← hq₀]
    · simp [ψ, T, CC_R, hq, Function.comp, ← hq₀]
  · filter_upwards [hμ.herm] with h hh
    simp only [Function.comp, φ, q₀, CC_q0]
    by_cases hij : toLex i ≤ toLex j
    · simp [hij]
    · simpa [hij, Complex.star_def] using hh.apply i j

/-- Each entry of `CC_fill c` is a smooth function of the family `c`. -/
private lemma CC_contDiff_fill {D N : ℕ} (k l : Idx D N) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun c : CC_U D N → ℂ => CC_fill c k l) := by
  unfold CC_fill
  by_cases hkl : toLex k ≤ toLex l
  · simp only [hkl, dite_true]
    exact (contDiff_apply ℝ (fun _ : CC_U D N => ℂ) _)
  · simp only [hkl, dite_false]
    exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ : CC_U D N => ℂ) _)

/-- The array `setEntry (CC_fill r) i j w` is a smooth function of `(r, w)`. -/
private lemma CC_contDiff_theta {D N : ℕ} (i j : Idx D N) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : (CC_U D N → ℂ) × ℂ => setEntry (CC_fill p.1) i j p.2) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hre : ContDiff ℝ n (fun p : (CC_U D N → ℂ) × ℂ => ((p.2.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
  have hw : ContDiff ℝ n (fun p : (CC_U D N → ℂ) × ℂ => p.2) := contDiff_snd
  have hcw : ContDiff ℝ n (fun p : (CC_U D N → ℂ) × ℂ => starRingEnd ℂ p.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  have hf : ContDiff ℝ n (fun p : (CC_U D N → ℂ) × ℂ => CC_fill p.1 k l) :=
    (CC_contDiff_fill k l n).comp contDiff_fst
  simp only [setEntry]
  split_ifs <;> assumption

/-! ### Derivatives in the entry, with the other entries as parameters -/

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Wirtinger derivative `∂_w` of a function of `(r, w)` in the variable `w`. -/
private def CC_pdW (G : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun x => (fderiv ℝ G x (0, 1) - Complex.I * fderiv ℝ G x (0, Complex.I)) / 2

/-- The Wirtinger derivative `∂_{w̄}` of a function of `(r, w)` in the variable `w`. -/
private def CC_pdWbar (G : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun x => (fderiv ℝ G x (0, 1) + Complex.I * fderiv ℝ G x (0, Complex.I)) / 2

/-- The real derivative of `w ↦ G (r, w)` is the derivative of `G` along `(0, v)`. -/
private lemma CC_fderiv_slice (G : E × ℂ → ℂ) (r : E) (w : ℂ)
    (hG : DifferentiableAt ℝ G (r, w)) (v : ℂ) :
    fderiv ℝ (fun w' => G (r, w')) w v = fderiv ℝ G (r, w) (0, v) := by
  have h1 : HasFDerivAt (fun w' : ℂ => (r, w')) (ContinuousLinearMap.inr ℝ E ℂ) w :=
    hasFDerivAt_prodMk_right r w
  have h2 := hG.hasFDerivAt.comp w h1
  have h3 : fderiv ℝ (fun w' => G (r, w')) w = _ := h2.fderiv
  rw [h3]
  simp

/-- `∂_w` of a slice `w ↦ G (r, w)` is the slice of the partial derivative `CC_pdW G`. -/
private lemma CC_dW_slice (G : E × ℂ → ℂ) (hG : Differentiable ℝ G) (r : E) :
    dW (fun w => G (r, w)) = fun w => CC_pdW G (r, w) := by
  funext w
  simp only [dW, CC_pdW]
  rw [CC_fderiv_slice G r w (hG _), CC_fderiv_slice G r w (hG _)]

/-- `∂_{w̄}` of a slice `w ↦ G (r, w)` is the slice of the partial derivative `CC_pdWbar G`. -/
private lemma CC_dWbar_slice (G : E × ℂ → ℂ) (hG : Differentiable ℝ G) (r : E) :
    dWbar (fun w => G (r, w)) = fun w => CC_pdWbar G (r, w) := by
  funext w
  simp only [dWbar, CC_pdWbar]
  rw [CC_fderiv_slice G r w (hG _), CC_fderiv_slice G r w (hG _)]

/-- `CC_pdW G` is `C^n` if `G` is `C^{n+1}`. -/
private lemma CC_pdW_contDiff {G : E × ℂ → ℂ} {n : ℕ} (hG : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (n : WithTop ℕ∞) (CC_pdW G) := by
  have hd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by push_cast; exact le_rfl)
  unfold CC_pdW
  exact ((hd.clm_apply contDiff_const).sub (contDiff_const.mul (hd.clm_apply contDiff_const))).div_const 2

/-- `CC_pdWbar G` is `C^n` if `G` is `C^{n+1}`. -/
private lemma CC_pdWbar_contDiff {G : E × ℂ → ℂ} {n : ℕ}
    (hG : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (n : WithTop ℕ∞) (CC_pdWbar G) := by
  have hd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by push_cast; exact le_rfl)
  unfold CC_pdWbar
  exact ((hd.clm_apply contDiff_const).add (contDiff_const.mul (hd.clm_apply contDiff_const))).div_const 2

/-- Iterating a slice-compatible derivative operator. -/
private lemma CC_iter (pd : (E × ℂ → ℂ) → (E × ℂ → ℂ)) (d : (ℂ → ℂ) → (ℂ → ℂ))
    (h1 : ∀ (n : ℕ) (G : E × ℂ → ℂ), ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G →
      ContDiff ℝ (n : WithTop ℕ∞) (pd G))
    (h2 : ∀ (G : E × ℂ → ℂ), ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) G → ∀ r : E,
      d (fun w => G (r, w)) = fun w => pd G (r, w)) :
    ∀ (q n : ℕ) (G : E × ℂ → ℂ), ContDiff ℝ ((n + q : ℕ) : WithTop ℕ∞) G →
      ContDiff ℝ (n : WithTop ℕ∞) (pd^[q] G) ∧
        ∀ r : E, d^[q] (fun w => G (r, w)) = fun w => (pd^[q] G) (r, w) := by
  intro q
  induction q with
  | zero =>
    intro n G hG
    exact ⟨hG, fun r => rfl⟩
  | succ q ih =>
    intro n G hG
    have hG' : ContDiff ℝ ((n + q + 1 : ℕ) : WithTop ℕ∞) G := hG
    have hpd : ContDiff ℝ ((n + q : ℕ) : WithTop ℕ∞) (pd G) := h1 (n + q) G hG'
    obtain ⟨c, e⟩ := ih n (pd G) hpd
    refine ⟨by simpa [Function.iterate_succ_apply] using c, fun r => ?_⟩
    have hG1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) G :=
      hG'.of_le (by exact_mod_cast Nat.le_add_left 1 (n + q))
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h2 G hG1 r]
    exact e r

/-- The Wirtinger derivatives `F^{(p,q)}(r, ·)(w)` of a `C^{l+1}` function of `(r, w)` are jointly
continuous in `(r, w)` for `p + q ≤ l + 1`. -/
private lemma CC_wirt_continuous (G : E × ℂ → ℂ) (l : ℕ)
    (hG : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) G) (p q : ℕ) (hpq : p + q ≤ l + 1) :
    Continuous (fun x : E × ℂ => wirt p q (fun w => G (x.1, w)) x.2) := by
  have hq : (l + 1 - q) + q = l + 1 := by omega
  have hG1 : ContDiff ℝ ((l + 1 - q + q : ℕ) : WithTop ℕ∞) G := by rw [hq]; exact hG
  obtain ⟨c1, e1⟩ := CC_iter CC_pdWbar dWbar (fun n G hG => CC_pdWbar_contDiff hG)
    (fun G hG r => CC_dWbar_slice G (hG.differentiable (by simp)) r) q (l + 1 - q) G hG1
  have hp : (l + 1 - q - p) + p = l + 1 - q := by omega
  have hc1 : ContDiff ℝ ((l + 1 - q - p + p : ℕ) : WithTop ℕ∞) (CC_pdWbar^[q] G) := by
    rw [hp]; exact c1
  obtain ⟨c2, e2⟩ := CC_iter CC_pdW dW (fun n G hG => CC_pdW_contDiff hG)
    (fun G hG r => CC_dW_slice G (hG.differentiable (by simp)) r) p (l + 1 - q - p)
    (CC_pdWbar^[q] G) hc1
  have : (fun x : E × ℂ => wirt p q (fun w => G (x.1, w)) x.2) = CC_pdW^[p] (CC_pdWbar^[q] G) := by
    funext x
    unfold wirt
    rw [e1 x.1, e2 x.1]
  rw [this]
  exact c2.continuous

end Param

/-- Integrating a function of `(R, X)` for independent `R` and `X`: first over `X`, then over `R`. -/
private lemma CC_cond_integral {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → E} {X : Ω → ℂ}
    (hR : Measurable R) (hX : Measurable X) (hind : IndepFun R X μ) {Ψ : E × ℂ → ℂ}
    (hΨ : Integrable Ψ ((μ.map R).prod (μ.map X))) :
    ∫ ω, Ψ (R ω, X ω) ∂μ = ∫ c, (∫ x, Ψ (c, x) ∂(μ.map X)) ∂(μ.map R) := by
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hX.aemeasurable).mp hind
  have hm : AEMeasurable (fun ω => (R ω, X ω)) μ := (hR.prodMk hX).aemeasurable
  have hΨ' : AEStronglyMeasurable Ψ (μ.map fun ω => (R ω, X ω)) := by
    rw [hjoint]; exact hΨ.aestronglyMeasurable
  rw [← integral_map (φ := fun ω => (R ω, X ω)) (f := Ψ) hm hΨ', hjoint, integral_prod _ hΨ]

/-! ### Cumulants of the class -/

/-- The variable of the `i`-th slot of `ccum μ p q`: `h` in the first `p` slots, `h̄` after. -/
private def CC_X (p q : ℕ) : Fin (p + q) → ℂ → ℂ :=
  fun i => if (i : ℕ) < p then (fun z => z) else (fun z => starRingEnd ℂ z)

/-- `ccum μ p q` is the joint cumulant of the variables `CC_X p q`. -/
private lemma CC_ccum_eq (μ : Measure ℂ) (p q : ℕ) : ccum μ p q = jointCum μ (CC_X p q) := rfl

/-- Each variable `CC_X p q k` has the modulus of `z`. -/
private lemma CC_norm_X (p q : ℕ) (k : Fin (p + q)) (z : ℂ) : ‖CC_X p q k z‖ = ‖z‖ := by
  unfold CC_X
  split_ifs <;> simp

/-- A product of `|B|` of the variables has modulus `|z|^{|B|}`. -/
private lemma CC_norm_prod_X (p q : ℕ) (B : Finset (Fin (p + q))) (z : ℂ) :
    ‖∏ k ∈ B, CC_X p q k z‖ = ‖z‖ ^ B.card := by
  rw [norm_prod, Finset.prod_congr rfl fun k _ => CC_norm_X p q k z, Finset.prod_const]

/-- The partition-sum bound on `ccum μ p q` from bounds `E b` on the moments `∫ |z|^b dμ`. -/
private lemma CC_jointCum_le (μ : Measure ℂ) (p q : ℕ) (E : ℕ → ℝ)
    (hE : ∀ B : Finset (Fin (p + q)), ∫ z, ‖z‖ ^ B.card ∂μ ≤ E B.card) :
    ‖ccum μ p q‖ ≤ ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
      ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, E B.card := by
  rw [CC_ccum_eq]
  unfold jointCum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
    norm_prod]
  gcongr with B hB
  exact (norm_integral_le_integral_norm _).trans (by
    simp only [CC_norm_prod_X]
    exact hE B)

/-- The full index set of `Fin (n + 1)` is not empty. -/
private lemma CC_ne_bot (n : ℕ) : (Finset.univ : Finset (Fin (n + 1))) ≠ ⊥ := by
  simp
  exact Finset.univ_nonempty.ne_empty

/-- The only set partition of `Fin 1` is the one with a single block. -/
private lemma CC_part_one (π : Finpartition (Finset.univ : Finset (Fin 1))) :
    π = Finpartition.indiscrete (CC_ne_bot 0) := by
  have hall : ∀ B : Finset (Fin 1), B.Nonempty → B = Finset.univ := by decide
  refine Finpartition.ext ?_
  rw [Finpartition.indiscrete_parts]
  ext B
  simp only [Finset.mem_singleton]
  constructor
  · intro hB
    exact hall B (π.nonempty_of_mem_parts hB)
  · rintro rfl
    obtain ⟨t, ht, -⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
    exact hall t (π.nonempty_of_mem_parts ht) ▸ ht

/-- The set partitions of `Fin 2` are the one-block partition and the partition into singletons. -/
private lemma CC_part_two (π : Finpartition (Finset.univ : Finset (Fin 2))) :
    π = Finpartition.indiscrete (CC_ne_bot 1) ∨ π = ⊥ := by
  by_cases hu : (Finset.univ : Finset (Fin 2)) ∈ π.parts
  · left
    refine Finpartition.ext ?_
    rw [Finpartition.indiscrete_parts]
    ext B
    simp only [Finset.mem_singleton]
    constructor
    · intro hB
      obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hB
      exact π.eq_of_mem_parts hB hu hx (Finset.mem_univ x)
    · rintro rfl
      exact hu
  · right
    refine Finpartition.ext ?_
    rw [Finpartition.parts_bot]
    have hsing : ∀ B ∈ π.parts, B = {0} ∨ B = {1} := by
      intro B hB
      have hne : B ≠ Finset.univ := fun h => hu (h ▸ hB)
      have hn := π.nonempty_of_mem_parts hB
      revert hne hn
      generalize B = B'
      revert B'
      decide
    ext B
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_univ, true_and]
    constructor
    · intro hB
      rcases hsing B hB with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨t, ht, hx⟩ := π.exists_mem (Finset.mem_univ a)
      rcases hsing t ht with rfl | rfl
      · have : a = 0 := by simpa using hx
        subst this; exact ht
      · have : a = 1 := by simpa using hx
        subst this; exact ht

/-- The joint cumulant of one variable is its mean. -/
private lemma CC_jointCum_one (μ : Measure ℂ) (X : Fin 1 → ℂ → ℂ) :
    jointCum μ X = ∫ z, X 0 z ∂μ := by
  unfold jointCum
  rw [Finset.sum_eq_single (Finpartition.indiscrete (CC_ne_bot 0))
    (fun π _ hπ => absurd (CC_part_one π) hπ) (by simp)]
  simp

/-- The joint cumulant of two variables is `E X₀ X₁ - E X₀ E X₁`. -/
private lemma CC_jointCum_two (μ : Measure ℂ) (X : Fin 2 → ℂ → ℂ) :
    jointCum μ X = (∫ z, X 0 z * X 1 z ∂μ) - (∫ z, X 0 z ∂μ) * ∫ z, X 1 z ∂μ := by
  unfold jointCum
  have hne : (Finpartition.indiscrete (CC_ne_bot 1) : Finpartition (Finset.univ : Finset (Fin 2))) ≠ ⊥ := by
    intro h
    have := congrArg (fun π : Finpartition (Finset.univ : Finset (Fin 2)) => π.parts.card) h
    simp at this
  have hU : (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin 2)))) =
      {Finpartition.indiscrete (CC_ne_bot 1), ⊥} := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact CC_part_two π
  rw [hU, Finset.sum_pair hne]
  simp [Finpartition.parts_bot, Finset.prod_map, Fin.prod_univ_two, sub_eq_add_neg]

/-- Values of the variables `CC_X` for the pairs `(1, 0)`, `(2, 0)`, `(0, 2)`, `(1, 1)`. -/
private lemma CC_X_10 (z : ℂ) : CC_X 1 0 0 z = z := by simp [CC_X]
private lemma CC_X_20 (k : Fin 2) (z : ℂ) : CC_X 2 0 k z = z := by
  fin_cases k <;> simp [CC_X]
private lemma CC_X_02 (k : Fin 2) (z : ℂ) : CC_X 0 2 k z = starRingEnd ℂ z := by
  fin_cases k <;> simp [CC_X]
private lemma CC_X_11_0 (z : ℂ) : CC_X 1 1 0 z = z := by simp [CC_X]
private lemma CC_X_11_1 (z : ℂ) : CC_X 1 1 1 z = starRingEnd ℂ z := by simp [CC_X]

/-- (2.27) [eq:bdd_cumu] for the class `LLClass`: for fixed `p, q`, every `(p, q)`-cumulant of
every entry is at most `K N^{-(p+q)/2}`, with `K` depending on `p`, `q` and `C` only. -/
theorem llClass_ccum_le (C : ℕ → ℝ) (p q : ℕ) :
    ∃ K : ℝ, ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)), LLClass D N C θ μ →
      ∀ i j : Idx D N,
        ‖ccum (μ.map fun h => h i j) p q‖ ≤ K * (N : ℝ) ^ (-(((p + q : ℕ) : ℝ) / 2)) := by
  refine ⟨∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
    ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, C B.card, ?_⟩
  intro D N θ μ hμ i j
  have := hμ.prob
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos i.2
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hmom : ∀ b : ℕ, ∫ z, ‖z‖ ^ b ∂(μ.map fun h : Idx D N → Idx D N → ℂ => h i j) ≤
      C b * (N : ℝ) ^ (-((b : ℝ) / 2)) := by
    intro b
    rw [integral_map (f := fun z : ℂ => ‖z‖ ^ b) hmeas.aemeasurable
      (continuous_norm.pow b).aestronglyMeasurable]
    exact hμ.moments b i j
  refine (CC_jointCum_le _ p q (fun b => C b * (N : ℝ) ^ (-((b : ℝ) / 2)))
    fun B => hmom B.card).trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [mul_assoc, Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hN]
  congr 3
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Nat.cast_sum, π.sum_card_parts]
  simp

/-- The low-order cumulants of the class (the display before (2.27) [eq:bdd_cumu] with the
profile `S_θ`): `𝒞^{(1,0)}(h_{ij}) = 0`, `𝒞^{(1,1)}(h_{ij}) = (S_θ)_{ij}` and
`𝒞^{(2,0)}(h_{ij}) = 𝒞^{(0,2)}(h_{ij}) = (S_θ)_{ij} δ_{ij}`. -/
theorem llClass_ccum_low (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (i j : Idx D N) :
    ccum (μ.map fun h => h i j) 1 0 = 0 ∧
      ccum (μ.map fun h => h i j) 1 1 = (varProf D N θ i j : ℂ) ∧
      ccum (μ.map fun h => h i j) 2 0 = (if i = j then (varProf D N θ i j : ℂ) else 0) ∧
      ccum (μ.map fun h => h i j) 0 2 = (if i = j then (varProf D N θ i j : ℂ) else 0) := by
  have hprob := hμ.prob
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  set ν := μ.map fun h : Idx D N → Idx D N → ℂ => h i j with hν
  have hmap : ∀ f : ℂ → ℂ, Continuous f → ∫ z, f z ∂ν = ∫ h, f (h i j) ∂μ := fun f hf =>
    integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  have e1 : ∫ z, z ∂ν = 0 := by
    rw [hmap (fun z => z) continuous_id]
    exact hμ.mean i j
  have ec : ∫ z, starRingEnd ℂ z ∂ν = 0 := by
    rw [hmap (fun z => starRingEnd ℂ z) Complex.continuous_conj, integral_conj, hμ.mean i j, map_zero]
  have e11 : ∫ z, z * starRingEnd ℂ z ∂ν = (varProf D N θ i j : ℂ) := by
    rw [hmap (fun z => z * starRingEnd ℂ z) (continuous_id.mul Complex.continuous_conj)]
    have : (fun h : Idx D N → Idx D N → ℂ => h i j * starRingEnd ℂ (h i j)) =
        fun h => (((‖h i j‖ ^ 2 : ℝ)) : ℂ) := by
      funext h
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, integral_complex_ofReal, hμ.var i j]
  have e20 : ∫ z, z * z ∂ν = (if i = j then (varProf D N θ i j : ℂ) else 0) := by
    rw [hmap (fun z => z * z) (continuous_id.mul continuous_id)]
    by_cases hij : i = j
    · subst hij
      rw [show (if i = i then (varProf D N θ i i : ℂ) else 0) = (varProf D N θ i i : ℂ) by simp,
        ← e11, hmap (fun z => z * starRingEnd ℂ z) (continuous_id.mul Complex.continuous_conj)]
      refine integral_congr_ae ?_
      filter_upwards [hμ.herm] with h hh
      have h1 : starRingEnd ℂ (h i i) = h i i := by
        simpa [Complex.star_def] using hh.apply i i
      rw [h1]
    · simp only [hij, ↓reduceIte]
      have := hμ.pseudo i j hij
      simpa [sq] using this
  have e02 : ∫ z, starRingEnd ℂ z * starRingEnd ℂ z ∂ν =
      (if i = j then (varProf D N θ i j : ℂ) else 0) := by
    have : ∫ z, starRingEnd ℂ z * starRingEnd ℂ z ∂ν = starRingEnd ℂ (∫ z, z * z ∂ν) := by
      rw [← integral_conj]
      simp only [map_mul]
    rw [this, e20]
    split_ifs
    · exact Complex.conj_ofReal _
    · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CC_ccum_eq]
    refine (CC_jointCum_one ν (CC_X 1 0)).trans ?_
    simp only [CC_X_10]
    exact e1
  · rw [CC_ccum_eq]
    refine (CC_jointCum_two ν (CC_X 1 1)).trans ?_
    simp only [CC_X_11_0, CC_X_11_1, e11, e1, ec]
    ring
  · rw [CC_ccum_eq]
    refine (CC_jointCum_two ν (CC_X 2 0)).trans ?_
    simp only [CC_X_20, e20, e1]
    ring
  · rw [CC_ccum_eq]
    refine (CC_jointCum_two ν (CC_X 0 2)).trans ?_
    simp only [CC_X_02, e02, ec]
    ring

/-- Lemma 2.11 [lem:complex_cumu], (2.26) [5.16], for one entry of a member of `LLClass` with the
other entries fixed: for `F` of class `C^{l+1}` on arrays whose restrictions
`w ↦ F(setEntry h i j w)` have Wirtinger derivatives of order `≤ l + 1` bounded by `B`, and of
order `l + 1` bounded by `A` on `|w| ≤ M`,
`|E F(h) h̄_{ij} - Σ_{p+q ≤ l} 𝒞^{(p,q+1)}(h_{ij}) E F^{(p,q)} / (p! q!)|
≤ K (E|h_{ij}|^{l+2} A + E[|h_{ij}|^{l+2} 1(|h_{ij}| > M)] B)`, with `K` depending on `l` only. -/
theorem llClass_cumulant_expansion (l : ℕ) :
    ∃ K : ℝ, ∀ (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → ∀ (i j : Idx D N) (F : (Idx D N → Idx D N → ℂ) → ℂ) (M A B : ℝ),
      ContDiff ℝ (l + 1 : ℕ) F → 0 < M →
      (∀ p q : ℕ, p + q = l + 1 → ∀ (h : Idx D N → Idx D N → ℂ) (w : ℂ), ‖w‖ ≤ M →
        ‖wirt p q (fun w' => F (setEntry h i j w')) w‖ ≤ A) →
      (∀ p q : ℕ, p + q ≤ l + 1 → ∀ (h : Idx D N → Idx D N → ℂ) (w : ℂ),
        ‖wirt p q (fun w' => F (setEntry h i j w')) w‖ ≤ B) →
      ‖(∫ h, F h * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
              ∫ h, wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ‖ ≤
        K * ((∫ h, ‖h i j‖ ^ (l + 2) ∂μ) * A +
          (∫ h, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ∂μ) * B) := by
  obtain ⟨K, hK⟩ := cumulant_expansion l
  refine ⟨K, ?_⟩
  intro D N C θ μ hμ i j F M A B hF hM hA hB
  have hprob := hμ.prob
  have hXm : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hRm : Measurable (CC_R i j : (Idx D N → Idx D N → ℂ) → CC_U D N → ℂ) := by
    refine measurable_pi_iff.mpr fun q => ?_
    by_cases hq : q = CC_q0 i j
    · simp only [CC_R, hq, ↓reduceIte]
      exact measurable_const
    · simp only [CC_R, hq, ↓reduceIte]
      exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  set ν := μ.map fun h : Idx D N → Idx D N → ℂ => h i j with hν
  set ρ := μ.map (CC_R i j : (Idx D N → Idx D N → ℂ) → CC_U D N → ℂ) with hρ
  have hνprob : IsProbabilityMeasure ν := inferInstance
  have hρprob : IsProbabilityMeasure ρ := inferInstance
  have hind := CC_indep hμ i j
  -- the smooth function of `(r, w)`
  set G : (CC_U D N → ℂ) × ℂ → ℂ := fun x => F (setEntry (CC_fill x.1) i j x.2) with hG
  have hGs : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) G := hF.comp (CC_contDiff_theta i j _)
  set Φ : ℕ → ℕ → (CC_U D N → ℂ) × ℂ → ℂ :=
    fun p q x => wirt p q (fun w => G (x.1, w)) x.2 with hΦ
  have hΦc : ∀ p q, p + q ≤ l + 1 → Continuous (Φ p q) := fun p q hpq =>
    CC_wirt_continuous G l hGs p q hpq
  have hΦb : ∀ p q, p + q ≤ l + 1 → ∀ x, ‖Φ p q x‖ ≤ B := fun p q hpq x =>
    hB p q hpq (CC_fill x.1) x.2
  have hGc : Continuous G := hΦc 0 0 (by omega)
  have hGb : ∀ x, ‖G x‖ ≤ B := fun x => hΦb 0 0 (by omega) x
  have hmom : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) ν := fun p =>
    (integrable_map_measure (continuous_norm.pow p).aestronglyMeasurable
      hXm.aemeasurable).mpr (hμ.integrable p i j)
  have hmom1 : Integrable (fun z : ℂ => ‖z‖) ν := by simpa using hmom 1
  -- integrability on `ρ ⊗ ν`
  have hI0 : Integrable (fun x : (CC_U D N → ℂ) × ℂ => G x * starRingEnd ℂ x.2) (ρ.prod ν) := by
    refine Integrable.mono' ((hmom1.const_mul B).comp_snd ρ)
      (hGc.mul (Complex.continuous_conj.comp continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _)
  have hIpq : ∀ p q, p + q ≤ l + 1 → Integrable (Φ p q) (ρ.prod ν) := fun p q hpq =>
    Integrable.mono' (integrable_const B) (hΦc p q hpq).aestronglyMeasurable
      (Eventually.of_forall (hΦb p q hpq))
  -- the entries are integrated first over `h_{ij}`, then over the rest
  have hint0 : ∫ h, F h * starRingEnd ℂ (h i j) ∂μ =
      ∫ c, (∫ x, G (c, x) * starRingEnd ℂ x ∂ν) ∂ρ := by
    have key := CC_cond_integral (Ψ := fun x : (CC_U D N → ℂ) × ℂ => G x * starRingEnd ℂ x.2)
      hRm hXm hind hI0
    refine Eq.trans (integral_congr_ae ?_) key
    filter_upwards [hμ.herm] with h hh
    show F h * starRingEnd ℂ (h i j) =
      F (setEntry (CC_fill (CC_R i j h)) i j (h i j)) * starRingEnd ℂ (h i j)
    rw [← CC_setEntry_eq h hh i j (h i j), CC_setEntry_self h hh i j]
  have hintpq : ∀ p q, p + q ≤ l + 1 →
      ∫ h, wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ =
        ∫ c, (∫ x, Φ p q (c, x) ∂ν) ∂ρ := by
    intro p q hpq
    have key := CC_cond_integral (Ψ := Φ p q) hRm hXm hind (hIpq p q hpq)
    refine Eq.trans (integral_congr_ae ?_) key
    filter_upwards [hμ.herm] with h hh
    have hfun : (fun w' => F (setEntry h i j w')) = fun w => G (CC_R i j h, w) := by
      funext w
      exact congrArg F (CC_setEntry_eq h hh i j w)
    show wirt p q (fun w' => F (setEntry h i j w')) (h i j) =
      wirt p q (fun w => G (CC_R i j h, w)) (h i j)
    rw [hfun]
  set κ : ℕ → ℕ → ℂ := fun p q => ccum ν p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ)
    with hκ
  have hf0 : Integrable (fun c => ∫ x, G (c, x) * starRingEnd ℂ x ∂ν) ρ :=
    hI0.integral_prod_left
  have hfpq : ∀ p ∈ Finset.range (l + 1), ∀ q ∈ Finset.range (l + 1 - p),
      Integrable (fun c => κ p q * ∫ x, Φ p q (c, x) ∂ν) ρ := by
    intro p hp q hq
    have hpq : p + q ≤ l + 1 := by
      simp only [Finset.mem_range] at hp hq
      omega
    exact ((hIpq p q hpq).integral_prod_left).const_mul _
  have hsum : ∫ c, ((∫ x, G (c, x) * starRingEnd ℂ x ∂ν) -
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        κ p q * ∫ x, Φ p q (c, x) ∂ν) ∂ρ =
      (∫ c, (∫ x, G (c, x) * starRingEnd ℂ x ∂ν) ∂ρ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          κ p q * ∫ c, (∫ x, Φ p q (c, x) ∂ν) ∂ρ := by
    rw [integral_sub hf0 (integrable_finsetSum _ fun p hp =>
      integrable_finsetSum _ fun q hq => hfpq p hp q hq)]
    rw [integral_finsetSum _ (fun p hp => integrable_finsetSum _ (fun q hq => hfpq p hp q hq))]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_finsetSum _ (fun q hq => hfpq p hp q hq)]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [integral_const_mul]
  have hrw : (∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      ccum ν p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        ∫ h, wirt p q (fun w' => F (setEntry h i j w')) (h i j) ∂μ) =
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          κ p q * ∫ c, (∫ x, Φ p q (c, x) ∂ν) ∂ρ := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    have hpq : p + q ≤ l + 1 := by
      simp only [Finset.mem_range] at hp hq
      omega
    rw [hintpq p q hpq]
  have hbound : ∀ c : CC_U D N → ℂ, ‖(∫ x, G (c, x) * starRingEnd ℂ x ∂ν) -
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        κ p q * ∫ x, Φ p q (c, x) ∂ν‖ ≤
      K * ((∫ h, ‖h i j‖ ^ (l + 2) ∂μ) * A +
        (∫ h, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ∂μ) * B) := by
    intro c
    have hGc' : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fun w => G (c, w)) :=
      hGs.comp (contDiff_const.prodMk contDiff_id)
    have hmain := hK ν (fun w => G (c, w)) M A B hmom hGc' hM
      (fun p q hpq z hz => hA p q hpq (CC_fill c) z hz)
      (fun p q hpq z => hB p q hpq.le (CC_fill c) z)
    have e1 : ∫ z, ‖z‖ ^ (l + 2) ∂ν = ∫ h, ‖h i j‖ ^ (l + 2) ∂μ :=
      integral_map hXm.aemeasurable (continuous_norm.pow _).aestronglyMeasurable
    have hmi : Measurable (Set.indicator {w : ℂ | M < ‖w‖} (fun w : ℂ => ‖w‖ ^ (l + 2))) :=
      (continuous_norm.pow _).measurable.indicator
        (measurableSet_lt measurable_const continuous_norm.measurable)
    have e2 : ∫ z, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) z ∂ν =
        ∫ h, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ∂μ :=
      integral_map hXm.aemeasurable hmi.aestronglyMeasurable
    rw [e1, e2] at hmain
    exact hmain
  rw [hint0, hrw, ← hsum]
  calc ‖∫ c, ((∫ x, G (c, x) * starRingEnd ℂ x ∂ν) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          κ p q * ∫ x, Φ p q (c, x) ∂ν) ∂ρ‖
      ≤ (K * ((∫ h, ‖h i j‖ ^ (l + 2) ∂μ) * A +
        (∫ h, Set.indicator {w : ℂ | M < ‖w‖} (fun w => ‖w‖ ^ (l + 2)) (h i j) ∂μ) * B)) *
          ρ.real Set.univ := norm_integral_le_of_norm_le_const (Eventually.of_forall hbound)
    _ = _ := by simp

/-! ### The one-entry perturbation of the resolvent -/

/-- Substituting a pair into a Hermitian array keeps it Hermitian. -/
private lemma CC_setEntry_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun k l => ?_
  have h1 : ∀ k l, star (h l k) = h k l := fun k l => hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨rfl, rfl⟩ := hkl
      simp [setEntry]
    · have hlk : ¬ (l = i ∧ k = i) := fun h' => hkl ⟨h'.2, h'.1⟩
      simp [setEntry, hkl, hlk, h1 k l]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd, Ne.symm hd]
    · by_cases h2' : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2'
        simp [setEntry, hd, Ne.symm hd]
      · have e1 : ¬ (l = i ∧ k = j) := fun h' => h2' ⟨h'.2, h'.1⟩
        have e2 : ¬ (l = j ∧ k = i) := fun h' => h1' ⟨h'.2, h'.1⟩
        simp [setEntry, hd, h1', h2', e1, e2, h1 k l]

/-- The change of `setEntry h i i w` applied to a vector, on the diagonal. -/
private lemma CC_pert_diag {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i : Idx D N) (w : ℂ)
    (u : Idx D N → ℂ) :
    (Matrix.of (setEntry h i i w) - Matrix.of h) *ᵥ u =
      ((((w.re : ℝ) : ℂ) - h i i) * u i) • (Pi.single i (1 : ℂ) : Idx D N → ℂ) := by
  funext k
  have : ∀ l, (Matrix.of (setEntry h i i w) - Matrix.of h) k l * u l =
      if k = i ∧ l = i then (((w.re : ℝ) : ℂ) - h i i) * u i else 0 := by
    intro l
    by_cases hk : k = i ∧ l = i
    · obtain ⟨rfl, rfl⟩ := hk
      simp [setEntry]
    · simp [setEntry, hk]
  simp only [Matrix.mulVec, dotProduct, this]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

/-- The change of `setEntry h i j w` applied to a vector, for `i ≠ j`. -/
private lemma CC_pert_off {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (hd : i ≠ j)
    (w : ℂ) (u : Idx D N → ℂ) :
    (Matrix.of (setEntry h i j w) - Matrix.of h) *ᵥ u =
      ((w - h i j) * u j) • (Pi.single i (1 : ℂ) : Idx D N → ℂ) +
        ((starRingEnd ℂ w - h j i) * u i) • (Pi.single j (1 : ℂ) : Idx D N → ℂ) := by
  funext k
  have : ∀ l, (Matrix.of (setEntry h i j w) - Matrix.of h) k l * u l =
      (if k = i ∧ l = j then (w - h i j) * u j else 0) +
        (if k = j ∧ l = i then (starRingEnd ℂ w - h j i) * u i else 0) := by
    intro l
    by_cases h1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [setEntry, hd, Ne.symm hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd]
      · simp [setEntry, hd, h1, h2]
  simp only [Matrix.mulVec, dotProduct, this, Finset.sum_add_distrib]
  by_cases hk : k = i
  · subst hk
    simp [hd]
  · by_cases hk' : k = j
    · subst hk'
      simp [hk]
    · simp [hk, hk']

/-- The change of `setEntry h i j w` applied to a vector lies in the span of `e_i`, `e_j`, with
coefficients bounded by `2 M` times the entries `u_i`, `u_j`. -/
private lemma CC_pert {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) (M : ℝ) (hw : ‖w‖ ≤ M)
    (hij : ‖h i j‖ ≤ M) (u : Idx D N → ℂ) :
    ∃ a b : ℂ, (Matrix.of (setEntry h i j w) - Matrix.of h) *ᵥ u =
        a • (Pi.single i (1 : ℂ) : Idx D N → ℂ) + b • (Pi.single j (1 : ℂ) : Idx D N → ℂ) ∧
      ‖a‖ + ‖b‖ ≤ 2 * M * (‖u i‖ + ‖u j‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hw
  by_cases hd : i = j
  · subst hd
    refine ⟨(((w.re : ℝ) : ℂ) - h i i) * u i, 0, ?_, ?_⟩
    · rw [CC_pert_diag, zero_smul, add_zero]
    · have h1 : ‖((w.re : ℝ) : ℂ) - h i i‖ ≤ 2 * M := by
        calc ‖((w.re : ℝ) : ℂ) - h i i‖ ≤ ‖((w.re : ℝ) : ℂ)‖ + ‖h i i‖ := norm_sub_le _ _
          _ ≤ M + M := by
            gcongr
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact (Complex.abs_re_le_norm w).trans hw
          _ = 2 * M := by ring
      rw [norm_mul, norm_zero, add_zero]
      calc ‖((w.re : ℝ) : ℂ) - h i i‖ * ‖u i‖ ≤ 2 * M * ‖u i‖ := by gcongr
        _ ≤ 2 * M * (‖u i‖ + ‖u i‖) := by nlinarith [norm_nonneg (u i)]
  · refine ⟨(w - h i j) * u j, (starRingEnd ℂ w - h j i) * u i, CC_pert_off h i j hd w u, ?_⟩
    have hji : h j i = starRingEnd ℂ (h i j) := by
      have := hh.apply j i
      simpa [Complex.star_def] using this.symm
    have h1 : ‖w - h i j‖ ≤ 2 * M := by
      calc ‖w - h i j‖ ≤ ‖w‖ + ‖h i j‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add hw hij
        _ = 2 * M := by ring
    have h2 : ‖starRingEnd ℂ w - h j i‖ ≤ 2 * M := by
      rw [hji, ← map_sub, Complex.norm_conj]
      exact h1
    rw [norm_mul, norm_mul]
    nlinarith [mul_le_mul h1 le_rfl (norm_nonneg (u j)) (by positivity : (0:ℝ) ≤ 2 * M),
      mul_le_mul h2 le_rfl (norm_nonneg (u i)) (by positivity : (0:ℝ) ≤ 2 * M)]

/-- The one-entry perturbation bound: for Hermitian `h` and `Λ`, `Im z > 0`, `|w|, |h_{ij}| ≤ M`,
and `|x^* G y| ≤ Γ` for `x ∈ {s, e_i, e_j}`, `y ∈ {t, e_i, e_j}` with `4 M Γ ≤ 1/2`, the resolvent
`G'` of `setEntry h i j w + Λ` satisfies `|x^* G' y| ≤ 2Γ` for the same `x, y`. -/
theorem res_setEntry_le (D N : ℕ) (h : Idx D N → Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hh : (Matrix.of h).IsHermitian) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (i j : Idx D N) (w : ℂ) (M Γ : ℝ) (hw : ‖w‖ ≤ M) (hij : ‖h i j‖ ≤ M)
    (hMΓ : 4 * M * Γ ≤ 1 / 2) (s t : Idx D N → ℂ)
    (hG : ∀ x ∈ ({s, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
      ∀ y ∈ ({t, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
        ‖star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)‖ ≤ Γ) :
    ∀ x ∈ ({s, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
      ∀ y ∈ ({t, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
        ‖star x ⬝ᵥ (res (Matrix.of (setEntry h i j w) + Λ) z *ᵥ y)‖ ≤ 2 * Γ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hw
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans
    (hG s (by simp) t (by simp))
  have hH' := CC_setEntry_herm h hh i j w
  obtain ⟨hG1, hG2⟩ := res_mul_sub (Matrix.of h + Λ) (hh.add hΛ) z hz
  obtain ⟨hG1', hG2'⟩ := res_mul_sub (Matrix.of (setEntry h i j w) + Λ) (hH'.add hΛ) z hz
  set G := res (Matrix.of h + Λ) z with hGdef
  set G' := res (Matrix.of (setEntry h i j w) + Λ) z with hG'def
  set V : Matrix (Idx D N) (Idx D N) ℂ := Matrix.of (setEntry h i j w) - Matrix.of h with hVdef
  have hV : V = ((Matrix.of (setEntry h i j w) + Λ) - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) -
      ((Matrix.of h + Λ) - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
    rw [hVdef]; abel
  have key : G * V * G' = G - G' := by
    rw [hV, mul_sub, sub_mul, mul_assoc G, hG1', mul_one, hG2, one_mul]
  have hvec : ∀ y : Idx D N → ℂ, G' *ᵥ y = G *ᵥ y - G *ᵥ (V *ᵥ (G' *ᵥ y)) := by
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.sub_mulVec]
    have : G' = G - G * V * G' := by rw [key]; abel
    conv_lhs => rw [this]
  -- the finite set of the nine pairs
  set Xs : Set (Idx D N → ℂ) := {s, Pi.single i 1, Pi.single j 1} with hXs
  set Ys : Set (Idx D N → ℂ) := {t, Pi.single i 1, Pi.single j 1} with hYs
  have hfin : (Xs ×ˢ Ys).Finite := (Set.toFinite Xs).prod (Set.toFinite Ys)
  have hne : (Xs ×ˢ Ys).Nonempty := ⟨(s, t), by simp [hXs, hYs]⟩
  obtain ⟨a₀, ha₀, hmax⟩ := Set.exists_max_image (Xs ×ˢ Ys)
    (fun p => ‖star p.1 ⬝ᵥ (G' *ᵥ p.2)‖) hfin hne
  set β := ‖star a₀.1 ⬝ᵥ (G' *ᵥ a₀.2)‖ with hβ
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hei : (Pi.single i (1 : ℂ) : Idx D N → ℂ) ∈ Xs := by simp [hXs]
  have hej : (Pi.single j (1 : ℂ) : Idx D N → ℂ) ∈ Xs := by simp [hXs]
  have hEi : (Pi.single i (1 : ℂ) : Idx D N → ℂ) ∈ Ys := by simp [hYs]
  have hEj : (Pi.single j (1 : ℂ) : Idx D N → ℂ) ∈ Ys := by simp [hYs]
  have step : ∀ x ∈ Xs, ∀ y ∈ Ys, ‖star x ⬝ᵥ (G' *ᵥ y)‖ ≤ Γ + 4 * M * Γ * β := by
    intro x hx y hy
    obtain ⟨a, b, hab, hn⟩ := CC_pert h hh i j w M hw hij (G' *ᵥ y)
    have hu : ∀ k : Idx D N, (Pi.single k (1 : ℂ) : Idx D N → ℂ) ∈ Xs →
        ‖(G' *ᵥ y) k‖ ≤ β := by
      intro k hk
      have := hmax (Pi.single k 1, y) ⟨hk, hy⟩
      simpa using this
    have hui := hu i hei
    have huj := hu j hej
    have e1 : star x ⬝ᵥ (G' *ᵥ y) = star x ⬝ᵥ (G *ᵥ y) -
        (a * (star x ⬝ᵥ (G *ᵥ Pi.single i 1)) + b * (star x ⬝ᵥ (G *ᵥ Pi.single j 1))) := by
      rw [hvec y, hab, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have g1 := hG x hx y hy
    have g2 := hG x hx (Pi.single i 1) hEi
    have g3 := hG x hx (Pi.single j 1) hEj
    rw [e1]
    calc ‖star x ⬝ᵥ (G *ᵥ y) -
          (a * (star x ⬝ᵥ (G *ᵥ Pi.single i 1)) + b * (star x ⬝ᵥ (G *ᵥ Pi.single j 1)))‖
        ≤ ‖star x ⬝ᵥ (G *ᵥ y)‖ + (‖a‖ * ‖star x ⬝ᵥ (G *ᵥ Pi.single i 1)‖ +
            ‖b‖ * ‖star x ⬝ᵥ (G *ᵥ Pi.single j 1)‖) := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ Γ + (‖a‖ * Γ + ‖b‖ * Γ) := by gcongr
      _ = Γ + (‖a‖ + ‖b‖) * Γ := by ring
      _ ≤ Γ + (2 * M * (β + β)) * Γ := by
          gcongr
          exact hn.trans (mul_le_mul_of_nonneg_left (add_le_add hui huj) (by positivity))
      _ = Γ + 4 * M * Γ * β := by ring
  have hβle : β ≤ 2 * Γ := by
    have := step a₀.1 (ha₀.1) a₀.2 (ha₀.2)
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hM) hΓ, mul_le_mul_of_nonneg_right hMΓ hβ0]
  intro x hx y hy
  exact (hmax (x, y) ⟨hx, hy⟩).trans hβle

end RBMTransitionEdge

end
