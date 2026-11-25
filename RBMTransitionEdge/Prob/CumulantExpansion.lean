module

public import RBMTransitionEdge.Prob.Cumulant

@[expose] public section

/-!
# The complex cumulant expansion (Lemma 2.11, (2.26))

Lemma 2.11 [lem:complex_cumu], (2.26) [5.16]: `E[h̄ F(h)]` expanded in complex cumulants `𝒞^{(p,q+1)}` and
Wirtinger derivatives up to order `l`, with the remainder bounded by an inner part (`|h| ≤ M`) and a tail.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `G` has real derivative `v ↦ α v + β v̄` at `w`. -/
private def CE_HasW (G : ℂ → ℂ) (w α β : ℂ) : Prop :=
  ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L w ∧ ∀ v, L v = α * v + β * starRingEnd ℂ v

/-- Every real-linear map on `ℂ` is `v ↦ α v + β v̄` with its two Wirtinger coefficients. -/
private lemma CE_clm_split (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (L 1 - Complex.I * L Complex.I) / 2 * v +
      (L 1 + Complex.I * L Complex.I) / 2 * starRingEnd ℂ v := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hL : L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL]
  conv_rhs => rw [hv]
  simp only [map_add, Complex.real_smul, map_mul, Complex.conj_ofReal, map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Wirtinger derivatives read off a derivative of the form `v ↦ α v + β v̄`. -/
private lemma CE_HasW.eq {G : ℂ → ℂ} {w α β : ℂ} (h : CE_HasW G w α β) :
    dW G w = α ∧ dWbar G w = β := by
  obtain ⟨L, hL, hv⟩ := h
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [dW, dWbar, hL.fderiv, hv, map_one, mul_one, Complex.conj_I]
  constructor
  · linear_combination (β - α) / 2 * hI
  · linear_combination (α - β) / 2 * hI

/-- A differentiable function has derivative `v ↦ ∂G v + ∂̄G v̄`. -/
private lemma CE_HasW_of_diff {G : ℂ → ℂ} {w : ℂ} (h : DifferentiableAt ℝ G w) :
    CE_HasW G w (dW G w) (dWbar G w) :=
  ⟨fderiv ℝ G w, h.hasFDerivAt, fun v => CE_clm_split _ v⟩

/-- Wirtinger derivatives of a difference. -/
private lemma CE_HasW.sub {G H : ℂ → ℂ} {w α β α' β' : ℂ} (hG : CE_HasW G w α β)
    (hH : CE_HasW H w α' β') : CE_HasW (fun z => G z - H z) w (α - α') (β - β') := by
  obtain ⟨L, hL, hv⟩ := hG
  obtain ⟨L', hL', hv'⟩ := hH
  exact ⟨L - L', hL.sub hL', fun v => by simp [hv, hv']; ring⟩

/-- Wirtinger derivatives of a constant multiple. -/
private lemma CE_HasW.const_mul {G : ℂ → ℂ} {w α β : ℂ} (c : ℂ) (hG : CE_HasW G w α β) :
    CE_HasW (fun z => c * G z) w (c * α) (c * β) := by
  obtain ⟨L, hL, hv⟩ := hG
  exact ⟨c • L, hL.const_mul c, fun v => by simp [hv]; ring⟩

/-- Wirtinger derivatives of a finite sum. -/
private lemma CE_HasW.sum {ι : Type*} (s : Finset ι) {G : ι → ℂ → ℂ} {w : ℂ} {α β : ι → ℂ}
    (h : ∀ i, CE_HasW (G i) w (α i) (β i)) :
    CE_HasW (fun z => ∑ i ∈ s, G i z) w (∑ i ∈ s, α i) (∑ i ∈ s, β i) := by
  choose L hL hv using h
  refine ⟨∑ i ∈ s, L i, HasFDerivAt.fun_sum (fun i _ => hL i), fun v => ?_⟩
  simp only [FunLike.coe_sum, Finset.sum_apply, hv, Finset.sum_add_distrib,
    Finset.sum_mul]

/-- The monomial `z^a z̄^b` has Wirtinger derivatives `a z^{a-1} z̄^b` and `b z^a z̄^{b-1}`. -/
private lemma CE_HasW_mono (a b : ℕ) (w : ℂ) :
    CE_HasW (fun z => z ^ a * starRingEnd ℂ z ^ b) w
      ((a : ℂ) * w ^ (a - 1) * starRingEnd ℂ w ^ b)
      ((b : ℂ) * w ^ a * starRingEnd ℂ w ^ (b - 1)) := by
  have h1 : HasFDerivAt (fun z : ℂ => z ^ a)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((a : ℂ) * w ^ (a - 1))).restrictScalars ℝ)
      w :=
    ((hasDerivAt_pow a w).hasFDerivAt).restrictScalars ℝ
  have h2' : HasFDerivAt (fun z : ℂ => z ^ b)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((b : ℂ) * w ^ (b - 1))).restrictScalars ℝ)
      w :=
    ((hasDerivAt_pow b w).hasFDerivAt).restrictScalars ℝ
  have h2 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp w h2'
  refine ⟨_, h1.mul (h2.congr_of_eventuallyEq ?_), fun v => ?_⟩
  · exact Filter.Eventually.of_forall fun z => by simp
  · simp
    ring

/-- `∂G` and `∂̄G` are `C^n` when `G` is `C^{n+1}`. -/
private lemma CE_contDiff_dW {n : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ (n + 1 : ℕ) G) :
    ContDiff ℝ n (dW G) ∧ ContDiff ℝ n (dWbar G) := by
  have hD : ContDiff ℝ n (fderiv ℝ G) := h.fderiv_right (by norm_cast)
  have h1 : ContDiff ℝ n (fun z => fderiv ℝ G z 1) := hD.clm_apply contDiff_const
  have hI : ContDiff ℝ n (fun z => fderiv ℝ G z Complex.I) := hD.clm_apply contDiff_const
  exact ⟨(h1.sub (contDiff_const.mul hI)).div_const 2,
    (h1.add (contDiff_const.mul hI)).div_const 2⟩

/-- The derivative of `z ↦ DG(z) v` at `w` is `u ↦ D²G(w) u v`, in Wirtinger form. -/
private lemma CE_HasW_apply {G : ℂ → ℂ} {w : ℂ} (h : DifferentiableAt ℝ (fderiv ℝ G) w) (v : ℂ) :
    CE_HasW (fun z => fderiv ℝ G z v) w
      ((fderiv ℝ (fderiv ℝ G) w 1 v - Complex.I * fderiv ℝ (fderiv ℝ G) w Complex.I v) / 2)
      ((fderiv ℝ (fderiv ℝ G) w 1 v + Complex.I * fderiv ℝ (fderiv ℝ G) w Complex.I v) / 2) := by
  have := h.hasFDerivAt.clm_apply (hasFDerivAt_const v w)
  refine ⟨_, this, fun u => ?_⟩
  simpa using CE_clm_split ((fderiv ℝ (fderiv ℝ G) w).flip v) u

/-- Wirtinger derivatives of a sum. -/
private lemma CE_HasW.add {G H : ℂ → ℂ} {w α β α' β' : ℂ} (hG : CE_HasW G w α β)
    (hH : CE_HasW H w α' β') : CE_HasW (fun z => G z + H z) w (α + α') (β + β') := by
  obtain ⟨L, hL, hv⟩ := hG
  obtain ⟨L', hL', hv'⟩ := hH
  exact ⟨L + L', hL.add hL', fun v => by simp [hv, hv']; ring⟩

/-- Wirtinger derivatives of `G / 2`. -/
private lemma CE_HasW.div_two {G : ℂ → ℂ} {w α β : ℂ} (hG : CE_HasW G w α β) :
    CE_HasW (fun z => G z / 2) w (α / 2) (β / 2) := by
  have := hG.const_mul (1 / 2)
  simp only [one_div] at this
  convert this using 1 <;> [funext z; skip; skip] <;> ring

/-- `∂` and `∂̄` commute on `C^2` functions. -/
private lemma CE_comm {G : ℂ → ℂ} (h : ContDiff ℝ 2 G) : dW (dWbar G) = dWbar (dW G) := by
  funext w
  have hd : DifferentiableAt ℝ (fderiv ℝ G) w :=
    ((h.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) w
  have hs : IsSymmSndFDerivAt ℝ G w := h.contDiffAt.isSymmSndFDerivAt (by simp)
  have h1 := CE_HasW_apply hd 1
  have hI := CE_HasW_apply hd Complex.I
  have hb := ((h1.add (hI.const_mul Complex.I)).div_two).eq.1
  have ha := ((h1.sub (hI.const_mul Complex.I)).div_two).eq.2
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsym := hs 1 Complex.I
  change dW (fun z => (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) / 2) w =
    dWbar (fun z => (fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I) / 2) w
  rw [hb, ha]
  linear_combination (Complex.I / 2) * hsym

/-- `C^N` gives `C^{N-1}` for `∂G` and `∂̄G` in the `≤` form. -/
private lemma CE_contDiff_dW' {n N : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ N G) (hn : n + 1 ≤ N) :
    ContDiff ℝ n (dW G) ∧ ContDiff ℝ n (dWbar G) :=
  CE_contDiff_dW (h.of_le (by exact_mod_cast hn))

/-- `F^{(p,q)}` is `C^n` when `F` is `C^N` with `n + p + q ≤ N`. -/
private lemma CE_contDiff_wirt {N : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ N G) (n p q : ℕ)
    (hn : n + p + q ≤ N) : ContDiff ℝ n (wirt p q G) := by
  have hq : ∀ q N : ℕ, ∀ G : ℂ → ℂ, ContDiff ℝ N G → ∀ n : ℕ, n + q ≤ N →
      ContDiff ℝ n (dWbar^[q] G) := by
    intro q
    induction q with
    | zero => intro N G h n hn; exact h.of_le (by exact_mod_cast hn)
    | succ q ih =>
      intro N G h n hn
      rw [Function.iterate_succ_apply]
      exact ih (n + q) _ (CE_contDiff_dW' h (by omega)).2 n le_rfl
  have hp : ∀ p N : ℕ, ∀ G : ℂ → ℂ, ContDiff ℝ N G → ∀ n : ℕ, n + p ≤ N →
      ContDiff ℝ n (dW^[p] G) := by
    intro p
    induction p with
    | zero => intro N G h n hn; exact h.of_le (by exact_mod_cast hn)
    | succ p ih =>
      intro N G h n hn
      rw [Function.iterate_succ_apply]
      exact ih (n + p) _ (CE_contDiff_dW' h (by omega)).1 n le_rfl
  exact hp p (n + p) _ (hq q N G h (n + p) (by omega)) n le_rfl

/-- `∂ ∂̄^b G = ∂̄^b ∂ G` for `G` of class `C^N`, `b + 1 ≤ N`. -/
private lemma CE_comm_iter1 (b : ℕ) : ∀ {N : ℕ} {G : ℂ → ℂ}, ContDiff ℝ N G → b + 1 ≤ N →
    dW (dWbar^[b] G) = dWbar^[b] (dW G) := by
  induction b with
  | zero => intro N G _ _; rfl
  | succ b ih =>
    intro N G h hb
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih (CE_contDiff_dW' h (n := N - 1) (by omega)).2 (by omega),
      CE_comm (h.of_le (by exact_mod_cast (show 2 ≤ N by omega)))]

/-- `∂̄^b ∂^p H = ∂^p ∂̄^b H` for `H` of class `C^N`, `p + b ≤ N`. -/
private lemma CE_comm_iter (p : ℕ) : ∀ {N b : ℕ} {H : ℂ → ℂ}, ContDiff ℝ N H → p + b ≤ N →
    dWbar^[b] (dW^[p] H) = dW^[p] (dWbar^[b] H) := by
  induction p with
  | zero => intro N b H _ _; rfl
  | succ p ih =>
    intro N b H h hb
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih (CE_contDiff_dW' h (n := N - 1) (by omega)).1 (by omega),
      CE_comm_iter1 b h (by omega)]

/-- `(F^{(p,q)})^{(a,b)} = F^{(a+p, b+q)}` for `F` of class `C^N`, `p + q + b ≤ N`. -/
private lemma CE_wirt_wirt {N : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ N G) (a b p q : ℕ)
    (hb : p + q + b ≤ N) : wirt a b (wirt p q G) = wirt (a + p) (b + q) G := by
  unfold wirt
  have hH : ContDiff ℝ (p + b : ℕ) (dWbar^[q] G) := CE_contDiff_wirt h (p + b) 0 q (by omega)
  rw [CE_comm_iter p hH le_rfl,
    ← Function.iterate_add_apply, ← Function.iterate_add_apply]

/-- Rewriting the Wirtinger coefficients. -/
private lemma CE_HasW.congr {G : ℂ → ℂ} {w α β α' β' : ℂ} (h : CE_HasW G w α β) (hα : α = α')
    (hβ : β = β') : CE_HasW G w α' β' := hα ▸ hβ ▸ h

/-- A derivative `v ↦ α v + β v̄` has operator norm at most `‖α‖ + ‖β‖`. -/
private lemma CE_HasW.norm_fderiv_le {G : ℂ → ℂ} {w α β : ℂ} (h : CE_HasW G w α β) :
    DifferentiableAt ℝ G w ∧ ‖fderiv ℝ G w‖ ≤ ‖α‖ + ‖β‖ := by
  obtain ⟨L, hL, hv⟩ := h
  refine ⟨hL.differentiableAt, ?_⟩
  rw [hL.fderiv]
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  rw [hv]
  calc ‖α * v + β * starRingEnd ℂ v‖ ≤ ‖α * v‖ + ‖β * starRingEnd ℂ v‖ := norm_add_le _ _
    _ = (‖α‖ + ‖β‖) * ‖v‖ := by simp; ring

/-- The index set `{(a, b) : a + b < n}`. -/
private def CE_S (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun x => x.1 + x.2 < n

/-- Membership in `{(a, b) : a + b < n}`. -/
private lemma CE_mem_S {n : ℕ} {x : ℕ × ℕ} : x ∈ CE_S n ↔ x.1 + x.2 < n := by
  simp only [CE_S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The Taylor polynomial of order `n - 1` at `0` in Wirtinger form:
`Σ_{a+b<n} G^{(a,b)}(0) z^a z̄^b / (a! b!)`. -/
private def CE_tay (n : ℕ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ x ∈ CE_S n, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
    (z ^ x.1 * starRingEnd ℂ z ^ x.2)

/-- The Taylor polynomial takes the value `G(0)` at `0`. -/
private lemma CE_tay_zero (n : ℕ) (G : ℂ → ℂ) : CE_tay (n + 1) G 0 = G 0 := by
  unfold CE_tay
  rw [Finset.sum_eq_single (0, 0)]
  · simp [wirt]
  · rintro ⟨a, b⟩ _ hab
    have : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact hab (by rw [h.1, h.2])
    rcases this with h | h <;> simp [h]
  · intro h
    exact absurd (CE_mem_S.2 (by simp)) h

/-- Shifting the first index: terms with `a = 0` vanish. -/
private lemma CE_sum_S_shift1 (n : ℕ) (f : ℕ × ℕ → ℂ) (hf : ∀ b, f (0, b) = 0) :
    ∑ x ∈ CE_S (n + 1), f x = ∑ y ∈ CE_S n, f (y.1 + 1, y.2) := by
  have hinj : Set.InjOn (fun y : ℕ × ℕ => (y.1 + 1, y.2)) (CE_S n) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) h.2
  rw [← Finset.sum_image (g := fun y : ℕ × ℕ => (y.1 + 1, y.2)) (f := f) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact CE_mem_S.2 (by have := CE_mem_S.1 hy; simp only at this ⊢; omega)
  · obtain ⟨a, b⟩ := x
    rcases a with _ | a
    · exact hf b
    · exact absurd (Finset.mem_image.2 ⟨(a, b), CE_mem_S.2 (by
        have := CE_mem_S.1 hx; simp only at this ⊢; omega), rfl⟩) hx'

/-- Shifting the second index: terms with `b = 0` vanish. -/
private lemma CE_sum_S_shift2 (n : ℕ) (f : ℕ × ℕ → ℂ) (hf : ∀ a, f (a, 0) = 0) :
    ∑ x ∈ CE_S (n + 1), f x = ∑ y ∈ CE_S n, f (y.1, y.2 + 1) := by
  have hinj : Set.InjOn (fun y : ℕ × ℕ => (y.1, y.2 + 1)) (CE_S n) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  rw [← Finset.sum_image (g := fun y : ℕ × ℕ => (y.1, y.2 + 1)) (f := f) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact CE_mem_S.2 (by have := CE_mem_S.1 hy; simp only at this ⊢; omega)
  · obtain ⟨a, b⟩ := x
    rcases b with _ | b
    · exact hf a
    · exact absurd (Finset.mem_image.2 ⟨(a, b), CE_mem_S.2 (by
        have := CE_mem_S.1 hx; simp only at this ⊢; omega), rfl⟩) hx'

/-- The Wirtinger derivatives of the Taylor polynomial are the Taylor polynomials of `∂G`, `∂̄G`. -/
private lemma CE_HasW_tay {n : ℕ} {G : ℂ → ℂ} (hG : ContDiff ℝ (n + 1 : ℕ) G) (w : ℂ) :
    CE_HasW (CE_tay (n + 1) G) w (CE_tay n (dW G) w) (CE_tay n (dWbar G) w) := by
  have h := CE_HasW.sum (CE_S (n + 1)) (fun x => (CE_HasW_mono x.1 x.2 w).const_mul
    (wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ)))
  refine h.congr ?_ ?_
  · rw [CE_sum_S_shift1 n _ (fun b => by simp)]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := CE_mem_S.1 hy
    have hw : wirt y.1 y.2 (dW G) = wirt (y.1 + 1) y.2 G := by
      have := CE_wirt_wirt hG y.1 y.2 1 0 (by omega)
      simpa [wirt] using this
    rw [hw]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
    have h1 : (y.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (y.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
  · rw [CE_sum_S_shift2 n _ (fun a => by simp)]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hw : wirt y.1 y.2 (dWbar G) = wirt y.1 (y.2 + 1) G := by
      simp only [wirt, Function.iterate_succ_apply]
    rw [hw]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
    have h1 : (y.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (y.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp

/-- Taylor's estimate in Wirtinger form: if `‖G^{(a,b)}‖ ≤ S` on the ball of radius `r` for
`a + b = n`, then `‖G(z) - Σ_{a+b<n} G^{(a,b)}(0) z^a z̄^b / (a! b!)‖ ≤ 2^n S ‖z‖^n` on that
ball. -/
private lemma CE_taylor (n : ℕ) : ∀ {G : ℂ → ℂ}, ContDiff ℝ n G → ∀ {r S : ℝ},
    (∀ a b, a + b = n → ∀ w : ℂ, ‖w‖ ≤ r → ‖wirt a b G w‖ ≤ S) →
    ∀ z : ℂ, ‖z‖ ≤ r → ‖G z - CE_tay n G z‖ ≤ 2 ^ n * S * ‖z‖ ^ n := by
  induction n with
  | zero =>
    intro G _ r S hS z hz
    have h := hS 0 0 rfl z hz
    simpa [CE_tay, CE_S, wirt] using h
  | succ n ih =>
    intro G hG r S hS z hz
    have hS0 : 0 ≤ S :=
      (norm_nonneg _).trans (hS (n + 1) 0 rfl 0 (by simpa using (norm_nonneg z).trans hz))
    have hd := CE_contDiff_dW hG
    have hGd : Differentiable ℝ G := hG.differentiable (by norm_cast)
    have ih1 := ih hd.1 (r := r) (S := S) (fun a b hab w hw => by
      have := CE_wirt_wirt hG a b 1 0 (by omega)
      simp only [wirt, Function.iterate_zero, id_eq, Function.iterate_one, add_zero] at this
      have h' := hS (a + 1) b (by omega) w hw
      simp only [wirt] at h' ⊢
      rwa [this])
    have ih2 := ih hd.2 (r := r) (S := S) (fun a b hab w hw => by
      have h' := hS a (b + 1) (by omega) w hw
      simpa only [wirt, Function.iterate_succ_apply] using h')
    set R : ℂ → ℂ := fun w => G w - CE_tay (n + 1) G w
    have hR : ∀ w, CE_HasW R w (dW G w - CE_tay n (dW G) w) (dWbar G w - CE_tay n (dWbar G) w) :=
      fun w => (CE_HasW_of_diff (hGd w)).sub (CE_HasW_tay hG w)
    have hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) ‖z‖,
        ‖fderiv ℝ R w‖ ≤ 2 ^ (n + 1) * S * ‖z‖ ^ n := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      have hwr : ‖w‖ ≤ r := hw.trans hz
      have hpow : ‖w‖ ^ n ≤ ‖z‖ ^ n := pow_le_pow_left₀ (norm_nonneg _) hw n
      refine (hR w).norm_fderiv_le.2.trans ?_
      have e1 := ih1 w hwr
      have e2 := ih2 w hwr
      have : 2 ^ n * S * ‖w‖ ^ n ≤ 2 ^ n * S * ‖z‖ ^ n := by gcongr
      rw [pow_succ]
      linarith
    have hmvt := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (hR w).norm_fderiv_le.1) hbound (Metric.mem_closedBall_self (norm_nonneg z))
      (y := z) (by simp)
    have hR0 : R 0 = 0 := by simp [R, CE_tay_zero]
    rw [hR0, sub_zero, sub_zero] at hmvt
    calc ‖G z - CE_tay (n + 1) G z‖ = ‖R z‖ := rfl
      _ ≤ 2 ^ (n + 1) * S * ‖z‖ ^ n * ‖z‖ := hmvt
      _ = 2 ^ (n + 1) * S * ‖z‖ ^ (n + 1) := by ring

/-- Chebyshev's association inequality: `E|h|^j · E g(|h|) ≤ E[|h|^j g(|h|)]` for `g`
nondecreasing on `[0, ∞)`. -/
private lemma CE_cheb (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) (j : ℕ) {g : ℝ → ℝ}
    (hmono : MonotoneOn g (Set.Ici 0))
    (hint : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k * g ‖z‖) μ) :
    (∫ z, ‖z‖ ^ j ∂μ) * ∫ z, g ‖z‖ ∂μ ≤ ∫ z, ‖z‖ ^ j * g ‖z‖ ∂μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  set m := ∫ z, ‖z‖ ^ j ∂μ
  have hm : 0 ≤ m := integral_nonneg fun z => by positivity
  set t0 := m ^ ((j : ℝ)⁻¹)
  have ht0 : 0 ≤ t0 := Real.rpow_nonneg hm _
  have ht0j : t0 ^ j = m := Real.rpow_inv_natCast_pow hm hj.ne'
  have hg : Integrable (fun z : ℂ => g ‖z‖) μ := by simpa using hint 0
  have hpt : ∀ z : ℂ, 0 ≤ (‖z‖ ^ j - m) * (g ‖z‖ - g t0) := by
    intro z
    rcases le_total ‖z‖ t0 with h | h
    · refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      · rw [sub_nonpos, ← ht0j]; exact pow_le_pow_left₀ (norm_nonneg _) h j
      · rw [sub_nonpos]; exact hmono (norm_nonneg z) ht0 h
    · refine mul_nonneg ?_ ?_
      · rw [sub_nonneg, ← ht0j]; exact pow_le_pow_left₀ ht0 h j
      · rw [sub_nonneg]; exact hmono ht0 (norm_nonneg z) h
  have h0 := integral_nonneg (μ := μ) (Pi.le_def.mpr hpt)
  have heq : (fun z : ℂ => (‖z‖ ^ j - m) * (g ‖z‖ - g t0)) =
      fun z => ‖z‖ ^ j * g ‖z‖ - (g t0 * ‖z‖ ^ j + m * g ‖z‖) + m * g t0 := by
    funext z; ring
  have i1 : Integrable (fun z : ℂ => g t0 * ‖z‖ ^ j + m * g ‖z‖) μ :=
    ((hμ j).const_mul _).add (hg.const_mul _)
  have i2 : Integrable (fun z : ℂ => ‖z‖ ^ j * g ‖z‖ - (g t0 * ‖z‖ ^ j + m * g ‖z‖)) μ :=
    (hint j).sub i1
  rw [heq, integral_add i2 (integrable_const _), integral_sub (hint j) i1,
    integral_add ((hμ j).const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul,
    integral_const] at h0
  simp only [probReal_univ, smul_eq_mul, one_mul] at h0
  linarith

/-- Iterated Chebyshev: `Π_i E|h|^{k_i} · E g(|h|) ≤ E[|h|^{Σ k_i} g(|h|)]` for `g ≥ 0`
nondecreasing on `[0, ∞)`. -/
private lemma CE_prod_moments (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) {ι : Type*} (s : Finset ι) (k : ι → ℕ) :
    ∀ {g : ℝ → ℝ}, MonotoneOn g (Set.Ici 0) → (∀ t, 0 ≤ t → 0 ≤ g t) →
      (∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k * g ‖z‖) μ) →
      (∏ i ∈ s, ∫ z, ‖z‖ ^ k i ∂μ) * ∫ z, g ‖z‖ ∂μ ≤ ∫ z, ‖z‖ ^ (∑ i ∈ s, k i) * g ‖z‖ ∂μ := by
  induction s using Finset.induction_on with
  | empty => intro g _ _ _; simp
  | insert i s hi ih =>
    intro g hmono hnn hint
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    set N := ∑ j ∈ s, k j
    have hm : 0 ≤ ∫ z, ‖z‖ ^ k i ∂μ := integral_nonneg fun z => by positivity
    have hmono' : MonotoneOn (fun t => t ^ N * g t) (Set.Ici 0) := by
      intro a ha b hb hab
      exact mul_le_mul (pow_le_pow_left₀ ha hab N) (hmono ha hb hab) (hnn a ha)
        (pow_nonneg (le_trans ha hab) N)
    have hint' : ∀ k' : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k' * (‖z‖ ^ N * g ‖z‖)) μ := by
      intro k'
      refine (hint (k' + N)).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only
      ring
    calc (∫ z, ‖z‖ ^ k i ∂μ) * (∏ j ∈ s, ∫ z, ‖z‖ ^ k j ∂μ) * ∫ z, g ‖z‖ ∂μ
        = (∫ z, ‖z‖ ^ k i ∂μ) * ((∏ j ∈ s, ∫ z, ‖z‖ ^ k j ∂μ) * ∫ z, g ‖z‖ ∂μ) := by ring
      _ ≤ (∫ z, ‖z‖ ^ k i ∂μ) * ∫ z, ‖z‖ ^ N * g ‖z‖ ∂μ :=
          mul_le_mul_of_nonneg_left (ih hmono hnn hint) hm
      _ ≤ ∫ z, ‖z‖ ^ k i * (‖z‖ ^ N * g ‖z‖) ∂μ := CE_cheb μ hμ (k i) hmono' hint'
      _ = ∫ z, ‖z‖ ^ (k i + N) * g ‖z‖ ∂μ := by
          congr 1; funext z; ring

/-- The combinatorial constant `Σ_π (|π| - 1)!` over the set partitions of `{0, …, n-1}`. -/
private def CE_cc (n : ℕ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin n)), ((π.parts.card - 1).factorial : ℝ)

/-- `|𝒞^{(p,q)}(h)| · E g(|h|) ≤ c_{p+q} E[|h|^{p+q} g(|h|)]` for `g ≥ 0` nondecreasing on
`[0, ∞)`. -/
private lemma CE_ccum_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) (p q : ℕ) {g : ℝ → ℝ}
    (hmono : MonotoneOn g (Set.Ici 0)) (hnn : ∀ t, 0 ≤ t → 0 ≤ g t)
    (hint : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k * g ‖z‖) μ) :
    ‖ccum μ p q‖ * ∫ z, g ‖z‖ ∂μ ≤ CE_cc (p + q) * ∫ z, ‖z‖ ^ (p + q) * g ‖z‖ ∂μ := by
  have hEg : 0 ≤ ∫ z, g ‖z‖ ∂μ := integral_nonneg fun z => hnn _ (norm_nonneg _)
  have hX : ∀ (B : Finset (Fin (p + q))) (z : ℂ),
      ‖∏ i ∈ B, (if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) z‖ =
        ‖z‖ ^ B.card := by
    intro B z
    rw [norm_prod]
    rw [Finset.prod_congr rfl fun (i : Fin (p + q)) _ => (show
      ‖(if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) z‖ = ‖z‖ by
        split_ifs <;> simp), Finset.prod_const]
  have h1 : ‖ccum μ p q‖ ≤ ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
      ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, ∫ z, ‖z‖ ^ B.card ∂μ := by
    unfold ccum jointCum
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod,
      Complex.norm_natCast]
    gcongr with B hB
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [hX]
  calc ‖ccum μ p q‖ * ∫ z, g ‖z‖ ∂μ
      ≤ (∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
          ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, ∫ z, ‖z‖ ^ B.card ∂μ) *
          ∫ z, g ‖z‖ ∂μ := mul_le_mul_of_nonneg_right h1 hEg
    _ = ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
          ((π.parts.card - 1).factorial : ℝ) *
            ((∏ B ∈ π.parts, ∫ z, ‖z‖ ^ B.card ∂μ) * ∫ z, g ‖z‖ ∂μ) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun π _ => by ring
    _ ≤ ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
          ((π.parts.card - 1).factorial : ℝ) * ∫ z, ‖z‖ ^ (p + q) * g ‖z‖ ∂μ := by
        refine Finset.sum_le_sum fun π _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := CE_prod_moments μ hμ π.parts Finset.card hmono hnn hint
        rwa [π.sum_card_parts, Finset.card_univ, Fintype.card_fin] at this
    _ = CE_cc (p + q) * ∫ z, ‖z‖ ^ (p + q) * g ‖z‖ ∂μ := by
        rw [CE_cc, Finset.sum_mul]

/-- The triangular double sum `Σ_{p<L} Σ_{q<L-p}` as a sum over `{(p, q) : p + q < L}`. -/
private lemma CE_sum_S_eq (L : ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ p ∈ Finset.range L, ∑ q ∈ Finset.range (L - p), f p q = ∑ x ∈ CE_S L, f x.1 x.2 := by
  rw [CE_S, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_range, Finset.mem_filter] at hp ⊢
  omega

/-- The Taylor polynomial is continuous. -/
private lemma CE_tay_continuous (n : ℕ) (G : ℂ → ℂ) : Continuous (CE_tay n G) := by
  unfold CE_tay
  fun_prop

/-- The monomials `z^a z̄^b` are integrable when all moments are finite. -/
private lemma CE_int_mono (μ : Measure ℂ) (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ)
    (a b : ℕ) : Integrable (fun z : ℂ => z ^ a * starRingEnd ℂ z ^ b) μ := by
  refine (hμ (a + b)).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp [pow_add]

/-- The integral of the Taylor polynomial. -/
private lemma CE_int_tay (μ : Measure ℂ) (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ)
    (n : ℕ) (G : ℂ → ℂ) :
    Integrable (CE_tay n G) μ ∧ ∫ z, CE_tay n G z ∂μ =
      ∑ x ∈ CE_S n, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        ∫ z, z ^ x.1 * starRingEnd ℂ z ^ x.2 ∂μ := by
  have hi : ∀ x ∈ CE_S n, Integrable (fun z : ℂ => wirt x.1 x.2 G 0 /
      ((x.1.factorial * x.2.factorial : ℕ) : ℂ) * (z ^ x.1 * starRingEnd ℂ z ^ x.2)) μ :=
    fun x _ => (CE_int_mono μ hμ x.1 x.2).const_mul _
  refine ⟨?_, ?_⟩
  · unfold CE_tay
    exact integrable_finsetSum _ hi
  · unfold CE_tay
    rw [integral_finsetSum _ hi]
    simp only [integral_const_mul]

/-- The integral of the Taylor polynomial times `z̄`. -/
private lemma CE_int_tay_conj (μ : Measure ℂ) (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ)
    (n : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z => CE_tay n G z * starRingEnd ℂ z) μ ∧
      ∫ z, CE_tay n G z * starRingEnd ℂ z ∂μ =
      ∑ x ∈ CE_S n, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        ∫ z, z ^ x.1 * starRingEnd ℂ z ^ (x.2 + 1) ∂μ := by
  have heq : (fun z => CE_tay n G z * starRingEnd ℂ z) = fun z => ∑ x ∈ CE_S n,
      wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        (z ^ x.1 * starRingEnd ℂ z ^ (x.2 + 1)) := by
    funext z
    unfold CE_tay
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => by ring
  have hi : ∀ x ∈ CE_S n, Integrable (fun z : ℂ => wirt x.1 x.2 G 0 /
      ((x.1.factorial * x.2.factorial : ℕ) : ℂ) * (z ^ x.1 * starRingEnd ℂ z ^ (x.2 + 1))) μ :=
    fun x _ => (CE_int_mono μ hμ x.1 (x.2 + 1)).const_mul _
  rw [heq]
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  simp only [integral_const_mul]

/-- The cumulant expansion is exact on the Taylor polynomial: `E[P(h) h̄] =
Σ_{p+q≤l} 𝒞^{(p,q+1)} / (p! q!) E[P_{p,q}(h)]`, where `P_{p,q}` is the Taylor polynomial of
`F^{(p,q)}` of order `l - p - q`. -/
private lemma CE_poly_identity (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) {L : ℕ} {F : ℂ → ℂ}
    (hF : ContDiff ℝ L F) :
    ∫ z, CE_tay L F z * starRingEnd ℂ z ∂μ =
      ∑ y ∈ CE_S L, ccum μ y.1 (y.2 + 1) / ((y.1.factorial * y.2.factorial : ℕ) : ℂ) *
        ∫ z, CE_tay (L - y.1 - y.2) (wirt y.1 y.2 F) z ∂μ := by
  rw [(CE_int_tay_conj μ hμ L F).2]
  simp only [moment_ccum_recursion μ hμ, Finset.mul_sum, (CE_int_tay μ hμ _ _).2]
  simp only [← Finset.sum_product']
  rw [Finset.sum_comm' (t' := CE_S L) (s' := fun y => (CE_S L).filter
    fun x => y.1 ≤ x.1 ∧ y.2 ≤ x.2)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := CE_mem_S.1 hy
    refine Finset.sum_nbij' (fun x => (x.1 - y.1, x.2 - y.2)) (fun x => (x.1 + y.1, x.2 + y.2))
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, CE_mem_S] at hx ⊢
      omega
    · intro x hx
      simp only [Finset.mem_filter, CE_mem_S] at hx ⊢
      omega
    · intro x hx
      simp only [Finset.mem_filter, CE_mem_S] at hx
      ext <;> simp <;> omega
    · intro x hx
      simp
    · intro x hx
      simp only [Finset.mem_filter, CE_mem_S] at hx
      obtain ⟨a, b⟩ := x
      obtain ⟨p, q⟩ := y
      simp only at hx hy' ⊢
      obtain ⟨hab, hpa, hqb⟩ := hx
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + p := ⟨a - p, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + q := ⟨b - q, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [CE_wirt_wirt hF a' b' p q (by omega)]
      have e1 : (((a' + p).choose p : ℕ) : ℂ) * (a'.factorial : ℂ) * (p.factorial : ℂ) =
          ((a' + p).factorial : ℂ) := by
        exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial a' p
      have e2 : (((b' + q).choose q : ℕ) : ℂ) * (b'.factorial : ℂ) * (q.factorial : ℂ) =
          ((b' + q).factorial : ℂ) := by
        exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial b' q
      have f1 : (a'.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have f2 : (b'.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have f3 : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have f4 : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have c1 : (((a' + p).choose p : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have c2 : (((b' + q).choose q : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      push_cast
      rw [← e1, ← e2]
      field_simp
  · intro x y
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter, CE_mem_S]
    omega

/-- The pointwise remainder bound: `‖G(z) - P(z)‖ ≤ 2^n (A ‖z‖^n + B ‖z‖^n 1_{‖z‖>M})`. -/
private lemma CE_pt {n : ℕ} {G : ℂ → ℂ} (hG : ContDiff ℝ n G) {M A B : ℝ} (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : ∀ a b, a + b = n → ∀ z : ℂ, ‖z‖ ≤ M → ‖wirt a b G z‖ ≤ A)
    (hB : ∀ a b, a + b = n → ∀ z : ℂ, ‖wirt a b G z‖ ≤ B) (z : ℂ) :
    ‖G z - CE_tay n G z‖ ≤
      2 ^ n * (A * ‖z‖ ^ n + B * Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ n) z) := by
  by_cases hz : ‖z‖ ≤ M
  · have h := CE_taylor n hG hA z hz
    have : 0 ≤ B * Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ n) z :=
      mul_nonneg hB0 (Set.indicator_nonneg (fun z _ => by positivity) z)
    have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
    nlinarith
  · have h := CE_taylor n hG (r := ‖z‖) (fun a b hab w _ => hB a b hab w) z le_rfl
    have hi : Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ n) z = ‖z‖ ^ n :=
      Set.indicator_of_mem (show M < ‖z‖ from lt_of_not_ge hz) _
    rw [hi]
    have : 0 ≤ A * ‖z‖ ^ n := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
    nlinarith

/-- From a pointwise bound to the integrals: `H` is integrable and
`‖E H - E Q‖ ≤ c (A E|h|^k + B E[|h|^k 1_{|h|>M}])`. -/
private lemma CE_int_bound (μ : Measure ℂ) (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ)
    {H Q : ℂ → ℂ} (hH : Continuous H) (hQ : Continuous Q) (hQi : Integrable Q μ) {k : ℕ}
    {M A B c : ℝ}
    (hpt : ∀ z, ‖H z - Q z‖ ≤
      c * (A * ‖z‖ ^ k + B * Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ k) z)) :
    Integrable H μ ∧ ‖(∫ z, H z ∂μ) - ∫ z, Q z ∂μ‖ ≤
      c * (A * ∫ z, ‖z‖ ^ k ∂μ +
        B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ k) z ∂μ) := by
  have hind : Integrable (fun z => Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ k) z) μ :=
    (hμ k).indicator (measurableSet_lt measurable_const continuous_norm.measurable)
  have hbd : Integrable (fun z => c * (A * ‖z‖ ^ k +
      B * Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ k) z)) μ :=
    (((hμ k).const_mul A).add (hind.const_mul B)).const_mul c
  have hd : Integrable (fun z => H z - Q z) μ :=
    hbd.mono' (hH.sub hQ).aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  have hHi : Integrable H μ := (hd.add hQi).congr (Filter.Eventually.of_forall fun z => by simp)
  refine ⟨hHi, ?_⟩
  rw [← integral_sub hHi hQi]
  refine (norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add ((hμ k).const_mul A) (hind.const_mul B), integral_const_mul,
    integral_const_mul]

/-- `|𝒞^{(p,q)}| (A E|h|^k + B E[|h|^k 1_{|h|>M}]) ≤ c_{p+q} (A E|h|^{p+q+k} +
B E[|h|^{p+q+k} 1_{|h|>M}])` for `A, B ≥ 0`. -/
private lemma CE_ccum_mom (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) (p q k : ℕ) {M A B : ℝ} (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) :
    ‖ccum μ p q‖ * (A * ∫ z, ‖z‖ ^ k ∂μ +
        B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ k) z ∂μ) ≤
      CE_cc (p + q) * (A * ∫ z, ‖z‖ ^ (p + q + k) ∂μ +
        B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (p + q + k)) z ∂μ) := by
  have h1 := CE_ccum_le μ hμ p q (g := fun t => t ^ k)
    (fun a ha b _ hab => pow_le_pow_left₀ ha hab k) (fun t ht => pow_nonneg ht k)
    (fun j => by simpa [← pow_add] using hμ (j + k))
  have hg : ∀ j : ℕ, (fun z : ℂ => ‖z‖ ^ j * Set.indicator (Set.Ioi M) (fun t => t ^ k) ‖z‖) =
      fun z => Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (j + k)) z := by
    intro j
    funext z
    by_cases hz : M < ‖z‖
    · rw [Set.indicator_of_mem (show ‖z‖ ∈ Set.Ioi M from hz),
        Set.indicator_of_mem (show z ∈ {z : ℂ | M < ‖z‖} from hz), pow_add]
    · rw [Set.indicator_of_notMem (show ‖z‖ ∉ Set.Ioi M from hz),
        Set.indicator_of_notMem (show z ∉ {z : ℂ | M < ‖z‖} from hz), mul_zero]
  have h2 := CE_ccum_le μ hμ p q (g := Set.indicator (Set.Ioi M) (fun t => t ^ k))
    (by
      intro a ha b hb hab
      by_cases h : M < a
      · rw [Set.indicator_of_mem (show a ∈ Set.Ioi M from h),
          Set.indicator_of_mem (show b ∈ Set.Ioi M from lt_of_lt_of_le h hab)]
        exact pow_le_pow_left₀ ha hab k
      · rw [Set.indicator_of_notMem (show a ∉ Set.Ioi M from h)]
        exact Set.indicator_nonneg (fun t _ => pow_nonneg (le_trans ha hab) k) b)
    (fun t ht => by
      by_cases h' : M < t
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioi M from h')]; exact pow_nonneg ht k
      · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi M from h')])
    (fun j => by
      rw [hg j]
      exact (hμ (j + k)).indicator (measurableSet_lt measurable_const continuous_norm.measurable))
  have e0 := hg 0
  simp only [pow_zero, one_mul, zero_add] at e0
  rw [e0, hg (p + q)] at h2
  simp only [← pow_add] at h1
  have := mul_le_mul_of_nonneg_left h1 hA0
  have := mul_le_mul_of_nonneg_left h2 hB0
  nlinarith

/-- Lemma 2.11 [lem:complex_cumu], (2.26) [5.16], with the remainder bound for an arbitrary
truncation radius `M` (the paper takes `M = N^{τ-1/2}`); `K` depends on `l` only. -/
theorem cumulant_expansion (l : ℕ) :
    ∃ K : ℝ, ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ] (F : ℂ → ℂ) (M A B : ℝ),
      (∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) → ContDiff ℝ (l + 1 : ℕ) F → 0 < M →
      (∀ p q : ℕ, p + q = l + 1 → ∀ z : ℂ, ‖z‖ ≤ M → ‖wirt p q F z‖ ≤ A) →
      (∀ p q : ℕ, p + q = l + 1 → ∀ z : ℂ, ‖wirt p q F z‖ ≤ B) →
      ‖(∫ z, F z * starRingEnd ℂ z ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum μ p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) * ∫ z, wirt p q F z ∂μ‖ ≤
        K * ((∫ z, ‖z‖ ^ (l + 2) ∂μ) * A +
          (∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (l + 2)) z ∂μ) * B) := by
  refine ⟨2 ^ (l + 1) + ∑ y ∈ CE_S (l + 1), 2 ^ (l + 1 - y.1 - y.2) /
    ((y.1.factorial * y.2.factorial : ℕ) : ℝ) * CE_cc (y.1 + (y.2 + 1)), ?_⟩
  intro μ _ F M A B hμ hF hM hA hB
  set L := l + 1 with hL
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA L 0 rfl 0 (by simpa using hM.le))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB L 0 rfl 0)
  set T := A * ∫ z, ‖z‖ ^ (l + 2) ∂μ +
    B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (l + 2)) z ∂μ with hT
  have hT0 : 0 ≤ T := by
    have h1 : 0 ≤ ∫ z, ‖z‖ ^ (l + 2) ∂μ := integral_nonneg fun z => by positivity
    have h2 : 0 ≤ ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (l + 2)) z ∂μ :=
      integral_nonneg fun z => Set.indicator_nonneg (fun z _ => by positivity) z
    positivity
  rw [CE_sum_S_eq L (fun p q => ccum μ p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
    ∫ z, wirt p q F z ∂μ)]
  -- the term `E[h̄ F(h)]`
  have hP := CE_pt hF hA0 hB0 hA hB
  have hFc := CE_int_bound μ hμ (H := fun z => F z * starRingEnd ℂ z)
    (Q := fun z => CE_tay L F z * starRingEnd ℂ z) (k := l + 2) (M := M) (A := A) (B := B)
    (c := 2 ^ L) (by fun_prop) (by have := CE_tay_continuous L F; fun_prop)
    (CE_int_tay_conj μ hμ L F).1 (fun z => by
      rw [← sub_mul, norm_mul, Complex.norm_conj]
      have hz := mul_le_mul_of_nonneg_right (hP z) (norm_nonneg z)
      refine hz.trans (le_of_eq ?_)
      by_cases hm : M < ‖z‖
      · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | M < ‖z‖} from hm),
          Set.indicator_of_mem (show z ∈ {z : ℂ | M < ‖z‖} from hm)]
        ring
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | M < ‖z‖} from hm),
          Set.indicator_of_notMem (show z ∉ {z : ℂ | M < ‖z‖} from hm)]
        ring)
  -- the terms `E F^{(p,q)}(h)`
  have hG : ∀ y ∈ CE_S L, ‖(∫ z, wirt y.1 y.2 F z ∂μ) -
      ∫ z, CE_tay (L - y.1 - y.2) (wirt y.1 y.2 F) z ∂μ‖ ≤
      2 ^ (L - y.1 - y.2) * (A * ∫ z, ‖z‖ ^ (L - y.1 - y.2) ∂μ +
        B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (L - y.1 - y.2)) z ∂μ) := by
    intro y hy
    have hy' := CE_mem_S.1 hy
    have hGs : ContDiff ℝ (L - y.1 - y.2 : ℕ) (wirt y.1 y.2 F) :=
      CE_contDiff_wirt hF _ _ _ (by omega)
    have hww : ∀ a b, a + b = L - y.1 - y.2 → wirt a b (wirt y.1 y.2 F) =
        wirt (a + y.1) (b + y.2) F := fun a b hab => CE_wirt_wirt hF a b y.1 y.2 (by omega)
    exact (CE_int_bound μ hμ hGs.continuous (CE_tay_continuous _ _) (CE_int_tay μ hμ _ _).1
      (CE_pt hGs hA0 hB0 (fun a b hab z hz => by rw [hww a b hab]; exact hA _ _ (by omega) z hz)
        (fun a b hab z => by rw [hww a b hab]; exact hB _ _ (by omega) z))).2
  -- the exact identity for the Taylor polynomial
  have hid := CE_poly_identity μ hμ hF
  have hsplit : (∫ z, F z * starRingEnd ℂ z ∂μ) - ∑ y ∈ CE_S L, ccum μ y.1 (y.2 + 1) /
      ((y.1.factorial * y.2.factorial : ℕ) : ℂ) * ∫ z, wirt y.1 y.2 F z ∂μ =
      ((∫ z, F z * starRingEnd ℂ z ∂μ) - ∫ z, CE_tay L F z * starRingEnd ℂ z ∂μ) -
        ∑ y ∈ CE_S L, ccum μ y.1 (y.2 + 1) / ((y.1.factorial * y.2.factorial : ℕ) : ℂ) *
          ((∫ z, wirt y.1 y.2 F z ∂μ) - ∫ z, CE_tay (L - y.1 - y.2) (wirt y.1 y.2 F) z ∂μ) := by
    rw [hid]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have hsum : ‖∑ y ∈ CE_S L, ccum μ y.1 (y.2 + 1) / ((y.1.factorial * y.2.factorial : ℕ) : ℂ) *
      ((∫ z, wirt y.1 y.2 F z ∂μ) - ∫ z, CE_tay (L - y.1 - y.2) (wirt y.1 y.2 F) z ∂μ)‖ ≤
      (∑ y ∈ CE_S L, 2 ^ (l + 1 - y.1 - y.2) / ((y.1.factorial * y.2.factorial : ℕ) : ℝ) *
        CE_cc (y.1 + (y.2 + 1))) * T := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    have hy' := CE_mem_S.1 hy
    have hfac : (0 : ℝ) < ((y.1.factorial * y.2.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    have hcm := CE_ccum_mom μ hμ y.1 (y.2 + 1) (L - y.1 - y.2) (M := M) hA0 hB0
    have hidx : y.1 + (y.2 + 1) + (L - y.1 - y.2) = l + 2 := by omega
    rw [hidx] at hcm
    rw [norm_mul, norm_div, Complex.norm_natCast]
    have h2 : (0 : ℝ) ≤ 2 ^ (L - y.1 - y.2) := by positivity
    calc ‖ccum μ y.1 (y.2 + 1)‖ / ((y.1.factorial * y.2.factorial : ℕ) : ℝ) *
          ‖(∫ z, wirt y.1 y.2 F z ∂μ) - ∫ z, CE_tay (L - y.1 - y.2) (wirt y.1 y.2 F) z ∂μ‖
        ≤ ‖ccum μ y.1 (y.2 + 1)‖ / ((y.1.factorial * y.2.factorial : ℕ) : ℝ) *
          (2 ^ (L - y.1 - y.2) * (A * ∫ z, ‖z‖ ^ (L - y.1 - y.2) ∂μ +
            B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (L - y.1 - y.2)) z ∂μ)) :=
          mul_le_mul_of_nonneg_left (hG y hy) (by positivity)
      _ = 2 ^ (L - y.1 - y.2) / ((y.1.factorial * y.2.factorial : ℕ) : ℝ) *
          (‖ccum μ y.1 (y.2 + 1)‖ * (A * ∫ z, ‖z‖ ^ (L - y.1 - y.2) ∂μ +
            B * ∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (L - y.1 - y.2)) z ∂μ)) := by
          ring
      _ ≤ 2 ^ (L - y.1 - y.2) / ((y.1.factorial * y.2.factorial : ℕ) : ℝ) *
          (CE_cc (y.1 + (y.2 + 1)) * T) :=
          mul_le_mul_of_nonneg_left hcm (by positivity)
      _ = 2 ^ (l + 1 - y.1 - y.2) / ((y.1.factorial * y.2.factorial : ℕ) : ℝ) *
          CE_cc (y.1 + (y.2 + 1)) * T := by ring
  have hfirst : ‖(∫ z, F z * starRingEnd ℂ z ∂μ) - ∫ z, CE_tay L F z * starRingEnd ℂ z ∂μ‖ ≤
      2 ^ (l + 1) * T := hFc.2
  have hTe : (∫ z, ‖z‖ ^ (l + 2) ∂μ) * A +
      (∫ z, Set.indicator {z : ℂ | M < ‖z‖} (fun z => ‖z‖ ^ (l + 2)) z ∂μ) * B = T := by
    rw [hT]; ring
  rw [hTe]
  calc _ ≤ ‖(∫ z, F z * starRingEnd ℂ z ∂μ) - ∫ z, CE_tay L F z * starRingEnd ℂ z ∂μ‖ +
        ‖∑ y ∈ CE_S L, ccum μ y.1 (y.2 + 1) / ((y.1.factorial * y.2.factorial : ℕ) : ℂ) *
          ((∫ z, wirt y.1 y.2 F z ∂μ) - ∫ z, CE_tay (L - y.1 - y.2) (wirt y.1 y.2 F) z ∂μ)‖ :=
        norm_sub_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add hfirst hsum

end RBMTransitionEdge

end
