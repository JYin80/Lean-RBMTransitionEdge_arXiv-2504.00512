module

public import RBMTransitionEdge.Flow.Chain
public import RBMTransitionEdge.Flow.ChainDer
public import RBMTransitionEdge.Flow.Endpoint
public import RBMTransitionEdge.LocalLaw.LocalLaw
public import RBMTransitionEdge.Prob.BlockOU

@[expose] public section

/-!
# The comparison lemma of §3 for the laws of `H_t`

Lemma 3.13 [main_lemma_com]: two entry laws that match to order three, (3.36) [comH0], and to
order four up to `K N^{-δ}`, (3.37) [comH], give the same `E L` of (3.1) [def_ML] up to
`N^{τ'} N^{-1-δ} η^{-2}`, (3.38) [eq:cpmparison], for the laws of `H_t` of (4.1) [defVt].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Taylor expansion in Wirtinger form -/

/-- `G` has real derivative `v ↦ α v + β v̄` at `w`. -/
private def Cmp_HasW (G : ℂ → ℂ) (w α β : ℂ) : Prop :=
  ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L w ∧ ∀ v, L v = α * v + β * starRingEnd ℂ v

/-- Every real-linear map on `ℂ` is `v ↦ α v + β v̄` with its two Wirtinger coefficients. -/
private lemma Cmp_clm_split (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
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
private lemma Cmp_HasW.eq {G : ℂ → ℂ} {w α β : ℂ} (h : Cmp_HasW G w α β) :
    dW G w = α ∧ dWbar G w = β := by
  obtain ⟨L, hL, hv⟩ := h
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [dW, dWbar, hL.fderiv, hv, map_one, mul_one, Complex.conj_I]
  constructor
  · linear_combination (β - α) / 2 * hI
  · linear_combination (α - β) / 2 * hI

/-- A differentiable function has derivative `v ↦ ∂G v + ∂̄G v̄`. -/
private lemma Cmp_HasW_of_diff {G : ℂ → ℂ} {w : ℂ} (h : DifferentiableAt ℝ G w) :
    Cmp_HasW G w (dW G w) (dWbar G w) :=
  ⟨fderiv ℝ G w, h.hasFDerivAt, fun v => Cmp_clm_split _ v⟩

/-- Wirtinger derivatives of a difference. -/
private lemma Cmp_HasW.sub {G H : ℂ → ℂ} {w α β α' β' : ℂ} (hG : Cmp_HasW G w α β)
    (hH : Cmp_HasW H w α' β') : Cmp_HasW (fun z => G z - H z) w (α - α') (β - β') := by
  obtain ⟨L, hL, hv⟩ := hG
  obtain ⟨L', hL', hv'⟩ := hH
  exact ⟨L - L', hL.sub hL', fun v => by simp [hv, hv']; ring⟩

/-- Wirtinger derivatives of a constant multiple. -/
private lemma Cmp_HasW.const_mul {G : ℂ → ℂ} {w α β : ℂ} (c : ℂ) (hG : Cmp_HasW G w α β) :
    Cmp_HasW (fun z => c * G z) w (c * α) (c * β) := by
  obtain ⟨L, hL, hv⟩ := hG
  exact ⟨c • L, hL.const_mul c, fun v => by simp [hv]; ring⟩

/-- Wirtinger derivatives of a finite sum. -/
private lemma Cmp_HasW.sum {ι : Type*} (s : Finset ι) {G : ι → ℂ → ℂ} {w : ℂ} {α β : ι → ℂ}
    (h : ∀ i, Cmp_HasW (G i) w (α i) (β i)) :
    Cmp_HasW (fun z => ∑ i ∈ s, G i z) w (∑ i ∈ s, α i) (∑ i ∈ s, β i) := by
  choose L hL hv using h
  refine ⟨∑ i ∈ s, L i, HasFDerivAt.fun_sum (fun i _ => hL i), fun v => ?_⟩
  simp only [FunLike.coe_sum, Finset.sum_apply, hv, Finset.sum_add_distrib,
    Finset.sum_mul]

/-- The monomial `z^a z̄^b` has Wirtinger derivatives `a z^{a-1} z̄^b` and `b z^a z̄^{b-1}`. -/
private lemma Cmp_HasW_mono (a b : ℕ) (w : ℂ) :
    Cmp_HasW (fun z => z ^ a * starRingEnd ℂ z ^ b) w
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
private lemma Cmp_contDiff_dW {n : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ (n + 1 : ℕ) G) :
    ContDiff ℝ n (dW G) ∧ ContDiff ℝ n (dWbar G) := by
  have hD : ContDiff ℝ n (fderiv ℝ G) := h.fderiv_right (by norm_cast)
  have h1 : ContDiff ℝ n (fun z => fderiv ℝ G z 1) := hD.clm_apply contDiff_const
  have hI : ContDiff ℝ n (fun z => fderiv ℝ G z Complex.I) := hD.clm_apply contDiff_const
  exact ⟨(h1.sub (contDiff_const.mul hI)).div_const 2,
    (h1.add (contDiff_const.mul hI)).div_const 2⟩

/-- The derivative of `z ↦ DG(z) v` at `w` is `u ↦ D²G(w) u v`, in Wirtinger form. -/
private lemma Cmp_HasW_apply {G : ℂ → ℂ} {w : ℂ} (h : DifferentiableAt ℝ (fderiv ℝ G) w) (v : ℂ) :
    Cmp_HasW (fun z => fderiv ℝ G z v) w
      ((fderiv ℝ (fderiv ℝ G) w 1 v - Complex.I * fderiv ℝ (fderiv ℝ G) w Complex.I v) / 2)
      ((fderiv ℝ (fderiv ℝ G) w 1 v + Complex.I * fderiv ℝ (fderiv ℝ G) w Complex.I v) / 2) := by
  have := h.hasFDerivAt.clm_apply (hasFDerivAt_const v w)
  refine ⟨_, this, fun u => ?_⟩
  simpa using Cmp_clm_split ((fderiv ℝ (fderiv ℝ G) w).flip v) u

/-- Wirtinger derivatives of a sum. -/
private lemma Cmp_HasW.add {G H : ℂ → ℂ} {w α β α' β' : ℂ} (hG : Cmp_HasW G w α β)
    (hH : Cmp_HasW H w α' β') : Cmp_HasW (fun z => G z + H z) w (α + α') (β + β') := by
  obtain ⟨L, hL, hv⟩ := hG
  obtain ⟨L', hL', hv'⟩ := hH
  exact ⟨L + L', hL.add hL', fun v => by simp [hv, hv']; ring⟩

/-- Wirtinger derivatives of `G / 2`. -/
private lemma Cmp_HasW.div_two {G : ℂ → ℂ} {w α β : ℂ} (hG : Cmp_HasW G w α β) :
    Cmp_HasW (fun z => G z / 2) w (α / 2) (β / 2) := by
  have := hG.const_mul (1 / 2)
  simp only [one_div] at this
  convert this using 1 <;> [funext z; skip; skip] <;> ring

/-- `∂` and `∂̄` commute on `C^2` functions. -/
private lemma Cmp_comm {G : ℂ → ℂ} (h : ContDiff ℝ 2 G) : dW (dWbar G) = dWbar (dW G) := by
  funext w
  have hd : DifferentiableAt ℝ (fderiv ℝ G) w :=
    ((h.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) w
  have hs : IsSymmSndFDerivAt ℝ G w := h.contDiffAt.isSymmSndFDerivAt (by simp)
  have h1 := Cmp_HasW_apply hd 1
  have hI := Cmp_HasW_apply hd Complex.I
  have hb := ((h1.add (hI.const_mul Complex.I)).div_two).eq.1
  have ha := ((h1.sub (hI.const_mul Complex.I)).div_two).eq.2
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsym := hs 1 Complex.I
  change dW (fun z => (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) / 2) w =
    dWbar (fun z => (fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I) / 2) w
  rw [hb, ha]
  linear_combination (Complex.I / 2) * hsym

/-- `C^N` gives `C^{N-1}` for `∂G` and `∂̄G` in the `≤` form. -/
private lemma Cmp_contDiff_dW' {n N : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ N G) (hn : n + 1 ≤ N) :
    ContDiff ℝ n (dW G) ∧ ContDiff ℝ n (dWbar G) :=
  Cmp_contDiff_dW (h.of_le (by exact_mod_cast hn))

/-- `F^{(p,q)}` is `C^n` when `F` is `C^N` with `n + p + q ≤ N`. -/
private lemma Cmp_contDiff_wirt {N : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ N G) (n p q : ℕ)
    (hn : n + p + q ≤ N) : ContDiff ℝ n (wirt p q G) := by
  have hq : ∀ q N : ℕ, ∀ G : ℂ → ℂ, ContDiff ℝ N G → ∀ n : ℕ, n + q ≤ N →
      ContDiff ℝ n (dWbar^[q] G) := by
    intro q
    induction q with
    | zero => intro N G h n hn; exact h.of_le (by exact_mod_cast hn)
    | succ q ih =>
      intro N G h n hn
      rw [Function.iterate_succ_apply]
      exact ih (n + q) _ (Cmp_contDiff_dW' h (by omega)).2 n le_rfl
  have hp : ∀ p N : ℕ, ∀ G : ℂ → ℂ, ContDiff ℝ N G → ∀ n : ℕ, n + p ≤ N →
      ContDiff ℝ n (dW^[p] G) := by
    intro p
    induction p with
    | zero => intro N G h n hn; exact h.of_le (by exact_mod_cast hn)
    | succ p ih =>
      intro N G h n hn
      rw [Function.iterate_succ_apply]
      exact ih (n + p) _ (Cmp_contDiff_dW' h (by omega)).1 n le_rfl
  exact hp p (n + p) _ (hq q N G h (n + p) (by omega)) n le_rfl

/-- `∂ ∂̄^b G = ∂̄^b ∂ G` for `G` of class `C^N`, `b + 1 ≤ N`. -/
private lemma Cmp_comm_iter1 (b : ℕ) : ∀ {N : ℕ} {G : ℂ → ℂ}, ContDiff ℝ N G → b + 1 ≤ N →
    dW (dWbar^[b] G) = dWbar^[b] (dW G) := by
  induction b with
  | zero => intro N G _ _; rfl
  | succ b ih =>
    intro N G h hb
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih (Cmp_contDiff_dW' h (n := N - 1) (by omega)).2 (by omega),
      Cmp_comm (h.of_le (by exact_mod_cast (show 2 ≤ N by omega)))]

/-- `∂̄^b ∂^p H = ∂^p ∂̄^b H` for `H` of class `C^N`, `p + b ≤ N`. -/
private lemma Cmp_comm_iter (p : ℕ) : ∀ {N b : ℕ} {H : ℂ → ℂ}, ContDiff ℝ N H → p + b ≤ N →
    dWbar^[b] (dW^[p] H) = dW^[p] (dWbar^[b] H) := by
  induction p with
  | zero => intro N b H _ _; rfl
  | succ p ih =>
    intro N b H h hb
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih (Cmp_contDiff_dW' h (n := N - 1) (by omega)).1 (by omega),
      Cmp_comm_iter1 b h (by omega)]

/-- `(F^{(p,q)})^{(a,b)} = F^{(a+p, b+q)}` for `F` of class `C^N`, `p + q + b ≤ N`. -/
private lemma Cmp_wirt_wirt {N : ℕ} {G : ℂ → ℂ} (h : ContDiff ℝ N G) (a b p q : ℕ)
    (hb : p + q + b ≤ N) : wirt a b (wirt p q G) = wirt (a + p) (b + q) G := by
  unfold wirt
  have hH : ContDiff ℝ (p + b : ℕ) (dWbar^[q] G) := Cmp_contDiff_wirt h (p + b) 0 q (by omega)
  rw [Cmp_comm_iter p hH le_rfl,
    ← Function.iterate_add_apply, ← Function.iterate_add_apply]

/-- Rewriting the Wirtinger coefficients. -/
private lemma Cmp_HasW.congr {G : ℂ → ℂ} {w α β α' β' : ℂ} (h : Cmp_HasW G w α β) (hα : α = α')
    (hβ : β = β') : Cmp_HasW G w α' β' := hα ▸ hβ ▸ h

/-- A derivative `v ↦ α v + β v̄` has operator norm at most `‖α‖ + ‖β‖`. -/
private lemma Cmp_HasW.norm_fderiv_le {G : ℂ → ℂ} {w α β : ℂ} (h : Cmp_HasW G w α β) :
    DifferentiableAt ℝ G w ∧ ‖fderiv ℝ G w‖ ≤ ‖α‖ + ‖β‖ := by
  obtain ⟨L, hL, hv⟩ := h
  refine ⟨hL.differentiableAt, ?_⟩
  rw [hL.fderiv]
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  rw [hv]
  calc ‖α * v + β * starRingEnd ℂ v‖ ≤ ‖α * v‖ + ‖β * starRingEnd ℂ v‖ := norm_add_le _ _
    _ = (‖α‖ + ‖β‖) * ‖v‖ := by simp; ring

/-- The index set `{(a, b) : a + b < n}`. -/
private def Cmp_S (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun x => x.1 + x.2 < n

/-- Membership in `{(a, b) : a + b < n}`. -/
private lemma Cmp_mem_S {n : ℕ} {x : ℕ × ℕ} : x ∈ Cmp_S n ↔ x.1 + x.2 < n := by
  simp only [Cmp_S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The Taylor polynomial of order `n - 1` at `0` in Wirtinger form:
`Σ_{a+b<n} G^{(a,b)}(0) z^a z̄^b / (a! b!)`. -/
private def Cmp_tay (n : ℕ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ x ∈ Cmp_S n, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
    (z ^ x.1 * starRingEnd ℂ z ^ x.2)

/-- The Taylor polynomial takes the value `G(0)` at `0`. -/
private lemma Cmp_tay_zero (n : ℕ) (G : ℂ → ℂ) : Cmp_tay (n + 1) G 0 = G 0 := by
  unfold Cmp_tay
  rw [Finset.sum_eq_single (0, 0)]
  · simp [wirt]
  · rintro ⟨a, b⟩ _ hab
    have : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact hab (by rw [h.1, h.2])
    rcases this with h | h <;> simp [h]
  · intro h
    exact absurd (Cmp_mem_S.2 (by simp)) h

/-- Shifting the first index: terms with `a = 0` vanish. -/
private lemma Cmp_sum_S_shift1 (n : ℕ) (f : ℕ × ℕ → ℂ) (hf : ∀ b, f (0, b) = 0) :
    ∑ x ∈ Cmp_S (n + 1), f x = ∑ y ∈ Cmp_S n, f (y.1 + 1, y.2) := by
  have hinj : Set.InjOn (fun y : ℕ × ℕ => (y.1 + 1, y.2)) (Cmp_S n) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) h.2
  rw [← Finset.sum_image (g := fun y : ℕ × ℕ => (y.1 + 1, y.2)) (f := f) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Cmp_mem_S.2 (by have := Cmp_mem_S.1 hy; simp only at this ⊢; omega)
  · obtain ⟨a, b⟩ := x
    rcases a with _ | a
    · exact hf b
    · exact absurd (Finset.mem_image.2 ⟨(a, b), Cmp_mem_S.2 (by
        have := Cmp_mem_S.1 hx; simp only at this ⊢; omega), rfl⟩) hx'

/-- Shifting the second index: terms with `b = 0` vanish. -/
private lemma Cmp_sum_S_shift2 (n : ℕ) (f : ℕ × ℕ → ℂ) (hf : ∀ a, f (a, 0) = 0) :
    ∑ x ∈ Cmp_S (n + 1), f x = ∑ y ∈ Cmp_S n, f (y.1, y.2 + 1) := by
  have hinj : Set.InjOn (fun y : ℕ × ℕ => (y.1, y.2 + 1)) (Cmp_S n) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  rw [← Finset.sum_image (g := fun y : ℕ × ℕ => (y.1, y.2 + 1)) (f := f) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Cmp_mem_S.2 (by have := Cmp_mem_S.1 hy; simp only at this ⊢; omega)
  · obtain ⟨a, b⟩ := x
    rcases b with _ | b
    · exact hf a
    · exact absurd (Finset.mem_image.2 ⟨(a, b), Cmp_mem_S.2 (by
        have := Cmp_mem_S.1 hx; simp only at this ⊢; omega), rfl⟩) hx'

/-- The Wirtinger derivatives of the Taylor polynomial are the Taylor polynomials of `∂G`, `∂̄G`. -/
private lemma Cmp_HasW_tay {n : ℕ} {G : ℂ → ℂ} (hG : ContDiff ℝ (n + 1 : ℕ) G) (w : ℂ) :
    Cmp_HasW (Cmp_tay (n + 1) G) w (Cmp_tay n (dW G) w) (Cmp_tay n (dWbar G) w) := by
  have h := Cmp_HasW.sum (Cmp_S (n + 1)) (fun x => (Cmp_HasW_mono x.1 x.2 w).const_mul
    (wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ)))
  refine h.congr ?_ ?_
  · rw [Cmp_sum_S_shift1 n _ (fun b => by simp)]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := Cmp_mem_S.1 hy
    have hw : wirt y.1 y.2 (dW G) = wirt (y.1 + 1) y.2 G := by
      have := Cmp_wirt_wirt hG y.1 y.2 1 0 (by omega)
      simpa [wirt] using this
    rw [hw]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
    have h1 : (y.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (y.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
  · rw [Cmp_sum_S_shift2 n _ (fun a => by simp)]
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
private lemma Cmp_taylor (n : ℕ) : ∀ {G : ℂ → ℂ}, ContDiff ℝ n G → ∀ {r S : ℝ},
    (∀ a b, a + b = n → ∀ w : ℂ, ‖w‖ ≤ r → ‖wirt a b G w‖ ≤ S) →
    ∀ z : ℂ, ‖z‖ ≤ r → ‖G z - Cmp_tay n G z‖ ≤ 2 ^ n * S * ‖z‖ ^ n := by
  induction n with
  | zero =>
    intro G _ r S hS z hz
    have h := hS 0 0 rfl z hz
    simpa [Cmp_tay, Cmp_S, wirt] using h
  | succ n ih =>
    intro G hG r S hS z hz
    have hS0 : 0 ≤ S :=
      (norm_nonneg _).trans (hS (n + 1) 0 rfl 0 (by simpa using (norm_nonneg z).trans hz))
    have hd := Cmp_contDiff_dW hG
    have hGd : Differentiable ℝ G := hG.differentiable (by norm_cast)
    have ih1 := ih hd.1 (r := r) (S := S) (fun a b hab w hw => by
      have := Cmp_wirt_wirt hG a b 1 0 (by omega)
      simp only [wirt, Function.iterate_zero, id_eq, Function.iterate_one, add_zero] at this
      have h' := hS (a + 1) b (by omega) w hw
      simp only [wirt] at h' ⊢
      rwa [this])
    have ih2 := ih hd.2 (r := r) (S := S) (fun a b hab w hw => by
      have h' := hS a (b + 1) (by omega) w hw
      simpa only [wirt, Function.iterate_succ_apply] using h')
    set R : ℂ → ℂ := fun w => G w - Cmp_tay (n + 1) G w
    have hR : ∀ w, Cmp_HasW R w (dW G w - Cmp_tay n (dW G) w) (dWbar G w - Cmp_tay n (dWbar G) w) :=
      fun w => (Cmp_HasW_of_diff (hGd w)).sub (Cmp_HasW_tay hG w)
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
    have hR0 : R 0 = 0 := by simp [R, Cmp_tay_zero]
    rw [hR0, sub_zero, sub_zero] at hmvt
    calc ‖G z - Cmp_tay (n + 1) G z‖ = ‖R z‖ := rfl
      _ ≤ 2 ^ (n + 1) * S * ‖z‖ ^ n * ‖z‖ := hmvt
      _ = 2 ^ (n + 1) * S * ‖z‖ ^ (n + 1) := by ring

/-- The Taylor polynomial is continuous. -/
private lemma Cmp_tay_continuous (n : ℕ) (G : ℂ → ℂ) : Continuous (Cmp_tay n G) := by
  unfold Cmp_tay
  fun_prop

/-- The monomials `z^a z̄^b` are integrable when all moments are finite. -/
private lemma Cmp_int_mono (μ : Measure ℂ) (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ)
    (a b : ℕ) : Integrable (fun z : ℂ => z ^ a * starRingEnd ℂ z ^ b) μ := by
  refine (hμ (a + b)).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp [pow_add]

/-- The integral of the Taylor polynomial. -/
private lemma Cmp_int_tay (μ : Measure ℂ) (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ)
    (n : ℕ) (G : ℂ → ℂ) :
    Integrable (Cmp_tay n G) μ ∧ ∫ z, Cmp_tay n G z ∂μ =
      ∑ x ∈ Cmp_S n, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        ∫ z, z ^ x.1 * starRingEnd ℂ z ^ x.2 ∂μ := by
  have hi : ∀ x ∈ Cmp_S n, Integrable (fun z : ℂ => wirt x.1 x.2 G 0 /
      ((x.1.factorial * x.2.factorial : ℕ) : ℂ) * (z ^ x.1 * starRingEnd ℂ z ^ x.2)) μ :=
    fun x _ => (Cmp_int_mono μ hμ x.1 x.2).const_mul _
  refine ⟨?_, ?_⟩
  · unfold Cmp_tay
    exact integrable_finsetSum _ hi
  · unfold Cmp_tay
    rw [integral_finsetSum _ hi]
    simp only [integral_const_mul]

/-! ### Operator norms and entries -/

/-- `‖Aᴴ‖ = ‖A‖`. -/
private lemma Cmp_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- `‖A x‖ ≤ ‖A‖ ‖x‖` in the Euclidean norm. -/
private lemma Cmp_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℂ) : ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ opNorm A * ‖WithLp.toLp 2 x‖ := by
  unfold opNorm
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 x)
  rwa [Matrix.toEuclideanCLM_toLp] at h

/-- A diagonal matrix with entries of modulus `≤ 1` has operator norm `≤ 1`. -/
private lemma Cmp_opNorm_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ)
    (hd : ∀ k, ‖d k‖ ≤ 1) : opNorm (Matrix.diagonal d) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hx, Matrix.toEuclideanCLM_toLp, one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  simp only [Matrix.mulVec_diagonal, norm_mul]
  have h0 : 0 ≤ ‖x.ofLp k‖ := norm_nonneg _
  have h1 : ‖d k‖ * ‖x.ofLp k‖ ≤ ‖x.ofLp k‖ := by
    have := mul_le_mul_of_nonneg_right (hd k) h0
    linarith
  exact pow_le_pow_left₀ (by positivity) h1 2

/-- The resolvent bound `‖G(ξ)‖ ≤ |Im ξ|⁻¹` on both half planes. -/
private lemma Cmp_opNorm_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0) : opNorm (res X ξ) ≤ |ξ.im|⁻¹ := by
  rcases lt_or_gt_of_ne hξ with h | h
  · have h' : 0 < (star ξ).im := by simpa using h
    have e : res X ξ = (res X (star ξ))ᴴ := by
      have := res_conj X hX (star ξ) h'
      rwa [show starRingEnd ℂ (star ξ) = ξ from star_star ξ] at this
    rw [e, Cmp_opNorm_conjTranspose]
    have := opNorm_res_le X hX (star ξ) h'
    have e2 : (star ξ).im = |ξ.im| := by simp [abs_of_neg h]
    rwa [e2] at this
  · have := opNorm_res_le X hX ξ h
    rwa [abs_of_pos h]

/-- The entry `(k, m)` read with basis vectors. -/
private lemma Cmp_single_form {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (k m : ι) : star (Pi.single k (1 : ℂ)) ⬝ᵥ (A *ᵥ Pi.single m 1) = A k m := by
  simp [Matrix.mulVec_single, dotProduct, Pi.single_apply, apply_ite (starRingEnd ℂ)]

/-- A basis vector has norm `1`. -/
private lemma Cmp_single_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    ∑ r, ‖(Pi.single k (1 : ℂ) : ι → ℂ) r‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Ward's identity (2.32) [eq_Ward] on both half planes, as a bound: the squared norms of the
row and the column `k` of `G(ξ)` are at most `Γ/|Im ξ|` when `|G(ξ)_{kk}|, |G(ξ̄)_{kk}| ≤ Γ`. -/
private lemma Cmp_ward {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0) (k : ι) (Γ : ℝ)
    (h1 : ‖res X ξ k k‖ ≤ Γ) (h2 : ‖res X (star ξ) k k‖ ≤ Γ) :
    ∑ s, ‖res X ξ k s‖ ^ 2 ≤ Γ / |ξ.im| ∧ ∑ s, ‖res X ξ s k‖ ^ 2 ≤ Γ / |ξ.im| := by
  have hpos : 0 < |ξ.im| := abs_pos.mpr hξ
  rcases lt_or_gt_of_ne hξ with h | h
  · have h' : 0 < (star ξ).im := by simpa using h
    have e : res X ξ = (res X (star ξ))ᴴ := by
      have := res_conj X hX (star ξ) h'
      rwa [show starRingEnd ℂ (star ξ) = ξ from star_star ξ] at this
    have e2 : (star ξ).im = |ξ.im| := by simp [abs_of_neg h]
    obtain ⟨w1, w2⟩ := ward_diag X hX (star ξ) h' k
    have hb : (res X (star ξ) k k).im / (star ξ).im ≤ Γ / |ξ.im| := by
      rw [e2]
      exact div_le_div_of_nonneg_right ((Complex.im_le_norm _).trans h2) hpos.le
    have r1 : ∀ s, ‖res X ξ k s‖ = ‖res X (star ξ) s k‖ := fun s => by
      rw [e, Matrix.conjTranspose_apply, norm_star]
    have r2 : ∀ s, ‖res X ξ s k‖ = ‖res X (star ξ) k s‖ := fun s => by
      rw [e, Matrix.conjTranspose_apply, norm_star]
    simp only [r1, r2]
    exact ⟨w1 ▸ hb, w2 ▸ hb⟩
  · obtain ⟨w1, w2⟩ := ward_diag X hX ξ h k
    have hb : (res X ξ k k).im / ξ.im ≤ Γ / |ξ.im| := by
      rw [abs_of_pos h]
      exact div_le_div_of_nonneg_right ((Complex.im_le_norm _).trans h1) h.le
    exact ⟨w2 ▸ hb, w1 ▸ hb⟩

/-- `|Σ_s r_s (A c)_s| ≤ ‖r‖ ‖A‖ ‖c‖`. -/
private lemma Cmp_bilin {ι : Type*} [Fintype ι] [DecidableEq ι] (r c : ι → ℂ)
    (A : Matrix ι ι ℂ) :
    ‖∑ s, r s * (A *ᵥ c) s‖ ≤
      Real.sqrt (∑ s, ‖r s‖ ^ 2) * opNorm A * Real.sqrt (∑ s, ‖c s‖ ^ 2) := by
  have h1 : ‖∑ s, r s * (A *ᵥ c) s‖ ≤ ∑ s, ‖r s‖ * ‖(A *ᵥ c) s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_mul _ _))
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun s => ‖r s‖)
    (fun s => ‖(A *ᵥ c) s‖)
  have h3 : Real.sqrt (∑ s, ‖(A *ᵥ c) s‖ ^ 2) ≤ opNorm A * Real.sqrt (∑ s, ‖c s‖ ^ 2) := by
    have := Cmp_mulVec_le A c
    rwa [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at this
  have h4 : 0 ≤ Real.sqrt (∑ s, ‖r s‖ ^ 2) := Real.sqrt_nonneg _
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ Real.sqrt (∑ s, ‖r s‖ ^ 2) * (opNorm A * Real.sqrt (∑ s, ‖c s‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by ring

/-! ### Chains along a Hermitian slice -/

/-- The factor conditions on the chains of the loop `L_{ab}` of (3.1) [def_ML]: `B` diagonal with
entries of modulus `≤ 1`, `Λ` Hermitian, `ξ ∈ {z, z̄}`. -/
private def Cmp_fac {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (f : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ) : Prop :=
  (∃ d : Idx D N → ℂ, f.1 = Matrix.diagonal d ∧ ∀ k, ‖d k‖ ≤ 1) ∧ f.2.1 = Λ ∧
    (f.2.2 = z ∨ f.2.2 = star z)

/-- Entry bounds `|G(z)_{km}|, |G(z̄)_{km}| ≤ Γ` for the array `h`. -/
private def Cmp_EB {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (Γ : ℝ)
    (h : Idx D N → Idx D N → ℂ) : Prop :=
  ∀ k m, ‖res (Matrix.of h + Λ) z k m‖ ≤ Γ ∧ ‖res (Matrix.of h + Λ) (star z) k m‖ ≤ Γ

/-- The entry bounds hold at `ξ` and `ξ̄` for every `ξ ∈ {z, z̄}`. -/
private lemma Cmp_EB_of {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {Γ : ℝ}
    {h : Idx D N → Idx D N → ℂ} (hE : Cmp_EB Λ z Γ h) {ξ : ℂ} (hξ : ξ = z ∨ ξ = star z)
    (k m : Idx D N) :
    ‖res (Matrix.of h + Λ) ξ k m‖ ≤ Γ ∧ ‖res (Matrix.of h + Λ) (star ξ) k m‖ ≤ Γ := by
  rcases hξ with rfl | rfl
  · exact hE k m
  · rw [star_star]; exact ⟨(hE k m).2, (hE k m).1⟩

/-- A chain of factors as in `Cmp_fac` has operator norm `≤ |Im z|^{-p}`. -/
private lemma Cmp_opNorm_chain {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ l, Cmp_fac Λ z f) → opNorm (chainB h l) ≤ (|z.im|⁻¹) ^ l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [chainB, List.map_nil, List.prod_nil, List.length_nil, pow_zero]
    unfold opNorm
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  | cons f t ih =>
    intro hf
    obtain ⟨⟨d, hd1, hd2⟩, hΛf, hξ⟩ := hf f (by simp)
    have ht := ih fun g hg => hf g (by simp [hg])
    have hc : chainB h (f :: t) = (f.1 * res (Matrix.of h + f.2.1) f.2.2) * chainB h t := by
      simp [chainB]
    have hξim : f.2.2.im ≠ 0 ∧ |f.2.2.im| = |z.im| := by
      rcases hξ with e | e <;> rw [e] <;> simp [hz]
    have hB : opNorm f.1 ≤ 1 := hd1 ▸ Cmp_opNorm_diag d hd2
    have hG : opNorm (res (Matrix.of h + f.2.1) f.2.2) ≤ |z.im|⁻¹ := by
      have := Cmp_opNorm_res (Matrix.of h + f.2.1) (hΛf ▸ hh.add hΛ) f.2.2 hξim.1
      rwa [hξim.2] at this
    rw [hc, List.length_cons, pow_succ']
    have hn0 : 0 ≤ opNorm (res (Matrix.of h + f.2.1) f.2.2) := norm_nonneg _
    have hn1 : 0 ≤ opNorm (chainB h t) := norm_nonneg _
    calc opNorm (f.1 * res (Matrix.of h + f.2.1) f.2.2 * chainB h t)
        ≤ opNorm (f.1 * res (Matrix.of h + f.2.1) f.2.2) * opNorm (chainB h t) :=
          opNorm_mul_le _ _
      _ ≤ (opNorm f.1 * opNorm (res (Matrix.of h + f.2.1) f.2.2)) * opNorm (chainB h t) :=
          mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) hn1
      _ ≤ (1 * |z.im|⁻¹) * (|z.im|⁻¹) ^ t.length := by
          gcongr
      _ = _ := by ring

/-- The good chain bound: if `|G(ξ)_{km}| ≤ Γ` for `ξ ∈ {z, z̄}`, a chain of `p ≥ 1` factors as
in `Cmp_fac` has entries `≤ Γ |Im z|^{-(p-1)}` (Ward's identity (2.32) [eq_Ward] at both ends). -/
private lemma Cmp_chain_good {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (Γ : ℝ) (hE : Cmp_EB Λ z Γ h)
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (hl : 1 ≤ l.length) (hf : ∀ f ∈ l, Cmp_fac Λ z f) (k m : Idx D N) :
    ‖chainB h l k m‖ ≤ Γ * (|z.im|⁻¹) ^ (l.length - 1) := by
  obtain ⟨f, t, rfl⟩ : ∃ f t, l = f :: t := List.exists_cons_of_length_pos hl
  obtain ⟨⟨d, hd1, hd2⟩, hΛf, hξ⟩ := hf f (by simp)
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  set G := res (Matrix.of h + f.2.1) f.2.2 with hGdef
  have hXf : (Matrix.of h + f.2.1).IsHermitian := hΛf ▸ hh.add hΛ
  have hξim : f.2.2.im ≠ 0 ∧ |f.2.2.im| = |z.im| := by
    rcases hξ with e | e <;> rw [e] <;> simp [hz]
  have hEf : ∀ k m, ‖G k m‖ ≤ Γ ∧ ‖res (Matrix.of h + f.2.1) (star f.2.2) k m‖ ≤ Γ := by
    intro k m
    rw [hGdef, hΛf]
    exact Cmp_EB_of hE hξ k m
  have hrow : ∀ s, (f.1 * G) k s = d k * G k s := by
    intro s; rw [hd1, Matrix.diagonal_mul]
  rcases List.eq_nil_or_concat t with rfl | ⟨t', g, rfl⟩
  · have hc : chainB h [f] k m = d k * G k m := by
      rw [← hrow m]; simp [chainB, hGdef]
    rw [hc, norm_mul]
    simp only [List.length_singleton, Nat.sub_self, pow_zero, mul_one]
    calc ‖d k‖ * ‖G k m‖ ≤ 1 * Γ :=
          mul_le_mul (hd2 k) (hEf k m).1 (norm_nonneg _) zero_le_one
      _ = Γ := one_mul Γ
  · rw [List.concat_eq_append] at hf hl ⊢
    obtain ⟨⟨d', hd1', hd2'⟩, hΛg, hξg⟩ := hf g (by simp)
    have hξg' : g.2.2.im ≠ 0 ∧ |g.2.2.im| = |z.im| := by
      rcases hξg with e | e <;> rw [e] <;> simp [hz]
    set G' := res (Matrix.of h + g.2.1) g.2.2 with hG'def
    have hEg : ∀ k m, ‖G' k m‖ ≤ Γ ∧ ‖res (Matrix.of h + g.2.1) (star g.2.2) k m‖ ≤ Γ := by
      intro k m
      rw [hG'def, hΛg]
      exact Cmp_EB_of hE hξg k m
    set Mid := chainB h t' * g.1 with hMid
    have hc : chainB h (f :: (t' ++ [g])) = (f.1 * G) * (Mid * G') := by
      simp [chainB, hGdef, hG'def, hMid, List.prod_append, Matrix.mul_assoc]
    have hentry : chainB h (f :: (t' ++ [g])) k m =
        ∑ s, (d k * G k s) * (Mid *ᵥ fun u => G' u m) s := by
      rw [hc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hrow s, Matrix.mul_apply]
      rfl
    have hfac : ∀ f' ∈ t', Cmp_fac Λ z f' := fun f' hf' => hf f' (by simp [hf'])
    have hMidn : opNorm Mid ≤ (|z.im|⁻¹) ^ t'.length := by
      have h1 := Cmp_opNorm_chain Λ hΛ z hz h hh t' hfac
      have h2 : opNorm g.1 ≤ 1 := hd1' ▸ Cmp_opNorm_diag d' hd2'
      calc opNorm Mid ≤ opNorm (chainB h t') * opNorm g.1 := opNorm_mul_le _ _
        _ ≤ (|z.im|⁻¹) ^ t'.length * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    have hr : ∑ s, ‖d k * G k s‖ ^ 2 ≤ Γ / |z.im| := by
      have hw := (Cmp_ward (Matrix.of h + f.2.1) hXf f.2.2 hξim.1 k Γ (hEf k k).1
        (hEf k k).2).1
      rw [hξim.2] at hw
      refine le_trans (Finset.sum_le_sum fun s _ => ?_) hw
      rw [norm_mul]
      have : ‖d k‖ * ‖G k s‖ ≤ ‖G k s‖ := by
        have := mul_le_mul_of_nonneg_right (hd2 k) (norm_nonneg (G k s)); linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have hcol : ∑ u, ‖G' u m‖ ^ 2 ≤ Γ / |z.im| := by
      have hXg : (Matrix.of h + g.2.1).IsHermitian := hΛg ▸ hh.add hΛ
      have hw := (Cmp_ward (Matrix.of h + g.2.1) hXg g.2.2 hξg'.1 m Γ (hEg m m).1
        (hEg m m).2).2
      rwa [hξg'.2] at hw
    have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hEf k k).1
    rw [hentry]
    have hb := Cmp_bilin (fun s => d k * G k s) (fun u => G' u m) Mid
    have hs1 : Real.sqrt (∑ s, ‖d k * G k s‖ ^ 2) ≤ Real.sqrt (Γ / |z.im|) :=
      Real.sqrt_le_sqrt hr
    have hs2 : Real.sqrt (∑ u, ‖G' u m‖ ^ 2) ≤ Real.sqrt (Γ / |z.im|) := Real.sqrt_le_sqrt hcol
    have hsq : Real.sqrt (Γ / |z.im|) * Real.sqrt (Γ / |z.im|) = Γ / |z.im| :=
      Real.mul_self_sqrt (div_nonneg hΓ0 hpos.le)
    have hlen : (f :: (t' ++ [g])).length - 1 = t'.length + 1 := by simp
    rw [hlen]
    calc _ ≤ _ := hb
      _ ≤ Real.sqrt (Γ / |z.im|) * (|z.im|⁻¹) ^ t'.length * Real.sqrt (Γ / |z.im|) := by
          have : 0 ≤ opNorm Mid := norm_nonneg _
          gcongr
      _ = Γ * (|z.im|⁻¹) ^ (t'.length + 1) := by
          rw [mul_comm (Real.sqrt _ * _), ← mul_assoc, mul_comm (Real.sqrt _) (Real.sqrt _),
            hsq, pow_succ]
          field_simp

/-! ### The one-entry slice of the loop `L_{ab}` -/

/-- A Hermitian array stays Hermitian after the one-entry substitution. -/
private lemma Cmp_setEntry_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have e : symArr (setEntry h i j w) = setEntry h i j w := by
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [← e]
  exact symArr_isHermitian _

/-- `|G(ξ̄)_{km}| = |G(ξ)_{mk}|` for Hermitian `X`, `Im ξ > 0`. -/
private lemma Cmp_res_star_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ξ : ℂ) (hξ : 0 < ξ.im) (k m : ι) :
    ‖res X (star ξ) k m‖ = ‖res X ξ m k‖ := by
  rw [show star ξ = starRingEnd ℂ ξ from rfl, res_conj X hX ξ hξ, Matrix.conjTranspose_apply,
    norm_star]

/-- One-entry stability of the entries at `Im ξ > 0` (`res_setEntry_le` with basis vectors). -/
private lemma Cmp_entry_setEntry_pos {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (ξ : ℂ) (hξ : 0 < ξ.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) (M Γ : ℝ) (hw : ‖w‖ ≤ M)
    (hij : ‖h i j‖ ≤ M) (hMΓ : 4 * M * Γ ≤ 1 / 2)
    (hE : ∀ k m, ‖res (Matrix.of h + Λ) ξ k m‖ ≤ Γ) (k m : Idx D N) :
    ‖res (Matrix.of (setEntry h i j w) + Λ) ξ k m‖ ≤ 2 * Γ := by
  have hG : ∀ x ∈ ({Pi.single k 1, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
      ∀ y ∈ ({Pi.single m 1, Pi.single i 1, Pi.single j 1} : Set (Idx D N → ℂ)),
        ‖star x ⬝ᵥ (res (Matrix.of h + Λ) ξ *ᵥ y)‖ ≤ Γ := by
    intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rw [Cmp_single_form] <;> exact hE _ _
  have := res_setEntry_le D N h Λ hh hΛ ξ hξ i j w M Γ hw hij hMΓ _ _ hG (Pi.single k 1)
    (by simp) (Pi.single m 1) (by simp)
  rwa [Cmp_single_form] at this

/-- One-entry stability of the entry bounds `Cmp_EB` on both half planes. -/
private lemma Cmp_EB_setEntry {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) (M Γ : ℝ) (hw : ‖w‖ ≤ M)
    (hij : ‖h i j‖ ≤ M) (hMΓ : 4 * M * Γ ≤ 1 / 2) (hE : Cmp_EB Λ z Γ h) :
    Cmp_EB Λ z (2 * Γ) (setEntry h i j w) := by
  have hX' := (Cmp_setEntry_herm h hh i j w).add hΛ
  have hX := hh.add hΛ
  intro k m
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hs : 0 < (star z).im := by simpa using hneg
    have hE' : ∀ k m, ‖res (Matrix.of h + Λ) (star z) k m‖ ≤ Γ := fun k m => (hE k m).2
    have h2 := fun k m => Cmp_entry_setEntry_pos Λ hΛ (star z) hs h hh i j w M Γ hw hij hMΓ hE' k m
    refine ⟨?_, h2 k m⟩
    have := Cmp_res_star_entry _ hX' (star z) hs k m
    rw [star_star] at this
    rw [this]
    exact h2 m k
  · have hE' : ∀ k m, ‖res (Matrix.of h + Λ) z k m‖ ≤ Γ := fun k m => (hE k m).1
    have h2 := fun k m => Cmp_entry_setEntry_pos Λ hΛ z hpos h hh i j w M Γ hw hij hMΓ hE' k m
    refine ⟨h2 k m, ?_⟩
    rw [Cmp_res_star_entry _ hX' z hpos k m]
    exact h2 m k

/-- The slice `x ↦ setEntry h i j x` is smooth. -/
private lemma Cmp_contDiff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun x : ℂ => setEntry h i j x) := by
  refine contDiff_pi.mpr fun p => contDiff_pi.mpr fun m => ?_
  by_cases hij : i = j
  · subst hij
    by_cases hpm : p = i ∧ m = i
    · have e : (fun x : ℂ => setEntry h i i x p m) = fun x => ((x.re : ℝ) : ℂ) := by
        funext x; simp [setEntry, hpm]
      rw [e]
      exact (Complex.ofRealCLM.comp Complex.reCLM).contDiff
    · have e : (fun x : ℂ => setEntry h i i x p m) = fun _ => h p m := by
        funext x; simp [setEntry, hpm]
      rw [e]
      exact contDiff_const
  · by_cases h1 : p = i ∧ m = j
    · have e : (fun x : ℂ => setEntry h i j x p m) = fun x => x := by
        funext x; simp [setEntry, hij, h1]
      rw [e]
      exact contDiff_id
    · by_cases h2 : p = j ∧ m = i
      · have e : (fun x : ℂ => setEntry h i j x p m) = fun x => starRingEnd ℂ x := by
          funext x; simp [setEntry, hij, h2]
        rw [e]
        exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff
      · have e : (fun x : ℂ => setEntry h i j x p m) = fun _ => h p m := by
          funext x; simp [setEntry, hij, h1, h2]
        rw [e]
        exact contDiff_const

/-- Every entry of a chain along a Hermitian slice is smooth. -/
private lemma Cmp_contDiff_chain {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (n : ℕ) :
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) → ∀ k m,
        ContDiff ℝ n (fun x : ℂ => chainB (setEntry h i j x) l k m) := by
  intro l
  induction l with
  | nil =>
    intro _ k m
    simp only [chainB, List.map_nil, List.prod_nil]
    exact contDiff_const
  | cons f t ih =>
    intro hl k m
    have ht := ih fun g hg => hl g (by simp [hg])
    obtain ⟨hΛ, hξ⟩ := hl f (by simp)
    have hG : ∀ s q, ContDiff ℝ n
        (fun x : ℂ => res (Matrix.of (setEntry h i j x) + f.2.1) f.2.2 s q) := by
      intro s q
      have e : (fun x : ℂ => res (Matrix.of (setEntry h i j x) + f.2.1) f.2.2 s q) =
          (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + f.2.1) f.2.2 s q) ∘
            fun x : ℂ => setEntry h i j x := by
        funext x
        simp only [Function.comp]
        rw [symArr_setEntry, symArr_of_isHermitian h hh]
      rw [e]
      exact (contDiff_res_symArr f.2.1 hΛ f.2.2 hξ s q n).comp (Cmp_contDiff_slice h i j n)
    have e : (fun x : ℂ => chainB (setEntry h i j x) (f :: t) k m) = fun x =>
        ∑ q, (∑ s, f.1 k s * res (Matrix.of (setEntry h i j x) + f.2.1) f.2.2 s q) *
          chainB (setEntry h i j x) t q m := by
      funext x
      simp only [chainB, List.map_cons, List.prod_cons, Matrix.mul_apply]
    rw [e]
    exact ContDiff.sum fun q _ => (ContDiff.sum fun s _ => contDiff_const.mul (hG s q)).mul
      (ht q m)

/-- The chain `E_b G(z₁) E_a G(z₂)` whose normalized trace times `D` is `L_{ab}` of (3.1)
[def_ML]. -/
private def Cmp_l0 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a b : Fin D) :
    List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ) :=
  [(Ea D N b, Λ, z₁), (Ea D N a, Λ, z₂)]

/-- `L_{ab} = D ⟨E_b G(z₁) E_a G(z₂)⟩`, (3.1) [def_ML]. -/
private lemma Cmp_Lmat_eq {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (z₁ z₂ : ℂ) (a b : Fin D) :
    Lmat Λ h z₁ z₂ a b = (D : ℂ) * ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b)) := by
  have hc : chainB h (Cmp_l0 Λ z₁ z₂ a b) = Ea D N b * (res (Matrix.of h + Λ) z₁ *
      (Ea D N a * res (Matrix.of h + Λ) z₂)) := by
    simp only [Cmp_l0, chainB, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Matrix.mul_assoc]
  have ht : (res (Matrix.of h + Λ) z₁ * Ea D N a * res (Matrix.of h + Λ) z₂ * Ea D N b).trace =
      (Ea D N b * (res (Matrix.of h + Λ) z₁ * (Ea D N a * res (Matrix.of h + Λ) z₂))).trace := by
    rw [Matrix.trace_mul_comm (Ea D N b)]
    simp only [Matrix.mul_assoc]
  rw [hc]
  unfold Lmat ntr
  rw [ht]

/-- The factors of the chains used with `loopB_wirt_le` for `Cmp_l0` satisfy `Cmp_fac`. -/
private lemma Cmp_l0_fac {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z z₁ z₂ : ℂ)
    (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z) (a b : Fin D)
    (f : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ)
    (hf : f ∈ Cmp_l0 Λ z₁ z₂ a b ∨ (f.1 = 1 ∧ ∃ g ∈ Cmp_l0 Λ z₁ z₂ a b, g.2 = f.2)) :
    Cmp_fac Λ z f := by
  have hEa : ∀ c : Fin D, ∃ d : Idx D N → ℂ, Ea D N c = Matrix.diagonal d ∧ ∀ k, ‖d k‖ ≤ 1 :=
    fun c => ⟨_, rfl, fun k => by split_ifs <;> simp⟩
  have h1 : ∃ d : Idx D N → ℂ, (1 : Matrix (Idx D N) (Idx D N) ℂ) = Matrix.diagonal d ∧
      ∀ k, ‖d k‖ ≤ 1 := ⟨fun _ => 1, Matrix.diagonal_one.symm, fun k => by simp⟩
  rcases hf with hf | ⟨hf1, g, hg, hg2⟩
  · simp only [Cmp_l0, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨hEa b, rfl, hz₁⟩
    · exact ⟨hEa a, rfl, hz₂⟩
  · simp only [Cmp_l0, List.mem_cons, List.not_mem_nil, or_false] at hg
    refine ⟨hf1 ▸ h1, ?_, ?_⟩
    · rcases hg with rfl | rfl <;> rw [← hg2]
    · rcases hg with rfl | rfl <;> rw [← hg2] <;> assumption

/-- The deterministic derivative bound of the slice of the loop: for every point,
`|∂^{(a,b)} ⟨E_b G₁ E_a G₂⟩| ≤ (2+n)^n (DN)⁻¹ |Im z|^{-(n+2)}`, `n = a + b ≥ 1`. -/
private lemma Cmp_wirt_det {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z z₁ z₂ : ℂ) (hz : z.im ≠ 0) (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (w : ℂ) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ‖wirt p q (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) w‖ ≤
      ((2 + p + q : ℕ) : ℝ) ^ (p + q) * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ (p + q + 2) := by
  have hl : ∀ f ∈ Cmp_l0 Λ z₁ z₂ a b, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
    intro f hf
    obtain ⟨-, h2, h3⟩ := Cmp_l0_fac Λ z z₁ z₂ hz₁ hz₂ a b f (Or.inl hf)
    refine ⟨h2 ▸ hΛ, ?_⟩
    rcases h3 with e | e <;> rw [e] <;> simpa using hz
  set Γ : ℕ → ℝ := fun r => (|z.im|⁻¹) ^ r with hΓdef
  have hΓ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Γ a * Γ b ≤ Γ 1 * Γ (a + b - 1) := by
    intro a b ha hb
    simp only [hΓdef, ← pow_add]
    exact le_of_eq (congrArg _ (by omega))
  have hX : Pi.single i (1 : ℂ) ∈ Set.range (fun k : Idx D N => (Pi.single k (1 : ℂ))) ∧
      Pi.single j (1 : ℂ) ∈ Set.range (fun k : Idx D N => (Pi.single k (1 : ℂ))) :=
    ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
  have hhw := Cmp_setEntry_herm h hh i j w
  have hb := loopB_wirt_le (Cmp_l0 Λ z₁ z₂ a b) (by simp [Cmp_l0]) hl h hh i j w Γ hΓ _ hX
    (fun l' hl1 _ hl' x hx y hy => by
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      rw [Cmp_single_form]
      exact (norm_apply_le_opNorm _ k m).trans (Cmp_opNorm_chain Λ hΛ z hz _ hhw l'
        fun f hf => Cmp_l0_fac Λ z z₁ z₂ hz₁ hz₂ a b f (hl' f hf))) p q hpq
  have hlen : (Cmp_l0 Λ z₁ z₂ a b).length = 2 := rfl
  rw [hlen] at hb
  have e : Γ 1 ^ (p + q - 1) * Γ (2 + 1) = (|z.im|⁻¹) ^ (p + q + 2) := by
    simp only [hΓdef, ← pow_mul, ← pow_add, one_mul]
    congr 1
    omega
  calc _ ≤ _ := hb
    _ = ((2 + p + q : ℕ) : ℝ) ^ (p + q) * ((D : ℝ) * N)⁻¹ * (Γ 1 ^ (p + q - 1) * Γ (2 + 1)) := by
        ring
    _ = _ := by rw [e]

/-- The good derivative bound of the slice of the loop: if `|G(ξ)_{km}| ≤ Γ'` at the point for
`ξ ∈ {z, z̄}`, then `|∂^{(a,b)} ⟨E_b G₁ E_a G₂⟩| ≤ (2+n)^n (DN)⁻¹ Γ'^n |Im z|^{-2}`,
`n = a + b ≥ 1` (the count of (3.38) [eq:cpmparison]). -/
private lemma Cmp_wirt_good {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z z₁ z₂ : ℂ) (hz : z.im ≠ 0) (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (w : ℂ) (Γ' : ℝ) (hE : Cmp_EB Λ z Γ' (setEntry h i j w)) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ‖wirt p q (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) w‖ ≤
      ((2 + p + q : ℕ) : ℝ) ^ (p + q) * ((D : ℝ) * N)⁻¹ * Γ' ^ (p + q) * (|z.im|⁻¹) ^ 2 := by
  have hl : ∀ f ∈ Cmp_l0 Λ z₁ z₂ a b, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
    intro f hf
    obtain ⟨-, h2, h3⟩ := Cmp_l0_fac Λ z z₁ z₂ hz₁ hz₂ a b f (Or.inl hf)
    refine ⟨h2 ▸ hΛ, ?_⟩
    rcases h3 with e | e <;> rw [e] <;> simpa using hz
  set Γ : ℕ → ℝ := fun r => Γ' * (|z.im|⁻¹) ^ (r - 1) with hΓdef
  have hΓ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Γ a * Γ b ≤ Γ 1 * Γ (a + b - 1) := by
    intro a b ha hb
    simp only [hΓdef, Nat.sub_self, pow_zero, mul_one]
    apply le_of_eq
    rw [mul_mul_mul_comm, ← pow_add, show a - 1 + (b - 1) = a + b - 1 - 1 by omega]
    ring
  have hX : Pi.single i (1 : ℂ) ∈ Set.range (fun k : Idx D N => (Pi.single k (1 : ℂ))) ∧
      Pi.single j (1 : ℂ) ∈ Set.range (fun k : Idx D N => (Pi.single k (1 : ℂ))) :=
    ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
  have hhw := Cmp_setEntry_herm h hh i j w
  have hb := loopB_wirt_le (Cmp_l0 Λ z₁ z₂ a b) (by simp [Cmp_l0]) hl h hh i j w Γ hΓ _ hX
    (fun l' hl1 _ hl' x hx y hy => by
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      rw [Cmp_single_form]
      exact Cmp_chain_good Λ hΛ z hz _ hhw Γ' hE l' hl1
        (fun f hf => Cmp_l0_fac Λ z z₁ z₂ hz₁ hz₂ a b f (hl' f hf)) k m) p q hpq
  have hlen : (Cmp_l0 Λ z₁ z₂ a b).length = 2 := rfl
  rw [hlen] at hb
  have e : Γ 1 ^ (p + q - 1) * Γ (2 + 1) = Γ' ^ (p + q) * (|z.im|⁻¹) ^ 2 := by
    simp only [hΓdef, Nat.sub_self, pow_zero, mul_one, show 2 + 1 - 1 = 2 from rfl]
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hpq]
  calc _ ≤ _ := hb
    _ = ((2 + p + q : ℕ) : ℝ) ^ (p + q) * ((D : ℝ) * N)⁻¹ * (Γ 1 ^ (p + q - 1) * Γ (2 + 1)) := by
        ring
    _ = _ := by rw [e]; ring

/-! ### The Taylor comparison for one entry -/

/-- The comparison of `E G(w)` under two laws matching to order three and to `ε₄` at order four:
the fourth-order term and the fifth-order remainder, split at `|w| = M`. -/
private lemma Cmp_taylor_cmp (G : ℂ → ℂ) (hG : ContDiff ℝ 5 G) (ρ ρ' : Measure ℂ)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ']
    (hρ : ∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) ρ)
    (hρ' : ∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) ρ') (ε₄ : ℝ)
    (hm3 : ∀ a b : ℕ, a + b ≤ 3 → mixMom ρ a b = mixMom ρ' a b)
    (hm4 : ∀ a b : ℕ, a + b = 4 → ‖mixMom ρ a b - mixMom ρ' a b‖ ≤ ε₄)
    (S4 S5 S5' M : ℝ) (hM : 0 < M) (k : ℕ)
    (h4 : ∀ a b : ℕ, a + b = 4 → ‖wirt a b G 0‖ ≤ S4)
    (h5 : ∀ a b : ℕ, a + b = 5 → ∀ w, ‖wirt a b G w‖ ≤ S5)
    (h5' : ∀ a b : ℕ, a + b = 5 → ∀ w, ‖w‖ ≤ M → ‖wirt a b G w‖ ≤ S5') :
    ‖(∫ x, G x ∂ρ) - ∫ x, G x ∂ρ'‖ ≤ 25 * S4 * ε₄ +
      32 * S5' * ((∫ x, ‖x‖ ^ 5 ∂ρ) + ∫ x, ‖x‖ ^ 5 ∂ρ') +
      32 * S5 * ((∫ x, ‖x‖ ^ (5 + k) ∂ρ) + ∫ x, ‖x‖ ^ (5 + k) ∂ρ') / M ^ k := by
  set R : ℂ → ℂ := fun x => G x - Cmp_tay 5 G x with hRdef
  have hS5 : 0 ≤ S5 := (norm_nonneg _).trans (h5 5 0 rfl 0)
  have hS5' : 0 ≤ S5' := (norm_nonneg _).trans (h5' 5 0 rfl 0 (by simp [hM.le]))
  have hS4 : 0 ≤ S4 := (norm_nonneg _).trans (h4 4 0 rfl)
  have hε : 0 ≤ ε₄ := (norm_nonneg _).trans (hm4 4 0 rfl)
  have hRd : ∀ x, ‖R x‖ ≤ 2 ^ 5 * S5 * ‖x‖ ^ 5 := fun x =>
    Cmp_taylor 5 hG (r := ‖x‖) (S := S5) (fun a b hab w _ => h5 a b hab w) x le_rfl
  have hRg : ∀ x, ‖x‖ ≤ M → ‖R x‖ ≤ 2 ^ 5 * S5' * ‖x‖ ^ 5 := fun x hx =>
    Cmp_taylor 5 hG (r := M) (S := S5') h5' x hx
  have hRc : Continuous R :=
    (hG.continuous).sub (Cmp_tay_continuous 5 G)
  -- the pointwise bound of the remainder
  have hRb : ∀ x, ‖R x‖ ≤ 32 * S5' * ‖x‖ ^ 5 + 32 * S5 * ‖x‖ ^ (5 + k) / M ^ k := by
    intro x
    have hMk : 0 < M ^ k := pow_pos hM k
    by_cases hx : ‖x‖ ≤ M
    · have := hRg x hx
      have : 0 ≤ 32 * S5 * ‖x‖ ^ (5 + k) / M ^ k := by positivity
      norm_num at *
      linarith
    · push Not at hx
      have h1 := hRd x
      have h2 : ‖x‖ ^ 5 ≤ ‖x‖ ^ (5 + k) / M ^ k := by
        rw [le_div_iff₀ hMk, pow_add]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le hx.le k) (by positivity)
      have : 0 ≤ 32 * S5' * ‖x‖ ^ 5 := by positivity
      have h3 : 32 * S5 * ‖x‖ ^ 5 ≤ 32 * S5 * (‖x‖ ^ (5 + k) / M ^ k) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      norm_num at h1
      calc ‖R x‖ ≤ 32 * S5 * ‖x‖ ^ 5 := h1
        _ ≤ 32 * S5 * (‖x‖ ^ (5 + k) / M ^ k) := h3
        _ ≤ _ := by rw [mul_div_assoc]; linarith
  have hRi : ∀ (μ : Measure ℂ), (∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) μ) →
      Integrable R μ := fun μ hμ =>
    ((hμ 5).const_mul (2 ^ 5 * S5)).mono' hRc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hRd x)
  have hBi : ∀ (μ : Measure ℂ), (∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) μ) →
      Integrable (fun x : ℂ => 32 * S5' * ‖x‖ ^ 5 + 32 * S5 * ‖x‖ ^ (5 + k) / M ^ k) μ :=
    fun μ hμ => ((hμ 5).const_mul _).add (((hμ (5 + k)).const_mul _).div_const _)
  have hRint : ∀ (μ : Measure ℂ), (∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) μ) →
      ‖∫ x, R x ∂μ‖ ≤ 32 * S5' * (∫ x, ‖x‖ ^ 5 ∂μ) +
        32 * S5 * (∫ x, ‖x‖ ^ (5 + k) ∂μ) / M ^ k := by
    intro μ hμ
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono (hRi μ hμ).norm (hBi μ hμ) hRb).trans (le_of_eq ?_)
    rw [integral_add ((hμ 5).const_mul _) (((hμ (5 + k)).const_mul _).div_const _),
      integral_const_mul, integral_div, integral_const_mul]
  -- the expansion of `E G`
  have hexp : ∀ (μ : Measure ℂ), (∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) μ) →
      ∫ x, G x ∂μ = (∑ x ∈ Cmp_S 5, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        mixMom μ x.1 x.2) + ∫ x, R x ∂μ := by
    intro μ hμ
    obtain ⟨hti, htv⟩ := Cmp_int_tay μ hμ 5 G
    have e : (fun x => G x) = fun x => Cmp_tay 5 G x + R x := by
      funext x; simp [hRdef]
    rw [e, integral_add hti (hRi μ hμ), htv]
    rfl
  rw [hexp ρ hρ, hexp ρ' hρ']
  have hsplit : ((∑ x ∈ Cmp_S 5, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        mixMom ρ x.1 x.2) + ∫ x, R x ∂ρ) -
      ((∑ x ∈ Cmp_S 5, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        mixMom ρ' x.1 x.2) + ∫ x, R x ∂ρ') =
      (∑ x ∈ Cmp_S 5, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        (mixMom ρ x.1 x.2 - mixMom ρ' x.1 x.2)) + ((∫ x, R x ∂ρ) - ∫ x, R x ∂ρ') := by
    rw [← sub_add_sub_comm, ← Finset.sum_sub_distrib]
    simp only [mul_sub]
  rw [hsplit]
  have hsum : ‖∑ x ∈ Cmp_S 5, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
      (mixMom ρ x.1 x.2 - mixMom ρ' x.1 x.2)‖ ≤ 25 * S4 * ε₄ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ x ∈ Cmp_S 5,
        ‖wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
          (mixMom ρ x.1 x.2 - mixMom ρ' x.1 x.2)‖ ≤ S4 * ε₄ := by
      intro x hx
      have hx' := Cmp_mem_S.1 hx
      by_cases h3 : x.1 + x.2 ≤ 3
      · rw [hm3 x.1 x.2 h3, sub_self, mul_zero, norm_zero]
        positivity
      · have h4' : x.1 + x.2 = 4 := by omega
        rw [norm_mul, norm_div]
        have hf : (1 : ℝ) ≤ ‖((x.1.factorial * x.2.factorial : ℕ) : ℂ)‖ := by
          rw [Complex.norm_natCast]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        have h1 : ‖wirt x.1 x.2 G 0‖ / ‖((x.1.factorial * x.2.factorial : ℕ) : ℂ)‖ ≤ S4 :=
          (div_le_self (norm_nonneg _) hf).trans (h4 x.1 x.2 h4')
        exact mul_le_mul h1 (hm4 x.1 x.2 h4') (norm_nonneg _) hS4
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Cmp_S 5).card : ℝ) ≤ 25 := by
      have : (Cmp_S 5).card ≤ 25 := by
        unfold Cmp_S
        refine (Finset.card_filter_le _ _).trans ?_
        simp
      exact_mod_cast this
    have : 0 ≤ S4 * ε₄ := mul_nonneg hS4 hε
    nlinarith
  have hR1 := hRint ρ hρ
  have hR2 := hRint ρ' hρ'
  calc _ ≤ ‖∑ x ∈ Cmp_S 5, wirt x.1 x.2 G 0 / ((x.1.factorial * x.2.factorial : ℕ) : ℂ) *
        (mixMom ρ x.1 x.2 - mixMom ρ' x.1 x.2)‖ + (‖∫ x, R x ∂ρ‖ + ‖∫ x, R x ∂ρ'‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ _ := by
        have e : 32 * S5 * ((∫ x, ‖x‖ ^ (5 + k) ∂ρ) + ∫ x, ‖x‖ ^ (5 + k) ∂ρ') / M ^ k =
            32 * S5 * (∫ x, ‖x‖ ^ (5 + k) ∂ρ) / M ^ k +
              32 * S5 * (∫ x, ‖x‖ ^ (5 + k) ∂ρ') / M ^ k := by ring
        rw [e]
        linarith

/-- The one-entry comparison for the loop `⟨E_b G₁ E_a G₂⟩` at a Hermitian base `h` with
`h_{ij} = 0`: the deterministic bound, and the good bound when `|G(ξ)_{km}| ≤ Γ₁` at `h`. -/
private lemma Cmp_step {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z z₁ z₂ : ℂ) (hz : z.im ≠ 0) (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (hij : h i j = 0) (ρ ρ' : Measure ℂ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ']
    (hρ : ∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) ρ)
    (hρ' : ∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) ρ') (ε₄ : ℝ)
    (hm3 : ∀ a b : ℕ, a + b ≤ 3 → mixMom ρ a b = mixMom ρ' a b)
    (hm4 : ∀ a b : ℕ, a + b = 4 → ‖mixMom ρ a b - mixMom ρ' a b‖ ≤ ε₄)
    (Γ₁ M : ℝ) (hM : 0 < M) (hMΓ : 4 * M * Γ₁ ≤ 1 / 2) (k : ℕ) :
    (‖(∫ x, ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b)) ∂ρ) -
        ∫ x, ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b)) ∂ρ'‖ ≤
      25 * (6 ^ 4 * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ 6) * ε₄ +
      32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ 7) *
        ((∫ x, ‖x‖ ^ 5 ∂ρ) + ∫ x, ‖x‖ ^ 5 ∂ρ') +
      32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ 7) *
        ((∫ x, ‖x‖ ^ (5 + k) ∂ρ) + ∫ x, ‖x‖ ^ (5 + k) ∂ρ') / M ^ k) ∧
    (Cmp_EB Λ z Γ₁ h →
      ‖(∫ x, ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b)) ∂ρ) -
          ∫ x, ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b)) ∂ρ'‖ ≤
        25 * (6 ^ 4 * ((D : ℝ) * N)⁻¹ * (2 * Γ₁) ^ 4 * (|z.im|⁻¹) ^ 2) * ε₄ +
        32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * (2 * Γ₁) ^ 5 * (|z.im|⁻¹) ^ 2) *
          ((∫ x, ‖x‖ ^ 5 ∂ρ) + ∫ x, ‖x‖ ^ 5 ∂ρ') +
        32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ 7) *
          ((∫ x, ‖x‖ ^ (5 + k) ∂ρ) + ∫ x, ‖x‖ ^ (5 + k) ∂ρ') / M ^ k) := by
  have hl : ∀ f ∈ Cmp_l0 Λ z₁ z₂ a b, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
    intro f hf
    obtain ⟨-, h2, h3⟩ := Cmp_l0_fac Λ z z₁ z₂ hz₁ hz₂ a b f (Or.inl hf)
    refine ⟨h2 ▸ hΛ, ?_⟩
    rcases h3 with e | e <;> rw [e] <;> simpa using hz
  have hG : ContDiff ℝ 5 (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) := by
    have e : (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) = fun x =>
        ((Fintype.card (Idx D N) : ℂ))⁻¹ *
          ∑ k, chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b) k k := by
      funext x; rfl
    rw [e]
    exact contDiff_const.mul (ContDiff.sum fun k _ =>
      Cmp_contDiff_chain h hh i j 5 _ hl k k)
  have hd : ∀ p q : ℕ, ∀ n : ℕ, p + q = n → 1 ≤ n → ∀ w,
      ‖wirt p q (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) w‖ ≤
        ((2 + n : ℕ) : ℝ) ^ n * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ (n + 2) := by
    intro p q n hn h1 w
    subst hn
    have := Cmp_wirt_det Λ hΛ z z₁ z₂ hz hz₁ hz₂ a b h hh i j w p q h1
    rwa [show 2 + p + q = 2 + (p + q) by ring] at this
  have h5 : ∀ p q : ℕ, p + q = 5 → ∀ w,
      ‖wirt p q (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) w‖ ≤
        7 ^ 5 * ((D : ℝ) * N)⁻¹ * (|z.im|⁻¹) ^ 7 := by
    intro p q hpq w
    have := hd p q 5 hpq (by norm_num) w
    norm_num at this ⊢
    exact this
  refine ⟨?_, fun hE => ?_⟩
  · refine Cmp_taylor_cmp _ hG ρ ρ' hρ hρ' ε₄ hm3 hm4 _ _ _ M hM k (fun p q hpq => ?_) h5
      (fun p q hpq w _ => h5 p q hpq w)
    have := hd p q 4 hpq (by norm_num) 0
    norm_num at this ⊢
    exact this
  · have hEw : ∀ w : ℂ, ‖w‖ ≤ M → Cmp_EB Λ z (2 * Γ₁) (setEntry h i j w) := fun w hw =>
      Cmp_EB_setEntry Λ hΛ z hz h hh i j w M Γ₁ hw (by rw [hij, norm_zero]; exact hM.le) hMΓ hE
    have hg : ∀ p q : ℕ, ∀ n : ℕ, p + q = n → 1 ≤ n → ∀ w : ℂ, ‖w‖ ≤ M →
        ‖wirt p q (fun x => ntr (chainB (setEntry h i j x) (Cmp_l0 Λ z₁ z₂ a b))) w‖ ≤
          ((2 + n : ℕ) : ℝ) ^ n * ((D : ℝ) * N)⁻¹ * (2 * Γ₁) ^ n * (|z.im|⁻¹) ^ 2 := by
      intro p q n hn h1 w hw
      subst hn
      have := Cmp_wirt_good Λ hΛ z z₁ z₂ hz hz₁ hz₂ a b h hh i j w (2 * Γ₁) (hEw w hw) p q h1
      rwa [show 2 + p + q = 2 + (p + q) by ring] at this
    refine Cmp_taylor_cmp _ hG ρ ρ' hρ hρ' ε₄ hm3 hm4 _ _ _ M hM k (fun p q hpq => ?_) h5
      (fun p q hpq w hw => ?_)
    · have := hg p q 4 hpq (by norm_num) 0 (by simp [hM.le])
      norm_num at this ⊢
      exact this
    · have := hg p q 5 hpq (by norm_num) w hw
      norm_num at this ⊢
      exact this

/-! ### The entry laws of `H_t`, (4.3) [eq:eq_in_law_H] -/

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma Cmp_measurable_wig (n : ℕ) (i j : Fin n) :
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

/-- Every entry of `blockH D N w` is a measurable function of `w`. -/
private lemma Cmp_measurable_blockH (D N : ℕ) (p q : Idx D N) :
    Measurable fun w : Fin D → Coords N => blockH D N w p q := by
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (Cmp_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
  · simp only [blockH, h, ↓reduceIte]
    exact measurable_const

/-- The array of coordinates `blockEmb D N w` is a measurable function of `w`. -/
private lemma Cmp_measurable_blockEmb (D N : ℕ) : Measurable (blockEmb D N) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun k => ?_
    exact measurable_const.mul ((measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))
  · refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun l => ?_
    by_cases h : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · simp only [h, ↓reduceIte]
      exact measurable_const.mul ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (measurable_snd.comp (measurable_pi_apply _))))
    · simp only [h, ↓reduceIte]
      exact measurable_const

/-- The map of the law `ouLaw` is measurable. -/
private lemma Cmp_measurable_phi0 (D N : ℕ) (t : ℝ) :
    Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2 := by
  have h1 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 :=
    ((Cmp_measurable_blockEmb D N).comp measurable_fst).const_smul (Real.exp (-t / 2))
  have h2 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.sqrt (1 - Real.exp (-t)) • p.2 :=
    measurable_snd.const_smul (Real.sqrt (1 - Real.exp (-t)))
  exact h1.add h2

/-- The array map of `ouMatLaw` is measurable. -/
private lemma Cmp_measurable_psi (D N : ℕ) :
    Measurable fun c : Coords (D * N) => Matrix.of.symm
      ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    Cmp_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)

/-- The entries of `H_t`: `e^{-t/2} (blockH w)_{pq} + √(1 - e^{-t}) (wig (DN) W)_{pq}`. -/
private def Cmp_Θ (D N : ℕ) (t : ℝ) (ω : (Fin D → Coords N) × Coords (D * N)) :
    Idx D N → Idx D N → ℂ := fun p q =>
  ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 p q +
    ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
      wig (D * N) ω.2 (finProdFinEquiv p) (finProdFinEquiv q)

/-- The law `ouMatLaw` is the image of `blockLaw ⊗ gueLaw (DN)` under `Cmp_Θ`. -/
private lemma Cmp_ouMatLaw_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) :
    ouMatLaw D N L t = ((blockLaw D N L).prod (gueLaw (D * N))).map (Cmp_Θ D N t) := by
  unfold ouMatLaw ouLaw
  rw [Measure.map_map (Cmp_measurable_psi D N) (Cmp_measurable_phi0 D N t)]
  congr 1
  funext ω
  funext p q
  change wig (D * N) (Real.exp (-t / 2) • blockEmb D N ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2)
      (finProdFinEquiv p) (finProdFinEquiv q) = Cmp_Θ D N t ω p q
  rw [wig_add, wig_smul, wig_smul]
  have h := congrFun (congrFun (wig_blockEmb D N ω.1) p) q
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h, Cmp_Θ]

/-- The law of `c x + d y` for independent `x ∼ μ₁`, `y ∼ μ₂`. -/
private def Cmp_conv (c d : ℂ) (μ₁ μ₂ : Measure ℂ) : Measure ℂ :=
  (μ₁.prod μ₂).map fun p => c * p.1 + d * p.2

/-- Mixed moments are integrable when all absolute moments are. -/
private lemma Cmp_integrable_mom {μ : Measure ℂ}
    (h : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ) (i j : ℕ) :
    Integrable (fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j) μ := by
  refine (h (i + j)).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  simp [norm_pow, pow_add]

/-- The mixed moments of `c x + d y`, by the binomial theorem and independence. -/
private lemma Cmp_conv_mom {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₁)
    (h₂ : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₂) (c d : ℂ) (p q : ℕ) :
    mixMom (Cmp_conv c d μ₁ μ₂) p q =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ((p.choose i : ℂ) * (q.choose j : ℂ) *
          (c ^ i * starRingEnd ℂ c ^ j * d ^ (p - i) * starRingEnd ℂ d ^ (q - j))) *
        (mixMom μ₁ i j * mixMom μ₂ (p - i) (q - j)) := by
  unfold mixMom Cmp_conv
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hexp : ∀ x : ℂ × ℂ, (c * x.1 + d * x.2) ^ p * starRingEnd ℂ (c * x.1 + d * x.2) ^ q =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ((p.choose i : ℂ) * (q.choose j : ℂ) *
          (c ^ i * starRingEnd ℂ c ^ j * d ^ (p - i) * starRingEnd ℂ d ^ (q - j))) *
        ((x.1 ^ i * starRingEnd ℂ x.1 ^ j) * (x.2 ^ (p - i) * starRingEnd ℂ x.2 ^ (q - j))) := by
    intro x
    rw [map_add, map_mul, map_mul, add_pow, add_pow, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j : ℕ, Integrable (fun x : ℂ × ℂ =>
      ((x.1 ^ i * starRingEnd ℂ x.1 ^ j) * (x.2 ^ (p - i) * starRingEnd ℂ x.2 ^ (q - j))))
      (μ₁.prod μ₂) := fun i j =>
    Integrable.mul_prod (f := fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j)
      (g := fun z : ℂ => z ^ (p - i) * starRingEnd ℂ z ^ (q - j))
      (Cmp_integrable_mom h₁ i j) (Cmp_integrable_mom h₂ (p - i) (q - j))
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_prod_mul (μ := μ₁) (ν := μ₂)
        (fun z : ℂ => z ^ i * starRingEnd ℂ z ^ j)
        (fun z : ℂ => z ^ (p - i) * starRingEnd ℂ z ^ (q - j))]
    · exact (hint i j).const_mul _
  · exact integrable_finsetSum _ fun j _ => (hint i j).const_mul _

/-- Matching of `x`, `x'` to order three and to `ε` at order four passes to `c x + d y`, with
`|c|^4 ε` at order four. -/
private lemma Cmp_conv_cmp (c d : ℂ) (r ε : ℝ) (hc : ‖c‖ ≤ r) (μ₁ μ₁' μ₂ : Measure ℂ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₁'] [IsProbabilityMeasure μ₂]
    (h₁ : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₁)
    (h₁' : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₁')
    (h₂ : ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) μ₂)
    (hm3 : ∀ a b : ℕ, a + b ≤ 3 → mixMom μ₁ a b = mixMom μ₁' a b)
    (hm4 : ∀ a b : ℕ, a + b = 4 → ‖mixMom μ₁ a b - mixMom μ₁' a b‖ ≤ ε) :
    (∀ a b : ℕ, a + b ≤ 3 → mixMom (Cmp_conv c d μ₁ μ₂) a b = mixMom (Cmp_conv c d μ₁' μ₂) a b) ∧
    (∀ a b : ℕ, a + b = 4 →
      ‖mixMom (Cmp_conv c d μ₁ μ₂) a b - mixMom (Cmp_conv c d μ₁' μ₂) a b‖ ≤ r ^ 4 * ε) := by
  have hdiff : ∀ p q : ℕ, mixMom (Cmp_conv c d μ₁ μ₂) p q - mixMom (Cmp_conv c d μ₁' μ₂) p q =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ((p.choose i : ℂ) * (q.choose j : ℂ) *
          (c ^ i * starRingEnd ℂ c ^ j * d ^ (p - i) * starRingEnd ℂ d ^ (q - j))) *
        ((mixMom μ₁ i j - mixMom μ₁' i j) * mixMom μ₂ (p - i) (q - j)) := by
    intro p q
    rw [Cmp_conv_mom h₁ h₂, Cmp_conv_mom h₁' h₂, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · rw [← sub_eq_zero, hdiff]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hi hj
    rw [hm3 i j (by omega), sub_self, zero_mul, mul_zero]
  · rw [hdiff, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · have h0 : mixMom μ₂ 0 0 = 1 := by simp [mixMom]
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul, h0]
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add, hab]
      have hr : 0 ≤ r := (norm_nonneg _).trans hc
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hc 4) (hm4 a b hab) (norm_nonneg _)
        (by positivity)
    · intro j hj hjb
      rw [Finset.mem_range] at hj
      rw [hm3 a j (by omega), sub_self, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self b)) h
    · intro i hi hia
      rw [Finset.mem_range] at hi
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [hm3 i j (by omega), sub_self, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self a)) h

/-- The coordinate law of one block is a probability measure. -/
private lemma Cmp_coordLaw_prob (N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    IsProbabilityMeasure (coordLaw N L) := by
  unfold coordLaw; infer_instance

/-- An entry above the diagonal of block `a` has law `νo`. -/
private lemma Cmp_mp_off (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (a : Fin D) (p q : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w a).2 p q) (blockLaw D N L)
      (L.νo : Measure ℂ) := by
  have := Cmp_coordLaw_prob N L
  have h1 : MeasurePreserving (Function.eval a) (blockLaw D N L) (coordLaw N L) :=
    measurePreserving_eval (fun _ : Fin D => coordLaw N L) a
  have h2 : MeasurePreserving (Prod.snd : Coords N → (Fin N → Fin N → ℂ)) (coordLaw N L)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) :=
    measurePreserving_snd
  have h3 := measurePreserving_eval (fun _ : Fin N => Measure.pi fun _ : Fin N =>
    (L.νo : Measure ℂ)) p
  have h4 := measurePreserving_eval (fun _ : Fin N => (L.νo : Measure ℂ)) q
  exact h4.comp (h3.comp (h2.comp h1))

/-- A diagonal entry of block `a` has law `νd`, as a complex number. -/
private lemma Cmp_mp_diag (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (a : Fin D) (p : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (((w a).1 p : ℝ) : ℂ)) (blockLaw D N L)
      ((L.νd : Measure ℝ).map (fun x : ℝ => (x : ℂ))) := by
  have := Cmp_coordLaw_prob N L
  have h1 : MeasurePreserving (Function.eval a) (blockLaw D N L) (coordLaw N L) :=
    measurePreserving_eval (fun _ : Fin D => coordLaw N L) a
  have h2 : MeasurePreserving (Prod.fst : Coords N → (Fin N → ℝ)) (coordLaw N L)
      (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)) := measurePreserving_fst
  have h3 := measurePreserving_eval (fun _ : Fin N => (L.νd : Measure ℝ)) p
  have h4 : MeasurePreserving (fun x : ℝ => (x : ℂ)) (L.νd : Measure ℝ)
      ((L.νd : Measure ℝ).map (fun x : ℝ => (x : ℂ))) :=
    ⟨Complex.measurable_ofReal, rfl⟩
  exact h4.comp (h3.comp (h2.comp h1))

/-- An entry above the diagonal of the GUE coordinates has law `cGauss`. -/
private lemma Cmp_mp_goff (n : ℕ) (p q : Fin n) :
    MeasurePreserving (fun w : Coords n => w.2 p q) (gueLaw n) (cGauss : Measure ℂ) := by
  have h2 : MeasurePreserving (Prod.snd : Coords n → (Fin n → Fin n → ℂ)) (gueLaw n)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) :=
    measurePreserving_snd
  have h3 := measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin n =>
    (cGauss : Measure ℂ)) p
  have h4 := measurePreserving_eval (fun _ : Fin n => (cGauss : Measure ℂ)) q
  exact h4.comp (h3.comp h2)

/-- A diagonal GUE coordinate has law `N(0, 1)`, as a complex number. -/
private lemma Cmp_mp_gdiag (n : ℕ) (p : Fin n) :
    MeasurePreserving (fun w : Coords n => ((w.1 p : ℝ) : ℂ)) (gueLaw n)
      ((gaussianReal 0 1).map (fun x : ℝ => (x : ℂ))) := by
  have h2 : MeasurePreserving (Prod.fst : Coords n → (Fin n → ℝ)) (gueLaw n)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := measurePreserving_fst
  have h3 := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) p
  have h4 : MeasurePreserving (fun x : ℝ => (x : ℂ)) (gaussianReal 0 1)
      ((gaussianReal 0 1).map (fun x : ℝ => (x : ℂ))) :=
    ⟨Complex.measurable_ofReal, rfl⟩
  exact h4.comp (h3.comp h2)

/-- The law of an entry `(p, q)` of `H_t` is `c x + d y` with `x` an entry of the
scaled blocks and `y` a GUE coordinate, as soon as `Cmp_Θ` has this form. -/
private lemma Cmp_entry_conv (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (p q : Idx D N)
    (c d : ℂ) (μ₁ μ₂ : Measure ℂ) [SFinite μ₁] [SFinite μ₂]
    (X : (Fin D → Coords N) → ℂ) (Y : Coords (D * N) → ℂ)
    (hX : MeasurePreserving X (blockLaw D N L) μ₁) (hY : MeasurePreserving Y (gueLaw (D * N)) μ₂)
    (hΘ : ∀ ω, Cmp_Θ D N t ω p q = c * X ω.1 + d * Y ω.2) :
    (ouMatLaw D N L t).map (fun h => h p q) = Cmp_conv c d μ₁ μ₂ := by
  have hΘm : Measurable (Cmp_Θ D N t) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
      (measurable_const.mul ((Cmp_measurable_blockH D N p q).comp measurable_fst)).add
        (measurable_const.mul
          ((Cmp_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)).comp
            measurable_snd))
  have hev : Measurable (fun h : Idx D N → Idx D N → ℂ => h p q) :=
    (measurable_pi_apply q).comp (measurable_pi_apply p)
  rw [Cmp_ouMatLaw_eq, Measure.map_map hev hΘm, Cmp_conv, ← (hX.prod hY).map_eq,
    Measure.map_map (by fun_prop) (hX.measurable.prodMap hY.measurable)]
  congr 1
  funext ω
  simp only [Function.comp, hΘ, Prod.map]

/-- `finProdFinEquiv` preserves the lexicographic order. -/
private lemma Cmp_fpe_lt {D N : ℕ} (p q : Idx D N) (h : toLex p < toLex q) :
    finProdFinEquiv p < finProdFinEquiv q := by
  rw [Prod.Lex.lt_iff] at h
  simp only [Fin.lt_def, finProdFinEquiv_apply_val]
  rcases h with h | ⟨h1, h2⟩
  · have := p.2.isLt
    have hq : (p.1 : ℕ) < q.1 := h
    nlinarith
  · have h1' : (p.1 : ℕ) = q.1 := congrArg Fin.val h1
    have h2' : (p.2 : ℕ) < q.2 := h2
    rw [h1']
    omega

/-- `(a + b)^k ≤ 2^k (a^k + b^k)` for `a, b ≥ 0`. -/
private lemma Cmp_pow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  refine (add_pow_le ha hb k).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)

/-- Every absolute moment of a real Gaussian law is finite. -/
private lemma Cmp_G_int (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal' (μ := 0) (v := v) ((k : ℕ) : ENNReal)
    (by simp)).integrable_norm_pow'
  simpa using this

/-- Every absolute moment of `cGauss` is finite. -/
private lemma Cmp_c_int (k : ℕ) : Integrable (fun z : ℂ => ‖z‖ ^ k) (cGauss : Measure ℂ) := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  have hc : Continuous (fun z : ℂ => ‖z‖ ^ k) := by fun_prop
  have hφ : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have e : (cGauss : Measure ℂ) = (G.prod G).map
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := rfl
  rw [e, integrable_map_measure hc.aestronglyMeasurable hφ.aemeasurable]
  refine Integrable.mono' (g := fun p : ℝ × ℝ => 2 ^ k * (|p.1| ^ k + |p.2| ^ k)) ?_ ?_ ?_
  · exact (((Cmp_G_int _ k).comp_fst G).add ((Cmp_G_int _ k).comp_snd G)).const_mul _
  · exact (hc.measurable.comp hφ).aestronglyMeasurable
  · filter_upwards with p
    have h1 : ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ≤ |p.1| + |p.2| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h2 := Cmp_pow_add_le (abs_nonneg p.1) (abs_nonneg p.2) k
    simp only [Function.comp, Real.norm_eq_abs, abs_pow, abs_norm]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 k).trans h2

/-- Moments of a real law viewed in `ℂ`. -/
private lemma Cmp_real_mom (ν : Measure ℝ) (hν : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) ν) :
    (∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ n) (ν.map (fun x : ℝ => (x : ℂ)))) ∧
    ∀ a b : ℕ, mixMom (ν.map (fun x : ℝ => (x : ℂ))) a b = ((∫ x, x ^ (a + b) ∂ν : ℝ) : ℂ) := by
  refine ⟨fun n => ?_, fun a b => ?_⟩
  · rw [integrable_map_measure (by fun_prop) Complex.measurable_ofReal.aemeasurable]
    exact (hν n).congr (Filter.Eventually.of_forall fun x => by simp)
  · unfold mixMom
    rw [integral_map Complex.measurable_ofReal.aemeasurable (by fun_prop),
      ← integral_complex_ofReal]
    congr 1
    funext x
    simp [pow_add]

/-- The scale `e^{-t/2} N^{-1/2}` of the entries of `H` in `H_t`. -/
private def Cmp_c0 (t : ℝ) (N : ℕ) : ℂ := ((Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- The scale `√(1 - e^{-t}) (DN)^{-1/2}` of the GUE entries in `H_t`. -/
private def Cmp_d0 (t : ℝ) (D N : ℕ) : ℂ :=
  ((Real.sqrt (1 - Real.exp (-t)) * ((D * N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- The law of an entry `(p, q)`, `p ≤ q`, of `H_t`, (4.3) [eq:eq_in_law_H]: on the diagonal
`c₀ x + d₀ g` with `x ∼ νd`, `g ∼ N(0, 1)`; above the diagonal `c x + d₀ g` with `x ∼ νo`,
`g ∼ cGauss`, `c = c₀` in a diagonal block and `c = 0` outside. -/
private lemma Cmp_entry_law (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (p q : Idx D N)
    (hpq : toLex p ≤ toLex q) :
    (p = q → (ouMatLaw D N L t).map (fun h => h p q) = Cmp_conv (Cmp_c0 t N) (Cmp_d0 t D N)
      ((L.νd : Measure ℝ).map (fun x : ℝ => (x : ℂ)))
      ((gaussianReal 0 1).map (fun x : ℝ => (x : ℂ)))) ∧
    (p ≠ q → (ouMatLaw D N L t).map (fun h => h p q) =
      Cmp_conv (if p.1 = q.1 then Cmp_c0 t N else 0) (Cmp_d0 t D N) (L.νo : Measure ℂ)
        (cGauss : Measure ℂ)) := by
  refine ⟨fun hpq' => ?_, fun hpq' => ?_⟩
  · subst hpq'
    refine Cmp_entry_conv D N L t p p _ _ _ _ _ _ (Cmp_mp_diag D N L p.1 p.2)
      (Cmp_mp_gdiag (D * N) (finProdFinEquiv p)) fun ω => ?_
    simp only [Cmp_Θ, blockH, wig, ite_true, Cmp_c0, Cmp_d0]
    push_cast
    ring
  · have hlt : toLex p < toLex q := lt_of_le_of_ne hpq (fun h => hpq' (toLex.injective h))
    have hIJ := Cmp_fpe_lt p q hlt
    have hIJ' : finProdFinEquiv p ≠ finProdFinEquiv q := ne_of_lt hIJ
    refine Cmp_entry_conv D N L t p q _ _ _ _ _ _ (Cmp_mp_off D N L p.1 p.2 q.2)
      (Cmp_mp_goff (D * N) (finProdFinEquiv p) (finProdFinEquiv q)) fun ω => ?_
    by_cases hb : p.1 = q.1
    · have h2 : p.2 < q.2 := by
        rw [Prod.Lex.lt_iff] at hlt
        rcases hlt with h | ⟨_, h⟩
        · exact absurd hb (ne_of_lt h)
        · exact h
      have h2' : p.2 ≠ q.2 := ne_of_lt h2
      simp only [Cmp_Θ, blockH, wig, hb, ite_true, h2', h2, hIJ', hIJ, ite_false, Cmp_c0, Cmp_d0]
      push_cast
      ring
    · simp only [Cmp_Θ, blockH, wig, hb, ite_false, hIJ', hIJ, ite_true, Cmp_d0]
      push_cast
      ring

/-- The matching (3.36) [comH0], (3.37) [comH] of the scaled entry laws passes to the entries
`(p, q)`, `p ≤ q`, of `H_t`, `t ≥ 0`: equal moments of order `≤ 3`, and order `4` within
`N^{-2} ε`. -/
private lemma Cmp_entry_cmp (D N : ℕ) {C C' : ℕ → ℝ} (L : EntryLaws C) (L' : EntryLaws C') (ε : ℝ)
    (h3o : ∀ a b : ℕ, a + b ≤ 3 → mixMom L.νo a b = mixMom L'.νo a b)
    (h4o : ∀ a b : ℕ, a + b = 4 → ‖mixMom L.νo a b - mixMom L'.νo a b‖ ≤ ε)
    (h3d : ∀ a : ℕ, a ≤ 3 → ∫ x, x ^ a ∂(L.νd : Measure ℝ) = ∫ x, x ^ a ∂(L'.νd : Measure ℝ))
    (h4d : |(∫ x, x ^ 4 ∂(L.νd : Measure ℝ)) - ∫ x, x ^ 4 ∂(L'.νd : Measure ℝ)| ≤ ε)
    (t : ℝ) (ht : 0 ≤ t) (p q : Idx D N) (hpq : toLex p ≤ toLex q) :
    (∀ a b : ℕ, a + b ≤ 3 → mixMom ((ouMatLaw D N L t).map (fun h => h p q)) a b =
      mixMom ((ouMatLaw D N L' t).map (fun h => h p q)) a b) ∧
    (∀ a b : ℕ, a + b = 4 → ‖mixMom ((ouMatLaw D N L t).map (fun h => h p q)) a b -
      mixMom ((ouMatLaw D N L' t).map (fun h => h p q)) a b‖ ≤
        ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 4 * ε) := by
  have hc0 : ‖Cmp_c0 t N‖ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have h1 : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [Cmp_c0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := one_mul _
  by_cases hd : p = q
  · rw [(Cmp_entry_law D N L t p q hpq).1 hd, (Cmp_entry_law D N L' t p q hpq).1 hd]
    obtain ⟨i1, m1⟩ := Cmp_real_mom (L.νd : Measure ℝ) L.intd
    obtain ⟨i1', m1'⟩ := Cmp_real_mom (L'.νd : Measure ℝ) L'.intd
    obtain ⟨i2, -⟩ := Cmp_real_mom (gaussianReal 0 1) (Cmp_G_int 1)
    refine Cmp_conv_cmp _ _ _ ε hc0 _ _ _ i1 i1' i2 (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [m1, m1', h3d (a + b) hab]
    · rw [m1, m1', hab, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact h4d
  · rw [(Cmp_entry_law D N L t p q hpq).2 hd, (Cmp_entry_law D N L' t p q hpq).2 hd]
    have hc : ‖(if p.1 = q.1 then Cmp_c0 t N else 0)‖ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      split_ifs
      · exact hc0
      · rw [norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact Cmp_conv_cmp _ _ _ ε hc _ _ _ L.into L'.into Cmp_c_int h3o h4o

/-! ### Measurability and boundedness of the loop -/

/-- Every entry of `(h + Λ - ξ)⁻¹` is a measurable function of the array. -/
private lemma Cmp_meas_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (k l : Idx D N) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of h + Λ) ξ k l) := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ =>
      Matrix.of h + Λ - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) :=
    (continuous_id.add continuous_const).sub continuous_const
  have hdet := hc.matrix_det.measurable
  have hadj := hc.matrix_adjugate.measurable
  simp only [res, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp hadj))

/-- Every entry of a chain is a measurable function of the array. -/
private lemma Cmp_meas_chain {D N : ℕ} :
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ), ∀ k m,
      Measurable (fun h : Idx D N → Idx D N → ℂ => chainB h l k m) := by
  intro l
  induction l with
  | nil =>
    intro k m
    simp only [chainB, List.map_nil, List.prod_nil]
    exact measurable_const
  | cons f t ih =>
    intro k m
    have e : (fun h : Idx D N → Idx D N → ℂ => chainB h (f :: t) k m) = fun h =>
        ∑ q, (∑ s, f.1 k s * res (Matrix.of h + f.2.1) f.2.2 s q) * chainB h t q m := by
      funext h
      simp only [chainB, List.map_cons, List.prod_cons, Matrix.mul_apply]
    rw [e]
    exact Finset.measurable_sum _ fun q _ => (Finset.measurable_sum _ fun s _ =>
      measurable_const.mul (Cmp_meas_res _ _ s q)).mul (ih q m)

/-- The loop `h ↦ ⟨chain⟩` is measurable. -/
private lemma Cmp_meas_loop {D N : ℕ}
    (l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ)) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => ntr (chainB h l)) := by
  have e : (fun h : Idx D N → Idx D N → ℂ => ntr (chainB h l)) = fun h =>
      ((Fintype.card (Idx D N) : ℂ))⁻¹ * ∑ k, chainB h l k k := by
    funext h; rfl
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ => Cmp_meas_chain l k k)

/-- `|⟨B⟩| ≤ ‖B‖`. -/
private lemma Cmp_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    ‖ntr B‖ ≤ opNorm B := by
  have h0 : 0 ≤ opNorm B := norm_nonneg _
  unfold ntr Matrix.trace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc | hc
  · rw [hc]; simp [h0]
  · have hc' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hc
    rw [inv_mul_le_iff₀ hc']
    calc ‖∑ i, Matrix.diag B i‖ ≤ ∑ i, ‖Matrix.diag B i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, opNorm B := Finset.sum_le_sum fun i _ => norm_apply_le_opNorm B i i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The Hermitian completion of an array from its entries on and above the diagonal (real part on
the diagonal, conjugates below). -/
private def Cmp_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ) : Idx D N → Idx D N → ℂ :=
  fun r s => if r = s then (((h r r).re : ℝ) : ℂ) else if toLex r < toLex s then h r s
    else starRingEnd ℂ (h s r)

/-- The Hermitian completion is Hermitian. -/
private lemma Cmp_herm_isHermitian {D N : ℕ} (h : Idx D N → Idx D N → ℂ) :
    (Matrix.of (Cmp_herm h)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun r s => ?_
  simp only [Matrix.of_apply, Cmp_herm]
  by_cases hrs : r = s
  · subst hrs; simp
  · have hsr : ¬ s = r := fun e => hrs e.symm
    by_cases hlt : toLex r < toLex s
    · have : ¬ toLex s < toLex r := fun e => lt_asymm hlt e
      simp [hrs, hsr, hlt, this]
    · have : toLex s < toLex r := lt_of_le_of_ne (not_lt.mp hlt)
        (fun e => hrs (toLex.injective e).symm)
      simp [hrs, hsr, hlt, this]

/-- A Hermitian array is its own Hermitian completion. -/
private lemma Cmp_herm_of_isHermitian {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) : Cmp_herm h = h := by
  funext r s
  have h1 : ∀ r s, starRingEnd ℂ (h s r) = h r s := fun r s => by
    simpa [Complex.star_def] using hh.apply r s
  simp only [Cmp_herm]
  by_cases hrs : r = s
  · subst hrs
    simp only [ite_true]
    have := h1 r r
    exact Complex.conj_eq_iff_re.mp this
  · simp only [hrs, ite_false]
    split_ifs
    · rfl
    · exact h1 r s

/-- The Hermitian completion is measurable. -/
private lemma Cmp_meas_herm {D N : ℕ} :
    Measurable (fun h : Idx D N → Idx D N → ℂ => Cmp_herm h) := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun s => ?_
  simp only [Cmp_herm]
  split_ifs
  · exact Complex.measurable_ofReal.comp (Complex.measurable_re.comp
      ((measurable_pi_apply r).comp (measurable_pi_apply r)))
  · exact (measurable_pi_apply s).comp (measurable_pi_apply r)
  · exact (continuous_star (R := ℂ)).measurable.comp
      ((measurable_pi_apply r).comp (measurable_pi_apply s))

/-- The one-entry substitution is jointly measurable in the array and the value. -/
private lemma Cmp_meas_setEntry {D N : ℕ} (i j : Idx D N) :
    Measurable (fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2) := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun s => ?_
  simp only [setEntry]
  split_ifs
  · exact Complex.measurable_ofReal.comp (Complex.measurable_re.comp measurable_snd)
  · exact (measurable_pi_apply s).comp ((measurable_pi_apply r).comp measurable_fst)
  · exact measurable_snd
  · exact (continuous_star (R := ℂ)).measurable.comp measurable_snd
  · exact (measurable_pi_apply s).comp ((measurable_pi_apply r).comp measurable_fst)

/-- The set of arrays with the entry bounds `Cmp_EB` is measurable. -/
private lemma Cmp_meas_EB {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (Γ : ℝ) :
    MeasurableSet {h : Idx D N → Idx D N → ℂ | Cmp_EB Λ z Γ h} := by
  have e : {h : Idx D N → Idx D N → ℂ | Cmp_EB Λ z Γ h} = ⋂ k, ⋂ m,
      ({h | ‖res (Matrix.of h + Λ) z k m‖ ≤ Γ} ∩
        {h | ‖res (Matrix.of h + Λ) (star z) k m‖ ≤ Γ}) := by
    ext h; simp [Cmp_EB, Set.mem_iInter]
  rw [e]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun m =>
    (measurableSet_le (Cmp_meas_res Λ z k m).norm measurable_const).inter
      (measurableSet_le (Cmp_meas_res Λ (star z) k m).norm measurable_const)

/-- The loop of `Cmp_l0` at a Hermitian array is bounded by `|Im z|^{-2}`. -/
private lemma Cmp_loop_le {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z z₁ z₂ : ℂ) (hz : z.im ≠ 0) (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ‖ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b))‖ ≤ (|z.im|⁻¹) ^ 2 :=
  (Cmp_ntr_le _).trans (Cmp_opNorm_chain Λ hΛ z hz h hh _
    fun f hf => Cmp_l0_fac Λ z z₁ z₂ hz₁ hz₂ a b f (Or.inl hf))

/-! ### Independence and the one-entry factorization -/

/-- Two independent families of independent complex random variables form one independent
family, indexed by the disjoint sum. -/
private lemma Cmp_iIndepFun_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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

/-- Independence of a family transfers along a measure-preserving map. -/
private lemma Cmp_iIndepFun_comp_mp {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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

/-- The index set of the entries on and above the diagonal. -/
private abbrev Cmp_UT (D N : ℕ) := {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}

/-- The joint family of the entries on and above the diagonal of the two arrays. -/
private def Cmp_F {D N : ℕ} :
    Cmp_UT D N ⊕ Cmp_UT D N → (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) → ℂ :=
  Sum.elim (fun q p => p.1 q.1.1 q.1.2) (fun q p => p.2 q.1.1 q.1.2)

/-- Under `μ ⊗ μ'` with independent upper entries in each factor, the joint family is
independent. -/
private lemma Cmp_iIndep_F {D N : ℕ} {μ μ' : Measure (Idx D N → Idx D N → ℂ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : iIndepFun (fun (q : Cmp_UT D N) (h : Idx D N → Idx D N → ℂ) => h q.1.1 q.1.2) μ)
    (hμ' : iIndepFun (fun (q : Cmp_UT D N) (h : Idx D N → Idx D N → ℂ) => h q.1.1 q.1.2) μ') :
    iIndepFun (Cmp_F (D := D) (N := N)) (μ.prod μ') := by
  have hu : ∀ q : Cmp_UT D N, Measurable (fun h : Idx D N → Idx D N → ℂ => h q.1.1 q.1.2) :=
    fun q => (measurable_pi_apply q.1.2).comp (measurable_pi_apply q.1.1)
  have h1 := Cmp_iIndepFun_comp_mp (measurePreserving_fst (μ := μ) (ν := μ')) hu hμ
  have h2 := Cmp_iIndepFun_comp_mp (measurePreserving_snd (μ := μ) (ν := μ')) hu hμ'
  have h3 : IndepFun (fun (ω : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ))
      (q : Cmp_UT D N) => ω.1 q.1.1 q.1.2)
      (fun (ω : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) (q : Cmp_UT D N) =>
        ω.2 q.1.1 q.1.2) (μ.prod μ') :=
    indepFun_prod (μ := μ) (ν := μ')
      (X := fun x (q : Cmp_UT D N) => x q.1.1 q.1.2) (Y := fun y (q : Cmp_UT D N) => y q.1.1 q.1.2)
      (measurable_pi_iff.mpr hu) (measurable_pi_iff.mpr hu)
  exact Cmp_iIndepFun_sum h1 h2 h3

/-- `E G(Y, W) = E ∫ G(Y, x) dLaw(W)(x)` for independent `Y`, `W` and bounded measurable `G`. -/
private lemma Cmp_indep_integral {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → α} {W : Ω → ℂ} (hY : Measurable Y)
    (hW : Measurable W) (hind : IndepFun Y W P) (G : α → ℂ → ℂ)
    (hG : Measurable (Function.uncurry G)) (c : ℝ) (hc : ∀ a x, ‖G a x‖ ≤ c) :
    ∫ ω, G (Y ω) (W ω) ∂P = ∫ ω, (∫ x, G (Y ω) x ∂(P.map W)) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hW.aemeasurable).1 hind
  have hint : Integrable (Function.uncurry G) ((P.map Y).prod (P.map W)) :=
    Integrable.of_bound hG.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun p => hc p.1 p.2)
  have e1 : ∫ ω, G (Y ω) (W ω) ∂P = ∫ p, Function.uncurry G p ∂(P.map fun ω => (Y ω, W ω)) := by
    rw [integral_map (hY.prodMk hW).aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [e1, hmap, integral_prod _ hint]
  have hsm : StronglyMeasurable (fun a => ∫ x, Function.uncurry G (a, x) ∂(P.map W)) :=
    hG.stronglyMeasurable.integral_prod_right'
  rw [integral_map hY.aemeasurable hsm.aestronglyMeasurable]
  rfl

/-! ### The Lindeberg replacement -/

/-- The pairs `(p, q)`, `p ≤ q` lexicographically, listed once each. -/
private def Cmp_UTl (D N : ℕ) : List (Idx D N × Idx D N) :=
  (Finset.univ.filter fun q : Idx D N × Idx D N => toLex q.1 ≤ toLex q.2).toList

/-- The replacement set after `k` steps: the first `k` pairs of `Cmp_UTl`. -/
private def Cmp_Γ (D N : ℕ) (k : ℕ) : Set (Idx D N × Idx D N) := {q | q ∈ (Cmp_UTl D N).take k}

/-- Membership in `Cmp_UTl`. -/
private lemma Cmp_mem_UTl {D N : ℕ} (q : Idx D N × Idx D N) :
    q ∈ Cmp_UTl D N ↔ toLex q.1 ≤ toLex q.2 := by
  simp [Cmp_UTl]

/-- `Cmp_UTl` has no duplicates. -/
private lemma Cmp_UTl_nodup (D N : ℕ) : (Cmp_UTl D N).Nodup := Finset.nodup_toList _

/-- At most `(DN)²` pairs. -/
private lemma Cmp_UTl_length (D N : ℕ) : ((Cmp_UTl D N).length : ℝ) ≤ ((D : ℝ) * N) ^ 2 := by
  have h : (Cmp_UTl D N).length ≤ D * N * (D * N) := by
    rw [Cmp_UTl, Finset.length_toList]
    refine (Finset.card_filter_le _ _).trans ?_
    simp [Finset.card_univ, Fintype.card_prod]
  have : ((Cmp_UTl D N).length : ℝ) ≤ ((D * N * (D * N) : ℕ) : ℝ) := by exact_mod_cast h
  rw [sq]
  push_cast at this
  exact this

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma Cmp_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · rw [hkl.1, hkl.2]
      simp only [setEntry, and_self, ite_true]
      exact Complex.conj_eq_iff_re.mp (h1 i i)
    · simp [setEntry, hkl]
  · by_cases ha : k = i ∧ l = j
    · rw [ha.1, ha.2]
      simp [setEntry, hd]
    · by_cases hb : k = j ∧ l = i
      · rw [hb.1, hb.2]
        simp [setEntry, hd, Ne.symm hd, h1]
      · simp [setEntry, hd, ha, hb]

/-- Two arrays that agree outside `(i, j)`, `(j, i)` agree after the substitution. -/
private lemma Cmp_setEntry_congr {D N : ℕ} (h h' : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (hhh : ∀ r s, ¬ (r = i ∧ s = j) → ¬ (r = j ∧ s = i) → h r s = h' r s) (w : ℂ) :
    setEntry h i j w = setEntry h' i j w := by
  funext r s
  by_cases hd : i = j
  · subst hd
    by_cases hrs : r = i ∧ s = i
    · simp [setEntry, hrs]
    · simp only [setEntry, ite_true, hrs, ite_false]
      exact hhh r s hrs hrs
  · by_cases ha : r = i ∧ s = j
    · simp [setEntry, hd, ha]
    · by_cases hb : r = j ∧ s = i
      · simp [setEntry, hd, hb]
      · simp only [setEntry, hd, ha, hb, ite_false]
        exact hhh r s ha hb

/-- The hybrid of two Hermitian arrays is Hermitian. -/
private lemma Cmp_hyb_herm {D N : ℕ} (Γ : Set (Idx D N × Idx D N))
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) (h1 : (Matrix.of p.1).IsHermitian)
    (h2 : (Matrix.of p.2).IsHermitian) : (Matrix.of (hybridArr Γ p)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  by_cases h : (i, j) ∈ Γ ∨ (j, i) ∈ Γ
  · have h' : (j, i) ∈ Γ ∨ (i, j) ∈ Γ := h.symm
    simp only [Matrix.of_apply, hybridArr, h, h', ↓reduceIte]
    exact h1.apply i j
  · have h' : ¬ ((j, i) ∈ Γ ∨ (i, j) ∈ Γ) := fun h2 => h h2.symm
    simp only [Matrix.of_apply, hybridArr, h, h', ↓reduceIte]
    exact h2.apply i j

/-- `hybridArr Γ` is measurable. -/
private lemma Cmp_hyb_meas {D N : ℕ} (Γ : Set (Idx D N × Idx D N)) :
    Measurable (hybridArr Γ) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have h1 : Measurable fun x : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => x.1 i j := by
    fun_prop
  have h2 : Measurable fun x : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => x.2 i j := by
    fun_prop
  by_cases h : (i, j) ∈ Γ ∨ (j, i) ∈ Γ
  · simpa only [hybridArr, h, ↓reduceIte] using h1
  · simpa only [hybridArr, h, ↓reduceIte] using h2

/-- The structure of one step: `Γ_{k+1} = Γ_k ∪ {(i, j)}` with `(i, j) ∉ Γ_k`, `i ≤ j`. -/
private lemma Cmp_Γ_succ {D N : ℕ} (k : ℕ) (hk : k < (Cmp_UTl D N).length) :
    (∀ q, q ∈ Cmp_Γ D N (k + 1) ↔ q ∈ Cmp_Γ D N k ∨ q = (Cmp_UTl D N)[k]) ∧
    (Cmp_UTl D N)[k] ∉ Cmp_Γ D N k ∧
    toLex ((Cmp_UTl D N)[k]).1 ≤ toLex ((Cmp_UTl D N)[k]).2 ∧
    (∀ q ∈ Cmp_Γ D N k, toLex q.1 ≤ toLex q.2) := by
  have ht := List.take_succ_eq_append_getElem hk
  refine ⟨fun q => ?_, ?_, ?_, ?_⟩
  · simp only [Cmp_Γ, Set.mem_ofPred_eq, ht, List.mem_append, List.mem_singleton]
  · intro hmem
    have hnd : ((Cmp_UTl D N).take (k + 1)).Nodup :=
      (Cmp_UTl_nodup D N).sublist (List.take_sublist _ _)
    rw [ht, List.nodup_append] at hnd
    exact hnd.2.2 _ hmem _ (List.mem_singleton_self _) rfl
  · exact (Cmp_mem_UTl _).1 (List.getElem_mem hk)
  · intro q hq
    exact (Cmp_mem_UTl q).1 (List.mem_of_mem_take hq)

/-- The base of step `k`: the Hermitian completion of the hybrid `Γ_k`, with `(i, j)` set to `0`. -/
private def Cmp_B {D N : ℕ} (k : ℕ) (i j : Idx D N)
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) : Idx D N → Idx D N → ℂ :=
  setEntry (Cmp_herm (hybridArr (Cmp_Γ D N k) p)) i j 0

/-- The base is Hermitian, with entry `(i, j)` equal to `0`. -/
private lemma Cmp_B_herm {D N : ℕ} (k : ℕ) (i j : Idx D N)
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) :
    (Matrix.of (Cmp_B k i j p)).IsHermitian ∧ Cmp_B k i j p i j = 0 := by
  refine ⟨Cmp_setEntry_herm _ (Cmp_herm_isHermitian _) i j 0, ?_⟩
  by_cases hd : i = j
  · subst hd; simp [Cmp_B, setEntry]
  · simp [Cmp_B, setEntry, hd]

/-- The base is measurable. -/
private lemma Cmp_B_meas {D N : ℕ} (k : ℕ) (i j : Idx D N) :
    Measurable (Cmp_B (D := D) (N := N) k i j) :=
  (Cmp_meas_setEntry i j).comp ((Cmp_meas_herm.comp (Cmp_hyb_meas _)).prodMk measurable_const)

/-- On Hermitian pairs, the two hybrids of step `k` are the base with the entry `(i, j)` of `μ`,
resp. of `μ'`. -/
private lemma Cmp_hyb_eq {D N : ℕ} (k : ℕ) (hk : k < (Cmp_UTl D N).length)
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) (h1 : (Matrix.of p.1).IsHermitian)
    (h2 : (Matrix.of p.2).IsHermitian) :
    hybridArr (Cmp_Γ D N (k + 1)) p = setEntry (Cmp_B k ((Cmp_UTl D N)[k]).1
      ((Cmp_UTl D N)[k]).2 p) ((Cmp_UTl D N)[k]).1 ((Cmp_UTl D N)[k]).2
        (p.1 ((Cmp_UTl D N)[k]).1 ((Cmp_UTl D N)[k]).2) ∧
    hybridArr (Cmp_Γ D N k) p = setEntry (Cmp_B k ((Cmp_UTl D N)[k]).1
      ((Cmp_UTl D N)[k]).2 p) ((Cmp_UTl D N)[k]).1 ((Cmp_UTl D N)[k]).2
        (p.2 ((Cmp_UTl D N)[k]).1 ((Cmp_UTl D N)[k]).2) := by
  obtain ⟨hsucc, hnot, hle, hup⟩ := Cmp_Γ_succ (D := D) (N := N) k hk
  set i := ((Cmp_UTl D N)[k]).1 with hi
  set j := ((Cmp_UTl D N)[k]).2 with hj
  have hji : i ≠ j → (j, i) ∉ Cmp_Γ D N k := by
    intro hne hmem
    have := hup _ hmem
    have h' : toLex i = toLex j := le_antisymm hle this
    exact hne (toLex.injective h')
  have hji' : i ≠ j → (j, i) ∉ Cmp_Γ D N (k + 1) := by
    intro hne hmem
    rcases (hsucc _).1 hmem with h | h
    · exact hji hne h
    · exact hne (Prod.ext_iff.1 h).1.symm
  set X := hybridArr (Cmp_Γ D N k) p with hX
  set X' := hybridArr (Cmp_Γ D N (k + 1)) p with hX'
  have hXh : (Matrix.of X).IsHermitian := Cmp_hyb_herm _ p h1 h2
  have hX'h : (Matrix.of X').IsHermitian := Cmp_hyb_herm _ p h1 h2
  have hB : Cmp_B k i j p = setEntry X i j 0 := by
    rw [Cmp_B, ← hX, Cmp_herm_of_isHermitian X hXh]
  have hXij : X i j = p.2 i j := by
    have : ¬ ((i, j) ∈ Cmp_Γ D N k ∨ (j, i) ∈ Cmp_Γ D N k) := by
      rintro (h | h)
      · exact hnot h
      · by_cases hd : i = j
        · have e : (Cmp_UTl D N)[k] = (j, i) := Prod.ext hd hd.symm
          exact hnot (e ▸ h)
        · exact hji hd h
    simp [hX, hybridArr, this]
  have hX'ij : X' i j = p.1 i j := by
    have : (i, j) ∈ Cmp_Γ D N (k + 1) ∨ (j, i) ∈ Cmp_Γ D N (k + 1) :=
      Or.inl ((hsucc _).2 (Or.inr rfl))
    simp [hX', hybridArr, this]
  have hagree : ∀ r s, ¬ (r = i ∧ s = j) → ¬ (r = j ∧ s = i) → X r s = X' r s := by
    intro r s ha hb
    have e1 : (r, s) ∈ Cmp_Γ D N (k + 1) ↔ (r, s) ∈ Cmp_Γ D N k := by
      rw [hsucc]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd (Prod.ext_iff.1 h) ha
      · exact Or.inl
    have e2 : (s, r) ∈ Cmp_Γ D N (k + 1) ↔ (s, r) ∈ Cmp_Γ D N k := by
      rw [hsucc]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd ⟨(Prod.ext_iff.1 h).2, (Prod.ext_iff.1 h).1⟩ hb
      · exact Or.inl
    simp only [hX, hX', hybridArr, e1, e2]
  refine ⟨?_, ?_⟩
  · rw [hB, Cmp_setEntry_congr X X' i j hagree 0, setEntry_setEntry, ← hX'ij,
      Cmp_setEntry_self X' hX'h]
  · rw [hB, setEntry_setEntry, ← hXij, Cmp_setEntry_self X hXh]

/-- The base of step `k` is independent of the entry `(i, j)` of each of the two arrays. -/
private lemma Cmp_B_indep {D N : ℕ} {μ μ' : Measure (Idx D N → Idx D N → ℂ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : iIndepFun (fun (q : Cmp_UT D N) (h : Idx D N → Idx D N → ℂ) => h q.1.1 q.1.2) μ)
    (hμ' : iIndepFun (fun (q : Cmp_UT D N) (h : Idx D N → Idx D N → ℂ) => h q.1.1 q.1.2) μ')
    (k : ℕ) (i j : Idx D N) (hij : toLex i ≤ toLex j) :
    IndepFun (Cmp_B k i j) (fun p => p.1 i j) (μ.prod μ') ∧
      IndepFun (Cmp_B k i j) (fun p => p.2 i j) (μ.prod μ') := by
  have hF := Cmp_iIndep_F hμ hμ'
  set q₀ : Cmp_UT D N := ⟨(i, j), hij⟩ with hq₀
  set m : Cmp_UT D N ⊕ Cmp_UT D N →
      MeasurableSpace ((Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) :=
    fun s => MeasurableSpace.comap (Cmp_F s) (inferInstance : MeasurableSpace ℂ) with hm
  have hle : ∀ s, m s ≤ (inferInstance : MeasurableSpace
      ((Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ))) := fun s => by
    have : Measurable (Cmp_F (D := D) (N := N) s) := by
      cases s with
      | inl q => exact (measurable_pi_apply q.1.2).comp ((measurable_pi_apply q.1.1).comp
          measurable_fst)
      | inr q => exact (measurable_pi_apply q.1.2).comp ((measurable_pi_apply q.1.1).comp
          measurable_snd)
    exact this.comap_le
  have hind := hF.iIndep
  set T : Set (Cmp_UT D N ⊕ Cmp_UT D N) := {s | s ≠ Sum.inl q₀ ∧ s ≠ Sum.inr q₀} with hT
  set mT := ⨆ s ∈ T, m s with hmT
  have hFT : ∀ s ∈ T, Measurable[mT] (Cmp_F (D := D) (N := N) s) := fun s hs =>
    (comap_measurable (Cmp_F s)).mono (le_iSup₂ (f := fun s _ => m s) s hs) le_rfl
  -- the entries of the base are `mT`-measurable
  have hXm : ∀ r s : Idx D N, toLex r ≤ toLex s → (r, s) ≠ (i, j) →
      Measurable[mT] (fun p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) =>
        hybridArr (Cmp_Γ D N k) p r s) := by
    intro r s hrs hne
    have h1 : Sum.inl (⟨(r, s), hrs⟩ : Cmp_UT D N) ∈ T := by
      refine ⟨fun e => hne ?_, fun e => Sum.inl_ne_inr e⟩
      have := Sum.inl_injective e
      exact congrArg Subtype.val this
    have h2 : Sum.inr (⟨(r, s), hrs⟩ : Cmp_UT D N) ∈ T := by
      refine ⟨fun e => Sum.inr_ne_inl e, fun e => hne ?_⟩
      have := Sum.inr_injective e
      exact congrArg Subtype.val this
    by_cases hc : (r, s) ∈ Cmp_Γ D N k ∨ (s, r) ∈ Cmp_Γ D N k
    · simp only [hybridArr, hc, ↓reduceIte]
      exact hFT _ h1
    · simp only [hybridArr, hc, ↓reduceIte]
      exact hFT _ h2
  have hBm : Measurable[mT] (Cmp_B (D := D) (N := N) k i j) := by
    refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun s => ?_
    have hH : ¬ (r = i ∧ s = j) → ¬ (r = j ∧ s = i) →
        Measurable[mT] (fun p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) =>
          Cmp_herm (hybridArr (Cmp_Γ D N k) p) r s) := by
      intro ha hb
      simp only [Cmp_herm]
      by_cases hrs : r = s
      · subst hrs
        simp only [ite_true]
        exact Complex.measurable_ofReal.comp (Complex.measurable_re.comp
          (hXm r r le_rfl fun e => ha ⟨(Prod.ext_iff.1 e).1, (Prod.ext_iff.1 e).2⟩))
      · simp only [hrs, ite_false]
        by_cases hlt : toLex r < toLex s
        · simp only [hlt, ite_true]
          exact hXm r s hlt.le fun e => ha ⟨(Prod.ext_iff.1 e).1, (Prod.ext_iff.1 e).2⟩
        · simp only [hlt, ite_false]
          exact (continuous_star (R := ℂ)).measurable.comp (hXm s r (not_lt.mp hlt)
            fun e => hb ⟨(Prod.ext_iff.1 e).2, (Prod.ext_iff.1 e).1⟩)
    simp only [Cmp_B, setEntry]
    by_cases hd : i = j
    · subst hd
      by_cases hrs : r = i ∧ s = i
      · simp only [ite_true, hrs]; exact measurable_const
      · simp only [ite_true, hrs, ite_false]
        exact hH hrs hrs
    · simp only [hd, ite_false]
      by_cases ha : r = i ∧ s = j
      · simp only [ha]; exact measurable_const
      · simp only [ha, ite_false]
        by_cases hb : r = j ∧ s = i
        · simp only [hb]; exact measurable_const
        · simp only [hb, ite_false]
          exact hH ha hb
  have hBle : MeasurableSpace.comap (Cmp_B (D := D) (N := N) k i j)
      (inferInstance : MeasurableSpace (Idx D N → Idx D N → ℂ)) ≤ mT :=
    hBm.comap_le
  have key : ∀ s₀ : Cmp_UT D N ⊕ Cmp_UT D N, s₀ ∉ T →
      IndepFun (Cmp_B k i j) (Cmp_F s₀) (μ.prod μ') := by
    intro s₀ hs₀
    have hdis : Disjoint T {s₀} := Set.disjoint_singleton_right.mpr hs₀
    have h := indep_iSup_of_disjoint hle hind hdis
    have h' : m s₀ ≤ ⨆ s ∈ ({s₀} : Set (Cmp_UT D N ⊕ Cmp_UT D N)), m s :=
      le_iSup₂ (f := fun s _ => m s) s₀ rfl
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h hBle) h'
  refine ⟨key (Sum.inl q₀) (fun h => h.1 rfl), key (Sum.inr q₀) (fun h => h.2 rfl)⟩

/-- The good bound of one Lindeberg step (fourth order, fifth order inside `|w| ≤ M`, tail). -/
private def Cmp_Bg (D N : ℕ) (u Γ₁ ε₄ m5 mk M : ℝ) (k : ℕ) : ℝ :=
  25 * (6 ^ 4 * ((D : ℝ) * N)⁻¹ * (2 * Γ₁) ^ 4 * u ^ 2) * ε₄ +
    32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * (2 * Γ₁) ^ 5 * u ^ 2) * m5 +
    32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * u ^ 7) * mk / M ^ k

/-- The deterministic bound of one Lindeberg step. -/
private def Cmp_Bd (D N : ℕ) (u ε₄ m5 mk M : ℝ) (k : ℕ) : ℝ :=
  25 * (6 ^ 4 * ((D : ℝ) * N)⁻¹ * u ^ 6) * ε₄ + 32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * u ^ 7) * m5 +
    32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * u ^ 7) * mk / M ^ k

/-- A class member is almost surely Hermitian in each factor of `μ ⊗ μ'`. -/
private lemma Cmp_ae_herm {D N : ℕ} {Cst : ℕ → ℝ} {θ : ℝ} {μ μ' : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N Cst θ μ) (hμ' : LLClass D N Cst θ μ') :
    ∀ᵐ p ∂(μ.prod μ'), (Matrix.of p.1).IsHermitian ∧ (Matrix.of p.2).IsHermitian := by
  have := hμ.prob
  have := hμ'.prob
  have e1 : ∀ᵐ p ∂(μ.prod μ'), (Matrix.of p.1).IsHermitian :=
    (measurePreserving_fst (μ := μ) (ν := μ')).quasiMeasurePreserving.ae hμ.herm
  have e2 : ∀ᵐ p ∂(μ.prod μ'), (Matrix.of p.2).IsHermitian :=
    (measurePreserving_snd (μ := μ) (ν := μ')).quasiMeasurePreserving.ae hμ'.herm
  filter_upwards [e1, e2] with p h1 h2
  exact ⟨h1, h2⟩

/-- One Lindeberg step: replacing the entry `(i, j)` of the hybrid `Γ_k` changes `E ⟨E_b G₁ E_a G₂⟩`
by at most the good bound plus the deterministic bound times the probability of the bad event
(entries of `G` above `Γ₀`, or `|h_{ij}| > M`) for the hybrid. -/
private lemma Cmp_lind_step {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z z₁ z₂ : ℂ) (hz : z.im ≠ 0) (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) {Cst : ℕ → ℝ} {θ : ℝ} (μ μ' : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N Cst θ μ) (hμ' : LLClass D N Cst θ μ')
    (k : ℕ) (hk : k < (Cmp_UTl D N).length) (i j : Idx D N) (hij : (Cmp_UTl D N)[k] = (i, j))
    (ε₄ m5 mk Γ₀ M : ℝ) (k' : ℕ)
    (hm3 : ∀ a b : ℕ, a + b ≤ 3 →
      mixMom (μ.map fun h => h i j) a b = mixMom (μ'.map fun h => h i j) a b)
    (hm4 : ∀ a b : ℕ, a + b = 4 →
      ‖mixMom (μ.map fun h => h i j) a b - mixMom (μ'.map fun h => h i j) a b‖ ≤ ε₄)
    (h5 : (∫ h, ‖h i j‖ ^ 5 ∂μ) + ∫ h, ‖h i j‖ ^ 5 ∂μ' ≤ m5)
    (hk5 : (∫ h, ‖h i j‖ ^ (5 + k') ∂μ) + ∫ h, ‖h i j‖ ^ (5 + k') ∂μ' ≤ mk)
    (hΓ₀ : 0 ≤ Γ₀) (hM : 0 < M) (hMΓ : 4 * M * (2 * Γ₀) ≤ 1 / 2) :
    ‖(∫ p, ntr (chainB (hybridArr (Cmp_Γ D N (k + 1)) p) (Cmp_l0 Λ z₁ z₂ a b)) ∂(μ.prod μ')) -
        ∫ p, ntr (chainB (hybridArr (Cmp_Γ D N k) p) (Cmp_l0 Λ z₁ z₂ a b)) ∂(μ.prod μ')‖ ≤
      Cmp_Bg D N |z.im|⁻¹ (2 * Γ₀) ε₄ m5 mk M k' + Cmp_Bd D N |z.im|⁻¹ ε₄ m5 mk M k' *
        (μ.prod μ').real (hybridArr (Cmp_Γ D N k) ⁻¹'
          {h | Cmp_EB Λ z Γ₀ h ∧ ‖h i j‖ ≤ M}ᶜ) := by
  have := hμ.prob
  have := hμ'.prob
  obtain ⟨-, -, hle, -⟩ := Cmp_Γ_succ (D := D) (N := N) k hk
  rw [hij] at hle
  set P := μ.prod μ' with hP
  set l₀ := Cmp_l0 Λ z₁ z₂ a b with hl₀
  set u := |z.im|⁻¹ with hu
  have hu0 : 0 ≤ u := inv_nonneg.mpr (abs_nonneg _)
  set G : (Idx D N → Idx D N → ℂ) → ℂ → ℂ := fun b' x =>
    ntr (chainB (setEntry (Cmp_herm b') i j x) l₀) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    (Cmp_meas_loop l₀).comp ((Cmp_meas_setEntry i j).comp
      ((Cmp_meas_herm.comp measurable_fst).prodMk measurable_snd))
  have hGb : ∀ b' x, ‖G b' x‖ ≤ u ^ 2 := fun b' x =>
    Cmp_loop_le Λ hΛ z z₁ z₂ hz hz₁ hz₂ a b _
      (Cmp_setEntry_herm _ (Cmp_herm_isHermitian b') i j x)
  have hGB : ∀ p x, G (Cmp_B k i j p) x = ntr (chainB (setEntry (Cmp_B k i j p) i j x) l₀) := by
    intro p x
    simp only [hGdef, Cmp_herm_of_isHermitian _ (Cmp_B_herm k i j p).1]
  obtain ⟨hind1, hind2⟩ := Cmp_B_indep hμ.indep hμ'.indep k i j hle
  have hev : Measurable (fun h : Idx D N → Idx D N → ℂ => h i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hW1 : Measurable (fun p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => p.1 i j) :=
    hev.comp measurable_fst
  have hW2 : Measurable (fun p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => p.2 i j) :=
    hev.comp measurable_snd
  have hmap1 : P.map (fun p => p.1 i j) = μ.map fun h => h i j := by
    rw [show (fun p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => p.1 i j) =
      (fun h => h i j) ∘ Prod.fst from rfl, ← Measure.map_map hev measurable_fst,
      (measurePreserving_fst (μ := μ) (ν := μ')).map_eq]
  have hmap2 : P.map (fun p => p.2 i j) = μ'.map fun h => h i j := by
    rw [show (fun p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => p.2 i j) =
      (fun h => h i j) ∘ Prod.snd from rfl, ← Measure.map_map hev measurable_snd,
      (measurePreserving_snd (μ := μ) (ν := μ')).map_eq]
  set ρ := μ.map fun h => h i j with hρ
  set ρ' := μ'.map fun h => h i j with hρ'
  have hBm := Cmp_B_meas (D := D) (N := N) k i j
  have hae := Cmp_ae_herm hμ hμ'
  -- the two expectations through the base
  have e1 : ∫ p, ntr (chainB (hybridArr (Cmp_Γ D N (k + 1)) p) l₀) ∂P =
      ∫ p, (∫ x, G (Cmp_B k i j p) x ∂ρ) ∂P := by
    rw [← hmap1, ← Cmp_indep_integral hBm hW1 hind1 G hGm _ hGb]
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hGB, (Cmp_hyb_eq k hk p hp.1 hp.2).1]
    simp only [hij]
  have e2 : ∫ p, ntr (chainB (hybridArr (Cmp_Γ D N k) p) l₀) ∂P =
      ∫ p, (∫ x, G (Cmp_B k i j p) x ∂ρ') ∂P := by
    rw [← hmap2, ← Cmp_indep_integral hBm hW2 hind2 G hGm _ hGb]
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hGB, (Cmp_hyb_eq k hk p hp.1 hp.2).2]
    simp only [hij]
  have hIi : ∀ (ν : Measure ℂ) [IsProbabilityMeasure ν],
      Integrable (fun p => ∫ x, G (Cmp_B k i j p) x ∂ν) P := by
    intro ν _
    have hsm : StronglyMeasurable (fun b' => ∫ x, Function.uncurry G (b', x) ∂ν) :=
      hGm.stronglyMeasurable.integral_prod_right'
    refine Integrable.of_bound (hsm.measurable.comp hBm).aestronglyMeasurable (u ^ 2)
      (Filter.Eventually.of_forall fun p => ?_)
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (integrable_const (u ^ 2)) (Filter.Eventually.of_forall fun x => hGb _ x)).trans ?_
    simp
  rw [e1, e2, ← integral_sub (hIi ρ) (hIi ρ')]
  -- the moments of the two entry laws
  have hρm : ∀ (ν : Measure (Idx D N → Idx D N → ℂ)), LLClass D N Cst θ ν →
      ∀ n : ℕ, Integrable (fun x : ℂ => ‖x‖ ^ n) (ν.map fun h => h i j) := by
    intro ν hν n
    rw [integrable_map_measure (by fun_prop) hev.aemeasurable]
    exact hν.integrable n i j
  have hρint : ∀ (ν : Measure (Idx D N → Idx D N → ℂ)) (n : ℕ),
      ∫ x, ‖x‖ ^ n ∂(ν.map fun h => h i j) = ∫ h, ‖h i j‖ ^ n ∂ν := fun ν n =>
    integral_map hev.aemeasurable (by fun_prop)
  set S := {h : Idx D N → Idx D N → ℂ | Cmp_EB Λ z Γ₀ h ∧ ‖h i j‖ ≤ M} with hS
  have hSm : MeasurableSet S :=
    (Cmp_meas_EB Λ z Γ₀).inter (measurableSet_le hev.norm measurable_const)
  have hbad : MeasurableSet (hybridArr (Cmp_Γ D N k) ⁻¹' Sᶜ) :=
    (Cmp_hyb_meas _) hSm.compl
  -- the pointwise bound
  have hc5 : 0 ≤ 32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * (2 * (2 * Γ₀)) ^ 5 * u ^ 2) := by positivity
  have hc5d : 0 ≤ 32 * (7 ^ 5 * ((D : ℝ) * N)⁻¹ * u ^ 7) := by positivity
  have hMk : 0 < M ^ k' := pow_pos hM k'
  have hpt : ∀ᵐ p ∂P, ‖(∫ x, G (Cmp_B k i j p) x ∂ρ) - ∫ x, G (Cmp_B k i j p) x ∂ρ'‖ ≤
      Cmp_Bg D N u (2 * Γ₀) ε₄ m5 mk M k' +
        (hybridArr (Cmp_Γ D N k) ⁻¹' Sᶜ).indicator
          (fun _ => Cmp_Bd D N u ε₄ m5 mk M k') p := by
    filter_upwards [hae] with p hp
    obtain ⟨hBh, hB0⟩ := Cmp_B_herm k i j p
    have hstep := Cmp_step Λ hΛ z z₁ z₂ hz hz₁ hz₂ a b (Cmp_B k i j p) hBh i j hB0 ρ ρ'
      (hρm μ hμ) (hρm μ' hμ') ε₄ hm3 hm4 (2 * Γ₀) M hM hMΓ k'
    simp only [hGB]
    rw [hρint μ 5, hρint μ' 5, hρint μ (5 + k'), hρint μ' (5 + k')] at hstep
    have hdet : ‖(∫ x, ntr (chainB (setEntry (Cmp_B k i j p) i j x) l₀) ∂ρ) -
        ∫ x, ntr (chainB (setEntry (Cmp_B k i j p) i j x) l₀) ∂ρ'‖ ≤
          Cmp_Bd D N u ε₄ m5 mk M k' := by
      refine hstep.1.trans ?_
      unfold Cmp_Bd
      gcongr
    have hBg0 : 0 ≤ Cmp_Bg D N u (2 * Γ₀) ε₄ m5 mk M k' := by
      have h0 := (norm_nonneg _).trans (hm4 4 0 rfl)
      have h1 : 0 ≤ m5 := le_trans (by positivity) h5
      have h2 : 0 ≤ mk := le_trans (by positivity) hk5
      unfold Cmp_Bg; positivity
    by_cases hgood : hybridArr (Cmp_Γ D N k) p ∈ S
    · rw [Set.indicator_of_notMem (show p ∉ hybridArr (Cmp_Γ D N k) ⁻¹' Sᶜ from fun h => h hgood),
        add_zero]
      obtain ⟨hE, hM'⟩ := hgood
      have hXh := Cmp_hyb_herm (Cmp_Γ D N k) p hp.1 hp.2
      have hB : Cmp_B k i j p = setEntry (hybridArr (Cmp_Γ D N k) p) i j 0 := by
        rw [Cmp_B, Cmp_herm_of_isHermitian _ hXh]
      have hEB : Cmp_EB Λ z (2 * Γ₀) (Cmp_B k i j p) := by
        rw [hB]
        refine Cmp_EB_setEntry Λ hΛ z hz _ hXh i j 0 M Γ₀ (by simp [hM.le]) hM' ?_ hE
        nlinarith
      refine (hstep.2 hEB).trans ?_
      unfold Cmp_Bg
      gcongr
    · rw [Set.indicator_of_mem (show p ∈ hybridArr (Cmp_Γ D N k) ⁻¹' Sᶜ from hgood)]
      linarith
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_ae ((hIi ρ).sub (hIi ρ')).norm
    ((integrable_const _).add ((integrable_const _).indicator hbad)) hpt).trans (le_of_eq ?_)
  rw [integral_add' (integrable_const _) ((integrable_const _).indicator hbad),
    integral_const, integral_indicator_const _ hbad]
  simp [mul_comm]

/-- The Lindeberg replacement over all pairs `p ≤ q`: the difference of `E ⟨E_b G₁ E_a G₂⟩` under
`μ` and `μ'` is at most `(DN)²` times the step bound. -/
private lemma Cmp_telescope {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z z₁ z₂ : ℂ) (hz : z.im ≠ 0) (hz₁ : z₁ = z ∨ z₁ = star z) (hz₂ : z₂ = z ∨ z₂ = star z)
    (a b : Fin D) {Cst : ℕ → ℝ} {θ : ℝ} (μ μ' : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N Cst θ μ) (hμ' : LLClass D N Cst θ μ') (ε₄ m5 mk Γ₀ M Pb : ℝ) (k' : ℕ)
    (hm3 : ∀ p q : Idx D N, toLex p ≤ toLex q → ∀ a b : ℕ, a + b ≤ 3 →
      mixMom (μ.map fun h => h p q) a b = mixMom (μ'.map fun h => h p q) a b)
    (hm4 : ∀ p q : Idx D N, toLex p ≤ toLex q → ∀ a b : ℕ, a + b = 4 →
      ‖mixMom (μ.map fun h => h p q) a b - mixMom (μ'.map fun h => h p q) a b‖ ≤ ε₄)
    (h5 : ∀ p q : Idx D N, (∫ h, ‖h p q‖ ^ 5 ∂μ) + ∫ h, ‖h p q‖ ^ 5 ∂μ' ≤ m5)
    (hk5 : ∀ p q : Idx D N,
      (∫ h, ‖h p q‖ ^ (5 + k') ∂μ) + ∫ h, ‖h p q‖ ^ (5 + k') ∂μ' ≤ mk)
    (hε0 : 0 ≤ ε₄) (hm50 : 0 ≤ m5) (hmk0 : 0 ≤ mk)
    (hΓ₀ : 0 ≤ Γ₀) (hM : 0 < M) (hMΓ : 4 * M * (2 * Γ₀) ≤ 1 / 2) (hPb : 0 ≤ Pb)
    (hbad : ∀ k : ℕ, ∀ p q : Idx D N, (μ.prod μ').real (hybridArr (Cmp_Γ D N k) ⁻¹'
      {h | Cmp_EB Λ z Γ₀ h ∧ ‖h p q‖ ≤ M}ᶜ) ≤ Pb) :
    ‖(∫ h, ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b)) ∂μ) - ∫ h, ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b)) ∂μ'‖ ≤
      ((D : ℝ) * N) ^ 2 * (Cmp_Bg D N |z.im|⁻¹ (2 * Γ₀) ε₄ m5 mk M k' +
        Cmp_Bd D N |z.im|⁻¹ ε₄ m5 mk M k' * Pb) := by
  have := hμ.prob
  have := hμ'.prob
  set l₀ := Cmp_l0 Λ z₁ z₂ a b with hl₀
  set n := (Cmp_UTl D N).length with hn
  set f : ℕ → ℂ := fun k =>
    ∫ p, ntr (chainB (hybridArr (Cmp_Γ D N k) p) l₀) ∂(μ.prod μ') with hf
  have hgm := Cmp_meas_loop (D := D) (N := N) l₀
  have hfn : f n = ∫ h, ntr (chainB h l₀) ∂μ := by
    have e : ∀ p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ),
        hybridArr (Cmp_Γ D N n) p = p.1 := by
      intro p
      funext r s
      have : (r, s) ∈ Cmp_Γ D N n ∨ (s, r) ∈ Cmp_Γ D N n := by
        simp only [Cmp_Γ, hn, List.take_length, Set.mem_ofPred_eq, Cmp_mem_UTl]
        exact le_total _ _
      simp [hybridArr, this]
    simp only [hf, e]
    rw [← (measurePreserving_fst (μ := μ) (ν := μ')).map_eq] 
    rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable,
      (measurePreserving_fst (μ := μ) (ν := μ')).map_eq]
  have hf0 : f 0 = ∫ h, ntr (chainB h l₀) ∂μ' := by
    have e : ∀ p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ),
        hybridArr (Cmp_Γ D N 0) p = p.2 := by
      intro p
      funext r s
      simp [hybridArr, Cmp_Γ]
    simp only [hf, e]
    rw [← (measurePreserving_snd (μ := μ) (ν := μ')).map_eq]
    rw [integral_map measurable_snd.aemeasurable hgm.aestronglyMeasurable,
      (measurePreserving_snd (μ := μ) (ν := μ')).map_eq]
  have hBd0 : 0 ≤ Cmp_Bd D N |z.im|⁻¹ ε₄ m5 mk M k' := by unfold Cmp_Bd; positivity
  have hBg0 : 0 ≤ Cmp_Bg D N |z.im|⁻¹ (2 * Γ₀) ε₄ m5 mk M k' := by unfold Cmp_Bg; positivity
  have hstep : ∀ k ∈ Finset.range n, ‖f (k + 1) - f k‖ ≤
      Cmp_Bg D N |z.im|⁻¹ (2 * Γ₀) ε₄ m5 mk M k' + Cmp_Bd D N |z.im|⁻¹ ε₄ m5 mk M k' * Pb := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨-, -, hle, -⟩ := Cmp_Γ_succ (D := D) (N := N) k hk
    set i := ((Cmp_UTl D N)[k]).1
    set j := ((Cmp_UTl D N)[k]).2
    have hij : (Cmp_UTl D N)[k] = (i, j) := rfl
    have h := Cmp_lind_step Λ hΛ z z₁ z₂ hz hz₁ hz₂ a b μ μ' hμ hμ' k hk i j hij ε₄ m5 mk Γ₀ M k'
      (hm3 i j hle) (hm4 i j hle) (h5 i j) (hk5 i j) hΓ₀ hM hMΓ
    refine h.trans ?_
    gcongr
    exact hbad k i j
  rw [← hfn, ← hf0, ← Finset.sum_range_sub]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Cmp_UTl_length D N) (by positivity)

/-- The bad event of one step has probability at most `(DN)² N^{-D'}` (the anisotropic local law
(2.22) [eq:aniso_local] for every pair of basis vectors) plus the Markov bound for
`|h_{pq}| > M`. -/
private lemma Cmp_bad {D N : ℕ} (ν : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure ν]
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (τ Γ₀ M ε' Dp B : ℝ) (p q : Idx D N)
    (hz : z ∈ specDom τ N) (hzs : star z ∈ specDom τ N)
    (hΓ : ∀ z' : ℂ, (z' = z ∨ z' = star z) → ∀ k m : Idx D N,
      ‖MExt Λ z' k m‖ + (N : ℝ) ^ ε' * psiIso Λ N z' ≤ Γ₀)
    (haniso : ∀ k m : Idx D N, ν {h | ∃ z' ∈ specDom τ N, (N : ℝ) ^ ε' * psiIso Λ N z' <
      ‖star (Pi.single k (1 : ℂ)) ⬝ᵥ ((res (Matrix.of h + Λ) z' - MExt Λ z') *ᵥ
        Pi.single m 1)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-Dp)))
    (Mp : ℕ) (hM : 0 < M) (hint : Integrable (fun h : Idx D N → Idx D N → ℂ => ‖h p q‖ ^ Mp) ν)
    (hmom : ∫ h, ‖h p q‖ ^ Mp ∂ν ≤ B) :
    ν.real {h | Cmp_EB Λ z Γ₀ h ∧ ‖h p q‖ ≤ M}ᶜ ≤
      ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-Dp) + B / M ^ Mp := by
  set Bad : Idx D N → Idx D N → Set (Idx D N → Idx D N → ℂ) := fun k m =>
    {h | ∃ z' ∈ specDom τ N, (N : ℝ) ^ ε' * psiIso Λ N z' <
      ‖star (Pi.single k (1 : ℂ)) ⬝ᵥ ((res (Matrix.of h + Λ) z' - MExt Λ z') *ᵥ
        Pi.single m 1)‖} with hBad
  have hsub : {h | Cmp_EB Λ z Γ₀ h ∧ ‖h p q‖ ≤ M}ᶜ ⊆
      (⋃ k, ⋃ m, Bad k m) ∪ {h | M ^ Mp ≤ ‖h p q‖ ^ Mp} := by
    intro h hh
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
      not_le] at hc
    obtain ⟨hc1, hc2⟩ := hc
    apply hh
    refine ⟨fun k m => ?_, ?_⟩
    · have hgood : ∀ z' ∈ specDom τ N,
          ‖(res (Matrix.of h + Λ) z' - MExt Λ z') k m‖ ≤ (N : ℝ) ^ ε' * psiIso Λ N z' := by
        intro z' hz'
        have := hc1 k m
        simp only [hBad, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at this
        have h' := this z' hz'
        rwa [Cmp_single_form] at h'
      have hb : ∀ z' : ℂ, (z' = z ∨ z' = star z) → z' ∈ specDom τ N →
          ‖res (Matrix.of h + Λ) z' k m‖ ≤ Γ₀ := by
        intro z' hz' hzd
        have e : res (Matrix.of h + Λ) z' k m =
            (res (Matrix.of h + Λ) z' - MExt Λ z') k m + MExt Λ z' k m := by
          simp
        rw [e]
        refine (norm_add_le _ _).trans ?_
        have := hΓ z' hz' k m
        have := hgood z' hzd
        linarith
      exact ⟨hb z (Or.inl rfl) hz, hb (star z) (Or.inr rfl) hzs⟩
    · by_contra hcon
      push Not at hcon
      exact absurd (pow_le_pow_left₀ hM.le hcon.le Mp) (not_le.mpr hc2)
  have hDp : 0 ≤ (N : ℝ) ^ (-Dp) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : ν.real (⋃ k, ⋃ m, Bad k m) ≤ ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-Dp) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    refine (Finset.sum_le_sum fun k _ => measureReal_iUnion_fintype_le _).trans ?_
    have hb : ∀ k m, ν.real (Bad k m) ≤ (N : ℝ) ^ (-Dp) := fun k m =>
      ENNReal.toReal_le_of_le_ofReal hDp (haniso k m)
    refine (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun m _ => hb k m).trans
      (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have h2 : ν.real {h | M ^ Mp ≤ ‖h p q‖ ^ Mp} ≤ B / M ^ Mp := by
    have hMp : 0 < M ^ Mp := pow_pos hM Mp
    rw [le_div_iff₀ hMp, mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun h => by
      positivity) hint (M ^ Mp)).trans hmom
  calc _ ≤ ν.real ((⋃ k, ⋃ m, Bad k m) ∪ {h | M ^ Mp ≤ ‖h p q‖ ^ Mp}) := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add h1 h2)

/-! ### Deterministic inputs on `𝐃(τ)` and the exponent count -/

/-- `|M(z)_{km}| ≤ 5/4` and `|m(z)| < 1` for Hermitian `Λ`, `‖Λ‖ ≤ 1/10`, `Im z ≠ 0`
(from `mSol_apriori` and `M(z̄) = M(z)^*`). -/
private lemma Cmp_MExt_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : z.im ≠ 0) :
    (∀ k m, ‖MExt Λ z k m‖ ≤ 5 / 4) ∧ ‖mExt Λ z‖ < 1 := by
  have hpos : ∀ w : ℂ, 0 < w.im → (∀ k m, ‖MExt Λ w k m‖ ≤ 5 / 4) ∧ ‖mExt Λ w‖ < 1 := by
    intro w hw
    obtain ⟨-, hm, hM⟩ := mSol_apriori Λ hΛ hℓ w hw
    have hm' : mExt Λ w = mSol Λ w := by simp only [mExt, hw, ↓reduceIte]
    have hM' : MExt Λ w = MSol Λ w := by rw [MExt, MSol, hm']
    refine ⟨fun k m => ?_, hm' ▸ hm⟩
    rw [hM']
    have h0 : 0 ≤ opNorm Λ := norm_nonneg _
    have h1 : (1 - 2 * opNorm Λ)⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact (norm_apply_le_opNorm _ k m).trans (hM.le.trans h1)
  rcases lt_or_gt_of_ne hz with h | h
  · have h' : 0 < (star z).im := by simpa using h
    obtain ⟨e1, e2⟩ := mExt_conj Λ hΛ (star z) h'.ne'
    rw [star_star] at e1 e2
    obtain ⟨h1, h2⟩ := hpos (star z) h'
    refine ⟨fun k m => ?_, ?_⟩
    · rw [e2, Matrix.conjTranspose_apply, norm_star]; exact h1 m k
    · rw [e1, norm_star]; exact h2
  · exact hpos z h

/-- The control parameter of (2.22) [eq:aniso_local] is at most `2` when `N|Im z| ≥ 1`. -/
private lemma Cmp_psi_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (N : ℕ) (z : ℂ)
    (hz : z.im ≠ 0) (hNz : 1 ≤ (N : ℝ) * |z.im|) : psiIso Λ N z ≤ 2 := by
  have hm := (Cmp_MExt_le Λ hΛ hℓ z hz).2
  have hpos : 0 < (N : ℝ) * |z.im| := by linarith
  have h1 : |(mExt Λ z).im| / ((N : ℝ) * |z.im|) ≤ 1 := by
    rw [div_le_one hpos]
    exact (Complex.abs_im_le_norm _).trans (hm.le.trans hNz)
  have h2 : Real.sqrt (|(mExt Λ z).im| / ((N : ℝ) * |z.im|)) ≤ 1 :=
    Real.sqrt_le_one.mpr h1
  have h3 : 1 / ((N : ℝ) * |z.im|) ≤ 1 := by rw [div_le_one hpos]; exact hNz
  unfold psiIso
  linarith

set_option maxHeartbeats 1000000 in
/-- The exponent count of (3.38) [eq:cpmparison] in the variables `s = N^{-1/2}`, `e = N^ε`,
`d = N^{-δ}`, `u = |Im z|⁻¹`: the total Lindeberg bound is at most a constant times
`e^5 s² d u² = N^{5ε} N^{-1-δ} η^{-2}`. -/
private lemma Cmp_alg (D N : ℕ) (hD : 1 ≤ D) (s e d u K C5 Ck Cp Pb : ℝ) (k' : ℕ)
    (hs : 0 < s) (hNs : (N : ℝ) * s ^ 2 = 1) (hs1 : s ≤ 1) (hsd : s ≤ d) (hu : 0 < u)
    (hus : u * s ^ 2 ≤ 1) (he : 1 ≤ e) (hek : 1 ≤ s ^ 10 * e ^ k') (hK : 0 ≤ K) (hC5 : 0 ≤ C5)
    (hCk : 0 ≤ Ck) (hCp : 0 ≤ Cp) (hPb0 : 0 ≤ Pb) (hPb : Pb ≤ ((D : ℝ) ^ 2 + Cp) * s ^ 16) :
    (D : ℝ) * (((D : ℝ) * N) ^ 2 * (Cmp_Bg D N u (2 * (4 * e)) (s ^ 4 * (K * d))
      (2 * C5 * s ^ 5) (2 * Ck * s ^ (5 + k')) (s * e) k' +
      Cmp_Bd D N u (s ^ 4 * (K * d)) (2 * C5 * s ^ 5) (2 * Ck * s ^ (5 + k')) (s * e) k' * Pb)) ≤
    (D : ℝ) ^ 2 * (2 ^ 31 * K + 2 ^ 41 * C5 + 2 ^ 21 * Ck +
      ((D : ℝ) ^ 2 + Cp) * (2 ^ 16 * K + 2 ^ 21 * C5 + 2 ^ 21 * Ck)) * e ^ 5 *
        (s ^ 2 * d * u ^ 2) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hN0 : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hNs; simp at hNs
    · exact_mod_cast h
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le hs hsd
  have hek0 : 0 < e ^ k' := pow_pos he0 k'
  have hNe : (N : ℝ) = (s ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hNs
  -- the exact form of the left side
  have hL : (D : ℝ) * (((D : ℝ) * N) ^ 2 * (Cmp_Bg D N u (2 * (4 * e)) (s ^ 4 * (K * d))
      (2 * C5 * s ^ 5) (2 * Ck * s ^ (5 + k')) (s * e) k' +
      Cmp_Bd D N u (s ^ 4 * (K * d)) (2 * C5 * s ^ 5) (2 * Ck * s ^ (5 + k')) (s * e) k' * Pb)) =
      (D : ℝ) ^ 2 * ((25 * 6 ^ 4 * 16 ^ 4) * e ^ 4 * (K * (s ^ 2 * d * u ^ 2)) +
        (64 * 7 ^ 5 * 16 ^ 5) * e ^ 5 * (C5 * (u ^ 2 * s ^ 3)) +
        (64 * 7 ^ 5) * (Ck * (u ^ 7 * s ^ 3 / e ^ k')) +
        Pb * ((25 * 6 ^ 4) * (K * (u ^ 6 * (s ^ 2 * d))) + (64 * 7 ^ 5) * (C5 * (u ^ 7 * s ^ 3)) +
          (64 * 7 ^ 5) * (Ck * (u ^ 7 * s ^ 3 / e ^ k')))) := by
    unfold Cmp_Bg Cmp_Bd
    rw [hNe, pow_add, mul_pow]
    field_simp
    ring
  rw [hL]
  have hs2 : 0 < s ^ 2 := by positivity
  have hus5 : u ^ 5 * s ^ 10 ≤ 1 := by
    have : (u * s ^ 2) ^ 5 ≤ 1 := pow_le_one₀ (by positivity) hus
    calc u ^ 5 * s ^ 10 = (u * s ^ 2) ^ 5 := by ring
      _ ≤ 1 := this
  have hus4 : u ^ 4 * s ^ 8 ≤ 1 := by
    have : (u * s ^ 2) ^ 4 ≤ 1 := pow_le_one₀ (by positivity) hus
    calc u ^ 4 * s ^ 8 = (u * s ^ 2) ^ 4 := by ring
      _ ≤ 1 := this
  have hT : 0 ≤ s ^ 2 * d * u ^ 2 := by positivity
  have hs3 : u ^ 2 * s ^ 3 ≤ s ^ 2 * d * u ^ 2 := by
    have : s ^ 3 ≤ s ^ 2 * d := by
      calc s ^ 3 = s ^ 2 * s := by ring
        _ ≤ s ^ 2 * d := mul_le_mul_of_nonneg_left hsd hs2.le
    nlinarith [sq_nonneg u]
  have hek' : 1 / e ^ k' ≤ s ^ 10 := by
    rw [div_le_iff₀ hek0]; linarith
  have hX3 : u ^ 7 * s ^ 3 / e ^ k' ≤ s ^ 2 * d * u ^ 2 := by
    have h1 : u ^ 7 * s ^ 3 / e ^ k' ≤ u ^ 7 * s ^ 3 * s ^ 10 := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hek' (by positivity)
    have h2 : u ^ 7 * s ^ 3 * s ^ 10 = (u ^ 2 * s ^ 3) * (u ^ 5 * s ^ 10) := by ring
    have h3 : (u ^ 2 * s ^ 3) * (u ^ 5 * s ^ 10) ≤ u ^ 2 * s ^ 3 :=
      mul_le_of_le_one_right (by positivity) hus5
    linarith
  have hDC : 0 ≤ (D : ℝ) ^ 2 + Cp := by positivity
  have hX4 : Pb * (u ^ 6 * (s ^ 2 * d)) ≤ ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2) := by
    have h1 : Pb * (u ^ 6 * (s ^ 2 * d)) ≤ ((D : ℝ) ^ 2 + Cp) * s ^ 16 * (u ^ 6 * (s ^ 2 * d)) :=
      mul_le_mul_of_nonneg_right hPb (by positivity)
    have h2 : s ^ 16 * u ^ 6 = u ^ 2 * (u ^ 4 * s ^ 8) * s ^ 8 := by ring
    have h3 : u ^ 2 * (u ^ 4 * s ^ 8) * s ^ 8 ≤ u ^ 2 := by
      have : s ^ 8 ≤ 1 := pow_le_one₀ hs.le hs1
      have : u ^ 4 * s ^ 8 * s ^ 8 ≤ 1 := by nlinarith [pow_pos hs 8, pow_pos hu 4]
      nlinarith [sq_nonneg u]
    have h4 : ((D : ℝ) ^ 2 + Cp) * s ^ 16 * (u ^ 6 * (s ^ 2 * d)) =
        ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d) * (s ^ 16 * u ^ 6) := by ring
    have h5 : ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d) * (s ^ 16 * u ^ 6) ≤
        ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d) * u ^ 2 := by
      rw [h2]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have hX5 : Pb * (u ^ 7 * s ^ 3) ≤ ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2) := by
    have h1 : Pb * (u ^ 7 * s ^ 3) ≤ ((D : ℝ) ^ 2 + Cp) * s ^ 16 * (u ^ 7 * s ^ 3) :=
      mul_le_mul_of_nonneg_right hPb (by positivity)
    have h2 : s ^ 16 * (u ^ 7 * s ^ 3) = (u ^ 2 * s ^ 3) * (u ^ 5 * s ^ 10) * s ^ 6 := by ring
    have h3 : (u ^ 2 * s ^ 3) * (u ^ 5 * s ^ 10) * s ^ 6 ≤ u ^ 2 * s ^ 3 := by
      have : s ^ 6 ≤ 1 := pow_le_one₀ hs.le hs1
      have h' : (u ^ 5 * s ^ 10) * s ^ 6 ≤ 1 := by
        nlinarith [pow_pos hs 6, pow_pos hu 5, pow_pos hs 10]
      calc (u ^ 2 * s ^ 3) * (u ^ 5 * s ^ 10) * s ^ 6 =
          (u ^ 2 * s ^ 3) * ((u ^ 5 * s ^ 10) * s ^ 6) := by ring
        _ ≤ u ^ 2 * s ^ 3 := mul_le_of_le_one_right (by positivity) h'
    have h4 : ((D : ℝ) ^ 2 + Cp) * s ^ 16 * (u ^ 7 * s ^ 3) ≤
        ((D : ℝ) ^ 2 + Cp) * (u ^ 2 * s ^ 3) := by
      rw [mul_assoc, h2]; exact mul_le_mul_of_nonneg_left h3 hDC
    have h5 : ((D : ℝ) ^ 2 + Cp) * (u ^ 2 * s ^ 3) ≤ ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2) :=
      mul_le_mul_of_nonneg_left hs3 hDC
    exact h1.trans (h4.trans h5)
  have hX6 : Pb * (u ^ 7 * s ^ 3 / e ^ k') ≤ ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2) := by
    have h1 : u ^ 7 * s ^ 3 / e ^ k' ≤ u ^ 7 * s ^ 3 := by
      rw [div_le_iff₀ hek0]
      have : 1 ≤ e ^ k' := one_le_pow₀ he
      exact le_mul_of_one_le_right (by positivity) this
    exact (mul_le_mul_of_nonneg_left h1 hPb0).trans hX5
  have he4 : e ^ 4 ≤ e ^ 5 := pow_le_pow_right₀ he (by norm_num)
  have he5 : 1 ≤ e ^ 5 := one_le_pow₀ he
  -- assemble
  have t1 : (25 * 6 ^ 4 * 16 ^ 4 : ℝ) * e ^ 4 * (K * (s ^ 2 * d * u ^ 2)) ≤
      2 ^ 31 * K * e ^ 5 * (s ^ 2 * d * u ^ 2) := by
    have : (25 * 6 ^ 4 * 16 ^ 4 : ℝ) ≤ 2 ^ 31 := by norm_num
    have hKT : 0 ≤ K * (s ^ 2 * d * u ^ 2) := mul_nonneg hK hT
    calc (25 * 6 ^ 4 * 16 ^ 4 : ℝ) * e ^ 4 * (K * (s ^ 2 * d * u ^ 2))
        ≤ 2 ^ 31 * e ^ 5 * (K * (s ^ 2 * d * u ^ 2)) := by gcongr
      _ = _ := by ring
  have t2 : (64 * 7 ^ 5 * 16 ^ 5 : ℝ) * e ^ 5 * (C5 * (u ^ 2 * s ^ 3)) ≤
      2 ^ 41 * C5 * e ^ 5 * (s ^ 2 * d * u ^ 2) := by
    have : (64 * 7 ^ 5 * 16 ^ 5 : ℝ) ≤ 2 ^ 41 := by norm_num
    calc (64 * 7 ^ 5 * 16 ^ 5 : ℝ) * e ^ 5 * (C5 * (u ^ 2 * s ^ 3))
        ≤ 2 ^ 41 * e ^ 5 * (C5 * (s ^ 2 * d * u ^ 2)) := by gcongr
      _ = _ := by ring
  have t3 : (64 * 7 ^ 5 : ℝ) * (Ck * (u ^ 7 * s ^ 3 / e ^ k')) ≤
      2 ^ 21 * Ck * e ^ 5 * (s ^ 2 * d * u ^ 2) := by
    have : (64 * 7 ^ 5 : ℝ) ≤ 2 ^ 21 := by norm_num
    calc (64 * 7 ^ 5 : ℝ) * (Ck * (u ^ 7 * s ^ 3 / e ^ k'))
        ≤ 2 ^ 21 * (Ck * (s ^ 2 * d * u ^ 2)) := by gcongr
      _ ≤ 2 ^ 21 * (Ck * (s ^ 2 * d * u ^ 2)) * e ^ 5 :=
          le_mul_of_one_le_right (by positivity) he5
      _ = _ := by ring
  have t4 : Pb * ((25 * 6 ^ 4) * (K * (u ^ 6 * (s ^ 2 * d))) +
      (64 * 7 ^ 5) * (C5 * (u ^ 7 * s ^ 3)) +
      (64 * 7 ^ 5) * (Ck * (u ^ 7 * s ^ 3 / e ^ k'))) ≤
      ((D : ℝ) ^ 2 + Cp) * (2 ^ 16 * K + 2 ^ 21 * C5 + 2 ^ 21 * Ck) * e ^ 5 *
        (s ^ 2 * d * u ^ 2) := by
    have a1 : (25 * 6 ^ 4 : ℝ) ≤ 2 ^ 16 := by norm_num
    have a2 : (64 * 7 ^ 5 : ℝ) ≤ 2 ^ 21 := by norm_num
    have e1 : Pb * ((25 * 6 ^ 4) * (K * (u ^ 6 * (s ^ 2 * d))) +
        (64 * 7 ^ 5) * (C5 * (u ^ 7 * s ^ 3)) +
        (64 * 7 ^ 5) * (Ck * (u ^ 7 * s ^ 3 / e ^ k'))) =
        (25 * 6 ^ 4) * K * (Pb * (u ^ 6 * (s ^ 2 * d))) +
          (64 * 7 ^ 5) * C5 * (Pb * (u ^ 7 * s ^ 3)) +
          (64 * 7 ^ 5) * Ck * (Pb * (u ^ 7 * s ^ 3 / e ^ k')) := by ring
    rw [e1]
    have hW : 0 ≤ ((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2) := mul_nonneg hDC hT
    have b1 : (25 * 6 ^ 4) * K * (Pb * (u ^ 6 * (s ^ 2 * d))) ≤
        2 ^ 16 * K * (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) := by
      gcongr
    have b2 : (64 * 7 ^ 5) * C5 * (Pb * (u ^ 7 * s ^ 3)) ≤
        2 ^ 21 * C5 * (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) := by
      gcongr
    have b3 : (64 * 7 ^ 5) * Ck * (Pb * (u ^ 7 * s ^ 3 / e ^ k')) ≤
        2 ^ 21 * Ck * (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) := by
      gcongr
    have hsum : 0 ≤ (2 ^ 16 * K + 2 ^ 21 * C5 + 2 ^ 21 * Ck) *
        (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) := by positivity
    calc _ ≤ 2 ^ 16 * K * (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) +
          2 ^ 21 * C5 * (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) +
          2 ^ 21 * Ck * (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) := by linarith
      _ = (2 ^ 16 * K + 2 ^ 21 * C5 + 2 ^ 21 * Ck) *
          (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) := by ring
      _ ≤ (2 ^ 16 * K + 2 ^ 21 * C5 + 2 ^ 21 * Ck) *
          (((D : ℝ) ^ 2 + Cp) * (s ^ 2 * d * u ^ 2)) * e ^ 5 :=
          le_mul_of_one_le_right hsum he5
      _ = _ := by ring
  have hD2 : 0 ≤ (D : ℝ) ^ 2 := by positivity
  calc _ ≤ (D : ℝ) ^ 2 * (2 ^ 31 * K * e ^ 5 * (s ^ 2 * d * u ^ 2) +
        2 ^ 41 * C5 * e ^ 5 * (s ^ 2 * d * u ^ 2) + 2 ^ 21 * Ck * e ^ 5 * (s ^ 2 * d * u ^ 2) +
        ((D : ℝ) ^ 2 + Cp) * (2 ^ 16 * K + 2 ^ 21 * C5 + 2 ^ 21 * Ck) * e ^ 5 *
          (s ^ 2 * d * u ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hD2
        linarith
    _ = _ := by ring

/-- Class membership is monotone in the moment constants. -/
private lemma Cmp_class_mono {D N : ℕ} {C C' : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (h : LLClass D N C θ μ) (hC : ∀ k, C k ≤ C' k) :
    LLClass D N C' θ μ :=
  ⟨h.prob, h.herm, h.indep, h.integrable, h.mean, h.var, h.pseudo, fun k i j =>
    (h.moments k i j).trans
      (mul_le_mul_of_nonneg_right (hC k) (Real.rpow_nonneg (Nat.cast_nonneg N) _))⟩

/-- `(N^{-1/2})^n = N^{-n/2}`. -/
private lemma Cmp_s_pow (N : ℕ) (n : ℕ) :
    ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ n = (N : ℝ) ^ (-((n : ℝ) / 2)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

/-- `(N^ε)^n = N^{εn}`. -/
private lemma Cmp_e_pow (N : ℕ) (ε : ℝ) (n : ℕ) : ((N : ℝ) ^ ε) ^ n = (N : ℝ) ^ (ε * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]

set_option maxHeartbeats 1000000 in
/-- Lemma 3.13 [main_lemma_com] for the laws of `H_t` of (4.1) [defVt], `t ∈ [0, 1]`: if the
scaled entry laws match to order 3, (3.36) [comH0], and to order 4 up to `K N^{-δ}`, (3.37)
[comH], then `|E L_{ab} - E L̃_{ab}| ≤ N^{τ'} N^{-1-δ} η^{-2}` for `z ∈ 𝐃(τ)`,
`z₁, z₂ ∈ {z, z̄}`; at `t = 0` this is Lemma 3.13 [main_lemma_com]. -/
theorem main_lemma_com_theta (D : ℕ) (hD : 1 ≤ D) (δA τ δ K : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (C C' : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (L' : EntryLaws C'),
      (∀ a b : ℕ, a + b ≤ 3 → mixMom L.νo a b = mixMom L'.νo a b) →
      (∀ a b : ℕ, a + b = 4 → ‖mixMom L.νo a b - mixMom L'.νo a b‖ ≤ K * (N : ℝ) ^ (-δ)) →
      (∀ a : ℕ, a ≤ 3 → ∫ x, x ^ a ∂(L.νd : Measure ℝ) = ∫ x, x ^ a ∂(L'.νd : Measure ℝ)) →
      |(∫ x, x ^ 4 ∂(L.νd : Measure ℝ)) - ∫ x, x ^ 4 ∂(L'.νd : Measure ℝ)| ≤
        K * (N : ℝ) ^ (-δ) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ a b : Fin D,
        ‖ELmat (ouMatLaw D N L t) (lam D N A) z₁ z₂ a b -
            ELmat (ouMatLaw D N L' t) (lam D N A) z₁ z₂ a b‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-1 - δ) * (z.im ^ 2)⁻¹) := by
  intro τ' hτ'
  obtain ⟨C₁, hC₁⟩ := llClass_ouLaw D C
  obtain ⟨C₂, hC₂⟩ := llClass_ouLaw D C'
  set Cst : ℕ → ℝ := fun k => max (max (C₁ k) (C₂ k)) 0 with hCst
  have hCst0 : ∀ k, 0 ≤ Cst k := fun k => le_max_right _ _
  set ε : ℝ := min (τ' / 10) (1 / 8) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ τ' / 10 := min_le_left _ _
  have hε2 : ε ≤ 1 / 8 := min_le_right _ _
  set k' : ℕ := ⌈5 / ε⌉₊ with hk'
  set Mp : ℕ := ⌈10 / ε⌉₊ with hMp
  have hk'ε : 5 ≤ ε * k' := by
    have := Nat.le_ceil (5 / ε)
    rw [div_le_iff₀ hε0] at this
    linarith
  have hMpε : 10 ≤ ε * Mp := by
    have := Nat.le_ceil (10 / ε)
    rw [div_le_iff₀ hε0] at this
    linarith
  obtain ⟨N₁, hN₁⟩ := aniso_local D hD δA τ hδA hτ Cst ε hε0 10 (by norm_num)
  set Const : ℝ := (D : ℝ) ^ 2 * (2 ^ 31 * |K| + 2 ^ 41 * Cst 5 + 2 ^ 21 * Cst (5 + k') +
      ((D : ℝ) ^ 2 + Cst Mp) * (2 ^ 16 * |K| + 2 ^ 21 * Cst 5 + 2 ^ 21 * Cst (5 + k')))
    with hConst
  have hConst0 : 0 ≤ Const := by positivity
  refine ⟨max (max N₁ (2 ^ 24)) (max ⌈(20 : ℝ) ^ (1 / δA)⌉₊ ⌈Const ^ (2 / τ')⌉₊), ?_⟩
  intro N hN L L' h3o h4o h3d h4d t ht0 ht1 A hA z hz z₁ z₂ hz₁ hz₂ a b
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN24 : 2 ^ 24 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNA : ⌈(20 : ℝ) ^ (1 / δA)⌉₊ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNC : ⌈Const ^ (2 / τ')⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (by norm_num) hN24
  have hN0 : (0 : ℝ) < N := by linarith
  have hNnat : 1 ≤ N := le_trans (by norm_num) hN24
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hNnat⟩)⟩
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  have hℓ : opNorm Λ ≤ 1 / 10 := by
    have h1 := opNorm_lam_le D N A
    have h20 : (20 : ℝ) ≤ (N : ℝ) ^ δA := by
      have hc : (20 : ℝ) ^ (1 / δA) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNA)
      have := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hc hδA.le
      rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδA.ne', Real.rpow_one] at this
    have h2 : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
      rw [Real.rpow_neg hN0.le]
      rw [inv_le_comm₀ (Real.rpow_pos_of_pos hN0 _) (by norm_num)]
      linarith
    linarith
  -- the spectral domain
  obtain ⟨hz1, hz2⟩ := hz
  have hNτ0 : 0 < (N : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hN0 _
  have hzim0 : 0 < |z.im| := lt_of_lt_of_le hNτ0 hz2
  have hzim : z.im ≠ 0 := abs_pos.mp hzim0
  have hNτ : 1 ≤ (N : ℝ) * |z.im| := by
    have e : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [← Real.rpow_one_add' hN0.le (by linarith)]
      congr 1; ring
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
    calc (1 : ℝ) ≤ (N : ℝ) * (N : ℝ) ^ (-1 + τ) := by rw [e]; exact h1
      _ ≤ (N : ℝ) * |z.im| := mul_le_mul_of_nonneg_left hz2 hN0.le
  have hzs : star z ∈ specDom τ N := ⟨by simpa using hz1, by simpa using hz2⟩
  -- the variables of the exponent count
  set s : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hsdef
  set e : ℝ := (N : ℝ) ^ ε with hedef
  set d : ℝ := (N : ℝ) ^ (-δ) with hddef
  set u : ℝ := |z.im|⁻¹ with hudef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN0 _
  have hs1 : s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hs2 : s ^ 2 = (N : ℝ)⁻¹ := by
    rw [hsdef, Cmp_s_pow]
    norm_num
    exact Real.rpow_neg_one _
  have hNs : (N : ℝ) * s ^ 2 = 1 := by rw [hs2]; field_simp
  have hsd : s ≤ d := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hu0 : 0 < u := inv_pos.mpr hzim0
  have hus : u * s ^ 2 ≤ 1 := by
    rw [hs2, hudef, ← mul_inv]
    exact inv_le_one_of_one_le₀ (by linarith)
  have he1 : 1 ≤ e := Real.one_le_rpow hN1 hε0.le
  have he0 : 0 < e := by linarith
  have hs10 : s ^ 10 = (N : ℝ) ^ (-(5 : ℝ)) := by rw [hsdef, Cmp_s_pow]; norm_num
  have hs20 : s ^ 20 = (N : ℝ) ^ (-(10 : ℝ)) := by rw [hsdef, Cmp_s_pow]; norm_num
  have hek : 1 ≤ s ^ 10 * e ^ k' := by
    rw [hs10, hedef, Cmp_e_pow, ← Real.rpow_add hN0]
    exact Real.one_le_rpow hN1 (by linarith)
  have heM : 1 ≤ s ^ 20 * e ^ Mp := by
    rw [hs20, hedef, Cmp_e_pow, ← Real.rpow_add hN0]
    exact Real.one_le_rpow hN1 (by linarith)
  have hMΓ : 4 * (s * e) * (2 * (4 * e)) ≤ 1 / 2 := by
    have he8 : e ^ 8 ≤ N := by
      rw [hedef, Cmp_e_pow]
      calc (N : ℝ) ^ (ε * (8 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
        _ = N := Real.rpow_one _
    have hN24' : (2 : ℝ) ^ 24 ≤ N := by exact_mod_cast hN24
    have h4 : (s * e ^ 2) ^ 4 ≤ (1 / 64) ^ 4 := by
      have : (s * e ^ 2) ^ 4 = (s ^ 2) ^ 2 * e ^ 8 := by ring
      rw [this, hs2]
      calc ((N : ℝ)⁻¹) ^ 2 * e ^ 8 ≤ ((N : ℝ)⁻¹) ^ 2 * N :=
            mul_le_mul_of_nonneg_left he8 (by positivity)
        _ = (N : ℝ)⁻¹ := by field_simp
        _ ≤ ((2 : ℝ) ^ 24)⁻¹ := inv_anti₀ (by positivity) hN24'
        _ = (1 / 64) ^ 4 := by norm_num
    have h1 : s * e ^ 2 ≤ 1 / 64 :=
      (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp h4
    nlinarith
  have hM0 : 0 < s * e := mul_pos hs0 he0
  -- the two laws and their class
  set θ : ℝ := Real.exp (-t) with hθ
  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hθ1 : θ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  set μ := ouMatLaw D N L t with hμdef
  set μ' := ouMatLaw D N L' t with hμ'def
  have hμ : LLClass D N Cst θ μ :=
    Cmp_class_mono (hC₁ N L t ht0) fun k => (le_max_left _ _).trans (le_max_left _ _)
  have hμ' : LLClass D N Cst θ μ' :=
    Cmp_class_mono (hC₂ N L' t ht0) fun k => (le_max_right _ _).trans (le_max_left _ _)
  have := hμ.prob
  have := hμ'.prob
  have hmomb : ∀ ν : Measure (Idx D N → Idx D N → ℂ), LLClass D N Cst θ ν →
      ∀ (n : ℕ) (p q : Idx D N), ∫ h, ‖h p q‖ ^ n ∂ν ≤ Cst n * s ^ n := by
    intro ν hν n p q
    rw [hsdef, Cmp_s_pow]
    exact hν.moments n p q
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (h4o 4 0 rfl)
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos hN0 _)
  -- the bad events
  set Pb : ℝ := ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(10 : ℝ)) + Cst Mp * s ^ Mp / (s * e) ^ Mp
    with hPbdef
  have hPb0 : 0 ≤ Pb := by positivity
  have hΓ : ∀ z' : ℂ, (z' = z ∨ z' = star z) → ∀ k m : Idx D N,
      ‖MExt Λ z' k m‖ + (N : ℝ) ^ ε * psiIso Λ N z' ≤ 4 * e := by
    intro z' hz' k m
    have hz'im : z'.im ≠ 0 ∧ |z'.im| = |z.im| := by
      rcases hz' with rfl | rfl
      · exact ⟨hzim, rfl⟩
      · simp [hzim]
    have h1 := (Cmp_MExt_le Λ hΛ hℓ z' hz'im.1).1 k m
    have h2 := Cmp_psi_le Λ hΛ hℓ N z' hz'im.1 (by rw [hz'im.2]; exact hNτ)
    have h3 : (N : ℝ) ^ ε * psiIso Λ N z' ≤ e * 2 := mul_le_mul_of_nonneg_left h2 he0.le
    linarith
  have hbad : ∀ k : ℕ, ∀ p q : Idx D N, (μ.prod μ').real (hybridArr (Cmp_Γ D N k) ⁻¹'
      {h | Cmp_EB Λ z (4 * e) h ∧ ‖h p q‖ ≤ s * e}ᶜ) ≤ Pb := by
    intro k p q
    set ν := (μ.prod μ').map (hybridArr (Cmp_Γ D N k)) with hνdef
    have hν : LLClass D N Cst θ ν := llClass_hybrid D N Cst θ μ μ' hμ hμ' _
    have := hν.prob
    have hev : Measurable (fun h : Idx D N → Idx D N → ℂ => h p q) :=
      (measurable_pi_apply q).comp (measurable_pi_apply p)
    have hSm : MeasurableSet {h : Idx D N → Idx D N → ℂ | Cmp_EB Λ z (4 * e) h ∧ ‖h p q‖ ≤ s * e} :=
      (Cmp_meas_EB Λ z (4 * e)).inter (measurableSet_le hev.norm measurable_const)
    have e1 : (μ.prod μ').real (hybridArr (Cmp_Γ D N k) ⁻¹'
        {h | Cmp_EB Λ z (4 * e) h ∧ ‖h p q‖ ≤ s * e}ᶜ) =
        ν.real {h | Cmp_EB Λ z (4 * e) h ∧ ‖h p q‖ ≤ s * e}ᶜ := by
      simp only [Measure.real, hνdef, Measure.map_apply (Cmp_hyb_meas _) hSm.compl]
    rw [e1]
    exact Cmp_bad ν Λ z τ (4 * e) (s * e) ε 10 (Cst Mp * s ^ Mp) p q ⟨hz1, hz2⟩ hzs hΓ
      (fun k m => hN₁ N hN₁' θ hθ0 hθ1 ν hν A hA (Pi.single k 1) (Pi.single m 1)
        (Cmp_single_norm k) (Cmp_single_norm m)) Mp hM0 (hν.integrable Mp p q)
      (hmomb ν hν Mp p q)
  have hPb : Pb ≤ ((D : ℝ) ^ 2 + Cst Mp) * s ^ 16 := by
    have h1 : ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(10 : ℝ)) = (D : ℝ) ^ 2 * s ^ 16 := by
      rw [← hs20]
      have : ((D : ℝ) * N) ^ 2 * s ^ 20 = (D : ℝ) ^ 2 * s ^ 16 * ((N : ℝ) * s ^ 2) ^ 2 := by ring
      rw [this, hNs]; ring
    have h2 : Cst Mp * s ^ Mp / (s * e) ^ Mp ≤ Cst Mp * s ^ 16 := by
      have hsM : 0 < s ^ Mp := pow_pos hs0 Mp
      have heMp : 0 < e ^ Mp := pow_pos he0 Mp
      have hq : Cst Mp * s ^ Mp / (s * e) ^ Mp = Cst Mp / e ^ Mp := by
        rw [mul_pow]; field_simp
      rw [hq, div_le_iff₀ heMp]
      have h16 : s ^ 20 ≤ s ^ 16 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
      calc Cst Mp ≤ Cst Mp * (s ^ 20 * e ^ Mp) := le_mul_of_one_le_right (hCst0 _) heM
        _ ≤ Cst Mp * (s ^ 16 * e ^ Mp) := by gcongr
        _ = _ := by ring
    rw [hPbdef, h1]
    linarith
  -- the expectation of `L_{ab}` through the loop
  have hE : ∀ ν : Measure (Idx D N → Idx D N → ℂ), ELmat ν Λ z₁ z₂ a b =
      (D : ℂ) * ∫ h, ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b)) ∂ν := by
    intro ν
    simp only [ELmat, Matrix.of_apply, Cmp_Lmat_eq]
    exact integral_const_mul _ _
  rw [hE, hE, ← mul_sub, norm_mul, Complex.norm_natCast]
  have htel := Cmp_telescope Λ hΛ z z₁ z₂ hzim hz₁ hz₂ a b μ μ' hμ hμ' (s ^ 4 * (K * d))
    (2 * Cst 5 * s ^ 5) (2 * Cst (5 + k') * s ^ (5 + k')) (4 * e) (s * e) Pb k'
    (fun p q hpq => (Cmp_entry_cmp D N L L' (K * d) h3o h4o h3d h4d t ht0 p q hpq).1)
    (fun p q hpq => (Cmp_entry_cmp D N L L' (K * d) h3o h4o h3d h4d t ht0 p q hpq).2)
    (fun p q => by have h1 := hmomb μ hμ 5 p q; have h2 := hmomb μ' hμ' 5 p q; linarith)
    (fun p q => by
      have h1 := hmomb μ hμ (5 + k') p q; have h2 := hmomb μ' hμ' (5 + k') p q; linarith)
    (by positivity) (by have := hCst0 5; positivity) (by have := hCst0 (5 + k'); positivity)
    (by positivity) hM0 hMΓ hPb0 hbad
  have halg := Cmp_alg D N hD s e d u K (Cst 5) (Cst (5 + k')) (Cst Mp) Pb k' hs0 hNs hs1 hsd hu0
    hus he1 hek hK (hCst0 _) (hCst0 _) (hCst0 _) hPb0 hPb
  have hT : 0 ≤ s ^ 2 * d * u ^ 2 := by positivity
  have hConst' : (D : ℝ) ^ 2 * (2 ^ 31 * K + 2 ^ 41 * Cst 5 + 2 ^ 21 * Cst (5 + k') +
      ((D : ℝ) ^ 2 + Cst Mp) * (2 ^ 16 * K + 2 ^ 21 * Cst 5 + 2 ^ 21 * Cst (5 + k'))) ≤ Const := by
    rw [hConst, abs_of_nonneg hK]
  have hCN : Const ≤ (N : ℝ) ^ (τ' / 2) := by
    have hc : Const ^ (2 / τ') ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNC)
    have := Real.rpow_le_rpow (Real.rpow_nonneg hConst0 _) hc (by positivity : 0 ≤ τ' / 2)
    rwa [← Real.rpow_mul hConst0, show 2 / τ' * (τ' / 2) = 1 by field_simp, Real.rpow_one]
      at this
  have he5 : e ^ 5 ≤ (N : ℝ) ^ (τ' / 2) := by
    rw [hedef, Cmp_e_pow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hT' : s ^ 2 * d * u ^ 2 = (N : ℝ) ^ (-1 - δ) * (z.im ^ 2)⁻¹ := by
    rw [hs2, hddef, hudef, sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_neg_one, inv_pow,
      sq_abs]
  have hNτ' : (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) = (N : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  calc (D : ℝ) * ‖(∫ h, ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b)) ∂μ) -
        ∫ h, ntr (chainB h (Cmp_l0 Λ z₁ z₂ a b)) ∂μ'‖
      ≤ (D : ℝ) * (((D : ℝ) * N) ^ 2 * (Cmp_Bg D N |z.im|⁻¹ (2 * (4 * e)) (s ^ 4 * (K * d))
          (2 * Cst 5 * s ^ 5) (2 * Cst (5 + k') * s ^ (5 + k')) (s * e) k' +
        Cmp_Bd D N |z.im|⁻¹ (s ^ 4 * (K * d)) (2 * Cst 5 * s ^ 5) (2 * Cst (5 + k') * s ^ (5 + k'))
          (s * e) k' * Pb)) := mul_le_mul_of_nonneg_left htel (Nat.cast_nonneg _)
    _ ≤ _ := halg
    _ ≤ Const * e ^ 5 * (s ^ 2 * d * u ^ 2) := by gcongr
    _ ≤ (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) * (s ^ 2 * d * u ^ 2) := by gcongr
    _ = _ := by rw [hNτ', hT']

end RBMTransitionEdge

end
