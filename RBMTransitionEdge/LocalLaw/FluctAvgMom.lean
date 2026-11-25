module

public import RBMTransitionEdge.LocalLaw.FluctAvgQ
public import RBMTransitionEdge.LocalLaw.ExpansionHP

@[expose] public section

/-!
# The averaged moment inequality

The order-`k` terms of the expansion of `E|⟨B H̲G⟩|^{2p}` for (2.30) [eq:HGline] in the class
through Lemma 2.11 [lem:complex_cumu] with a high-probability remainder: the exact cancellation
of `E ⟨B S_θ(G) G⟩ f` at order one, the higher orders, and the averaged moment inequality, with
the bound on `Q` entering through the good event.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The order-`k` part of the averaged expansion: with `f = (G B)_{ji} ⟨B H̲G⟩^{p-1}
conj⟨B H̲G⟩^p`, `(DN)⁻¹ Σ_{i,j} Σ_{a ≤ k} 𝒞^{(a, k-a+1)}(h_{ji}) E ∂_w^a ∂_{w̄}^{k-a} f /
(a! (k-a)!)`, the terms of Lemma 2.11 [lem:complex_cumu] for
`⟨B H G⟩ = (DN)⁻¹ Σ h_{ij} (G B)_{ji}`. -/
def avgTerm (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (p k : ℕ) : ℂ :=
  ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
    ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
      ∫ h, wirt a (k - a) (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z * B) j i *
        ntr (B * hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z) ^ (p - 1) *
        starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z)) ^ p)
        (h j i) ∂μ

/-! ### Wirtinger calculus for smooth functions of one complex variable -/

/-- Smooth (real sense, every finite order) functions `ℂ → ℂ`, such as the slices
`w ↦ F(setEntry h i j w)` of Lemma 2.11 [lem:complex_cumu]. -/
private def AM_Sm (f : ℂ → ℂ) : Prop := ∀ n : ℕ, ContDiff ℝ n f

/-- A smooth function is real-differentiable. -/
private lemma AM_Sm.diff {f : ℂ → ℂ} (hf : AM_Sm f) : Differentiable ℝ f :=
  (hf 1).differentiable (by norm_num)

/-- `z ↦ f'(z) v` is smooth for smooth `f`. -/
private lemma AM_sm_fderiv_apply {f : ℂ → ℂ} (hf : AM_Sm f) (v : ℂ) :
    AM_Sm (fun z => fderiv ℝ f z v) := fun n =>
  ((hf (n + 1)).fderiv_right (by norm_cast)).clm_apply contDiff_const

/-- Constants are smooth. -/
private lemma AM_sm_const (c : ℂ) : AM_Sm (fun _ => c) := fun _ => contDiff_const

/-- Sums of smooth functions are smooth. -/
private lemma AM_sm_add {f g : ℂ → ℂ} (hf : AM_Sm f) (hg : AM_Sm g) :
    AM_Sm (fun z => f z + g z) := fun n => (hf n).add (hg n)

/-- Products of smooth functions are smooth. -/
private lemma AM_sm_mul {f g : ℂ → ℂ} (hf : AM_Sm f) (hg : AM_Sm g) :
    AM_Sm (fun z => f z * g z) := fun n => (hf n).mul (hg n)

/-- Constant multiples of smooth functions are smooth. -/
private lemma AM_sm_cmul (c : ℂ) {f : ℂ → ℂ} (hf : AM_Sm f) : AM_Sm (fun z => c * f z) :=
  AM_sm_mul (AM_sm_const c) hf

/-- Powers of smooth functions are smooth. -/
private lemma AM_sm_pow {f : ℂ → ℂ} (hf : AM_Sm f) (m : ℕ) : AM_Sm (fun z => f z ^ m) :=
  fun n => (hf n).pow m

/-- The complex conjugate of a smooth function is smooth. -/
private lemma AM_sm_conj {f : ℂ → ℂ} (hf : AM_Sm f) : AM_Sm (fun z => starRingEnd ℂ (f z)) :=
  fun n => Complex.conjCLE.contDiff.comp (hf n)

/-- `∂_w f` is smooth for smooth `f`. -/
private lemma AM_sm_dW {f : ℂ → ℂ} (hf : AM_Sm f) : AM_Sm (dW f) := fun n => by
  unfold dW
  exact ((AM_sm_fderiv_apply hf 1 n).sub
    (contDiff_const.mul (AM_sm_fderiv_apply hf Complex.I n))).div_const 2

/-- `∂_{w̄} f` is smooth for smooth `f`. -/
private lemma AM_sm_dWbar {f : ℂ → ℂ} (hf : AM_Sm f) : AM_Sm (dWbar f) := fun n => by
  unfold dWbar
  exact ((AM_sm_fderiv_apply hf 1 n).add
    (contDiff_const.mul (AM_sm_fderiv_apply hf Complex.I n))).div_const 2

/-- The operators `∂_w`, `∂_{w̄}` act on smooth functions as derivations. -/
private structure AM_Der (d : (ℂ → ℂ) → ℂ → ℂ) : Prop where
  sm : ∀ f, AM_Sm f → AM_Sm (d f)
  mul : ∀ f g, AM_Sm f → AM_Sm g → d (fun x => f x * g x) = fun x => d f x * g x + f x * d g x
  sum : ∀ (s : Finset ℕ) (F : ℕ → ℂ → ℂ), (∀ m, AM_Sm (F m)) →
    d (fun x => ∑ m ∈ s, F m x) = fun x => ∑ m ∈ s, d (F m) x
  cmul : ∀ (c : ℂ) f, AM_Sm f → d (fun x => c * f x) = fun x => c * d f x
  add : ∀ f g, AM_Sm f → AM_Sm g → d (fun x => f x + g x) = fun x => d f x + d g x
  const : ∀ c : ℂ, d (fun _ => c) = fun _ => 0

/-- `∂_w` is a derivation on smooth functions. -/
private lemma AM_der_dW : AM_Der dW where
  sm := fun _ hf => AM_sm_dW hf
  mul := fun f g hf hg => funext fun x => (dW_mul (hf.diff x) (hg.diff x)).1
  sum := fun s F hF => funext fun x => by
    simp only [dW]
    rw [fderiv_fun_sum fun m _ => (hF m).diff x]
    simp only [FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum,
      ← Finset.sum_sub_distrib, Finset.sum_div]
  cmul := fun c f hf => funext fun x => by
    simp only [dW]
    rw [fderiv_const_mul (hf.diff x)]
    simp only [_root_.smul_apply, smul_eq_mul]
    ring
  add := fun f g hf hg => funext fun x => by
    simp only [dW]
    rw [fderiv_fun_add (hf.diff x) (hg.diff x)]
    simp only [_root_.add_apply]
    ring
  const := fun c => funext fun x => by simp [dW]

/-- `∂_{w̄}` is a derivation on smooth functions. -/
private lemma AM_der_dWbar : AM_Der dWbar where
  sm := fun _ hf => AM_sm_dWbar hf
  mul := fun f g hf hg => funext fun x => (dW_mul (hf.diff x) (hg.diff x)).2
  sum := fun s F hF => funext fun x => by
    simp only [dWbar]
    rw [fderiv_fun_sum fun m _ => (hF m).diff x]
    simp only [FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib, Finset.sum_div]
  cmul := fun c f hf => funext fun x => by
    simp only [dWbar]
    rw [fderiv_const_mul (hf.diff x)]
    simp only [_root_.smul_apply, smul_eq_mul]
    ring
  add := fun f g hf hg => funext fun x => by
    simp only [dWbar]
    rw [fderiv_fun_add (hf.diff x) (hg.diff x)]
    simp only [_root_.add_apply]
    ring
  const := fun c => funext fun x => by simp [dWbar]

/-- Iterates of a derivation keep smoothness. -/
private lemma AM_der_iter_sm {d : (ℂ → ℂ) → ℂ → ℂ} (hd : AM_Der d) (n : ℕ) {f : ℂ → ℂ}
    (hf : AM_Sm f) : AM_Sm (d^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact hd.sm _ ih

/-- Iterates of a derivation on a constant. -/
private lemma AM_der_iter_const {d : (ℂ → ℂ) → ℂ → ℂ} (hd : AM_Der d) (n : ℕ) (c : ℂ) :
    d^[n] (fun _ => c) = fun _ => if n = 0 then c else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [Nat.add_one_ne_zero, ite_false]
    exact hd.const _

/-- Iterates of a derivation are linear on finite sums of smooth functions. -/
private lemma AM_der_iter_lin {d : (ℂ → ℂ) → ℂ → ℂ} (hd : AM_Der d) (n : ℕ) (s : Finset ℕ)
    (c : ℕ → ℂ) (F : ℕ → ℂ → ℂ) (hF : ∀ m, AM_Sm (F m)) :
    d^[n] (fun x => ∑ m ∈ s, c m * F m x) = fun x => ∑ m ∈ s, c m * d^[n] (F m) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hd.sum s _ fun m => AM_sm_cmul _ (AM_der_iter_sm hd n (hF m))]
    funext x
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hd.cmul _ _ (AM_der_iter_sm hd n (hF m)), Function.iterate_succ_apply']

/-- Iterates of a derivation are additive on smooth functions. -/
private lemma AM_der_iter_add {d : (ℂ → ℂ) → ℂ → ℂ} (hd : AM_Der d) (n : ℕ) {f g : ℂ → ℂ}
    (hf : AM_Sm f) (hg : AM_Sm g) :
    d^[n] (fun x => f x + g x) = fun x => d^[n] f x + d^[n] g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hd.add _ _ (AM_der_iter_sm hd n hf) (AM_der_iter_sm hd n hg),
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- Iterates of a derivation commute with constant factors. -/
private lemma AM_der_iter_cmul {d : (ℂ → ℂ) → ℂ → ℂ} (hd : AM_Der d) (n : ℕ) (c : ℂ)
    {f : ℂ → ℂ} (hf : AM_Sm f) :
    d^[n] (fun x => c * f x) = fun x => c * d^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hd.cmul _ _ (AM_der_iter_sm hd n hf),
      Function.iterate_succ_apply']

/-- The Leibniz rule for iterates of a derivation on smooth functions. -/
private lemma AM_leib {d : (ℂ → ℂ) → ℂ → ℂ} (hd : AM_Der d) {f g : ℂ → ℂ} (hf : AM_Sm f)
    (hg : AM_Sm g) (n : ℕ) :
    d^[n] (fun x => f x * g x) = fun x => ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℂ) * (d^[m] f x * d^[n - m] g x) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hs : ∀ m, AM_Sm (fun x => d^[m] f x * d^[n - m] g x) := fun m =>
      AM_sm_mul (AM_der_iter_sm hd m hf) (AM_der_iter_sm hd (n - m) hg)
    rw [hd.sum _ _ fun m => AM_sm_cmul _ (hs m)]
    funext x
    rw [Finset.sum_choose_succ_mul (fun i j => d^[i] f x * d^[j] g x) n]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [hd.cmul _ _ (hs m), hd.mul _ _ (AM_der_iter_sm hd m hf) (AM_der_iter_sm hd (n - m) hg)]
    rw [← Function.iterate_succ_apply' d m f, ← Function.iterate_succ_apply' d (n - m) g]
    rw [show n + 1 - m = (n - m).succ by omega]
    ring

/-- The Leibniz rule for the mixed derivatives `∂_w^a ∂_{w̄}^b` of a product of smooth
functions. -/
private lemma AM_wirt_mul {f g : ℂ → ℂ} (hf : AM_Sm f) (hg : AM_Sm g) (a b : ℕ) (x : ℂ) :
    wirt a b (fun y => f y * g y) x = ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
      (a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f x * wirt (a - a') (b - b') g x) := by
  unfold wirt
  rw [AM_leib AM_der_dWbar hf hg b]
  have hs : ∀ m, AM_Sm (fun x => dWbar^[m] f x * dWbar^[b - m] g x) := fun m =>
    AM_sm_mul (AM_der_iter_sm AM_der_dWbar m hf) (AM_der_iter_sm AM_der_dWbar (b - m) hg)
  rw [AM_der_iter_lin AM_der_dW a _ _ _ hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [AM_leib AM_der_dW (AM_der_iter_sm AM_der_dWbar b' hf)
    (AM_der_iter_sm AM_der_dWbar (b - b') hg) a]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  ring

/-- The mixed derivatives of a constant. -/
private lemma AM_wirt_const (c : ℂ) (a b : ℕ) :
    wirt a b (fun _ => c) = fun _ => if a = 0 ∧ b = 0 then c else 0 := by
  unfold wirt
  rw [AM_der_iter_const AM_der_dWbar b c]
  by_cases hb : b = 0
  · simp only [hb, ite_true]
    rw [AM_der_iter_const AM_der_dW a c]
    simp
  · simp only [hb, ite_false, and_false]
    rw [AM_der_iter_const AM_der_dW a 0]
    simp

/-- Linearity of the mixed derivatives. -/
private lemma AM_wirt_lin {f g : ℂ → ℂ} (hf : AM_Sm f) (hg : AM_Sm g) (c₁ c₂ : ℂ) (a b : ℕ) :
    wirt a b (fun x => c₁ * f x + c₂ * g x) = fun x => c₁ * wirt a b f x + c₂ * wirt a b g x := by
  unfold wirt
  rw [AM_der_iter_add AM_der_dWbar b (AM_sm_cmul c₁ hf) (AM_sm_cmul c₂ hg),
    AM_der_iter_cmul AM_der_dWbar b c₁ hf, AM_der_iter_cmul AM_der_dWbar b c₂ hg,
    AM_der_iter_add AM_der_dW a (AM_sm_cmul c₁ (AM_der_iter_sm AM_der_dWbar b hf))
      (AM_sm_cmul c₂ (AM_der_iter_sm AM_der_dWbar b hg)),
    AM_der_iter_cmul AM_der_dW a c₁ (AM_der_iter_sm AM_der_dWbar b hf),
    AM_der_iter_cmul AM_der_dW a c₂ (AM_der_iter_sm AM_der_dWbar b hg)]

/-- `∂_{w̄} ∂_w f = ∂_w ∂_{w̄} f` for smooth `f` (symmetry of the second derivative). -/
private lemma AM_dWbar_dW {f : ℂ → ℂ} (hf : AM_Sm f) : dWbar (dW f) = dW (dWbar f) := by
  funext z
  have hL : Differentiable ℝ (fderiv ℝ f) :=
    ((hf 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ f z := (hf 2).contDiffAt.isSymmSndFDerivAt (by simp)
  set F2 := fderiv ℝ (fderiv ℝ f) z with hF2
  have hd : ∀ v : ℂ, HasFDerivAt (fun y => fderiv ℝ f y v) (F2.flip v) z := by
    intro v
    have := (hL z).hasFDerivAt.clm_apply (hasFDerivAt_const v z)
    simpa using this
  have e1 : dW f = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ f y 1 + (-Complex.I) * fderiv ℝ f y Complex.I) := by
    funext y; simp only [dW]; ring
  have e2 : dWbar f = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ f y 1 + Complex.I * fderiv ℝ f y Complex.I) := by
    funext y; simp only [dWbar]; ring
  have k1 : HasFDerivAt (dW f) ((2 : ℂ)⁻¹ • (F2.flip 1 + (-Complex.I) • F2.flip Complex.I)) z := by
    rw [e1]
    exact ((hd 1).add ((hd Complex.I).const_mul (-Complex.I))).const_mul _
  have k2 : HasFDerivAt (dWbar f) ((2 : ℂ)⁻¹ • (F2.flip 1 + Complex.I • F2.flip Complex.I)) z := by
    rw [e2]
    exact ((hd 1).add ((hd Complex.I).const_mul Complex.I)).const_mul _
  simp only [dW, dWbar] at k1 k2 ⊢
  rw [k1.fderiv, k2.fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  have hs : F2 Complex.I 1 = F2 1 Complex.I := hsym Complex.I 1
  rw [hs]
  ring_nf

/-- `∂_{w̄}^a ∂_w^b f = ∂_w^b ∂_{w̄}^a f` for smooth `f`. -/
private lemma AM_iter_comm {f : ℂ → ℂ} (hf : AM_Sm f) (a b : ℕ) :
    dWbar^[a] (dW^[b] f) = dW^[b] (dWbar^[a] f) := by
  have one : ∀ (b : ℕ) (g : ℂ → ℂ), AM_Sm g → dWbar (dW^[b] g) = dW^[b] (dWbar g) := by
    intro b
    induction b with
    | zero => intro g _; rfl
    | succ b ih =>
      intro g hg
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        AM_dWbar_dW (AM_der_iter_sm AM_der_dW b hg), ih g hg]
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, one b _ (AM_der_iter_sm AM_der_dWbar a hf),
      Function.iterate_succ_apply']

/-- The mixed derivatives of a complex conjugate: `∂_w^a ∂_{w̄}^b f̄ = conj(∂_w^b ∂_{w̄}^a f)`. -/
private lemma AM_wirt_conj {f : ℂ → ℂ} (hf : AM_Sm f) (a b : ℕ) :
    wirt a b (fun x => starRingEnd ℂ (f x)) = fun x => starRingEnd ℂ (wirt b a f x) := by
  have hb : ∀ (n : ℕ) (g : ℂ → ℂ), AM_Sm g →
      dWbar^[n] (fun x => starRingEnd ℂ (g x)) = fun x => starRingEnd ℂ (dW^[n] g x) := by
    intro n
    induction n with
    | zero => intro g _; rfl
    | succ n ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
      exact funext fun x => (dW_conj ((AM_der_iter_sm AM_der_dW n hg).diff x)).2
  have ha : ∀ (n : ℕ) (g : ℂ → ℂ), AM_Sm g →
      dW^[n] (fun x => starRingEnd ℂ (g x)) = fun x => starRingEnd ℂ (dWbar^[n] g x) := by
    intro n
    induction n with
    | zero => intro g _; rfl
    | succ n ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
      exact funext fun x => (dW_conj ((AM_der_iter_sm AM_der_dWbar n hg).diff x)).1
  unfold wirt
  rw [hb b f hf, ha a _ (AM_der_iter_sm AM_der_dW b hf), AM_iter_comm hf a b]

/-! ### Bounds on the mixed derivatives of products -/

/-- The Leibniz bound: if `|∂^{(a,b)} f| ≤ Γ^{a+b} α^{a+b} c_f` and `|∂^{(a,b)} g| ≤ Γ^{a+b} β^{a+b}
c_g` at `w` for `a + b ≤ k`, then `|∂^{(a,b)} (f g)| ≤ Γ^{a+b} (α + β)^{a+b} c_f c_g`. -/
private lemma AM_LB {f g : ℂ → ℂ} (hf : AM_Sm f) (hg : AM_Sm g) (w : ℂ) (Γ α β cf cg : ℝ)
    (k : ℕ) (hΓ : 0 ≤ Γ) (hα : 0 ≤ α) (hcf : 0 ≤ cf)
    (hF : ∀ a b, a + b ≤ k → ‖wirt a b f w‖ ≤ Γ ^ (a + b) * α ^ (a + b) * cf)
    (hG : ∀ a b, a + b ≤ k → ‖wirt a b g w‖ ≤ Γ ^ (a + b) * β ^ (a + b) * cg) :
    ∀ a b, a + b ≤ k →
      ‖wirt a b (fun y => f y * g y) w‖ ≤ Γ ^ (a + b) * (α + β) ^ (a + b) * (cf * cg) := by
  intro a b hab
  rw [AM_wirt_mul hf hg a b w]
  have key : ∀ a' ∈ Finset.range (a + 1), ∀ b' ∈ Finset.range (b + 1),
      ‖(a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f w * wirt (a - a') (b - b') g w)‖ ≤
        Γ ^ (a + b) * (cf * cg) * ((a.choose a' : ℝ) * α ^ a' * β ^ (a - a')) *
          ((b.choose b' : ℝ) * α ^ b' * β ^ (b - b')) := by
    intro a' ha' b' hb'
    have ha'' : a' ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha')
    have hb'' : b' ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have h1 := hF a' b' (by omega)
    have h2 := hG (a - a') (b - b') (by omega)
    have e : Γ ^ (a + b) = Γ ^ (a' + b') * Γ ^ (a - a' + (b - b')) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    calc (a.choose a' : ℝ) * (b.choose b' : ℝ) * (‖wirt a' b' f w‖ * ‖wirt (a - a') (b - b') g w‖)
        ≤ (a.choose a' : ℝ) * (b.choose b' : ℝ) * ((Γ ^ (a' + b') * α ^ (a' + b') * cf) *
            (Γ ^ (a - a' + (b - b')) * β ^ (a - a' + (b - b')) * cg)) := by
          gcongr
      _ = _ := by rw [pow_add, pow_add]; ring
  calc ‖∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        (a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f w * wirt (a - a') (b - b') g w)‖
      ≤ ∑ a' ∈ Finset.range (a + 1), ‖∑ b' ∈ Finset.range (b + 1),
        (a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f w * wirt (a - a') (b - b') g w)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        ‖(a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f w * wirt (a - a') (b - b') g w)‖ :=
        Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        Γ ^ (a + b) * (cf * cg) * ((a.choose a' : ℝ) * α ^ a' * β ^ (a - a')) *
          ((b.choose b' : ℝ) * α ^ b' * β ^ (b - b')) :=
        Finset.sum_le_sum fun a' ha' => Finset.sum_le_sum fun b' hb' => key a' ha' b' hb'
    _ = Γ ^ (a + b) * (cf * cg) *
        ((∑ a' ∈ Finset.range (a + 1), α ^ a' * β ^ (a - a') * (a.choose a' : ℝ)) *
          (∑ b' ∈ Finset.range (b + 1), α ^ b' * β ^ (b - b') * (b.choose b' : ℝ))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = Γ ^ (a + b) * (α + β) ^ (a + b) * (cf * cg) := by
        rw [← add_pow, ← add_pow, pow_add]
        ring

/-- The bound on the mixed derivatives of a power `u^m`: `|∂^{(a,b)} u^m| ≤ Γ^{a+b} m^{a+b} c^m`
when `|∂^{(a,b)} u| ≤ Γ^{a+b} c` for `a + b ≤ k`. -/
private lemma AM_pow_jet {u : ℂ → ℂ} (hu : AM_Sm u) (w : ℂ) (Γ c : ℝ) (k : ℕ) (hΓ : 0 ≤ Γ)
    (hc : 0 ≤ c) (hU : ∀ a b, a + b ≤ k → ‖wirt a b u w‖ ≤ Γ ^ (a + b) * c) (m : ℕ) :
    ∀ a b, a + b ≤ k →
      ‖wirt a b (fun y => u y ^ m) w‖ ≤ Γ ^ (a + b) * (m : ℝ) ^ (a + b) * c ^ m := by
  induction m with
  | zero =>
    intro a b _
    simp only [pow_zero, AM_wirt_const]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have : a + b ≠ 0 := by omega
      simp [zero_pow this]
  | succ m ih =>
    intro a b hab
    have e : (fun y => u y ^ (m + 1)) = fun y => u y ^ m * u y := funext fun y => pow_succ _ _
    rw [e]
    have := AM_LB (AM_sm_pow hu m) hu w Γ m 1 (c ^ m) c k hΓ (Nat.cast_nonneg m)
      (pow_nonneg hc m) ih (fun a b hab => by rw [one_pow, mul_one]; exact hU a b hab) a b hab
    rw [pow_succ]
    push_cast
    exact this

/-- The first derivatives of a power: `|∂ u^m| ≤ m β x^{m-1}` when `|u| ≤ x` and `|∂ u| ≤ β`. -/
private lemma AM_pow_d1 {u : ℂ → ℂ} (hu : AM_Sm u) (w : ℂ) (x β : ℝ) (hx : ‖u w‖ ≤ x)
    (hβ1 : ‖dW u w‖ ≤ β) (hβ2 : ‖dWbar u w‖ ≤ β) (m : ℕ) :
    ‖dW (fun y => u y ^ m) w‖ ≤ m * β * x ^ (m - 1) ∧
      ‖dWbar (fun y => u y ^ m) w‖ ≤ m * β * x ^ (m - 1) := by
  have hx0 : 0 ≤ x := (norm_nonneg _).trans hx
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ1
  induction m with
  | zero =>
    simp only [pow_zero]
    rw [AM_der_dW.const, AM_der_dWbar.const]
    simp
  | succ m ih =>
    have e : (fun y => u y ^ (m + 1)) = fun y => u y ^ m * u y := funext fun y => pow_succ _ _
    rw [e, AM_der_dW.mul _ _ (AM_sm_pow hu m) hu, AM_der_dWbar.mul _ _ (AM_sm_pow hu m) hu]
    have hum : ‖u w ^ m‖ ≤ x ^ m := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hx m
    have key : ∀ A B : ℂ, ‖A‖ ≤ m * β * x ^ (m - 1) → ‖B‖ ≤ β →
        ‖A * u w + u w ^ m * B‖ ≤ ((m + 1 : ℕ) : ℝ) * β * x ^ (m + 1 - 1) := by
      intro A B hA hB
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖A‖ * ‖u w‖ ≤ m * β * x ^ (m - 1) * x :=
        mul_le_mul hA hx (norm_nonneg _) (by positivity)
      have h2 : ‖u w ^ m‖ * ‖B‖ ≤ x ^ m * β := mul_le_mul hum hB (norm_nonneg _) (by positivity)
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, CharP.cast_eq_zero, zero_mul, zero_add] at h1 h2 ⊢
        push_cast
        nlinarith
      · have e : x ^ (m - 1) * x = x ^ m := by
          rw [← pow_succ]; congr 1; omega
        have e' : m + 1 - 1 = m := by omega
        rw [e']
        have h1' : ‖A‖ * ‖u w‖ ≤ m * β * x ^ m := by
          calc ‖A‖ * ‖u w‖ ≤ m * β * x ^ (m - 1) * x := h1
            _ = m * β * x ^ m := by rw [← e]; ring
        push_cast
        nlinarith
    exact ⟨key _ _ ih.1 hβ1, key _ _ ih.2 hβ2⟩

/-! ### Slices and resolvent polynomials -/

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma AM_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
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

/-- The one-entry slice of a Hermitian array is Hermitian. -/
private lemma AM_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

/-- The slice `w ↦ setEntry h i j w` is smooth. -/
private lemma AM_contDiff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun w : ℂ => setEntry h i j w) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hre : ContDiff ℝ n (fun w : ℂ => ((w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
  have hcw : ContDiff ℝ n (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.contDiff
  simp only [setEntry]
  split_ifs
  all_goals first | exact hre | exact contDiff_id | exact hcw | exact contDiff_const

/-- The slice of a resolvent polynomial through a Hermitian array is smooth. -/
private lemma AM_sm_slice {D N : ℕ} (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    AM_Sm (fun w => resPolyEval P (setEntry h i j w)) := fun n => by
  have e : (fun w => resPolyEval P (setEntry h i j w)) =
      (fun h' => resPolyEval P (symArr h')) ∘ (fun w => setEntry h i j w) := by
    funext w
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact (contDiff_resPoly_symArr P hP n).comp (AM_contDiff_slice h i j n)

/-- The form `e_p^* G (M e_q)` is the entry `(G M)_{pq}`. -/
private lemma AM_f_eM {D N : ℕ} (Λ M : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Pi.single p 1, M *ᵥ Pi.single q 1, Λ, z) h =
      (res (Matrix.of h + Λ) z * M) p q := by
  simp [resFactorEval, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply]

/-- The form `e_p^* G e_q` is the entry `G_{pq}`. -/
private lemma AM_f_ee {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Pi.single p 1, Pi.single q 1, Λ, z) h = res (Matrix.of h + Λ) z p q := by
  simp [resFactorEval, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The form `(Λ e_p)^* G (M e_q)` is the entry `(Λ G M)_{pq}` for Hermitian `Λ`. -/
private lemma AM_f_LeM {D N : ℕ} (Λ M : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Λ *ᵥ Pi.single p 1, M *ᵥ Pi.single q 1, Λ, z) h =
      (Λ * res (Matrix.of h + Λ) z * M) p q := by
  unfold resFactorEval
  simp only
  rw [Matrix.star_mulVec, hΛ.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply]

/-- The polynomial `Σ_x g(x)` over the index set, as a concatenation. -/
private def AM_sum {D N : ℕ} (g : Idx D N → ResPoly D N) : ResPoly D N :=
  (Finset.univ : Finset (Idx D N)).toList.flatMap g

/-- The value of a sum of polynomials over the index set. -/
private lemma AM_eval_sum {D N : ℕ} (g : Idx D N → ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (AM_sum g) h = ∑ x, resPolyEval (g x) h := by
  have key : ∀ L : List (Idx D N), resPolyEval (L.flatMap g) h =
      (L.map fun x => resPolyEval (g x) h).sum := by
    intro L
    induction L with
    | nil => simp [resPolyEval]
    | cons x L ih => simp only [List.flatMap_cons, resPolyEval_append, ih, List.map_cons,
        List.sum_cons]
  unfold AM_sum
  rw [key, Finset.sum_map_toList]

/-- Membership in a sum of polynomials. -/
private lemma AM_mem_sum {D N : ℕ} (g : Idx D N → ResPoly D N) (t : ℂ × ResMono D N) :
    t ∈ AM_sum g ↔ ∃ x, t ∈ g x := by
  simp [AM_sum, List.mem_flatMap]

/-- The weight `Σ_t |c_t|` of a resolvent polynomial. -/
private def AM_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

private lemma AM_wt_append {D N : ℕ} (P Q : ResPoly D N) :
    AM_wt (P ++ Q) = AM_wt P + AM_wt Q := by
  simp [AM_wt, List.map_append, List.sum_append]

private lemma AM_wt_single {D N : ℕ} (c : ℂ) (m : ResMono D N) : AM_wt [(c, m)] = ‖c‖ := by
  simp [AM_wt]

private lemma AM_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ AM_wt P :=
  List.sum_nonneg fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

private lemma AM_wt_sum {D N : ℕ} (g : Idx D N → ResPoly D N) :
    AM_wt (AM_sum g) = ∑ x, AM_wt (g x) := by
  have key : ∀ L : List (Idx D N), AM_wt (L.flatMap g) = (L.map fun x => AM_wt (g x)).sum := by
    intro L
    induction L with
    | nil => simp [AM_wt]
    | cons x L ih =>
      rw [List.flatMap_cons, AM_wt_append, ih, List.map_cons, List.sum_cons]
  unfold AM_sum
  rw [key, Finset.sum_map_toList]

/-- The weight of a product of polynomials is the product of the weights. -/
private lemma AM_wt_mul {D N : ℕ} (P Q : ResPoly D N) :
    AM_wt (resPolyMul P Q) = AM_wt P * AM_wt Q := by
  induction P with
  | nil => simp [resPolyMul, AM_wt]
  | cons s P ih =>
    have hrow : ∀ R : ResPoly D N,
        AM_wt (R.map fun t => (s.1 * t.1, s.2 ++ t.2)) = ‖s.1‖ * AM_wt R := by
      intro R
      induction R with
      | nil => simp [AM_wt]
      | cons t R ihR =>
        simp only [List.map_cons, AM_wt, List.sum_cons, norm_mul] at ihR ⊢
        rw [ihR]; ring
    have hsplit : resPolyMul (s :: P) Q
        = (Q.map fun t => (s.1 * t.1, s.2 ++ t.2)) ++ resPolyMul P Q := by
      simp [resPolyMul]
    rw [hsplit, AM_wt_append, ih, hrow]
    simp only [AM_wt, List.map_cons, List.sum_cons]
    ring

/-- The weight of the conjugate polynomial. -/
private lemma AM_wt_star {D N : ℕ} (P : ResPoly D N) : AM_wt (resPolyStar P) = AM_wt P := by
  simp [AM_wt, resPolyStar, Function.comp_def]

/-- The `n`-th power of a resolvent polynomial. -/
private def AM_pow {D N : ℕ} (P : ResPoly D N) : ℕ → ResPoly D N
  | 0 => [(1, [])]
  | n + 1 => resPolyMul (AM_pow P n) P

private lemma AM_eval_pow {D N : ℕ} (P : ResPoly D N) (n : ℕ) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (AM_pow P n) h = resPolyEval P h ^ n := by
  induction n with
  | zero => simp [AM_pow, resPolyEval, resMonoEval]
  | succ n ih => rw [AM_pow, resPolyEval_mul, ih, pow_succ]

private lemma AM_wt_pow {D N : ℕ} (P : ResPoly D N) (n : ℕ) : AM_wt (AM_pow P n) = AM_wt P ^ n := by
  induction n with
  | zero => simp [AM_pow, AM_wt]
  | succ n ih => rw [AM_pow, AM_wt_mul, ih, pow_succ]

/-- The shape of a resolvent polynomial: at most `m` factors per term, vectors in `V`, pairs in
`Ξ`. -/
private def AM_ok {D N : ℕ} (V : Set (Idx D N → ℂ)) (Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ))
    (m : ℕ) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2 ∈ Ξ

private lemma AM_ok_append {D N : ℕ} {V : Set (Idx D N → ℂ)}
    {Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)} {m : ℕ} {P Q : ResPoly D N}
    (hP : AM_ok V Ξ m P) (hQ : AM_ok V Ξ m Q) : AM_ok V Ξ m (P ++ Q) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hP t h
  · exact hQ t h

private lemma AM_ok_sum {D N : ℕ} {V : Set (Idx D N → ℂ)}
    {Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)} {m : ℕ} {g : Idx D N → ResPoly D N}
    (hg : ∀ x, AM_ok V Ξ m (g x)) : AM_ok V Ξ m (AM_sum g) := by
  intro t ht
  obtain ⟨x, hx⟩ := (AM_mem_sum g t).mp ht
  exact hg x t hx

private lemma AM_ok_mul {D N : ℕ} {V : Set (Idx D N → ℂ)}
    {Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)} {m₁ m₂ : ℕ} {P Q : ResPoly D N}
    (hP : AM_ok V Ξ m₁ P) (hQ : AM_ok V Ξ m₂ Q) : AM_ok V Ξ (m₁ + m₂) (resPolyMul P Q) := by
  intro t ht
  simp only [resPolyMul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  refine ⟨?_, fun f hf => ?_⟩
  · simp only [List.length_append]
    exact Nat.add_le_add (hP s hs).1 (hQ u hu).1
  · rcases List.mem_append.mp hf with h | h
    · exact (hP s hs).2 f h
    · exact (hQ u hu).2 f h

private lemma AM_ok_pow {D N : ℕ} {V : Set (Idx D N → ℂ)}
    {Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)} {m : ℕ} {P : ResPoly D N}
    (hP : AM_ok V Ξ m P) (n : ℕ) : AM_ok V Ξ (n * m) (AM_pow P n) := by
  induction n with
  | zero =>
    intro t ht
    simp only [AM_pow, List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, fun f hf => by simp at hf⟩
  | succ n ih =>
    rw [AM_pow, Nat.succ_mul]
    exact AM_ok_mul ih hP

private lemma AM_ok_star {D N : ℕ} {V : Set (Idx D N → ℂ)}
    {Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)} {m : ℕ} {P : ResPoly D N}
    (hΞ : ∀ q ∈ Ξ, (q.1, starRingEnd ℂ q.2) ∈ Ξ)
    (hP : AM_ok V Ξ m P) : AM_ok V Ξ m (resPolyStar P) := by
  intro t ht
  simp only [resPolyStar, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨by simpa using (hP s hs).1, fun f hf => ?_⟩
  simp only [List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨h1, h2, h3⟩ := (hP s hs).2 g hg
  exact ⟨h2, h1, hΞ _ h3⟩

/-! ### Measurability of resolvent polynomials -/

/-- Every entry of `(h + Λ - ξ)⁻¹` is a measurable function of the array. -/
private lemma AM_meas_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (k l : Idx D N) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of h + Λ) ξ k l) := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ =>
      Matrix.of h + Λ - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) :=
    (continuous_id.add continuous_const).sub continuous_const
  have hdet := hc.matrix_det.measurable
  have hadj := hc.matrix_adjugate.measurable
  simp only [res, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp hadj))

private lemma AM_meas_factor {D N : ℕ} (f : ResFactor D N) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => resFactorEval f h) := by
  simp only [resFactorEval, dotProduct, Matrix.mulVec]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul
    (Finset.measurable_sum _ fun l _ => (AM_meas_res _ _ k l).mul measurable_const)

private lemma AM_meas_mono {D N : ℕ} (m : ResMono D N) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => resMonoEval m h) := by
  induction m with
  | nil => simp only [resMonoEval, List.map_nil, List.prod_nil]; exact measurable_const
  | cons f m ih =>
    simp only [resMonoEval, List.map_cons, List.prod_cons] at ih ⊢
    exact (AM_meas_factor f).mul ih

/-- Every resolvent polynomial is a measurable function of the array. -/
private lemma AM_meas_poly {D N : ℕ} (P : ResPoly D N) :
    Measurable (fun h : Idx D N → Idx D N → ℂ => resPolyEval P h) := by
  induction P with
  | nil => simp only [resPolyEval, List.map_nil, List.sum_nil]; exact measurable_const
  | cons t P ih =>
    simp only [resPolyEval, List.map_cons, List.sum_cons] at ih ⊢
    exact (measurable_const.mul (AM_meas_mono t.2)).add ih

/-! ### `⟨B H̲G⟩` as a resolvent polynomial -/

/-- The entries of the profile `S_θ` as complex numbers. -/
private lemma AM_varProf_eq (D N : ℕ) (θ : ℝ) (r m : Idx D N) :
    (varProf D N θ r m : ℂ) = (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = m.1 then 1 else 0) +
      ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ := by
  unfold varProf
  push_cast
  split_ifs <;> simp

/-- The normalized trace as a sum over the diagonal. -/
private lemma AM_ntr_eq (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr M = ((D : ℂ) * N)⁻¹ * ∑ r, M r r := by
  simp [ntr, Matrix.trace, Fintype.card_prod]

/-- `S_θ(R)` is the diagonal matrix with entries `Σ_r (S_θ)_{rp} R_{rr}`. -/
private lemma AM_sTheta_apply (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ)
    (p q : Idx D N) :
    sTheta D N θ R p q = if p = q then ∑ r, (varProf D N θ r p : ℂ) * R r r else 0 := by
  have hD : (D : ℂ) ≠ 0 := by
    have : 0 < D := p.1.pos
    exact_mod_cast this.ne'
  have hDn : (D : ℂ) * ((D : ℂ) * N)⁻¹ = (N : ℂ)⁻¹ := by
    field_simp
  have hblk : ∀ a : Fin D, (D : ℂ) * ntr (R * Ea D N a) =
      (N : ℂ)⁻¹ * ∑ r, (if r.1 = a then R r r else 0) := by
    intro a
    rw [AM_ntr_eq]
    have : ∑ r, (R * Ea D N a) r r = ∑ r, (if r.1 = a then R r r else 0) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [Ea, Matrix.mul_diagonal]
    rw [this, ← hDn]
    ring
  by_cases h : p = q
  · subst h
    have hEa : ∀ a : Fin D, Ea D N a p p = if p.1 = a then (1 : ℂ) else 0 := by
      intro a
      simp [Ea]
    simp only [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, hEa,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, ite_true]
    have e1 : ∑ a : Fin D, (D : ℂ) * ntr (R * Ea D N a) * (if p.1 = a then (1 : ℂ) else 0) =
        (D : ℂ) * ntr (R * Ea D N p.1) := by
      simp [Finset.sum_ite_eq]
    rw [e1, hblk, AM_ntr_eq]
    simp only [AM_varProf_eq, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∀ r : Idx D N, (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = p.1 then (1 : ℂ) else 0) * R r r =
        (θ : ℂ) * ((N : ℂ)⁻¹ * if r.1 = p.1 then R r r else 0) := by
      intro r
      split_ifs <;> ring
    simp only [e2]
    push_cast
    simp only [mul_assoc]
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

/-- `H̲G = I - (Λ - z) G + S_θ(G) G` for Hermitian `H`, `Λ` and `Im z > 0` ((2.30)
[eq:HGline]). -/
private lemma AM_hgUnder_eq (D N : ℕ) (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    hgUnder D N θ H Λ z = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (H + Λ) z +
      sTheta D N θ (res (H + Λ) z) * res (H + Λ) z := by
  have hres := (res_mul_sub (H + Λ) (hH.add hΛ) z hz).1
  have hHG : H * res (H + Λ) z = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
      res (H + Λ) z := by
    have : H * res (H + Λ) z = (H + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        res (H + Λ) z - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (H + Λ) z := by
      rw [← Matrix.sub_mul]
      congr 1
      abel
    rw [this, hres]
  unfold hgUnder
  rw [hHG]

/-- The polynomial of `⟨B S_θ(G) G⟩ = (DN)⁻¹ Σ_{q,r} (S_θ)_{rq} G_{rr} (G B)_{qq}`. -/
private def AM_PS (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) : ResPoly D N :=
  AM_sum (fun r => AM_sum (fun q => [(((D : ℂ) * N)⁻¹ * (varProf D N θ r q : ℂ),
    [(Pi.single r 1, Pi.single r 1, Λ, z), (Pi.single q 1, B *ᵥ Pi.single q 1, Λ, z)])]))

/-- The polynomial of `⟨B H̲G⟩ = ⟨B⟩ - ⟨Λ G B⟩ + z ⟨G B⟩ + ⟨B S_θ(G) G⟩` ((2.30)
[eq:HGline]) in forms `x^* G y`, `x, y ∈ avgVecs`. -/
private def AM_PX (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) : ResPoly D N :=
  [(ntr B, [])] ++
  AM_sum (fun q => [(-((D : ℂ) * N)⁻¹, [(Λ *ᵥ Pi.single q 1, B *ᵥ Pi.single q 1, Λ, z)])]) ++
  AM_sum (fun q => [(((D : ℂ) * N)⁻¹ * z, [(Pi.single q 1, B *ᵥ Pi.single q 1, Λ, z)])]) ++
  AM_PS D N θ Λ B z

/-- The value of `AM_PS` is `⟨B S_θ(G) G⟩`. -/
private lemma AM_eval_PS (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (AM_PS D N θ Λ B z) h =
      ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) := by
  set G := res (Matrix.of h + Λ) z with hG
  have t3 : (B * (sTheta D N θ G * G)).trace =
      ∑ q, ∑ r, (varProf D N θ r q : ℂ) * G r r * (G * B) q q := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, AM_sTheta_apply, ite_mul,
      zero_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.sum_mul]
  rw [ntr, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, t3]
  simp only [AM_PS, AM_eval_sum]
  simp only [resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, add_zero, mul_one, AM_f_ee, AM_f_eM]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun r _ => by rw [← hG]; ring

/-- On Hermitian arrays the polynomial `AM_PX` takes the value `⟨B H̲G⟩`. -/
private lemma AM_eval_PX (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    resPolyEval (AM_PX D N θ Λ B z) h = ntr (B * hgUnder D N θ (Matrix.of h) Λ z) := by
  rw [AM_hgUnder_eq D N θ _ Λ hh hΛ z hz]
  have hmat : B * (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z +
      sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z) =
      B - (B * Λ) * res (Matrix.of h + Λ) z + z • (B * res (Matrix.of h + Λ) z) +
        B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z) := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Matrix.one_mul]
    abel
  have t1 : (B * Λ * res (Matrix.of h + Λ) z).trace =
      ∑ q, (Λ * res (Matrix.of h + Λ) z * B) q q := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag_apply]
  have t2 : (B * res (Matrix.of h + Λ) z).trace = ∑ q, (res (Matrix.of h + Λ) z * B) q q := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag_apply]
  have hntr : ∀ M : Matrix (Idx D N) (Idx D N) ℂ, ntr M = ((D : ℂ) * N)⁻¹ * M.trace := by
    intro M; simp [ntr, Fintype.card_prod]
  rw [hmat, hntr]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, t1, t2]
  have hPS := AM_eval_PS D N θ Λ B z h
  rw [hntr] at hPS
  simp only [AM_PX, resPolyEval_append, hPS, AM_eval_sum]
  simp only [resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, add_zero, mul_one, AM_f_eM, AM_f_LeM Λ B hΛ]
  have s2 : ∑ x, -((D : ℂ) * N)⁻¹ * (Λ * res (Matrix.of h + Λ) z * B) x x =
      -(((D : ℂ) * N)⁻¹ * ∑ q, (Λ * res (Matrix.of h + Λ) z * B) q q) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have s3 : ∑ x, ((D : ℂ) * N)⁻¹ * z * (res (Matrix.of h + Λ) z * B) x x =
      ((D : ℂ) * N)⁻¹ * (z * ∑ q, (res (Matrix.of h + Λ) z * B) q q) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [s2, s3, hntr B]
  ring

/-! ### Norms of the vectors and crude bounds on the forms -/

/-- `|x^* A y| ≤ ‖A‖` for vectors `x`, `y` of norm `≤ 1`. -/
private lemma AM_form_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x y : ι → ℂ) (hx : ∑ r, ‖x r‖ ^ 2 ≤ 1) (hy : ∑ r, ‖y r‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ≤ opNorm A := by
  have e : star x ⬝ᵥ (A *ᵥ y) = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanCLM_toLp]
    simp [dotProduct_comm]
  have hxn : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact (Real.sqrt_le_sqrt hx).trans_eq Real.sqrt_one
  have hyn : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact (Real.sqrt_le_sqrt hy).trans_eq Real.sqrt_one
  rw [e]
  unfold opNorm
  calc ‖inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * 1) :=
        mul_le_mul hxn ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm_of_le hyn)
          (norm_nonneg _) zero_le_one
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by ring

open scoped Matrix.Norms.L2Operator in
/-- `Σ_k |(T u)_k|² ≤ ‖T‖² Σ_k |u_k|²`. -/
private lemma AM_mulVec_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (u : ι → ℂ) : ∑ k, ‖(T *ᵥ u) k‖ ^ 2 ≤ opNorm T ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec T (WithLp.toLp 2 u)
  have h1 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have h2 : ‖(EuclideanSpace.equiv ι ℂ).symm (T *ᵥ (WithLp.toLp 2 u).ofLp)‖ ^ 2 =
      ∑ k, ‖(T *ᵥ u) k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h3 : ‖(EuclideanSpace.equiv ι ℂ).symm (T *ᵥ (WithLp.toLp 2 u).ofLp)‖ ^ 2 ≤
      (‖T‖ * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [h2, mul_pow, h1] at h3
  exact h3

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of the conjugate transpose. -/
private lemma AM_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) : opNorm Tᴴ = opNorm T := by
  change ‖Tᴴ‖ = ‖T‖
  exact Matrix.l2_opNorm_conjTranspose T

/-- A standard basis vector has norm `1`. -/
private lemma AM_single_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    ∑ r, ‖(Pi.single k (1 : ℂ) : ι → ℂ) r‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- `|T e_k| ≤ ‖T‖ ≤ 1`. -/
private lemma AM_col_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (hT : opNorm T ≤ 1) (k : ι) : ∑ r, ‖(T *ᵥ Pi.single k 1) r‖ ^ 2 ≤ 1 := by
  refine (AM_mulVec_sq T _).trans ?_
  rw [AM_single_sq, mul_one]
  have h0 : 0 ≤ opNorm T := norm_nonneg _
  nlinarith

/-- The vectors of `avgVecs` have norm at most `1` when `‖Λ‖, ‖B‖ ≤ 1`. -/
private lemma AM_avgVecs_norm {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : opNorm Λ ≤ 1) (hB : opNorm B ≤ 1) :
    ∀ x ∈ avgVecs D N Λ B, ∑ r, ‖x r‖ ^ 2 ≤ 1 := by
  intro x hx
  simp only [avgVecs, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨k, rfl⟩
  · exact (AM_single_sq k).le
  · exact AM_col_sq B hB k
  · exact AM_col_sq Bᴴ (by rw [AM_opNorm_conjTranspose]; exact hB) k
  · exact AM_col_sq Λ hΛ k

/-- On Hermitian arrays every form over `avgVecs` is at most `η⁻¹`. -/
private lemma AM_form_le_inv {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (hΛn : opNorm Λ ≤ 1) (hB : opNorm B ≤ 1) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (x y : Idx D N → ℂ)
    (hx : x ∈ avgVecs D N Λ B) (hy : y ∈ avgVecs D N Λ B) :
    ‖star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)‖ ≤ z.im⁻¹ :=
  (AM_form_le_opNorm _ x y (AM_avgVecs_norm Λ B hΛn hB x hx)
    (AM_avgVecs_norm Λ B hΛn hB y hy)).trans (opNorm_res_le _ (hh.add hΛ) z hz)

/-- Every Hermitian array lies in the good event on `avgVecs` with `Γ = Υ = c` once
`η⁻¹ ≤ c`. -/
private lemma AM_crude_good {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (hΛn : opNorm Λ ≤ 1) (hB : opNorm B ≤ 1) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (c : ℝ) (hc : z.im⁻¹ ≤ c) :
    h ∈ goodSet Λ z (avgVecs D N Λ B) c c := by
  intro x hx y hy
  refine ⟨(AM_form_le_inv Λ B hΛ hΛn hB z hz h hh x y hx hy).trans hc, ?_⟩
  exact (Complex.im_le_norm _).trans ((AM_form_le_inv Λ B hΛ hΛn hB z hz h hh x x hx hx).trans hc)

/-- For Hermitian `h` and `Λ`: `x^* (h + Λ - ξ̄)⁻¹ y = conj(y^* (h + Λ - ξ)⁻¹ x)`. -/
private lemma AM_form_conj {D N : ℕ} (x y : Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (ξ : ℂ) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    resFactorEval (x, y, Λ, starRingEnd ℂ ξ) h = starRingEnd ℂ (resFactorEval (y, x, Λ, ξ) h) := by
  have hP : ∀ t ∈ [((1 : ℂ), [(y, x, Λ, ξ)])], ∀ f ∈ t.2, f.2.2.1.IsHermitian := by
    intro t ht f hf
    rw [List.mem_singleton] at ht
    subst ht
    rw [List.mem_singleton] at hf
    subst hf
    exact hΛ
  have := resPolyEval_star [((1 : ℂ), [(y, x, Λ, ξ)])] hP h hh
  simpa [resPolyStar, resPolyEval, resMonoEval] using this

/-! ### The shapes and weights of the polynomials -/

/-- The pairs `(Λ, z)` and `(Λ, z̄)`. -/
private def AM_Ξ {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ) := {(Λ, z), (Λ, starRingEnd ℂ z)}

private lemma AM_Ξ_conj {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    ∀ q ∈ AM_Ξ Λ z, (q.1, starRingEnd ℂ q.2) ∈ AM_Ξ Λ z := by
  rintro q (rfl | rfl)
  · exact Or.inr rfl
  · exact Or.inl (by simp)

private lemma AM_Ξ_pair {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) : ∀ q ∈ AM_Ξ Λ z, q.1.IsHermitian ∧ q.2.im ≠ 0 := by
  rintro q (rfl | rfl)
  · exact ⟨hΛ, hz.ne'⟩
  · exact ⟨hΛ, by simp [hz.ne']⟩

/-- The pair hypothesis of the derivative lemmas from the shape. -/
private lemma AM_ok_pair {D N : ℕ} {V : Set (Idx D N → ℂ)} {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im) {m : ℕ} {P : ResPoly D N}
    (hP : AM_ok V (AM_Ξ Λ z) m P) : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 :=
  fun t ht f hf => AM_Ξ_pair Λ hΛ z hz _ ((hP t ht).2 f hf).2.2

private lemma AM_e_mem (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (Pi.single p 1 : Idx D N → ℂ) ∈ (avgVecs D N Λ B : Set (Idx D N → ℂ)) := by
  simp only [avgVecs, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_union, Set.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨p, rfl⟩))

private lemma AM_Be_mem (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (B *ᵥ Pi.single p 1 : Idx D N → ℂ) ∈ (avgVecs D N Λ B : Set (Idx D N → ℂ)) := by
  simp only [avgVecs, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_union, Set.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨p, rfl⟩))

private lemma AM_Le_mem (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (Λ *ᵥ Pi.single p 1 : Idx D N → ℂ) ∈ (avgVecs D N Λ B : Set (Idx D N → ℂ)) := by
  simp only [avgVecs, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_union, Set.mem_range]
  exact Or.inr ⟨p, rfl⟩

private lemma AM_PS_ok (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    AM_ok (avgVecs D N Λ B : Set (Idx D N → ℂ)) (AM_Ξ Λ z) 2 (AM_PS D N θ Λ B z) := by
  refine AM_ok_sum fun r => AM_ok_sum fun q => ?_
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  refine ⟨by simp, fun f hf => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨AM_e_mem D N Λ B r, AM_e_mem D N Λ B r, Or.inl rfl⟩
  · exact ⟨AM_e_mem D N Λ B q, AM_Be_mem D N Λ B q, Or.inl rfl⟩

private lemma AM_PX_ok (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    AM_ok (avgVecs D N Λ B : Set (Idx D N → ℂ)) (AM_Ξ Λ z) 2 (AM_PX D N θ Λ B z) := by
  refine AM_ok_append (AM_ok_append (AM_ok_append ?_ ?_) ?_) (AM_PS_ok D N θ Λ B z)
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, fun f hf => by simp at hf⟩
  · refine AM_ok_sum fun q => ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨by simp, fun f hf => ?_⟩
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨AM_Le_mem D N Λ B q, AM_Be_mem D N Λ B q, Or.inl rfl⟩
  · refine AM_ok_sum fun q => ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨by simp, fun f hf => ?_⟩
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨AM_e_mem D N Λ B q, AM_Be_mem D N Λ B q, Or.inl rfl⟩

/-- `|B_{kk}| ≤ ‖B‖`. -/
private lemma AM_diag_le {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (k : ι) :
    ‖B k k‖ ≤ opNorm B := by
  have := AM_form_le_opNorm B (Pi.single k 1) (Pi.single k 1) (AM_single_sq k).le
    (AM_single_sq k).le
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- `|⟨B⟩| ≤ ‖B‖`. -/
private lemma AM_ntr_le {D N : ℕ} (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) :
    ‖ntr B‖ ≤ 1 := by
  rw [AM_ntr_eq, norm_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card (Idx D N)) with h0 | hpos
  · have : IsEmpty (Idx D N) := Fintype.card_eq_zero_iff.mp h0
    simp
  · have hc : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
    have hpos' : (0 : ℝ) < (D : ℝ) * N := by rw [← hc]; exact_mod_cast hpos
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have hs : ‖∑ r, B r r‖ ≤ (D : ℝ) * N := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ r, ‖B r r‖ ≤ ∑ _r : Idx D N, (1 : ℝ) :=
            Finset.sum_le_sum fun r _ => (AM_diag_le B r).trans hB
        _ = (D : ℝ) * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, mul_one]
    rw [inv_mul_le_iff₀ hpos', mul_one]
    exact hs

/-- The weight of `AM_PX` is at most `3 + |z|`. -/
private lemma AM_PX_wt (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (z : ℂ) :
    AM_wt (AM_PX D N θ Λ B z) ≤ 3 + ‖z‖ ∧ AM_wt (AM_PS D N θ Λ B z) ≤ 1 := by
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have hninv : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hvp : ∀ r q : Idx D N, 0 ≤ varProf D N θ r q := by
    intro r q
    unfold varProf
    have : 0 ≤ 1 - θ := by linarith
    split_ifs <;> positivity
  have hrow : ∀ r : Idx D N, ∑ q : Idx D N, varProf D N θ r q ≤ 1 := by
    intro r
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [varProf]
    have hD : 0 < D := r.1.pos
    have hb : ∑ q : Idx D N, (if r.1 = q.1 then ((N : ℝ))⁻¹ else 0) = 1 := by
      rw [Fintype.sum_prod_type]
      have e : ∀ x : Fin D, ∑ _x1 : Fin N, (if r.1 = (x, _x1).1 then ((N : ℝ))⁻¹ else 0) =
          if r.1 = x then 1 else 0 := by
        intro x
        have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        by_cases hx : r.1 = x
        · simp only [hx, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp
        · simp [hx]
      simp only [e, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold varProf
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcard]
    have : (D : ℝ) * N * ((1 - θ) * ((D : ℝ) * N)⁻¹) = 1 - θ := by field_simp
    nlinarith
  have hDN : ((D : ℝ) * N)⁻¹ * ((D : ℝ) * N) ≤ 1 := by
    rcases eq_or_ne ((D : ℝ) * N) 0 with h0 | h0
    · rw [h0]; simp
    · rw [inv_mul_cancel₀ h0]
  have hPS : AM_wt (AM_PS D N θ Λ B z) ≤ 1 := by
    unfold AM_PS
    simp only [AM_wt_sum, AM_wt_single, norm_mul, hninv, Complex.norm_real, Real.norm_eq_abs]
    calc ∑ r : Idx D N, ∑ q : Idx D N, ((D : ℝ) * N)⁻¹ * |varProf D N θ r q|
        = ((D : ℝ) * N)⁻¹ * ∑ r : Idx D N, ∑ q : Idx D N, varProf D N θ r q := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by rw [abs_of_nonneg (hvp r q)]
      _ ≤ ((D : ℝ) * N)⁻¹ * ∑ _r : Idx D N, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => hrow r) (by positivity)
      _ ≤ 1 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one]; exact hDN
  unfold AM_PX
  simp only [AM_wt_append, AM_wt_sum, AM_wt_single, norm_neg, norm_mul, hninv,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have h1 := AM_ntr_le B hB
  have h2 : (D : ℝ) * N * ((D : ℝ) * N)⁻¹ ≤ 1 := by rw [mul_comm]; exact hDN
  have h3 : (D : ℝ) * N * (((D : ℝ) * N)⁻¹ * ‖z‖) ≤ ‖z‖ := by
    rw [← mul_assoc]; nlinarith [norm_nonneg z]
  exact ⟨by linarith, hPS⟩

/-! ### The slices of `G`, `G B`, `Q`, `⟨B H̲G⟩` and of the integrand in the entry `(j, i)` -/

/-- `w ↦ G_{kl}` along the slice in the entry `(j, i)`. -/
private def AM_G {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j k l : Idx D N) : ℂ → ℂ :=
  fun w => res (Matrix.of (setEntry h j i w) + Λ) z k l

/-- `w ↦ (G B)_{kl}` along the slice in the entry `(j, i)`. -/
private def AM_F {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j k l : Idx D N) : ℂ → ℂ :=
  fun w => (res (Matrix.of (setEntry h j i w) + Λ) z * B) k l

/-- `w ↦ Q_{kl}` along the slice in the entry `(j, i)`. -/
private def AM_Q {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j k l : Idx D N) : ℂ → ℂ :=
  fun w => qMat D N θ (Matrix.of (setEntry h j i w)) Λ B z k l

/-- `w ↦ ⟨B H̲G⟩` along the slice in the entry `(j, i)`. -/
private def AM_X {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) : ℂ → ℂ :=
  fun w => ntr (B * hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z)

/-- The integrand `f = (G B)_{ji} ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p` along the slice in the entry
`(j, i)`. -/
private def AM_f {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (p : ℕ) : ℂ → ℂ :=
  fun w => AM_F Λ B z h i j j i w * AM_X θ Λ B z h i j w ^ (p - 1) *
    starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p

/-- The one-term polynomial of `(G B)_{kl}`. -/
private def AM_PF {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N) :
    ResPoly D N := [(1, [(Pi.single k 1, B *ᵥ Pi.single l 1, Λ, z)])]

private lemma AM_eval_PF {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (AM_PF Λ B z k l) h = (res (Matrix.of h + Λ) z * B) k l := by
  rw [← AM_f_eM]
  simp only [AM_PF, resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, List.sum_cons, List.sum_nil, add_zero, one_mul]

private lemma AM_PF_ok {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N) :
    AM_ok (avgVecs D N Λ B : Set (Idx D N → ℂ)) (AM_Ξ Λ z) 1 (AM_PF Λ B z k l) := by
  intro t ht
  simp only [AM_PF, List.mem_singleton] at ht
  subst ht
  refine ⟨by simp, fun f hf => ?_⟩
  simp only [List.mem_singleton] at hf
  subst hf
  exact ⟨AM_e_mem D N Λ B k, AM_Be_mem D N Λ B l, Or.inl rfl⟩

/-- The one-term polynomial of `G_{kl}`. -/
private def AM_PG {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N) :
    ResPoly D N := [(1, [(Pi.single k 1, Pi.single l 1, Λ, z)])]

private lemma AM_eval_PG {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (AM_PG Λ z k l) h = res (Matrix.of h + Λ) z k l := by
  simp [AM_PG, resPolyEval, resMonoEval, AM_f_ee]

private lemma AM_sm_F {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) : AM_Sm (AM_F Λ B z h i j k l) := by
  have e : AM_F Λ B z h i j k l = fun w => resPolyEval (AM_PF Λ B z k l) (setEntry h j i w) :=
    funext fun w => (AM_eval_PF Λ B z k l _).symm
  rw [e]
  exact AM_sm_slice _ (AM_ok_pair hΛ hz (AM_PF_ok Λ B z k l)) h hh j i

private lemma AM_sm_G {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) : AM_Sm (AM_G Λ z h i j k l) := by
  have e : AM_G Λ z h i j k l = fun w => resPolyEval (AM_PG Λ z k l) (setEntry h j i w) :=
    funext fun w => (AM_eval_PG Λ z k l _).symm
  rw [e]
  refine AM_sm_slice _ ?_ h hh j i
  intro t ht f hf
  simp only [AM_PG, List.mem_singleton] at ht
  subst ht
  simp only [List.mem_singleton] at hf
  subst hf
  exact ⟨hΛ, hz.ne'⟩

private lemma AM_sm_Q {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) : AM_Sm (AM_Q θ Λ B z h i j k l) := by
  obtain ⟨P, hP, -, hev⟩ := qMat_resPoly D N θ hθ0 hθ1 Λ hΛ B z hz k l
  have e : AM_Q θ Λ B z h i j k l = fun w => resPolyEval P (setEntry h j i w) :=
    funext fun w => (hev _ (AM_slice_herm h hh j i w)).symm
  rw [e]
  refine AM_sm_slice _ ?_ h hh j i
  intro t ht f hf
  rw [((hP t ht).2 f hf).2.2]
  exact ⟨hΛ, hz.ne'⟩

private lemma AM_X_eq {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) :
    AM_X θ Λ B z h i j = fun w => resPolyEval (AM_PX D N θ Λ B z) (setEntry h j i w) :=
  funext fun w => (AM_eval_PX D N θ Λ B hΛ z hz _ (AM_slice_herm h hh j i w)).symm

private lemma AM_sm_X {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) : AM_Sm (AM_X θ Λ B z h i j) := by
  rw [AM_X_eq θ Λ B hΛ z hz h hh i j]
  exact AM_sm_slice _ (AM_ok_pair hΛ hz (AM_PX_ok D N θ Λ B z)) h hh j i

/-- The first Wirtinger derivatives of the slice of `⟨B H̲G⟩` in the entry `(j, i)`
(`ntr_hgUnder_dW`). -/
private lemma AM_dX {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) :
    dW (AM_X θ Λ B z h i j) = (fun w => (if j = i then 1 / 2 else 1) *
        (((D : ℂ) * N)⁻¹ * AM_F Λ B z h i j i j w - AM_Q θ Λ B z h i j i j w)) ∧
      dWbar (AM_X θ Λ B z h i j) = (fun w => (if j = i then 1 / 2 else 1) *
        (((D : ℂ) * N)⁻¹ * AM_F Λ B z h i j j i w - AM_Q θ Λ B z h i j j i w)) :=
  ⟨funext fun w => (ntr_hgUnder_dW D N θ Λ hΛ B z hz h hh j i w).1,
    funext fun w => (ntr_hgUnder_dW D N θ Λ hΛ B z hz h hh j i w).2⟩

/-- A mixed derivative of order `≥ 1` of the slice of `⟨B H̲G⟩` is `c ((DN)⁻¹ ∂^{(a',b')} (G B)_{kl}
- ∂^{(a',b')} Q_{kl})` with `a' + b' + 1 = a + b` and `(k, l) ∈ {(i, j), (j, i)}`. -/
private lemma AM_wirt_X {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (a b : ℕ) (hab : 1 ≤ a + b) :
    ∃ k l : Idx D N, ∃ a' b' : ℕ, a' + b' + 1 = a + b ∧ ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) ∧
      wirt a b (AM_X θ Λ B z h i j) = fun w => (if j = i then 1 / 2 else 1) *
        (((D : ℂ) * N)⁻¹ * wirt a' b' (AM_F Λ B z h i j k l) w +
          (-1) * wirt a' b' (AM_Q θ Λ B z h i j k l) w) := by
  have hc : ∀ k l, (fun w => (if j = i then (1 / 2 : ℂ) else 1) *
      (((D : ℂ) * N)⁻¹ * AM_F Λ B z h i j k l w - AM_Q θ Λ B z h i j k l w)) =
      fun w => (if j = i then (1 / 2 : ℂ) else 1) * (((D : ℂ) * N)⁻¹ * AM_F Λ B z h i j k l w +
        (-1) * AM_Q θ Λ B z h i j k l w) := fun k l => funext fun w => by ring
  have hlin : ∀ k l a' b', wirt a' b' (fun w => (if j = i then (1 / 2 : ℂ) else 1) *
      (((D : ℂ) * N)⁻¹ * AM_F Λ B z h i j k l w + (-1) * AM_Q θ Λ B z h i j k l w)) =
      fun w => (if j = i then 1 / 2 else 1) *
        (((D : ℂ) * N)⁻¹ * wirt a' b' (AM_F Λ B z h i j k l) w +
          (-1) * wirt a' b' (AM_Q θ Λ B z h i j k l) w) := by
    intro k l a' b'
    have hF := AM_sm_F Λ B hΛ z hz h hh i j k l
    have hQ := AM_sm_Q θ hθ0 hθ1 Λ B hΛ z hz h hh i j k l
    have e1 := AM_wirt_lin hF hQ (((D : ℂ) * N)⁻¹) (-1) a' b'
    have e2 := AM_wirt_lin (AM_sm_add (AM_sm_cmul (((D : ℂ) * N)⁻¹) hF) (AM_sm_cmul (-1) hQ))
      (AM_sm_const 0) (if j = i then (1 / 2 : ℂ) else 1) 0 a' b'
    simp only [zero_mul, add_zero] at e2
    rw [e2, e1]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    refine ⟨i, j, a', 0, by omega, Or.inl ⟨rfl, rfl⟩, ?_⟩
    have : wirt (a' + 1) 0 (AM_X θ Λ B z h i j) = wirt a' 0 (dW (AM_X θ Λ B z h i j)) := by
      unfold wirt; simp only [Function.iterate_zero, id, Function.iterate_succ_apply]
    rw [this, (AM_dX θ Λ B hΛ z hz h hh i j).1, hc, hlin]
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    refine ⟨j, i, a, b', by omega, Or.inr ⟨rfl, rfl⟩, ?_⟩
    have : wirt a (b' + 1) (AM_X θ Λ B z h i j) = wirt a b' (dWbar (AM_X θ Λ B z h i j)) := by
      unfold wirt; rw [Function.iterate_succ_apply]
    rw [this, (AM_dX θ Λ B hΛ z hz h hh i j).2, hc, hlin]

/-! ### Bounds on the derivatives at a point of the good event -/

/-- The constants of `qMat_wirt_le` for all orders. -/
private def AM_QB (D : ℕ) (cq : ℕ → ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, 0 ≤ cq a b ∧ ∀ (N : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, 0 < z.im → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (w : ℂ) (k l : Idx D N) (Γ Υ : ℝ), 1 ≤ Γ → z.im ≤ Υ →
      setEntry h i j w ∈ goodSet Λ z (avgVecs D N Λ B) Γ Υ →
      ‖wirt a b (fun w' => qMat D N θ (Matrix.of (setEntry h i j w')) Λ B z k l) w‖ ≤
        cq a b * (1 + ‖z‖) * Γ ^ (a + b + 1) * (Υ / ((N : ℝ) * z.im))

private lemma AM_QB_exists (D : ℕ) : ∃ cq, AM_QB D cq := by
  choose cq hcq0 hcq using fun a b => qMat_wirt_le D a b
  exact ⟨cq, fun a b => ⟨hcq0 a b, hcq a b⟩⟩

/-- `Σ_{a, b ≤ K} c_{ab}`. -/
private def AM_cQ (cq : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1), cq a b

private lemma AM_cQ_le {D : ℕ} {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) {K a b : ℕ} (ha : a ≤ K)
    (hb : b ≤ K) : cq a b ≤ AM_cQ cq K := by
  unfold AM_cQ
  have h1 : cq a b ≤ ∑ b' ∈ Finset.range (K + 1), cq a b' :=
    Finset.single_le_sum (f := fun b' => cq a b') (fun b' _ => (hcq a b').1)
      (Finset.mem_range.mpr (by omega))
  exact h1.trans (Finset.single_le_sum (f := fun a' => ∑ b' ∈ Finset.range (K + 1), cq a' b')
    (fun a' _ => Finset.sum_nonneg fun b' _ => (hcq a' b').1) (Finset.mem_range.mpr (by omega)))

private lemma AM_cQ_nonneg {D : ℕ} {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (K : ℕ) :
    0 ≤ AM_cQ cq K :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => (hcq a b).1

/-- The standing hypotheses at a Hermitian array `h` in the good event with parameters
`Γ, Υ, λ_Q`. -/
private structure AM_Ctx (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (Γ Υ lam : ℝ) : Prop where
  θ0 : 0 ≤ θ
  θ1 : θ ≤ 1
  hΛ : Λ.IsHermitian
  hΛn : opNorm Λ ≤ 1 / 10
  hB : opNorm B ≤ 1
  hz : 0 < z.im
  hh : (Matrix.of h).IsHermitian
  hΓ : 1 ≤ Γ
  hΥ : z.im ≤ Υ
  good : h ∈ goodSet Λ z (avgVecs D N Λ B) Γ Υ
  hQ : ∀ k l, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ≤ lam

private lemma AM_Ctx.lam_nonneg {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (k : Idx D N) : 0 ≤ lam :=
  (norm_nonneg _).trans (hc.hQ k k)

private lemma AM_Ctx.ups {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam) :
    0 ≤ Υ / ((N : ℝ) * z.im) :=
  div_nonneg (hc.hz.le.trans hc.hΥ) (mul_nonneg (Nat.cast_nonneg _) hc.hz.le)

/-- The forms of both pairs `(Λ, z)`, `(Λ, z̄)` over `avgVecs` are at most `Γ` on the good
event. -/
private lemma AM_Ctx.forms {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam) :
    ∀ q ∈ AM_Ξ Λ z, ∀ x ∈ (avgVecs D N Λ B : Set (Idx D N → ℂ)),
      ∀ y ∈ (avgVecs D N Λ B : Set (Idx D N → ℂ)), ‖resFactorEval (x, y, q.1, q.2) h‖ ≤ Γ := by
  rintro q (rfl | rfl) x hx y hy
  · exact (hc.good x hx y hy).1
  · simp only
    rw [AM_form_conj x y Λ hc.hΛ z h hc.hh, Complex.norm_conj]
    exact (hc.good y hy x hx).1

private lemma AM_F_eq {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j k l : Idx D N) :
    AM_F Λ B z h i j k l = fun w => resPolyEval (AM_PF Λ B z k l) (setEntry h j i w) :=
  funext fun _ => (AM_eval_PF Λ B z k l _).symm

/-- `|∂^{(a,b)} (G B)_{kl}| ≤ (1 + a + b)^{a+b} Γ^{1+a+b}` at `h` on the good event. -/
private lemma AM_jet_F {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (i j k l : Idx D N) (a b : ℕ) :
    ‖wirt a b (AM_F Λ B z h i j k l) (h j i)‖ ≤
      ((1 + a + b : ℕ) : ℝ) ^ (a + b) * Γ ^ (1 + a + b) := by
  rw [AM_F_eq]
  have := resPoly_wirt_le h hc.hh j i (avgVecs D N Λ B : Set (Idx D N → ℂ)) (AM_Ξ Λ z)
    (AM_e_mem D N Λ B j) (AM_e_mem D N Λ B i) (AM_Ξ_pair Λ hc.hΛ z hc.hz) (AM_PF Λ B z k l) 1
    (AM_PF_ok Λ B z k l) Γ hc.hΓ (h j i)
    (by rw [AM_setEntry_self h hc.hh]; exact hc.forms) a b
  have hw : ((AM_PF Λ B z k l).map fun t => ‖t.1‖).sum = 1 := by simp [AM_PF]
  rw [hw, mul_one] at this
  exact this

/-- `|∂^{(a,b)} Q_{kl}| ≤ c_{ab} (1 + |z|) Γ^{a+b+1} Υ/(Nη)` at `h` on the good event. -/
private lemma AM_jet_Q {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (i j k l : Idx D N) (a b : ℕ) :
    ‖wirt a b (AM_Q θ Λ B z h i j k l) (h j i)‖ ≤
      cq a b * (1 + ‖z‖) * Γ ^ (a + b + 1) * (Υ / ((N : ℝ) * z.im)) :=
  (hcq a b).2 N θ hc.θ0 hc.θ1 Λ hc.hΛ hc.hΛn B hc.hB z hc.hz h hc.hh j i (h j i) k l Γ Υ hc.hΓ
    hc.hΥ (by rw [AM_setEntry_self h hc.hh]; exact hc.good)

/-- The value of the slice of `⟨B H̲G⟩` at `w = h_{ji}`. -/
private lemma AM_X_self {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    AM_X θ Λ B z h i j (h j i) = ntr (B * hgUnder D N θ (Matrix.of h) Λ z) := by
  simp only [AM_X, AM_setEntry_self h hh]

/-- The first derivatives of the slice of `⟨B H̲G⟩` at `h` on the good event:
`|∂_w| ≤ (DN)⁻¹ |(G B)_{ij}| + λ_Q`, `|∂_{w̄}| ≤ (DN)⁻¹ |(G B)_{ji}| + λ_Q`. -/
private lemma AM_jet_X1 {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (i j : Idx D N) :
    ‖dW (AM_X θ Λ B z h i j) (h j i)‖ ≤
        ((D : ℝ) * N)⁻¹ * ‖(res (Matrix.of h + Λ) z * B) i j‖ + lam ∧
      ‖dWbar (AM_X θ Λ B z h i j) (h j i)‖ ≤
        ((D : ℝ) * N)⁻¹ * ‖(res (Matrix.of h + Λ) z * B) j i‖ + lam := by
  have hcn : ‖(if j = i then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hninv : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have key : ∀ k l : Idx D N, ‖(if j = i then (1 / 2 : ℂ) else 1) *
      (((D : ℂ) * N)⁻¹ * AM_F Λ B z h i j k l (h j i) - AM_Q θ Λ B z h i j k l (h j i))‖ ≤
      ((D : ℝ) * N)⁻¹ * ‖(res (Matrix.of h + Λ) z * B) k l‖ + lam := by
    intro k l
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hcn).trans ?_
    refine (norm_sub_le _ _).trans ?_
    simp only [AM_F, AM_Q, AM_setEntry_self h hc.hh, norm_mul, hninv]
    exact add_le_add le_rfl (hc.hQ k l)
  obtain ⟨e1, e2⟩ := AM_dX θ Λ B hc.hΛ z hc.hz h hc.hh i j
  rw [e1, e2]
  exact ⟨key i j, key j i⟩

/-- The bound `β_K = (DN)⁻¹ K^K + λ_Q + c_K (1 + |z|) Υ/(Nη)` on the derivatives of order
`1, …, K` of the slice of `⟨B H̲G⟩` (in units `Γ^{a+b}`). -/
private def AM_beta (D N : ℕ) (cq : ℕ → ℕ → ℝ) (K : ℕ) (z : ℂ) (Υ lam : ℝ) : ℝ :=
  ((D : ℝ) * N)⁻¹ * (K : ℝ) ^ K + lam + AM_cQ cq K * (1 + ‖z‖) * (Υ / ((N : ℝ) * z.im))

/-- `|∂^{(a,b)} ⟨B H̲G⟩| ≤ Γ^{a+b} β_K` for `1 ≤ a + b ≤ K` at `h` on the good event. -/
private lemma AM_jet_X {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (K : ℕ) (i j : Idx D N) (a b : ℕ) (hab : 1 ≤ a + b)
    (hK : a + b ≤ K) :
    ‖wirt a b (AM_X θ Λ B z h i j) (h j i)‖ ≤ Γ ^ (a + b) * AM_beta D N cq K z Υ lam := by
  obtain ⟨k, l, a', b', habe, -, e⟩ :=
    AM_wirt_X θ hc.θ0 hc.θ1 Λ B hc.hΛ z hc.hz h hc.hh i j a b hab
  rw [e]
  have hcn : ‖(if j = i then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hninv : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hΓ0 : 0 ≤ Γ := by linarith [hc.hΓ]
  have hΓ1 : 1 ≤ Γ ^ (a + b) := one_le_pow₀ hc.hΓ
  have hlam : 0 ≤ lam := hc.lam_nonneg i
  have hups := hc.ups
  have hcQ := AM_cQ_nonneg hcq K
  have hF := AM_jet_F hc i j k l a' b'
  have hFK : ((1 + a' + b' : ℕ) : ℝ) ^ (a' + b') * Γ ^ (1 + a' + b') ≤
      (K : ℝ) ^ K * Γ ^ (a + b) := by
    have e1 : 1 + a' + b' = a + b := by omega
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    calc ((a + b : ℕ) : ℝ) ^ (a' + b') ≤ (K : ℝ) ^ (a' + b') :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hK) _
      _ ≤ (K : ℝ) ^ K := pow_le_pow_right₀ hK1 (by omega)
  have hQ : ‖wirt a' b' (AM_Q θ Λ B z h i j k l) (h j i)‖ ≤
      Γ ^ (a + b) * (lam + AM_cQ cq K * (1 + ‖z‖) * (Υ / ((N : ℝ) * z.im))) := by
    rcases Nat.eq_zero_or_pos (a' + b') with h0 | hpos
    · have ha' : a' = 0 := by omega
      have hb' : b' = 0 := by omega
      subst ha' hb'
      simp only [wirt, Function.iterate_zero, id, AM_Q, AM_setEntry_self h hc.hh]
      calc ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ≤ lam := hc.hQ k l
        _ ≤ Γ ^ (a + b) * lam := le_mul_of_one_le_left hlam hΓ1
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
            (by positivity)
    · refine (AM_jet_Q hc hcq i j k l a' b').trans ?_
      have e1 : a' + b' + 1 = a + b := habe
      rw [e1]
      have hc' : cq a' b' ≤ AM_cQ cq K := AM_cQ_le hcq (by omega) (by omega)
      have : cq a' b' * (1 + ‖z‖) * Γ ^ (a + b) * (Υ / ((N : ℝ) * z.im)) ≤
          Γ ^ (a + b) * (AM_cQ cq K * (1 + ‖z‖) * (Υ / ((N : ℝ) * z.im))) := by
        have := norm_nonneg z
        calc cq a' b' * (1 + ‖z‖) * Γ ^ (a + b) * (Υ / ((N : ℝ) * z.im))
            = Γ ^ (a + b) * (cq a' b' * (1 + ‖z‖) * (Υ / ((N : ℝ) * z.im))) := by ring
          _ ≤ _ := by gcongr
      exact this.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hlam) (by positivity))
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) hcn).trans ?_
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hninv, norm_neg, norm_one, one_mul]
  have hν : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  unfold AM_beta
  calc ((D : ℝ) * N)⁻¹ * ‖wirt a' b' (AM_F Λ B z h i j k l) (h j i)‖ +
        ‖wirt a' b' (AM_Q θ Λ B z h i j k l) (h j i)‖
      ≤ ((D : ℝ) * N)⁻¹ * ((K : ℝ) ^ K * Γ ^ (a + b)) +
        Γ ^ (a + b) * (lam + AM_cQ cq K * (1 + ‖z‖) * (Υ / ((N : ℝ) * z.im))) :=
        add_le_add (mul_le_mul_of_nonneg_left (hF.trans hFK) hν) hQ
    _ = _ := by ring

private lemma AM_beta_nonneg {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (K : ℕ) (k : Idx D N) :
    0 ≤ AM_beta D N cq K z Υ lam := by
  have := hc.lam_nonneg k
  have := hc.ups
  have := AM_cQ_nonneg hcq K
  unfold AM_beta
  positivity

/-- The bound on the mixed derivatives of order `a + b ≤ K` of the integrand
`f = (G B)_{ji} ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p` at `h` on the good event:
`|∂^{(a,b)} f| ≤ Γ^{a+b} (2p)^{a+b} (1 + K)^K Γ (|⟨B H̲G⟩| + β_K)^{2p-1}`. -/
private lemma AM_jet_f {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (K : ℕ) (i j : Idx D N) (p : ℕ) (hp : 1 ≤ p)
    (a b : ℕ) (hK : a + b ≤ K) :
    ‖wirt a b (AM_f θ Λ B z h i j p) (h j i)‖ ≤ Γ ^ (a + b) * (2 * p : ℝ) ^ (a + b) *
      ((((1 + K : ℕ) : ℝ) ^ K * Γ) * (‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ +
        AM_beta D N cq K z Υ lam) ^ (2 * p - 1)) := by
  set x := ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ with hx
  set β := AM_beta D N cq K z Υ lam with hβ
  have hβ0 : 0 ≤ β := AM_beta_nonneg hc hcq K i
  have hx0 : 0 ≤ x := norm_nonneg _
  have hΓ0 : 0 ≤ Γ := by linarith [hc.hΓ]
  have hsX := AM_sm_X θ Λ B hc.hΛ z hc.hz h hc.hh i j
  have hsF := AM_sm_F Λ B hc.hΛ z hc.hz h hc.hh i j j i
  have hg : ∀ a b, a + b ≤ K → ‖wirt a b (AM_F Λ B z h i j j i) (h j i)‖ ≤
      Γ ^ (a + b) * 1 ^ (a + b) * (((1 + K : ℕ) : ℝ) ^ K * Γ) := by
    intro a b hab
    refine (AM_jet_F hc i j j i a b).trans ?_
    have h1 : ((1 + a + b : ℕ) : ℝ) ^ (a + b) ≤ ((1 + K : ℕ) : ℝ) ^ K := by
      calc ((1 + a + b : ℕ) : ℝ) ^ (a + b) ≤ ((1 + K : ℕ) : ℝ) ^ (a + b) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega)) _
        _ ≤ ((1 + K : ℕ) : ℝ) ^ K :=
            pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 1 + K)) hab
    have hΓe : Γ ^ (1 + a + b) = Γ ^ (a + b) * Γ := by rw [← pow_succ]; congr 1; omega
    rw [hΓe]
    calc ((1 + a + b : ℕ) : ℝ) ^ (a + b) * (Γ ^ (a + b) * Γ)
        ≤ ((1 + K : ℕ) : ℝ) ^ K * (Γ ^ (a + b) * Γ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Γ ^ (a + b) * 1 ^ (a + b) * (((1 + K : ℕ) : ℝ) ^ K * Γ) := by rw [one_pow]; ring
  have hX : ∀ a b, a + b ≤ K → ‖wirt a b (AM_X θ Λ B z h i j) (h j i)‖ ≤ Γ ^ (a + b) * (x + β) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp only [wirt, Function.iterate_zero, id, AM_X_self θ Λ B z h hc.hh, Nat.add_zero,
        pow_zero, one_mul]
      rw [← hx]
      linarith
    · refine (AM_jet_X hc hcq K i j a b hpos hab).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXc : ∀ a b, a + b ≤ K →
      ‖wirt a b (fun w => starRingEnd ℂ (AM_X θ Λ B z h i j w)) (h j i)‖ ≤
        Γ ^ (a + b) * (x + β) := by
    intro a b hab
    rw [AM_wirt_conj hsX, Complex.norm_conj, add_comm a b]
    exact hX b a (by omega)
  have h1 := AM_pow_jet hsX (h j i) Γ (x + β) K hΓ0 (by positivity) hX (p - 1)
  have h2 := AM_pow_jet (AM_sm_conj hsX) (h j i) Γ (x + β) K hΓ0 (by positivity) hXc p
  have h3 := AM_LB hsF (AM_sm_pow hsX (p - 1)) (h j i) Γ 1 (p - 1 : ℕ) _ _ K hΓ0 zero_le_one
    (by positivity) hg h1
  have h4 := AM_LB (AM_sm_mul hsF (AM_sm_pow hsX (p - 1))) (AM_sm_pow (AM_sm_conj hsX) p) (h j i)
    Γ (1 + ((p - 1 : ℕ) : ℝ)) p _ _ K hΓ0 (by positivity) (by positivity) h3 h2 a b hK
  have e1 : (1 + ((p - 1 : ℕ) : ℝ)) + p = 2 * p := by
    rw [Nat.cast_sub hp]; push_cast; ring
  have e2 : (x + β) ^ (p - 1) * (x + β) ^ p = (x + β) ^ (2 * p - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e1] at h4
  unfold AM_f
  calc _ ≤ _ := h4
    _ = _ := by rw [← e2]; ring

/-- The first derivatives of `f' = ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p` at `h`:
`|∂ f'| ≤ (2p - 1) β x^{2p-2}` with `x = |⟨B H̲G⟩|` and `β = (DN)⁻¹ (|(G B)_{ij}| + |(G B)_{ji}|)
+ λ_Q`. -/
private lemma AM_jet_f1 {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (i j : Idx D N) (p : ℕ) (hp : 1 ≤ p) :
    ‖dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) * starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p)
        (h j i)‖ ≤ (2 * p - 1 : ℝ) * (((D : ℝ) * N)⁻¹ * (‖(res (Matrix.of h + Λ) z * B) i j‖ +
          ‖(res (Matrix.of h + Λ) z * B) j i‖) + lam) *
          ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∧
      ‖dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) * starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p)
        (h j i)‖ ≤ (2 * p - 1 : ℝ) * (((D : ℝ) * N)⁻¹ * (‖(res (Matrix.of h + Λ) z * B) i j‖ +
          ‖(res (Matrix.of h + Λ) z * B) j i‖) + lam) *
          ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) := by
  set x := ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ with hx
  set β := ((D : ℝ) * N)⁻¹ * (‖(res (Matrix.of h + Λ) z * B) i j‖ +
    ‖(res (Matrix.of h + Λ) z * B) j i‖) + lam with hβ
  have hsX := AM_sm_X θ Λ B hc.hΛ z hc.hz h hc.hh i j
  have hν : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  obtain ⟨d1, d2⟩ := AM_jet_X1 hc i j
  have hb1 : ‖dW (AM_X θ Λ B z h i j) (h j i)‖ ≤ β := d1.trans (by
    rw [hβ]; gcongr; exact le_add_of_nonneg_right (norm_nonneg _))
  have hb2 : ‖dWbar (AM_X θ Λ B z h i j) (h j i)‖ ≤ β := d2.trans (by
    rw [hβ]; gcongr; exact le_add_of_nonneg_left (norm_nonneg _))
  have hxv : ‖AM_X θ Λ B z h i j (h j i)‖ ≤ x := by rw [AM_X_self θ Λ B z h hc.hh]
  have hxc : ‖starRingEnd ℂ (AM_X θ Λ B z h i j (h j i))‖ ≤ x := by
    rw [Complex.norm_conj]; exact hxv
  have hcd := dW_conj (hsX.diff (h j i))
  have hc1 : ‖dW (fun w => starRingEnd ℂ (AM_X θ Λ B z h i j w)) (h j i)‖ ≤ β := by
    rw [hcd.1, Complex.norm_conj]; exact hb2
  have hc2 : ‖dWbar (fun w => starRingEnd ℂ (AM_X θ Λ B z h i j w)) (h j i)‖ ≤ β := by
    rw [hcd.2, Complex.norm_conj]; exact hb1
  obtain ⟨p1, p2⟩ := AM_pow_d1 hsX (h j i) x β hxv hb1 hb2 (p - 1)
  obtain ⟨q1, q2⟩ := AM_pow_d1 (AM_sm_conj hsX) (h j i) x β hxc hc1 hc2 p
  have hx0 : 0 ≤ x := norm_nonneg _
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hb1
  have hpow1 : ‖AM_X θ Λ B z h i j (h j i) ^ (p - 1)‖ ≤ x ^ (p - 1) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxv _
  have hpow2 : ‖starRingEnd ℂ (AM_X θ Λ B z h i j (h j i)) ^ p‖ ≤ x ^ p := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxc _
  have key : ∀ A C : ℂ, ‖A‖ ≤ ((p - 1 : ℕ) : ℝ) * β * x ^ (p - 1 - 1) → ‖C‖ ≤ p * β * x ^ (p - 1) →
      ‖A * starRingEnd ℂ (AM_X θ Λ B z h i j (h j i)) ^ p +
        AM_X θ Λ B z h i j (h j i) ^ (p - 1) * C‖ ≤ (2 * p - 1 : ℝ) * β * x ^ (2 * p - 2) := by
    intro A C hA hC
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have t1 : ‖A‖ * ‖starRingEnd ℂ (AM_X θ Λ B z h i j (h j i)) ^ p‖ ≤
        ((p - 1 : ℕ) : ℝ) * β * x ^ (p - 1 - 1) * x ^ p :=
      mul_le_mul hA hpow2 (norm_nonneg _) (by positivity)
    have t2 : ‖AM_X θ Λ B z h i j (h j i) ^ (p - 1)‖ * ‖C‖ ≤ x ^ (p - 1) * (p * β * x ^ (p - 1)) :=
      mul_le_mul hpow1 hC (norm_nonneg _) (by positivity)
    have e2 : x ^ (p - 1) * (p * β * x ^ (p - 1)) = p * β * x ^ (2 * p - 2) := by
      rw [show 2 * p - 2 = (p - 1) + (p - 1) by omega, pow_add]; ring
    rcases Nat.lt_or_ge p 2 with hp2 | hp2
    · have hp1 : p = 1 := by omega
      subst hp1
      simp only [Nat.sub_self, CharP.cast_eq_zero, zero_mul] at t1 t2 e2 ⊢
      push_cast at t2 e2 ⊢
      nlinarith
    · have e1 : ((p - 1 : ℕ) : ℝ) * β * x ^ (p - 1 - 1) * x ^ p =
          ((p : ℝ) - 1) * β * x ^ (2 * p - 2) := by
        rw [Nat.cast_sub hp, show 2 * p - 2 = (p - 1 - 1) + p by omega, pow_add]
        push_cast; ring
      rw [e1] at t1
      rw [e2] at t2
      nlinarith
  have e : (fun w => AM_X θ Λ B z h i j w ^ (p - 1) * starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) =
      fun w => (fun w => AM_X θ Λ B z h i j w ^ (p - 1)) w *
        (fun w => starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) w := rfl
  rw [e, AM_der_dW.mul _ _ (AM_sm_pow hsX _) (AM_sm_pow (AM_sm_conj hsX) _),
    AM_der_dWbar.mul _ _ (AM_sm_pow hsX _) (AM_sm_pow (AM_sm_conj hsX) _)]
  exact ⟨key _ _ p1 q1, key _ _ p2 q2⟩

/-! ### Crude bounds, Ward sums -/

/-- A resolvent polynomial whose forms are at most `c ≥ 1` is at most `(Σ_t |c_t|) c^m`. -/
private lemma AM_eval_le {D N : ℕ} {V : Set (Idx D N → ℂ)}
    {Ξ : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)} {m : ℕ} {P : ResPoly D N} (hP : AM_ok V Ξ m P)
    (h : Idx D N → Idx D N → ℂ) (c : ℝ) (hc : 1 ≤ c)
    (hf : ∀ q ∈ Ξ, ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, q.1, q.2) h‖ ≤ c) :
    ‖resPolyEval P h‖ ≤ AM_wt P * c ^ m := by
  have hmono : ∀ mo : ResMono D N, (∀ f ∈ mo, f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2 ∈ Ξ) →
      ‖resMonoEval mo h‖ ≤ c ^ mo.length := by
    intro mo
    induction mo with
    | nil => intro _; simp [resMonoEval]
    | cons f mo ih =>
      intro hm
      simp only [resMonoEval, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
      rw [norm_mul, pow_succ, mul_comm (c ^ mo.length)]
      obtain ⟨h1, h2, h3⟩ := hm f List.mem_cons_self
      exact mul_le_mul (hf f.2.2 h3 f.1 h1 f.2.1 h2)
        (ih fun g hg => hm g (List.mem_cons_of_mem _ hg))
        (norm_nonneg _) (by linarith)
  induction P with
  | nil => simp [resPolyEval, AM_wt]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    simp only [resPolyEval, List.map_cons, List.sum_cons, AM_wt] at ih' ⊢
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, add_mul]
    refine add_le_add ?_ ih'
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (hmono t.2 (hP t List.mem_cons_self).2).trans
      (pow_le_pow_right₀ hc (hP t List.mem_cons_self).1)

/-- Every Hermitian array satisfies the standing hypotheses with `Γ = Υ = c` for `c ≥ 1`,
`c ≥ η⁻¹`, `c ≥ η`, and `λ_Q = c_{00} (1 + |z|) c · c/(Nη)`. -/
private lemma AM_crude_ctx {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΛ : Λ.IsHermitian)
    (hΛn : opNorm Λ ≤ 1 / 10) (hB : opNorm B ≤ 1) (hz : 0 < z.im)
    (hh : (Matrix.of h).IsHermitian) {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (c : ℝ) (hc1 : 1 ≤ c)
    (hcη : z.im⁻¹ ≤ c) (hηc : z.im ≤ c) :
    AM_Ctx D N θ Λ B z h c c (cq 0 0 * (1 + ‖z‖) * c ^ (0 + 0 + 1) * (c / ((N : ℝ) * z.im))) := by
  have hΛ1 : opNorm Λ ≤ 1 := hΛn.trans (by norm_num)
  have hg : h ∈ goodSet Λ z (avgVecs D N Λ B) c c := AM_crude_good Λ B hΛ hΛ1 hB z hz h hh c hcη
  refine ⟨hθ0, hθ1, hΛ, hΛn, hB, hz, hh, hc1, hηc, hg, fun k l => ?_⟩
  have := (hcq 0 0).2 N θ hθ0 hθ1 Λ hΛ hΛn B hB z hz h hh k k (h k k) k l c c hc1 hηc
    (by rw [AM_setEntry_self h hh]; exact hg)
  simpa only [wirt, Function.iterate_zero, id, AM_setEntry_self h hh] using this

/-- Ward's identity (2.32) [eq_Ward] for the columns of `G B`: `Σ_k |(G B)_{kl}|² ≤ Υ/η` on the
good event. -/
private lemma AM_ward_F {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (l : Idx D N) : ∑ k, ‖(res (Matrix.of h + Λ) z * B) k l‖ ^ 2 ≤ Υ / z.im := by
  have hw := ward_vec (Matrix.of h + Λ) (hc.hh.add hc.hΛ) z hc.hz (B *ᵥ Pi.single l 1)
  have e : ∀ k, (res (Matrix.of h + Λ) z *ᵥ (B *ᵥ Pi.single l 1)) k =
      (res (Matrix.of h + Λ) z * B) k l := by
    intro k
    rw [Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [e] at hw
  rw [hw]
  exact div_le_div_of_nonneg_right (hc.good _ (AM_Be_mem D N Λ B l) _ (AM_Be_mem D N Λ B l)).2
    hc.hz.le

/-- Ward's identity (2.32) [eq_Ward] for the columns of `G`: `Σ_k |G_{kl}|² ≤ Υ/η` on the good
event. -/
private lemma AM_ward_G {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (l : Idx D N) : ∑ k, ‖res (Matrix.of h + Λ) z k l‖ ^ 2 ≤ Υ / z.im := by
  have hw := ward_vec (Matrix.of h + Λ) (hc.hh.add hc.hΛ) z hc.hz (Pi.single l 1)
  have e : ∀ k, (res (Matrix.of h + Λ) z *ᵥ Pi.single l 1) k = res (Matrix.of h + Λ) z k l := by
    intro k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [e] at hw
  rw [hw]
  exact div_le_div_of_nonneg_right (hc.good _ (AM_e_mem D N Λ B l) _ (AM_e_mem D N Λ B l)).2
    hc.hz.le

/-- From column bounds `Σ_k f_{kl}² ≤ U`: `Σ_{i,j} f_{ij}² ≤ DN U` and `(Σ_{i,j} f_{ij})² ≤
(DN)² DN U`. -/
private lemma AM_sums {D N : ℕ} (f : Idx D N → Idx D N → ℝ) (U : ℝ)
    (hU : ∀ l, ∑ k, f k l ^ 2 ≤ U) :
    ∑ i, ∑ j, f i j ^ 2 ≤ (D : ℝ) * N * U ∧
      (∑ i, ∑ j, f i j) ^ 2 ≤ ((D : ℝ) * N) ^ 2 * ((D : ℝ) * N * U) := by
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have h2 : ∑ i, ∑ j, f i j ^ 2 ≤ (D : ℝ) * N * U := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, f i j ^ 2 ≤ ∑ _j : Idx D N, U := Finset.sum_le_sum fun j _ => hU j
      _ = (D : ℝ) * N * U := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  refine ⟨h2, ?_⟩
  have e : ∑ i, ∑ j, f i j = ∑ q ∈ (Finset.univ : Finset (Idx D N)) ×ˢ Finset.univ, f q.1 q.2 :=
    (Finset.sum_product (f := fun q : Idx D N × Idx D N => f q.1 q.2) _ _).symm
  have e2 : ∑ i, ∑ j, f i j ^ 2 =
      ∑ q ∈ (Finset.univ : Finset (Idx D N)) ×ˢ Finset.univ, f q.1 q.2 ^ 2 :=
    (Finset.sum_product (f := fun q : Idx D N × Idx D N => f q.1 q.2 ^ 2) _ _).symm
  rw [e]
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  rw [← e2, Finset.card_product, Finset.card_univ]
  push_cast
  rw [hcard, sq]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The Ward sums on the good event with `ζ = (Υ/(Nη))^{1/2}`: `Σ_{i,j} |(G B)_{ij}|² ≤ D N² ζ²`,
`Σ_{i,j} |(G B)_{ij}| ≤ D² N² ζ`, `Σ_{i,j} |G_{ij}| ≤ D² N² ζ`. -/
private lemma AM_ward_sums {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam) :
    ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2 ≤
        (D : ℝ) * N ^ 2 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 2 ∧
      ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ≤
        (D : ℝ) ^ 2 * N ^ 2 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ∧
      ∑ i, ∑ j, ‖res (Matrix.of h + Λ) z i j‖ ≤
        (D : ℝ) ^ 2 * N ^ 2 * Real.sqrt (Υ / ((N : ℝ) * z.im)) := by
  set ζ := Real.sqrt (Υ / ((N : ℝ) * z.im)) with hζ
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU : Υ / z.im = (N : ℝ) * ζ ^ 2 := by
    rw [hζ, Real.sq_sqrt hc.ups]
    field_simp
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hfin : ∀ f : Idx D N → Idx D N → ℝ, (∀ i j, 0 ≤ f i j) → (∀ l, ∑ k, f k l ^ 2 ≤ Υ / z.im) →
      ∑ i, ∑ j, f i j ≤ (D : ℝ) ^ 2 * N ^ 2 * ζ := by
    intro f hf0 hfl
    have h2 := (AM_sums f _ hfl).2
    rw [hU] at h2
    have hs0 : 0 ≤ ∑ i, ∑ j, f i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      hf0 i j
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      simp
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    refine (pow_le_pow_iff_left₀ hs0 (by positivity) two_ne_zero).mp (h2.trans ?_)
    have : ((D : ℝ) * N) ^ 2 * ((D : ℝ) * N * (N * ζ ^ 2)) =
        (D : ℝ) ^ 3 * N ^ 4 * ζ ^ 2 := by ring
    rw [this]
    have : ((D : ℝ) ^ 2 * N ^ 2 * ζ) ^ 2 = (D : ℝ) ^ 4 * N ^ 4 * ζ ^ 2 := by ring
    rw [this]
    have : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
    gcongr
  refine ⟨?_, hfin _ (fun i j => norm_nonneg _) (AM_ward_F hc),
    hfin _ (fun i j => norm_nonneg _) (AM_ward_G hc)⟩
  have := (AM_sums (fun i j => ‖(res (Matrix.of h + Λ) z * B) i j‖) _ (AM_ward_F hc)).1
  rw [hU] at this
  calc _ ≤ _ := this
    _ = (D : ℝ) * N ^ 2 * ζ ^ 2 := by ring

/-! ### The integrand as a resolvent polynomial, integrability -/

/-- The polynomial of `f = (G B)_{ji} ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p`. -/
private def AM_Pf (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (i j : Idx D N) (p : ℕ) : ResPoly D N :=
  resPolyMul (resPolyMul (AM_PF Λ B z j i) (AM_pow (AM_PX D N θ Λ B z) (p - 1)))
    (AM_pow (resPolyStar (AM_PX D N θ Λ B z)) p)

private lemma AM_Pf_ok (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (i j : Idx D N) (p : ℕ) :
    AM_ok (avgVecs D N Λ B : Set (Idx D N → ℂ)) (AM_Ξ Λ z) (1 + (p - 1) * 2 + p * 2)
      (AM_Pf D N θ Λ B z i j p) :=
  AM_ok_mul (AM_ok_mul (AM_PF_ok Λ B z j i) (AM_ok_pow (AM_PX_ok D N θ Λ B z) _))
    (AM_ok_pow (AM_ok_star (AM_Ξ_conj Λ z) (AM_PX_ok D N θ Λ B z)) _)

private lemma AM_Pf_wt (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (i j : Idx D N) (p : ℕ) :
    AM_wt (AM_Pf D N θ Λ B z i j p) =
      AM_wt (AM_PX D N θ Λ B z) ^ (p - 1) * AM_wt (AM_PX D N θ Λ B z) ^ p := by
  rw [AM_Pf, AM_wt_mul, AM_wt_mul, AM_wt_pow, AM_wt_pow, AM_wt_star]
  simp [AM_PF, AM_wt]

/-- On a Hermitian array the slice of the integrand is the slice of `AM_Pf`. -/
private lemma AM_f_eq {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (p : ℕ) :
    AM_f θ Λ B z h i j p = fun w => resPolyEval (AM_Pf D N θ Λ B z i j p) (setEntry h j i w) := by
  funext w
  have hw := AM_slice_herm h hh j i w
  have hPX : ∀ t ∈ AM_PX D N θ Λ B z, ∀ f ∈ t.2, f.2.2.1.IsHermitian := fun t ht f hf =>
    (AM_ok_pair hΛ hz (AM_PX_ok D N θ Λ B z) t ht f hf).1
  rw [AM_Pf, resPolyEval_mul, resPolyEval_mul, AM_eval_pow, AM_eval_pow,
    resPolyEval_star _ hPX _ hw, AM_eval_PF, AM_eval_PX D N θ Λ B hΛ z hz _ hw]
  rfl

/-- On Hermitian arrays `|⟨B H̲G⟩| ≤ (3 + |z|) c²` when the forms are at most `c ≥ 1`. -/
private lemma AM_X_crude {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {c lam : ℝ} (hc : AM_Ctx D N θ Λ B z h c c lam) :
    ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ≤ (3 + ‖z‖) * c ^ 2 := by
  rw [← AM_eval_PX D N θ Λ B hc.hΛ z hc.hz h hc.hh]
  refine (AM_eval_le (AM_PX_ok D N θ Λ B z) h c hc.hΓ hc.forms).trans ?_
  exact mul_le_mul_of_nonneg_right (AM_PX_wt D N θ hc.θ0 hc.θ1 Λ B hc.hB z).1 (by positivity)

/-- The crude constant `β_K` with `Γ = Υ = c`. -/
private lemma AM_beta_crude {D N : ℕ} (cq : ℕ → ℕ → ℝ) (K : ℕ) (z : ℂ) (c : ℝ) (hN : 1 ≤ N)
    (hc1 : 1 ≤ c) (hcη : z.im⁻¹ ≤ c) (hz : 0 < z.im) (hcq : 0 ≤ AM_cQ cq K) (hcq0 : 0 ≤ cq 0 0)
    (hD : 1 ≤ D) :
    AM_beta D N cq K z c (cq 0 0 * (1 + ‖z‖) * c ^ (0 + 0 + 1) * (c / ((N : ℝ) * z.im))) ≤
      ((K : ℝ) ^ K + (cq 0 0 + AM_cQ cq K) * (1 + ‖z‖) * c ^ 2) * c := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hν : ((D : ℝ) * N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hcN : c / ((N : ℝ) * z.im) ≤ c * c := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ c * z.im := by
      have := mul_le_mul_of_nonneg_right hcη hz.le
      rwa [inv_mul_cancel₀ hz.ne'] at this
    have h2 : 1 ≤ (N : ℝ) * (c * z.im) := by nlinarith
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * ((N : ℝ) * (c * z.im)) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = c * c * ((N : ℝ) * z.im) := by ring
  unfold AM_beta
  have hz0 := norm_nonneg z
  have hKK : (0 : ℝ) ≤ (K : ℝ) ^ K := by positivity
  have e1 : ((D : ℝ) * N)⁻¹ * (K : ℝ) ^ K ≤ (K : ℝ) ^ K * c := by nlinarith
  have e2 : cq 0 0 * (1 + ‖z‖) * c ^ (0 + 0 + 1) * (c / ((N : ℝ) * z.im)) ≤
      cq 0 0 * (1 + ‖z‖) * c ^ 2 * c := by
    simp only [zero_add, pow_one]
    have : 0 ≤ cq 0 0 * (1 + ‖z‖) * c := by positivity
    calc cq 0 0 * (1 + ‖z‖) * c * (c / ((N : ℝ) * z.im)) ≤ cq 0 0 * (1 + ‖z‖) * c * (c * c) :=
          mul_le_mul_of_nonneg_left hcN this
      _ = _ := by ring
  have e3 : AM_cQ cq K * (1 + ‖z‖) * (c / ((N : ℝ) * z.im)) ≤
      AM_cQ cq K * (1 + ‖z‖) * c ^ 2 * c := by
    have : 0 ≤ AM_cQ cq K * (1 + ‖z‖) := by positivity
    calc AM_cQ cq K * (1 + ‖z‖) * (c / ((N : ℝ) * z.im)) ≤ AM_cQ cq K * (1 + ‖z‖) * (c * c) :=
          mul_le_mul_of_nonneg_left hcN this
      _ ≤ AM_cQ cq K * (1 + ‖z‖) * c ^ 2 * c := by
          have hcc : c * c ≤ c ^ 2 * c := by nlinarith
          rw [mul_assoc (AM_cQ cq K * (1 + ‖z‖))]
          exact mul_le_mul_of_nonneg_left hcc this
  nlinarith

/-- The integrands of `avgTerm` are integrable. -/
private lemma AM_int_wirt {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (hB : opNorm B ≤ 1) {z : ℂ} (hz : 0 < z.im) (c : ℝ) (hc1 : 1 ≤ c) (hcη : z.im⁻¹ ≤ c)
    (hηc : z.im ≤ c) (i j : Idx D N) (p : ℕ) (hp : 1 ≤ p) (a b : ℕ) :
    Integrable (fun h => wirt a b (AM_f θ Λ B z h i j p) (h j i)) μ := by
  have := hμ.prob
  obtain ⟨cq, hcq⟩ := AM_QB_exists D
  have hP := AM_ok_pair hΛ hz (AM_Pf_ok D N θ Λ B z i j p)
  have hmeas : AEStronglyMeasurable (fun h => wirt a b (AM_f θ Λ B z h i j p) (h j i)) μ := by
    refine (AM_meas_poly ((resPolyD j i (if j = i then 1 / 2 else 1))^[a]
      ((resPolyD i j (if j = i then 1 / 2 else 1))^[b]
        (AM_Pf D N θ Λ B z i j p)))).aestronglyMeasurable.congr ?_
    filter_upwards [hμ.herm] with h hh
    rw [AM_f_eq θ Λ B hΛ z hz h hh i j p, resPoly_wirt h hh j i _ hP a b]
    simp only [AM_setEntry_self h hh]
  have hD : 1 ≤ D := i.1.pos
  have hN : 1 ≤ N := i.2.pos
  set lc := cq 0 0 * (1 + ‖z‖) * c ^ (0 + 0 + 1) * (c / ((N : ℝ) * z.im)) with hlc
  set bc := ((((a + b : ℕ) : ℝ) ^ (a + b) + (cq 0 0 + AM_cQ cq (a + b)) * (1 + ‖z‖) * c ^ 2) * c)
  refine Integrable.mono' (integrable_const (c ^ (a + b) * (2 * p : ℝ) ^ (a + b) *
    ((((1 + (a + b) : ℕ) : ℝ) ^ (a + b) * c) * ((3 + ‖z‖) * c ^ 2 + bc) ^ (2 * p - 1))))
    hmeas ?_
  filter_upwards [hμ.herm] with h hh
  have hctx := AM_crude_ctx hθ0 hθ1 hΛ hΛn hB hz hh hcq c hc1 hcη hηc
  refine (AM_jet_f hctx hcq (a + b) i j p hp a b le_rfl).trans ?_
  have hx := AM_X_crude hctx
  have hb := AM_beta_crude cq (a + b) z c hN hc1 hcη hz (AM_cQ_nonneg hcq _) (hcq 0 0).1 hD
  have hb0 := AM_beta_nonneg hctx hcq (a + b) i
  gcongr

/-- A bound on `∫ F` from `F ≤ G` off an event `S` of probability at most `ε₀` and `F ≤ C`
everywhere: `∫ F ≤ ∫ G + C ε₀^{1/2}`. -/
private lemma AM_split {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (F Gd : α → ℝ) (S : Set α) (Cr ε₀ : ℝ) (hGd : Integrable Gd μ) (hGd0 : ∀ x, 0 ≤ Gd x)
    (hCr : 0 ≤ Cr) (hS : μ S ≤ ENNReal.ofReal ε₀) (hF0 : ∀ᵐ x ∂μ, 0 ≤ F x)
    (hgood : ∀ᵐ x ∂μ, x ∉ S → F x ≤ Gd x) (hbad : ∀ᵐ x ∂μ, F x ≤ Cr) :
    ∫ x, F x ∂μ ≤ ∫ x, Gd x ∂μ + Cr * Real.sqrt ε₀ := by
  set T := toMeasurable μ S with hTdef
  have hT : MeasurableSet T := measurableSet_toMeasurable μ S
  have hST : S ⊆ T := subset_toMeasurable μ S
  have hμT : μ T = μ S := measure_toMeasurable S
  have hint : Integrable (fun x => Gd x + T.indicator (fun _ => Cr) x) μ :=
    hGd.add ((integrable_const Cr).indicator hT)
  have hle : ∀ᵐ x ∂μ, F x ≤ Gd x + T.indicator (fun _ => Cr) x := by
    filter_upwards [hgood, hbad] with x h1 h2
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx]; linarith [hGd0 x]
    · rw [Set.indicator_of_notMem hx, add_zero]; exact h1 (fun hs => hx (hST hs))
  have hμS : (μ T).toReal ≤ Real.sqrt ε₀ := by
    rw [hμT]
    rcases le_or_gt ε₀ 0 with h0 | h0
    · have : μ S = 0 := le_antisymm (hS.trans (by rw [ENNReal.ofReal_eq_zero.mpr h0])) bot_le
      rw [this]; simp
    · have h1 : (μ S).toReal ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal h0.le hS
      have h2 : (μ S).toReal ≤ 1 := by
        have := prob_le_one (μ := μ) (s := S)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      rcases le_or_gt ε₀ 1 with h3 | h3
      · refine h1.trans ?_
        rw [Real.le_sqrt h0.le h0.le]
        nlinarith
      · refine h2.trans ?_
        rw [Real.le_sqrt zero_le_one h0.le]
        linarith
  calc ∫ x, F x ∂μ ≤ ∫ x, (Gd x + T.indicator (fun _ => Cr) x) ∂μ :=
        integral_mono_of_nonneg hF0 hint hle
    _ = ∫ x, Gd x ∂μ + (μ T).toReal * Cr := by
        rw [integral_add hGd ((integrable_const Cr).indicator hT), integral_indicator_const _ hT]
        simp [Measure.real, smul_eq_mul]
    _ ≤ ∫ x, Gd x ∂μ + Cr * Real.sqrt ε₀ := by
        rw [mul_comm]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hμS hCr)

/-! ### The order-one terms: the cancellation of `E⟨B S_θ(G) G⟩ f` -/

/-- The first derivatives of `(G B)_{ji}` along the slice in the entry `(j, i)` at `w = h_{ji}`:
`∂_w (G B)_{ji} = -c G_{jj} (G B)_{ii}` and `∂_{w̄} (G B)_{ji} = -c G_{ji} (G B)_{ji}`. -/
private lemma AM_dF {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) :
    dW (AM_F Λ B z h i j j i) (h j i) = -(if j = i then 1 / 2 else 1) *
        (res (Matrix.of h + Λ) z j j * (res (Matrix.of h + Λ) z * B) i i) ∧
      dWbar (AM_F Λ B z h i j j i) (h j i) = -(if j = i then 1 / 2 else 1) *
        (res (Matrix.of h + Λ) z j i * (res (Matrix.of h + Λ) z * B) j i) := by
  rw [AM_F_eq]
  obtain ⟨e1, e2⟩ := resPoly_dW h hh j i (AM_PF Λ B z j i)
    (AM_ok_pair hΛ hz (AM_PF_ok Λ B z j i))
  rw [e1, e2]
  simp only [AM_setEntry_self h hh]
  constructor
  · rw [← AM_f_ee Λ z h j j, ← AM_f_eM Λ B z h i i]
    simp [resPolyD, resMonoD, AM_PF, resPolyEval, resMonoEval]
  · rw [← AM_f_ee Λ z h j i, ← AM_f_eM Λ B z h j i]
    simp [resPolyD, resMonoD, AM_PF, resPolyEval, resMonoEval]

/-- `⟨B S_θ(G) G⟩ = (DN)⁻¹ Σ_{i,j} (S_θ)_{ji} G_{jj} (G B)_{ii}`. -/
private lemma AM_ntrS {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) =
      ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, (varProf D N θ j i : ℂ) * res (Matrix.of h + Λ) z j j *
        (res (Matrix.of h + Λ) z * B) i i := by
  rw [← AM_eval_PS]
  simp only [AM_PS, AM_eval_sum]
  simp only [resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, add_zero, mul_one, AM_f_ee, AM_f_eM]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- The order-one terms on a Hermitian array: with `f' = ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p`, the
second cumulants cancel `⟨B S_θ(G) G⟩ f'` exactly, and the remainder is
`(DN)⁻¹ Σ_{i,j} (G B)_{ji} (𝒞^{(0,2)}_{ji} ∂_{w̄} f' + 𝒞^{(1,1)}_{ji} ∂_w f')`. -/
private lemma AM_one_identity {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (p : ℕ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ((D : ℂ) * N)⁻¹ * (∑ i, ∑ j, ∑ a ∈ Finset.range (1 + 1),
        ccum (μ.map fun h => h j i) a (1 - a + 1) / ((a.factorial * (1 - a).factorial : ℕ) : ℂ) *
          wirt a (1 - a) (AM_f θ Λ B z h i j p) (h j i)) +
      ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) *
        ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
        starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p =
    ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, (res (Matrix.of h + Λ) z * B) j i *
      (ccum (μ.map fun h => h j i) 0 2 * dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
          starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i) +
        ccum (μ.map fun h => h j i) 1 1 * dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
          starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)) := by
  set V := ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
    starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p with hV
  have term : ∀ i j : Idx D N, ∑ a ∈ Finset.range (1 + 1),
      ccum (μ.map fun h => h j i) a (1 - a + 1) / ((a.factorial * (1 - a).factorial : ℕ) : ℂ) *
        wirt a (1 - a) (AM_f θ Λ B z h i j p) (h j i) =
      -((varProf D N θ j i : ℂ) * res (Matrix.of h + Λ) z j j *
        (res (Matrix.of h + Λ) z * B) i i) * V +
      (res (Matrix.of h + Λ) z * B) j i *
        (ccum (μ.map fun h => h j i) 0 2 * dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
          starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i) +
        ccum (μ.map fun h => h j i) 1 1 * dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
          starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)) := by
    intro i j
    have hsX := AM_sm_X θ Λ B hΛ z hz h hh i j
    have hsF := AM_sm_F Λ B hΛ z hz h hh i j j i
    have hsf' : AM_Sm (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) :=
      AM_sm_mul (AM_sm_pow hsX _) (AM_sm_pow (AM_sm_conj hsX) _)
    have hf : AM_f θ Λ B z h i j p = fun w => AM_F Λ B z h i j j i w *
        (fun w => AM_X θ Λ B z h i j w ^ (p - 1) * starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) w :=
      funext fun w => by simp only [AM_f]; ring
    obtain ⟨-, c11, -, c02⟩ := llClass_ccum_low D N C θ μ hμ j i
    obtain ⟨d1, d2⟩ := AM_dF Λ B hΛ z hz h hh i j
    have hg0 : AM_F Λ B z h i j j i (h j i) = (res (Matrix.of h + Λ) z * B) j i := by
      simp only [AM_F, AM_setEntry_self h hh]
    have hf0 : AM_X θ Λ B z h i j (h j i) ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j (h j i)) ^ p = V := by
      simp only [AM_X_self θ Λ B z h hh, hV]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, div_one, Nat.sub_self, Nat.sub_zero, mul_one,
      Nat.reduceAdd]
    simp only [wirt, Function.iterate_zero, id, Function.iterate_one]
    rw [hf, AM_der_dW.mul _ _ hsF hsf', AM_der_dWbar.mul _ _ hsF hsf']
    simp only
    rw [d1, d2, hg0, hf0, c11, c02]
    by_cases hji : j = i
    · subst hji
      simp only [ite_true]
      ring
    · simp only [hji, ite_false]
      ring
  simp only [term, Finset.sum_add_distrib, mul_add]
  rw [AM_ntrS]
  have e : ∑ i, ∑ j, -((varProf D N θ j i : ℂ) * res (Matrix.of h + Λ) z j j *
      (res (Matrix.of h + Λ) z * B) i i) * V =
      -((∑ i, ∑ j, (varProf D N θ j i : ℂ) * res (Matrix.of h + Λ) z j j *
        (res (Matrix.of h + Λ) z * B) i i) * V) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  ring

/-! ### Integrals of the expansion -/

/-- Exchanging a triple finite sum with the integral. -/
private lemma AM_int_sum3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} [Fintype ι]
    (s : Finset ℕ) (c₀ : ℂ) (c : ι → ι → ℕ → ℂ) (F : ι → ι → ℕ → α → ℂ)
    (hF : ∀ i j a, Integrable (F i j a) μ) :
    c₀ * ∑ i, ∑ j, ∑ a ∈ s, c i j a * ∫ x, F i j a x ∂μ =
      ∫ x, c₀ * ∑ i, ∑ j, ∑ a ∈ s, c i j a * F i j a x ∂μ := by
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun a _ => (hF i j a).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun a _ => (hF i j a).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun a _ => (hF i j a).const_mul _]
  exact Finset.sum_congr rfl fun a _ => (integral_const_mul _ _).symm

/-- `avgTerm` as one integral. -/
private lemma AM_avgTerm_int {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (hB : opNorm B ≤ 1) {z : ℂ} (hz : 0 < z.im) (c : ℝ) (hc1 : 1 ≤ c) (hcη : z.im⁻¹ ≤ c)
    (hηc : z.im ≤ c) (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    avgTerm D N θ μ Λ B z p k = ∫ h, ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
      ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
        wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i) ∂μ :=
  AM_int_sum3 (Finset.range (k + 1)) _
    (fun i j a => ccum (μ.map fun h => h j i) a (k - a + 1) /
      ((a.factorial * (k - a).factorial : ℕ) : ℂ))
    (fun i j a h => wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i))
    (fun i j a => AM_int_wirt hμ hθ0 hθ1 hΛ hΛn hB hz c hc1 hcη hηc i j p hp a (k - a))

/-- The ranges of the hypotheses: `N ≥ 1`, `0 < η`, `η⁻¹ ≤ N`, `η ≤ |z| ≤ N`, `Γ⁶ ≤ N`, and
`N⁻¹ ≤ ζ² = Υ/(Nη) ≤ 1` for `ζ = (Υ/(Nη))^{1/2}`. -/
private lemma AM_setup {N : ℕ} {z : ℂ} {Γ Υ : ℝ} (hz1 : ((N : ℝ))⁻¹ ≤ z.im)
    (hz2 : ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9)) (hΓ1 : 1 ≤ Γ) (hΓ2 : Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6))
    (hηΥ : z.im ≤ Υ) (hΥ : Υ ≤ (N : ℝ) * z.im) :
    1 ≤ N ∧ 0 < z.im ∧ z.im⁻¹ ≤ N ∧ z.im ≤ N ∧ ‖z‖ ≤ N ∧ Γ ^ 6 ≤ N ∧
      Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 2 = Υ / ((N : ℝ) * z.im) ∧
      ((N : ℝ))⁻¹ ≤ Υ / ((N : ℝ) * z.im) ∧ Υ / ((N : ℝ) * z.im) ≤ 1 := by
  have hN : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num)] at hΓ2
      linarith
    · exact h0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := lt_of_lt_of_le (inv_pos.mpr hN0) hz1
  have hzN : ‖z‖ ≤ N := hz2.trans (by
    calc (N : ℝ) ^ ((1 : ℝ) / 9) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _)
  have hηN : z.im ≤ N := (Complex.im_le_norm z).trans hzN
  have hηinv : z.im⁻¹ ≤ N := by
    rw [inv_le_comm₀ hη hN0]; exact hz1
  have hΓ6 : Γ ^ 6 ≤ N := by
    calc Γ ^ 6 ≤ ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 :=
          pow_le_pow_left₀ (by linarith) hΓ2 6
      _ = N := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          norm_num
  have hpos : 0 < (N : ℝ) * z.im := by positivity
  refine ⟨hN, hη, hηinv, hηN, hzN, hΓ6, Real.sq_sqrt (div_nonneg (hη.le.trans hηΥ) hpos.le),
    ?_, ?_⟩
  · rw [le_div_iff₀ hpos, inv_mul_eq_div, mul_div_cancel_left₀ _ hN0.ne']
    exact hηΥ
  · rw [div_le_one hpos]; exact hΥ

/-- `‖⟨B H̲G⟩‖^n` is integrable. -/
private lemma AM_int_xpow {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (hB : opNorm B ≤ 1) {z : ℂ} (hz : 0 < z.im) (c : ℝ) (hc1 : 1 ≤ c) (hcη : z.im⁻¹ ≤ c)
    (hηc : z.im ≤ c) (n : ℕ) :
    Integrable (fun h => ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ n) μ := by
  have := hμ.prob
  obtain ⟨cq, hcq⟩ := AM_QB_exists D
  have hX : AEStronglyMeasurable (fun h => ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) μ := by
    refine (AM_meas_poly (AM_PX D N θ Λ B z)).aestronglyMeasurable.congr ?_
    filter_upwards [hμ.herm] with h hh
    exact AM_eval_PX D N θ Λ B hΛ z hz h hh
  refine Integrable.mono' (integrable_const (((3 + ‖z‖) * c ^ 2) ^ n)) (hX.norm.pow n) ?_
  filter_upwards [hμ.herm] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (AM_X_crude (AM_crude_ctx hθ0 hθ1 hΛ hΛn hB hz hh hcq c hc1 hcη hηc)) n

/-- `⟨B S_θ(G) G⟩ ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p` is integrable. -/
private lemma AM_int_T {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (hB : opNorm B ≤ 1) {z : ℂ} (hz : 0 < z.im) (c : ℝ) (hc1 : 1 ≤ c) (hcη : z.im⁻¹ ≤ c)
    (hηc : z.im ≤ c) (p : ℕ) :
    Integrable (fun h => ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) *
      res (Matrix.of h + Λ) z)) * ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
        starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p) μ := by
  have := hμ.prob
  obtain ⟨cq, hcq⟩ := AM_QB_exists D
  have hX : AEStronglyMeasurable (fun h => ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) μ := by
    refine (AM_meas_poly (AM_PX D N θ Λ B z)).aestronglyMeasurable.congr ?_
    filter_upwards [hμ.herm] with h hh
    exact AM_eval_PX D N θ Λ B hΛ z hz h hh
  have hS : AEStronglyMeasurable (fun h => ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) *
      res (Matrix.of h + Λ) z))) μ := by
    refine (AM_meas_poly (AM_PS D N θ Λ B z)).aestronglyMeasurable.congr ?_
    exact Filter.Eventually.of_forall fun h => AM_eval_PS D N θ Λ B z h
  have hm := (hS.mul (hX.pow (p - 1))).mul ((Complex.continuous_conj.comp_aestronglyMeasurable
    hX).pow p)
  refine Integrable.mono' (integrable_const ((1 * c ^ 2) * ((3 + ‖z‖) * c ^ 2) ^ (p - 1) *
    ((3 + ‖z‖) * c ^ 2) ^ p)) hm ?_
  filter_upwards [hμ.herm] with h hh
  have hctx := AM_crude_ctx hθ0 hθ1 hΛ hΛn hB hz hh hcq c hc1 hcη hηc
  have hx := AM_X_crude hctx
  have hs : ‖ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z))‖ ≤
      1 * c ^ 2 := by
    rw [← AM_eval_PS]
    refine (AM_eval_le (AM_PS_ok D N θ Λ B z) h c hc1 hctx.forms).trans ?_
    exact mul_le_mul_of_nonneg_right (AM_PX_wt D N θ hθ0 hθ1 Λ B hB z).2 (by positivity)
  simp only [norm_mul, norm_pow, Complex.norm_conj]
  gcongr

/-! ### The order-one remainder -/

/-- The order-one remainder
`(DN)⁻¹ Σ_{i,j} (G B)_{ji} (𝒞^{(0,2)}_{ji} ∂_{w̄} f' + 𝒞^{(1,1)}_{ji} ∂_w f')`,
`f' = ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p` along the slice in the entry `(j, i)`. -/
private def AM_R1 (D N : ℕ) (μ : Measure (Idx D N → Idx D N → ℂ)) (θ : ℝ)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (p : ℕ) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, (res (Matrix.of h + Λ) z * B) j i *
    (ccum (μ.map fun h => h j i) 0 2 * dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i) +
      ccum (μ.map fun h => h j i) 1 1 * dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i))

/-- `0 ≤ (S_θ)_{pq} ≤ N⁻¹` for `θ ∈ [0, 1]`. -/
private lemma AM_vp_le {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (p q : Idx D N) :
    0 ≤ varProf D N θ p q ∧ varProf D N θ p q ≤ ((N : ℝ))⁻¹ := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast p.1.pos
  have hN : (0 : ℝ) < N := by exact_mod_cast p.2.pos
  have h1 : 0 ≤ 1 - θ := by linarith
  have hDN : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
    nlinarith [inv_pos.mpr hN]
  unfold varProf
  constructor
  · split_ifs <;> positivity
  · split_ifs
    · nlinarith
    · nlinarith [inv_pos.mpr hN]

/-- The forms `G_{ij}` and `(G B)_{ij}` are at most `Γ` on the good event. -/
private lemma AM_Ctx.entry_le {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (i j : Idx D N) :
    ‖res (Matrix.of h + Λ) z i j‖ ≤ Γ ∧ ‖(res (Matrix.of h + Λ) z * B) i j‖ ≤ Γ := by
  constructor
  · rw [← AM_f_ee]; exact hc.forms _ (Or.inl rfl) _ (AM_e_mem D N Λ B i) _ (AM_e_mem D N Λ B j)
  · rw [← AM_f_eM]; exact hc.forms _ (Or.inl rfl) _ (AM_e_mem D N Λ B i) _ (AM_Be_mem D N Λ B j)

/-- The bound on the order-one remainder at `h` on the good event:
`|R₁| ≤ 2 N⁻¹ (DN)⁻¹ (2p - 1) x^{2p-2} (2 (DN)⁻¹ Σ |(G B)_{ij}|² + λ_Q Σ |(G B)_{ij}|)`. -/
private lemma AM_R1_bound {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam) (p : ℕ)
    (hp : 1 ≤ p) :
    ‖AM_R1 D N μ θ Λ B z p h‖ ≤ 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * p - 1) *
      ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) *
      (2 * ((D : ℝ) * N)⁻¹ * (∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2) +
        lam * ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖) := by
  set A : Idx D N → Idx D N → ℝ := fun i j => ‖(res (Matrix.of h + Λ) z * B) i j‖ with hA
  set x := ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ with hx
  set ν := ((D : ℝ) * N)⁻¹ with hν
  have hν0 : 0 ≤ ν := by positivity
  have hNi : 0 ≤ ((N : ℝ))⁻¹ := by positivity
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hlam : ∀ k : Idx D N, 0 ≤ lam := fun k => hc.lam_nonneg k
  have hninv : ‖((D : ℂ) * N)⁻¹‖ = ν := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hterm : ∀ i j : Idx D N, ‖(res (Matrix.of h + Λ) z * B) j i *
      (ccum (μ.map fun h => h j i) 0 2 * dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
          starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i) +
        ccum (μ.map fun h => h j i) 1 1 * dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
          starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i))‖ ≤
      2 * ((N : ℝ))⁻¹ * (2 * p - 1) * x ^ (2 * p - 2) * (A j i * (ν * (A i j + A j i) + lam)) := by
    intro i j
    obtain ⟨-, c11, -, c02⟩ := llClass_ccum_low D N C θ μ hμ j i
    obtain ⟨d1, d2⟩ := AM_jet_f1 hc i j p hp
    obtain ⟨v0, v1⟩ := AM_vp_le θ hc.θ0 hc.θ1 j i
    have n11 : ‖ccum (μ.map fun h => h j i) 1 1‖ ≤ ((N : ℝ))⁻¹ := by
      rw [c11, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg v0]; exact v1
    have n02 : ‖ccum (μ.map fun h => h j i) 0 2‖ ≤ ((N : ℝ))⁻¹ := by
      rw [c02]; split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg v0]; exact v1
      · simp
    set M := (2 * p - 1 : ℝ) * (ν * (A i j + A j i) + lam) * x ^ (2 * p - 2) with hM
    have hM0 : 0 ≤ M := by
      have := hlam i
      have : 0 ≤ A i j := norm_nonneg _
      have : 0 ≤ A j i := norm_nonneg _
      positivity
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans ?_
    rw [norm_mul, norm_mul]
    have b1 : ‖ccum (μ.map fun h => h j i) 0 2‖ * ‖dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)‖ ≤ ((N : ℝ))⁻¹ * M :=
      mul_le_mul n02 d2 (norm_nonneg _) hNi
    have b2 : ‖ccum (μ.map fun h => h j i) 1 1‖ * ‖dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)‖ ≤ ((N : ℝ))⁻¹ * M :=
      mul_le_mul n11 d1 (norm_nonneg _) hNi
    calc ‖(res (Matrix.of h + Λ) z * B) j i‖ * (‖ccum (μ.map fun h => h j i) 0 2‖ *
          ‖dWbar (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
            starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)‖ +
          ‖ccum (μ.map fun h => h j i) 1 1‖ * ‖dW (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
            starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)‖)
        ≤ A j i * (((N : ℝ))⁻¹ * M + ((N : ℝ))⁻¹ * M) :=
          mul_le_mul_of_nonneg_left (add_le_add b1 b2) (norm_nonneg _)
      _ = _ := by rw [hM]; ring
  have hsum : ∑ i, ∑ j, A j i * (ν * (A i j + A j i) + lam) ≤
      2 * ν * (∑ i, ∑ j, A i j ^ 2) + lam * ∑ i, ∑ j, A i j := by
    have e1 : ∑ i, ∑ j, A j i * (ν * (A i j + A j i) + lam) =
        ν * (∑ i, ∑ j, A j i * A i j) + ν * (∑ i, ∑ j, A j i ^ 2) + lam * ∑ i, ∑ j, A j i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ i, ∑ j, A j i ^ 2 = ∑ i, ∑ j, A i j ^ 2 := Finset.sum_comm
    have e3 : ∑ i, ∑ j, A j i = ∑ i, ∑ j, A i j := Finset.sum_comm
    have e4 : ∑ i, ∑ j, A j i * A i j ≤ ∑ i, ∑ j, A i j ^ 2 := by
      have : ∑ i, ∑ j, A j i * A i j ≤ ∑ i, ∑ j, (A j i ^ 2 + A i j ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          nlinarith [sq_nonneg (A j i - A i j)]
      refine this.trans (le_of_eq ?_)
      simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, e2]
      ring
    rw [e1, e2, e3]
    nlinarith
  unfold AM_R1
  rw [norm_mul, hninv]
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))) hν0).trans ?_
  simp only [← Finset.mul_sum]
  have hk : 0 ≤ 2 * ((N : ℝ))⁻¹ * (2 * p - 1) * x ^ (2 * p - 2) := by positivity
  calc ν * (2 * ((N : ℝ))⁻¹ * (2 * p - 1) * x ^ (2 * p - 2) *
        ∑ i, ∑ j, A j i * (ν * (A i j + A j i) + lam))
      ≤ ν * (2 * ((N : ℝ))⁻¹ * (2 * p - 1) * x ^ (2 * p - 2) *
        (2 * ν * (∑ i, ∑ j, A i j ^ 2) + lam * ∑ i, ∑ j, A i j)) := by gcongr
    _ = _ := by ring

/-- `N^n ≤ N^r` for `N ≥ 1` and `n ≤ r`. -/
private lemma AM_npow_le {N : ℕ} (hN : 1 ≤ N) {n : ℕ} {r : ℝ} (h : (n : ℝ) ≤ r) :
    (N : ℝ) ^ n ≤ (N : ℝ) ^ r := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

/-- The order-one remainder on the good event: `|R₁| ≤ (2p - 1)(4 + 2D) ϑ² x^{2p-2}` with
`ϑ = a (1 + |z|)² Γ⁶ Υ/(Nη)` and `λ_Q ≤ a (1 + |z|)² Γ⁴ (Υ/(Nη))^{3/2}`. -/
private lemma AM_R1_good {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ bQ a : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ bQ) (p : ℕ)
    (hp : 1 ≤ p) (hD : 1 ≤ D) (hNn : 1 ≤ N) (ha : 1 ≤ a)
    (hbQ : bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3))
    (hulo : ((N : ℝ))⁻¹ ≤ Υ / ((N : ℝ) * z.im)) (huhi : Υ / ((N : ℝ) * z.im) ≤ 1) :
    ‖AM_R1 D N μ θ Λ B z p h‖ ≤ (2 * p - 1) * (4 + 2 * D) *
      (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) ^ 2 *
      ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) := by
  refine (AM_R1_bound hμ hc p hp).trans ?_
  obtain ⟨hS2, hS1, -⟩ := AM_ward_sums hc
  set u := Υ / ((N : ℝ) * z.im) with hu
  set ζ := Real.sqrt u with hζ
  have hζsq : ζ ^ 2 = u := Real.sq_sqrt (hc.ups)
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  have hζ1 : ζ ≤ 1 := by rw [hζ]; exact Real.sqrt_le_one.mpr huhi
  have hN : (0 : ℝ) < N := by exact_mod_cast hNn
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hbQ0 : 0 ≤ bQ := hc.lam_nonneg ⟨⟨0, hD⟩, ⟨0, hNn⟩⟩
  have hx0 : 0 ≤ ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) := by positivity
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  set ρ := a * (1 + ‖z‖) ^ 2 with hρ
  have hρ1 : 1 ≤ ρ := by
    have : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg z])
    nlinarith
  have hΓ1 : 1 ≤ Γ := hc.hΓ
  have hΓ4 : 1 ≤ Γ ^ 4 := one_le_pow₀ hΓ1
  have hΓ6 : Γ ^ 4 ≤ Γ ^ 6 := pow_le_pow_right₀ hΓ1 (by norm_num)
  have hu0 : 0 ≤ u := hc.ups
  -- the scalar bound
  have key : 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ *
      (2 * ((D : ℝ) * N)⁻¹ * (∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2) +
        bQ * ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖) ≤
      (4 + 2 * D) * (ρ * Γ ^ 6 * u) ^ 2 := by
    have hν : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
    have s1 : 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * ((D : ℝ) * N)⁻¹ *
        ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2) ≤ 4 * u ^ 2 := by
      have e : 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * ((D : ℝ) * N)⁻¹ *
          ((D : ℝ) * N ^ 2 * ζ ^ 2)) = 4 * ((D : ℝ))⁻¹ * ((N : ℝ))⁻¹ * u := by
        rw [hζsq]; field_simp; ring
      calc _ ≤ 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * ((D : ℝ) * N)⁻¹ *
            ((D : ℝ) * N ^ 2 * ζ ^ 2)) := by gcongr
        _ = 4 * ((D : ℝ))⁻¹ * ((N : ℝ))⁻¹ * u := e
        _ ≤ 4 * 1 * u * u := by
            have : ((D : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
            gcongr
        _ = 4 * u ^ 2 := by ring
    have s2 : 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ *
        (bQ * ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖) ≤ 2 * D * (ρ * Γ ^ 4 * u ^ 2) := by
      have e : 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (bQ * ((D : ℝ) ^ 2 * N ^ 2 * ζ)) =
          2 * D * (bQ * ζ) := by field_simp
      have hb : bQ * ζ ≤ ρ * Γ ^ 4 * u ^ 2 := by
        calc bQ * ζ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * ζ ^ 3) * ζ :=
              mul_le_mul_of_nonneg_right hbQ hζ0
          _ = ρ * Γ ^ 4 * (ζ ^ 2) ^ 2 := by rw [hρ]; ring
          _ = ρ * Γ ^ 4 * u ^ 2 := by rw [hζsq]
      calc _ ≤ 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (bQ * ((D : ℝ) ^ 2 * N ^ 2 * ζ)) := by
            gcongr
        _ = 2 * D * (bQ * ζ) := e
        _ ≤ 2 * D * (ρ * Γ ^ 4 * u ^ 2) := by gcongr
    have t1 : u ^ 2 ≤ (ρ * Γ ^ 6 * u) ^ 2 := by
      have : 1 ≤ ρ * Γ ^ 6 := by nlinarith
      have : u ≤ ρ * Γ ^ 6 * u := le_mul_of_one_le_left hu0 this
      exact pow_le_pow_left₀ hu0 this 2
    have t2 : ρ * Γ ^ 4 * u ^ 2 ≤ (ρ * Γ ^ 6 * u) ^ 2 := by
      have e : (ρ * Γ ^ 6 * u) ^ 2 = (ρ * Γ ^ 4 * u ^ 2) * (ρ * Γ ^ 8) := by ring
      rw [e]
      have : 1 ≤ ρ * Γ ^ 8 := by nlinarith [one_le_pow₀ (n := 8) hΓ1]
      exact le_mul_of_one_le_right (by positivity) this
    nlinarith
  calc 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * p - 1) *
        ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) *
        (2 * ((D : ℝ) * N)⁻¹ * (∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2) +
          bQ * ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖)
      = (2 * p - 1) * ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) *
        (2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ *
        (2 * ((D : ℝ) * N)⁻¹ * (∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2) +
          bQ * ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖)) := by ring
    _ ≤ (2 * p - 1) * ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) *
        ((4 + 2 * D) * (ρ * Γ ^ 6 * u) ^ 2) := by gcongr
    _ = _ := by rw [hρ]; ring

/-- The order-one remainder on any Hermitian array: `|R₁| ≤ (2p - 1) 4^{2p-2} (4 + 4 D c_{00})
N^{6p-2}`. -/
private lemma AM_R1_crude {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq)
    (hc : AM_Ctx D N θ Λ B z h N N (cq 0 0 * (1 + ‖z‖) * (N : ℝ) ^ (0 + 0 + 1) *
      ((N : ℝ) / ((N : ℝ) * z.im)))) (p : ℕ) (hp : 1 ≤ p) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hzN : ‖z‖ ≤ N) (hηinv : z.im⁻¹ ≤ N) :
    ‖AM_R1 D N μ θ Λ B z p h‖ ≤
      (2 * p - 1) * 4 ^ (2 * p - 2) * (4 + 4 * D * cq 0 0) * (N : ℝ) ^ (6 * p - 2) := by
  refine (AM_R1_bound hμ hc p hp).trans ?_
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hη := hc.hz
  have hcq0 := (hcq 0 0).1
  set lc := cq 0 0 * (1 + ‖z‖) * (N : ℝ) ^ (0 + 0 + 1) * ((N : ℝ) / ((N : ℝ) * z.im)) with hlc
  have hlc : lc ≤ 2 * cq 0 0 * (N : ℝ) ^ 3 := by
    rw [hlc]
    have e : (N : ℝ) / ((N : ℝ) * z.im) = z.im⁻¹ := by field_simp
    rw [e]
    simp only [zero_add, pow_one]
    have h1 : 1 + ‖z‖ ≤ 2 * N := by linarith
    calc cq 0 0 * (1 + ‖z‖) * N * z.im⁻¹ ≤ cq 0 0 * (2 * N) * N * N := by
          gcongr
      _ = 2 * cq 0 0 * (N : ℝ) ^ 3 := by ring
  have hlc0 : 0 ≤ lc := hc.lam_nonneg ⟨⟨0, hD⟩, ⟨0, hN⟩⟩
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have hS2 : ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2 ≤
      ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ 2 := by
    calc ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2 ≤ ∑ _i : Idx D N, ∑ _j : Idx D N,
          (N : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hc.entry_le i j).2 2
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
  have hS1 : ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ≤ ((D : ℝ) * N) ^ 2 * (N : ℝ) := by
    calc ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ≤ ∑ _i : Idx D N, ∑ _j : Idx D N,
          (N : ℝ) := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            (hc.entry_le i j).2
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
  have hx : ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ≤ 4 * (N : ℝ) ^ 3 := by
    refine (AM_X_crude hc).trans ?_
    nlinarith [norm_nonneg z]
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  calc 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * p - 1) *
        ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) *
        (2 * ((D : ℝ) * N)⁻¹ * (∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖ ^ 2) +
          lc * ∑ i, ∑ j, ‖(res (Matrix.of h + Λ) z * B) i j‖)
      ≤ 2 * ((N : ℝ))⁻¹ * ((D : ℝ) * N)⁻¹ * (2 * p - 1) * (4 * (N : ℝ) ^ 3) ^ (2 * p - 2) *
        (2 * ((D : ℝ) * N)⁻¹ * (((D : ℝ) * N) ^ 2 * (N : ℝ) ^ 2) +
          (2 * cq 0 0 * (N : ℝ) ^ 3) * (((D : ℝ) * N) ^ 2 * (N : ℝ))) := by gcongr
    _ = (2 * p - 1) * (4 * (N : ℝ) ^ 3) ^ (2 * p - 2) * (4 * N + 4 * D * cq 0 0 * (N : ℝ) ^ 4) := by
        field_simp; ring
    _ ≤ (2 * p - 1) * (4 * (N : ℝ) ^ 3) ^ (2 * p - 2) * ((4 + 4 * D * cq 0 0) * (N : ℝ) ^ 4) := by
        have h4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
          calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
        gcongr
        nlinarith
    _ = (2 * p - 1) * 4 ^ (2 * p - 2) * (4 + 4 * D * cq 0 0) * (N : ℝ) ^ (6 * p - 2) := by
        have e : (N : ℝ) ^ (6 * p - 2) = ((N : ℝ) ^ 3) ^ (2 * p - 2) * (N : ℝ) ^ 4 := by
          rw [← pow_mul, ← pow_add]; congr 1; omega
        rw [e, mul_pow]; ring

/-- The order-one part of the averaged moment inequality: the second cumulants cancel
`E ⟨B S_θ(G) G⟩ f` exactly, and the rest is `≤ K (ϑ E|⟨B H̲G⟩|^{2p-1} + ϑ² E|⟨B H̲G⟩|^{2p-2})` plus
the bad-event term, where `ϑ = a (1 + |z|)² Γ⁶ Υ/(Nη)` and
`λ_Q ≤ a (1 + |z|)² Γ⁴ (Υ/(Nη))^{3/2}`. -/
theorem avg_order_one (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ Γ Υ a bQ ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im → 1 ≤ a →
        bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3) →
        μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ≤ ENNReal.ofReal ε₀ →
        ‖avgTerm D N θ μ Λ B z p 1 +
            ∫ h, ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) *
                res (Matrix.of h + Λ) z)) *
              ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
              starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p ∂μ‖ ≤
          K * (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) *
              ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ +
            K * (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) ^ 2 *
              ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ +
            K * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
  obtain ⟨cq, hcq⟩ := AM_QB_exists D
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set K1 : ℝ := (2 * p - 1) * (4 + 2 * D) with hK1
  set Kc : ℝ := (2 * p - 1) * 4 ^ (2 * p - 2) * (4 + 4 * D * cq 0 0) with hKc
  have hp2 : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hK10 : 0 ≤ K1 := by rw [hK1]; exact mul_nonneg hp2 (by positivity)
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    have := (hcq 0 0).1
    exact mul_nonneg (mul_nonneg hp2 (by positivity)) (by positivity)
  refine ⟨K1 + Kc, by linarith, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hz1 hz2 Γ Υ a bQ ε₀ hΓ1 hΓ2 hηΥ hΥ ha hbQ hbad
  obtain ⟨hN, hη, hηinv, hηN, hzN, -, -, hulo, huhi⟩ := AM_setup hz1 hz2 hΓ1 hΓ2 hηΥ hΥ
  have hprob := hμ.prob
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    have e1 : avgTerm 0 N θ μ Λ B z p 1 = 0 := by simp [avgTerm]
    have e2 : ∀ M : Matrix (Idx 0 N) (Idx 0 N) ℂ, ntr M = 0 := fun M => by simp [ntr]
    simp only [e1, e2, zero_mul, MeasureTheory.integral_zero, add_zero, norm_zero]
    have : 0 ≤ a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im)) := by
      have := hη.le.trans hηΥ
      have : (0 : ℝ) ≤ a := by linarith
      positivity
    have h1 : 0 ≤ ∫ h, ‖ntr (B * hgUnder 0 N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ :=
      integral_nonneg fun _ => by positivity
    have h2 : 0 ≤ ∫ h, ‖ntr (B * hgUnder 0 N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ :=
      integral_nonneg fun _ => by positivity
    have h3 : 0 ≤ (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by positivity
    have : 0 ≤ K1 + Kc := by linarith
    positivity
  set ϑ := a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im)) with hϑ
  have hav := AM_avgTerm_int hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN p hp 1
  have hT := AM_int_T hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN p
  have hI : Integrable (fun h => ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (1 + 1),
      ccum (μ.map fun h => h j i) a (1 - a + 1) / ((a.factorial * (1 - a).factorial : ℕ) : ℂ) *
        wirt a (1 - a) (AM_f θ Λ B z h i j p) (h j i)) μ :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun a _ => (AM_int_wirt hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN
        i j p hp a (1 - a)).const_mul _).const_mul _
  have hLHS : avgTerm D N θ μ Λ B z p 1 +
      ∫ h, ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) *
        ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
        starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p ∂μ =
      ∫ h, AM_R1 D N μ θ Λ B z p h ∂μ := by
    rw [hav, ← integral_add hI hT]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    exact AM_one_identity hμ Λ B hΛ z hη p h hh
  rw [hLHS]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hGd := (AM_int_xpow hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN (2 * p - 2)).const_mul
    (K1 * ϑ ^ 2)
  have hϑ0 : 0 ≤ ϑ := by
    have := hη.le.trans hηΥ
    have : (0 : ℝ) ≤ a := by linarith
    positivity
  have hsplit := AM_split (fun h => ‖AM_R1 D N μ θ Λ B z p h‖)
    (fun h => K1 * ϑ ^ 2 * ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2))
    (avgGood D N θ Λ B z Γ Υ bQ)ᶜ (Kc * (N : ℝ) ^ (21 * (p : ℝ) + 18)) ε₀ hGd
    (fun h => by positivity) (by positivity) hbad (Filter.Eventually.of_forall fun _ =>
      norm_nonneg _)
    (by
      filter_upwards [hμ.herm] with h hh hin
      have hΩ : h ∈ avgGood D N θ Λ B z Γ Υ bQ := not_not.mp hin
      have hc : AM_Ctx D N θ Λ B z h Γ Υ bQ :=
        ⟨hθ0, hθ1, hΛ, hΛn, hB, hη, hh, hΓ1, hηΥ, hΩ.1, hΩ.2⟩
      exact AM_R1_good hμ hc p hp hD hN ha hbQ hulo huhi)
    (by
      filter_upwards [hμ.herm] with h hh
      have hc := AM_crude_ctx hθ0 hθ1 hΛ hΛn hB hη hh hcq N hN1 hηinv hηN
      refine (AM_R1_crude hμ hcq hc p hp hD hN hzN hηinv).trans ?_
      rw [← hKc]
      exact mul_le_mul_of_nonneg_left (AM_npow_le hN (by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith)) hKc0)
  refine hsplit.trans ?_
  rw [integral_const_mul]
  have h1 : 0 ≤ ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ :=
    integral_nonneg fun _ => by positivity
  have h2 : 0 ≤ ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ :=
    integral_nonneg fun _ => by positivity
  have h3 : 0 ≤ (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by positivity
  have e : K1 * ϑ ^ 2 * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ ≤
      (K1 + Kc) * ϑ ^ 2 * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ := by
    gcongr; linarith
  have e2 : Kc * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ ≤
      (K1 + Kc) * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
    gcongr; linarith
  have e3 : 0 ≤ (K1 + Kc) * ϑ *
      ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ := by
    have : 0 ≤ K1 + Kc := by linarith
    positivity
  linarith

/-! ### The order-`k` terms -/

/-- `N^{-m/2} = (N^{1/2})^{-m}`. -/
private lemma AM_rpow_half (N m : ℕ) :
    (N : ℝ) ^ (-((m : ℝ) / 2)) = ((Real.sqrt N) ^ m)⁻¹ := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_neg hN0]
  congr 1
  ring

/-- `|x / n| ≤ |x|` for a natural number `n ≥ 1`. -/
private lemma AM_norm_div_nat (x : ℂ) (n : ℕ) (hn : 1 ≤ n) : ‖x / (n : ℂ)‖ ≤ ‖x‖ := by
  rw [norm_div, Complex.norm_natCast]
  exact div_le_self (norm_nonneg _) (by exact_mod_cast hn)

/-- The pointwise bound on the order-`k` integrand at `h` on the good event, from a bound
`Kk s` on the cumulants of total order `k + 1`. -/
private lemma AM_high_pt {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} {θ : ℝ}
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ}
    (hc : AM_Ctx D N θ Λ B z h Γ Υ lam) {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (p : ℕ)
    (hp : 1 ≤ p) (k : ℕ) (Kk sv : ℝ) (hKk : 0 ≤ Kk) (hsv : 0 ≤ sv)
    (hcum : ∀ i j : Idx D N, ∀ a ≤ k, ‖ccum (μ.map fun h => h j i) a (k - a + 1)‖ ≤ Kk * sv) :
    ‖((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
        ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
          wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤
      (D : ℝ) * N * ((k + 1) * (Kk * sv)) * (Γ ^ k * (2 * p : ℝ) ^ k *
        ((((1 + k : ℕ) : ℝ) ^ k * Γ) * (‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ +
          AM_beta D N cq k z Υ lam) ^ (2 * p - 1))) := by
  set J := Γ ^ k * (2 * p : ℝ) ^ k * ((((1 + k : ℕ) : ℝ) ^ k * Γ) *
    (‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ + AM_beta D N cq k z Υ lam) ^ (2 * p - 1))
    with hJ
  have hterm : ∀ i j : Idx D N, ∀ a ∈ Finset.range (k + 1),
      ‖ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
        wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤ Kk * sv * J := by
    intro i j a ha
    have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [norm_mul]
    refine mul_le_mul ((AM_norm_div_nat _ _ (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)))).trans
        (hcum i j a ha')) ?_ (norm_nonneg _) (mul_nonneg hKk hsv)
    have := AM_jet_f hc hcq k i j p hp a (k - a) (by omega)
    rwa [show a + (k - a) = k by omega] at this
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have hninv : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [norm_mul, hninv]
  have hs : ‖∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
      ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
        wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤
      ((D : ℝ) * N) ^ 2 * ((k + 1) * (Kk * sv * J)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖∑ j, ∑ a ∈ Finset.range (k + 1),
          ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
            wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖
        ≤ ∑ _i : Idx D N, ∑ _j : Idx D N, ∑ _a ∈ Finset.range (k + 1), Kk * sv * J :=
          Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => hterm i j a ha))
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul, hcard]
          push_cast; ring
  rcases eq_or_ne ((D : ℝ) * N) 0 with h0 | h0
  · rw [h0]; simp
  · calc ((D : ℝ) * N)⁻¹ * ‖∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
          ccum (μ.map fun h => h j i) a (k - a + 1) /
            ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
            wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖
        ≤ ((D : ℝ) * N)⁻¹ * (((D : ℝ) * N) ^ 2 * ((k + 1) * (Kk * sv * J))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp

/-- The binomial bound: if `Ψ B^q ≤ c^q ϑ^{q+1}` for `q ≤ m`, then
`Ψ (B + x)^m ≤ 2^m c^m Σ_{n=1}^{m+1} ϑ^n x^{m+1-n}`. -/
private lemma AM_poly_bound (Ψ Bb ϑ x c : ℝ) (hϑ : 0 ≤ ϑ) (hx : 0 ≤ x)
    (hc : 1 ≤ c) (m : ℕ) (h : ∀ q ≤ m, Ψ * Bb ^ q ≤ c ^ q * ϑ ^ (q + 1)) :
    Ψ * (x + Bb) ^ m ≤ 2 ^ m * c ^ m * ∑ n ∈ Finset.Icc 1 (m + 1), ϑ ^ n * x ^ (m + 1 - n) := by
  rw [add_comm, add_pow, Finset.mul_sum]
  have hre : ∑ q ∈ Finset.range (m + 1), ϑ ^ (q + 1) * x ^ (m - q) =
      ∑ n ∈ Finset.Icc 1 (m + 1), ϑ ^ n * x ^ (m + 1 - n) := by
    calc ∑ q ∈ Finset.range (m + 1), ϑ ^ (q + 1) * x ^ (m - q) =
        ∑ q ∈ Finset.Ico 0 (m + 1), (fun n => ϑ ^ n * x ^ (m + 1 - n)) (q + 1) := by
          rw [Finset.range_eq_Ico]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [Nat.add_sub_add_right]
      _ = _ := (Finset.sum_Ico_add' (fun n => ϑ ^ n * x ^ (m + 1 - n)) 0 (m + 1) 1).trans rfl
  rw [← hre, Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hch : ((m.choose q : ℕ) : ℝ) ≤ 2 ^ m := by
    have := Nat.choose_le_two_pow m q
    exact_mod_cast this
  have hcq : c ^ q ≤ c ^ m := pow_le_pow_right₀ hc hq'
  calc Ψ * (Bb ^ q * x ^ (m - q) * (m.choose q : ℝ)) = (Ψ * Bb ^ q) * x ^ (m - q) *
        (m.choose q : ℝ) := by ring
    _ ≤ (c ^ q * ϑ ^ (q + 1)) * x ^ (m - q) * 2 ^ m :=
        mul_le_mul (mul_le_mul_of_nonneg_right (h q hq') (by positivity)) hch (by positivity)
          (by positivity)
    _ ≤ (c ^ m * ϑ ^ (q + 1)) * x ^ (m - q) * 2 ^ m := by gcongr
    _ = 2 ^ m * c ^ m * (ϑ ^ (q + 1) * x ^ (m - q)) := by ring

/-- `β_K ≤ (K^K + 1 + c_K) a (1 + |z|)² Γ⁴ Υ/(Nη)` on the good event. -/
private lemma AM_beta_good {D N : ℕ} (cq : ℕ → ℕ → ℝ) (K : ℕ) (z : ℂ) (Γ Υ bQ a : ℝ)
    (hD : 1 ≤ D) (hN : 1 ≤ N) (hcQ : 0 ≤ AM_cQ cq K) (hΓ : 1 ≤ Γ) (ha : 1 ≤ a)
    (hbQ : bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3))
    (hu0 : 0 ≤ Υ / ((N : ℝ) * z.im)) (hulo : ((N : ℝ))⁻¹ ≤ Υ / ((N : ℝ) * z.im))
    (huhi : Υ / ((N : ℝ) * z.im) ≤ 1) :
    AM_beta D N cq K z Υ bQ ≤ ((K : ℝ) ^ K + 1 + AM_cQ cq K) *
      (a * (1 + ‖z‖) ^ 2 * Γ ^ 4 * (Υ / ((N : ℝ) * z.im))) := by
  set u := Υ / ((N : ℝ) * z.im) with hu
  set ζ := Real.sqrt u with hζ
  have hζsq : ζ ^ 2 = u := Real.sq_sqrt hu0
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  have hζ1 : ζ ≤ 1 := by rw [hζ]; exact Real.sqrt_le_one.mpr huhi
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set ρ := a * (1 + ‖z‖) ^ 2 * Γ ^ 4 with hρ
  have hz1 : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg z])
  have hΓ4 : 1 ≤ Γ ^ 4 := one_le_pow₀ hΓ
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]
    have : 1 ≤ a * (1 + ‖z‖) ^ 2 := by nlinarith
    nlinarith
  have h1 : ((D : ℝ) * N)⁻¹ ≤ u := by
    refine le_trans ?_ hulo
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
    nlinarith [inv_pos.mpr (show (0 : ℝ) < N by linarith)]
  have h2 : bQ ≤ ρ * u := by
    refine hbQ.trans ?_
    have : ζ ^ 3 ≤ u := by rw [← hζsq]; nlinarith
    calc a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * ζ ^ 3) = ρ * ζ ^ 3 := by rw [hρ]; ring
      _ ≤ ρ * u := by gcongr
  have h3 : 1 + ‖z‖ ≤ ρ := by
    have : 1 + ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
    have haΓ : 1 ≤ a * Γ ^ 4 := by nlinarith
    calc 1 + ‖z‖ ≤ (1 + ‖z‖) ^ 2 := this
      _ = 1 * (1 + ‖z‖) ^ 2 := (one_mul _).symm
      _ ≤ (a * Γ ^ 4) * (1 + ‖z‖) ^ 2 := by gcongr
      _ = ρ := by rw [hρ]; ring
  unfold AM_beta
  have hKK : (0 : ℝ) ≤ (K : ℝ) ^ K := by positivity
  have e1 : ((D : ℝ) * N)⁻¹ * (K : ℝ) ^ K ≤ (K : ℝ) ^ K * (ρ * u) := by
    have : ((D : ℝ) * N)⁻¹ ≤ ρ * u := h1.trans (le_mul_of_one_le_left hu0 hρ1)
    nlinarith
  have e3 : AM_cQ cq K * (1 + ‖z‖) * u ≤ AM_cQ cq K * (ρ * u) := by
    rw [mul_assoc]; gcongr
  nlinarith

/-- The order-`k` integrand on the good event for `k ≥ 3`: at most
`K Σ_{n=1}^{2p} ϑ^n x^{2p-n}`. -/
private lemma AM_high_good3 {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} {θ : ℝ}
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {h : Idx D N → Idx D N → ℂ} {Γ Υ bQ a : ℝ}
    (hc : AM_Ctx D N θ Λ B z h Γ Υ bQ) {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (p : ℕ)
    (hp : 1 ≤ p) (k : ℕ) (hk : 3 ≤ k) (Kk : ℝ) (hKk : 0 ≤ Kk) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (ha : 1 ≤ a)
    (hbQ : bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3))
    (hulo : ((N : ℝ))⁻¹ ≤ Υ / ((N : ℝ) * z.im)) (huhi : Υ / ((N : ℝ) * z.im) ≤ 1)
    (hΓ6 : Γ ^ 6 ≤ N)
    (hcum : ∀ i j : Idx D N, ∀ a ≤ k, ‖ccum (μ.map fun h => h j i) a (k - a + 1)‖ ≤
      Kk * ((Real.sqrt N) ^ (k + 1))⁻¹) :
    ‖((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
        ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
          wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤
      ((D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) *
        (2 ^ (2 * p - 1) * ((k : ℝ) ^ k + 1 + AM_cQ cq k) ^ (2 * p - 1))) *
      ∑ n ∈ Finset.Icc 1 (2 * p), (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) ^ n *
        ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) := by
  set sN := Real.sqrt N with hsN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ sN := by rw [hsN]; exact Real.one_le_sqrt.mpr hN1
  have hs2 : sN ^ 2 = N := Real.sq_sqrt (by linarith)
  have hsv0 : 0 ≤ (sN ^ (k + 1))⁻¹ := by positivity
  refine (AM_high_pt hc hcq p hp k Kk _ hKk hsv0 hcum).trans ?_
  set u := Υ / ((N : ℝ) * z.im) with hu
  have hu0 : 0 ≤ u := hc.ups
  have hΓ := hc.hΓ
  have hΓ0 : 0 ≤ Γ := by linarith
  set x := ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ with hx
  set Cβ := (k : ℝ) ^ k + 1 + AM_cQ cq k with hCβ
  have hcQ := AM_cQ_nonneg hcq k
  have hCβ1 : 1 ≤ Cβ := by rw [hCβ]; have : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
                           linarith
  set ρ4 := a * (1 + ‖z‖) ^ 2 * Γ ^ 4 with hρ4
  have hβ := AM_beta_good cq k z Γ Υ bQ a hD hN hcQ hΓ ha hbQ hu0 hulo huhi
  have hβ0 := AM_beta_nonneg hc hcq k ⟨⟨0, hD⟩, ⟨0, hN⟩⟩
  have hρ1 : 1 ≤ a * (1 + ‖z‖) ^ 2 := by
    have : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg z])
    nlinarith
  -- the key power-counting inequality `N Γ^{k+1} s^{-(k+1)} ≤ Γ⁶ u`
  have hΓs : Γ ≤ sN := by
    have h3 : Γ ^ 3 ≤ sN := by
      rw [hsN]
      refine Real.le_sqrt_of_sq_le ?_
      calc (Γ ^ 3) ^ 2 = Γ ^ 6 := by ring
        _ ≤ (N : ℝ) := hΓ6
    calc Γ ≤ Γ ^ 3 := by
          calc Γ = Γ ^ 1 := (pow_one Γ).symm
            _ ≤ Γ ^ 3 := pow_le_pow_right₀ hΓ (by norm_num)
      _ ≤ sN := h3
  have hNu : 1 ≤ (N : ℝ) * u := by
    have := mul_le_mul_of_nonneg_left hulo (show (0 : ℝ) ≤ N by linarith)
    rwa [mul_inv_cancel₀ (by linarith)] at this
  have hkey : (N : ℝ) * (sN ^ (k + 1))⁻¹ * Γ ^ (k + 1) ≤ Γ ^ 6 * u := by
    have hsk : 0 < sN ^ (k + 1) := by positivity
    rw [mul_comm (N : ℝ), mul_assoc, inv_mul_le_iff₀ hsk]
    have e1 : sN ^ (k + 1) = sN ^ (k - 3) * (sN ^ 2) ^ 2 := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have e2 : Γ ^ (k + 1) ≤ Γ ^ 6 * Γ ^ (k - 3) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hΓ (by omega)
    have e3 : Γ ^ (k - 3) ≤ sN ^ (k - 3) := pow_le_pow_left₀ hΓ0 hΓs _
    rw [e1, hs2]
    calc (N : ℝ) * Γ ^ (k + 1) ≤ N * (Γ ^ 6 * sN ^ (k - 3)) := by
          gcongr; exact e2.trans (by gcongr)
      _ ≤ N * (Γ ^ 6 * sN ^ (k - 3)) * (N * u) := le_mul_of_one_le_right (by positivity) hNu
      _ = sN ^ (k - 3) * (N : ℝ) ^ 2 * (Γ ^ 6 * u) := by ring
  -- apply the binomial bound
  have hpb := AM_poly_bound ((N : ℝ) * (sN ^ (k + 1))⁻¹ * Γ ^ (k + 1)) (Cβ * (ρ4 * u))
    (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * u) x Cβ (by positivity)
    (norm_nonneg _) hCβ1 (2 * p - 1) (fun q _ => by
      have e : (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * u) ^ (q + 1) =
          (ρ4 * u) ^ q * (Γ ^ 2) ^ q * ((a * (1 + ‖z‖) ^ 2) * (Γ ^ 6 * u)) := by
        rw [pow_succ, ← mul_pow]
        congr 1
        · congr 1; rw [hρ4]; ring
        · ring
      rw [e, mul_pow]
      have hΓ2q : 1 ≤ (Γ ^ 2) ^ q := one_le_pow₀ (one_le_pow₀ hΓ)
      have hA : 0 ≤ Cβ ^ q * (ρ4 * u) ^ q := by positivity
      calc (N : ℝ) * (sN ^ (k + 1))⁻¹ * Γ ^ (k + 1) * (Cβ ^ q * (ρ4 * u) ^ q)
          ≤ (Γ ^ 6 * u) * (Cβ ^ q * (ρ4 * u) ^ q) := mul_le_mul_of_nonneg_right hkey hA
        _ = (Cβ ^ q * (ρ4 * u) ^ q) * 1 * 1 * (Γ ^ 6 * u) := by ring
        _ ≤ (Cβ ^ q * (ρ4 * u) ^ q) * (Γ ^ 2) ^ q * (a * (1 + ‖z‖) ^ 2) * (Γ ^ 6 * u) := by
            gcongr
        _ = Cβ ^ q * ((ρ4 * u) ^ q * (Γ ^ 2) ^ q * ((a * (1 + ‖z‖) ^ 2) * (Γ ^ 6 * u))) := by
            ring)
  rw [show 2 * p - 1 + 1 = 2 * p by omega] at hpb
  have hxb : (x + AM_beta D N cq k z Υ bQ) ^ (2 * p - 1) ≤ (x + Cβ * (ρ4 * u)) ^ (2 * p - 1) :=
    pow_le_pow_left₀ (by positivity) (by rw [hρ4]; linarith) _
  have hS0 : 0 ≤ (D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) := by
    positivity
  calc (D : ℝ) * N * ((k + 1) * (Kk * (sN ^ (k + 1))⁻¹)) * (Γ ^ k * (2 * p : ℝ) ^ k *
        ((((1 + k : ℕ) : ℝ) ^ k * Γ) * (x + AM_beta D N cq k z Υ bQ) ^ (2 * p - 1)))
      = ((D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k))) *
        (((N : ℝ) * (sN ^ (k + 1))⁻¹ * Γ ^ (k + 1)) *
          (x + AM_beta D N cq k z Υ bQ) ^ (2 * p - 1)) := by ring
    _ ≤ ((D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k))) *
        (((N : ℝ) * (sN ^ (k + 1))⁻¹ * Γ ^ (k + 1)) * (x + Cβ * (ρ4 * u)) ^ (2 * p - 1)) := by
        gcongr
    _ ≤ ((D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k))) *
        (2 ^ (2 * p - 1) * Cβ ^ (2 * p - 1) * ∑ n ∈ Finset.Icc 1 (2 * p),
          (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * u) ^ n * x ^ (2 * p - n)) :=
        mul_le_mul_of_nonneg_left hpb hS0
    _ = _ := by ring

/-- `N^{k+2} (N⁴)^{2p-1} N^{-(k+1)/2} ≤ N^{21p+18}` for `2 ≤ k ≤ 16p + 16`. -/
private lemma AM_crude_exp {N : ℕ} (hN : 1 ≤ N) (p k : ℕ) (hp : 1 ≤ p) (hk2 : 2 ≤ k)
    (hk' : k ≤ 16 * p + 16) (hs : (Real.sqrt N) ^ (k + 1) ≠ 0) :
    (N : ℝ) ^ (k + 2) * ((N : ℝ) ^ 4) ^ (2 * p - 1) * ((Real.sqrt N) ^ (k + 1))⁻¹ ≤
      (N : ℝ) ^ (21 * (p : ℝ) + 18) := by
  set sN := Real.sqrt N with hsN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ sN := by rw [hsN]; exact Real.one_le_sqrt.mpr hN1
  have hs2 : (N : ℝ) = sN ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have e1 : (N : ℝ) ^ (21 * (p : ℝ) + 18) = sN ^ (42 * p + 36) := by
    rw [show 21 * (p : ℝ) + 18 = ((21 * p + 18 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      hs2, ← pow_mul]
    congr 1; ring
  have e2 : (N : ℝ) ^ (k + 2) * ((N : ℝ) ^ 4) ^ (2 * p - 1) =
      sN ^ (k + 1) * sN ^ (k + 16 * p - 5) := by
    rw [hs2, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1; omega
  rw [e1, e2, mul_comm (sN ^ (k + 1)), mul_assoc, mul_inv_cancel₀ hs, mul_one]
  exact pow_le_pow_right₀ hs1 (by omega)

/-- The order-`k` integrand on any Hermitian array, for `2 ≤ k ≤ 16p + 16`: at most
`K N^{21p+18}`. -/
private lemma AM_high_crude {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} {θ : ℝ}
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {h : Idx D N → Idx D N → ℂ}
    {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq)
    (hc : AM_Ctx D N θ Λ B z h N N (cq 0 0 * (1 + ‖z‖) * (N : ℝ) ^ (0 + 0 + 1) *
      ((N : ℝ) / ((N : ℝ) * z.im)))) (p : ℕ) (hp : 1 ≤ p) (k : ℕ) (hk2 : 2 ≤ k)
    (hk' : k ≤ 16 * p + 16) (Kk : ℝ) (hKk : 0 ≤ Kk) (hD : 1 ≤ D) (hN : 1 ≤ N) (hzN : ‖z‖ ≤ N)
    (hηinv : z.im⁻¹ ≤ N)
    (hcum : ∀ i j : Idx D N, ∀ a ≤ k, ‖ccum (μ.map fun h => h j i) a (k - a + 1)‖ ≤
      Kk * ((Real.sqrt N) ^ (k + 1))⁻¹) :
    ‖((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
        ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
          wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤
      ((D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) *
        (4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) ^ (2 * p - 1)) *
      (N : ℝ) ^ (21 * (p : ℝ) + 18) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsv0 : 0 ≤ ((Real.sqrt N) ^ (k + 1))⁻¹ := by positivity
  refine (AM_high_pt hc hcq p hp k Kk _ hKk hsv0 hcum).trans ?_
  have hcQ := AM_cQ_nonneg hcq k
  have hcq0 := (hcq 0 0).1
  have hx : ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ≤ 4 * (N : ℝ) ^ 4 := by
    refine (AM_X_crude hc).trans ?_
    have : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    have : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    nlinarith [norm_nonneg z]
  have hb := AM_beta_crude cq k z N hN hN1 hηinv hc.hz hcQ hcq0 hD
  have hb' : AM_beta D N cq k z N (cq 0 0 * (1 + ‖z‖) * (N : ℝ) ^ (0 + 0 + 1) *
      ((N : ℝ) / ((N : ℝ) * z.im))) ≤ ((k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) * (N : ℝ) ^ 4 := by
    refine hb.trans ?_
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have h2 : (1 + ‖z‖) * (N : ℝ) ^ 2 * N ≤ 2 * (N : ℝ) ^ 4 := by
      have : 1 + ‖z‖ ≤ 2 * N := by linarith
      calc (1 + ‖z‖) * (N : ℝ) ^ 2 * N ≤ (2 * N) * (N : ℝ) ^ 2 * N := by gcongr
        _ = 2 * (N : ℝ) ^ 4 := by ring
    have hkk : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
    have hs : 0 ≤ cq 0 0 + AM_cQ cq k := by linarith
    calc ((k : ℝ) ^ k + (cq 0 0 + AM_cQ cq k) * (1 + ‖z‖) * (N : ℝ) ^ 2) * N
        = (k : ℝ) ^ k * N + (cq 0 0 + AM_cQ cq k) * ((1 + ‖z‖) * (N : ℝ) ^ 2 * N) := by ring
      _ ≤ (k : ℝ) ^ k * (N : ℝ) ^ 4 + (cq 0 0 + AM_cQ cq k) * (2 * (N : ℝ) ^ 4) := by gcongr
      _ = _ := by ring
  have hxb : ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ + AM_beta D N cq k z N
      (cq 0 0 * (1 + ‖z‖) * (N : ℝ) ^ (0 + 0 + 1) * ((N : ℝ) / ((N : ℝ) * z.im))) ≤
      (4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) * (N : ℝ) ^ 4 := by linarith
  have hb0 := AM_beta_nonneg hc hcq k ⟨⟨0, hD⟩, ⟨0, hN⟩⟩
  have hexp := AM_crude_exp hN p k hp hk2 hk' (by positivity)
  have hpos : 0 ≤ (D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) *
      (4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) ^ (2 * p - 1) := by
    have : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
    have : 0 ≤ 4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k) := by linarith
    positivity
  calc (D : ℝ) * N * ((k + 1) * (Kk * ((Real.sqrt N) ^ (k + 1))⁻¹)) * ((N : ℝ) ^ k *
        (2 * p : ℝ) ^ k * ((((1 + k : ℕ) : ℝ) ^ k * N) *
          (‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ + AM_beta D N cq k z N
            (cq 0 0 * (1 + ‖z‖) * (N : ℝ) ^ (0 + 0 + 1) * ((N : ℝ) / ((N : ℝ) * z.im)))) ^
              (2 * p - 1)))
      ≤ (D : ℝ) * N * ((k + 1) * (Kk * ((Real.sqrt N) ^ (k + 1))⁻¹)) * ((N : ℝ) ^ k *
        (2 * p : ℝ) ^ k * ((((1 + k : ℕ) : ℝ) ^ k * N) *
          ((4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) * (N : ℝ) ^ 4) ^ (2 * p - 1))) := by
        gcongr
    _ = ((D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) *
        (4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) ^ (2 * p - 1)) *
        ((N : ℝ) ^ (k + 2) * ((N : ℝ) ^ 4) ^ (2 * p - 1) * ((Real.sqrt N) ^ (k + 1))⁻¹) := by
        simp only [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hpos

/-! ### The order-two terms -/

/-- The first derivatives of `w ↦ (G B)_{kl}` along the slice in the entry `(j, i)`:
`∂_w = -c G_{kj} (G B)_{il}`, `∂_{w̄} = -c G_{ki} (G B)_{jl}`. -/
private lemma AM_dF_fun {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) :
    dW (AM_F Λ B z h i j k l) = (fun w => -(if j = i then 1 / 2 else 1) *
        (AM_G Λ z h i j k j w * AM_F Λ B z h i j i l w)) ∧
      dWbar (AM_F Λ B z h i j k l) = (fun w => -(if j = i then 1 / 2 else 1) *
        (AM_G Λ z h i j k i w * AM_F Λ B z h i j j l w)) := by
  rw [AM_F_eq]
  obtain ⟨e1, e2⟩ := resPoly_dW h hh j i (AM_PF Λ B z k l)
    (AM_ok_pair hΛ hz (AM_PF_ok Λ B z k l))
  rw [e1, e2]
  constructor
  · funext w
    simp only [AM_G, AM_F]
    rw [← AM_f_ee Λ z _ k j, ← AM_f_eM Λ B z _ i l]
    simp [resPolyD, resMonoD, AM_PF, resPolyEval, resMonoEval]
  · funext w
    simp only [AM_G, AM_F]
    rw [← AM_f_ee Λ z _ k i, ← AM_f_eM Λ B z _ j l]
    simp [resPolyD, resMonoD, AM_PF, resPolyEval, resMonoEval]

/-- The first derivatives of `w ↦ G_{kl}` along the slice in the entry `(j, i)` (`res_dW`). -/
private lemma AM_dG_fun {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) :
    dW (AM_G Λ z h i j k l) = (fun w => -(if j = i then 1 / 2 else 1) *
        (AM_G Λ z h i j k j w * AM_G Λ z h i j i l w)) ∧
      dWbar (AM_G Λ z h i j k l) = (fun w => -(if j = i then 1 / 2 else 1) *
        (AM_G Λ z h i j k i w * AM_G Λ z h i j j l w)) :=
  res_dW Λ hΛ z hz.ne' h hh j i k l

/-- The parity bound for the second derivatives of `(G B)_{ji}` at `h` on the good event: every
term contains `G_{ij}`, `G_{ji}` or `(G B)_{ji}`, so
`|∂^{(a,b)} (G B)_{ji}| ≤ 2 Γ² (|G_{ij}| + |G_{ji}| + |(G B)_{ji}|)` for `a + b = 2`. -/
private lemma AM_jet_F2 {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    (i j : Idx D N) (a b : ℕ) (hab : a + b = 2) :
    ‖wirt a b (AM_F Λ B z h i j j i) (h j i)‖ ≤ 2 * Γ ^ 2 *
      (‖res (Matrix.of h + Λ) z i j‖ + ‖res (Matrix.of h + Λ) z j i‖ +
        ‖(res (Matrix.of h + Λ) z * B) j i‖) := by
  have hΛ := hc.hΛ
  have hz := hc.hz
  have hh := hc.hh
  set c : ℂ := if j = i then 1 / 2 else 1 with hcdef
  have hc1 : ‖c‖ ≤ 1 := by rw [hcdef]; split_ifs <;> norm_num
  have sG : ∀ k l, AM_Sm (AM_G Λ z h i j k l) := fun k l => AM_sm_G Λ hΛ z hz h hh i j k l
  have sF : ∀ k l, AM_Sm (AM_F Λ B z h i j k l) := fun k l => AM_sm_F Λ B hΛ z hz h hh i j k l
  have vG : ∀ k l, AM_G Λ z h i j k l (h j i) = res (Matrix.of h + Λ) z k l := fun k l => by
    simp only [AM_G, AM_setEntry_self h hh]
  have vF : ∀ k l, AM_F Λ B z h i j k l (h j i) = (res (Matrix.of h + Λ) z * B) k l :=
    fun k l => by simp only [AM_F, AM_setEntry_self h hh]
  have bG : ∀ k l, ‖res (Matrix.of h + Λ) z k l‖ ≤ Γ := fun k l => (hc.entry_le k l).1
  have bF : ∀ k l, ‖(res (Matrix.of h + Λ) z * B) k l‖ ≤ Γ := fun k l => (hc.entry_le k l).2
  have hΓ0 : 0 ≤ Γ := by linarith [hc.hΓ]
  set gij := ‖res (Matrix.of h + Λ) z i j‖
  set gji := ‖res (Matrix.of h + Λ) z j i‖
  set fji := ‖(res (Matrix.of h + Λ) z * B) j i‖
  have hw0 : 0 ≤ gij + gji + fji := by positivity
  -- the derivative of a product `-c (u v)`
  have dprod : ∀ (d : (ℂ → ℂ) → ℂ → ℂ), AM_Der d → ∀ u v : ℂ → ℂ, AM_Sm u → AM_Sm v →
      d (fun w => -c * (u w * v w)) = fun w => -c * (d u w * v w + u w * d v w) := by
    intro d hd u v hu hv
    rw [hd.cmul _ _ (AM_sm_mul hu hv), hd.mul _ _ hu hv]
  obtain ⟨dF1, dF2⟩ := AM_dF_fun Λ B hΛ z hz h hh i j j i
  have t3 : ∀ x y t : ℂ, ‖x‖ ≤ Γ → ‖y‖ ≤ Γ →
      ‖c‖ * ‖c‖ * (‖x‖ * ‖y‖) * ‖t‖ ≤ Γ ^ 2 * ‖t‖ := by
    intro x y t hx hy
    have hcc : ‖c‖ * ‖c‖ ≤ 1 := by nlinarith [norm_nonneg c]
    have hxy : ‖x‖ * ‖y‖ ≤ Γ ^ 2 := by
      rw [sq]; exact mul_le_mul hx hy (norm_nonneg _) hΓ0
    calc ‖c‖ * ‖c‖ * (‖x‖ * ‖y‖) * ‖t‖ ≤ 1 * Γ ^ 2 * ‖t‖ := by gcongr
      _ = Γ ^ 2 * ‖t‖ := by ring
  have hab' : (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2) := by omega
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [wirt, Function.iterate_zero, id, Function.iterate_succ_apply]
    rw [dF1, dprod dW AM_der_dW _ _ (sG j j) (sF i i), (AM_dG_fun Λ hΛ z hz h hh i j j j).1,
      (AM_dF_fun Λ B hΛ z hz h hh i j i i).1]
    simp only [vG, vF]
    rw [mul_add]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖-c * (-c * (res (Matrix.of h + Λ) z j j * res (Matrix.of h + Λ) z i j) *
        (res (Matrix.of h + Λ) z * B) i i)‖ = ‖c‖ * ‖c‖ * (‖res (Matrix.of h + Λ) z j j‖ *
          ‖(res (Matrix.of h + Λ) z * B) i i‖) * gij := by
      simp only [norm_mul, norm_neg]; ring
    have e2 : ‖-c * (res (Matrix.of h + Λ) z j j * (-c * (res (Matrix.of h + Λ) z i j *
        (res (Matrix.of h + Λ) z * B) i i)))‖ = ‖c‖ * ‖c‖ * (‖res (Matrix.of h + Λ) z j j‖ *
          ‖(res (Matrix.of h + Λ) z * B) i i‖) * gij := by
      simp only [norm_mul, norm_neg]; ring
    rw [e1, e2]
    have := t3 _ _ (res (Matrix.of h + Λ) z i j) (bG j j) (bF i i)
    have : 0 ≤ gji + fji := by positivity
    nlinarith [sq_nonneg Γ]
  · simp only [wirt, Function.iterate_zero, id, Function.iterate_succ_apply]
    rw [dF2, dprod dW AM_der_dW _ _ (sG j i) (sF j i), (AM_dG_fun Λ hΛ z hz h hh i j j i).1,
      (AM_dF_fun Λ B hΛ z hz h hh i j j i).1]
    simp only [vG, vF]
    rw [mul_add]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖-c * (-c * (res (Matrix.of h + Λ) z j j * res (Matrix.of h + Λ) z i i) *
        (res (Matrix.of h + Λ) z * B) j i)‖ = ‖c‖ * ‖c‖ * (‖res (Matrix.of h + Λ) z j j‖ *
          ‖res (Matrix.of h + Λ) z i i‖) * fji := by
      simp only [norm_mul, norm_neg]; ring
    have e2 : ‖-c * (res (Matrix.of h + Λ) z j i * (-c * (res (Matrix.of h + Λ) z j j *
        (res (Matrix.of h + Λ) z * B) i i)))‖ = ‖c‖ * ‖c‖ * (‖res (Matrix.of h + Λ) z j j‖ *
          ‖(res (Matrix.of h + Λ) z * B) i i‖) * gji := by
      simp only [norm_mul, norm_neg]; ring
    rw [e1, e2]
    have h1 := t3 _ _ ((res (Matrix.of h + Λ) z * B) j i) (bG j j) (bG i i)
    have h2 := t3 _ _ (res (Matrix.of h + Λ) z j i) (bG j j) (bF i i)
    have : 0 ≤ gij := norm_nonneg _
    have : 0 ≤ gji := norm_nonneg _
    have : 0 ≤ fji := norm_nonneg _
    nlinarith [sq_nonneg Γ]
  · simp only [wirt, Function.iterate_zero, id, Function.iterate_succ_apply]
    rw [dF2, dprod dWbar AM_der_dWbar _ _ (sG j i) (sF j i), (AM_dG_fun Λ hΛ z hz h hh i j j i).2,
      (AM_dF_fun Λ B hΛ z hz h hh i j j i).2]
    simp only [vG, vF]
    rw [mul_add]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖-c * (-c * (res (Matrix.of h + Λ) z j i * res (Matrix.of h + Λ) z j i) *
        (res (Matrix.of h + Λ) z * B) j i)‖ = ‖c‖ * ‖c‖ * (‖res (Matrix.of h + Λ) z j i‖ *
          ‖res (Matrix.of h + Λ) z j i‖) * fji := by
      simp only [norm_mul, norm_neg]; ring
    have e2 : ‖-c * (res (Matrix.of h + Λ) z j i * (-c * (res (Matrix.of h + Λ) z j i *
        (res (Matrix.of h + Λ) z * B) j i)))‖ = ‖c‖ * ‖c‖ * (‖res (Matrix.of h + Λ) z j i‖ *
          ‖res (Matrix.of h + Λ) z j i‖) * fji := by
      simp only [norm_mul, norm_neg]; ring
    rw [e1, e2]
    have := t3 _ _ ((res (Matrix.of h + Λ) z * B) j i) (bG j i) (bG j i)
    have : 0 ≤ gij + gji := by positivity
    nlinarith [sq_nonneg Γ]

/-- The Leibniz bound at order two: for `a + b = 2`,
`|∂^{(a,b)} (u v)| ≤ |u| M₂(v) + 2 M₁(u) M₁(v) + M₂(u) |v|`. -/
private lemma AM_wirt2 {u v : ℂ → ℂ} (hu : AM_Sm u) (hv : AM_Sm v) (w : ℂ) (M1u M2u M1v M2v : ℝ)
    (hu1 : ∀ a b, a + b = 1 → ‖wirt a b u w‖ ≤ M1u) (hu2 : ∀ a b, a + b = 2 → ‖wirt a b u w‖ ≤ M2u)
    (hv1 : ∀ a b, a + b = 1 → ‖wirt a b v w‖ ≤ M1v) (hv2 : ∀ a b, a + b = 2 → ‖wirt a b v w‖ ≤ M2v)
    (a b : ℕ) (hab : a + b = 2) :
    ‖wirt a b (fun y => u y * v y) w‖ ≤ ‖u w‖ * M2v + 2 * (M1u * M1v) + M2u * ‖v w‖ := by
  have w0 : ∀ F : ℂ → ℂ, wirt 0 0 F w = F w := fun F => rfl
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  have m1u : 0 ≤ M1u := (norm_nonneg _).trans (hu1 1 0 rfl)
  have m1v : 0 ≤ M1v := (norm_nonneg _).trans (hv1 1 0 rfl)
  rw [AM_wirt_mul hu hv a b w]
  have hab' : (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2) := by omega
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.choose_one_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
      w0, Nat.reduceSub]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl
      le_rfl)) le_rfl) |>.trans ?_
    simp only [norm_mul, n2, mul_one, Nat.cast_ofNat]
    have := mul_le_mul (hu1 1 0 rfl) (hv1 1 0 rfl) (norm_nonneg _) m1u
    have := mul_le_mul_of_nonneg_left (hv2 2 0 rfl) (norm_nonneg (u w))
    have := mul_le_mul_of_nonneg_right (hu2 2 0 rfl) (norm_nonneg (v w))
    linarith
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self, w0]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl
      le_rfl)) ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl))) |>.trans ?_
    simp only [norm_mul]
    have := mul_le_mul (hu1 0 1 rfl) (hv1 1 0 rfl) (norm_nonneg _) m1u
    have := mul_le_mul (hu1 1 0 rfl) (hv1 0 1 rfl) (norm_nonneg _) m1u
    have := mul_le_mul_of_nonneg_left (hv2 1 1 rfl) (norm_nonneg (u w))
    have := mul_le_mul_of_nonneg_right (hu2 1 1 rfl) (norm_nonneg (v w))
    linarith
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.choose_one_right, Nat.cast_one, one_mul, mul_one, Nat.sub_zero,
      Nat.sub_self, w0, Nat.reduceSub]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl
      le_rfl)) le_rfl) |>.trans ?_
    simp only [norm_mul, n2, Nat.cast_ofNat]
    have := mul_le_mul (hu1 0 1 rfl) (hv1 0 1 rfl) (norm_nonneg _) m1u
    have := mul_le_mul_of_nonneg_left (hv2 0 2 rfl) (norm_nonneg (u w))
    have := mul_le_mul_of_nonneg_right (hu2 0 2 rfl) (norm_nonneg (v w))
    linarith

/-- The bound on the mixed derivatives of order `a + b ≤ K` of
`f' = ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p` at `h` on the good event:
`|∂^{(a,b)} f'| ≤ Γ^{a+b} (2p - 1)^{a+b} (|⟨B H̲G⟩| + β_K)^{2p-1}`. -/
private lemma AM_jet_fp {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {h : Idx D N → Idx D N → ℂ} {Γ Υ lam : ℝ} (hc : AM_Ctx D N θ Λ B z h Γ Υ lam)
    {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (K : ℕ) (i j : Idx D N) (p : ℕ) (hp : 1 ≤ p)
    (a b : ℕ) (hK : a + b ≤ K) :
    ‖wirt a b (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) (h j i)‖ ≤
      Γ ^ (a + b) * (2 * p - 1 : ℝ) ^ (a + b) *
        (‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ + AM_beta D N cq K z Υ lam) ^ (2 * p - 1) := by
  set x := ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ with hx
  set β := AM_beta D N cq K z Υ lam with hβ
  have hβ0 : 0 ≤ β := AM_beta_nonneg hc hcq K i
  have hx0 : 0 ≤ x := norm_nonneg _
  have hΓ0 : 0 ≤ Γ := by linarith [hc.hΓ]
  have hsX := AM_sm_X θ Λ B hc.hΛ z hc.hz h hc.hh i j
  have hX : ∀ a b, a + b ≤ K → ‖wirt a b (AM_X θ Λ B z h i j) (h j i)‖ ≤ Γ ^ (a + b) * (x + β) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp only [wirt, Function.iterate_zero, id, AM_X_self θ Λ B z h hc.hh, Nat.add_zero,
        pow_zero, one_mul]
      rw [← hx]
      linarith
    · refine (AM_jet_X hc hcq K i j a b hpos hab).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXc : ∀ a b, a + b ≤ K →
      ‖wirt a b (fun w => starRingEnd ℂ (AM_X θ Λ B z h i j w)) (h j i)‖ ≤
        Γ ^ (a + b) * (x + β) := by
    intro a b hab
    rw [AM_wirt_conj hsX, Complex.norm_conj, add_comm a b]
    exact hX b a (by omega)
  have h1 := AM_pow_jet hsX (h j i) Γ (x + β) K hΓ0 (by positivity) hX (p - 1)
  have h2 := AM_pow_jet (AM_sm_conj hsX) (h j i) Γ (x + β) K hΓ0 (by positivity) hXc p
  have h4 := AM_LB (AM_sm_pow hsX (p - 1)) (AM_sm_pow (AM_sm_conj hsX) p) (h j i)
    Γ ((p - 1 : ℕ) : ℝ) p _ _ K hΓ0 (by positivity) (by positivity) h1 h2 a b hK
  have e1 : ((p - 1 : ℕ) : ℝ) + p = 2 * p - 1 := by rw [Nat.cast_sub hp]; push_cast; ring
  have e2 : (x + β) ^ (p - 1) * (x + β) ^ p = (x + β) ^ (2 * p - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e1, e2] at h4
  exact h4

/-- The value `|f'(h)| = |⟨B H̲G⟩|^{2p-1}`. -/
private lemma AM_fp_self {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (p : ℕ)
    (hp : 1 ≤ p) :
    ‖AM_X θ Λ B z h i j (h j i) ^ (p - 1) * starRingEnd ℂ (AM_X θ Λ B z h i j (h j i)) ^ p‖ =
      ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) := by
  rw [AM_X_self θ Λ B z h hh, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
  congr 1; omega

set_option maxHeartbeats 1000000 in
/-- The order-two integrand on the good event: at most `K Σ_{n=1}^{2p} ϑ^n x^{2p-n}`, through
the parity bound, Ward's identity and the structure of `∂⟨B H̲G⟩`. -/
private lemma AM_high_good2 {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} {θ : ℝ}
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {h : Idx D N → Idx D N → ℂ} {Γ Υ bQ a : ℝ}
    (hc : AM_Ctx D N θ Λ B z h Γ Υ bQ) {cq : ℕ → ℕ → ℝ} (hcq : AM_QB D cq) (p : ℕ)
    (hp : 1 ≤ p) (K2 : ℝ) (hK2 : 0 ≤ K2) (hD : 1 ≤ D) (hN : 1 ≤ N) (ha : 1 ≤ a)
    (hbQ : bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3))
    (hulo : ((N : ℝ))⁻¹ ≤ Υ / ((N : ℝ) * z.im)) (huhi : Υ / ((N : ℝ) * z.im) ≤ 1)
    (hcum : ∀ i j : Idx D N, ∀ a : ℕ, a ≤ 2 → ‖ccum (μ.map fun h => h j i) a (2 - a + 1)‖ ≤
      K2 * ((Real.sqrt N) ^ (2 + 1))⁻¹) :
    ‖((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (2 + 1),
        ccum (μ.map fun h => h j i) a (2 - a + 1) / ((a.factorial * (2 - a).factorial : ℕ) : ℂ) *
          wirt a (2 - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤
      (K2 * (3 * D * (2 * p - 1) ^ 2 * (2 ^ (2 * p - 1) *
          ((2 : ℝ) ^ 2 + 1 + AM_cQ cq 2) ^ (2 * p - 1)) + 12 * (2 * p - 1) * (2 + D) + 18 * D)) *
      ∑ n ∈ Finset.Icc 1 (2 * p), (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) ^ n *
        ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) := by
  set sN := Real.sqrt N with hsN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs1 : 1 ≤ sN := by rw [hsN]; exact Real.one_le_sqrt.mpr hN1
  have hs2 : sN ^ 2 = N := Real.sq_sqrt (by linarith)
  have hs0 : 0 < sN := by linarith
  set sv := (sN ^ (2 + 1))⁻¹ with hsv
  have hsv0 : 0 ≤ sv := by positivity
  set u := Υ / ((N : ℝ) * z.im) with hu
  have hu0 : 0 ≤ u := hc.ups
  set ζ := Real.sqrt u with hζ
  have hζsq : ζ ^ 2 = u := Real.sq_sqrt hu0
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  have hζ1 : ζ ≤ 1 := by rw [hζ]; exact Real.sqrt_le_one.mpr huhi
  have hsζ : sN⁻¹ ≤ ζ := by
    rw [hζ]
    refine Real.le_sqrt_of_sq_le ?_
    rw [inv_pow, hs2]; exact hulo
  have hΓ := hc.hΓ
  have hΓ0 : 0 ≤ Γ := by linarith
  set x := ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hbQ0 : 0 ≤ bQ := hc.lam_nonneg ⟨⟨0, hD⟩, ⟨0, hN⟩⟩
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  set β2 := AM_beta D N cq 2 z Υ bQ with hβ2
  have hβ20 : 0 ≤ β2 := AM_beta_nonneg hc hcq 2 ⟨⟨0, hD⟩, ⟨0, hN⟩⟩
  set M2 := Γ ^ 2 * (2 * p - 1 : ℝ) ^ 2 * (x + β2) ^ (2 * p - 1) with hM2
  set F := fun k l => ‖(res (Matrix.of h + Λ) z * B) k l‖ with hF
  set G := fun k l => ‖res (Matrix.of h + Λ) z k l‖ with hG
  set bt := fun i j => ((D : ℝ) * N)⁻¹ * (F i j + F j i) + bQ with hbt
  set c2 := 4 * Γ ^ 2 * ((2 * p - 1) * x ^ (2 * p - 2)) with hc2
  set c3 := 2 * Γ ^ 2 * x ^ (2 * p - 1) with hc3
  set T := fun i j => M2 * F j i + c2 * bt i j + c3 * (G i j + G j i + F j i) with hT
  -- the bound per entry
  have hentry : ∀ i j : Idx D N, ∀ a : ℕ, a ≤ 2 →
      ‖ccum (μ.map fun h => h j i) a (2 - a + 1) / ((a.factorial * (2 - a).factorial : ℕ) : ℂ) *
        wirt a (2 - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤ K2 * sv * T i j := by
    intro i j a ha
    have hsF := AM_sm_F Λ B hc.hΛ z hc.hz h hc.hh i j j i
    have hsX := AM_sm_X θ Λ B hc.hΛ z hc.hz h hc.hh i j
    have hsf' : AM_Sm (fun w => AM_X θ Λ B z h i j w ^ (p - 1) *
        starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) :=
      AM_sm_mul (AM_sm_pow hsX _) (AM_sm_pow (AM_sm_conj hsX) _)
    have hfe : AM_f θ Λ B z h i j p = fun w => AM_F Λ B z h i j j i w *
        (fun w => AM_X θ Λ B z h i j w ^ (p - 1) * starRingEnd ℂ (AM_X θ Λ B z h i j w) ^ p) w :=
      funext fun w => by simp only [AM_f]; ring
    obtain ⟨d1, d2⟩ := AM_jet_f1 hc i j p hp
    have hw := AM_wirt2 hsF hsf' (h j i) (2 * Γ ^ 2) (2 * Γ ^ 2 * (G i j + G j i + F j i))
      ((2 * p - 1) * bt i j * x ^ (2 * p - 2)) M2
      (fun a b hab => by
        have := AM_jet_F hc i j j i a b
        rw [hab] at this
        simpa [show 1 + a + b = 2 by omega] using this)
      (fun a b hab => AM_jet_F2 hc i j a b hab)
      (fun a b hab => by
        rcases (show (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact d1
        · exact d2)
      (fun a b hab => by
        have := AM_jet_fp hc hcq 2 i j p hp a b (by omega)
        rw [hab] at this
        rw [hM2]; linarith)
      a (2 - a) (by omega)
    have hg0 : ‖AM_F Λ B z h i j j i (h j i)‖ = F j i := by
      simp only [AM_F, AM_setEntry_self h hc.hh, hF]
    have hv0 := AM_fp_self θ Λ B z h hc.hh i j p hp
    rw [hfe, norm_mul]
    refine mul_le_mul ((AM_norm_div_nat _ _ (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)))).trans
        (hcum i j a ha)) ?_ (norm_nonneg _) (mul_nonneg hK2 hsv0)
    refine hw.trans (le_of_eq ?_)
    rw [hg0, hv0, hT]
    ring
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have hninv : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  set ν := ((D : ℝ) * N)⁻¹ with hν
  have hν0 : 0 ≤ ν := by positivity
  have step1 : ‖((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (2 + 1),
        ccum (μ.map fun h => h j i) a (2 - a + 1) / ((a.factorial * (2 - a).factorial : ℕ) : ℂ) *
          wirt a (2 - a) (AM_f θ Λ B z h i j p) (h j i)‖ ≤
      ν * ∑ i, ∑ j, 3 * (K2 * sv * T i j) := by
    rw [norm_mul, hninv]
    refine mul_le_mul_of_nonneg_left ?_ hν0
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Finset.range (2 + 1), ‖ccum (μ.map fun h => h j i) a (2 - a + 1) /
          ((a.factorial * (2 - a).factorial : ℕ) : ℂ) *
          wirt a (2 - a) (AM_f θ Λ B z h i j p) (h j i)‖
        ≤ ∑ _a ∈ Finset.range (2 + 1), K2 * sv * T i j :=
          Finset.sum_le_sum fun a ha => hentry i j a
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
      _ = 3 * (K2 * sv * T i j) := by simp
  obtain ⟨-, hS1, hSG⟩ := AM_ward_sums hc
  set L := (D : ℝ) ^ 2 * N ^ 2 * ζ with hL
  have hA2 : ∑ i, ∑ j, F i j ≤ L := hS1
  have hA1 : ∑ i, ∑ j, F j i ≤ L := by rw [Finset.sum_comm]; exact hS1
  have hA3 : ∑ i, ∑ j, G i j ≤ L := hSG
  have hA4 : ∑ i, ∑ j, G j i ≤ L := by rw [Finset.sum_comm]; exact hSG
  have hsumT : ∑ i, ∑ j, T i j = M2 * (∑ i, ∑ j, F j i) +
      c2 * (ν * ((∑ i, ∑ j, F i j) + ∑ i, ∑ j, F j i) + ((D : ℝ) * N) ^ 2 * bQ) +
      c3 * ((∑ i, ∑ j, G i j) + (∑ i, ∑ j, G j i) + ∑ i, ∑ j, F j i) := by
    simp only [hT, hbt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcard]
    ring
  -- the three power-counting facts
  have hNsv : (N : ℝ) * sv ≤ ζ := by
    have : (N : ℝ) * sv = sN⁻¹ := by
      rw [hsv, ← hs2]; field_simp
    rw [this]; exact hsζ
  have f1 : (N : ℝ) * sv * ζ ≤ u := by
    calc (N : ℝ) * sv * ζ ≤ ζ * ζ := by gcongr
      _ = u := by rw [← hζsq]; ring
  have f2 : sv * ζ ≤ u ^ 2 := by
    have : sv ≤ ζ ^ 3 := by
      rw [hsv, ← inv_pow]; exact pow_le_pow_left₀ (by positivity) hsζ 3
    calc sv * ζ ≤ ζ ^ 3 * ζ := by gcongr
      _ = u ^ 2 := by rw [← hζsq]; ring
  have hρ1 : 1 ≤ a * (1 + ‖z‖) ^ 2 := by
    have : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg z])
    nlinarith
  obtain ⟨ρ4, hρ4⟩ : ∃ r : ℝ, r = a * (1 + ‖z‖) ^ 2 * Γ ^ 4 := ⟨_, rfl⟩
  have hρ41 : 1 ≤ ρ4 := by
    have := mul_le_mul hρ1 (one_le_pow₀ (n := 4) hΓ) zero_le_one (by positivity)
    rw [hρ4]; rwa [one_mul] at this
  have hbQ' : bQ ≤ ρ4 * ζ ^ 3 := by rw [hρ4]; linarith [hbQ]
  have f3 : (D : ℝ) * N * sv * bQ ≤ D * (ρ4 * u ^ 2) := by
    calc (D : ℝ) * N * sv * bQ = D * ((N * sv) * bQ) := by ring
      _ ≤ D * (ζ * (ρ4 * ζ ^ 3)) := by gcongr
      _ = D * (ρ4 * u ^ 2) := by rw [← hζsq]; ring
  obtain ⟨ϑ, hϑ⟩ : ∃ t : ℝ, t = a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * u := ⟨_, rfl⟩
  have hϑρ : ϑ = ρ4 * u * Γ ^ 2 := by rw [hϑ, hρ4]; ring
  have hϑ0 : 0 ≤ ϑ := by rw [hϑρ]; positivity
  rw [← hϑ]
  have hM20 : 0 ≤ M2 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by positivity
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨Sg, hSg⟩ : ∃ t : ℝ, t = ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n * x ^ (2 * p - n) :=
    ⟨_, rfl⟩
  rw [← hSg]
  have hn1 : ϑ * x ^ (2 * p - 1) ≤ Sg := by
    have := Finset.single_le_sum (f := fun n => ϑ ^ n * x ^ (2 * p - n))
      (fun n _ => by positivity) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩ : 1 ∈ Finset.Icc 1 (2 * p))
    rw [hSg]; simpa using this
  have hn2 : ϑ ^ 2 * x ^ (2 * p - 2) ≤ Sg := by
    rw [hSg]
    exact Finset.single_le_sum (f := fun n => ϑ ^ n * x ^ (2 * p - n))
      (fun n _ => by positivity) (Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩)
  -- term 1 through the binomial bound
  have hβ := AM_beta_good cq 2 z Γ Υ bQ a hD hN (AM_cQ_nonneg hcq 2) hΓ ha hbQ hu0 hulo huhi
  rw [← hu, ← hβ2, ← hρ4] at hβ
  obtain ⟨Cβ, hCβ⟩ : ∃ t : ℝ, t = ((2 : ℕ) : ℝ) ^ 2 + 1 + AM_cQ cq 2 := ⟨_, rfl⟩
  rw [← hCβ] at hβ
  have hCβ1 : 1 ≤ Cβ := by rw [hCβ]; have := AM_cQ_nonneg hcq 2; push_cast; linarith
  have hpb := AM_poly_bound (Γ ^ 2 * u) (Cβ * (ρ4 * u)) ϑ x Cβ hϑ0 hx0 hCβ1 (2 * p - 1)
    (fun q _ => by
      have e : ϑ ^ (q + 1) = (ρ4 * u) ^ q * (Γ ^ 2) ^ q * (ρ4 * u * Γ ^ 2) := by
        rw [hϑρ, pow_succ, mul_pow]
      rw [e, mul_pow]
      have hΓ2q : 1 ≤ (Γ ^ 2) ^ q := one_le_pow₀ (one_le_pow₀ hΓ)
      have hA : 0 ≤ Cβ ^ q * (ρ4 * u) ^ q := by positivity
      have hΓu : Γ ^ 2 * u ≤ ρ4 * u * Γ ^ 2 := by
        have : u ≤ ρ4 * u := le_mul_of_one_le_left hu0 hρ41
        calc Γ ^ 2 * u ≤ Γ ^ 2 * (ρ4 * u) := mul_le_mul_of_nonneg_left this (by positivity)
          _ = ρ4 * u * Γ ^ 2 := by ring
      calc Γ ^ 2 * u * (Cβ ^ q * (ρ4 * u) ^ q) ≤ (ρ4 * u * Γ ^ 2) * (Cβ ^ q * (ρ4 * u) ^ q) :=
            mul_le_mul_of_nonneg_right hΓu hA
        _ = (Cβ ^ q * (ρ4 * u) ^ q) * 1 * (ρ4 * u * Γ ^ 2) := by ring
        _ ≤ (Cβ ^ q * (ρ4 * u) ^ q) * (Γ ^ 2) ^ q * (ρ4 * u * Γ ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΓ2q hA) (by positivity)
        _ = Cβ ^ q * ((ρ4 * u) ^ q * (Γ ^ 2) ^ q * (ρ4 * u * Γ ^ 2)) := by ring)
  rw [show 2 * p - 1 + 1 = 2 * p by omega, ← hSg] at hpb
  have hxb : (x + β2) ^ (2 * p - 1) ≤ (x + Cβ * (ρ4 * u)) ^ (2 * p - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have T1 : M2 * u ≤ (2 * p - 1) ^ 2 * (2 ^ (2 * p - 1) * Cβ ^ (2 * p - 1) * Sg) := by
    calc M2 * u = (2 * p - 1 : ℝ) ^ 2 * (Γ ^ 2 * u * (x + β2) ^ (2 * p - 1)) := by
          rw [hM2]; ring
      _ ≤ (2 * p - 1 : ℝ) ^ 2 * (Γ ^ 2 * u * (x + Cβ * (ρ4 * u)) ^ (2 * p - 1)) := by gcongr
      _ ≤ _ := by gcongr
  have T2 : Γ ^ 2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2)) ≤ (2 + D) * ϑ ^ 2 := by
    have e2 : Γ ^ 2 * (ρ4 * u ^ 2) ≤ ϑ ^ 2 := by
      have e : ϑ ^ 2 = Γ ^ 2 * (ρ4 * u ^ 2) * (ρ4 * Γ ^ 2) := by rw [hϑρ]; ring
      rw [e]
      exact le_mul_of_one_le_right (by positivity)
        (one_le_mul_of_one_le_of_one_le hρ41 (one_le_pow₀ hΓ))
    have e1 : Γ ^ 2 * u ^ 2 ≤ Γ ^ 2 * (ρ4 * u ^ 2) := by
      have : u ^ 2 ≤ ρ4 * u ^ 2 := le_mul_of_one_le_left (by positivity) hρ41
      gcongr
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have e3 := mul_le_mul_of_nonneg_left e2 hD0
    calc Γ ^ 2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2)) = 2 * (Γ ^ 2 * u ^ 2) +
          D * (Γ ^ 2 * (ρ4 * u ^ 2)) := by ring
      _ ≤ 2 * ϑ ^ 2 + D * ϑ ^ 2 := add_le_add (by linarith) e3
      _ = (2 + D) * ϑ ^ 2 := by ring
  have T3 : Γ ^ 2 * u ≤ ϑ := by
    rw [hϑρ]
    have : u ≤ ρ4 * u := le_mul_of_one_le_left hu0 hρ41
    calc Γ ^ 2 * u ≤ Γ ^ 2 * (ρ4 * u) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = ρ4 * u * Γ ^ 2 := by ring
  refine step1.trans ?_
  have hDN0 : (0 : ℝ) < (D : ℝ) * N := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    positivity
  have hνL : ν * L = (D : ℝ) * N * ζ := by rw [hν, hL]; field_simp
  have hννL : ν * ν * L = ζ := by rw [hν, hL]; field_simp
  have hνD : ν * ((D : ℝ) * N) ^ 2 = (D : ℝ) * N := by rw [hν]; field_simp
  have hS : ∑ i, ∑ j, 3 * (K2 * sv * T i j) = 3 * (K2 * sv) * ∑ i, ∑ j, T i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hS, hsumT]
  set A1 := ∑ i, ∑ j, F j i
  set A2 := ∑ i, ∑ j, F i j
  set A3 := ∑ i, ∑ j, G i j
  set A4 := ∑ i, ∑ j, G j i
  have hDu : (D : ℝ) * N * sv * ζ ≤ D * u := by
    calc (D : ℝ) * N * sv * ζ = D * ((N : ℝ) * sv * ζ) := by ring
      _ ≤ D * u := by gcongr
  have B1 : ν * sv * (M2 * A1) ≤ D * (M2 * u) := by
    calc ν * sv * (M2 * A1) ≤ ν * sv * (M2 * L) := by gcongr
      _ = M2 * sv * (ν * L) := by ring
      _ = M2 * ((D : ℝ) * N * sv * ζ) := by rw [hνL]; ring
      _ ≤ M2 * (D * u) := by gcongr
      _ = D * (M2 * u) := by ring
  have B2 : ν * sv * (c2 * (ν * (A2 + A1) + ((D : ℝ) * N) ^ 2 * bQ)) ≤
      c2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2)) := by
    calc ν * sv * (c2 * (ν * (A2 + A1) + ((D : ℝ) * N) ^ 2 * bQ))
        ≤ ν * sv * (c2 * (ν * (L + L) + ((D : ℝ) * N) ^ 2 * bQ)) := by gcongr
      _ = c2 * (2 * (sv * (ν * ν * L)) + (ν * ((D : ℝ) * N) ^ 2) * sv * bQ) := by ring
      _ = c2 * (2 * (sv * ζ) + (D : ℝ) * N * sv * bQ) := by rw [hννL, hνD]
      _ ≤ c2 * (2 * u ^ 2 + D * (ρ4 * u ^ 2)) := by gcongr
      _ = c2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2)) := by ring
  have B3 : ν * sv * (c3 * (A3 + A4 + A1)) ≤ 3 * D * (c3 * u) := by
    calc ν * sv * (c3 * (A3 + A4 + A1)) ≤ ν * sv * (c3 * (L + L + L)) := by gcongr
      _ = 3 * c3 * sv * (ν * L) := by ring
      _ = 3 * c3 * ((D : ℝ) * N * sv * ζ) := by rw [hνL]; ring
      _ ≤ 3 * c3 * (D * u) := by gcongr
      _ = 3 * D * (c3 * u) := by ring
  have C1 : D * (M2 * u) ≤ D * ((2 * p - 1) ^ 2 * (2 ^ (2 * p - 1) * Cβ ^ (2 * p - 1) * Sg)) := by
    gcongr
  have C2 : c2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2)) ≤ 4 * (2 * p - 1) * (2 + D) * Sg := by
    calc c2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2)) = 4 * ((2 * p - 1) * x ^ (2 * p - 2)) *
          (Γ ^ 2 * (u ^ 2 * 2 + D * (ρ4 * u ^ 2))) := by rw [hc2]; ring
      _ ≤ 4 * ((2 * p - 1) * x ^ (2 * p - 2)) * ((2 + D) * ϑ ^ 2) := by gcongr
      _ = 4 * (2 * p - 1) * (2 + D) * (ϑ ^ 2 * x ^ (2 * p - 2)) := by ring
      _ ≤ 4 * (2 * p - 1) * (2 + D) * Sg := by gcongr
  have C3 : 3 * D * (c3 * u) ≤ 6 * D * Sg := by
    calc 3 * D * (c3 * u) = 6 * D * (Γ ^ 2 * u * x ^ (2 * p - 1)) := by rw [hc3]; ring
      _ ≤ 6 * D * (ϑ * x ^ (2 * p - 1)) := by gcongr
      _ ≤ 6 * D * Sg := by gcongr
  have hCβe : Cβ = (2 : ℝ) ^ 2 + 1 + AM_cQ cq 2 := by rw [hCβ]; push_cast; ring
  rw [← hCβe]
  calc ν * (3 * (K2 * sv) * (M2 * A1 + c2 * (ν * (A2 + A1) + ((D : ℝ) * N) ^ 2 * bQ) +
        c3 * (A3 + A4 + A1)))
      = 3 * K2 * (ν * sv * (M2 * A1) + ν * sv * (c2 * (ν * (A2 + A1) +
          ((D : ℝ) * N) ^ 2 * bQ)) + ν * sv * (c3 * (A3 + A4 + A1))) := by ring
    _ ≤ 3 * K2 * (D * ((2 * p - 1) ^ 2 * (2 ^ (2 * p - 1) * Cβ ^ (2 * p - 1) * Sg)) +
          4 * (2 * p - 1) * (2 + D) * Sg + 6 * D * Sg) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (B1.trans C1) (B2.trans C2))
          (B3.trans C3)) (mul_nonneg (by norm_num) hK2)
    _ = _ := by ring

/-- The order-`k` part of the averaged moment inequality for `2 ≤ k ≤ 16p + 16` (up to the order
at which the expansion is truncated): `≤ K Σ_{n=1}^{2p} ϑ^n E|⟨B H̲G⟩|^{2p-n}` plus the bad-event
term, with `ϑ` as in `avg_order_one`. -/
theorem avg_order_high' (D p k : ℕ) (hp : 1 ≤ p) (hk : 2 ≤ k) (hk' : k ≤ 16 * p + 16)
    (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ Γ Υ a bQ ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im → 1 ≤ a →
        bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3) →
        μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ≤ ENNReal.ofReal ε₀ →
        ‖avgTerm D N θ μ Λ B z p k‖ ≤
          K * (∑ n ∈ Finset.Icc 1 (2 * p),
              (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) ^ n *
              ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ) +
            K * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
  obtain ⟨cq, hcq⟩ := AM_QB_exists D
  choose Kc hKc using fun a q => llClass_ccum_le C a q
  set Kk : ℝ := ∑ a ∈ Finset.range (k + 1), |Kc a (k - a + 1)| with hKk
  have hKk0 : 0 ≤ Kk := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hcQ2 := AM_cQ_nonneg hcq 2
  have hcQk := AM_cQ_nonneg hcq k
  have hcq0 := (hcq 0 0).1
  set K2 : ℝ := Kk * (3 * D * (2 * p - 1) ^ 2 * (2 ^ (2 * p - 1) *
    ((2 : ℝ) ^ 2 + 1 + AM_cQ cq 2) ^ (2 * p - 1)) + 12 * (2 * p - 1) * (2 + D) + 18 * D) with hK2
  set K3 : ℝ := (D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) *
    (2 ^ (2 * p - 1) * ((k : ℝ) ^ k + 1 + AM_cQ cq k) ^ (2 * p - 1)) with hK3
  set Kr : ℝ := (D : ℝ) * ((k + 1) * Kk) * ((2 * p : ℝ) ^ k * (((1 + k : ℕ) : ℝ) ^ k)) *
    (4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k)) ^ (2 * p - 1) with hKr
  have hK20 : 0 ≤ K2 := by
    rw [hK2]
    have : (0 : ℝ) ≤ 2 ^ 2 + 1 + AM_cQ cq 2 := by positivity
    exact mul_nonneg hKk0 (by positivity)
  have hK30 : 0 ≤ K3 := by
    rw [hK3]
    have : (0 : ℝ) ≤ (k : ℝ) ^ k + 1 + AM_cQ cq k := by positivity
    positivity
  have hKr0 : 0 ≤ Kr := by
    rw [hKr]
    have : (0 : ℝ) ≤ 4 + (k : ℝ) ^ k + 2 * (cq 0 0 + AM_cQ cq k) := by positivity
    positivity
  refine ⟨K2 + K3 + Kr, by positivity, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hz1 hz2 Γ Υ a bQ ε₀ hΓ1 hΓ2 hηΥ hΥ ha hbQ hbad
  obtain ⟨hN, hη, hηinv, hηN, hzN, hΓ6, -, hulo, huhi⟩ := AM_setup hz1 hz2 hΓ1 hΓ2 hηΥ hΥ
  have hprob := hμ.prob
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set ϑ := a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im)) with hϑ
  have hϑ0 : 0 ≤ ϑ := by
    have := hη.le.trans hηΥ
    have : (0 : ℝ) ≤ a := by linarith
    positivity
  have hRHS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
      ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    have e1 : avgTerm 0 N θ μ Λ B z p k = 0 := by simp [avgTerm]
    rw [e1, norm_zero]
    positivity
  have hcum : ∀ i j : Idx D N, ∀ a ≤ k, ‖ccum (μ.map fun h => h j i) a (k - a + 1)‖ ≤
      Kk * ((Real.sqrt N) ^ (k + 1))⁻¹ := by
    intro i j a ha
    have h1 := hKc a (k - a + 1) D N θ μ hμ j i
    rw [show a + (k - a + 1) = k + 1 by omega, AM_rpow_half] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f := fun a => |Kc a (k - a + 1)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  rw [AM_avgTerm_int hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN p hp k]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint : ∀ n : ℕ, Integrable (fun h => ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ n) μ :=
    fun n => AM_int_xpow hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN n
  have hGd : Integrable (fun h => (K2 + K3) * ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
      ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n)) μ :=
    (integrable_finsetSum _ fun n _ => (hint _).const_mul _).const_mul _
  have hsplit := AM_split (fun h => ‖((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ a ∈ Finset.range (k + 1),
      ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
        wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i)‖)
    (fun h => (K2 + K3) * ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
      ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n))
    (avgGood D N θ Λ B z Γ Υ bQ)ᶜ (Kr * (N : ℝ) ^ (21 * (p : ℝ) + 18)) ε₀ hGd
    (fun h => mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => by positivity))
    (by positivity) hbad (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (by
      filter_upwards [hμ.herm] with h hh hin
      have hΩ : h ∈ avgGood D N θ Λ B z Γ Υ bQ := not_not.mp hin
      have hc : AM_Ctx D N θ Λ B z h Γ Υ bQ :=
        ⟨hθ0, hθ1, hΛ, hΛn, hB, hη, hh, hΓ1, hηΥ, hΩ.1, hΩ.2⟩
      have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
          ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) :=
        Finset.sum_nonneg fun n _ => by positivity
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · have hk2 : k = 2 := by omega
        subst hk2
        refine (AM_high_good2 hc hcq p hp Kk hKk0 hD hN ha hbQ hulo huhi hcum).trans ?_
        rw [← hK2]
        exact mul_le_mul_of_nonneg_right (by linarith) hS0
      · refine (AM_high_good3 hc hcq p hp k hk3 Kk hKk0 hD hN ha hbQ hulo huhi hΓ6 hcum).trans ?_
        rw [← hK3]
        exact mul_le_mul_of_nonneg_right (by linarith) hS0)
    (by
      filter_upwards [hμ.herm] with h hh
      have hc := AM_crude_ctx hθ0 hθ1 hΛ hΛn hB hη hh hcq N hN1 hηinv hηN
      refine (AM_high_crude hcq hc p hp k hk hk' Kk hKk0 hD hN hzN hηinv hcum).trans ?_
      rw [← hKr])
  refine hsplit.trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun n _ => (hint _).const_mul _]
  simp only [integral_const_mul]
  have e1 : (K2 + K3) * ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
      ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ ≤
      (K2 + K3 + Kr) * ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
      ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ :=
    mul_le_mul_of_nonneg_right (by linarith) hRHS0
  have e2 : Kr * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ ≤
      (K2 + K3 + Kr) * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
    gcongr; linarith
  linarith

/-! ### The assembly of the averaged moment inequality -/

/-- The full index set of `Fin 1` is not empty. -/
private lemma AM_ne_bot : (Finset.univ : Finset (Fin 1)) ≠ ⊥ := by simp

/-- The only set partition of `Fin 1` is the one with a single block. -/
private lemma AM_part_one (π : Finpartition (Finset.univ : Finset (Fin 1))) :
    π = Finpartition.indiscrete AM_ne_bot := by
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

/-- `𝒞^{(0,1)}(h_{ij}) = E h̄_{ij} = 0` for the class. -/
private lemma AM_ccum01 {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h i j) 0 1 = 0 := by
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  unfold ccum jointCum
  rw [Finset.sum_eq_single (Finpartition.indiscrete AM_ne_bot)
    (fun π _ hπ => absurd (AM_part_one π) hπ) (by simp)]
  simp only [Finpartition.indiscrete_parts, Finset.card_singleton, Nat.sub_self, pow_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, Finset.prod_singleton]
  have e : ∀ z : ℂ, ∏ k ∈ (Finset.univ : Finset (Fin (0 + 1))),
      (if (k : ℕ) < 0 then (fun z => z) else (fun z => starRingEnd ℂ z)) z = starRingEnd ℂ z := by
    intro z
    simp
  simp only [e]
  rw [integral_map hmeas.aemeasurable Complex.continuous_conj.aestronglyMeasurable, integral_conj,
    hμ.mean i j, map_zero]

/-- Regrouping the double sum of the expansion by the order `k = p + q`. -/
private lemma AM_regroup (F : ℕ → ℕ → ℂ) (l : ℕ) :
    ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), F p q =
      ∑ k ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (k + 1), F a (k - a) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have e1 : ∑ p ∈ Finset.range (l + 1 + 1), ∑ q ∈ Finset.range (l + 1 + 1 - p), F p q =
        ∑ p ∈ Finset.range (l + 1 + 1), ((∑ q ∈ Finset.range (l + 1 - p), F p q) +
          F p (l + 1 - p)) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p ≤ l + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      rw [show l + 1 + 1 - p = (l + 1 - p) + 1 by omega, Finset.sum_range_succ]
    rw [e1, Finset.sum_add_distrib, Finset.sum_range_succ (fun p => ∑ q ∈ Finset.range (l + 1 - p),
      F p q), ih, Finset.sum_range_succ (fun k => ∑ a ∈ Finset.range (k + 1), F a (k - a)) (l + 1),
      Finset.sum_range_succ (fun a => F a (l + 1 - a)) (l + 1)]
    simp

/-- `⟨B H G⟩ = (DN)⁻¹ Σ_{i,j} (G B)_{ji} h̄_{ji}` for a Hermitian array. -/
private lemma AM_ntrHG {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ntr (B * (Matrix.of h * res (Matrix.of h + Λ) z)) = ((D : ℂ) * N)⁻¹ *
      ∑ i, ∑ j, (res (Matrix.of h + Λ) z * B) j i * starRingEnd ℂ (h j i) := by
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  rw [AM_ntr_eq]
  congr 1
  have : (B * (Matrix.of h * res (Matrix.of h + Λ) z)).trace =
      (Matrix.of h * (res (Matrix.of h + Λ) z * B)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [show ∑ r, (B * (Matrix.of h * res (Matrix.of h + Λ) z)) r r =
    (B * (Matrix.of h * res (Matrix.of h + Λ) z)).trace from rfl, this]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h1 i j]
  ring

/-- On a Hermitian array `AM_Pf` takes the value `(G B)_{ji} ⟨B H̲G⟩^{p-1} conj⟨B H̲G⟩^p`. -/
private lemma AM_eval_Pf_self {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (p : ℕ) :
    resPolyEval (AM_Pf D N θ Λ B z i j p) h = (res (Matrix.of h + Λ) z * B) j i *
      ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
      starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p := by
  have := congrFun (AM_f_eq θ Λ B hΛ z hz h hh i j p) (h j i)
  simp only [AM_setEntry_self h hh] at this
  rw [← this]
  simp only [AM_f, AM_F, AM_X, AM_setEntry_self h hh]

/-- `√(x + y) ≤ √x + √y` for `y ≥ 0`. -/
private lemma AM_sqrt_add (x y : ℝ) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hx
    have := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  · rw [Real.sqrt_eq_zero'.mpr hx.le, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)

/-- The truncation remainder at `ℓ = 14p + 2`, `m = 4p - 1`:
`N (4N)^{2p-1} N^{-(ℓ+2)/2} (6Γ)^{m+ℓ+1} ≤ 4^{2p-1} 6^{18p+2} N^{-2p-1}` for `Γ⁶ ≤ N`. -/
private lemma AM_rem1 {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (hp : 1 ≤ p) (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (hΓ6 : Γ ^ 6 ≤ N) :
    (N : ℝ) * (4 * N) ^ (2 * p - 1) * ((N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) *
      (6 * Γ) ^ (4 * p - 1 + (14 * p + 2) + 1)) ≤
      4 ^ (2 * p - 1) * 6 ^ (18 * p + 2) * (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : (N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) = ((N : ℝ) ^ (7 * p + 2))⁻¹ := by
    rw [show -(((14 * p + 2 : ℕ) : ℝ) + 2) / 2 = -((7 * p + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hN0.le, Real.rpow_natCast]
  have e2 : (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) = ((N : ℝ) ^ (2 * p + 1))⁻¹ := by
    rw [show -(2 * (p : ℝ) + 1) = -((2 * p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hN0.le, Real.rpow_natCast]
  rw [e1, e2, show 4 * p - 1 + (14 * p + 2) + 1 = 18 * p + 2 by omega]
  have hΓ0 : 0 ≤ Γ := by linarith
  have hG : Γ ^ (18 * p + 2) ≤ (N : ℝ) ^ (3 * p + 1) := by
    calc Γ ^ (18 * p + 2) ≤ Γ ^ (6 * (3 * p + 1)) := pow_le_pow_right₀ hΓ (by omega)
      _ = (Γ ^ 6) ^ (3 * p + 1) := by rw [pow_mul]
      _ ≤ (N : ℝ) ^ (3 * p + 1) := pow_le_pow_left₀ (by positivity) hΓ6 _
  calc (N : ℝ) * (4 * N) ^ (2 * p - 1) * (((N : ℝ) ^ (7 * p + 2))⁻¹ * (6 * Γ) ^ (18 * p + 2))
      = 4 ^ (2 * p - 1) * 6 ^ (18 * p + 2) * ((N : ℝ) * N ^ (2 * p - 1) * Γ ^ (18 * p + 2) *
        ((N : ℝ) ^ (7 * p + 2))⁻¹) := by rw [mul_pow, mul_pow]; ring
    _ ≤ 4 ^ (2 * p - 1) * 6 ^ (18 * p + 2) * ((N : ℝ) * N ^ (2 * p - 1) * N ^ (3 * p + 1) *
        ((N : ℝ) ^ (7 * p + 2))⁻¹) := by gcongr
    _ = 4 ^ (2 * p - 1) * 6 ^ (18 * p + 2) * ((N : ℝ) ^ (2 * p + 1))⁻¹ := by
        congr 1
        have e : (N : ℝ) ^ (7 * p + 2) = ((N : ℝ) * N ^ (2 * p - 1) * N ^ (3 * p + 1)) *
            (N : ℝ) ^ (2 * p + 1) := by
          rw [← pow_succ', ← pow_add, ← pow_add]; congr 1; omega
        rw [e]
        have : (0 : ℝ) < (N : ℝ) * N ^ (2 * p - 1) * N ^ (3 * p + 1) := by positivity
        field_simp

/-- The tail term: `(σ)^{1/2} ≤ 24^{3κ} N^{-κ}` for `σ = (N^{1/2}/(24Γ))^{-6κ}` and `Γ⁶ ≤ N`. -/
private lemma AM_sigma {N : ℕ} (hN : 1 ≤ N) (Γ : ℝ) (hΓ : 1 ≤ Γ) (hΓ6 : Γ ^ 6 ≤ N) (κ : ℕ) :
    Real.sqrt (((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-((6 * κ : ℕ) : ℝ))) ≤
      24 ^ (3 * κ) * ((N : ℝ) ^ κ)⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set sN := (N : ℝ) ^ ((1 : ℝ) / 2) with hsN
  have hs0 : 0 < sN := Real.rpow_pos_of_pos hN0 _
  have hs2 : sN ^ 2 = N := by
    rw [hsN, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hΓ0 : 0 < Γ := by linarith
  have hΓ3 : Γ ^ 3 ≤ sN := by
    have : (Γ ^ 3) ^ 2 ≤ sN ^ 2 := by
      rw [hs2, ← pow_mul]
      exact hΓ6
    exact (pow_le_pow_iff_left₀ (by positivity) hs0.le two_ne_zero).mp this
  set t := sN * (24 * Γ)⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have ht3 : (N : ℝ) / 24 ^ 3 ≤ t ^ 3 := by
    rw [ht, mul_pow, inv_pow, mul_pow, ← hs2]
    rw [div_le_iff₀ (by norm_num)]
    have : sN ^ 2 * (24 ^ 3 * Γ ^ 3) ≤ sN ^ 3 * 24 ^ 3 := by
      have := mul_le_mul_of_nonneg_left hΓ3 (show (0 : ℝ) ≤ sN ^ 2 * 24 ^ 3 by positivity)
      nlinarith
    calc sN ^ 2 = sN ^ 2 * (24 ^ 3 * Γ ^ 3) * (24 ^ 3 * Γ ^ 3)⁻¹ := by field_simp
      _ ≤ sN ^ 3 * 24 ^ 3 * (24 ^ 3 * Γ ^ 3)⁻¹ := by gcongr
      _ = sN ^ 3 * (24 ^ 3 * Γ ^ 3)⁻¹ * 24 ^ 3 := by ring
  have hσ : t ^ (-((6 * κ : ℕ) : ℝ)) ≤ (24 ^ (3 * κ) * ((N : ℝ) ^ κ)⁻¹) ^ 2 := by
    rw [Real.rpow_neg ht0.le, Real.rpow_natCast]
    have h1 : ((N : ℝ) / 24 ^ 3) ^ (2 * κ) ≤ t ^ (6 * κ) := by
      rw [show t ^ (6 * κ) = (t ^ 3) ^ (2 * κ) by rw [← pow_mul]; ring_nf]
      exact pow_le_pow_left₀ (by positivity) ht3 _
    have h2 : 0 < ((N : ℝ) / 24 ^ 3) ^ (2 * κ) := by positivity
    calc (t ^ (6 * κ))⁻¹ ≤ (((N : ℝ) / 24 ^ 3) ^ (2 * κ))⁻¹ := inv_anti₀ h2 h1
      _ = (24 ^ (3 * κ) * ((N : ℝ) ^ κ)⁻¹) ^ 2 := by
          rw [div_pow, ← pow_mul, inv_div, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
          rw [show 3 * (2 * κ) = 3 * κ * 2 by ring, show κ * 2 = 2 * κ by ring]
          field_simp
  calc Real.sqrt (t ^ (-((6 * κ : ℕ) : ℝ))) ≤ Real.sqrt ((24 ^ (3 * κ) * ((N : ℝ) ^ κ)⁻¹) ^ 2) :=
        Real.sqrt_le_sqrt hσ
    _ = 24 ^ (3 * κ) * ((N : ℝ) ^ κ)⁻¹ := Real.sqrt_sq (by positivity)

/-- `h ↦ AM_Pf(h) h̄_{ji}` is integrable. -/
private lemma AM_int_PfH {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (hB : opNorm B ≤ 1) {z : ℂ} (hz : 0 < z.im) (c : ℝ) (hc1 : 1 ≤ c) (hcη : z.im⁻¹ ≤ c)
    (hηc : z.im ≤ c) (i j : Idx D N) (p : ℕ) :
    Integrable (fun h => resPolyEval (AM_Pf D N θ Λ B z i j p) h * starRingEnd ℂ (h j i)) μ := by
  have := hμ.prob
  obtain ⟨cq, hcq⟩ := AM_QB_exists D
  have hmeasc : Measurable fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h j i) :=
    Complex.continuous_conj.measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply j))
  have hg : Integrable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h j i)) μ := by
    refine Integrable.mono' (hμ.integrable 1 j i) hmeasc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun h => by simp
  refine hg.bdd_mul (c := AM_wt (AM_Pf D N θ Λ B z i j p) * c ^ (1 + (p - 1) * 2 + p * 2))
    (AM_meas_poly _).aestronglyMeasurable ?_
  filter_upwards [hμ.herm] with h hh
  exact AM_eval_le (AM_Pf_ok D N θ Λ B z i j p) h c hc1
    (AM_crude_ctx hθ0 hθ1 hΛ hΛn hB hz hh hcq c hc1 hcη hηc).forms

/-- The averaged moment inequality for one member of the class:
`E|⟨B H̲G⟩|^{2p} ≤ K Σ_{n=1}^{2p} ϑ^n E|⟨B H̲G⟩|^{2p-n} + K (N^{-2p-1} + N^{21p+18} ε₀^{1/2})`,
with `ϑ = a (1 + |z|)² Γ⁶ Υ/(Nη)`, on the good event `avgGood` with
`λ_Q ≤ a (1 + |z|)² Γ⁴ (Υ/(Nη))^{3/2}` off probability `ε₀`. -/
theorem avg_moment_ineq (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ Γ Υ a bQ ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im → 1 ≤ a →
        bQ ≤ a * ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3) →
        μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ≤ ENNReal.ofReal ε₀ →
        ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p) ∂μ ≤
          K * (∑ n ∈ Finset.Icc 1 (2 * p),
              (a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im))) ^ n *
              ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ) +
            K * ((N : ℝ) ^ (-(2 * (p : ℝ) + 1)) +
              (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
  obtain ⟨KE, hKE0, hKE⟩ := expansion_hp (14 * p + 2) (1 + (p - 1) * 2 + p * 2)
    (6 * (22 * p + 3)) C
  obtain ⟨K1, hK10, hK1⟩ := avg_order_one D p hp C
  let Kh : ℕ → ℝ := fun k => if h : 2 ≤ k ∧ k ≤ 16 * p + 16 then
    (avg_order_high' D p k hp h.1 h.2 C).choose else 0
  have hKh0 : ∀ k, 0 ≤ Kh k := by
    intro k
    simp only [Kh]
    split_ifs with h
    · exact (avg_order_high' D p k hp h.1 h.2 C).choose_spec.1
    · exact le_rfl
  set KH := ∑ k ∈ Finset.Icc 2 (14 * p + 2), Kh k with hKH
  have hKH0 : 0 ≤ KH := Finset.sum_nonneg fun k _ => hKh0 k
  set KR1 := (D : ℝ) * KE * 4 ^ (2 * p - 1) * 6 ^ (18 * p + 2) with hKR1
  set KR2 := (D : ℝ) * KE * 4 ^ (2 * p - 1) * 2 ^ (18 * p + 2) with hKR2
  have hKR10 : 0 ≤ KR1 := by positivity
  have hKR20 : 0 ≤ KR2 := by positivity
  refine ⟨K1 + KH + KR1 + KR2 * 24 ^ (3 * (22 * p + 3)) + KR2, by positivity, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hz1 hz2 Γ Υ a bQ ε₀ hΓ1 hΓ2 hηΥ hΥ ha hbQ hbad
  obtain ⟨hN, hη, hηinv, hηN, hzN, hΓ6, -, hulo, huhi⟩ := AM_setup hz1 hz2 hΓ1 hΓ2 hηΥ hΥ
  have hprob := hμ.prob
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set ϑ := a * (1 + ‖z‖) ^ 2 * Γ ^ 6 * (Υ / ((N : ℝ) * z.im)) with hϑ
  have hϑ0 : 0 ≤ ϑ := by
    have := hη.le.trans hηΥ
    have : (0 : ℝ) ≤ a := by linarith
    positivity
  have hEn0 : ∀ n, 0 ≤ ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ n ∂μ :=
    fun n => integral_nonneg fun _ => by positivity
  set Sg := ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
    ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (hEn0 _)
  have hNr0 : 0 ≤ (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by positivity
  have hNm0 : 0 ≤ (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) := by positivity
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    have e2 : ∀ M : Matrix (Idx 0 N) (Idx 0 N) ℂ, ntr M = 0 := fun M => by simp [ntr]
    have h2p : 2 * p ≠ 0 := by omega
    have hL : ∫ h, ‖ntr (B * hgUnder 0 N θ (Matrix.of h) Λ z)‖ ^ (2 * p) ∂μ = 0 := by
      simp [e2, zero_pow h2p]
    rw [hL]
    have : 0 ≤ K1 + KH + KR1 + KR2 * 24 ^ (3 * (22 * p + 3)) + KR2 := by positivity
    have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 (2 * p), ϑ ^ n *
        ∫ h, ‖ntr (B * hgUnder 0 N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ :=
      Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (integral_nonneg fun _ => by
        positivity)
    positivity
  -- the order-one and order-`k` bounds at this point
  have b1 := hK1 N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hz1 hz2 Γ Υ a bQ ε₀ hΓ1 hΓ2 hηΥ hΥ ha hbQ hbad
  have bk : ∀ k ∈ Finset.Icc 2 (14 * p + 2), ‖avgTerm D N θ μ Λ B z p k‖ ≤
      Kh k * Sg + Kh k * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
    intro k hk
    obtain ⟨hk2, hkl⟩ := Finset.mem_Icc.mp hk
    have hc : 2 ≤ k ∧ k ≤ 16 * p + 16 := ⟨hk2, by omega⟩
    have := (avg_order_high' D p k hp hc.1 hc.2 C).choose_spec.2 N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB
      z hz1 hz2 Γ Υ a bQ ε₀ hΓ1 hΓ2 hηΥ hΥ ha hbQ hbad
    simp only [Kh, dite_eq_left hc]
    exact this
  -- integrability
  have hT := AM_int_T hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN p
  have hPf : ∀ i j : Idx D N, Integrable (fun h => resPolyEval (AM_Pf D N θ Λ B z i j p) h *
      starRingEnd ℂ (h j i)) μ :=
    fun i j => AM_int_PfH hμ hθ0 hθ1 hΛ hΛn hB hη N hN1 hηinv hηN i j p
  -- `E|⟨B H̲G⟩|^{2p} = (DN)⁻¹ Σ_{i,j} E[f_{ij} h̄_{ji}] + E⟨B S_θ(G) G⟩ f'`
  have hid : ((∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p) ∂μ : ℝ) : ℂ) =
      ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∫ h, resPolyEval (AM_Pf D N θ Λ B z i j p) h *
        starRingEnd ℂ (h j i) ∂μ +
      ∫ h, ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) *
        ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
        starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p ∂μ := by
    have hsum : ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∫ h, resPolyEval (AM_Pf D N θ Λ B z i j p) h *
        starRingEnd ℂ (h j i) ∂μ = ∫ h, ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j,
          resPolyEval (AM_Pf D N θ Λ B z i j p) h * starRingEnd ℂ (h j i) ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        hPf i j]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hPf i j]
    rw [hsum, ← integral_add ((integrable_finsetSum _ fun i _ => integrable_finsetSum _
      fun j _ => hPf i j).const_mul _) hT, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    set X := ntr (B * hgUnder D N θ (Matrix.of h) Λ z) with hX
    have hXs : X = ntr (B * (Matrix.of h * res (Matrix.of h + Λ) z)) +
        ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) := by
      rw [hX]
      unfold hgUnder
      rw [Matrix.mul_add]
      simp only [ntr, Matrix.trace_add, mul_add]
    have hPfv : ∀ i j, resPolyEval (AM_Pf D N θ Λ B z i j p) h =
        (res (Matrix.of h + Λ) z * B) j i * X ^ (p - 1) * starRingEnd ℂ X ^ p :=
      fun i j => AM_eval_Pf_self θ Λ B hΛ z hη h hh i j p
    simp only [hPfv]
    have hn : ((‖X‖ ^ (2 * p) : ℝ) : ℂ) = X * (X ^ (p - 1) * starRingEnd ℂ X ^ p) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hp, ← mul_pow, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      rw [← pow_mul]
    rw [hn]
    calc X * (X ^ (p - 1) * starRingEnd ℂ X ^ p)
        = (ntr (B * (Matrix.of h * res (Matrix.of h + Λ) z)) +
          ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z))) *
            (X ^ (p - 1) * starRingEnd ℂ X ^ p) := by rw [← hXs]
      _ = _ := by
        rw [AM_ntrHG Λ B z h hh, add_mul, mul_assoc (((D : ℂ) * N)⁻¹), Finset.sum_mul]
        congr 1
        · congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        · ring
  -- the expansion in each entry, with the high-probability remainder
  set σ := ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-((6 * (22 * p + 3) : ℕ) : ℝ)) with hσ
  set W := AM_wt (AM_PX D N θ Λ B z) with hWdef
  set R := KE * (W ^ (p - 1) * W ^ p) *
    ((N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) *
      (6 * Γ) ^ (1 + (p - 1) * 2 + p * 2 + (14 * p + 2) + 1) +
      (1 + z.im⁻¹) ^ (1 + (p - 1) * 2 + p * 2 + (14 * p + 2) + 1) *
        Real.sqrt (max ε₀ 0 + σ)) with hR
  have hbadset : μ {h | ∃ q ∈ ({(Λ, z)} : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
      ∃ x ∈ avgVecs D N Λ B, ∃ y ∈ avgVecs D N Λ B,
        Γ < ‖resFactorEval (x, y, q.1, q.2) (symArr h)‖} ≤ ENNReal.ofReal (max ε₀ 0) := by
    have hsub : {h : Idx D N → Idx D N → ℂ | ∃ q ∈ ({(Λ, z)} :
        Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)), ∃ x ∈ avgVecs D N Λ B,
          ∃ y ∈ avgVecs D N Λ B, Γ < ‖resFactorEval (x, y, q.1, q.2) (symArr h)‖} ⊆
        {h | ¬ (Matrix.of h).IsHermitian} ∪ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ := by
      intro h hb
      by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Set.mem_compl_iff] at hc
      obtain ⟨hh, hΩ⟩ := hc
      obtain ⟨q, hq, x, hx, y, hy, hlt⟩ := hb
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [symArr_of_isHermitian h hh] at hlt
      exact absurd (hΩ.1 x hx y hy).1 (not_le.mpr hlt)
    calc _ ≤ μ ({h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} ∪
          (avgGood D N θ Λ B z Γ Υ bQ)ᶜ) := measure_mono hsub
      _ ≤ μ {h : Idx D N → Idx D N → ℂ | ¬ (Matrix.of h).IsHermitian} +
          μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ := measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal ε₀ := add_le_add (le_of_eq (ae_iff.mp hμ.herm)) hbad
      _ ≤ ENNReal.ofReal (max ε₀ 0) := by
          rw [zero_add]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hPok : ∀ i j : Idx D N, ∀ t ∈ AM_Pf D N θ Λ B z i j p,
      t.2.length ≤ 1 + (p - 1) * 2 + p * 2 ∧ ∀ f ∈ t.2, f.1 ∈ avgVecs D N Λ B ∧
        f.2.1 ∈ avgVecs D N Λ B ∧ ∃ q ∈ ({(Λ, z)} : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
          f.2.2 = q ∨ f.2.2 = (q.1, starRingEnd ℂ q.2) := by
    intro i j t ht
    obtain ⟨hl, hf⟩ := AM_Pf_ok D N θ Λ B z i j p t ht
    refine ⟨hl, fun f hf' => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf f hf'
    exact ⟨Finset.mem_coe.mp h1, Finset.mem_coe.mp h2, (Λ, z), Finset.mem_singleton_self _, h3⟩
  have hexp : ∀ i j : Idx D N,
      ‖(∫ h, resPolyEval (AM_Pf D N θ Λ B z i j p) h * starRingEnd ℂ (h j i) ∂μ) -
        ∑ p' ∈ Finset.range (14 * p + 2 + 1), ∑ q ∈ Finset.range (14 * p + 2 + 1 - p'),
          ccum (μ.map fun h => h j i) p' (q + 1) / ((p'.factorial * q.factorial : ℕ) : ℂ) *
            ∫ h, wirt p' q (AM_f θ Λ B z h i j p) (h j i) ∂μ‖ ≤ R := by
    intro i j
    have := hKE D N θ μ hμ {(Λ, z)} z.im hη (by
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact ⟨hΛ, le_rfl⟩) j i (avgVecs D N Λ B) (Finset.mem_coe.mp (AM_e_mem D N Λ B j))
      (Finset.mem_coe.mp (AM_e_mem D N Λ B i))
      (AM_avgVecs_norm Λ B (hΛn.trans (by norm_num)) hB) (AM_Pf D N θ Λ B z i j p) (hPok i j)
      Γ (24 * Γ)⁻¹ (max ε₀ 0) hΓ1 (by positivity) (by field_simp; rfl) (le_max_right _ _)
      hbadset
    have hconv : ∀ p' q, ∫ h, wirt p' q (fun w => resPolyEval (AM_Pf D N θ Λ B z i j p)
        (setEntry h j i w)) (h j i) ∂μ = ∫ h, wirt p' q (AM_f θ Λ B z h i j p) (h j i) ∂μ := by
      intro p' q
      refine integral_congr_ae ?_
      filter_upwards [hμ.herm] with h hh
      rw [AM_f_eq θ Λ B hΛ z hη h hh i j p]
    simp only [hconv] at this
    have hwt : ((AM_Pf D N θ Λ B z i j p).map fun t => ‖t.1‖).sum = W ^ (p - 1) * W ^ p :=
      AM_Pf_wt D N θ Λ B z i j p
    rw [hwt] at this
    exact this
  -- regrouping the expansion by the order `k`
  have hS : ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, ∑ p' ∈ Finset.range (14 * p + 2 + 1),
      ∑ q ∈ Finset.range (14 * p + 2 + 1 - p'),
        ccum (μ.map fun h => h j i) p' (q + 1) / ((p'.factorial * q.factorial : ℕ) : ℂ) *
          ∫ h, wirt p' q (AM_f θ Λ B z h i j p) (h j i) ∂μ =
      ∑ k ∈ Finset.range (14 * p + 2 + 1), avgTerm D N θ μ Λ B z p k := by
    simp only [fun i j => AM_regroup (fun p' q => ccum (μ.map fun h => h j i) p' (q + 1) /
      ((p'.factorial * q.factorial : ℕ) : ℂ) *
        ∫ h, wirt p' q (AM_f θ Λ B z h i j p) (h j i) ∂μ) (14 * p + 2)]
    have e : ∀ k, avgTerm D N θ μ Λ B z p k = ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j,
        ∑ a ∈ Finset.range (k + 1), ccum (μ.map fun h => h j i) a (k - a + 1) /
          ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
            ∫ h, wirt a (k - a) (AM_f θ Λ B z h i j p) (h j i) ∂μ := fun k => rfl
    simp only [e, ← Finset.mul_sum]
    congr 1
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  have h0 : avgTerm D N θ μ Λ B z p 0 = 0 := by simp [avgTerm, AM_ccum01 hμ]
  have hsplit3 : ∑ k ∈ Finset.range (14 * p + 2 + 1), avgTerm D N θ μ Λ B z p k =
      avgTerm D N θ μ Λ B z p 0 + avgTerm D N θ μ Λ B z p 1 +
        ∑ k ∈ Finset.Icc 2 (14 * p + 2), avgTerm D N θ μ Λ B z p k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (by omega), ← add_assoc]
    congr 1
  -- the identity with the remainder
  set Ij := fun i j => ∫ h, resPolyEval (AM_Pf D N θ Λ B z i j p) h * starRingEnd ℂ (h j i) ∂μ
    with hIj
  set Sj := fun (i j : Idx D N) => ∑ p' ∈ Finset.range (14 * p + 2 + 1),
      ∑ q ∈ Finset.range (14 * p + 2 + 1 - p'),
        ccum (μ.map fun h => h j i) p' (q + 1) / ((p'.factorial * q.factorial : ℕ) : ℂ) *
          ∫ h, wirt p' q (AM_f θ Λ B z h i j p) (h j i) ∂μ with hSj
  set T := ∫ h, ntr (B * (sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) *
        ntr (B * hgUnder D N θ (Matrix.of h) Λ z) ^ (p - 1) *
        starRingEnd ℂ (ntr (B * hgUnder D N θ (Matrix.of h) Λ z)) ^ p ∂μ with hTdef
  have hmain : ((∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p) ∂μ : ℝ) : ℂ) =
      (avgTerm D N θ μ Λ B z p 1 + T) +
        (∑ k ∈ Finset.Icc 2 (14 * p + 2), avgTerm D N θ μ Λ B z p k) +
          ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, (Ij i j - Sj i j) := by
    rw [hid]
    have e1 : ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, (Ij i j - Sj i j) =
        ((D : ℂ) * N)⁻¹ * (∑ i, ∑ j, Ij i j) - ((D : ℂ) * N)⁻¹ * ∑ i, ∑ j, Sj i j := by
      simp only [Finset.sum_sub_distrib, mul_sub]
    rw [e1, hS, hsplit3, h0]
    ring
  have hpos : 0 ≤ ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p) ∂μ :=
    integral_nonneg fun _ => by positivity
  have hnorm : ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p) ∂μ ≤
      ‖avgTerm D N θ μ Λ B z p 1 + T‖ +
        (∑ k ∈ Finset.Icc 2 (14 * p + 2), ‖avgTerm D N θ μ Λ B z p k‖) +
          ((D : ℝ) * N)⁻¹ * ∑ i, ∑ j, ‖Ij i j - Sj i j‖ := by
    have h1 := congrArg norm hmain
    rw [Complex.norm_real, Real.norm_of_nonneg hpos] at h1
    rw [h1]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add le_rfl (norm_sum_le _ _))) ?_)
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => norm_sum_le _ _)) (by positivity)
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have hDN0 : (0 : ℝ) < (D : ℝ) * N := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    positivity
  have hrem : ((D : ℝ) * N)⁻¹ * ∑ i, ∑ j, ‖Ij i j - Sj i j‖ ≤ (D : ℝ) * N * R := by
    calc ((D : ℝ) * N)⁻¹ * ∑ i, ∑ j, ‖Ij i j - Sj i j‖ ≤
          ((D : ℝ) * N)⁻¹ * ∑ _i : Idx D N, ∑ _j : Idx D N, R :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            hexp i j) (by positivity)
      _ = (D : ℝ) * N * R := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          field_simp
  -- the remainder in powers of `N`
  have hW0 : 0 ≤ W := AM_wt_nonneg _
  have hW : W ≤ 4 * N := (AM_PX_wt D N θ hθ0 hθ1 Λ B hB z).1.trans (by linarith)
  have hWp : W ^ (p - 1) * W ^ p ≤ (4 * (N : ℝ)) ^ (2 * p - 1) := by
    rw [← pow_add, show p - 1 + p = 2 * p - 1 by omega]
    exact pow_le_pow_left₀ hW0 hW _
  have hmid : 1 + (p - 1) * 2 + p * 2 + (14 * p + 2) + 1 = 4 * p - 1 + (14 * p + 2) + 1 := by
    omega
  have hσ0 : 0 ≤ σ := by positivity
  have hsq : Real.sqrt (max ε₀ 0 + σ) ≤ Real.sqrt ε₀ + Real.sqrt σ := by
    refine (AM_sqrt_add _ _ hσ0).trans (le_of_eq ?_)
    congr 1
    rcases le_or_gt 0 ε₀ with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, Real.sqrt_zero, Real.sqrt_eq_zero'.mpr h.le]
  have hη2 : 1 + z.im⁻¹ ≤ 2 * N := by linarith
  have hX2 := AM_rem1 hN p hp Γ hΓ1 hΓ6
  have hσb := AM_sigma hN Γ hΓ1 hΓ6 (22 * p + 3)
  have hNr : (N : ℝ) ^ (20 * p + 2) ≤ (N : ℝ) ^ (21 * (p : ℝ) + 18) :=
    AM_npow_le hN (by push_cast; linarith)
  have hNm : (N : ℝ) ^ (20 * p + 2) * ((N : ℝ) ^ (22 * p + 3))⁻¹ =
      (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) := by
    rw [show -(2 * (p : ℝ) + 1) = -((2 * p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hN0.le, Real.rpow_natCast,
      show 22 * p + 3 = (20 * p + 2) + (2 * p + 1) by ring, pow_add]
    field_simp
    ring
  have hX3 : (N : ℝ) * (4 * N) ^ (2 * p - 1) * ((1 + z.im⁻¹) ^ (18 * p + 2) *
      (Real.sqrt ε₀ + Real.sqrt σ)) ≤ 4 ^ (2 * p - 1) * 2 ^ (18 * p + 2) *
        ((N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ +
          24 ^ (3 * (22 * p + 3)) * (N : ℝ) ^ (-(2 * (p : ℝ) + 1))) := by
    have e : (N : ℝ) * (4 * N) ^ (2 * p - 1) * (2 * N) ^ (18 * p + 2) =
        4 ^ (2 * p - 1) * 2 ^ (18 * p + 2) * (N : ℝ) ^ (20 * p + 2) := by
      rw [mul_pow, mul_pow, show (N : ℝ) ^ (20 * p + 2) = N * N ^ (2 * p - 1) * N ^ (18 * p + 2) by
        rw [← pow_succ', ← pow_add]; congr 1; omega]
      ring
    have hs0 : 0 ≤ Real.sqrt ε₀ + Real.sqrt σ := by positivity
    calc (N : ℝ) * (4 * N) ^ (2 * p - 1) * ((1 + z.im⁻¹) ^ (18 * p + 2) *
          (Real.sqrt ε₀ + Real.sqrt σ))
        ≤ (N : ℝ) * (4 * N) ^ (2 * p - 1) * ((2 * N) ^ (18 * p + 2) *
          (Real.sqrt ε₀ + Real.sqrt σ)) := by gcongr
      _ = 4 ^ (2 * p - 1) * 2 ^ (18 * p + 2) * ((N : ℝ) ^ (20 * p + 2) * Real.sqrt ε₀ +
          (N : ℝ) ^ (20 * p + 2) * Real.sqrt σ) := by rw [← mul_assoc, e]; ring
      _ ≤ 4 ^ (2 * p - 1) * 2 ^ (18 * p + 2) * ((N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ +
          (N : ℝ) ^ (20 * p + 2) * (24 ^ (3 * (22 * p + 3)) * ((N : ℝ) ^ (22 * p + 3))⁻¹)) := by
          gcongr
      _ = _ := by rw [← hNm]; ring
  have hDNR : (D : ℝ) * N * R ≤ KR1 * (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) +
      KR2 * ((N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ +
        24 ^ (3 * (22 * p + 3)) * (N : ℝ) ^ (-(2 * (p : ℝ) + 1))) := by
    rw [hR, hmid, show 4 * p - 1 + (14 * p + 2) + 1 = 18 * p + 2 by omega]
    rw [show 4 * p - 1 + (14 * p + 2) + 1 = 18 * p + 2 by omega] at hX2
    have hA : 0 ≤ (N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) * (6 * Γ) ^ (18 * p + 2) := by
      have : 0 ≤ Γ := by linarith
      positivity
    have hB' : 0 ≤ (1 + z.im⁻¹) ^ (18 * p + 2) * Real.sqrt (max ε₀ 0 + σ) := by
      have := hη.le
      positivity
    calc (D : ℝ) * N * (KE * (W ^ (p - 1) * W ^ p) *
          ((N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) * (6 * Γ) ^ (18 * p + 2) +
            (1 + z.im⁻¹) ^ (18 * p + 2) * Real.sqrt (max ε₀ 0 + σ)))
        ≤ (D : ℝ) * N * (KE * (4 * (N : ℝ)) ^ (2 * p - 1) *
          ((N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) * (6 * Γ) ^ (18 * p + 2) +
            (1 + z.im⁻¹) ^ (18 * p + 2) * (Real.sqrt ε₀ + Real.sqrt σ))) := by
          gcongr
      _ = (D : ℝ) * KE * ((N : ℝ) * (4 * N) ^ (2 * p - 1) *
            ((N : ℝ) ^ (-(((14 * p + 2 : ℕ) : ℝ) + 2) / 2) * (6 * Γ) ^ (18 * p + 2))) +
          (D : ℝ) * KE * ((N : ℝ) * (4 * N) ^ (2 * p - 1) * ((1 + z.im⁻¹) ^ (18 * p + 2) *
            (Real.sqrt ε₀ + Real.sqrt σ))) := by ring
      _ ≤ (D : ℝ) * KE * (4 ^ (2 * p - 1) * 6 ^ (18 * p + 2) *
            (N : ℝ) ^ (-(2 * (p : ℝ) + 1))) +
          (D : ℝ) * KE * (4 ^ (2 * p - 1) * 2 ^ (18 * p + 2) *
            ((N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ +
              24 ^ (3 * (22 * p + 3)) * (N : ℝ) ^ (-(2 * (p : ℝ) + 1)))) :=
          add_le_add (mul_le_mul_of_nonneg_left hX2 (by positivity))
            (mul_le_mul_of_nonneg_left hX3 (by positivity))
      _ = _ := by rw [hKR1, hKR2]; ring
  -- the final combination
  rw [← hϑ] at b1
  have h12 : ϑ * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ +
      ϑ ^ 2 * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ ≤ Sg := by
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 (2 * p) := by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n => ϑ ^ n *
      ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - n) ∂μ)
      (fun n _ _ => mul_nonneg (by positivity) (hEn0 _))
    rw [Finset.sum_pair (by norm_num)] at this
    simpa using this
  have hsumk : ∑ k ∈ Finset.Icc 2 (14 * p + 2), ‖avgTerm D N θ μ Λ B z p k‖ ≤
      KH * Sg + KH * ((N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
    refine (Finset.sum_le_sum bk).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hKH]
    ring
  have hK1m := mul_le_mul_of_nonneg_left h12 hK10
  set c24 : ℝ := 24 ^ (3 * (22 * p + 3)) with hc24
  have hc240 : 0 ≤ c24 := by positivity
  set Nm := (N : ℝ) ^ (-(2 * (p : ℝ) + 1)) with hNmdef
  set Nr := (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ with hNrdef
  have p1 := mul_nonneg hKR10 hSg0
  have p2 := mul_nonneg (mul_nonneg hKR20 hc240) hSg0
  have p3 := mul_nonneg hKR20 hSg0
  have p4 := mul_nonneg hK10 hNm0
  have p5 := mul_nonneg hKH0 hNm0
  have p6 := mul_nonneg hKR20 hNm0
  have p7 := mul_nonneg hKR10 hNr0
  have p8 := mul_nonneg (mul_nonneg hKR20 hc240) hNr0
  have p9 := mul_nonneg hKR10 hNm0
  have hexpand : (K1 + KH + KR1 + KR2 * c24 + KR2) * Sg +
      (K1 + KH + KR1 + KR2 * c24 + KR2) * (Nm + Nr) =
      (K1 * Sg + KH * Sg + K1 * Nr + KH * Nr + KR1 * Nm + KR2 * Nr + KR2 * (c24 * Nm)) +
      (KR1 * Sg + KR2 * c24 * Sg + KR2 * Sg + K1 * Nm + KH * Nm + KR2 * Nm + KR1 * Nr +
        KR2 * c24 * Nr) := by ring
  rw [hexpand]
  have hb1 : ‖avgTerm D N θ μ Λ B z p 1 + T‖ ≤ K1 * Sg + K1 * Nr := by
    refine b1.trans ?_
    have e : K1 * ϑ * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ +
        K1 * ϑ ^ 2 * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ =
        K1 * (ϑ * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 1) ∂μ +
        ϑ ^ 2 * ∫ h, ‖ntr (B * hgUnder D N θ (Matrix.of h) Λ z)‖ ^ (2 * p - 2) ∂μ) := by ring
    have e2 : K1 * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ = K1 * Nr := by
      rw [hNrdef]; ring
    rw [e2, e]
    linarith
  have hr : ((D : ℝ) * N)⁻¹ * ∑ i, ∑ j, ‖Ij i j - Sj i j‖ ≤
      KR1 * Nm + KR2 * Nr + KR2 * (c24 * Nm) := by
    refine hrem.trans (hDNR.trans (le_of_eq ?_))
    ring
  linarith [hnorm, hb1, hsumk, hr]

end RBMTransitionEdge

end
