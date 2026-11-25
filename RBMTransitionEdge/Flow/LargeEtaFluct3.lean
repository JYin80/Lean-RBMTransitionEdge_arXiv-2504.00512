module

public import RBMTransitionEdge.Flow.LargeEtaFluct

@[expose] public section

/-!
# The fluctuation term of the three-resolvent identity at large `η`

The term `⟨\underline{G₁E_{a₁}G₂E_{a₂}M₃HG₃}E_{a₃}⟩` of the three-resolvent analogue of (3.39)
[eq:aftertrace] is `≺ N⁻¹η⁻³` in the setting of Lemma 3.6 [lemma_G_large], uniformly in
`θ ∈ [0, 1]` and the class.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Wirtinger calculus for smooth functions of one complex variable -/

/-- Smooth (real sense, every finite order) functions `ℂ → ℂ`, such as the slices
`w ↦ F(setEntry h i j w)` of Lemma 2.11 [lem:complex_cumu]. -/
private def L3_Sm (f : ℂ → ℂ) : Prop := ∀ n : ℕ, ContDiff ℝ n f

/-- A smooth function is real-differentiable. -/
private lemma L3_Sm.diff {f : ℂ → ℂ} (hf : L3_Sm f) : Differentiable ℝ f :=
  (hf 1).differentiable (by norm_num)

/-- `z ↦ f'(z) v` is smooth for smooth `f`. -/
private lemma L3_sm_fderiv_apply {f : ℂ → ℂ} (hf : L3_Sm f) (v : ℂ) :
    L3_Sm (fun z => fderiv ℝ f z v) := fun n =>
  ((hf (n + 1)).fderiv_right (by norm_cast)).clm_apply contDiff_const

/-- Constants are smooth. -/
private lemma L3_sm_const (c : ℂ) : L3_Sm (fun _ => c) := fun _ => contDiff_const

/-- Products of smooth functions are smooth. -/
private lemma L3_sm_mul {f g : ℂ → ℂ} (hf : L3_Sm f) (hg : L3_Sm g) :
    L3_Sm (fun z => f z * g z) := fun n => (hf n).mul (hg n)

/-- Constant multiples of smooth functions are smooth. -/
private lemma L3_sm_cmul (c : ℂ) {f : ℂ → ℂ} (hf : L3_Sm f) : L3_Sm (fun z => c * f z) :=
  L3_sm_mul (L3_sm_const c) hf

/-- Powers of smooth functions are smooth. -/
private lemma L3_sm_pow {f : ℂ → ℂ} (hf : L3_Sm f) (m : ℕ) : L3_Sm (fun z => f z ^ m) :=
  fun n => (hf n).pow m

/-- The complex conjugate of a smooth function is smooth. -/
private lemma L3_sm_conj {f : ℂ → ℂ} (hf : L3_Sm f) : L3_Sm (fun z => starRingEnd ℂ (f z)) :=
  fun n => Complex.conjCLE.contDiff.comp (hf n)

/-- `∂_w f` is smooth for smooth `f`. -/
private lemma L3_sm_dW {f : ℂ → ℂ} (hf : L3_Sm f) : L3_Sm (dW f) := fun n => by
  unfold dW
  exact ((L3_sm_fderiv_apply hf 1 n).sub
    (contDiff_const.mul (L3_sm_fderiv_apply hf Complex.I n))).div_const 2

/-- `∂_{w̄} f` is smooth for smooth `f`. -/
private lemma L3_sm_dWbar {f : ℂ → ℂ} (hf : L3_Sm f) : L3_Sm (dWbar f) := fun n => by
  unfold dWbar
  exact ((L3_sm_fderiv_apply hf 1 n).add
    (contDiff_const.mul (L3_sm_fderiv_apply hf Complex.I n))).div_const 2

/-- The operators `∂_w`, `∂_{w̄}` act on smooth functions as derivations. -/
private structure L3_Der (d : (ℂ → ℂ) → ℂ → ℂ) : Prop where
  sm : ∀ f, L3_Sm f → L3_Sm (d f)
  mul : ∀ f g, L3_Sm f → L3_Sm g → d (fun x => f x * g x) = fun x => d f x * g x + f x * d g x
  sum : ∀ (s : Finset ℕ) (F : ℕ → ℂ → ℂ), (∀ m, L3_Sm (F m)) →
    d (fun x => ∑ m ∈ s, F m x) = fun x => ∑ m ∈ s, d (F m) x
  cmul : ∀ (c : ℂ) f, L3_Sm f → d (fun x => c * f x) = fun x => c * d f x
  add : ∀ f g, L3_Sm f → L3_Sm g → d (fun x => f x + g x) = fun x => d f x + d g x
  const : ∀ c : ℂ, d (fun _ => c) = fun _ => 0

/-- `∂_w` is a derivation on smooth functions. -/
private lemma L3_der_dW : L3_Der dW where
  sm := fun _ hf => L3_sm_dW hf
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
private lemma L3_der_dWbar : L3_Der dWbar where
  sm := fun _ hf => L3_sm_dWbar hf
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
private lemma L3_der_iter_sm {d : (ℂ → ℂ) → ℂ → ℂ} (hd : L3_Der d) (n : ℕ) {f : ℂ → ℂ}
    (hf : L3_Sm f) : L3_Sm (d^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact hd.sm _ ih

/-- Iterates of a derivation on a constant. -/
private lemma L3_der_iter_const {d : (ℂ → ℂ) → ℂ → ℂ} (hd : L3_Der d) (n : ℕ) (c : ℂ) :
    d^[n] (fun _ => c) = fun _ => if n = 0 then c else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [Nat.add_one_ne_zero, ite_false]
    exact hd.const _

/-- Iterates of a derivation are linear on finite sums of smooth functions. -/
private lemma L3_der_iter_lin {d : (ℂ → ℂ) → ℂ → ℂ} (hd : L3_Der d) (n : ℕ) (s : Finset ℕ)
    (c : ℕ → ℂ) (F : ℕ → ℂ → ℂ) (hF : ∀ m, L3_Sm (F m)) :
    d^[n] (fun x => ∑ m ∈ s, c m * F m x) = fun x => ∑ m ∈ s, c m * d^[n] (F m) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hd.sum s _ fun m => L3_sm_cmul _ (L3_der_iter_sm hd n (hF m))]
    funext x
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hd.cmul _ _ (L3_der_iter_sm hd n (hF m)), Function.iterate_succ_apply']

/-- Iterates of a derivation are additive on smooth functions. -/
private lemma L3_der_iter_add {d : (ℂ → ℂ) → ℂ → ℂ} (hd : L3_Der d) (n : ℕ) {f g : ℂ → ℂ}
    (hf : L3_Sm f) (hg : L3_Sm g) :
    d^[n] (fun x => f x + g x) = fun x => d^[n] f x + d^[n] g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hd.add _ _ (L3_der_iter_sm hd n hf) (L3_der_iter_sm hd n hg),
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- Iterates of a derivation commute with constant factors. -/
private lemma L3_der_iter_cmul {d : (ℂ → ℂ) → ℂ → ℂ} (hd : L3_Der d) (n : ℕ) (c : ℂ)
    {f : ℂ → ℂ} (hf : L3_Sm f) :
    d^[n] (fun x => c * f x) = fun x => c * d^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hd.cmul _ _ (L3_der_iter_sm hd n hf),
      Function.iterate_succ_apply']

/-- The Leibniz rule for iterates of a derivation on smooth functions. -/
private lemma L3_leib {d : (ℂ → ℂ) → ℂ → ℂ} (hd : L3_Der d) {f g : ℂ → ℂ} (hf : L3_Sm f)
    (hg : L3_Sm g) (n : ℕ) :
    d^[n] (fun x => f x * g x) = fun x => ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℂ) * (d^[m] f x * d^[n - m] g x) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hs : ∀ m, L3_Sm (fun x => d^[m] f x * d^[n - m] g x) := fun m =>
      L3_sm_mul (L3_der_iter_sm hd m hf) (L3_der_iter_sm hd (n - m) hg)
    rw [hd.sum _ _ fun m => L3_sm_cmul _ (hs m)]
    funext x
    rw [Finset.sum_choose_succ_mul (fun i j => d^[i] f x * d^[j] g x) n]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [hd.cmul _ _ (hs m), hd.mul _ _ (L3_der_iter_sm hd m hf) (L3_der_iter_sm hd (n - m) hg)]
    rw [← Function.iterate_succ_apply' d m f, ← Function.iterate_succ_apply' d (n - m) g]
    rw [show n + 1 - m = (n - m).succ by omega]
    ring

/-- The Leibniz rule for the mixed derivatives `∂_w^a ∂_{w̄}^b` of a product of smooth
functions. -/
private lemma L3_wirt_mul {f g : ℂ → ℂ} (hf : L3_Sm f) (hg : L3_Sm g) (a b : ℕ) (x : ℂ) :
    wirt a b (fun y => f y * g y) x = ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
      (a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f x * wirt (a - a') (b - b') g x) := by
  unfold wirt
  rw [L3_leib L3_der_dWbar hf hg b]
  have hs : ∀ m, L3_Sm (fun x => dWbar^[m] f x * dWbar^[b - m] g x) := fun m =>
    L3_sm_mul (L3_der_iter_sm L3_der_dWbar m hf) (L3_der_iter_sm L3_der_dWbar (b - m) hg)
  rw [L3_der_iter_lin L3_der_dW a _ _ _ hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [L3_leib L3_der_dW (L3_der_iter_sm L3_der_dWbar b' hf)
    (L3_der_iter_sm L3_der_dWbar (b - b') hg) a]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  ring

/-- The mixed derivatives of a constant. -/
private lemma L3_wirt_const (c : ℂ) (a b : ℕ) :
    wirt a b (fun _ => c) = fun _ => if a = 0 ∧ b = 0 then c else 0 := by
  unfold wirt
  rw [L3_der_iter_const L3_der_dWbar b c]
  by_cases hb : b = 0
  · simp only [hb, ite_true]
    rw [L3_der_iter_const L3_der_dW a c]
    simp
  · simp only [hb, ite_false, and_false]
    rw [L3_der_iter_const L3_der_dW a 0]
    simp

/-- Linearity of the mixed derivatives. -/
private lemma L3_wirt_lin {f g : ℂ → ℂ} (hf : L3_Sm f) (hg : L3_Sm g) (c₁ c₂ : ℂ) (a b : ℕ) :
    wirt a b (fun x => c₁ * f x + c₂ * g x) = fun x => c₁ * wirt a b f x + c₂ * wirt a b g x := by
  unfold wirt
  rw [L3_der_iter_add L3_der_dWbar b (L3_sm_cmul c₁ hf) (L3_sm_cmul c₂ hg),
    L3_der_iter_cmul L3_der_dWbar b c₁ hf, L3_der_iter_cmul L3_der_dWbar b c₂ hg,
    L3_der_iter_add L3_der_dW a (L3_sm_cmul c₁ (L3_der_iter_sm L3_der_dWbar b hf))
      (L3_sm_cmul c₂ (L3_der_iter_sm L3_der_dWbar b hg)),
    L3_der_iter_cmul L3_der_dW a c₁ (L3_der_iter_sm L3_der_dWbar b hf),
    L3_der_iter_cmul L3_der_dW a c₂ (L3_der_iter_sm L3_der_dWbar b hg)]

/-- `∂_{w̄} ∂_w f = ∂_w ∂_{w̄} f` for smooth `f` (symmetry of the second derivative). -/
private lemma L3_dWbar_dW {f : ℂ → ℂ} (hf : L3_Sm f) : dWbar (dW f) = dW (dWbar f) := by
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
private lemma L3_iter_comm {f : ℂ → ℂ} (hf : L3_Sm f) (a b : ℕ) :
    dWbar^[a] (dW^[b] f) = dW^[b] (dWbar^[a] f) := by
  have one : ∀ (b : ℕ) (g : ℂ → ℂ), L3_Sm g → dWbar (dW^[b] g) = dW^[b] (dWbar g) := by
    intro b
    induction b with
    | zero => intro g _; rfl
    | succ b ih =>
      intro g hg
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        L3_dWbar_dW (L3_der_iter_sm L3_der_dW b hg), ih g hg]
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, one b _ (L3_der_iter_sm L3_der_dWbar a hf),
      Function.iterate_succ_apply']

/-- The mixed derivatives of a complex conjugate: `∂_w^a ∂_{w̄}^b f̄ = conj(∂_w^b ∂_{w̄}^a f)`. -/
private lemma L3_wirt_conj {f : ℂ → ℂ} (hf : L3_Sm f) (a b : ℕ) :
    wirt a b (fun x => starRingEnd ℂ (f x)) = fun x => starRingEnd ℂ (wirt b a f x) := by
  have hb : ∀ (n : ℕ) (g : ℂ → ℂ), L3_Sm g →
      dWbar^[n] (fun x => starRingEnd ℂ (g x)) = fun x => starRingEnd ℂ (dW^[n] g x) := by
    intro n
    induction n with
    | zero => intro g _; rfl
    | succ n ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
      exact funext fun x => (dW_conj ((L3_der_iter_sm L3_der_dW n hg).diff x)).2
  have ha : ∀ (n : ℕ) (g : ℂ → ℂ), L3_Sm g →
      dW^[n] (fun x => starRingEnd ℂ (g x)) = fun x => starRingEnd ℂ (dWbar^[n] g x) := by
    intro n
    induction n with
    | zero => intro g _; rfl
    | succ n ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
      exact funext fun x => (dW_conj ((L3_der_iter_sm L3_der_dWbar n hg).diff x)).1
  unfold wirt
  rw [hb b f hf, ha a _ (L3_der_iter_sm L3_der_dW b hf), L3_iter_comm hf a b]

/-! ### Bounds on the mixed derivatives of products -/

/-- The Leibniz bound: if `|∂^{(a,b)} f| ≤ Γ^{a+b} α^{a+b} c_f` and `|∂^{(a,b)} g| ≤ Γ^{a+b} β^{a+b}
c_g` at `w` for `a + b ≤ k`, then `|∂^{(a,b)} (f g)| ≤ Γ^{a+b} (α + β)^{a+b} c_f c_g`. -/
private lemma L3_LB {f g : ℂ → ℂ} (hf : L3_Sm f) (hg : L3_Sm g) (w : ℂ) (Γ α β cf cg : ℝ)
    (k : ℕ) (hΓ : 0 ≤ Γ) (hα : 0 ≤ α) (hcf : 0 ≤ cf)
    (hF : ∀ a b, a + b ≤ k → ‖wirt a b f w‖ ≤ Γ ^ (a + b) * α ^ (a + b) * cf)
    (hG : ∀ a b, a + b ≤ k → ‖wirt a b g w‖ ≤ Γ ^ (a + b) * β ^ (a + b) * cg) :
    ∀ a b, a + b ≤ k →
      ‖wirt a b (fun y => f y * g y) w‖ ≤ Γ ^ (a + b) * (α + β) ^ (a + b) * (cf * cg) := by
  intro a b hab
  rw [L3_wirt_mul hf hg a b w]
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
private lemma L3_pow_jet {u : ℂ → ℂ} (hu : L3_Sm u) (w : ℂ) (Γ c : ℝ) (k : ℕ) (hΓ : 0 ≤ Γ)
    (hc : 0 ≤ c) (hU : ∀ a b, a + b ≤ k → ‖wirt a b u w‖ ≤ Γ ^ (a + b) * c) (m : ℕ) :
    ∀ a b, a + b ≤ k →
      ‖wirt a b (fun y => u y ^ m) w‖ ≤ Γ ^ (a + b) * (m : ℝ) ^ (a + b) * c ^ m := by
  induction m with
  | zero =>
    intro a b _
    simp only [pow_zero, L3_wirt_const]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have : a + b ≠ 0 := by omega
      simp [zero_pow this]
  | succ m ih =>
    intro a b hab
    have e : (fun y => u y ^ (m + 1)) = fun y => u y ^ m * u y := funext fun y => pow_succ _ _
    rw [e]
    have := L3_LB (L3_sm_pow hu m) hu w Γ m 1 (c ^ m) c k hΓ (Nat.cast_nonneg m)
      (pow_nonneg hc m) ih (fun a b hab => by rw [one_pow, mul_one]; exact hU a b hab) a b hab
    rw [pow_succ]
    push_cast
    exact this

/-- The first derivatives of a power: `|∂ u^m| ≤ m β x^{m-1}` when `|u| ≤ x` and `|∂ u| ≤ β`. -/
private lemma L3_pow_d1 {u : ℂ → ℂ} (hu : L3_Sm u) (w : ℂ) (x β : ℝ) (hx : ‖u w‖ ≤ x)
    (hβ1 : ‖dW u w‖ ≤ β) (hβ2 : ‖dWbar u w‖ ≤ β) (m : ℕ) :
    ‖dW (fun y => u y ^ m) w‖ ≤ m * β * x ^ (m - 1) ∧
      ‖dWbar (fun y => u y ^ m) w‖ ≤ m * β * x ^ (m - 1) := by
  have hx0 : 0 ≤ x := (norm_nonneg _).trans hx
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ1
  induction m with
  | zero =>
    simp only [pow_zero]
    rw [L3_der_dW.const, L3_der_dWbar.const]
    simp
  | succ m ih =>
    have e : (fun y => u y ^ (m + 1)) = fun y => u y ^ m * u y := funext fun y => pow_succ _ _
    rw [e, L3_der_dW.mul _ _ (L3_sm_pow hu m) hu, L3_der_dWbar.mul _ _ (L3_sm_pow hu m) hu]
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

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma L3_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
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
private lemma L3_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

/-! ### Norms of the vectors and crude bounds on the forms -/

/-- `|x^* A y| ≤ ‖A‖` for vectors `x`, `y` of norm `≤ 1`. -/
private lemma L3_form_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
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
private lemma L3_mulVec_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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
private lemma L3_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) : opNorm Tᴴ = opNorm T := by
  change ‖Tᴴ‖ = ‖T‖
  exact Matrix.l2_opNorm_conjTranspose T

/-- A standard basis vector has norm `1`. -/
private lemma L3_single_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    ∑ r, ‖(Pi.single k (1 : ℂ) : ι → ℂ) r‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp

private lemma L3_ne_bot : (Finset.univ : Finset (Fin 1)) ≠ ⊥ := by simp

/-- The only set partition of `Fin 1` is the one with a single block. -/
private lemma L3_part_one (π : Finpartition (Finset.univ : Finset (Fin 1))) :
    π = Finpartition.indiscrete L3_ne_bot := by
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
private lemma L3_ccum01 {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h i j) 0 1 = 0 := by
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  unfold ccum jointCum
  rw [Finset.sum_eq_single (Finpartition.indiscrete L3_ne_bot)
    (fun π _ hπ => absurd (L3_part_one π) hπ) (by simp)]
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
private lemma L3_regroup (F : ℕ → ℕ → ℂ) (l : ℕ) :
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

/-! ### Wirtinger derivatives of slices of jointly smooth functions -/

/-- The derivative `∂_w` of the slice `w ↦ Ψ(p₁, w)`, as a function of `(p₁, w)`. -/
private def L3_pdW {E : Type*} (Ψ : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun p => dW (fun w => Ψ (p.1, w)) p.2

/-- The derivative `∂_{w̄}` of the slice `w ↦ Ψ(p₁, w)`, as a function of `(p₁, w)`. -/
private def L3_pdWb {E : Type*} (Ψ : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun p => dWbar (fun w => Ψ (p.1, w)) p.2

/-- The partial derivative of a jointly smooth function in the direction `v` of the last
variable is jointly smooth. -/
private lemma L3_fderiv_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (v : ℂ) (n : ℕ) :
    ContDiff ℝ n (fun p : E × ℂ => fderiv ℝ (fun w => Ψ (p.1, w)) p.2 v) := by
  have h1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry fun (p : E × ℂ) (w : ℂ) => Ψ (p.1, w)) :=
    (hΨ (n + 1)).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have h2 := ContDiff.fderiv h1 (contDiff_snd (𝕜 := ℝ) (E := E) (F := ℂ) (n := (n : WithTop ℕ∞)))
    (by push_cast; exact le_rfl)
  exact h2.clm_apply contDiff_const

/-- `∂_w` and `∂_{w̄}` of the slices of a jointly smooth function are jointly smooth. -/
private lemma L3_pd_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) :
    (∀ n : ℕ, ContDiff ℝ n (L3_pdW Ψ)) ∧ (∀ n : ℕ, ContDiff ℝ n (L3_pdWb Ψ)) := by
  constructor
  · intro n
    unfold L3_pdW dW
    exact ((L3_fderiv_param hΨ 1 n).sub
      (contDiff_const.mul (L3_fderiv_param hΨ Complex.I n))).div_const 2
  · intro n
    unfold L3_pdWb dWbar
    exact ((L3_fderiv_param hΨ 1 n).add
      (contDiff_const.mul (L3_fderiv_param hΨ Complex.I n))).div_const 2

/-- The iterated parametric derivatives of a jointly smooth function are jointly smooth. -/
private lemma L3_iter_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (a b : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (L3_pdW^[a] (L3_pdWb^[b] Ψ)) := by
  have hb : ∀ b : ℕ, ∀ n : ℕ, ContDiff ℝ n (L3_pdWb^[b] Ψ) := by
    intro b
    induction b with
    | zero => exact hΨ
    | succ b ih => rw [Function.iterate_succ_apply']; exact (L3_pd_smooth ih).2
  induction a with
  | zero => exact hb b
  | succ a ih => rw [Function.iterate_succ_apply']; exact (L3_pd_smooth ih).1

/-- The mixed Wirtinger derivatives of a slice are the slices of the iterated parametric
derivatives. -/
private lemma L3_wirt_param {E : Type*} (Ψ : E × ℂ → ℂ) (x : E) (a b : ℕ) :
    wirt a b (fun w => Ψ (x, w)) = fun w => (L3_pdW^[a] (L3_pdWb^[b] Ψ)) (x, w) := by
  have hb : ∀ (n : ℕ) (Φ : E × ℂ → ℂ),
      dWbar^[n] (fun w => Φ (x, w)) = fun w => (L3_pdWb^[n] Φ) (x, w) := by
    intro n
    induction n with
    | zero => intro Φ; rfl
    | succ n ih =>
      intro Φ
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  have ha : ∀ (n : ℕ) (Φ : E × ℂ → ℂ),
      dW^[n] (fun w => Φ (x, w)) = fun w => (L3_pdW^[n] Φ) (x, w) := by
    intro n
    induction n with
    | zero => intro Φ; rfl
    | succ n ih =>
      intro Φ
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  unfold wirt
  rw [hb, ha]

/-- The mixed Wirtinger derivatives of the slices of a jointly smooth function are jointly
continuous. -/
private lemma L3_wirt_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (a b : ℕ) :
    Continuous (fun p : E × ℂ => wirt a b (fun w => Ψ (p.1, w)) p.2) := by
  have e : (fun p : E × ℂ => wirt a b (fun w => Ψ (p.1, w)) p.2) =
      L3_pdW^[a] (L3_pdWb^[b] Ψ) := by
    funext p
    rw [L3_wirt_param]
  rw [e]
  exact (L3_iter_smooth hΨ a b 0).continuous

/-- The substitution `(h, w) ↦ setEntry h i j w` is jointly smooth. -/
private lemma L3_contDiff_setEntry {D N : ℕ} (i j : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hre : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => ((p.2.re : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff).comp contDiff_snd
  have hw : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => p.2) := contDiff_snd
  have hcw : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => starRingEnd ℂ p.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  have hh : ContDiff ℝ n (fun p : (Idx D N → Idx D N → ℂ) × ℂ => p.1 k l) :=
    (contDiff_apply_apply ℝ k l).comp contDiff_fst
  simp only [setEntry]
  split_ifs
  all_goals first | exact hre | exact hw | exact hcw | exact hh

/-- For a Hermitian array, `F` and `F ∘ symArr` agree along every one-entry slice. -/
private lemma L3_slice_sym {D N : ℕ} (F : (Idx D N → Idx D N → ℂ) → ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    F (setEntry h i j w) = F (symArr (setEntry h i j w)) := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- The slices of `F` through Hermitian arrays are smooth when `F ∘ symArr` is smooth. -/
private lemma L3_sm_slice {D N : ℕ} {F : (Idx D N → Idx D N → ℂ) → ℂ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (fun h => F (symArr h))) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    L3_Sm (fun w => F (setEntry h i j w)) := fun n => by
  have e : (fun w => F (setEntry h i j w)) =
      (fun h' => F (symArr h')) ∘ (fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2) ∘
        (fun w : ℂ => (h, w)) := by
    funext w
    simp only [Function.comp]
    exact L3_slice_sym F h hh i j w
  rw [e]
  exact (hF n).comp ((L3_contDiff_setEntry i j n).comp (contDiff_prodMk_right h))

/-- The integrands `h ↦ ∂_w^a ∂_{w̄}^b F(setEntry h i j w)|_{w = h_{ij}}` of Lemma 2.11
[lem:complex_cumu] are almost everywhere strongly measurable for an almost surely Hermitian
law, when `F ∘ symArr` is smooth. -/
private lemma L3_wirt_aesm {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) {F : (Idx D N → Idx D N → ℂ) → ℂ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (fun h => F (symArr h))) (i j : Idx D N) (a b : ℕ) :
    AEStronglyMeasurable (fun h => wirt a b (fun w => F (setEntry h i j w)) (h i j)) μ := by
  let Ψ : (Idx D N → Idx D N → ℂ) × ℂ → ℂ := fun p => F (symArr (setEntry p.1 i j p.2))
  have hΨs : ∀ n : ℕ, ContDiff ℝ n Ψ := fun n =>
    (hF n).comp (L3_contDiff_setEntry i j n)
  have hc := L3_wirt_cont hΨs a b
  have hpair : Continuous (fun h : Idx D N → Idx D N → ℂ => (h, h i j)) :=
    continuous_id.prodMk ((continuous_apply j).comp (continuous_apply i))
  have hcont := hc.comp hpair
  refine hcont.aestronglyMeasurable.congr ?_
  filter_upwards [hμh] with h hh
  have e : (fun w => Ψ (h, w)) = fun w => F (setEntry h i j w) := by
    funext w
    exact (L3_slice_sym F h hh i j w).symm
  change wirt a b (fun w => Ψ (h, w)) (h i j) = _
  rw [e]

/-! ### Entrywise Wirtinger derivatives of matrix-valued slices -/

/-- The entrywise derivative `(∂_x + s ∂_y)/2` of a matrix-valued function of `w = x + iy`;
`s = -i` gives `∂_w` and `s = i` gives `∂_{w̄}`. -/
private def L3_dm {ι : Type*} (s : ℂ) (M : ℂ → Matrix ι ι ℂ) (w : ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun k l => (fderiv ℝ (fun w => M w k l) w 1 +
    s * fderiv ℝ (fun w => M w k l) w Complex.I) / 2

/-- Matrix-valued functions with smooth entries. -/
private def L3_Dm {ι : Type*} (M : ℂ → Matrix ι ι ℂ) : Prop := ∀ k l, L3_Sm (fun w => M w k l)

/-- `s = -i` is the entrywise `∂_w`. -/
private lemma L3_dm_dW {ι : Type*} (M : ℂ → Matrix ι ι ℂ) (w : ℂ) (k l : ι) :
    L3_dm (-Complex.I) M w k l = dW (fun w => M w k l) w := by
  simp only [L3_dm, dW, Matrix.of_apply]
  ring

/-- `s = i` is the entrywise `∂_{w̄}`. -/
private lemma L3_dm_dWbar {ι : Type*} (M : ℂ → Matrix ι ι ℂ) (w : ℂ) (k l : ι) :
    L3_dm Complex.I M w k l = dWbar (fun w => M w k l) w := by
  simp only [L3_dm, dWbar, Matrix.of_apply]

/-- Constant matrix-valued functions have smooth entries. -/
private lemma L3_Dm.const {ι : Type*} (C : Matrix ι ι ℂ) : L3_Dm (fun _ : ℂ => C) :=
  fun _ _ => L3_sm_const _

/-- Products of matrix-valued functions with smooth entries have smooth entries. -/
private lemma L3_Dm.mul {ι : Type*} [Fintype ι] {M₁ M₂ : ℂ → Matrix ι ι ℂ} (h₁ : L3_Dm M₁)
    (h₂ : L3_Dm M₂) : L3_Dm (fun w => M₁ w * M₂ w) := fun k l n => by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun m _ => (h₁ k m n).mul (h₂ m l n)

/-- Sums of matrix-valued functions with smooth entries have smooth entries. -/
private lemma L3_Dm.add {ι : Type*} {M₁ M₂ : ℂ → Matrix ι ι ℂ} (h₁ : L3_Dm M₁)
    (h₂ : L3_Dm M₂) : L3_Dm (fun w => M₁ w + M₂ w) := fun k l n => by
  simp only [Matrix.add_apply]
  exact (h₁ k l n).add (h₂ k l n)

/-- The product rule for the entrywise derivative. -/
private lemma L3_dm_mul {ι : Type*} [Fintype ι] (s : ℂ) {M₁ M₂ : ℂ → Matrix ι ι ℂ}
    (h₁ : L3_Dm M₁) (h₂ : L3_Dm M₂) :
    L3_dm s (fun w => M₁ w * M₂ w) = fun w => L3_dm s M₁ w * M₂ w + M₁ w * L3_dm s M₂ w := by
  funext w
  ext k l
  have hd : ∀ m, DifferentiableAt ℝ (fun w => M₁ w k m * M₂ w m l) w := fun m =>
    ((h₁ k m).diff w).mul ((h₂ m l).diff w)
  simp only [L3_dm, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [fderiv_fun_sum fun m _ => hd m]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [fderiv_fun_mul ((h₁ k m).diff w) ((h₂ m l).diff w)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- The entrywise derivative of a constant matrix vanishes. -/
private lemma L3_dm_const {ι : Type*} (s : ℂ) (C : Matrix ι ι ℂ) :
    L3_dm s (fun _ : ℂ => C) = fun _ => 0 := by
  funext w
  ext k l
  simp [L3_dm]

/-- The entrywise derivative is additive. -/
private lemma L3_dm_add {ι : Type*} (s : ℂ) {M₁ M₂ : ℂ → Matrix ι ι ℂ} (h₁ : L3_Dm M₁)
    (h₂ : L3_Dm M₂) :
    L3_dm s (fun w => M₁ w + M₂ w) = fun w => L3_dm s M₁ w + L3_dm s M₂ w := by
  funext w
  ext k l
  simp only [L3_dm, Matrix.of_apply, Matrix.add_apply]
  rw [fderiv_fun_add ((h₁ k l).diff w) ((h₂ k l).diff w)]
  simp only [_root_.add_apply]
  ring

/-- The entrywise derivative commutes with scalar multiplication. -/
private lemma L3_dm_smul {ι : Type*} (s c : ℂ) {M : ℂ → Matrix ι ι ℂ} (h : L3_Dm M) :
    L3_dm s (fun w => c • M w) = fun w => c • L3_dm s M w := by
  funext w
  ext k l
  simp only [L3_dm, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul ((h k l).diff w)]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/-- `(P E_{ij} Q)_{kl} = P_{ki} Q_{jl}` for the matrix unit `E_{ij}`. -/
private lemma L3_single_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℂ)
    (i j k l : ι) : (P * Matrix.single i j (1 : ℂ) * Q) k l = P k i * Q j l := by
  have h1 : ∀ m, (P * Matrix.single i j (1 : ℂ)) k m = if j = m then P k i else 0 := by
    intro m
    by_cases hm : j = m
    · subst hm
      simp [Matrix.mul_single_apply_same]
    · simp [Matrix.mul_apply, Matrix.single_apply, hm]
  rw [Matrix.mul_apply]
  simp only [h1, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ### The resolvent along a slice -/

/-- The resolvent `G(w) = (setEntry h i j w + Λ - ξ)⁻¹` along a slice. -/
private def L3_g {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (h : Idx D N → Idx D N → ℂ)
    (i j : Idx D N) (w : ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of (setEntry h i j w) + Λ) ξ

/-- The resolvent along a slice through a Hermitian array has smooth entries. -/
private lemma L3_Dm.g {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {ξ : ℂ}
    (hξ : ξ.im ≠ 0) {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) : L3_Dm (L3_g Λ ξ h i j) := fun k l =>
  L3_sm_slice (F := fun h' => res (Matrix.of h' + Λ) ξ k l)
    (fun n => contDiff_res_symArr Λ hΛ ξ hξ k l n) h hh i j

/-- The constant `c = 1` for `i ≠ j` and `c = 1/2` for `i = j` of the slice derivatives. -/
private def L3_cc {D N : ℕ} (i j : Idx D N) : ℂ := if i = j then 1 / 2 else 1

/-- The matrix unit of the slice derivative: `E_{ij}` for `∂_w`, `E_{ji}` for `∂_{w̄}`. -/
private def L3_E {D N : ℕ} (s : ℂ) (i j : Idx D N) : Matrix (Idx D N) (Idx D N) ℂ :=
  if s = Complex.I then Matrix.single j i 1 else Matrix.single i j 1

/-- `∂_w G = -c G E_{ij} G` and `∂_{w̄} G = -c G E_{ji} G` along a Hermitian slice. -/
private lemma L3_dm_g {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {ξ : ℂ}
    (hξ : ξ.im ≠ 0) {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) :
    L3_dm s (L3_g Λ ξ h i j) = fun w =>
      (-L3_cc i j) • (L3_g Λ ξ h i j w * L3_E s i j * L3_g Λ ξ h i j w) := by
  funext w
  ext k l
  obtain ⟨d1, d2⟩ := res_dW Λ hΛ ξ hξ h hh i j k l
  rcases hs with rfl | rfl
  · rw [L3_dm_dWbar]
    simp only [L3_g] at d2 ⊢
    rw [d2]
    simp only [L3_E, ite_true, Matrix.smul_apply, L3_single_entry, smul_eq_mul, L3_cc]
  · have hne : -Complex.I ≠ Complex.I := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    rw [L3_dm_dW]
    simp only [L3_g] at d1 ⊢
    rw [d1]
    simp only [L3_E, hne, ite_false, Matrix.smul_apply, L3_single_entry, smul_eq_mul, L3_cc]

/-! ### Norms of vectors and matrices, Ward's identity -/

/-- The squared Euclidean norm `Σ_k |v_k|²`. -/
private def L3_ns {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ k, ‖v k‖ ^ 2

/-- The squared Hilbert–Schmidt norm `Σ_{k,l} |M_{kl}|²`. -/
private def L3_fs {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ := ∑ k, ∑ l, ‖M k l‖ ^ 2

private lemma L3_fs_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : 0 ≤ L3_fs M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- `|x^* A y| ≤ ‖A‖ |x| |y|`. -/
private lemma L3_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x y : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ≤ opNorm A * (Real.sqrt (L3_ns x) * Real.sqrt (L3_ns y)) := by
  have e : star x ⬝ᵥ (A *ᵥ y) = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanCLM_toLp]
    simp [dotProduct_comm]
  have hxn : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (L3_ns x) := by
    rw [EuclideanSpace.norm_eq]; rfl
  have hyn : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ = Real.sqrt (L3_ns y) := by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [e]
  unfold opNorm
  calc ‖inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
        (‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖) :=
        mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm _)
          (norm_nonneg _)
    _ = _ := by rw [hxn, hyn]; ring

/-- `‖1‖ ≤ 1`. -/
private lemma L3_opNorm_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `x^* (A y) = (Aᴴ x)^* y`. -/
private lemma L3_dot_adj {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

/-- Ward's identity (2.32) [eq_Ward] for a vector, on both half planes:
`|G u|² = Im(u^* G u) / Im ζ` for `G = (X - ζ)⁻¹`, `X` Hermitian, `Im ζ ≠ 0`. -/
private lemma L3_ward {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (u : ι → ℂ) :
    L3_ns (res X ζ *ᵥ u) = (star u ⬝ᵥ (res X ζ *ᵥ u)).im / ζ.im := by
  set R := res X ζ with hR
  obtain ⟨h1, h2⟩ := res_mul_sub_of_im_ne X hX ζ hζ
  have h3 : Rᴴ * (X - starRingEnd ℂ ζ • (1 : Matrix ι ι ℂ)) = 1 := by
    have := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hX.eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] at this
    simpa [Complex.star_def] using this
  have key : (ζ - starRingEnd ℂ ζ) • (Rᴴ * R) = R - Rᴴ := by
    have hd : (X - starRingEnd ℂ ζ • (1 : Matrix ι ι ℂ)) - (X - ζ • 1) =
        (ζ - starRingEnd ℂ ζ) • (1 : Matrix ι ι ℂ) := by
      rw [sub_smul]; abel
    calc (ζ - starRingEnd ℂ ζ) • (Rᴴ * R)
        = Rᴴ * ((ζ - starRingEnd ℂ ζ) • (1 : Matrix ι ι ℂ)) * R := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = Rᴴ * ((X - starRingEnd ℂ ζ • (1 : Matrix ι ι ℂ)) - (X - ζ • 1)) * R := by rw [hd]
      _ = Rᴴ * (X - starRingEnd ℂ ζ • (1 : Matrix ι ι ℂ)) * R - Rᴴ * ((X - ζ • 1) * R) := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (Rᴴ) (X - ζ • 1)]
      _ = R - Rᴴ := by rw [h3, Matrix.one_mul, h1, Matrix.mul_one]
  have hn : ((L3_ns (R *ᵥ u) : ℝ) : ℂ) = star u ⬝ᵥ ((Rᴴ * R) *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, L3_dot_adj, Matrix.conjTranspose_conjTranspose]
    simp only [L3_ns, dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj']
  have hz : ζ - starRingEnd ℂ ζ = 2 * Complex.I * ζ.im := by
    rw [Complex.sub_conj]; push_cast; ring
  have hz0 : (ζ - starRingEnd ℂ ζ) ≠ 0 := by
    rw [hz]; simp [hζ]
  have e3 : star u ⬝ᵥ ((Rᴴ * R) *ᵥ u) =
      (ζ - starRingEnd ℂ ζ)⁻¹ * (star u ⬝ᵥ (R *ᵥ u) - star u ⬝ᵥ (Rᴴ *ᵥ u)) := by
    have : Rᴴ * R = (ζ - starRingEnd ℂ ζ)⁻¹ • (R - Rᴴ) := by
      rw [← key, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rw [this, Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub,
      smul_eq_mul]
  have e4 : star u ⬝ᵥ (Rᴴ *ᵥ u) = starRingEnd ℂ (star u ⬝ᵥ (R *ᵥ u)) := by
    rw [L3_dot_adj, Matrix.conjTranspose_conjTranspose]
    simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Matrix.mulVec, Complex.star_def,
      Complex.conj_conj]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  apply Complex.ofReal_injective
  rw [hn, e3, e4, hz, Complex.sub_conj]
  push_cast
  field_simp

/-- `|G u|² ≤ |u^* G u| / |Im ζ|`. -/
private lemma L3_ward_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (u : ι → ℂ) :
    L3_ns (res X ζ *ᵥ u) ≤ ‖star u ⬝ᵥ (res X ζ *ᵥ u)‖ / |ζ.im| := by
  rw [L3_ward X hX ζ hζ u]
  have hw := Complex.abs_im_le_norm (star u ⬝ᵥ (res X ζ *ᵥ u))
  rcases lt_or_gt_of_ne hζ with h | h
  · rw [abs_of_neg h, ← neg_div_neg_eq]
    exact div_le_div_of_nonneg_right ((neg_le_abs _).trans hw) (by linarith)
  · rw [abs_of_pos h]
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans hw) h.le

/-- `‖G(ζ)‖ ≤ |Im ζ|⁻¹` on both half planes. -/
private lemma L3_opNorm_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) : opNorm (res X ζ) ≤ |ζ.im|⁻¹ := by
  rcases lt_or_gt_of_ne hζ with h | h
  · have h' : 0 < (starRingEnd ℂ ζ).im := by simpa using h
    have e : res X ζ = (res X (starRingEnd ℂ ζ))ᴴ := by
      have := res_conj X hX (starRingEnd ℂ ζ) h'
      rw [Complex.conj_conj] at this
      exact this
    rw [e, L3_opNorm_conjTranspose, abs_of_neg h]
    have := opNorm_res_le X hX _ h'
    simpa using this
  · rw [abs_of_pos h]
    exact opNorm_res_le X hX ζ h

/-- `|A M|_{HS}² ≤ ‖A‖² |M|_{HS}²`. -/
private lemma L3_fs_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι] (A M : Matrix ι ι ℂ) :
    L3_fs (A * M) ≤ opNorm A ^ 2 * L3_fs M := by
  have e : ∀ P : Matrix ι ι ℂ, L3_fs P = ∑ l, L3_ns (fun k => P k l) := by
    intro P
    simp only [L3_fs, L3_ns]
    exact Finset.sum_comm
  rw [e, e, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have : (fun k => (A * M) k l) = A *ᵥ (fun k => M k l) := by
    funext k
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [this]
  exact L3_mulVec_sq A _

/-- The Hilbert–Schmidt norm is invariant under the conjugate transpose. -/
private lemma L3_fs_conjT {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : L3_fs Mᴴ = L3_fs M := by
  simp only [L3_fs, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- `|M A|_{HS}² ≤ |M|_{HS}² ‖A‖²`. -/
private lemma L3_fs_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M A : Matrix ι ι ℂ) :
    L3_fs (M * A) ≤ L3_fs M * opNorm A ^ 2 := by
  rw [← L3_fs_conjT, Matrix.conjTranspose_mul, ← L3_fs_conjT M, ← L3_opNorm_conjTranspose A,
    mul_comm]
  exact L3_fs_mul_left _ _

/-- `|G|_{HS}² = Σ_l |G e_l|² ≤ Σ_l |G_{ll}| / |Im ζ|`. -/
private lemma L3_fs_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    L3_fs (res X ζ) ≤ ∑ l, ‖res X ζ l l‖ / |ζ.im| := by
  have e : L3_fs (res X ζ) = ∑ l, L3_ns (res X ζ *ᵥ Pi.single l 1) := by
    simp only [L3_fs, L3_ns]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e]
  refine Finset.sum_le_sum fun l _ => (L3_ward_le X hX ζ hζ _).trans_eq ?_
  congr 2
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `(Σ_{k,l} |M_{kl}|)² ≤ (card)² |M|_{HS}²`. -/
private lemma L3_sum_abs_sq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    (∑ k, ∑ l, ‖M k l‖) ^ 2 ≤ ((Fintype.card ι : ℝ) ^ 2) * L3_fs M := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => ‖M p.1 p.2‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul, mul_one, Fintype.sum_prod_type] at h
  rw [L3_fs]
  push_cast at h
  nlinarith [h]

/-! ### The fluctuation term as a polynomial in loops -/

/-- The factors `(B_r, Λ_r, ξ_r)` of a chain. -/
private abbrev L3_T (D N : ℕ) :=
  Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ

/-- The chain `G₃ B G₁ C G₂` of `X = G₃ B G₁ C G₂ T`. -/
private def L3_lX {D N : ℕ} (Λ B C : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ) :
    List (L3_T D N) :=
  [(1, Λ, z₃), (B, Λ, z₁), (C, Λ, z₂)]

/-- `X_{βα} = e_β^* G₃ B G₁ C G₂ (T e_α)`: with `B = E_{a₃}`, `C = E_{a₁}`, `T = E_{a₂} M₃`, the
coefficient of `h_{αβ}` in `⟨G₁ E_{a₁} G₂ E_{a₂} M₃ H G₃ E_{a₃}⟩`. -/
private def L3_X {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (h : Idx D N → Idx D N → ℂ) (β α : Idx D N) : ℂ :=
  star (Pi.single β (1 : ℂ)) ⬝ᵥ (chainB h (L3_lX Λ B C z₁ z₂ z₃) *ᵥ (T *ᵥ Pi.single α 1))

/-- `e_β^* M (T e_α) = (M T)_{βα}`. -/
private lemma L3_form_single {D N : ℕ} (M T : Matrix (Idx D N) (Idx D N) ℂ) (β α : Idx D N) :
    star (Pi.single β (1 : ℂ)) ⬝ᵥ (M *ᵥ (T *ᵥ Pi.single α 1)) = (M * T) β α := by
  rw [Matrix.mulVec_mulVec]
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- Chains of length one, two and three as matrix products. -/
private lemma L3_chain1 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a : L3_T D N) :
    chainB h [a] = a.1 * res (Matrix.of h + a.2.1) a.2.2 := by
  simp [chainB]

private lemma L3_chain2 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a b : L3_T D N) :
    chainB h [a, b] = a.1 * res (Matrix.of h + a.2.1) a.2.2 * (b.1 * res (Matrix.of h + b.2.1) b.2.2) := by
  simp [chainB]

private lemma L3_chain3 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a b c : L3_T D N) :
    chainB h [a, b, c] = a.1 * res (Matrix.of h + a.2.1) a.2.2 *
      (b.1 * res (Matrix.of h + b.2.1) b.2.2 * (c.1 * res (Matrix.of h + c.2.1) c.2.2)) := by
  simp [chainB]

private lemma L3_chain0 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) :
    chainB h ([] : List (L3_T D N)) = 1 := by
  simp [chainB]

/-- `X_{βα} = (G₃ B G₁ C G₂ T)_{βα}`. -/
private lemma L3_X_eq {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (h : Idx D N → Idx D N → ℂ) (β α : Idx D N) :
    L3_X Λ B C T z₁ z₂ z₃ h β α =
      (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ *
        T) β α := by
  rw [L3_X, L3_form_single, L3_lX, L3_chain3]
  simp only [Matrix.one_mul, Matrix.mul_assoc]

/-- The coefficients of the eight groups of terms of the fluctuation term. -/
private def L3_cf (D : ℕ) (θ : ℝ) : Fin 8 → ℂ :=
  ![(D : ℂ)⁻¹, -(D : ℂ)⁻¹, (θ : ℂ) * D, ((1 - θ : ℝ) : ℂ) * (D : ℂ)⁻¹, (θ : ℂ) * D,
    ((1 - θ : ℝ) : ℂ) * (D : ℂ)⁻¹, (θ : ℂ) * D, ((1 - θ : ℝ) : ℂ) * (D : ℂ)⁻¹]

/-- The first loops of the terms (the empty chain has loop `1`). -/
private def L3_l1 {D N : ℕ} (Λ C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ) (x : Fin D) :
    Fin 8 → List (L3_T D N) :=
  ![[], [], [(Ea D N x, Λ, z₃)], [(1, Λ, z₃)], [(T * Ea D N x, Λ, z₁), (C, Λ, z₂)],
    [(T, Λ, z₁), (C, Λ, z₂)], [(T * Ea D N x, Λ, z₂)], [(T, Λ, z₂)]]

/-- The second loops of the terms. -/
private def L3_l2 {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ) (x : Fin D) :
    Fin 8 → List (L3_T D N) :=
  ![[(T * B, Λ, z₁), (C, Λ, z₂)], [(B, Λ, z₁), (C, Λ, z₂), (T * (Λ - z₃ • 1), Λ, z₃)],
    [(B, Λ, z₁), (C, Λ, z₂), (T * Ea D N x, Λ, z₃)], [(B, Λ, z₁), (C, Λ, z₂), (T, Λ, z₃)],
    [(B, Λ, z₁), (Ea D N x, Λ, z₃)], [(B, Λ, z₁), (1, Λ, z₃)],
    [(B, Λ, z₁), (C, Λ, z₂), (Ea D N x, Λ, z₃)], [(B, Λ, z₁), (C, Λ, z₂), (1, Λ, z₃)]]

/-- The fluctuation term on Hermitian arrays as a polynomial in loops: with `g = G₁ C G₂ T`,
`⟨g B⟩ - ⟨g(Λ - z₃)G₃B⟩ + θ Σ_x D⟨G₃E_x⟩⟨gE_xG₃B⟩ + (1 - θ)⟨G₃⟩⟨gG₃B⟩ + θ Σ_x D⟨gE_x⟩⟨G₁E_xG₃B⟩
+ (1 - θ)⟨g⟩⟨G₁G₃B⟩ + θ Σ_x D⟨G₂TE_x⟩⟨G₁CG₂E_xG₃B⟩ + (1 - θ)⟨G₂T⟩⟨G₁CG₂G₃B⟩`. -/
private def L3_Z {D N : ℕ} (θ : ℝ) (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ∑ t : Fin 8, ∑ x : Fin D, L3_cf D θ t * ntr (chainB h (L3_l1 Λ C T z₁ z₂ z₃ x t)) *
    ntr (chainB h (L3_l2 Λ B C T z₁ z₂ z₃ x t))

/-- The counterterms of Definition 2.12 [def:underline] for `f = G₃`, `g = G₁ C G₂ T`:
`⟨g S_θ(G₃) G₃ B⟩ + ⟨G₁ S_θ(g) G₃ B⟩ + ⟨G₁ C G₂ S_θ(G₂ T) G₃ B⟩`. -/
private def L3_C {D N : ℕ} (θ : ℝ) (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ntr (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T *
      (sTheta D N θ (res (Matrix.of h + Λ) z₃) * res (Matrix.of h + Λ) z₃) * B) +
    ntr (res (Matrix.of h + Λ) z₁ *
      sTheta D N θ (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) *
        res (Matrix.of h + Λ) z₃ * B) +
    ntr (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ *
      sTheta D N θ (res (Matrix.of h + Λ) z₂ * T) * res (Matrix.of h + Λ) z₃ * B)

private lemma L3_ntr_add {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P + Q) = ntr P + ntr Q := by
  simp [ntr, Matrix.trace_add, mul_add]

private lemma L3_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

private lemma L3_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

private lemma L3_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (P : κ → Matrix ι ι ℂ) :
    ntr (∑ k ∈ s, P k) = ∑ k ∈ s, ntr (P k) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

private lemma L3_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  unfold ntr
  rw [Matrix.trace_mul_comm]

private lemma L3_ntr_one {D N : ℕ} [NeZero D] [NeZero N] :
    ntr (1 : Matrix (Idx D N) (Idx D N) ℂ) = 1 := by
  have hD : (D : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp only [ntr, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp

/-- `⟨P S_θ(R) Q⟩ = θ Σ_x D⟨R E_x⟩⟨P E_x Q⟩ + (1 - θ)⟨R⟩⟨P Q⟩`. -/
private lemma L3_ntr_S {D N : ℕ} (θ : ℝ) (P R Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (P * sTheta D N θ R * Q) = (θ : ℂ) * (∑ x : Fin D, ((D : ℂ) * ntr (R * Ea D N x)) *
      ntr (P * Ea D N x * Q)) + ((1 - θ : ℝ) : ℂ) * ntr R * ntr (P * Q) := by
  unfold sTheta
  simp only [Matrix.mul_add, Matrix.add_mul, L3_ntr_add, Matrix.mul_smul, Matrix.smul_mul,
    L3_ntr_smul, Matrix.mul_sum, Matrix.sum_mul, L3_ntr_sum, Matrix.mul_one]
  ring

/-- `underThree = ⟨G₁ C G₂ T H G₃ B⟩ + (the counterterms)` for `B = E_{a₃}`, `C = E_{a₁}`,
`T = E_{a₂} M₃`. -/
private lemma L3_under_eq {D N : ℕ} (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (a₁ a₂ a₃ : Fin D) (h : Idx D N → Idx D N → ℂ) :
    underThree Λ θ h z₁ z₂ z₃ a₁ a₂ a₃ =
      ntr (res (Matrix.of h + Λ) z₁ * Ea D N a₁ * res (Matrix.of h + Λ) z₂ *
        (Ea D N a₂ * MExt Λ z₃) * Matrix.of h * res (Matrix.of h + Λ) z₃ * Ea D N a₃) +
        L3_C θ Λ (Ea D N a₃) (Ea D N a₁) (Ea D N a₂ * MExt Λ z₃) z₁ z₂ z₃ h := by
  unfold underThree hgUnder L3_C
  simp only [Matrix.mul_add, Matrix.add_mul, L3_ntr_add, Matrix.mul_assoc]
  ring

/-- `⟨G₁ C G₂ T H G₃ B⟩ = (DN)⁻¹ Σ_{β,α} X_{βα} h_{αβ}`. -/
private lemma L3_ntrH {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    ntr (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T * Matrix.of h *
      res (Matrix.of h + Λ) z₃ * B) =
      ((D : ℂ) * N)⁻¹ * ∑ β, ∑ α, L3_X Λ B C T z₁ z₂ z₃ h β α * h α β := by
  have e : res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T * Matrix.of h *
      res (Matrix.of h + Λ) z₃ * B =
      (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) *
        (Matrix.of h * (res (Matrix.of h + Λ) z₃ * B)) := by
    simp only [Matrix.mul_assoc]
  have e2 : Matrix.of h * (res (Matrix.of h + Λ) z₃ * B) *
      (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) =
      Matrix.of h * (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
        res (Matrix.of h + Λ) z₂ * T) := by
    simp only [Matrix.mul_assoc]
  rw [e, L3_ntr_comm, e2]
  simp only [ntr, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply (M := Matrix.of h), Matrix.of_apply]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
  rw [L3_X_eq]
  ring

/-- On Hermitian arrays the polynomial `L3_Z` is `⟨G₁ C G₂ T H G₃ B⟩` plus the counterterms. -/
private lemma L3_Z_eq {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ)
    (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z₁ z₂ z₃ : ℂ)
    (hz₃ : z₃.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    L3_Z θ Λ B C T z₁ z₂ z₃ h =
      ntr (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T * Matrix.of h *
        res (Matrix.of h + Λ) z₃ * B) + L3_C θ Λ B C T z₁ z₂ z₃ h := by
  have hres := (res_mul_sub_of_im_ne (Matrix.of h + Λ) (hh.add hΛ) z₃ hz₃).1
  have hHG : Matrix.of h * res (Matrix.of h + Λ) z₃ =
      1 - (Λ - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z₃ := by
    calc Matrix.of h * res (Matrix.of h + Λ) z₃
        = (Matrix.of h + Λ - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z₃ -
            (Λ - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z₃ := by
          rw [← Matrix.sub_mul]; congr 1; abel
      _ = _ := by rw [hres]
  have hD : (D : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
  unfold L3_C L3_Z
  have eH : res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T * Matrix.of h *
      res (Matrix.of h + Λ) z₃ * B = res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T *
        (Matrix.of h * res (Matrix.of h + Λ) z₃) * B := by
    simp only [Matrix.mul_assoc]
  have eS1 : res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T *
      (sTheta D N θ (res (Matrix.of h + Λ) z₃) * res (Matrix.of h + Λ) z₃) * B =
      (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) *
        sTheta D N θ (res (Matrix.of h + Λ) z₃) * (res (Matrix.of h + Λ) z₃ * B) := by
    simp only [Matrix.mul_assoc]
  have eS2 : res (Matrix.of h + Λ) z₁ *
      sTheta D N θ (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) *
        res (Matrix.of h + Λ) z₃ * B = res (Matrix.of h + Λ) z₁ *
      sTheta D N θ (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) *
        (res (Matrix.of h + Λ) z₃ * B) := by
    simp only [Matrix.mul_assoc]
  have eS3 : res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ *
      sTheta D N θ (res (Matrix.of h + Λ) z₂ * T) * res (Matrix.of h + Λ) z₃ * B =
      (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂) *
        sTheta D N θ (res (Matrix.of h + Λ) z₂ * T) * (res (Matrix.of h + Λ) z₃ * B) := by
    simp only [Matrix.mul_assoc]
  rw [eH, hHG, eS1, eS2, eS3, L3_ntr_S, L3_ntr_S, L3_ntr_S]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, L3_cf, L3_l1, L3_l2, Matrix.cons_val_zero,
    Matrix.cons_val_succ, L3_chain0, L3_chain1, L3_chain2, L3_chain3, L3_ntr_one,
    Matrix.one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  generalize Λ - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ) = L
  generalize res (Matrix.of h + Λ) z₁ = G₁
  generalize res (Matrix.of h + Λ) z₂ = G₂
  generalize res (Matrix.of h + Λ) z₃ = G₃
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, L3_ntr_sub]
  simp only [Matrix.mul_assoc]
  have c0 : ntr (T * (B * (G₁ * (C * G₂)))) = ntr (G₁ * (C * (G₂ * (T * B)))) := by
    rw [← Matrix.mul_assoc T B, L3_ntr_comm]; simp only [Matrix.mul_assoc]
  have c4 : ∀ x, ntr (T * (Ea D N x * (G₁ * (C * G₂)))) =
      ntr (G₁ * (C * (G₂ * (T * Ea D N x)))) := by
    intro x; rw [← Matrix.mul_assoc T, L3_ntr_comm]; simp only [Matrix.mul_assoc]
  have c5 : ntr (T * (G₁ * (C * G₂))) = ntr (G₁ * (C * (G₂ * T))) := by
    rw [L3_ntr_comm]; simp only [Matrix.mul_assoc]
  have c6 : ∀ x, ntr (T * (Ea D N x * G₂)) = ntr (G₂ * (T * Ea D N x)) := by
    intro x; rw [← Matrix.mul_assoc, L3_ntr_comm]
  have c7 : ntr (T * G₂) = ntr (G₂ * T) := L3_ntr_comm _ _
  have c2 : ∀ x, ntr (Ea D N x * G₃) = ntr (G₃ * Ea D N x) := fun x => L3_ntr_comm _ _
  have cB : ∀ Q, ntr (B * Q) = ntr (Q * B) := fun Q => L3_ntr_comm _ _
  simp only [c0, c4, c5, c6, c7, c2, cB, Matrix.mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have s1 : ∀ f g : Fin D → ℂ, ∑ x, (θ : ℂ) * D * f x * g x = ∑ x, (θ : ℂ) * (D * f x * g x) :=
    fun f g => Finset.sum_congr rfl fun x _ => by ring
  rw [s1, s1, s1]
  field_simp
  ring

/-- `G(ζ)^* = G(ζ̄)` on both half planes. -/
private lemma L3_res_conjT {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) : (res X ζ)ᴴ = res X (starRingEnd ℂ ζ) := by
  rcases lt_or_gt_of_ne hζ with h | h
  · have h' : 0 < (starRingEnd ℂ ζ).im := by simpa using h
    have := res_conj X hX (starRingEnd ℂ ζ) h'
    rw [Complex.conj_conj] at this
    rw [this, Matrix.conjTranspose_conjTranspose]
  · exact (res_conj X hX ζ h).symm

/-- The spectral parameters `ζ ∈ {z, z̄}` with `Im z > 0`. -/
private def L3_pm (z ζ : ℂ) : Prop := ζ = z ∨ ζ = starRingEnd ℂ z

private lemma L3_pm_im {z ζ : ℂ} (hz : 0 < z.im) (hζ : L3_pm z ζ) : |ζ.im| = z.im := by
  rcases hζ with rfl | rfl
  · exact abs_of_pos hz
  · simp [abs_of_pos hz]

private lemma L3_pm_ne {z ζ : ℂ} (hz : 0 < z.im) (hζ : L3_pm z ζ) : ζ.im ≠ 0 := by
  have := L3_pm_im hz hζ
  intro h0
  rw [h0, abs_zero] at this
  linarith

private lemma L3_pm_conj {z ζ : ℂ} (hζ : L3_pm z ζ) : L3_pm z (starRingEnd ℂ ζ) := by
  rcases hζ with rfl | rfl
  · exact Or.inr rfl
  · left; simp

/-- The operator norm of a chain whose factors have `‖B_r‖ ≤ K` and spectral parameters in
`{z, z̄}`, on a Hermitian array: `‖B₁G₁⋯B_qG_q‖ ≤ (K/η)^q`. -/
private lemma L3_opNorm_chain {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (K : ℝ) (hK : 0 ≤ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    ∀ l : List (L3_T D N), (∀ f ∈ l, opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2) →
      opNorm (chainB h l) ≤ (K * z.im⁻¹) ^ l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [L3_chain0, List.length_nil, pow_zero]
    exact L3_opNorm_one
  | cons a t ih =>
    intro hl
    have ha := hl a (List.mem_cons_self)
    have ht := ih fun f hf => hl f (List.mem_cons_of_mem a hf)
    have e : chainB h (a :: t) = a.1 * res (Matrix.of h + a.2.1) a.2.2 * chainB h t := by
      simp [chainB]
    rw [e, List.length_cons, pow_succ']
    have hG : opNorm (res (Matrix.of h + a.2.1) a.2.2) ≤ z.im⁻¹ := by
      rw [ha.2.1]
      have := L3_opNorm_res (Matrix.of h + Λ) (hh.add hΛ) a.2.2 (L3_pm_ne hz ha.2.2)
      rwa [L3_pm_im hz ha.2.2] at this
    have h0 : 0 ≤ opNorm (chainB h t) := norm_nonneg _
    calc opNorm (a.1 * res (Matrix.of h + a.2.1) a.2.2 * chainB h t)
        ≤ opNorm a.1 * opNorm (res (Matrix.of h + a.2.1) a.2.2) * opNorm (chainB h t) :=
          (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) h0)
      _ ≤ K * z.im⁻¹ * (K * z.im⁻¹) ^ t.length := by
          have h1 : opNorm a.1 * opNorm (res (Matrix.of h + a.2.1) a.2.2) ≤ K * z.im⁻¹ :=
            mul_le_mul ha.1 hG (norm_nonneg _) hK
          exact mul_le_mul h1 ht h0 (by positivity)

/-- The good event of the forms over a set `U` of vectors at `z` and `z̄`. -/
private def L3_good {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (U : Set (Idx D N → ℂ))
    (Γ₀ : ℝ) (h : Idx D N → Idx D N → ℂ) : Prop :=
  ∀ ζ, L3_pm z ζ → ∀ u ∈ U, ∀ v ∈ U, ‖star u ⬝ᵥ (res (Matrix.of h + Λ) ζ *ᵥ v)‖ ≤ Γ₀

/-- On the good event, `|G(ζ) v|² ≤ Γ₀/η` and `|G(ζ)^* v|² ≤ Γ₀/η` for `v ∈ U`. -/
private lemma L3_good_ward {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {U : Set (Idx D N → ℂ)} {Γ₀ : ℝ} {h : Idx D N → Idx D N → ℂ}
    (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z U Γ₀ h) {ζ : ℂ} (hζ : L3_pm z ζ)
    {v : Idx D N → ℂ} (hv : v ∈ U) :
    L3_ns (res (Matrix.of h + Λ) ζ *ᵥ v) ≤ Γ₀ / z.im ∧
      L3_ns ((res (Matrix.of h + Λ) ζ)ᴴ *ᵥ v) ≤ Γ₀ / z.im := by
  have hX := hh.add hΛ
  constructor
  · refine (L3_ward_le _ hX ζ (L3_pm_ne hz hζ) v).trans ?_
    rw [L3_pm_im hz hζ]
    exact div_le_div_of_nonneg_right (hg ζ hζ v hv v hv) hz.le
  · rw [L3_res_conjT _ hX ζ (L3_pm_ne hz hζ)]
    have hζ' := L3_pm_conj hζ
    refine (L3_ward_le _ hX _ (L3_pm_ne hz hζ') v).trans ?_
    rw [L3_pm_im hz hζ']
    exact div_le_div_of_nonneg_right (hg _ hζ' v hv v hv) hz.le

/-- The sharp bound on chain entries on the good event (Ward's identity at both ends): for
chains of length `q ≤ 4` with factors `(Q, Λ, ζ)`, `Q ∈ 𝒬`, `‖Q‖ ≤ K`, `ζ ∈ {z, z̄}`, and
`x, y ∈ X ⊆ U` with `Q^* x ∈ U`: `|x^* C y| ≤ K^q Γ₀ η^{-(q-1)}`. -/
private lemma L3_entry_sharp {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {U : Set (Idx D N → ℂ)} {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z U Γ₀ h)
    (K : ℝ) (hK : 1 ≤ K) (Q : Set (Matrix (Idx D N) (Idx D N) ℂ)) (X : Set (Idx D N → ℂ))
    (hXU : X ⊆ U) (hQX : ∀ B ∈ Q, ∀ x ∈ X, Bᴴ *ᵥ x ∈ U) (l : List (L3_T D N))
    (hl1 : 1 ≤ l.length) (hl3 : l.length ≤ 4)
    (hl : ∀ f ∈ l, f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2) :
    ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB h l *ᵥ y)‖ ≤ K ^ l.length * Γ₀ * (z.im⁻¹) ^ (l.length - 1) := by
  intro x hx y hy
  have hX := hh.add hΛ
  have hη : 0 < z.im := hz
  have hK0 : 0 ≤ K := by linarith
  -- the two ends
  have hend : ∀ f ∈ l, Real.sqrt (L3_ns ((res (Matrix.of h + f.2.1) f.2.2)ᴴ *ᵥ (f.1ᴴ *ᵥ x))) ≤
      Real.sqrt (Γ₀ / z.im) := by
    intro f hf
    obtain ⟨hfQ, -, hfΛ, hfz⟩ := hl f hf
    rw [hfΛ]
    exact Real.sqrt_le_sqrt (L3_good_ward hΛ hz hh hg hfz (hQX _ hfQ x hx)).2
  have hendy : ∀ f ∈ l, Real.sqrt (L3_ns (res (Matrix.of h + f.2.1) f.2.2 *ᵥ y)) ≤
      Real.sqrt (Γ₀ / z.im) := by
    intro f hf
    obtain ⟨-, -, hfΛ, hfz⟩ := hl f hf
    rw [hfΛ]
    exact Real.sqrt_le_sqrt (L3_good_ward hΛ hz hh hg hfz (hXU hy)).1
  have hsq : Real.sqrt (Γ₀ / z.im) * Real.sqrt (Γ₀ / z.im) = Γ₀ * z.im⁻¹ := by
    rw [Real.mul_self_sqrt (by positivity), div_eq_mul_inv]
  have hpow : ∀ n : ℕ, 1 ≤ K ^ n := fun n => one_le_pow₀ hK
  match l, hl1, hl3 with
  | [a], _, _ =>
    have ha := hl a (by simp)
    rw [L3_chain1, ← Matrix.mulVec_mulVec, L3_dot_adj]
    have := hg a.2.2 ha.2.2.2 _ (hQX _ ha.1 x hx) y (hXU hy)
    rw [ha.2.2.1]
    simp only [List.length_singleton, pow_one, Nat.sub_self, pow_zero, mul_one]
    nlinarith
  | [a, b], _, _ =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    rw [L3_chain2]
    have e : star x ⬝ᵥ ((a.1 * res (Matrix.of h + a.2.1) a.2.2 *
        (b.1 * res (Matrix.of h + b.2.1) b.2.2)) *ᵥ y) =
        star ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x)) ⬝ᵥ
          (b.1 *ᵥ (res (Matrix.of h + b.2.1) b.2.2 *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, L3_dot_adj,
        L3_dot_adj (res _ _)]
    rw [e]
    refine (L3_form_le _ _ _).trans ?_
    have h1 := hend a (by simp)
    have h2 := hendy b (by simp)
    simp only [List.length_cons, List.length_nil]
    calc opNorm b.1 * (Real.sqrt (L3_ns ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x))) *
          Real.sqrt (L3_ns (res (Matrix.of h + b.2.1) b.2.2 *ᵥ y)))
        ≤ K * (Real.sqrt (Γ₀ / z.im) * Real.sqrt (Γ₀ / z.im)) :=
          mul_le_mul hb.2.1 (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (by positivity) hK0
      _ = K * (Γ₀ * z.im⁻¹) := by rw [hsq]
      _ ≤ K ^ (0 + 1 + 1) * Γ₀ * z.im⁻¹ ^ (0 + 1 + 1 - 1) := by
          simp only [zero_add, Nat.reduceAdd, Nat.add_one_sub_one, pow_one]
          have h0 : 0 ≤ Γ₀ * z.im⁻¹ := by positivity
          have hKK : K ≤ K ^ 2 := by nlinarith
          calc K * (Γ₀ * z.im⁻¹) ≤ K ^ 2 * (Γ₀ * z.im⁻¹) := mul_le_mul_of_nonneg_right hKK h0
            _ = K ^ 2 * Γ₀ * z.im⁻¹ := by ring
  | [a, b, c], _, _ =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have hc := hl c (by simp)
    have e : chainB h [a, b, c] = a.1 * res (Matrix.of h + a.2.1) a.2.2 *
        (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) * res (Matrix.of h + c.2.1) c.2.2 := by
      simp [chainB, Matrix.mul_assoc]
    rw [e]
    have e2 : star x ⬝ᵥ ((a.1 * res (Matrix.of h + a.2.1) a.2.2 *
        (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) * res (Matrix.of h + c.2.1) c.2.2) *ᵥ y) =
        star ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x)) ⬝ᵥ
          ((b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) *ᵥ
            (res (Matrix.of h + c.2.1) c.2.2 *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, L3_dot_adj,
        L3_dot_adj (res _ _)]
    rw [e2]
    refine (L3_form_le _ _ _).trans ?_
    have h1 := hend a (by simp)
    have h2 := hendy c (by simp)
    have hbG : opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) ≤ K * z.im⁻¹ * K := by
      have hG : opNorm (res (Matrix.of h + b.2.1) b.2.2) ≤ z.im⁻¹ := by
        rw [hb.2.2.1]
        have := L3_opNorm_res (Matrix.of h + Λ) hX b.2.2 (L3_pm_ne hz hb.2.2.2)
        rwa [L3_pm_im hz hb.2.2.2] at this
      calc opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1)
          ≤ opNorm b.1 * opNorm (res (Matrix.of h + b.2.1) b.2.2) * opNorm c.1 :=
            (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _)
              (norm_nonneg _))
        _ ≤ K * z.im⁻¹ * K :=
            mul_le_mul (mul_le_mul hb.2.1 hG (norm_nonneg _) hK0) hc.2.1 (norm_nonneg _)
              (by positivity)
    simp only [List.length_cons, List.length_nil]
    calc opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) *
          (Real.sqrt (L3_ns ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x))) *
            Real.sqrt (L3_ns (res (Matrix.of h + c.2.1) c.2.2 *ᵥ y)))
        ≤ K * z.im⁻¹ * K * (Real.sqrt (Γ₀ / z.im) * Real.sqrt (Γ₀ / z.im)) :=
          mul_le_mul hbG (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (by positivity) (by positivity)
      _ = K ^ 2 * Γ₀ * z.im⁻¹ ^ 2 := by rw [hsq]; ring
      _ ≤ K ^ (0 + 1 + 1 + 1) * Γ₀ * z.im⁻¹ ^ (0 + 1 + 1 + 1 - 1) := by
          simp only [zero_add, Nat.reduceAdd, Nat.add_one_sub_one]
          have h0 : 0 ≤ Γ₀ * z.im⁻¹ ^ 2 := by positivity
          have hKK : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK (by norm_num)
          calc K ^ 2 * Γ₀ * z.im⁻¹ ^ 2 = K ^ 2 * (Γ₀ * z.im⁻¹ ^ 2) := by ring
            _ ≤ K ^ 3 * (Γ₀ * z.im⁻¹ ^ 2) := mul_le_mul_of_nonneg_right hKK h0
            _ = K ^ 3 * Γ₀ * z.im⁻¹ ^ 2 := by ring
  | [a, b, c, d], _, _ =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have hc := hl c (by simp)
    have hd := hl d (by simp)
    have e : chainB h [a, b, c, d] = a.1 * res (Matrix.of h + a.2.1) a.2.2 *
        (b.1 * res (Matrix.of h + b.2.1) b.2.2 * (c.1 * res (Matrix.of h + c.2.1) c.2.2 * d.1)) *
          res (Matrix.of h + d.2.1) d.2.2 := by
      simp [chainB, Matrix.mul_assoc]
    rw [e]
    have e2 : star x ⬝ᵥ ((a.1 * res (Matrix.of h + a.2.1) a.2.2 *
        (b.1 * res (Matrix.of h + b.2.1) b.2.2 * (c.1 * res (Matrix.of h + c.2.1) c.2.2 * d.1)) *
          res (Matrix.of h + d.2.1) d.2.2) *ᵥ y) =
        star ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x)) ⬝ᵥ
          ((b.1 * res (Matrix.of h + b.2.1) b.2.2 * (c.1 * res (Matrix.of h + c.2.1) c.2.2 * d.1)) *ᵥ
            (res (Matrix.of h + d.2.1) d.2.2 *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, L3_dot_adj,
        L3_dot_adj (res _ _)]
    rw [e2]
    refine (L3_form_le _ _ _).trans ?_
    have h1 := hend a (by simp)
    have h2 := hendy d (by simp)
    have hGr : ∀ f ∈ [a, b, c, d], opNorm (res (Matrix.of h + f.2.1) f.2.2) ≤ z.im⁻¹ := by
      intro f hf
      have hf' := hl f hf
      rw [hf'.2.2.1]
      have := L3_opNorm_res (Matrix.of h + Λ) hX f.2.2 (L3_pm_ne hz hf'.2.2.2)
      rwa [L3_pm_im hz hf'.2.2.2] at this
    have hcG : opNorm (c.1 * res (Matrix.of h + c.2.1) c.2.2 * d.1) ≤ K * z.im⁻¹ * K :=
      (opNorm_mul_le _ _).trans (mul_le_mul ((opNorm_mul_le _ _).trans
        (mul_le_mul hc.2.1 (hGr c (by simp)) (norm_nonneg _) hK0)) hd.2.1 (norm_nonneg _)
          (by positivity))
    have hbG : opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 *
        (c.1 * res (Matrix.of h + c.2.1) c.2.2 * d.1)) ≤ K * z.im⁻¹ * (K * z.im⁻¹ * K) :=
      (opNorm_mul_le _ _).trans (mul_le_mul ((opNorm_mul_le _ _).trans
        (mul_le_mul hb.2.1 (hGr b (by simp)) (norm_nonneg _) hK0)) hcG (norm_nonneg _)
          (by positivity))
    simp only [List.length_cons, List.length_nil]
    calc opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 *
          (c.1 * res (Matrix.of h + c.2.1) c.2.2 * d.1)) *
          (Real.sqrt (L3_ns ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x))) *
            Real.sqrt (L3_ns (res (Matrix.of h + d.2.1) d.2.2 *ᵥ y)))
        ≤ K * z.im⁻¹ * (K * z.im⁻¹ * K) * (Real.sqrt (Γ₀ / z.im) * Real.sqrt (Γ₀ / z.im)) :=
          mul_le_mul hbG (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (by positivity) (by positivity)
      _ = K ^ 3 * Γ₀ * z.im⁻¹ ^ 3 := by rw [hsq]; ring
      _ ≤ K ^ (0 + 1 + 1 + 1 + 1) * Γ₀ * z.im⁻¹ ^ (0 + 1 + 1 + 1 + 1 - 1) := by
          simp only [zero_add, Nat.reduceAdd, Nat.add_one_sub_one]
          have h0 : 0 ≤ Γ₀ * z.im⁻¹ ^ 3 := by positivity
          have hKK : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
          calc K ^ 3 * Γ₀ * z.im⁻¹ ^ 3 = K ^ 3 * (Γ₀ * z.im⁻¹ ^ 3) := by ring
            _ ≤ K ^ 4 * (Γ₀ * z.im⁻¹ ^ 3) := mul_le_mul_of_nonneg_right hKK h0
            _ = K ^ 4 * Γ₀ * z.im⁻¹ ^ 3 := by ring

/-! ### The vectors of the good event and the derivative bounds of the chains -/

open scoped Matrix.Norms.L2Operator in
/-- `‖E_a‖ ≤ 1`. -/
private lemma L3_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

private lemma L3_Ea_conj (D N : ℕ) (a : Fin D) : (Ea D N a)ᴴ = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

/-- The matrices `Q` of the vectors `Q e_k` of the good event. -/
private def L3_Qf {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    Fin 9 ⊕ (Fin D ⊕ Fin D) → Matrix (Idx D N) (Idx D N) ℂ
  | Sum.inl i => ![1, T, Bᴴ, Bᴴ * T, (T * B)ᴴ, (T * (Λ - z₃ • 1))ᴴ, Tᴴ, Cᴴ, Cᴴ * T] i
  | Sum.inr (Sum.inl x) => Ea D N x
  | Sum.inr (Sum.inr x) => (T * Ea D N x)ᴴ

/-- The vectors `Q e_k` of the good event. -/
private def L3_U {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    Set (Idx D N → ℂ) :=
  Set.range fun p : (Fin 9 ⊕ (Fin D ⊕ Fin D)) × Idx D N =>
    L3_Qf Λ B C T z₃ p.1 *ᵥ Pi.single p.2 1

private lemma L3_U_mem {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ)
    (q : Fin 9 ⊕ (Fin D ⊕ Fin D)) (M : Matrix (Idx D N) (Idx D N) ℂ)
    (hM : L3_Qf Λ B C T z₃ q = M) (k : Idx D N) :
    M *ᵥ Pi.single k 1 ∈ L3_U Λ B C T z₃ := ⟨(q, k), by rw [← hM]⟩

/-- The vectors `e_k` and `T e_k` of the entries of `X`. -/
private def L3_XX {D N : ℕ} (T : Matrix (Idx D N) (Idx D N) ℂ) : Set (Idx D N → ℂ) :=
  Set.range (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)) ∪
    Set.range (fun k : Idx D N => T *ᵥ Pi.single k 1)

/-- The vectors `e_k` of the loops. -/
private def L3_XL (D N : ℕ) : Set (Idx D N → ℂ) :=
  Set.range (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ))

private lemma L3_e_U {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ)
    (k : Idx D N) : (Pi.single k 1 : Idx D N → ℂ) ∈ L3_U Λ B C T z₃ := by
  have := L3_U_mem Λ B C T z₃ (Sum.inl 0) 1 (by simp [L3_Qf]) k
  rwa [Matrix.one_mulVec] at this

private lemma L3_XX_U {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    L3_XX T ⊆ L3_U Λ B C T z₃ := by
  rintro v (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact L3_e_U Λ B C T z₃ k
  · exact L3_U_mem Λ B C T z₃ (Sum.inl 1) T (by simp [L3_Qf]) k

private lemma L3_XL_U {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    L3_XL D N ⊆ L3_U Λ B C T z₃ := by
  rintro v ⟨k, rfl⟩
  exact L3_e_U Λ B C T z₃ k

/-- The admissible matrices of the factors of `X`: `Q ∈ {1, B, C}` and `Q^* x ∈ U` for `x` in
`L3_XX`. -/
private lemma L3_QX_ok {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    ∀ Q ∈ ({1, B, C} : Set (Matrix (Idx D N) (Idx D N) ℂ)), ∀ x ∈ L3_XX T,
      Qᴴ *ᵥ x ∈ L3_U Λ B C T z₃ := by
  intro Q hQ x hx
  rcases hQ with hQ | hQ | hQ <;> rw [hQ]
  · rw [Matrix.conjTranspose_one, Matrix.one_mulVec]
    exact L3_XX_U Λ B C T z₃ hx
  · rcases hx with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact L3_U_mem Λ B C T z₃ (Sum.inl 2) Bᴴ (by simp [L3_Qf]) k
    · rw [Matrix.mulVec_mulVec]
      exact L3_U_mem Λ B C T z₃ (Sum.inl 3) (Bᴴ * T) (by simp [L3_Qf]) k
  · rcases hx with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact L3_U_mem Λ B C T z₃ (Sum.inl 7) Cᴴ (by simp [L3_Qf]) k
    · rw [Matrix.mulVec_mulVec]
      exact L3_U_mem Λ B C T z₃ (Sum.inl 8) (Cᴴ * T) (by simp [L3_Qf]) k

/-- The admissible matrices of the factors of the loops. -/
private def L3_QL {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    Set (Matrix (Idx D N) (Idx D N) ℂ) :=
  {1, T, B, C, T * B, T * (Λ - z₃ • 1)} ∪ Set.range (Ea D N) ∪
    Set.range (fun x => T * Ea D N x)

private lemma L3_QL_ok {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    ∀ Q ∈ L3_QL Λ B C T z₃, ∀ x ∈ L3_XL D N, Qᴴ *ᵥ x ∈ L3_U Λ B C T z₃ := by
  rintro Q hQ x ⟨k, rfl⟩
  rcases hQ with ((hQ | hQ | hQ | hQ | hQ | hQ) | ⟨y, rfl⟩) | ⟨y, rfl⟩
  · rw [hQ, Matrix.conjTranspose_one, Matrix.one_mulVec]; exact L3_e_U Λ B C T z₃ k
  · rw [hQ]; exact L3_U_mem Λ B C T z₃ (Sum.inl 6) _ (by simp [L3_Qf]) k
  · rw [hQ]; exact L3_U_mem Λ B C T z₃ (Sum.inl 2) _ (by simp [L3_Qf]) k
  · rw [hQ]; exact L3_U_mem Λ B C T z₃ (Sum.inl 7) _ (by simp [L3_Qf]) k
  · rw [hQ]; exact L3_U_mem Λ B C T z₃ (Sum.inl 4) _ (by simp [L3_Qf]) k
  · rw [hQ]; exact L3_U_mem Λ B C T z₃ (Sum.inl 5) _ (by simp [L3_Qf]) k
  · rw [L3_Ea_conj]; exact L3_U_mem Λ B C T z₃ (Sum.inr (Sum.inl y)) _ rfl k
  · exact L3_U_mem Λ B C T z₃ (Sum.inr (Sum.inr y)) _ rfl k

/-- The sharp bound function `Γ_q = K^q Γ₀ η^{-(q-1)}` of the chain entries on the good event. -/
private def L3_Gs (K Γ₀ η : ℝ) (q : ℕ) : ℝ := K ^ q * Γ₀ * (η⁻¹) ^ (q - 1)

private lemma L3_Gs_mul (K Γ₀ η : ℝ) : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    L3_Gs K Γ₀ η a * L3_Gs K Γ₀ η b ≤ L3_Gs K Γ₀ η 1 * L3_Gs K Γ₀ η (a + b - 1) := by
  intro a b ha hb
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [L3_Gs, Nat.add_sub_cancel, show a + 1 + (b + 1) - 1 = a + b + 1 by omega,
    show a + b + 1 - 1 = a + b by omega, Nat.sub_self, pow_zero, pow_one, pow_add, pow_succ]
  ring_nf
  exact le_rfl

/-- The factors of a chain with matrices in `𝒬`, the pair `(Λ, ζ)`, `ζ ∈ {z, z̄}`, and the
factors of the sub-chains admitted in `chainB_wirt_le`. -/
private lemma L3_sub_factors {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {Q : Set (Matrix (Idx D N) (Idx D N) ℂ)} (h1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ Q)
    {K : ℝ} (hK : 1 ≤ K) {l : List (L3_T D N)}
    (hl : ∀ f ∈ l, f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2)
    {l' : List (L3_T D N)} (hl' : ∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) :
    ∀ f ∈ l', f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2 := by
  intro f hf
  rcases hl' f hf with h | ⟨h1', g, hg, hgf⟩
  · exact hl f h
  · obtain ⟨-, -, hgΛ, hgz⟩ := hl g hg
    refine ⟨h1' ▸ h1, h1' ▸ L3_opNorm_one.trans hK, ?_, ?_⟩
    · rw [← hgf]; exact hgΛ
    · rw [← hgf]; exact hgz

/-- The hypothesis of `chainB_wirt_le` on the good event, for chains of length `≤ 3`. -/
private lemma L3_hG_sharp {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {U : Set (Idx D N → ℂ)} {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z U Γ₀ h)
    (K : ℝ) (hK : 1 ≤ K) (Q : Set (Matrix (Idx D N) (Idx D N) ℂ))
    (h1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ Q) (X : Set (Idx D N → ℂ))
    (hXU : X ⊆ U) (hQX : ∀ B ∈ Q, ∀ x ∈ X, Bᴴ *ᵥ x ∈ U) (l : List (L3_T D N))
    (hl2 : l.length ≤ 3) (hl : ∀ f ∈ l, f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2) :
    ∀ l' : List (L3_T D N), 1 ≤ l'.length → l'.length ≤ l.length + 1 →
      (∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) →
      ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB h l' *ᵥ y)‖ ≤ L3_Gs K Γ₀ z.im l'.length := by
  intro l' hl1 hl3 hl'
  exact L3_entry_sharp hΛ hz hΓ₀ hh hg K hK Q X hXU hQX l' hl1 (by omega)
    (L3_sub_factors h1 hK hl hl')

/-! ### Smoothness of the chains, the loops and the fluctuation term -/

/-- Entries of chains of the Hermitian part are smooth in the array. -/
private lemma L3_cd_chain {D N : ℕ} :
    ∀ l : List (L3_T D N), (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) → ∀ (k m : Idx D N)
      (n : ℕ), ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => chainB (symArr h) l k m) := by
  intro l
  induction l with
  | nil =>
    intro _ k m n
    simp only [L3_chain0]
    exact contDiff_const
  | cons a t ih =>
    intro hl k m n
    have ha := hl a List.mem_cons_self
    have ht := ih fun f hf => hl f (List.mem_cons_of_mem a hf)
    have e : ∀ h : Idx D N → Idx D N → ℂ, chainB (symArr h) (a :: t) k m =
        ∑ s, (∑ r, a.1 k r * res (Matrix.of (symArr h) + a.2.1) a.2.2 r s) *
          chainB (symArr h) t s m := by
      intro h
      simp [chainB, Matrix.mul_apply]
    simp only [e]
    exact ContDiff.sum fun s _ => (ContDiff.sum fun r _ => contDiff_const.mul
      (contDiff_res_symArr a.2.1 ha.1 a.2.2 ha.2 r s n)).mul (ht s m n)

/-- Forms of chains of the Hermitian part are smooth in the array. -/
private lemma L3_cd_form {D N : ℕ} (l : List (L3_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (x y : Idx D N → ℂ) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => star x ⬝ᵥ (chainB (symArr h) l *ᵥ y)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact ContDiff.sum fun k _ => ContDiff.sum fun m _ =>
    contDiff_const.mul ((L3_cd_chain l hl k m n).mul contDiff_const)

/-- Loops of chains of the Hermitian part are smooth in the array. -/
private lemma L3_cd_loop {D N : ℕ} (l : List (L3_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (symArr h) l)) := by
  simp only [ntr, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  exact ContDiff.sum fun k _ => contDiff_const.mul (L3_cd_chain l hl k k n)
/-- The factors of the chains of the fluctuation term: Hermitian `Λ` and `Im ζ ≠ 0`. -/
private lemma L3_lX_ok {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) :
    ∀ f ∈ L3_lX Λ B C z₁ z₂ z₃, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  simp only [L3_lX, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨hΛ, hz₃⟩
  · exact ⟨hΛ, hz₁⟩
  · exact ⟨hΛ, hz₂⟩

private lemma L3_l1_ok {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) (x : Fin D) (t : Fin 8) :
    ∀ f ∈ L3_l1 Λ C T z₁ z₂ z₃ x t, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  fin_cases t <;> simp [L3_l1] at hf <;> (try rcases hf with rfl | rfl) <;> (try subst hf) <;>
    first | exact ⟨hΛ, hz₁⟩ | exact ⟨hΛ, hz₂⟩ | exact ⟨hΛ, hz₃⟩

private lemma L3_l2_ok {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) (x : Fin D) (t : Fin 8) :
    ∀ f ∈ L3_l2 Λ B C T z₁ z₂ z₃ x t, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  fin_cases t <;> simp [L3_l2] at hf <;> (try rcases hf with rfl | rfl | rfl) <;>
    first | exact ⟨hΛ, hz₁⟩ | exact ⟨hΛ, hz₂⟩ | exact ⟨hΛ, hz₃⟩

/-- `X_{βα}` of the Hermitian part is smooth in the array. -/
private lemma L3_cd_X {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) (β α : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun h => L3_X Λ B C T z₁ z₂ z₃ (symArr h) β α) :=
  L3_cd_form _ (L3_lX_ok hΛ B C hz₁ hz₂ hz₃) _ _ n

/-- The polynomial `L3_Z` of the Hermitian part is smooth in the array. -/
private lemma L3_cd_Z {D N : ℕ} (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) (n : ℕ) : ContDiff ℝ n (fun h => L3_Z θ Λ B C T z₁ z₂ z₃ (symArr h)) := by
  unfold L3_Z
  exact ContDiff.sum fun t _ => ContDiff.sum fun x _ =>
    (contDiff_const.mul (L3_cd_loop _ (L3_l1_ok hΛ C T hz₁ hz₂ hz₃ x t) n)).mul
      (L3_cd_loop _ (L3_l2_ok hΛ B C T hz₁ hz₂ hz₃ x t) n)

/-- The integrand `X_{βα} Z^{p-1} Z̄^p` of the moment expansion. -/
private def L3_F {D N : ℕ} (θ : ℝ) (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (p : ℕ) (β α : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  L3_X Λ B C T z₁ z₂ z₃ h β α * (L3_Z θ Λ B C T z₁ z₂ z₃ h ^ (p - 1) *
    starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ h) ^ p)

private lemma L3_cd_F {D N : ℕ} (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) (p : ℕ) (β α : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun h => L3_F θ Λ B C T z₁ z₂ z₃ p β α (symArr h)) := by
  unfold L3_F
  exact (L3_cd_X hΛ B C T hz₁ hz₂ hz₃ β α n).mul (((L3_cd_Z θ hΛ B C T hz₁ hz₂ hz₃ n).pow _).mul
    ((Complex.conjCLE.contDiff.comp (L3_cd_Z θ hΛ B C T hz₁ hz₂ hz₃ n)).pow _))

/-! ### Linearity and products of the mixed derivatives -/

/-- `∂_w^a ∂_{w̄}^b (c f) = c ∂_w^a ∂_{w̄}^b f`. -/
private lemma L3_wirt_cmul {f : ℂ → ℂ} (hf : L3_Sm f) (c : ℂ) (a b : ℕ) :
    wirt a b (fun w => c * f w) = fun w => c * wirt a b f w := by
  unfold wirt
  rw [L3_der_iter_cmul L3_der_dWbar b c hf,
    L3_der_iter_cmul L3_der_dW a c (L3_der_iter_sm L3_der_dWbar b hf)]

/-- The mixed derivatives of a finite sum. -/
private lemma L3_wirt_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ i, L3_Sm (f i))
    (a b : ℕ) : wirt a b (fun w => ∑ i ∈ s, f i w) = fun w => ∑ i ∈ s, wirt a b (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [L3_wirt_const]
    funext w
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs : L3_Sm (fun w => ∑ j ∈ s, f j w) := fun n => ContDiff.sum fun j _ => hf j n
    have := L3_wirt_lin (hf i) hs 1 1 a b
    simp only [one_mul] at this
    rw [this, ih]

/-- The product bound for `a + b ≥ 1`: if `|f| ≤ F₀`, `|∂^{(a,b)} f| ≤ Γ^{a+b} F₁` and
`|g| ≤ G₀`, `|∂^{(a,b)} g| ≤ Γ^{a+b} G₁` for `1 ≤ a + b ≤ k`, then
`|∂^{(a,b)} (f g)| ≤ (2Γ)^{a+b} (F₀ G₁ + F₁ G₀ + F₁ G₁)`. -/
private lemma L3_LB2 {f g : ℂ → ℂ} (hf : L3_Sm f) (hg : L3_Sm g) (w : ℂ) (Γ F₀ F₁ G₀ G₁ : ℝ)
    (k : ℕ) (hΓ : 0 ≤ Γ) (hF₀ : ‖f w‖ ≤ F₀) (hG₀ : ‖g w‖ ≤ G₀) (hF₁0 : 0 ≤ F₁) (hG₁0 : 0 ≤ G₁)
    (hF : ∀ a b, 1 ≤ a + b → a + b ≤ k → ‖wirt a b f w‖ ≤ Γ ^ (a + b) * F₁)
    (hG : ∀ a b, 1 ≤ a + b → a + b ≤ k → ‖wirt a b g w‖ ≤ Γ ^ (a + b) * G₁) :
    ∀ a b, 1 ≤ a + b → a + b ≤ k →
      ‖wirt a b (fun y => f y * g y) w‖ ≤ (2 * Γ) ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁) := by
  intro a b hab hk
  have hF₀0 : 0 ≤ F₀ := (norm_nonneg _).trans hF₀
  have hG₀0 : 0 ≤ G₀ := (norm_nonneg _).trans hG₀
  have hS : 0 ≤ F₀ * G₁ + F₁ * G₀ + F₁ * G₁ := by positivity
  rw [L3_wirt_mul hf hg a b w]
  have key : ∀ a' ∈ Finset.range (a + 1), ∀ b' ∈ Finset.range (b + 1),
      ‖(a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f w * wirt (a - a') (b - b') g w)‖ ≤
        (a.choose a' : ℝ) * (b.choose b' : ℝ) *
          (Γ ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁)) := by
    intro a' ha' b' hb'
    have ha'' : a' ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha')
    have hb'' : b' ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : Γ ^ (a + b) = Γ ^ (a' + b') * Γ ^ (a - a' + (b - b')) := by
      rw [← pow_add]; congr 1; omega
    by_cases h0 : a' + b' = 0
    · have ha0 : a' = 0 := by omega
      have hb0 : b' = 0 := by omega
      subst ha0 hb0
      have h2 := hG a b (by omega) hk
      rw [Nat.sub_zero, Nat.sub_zero]
      calc ‖wirt 0 0 f w‖ * ‖wirt a b g w‖ ≤ F₀ * (Γ ^ (a + b) * G₁) :=
            mul_le_mul (by simpa [wirt] using hF₀) h2 (norm_nonneg _) hF₀0
        _ ≤ Γ ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁) := by
            have : 0 ≤ Γ ^ (a + b) := pow_nonneg hΓ _
            nlinarith [mul_nonneg hF₁0 hG₀0, mul_nonneg hF₁0 hG₁0, mul_nonneg this hF₁0,
              mul_nonneg (mul_nonneg this hF₁0) hG₀0, mul_nonneg (mul_nonneg this hF₁0) hG₁0]
    · have h1 := hF a' b' (by omega) (by omega)
      by_cases h0' : a - a' + (b - b') = 0
      · have ha0 : a - a' = 0 := by omega
        have hb0 : b - b' = 0 := by omega
        rw [ha0, hb0]
        have ea : a' = a := by omega
        have eb : b' = b := by omega
        subst ea eb
        calc ‖wirt a' b' f w‖ * ‖wirt 0 0 g w‖ ≤ (Γ ^ (a' + b') * F₁) * G₀ :=
              mul_le_mul h1 (by simpa [wirt] using hG₀) (norm_nonneg _) (by positivity)
          _ ≤ Γ ^ (a' + b') * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁) := by
              have : 0 ≤ Γ ^ (a' + b') := pow_nonneg hΓ _
              nlinarith [mul_nonneg this (mul_nonneg hF₀0 hG₁0),
                mul_nonneg this (mul_nonneg hF₁0 hG₁0)]
      · have h2 := hG (a - a') (b - b') (by omega) (by omega)
        rw [e]
        calc ‖wirt a' b' f w‖ * ‖wirt (a - a') (b - b') g w‖
            ≤ (Γ ^ (a' + b') * F₁) * (Γ ^ (a - a' + (b - b')) * G₁) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ ≤ Γ ^ (a' + b') * Γ ^ (a - a' + (b - b')) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁) := by
              have : 0 ≤ Γ ^ (a' + b') * Γ ^ (a - a' + (b - b')) := by positivity
              nlinarith [mul_nonneg this (mul_nonneg hF₀0 hG₁0),
                mul_nonneg this (mul_nonneg hF₁0 hG₀0)]
  calc ‖∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        (a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f w * wirt (a - a') (b - b') g w)‖
      ≤ ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        (a.choose a' : ℝ) * (b.choose b' : ℝ) *
          (Γ ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' ha' => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b' hb' => key a' ha' b' hb'))
    _ = (∑ a' ∈ Finset.range (a + 1), (a.choose a' : ℝ)) *
          (∑ b' ∈ Finset.range (b + 1), (b.choose b' : ℝ)) *
          (Γ ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁)) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_mul]
    _ = (2 * Γ) ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁) := by
        have ha2 : ∑ a' ∈ Finset.range (a + 1), (a.choose a' : ℝ) = 2 ^ a := by
          exact_mod_cast Nat.sum_range_choose a
        have hb2 : ∑ b' ∈ Finset.range (b + 1), (b.choose b' : ℝ) = 2 ^ b := by
          exact_mod_cast Nat.sum_range_choose b
        rw [ha2, hb2, mul_pow, pow_add]
        ring

/-! ### The deterministic setting and the jets of the integrand -/

/-- The deterministic setting of the expansion: `Λ` Hermitian, `Im z > 0`, `z₁, z₂, z₃ ∈ {z, z̄}`,
and the norms of the matrices of the chains bounded by `K ≥ 1`. -/
private structure L3_Set {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z z₁ z₂ z₃ : ℂ)
    (K : ℝ) : Prop where
  herm : Λ.IsHermitian
  hz : 0 < z.im
  h1 : L3_pm z z₁
  h2 : L3_pm z z₂
  h3 : L3_pm z z₃
  hK : 1 ≤ K
  hB : opNorm B ≤ K
  hC : opNorm C ≤ K
  hT : opNorm T ≤ K
  hTB : opNorm (T * B) ≤ K
  hTL : opNorm (T * (Λ - z₃ • 1)) ≤ K
  hTE : ∀ x, opNorm (T * Ea D N x) ≤ K
  hQ : ∀ q, opNorm (L3_Qf Λ B C T z₃ q) ≤ K

/-- The factors of the chain of `X`. -/
private lemma L3_Set.fX {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) :
    ∀ f ∈ L3_lX Λ B C z₁ z₂ z₃, f.1 ∈ ({1, B, C} : Set (Matrix (Idx D N) (Idx D N) ℂ)) ∧
      opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2 := by
  intro f hf
  simp only [L3_lX, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨Or.inl rfl, L3_opNorm_one.trans hs.hK, rfl, hs.h3⟩
  · exact ⟨Or.inr (Or.inl rfl), hs.hB, rfl, hs.h1⟩
  · exact ⟨Or.inr (Or.inr rfl), hs.hC, rfl, hs.h2⟩

/-- The factors of the loops of the terms. -/
private lemma L3_Set.fL {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) (x : Fin D) (t : Fin 8) :
    (∀ f ∈ L3_l1 Λ C T z₁ z₂ z₃ x t, f.1 ∈ L3_QL Λ B C T z₃ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
      L3_pm z f.2.2) ∧
    (∀ f ∈ L3_l2 Λ B C T z₁ z₂ z₃ x t, f.1 ∈ L3_QL Λ B C T z₃ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
      L3_pm z f.2.2) := by
  have hE : opNorm (Ea D N x) ≤ K := (L3_opNorm_Ea D N x).trans hs.hK
  have h1 : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ K := L3_opNorm_one.trans hs.hK
  have m1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ L3_QL Λ B C T z₃ := Or.inl (Or.inl (Or.inl rfl))
  have mT : T ∈ L3_QL Λ B C T z₃ := Or.inl (Or.inl (Or.inr (Or.inl rfl)))
  have mB : B ∈ L3_QL Λ B C T z₃ := Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
  have mC : C ∈ L3_QL Λ B C T z₃ := Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have mTB : T * B ∈ L3_QL Λ B C T z₃ :=
    Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have mTL : T * (Λ - z₃ • 1) ∈ L3_QL Λ B C T z₃ :=
    Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have mE : Ea D N x ∈ L3_QL Λ B C T z₃ := Or.inl (Or.inr ⟨x, rfl⟩)
  have mTE : T * Ea D N x ∈ L3_QL Λ B C T z₃ := Or.inr ⟨x, rfl⟩
  constructor
  · intro f hf
    fin_cases t <;> simp [L3_l1] at hf <;> (try rcases hf with rfl | rfl) <;> (try subst hf) <;>
      first
      | exact ⟨m1, h1, rfl, hs.h3⟩ | exact ⟨mE, hE, rfl, hs.h3⟩
      | exact ⟨mTE, hs.hTE x, rfl, hs.h1⟩ | exact ⟨mC, hs.hC, rfl, hs.h2⟩
      | exact ⟨mT, hs.hT, rfl, hs.h1⟩ | exact ⟨mTE, hs.hTE x, rfl, hs.h2⟩
      | exact ⟨mT, hs.hT, rfl, hs.h2⟩
  · intro f hf
    fin_cases t <;> simp [L3_l2] at hf <;> (try rcases hf with rfl | rfl | rfl) <;>
      (try subst hf) <;>
      first
      | exact ⟨mTB, hs.hTB, rfl, hs.h1⟩ | exact ⟨mC, hs.hC, rfl, hs.h2⟩
      | exact ⟨mB, hs.hB, rfl, hs.h1⟩ | exact ⟨mTL, hs.hTL, rfl, hs.h3⟩
      | exact ⟨mTE, hs.hTE x, rfl, hs.h3⟩ | exact ⟨mT, hs.hT, rfl, hs.h3⟩
      | exact ⟨mE, hE, rfl, hs.h3⟩ | exact ⟨m1, h1, rfl, hs.h3⟩

/-- The lengths of the loops of the terms: at most two and three, four resolvents in total. -/
private lemma L3_lens {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (x : Fin D) (t : Fin 8) :
    (L3_l1 Λ C T z₁ z₂ z₃ x t).length ≤ 2 ∧ 1 ≤ (L3_l2 Λ B C T z₁ z₂ z₃ x t).length ∧
      (L3_l2 Λ B C T z₁ z₂ z₃ x t).length ≤ 3 ∧
      (L3_l1 Λ C T z₁ z₂ z₃ x t).length + (L3_l2 Λ B C T z₁ z₂ z₃ x t).length ≤ 4 := by
  fin_cases t <;> simp [L3_l1, L3_l2]

/-- Every Hermitian array is in the good event with `Γ₀ = K² (1 + η⁻¹)`. -/
private lemma L3_good_crude {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    L3_good Λ z (L3_U Λ B C T z₃) (K ^ 2 * (1 + z.im⁻¹)) h := by
  intro ζ hζ u hu v hv
  obtain ⟨⟨q, k⟩, rfl⟩ := hu
  obtain ⟨⟨q', k'⟩, rfl⟩ := hv
  have hn : ∀ q k, Real.sqrt (L3_ns (L3_Qf Λ B C T z₃ q *ᵥ Pi.single k 1)) ≤ K := by
    intro q k
    have h1 := L3_mulVec_sq (L3_Qf Λ B C T z₃ q) (Pi.single k 1)
    have h2 : L3_ns (Pi.single k (1 : ℂ) : Idx D N → ℂ) = 1 := L3_single_sq k
    change L3_ns _ ≤ _ * L3_ns _ at h1
    rw [h2, mul_one] at h1
    refine Real.sqrt_le_iff.mpr ⟨by linarith [hs.hK], h1.trans ?_⟩
    have := hs.hQ q
    have h0 : 0 ≤ opNorm (L3_Qf Λ B C T z₃ q) := norm_nonneg _
    nlinarith
  have hG := L3_opNorm_res (Matrix.of h + Λ) (hh.add hs.herm) ζ (L3_pm_ne hs.hz hζ)
  rw [L3_pm_im hs.hz hζ] at hG
  refine (L3_form_le _ _ _).trans ?_
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  calc opNorm (res (Matrix.of h + Λ) ζ) *
        (Real.sqrt (L3_ns (L3_Qf Λ B C T z₃ q *ᵥ Pi.single k 1)) *
          Real.sqrt (L3_ns (L3_Qf Λ B C T z₃ q' *ᵥ Pi.single k' 1)))
      ≤ z.im⁻¹ * (K * K) := mul_le_mul hG (mul_le_mul (hn q k) (hn q' k') (Real.sqrt_nonneg _)
        (by linarith [hs.hK])) (by positivity) hi
    _ ≤ K ^ 2 * (1 + z.im⁻¹) := by nlinarith [hs.hK]

/-- The jet of `X_{βα}` along a slice at a point of the good event with constant `Γ₀`. -/
private lemma L3_jet_X {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h i j w)) (β α : Idx D N) (a b : ℕ) :
    ‖wirt a b (fun w' => L3_X Λ B C T z₁ z₂ z₃ (setEntry h i j w') β α) w‖ ≤
      ((3 + a + b : ℕ) : ℝ) ^ (a + b) * L3_Gs K Γ₀ z.im 1 ^ (a + b) * L3_Gs K Γ₀ z.im 3 := by
  have hX : ∀ k : Idx D N, (Pi.single k 1 : Idx D N → ℂ) ∈ L3_XX T := fun k =>
    Or.inl ⟨k, rfl⟩
  have := chainB_wirt_le (L3_lX Λ B C z₁ z₂ z₃) (by simp [L3_lX])
    (L3_lX_ok hs.herm B C (L3_pm_ne hs.hz hs.h1) (L3_pm_ne hs.hz hs.h2) (L3_pm_ne hs.hz hs.h3))
    h hh i j w (L3_Gs K Γ₀ z.im) (L3_Gs_mul K Γ₀ z.im) (L3_XX T) ⟨hX i, hX j⟩
    (L3_hG_sharp hs.herm hs.hz hΓ₀ (L3_slice_herm h hh i j w) hg K hs.hK {1, B, C} (Or.inl rfl)
      (L3_XX T) (L3_XX_U Λ B C T z₃) (L3_QX_ok Λ B C T z₃) (L3_lX Λ B C z₁ z₂ z₃)
      (by simp [L3_lX]) hs.fX) a b (Pi.single β 1) (hX β) (T *ᵥ Pi.single α 1) (Or.inr ⟨α, rfl⟩)
  have e : (L3_lX Λ B C z₁ z₂ z₃).length = 3 := rfl
  rw [e] at this
  exact this

/-- The jet of a loop of length `1`, `2` or `3` along a slice at a point of the good event. -/
private lemma L3_jet_loop {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h i j w)) (l : List (L3_T D N))
    (hl1 : 1 ≤ l.length) (hl2 : l.length ≤ 3)
    (hl : ∀ f ∈ l, f.1 ∈ L3_QL Λ B C T z₃ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2) :
    ‖ntr (chainB (setEntry h i j w) l)‖ ≤ L3_Gs K Γ₀ z.im l.length ∧
      ∀ a b, 1 ≤ a + b → ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') l)) w‖ ≤
        ((l.length + a + b : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) * N)⁻¹ *
          L3_Gs K Γ₀ z.im 1 ^ (a + b - 1) * L3_Gs K Γ₀ z.im (l.length + 1) := by
  have hX : ∀ k : Idx D N, (Pi.single k 1 : Idx D N → ℂ) ∈ L3_XL D N := fun k => ⟨k, rfl⟩
  have m1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ L3_QL Λ B C T z₃ := Or.inl (Or.inl (Or.inl rfl))
  have hok : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := fun f hf => by
    obtain ⟨-, -, h1, h2⟩ := hl f hf
    exact ⟨h1 ▸ hs.herm, L3_pm_ne hs.hz h2⟩
  have hG := L3_hG_sharp hs.herm hs.hz hΓ₀ (L3_slice_herm h hh i j w) hg K hs.hK
    (L3_QL Λ B C T z₃) m1 (L3_XL D N) (L3_XL_U Λ B C T z₃) (L3_QL_ok Λ B C T z₃) l hl2 hl
  constructor
  · have hd : ∀ k, ‖chainB (setEntry h i j w) l k k‖ ≤ L3_Gs K Γ₀ z.im l.length := by
      intro k
      have := hG l hl1 (by omega) (fun f hf => Or.inl hf) _ (hX k) _ (hX k)
      have e : star (Pi.single k (1 : ℂ)) ⬝ᵥ (chainB (setEntry h i j w) l *ᵥ Pi.single k 1) =
          chainB (setEntry h i j w) l k k := by
        simp [dotProduct, Matrix.mulVec, Pi.single_apply]
      rwa [e] at this
    have hc : (0 : ℝ) < Fintype.card (Idx D N) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    unfold ntr
    rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)).trans ?_
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hd k)
      (inv_nonneg.mpr hc.le)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc.ne',
      one_mul]
  · intro a b hab
    exact loopB_wirt_le l hl1 hok h hh i j w (L3_Gs K Γ₀ z.im) (L3_Gs_mul K Γ₀ z.im) (L3_XL D N)
      ⟨hX i, hX j⟩ hG a b hab

/-- The bound `V_n` on a loop of length `n` on the good event: `1` for `n = 0` and
`K^n Γ₀ (1 + η⁻¹)^{n-1}` otherwise. -/
private def L3_Lv (K Γ₀ η : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else K ^ n * Γ₀ * (1 + η⁻¹) ^ (n - 1)

/-- The bound `K^n (DN)⁻¹ η^{-n}` on the derivatives of a loop of length `n`. -/
private def L3_Ld (D N : ℕ) (K η : ℝ) (n : ℕ) : ℝ := K ^ n * (((D : ℝ) * N)⁻¹ * (η⁻¹) ^ n)

/-- The derivative scale `Γ_t = (3 + K_m) K Γ₀` of the jets up to order `K_m`. -/
private def L3_Gt (Km : ℕ) (K Γ₀ : ℝ) : ℝ := (3 + Km) * K * Γ₀

/-- `(n + a + b)^{a+b} (DN)⁻¹ Γ₁^{a+b-1} Γ_{n+1} ≤ Γ_t^{a+b} K^n (DN)⁻¹ η^{-n}` for `n ≤ 3`. -/
private lemma L3_hpow {D N : ℕ} {K Γ₀ η : ℝ} (hK0 : 0 ≤ K) (hΓ0 : 0 ≤ Γ₀) (hη : 0 < η)
    (Km n a b : ℕ) (hn : n ≤ 3) (hk1 : 1 ≤ a + b) (hkm : a + b ≤ Km) :
    ((n + a + b : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) * N)⁻¹ * L3_Gs K Γ₀ η 1 ^ (a + b - 1) *
      L3_Gs K Γ₀ η (n + 1) ≤ L3_Gt Km K Γ₀ ^ (a + b) * L3_Ld D N K η n := by
  have hi : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  obtain ⟨k, hk⟩ : ∃ k', a + b = k' + 1 := ⟨a + b - 1, by omega⟩
  have hnab : n + a + b = n + (k + 1) := by omega
  rw [hnab, hk]
  unfold L3_Gt L3_Gs L3_Ld
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_one, mul_one]
  have h1 : ((n + (k + 1) : ℕ) : ℝ) ≤ 3 + Km := by
    have : n + (k + 1) ≤ 3 + Km := by omega
    exact_mod_cast this
  have h2 : ((n + (k + 1) : ℕ) : ℝ) ^ (k + 1) ≤ (3 + Km) ^ (k + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
  have h3 : 0 ≤ (K * Γ₀) ^ (k + 1) * K ^ n * ((D : ℝ) * N)⁻¹ * η⁻¹ ^ n := by positivity
  calc ((n + (k + 1) : ℕ) : ℝ) ^ (k + 1) * ((D : ℝ) * N)⁻¹ * (K * Γ₀) ^ k *
        (K ^ (n + 1) * Γ₀ * η⁻¹ ^ n)
      = ((n + (k + 1) : ℕ) : ℝ) ^ (k + 1) *
          ((K * Γ₀) ^ (k + 1) * K ^ n * ((D : ℝ) * N)⁻¹ * η⁻¹ ^ n) := by ring
    _ ≤ (3 + Km) ^ (k + 1) * ((K * Γ₀) ^ (k + 1) * K ^ n * ((D : ℝ) * N)⁻¹ * η⁻¹ ^ n) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = ((3 + Km) * K * Γ₀) ^ (k + 1) * (K ^ n * (((D : ℝ) * N)⁻¹ * η⁻¹ ^ n)) := by
        rw [mul_pow, mul_pow, mul_pow]; ring

/-- The value and the jet of a loop of length `≤ 3` along a slice at a point of the good
event, in terms of `V_n` and `K^n (DN)⁻¹ η^{-n}`. -/
private lemma L3_loop_jet {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h i j w)) (Km : ℕ) (l : List (L3_T D N))
    (hl3 : l.length ≤ 3)
    (hl : ∀ f ∈ l, f.1 ∈ L3_QL Λ B C T z₃ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2) :
    ‖ntr (chainB (setEntry h i j w) l)‖ ≤ L3_Lv K Γ₀ z.im l.length ∧
      ∀ a b, 1 ≤ a + b → a + b ≤ Km →
        ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') l)) w‖ ≤
          L3_Gt Km K Γ₀ ^ (a + b) * L3_Ld D N K z.im l.length := by
  have hη : 0 < z.im := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  rcases Nat.lt_or_ge l.length 1 with h0 | h1
  · have hnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hD : NeZero D := ⟨by have := i.1.pos; omega⟩
    have hN : NeZero N := ⟨by have := i.2.pos; omega⟩
    subst hnil
    simp only [L3_chain0, L3_ntr_one, norm_one, List.length_nil, L3_Lv, ite_true]
    refine ⟨le_rfl, fun a b hab _ => ?_⟩
    rw [L3_wirt_const]
    have : ¬ (a = 0 ∧ b = 0) := by omega
    simp only [this, ite_false, norm_zero]
    unfold L3_Ld L3_Gt
    positivity
  · obtain ⟨hv, hd⟩ := L3_jet_loop hs hΓ0 h hh i j w hg l h1 hl3 hl
    have hn : l.length ≠ 0 := by omega
    refine ⟨hv.trans ?_, fun a b hab hkm => (hd a b hab).trans
      (L3_hpow hK0 hΓ0 hη Km _ a b hl3 hab hkm)⟩
    simp only [L3_Lv, hn, ite_false, L3_Gs]
    have : z.im⁻¹ ^ (l.length - 1) ≤ (1 + z.im⁻¹) ^ (l.length - 1) :=
      pow_le_pow_left₀ hi (by linarith) _
    gcongr

/-- `K^a s^c ≤ K^b s^d` for `K, s ≥ 1`, `a ≤ b`, `c ≤ d`. -/
private lemma L3_mono {K s : ℝ} (hK : 1 ≤ K) (hs : 1 ≤ s) {a b c d : ℕ} (hab : a ≤ b)
    (hcd : c ≤ d) : K ^ a * s ^ c ≤ K ^ b * s ^ d :=
  mul_le_mul (pow_le_pow_right₀ hK hab) (pow_le_pow_right₀ hs hcd) (by positivity)
    (by positivity)

/-- The bound `2 K⁴ Γ₀ (DN)⁻¹ (1 + η⁻¹)³ + K⁴ (DN)⁻² (1 + η⁻¹)⁴` on the products of the jets. -/
private def L3_P1 (D N : ℕ) (K Γ₀ η : ℝ) : ℝ :=
  2 * K ^ 4 * Γ₀ * (((D : ℝ) * N)⁻¹ * (1 + η⁻¹) ^ 3) +
    K ^ 4 * ((((D : ℝ) * N)⁻¹) ^ 2 * (1 + η⁻¹) ^ 4)

/-- For loop lengths `n₁ + n₂ ≤ 4`, `1 ≤ n₂ ≤ 3`:
`V_{n₁} D_{n₂} + D_{n₁} V_{n₂} + D_{n₁} D_{n₂} ≤ P₁`. -/
private lemma L3_prod_le {D N : ℕ} {K Γ₀ η : ℝ} (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η)
    (n₁ n₂ : ℕ) (h12 : n₁ + n₂ ≤ 4) (h2 : 1 ≤ n₂) (h3 : n₂ ≤ 3) :
    L3_Lv K Γ₀ η n₁ * L3_Ld D N K η n₂ + L3_Ld D N K η n₁ * L3_Lv K Γ₀ η n₂ +
      L3_Ld D N K η n₁ * L3_Ld D N K η n₂ ≤ L3_P1 D N K Γ₀ η := by
  set i := η⁻¹ with hi
  have hi0 : 0 ≤ i := inv_nonneg.mpr hη.le
  set s := 1 + i with hsd
  have hs1 : 1 ≤ s := by linarith
  set u := ((D : ℝ) * N)⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have his : ∀ n : ℕ, i ^ n ≤ s ^ n := fun n => pow_le_pow_left₀ hi0 (by linarith) n
  have hn2 : n₂ ≠ 0 := by omega
  have hV2 : L3_Lv K Γ₀ η n₂ = K ^ n₂ * Γ₀ * s ^ (n₂ - 1) := by simp [L3_Lv, hn2, hi, hsd]
  have hD : ∀ n, L3_Ld D N K η n ≤ u * (K ^ n * s ^ n) := by
    intro n
    unfold L3_Ld
    rw [← hi, ← hu]
    calc K ^ n * (u * i ^ n) ≤ K ^ n * (u * s ^ n) := by gcongr; linarith
      _ = _ := by ring
  have hD0 : ∀ n, 0 ≤ L3_Ld D N K η n := fun n => by unfold L3_Ld; positivity
  -- the term `V_{n₁} D_{n₂}`
  have tA : L3_Lv K Γ₀ η n₁ * L3_Ld D N K η n₂ ≤ K ^ 4 * Γ₀ * (u * s ^ 3) := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · subst h0
      simp only [L3_Lv, ite_true, one_mul]
      refine (hD n₂).trans ?_
      have := L3_mono hK hs1 (show n₂ ≤ 4 by omega) (show n₂ ≤ 3 by omega)
      calc u * (K ^ n₂ * s ^ n₂) ≤ u * (K ^ 4 * s ^ 3) := by gcongr
        _ = 1 * (K ^ 4 * (u * s ^ 3)) := by ring
        _ ≤ Γ₀ * (K ^ 4 * (u * s ^ 3)) := by gcongr
        _ = _ := by ring
    · have hn1 : n₁ ≠ 0 := by omega
      simp only [L3_Lv, hn1, ite_false]
      rw [← hi, ← hsd]
      have hpos : 0 ≤ K ^ n₁ * Γ₀ * s ^ (n₁ - 1) := by positivity
      calc K ^ n₁ * Γ₀ * s ^ (n₁ - 1) * L3_Ld D N K η n₂
          ≤ K ^ n₁ * Γ₀ * s ^ (n₁ - 1) * (u * (K ^ n₂ * s ^ n₂)) :=
            mul_le_mul_of_nonneg_left (hD n₂) hpos
        _ = Γ₀ * u * (K ^ (n₁ + n₂) * s ^ (n₁ - 1 + n₂)) := by rw [pow_add, pow_add]; ring
        _ ≤ Γ₀ * u * (K ^ 4 * s ^ 3) := by
            exact mul_le_mul_of_nonneg_left (L3_mono hK hs1 (by omega) (by omega))
              (by positivity)
        _ = _ := by ring
  -- the term `D_{n₁} V_{n₂}`
  have tB : L3_Ld D N K η n₁ * L3_Lv K Γ₀ η n₂ ≤ K ^ 4 * Γ₀ * (u * s ^ 3) := by
    rw [hV2]
    have hpos : 0 ≤ K ^ n₂ * Γ₀ * s ^ (n₂ - 1) := by positivity
    calc L3_Ld D N K η n₁ * (K ^ n₂ * Γ₀ * s ^ (n₂ - 1))
        ≤ u * (K ^ n₁ * s ^ n₁) * (K ^ n₂ * Γ₀ * s ^ (n₂ - 1)) :=
          mul_le_mul_of_nonneg_right (hD n₁) hpos
      _ = Γ₀ * u * (K ^ (n₁ + n₂) * s ^ (n₁ + (n₂ - 1))) := by rw [pow_add, pow_add]; ring
      _ ≤ Γ₀ * u * (K ^ 4 * s ^ 3) := by
          exact mul_le_mul_of_nonneg_left (L3_mono hK hs1 (by omega) (by omega)) (by positivity)
      _ = _ := by ring
  -- the term `D_{n₁} D_{n₂}`
  have tC : L3_Ld D N K η n₁ * L3_Ld D N K η n₂ ≤ K ^ 4 * (u ^ 2 * s ^ 4) := by
    calc L3_Ld D N K η n₁ * L3_Ld D N K η n₂ ≤ u * (K ^ n₁ * s ^ n₁) * (u * (K ^ n₂ * s ^ n₂)) :=
          mul_le_mul (hD n₁) (hD n₂) (hD0 _) (by positivity)
      _ = u ^ 2 * (K ^ (n₁ + n₂) * s ^ (n₁ + n₂)) := by rw [pow_add, pow_add]; ring
      _ ≤ u ^ 2 * (K ^ 4 * s ^ 4) :=
          mul_le_mul_of_nonneg_left (L3_mono hK hs1 h12 h12) (by positivity)
      _ = _ := by ring
  unfold L3_P1
  rw [← hi, ← hsd, ← hu]
  linarith

/-- For loop lengths `n₁ + n₂ ≤ 4`, `1 ≤ n₂ ≤ 3`: `V_{n₁} V_{n₂} ≤ K⁴ Γ₀² (1 + η⁻¹)²`. -/
private lemma L3_vv_le {K Γ₀ η : ℝ} (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η)
    (n₁ n₂ : ℕ) (h12 : n₁ + n₂ ≤ 4) (h2 : 1 ≤ n₂) (h3 : n₂ ≤ 3) :
    L3_Lv K Γ₀ η n₁ * L3_Lv K Γ₀ η n₂ ≤ K ^ 4 * Γ₀ ^ 2 * (1 + η⁻¹) ^ 2 := by
  set s := 1 + η⁻¹ with hsd
  have hs1 : 1 ≤ s := by have := inv_nonneg.mpr hη.le; linarith
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hn2 : n₂ ≠ 0 := by omega
  have hV2 : L3_Lv K Γ₀ η n₂ = K ^ n₂ * Γ₀ * s ^ (n₂ - 1) := by simp [L3_Lv, hn2, hsd]
  rw [hV2]
  rcases Nat.eq_zero_or_pos n₁ with h0 | h0
  · subst h0
    simp only [L3_Lv, ite_true, one_mul]
    calc K ^ n₂ * Γ₀ * s ^ (n₂ - 1) = Γ₀ * (K ^ n₂ * s ^ (n₂ - 1)) := by ring
      _ ≤ Γ₀ ^ 2 * (K ^ 4 * s ^ 2) :=
          mul_le_mul (le_self_pow₀ hΓ two_ne_zero) (L3_mono hK hs1 (by omega) (by omega))
            (by positivity) (by positivity)
      _ = _ := by ring
  · have hn1 : n₁ ≠ 0 := by omega
    simp only [L3_Lv, hn1, ite_false]
    rw [← hsd]
    calc K ^ n₁ * Γ₀ * s ^ (n₁ - 1) * (K ^ n₂ * Γ₀ * s ^ (n₂ - 1))
        = Γ₀ ^ 2 * (K ^ (n₁ + n₂) * s ^ (n₁ - 1 + (n₂ - 1))) := by rw [pow_add, pow_add]; ring
      _ ≤ Γ₀ ^ 2 * (K ^ 4 * s ^ 2) := by
          exact mul_le_mul_of_nonneg_left (L3_mono hK hs1 (by omega) (by omega)) (by positivity)
      _ = _ := by ring

/-- The sum `Σ_{t,x} |c_t|` of the coefficients of `L3_Z`. -/
private def L3_Cz (D : ℕ) (θ : ℝ) : ℝ := ∑ t : Fin 8, ∑ _x : Fin D, ‖L3_cf D θ t‖

private lemma L3_Cz_nonneg (D : ℕ) (θ : ℝ) : 0 ≤ L3_Cz D θ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The bound `Ψ_Z` on the derivatives of `L3_Z`, of order `Γ₀ (DN)⁻¹ η⁻³`. -/
private def L3_Pz (D N : ℕ) (θ K Γ₀ η : ℝ) : ℝ := L3_Cz D θ * L3_P1 D N K Γ₀ η

/-- The jet of `L3_Z` along a slice at a point of the good event, orders `1 ≤ a + b ≤ K_m`. -/
private lemma L3_jet_Z {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ}
    {z z₁ z₂ z₃ : ℂ} {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h i j w)) (Km : ℕ) :
    ∀ a b, 1 ≤ a + b → a + b ≤ Km →
      ‖wirt a b (fun w' => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w')) w‖ ≤
        (2 * L3_Gt Km K Γ₀) ^ (a + b) * L3_Pz D N θ K Γ₀ z.im := by
  intro a b hab hk
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hη : 0 < z.im := hs.hz
  have hK := hs.hK
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Γt := L3_Gt Km K Γ₀ with hΓt
  have hΓt0 : 0 ≤ Γt := by simp only [hΓt, L3_Gt]; positivity
  have hsm : ∀ l : List (L3_T D N), (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) →
      L3_Sm (fun w' => ntr (chainB (setEntry h i j w') l)) := fun l hl =>
    L3_sm_slice (F := fun h' => ntr (chainB h' l)) (fun n => L3_cd_loop l hl n) h hh i j
  have hsm1 := fun x t => hsm _ (L3_l1_ok hs.herm C T hz₁ hz₂ hz₃ x t)
  have hsm2 := fun x t => hsm _ (L3_l2_ok hs.herm B C T hz₁ hz₂ hz₃ x t)
  have hsmP : ∀ x t, L3_Sm (fun w' =>
      ntr (chainB (setEntry h i j w') (L3_l1 Λ C T z₁ z₂ z₃ x t)) *
        ntr (chainB (setEntry h i j w') (L3_l2 Λ B C T z₁ z₂ z₃ x t))) := fun x t =>
    L3_sm_mul (hsm1 x t) (hsm2 x t)
  have hZ : (fun w' => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w')) = fun w' => ∑ t : Fin 8,
      ∑ x : Fin D, L3_cf D θ t * (ntr (chainB (setEntry h i j w') (L3_l1 Λ C T z₁ z₂ z₃ x t)) *
        ntr (chainB (setEntry h i j w') (L3_l2 Λ B C T z₁ z₂ z₃ x t))) := by
    funext w'
    unfold L3_Z
    simp only [mul_assoc]
  rw [hZ, L3_wirt_sum _ _ (fun t => fun n => ContDiff.sum fun x _ =>
      (L3_sm_cmul _ (hsmP x t)) n) a b]
  simp only
  have hterm : ∀ t x, ‖wirt a b (fun w' => L3_cf D θ t *
      (ntr (chainB (setEntry h i j w') (L3_l1 Λ C T z₁ z₂ z₃ x t)) *
        ntr (chainB (setEntry h i j w') (L3_l2 Λ B C T z₁ z₂ z₃ x t)))) w‖ ≤
      ‖L3_cf D θ t‖ * ((2 * Γt) ^ (a + b) * L3_P1 D N K Γ₀ z.im) := by
    intro t x
    rw [L3_wirt_cmul (hsmP x t), norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨hl1, hl2a, hl2b, hl12⟩ := L3_lens Λ B C T z₁ z₂ z₃ x t
    obtain ⟨v1, d1⟩ := L3_loop_jet hs hΓ₀ h hh i j w hg Km _ (by omega) (hs.fL x t).1
    obtain ⟨v2, d2⟩ := L3_loop_jet hs hΓ₀ h hh i j w hg Km _ hl2b (hs.fL x t).2
    refine (L3_LB2 (hsm1 x t) (hsm2 x t) w Γt _ _ _ _ Km hΓt0 v1 v2
      (by unfold L3_Ld; have := inv_nonneg.mpr hη.le; positivity)
      (by unfold L3_Ld; have := inv_nonneg.mpr hη.le; positivity) d1 d2 a b hab hk).trans ?_
    exact mul_le_mul_of_nonneg_left (L3_prod_le hK hΓ₀ hη _ _ hl12 hl2a hl2b) (by positivity)
  calc ‖∑ t : Fin 8, wirt a b (fun w' => ∑ x : Fin D, L3_cf D θ t *
        (ntr (chainB (setEntry h i j w') (L3_l1 Λ C T z₁ z₂ z₃ x t)) *
          ntr (chainB (setEntry h i j w') (L3_l2 Λ B C T z₁ z₂ z₃ x t)))) w‖
      ≤ ∑ t : Fin 8, ∑ x : Fin D, ‖wirt a b (fun w' => L3_cf D θ t *
        (ntr (chainB (setEntry h i j w') (L3_l1 Λ C T z₁ z₂ z₃ x t)) *
          ntr (chainB (setEntry h i j w') (L3_l2 Λ B C T z₁ z₂ z₃ x t)))) w‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
        rw [L3_wirt_sum _ _ (fun x => L3_sm_cmul _ (hsmP x t)) a b]
        exact norm_sum_le _ _
    _ ≤ ∑ t : Fin 8, ∑ x : Fin D, ‖L3_cf D θ t‖ * ((2 * Γt) ^ (a + b) * L3_P1 D N K Γ₀ z.im) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun x _ => hterm t x
    _ = (2 * Γt) ^ (a + b) * L3_Pz D N θ K Γ₀ z.im := by
        simp only [L3_Pz, L3_Cz, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ => ?_
        ring

private lemma L3_Pz_nonneg {D N : ℕ} (θ : ℝ) {K Γ₀ η : ℝ} (hK : 0 ≤ K) (hΓ₀ : 0 ≤ Γ₀)
    (hη : 0 < η) : 0 ≤ L3_Pz D N θ K Γ₀ η := by
  have := L3_Cz_nonneg D θ
  have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  unfold L3_Pz L3_P1
  positivity

/-- The jet of the integrand `X_{βα} Z^{p-1} Z̄^p` along a slice at a point of the good event:
`|∂^{(a,b)}| ≤ (4 p Γ_t)^{a+b} Γ₃ (|Z| + Ψ_Z)^{2p-1}` for `a + b ≤ K_m`. -/
private lemma L3_jet_F {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h i j w)) (Km p : ℕ) (hp : 1 ≤ p)
    (β α : Idx D N) :
    ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h i j w')) w‖ ≤
        (4 * p * L3_Gt Km K Γ₀) ^ (a + b) * L3_Gs K Γ₀ z.im 3 *
          (‖L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1) := by
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Γt := L3_Gt Km K Γ₀ with hΓt
  have hΓt0 : 0 ≤ Γt := by simp only [hΓt, L3_Gt]; positivity
  set Pz := L3_Pz D N θ K Γ₀ z.im with hPz
  have hPz0 : 0 ≤ Pz := L3_Pz_nonneg θ hK0 hΓ0 hs.hz
  set u : ℂ → ℂ := fun w' => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w') with hu
  set X : ℂ → ℂ := fun w' => L3_X Λ B C T z₁ z₂ z₃ (setEntry h i j w') β α with hX
  have hsu : L3_Sm u := L3_sm_slice (F := fun h' => L3_Z θ Λ B C T z₁ z₂ z₃ h')
    (fun n => L3_cd_Z θ hs.herm B C T hz₁ hz₂ hz₃ n) h hh i j
  have hsX : L3_Sm X := L3_sm_slice (F := fun h' => L3_X Λ B C T z₁ z₂ z₃ h' β α)
    (fun n => L3_cd_X hs.herm B C T hz₁ hz₂ hz₃ β α n) h hh i j
  set c := ‖u w‖ + Pz with hc
  have hc0 : 0 ≤ c := by positivity
  have hGs3 : 0 ≤ L3_Gs K Γ₀ z.im 3 := by
    unfold L3_Gs
    have := inv_nonneg.mpr hs.hz.le
    positivity
  have hU : ∀ a b, a + b ≤ Km → ‖wirt a b u w‖ ≤ (2 * Γt) ^ (a + b) * c := by
    intro a b hab
    rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp only [wirt, Function.iterate_zero, id, add_zero, pow_zero, one_mul]
      linarith
    · refine (L3_jet_Z θ hs hΓ₀ h hh i j w hg Km a b h0 hab).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (u w)]) (by positivity)
  have hUc : ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => starRingEnd ℂ (u w')) w‖ ≤ (2 * Γt) ^ (a + b) * c := by
    intro a b hab
    rw [L3_wirt_conj hsu, Complex.norm_conj, add_comm a b]
    exact hU b a (by omega)
  have hP1 := L3_pow_jet hsu w (2 * Γt) c Km (by positivity) hc0 hU (p - 1)
  have hP2 := L3_pow_jet (L3_sm_conj hsu) w (2 * Γt) c Km (by positivity) hc0 hUc p
  have hΦ := L3_LB (L3_sm_pow hsu (p - 1)) (L3_sm_pow (L3_sm_conj hsu) p) w (2 * Γt)
    ((p - 1 : ℕ) : ℝ) (p : ℝ) (c ^ (p - 1)) (c ^ p) Km (by positivity) (Nat.cast_nonneg _)
    (pow_nonneg hc0 _) hP1 hP2
  have hXj : ∀ a b, a + b ≤ Km → ‖wirt a b X w‖ ≤
      (2 * Γt) ^ (a + b) * 1 ^ (a + b) * L3_Gs K Γ₀ z.im 3 := by
    intro a b hab
    refine (L3_jet_X hs hΓ0 h hh i j w hg β α a b).trans ?_
    rw [one_pow, mul_one, ← mul_pow]
    have hG1 : 0 ≤ L3_Gs K Γ₀ z.im 1 := by
      unfold L3_Gs
      have := inv_nonneg.mpr hs.hz.le
      positivity
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) hGs3
    simp only [hΓt, L3_Gt, L3_Gs, pow_one, Nat.sub_self, pow_zero, mul_one]
    have : ((3 + a + b : ℕ) : ℝ) ≤ 3 + Km := by exact_mod_cast (by omega : 3 + a + b ≤ 3 + Km)
    have h1 : 0 ≤ K * Γ₀ := by positivity
    have h2 : (0 : ℝ) ≤ Km := Nat.cast_nonneg _
    nlinarith
  have hF := L3_LB hsX (L3_sm_mul (L3_sm_pow hsu (p - 1)) (L3_sm_pow (L3_sm_conj hsu) p)) w
    (2 * Γt) 1 (((p - 1 : ℕ) : ℝ) + p) (L3_Gs K Γ₀ z.im 3) (c ^ (p - 1) * c ^ p) Km
    (by positivity) zero_le_one hGs3 hXj hΦ
  intro a b hab
  have e : (fun w' => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h i j w')) =
      fun y => X y * (u y ^ (p - 1) * starRingEnd ℂ (u y) ^ p) := by
    funext y; rfl
  rw [e]
  refine (hF a b hab).trans (le_of_eq ?_)
  have hp' : ((p - 1 : ℕ) : ℝ) = p - 1 := by
    rw [Nat.cast_sub hp]; simp
  have hc2 : c ^ (p - 1) * c ^ p = c ^ (2 * p - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hp', hc2]
  have : (2 * Γt) ^ (a + b) * (1 + ((p : ℝ) - 1 + p)) ^ (a + b) = (4 * p * Γt) ^ (a + b) := by
    rw [← mul_pow]; congr 1; ring
  rw [← this]
  ring

/-! ### The first and second derivatives of `X_{βα}` along its own slice -/

/-- `∂(G₂ B G₁ T) = -c (G₂ E G₂ B G₁ T + G₂ B G₁ E G₁ T)` along a Hermitian slice, for every
constant `B, T` and `G_i = G(z_i)`, with `E = E_{ij}` for `∂_w` and `E = E_{ji}` for `∂_{w̄}`. -/
private lemma L3_dm_Y {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (s : ℂ)
    (hs : s = Complex.I ∨ s = -Complex.I) :
    L3_dm s (fun w => L3_g Λ z₂ h i j w * B * L3_g Λ z₁ h i j w * T) = fun w =>
      (-L3_cc i j) • (L3_g Λ z₂ h i j w * (L3_E s i j * (L3_g Λ z₂ h i j w * (B *
        (L3_g Λ z₁ h i j w * T))))) +
      (-L3_cc i j) • (L3_g Λ z₂ h i j w * (B * (L3_g Λ z₁ h i j w * (L3_E s i j *
        (L3_g Λ z₁ h i j w * T))))) := by
  have d1 := L3_Dm.g hΛ hz₁ hh i j
  have d2 := L3_Dm.g hΛ hz₂ hh i j
  have dB := L3_Dm.const (ι := Idx D N) B
  have dT := L3_Dm.const (ι := Idx D N) T
  rw [L3_dm_mul s ((d2.mul dB).mul d1) dT, L3_dm_mul s (d2.mul dB) d1, L3_dm_mul s d2 dB,
    L3_dm_const, L3_dm_const, L3_dm_g hΛ hz₁ hh i j s hs, L3_dm_g hΛ hz₂ hh i j s hs]
  funext w
  simp only [Matrix.mul_zero, add_zero, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_assoc]

/-- `∂(G₁ T) = -c G₁ E G₁ T` along a Hermitian slice. -/
private lemma L3_dm_GT {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (T : Matrix (Idx D N) (Idx D N) ℂ) {ξ : ℂ} (hξ : ξ.im ≠ 0)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (s : ℂ)
    (hs : s = Complex.I ∨ s = -Complex.I) :
    L3_dm s (fun w => L3_g Λ ξ h i j w * T) = fun w =>
      (-L3_cc i j) • (L3_g Λ ξ h i j w * (L3_E s i j * (L3_g Λ ξ h i j w * T))) := by
  rw [L3_dm_mul s (L3_Dm.g hΛ hξ hh i j) (L3_Dm.const T), L3_dm_const, L3_dm_g hΛ hξ hh i j s hs]
  funext w
  simp only [Matrix.mul_zero, add_zero, Matrix.smul_mul, Matrix.mul_assoc]

/-- Products `A E B` with a constant `E` of matrix-valued functions with smooth entries have
smooth entries. -/
private lemma L3_Dm.mulE {ι : Type*} [Fintype ι] {A B : ℂ → Matrix ι ι ℂ} (hA : L3_Dm A)
    (hB : L3_Dm B) (E : Matrix ι ι ℂ) : L3_Dm (fun w => A w * (E * B w)) :=
  hA.mul ((L3_Dm.const E).mul hB)

/-- `∂(A E B) = ∂A E B + A E ∂B` for a constant `E`. -/
private lemma L3_dm_mulE {ι : Type*} [Fintype ι] (s : ℂ) {A B : ℂ → Matrix ι ι ℂ}
    (hA : L3_Dm A) (hB : L3_Dm B) (E : Matrix ι ι ℂ) :
    L3_dm s (fun w => A w * (E * B w)) = fun w =>
      L3_dm s A w * (E * B w) + A w * (E * L3_dm s B w) := by
  rw [L3_dm_mul s hA ((L3_Dm.const E).mul hB), L3_dm_mul s (L3_Dm.const E) hB, L3_dm_const]
  funext w
  simp only [Matrix.zero_mul, zero_add]

/-- `∂(G₃ B G₁ C G₂ T) = -c (G₃ E X + (G₃ B G₁) E (G₁ C G₂ T) + (G₃ B G₁ C G₂) E (G₂ T))` along
a Hermitian slice, for constant `B, C, T`, with `E = E_{ij}` for `∂_w` and `E_{ji}` for `∂_{w̄}`. -/
private lemma L3_dm_X {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) :
    L3_dm s (fun w => L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T) =
      fun w => (-L3_cc i j) • (L3_g Λ z₃ h i j w * (L3_E s i j *
          (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) * (L3_E s i j *
          (L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w) * (L3_E s i j *
          (L3_g Λ z₂ h i j w * T))) := by
  have d3 := L3_Dm.g hΛ hz₃ hh i j
  have dY := (((L3_Dm.g hΛ hz₁ hh i j).mul (L3_Dm.const C)).mul
    (L3_Dm.g hΛ hz₂ hh i j)).mul (L3_Dm.const T)
  have e : (fun w => L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T) =
      fun w => L3_g Λ z₃ h i j w * (B * (L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)) := by
    funext w; simp only [Matrix.mul_assoc]
  rw [e, L3_dm_mulE s d3 dY B, L3_dm_g hΛ hz₃ hh i j s hs, L3_dm_Y hΛ C T hz₂ hz₁ hh i j s hs]
  funext w
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, smul_add, Matrix.mul_assoc]
  abel

/-- The second entrywise derivatives of `X = G₃ B G₁ C G₂ T`: `c²` times the sum of the twelve
products `P E' Q E R` and `P E Q E' R` over the triples `(G₃, G₃, X)`, `(G₃, G₃BG₁, G₁CG₂T)`,
`(G₃, G₃BG₁CG₂, G₂T)`, `(G₃BG₁, G₁, G₁CG₂T)`, `(G₃BG₁, G₁CG₂, G₂T)`, `(G₃BG₁CG₂, G₂, G₂T)`. -/
private lemma L3_dm2_X {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hz₃ : z₃.im ≠ 0) {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (s s' : ℂ) (hs : s = Complex.I ∨ s = -Complex.I)
    (hs' : s' = Complex.I ∨ s' = -Complex.I) (w : ℂ) :
    L3_dm s' (L3_dm s (fun w => L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C *
      L3_g Λ z₂ h i j w * T)) w =
      (L3_cc i j ^ 2) • (
        L3_g Λ z₃ h i j w * (L3_E s' i j * (L3_g Λ z₃ h i j w * (L3_E s i j *
          (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)))) +
        L3_g Λ z₃ h i j w * (L3_E s i j * (L3_g Λ z₃ h i j w * (L3_E s' i j *
          (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)))) +
        L3_g Λ z₃ h i j w * (L3_E s i j * ((L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) *
          (L3_E s' i j * (L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)))) +
        L3_g Λ z₃ h i j w * (L3_E s' i j * ((L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) *
          (L3_E s i j * (L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)))) +
        L3_g Λ z₃ h i j w * (L3_E s i j * ((L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C *
          L3_g Λ z₂ h i j w) * (L3_E s' i j * (L3_g Λ z₂ h i j w * T)))) +
        L3_g Λ z₃ h i j w * (L3_E s' i j * ((L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C *
          L3_g Λ z₂ h i j w) * (L3_E s i j * (L3_g Λ z₂ h i j w * T)))) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) * (L3_E s' i j * (L3_g Λ z₁ h i j w *
          (L3_E s i j * (L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)))) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) * (L3_E s i j * (L3_g Λ z₁ h i j w *
          (L3_E s' i j * (L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w * T)))) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) * (L3_E s i j *
          ((L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w) * (L3_E s' i j * (L3_g Λ z₂ h i j w * T)))) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w) * (L3_E s' i j *
          ((L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w) * (L3_E s i j * (L3_g Λ z₂ h i j w * T)))) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w) * (L3_E s' i j *
          (L3_g Λ z₂ h i j w * (L3_E s i j * (L3_g Λ z₂ h i j w * T)))) +
        (L3_g Λ z₃ h i j w * B * L3_g Λ z₁ h i j w * C * L3_g Λ z₂ h i j w) * (L3_E s i j *
          (L3_g Λ z₂ h i j w * (L3_E s' i j * (L3_g Λ z₂ h i j w * T))))) := by
  set G₁ := L3_g Λ z₁ h i j with hG₁
  set G₂ := L3_g Λ z₂ h i j with hG₂
  set G₃ := L3_g Λ z₃ h i j with hG₃
  set E := L3_E s i j with hE
  set E' := L3_E s' i j with hE'
  set c := L3_cc i j with hc
  have d1 := L3_Dm.g hΛ hz₁ hh i j
  have d2 := L3_Dm.g hΛ hz₂ hh i j
  have d3 := L3_Dm.g hΛ hz₃ hh i j
  have dc : ∀ M : Matrix (Idx D N) (Idx D N) ℂ, L3_Dm (fun _ : ℂ => M) := L3_Dm.const
  have dX : L3_Dm (fun w => G₃ w * B * G₁ w * C * G₂ w * T) :=
    ((((d3.mul (dc B)).mul d1).mul (dc C)).mul d2).mul (dc T)
  have dP₂ : L3_Dm (fun w => G₃ w * B * G₁ w) := (d3.mul (dc B)).mul d1
  have dR₂ : L3_Dm (fun w => G₁ w * C * G₂ w * T) := ((d1.mul (dc C)).mul d2).mul (dc T)
  have dP₃ : L3_Dm (fun w => G₃ w * B * G₁ w * C * G₂ w) :=
    (((d3.mul (dc B)).mul d1).mul (dc C)).mul d2
  have dR₃ : L3_Dm (fun w => G₂ w * T) := d2.mul (dc T)
  have hX1 := L3_dm_X hΛ B C T hz₁ hz₂ hz₃ hh i j s hs
  have hX1' := L3_dm_X hΛ B C T hz₁ hz₂ hz₃ hh i j s' hs'
  have hP₃' := L3_dm_X hΛ B C 1 hz₁ hz₂ hz₃ hh i j s' hs'
  simp only [Matrix.mul_one] at hP₃'
  have hP₂' := L3_dm_Y hΛ B 1 hz₁ hz₃ hh i j s' hs'
  simp only [Matrix.mul_one] at hP₂'
  have hR₂' := L3_dm_Y hΛ C T hz₂ hz₁ hh i j s' hs'
  have hR₃' := L3_dm_GT hΛ T hz₂ hh i j s' hs'
  have hg3 := L3_dm_g hΛ hz₃ hh i j s' hs'
  have dT1 : L3_Dm (fun w => G₃ w * (E * (G₃ w * B * G₁ w * C * G₂ w * T))) := d3.mulE dX E
  have dT2 : L3_Dm (fun w => G₃ w * B * G₁ w * (E * (G₁ w * C * G₂ w * T))) := dP₂.mulE dR₂ E
  have dT3 : L3_Dm (fun w => G₃ w * B * G₁ w * C * G₂ w * (E * (G₂ w * T))) := dP₃.mulE dR₃ E
  rw [hX1, L3_dm_smul s' _ ((dT1.add dT2).add dT3), L3_dm_add s' (dT1.add dT2) dT3,
    L3_dm_add s' dT1 dT2, L3_dm_mulE s' d3 dX E, L3_dm_mulE s' dP₂ dR₂ E,
    L3_dm_mulE s' dP₃ dR₃ E, hg3, hX1', hP₂', hR₂', hP₃', hR₃']
  simp only [smul_add, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc]
  rw [show c ^ 2 = -c * -c by ring]
  abel

/-- `(P (E_{ij} Y))_{kl} = P_{ki} Y_{jl}`. -/
private lemma L3_single_entry' {ι : Type*} [Fintype ι] [DecidableEq ι] (P Y : Matrix ι ι ℂ)
    (i j k l : ι) : (P * (Matrix.single i j (1 : ℂ) * Y)) k l = P k i * Y j l := by
  rw [← Matrix.mul_assoc, L3_single_entry]

/-- The off-diagonal structure of `(P E₁ Q E₂ R)_{βα}` for `E₁, E₂ ∈ {E_{βα}, E_{αβ}}`: one of the
three factors is an off-diagonal entry `P_{βα}`, `Q_{αβ}` or `R_{βα}`. -/
private lemma L3_entry3 {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q R : Matrix ι ι ℂ)
    (α β : ι) (E₁ E₂ : Matrix ι ι ℂ)
    (h₁ : E₁ = Matrix.single β α 1 ∨ E₁ = Matrix.single α β 1)
    (h₂ : E₂ = Matrix.single β α 1 ∨ E₂ = Matrix.single α β 1) (mP mQ mR : ℝ)
    (hP : ∀ x ∈ ({α, β} : Set ι), ∀ y ∈ ({α, β} : Set ι), ‖P x y‖ ≤ mP)
    (hQ : ∀ x ∈ ({α, β} : Set ι), ∀ y ∈ ({α, β} : Set ι), ‖Q x y‖ ≤ mQ)
    (hR : ∀ x ∈ ({α, β} : Set ι), ∀ y ∈ ({α, β} : Set ι), ‖R x y‖ ≤ mR) :
    ‖(P * (E₁ * (Q * (E₂ * R)))) β α‖ ≤
      mQ * mR * ‖P β α‖ + mP * mR * ‖Q α β‖ + mP * mQ * ‖R β α‖ := by
  have hα : α ∈ ({α, β} : Set ι) := Or.inl rfl
  have hβ : β ∈ ({α, β} : Set ι) := Or.inr rfl
  have mP0 : 0 ≤ mP := (norm_nonneg _).trans (hP α hα α hα)
  have mQ0 : 0 ≤ mQ := (norm_nonneg _).trans (hQ α hα α hα)
  have mR0 : 0 ≤ mR := (norm_nonneg _).trans (hR α hα α hα)
  have t1 : 0 ≤ mQ * mR * ‖P β α‖ := by positivity
  have t2 : 0 ≤ mP * mR * ‖Q α β‖ := by positivity
  have t3 : 0 ≤ mP * mQ * ‖R β α‖ := by positivity
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    rw [L3_single_entry', L3_single_entry', norm_mul, norm_mul]
  · -- `P_{ββ} Q_{αβ} R_{αα}`
    have := mul_le_mul (hP β hβ β hβ) (hR α hα α hα) (norm_nonneg _) mP0
    nlinarith [norm_nonneg (Q α β), mul_nonneg (norm_nonneg (P β β)) (norm_nonneg (Q α β))]
  · -- `P_{ββ} Q_{αα} R_{βα}`
    have := mul_le_mul (hP β hβ β hβ) (hQ α hα α hα) (norm_nonneg _) mP0
    nlinarith [norm_nonneg (R β α), mul_nonneg (norm_nonneg (P β β)) (norm_nonneg (Q α α))]
  · -- `P_{βα} Q_{ββ} R_{αα}`
    have := mul_le_mul (hQ β hβ β hβ) (hR α hα α hα) (norm_nonneg _) mQ0
    nlinarith [norm_nonneg (P β α), mul_nonneg (norm_nonneg (Q β β)) (norm_nonneg (R α α))]
  · -- `P_{βα} Q_{βα} R_{βα}`
    have := mul_le_mul (hQ β hβ α hα) (hR β hβ α hα) (norm_nonneg _) mQ0
    nlinarith [norm_nonneg (P β α), mul_nonneg (norm_nonneg (Q β α)) (norm_nonneg (R β α))]

/-- The mixed derivatives of order two of matrix entries along a slice are entries of the
iterated entrywise derivatives. -/
private lemma L3_wirt2_dm (a b : ℕ) (hab : a + b = 2) : ∃ s s' : ℂ,
    (s = Complex.I ∨ s = -Complex.I) ∧ (s' = Complex.I ∨ s' = -Complex.I) ∧
      ∀ {ι : Type} (M : ℂ → Matrix ι ι ℂ) (k l : ι),
        wirt a b (fun w => M w k l) = fun w => L3_dm s' (L3_dm s M) w k l := by
  have e1 : ∀ {ι : Type} (M' : ℂ → Matrix ι ι ℂ) (k l : ι),
      dW (fun w => M' w k l) = fun w => L3_dm (-Complex.I) M' w k l := by
    intro ι M' k l; funext w; rw [L3_dm_dW]
  have e2 : ∀ {ι : Type} (M' : ℂ → Matrix ι ι ℂ) (k l : ι),
      dWbar (fun w => M' w k l) = fun w => L3_dm Complex.I M' w k l := by
    intro ι M' k l; funext w; rw [L3_dm_dWbar]
  rcases (show (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨-Complex.I, -Complex.I, Or.inr rfl, Or.inr rfl, fun M k l => ?_⟩
    simp only [wirt, Function.iterate_zero, id, Function.iterate_succ, Function.comp]
    rw [e1 M, e1 (L3_dm (-Complex.I) M)]
  · refine ⟨Complex.I, -Complex.I, Or.inl rfl, Or.inr rfl, fun M k l => ?_⟩
    simp only [wirt, Function.iterate_one]
    rw [e2 M, e1 (L3_dm Complex.I M)]
  · refine ⟨Complex.I, Complex.I, Or.inl rfl, Or.inl rfl, fun M k l => ?_⟩
    simp only [wirt, Function.iterate_zero, id, Function.iterate_succ, Function.comp]
    rw [e2 M, e2 (L3_dm Complex.I M)]

/-- `e_x^* M e_y = M_{xy}`. -/
private lemma L3_form_ee {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ) (x y : Idx D N) :
    star (Pi.single x (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single y 1) = M x y := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- `Σ_{k,l} |M_{kl}| ≤ card · F^{1/2}` when `|M|_{HS}² ≤ F`. -/
private lemma L3_sum_off {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (F : ℝ) (hF : L3_fs M ≤ F) :
    ∑ k, ∑ l, ‖M k l‖ ≤ (Fintype.card ι : ℝ) * Real.sqrt F := by
  have h1 := L3_sum_abs_sq M
  have h0 : 0 ≤ ∑ k, ∑ l, ‖M k l‖ := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hF0 : 0 ≤ F := (L3_fs_nonneg M).trans hF
  rw [← Real.sqrt_sq h0, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_left hF (sq_nonneg _)))

/-- The bounds on the good event used for the sums over the entries `(β, α)`: entries and
Hilbert–Schmidt norms of `G₁, G₂, G₃`, `G₃BG₁`, `G₁CG₂`, `G₃BG₁CG₂`, `X = G₃BG₁CG₂T`, `G₁CG₂T`
and `G₂T`. -/
private lemma L3_good_mats {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) :
    (∀ x y, ‖res (Matrix.of h + Λ) z₁ x y‖ ≤ K * Γ₀) ∧
    (∀ x y, ‖res (Matrix.of h + Λ) z₂ x y‖ ≤ K * Γ₀) ∧
    (∀ x y, ‖res (Matrix.of h + Λ) z₃ x y‖ ≤ K * Γ₀) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁) x y‖ ≤
      K ^ 2 * Γ₀ * z.im⁻¹) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂) x y‖ ≤
      K ^ 2 * Γ₀ * z.im⁻¹) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
      res (Matrix.of h + Λ) z₂) x y‖ ≤ K ^ 3 * Γ₀ * z.im⁻¹ ^ 2) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
      res (Matrix.of h + Λ) z₂ * T) x y‖ ≤ K ^ 3 * Γ₀ * z.im⁻¹ ^ 2) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) x y‖ ≤
      K ^ 2 * Γ₀ * z.im⁻¹) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₂ * T) x y‖ ≤ K * Γ₀) ∧
    L3_fs (res (Matrix.of h + Λ) z₁) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ ∧
    L3_fs (res (Matrix.of h + Λ) z₂) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ ∧
    L3_fs (res (Matrix.of h + Λ) z₃) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ ∧
    L3_fs (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁) ≤
      (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹) ^ 2 ∧
    L3_fs (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂) ≤
      (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹) ^ 2 ∧
    L3_fs (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
      res (Matrix.of h + Λ) z₂) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹)) ^ 2 ∧
    L3_fs (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
      res (Matrix.of h + Λ) z₂ * T) ≤
      (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2 ∧
    L3_fs (res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T) ≤
      (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2 ∧
    L3_fs (res (Matrix.of h + Λ) z₂ * T) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ * K ^ 2 := by
  have hX := hh.add hs.herm
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hXX : ∀ k : Idx D N, (Pi.single k 1 : Idx D N → ℂ) ∈ L3_XX T := fun k => Or.inl ⟨k, rfl⟩
  have hXT : ∀ k : Idx D N, T *ᵥ Pi.single k 1 ∈ L3_XX T := fun k => Or.inr ⟨k, rfl⟩
  have hent := fun l hl1 hl3 hl => L3_entry_sharp hs.herm hs.hz hΓ0 hh hg K hs.hK {1, B, C}
    (L3_XX T) (L3_XX_U Λ B C T z₃) (L3_QX_ok Λ B C T z₃) l hl1 hl3 hl
  have m1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ ({1, B, C} : Set (Matrix (Idx D N) (Idx D N) ℂ)) :=
    Or.inl rfl
  have hone : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ K := L3_opNorm_one.trans hs.hK
  have hl1 : ∀ ζ, L3_pm z ζ → ∀ f ∈ [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, ζ)],
      f.1 ∈ ({1, B, C} : Set (Matrix (Idx D N) (Idx D N) ℂ)) ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
        L3_pm z f.2.2 := by
    intro ζ hζ f hf
    rw [List.mem_singleton] at hf
    subst hf
    exact ⟨m1, hone, rfl, hζ⟩
  have hlB : ∀ f ∈ [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, z₃), (B, Λ, z₁)],
      f.1 ∈ ({1, B, C} : Set (Matrix (Idx D N) (Idx D N) ℂ)) ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
        L3_pm z f.2.2 := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨m1, hone, rfl, hs.h3⟩
    · exact ⟨Or.inr (Or.inl rfl), hs.hB, rfl, hs.h1⟩
  have hlC : ∀ f ∈ [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, z₁), (C, Λ, z₂)],
      f.1 ∈ ({1, B, C} : Set (Matrix (Idx D N) (Idx D N) ℂ)) ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
        L3_pm z f.2.2 := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨m1, hone, rfl, hs.h1⟩
    · exact ⟨Or.inr (Or.inr rfl), hs.hC, rfl, hs.h2⟩
  have e1 : ∀ ζ, chainB h [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, ζ)] =
      res (Matrix.of h + Λ) ζ := fun ζ => by rw [L3_chain1, Matrix.one_mul]
  have eB : chainB h [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, z₃), (B, Λ, z₁)] =
      res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ := by
    rw [L3_chain2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
  have eC : chainB h [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, z₁), (C, Λ, z₂)] =
      res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ := by
    rw [L3_chain2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
  have eX : chainB h (L3_lX Λ B C z₁ z₂ z₃) =
      res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ := by
    rw [L3_lX, L3_chain3]; simp only [Matrix.one_mul, Matrix.mul_assoc]
  have hGres : ∀ ζ, L3_pm z ζ → opNorm (res (Matrix.of h + Λ) ζ) ≤ z.im⁻¹ := fun ζ hζ => by
    have := L3_opNorm_res _ hX ζ (L3_pm_ne hη hζ)
    rwa [L3_pm_im hη hζ] at this
  have hfs : ∀ ζ, L3_pm z ζ → L3_fs (res (Matrix.of h + Λ) ζ) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ := by
    intro ζ hζ
    refine (L3_fs_res _ hX ζ (L3_pm_ne hη hζ)).trans ?_
    rw [L3_pm_im hη hζ]
    have hd : ∀ l, ‖res (Matrix.of h + Λ) ζ l l‖ / z.im ≤ Γ₀ * z.im⁻¹ := by
      intro l
      have := hg ζ hζ _ (L3_e_U Λ B C T z₃ l) _ (L3_e_U Λ B C T z₃ l)
      rw [L3_form_ee] at this
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right this hi
    refine (Finset.sum_le_sum fun l _ => hd l).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have nBG : opNorm (B * res (Matrix.of h + Λ) z₁) ≤ K * z.im⁻¹ :=
    (opNorm_mul_le _ _).trans (mul_le_mul hs.hB (hGres z₁ hs.h1) (norm_nonneg _) hK0)
  have nCG : opNorm (C * res (Matrix.of h + Λ) z₂) ≤ K * z.im⁻¹ :=
    (opNorm_mul_le _ _).trans (mul_le_mul hs.hC (hGres z₂ hs.h2) (norm_nonneg _) hK0)
  have nCGT : opNorm (C * res (Matrix.of h + Λ) z₂ * T) ≤ K * z.im⁻¹ * K :=
    (opNorm_mul_le _ _).trans (mul_le_mul nCG hs.hT (norm_nonneg _) (by positivity))
  have nBGCG : opNorm (B * res (Matrix.of h + Λ) z₁ * (C * res (Matrix.of h + Λ) z₂)) ≤
      K * z.im⁻¹ * (K * z.im⁻¹) :=
    (opNorm_mul_le _ _).trans (mul_le_mul nBG nCG (norm_nonneg _) (by positivity))
  have nBGCGT : opNorm (B * res (Matrix.of h + Λ) z₁ * (C * res (Matrix.of h + Λ) z₂ * T)) ≤
      K * z.im⁻¹ * (K * z.im⁻¹ * K) :=
    (opNorm_mul_le _ _).trans (mul_le_mul nBG nCGT (norm_nonneg _) (by positivity))
  refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_,
    fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_,
    hfs z₁ hs.h1, hfs z₂ hs.h2, hfs z₃ hs.h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hent _ (by simp) (by simp) (hl1 z₁ hs.h1) _ (hXX x) _ (hXX y)
    rw [e1, L3_form_ee] at this
    simpa [L3_Gs] using this
  · have := hent _ (by simp) (by simp) (hl1 z₂ hs.h2) _ (hXX x) _ (hXX y)
    rw [e1, L3_form_ee] at this
    simpa [L3_Gs] using this
  · have := hent _ (by simp) (by simp) (hl1 z₃ hs.h3) _ (hXX x) _ (hXX y)
    rw [e1, L3_form_ee] at this
    simpa [L3_Gs] using this
  · have := hent _ (by simp) (by simp) hlB _ (hXX x) _ (hXX y)
    rw [eB, L3_form_ee] at this
    simpa [L3_Gs] using this
  · have := hent _ (by simp) (by simp) hlC _ (hXX x) _ (hXX y)
    rw [eC, L3_form_ee] at this
    simpa [L3_Gs] using this
  · have := hent _ (by simp [L3_lX]) (by simp [L3_lX]) hs.fX _ (hXX x) _ (hXX y)
    rw [eX, L3_form_ee] at this
    simpa [L3_lX, L3_Gs] using this
  · have := hent _ (by simp [L3_lX]) (by simp [L3_lX]) hs.fX _ (hXX x) _ (hXT y)
    rw [eX, L3_form_single] at this
    simpa [L3_lX, L3_Gs] using this
  · have := hent _ (by simp) (by simp) hlC _ (hXX x) _ (hXT y)
    rw [eC, L3_form_single] at this
    simpa [L3_Gs] using this
  · have := hent _ (by simp) (by simp) (hl1 z₂ hs.h2) _ (hXX x) _ (hXT y)
    rw [e1, L3_form_single] at this
    simpa [L3_Gs] using this
  · rw [Matrix.mul_assoc]
    exact (L3_fs_mul_right _ _).trans (mul_le_mul (hfs z₃ hs.h3)
      (pow_le_pow_left₀ (norm_nonneg _) nBG 2) (sq_nonneg _) (by positivity))
  · rw [Matrix.mul_assoc]
    exact (L3_fs_mul_right _ _).trans (mul_le_mul (hfs z₁ hs.h1)
      (pow_le_pow_left₀ (norm_nonneg _) nCG 2) (sq_nonneg _) (by positivity))
  · have e : res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
        res (Matrix.of h + Λ) z₂ = res (Matrix.of h + Λ) z₃ *
          (B * res (Matrix.of h + Λ) z₁ * (C * res (Matrix.of h + Λ) z₂)) := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (L3_fs_mul_right _ _).trans (mul_le_mul (hfs z₃ hs.h3)
      (pow_le_pow_left₀ (norm_nonneg _) nBGCG 2) (sq_nonneg _) (by positivity))
  · have e : res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
        res (Matrix.of h + Λ) z₂ * T = res (Matrix.of h + Λ) z₃ *
          (B * res (Matrix.of h + Λ) z₁ * (C * res (Matrix.of h + Λ) z₂ * T)) := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (L3_fs_mul_right _ _).trans (mul_le_mul (hfs z₃ hs.h3)
      (pow_le_pow_left₀ (norm_nonneg _) nBGCGT 2) (sq_nonneg _) (by positivity))
  · have e : res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ * T =
        res (Matrix.of h + Λ) z₁ * (C * res (Matrix.of h + Λ) z₂ * T) := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (L3_fs_mul_right _ _).trans (mul_le_mul (hfs z₁ hs.h1)
      (pow_le_pow_left₀ (norm_nonneg _) nCGT 2) (sq_nonneg _) (by positivity))
  · exact (L3_fs_mul_right _ _).trans (mul_le_mul (hfs z₂ hs.h2)
      (pow_le_pow_left₀ (norm_nonneg _) hs.hT 2) (sq_nonneg _) (by positivity))

/-- The sum over `(β, α)` of `|(P E₁ Q E₂ R)_{βα}|`, `E_r ∈ {E_{βα}, E_{αβ}}`:
`≤ DN (m_Q m_R F_P^{1/2} + m_P m_R F_Q^{1/2} + m_P m_Q F_R^{1/2})`. -/
private lemma L3_triple_sum {D N : ℕ} (P Q R : Matrix (Idx D N) (Idx D N) ℂ)
    (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ)
    (h₁ : ∀ β α, E₁ β α = Matrix.single β α 1 ∨ E₁ β α = Matrix.single α β 1)
    (h₂ : ∀ β α, E₂ β α = Matrix.single β α 1 ∨ E₂ β α = Matrix.single α β 1)
    (mP mQ mR FP FQ FR : ℝ) (hP : ∀ x y, ‖P x y‖ ≤ mP) (hQ : ∀ x y, ‖Q x y‖ ≤ mQ)
    (hR : ∀ x y, ‖R x y‖ ≤ mR) (hFP : L3_fs P ≤ FP) (hFQ : L3_fs Q ≤ FQ)
    (hFR : L3_fs R ≤ FR) :
    ∑ β, ∑ α, ‖(P * (E₁ β α * (Q * (E₂ β α * R)))) β α‖ ≤
      (D * N : ℝ) * (mQ * mR * Real.sqrt FP + mP * mR * Real.sqrt FQ +
        mP * mQ * Real.sqrt FR) := by
  have mP0 : ∀ x : Idx D N, 0 ≤ mP := fun x => (norm_nonneg _).trans (hP x x)
  have mQ0 : ∀ x : Idx D N, 0 ≤ mQ := fun x => (norm_nonneg _).trans (hQ x x)
  have mR0 : ∀ x : Idx D N, 0 ≤ mR := fun x => (norm_nonneg _).trans (hR x x)
  have hcard : (Fintype.card (Idx D N) : ℝ) = D * N := by
    simp [Fintype.card_prod]
  have key : ∀ β α, ‖(P * (E₁ β α * (Q * (E₂ β α * R)))) β α‖ ≤
      mQ * mR * ‖P β α‖ + mP * mR * ‖Q α β‖ + mP * mQ * ‖R β α‖ := fun β α =>
    L3_entry3 P Q R α β _ _ (h₁ β α) (h₂ β α) mP mQ mR (fun x _ y _ => hP x y)
      (fun x _ y _ => hQ x y) (fun x _ y _ => hR x y)
  refine (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => key β α).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have sP := L3_sum_off P FP hFP
  have sQ := L3_sum_off Q FQ hFQ
  have sR := L3_sum_off R FR hFR
  rw [hcard] at sP sQ sR
  rw [Finset.sum_comm (f := fun β α => ‖Q α β‖)]
  rcases isEmpty_or_nonempty (Idx D N) with hE | ⟨⟨x⟩⟩
  · simp [Finset.univ_eq_empty]
    have : (D : ℝ) * N = 0 := by
      have := Fintype.card_eq_zero (α := Idx D N)
      rw [← hcard, this]; simp
    rw [this]; simp
  have := mP0 x; have := mQ0 x; have := mR0 x
  calc mQ * mR * (∑ β, ∑ α, ‖P β α‖) + mP * mR * (∑ β, ∑ α, ‖Q β α‖) +
        mP * mQ * ∑ β, ∑ α, ‖R β α‖
      ≤ mQ * mR * ((D * N : ℝ) * Real.sqrt FP) + mP * mR * ((D * N : ℝ) * Real.sqrt FQ) +
          mP * mQ * ((D * N : ℝ) * Real.sqrt FR) := by
        gcongr
    _ = _ := by ring

/-- The sum over `(β, α)` of the second derivatives of `X_{βα}` along its own slice on the good
event: `≤ 36 DN K⁵ Γ₀² η⁻² (DN Γ₀ η⁻¹)^{1/2}`. -/
private lemma L3_sum_d2X {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) (a b : ℕ) (hab : a + b = 2) :
    ∑ β, ∑ α, ‖wirt a b (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ ≤
      36 * ((D * N : ℝ) * (K ^ 5 * Γ₀ ^ 2 * z.im⁻¹ ^ 2 *
        Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) := by
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK := hs.hK
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  obtain ⟨mG1, mG2, mG3, mP2, mY2, mP3, mX, mR2, mR3, fG1, fG2, fG3, fP2, fY2, fP3, fX, fR2,
    fR3⟩ := L3_good_mats hs hΓ₀ h hh hg
  set G₁ := res (Matrix.of h + Λ) z₁ with hG₁
  set G₂ := res (Matrix.of h + Λ) z₂ with hG₂
  set G₃ := res (Matrix.of h + Λ) z₃ with hG₃
  set i := z.im⁻¹ with hidef
  set F1 := (D * N : ℝ) * Γ₀ * i with hF1
  have hF10 : 0 ≤ F1 := by positivity
  obtain ⟨s, s', hs1, hs2, hw⟩ := L3_wirt2_dm a b hab
  have hE : ∀ (s : ℂ), (s = Complex.I ∨ s = -Complex.I) → ∀ β α : Idx D N,
      L3_E s β α = Matrix.single β α 1 ∨ L3_E s β α = Matrix.single α β 1 := by
    intro s _ β α
    unfold L3_E
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hc : ∀ β α : Idx D N, ‖L3_cc β α ^ 2‖ ≤ 1 := by
    intro β α
    unfold L3_cc
    split_ifs <;> norm_num
  set E := fun β α : Idx D N => L3_E s β α with hEdef
  set E' := fun β α : Idx D N => L3_E s' β α with hE'def
  set X := G₃ * B * G₁ * C * G₂ * T with hX
  set P₂ := G₃ * B * G₁ with hP₂
  set R₂ := G₁ * C * G₂ * T with hR₂
  set P₃ := G₃ * B * G₁ * C * G₂ with hP₃
  set R₃ := G₂ * T with hR₃
  set Y₂ := G₁ * C * G₂ with hY₂
  have hpt : ∀ β α, ‖wirt a b (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ ≤
      ‖(G₃ * (E' β α * (G₃ * (E β α * X)))) β α‖ + ‖(G₃ * (E β α * (G₃ * (E' β α * X)))) β α‖ +
      ‖(G₃ * (E β α * (P₂ * (E' β α * R₂)))) β α‖ + ‖(G₃ * (E' β α * (P₂ * (E β α * R₂)))) β α‖ +
      ‖(G₃ * (E β α * (P₃ * (E' β α * R₃)))) β α‖ + ‖(G₃ * (E' β α * (P₃ * (E β α * R₃)))) β α‖ +
      ‖(P₂ * (E' β α * (G₁ * (E β α * R₂)))) β α‖ + ‖(P₂ * (E β α * (G₁ * (E' β α * R₂)))) β α‖ +
      ‖(P₂ * (E β α * (Y₂ * (E' β α * R₃)))) β α‖ + ‖(P₂ * (E' β α * (Y₂ * (E β α * R₃)))) β α‖ +
      ‖(P₃ * (E' β α * (G₂ * (E β α * R₃)))) β α‖ +
      ‖(P₃ * (E β α * (G₂ * (E' β α * R₃)))) β α‖ := by
    intro β α
    have e : (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) =
        fun w => (L3_g Λ z₃ h β α w * B * L3_g Λ z₁ h β α w * C * L3_g Λ z₂ h β α w * T) β α := by
      funext w; rw [L3_X_eq]; rfl
    rw [e, hw]
    simp only
    rw [L3_dm2_X hs.herm B C T hz₁ hz₂ hz₃ hh β α s s' hs1 hs2]
    have hself : ∀ ξ, L3_g Λ ξ h β α (h β α) = res (Matrix.of h + Λ) ξ := by
      intro ξ; simp only [L3_g, L3_setEntry_self h hh]
    simp only [hself, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc β α)).trans ?_
    refine (norm_add_le _ _).trans ?_
    gcongr
    iterate 9 (refine (norm_add_le _ _).trans ?_; gcongr)
    exact norm_add_le _ _
  have hEs := hE s hs1
  have hE's := hE s' hs2
  have sq : ∀ c : ℝ, 0 ≤ c → Real.sqrt (F1 * c ^ 2) = Real.sqrt F1 * c := fun c hc0 => by
    rw [Real.sqrt_mul hF10, Real.sqrt_sq hc0]
  have hS0 : 0 ≤ Real.sqrt F1 := Real.sqrt_nonneg _
  set V := Γ₀ ^ 2 * i ^ 2 * Real.sqrt F1 with hV
  have hV0 : 0 ≤ V := by positivity
  have k4 : K ^ 4 * V ≤ K ^ 5 * V :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by norm_num)) hV0
  -- the six triples, each with both orders of `E, E'`
  have t1 := fun (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ) h₁ h₂ =>
    L3_triple_sum G₃ G₃ X E₁ E₂ h₁ h₂ (K * Γ₀) (K * Γ₀) (K ^ 3 * Γ₀ * i ^ 2) F1 F1
      (F1 * (K * i * (K * i * K)) ^ 2) mG3 mG3 mX fG3 fG3 fX
  have t2 := fun (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ) h₁ h₂ =>
    L3_triple_sum G₃ P₂ R₂ E₁ E₂ h₁ h₂ (K * Γ₀) (K ^ 2 * Γ₀ * i) (K ^ 2 * Γ₀ * i) F1
      (F1 * (K * i) ^ 2) (F1 * (K * i * K) ^ 2) mG3 mP2 mR2 fG3 fP2 fR2
  have t3 := fun (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ) h₁ h₂ =>
    L3_triple_sum G₃ P₃ R₃ E₁ E₂ h₁ h₂ (K * Γ₀) (K ^ 3 * Γ₀ * i ^ 2) (K * Γ₀) F1
      (F1 * (K * i * (K * i)) ^ 2) (F1 * K ^ 2) mG3 mP3 mR3 fG3 fP3 fR3
  have t4 := fun (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ) h₁ h₂ =>
    L3_triple_sum P₂ G₁ R₂ E₁ E₂ h₁ h₂ (K ^ 2 * Γ₀ * i) (K * Γ₀) (K ^ 2 * Γ₀ * i)
      (F1 * (K * i) ^ 2) F1 (F1 * (K * i * K) ^ 2) mP2 mG1 mR2 fP2 fG1 fR2
  have t5 := fun (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ) h₁ h₂ =>
    L3_triple_sum P₂ Y₂ R₃ E₁ E₂ h₁ h₂ (K ^ 2 * Γ₀ * i) (K ^ 2 * Γ₀ * i) (K * Γ₀)
      (F1 * (K * i) ^ 2) (F1 * (K * i) ^ 2) (F1 * K ^ 2) mP2 mY2 mR3 fP2 fY2 fR3
  have t6 := fun (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ) h₁ h₂ =>
    L3_triple_sum P₃ G₂ R₃ E₁ E₂ h₁ h₂ (K ^ 3 * Γ₀ * i ^ 2) (K * Γ₀) (K * Γ₀)
      (F1 * (K * i * (K * i)) ^ 2) F1 (F1 * K ^ 2) mP3 mG2 mR3 fP3 fG2 fR3
  have a1 := t1 E' E hE's hEs
  have a2 := t1 E E' hEs hE's
  have a3 := t2 E E' hEs hE's
  have a4 := t2 E' E hE's hEs
  have a5 := t3 E E' hEs hE's
  have a6 := t3 E' E hE's hEs
  have a7 := t4 E' E hE's hEs
  have a8 := t4 E E' hEs hE's
  have a9 := t5 E E' hEs hE's
  have a10 := t5 E' E hE's hEs
  have a11 := t6 E' E hE's hEs
  have a12 := t6 E E' hEs hE's
  rw [sq _ (by positivity)] at a1 a2
  rw [sq _ (by positivity), sq _ (by positivity)] at a3 a4 a5 a6 a9 a10
  rw [sq _ (by positivity), sq _ (by positivity)] at a7 a8
  rw [sq _ (by positivity), sq _ (by positivity)] at a11 a12
  refine (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => hpt β α).trans ?_
  simp only [Finset.sum_add_distrib]
  have hDN : (0 : ℝ) ≤ D * N := by positivity
  have k4' : (D * N : ℝ) * (K ^ 4 * V) ≤ (D * N : ℝ) * (K ^ 5 * V) :=
    mul_le_mul_of_nonneg_left k4 hDN
  rw [hV] at k4'
  linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, k4']

/-! ### The cancellation at first order -/

/-- The entries of the profile `S_θ` as complex numbers. -/
private lemma L3_varProf_eq (D N : ℕ) (θ : ℝ) (r m : Idx D N) :
    (varProf D N θ r m : ℂ) = (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = m.1 then 1 else 0) +
      ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ := by
  unfold varProf
  push_cast
  split_ifs <;> simp

/-- The normalized trace as a sum over the diagonal. -/
private lemma L3_ntr_eq (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr M = ((D : ℂ) * N)⁻¹ * ∑ r, M r r := by
  simp [ntr, Matrix.trace, Fintype.card_prod]

/-- `S_θ(R)` is the diagonal matrix with entries `Σ_r (S_θ)_{rp} R_{rr}`. -/
private lemma L3_sTheta_apply (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ)
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
    rw [L3_ntr_eq]
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
    rw [e1, hblk, L3_ntr_eq]
    simp only [L3_varProf_eq, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∀ r : Idx D N, (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = p.1 then (1 : ℂ) else 0) * R r r =
        (θ : ℂ) * ((N : ℂ)⁻¹ * if r.1 = p.1 then R r r else 0) := by
      intro r
      split_ifs <;> ring
    simp only [e2]
    push_cast
    simp only [mul_assoc]
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

/-- `S_θ` has symmetric weights: `(S_θ)_{pq} = (S_θ)_{qp}`. -/
private lemma L3_varProf_symm (D N : ℕ) (θ : ℝ) (p q : Idx D N) :
    varProf D N θ p q = varProf D N θ q p := by
  unfold varProf
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

/-- `⟨S M⟩ = (DN)⁻¹ Σ_p S_{pp} M_{pp}` for a diagonal `S`. -/
private lemma L3_ntr_diag {D N : ℕ} (S M : Matrix (Idx D N) (Idx D N) ℂ)
    (hS : ∀ p q, p ≠ q → S p q = 0) :
    ntr (S * M) = ((D : ℂ) * N)⁻¹ * ∑ p, S p p * M p p := by
  rw [L3_ntr_eq]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single p (fun q _ hq => by rw [hS p q (Ne.symm hq),
    zero_mul]) (by simp)]

/-- The cancellation of the counterterms at first order (the second cumulants): on a Hermitian
array, `Σ_{β,α} ((S_θ)_{βα} ∂_w X_{βα} + δ_{βα} (S_θ)_{βα} ∂_{w̄} X_{βα})` along the slice
`(β, α)` at `w = h_{βα}` equals `-DN` times the three counterterms `L3_C`. -/
private lemma L3_cancel {D N : ℕ} (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) (B C T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ z₃ : ℂ}
    (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hz₃ : z₃.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    ∑ β, ∑ α, ((varProf D N θ β α : ℂ) *
        dW (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α) +
      (if β = α then (varProf D N θ β α : ℂ) else 0) *
        dWbar (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)) =
      -((D : ℂ) * N) * L3_C θ Λ B C T z₁ z₂ z₃ h := by
  set G₁ := res (Matrix.of h + Λ) z₁ with hG₁
  set G₂ := res (Matrix.of h + Λ) z₂ with hG₂
  set G₃ := res (Matrix.of h + Λ) z₃ with hG₃
  set X := G₃ * B * G₁ * C * G₂ * T with hX
  set P₂ := G₃ * B * G₁ with hP₂
  set R₂ := G₁ * C * G₂ * T with hR₂
  set P₃ := G₃ * B * G₁ * C * G₂ with hP₃
  set R₃ := G₂ * T with hR₃
  have hpt : ∀ β α, (varProf D N θ β α : ℂ) *
      dW (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α) +
      (if β = α then (varProf D N θ β α : ℂ) else 0) *
        dWbar (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α) =
      -((varProf D N θ β α : ℂ) * (G₃ β β * X α α + P₂ β β * R₂ α α + P₃ β β * R₃ α α)) := by
    intro β α
    have e : (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) =
        fun w => (L3_g Λ z₃ h β α w * B * L3_g Λ z₁ h β α w * C * L3_g Λ z₂ h β α w * T) β α := by
      funext w; rw [L3_X_eq]; rfl
    have hself : ∀ ξ, L3_g Λ ξ h β α (h β α) = res (Matrix.of h + Λ) ξ := by
      intro ξ; simp only [L3_g, L3_setEntry_self h hh]
    have d1 : dW (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α) =
        -L3_cc β α * (G₃ β β * X α α + P₂ β β * R₂ α α + P₃ β β * R₃ α α) := by
      rw [e, ← L3_dm_dW, L3_dm_X hΛ B C T hz₁ hz₂ hz₃ hh β α _ (Or.inr rfl)]
      have hne : -Complex.I ≠ Complex.I := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      simp only [hself, L3_E, hne, ite_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [L3_single_entry', L3_single_entry', L3_single_entry']
    have d2 : dWbar (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α) =
        -L3_cc β α * (G₃ β α * X β α + P₂ β α * R₂ β α + P₃ β α * R₃ β α) := by
      rw [e, ← L3_dm_dWbar, L3_dm_X hΛ B C T hz₁ hz₂ hz₃ hh β α _ (Or.inl rfl)]
      simp only [hself, L3_E, ite_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [L3_single_entry', L3_single_entry', L3_single_entry']
    rw [d1, d2]
    by_cases hβα : β = α
    · subst hβα
      simp only [L3_cc, ite_true]
      ring
    · simp only [L3_cc, hβα, ite_false]
      ring
  simp only [hpt]
  have hdiag : ∀ R : Matrix (Idx D N) (Idx D N) ℂ, ∀ p q, p ≠ q → sTheta D N θ R p q = 0 := by
    intro R p q hpq
    simp only [L3_sTheta_apply, hpq, ↓reduceIte]
  -- the three sums as normalized traces against `S_θ`
  have hS1 : ∑ β, ∑ α, (varProf D N θ β α : ℂ) * G₃ β β * X α α =
      ∑ α, sTheta D N θ G₃ α α * X α α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [L3_sTheta_apply, ↓reduceIte]
    rw [Finset.sum_mul]
  have hS : ∀ P R : Matrix (Idx D N) (Idx D N) ℂ,
      ∑ β, ∑ α, (varProf D N θ β α : ℂ) * P β β * R α α =
        ∑ β, sTheta D N θ R β β * P β β := by
    intro P R
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [L3_sTheta_apply, ↓reduceIte]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [L3_varProf_symm D N θ β α]
    ring
  have hC1 : ntr (G₁ * C * G₂ * T * (sTheta D N θ G₃ * G₃) * B) =
      ((D : ℂ) * N)⁻¹ * ∑ α, sTheta D N θ G₃ α α * X α α := by
    rw [← L3_ntr_diag _ _ (hdiag G₃)]
    rw [show G₁ * C * G₂ * T * (sTheta D N θ G₃ * G₃) * B =
      (G₁ * C * G₂ * T) * (sTheta D N θ G₃ * (G₃ * B)) by simp only [Matrix.mul_assoc],
      L3_ntr_comm]
    simp only [hX, hP₃, Matrix.mul_assoc]
  have hC2 : ntr (G₁ * sTheta D N θ R₂ * G₃ * B) =
      ((D : ℂ) * N)⁻¹ * ∑ β, sTheta D N θ R₂ β β * P₂ β β := by
    rw [← L3_ntr_diag _ _ (hdiag R₂)]
    rw [show G₁ * sTheta D N θ R₂ * G₃ * B = G₁ * (sTheta D N θ R₂ * (G₃ * B)) by
      simp only [Matrix.mul_assoc], L3_ntr_comm]
    simp only [hP₂, Matrix.mul_assoc]
  have hC3 : ntr (G₁ * C * G₂ * sTheta D N θ R₃ * G₃ * B) =
      ((D : ℂ) * N)⁻¹ * ∑ β, sTheta D N θ R₃ β β * P₃ β β := by
    rw [← L3_ntr_diag _ _ (hdiag R₃)]
    rw [show G₁ * C * G₂ * sTheta D N θ R₃ * G₃ * B = (G₁ * C * G₂) * (sTheta D N θ R₃ * (G₃ * B))
      by simp only [Matrix.mul_assoc], L3_ntr_comm]
    simp only [hP₃, Matrix.mul_assoc]
  have hDN : ((D : ℂ) * N) ≠ 0 ∨ ((D : ℂ) * N) = 0 := ne_or_eq _ _
  unfold L3_C
  rw [← hG₁, ← hG₂, ← hG₃]
  rw [show G₁ * C * G₂ * T = R₂ from rfl, show G₂ * T = R₃ from rfl, hC1, hC2, hC3, ← hS1,
    ← hS P₂ R₂, ← hS P₃ R₃]
  simp only [Finset.sum_neg_distrib, mul_add, Finset.sum_add_distrib, ← mul_assoc]
  rcases hDN with hDN | hDN
  · have hD : (D : ℂ) ≠ 0 := left_ne_zero_of_mul hDN
    have hN : (N : ℂ) ≠ 0 := right_ne_zero_of_mul hDN
    field_simp
    ring
  · have hD0 : D = 0 ∨ N = 0 := by
      rcases mul_eq_zero.mp hDN with h0 | h0
      · left; exact_mod_cast h0
      · right; exact_mod_cast h0
    have hE : IsEmpty (Idx D N) := by
      rcases hD0 with rfl | rfl
      · exact ⟨fun p => p.1.elim0⟩
      · exact ⟨fun p => p.2.elim0⟩
    simp [Finset.univ_eq_empty]

/-! ### The first derivatives of the loops and of the fluctuation term -/

/-- The matrix `W_r = (G_r B_{r+1} G_{r+1} ⋯ B_q G_q)(B₁ G₁ ⋯ B_r G_r)` of the first derivative of
a loop: `∂_w ⟨C⟩ = -c (DN)⁻¹ Σ_r (W_r)_{ji}`. -/
private def L3_W {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (l : List (L3_T D N)) (r : Fin l.length) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of h + (l.get r).2.1) (l.get r).2.2 * chainB h (l.drop (r + 1)) *
    chainB h (l.take (r + 1))

/-- The first Wirtinger derivatives of a loop along a Hermitian slice at `w = h_{ij}`. -/
private lemma L3_loop_d1 {D N : ℕ} (l : List (L3_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    dW (fun w => ntr (chainB (setEntry h i j w) l)) (h i j) =
        -L3_cc i j * (((D : ℂ) * N)⁻¹ * ∑ r : Fin l.length, L3_W h l r j i) ∧
      dWbar (fun w => ntr (chainB (setEntry h i j w) l)) (h i j) =
        -L3_cc i j * (((D : ℂ) * N)⁻¹ * ∑ r : Fin l.length, L3_W h l r i j) := by
  have hsm : ∀ k m, L3_Sm (fun w => chainB (setEntry h i j w) l k m) := fun k m =>
    L3_sm_slice (F := fun h' => chainB h' l k m) (fun n => L3_cd_chain l hl k m n) h hh i j
  have e : (fun w => ntr (chainB (setEntry h i j w) l)) =
      fun w => ((D : ℂ) * N)⁻¹ * ∑ k, chainB (setEntry h i j w) l k k := by
    funext w; rw [L3_ntr_eq]
  have hsum : L3_Sm (fun w => ∑ k, chainB (setEntry h i j w) l k k) := fun n =>
    ContDiff.sum fun k _ => hsm k k n
  have hw10 : ∀ f : ℂ → ℂ, wirt 1 0 f = dW f := fun f => rfl
  have hw01 : ∀ f : ℂ → ℂ, wirt 0 1 f = dWbar f := fun f => rfl
  have hD := L3_wirt_sum (Finset.univ : Finset (Idx D N))
    (fun k w => chainB (setEntry h i j w) l k k) (fun k => hsm k k)
  rw [e]
  constructor
  · rw [← hw10, L3_wirt_cmul hsum, hD 1 0]
    simp only [hw10]
    simp only [chainB_dW l hl h hh i j, L3_setEntry_self h hh]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [L3_W, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, L3_cc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [← hw01, L3_wirt_cmul hsum, hD 0 1]
    simp only [hw01]
    simp only [chainB_dWbar l hl h hh i j, L3_setEntry_self h hh]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [L3_W, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, L3_cc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- On the good event, `|G(ζ)|_{HS}² ≤ DN Γ₀ η⁻¹` for `ζ ∈ {z, z̄}`. -/
private lemma L3_fs_good {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) {ζ : ℂ}
    (hζ : L3_pm z ζ) : L3_fs (res (Matrix.of h + Λ) ζ) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ := by
  have hX := hh.add hs.herm
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  refine (L3_fs_res _ hX ζ (L3_pm_ne hη hζ)).trans ?_
  rw [L3_pm_im hη hζ]
  have hd : ∀ l, ‖res (Matrix.of h + Λ) ζ l l‖ / z.im ≤ Γ₀ * z.im⁻¹ := by
    intro l
    have := hg ζ hζ _ (L3_e_U Λ B C T z₃ l) _ (L3_e_U Λ B C T z₃ l)
    rw [L3_form_ee] at this
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right this hi
  refine (Finset.sum_le_sum fun l _ => hd l).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `Σ_{i,j} |∂ ⟨C⟩|² ≤ (DN)⁻² q² (DN Γ₀ η⁻¹) (K η⁻¹)^{2q}` for the first derivatives of a loop of
length `q` along the slices `(i, j)` at `w = h_{ij}`, on the good event. -/
private lemma L3_loop_d1_sq {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h)
    (l : List (L3_T D N)) (hl : ∀ f ∈ l, opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ L3_pm z f.2.2) :
    ∑ i, ∑ j, (‖dW (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2 +
        ‖dWbar (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2) ≤
      2 * ((((D : ℝ) * N)⁻¹) ^ 2 * (l.length : ℝ) ^ 2 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) *
        (K * z.im⁻¹) ^ (2 * l.length)) := by
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hok : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := fun f hf => by
    obtain ⟨-, h1, h2⟩ := hl f hf
    exact ⟨h1 ▸ hs.herm, L3_pm_ne hη h2⟩
  set n := l.length with hn
  set F := (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹) ^ (2 * n) with hF
  have hWfs : ∀ r : Fin n, L3_fs (L3_W h l r) ≤ F := by
    intro r
    have hr := hl (l.get r) (List.get_mem l r)
    have hG := L3_fs_good hs h hh hg hr.2.2
    have hdr : opNorm (chainB h (l.drop (r + 1))) ≤ (K * z.im⁻¹) ^ (l.drop (r + 1)).length :=
      L3_opNorm_chain Λ hs.herm z hη K hK0 h hh _ fun f hf => hl f (List.mem_of_mem_drop hf)
    have htk : opNorm (chainB h (l.take (r + 1))) ≤ (K * z.im⁻¹) ^ (l.take (r + 1)).length :=
      L3_opNorm_chain Λ hs.herm z hη K hK0 h hh _ fun f hf => hl f (List.mem_of_mem_take hf)
    have hlen : (l.drop (r + 1)).length + (l.take (r + 1)).length = n := by
      simp only [List.length_drop, List.length_take, hn]
      have := r.2
      omega
    unfold L3_W
    rw [hr.2.1]
    refine (L3_fs_mul_right _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (L3_fs_mul_right _ _) (sq_nonneg _)).trans ?_
    have hKe : 0 ≤ K * z.im⁻¹ := by positivity
    calc L3_fs (res (Matrix.of h + Λ) (l.get r).2.2) * opNorm (chainB h (l.drop (r + 1))) ^ 2 *
          opNorm (chainB h (l.take (r + 1))) ^ 2
        ≤ ((D * N : ℝ) * Γ₀ * z.im⁻¹) * ((K * z.im⁻¹) ^ (l.drop (r + 1)).length) ^ 2 *
            ((K * z.im⁻¹) ^ (l.take (r + 1)).length) ^ 2 := by
          have h1 := pow_le_pow_left₀ (norm_nonneg _) hdr 2
          have h2 := pow_le_pow_left₀ (norm_nonneg _) htk 2
          have h3 : 0 ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ := by positivity
          exact mul_le_mul (mul_le_mul hG h1 (sq_nonneg _) h3) h2 (sq_nonneg _)
            (by positivity)
      _ = F := by
          have hexp : (l.drop (r + 1)).length * 2 + (l.take (r + 1)).length * 2 = 2 * n := by
            omega
          rw [hF, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add, hexp]
  have hc : ∀ i j : Idx D N, ‖L3_cc i j‖ ≤ 1 := by
    intro i j; unfold L3_cc; split_ifs <;> norm_num
  have hDN : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  have hnorm : ∀ (i j : Idx D N) (v : Fin n → ℂ),
      ‖-L3_cc i j * (((D : ℂ) * N)⁻¹ * ∑ r, v r)‖ ^ 2 ≤
        (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r, ‖v r‖ ^ 2) := by
    intro i j v
    rw [norm_mul, norm_mul, norm_neg]
    have h1 : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [h1]
    have h2 : ‖∑ r, v r‖ ^ 2 ≤ (n : ℝ) * ∑ r, ‖v r‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ))
        (fun r => ‖v r‖)
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, one_mul] at this
      calc ‖∑ r, v r‖ ^ 2 ≤ (∑ r, ‖v r‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := this
    calc (‖L3_cc i j‖ * (((D : ℝ) * N)⁻¹ * ‖∑ r, v r‖)) ^ 2
        ≤ (1 * (((D : ℝ) * N)⁻¹ * ‖∑ r, v r‖)) ^ 2 := by
          gcongr
          exact hc i j
      _ = (((D : ℝ) * N)⁻¹) ^ 2 * ‖∑ r, v r‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hpt : ∀ i j, ‖dW (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2 +
      ‖dWbar (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2 ≤
      (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, ‖L3_W h l r j i‖ ^ 2) +
        (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, ‖L3_W h l r i j‖ ^ 2) := by
    intro i j
    obtain ⟨d1, d2⟩ := L3_loop_d1 l hok h hh i j
    rw [d1, d2]
    exact add_le_add (hnorm i j _) (hnorm i j _)
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsw : ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖L3_W h l r j i‖ ^ 2 =
      ∑ r : Fin n, L3_fs (L3_W h l r) := by
    calc ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖L3_W h l r j i‖ ^ 2
        = ∑ i : Idx D N, ∑ r : Fin n, ∑ j : Idx D N, ‖L3_W h l r j i‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r : Fin n, ∑ i : Idx D N, ∑ j : Idx D N, ‖L3_W h l r j i‖ ^ 2 := Finset.sum_comm
      _ = ∑ r : Fin n, ∑ j : Idx D N, ∑ i : Idx D N, ‖L3_W h l r j i‖ ^ 2 :=
          Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r : Fin n, L3_fs (L3_W h l r) := rfl
  have hsw' : ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖L3_W h l r i j‖ ^ 2 =
      ∑ r : Fin n, L3_fs (L3_W h l r) := by
    calc ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖L3_W h l r i j‖ ^ 2
        = ∑ i : Idx D N, ∑ r : Fin n, ∑ j : Idx D N, ‖L3_W h l r i j‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r : Fin n, ∑ i : Idx D N, ∑ j : Idx D N, ‖L3_W h l r i j‖ ^ 2 := Finset.sum_comm
      _ = ∑ r : Fin n, L3_fs (L3_W h l r) := rfl
  rw [hsw, hsw']
  have hsum : ∑ r : Fin n, L3_fs (L3_W h l r) ≤ n * F := by
    refine (Finset.sum_le_sum fun r _ => hWfs r).trans (le_of_eq ?_)
    simp
  have hF0 : 0 ≤ F := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hsum hn0
  calc (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, L3_fs (L3_W h l r)) +
        (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, L3_fs (L3_W h l r))
      ≤ (((D : ℝ) * N)⁻¹) ^ 2 * (n * (n * F)) + (((D : ℝ) * N)⁻¹) ^ 2 * (n * (n * F)) := by
        gcongr
    _ = _ := by rw [hF]; ring

/-- The sum `Σ_{t,x} |c_t|²`. -/
private def L3_Cz2 (D : ℕ) (θ : ℝ) : ℝ := ∑ t : Fin 8, ∑ _x : Fin D, ‖L3_cf D θ t‖ ^ 2

/-- Exchanging two pairs of finite sums. -/
private lemma L3_sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- `|Σ_{m} a_m|² ≤ |S| Σ_m |a_m|²`. -/
private lemma L3_sq_sum_le {κ : Type*} (s : Finset κ) (a : κ → ℂ) :
    ‖∑ m ∈ s, a m‖ ^ 2 ≤ (s.card : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun m => ‖a m‖)
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at this
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans this

/-- The values of the loops of the terms at a point of the good event. -/
private lemma L3_loop_vals {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) (k : Idx D N) (x : Fin D) (t : Fin 8) :
    ‖ntr (chainB h (L3_l1 Λ C T z₁ z₂ z₃ x t))‖ ≤
        L3_Lv K Γ₀ z.im (L3_l1 Λ C T z₁ z₂ z₃ x t).length ∧
      ‖ntr (chainB h (L3_l2 Λ B C T z₁ z₂ z₃ x t))‖ ≤
        L3_Lv K Γ₀ z.im (L3_l2 Λ B C T z₁ z₂ z₃ x t).length := by
  have hg' : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h k k (h k k)) := by
    rw [L3_setEntry_self h hh]; exact hg
  obtain ⟨hl1, -, hl2, -⟩ := L3_lens Λ B C T z₁ z₂ z₃ x t
  have v1 := (L3_loop_jet hs hΓ₀ h hh k k (h k k) hg' 0 _ (by omega) (hs.fL x t).1).1
  have v2 := (L3_loop_jet hs hΓ₀ h hh k k (h k k) hg' 0 _ hl2 (hs.fL x t).2).1
  rw [L3_setEntry_self h hh] at v1 v2
  exact ⟨v1, v2⟩

/-- The bound `2 (DN)⁻² n² (DN Γ₀ η⁻¹) (K η⁻¹)^{2n}` of `L3_loop_d1_sq` for a loop of length
`n`. -/
private def L3_Sd (D N : ℕ) (K Γ₀ η : ℝ) (n : ℕ) : ℝ :=
  2 * ((((D : ℝ) * N)⁻¹) ^ 2 * (n : ℝ) ^ 2 * ((D * N : ℝ) * Γ₀ * η⁻¹) * (K * η⁻¹) ^ (2 * n))

/-- The bound `36 K⁸ Γ₀³ (DN)⁻² DN (1 + η⁻¹)⁷` on the squared first derivatives of a term. -/
private def L3_S1 (D N : ℕ) (K Γ₀ η : ℝ) : ℝ :=
  36 * K ^ 8 * Γ₀ ^ 3 * ((((D : ℝ) * N)⁻¹) ^ 2 * (D * N : ℝ) * (1 + η⁻¹) ^ 7)

/-- For loop lengths `n₁ + n₂ ≤ 4`, `n₁ ≤ 3`, `1 ≤ n₂ ≤ 3`:
`V_{n₂}² S_{n₁} + V_{n₁}² S_{n₂} ≤ S₁`. -/
private lemma L3_sd_le {D N : ℕ} {K Γ₀ η : ℝ} (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η)
    (n₁ n₂ : ℕ) (h12 : n₁ + n₂ ≤ 4) (h1 : n₁ ≤ 3) (h2 : 1 ≤ n₂) (h3 : n₂ ≤ 3) :
    L3_Lv K Γ₀ η n₂ ^ 2 * L3_Sd D N K Γ₀ η n₁ + L3_Lv K Γ₀ η n₁ ^ 2 * L3_Sd D N K Γ₀ η n₂ ≤
      L3_S1 D N K Γ₀ η := by
  set i := η⁻¹ with hi
  have hi0 : 0 ≤ i := inv_nonneg.mpr hη.le
  set s := 1 + i with hsd
  have hs1 : 1 ≤ s := by linarith
  set w := (((D : ℝ) * N)⁻¹) ^ 2 * (D * N : ℝ) with hw
  have hw0 : 0 ≤ w := by positivity
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hsd' : ∀ n : ℕ, n ≤ 3 → L3_Sd D N K Γ₀ η n ≤ 18 * Γ₀ * w * (K ^ (2 * n) * s ^ (2 * n + 1)) := by
    intro n hn
    have hn2 : (n : ℝ) ^ 2 ≤ 9 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith
    have his : i ^ (2 * n + 1) ≤ s ^ (2 * n + 1) := pow_le_pow_left₀ hi0 (by linarith) _
    unfold L3_Sd
    rw [← hi]
    calc 2 * ((((D : ℝ) * N)⁻¹) ^ 2 * (n : ℝ) ^ 2 * ((D * N : ℝ) * Γ₀ * i) * (K * i) ^ (2 * n))
        = 2 * (n : ℝ) ^ 2 * Γ₀ * w * (K ^ (2 * n) * i ^ (2 * n + 1)) := by
          rw [hw, mul_pow, pow_succ]; ring
      _ ≤ 2 * 9 * Γ₀ * w * (K ^ (2 * n) * s ^ (2 * n + 1)) := by gcongr
      _ = _ := by ring
  have hLv : ∀ n : ℕ, n ≠ 0 → L3_Lv K Γ₀ η n ^ 2 = K ^ (2 * n) * Γ₀ ^ 2 * s ^ (2 * (n - 1)) := by
    intro n hn
    simp only [L3_Lv, hn, ite_false, ← hi, ← hsd]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
  have hn2 : n₂ ≠ 0 := by omega
  have hSd0 : ∀ n, 0 ≤ L3_Sd D N K Γ₀ η n := fun n => by unfold L3_Sd; positivity
  -- the first term
  have tA : L3_Lv K Γ₀ η n₂ ^ 2 * L3_Sd D N K Γ₀ η n₁ ≤ 18 * Γ₀ ^ 3 * w * (K ^ 8 * s ^ 7) := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · subst h0
      have : L3_Sd D N K Γ₀ η 0 = 0 := by simp [L3_Sd]
      rw [this, mul_zero]; positivity
    · rw [hLv n₂ hn2]
      calc K ^ (2 * n₂) * Γ₀ ^ 2 * s ^ (2 * (n₂ - 1)) * L3_Sd D N K Γ₀ η n₁
          ≤ K ^ (2 * n₂) * Γ₀ ^ 2 * s ^ (2 * (n₂ - 1)) *
              (18 * Γ₀ * w * (K ^ (2 * n₁) * s ^ (2 * n₁ + 1))) :=
            mul_le_mul_of_nonneg_left (hsd' n₁ h1) (by positivity)
        _ = 18 * Γ₀ ^ 3 * w * (K ^ (2 * n₂ + 2 * n₁) * s ^ (2 * (n₂ - 1) + (2 * n₁ + 1))) := by
            rw [pow_add, pow_add]; ring
        _ ≤ 18 * Γ₀ ^ 3 * w * (K ^ 8 * s ^ 7) :=
            mul_le_mul_of_nonneg_left (L3_mono hK hs1 (by omega) (by omega)) (by positivity)
  -- the second term
  have tB : L3_Lv K Γ₀ η n₁ ^ 2 * L3_Sd D N K Γ₀ η n₂ ≤ 18 * Γ₀ ^ 3 * w * (K ^ 8 * s ^ 7) := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · subst h0
      simp only [L3_Lv, ite_true, one_pow, one_mul]
      refine (hsd' n₂ h3).trans ?_
      have hΓ3 : Γ₀ ≤ Γ₀ ^ 3 := le_self_pow₀ hΓ (by norm_num)
      have hm := L3_mono hK hs1 (show 2 * n₂ ≤ 8 by omega) (show 2 * n₂ + 1 ≤ 7 by omega)
      have h18 : 18 * Γ₀ * w ≤ 18 * Γ₀ ^ 3 * w := by gcongr
      exact mul_le_mul h18 hm (by positivity) (by positivity)
    · rw [hLv n₁ (by omega)]
      calc K ^ (2 * n₁) * Γ₀ ^ 2 * s ^ (2 * (n₁ - 1)) * L3_Sd D N K Γ₀ η n₂
          ≤ K ^ (2 * n₁) * Γ₀ ^ 2 * s ^ (2 * (n₁ - 1)) *
              (18 * Γ₀ * w * (K ^ (2 * n₂) * s ^ (2 * n₂ + 1))) :=
            mul_le_mul_of_nonneg_left (hsd' n₂ h3) (by positivity)
        _ = 18 * Γ₀ ^ 3 * w * (K ^ (2 * n₁ + 2 * n₂) * s ^ (2 * (n₁ - 1) + (2 * n₂ + 1))) := by
            rw [pow_add, pow_add]; ring
        _ ≤ 18 * Γ₀ ^ 3 * w * (K ^ 8 * s ^ 7) :=
            mul_le_mul_of_nonneg_left (L3_mono hK hs1 (by omega) (by omega)) (by positivity)
  unfold L3_S1
  rw [← hi, ← hsd, ← hw]
  linarith

/-- The sum over the slices `(i, j)` of the squared first derivatives of `L3_Z` at `w = h_{ij}`
on the good event: `≤ 16 D (Σ |c_t|²) S₁`, which is of order `Γ₀³ (DN)⁻¹ η⁻⁷`. -/
private lemma L3_Z_d1_sq {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ}
    {z z₁ z₂ z₃ : ℂ} {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) :
    ∑ i, ∑ j, (‖dW (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) (h i j)‖ ^ 2 +
        ‖dWbar (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) (h i j)‖ ^ 2) ≤
      16 * D * L3_Cz2 D θ * L3_S1 D N K Γ₀ z.im := by
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hη := hs.hz
  have hK := hs.hK
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  -- the slices of the loops and their derivatives
  let L1 : Fin 8 → Fin D → Idx D N → Idx D N → ℂ → ℂ := fun t x i j w =>
    ntr (chainB (setEntry h i j w) (L3_l1 Λ C T z₁ z₂ z₃ x t))
  let L2 : Fin 8 → Fin D → Idx D N → Idx D N → ℂ → ℂ := fun t x i j w =>
    ntr (chainB (setEntry h i j w) (L3_l2 Λ B C T z₁ z₂ z₃ x t))
  let A1 : Fin 8 → Fin D → ℝ := fun t x => L3_Lv K Γ₀ z.im (L3_l1 Λ C T z₁ z₂ z₃ x t).length
  let A2 : Fin 8 → Fin D → ℝ := fun t x => L3_Lv K Γ₀ z.im (L3_l2 Λ B C T z₁ z₂ z₃ x t).length
  have hsm1 : ∀ t x i j, L3_Sm (L1 t x i j) := fun t x i j =>
    L3_sm_slice (F := fun h' => ntr (chainB h' (L3_l1 Λ C T z₁ z₂ z₃ x t)))
      (fun n => L3_cd_loop _ (L3_l1_ok hs.herm C T hz₁ hz₂ hz₃ x t) n) h hh i j
  have hsm2 : ∀ t x i j, L3_Sm (L2 t x i j) := fun t x i j =>
    L3_sm_slice (F := fun h' => ntr (chainB h' (L3_l2 Λ B C T z₁ z₂ z₃ x t)))
      (fun n => L3_cd_loop _ (L3_l2_ok hs.herm B C T hz₁ hz₂ hz₃ x t) n) h hh i j
  -- the loop derivative sums
  have hd1 : ∀ t x, ∑ i, ∑ j, (‖dW (L1 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L1 t x i j) (h i j)‖ ^ 2)
      ≤ L3_Sd D N K Γ₀ z.im (L3_l1 Λ C T z₁ z₂ z₃ x t).length := fun t x =>
    L3_loop_d1_sq hs hΓ0 h hh hg (L3_l1 Λ C T z₁ z₂ z₃ x t) (fun f hf => ((hs.fL x t).1 f hf).2)
  have hd2 : ∀ t x, ∑ i, ∑ j, (‖dW (L2 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L2 t x i j) (h i j)‖ ^ 2)
      ≤ L3_Sd D N K Γ₀ z.im (L3_l2 Λ B C T z₁ z₂ z₃ x t).length := fun t x =>
    L3_loop_d1_sq hs hΓ0 h hh hg (L3_l2 Λ B C T z₁ z₂ z₃ x t) (fun f hf => ((hs.fL x t).2 f hf).2)
  -- the derivative of `L3_Z` along a slice
  have hZd : ∀ i j, (‖dW (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) (h i j)‖ ^ 2 +
      ‖dWbar (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) (h i j)‖ ^ 2) ≤
      16 * D * ∑ t : Fin 8, ∑ x : Fin D, ‖L3_cf D θ t‖ ^ 2 *
        (A2 t x ^ 2 * (‖dW (L1 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L1 t x i j) (h i j)‖ ^ 2) +
          A1 t x ^ 2 * (‖dW (L2 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L2 t x i j) (h i j)‖ ^ 2)) := by
    intro i j
    have e : (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) = fun w =>
        ∑ p : Fin 8 × Fin D, L3_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w) := by
      funext w
      unfold L3_Z
      rw [Fintype.sum_prod_type]
      simp only [L1, L2, mul_assoc]
    have hsP : ∀ p : Fin 8 × Fin D, L3_Sm (fun w =>
        L3_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w)) := fun p =>
      L3_sm_cmul _ (L3_sm_mul (hsm1 _ _ i j) (hsm2 _ _ i j))
    have hD1 : ∀ (d : (ℂ → ℂ) → ℂ → ℂ), (d = dW ∨ d = dWbar) →
        d (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) (h i j) = ∑ p : Fin 8 × Fin D,
          L3_cf D θ p.1 * (d (L1 p.1 p.2 i j) (h i j) * L2 p.1 p.2 i j (h i j) +
            L1 p.1 p.2 i j (h i j) * d (L2 p.1 p.2 i j) (h i j)) := by
      rintro d (rfl | rfl)
      · have hs1 := L3_wirt_sum Finset.univ _ hsP 1 0
        have hc1 : ∀ p : Fin 8 × Fin D, wirt 1 0 (fun w =>
            L3_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w)) = fun w =>
            L3_cf D θ p.1 * wirt 1 0 (fun w => L1 p.1 p.2 i j w * L2 p.1 p.2 i j w) w :=
          fun p => L3_wirt_cmul (L3_sm_mul (hsm1 _ _ i j) (hsm2 _ _ i j)) _ 1 0
        simp only [hc1] at hs1
        simp only [wirt, Function.iterate_one, Function.iterate_zero, id_eq] at hs1
        rw [e, hs1]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [(dW_mul ((hsm1 _ _ i j).diff _) ((hsm2 _ _ i j).diff _)).1]
      · have hs1 := L3_wirt_sum Finset.univ _ hsP 0 1
        have hc1 : ∀ p : Fin 8 × Fin D, wirt 0 1 (fun w =>
            L3_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w)) = fun w =>
            L3_cf D θ p.1 * wirt 0 1 (fun w => L1 p.1 p.2 i j w * L2 p.1 p.2 i j w) w :=
          fun p => L3_wirt_cmul (L3_sm_mul (hsm1 _ _ i j) (hsm2 _ _ i j)) _ 0 1
        simp only [hc1] at hs1
        simp only [wirt, Function.iterate_one, Function.iterate_zero, id_eq] at hs1
        rw [e, hs1]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [(dW_mul ((hsm1 _ _ i j).diff _) ((hsm2 _ _ i j).diff _)).2]
    have hv : ∀ p : Fin 8 × Fin D, ‖L1 p.1 p.2 i j (h i j)‖ ≤ A1 p.1 p.2 ∧
        ‖L2 p.1 p.2 i j (h i j)‖ ≤ A2 p.1 p.2 := by
      intro p
      simp only [L1, L2, A1, A2, L3_setEntry_self h hh]
      exact L3_loop_vals hs hΓ₀ h hh hg i p.2 p.1
    have hbd : ∀ (d : (ℂ → ℂ) → ℂ → ℂ), (d = dW ∨ d = dWbar) →
        ‖d (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)) (h i j)‖ ^ 2 ≤
          8 * D * ∑ p : Fin 8 × Fin D, ‖L3_cf D θ p.1‖ ^ 2 *
            (2 * (A2 p.1 p.2 ^ 2 * ‖d (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
              A1 p.1 p.2 ^ 2 * ‖d (L2 p.1 p.2 i j) (h i j)‖ ^ 2)) := by
      intro d hd
      rw [hD1 d hd]
      refine (L3_sq_sum_le _ _).trans ?_
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      push_cast
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (by positivity)
      rw [norm_mul, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      obtain ⟨v1, v2⟩ := hv p
      have h1 : ‖d (L1 p.1 p.2 i j) (h i j) * L2 p.1 p.2 i j (h i j)‖ ≤
          ‖d (L1 p.1 p.2 i j) (h i j)‖ * A2 p.1 p.2 := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left v2 (norm_nonneg _)
      have h2 : ‖L1 p.1 p.2 i j (h i j) * d (L2 p.1 p.2 i j) (h i j)‖ ≤
          A1 p.1 p.2 * ‖d (L2 p.1 p.2 i j) (h i j)‖ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right v1 (norm_nonneg _)
      have h3 := (norm_add_le _ _).trans (add_le_add h1 h2)
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      refine h4.trans ?_
      nlinarith [sq_nonneg (‖d (L1 p.1 p.2 i j) (h i j)‖ * A2 p.1 p.2 -
        A1 p.1 p.2 * ‖d (L2 p.1 p.2 i j) (h i j)‖)]
    have b1 := hbd dW (Or.inl rfl)
    have b2 := hbd dWbar (Or.inr rfl)
    rw [← Fintype.sum_prod_type (f := fun p : Fin 8 × Fin D => ‖L3_cf D θ p.1‖ ^ 2 *
      (A2 p.1 p.2 ^ 2 * (‖dW (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
        ‖dWbar (L1 p.1 p.2 i j) (h i j)‖ ^ 2) +
        A1 p.1 p.2 ^ 2 * (‖dW (L2 p.1 p.2 i j) (h i j)‖ ^ 2 +
          ‖dWbar (L2 p.1 p.2 i j) (h i j)‖ ^ 2)))]
    have : 8 * (D : ℝ) * (∑ p : Fin 8 × Fin D, ‖L3_cf D θ p.1‖ ^ 2 *
          (2 * (A2 p.1 p.2 ^ 2 * ‖dW (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
            A1 p.1 p.2 ^ 2 * ‖dW (L2 p.1 p.2 i j) (h i j)‖ ^ 2))) +
        8 * (D : ℝ) * ∑ p : Fin 8 × Fin D, ‖L3_cf D θ p.1‖ ^ 2 *
          (2 * (A2 p.1 p.2 ^ 2 * ‖dWbar (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
            A1 p.1 p.2 ^ 2 * ‖dWbar (L2 p.1 p.2 i j) (h i j)‖ ^ 2)) =
        16 * D * ∑ p : Fin 8 × Fin D, ‖L3_cf D θ p.1‖ ^ 2 *
          (A2 p.1 p.2 ^ 2 * (‖dW (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
            ‖dWbar (L1 p.1 p.2 i j) (h i j)‖ ^ 2) +
            A1 p.1 p.2 ^ 2 * (‖dW (L2 p.1 p.2 i j) (h i j)‖ ^ 2 +
              ‖dWbar (L2 p.1 p.2 i j) (h i j)‖ ^ 2)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    linarith
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hZd i j).trans ?_
  set F : Fin 8 → Fin D → Idx D N → Idx D N → ℝ := fun t x i j => ‖L3_cf D θ t‖ ^ 2 *
    (A2 t x ^ 2 * (‖dW (L1 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L1 t x i j) (h i j)‖ ^ 2) +
      A1 t x ^ 2 * (‖dW (L2 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L2 t x i j) (h i j)‖ ^ 2)) with hF
  have hswap : ∑ i, ∑ j, (16 * (D : ℝ) * ∑ t, ∑ x, F t x i j) =
      16 * (D : ℝ) * ∑ t, ∑ x, ∑ i, ∑ j, F t x i j := by
    rw [← L3_sum4_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hswap, mul_assoc (16 * (D : ℝ)) (L3_Cz2 D θ)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold L3_Cz2
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [hF, ← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hd1' := hd1 t x
  have hd2' := hd2 t x
  simp only [Finset.sum_add_distrib] at hd1' hd2'
  obtain ⟨hl1, hl2a, hl2b, hl12⟩ := L3_lens Λ B C T z₁ z₂ z₃ x t
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left hd1' (sq_nonneg _))
    (mul_le_mul_of_nonneg_left hd2' (sq_nonneg _))) ?_
  exact L3_sd_le hK hΓ₀ hη _ _ hl12 (by omega) hl2a hl2b

private lemma L3_dPhi {u : ℂ → ℂ} (hu : L3_Sm u) (w : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    ‖dW (fun y => u y ^ (p - 1) * starRingEnd ℂ (u y) ^ p) w‖ +
        ‖dWbar (fun y => u y ^ (p - 1) * starRingEnd ℂ (u y) ^ p) w‖ ≤
      2 * (2 * p - 1) * ‖u w‖ ^ (2 * p - 2) * (‖dW u w‖ + ‖dWbar u w‖) := by
  set β := ‖dW u w‖ + ‖dWbar u w‖ with hβ
  have hβ1 : ‖dW u w‖ ≤ β := by linarith [norm_nonneg (dWbar u w)]
  have hβ2 : ‖dWbar u w‖ ≤ β := by linarith [norm_nonneg (dW u w)]
  have hβ0 : 0 ≤ β := by positivity
  have huc : L3_Sm (fun y => starRingEnd ℂ (u y)) := L3_sm_conj hu
  have hc1 : ‖dW (fun y => starRingEnd ℂ (u y)) w‖ ≤ β := by
    rw [(dW_conj (hu.diff w)).1, Complex.norm_conj]; exact hβ2
  have hc2 : ‖dWbar (fun y => starRingEnd ℂ (u y)) w‖ ≤ β := by
    rw [(dW_conj (hu.diff w)).2, Complex.norm_conj]; exact hβ1
  obtain ⟨a1, a2⟩ := L3_pow_d1 hu w ‖u w‖ β le_rfl hβ1 hβ2 (p - 1)
  obtain ⟨b1, b2⟩ := L3_pow_d1 huc w ‖u w‖ β (by rw [Complex.norm_conj]) hc1 hc2 p
  have hA := L3_sm_pow hu (p - 1)
  have hB := L3_sm_pow huc p
  have hx0 : 0 ≤ ‖u w‖ := norm_nonneg _
  have hpu : ‖u w ^ (p - 1)‖ = ‖u w‖ ^ (p - 1) := norm_pow _ _
  have hpc : ‖starRingEnd ℂ (u w) ^ p‖ = ‖u w‖ ^ p := by rw [norm_pow, Complex.norm_conj]
  have key : ∀ X Y : ℂ, ‖X‖ ≤ ((p - 1 : ℕ) : ℝ) * β * ‖u w‖ ^ (p - 1 - 1) →
      ‖Y‖ ≤ (p : ℝ) * β * ‖u w‖ ^ (p - 1) →
      ‖X * starRingEnd ℂ (u w) ^ p + u w ^ (p - 1) * Y‖ ≤
        (2 * p - 1) * β * ‖u w‖ ^ (2 * p - 2) := by
    intro X Y hX hY
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hpu, hpc]
    rcases Nat.lt_or_ge p 2 with hp2 | hp2
    · have hp1 : p = 1 := by omega
      subst hp1
      have hX0 : ‖X‖ = 0 := le_antisymm (by simpa using hX) (norm_nonneg _)
      have hY' : ‖Y‖ ≤ β := by simpa using hY
      rw [hX0]
      norm_num
      exact hY'
    · have e1 : ‖u w‖ ^ (p - 1 - 1) * ‖u w‖ ^ p = ‖u w‖ ^ (2 * p - 2) := by
        rw [← pow_add]; congr 1; omega
      have e2 : ‖u w‖ ^ (p - 1) * ‖u w‖ ^ (p - 1) = ‖u w‖ ^ (2 * p - 2) := by
        rw [← pow_add]; congr 1; omega
      have hp' : ((p - 1 : ℕ) : ℝ) = p - 1 := by rw [Nat.cast_sub hp]; simp
      calc ‖X‖ * ‖u w‖ ^ p + ‖u w‖ ^ (p - 1) * ‖Y‖
          ≤ ((p - 1 : ℕ) : ℝ) * β * ‖u w‖ ^ (p - 1 - 1) * ‖u w‖ ^ p +
              ‖u w‖ ^ (p - 1) * ((p : ℝ) * β * ‖u w‖ ^ (p - 1)) := by
            gcongr
        _ = (2 * p - 1) * β * ‖u w‖ ^ (2 * p - 2) := by
            rw [hp']
            have : ((p : ℝ) - 1) * β * ‖u w‖ ^ (p - 1 - 1) * ‖u w‖ ^ p =
                ((p : ℝ) - 1) * β * (‖u w‖ ^ (p - 1 - 1) * ‖u w‖ ^ p) := by ring
            rw [this, e1]
            have : ‖u w‖ ^ (p - 1) * ((p : ℝ) * β * ‖u w‖ ^ (p - 1)) =
                (p : ℝ) * β * (‖u w‖ ^ (p - 1) * ‖u w‖ ^ (p - 1)) := by ring
            rw [this, e2]
            ring
  have d1 := (dW_mul (hA.diff w) (hB.diff w)).1
  have d2 := (dW_mul (hA.diff w) (hB.diff w)).2
  rw [d1, d2]
  have k1 := key _ _ a1 b1
  have k2 := key _ _ a2 b2
  have : 2 * (2 * (p : ℝ) - 1) * ‖u w‖ ^ (2 * p - 2) * β =
      (2 * p - 1) * β * ‖u w‖ ^ (2 * p - 2) + (2 * p - 1) * β * ‖u w‖ ^ (2 * p - 2) := by ring
  rw [this]
  exact add_le_add k1 k2

/-- The second-order Leibniz bound: for `a + b = 2`,
`|∂^{(a,b)} (f g)| ≤ |∂^{(a,b)} f| |g| + 2 (|∂_w f| + |∂_{w̄} f|)(|∂_w g| + |∂_{w̄} g|) + |f| |∂^{(a,b)} g|`. -/
private lemma L3_leib2 {f g : ℂ → ℂ} (hf : L3_Sm f) (hg : L3_Sm g) (w : ℂ) (a b : ℕ)
    (hab : a + b = 2) :
    ‖wirt a b (fun y => f y * g y) w‖ ≤ ‖wirt a b f w‖ * ‖g w‖ +
      2 * ((‖dW f w‖ + ‖dWbar f w‖) * (‖dW g w‖ + ‖dWbar g w‖)) + ‖f w‖ * ‖wirt a b g w‖ := by
  have w10 : ∀ F : ℂ → ℂ, wirt 1 0 F = dW F := fun F => rfl
  have w01 : ∀ F : ℂ → ℂ, wirt 0 1 F = dWbar F := fun F => rfl
  have w00 : ∀ F : ℂ → ℂ, wirt 0 0 F = F := fun F => rfl
  have hfa := norm_nonneg (dW f w)
  have hfb := norm_nonneg (dWbar f w)
  have hga := norm_nonneg (dW g w)
  have hgb := norm_nonneg (dWbar g w)
  rw [L3_wirt_mul hf hg a b w]
  rcases (show (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
      Nat.reduceSub, w00, w10]
    push_cast
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    simp only [norm_mul, Complex.norm_ofNat, norm_one, mul_one]
    nlinarith [mul_nonneg hfa hga, mul_nonneg hfb hgb, mul_nonneg hfa hgb, mul_nonneg hfb hga]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self, w00, w10, w01]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
    simp only [norm_mul]
    nlinarith [mul_nonneg hfa hga, mul_nonneg hfb hgb, mul_nonneg hfa hgb, mul_nonneg hfb hga]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
      Nat.reduceSub, w00, w01]
    push_cast
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    simp only [norm_mul, Complex.norm_ofNat, norm_one, mul_one]
    nlinarith [mul_nonneg hfa hga, mul_nonneg hfb hgb, mul_nonneg hfa hgb, mul_nonneg hfb hga]

/-! ### Pointwise bounds on the good event -/

/-- The jet of `Z^{p-1} Z̄^p` along a slice at a point of the good event:
`|∂^{(a,b)}| ≤ (2 Γ_t)^{a+b} (2p - 1)^{a+b} (|Z| + Ψ_Z)^{2p-1}` for `a + b ≤ K_m`. -/
private lemma L3_jet_Phi {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h i j w)) (Km p : ℕ) (hp : 1 ≤ p) :
    ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w') ^ (p - 1) *
          starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w')) ^ p) w‖ ≤
        (2 * L3_Gt Km K Γ₀) ^ (a + b) * ((2 * p - 1 : ℝ)) ^ (a + b) *
          (‖L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w)‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1) := by
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Γt := L3_Gt Km K Γ₀ with hΓt
  have hΓt0 : 0 ≤ Γt := by simp only [hΓt, L3_Gt]; positivity
  set Pz := L3_Pz D N θ K Γ₀ z.im with hPz
  have hPz0 : 0 ≤ Pz := L3_Pz_nonneg θ hK0 hΓ0 hs.hz
  set u : ℂ → ℂ := fun w' => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h i j w') with hu
  have hsu : L3_Sm u := L3_sm_slice (F := fun h' => L3_Z θ Λ B C T z₁ z₂ z₃ h')
    (fun n => L3_cd_Z θ hs.herm B C T hz₁ hz₂ hz₃ n) h hh i j
  set c := ‖u w‖ + Pz with hc
  have hc0 : 0 ≤ c := by positivity
  have hU : ∀ a b, a + b ≤ Km → ‖wirt a b u w‖ ≤ (2 * Γt) ^ (a + b) * c := by
    intro a b hab
    rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp only [wirt, Function.iterate_zero, id, add_zero, pow_zero, one_mul]
      linarith
    · refine (L3_jet_Z θ hs hΓ₀ h hh i j w hg Km a b h0 hab).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (u w)]) (by positivity)
  have hUc : ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => starRingEnd ℂ (u w')) w‖ ≤ (2 * Γt) ^ (a + b) * c := by
    intro a b hab
    rw [L3_wirt_conj hsu, Complex.norm_conj, add_comm a b]
    exact hU b a (by omega)
  have hP1 := L3_pow_jet hsu w (2 * Γt) c Km (by positivity) hc0 hU (p - 1)
  have hP2 := L3_pow_jet (L3_sm_conj hsu) w (2 * Γt) c Km (by positivity) hc0 hUc p
  have hΦ := L3_LB (L3_sm_pow hsu (p - 1)) (L3_sm_pow (L3_sm_conj hsu) p) w (2 * Γt)
    ((p - 1 : ℕ) : ℝ) (p : ℝ) (c ^ (p - 1)) (c ^ p) Km (by positivity) (Nat.cast_nonneg _)
    (pow_nonneg hc0 _) hP1 hP2
  intro a b hab
  refine (hΦ a b hab).trans (le_of_eq ?_)
  have hp' : ((p - 1 : ℕ) : ℝ) = p - 1 := by
    rw [Nat.cast_sub hp]; simp
  have hc2 : c ^ (p - 1) * c ^ p = c ^ (2 * p - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hp', hc2]
  ring/-- The bound `S_Z` on `Σ_{i,j} (|∂_w Z|² + |∂_{w̄} Z|²)` of `L3_Z_d1_sq`. -/
private def L3_SZ (D N : ℕ) (θ K Γ₀ η : ℝ) : ℝ := 16 * D * L3_Cz2 D θ * L3_S1 D N K Γ₀ η

/-- Cauchy–Schwarz for real arrays over the pairs `(i, j)`. -/
private lemma L3_cs_real {ι : Type*} [Fintype ι] (f g : ι → ι → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hg : ∀ i j, 0 ≤ g i j) :
    ∑ i, ∑ j, f i j * g i j ≤
      Real.sqrt (∑ i, ∑ j, f i j ^ 2) * Real.sqrt (∑ i, ∑ j, g i j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => f p.1 p.2) (fun p => g p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  have h0 : 0 ≤ ∑ i, ∑ j, f i j * g i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hf i j) (hg i j)
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

/-- `Σ_{i,j} (x_{ij} + y_{ij}) ≤ DN (2 Σ (x² + y²))^{1/2}` for nonnegative arrays. -/
private lemma L3_sum_pair {D N : ℕ} (x y : Idx D N → Idx D N → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (hy : ∀ i j, 0 ≤ y i j) (S : ℝ) (hS : ∑ i, ∑ j, (x i j ^ 2 + y i j ^ 2) ≤ S) :
    ∑ i, ∑ j, (x i j + y i j) ≤ (D * N : ℝ) * Real.sqrt (2 * S) := by
  have h := L3_cs_real (fun i j => x i j + y i j) (fun _ _ => (1 : ℝ))
    (fun i j => add_nonneg (hx i j) (hy i j)) (fun _ _ => zero_le_one)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  refine h.trans ?_
  have hc : ((Fintype.card (Idx D N) : ℕ) : ℝ) * ((Fintype.card (Idx D N) : ℕ) : ℝ) =
      ((D : ℝ) * N) ^ 2 := by
    simp [Fintype.card_prod]; ring
  have h2 : ∑ i, ∑ j, (x i j + y i j) ^ 2 ≤ 2 * S := by
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      (show (x i j + y i j) ^ 2 ≤ 2 * (x i j ^ 2 + y i j ^ 2) by
        nlinarith [sq_nonneg (x i j - y i j)])) ?_
    simp only [← Finset.mul_sum]
    linarith
  have hDN : (0 : ℝ) ≤ D * N := by positivity
  rw [hc, Real.sqrt_sq hDN]
  calc Real.sqrt (∑ i, ∑ j, (x i j + y i j) ^ 2) * ((D : ℝ) * N)
      ≤ Real.sqrt (2 * S) * (D * N : ℝ) := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2) hDN
    _ = _ := by ring

/-- The pointwise bounds on the good event behind the terms of order one and two of the
expansion: the sum over `(β, α)` of `|X_{βα}| (|∂_w Φ| + |∂_{w̄} Φ|)`, `Φ = Z^{p-1} Z̄^p`, and of
`|∂^{(a,b)} (X_{βα} Φ)|`, `a + b = 2`, along the slice `(β, α)` at `w = h_{βα}`. -/
private lemma L3_pw12 {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) (Km p : ℕ)
    (hKm : 2 ≤ Km) (hp : 1 ≤ p) :
    let c := ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ + L3_Pz D N θ K Γ₀ z.im
    let FX := (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2
    let SZ := L3_SZ D N θ K Γ₀ z.im
    (∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
        (‖dW (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w) ^ (p - 1) *
            starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w)) ^ p) (h β α)‖ +
          ‖dWbar (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w) ^ (p - 1) *
            starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w)) ^ p) (h β α)‖) ≤
      2 * (2 * p - 1) * c ^ (2 * p - 2) * (Real.sqrt FX * Real.sqrt (2 * SZ))) ∧
    (∀ a b, a + b = 2 →
      ∑ β, ∑ α, ‖wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α)‖ ≤
        36 * ((D * N : ℝ) * (K ^ 5 * Γ₀ ^ 2 * z.im⁻¹ ^ 2 *
          Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) * c ^ (2 * p - 1) +
        2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) *
          (2 * (2 * p - 1) * c ^ (2 * p - 2) * ((D * N : ℝ) * Real.sqrt (2 * SZ))) +
        (D * N : ℝ) * Real.sqrt FX *
          ((2 * L3_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))) := by
  intro c FX SZ
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  have hc0 : 0 ≤ c := add_nonneg (norm_nonneg _) (L3_Pz_nonneg θ hK0 hΓ0 hs.hz)
  have hZc : ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ≤ c := le_add_of_nonneg_right (L3_Pz_nonneg θ hK0 hΓ0 hs.hz)
  have hp1 : (1 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  -- the slices
  have hg' : ∀ β α, L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h β α (h β α)) := fun β α => by
    rw [L3_setEntry_self h hh]; exact hg
  set u : Idx D N → Idx D N → ℂ → ℂ := fun β α w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w)
    with hu
  have hsu : ∀ β α, L3_Sm (u β α) := fun β α =>
    L3_sm_slice (F := fun h' => L3_Z θ Λ B C T z₁ z₂ z₃ h') (fun n => L3_cd_Z θ hs.herm B C T hz₁ hz₂ hz₃ n)
      h hh β α
  have hu0 : ∀ β α, u β α (h β α) = L3_Z θ Λ B C T z₁ z₂ z₃ h := fun β α => by
    simp only [hu, L3_setEntry_self h hh]
  -- the first derivatives of `Z` and `Φ`
  have hdZ := L3_Z_d1_sq θ hs hΓ₀ h hh hg
  have hdu : ∑ β, ∑ α, (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖) ≤
      (D * N : ℝ) * Real.sqrt (2 * SZ) :=
    L3_sum_pair (fun β α => ‖dW (u β α) (h β α)‖) (fun β α => ‖dWbar (u β α) (h β α)‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) SZ hdZ
  have hdΦ : ∀ β α, ‖dW (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ +
      ‖dWbar (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ ≤
      2 * (2 * p - 1) * c ^ (2 * p - 2) * (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖) := by
    intro β α
    refine (L3_dPhi (hsu β α) (h β α) p hp).trans ?_
    rw [hu0]
    gcongr
  -- the matrix `X̃ = G₂ B G₁ T`
  obtain ⟨-, -, -, -, -, -, mX, -, -, -, -, -, -, -, -, fX, -, -⟩ := L3_good_mats hs hΓ₀ h hh hg
  have hXe : ∀ β α, L3_X Λ B C T z₁ z₂ z₃ h β α =
      (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C * res (Matrix.of h + Λ) z₂ *
        T) β α := fun β α =>
    L3_X_eq Λ B C T z₁ z₂ z₃ h β α
  refine ⟨?_, ?_⟩
  · -- the term of order one
    have hcs := L3_cs_real (fun β α => ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖)
      (fun β α => ‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => by positivity)
    have h1 : ∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ ^ 2 ≤ FX := by
      simp only [hXe]
      exact fX
    have h2 : ∑ β, ∑ α, (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖) ^ 2 ≤ 2 * SZ := by
      refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (show (‖dW (u i j) (h i j)‖ + ‖dWbar (u i j) (h i j)‖) ^ 2 ≤
          2 * (‖dW (u i j) (h i j)‖ ^ 2 + ‖dWbar (u i j) (h i j)‖ ^ 2) by
            nlinarith [sq_nonneg (‖dW (u i j) (h i j)‖ - ‖dWbar (u i j) (h i j)‖)])) ?_
      simp only [← Finset.mul_sum]
      have hdZ' : ∑ i, ∑ j, (‖dW (u i j) (h i j)‖ ^ 2 + ‖dWbar (u i j) (h i j)‖ ^ 2) ≤ SZ :=
        hdZ
      linarith
    calc ∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
          (‖dW (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ +
            ‖dWbar (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖)
        ≤ ∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
            (2 * (2 * p - 1) * c ^ (2 * p - 2) *
              (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)) :=
          Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ =>
            mul_le_mul_of_nonneg_left (hdΦ β α) (norm_nonneg _)
      _ = 2 * (2 * p - 1) * c ^ (2 * p - 2) * ∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
            (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          ring
      _ ≤ 2 * (2 * p - 1) * c ^ (2 * p - 2) * (Real.sqrt FX * Real.sqrt (2 * SZ)) := by
          refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (by positivity)
          exact mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
  · -- the terms of order two
    intro a b hab
    have hsX : ∀ β α, L3_Sm (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) := fun β α =>
      L3_sm_slice (F := fun h' => L3_X Λ B C T z₁ z₂ z₃ h' β α)
        (fun n => L3_cd_X hs.herm B C T hz₁ hz₂ hz₃ β α n) h hh β α
    have hsΦ : ∀ β α, L3_Sm (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) :=
      fun β α => L3_sm_mul (L3_sm_pow (hsu β α) _) (L3_sm_pow (L3_sm_conj (hsu β α)) _)
    have hX1 : ∀ β α, ‖dW (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ +
        ‖dWbar (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ ≤
        2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2)) := by
      intro β α
      have e1 := L3_jet_X hs hΓ0 h hh β α (h β α) (hg' β α) β α 1 0
      have e2 := L3_jet_X hs hΓ0 h hh β α (h β α) (hg' β α) β α 0 1
      have hv : ((3 + 1 + 0 : ℕ) : ℝ) ^ (1 + 0) * L3_Gs K Γ₀ z.im 1 ^ (1 + 0) *
          L3_Gs K Γ₀ z.im 3 = 4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2) := by
        simp only [L3_Gs]; norm_num
      have hv' : ((3 + 0 + 1 : ℕ) : ℝ) ^ (0 + 1) * L3_Gs K Γ₀ z.im 1 ^ (0 + 1) *
          L3_Gs K Γ₀ z.im 3 = 4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2) := by
        simp only [L3_Gs]; norm_num
      rw [hv] at e1
      rw [hv'] at e2
      have e1' : ‖dW (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ ≤
          4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2) := e1
      have e2' : ‖dWbar (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ ≤
          4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2) := e2
      linarith
    have hΦv : ∀ β α, ‖u β α (h β α) ^ (p - 1) * starRingEnd ℂ (u β α (h β α)) ^ p‖ ≤
        c ^ (2 * p - 1) := by
      intro β α
      rw [hu0, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add,
        show p - 1 + p = 2 * p - 1 by omega]
      exact pow_le_pow_left₀ (norm_nonneg _) hZc _
    have hΦ2 : ∀ β α, ‖wirt a b (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p)
        (h β α)‖ ≤ (2 * L3_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1) := by
      intro β α
      have := L3_jet_Phi θ hs hΓ₀ h hh β α (h β α) (hg' β α) Km p hp a b (by omega)
      rw [hab, L3_setEntry_self h hh] at this
      exact this
    have hpt : ∀ β α, ‖wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w))
        (h β α)‖ ≤
        ‖wirt a b (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ * c ^ (2 * p - 1) +
        2 * ((2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) *
          (2 * (2 * p - 1) * c ^ (2 * p - 2) * (‖dW (u β α) (h β α)‖ +
            ‖dWbar (u β α) (h β α)‖))) +
        ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
          ((2 * L3_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1)) := by
      intro β α
      have e : (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) = fun w =>
          L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α *
            (u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) := by
        funext w; rfl
      rw [e]
      refine (L3_leib2 (hsX β α) (hsΦ β α) (h β α) a b hab).trans ?_
      have hXv : ‖L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α (h β α)) β α‖ = ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ := by
        rw [L3_setEntry_self h hh]
      rw [hXv]
      have hdx0 : 0 ≤ ‖dW (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ +
          ‖dWbar (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ := by positivity
      have hdp0 : 0 ≤ ‖dW (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ +
          ‖dWbar (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ := by
        positivity
      have hW : 0 ≤ 2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2)) := by positivity
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hΦv β α) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (mul_le_mul (hX1 β α) (hdΦ β α) hdp0 hW) (by norm_num)))
        (mul_le_mul_of_nonneg_left (hΦ2 β α) (norm_nonneg _))
    refine (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => hpt β α).trans ?_
    simp only [Finset.sum_add_distrib]
    have s1 := L3_sum_d2X hs hΓ₀ h hh hg a b hab
    have s3 : ∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ ≤ (D * N : ℝ) * Real.sqrt FX := by
      have := L3_sum_off (res (Matrix.of h + Λ) z₃ * B * res (Matrix.of h + Λ) z₁ * C *
        res (Matrix.of h + Λ) z₂ * T) FX fX
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at this
      simpa only [hXe] using this
    have hcp : 0 ≤ c ^ (2 * p - 1) := pow_nonneg hc0 _
    have hJ : 0 ≤ (2 * L3_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1) := by
      positivity
    have hW : 0 ≤ 2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2)) := by positivity
    have hcq : 0 ≤ 2 * (2 * (p : ℝ) - 1) * c ^ (2 * p - 2) := by
      have := pow_nonneg hc0 (2 * p - 2); nlinarith
    calc (∑ β, ∑ α, ‖wirt a b (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α) (h β α)‖ *
            c ^ (2 * p - 1)) +
          (∑ β, ∑ α, 2 * ((2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) *
            (2 * (2 * p - 1) * c ^ (2 * p - 2) *
              (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)))) +
          ∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
            ((2 * L3_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))
        = (∑ β, ∑ α, ‖wirt a b (fun w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α)
              (h β α)‖) * c ^ (2 * p - 1) +
          2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) * (2 * (2 * p - 1) *
            c ^ (2 * p - 2) * ∑ β, ∑ α, (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)) +
          (∑ β, ∑ α, ‖L3_X Λ B C T z₁ z₂ z₃ h β α‖) *
            ((2 * L3_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1)) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          congr 1
          congr 1
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          ring
      _ ≤ _ := by
          gcongr

/-! ### Crude bounds and integrability -/

private lemma L3_Lv_nonneg {K Γ₀ η : ℝ} (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (n : ℕ) :
    0 ≤ L3_Lv K Γ₀ η n := by
  have := inv_nonneg.mpr hη.le
  have : 0 ≤ K := by linarith
  have : 0 ≤ Γ₀ := by linarith
  unfold L3_Lv
  split_ifs <;> positivity

/-- The bound on `|Z|` at a point of the good event with constant `Γ₀ ≥ 1`:
`|Z| ≤ C_z K⁴ Γ₀² (1 + η⁻¹)²`. -/
private lemma L3_Z_good {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ}
    {z z₁ z₂ z₃ : ℂ} {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) :
    ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ≤ L3_Cz D θ * (K ^ 4 * Γ₀ ^ 2 * (1 + z.im⁻¹) ^ 2) := by
  rcases isEmpty_or_nonempty (Idx D N) with hE | ⟨⟨k⟩⟩
  · have e : L3_Z θ Λ B C T z₁ z₂ z₃ h = 0 := by
      have hD : D = 0 ∨ N = 0 := by
        by_contra hc
        push_neg at hc
        exact hE.false (⟨0, Nat.pos_of_ne_zero hc.1⟩, ⟨0, Nat.pos_of_ne_zero hc.2⟩)
      unfold L3_Z
      rcases hD with rfl | rfl
      · simp
      · simp [ntr]
    rw [e, norm_zero]
    have := L3_Cz_nonneg D θ
    have : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
    positivity
  unfold L3_Z L3_Cz
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  obtain ⟨v1, v2⟩ := L3_loop_vals hs hΓ₀ h hh hg k x t
  obtain ⟨-, hl2a, hl2b, hl12⟩ := L3_lens Λ B C T z₁ z₂ z₃ x t
  rw [norm_mul, norm_mul]
  have hp : ‖ntr (chainB h (L3_l1 Λ C T z₁ z₂ z₃ x t))‖ *
      ‖ntr (chainB h (L3_l2 Λ B C T z₁ z₂ z₃ x t))‖ ≤ K ^ 4 * Γ₀ ^ 2 * (1 + z.im⁻¹) ^ 2 :=
    (mul_le_mul v1 v2 (norm_nonneg _) (L3_Lv_nonneg hs.hK hΓ₀ hs.hz _)).trans
      (L3_vv_le hs.hK hΓ₀ hs.hz _ _ hl12 hl2a hl2b)
  calc ‖L3_cf D θ t‖ * ‖ntr (chainB h (L3_l1 Λ C T z₁ z₂ z₃ x t))‖ *
        ‖ntr (chainB h (L3_l2 Λ B C T z₁ z₂ z₃ x t))‖
      = ‖L3_cf D θ t‖ * (‖ntr (chainB h (L3_l1 Λ C T z₁ z₂ z₃ x t))‖ *
        ‖ntr (chainB h (L3_l2 Λ B C T z₁ z₂ z₃ x t))‖) := by ring
    _ ≤ ‖L3_cf D θ t‖ * (K ^ 4 * Γ₀ ^ 2 * (1 + z.im⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)

/-- The crude constant `Γ₀ = K² (1 + η⁻¹)` of the good event, valid on every Hermitian array. -/
private def L3_Gc0 (K η : ℝ) : ℝ := K ^ 2 * (1 + η⁻¹)

/-- The crude bound `|Z| ≤ C_z K⁴ Γ₀² (1 + η⁻¹)²` with `Γ₀ = L3_Gc0`. -/
private def L3_Zc (D : ℕ) (θ K η : ℝ) : ℝ :=
  L3_Cz D θ * (K ^ 4 * L3_Gc0 K η ^ 2 * (1 + η⁻¹) ^ 2)

/-- The crude bound on the mixed derivatives of order `≤ K_m` of the integrand. -/
private def L3_Bc (D N : ℕ) (θ : ℝ) (Km p : ℕ) (K η : ℝ) : ℝ :=
  (4 * p * L3_Gt Km K (L3_Gc0 K η)) ^ Km * L3_Gs K (L3_Gc0 K η) η 3 *
    (L3_Zc D θ K η + L3_Pz D N θ K (L3_Gc0 K η) η) ^ (2 * p - 1)

private lemma L3_Gc0_ge {K η : ℝ} (hK : 1 ≤ K) (hη : 0 < η) : 1 ≤ L3_Gc0 K η := by
  unfold L3_Gc0
  have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  nlinarith

/-- The crude bound on `|Z|` on Hermitian arrays. -/
private lemma L3_Z_crude {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ}
    {z z₁ z₂ z₃ : ℂ} {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) : ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ≤ L3_Zc D θ K z.im :=
  L3_Z_good θ hs (L3_Gc0_ge hs.hK hs.hz) h hh (L3_good_crude hs h hh)

/-- The crude bound on the mixed derivatives of the integrand along every slice through a
Hermitian array, orders `a + b ≤ K_m`. -/
private lemma L3_F_crude {D N : ℕ} (θ : ℝ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) (Km p : ℕ) (hp : 1 ≤ p)
    (β α : Idx D N) (a b : ℕ) (hab : a + b ≤ Km) :
    ‖wirt a b (fun w' => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h i j w')) w‖ ≤
      L3_Bc D N θ Km p K z.im := by
  have hΓ := L3_Gc0_ge hs.hK hs.hz
  have hh' := L3_slice_herm h hh i j w
  have hg := L3_good_crude hs (setEntry h i j w) hh'
  refine (L3_jet_F θ hs hΓ h hh i j w hg Km p hp β α a b hab).trans ?_
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  have hΓ0 : 0 ≤ L3_Gc0 K z.im := by linarith
  have hGt : 1 ≤ 4 * p * L3_Gt Km K (L3_Gc0 K z.im) := by
    unfold L3_Gt
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h2 : (3 : ℝ) ≤ 3 + Km := by have : (0 : ℝ) ≤ Km := Nat.cast_nonneg _; linarith
    have h3 : 1 ≤ K * L3_Gc0 K z.im := by nlinarith [hs.hK]
    have h5 : (1 : ℝ) ≤ p * (3 + Km) := by nlinarith
    have h6 := one_le_mul_of_one_le_of_one_le h5 h3
    have e : 4 * (p : ℝ) * ((3 + Km) * K * L3_Gc0 K z.im) =
        4 * ((p * (3 + Km)) * (K * L3_Gc0 K z.im)) := by ring
    rw [e]
    linarith
  have hZ := L3_Z_crude θ hs (setEntry h i j w) hh'
  have hPz := L3_Pz_nonneg (D := D) (N := N) θ hK0 hΓ0 hs.hz
  unfold L3_Bc
  have hG3 : 0 ≤ L3_Gs K (L3_Gc0 K z.im) z.im 3 := by unfold L3_Gs; positivity
  refine mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hGt hab) hG3)
    (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)

/-- The integrands of the expansion are integrable: `∂_w^a ∂_{w̄}^b X_{βα}Φ` at `w = h_{βα}`. -/
private lemma L3_int_wirt {D N : ℕ} (θ : ℝ) {Cc : ℕ → ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N Cc θ μ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ} {K : ℝ}
    (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) (p : ℕ) (hp : 1 ≤ p) (β α : Idx D N) (i j : Idx D N)
    (a b : ℕ) :
    Integrable (fun h => wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h i j w))
      (h i j)) μ := by
  have := hμ.prob
  refine Integrable.mono' (integrable_const (L3_Bc D N θ (a + b) p K z.im))
    (L3_wirt_aesm hμ.herm (fun n => L3_cd_F θ hs.herm B C T (L3_pm_ne hs.hz hs.h1)
      (L3_pm_ne hs.hz hs.h2) (L3_pm_ne hs.hz hs.h3) p β α n) i j a b) ?_
  filter_upwards [hμ.herm] with h hh
  exact L3_F_crude θ hs h hh i j (h i j) (a + b) p hp β α a b le_rfl

/-- `h ↦ F(h)` is almost everywhere strongly measurable when `F ∘ symArr` is continuous. -/
private lemma L3_aesm_sym {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) {E : Type*} [NormedAddCommGroup E]
    {F : (Idx D N → Idx D N → ℂ) → E} (hF : Continuous (fun h => F (symArr h))) :
    AEStronglyMeasurable F μ := by
  refine hF.aestronglyMeasurable.congr ?_
  filter_upwards [hμh] with h hh
  rw [symArr_of_isHermitian h hh]

/-! ### The terms of order `≤ l` of the expansion at a point of the good event -/

/-- The terms of order `≤ l` of the cumulant expansion (2.26) [5.16] of `E X_{βα} Φ h̄_{βα}`,
summed over `(β, α)`, at the array `h`, for the cumulants `κ_{p,q}(β, α)`. -/
private def L3_ES {D N : ℕ} (θ : ℝ) (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (p l : ℕ) (κ : ℕ → ℕ → Idx D N → Idx D N → ℂ) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ∑ β, ∑ α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
    κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
      wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α)

/-- `0 ≤ (S_θ)_{βα} ≤ N⁻¹` for `θ ∈ [0, 1]`. -/
private lemma L3_varProf_le {D N : ℕ} [NeZero D] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (β α : Idx D N) : 0 ≤ varProf D N θ β α ∧ varProf D N θ β α ≤ (N : ℝ)⁻¹ := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hN : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hDN : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    exact mul_le_of_le_one_left hN (inv_le_one_of_one_le₀ hD)
  have hDN0 : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  unfold varProf
  constructor
  · split_ifs <;> nlinarith
  · split_ifs <;> nlinarith

/-- The terms of order `≤ l` at a point `h` of the good event: the terms of order one
cancel the counterterms up to `(DN)⁻¹ Σ (S_θ)_{βα} X_{βα} ∂Φ`, and the terms of order `≥ 2`
are bounded by the jets. Here `κ_{p,q}` are numbers with the values of the second cumulants
of the class and `|κ_{p,q}| ≤ K_c N^{-(p+q)/2}` for `p + q ≥ 3`. -/
private lemma L3_pw_all {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : L3_good Λ z (L3_U Λ B C T z₃) Γ₀ h) (p l : ℕ)
    (hp : 1 ≤ p) (hl : 2 ≤ l) (κ : ℕ → ℕ → Idx D N → Idx D N → ℂ) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (h01 : ∀ β α, κ 0 1 β α = 0) (h11 : ∀ β α, κ 1 1 β α = varProf D N θ β α)
    (h02 : ∀ β α, κ 0 2 β α = if β = α then (varProf D N θ β α : ℂ) else 0)
    (hκ : ∀ a b β α, 3 ≤ a + b → a + b ≤ l + 1 →
      ‖κ a b β α‖ ≤ Kc * (N : ℝ) ^ (-(((a + b : ℕ) : ℝ) / 2))) :
    ‖((D : ℂ) * N)⁻¹ * L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h +
        L3_C θ Λ B C T z₁ z₂ z₃ h * (L3_Z θ Λ B C T z₁ z₂ z₃ h ^ (p - 1) *
          starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ h) ^ p)‖ ≤
      ((D : ℝ) * N)⁻¹ * ((N : ℝ)⁻¹ *
        (2 * (2 * p - 1) * (‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 2) *
          (Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2) *
            Real.sqrt (2 * L3_SZ D N θ K Γ₀ z.im))) +
        3 * Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
          (36 * ((D * N : ℝ) * (K ^ 5 * Γ₀ ^ 2 * z.im⁻¹ ^ 2 *
            Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) *
              (‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1) +
            2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) *
              (2 * (2 * p - 1) * (‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 2) *
                ((D * N : ℝ) * Real.sqrt (2 * L3_SZ D N θ K Γ₀ z.im))) +
            (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2) *
              ((2 * L3_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 *
                (‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1))) +
        ((l : ℝ) + 1) ^ 2 * Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 *
          ((4 * p * L3_Gt l K Γ₀) ^ l * L3_Gs K Γ₀ z.im 3 *
            (‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ + L3_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1)))) := by
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Pz := L3_Pz D N θ K Γ₀ z.im with hPz
  have hPz0 : 0 ≤ Pz := L3_Pz_nonneg θ hK0 hΓ0 hs.hz
  set Zh := L3_Z θ Λ B C T z₁ z₂ z₃ h with hZh
  set c := ‖Zh‖ + Pz with hc
  have hc0 : 0 ≤ c := by positivity
  -- the slices
  set X : Idx D N → Idx D N → ℂ → ℂ := fun β α w => L3_X Λ B C T z₁ z₂ z₃ (setEntry h β α w) β α
    with hX
  set u : Idx D N → Idx D N → ℂ → ℂ := fun β α w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w)
    with hu
  set Φ : Idx D N → Idx D N → ℂ → ℂ := fun β α w => u β α w ^ (p - 1) *
    starRingEnd ℂ (u β α w) ^ p with hΦ
  have hsX : ∀ β α, L3_Sm (X β α) := fun β α =>
    L3_sm_slice (F := fun h' => L3_X Λ B C T z₁ z₂ z₃ h' β α)
      (fun n => L3_cd_X hs.herm B C T hz₁ hz₂ hz₃ β α n) h hh β α
  have hsu : ∀ β α, L3_Sm (u β α) := fun β α =>
    L3_sm_slice (F := fun h' => L3_Z θ Λ B C T z₁ z₂ z₃ h') (fun n => L3_cd_Z θ hs.herm B C T hz₁ hz₂ hz₃ n)
      h hh β α
  have hsΦ : ∀ β α, L3_Sm (Φ β α) := fun β α =>
    L3_sm_mul (L3_sm_pow (hsu β α) _) (L3_sm_pow (L3_sm_conj (hsu β α)) _)
  have hX0 : ∀ β α, X β α (h β α) = L3_X Λ B C T z₁ z₂ z₃ h β α := fun β α => by
    simp only [hX, L3_setEntry_self h hh]
  have hΦ0 : ∀ β α, Φ β α (h β α) = Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p := fun β α => by
    simp only [hΦ, hu, L3_setEntry_self h hh, hZh]
  have hFe : ∀ β α, (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) =
      fun w => X β α w * Φ β α w := fun β α => by funext w; rfl
  -- the terms of order one and of order `≥ 2`
  set tm : Idx D N → Idx D N → ℕ → ℕ → ℂ := fun β α a b =>
    κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
      wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α) with htm
  have hsplit : ∀ β α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a), tm β α a b =
      (κ 1 1 β α * dW (fun w => X β α w * Φ β α w) (h β α) +
        κ 0 2 β α * dWbar (fun w => X β α w * Φ β α w) (h β α)) +
      ∑ k ∈ Finset.Ico 2 (l + 1), ∑ a ∈ Finset.range (k + 1), tm β α a (k - a) := by
    intro β α
    rw [L3_regroup (tm β α) l, ← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ l + 1)]
    congr 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, htm, h01, hFe]
    simp only [Nat.factorial, Nat.cast_one, Nat.mul_one, div_one, zero_mul, zero_add,
      Nat.sub_self, Nat.sub_zero, Nat.succ_eq_add_one]
    norm_num [wirt]
    ring
  -- the order one: the product rule and the cancellation
  have hprod : ∀ β α, κ 1 1 β α * dW (fun w => X β α w * Φ β α w) (h β α) +
      κ 0 2 β α * dWbar (fun w => X β α w * Φ β α w) (h β α) =
      (Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p) * ((varProf D N θ β α : ℂ) * dW (X β α) (h β α) +
        (if β = α then (varProf D N θ β α : ℂ) else 0) * dWbar (X β α) (h β α)) +
      ((varProf D N θ β α : ℂ) * (L3_X Λ B C T z₁ z₂ z₃ h β α * dW (Φ β α) (h β α)) +
        (if β = α then (varProf D N θ β α : ℂ) else 0) *
          (L3_X Λ B C T z₁ z₂ z₃ h β α * dWbar (Φ β α) (h β α))) := by
    intro β α
    rw [L3_der_dW.mul _ _ (hsX β α) (hsΦ β α), L3_der_dWbar.mul _ _ (hsX β α) (hsΦ β α)]
    simp only [h11, h02, hX0, hΦ0]
    ring
  have hcan := L3_cancel θ hs.herm B C T hz₁ hz₂ hz₃ h hh
  set R1 : ℂ := ∑ β, ∑ α, ((varProf D N θ β α : ℂ) * (L3_X Λ B C T z₁ z₂ z₃ h β α *
      dW (Φ β α) (h β α)) + (if β = α then (varProf D N θ β α : ℂ) else 0) *
        (L3_X Λ B C T z₁ z₂ z₃ h β α * dWbar (Φ β α) (h β α))) with hR1
  set R2 : ℂ := ∑ β, ∑ α, ∑ k ∈ Finset.Ico 2 (l + 1), ∑ a ∈ Finset.range (k + 1),
      tm β α a (k - a) with hR2
  have hES : L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h =
      (Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p) * (-((D : ℂ) * N) * L3_C θ Λ B C T z₁ z₂ z₃ h) +
        R1 + R2 := by
    have e1 : L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h =
        ∑ β, ∑ α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a), tm β α a b := rfl
    rw [e1]
    simp only [hsplit, hprod, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hR1, hR2, ← hcan]
    simp only [Finset.sum_add_distrib, hX]
  have hDN : ((D : ℂ) * N) ≠ 0 := by
    have : (D : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne D
    have : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    exact mul_ne_zero ‹_› ‹_›
  have hmain : ((D : ℂ) * N)⁻¹ * L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h +
      L3_C θ Λ B C T z₁ z₂ z₃ h * (Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p) =
      ((D : ℂ) * N)⁻¹ * (R1 + R2) := by
    rw [hES]
    have hinv : ((D : ℂ) * N)⁻¹ * ((D : ℂ) * N) = 1 := inv_mul_cancel₀ hDN
    linear_combination (-(Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p * L3_C θ Λ B C T z₁ z₂ z₃ h)) * hinv
  rw [hmain, norm_mul]
  have hDNn : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [hDNn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the bound on `R1`
  obtain ⟨pw1, pw2⟩ := L3_pw12 θ hs hΓ₀ h hh hg l p hl hp
  have hR1b : ‖R1‖ ≤ (N : ℝ)⁻¹ *
      (2 * (2 * p - 1) * c ^ (2 * p - 2) *
        (Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2) *
          Real.sqrt (2 * L3_SZ D N θ K Γ₀ z.im))) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left pw1 (inv_nonneg.mpr hN0.le))
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    obtain ⟨v0, v1⟩ := L3_varProf_le (D := D) (N := N) θ hθ0 hθ1 β α
    have hv : ‖(varProf D N θ β α : ℂ)‖ ≤ (N : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg v0]; exact v1
    have hv' : ‖(if β = α then (varProf D N θ β α : ℂ) else 0)‖ ≤ (N : ℝ)⁻¹ := by
      split_ifs
      · exact hv
      · rw [norm_zero]; exact inv_nonneg.mpr hN0.le
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have e : (Φ β α) = (fun w => L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w) ^ (p - 1) *
        starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ (setEntry h β α w)) ^ p) := rfl
    rw [← e]
    have hn1 := norm_nonneg (L3_X Λ B C T z₁ z₂ z₃ h β α)
    have hn2 := norm_nonneg (dW (Φ β α) (h β α))
    have hn3 := norm_nonneg (dWbar (Φ β α) (h β α))
    calc ‖(varProf D N θ β α : ℂ)‖ * (‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ * ‖dW (Φ β α) (h β α)‖) +
          ‖(if β = α then (varProf D N θ β α : ℂ) else 0)‖ *
            (‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ * ‖dWbar (Φ β α) (h β α)‖)
        ≤ (N : ℝ)⁻¹ * (‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ * ‖dW (Φ β α) (h β α)‖) +
          (N : ℝ)⁻¹ * (‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ * ‖dWbar (Φ β α) (h β α)‖) := by
          gcongr
      _ = (N : ℝ)⁻¹ * (‖L3_X Λ B C T z₁ z₂ z₃ h β α‖ *
            (‖dW (Φ β α) (h β α)‖ + ‖dWbar (Φ β α) (h β α)‖)) := by ring
  -- the bound on `R2`
  have hGt1 : 1 ≤ 4 * p * L3_Gt l K Γ₀ := by
    unfold L3_Gt
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h2 : (3 : ℝ) ≤ 3 + l := by have : (0 : ℝ) ≤ l := Nat.cast_nonneg _; linarith
    have h3 : 1 ≤ K * Γ₀ := one_le_mul_of_one_le_of_one_le hs.hK hΓ₀
    have h5 : (1 : ℝ) ≤ p * (3 + l) := by nlinarith
    have h6 := one_le_mul_of_one_le_of_one_le h5 h3
    have e : 4 * (p : ℝ) * ((3 + l) * K * Γ₀) = 4 * ((p * (3 + l)) * (K * Γ₀)) := by ring
    rw [e]
    linarith
  have hGs3 : 0 ≤ L3_Gs K Γ₀ z.im 3 := by
    unfold L3_Gs
    have := inv_nonneg.mpr hs.hz.le
    positivity
  set J := (4 * p * L3_Gt l K Γ₀) ^ l * L3_Gs K Γ₀ z.im 3 * c ^ (2 * p - 1) with hJ
  have hJ0 : 0 ≤ J := by positivity
  have hg' : ∀ β α, L3_good Λ z (L3_U Λ B C T z₃) Γ₀ (setEntry h β α (h β α)) := fun β α => by
    rw [L3_setEntry_self h hh]; exact hg
  have hfac : ∀ a b : ℕ, ‖((a.factorial * b.factorial : ℕ) : ℂ)‖⁻¹ ≤ 1 := by
    intro a b
    rw [Complex.norm_natCast]
    refine inv_le_one_of_one_le₀ ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero a)
      (Nat.factorial_ne_zero b))
  have htm : ∀ β α k a, a ≤ k → 2 ≤ k → k ≤ l →
      ‖tm β α a (k - a)‖ ≤ Kc * (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) / 2)) *
        ‖wirt a (k - a) (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α)‖ := by
    intro β α k a hak hk hkl
    simp only [htm]
    rw [norm_mul, norm_div]
    have e : a + (k - a + 1) = k + 1 := by omega
    have := hκ a (k - a + 1) β α (by omega) (by omega)
    rw [e] at this
    rw [div_eq_mul_inv]
    have h0 := norm_nonneg (wirt a (k - a) (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α
      (setEntry h β α w)) (h β α))
    calc ‖κ a (k - a + 1) β α‖ * ‖((a.factorial * (k - a).factorial : ℕ) : ℂ)‖⁻¹ *
          ‖wirt a (k - a) (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α)‖
        ≤ (Kc * (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) / 2))) * 1 *
          ‖wirt a (k - a) (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α)‖ := by
          gcongr
          exact hfac _ _
      _ = _ := by ring
  have hR2e : R2 = ∑ k ∈ Finset.Ico 2 (l + 1), ∑ a ∈ Finset.range (k + 1),
      ∑ β, ∑ α, tm β α a (k - a) := by
    rw [hR2]
    simp only [Finset.sum_comm (s := Finset.univ) (t := Finset.Ico 2 (l + 1))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.sum_comm (s := Finset.univ) (t := Finset.range (k + 1))]
  have hIco : Finset.Ico 2 (l + 1) = insert 2 (Finset.Ico 3 (l + 1)) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have h3 : (N : ℝ) ^ (-(((2 + 1 : ℕ) : ℝ) / 2)) = (N : ℝ) ^ (-((3 : ℝ) / 2)) := by norm_num
  have hk2 : ‖∑ a ∈ Finset.range (2 + 1), ∑ β, ∑ α, tm β α a (2 - a)‖ ≤
      3 * Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
        (36 * ((D * N : ℝ) * (K ^ 5 * Γ₀ ^ 2 * z.im⁻¹ ^ 2 *
            Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) * c ^ (2 * p - 1) +
          2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) *
            (2 * (2 * p - 1) * c ^ (2 * p - 2) *
              ((D * N : ℝ) * Real.sqrt (2 * L3_SZ D N θ K Γ₀ z.im))) +
          (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2) *
            ((2 * L3_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))) := by
    have hN32 : 0 ≤ (N : ℝ) ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg hN0.le _
    have each : ∀ a ∈ Finset.range (2 + 1), ‖∑ β, ∑ α, tm β α a (2 - a)‖ ≤
        Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
          (36 * ((D * N : ℝ) * (K ^ 5 * Γ₀ ^ 2 * z.im⁻¹ ^ 2 *
              Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) * c ^ (2 * p - 1) +
            2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * z.im⁻¹ ^ 2))) *
              (2 * (2 * p - 1) * c ^ (2 * p - 2) *
                ((D * N : ℝ) * Real.sqrt (2 * L3_SZ D N θ K Γ₀ z.im))) +
            (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * (K * z.im⁻¹ * K)) ^ 2) *
              ((2 * L3_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))) := by
      intro a ha
      have ha2 : a ≤ 2 := by simpa [Nat.lt_succ_iff] using ha
      refine (norm_sum_le _ _).trans ?_
      refine le_trans (Finset.sum_le_sum fun β _ => norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ =>
        htm β α 2 a ha2 le_rfl hl) ?_
      rw [h3]
      simp only [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (pw2 a (2 - a) (by omega)) (mul_nonneg hKc hN32)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum each).trans (le_of_eq ?_))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hk3 : ‖∑ k ∈ Finset.Ico 3 (l + 1), ∑ a ∈ Finset.range (k + 1), ∑ β, ∑ α,
      tm β α a (k - a)‖ ≤ ((l : ℝ) + 1) ^ 2 * Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 * J) := by
    have each : ∀ k ∈ Finset.Ico 3 (l + 1), ∀ a ∈ Finset.range (k + 1),
        ‖∑ β, ∑ α, tm β α a (k - a)‖ ≤ Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 * J) := by
      intro k hk a ha
      have hk' : 3 ≤ k ∧ k ≤ l := by simp only [Finset.mem_Ico] at hk; omega
      have ha' : a ≤ k := by simpa [Nat.lt_succ_iff] using ha
      have hNk : (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) / 2)) ≤ (N : ℝ) ^ (-(2 : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
        have : (4 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ k + 1)
        linarith
      have hpt : ∀ β α, ‖tm β α a (k - a)‖ ≤ Kc * (N : ℝ) ^ (-(2 : ℝ)) * J := by
        intro β α
        refine (htm β α k a ha' (by omega) hk'.2).trans ?_
        have hj := L3_jet_F θ hs hΓ₀ h hh β α (h β α) (hg' β α) l p hp β α a (k - a) (by omega)
        rw [L3_setEntry_self h hh, show a + (k - a) = k by omega] at hj
        have hj' : ‖wirt a (k - a) (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w))
            (h β α)‖ ≤ J := by
          refine hj.trans ?_
          rw [hJ]
          gcongr
          all_goals first | exact hGt1 | exact hk'.2
        exact mul_le_mul (mul_le_mul_of_nonneg_left hNk hKc) hj' (norm_nonneg _)
          (mul_nonneg hKc (Real.rpow_nonneg hN0.le _))
      refine (norm_sum_le _ _).trans ?_
      refine le_trans (Finset.sum_le_sum fun β _ => norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => hpt β α) ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      apply le_of_eq
      ring
    have hb0 : 0 ≤ Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 * J) :=
      mul_nonneg (mul_nonneg hKc (Real.rpow_nonneg hN0.le _)) (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun a ha => each k hk a ha)) ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hc1 : ∀ k ∈ Finset.Ico 3 (l + 1), ((k + 1 : ℕ) : ℝ) *
        (Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 * J)) ≤
        ((l : ℝ) + 1) * (Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 * J)) := by
      intro k hk
      have : k ≤ l := by simp only [Finset.mem_Ico] at hk; omega
      have : ((k + 1 : ℕ) : ℝ) ≤ (l : ℝ) + 1 := by push_cast; exact_mod_cast (by omega : k + 1 ≤ l + 1)
      exact mul_le_mul_of_nonneg_right this hb0
    refine (Finset.sum_le_sum hc1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    have : ((l + 1 - 3 : ℕ) : ℝ) ≤ (l : ℝ) + 1 := by
      have : l + 1 - 3 ≤ l + 1 := Nat.sub_le _ _
      exact_mod_cast this
    have hl0 : 0 ≤ ((l : ℝ) + 1) * (Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 * J)) := by
      positivity
    calc ((l + 1 - 3 : ℕ) : ℝ) * (((l : ℝ) + 1) * (Kc * (N : ℝ) ^ (-(2 : ℝ)) *
          (((D : ℝ) * N) ^ 2 * J)))
        ≤ ((l : ℝ) + 1) * (((l : ℝ) + 1) * (Kc * (N : ℝ) ^ (-(2 : ℝ)) *
          (((D : ℝ) * N) ^ 2 * J))) := mul_le_mul_of_nonneg_right this hl0
      _ = _ := by ring
  refine (norm_add_le _ _).trans ?_
  rw [hR2e, hIco, Finset.sum_insert (by simp)]
  refine le_trans (add_le_add hR1b ((norm_add_le _ _).trans (add_le_add hk2 hk3))) (le_of_eq ?_)
  ring

/-! ### The good event as a finite family of forms -/

/-- The vectors `Q e_k` of the good event as a finite set. -/
private def L3_V {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) :
    Finset (Idx D N → ℂ) :=
  Finset.univ.image fun p : (Fin 9 ⊕ (Fin D ⊕ Fin D)) × Idx D N =>
    L3_Qf Λ B C T z₃ p.1 *ᵥ Pi.single p.2 1

private lemma L3_V_mem {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z₃ : ℂ}
    {v : Idx D N → ℂ} : v ∈ L3_V Λ B C T z₃ ↔ v ∈ L3_U Λ B C T z₃ := by
  simp only [L3_V, Finset.mem_image, Finset.mem_univ, true_and, L3_U, Set.mem_range]

private lemma L3_e_V {D N : ℕ} (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₃ : ℂ) (k : Idx D N) :
    (Pi.single k 1 : Idx D N → ℂ) ∈ L3_V Λ B C T z₃ :=
  L3_V_mem.mpr (L3_e_U Λ B C T z₃ k)

/-- The Hermitian part `h ↦ (h + hᴴ)/2` is smooth. -/
private lemma L3_contDiff_symArr {D N : ℕ} (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => symArr h) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  simp only [symArr]
  exact ((contDiff_apply_apply ℝ k l).add
    (Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ l k))).div_const 2

/-- `x^* (Aᴴ y) = conj (y^* (A x))`. -/
private lemma L3_dot_conjT {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star x ⬝ᵥ (Aᴴ *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ (A *ᵥ x)) := by
  rw [L3_dot_adj, Matrix.conjTranspose_conjTranspose]
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The forms `x^* G(z) y`, `x, y ∈ V`, bounded by `Γ` at a Hermitian array give the good event
with constant `Γ` (the forms at `z̄` are their conjugates). -/
private lemma L3_good_of_forms {D N : ℕ} {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ}
    {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) {Γ : ℝ} {h : Idx D N → Idx D N → ℂ}
    (hh : (Matrix.of h).IsHermitian)
    (hf : ∀ x ∈ L3_V Λ B C T z₃, ∀ y ∈ L3_V Λ B C T z₃,
      ‖resFactorEval (x, y, Λ, z) h‖ ≤ Γ) :
    L3_good Λ z (L3_U Λ B C T z₃) Γ h := by
  intro ζ hζ u hu v hv
  have hu' := L3_V_mem.mpr hu
  have hv' := L3_V_mem.mpr hv
  rcases hζ with rfl | rfl
  · exact hf u hu' v hv'
  · have hX := hh.add hs.herm
    rw [← L3_res_conjT _ hX z hs.hz.ne', L3_dot_conjT, Complex.norm_conj]
    exact hf v hv' u hu'

/-- The set of arrays where a form `x^* G(z) y`, `x, y ∈ V`, of the Hermitian part exceeds `Γ`
is open. -/
private lemma L3_bad_open {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (V : Finset (Idx D N → ℂ)) (Γ : ℝ) :
    IsOpen {h : Idx D N → Idx D N → ℂ | ∃ x ∈ V, ∃ y ∈ V,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} := by
  have hc : ∀ x y : Idx D N → ℂ, Continuous fun h : Idx D N → Idx D N → ℂ =>
      ‖resFactorEval (x, y, Λ, z) (symArr h)‖ := by
    intro x y
    refine Continuous.norm ?_
    simp only [resFactorEval, dotProduct, Matrix.mulVec]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul
      (continuous_finsetSum _ fun m _ =>
        ((contDiff_res_symArr Λ hΛ z hz k m 0).continuous).mul continuous_const)
  have e : {h : Idx D N → Idx D N → ℂ | ∃ x ∈ V, ∃ y ∈ V,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} =
      ⋃ x ∈ V, ⋃ y ∈ V, {h | Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} := by
    ext h; simp
  rw [e]
  exact isOpen_biUnion fun x _ => isOpen_biUnion fun y _ =>
    isOpen_lt continuous_const (hc x y)

/-! ### Young's inequality for the moment -/

/-- `Q (x + Q)^{2p-1} + Q² (x + Q)^{2p-2} ≤ x^{2p}/2 + 2 (2^{2p+2} + 1)^{2p} Q^{2p}`. -/
private lemma L3_young {x Q : ℝ} (hx : 0 ≤ x) (hQ : 0 ≤ Q) (p : ℕ) (hp : 1 ≤ p) :
    Q * (x + Q) ^ (2 * p - 1) + Q ^ 2 * (x + Q) ^ (2 * p - 2) ≤
      x ^ (2 * p) / 2 + 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p) := by
  set L0 : ℝ := (2 : ℝ) ^ (2 * p + 2) with hL0
  have hL01 : 1 ≤ L0 := one_le_pow₀ (by norm_num)
  have hL00 : 0 < L0 := by linarith
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have e2 : 2 * (n + 1) - 2 = 2 * n := by omega
  have e3 : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [e1, e2, e3]
  have hx2 : 0 ≤ x ^ (2 * n + 2) := pow_nonneg hx _
  rcases le_or_gt x (L0 * Q) with hxQ | hxQ
  · have hs : x + Q ≤ (L0 + 1) * Q := by linarith
    have hl1 : 1 ≤ L0 + 1 := by linarith
    have a1 : Q * (x + Q) ^ (2 * n + 1) ≤ (L0 + 1) ^ (2 * n + 2) * Q ^ (2 * n + 2) := by
      calc Q * (x + Q) ^ (2 * n + 1) ≤ Q * ((L0 + 1) * Q) ^ (2 * n + 1) := by
            gcongr
        _ = (L0 + 1) ^ (2 * n + 1) * Q ^ (2 * n + 2) := by rw [mul_pow]; ring
        _ ≤ (L0 + 1) ^ (2 * n + 2) * Q ^ (2 * n + 2) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (by omega)) (by positivity)
    have a2 : Q ^ 2 * (x + Q) ^ (2 * n) ≤ (L0 + 1) ^ (2 * n + 2) * Q ^ (2 * n + 2) := by
      calc Q ^ 2 * (x + Q) ^ (2 * n) ≤ Q ^ 2 * ((L0 + 1) * Q) ^ (2 * n) := by
            gcongr
        _ = (L0 + 1) ^ (2 * n) * Q ^ (2 * n + 2) := by rw [mul_pow]; ring
        _ ≤ (L0 + 1) ^ (2 * n + 2) * Q ^ (2 * n + 2) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (by omega)) (by positivity)
    linarith
  · have hQx : Q ≤ x / L0 := by rw [le_div_iff₀ hL00]; linarith
    have hs : x + Q ≤ 2 * x := by
      have : x / L0 ≤ x := div_le_self hx hL01
      linarith
    have hp2 : (2 : ℝ) ^ (2 * n + 1) * 8 ≤ L0 := by
      rw [hL0, show 2 * (n + 1) + 2 = (2 * n + 1) + 3 by omega, pow_add (2 : ℝ) (2 * n + 1) 3]
      norm_num
    have a1 : Q * (x + Q) ^ (2 * n + 1) ≤ x ^ (2 * n + 2) / 8 := by
      calc Q * (x + Q) ^ (2 * n + 1) ≤ (x / L0) * (2 * x) ^ (2 * n + 1) := by
            gcongr
        _ = (2 : ℝ) ^ (2 * n + 1) / L0 * x ^ (2 * n + 2) := by rw [mul_pow]; ring
        _ ≤ (1 / 8) * x ^ (2 * n + 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hx2
            rw [div_le_iff₀ hL00]; linarith
        _ = _ := by ring
    have hp3 : (2 : ℝ) ^ (2 * n) * 8 ≤ L0 ^ 2 := by
      have : (2 : ℝ) ^ (2 * n) * 8 ≤ L0 := by
        rw [hL0, show 2 * (n + 1) + 2 = (2 * n) + 4 by omega, pow_add]; norm_num
      nlinarith
    have hL02 : 0 < L0 ^ 2 := by positivity
    have a2 : Q ^ 2 * (x + Q) ^ (2 * n) ≤ x ^ (2 * n + 2) / 8 := by
      calc Q ^ 2 * (x + Q) ^ (2 * n) ≤ (x / L0) ^ 2 * (2 * x) ^ (2 * n) := by
            gcongr
        _ = (2 : ℝ) ^ (2 * n) / L0 ^ 2 * x ^ (2 * n + 2) := by rw [mul_pow, div_pow]; ring
        _ ≤ (1 / 8) * x ^ (2 * n + 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hx2
            rw [div_le_iff₀ hL02]; linarith
        _ = _ := by ring
    have : 0 ≤ 2 * (L0 + 1) ^ (2 * n + 2) * Q ^ (2 * n + 2) := by positivity
    linarith

/-! ### The moment `E|Z|^{2p}` -/

/-- The bound of `L3_pw_all` as a function of `x = |Z|`. -/
private def L3_RB (D N : ℕ) (θ K Γ₀ η : ℝ) (p l : ℕ) (Kc x : ℝ) : ℝ :=
  ((D : ℝ) * N)⁻¹ * ((N : ℝ)⁻¹ *
    (2 * (2 * p - 1) * (x + L3_Pz D N θ K Γ₀ η) ^ (2 * p - 2) *
      (Real.sqrt ((D * N : ℝ) * Γ₀ * η⁻¹ * (K * η⁻¹ * (K * η⁻¹ * K)) ^ 2) *
        Real.sqrt (2 * L3_SZ D N θ K Γ₀ η))) +
    3 * Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
      (36 * ((D * N : ℝ) * (K ^ 5 * Γ₀ ^ 2 * η⁻¹ ^ 2 * Real.sqrt ((D * N : ℝ) * Γ₀ * η⁻¹))) *
          (x + L3_Pz D N θ K Γ₀ η) ^ (2 * p - 1) +
        2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * η⁻¹ ^ 2))) *
          (2 * (2 * p - 1) * (x + L3_Pz D N θ K Γ₀ η) ^ (2 * p - 2) *
            ((D * N : ℝ) * Real.sqrt (2 * L3_SZ D N θ K Γ₀ η))) +
        (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * η⁻¹ * (K * η⁻¹ * (K * η⁻¹ * K)) ^ 2) *
          ((2 * L3_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 *
            (x + L3_Pz D N θ K Γ₀ η) ^ (2 * p - 1))) +
    ((l : ℝ) + 1) ^ 2 * Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 *
      ((4 * p * L3_Gt l K Γ₀) ^ l * L3_Gs K Γ₀ η 3 *
        (x + L3_Pz D N θ K Γ₀ η) ^ (2 * p - 1))))

/-- `L3_RB` is nondecreasing in `x ≥ 0`. -/
private lemma L3_RB_mono {D N : ℕ} (θ : ℝ) {K Γ₀ η : ℝ} (hK : 0 ≤ K) (hΓ₀ : 0 ≤ Γ₀)
    (hη : 0 < η) (p l : ℕ) (hp : 1 ≤ p) {Kc : ℝ} (hKc : 0 ≤ Kc) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : L3_RB D N θ K Γ₀ η p l Kc x ≤ L3_RB D N θ K Γ₀ η p l Kc y := by
  have hPz := L3_Pz_nonneg (D := D) (N := N) θ hK hΓ₀ hη
  have hp' : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hi : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hGs : 0 ≤ L3_Gs K Γ₀ η 3 := by unfold L3_Gs; positivity
  have hGt : 0 ≤ L3_Gt l K Γ₀ := by unfold L3_Gt; positivity
  have hxP : x + L3_Pz D N θ K Γ₀ η ≤ y + L3_Pz D N θ K Γ₀ η := by linarith
  have hxP0 : 0 ≤ x + L3_Pz D N θ K Γ₀ η := by linarith
  have m1 := pow_le_pow_left₀ hxP0 hxP (2 * p - 1)
  have m2 := pow_le_pow_left₀ hxP0 hxP (2 * p - 2)
  unfold L3_RB
  have hN32 : 0 ≤ (N : ℝ) ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN2 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  gcongr

/-- `w (w^{p-1} w̄^p) = |w|^{2p}`. -/
private lemma L3_zphi (w : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    w * (w ^ (p - 1) * starRingEnd ℂ w ^ p) = ((‖w‖ ^ (2 * p) : ℝ) : ℂ) := by
  have e : w * (w ^ (p - 1) * starRingEnd ℂ w ^ p) = (w * starRingEnd ℂ w) ^ p := by
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hp]
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
  push_cast
  ring

/-- The moment bound: with the expansion of each `E X_{βα} Φ h̄_{βα}` to order `l` up to `ρ`,
the bad event of the forms of probability `≤ ε₀`, and the bound of `L3_pw_all` on the good event
dominated by `Q (x + Q)^{2p-1} + Q² (x + Q)^{2p-2}`, Young's inequality gives
`E|Z|^{2p} ≤ 2 (C_p Q^{2p} + ε₀ R_c + DN ρ)`. -/
private lemma L3_mom {D N : ℕ} [NeZero D] [NeZero N] {Cc : ℕ → ℝ} (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N Cc θ μ)
    {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ} {K : ℝ} (hs : L3_Set Λ B C T z z₁ z₂ z₃ K)
    (hZd : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      L3_Z θ Λ B C T z₁ z₂ z₃ h = ((D : ℂ) * N)⁻¹ *
        (∑ β, ∑ α, L3_X Λ B C T z₁ z₂ z₃ h β α * starRingEnd ℂ (h β α)) + L3_C θ Λ B C T z₁ z₂ z₃ h)
    (p l : ℕ) (hp : 1 ≤ p) (hl : 2 ≤ l) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hcc : ∀ a b β α, 3 ≤ a + b → a + b ≤ l + 1 →
      ‖ccum (μ.map fun h => h β α) a b‖ ≤ Kc * (N : ℝ) ^ (-(((a + b : ℕ) : ℝ) / 2)))
    (ρ : ℝ) (hexp : ∀ β α, ‖(∫ h, L3_F θ Λ B C T z₁ z₂ z₃ p β α h * starRingEnd ℂ (h β α) ∂μ) -
        ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
          ccum (μ.map fun h => h β α) a (b + 1) / ((a.factorial * b.factorial : ℕ) : ℂ) *
            ∫ h, wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α) ∂μ‖ ≤
        ρ)
    (Γ ε₀ Q : ℝ) (hΓ : 1 ≤ Γ) (hε₀ : 0 ≤ ε₀) (hQ : 0 ≤ Q)
    (hbad : μ {h | ∃ x ∈ L3_V Λ B C T z₃, ∃ y ∈ L3_V Λ B C T z₃,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} ≤ ENNReal.ofReal ε₀)
    (hRB : ∀ x, 0 ≤ x → L3_RB D N θ K Γ z.im p l Kc x ≤
      Q * (x + Q) ^ (2 * p - 1) + Q ^ 2 * (x + Q) ^ (2 * p - 2)) :
    ∫ h, ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ^ (2 * p) ∂μ ≤
      2 * (2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p) +
        ε₀ * L3_RB D N θ K (L3_Gc0 K z.im) z.im p l Kc (L3_Zc D θ K z.im) +
          (D * N : ℝ) * ρ) := by
  have hprob := hμ.prob
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  set Zf : (Idx D N → Idx D N → ℂ) → ℂ := fun h => L3_Z θ Λ B C T z₁ z₂ z₃ h with hZf
  set Φf : (Idx D N → Idx D N → ℂ) → ℂ := fun h => Zf h ^ (p - 1) * starRingEnd ℂ (Zf h) ^ p
    with hΦf
  set Zc := L3_Zc D θ K z.im with hZc
  -- measurability and bounds
  have hZm : AEStronglyMeasurable Zf μ :=
    L3_aesm_sym hμ.herm (L3_cd_Z θ hs.herm B C T hz₁ hz₂ hz₃ 0).continuous
  have hZb : ∀ᵐ h ∂μ, ‖Zf h‖ ≤ Zc := by
    filter_upwards [hμ.herm] with h hh
    exact L3_Z_crude θ hs h hh
  have hZc0 : 0 ≤ Zc := by
    obtain ⟨h, hh⟩ := hμ.herm.exists
    exact (norm_nonneg _).trans (L3_Z_crude θ hs h hh)
  have hnZm : AEStronglyMeasurable (fun h => ‖Zf h‖) μ := hZm.norm
  have hpow_int : ∀ (c : ℝ) (n : ℕ), 0 ≤ c → Integrable (fun h => (‖Zf h‖ + c) ^ n) μ := by
    intro c n hc
    refine Integrable.mono' (integrable_const ((Zc + c) ^ n)) ((hnZm.add aestronglyMeasurable_const).pow n) ?_
    filter_upwards [hZb] with h hb
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  have hY : Integrable (fun h => ‖Zf h‖ ^ (2 * p)) μ := by
    have := hpow_int 0 (2 * p) le_rfl
    simpa using this
  -- `|Z|^{2p} = Z Φ`
  have hZΦ : ∀ h, Zf h * Φf h = ((‖Zf h‖ ^ (2 * p) : ℝ) : ℂ) := fun h => L3_zphi (Zf h) p hp
  have hYc : ((∫ h, ‖Zf h‖ ^ (2 * p) ∂μ : ℝ) : ℂ) = ∫ h, Zf h * Φf h ∂μ := by
    simp only [hZΦ]
    exact integral_complex_ofReal.symm
  have hZΦi : Integrable (fun h => Zf h * Φf h) μ := by
    simp only [hZΦ]
    exact hY.ofReal
  -- the terms `X_{βα} Φ h̄_{βα}`
  have hFi : ∀ β α, Integrable (fun h => L3_F θ Λ B C T z₁ z₂ z₃ p β α h *
      starRingEnd ℂ (h β α)) μ := by
    intro β α
    have hm : AEStronglyMeasurable (fun h => L3_F θ Λ B C T z₁ z₂ z₃ p β α h) μ :=
      L3_aesm_sym hμ.herm (L3_cd_F θ hs.herm B C T hz₁ hz₂ hz₃ p β α 0).continuous
    have hb : ∀ᵐ h ∂μ, ‖L3_F θ Λ B C T z₁ z₂ z₃ p β α h‖ ≤ L3_Bc D N θ 0 p K z.im := by
      filter_upwards [hμ.herm] with h hh
      have := L3_F_crude θ hs h hh β α (h β α) 0 p hp β α 0 0 le_rfl
      simp only [wirt, Function.iterate_zero, id, L3_setEntry_self h hh] at this
      exact this
    have hh1 : Integrable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h β α)) μ := by
      have hm1 : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ =>
          starRingEnd ℂ (h β α)) μ :=
        (Complex.continuous_conj.comp ((continuous_apply α).comp
          (continuous_apply β))).aestronglyMeasurable
      refine Integrable.mono' (by simpa using hμ.integrable 1 β α) hm1 ?_
      exact ae_of_all _ fun h => by simp
    exact hh1.bdd_mul hm hb
  set G : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ((D : ℂ) * N)⁻¹ *
    ∑ β, ∑ α, L3_F θ Λ B C T z₁ z₂ z₃ p β α h * starRingEnd ℂ (h β α) with hG
  have hGi : Integrable G μ :=
    (integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun α _ => hFi β α).const_mul _
  have hCe : ∀ᵐ h ∂μ, Zf h * Φf h - G h = L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h := by
    filter_upwards [hμ.herm] with h hh
    simp only [hZf, hG]
    rw [hZd h hh]
    simp only [L3_F, Finset.mul_sum, Finset.sum_mul, add_mul]
    have : ∀ β α, ((D : ℂ) * N)⁻¹ * (L3_X Λ B C T z₁ z₂ z₃ h β α * starRingEnd ℂ (h β α)) *
        Φf h = ((D : ℂ) * N)⁻¹ * (L3_X Λ B C T z₁ z₂ z₃ h β α *
          (L3_Z θ Λ B C T z₁ z₂ z₃ h ^ (p - 1) * starRingEnd ℂ (L3_Z θ Λ B C T z₁ z₂ z₃ h) ^ p) *
            starRingEnd ℂ (h β α)) := fun β α => by
      simp only [hΦf, hZf]; ring
    simp only [this]
    ring
  have hCi : Integrable (fun h => L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h) μ :=
    (hZΦi.sub hGi).congr hCe
  -- the integrands of the expansion
  set κ : ℕ → ℕ → Idx D N → Idx D N → ℂ := fun a b β α => ccum (μ.map fun h => h β α) a b
    with hκ
  have hWi : ∀ β α a b, Integrable (fun h => wirt a b
      (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α)) μ := fun β α a b =>
    L3_int_wirt θ hμ hs p hp β α β α a b
  have hESi : Integrable (fun h => L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h) μ := by
    unfold L3_ES
    exact integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        (hWi β α a b).const_mul _
  have hESint : ∫ h, L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h ∂μ =
      ∑ β, ∑ α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
        κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
          ∫ h, wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α) ∂μ := by
    unfold L3_ES
    rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        (hWi β α a b).const_mul _]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => (hWi β α a b).const_mul _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (hWi β α a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hWi β α a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact integral_const_mul _ _
  -- the decomposition of `E Z Φ`
  set r : Idx D N → Idx D N → ℂ := fun β α =>
    (∫ h, L3_F θ Λ B C T z₁ z₂ z₃ p β α h * starRingEnd ℂ (h β α) ∂μ) -
      ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
        κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
          ∫ h, wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α) ∂μ
    with hr
  have hdec : ∫ h, Zf h * Φf h ∂μ =
      (∫ h, (((D : ℂ) * N)⁻¹ * L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h +
        L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h) ∂μ) + ((D : ℂ) * N)⁻¹ * ∑ β, ∑ α, r β α := by
    have e1 : ∫ h, Zf h * Φf h ∂μ = (∫ h, G h ∂μ) + ∫ h, L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h ∂μ := by
      rw [← integral_congr_ae hCe, integral_sub hZΦi hGi]
      ring
    have e2 : ∫ h, G h ∂μ = ((D : ℂ) * N)⁻¹ *
        ∑ β, ∑ α, ∫ h, L3_F θ Λ B C T z₁ z₂ z₃ p β α h * starRingEnd ℂ (h β α) ∂μ := by
      simp only [hG]
      rw [integral_const_mul, integral_finsetSum _ fun β _ =>
        integrable_finsetSum _ fun α _ => hFi β α]
      congr 1
      refine Finset.sum_congr rfl fun β _ => ?_
      exact integral_finsetSum _ fun α _ => hFi β α
    rw [e1, e2, integral_add (hESi.const_mul _) hCi, integral_const_mul, hESint]
    simp only [hr, Finset.sum_sub_distrib, mul_sub]
    ring
  -- the pointwise bound
  set S : Set (Idx D N → Idx D N → ℂ) := {h | ∃ x ∈ L3_V Λ B C T z₃, ∃ y ∈ L3_V Λ B C T z₃,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} with hS
  have hSm : MeasurableSet S := (L3_bad_open hs.herm hs.hz.ne' _ Γ).measurableSet
  set Rc := L3_RB D N θ K (L3_Gc0 K z.im) z.im p l Kc Zc with hRc
  have h01 : ∀ β α, κ 0 1 β α = 0 := fun β α => L3_ccum01 hμ β α
  have h11 : ∀ β α, κ 1 1 β α = varProf D N θ β α := fun β α =>
    (llClass_ccum_low D N Cc θ μ hμ β α).2.1
  have h02 : ∀ β α, κ 0 2 β α = if β = α then (varProf D N θ β α : ℂ) else 0 := fun β α =>
    (llClass_ccum_low D N Cc θ μ hμ β α).2.2.2
  have hpw : ∀ᵐ h ∂μ, ‖((D : ℂ) * N)⁻¹ * L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h +
      L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h‖ ≤
      (Q * (‖Zf h‖ + Q) ^ (2 * p - 1) + Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2)) +
        S.indicator (fun _ => Rc) h := by
    filter_upwards [hμ.herm] with h hh
    have hg0 : 0 ≤ Q * (‖Zf h‖ + Q) ^ (2 * p - 1) + Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2) := by
      positivity
    by_cases hb : h ∈ S
    · rw [Set.indicator_of_mem hb]
      have hΓc := L3_Gc0_ge hs.hK hs.hz
      have hp1 := L3_pw_all θ hθ0 hθ1 hs hΓc h hh (L3_good_crude hs h hh) p l hp hl κ Kc hKc
        h01 h11 h02 (fun a b β α hab hab' => hcc a b β α hab hab')
      have hm := L3_RB_mono (D := D) (N := N) θ (Γ₀ := L3_Gc0 K z.im) hK0 (by linarith) hs.hz
        p l hp hKc
        (norm_nonneg (Zf h)) (L3_Z_crude θ hs h hh)
      have : ‖((D : ℂ) * N)⁻¹ * L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h +
          L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h‖ ≤ Rc := hp1.trans hm
      linarith
    · rw [Set.indicator_of_notMem hb, add_zero]
      have hf : ∀ x ∈ L3_V Λ B C T z₃, ∀ y ∈ L3_V Λ B C T z₃,
          ‖resFactorEval (x, y, Λ, z) h‖ ≤ Γ := by
        intro x hx y hy
        by_contra hc
        push_neg at hc
        exact hb ⟨x, hx, y, hy, by rwa [symArr_of_isHermitian h hh]⟩
      have hp1 := L3_pw_all θ hθ0 hθ1 hs hΓ h hh (L3_good_of_forms hs hh hf) p l hp hl κ Kc
        hKc h01 h11 h02 (fun a b β α hab hab' => hcc a b β α hab hab')
      exact hp1.trans (hRB _ (norm_nonneg _))
  -- integration
  have hgi : Integrable (fun h => Q * (‖Zf h‖ + Q) ^ (2 * p - 1) +
      Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2)) μ :=
    ((hpow_int Q _ hQ).const_mul Q).add ((hpow_int Q _ hQ).const_mul (Q ^ 2))
  have hIi : Integrable (fun h => S.indicator (fun _ => Rc) h) μ :=
    (integrable_const Rc).indicator hSm
  have hμS : μ.real S ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal hε₀ hbad
  have hRc0 : 0 ≤ Rc := by
    obtain ⟨h, hh⟩ := hμ.herm.exists
    have := L3_pw_all θ hθ0 hθ1 hs (L3_Gc0_ge hs.hK hs.hz) h hh (L3_good_crude hs h hh) p l hp
      hl κ Kc hKc h01 h11 h02 (fun a b β α hab hab' => hcc a b β α hab hab')
    exact (norm_nonneg _).trans (this.trans (L3_RB_mono (D := D) (N := N) θ hK0
      (by linarith [L3_Gc0_ge hs.hK hs.hz]) hs.hz p l hp hKc (norm_nonneg _)
      (L3_Z_crude θ hs h hh)))
  have hint1 : ‖∫ h, (((D : ℂ) * N)⁻¹ * L3_ES θ Λ B C T z₁ z₂ z₃ p l κ h +
      L3_C θ Λ B C T z₁ z₂ z₃ h * Φf h) ∂μ‖ ≤
      (∫ h, ‖Zf h‖ ^ (2 * p) ∂μ) / 2 + 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p) +
        ε₀ * Rc := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_ae ((hESi.const_mul _).add hCi).norm (hgi.add hIi) hpw).trans ?_
    rw [integral_add' hgi hIi, integral_indicator_const _ hSm, smul_eq_mul]
    have hy : ∫ h, (Q * (‖Zf h‖ + Q) ^ (2 * p - 1) + Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2)) ∂μ ≤
        ∫ h, (‖Zf h‖ ^ (2 * p) / 2 + 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p)) ∂μ :=
      integral_mono hgi ((hY.div_const 2).add (integrable_const _)) fun h =>
        L3_young (norm_nonneg _) hQ p hp
    rw [integral_add (hY.div_const 2) (integrable_const _), integral_div, integral_const,
      probReal_univ, one_smul] at hy
    have : μ.real S * Rc ≤ ε₀ * Rc := mul_le_mul_of_nonneg_right hμS hRc0
    linarith
  have hint2 : ‖((D : ℂ) * N)⁻¹ * ∑ β, ∑ α, r β α‖ ≤ (D * N : ℝ) * ρ := by
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have hs2 : ‖∑ β, ∑ α, r β α‖ ≤ ∑ _β : Idx D N, ∑ _α : Idx D N, ρ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => hexp β α))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul] at hs2
    push_cast at hs2
    calc ((D : ℝ) * N)⁻¹ * ‖∑ β, ∑ α, r β α‖ ≤ ((D : ℝ) * N)⁻¹ * (D * N * (D * N * ρ)) :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = (D * N : ℝ) * ρ := by field_simp
  have hYn : ∫ h, ‖Zf h‖ ^ (2 * p) ∂μ = ‖∫ h, Zf h * Φf h ∂μ‖ := by
    rw [← hYc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun h => by positivity)]
  have key : ‖∫ h, Zf h * Φf h ∂μ‖ ≤ (∫ h, ‖Zf h‖ ^ (2 * p) ∂μ) / 2 +
      2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p) + ε₀ * Rc + (D * N : ℝ) * ρ := by
    rw [hdec]
    refine (norm_add_le _ _).trans ?_
    linarith
  rw [← hYn] at key
  linarith

/-! ### The remainder of the expansion -/

/-- The bound `(4pΓ_t)^{l+1} Γ₃ (|Z| + Ψ_Z)^{2p-1}` at `Γ₀ = 6Γ` on the derivatives of order
`l + 1` of the integrand where the cutoff of level `Γ` is nonzero. -/
private def L3_Ag (D N : ℕ) (θ : ℝ) (p l : ℕ) (K Γ η : ℝ) : ℝ :=
  (4 * p * L3_Gt (l + 1) K (6 * Γ)) ^ (l + 1) * L3_Gs K (6 * Γ) η 3 *
    (L3_Cz D θ * (K ^ 4 * (6 * Γ) ^ 2 * (1 + η⁻¹) ^ 2) + L3_Pz D N θ K (6 * Γ) η) ^ (2 * p - 1)

/-- The expansion of `E X_{βα} Φ h̄_{βα}` to order `l` (Lemma 2.11 [lem:complex_cumu], (2.26)
[5.16]) with the cutoff of the forms of `V` at level `Γ`: the remainder is
`K_e (N^{-(l+2)/2} A + B_c (ε₀ + (K_k + 1)(N^{1/2} M)^{-k})^{1/2})`. -/
private lemma L3_rem (l k : ℕ) (Cc : ℕ → ℝ) : ∃ Ke Kk : ℝ, 0 ≤ Ke ∧ 0 ≤ Kk ∧
    ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)), LLClass D N Cc θ μ →
    ∀ (Λ B C T : Matrix (Idx D N) (Idx D N) ℂ) (z z₁ z₂ z₃ : ℂ) (K : ℝ), L3_Set Λ B C T z z₁ z₂ z₃ K →
    ∀ p : ℕ, 1 ≤ p → ∀ Γ M ε₀ : ℝ, 1 ≤ Γ → 0 < M → 24 * M * Γ ≤ 1 → 0 ≤ ε₀ →
    μ {h | ∃ x ∈ L3_V Λ B C T z₃, ∃ y ∈ L3_V Λ B C T z₃,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} ≤ ENNReal.ofReal ε₀ →
    ∀ β α : Idx D N, ‖(∫ h, L3_F θ Λ B C T z₁ z₂ z₃ p β α h * starRingEnd ℂ (h β α) ∂μ) -
        ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
          ccum (μ.map fun h => h β α) a (b + 1) / ((a.factorial * b.factorial : ℕ) : ℂ) *
            ∫ h, wirt a b (fun w => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w)) (h β α) ∂μ‖ ≤
      Ke * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * L3_Ag D N θ p l K Γ z.im +
        L3_Bc D N θ (l + 1) p K z.im *
          Real.sqrt (ε₀ + Kk * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
            ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)))) := by
  obtain ⟨Ke, hKe0, hKe⟩ := expansion_hp_gen l k Cc
  obtain ⟨Kk, hKk0, hKk⟩ := hpCut_ne_one_le k Cc
  refine ⟨Ke, Kk, hKe0, hKk0, ?_⟩
  intro D N θ μ hμ Λ B C T z z₁ z₂ z₃ K hs p hp Γ M ε₀ hΓ hM hMΓ hε₀ hbad β α
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  set Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ) := {(Λ, z)} with hΞ
  have hΞp : ∀ q ∈ Ξ, q.1.IsHermitian ∧ 0 < q.2.im := by
    intro q hq
    rw [hΞ, Finset.mem_singleton] at hq
    subst hq
    exact ⟨hs.herm, hs.hz⟩
  have hΞne : ∀ q ∈ Ξ, q.1.IsHermitian ∧ q.2.im ≠ 0 := fun q hq =>
    ⟨(hΞp q hq).1, (hΞp q hq).2.ne'⟩
  set V := L3_V Λ B C T z₃ with hV
  have hbad' : μ {h | ∃ q ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V,
      Γ < ‖resFactorEval (x, y, q.1, q.2) (symArr h)‖} ≤ ENNReal.ofReal ε₀ := by
    refine le_trans (measure_mono ?_) hbad
    rintro h ⟨q, hq, x, hx, y, hy, hlt⟩
    rw [hΞ, Finset.mem_singleton] at hq
    subst hq
    exact ⟨x, hx, y, hy, hlt⟩
  have hMΓ' : 4 * M * Γ ≤ 1 / 2 := by nlinarith
  have hχ := hKk D N θ μ hμ Ξ hΞp β α V (L3_e_V Λ B C T z₃ β) (L3_e_V Λ B C T z₃ α) Γ M ε₀ hM
    hMΓ' hε₀ hbad'
  have h6 : 1 ≤ 6 * Γ := by linarith
  have hPz6 := L3_Pz_nonneg (D := D) (N := N) θ hK0 (by linarith : (0 : ℝ) ≤ 6 * Γ) hs.hz
  have hGs6 : 0 ≤ L3_Gs K (6 * Γ) z.im 3 := by
    unfold L3_Gs; have := inv_nonneg.mpr hs.hz.le; have : (0 : ℝ) ≤ 6 * Γ := by linarith
    positivity
  have hGt6 : 0 ≤ L3_Gt (l + 1) K (6 * Γ) := by
    unfold L3_Gt; have : (0 : ℝ) ≤ 6 * Γ := by linarith
    positivity
  have hA0 : 0 ≤ L3_Ag D N θ p l K Γ z.im := by
    unfold L3_Ag
    have := L3_Cz_nonneg D θ
    have := inv_nonneg.mpr hs.hz.le
    have : (0 : ℝ) ≤ 6 * Γ := by linarith
    positivity
  have hA : ∀ a b : ℕ, a + b = l + 1 → ∀ h : Idx D N → Idx D N → ℂ,
      (Matrix.of h).IsHermitian → hpCut Ξ V Γ β α h ≠ 0 → ∀ w : ℂ, ‖w‖ ≤ M →
      ‖wirt a b (fun w' => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w')) w‖ ≤
        L3_Ag D N θ p l K Γ z.im := by
    intro a b hab h hh hc w hw
    have hf := hpCut_ne_zero_le Ξ hΞp h hh β α V (L3_e_V Λ B C T z₃ β) (L3_e_V Λ B C T z₃ α) M Γ
      (by linarith) hMΓ hc w hw
    have hh' := L3_slice_herm h hh β α w
    have hg : L3_good Λ z (L3_U Λ B C T z₃) (6 * Γ) (setEntry h β α w) :=
      L3_good_of_forms hs hh' fun x hx y hy => hf (Λ, z) (Finset.mem_singleton_self _) x hx y hy
    have hj := L3_jet_F θ hs h6 h hh β α w hg (l + 1) p hp β α a b hab.le
    rw [hab] at hj
    refine hj.trans ?_
    have hZ := L3_Z_good θ hs h6 _ hh' hg
    unfold L3_Ag
    gcongr
  have hB : ∀ a b : ℕ, a + b ≤ l + 1 → ∀ h : Idx D N → Idx D N → ℂ,
      (Matrix.of h).IsHermitian → ∀ w : ℂ,
      ‖wirt a b (fun w' => L3_F θ Λ B C T z₁ z₂ z₃ p β α (setEntry h β α w')) w‖ ≤
        L3_Bc D N θ (l + 1) p K z.im := fun a b hab h hh w =>
    L3_F_crude θ hs h hh β α w (l + 1) p hp β α a b hab
  have hσ : 0 ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hM.le) _
  exact hKe D N θ μ hμ β α (L3_F θ Λ B C T z₁ z₂ z₃ p β α) (hpCut Ξ V Γ β α) M
    (L3_Ag D N θ p l K Γ z.im) (L3_Bc D N θ (l + 1) p K z.im)
    (ε₀ + Kk * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)))
    (L3_cd_F θ hs.herm B C T hz₁ hz₂ hz₃ p β α (l + 1))
    ((hpCut_contDiff Ξ hΞne V Γ β α (l + 1)).comp (L3_contDiff_symArr _))
    (hpCut_mem_Icc Ξ V Γ β α) (hpCut_setEntry Ξ V Γ β α) hM hA0
    (by positivity) hA hB hχ

/-! ### The bounds in the scale `Ψ = N⁻¹ η⁻³` -/

/-- `i^a ≤ E^{b-a} i^b` for `a ≤ b` when `1 ≤ E i`. -/
private lemma L3_ipow {i E : ℝ} (hi : 0 ≤ i) (hE : 1 ≤ E * i) {a b : ℕ} (hab : a ≤ b) :
    i ^ a ≤ E ^ (b - a) * i ^ b := by
  calc i ^ a = i ^ a * 1 := (mul_one _).symm
    _ ≤ i ^ a * (E * i) ^ (b - a) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hE) (pow_nonneg hi _)
    _ = E ^ (b - a) * i ^ b := by
        rw [mul_pow, show i ^ b = i ^ a * i ^ (b - a) by rw [← pow_add, Nat.add_sub_cancel' hab]]
        ring

/-- `N^{-3/2} √y = √(N⁻³ y)`. -/
private lemma L3_rpow32 {n : ℝ} (hn : 0 ≤ n) {y : ℝ} :
    n ^ (-((3 : ℝ) / 2)) * Real.sqrt y = Real.sqrt ((n ^ 3)⁻¹ * y) := by
  rw [Real.sqrt_mul (inv_nonneg.mpr (pow_nonneg hn 3))]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.inv_rpow (pow_nonneg hn 3), ← Real.rpow_natCast,
    ← Real.rpow_mul hn, ← Real.rpow_neg hn]
  norm_num

/-- `N^{-2} = (N²)⁻¹`. -/
private lemma L3_rpow2 {n : ℝ} (hn : 0 ≤ n) : n ^ (-(2 : ℝ)) = (n ^ 2)⁻¹ := by
  rw [Real.rpow_neg hn, Real.rpow_two]

/-- The constant of the bound `S_Z ≤ C_s Γ₀³ (DN)⁻¹ η⁻⁷`. -/
private def L3_Cs (D : ℕ) (Cz2 K E₀ : ℝ) : ℝ := 576 * D * Cz2 * K ^ 8 * (1 + E₀) ^ 7

private lemma L3_Cs_nonneg (D : ℕ) {Cz2 K E₀ : ℝ} (hC : 0 ≤ Cz2) (hK : 0 ≤ K) (hE : 0 ≤ E₀) :
    0 ≤ L3_Cs D Cz2 K E₀ := by
  unfold L3_Cs; positivity

private lemma L3_Cz2_nonneg (D : ℕ) (θ : ℝ) : 0 ≤ L3_Cz2 D θ := by
  unfold L3_Cz2; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- `S_Z ≤ C_s Γ₀³ (DN)⁻¹ η⁻⁷` for `η ≤ E₀`. -/
private lemma L3_SZ_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K Γ₀ η E₀ Cz2 : ℝ}
    (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (hηE : η ≤ E₀) (hC : L3_Cz2 D θ ≤ Cz2) :
    L3_SZ D N θ K Γ₀ η ≤ L3_Cs D Cz2 K E₀ * Γ₀ ^ 3 * ((D : ℝ) * N)⁻¹ * (η⁻¹) ^ 7 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hd : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  set i := η⁻¹ with hi
  have hi0 : 0 < i := inv_pos.mpr hη
  have hE1 : 1 ≤ E₀ * i := by
    have h1 := mul_le_mul_of_nonneg_right hηE hi0.le
    have h2 : η * i = 1 := mul_inv_cancel₀ hη.ne'
    linarith
  have hs : 1 + i ≤ (1 + E₀) * i := by linarith
  set u := ((D : ℝ) * N)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hw : u ^ 2 * ((D : ℝ) * N) = u := by rw [hu]; field_simp
  have hC0 := L3_Cz2_nonneg D θ
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  unfold L3_SZ L3_S1 L3_Cs
  rw [← hi, ← hu, hw]
  have h7 : (1 + i) ^ 7 ≤ (1 + E₀) ^ 7 * i ^ 7 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hs 7
  calc 16 * (D : ℝ) * L3_Cz2 D θ * (36 * K ^ 8 * Γ₀ ^ 3 * (u * (1 + i) ^ 7))
      ≤ 16 * (D : ℝ) * Cz2 * (36 * K ^ 8 * Γ₀ ^ 3 * (u * ((1 + E₀) ^ 7 * i ^ 7))) := by
        gcongr
        exact mul_nonneg (by positivity) (hC0.trans hC)
    _ = _ := by ring

/-- `Ψ_Z ≤ 3 C_z K⁴ (1 + E₀)⁴ Γ₀ N⁻¹ η⁻³` for `N⁻¹ ≤ η ≤ E₀`. -/
private lemma L3_Pz_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K Γ₀ η E₀ Cz : ℝ}
    (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (hηE : η ≤ E₀) (hNη : (N : ℝ)⁻¹ ≤ η)
    (hC : L3_Cz D θ ≤ Cz) :
    L3_Pz D N θ K Γ₀ η ≤ 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * Γ₀ * ((N : ℝ)⁻¹ * (η⁻¹) ^ 3) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  set i := η⁻¹ with hi
  have hi0 : 0 < i := inv_pos.mpr hη
  have hηi : η * i = 1 := mul_inv_cancel₀ hη.ne'
  have hE1 : 1 ≤ E₀ * i := by
    have h1 := mul_le_mul_of_nonneg_right hηE hi0.le
    linarith
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hs : 1 + i ≤ (1 + E₀) * i := by linarith
  set m := (N : ℝ)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.mpr hn
  have hni : m * i ≤ 1 := by nlinarith
  set u := ((D : ℝ) * N)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hum : u ≤ m := by
    rw [hu, hm, mul_inv]
    exact mul_le_of_le_one_left hm0.le (inv_le_one_of_one_le₀ hd1)
  have hCz0 : 0 ≤ L3_Cz D θ := L3_Cz_nonneg D θ
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hE4 : (1 + E₀) ^ 3 ≤ (1 + E₀) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : (1 + i) ^ 3 ≤ (1 + E₀) ^ 3 * i ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hs 3
  have h4 : (1 + i) ^ 4 ≤ (1 + E₀) ^ 4 * i ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hs 4
  have t1 : 2 * K ^ 4 * Γ₀ * (u * (1 + i) ^ 3) ≤ 2 * (K ^ 4 * (1 + E₀) ^ 4 * Γ₀ * (m * i ^ 3)) := by
    calc 2 * K ^ 4 * Γ₀ * (u * (1 + i) ^ 3) ≤ 2 * K ^ 4 * Γ₀ * (m * ((1 + E₀) ^ 4 * i ^ 3)) := by
          gcongr
          exact h3.trans (mul_le_mul_of_nonneg_right hE4 (by positivity))
      _ = _ := by ring
  have t2 : K ^ 4 * (u ^ 2 * (1 + i) ^ 4) ≤ K ^ 4 * (1 + E₀) ^ 4 * Γ₀ * (m * i ^ 3) := by
    have hui : u * i ≤ 1 := (mul_le_mul_of_nonneg_right hum hi0.le).trans hni
    calc K ^ 4 * (u ^ 2 * (1 + i) ^ 4) ≤ K ^ 4 * (u ^ 2 * ((1 + E₀) ^ 4 * i ^ 4)) := by gcongr
      _ = K ^ 4 * (1 + E₀) ^ 4 * (u * (u * i) * i ^ 3) := by ring
      _ ≤ K ^ 4 * (1 + E₀) ^ 4 * (m * 1 * i ^ 3) := by gcongr
      _ = K ^ 4 * (1 + E₀) ^ 4 * 1 * (m * i ^ 3) := by ring
      _ ≤ _ := by gcongr
  unfold L3_Pz L3_P1
  rw [← hi, ← hu]
  calc L3_Cz D θ * (2 * K ^ 4 * Γ₀ * (u * (1 + i) ^ 3) + K ^ 4 * (u ^ 2 * (1 + i) ^ 4))
      ≤ Cz * (3 * (K ^ 4 * (1 + E₀) ^ 4 * Γ₀ * (m * i ^ 3))) :=
        mul_le_mul hC (by linarith) (by positivity) (hCz0.trans hC)
    _ = _ := by ring

/-- `i^a ≤ E^c i^b` for `a ≤ b`, `b - a ≤ c` when `1 ≤ E` and `1 ≤ E i`. -/
private lemma L3_ipow' {i E : ℝ} (hi : 0 ≤ i) (hE1 : 1 ≤ E) (hE : 1 ≤ E * i) {a b c : ℕ}
    (hab : a ≤ b) (hc : b - a ≤ c) : i ^ a ≤ E ^ c * i ^ b :=
  (L3_ipow hi hE hab).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hE1 hc)
    (pow_nonneg hi _))

private lemma L3_le_sq1 {t : ℝ} (ht : 0 ≤ t) : t ≤ (1 + t) ^ 2 := by nlinarith

/-- The constant `K_q` of the scale `Q = K_q Γ₀^{l+4} N⁻¹ η⁻³` of the terms of order `≤ l`. -/
private def L3_Kq (D : ℕ) (p l : ℕ) (Kc Cz Cz2 K E₀ : ℝ) : ℝ :=
  108 * Kc * K ^ 5 * D * (1 + E₀) +
    12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) +
    ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l * K ^ 3 * (1 + E₀) +
    (2 * (2 * p - 1) * (1 + 2 * L3_Cs D Cz2 K E₀ * K ^ 6) +
      96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * L3_Cs D Cz2 K E₀) * (1 + E₀)) +
    3 * Cz * K ^ 4 * (1 + E₀) ^ 4 + 1

set_option maxHeartbeats 1000000 in
/-- The bound of `L3_pw_all` in the scale `Ψ = N⁻¹ η⁻³`: for `N⁻¹ ≤ η ≤ E₀` and
`Q = K_q Γ₀^{l+4} Ψ`, `L3_RB(x) ≤ Q (x + Q)^{2p-1} + Q² (x + Q)^{2p-2}`. -/
private lemma L3_RB_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K Γ₀ η E₀ Cz Cz2 Kc : ℝ}
    (p l : ℕ) (hp : 1 ≤ p) (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (hηE : η ≤ E₀)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hKc : 0 ≤ Kc) (hCz : L3_Cz D θ ≤ Cz) (hCz2 : L3_Cz2 D θ ≤ Cz2)
    (x : ℝ) (hx : 0 ≤ x) :
    L3_RB D N θ K Γ₀ η p l Kc x ≤
      (L3_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 3)) *
          (x + L3_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 3)) ^ (2 * p - 1) +
        (L3_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 3)) ^ 2 *
          (x + L3_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 3)) ^
            (2 * p - 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hCz0 : 0 ≤ Cz := (L3_Cz_nonneg D θ).trans hCz
  have hCz20 : 0 ≤ Cz2 := (L3_Cz2_nonneg D θ).trans hCz2
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hE1 : (1 : ℝ) ≤ 1 + E₀ := by linarith
  set i := η⁻¹ with hi
  have hi0 : 0 < i := inv_pos.mpr hη
  have hηi : η * i = 1 := mul_inv_cancel₀ hη.ne'
  have hEi : 1 ≤ (1 + E₀) * i := by nlinarith
  set m := (N : ℝ)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.mpr hn
  set u := ((D : ℝ) * N)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hum : u ≤ m := by
    rw [hu, hm, mul_inv]
    exact mul_le_of_le_one_left hm0.le (inv_le_one_of_one_le₀ hd1)
  have hudn : u * ((D : ℝ) * N) = 1 := by rw [hu]; field_simp
  have hmn : m * N = 1 := by rw [hm]; field_simp
  set Cs := L3_Cs D Cz2 K E₀ with hCs
  have hCs0 : 0 ≤ Cs := L3_Cs_nonneg D hCz20 hK0 hE0
  set Ψ := m * i ^ 3 with hΨ
  have hΨ0 : 0 ≤ Ψ := by positivity
  set Kq := L3_Kq D p l Kc Cz Cz2 K E₀ with hKq
  set Q := Kq * Γ₀ ^ (l + 4) * Ψ with hQ
  set Pz := L3_Pz D N θ K Γ₀ η with hPz
  have hPz0 : 0 ≤ Pz := L3_Pz_nonneg θ hK0 hΓ0 hη
  have hPzle : Pz ≤ 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * Γ₀ * Ψ := L3_Pz_le θ hK hΓ hη hηE hNη hCz
  have hSZ : L3_SZ D N θ K Γ₀ η ≤ Cs * Γ₀ ^ 3 * u * i ^ 7 := L3_SZ_le θ hK hΓ hη hηE hCz2
  have hSZ0 : 0 ≤ L3_SZ D N θ K Γ₀ η := by
    unfold L3_SZ L3_S1
    have := L3_Cz2_nonneg D θ
    positivity
  set S := Real.sqrt ((D * N : ℝ) * Γ₀ * i) with hS
  set sF := Real.sqrt ((D * N : ℝ) * Γ₀ * i * (K * i * (K * i * K)) ^ 2) with hsF
  set sS := Real.sqrt (2 * L3_SZ D N θ K Γ₀ η) with hsS
  set n32 := (N : ℝ) ^ (-((3 : ℝ) / 2)) with hn32
  have hn320 : 0 ≤ n32 := Real.rpow_nonneg hn.le _
  have hn2 : (N : ℝ) ^ (-(2 : ℝ)) = m ^ 2 := by rw [L3_rpow2 hn.le, hm, inv_pow]
  have hn3 : ((N : ℝ) ^ 3)⁻¹ = m ^ 3 := by rw [hm, inv_pow]
  have hDΓ : (D : ℝ) * Γ₀ ≤ (D * Γ₀) ^ 2 :=
    le_self_pow₀ (one_le_mul_of_one_le_of_one_le hd1 hΓ) two_ne_zero
  -- the square-root bounds
  have sb1 : n32 * S ≤ D * Γ₀ * (1 + E₀) * m * i := by
    rw [hn32, L3_rpow32 hn.le, hn3]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : m ^ 3 * ((D * N : ℝ) * Γ₀ * i) = D * Γ₀ * m ^ 2 * i := by
      linear_combination (D * Γ₀ * m ^ 2 * i) * hmn
    rw [e]
    have h2 : i ≤ (1 + E₀) ^ 2 * i ^ 2 := by
      simpa using L3_ipow' hi0.le hE1 hEi (a := 1) (b := 2) (c := 2) (by norm_num) (by norm_num)
    calc (D : ℝ) * Γ₀ * m ^ 2 * i ≤ (D * Γ₀) ^ 2 * m ^ 2 * ((1 + E₀) ^ 2 * i ^ 2) := by
          gcongr
      _ = _ := by ring
  have sb2 : n32 * sF ≤ D * Γ₀ * K ^ 3 * (1 + E₀) * m * i ^ 3 := by
    rw [hn32, L3_rpow32 hn.le, hn3]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : m ^ 3 * ((D * N : ℝ) * Γ₀ * i * (K * i * (K * i * K)) ^ 2) =
        D * Γ₀ * K ^ 6 * m ^ 2 * i ^ 5 := by
      linear_combination (D * Γ₀ * K ^ 6 * m ^ 2 * i ^ 5) * hmn
    rw [e]
    have h2 : i ^ 5 ≤ (1 + E₀) ^ 2 * i ^ 6 :=
      L3_ipow' hi0.le hE1 hEi (a := 5) (b := 6) (c := 2) (by norm_num) (by norm_num)
    calc (D : ℝ) * Γ₀ * K ^ 6 * m ^ 2 * i ^ 5 ≤ (D * Γ₀) ^ 2 * K ^ 6 * m ^ 2 *
          ((1 + E₀) ^ 2 * i ^ 6) := by gcongr
      _ = _ := by ring
  have sb3 : sF * sS ≤ (1 + 2 * Cs * K ^ 6) * Γ₀ ^ 2 * i ^ 6 := by
    rw [hsF, hsS, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc (D * N : ℝ) * Γ₀ * i * (K * i * (K * i * K)) ^ 2 * (2 * L3_SZ D N θ K Γ₀ η)
        ≤ (D * N : ℝ) * Γ₀ * i * (K * i * (K * i * K)) ^ 2 * (2 * (Cs * Γ₀ ^ 3 * u * i ^ 7)) := by
          gcongr
      _ = 2 * Cs * K ^ 6 * Γ₀ ^ 4 * i ^ 12 * (u * ((D : ℝ) * N)) := by ring
      _ = 2 * Cs * K ^ 6 * Γ₀ ^ 4 * i ^ 12 := by rw [hudn, mul_one]
      _ ≤ ((1 + 2 * Cs * K ^ 6) * Γ₀ ^ 2 * i ^ 6) ^ 2 := by
          have : 2 * Cs * K ^ 6 ≤ (1 + 2 * Cs * K ^ 6) ^ 2 := L3_le_sq1 (by positivity)
          have h4 : 0 ≤ Γ₀ ^ 4 * i ^ 12 := by positivity
          calc 2 * Cs * K ^ 6 * Γ₀ ^ 4 * i ^ 12 = 2 * Cs * K ^ 6 * (Γ₀ ^ 4 * i ^ 12) := by ring
            _ ≤ (1 + 2 * Cs * K ^ 6) ^ 2 * (Γ₀ ^ 4 * i ^ 12) := mul_le_mul_of_nonneg_right this h4
            _ = _ := by ring
  have sb4 : n32 * sS ≤ (1 + 2 * Cs) * Γ₀ ^ 2 * (1 + E₀) * m ^ 2 * i ^ 4 := by
    rw [hn32, L3_rpow32 hn.le, hn3]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc m ^ 3 * (2 * L3_SZ D N θ K Γ₀ η) ≤ m ^ 3 * (2 * (Cs * Γ₀ ^ 3 * u * i ^ 7)) := by gcongr
      _ ≤ m ^ 3 * (2 * (Cs * Γ₀ ^ 3 * m * i ^ 7)) := by gcongr
      _ ≤ m ^ 3 * (2 * (Cs * Γ₀ ^ 4 * m * ((1 + E₀) ^ 2 * i ^ 8))) := by
          have h1 : Γ₀ ^ 3 ≤ Γ₀ ^ 4 := pow_le_pow_right₀ hΓ (by norm_num)
          have h2 : i ^ 7 ≤ (1 + E₀) ^ 2 * i ^ 8 :=
            L3_ipow' hi0.le hE1 hEi (a := 7) (b := 8) (c := 2) (by norm_num) (by norm_num)
          gcongr
      _ = 2 * Cs * (Γ₀ ^ 4 * (1 + E₀) ^ 2 * m ^ 4 * i ^ 8) := by ring
      _ ≤ (1 + 2 * Cs) ^ 2 * (Γ₀ ^ 4 * (1 + E₀) ^ 2 * m ^ 4 * i ^ 8) := by
          have : 2 * Cs ≤ (1 + 2 * Cs) ^ 2 := L3_le_sq1 (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  -- the coefficients of `(x + Ψ_Z)^{2p-1}` and `(x + Ψ_Z)^{2p-2}`
  set Y₁ := (x + Pz) ^ (2 * p - 1) with hY₁
  set Y₂ := (x + Pz) ^ (2 * p - 2) with hY₂
  have hGt : L3_Gt l K Γ₀ = (3 + l) * K * Γ₀ := rfl
  have hGs : L3_Gs K Γ₀ η 3 = K ^ 3 * Γ₀ * i ^ 2 := by simp [L3_Gs, hi]
  set c₁ := 108 * Kc * K ^ 5 * Γ₀ ^ 2 * i ^ 2 * (n32 * S) +
      3 * Kc * (2 * ((3 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * (n32 * sF) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * m * ((4 * p * ((3 + l) * K * Γ₀)) ^ l * (K ^ 3 * Γ₀ * i ^ 2))
    with hc₁
  set c₂ := 2 * (2 * p - 1) * (u * m) * (sF * sS) +
      96 * (2 * p - 1) * Kc * K ^ 4 * Γ₀ ^ 2 * i ^ 2 * (n32 * sS) with hc₂
  have hRB : L3_RB D N θ K Γ₀ η p l Kc x = c₁ * Y₁ + c₂ * Y₂ := by
    unfold L3_RB
    rw [← hPz, ← hi, ← hS, ← hsF, ← hsS, ← hn32, hn2, hGt, hGs, ← hY₁, ← hY₂, ← hu, ← hm]
    have e1 : u * ((D * N : ℝ)) = 1 := hudn
    linear_combination (3 * Kc * n32 * (36 * (K ^ 5 * Γ₀ ^ 2 * i ^ 2 * S) * Y₁ +
      2 * (2 * (4 * (K * Γ₀) * (K ^ 3 * Γ₀ * i ^ 2))) * (2 * (2 * p - 1) * Y₂ * sS) +
      sF * ((2 * ((3 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * Y₁)) +
      ((l : ℝ) + 1) ^ 2 * Kc * m ^ 2 * (((D : ℝ) * N) * ((4 * p * ((3 + l) * K * Γ₀)) ^ l *
        (K ^ 3 * Γ₀ * i ^ 2) * Y₁))) * e1 + (((l : ℝ) + 1) ^ 2 * Kc * D * m *
          ((4 * p * ((3 + l) * K * Γ₀)) ^ l * (K ^ 3 * Γ₀ * i ^ 2) * Y₁)) * hmn
  -- the bounds on the coefficients
  have hΓl : Γ₀ ^ 3 ≤ Γ₀ ^ (l + 4) := pow_le_pow_right₀ hΓ (by omega)
  have hΓl1 : Γ₀ ^ (l + 1) ≤ Γ₀ ^ (l + 4) := pow_le_pow_right₀ hΓ (by omega)
  have hΓ1 : Γ₀ ≤ Γ₀ ^ (l + 4) := by
    calc Γ₀ = Γ₀ ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hΓ (by omega)
  have hΓ4 : Γ₀ ^ 4 ≤ (Γ₀ ^ (l + 4)) ^ 2 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hΓ (by omega)
  have hi2 : i ^ 2 ≤ (1 + E₀) * i ^ 3 := by
    simpa using L3_ipow' hi0.le hE1 hEi (a := 2) (b := 3) (c := 1) (by norm_num) (by norm_num)
  have hc₁le : c₁ ≤ (108 * Kc * K ^ 5 * D * (1 + E₀) +
      12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l * K ^ 3 * (1 + E₀)) *
        Γ₀ ^ (l + 4) * Ψ := by
    have a1 : 108 * Kc * K ^ 5 * Γ₀ ^ 2 * i ^ 2 * (n32 * S) ≤
        108 * Kc * K ^ 5 * D * (1 + E₀) * Γ₀ ^ (l + 4) * Ψ := by
      calc 108 * Kc * K ^ 5 * Γ₀ ^ 2 * i ^ 2 * (n32 * S) ≤
            108 * Kc * K ^ 5 * Γ₀ ^ 2 * i ^ 2 * (D * Γ₀ * (1 + E₀) * m * i) := by gcongr
        _ = 108 * Kc * K ^ 5 * D * (1 + E₀) * Γ₀ ^ 3 * Ψ := by rw [hΨ]; ring
        _ ≤ _ := by gcongr
    have a2 : 3 * Kc * (2 * ((3 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * (n32 * sF) ≤
        12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) *
          Γ₀ ^ (l + 4) * Ψ := by
      calc 3 * Kc * (2 * ((3 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * (n32 * sF) ≤
            3 * Kc * (2 * ((3 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 *
              (D * Γ₀ * K ^ 3 * (1 + E₀) * m * i ^ 3) := by gcongr
        _ = 12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) *
              Γ₀ ^ 3 * Ψ := by rw [hΨ]; ring
        _ ≤ _ := by gcongr
    have a3 : ((l : ℝ) + 1) ^ 2 * Kc * D * m * ((4 * p * ((3 + l) * K * Γ₀)) ^ l *
        (K ^ 3 * Γ₀ * i ^ 2)) ≤ ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l *
          K ^ 3 * (1 + E₀) * Γ₀ ^ (l + 4) * Ψ := by
      calc ((l : ℝ) + 1) ^ 2 * Kc * D * m * ((4 * p * ((3 + l) * K * Γ₀)) ^ l *
            (K ^ 3 * Γ₀ * i ^ 2)) ≤ ((l : ℝ) + 1) ^ 2 * Kc * D * m *
              ((4 * p * ((3 + l) * K * Γ₀)) ^ l * (K ^ 3 * Γ₀ * ((1 + E₀) * i ^ 3))) := by
            gcongr
        _ = ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l * K ^ 3 * (1 + E₀) *
              Γ₀ ^ (l + 1) * Ψ := by
            have hpw : (4 * (p : ℝ) * ((3 + l) * K * Γ₀)) ^ l =
                (4 * p * ((3 + l) * K)) ^ l * Γ₀ ^ l := by
              rw [← mul_pow]; congr 1; ring
            rw [hΨ, hpw]; ring
        _ ≤ _ := by gcongr
    linarith
  have hc₂le : c₂ ≤ (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
      96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀)) * (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2 := by
    have hum2 : u * m ≤ m ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hum hm0.le
    have a1 : 2 * (2 * p - 1) * (u * m) * (sF * sS) ≤
        2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) * Γ₀ ^ 4 * Ψ ^ 2 := by
      calc 2 * (2 * p - 1) * (u * m) * (sF * sS) ≤
            2 * (2 * p - 1) * m ^ 2 * ((1 + 2 * Cs * K ^ 6) * Γ₀ ^ 2 * i ^ 6) := by
            gcongr
        _ ≤ 2 * (2 * p - 1) * m ^ 2 * ((1 + 2 * Cs * K ^ 6) * Γ₀ ^ 4 * i ^ 6) := by
            have : Γ₀ ^ 2 ≤ Γ₀ ^ 4 := pow_le_pow_right₀ hΓ (by norm_num)
            gcongr
        _ = _ := by rw [hΨ]; ring
    have a2 : 96 * (2 * p - 1) * Kc * K ^ 4 * Γ₀ ^ 2 * i ^ 2 * (n32 * sS) ≤
        96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀) * Γ₀ ^ 4 * Ψ ^ 2 := by
      calc 96 * (2 * p - 1) * Kc * K ^ 4 * Γ₀ ^ 2 * i ^ 2 * (n32 * sS) ≤
            96 * (2 * p - 1) * Kc * K ^ 4 * Γ₀ ^ 2 * i ^ 2 *
              ((1 + 2 * Cs) * Γ₀ ^ 2 * (1 + E₀) * m ^ 2 * i ^ 4) := by gcongr
        _ = _ := by rw [hΨ]; ring
    have h4 : Γ₀ ^ 4 * Ψ ^ 2 ≤ (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2 :=
      mul_le_mul_of_nonneg_right hΓ4 (by positivity)
    have hk1 : 0 ≤ 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) := by positivity
    have hk2 : 0 ≤ 96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀) := by positivity
    calc c₂ ≤ 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) * Γ₀ ^ 4 * Ψ ^ 2 +
          96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀) * Γ₀ ^ 4 * Ψ ^ 2 :=
          add_le_add a1 a2
      _ = (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
          96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀)) * (Γ₀ ^ 4 * Ψ ^ 2) := by ring
      _ ≤ (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
          96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀)) *
            ((Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2) := mul_le_mul_of_nonneg_left h4 (add_nonneg hk1 hk2)
      _ = _ := by ring
  -- `Ψ_Z ≤ Q`, `c₁ ≤ Q`, `c₂ ≤ Q²`
  have hpos2 : 0 ≤ 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
      96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀) := by positivity
  have hpos1 : 0 ≤ 108 * Kc * K ^ 5 * D * (1 + E₀) +
      12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l * K ^ 3 * (1 + E₀) := by
    positivity
  have hpos3 : 0 ≤ 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 := by positivity
  have hKqe : Kq = (108 * Kc * K ^ 5 * D * (1 + E₀) +
      12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l * K ^ 3 * (1 + E₀)) +
      (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
        96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀)) +
      3 * Cz * K ^ 4 * (1 + E₀) ^ 4 + 1 := by
    rw [hKq, hCs]; unfold L3_Kq; ring
  have hKq1 : 1 ≤ Kq := by rw [hKqe]; linarith
  have hPQ : Pz ≤ Q := by
    refine hPzle.trans ?_
    rw [hQ]
    calc 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * Γ₀ * Ψ = 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * (Γ₀ * Ψ) := by
          ring
      _ ≤ 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * (Γ₀ ^ (l + 4) * Ψ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΓ1 hΨ0) hpos3
      _ ≤ Kq * (Γ₀ ^ (l + 4) * Ψ) := by
          gcongr
          rw [hKqe]; linarith
      _ = _ := by ring
  have hc₁Q : c₁ ≤ Q := by
    refine hc₁le.trans ?_
    rw [hQ, mul_assoc, mul_assoc Kq]
    gcongr
    rw [hKqe]; linarith
  have hc₂Q : c₂ ≤ Q ^ 2 := by
    refine hc₂le.trans ?_
    rw [hQ]
    have hK2 : 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
        96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀) ≤ Kq ^ 2 := by
      have : 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
          96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀) ≤ Kq := by
        rw [hKqe]; linarith
      exact this.trans (le_self_pow₀ hKq1 two_ne_zero)
    calc (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 6) +
          96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * Cs) * (1 + E₀)) * (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2
        ≤ Kq ^ 2 * (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2 := by gcongr
      _ = _ := by ring
  -- conclusion
  have hQ0 : 0 ≤ Q := by positivity
  have hc₁0 : 0 ≤ c₁ := by
    have := Real.sqrt_nonneg ((D * N : ℝ) * Γ₀ * i)
    have := Real.sqrt_nonneg ((D * N : ℝ) * Γ₀ * i * (K * i * (K * i * K)) ^ 2)
    positivity
  have hc₂0 : 0 ≤ c₂ := by
    have := Real.sqrt_nonneg ((D * N : ℝ) * Γ₀ * i * (K * i * (K * i * K)) ^ 2)
    have := Real.sqrt_nonneg (2 * L3_SZ D N θ K Γ₀ η)
    positivity
  rw [hRB]
  have hY1 : Y₁ ≤ (x + Q) ^ (2 * p - 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hY2 : Y₂ ≤ (x + Q) ^ (2 * p - 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hY10 : 0 ≤ Y₁ := by positivity
  have hY20 : 0 ≤ Y₂ := by positivity
  exact add_le_add (mul_le_mul hc₁Q hY1 hY10 hQ0) (mul_le_mul hc₂Q hY2 hY20 (by positivity))

/-! ### The setting of Lemma 3.6 -/

/-- `‖M(z)‖ ≤ 5/4` and `|m(z)| < 1` for `‖Λ‖ ≤ 1/10` and `Im z > 0`, and `‖M(z̄)‖ = ‖M(z)‖`. -/
private lemma L3_M_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Λ : Matrix ι ι ℂ}
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z ζ : ℂ} (hz : 0 < z.im) (hζ : L3_pm z ζ) :
    opNorm (MExt Λ ζ) ≤ 5 / 4 ∧ ‖mExt Λ z‖ < 1 := by
  have e1 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  have e2 : MExt Λ z = MSol Λ z := by simp [MExt, MSol, e1]
  obtain ⟨-, hm, hM⟩ := mSol_apriori Λ hΛ hℓ z hz
  have hM' : opNorm (MExt Λ z) ≤ 5 / 4 := by
    rw [e2]
    refine hM.le.trans ?_
    have h0 : 0 ≤ opNorm Λ := norm_nonneg _
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨?_, by rw [e1]; exact hm⟩
  rcases hζ with rfl | rfl
  · exact hM'
  · have := (mExt_conj Λ hΛ z hz.ne').2
    change opNorm (MExt Λ (star z)) ≤ 5 / 4
    rw [this, L3_opNorm_conjTranspose]
    exact hM'

/-- The setting `L3_Set` for `Λ = Λ(A)` with `‖A‖ ≤ 1/20`, `|z| ≤ τ⁻¹`, `‖B‖, ‖C‖ ≤ 1` and
`T = E_a M(z₃)`, with `K = 2 + 2τ⁻¹`. -/
private lemma L3_set_inst {D N : ℕ} [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm A ≤ 1 / 20) {τ : ℝ} (hτ : 0 < τ) {z z₁ z₂ z₃ : ℂ} (hz : 0 < z.im)
    (hzn : ‖z‖ ≤ τ⁻¹) (h1 : L3_pm z z₁) (h2 : L3_pm z z₂) (h3 : L3_pm z z₃)
    (B C : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (hC : opNorm C ≤ 1) (a : Fin D) :
    L3_Set (lam D N A) B C (Ea D N a * MExt (lam D N A) z₃) z z₁ z₂ z₃ (2 + 2 * τ⁻¹) := by
  have hne : Nonempty (Idx D N) :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩, ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := (opNorm_lam_le D N A).trans (by linarith)
  have hti : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hM := (L3_M_le hΛ hℓ hz h3).1
  have hE := L3_opNorm_Ea D N a
  set T := Ea D N a * MExt (lam D N A) z₃ with hT
  have hT0 : opNorm T ≤ 5 / 4 := by
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm (Ea D N a) * opNorm (MExt (lam D N A) z₃) ≤ 1 * (5 / 4) :=
          mul_le_mul hE hM (norm_nonneg _) zero_le_one
      _ = 5 / 4 := by ring
  have hTB : opNorm (T * B) ≤ 5 / 4 := by
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm T * opNorm B ≤ 5 / 4 * 1 := mul_le_mul hT0 hB (norm_nonneg _) (by norm_num)
      _ = 5 / 4 := by ring
  have hz₃ : ‖z₃‖ = ‖z‖ := by
    rcases h3 with rfl | rfl
    · rfl
    · exact Complex.norm_conj z
  have hL : opNorm (lam D N A - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 1 / 10 + τ⁻¹ := by
    rw [sub_eq_add_neg, ← neg_smul]
    refine (opNorm_add_le _ _).trans ?_
    rw [opNorm_smul, norm_neg, hz₃]
    have h1' := L3_opNorm_one (ι := Idx D N)
    have : ‖z‖ * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ τ⁻¹ := by
      calc ‖z‖ * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ τ⁻¹ * 1 :=
            mul_le_mul hzn h1' (norm_nonneg _) hti.le
        _ = τ⁻¹ := mul_one _
    linarith
  have hTL : opNorm (T * (lam D N A - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ))) ≤
      2 + 2 * τ⁻¹ := by
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm T * opNorm (lam D N A - z₃ • (1 : Matrix (Idx D N) (Idx D N) ℂ))
        ≤ 5 / 4 * (1 / 10 + τ⁻¹) := mul_le_mul hT0 hL (norm_nonneg _) (by norm_num)
      _ ≤ 2 + 2 * τ⁻¹ := by linarith
  have hTE : ∀ x, opNorm (T * Ea D N x) ≤ 5 / 4 := by
    intro x
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm T * opNorm (Ea D N x) ≤ 5 / 4 * 1 :=
          mul_le_mul hT0 (L3_opNorm_Ea D N x) (norm_nonneg _) (by norm_num)
      _ = 5 / 4 := by ring
  have hK : (5 / 4 : ℝ) ≤ 2 + 2 * τ⁻¹ := by linarith
  have hK1 : (1 : ℝ) ≤ 2 + 2 * τ⁻¹ := by linarith
  have hXT : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, opNorm X ≤ 1 → opNorm (Xᴴ * T) ≤ 2 + 2 * τ⁻¹ := by
    intro X hX
    refine (opNorm_mul_le _ _).trans ?_
    rw [L3_opNorm_conjTranspose]
    calc opNorm X * opNorm T ≤ 1 * (5 / 4) := mul_le_mul hX hT0 (norm_nonneg _) zero_le_one
      _ ≤ _ := by linarith
  refine ⟨hΛ, hz, h1, h2, h3, hK1, hB.trans hK1, hC.trans hK1, hT0.trans hK, hTB.trans hK, hTL,
    fun x => (hTE x).trans hK, ?_⟩
  intro q
  rcases q with i | x | x
  · fin_cases i <;> simp only [L3_Qf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, L3_opNorm_conjTranspose]
    · exact L3_opNorm_one.trans hK1
    · exact hT0.trans hK
    · exact hB.trans hK1
    · exact hXT B hB
    · exact hTB.trans hK
    · exact hTL
    · exact hT0.trans hK
    · exact hC.trans hK1
    · exact hXT C hC
  · exact (L3_opNorm_Ea D N x).trans hK1
  · simp only [L3_Qf, L3_opNorm_conjTranspose]
    exact (hTE x).trans hK

/-- On Hermitian arrays, `Z = (DN)⁻¹ Σ_{β,α} X_{βα} h̄_{βα} + (the counterterms)`. -/
private lemma L3_Zd {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) (B C T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ z₃ : ℂ)
    (hz₃ : z₃.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    L3_Z θ Λ B C T z₁ z₂ z₃ h = ((D : ℂ) * N)⁻¹ *
      (∑ β, ∑ α, L3_X Λ B C T z₁ z₂ z₃ h β α * starRingEnd ℂ (h β α)) +
        L3_C θ Λ B C T z₁ z₂ z₃ h := by
  have e : ∀ β α : Idx D N, h α β = starRingEnd ℂ (h β α) := by
    intro β α
    have := hh.apply α β
    simp only [Matrix.of_apply] at this
    rw [← this]
    rfl
  have hs : ∑ β, ∑ α, L3_X Λ B C T z₁ z₂ z₃ h β α * h α β =
      ∑ β, ∑ α, L3_X Λ B C T z₁ z₂ z₃ h β α * starRingEnd ℂ (h β α) :=
    Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by rw [e β α]
  rw [L3_Z_eq θ Λ B C T hΛ z₁ z₂ z₃ hz₃ h hh, L3_ntrH, hs]

/-- On Hermitian arrays the term `underThree` is the polynomial `L3_Z` for `B = E_{a₃}`,
`C = E_{a₁}`, `T = E_{a₂} M(z₃)`. -/
private lemma L3_under_Z {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ)
    {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) (z₁ z₂ z₃ : ℂ) (hz₃ : z₃.im ≠ 0)
    (a₁ a₂ a₃ : Fin D) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    underThree Λ θ h z₁ z₂ z₃ a₁ a₂ a₃ =
      L3_Z θ Λ (Ea D N a₃) (Ea D N a₁) (Ea D N a₂ * MExt Λ z₃) z₁ z₂ z₃ h := by
  rw [L3_under_eq, L3_Z_eq θ Λ _ _ _ hΛ z₁ z₂ z₃ hz₃ h hh]

/-- `Σ_{t,x} |c_t| ≤ 8 D²` and `Σ_{t,x} |c_t|² ≤ 8 D³` for `θ ∈ [0, 1]`. -/
private lemma L3_Cz_le {D : ℕ} [NeZero D] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    L3_Cz D θ ≤ 8 * (D : ℝ) ^ 2 ∧ L3_Cz2 D θ ≤ 8 * (D : ℝ) ^ 3 := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hDi : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
  have hDi0 : 0 ≤ (D : ℝ)⁻¹ := by positivity
  have hc : ∀ t, ‖L3_cf D θ t‖ ≤ D := by
    intro t
    fin_cases t <;> simp only [L3_cf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, norm_neg, norm_inv, norm_mul,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0,
      abs_of_nonneg (sub_nonneg.mpr hθ1)]
    all_goals nlinarith
  have hcs : ∀ t, ‖L3_cf D θ t‖ ^ 2 ≤ (D : ℝ) ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (hc t) 2
  constructor
  · unfold L3_Cz
    calc ∑ t : Fin 8, ∑ _x : Fin D, ‖L3_cf D θ t‖ ≤ ∑ _t : Fin 8, ∑ _x : Fin D, (D : ℝ) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun _ _ => hc t
      _ = 8 * (D : ℝ) ^ 2 := by simp; ring
  · unfold L3_Cz2
    calc ∑ t : Fin 8, ∑ _x : Fin D, ‖L3_cf D θ t‖ ^ 2 ≤
          ∑ _t : Fin 8, ∑ _x : Fin D, (D : ℝ) ^ 2 :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun _ _ => hcs t
      _ = 8 * (D : ℝ) ^ 3 := by simp; ring

/-! ### Polynomial bounds -/

/-- `η⁻¹ ≤ N` and `N⁻¹ η⁻³ ≤ N²` for `N⁻¹ ≤ η`. -/
private lemma L3_inv_le {N : ℕ} [NeZero N] {η : ℝ} (hη : 0 < η) (hNη : (N : ℝ)⁻¹ ≤ η) :
    η⁻¹ ≤ N ∧ (N : ℝ)⁻¹ * (η⁻¹) ^ 3 ≤ (N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : η⁻¹ ≤ N := by
    have := inv_anti₀ (inv_pos.mpr hn) hNη
    rwa [inv_inv] at this
  refine ⟨h1, ?_⟩
  have h0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  calc (N : ℝ)⁻¹ * (η⁻¹) ^ 3 ≤ (N : ℝ)⁻¹ * (N : ℝ) ^ 3 := by gcongr
    _ = (N : ℝ) ^ 2 := by field_simp

/-- `Γ₀ = K² (1 + η⁻¹) ≤ 2 K² N` and `|Z| ≤ Z_c ≤ 16 C_z K⁸ N⁴`. -/
private lemma L3_Gc0_Zc_le {D N : ℕ} [NeZero N] (θ : ℝ) {K η Cz : ℝ} (hK : 1 ≤ K) (hη : 0 < η)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hCz : L3_Cz D θ ≤ Cz) :
    L3_Gc0 K η ≤ 2 * K ^ 2 * N ∧ L3_Zc D θ K η ≤ 16 * Cz * K ^ 8 * (N : ℝ) ^ 4 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨hi, -⟩ := L3_inv_le hη hNη
  have hi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith
  have h1 : 1 + η⁻¹ ≤ 2 * N := by linarith
  have hG : L3_Gc0 K η ≤ 2 * K ^ 2 * N := by
    unfold L3_Gc0
    calc K ^ 2 * (1 + η⁻¹) ≤ K ^ 2 * (2 * N) := by gcongr
      _ = _ := by ring
  have hG0 : 0 ≤ L3_Gc0 K η := by unfold L3_Gc0; positivity
  refine ⟨hG, ?_⟩
  unfold L3_Zc
  have hCz0 : 0 ≤ L3_Cz D θ := L3_Cz_nonneg D θ
  calc L3_Cz D θ * (K ^ 4 * L3_Gc0 K η ^ 2 * (1 + η⁻¹) ^ 2)
      ≤ Cz * (K ^ 4 * (2 * K ^ 2 * N) ^ 2 * (2 * N) ^ 2) := by
        gcongr
        exact hCz0.trans hCz
    _ = 16 * Cz * K ^ 8 * (N : ℝ) ^ 4 := by ring

/-- The crude constant `R_c = L3_RB(Γ₀ = K²(1 + η⁻¹), x = Z_c) ≤ 2 (W N^{l+6})^{2p}`. -/
private lemma L3_Rc_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K η E₀ Cz Cz2 Kc : ℝ}
    (p l : ℕ) (hp : 1 ≤ p) (hK : 1 ≤ K) (hη : 0 < η) (hηE : η ≤ E₀)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hKc : 0 ≤ Kc) (hCz : L3_Cz D θ ≤ Cz) (hCz2 : L3_Cz2 D θ ≤ Cz2) :
    L3_RB D N θ K (L3_Gc0 K η) η p l Kc (L3_Zc D θ K η) ≤
      2 * ((16 * Cz * K ^ 8 + L3_Kq D p l Kc Cz Cz2 K E₀ * (2 * K ^ 2) ^ (l + 4) + 1) *
        (N : ℝ) ^ (l + 6)) ^ (2 * p) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hn0 : (0 : ℝ) ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hΓ := L3_Gc0_ge hK hη
  obtain ⟨hG, hZ⟩ := L3_Gc0_Zc_le θ hK hη hNη hCz
  obtain ⟨-, hΨ⟩ := L3_inv_le hη hNη
  have hZ0 : 0 ≤ L3_Zc D θ K η := by
    unfold L3_Zc L3_Gc0
    have := L3_Cz_nonneg D θ; have := inv_nonneg.mpr hη.le
    positivity
  have hR := L3_RB_le θ p l hp hK hΓ hη hηE hNη hKc hCz hCz2 _ hZ0
  set Kq := L3_Kq D p l Kc Cz Cz2 K E₀ with hKq
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hCz0 : 0 ≤ Cz := (L3_Cz_nonneg D θ).trans hCz
  have hCz20 : 0 ≤ Cz2 := (L3_Cz2_nonneg D θ).trans hCz2
  have hKq0 : 0 ≤ Kq := by
    rw [hKq]; unfold L3_Kq
    have : (0 : ℝ) ≤ 2 * p - 1 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have := L3_Cs_nonneg D hCz20 hK0 hE0
    positivity
  set Qc := Kq * L3_Gc0 K η ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 3) with hQc
  set W := 16 * Cz * K ^ 8 + Kq * (2 * K ^ 2) ^ (l + 4) + 1 with hW
  have hN4 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ (l + 6) := pow_le_pow_right₀ hn1 (by omega)
  have hQ : Qc ≤ Kq * (2 * K ^ 2) ^ (l + 4) * (N : ℝ) ^ (l + 6) := by
    have h0 : 0 ≤ (N : ℝ)⁻¹ * (η⁻¹) ^ 3 := by have := inv_nonneg.mpr hη.le; positivity
    calc Qc ≤ Kq * (2 * K ^ 2 * N) ^ (l + 4) * (N : ℝ) ^ 2 := by
          rw [hQc]; gcongr
      _ = Kq * (2 * K ^ 2) ^ (l + 4) * (N : ℝ) ^ (l + 6) := by rw [mul_pow]; ring
  have hQ0 : 0 ≤ Qc := by rw [hQc]; have := inv_nonneg.mpr hη.le; positivity
  have hX1 : Qc ≤ W * (N : ℝ) ^ (l + 6) := by
    refine hQ.trans ?_
    have : 0 ≤ (16 * Cz * K ^ 8 + 1) * (N : ℝ) ^ (l + 6) := by positivity
    rw [hW]; nlinarith
  have hX2 : L3_Zc D θ K η + Qc ≤ W * (N : ℝ) ^ (l + 6) := by
    have : L3_Zc D θ K η ≤ 16 * Cz * K ^ 8 * (N : ℝ) ^ (l + 6) :=
      hZ.trans (mul_le_mul_of_nonneg_left hN4 (by positivity))
    have : (0 : ℝ) ≤ (N : ℝ) ^ (l + 6) := by positivity
    rw [hW]; nlinarith
  refine hR.trans ?_
  set X := W * (N : ℝ) ^ (l + 6) with hX
  have hp1 : 2 * p - 1 + 1 = 2 * p := by omega
  have hp2 : 2 * p - 2 + 2 = 2 * p := by omega
  have a1 : Qc * (L3_Zc D θ K η + Qc) ^ (2 * p - 1) ≤ X ^ (2 * p) := by
    calc Qc * (L3_Zc D θ K η + Qc) ^ (2 * p - 1) ≤ X * X ^ (2 * p - 1) := by
          gcongr
      _ = X ^ (2 * p) := by rw [← pow_succ', hp1]
  have a2 : Qc ^ 2 * (L3_Zc D θ K η + Qc) ^ (2 * p - 2) ≤ X ^ (2 * p) := by
    calc Qc ^ 2 * (L3_Zc D θ K η + Qc) ^ (2 * p - 2) ≤ X ^ 2 * X ^ (2 * p - 2) := by
          gcongr
      _ = X ^ (2 * p) := by rw [← pow_add, add_comm, hp2]
  linarith

/-- The crude bound `B_c ≤ W_b N^{l+8p}` on the derivatives of order `≤ l + 1`. -/
private lemma L3_Bc_le {D N : ℕ} [NeZero N] (θ : ℝ) {K η E₀ Cz : ℝ} (p l : ℕ) (hp : 1 ≤ p)
    (hK : 1 ≤ K) (hη : 0 < η) (hηE : η ≤ E₀) (hNη : (N : ℝ)⁻¹ ≤ η) (hCz : L3_Cz D θ ≤ Cz)
    [NeZero D] :
    L3_Bc D N θ (l + 1) p K η ≤ (8 * p * (4 + l) * K ^ 3) ^ (l + 1) * (2 * K ^ 5) *
      (16 * Cz * K ^ 8 + 6 * Cz * K ^ 6 * (1 + E₀) ^ 4) ^ (2 * p - 1) *
        (N : ℝ) ^ (l + 8 * p) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hK0 : 0 ≤ K := by linarith
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hCz0 : 0 ≤ Cz := (L3_Cz_nonneg D θ).trans hCz
  have hΓ := L3_Gc0_ge hK hη
  obtain ⟨hG, hZ⟩ := L3_Gc0_Zc_le θ hK hη hNη hCz
  obtain ⟨hi, hΨ⟩ := L3_inv_le hη hNη
  have hi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hP := L3_Pz_le θ hK hΓ hη hηE hNη hCz
  have hG0 : 0 ≤ L3_Gc0 K η := by linarith
  have hPz0 := L3_Pz_nonneg (D := D) (N := N) θ hK0 hG0 hη
  have hZ0 : 0 ≤ L3_Zc D θ K η := by
    unfold L3_Zc L3_Gc0
    have := L3_Cz_nonneg D θ
    positivity
  have t1 : 4 * p * L3_Gt (l + 1) K (L3_Gc0 K η) ≤ 8 * p * (4 + l) * K ^ 3 * N := by
    unfold L3_Gt
    push_cast
    calc 4 * (p : ℝ) * ((3 + (l + 1)) * K * L3_Gc0 K η) ≤
          4 * p * ((3 + (l + 1)) * K * (2 * K ^ 2 * N)) := by gcongr
      _ = _ := by ring
  have t2 : L3_Gs K (L3_Gc0 K η) η 3 ≤ 2 * K ^ 5 * (N : ℝ) ^ 3 := by
    unfold L3_Gs
    simp only [show (3 : ℕ) - 1 = 2 from rfl]
    calc K ^ 3 * L3_Gc0 K η * η⁻¹ ^ 2 ≤ K ^ 3 * (2 * K ^ 2 * N) * (N : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have t3 : L3_Zc D θ K η + L3_Pz D N θ K (L3_Gc0 K η) η ≤
      (16 * Cz * K ^ 8 + 6 * Cz * K ^ 6 * (1 + E₀) ^ 4) * (N : ℝ) ^ 4 := by
    have : L3_Pz D N θ K (L3_Gc0 K η) η ≤ 6 * Cz * K ^ 6 * (1 + E₀) ^ 4 * (N : ℝ) ^ 4 := by
      refine hP.trans ?_
      calc 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * L3_Gc0 K η * ((N : ℝ)⁻¹ * η⁻¹ ^ 3) ≤
            3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * (2 * K ^ 2 * N) * (N : ℝ) ^ 2 := by gcongr
        _ = 6 * Cz * K ^ 6 * (1 + E₀) ^ 4 * (N : ℝ) ^ 3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by norm_num))
            (by positivity)
    linarith
  have hGt0 : 0 ≤ 4 * p * L3_Gt (l + 1) K (L3_Gc0 K η) := by unfold L3_Gt; positivity
  have hGs0 : 0 ≤ L3_Gs K (L3_Gc0 K η) η 3 := by unfold L3_Gs; positivity
  unfold L3_Bc
  set c1 := 8 * (p : ℝ) * (4 + l) * K ^ 3 with hc1
  set c2 := 16 * Cz * K ^ 8 + 6 * Cz * K ^ 6 * (1 + E₀) ^ 4 with hc2
  calc (4 * p * L3_Gt (l + 1) K (L3_Gc0 K η)) ^ (l + 1) * L3_Gs K (L3_Gc0 K η) η 3 *
        (L3_Zc D θ K η + L3_Pz D N θ K (L3_Gc0 K η) η) ^ (2 * p - 1)
      ≤ (c1 * N) ^ (l + 1) * (2 * K ^ 5 * (N : ℝ) ^ 3) *
        (c2 * (N : ℝ) ^ 4) ^ (2 * p - 1) := by
        gcongr
    _ = c1 ^ (l + 1) * (2 * K ^ 5) *
        c2 ^ (2 * p - 1) *
          ((N : ℝ) ^ (l + 1) * (N : ℝ) ^ 3 * ((N : ℝ) ^ 4) ^ (2 * p - 1)) := by
        rw [mul_pow, mul_pow]; ring
    _ = _ := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 2
        omega

/-- The good-event constant `A ≤ W_a Γ^{l+4p} N^{4p}` for `Γ ≥ 1`. -/
private lemma L3_Ag_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K η E₀ Cz Γ : ℝ} (p l : ℕ)
    (hp : 1 ≤ p) (hK : 1 ≤ K) (hΓ : 1 ≤ Γ) (hη : 0 < η) (hηE : η ≤ E₀)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hCz : L3_Cz D θ ≤ Cz) :
    L3_Ag D N θ p l K Γ η ≤ (24 * p * (4 + l) * K) ^ (l + 1) * (6 * K ^ 3) *
      (144 * Cz * K ^ 4 + 18 * Cz * K ^ 4 * (1 + E₀) ^ 4) ^ (2 * p - 1) * Γ ^ (l + 4 * p) *
        (N : ℝ) ^ (4 * p) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hCz0 : 0 ≤ Cz := (L3_Cz_nonneg D θ).trans hCz
  obtain ⟨hi, hΨ⟩ := L3_inv_le hη hNη
  have hi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have h6 : 1 ≤ 6 * Γ := by linarith
  have hP := L3_Pz_le θ hK h6 hη hηE hNη hCz
  have hΓ2 : Γ ≤ Γ ^ 2 := le_self_pow₀ hΓ two_ne_zero
  have t1 : 4 * p * L3_Gt (l + 1) K (6 * Γ) = 24 * p * (4 + l) * K * Γ := by
    unfold L3_Gt; push_cast; ring
  have t2 : L3_Gs K (6 * Γ) η 3 ≤ 6 * K ^ 3 * Γ * (N : ℝ) ^ 2 := by
    unfold L3_Gs
    simp only [show (3 : ℕ) - 1 = 2 from rfl]
    calc K ^ 3 * (6 * Γ) * η⁻¹ ^ 2 ≤ K ^ 3 * (6 * Γ) * (N : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have t3 : L3_Cz D θ * (K ^ 4 * (6 * Γ) ^ 2 * (1 + η⁻¹) ^ 2) + L3_Pz D N θ K (6 * Γ) η ≤
      (144 * Cz * K ^ 4 + 18 * Cz * K ^ 4 * (1 + E₀) ^ 4) * Γ ^ 2 * (N : ℝ) ^ 2 := by
    have h1 : 1 + η⁻¹ ≤ 2 * N := by linarith
    have a1 : L3_Cz D θ * (K ^ 4 * (6 * Γ) ^ 2 * (1 + η⁻¹) ^ 2) ≤
        144 * Cz * K ^ 4 * Γ ^ 2 * (N : ℝ) ^ 2 := by
      have := L3_Cz_nonneg D θ
      calc L3_Cz D θ * (K ^ 4 * (6 * Γ) ^ 2 * (1 + η⁻¹) ^ 2) ≤
            Cz * (K ^ 4 * (6 * Γ) ^ 2 * (2 * N) ^ 2) := by gcongr
        _ = _ := by ring
    have a2 : L3_Pz D N θ K (6 * Γ) η ≤ 18 * Cz * K ^ 4 * (1 + E₀) ^ 4 * Γ ^ 2 * (N : ℝ) ^ 2 := by
      refine hP.trans ?_
      calc 3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * (6 * Γ) * ((N : ℝ)⁻¹ * η⁻¹ ^ 3) ≤
            3 * Cz * K ^ 4 * (1 + E₀) ^ 4 * (6 * Γ ^ 2) * (N : ℝ) ^ 2 := by gcongr
        _ = _ := by ring
    have : (144 * Cz * K ^ 4 + 18 * Cz * K ^ 4 * (1 + E₀) ^ 4) * Γ ^ 2 * (N : ℝ) ^ 2 =
        144 * Cz * K ^ 4 * Γ ^ 2 * (N : ℝ) ^ 2 +
          18 * Cz * K ^ 4 * (1 + E₀) ^ 4 * Γ ^ 2 * (N : ℝ) ^ 2 := by ring
    linarith
  have hGs0 : 0 ≤ L3_Gs K (6 * Γ) η 3 := by unfold L3_Gs; positivity
  have hs0 : 0 ≤ L3_Cz D θ * (K ^ 4 * (6 * Γ) ^ 2 * (1 + η⁻¹) ^ 2) +
      L3_Pz D N θ K (6 * Γ) η := by
    have := L3_Cz_nonneg D θ
    have := L3_Pz_nonneg (D := D) (N := N) θ hK0 (by linarith : (0 : ℝ) ≤ 6 * Γ) hη
    positivity
  unfold L3_Ag
  rw [t1]
  set c1 := 24 * (p : ℝ) * (4 + l) * K with hc1
  set c2 := 144 * Cz * K ^ 4 + 18 * Cz * K ^ 4 * (1 + E₀) ^ 4 with hc2
  calc (c1 * Γ) ^ (l + 1) * L3_Gs K (6 * Γ) η 3 *
        (L3_Cz D θ * (K ^ 4 * (6 * Γ) ^ 2 * (1 + η⁻¹) ^ 2) +
          L3_Pz D N θ K (6 * Γ) η) ^ (2 * p - 1)
      ≤ (c1 * Γ) ^ (l + 1) * (6 * K ^ 3 * Γ * (N : ℝ) ^ 2) *
        (c2 * Γ ^ 2 * (N : ℝ) ^ 2) ^ (2 * p - 1) := by
        gcongr
    _ = c1 ^ (l + 1) * (6 * K ^ 3) * c2 ^ (2 * p - 1) *
          (Γ ^ (l + 1) * Γ * (Γ ^ 2) ^ (2 * p - 1)) *
            ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ (2 * p - 1)) := by
        rw [mul_pow, mul_pow, mul_pow]; ring
    _ = _ := by
        rw [← pow_mul, ← pow_mul, ← pow_succ, ← pow_add, ← pow_add]
        congr 3
        · omega
        · omega

/-- `c ≤ N^τ` for all large `N`. -/
private lemma L3_exists_rpow_ge {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → c ≤ (N : ℝ) ^ τ :=
  Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c)

/-! ### The probability of the bad event of the forms -/

/-- The unit vector `v/|v|` (and `e_k` for `v = 0`). -/
private def L3_nrm {D N : ℕ} (k : Idx D N) (v : Idx D N → ℂ) : Idx D N → ℂ :=
  if Real.sqrt (∑ i, ‖v i‖ ^ 2) = 0 then Pi.single k 1
  else ((Real.sqrt (∑ i, ‖v i‖ ^ 2))⁻¹ : ℂ) • v

private lemma L3_nrm_unit {D N : ℕ} (k : Idx D N) (v : Idx D N → ℂ) :
    ∑ i, ‖L3_nrm k v i‖ ^ 2 = 1 := by
  unfold L3_nrm
  split_ifs with h
  · exact L3_single_sq k
  · have h0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hs := Real.sq_sqrt h0
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← Finset.mul_sum, inv_pow]
    rw [hs]
    have : ∑ i, ‖v i‖ ^ 2 ≠ 0 := by
      intro h'; apply h; rw [h', Real.sqrt_zero]
    exact inv_mul_cancel₀ this

private lemma L3_nrm_eq {D N : ℕ} (k : Idx D N) (v : Idx D N → ℂ)
    (hv : Real.sqrt (∑ i, ‖v i‖ ^ 2) ≠ 0) :
    v = ((Real.sqrt (∑ i, ‖v i‖ ^ 2) : ℝ) : ℂ) • L3_nrm k v := by
  unfold L3_nrm
  rw [if_neg hv, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hv, Complex.ofReal_one, one_smul]

/-- `psiIso ≤ 2` for `|m| < 1` and `N η ≥ 1`. -/
private lemma L3_psi_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : Matrix ι ι ℂ} {N : ℕ}
    {z : ℂ} (hz : 0 < z.im) (hm : ‖mExt Λ z‖ < 1) (hNη : (N : ℝ)⁻¹ ≤ z.im) (hN : 0 < N) :
    psiIso Λ N z ≤ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hNe : 1 ≤ (N : ℝ) * |z.im| := by
    rw [abs_of_pos hz]
    have := mul_le_mul_of_nonneg_left hNη hn.le
    rwa [mul_inv_cancel₀ hn.ne'] at this
  have hpos : 0 < (N : ℝ) * |z.im| := by linarith
  have hIm : |(mExt Λ z).im| ≤ 1 := (Complex.abs_im_le_norm _).trans hm.le
  unfold psiIso
  have h1 : |(mExt Λ z).im| / ((N : ℝ) * |z.im|) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  have h2 : 1 / ((N : ℝ) * |z.im|) ≤ 1 := by rw [div_le_one hpos]; exact hNe
  have h3 : Real.sqrt (|(mExt Λ z).im| / ((N : ℝ) * |z.im|)) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact h1
  linarith

/-- The forms of `V` exceed `Γ = 4 K² N^{τ₀}` only on the union of the events of (2.22)
[eq:aniso_local] for the pairs of normalized vectors of `V`, outside a null set: the
probability is `≤ |V|² r ≤ ((9 + 2D) DN)² r`. -/
private lemma L3_bad_le {D N : ℕ} [NeZero D] [NeZero N] {Cc : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N Cc θ μ)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm A ≤ 1 / 20) {τ τ₀ r : ℝ} (hτ : 0 < τ)
    (hτ₀ : 0 ≤ τ₀) (hr : 0 ≤ r) {z z₁ z₂ z₃ : ℂ} (hzD : z ∈ specDom τ N) (hz : 0 < z.im)
    (hNη : (N : ℝ)⁻¹ ≤ z.im) (h1 : L3_pm z z₁) (h2 : L3_pm z z₂) (h3 : L3_pm z z₃)
    (B C : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (hC : opNorm C ≤ 1) (a : Fin D)
    (hani : ∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
      μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ₀ * psiIso (lam D N A) N z <
        ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖} ≤
        ENNReal.ofReal r) :
    μ {h | ∃ x ∈ L3_V (lam D N A) B C (Ea D N a * MExt (lam D N A) z₃) z₃,
      ∃ y ∈ L3_V (lam D N A) B C (Ea D N a * MExt (lam D N A) z₃) z₃,
        4 * (2 + 2 * τ⁻¹) ^ 2 * (N : ℝ) ^ τ₀ <
          ‖resFactorEval (x, y, lam D N A, z) (symArr h)‖} ≤
      ENNReal.ofReal ((((9 + 2 * D) * (D * N) : ℕ) : ℝ) ^ 2 * r) := by
  have hne : Nonempty (Idx D N) :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩, ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  obtain ⟨k₀⟩ := hne
  have hs := L3_set_inst (D := D) (N := N) A hA hτ hz hzD.1 h1 h2 h3 B C hB hC a
  set Λ := lam D N A with hΛ
  set T := Ea D N a * MExt Λ z₃ with hT
  set V := L3_V Λ B C T z₃ with hV
  set K := 2 + 2 * τ⁻¹ with hK
  have hK1 : 1 ≤ K := hs.hK
  have hℓ : opNorm Λ ≤ 1 / 10 := (opNorm_lam_le D N A).trans (by linarith)
  obtain ⟨hM, hm⟩ := L3_M_le (lam_isHermitian D N A) hℓ hz (Or.inl rfl : L3_pm z z)
  have hψ := L3_psi_le hz hm hNη (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ₀ := Real.one_le_rpow
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) hτ₀
  -- the vectors of `V` have norm `≤ K`
  have hVn : ∀ x ∈ V, Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ K := by
    intro x hx
    obtain ⟨⟨q, k⟩, -, rfl⟩ := Finset.mem_image.mp hx
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    refine (L3_mulVec_sq _ _).trans ?_
    rw [L3_single_sq, mul_one]
    have := hs.hQ q
    have h0 : 0 ≤ opNorm (L3_Qf Λ B C T z₃ q) := norm_nonneg _
    nlinarith
  set Bad : (Idx D N → ℂ) → (Idx D N → ℂ) → Set (Idx D N → Idx D N → ℂ) := fun x y =>
    {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ₀ * psiIso Λ N z <
      ‖star (L3_nrm k₀ x) ⬝ᵥ ((res (Matrix.of h + Λ) z - MExt Λ z) *ᵥ L3_nrm k₀ y)‖} with hBad
  have hsub : {h | ∃ x ∈ V, ∃ y ∈ V, 4 * K ^ 2 * (N : ℝ) ^ τ₀ <
      ‖resFactorEval (x, y, Λ, z) (symArr h)‖} ≤ᵐ[μ] ⋃ x ∈ V, ⋃ y ∈ V, Bad x y := by
    filter_upwards [hμ.herm] with h hh hS
    obtain ⟨x, hx, y, hy, hlt⟩ := hS
    rw [symArr_of_isHermitian h hh] at hlt
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨x, hx, y, hy, ?_⟩
    by_contra hc
    simp only [hBad, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hc
    have hcz := hc z hzD
    set nx := Real.sqrt (∑ i, ‖x i‖ ^ 2) with hnx
    set ny := Real.sqrt (∑ i, ‖y i‖ ^ 2) with hny
    have hnx0 : nx ≠ 0 := by
      intro h0
      have : x = 0 := by
        have h' : ∑ i, ‖x i‖ ^ 2 = 0 := by
          rw [hnx, Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)] at h0
          exact h0
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp h' i
          (Finset.mem_univ _)
        simpa using this
      rw [this] at hlt
      simp [resFactorEval] at hlt
      linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (pow_pos (by linarith : (0 : ℝ) < K) 2))
        (by linarith : (0 : ℝ) < (N : ℝ) ^ τ₀)]
    have hny0 : ny ≠ 0 := by
      intro h0
      have : y = 0 := by
        have h' : ∑ i, ‖y i‖ ^ 2 = 0 := by
          rw [hny, Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)] at h0
          exact h0
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp h' i
          (Finset.mem_univ _)
        simpa using this
      rw [this] at hlt
      simp [resFactorEval] at hlt
      linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (pow_pos (by linarith : (0 : ℝ) < K) 2))
        (by linarith : (0 : ℝ) < (N : ℝ) ^ τ₀)]
    set u := L3_nrm k₀ x with hu
    set v := L3_nrm k₀ y with hv
    have hxu : x = (nx : ℂ) • u := L3_nrm_eq k₀ x hnx0
    have hyv : y = (ny : ℂ) • v := L3_nrm_eq k₀ y hny0
    set G := res (Matrix.of h + Λ) z with hG
    set M := MExt Λ z with hMd
    have hform : resFactorEval (x, y, Λ, z) h =
        ((nx * ny : ℝ) : ℂ) * (star u ⬝ᵥ ((G - M) *ᵥ v) + star u ⬝ᵥ (M *ᵥ v)) := by
      simp only [resFactorEval]
      rw [hxu, hyv, Matrix.sub_mulVec, dotProduct_sub, star_smul, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    have hMf : ‖star u ⬝ᵥ (M *ᵥ v)‖ ≤ 5 / 4 :=
      (L3_form_le_opNorm M u v (L3_nrm_unit k₀ x).le (L3_nrm_unit k₀ y).le).trans hM
    have hnxK : nx ≤ K := hVn x hx
    have hnyK : ny ≤ K := hVn y hy
    have hnx' : 0 ≤ nx := Real.sqrt_nonneg _
    have hny' : 0 ≤ ny := Real.sqrt_nonneg _
    have hb : ‖resFactorEval (x, y, Λ, z) h‖ ≤ 4 * K ^ 2 * (N : ℝ) ^ τ₀ := by
      rw [hform, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hnx' hny')]
      have h3 : ‖star u ⬝ᵥ ((G - M) *ᵥ v) + star u ⬝ᵥ (M *ᵥ v)‖ ≤
          (N : ℝ) ^ τ₀ * 2 + 5 / 4 := by
        refine (norm_add_le _ _).trans (add_le_add (hcz.trans ?_) hMf)
        exact mul_le_mul_of_nonneg_left hψ (by linarith)
      have h4 : nx * ny ≤ K ^ 2 := by
        rw [sq]; exact mul_le_mul hnxK hnyK hny' (by linarith)
      calc nx * ny * ‖star u ⬝ᵥ ((G - M) *ᵥ v) + star u ⬝ᵥ (M *ᵥ v)‖ ≤
            K ^ 2 * ((N : ℝ) ^ τ₀ * 2 + 5 / 4) :=
            mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
        _ ≤ 4 * K ^ 2 * (N : ℝ) ^ τ₀ := by nlinarith [sq_nonneg K]
    linarith
  refine (measure_mono_ae hsub).trans ?_
  refine (measure_biUnion_finset_le V _).trans ?_
  have hsum : ∀ x ∈ V, μ (⋃ y ∈ V, Bad x y) ≤ ∑ _y ∈ V, ENNReal.ofReal r := fun x _ =>
    (measure_biUnion_finset_le V _).trans (Finset.sum_le_sum fun y _ =>
      hani _ _ (L3_nrm_unit k₀ x) (L3_nrm_unit k₀ y))
  refine (Finset.sum_le_sum hsum).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (V.card : ℝ) ≤ (((9 + 2 * D) * (D * N) : ℕ) : ℝ) := by
    have : V.card ≤ (9 + 2 * D) * (D * N) := by
      refine Finset.card_image_le.trans ?_
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
      apply le_of_eq; ring
    exact_mod_cast this
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc0 : (0 : ℝ) ≤ V.card := Nat.cast_nonneg _
  calc (V.card : ℝ) * ((V.card : ℝ) * r) = (V.card : ℝ) ^ 2 * r := by ring
    _ ≤ _ := by gcongr

/-- Markov's inequality for the moment `E|Z|^{2p}`. -/
private lemma L3_markov {D N : ℕ} {Cc : ℕ → ℝ} (θ : ℝ) {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N Cc θ μ) {Λ B C T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ z₃ : ℂ} {K : ℝ}
    (hs : L3_Set Λ B C T z z₁ z₂ z₃ K) (p : ℕ) {s : ℝ} (hs0 : 0 < s) :
    μ {h | s < ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖} ≤
      ENNReal.ofReal ((∫ h, ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ^ (2 * p) ∂μ) / s ^ (2 * p)) := by
  have hprob := hμ.prob
  have hz₁ := L3_pm_ne hs.hz hs.h1
  have hz₂ := L3_pm_ne hs.hz hs.h2
  have hz₃ := L3_pm_ne hs.hz hs.h3
  set f : (Idx D N → Idx D N → ℂ) → ℝ := fun h => ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ^ (2 * p) with hf
  have hZm : AEStronglyMeasurable (fun h => L3_Z θ Λ B C T z₁ z₂ z₃ h) μ :=
    L3_aesm_sym hμ.herm (L3_cd_Z θ hs.herm B C T hz₁ hz₂ hz₃ 0).continuous
  have hfi : Integrable f μ := by
    refine Integrable.mono' (integrable_const (L3_Zc D θ K z.im ^ (2 * p)))
      (hZm.norm.pow _) ?_
    filter_upwards [hμ.herm] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (L3_Z_crude θ hs h hh) _
  have hsp : 0 < s ^ (2 * p) := pow_pos hs0 _
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun h => by positivity) hfi
    (s ^ (2 * p))
  have hsub : {h | s < ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖} ⊆ {h | s ^ (2 * p) ≤ f h} := by
    intro h hh
    exact pow_le_pow_left₀ hs0.le hh.le _
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hsp, mul_comm]
  exact hm

/-! ### The exponent bookkeeping -/

private lemma L3_herm0 {D N : ℕ} : (Matrix.of (0 : Idx D N → Idx D N → ℂ)).IsHermitian := by
  ext i j; simp

/-- The crude constant on the bad event: `N^{-2h} 2 (W N^{l+6})^{2p} ≤ τ^{6p} N^{-2p}/3` for
`2h ≥ 2p(l+6) + 2p + 1` and `6 W^{2p} τ^{-6p} ≤ N`. -/
private lemma L3_num_a {n W τ : ℝ} (hn1 : 1 ≤ n) (hW : 0 ≤ W) (hτ : 0 < τ) (p l hh e : ℕ)
    (e2 : hh * 2 = (l + 6) * (2 * p) + (2 * p + 1) + e)
    (h4 : 6 * W ^ (2 * p) / τ ^ (6 * p) ≤ n) :
    (n ^ (hh * 2))⁻¹ * (2 * (W * n ^ (l + 6)) ^ (2 * p)) ≤ τ ^ (6 * p) / 3 / n ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hτ4 : 0 < τ ^ (6 * p) := pow_pos hτ _
  have h1 : (n ^ (hh * 2))⁻¹ * (2 * (W * n ^ (l + 6)) ^ (2 * p)) =
      2 * W ^ (2 * p) * ((n ^ (2 * p + 1))⁻¹ * (n ^ e)⁻¹) := by
    rw [e2, pow_add, pow_add, mul_pow, ← pow_mul]
    field_simp
  have h2 : (n ^ e)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hn1)
  have h3 : 0 ≤ 2 * W ^ (2 * p) * (n ^ (2 * p + 1))⁻¹ := by positivity
  rw [h1]
  calc 2 * W ^ (2 * p) * ((n ^ (2 * p + 1))⁻¹ * (n ^ e)⁻¹)
      ≤ 2 * W ^ (2 * p) * (n ^ (2 * p + 1))⁻¹ * 1 := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h2 h3
    _ = 2 * W ^ (2 * p) / n / n ^ (2 * p) := by rw [pow_succ]; field_simp
    _ ≤ τ ^ (6 * p) / 3 / n ^ (2 * p) := by
        have : 2 * W ^ (2 * p) / n ≤ τ ^ (6 * p) / 3 := by
          rw [div_le_iff₀ hn0]
          rw [div_le_iff₀ hτ4] at h4
          nlinarith
        exact div_le_div_of_nonneg_right this (by positivity)

/-- The good part of the remainder: `DN K_e N^{-(l+2)/2} A ≤ τ^{6p} N^{-2p}/3` for `l = 12p + 2`,
`A ≤ W_a (4K² N^{τ₀})^{l+4p} N^{4p}`, `τ₀ (l + 4p) ≤ 1/2` and
`3 D K_e W_a (4K²)^{l+4p} τ^{-6p} ≤ N^{1/2}`. -/
private lemma L3_num_b {n τ τ₀ d Ke Wa K Ag : ℝ} (hn1 : 1 ≤ n) (hτ : 0 < τ) (hτ₀ : 0 ≤ τ₀)
    (hd : 0 ≤ d) (hKe : 0 ≤ Ke) (hWa : 0 ≤ Wa) (p l : ℕ) (hl : l = 12 * p + 2)
    (hτ₀b : ((l : ℝ) + 4 * p) * τ₀ ≤ 1 / 2)
    (hAg : Ag ≤ Wa * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4 * p) * n ^ (4 * p))
    (h5 : 3 * (d * Ke * Wa * (4 * K ^ 2) ^ (l + 4 * p)) / τ ^ (6 * p) ≤ n ^ (1 / 2 : ℝ)) :
    d * n * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * Ag)) ≤ τ ^ (6 * p) / 3 / n ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hτ4 : 0 < τ ^ (6 * p) := pow_pos hτ _
  have hr : n ^ (-((l : ℝ) + 2) / 2) = (n ^ (6 * p + 2))⁻¹ := by
    rw [show -((l : ℝ) + 2) / 2 = -((6 * p + 2 : ℕ) : ℝ) by rw [hl]; push_cast; ring,
      Real.rpow_neg hn0.le, Real.rpow_natCast]
  have hΓ : (4 * K ^ 2 * n ^ τ₀) ^ (l + 4 * p) ≤ (4 * K ^ 2) ^ (l + 4 * p) * n ^ (1 / 2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hn0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 ?_) (by positivity)
    push_cast; linarith
  have hs : n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hn0]; norm_num
  have hs0 : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  set c := d * Ke * Wa * (4 * K ^ 2) ^ (l + 4 * p) with hc
  have hc0 : 0 ≤ c := by positivity
  have hAg' : Ag ≤ Wa * ((4 * K ^ 2) ^ (l + 4 * p) * n ^ (1 / 2 : ℝ)) * n ^ (4 * p) :=
    hAg.trans (by gcongr)
  have hnp : n ^ (6 * p + 2) = n ^ (4 * p) * n ^ (2 * p) * n * n := by
    rw [show 6 * p + 2 = 4 * p + 2 * p + 1 + 1 by ring, pow_succ, pow_succ, pow_add]
  calc d * n * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * Ag))
      ≤ d * n * (Ke * ((n ^ (6 * p + 2))⁻¹ *
          (Wa * ((4 * K ^ 2) ^ (l + 4 * p) * n ^ (1 / 2 : ℝ)) * n ^ (4 * p)))) := by
        rw [hr]; gcongr
    _ = c * n ^ (1 / 2 : ℝ) / n / n ^ (2 * p) := by
        rw [hc, hnp]; field_simp
    _ ≤ τ ^ (6 * p) / 3 / n ^ (2 * p) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hn0]
        rw [div_le_iff₀ hτ4] at h5
        calc c * n ^ (1 / 2 : ℝ) = (3 * c) * n ^ (1 / 2 : ℝ) / 3 := by ring
          _ ≤ (n ^ (1 / 2 : ℝ) * τ ^ (6 * p)) * n ^ (1 / 2 : ℝ) / 3 := by gcongr
          _ = τ ^ (6 * p) / 3 * (n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ)) := by ring
          _ = τ ^ (6 * p) / 3 * n := by rw [hs]

/-- The crude part of the remainder: `DN K_e B_c √(ε₀ + K_k σ + σ) ≤ τ^{6p} N^{-2p}/3` for
`ε₀, σ ≤ N^{-2h}`, `B_c ≤ W_b N^{l+8p}`, `h ≥ l + 10p + 2` and
`3 D K_e W_b √(K_k + 2) τ^{-6p} ≤ N`. -/
private lemma L3_num_c {n τ d Ke Wb Kk Bc ε₀ σ : ℝ} (hn1 : 1 ≤ n) (hτ : 0 < τ) (hd : 0 ≤ d)
    (hKe : 0 ≤ Ke) (hWb : 0 ≤ Wb) (hKk : 0 ≤ Kk) (p l hh e : ℕ)
    (e3 : hh = (1 + (l + 8 * p)) + (2 * p + 1) + e) (hε₀ : 0 ≤ ε₀)
    (hε : ε₀ ≤ (n ^ (hh * 2))⁻¹) (hσ : σ = (n ^ (hh * 2))⁻¹) (hBc0 : 0 ≤ Bc)
    (hBc : Bc ≤ Wb * n ^ (l + 8 * p))
    (h6 : 3 * (d * Ke * Wb * Real.sqrt (Kk + 2)) / τ ^ (6 * p) ≤ n) :
    d * n * (Ke * (Bc * Real.sqrt (ε₀ + Kk * σ + σ))) ≤ τ ^ (6 * p) / 3 / n ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hτ4 : 0 < τ ^ (6 * p) := pow_pos hτ _
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hsq : Real.sqrt (ε₀ + Kk * σ + σ) ≤ Real.sqrt (Kk + 2) * (n ^ hh)⁻¹ := by
    have h1 : ε₀ + Kk * σ + σ ≤ (Kk + 2) * (n ^ (hh * 2))⁻¹ := by
      rw [hσ] at *; nlinarith
    calc Real.sqrt (ε₀ + Kk * σ + σ) ≤ Real.sqrt ((Kk + 2) * (n ^ (hh * 2))⁻¹) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Kk + 2) * (n ^ hh)⁻¹ := by
          rw [Real.sqrt_mul (by linarith), Real.sqrt_inv, pow_mul,
            Real.sqrt_sq (by positivity)]
  set c := d * Ke * Wb * Real.sqrt (Kk + 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hnh : n ^ hh = n ^ (l + 8 * p) * n * n ^ (2 * p) * (n * n ^ e) := by
    rw [e3]; ring
  calc d * n * (Ke * (Bc * Real.sqrt (ε₀ + Kk * σ + σ)))
      ≤ d * n * (Ke * ((Wb * n ^ (l + 8 * p)) * (Real.sqrt (Kk + 2) * (n ^ hh)⁻¹))) := by
        gcongr
    _ = c / n ^ (2 * p) / (n * n ^ e) := by
        rw [hc, hnh]; field_simp
    _ ≤ c / n ^ (2 * p) / n := by
        gcongr
        calc n = n * 1 := (mul_one n).symm
          _ ≤ n * n ^ e := by gcongr; exact one_le_pow₀ hn1
    _ ≤ τ ^ (6 * p) / 3 / n ^ (2 * p) := by
        rw [div_div, div_div, mul_comm (n ^ (2 * p)) n, ← div_div, ← div_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hn0]
        rw [div_le_iff₀ hτ4] at h6
        nlinarith

/-- The final Markov step: `2(C_p + 1) Q^{2p} / (N^{τ'} Ψ)^{2p} ≤ N^{-D'}` for
`Q = K_q (4K² N^{τ₀})^{l+4} Ψ`, `(l + 4) τ₀ ≤ t/2`, `t ≤ τ'`, `D' + 1 ≤ p t` and `C_m ≤ N`. -/
private lemma L3_num_m {n τ₀ t τ' D' Kq K Ψ Cp : ℝ} (hn1 : 1 ≤ n) (hτ₀ : 0 ≤ τ₀) (ht : 0 < t)
    (htτ : t ≤ τ') (hΨ : 0 < Ψ) (hKq : 0 ≤ Kq) (hCp : 0 ≤ Cp) (p l : ℕ)
    (hτ₀a : ((l : ℝ) + 4) * τ₀ ≤ t / 2) (hpt : D' + 1 ≤ p * t)
    (h7 : 2 * (Cp + 1) * (Kq * (4 * K ^ 2) ^ (l + 4)) ^ (2 * p) ≤ n) :
    2 * (Cp + 1) * (Kq * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4) * Ψ) ^ (2 * p) /
        (n ^ τ' * Ψ) ^ (2 * p) ≤ n ^ (-D') := by
  have hn0 : 0 < n := by linarith
  set c := Kq * (4 * K ^ 2) ^ (l + 4) with hc
  have hc0 : 0 ≤ c := by positivity
  have hΓ : (4 * K ^ 2 * n ^ τ₀) ^ (l + 4) ≤ (4 * K ^ 2) ^ (l + 4) * n ^ (t / 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hn0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 ?_) (by positivity)
    push_cast; linarith
  have hτ' : n ^ t ≤ n ^ τ' := Real.rpow_le_rpow_of_exponent_le hn1 htτ
  have ht2 : n ^ (t / 2) * n ^ (t / 2) = n ^ t := by rw [← Real.rpow_add hn0]; ring_nf
  have hpos : 0 < n ^ (t / 2) := Real.rpow_pos_of_pos hn0 _
  have hpos' : 0 < n ^ τ' := Real.rpow_pos_of_pos hn0 _
  have hq : Kq * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4) * Ψ / (n ^ τ' * Ψ) ≤ c * (n ^ (t / 2))⁻¹ := by
    rw [mul_div_mul_right _ _ hΨ.ne', div_le_iff₀ hpos']
    calc Kq * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4) ≤ Kq * ((4 * K ^ 2) ^ (l + 4) * n ^ (t / 2)) := by
          gcongr
      _ = c * (n ^ (t / 2))⁻¹ * (n ^ (t / 2) * n ^ (t / 2)) := by
          rw [hc]; field_simp
      _ ≤ c * (n ^ (t / 2))⁻¹ * n ^ τ' := by rw [ht2]; gcongr
  have hq0 : 0 ≤ Kq * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4) * Ψ / (n ^ τ' * Ψ) := by positivity
  have hpow : ((n ^ (t / 2))⁻¹) ^ (2 * p) ≤ (n ^ (D' + 1))⁻¹ := by
    rw [inv_pow, ← Real.rpow_mul_natCast hn0.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos hn0 _) (Real.rpow_le_rpow_of_exponent_le hn1 ?_)
    push_cast; linarith
  have hD1 : n ^ (D' + 1) = n ^ D' * n := Real.rpow_add_one hn0.ne' D'
  rw [mul_div_assoc, ← div_pow]
  calc 2 * (Cp + 1) * (Kq * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4) * Ψ / (n ^ τ' * Ψ)) ^ (2 * p)
      ≤ 2 * (Cp + 1) * (c * (n ^ (t / 2))⁻¹) ^ (2 * p) := by gcongr
    _ = 2 * (Cp + 1) * c ^ (2 * p) * ((n ^ (t / 2))⁻¹) ^ (2 * p) := by rw [mul_pow]; ring
    _ ≤ 2 * (Cp + 1) * c ^ (2 * p) * (n ^ (D' + 1))⁻¹ := by gcongr
    _ = 2 * (Cp + 1) * c ^ (2 * p) / n * (n ^ D')⁻¹ := by rw [hD1]; field_simp
    _ ≤ 1 * (n ^ D')⁻¹ := by
        gcongr
        rw [div_le_one hn0]; exact h7
    _ = n ^ (-D') := by rw [one_mul, Real.rpow_neg hn0.le]

set_option maxHeartbeats 1000000 in
/-- The fluctuation term of the expansion of `L₍₁,₂,₃₎` (the term `underThree`) is `≺ N⁻¹η⁻³` in
the setting of Lemma 3.6 [lemma_G_large], uniformly in `θ ∈ [0, 1]` and the class, for
`z₁, z₂, z₃ ∈ {z, z̄}`, outside probability `N^{-D'}`. -/
theorem underThree_fluct (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ z₃ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      (z₃ = z ∨ z₃ = star z) → ∀ a₁ a₂ a₃ : Fin D,
        μ {h | (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 3)⁻¹) <
            ‖underThree (lam D N A) θ h z₁ z₂ z₃ a₁ a₂ a₃‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  haveI : NeZero D := ⟨by omega⟩
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  -- the exponents
  set t := min τ' 1 with ht
  have ht0 : 0 < t := lt_min hτ' one_pos
  have htτ : t ≤ τ' := min_le_left _ _
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈(D' + 1) / t⌉₊ + 1 := ⟨_, rfl⟩
  have hp : 1 ≤ p := by omega
  have hpt : D' + 1 ≤ p * t := by
    have h1 := Nat.le_ceil ((D' + 1) / t)
    have h2 : ((D' + 1) / t) ≤ (p : ℝ) := by
      rw [hpdef]; push_cast; linarith
    rw [div_le_iff₀ ht0] at h2
    linarith
  set l : ℕ := 12 * p + 2 with hl
  have hl2 : 2 ≤ l := by omega
  set hh : ℕ := p * (l + 7) + l + 10 * p + 4 with hhh
  set k : ℕ := 8 * hh with hk
  set τ₀ : ℝ := t / (2 * ((l : ℝ) + 4 * p + 4)) with hτ₀
  have hL0 : (0 : ℝ) < 2 * ((l : ℝ) + 4 * p + 4) := by positivity
  have hτ₀0 : 0 < τ₀ := div_pos ht0 hL0
  have hτ₀a : ((l : ℝ) + 4) * τ₀ ≤ t / 2 := by
    rw [hτ₀, mul_div_assoc', div_le_div_iff₀ hL0 (by norm_num)]
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith
  have hτ₀b : ((l : ℝ) + 4 * p) * τ₀ ≤ 1 / 2 := by
    rw [hτ₀, mul_div_assoc', div_le_div_iff₀ hL0 (by norm_num)]
    have : t ≤ 1 := min_le_right _ _
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith
  have hτ₀c : τ₀ ≤ 1 / 8 := by
    rw [hτ₀, div_le_div_iff₀ hL0 (by norm_num)]
    have : t ≤ 1 := min_le_right _ _
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith
  -- the constants
  set K : ℝ := 2 + 2 * τ⁻¹ with hK
  have hti : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hK1 : 1 ≤ K := by linarith
  set E₀ : ℝ := τ⁻¹ with hE₀
  set Cz : ℝ := 8 * (D : ℝ) ^ 2 with hCz
  set Cz2 : ℝ := 8 * (D : ℝ) ^ 3 with hCz2
  choose Kab hKab using fun a b => llClass_ccum_le C a b
  set Kc : ℝ := ∑ a ∈ Finset.range (l + 2), ∑ b ∈ Finset.range (l + 2), max (Kab a b) 0
    with hKc
  have hKc0 : 0 ≤ Kc := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    le_max_right _ _
  have hKab' : ∀ a b, a + b ≤ l + 1 → Kab a b ≤ Kc := by
    intro a b hab
    have ha : a ∈ Finset.range (l + 2) := Finset.mem_range.mpr (by omega)
    have hb : b ∈ Finset.range (l + 2) := Finset.mem_range.mpr (by omega)
    calc Kab a b ≤ max (Kab a b) 0 := le_max_left _ _
      _ ≤ ∑ b ∈ Finset.range (l + 2), max (Kab a b) 0 :=
          Finset.single_le_sum (f := fun b => max (Kab a b) 0)
            (fun _ _ => le_max_right _ _) hb
      _ ≤ Kc := Finset.single_le_sum (f := fun a =>
            ∑ b ∈ Finset.range (l + 2), max (Kab a b) 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) ha
  obtain ⟨Ke, Kk, hKe0, hKk0, hrem⟩ := L3_rem l k C
  set Kq := L3_Kq D p l Kc Cz Cz2 K E₀ with hKq
  set W := 16 * Cz * K ^ 8 + Kq * (2 * K ^ 2) ^ (l + 4) + 1 with hW
  set Wb := (8 * p * (4 + l) * K ^ 3) ^ (l + 1) * (2 * K ^ 5) *
    (16 * Cz * K ^ 8 + 6 * Cz * K ^ 6 * (1 + E₀) ^ 4) ^ (2 * p - 1) with hWb
  set Wa := (24 * p * (4 + l) * K) ^ (l + 1) * (6 * K ^ 3) *
    (144 * Cz * K ^ 4 + 18 * Cz * K ^ 4 * (1 + E₀) ^ 4) ^ (2 * p - 1) with hWa
  set Cp := 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) with hCp
  set Cm := 2 * (Cp + 1) * (Kq * (4 * K ^ 2) ^ (l + 4)) ^ (2 * p) with hCm
  have hτ4 : 0 < τ ^ (6 * p) := pow_pos hτ _
  -- the thresholds
  obtain ⟨N₁, hN₁⟩ := aniso_local D (by omega) δA τ hδA hτ C τ₀ hτ₀0 ((hh * 2 + 3 : ℕ) : ℝ)
    (by positivity)
  obtain ⟨N₂, hN₂⟩ := L3_exists_rpow_ge hδA 20
  obtain ⟨N₃, hN₃⟩ := L3_exists_rpow_ge (by norm_num : (0 : ℝ) < 1 / 8) (96 * K ^ 2)
  obtain ⟨N₄, hN₄⟩ := L3_exists_rpow_ge one_pos (6 * W ^ (2 * p) / τ ^ (6 * p))
  obtain ⟨N₅, hN₅⟩ := L3_exists_rpow_ge (by norm_num : (0 : ℝ) < 1 / 2)
    (3 * (D * Ke * Wa * (4 * K ^ 2) ^ (l + 4 * p)) / τ ^ (6 * p))
  obtain ⟨N₆, hN₆⟩ := L3_exists_rpow_ge one_pos
    (3 * (D * Ke * Wb * Real.sqrt (Kk + 2)) / τ ^ (6 * p))
  obtain ⟨N₇, hN₇⟩ := L3_exists_rpow_ge one_pos Cm
  obtain ⟨N₈, hN₈⟩ := L3_exists_rpow_ge one_pos ((((9 + 2 * D) * D : ℕ) : ℝ) ^ 2)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ (max N₈ 1))), ?_⟩
  intro N hN θ hθ0 hθ1 μ hμ A hA z hzD hzim _ _ _ z₁ z₂ z₃ h1 h2 h3 a₁ a₂ a₃
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : N₅ ≤ N := by omega
  have hN6 : N₆ ≤ N := by omega
  have hN7 : N₇ ≤ N := by omega
  have hN8 : N₈ ≤ N := by omega
  have hNpos : 1 ≤ N := by omega
  haveI : NeZero N := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  set n : ℝ := (N : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hprob := hμ.prob
  -- the deterministic setting
  have hA' : opNorm A ≤ 1 / 20 := by
    refine hA.trans ?_
    rw [Real.rpow_neg hn0.le]
    have := hN₂ N hN2
    rw [inv_le_comm₀ (Real.rpow_pos_of_pos hn0 _) (by norm_num)]
    linarith
  have hη : z.im ≤ E₀ := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzD.1)
  have hNη : n⁻¹ ≤ z.im := by
    have h1' := hzD.2
    rw [abs_of_pos hzim] at h1'
    refine le_trans ?_ h1'
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h1' : L3_pm z z₁ := h1
  have h2' : L3_pm z z₂ := h2
  have h3' : L3_pm z z₃ := h3
  have hs := L3_set_inst (D := D) (N := N) A hA' hτ hzim hzD.1 h1' h2' h3' (Ea D N a₃)
    (Ea D N a₁) (L3_opNorm_Ea D N a₃) (L3_opNorm_Ea D N a₁) a₂
  set Λ := lam D N A with hΛ
  set B := Ea D N a₃ with hB
  set C := Ea D N a₁ with hC
  set T := Ea D N a₂ * MExt Λ z₃ with hT
  have hz₃ := L3_pm_ne hzim h3'
  obtain ⟨hCz', hCz2'⟩ := L3_Cz_le (D := D) hθ0 hθ1
  -- the cutoff level and the bad event
  set Γ := 4 * K ^ 2 * n ^ τ₀ with hΓ
  have hnτ : 1 ≤ n ^ τ₀ := Real.one_le_rpow hn1 hτ₀0.le
  have hΓ1 : 1 ≤ Γ := by
    have : 1 ≤ 4 * K ^ 2 := by have := one_le_pow₀ (n := 2) hK1; linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 4 * K ^ 2 * n ^ τ₀ := mul_le_mul this hnτ zero_le_one (by positivity)
  set r : ℝ := n ^ (-((hh * 2 + 3 : ℕ) : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hn0.le _
  have hani : ∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
      μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ₀ * psiIso (lam D N A) N z <
        ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖} ≤
        ENNReal.ofReal r := fun u v hu hv => hN₁ N hN1 θ hθ0 hθ1 μ hμ A hA u v hu hv
  have hbad := L3_bad_le hμ A hA' hτ hτ₀0.le hr0 hzD hzim hNη h1' h2' h3' B C
    (L3_opNorm_Ea D N a₃) (L3_opNorm_Ea D N a₁) a₂ hani
  set ε₀ := ((((9 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 * r with hε₀
  have hε₀0 : 0 ≤ ε₀ := by positivity
  have hr' : r = (n ^ (hh * 2 + 3))⁻¹ := by
    rw [hr, Real.rpow_neg hn0.le, Real.rpow_natCast]
  have hε₀le : ε₀ ≤ (n ^ (hh * 2))⁻¹ := by
    have h8 := hN₈ N hN8
    rw [Real.rpow_one] at h8
    have hc : ((((9 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 ≤ n ^ 3 := by
      have e : ((((9 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 =
          ((((9 + 2 * D) * D : ℕ) : ℝ)) ^ 2 * n ^ 2 := by push_cast; ring
      rw [e, pow_succ' n 2]
      exact mul_le_mul_of_nonneg_right h8 (by positivity)
    rw [hε₀, hr', pow_add, mul_inv]
    calc ((((9 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 * ((n ^ (hh * 2))⁻¹ * (n ^ 3)⁻¹)
        ≤ n ^ 3 * ((n ^ (hh * 2))⁻¹ * (n ^ 3)⁻¹) := by gcongr
      _ = (n ^ (hh * 2))⁻¹ := by field_simp
  -- the cutoff radius
  set M : ℝ := n ^ (-(1 / 4 : ℝ)) with hM
  have hM0 : 0 < M := Real.rpow_pos_of_pos hn0 _
  have hMΓ : 24 * M * Γ ≤ 1 := by
    have h3 := hN₃ N hN3
    have e : 24 * M * Γ = 96 * K ^ 2 * (n ^ (-(1 / 4 : ℝ)) * n ^ τ₀) := by rw [hM, hΓ]; ring
    rw [e, ← Real.rpow_add hn0]
    have h4 : n ^ (-(1 / 4 : ℝ) + τ₀) ≤ n ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h5 : n ^ (-(1 / 8 : ℝ)) = (n ^ (1 / 8 : ℝ))⁻¹ := Real.rpow_neg hn0.le _
    have h6 : 0 < n ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hn0 _
    calc 96 * K ^ 2 * n ^ (-(1 / 4 : ℝ) + τ₀) ≤ 96 * K ^ 2 * (n ^ (1 / 8 : ℝ))⁻¹ := by
          rw [← h5]; gcongr
      _ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one h6]; exact h3
  have hσ : (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) = (n ^ (hh * 2))⁻¹ := by
    rw [hM, ← Real.rpow_add hn0, ← Real.rpow_mul hn0.le,
      show ((1 : ℝ) / 2 + -(1 / 4)) * -(k : ℝ) = -((hh * 2 : ℕ) : ℝ) by rw [hk]; push_cast; ring,
      Real.rpow_neg hn0.le, Real.rpow_natCast]
  -- the expansion and the moment bound
  have hcc : ∀ a' b β α, 3 ≤ a' + b → a' + b ≤ l + 1 →
      ‖ccum (μ.map fun h => h β α) a' b‖ ≤ Kc * (N : ℝ) ^ (-(((a' + b : ℕ) : ℝ) / 2)) := by
    intro a' b β α _ hab
    refine (hKab a' b D N θ μ hμ β α).trans ?_
    exact mul_le_mul_of_nonneg_right (hKab' a' b hab) (Real.rpow_nonneg hn0.le _)
  have hhrem := hrem D N θ μ hμ Λ B C T z z₁ z₂ z₃ K hs p hp Γ M ε₀ hΓ1 hM0 hMΓ hε₀0 hbad
  set Ψ := n⁻¹ * (z.im⁻¹) ^ 3 with hΨ
  have hΨ0 : 0 < Ψ := by positivity
  set Q := Kq * Γ ^ (l + 4) * Ψ with hQ
  have hKq1 : 1 ≤ Kq := by
    rw [hKq]; unfold L3_Kq
    have : (0 : ℝ) ≤ 2 * p - 1 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hCz20 : 0 ≤ Cz2 := by positivity
    have := L3_Cs_nonneg D hCz20 (by linarith : (0 : ℝ) ≤ K) hti.le
    have : 0 ≤ 108 * Kc * K ^ 5 * D * (1 + E₀) +
        12 * Kc * ((3 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 3 * (1 + E₀) +
        ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((3 + l) * K)) ^ l * K ^ 3 * (1 + E₀) +
        (2 * (2 * p - 1) * (1 + 2 * L3_Cs D Cz2 K E₀ * K ^ 6) +
          96 * (2 * p - 1) * Kc * K ^ 4 * (1 + 2 * L3_Cs D Cz2 K E₀) * (1 + E₀)) +
        3 * Cz * K ^ 4 * (1 + E₀) ^ 4 := by positivity
    linarith
  have hΓl1 : 1 ≤ Γ ^ (l + 4) := one_le_pow₀ hΓ1
  have hQΨ : Ψ ≤ Q := by
    rw [hQ]
    calc Ψ = 1 * 1 * Ψ := by ring
      _ ≤ Kq * Γ ^ (l + 4) * Ψ := by gcongr
  have hQ0 : 0 ≤ Q := hΨ0.le.trans hQΨ
  have hRB : ∀ x, 0 ≤ x → L3_RB D N θ K Γ z.im p l Kc x ≤
      Q * (x + Q) ^ (2 * p - 1) + Q ^ 2 * (x + Q) ^ (2 * p - 2) := fun x hx =>
    L3_RB_le θ p l hp hK1 hΓ1 hzim hη hNη hKc0 hCz' hCz2' x hx
  have hmom := L3_mom θ hθ0 hθ1 hμ hs (L3_Zd θ hs.herm B C T z₁ z₂ z₃ hz₃) p l hp hl2 Kc hKc0
    hcc _
    hhrem Γ ε₀ Q hΓ1 hε₀0 hQ0 hbad hRB
  -- the remainders are `≤ τ^{4p} N^{-2p} ≤ Q^{2p}`
  have hRc := L3_Rc_le (D := D) (N := N) θ (E₀ := E₀) p l hp hK1 hzim hη hNη hKc0 hCz' hCz2'
  have hBc := L3_Bc_le (D := D) (N := N) θ (E₀ := E₀) p l hp hK1 hzim hη hNη hCz'
  have hAg := L3_Ag_le (D := D) (N := N) θ (E₀ := E₀) p l hp hK1 hΓ1 hzim hη hNη hCz'
  have hW0 : 0 ≤ W := by
    have : 0 ≤ Kq := by linarith
    rw [hW]; positivity
  have hn2p : 0 < n ^ (2 * p) := pow_pos hn0 _
  have hnτ4 : τ ^ (6 * p) / n ^ (2 * p) ≤ Q ^ (2 * p) := by
    have hτz : τ ≤ z.im⁻¹ := by
      rw [le_inv_comm₀ hτ hzim]; exact hη
    have : τ ^ 3 / n ≤ Ψ := by
      rw [hΨ, div_eq_inv_mul]
      gcongr
    calc τ ^ (6 * p) / n ^ (2 * p) = (τ ^ 3 / n) ^ (2 * p) := by
          rw [div_pow, ← pow_mul]; ring_nf
      _ ≤ Ψ ^ (2 * p) := by gcongr
      _ ≤ Q ^ (2 * p) := by gcongr
  -- the remainders
  have hh2 : hh * 2 = (l + 6) * (2 * p) + (2 * p + 1) + (2 * l + 20 * p + 7) := by
    rw [hhh]; ring
  have hh3 : hh = (1 + (l + 8 * p)) + (2 * p + 1) + (p * (l + 7) + 2) := by rw [hhh]; ring
  have hWa0 : 0 ≤ Wa := by rw [hWa]; positivity
  have hWb0 : 0 ≤ Wb := by rw [hWb]; positivity
  have hd0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have k₀ : Idx D N := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hBc0 : 0 ≤ L3_Bc D N θ (l + 1) p K z.im :=
    (norm_nonneg _).trans (L3_F_crude θ hs 0 L3_herm0 k₀ k₀ 0
      (l + 1) p hp k₀ k₀ 0 0 (Nat.zero_le _))
  have ha : ε₀ * L3_RB D N θ K (L3_Gc0 K z.im) z.im p l Kc (L3_Zc D θ K z.im) ≤
      τ ^ (6 * p) / 3 / n ^ (2 * p) :=
    (mul_le_mul_of_nonneg_left hRc hε₀0).trans ((mul_le_mul_of_nonneg_right hε₀le
      (by positivity)).trans (L3_num_a hn1 hW0 hτ p l hh _ hh2
        (by have := hN₄ N hN4; rwa [Real.rpow_one] at this)))
  have hb := L3_num_b hn1 hτ hτ₀0.le hd0 hKe0 hWa0 p l rfl hτ₀b hAg (hN₅ N hN5)
  have hc := L3_num_c hn1 hτ hd0 hKe0 hWb0 hKk0 p l hh _ hh3 hε₀0 hε₀le hσ hBc0 hBc
    (by have := hN₆ N hN6; rwa [Real.rpow_one] at this)
  have hsum : ε₀ * L3_RB D N θ K (L3_Gc0 K z.im) z.im p l Kc (L3_Zc D θ K z.im) +
      (D * n : ℝ) * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * L3_Ag D N θ p l K Γ z.im +
        L3_Bc D N θ (l + 1) p K z.im * Real.sqrt (ε₀ + Kk * (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
          (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))))) ≤ Q ^ (2 * p) := by
    have e : (D * n : ℝ) * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * L3_Ag D N θ p l K Γ z.im +
        L3_Bc D N θ (l + 1) p K z.im * Real.sqrt (ε₀ + Kk * (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
          (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))))) =
        D * n * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * L3_Ag D N θ p l K Γ z.im)) +
        D * n * (Ke * (L3_Bc D N θ (l + 1) p K z.im *
          Real.sqrt (ε₀ + Kk * (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
            (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))))) := by ring
    rw [e]
    have : τ ^ (6 * p) / 3 / n ^ (2 * p) + τ ^ (6 * p) / 3 / n ^ (2 * p) +
        τ ^ (6 * p) / 3 / n ^ (2 * p) = τ ^ (6 * p) / n ^ (2 * p) := by ring
    linarith
  have hY : ∫ h, ‖L3_Z θ Λ B C T z₁ z₂ z₃ h‖ ^ (2 * p) ∂μ ≤ 2 * (Cp + 1) * Q ^ (2 * p) := by
    have := hmom
    rw [← hCp] at this
    linarith
  -- Markov's inequality
  have hs0 : 0 < n ^ τ' * Ψ := mul_pos (Real.rpow_pos_of_pos hn0 _) hΨ0
  simp only [← inv_pow]
  refine (measure_mono_ae ?_).trans ((L3_markov θ hμ hs p hs0).trans ?_)
  · filter_upwards [hμ.herm] with h hh' hlt
    rw [← L3_under_Z θ hs.herm z₁ z₂ z₃ hz₃ a₁ a₂ a₃ h hh']
    exact hlt
  · refine ENNReal.ofReal_le_ofReal ?_
    refine (div_le_div_of_nonneg_right hY (by positivity)).trans ?_
    have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
    exact L3_num_m hn1 hτ₀0.le ht0 htτ hΨ0 (by linarith) hCp0 p l hτ₀a hpt
      (by have := hN₇ N hN7; rwa [Real.rpow_one] at this)

end RBMTransitionEdge

end
