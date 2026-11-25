module

public import RBMTransitionEdge.Flow.ChainDer
public import RBMTransitionEdge.Flow.LargeEtaId

@[expose] public section

/-!
# The fluctuation term of the two-resolvent identity at large `η`

The term `⟨\underline{G₁E_aM₂HG₂}B⟩` of (3.39) [eq:aftertrace] is `≺ N⁻¹η⁻²` in the setting of
Lemma 3.6 [lemma_G_large], uniformly in `θ ∈ [0, 1]` and the class.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Wirtinger calculus for smooth functions of one complex variable -/

/-- Smooth (real sense, every finite order) functions `ℂ → ℂ`, such as the slices
`w ↦ F(setEntry h i j w)` of Lemma 2.11 [lem:complex_cumu]. -/
private def LF_Sm (f : ℂ → ℂ) : Prop := ∀ n : ℕ, ContDiff ℝ n f

/-- A smooth function is real-differentiable. -/
private lemma LF_Sm.diff {f : ℂ → ℂ} (hf : LF_Sm f) : Differentiable ℝ f :=
  (hf 1).differentiable (by norm_num)

/-- `z ↦ f'(z) v` is smooth for smooth `f`. -/
private lemma LF_sm_fderiv_apply {f : ℂ → ℂ} (hf : LF_Sm f) (v : ℂ) :
    LF_Sm (fun z => fderiv ℝ f z v) := fun n =>
  ((hf (n + 1)).fderiv_right (by norm_cast)).clm_apply contDiff_const

/-- Constants are smooth. -/
private lemma LF_sm_const (c : ℂ) : LF_Sm (fun _ => c) := fun _ => contDiff_const

/-- Products of smooth functions are smooth. -/
private lemma LF_sm_mul {f g : ℂ → ℂ} (hf : LF_Sm f) (hg : LF_Sm g) :
    LF_Sm (fun z => f z * g z) := fun n => (hf n).mul (hg n)

/-- Constant multiples of smooth functions are smooth. -/
private lemma LF_sm_cmul (c : ℂ) {f : ℂ → ℂ} (hf : LF_Sm f) : LF_Sm (fun z => c * f z) :=
  LF_sm_mul (LF_sm_const c) hf

/-- Powers of smooth functions are smooth. -/
private lemma LF_sm_pow {f : ℂ → ℂ} (hf : LF_Sm f) (m : ℕ) : LF_Sm (fun z => f z ^ m) :=
  fun n => (hf n).pow m

/-- The complex conjugate of a smooth function is smooth. -/
private lemma LF_sm_conj {f : ℂ → ℂ} (hf : LF_Sm f) : LF_Sm (fun z => starRingEnd ℂ (f z)) :=
  fun n => Complex.conjCLE.contDiff.comp (hf n)

/-- `∂_w f` is smooth for smooth `f`. -/
private lemma LF_sm_dW {f : ℂ → ℂ} (hf : LF_Sm f) : LF_Sm (dW f) := fun n => by
  unfold dW
  exact ((LF_sm_fderiv_apply hf 1 n).sub
    (contDiff_const.mul (LF_sm_fderiv_apply hf Complex.I n))).div_const 2

/-- `∂_{w̄} f` is smooth for smooth `f`. -/
private lemma LF_sm_dWbar {f : ℂ → ℂ} (hf : LF_Sm f) : LF_Sm (dWbar f) := fun n => by
  unfold dWbar
  exact ((LF_sm_fderiv_apply hf 1 n).add
    (contDiff_const.mul (LF_sm_fderiv_apply hf Complex.I n))).div_const 2

/-- The operators `∂_w`, `∂_{w̄}` act on smooth functions as derivations. -/
private structure LF_Der (d : (ℂ → ℂ) → ℂ → ℂ) : Prop where
  sm : ∀ f, LF_Sm f → LF_Sm (d f)
  mul : ∀ f g, LF_Sm f → LF_Sm g → d (fun x => f x * g x) = fun x => d f x * g x + f x * d g x
  sum : ∀ (s : Finset ℕ) (F : ℕ → ℂ → ℂ), (∀ m, LF_Sm (F m)) →
    d (fun x => ∑ m ∈ s, F m x) = fun x => ∑ m ∈ s, d (F m) x
  cmul : ∀ (c : ℂ) f, LF_Sm f → d (fun x => c * f x) = fun x => c * d f x
  add : ∀ f g, LF_Sm f → LF_Sm g → d (fun x => f x + g x) = fun x => d f x + d g x
  const : ∀ c : ℂ, d (fun _ => c) = fun _ => 0

/-- `∂_w` is a derivation on smooth functions. -/
private lemma LF_der_dW : LF_Der dW where
  sm := fun _ hf => LF_sm_dW hf
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
private lemma LF_der_dWbar : LF_Der dWbar where
  sm := fun _ hf => LF_sm_dWbar hf
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
private lemma LF_der_iter_sm {d : (ℂ → ℂ) → ℂ → ℂ} (hd : LF_Der d) (n : ℕ) {f : ℂ → ℂ}
    (hf : LF_Sm f) : LF_Sm (d^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact hd.sm _ ih

/-- Iterates of a derivation on a constant. -/
private lemma LF_der_iter_const {d : (ℂ → ℂ) → ℂ → ℂ} (hd : LF_Der d) (n : ℕ) (c : ℂ) :
    d^[n] (fun _ => c) = fun _ => if n = 0 then c else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [Nat.add_one_ne_zero, ite_false]
    exact hd.const _

/-- Iterates of a derivation are linear on finite sums of smooth functions. -/
private lemma LF_der_iter_lin {d : (ℂ → ℂ) → ℂ → ℂ} (hd : LF_Der d) (n : ℕ) (s : Finset ℕ)
    (c : ℕ → ℂ) (F : ℕ → ℂ → ℂ) (hF : ∀ m, LF_Sm (F m)) :
    d^[n] (fun x => ∑ m ∈ s, c m * F m x) = fun x => ∑ m ∈ s, c m * d^[n] (F m) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hd.sum s _ fun m => LF_sm_cmul _ (LF_der_iter_sm hd n (hF m))]
    funext x
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hd.cmul _ _ (LF_der_iter_sm hd n (hF m)), Function.iterate_succ_apply']

/-- Iterates of a derivation are additive on smooth functions. -/
private lemma LF_der_iter_add {d : (ℂ → ℂ) → ℂ → ℂ} (hd : LF_Der d) (n : ℕ) {f g : ℂ → ℂ}
    (hf : LF_Sm f) (hg : LF_Sm g) :
    d^[n] (fun x => f x + g x) = fun x => d^[n] f x + d^[n] g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hd.add _ _ (LF_der_iter_sm hd n hf) (LF_der_iter_sm hd n hg),
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- Iterates of a derivation commute with constant factors. -/
private lemma LF_der_iter_cmul {d : (ℂ → ℂ) → ℂ → ℂ} (hd : LF_Der d) (n : ℕ) (c : ℂ)
    {f : ℂ → ℂ} (hf : LF_Sm f) :
    d^[n] (fun x => c * f x) = fun x => c * d^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hd.cmul _ _ (LF_der_iter_sm hd n hf),
      Function.iterate_succ_apply']

/-- The Leibniz rule for iterates of a derivation on smooth functions. -/
private lemma LF_leib {d : (ℂ → ℂ) → ℂ → ℂ} (hd : LF_Der d) {f g : ℂ → ℂ} (hf : LF_Sm f)
    (hg : LF_Sm g) (n : ℕ) :
    d^[n] (fun x => f x * g x) = fun x => ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℂ) * (d^[m] f x * d^[n - m] g x) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hs : ∀ m, LF_Sm (fun x => d^[m] f x * d^[n - m] g x) := fun m =>
      LF_sm_mul (LF_der_iter_sm hd m hf) (LF_der_iter_sm hd (n - m) hg)
    rw [hd.sum _ _ fun m => LF_sm_cmul _ (hs m)]
    funext x
    rw [Finset.sum_choose_succ_mul (fun i j => d^[i] f x * d^[j] g x) n]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [hd.cmul _ _ (hs m), hd.mul _ _ (LF_der_iter_sm hd m hf) (LF_der_iter_sm hd (n - m) hg)]
    rw [← Function.iterate_succ_apply' d m f, ← Function.iterate_succ_apply' d (n - m) g]
    rw [show n + 1 - m = (n - m).succ by omega]
    ring

/-- The Leibniz rule for the mixed derivatives `∂_w^a ∂_{w̄}^b` of a product of smooth
functions. -/
private lemma LF_wirt_mul {f g : ℂ → ℂ} (hf : LF_Sm f) (hg : LF_Sm g) (a b : ℕ) (x : ℂ) :
    wirt a b (fun y => f y * g y) x = ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
      (a.choose a' : ℂ) * (b.choose b' : ℂ) * (wirt a' b' f x * wirt (a - a') (b - b') g x) := by
  unfold wirt
  rw [LF_leib LF_der_dWbar hf hg b]
  have hs : ∀ m, LF_Sm (fun x => dWbar^[m] f x * dWbar^[b - m] g x) := fun m =>
    LF_sm_mul (LF_der_iter_sm LF_der_dWbar m hf) (LF_der_iter_sm LF_der_dWbar (b - m) hg)
  rw [LF_der_iter_lin LF_der_dW a _ _ _ hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [LF_leib LF_der_dW (LF_der_iter_sm LF_der_dWbar b' hf)
    (LF_der_iter_sm LF_der_dWbar (b - b') hg) a]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  ring

/-- The mixed derivatives of a constant. -/
private lemma LF_wirt_const (c : ℂ) (a b : ℕ) :
    wirt a b (fun _ => c) = fun _ => if a = 0 ∧ b = 0 then c else 0 := by
  unfold wirt
  rw [LF_der_iter_const LF_der_dWbar b c]
  by_cases hb : b = 0
  · simp only [hb, ite_true]
    rw [LF_der_iter_const LF_der_dW a c]
    simp
  · simp only [hb, ite_false, and_false]
    rw [LF_der_iter_const LF_der_dW a 0]
    simp

/-- Linearity of the mixed derivatives. -/
private lemma LF_wirt_lin {f g : ℂ → ℂ} (hf : LF_Sm f) (hg : LF_Sm g) (c₁ c₂ : ℂ) (a b : ℕ) :
    wirt a b (fun x => c₁ * f x + c₂ * g x) = fun x => c₁ * wirt a b f x + c₂ * wirt a b g x := by
  unfold wirt
  rw [LF_der_iter_add LF_der_dWbar b (LF_sm_cmul c₁ hf) (LF_sm_cmul c₂ hg),
    LF_der_iter_cmul LF_der_dWbar b c₁ hf, LF_der_iter_cmul LF_der_dWbar b c₂ hg,
    LF_der_iter_add LF_der_dW a (LF_sm_cmul c₁ (LF_der_iter_sm LF_der_dWbar b hf))
      (LF_sm_cmul c₂ (LF_der_iter_sm LF_der_dWbar b hg)),
    LF_der_iter_cmul LF_der_dW a c₁ (LF_der_iter_sm LF_der_dWbar b hf),
    LF_der_iter_cmul LF_der_dW a c₂ (LF_der_iter_sm LF_der_dWbar b hg)]

/-- `∂_{w̄} ∂_w f = ∂_w ∂_{w̄} f` for smooth `f` (symmetry of the second derivative). -/
private lemma LF_dWbar_dW {f : ℂ → ℂ} (hf : LF_Sm f) : dWbar (dW f) = dW (dWbar f) := by
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
private lemma LF_iter_comm {f : ℂ → ℂ} (hf : LF_Sm f) (a b : ℕ) :
    dWbar^[a] (dW^[b] f) = dW^[b] (dWbar^[a] f) := by
  have one : ∀ (b : ℕ) (g : ℂ → ℂ), LF_Sm g → dWbar (dW^[b] g) = dW^[b] (dWbar g) := by
    intro b
    induction b with
    | zero => intro g _; rfl
    | succ b ih =>
      intro g hg
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        LF_dWbar_dW (LF_der_iter_sm LF_der_dW b hg), ih g hg]
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, one b _ (LF_der_iter_sm LF_der_dWbar a hf),
      Function.iterate_succ_apply']

/-- The mixed derivatives of a complex conjugate: `∂_w^a ∂_{w̄}^b f̄ = conj(∂_w^b ∂_{w̄}^a f)`. -/
private lemma LF_wirt_conj {f : ℂ → ℂ} (hf : LF_Sm f) (a b : ℕ) :
    wirt a b (fun x => starRingEnd ℂ (f x)) = fun x => starRingEnd ℂ (wirt b a f x) := by
  have hb : ∀ (n : ℕ) (g : ℂ → ℂ), LF_Sm g →
      dWbar^[n] (fun x => starRingEnd ℂ (g x)) = fun x => starRingEnd ℂ (dW^[n] g x) := by
    intro n
    induction n with
    | zero => intro g _; rfl
    | succ n ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
      exact funext fun x => (dW_conj ((LF_der_iter_sm LF_der_dW n hg).diff x)).2
  have ha : ∀ (n : ℕ) (g : ℂ → ℂ), LF_Sm g →
      dW^[n] (fun x => starRingEnd ℂ (g x)) = fun x => starRingEnd ℂ (dWbar^[n] g x) := by
    intro n
    induction n with
    | zero => intro g _; rfl
    | succ n ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
      exact funext fun x => (dW_conj ((LF_der_iter_sm LF_der_dWbar n hg).diff x)).1
  unfold wirt
  rw [hb b f hf, ha a _ (LF_der_iter_sm LF_der_dW b hf), LF_iter_comm hf a b]

/-! ### Bounds on the mixed derivatives of products -/

/-- The Leibniz bound: if `|∂^{(a,b)} f| ≤ Γ^{a+b} α^{a+b} c_f` and `|∂^{(a,b)} g| ≤ Γ^{a+b} β^{a+b}
c_g` at `w` for `a + b ≤ k`, then `|∂^{(a,b)} (f g)| ≤ Γ^{a+b} (α + β)^{a+b} c_f c_g`. -/
private lemma LF_LB {f g : ℂ → ℂ} (hf : LF_Sm f) (hg : LF_Sm g) (w : ℂ) (Γ α β cf cg : ℝ)
    (k : ℕ) (hΓ : 0 ≤ Γ) (hα : 0 ≤ α) (hcf : 0 ≤ cf)
    (hF : ∀ a b, a + b ≤ k → ‖wirt a b f w‖ ≤ Γ ^ (a + b) * α ^ (a + b) * cf)
    (hG : ∀ a b, a + b ≤ k → ‖wirt a b g w‖ ≤ Γ ^ (a + b) * β ^ (a + b) * cg) :
    ∀ a b, a + b ≤ k →
      ‖wirt a b (fun y => f y * g y) w‖ ≤ Γ ^ (a + b) * (α + β) ^ (a + b) * (cf * cg) := by
  intro a b hab
  rw [LF_wirt_mul hf hg a b w]
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
private lemma LF_pow_jet {u : ℂ → ℂ} (hu : LF_Sm u) (w : ℂ) (Γ c : ℝ) (k : ℕ) (hΓ : 0 ≤ Γ)
    (hc : 0 ≤ c) (hU : ∀ a b, a + b ≤ k → ‖wirt a b u w‖ ≤ Γ ^ (a + b) * c) (m : ℕ) :
    ∀ a b, a + b ≤ k →
      ‖wirt a b (fun y => u y ^ m) w‖ ≤ Γ ^ (a + b) * (m : ℝ) ^ (a + b) * c ^ m := by
  induction m with
  | zero =>
    intro a b _
    simp only [pow_zero, LF_wirt_const]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have : a + b ≠ 0 := by omega
      simp [zero_pow this]
  | succ m ih =>
    intro a b hab
    have e : (fun y => u y ^ (m + 1)) = fun y => u y ^ m * u y := funext fun y => pow_succ _ _
    rw [e]
    have := LF_LB (LF_sm_pow hu m) hu w Γ m 1 (c ^ m) c k hΓ (Nat.cast_nonneg m)
      (pow_nonneg hc m) ih (fun a b hab => by rw [one_pow, mul_one]; exact hU a b hab) a b hab
    rw [pow_succ]
    push_cast
    exact this

/-- The first derivatives of a power: `|∂ u^m| ≤ m β x^{m-1}` when `|u| ≤ x` and `|∂ u| ≤ β`. -/
private lemma LF_pow_d1 {u : ℂ → ℂ} (hu : LF_Sm u) (w : ℂ) (x β : ℝ) (hx : ‖u w‖ ≤ x)
    (hβ1 : ‖dW u w‖ ≤ β) (hβ2 : ‖dWbar u w‖ ≤ β) (m : ℕ) :
    ‖dW (fun y => u y ^ m) w‖ ≤ m * β * x ^ (m - 1) ∧
      ‖dWbar (fun y => u y ^ m) w‖ ≤ m * β * x ^ (m - 1) := by
  have hx0 : 0 ≤ x := (norm_nonneg _).trans hx
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ1
  induction m with
  | zero =>
    simp only [pow_zero]
    rw [LF_der_dW.const, LF_der_dWbar.const]
    simp
  | succ m ih =>
    have e : (fun y => u y ^ (m + 1)) = fun y => u y ^ m * u y := funext fun y => pow_succ _ _
    rw [e, LF_der_dW.mul _ _ (LF_sm_pow hu m) hu, LF_der_dWbar.mul _ _ (LF_sm_pow hu m) hu]
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
private lemma LF_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
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
private lemma LF_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this


/-! ### Norms of the vectors and crude bounds on the forms -/

/-- `|x^* A y| ≤ ‖A‖` for vectors `x`, `y` of norm `≤ 1`. -/
private lemma LF_form_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
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
private lemma LF_mulVec_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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
private lemma LF_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) : opNorm Tᴴ = opNorm T := by
  change ‖Tᴴ‖ = ‖T‖
  exact Matrix.l2_opNorm_conjTranspose T

/-- A standard basis vector has norm `1`. -/
private lemma LF_single_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    ∑ r, ‖(Pi.single k (1 : ℂ) : ι → ℂ) r‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp


private lemma LF_ne_bot : (Finset.univ : Finset (Fin 1)) ≠ ⊥ := by simp

/-- The only set partition of `Fin 1` is the one with a single block. -/
private lemma LF_part_one (π : Finpartition (Finset.univ : Finset (Fin 1))) :
    π = Finpartition.indiscrete LF_ne_bot := by
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
private lemma LF_ccum01 {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h i j) 0 1 = 0 := by
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  unfold ccum jointCum
  rw [Finset.sum_eq_single (Finpartition.indiscrete LF_ne_bot)
    (fun π _ hπ => absurd (LF_part_one π) hπ) (by simp)]
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
private lemma LF_regroup (F : ℕ → ℕ → ℂ) (l : ℕ) :
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
private def LF_pdW {E : Type*} (Ψ : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun p => dW (fun w => Ψ (p.1, w)) p.2

/-- The derivative `∂_{w̄}` of the slice `w ↦ Ψ(p₁, w)`, as a function of `(p₁, w)`. -/
private def LF_pdWb {E : Type*} (Ψ : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun p => dWbar (fun w => Ψ (p.1, w)) p.2

/-- The partial derivative of a jointly smooth function in the direction `v` of the last
variable is jointly smooth. -/
private lemma LF_fderiv_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (v : ℂ) (n : ℕ) :
    ContDiff ℝ n (fun p : E × ℂ => fderiv ℝ (fun w => Ψ (p.1, w)) p.2 v) := by
  have h1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry fun (p : E × ℂ) (w : ℂ) => Ψ (p.1, w)) :=
    (hΨ (n + 1)).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have h2 := ContDiff.fderiv h1 (contDiff_snd (𝕜 := ℝ) (E := E) (F := ℂ) (n := (n : WithTop ℕ∞)))
    (by push_cast; exact le_rfl)
  exact h2.clm_apply contDiff_const

/-- `∂_w` and `∂_{w̄}` of the slices of a jointly smooth function are jointly smooth. -/
private lemma LF_pd_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) :
    (∀ n : ℕ, ContDiff ℝ n (LF_pdW Ψ)) ∧ (∀ n : ℕ, ContDiff ℝ n (LF_pdWb Ψ)) := by
  constructor
  · intro n
    unfold LF_pdW dW
    exact ((LF_fderiv_param hΨ 1 n).sub
      (contDiff_const.mul (LF_fderiv_param hΨ Complex.I n))).div_const 2
  · intro n
    unfold LF_pdWb dWbar
    exact ((LF_fderiv_param hΨ 1 n).add
      (contDiff_const.mul (LF_fderiv_param hΨ Complex.I n))).div_const 2

/-- The iterated parametric derivatives of a jointly smooth function are jointly smooth. -/
private lemma LF_iter_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (a b : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (LF_pdW^[a] (LF_pdWb^[b] Ψ)) := by
  have hb : ∀ b : ℕ, ∀ n : ℕ, ContDiff ℝ n (LF_pdWb^[b] Ψ) := by
    intro b
    induction b with
    | zero => exact hΨ
    | succ b ih => rw [Function.iterate_succ_apply']; exact (LF_pd_smooth ih).2
  induction a with
  | zero => exact hb b
  | succ a ih => rw [Function.iterate_succ_apply']; exact (LF_pd_smooth ih).1

/-- The mixed Wirtinger derivatives of a slice are the slices of the iterated parametric
derivatives. -/
private lemma LF_wirt_param {E : Type*} (Ψ : E × ℂ → ℂ) (x : E) (a b : ℕ) :
    wirt a b (fun w => Ψ (x, w)) = fun w => (LF_pdW^[a] (LF_pdWb^[b] Ψ)) (x, w) := by
  have hb : ∀ (n : ℕ) (Φ : E × ℂ → ℂ),
      dWbar^[n] (fun w => Φ (x, w)) = fun w => (LF_pdWb^[n] Φ) (x, w) := by
    intro n
    induction n with
    | zero => intro Φ; rfl
    | succ n ih =>
      intro Φ
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  have ha : ∀ (n : ℕ) (Φ : E × ℂ → ℂ),
      dW^[n] (fun w => Φ (x, w)) = fun w => (LF_pdW^[n] Φ) (x, w) := by
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
private lemma LF_wirt_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E × ℂ → ℂ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (a b : ℕ) :
    Continuous (fun p : E × ℂ => wirt a b (fun w => Ψ (p.1, w)) p.2) := by
  have e : (fun p : E × ℂ => wirt a b (fun w => Ψ (p.1, w)) p.2) =
      LF_pdW^[a] (LF_pdWb^[b] Ψ) := by
    funext p
    rw [LF_wirt_param]
  rw [e]
  exact (LF_iter_smooth hΨ a b 0).continuous

/-- The substitution `(h, w) ↦ setEntry h i j w` is jointly smooth. -/
private lemma LF_contDiff_setEntry {D N : ℕ} (i j : Idx D N) (n : ℕ) :
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
private lemma LF_slice_sym {D N : ℕ} (F : (Idx D N → Idx D N → ℂ) → ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    F (setEntry h i j w) = F (symArr (setEntry h i j w)) := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

/-- The slices of `F` through Hermitian arrays are smooth when `F ∘ symArr` is smooth. -/
private lemma LF_sm_slice {D N : ℕ} {F : (Idx D N → Idx D N → ℂ) → ℂ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (fun h => F (symArr h))) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    LF_Sm (fun w => F (setEntry h i j w)) := fun n => by
  have e : (fun w => F (setEntry h i j w)) =
      (fun h' => F (symArr h')) ∘ (fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2) ∘
        (fun w : ℂ => (h, w)) := by
    funext w
    simp only [Function.comp]
    exact LF_slice_sym F h hh i j w
  rw [e]
  exact (hF n).comp ((LF_contDiff_setEntry i j n).comp (contDiff_prodMk_right h))

/-- The integrands `h ↦ ∂_w^a ∂_{w̄}^b F(setEntry h i j w)|_{w = h_{ij}}` of Lemma 2.11
[lem:complex_cumu] are almost everywhere strongly measurable for an almost surely Hermitian
law, when `F ∘ symArr` is smooth. -/
private lemma LF_wirt_aesm {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) {F : (Idx D N → Idx D N → ℂ) → ℂ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (fun h => F (symArr h))) (i j : Idx D N) (a b : ℕ) :
    AEStronglyMeasurable (fun h => wirt a b (fun w => F (setEntry h i j w)) (h i j)) μ := by
  let Ψ : (Idx D N → Idx D N → ℂ) × ℂ → ℂ := fun p => F (symArr (setEntry p.1 i j p.2))
  have hΨs : ∀ n : ℕ, ContDiff ℝ n Ψ := fun n =>
    (hF n).comp (LF_contDiff_setEntry i j n)
  have hc := LF_wirt_cont hΨs a b
  have hpair : Continuous (fun h : Idx D N → Idx D N → ℂ => (h, h i j)) :=
    continuous_id.prodMk ((continuous_apply j).comp (continuous_apply i))
  have hcont := hc.comp hpair
  refine hcont.aestronglyMeasurable.congr ?_
  filter_upwards [hμh] with h hh
  have e : (fun w => Ψ (h, w)) = fun w => F (setEntry h i j w) := by
    funext w
    exact (LF_slice_sym F h hh i j w).symm
  change wirt a b (fun w => Ψ (h, w)) (h i j) = _
  rw [e]

/-! ### Entrywise Wirtinger derivatives of matrix-valued slices -/

/-- The entrywise derivative `(∂_x + s ∂_y)/2` of a matrix-valued function of `w = x + iy`;
`s = -i` gives `∂_w` and `s = i` gives `∂_{w̄}`. -/
private def LF_dm {ι : Type*} (s : ℂ) (M : ℂ → Matrix ι ι ℂ) (w : ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun k l => (fderiv ℝ (fun w => M w k l) w 1 +
    s * fderiv ℝ (fun w => M w k l) w Complex.I) / 2

/-- Matrix-valued functions with smooth entries. -/
private def LF_Dm {ι : Type*} (M : ℂ → Matrix ι ι ℂ) : Prop := ∀ k l, LF_Sm (fun w => M w k l)

/-- `s = -i` is the entrywise `∂_w`. -/
private lemma LF_dm_dW {ι : Type*} (M : ℂ → Matrix ι ι ℂ) (w : ℂ) (k l : ι) :
    LF_dm (-Complex.I) M w k l = dW (fun w => M w k l) w := by
  simp only [LF_dm, dW, Matrix.of_apply]
  ring

/-- `s = i` is the entrywise `∂_{w̄}`. -/
private lemma LF_dm_dWbar {ι : Type*} (M : ℂ → Matrix ι ι ℂ) (w : ℂ) (k l : ι) :
    LF_dm Complex.I M w k l = dWbar (fun w => M w k l) w := by
  simp only [LF_dm, dWbar, Matrix.of_apply]

/-- Constant matrix-valued functions have smooth entries. -/
private lemma LF_Dm.const {ι : Type*} (C : Matrix ι ι ℂ) : LF_Dm (fun _ : ℂ => C) :=
  fun _ _ => LF_sm_const _

/-- Products of matrix-valued functions with smooth entries have smooth entries. -/
private lemma LF_Dm.mul {ι : Type*} [Fintype ι] {M₁ M₂ : ℂ → Matrix ι ι ℂ} (h₁ : LF_Dm M₁)
    (h₂ : LF_Dm M₂) : LF_Dm (fun w => M₁ w * M₂ w) := fun k l n => by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun m _ => (h₁ k m n).mul (h₂ m l n)

/-- Scalar multiples of matrix-valued functions with smooth entries have smooth entries. -/
private lemma LF_Dm.smul {ι : Type*} (c : ℂ) {M : ℂ → Matrix ι ι ℂ} (h : LF_Dm M) :
    LF_Dm (fun w => c • M w) := fun k l n => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.mul (h k l n)

/-- The product rule for the entrywise derivative. -/
private lemma LF_dm_mul {ι : Type*} [Fintype ι] (s : ℂ) {M₁ M₂ : ℂ → Matrix ι ι ℂ}
    (h₁ : LF_Dm M₁) (h₂ : LF_Dm M₂) :
    LF_dm s (fun w => M₁ w * M₂ w) = fun w => LF_dm s M₁ w * M₂ w + M₁ w * LF_dm s M₂ w := by
  funext w
  ext k l
  have hd : ∀ m, DifferentiableAt ℝ (fun w => M₁ w k m * M₂ w m l) w := fun m =>
    ((h₁ k m).diff w).mul ((h₂ m l).diff w)
  simp only [LF_dm, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [fderiv_fun_sum fun m _ => hd m]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [fderiv_fun_mul ((h₁ k m).diff w) ((h₂ m l).diff w)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- The entrywise derivative of a constant matrix vanishes. -/
private lemma LF_dm_const {ι : Type*} (s : ℂ) (C : Matrix ι ι ℂ) :
    LF_dm s (fun _ : ℂ => C) = fun _ => 0 := by
  funext w
  ext k l
  simp [LF_dm]

/-- The entrywise derivative is additive. -/
private lemma LF_dm_add {ι : Type*} (s : ℂ) {M₁ M₂ : ℂ → Matrix ι ι ℂ} (h₁ : LF_Dm M₁)
    (h₂ : LF_Dm M₂) :
    LF_dm s (fun w => M₁ w + M₂ w) = fun w => LF_dm s M₁ w + LF_dm s M₂ w := by
  funext w
  ext k l
  simp only [LF_dm, Matrix.of_apply, Matrix.add_apply]
  rw [fderiv_fun_add ((h₁ k l).diff w) ((h₂ k l).diff w)]
  simp only [_root_.add_apply]
  ring

/-- The entrywise derivative commutes with scalar multiplication. -/
private lemma LF_dm_smul {ι : Type*} (s c : ℂ) {M : ℂ → Matrix ι ι ℂ} (h : LF_Dm M) :
    LF_dm s (fun w => c • M w) = fun w => c • LF_dm s M w := by
  funext w
  ext k l
  simp only [LF_dm, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul ((h k l).diff w)]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/-- `(P E_{ij} Q)_{kl} = P_{ki} Q_{jl}` for the matrix unit `E_{ij}`. -/
private lemma LF_single_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℂ)
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
private def LF_g {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (h : Idx D N → Idx D N → ℂ)
    (i j : Idx D N) (w : ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of (setEntry h i j w) + Λ) ξ

/-- The resolvent along a slice through a Hermitian array has smooth entries. -/
private lemma LF_Dm.g {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {ξ : ℂ}
    (hξ : ξ.im ≠ 0) {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) : LF_Dm (LF_g Λ ξ h i j) := fun k l =>
  LF_sm_slice (F := fun h' => res (Matrix.of h' + Λ) ξ k l)
    (fun n => contDiff_res_symArr Λ hΛ ξ hξ k l n) h hh i j

/-- The constant `c = 1` for `i ≠ j` and `c = 1/2` for `i = j` of the slice derivatives. -/
private def LF_cc {D N : ℕ} (i j : Idx D N) : ℂ := if i = j then 1 / 2 else 1

/-- The matrix unit of the slice derivative: `E_{ij}` for `∂_w`, `E_{ji}` for `∂_{w̄}`. -/
private def LF_E {D N : ℕ} (s : ℂ) (i j : Idx D N) : Matrix (Idx D N) (Idx D N) ℂ :=
  if s = Complex.I then Matrix.single j i 1 else Matrix.single i j 1

/-- `∂_w G = -c G E_{ij} G` and `∂_{w̄} G = -c G E_{ji} G` along a Hermitian slice. -/
private lemma LF_dm_g {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {ξ : ℂ}
    (hξ : ξ.im ≠ 0) {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) :
    LF_dm s (LF_g Λ ξ h i j) = fun w =>
      (-LF_cc i j) • (LF_g Λ ξ h i j w * LF_E s i j * LF_g Λ ξ h i j w) := by
  funext w
  ext k l
  obtain ⟨d1, d2⟩ := res_dW Λ hΛ ξ hξ h hh i j k l
  rcases hs with rfl | rfl
  · rw [LF_dm_dWbar]
    simp only [LF_g] at d2 ⊢
    rw [d2]
    simp only [LF_E, ite_true, Matrix.smul_apply, LF_single_entry, smul_eq_mul, LF_cc]
  · have hne : -Complex.I ≠ Complex.I := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    rw [LF_dm_dW]
    simp only [LF_g] at d1 ⊢
    rw [d1]
    simp only [LF_E, hne, ite_false, Matrix.smul_apply, LF_single_entry, smul_eq_mul, LF_cc]

/-! ### Norms of vectors and matrices, Ward's identity -/

/-- The squared Euclidean norm `Σ_k |v_k|²`. -/
private def LF_ns {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ k, ‖v k‖ ^ 2

/-- The squared Hilbert–Schmidt norm `Σ_{k,l} |M_{kl}|²`. -/
private def LF_fs {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ := ∑ k, ∑ l, ‖M k l‖ ^ 2

private lemma LF_fs_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : 0 ≤ LF_fs M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- `|x^* A y| ≤ ‖A‖ |x| |y|`. -/
private lemma LF_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x y : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ≤ opNorm A * (Real.sqrt (LF_ns x) * Real.sqrt (LF_ns y)) := by
  have e : star x ⬝ᵥ (A *ᵥ y) = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 y)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanCLM_toLp]
    simp [dotProduct_comm]
  have hxn : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (LF_ns x) := by
    rw [EuclideanSpace.norm_eq]; rfl
  have hyn : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ = Real.sqrt (LF_ns y) := by
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
private lemma LF_opNorm_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `x^* (A y) = (Aᴴ x)^* y`. -/
private lemma LF_dot_adj {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

/-- Ward's identity (2.32) [eq_Ward] for a vector, on both half planes:
`|G u|² = Im(u^* G u) / Im ζ` for `G = (X - ζ)⁻¹`, `X` Hermitian, `Im ζ ≠ 0`. -/
private lemma LF_ward {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (u : ι → ℂ) :
    LF_ns (res X ζ *ᵥ u) = (star u ⬝ᵥ (res X ζ *ᵥ u)).im / ζ.im := by
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
  have hn : ((LF_ns (R *ᵥ u) : ℝ) : ℂ) = star u ⬝ᵥ ((Rᴴ * R) *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, LF_dot_adj, Matrix.conjTranspose_conjTranspose]
    simp only [LF_ns, dotProduct, Pi.star_apply]
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
    rw [LF_dot_adj, Matrix.conjTranspose_conjTranspose]
    simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Matrix.mulVec, Complex.star_def,
      Complex.conj_conj]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  apply Complex.ofReal_injective
  rw [hn, e3, e4, hz, Complex.sub_conj]
  push_cast
  field_simp

/-- `|G u|² ≤ |u^* G u| / |Im ζ|`. -/
private lemma LF_ward_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (u : ι → ℂ) :
    LF_ns (res X ζ *ᵥ u) ≤ ‖star u ⬝ᵥ (res X ζ *ᵥ u)‖ / |ζ.im| := by
  rw [LF_ward X hX ζ hζ u]
  have hw := Complex.abs_im_le_norm (star u ⬝ᵥ (res X ζ *ᵥ u))
  rcases lt_or_gt_of_ne hζ with h | h
  · rw [abs_of_neg h, ← neg_div_neg_eq]
    exact div_le_div_of_nonneg_right ((neg_le_abs _).trans hw) (by linarith)
  · rw [abs_of_pos h]
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans hw) h.le

/-- `‖G(ζ)‖ ≤ |Im ζ|⁻¹` on both half planes. -/
private lemma LF_opNorm_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) : opNorm (res X ζ) ≤ |ζ.im|⁻¹ := by
  rcases lt_or_gt_of_ne hζ with h | h
  · have h' : 0 < (starRingEnd ℂ ζ).im := by simpa using h
    have e : res X ζ = (res X (starRingEnd ℂ ζ))ᴴ := by
      have := res_conj X hX (starRingEnd ℂ ζ) h'
      rw [Complex.conj_conj] at this
      exact this
    rw [e, LF_opNorm_conjTranspose, abs_of_neg h]
    have := opNorm_res_le X hX _ h'
    simpa using this
  · rw [abs_of_pos h]
    exact opNorm_res_le X hX ζ h

/-- `|A M|_{HS}² ≤ ‖A‖² |M|_{HS}²`. -/
private lemma LF_fs_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι] (A M : Matrix ι ι ℂ) :
    LF_fs (A * M) ≤ opNorm A ^ 2 * LF_fs M := by
  have e : ∀ P : Matrix ι ι ℂ, LF_fs P = ∑ l, LF_ns (fun k => P k l) := by
    intro P
    simp only [LF_fs, LF_ns]
    exact Finset.sum_comm
  rw [e, e, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have : (fun k => (A * M) k l) = A *ᵥ (fun k => M k l) := by
    funext k
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [this]
  exact LF_mulVec_sq A _

/-- The Hilbert–Schmidt norm is invariant under the conjugate transpose. -/
private lemma LF_fs_conjT {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : LF_fs Mᴴ = LF_fs M := by
  simp only [LF_fs, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- `|M A|_{HS}² ≤ |M|_{HS}² ‖A‖²`. -/
private lemma LF_fs_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M A : Matrix ι ι ℂ) :
    LF_fs (M * A) ≤ LF_fs M * opNorm A ^ 2 := by
  rw [← LF_fs_conjT, Matrix.conjTranspose_mul, ← LF_fs_conjT M, ← LF_opNorm_conjTranspose A,
    mul_comm]
  exact LF_fs_mul_left _ _

/-- `|G|_{HS}² = Σ_l |G e_l|² ≤ Σ_l |G_{ll}| / |Im ζ|`. -/
private lemma LF_fs_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    LF_fs (res X ζ) ≤ ∑ l, ‖res X ζ l l‖ / |ζ.im| := by
  have e : LF_fs (res X ζ) = ∑ l, LF_ns (res X ζ *ᵥ Pi.single l 1) := by
    simp only [LF_fs, LF_ns]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e]
  refine Finset.sum_le_sum fun l _ => (LF_ward_le X hX ζ hζ _).trans_eq ?_
  congr 2
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `(Σ_{k,l} |M_{kl}|)² ≤ (card)² |M|_{HS}²`. -/
private lemma LF_sum_abs_sq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    (∑ k, ∑ l, ‖M k l‖) ^ 2 ≤ ((Fintype.card ι : ℝ) ^ 2) * LF_fs M := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => ‖M p.1 p.2‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul, mul_one, Fintype.sum_prod_type] at h
  rw [LF_fs]
  push_cast at h
  nlinarith [h]

/-! ### The fluctuation term as a polynomial in loops -/

/-- The factors `(B_r, Λ_r, ξ_r)` of a chain. -/
private abbrev LF_T (D N : ℕ) :=
  Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ

/-- The chain `G₂ B G₁` of `X = G₂ B G₁ E_a M₂`. -/
private def LF_lX {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) : List (LF_T D N) :=
  [(1, Λ, z₂), (B, Λ, z₁)]

/-- `X_{βα} = e_β^* G₂ B G₁ (T e_α)`, `T = E_a M₂`: the coefficient of `h_{αβ}` in
`⟨G₁ E_a M₂ H G₂ B⟩` of (3.39) [eq:aftertrace]. -/
private def LF_X {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (h : Idx D N → Idx D N → ℂ) (β α : Idx D N) : ℂ :=
  star (Pi.single β (1 : ℂ)) ⬝ᵥ (chainB h (LF_lX Λ B z₁ z₂) *ᵥ (T *ᵥ Pi.single α 1))

/-- `e_β^* M (T e_α) = (M T)_{βα}`. -/
private lemma LF_form_single {D N : ℕ} (M T : Matrix (Idx D N) (Idx D N) ℂ) (β α : Idx D N) :
    star (Pi.single β (1 : ℂ)) ⬝ᵥ (M *ᵥ (T *ᵥ Pi.single α 1)) = (M * T) β α := by
  rw [Matrix.mulVec_mulVec]
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- A chain of length one and of length two as matrix products. -/
private lemma LF_chain1 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a : LF_T D N) :
    chainB h [a] = a.1 * res (Matrix.of h + a.2.1) a.2.2 := by
  simp [chainB]

private lemma LF_chain2 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (a b : LF_T D N) :
    chainB h [a, b] = a.1 * res (Matrix.of h + a.2.1) a.2.2 * (b.1 * res (Matrix.of h + b.2.1) b.2.2) := by
  simp [chainB]

private lemma LF_chain0 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) :
    chainB h ([] : List (LF_T D N)) = 1 := by
  simp [chainB]

/-- `X_{βα} = (G₂ B G₁ T)_{βα}`. -/
private lemma LF_X_eq {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (h : Idx D N → Idx D N → ℂ) (β α : Idx D N) :
    LF_X Λ B T z₁ z₂ h β α =
      (res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ * T) β α := by
  rw [LF_X, LF_form_single, LF_lX, LF_chain2]
  simp only [Matrix.one_mul, Matrix.mul_assoc]

/-- The coefficients of the six groups of terms of `⟨\underline{G₁E_aM₂HG₂}B⟩`. -/
private def LF_cf (D : ℕ) (θ : ℝ) : Fin 6 → ℂ :=
  ![(D : ℂ)⁻¹, -(D : ℂ)⁻¹, (θ : ℂ) * D, ((1 - θ : ℝ) : ℂ) * (D : ℂ)⁻¹, (θ : ℂ) * D,
    ((1 - θ : ℝ) : ℂ) * (D : ℂ)⁻¹]

/-- The first loops of the terms (the empty chain has loop `1`). -/
private def LF_l1 {D N : ℕ} (Λ T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (x : Fin D) :
    Fin 6 → List (LF_T D N) :=
  ![[], [], [(Ea D N x, Λ, z₂)], [(1, Λ, z₂)], [(T * Ea D N x, Λ, z₁)], [(T, Λ, z₁)]]

/-- The second loops of the terms. -/
private def LF_l2 {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (x : Fin D) :
    Fin 6 → List (LF_T D N) :=
  ![[(T * B, Λ, z₁)], [(B, Λ, z₁), (T * (Λ - z₂ • 1), Λ, z₂)], [(B, Λ, z₁), (T * Ea D N x, Λ, z₂)],
    [(B, Λ, z₁), (T, Λ, z₂)], [(B, Λ, z₁), (Ea D N x, Λ, z₂)], [(B, Λ, z₁), (1, Λ, z₂)]]

/-- `⟨\underline{G₁E_aM₂HG₂}B⟩` on Hermitian arrays as a polynomial in loops: with
`T = E_a M₂`, `⟨G₁TB⟩ - ⟨G₁T(Λ - z₂)G₂B⟩ + θ Σ_x D⟨G₂E_x⟩⟨G₁TE_xG₂B⟩ + (1 - θ)⟨G₂⟩⟨G₁TG₂B⟩
+ θ Σ_x D⟨G₁TE_x⟩⟨G₁E_xG₂B⟩ + (1 - θ)⟨G₁T⟩⟨G₁G₂B⟩`. -/
private def LF_Z {D N : ℕ} (θ : ℝ) (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ∑ t : Fin 6, ∑ x : Fin D, LF_cf D θ t * ntr (chainB h (LF_l1 Λ T z₁ z₂ x t)) *
    ntr (chainB h (LF_l2 Λ B T z₁ z₂ x t))

/-- The counterterms of Definition 2.12 [def:underline]:
`⟨G₁ T S_θ(G₂) G₂ B⟩ + ⟨G₁ S_θ(G₁ T) G₂ B⟩`. -/
private def LF_C {D N : ℕ} (θ : ℝ) (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ntr (res (Matrix.of h + Λ) z₁ * T * (sTheta D N θ (res (Matrix.of h + Λ) z₂) *
      res (Matrix.of h + Λ) z₂) * B) +
    ntr (res (Matrix.of h + Λ) z₁ * sTheta D N θ (res (Matrix.of h + Λ) z₁ * T) *
      res (Matrix.of h + Λ) z₂ * B)

private lemma LF_ntr_add {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P + Q) = ntr P + ntr Q := by
  simp [ntr, Matrix.trace_add, mul_add]

private lemma LF_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

private lemma LF_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

private lemma LF_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (P : κ → Matrix ι ι ℂ) :
    ntr (∑ k ∈ s, P k) = ∑ k ∈ s, ntr (P k) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

private lemma LF_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  unfold ntr
  rw [Matrix.trace_mul_comm]

private lemma LF_ntr_one {D N : ℕ} [NeZero D] [NeZero N] :
    ntr (1 : Matrix (Idx D N) (Idx D N) ℂ) = 1 := by
  have hD : (D : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp only [ntr, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp

/-- `⟨P S_θ(R) Q⟩ = θ Σ_x D⟨R E_x⟩⟨P E_x Q⟩ + (1 - θ)⟨R⟩⟨P Q⟩`. -/
private lemma LF_ntr_S {D N : ℕ} (θ : ℝ) (P R Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (P * sTheta D N θ R * Q) = (θ : ℂ) * (∑ x : Fin D, ((D : ℂ) * ntr (R * Ea D N x)) *
      ntr (P * Ea D N x * Q)) + ((1 - θ : ℝ) : ℂ) * ntr R * ntr (P * Q) := by
  unfold sTheta
  simp only [Matrix.mul_add, Matrix.add_mul, LF_ntr_add, Matrix.mul_smul, Matrix.smul_mul,
    LF_ntr_smul, Matrix.mul_sum, Matrix.sum_mul, LF_ntr_sum, Matrix.mul_one]
  ring

/-- `⟨\underline{G₁E_aM₂HG₂}B⟩ = ⟨G₁ T H G₂ B⟩ + (the counterterms)`, `T = E_a M₂`. -/
private lemma LF_under_eq {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (a : Fin D) (h : Idx D N → Idx D N → ℂ) :
    underTwoB Λ θ h z₁ z₂ a B =
      ntr (res (Matrix.of h + Λ) z₁ * (Ea D N a * MExt Λ z₂) * Matrix.of h *
        res (Matrix.of h + Λ) z₂ * B) + LF_C θ Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h := by
  unfold underTwoB hgUnder LF_C
  simp only [Matrix.mul_add, Matrix.add_mul, LF_ntr_add, Matrix.mul_assoc]
  ring

/-- `⟨G₁ T H G₂ B⟩ = (DN)⁻¹ Σ_{β,α} X_{βα} h_{αβ}`. -/
private lemma LF_ntrH {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    ntr (res (Matrix.of h + Λ) z₁ * T * Matrix.of h * res (Matrix.of h + Λ) z₂ * B) =
      ((D : ℂ) * N)⁻¹ * ∑ β, ∑ α, LF_X Λ B T z₁ z₂ h β α * h α β := by
  have e : res (Matrix.of h + Λ) z₁ * T * Matrix.of h * res (Matrix.of h + Λ) z₂ * B =
      (res (Matrix.of h + Λ) z₁ * T) * (Matrix.of h * (res (Matrix.of h + Λ) z₂ * B)) := by
    simp only [Matrix.mul_assoc]
  have e2 : Matrix.of h * (res (Matrix.of h + Λ) z₂ * B) * (res (Matrix.of h + Λ) z₁ * T) =
      Matrix.of h * (res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ * T) := by
    simp only [Matrix.mul_assoc]
  rw [e, LF_ntr_comm, e2]
  simp only [ntr, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply (M := Matrix.of h), Matrix.of_apply]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
  rw [LF_X_eq]
  ring

/-- On Hermitian arrays the polynomial `LF_Z` is `⟨\underline{G₁E_aM₂HG₂}B⟩` (`underTwoB`). -/
private lemma LF_Z_eq {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z₁ z₂ : ℂ) (hz₂ : z₂.im ≠ 0) (a : Fin D) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    LF_Z θ Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h = underTwoB Λ θ h z₁ z₂ a B := by
  have hres := (res_mul_sub_of_im_ne (Matrix.of h + Λ) (hh.add hΛ) z₂ hz₂).1
  have hHG : Matrix.of h * res (Matrix.of h + Λ) z₂ =
      1 - (Λ - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z₂ := by
    calc Matrix.of h * res (Matrix.of h + Λ) z₂
        = (Matrix.of h + Λ - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z₂ -
            (Λ - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z₂ := by
          rw [← Matrix.sub_mul]; congr 1; abel
      _ = _ := by rw [hres]
  have hD : (D : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
  rw [LF_under_eq]
  unfold LF_C LF_Z
  have eH : res (Matrix.of h + Λ) z₁ * (Ea D N a * MExt Λ z₂) * Matrix.of h *
      res (Matrix.of h + Λ) z₂ * B = res (Matrix.of h + Λ) z₁ * (Ea D N a * MExt Λ z₂) *
        (Matrix.of h * res (Matrix.of h + Λ) z₂) * B := by
    simp only [Matrix.mul_assoc]
  have eS1 : res (Matrix.of h + Λ) z₁ * (Ea D N a * MExt Λ z₂) *
      (sTheta D N θ (res (Matrix.of h + Λ) z₂) * res (Matrix.of h + Λ) z₂) * B =
      (res (Matrix.of h + Λ) z₁ * (Ea D N a * MExt Λ z₂)) *
        sTheta D N θ (res (Matrix.of h + Λ) z₂) * (res (Matrix.of h + Λ) z₂ * B) := by
    simp only [Matrix.mul_assoc]
  have eS2 : res (Matrix.of h + Λ) z₁ * sTheta D N θ (res (Matrix.of h + Λ) z₁ * (Ea D N a *
      MExt Λ z₂)) * res (Matrix.of h + Λ) z₂ * B = res (Matrix.of h + Λ) z₁ *
        sTheta D N θ (res (Matrix.of h + Λ) z₁ * (Ea D N a * MExt Λ z₂)) *
        (res (Matrix.of h + Λ) z₂ * B) := by
    simp only [Matrix.mul_assoc]
  rw [eH, hHG, eS1, eS2, LF_ntr_S, LF_ntr_S]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, LF_cf, LF_l1, LF_l2, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, LF_chain0, LF_chain1,
    LF_chain2, LF_ntr_one, Matrix.one_mul, Matrix.mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  generalize Λ - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ) = L
  generalize res (Matrix.of h + Λ) z₁ = G₁
  generalize res (Matrix.of h + Λ) z₂ = G₂
  generalize MExt Λ z₂ = M
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, LF_ntr_sub]
  simp only [Matrix.mul_assoc]
  have c1 : ntr (Ea D N a * (M * (B * G₁))) = ntr (G₁ * (Ea D N a * (M * B))) := by
    rw [LF_ntr_comm G₁]; simp only [Matrix.mul_assoc]
  have c5 : ∀ x, ntr (Ea D N a * (M * (Ea D N x * G₁))) = ntr (G₁ * (Ea D N a * (M * Ea D N x))) := by
    intro x; rw [LF_ntr_comm G₁]; simp only [Matrix.mul_assoc]
  have c6 : ntr (Ea D N a * (M * G₁)) = ntr (G₁ * (Ea D N a * M)) := by
    rw [LF_ntr_comm G₁]; simp only [Matrix.mul_assoc]
  have c3 : ∀ x, ntr (G₂ * Ea D N x) = ntr (Ea D N x * G₂) := fun x => LF_ntr_comm _ _
  have cB : ∀ Q, ntr (B * Q) = ntr (Q * B) := fun Q => LF_ntr_comm _ _
  simp only [c1, c5, c6, c3, cB, Matrix.mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum]
  have s1 : ∀ f g : Fin D → ℂ, ∑ x, (θ : ℂ) * D * f x * g x = ∑ x, (θ : ℂ) * (D * f x * g x) :=
    fun f g => Finset.sum_congr rfl fun x _ => by ring
  rw [s1, s1]
  field_simp
  ring

/-! ### Bounds on chain entries: crude, and on the good event by Ward's identity -/

/-- `G(ζ)^* = G(ζ̄)` on both half planes. -/
private lemma LF_res_conjT {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) : (res X ζ)ᴴ = res X (starRingEnd ℂ ζ) := by
  rcases lt_or_gt_of_ne hζ with h | h
  · have h' : 0 < (starRingEnd ℂ ζ).im := by simpa using h
    have := res_conj X hX (starRingEnd ℂ ζ) h'
    rw [Complex.conj_conj] at this
    rw [this, Matrix.conjTranspose_conjTranspose]
  · exact (res_conj X hX ζ h).symm

/-- The spectral parameters `ζ ∈ {z, z̄}` with `Im z > 0`. -/
private def LF_pm (z ζ : ℂ) : Prop := ζ = z ∨ ζ = starRingEnd ℂ z

private lemma LF_pm_im {z ζ : ℂ} (hz : 0 < z.im) (hζ : LF_pm z ζ) : |ζ.im| = z.im := by
  rcases hζ with rfl | rfl
  · exact abs_of_pos hz
  · simp [abs_of_pos hz]

private lemma LF_pm_ne {z ζ : ℂ} (hz : 0 < z.im) (hζ : LF_pm z ζ) : ζ.im ≠ 0 := by
  have := LF_pm_im hz hζ
  intro h0
  rw [h0, abs_zero] at this
  linarith

private lemma LF_pm_conj {z ζ : ℂ} (hζ : LF_pm z ζ) : LF_pm z (starRingEnd ℂ ζ) := by
  rcases hζ with rfl | rfl
  · exact Or.inr rfl
  · left; simp

/-- The operator norm of a chain whose factors have `‖B_r‖ ≤ K` and spectral parameters in
`{z, z̄}`, on a Hermitian array: `‖B₁G₁⋯B_qG_q‖ ≤ (K/η)^q`. -/
private lemma LF_opNorm_chain {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (K : ℝ) (hK : 0 ≤ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    ∀ l : List (LF_T D N), (∀ f ∈ l, opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2) →
      opNorm (chainB h l) ≤ (K * z.im⁻¹) ^ l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [LF_chain0, List.length_nil, pow_zero]
    exact LF_opNorm_one
  | cons a t ih =>
    intro hl
    have ha := hl a (List.mem_cons_self)
    have ht := ih fun f hf => hl f (List.mem_cons_of_mem a hf)
    have e : chainB h (a :: t) = a.1 * res (Matrix.of h + a.2.1) a.2.2 * chainB h t := by
      simp [chainB]
    rw [e, List.length_cons, pow_succ']
    have hG : opNorm (res (Matrix.of h + a.2.1) a.2.2) ≤ z.im⁻¹ := by
      rw [ha.2.1]
      have := LF_opNorm_res (Matrix.of h + Λ) (hh.add hΛ) a.2.2 (LF_pm_ne hz ha.2.2)
      rwa [LF_pm_im hz ha.2.2] at this
    have h0 : 0 ≤ opNorm (chainB h t) := norm_nonneg _
    calc opNorm (a.1 * res (Matrix.of h + a.2.1) a.2.2 * chainB h t)
        ≤ opNorm a.1 * opNorm (res (Matrix.of h + a.2.1) a.2.2) * opNorm (chainB h t) :=
          (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) h0)
      _ ≤ K * z.im⁻¹ * (K * z.im⁻¹) ^ t.length := by
          have h1 : opNorm a.1 * opNorm (res (Matrix.of h + a.2.1) a.2.2) ≤ K * z.im⁻¹ :=
            mul_le_mul ha.1 hG (norm_nonneg _) hK
          exact mul_le_mul h1 ht h0 (by positivity)

/-- The good event of the forms over a set `U` of vectors at `z` and `z̄`. -/
private def LF_good {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (U : Set (Idx D N → ℂ))
    (Γ₀ : ℝ) (h : Idx D N → Idx D N → ℂ) : Prop :=
  ∀ ζ, LF_pm z ζ → ∀ u ∈ U, ∀ v ∈ U, ‖star u ⬝ᵥ (res (Matrix.of h + Λ) ζ *ᵥ v)‖ ≤ Γ₀

/-- On the good event, `|G(ζ) v|² ≤ Γ₀/η` and `|G(ζ)^* v|² ≤ Γ₀/η` for `v ∈ U`. -/
private lemma LF_good_ward {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {U : Set (Idx D N → ℂ)} {Γ₀ : ℝ} {h : Idx D N → Idx D N → ℂ}
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z U Γ₀ h) {ζ : ℂ} (hζ : LF_pm z ζ)
    {v : Idx D N → ℂ} (hv : v ∈ U) :
    LF_ns (res (Matrix.of h + Λ) ζ *ᵥ v) ≤ Γ₀ / z.im ∧
      LF_ns ((res (Matrix.of h + Λ) ζ)ᴴ *ᵥ v) ≤ Γ₀ / z.im := by
  have hX := hh.add hΛ
  constructor
  · refine (LF_ward_le _ hX ζ (LF_pm_ne hz hζ) v).trans ?_
    rw [LF_pm_im hz hζ]
    exact div_le_div_of_nonneg_right (hg ζ hζ v hv v hv) hz.le
  · rw [LF_res_conjT _ hX ζ (LF_pm_ne hz hζ)]
    have hζ' := LF_pm_conj hζ
    refine (LF_ward_le _ hX _ (LF_pm_ne hz hζ') v).trans ?_
    rw [LF_pm_im hz hζ']
    exact div_le_div_of_nonneg_right (hg _ hζ' v hv v hv) hz.le

/-- The sharp bound on chain entries on the good event (Ward's identity at both ends): for
chains of length `q ≤ 3` with factors `(Q, Λ, ζ)`, `Q ∈ 𝒬`, `‖Q‖ ≤ K`, `ζ ∈ {z, z̄}`, and
`x, y ∈ X ⊆ U` with `Q^* x ∈ U`: `|x^* C y| ≤ K^q Γ₀ η^{-(q-1)}`. -/
private lemma LF_entry_sharp {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {U : Set (Idx D N → ℂ)} {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z U Γ₀ h)
    (K : ℝ) (hK : 1 ≤ K) (Q : Set (Matrix (Idx D N) (Idx D N) ℂ)) (X : Set (Idx D N → ℂ))
    (hXU : X ⊆ U) (hQX : ∀ B ∈ Q, ∀ x ∈ X, Bᴴ *ᵥ x ∈ U) (l : List (LF_T D N))
    (hl1 : 1 ≤ l.length) (hl3 : l.length ≤ 3)
    (hl : ∀ f ∈ l, f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2) :
    ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB h l *ᵥ y)‖ ≤ K ^ l.length * Γ₀ * (z.im⁻¹) ^ (l.length - 1) := by
  intro x hx y hy
  have hX := hh.add hΛ
  have hη : 0 < z.im := hz
  have hK0 : 0 ≤ K := by linarith
  -- the two ends
  have hend : ∀ f ∈ l, Real.sqrt (LF_ns ((res (Matrix.of h + f.2.1) f.2.2)ᴴ *ᵥ (f.1ᴴ *ᵥ x))) ≤
      Real.sqrt (Γ₀ / z.im) := by
    intro f hf
    obtain ⟨hfQ, -, hfΛ, hfz⟩ := hl f hf
    rw [hfΛ]
    exact Real.sqrt_le_sqrt (LF_good_ward hΛ hz hh hg hfz (hQX _ hfQ x hx)).2
  have hendy : ∀ f ∈ l, Real.sqrt (LF_ns (res (Matrix.of h + f.2.1) f.2.2 *ᵥ y)) ≤
      Real.sqrt (Γ₀ / z.im) := by
    intro f hf
    obtain ⟨-, -, hfΛ, hfz⟩ := hl f hf
    rw [hfΛ]
    exact Real.sqrt_le_sqrt (LF_good_ward hΛ hz hh hg hfz (hXU hy)).1
  have hsq : Real.sqrt (Γ₀ / z.im) * Real.sqrt (Γ₀ / z.im) = Γ₀ * z.im⁻¹ := by
    rw [Real.mul_self_sqrt (by positivity), div_eq_mul_inv]
  have hpow : ∀ n : ℕ, 1 ≤ K ^ n := fun n => one_le_pow₀ hK
  match l, hl1, hl3 with
  | [a], _, _ =>
    have ha := hl a (by simp)
    rw [LF_chain1, ← Matrix.mulVec_mulVec, LF_dot_adj]
    have := hg a.2.2 ha.2.2.2 _ (hQX _ ha.1 x hx) y (hXU hy)
    rw [ha.2.2.1]
    simp only [List.length_singleton, pow_one, Nat.sub_self, pow_zero, mul_one]
    nlinarith
  | [a, b], _, _ =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    rw [LF_chain2]
    have e : star x ⬝ᵥ ((a.1 * res (Matrix.of h + a.2.1) a.2.2 *
        (b.1 * res (Matrix.of h + b.2.1) b.2.2)) *ᵥ y) =
        star ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x)) ⬝ᵥ
          (b.1 *ᵥ (res (Matrix.of h + b.2.1) b.2.2 *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LF_dot_adj,
        LF_dot_adj (res _ _)]
    rw [e]
    refine (LF_form_le _ _ _).trans ?_
    have h1 := hend a (by simp)
    have h2 := hendy b (by simp)
    simp only [List.length_cons, List.length_nil]
    calc opNorm b.1 * (Real.sqrt (LF_ns ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x))) *
          Real.sqrt (LF_ns (res (Matrix.of h + b.2.1) b.2.2 *ᵥ y)))
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
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LF_dot_adj,
        LF_dot_adj (res _ _)]
    rw [e2]
    refine (LF_form_le _ _ _).trans ?_
    have h1 := hend a (by simp)
    have h2 := hendy c (by simp)
    have hbG : opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) ≤ K * z.im⁻¹ * K := by
      have hG : opNorm (res (Matrix.of h + b.2.1) b.2.2) ≤ z.im⁻¹ := by
        rw [hb.2.2.1]
        have := LF_opNorm_res (Matrix.of h + Λ) hX b.2.2 (LF_pm_ne hz hb.2.2.2)
        rwa [LF_pm_im hz hb.2.2.2] at this
      calc opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1)
          ≤ opNorm b.1 * opNorm (res (Matrix.of h + b.2.1) b.2.2) * opNorm c.1 :=
            (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _)
              (norm_nonneg _))
        _ ≤ K * z.im⁻¹ * K :=
            mul_le_mul (mul_le_mul hb.2.1 hG (norm_nonneg _) hK0) hc.2.1 (norm_nonneg _)
              (by positivity)
    simp only [List.length_cons, List.length_nil]
    calc opNorm (b.1 * res (Matrix.of h + b.2.1) b.2.2 * c.1) *
          (Real.sqrt (LF_ns ((res (Matrix.of h + a.2.1) a.2.2)ᴴ *ᵥ (a.1ᴴ *ᵥ x))) *
            Real.sqrt (LF_ns (res (Matrix.of h + c.2.1) c.2.2 *ᵥ y)))
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

/-! ### The vectors of the good event and the derivative bounds of the chains -/

open scoped Matrix.Norms.L2Operator in
/-- `‖E_a‖ ≤ 1`. -/
private lemma LF_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

private lemma LF_Ea_conj (D N : ℕ) (a : Fin D) : (Ea D N a)ᴴ = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

/-- The matrices `Q` of the vectors `Q e_k` of the good event. -/
private def LF_Qf {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    Fin 7 ⊕ (Fin D ⊕ Fin D) → Matrix (Idx D N) (Idx D N) ℂ
  | Sum.inl i => ![1, T, Bᴴ, Bᴴ * T, (T * B)ᴴ, (T * (Λ - z₂ • 1))ᴴ, Tᴴ] i
  | Sum.inr (Sum.inl x) => Ea D N x
  | Sum.inr (Sum.inr x) => (T * Ea D N x)ᴴ

/-- The vectors `Q e_k` of the good event. -/
private def LF_U {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) : Set (Idx D N → ℂ) :=
  Set.range fun p : (Fin 7 ⊕ (Fin D ⊕ Fin D)) × Idx D N =>
    LF_Qf Λ B T z₂ p.1 *ᵥ Pi.single p.2 1

private lemma LF_U_mem {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ)
    (q : Fin 7 ⊕ (Fin D ⊕ Fin D)) (M : Matrix (Idx D N) (Idx D N) ℂ)
    (hM : LF_Qf Λ B T z₂ q = M) (k : Idx D N) :
    M *ᵥ Pi.single k 1 ∈ LF_U Λ B T z₂ := ⟨(q, k), by rw [← hM]⟩

/-- The vectors `e_k` and `T e_k` of the entries of `X`. -/
private def LF_XX {D N : ℕ} (T : Matrix (Idx D N) (Idx D N) ℂ) : Set (Idx D N → ℂ) :=
  Set.range (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)) ∪
    Set.range (fun k : Idx D N => T *ᵥ Pi.single k 1)

/-- The vectors `e_k` of the loops. -/
private def LF_XL (D N : ℕ) : Set (Idx D N → ℂ) :=
  Set.range (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ))

private lemma LF_e_U {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) (k : Idx D N) :
    (Pi.single k 1 : Idx D N → ℂ) ∈ LF_U Λ B T z₂ := by
  have := LF_U_mem Λ B T z₂ (Sum.inl 0) 1 (by simp [LF_Qf]) k
  rwa [Matrix.one_mulVec] at this

private lemma LF_XX_U {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    LF_XX T ⊆ LF_U Λ B T z₂ := by
  rintro v (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact LF_e_U Λ B T z₂ k
  · exact LF_U_mem Λ B T z₂ (Sum.inl 1) T (by simp [LF_Qf]) k

private lemma LF_XL_U {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    LF_XL D N ⊆ LF_U Λ B T z₂ := by
  rintro v ⟨k, rfl⟩
  exact LF_e_U Λ B T z₂ k

/-- The admissible matrices of the factors of `X`: `Q ∈ {1, B}` and `Q^* x ∈ U` for `x` in
`LF_XX`. -/
private lemma LF_QX_ok {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    ∀ Q ∈ ({1, B} : Set (Matrix (Idx D N) (Idx D N) ℂ)), ∀ x ∈ LF_XX T,
      Qᴴ *ᵥ x ∈ LF_U Λ B T z₂ := by
  rintro Q hQ x hx
  rcases hQ with rfl | rfl
  · rw [Matrix.conjTranspose_one, Matrix.one_mulVec]
    exact LF_XX_U Λ B T z₂ hx
  · rcases hx with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact LF_U_mem Λ Q T z₂ (Sum.inl 2) Qᴴ (by simp [LF_Qf]) k
    · rw [Matrix.mulVec_mulVec]
      exact LF_U_mem Λ Q T z₂ (Sum.inl 3) (Qᴴ * T) (by simp [LF_Qf]) k

/-- The admissible matrices of the factors of the loops. -/
private def LF_QL {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    Set (Matrix (Idx D N) (Idx D N) ℂ) :=
  {1, T, B, T * B, T * (Λ - z₂ • 1)} ∪ Set.range (Ea D N) ∪ Set.range (fun x => T * Ea D N x)

private lemma LF_QL_ok {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    ∀ Q ∈ LF_QL Λ B T z₂, ∀ x ∈ LF_XL D N, Qᴴ *ᵥ x ∈ LF_U Λ B T z₂ := by
  rintro Q hQ x ⟨k, rfl⟩
  rcases hQ with ((rfl | rfl | rfl | rfl | rfl) | ⟨y, rfl⟩) | ⟨y, rfl⟩
  · rw [Matrix.conjTranspose_one, Matrix.one_mulVec]; exact LF_e_U Λ B _ z₂ k
  · exact LF_U_mem Λ B Q z₂ (Sum.inl 6) _ (by simp [LF_Qf]) k
  · exact LF_U_mem Λ Q T z₂ (Sum.inl 2) _ (by simp [LF_Qf]) k
  · exact LF_U_mem Λ B T z₂ (Sum.inl 4) _ (by simp [LF_Qf]) k
  · exact LF_U_mem Λ B T z₂ (Sum.inl 5) _ (by simp [LF_Qf]) k
  · rw [LF_Ea_conj]; exact LF_U_mem Λ B T z₂ (Sum.inr (Sum.inl y)) _ rfl k
  · exact LF_U_mem Λ B T z₂ (Sum.inr (Sum.inr y)) _ rfl k

/-- The sharp bound function `Γ_q = K^q Γ₀ η^{-(q-1)}` of the chain entries on the good event. -/
private def LF_Gs (K Γ₀ η : ℝ) (q : ℕ) : ℝ := K ^ q * Γ₀ * (η⁻¹) ^ (q - 1)

private lemma LF_Gs_mul (K Γ₀ η : ℝ) : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    LF_Gs K Γ₀ η a * LF_Gs K Γ₀ η b ≤ LF_Gs K Γ₀ η 1 * LF_Gs K Γ₀ η (a + b - 1) := by
  intro a b ha hb
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [LF_Gs, Nat.add_sub_cancel, show a + 1 + (b + 1) - 1 = a + b + 1 by omega,
    show a + b + 1 - 1 = a + b by omega, Nat.sub_self, pow_zero, pow_one, pow_add, pow_succ]
  ring_nf
  exact le_rfl

/-- The factors of a chain with matrices in `𝒬`, the pair `(Λ, ζ)`, `ζ ∈ {z, z̄}`, and the
factors of the sub-chains admitted in `chainB_wirt_le`. -/
private lemma LF_sub_factors {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {Q : Set (Matrix (Idx D N) (Idx D N) ℂ)} (h1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ Q)
    {K : ℝ} (hK : 1 ≤ K) {l : List (LF_T D N)}
    (hl : ∀ f ∈ l, f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2)
    {l' : List (LF_T D N)} (hl' : ∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) :
    ∀ f ∈ l', f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2 := by
  intro f hf
  rcases hl' f hf with h | ⟨h1', g, hg, hgf⟩
  · exact hl f h
  · obtain ⟨-, -, hgΛ, hgz⟩ := hl g hg
    refine ⟨h1' ▸ h1, h1' ▸ LF_opNorm_one.trans hK, ?_, ?_⟩
    · rw [← hgf]; exact hgΛ
    · rw [← hgf]; exact hgz

/-- The hypothesis of `chainB_wirt_le` on the good event, for chains of length `≤ 2`. -/
private lemma LF_hG_sharp {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {U : Set (Idx D N → ℂ)} {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z U Γ₀ h)
    (K : ℝ) (hK : 1 ≤ K) (Q : Set (Matrix (Idx D N) (Idx D N) ℂ))
    (h1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ Q) (X : Set (Idx D N → ℂ))
    (hXU : X ⊆ U) (hQX : ∀ B ∈ Q, ∀ x ∈ X, Bᴴ *ᵥ x ∈ U) (l : List (LF_T D N))
    (hl2 : l.length ≤ 2) (hl : ∀ f ∈ l, f.1 ∈ Q ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2) :
    ∀ l' : List (LF_T D N), 1 ≤ l'.length → l'.length ≤ l.length + 1 →
      (∀ f ∈ l', f ∈ l ∨ (f.1 = 1 ∧ ∃ g ∈ l, g.2 = f.2)) →
      ∀ x ∈ X, ∀ y ∈ X, ‖star x ⬝ᵥ (chainB h l' *ᵥ y)‖ ≤ LF_Gs K Γ₀ z.im l'.length := by
  intro l' hl1 hl3 hl'
  exact LF_entry_sharp hΛ hz hΓ₀ hh hg K hK Q X hXU hQX l' hl1 (by omega)
    (LF_sub_factors h1 hK hl hl')

/-! ### Smoothness of the chains, the loops and the fluctuation term -/

/-- Entries of chains of the Hermitian part are smooth in the array. -/
private lemma LF_cd_chain {D N : ℕ} :
    ∀ l : List (LF_T D N), (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) → ∀ (k m : Idx D N)
      (n : ℕ), ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => chainB (symArr h) l k m) := by
  intro l
  induction l with
  | nil =>
    intro _ k m n
    simp only [LF_chain0]
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
private lemma LF_cd_form {D N : ℕ} (l : List (LF_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (x y : Idx D N → ℂ) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => star x ⬝ᵥ (chainB (symArr h) l *ᵥ y)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact ContDiff.sum fun k _ => ContDiff.sum fun m _ =>
    contDiff_const.mul ((LF_cd_chain l hl k m n).mul contDiff_const)

/-- Loops of chains of the Hermitian part are smooth in the array. -/
private lemma LF_cd_loop {D N : ℕ} (l : List (LF_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (n : ℕ) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => ntr (chainB (symArr h) l)) := by
  simp only [ntr, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  exact ContDiff.sum fun k _ => contDiff_const.mul (LF_cd_chain l hl k k n)

/-- The factors of the chains of the fluctuation term: Hermitian `Λ` and `Im ζ ≠ 0`. -/
private lemma LF_lX_ok {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
    ∀ f ∈ LF_lX Λ B z₁ z₂, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  simp only [LF_lX, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨hΛ, hz₂⟩
  · exact ⟨hΛ, hz₁⟩

private lemma LF_l1_ok {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (x : Fin D) (t : Fin 6) :
    ∀ f ∈ LF_l1 Λ T z₁ z₂ x t, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  fin_cases t <;> simp [LF_l1] at hf <;> subst hf <;> exact ⟨hΛ, by assumption⟩

private lemma LF_l2_ok {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (x : Fin D) (t : Fin 6) :
    ∀ f ∈ LF_l2 Λ B T z₁ z₂ x t, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  fin_cases t <;> simp [LF_l2] at hf <;> rcases hf with rfl | rfl <;>
    first | exact ⟨hΛ, hz₁⟩ | exact ⟨hΛ, hz₂⟩

/-- `X_{βα}` of the Hermitian part is smooth in the array. -/
private lemma LF_cd_X {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (β α : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun h => LF_X Λ B T z₁ z₂ (symArr h) β α) :=
  LF_cd_form _ (LF_lX_ok hΛ B hz₁ hz₂) _ _ n

/-- The polynomial `LF_Z` of the Hermitian part is smooth in the array. -/
private lemma LF_cd_Z {D N : ℕ} (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (n : ℕ) : ContDiff ℝ n (fun h => LF_Z θ Λ B T z₁ z₂ (symArr h)) := by
  unfold LF_Z
  exact ContDiff.sum fun t _ => ContDiff.sum fun x _ =>
    (contDiff_const.mul (LF_cd_loop _ (LF_l1_ok hΛ T hz₁ hz₂ x t) n)).mul
      (LF_cd_loop _ (LF_l2_ok hΛ B T hz₁ hz₂ x t) n)

/-- The integrand `X_{βα} Z^{p-1} Z̄^p` of the moment expansion. -/
private def LF_F {D N : ℕ} (θ : ℝ) (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (p : ℕ)
    (β α : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  LF_X Λ B T z₁ z₂ h β α * (LF_Z θ Λ B T z₁ z₂ h ^ (p - 1) *
    starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ h) ^ p)

private lemma LF_cd_F {D N : ℕ} (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p : ℕ) (β α : Idx D N) (n : ℕ) :
    ContDiff ℝ n (fun h => LF_F θ Λ B T z₁ z₂ p β α (symArr h)) := by
  unfold LF_F
  exact (LF_cd_X hΛ B T hz₁ hz₂ β α n).mul (((LF_cd_Z θ hΛ B T hz₁ hz₂ n).pow _).mul
    ((Complex.conjCLE.contDiff.comp (LF_cd_Z θ hΛ B T hz₁ hz₂ n)).pow _))

/-! ### Linearity and products of the mixed derivatives -/

/-- `∂_w^a ∂_{w̄}^b (c f) = c ∂_w^a ∂_{w̄}^b f`. -/
private lemma LF_wirt_cmul {f : ℂ → ℂ} (hf : LF_Sm f) (c : ℂ) (a b : ℕ) :
    wirt a b (fun w => c * f w) = fun w => c * wirt a b f w := by
  unfold wirt
  rw [LF_der_iter_cmul LF_der_dWbar b c hf,
    LF_der_iter_cmul LF_der_dW a c (LF_der_iter_sm LF_der_dWbar b hf)]

/-- The mixed derivatives of a finite sum. -/
private lemma LF_wirt_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ i, LF_Sm (f i))
    (a b : ℕ) : wirt a b (fun w => ∑ i ∈ s, f i w) = fun w => ∑ i ∈ s, wirt a b (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [LF_wirt_const]
    funext w
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs : LF_Sm (fun w => ∑ j ∈ s, f j w) := fun n => ContDiff.sum fun j _ => hf j n
    have := LF_wirt_lin (hf i) hs 1 1 a b
    simp only [one_mul] at this
    rw [this, ih]

/-- The product bound for `a + b ≥ 1`: if `|f| ≤ F₀`, `|∂^{(a,b)} f| ≤ Γ^{a+b} F₁` and
`|g| ≤ G₀`, `|∂^{(a,b)} g| ≤ Γ^{a+b} G₁` for `1 ≤ a + b ≤ k`, then
`|∂^{(a,b)} (f g)| ≤ (2Γ)^{a+b} (F₀ G₁ + F₁ G₀ + F₁ G₁)`. -/
private lemma LF_LB2 {f g : ℂ → ℂ} (hf : LF_Sm f) (hg : LF_Sm g) (w : ℂ) (Γ F₀ F₁ G₀ G₁ : ℝ)
    (k : ℕ) (hΓ : 0 ≤ Γ) (hF₀ : ‖f w‖ ≤ F₀) (hG₀ : ‖g w‖ ≤ G₀) (hF₁0 : 0 ≤ F₁) (hG₁0 : 0 ≤ G₁)
    (hF : ∀ a b, 1 ≤ a + b → a + b ≤ k → ‖wirt a b f w‖ ≤ Γ ^ (a + b) * F₁)
    (hG : ∀ a b, 1 ≤ a + b → a + b ≤ k → ‖wirt a b g w‖ ≤ Γ ^ (a + b) * G₁) :
    ∀ a b, 1 ≤ a + b → a + b ≤ k →
      ‖wirt a b (fun y => f y * g y) w‖ ≤ (2 * Γ) ^ (a + b) * (F₀ * G₁ + F₁ * G₀ + F₁ * G₁) := by
  intro a b hab hk
  have hF₀0 : 0 ≤ F₀ := (norm_nonneg _).trans hF₀
  have hG₀0 : 0 ≤ G₀ := (norm_nonneg _).trans hG₀
  have hS : 0 ≤ F₀ * G₁ + F₁ * G₀ + F₁ * G₁ := by positivity
  rw [LF_wirt_mul hf hg a b w]
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

/-- The deterministic setting of the expansion: `Λ` Hermitian, `Im z > 0`, `z₁, z₂ ∈ {z, z̄}`,
and the norms of the matrices of the chains bounded by `K ≥ 1`. -/
private structure LF_Set {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z z₁ z₂ : ℂ)
    (K : ℝ) : Prop where
  herm : Λ.IsHermitian
  hz : 0 < z.im
  h1 : LF_pm z z₁
  h2 : LF_pm z z₂
  hK : 1 ≤ K
  hB : opNorm B ≤ K
  hT : opNorm T ≤ K
  hTB : opNorm (T * B) ≤ K
  hTL : opNorm (T * (Λ - z₂ • 1)) ≤ K
  hTE : ∀ x, opNorm (T * Ea D N x) ≤ K
  hQ : ∀ q, opNorm (LF_Qf Λ B T z₂ q) ≤ K

/-- The factors of the chain of `X`. -/
private lemma LF_Set.fX {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ}
    (hs : LF_Set Λ B T z z₁ z₂ K) :
    ∀ f ∈ LF_lX Λ B z₁ z₂, f.1 ∈ ({1, B} : Set (Matrix (Idx D N) (Idx D N) ℂ)) ∧
      opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2 := by
  intro f hf
  simp only [LF_lX, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨Or.inl rfl, LF_opNorm_one.trans hs.hK, rfl, hs.h2⟩
  · exact ⟨Or.inr rfl, hs.hB, rfl, hs.h1⟩

/-- The factors of the first loops. -/
private lemma LF_Set.f1 {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ}
    (hs : LF_Set Λ B T z z₁ z₂ K) (x : Fin D) (t : Fin 6) :
    ∀ f ∈ LF_l1 Λ T z₁ z₂ x t, f.1 ∈ LF_QL Λ B T z₂ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
      LF_pm z f.2.2 := by
  intro f hf
  have hE : opNorm (Ea D N x) ≤ K := (LF_opNorm_Ea D N x).trans hs.hK
  fin_cases t <;> simp [LF_l1] at hf <;> subst hf
  · exact ⟨Or.inl (Or.inr ⟨x, rfl⟩), hE, rfl, hs.h2⟩
  · exact ⟨Or.inl (Or.inl (Or.inl rfl)), LF_opNorm_one.trans hs.hK, rfl, hs.h2⟩
  · exact ⟨Or.inr ⟨x, rfl⟩, hs.hTE x, rfl, hs.h1⟩
  · exact ⟨Or.inl (Or.inl (Or.inr (Or.inl rfl))), hs.hT, rfl, hs.h1⟩

/-- The factors of the second loops. -/
private lemma LF_Set.f2 {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ}
    (hs : LF_Set Λ B T z z₁ z₂ K) (x : Fin D) (t : Fin 6) :
    ∀ f ∈ LF_l2 Λ B T z₁ z₂ x t, f.1 ∈ LF_QL Λ B T z₂ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
      LF_pm z f.2.2 := by
  intro f hf
  have hE : opNorm (Ea D N x) ≤ K := (LF_opNorm_Ea D N x).trans hs.hK
  have h1 : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ K := LF_opNorm_one.trans hs.hK
  have mB : B ∈ LF_QL Λ B T z₂ := Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
  have m1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ LF_QL Λ B T z₂ := Or.inl (Or.inl (Or.inl rfl))
  have mT : T ∈ LF_QL Λ B T z₂ := Or.inl (Or.inl (Or.inr (Or.inl rfl)))
  have mTB : T * B ∈ LF_QL Λ B T z₂ := Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have mTL : T * (Λ - z₂ • 1) ∈ LF_QL Λ B T z₂ :=
    Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have mE : Ea D N x ∈ LF_QL Λ B T z₂ := Or.inl (Or.inr ⟨x, rfl⟩)
  have mTE : T * Ea D N x ∈ LF_QL Λ B T z₂ := Or.inr ⟨x, rfl⟩
  fin_cases t <;> simp [LF_l2] at hf
  · subst hf; exact ⟨mTB, hs.hTB, rfl, hs.h1⟩
  all_goals rcases hf with rfl | rfl
  all_goals first
    | exact ⟨mB, hs.hB, rfl, hs.h1⟩
    | exact ⟨mTL, hs.hTL, rfl, hs.h2⟩
    | exact ⟨mTE, hs.hTE x, rfl, hs.h2⟩
    | exact ⟨mT, hs.hT, rfl, hs.h2⟩
    | exact ⟨mE, hE, rfl, hs.h2⟩
    | exact ⟨m1, h1, rfl, hs.h2⟩

private lemma LF_l1_len {D N : ℕ} (Λ T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (x : Fin D)
    (t : Fin 6) : (LF_l1 Λ T z₁ z₂ x t).length ≤ 1 := by
  fin_cases t <;> simp [LF_l1]

private lemma LF_l2_len {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (x : Fin D) (t : Fin 6) :
    1 ≤ (LF_l2 Λ B T z₁ z₂ x t).length ∧ (LF_l2 Λ B T z₁ z₂ x t).length ≤ 2 := by
  fin_cases t <;> simp [LF_l2]

/-- Every Hermitian array is in the good event with `Γ₀ = K² (1 + η⁻¹)`. -/
private lemma LF_good_crude {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    LF_good Λ z (LF_U Λ B T z₂) (K ^ 2 * (1 + z.im⁻¹)) h := by
  intro ζ hζ u hu v hv
  obtain ⟨⟨q, k⟩, rfl⟩ := hu
  obtain ⟨⟨q', k'⟩, rfl⟩ := hv
  have hn : ∀ q k, Real.sqrt (LF_ns (LF_Qf Λ B T z₂ q *ᵥ Pi.single k 1)) ≤ K := by
    intro q k
    have h1 := LF_mulVec_sq (LF_Qf Λ B T z₂ q) (Pi.single k 1)
    have h2 : LF_ns (Pi.single k (1 : ℂ) : Idx D N → ℂ) = 1 := LF_single_sq k
    change LF_ns _ ≤ _ * LF_ns _ at h1
    rw [h2, mul_one] at h1
    refine Real.sqrt_le_iff.mpr ⟨by linarith [hs.hK], h1.trans ?_⟩
    have := hs.hQ q
    have h0 : 0 ≤ opNorm (LF_Qf Λ B T z₂ q) := norm_nonneg _
    nlinarith
  have hG := LF_opNorm_res (Matrix.of h + Λ) (hh.add hs.herm) ζ (LF_pm_ne hs.hz hζ)
  rw [LF_pm_im hs.hz hζ] at hG
  refine (LF_form_le _ _ _).trans ?_
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  calc opNorm (res (Matrix.of h + Λ) ζ) *
        (Real.sqrt (LF_ns (LF_Qf Λ B T z₂ q *ᵥ Pi.single k 1)) *
          Real.sqrt (LF_ns (LF_Qf Λ B T z₂ q' *ᵥ Pi.single k' 1)))
      ≤ z.im⁻¹ * (K * K) := mul_le_mul hG (mul_le_mul (hn q k) (hn q' k') (Real.sqrt_nonneg _)
        (by linarith [hs.hK])) (by positivity) hi
    _ ≤ K ^ 2 * (1 + z.im⁻¹) := by nlinarith [hs.hK]

/-- The jet of `X_{βα}` along a slice at a point of the good event with constant `Γ₀`. -/
private lemma LF_jet_X {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ}
    (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h i j w)) (β α : Idx D N) (a b : ℕ) :
    ‖wirt a b (fun w' => LF_X Λ B T z₁ z₂ (setEntry h i j w') β α) w‖ ≤
      ((2 + a + b : ℕ) : ℝ) ^ (a + b) * LF_Gs K Γ₀ z.im 1 ^ (a + b) * LF_Gs K Γ₀ z.im 2 := by
  have hX : ∀ k : Idx D N, (Pi.single k 1 : Idx D N → ℂ) ∈ LF_XX T := fun k =>
    Or.inl ⟨k, rfl⟩
  have := chainB_wirt_le (LF_lX Λ B z₁ z₂) (by simp [LF_lX])
    (LF_lX_ok hs.herm B (LF_pm_ne hs.hz hs.h1) (LF_pm_ne hs.hz hs.h2)) h hh i j w
    (LF_Gs K Γ₀ z.im) (LF_Gs_mul K Γ₀ z.im) (LF_XX T) ⟨hX i, hX j⟩
    (LF_hG_sharp hs.herm hs.hz hΓ₀ (LF_slice_herm h hh i j w) hg K hs.hK {1, B} (Or.inl rfl)
      (LF_XX T) (LF_XX_U Λ B T z₂) (LF_QX_ok Λ B T z₂) (LF_lX Λ B z₁ z₂) (by simp [LF_lX])
      hs.fX) a b (Pi.single β 1) (hX β) (T *ᵥ Pi.single α 1) (Or.inr ⟨α, rfl⟩)
  have e : (LF_lX Λ B z₁ z₂).length = 2 := rfl
  rw [e] at this
  exact this

/-- The jet of a loop of length `1` or `2` along a slice at a point of the good event. -/
private lemma LF_jet_loop {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h i j w)) (l : List (LF_T D N))
    (hl1 : 1 ≤ l.length) (hl2 : l.length ≤ 2)
    (hl : ∀ f ∈ l, f.1 ∈ LF_QL Λ B T z₂ ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2) :
    ‖ntr (chainB (setEntry h i j w) l)‖ ≤ LF_Gs K Γ₀ z.im l.length ∧
      ∀ a b, 1 ≤ a + b → ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') l)) w‖ ≤
        ((l.length + a + b : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) * N)⁻¹ *
          LF_Gs K Γ₀ z.im 1 ^ (a + b - 1) * LF_Gs K Γ₀ z.im (l.length + 1) := by
  have hX : ∀ k : Idx D N, (Pi.single k 1 : Idx D N → ℂ) ∈ LF_XL D N := fun k => ⟨k, rfl⟩
  have m1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ LF_QL Λ B T z₂ := Or.inl (Or.inl (Or.inl rfl))
  have hok : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := fun f hf => by
    obtain ⟨-, -, h1, h2⟩ := hl f hf
    exact ⟨h1 ▸ hs.herm, LF_pm_ne hs.hz h2⟩
  have hG := LF_hG_sharp hs.herm hs.hz hΓ₀ (LF_slice_herm h hh i j w) hg K hs.hK
    (LF_QL Λ B T z₂) m1 (LF_XL D N) (LF_XL_U Λ B T z₂) (LF_QL_ok Λ B T z₂) l hl2 hl
  constructor
  · have hd : ∀ k, ‖chainB (setEntry h i j w) l k k‖ ≤ LF_Gs K Γ₀ z.im l.length := by
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
    exact loopB_wirt_le l hl1 hok h hh i j w (LF_Gs K Γ₀ z.im) (LF_Gs_mul K Γ₀ z.im) (LF_XL D N)
      ⟨hX i, hX j⟩ hG a b hab

/-- The sum `Σ_{t,x} |c_t|` of the coefficients of `LF_Z`. -/
private def LF_Cz (D : ℕ) (θ : ℝ) : ℝ := ∑ t : Fin 6, ∑ _x : Fin D, ‖LF_cf D θ t‖

private lemma LF_Cz_nonneg (D : ℕ) (θ : ℝ) : 0 ≤ LF_Cz D θ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The derivative scale `Γ_t = (2 + K_m) K Γ₀` of the jets up to order `K_m`. -/
private def LF_Gt (Km : ℕ) (K Γ₀ : ℝ) : ℝ := (2 + Km) * K * Γ₀

/-- The bound `Ψ_Z` on the derivatives of `LF_Z`, of order `Γ₀ (DN)⁻¹ η⁻²`. -/
private def LF_Pz (D N : ℕ) (θ K Γ₀ η : ℝ) : ℝ :=
  LF_Cz D θ * (K * Γ₀ * (K ^ 2 * (((D : ℝ) * N)⁻¹ * (η⁻¹ + η⁻¹ ^ 2))) +
    K * (((D : ℝ) * N)⁻¹ * η⁻¹) * (K ^ 2 * Γ₀ * (1 + η⁻¹)) +
    K * (((D : ℝ) * N)⁻¹ * η⁻¹) * (K ^ 2 * (((D : ℝ) * N)⁻¹ * (η⁻¹ + η⁻¹ ^ 2))))

/-- The jet of `LF_Z` along a slice at a point of the good event, orders `1 ≤ a + b ≤ K_m`. -/
private lemma LF_jet_Z {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h i j w)) (Km : ℕ) :
    ∀ a b, 1 ≤ a + b → a + b ≤ Km →
      ‖wirt a b (fun w' => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w')) w‖ ≤
        (2 * LF_Gt Km K Γ₀) ^ (a + b) * LF_Pz D N θ K Γ₀ z.im := by
  intro a b hab hk
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hη : 0 < z.im := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK := hs.hK
  have hK0 : 0 ≤ K := by linarith
  have hDN : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  set Γt := LF_Gt Km K Γ₀ with hΓt
  have hΓt0 : 0 ≤ Γt := by simp only [hΓt, LF_Gt]; positivity
  have hsm : ∀ l : List (LF_T D N), (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) →
      LF_Sm (fun w' => ntr (chainB (setEntry h i j w') l)) := fun l hl =>
    LF_sm_slice (F := fun h' => ntr (chainB h' l)) (fun n => LF_cd_loop l hl n) h hh i j
  -- the bounds on the loops of the terms
  have hpow : ∀ (n a b : ℕ), n ≤ 2 → 1 ≤ a + b → a + b ≤ Km →
      ((n + a + b : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) * N)⁻¹ * LF_Gs K Γ₀ z.im 1 ^ (a + b - 1) *
        LF_Gs K Γ₀ z.im (n + 1) ≤ Γt ^ (a + b) * (K ^ n * (((D : ℝ) * N)⁻¹ * z.im⁻¹ ^ n)) := by
    intro n a b hn hk1 hkm
    obtain ⟨k, hk⟩ : ∃ k', a + b = k' + 1 := ⟨a + b - 1, by omega⟩
    have hnab : n + a + b = n + (k + 1) := by omega
    rw [hnab, hk, hΓt]
    unfold LF_Gt LF_Gs
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_one, mul_one]
    have h1 : ((n + (k + 1) : ℕ) : ℝ) ≤ 2 + Km := by
      have : n + (k + 1) ≤ 2 + Km := by omega
      exact_mod_cast this
    have h2 : ((n + (k + 1) : ℕ) : ℝ) ^ (k + 1) ≤ (2 + Km) ^ (k + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
    have hΓ0 : 0 ≤ Γ₀ := by linarith
    have h3 : 0 ≤ (K * Γ₀) ^ (k + 1) * K ^ n * ((D : ℝ) * N)⁻¹ * z.im⁻¹ ^ n := by positivity
    calc ((n + (k + 1) : ℕ) : ℝ) ^ (k + 1) * ((D : ℝ) * N)⁻¹ * (K * Γ₀) ^ k *
          (K ^ (n + 1) * Γ₀ * z.im⁻¹ ^ n)
        = ((n + (k + 1) : ℕ) : ℝ) ^ (k + 1) *
            ((K * Γ₀) ^ (k + 1) * K ^ n * ((D : ℝ) * N)⁻¹ * z.im⁻¹ ^ n) := by ring
      _ ≤ (2 + Km) ^ (k + 1) * ((K * Γ₀) ^ (k + 1) * K ^ n * ((D : ℝ) * N)⁻¹ * z.im⁻¹ ^ n) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = ((2 + Km) * K * Γ₀) ^ (k + 1) * (K ^ n * (((D : ℝ) * N)⁻¹ * z.im⁻¹ ^ n)) := by
          rw [mul_pow, mul_pow, mul_pow]; ring
  have hL1 : ∀ x t, ‖ntr (chainB (setEntry h i j w) (LF_l1 Λ T z₁ z₂ x t))‖ ≤ K * Γ₀ ∧
      ∀ a b, 1 ≤ a + b → a + b ≤ Km →
        ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t))) w‖ ≤
          Γt ^ (a + b) * (K * (((D : ℝ) * N)⁻¹ * z.im⁻¹)) := by
    intro x t
    have hlen := LF_l1_len Λ T z₁ z₂ x t
    rcases Nat.lt_or_ge (LF_l1 Λ T z₁ z₂ x t).length 1 with h0 | h1
    · have hnil : LF_l1 Λ T z₁ z₂ x t = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hD : NeZero D := ⟨by have := i.1.pos; omega⟩
      have hN : NeZero N := ⟨by have := i.2.pos; omega⟩
      rw [hnil]
      simp only [LF_chain0, LF_ntr_one, norm_one]
      refine ⟨by nlinarith, fun a b hab _ => ?_⟩
      rw [LF_wirt_const]
      have : ¬ (a = 0 ∧ b = 0) := by omega
      simp only [this, ite_false, norm_zero]
      positivity
    · obtain ⟨hv, hd⟩ := LF_jet_loop hs (by linarith) h hh i j w hg _ h1 (by omega) (hs.f1 x t)
      have hl1' : (LF_l1 Λ T z₁ z₂ x t).length = 1 := by omega
      rw [hl1'] at hv hd
      refine ⟨by simpa [LF_Gs] using hv, fun a b hab hkm => (hd a b hab).trans ?_⟩
      have := hpow 1 a b (by norm_num) hab hkm
      simpa using this
  have hL2 : ∀ x t, ‖ntr (chainB (setEntry h i j w) (LF_l2 Λ B T z₁ z₂ x t))‖ ≤
      K ^ 2 * Γ₀ * (1 + z.im⁻¹) ∧
      ∀ a b, 1 ≤ a + b → a + b ≤ Km →
        ‖wirt a b (fun w' => ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t))) w‖ ≤
          Γt ^ (a + b) * (K ^ 2 * (((D : ℝ) * N)⁻¹ * (z.im⁻¹ + z.im⁻¹ ^ 2))) := by
    intro x t
    obtain ⟨hlen1, hlen2⟩ := LF_l2_len Λ B T z₁ z₂ x t
    obtain ⟨hv, hd⟩ := LF_jet_loop hs (by linarith) h hh i j w hg _ hlen1 hlen2 (hs.f2 x t)
    have hΓ0 : 0 ≤ Γ₀ := by linarith
    rcases Nat.lt_or_ge (LF_l2 Λ B T z₁ z₂ x t).length 2 with h1 | h2
    · have e : (LF_l2 Λ B T z₁ z₂ x t).length = 1 := by omega
      rw [e] at hv hd
      refine ⟨hv.trans ?_, fun a b hab hkm => (hd a b hab).trans ?_⟩
      · simp only [LF_Gs, pow_one, Nat.sub_self, pow_zero, mul_one]
        have h5 : K * Γ₀ ≤ K ^ 2 * Γ₀ := mul_le_mul_of_nonneg_right (by nlinarith) hΓ0
        have h6 : 0 ≤ K ^ 2 * Γ₀ * z.im⁻¹ := by positivity
        nlinarith
      · have := hpow 1 a b (by norm_num) hab hkm
        refine (by simpa using this : _ ≤ Γt ^ (a + b) * (K * (((D : ℝ) * N)⁻¹ * z.im⁻¹))).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΓt0 _)
        have h7 : 0 ≤ ((D : ℝ) * N)⁻¹ * z.im⁻¹ ^ 2 := by positivity
        have hX : 0 ≤ ((D : ℝ) * N)⁻¹ * z.im⁻¹ := by positivity
        calc K * (((D : ℝ) * N)⁻¹ * z.im⁻¹) ≤ K ^ 2 * (((D : ℝ) * N)⁻¹ * z.im⁻¹) :=
              mul_le_mul_of_nonneg_right (by nlinarith) hX
          _ ≤ K ^ 2 * (((D : ℝ) * N)⁻¹ * (z.im⁻¹ + z.im⁻¹ ^ 2)) :=
              mul_le_mul_of_nonneg_left (by rw [mul_add]; linarith) (sq_nonneg K)
    · have e : (LF_l2 Λ B T z₁ z₂ x t).length = 2 := by omega
      rw [e] at hv hd
      refine ⟨hv.trans ?_, fun a b hab hkm => (hd a b hab).trans ?_⟩
      · simp only [LF_Gs, Nat.add_one_sub_one, pow_one]
        nlinarith [mul_nonneg (mul_nonneg hK0 hK0) hΓ0]
      · refine (hpow 2 a b le_rfl hab hkm).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΓt0 _)
        have : 0 ≤ ((D : ℝ) * N)⁻¹ * z.im⁻¹ := by positivity
        nlinarith [sq_nonneg K]
  -- the sum over the terms
  have hZ : (fun w' => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w')) = fun w' => ∑ t : Fin 6,
      ∑ x : Fin D, LF_cf D θ t * (ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t)) *
        ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t))) := by
    funext w'
    unfold LF_Z
    simp only [mul_assoc]
  have hsm1 := fun x t => hsm _ (LF_l1_ok hs.herm T hz₁ hz₂ x t)
  have hsm2 := fun x t => hsm _ (LF_l2_ok hs.herm B T hz₁ hz₂ x t)
  have hsmP : ∀ x t, LF_Sm (fun w' => ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t)) *
      ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t))) := fun x t =>
    LF_sm_mul (hsm1 x t) (hsm2 x t)
  rw [hZ, LF_wirt_sum _ _ (fun t => fun n => ContDiff.sum fun x _ =>
      (LF_sm_cmul _ (hsmP x t)) n) a b]
  simp only
  have hterm : ∀ t x, ‖wirt a b (fun w' => LF_cf D θ t *
      (ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t)) *
        ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t)))) w‖ ≤
      ‖LF_cf D θ t‖ * ((2 * Γt) ^ (a + b) * (K * Γ₀ * (K ^ 2 * (((D : ℝ) * N)⁻¹ *
        (z.im⁻¹ + z.im⁻¹ ^ 2))) + K * (((D : ℝ) * N)⁻¹ * z.im⁻¹) * (K ^ 2 * Γ₀ * (1 + z.im⁻¹)) +
        K * (((D : ℝ) * N)⁻¹ * z.im⁻¹) * (K ^ 2 * (((D : ℝ) * N)⁻¹ *
          (z.im⁻¹ + z.im⁻¹ ^ 2))))) := by
    intro t x
    rw [LF_wirt_cmul (hsmP x t), norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact LF_LB2 (hsm1 x t) (hsm2 x t) w Γt _ _ _ _ Km hΓt0 (hL1 x t).1 (hL2 x t).1
      (by positivity) (by positivity) (hL1 x t).2 (hL2 x t).2 a b hab hk
  have hwsum : ∀ t, LF_Sm (fun w' => ∑ x : Fin D, LF_cf D θ t *
      (ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t)) *
        ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t)))) := fun t n =>
    ContDiff.sum fun x _ => (LF_sm_cmul _ (hsmP x t)) n
  calc ‖∑ t : Fin 6, wirt a b (fun w' => ∑ x : Fin D, LF_cf D θ t *
        (ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t)) *
          ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t)))) w‖
      ≤ ∑ t : Fin 6, ∑ x : Fin D, ‖wirt a b (fun w' => LF_cf D θ t *
        (ntr (chainB (setEntry h i j w') (LF_l1 Λ T z₁ z₂ x t)) *
          ntr (chainB (setEntry h i j w') (LF_l2 Λ B T z₁ z₂ x t)))) w‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
        rw [LF_wirt_sum _ _ (fun x => LF_sm_cmul _ (hsmP x t)) a b]
        exact norm_sum_le _ _
    _ ≤ ∑ t : Fin 6, ∑ x : Fin D, ‖LF_cf D θ t‖ * ((2 * Γt) ^ (a + b) * (K * Γ₀ * (K ^ 2 *
        (((D : ℝ) * N)⁻¹ * (z.im⁻¹ + z.im⁻¹ ^ 2))) + K * (((D : ℝ) * N)⁻¹ * z.im⁻¹) *
        (K ^ 2 * Γ₀ * (1 + z.im⁻¹)) + K * (((D : ℝ) * N)⁻¹ * z.im⁻¹) * (K ^ 2 *
        (((D : ℝ) * N)⁻¹ * (z.im⁻¹ + z.im⁻¹ ^ 2))))) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun x _ => hterm t x
    _ = (2 * Γt) ^ (a + b) * LF_Pz D N θ K Γ₀ z.im := by
        simp only [LF_Pz, LF_Cz, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ => ?_
        ring

private lemma LF_Pz_nonneg {D N : ℕ} (θ : ℝ) {K Γ₀ η : ℝ} (hK : 0 ≤ K) (hΓ₀ : 0 ≤ Γ₀)
    (hη : 0 < η) : 0 ≤ LF_Pz D N θ K Γ₀ η := by
  have := LF_Cz_nonneg D θ
  have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  unfold LF_Pz
  positivity

/-- The jet of the integrand `X_{βα} Z^{p-1} Z̄^p` along a slice at a point of the good event:
`|∂^{(a,b)}| ≤ (4 p Γ_t)^{a+b} Γ₂ (|Z| + Ψ_Z)^{2p-1}` for `a + b ≤ K_m`. -/
private lemma LF_jet_F {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h i j w)) (Km p : ℕ) (hp : 1 ≤ p)
    (β α : Idx D N) :
    ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => LF_F θ Λ B T z₁ z₂ p β α (setEntry h i j w')) w‖ ≤
        (4 * p * LF_Gt Km K Γ₀) ^ (a + b) * LF_Gs K Γ₀ z.im 2 *
          (‖LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1) := by
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Γt := LF_Gt Km K Γ₀ with hΓt
  have hΓt0 : 0 ≤ Γt := by simp only [hΓt, LF_Gt]; positivity
  set Pz := LF_Pz D N θ K Γ₀ z.im with hPz
  have hPz0 : 0 ≤ Pz := LF_Pz_nonneg θ hK0 hΓ0 hs.hz
  set u : ℂ → ℂ := fun w' => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w') with hu
  set X : ℂ → ℂ := fun w' => LF_X Λ B T z₁ z₂ (setEntry h i j w') β α with hX
  have hsu : LF_Sm u := LF_sm_slice (F := fun h' => LF_Z θ Λ B T z₁ z₂ h')
    (fun n => LF_cd_Z θ hs.herm B T hz₁ hz₂ n) h hh i j
  have hsX : LF_Sm X := LF_sm_slice (F := fun h' => LF_X Λ B T z₁ z₂ h' β α)
    (fun n => LF_cd_X hs.herm B T hz₁ hz₂ β α n) h hh i j
  set c := ‖u w‖ + Pz with hc
  have hc0 : 0 ≤ c := by positivity
  have hGs2 : 0 ≤ LF_Gs K Γ₀ z.im 2 := by
    unfold LF_Gs
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
    · refine (LF_jet_Z θ hs hΓ₀ h hh i j w hg Km a b h0 hab).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (u w)]) (by positivity)
  have hUc : ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => starRingEnd ℂ (u w')) w‖ ≤ (2 * Γt) ^ (a + b) * c := by
    intro a b hab
    rw [LF_wirt_conj hsu, Complex.norm_conj, add_comm a b]
    exact hU b a (by omega)
  have hP1 := LF_pow_jet hsu w (2 * Γt) c Km (by positivity) hc0 hU (p - 1)
  have hP2 := LF_pow_jet (LF_sm_conj hsu) w (2 * Γt) c Km (by positivity) hc0 hUc p
  have hΦ := LF_LB (LF_sm_pow hsu (p - 1)) (LF_sm_pow (LF_sm_conj hsu) p) w (2 * Γt)
    ((p - 1 : ℕ) : ℝ) (p : ℝ) (c ^ (p - 1)) (c ^ p) Km (by positivity) (Nat.cast_nonneg _)
    (pow_nonneg hc0 _) hP1 hP2
  have hXj : ∀ a b, a + b ≤ Km → ‖wirt a b X w‖ ≤
      (2 * Γt) ^ (a + b) * 1 ^ (a + b) * LF_Gs K Γ₀ z.im 2 := by
    intro a b hab
    refine (LF_jet_X hs hΓ0 h hh i j w hg β α a b).trans ?_
    rw [one_pow, mul_one, ← mul_pow]
    have hG1 : 0 ≤ LF_Gs K Γ₀ z.im 1 := by
      unfold LF_Gs
      have := inv_nonneg.mpr hs.hz.le
      positivity
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) hGs2
    simp only [hΓt, LF_Gt, LF_Gs, pow_one, Nat.sub_self, pow_zero, mul_one]
    have : ((2 + a + b : ℕ) : ℝ) ≤ 2 + Km := by exact_mod_cast (by omega : 2 + a + b ≤ 2 + Km)
    have h1 : 0 ≤ K * Γ₀ := by positivity
    have h2 : (0 : ℝ) ≤ Km := Nat.cast_nonneg _
    nlinarith
  have hF := LF_LB hsX (LF_sm_mul (LF_sm_pow hsu (p - 1)) (LF_sm_pow (LF_sm_conj hsu) p)) w
    (2 * Γt) 1 (((p - 1 : ℕ) : ℝ) + p) (LF_Gs K Γ₀ z.im 2) (c ^ (p - 1) * c ^ p) Km
    (by positivity) zero_le_one hGs2 hXj hΦ
  intro a b hab
  have e : (fun w' => LF_F θ Λ B T z₁ z₂ p β α (setEntry h i j w')) =
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
constant `T`, with `E = E_{ij}` for `∂_w` and `E = E_{ji}` for `∂_{w̄}`. -/
private lemma LF_dm_X {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (s : ℂ)
    (hs : s = Complex.I ∨ s = -Complex.I) :
    LF_dm s (fun w => LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w * T) = fun w =>
      (-LF_cc i j) • (LF_g Λ z₂ h i j w * (LF_E s i j * (LF_g Λ z₂ h i j w * (B *
        (LF_g Λ z₁ h i j w * T))))) +
      (-LF_cc i j) • (LF_g Λ z₂ h i j w * (B * (LF_g Λ z₁ h i j w * (LF_E s i j *
        (LF_g Λ z₁ h i j w * T))))) := by
  have d1 := LF_Dm.g hΛ hz₁ hh i j
  have d2 := LF_Dm.g hΛ hz₂ hh i j
  have dB := LF_Dm.const (ι := Idx D N) B
  have dT := LF_Dm.const (ι := Idx D N) T
  rw [LF_dm_mul s ((d2.mul dB).mul d1) dT, LF_dm_mul s (d2.mul dB) d1, LF_dm_mul s d2 dB,
    LF_dm_const, LF_dm_const, LF_dm_g hΛ hz₁ hh i j s hs, LF_dm_g hΛ hz₂ hh i j s hs]
  funext w
  simp only [Matrix.mul_zero, add_zero, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_assoc]

/-- `∂(G₁ T) = -c G₁ E G₁ T` along a Hermitian slice. -/
private lemma LF_dm_GT {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (T : Matrix (Idx D N) (Idx D N) ℂ) {ξ : ℂ} (hξ : ξ.im ≠ 0)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (s : ℂ)
    (hs : s = Complex.I ∨ s = -Complex.I) :
    LF_dm s (fun w => LF_g Λ ξ h i j w * T) = fun w =>
      (-LF_cc i j) • (LF_g Λ ξ h i j w * (LF_E s i j * (LF_g Λ ξ h i j w * T))) := by
  rw [LF_dm_mul s (LF_Dm.g hΛ hξ hh i j) (LF_Dm.const T), LF_dm_const, LF_dm_g hΛ hξ hh i j s hs]
  funext w
  simp only [Matrix.mul_zero, add_zero, Matrix.smul_mul, Matrix.mul_assoc]

/-- The second entrywise derivatives of `G₂ B G₁ T`:
`∂'∂(G₂BG₁T) = c² Σ (P E' Q E R + P E Q E' R)` over the triples
`(G₂, G₂, G₂BG₁T)`, `(G₂, G₂BG₁, G₁T)`, `(G₂BG₁, G₁, G₁T)`. -/
private lemma LF_dm2_X {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    {h : Idx D N → Idx D N → ℂ} (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (s s' : ℂ)
    (hs : s = Complex.I ∨ s = -Complex.I) (hs' : s' = Complex.I ∨ s' = -Complex.I) (w : ℂ) :
    LF_dm s' (LF_dm s (fun w => LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w * T)) w =
      (LF_cc i j ^ 2) • (
        LF_g Λ z₂ h i j w * (LF_E s' i j * (LF_g Λ z₂ h i j w * (LF_E s i j *
          (LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w * T)))) +
        LF_g Λ z₂ h i j w * (LF_E s i j * (LF_g Λ z₂ h i j w * (LF_E s' i j *
          (LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w * T)))) +
        LF_g Λ z₂ h i j w * (LF_E s' i j * ((LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w) *
          (LF_E s i j * (LF_g Λ z₁ h i j w * T)))) +
        LF_g Λ z₂ h i j w * (LF_E s i j * ((LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w) *
          (LF_E s' i j * (LF_g Λ z₁ h i j w * T)))) +
        (LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w) * (LF_E s' i j * (LF_g Λ z₁ h i j w *
          (LF_E s i j * (LF_g Λ z₁ h i j w * T)))) +
        (LF_g Λ z₂ h i j w * B * LF_g Λ z₁ h i j w) * (LF_E s i j * (LF_g Λ z₁ h i j w *
          (LF_E s' i j * (LF_g Λ z₁ h i j w * T))))) := by
  have d1 := LF_Dm.g hΛ hz₁ hh i j
  have d2 := LF_Dm.g hΛ hz₂ hh i j
  have dc : ∀ C : Matrix (Idx D N) (Idx D N) ℂ, LF_Dm (fun _ : ℂ => C) := LF_Dm.const
  set G₁ := LF_g Λ z₁ h i j with hG₁
  set G₂ := LF_g Λ z₂ h i j with hG₂
  set E := LF_E s i j with hE
  set E' := LF_E s' i j with hE'
  set c := LF_cc i j with hc
  have hX : LF_dm s (fun w => G₂ w * B * G₁ w * T) = fun w =>
      (-c) • (G₂ w * E * (G₂ w * B * G₁ w * T)) + (-c) • ((G₂ w * B * G₁ w) * E * (G₁ w * T)) := by
    rw [LF_dm_X hΛ B T hz₁ hz₂ hh i j s hs]
    funext w
    simp only [hG₁, hG₂, hE, hc, Matrix.mul_assoc]
  have hX' := LF_dm_X hΛ B T hz₁ hz₂ hh i j s' hs'
  have hP := LF_dm_X hΛ B 1 hz₁ hz₂ hh i j s' hs'
  simp only [Matrix.mul_one] at hP
  have hQ := LF_dm_GT hΛ T hz₁ hh i j s' hs'
  have hg2 := LF_dm_g hΛ hz₂ hh i j s' hs'
  rw [hX]
  have dX : LF_Dm (fun w => G₂ w * B * G₁ w * T) := ((d2.mul (dc B)).mul d1).mul (dc T)
  have dP : LF_Dm (fun w => G₂ w * B * G₁ w) := (d2.mul (dc B)).mul d1
  have dQ : LF_Dm (fun w => G₁ w * T) := d1.mul (dc T)
  rw [LF_dm_add s' (((d2.mul (dc E)).mul dX).smul _) (((dP.mul (dc E)).mul dQ).smul _),
    LF_dm_smul s' _ ((d2.mul (dc E)).mul dX), LF_dm_smul s' _ ((dP.mul (dc E)).mul dQ),
    LF_dm_mul s' (d2.mul (dc E)) dX, LF_dm_mul s' (dP.mul (dc E)) dQ,
    LF_dm_mul s' d2 (dc E), LF_dm_mul s' dP (dc E), LF_dm_const, hg2, hX', hQ]
  rw [show (fun w => G₂ w * B * G₁ w) = fun w => G₂ w * B * G₁ w from rfl, hP]
  simp only [Matrix.mul_zero, add_zero, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, smul_add, smul_smul, Matrix.mul_assoc]
  rw [show (LF_cc i j) ^ 2 = -c * -c by rw [hc]; ring]
  abel

/-- `(P (E_{ij} Y))_{kl} = P_{ki} Y_{jl}`. -/
private lemma LF_single_entry' {ι : Type*} [Fintype ι] [DecidableEq ι] (P Y : Matrix ι ι ℂ)
    (i j k l : ι) : (P * (Matrix.single i j (1 : ℂ) * Y)) k l = P k i * Y j l := by
  rw [← Matrix.mul_assoc, LF_single_entry]

/-- The off-diagonal structure of `(P E₁ Q E₂ R)_{βα}` for `E₁, E₂ ∈ {E_{βα}, E_{αβ}}`: one of the
three factors is an off-diagonal entry `P_{βα}`, `Q_{αβ}` or `R_{βα}`. -/
private lemma LF_entry3 {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q R : Matrix ι ι ℂ)
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
    rw [LF_single_entry', LF_single_entry', norm_mul, norm_mul]
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
private lemma LF_wirt2_dm (a b : ℕ) (hab : a + b = 2) : ∃ s s' : ℂ,
    (s = Complex.I ∨ s = -Complex.I) ∧ (s' = Complex.I ∨ s' = -Complex.I) ∧
      ∀ {ι : Type} (M : ℂ → Matrix ι ι ℂ) (k l : ι),
        wirt a b (fun w => M w k l) = fun w => LF_dm s' (LF_dm s M) w k l := by
  have e1 : ∀ {ι : Type} (M' : ℂ → Matrix ι ι ℂ) (k l : ι),
      dW (fun w => M' w k l) = fun w => LF_dm (-Complex.I) M' w k l := by
    intro ι M' k l; funext w; rw [LF_dm_dW]
  have e2 : ∀ {ι : Type} (M' : ℂ → Matrix ι ι ℂ) (k l : ι),
      dWbar (fun w => M' w k l) = fun w => LF_dm Complex.I M' w k l := by
    intro ι M' k l; funext w; rw [LF_dm_dWbar]
  rcases (show (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨-Complex.I, -Complex.I, Or.inr rfl, Or.inr rfl, fun M k l => ?_⟩
    simp only [wirt, Function.iterate_zero, id, Function.iterate_succ, Function.comp]
    rw [e1 M, e1 (LF_dm (-Complex.I) M)]
  · refine ⟨Complex.I, -Complex.I, Or.inl rfl, Or.inr rfl, fun M k l => ?_⟩
    simp only [wirt, Function.iterate_one]
    rw [e2 M, e1 (LF_dm Complex.I M)]
  · refine ⟨Complex.I, Complex.I, Or.inl rfl, Or.inl rfl, fun M k l => ?_⟩
    simp only [wirt, Function.iterate_zero, id, Function.iterate_succ, Function.comp]
    rw [e2 M, e2 (LF_dm Complex.I M)]

/-- `e_x^* M e_y = M_{xy}`. -/
private lemma LF_form_ee {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ) (x y : Idx D N) :
    star (Pi.single x (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single y 1) = M x y := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- `Σ_{k,l} |M_{kl}| ≤ card · F^{1/2}` when `|M|_{HS}² ≤ F`. -/
private lemma LF_sum_off {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (F : ℝ) (hF : LF_fs M ≤ F) :
    ∑ k, ∑ l, ‖M k l‖ ≤ (Fintype.card ι : ℝ) * Real.sqrt F := by
  have h1 := LF_sum_abs_sq M
  have h0 : 0 ≤ ∑ k, ∑ l, ‖M k l‖ := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hF0 : 0 ≤ F := (LF_fs_nonneg M).trans hF
  rw [← Real.sqrt_sq h0, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_left hF (sq_nonneg _)))

/-- The bounds on the good event used for the sums over the entries `(β, α)`: entries of
`G₁, G₂, G₂BG₁, G₂BG₁T, G₁T` and their Hilbert–Schmidt norms. -/
private lemma LF_good_mats {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) :
    (∀ x y, ‖res (Matrix.of h + Λ) z₁ x y‖ ≤ K * Γ₀) ∧
    (∀ x y, ‖res (Matrix.of h + Λ) z₂ x y‖ ≤ K * Γ₀) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁) x y‖ ≤
      K ^ 2 * Γ₀ * z.im⁻¹) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ * T) x y‖ ≤
      K ^ 2 * Γ₀ * z.im⁻¹) ∧
    (∀ x y, ‖(res (Matrix.of h + Λ) z₁ * T) x y‖ ≤ K * Γ₀) ∧
    LF_fs (res (Matrix.of h + Λ) z₁) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ ∧
    LF_fs (res (Matrix.of h + Λ) z₂) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ ∧
    LF_fs (res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁) ≤
      (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹) ^ 2 ∧
    LF_fs (res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ * T) ≤
      (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2 ∧
    LF_fs (res (Matrix.of h + Λ) z₁ * T) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ * K ^ 2 := by
  have hX := hh.add hs.herm
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hXX : ∀ k : Idx D N, (Pi.single k 1 : Idx D N → ℂ) ∈ LF_XX T := fun k => Or.inl ⟨k, rfl⟩
  have hXT : ∀ k : Idx D N, T *ᵥ Pi.single k 1 ∈ LF_XX T := fun k => Or.inr ⟨k, rfl⟩
  have m1 : (1 : Matrix (Idx D N) (Idx D N) ℂ) ∈ ({1, B} : Set (Matrix (Idx D N) (Idx D N) ℂ)) :=
    Or.inl rfl
  have hent := fun l hl1 hl3 hl => LF_entry_sharp hs.herm hs.hz hΓ0 hh hg K hs.hK {1, B}
    (LF_XX T) (LF_XX_U Λ B T z₂) (LF_QX_ok Λ B T z₂) l hl1 hl3 hl
  have hl1 : ∀ ζ, LF_pm z ζ → ∀ f ∈ [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, ζ)],
      f.1 ∈ ({1, B} : Set (Matrix (Idx D N) (Idx D N) ℂ)) ∧ opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧
        LF_pm z f.2.2 := by
    intro ζ hζ f hf
    rw [List.mem_singleton] at hf
    subst hf
    exact ⟨m1, LF_opNorm_one.trans hs.hK, rfl, hζ⟩
  have e1 : ∀ ζ, chainB h [((1 : Matrix (Idx D N) (Idx D N) ℂ), Λ, ζ)] =
      res (Matrix.of h + Λ) ζ := fun ζ => by rw [LF_chain1, Matrix.one_mul]
  have eX : chainB h (LF_lX Λ B z₁ z₂) =
      res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ := by
    rw [LF_lX, LF_chain2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
  have hGres : ∀ ζ, LF_pm z ζ → opNorm (res (Matrix.of h + Λ) ζ) ≤ z.im⁻¹ := fun ζ hζ => by
    have := LF_opNorm_res _ hX ζ (LF_pm_ne hη hζ)
    rwa [LF_pm_im hη hζ] at this
  have hfs : ∀ ζ, LF_pm z ζ → LF_fs (res (Matrix.of h + Λ) ζ) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ := by
    intro ζ hζ
    refine (LF_fs_res _ hX ζ (LF_pm_ne hη hζ)).trans ?_
    rw [LF_pm_im hη hζ]
    have hd : ∀ l, ‖res (Matrix.of h + Λ) ζ l l‖ / z.im ≤ Γ₀ * z.im⁻¹ := by
      intro l
      have := hg ζ hζ _ (LF_e_U Λ B T z₂ l) _ (LF_e_U Λ B T z₂ l)
      rw [LF_form_ee] at this
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right this hi
    refine (Finset.sum_le_sum fun l _ => hd l).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_,
    hfs z₁ hs.h1, hfs z₂ hs.h2, ?_, ?_, ?_⟩
  · have := hent _ (by simp) (by simp) (hl1 z₁ hs.h1) _ (hXX x) _ (hXX y)
    rw [e1, LF_form_ee] at this
    simpa using this
  · have := hent _ (by simp) (by simp) (hl1 z₂ hs.h2) _ (hXX x) _ (hXX y)
    rw [e1, LF_form_ee] at this
    simpa using this
  · have := hent _ (by simp [LF_lX]) (by simp [LF_lX]) hs.fX _ (hXX x) _ (hXX y)
    rw [eX, LF_form_ee] at this
    simpa [LF_lX] using this
  · have := hent _ (by simp [LF_lX]) (by simp [LF_lX]) hs.fX _ (hXX x) _ (hXT y)
    rw [eX, LF_form_single] at this
    simpa [LF_lX] using this
  · have := hent _ (by simp) (by simp) (hl1 z₁ hs.h1) _ (hXX x) _ (hXT y)
    rw [e1, LF_form_single] at this
    simpa using this
  · have h1 : opNorm (B * res (Matrix.of h + Λ) z₁) ≤ K * z.im⁻¹ :=
      (opNorm_mul_le _ _).trans (mul_le_mul hs.hB (hGres z₁ hs.h1) (norm_nonneg _) hK0)
    rw [Matrix.mul_assoc]
    refine (LF_fs_mul_right _ _).trans ?_
    exact mul_le_mul (hfs z₂ hs.h2) (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _)
      (by positivity)
  · have h1 : opNorm (B * res (Matrix.of h + Λ) z₁ * T) ≤ K * z.im⁻¹ * K :=
      (opNorm_mul_le _ _).trans (mul_le_mul ((opNorm_mul_le _ _).trans
        (mul_le_mul hs.hB (hGres z₁ hs.h1) (norm_nonneg _) hK0)) hs.hT (norm_nonneg _)
          (by positivity))
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B]
    refine (LF_fs_mul_right _ _).trans ?_
    exact mul_le_mul (hfs z₂ hs.h2) (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _)
      (by positivity)
  · refine (LF_fs_mul_right _ _).trans ?_
    exact mul_le_mul (hfs z₁ hs.h1) (pow_le_pow_left₀ (norm_nonneg _) hs.hT 2) (sq_nonneg _)
      (by positivity)

/-- The sum over `(β, α)` of `|(P E₁ Q E₂ R)_{βα}|`, `E_r ∈ {E_{βα}, E_{αβ}}`:
`≤ DN (m_Q m_R F_P^{1/2} + m_P m_R F_Q^{1/2} + m_P m_Q F_R^{1/2})`. -/
private lemma LF_triple_sum {D N : ℕ} (P Q R : Matrix (Idx D N) (Idx D N) ℂ)
    (E₁ E₂ : Idx D N → Idx D N → Matrix (Idx D N) (Idx D N) ℂ)
    (h₁ : ∀ β α, E₁ β α = Matrix.single β α 1 ∨ E₁ β α = Matrix.single α β 1)
    (h₂ : ∀ β α, E₂ β α = Matrix.single β α 1 ∨ E₂ β α = Matrix.single α β 1)
    (mP mQ mR FP FQ FR : ℝ) (hP : ∀ x y, ‖P x y‖ ≤ mP) (hQ : ∀ x y, ‖Q x y‖ ≤ mQ)
    (hR : ∀ x y, ‖R x y‖ ≤ mR) (hFP : LF_fs P ≤ FP) (hFQ : LF_fs Q ≤ FQ)
    (hFR : LF_fs R ≤ FR) :
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
    LF_entry3 P Q R α β _ _ (h₁ β α) (h₂ β α) mP mQ mR (fun x _ y _ => hP x y)
      (fun x _ y _ => hQ x y) (fun x _ y _ => hR x y)
  refine (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => key β α).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have sP := LF_sum_off P FP hFP
  have sQ := LF_sum_off Q FQ hFQ
  have sR := LF_sum_off R FR hFR
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

set_option maxHeartbeats 1000000 in
/-- The sum over `(β, α)` of the second derivatives of `X_{βα}` along its own slice on the good
event: `≤ 18 DN K⁴ Γ₀² η⁻¹ (DN Γ₀ η⁻¹)^{1/2}`. -/
private lemma LF_sum_d2X {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) (a b : ℕ)
    (hab : a + b = 2) :
    ∑ β, ∑ α, ‖wirt a b (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ ≤
      18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * z.im⁻¹ *
        Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) := by
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK := hs.hK
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  obtain ⟨mG1, mG2, mP, mX, mQ, fG1, fG2, fP, fX, fQ⟩ := LF_good_mats hs hΓ₀ h hh hg
  set G₁ := res (Matrix.of h + Λ) z₁ with hG₁
  set G₂ := res (Matrix.of h + Λ) z₂ with hG₂
  set F1 := (D * N : ℝ) * Γ₀ * z.im⁻¹ with hF1
  have hF10 : 0 ≤ F1 := by positivity
  obtain ⟨s, s', hs1, hs2, hw⟩ := LF_wirt2_dm a b hab
  have hE : ∀ (s : ℂ), (s = Complex.I ∨ s = -Complex.I) → ∀ β α : Idx D N,
      LF_E s β α = Matrix.single β α 1 ∨ LF_E s β α = Matrix.single α β 1 := by
    intro s _ β α
    unfold LF_E
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hc : ∀ β α : Idx D N, ‖LF_cc β α ^ 2‖ ≤ 1 := by
    intro β α
    unfold LF_cc
    split_ifs <;> norm_num
  set E := fun β α : Idx D N => LF_E s β α with hEdef
  set E' := fun β α : Idx D N => LF_E s' β α with hE'def
  have hpt : ∀ β α, ‖wirt a b (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ ≤
      ‖(G₂ * (E' β α * (G₂ * (E β α * (G₂ * B * G₁ * T))))) β α‖ +
      ‖(G₂ * (E β α * (G₂ * (E' β α * (G₂ * B * G₁ * T))))) β α‖ +
      ‖(G₂ * (E' β α * ((G₂ * B * G₁) * (E β α * (G₁ * T))))) β α‖ +
      ‖(G₂ * (E β α * ((G₂ * B * G₁) * (E' β α * (G₁ * T))))) β α‖ +
      ‖((G₂ * B * G₁) * (E' β α * (G₁ * (E β α * (G₁ * T))))) β α‖ +
      ‖((G₂ * B * G₁) * (E β α * (G₁ * (E' β α * (G₁ * T))))) β α‖ := by
    intro β α
    have e : (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) =
        fun w => (LF_g Λ z₂ h β α w * B * LF_g Λ z₁ h β α w * T) β α := by
      funext w; rw [LF_X_eq]; rfl
    rw [e, hw]
    simp only
    rw [LF_dm2_X hs.herm B T hz₁ hz₂ hh β α s s' hs1 hs2]
    have hself : ∀ ξ, LF_g Λ ξ h β α (h β α) = res (Matrix.of h + Λ) ξ := by
      intro ξ; simp only [LF_g, LF_setEntry_self h hh]
    simp only [hself, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc β α)).trans ?_
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have hEs := hE s hs1
  have hE's := hE s' hs2
  have tA1 := LF_triple_sum G₂ G₂ (G₂ * B * G₁ * T) E' E hE's hEs (K * Γ₀) (K * Γ₀)
    (K ^ 2 * Γ₀ * z.im⁻¹) F1 F1 (F1 * (K * z.im⁻¹ * K) ^ 2) mG2 mG2 mX fG2 fG2 fX
  have tA2 := LF_triple_sum G₂ G₂ (G₂ * B * G₁ * T) E E' hEs hE's (K * Γ₀) (K * Γ₀)
    (K ^ 2 * Γ₀ * z.im⁻¹) F1 F1 (F1 * (K * z.im⁻¹ * K) ^ 2) mG2 mG2 mX fG2 fG2 fX
  have tB1 := LF_triple_sum G₂ (G₂ * B * G₁) (G₁ * T) E' E hE's hEs (K * Γ₀)
    (K ^ 2 * Γ₀ * z.im⁻¹) (K * Γ₀) F1 (F1 * (K * z.im⁻¹) ^ 2) (F1 * K ^ 2) mG2 mP mQ fG2 fP fQ
  have tB2 := LF_triple_sum G₂ (G₂ * B * G₁) (G₁ * T) E E' hEs hE's (K * Γ₀)
    (K ^ 2 * Γ₀ * z.im⁻¹) (K * Γ₀) F1 (F1 * (K * z.im⁻¹) ^ 2) (F1 * K ^ 2) mG2 mP mQ fG2 fP fQ
  have tC1 := LF_triple_sum (G₂ * B * G₁) G₁ (G₁ * T) E' E hE's hEs (K ^ 2 * Γ₀ * z.im⁻¹)
    (K * Γ₀) (K * Γ₀) (F1 * (K * z.im⁻¹) ^ 2) F1 (F1 * K ^ 2) mP mG1 mQ fP fG1 fQ
  have tC2 := LF_triple_sum (G₂ * B * G₁) G₁ (G₁ * T) E E' hEs hE's (K ^ 2 * Γ₀ * z.im⁻¹)
    (K * Γ₀) (K * Γ₀) (F1 * (K * z.im⁻¹) ^ 2) F1 (F1 * K ^ 2) mP mG1 mQ fP fG1 fQ
  refine (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => hpt β α).trans ?_
  simp only [Finset.sum_add_distrib]
  have sq1 : Real.sqrt (F1 * (K * z.im⁻¹ * K) ^ 2) = Real.sqrt F1 * (K * z.im⁻¹ * K) := by
    rw [Real.sqrt_mul hF10, Real.sqrt_sq (by positivity)]
  have sq2 : Real.sqrt (F1 * (K * z.im⁻¹) ^ 2) = Real.sqrt F1 * (K * z.im⁻¹) := by
    rw [Real.sqrt_mul hF10, Real.sqrt_sq (by positivity)]
  have sq3 : Real.sqrt (F1 * K ^ 2) = Real.sqrt F1 * K := by
    rw [Real.sqrt_mul hF10, Real.sqrt_sq hK0]
  rw [sq1] at tA1 tA2
  rw [sq2, sq3] at tB1 tB2 tC1 tC2
  have hS0 : 0 ≤ Real.sqrt F1 := Real.sqrt_nonneg _
  have hDN : (0 : ℝ) ≤ D * N := by positivity
  have hK3 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hK2 : K ^ 2 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hu : 0 ≤ Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1 * (D * N : ℝ) := by positivity
  have key : ∀ k : ℕ, k ≤ 4 → K ^ k ≤ K ^ 4 := fun k hk => pow_le_pow_right₀ hK hk
  calc _ ≤ (D * N : ℝ) * (K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * Real.sqrt F1 +
          K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * Real.sqrt F1 +
          K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹ * K))) +
        (D * N : ℝ) * (K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * Real.sqrt F1 +
          K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * Real.sqrt F1 +
          K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹ * K))) +
        (D * N : ℝ) * (K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * Real.sqrt F1 +
          K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹)) +
          K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * (Real.sqrt F1 * K)) +
        (D * N : ℝ) * (K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * Real.sqrt F1 +
          K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹)) +
          K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * (Real.sqrt F1 * K)) +
        (D * N : ℝ) * (K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹)) +
          K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * Real.sqrt F1 +
          K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * (Real.sqrt F1 * K)) +
        (D * N : ℝ) * (K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹)) +
          K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * Real.sqrt F1 +
          K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * (Real.sqrt F1 * K)) := by
        linarith [tA1, tA2, tB1, tB2, tC1, tC2]
    _ ≤ 18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1)) := by
        have e1 : K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * Real.sqrt F1 =
            K ^ 3 * (Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1) := by ring
        have e2 : K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹ * K)) =
            K ^ 4 * (Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1) := by ring
        have e3 : K * Γ₀ * (K * Γ₀) * (Real.sqrt F1 * (K * z.im⁻¹)) =
            K ^ 3 * (Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1) := by ring
        have e4 : K * Γ₀ * (K ^ 2 * Γ₀ * z.im⁻¹) * (Real.sqrt F1 * K) =
            K ^ 4 * (Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1) := by ring
        have e5 : K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * Real.sqrt F1 =
            K ^ 3 * (Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1) := by ring
        have e6 : K ^ 2 * Γ₀ * z.im⁻¹ * (K * Γ₀) * (Real.sqrt F1 * K) =
            K ^ 4 * (Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1) := by ring
        rw [e1, e2, e3, e4, e5, e6]
        have hv : 0 ≤ Γ₀ ^ 2 * z.im⁻¹ * Real.sqrt F1 := by positivity
        have h3 := mul_le_mul_of_nonneg_right hK3 hv
        nlinarith [mul_le_mul_of_nonneg_left h3 hDN]

/-! ### The cancellation at first order -/

/-- The entries of the profile `S_θ` as complex numbers. -/
private lemma LF_varProf_eq (D N : ℕ) (θ : ℝ) (r m : Idx D N) :
    (varProf D N θ r m : ℂ) = (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = m.1 then 1 else 0) +
      ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ := by
  unfold varProf
  push_cast
  split_ifs <;> simp

/-- The normalized trace as a sum over the diagonal. -/
private lemma LF_ntr_eq (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr M = ((D : ℂ) * N)⁻¹ * ∑ r, M r r := by
  simp [ntr, Matrix.trace, Fintype.card_prod]

/-- `S_θ(R)` is the diagonal matrix with entries `Σ_r (S_θ)_{rp} R_{rr}`. -/
private lemma LF_sTheta_apply (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ)
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
    rw [LF_ntr_eq]
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
    rw [e1, hblk, LF_ntr_eq]
    simp only [LF_varProf_eq, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∀ r : Idx D N, (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = p.1 then (1 : ℂ) else 0) * R r r =
        (θ : ℂ) * ((N : ℂ)⁻¹ * if r.1 = p.1 then R r r else 0) := by
      intro r
      split_ifs <;> ring
    simp only [e2]
    push_cast
    simp only [mul_assoc]
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]



/-- `S_θ` has symmetric weights: `(S_θ)_{pq} = (S_θ)_{qp}`. -/
private lemma LF_varProf_symm (D N : ℕ) (θ : ℝ) (p q : Idx D N) :
    varProf D N θ p q = varProf D N θ q p := by
  unfold varProf
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

/-- `⟨S M⟩ = (DN)⁻¹ Σ_p S_{pp} M_{pp}` for a diagonal `S`. -/
private lemma LF_ntr_diag {D N : ℕ} (S M : Matrix (Idx D N) (Idx D N) ℂ)
    (hS : ∀ p q, p ≠ q → S p q = 0) :
    ntr (S * M) = ((D : ℂ) * N)⁻¹ * ∑ p, S p p * M p p := by
  rw [LF_ntr_eq]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single p (fun q _ hq => by rw [hS p q (Ne.symm hq),
    zero_mul]) (by simp)]

/-- The cancellation of the counterterms at first order (the second cumulants): on a Hermitian
array, `Σ_{β,α} ((S_θ)_{βα} ∂_w X_{βα} + δ_{βα} (S_θ)_{βα} ∂_{w̄} X_{βα})` along the slice
`(β, α)` at `w = h_{βα}` equals `-DN (⟨G₁ T S_θ(G₂) G₂ B⟩ + ⟨G₁ S_θ(G₁ T) G₂ B⟩)`. -/
private lemma LF_cancel {D N : ℕ} (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) (B T : Matrix (Idx D N) (Idx D N) ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0)
    (hz₂ : z₂.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ∑ β, ∑ α, ((varProf D N θ β α : ℂ) *
        dW (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α) +
      (if β = α then (varProf D N θ β α : ℂ) else 0) *
        dWbar (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)) =
      -((D : ℂ) * N) * LF_C θ Λ B T z₁ z₂ h := by
  set G₁ := res (Matrix.of h + Λ) z₁ with hG₁
  set G₂ := res (Matrix.of h + Λ) z₂ with hG₂
  have hpt : ∀ β α, (varProf D N θ β α : ℂ) *
      dW (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α) +
      (if β = α then (varProf D N θ β α : ℂ) else 0) *
        dWbar (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α) =
      -((varProf D N θ β α : ℂ) * (G₂ β β * (G₂ * B * G₁ * T) α α +
        (G₂ * B * G₁) β β * (G₁ * T) α α)) := by
    intro β α
    have e : (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) =
        fun w => (LF_g Λ z₂ h β α w * B * LF_g Λ z₁ h β α w * T) β α := by
      funext w; rw [LF_X_eq]; rfl
    have hself : ∀ ξ, LF_g Λ ξ h β α (h β α) = res (Matrix.of h + Λ) ξ := by
      intro ξ; simp only [LF_g, LF_setEntry_self h hh]
    have d1 : dW (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α) =
        -LF_cc β α * (G₂ β β * (G₂ * B * G₁ * T) α α + (G₂ * B * G₁) β β * (G₁ * T) α α) := by
      rw [e, ← LF_dm_dW, LF_dm_X hΛ B T hz₁ hz₂ hh β α _ (Or.inr rfl)]
      have hne : -Complex.I ≠ Complex.I := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      simp only [hself, LF_E, hne, ite_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [LF_single_entry', show G₂ * (B * (G₁ * (Matrix.single β α 1 * (G₁ * T)))) =
        (G₂ * B * G₁) * (Matrix.single β α 1 * (G₁ * T)) by simp only [Matrix.mul_assoc],
        LF_single_entry']
      simp only [Matrix.mul_assoc]
      ring
    have d2 : dWbar (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α) =
        -LF_cc β α * (G₂ β α * (G₂ * B * G₁ * T) β α + (G₂ * B * G₁) β α * (G₁ * T) β α) := by
      rw [e, ← LF_dm_dWbar, LF_dm_X hΛ B T hz₁ hz₂ hh β α _ (Or.inl rfl)]
      simp only [hself, LF_E, ite_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [LF_single_entry', show G₂ * (B * (G₁ * (Matrix.single α β 1 * (G₁ * T)))) =
        (G₂ * B * G₁) * (Matrix.single α β 1 * (G₁ * T)) by simp only [Matrix.mul_assoc],
        LF_single_entry']
      simp only [Matrix.mul_assoc]
      ring
    rw [d1, d2]
    by_cases hβα : β = α
    · subst hβα
      simp only [LF_cc, ite_true]
      ring
    · simp only [LF_cc, hβα, ite_false]
      ring
  simp only [hpt]
  -- the two sums as normalized traces against `S_θ`
  have hS2 : ∑ β, ∑ α, (varProf D N θ β α : ℂ) * G₂ β β * (G₂ * B * G₁ * T) α α =
      ∑ α, sTheta D N θ G₂ α α * (G₂ * B * G₁ * T) α α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [LF_sTheta_apply, ↓reduceIte]
    rw [Finset.sum_mul]
  have hS1 : ∑ β, ∑ α, (varProf D N θ β α : ℂ) * (G₂ * B * G₁) β β * (G₁ * T) α α =
      ∑ β, sTheta D N θ (G₁ * T) β β * (G₂ * B * G₁) β β := by
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [LF_sTheta_apply, ↓reduceIte]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [LF_varProf_symm D N θ β α]
    ring
  have hdiag : ∀ R : Matrix (Idx D N) (Idx D N) ℂ, ∀ p q, p ≠ q → sTheta D N θ R p q = 0 := by
    intro R p q hpq
    simp only [LF_sTheta_apply, hpq, ↓reduceIte]
  have hC1 : ntr (G₁ * T * (sTheta D N θ G₂ * G₂) * B) =
      ((D : ℂ) * N)⁻¹ * ∑ α, sTheta D N θ G₂ α α * (G₂ * B * G₁ * T) α α := by
    rw [← LF_ntr_diag _ _ (hdiag G₂)]
    rw [show G₁ * T * (sTheta D N θ G₂ * G₂) * B = (G₁ * T) * (sTheta D N θ G₂ * (G₂ * B)) by
      simp only [Matrix.mul_assoc], LF_ntr_comm]
    simp only [Matrix.mul_assoc]
  have hC2 : ntr (G₁ * sTheta D N θ (G₁ * T) * G₂ * B) =
      ((D : ℂ) * N)⁻¹ * ∑ β, sTheta D N θ (G₁ * T) β β * (G₂ * B * G₁) β β := by
    rw [← LF_ntr_diag _ _ (hdiag (G₁ * T))]
    rw [show G₁ * sTheta D N θ (G₁ * T) * G₂ * B = G₁ * (sTheta D N θ (G₁ * T) * (G₂ * B)) by
      simp only [Matrix.mul_assoc], LF_ntr_comm]
    simp only [Matrix.mul_assoc]
  have hDN : ((D : ℂ) * N) ≠ 0 ∨ ((D : ℂ) * N) = 0 := ne_or_eq _ _
  unfold LF_C
  rw [← hG₁, ← hG₂, hC1, hC2, ← hS2, ← hS1]
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
private def LF_W {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (l : List (LF_T D N)) (r : Fin l.length) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of h + (l.get r).2.1) (l.get r).2.2 * chainB h (l.drop (r + 1)) *
    chainB h (l.take (r + 1))

/-- The first Wirtinger derivatives of a loop along a Hermitian slice at `w = h_{ij}`. -/
private lemma LF_loop_d1 {D N : ℕ} (l : List (LF_T D N))
    (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    dW (fun w => ntr (chainB (setEntry h i j w) l)) (h i j) =
        -LF_cc i j * (((D : ℂ) * N)⁻¹ * ∑ r : Fin l.length, LF_W h l r j i) ∧
      dWbar (fun w => ntr (chainB (setEntry h i j w) l)) (h i j) =
        -LF_cc i j * (((D : ℂ) * N)⁻¹ * ∑ r : Fin l.length, LF_W h l r i j) := by
  have hsm : ∀ k m, LF_Sm (fun w => chainB (setEntry h i j w) l k m) := fun k m =>
    LF_sm_slice (F := fun h' => chainB h' l k m) (fun n => LF_cd_chain l hl k m n) h hh i j
  have e : (fun w => ntr (chainB (setEntry h i j w) l)) =
      fun w => ((D : ℂ) * N)⁻¹ * ∑ k, chainB (setEntry h i j w) l k k := by
    funext w; rw [LF_ntr_eq]
  have hsum : LF_Sm (fun w => ∑ k, chainB (setEntry h i j w) l k k) := fun n =>
    ContDiff.sum fun k _ => hsm k k n
  have hw10 : ∀ f : ℂ → ℂ, wirt 1 0 f = dW f := fun f => rfl
  have hw01 : ∀ f : ℂ → ℂ, wirt 0 1 f = dWbar f := fun f => rfl
  have hD := LF_wirt_sum (Finset.univ : Finset (Idx D N))
    (fun k w => chainB (setEntry h i j w) l k k) (fun k => hsm k k)
  rw [e]
  constructor
  · rw [← hw10, LF_wirt_cmul hsum, hD 1 0]
    simp only [hw10]
    simp only [chainB_dW l hl h hh i j, LF_setEntry_self h hh]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [LF_W, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, LF_cc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [← hw01, LF_wirt_cmul hsum, hD 0 1]
    simp only [hw01]
    simp only [chainB_dWbar l hl h hh i j, LF_setEntry_self h hh]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [LF_W, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, LF_cc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- On the good event, `|G(ζ)|_{HS}² ≤ DN Γ₀ η⁻¹` for `ζ ∈ {z, z̄}`. -/
private lemma LF_fs_good {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) {ζ : ℂ}
    (hζ : LF_pm z ζ) : LF_fs (res (Matrix.of h + Λ) ζ) ≤ (D * N : ℝ) * Γ₀ * z.im⁻¹ := by
  have hX := hh.add hs.herm
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  refine (LF_fs_res _ hX ζ (LF_pm_ne hη hζ)).trans ?_
  rw [LF_pm_im hη hζ]
  have hd : ∀ l, ‖res (Matrix.of h + Λ) ζ l l‖ / z.im ≤ Γ₀ * z.im⁻¹ := by
    intro l
    have := hg ζ hζ _ (LF_e_U Λ B T z₂ l) _ (LF_e_U Λ B T z₂ l)
    rw [LF_form_ee] at this
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right this hi
  refine (Finset.sum_le_sum fun l _ => hd l).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `Σ_{i,j} |∂ ⟨C⟩|² ≤ (DN)⁻² q² (DN Γ₀ η⁻¹) (K η⁻¹)^{2q}` for the first derivatives of a loop of
length `q` along the slices `(i, j)` at `w = h_{ij}`, on the good event. -/
private lemma LF_loop_d1_sq {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 0 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h)
    (l : List (LF_T D N)) (hl : ∀ f ∈ l, opNorm f.1 ≤ K ∧ f.2.1 = Λ ∧ LF_pm z f.2.2) :
    ∑ i, ∑ j, (‖dW (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2 +
        ‖dWbar (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2) ≤
      2 * ((((D : ℝ) * N)⁻¹) ^ 2 * (l.length : ℝ) ^ 2 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) *
        (K * z.im⁻¹) ^ (2 * l.length)) := by
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hok : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := fun f hf => by
    obtain ⟨-, h1, h2⟩ := hl f hf
    exact ⟨h1 ▸ hs.herm, LF_pm_ne hη h2⟩
  set n := l.length with hn
  set F := (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹) ^ (2 * n) with hF
  have hWfs : ∀ r : Fin n, LF_fs (LF_W h l r) ≤ F := by
    intro r
    have hr := hl (l.get r) (List.get_mem l r)
    have hG := LF_fs_good hs h hh hg hr.2.2
    have hdr : opNorm (chainB h (l.drop (r + 1))) ≤ (K * z.im⁻¹) ^ (l.drop (r + 1)).length :=
      LF_opNorm_chain Λ hs.herm z hη K hK0 h hh _ fun f hf => hl f (List.mem_of_mem_drop hf)
    have htk : opNorm (chainB h (l.take (r + 1))) ≤ (K * z.im⁻¹) ^ (l.take (r + 1)).length :=
      LF_opNorm_chain Λ hs.herm z hη K hK0 h hh _ fun f hf => hl f (List.mem_of_mem_take hf)
    have hlen : (l.drop (r + 1)).length + (l.take (r + 1)).length = n := by
      simp only [List.length_drop, List.length_take, hn]
      have := r.2
      omega
    unfold LF_W
    rw [hr.2.1]
    refine (LF_fs_mul_right _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (LF_fs_mul_right _ _) (sq_nonneg _)).trans ?_
    have hKe : 0 ≤ K * z.im⁻¹ := by positivity
    calc LF_fs (res (Matrix.of h + Λ) (l.get r).2.2) * opNorm (chainB h (l.drop (r + 1))) ^ 2 *
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
  have hc : ∀ i j : Idx D N, ‖LF_cc i j‖ ≤ 1 := by
    intro i j; unfold LF_cc; split_ifs <;> norm_num
  have hDN : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  have hnorm : ∀ (i j : Idx D N) (v : Fin n → ℂ),
      ‖-LF_cc i j * (((D : ℂ) * N)⁻¹ * ∑ r, v r)‖ ^ 2 ≤
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
    calc (‖LF_cc i j‖ * (((D : ℝ) * N)⁻¹ * ‖∑ r, v r‖)) ^ 2
        ≤ (1 * (((D : ℝ) * N)⁻¹ * ‖∑ r, v r‖)) ^ 2 := by
          gcongr
          exact hc i j
      _ = (((D : ℝ) * N)⁻¹) ^ 2 * ‖∑ r, v r‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hpt : ∀ i j, ‖dW (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2 +
      ‖dWbar (fun w => ntr (chainB (setEntry h i j w) l)) (h i j)‖ ^ 2 ≤
      (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, ‖LF_W h l r j i‖ ^ 2) +
        (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, ‖LF_W h l r i j‖ ^ 2) := by
    intro i j
    obtain ⟨d1, d2⟩ := LF_loop_d1 l hok h hh i j
    rw [d1, d2]
    exact add_le_add (hnorm i j _) (hnorm i j _)
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsw : ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖LF_W h l r j i‖ ^ 2 =
      ∑ r : Fin n, LF_fs (LF_W h l r) := by
    calc ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖LF_W h l r j i‖ ^ 2
        = ∑ i : Idx D N, ∑ r : Fin n, ∑ j : Idx D N, ‖LF_W h l r j i‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r : Fin n, ∑ i : Idx D N, ∑ j : Idx D N, ‖LF_W h l r j i‖ ^ 2 := Finset.sum_comm
      _ = ∑ r : Fin n, ∑ j : Idx D N, ∑ i : Idx D N, ‖LF_W h l r j i‖ ^ 2 :=
          Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r : Fin n, LF_fs (LF_W h l r) := rfl
  have hsw' : ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖LF_W h l r i j‖ ^ 2 =
      ∑ r : Fin n, LF_fs (LF_W h l r) := by
    calc ∑ i : Idx D N, ∑ j : Idx D N, ∑ r : Fin n, ‖LF_W h l r i j‖ ^ 2
        = ∑ i : Idx D N, ∑ r : Fin n, ∑ j : Idx D N, ‖LF_W h l r i j‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r : Fin n, ∑ i : Idx D N, ∑ j : Idx D N, ‖LF_W h l r i j‖ ^ 2 := Finset.sum_comm
      _ = ∑ r : Fin n, LF_fs (LF_W h l r) := rfl
  rw [hsw, hsw']
  have hsum : ∑ r : Fin n, LF_fs (LF_W h l r) ≤ n * F := by
    refine (Finset.sum_le_sum fun r _ => hWfs r).trans (le_of_eq ?_)
    simp
  have hF0 : 0 ≤ F := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hsum hn0
  calc (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, LF_fs (LF_W h l r)) +
        (((D : ℝ) * N)⁻¹) ^ 2 * ((n : ℝ) * ∑ r : Fin n, LF_fs (LF_W h l r))
      ≤ (((D : ℝ) * N)⁻¹) ^ 2 * (n * (n * F)) + (((D : ℝ) * N)⁻¹) ^ 2 * (n * (n * F)) := by
        gcongr
    _ = _ := by rw [hF]; ring

/-- The sum `Σ_{t,x} |c_t|²`. -/
private def LF_Cz2 (D : ℕ) (θ : ℝ) : ℝ := ∑ t : Fin 6, ∑ _x : Fin D, ‖LF_cf D θ t‖ ^ 2

/-- Exchanging two pairs of finite sums. -/
private lemma LF_sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- `|Σ_{m} a_m|² ≤ |S| Σ_m |a_m|²`. -/
private lemma LF_sq_sum_le {κ : Type*} (s : Finset κ) (a : κ → ℂ) :
    ‖∑ m ∈ s, a m‖ ^ 2 ≤ (s.card : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun m => ‖a m‖)
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at this
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans this

/-- The values of the loops of the terms at a point of the good event. -/
private lemma LF_loop_vals {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) (k : Idx D N)
    (x : Fin D) (t : Fin 6) :
    ‖ntr (chainB h (LF_l1 Λ T z₁ z₂ x t))‖ ≤ K * Γ₀ ∧
      ‖ntr (chainB h (LF_l2 Λ B T z₁ z₂ x t))‖ ≤ K ^ 2 * Γ₀ * (1 + z.im⁻¹) := by
  have hg' : LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h k k (h k k)) := by
    rw [LF_setEntry_self h hh]; exact hg
  have hK := hs.hK
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  constructor
  · rcases Nat.lt_or_ge (LF_l1 Λ T z₁ z₂ x t).length 1 with h0 | h1
    · have hnil : LF_l1 Λ T z₁ z₂ x t = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hD : NeZero D := ⟨by have := k.1.pos; omega⟩
      have hN : NeZero N := ⟨by have := k.2.pos; omega⟩
      rw [hnil, LF_chain0, LF_ntr_one, norm_one]
      nlinarith
    · have hv := (LF_jet_loop hs hΓ0 h hh k k (h k k) hg' _ h1
        (LF_l1_len Λ T z₁ z₂ x t |>.trans (by norm_num)) (hs.f1 x t)).1
      rw [LF_setEntry_self h hh] at hv
      have e : (LF_l1 Λ T z₁ z₂ x t).length = 1 := le_antisymm (LF_l1_len Λ T z₁ z₂ x t) h1
      rw [e] at hv
      simpa [LF_Gs] using hv
  · obtain ⟨hl1, hl2⟩ := LF_l2_len Λ B T z₁ z₂ x t
    have hv := (LF_jet_loop hs hΓ0 h hh k k (h k k) hg' _ hl1 hl2 (hs.f2 x t)).1
    rw [LF_setEntry_self h hh] at hv
    refine hv.trans ?_
    rcases Nat.lt_or_ge (LF_l2 Λ B T z₁ z₂ x t).length 2 with h1 | h2
    · have e : (LF_l2 Λ B T z₁ z₂ x t).length = 1 := by omega
      rw [e]
      simp only [LF_Gs, pow_one, Nat.sub_self, pow_zero, mul_one]
      have h5 : K * Γ₀ ≤ K ^ 2 * Γ₀ := mul_le_mul_of_nonneg_right (by nlinarith) hΓ0
      have h6 : 0 ≤ K ^ 2 * Γ₀ * z.im⁻¹ := by positivity
      nlinarith
    · have e : (LF_l2 Λ B T z₁ z₂ x t).length = 2 := by omega
      rw [e]
      simp only [LF_Gs, Nat.add_one_sub_one, pow_one]
      nlinarith [mul_nonneg (mul_nonneg hK0 hK0) hΓ0]

/-- The sum over the slices `(i, j)` of the squared first derivatives of `LF_Z` at `w = h_{ij}`
on the good event: `≤ 12 D (Σ |c_t|²) (A₂² S₁ + A₁² S₂)`, which is of order
`Γ₀³ (DN)⁻¹ η⁻⁵`. -/
private lemma LF_Z_d1_sq {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ}
    {z z₁ z₂ : ℂ} {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) :
    ∑ i, ∑ j, (‖dW (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) (h i j)‖ ^ 2 +
        ‖dWbar (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) (h i j)‖ ^ 2) ≤
      12 * D * LF_Cz2 D θ * ((K ^ 2 * Γ₀ * (1 + z.im⁻¹)) ^ 2 *
          (2 * ((((D : ℝ) * N)⁻¹) ^ 2 * 1 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) * (K * z.im⁻¹) ^ 2)) +
        (K * Γ₀) ^ 2 * (2 * ((((D : ℝ) * N)⁻¹) ^ 2 * 4 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) *
          ((K * z.im⁻¹) ^ 2 + (K * z.im⁻¹) ^ 4)))) := by
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hη := hs.hz
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hK := hs.hK
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hDN : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  set A1 := K * Γ₀ with hA1
  set A2 := K ^ 2 * Γ₀ * (1 + z.im⁻¹) with hA2
  set S1 := 2 * ((((D : ℝ) * N)⁻¹) ^ 2 * 1 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) * (K * z.im⁻¹) ^ 2)
    with hS1
  set S2 := 2 * ((((D : ℝ) * N)⁻¹) ^ 2 * 4 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) *
    ((K * z.im⁻¹) ^ 2 + (K * z.im⁻¹) ^ 4)) with hS2
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  -- the slices of the loops and their derivatives
  let L1 : Fin 6 → Fin D → Idx D N → Idx D N → ℂ → ℂ := fun t x i j w =>
    ntr (chainB (setEntry h i j w) (LF_l1 Λ T z₁ z₂ x t))
  let L2 : Fin 6 → Fin D → Idx D N → Idx D N → ℂ → ℂ := fun t x i j w =>
    ntr (chainB (setEntry h i j w) (LF_l2 Λ B T z₁ z₂ x t))
  have hsm1 : ∀ t x i j, LF_Sm (L1 t x i j) := fun t x i j =>
    LF_sm_slice (F := fun h' => ntr (chainB h' (LF_l1 Λ T z₁ z₂ x t)))
      (fun n => LF_cd_loop _ (LF_l1_ok hs.herm T hz₁ hz₂ x t) n) h hh i j
  have hsm2 : ∀ t x i j, LF_Sm (L2 t x i j) := fun t x i j =>
    LF_sm_slice (F := fun h' => ntr (chainB h' (LF_l2 Λ B T z₁ z₂ x t)))
      (fun n => LF_cd_loop _ (LF_l2_ok hs.herm B T hz₁ hz₂ x t) n) h hh i j
  -- the loop derivative sums
  have hd1 : ∀ t x, ∑ i, ∑ j, (‖dW (L1 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L1 t x i j) (h i j)‖ ^ 2)
      ≤ S1 := by
    intro t x
    have hlen := LF_l1_len Λ T z₁ z₂ x t
    have := LF_loop_d1_sq hs hΓ0 h hh hg (LF_l1 Λ T z₁ z₂ x t)
      (fun f hf => (hs.f1 x t f hf).2)
    refine this.trans ?_
    rw [hS1]
    have hn : ((LF_l1 Λ T z₁ z₂ x t).length : ℝ) ≤ 1 := by exact_mod_cast hlen
    have hn0 : (0 : ℝ) ≤ (LF_l1 Λ T z₁ z₂ x t).length := Nat.cast_nonneg _
    rcases Nat.lt_or_ge (LF_l1 Λ T z₁ z₂ x t).length 1 with h0 | h1
    · have e : (LF_l1 Λ T z₁ z₂ x t).length = 0 := by omega
      rw [e]; norm_num; positivity
    · have e : (LF_l1 Λ T z₁ z₂ x t).length = 1 := by omega
      rw [e]; simp
  have hd2 : ∀ t x, ∑ i, ∑ j, (‖dW (L2 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L2 t x i j) (h i j)‖ ^ 2)
      ≤ S2 := by
    intro t x
    obtain ⟨hl1, hl2⟩ := LF_l2_len Λ B T z₁ z₂ x t
    have := LF_loop_d1_sq hs hΓ0 h hh hg (LF_l2 Λ B T z₁ z₂ x t)
      (fun f hf => (hs.f2 x t f hf).2)
    refine this.trans ?_
    rw [hS2]
    have hP : 0 ≤ (((D : ℝ) * N)⁻¹) ^ 2 * ((D * N : ℝ) * Γ₀ * z.im⁻¹) := by positivity
    have hKe : 0 ≤ (K * z.im⁻¹) ^ 2 := sq_nonneg _
    have hKe4 : 0 ≤ (K * z.im⁻¹) ^ 4 := by positivity
    rcases Nat.lt_or_ge (LF_l2 Λ B T z₁ z₂ x t).length 2 with h1 | h2
    · have e : (LF_l2 Λ B T z₁ z₂ x t).length = 1 := by omega
      rw [e]; simp only [Nat.cast_one, one_pow, mul_one]
      nlinarith [mul_nonneg hP hKe4, mul_nonneg hP hKe]
    · have e : (LF_l2 Λ B T z₁ z₂ x t).length = 2 := by omega
      rw [e]
      have e4 : (K * z.im⁻¹) ^ (2 * 2) = (K * z.im⁻¹) ^ 4 := by norm_num
      rw [e4]
      push_cast
      have h4 : (K * z.im⁻¹) ^ 4 ≤ (K * z.im⁻¹) ^ 2 + (K * z.im⁻¹) ^ 4 := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hP
      nlinarith [h5]
  -- the derivative of `LF_Z` along a slice
  have hZd : ∀ i j, (‖dW (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) (h i j)‖ ^ 2 +
      ‖dWbar (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) (h i j)‖ ^ 2) ≤
      12 * D * ∑ t : Fin 6, ∑ x : Fin D, ‖LF_cf D θ t‖ ^ 2 *
        (A2 ^ 2 * (‖dW (L1 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L1 t x i j) (h i j)‖ ^ 2) +
          A1 ^ 2 * (‖dW (L2 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L2 t x i j) (h i j)‖ ^ 2)) := by
    intro i j
    have e : (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) = fun w => ∑ p : Fin 6 × Fin D,
        LF_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w) := by
      funext w
      unfold LF_Z
      rw [Fintype.sum_prod_type]
      simp only [L1, L2, mul_assoc]
    have hsP : ∀ p : Fin 6 × Fin D, LF_Sm (fun w =>
        LF_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w)) := fun p =>
      LF_sm_cmul _ (LF_sm_mul (hsm1 _ _ i j) (hsm2 _ _ i j))
    have hD1 : ∀ (d : (ℂ → ℂ) → ℂ → ℂ), (d = dW ∨ d = dWbar) →
        d (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) (h i j) = ∑ p : Fin 6 × Fin D,
          LF_cf D θ p.1 * (d (L1 p.1 p.2 i j) (h i j) * L2 p.1 p.2 i j (h i j) +
            L1 p.1 p.2 i j (h i j) * d (L2 p.1 p.2 i j) (h i j)) := by
      rintro d (rfl | rfl)
      · have hs1 := LF_wirt_sum Finset.univ _ hsP 1 0
        have hc1 : ∀ p : Fin 6 × Fin D, wirt 1 0 (fun w =>
            LF_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w)) = fun w =>
            LF_cf D θ p.1 * wirt 1 0 (fun w => L1 p.1 p.2 i j w * L2 p.1 p.2 i j w) w :=
          fun p => LF_wirt_cmul (LF_sm_mul (hsm1 _ _ i j) (hsm2 _ _ i j)) _ 1 0
        simp only [hc1] at hs1
        simp only [wirt, Function.iterate_one, Function.iterate_zero, id_eq] at hs1
        rw [e, hs1]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [(dW_mul ((hsm1 _ _ i j).diff _) ((hsm2 _ _ i j).diff _)).1]
      · have hs1 := LF_wirt_sum Finset.univ _ hsP 0 1
        have hc1 : ∀ p : Fin 6 × Fin D, wirt 0 1 (fun w =>
            LF_cf D θ p.1 * (L1 p.1 p.2 i j w * L2 p.1 p.2 i j w)) = fun w =>
            LF_cf D θ p.1 * wirt 0 1 (fun w => L1 p.1 p.2 i j w * L2 p.1 p.2 i j w) w :=
          fun p => LF_wirt_cmul (LF_sm_mul (hsm1 _ _ i j) (hsm2 _ _ i j)) _ 0 1
        simp only [hc1] at hs1
        simp only [wirt, Function.iterate_one, Function.iterate_zero, id_eq] at hs1
        rw [e, hs1]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [(dW_mul ((hsm1 _ _ i j).diff _) ((hsm2 _ _ i j).diff _)).2]
    have hv : ∀ p : Fin 6 × Fin D, ‖L1 p.1 p.2 i j (h i j)‖ ≤ A1 ∧
        ‖L2 p.1 p.2 i j (h i j)‖ ≤ A2 := by
      intro p
      simp only [L1, L2, LF_setEntry_self h hh]
      exact LF_loop_vals hs hΓ₀ h hh hg i p.2 p.1
    have hbd : ∀ (d : (ℂ → ℂ) → ℂ → ℂ), (d = dW ∨ d = dWbar) →
        ‖d (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)) (h i j)‖ ^ 2 ≤
          6 * D * ∑ p : Fin 6 × Fin D, ‖LF_cf D θ p.1‖ ^ 2 *
            (2 * (A2 ^ 2 * ‖d (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
              A1 ^ 2 * ‖d (L2 p.1 p.2 i j) (h i j)‖ ^ 2)) := by
      intro d hd
      rw [hD1 d hd]
      refine (LF_sq_sum_le _ _).trans ?_
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      push_cast
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (by positivity)
      rw [norm_mul, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      obtain ⟨v1, v2⟩ := hv p
      have h1 : ‖d (L1 p.1 p.2 i j) (h i j) * L2 p.1 p.2 i j (h i j)‖ ≤
          ‖d (L1 p.1 p.2 i j) (h i j)‖ * A2 := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left v2 (norm_nonneg _)
      have h2 : ‖L1 p.1 p.2 i j (h i j) * d (L2 p.1 p.2 i j) (h i j)‖ ≤
          A1 * ‖d (L2 p.1 p.2 i j) (h i j)‖ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right v1 (norm_nonneg _)
      have h3 := (norm_add_le _ _).trans (add_le_add h1 h2)
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      refine h4.trans ?_
      nlinarith [sq_nonneg (‖d (L1 p.1 p.2 i j) (h i j)‖ * A2 - A1 * ‖d (L2 p.1 p.2 i j) (h i j)‖)]
    have b1 := hbd dW (Or.inl rfl)
    have b2 := hbd dWbar (Or.inr rfl)
    rw [← Fintype.sum_prod_type (f := fun p : Fin 6 × Fin D => ‖LF_cf D θ p.1‖ ^ 2 *
      (A2 ^ 2 * (‖dW (L1 p.1 p.2 i j) (h i j)‖ ^ 2 + ‖dWbar (L1 p.1 p.2 i j) (h i j)‖ ^ 2) +
        A1 ^ 2 * (‖dW (L2 p.1 p.2 i j) (h i j)‖ ^ 2 + ‖dWbar (L2 p.1 p.2 i j) (h i j)‖ ^ 2)))]
    have : 6 * (D : ℝ) * (∑ p : Fin 6 × Fin D, ‖LF_cf D θ p.1‖ ^ 2 *
          (2 * (A2 ^ 2 * ‖dW (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
            A1 ^ 2 * ‖dW (L2 p.1 p.2 i j) (h i j)‖ ^ 2))) +
        6 * (D : ℝ) * ∑ p : Fin 6 × Fin D, ‖LF_cf D θ p.1‖ ^ 2 *
          (2 * (A2 ^ 2 * ‖dWbar (L1 p.1 p.2 i j) (h i j)‖ ^ 2 +
            A1 ^ 2 * ‖dWbar (L2 p.1 p.2 i j) (h i j)‖ ^ 2)) =
        12 * D * ∑ p : Fin 6 × Fin D, ‖LF_cf D θ p.1‖ ^ 2 *
          (A2 ^ 2 * (‖dW (L1 p.1 p.2 i j) (h i j)‖ ^ 2 + ‖dWbar (L1 p.1 p.2 i j) (h i j)‖ ^ 2) +
            A1 ^ 2 * (‖dW (L2 p.1 p.2 i j) (h i j)‖ ^ 2 +
              ‖dWbar (L2 p.1 p.2 i j) (h i j)‖ ^ 2)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    linarith
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hZd i j).trans ?_
  set F : Fin 6 → Fin D → Idx D N → Idx D N → ℝ := fun t x i j => ‖LF_cf D θ t‖ ^ 2 *
    (A2 ^ 2 * (‖dW (L1 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L1 t x i j) (h i j)‖ ^ 2) +
      A1 ^ 2 * (‖dW (L2 t x i j) (h i j)‖ ^ 2 + ‖dWbar (L2 t x i j) (h i j)‖ ^ 2)) with hF
  have hswap : ∑ i, ∑ j, (12 * (D : ℝ) * ∑ t, ∑ x, F t x i j) =
      12 * (D : ℝ) * ∑ t, ∑ x, ∑ i, ∑ j, F t x i j := by
    rw [← LF_sum4_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hswap, mul_assoc (12 * (D : ℝ)) (LF_Cz2 D θ)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold LF_Cz2
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [hF, ← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hd1' := hd1 t x
  have hd2' := hd2 t x
  simp only [Finset.sum_add_distrib] at hd1' hd2'
  exact add_le_add (mul_le_mul_of_nonneg_left hd1' (sq_nonneg _))
    (mul_le_mul_of_nonneg_left hd2' (sq_nonneg _))

/-! ### Derivatives of `Z^{p-1} Z̄^p` and the second-order Leibniz bound -/

/-- `|∂_w (u^{p-1} ū^p)| + |∂_{w̄} (u^{p-1} ū^p)| ≤ 2(2p-1) |u|^{2p-2} (|∂_w u| + |∂_{w̄} u|)`. -/
private lemma LF_dPhi {u : ℂ → ℂ} (hu : LF_Sm u) (w : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    ‖dW (fun y => u y ^ (p - 1) * starRingEnd ℂ (u y) ^ p) w‖ +
        ‖dWbar (fun y => u y ^ (p - 1) * starRingEnd ℂ (u y) ^ p) w‖ ≤
      2 * (2 * p - 1) * ‖u w‖ ^ (2 * p - 2) * (‖dW u w‖ + ‖dWbar u w‖) := by
  set β := ‖dW u w‖ + ‖dWbar u w‖ with hβ
  have hβ1 : ‖dW u w‖ ≤ β := by linarith [norm_nonneg (dWbar u w)]
  have hβ2 : ‖dWbar u w‖ ≤ β := by linarith [norm_nonneg (dW u w)]
  have hβ0 : 0 ≤ β := by positivity
  have huc : LF_Sm (fun y => starRingEnd ℂ (u y)) := LF_sm_conj hu
  have hc1 : ‖dW (fun y => starRingEnd ℂ (u y)) w‖ ≤ β := by
    rw [(dW_conj (hu.diff w)).1, Complex.norm_conj]; exact hβ2
  have hc2 : ‖dWbar (fun y => starRingEnd ℂ (u y)) w‖ ≤ β := by
    rw [(dW_conj (hu.diff w)).2, Complex.norm_conj]; exact hβ1
  obtain ⟨a1, a2⟩ := LF_pow_d1 hu w ‖u w‖ β le_rfl hβ1 hβ2 (p - 1)
  obtain ⟨b1, b2⟩ := LF_pow_d1 huc w ‖u w‖ β (by rw [Complex.norm_conj]) hc1 hc2 p
  have hA := LF_sm_pow hu (p - 1)
  have hB := LF_sm_pow huc p
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
private lemma LF_leib2 {f g : ℂ → ℂ} (hf : LF_Sm f) (hg : LF_Sm g) (w : ℂ) (a b : ℕ)
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
  rw [LF_wirt_mul hf hg a b w]
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
private lemma LF_jet_Phi {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ)
    (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h i j w)) (Km p : ℕ) (hp : 1 ≤ p) :
    ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w') ^ (p - 1) *
          starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ (setEntry h i j w')) ^ p) w‖ ≤
        (2 * LF_Gt Km K Γ₀) ^ (a + b) * ((2 * p - 1 : ℝ)) ^ (a + b) *
          (‖LF_Z θ Λ B T z₁ z₂ (setEntry h i j w)‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1) := by
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Γt := LF_Gt Km K Γ₀ with hΓt
  have hΓt0 : 0 ≤ Γt := by simp only [hΓt, LF_Gt]; positivity
  set Pz := LF_Pz D N θ K Γ₀ z.im with hPz
  have hPz0 : 0 ≤ Pz := LF_Pz_nonneg θ hK0 hΓ0 hs.hz
  set u : ℂ → ℂ := fun w' => LF_Z θ Λ B T z₁ z₂ (setEntry h i j w') with hu
  have hsu : LF_Sm u := LF_sm_slice (F := fun h' => LF_Z θ Λ B T z₁ z₂ h')
    (fun n => LF_cd_Z θ hs.herm B T hz₁ hz₂ n) h hh i j
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
    · refine (LF_jet_Z θ hs hΓ₀ h hh i j w hg Km a b h0 hab).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (u w)]) (by positivity)
  have hUc : ∀ a b, a + b ≤ Km →
      ‖wirt a b (fun w' => starRingEnd ℂ (u w')) w‖ ≤ (2 * Γt) ^ (a + b) * c := by
    intro a b hab
    rw [LF_wirt_conj hsu, Complex.norm_conj, add_comm a b]
    exact hU b a (by omega)
  have hP1 := LF_pow_jet hsu w (2 * Γt) c Km (by positivity) hc0 hU (p - 1)
  have hP2 := LF_pow_jet (LF_sm_conj hsu) w (2 * Γt) c Km (by positivity) hc0 hUc p
  have hΦ := LF_LB (LF_sm_pow hsu (p - 1)) (LF_sm_pow (LF_sm_conj hsu) p) w (2 * Γt)
    ((p - 1 : ℕ) : ℝ) (p : ℝ) (c ^ (p - 1)) (c ^ p) Km (by positivity) (Nat.cast_nonneg _)
    (pow_nonneg hc0 _) hP1 hP2
  intro a b hab
  refine (hΦ a b hab).trans (le_of_eq ?_)
  have hp' : ((p - 1 : ℕ) : ℝ) = p - 1 := by
    rw [Nat.cast_sub hp]; simp
  have hc2 : c ^ (p - 1) * c ^ p = c ^ (2 * p - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hp', hc2]
  ring

/-- The bound `S_Z` on `Σ_{i,j} (|∂_w Z|² + |∂_{w̄} Z|²)` of `LF_Z_d1_sq`. -/
private def LF_SZ (D N : ℕ) (θ K Γ₀ η : ℝ) : ℝ :=
  12 * D * LF_Cz2 D θ * ((K ^ 2 * Γ₀ * (1 + η⁻¹)) ^ 2 *
      (2 * ((((D : ℝ) * N)⁻¹) ^ 2 * 1 * ((D * N : ℝ) * Γ₀ * η⁻¹) * (K * η⁻¹) ^ 2)) +
    (K * Γ₀) ^ 2 * (2 * ((((D : ℝ) * N)⁻¹) ^ 2 * 4 * ((D * N : ℝ) * Γ₀ * η⁻¹) *
      ((K * η⁻¹) ^ 2 + (K * η⁻¹) ^ 4))))

/-- Cauchy–Schwarz for real arrays over the pairs `(i, j)`. -/
private lemma LF_cs_real {ι : Type*} [Fintype ι] (f g : ι → ι → ℝ) (hf : ∀ i j, 0 ≤ f i j)
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
private lemma LF_sum_pair {D N : ℕ} (x y : Idx D N → Idx D N → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (hy : ∀ i j, 0 ≤ y i j) (S : ℝ) (hS : ∑ i, ∑ j, (x i j ^ 2 + y i j ^ 2) ≤ S) :
    ∑ i, ∑ j, (x i j + y i j) ≤ (D * N : ℝ) * Real.sqrt (2 * S) := by
  have h := LF_cs_real (fun i j => x i j + y i j) (fun _ _ => (1 : ℝ))
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
private lemma LF_pw12 {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) (Km p : ℕ)
    (hKm : 2 ≤ Km) (hp : 1 ≤ p) :
    let c := ‖LF_Z θ Λ B T z₁ z₂ h‖ + LF_Pz D N θ K Γ₀ z.im
    let FX := (D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2
    let SZ := LF_SZ D N θ K Γ₀ z.im
    (∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ *
        (‖dW (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h β α w) ^ (p - 1) *
            starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ (setEntry h β α w)) ^ p) (h β α)‖ +
          ‖dWbar (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h β α w) ^ (p - 1) *
            starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ (setEntry h β α w)) ^ p) (h β α)‖) ≤
      2 * (2 * p - 1) * c ^ (2 * p - 2) * (Real.sqrt FX * Real.sqrt (2 * SZ))) ∧
    (∀ a b, a + b = 2 →
      ∑ β, ∑ α, ‖wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α)‖ ≤
        18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * z.im⁻¹ *
          Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) * c ^ (2 * p - 1) +
        2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) *
          (2 * (2 * p - 1) * c ^ (2 * p - 2) * ((D * N : ℝ) * Real.sqrt (2 * SZ))) +
        (D * N : ℝ) * Real.sqrt FX *
          ((2 * LF_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))) := by
  intro c FX SZ
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  have hc0 : 0 ≤ c := add_nonneg (norm_nonneg _) (LF_Pz_nonneg θ hK0 hΓ0 hs.hz)
  have hZc : ‖LF_Z θ Λ B T z₁ z₂ h‖ ≤ c := le_add_of_nonneg_right (LF_Pz_nonneg θ hK0 hΓ0 hs.hz)
  have hp1 : (1 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  -- the slices
  have hg' : ∀ β α, LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h β α (h β α)) := fun β α => by
    rw [LF_setEntry_self h hh]; exact hg
  set u : Idx D N → Idx D N → ℂ → ℂ := fun β α w => LF_Z θ Λ B T z₁ z₂ (setEntry h β α w)
    with hu
  have hsu : ∀ β α, LF_Sm (u β α) := fun β α =>
    LF_sm_slice (F := fun h' => LF_Z θ Λ B T z₁ z₂ h') (fun n => LF_cd_Z θ hs.herm B T hz₁ hz₂ n)
      h hh β α
  have hu0 : ∀ β α, u β α (h β α) = LF_Z θ Λ B T z₁ z₂ h := fun β α => by
    simp only [hu, LF_setEntry_self h hh]
  -- the first derivatives of `Z` and `Φ`
  have hdZ := LF_Z_d1_sq θ hs hΓ₀ h hh hg
  have hdu : ∑ β, ∑ α, (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖) ≤
      (D * N : ℝ) * Real.sqrt (2 * SZ) :=
    LF_sum_pair (fun β α => ‖dW (u β α) (h β α)‖) (fun β α => ‖dWbar (u β α) (h β α)‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) SZ hdZ
  have hdΦ : ∀ β α, ‖dW (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ +
      ‖dWbar (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ ≤
      2 * (2 * p - 1) * c ^ (2 * p - 2) * (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖) := by
    intro β α
    refine (LF_dPhi (hsu β α) (h β α) p hp).trans ?_
    rw [hu0]
    gcongr
  -- the matrix `X̃ = G₂ B G₁ T`
  obtain ⟨-, -, -, mX, -, -, -, -, fX, -⟩ := LF_good_mats hs hΓ₀ h hh hg
  have hXe : ∀ β α, LF_X Λ B T z₁ z₂ h β α =
      (res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ * T) β α := fun β α =>
    LF_X_eq Λ B T z₁ z₂ h β α
  refine ⟨?_, ?_⟩
  · -- the term of order one
    have hcs := LF_cs_real (fun β α => ‖LF_X Λ B T z₁ z₂ h β α‖)
      (fun β α => ‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => by positivity)
    have h1 : ∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ ^ 2 ≤ FX := by
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
    calc ∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ *
          (‖dW (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ +
            ‖dWbar (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖)
        ≤ ∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ *
            (2 * (2 * p - 1) * c ^ (2 * p - 2) *
              (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)) :=
          Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ =>
            mul_le_mul_of_nonneg_left (hdΦ β α) (norm_nonneg _)
      _ = 2 * (2 * p - 1) * c ^ (2 * p - 2) * ∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ *
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
    have hsX : ∀ β α, LF_Sm (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) := fun β α =>
      LF_sm_slice (F := fun h' => LF_X Λ B T z₁ z₂ h' β α)
        (fun n => LF_cd_X hs.herm B T hz₁ hz₂ β α n) h hh β α
    have hsΦ : ∀ β α, LF_Sm (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) :=
      fun β α => LF_sm_mul (LF_sm_pow (hsu β α) _) (LF_sm_pow (LF_sm_conj (hsu β α)) _)
    have hX1 : ∀ β α, ‖dW (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ +
        ‖dWbar (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ ≤
        2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹)) := by
      intro β α
      have e1 := LF_jet_X hs hΓ0 h hh β α (h β α) (hg' β α) β α 1 0
      have e2 := LF_jet_X hs hΓ0 h hh β α (h β α) (hg' β α) β α 0 1
      have hv : ((2 + 1 + 0 : ℕ) : ℝ) ^ (1 + 0) * LF_Gs K Γ₀ z.im 1 ^ (1 + 0) *
          LF_Gs K Γ₀ z.im 2 = 3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹) := by
        simp only [LF_Gs]; norm_num
      have hv' : ((2 + 0 + 1 : ℕ) : ℝ) ^ (0 + 1) * LF_Gs K Γ₀ z.im 1 ^ (0 + 1) *
          LF_Gs K Γ₀ z.im 2 = 3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹) := by
        simp only [LF_Gs]; norm_num
      rw [hv] at e1
      rw [hv'] at e2
      have e1' : ‖dW (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ ≤
          3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹) := e1
      have e2' : ‖dWbar (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ ≤
          3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹) := e2
      linarith
    have hΦv : ∀ β α, ‖u β α (h β α) ^ (p - 1) * starRingEnd ℂ (u β α (h β α)) ^ p‖ ≤
        c ^ (2 * p - 1) := by
      intro β α
      rw [hu0, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add,
        show p - 1 + p = 2 * p - 1 by omega]
      exact pow_le_pow_left₀ (norm_nonneg _) hZc _
    have hΦ2 : ∀ β α, ‖wirt a b (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p)
        (h β α)‖ ≤ (2 * LF_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1) := by
      intro β α
      have := LF_jet_Phi θ hs hΓ₀ h hh β α (h β α) (hg' β α) Km p hp a b (by omega)
      rw [hab, LF_setEntry_self h hh] at this
      exact this
    have hpt : ∀ β α, ‖wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w))
        (h β α)‖ ≤
        ‖wirt a b (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ * c ^ (2 * p - 1) +
        2 * ((2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) *
          (2 * (2 * p - 1) * c ^ (2 * p - 2) * (‖dW (u β α) (h β α)‖ +
            ‖dWbar (u β α) (h β α)‖))) +
        ‖LF_X Λ B T z₁ z₂ h β α‖ *
          ((2 * LF_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1)) := by
      intro β α
      have e : (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) = fun w =>
          LF_X Λ B T z₁ z₂ (setEntry h β α w) β α *
            (u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) := by
        funext w; rfl
      rw [e]
      refine (LF_leib2 (hsX β α) (hsΦ β α) (h β α) a b hab).trans ?_
      have hXv : ‖LF_X Λ B T z₁ z₂ (setEntry h β α (h β α)) β α‖ = ‖LF_X Λ B T z₁ z₂ h β α‖ := by
        rw [LF_setEntry_self h hh]
      rw [hXv]
      have hdx0 : 0 ≤ ‖dW (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ +
          ‖dWbar (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ := by positivity
      have hdp0 : 0 ≤ ‖dW (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ +
          ‖dWbar (fun w => u β α w ^ (p - 1) * starRingEnd ℂ (u β α w) ^ p) (h β α)‖ := by
        positivity
      have hW : 0 ≤ 2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹)) := by positivity
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hΦv β α) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (mul_le_mul (hX1 β α) (hdΦ β α) hdp0 hW) (by norm_num)))
        (mul_le_mul_of_nonneg_left (hΦ2 β α) (norm_nonneg _))
    refine (Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun α _ => hpt β α).trans ?_
    simp only [Finset.sum_add_distrib]
    have s1 := LF_sum_d2X hs hΓ₀ h hh hg a b hab
    have s3 : ∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ ≤ (D * N : ℝ) * Real.sqrt FX := by
      have := LF_sum_off (res (Matrix.of h + Λ) z₂ * B * res (Matrix.of h + Λ) z₁ * T) FX fX
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at this
      simpa only [hXe] using this
    have hcp : 0 ≤ c ^ (2 * p - 1) := pow_nonneg hc0 _
    have hJ : 0 ≤ (2 * LF_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1) := by
      positivity
    have hW : 0 ≤ 2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹)) := by positivity
    have hcq : 0 ≤ 2 * (2 * (p : ℝ) - 1) * c ^ (2 * p - 2) := by
      have := pow_nonneg hc0 (2 * p - 2); nlinarith
    calc (∑ β, ∑ α, ‖wirt a b (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α) (h β α)‖ *
            c ^ (2 * p - 1)) +
          (∑ β, ∑ α, 2 * ((2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) *
            (2 * (2 * p - 1) * c ^ (2 * p - 2) *
              (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)))) +
          ∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖ *
            ((2 * LF_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))
        = (∑ β, ∑ α, ‖wirt a b (fun w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α)
              (h β α)‖) * c ^ (2 * p - 1) +
          2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) * (2 * (2 * p - 1) *
            c ^ (2 * p - 2) * ∑ β, ∑ α, (‖dW (u β α) (h β α)‖ + ‖dWbar (u β α) (h β α)‖)) +
          (∑ β, ∑ α, ‖LF_X Λ B T z₁ z₂ h β α‖) *
            ((2 * LF_Gt Km K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1)) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          congr 1
          congr 1
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          ring
      _ ≤ _ := by
          gcongr

/-! ### Crude bounds and integrability -/

/-- The crude constant `Γ₀ = K² (1 + η⁻¹)` of the good event, valid on every Hermitian array. -/
private def LF_Gc0 (K η : ℝ) : ℝ := K ^ 2 * (1 + η⁻¹)

/-- The crude bound `|Z| ≤ Σ|c_t| (K Γ₀) (K² Γ₀ (1 + η⁻¹))` with `Γ₀ = LF_Gc0`. -/
private def LF_Zc (D : ℕ) (θ K η : ℝ) : ℝ :=
  LF_Cz D θ * (K * LF_Gc0 K η) * (K ^ 2 * LF_Gc0 K η * (1 + η⁻¹))

/-- The crude bound on the mixed derivatives of order `≤ K_m` of the integrand. -/
private def LF_Bc (D N : ℕ) (θ : ℝ) (Km p : ℕ) (K η : ℝ) : ℝ :=
  (4 * p * LF_Gt Km K (LF_Gc0 K η)) ^ Km * LF_Gs K (LF_Gc0 K η) η 2 *
    (LF_Zc D θ K η + LF_Pz D N θ K (LF_Gc0 K η) η) ^ (2 * p - 1)

private lemma LF_Gc0_ge {K η : ℝ} (hK : 1 ≤ K) (hη : 0 < η) : 1 ≤ LF_Gc0 K η := by
  unfold LF_Gc0
  have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  nlinarith

/-- The crude bound on `|Z|` on Hermitian arrays. -/
private lemma LF_Z_crude {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) : ‖LF_Z θ Λ B T z₁ z₂ h‖ ≤ LF_Zc D θ K z.im := by
  have hΓ := LF_Gc0_ge hs.hK hs.hz
  have hg := LF_good_crude hs h hh
  rcases isEmpty_or_nonempty (Idx D N) with hE | ⟨⟨k⟩⟩
  · have e : LF_Z θ Λ B T z₁ z₂ h = 0 := by
      have hD : D = 0 ∨ N = 0 := by
        by_contra hc
        push_neg at hc
        exact hE.false (⟨0, Nat.pos_of_ne_zero hc.1⟩, ⟨0, Nat.pos_of_ne_zero hc.2⟩)
      unfold LF_Z
      rcases hD with rfl | rfl
      · simp
      · simp [ntr]
    rw [e, norm_zero]
    unfold LF_Zc
    have := LF_Cz_nonneg D θ
    have : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
    have : 0 ≤ K := by linarith [hs.hK]
    positivity
  unfold LF_Z LF_Zc LF_Cz
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  obtain ⟨v1, v2⟩ := LF_loop_vals hs hΓ h hh hg k x t
  rw [norm_mul, norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact mul_le_mul v1 v2 (norm_nonneg _) (by unfold LF_Gc0 at hΓ ⊢; nlinarith [hs.hK])

/-- The crude bound on the mixed derivatives of the integrand along every slice through a
Hermitian array, orders `a + b ≤ K_m`. -/
private lemma LF_F_crude {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) (Km p : ℕ) (hp : 1 ≤ p)
    (β α : Idx D N) (a b : ℕ) (hab : a + b ≤ Km) :
    ‖wirt a b (fun w' => LF_F θ Λ B T z₁ z₂ p β α (setEntry h i j w')) w‖ ≤
      LF_Bc D N θ Km p K z.im := by
  have hΓ := LF_Gc0_ge hs.hK hs.hz
  have hh' := LF_slice_herm h hh i j w
  have hg := LF_good_crude hs (setEntry h i j w) hh'
  refine (LF_jet_F θ hs hΓ h hh i j w hg Km p hp β α a b hab).trans ?_
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hi : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
  have hΓ0 : 0 ≤ LF_Gc0 K z.im := by linarith
  have hGt : 1 ≤ 4 * p * LF_Gt Km K (LF_Gc0 K z.im) := by
    unfold LF_Gt
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h2 : (2 : ℝ) ≤ 2 + Km := by have : (0 : ℝ) ≤ Km := Nat.cast_nonneg _; linarith
    have h3 : 1 ≤ K * LF_Gc0 K z.im := by nlinarith [hs.hK]
    have h5 : (1 : ℝ) ≤ p * (2 + Km) := by nlinarith
    have h6 := one_le_mul_of_one_le_of_one_le h5 h3
    have e : 4 * (p : ℝ) * ((2 + Km) * K * LF_Gc0 K z.im) =
        4 * ((p * (2 + Km)) * (K * LF_Gc0 K z.im)) := by ring
    rw [e]
    linarith
  have hZ := LF_Z_crude θ hs (setEntry h i j w) hh'
  have hPz := LF_Pz_nonneg (D := D) (N := N) θ hK0 hΓ0 hs.hz
  unfold LF_Bc
  have hG2 : 0 ≤ LF_Gs K (LF_Gc0 K z.im) z.im 2 := by unfold LF_Gs; positivity
  refine mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hGt hab) hG2)
    (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)

/-- The integrands of the expansion are integrable: `∂_w^a ∂_{w̄}^b X_{βα}Φ` at `w = h_{βα}`. -/
private lemma LF_int_wirt {D N : ℕ} (θ : ℝ) {C : ℕ → ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ}
    (hs : LF_Set Λ B T z z₁ z₂ K) (p : ℕ) (hp : 1 ≤ p) (β α : Idx D N) (i j : Idx D N)
    (a b : ℕ) :
    Integrable (fun h => wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h i j w))
      (h i j)) μ := by
  have := hμ.prob
  refine Integrable.mono' (integrable_const (LF_Bc D N θ (a + b) p K z.im))
    (LF_wirt_aesm hμ.herm (fun n => LF_cd_F θ hs.herm B T (LF_pm_ne hs.hz hs.h1)
      (LF_pm_ne hs.hz hs.h2) p β α n) i j a b) ?_
  filter_upwards [hμ.herm] with h hh
  exact LF_F_crude θ hs h hh i j (h i j) (a + b) p hp β α a b le_rfl

/-- `h ↦ F(h)` is almost everywhere strongly measurable when `F ∘ symArr` is continuous. -/
private lemma LF_aesm_sym {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) {E : Type*} [NormedAddCommGroup E]
    {F : (Idx D N → Idx D N → ℂ) → E} (hF : Continuous (fun h => F (symArr h))) :
    AEStronglyMeasurable F μ := by
  refine hF.aestronglyMeasurable.congr ?_
  filter_upwards [hμh] with h hh
  rw [symArr_of_isHermitian h hh]

/-! ### The terms of order `≤ l` of the expansion at a point of the good event -/

/-- The terms of order `≤ l` of the cumulant expansion (2.26) [5.16] of `E X_{βα} Φ h̄_{βα}`,
summed over `(β, α)`, at the array `h`, for the cumulants `κ_{p,q}(β, α)`. -/
private def LF_ES {D N : ℕ} (θ : ℝ) (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ)
    (p l : ℕ) (κ : ℕ → ℕ → Idx D N → Idx D N → ℂ) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ∑ β, ∑ α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
    κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
      wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α)

/-- `0 ≤ (S_θ)_{βα} ≤ N⁻¹` for `θ ∈ [0, 1]`. -/
private lemma LF_varProf_le {D N : ℕ} [NeZero D] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
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
private lemma LF_pw_all {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) (p l : ℕ)
    (hp : 1 ≤ p) (hl : 2 ≤ l) (κ : ℕ → ℕ → Idx D N → Idx D N → ℂ) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (h01 : ∀ β α, κ 0 1 β α = 0) (h11 : ∀ β α, κ 1 1 β α = varProf D N θ β α)
    (h02 : ∀ β α, κ 0 2 β α = if β = α then (varProf D N θ β α : ℂ) else 0)
    (hκ : ∀ a b β α, 3 ≤ a + b → a + b ≤ l + 1 →
      ‖κ a b β α‖ ≤ Kc * (N : ℝ) ^ (-(((a + b : ℕ) : ℝ) / 2))) :
    ‖((D : ℂ) * N)⁻¹ * LF_ES θ Λ B T z₁ z₂ p l κ h +
        LF_C θ Λ B T z₁ z₂ h * (LF_Z θ Λ B T z₁ z₂ h ^ (p - 1) *
          starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ h) ^ p)‖ ≤
      ((D : ℝ) * N)⁻¹ * ((N : ℝ)⁻¹ *
        (2 * (2 * p - 1) * (‖LF_Z θ Λ B T z₁ z₂ h‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 2) *
          (Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2) *
            Real.sqrt (2 * LF_SZ D N θ K Γ₀ z.im))) +
        3 * Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
          (18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * z.im⁻¹ *
            Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) *
              (‖LF_Z θ Λ B T z₁ z₂ h‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1) +
            2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) *
              (2 * (2 * p - 1) * (‖LF_Z θ Λ B T z₁ z₂ h‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 2) *
                ((D * N : ℝ) * Real.sqrt (2 * LF_SZ D N θ K Γ₀ z.im))) +
            (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2) *
              ((2 * LF_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 *
                (‖LF_Z θ Λ B T z₁ z₂ h‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1))) +
        ((l : ℝ) + 1) ^ 2 * Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 *
          ((4 * p * LF_Gt l K Γ₀) ^ l * LF_Gs K Γ₀ z.im 2 *
            (‖LF_Z θ Λ B T z₁ z₂ h‖ + LF_Pz D N θ K Γ₀ z.im) ^ (2 * p - 1)))) := by
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  set Pz := LF_Pz D N θ K Γ₀ z.im with hPz
  have hPz0 : 0 ≤ Pz := LF_Pz_nonneg θ hK0 hΓ0 hs.hz
  set Zh := LF_Z θ Λ B T z₁ z₂ h with hZh
  set c := ‖Zh‖ + Pz with hc
  have hc0 : 0 ≤ c := by positivity
  -- the slices
  set X : Idx D N → Idx D N → ℂ → ℂ := fun β α w => LF_X Λ B T z₁ z₂ (setEntry h β α w) β α
    with hX
  set u : Idx D N → Idx D N → ℂ → ℂ := fun β α w => LF_Z θ Λ B T z₁ z₂ (setEntry h β α w)
    with hu
  set Φ : Idx D N → Idx D N → ℂ → ℂ := fun β α w => u β α w ^ (p - 1) *
    starRingEnd ℂ (u β α w) ^ p with hΦ
  have hsX : ∀ β α, LF_Sm (X β α) := fun β α =>
    LF_sm_slice (F := fun h' => LF_X Λ B T z₁ z₂ h' β α)
      (fun n => LF_cd_X hs.herm B T hz₁ hz₂ β α n) h hh β α
  have hsu : ∀ β α, LF_Sm (u β α) := fun β α =>
    LF_sm_slice (F := fun h' => LF_Z θ Λ B T z₁ z₂ h') (fun n => LF_cd_Z θ hs.herm B T hz₁ hz₂ n)
      h hh β α
  have hsΦ : ∀ β α, LF_Sm (Φ β α) := fun β α =>
    LF_sm_mul (LF_sm_pow (hsu β α) _) (LF_sm_pow (LF_sm_conj (hsu β α)) _)
  have hX0 : ∀ β α, X β α (h β α) = LF_X Λ B T z₁ z₂ h β α := fun β α => by
    simp only [hX, LF_setEntry_self h hh]
  have hΦ0 : ∀ β α, Φ β α (h β α) = Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p := fun β α => by
    simp only [hΦ, hu, LF_setEntry_self h hh, hZh]
  have hFe : ∀ β α, (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) =
      fun w => X β α w * Φ β α w := fun β α => by funext w; rfl
  -- the terms of order one and of order `≥ 2`
  set tm : Idx D N → Idx D N → ℕ → ℕ → ℂ := fun β α a b =>
    κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
      wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α) with htm
  have hsplit : ∀ β α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a), tm β α a b =
      (κ 1 1 β α * dW (fun w => X β α w * Φ β α w) (h β α) +
        κ 0 2 β α * dWbar (fun w => X β α w * Φ β α w) (h β α)) +
      ∑ k ∈ Finset.Ico 2 (l + 1), ∑ a ∈ Finset.range (k + 1), tm β α a (k - a) := by
    intro β α
    rw [LF_regroup (tm β α) l, ← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ l + 1)]
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
      ((varProf D N θ β α : ℂ) * (LF_X Λ B T z₁ z₂ h β α * dW (Φ β α) (h β α)) +
        (if β = α then (varProf D N θ β α : ℂ) else 0) *
          (LF_X Λ B T z₁ z₂ h β α * dWbar (Φ β α) (h β α))) := by
    intro β α
    rw [LF_der_dW.mul _ _ (hsX β α) (hsΦ β α), LF_der_dWbar.mul _ _ (hsX β α) (hsΦ β α)]
    simp only [h11, h02, hX0, hΦ0]
    ring
  have hcan := LF_cancel θ hs.herm B T hz₁ hz₂ h hh
  set R1 : ℂ := ∑ β, ∑ α, ((varProf D N θ β α : ℂ) * (LF_X Λ B T z₁ z₂ h β α *
      dW (Φ β α) (h β α)) + (if β = α then (varProf D N θ β α : ℂ) else 0) *
        (LF_X Λ B T z₁ z₂ h β α * dWbar (Φ β α) (h β α))) with hR1
  set R2 : ℂ := ∑ β, ∑ α, ∑ k ∈ Finset.Ico 2 (l + 1), ∑ a ∈ Finset.range (k + 1),
      tm β α a (k - a) with hR2
  have hES : LF_ES θ Λ B T z₁ z₂ p l κ h =
      (Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p) * (-((D : ℂ) * N) * LF_C θ Λ B T z₁ z₂ h) +
        R1 + R2 := by
    have e1 : LF_ES θ Λ B T z₁ z₂ p l κ h =
        ∑ β, ∑ α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a), tm β α a b := rfl
    rw [e1]
    simp only [hsplit, hprod, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hR1, hR2, ← hcan]
    simp only [Finset.sum_add_distrib, hX]
  have hDN : ((D : ℂ) * N) ≠ 0 := by
    have : (D : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne D
    have : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    exact mul_ne_zero ‹_› ‹_›
  have hmain : ((D : ℂ) * N)⁻¹ * LF_ES θ Λ B T z₁ z₂ p l κ h +
      LF_C θ Λ B T z₁ z₂ h * (Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p) =
      ((D : ℂ) * N)⁻¹ * (R1 + R2) := by
    rw [hES]
    have hinv : ((D : ℂ) * N)⁻¹ * ((D : ℂ) * N) = 1 := inv_mul_cancel₀ hDN
    linear_combination (-(Zh ^ (p - 1) * starRingEnd ℂ Zh ^ p * LF_C θ Λ B T z₁ z₂ h)) * hinv
  rw [hmain, norm_mul]
  have hDNn : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [hDNn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the bound on `R1`
  obtain ⟨pw1, pw2⟩ := LF_pw12 θ hs hΓ₀ h hh hg l p hl hp
  have hR1b : ‖R1‖ ≤ (N : ℝ)⁻¹ *
      (2 * (2 * p - 1) * c ^ (2 * p - 2) *
        (Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2) *
          Real.sqrt (2 * LF_SZ D N θ K Γ₀ z.im))) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left pw1 (inv_nonneg.mpr hN0.le))
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    obtain ⟨v0, v1⟩ := LF_varProf_le (D := D) (N := N) θ hθ0 hθ1 β α
    have hv : ‖(varProf D N θ β α : ℂ)‖ ≤ (N : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg v0]; exact v1
    have hv' : ‖(if β = α then (varProf D N θ β α : ℂ) else 0)‖ ≤ (N : ℝ)⁻¹ := by
      split_ifs
      · exact hv
      · rw [norm_zero]; exact inv_nonneg.mpr hN0.le
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have e : (Φ β α) = (fun w => LF_Z θ Λ B T z₁ z₂ (setEntry h β α w) ^ (p - 1) *
        starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ (setEntry h β α w)) ^ p) := rfl
    rw [← e]
    have hn1 := norm_nonneg (LF_X Λ B T z₁ z₂ h β α)
    have hn2 := norm_nonneg (dW (Φ β α) (h β α))
    have hn3 := norm_nonneg (dWbar (Φ β α) (h β α))
    calc ‖(varProf D N θ β α : ℂ)‖ * (‖LF_X Λ B T z₁ z₂ h β α‖ * ‖dW (Φ β α) (h β α)‖) +
          ‖(if β = α then (varProf D N θ β α : ℂ) else 0)‖ *
            (‖LF_X Λ B T z₁ z₂ h β α‖ * ‖dWbar (Φ β α) (h β α)‖)
        ≤ (N : ℝ)⁻¹ * (‖LF_X Λ B T z₁ z₂ h β α‖ * ‖dW (Φ β α) (h β α)‖) +
          (N : ℝ)⁻¹ * (‖LF_X Λ B T z₁ z₂ h β α‖ * ‖dWbar (Φ β α) (h β α)‖) := by
          gcongr
      _ = (N : ℝ)⁻¹ * (‖LF_X Λ B T z₁ z₂ h β α‖ *
            (‖dW (Φ β α) (h β α)‖ + ‖dWbar (Φ β α) (h β α)‖)) := by ring
  -- the bound on `R2`
  have hGt1 : 1 ≤ 4 * p * LF_Gt l K Γ₀ := by
    unfold LF_Gt
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h2 : (2 : ℝ) ≤ 2 + l := by have : (0 : ℝ) ≤ l := Nat.cast_nonneg _; linarith
    have h3 : 1 ≤ K * Γ₀ := one_le_mul_of_one_le_of_one_le hs.hK hΓ₀
    have h5 : (1 : ℝ) ≤ p * (2 + l) := by nlinarith
    have h6 := one_le_mul_of_one_le_of_one_le h5 h3
    have e : 4 * (p : ℝ) * ((2 + l) * K * Γ₀) = 4 * ((p * (2 + l)) * (K * Γ₀)) := by ring
    rw [e]
    linarith
  have hGs2 : 0 ≤ LF_Gs K Γ₀ z.im 2 := by
    unfold LF_Gs
    have := inv_nonneg.mpr hs.hz.le
    positivity
  set J := (4 * p * LF_Gt l K Γ₀) ^ l * LF_Gs K Γ₀ z.im 2 * c ^ (2 * p - 1) with hJ
  have hJ0 : 0 ≤ J := by positivity
  have hg' : ∀ β α, LF_good Λ z (LF_U Λ B T z₂) Γ₀ (setEntry h β α (h β α)) := fun β α => by
    rw [LF_setEntry_self h hh]; exact hg
  have hfac : ∀ a b : ℕ, ‖((a.factorial * b.factorial : ℕ) : ℂ)‖⁻¹ ≤ 1 := by
    intro a b
    rw [Complex.norm_natCast]
    refine inv_le_one_of_one_le₀ ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero a)
      (Nat.factorial_ne_zero b))
  have htm : ∀ β α k a, a ≤ k → 2 ≤ k → k ≤ l →
      ‖tm β α a (k - a)‖ ≤ Kc * (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) / 2)) *
        ‖wirt a (k - a) (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α)‖ := by
    intro β α k a hak hk hkl
    simp only [htm]
    rw [norm_mul, norm_div]
    have e : a + (k - a + 1) = k + 1 := by omega
    have := hκ a (k - a + 1) β α (by omega) (by omega)
    rw [e] at this
    rw [div_eq_mul_inv]
    have h0 := norm_nonneg (wirt a (k - a) (fun w => LF_F θ Λ B T z₁ z₂ p β α
      (setEntry h β α w)) (h β α))
    calc ‖κ a (k - a + 1) β α‖ * ‖((a.factorial * (k - a).factorial : ℕ) : ℂ)‖⁻¹ *
          ‖wirt a (k - a) (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α)‖
        ≤ (Kc * (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) / 2))) * 1 *
          ‖wirt a (k - a) (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α)‖ := by
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
        (18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * z.im⁻¹ *
            Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) * c ^ (2 * p - 1) +
          2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) *
            (2 * (2 * p - 1) * c ^ (2 * p - 2) *
              ((D * N : ℝ) * Real.sqrt (2 * LF_SZ D N θ K Γ₀ z.im))) +
          (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2) *
            ((2 * LF_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))) := by
    have hN32 : 0 ≤ (N : ℝ) ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg hN0.le _
    have each : ∀ a ∈ Finset.range (2 + 1), ‖∑ β, ∑ α, tm β α a (2 - a)‖ ≤
        Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
          (18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * z.im⁻¹ *
              Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹))) * c ^ (2 * p - 1) +
            2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * z.im⁻¹))) *
              (2 * (2 * p - 1) * c ^ (2 * p - 2) *
                ((D * N : ℝ) * Real.sqrt (2 * LF_SZ D N θ K Γ₀ z.im))) +
            (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * z.im⁻¹ * (K * z.im⁻¹ * K) ^ 2) *
              ((2 * LF_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 * c ^ (2 * p - 1))) := by
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
        have hj := LF_jet_F θ hs hΓ₀ h hh β α (h β α) (hg' β α) l p hp β α a (k - a) (by omega)
        rw [LF_setEntry_self h hh, show a + (k - a) = k by omega] at hj
        have hj' : ‖wirt a (k - a) (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w))
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
private def LF_V {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) :
    Finset (Idx D N → ℂ) :=
  Finset.univ.image fun p : (Fin 7 ⊕ (Fin D ⊕ Fin D)) × Idx D N =>
    LF_Qf Λ B T z₂ p.1 *ᵥ Pi.single p.2 1

private lemma LF_V_mem {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z₂ : ℂ}
    {v : Idx D N → ℂ} : v ∈ LF_V Λ B T z₂ ↔ v ∈ LF_U Λ B T z₂ := by
  simp only [LF_V, Finset.mem_image, Finset.mem_univ, true_and, LF_U, Set.mem_range]

private lemma LF_e_V {D N : ℕ} (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z₂ : ℂ) (k : Idx D N) :
    (Pi.single k 1 : Idx D N → ℂ) ∈ LF_V Λ B T z₂ :=
  LF_V_mem.mpr (LF_e_U Λ B T z₂ k)

/-- The Hermitian part `h ↦ (h + hᴴ)/2` is smooth. -/
private lemma LF_contDiff_symArr {D N : ℕ} (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun h : Idx D N → Idx D N → ℂ => symArr h) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  simp only [symArr]
  exact ((contDiff_apply_apply ℝ k l).add
    (Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ l k))).div_const 2

/-- `x^* (Aᴴ y) = conj (y^* (A x))`. -/
private lemma LF_dot_conjT {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star x ⬝ᵥ (Aᴴ *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ (A *ᵥ x)) := by
  rw [LF_dot_adj, Matrix.conjTranspose_conjTranspose]
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The forms `x^* G(z) y`, `x, y ∈ V`, bounded by `Γ` at a Hermitian array give the good event
with constant `Γ` (the forms at `z̄` are their conjugates). -/
private lemma LF_good_of_forms {D N : ℕ} {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ : ℝ} {h : Idx D N → Idx D N → ℂ}
    (hh : (Matrix.of h).IsHermitian)
    (hf : ∀ x ∈ LF_V Λ B T z₂, ∀ y ∈ LF_V Λ B T z₂,
      ‖resFactorEval (x, y, Λ, z) h‖ ≤ Γ) :
    LF_good Λ z (LF_U Λ B T z₂) Γ h := by
  intro ζ hζ u hu v hv
  have hu' := LF_V_mem.mpr hu
  have hv' := LF_V_mem.mpr hv
  rcases hζ with rfl | rfl
  · exact hf u hu' v hv'
  · have hX := hh.add hs.herm
    rw [← LF_res_conjT _ hX z hs.hz.ne', LF_dot_conjT, Complex.norm_conj]
    exact hf v hv' u hu'

/-- The bound on `|Z|` at a point of the good event with constant `Γ₀ ≥ 1`. -/
private lemma LF_Z_good {D N : ℕ} (θ : ℝ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ}
    {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K) {Γ₀ : ℝ} (hΓ₀ : 1 ≤ Γ₀) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hg : LF_good Λ z (LF_U Λ B T z₂) Γ₀ h) :
    ‖LF_Z θ Λ B T z₁ z₂ h‖ ≤ LF_Cz D θ * (K * Γ₀) * (K ^ 2 * Γ₀ * (1 + z.im⁻¹)) := by
  rcases isEmpty_or_nonempty (Idx D N) with hE | ⟨⟨k⟩⟩
  · have e : LF_Z θ Λ B T z₁ z₂ h = 0 := by
      have hD : D = 0 ∨ N = 0 := by
        by_contra hc
        push_neg at hc
        exact hE.false (⟨0, Nat.pos_of_ne_zero hc.1⟩, ⟨0, Nat.pos_of_ne_zero hc.2⟩)
      unfold LF_Z
      rcases hD with rfl | rfl
      · simp
      · simp [ntr]
    rw [e, norm_zero]
    have := LF_Cz_nonneg D θ
    have : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hs.hz.le
    have : 0 ≤ K := by linarith [hs.hK]
    have : 0 ≤ Γ₀ := by linarith
    positivity
  unfold LF_Z LF_Cz
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  obtain ⟨v1, v2⟩ := LF_loop_vals hs hΓ₀ h hh hg k x t
  rw [norm_mul, norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact mul_le_mul v1 v2 (norm_nonneg _) (by nlinarith [hs.hK])

/-- The set of arrays where a form `x^* G(z) y`, `x, y ∈ V`, of the Hermitian part exceeds `Γ`
is open. -/
private lemma LF_bad_open {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
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
private lemma LF_young {x Q : ℝ} (hx : 0 ≤ x) (hQ : 0 ≤ Q) (p : ℕ) (hp : 1 ≤ p) :
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

/-- The bound of `LF_pw_all` as a function of `x = |Z|`. -/
private def LF_RB (D N : ℕ) (θ K Γ₀ η : ℝ) (p l : ℕ) (Kc x : ℝ) : ℝ :=
  ((D : ℝ) * N)⁻¹ * ((N : ℝ)⁻¹ *
    (2 * (2 * p - 1) * (x + LF_Pz D N θ K Γ₀ η) ^ (2 * p - 2) *
      (Real.sqrt ((D * N : ℝ) * Γ₀ * η⁻¹ * (K * η⁻¹ * K) ^ 2) *
        Real.sqrt (2 * LF_SZ D N θ K Γ₀ η))) +
    3 * Kc * (N : ℝ) ^ (-((3 : ℝ) / 2)) *
      (18 * ((D * N : ℝ) * (K ^ 4 * Γ₀ ^ 2 * η⁻¹ * Real.sqrt ((D * N : ℝ) * Γ₀ * η⁻¹))) *
          (x + LF_Pz D N θ K Γ₀ η) ^ (2 * p - 1) +
        2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * η⁻¹))) *
          (2 * (2 * p - 1) * (x + LF_Pz D N θ K Γ₀ η) ^ (2 * p - 2) *
            ((D * N : ℝ) * Real.sqrt (2 * LF_SZ D N θ K Γ₀ η))) +
        (D * N : ℝ) * Real.sqrt ((D * N : ℝ) * Γ₀ * η⁻¹ * (K * η⁻¹ * K) ^ 2) *
          ((2 * LF_Gt l K Γ₀) ^ 2 * ((2 * p - 1 : ℝ)) ^ 2 *
            (x + LF_Pz D N θ K Γ₀ η) ^ (2 * p - 1))) +
    ((l : ℝ) + 1) ^ 2 * Kc * (N : ℝ) ^ (-(2 : ℝ)) * (((D : ℝ) * N) ^ 2 *
      ((4 * p * LF_Gt l K Γ₀) ^ l * LF_Gs K Γ₀ η 2 *
        (x + LF_Pz D N θ K Γ₀ η) ^ (2 * p - 1))))

/-- `LF_RB` is nondecreasing in `x ≥ 0`. -/
private lemma LF_RB_mono {D N : ℕ} (θ : ℝ) {K Γ₀ η : ℝ} (hK : 0 ≤ K) (hΓ₀ : 0 ≤ Γ₀)
    (hη : 0 < η) (p l : ℕ) (hp : 1 ≤ p) {Kc : ℝ} (hKc : 0 ≤ Kc) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : LF_RB D N θ K Γ₀ η p l Kc x ≤ LF_RB D N θ K Γ₀ η p l Kc y := by
  have hPz := LF_Pz_nonneg (D := D) (N := N) θ hK hΓ₀ hη
  have hp' : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hi : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hGs : 0 ≤ LF_Gs K Γ₀ η 2 := by unfold LF_Gs; positivity
  have hGt : 0 ≤ LF_Gt l K Γ₀ := by unfold LF_Gt; positivity
  have hxP : x + LF_Pz D N θ K Γ₀ η ≤ y + LF_Pz D N θ K Γ₀ η := by linarith
  have hxP0 : 0 ≤ x + LF_Pz D N θ K Γ₀ η := by linarith
  have m1 := pow_le_pow_left₀ hxP0 hxP (2 * p - 1)
  have m2 := pow_le_pow_left₀ hxP0 hxP (2 * p - 2)
  unfold LF_RB
  have hN32 : 0 ≤ (N : ℝ) ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN2 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  gcongr

/-- `w (w^{p-1} w̄^p) = |w|^{2p}`. -/
private lemma LF_zphi (w : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    w * (w ^ (p - 1) * starRingEnd ℂ w ^ p) = ((‖w‖ ^ (2 * p) : ℝ) : ℂ) := by
  have e : w * (w ^ (p - 1) * starRingEnd ℂ w ^ p) = (w * starRingEnd ℂ w) ^ p := by
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hp]
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
  push_cast
  ring

/-- The moment bound: with the expansion of each `E X_{βα} Φ h̄_{βα}` to order `l` up to `ρ`,
the bad event of the forms of probability `≤ ε₀`, and the bound of `LF_pw_all` on the good event
dominated by `Q (x + Q)^{2p-1} + Q² (x + Q)^{2p-2}`, Young's inequality gives
`E|Z|^{2p} ≤ 2 (C_p Q^{2p} + ε₀ R_c + DN ρ)`. -/
private lemma LF_mom {D N : ℕ} [NeZero D] [NeZero N] {C : ℕ → ℝ} (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ)
    {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ} (hs : LF_Set Λ B T z z₁ z₂ K)
    (hZd : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      LF_Z θ Λ B T z₁ z₂ h = ((D : ℂ) * N)⁻¹ *
        (∑ β, ∑ α, LF_X Λ B T z₁ z₂ h β α * starRingEnd ℂ (h β α)) + LF_C θ Λ B T z₁ z₂ h)
    (p l : ℕ) (hp : 1 ≤ p) (hl : 2 ≤ l) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hcc : ∀ a b β α, 3 ≤ a + b → a + b ≤ l + 1 →
      ‖ccum (μ.map fun h => h β α) a b‖ ≤ Kc * (N : ℝ) ^ (-(((a + b : ℕ) : ℝ) / 2)))
    (ρ : ℝ) (hexp : ∀ β α, ‖(∫ h, LF_F θ Λ B T z₁ z₂ p β α h * starRingEnd ℂ (h β α) ∂μ) -
        ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
          ccum (μ.map fun h => h β α) a (b + 1) / ((a.factorial * b.factorial : ℕ) : ℂ) *
            ∫ h, wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α) ∂μ‖ ≤
        ρ)
    (Γ ε₀ Q : ℝ) (hΓ : 1 ≤ Γ) (hε₀ : 0 ≤ ε₀) (hQ : 0 ≤ Q)
    (hbad : μ {h | ∃ x ∈ LF_V Λ B T z₂, ∃ y ∈ LF_V Λ B T z₂,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} ≤ ENNReal.ofReal ε₀)
    (hRB : ∀ x, 0 ≤ x → LF_RB D N θ K Γ z.im p l Kc x ≤
      Q * (x + Q) ^ (2 * p - 1) + Q ^ 2 * (x + Q) ^ (2 * p - 2)) :
    ∫ h, ‖LF_Z θ Λ B T z₁ z₂ h‖ ^ (2 * p) ∂μ ≤
      2 * (2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p) +
        ε₀ * LF_RB D N θ K (LF_Gc0 K z.im) z.im p l Kc (LF_Zc D θ K z.im) +
          (D * N : ℝ) * ρ) := by
  have hprob := hμ.prob
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  set Zf : (Idx D N → Idx D N → ℂ) → ℂ := fun h => LF_Z θ Λ B T z₁ z₂ h with hZf
  set Φf : (Idx D N → Idx D N → ℂ) → ℂ := fun h => Zf h ^ (p - 1) * starRingEnd ℂ (Zf h) ^ p
    with hΦf
  set Zc := LF_Zc D θ K z.im with hZc
  -- measurability and bounds
  have hZm : AEStronglyMeasurable Zf μ :=
    LF_aesm_sym hμ.herm (LF_cd_Z θ hs.herm B T hz₁ hz₂ 0).continuous
  have hZb : ∀ᵐ h ∂μ, ‖Zf h‖ ≤ Zc := by
    filter_upwards [hμ.herm] with h hh
    exact LF_Z_crude θ hs h hh
  have hZc0 : 0 ≤ Zc := by
    obtain ⟨h, hh⟩ := hμ.herm.exists
    exact (norm_nonneg _).trans (LF_Z_crude θ hs h hh)
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
  have hZΦ : ∀ h, Zf h * Φf h = ((‖Zf h‖ ^ (2 * p) : ℝ) : ℂ) := fun h => LF_zphi (Zf h) p hp
  have hYc : ((∫ h, ‖Zf h‖ ^ (2 * p) ∂μ : ℝ) : ℂ) = ∫ h, Zf h * Φf h ∂μ := by
    simp only [hZΦ]
    exact integral_complex_ofReal.symm
  have hZΦi : Integrable (fun h => Zf h * Φf h) μ := by
    simp only [hZΦ]
    exact hY.ofReal
  -- the terms `X_{βα} Φ h̄_{βα}`
  have hFi : ∀ β α, Integrable (fun h => LF_F θ Λ B T z₁ z₂ p β α h *
      starRingEnd ℂ (h β α)) μ := by
    intro β α
    have hm : AEStronglyMeasurable (fun h => LF_F θ Λ B T z₁ z₂ p β α h) μ :=
      LF_aesm_sym hμ.herm (LF_cd_F θ hs.herm B T hz₁ hz₂ p β α 0).continuous
    have hb : ∀ᵐ h ∂μ, ‖LF_F θ Λ B T z₁ z₂ p β α h‖ ≤ LF_Bc D N θ 0 p K z.im := by
      filter_upwards [hμ.herm] with h hh
      have := LF_F_crude θ hs h hh β α (h β α) 0 p hp β α 0 0 le_rfl
      simp only [wirt, Function.iterate_zero, id, LF_setEntry_self h hh] at this
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
    ∑ β, ∑ α, LF_F θ Λ B T z₁ z₂ p β α h * starRingEnd ℂ (h β α) with hG
  have hGi : Integrable G μ :=
    (integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun α _ => hFi β α).const_mul _
  have hCe : ∀ᵐ h ∂μ, Zf h * Φf h - G h = LF_C θ Λ B T z₁ z₂ h * Φf h := by
    filter_upwards [hμ.herm] with h hh
    simp only [hZf, hG]
    rw [hZd h hh]
    simp only [LF_F, Finset.mul_sum, Finset.sum_mul, add_mul]
    have : ∀ β α, ((D : ℂ) * N)⁻¹ * (LF_X Λ B T z₁ z₂ h β α * starRingEnd ℂ (h β α)) *
        Φf h = ((D : ℂ) * N)⁻¹ * (LF_X Λ B T z₁ z₂ h β α *
          (LF_Z θ Λ B T z₁ z₂ h ^ (p - 1) * starRingEnd ℂ (LF_Z θ Λ B T z₁ z₂ h) ^ p) *
            starRingEnd ℂ (h β α)) := fun β α => by
      simp only [hΦf, hZf]; ring
    simp only [this]
    ring
  have hCi : Integrable (fun h => LF_C θ Λ B T z₁ z₂ h * Φf h) μ :=
    (hZΦi.sub hGi).congr hCe
  -- the integrands of the expansion
  set κ : ℕ → ℕ → Idx D N → Idx D N → ℂ := fun a b β α => ccum (μ.map fun h => h β α) a b
    with hκ
  have hWi : ∀ β α a b, Integrable (fun h => wirt a b
      (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α)) μ := fun β α a b =>
    LF_int_wirt θ hμ hs p hp β α β α a b
  have hESi : Integrable (fun h => LF_ES θ Λ B T z₁ z₂ p l κ h) μ := by
    unfold LF_ES
    exact integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        (hWi β α a b).const_mul _
  have hESint : ∫ h, LF_ES θ Λ B T z₁ z₂ p l κ h ∂μ =
      ∑ β, ∑ α, ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
        κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
          ∫ h, wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α) ∂μ := by
    unfold LF_ES
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
    (∫ h, LF_F θ Λ B T z₁ z₂ p β α h * starRingEnd ℂ (h β α) ∂μ) -
      ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
        κ a (b + 1) β α / ((a.factorial * b.factorial : ℕ) : ℂ) *
          ∫ h, wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α) ∂μ
    with hr
  have hdec : ∫ h, Zf h * Φf h ∂μ =
      (∫ h, (((D : ℂ) * N)⁻¹ * LF_ES θ Λ B T z₁ z₂ p l κ h +
        LF_C θ Λ B T z₁ z₂ h * Φf h) ∂μ) + ((D : ℂ) * N)⁻¹ * ∑ β, ∑ α, r β α := by
    have e1 : ∫ h, Zf h * Φf h ∂μ = (∫ h, G h ∂μ) + ∫ h, LF_C θ Λ B T z₁ z₂ h * Φf h ∂μ := by
      rw [← integral_congr_ae hCe, integral_sub hZΦi hGi]
      ring
    have e2 : ∫ h, G h ∂μ = ((D : ℂ) * N)⁻¹ *
        ∑ β, ∑ α, ∫ h, LF_F θ Λ B T z₁ z₂ p β α h * starRingEnd ℂ (h β α) ∂μ := by
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
  set S : Set (Idx D N → Idx D N → ℂ) := {h | ∃ x ∈ LF_V Λ B T z₂, ∃ y ∈ LF_V Λ B T z₂,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} with hS
  have hSm : MeasurableSet S := (LF_bad_open hs.herm hs.hz.ne' _ Γ).measurableSet
  set Rc := LF_RB D N θ K (LF_Gc0 K z.im) z.im p l Kc Zc with hRc
  have h01 : ∀ β α, κ 0 1 β α = 0 := fun β α => LF_ccum01 hμ β α
  have h11 : ∀ β α, κ 1 1 β α = varProf D N θ β α := fun β α =>
    (llClass_ccum_low D N C θ μ hμ β α).2.1
  have h02 : ∀ β α, κ 0 2 β α = if β = α then (varProf D N θ β α : ℂ) else 0 := fun β α =>
    (llClass_ccum_low D N C θ μ hμ β α).2.2.2
  have hpw : ∀ᵐ h ∂μ, ‖((D : ℂ) * N)⁻¹ * LF_ES θ Λ B T z₁ z₂ p l κ h +
      LF_C θ Λ B T z₁ z₂ h * Φf h‖ ≤
      (Q * (‖Zf h‖ + Q) ^ (2 * p - 1) + Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2)) +
        S.indicator (fun _ => Rc) h := by
    filter_upwards [hμ.herm] with h hh
    have hg0 : 0 ≤ Q * (‖Zf h‖ + Q) ^ (2 * p - 1) + Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2) := by
      positivity
    by_cases hb : h ∈ S
    · rw [Set.indicator_of_mem hb]
      have hΓc := LF_Gc0_ge hs.hK hs.hz
      have hp1 := LF_pw_all θ hθ0 hθ1 hs hΓc h hh (LF_good_crude hs h hh) p l hp hl κ Kc hKc
        h01 h11 h02 (fun a b β α hab hab' => hcc a b β α hab hab')
      have hm := LF_RB_mono (D := D) (N := N) θ (Γ₀ := LF_Gc0 K z.im) hK0 (by linarith) hs.hz
        p l hp hKc
        (norm_nonneg (Zf h)) (LF_Z_crude θ hs h hh)
      have : ‖((D : ℂ) * N)⁻¹ * LF_ES θ Λ B T z₁ z₂ p l κ h +
          LF_C θ Λ B T z₁ z₂ h * Φf h‖ ≤ Rc := hp1.trans hm
      linarith
    · rw [Set.indicator_of_notMem hb, add_zero]
      have hf : ∀ x ∈ LF_V Λ B T z₂, ∀ y ∈ LF_V Λ B T z₂,
          ‖resFactorEval (x, y, Λ, z) h‖ ≤ Γ := by
        intro x hx y hy
        by_contra hc
        push_neg at hc
        exact hb ⟨x, hx, y, hy, by rwa [symArr_of_isHermitian h hh]⟩
      have hp1 := LF_pw_all θ hθ0 hθ1 hs hΓ h hh (LF_good_of_forms hs hh hf) p l hp hl κ Kc
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
    have := LF_pw_all θ hθ0 hθ1 hs (LF_Gc0_ge hs.hK hs.hz) h hh (LF_good_crude hs h hh) p l hp
      hl κ Kc hKc h01 h11 h02 (fun a b β α hab hab' => hcc a b β α hab hab')
    exact (norm_nonneg _).trans (this.trans (LF_RB_mono (D := D) (N := N) θ hK0
      (by linarith [LF_Gc0_ge hs.hK hs.hz]) hs.hz p l hp hKc (norm_nonneg _)
      (LF_Z_crude θ hs h hh)))
  have hint1 : ‖∫ h, (((D : ℂ) * N)⁻¹ * LF_ES θ Λ B T z₁ z₂ p l κ h +
      LF_C θ Λ B T z₁ z₂ h * Φf h) ∂μ‖ ≤
      (∫ h, ‖Zf h‖ ^ (2 * p) ∂μ) / 2 + 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p) +
        ε₀ * Rc := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_ae ((hESi.const_mul _).add hCi).norm (hgi.add hIi) hpw).trans ?_
    rw [integral_add' hgi hIi, integral_indicator_const _ hSm, smul_eq_mul]
    have hy : ∫ h, (Q * (‖Zf h‖ + Q) ^ (2 * p - 1) + Q ^ 2 * (‖Zf h‖ + Q) ^ (2 * p - 2)) ∂μ ≤
        ∫ h, (‖Zf h‖ ^ (2 * p) / 2 + 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) * Q ^ (2 * p)) ∂μ :=
      integral_mono hgi ((hY.div_const 2).add (integrable_const _)) fun h =>
        LF_young (norm_nonneg _) hQ p hp
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

/-- The bound `(4pΓ_t)^{l+1} Γ₂ (|Z| + Ψ_Z)^{2p-1}` at `Γ₀ = 6Γ` on the derivatives of order
`l + 1` of the integrand where the cutoff of level `Γ` is nonzero. -/
private def LF_Ag (D N : ℕ) (θ : ℝ) (p l : ℕ) (K Γ η : ℝ) : ℝ :=
  (4 * p * LF_Gt (l + 1) K (6 * Γ)) ^ (l + 1) * LF_Gs K (6 * Γ) η 2 *
    (LF_Cz D θ * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (1 + η⁻¹)) + LF_Pz D N θ K (6 * Γ) η) ^
      (2 * p - 1)

/-- The expansion of `E X_{βα} Φ h̄_{βα}` to order `l` (Lemma 2.11 [lem:complex_cumu], (2.26)
[5.16]) with the cutoff of the forms of `V` at level `Γ`: the remainder is
`K_e (N^{-(l+2)/2} A + B_c (ε₀ + (K_k + 1)(N^{1/2} M)^{-k})^{1/2})`. -/
private lemma LF_rem (l k : ℕ) (C : ℕ → ℝ) : ∃ Ke Kk : ℝ, 0 ≤ Ke ∧ 0 ≤ Kk ∧
    ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)), LLClass D N C θ μ →
    ∀ (Λ B T : Matrix (Idx D N) (Idx D N) ℂ) (z z₁ z₂ : ℂ) (K : ℝ), LF_Set Λ B T z z₁ z₂ K →
    ∀ p : ℕ, 1 ≤ p → ∀ Γ M ε₀ : ℝ, 1 ≤ Γ → 0 < M → 24 * M * Γ ≤ 1 → 0 ≤ ε₀ →
    μ {h | ∃ x ∈ LF_V Λ B T z₂, ∃ y ∈ LF_V Λ B T z₂,
      Γ < ‖resFactorEval (x, y, Λ, z) (symArr h)‖} ≤ ENNReal.ofReal ε₀ →
    ∀ β α : Idx D N, ‖(∫ h, LF_F θ Λ B T z₁ z₂ p β α h * starRingEnd ℂ (h β α) ∂μ) -
        ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1 - a),
          ccum (μ.map fun h => h β α) a (b + 1) / ((a.factorial * b.factorial : ℕ) : ℂ) *
            ∫ h, wirt a b (fun w => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w)) (h β α) ∂μ‖ ≤
      Ke * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * LF_Ag D N θ p l K Γ z.im +
        LF_Bc D N θ (l + 1) p K z.im *
          Real.sqrt (ε₀ + Kk * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
            ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)))) := by
  obtain ⟨Ke, hKe0, hKe⟩ := expansion_hp_gen l k C
  obtain ⟨Kk, hKk0, hKk⟩ := hpCut_ne_one_le k C
  refine ⟨Ke, Kk, hKe0, hKk0, ?_⟩
  intro D N θ μ hμ Λ B T z z₁ z₂ K hs p hp Γ M ε₀ hΓ hM hMΓ hε₀ hbad β α
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  have hK0 : 0 ≤ K := by linarith [hs.hK]
  set Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ) := {(Λ, z)} with hΞ
  have hΞp : ∀ q ∈ Ξ, q.1.IsHermitian ∧ 0 < q.2.im := by
    intro q hq
    rw [hΞ, Finset.mem_singleton] at hq
    subst hq
    exact ⟨hs.herm, hs.hz⟩
  have hΞne : ∀ q ∈ Ξ, q.1.IsHermitian ∧ q.2.im ≠ 0 := fun q hq =>
    ⟨(hΞp q hq).1, (hΞp q hq).2.ne'⟩
  set V := LF_V Λ B T z₂ with hV
  have hbad' : μ {h | ∃ q ∈ Ξ, ∃ x ∈ V, ∃ y ∈ V,
      Γ < ‖resFactorEval (x, y, q.1, q.2) (symArr h)‖} ≤ ENNReal.ofReal ε₀ := by
    refine le_trans (measure_mono ?_) hbad
    rintro h ⟨q, hq, x, hx, y, hy, hlt⟩
    rw [hΞ, Finset.mem_singleton] at hq
    subst hq
    exact ⟨x, hx, y, hy, hlt⟩
  have hMΓ' : 4 * M * Γ ≤ 1 / 2 := by nlinarith
  have hχ := hKk D N θ μ hμ Ξ hΞp β α V (LF_e_V Λ B T z₂ β) (LF_e_V Λ B T z₂ α) Γ M ε₀ hM
    hMΓ' hε₀ hbad'
  have h6 : 1 ≤ 6 * Γ := by linarith
  have hPz6 := LF_Pz_nonneg (D := D) (N := N) θ hK0 (by linarith : (0 : ℝ) ≤ 6 * Γ) hs.hz
  have hGs6 : 0 ≤ LF_Gs K (6 * Γ) z.im 2 := by
    unfold LF_Gs; have := inv_nonneg.mpr hs.hz.le; have : (0 : ℝ) ≤ 6 * Γ := by linarith
    positivity
  have hGt6 : 0 ≤ LF_Gt (l + 1) K (6 * Γ) := by
    unfold LF_Gt; have : (0 : ℝ) ≤ 6 * Γ := by linarith
    positivity
  have hA0 : 0 ≤ LF_Ag D N θ p l K Γ z.im := by
    unfold LF_Ag
    have := LF_Cz_nonneg D θ
    have := inv_nonneg.mpr hs.hz.le
    have : (0 : ℝ) ≤ 6 * Γ := by linarith
    positivity
  have hA : ∀ a b : ℕ, a + b = l + 1 → ∀ h : Idx D N → Idx D N → ℂ,
      (Matrix.of h).IsHermitian → hpCut Ξ V Γ β α h ≠ 0 → ∀ w : ℂ, ‖w‖ ≤ M →
      ‖wirt a b (fun w' => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w')) w‖ ≤
        LF_Ag D N θ p l K Γ z.im := by
    intro a b hab h hh hc w hw
    have hf := hpCut_ne_zero_le Ξ hΞp h hh β α V (LF_e_V Λ B T z₂ β) (LF_e_V Λ B T z₂ α) M Γ
      (by linarith) hMΓ hc w hw
    have hh' := LF_slice_herm h hh β α w
    have hg : LF_good Λ z (LF_U Λ B T z₂) (6 * Γ) (setEntry h β α w) :=
      LF_good_of_forms hs hh' fun x hx y hy => hf (Λ, z) (Finset.mem_singleton_self _) x hx y hy
    have hj := LF_jet_F θ hs h6 h hh β α w hg (l + 1) p hp β α a b hab.le
    rw [hab] at hj
    refine hj.trans ?_
    have hZ := LF_Z_good θ hs h6 _ hh' hg
    unfold LF_Ag
    gcongr
  have hB : ∀ a b : ℕ, a + b ≤ l + 1 → ∀ h : Idx D N → Idx D N → ℂ,
      (Matrix.of h).IsHermitian → ∀ w : ℂ,
      ‖wirt a b (fun w' => LF_F θ Λ B T z₁ z₂ p β α (setEntry h β α w')) w‖ ≤
        LF_Bc D N θ (l + 1) p K z.im := fun a b hab h hh w =>
    LF_F_crude θ hs h hh β α w (l + 1) p hp β α a b hab
  have hσ : 0 ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hM.le) _
  exact hKe D N θ μ hμ β α (LF_F θ Λ B T z₁ z₂ p β α) (hpCut Ξ V Γ β α) M
    (LF_Ag D N θ p l K Γ z.im) (LF_Bc D N θ (l + 1) p K z.im)
    (ε₀ + Kk * ((N : ℝ) ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)))
    (LF_cd_F θ hs.herm B T hz₁ hz₂ p β α (l + 1))
    ((hpCut_contDiff Ξ hΞne V Γ β α (l + 1)).comp (LF_contDiff_symArr _))
    (hpCut_mem_Icc Ξ V Γ β α) (hpCut_setEntry Ξ V Γ β α) hM hA0
    (by positivity) hA hB hχ

/-! ### The bounds in the scale `Ψ = N⁻¹ η⁻²` -/

/-- `i^a ≤ E^{b-a} i^b` for `a ≤ b` when `1 ≤ E i`. -/
private lemma LF_ipow {i E : ℝ} (hi : 0 ≤ i) (hE : 1 ≤ E * i) {a b : ℕ} (hab : a ≤ b) :
    i ^ a ≤ E ^ (b - a) * i ^ b := by
  calc i ^ a = i ^ a * 1 := (mul_one _).symm
    _ ≤ i ^ a * (E * i) ^ (b - a) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hE) (pow_nonneg hi _)
    _ = E ^ (b - a) * i ^ b := by
        rw [mul_pow, show i ^ b = i ^ a * i ^ (b - a) by rw [← pow_add, Nat.add_sub_cancel' hab]]
        ring

/-- `N^{-3/2} √y = √(N⁻³ y)`. -/
private lemma LF_rpow32 {n : ℝ} (hn : 0 ≤ n) {y : ℝ} :
    n ^ (-((3 : ℝ) / 2)) * Real.sqrt y = Real.sqrt ((n ^ 3)⁻¹ * y) := by
  rw [Real.sqrt_mul (inv_nonneg.mpr (pow_nonneg hn 3))]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.inv_rpow (pow_nonneg hn 3), ← Real.rpow_natCast,
    ← Real.rpow_mul hn, ← Real.rpow_neg hn]
  norm_num

/-- `N^{-2} = (N²)⁻¹`. -/
private lemma LF_rpow2 {n : ℝ} (hn : 0 ≤ n) : n ^ (-(2 : ℝ)) = (n ^ 2)⁻¹ := by
  rw [Real.rpow_neg hn, Real.rpow_two]

/-- The constant of the bound `S_Z ≤ C_s Γ₀³ (DN)⁻¹ η⁻⁵`. -/
private def LF_Cs (D : ℕ) (Cz2 K E₀ : ℝ) : ℝ :=
  12 * D * Cz2 * (2 * K ^ 6 * (1 + E₀) ^ 2 + 8 * K ^ 2 * (K ^ 2 * (1 + E₀) ^ 2 + K ^ 4))

private lemma LF_Cs_nonneg (D : ℕ) {Cz2 K E₀ : ℝ} (hC : 0 ≤ Cz2) : 0 ≤ LF_Cs D Cz2 K E₀ := by
  unfold LF_Cs; positivity

/-- `S_Z ≤ C_s Γ₀³ (DN)⁻¹ η⁻⁵` for `η ≤ E₀`. -/
private lemma LF_SZ_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K Γ₀ η E₀ Cz2 : ℝ}
    (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (hηE : η ≤ E₀) (hC : LF_Cz2 D θ ≤ Cz2) :
    LF_SZ D N θ K Γ₀ η ≤ LF_Cs D Cz2 K E₀ * Γ₀ ^ 3 * ((D : ℝ) * N)⁻¹ * (η⁻¹) ^ 5 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hd : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  set i := η⁻¹ with hi
  have hi0 : 0 < i := inv_pos.mpr hη
  have hEi : 1 ≤ (1 + E₀) * i := by
    have : η * i = 1 := mul_inv_cancel₀ hη.ne'
    nlinarith
  have hE0 : 0 ≤ 1 + E₀ := by linarith
  set u := ((D : ℝ) * N)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hdu : u ^ 2 * ((D : ℝ) * N) = u := by rw [hu]; field_simp
  have hC0 : 0 ≤ LF_Cz2 D θ := by
    unfold LF_Cz2; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have e : LF_SZ D N θ K Γ₀ η = 12 * D * LF_Cz2 D θ * (2 * K ^ 6 * Γ₀ ^ 3 * u * ((1 + i) ^ 2 *
      i ^ 3) + 8 * K ^ 2 * Γ₀ ^ 3 * u * (K ^ 2 * i ^ 3 + K ^ 4 * i ^ 5)) := by
    unfold LF_SZ
    rw [← hu, ← hi]
    linear_combination (12 * D * LF_Cz2 D θ * (2 * K ^ 6 * Γ₀ ^ 3 * ((1 + i) ^ 2 * i ^ 3) +
      8 * K ^ 2 * Γ₀ ^ 3 * (K ^ 2 * i ^ 3 + K ^ 4 * i ^ 5))) * hdu
  rw [e]
  have b1 : (1 + i) ^ 2 * i ^ 3 ≤ (1 + E₀) ^ 2 * i ^ 5 := by
    have hE1 : 1 ≤ E₀ * i := by
      have h1 := mul_le_mul_of_nonneg_right hηE hi0.le
      have h2 : η * i = 1 := mul_inv_cancel₀ hη.ne'
      linarith
    have : 1 + i ≤ (1 + E₀) * i := by linarith
    calc (1 + i) ^ 2 * i ^ 3 ≤ ((1 + E₀) * i) ^ 2 * i ^ 3 := by gcongr
      _ = (1 + E₀) ^ 2 * i ^ 5 := by ring
  have b2 : i ^ 3 ≤ (1 + E₀) ^ 2 * i ^ 5 := by
    have := LF_ipow hi0.le hEi (show 3 ≤ 5 by norm_num)
    simpa using this
  have hA : 2 * K ^ 6 * Γ₀ ^ 3 * u * ((1 + i) ^ 2 * i ^ 3) + 8 * K ^ 2 * Γ₀ ^ 3 * u *
      (K ^ 2 * i ^ 3 + K ^ 4 * i ^ 5) ≤ (2 * K ^ 6 * (1 + E₀) ^ 2 + 8 * K ^ 2 *
        (K ^ 2 * (1 + E₀) ^ 2 + K ^ 4)) * Γ₀ ^ 3 * u * i ^ 5 := by
    have h1 : 0 ≤ 2 * K ^ 6 * Γ₀ ^ 3 * u := by positivity
    have h2 : 0 ≤ 8 * K ^ 2 * Γ₀ ^ 3 * u := by positivity
    have h3 : K ^ 2 * i ^ 3 + K ^ 4 * i ^ 5 ≤ (K ^ 2 * (1 + E₀) ^ 2 + K ^ 4) * i ^ 5 := by
      have : K ^ 2 * i ^ 3 ≤ K ^ 2 * ((1 + E₀) ^ 2 * i ^ 5) :=
        mul_le_mul_of_nonneg_left b2 (by positivity)
      nlinarith
    have := mul_le_mul_of_nonneg_left b1 h1
    have := mul_le_mul_of_nonneg_left h3 h2
    nlinarith
  have hA0 : 0 ≤ 2 * K ^ 6 * Γ₀ ^ 3 * u * ((1 + i) ^ 2 * i ^ 3) + 8 * K ^ 2 * Γ₀ ^ 3 * u *
      (K ^ 2 * i ^ 3 + K ^ 4 * i ^ 5) := by positivity
  unfold LF_Cs
  calc 12 * (D : ℝ) * LF_Cz2 D θ * (2 * K ^ 6 * Γ₀ ^ 3 * u * ((1 + i) ^ 2 * i ^ 3) +
        8 * K ^ 2 * Γ₀ ^ 3 * u * (K ^ 2 * i ^ 3 + K ^ 4 * i ^ 5))
      ≤ 12 * (D : ℝ) * Cz2 * ((2 * K ^ 6 * (1 + E₀) ^ 2 + 8 * K ^ 2 *
          (K ^ 2 * (1 + E₀) ^ 2 + K ^ 4)) * Γ₀ ^ 3 * u * i ^ 5) := by
        have : 12 * (D : ℝ) * LF_Cz2 D θ ≤ 12 * D * Cz2 := by
          have := hd.le; nlinarith
        exact mul_le_mul this hA hA0 (by nlinarith)
    _ = _ := by ring

/-- `Ψ_Z ≤ 3 C_z K³ (1 + E₀) Γ₀ N⁻¹ η⁻²` for `N⁻¹ ≤ η ≤ E₀`. -/
private lemma LF_Pz_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K Γ₀ η E₀ Cz : ℝ}
    (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (hηE : η ≤ E₀) (hNη : (N : ℝ)⁻¹ ≤ η)
    (hC : LF_Cz D θ ≤ Cz) :
    LF_Pz D N θ K Γ₀ η ≤ 3 * Cz * K ^ 3 * (1 + E₀) * Γ₀ * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  set i := η⁻¹ with hi
  have hi0 : 0 < i := inv_pos.mpr hη
  have hηi : η * i = 1 := mul_inv_cancel₀ hη.ne'
  have hEi : 1 ≤ (1 + E₀) * i := by nlinarith
  have hni : (N : ℝ)⁻¹ * i ≤ 1 := by nlinarith
  set m := (N : ℝ)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.mpr hn
  set u := ((D : ℝ) * N)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hum : u ≤ m := by
    rw [hu, hm, mul_inv]
    exact mul_le_of_le_one_left hm0.le (inv_le_one_of_one_le₀ hd1)
  have hCz0 : 0 ≤ LF_Cz D θ := LF_Cz_nonneg D θ
  have hK0 : 0 ≤ K := by linarith
  have hii : i + i ^ 2 ≤ (1 + E₀) * i ^ 2 := by nlinarith
  have hii' : i * (1 + i) ≤ (1 + E₀) * i ^ 2 := by nlinarith
  have t1 : K * Γ₀ * (K ^ 2 * (u * (i + i ^ 2))) ≤ K ^ 3 * (1 + E₀) * Γ₀ * (m * i ^ 2) := by
    have : u * (i + i ^ 2) ≤ m * ((1 + E₀) * i ^ 2) :=
      mul_le_mul hum hii (by positivity) hm0.le
    calc K * Γ₀ * (K ^ 2 * (u * (i + i ^ 2))) ≤ K * Γ₀ * (K ^ 2 * (m * ((1 + E₀) * i ^ 2))) := by
          gcongr
      _ = _ := by ring
  have t2 : K * (u * i) * (K ^ 2 * Γ₀ * (1 + i)) ≤ K ^ 3 * (1 + E₀) * Γ₀ * (m * i ^ 2) := by
    have : u * (i * (1 + i)) ≤ m * ((1 + E₀) * i ^ 2) :=
      mul_le_mul hum hii' (by positivity) hm0.le
    calc K * (u * i) * (K ^ 2 * Γ₀ * (1 + i)) = K ^ 3 * Γ₀ * (u * (i * (1 + i))) := by ring
      _ ≤ K ^ 3 * Γ₀ * (m * ((1 + E₀) * i ^ 2)) := by gcongr
      _ = _ := by ring
  have t3 : K * (u * i) * (K ^ 2 * (u * (i + i ^ 2))) ≤ K ^ 3 * (1 + E₀) * Γ₀ * (m * i ^ 2) := by
    have hu1 : u * i ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hum hi0.le) hni
    have : u * i * (u * (i + i ^ 2)) ≤ 1 * (m * ((1 + E₀) * i ^ 2)) :=
      mul_le_mul hu1 (mul_le_mul hum hii (by positivity) hm0.le) (by positivity) zero_le_one
    have hΓ' : (1 + E₀) * (m * i ^ 2) ≤ (1 + E₀) * Γ₀ * (m * i ^ 2) := by
      have : 0 ≤ (1 + E₀) * (m * i ^ 2) := by nlinarith [sq_nonneg i]
      nlinarith
    calc K * (u * i) * (K ^ 2 * (u * (i + i ^ 2))) = K ^ 3 * (u * i * (u * (i + i ^ 2))) := by
          ring
      _ ≤ K ^ 3 * (1 * (m * ((1 + E₀) * i ^ 2))) := by gcongr
      _ ≤ _ := by nlinarith [pow_nonneg hK0 3]
  have hs0 : 0 ≤ K * Γ₀ * (K ^ 2 * (u * (i + i ^ 2))) + K * (u * i) * (K ^ 2 * Γ₀ * (1 + i)) +
      K * (u * i) * (K ^ 2 * (u * (i + i ^ 2))) := by positivity
  unfold LF_Pz
  rw [← hu, ← hi]
  calc LF_Cz D θ * (K * Γ₀ * (K ^ 2 * (u * (i + i ^ 2))) + K * (u * i) * (K ^ 2 * Γ₀ * (1 + i)) +
        K * (u * i) * (K ^ 2 * (u * (i + i ^ 2))))
      ≤ Cz * (3 * (K ^ 3 * (1 + E₀) * Γ₀ * (m * i ^ 2))) :=
        mul_le_mul hC (by linarith) hs0 (hCz0.trans hC)
    _ = _ := by ring

/-- `i^a ≤ E^c i^b` for `a ≤ b`, `b - a ≤ c` when `1 ≤ E` and `1 ≤ E i`. -/
private lemma LF_ipow' {i E : ℝ} (hi : 0 ≤ i) (hE1 : 1 ≤ E) (hE : 1 ≤ E * i) {a b c : ℕ}
    (hab : a ≤ b) (hc : b - a ≤ c) : i ^ a ≤ E ^ c * i ^ b :=
  (LF_ipow hi hE hab).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hE1 hc)
    (pow_nonneg hi _))

private lemma LF_le_sq1 {t : ℝ} (ht : 0 ≤ t) : t ≤ (1 + t) ^ 2 := by nlinarith

/-- The constant `K_q` of the scale `Q = K_q Γ₀^{l+4} N⁻¹ η⁻²` of the terms of order `≤ l`. -/
private def LF_Kq (D : ℕ) (p l : ℕ) (Kc Cz Cz2 K E₀ : ℝ) : ℝ :=
  54 * Kc * K ^ 4 * D * (1 + E₀) +
    12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) +
    ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀) +
    (2 * (2 * p - 1) * (1 + 2 * LF_Cs D Cz2 K E₀ * K ^ 4) +
      72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * LF_Cs D Cz2 K E₀) * (1 + E₀)) +
    3 * Cz * K ^ 3 * (1 + E₀) + 1

set_option maxHeartbeats 1000000 in
/-- The bound of `LF_pw_all` in the scale `Ψ = N⁻¹ η⁻²`: for `N⁻¹ ≤ η ≤ E₀` and
`Q = K_q Γ₀^{l+4} Ψ`, `LF_RB(x) ≤ Q (x + Q)^{2p-1} + Q² (x + Q)^{2p-2}`. -/
private lemma LF_RB_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K Γ₀ η E₀ Cz Cz2 Kc : ℝ}
    (p l : ℕ) (hp : 1 ≤ p) (hK : 1 ≤ K) (hΓ : 1 ≤ Γ₀) (hη : 0 < η) (hηE : η ≤ E₀)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hKc : 0 ≤ Kc) (hCz : LF_Cz D θ ≤ Cz) (hCz2 : LF_Cz2 D θ ≤ Cz2)
    (x : ℝ) (hx : 0 ≤ x) :
    LF_RB D N θ K Γ₀ η p l Kc x ≤
      (LF_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2)) *
          (x + LF_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2)) ^ (2 * p - 1) +
        (LF_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2)) ^ 2 *
          (x + LF_Kq D p l Kc Cz Cz2 K E₀ * Γ₀ ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2)) ^
            (2 * p - 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hd : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ₀ := by linarith
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hCz0 : 0 ≤ Cz := (LF_Cz_nonneg D θ).trans hCz
  have hCz20 : 0 ≤ Cz2 := by
    refine le_trans ?_ hCz2
    unfold LF_Cz2; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
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
  set Cs := LF_Cs D Cz2 K E₀ with hCs
  have hCs0 : 0 ≤ Cs := LF_Cs_nonneg D hCz20
  set Ψ := m * i ^ 2 with hΨ
  have hΨ0 : 0 ≤ Ψ := by positivity
  set Kq := LF_Kq D p l Kc Cz Cz2 K E₀ with hKq
  set Q := Kq * Γ₀ ^ (l + 4) * Ψ with hQ
  -- the two pieces of the bound
  set Pz := LF_Pz D N θ K Γ₀ η with hPz
  have hPz0 : 0 ≤ Pz := LF_Pz_nonneg θ hK0 hΓ0 hη
  have hPzle : Pz ≤ 3 * Cz * K ^ 3 * (1 + E₀) * Γ₀ * Ψ := LF_Pz_le θ hK hΓ hη hηE hNη hCz
  have hSZ : LF_SZ D N θ K Γ₀ η ≤ Cs * Γ₀ ^ 3 * u * i ^ 5 := LF_SZ_le θ hK hΓ hη hηE hCz2
  have hSZ0 : 0 ≤ LF_SZ D N θ K Γ₀ η := by
    unfold LF_SZ
    have : 0 ≤ LF_Cz2 D θ := by
      unfold LF_Cz2; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    positivity
  set S := Real.sqrt ((D * N : ℝ) * Γ₀ * i) with hS
  set sF := Real.sqrt ((D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2) with hsF
  set sS := Real.sqrt (2 * LF_SZ D N θ K Γ₀ η) with hsS
  set n32 := (N : ℝ) ^ (-((3 : ℝ) / 2)) with hn32
  have hn320 : 0 ≤ n32 := Real.rpow_nonneg hn.le _
  have hn2 : (N : ℝ) ^ (-(2 : ℝ)) = m ^ 2 := by rw [LF_rpow2 hn.le, hm, inv_pow]
  -- the square-root bounds
  have hn3 : ((N : ℝ) ^ 3)⁻¹ = m ^ 3 := by rw [hm, inv_pow]
  have sb1 : n32 * S ≤ D * Γ₀ * (1 + E₀) * m * i := by
    rw [hn32, LF_rpow32 hn.le, hn3]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : m ^ 3 * ((D * N : ℝ) * Γ₀ * i) = D * Γ₀ * m ^ 2 * i := by
      linear_combination (D * Γ₀ * m ^ 2 * i) * hmn
    rw [e]
    have h1 : (D : ℝ) * Γ₀ ≤ (D * Γ₀) ^ 2 :=
      le_self_pow₀ (one_le_mul_of_one_le_of_one_le hd1 hΓ) two_ne_zero
    have h2 : i ≤ (1 + E₀) ^ 2 * i ^ 2 := by
      simpa using LF_ipow' hi0.le hE1 hEi (a := 1) (b := 2) (c := 2) (by norm_num) (by norm_num)
    calc (D : ℝ) * Γ₀ * m ^ 2 * i ≤ (D * Γ₀) ^ 2 * m ^ 2 * ((1 + E₀) ^ 2 * i ^ 2) := by
          gcongr
      _ = _ := by ring
  have sb2 : n32 * sF ≤ D * Γ₀ * K ^ 2 * (1 + E₀) * m * i ^ 2 := by
    rw [hn32, LF_rpow32 hn.le, hn3]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : m ^ 3 * ((D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2) = D * Γ₀ * K ^ 4 * m ^ 2 * i ^ 3 := by
      linear_combination (D * Γ₀ * K ^ 4 * m ^ 2 * i ^ 3) * hmn
    rw [e]
    have h1 : (D : ℝ) * Γ₀ ≤ (D * Γ₀) ^ 2 :=
      le_self_pow₀ (one_le_mul_of_one_le_of_one_le hd1 hΓ) two_ne_zero
    have h2 : i ^ 3 ≤ (1 + E₀) ^ 2 * i ^ 4 :=
      LF_ipow' hi0.le hE1 hEi (a := 3) (b := 4) (c := 2) (by norm_num) (by norm_num)
    calc (D : ℝ) * Γ₀ * K ^ 4 * m ^ 2 * i ^ 3 ≤ (D * Γ₀) ^ 2 * K ^ 4 * m ^ 2 *
          ((1 + E₀) ^ 2 * i ^ 4) := by gcongr
      _ = _ := by ring
  have sb3 : sF * sS ≤ (1 + 2 * Cs * K ^ 4) * Γ₀ ^ 2 * i ^ 4 := by
    rw [hsF, hsS, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have h0 : 0 ≤ (D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2 := by positivity
    calc (D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2 * (2 * LF_SZ D N θ K Γ₀ η)
        ≤ (D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2 * (2 * (Cs * Γ₀ ^ 3 * u * i ^ 5)) := by
          gcongr
      _ = 2 * Cs * K ^ 4 * Γ₀ ^ 4 * i ^ 8 * (u * ((D : ℝ) * N)) := by ring
      _ = 2 * Cs * K ^ 4 * Γ₀ ^ 4 * i ^ 8 := by rw [hudn, mul_one]
      _ ≤ ((1 + 2 * Cs * K ^ 4) * Γ₀ ^ 2 * i ^ 4) ^ 2 := by
          have : 2 * Cs * K ^ 4 ≤ (1 + 2 * Cs * K ^ 4) ^ 2 := LF_le_sq1 (by positivity)
          have h4 : 0 ≤ Γ₀ ^ 4 * i ^ 8 := by positivity
          calc 2 * Cs * K ^ 4 * Γ₀ ^ 4 * i ^ 8 = 2 * Cs * K ^ 4 * (Γ₀ ^ 4 * i ^ 8) := by ring
            _ ≤ (1 + 2 * Cs * K ^ 4) ^ 2 * (Γ₀ ^ 4 * i ^ 8) := mul_le_mul_of_nonneg_right this h4
            _ = _ := by ring
  have sb4 : n32 * sS ≤ (1 + 2 * Cs) * Γ₀ ^ 2 * (1 + E₀) * m ^ 2 * i ^ 3 := by
    rw [hn32, LF_rpow32 hn.le, hn3]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hdu : u ≤ m := hum
    calc m ^ 3 * (2 * LF_SZ D N θ K Γ₀ η) ≤ m ^ 3 * (2 * (Cs * Γ₀ ^ 3 * u * i ^ 5)) := by gcongr
      _ ≤ m ^ 3 * (2 * (Cs * Γ₀ ^ 3 * m * i ^ 5)) := by gcongr
      _ ≤ m ^ 3 * (2 * (Cs * Γ₀ ^ 4 * m * ((1 + E₀) ^ 2 * i ^ 6))) := by
          have h1 : Γ₀ ^ 3 ≤ Γ₀ ^ 4 := pow_le_pow_right₀ hΓ (by norm_num)
          have h2 : i ^ 5 ≤ (1 + E₀) ^ 2 * i ^ 6 :=
            LF_ipow' hi0.le hE1 hEi (a := 5) (b := 6) (c := 2) (by norm_num) (by norm_num)
          gcongr
      _ = 2 * Cs * (Γ₀ ^ 4 * (1 + E₀) ^ 2 * m ^ 4 * i ^ 6) := by ring
      _ ≤ (1 + 2 * Cs) ^ 2 * (Γ₀ ^ 4 * (1 + E₀) ^ 2 * m ^ 4 * i ^ 6) := by
          have : 2 * Cs ≤ (1 + 2 * Cs) ^ 2 := LF_le_sq1 (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  -- the coefficients of `(x + Ψ_Z)^{2p-1}` and `(x + Ψ_Z)^{2p-2}`
  set Y₁ := (x + Pz) ^ (2 * p - 1) with hY₁
  set Y₂ := (x + Pz) ^ (2 * p - 2) with hY₂
  have hGt : LF_Gt l K Γ₀ = (2 + l) * K * Γ₀ := rfl
  have hGs : LF_Gs K Γ₀ η 2 = K ^ 2 * Γ₀ * i := by simp [LF_Gs, hi]
  set c₁ := 54 * Kc * K ^ 4 * Γ₀ ^ 2 * i * (n32 * S) +
      3 * Kc * (2 * ((2 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * (n32 * sF) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * m * ((4 * p * ((2 + l) * K * Γ₀)) ^ l * (K ^ 2 * Γ₀ * i))
    with hc₁
  set c₂ := 2 * (2 * p - 1) * (u * m) * (sF * sS) +
      72 * (2 * p - 1) * Kc * K ^ 3 * Γ₀ ^ 2 * i * (n32 * sS) with hc₂
  have hRB : LF_RB D N θ K Γ₀ η p l Kc x = c₁ * Y₁ + c₂ * Y₂ := by
    unfold LF_RB
    rw [← hPz, ← hi, ← hS, ← hsF, ← hsS, ← hn32, hn2, hGt, hGs, ← hY₁, ← hY₂, ← hu, ← hm]
    have e1 : u * ((D * N : ℝ)) = 1 := hudn
    linear_combination (3 * Kc * n32 * (18 * (K ^ 4 * Γ₀ ^ 2 * i * S) * Y₁ +
      2 * (2 * (3 * (K * Γ₀) * (K ^ 2 * Γ₀ * i))) * (2 * (2 * p - 1) * Y₂ * sS) +
      sF * ((2 * ((2 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * Y₁)) +
      ((l : ℝ) + 1) ^ 2 * Kc * m ^ 2 * (((D : ℝ) * N) * ((4 * p * ((2 + l) * K * Γ₀)) ^ l *
        (K ^ 2 * Γ₀ * i) * Y₁))) * e1 + (((l : ℝ) + 1) ^ 2 * Kc * D * m *
          ((4 * p * ((2 + l) * K * Γ₀)) ^ l * (K ^ 2 * Γ₀ * i) * Y₁)) * hmn
  -- the bounds on the coefficients
  have hΓl : Γ₀ ^ 3 ≤ Γ₀ ^ (l + 4) := pow_le_pow_right₀ hΓ (by omega)
  have hΓl1 : Γ₀ ^ (l + 1) ≤ Γ₀ ^ (l + 4) := pow_le_pow_right₀ hΓ (by omega)
  have hΓ1 : Γ₀ ≤ Γ₀ ^ (l + 4) := by
    calc Γ₀ = Γ₀ ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hΓ (by omega)
  have hΓ4 : Γ₀ ^ 4 ≤ (Γ₀ ^ (l + 4)) ^ 2 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hΓ (by omega)
  have hi2 : i ≤ (1 + E₀) * i ^ 2 := by
    simpa using LF_ipow' hi0.le hE1 hEi (a := 1) (b := 2) (c := 1) (by norm_num) (by norm_num)
  have hc₁le : c₁ ≤ (54 * Kc * K ^ 4 * D * (1 + E₀) +
      12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀)) *
        Γ₀ ^ (l + 4) * Ψ := by
    have a1 : 54 * Kc * K ^ 4 * Γ₀ ^ 2 * i * (n32 * S) ≤
        54 * Kc * K ^ 4 * D * (1 + E₀) * Γ₀ ^ (l + 4) * Ψ := by
      calc 54 * Kc * K ^ 4 * Γ₀ ^ 2 * i * (n32 * S) ≤
            54 * Kc * K ^ 4 * Γ₀ ^ 2 * i * (D * Γ₀ * (1 + E₀) * m * i) := by gcongr
        _ = 54 * Kc * K ^ 4 * D * (1 + E₀) * Γ₀ ^ 3 * Ψ := by rw [hΨ]; ring
        _ ≤ _ := by gcongr
    have a2 : 3 * Kc * (2 * ((2 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * (n32 * sF) ≤
        12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) *
          Γ₀ ^ (l + 4) * Ψ := by
      calc 3 * Kc * (2 * ((2 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 * (n32 * sF) ≤
            3 * Kc * (2 * ((2 + l) * K * Γ₀)) ^ 2 * (2 * p - 1) ^ 2 *
              (D * Γ₀ * K ^ 2 * (1 + E₀) * m * i ^ 2) := by gcongr
        _ = 12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) *
              Γ₀ ^ 3 * Ψ := by rw [hΨ]; ring
        _ ≤ _ := by gcongr
    have a3 : ((l : ℝ) + 1) ^ 2 * Kc * D * m * ((4 * p * ((2 + l) * K * Γ₀)) ^ l *
        (K ^ 2 * Γ₀ * i)) ≤ ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l *
          K ^ 2 * (1 + E₀) * Γ₀ ^ (l + 4) * Ψ := by
      calc ((l : ℝ) + 1) ^ 2 * Kc * D * m * ((4 * p * ((2 + l) * K * Γ₀)) ^ l *
            (K ^ 2 * Γ₀ * i)) ≤ ((l : ℝ) + 1) ^ 2 * Kc * D * m *
              ((4 * p * ((2 + l) * K * Γ₀)) ^ l * (K ^ 2 * Γ₀ * ((1 + E₀) * i ^ 2))) := by
            gcongr
        _ = ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀) *
              Γ₀ ^ (l + 1) * Ψ := by
            have hpw : (4 * (p : ℝ) * ((2 + l) * K * Γ₀)) ^ l =
                (4 * p * ((2 + l) * K)) ^ l * Γ₀ ^ l := by
              rw [← mul_pow]; congr 1; ring
            rw [hΨ, hpw]; ring
        _ ≤ _ := by gcongr
    linarith
  have hc₂le : c₂ ≤ (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
      72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀)) * (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2 := by
    have hum2 : u * m ≤ m ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hum hm0.le
    have a1 : 2 * (2 * p - 1) * (u * m) * (sF * sS) ≤
        2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) * Γ₀ ^ 4 * Ψ ^ 2 := by
      calc 2 * (2 * p - 1) * (u * m) * (sF * sS) ≤
            2 * (2 * p - 1) * m ^ 2 * ((1 + 2 * Cs * K ^ 4) * Γ₀ ^ 2 * i ^ 4) := by
            gcongr
        _ ≤ 2 * (2 * p - 1) * m ^ 2 * ((1 + 2 * Cs * K ^ 4) * Γ₀ ^ 4 * i ^ 4) := by
            have : Γ₀ ^ 2 ≤ Γ₀ ^ 4 := pow_le_pow_right₀ hΓ (by norm_num)
            gcongr
        _ = _ := by rw [hΨ]; ring
    have a2 : 72 * (2 * p - 1) * Kc * K ^ 3 * Γ₀ ^ 2 * i * (n32 * sS) ≤
        72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀) * Γ₀ ^ 4 * Ψ ^ 2 := by
      calc 72 * (2 * p - 1) * Kc * K ^ 3 * Γ₀ ^ 2 * i * (n32 * sS) ≤
            72 * (2 * p - 1) * Kc * K ^ 3 * Γ₀ ^ 2 * i *
              ((1 + 2 * Cs) * Γ₀ ^ 2 * (1 + E₀) * m ^ 2 * i ^ 3) := by gcongr
        _ = _ := by rw [hΨ]; ring
    have h4 : Γ₀ ^ 4 * Ψ ^ 2 ≤ (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2 :=
      mul_le_mul_of_nonneg_right hΓ4 (by positivity)
    have hk1 : 0 ≤ 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) := by positivity
    have hk2 : 0 ≤ 72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀) := by positivity
    calc c₂ ≤ 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) * Γ₀ ^ 4 * Ψ ^ 2 +
          72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀) * Γ₀ ^ 4 * Ψ ^ 2 :=
          add_le_add a1 a2
      _ = (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
          72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀)) * (Γ₀ ^ 4 * Ψ ^ 2) := by ring
      _ ≤ (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
          72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀)) *
            ((Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2) := mul_le_mul_of_nonneg_left h4 (add_nonneg hk1 hk2)
      _ = _ := by ring
  -- `Ψ_Z ≤ Q`, `c₁ ≤ Q`, `c₂ ≤ Q²`
  have hKq1 : 1 ≤ Kq := by
    rw [hKq]; unfold LF_Kq
    have : 0 ≤ 54 * Kc * K ^ 4 * D * (1 + E₀) := by positivity
    have : 0 ≤ 12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) := by
      positivity
    have : 0 ≤ ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀) := by
      positivity
    have : 0 ≤ 2 * (2 * p - 1) * (1 + 2 * LF_Cs D Cz2 K E₀ * K ^ 4) +
      72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * LF_Cs D Cz2 K E₀) * (1 + E₀) := by positivity
    have : 0 ≤ 3 * Cz * K ^ 3 * (1 + E₀) := by positivity
    linarith
  have hKqe : Kq = (54 * Kc * K ^ 4 * D * (1 + E₀) +
      12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀)) +
      (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
        72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀)) +
      3 * Cz * K ^ 3 * (1 + E₀) + 1 := by
    rw [hKq, hCs]; unfold LF_Kq; ring
  have hΓΨ : 0 ≤ Γ₀ ^ (l + 4) * Ψ := by positivity
  have hpos2 : 0 ≤ 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
      72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀) := by positivity
  have hpos1 : 0 ≤ 54 * Kc * K ^ 4 * D * (1 + E₀) +
      12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) +
      ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀) := by
    positivity
  have hpos3 : 0 ≤ 3 * Cz * K ^ 3 * (1 + E₀) := by positivity
  have hPQ : Pz ≤ Q := by
    refine hPzle.trans ?_
    rw [hQ]
    calc 3 * Cz * K ^ 3 * (1 + E₀) * Γ₀ * Ψ = 3 * Cz * K ^ 3 * (1 + E₀) * (Γ₀ * Ψ) := by ring
      _ ≤ 3 * Cz * K ^ 3 * (1 + E₀) * (Γ₀ ^ (l + 4) * Ψ) :=
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
    have hK2 : 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
        72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀) ≤ Kq ^ 2 := by
      have : 2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
          72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀) ≤ Kq := by
        rw [hKqe]; linarith
      exact this.trans (le_self_pow₀ hKq1 two_ne_zero)
    calc (2 * (2 * p - 1) * (1 + 2 * Cs * K ^ 4) +
          72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * Cs) * (1 + E₀)) * (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2
        ≤ Kq ^ 2 * (Γ₀ ^ (l + 4)) ^ 2 * Ψ ^ 2 := by gcongr
      _ = _ := by ring
  -- conclusion
  have hQ0 : 0 ≤ Q := by positivity
  have hc₁0 : 0 ≤ c₁ := by
    have := Real.sqrt_nonneg ((D * N : ℝ) * Γ₀ * i)
    have := Real.sqrt_nonneg ((D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2)
    positivity
  have hc₂0 : 0 ≤ c₂ := by
    have := Real.sqrt_nonneg ((D * N : ℝ) * Γ₀ * i * (K * i * K) ^ 2)
    have := Real.sqrt_nonneg (2 * LF_SZ D N θ K Γ₀ η)
    positivity
  rw [hRB]
  have hY1 : Y₁ ≤ (x + Q) ^ (2 * p - 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hY2 : Y₂ ≤ (x + Q) ^ (2 * p - 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hY10 : 0 ≤ Y₁ := by positivity
  have hY20 : 0 ≤ Y₂ := by positivity
  exact add_le_add (mul_le_mul hc₁Q hY1 hY10 hQ0) (mul_le_mul hc₂Q hY2 hY20 (by positivity))

/-! ### The setting of Lemma 3.6 -/

/-- `‖M(z)‖ ≤ 5/4` and `|m(z)| < 1` for `‖Λ‖ ≤ 1/10` and `Im z > 0`, and `‖M(z̄)‖ = ‖M(z)‖`. -/
private lemma LF_M_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Λ : Matrix ι ι ℂ}
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z ζ : ℂ} (hz : 0 < z.im) (hζ : LF_pm z ζ) :
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
    rw [this, LF_opNorm_conjTranspose]
    exact hM'

/-- The setting `LF_Set` for `Λ = Λ(A)` with `‖A‖ ≤ 1/20`, `|z| ≤ τ⁻¹`, `‖B‖ ≤ 1` and
`T = E_a M(z₂)`, with `K = 2 + 2τ⁻¹`. -/
private lemma LF_set_inst {D N : ℕ} [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm A ≤ 1 / 20) {τ : ℝ} (hτ : 0 < τ) {z z₁ z₂ : ℂ} (hz : 0 < z.im)
    (hzn : ‖z‖ ≤ τ⁻¹) (h1 : LF_pm z z₁) (h2 : LF_pm z z₂) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (hB : opNorm B ≤ 1) (a : Fin D) :
    LF_Set (lam D N A) B (Ea D N a * MExt (lam D N A) z₂) z z₁ z₂ (2 + 2 * τ⁻¹) := by
  have hne : Nonempty (Idx D N) :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩, ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := (opNorm_lam_le D N A).trans (by linarith)
  have hti : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hM := (LF_M_le hΛ hℓ hz h2).1
  have hE := LF_opNorm_Ea D N a
  set T := Ea D N a * MExt (lam D N A) z₂ with hT
  have hT0 : opNorm T ≤ 5 / 4 := by
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm (Ea D N a) * opNorm (MExt (lam D N A) z₂) ≤ 1 * (5 / 4) :=
          mul_le_mul hE hM (norm_nonneg _) zero_le_one
      _ = 5 / 4 := by ring
  have hTB : opNorm (T * B) ≤ 5 / 4 := by
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm T * opNorm B ≤ 5 / 4 * 1 := mul_le_mul hT0 hB (norm_nonneg _) (by norm_num)
      _ = 5 / 4 := by ring
  have hz₂ : ‖z₂‖ = ‖z‖ := by
    rcases h2 with rfl | rfl
    · rfl
    · exact Complex.norm_conj z
  have hL : opNorm (lam D N A - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ 1 / 10 + τ⁻¹ := by
    rw [sub_eq_add_neg, ← neg_smul]
    refine (opNorm_add_le _ _).trans ?_
    rw [opNorm_smul, norm_neg, hz₂]
    have h1' := LF_opNorm_one (ι := Idx D N)
    have : ‖z‖ * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ τ⁻¹ := by
      calc ‖z‖ * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ τ⁻¹ * 1 :=
            mul_le_mul hzn h1' (norm_nonneg _) hti.le
        _ = τ⁻¹ := mul_one _
    linarith
  have hTL : opNorm (T * (lam D N A - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ))) ≤
      2 + 2 * τ⁻¹ := by
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm T * opNorm (lam D N A - z₂ • (1 : Matrix (Idx D N) (Idx D N) ℂ))
        ≤ 5 / 4 * (1 / 10 + τ⁻¹) := mul_le_mul hT0 hL (norm_nonneg _) (by norm_num)
      _ ≤ 2 + 2 * τ⁻¹ := by linarith
  have hTE : ∀ x, opNorm (T * Ea D N x) ≤ 5 / 4 := by
    intro x
    refine (opNorm_mul_le _ _).trans ?_
    calc opNorm T * opNorm (Ea D N x) ≤ 5 / 4 * 1 :=
          mul_le_mul hT0 (LF_opNorm_Ea D N x) (norm_nonneg _) (by norm_num)
      _ = 5 / 4 := by ring
  have hK : (5 / 4 : ℝ) ≤ 2 + 2 * τ⁻¹ := by linarith
  have hK1 : (1 : ℝ) ≤ 2 + 2 * τ⁻¹ := by linarith
  refine ⟨hΛ, hz, h1, h2, hK1, hB.trans hK1, hT0.trans hK, hTB.trans hK, hTL,
    fun x => (hTE x).trans hK, ?_⟩
  intro q
  rcases q with i | x | x
  · fin_cases i <;> simp only [LF_Qf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LF_opNorm_conjTranspose]
    · exact LF_opNorm_one.trans hK1
    · exact hT0.trans hK
    · exact hB.trans hK1
    · refine (opNorm_mul_le _ _).trans ?_
      rw [LF_opNorm_conjTranspose]
      calc opNorm B * opNorm T ≤ 1 * (5 / 4) := mul_le_mul hB hT0 (norm_nonneg _) zero_le_one
        _ ≤ _ := by linarith
    · exact hTB.trans hK
    · exact hTL
    · exact hT0.trans hK
  · exact (LF_opNorm_Ea D N x).trans hK1
  · simp only [LF_Qf, LF_opNorm_conjTranspose]
    exact (hTE x).trans hK

/-- On Hermitian arrays, `Z = (DN)⁻¹ Σ_{β,α} X_{βα} h̄_{βα} + (the counterterms)` for
`T = E_a M(z₂)`. -/
private lemma LF_Zd {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) (B : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (hz₂ : z₂.im ≠ 0)
    (a : Fin D) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    LF_Z θ Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h = ((D : ℂ) * N)⁻¹ *
      (∑ β, ∑ α, LF_X Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h β α * starRingEnd ℂ (h β α)) +
        LF_C θ Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h := by
  have e : ∀ β α : Idx D N, h α β = starRingEnd ℂ (h β α) := by
    intro β α
    have := hh.apply α β
    simp only [Matrix.of_apply] at this
    rw [← this]
    rfl
  have hs : ∑ β, ∑ α, LF_X Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h β α * h α β =
      ∑ β, ∑ α, LF_X Λ B (Ea D N a * MExt Λ z₂) z₁ z₂ h β α * starRingEnd ℂ (h β α) :=
    Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by rw [e β α]
  rw [LF_Z_eq θ Λ B hΛ z₁ z₂ hz₂ a h hh, LF_under_eq, LF_ntrH, hs]

/-- `Σ_{t,x} |c_t| ≤ 6 D²` and `Σ_{t,x} |c_t|² ≤ 6 D³` for `θ ∈ [0, 1]`. -/
private lemma LF_Cz_le {D : ℕ} [NeZero D] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    LF_Cz D θ ≤ 6 * (D : ℝ) ^ 2 ∧ LF_Cz2 D θ ≤ 6 * (D : ℝ) ^ 3 := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have hDi : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
  have hDi0 : 0 ≤ (D : ℝ)⁻¹ := by positivity
  have hc : ∀ t, ‖LF_cf D θ t‖ ≤ D := by
    intro t
    fin_cases t <;> simp only [LF_cf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, norm_neg, norm_inv, norm_mul,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0,
      abs_of_nonneg (sub_nonneg.mpr hθ1)]
    all_goals nlinarith
  have hcs : ∀ t, ‖LF_cf D θ t‖ ^ 2 ≤ (D : ℝ) ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (hc t) 2
  constructor
  · unfold LF_Cz
    calc ∑ t : Fin 6, ∑ _x : Fin D, ‖LF_cf D θ t‖ ≤ ∑ _t : Fin 6, ∑ _x : Fin D, (D : ℝ) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun _ _ => hc t
      _ = 6 * (D : ℝ) ^ 2 := by simp; ring
  · unfold LF_Cz2
    calc ∑ t : Fin 6, ∑ _x : Fin D, ‖LF_cf D θ t‖ ^ 2 ≤
          ∑ _t : Fin 6, ∑ _x : Fin D, (D : ℝ) ^ 2 :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun _ _ => hcs t
      _ = 6 * (D : ℝ) ^ 3 := by simp; ring

/-! ### Polynomial bounds -/

/-- `η⁻¹ ≤ N` and `N⁻¹ η⁻² ≤ N` for `N⁻¹ ≤ η`. -/
private lemma LF_inv_le {N : ℕ} [NeZero N] {η : ℝ} (hη : 0 < η) (hNη : (N : ℝ)⁻¹ ≤ η) :
    η⁻¹ ≤ N ∧ (N : ℝ)⁻¹ * (η⁻¹) ^ 2 ≤ N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : η⁻¹ ≤ N := by
    have := inv_anti₀ (inv_pos.mpr hn) hNη
    rwa [inv_inv] at this
  refine ⟨h1, ?_⟩
  have h0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  calc (N : ℝ)⁻¹ * (η⁻¹) ^ 2 ≤ (N : ℝ)⁻¹ * (N : ℝ) ^ 2 := by gcongr
    _ = (N : ℝ) := by rw [sq, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

/-- `Γ₀ = K² (1 + η⁻¹) ≤ 2 K² N` and `|Z| ≤ Z_c ≤ 8 C_z K⁷ N³`. -/
private lemma LF_Gc0_Zc_le {D N : ℕ} [NeZero N] (θ : ℝ) {K η Cz : ℝ} (hK : 1 ≤ K) (hη : 0 < η)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hCz : LF_Cz D θ ≤ Cz) :
    LF_Gc0 K η ≤ 2 * K ^ 2 * N ∧ LF_Zc D θ K η ≤ 8 * Cz * K ^ 7 * (N : ℝ) ^ 3 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨hi, -⟩ := LF_inv_le hη hNη
  have hi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hK0 : 0 ≤ K := by linarith
  have hG : LF_Gc0 K η ≤ 2 * K ^ 2 * N := by
    unfold LF_Gc0
    have : 1 + η⁻¹ ≤ 2 * N := by linarith
    calc K ^ 2 * (1 + η⁻¹) ≤ K ^ 2 * (2 * N) := by gcongr
      _ = _ := by ring
  have hG0 : 0 ≤ LF_Gc0 K η := by unfold LF_Gc0; positivity
  refine ⟨hG, ?_⟩
  unfold LF_Zc
  have hCz0 : 0 ≤ LF_Cz D θ := LF_Cz_nonneg D θ
  have h1 : 1 + η⁻¹ ≤ 2 * N := by linarith
  have hCz0' : 0 ≤ Cz := hCz0.trans hCz
  calc LF_Cz D θ * (K * LF_Gc0 K η) * (K ^ 2 * LF_Gc0 K η * (1 + η⁻¹))
      ≤ Cz * (K * (2 * K ^ 2 * N)) * (K ^ 2 * (2 * K ^ 2 * N) * (2 * N)) := by gcongr
    _ = 8 * Cz * K ^ 7 * (N : ℝ) ^ 3 := by ring

/-- The crude constant `R_c = LF_RB(Γ₀ = K²(1 + η⁻¹), x = Z_c) ≤ 2 (W N^{l+5})^{2p}`. -/
private lemma LF_Rc_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K η E₀ Cz Cz2 Kc : ℝ}
    (p l : ℕ) (hp : 1 ≤ p) (hK : 1 ≤ K) (hη : 0 < η) (hηE : η ≤ E₀)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hKc : 0 ≤ Kc) (hCz : LF_Cz D θ ≤ Cz) (hCz2 : LF_Cz2 D θ ≤ Cz2) :
    LF_RB D N θ K (LF_Gc0 K η) η p l Kc (LF_Zc D θ K η) ≤
      2 * ((8 * Cz * K ^ 7 + LF_Kq D p l Kc Cz Cz2 K E₀ * (2 * K ^ 2) ^ (l + 4) + 1) *
        (N : ℝ) ^ (l + 5)) ^ (2 * p) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hn0 : (0 : ℝ) ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hΓ := LF_Gc0_ge hK hη
  obtain ⟨hG, hZ⟩ := LF_Gc0_Zc_le θ hK hη hNη hCz
  obtain ⟨-, hΨ⟩ := LF_inv_le hη hNη
  have hZ0 : 0 ≤ LF_Zc D θ K η := by
    unfold LF_Zc LF_Gc0
    have := LF_Cz_nonneg D θ; have := inv_nonneg.mpr hη.le
    positivity
  have hR := LF_RB_le θ p l hp hK hΓ hη hηE hNη hKc hCz hCz2 _ hZ0
  set Kq := LF_Kq D p l Kc Cz Cz2 K E₀ with hKq
  have hKq0 : 0 ≤ Kq := by
    rw [hKq]; unfold LF_Kq
    have : (0 : ℝ) ≤ 2 * p - 1 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hE0 : 0 ≤ E₀ := hη.le.trans hηE
    have hCz0 : 0 ≤ Cz := (LF_Cz_nonneg D θ).trans hCz
    have hCz20 : 0 ≤ Cz2 := by
      refine le_trans ?_ hCz2
      unfold LF_Cz2
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have := LF_Cs_nonneg D (K := K) (E₀ := E₀) hCz20
    positivity
  have hCz0 : 0 ≤ Cz := (LF_Cz_nonneg D θ).trans hCz
  set Qc := Kq * LF_Gc0 K η ^ (l + 4) * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2) with hQc
  set W := 8 * Cz * K ^ 7 + Kq * (2 * K ^ 2) ^ (l + 4) + 1 with hW
  have hN3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (l + 5) := pow_le_pow_right₀ hn1 (by omega)
  have hQ : Qc ≤ Kq * (2 * K ^ 2) ^ (l + 4) * (N : ℝ) ^ (l + 5) := by
    have h0 : 0 ≤ (N : ℝ)⁻¹ * (η⁻¹) ^ 2 := by have := inv_nonneg.mpr hη.le; positivity
    calc Qc ≤ Kq * (2 * K ^ 2 * N) ^ (l + 4) * N := by
          rw [hQc]; gcongr
      _ = Kq * (2 * K ^ 2) ^ (l + 4) * (N : ℝ) ^ (l + 5) := by rw [mul_pow]; ring
  have hQ0 : 0 ≤ Qc := by rw [hQc]; have := inv_nonneg.mpr hη.le; positivity
  have hX1 : Qc ≤ W * (N : ℝ) ^ (l + 5) := by
    refine hQ.trans ?_
    have : 0 ≤ (8 * Cz * K ^ 7 + 1) * (N : ℝ) ^ (l + 5) := by positivity
    rw [hW]; nlinarith
  have hX2 : LF_Zc D θ K η + Qc ≤ W * (N : ℝ) ^ (l + 5) := by
    have : LF_Zc D θ K η ≤ 8 * Cz * K ^ 7 * (N : ℝ) ^ (l + 5) :=
      hZ.trans (mul_le_mul_of_nonneg_left hN3 (by positivity))
    have : (0 : ℝ) ≤ (N : ℝ) ^ (l + 5) := by positivity
    rw [hW]; nlinarith
  refine hR.trans ?_
  set X := W * (N : ℝ) ^ (l + 5) with hX
  have hp1 : 2 * p - 1 + 1 = 2 * p := by omega
  have hp2 : 2 * p - 2 + 2 = 2 * p := by omega
  have a1 : Qc * (LF_Zc D θ K η + Qc) ^ (2 * p - 1) ≤ X ^ (2 * p) := by
    calc Qc * (LF_Zc D θ K η + Qc) ^ (2 * p - 1) ≤ X * X ^ (2 * p - 1) := by
          gcongr
      _ = X ^ (2 * p) := by rw [← pow_succ', hp1]
  have a2 : Qc ^ 2 * (LF_Zc D θ K η + Qc) ^ (2 * p - 2) ≤ X ^ (2 * p) := by
    calc Qc ^ 2 * (LF_Zc D θ K η + Qc) ^ (2 * p - 2) ≤ X ^ 2 * X ^ (2 * p - 2) := by
          gcongr
      _ = X ^ (2 * p) := by rw [← pow_add, add_comm, hp2]
  linarith

/-- The crude bound `B_c ≤ W_b N^{l+6p}` on the derivatives of order `≤ l + 1`. -/
private lemma LF_Bc_le {D N : ℕ} [NeZero N] (θ : ℝ) {K η E₀ Cz : ℝ} (p l : ℕ) (hp : 1 ≤ p)
    (hK : 1 ≤ K) (hη : 0 < η) (hηE : η ≤ E₀) (hNη : (N : ℝ)⁻¹ ≤ η) (hCz : LF_Cz D θ ≤ Cz)
    [NeZero D] :
    LF_Bc D N θ (l + 1) p K η ≤ (8 * p * (3 + l) * K ^ 3) ^ (l + 1) * (2 * K ^ 4) *
      (8 * Cz * K ^ 7 + 6 * Cz * K ^ 5 * (1 + E₀)) ^ (2 * p - 1) * (N : ℝ) ^ (l + 6 * p) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hK0 : 0 ≤ K := by linarith
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hCz0 : 0 ≤ Cz := (LF_Cz_nonneg D θ).trans hCz
  have hΓ := LF_Gc0_ge hK hη
  obtain ⟨hG, hZ⟩ := LF_Gc0_Zc_le θ hK hη hNη hCz
  obtain ⟨hi, hΨ⟩ := LF_inv_le hη hNη
  have hi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hP := LF_Pz_le θ hK hΓ hη hηE hNη hCz
  have hG0 : 0 ≤ LF_Gc0 K η := by linarith
  have hPz0 := LF_Pz_nonneg (D := D) (N := N) θ hK0 hG0 hη
  have hZ0 : 0 ≤ LF_Zc D θ K η := by
    unfold LF_Zc LF_Gc0
    have := LF_Cz_nonneg D θ
    positivity
  have t1 : 4 * p * LF_Gt (l + 1) K (LF_Gc0 K η) ≤ 8 * p * (3 + l) * K ^ 3 * N := by
    unfold LF_Gt
    push_cast
    calc 4 * (p : ℝ) * ((2 + (l + 1)) * K * LF_Gc0 K η) ≤
          4 * p * ((2 + (l + 1)) * K * (2 * K ^ 2 * N)) := by gcongr
      _ = _ := by ring
  have t2 : LF_Gs K (LF_Gc0 K η) η 2 ≤ 2 * K ^ 4 * (N : ℝ) ^ 2 := by
    unfold LF_Gs
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    calc K ^ 2 * LF_Gc0 K η * η⁻¹ ≤ K ^ 2 * (2 * K ^ 2 * N) * N := by gcongr
      _ = _ := by ring
  have t3 : LF_Zc D θ K η + LF_Pz D N θ K (LF_Gc0 K η) η ≤
      (8 * Cz * K ^ 7 + 6 * Cz * K ^ 5 * (1 + E₀)) * (N : ℝ) ^ 3 := by
    have : LF_Pz D N θ K (LF_Gc0 K η) η ≤ 6 * Cz * K ^ 5 * (1 + E₀) * (N : ℝ) ^ 3 := by
      refine hP.trans ?_
      calc 3 * Cz * K ^ 3 * (1 + E₀) * LF_Gc0 K η * ((N : ℝ)⁻¹ * η⁻¹ ^ 2) ≤
            3 * Cz * K ^ 3 * (1 + E₀) * (2 * K ^ 2 * N) * N := by gcongr
        _ = 6 * Cz * K ^ 5 * (1 + E₀) * (N : ℝ) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by norm_num))
            (by positivity)
    linarith
  have hGt0 : 0 ≤ 4 * p * LF_Gt (l + 1) K (LF_Gc0 K η) := by unfold LF_Gt; positivity
  have hGs0 : 0 ≤ LF_Gs K (LF_Gc0 K η) η 2 := by unfold LF_Gs; positivity
  unfold LF_Bc
  set c1 := 8 * (p : ℝ) * (3 + l) * K ^ 3 with hc1
  set c2 := 8 * Cz * K ^ 7 + 6 * Cz * K ^ 5 * (1 + E₀) with hc2
  calc (4 * p * LF_Gt (l + 1) K (LF_Gc0 K η)) ^ (l + 1) * LF_Gs K (LF_Gc0 K η) η 2 *
        (LF_Zc D θ K η + LF_Pz D N θ K (LF_Gc0 K η) η) ^ (2 * p - 1)
      ≤ (c1 * N) ^ (l + 1) * (2 * K ^ 4 * (N : ℝ) ^ 2) *
        (c2 * (N : ℝ) ^ 3) ^ (2 * p - 1) := by
        gcongr
    _ = c1 ^ (l + 1) * (2 * K ^ 4) *
        c2 ^ (2 * p - 1) *
          ((N : ℝ) ^ (l + 1) * (N : ℝ) ^ 2 * ((N : ℝ) ^ 3) ^ (2 * p - 1)) := by
        rw [mul_pow, mul_pow]; ring
    _ = _ := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 2
        omega

/-- The good-event constant `A ≤ W_a Γ^{l+4p} N^{2p}` for `Γ ≥ 1`. -/
private lemma LF_Ag_le {D N : ℕ} [NeZero D] [NeZero N] (θ : ℝ) {K η E₀ Cz Γ : ℝ} (p l : ℕ)
    (hp : 1 ≤ p) (hK : 1 ≤ K) (hΓ : 1 ≤ Γ) (hη : 0 < η) (hηE : η ≤ E₀)
    (hNη : (N : ℝ)⁻¹ ≤ η) (hCz : LF_Cz D θ ≤ Cz) :
    LF_Ag D N θ p l K Γ η ≤ (24 * p * (3 + l) * K) ^ (l + 1) * (6 * K ^ 2) *
      (72 * Cz * K ^ 3 + 18 * Cz * K ^ 3 * (1 + E₀)) ^ (2 * p - 1) * Γ ^ (l + 4 * p) *
        (N : ℝ) ^ (2 * p) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hK0 : 0 ≤ K := by linarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have hE0 : 0 ≤ E₀ := hη.le.trans hηE
  have hCz0 : 0 ≤ Cz := (LF_Cz_nonneg D θ).trans hCz
  obtain ⟨hi, hΨ⟩ := LF_inv_le hη hNη
  have hi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have h6 : 1 ≤ 6 * Γ := by linarith
  have hP := LF_Pz_le θ hK h6 hη hηE hNη hCz
  have hΓ2 : Γ ≤ Γ ^ 2 := le_self_pow₀ hΓ two_ne_zero
  have t1 : 4 * p * LF_Gt (l + 1) K (6 * Γ) = 24 * p * (3 + l) * K * Γ := by
    unfold LF_Gt; push_cast; ring
  have t2 : LF_Gs K (6 * Γ) η 2 ≤ 6 * K ^ 2 * Γ * N := by
    unfold LF_Gs
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    calc K ^ 2 * (6 * Γ) * η⁻¹ ≤ K ^ 2 * (6 * Γ) * N := by gcongr
      _ = _ := by ring
  have t3 : LF_Cz D θ * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (1 + η⁻¹)) +
      LF_Pz D N θ K (6 * Γ) η ≤ (72 * Cz * K ^ 3 + 18 * Cz * K ^ 3 * (1 + E₀)) * Γ ^ 2 * N := by
    have h1 : 1 + η⁻¹ ≤ 2 * N := by linarith
    have a1 : LF_Cz D θ * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (1 + η⁻¹)) ≤
        72 * Cz * K ^ 3 * Γ ^ 2 * N := by
      have := LF_Cz_nonneg D θ
      calc LF_Cz D θ * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (1 + η⁻¹)) ≤
            Cz * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (2 * N)) := by gcongr
        _ = _ := by ring
    have a2 : LF_Pz D N θ K (6 * Γ) η ≤ 18 * Cz * K ^ 3 * (1 + E₀) * Γ ^ 2 * N := by
      refine hP.trans ?_
      calc 3 * Cz * K ^ 3 * (1 + E₀) * (6 * Γ) * ((N : ℝ)⁻¹ * η⁻¹ ^ 2) ≤
            3 * Cz * K ^ 3 * (1 + E₀) * (6 * Γ ^ 2) * N := by gcongr
        _ = _ := by ring
    have : (72 * Cz * K ^ 3 + 18 * Cz * K ^ 3 * (1 + E₀)) * Γ ^ 2 * N =
        72 * Cz * K ^ 3 * Γ ^ 2 * N + 18 * Cz * K ^ 3 * (1 + E₀) * Γ ^ 2 * N := by ring
    linarith
  have hGs0 : 0 ≤ LF_Gs K (6 * Γ) η 2 := by unfold LF_Gs; positivity
  have hs0 : 0 ≤ LF_Cz D θ * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (1 + η⁻¹)) +
      LF_Pz D N θ K (6 * Γ) η := by
    have := LF_Cz_nonneg D θ
    have := LF_Pz_nonneg (D := D) (N := N) θ hK0 (by linarith : (0 : ℝ) ≤ 6 * Γ) hη
    positivity
  unfold LF_Ag
  rw [t1]
  set c1 := 24 * (p : ℝ) * (3 + l) * K with hc1
  set c2 := 72 * Cz * K ^ 3 + 18 * Cz * K ^ 3 * (1 + E₀) with hc2
  calc (c1 * Γ) ^ (l + 1) * LF_Gs K (6 * Γ) η 2 *
        (LF_Cz D θ * (K * (6 * Γ)) * (K ^ 2 * (6 * Γ) * (1 + η⁻¹)) +
          LF_Pz D N θ K (6 * Γ) η) ^ (2 * p - 1)
      ≤ (c1 * Γ) ^ (l + 1) * (6 * K ^ 2 * Γ * N) *
        (c2 * Γ ^ 2 * N) ^ (2 * p - 1) := by
        gcongr
    _ = c1 ^ (l + 1) * (6 * K ^ 2) *
        c2 ^ (2 * p - 1) *
          (Γ ^ (l + 1) * Γ * (Γ ^ 2) ^ (2 * p - 1)) * ((N : ℝ) * (N : ℝ) ^ (2 * p - 1)) := by
        rw [mul_pow, mul_pow, mul_pow]; ring
    _ = _ := by
        rw [← pow_mul, ← pow_succ, ← pow_add, ← pow_succ']
        congr 3
        · omega
        · omega

/-- `c ≤ N^τ` for all large `N`. -/
private lemma LF_exists_rpow_ge {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → c ≤ (N : ℝ) ^ τ :=
  Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c)

/-! ### The probability of the bad event of the forms -/

/-- The unit vector `v/|v|` (and `e_k` for `v = 0`). -/
private def LF_nrm {D N : ℕ} (k : Idx D N) (v : Idx D N → ℂ) : Idx D N → ℂ :=
  if Real.sqrt (∑ i, ‖v i‖ ^ 2) = 0 then Pi.single k 1
  else ((Real.sqrt (∑ i, ‖v i‖ ^ 2))⁻¹ : ℂ) • v

private lemma LF_nrm_unit {D N : ℕ} (k : Idx D N) (v : Idx D N → ℂ) :
    ∑ i, ‖LF_nrm k v i‖ ^ 2 = 1 := by
  unfold LF_nrm
  split_ifs with h
  · exact LF_single_sq k
  · have h0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hs := Real.sq_sqrt h0
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← Finset.mul_sum, inv_pow]
    rw [hs]
    have : ∑ i, ‖v i‖ ^ 2 ≠ 0 := by
      intro h'; apply h; rw [h', Real.sqrt_zero]
    exact inv_mul_cancel₀ this

private lemma LF_nrm_eq {D N : ℕ} (k : Idx D N) (v : Idx D N → ℂ)
    (hv : Real.sqrt (∑ i, ‖v i‖ ^ 2) ≠ 0) :
    v = ((Real.sqrt (∑ i, ‖v i‖ ^ 2) : ℝ) : ℂ) • LF_nrm k v := by
  unfold LF_nrm
  rw [if_neg hv, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hv, Complex.ofReal_one, one_smul]

/-- `psiIso ≤ 2` for `|m| < 1` and `N η ≥ 1`. -/
private lemma LF_psi_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : Matrix ι ι ℂ} {N : ℕ}
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
probability is `≤ |V|² r ≤ ((7 + 2D) DN)² r`. -/
private lemma LF_bad_le {D N : ℕ} [NeZero D] [NeZero N] {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C θ μ)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm A ≤ 1 / 20) {τ τ₀ r : ℝ} (hτ : 0 < τ)
    (hτ₀ : 0 ≤ τ₀) (hr : 0 ≤ r) {z z₁ z₂ : ℂ} (hzD : z ∈ specDom τ N) (hz : 0 < z.im)
    (hNη : (N : ℝ)⁻¹ ≤ z.im) (h1 : LF_pm z z₁) (h2 : LF_pm z z₂)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (a : Fin D)
    (hani : ∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
      μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ₀ * psiIso (lam D N A) N z <
        ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖} ≤
        ENNReal.ofReal r) :
    μ {h | ∃ x ∈ LF_V (lam D N A) B (Ea D N a * MExt (lam D N A) z₂) z₂,
      ∃ y ∈ LF_V (lam D N A) B (Ea D N a * MExt (lam D N A) z₂) z₂,
        4 * (2 + 2 * τ⁻¹) ^ 2 * (N : ℝ) ^ τ₀ <
          ‖resFactorEval (x, y, lam D N A, z) (symArr h)‖} ≤
      ENNReal.ofReal ((((7 + 2 * D) * (D * N) : ℕ) : ℝ) ^ 2 * r) := by
  have hne : Nonempty (Idx D N) :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩, ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  obtain ⟨k₀⟩ := hne
  have hs := LF_set_inst (D := D) (N := N) A hA hτ hz hzD.1 h1 h2 B hB a
  set Λ := lam D N A with hΛ
  set T := Ea D N a * MExt Λ z₂ with hT
  set V := LF_V Λ B T z₂ with hV
  set K := 2 + 2 * τ⁻¹ with hK
  have hK1 : 1 ≤ K := hs.hK
  have hℓ : opNorm Λ ≤ 1 / 10 := (opNorm_lam_le D N A).trans (by linarith)
  obtain ⟨hM, hm⟩ := LF_M_le (lam_isHermitian D N A) hℓ hz (Or.inl rfl : LF_pm z z)
  have hψ := LF_psi_le hz hm hNη (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ₀ := Real.one_le_rpow
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) hτ₀
  -- the vectors of `V` have norm `≤ K`
  have hVn : ∀ x ∈ V, Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ K := by
    intro x hx
    obtain ⟨⟨q, k⟩, -, rfl⟩ := Finset.mem_image.mp hx
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    refine (LF_mulVec_sq _ _).trans ?_
    rw [LF_single_sq, mul_one]
    have := hs.hQ q
    have h0 : 0 ≤ opNorm (LF_Qf Λ B T z₂ q) := norm_nonneg _
    nlinarith
  set Bad : (Idx D N → ℂ) → (Idx D N → ℂ) → Set (Idx D N → Idx D N → ℂ) := fun x y =>
    {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ₀ * psiIso Λ N z <
      ‖star (LF_nrm k₀ x) ⬝ᵥ ((res (Matrix.of h + Λ) z - MExt Λ z) *ᵥ LF_nrm k₀ y)‖} with hBad
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
    set u := LF_nrm k₀ x with hu
    set v := LF_nrm k₀ y with hv
    have hxu : x = (nx : ℂ) • u := LF_nrm_eq k₀ x hnx0
    have hyv : y = (ny : ℂ) • v := LF_nrm_eq k₀ y hny0
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
      (LF_form_le_opNorm M u v (LF_nrm_unit k₀ x).le (LF_nrm_unit k₀ y).le).trans hM
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
      hani _ _ (LF_nrm_unit k₀ x) (LF_nrm_unit k₀ y))
  refine (Finset.sum_le_sum hsum).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (V.card : ℝ) ≤ (((7 + 2 * D) * (D * N) : ℕ) : ℝ) := by
    have : V.card ≤ (7 + 2 * D) * (D * N) := by
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

/-! ### Markov's inequality -/

/-- Markov's inequality for the moment `E|Z|^{2p}`. -/
private lemma LF_markov {D N : ℕ} {C : ℕ → ℝ} (θ : ℝ) {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) {Λ B T : Matrix (Idx D N) (Idx D N) ℂ} {z z₁ z₂ : ℂ} {K : ℝ}
    (hs : LF_Set Λ B T z z₁ z₂ K) (p : ℕ) {s : ℝ} (hs0 : 0 < s) :
    μ {h | s < ‖LF_Z θ Λ B T z₁ z₂ h‖} ≤
      ENNReal.ofReal ((∫ h, ‖LF_Z θ Λ B T z₁ z₂ h‖ ^ (2 * p) ∂μ) / s ^ (2 * p)) := by
  have hprob := hμ.prob
  have hz₁ := LF_pm_ne hs.hz hs.h1
  have hz₂ := LF_pm_ne hs.hz hs.h2
  set f : (Idx D N → Idx D N → ℂ) → ℝ := fun h => ‖LF_Z θ Λ B T z₁ z₂ h‖ ^ (2 * p) with hf
  have hZm : AEStronglyMeasurable (fun h => LF_Z θ Λ B T z₁ z₂ h) μ :=
    LF_aesm_sym hμ.herm (LF_cd_Z θ hs.herm B T hz₁ hz₂ 0).continuous
  have hfi : Integrable f μ := by
    refine Integrable.mono' (integrable_const (LF_Zc D θ K z.im ^ (2 * p)))
      (hZm.norm.pow _) ?_
    filter_upwards [hμ.herm] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (LF_Z_crude θ hs h hh) _
  have hsp : 0 < s ^ (2 * p) := pow_pos hs0 _
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun h => by positivity) hfi
    (s ^ (2 * p))
  have hsub : {h | s < ‖LF_Z θ Λ B T z₁ z₂ h‖} ⊆ {h | s ^ (2 * p) ≤ f h} := by
    intro h hh
    exact pow_le_pow_left₀ hs0.le hh.le _
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hsp, mul_comm]
  exact hm

/-! ### The exponent bookkeeping -/

private lemma LF_herm0 {D N : ℕ} : (Matrix.of (0 : Idx D N → Idx D N → ℂ)).IsHermitian := by
  ext i j; simp

/-- The crude constant on the bad event: `N^{-2h} 2 (W N^{l+5})^{2p} ≤ τ^{4p} N^{-2p}/3` for
`2h ≥ 2p(l+5) + 2p + 1` and `6 W^{2p} τ^{-4p} ≤ N`. -/
private lemma LF_num_a {n W τ : ℝ} (hn1 : 1 ≤ n) (hW : 0 ≤ W) (hτ : 0 < τ) (p l hh e : ℕ)
    (e2 : hh * 2 = (l + 5) * (2 * p) + (2 * p + 1) + e)
    (h4 : 6 * W ^ (2 * p) / τ ^ (4 * p) ≤ n) :
    (n ^ (hh * 2))⁻¹ * (2 * (W * n ^ (l + 5)) ^ (2 * p)) ≤ τ ^ (4 * p) / 3 / n ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hτ4 : 0 < τ ^ (4 * p) := pow_pos hτ _
  have h1 : (n ^ (hh * 2))⁻¹ * (2 * (W * n ^ (l + 5)) ^ (2 * p)) =
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
    _ ≤ τ ^ (4 * p) / 3 / n ^ (2 * p) := by
        have : 2 * W ^ (2 * p) / n ≤ τ ^ (4 * p) / 3 := by
          rw [div_le_iff₀ hn0]
          rw [div_le_iff₀ hτ4] at h4
          nlinarith
        exact div_le_div_of_nonneg_right this (by positivity)

/-- The good part of the remainder: `DN K_e N^{-(l+2)/2} A ≤ τ^{4p} N^{-2p}/3` for `l = 8p + 2`,
`A ≤ W_a (4K² N^{τ₀})^{l+4p} N^{2p}`, `τ₀ (l + 4p) ≤ 1/2` and
`3 D K_e W_a (4K²)^{l+4p} τ^{-4p} ≤ N^{1/2}`. -/
private lemma LF_num_b {n τ τ₀ d Ke Wa K Ag : ℝ} (hn1 : 1 ≤ n) (hτ : 0 < τ) (hτ₀ : 0 ≤ τ₀)
    (hd : 0 ≤ d) (hKe : 0 ≤ Ke) (hWa : 0 ≤ Wa) (p l : ℕ) (hl : l = 8 * p + 2)
    (hτ₀b : ((l : ℝ) + 4 * p) * τ₀ ≤ 1 / 2)
    (hAg : Ag ≤ Wa * (4 * K ^ 2 * n ^ τ₀) ^ (l + 4 * p) * n ^ (2 * p))
    (h5 : 3 * (d * Ke * Wa * (4 * K ^ 2) ^ (l + 4 * p)) / τ ^ (4 * p) ≤ n ^ (1 / 2 : ℝ)) :
    d * n * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * Ag)) ≤ τ ^ (4 * p) / 3 / n ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hτ4 : 0 < τ ^ (4 * p) := pow_pos hτ _
  have hr : n ^ (-((l : ℝ) + 2) / 2) = (n ^ (4 * p + 2))⁻¹ := by
    rw [show -((l : ℝ) + 2) / 2 = -((4 * p + 2 : ℕ) : ℝ) by rw [hl]; push_cast; ring,
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
  have hAg' : Ag ≤ Wa * ((4 * K ^ 2) ^ (l + 4 * p) * n ^ (1 / 2 : ℝ)) * n ^ (2 * p) :=
    hAg.trans (by gcongr)
  have hnp : n ^ (4 * p + 2) = n ^ (2 * p) * n ^ (2 * p) * n * n := by
    rw [show 4 * p + 2 = 2 * p + 2 * p + 1 + 1 by ring, pow_succ, pow_succ, pow_add]
  calc d * n * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * Ag))
      ≤ d * n * (Ke * ((n ^ (4 * p + 2))⁻¹ *
          (Wa * ((4 * K ^ 2) ^ (l + 4 * p) * n ^ (1 / 2 : ℝ)) * n ^ (2 * p)))) := by
        rw [hr]; gcongr
    _ = c * n ^ (1 / 2 : ℝ) / n / n ^ (2 * p) := by
        rw [hc, hnp]; field_simp
    _ ≤ τ ^ (4 * p) / 3 / n ^ (2 * p) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hn0]
        rw [div_le_iff₀ hτ4] at h5
        calc c * n ^ (1 / 2 : ℝ) = (3 * c) * n ^ (1 / 2 : ℝ) / 3 := by ring
          _ ≤ (n ^ (1 / 2 : ℝ) * τ ^ (4 * p)) * n ^ (1 / 2 : ℝ) / 3 := by gcongr
          _ = τ ^ (4 * p) / 3 * (n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ)) := by ring
          _ = τ ^ (4 * p) / 3 * n := by rw [hs]

/-- The crude part of the remainder: `DN K_e B_c √(ε₀ + K_k σ + σ) ≤ τ^{4p} N^{-2p}/3` for
`ε₀, σ ≤ N^{-2h}`, `B_c ≤ W_b N^{l+6p}`, `h ≥ l + 8p + 2` and
`3 D K_e W_b √(K_k + 2) τ^{-4p} ≤ N`. -/
private lemma LF_num_c {n τ d Ke Wb Kk Bc ε₀ σ : ℝ} (hn1 : 1 ≤ n) (hτ : 0 < τ) (hd : 0 ≤ d)
    (hKe : 0 ≤ Ke) (hWb : 0 ≤ Wb) (hKk : 0 ≤ Kk) (p l hh e : ℕ)
    (e3 : hh = (1 + (l + 6 * p)) + (2 * p + 1) + e) (hε₀ : 0 ≤ ε₀)
    (hε : ε₀ ≤ (n ^ (hh * 2))⁻¹) (hσ : σ = (n ^ (hh * 2))⁻¹) (hBc0 : 0 ≤ Bc)
    (hBc : Bc ≤ Wb * n ^ (l + 6 * p))
    (h6 : 3 * (d * Ke * Wb * Real.sqrt (Kk + 2)) / τ ^ (4 * p) ≤ n) :
    d * n * (Ke * (Bc * Real.sqrt (ε₀ + Kk * σ + σ))) ≤ τ ^ (4 * p) / 3 / n ^ (2 * p) := by
  have hn0 : 0 < n := by linarith
  have hτ4 : 0 < τ ^ (4 * p) := pow_pos hτ _
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
  have hnh : n ^ hh = n ^ (l + 6 * p) * n * n ^ (2 * p) * (n * n ^ e) := by
    rw [e3]; ring
  calc d * n * (Ke * (Bc * Real.sqrt (ε₀ + Kk * σ + σ)))
      ≤ d * n * (Ke * ((Wb * n ^ (l + 6 * p)) * (Real.sqrt (Kk + 2) * (n ^ hh)⁻¹))) := by
        gcongr
    _ = c / n ^ (2 * p) / (n * n ^ e) := by
        rw [hc, hnh]; field_simp
    _ ≤ c / n ^ (2 * p) / n := by
        gcongr
        calc n = n * 1 := (mul_one n).symm
          _ ≤ n * n ^ e := by gcongr; exact one_le_pow₀ hn1
    _ ≤ τ ^ (4 * p) / 3 / n ^ (2 * p) := by
        rw [div_div, div_div, mul_comm (n ^ (2 * p)) n, ← div_div, ← div_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hn0]
        rw [div_le_iff₀ hτ4] at h6
        nlinarith

/-- The final Markov step: `2(C_p + 1) Q^{2p} / (N^{τ'} Ψ)^{2p} ≤ N^{-D'}` for
`Q = K_q (4K² N^{τ₀})^{l+4} Ψ`, `(l + 4) τ₀ ≤ t/2`, `t ≤ τ'`, `D' + 1 ≤ p t` and `C_m ≤ N`. -/
private lemma LF_num_m {n τ₀ t τ' D' Kq K Ψ Cp : ℝ} (hn1 : 1 ≤ n) (hτ₀ : 0 ≤ τ₀) (ht : 0 < t)
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
/-- The fluctuation term `⟨\underline{G₁E_aM₂HG₂}B⟩` of (3.39) [eq:aftertrace] is `≺ N⁻¹η⁻²` in
the setting of Lemma 3.6 [lemma_G_large], uniformly in `θ ∈ [0, 1]` and the class: for
`η ≥ c⁻¹ N^{-1/3}`, `η / Im m ∈ [c⁻¹ N^{-ε_g}, c N^{-ε_g}]`, `z₁, z₂ ∈ {z, z̄}` and deterministic
`‖B‖ ≤ 1`, `|⟨\underline{G₁E_aM₂HG₂}B⟩| ≤ N^{τ'} N⁻¹ η⁻²` outside probability `N^{-D'}`. -/
theorem underTwo_fluct (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 → ∀ a : Fin D,
        μ {h | (N : ℝ) ^ τ' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹) <
            ‖underTwoB (lam D N A) θ h z₁ z₂ a B‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
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
  set l : ℕ := 8 * p + 2 with hl
  have hl2 : 2 ≤ l := by omega
  set hh : ℕ := p * (l + 5) + l + 8 * p + 3 with hhh
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
  set Cz : ℝ := 6 * (D : ℝ) ^ 2 with hCz
  set Cz2 : ℝ := 6 * (D : ℝ) ^ 3 with hCz2
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
  obtain ⟨Ke, Kk, hKe0, hKk0, hrem⟩ := LF_rem l k C
  set Kq := LF_Kq D p l Kc Cz Cz2 K E₀ with hKq
  set W := 8 * Cz * K ^ 7 + Kq * (2 * K ^ 2) ^ (l + 4) + 1 with hW
  set Wb := (8 * p * (3 + l) * K ^ 3) ^ (l + 1) * (2 * K ^ 4) *
    (8 * Cz * K ^ 7 + 6 * Cz * K ^ 5 * (1 + E₀)) ^ (2 * p - 1) with hWb
  set Wa := (24 * p * (3 + l) * K) ^ (l + 1) * (6 * K ^ 2) *
    (72 * Cz * K ^ 3 + 18 * Cz * K ^ 3 * (1 + E₀)) ^ (2 * p - 1) with hWa
  set Cp := 2 * ((2 : ℝ) ^ (2 * p + 2) + 1) ^ (2 * p) with hCp
  set Cm := 2 * (Cp + 1) * (Kq * (4 * K ^ 2) ^ (l + 4)) ^ (2 * p) with hCm
  have hτ4 : 0 < τ ^ (4 * p) := pow_pos hτ _
  -- the thresholds
  obtain ⟨N₁, hN₁⟩ := aniso_local D (by omega) δA τ hδA hτ C τ₀ hτ₀0 ((hh * 2 + 3 : ℕ) : ℝ)
    (by positivity)
  obtain ⟨N₂, hN₂⟩ := LF_exists_rpow_ge hδA 20
  obtain ⟨N₃, hN₃⟩ := LF_exists_rpow_ge (by norm_num : (0 : ℝ) < 1 / 8) (96 * K ^ 2)
  obtain ⟨N₄, hN₄⟩ := LF_exists_rpow_ge one_pos (6 * W ^ (2 * p) / τ ^ (4 * p))
  obtain ⟨N₅, hN₅⟩ := LF_exists_rpow_ge (by norm_num : (0 : ℝ) < 1 / 2)
    (3 * (D * Ke * Wa * (4 * K ^ 2) ^ (l + 4 * p)) / τ ^ (4 * p))
  obtain ⟨N₆, hN₆⟩ := LF_exists_rpow_ge one_pos
    (3 * (D * Ke * Wb * Real.sqrt (Kk + 2)) / τ ^ (4 * p))
  obtain ⟨N₇, hN₇⟩ := LF_exists_rpow_ge one_pos Cm
  obtain ⟨N₈, hN₈⟩ := LF_exists_rpow_ge one_pos ((((7 + 2 * D) * D : ℕ) : ℝ) ^ 2)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ (max N₈ 1))), ?_⟩
  intro N hN θ hθ0 hθ1 μ hμ A hA z hzD hzim _ _ _ z₁ z₂ h1 h2 B hB a
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
  have h1' : LF_pm z z₁ := h1
  have h2' : LF_pm z z₂ := h2
  have hs := LF_set_inst (D := D) (N := N) A hA' hτ hzim hzD.1 h1' h2' B hB a
  set Λ := lam D N A with hΛ
  set T := Ea D N a * MExt Λ z₂ with hT
  have hz₂ := LF_pm_ne hzim h2'
  obtain ⟨hCz', hCz2'⟩ := LF_Cz_le (D := D) hθ0 hθ1
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
  have hbad := LF_bad_le hμ A hA' hτ hτ₀0.le hr0 hzD hzim hNη h1' h2' B hB a hani
  set ε₀ := ((((7 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 * r with hε₀
  have hε₀0 : 0 ≤ ε₀ := by positivity
  have hr' : r = (n ^ (hh * 2 + 3))⁻¹ := by
    rw [hr, Real.rpow_neg hn0.le, Real.rpow_natCast]
  have hε₀le : ε₀ ≤ (n ^ (hh * 2))⁻¹ := by
    have h8 := hN₈ N hN8
    rw [Real.rpow_one] at h8
    have hc : ((((7 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 ≤ n ^ 3 := by
      have e : ((((7 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 =
          ((((7 + 2 * D) * D : ℕ) : ℝ)) ^ 2 * n ^ 2 := by push_cast; ring
      rw [e, pow_succ' n 2]
      exact mul_le_mul_of_nonneg_right h8 (by positivity)
    rw [hε₀, hr', pow_add, mul_inv]
    calc ((((7 + 2 * D) * (D * N) : ℕ) : ℝ)) ^ 2 * ((n ^ (hh * 2))⁻¹ * (n ^ 3)⁻¹)
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
  have hhrem := hrem D N θ μ hμ Λ B T z z₁ z₂ K hs p hp Γ M ε₀ hΓ1 hM0 hMΓ hε₀0 hbad
  set Ψ := n⁻¹ * (z.im⁻¹) ^ 2 with hΨ
  have hΨ0 : 0 < Ψ := by positivity
  set Q := Kq * Γ ^ (l + 4) * Ψ with hQ
  have hKq1 : 1 ≤ Kq := by
    rw [hKq]; unfold LF_Kq
    have : (0 : ℝ) ≤ 2 * p - 1 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hCz20 : 0 ≤ Cz2 := by positivity
    have := LF_Cs_nonneg D (K := K) (E₀ := E₀) hCz20
    have : 0 ≤ 54 * Kc * K ^ 4 * D * (1 + E₀) +
        12 * Kc * ((2 + l) * K) ^ 2 * (2 * p - 1) ^ 2 * D * K ^ 2 * (1 + E₀) +
        ((l : ℝ) + 1) ^ 2 * Kc * D * (4 * p * ((2 + l) * K)) ^ l * K ^ 2 * (1 + E₀) +
        (2 * (2 * p - 1) * (1 + 2 * LF_Cs D Cz2 K E₀ * K ^ 4) +
          72 * (2 * p - 1) * Kc * K ^ 3 * (1 + 2 * LF_Cs D Cz2 K E₀) * (1 + E₀)) +
        3 * Cz * K ^ 3 * (1 + E₀) := by positivity
    linarith
  have hΓl1 : 1 ≤ Γ ^ (l + 4) := one_le_pow₀ hΓ1
  have hQΨ : Ψ ≤ Q := by
    rw [hQ]
    calc Ψ = 1 * 1 * Ψ := by ring
      _ ≤ Kq * Γ ^ (l + 4) * Ψ := by gcongr
  have hQ0 : 0 ≤ Q := hΨ0.le.trans hQΨ
  have hRB : ∀ x, 0 ≤ x → LF_RB D N θ K Γ z.im p l Kc x ≤
      Q * (x + Q) ^ (2 * p - 1) + Q ^ 2 * (x + Q) ^ (2 * p - 2) := fun x hx =>
    LF_RB_le θ p l hp hK1 hΓ1 hzim hη hNη hKc0 hCz' hCz2' x hx
  have hmom := LF_mom θ hθ0 hθ1 hμ hs (LF_Zd θ hs.herm B z₁ z₂ hz₂ a) p l hp hl2 Kc hKc0 hcc _
    hhrem Γ ε₀ Q hΓ1 hε₀0 hQ0 hbad hRB
  -- the remainders are `≤ τ^{4p} N^{-2p} ≤ Q^{2p}`
  have hRc := LF_Rc_le (D := D) (N := N) θ (E₀ := E₀) p l hp hK1 hzim hη hNη hKc0 hCz' hCz2'
  have hBc := LF_Bc_le (D := D) (N := N) θ (E₀ := E₀) p l hp hK1 hzim hη hNη hCz'
  have hAg := LF_Ag_le (D := D) (N := N) θ (E₀ := E₀) p l hp hK1 hΓ1 hzim hη hNη hCz'
  have hW0 : 0 ≤ W := by
    have : 0 ≤ Kq := by linarith
    rw [hW]; positivity
  have hn2p : 0 < n ^ (2 * p) := pow_pos hn0 _
  have hnτ4 : τ ^ (4 * p) / n ^ (2 * p) ≤ Q ^ (2 * p) := by
    have hτz : τ ≤ z.im⁻¹ := by
      rw [le_inv_comm₀ hτ hzim]; exact hη
    have : τ ^ 2 / n ≤ Ψ := by
      rw [hΨ, div_eq_inv_mul]
      gcongr
    calc τ ^ (4 * p) / n ^ (2 * p) = (τ ^ 2 / n) ^ (2 * p) := by
          rw [div_pow, ← pow_mul]; ring_nf
      _ ≤ Ψ ^ (2 * p) := by gcongr
      _ ≤ Q ^ (2 * p) := by gcongr
  -- the remainders
  have hh2 : hh * 2 = (l + 5) * (2 * p) + (2 * p + 1) + (2 * l + 14 * p + 5) := by
    rw [hhh]; ring
  have hh3 : hh = (1 + (l + 6 * p)) + (2 * p + 1) + (p * (l + 5) + 1) := by rw [hhh]; ring
  have hWa0 : 0 ≤ Wa := by rw [hWa]; positivity
  have hWb0 : 0 ≤ Wb := by rw [hWb]; positivity
  have hd0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have k₀ : Idx D N := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hBc0 : 0 ≤ LF_Bc D N θ (l + 1) p K z.im :=
    (norm_nonneg _).trans (LF_F_crude θ hs 0 LF_herm0 k₀ k₀ 0
      (l + 1) p hp k₀ k₀ 0 0 (Nat.zero_le _))
  have ha : ε₀ * LF_RB D N θ K (LF_Gc0 K z.im) z.im p l Kc (LF_Zc D θ K z.im) ≤
      τ ^ (4 * p) / 3 / n ^ (2 * p) :=
    (mul_le_mul_of_nonneg_left hRc hε₀0).trans ((mul_le_mul_of_nonneg_right hε₀le
      (by positivity)).trans (LF_num_a hn1 hW0 hτ p l hh _ hh2
        (by have := hN₄ N hN4; rwa [Real.rpow_one] at this)))
  have hb := LF_num_b hn1 hτ hτ₀0.le hd0 hKe0 hWa0 p l rfl hτ₀b hAg (hN₅ N hN5)
  have hc := LF_num_c hn1 hτ hd0 hKe0 hWb0 hKk0 p l hh _ hh3 hε₀0 hε₀le hσ hBc0 hBc
    (by have := hN₆ N hN6; rwa [Real.rpow_one] at this)
  have hsum : ε₀ * LF_RB D N θ K (LF_Gc0 K z.im) z.im p l Kc (LF_Zc D θ K z.im) +
      (D * n : ℝ) * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * LF_Ag D N θ p l K Γ z.im +
        LF_Bc D N θ (l + 1) p K z.im * Real.sqrt (ε₀ + Kk * (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
          (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))))) ≤ Q ^ (2 * p) := by
    have e : (D * n : ℝ) * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * LF_Ag D N θ p l K Γ z.im +
        LF_Bc D N θ (l + 1) p K z.im * Real.sqrt (ε₀ + Kk * (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
          (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))))) =
        D * n * (Ke * (n ^ (-((l : ℝ) + 2) / 2) * LF_Ag D N θ p l K Γ z.im)) +
        D * n * (Ke * (LF_Bc D N θ (l + 1) p K z.im *
          Real.sqrt (ε₀ + Kk * (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ)) +
            (n ^ ((1 : ℝ) / 2) * M) ^ (-(k : ℝ))))) := by ring
    rw [e]
    have : τ ^ (4 * p) / 3 / n ^ (2 * p) + τ ^ (4 * p) / 3 / n ^ (2 * p) +
        τ ^ (4 * p) / 3 / n ^ (2 * p) = τ ^ (4 * p) / n ^ (2 * p) := by ring
    linarith
  have hY : ∫ h, ‖LF_Z θ Λ B T z₁ z₂ h‖ ^ (2 * p) ∂μ ≤ 2 * (Cp + 1) * Q ^ (2 * p) := by
    have := hmom
    rw [← hCp] at this
    linarith
  -- Markov's inequality
  have hs0 : 0 < n ^ τ' * Ψ := mul_pos (Real.rpow_pos_of_pos hn0 _) hΨ0
  simp only [← inv_pow]
  refine (measure_mono_ae ?_).trans ((LF_markov θ hμ hs p hs0).trans ?_)
  · filter_upwards [hμ.herm] with h hh' hlt
    change n ^ τ' * Ψ < ‖LF_Z θ Λ B T z₁ z₂ h‖
    rw [LF_Z_eq θ Λ B hs.herm z₁ z₂ hz₂ a h hh']
    exact hlt
  · refine ENNReal.ofReal_le_ofReal ?_
    refine (div_le_div_of_nonneg_right hY (by positivity)).trans ?_
    have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
    exact LF_num_m hn1 hτ₀0.le ht0 htτ hΨ0 (by linarith) hCp0 p l hτ₀a hpt
      (by have := hN₇ N hN7; rwa [Real.rpow_one] at this)

end RBMTransitionEdge

end
