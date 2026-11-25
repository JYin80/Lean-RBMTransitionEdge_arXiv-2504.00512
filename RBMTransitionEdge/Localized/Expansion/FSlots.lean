module

public import RBMTransitionEdge.Localized.Expansion.AddLambda
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.Localized.Expansion.Leaf
public import RBMTransitionEdge.Localized.Expansion.AddLambda
public import RBMTransitionEdge.Localized.Expansion.FFactor
import all RBMTransitionEdge.Localized.Expansion.Leaf
import all RBMTransitionEdge.Localized.Expansion.Bound
import all RBMTransitionEdge.Localized.Expansion.PkgEval
import all RBMTransitionEdge.Localized.Expansion.AddLambda

@[expose] public section

/-!
# Slot facts for the bound of the further class

Public forms, at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law], of the bound on `Im m` from (A.1) [square_root_density]
and (2.21) [eq:kappa_gamma_k], of (2.23) [eq:aver_local] for the light weights, of (5.90)
[eq:addoneLambda], and of the integrability of a product of factors.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private Lf_slots from RBMTransitionEdge.Localized.Expansion.Leaf
open private Bd_weight from RBMTransitionEdge.Localized.Expansion.Bound
open private PE_good PE_goodM PE_good_mul PE_good_prod PE_goodM_const PE_goodM_mul PE_goodM_sub
  PE_good_ntr PE_goodM_res PE_good_integrable PE_slot_herm PE_goodM_G
  from RBMTransitionEdge.Localized.Expansion.PkgEval
open private AddL_good AddL_good_of AddL_row AddL_col AddL_expand AddL_sandwich AddL_entry_le
  AddL_one_le AddL_op_mul AddL_op_nonneg AddL_op_add AddL_op_smul AddL_op_one AddL_op_zero
  from RBMTransitionEdge.Localized.Expansion.AddLambda

/-- The upper bound `Im m_a ≤ C N^{-1/3+ε/2} 𝔯(k)^{1/3}` at both slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law], from
(A.1) [square_root_density] and (2.21) [eq:kappa_gamma_k], with `Im z_a = η`. -/
theorem pkg_slot_im (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) :
    ∃ CU : ℝ, 0 < CU ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ∀ a, (e.z a).im = etaK D N k ε ∧ (mSol ((e.c a : ℂ) • lam D N e.A) (e.z a)).im ≤
          CU * ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) := by
  obtain ⟨_, _, _, _, CU, -, -, -, -, hCU, N₀, hN₀⟩ :=
    Lf_slots D hD δA εA ε hδA hεA hε hε' hε'' 0
  refine ⟨CU, hCU, N₀, fun N hN A hA k hk hkN hhs e he a => ?_⟩
  obtain ⟨-, -, hz, -, -, -, him⟩ := hN₀ N hN A hA k hk hkN hhs e he
  exact ⟨(hz a).2.2.1, him a⟩

/-- (2.23) [eq:aver_local] for the light weights `⟨(𝒢_a - 𝔐_a) B⟩`, `‖B‖ ≤ 1`, uniformly in the
member of the class and the slots. -/
theorem fb_weight (D : ℕ) (hD : 1 ≤ D) (δA τ C₀ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hC₀ : 1 ≤ C₀) (C : ℕ → ℝ) :
    ∀ τ'' : ℝ, 0 < τ'' → ∀ D' : ℝ, 0 < D' → ∀ᶠ N in atTop,
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ e : LoopEnv D N, opNorm e.A ≤ (N : ℝ) ^ (-δA) → (∀ a, |e.c a| ≤ C₀) →
      (∀ a, e.z a ∈ specDom τ N) →
      ∀ (a : Fin 2) (B : Matrix (Idx D N) (Idx D N) ℂ), opNorm B ≤ 1 →
        ∃ bad : Set (Idx D N → Idx D N → ℂ), μ bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
          ∀ h, h ∉ bad → ‖ntr ((e.G h a - e.M a) * B)‖ ≤
            (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |(e.z a).im|)) := by
  exact Bd_weight D hD δA τ C₀ hδA hτ hC₀ C

/-- The letter is `𝔐_a` (not paired) or `E_x`. -/
def FLet.isDetE : FLet → Bool
  | .det _ pr => !pr
  | .proj _ => true
  | _ => false

/-! ### (5.90) at the slots, by the expansion (5.89) -/

section AddLambdaSlot

open scoped Matrix.Norms.L2Operator

/-- A factor `F = -α + β Λ F = -α + β F Λ` with `|α|, |β| ≤ 2` and `‖F‖ ≤ 2`: the form (5.89)
[further_expansion_first_order_expansion] of `M(cΛ, z)` and its adjoint for `|c| ≤ 1`. -/
private def FS_good {D N : ℕ} (Λ F : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  ∃ α β : ℂ, ‖α‖ ≤ 2 ∧ ‖β‖ ≤ 2 ∧ opNorm F ≤ 2 ∧
    F = -α • (1 : Matrix (Idx D N) (Idx D N) ℂ) + β • (Λ * F) ∧
    F = -α • (1 : Matrix (Idx D N) (Idx D N) ℂ) + β • (F * Λ)

/-- A letter of a word in (5.90) [eq:addoneLambda]: of the form (5.89)
[further_expansion_first_order_expansion], or diagonal with entries of modulus at most `1`. -/
private def FS_let {D N : ℕ} (Λ F : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  FS_good Λ F ∨ ∃ d : Idx D N → ℂ, F = Matrix.diagonal d ∧ ∀ i, ‖d i‖ ≤ 1

/-- A diagonal matrix with entries of modulus at most `1` has norm at most `1`. -/
private lemma FS_op_diag {D N : ℕ} (d : Idx D N → ℂ) (hd : ∀ i, ‖d i‖ ≤ 1) :
    opNorm (Matrix.diagonal d) ≤ 1 := by
  change ‖(Matrix.diagonal d : Matrix (Idx D N) (Idx D N) ℂ)‖ ≤ 1
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 hd

/-- The adjoint of a factor of the form (5.89) [further_expansion_first_order_expansion] has the
same form, for Hermitian `Λ`. -/
private lemma FS_good_conj {D N : ℕ} {Λ F : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (hF : FS_good Λ F) : FS_good Λ Fᴴ := by
  obtain ⟨α, β, hα, hβ, hn, h1, h2⟩ := hF
  refine ⟨star α, star β, by rwa [norm_star], by rwa [norm_star], ?_, ?_, ?_⟩
  · change ‖Fᴴ‖ ≤ 2
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hn
  · conv_lhs => rw [h2]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, hΛ.eq, Matrix.conjTranspose_one, star_neg]
  · conv_lhs => rw [h1]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, hΛ.eq, Matrix.conjTranspose_one, star_neg]

/-- The adjoint of a letter is a letter, for Hermitian `Λ`. -/
private lemma FS_let_conj {D N : ℕ} {Λ F : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (hF : FS_let Λ F) : FS_let Λ Fᴴ := by
  rcases hF with hF | ⟨d, rfl, hd⟩
  · exact Or.inl (FS_good_conj hΛ hF)
  · exact Or.inr ⟨star d, Matrix.diagonal_conjTranspose d, fun i => by
      rw [Pi.star_apply, norm_star]
      exact hd i⟩

/-- The left factor of (5.90) [eq:addoneLambda] by (5.89)
[further_expansion_first_order_expansion]: row `x` of a product `B₁` of `n` letters is
`p e_xᵀ + e_xᵀ Λ W`, with `|p|`, `‖W‖` and `‖B₁‖` bounded in terms of `n`. -/
private lemma FS_left (n : ℕ) : ∃ Kp Kw Kb : ℝ, 0 ≤ Kp ∧ 0 ≤ Kw ∧ 0 ≤ Kb ∧
    ∀ {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (L : List (Matrix (Idx D N) (Idx D N) ℂ)),
      L.length = n → (∀ F ∈ L, FS_let Λ F) →
      opNorm L.prod ≤ Kb ∧ ∀ x : Idx D N, ∃ (p : ℂ) (W : Matrix (Idx D N) (Idx D N) ℂ),
        ‖p‖ ≤ Kp ∧ opNorm W ≤ Kw ∧
        ∀ j, L.prod x j = p * (1 : Matrix (Idx D N) (Idx D N) ℂ) x j + (Λ * W) x j := by
  induction n with
  | zero =>
    refine ⟨1, 0, 1, by norm_num, le_rfl, by norm_num, fun Λ L hL _ => ?_⟩
    rw [List.length_eq_zero_iff.1 hL, List.prod_nil]
    exact ⟨AddL_op_one, fun x => ⟨1, 0, by simp, by rw [AddL_op_zero], fun j => by simp⟩⟩
  | succ n ih =>
    obtain ⟨Kp, Kw, Kb, hKp, hKw, hKb, h⟩ := ih
    refine ⟨2 * Kp, 2 * Kw + 4 * Kb, 2 * Kb, by positivity, by positivity, by positivity,
      fun {D N} Λ L hL hF => ?_⟩
    obtain _ | ⟨F, L⟩ := L
    · simp at hL
    obtain ⟨hB, hrow⟩ := h Λ L (by simpa using hL) fun G hG => hF G (List.mem_cons_of_mem _ hG)
    rw [List.prod_cons]
    have hB0 := AddL_op_nonneg L.prod
    rcases hF F List.mem_cons_self with ⟨α, β, hα, hβ, hFn, hL1, -⟩ | ⟨d, rfl, hd⟩
    · have hF0 := AddL_op_nonneg F
      have hFB : opNorm (F * L.prod) ≤ 2 * Kb :=
        (AddL_op_mul _ _).trans (by nlinarith)
      refine ⟨hFB, fun x => ?_⟩
      obtain ⟨p, W, hp, hW, hx⟩ := hrow x
      refine ⟨-α * p, (-α) • W + β • (F * L.prod), ?_, ?_, fun j => ?_⟩
      · rw [norm_mul, norm_neg]
        nlinarith [norm_nonneg α, norm_nonneg p]
      · refine (AddL_op_add _ _).trans ?_
        rw [AddL_op_smul, AddL_op_smul, norm_neg]
        nlinarith [norm_nonneg α, norm_nonneg β, AddL_op_nonneg W, AddL_op_nonneg (F * L.prod)]
      · have e1 : (F * L.prod) x j = -α * L.prod x j + β * (Λ * (F * L.prod)) x j := by
          conv_lhs => rw [hL1]
          simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        rw [e1, hx j]
        simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
          smul_eq_mul]
        ring
    · have hdn := FS_op_diag d hd
      refine ⟨(AddL_op_mul _ _).trans (by nlinarith), fun x => ?_⟩
      obtain ⟨p, W, hp, hW, hx⟩ := hrow x
      have hdx := hd x
      refine ⟨d x * p, d x • W, ?_, ?_, fun j => ?_⟩
      · rw [norm_mul]
        nlinarith [norm_nonneg (d x), norm_nonneg p]
      · rw [AddL_op_smul]
        nlinarith [norm_nonneg (d x), AddL_op_nonneg W]
      · rw [Matrix.diagonal_mul, hx j]
        simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
        ring

/-- The right factor of (5.90) [eq:addoneLambda] by (5.89)
[further_expansion_first_order_expansion]: column `y` of a product `B₂` of `n` letters is
`q e_y + W Λ e_y`, with `|q|` and `‖W‖` bounded in terms of `n`, for Hermitian `Λ`. -/
private lemma FS_right (n : ℕ) : ∃ Kq Kv : ℝ, 0 ≤ Kq ∧ 0 ≤ Kv ∧
    ∀ {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian →
      ∀ L : List (Matrix (Idx D N) (Idx D N) ℂ), L.length = n → (∀ F ∈ L, FS_let Λ F) →
      ∀ y : Idx D N, ∃ (q : ℂ) (V : Matrix (Idx D N) (Idx D N) ℂ), ‖q‖ ≤ Kq ∧ opNorm V ≤ Kv ∧
        ∀ i, L.prod i y = q * (1 : Matrix (Idx D N) (Idx D N) ℂ) i y + (V * Λ) i y := by
  obtain ⟨Kp, Kw, _, hKp, hKw, -, h⟩ := FS_left n
  refine ⟨Kp, Kw, hKp, hKw, fun {D N} Λ hΛ L hL hF y => ?_⟩
  obtain ⟨-, hrow⟩ := h Λ (L.map Matrix.conjTranspose).reverse (by simpa using hL)
    fun G hG => by
      obtain ⟨F, hF', rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hG)
      exact FS_let_conj hΛ (hF F hF')
  obtain ⟨p, W, hp, hW, hy⟩ := hrow y
  refine ⟨star p, Wᴴ, by rwa [norm_star], ?_, fun i => ?_⟩
  · change ‖Wᴴ‖ ≤ Kw
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hW
  · have e := hy i
    rw [← Matrix.conjTranspose_list_prod, Matrix.conjTranspose_apply] at e
    have e2 : L.prod i y = star (p * (1 : Matrix (Idx D N) (Idx D N) ℂ) y i + (Λ * W) y i) := by
      rw [← e, star_star]
    rw [e2, star_add, star_mul', ← Matrix.conjTranspose_apply (1 : Matrix (Idx D N) (Idx D N) ℂ),
      ← Matrix.conjTranspose_apply (Λ * W), Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      hΛ.eq]

/-- The entry bound of (5.90) [eq:addoneLambda]: for Hermitian `Λ` with `‖Λ‖ ≤ 1/10`,
`Λ_{xy} = 0`, row `x` of `B₁` equal to `p e_xᵀ + e_xᵀ Λ W` and column `y` of `B₂` equal to
`q e_y + V Λ e_y`, `|(B₁ (Λ - δ) B₂)_{xy}| ≤ C (‖Λ e_x‖ ‖Λ e_y‖ + |δ|)`. -/
private lemma FS_final {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {B₁ B₂ : Matrix (Idx D N) (Idx D N) ℂ} {x y : Idx D N}
    (hLam : Λ x y = 0) (δ : ℝ) {Kp Kw Kq Kv : ℝ} (hKp : 0 ≤ Kp) (hKw : 0 ≤ Kw) (hKq : 0 ≤ Kq)
    (hKv : 0 ≤ Kv) {p q : ℂ} {W V : Matrix (Idx D N) (Idx D N) ℂ} (hp : ‖p‖ ≤ Kp)
    (hW : opNorm W ≤ Kw)
    (hx : ∀ j, B₁ x j = p * (1 : Matrix (Idx D N) (Idx D N) ℂ) x j + (Λ * W) x j)
    (hq : ‖q‖ ≤ Kq) (hV : opNorm V ≤ Kv)
    (hy : ∀ i, B₂ i y = q * (1 : Matrix (Idx D N) (Idx D N) ℂ) i y + (V * Λ) i y) :
    ‖(B₁ * (Λ - (δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * B₂) x y‖ ≤
      (Kp * Kq + Kp * Kv + Kq * Kw + Kw * Kv + 1) *
        (Real.sqrt (∑ i, ‖Λ i x‖ ^ 2) * Real.sqrt (∑ i, ‖Λ i y‖ ^ 2) + |δ|) := by
  have hℓ0 : 0 ≤ opNorm Λ := AddL_op_nonneg Λ
  have h1 : ∀ j, B₁ x j =
      (p • (1 : Matrix (Idx D N) (Idx D N) ℂ) + Λ * W) x j := fun j => by
    rw [hx j]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h2 : ∀ k, B₂ k y =
      (q • (1 : Matrix (Idx D N) (Idx D N) ℂ) + V * Λ) k y := fun k => by
    rw [hy k]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [AddL_col y h2, Matrix.mul_assoc, AddL_row x h1, ← Matrix.mul_assoc,
    AddL_expand p q (δ : ℂ) Λ W V]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hLam]
  set cx := Real.sqrt (∑ i, ‖Λ i x‖ ^ 2)
  set cy := Real.sqrt (∑ i, ‖Λ i y‖ ^ 2)
  have hcx : 0 ≤ cx := Real.sqrt_nonneg _
  have hcy : 0 ≤ cy := Real.sqrt_nonneg _
  have hd : 0 ≤ |δ| := abs_nonneg δ
  have hδn : ‖(δ : ℂ)‖ = |δ| := Complex.norm_real δ
  have hA : 0 ≤ cx * cy := mul_nonneg hcx hcy
  have e1 : ‖(p * q) * (0 - (δ : ℂ) * (1 : Matrix (Idx D N) (Idx D N) ℂ) x y)‖ ≤
      Kp * Kq * |δ| := by
    rw [zero_sub, norm_mul, norm_neg, norm_mul, norm_mul, hδn]
    have h3 : |δ| * ‖(1 : Matrix (Idx D N) (Idx D N) ℂ) x y‖ ≤ |δ| :=
      mul_le_of_le_one_right hd (AddL_one_le x y)
    exact mul_le_mul (mul_le_mul hp hq (norm_nonneg _) hKp) h3 (by positivity)
      (mul_nonneg hKp hKq)
  have e2 : ‖p * (Λ * V * Λ) x y‖ ≤ Kp * Kv * (cx * cy) := by
    rw [norm_mul]
    have hs := AddL_sandwich hΛ V x y
    have : cx * opNorm V * cy ≤ Kv * (cx * cy) := by nlinarith [AddL_op_nonneg V]
    have h0 : ‖(Λ * V * Λ) x y‖ ≤ Kv * (cx * cy) := hs.trans this
    nlinarith [norm_nonneg p, norm_nonneg ((Λ * V * Λ) x y), mul_le_mul hp h0 (norm_nonneg _) hKp]
  have e3 : ‖(p * (δ : ℂ)) * (V * Λ) x y‖ ≤ Kp * Kv * |δ| := by
    rw [norm_mul, norm_mul, hδn]
    have h0 : ‖(V * Λ) x y‖ ≤ Kv := by
      refine (AddL_entry_le _ x y).trans ((AddL_op_mul _ _).trans ?_)
      nlinarith [AddL_op_nonneg V]
    nlinarith [norm_nonneg p, norm_nonneg ((V * Λ) x y), mul_le_mul hp h0 (norm_nonneg _) hKp]
  have e4 : ‖q * (Λ * W * Λ) x y‖ ≤ Kq * Kw * (cx * cy) := by
    rw [norm_mul]
    have hs := AddL_sandwich hΛ W x y
    have : cx * opNorm W * cy ≤ Kw * (cx * cy) := by nlinarith [AddL_op_nonneg W]
    have h0 : ‖(Λ * W * Λ) x y‖ ≤ Kw * (cx * cy) := hs.trans this
    nlinarith [norm_nonneg q, norm_nonneg ((Λ * W * Λ) x y), mul_le_mul hq h0 (norm_nonneg _) hKq]
  have e5 : ‖(q * (δ : ℂ)) * (Λ * W) x y‖ ≤ Kq * Kw * |δ| := by
    rw [norm_mul, norm_mul, hδn]
    have h0 : ‖(Λ * W) x y‖ ≤ Kw := by
      refine (AddL_entry_le _ x y).trans ((AddL_op_mul _ _).trans ?_)
      nlinarith [AddL_op_nonneg W]
    nlinarith [norm_nonneg q, norm_nonneg ((Λ * W) x y), mul_le_mul hq h0 (norm_nonneg _) hKq]
  have e6 : ‖(Λ * (W * Λ * V) * Λ) x y‖ ≤ Kw * Kv * (cx * cy) := by
    have hs := AddL_sandwich hΛ (W * Λ * V) x y
    have hn : opNorm (W * Λ * V) ≤ Kw * Kv := by
      refine (AddL_op_mul _ _).trans ?_
      have := AddL_op_mul W Λ
      have h3 : opNorm (W * Λ) ≤ Kw := this.trans (by nlinarith [AddL_op_nonneg W])
      exact mul_le_mul h3 hV (AddL_op_nonneg _) hKw
    have : cx * opNorm (W * Λ * V) * cy ≤ Kw * Kv * (cx * cy) := by
      nlinarith [AddL_op_nonneg (W * Λ * V)]
    exact hs.trans this
  have e7 : ‖(δ : ℂ) * (Λ * (W * V) * Λ) x y‖ ≤ Kw * Kv * |δ| := by
    rw [norm_mul, hδn]
    have hWV : opNorm (W * V) ≤ Kw * Kv :=
      (AddL_op_mul W V).trans (mul_le_mul hW hV (AddL_op_nonneg _) hKw)
    have hΛWV : opNorm (Λ * (W * V)) ≤ Kw * Kv := by
      refine (AddL_op_mul _ _).trans ?_
      nlinarith [AddL_op_nonneg (W * V), mul_nonneg hKw hKv]
    have h0 : ‖(Λ * (W * V) * Λ) x y‖ ≤ Kw * Kv := by
      refine (AddL_entry_le _ x y).trans ((AddL_op_mul _ _).trans ?_)
      nlinarith [AddL_op_nonneg (Λ * (W * V)), mul_nonneg hKw hKv]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right h0 hd
  have tri : ‖(p * q) * (0 - (δ : ℂ) * (1 : Matrix (Idx D N) (Idx D N) ℂ) x y) +
      p * (Λ * V * Λ) x y - (p * (δ : ℂ)) * (V * Λ) x y + q * (Λ * W * Λ) x y -
      (q * (δ : ℂ)) * (Λ * W) x y + (Λ * (W * Λ * V) * Λ) x y -
      (δ : ℂ) * (Λ * (W * V) * Λ) x y‖ ≤
      ‖(p * q) * (0 - (δ : ℂ) * (1 : Matrix (Idx D N) (Idx D N) ℂ) x y)‖ +
      ‖p * (Λ * V * Λ) x y‖ + ‖(p * (δ : ℂ)) * (V * Λ) x y‖ + ‖q * (Λ * W * Λ) x y‖ +
      ‖(q * (δ : ℂ)) * (Λ * W) x y‖ + ‖(Λ * (W * Λ * V) * Λ) x y‖ +
      ‖(δ : ℂ) * (Λ * (W * V) * Λ) x y‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine tri.trans ?_
  nlinarith [mul_nonneg (mul_nonneg hKp hKq) hA, mul_nonneg (mul_nonneg hKp hKv) hd,
    mul_nonneg (mul_nonneg hKq hKw) hd, mul_nonneg (mul_nonneg hKw hKv) hd, hA, hd]

/-- The diagonal blocks of `Λ` of (1.3) [matrix_H] vanish. -/
private lemma FS_lam_diag {D N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x y : Idx D N)
    (hxy : x.1 = y.1) : lam D N A x y = 0 := by
  have hf : ¬ fwd D y.1 y.1 := by
    unfold fwd
    omega
  simp [lam, hxy, hf]

/-- `M(cΛ, z)` and `M(cΛ, z̄) = M(cΛ, z)^*` of (2.17) [def_G0], for Hermitian `Λ`, `|c| ≤ 1`,
`‖cΛ‖ ≤ 1/10` and `Im z > 0`, have the form (5.89) [further_expansion_first_order_expansion]
with respect to `Λ`. -/
private lemma FS_good_M {D N : ℕ} [Nonempty (Idx D N)] {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) {c : ℝ} (hc : |c| ≤ 1) (hℓ : opNorm ((c : ℂ) • Λ) ≤ 1 / 10) {z : ℂ}
    (hz : 0 < z.im) (s : Bool) :
    FS_good Λ (MExt ((c : ℂ) • Λ) (if s then star z else z)) := by
  have hΛ' : ((c : ℂ) • Λ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hΛ.eq]
    simp
  obtain ⟨-, -, hspec⟩ := mSol_spec _ hΛ' z hz
  obtain ⟨hζ, -, hM⟩ := mSol_apriori _ hΛ' hℓ z hz
  have hℓ0 := AddL_op_nonneg ((c : ℂ) • Λ)
  have hE : MExt ((c : ℂ) • Λ) z = MSol ((c : ℂ) • Λ) z := by
    have h : mExt ((c : ℂ) • Λ) z = mSol ((c : ℂ) • Λ) z := by
      unfold mExt
      simp [hz]
    unfold MExt MSol
    rw [h]
  have hM2 : opNorm (MSol ((c : ℂ) • Λ) z) ≤ 2 := by
    refine hM.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  obtain ⟨α, hα, hn, h1, h2⟩ := AddL_good_of _ _ _ (by linarith) hM2 hspec
  have key : FS_good Λ (MSol ((c : ℂ) • Λ) z) := by
    refine ⟨α, α * c, hα, ?_, hn, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg α, abs_nonneg c]
    · conv_lhs => rw [h1]
      rw [Matrix.smul_mul, smul_smul]
    · conv_lhs => rw [h2]
      rw [Matrix.mul_smul, smul_smul]
  cases s
  · simp only [Bool.false_eq_true, ite_false]
    rw [hE]
    exact key
  · simp only [ite_true]
    rw [(mExt_conj _ hΛ' z hz.ne').2, hE]
    exact FS_good_conj hΛ key

/-- At the slots, every letter `𝔐_a` (not paired) or `E_x` is a letter of (5.90)
[eq:addoneLambda] with respect to `Λ`. -/
private lemma FS_let_slot {D N : ℕ} [Nonempty (Idx D N)] (e : LoopEnv D N)
    (hΛ : (lam D N e.A).IsHermitian) (hℓ : opNorm (lam D N e.A) ≤ 1 / 10)
    (hc : ∀ a, |e.c a| ≤ 1) (hz : ∀ a, 0 < (e.z a).im) {nb : ℕ} (ι : Fin nb → Fin D)
    (h : Idx D N → Idx D N → ℂ) (l : FLet) (hl : l.isDetE = true) :
    FS_let (lam D N e.A) (FLet.mat e ι h l) := by
  cases l with
  | res a f => simp [FLet.isDetE] at hl
  | lamt => simp [FLet.isDetE] at hl
  | det a pr =>
    have hpr : pr = false := by simpa [FLet.isDetE] using hl
    subst hpr
    left
    simp only [FLet.mat, Bool.false_eq_true, ite_false, LoopEnv.M]
    refine FS_good_M hΛ (hc a) ?_ (hz a) (e.s a)
    rw [AddL_op_smul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (e.c a), AddL_op_nonneg (lam D N e.A), hc a]
  | proj x =>
    right
    simp only [FLet.mat, LoopEnv.E]
    split_ifs with hx
    · exact ⟨fun p => if p.1 = ι ⟨x, hx⟩ then 1 else 0, rfl, fun i => by
      dsimp only
      split_ifs <;> simp⟩
    · exact ⟨fun _ => 1, Matrix.diagonal_one.symm, fun _ => by simp⟩

end AddLambdaSlot

/-- (5.90) [eq:addoneLambda] at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law]
and 5.4 [lemma_localized_eigenvalue_local_law]: for words `u₁`, `u₂` of letters `𝔐_a`, `E_x` and
labels in one block, `|(u₁ Λ̃ u₂)_{xy}| ≤ K (‖Λ e_x‖ ‖Λ e_y‖ + |δ|)`, every flag. -/
theorem pkg_add_lambda_slot (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (u₁ u₂ : List FLet)
    (hu : (u₁ ++ u₂).all FLet.isDetE = true) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ) (x y : Idx D N), x.1 = y.1 →
        ‖((u₁.map (FLet.mat e ι h)).prod * e.Lt * (u₂.map (FLet.mat e ι h)).prod) x y‖ ≤
          K * (Real.sqrt (∑ i, ‖lam D N e.A i x‖ ^ 2) * Real.sqrt (∑ i, ‖lam D N e.A i y‖ ^ 2) +
            |e.δ|) := by
  obtain ⟨_, _, -, -, N₀, hN₀⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨Kp, Kw, _, hKp, hKw, -, hL⟩ := FS_left u₁.length
  obtain ⟨Kq, Kv, hKq, hKv, hR⟩ := FS_right u₂.length
  refine ⟨Kp * Kq + Kp * Kv + Kq * Kw + Kw * Kv + 1, by positivity, N₀, ?_⟩
  intro N hN A hA k hk hkN hhs e he nb ι h x y hxy
  obtain ⟨hA2, hc, hz, -⟩ := hN₀ N hN A hA k hk hkN hhs e he
  have : Nonempty (Idx D N) := ⟨x⟩
  have hΛ : (lam D N e.A).IsHermitian := lam_isHermitian D N e.A
  have hℓ : opNorm (lam D N e.A) ≤ 1 / 10 := (opNorm_lam_le D N e.A).trans hA2
  have hlet : ∀ l ∈ u₁ ++ u₂, FS_let (lam D N e.A) (FLet.mat e ι h l) :=
    fun l hl => FS_let_slot e hΛ hℓ hc (fun a => (hz a).2.1) ι h l (List.all_eq_true.1 hu l hl)
  obtain ⟨-, hrow⟩ := hL (lam D N e.A) (u₁.map (FLet.mat e ι h)) (by simp) fun F hF => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hF
    exact hlet l (List.mem_append_left _ hl)
  obtain ⟨p, W, hp, hW, hx⟩ := hrow x
  obtain ⟨q, V, hq, hV, hy⟩ := hR (lam D N e.A) hΛ (u₂.map (FLet.mat e ι h)) (by simp)
    (fun F hF => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hF
      exact hlet l (List.mem_append_right _ hl)) y
  exact FS_final hΛ hℓ (FS_lam_diag e.A x y hxy) e.δ hKp hKw hKq hKv hp hW hx hq hV hy

/-! ### Integrability of a product of factors -/

/-- The conjugate of a function that is smooth through the Hermitian part and bounded on
Hermitian arrays has the same two properties. -/
private lemma FS_good_star {D N : ℕ} {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : PE_good f) :
    PE_good fun h => star (f h) := by
  obtain ⟨hd, C, hC⟩ := hf
  refine ⟨Complex.conjCLE.differentiable.comp hd, C, fun h hh => ?_⟩
  rw [norm_star]
  exact hC h hh

/-- The entries of the adjoint of a matrix-valued function with those two properties. -/
private lemma FS_goodM_conj {D N : ℕ}
    {M : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ} (hM : PE_goodM M) :
    PE_goodM fun h => (M h)ᴴ := fun k l => by
  simpa only [Matrix.conjTranspose_apply] using FS_good_star (hM l k)

/-- The matrix of a letter, as a function of the array, at slots with `Im z_a ≠ 0`. -/
private lemma FS_goodM_let {D N : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) {nb : ℕ}
    (ι : Fin nb → Fin D) (l : FLet) : PE_goodM fun h => FLet.mat e ι h l := by
  cases l with
  | res a f =>
    have hr := PE_goodM_res _ (PE_slot_herm e a) (e.z a) (he a)
    cases f
    · simpa only [FLet.mat, Bool.false_eq_true, ite_false] using hr
    · simpa only [FLet.mat, ite_true] using FS_goodM_conj hr
  | det a pr => exact PE_goodM_const (if pr then e.M a - (e.M a)ᴴ else e.M a)
  | proj x => exact PE_goodM_const (e.E ι x)
  | lamt => exact PE_goodM_const e.Lt

/-- The matrix of a word, as a function of the array, at slots with `Im z_a ≠ 0`. -/
private lemma FS_goodM_word {D N : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) {nb : ℕ}
    (ι : Fin nb → Fin D) (w : List FLet) :
    PE_goodM fun h => (w.map (FLet.mat e ι h)).prod := by
  induction w with
  | nil => simpa using PE_goodM_const (D := D) (N := N) 1
  | cons l w ih =>
    simpa only [List.map_cons, List.prod_cons] using PE_goodM_mul (FS_goodM_let e he ι l) ih

/-- The value of a factor, as a function of the array, at slots with `Im z_a ≠ 0`. -/
private lemma FS_good_fac {D N : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) {nb : ℕ}
    (ι : Fin nb → Fin D) (κ : ℕ → Idx D N) (f : FFac) : PE_good fun h => FFac.val e ι κ h f := by
  cases f with
  | ent x y w => exact FS_goodM_word e he ι w (κ x) (κ y)
  | loop w => exact PE_good_ntr (FS_goodM_word e he ι w)
  | wt a x =>
    exact PE_good_ntr (PE_goodM_mul (PE_goodM_sub (PE_goodM_G e he a) (PE_goodM_const _))
      (PE_goodM_const _))

/-- The product of the factors is integrable for a member of the class, at slots with
`Im z_a ≠ 0`. -/
theorem fb_integrable {D N : ℕ} (C : ℕ → ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C 1 μ) (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) {nb : ℕ}
    (ι : Fin nb → Fin D) (κ : ℕ → Idx D N) (F : List FFac) :
    Integrable (fun h => ((F.map (FFac.val e ι κ h)).prod)) μ := by
  have := hμ.prob
  exact PE_good_integrable hμ.herm
    (PE_good_prod (fun f h => FFac.val e ι κ h f) F fun f _ => FS_good_fac e he ι κ f)

end RBMTransitionEdge

end
