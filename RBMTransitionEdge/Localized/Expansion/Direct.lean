module

public import RBMTransitionEdge.Localized.Expansion.FSlots
public import RBMTransitionEdge.Localized.Expansion.FRows
public import RBMTransitionEdge.Localized.Expansion.PkgSharp
public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.PkgColl
public import RBMTransitionEdge.Localized.Expansion.PkgShape
public import RBMTransitionEdge.Localized.Expansion.PkgWords
import all RBMTransitionEdge.Localized.Expansion.PkgSharp
import all RBMTransitionEdge.Localized.Expansion.PkgEval
import all RBMTransitionEdge.Localized.Expansion.PkgColl
import all RBMTransitionEdge.Localized.Expansion.PkgShape
import all RBMTransitionEdge.Localized.Expansion.PkgWords
import all Init.Data.List.SplitOn.Basic

@[expose] public section

/-!
# The direct estimation of the remainder terms in the proof of Lemma 5.5

For an expanded expression of the Ψ-tree and `p + q ≥ 3` or `R ≥ 1`, the signed sum over the four
starting loops of (5.29) [expansion_of_im] of the remainder `𝓡_𝒯(p, q)` is
`≺ N^{2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` at the slots of Lemmas 5.2 and 5.4 (cases (i)–(iv) of the
direct estimation, (5.67)–(5.78)).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open private PS_val_nonneg PS_psi_nonneg PS_half_nonneg PS_im_nonneg
  from RBMTransitionEdge.Localized.Expansion.PkgSharp
open private PS_shape PS_segs_lam PS_dwirt_wf PS_seg_count PS_segs_free
  from RBMTransitionEdge.Localized.Expansion.PkgSharp
open private PE_good_integrable PE_good_val PE_evalH PE_wirt_zero PE_val
  from RBMTransitionEdge.Localized.Expansion.PkgEval
open private pkgSegs_counts pkgColl_free from RBMTransitionEdge.Localized.Expansion.PkgColl
open private focus_shape isResL ShapeInv ShapeInv.start ShapeInv.iter ShapeInv.main pkgSegs_perm
  seg_free_append Seg from RBMTransitionEdge.Localized.Expansion.PkgShape
open private focus_lam isLamL from RBMTransitionEdge.Localized.Expansion.PkgColl
open private pkgStart_wf from RBMTransitionEdge.Localized.Expansion.PkgWords

/-! ### The monomials of the factor sizes of (5.68)–(5.78) -/

/-- The monomial `1`. -/
private def Dr_one : FMono := ⟨0, 0, 0, 0, 0⟩

/-- The product of a list of monomials. -/
private def Dr_prod (L : List FMono) : FMono := L.foldr FMono.mul Dr_one

/-- The size of a factor of (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1] as a
monomial in `N`, `Im m`, `η⁻¹`, `‖A‖_HS`. -/
private def Dr_fm : PkgFac → FMono
  | .wt => ⟨-2, 0, 2, 0, 0⟩
  | .free r => FMono.psi r
  | .lam1 r => FMono.mul ⟨-1, 0, 0, 1, 0⟩ (FMono.psi r)
  | .lam0 g => ⟨-2, if g then 2 else 0, 0, 2, 0⟩
  | .lam2 a c => FMono.mul (FMono.mul ⟨-2, 0, 0, 2, 0⟩ (FMono.omega a)) (FMono.omega c)
  | .pair => ⟨0, 2, 0, 0, 0⟩

/-- The monomial of `N^{1-(P+1)/2} sharpB`, the row of a derivative structure of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] with `P = p + q` derivatives. -/
private def Dr_mono (R : PkgExpr) (pr : Fin 2 → Bool) (P : ℕ) : FMono :=
  FMono.mul ⟨1 - (P : ℤ) - 2 * R.S, 0, 0, 0, 0⟩ (Dr_prod ((R.profile pr).map Dr_fm))

/-- The hypotheses of the row lemma at `λ₀ = 2ε`. -/
private def Dr_ok (ε εA : ℝ) (m : FMono) : Prop :=
  0 ≤ m.i ∧ 2 ≤ m.d + m.o ∧ m.lamR ε εA (-(1 / 3)) ≤ 2 * ε ∧ m.lamR ε εA (-εA) ≤ 2 * ε ∧
    m.lamR ε εA 0 ≤ 2 * ε

private lemma Dr_prod_cons (m : FMono) (L : List FMono) :
    Dr_prod (m :: L) = m.mul (Dr_prod L) := rfl

private lemma Dr_evalR_mul (m₁ m₂ : FMono) {N : ℕ} {M η hs op : ℝ} (hN : 0 < (N : ℝ))
    (hM : 0 < M) (hη : 0 < η) :
    (m₁.mul m₂).evalR N M η hs op = m₁.evalR N M η hs op * m₂.evalR N M η hs op := by
  simp only [FMono.evalR, FMono.mul]
  push_cast
  rw [show ((m₁.a : ℝ) + m₂.a) / 2 = (m₁.a : ℝ) / 2 + (m₂.a : ℝ) / 2 by ring,
    show ((m₁.i : ℝ) + m₂.i) / 2 = (m₁.i : ℝ) / 2 + (m₂.i : ℝ) / 2 by ring,
    show -((m₁.l : ℝ) + m₂.l) / 2 = -(m₁.l : ℝ) / 2 + -(m₂.l : ℝ) / 2 by ring,
    Real.rpow_add hN, Real.rpow_add hM, Real.rpow_add hη, pow_add, pow_add]
  ring

private lemma Dr_evalR_prod (L : List FMono) {N : ℕ} {M η hs op : ℝ} (hN : 0 < (N : ℝ))
    (hM : 0 < M) (hη : 0 < η) :
    (Dr_prod L).evalR N M η hs op = (L.map fun m => m.evalR N M η hs op).prod := by
  induction L with
  | nil => simp [Dr_prod, Dr_one, FMono.evalR]
  | cons m L ih => rw [Dr_prod_cons, Dr_evalR_mul _ _ hN hM hη, ih, List.map_cons, List.prod_cons]

private lemma Dr_psi_eval (r : ℕ) (N : ℕ) {M η : ℝ} (hs op : ℝ) (hη : 0 < η) :
    pkgPsi η M r = (FMono.psi r).evalR N M η hs op := by
  unfold pkgPsi FMono.psi
  by_cases hr : 2 ≤ r
  · simp only [hr, ↓reduceIte, FMono.evalR]
    have e : -((2 * ((r : ℤ) - 1) : ℤ) : ℝ) / 2 = -((r - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ r)]; ring
    rw [e, Real.rpow_neg hη.le, Real.rpow_natCast]
    simp [div_eq_mul_inv]
  · simp only [hr, ↓reduceIte, FMono.evalR]
    have : r - 1 = 0 := by omega
    simp [this]

private lemma Dr_half_eval (a : ℕ) (N : ℕ) {M η : ℝ} (hs op : ℝ) (hM : 0 ≤ M) (hη : 0 < η) :
    pkgHalf η M a = (FMono.omega a).evalR N M η hs op := by
  unfold pkgHalf FMono.omega
  by_cases ha : 1 ≤ a
  · simp only [show a ≠ 0 by omega, ↓reduceIte, ha, FMono.evalR]
    have e : -((2 * (a : ℤ) - 1 : ℤ) : ℝ) / 2 = -(1 / 2 : ℝ) + -((a - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub ha]; ring
    rw [e, Real.rpow_add hη, Real.rpow_neg hη.le, Real.rpow_neg hη.le, Real.rpow_natCast,
      Real.sqrt_eq_rpow, Real.div_rpow hM hη.le]
    simp only [Int.cast_one, Int.cast_zero, zero_div, Real.rpow_zero, pow_zero, mul_one]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    norm_num
    ring
  · simp only [show a = 0 by omega, ↓reduceIte, FMono.evalR]
    simp

/-- The size of a factor is the value of its monomial. -/
private lemma Dr_val_eq (f : PkgFac) {N : ℕ} {M η hs : ℝ} (op : ℝ) (hN : 0 < (N : ℝ))
    (hM : 0 < M) (hη : 0 < η) :
    PkgFac.val N η M hs f = (Dr_fm f).evalR N M η hs op := by
  cases f with
  | wt =>
    simp only [PkgFac.val, Dr_fm, FMono.evalR]
    norm_num
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    ring
  | free r => exact Dr_psi_eval r N hs op hη
  | lam1 r =>
    simp only [PkgFac.val, Dr_fm]
    rw [Dr_evalR_mul _ _ hN hM hη, ← Dr_psi_eval r N hs op hη]
    simp only [FMono.evalR]
    norm_num
  | lam0 g =>
    simp only [PkgFac.val, Dr_fm, FMono.evalR]
    cases g
    · norm_num [Real.rpow_neg_one, div_eq_mul_inv]; ring
    · norm_num [Real.rpow_neg_one, div_eq_mul_inv]; ring
  | lam2 a c =>
    simp only [PkgFac.val, Dr_fm]
    rw [Dr_evalR_mul _ _ hN hM hη, Dr_evalR_mul _ _ hN hM hη,
      ← Dr_half_eval a N hs op hM.le hη, ← Dr_half_eval c N hs op hM.le hη]
    have h2 : (⟨-2, 0, 0, 2, 0⟩ : FMono).evalR N M η hs op = hs ^ 2 / N := by
      simp only [FMono.evalR]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]
      ring
    rw [h2]
  | pair =>
    simp only [PkgFac.val, Dr_fm, FMono.evalR]
    norm_num

/-- The size of a factor is nonnegative and nondecreasing in `Im m ≥ 0`. -/
private lemma Dr_val_mono (f : PkgFac) (N : ℕ) {η m M hs : ℝ} (hη : 0 < η) (hm : 0 ≤ m)
    (hmM : m ≤ M) (hs0 : 0 ≤ hs) :
    0 ≤ PkgFac.val N η m hs f ∧ PkgFac.val N η m hs f ≤ PkgFac.val N η M hs f := by
  have hpsi : ∀ r, pkgPsi η m r ≤ pkgPsi η M r := fun r => by
    unfold pkgPsi
    split_ifs
    · exact div_le_div_of_nonneg_right hmM (by positivity)
    · exact le_rfl
  have hhalf : ∀ a, pkgHalf η m a ≤ pkgHalf η M a := fun a => by
    unfold pkgHalf
    split_ifs
    · exact le_rfl
    · exact div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hmM hη.le)) (by positivity)
  refine ⟨PS_val_nonneg N hη hm hs0 f, ?_⟩
  cases f with
  | wt => exact le_rfl
  | free r => exact hpsi r
  | lam1 r =>
    simp only [PkgFac.val]
    exact mul_le_mul_of_nonneg_left (hpsi r) (by positivity)
  | lam0 g =>
    simp only [PkgFac.val]
    cases g
    · exact le_rfl
    · simp only [↓reduceIte]
      exact mul_le_mul_of_nonneg_right hmM (by positivity)
  | lam2 a c =>
    simp only [PkgFac.val]
    have h1 := PS_half_nonneg m hη a
    have h2 := PS_half_nonneg m hη c
    have h3 := PS_half_nonneg M hη a
    calc hs ^ 2 / N * pkgHalf η m a * pkgHalf η m c ≤ hs ^ 2 / N * pkgHalf η M a * pkgHalf η M c :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hhalf a) (by positivity)) (hhalf c) h2
            (by positivity)
      _ = _ := rfl
  | pair => exact hmM

private lemma Dr_prod_le (L : List PkgFac) (g₁ g₂ : PkgFac → ℝ)
    (h : ∀ f ∈ L, 0 ≤ g₁ f ∧ g₁ f ≤ g₂ f) : (L.map g₁).prod ≤ (L.map g₂).prod := by
  induction L with
  | nil => simp
  | cons f L ih =>
    simp only [List.map_cons, List.prod_cons]
    have h0 := h f List.mem_cons_self
    have hL := ih fun f' hf' => h f' (List.mem_cons_of_mem _ hf')
    have hn : 0 ≤ (L.map g₁).prod :=
      List.prod_nonneg fun y hy => by
        obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hy
        exact (h f' (List.mem_cons_of_mem _ hf')).1
    exact mul_le_mul h0.2 hL hn (h0.1.trans h0.2)

/-- `N^{(1-P)/2} sharpB` is `|c_𝓡| D^{dexp+nb}` times the value of the row monomial. -/
private lemma Dr_sharp_eq (R : PkgExpr) (D N P : ℕ) (pr : Fin 2 → Bool) {M η hs : ℝ} (op : ℝ)
    (hN : 0 < (N : ℝ)) (hM : 0 < M) (hη : 0 < η) :
    (N : ℝ) ^ (((1 : ℝ) - P) / 2) * R.sharpB D N η M hs pr =
      |(R.cf : ℝ)| * (D : ℝ) ^ (R.dexp + R.nb) * (Dr_mono R pr P).evalR N M η hs op := by
  unfold PkgExpr.sharpB Dr_mono
  rw [Dr_evalR_mul _ _ hN hM hη, Dr_evalR_prod _ hN hM hη, List.map_map]
  have hv : ((R.profile pr).map (PkgFac.val N η M hs)) =
      (R.profile pr).map ((fun m => m.evalR N M η hs op) ∘ Dr_fm) :=
    List.map_congr_left fun f _ => Dr_val_eq f op hN hM hη
  rw [hv]
  have e : (⟨1 - (P : ℤ) - 2 * R.S, 0, 0, 0, 0⟩ : FMono).evalR N M η hs op =
      (N : ℝ) ^ (((1 : ℝ) - P) / 2) * (N : ℝ) ^ (-R.S) := by
    simp only [FMono.evalR]
    rw [← Real.rpow_intCast, ← Real.rpow_add hN]
    push_cast
    simp only [zero_div, Real.rpow_zero, neg_zero, pow_zero, mul_one]
    congr 1
    ring
  rw [e]
  ring

/-! ### The bound of one derivative structure at the slots -/

/-- The cumulant sum of (5.65) [explicit_reminder_terms_before_expansions] around an expression of
the class `𝓡`, with the deterministic letters of `LoopEnv.pairM` in its words. -/
private def Dr_out {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (pr : Fin 2 → Bool)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) : ℂ :=
  -((D : ℂ) * N)⁻¹ * ∑ i : Idx D N, ∑ j : Idx D N,
    if i.1 = j.1 then
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
        ∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ
    else 0

private lemma Dr_out_false {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) :
    Dr_out R e (fun _ => false) μ p q = R.outer e μ p q := by
  unfold Dr_out PkgExpr.outer
  simp only [pkg_evalP_false]

/-- The slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law]. -/
private def Dr_slot (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ) (e : LoopEnv D N) :
    Prop :=
  (∃ s, e = evecEnv D N A k ε s) ∨ ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s

/-- `𝔗 = N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`. -/
private def Dr_T (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : ℝ :=
  (N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2

private lemma Dr_T_nonneg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : 0 ≤ Dr_T D N A k := by
  unfold Dr_T rk
  positivity

/-- A quantity `F` is `≺ N^{2ε} 𝔗` uniformly at the slots. -/
private def Dr_Bd (D : ℕ) (δA εA ε : ℝ) (C : ℕ → ℝ)
    (F : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
    hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
    ∀ e : LoopEnv D N, Dr_slot D N A k ε e →
      F N μ e ≤ K * (N : ℝ) ^ τ * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k)

private lemma Dr_Bd_add {D : ℕ} {δA εA ε : ℝ} {C : ℕ → ℝ}
    {F G : (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℝ}
    (hF : Dr_Bd D δA εA ε C F) (hG : Dr_Bd D δA εA ε C G) :
    Dr_Bd D δA εA ε C fun N μ e => F N μ e + G N μ e := by
  intro τ hτ
  obtain ⟨K₁, hK₁, N₁, h₁⟩ := hF τ hτ
  obtain ⟨K₂, hK₂, N₂, h₂⟩ := hG τ hτ
  refine ⟨K₁ + K₂, by positivity, max N₁ N₂, fun N hN μ hμ A hA k hk hkN hhs e he => ?_⟩
  have a1 := h₁ N (le_trans (le_max_left _ _) hN) μ hμ A hA k hk hkN hhs e he
  have a2 := h₂ N (le_trans (le_max_right _ _) hN) μ hμ A hA k hk hkN hhs e he
  linarith

private lemma Dr_Bd_sum {D : ℕ} {δA εA ε : ℝ} {C : ℕ → ℝ} {α : Type*}
    (F : α → (N : ℕ) → Measure (Idx D N → Idx D N → ℂ) → LoopEnv D N → ℝ) :
    ∀ L : List α, (∀ x ∈ L, Dr_Bd D δA εA ε C (F x)) →
      Dr_Bd D δA εA ε C fun N μ e => (L.map fun x => F x N μ e).sum
  | [], _ => fun τ _ => ⟨0, le_rfl, 0, fun N _ μ _ A _ k _ _ _ e _ => by simp⟩
  | x :: L, h => by
    have := Dr_Bd_add (h x List.mem_cons_self)
      (Dr_Bd_sum F L fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa using this

private lemma Dr_rk (D N k : ℕ) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) : 1 ≤ rk D N k := by
  unfold rk
  exact_mod_cast (le_min hk (by omega))

/-- The direct estimation for one derivative structure of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]: (2.27) [eq:bdd_cumu], the sharp factor
bound (5.68) [bound_factors]–(5.78) [concrete_bound_type_2_2_1], the bound on `Im m` and the row
lemma, when the row monomial satisfies the row hypotheses. -/
private lemma Dr_row (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (T : LoopExpr)
    (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (pr : Fin 2 → Bool) (hpr : R.pairIn pr = true)
    (hm : Dr_ok ε (min εA (1 / 3)) (Dr_mono R pr (p + q))) :
    Dr_Bd D δA εA ε C fun N μ e => ‖Dr_out R e pr μ p q‖ := by
  intro τ hτ
  obtain ⟨K₁, hK₁⟩ := llClass_ccum_le C p (q + 1)
  obtain ⟨N₁, hN₁⟩ := pkg_sharp_bound D hD δA εA ε hδA hεA hε hε' hε'' C T hT hf p q R hR pr
    hpr τ hτ
  obtain ⟨CU, hCU, N₂, hN₂⟩ := pkg_slot_im D hD δA εA ε hδA hεA hε hε' hε''
  have hεA'0 : 0 < min εA (1 / 3) := lt_min hεA (by norm_num)
  have hεA'1 : min εA (1 / 3) ≤ εA := min_le_left _ _
  have hε2 : ε < 2 * min εA (1 / 3) := by
    rcases min_cases εA (1 / 3) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  obtain ⟨hi, hd, h1, h2, h3⟩ := hm
  obtain ⟨Cf, hCf, hrow⟩ := fmono_row D hD (min εA (1 / 3)) ε hεA'0 hε hε2 hε'' _ hi hd
    (2 * ε) h1 h2 h3
  set m := Dr_mono R pr (p + q) with hmdef
  set c₀ := |(R.cf : ℝ)| * (D : ℝ) ^ (R.dexp + R.nb) with hc₀
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hc₀0 : 0 ≤ c₀ := by positivity
  refine ⟨|K₁| * c₀ * CU ^ ((m.i : ℝ) / 2) * Cf, by positivity, max (max N₁ N₂) 1, ?_⟩
  intro N hN μ hμ A hA k hk hkN hhs e he
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hrk := Dr_rk D N k hk hkN
  have hrk0 : (0 : ℝ) < rk D N k := by linarith
  have hslot := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) A hA k
    hk hkN hhs e he
  have hsharp := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) μ hμ A hA k
    hk hkN hhs e he
  set η := etaK D N k ε with hηdef
  have hη : 0 < η := by rw [hηdef, etaK]; positivity
  set M₀ := (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) with hM₀
  have hM₀0 : 0 < M₀ := by positivity
  set mi := (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im with hmi
  have hmi0 : 0 ≤ mi := PS_im_nonneg _ _
  have hmiM : mi ≤ CU * M₀ := (hslot 1).2
  have hs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  -- the cumulant sum
  have hP : ∀ i j : Idx D N, ‖(if i.1 = j.1 then
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
        ∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ else 0)‖ ≤
      |K₁| * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) *
        (if i.1 = j.1 then ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ else 0) := by
    intro i j
    by_cases hij : i.1 = j.1
    · simp only [hij, ↓reduceIte]
      rw [norm_mul, norm_mul, norm_div, norm_pow]
      have hc : ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by split_ifs <;> norm_num
      have hc' : ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ^ (p + q) ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) hc
      have hf1 : (1 : ℝ) ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
        rw [Complex.norm_natCast]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
      have hcc := hK₁ D N 1 μ hμ i j
      have hK : ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤
          |K₁| * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) :=
        hcc.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      have hdiv : ‖ccum (μ.map fun h => h i j) p (q + 1)‖ /
          ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ ≤ ‖ccum (μ.map fun h => h i j) p (q + 1)‖ :=
        div_le_self (norm_nonneg _) hf1
      have hI := norm_nonneg (∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ)
      calc _ ≤ ‖ccum (μ.map fun h => h i j) p (q + 1)‖ * 1 *
            ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖ := by
            gcongr
        _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hK hI
    · simp [hij]
  have hout : ‖Dr_out R e pr μ p q‖ ≤ |K₁| * (N : ℝ) ^ τ *
      ((N : ℝ) ^ (((1 : ℝ) - (p + q : ℕ)) / 2) *
        R.sharpB D N η mi (hsNorm A) pr) := by
    unfold Dr_out
    rw [norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have hs1 : ‖∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
          ∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ else 0)‖ ≤
        |K₁| * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) * ∑ i : Idx D N, ∑ j : Idx D N,
          (if i.1 = j.1 then ‖∫ h, R.evalP e pr (fun l => if l = 0 then i else j) h ∂μ‖
            else 0) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hP i j
    have hK0 : 0 ≤ |K₁| * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) := by positivity
    have e1 : (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) * (N : ℝ) =
        (N : ℝ) ^ (((1 : ℝ) - (p + q : ℕ)) / 2) := by
      rw [← Real.rpow_add_one hN0.ne']
      congr 1
      push_cast
      ring
    calc ((D : ℝ) * N)⁻¹ * ‖_‖ ≤ ((D : ℝ) * N)⁻¹ *
          (|K₁| * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) *
            ((N : ℝ) ^ τ * ((D : ℝ) * (N : ℝ) ^ 2 * R.sharpB D N η mi (hsNorm A) pr))) := by
          gcongr
          exact hs1.trans (mul_le_mul_of_nonneg_left hsharp hK0)
      _ = |K₁| * (N : ℝ) ^ τ * (((N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) * (N : ℝ)) *
            R.sharpB D N η mi (hsNorm A) pr) := by
          field_simp
      _ = _ := by rw [e1]
  -- the monomial at `Im m ≤ C_U N^{-1/3+ε/2} 𝔯(k)^{1/3}`
  have hmono : R.sharpB D N η mi (hsNorm A) pr ≤ R.sharpB D N η (CU * M₀) (hsNorm A) pr := by
    unfold PkgExpr.sharpB
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Dr_prod_le _ _ _ fun f _ => Dr_val_mono f N hη hmi0 hmiM hs0
  have heq := Dr_sharp_eq R D N (p + q) pr (opNorm A) (hs := hsNorm A) hN0
    (mul_pos hCU hM₀0) hη
  have hscale : m.evalR N (CU * M₀) η (hsNorm A) (opNorm A) =
      CU ^ ((m.i : ℝ) / 2) * m.evalR N M₀ η (hsNorm A) (opNorm A) := by
    unfold FMono.evalR
    rw [Real.mul_rpow hCU.le hM₀0.le]
    ring
  have hA1 : opNorm A ≤ 1 :=
    hA.trans (Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith))
  have hhs' : hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - min εA (1 / 3)) * rk D N k ^ (-(1 / 3 : ℝ)) :=
    hhs.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)) (by positivity))
  have hR1 := hrow N hN1 A hA1 k hk hkN hhs'
  have hT0 := Dr_T_nonneg D N A k
  calc ‖Dr_out R e pr μ p q‖ ≤ |K₁| * (N : ℝ) ^ τ *
        ((N : ℝ) ^ (((1 : ℝ) - (p + q : ℕ)) / 2) *
          R.sharpB D N η (CU * M₀) (hsNorm A) pr) := by
        refine hout.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmono (by positivity)) (by positivity))
    _ = |K₁| * (N : ℝ) ^ τ * (c₀ * (CU ^ ((m.i : ℝ) / 2) *
          m.evalR N M₀ η (hsNorm A) (opNorm A))) := by
        rw [heq, hscale]
    _ ≤ |K₁| * (N : ℝ) ^ τ * (c₀ * (CU ^ ((m.i : ℝ) / 2) *
          (Cf * (N : ℝ) ^ (2 * ε) * Dr_T D N A k))) := by
        gcongr
        exact hR1
    _ = _ := by ring

/-! ### The exponent of a row as a sum over the factors -/

/-- The counts of a factor: factor with resolvents, resolvents, letters `Λ̃`, `lam0`, `lam2 0 c`
with `c ≤ 1`, `lam2 0 c` with `c ≥ 2`, `lam0 true`, `pair`, `wt`, at least two resolvents. -/
private def Dr_cv : PkgFac → Fin 10 → ℤ
  | .wt => ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  | .free r => ![1, r, 0, 0, 0, 0, 0, 0, 0, if 2 ≤ r then 1 else 0]
  | .lam1 r => ![1, r, 1, 0, 0, 0, 0, 0, 0, if 2 ≤ r then 1 else 0]
  | .lam0 g => ![1, 0, 1, 1, 0, 0, if g then 1 else 0, 0, 0, 0]
  | .lam2 a c => ![1, a + c, 2, 0, if a = 0 ∧ c ≤ 1 then 1 else 0,
      if a = 0 ∧ 2 ≤ c then 1 else 0, 0, 0, 0, if 2 ≤ a + c then 1 else 0]
  | .pair => ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]

/-- The counts of a list of factors. -/
private def Dr_CV (L : List PkgFac) : Fin 10 → ℤ := (L.map Dr_cv).sum

/-- Every package and every loop with a resolvent count has a resolvent, and a package with both
`Λ̃` ends with a resolvent after the second one. -/
private def Dr_good : PkgFac → Prop
  | .free r => 1 ≤ r
  | .lam1 r => 1 ≤ r
  | .lam2 _ c => 1 ≤ c
  | _ => True

/-- The exponent of a monomial at `ξ` with the part `‖A‖_HS^d`, before the normalization. -/
private def Dr_lf (ε εA ξ : ℝ) (m : FMono) : ℝ :=
  (m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2 + ξ) + (m.l : ℝ) / 2 * (1 - ε + ξ) + (m.d : ℝ) * (-εA - ξ)

/-- The bound of the exponent at `ξ = 0` in terms of the counts. -/
private def Dr_Φ0 (ε εA : ℝ) (v : Fin 10 → ℤ) : ℝ :=
  ((v 1 : ℝ) - v 0) - (v 2 : ℝ) / 2 + ((v 3 : ℝ) + v 4 + v 5) / 2 + ε * ((v 6 : ℝ) + v 7) / 2 +
    ((v 2 : ℝ) + v 3) * (-εA)

/-- The bound of the exponent at `ξ = -1/3` in terms of the counts. -/
private def Dr_Φ1 (ε εA : ℝ) (v : Fin 10 → ℤ) : ℝ :=
  2 / 3 * ((v 1 : ℝ) - v 0) - (v 9 : ℝ) / 3 - (v 2 : ℝ) / 2 - (v 8 : ℝ) / 3 - (v 7 : ℝ) / 3 +
    (v 5 : ℝ) / 2 + (v 4 : ℝ) / 6 + (v 3 : ℝ) / 6 - (v 6 : ℝ) / 3 + ε * ((v 6 : ℝ) + v 7) / 2 +
    ((v 2 : ℝ) + v 3) * (1 / 3 - εA)

private lemma Dr_CV_apply (L : List PkgFac) (k : Fin 10) :
    Dr_CV L k = (L.map fun f => Dr_cv f k).sum := by
  induction L with
  | nil => simp [Dr_CV]
  | cons f L ih =>
    simp only [Dr_CV, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
    rw [ih]

private lemma Dr_CV_append (L₁ L₂ : List PkgFac) : Dr_CV (L₁ ++ L₂) = Dr_CV L₁ + Dr_CV L₂ := by
  simp [Dr_CV]

private lemma Dr_lf_mul (ε εA ξ : ℝ) (m₁ m₂ : FMono) :
    Dr_lf ε εA ξ (m₁.mul m₂) = Dr_lf ε εA ξ m₁ + Dr_lf ε εA ξ m₂ := by
  unfold Dr_lf FMono.mul
  push_cast
  ring

private lemma Dr_lf_prod (ε εA ξ : ℝ) (L : List FMono) :
    Dr_lf ε εA ξ (Dr_prod L) = (L.map (Dr_lf ε εA ξ)).sum := by
  induction L with
  | nil => simp [Dr_prod, Dr_one, Dr_lf]
  | cons m L ih => rw [Dr_prod_cons, Dr_lf_mul, ih, List.map_cons, List.sum_cons]

private lemma Dr_Φ_sum (ε εA : ℝ) (L : List PkgFac) :
    (L.map fun f => Dr_Φ0 ε εA (Dr_cv f)).sum = Dr_Φ0 ε εA (Dr_CV L) ∧
      (L.map fun f => Dr_Φ1 ε εA (Dr_cv f)).sum = Dr_Φ1 ε εA (Dr_CV L) := by
  induction L with
  | nil => simp [Dr_CV, Dr_Φ0, Dr_Φ1]
  | cons f L ih =>
    simp only [List.map_cons, List.sum_cons, ih.1, ih.2]
    have e : Dr_CV (f :: L) = Dr_cv f + Dr_CV L := by simp [Dr_CV]
    rw [e]
    constructor
    · simp only [Dr_Φ0, Pi.add_apply]; push_cast; ring
    · simp only [Dr_Φ1, Pi.add_apply]; push_cast; ring

/-- The exponent of one factor at `ξ = 0` and `ξ = -1/3` against its counts. -/
private lemma Dr_fac_bd (f : PkgFac) (hf : Dr_good f) (ε εA : ℝ) (hε : 0 ≤ ε) :
    Dr_lf ε εA 0 (Dr_fm f) ≤ Dr_Φ0 ε εA (Dr_cv f) ∧
      Dr_lf ε εA (-(1 / 3)) (Dr_fm f) ≤ Dr_Φ1 ε εA (Dr_cv f) := by
  cases f with
  | wt =>
    refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, Dr_Φ0, Dr_Φ1, Dr_cv, Matrix.cons_val] <;>
      push_cast <;> linarith
  | free r =>
    simp only [Dr_good] at hf
    by_cases hr : 2 ≤ r
    · have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.psi, hr, ↓reduceIte, Dr_Φ0, Dr_Φ1,
        Dr_cv, Matrix.cons_val] <;> push_cast <;> nlinarith
    · have hr1 : r = 1 := by omega
      subst hr1
      refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.psi, Dr_Φ0, Dr_Φ1, Dr_cv,
        Matrix.cons_val] <;> norm_num
  | lam1 r =>
    simp only [Dr_good] at hf
    by_cases hr : 2 ≤ r
    · have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.psi, FMono.mul, hr, ↓reduceIte, Dr_Φ0,
        Dr_Φ1, Dr_cv, Matrix.cons_val] <;> push_cast <;> nlinarith
    · have hr1 : r = 1 := by omega
      subst hr1
      refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.psi, FMono.mul, Dr_Φ0, Dr_Φ1, Dr_cv,
        Matrix.cons_val] <;> norm_num <;> linarith
  | lam0 g =>
    cases g <;> refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, Dr_Φ0, Dr_Φ1, Dr_cv,
      Matrix.cons_val, Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> linarith
  | lam2 a c =>
    simp only [Dr_good] at hf
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hf
    by_cases ha : a = 0
    · subst ha
      by_cases hc : 2 ≤ c
      · have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast hc
        refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.omega, FMono.mul, hf, hc,
          ↓reduceIte, Dr_Φ0, Dr_Φ1, Dr_cv, Matrix.cons_val, show ¬ (1 ≤ 0) by omega,
          show ¬ c ≤ 1 by omega, true_and, and_false, zero_add] <;> push_cast <;> nlinarith
      · have hc1 : c = 1 := by omega
        subst hc1
        refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.omega, FMono.mul, Dr_Φ0, Dr_Φ1, Dr_cv,
          Matrix.cons_val] <;> norm_num <;> linarith
    · have ha1 : 1 ≤ a := by omega
      have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
      refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, FMono.omega, FMono.mul, hf, ha1, ↓reduceIte,
        Dr_Φ0, Dr_Φ1, Dr_cv, Matrix.cons_val, ha, false_and, show 2 ≤ a + c by omega] <;>
        push_cast <;> nlinarith
  | pair =>
    refine ⟨?_, ?_⟩ <;> simp only [Dr_lf, Dr_fm, Dr_Φ0, Dr_Φ1, Dr_cv, Matrix.cons_val] <;>
      push_cast <;> linarith

/-- Per factor: the degree in `‖A‖_HS` is the number of `Λ̃` plus one for `lam0`, the power of
`Im m` is nonnegative and there is no `‖A‖`. -/
private lemma Dr_fm_deg (f : PkgFac) :
    ((Dr_fm f).d : ℤ) = Dr_cv f 2 + Dr_cv f 3 ∧ 0 ≤ (Dr_fm f).i ∧ (Dr_fm f).o = 0 := by
  cases f with
  | wt => simp [Dr_fm, Dr_cv]
  | free r => simp only [Dr_fm, FMono.psi]; split_ifs <;> simp [Dr_cv]
  | lam1 r => simp only [Dr_fm, FMono.psi]; split_ifs <;> simp [Dr_cv, FMono.mul]
  | lam0 g => cases g <;> simp [Dr_fm, Dr_cv]
  | lam2 a c =>
    simp only [Dr_fm, FMono.omega]
    split_ifs <;> simp [Dr_cv, FMono.mul] <;> norm_num
  | pair => simp [Dr_fm, Dr_cv]

private lemma Dr_prod_fields (L : List PkgFac) :
    ((Dr_prod (L.map Dr_fm)).d : ℤ) = Dr_CV L 2 + Dr_CV L 3 ∧ 0 ≤ (Dr_prod (L.map Dr_fm)).i ∧
      (Dr_prod (L.map Dr_fm)).o = 0 := by
  induction L with
  | nil => simp [Dr_prod, Dr_one, Dr_CV]
  | cons f L ih =>
    obtain ⟨h1, h2, h3⟩ := Dr_fm_deg f
    simp only [List.map_cons, Dr_prod_cons, FMono.mul]
    have e : Dr_CV (f :: L) = Dr_cv f + Dr_CV L := by simp [Dr_CV]
    rw [e]
    simp only [Pi.add_apply]
    push_cast
    refine ⟨by rw [h1, ih.1]; ring, by linarith [ih.2.1], by rw [h3, ih.2.2]⟩

/-- `lamR` of a monomial of degree at least `2` in `‖A‖_HS` and none in `‖A‖`. -/
private lemma Dr_lamR_eq (m : FMono) (hd : 2 ≤ m.d) (ho : m.o = 0) (ε εA ξ : ℝ) :
    m.lamR ε εA ξ = Dr_lf ε εA ξ m + 1 + 2 * εA := by
  unfold FMono.lamR Dr_lf
  simp only [hd, ↓reduceIte, ho, Nat.cast_zero, zero_mul, add_zero]
  ring

/-- The exponent is affine in `ξ`: its value at `-ε_A ∈ [-1/3, 0]` is at most the larger value at
the ends. -/
private lemma Dr_mid (m : FMono) (hd : 2 ≤ m.d) (ho : m.o = 0) (ε εA L : ℝ) (h0 : 0 ≤ εA)
    (h1 : εA ≤ 1 / 3) (hl : m.lamR ε εA (-(1 / 3)) ≤ L) (hr : m.lamR ε εA 0 ≤ L) :
    m.lamR ε εA (-εA) ≤ L := by
  rw [Dr_lamR_eq m hd ho] at hl hr ⊢
  unfold Dr_lf at hl hr ⊢
  have a1 : 0 ≤ 3 * εA := by linarith
  have a2 : 0 ≤ 1 - 3 * εA := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hl a1, mul_le_mul_of_nonneg_left hr a2]

/-- The row hypotheses from the counts of the factors: the bounds `Φ₀`, `Φ₁` of the exponent at the
two ends of the window. -/
private lemma Dr_ok_of (R : PkgExpr) (pr : Fin 2 → Bool) (P : ℕ) (ε εA : ℝ) (hε : 0 ≤ ε)
    (hεA : 0 ≤ εA) (hεA' : εA ≤ 1 / 3) (hg : ∀ f ∈ R.profile pr, Dr_good f)
    (hd : 2 ≤ Dr_CV (R.profile pr) 2 + Dr_CV (R.profile pr) 3)
    (h0 : ((1 : ℝ) - P) / 2 - R.S + Dr_Φ0 ε εA (Dr_CV (R.profile pr)) + 1 + 2 * εA ≤ 2 * ε)
    (h1 : ((1 : ℝ) - P) / 2 - R.S + Dr_Φ1 ε εA (Dr_CV (R.profile pr)) + 1 + 2 * εA ≤ 2 * ε) :
    Dr_ok ε εA (Dr_mono R pr P) := by
  obtain ⟨hD, hi, ho⟩ := Dr_prod_fields (R.profile pr)
  have hmd : 2 ≤ (Dr_mono R pr P).d := by
    have : ((Dr_mono R pr P).d : ℤ) = ((Dr_prod ((R.profile pr).map Dr_fm)).d : ℤ) := by
      simp [Dr_mono, FMono.mul]
    omega
  have hmo : (Dr_mono R pr P).o = 0 := by simp [Dr_mono, FMono.mul, ho]
  have hmi : 0 ≤ (Dr_mono R pr P).i := by simp [Dr_mono, FMono.mul, hi]
  have hlf : ∀ ξ, Dr_lf ε εA ξ (Dr_mono R pr P) = ((1 : ℝ) - P) / 2 - R.S +
      ((R.profile pr).map fun f => Dr_lf ε εA ξ (Dr_fm f)).sum := by
    intro ξ
    have hpre : Dr_lf ε εA ξ ⟨1 - (P : ℤ) - 2 * R.S, 0, 0, 0, 0⟩ = ((1 : ℝ) - P) / 2 - R.S := by
      simp only [Dr_lf]
      push_cast
      ring
    rw [Dr_mono, Dr_lf_mul, Dr_lf_prod, List.map_map, hpre]
    rfl
  have hsum : ∀ (g₁ g₂ : PkgFac → ℝ), (∀ f ∈ R.profile pr, g₁ f ≤ g₂ f) →
      ((R.profile pr).map g₁).sum ≤ ((R.profile pr).map g₂).sum :=
    fun g₁ g₂ h => List.sum_le_sum (fun f hf => h f hf)
  have e0 : (Dr_mono R pr P).lamR ε εA 0 ≤ 2 * ε := by
    rw [Dr_lamR_eq _ hmd hmo, hlf]
    have := hsum _ _ fun f hf => (Dr_fac_bd f (hg f hf) ε εA hε).1
    rw [(Dr_Φ_sum ε εA _).1] at this
    linarith
  have e1 : (Dr_mono R pr P).lamR ε εA (-(1 / 3)) ≤ 2 * ε := by
    rw [Dr_lamR_eq _ hmd hmo, hlf]
    have := hsum _ _ fun f hf => (Dr_fac_bd f (hg f hf) ε εA hε).2
    rw [(Dr_Φ_sum ε εA _).2] at this
    linarith
  exact ⟨hmi, by omega, e1, Dr_mid _ hmd hmo ε εA _ hεA hεA' e1 e0, e0⟩

/-! ### Sums over lists -/

section ListSums

variable {α : Type*}

private lemma Dr_ls_le (L : List α) (g h : α → ℤ) (hgh : ∀ x ∈ L, g x ≤ h x) :
    (L.map g).sum ≤ (L.map h).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [hgh x List.mem_cons_self, ih fun y hy => hgh y (List.mem_cons_of_mem _ hy)]

private lemma Dr_ls_nonneg (L : List α) (g : α → ℤ) (hg : ∀ x ∈ L, 0 ≤ g x) :
    0 ≤ (L.map g).sum := by
  simpa using Dr_ls_le L (fun _ => 0) g hg

private lemma Dr_ls_single (L : List α) (g : α → ℤ) (hg : ∀ x ∈ L, 0 ≤ g x) (x : α)
    (hx : x ∈ L) : g x ≤ (L.map g).sum := by
  induction L with
  | nil => simp at hx
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hL := Dr_ls_nonneg L g fun z hz => hg z (List.mem_cons_of_mem _ hz)
    rcases List.mem_cons.1 hx with rfl | hx
    · linarith
    · linarith [hg y List.mem_cons_self, ih (fun z hz => hg z (List.mem_cons_of_mem _ hz)) hx]

private lemma Dr_ls_exists (L : List α) (g : α → ℤ) (h : 1 ≤ (L.map g).sum) :
    ∃ x ∈ L, 1 ≤ g x := by
  by_contra hc
  push_neg at hc
  have := Dr_ls_le L g (fun _ => 0) fun x hx => by have := hc x hx; omega
  simp at this
  omega

private lemma Dr_ls_sub (L : List α) (g h : α → ℤ) :
    (L.map fun x => g x - h x).sum = (L.map g).sum - (L.map h).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private lemma Dr_ls_add (L : List α) (g h : α → ℤ) :
    (L.map fun x => g x + h x).sum = (L.map g).sum + (L.map h).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

end ListSums

/-! ### The counts of the factors from the shape of the derivative structures -/

/-- The resolvents between the two `Λ̃` of a package, `a` of `lam2 a c`. -/
private def Dr_a (σ : List PkgLetter) : ℕ :=
  ((((σ.dropWhile fun x => !x.isLam).drop 1).takeWhile fun x => !x.isLam).countP PkgLetter.isRes)

/-- A list with a `Λ̃` splits at its first one. -/
private lemma Dr_lam_split (l : List PkgLetter) (h : 1 ≤ l.countP PkgLetter.isLam) :
    ∃ x S, l.dropWhile (fun x => !x.isLam) = x :: S ∧ x.isLam = true ∧
      l = l.takeWhile (fun x => !x.isLam) ++ x :: S := by
  have hl := List.takeWhile_append_dropWhile (p := fun x : PkgLetter => !x.isLam) (l := l)
  rcases hd : l.dropWhile (fun x => !x.isLam) with _ | ⟨x, S⟩
  · rw [List.dropWhile_eq_nil_iff] at hd
    have : l.countP PkgLetter.isLam = 0 :=
      List.countP_eq_zero.2 fun x hx => by simpa using hd x hx
    omega
  · have hx := List.head_dropWhile_not (fun x : PkgLetter => !x.isLam) (l := l)
      (by rw [hd]; simp)
    simp only [hd, List.head_cons, Bool.not_eq_false'] at hx
    refine ⟨x, S, hd, hx, ?_⟩
    rw [hd] at hl
    exact hl.symm

private lemma Dr_takeWhile_lam (l : List PkgLetter) :
    (l.takeWhile fun x => !x.isLam).countP PkgLetter.isLam = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  simpa using List.mem_takeWhile_imp hx

private lemma Dr_lam_res (x : PkgLetter) (hx : x.isLam = true) : x.isRes = false := by
  rcases x with (y | ⟨u, v⟩)
  · rcases y <;> simp_all [PkgLetter.isLam, PkgLetter.isRes]
  · rfl

/-- The counts of the factor of one package of a derivative structure. -/
private lemma Dr_seg (σ : List PkgLetter) (hl : σ.getLast?.map PkgLetter.isRes = some true)
    (h2 : σ.countP PkgLetter.isLam ≤ 2)
    (h0 : 2 ≤ σ.countP PkgLetter.isLam →
      (σ.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0) :
    Dr_good (pkgSegFac σ) ∧
    Dr_cv (pkgSegFac σ) 1 - Dr_cv (pkgSegFac σ) 0 = (σ.countP PkgLetter.isRes : ℤ) - 1 ∧
    Dr_cv (pkgSegFac σ) 2 = σ.countP PkgLetter.isLam ∧ Dr_cv (pkgSegFac σ) 3 = 0 ∧
    Dr_cv (pkgSegFac σ) 6 = 0 ∧ Dr_cv (pkgSegFac σ) 7 = 0 ∧ Dr_cv (pkgSegFac σ) 8 = 0 ∧
    (1 ≤ Dr_cv (pkgSegFac σ) 4 + Dr_cv (pkgSegFac σ) 5 →
      2 ≤ σ.countP PkgLetter.isLam ∧ Dr_a σ = 0) := by
  obtain ⟨z, hz, hzr⟩ := Option.map_eq_some_iff.1 hl
  have hr : 1 ≤ σ.countP PkgLetter.isRes :=
    List.countP_pos_iff.2 ⟨z, List.mem_of_getLast? hz, hzr⟩
  rcases hc : σ.countP PkgLetter.isLam with _ | _ | _ | n
  · have hf : pkgSegFac σ = .free (σ.countP PkgLetter.isRes) := by simp only [pkgSegFac, hc]
    rw [hf]
    refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Dr_cv, Matrix.cons_val]
  · have hf : pkgSegFac σ = .lam1 (σ.countP PkgLetter.isRes) := by simp only [pkgSegFac, hc]
    rw [hf]
    refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Dr_cv, Matrix.cons_val]
  · obtain ⟨x, S, hd, hx, hσ⟩ := Dr_lam_split σ (by omega)
    have hcS : S.countP PkgLetter.isLam = 1 := by
      have := congrArg (List.countP PkgLetter.isLam) hσ
      rw [List.countP_append, List.countP_cons, Dr_takeWhile_lam, hx] at this
      simp at this
      omega
    obtain ⟨y, S', hd', hy, hS⟩ := Dr_lam_split S (by omega)
    have hcS' : S'.countP PkgLetter.isLam = 0 := by
      have := congrArg (List.countP PkgLetter.isLam) hS
      rw [List.countP_append, List.countP_cons, Dr_takeWhile_lam, hy] at this
      simp at this
      omega
    have hP0 := h0 (by omega)
    have hres : σ.countP PkgLetter.isRes =
        (S.takeWhile fun x => !x.isLam).countP PkgLetter.isRes + S'.countP PkgLetter.isRes := by
      have e1 := congrArg (List.countP PkgLetter.isRes) hσ
      have e2 := congrArg (List.countP PkgLetter.isRes) hS
      rw [List.countP_append, List.countP_cons, Dr_lam_res x hx, hP0] at e1
      rw [List.countP_append, List.countP_cons, Dr_lam_res y hy] at e2
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add] at e1 e2
      omega
    have hc1 : 1 ≤ S'.countP PkgLetter.isRes := by
      rcases S' with _ | ⟨s, S''⟩
      · exfalso
        have e : σ = ((σ.takeWhile fun x => !x.isLam) ++ x ::
            (S.takeWhile fun x => !x.isLam)) ++ [y] := by
          conv_lhs => rw [hσ, hS]
          simp
        rw [e, List.getLast?_concat, Option.some.injEq] at hz
        subst hz
        rw [Dr_lam_res y hy] at hzr
        exact absurd hzr (by simp)
      · have e : σ = ((σ.takeWhile fun x => !x.isLam) ++ x ::
            ((S.takeWhile fun x => !x.isLam) ++ [y])) ++ (s :: S'') := by
          conv_lhs => rw [hσ, hS]
          simp
        rw [e, List.getLast?_append] at hz
        have hne : (s :: S'').getLast? = some ((s :: S'').getLast (by simp)) :=
          List.getLast?_eq_getLast _
        rw [hne, Option.some_or, Option.some.injEq] at hz
        refine List.countP_pos_iff.2 ⟨z, ?_, hzr⟩
        rw [← hz]
        exact List.getLast_mem _
    have hf : pkgSegFac σ = .lam2 (Dr_a σ) (S'.countP PkgLetter.isRes) := by
      simp only [pkgSegFac, hc, Dr_a, hd, List.drop_one, List.tail_cons, hd']
    have ha : Dr_a σ = (S.takeWhile fun x => !x.isLam).countP PkgLetter.isRes := by
      simp only [Dr_a, hd, List.drop_one, List.tail_cons]
    rw [hf]
    refine ⟨hc1, ?_, by simp [Dr_cv], by simp [Dr_cv], by simp [Dr_cv], by simp [Dr_cv],
      by simp [Dr_cv], fun h => ⟨le_rfl, ?_⟩⟩
    · simp only [Dr_cv, Matrix.cons_val]
      rw [ha, hres]
      push_cast
      ring
    · by_contra hne
      simp only [Dr_cv, Matrix.cons_val, hne, false_and, ↓reduceIte] at h
      omega
  · omega

/-- The factors of a word with a letter `Δ`, with no paired letter. -/
private lemma Dr_word_ent (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = true)
    (hseg : ∀ σ ∈ pkgSegs w, σ.getLast?.map PkgLetter.isRes = some true ∧
      σ.countP PkgLetter.isLam ≤ 2 ∧ (2 ≤ σ.countP PkgLetter.isLam →
        (σ.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0)) :
    pkgWordFac (fun _ => false) w = (pkgSegs w).map pkgSegFac ∧
    (∀ σ ∈ pkgSegs w, Dr_good (pkgSegFac σ) ∧
      Dr_cv (pkgSegFac σ) 1 - Dr_cv (pkgSegFac σ) 0 = (σ.countP PkgLetter.isRes : ℤ) - 1 ∧
      Dr_cv (pkgSegFac σ) 2 = σ.countP PkgLetter.isLam ∧ Dr_cv (pkgSegFac σ) 3 = 0 ∧
      Dr_cv (pkgSegFac σ) 6 = 0 ∧ Dr_cv (pkgSegFac σ) 7 = 0 ∧ Dr_cv (pkgSegFac σ) 8 = 0 ∧
      (1 ≤ Dr_cv (pkgSegFac σ) 4 + Dr_cv (pkgSegFac σ) 5 →
        2 ≤ σ.countP PkgLetter.isLam ∧ Dr_a σ = 0)) := by
  refine ⟨?_, fun σ hσ => Dr_seg σ (hseg σ hσ).1 (hseg σ hσ).2.1 (hseg σ hσ).2.2⟩
  simp only [pkgWordFac, hw, ↓reduceIte]
  convert List.append_nil _ using 2
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x _
  rcases x with ((a | a | a | a) | ⟨u, v⟩) <;> simp

/-- The factor of a loop without `Δ`. -/
private lemma Dr_word_free (w : List PkgLetter) (hw : w.any PkgLetter.isEnt = false)
    (h1 : w.countP PkgLetter.isLam ≤ 1)
    (h0 : w.countP PkgLetter.isLam = 0 → 1 ≤ w.countP PkgLetter.isRes) :
    (∀ f ∈ pkgWordFac (fun _ => false) w, Dr_good f) ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 1 - Dr_CV (pkgWordFac (fun _ => false) w) 0 =
      (w.countP PkgLetter.isRes : ℤ) - 1 ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 2 = w.countP PkgLetter.isLam ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 4 + Dr_CV (pkgWordFac (fun _ => false) w) 5 = 0 ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 7 = 0 ∧ Dr_CV (pkgWordFac (fun _ => false) w) 8 = 0 ∧
    (1 ≤ Dr_CV (pkgWordFac (fun _ => false) w) 3 →
      w.countP PkgLetter.isLam = 1 ∧ w.countP PkgLetter.isRes = 0) := by
  rcases hc : w.countP PkgLetter.isLam with _ | _ | n
  · have hr := h0 hc
    simp only [pkgWordFac, hw, hc, Bool.false_eq_true, ↓reduceIte, Dr_CV, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.mem_singleton, forall_eq,
      Dr_good, Dr_cv, Matrix.cons_val]
    refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> first | omega | simp
  · by_cases hr : w.countP PkgLetter.isRes = 0
    · simp only [pkgWordFac, hw, hc, hr, Bool.false_eq_true, ↓reduceIte, Dr_CV, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.mem_singleton, forall_eq,
        Dr_good, Dr_cv, Matrix.cons_val]
      refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> first | omega | simp [hr]
    · simp only [pkgWordFac, hw, hc, hr, Bool.false_eq_true, ↓reduceIte, Dr_CV, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.mem_singleton, forall_eq,
        Dr_good, Dr_cv, Matrix.cons_val]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> first | omega | simp
  · omega

/-- The resolvents minus the packages of a word with `Δ`, and the resolvents minus one of a loop. -/
private def Dr_G (w : List PkgLetter) : ℤ :=
  if w.any PkgLetter.isEnt then ((pkgSegs w).map fun σ => (σ.countP PkgLetter.isRes : ℤ) - 1).sum
  else (w.countP PkgLetter.isRes : ℤ) - 1

/-- The counts of a factor are nonnegative and satisfy the relations used in the rows. -/
private lemma Dr_cv_facts (f : PkgFac) :
    0 ≤ Dr_cv f 3 ∧ 0 ≤ Dr_cv f 4 ∧ 0 ≤ Dr_cv f 5 ∧ 0 ≤ Dr_cv f 6 ∧ 0 ≤ Dr_cv f 8 ∧
    0 ≤ Dr_cv f 9 ∧ Dr_cv f 6 ≤ Dr_cv f 3 ∧ Dr_cv f 5 ≤ Dr_cv f 9 ∧
    2 * (Dr_cv f 4 + Dr_cv f 5) + Dr_cv f 3 ≤ Dr_cv f 2 ∧
    (Dr_good f → 0 ≤ Dr_cv f 1 - Dr_cv f 0 + Dr_cv f 3 ∧
      (1 ≤ Dr_cv f 1 - Dr_cv f 0 + Dr_cv f 3 → 1 ≤ Dr_cv f 9)) := by
  cases f with
  | wt => simp [Dr_cv, Matrix.cons_val]
  | free r =>
    simp only [Dr_cv, Matrix.cons_val, Dr_good]
    split_ifs <;> omega
  | lam1 r =>
    simp only [Dr_cv, Matrix.cons_val, Dr_good]
    split_ifs <;> omega
  | lam0 g => cases g <;> simp [Dr_cv, Matrix.cons_val]
  | lam2 a c =>
    simp only [Dr_cv, Matrix.cons_val, Dr_good]
    split_ifs <;> omega
  | pair => simp [Dr_cv, Matrix.cons_val]

private lemma Dr_lsum_apply (L : List (Fin 10 → ℤ)) (k : Fin 10) :
    L.sum k = (L.map fun v => v k).sum := by
  induction L with
  | nil => simp
  | cons v L ih => simp [ih]

private lemma Dr_CV_flatMap {β : Type*} (L : List β) (g : β → List PkgFac) :
    Dr_CV (L.flatMap g) = (L.map fun w => Dr_CV (g w)).sum := by
  induction L with
  | nil => simp [Dr_CV]
  | cons w L ih => rw [List.flatMap_cons, Dr_CV_append, ih, List.map_cons, List.sum_cons]

private lemma Dr_CV_wt {β : Type*} (L : List β) (k : Fin 10) :
    Dr_CV (L.map fun _ => PkgFac.wt) k = L.length * Dr_cv .wt k := by
  induction L with
  | nil => simp [Dr_CV]
  | cons w L ih =>
    have e : Dr_CV ((w :: L).map fun _ => PkgFac.wt) = Dr_cv .wt + Dr_CV (L.map fun _ => .wt) := by
      simp [Dr_CV]
    rw [e, Pi.add_apply, ih, List.length_cons]
    push_cast
    ring

/-- The general relations of the counts of a list of factors. -/
private lemma Dr_gen (L : List PkgFac) (hg : ∀ f ∈ L, Dr_good f) :
    0 ≤ Dr_CV L 3 ∧ 0 ≤ Dr_CV L 4 ∧ 0 ≤ Dr_CV L 5 ∧ 0 ≤ Dr_CV L 6 ∧ 0 ≤ Dr_CV L 8 ∧
    0 ≤ Dr_CV L 9 ∧ Dr_CV L 6 ≤ Dr_CV L 3 ∧ Dr_CV L 5 ≤ Dr_CV L 9 ∧
    2 * (Dr_CV L 4 + Dr_CV L 5) + Dr_CV L 3 ≤ Dr_CV L 2 ∧
    0 ≤ Dr_CV L 1 - Dr_CV L 0 + Dr_CV L 3 ∧
    (1 ≤ Dr_CV L 1 - Dr_CV L 0 + Dr_CV L 3 → 1 ≤ Dr_CV L 9) := by
  simp only [Dr_CV_apply]
  have F := fun f => Dr_cv_facts f
  have s1 : ∀ k : Fin 10, (∀ f ∈ L, 0 ≤ Dr_cv f k) → 0 ≤ (L.map fun f => Dr_cv f k).sum :=
    fun k h => Dr_ls_nonneg L _ h
  have s2 : ∀ k k' : Fin 10, (∀ f ∈ L, Dr_cv f k ≤ Dr_cv f k') →
      (L.map fun f => Dr_cv f k).sum ≤ (L.map fun f => Dr_cv f k').sum :=
    fun k k' h => Dr_ls_le L _ _ h
  have hQ : (L.map fun f => Dr_cv f 1).sum - (L.map fun f => Dr_cv f 0).sum +
      (L.map fun f => Dr_cv f 3).sum =
      (L.map fun f => Dr_cv f 1 - Dr_cv f 0 + Dr_cv f 3).sum := by
    rw [Dr_ls_add, Dr_ls_sub]
  have h45 : 2 * ((L.map fun f => Dr_cv f 4).sum + (L.map fun f => Dr_cv f 5).sum) +
      (L.map fun f => Dr_cv f 3).sum =
      (L.map fun f => 2 * (Dr_cv f 4 + Dr_cv f 5) + Dr_cv f 3).sum := by
    rw [Dr_ls_add, ← Dr_ls_add L (fun f => Dr_cv f 4) (fun f => Dr_cv f 5)]
    simp only [List.sum_map_mul_left]
  refine ⟨s1 3 fun f _ => (F f).1, s1 4 fun f _ => (F f).2.1, s1 5 fun f _ => (F f).2.2.1,
    s1 6 fun f _ => (F f).2.2.2.1, s1 8 fun f _ => (F f).2.2.2.2.1,
    s1 9 fun f _ => (F f).2.2.2.2.2.1, s2 6 3 fun f _ => (F f).2.2.2.2.2.2.1,
    s2 5 9 fun f _ => (F f).2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · rw [h45]
    exact Dr_ls_le L _ _ fun f _ => (F f).2.2.2.2.2.2.2.2.1
  · rw [hQ]
    exact Dr_ls_nonneg L _ fun f hf => ((F f).2.2.2.2.2.2.2.2.2 (hg f hf)).1
  · intro h
    rw [hQ] at h
    obtain ⟨f, hf, h1⟩ := Dr_ls_exists L _ h
    have := ((F f).2.2.2.2.2.2.2.2.2 (hg f hf)).2 h1
    exact this.trans (Dr_ls_single L (fun f => Dr_cv f 9) (fun f _ => (F f).2.2.2.2.2.1) f hf)

/-- The counts of the factors of one word of a derivative structure. -/
private lemma Dr_wordV (T : LoopExpr) (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ)
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (w : List PkgLetter) (hw : w ∈ R.loops) :
    (∀ f ∈ pkgWordFac (fun _ => false) w, Dr_good f) ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 1 - Dr_CV (pkgWordFac (fun _ => false) w) 0 = Dr_G w ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 2 = w.countP PkgLetter.isLam ∧
    Dr_CV (pkgWordFac (fun _ => false) w) 7 = 0 ∧ Dr_CV (pkgWordFac (fun _ => false) w) 8 = 0 ∧
    (w.any PkgLetter.isEnt = true → Dr_CV (pkgWordFac (fun _ => false) w) 3 = 0) ∧
    (1 ≤ Dr_CV (pkgWordFac (fun _ => false) w) 4 + Dr_CV (pkgWordFac (fun _ => false) w) 5 →
      ∃ σ ∈ pkgSegs w, 2 ≤ σ.countP PkgLetter.isLam ∧ Dr_a σ = 0) ∧
    (1 ≤ Dr_CV (pkgWordFac (fun _ => false) w) 3 → w.any PkgLetter.isEnt = false ∧
      w.countP PkgLetter.isLam = 1 ∧ w.countP PkgLetter.isRes = 0) := by
  obtain ⟨-, hent, hfree⟩ := PS_shape T hT hf p q R hR
  by_cases hwe : w.any PkgLetter.isEnt = true
  · obtain ⟨he, hs⟩ := Dr_word_ent w hwe fun σ hσ => hent w hw hwe σ hσ
    rw [he]
    have ap : ∀ k : Fin 10, Dr_CV ((pkgSegs w).map pkgSegFac) k =
        ((pkgSegs w).map fun σ => Dr_cv (pkgSegFac σ) k).sum := fun k => by
      rw [Dr_CV_apply, List.map_map]; rfl
    have z : ∀ k : Fin 10, (∀ σ ∈ pkgSegs w, Dr_cv (pkgSegFac σ) k = 0) →
        Dr_CV ((pkgSegs w).map pkgSegFac) k = 0 := fun k h => by
      rw [ap]
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
        exact h σ hσ
    refine ⟨fun f hf' => ?_, ?_, ?_, z 7 fun σ hσ => (hs σ hσ).2.2.2.2.2.1,
      z 8 fun σ hσ => (hs σ hσ).2.2.2.2.2.2.1, fun _ => z 3 fun σ hσ => (hs σ hσ).2.2.2.1, ?_,
      ?_⟩
    · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hf'
      exact (hs σ hσ).1
    · rw [ap, ap, ← Dr_ls_sub, Dr_G, if_pos hwe]
      exact congrArg List.sum (List.map_congr_left fun σ hσ => (hs σ hσ).2.1)
    · rw [ap, ← PS_segs_lam w]
      push_cast
      rw [List.map_map]
      exact congrArg List.sum (List.map_congr_left fun σ hσ => (hs σ hσ).2.2.1)
    · intro h
      rw [ap, ap, ← Dr_ls_add] at h
      obtain ⟨σ, hσ, h1⟩ := Dr_ls_exists _ _ h
      exact ⟨σ, hσ, (hs σ hσ).2.2.2.2.2.2.2 h1⟩
    · intro h
      rw [z 3 fun σ hσ => (hs σ hσ).2.2.2.1] at h
      omega
  · have hwe' : w.any PkgLetter.isEnt = false := by simpa using hwe
    obtain ⟨h1, h0, -⟩ := hfree w hw hwe'
    obtain ⟨g, hq, hl, h45, h7, h8, h3⟩ := Dr_word_free w hwe' h1 h0
    refine ⟨g, by rw [hq, Dr_G, if_neg hwe], hl, h7, h8, fun h => absurd h hwe, fun h => ?_,
      fun h => ⟨hwe', h3 h⟩⟩
    omega

/-- The counts of the factors of a derivative structure with no paired letter. -/
private lemma Dr_prof (T : LoopExpr) (hT : T.wf = true) (hf : T.focus.isSome = true) (p q : ℕ)
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) :
    (∀ f ∈ R.profile (fun _ => false), Dr_good f) ∧
    Dr_CV (R.profile fun _ => false) 1 - Dr_CV (R.profile fun _ => false) 0 =
      (R.loops.map Dr_G).sum ∧
    Dr_CV (R.profile fun _ => false) 2 = 2 ∧ Dr_CV (R.profile fun _ => false) 7 = 0 ∧
    Dr_CV (R.profile fun _ => false) 8 = R.weights.length ∧
    (1 ≤ Dr_CV (R.profile fun _ => false) 4 + Dr_CV (R.profile fun _ => false) 5 →
      ∃ w ∈ R.loops, ∃ σ ∈ pkgSegs w, 2 ≤ σ.countP PkgLetter.isLam ∧ Dr_a σ = 0) ∧
    (1 ≤ Dr_CV (R.profile fun _ => false) 3 → ∃ w ∈ R.loops, w.any PkgLetter.isEnt = false ∧
      w.countP PkgLetter.isLam = 1 ∧ w.countP PkgLetter.isRes = 0) ∧
    (∀ w ∈ R.loops, w.any PkgLetter.isEnt = true →
      (w.countP PkgLetter.isLam : ℤ) ≤
        Dr_CV (R.profile fun _ => false) 2 - Dr_CV (R.profile fun _ => false) 3) := by
  obtain ⟨hsum, -, -⟩ := PS_shape T hT hf p q R hR
  have W := fun w (hw : w ∈ R.loops) => Dr_wordV T hT hf p q R hR w hw
  have hP : R.profile (fun _ => false) = R.weights.map (fun _ => PkgFac.wt) ++
      R.loops.flatMap (pkgWordFac fun _ => false) := rfl
  have ap : ∀ k : Fin 10, Dr_CV (R.profile fun _ => false) k =
      R.weights.length * Dr_cv .wt k +
        (R.loops.map fun w => Dr_CV (pkgWordFac (fun _ => false) w) k).sum := fun k => by
    rw [hP, Dr_CV_append, Pi.add_apply, Dr_CV_wt, Dr_CV_flatMap, Dr_lsum_apply, List.map_map]
    rfl
  have c : ∀ k : Fin 10, Dr_cv .wt k = if k = 8 then 1 else 0 := fun k => by
    fin_cases k <;> simp [Dr_cv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf'
    rw [hP] at hf'
    rcases List.mem_append.1 hf' with h | h
    · obtain ⟨-, -, rfl⟩ := List.mem_map.1 h
      trivial
    · obtain ⟨w, hw, hfw⟩ := List.mem_flatMap.1 h
      exact (W w hw).1 f hfw
  · rw [ap, ap, c, c]
    simp only [show ¬ ((1 : Fin 10) = 8) by decide, show ¬ ((0 : Fin 10) = 8) by decide,
      ↓reduceIte, mul_zero, zero_add]
    rw [← Dr_ls_sub]
    exact congrArg List.sum (List.map_congr_left fun w hw => (W w hw).2.1)
  · rw [ap, c]
    simp only [show ¬ ((2 : Fin 10) = 8) by decide, ↓reduceIte, mul_zero, zero_add]
    rw [List.map_congr_left fun w hw => (W w hw).2.2.1,
      show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, ← hsum, Nat.cast_list_sum, List.map_map]
    rfl
  · rw [ap, c]
    simp only [show ¬ ((7 : Fin 10) = 8) by decide, ↓reduceIte, mul_zero, zero_add]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact (W w hw).2.2.2.1
  · rw [ap, c]
    simp only [↓reduceIte, mul_one]
    rw [List.sum_eq_zero fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact (W w hw).2.2.2.2.1]
    simp
  · intro h
    rw [ap, ap, c, c] at h
    simp only [show ¬ ((4 : Fin 10) = 8) by decide, show ¬ ((5 : Fin 10) = 8) by decide,
      ↓reduceIte, mul_zero, zero_add] at h
    rw [← Dr_ls_add] at h
    obtain ⟨w, hw, h1⟩ := Dr_ls_exists _ _ h
    obtain ⟨σ, hσ, h2⟩ := (W w hw).2.2.2.2.2.2.1 h1
    exact ⟨w, hw, σ, hσ, h2⟩
  · intro h
    rw [ap, c] at h
    simp only [show ¬ ((3 : Fin 10) = 8) by decide, ↓reduceIte, mul_zero, zero_add] at h
    obtain ⟨w, hw, h1⟩ := Dr_ls_exists _ _ h
    exact ⟨w, hw, (W w hw).2.2.2.2.2.2.2 h1⟩
  · intro w hw hwe
    rw [ap, ap, c, c]
    simp only [show ¬ ((2 : Fin 10) = 8) by decide, show ¬ ((3 : Fin 10) = 8) by decide,
      ↓reduceIte, mul_zero, zero_add]
    rw [← Dr_ls_sub]
    have hnn : ∀ v ∈ R.loops, 0 ≤ Dr_CV (pkgWordFac (fun _ => false) v) 2 -
        Dr_CV (pkgWordFac (fun _ => false) v) 3 := fun v hv => by
      have := (Dr_gen _ (W v hv).1).2.2.2.2.2.2.2.2.1
      have := (Dr_gen _ (W v hv).1).2.2.1
      have := (Dr_gen _ (W v hv).1).2.1
      omega
    have := Dr_ls_single R.loops (fun v => Dr_CV (pkgWordFac (fun _ => false) v) 2 -
        Dr_CV (pkgWordFac (fun _ => false) v) 3) hnn w hw
    simp only at this
    rw [(W w hw).2.2.1, (W w hw).2.2.2.2.2.1 hwe] at this
    simpa using this

/-! ### The counts of a derivative structure from the characters of `𝒯` -/

private lemma Dr_res_map (w : List LoopLetter) :
    (w.map PkgLetter.lw).countP PkgLetter.isRes =
      w.countP fun x => match x with | .res _ => true | _ => false := by
  rw [List.countP_map]
  congr 1
  funext x
  cases x <;> rfl

private lemma Dr_ent_map (w : List LoopLetter) :
    (w.map PkgLetter.lw).countP PkgLetter.isEnt = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  simp [PkgLetter.isEnt]

private lemma Dr_countP_sum {α : Type*} (L : List α) (P : α → Bool) :
    (L.countP P : ℤ) = (L.map fun x => if P x then (1 : ℤ) else 0).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons]
    push_cast
    rw [ih]
    split_ifs <;> ring

/-- The resolvent pattern of a loop letter. -/
private abbrev Dr_pat : LoopLetter → Bool := fun x => match x with | .res _ => true | _ => false

/-- The words of `𝒯.pkgStart`: their resolvents are those of `𝒯`, they have one letter `Δ`, and
there are as many as loops of `𝒯`. -/
private lemma Dr_start_sums (T : LoopExpr) (hT : T.wf = true) (ℓ : ℕ) (a : Fin 2)
    (tl : List LoopLetter) (hf : T.focus = some (ℓ, a, tl)) :
    (T.pkgStart.loops.map fun w => (w.countP PkgLetter.isRes : ℤ)).sum = T.charsZ.1 ∧
    (T.pkgStart.loops.map fun w => (w.countP PkgLetter.isEnt : ℤ)).sum = 1 ∧
    T.pkgStart.loops.length = T.loops.length := by
  obtain ⟨w, -, -, hw, hperm, -⟩ := focus_shape hT hf
  have hℓ : ℓ < T.loops.length := (List.getElem?_eq_some_iff.1 hw).1
  have hwe : T.loops[ℓ] = w := (List.getElem?_eq_some_iff.1 hw).2
  have hs : T.pkgStart.loops = (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map
      PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
        (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw := by
    simp [LoopExpr.pkgStart, hf]
  have hp := List.getElem_cons_eraseIdx_perm hℓ
  rw [hwe] at hp
  have hm : T.charsZ.1 = (((T.loops.map fun v => v.countP Dr_pat).sum : ℕ) : ℤ) := rfl
  have hsumT := (hp.map fun v => v.countP Dr_pat).sum_eq
  have hw1 := hperm.countP_eq Dr_pat
  have hmain : (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw) ++
      [PkgLetter.ent 1 0]).countP PkgLetter.isRes = tl.countP Dr_pat + 1 := by
    rw [List.countP_append, Dr_res_map]
    simp [List.countP_cons, List.countP_append, PkgLetter.isRes]
  have hw2 : w.countP Dr_pat = tl.countP Dr_pat + 1 := by
    rw [hw1, List.countP_cons]
    simp
  have hrest : ((T.loops.eraseIdx ℓ).map fun v => (((v.map PkgLetter.lw).countP
      PkgLetter.isRes : ℕ) : ℤ)) = (T.loops.eraseIdx ℓ).map fun v => ((v.countP Dr_pat : ℕ) : ℤ) :=
    List.map_congr_left fun v _ => by rw [Dr_res_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, hm, ← hsumT]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    rw [hmain, hrest, hw2]
    push_cast [Nat.cast_list_sum, List.map_map, Function.comp_def]
    ring
  · rw [hs]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, List.countP_append,
      Dr_ent_map]
    simp [PkgLetter.isEnt]
  · rw [hs]
    simp [List.length_eraseIdx_of_lt hℓ]
    omega

/-- The resolvents of a word, as an integer. -/
private def Dr_rs (x : List PkgLetter) : ℤ := (x.countP PkgLetter.isRes : ℤ)

/-- The letters `Δ` of a word, as an integer. -/
private def Dr_es (x : List PkgLetter) : ℤ := (x.countP PkgLetter.isEnt : ℤ)

/-- `1` for a word with a letter `Δ`. -/
private def Dr_ind (x : List PkgLetter) : ℤ := if x.any PkgLetter.isEnt then 1 else 0

private lemma Dr_free_of (w : List PkgLetter) (h : w.any PkgLetter.isEnt = false) :
    ∀ z ∈ w, PkgLetter.isEnt z = false := fun z hz => by
  simpa using List.any_eq_false.1 h z hz

private lemma Dr_cnt0 (w : List PkgLetter) (h : w.any PkgLetter.isEnt = false) :
    w.countP PkgLetter.isEnt = 0 :=
  List.countP_eq_zero.2 fun z hz => by simp [Dr_free_of w h z hz]

/-- (5.67) [eq:sumai] summed over the words, with Table 1 [table_effect_of_operations]: the
resolvents minus the factors of a derivative structure are `m - n` of `𝒯` plus the number of hit
loops and light weights, which is the increase of `S`; the light weights of `𝒯` are those of the
structure and the hit ones. -/
private lemma Dr_KS (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hTr : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) (hT : T.wf = true)
    (ℓ : ℕ) (a : Fin 2) (tl : List LoopLetter) (hfoc : T.focus = some (ℓ, a, tl)) (p q : ℕ)
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) :
    (R.loops.map Dr_G).sum = T.charsZ.1 - T.charsZ.2.1 + (R.S - T.S) ∧
    (T.weights.length : ℤ) ≤ R.weights.length + (R.S - T.S) ∧ (T.S : ℤ) ≤ R.S := by
  obtain ⟨hc1, ⟨hs, hperm, hc2⟩, -, hc4, hc5, -, -, -, -, -, hS⟩ :=
    pkg_dwirt_words T hT ℓ a tl hfoc 0 1 p q R hR
  obtain ⟨hsr, hse, hsl⟩ := Dr_start_sums T hT ℓ a tl hfoc
  have hcoll : R.loops.map pkgColl = T.pkgStart.loops ++
      hs.map (fun y => [.lw (.res y.1), .lw (.proj y.2)]) := by
    rw [← List.take_append_drop T.pkgStart.loops.length R.loops, List.map_append, hc1, hc2]
  have hlen : R.loops.length = T.loops.length + hs.length := by
    have := congrArg List.length hcoll
    simp only [List.length_map, List.length_append] at this
    omega
  have hwW : ∀ y : Fin 2 × ℕ, Dr_rs [.lw (.res y.1), .lw (.proj y.2)] = 1 ∧
      Dr_es [.lw (.res y.1), .lw (.proj y.2)] = 0 := fun y => by
    simp [Dr_rs, Dr_es, List.countP_cons, PkgLetter.isRes, PkgLetter.isEnt]
  have hsumC : ((R.loops.map pkgColl).map Dr_rs).sum = T.charsZ.1 + hs.length ∧
      ((R.loops.map pkgColl).map Dr_es).sum = 1 := by
    rw [hcoll, List.map_append, List.map_append, List.sum_append, List.sum_append, List.map_map,
      List.map_map]
    have e1 : (hs.map (Dr_rs ∘ fun y => [.lw (.res y.1), .lw (.proj y.2)])).sum = hs.length := by
      rw [show (Dr_rs ∘ fun y : Fin 2 × ℕ => [PkgLetter.lw (.res y.1), .lw (.proj y.2)]) =
        fun _ => (1 : ℤ) from funext fun y => (hwW y).1]
      simp
    have e2 : (hs.map (Dr_es ∘ fun y => [.lw (.res y.1), .lw (.proj y.2)])).sum = 0 := by
      rw [show (Dr_es ∘ fun y : Fin 2 × ℕ => [PkgLetter.lw (.res y.1), .lw (.proj y.2)]) =
        fun _ => (0 : ℤ) from funext fun y => (hwW y).2]
      simp
    refine ⟨?_, ?_⟩
    · rw [e1, ← hsr]; rfl
    · rw [e2, add_zero, ← hse]; rfl
  have hes1 : ∀ x ∈ R.loops.map pkgColl, Dr_es x ≤ 1 := fun x hx => by
    have := Dr_ls_single _ Dr_es (fun y _ => by simp [Dr_es]) x hx
    rw [hsumC.2] at this
    exact this
  have hind_es : ∀ x ∈ R.loops.map pkgColl, Dr_ind x = Dr_es x := fun x hx => by
    have h1 := hes1 x hx
    simp only [Dr_ind, Dr_es] at h1 ⊢
    by_cases h : x.any PkgLetter.isEnt = true
    · have : 0 < x.countP PkgLetter.isEnt := List.countP_pos_iff.2 (by simpa using h)
      simp only [h, ↓reduceIte]
      omega
    · have h' : x.countP PkgLetter.isEnt = 0 := Dr_cnt0 x (by simpa using h)
      simp [h, h']
  -- one word
  have hG : ∀ w ∈ R.loops, Dr_G w = Dr_rs (pkgColl w) - Dr_es (pkgColl w) - (1 - Dr_ind w) := by
    intro w hw
    by_cases hwe : w.any PkgLetter.isEnt = true
    · have h4 := hc4 w hw hwe
      have h4' : ((pkgSegs w).map fun σ => (σ.countP PkgLetter.isRes : ℤ)).sum +
          Dr_es (pkgColl w) = Dr_rs (pkgColl w) + (pkgSegs w).length := by
        have := congrArg (Nat.cast : ℕ → ℤ) h4
        push_cast [Nat.cast_list_sum, List.map_map] at this
        simpa [Dr_es, Dr_rs, Function.comp_def] using this
      rw [Dr_G, if_pos hwe, Dr_ls_sub]
      simp only [Dr_ind, hwe, ↓reduceIte, List.map_const', List.sum_replicate, nsmul_eq_mul,
        mul_one]
      linarith
    · have hwe' : w.any PkgLetter.isEnt = false := by simpa using hwe
      rw [Dr_G, if_neg hwe, pkgColl_free w (Dr_free_of w hwe')]
      simp only [Dr_rs, Dr_es, Dr_ind, hwe', Bool.false_eq_true, ↓reduceIte, Dr_cnt0 w hwe']
      push_cast
      ring
  have hind_le : ∀ w ∈ R.loops, Dr_ind (pkgColl w) ≤ Dr_ind w := by
    intro w hw
    by_cases hwe : w.any PkgLetter.isEnt = true
    · simp only [Dr_ind, hwe, ↓reduceIte]
      split_ifs <;> norm_num
    · rw [pkgColl_free w (Dr_free_of w (by simpa using hwe))]
  -- the increase of `S`
  have hh : R.S - T.S = (R.loops.map fun w => Dr_ind w - Dr_ind (pkgColl w)).sum := by
    rw [hS, add_sub_cancel_left, Dr_countP_sum]
    congr 1
    refine List.map_congr_left fun w hw => ?_
    have := hind_le w hw
    simp only [Dr_ind] at this ⊢
    split_ifs at this ⊢ <;> simp_all
  have hsumG : (R.loops.map Dr_G).sum =
      ((R.loops.map pkgColl).map Dr_rs).sum - ((R.loops.map pkgColl).map Dr_es).sum -
        R.loops.length + (R.loops.map Dr_ind).sum := by
    rw [List.map_congr_left hG, Dr_ls_sub, Dr_ls_sub, Dr_ls_sub, List.map_map, List.map_map]
    simp only [Function.comp_def, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
    ring
  have hsumI : (R.loops.map fun w => Dr_ind (pkgColl w)).sum = 1 := by
    have : (R.loops.map fun w => Dr_ind (pkgColl w)) = (R.loops.map pkgColl).map Dr_ind := by
      rw [List.map_map]; rfl
    rw [this, List.map_congr_left hind_es, hsumC.2]
  have hcharN : T.charsZ.2.1 = (T.loops.length : ℤ) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsumG, hh, hsumC.1, hsumC.2, hlen, hcharN, Dr_ls_sub, hsumI]
    push_cast
    ring
  · -- the hit light weights give words with `Δ` whose collapse has none
    have hwl : (T.weights.length : ℤ) = R.weights.length + hs.length := by
      have := hperm.length_eq
      simp only [List.length_append] at this
      omega
    have hdrop : ∀ w ∈ R.loops.drop T.pkgStart.loops.length, (w.any PkgLetter.isEnt &&
        !(pkgColl w).any PkgLetter.isEnt) = true := by
      intro w hw
      have hwc : pkgColl w ∈ hs.map (fun y => [.lw (.res y.1), .lw (.proj y.2)]) := by
        rw [← hc2]; exact List.mem_map.2 ⟨w, hw, rfl⟩
      obtain ⟨y, -, hy⟩ := List.mem_map.1 hwc
      have hc0 : (pkgColl w).any PkgLetter.isEnt = false := by
        rw [← hy]; simp [PkgLetter.isEnt]
      rw [hc0]
      by_contra hne
      have hwe' : w.any PkgLetter.isEnt = false := by simpa using hne
      obtain ⟨w₀, hw₀, rfl⟩ := hc5 w (List.mem_of_mem_drop hw) hwe'
      rw [pkgColl_free _ (Dr_free_of _ hwe')] at hy
      have hw₀' : w₀ = [.res y.1, .proj y.2] := by
        apply List.map_injective_iff.2 (fun a b h => PkgLetter.lw.inj h)
        rw [← hy]
        simp
      have := loop_free_two ε n T hTr w₀ hw₀ (by rw [hw₀']; simp) (by rw [hw₀']; simp)
      rw [hw₀'] at this
      simp at this
    have h1 : ((R.loops.drop T.pkgStart.loops.length).countP fun w => w.any PkgLetter.isEnt &&
        !(pkgColl w).any PkgLetter.isEnt) = hs.length := by
      rw [List.countP_eq_length.2 hdrop]
      have := congrArg List.length hc2
      simpa using this
    have h2 := (List.drop_sublist T.pkgStart.loops.length R.loops).countP_le
      (p := fun w => w.any PkgLetter.isEnt && !(pkgColl w).any PkgLetter.isEnt)
    rw [hS]
    push_cast
    omega
  · rw [hS]
    push_cast
    omega

/-! ### The letters `Λ̃`, the main word and the counts `k₁`, `k₂` -/

/-- The number of resolvents cyclically to the left of `Λ̃_x` up to the other `Λ̃`, in one loop:
the term of `k₁`, `k₂` of (5.34) [Gamma_Type_1] and (5.35) [Gamma_Type_2]. -/
private def Dr_F (x : Fin 2) (w : List LoopLetter) : ℕ :=
  ((((w.rotate (w.idxOf (.lamt x))).drop 1).reverse.takeWhile fun y =>
      match y with | .lamt _ => false | _ => true).countP Dr_pat)

private lemma Dr_kk_def (T : LoopExpr) (x : Fin 2) :
    T.kk x = (T.loops.map fun w => if w.contains (.lamt x) then Dr_F x w else 0).sum := rfl

private lemma Dr_F_le (x : Fin 2) (w : List LoopLetter) : Dr_F x w ≤ w.countP Dr_pat := by
  unfold Dr_F
  calc _ ≤ (((w.rotate (w.idxOf (.lamt x))).drop 1).reverse).countP Dr_pat :=
        (List.takeWhile_sublist _).countP_le
    _ = ((w.rotate (w.idxOf (.lamt x))).drop 1).countP Dr_pat := List.countP_reverse
    _ ≤ (w.rotate (w.idxOf (.lamt x))).countP Dr_pat := (List.drop_sublist _ _).countP_le
    _ = w.countP Dr_pat := (List.rotate_perm _ _).countP_eq _

/-- In the class `𝒯` the loop of `Λ̃_x` is unique, and `k_x` is its term. -/
private lemma Dr_kk_eq (T : LoopExpr) (hT : T.wf = true) (x : Fin 2) (w₀ : List LoopLetter)
    (hw₀ : w₀ ∈ T.loops) (hx : LoopLetter.lamt x ∈ w₀) :
    T.kk x = Dr_F x w₀ ∧ w₀.count (.lamt x) = 1 := by
  have hcnt : (T.loops.map fun w => w.count (.lamt x)).sum = 1 := by
    simp only [LoopExpr.wf, Bool.and_eq_true, beq_iff_eq] at hT
    fin_cases x
    · exact hT.1.1.1.1
    · exact hT.1.1.1.2
  have hp := List.perm_cons_erase hw₀
  have hs := (hp.map fun w => w.count (.lamt x)).sum_eq
  rw [hcnt, List.map_cons, List.sum_cons] at hs
  have h1 : 1 ≤ w₀.count (.lamt x) := List.count_pos_iff.2 hx
  have hz : ∀ v ∈ T.loops.erase w₀, v.contains (.lamt x) = false := by
    intro v hv
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count (.lamt x)) hv)
    have h0 : v.count (.lamt x) = 0 := by omega
    simpa [List.count_eq_zero] using h0
  refine ⟨?_, by omega⟩
  rw [Dr_kk_def, (hp.map _).sum_eq, List.map_cons, List.sum_cons]
  rw [List.sum_eq_zero fun y hy => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hy
    have : ¬ (LoopLetter.lamt x ∈ v) := by simpa using hz v hv
    simp [this]]
  simp [hx]

private lemma Dr_rot_one (x : LoopLetter) (u : List LoopLetter) (hu : u.count x = 1) :
    (u.rotate 1).rotate ((u.rotate 1).idxOf x) = u.rotate (u.idxOf x) := by
  rcases u with _ | ⟨y, u'⟩
  · simp at hu
  · rw [List.rotate_cons_succ, List.rotate_zero]
    by_cases hy : y = x
    · subst hy
      have hn : y ∉ u' := by
        rw [List.count_cons_self] at hu
        exact List.count_eq_zero.1 (by omega)
      rw [List.idxOf_append_of_notMem hn, List.idxOf_cons_self, add_zero,
        List.rotate_append_length_eq, List.idxOf_cons_self, List.rotate_zero]
      rfl
    · have hm : x ∈ u' := by
        have : u'.count x = 1 := by simpa [List.count_cons, hy] using hu
        exact List.count_pos_iff.1 (by omega)
      rw [List.idxOf_append_of_mem hm, List.idxOf_cons_ne _ hy, List.rotate_cons_succ]

private lemma Dr_rot_inv (x : LoopLetter) (v : List LoopLetter) (hv : v.count x = 1) :
    ∀ r, (v.rotate r).rotate ((v.rotate r).idxOf x) = v.rotate (v.idxOf x)
  | 0 => by rw [List.rotate_zero]
  | r + 1 => by
    have hc : (v.rotate r).count x = 1 := by rw [((List.rotate_perm v r).count_eq x), hv]
    rw [← List.rotate_rotate, Dr_rot_one x _ hc, Dr_rot_inv x v hv r]

private lemma Dr_F_rot (x : Fin 2) (w : List LoopLetter) (hw : w.count (.lamt x) = 1) (r : ℕ) :
    Dr_F x (w.rotate r) = Dr_F x w := by
  unfold Dr_F
  rw [Dr_rot_inv _ w hw r]

private lemma Dr_F_comp (x o : Fin 2) (C A B : List LoopLetter)
    (hP : LoopLetter.lamt x ∉ C ++ LoopLetter.lamt o :: A)
    (hA : ∀ z ∈ A, ∀ b, z ≠ .lamt b) :
    Dr_F x ((C ++ .lamt o :: A) ++ .lamt x :: B) = A.countP Dr_pat := by
  unfold Dr_F
  rw [List.idxOf_append_of_notMem hP, List.idxOf_cons_self, add_zero,
    List.rotate_append_length_eq]
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.reverse_append,
    List.reverse_cons, List.append_assoc]
  rw [List.takeWhile_append_of_pos]
  · simp
  · intro z hz
    rw [List.mem_reverse] at hz
    rcases z with b | b | b | b
    · rfl
    · rfl
    · rfl
    · exact absurd rfl (hA _ hz b)

private lemma Dr_count_lam (l : List PkgLetter) :
    l.countP PkgLetter.isLam = l.count (.lw (.lamt 0)) + l.count (.lw (.lamt 1)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.countP_cons, List.count_cons, List.count_cons, ih]
    rcases x with ((b | b | b | b) | ⟨u, v⟩)
    · simp [PkgLetter.isLam]
    · simp [PkgLetter.isLam]
    · simp [PkgLetter.isLam]
    · fin_cases b <;> simp [PkgLetter.isLam] <;> omega
    · simp [PkgLetter.isLam]

private lemma Dr_split_uniq {α : Type*} (x : α) (X Y X' Y' : List α) (hX : x ∉ X) (hX' : x ∉ X')
    (h : X ++ x :: Y = X' ++ x :: Y') : X = X' ∧ Y = Y' := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · rcases as with _ | ⟨c, as⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at h1 h2
      exact ⟨h1.symm, h2.2⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      exact absurd (by rw [h1, ← h2.1]; simp) hX'
  · rcases bs with _ | ⟨c, bs⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at h1 h2
      exact ⟨h1, h2.2.symm⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      exact absurd (by rw [h1, ← h2.1]; simp) hX

private lemma Dr_coll_pre (H Y : List PkgLetter) (hH : ∀ z ∈ H, PkgLetter.isRes z = false) :
    pkgColl (H ++ Y) = H ++ pkgColl Y := by
  induction H with
  | nil => rfl
  | cons x H ih =>
    have hx := hH x List.mem_cons_self
    rw [List.cons_append, List.cons_append, ← ih fun z hz => hH z (List.mem_cons_of_mem _ hz)]
    rcases x with ((b | b | b | b) | ⟨u, v⟩)
    · simp [PkgLetter.isRes] at hx
    all_goals rfl

private lemma Dr_splitOnP_prefix (p : PkgLetter → Bool) :
    ∀ (Q σ : List PkgLetter) (L : List (List PkgLetter)), Q.splitOnP p = σ :: L →
      ∃ Z, Q = σ ++ Z
  | [], σ, L, h => by
    rw [List.splitOnP_nil, List.cons.injEq] at h
    exact ⟨[], by rw [← h.1]; rfl⟩
  | x :: Q, σ, L, h => by
    rw [List.splitOnP_cons_eq_ite_modifyHead] at h
    split_ifs at h with hx
    · rw [List.cons.injEq] at h
      exact ⟨x :: Q, by rw [← h.1]; rfl⟩
    · rcases hQ : Q.splitOnP p with _ | ⟨σ', L'⟩
      · exact absurd hQ (List.splitOnP_ne_nil _ _)
      · rw [hQ, List.modifyHead_cons, List.cons.injEq] at h
        obtain ⟨Z, hZ⟩ := Dr_splitOnP_prefix p Q σ' L' hQ
        exact ⟨Z, by rw [← h.1, hZ]; rfl⟩

/-- The words of a derivative structure carry each `Λ̃` once. -/
private lemma Dr_R_lam (T : LoopExpr) (hT : T.wf = true) (ℓ : ℕ) (a : Fin 2)
    (tl : List LoopLetter) (hfoc : T.focus = some (ℓ, a, tl)) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (x : Fin 2) :
    (R.loops.map fun w => w.count (.lw (.lamt x))).sum = 1 := by
  have hwf : R.wf = true := by
    unfold PkgExpr.dwirt at hR
    refine PS_dwirt_wf 0 1 p _ (PS_dwirt_wf 1 0 q _ ?_) R hR
    intro R' hR'
    rw [List.mem_singleton] at hR'
    subst hR'
    exact pkgStart_wf hT hfoc
  simp only [PkgExpr.wf, Bool.and_eq_true, beq_iff_eq] at hwf
  fin_cases x
  · exact hwf.1.1.1.1
  · exact hwf.1.1.1.2

private lemma Dr_seg_cnt (w σ : List PkgLetter) (hσ : σ ∈ pkgSegs w) (x : Fin 2) :
    σ.count (.lw (.lamt x)) ≤ w.count (.lw (.lamt x)) := by
  rw [← PS_seg_count (.lw (.lamt x)) rfl w]
  exact List.le_sum_of_mem (List.mem_map_of_mem hσ)

/-- The main word of a derivative structure of (5.66)
[R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression] and the focus (5.38) [explicit_cT]: the
loop of `Λ̃_o` is a rotation of `𝒢_a tl₀ Λ̃_o tl₁` with no resolvent and no `Λ̃` in `tl₀`; the main
word is `𝔐_a tl₀ Λ̃_o Q Δ` with `Q Δ` collapsing to `tl₁ 𝒢_a Δ`. -/
private lemma Dr_main (T : LoopExpr) (hT : T.wf = true) (ℓ : ℕ) (a : Fin 2)
    (tl : List LoopLetter) (hfoc : T.focus = some (ℓ, a, tl)) (p q : ℕ) (R : PkgExpr)
    (hR : R ∈ T.pkgStart.dwirt 0 1 p q) :
    ∃ (w₀ tl₀ tl₁ : List LoopLetter) (Q : List PkgLetter) (rest : List (List PkgLetter)) (r : ℕ),
      T.loops[ℓ]? = some w₀ ∧ w₀.rotate r = .res a :: tl ∧
      tl = tl₀ ++ .lamt (if 1 ≤ T.kk 0 then 0 else 1) :: tl₁ ∧ (∀ z ∈ tl₀, Dr_pat z = false) ∧
      (∀ z ∈ tl₀, ∀ b, z ≠ .lamt b) ∧
      R.loops = (((LoopLetter.det a :: tl₀).map PkgLetter.lw ++
        [.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))]) ++ Q ++ [.ent 1 0]) :: rest ∧
      pkgColl (Q ++ [.ent 1 0]) = (tl₁ ++ [LoopLetter.res a]).map PkgLetter.lw ++ [.ent 1 0] := by
  obtain ⟨w₀, tl₀, tl₁, hw, hperm, he, hfree, hnl⟩ := focus_shape hT hfoc
  obtain ⟨-, tl₀', tl₁', -, -, -, he', hlam⟩ := focus_lam hT _ rfl hfoc
  obtain ⟨h0, h1⟩ := Dr_split_uniq _ tl₀ tl₁ tl₀' tl₁' hnl (by
    intro hm
    have := hlam _ hm
    simp [isLamL] at this) (he.symm.trans he')
  subst h0 h1
  -- the rotation of the focus
  obtain ⟨w₁, r, hw₁, hrot⟩ : ∃ w r, T.loops[ℓ]? = some w ∧ w.rotate r = .res a :: tl := by
    unfold LoopExpr.focus at hfoc
    dsimp only at hfoc
    generalize (if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = o at hfoc
    split at hfoc
    · cases hfoc
    · rename_i w hw'
      split at hfoc
      · cases hfoc
      · rename_i r' hr'
        split at hfoc
        · rename_i a' tl' hrot
          split at hfoc
          · simp only [Option.some.injEq, Prod.mk.injEq] at hfoc
            obtain ⟨rfl, rfl, rfl⟩ := hfoc
            exact ⟨w, r', hw', hrot⟩
          · cases hfoc
        · cases hfoc
  rw [hw] at hw₁
  obtain rfl := Option.some.inj hw₁
  -- the shape invariant
  set H : List PkgLetter := (LoopLetter.det a :: tl₀).map PkgLetter.lw ++
    [.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))] with hHdef
  have hH : ∀ z ∈ H, PkgLetter.isRes z = false := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · have := hfree x hx
        revert this
        cases x <;> simp [PkgLetter.isRes, isResL]
    · rw [List.mem_singleton] at hz
      subst hz
      rfl
  have hI0 := ShapeInv.start hfoc hw hperm he
  unfold PkgExpr.dwirt at hR
  have h1 := ShapeInv.iter hH (T := T) 1 0 q 1 [T.pkgStart]
    (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hI0)
  have h2 := ShapeInv.iter hH (T := T) 0 1 p (1 + q) _ h1 R hR
  obtain ⟨Q, rest, hL⟩ := ShapeInv.main h2
  refine ⟨w₀, tl₀, tl₁, Q, rest, r, hw, hrot, he, fun z hz => ?_, fun z hz b hb => ?_, hL, ?_⟩
  · have := hfree z hz
    revert this
    cases z <;> simp [isResL]
  · subst hb
    have := hlam _ hz
    simp [isLamL] at this
  · -- the collapse of the main word is the main word of `𝒯.pkgStart`
    obtain ⟨hc1, -⟩ :=
      pkg_dwirt_words T hT ℓ a tl hfoc 0 1 p q R (by unfold PkgExpr.dwirt; exact hR)
    have hs : T.pkgStart.loops = (((LoopLetter.det a :: tl ++ [LoopLetter.res a]).map
        PkgLetter.lw) ++ [PkgLetter.ent 1 0]) ::
          (T.loops.eraseIdx ℓ).map fun w => w.map PkgLetter.lw := by
      simp [LoopExpr.pkgStart, hfoc]
    have hpos : 0 < T.pkgStart.loops.length := by rw [hs]; simp
    have hh := congrArg List.head? hc1
    obtain ⟨k, hk⟩ : ∃ k, T.pkgStart.loops.length = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hL, hk] at hh
    simp only [List.take_succ_cons, List.map_cons, List.head?_cons] at hh
    rw [hs, List.head?_cons, Option.some.injEq] at hh
    rw [List.append_assoc, Dr_coll_pre H _ hH] at hh
    have e : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).map PkgLetter.lw ++
        [PkgLetter.ent 1 0] =
        H ++ ((tl₁ ++ [LoopLetter.res a]).map PkgLetter.lw ++ [PkgLetter.ent 1 0]) := by
      rw [he, hHdef]
      simp
    rw [e] at hh
    exact List.append_cancel_left hh

private lemma Dr_lw_mem (w₀ : List LoopLetter) (x : LoopLetter)
    (h : 1 ≤ (w₀.map PkgLetter.lw).count (.lw x)) :
    x ∈ w₀ := by
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 (List.count_pos_iff.1 h)
  cases hyx
  exact hy

private lemma Dr_isLam_lw (b : LoopLetter) (h : PkgLetter.isLam (.lw b) = true) :
    ∃ x, b = .lamt x := by
  cases b <;> simp_all [PkgLetter.isLam]

/-- A loop without `Δ`, with one `Λ̃` and no resolvent, a factor `lam0`, occurs only in case (iv)
of the direct estimation in the proof of Lemma 5.5 [claim_estimate_remainder_terms]: Type II with
`k₁ = 0`. -/
private lemma Dr_L0 (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hTr : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) (hT : T.wf = true)
    (ℓ : ℕ) (a : Fin 2) (tl : List LoopLetter) (hfoc : T.focus = some (ℓ, a, tl)) (p q : ℕ)
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (w : List PkgLetter) (hw : w ∈ R.loops)
    (hwe : w.any PkgLetter.isEnt = false) (h1 : w.countP PkgLetter.isLam = 1)
    (h0 : w.countP PkgLetter.isRes = 0) :
    T.typeI = false ∧ T.kk 0 = 0 := by
  obtain ⟨-, tl₀, -, Q, rest, -, -, -, -, -, -, hL, -⟩ := Dr_main T hT ℓ a tl hfoc p q R hR
  obtain ⟨-, -, -, -, hc5, h6, -, -, -, -, -⟩ := pkg_dwirt_words T hT ℓ a tl hfoc 0 1 p q R hR
  have hoo : ((if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = 0 ∧
      (if 1 ≤ T.kk 0 then (1 : Fin 2) else 0) = 1)
      ∨ ((if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = 1 ∧
        (if 1 ≤ T.kk 0 then (1 : Fin 2) else 0) = 0) := by
    by_cases h : 1 ≤ T.kk 0 <;> simp [h]
  set o : Fin 2 := if 1 ≤ T.kk 0 then 0 else 1 with ho
  set o' : Fin 2 := if 1 ≤ T.kk 0 then 1 else 0 with ho'
  set hd := ((LoopLetter.det a :: tl₀).map PkgLetter.lw ++ [.lw (.lamt o)]) ++ Q ++ [.ent 1 0]
    with hhd
  have hdo : 1 ≤ hd.count (.lw (.lamt o)) := List.count_pos_iff.2 (by simp [hhd])
  have hdent : hd.any PkgLetter.isEnt = true := by simp [hhd, PkgLetter.isEnt]
  have hwrest : w ∈ rest := by
    rw [hL] at hw
    rcases List.mem_cons.1 hw with rfl | h
    · rw [hdent] at hwe; exact absurd hwe (by simp)
    · exact h
  have hsum := Dr_R_lam T hT ℓ a tl hfoc p q R hR o
  rw [hL, List.map_cons, List.sum_cons] at hsum
  have hwo : w.count (.lw (.lamt o)) = 0 := by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count (.lw (.lamt o))) hwrest)
    omega
  have hwo' : 1 ≤ w.count (.lw (.lamt o')) := by
    rw [Dr_count_lam] at h1
    rcases hoo with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hwo <;> rw [h'] <;> omega
  refine ⟨?_, ?_⟩
  · by_contra hI
    have hI' : T.typeI = true := by simpa using hI
    obtain ⟨w', hw', hc⟩ := h6 hI'
    rw [hL, List.head?_cons, Option.mem_def, Option.some.injEq] at hw'
    subst hw'
    have hmem : PkgLetter.lw (.lamt o') ∈ hd :=
      List.mem_of_mem_drop (List.contains_iff_mem.1 hc)
    have hsum' := Dr_R_lam T hT ℓ a tl hfoc p q R hR o'
    rw [hL, List.map_cons, List.sum_cons] at hsum'
    have := List.le_sum_of_mem
      (List.mem_map_of_mem (f := fun w => w.count (.lw (.lamt o'))) hwrest)
    have := List.count_pos_iff.2 hmem
    omega
  · by_contra hk
    have hk1 : 1 ≤ T.kk 0 := by omega
    have hk2 := (loop_reach ε n T hTr).2.1 hk1
    have ho1 : o' = 1 := by simp [ho', hk1]
    rw [ho1] at hwo'
    obtain ⟨w₀, hw₀, rfl⟩ := hc5 w hw hwe
    have hmem := Dr_lw_mem w₀ _ hwo'
    have hkk := (Dr_kk_eq T hT 1 w₀ hw₀ hmem).1
    have hle := Dr_F_le 1 w₀
    have h0' : w₀.countP Dr_pat = 0 := (Dr_res_map w₀).symm.trans h0
    omega

/-- A package with both `Λ̃` and no resolvent between them, a factor `lam2 0 c`, occurs only in
case (ii) of the direct estimation in the proof of Lemma 5.5 [claim_estimate_remainder_terms]:
Type I with `k₁ = 0`. -/
private lemma Dr_Z (ε : ℝ) (n : ℕ) (T : LoopExpr)
    (hTr : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart]) (hT : T.wf = true)
    (ℓ : ℕ) (a : Fin 2) (tl : List LoopLetter) (hfoc : T.focus = some (ℓ, a, tl)) (p q : ℕ)
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) (w : List PkgLetter) (hw : w ∈ R.loops)
    (σ : List PkgLetter) (hσ : σ ∈ pkgSegs w) (h2 : 2 ≤ σ.countP PkgLetter.isLam)
    (ha : Dr_a σ = 0) :
    T.typeI = true ∧ T.kk 0 = 0 := by
  obtain ⟨w₀, tl₀, tl₁, Q, rest, r, hw₀, hrot, he, hres0, hlam0, hL, hcollQ⟩ :=
    Dr_main T hT ℓ a tl hfoc p q R hR
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -⟩ := pkg_dwirt_words T hT ℓ a tl hfoc 0 1 p q R hR
  have hoo : ((if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = 0 ∧
      (if 1 ≤ T.kk 0 then (1 : Fin 2) else 0) = 1)
      ∨ ((if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = 1 ∧
        (if 1 ≤ T.kk 0 then (1 : Fin 2) else 0) = 0) := by
    by_cases h : 1 ≤ T.kk 0 <;> simp [h]
  set o : Fin 2 := if 1 ≤ T.kk 0 then 0 else 1 with ho
  set o' : Fin 2 := if 1 ≤ T.kk 0 then 1 else 0 with ho'
  set H := (LoopLetter.det a :: tl₀).map PkgLetter.lw ++ [PkgLetter.lw (.lamt o)] with hH
  set hd := H ++ Q ++ [.ent 1 0] with hhd
  have hHo : 1 ≤ H.count (.lw (.lamt o)) := List.count_pos_iff.2 (by simp [hH])
  have hsum := fun x => Dr_R_lam T hT ℓ a tl hfoc p q R hR x
  -- both `Λ̃` lie in `σ`, hence in the main word
  have hw1 : ∀ x : Fin 2, w.count (.lw (.lamt x)) ≤ 1 := fun x => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count (.lw (.lamt x))) hw)
    rw [hsum x] at this
    exact this
  have hσ2 : ∀ x : Fin 2, 1 ≤ σ.count (.lw (.lamt x)) := by
    have h01 := Dr_count_lam σ
    have c0 := (Dr_seg_cnt w σ hσ 0).trans (hw1 0)
    have c1 := (Dr_seg_cnt w σ hσ 1).trans (hw1 1)
    have g0 : 1 ≤ σ.count (.lw (.lamt 0)) := by omega
    have g1 : 1 ≤ σ.count (.lw (.lamt 1)) := by omega
    intro x
    fin_cases x
    · exact g0
    · exact g1
  have hwhd : w = hd := by
    rw [hL] at hw
    rcases List.mem_cons.1 hw with h | h
    · exact h
    · exfalso
      have hs := hsum o
      rw [hL, List.map_cons, List.sum_cons] at hs
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w => w.count (.lw (.lamt o))) h)
      have hd1 : 1 ≤ hd.count (.lw (.lamt o)) := List.count_pos_iff.2 (by simp [hhd, hH])
      have := (hσ2 o).trans (Dr_seg_cnt w σ hσ o)
      omega
  subst hwhd
  refine ⟨?_, ?_⟩
  · by_contra hI
    have hc := h7 (by simpa using hI) hd (by rw [hL]; rfl)
    have hmem : PkgLetter.lw (.lamt o') ∈ hd :=
      List.count_pos_iff.1 ((hσ2 o').trans (Dr_seg_cnt _ σ hσ o'))
    rw [List.contains_iff_mem.2 hmem] at hc
    exact absurd hc (by simp)
  · by_contra hk
    have hk1 : 1 ≤ T.kk 0 := by omega
    have hk2 := (loop_reach ε n T hTr).2.1 hk1
    have ho0 : o = 0 := by simp [ho, hk1]
    have ho1 : o' = 1 := by simp [ho', hk1]
    -- the packages of the main word
    have hHent : ∀ z ∈ H, PkgLetter.isEnt z = false := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz; rfl
      · rw [List.mem_singleton] at hz; subst hz; rfl
    obtain ⟨σ₀, L, hSQ, hSHQ⟩ := seg_free_append H Q hHent
    have hperm := pkgSegs_perm (H ++ Q) [] 1 0
    have ehd : hd = (H ++ Q) ++ PkgLetter.ent 1 0 :: [] := by simp [hhd]
    rw [← ehd, List.nil_append] at hperm
    change (pkgSegs hd).Perm (Seg (H ++ Q)) at hperm
    rw [hSHQ] at hperm
    have hcs := PS_seg_count (.lw (.lamt o)) rfl hd
    have hhd1 : hd.count (.lw (.lamt o)) = 1 := by
      have := hsum o
      rw [hL, List.map_cons, List.sum_cons] at this
      have : 1 ≤ hd.count (.lw (.lamt o)) := List.count_pos_iff.2 (by simp [hhd, hH])
      omega
    rw [(hperm.map (List.count (.lw (.lamt o)))).sum_eq, hhd1, List.map_cons, List.sum_cons]
      at hcs
    have hHσ₀ : 1 ≤ (H ++ σ₀).count (.lw (.lamt o)) := by
      rw [List.count_append]; omega
    have hσeq : σ = H ++ σ₀ := by
      rcases List.mem_cons.1 (hperm.mem_iff.1 hσ) with h | h
      · exact h
      · exfalso
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.count (.lw (.lamt o))) h)
        have := hσ2 o
        omega
    subst hσeq
    -- `a = 0`: no resolvent between the two `Λ̃` of the main package
    have hdrop : (H ++ σ₀).dropWhile (fun x => !x.isLam) = .lw (.lamt o) :: σ₀ := by
      have e : H ++ σ₀ = (LoopLetter.det a :: tl₀).map PkgLetter.lw ++ (.lw (.lamt o) :: σ₀) := by
        simp [hH]
      rw [e, List.dropWhile_append_of_pos]
      · simp [PkgLetter.isLam]
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
        rcases List.mem_cons.1 hx with rfl | hx
        · simp [PkgLetter.isLam]
        · rcases x with b | b | b | b <;> simp [PkgLetter.isLam]
          exact hlam0 _ hx b rfl
    have ha' : (σ₀.takeWhile fun x => !x.isLam).countP PkgLetter.isRes = 0 := by
      rw [← ha, Dr_a, hdrop]
      rfl
    have hcσ₀ : 1 ≤ σ₀.countP PkgLetter.isLam := by
      have := List.countP_append (p := PkgLetter.isLam) (l₁ := H) (l₂ := σ₀)
      have hHl : H.countP PkgLetter.isLam = 1 := by
        rw [hH, List.countP_append, List.countP_map]
        simp only [List.countP_cons, List.countP_nil]
        rw [List.countP_eq_zero.2]
        · simp [PkgLetter.isLam]
        · intro x hx
          rcases x with b | b | b | b <;> simp [PkgLetter.isLam]
          exact hlam0 _ hx b rfl
      omega
    obtain ⟨y, S, -, hy, hσ₀⟩ := Dr_lam_split σ₀ hcσ₀
    obtain ⟨Z, hZ⟩ := Dr_splitOnP_prefix _ Q σ₀ L hSQ
    set A' := σ₀.takeWhile fun x => !x.isLam with hA'
    have hA'res : ∀ z ∈ A', PkgLetter.isRes z = false := fun z hz => by
      simpa using List.countP_eq_zero.1 ha' z hz
    have hA'lam : ∀ z ∈ A', PkgLetter.isLam z = false := fun z hz => by
      simpa using List.mem_takeWhile_imp hz
    have hA'y : ∀ z ∈ A' ++ [y], PkgLetter.isRes z = false := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hA'res z hz
      · rw [List.mem_singleton] at hz; subst hz; exact Dr_lam_res _ hy
    have hQe : Q ++ [PkgLetter.ent 1 0] = (A' ++ [y]) ++ (S ++ Z ++ [.ent 1 0]) := by
      rw [hZ, hσ₀]; simp
    rw [hQe, Dr_coll_pre _ _ hA'y] at hcollQ
    -- hence `tl₁ = A Λ̃ B` with no resolvent in `A`
    obtain ⟨D, hD⟩ : ∃ D, tl₁.map PkgLetter.lw = A' ++ y :: D := by
      have e2 : (tl₁ ++ [LoopLetter.res a]).map PkgLetter.lw ++ [PkgLetter.ent 1 0] =
          tl₁.map PkgLetter.lw ++ [.lw (.res a), .ent 1 0] := by simp
      rw [e2] at hcollQ
      rcases List.append_eq_append_iff.1 hcollQ with ⟨as, h1, -⟩ | ⟨bs, h1, h2⟩
      · exact ⟨as, by rw [h1]; simp⟩
      · rcases bs with _ | ⟨c, bs⟩
        · exact ⟨[], by rw [List.append_nil] at h1; rw [← h1]⟩
        · exfalso
          simp only [List.cons_append, List.cons.injEq] at h2
          have hc : c ∈ A' ++ [y] := by rw [h1]; simp
          have := hA'y c hc
          rw [← h2.1] at this
          simp [PkgLetter.isRes] at this
    obtain ⟨A, B', htl₁, hA, hB'⟩ := List.map_eq_append_iff.1 hD
    obtain ⟨b, B, rfl, hb, -⟩ := List.map_eq_cons_iff.1 hB'
    subst hb
    obtain ⟨x', rfl⟩ := Dr_isLam_lw b hy
    -- `x' = 1`
    have hx' : x' = 1 := by
      by_contra hx0
      have hx0' : x' = 0 := by
        have h1 := x'.isLt
        have h2 : x'.val ≠ 1 := fun h => hx0 (Fin.ext h)
        exact Fin.ext (by omega)
      subst hx0'
      have hcnt : 2 ≤ hd.count (.lw (.lamt o)) := by
        rw [ho0, hhd, List.count_append, List.count_append, hZ, hσ₀]
        have := List.count_pos_iff.2 (show PkgLetter.lw (.lamt 0) ∈ H by simp [hH, ho0])
        simp only [List.count_append, List.count_cons, beq_self_eq_true, ↓reduceIte]
        omega
      omega
    subst hx'
    have hAlam : ∀ z ∈ A, ∀ c, z ≠ .lamt c := by
      intro z hz c hzc
      subst hzc
      have : PkgLetter.lw (.lamt c) ∈ A' := by rw [← hA]; exact List.mem_map_of_mem hz
      have := hA'lam _ this
      simp [PkgLetter.isLam] at this
    have hAres : A.countP Dr_pat = 0 := by
      rw [← Dr_res_map, hA]
      exact ha'
    -- `k₂` is the number of resolvents in `A`
    have hmem : LoopLetter.lamt 1 ∈ w₀ := by
      have hp := (List.rotate_perm w₀ r)
      rw [hrot] at hp
      refine hp.mem_iff.1 ?_
      rw [he, htl₁]
      simp
    have hw₀m : w₀ ∈ T.loops := List.mem_of_getElem? hw₀
    obtain ⟨hkk, hc1⟩ := Dr_kk_eq T hT 1 w₀ hw₀m hmem
    rw [← Dr_F_rot 1 w₀ hc1 r, hrot, he, htl₁, ho0] at hkk
    have e3 : LoopLetter.res a :: (tl₀ ++ LoopLetter.lamt 0 :: (A ++ LoopLetter.lamt 1 :: B)) =
        ((LoopLetter.res a :: tl₀) ++ LoopLetter.lamt 0 :: A) ++ LoopLetter.lamt 1 :: B := by simp
    rw [e3, Dr_F_comp 1 0 _ A B ?_ hAlam, hAres] at hkk
    · omega
    · intro hm
      rcases List.mem_append.1 hm with hm | hm
      · rcases List.mem_cons.1 hm with hm | hm
        · cases hm
        · exact hlam0 _ hm 1 rfl
      · rcases List.mem_cons.1 hm with hm | hm
        · cases hm
        · exact hAlam _ hm 1 rfl

/-! ### The exponent rows of cases (i)–(iv) of the direct estimation -/

/-- The exponent rows of the direct estimation for Type I, cases (i) and (ii), in the counts of the
factors and the characters of `𝒯`: `I₀ ≤ 0` at `ξ = 0`, `I₁ ≤ 0` at `ξ = -1/3`. -/
private lemma Dr_arI (P R m n u k₁ k₂ Q W h L0 Z1 Z2 G0 t : ℤ) (hP : 2 ≤ P)
    (hd : 3 ≤ P ∨ 1 ≤ R) (hR0 : 0 ≤ R)
    (hQ : Q = m - n + h) (hW : u ≤ W + h) (hh : 0 ≤ h) (hW0 : 0 ≤ W) (hL0 : L0 = 0)
    (hZ1 : 0 ≤ Z1) (hZ2' : 0 ≤ Z2) (hG : 0 ≤ G0) (hG' : G0 ≤ L0) (ht : 0 ≤ t) (hZ2 : Z2 ≤ t)
    (hZs : Z1 + Z2 ≤ 1) (hc : 1 ≤ Q + L0 → 1 ≤ t) (hk : 0 ≤ k₁) (hk' : 0 ≤ k₂)
    (hk0 : k₁ = 0 → 1 ≤ R) (hk1 : 1 ≤ k₁ → 1 ≤ k₂) (hk12 : 1 ≤ k₁ + k₂)
    (hcnt : 2 * (n - 1) ≤ m - k₁ - k₂) (hn : 1 ≤ n) (hkZ : 1 ≤ k₁ → Z1 + Z2 = 0)
    (hii : k₁ = 0 → R = 1 → m + u = 1 → P ≠ 2) (hu : 0 ≤ u) :
    3 - P - 2 * R + L0 + (Z1 + Z2) ≤ 0 ∧
      13 - 3 * P - 6 * R - 2 * (Q + t + W) + 3 * Z2 + Z1 + 3 * L0 - 2 * G0 ≤ 0 := by
  omega

/-- The exponent rows of the direct estimation for Type II, cases (iii) and (iv). -/
private lemma Dr_arII (P R m n u k₁ k₂ Q W h L0 Z1 Z2 G0 t : ℤ) (hP : 2 ≤ P)
    (hd : 3 ≤ P ∨ 1 ≤ R) (hR0 : 0 ≤ R)
    (hQ : Q = m - n + h) (hW : u ≤ W + h) (hh : 0 ≤ h) (hW0 : 0 ≤ W) (hL0 : 0 ≤ L0)
    (hL1 : L0 ≤ 1) (hZ1 : Z1 = 0) (hZ2' : Z2 = 0) (hG : 0 ≤ G0) (hG' : G0 ≤ L0) (ht : 0 ≤ t)
    (hQL : 0 ≤ Q + L0) (hc : 1 ≤ Q + L0 → 1 ≤ t) (hk : 0 ≤ k₁) (hk' : 0 ≤ k₂)
    (hk0 : k₁ = 0 → 1 ≤ R) (hk1 : 1 ≤ k₁ → 2 ≤ k₂) (hk12 : 1 ≤ k₁ + k₂)
    (hcnt : 2 * (n - 2) ≤ m - k₁ - k₂) (hn : 2 ≤ n) (hkL : 1 ≤ k₁ → L0 = 0)
    (hiv1 : k₁ = 0 → R = 1 → m + u ≤ 2 → m = 2 ∧ n = 2 ∧ u = 0 ∧ P ≠ 2)
    (hiv2 : k₁ = 0 → R = 1 → k₂ = 1 → m + u ≤ 3 → m = 3 ∧ n = 3 ∧ u = 0 ∧ P ≠ 2) (hu : 0 ≤ u) :
    3 - P - 2 * R + L0 + (Z1 + Z2) ≤ 0 ∧
      13 - 3 * P - 6 * R - 2 * (Q + t + W) + 3 * Z2 + Z1 + 3 * L0 - 2 * G0 ≤ 0 := by
  omega

/-- An expanded expression is not stopped. -/
private lemma Dr_inner (ε : ℝ) : ∀ (n : ℕ) (L : List LoopExpr) (T : LoopExpr),
    T ∈ loopInner ε n L → ¬ T.Stopped ε
  | 0, L, T, h => by simp [loopInner] at h
  | n + 1, L, T, h => by
    simp only [loopInner, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
    rcases h with ⟨-, h⟩ | h
    · exact h
    · exact Dr_inner ε n _ T h

/-- An expression of the class `𝒯` has a loop, and two for Type II. -/
private lemma Dr_nloops (T : LoopExpr) (hT : T.wf = true) :
    1 ≤ T.loops.length ∧ (T.typeI = false → 2 ≤ T.loops.length) := by
  have hex : ∀ x : Fin 2, ∃ w ∈ T.loops, LoopLetter.lamt x ∈ w := by
    intro x
    have hcnt : (T.loops.map fun w => w.count (.lamt x)).sum = 1 := by
      simp only [LoopExpr.wf, Bool.and_eq_true, beq_iff_eq] at hT
      fin_cases x
      · exact hT.1.1.1.1
      · exact hT.1.1.1.2
    by_contra hc
    push_neg at hc
    rw [List.sum_eq_zero fun y hy => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
      exact List.count_eq_zero.2 (hc w hw)] at hcnt
    exact absurd hcnt (by norm_num)
  obtain ⟨w₁, hw₁, h₁⟩ := hex 0
  obtain ⟨w₂, hw₂, h₂⟩ := hex 1
  refine ⟨List.length_pos_of_mem hw₁, fun hI => ?_⟩
  rcases hL : T.loops with _ | ⟨w, _ | ⟨w', rest⟩⟩
  · rw [hL] at hw₁; simp at hw₁
  · rw [hL] at hw₁ hw₂
    simp only [List.mem_singleton] at hw₁ hw₂
    subst hw₁ hw₂
    have : T.typeI = true := by
      unfold LoopExpr.typeI
      rw [hL]
      simp [h₁, h₂]
    rw [hI] at this
    exact absurd this (by simp)
  · simp

/-- The exponent rows of cases (i)–(iv) of the direct estimation in the proof of Lemma 5.5
[claim_estimate_remainder_terms], (5.69)–(5.78): for an expanded expression with `p + q ≥ 3` or
`R ≥ 1`, other than the exceptional words of (5.75) and of case (iv) at `p + q = 2`, the monomial
of every derivative structure satisfies the hypotheses of the row lemma at `λ₀ = 2ε`. -/
private lemma Dr_exp (ε : ℝ) (hε : 0 < ε) (εA : ℝ) (hεA : 0 < εA) (hεA' : εA ≤ 1 / 3) (n : ℕ)
    (T : LoopExpr) (hTi : T ∈ loopInner ε n [loopStart]) (ℓ : ℕ) (a : Fin 2)
    (tl : List LoopLetter) (hfoc : T.focus = some (ℓ, a, tl)) (p q : ℕ) (hpq : 2 ≤ p + q)
    (hd : 3 ≤ p + q ∨ 1 ≤ T.rcount)
    (hsp : ¬ ((T = loopWordII ∨ T = loopWordIV ∨ T = loopWordIVb) ∧ p + q = 2))
    (R : PkgExpr) (hR : R ∈ T.pkgStart.dwirt 0 1 p q) :
    Dr_ok ε εA (Dr_mono R (fun _ => false) (p + q)) := by
  have hTr : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart] := Or.inr hTi
  obtain ⟨hT, hk12, hk0R, R', C₁, C₂, P₁, P₂, hch⟩ := loop_reach ε n T hTr
  have hf : T.focus.isSome = true := by rw [hfoc]; rfl
  obtain ⟨hg, hQ, hV2, hV7, hV8, hZex, hLex, hhead⟩ := Dr_prof T hT hf p q R hR
  obtain ⟨hKS1, hKS2, hKS3⟩ := Dr_KS ε n T hTr hT ℓ a tl hfoc p q R hR
  obtain ⟨g3, g4, g5, g6, -, g9, g63, g59, g2, gQ, gt⟩ := Dr_gen _ hg
  set V := Dr_CV (R.profile fun _ => false) with hV
  -- the main word carries `Λ̃_o`
  have hV23 : 1 ≤ V 2 - V 3 := by
    obtain ⟨-, tl₀, -, Q, rest, -, -, -, -, -, -, hL, -⟩ := Dr_main T hT ℓ a tl hfoc p q R hR
    have := hhead _ (by rw [hL]; exact List.mem_cons_self) (by simp [PkgLetter.isEnt])
    have h1 : 1 ≤ (((LoopLetter.det a :: tl₀).map PkgLetter.lw ++
        [PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1))]) ++ Q ++
          [PkgLetter.ent 1 0]).countP PkgLetter.isLam :=
      List.countP_pos_iff.2 ⟨PkgLetter.lw (.lamt (if 1 ≤ T.kk 0 then 0 else 1)), by simp, rfl⟩
    omega
  have hnst := Dr_inner ε n _ T hTi
  have hk12' : 1 ≤ T.kk 0 + T.kk 1 := by
    by_contra h
    exact hnst (Or.inr ⟨by omega, by omega⟩)
  obtain ⟨hn1, hn2⟩ := Dr_nloops T hT
  obtain ⟨hcI, hcII⟩ := loop_count_res ε n T hTr
  have hkII := loop_kk_typeII ε n T hTr
  have hrc : T.rcount = (T.S : ℤ) - T.charsZ.1 + T.charsZ.2.1 + 1 := rfl
  have hR0 : 0 ≤ T.rcount := by
    rw [hrc]
    have hS : (T.S : ℤ) = T.charsZ.2.2.2 := rfl
    rw [hch] at hrc hS ⊢
    simp only at hS ⊢
    omega
  -- the factors `lam2 0 c` and `lam0`
  have hZk : 1 ≤ T.kk 0 → V 4 + V 5 = 0 := fun hk => by
    by_contra hne
    obtain ⟨w, hw, σ, hσ, h2, ha⟩ := hZex (by omega)
    have := (Dr_Z ε n T hTr hT ℓ a tl hfoc p q R hR w hw σ hσ h2 ha).2
    omega
  have hZII : T.typeI = false → V 4 + V 5 = 0 := fun hI => by
    by_contra hne
    obtain ⟨w, hw, σ, hσ, h2, ha⟩ := hZex (by omega)
    have := (Dr_Z ε n T hTr hT ℓ a tl hfoc p q R hR w hw σ hσ h2 ha).1
    rw [hI] at this
    exact absurd this (by simp)
  have hLk : 1 ≤ T.kk 0 → V 3 = 0 := fun hk => by
    by_contra hne
    obtain ⟨w, hw, hwe, h1, h0⟩ := hLex (by omega)
    have := (Dr_L0 ε n T hTr hT ℓ a tl hfoc p q R hR w hw hwe h1 h0).2
    omega
  have hLI : T.typeI = true → V 3 = 0 := fun hI => by
    by_contra hne
    obtain ⟨w, hw, hwe, h1, h0⟩ := hLex (by omega)
    have := (Dr_L0 ε n T hTr hT ℓ a tl hfoc p q R hR w hw hwe h1 h0).1
    rw [hI] at this
    exact absurd this (by simp)
  -- the integer rows
  have hm0 : 0 ≤ T.charsZ.1 := Int.natCast_nonneg _
  have hu0 : 0 ≤ T.charsZ.2.2.1 := by
    have : T.charsZ.2.2.1 = (T.weights.length : ℤ) := rfl
    omega
  have hcharN : T.charsZ.2.1 = (T.loops.length : ℤ) := rfl
  have hcharU : T.charsZ.2.2.1 = (T.weights.length : ℤ) := rfl
  have hI01 : 3 - ((p + q : ℕ) : ℤ) - 2 * T.rcount + V 3 + (V 4 + V 5) ≤ 0 ∧
      13 - 3 * ((p + q : ℕ) : ℤ) - 6 * T.rcount - 2 * ((V 1 - V 0) + V 9 + V 8) + 3 * V 5 +
        V 4 + 3 * V 3 - 2 * V 6 ≤ 0 := by
    have hQ' : V 1 - V 0 = T.charsZ.1 - T.charsZ.2.1 + (R.S - T.S) := by rw [hQ, hKS1]
    have hW' : T.charsZ.2.2.1 ≤ V 8 + (R.S - T.S) := by rw [hV8, hcharU]; exact hKS2
    cases hI : T.typeI
    · have hii1 : T.kk 0 = 0 → T.rcount = 1 → T.charsZ.1 + T.charsZ.2.2.1 ≤ 2 →
          T.charsZ.1 = 2 ∧ T.charsZ.2.1 = 2 ∧ T.charsZ.2.2.1 = 0 ∧ ((p + q : ℕ) : ℤ) ≠ 2 := by
        intro hk hr hmu
        have hT4 := (loop_word_iv ε n T hTi hk hI hr).1 hmu
        refine ⟨by rw [hT4]; rfl, by rw [hT4]; rfl, by rw [hT4]; rfl, fun h2 => hsp ⟨Or.inr
          (Or.inl hT4), by exact_mod_cast h2⟩⟩
      have hii2 : T.kk 0 = 0 → T.rcount = 1 → (T.kk 1 : ℤ) = 1 →
          T.charsZ.1 + T.charsZ.2.2.1 ≤ 3 →
          T.charsZ.1 = 3 ∧ T.charsZ.2.1 = 3 ∧ T.charsZ.2.2.1 = 0 ∧ ((p + q : ℕ) : ℤ) ≠ 2 := by
        intro hk hr hk1 hmu
        have hT4 := (loop_word_iv ε n T hTi hk hI hr).2 (by exact_mod_cast hk1) hmu
        refine ⟨by rw [hT4]; rfl, by rw [hT4]; rfl, by rw [hT4]; rfl, fun h2 => hsp ⟨Or.inr
          (Or.inr hT4), by exact_mod_cast h2⟩⟩
      have hc : 2 * (T.charsZ.2.1 - 2) ≤ T.charsZ.1 - (T.kk 0 : ℤ) - (T.kk 1 : ℤ) := hcII hI
      have hn : (2 : ℤ) ≤ T.charsZ.2.1 := by rw [hcharN]; exact_mod_cast hn2 hI
      have hZ0 : V 4 + V 5 = 0 := hZII hI
      have f1 : V 4 = 0 := by omega
      have f2 : V 5 = 0 := by omega
      have f3 : (T.kk 0 : ℤ) = 0 → 1 ≤ T.rcount := fun h => hk0R (by exact_mod_cast h)
      have f4 : 1 ≤ (T.kk 0 : ℤ) → 2 ≤ (T.kk 1 : ℤ) := fun h => by
        exact_mod_cast hkII hI (by exact_mod_cast h)
      have f5 : 1 ≤ (T.kk 0 : ℤ) → V 3 = 0 := fun h => hLk (by exact_mod_cast h)
      have f6 : (T.kk 0 : ℤ) = 0 → T.rcount = 1 → T.charsZ.1 + T.charsZ.2.2.1 ≤ 2 →
          T.charsZ.1 = 2 ∧ T.charsZ.2.1 = 2 ∧ T.charsZ.2.2.1 = 0 ∧ ((p + q : ℕ) : ℤ) ≠ 2 :=
        fun hk hr => hii1 (by exact_mod_cast hk) hr
      have f7 : (T.kk 0 : ℤ) = 0 → T.rcount = 1 → (T.kk 1 : ℤ) = 1 →
          T.charsZ.1 + T.charsZ.2.2.1 ≤ 3 →
          T.charsZ.1 = 3 ∧ T.charsZ.2.1 = 3 ∧ T.charsZ.2.2.1 = 0 ∧ ((p + q : ℕ) : ℤ) ≠ 2 :=
        fun hk hr hk1 => hii2 (by exact_mod_cast hk) hr hk1
      have f8 : 2 ≤ ((p + q : ℕ) : ℤ) := by exact_mod_cast hpq
      have f9 : 3 ≤ ((p + q : ℕ) : ℤ) ∨ 1 ≤ T.rcount := by
        rcases hd with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr h
      have f10 : 0 ≤ R.S - T.S := by omega
      have f11 : 0 ≤ V 8 := by rw [hV8]; positivity
      have f12 : V 3 ≤ 1 := by omega
      have f13 : 1 ≤ (T.kk 0 : ℤ) + (T.kk 1 : ℤ) := by exact_mod_cast hk12'
      exact Dr_arII ((p + q : ℕ) : ℤ) T.rcount T.charsZ.1 T.charsZ.2.1 T.charsZ.2.2.1 (T.kk 0)
        (T.kk 1) (V 1 - V 0) (V 8) (R.S - T.S) (V 3) (V 4) (V 5) (V 6) (V 9) f8 f9 hR0 hQ' hW'
        f10 f11 g3 f12 f1 f2 g6 g63 g9 gQ gt (by positivity) (by positivity) f3 f4 f13 hc hn f5 f6
        f7 hu0
    · have hii : T.kk 0 = 0 → T.rcount = 1 → T.charsZ.1 + T.charsZ.2.2.1 = 1 →
          ((p + q : ℕ) : ℤ) ≠ 2 := by
        intro hk hr hmu h2
        exact hsp ⟨Or.inl (loop_word_ii ε n T hTi hk hI hr hmu), by exact_mod_cast h2⟩
      have hc : 2 * (T.charsZ.2.1 - 1) ≤ T.charsZ.1 - (T.kk 0 : ℤ) - (T.kk 1 : ℤ) := hcI hI
      have hn : (1 : ℤ) ≤ T.charsZ.2.1 := by rw [hcharN]; exact_mod_cast hn1
      have f0 : V 3 = 0 := hLI hI
      have f3 : (T.kk 0 : ℤ) = 0 → 1 ≤ T.rcount := fun h => hk0R (by exact_mod_cast h)
      have f4 : 1 ≤ (T.kk 0 : ℤ) → 1 ≤ (T.kk 1 : ℤ) := fun h => by
        exact_mod_cast hk12 (by exact_mod_cast h)
      have f5 : 1 ≤ (T.kk 0 : ℤ) → V 4 + V 5 = 0 := fun h => hZk (by exact_mod_cast h)
      have f6 : (T.kk 0 : ℤ) = 0 → T.rcount = 1 → T.charsZ.1 + T.charsZ.2.2.1 = 1 →
          ((p + q : ℕ) : ℤ) ≠ 2 := fun hk hr hmu => hii (by exact_mod_cast hk) hr hmu
      have f8 : 2 ≤ ((p + q : ℕ) : ℤ) := by exact_mod_cast hpq
      have f9 : 3 ≤ ((p + q : ℕ) : ℤ) ∨ 1 ≤ T.rcount := by
        rcases hd with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr h
      have f10 : 0 ≤ R.S - T.S := by omega
      have f11 : 0 ≤ V 8 := by rw [hV8]; positivity
      have f12 : V 4 + V 5 ≤ 1 := by omega
      have f13 : 1 ≤ (T.kk 0 : ℤ) + (T.kk 1 : ℤ) := by exact_mod_cast hk12'
      exact Dr_arI ((p + q : ℕ) : ℤ) T.rcount T.charsZ.1 T.charsZ.2.1 T.charsZ.2.2.1 (T.kk 0)
        (T.kk 1) (V 1 - V 0) (V 8) (R.S - T.S) (V 3) (V 4) (V 5) (V 6) (V 9) f8 f9 hR0 hQ' hW'
        f10 f11 f0 g4 g5 g6 g63 g9 g59 f12 gt (by positivity) (by positivity) f3 f4 f13 hc hn f5
        f6 hu0
  obtain ⟨hI0, hI1⟩ := hI01
  -- the real rows
  have hS : (R.S : ℝ) = ((V 1 - V 0 : ℤ) : ℝ) + T.rcount - 1 := by
    have hQ' : V 1 - V 0 = T.charsZ.1 - T.charsZ.2.1 + (R.S - T.S) := by rw [hQ, hKS1]
    have : R.S = V 1 - V 0 + T.rcount - 1 := by rw [hrc]; omega
    exact_mod_cast this
  have hG1 : ((V 6 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (show V 6 ≤ 1 by omega)
  have hL0 : (0 : ℝ) ≤ ((V 3 : ℤ) : ℝ) := by exact_mod_cast g3
  have e1 := mul_le_mul_of_nonneg_left hG1 hε.le
  have e2 := mul_nonneg hL0 hεA.le
  have hI0r : (3 : ℝ) - ((p + q : ℕ) : ℝ) - 2 * T.rcount + V 3 + (V 4 + V 5) ≤ 0 := by
    exact_mod_cast hI0
  have hI1r : (13 : ℝ) - 3 * ((p + q : ℕ) : ℝ) - 6 * T.rcount -
      2 * (((V 1 : ℝ) - V 0) + V 9 + V 8) + 3 * V 5 + V 4 + 3 * V 3 - 2 * V 6 ≤ 0 := by
    exact_mod_cast hI1
  have hV2r : ((V 2 : ℤ) : ℝ) = 2 := by exact_mod_cast hV2
  have hV7r : ((V 7 : ℤ) : ℝ) = 0 := by exact_mod_cast hV7
  refine Dr_ok_of R _ (p + q) ε εA hε.le hεA.le hεA' hg (show 2 ≤ V 2 + V 3 by omega) ?_ ?_
  · rw [← hV]
    simp only [Dr_Φ0, hV2r, hV7r]
    rw [hS]
    push_cast at e1 e2 hI0r ⊢
    linarith
  · rw [← hV]
    simp only [Dr_Φ1, hV2r, hV7r]
    rw [hS]
    push_cast at e1 e2 hI1r ⊢
    linarith

/-! ### The exceptional words at `p + q = 2` -/

/-- The row hypotheses for the monomials of the exceptional words: `λ = ε/4` for (5.75)
[direct_estimate_type_1_k_1_0_k_2_geq_1_sR_1_p_plus_q_2_m_plus_u_1] paired on slot `0`, and
`λ ≤ -ε_A` for the words of case (iv) with the factor `lam0 true`. -/
private lemma Dr_ok_ex (ε εA : ℝ) (hε : 0 < ε) (hεA : 0 < εA) (m : FMono)
    (hm : m = ⟨-3, 3, 1, 2, 0⟩ ∨ m = ⟨-4, 4, 2, 3, 0⟩ ∨ m = ⟨-6, 6, 4, 3, 0⟩ ∨
      m = ⟨-6, 4, 4, 3, 0⟩) : Dr_ok ε εA m := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    rw [Dr_lamR_eq _ (by norm_num) rfl] <;> simp only [Dr_lf] <;> norm_num <;> linarith

/-- The derivative structures of `⟨𝔐₀ Λ̃₁ 𝒢₁ Λ̃₂⟩` at `p + q = 2`, paired on slot `0`: the monomial
`N^{-3/2} (Im m)^{3/2} η^{-1/2} ‖A‖²_HS` of (5.75)
[direct_estimate_type_1_k_1_0_k_2_geq_1_sR_1_p_plus_q_2_m_plus_u_1]. -/
private lemma Dr_wII (p q : ℕ) (hpq : p + q = 2) :
    ∀ R ∈ loopWordII.pkgStart.dwirt 0 1 p q,
      Dr_mono R (fun a => decide (a = 0)) 2 = ⟨-3, 3, 1, 2, 0⟩ ∧
        R.pairIn (fun a => decide (a = 0)) = true ∧ R.onlyDet 0 = true := by
  have h : (loopWordII.pkgStart.dwirt 0 1 p q).all (fun R =>
      Dr_mono R (fun a => decide (a = 0)) 2 == ⟨-3, 3, 1, 2, 0⟩ &&
        R.pairIn (fun a => decide (a = 0)) && R.onlyDet 0) = true := by
    rcases (by omega : (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 0)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  intro R hR
  have := List.all_eq_true.1 h R hR
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- The derivative structures of the exceptional words of case (iv) at `p + q = 2`. -/
private lemma Dr_wIV (T : LoopExpr) (hT : T = loopWordIV ∨ T = loopWordIVb) (p q : ℕ)
    (hpq : p + q = 2) :
    ∀ R ∈ T.pkgStart.dwirt 0 1 p q, Dr_mono R (fun _ => false) 2 = ⟨-4, 4, 2, 3, 0⟩ ∨
      Dr_mono R (fun _ => false) 2 = ⟨-6, 6, 4, 3, 0⟩ ∨
        Dr_mono R (fun _ => false) 2 = ⟨-6, 4, 4, 3, 0⟩ := by
  have h : (T.pkgStart.dwirt 0 1 p q).all (fun R =>
      Dr_mono R (fun _ => false) 2 == ⟨-4, 4, 2, 3, 0⟩ ||
        Dr_mono R (fun _ => false) 2 == ⟨-6, 6, 4, 3, 0⟩ ||
          Dr_mono R (fun _ => false) 2 == ⟨-6, 4, 4, 3, 0⟩) = true := by
    rcases (by omega : (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 0)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hT with rfl | rfl <;> decide
  intro R hR
  have := List.all_eq_true.1 h R hR
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-! ### The pairing of slot `0` -/

/-- The pairing (P) of (5.58) [eq:polar2] inside the cumulant sum of (5.65)
[explicit_reminder_terms_before_expansions]: the signed sum over the flag of slot `0` of `outer`
is `outer` with `𝔐₀ - 𝔐₀^*` in place of `𝔐₀`. -/
private lemma Dr_pair {D N : ℕ} (C : ℕ → ℝ) (R : PkgExpr) (hR : R.onlyDet 0 = true)
    (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C 1 μ) (p q : ℕ) :
    ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
        R.outer { e with s := Function.update e.s 0 b } μ p q =
      Dr_out R { e with s := Function.update e.s 0 false } (fun a => decide (a = 0)) μ p q := by
  have := hμ.prob
  have hint : ∀ (b : Bool) (κ : ℕ → Idx D N),
      Integrable (fun h => R.evalH { e with s := Function.update e.s 0 b } κ h) μ := by
    intro b κ
    have hfun : (fun h => R.evalH { e with s := Function.update e.s 0 b } κ h) =
        fun h => ∑ ι : Fin R.nb → Fin D, PE_val { e with s := Function.update e.s 0 b } ι κ R h :=
      funext fun h => PE_evalH R _ κ h rfl
    rw [hfun]
    set e' : LoopEnv D N := { e with s := Function.update e.s 0 b } with he'
    have hz : ∀ a, (e'.z a).im ≠ 0 := he
    refine integrable_finsetSum _ fun ι _ => ?_
    exact PE_good_integrable hμ.herm (PE_good_val e' hz ι κ R)
  have key : ∀ i j : Idx D N, ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
      (if i.1 = j.1 then ccum (μ.map fun h => h i j) p (q + 1) /
          ((p.factorial * q.factorial : ℕ) : ℂ) * (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
          ∫ h, R.evalH { e with s := Function.update e.s 0 b }
            (fun l => if l = 0 then i else j) h ∂μ else 0) =
      (if i.1 = j.1 then ccum (μ.map fun h => h i j) p (q + 1) /
          ((p.factorial * q.factorial : ℕ) : ℂ) * (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
          ∫ h, R.evalP { e with s := Function.update e.s 0 false } (fun a => decide (a = 0))
            (fun l => if l = 0 then i else j) h ∂μ else 0) := by
    intro i j
    by_cases hij : i.1 = j.1
    · simp only [hij, ↓reduceIte]
      have hI : ∫ h, R.evalP { e with s := Function.update e.s 0 false }
          (fun a => decide (a = 0)) (fun l => if l = 0 then i else j) h ∂μ =
          ∑ b : Bool, (if b then (-1 : ℂ) else 1) * ∫ h, R.evalH
            { e with s := Function.update e.s 0 b } (fun l => if l = 0 then i else j) h ∂μ := by
        have hp : ∀ h, R.evalP { e with s := Function.update e.s 0 false }
            (fun a => decide (a = 0)) (fun l => if l = 0 then i else j) h =
            ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
              R.evalH { e with s := Function.update e.s 0 b } (fun l => if l = 0 then i else j) h :=
          fun h => (pkg_pair_ident R 0 hR e (he 0) _ h).symm
        simp_rw [hp]
        rw [integral_finsetSum _ fun b _ => (hint b _).const_mul _]
        simp_rw [integral_const_mul]
      rw [hI, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    · simp [hij]
  unfold PkgExpr.outer Dr_out
  rw [← (show ∑ i : Idx D N, ∑ j : Idx D N, ∑ b : Bool, (if b then (-1 : ℂ) else 1) *
      (if i.1 = j.1 then ccum (μ.map fun h => h i j) p (q + 1) /
          ((p.factorial * q.factorial : ℕ) : ℂ) * (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
          ∫ h, R.evalH { e with s := Function.update e.s 0 b }
            (fun l => if l = 0 then i else j) h ∂μ else 0) = _ from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `4 C ≤ N^τ` for `N` large. -/
private lemma Dr_large (c τ : ℝ) (hτ : 0 < τ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ τ := by
  have h := (tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.1 (h.eventually_ge_atTop c)

/-- The sum over the four starting loops of (5.29) [expansion_of_im] as a sum over the flag of
slot `1` of a sum over the flag of slot `0`, with the sign `(-1)^{s₀} (-1)^{s₁}`. -/
private lemma Dr_split (g : (Fin 2 → Bool) → ℂ) :
    ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * g s =
      ∑ s₁ : Bool, (if s₁ then (-1 : ℂ) else 1) *
        ∑ s₀ : Bool, (if s₀ then (-1 : ℂ) else 1) * g ![s₀, s₁] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  simp only [finTwoArrowEquiv, Equiv.coe_fn_symm_mk]
  cases s₀ <;> cases s₁ <;> simp

private lemma Dr_lsum_comm {α : Type*} (L : List α) (c : Bool → ℂ) (f : Bool → α → ℂ) :
    ∑ b : Bool, c b * (L.map (f b)).sum = (L.map fun x => ∑ b : Bool, c b * f b x).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

private lemma Dr_pairIn_false (R : PkgExpr) : R.pairIn (fun _ => false) = true := by
  simp only [PkgExpr.pairIn, List.all_eq_true, Bool.or_eq_true]
  intro w _
  right
  simp only [Bool.not_eq_true', List.any_eq_false]
  intro x _
  rcases x with ((b | b | b | b) | ⟨u, v⟩) <;> simp

private lemma Dr_norm_lsum {α : Type*} (L : List α) (f : α → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map fun x => ‖f x‖).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The final count: `c K N^{τ/2} N^{2ε} 𝔗 ≤ N^{τ+2ε} 𝔗` when `c K ≤ N^{τ/2}`. -/
private lemma Dr_final (N : ℕ) (hN : 1 ≤ N) (τ ε c K X : ℝ) (hX : 0 ≤ X)
    (h : c * K ≤ (N : ℝ) ^ (τ / 2)) (hK : 0 ≤ K * (N : ℝ) ^ (τ / 2)) :
    c * (K * (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * X)) ≤ (N : ℝ) ^ (τ + 2 * ε) * X := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ (τ + 2 * ε) = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (2 * ε) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    ring_nf
  rw [e]
  have h2 : 0 ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * X) := by positivity
  calc c * (K * (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * X)) =
        (c * K) * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * X)) := by ring
    _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * X)) :=
        mul_le_mul_of_nonneg_right h h2
    _ = _ := by ring

/-- The direct estimation in the proof of Lemma 5.5 [claim_estimate_remainder_terms], cases
(i)–(iv): for an expanded expression and `p + q ≥ 3` or `R ≥ 1`, the signed sum over the four
starting loops of (5.29) [expansion_of_im] of `𝓡_𝒯(p, q)` is at most
`N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemmas 5.2 and 5.4. -/
theorem loop_rem_direct (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (n : ℕ) (T : LoopExpr)
    (hT : T ∈ loopInner ε n [loopStart]) (p q : ℕ) (hpq : 2 ≤ p + q)
    (hd : 3 ≤ p + q ∨ 1 ≤ T.rcount) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            T.remPQ (evecEnv D N A k ε s) μ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              T.remPQ (evalEnv D N A k ε t s) μ p q‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  intro τ hτ
  have hTr : T ∈ loopIter ε n [loopStart] ∨ T ∈ loopInner ε n [loopStart] := Or.inr hT
  have hwf := (loop_reach ε n T hTr).1
  have hεA0 : 0 < min εA (1 / 3) := lt_min hεA (by norm_num)
  have hεA1 : min εA (1 / 3) ≤ 1 / 3 := min_le_right _ _
  obtain ⟨CU, -, N₃, hN₃⟩ := pkg_slot_im D hD δA εA ε hδA hεA hε hε' hε''
  -- both kinds of slots at once
  suffices H : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ E : (Fin 2 → Bool) → LoopEnv D N, (∀ s, Dr_slot D N A k ε (E s)) →
        (∀ s s', E s = { E s' with s := s }) → (∀ s, (E s).s = s) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * T.remPQ (E s) μ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * Dr_T D N A k by
    obtain ⟨N₀, hN₀⟩ := H
    exact ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs =>
      ⟨hN₀ N hN μ hμ A hA k hk hkN hhs _ (fun s => Or.inl ⟨s, rfl⟩) (fun _ _ => rfl)
          (fun _ => rfl),
        fun t ht => hN₀ N hN μ hμ A hA k hk hkN hhs _ (fun s => Or.inr ⟨t, ht, s, rfl⟩)
          (fun _ _ => rfl) (fun _ => rfl)⟩⟩
  rcases hfoc : T.focus with _ | ⟨ℓ, a, tl⟩
  · -- without a focus the remainder vanishes
    refine ⟨0, fun N _ μ _ A _ k _ _ _ E _ _ _ => ?_⟩
    have h0 : ∀ e : LoopEnv D N, T.remPQ e μ p q = 0 := by
      intro e
      have hv : ∀ (ι : Fin T.nb → Fin D) (i j : Idx D N) (h' : Idx D N → Idx D N → ℂ),
          T.pkgVal e ι i j h' = 0 := by
        intro ι i j h'
        simp only [LoopExpr.pkgVal, hfoc]
      unfold LoopExpr.remPQ
      simp only [hv, PE_wirt_zero, integral_zero, mul_zero, ite_self, Finset.sum_const_zero]
    simp only [h0, mul_zero, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg (by positivity) (Dr_T_nonneg D N A k)
  have hf : T.focus.isSome = true := by rw [hfoc]; rfl
  have hz : ∀ N, N₃ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, Dr_slot D N A k ε e → ∀ a, (e.z a).im ≠ 0 := by
    intro N hN A hA k hk hkN hhs e he a
    rw [(hN₃ N hN A hA k hk hkN hhs e he a).1, etaK]
    have := Dr_rk D N k hk hkN
    have hN1 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp at hkN; omega
      · exact h
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  by_cases hII : T = loopWordII ∧ p + q = 2
  · -- the exceptional case (5.75): pairing on slot `0`
    obtain ⟨rfl, hP2⟩ := hII
    have hrow : ∀ R ∈ loopWordII.pkgStart.dwirt 0 1 p q, Dr_Bd D δA εA ε C
        fun N μ e => ‖Dr_out R e (fun a => decide (a = 0)) μ p q‖ := by
      intro R hR
      obtain ⟨hm, hpi, -⟩ := Dr_wII p q hP2 R hR
      refine Dr_row D hD δA εA ε hδA hεA hε hε' hε'' C loopWordII hwf hf p q R hR _ hpi ?_
      rw [hP2, hm]
      exact Dr_ok_ex ε _ hε hεA0 _ (Or.inl rfl)
    obtain ⟨K, hK, N₁, hN₁⟩ := Dr_Bd_sum (fun (R : PkgExpr) (N : ℕ)
      (μ : Measure (Idx D N → Idx D N → ℂ)) (e : LoopEnv D N) =>
        ‖Dr_out R e (fun a => decide (a = 0)) μ p q‖) _ hrow (τ / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Dr_large (2 * K) (τ / 2) (by positivity)
    refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN μ hμ A hA k hk hkN hhs E hE hE' hEs => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hzE : ∀ s a, ((E s).z a).im ≠ 0 := fun s =>
      hz N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN) A hA k hk hkN hhs _ (hE s)
    have hsum : ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        loopWordII.remPQ (E s) μ p q = ∑ s₁ : Bool, (if s₁ then (-1 : ℂ) else 1) *
          ((loopWordII.pkgStart.dwirt 0 1 p q).map fun R =>
            Dr_out R (E ![false, s₁]) (fun a => decide (a = 0)) μ p q).sum := by
      rw [Dr_split]
      refine Finset.sum_congr rfl fun s₁ _ => ?_
      congr 1
      have hupd : ∀ s₀ : Bool, Function.update (E ![false, s₁]).s 0 s₀ = ![s₀, s₁] := by
        intro s₀
        rw [hEs]
        funext i
        fin_cases i <;> simp [Function.update]
      have hE2 : ∀ s₀ : Bool, E ![s₀, s₁] =
          { E ![false, s₁] with s := Function.update (E ![false, s₁]).s 0 s₀ } := by
        intro s₀
        rw [hupd]
        exact hE' _ _
      have hexp : ∀ s₀ : Bool, loopWordII.remPQ (E ![s₀, s₁]) μ p q =
          ((loopWordII.pkgStart.dwirt 0 1 p q).map fun R => R.outer
            { E ![false, s₁] with s := Function.update (E ![false, s₁]).s 0 s₀ } μ p q).sum := by
        intro s₀
        rw [loop_rem_expand D N C loopWordII (E ![s₀, s₁]) (hzE _) μ hμ p q, hE2 s₀]
      rw [Finset.sum_congr rfl fun s₀ _ => by rw [hexp s₀], Dr_lsum_comm]
      refine congrArg List.sum (List.map_congr_left fun R hR => ?_)
      rw [Dr_pair C R (Dr_wII p q hP2 R hR).2.2 (E ![false, s₁]) (hzE _) μ hμ p q, hupd,
        ← hE']
    rw [hsum]
    have hb : ∀ s₁ : Bool, ‖(if s₁ then (-1 : ℂ) else 1) *
        ((loopWordII.pkgStart.dwirt 0 1 p q).map fun R =>
          Dr_out R (E ![false, s₁]) (fun a => decide (a = 0)) μ p q).sum‖ ≤
        K * (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k) := by
      intro s₁
      rw [norm_mul, show ‖(if s₁ then (-1 : ℂ) else 1)‖ = 1 by split_ifs <;> simp, one_mul]
      exact (Dr_norm_lsum _ _).trans (hN₁ N (le_trans (le_trans (le_max_left _ _)
        (le_max_left _ _)) hN) μ hμ A hA k hk hkN hhs _ (hE _))
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s₁ _ => hb s₁).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    exact Dr_final N hN1 τ ε 2 K _ (Dr_T_nonneg D N A k)
      (hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN))
      (by have := Real.rpow_nonneg (Nat.cast_nonneg N) (τ / 2); positivity)
  · -- cases (i)–(iv) with no paired slot
    have hrow : ∀ R ∈ T.pkgStart.dwirt 0 1 p q, Dr_Bd D δA εA ε C
        fun N μ e => ‖R.outer e μ p q‖ := by
      intro R hR
      have hok : Dr_ok ε (min εA (1 / 3)) (Dr_mono R (fun _ => false) (p + q)) := by
        by_cases hsp : (T = loopWordII ∨ T = loopWordIV ∨ T = loopWordIVb) ∧ p + q = 2
        · obtain ⟨h1 | h1, h2⟩ := hsp
          · exact absurd ⟨h1, h2⟩ hII
          · rw [h2]
            rcases Dr_wIV T h1 p q h2 R hR with h | h | h <;>
              exact Dr_ok_ex ε _ hε hεA0 _ (by simp [h])
        · exact Dr_exp ε hε _ hεA0 hεA1 n T hT ℓ a tl hfoc p q hpq hd hsp R hR
      have := Dr_row D hD δA εA ε hδA hεA hε hε' hε'' C T hwf hf p q R hR (fun _ => false)
        (Dr_pairIn_false R) hok
      simpa only [Dr_out_false] using this
    obtain ⟨K, hK, N₁, hN₁⟩ := Dr_Bd_sum (fun (R : PkgExpr) (N : ℕ)
      (μ : Measure (Idx D N → Idx D N → ℂ)) (e : LoopEnv D N) => ‖R.outer e μ p q‖) _ hrow (τ / 2)
      (by positivity)
    obtain ⟨N₂, hN₂⟩ := Dr_large (4 * K) (τ / 2) (by positivity)
    refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN μ hμ A hA k hk hkN hhs E hE hE' hEs => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hb : ∀ s : Fin 2 → Bool, ‖(if s 0 = s 1 then (1 : ℂ) else -1) * T.remPQ (E s) μ p q‖ ≤
        K * (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (2 * ε) * Dr_T D N A k) := by
      intro s
      rw [norm_mul, show ‖(if s 0 = s 1 then (1 : ℂ) else -1)‖ = 1 by split_ifs <;> simp,
        one_mul, loop_rem_expand D N C T (E s) (hz N (le_trans (le_trans (le_max_left _ _)
          (le_max_right _ _)) hN) A hA k hk hkN hhs _ (hE s)) μ hμ p q]
      exact (Dr_norm_lsum _ _).trans (hN₁ N (le_trans (le_trans (le_max_left _ _)
        (le_max_left _ _)) hN) μ hμ A hA k hk hkN hhs _ (hE _))
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s _ => hb s).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Fin 2 → Bool) : ℝ) = 4 := by simp
    rw [hcard]
    exact Dr_final N hN1 τ ε 4 K _ (Dr_T_nonneg D N A k)
      (hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN))
      (by have := Real.rpow_nonneg (Nat.cast_nonneg N) (τ / 2); positivity)

end RBMTransitionEdge

end
