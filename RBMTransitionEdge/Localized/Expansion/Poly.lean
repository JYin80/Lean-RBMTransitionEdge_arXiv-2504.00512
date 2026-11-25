module

public import RBMTransitionEdge.LocalLaw.CumulantClass
public import RBMTransitionEdge.LocalLaw.ResPoly
public import RBMTransitionEdge.Localized.Expansion.Eval

@[expose] public section

/-!
# Resolvent polynomials for the expansion of §5.3

The function `(F 𝒢)_{ij} W ⋯ f ⋯` of (5.41) [reminder_terms_expansion], the remainder terms
`𝓡_𝒯(p, q)` of (5.41) and (5.65) [explicit_reminder_terms_before_expansions], and the statement
that `pkgVal` of an expression of the class (5.33) [definition_class_of_expression_loop] is a
resolvent polynomial over the standard basis.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The function `(F 𝒢)_{ij} W₁ ⋯ W_u f^{(1)} ⋯ f^{(n-1)}` of (5.41) [reminder_terms_expansion],
`F = 𝔐_a B₁ Λ̃_o Π` from the decomposition (5.38) [explicit_cT], at fixed bound indices. -/
def LoopExpr.pkgVal {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (ι : Fin T.nb → Fin D)
    (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  match T.focus with
  | none => 0
  | some (ℓ, a, tl) =>
    loopWordMat (e.G h) e.M (e.E ι) e.Lt (.det a :: tl ++ [.res a]) i j *
      (T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
      ((T.loops.eraseIdx ℓ).map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod

/-- The term `𝓡_𝒯(p, q)` of (5.41) [reminder_terms_expansion] and (5.65)
[explicit_reminder_terms_before_expansions]: `-c_𝒯/(ND) Σ_ι Σ_b Σ_{i,j ∈ 𝓘_b}
𝒞^{(p,q+1)}(h_{ij})/(p! q!) E ∂^p_w ∂^q_w̄ [(F 𝒢)_{ij} W ⋯ f ⋯]` at `w = h_{ij}`. -/
def LoopExpr.remPQ {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (p q : ℕ) : ℂ :=
  -((D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹) / ((D : ℂ) * N) *
    ∑ ι : Fin T.nb → Fin D, ∑ i : Idx D N, ∑ j : Idx D N,
      if i.1 = j.1 then
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          ∫ h, wirt p q (fun w => T.pkgVal e ι i j (setEntry h i j w)) (h i j) ∂μ
      else 0


/-! ### Resolvent polynomials over the slots of an environment, with a degree and a mass -/

/-- A factor of a resolvent monomial over the standard basis, carrying a slot `(c_a Λ, z_a)` of the
environment (or `(c_a Λ, z̄_a)` when the flag is set). -/
private def PolySlot {D N : ℕ} (e : LoopEnv D N) (g : ResFactor D N) : Prop :=
  (∃ i, g.1 = Pi.single i 1) ∧ (∃ j, g.2.1 = Pi.single j 1) ∧
    ∃ a : Fin 2, g.2.2 = ((e.c a : ℂ) • lam D N e.A, if e.s a then star (e.z a) else e.z a)

/-- The function `f` of the array is the value of a resolvent polynomial with at most `n` factors
per term, every factor carrying a slot of `e`, and coefficient mass at most `μ`. -/
private def PolyRP {D N : ℕ} (e : LoopEnv D N) (n : ℕ) (μ : ℝ)
    (f : (Idx D N → Idx D N → ℂ) → ℂ) : Prop :=
  ∃ P : ResPoly D N, (∀ h, f h = resPolyEval P h) ∧
    (∀ t ∈ P, t.2.length ≤ n ∧ ∀ g ∈ t.2, PolySlot e g) ∧ (P.map fun t => ‖t.1‖).sum ≤ μ

/-- Larger degree and mass bounds are allowed. -/
private lemma PolyRP_mono {D N : ℕ} {e : LoopEnv D N} {n n' : ℕ} {μ μ' : ℝ}
    {f : (Idx D N → Idx D N → ℂ) → ℂ} (hn : n ≤ n') (hμ : μ ≤ μ') (hf : PolyRP e n μ f) :
    PolyRP e n' μ' f := by
  obtain ⟨P, h1, h2, h3⟩ := hf
  exact ⟨P, h1, fun t ht => ⟨(h2 t ht).1.trans hn, (h2 t ht).2⟩, h3.trans hμ⟩

/-- Functions that agree at every array are the same function for `PolyRP`. -/
private lemma PolyRP_congr {D N : ℕ} {e : LoopEnv D N} {n : ℕ} {μ : ℝ}
    {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hfg : ∀ h, f h = g h) (hf : PolyRP e n μ f) :
    PolyRP e n μ g := by
  obtain ⟨P, h1, h2, h3⟩ := hf
  exact ⟨P, fun h => (hfg h).symm.trans (h1 h), h2, h3⟩

/-- A constant is a resolvent polynomial of degree `0`. -/
private lemma PolyRP_const {D N : ℕ} (e : LoopEnv D N) (c : ℂ) (μ : ℝ) (hc : ‖c‖ ≤ μ) :
    PolyRP e 0 μ (fun _ => c) := by
  refine ⟨[(c, [])], fun h => ?_, ?_, ?_⟩
  · simp [resPolyEval, resMonoEval]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp
  · simpa using hc

/-- The sum of two resolvent polynomials. -/
private lemma PolyRP_add {D N : ℕ} {e : LoopEnv D N} {n : ℕ} {μ ν : ℝ}
    {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : PolyRP e n μ f) (hg : PolyRP e n ν g) :
    PolyRP e n (μ + ν) (fun h => f h + g h) := by
  obtain ⟨P, h1, h2, h3⟩ := hf
  obtain ⟨Q, k1, k2, k3⟩ := hg
  refine ⟨P ++ Q, fun h => ?_, ?_, ?_⟩
  · change f h + g h = _
    rw [resPolyEval_append, h1, k1]
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    exacts [h2 t ht, k2 t ht]
  · simp only [List.map_append, List.sum_append]
    exact add_le_add h3 k3

/-- The coefficient mass of a product of two resolvent polynomials is the product of the masses. -/
private lemma PolyRP_mass_mul {D N : ℕ} (P Q : ResPoly D N) :
    ((resPolyMul P Q).map fun t => ‖t.1‖).sum =
      (P.map fun t => ‖t.1‖).sum * (Q.map fun t => ‖t.1‖).sum := by
  induction P with
  | nil => simp [resPolyMul]
  | cons s P ih =>
    have hsplit : resPolyMul (s :: P) Q =
        (Q.map fun t => (s.1 * t.1, s.2 ++ t.2)) ++ resPolyMul P Q := by
      simp [resPolyMul]
    rw [hsplit, List.map_append, List.sum_append, ih]
    have h1 : ((Q.map fun t => (s.1 * t.1, s.2 ++ t.2)).map fun t => ‖t.1‖).sum =
        ‖s.1‖ * (Q.map fun t => ‖t.1‖).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      simp
    rw [h1]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The product of two resolvent polynomials: the degrees add and the masses multiply. -/
private lemma PolyRP_mul {D N : ℕ} {e : LoopEnv D N} {n m : ℕ} {μ ν : ℝ}
    {f g : (Idx D N → Idx D N → ℂ) → ℂ} (hf : PolyRP e n μ f) (hg : PolyRP e m ν g) :
    PolyRP e (n + m) (μ * ν) (fun h => f h * g h) := by
  obtain ⟨P, h1, h2, h3⟩ := hf
  obtain ⟨Q, k1, k2, k3⟩ := hg
  refine ⟨resPolyMul P Q, fun h => ?_, ?_, ?_⟩
  · change f h * g h = _
    rw [resPolyEval_mul, h1, k1]
  · intro t ht
    simp only [resPolyMul, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨s, hs, t', ht', rfl⟩ := ht
    refine ⟨?_, fun g hg => ?_⟩
    · simp only [List.length_append]
      exact add_le_add (h2 s hs).1 (k2 t' ht').1
    · rcases List.mem_append.1 hg with hg | hg
      exacts [(h2 s hs).2 g hg, (k2 t' ht').2 g hg]
  · rw [PolyRP_mass_mul]
    exact mul_le_mul h3 k3 (List.sum_nonneg fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _) ((List.sum_nonneg fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _).trans h3)

/-- A finite sum of resolvent polynomials of the same degree and mass: the mass is multiplied by the
number of terms. -/
private lemma PolyRP_sum {D N : ℕ} {ι : Type*} (e : LoopEnv D N) (s : Finset ι)
    {F : ι → (Idx D N → Idx D N → ℂ) → ℂ} {n : ℕ} {μ : ℝ}
    (hF : ∀ k ∈ s, PolyRP e n μ (F k)) :
    PolyRP e n ((s.card : ℝ) * μ) (fun h => ∑ k ∈ s, F k h) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp [resPolyEval], by simp, by simp⟩
  | insert a s ha ih =>
    have h1 := PolyRP_add (hF a (Finset.mem_insert_self _ _))
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))
    refine PolyRP_congr (fun h => (Finset.sum_insert ha).symm) (PolyRP_mono le_rfl ?_ h1)
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    linarith

/-- A product over a list of resolvent polynomials: the degrees add up and the masses multiply. -/
private lemma PolyRP_prod {D N : ℕ} {α : Type*} (e : LoopEnv D N) (l : List α)
    (F : α → (Idx D N → Idx D N → ℂ) → ℂ) (n : α → ℕ) (μ : α → ℝ)
    (hF : ∀ x ∈ l, PolyRP e (n x) (μ x) (F x)) :
    PolyRP e (l.map n).sum (l.map μ).prod (fun h => (l.map fun x => F x h).prod) := by
  induction l with
  | nil => exact PolyRP_const e 1 1 (by simp)
  | cons x l ih =>
    simpa using PolyRP_mul (hF x (by simp)) (ih fun y hy => hF y (by simp [hy]))

/-! ### Entries of words -/

/-- The letter is a resolvent `𝒢_a`. -/
private def PolyIsRes : LoopLetter → Bool
  | .res _ => true
  | _ => false

/-- The letter is a limit `𝔐_a`. -/
private def PolyIsDet : LoopLetter → Bool
  | .det _ => true
  | _ => false

/-- The letter is one of the two `Λ̃`. -/
private def PolyIsLam : LoopLetter → Bool
  | .lamt _ => true
  | _ => false

/-- An entry `(𝒢_a)_{kl}` of a resolvent is a resolvent polynomial of degree `1` and mass `1`: the
single factor `e_k^* (h + c_a Λ - z_a)⁻¹ e_l`. -/
private lemma PolyRP_res {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) (k l : Idx D N) :
    PolyRP e 1 1 (fun h => e.G h a k l) := by
  refine ⟨[(1, [(Pi.single k 1, Pi.single l 1, ((e.c a : ℂ) • lam D N e.A,
    if e.s a then star (e.z a) else e.z a))])], fun h => ?_, ?_, ?_⟩
  · simp [resPolyEval, resMonoEval, resFactorEval, LoopEnv.G]
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨by simp, fun g hg => ?_⟩
    simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨⟨k, rfl⟩, ⟨l, rfl⟩, ⟨a, rfl⟩⟩
  · simp

/-- An entry is bounded by the operator norm: `|A_{ij}| ≤ ‖A‖`. -/
private lemma PolyX_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : A i j = ((Matrix.toEuclideanCLM (𝕜 := ℂ) A) (EuclideanSpace.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec_single]
  rw [h3]
  exact (PiLp.norm_apply_le _ i).trans h1

/-- An entry of a block projection `E_x` has modulus at most `1`. -/
private lemma PolyX_E_entry {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (y : ℕ)
    (i k : Idx D N) : ‖e.E ι y i k‖ ≤ 1 := by
  unfold LoopEnv.E
  split_ifs
  · simp only [Ea, Matrix.diagonal_apply]
    split_ifs <;> simp
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

/-- Step of a product of matrices of resolvent polynomials: the entry `(X W)_{ij}` is the sum over
the middle index `k` of the products `X_{ik} W_{kj}`. -/
private lemma PolyX_step {D N : ℕ} (e : LoopEnv D N)
    {X W : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ} {n m : ℕ} {μ ν : ℝ}
    (hX : ∀ i k, PolyRP e n μ (fun h => X h i k))
    (hW : ∀ k j, PolyRP e m ν (fun h => W h k j)) (i j : Idx D N) :
    PolyRP e (n + m) (((D : ℝ) * N) * (μ * ν)) (fun h => (X h * W h) i j) := by
  have h1 := PolyRP_sum e (Finset.univ : Finset (Idx D N))
    (F := fun k h => X h i k * W h k j) (fun k _ => PolyRP_mul (hX i k) (hW k j))
  have hc : ((Finset.univ : Finset (Idx D N)).card : ℝ) = (D : ℝ) * N := by
    simp [Finset.card_univ, Fintype.card_prod]
  rw [hc] at h1
  exact PolyRP_congr (fun h => by simp [Matrix.mul_apply]) h1

/-- The entries of a word are resolvent polynomials: with `κ = DN`, a word with `r` resolvents,
`d` limits `𝔐_a` and `l` letters `Λ̃` has entries of degree `r` and mass `κ^{|w|} β^d ‖Λ̃‖^l`,
where `β` bounds `‖𝔐_a‖`. -/
private lemma PolyX_word {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (β : ℝ)
    (hβ : ∀ a, opNorm (e.M a) ≤ β) :
    ∀ (w : List LoopLetter) (i j : Idx D N),
      PolyRP e (w.countP PolyIsRes)
        (((D : ℝ) * N) ^ w.length * β ^ (w.countP PolyIsDet) * opNorm e.Lt ^ (w.countP PolyIsLam))
        (fun h => loopWordMat (e.G h) e.M (e.E ι) e.Lt w i j) := by
  intro w
  induction w with
  | nil =>
    intro i j
    refine PolyRP_mono le_rfl (by simp) (PolyRP_congr (fun h => ?_) (PolyRP_const e
      (if i = j then 1 else 0) 1 (by split_ifs <;> simp)))
    simp [loopWordMat, Matrix.one_apply]
  | cons x w ih =>
    intro i j
    have hstep : ∀ (X : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) (n : ℕ) (μ : ℝ),
        (∀ i k, PolyRP e n μ (fun h => X h i k)) →
        (∀ h, loopWordMat (e.G h) e.M (e.E ι) e.Lt (x :: w) =
          X h * loopWordMat (e.G h) e.M (e.E ι) e.Lt w) →
        PolyRP e (n + w.countP PolyIsRes) (((D : ℝ) * N) * (μ * (((D : ℝ) * N) ^ w.length *
          β ^ (w.countP PolyIsDet) * opNorm e.Lt ^ (w.countP PolyIsLam))))
          (fun h => loopWordMat (e.G h) e.M (e.E ι) e.Lt (x :: w) i j) := by
      intro X n μ hX hXe
      exact PolyRP_congr (fun h => by rw [hXe h]) (PolyX_step e hX ih i j)
    cases x with
    | res a =>
      refine PolyRP_mono (le_of_eq (by simp [List.countP_cons, PolyIsRes]; omega))
        (le_of_eq (by simp [PolyIsDet, PolyIsLam, pow_succ]; ring))
        (hstep (fun h => e.G h a) 1 1 (fun i k => PolyRP_res e a i k)
          (fun h => by simp [loopWordMat]))
    | det a =>
      refine PolyRP_mono (le_of_eq (by simp [PolyIsRes]))
        (le_of_eq (by simp [List.countP_cons, PolyIsDet, PolyIsLam, pow_succ]; ring))
        (hstep (fun _ => e.M a) 0 β (fun i k => PolyRP_const e _ β
          ((PolyX_entry_le _ i k).trans (hβ a))) (fun h => by simp [loopWordMat]))
    | proj y =>
      refine PolyRP_mono (le_of_eq (by simp [PolyIsRes]))
        (le_of_eq (by simp [PolyIsDet, PolyIsLam, pow_succ]; ring))
        (hstep (fun _ => e.E ι y) 0 1 (fun i k => PolyRP_const e _ 1 (PolyX_E_entry e ι y i k))
          (fun h => by simp [loopWordMat]))
    | lamt o =>
      refine PolyRP_mono (le_of_eq (by simp [PolyIsRes]))
        (le_of_eq (by simp [List.countP_cons, PolyIsDet, PolyIsLam, pow_succ]; ring))
        (hstep (fun _ => e.Lt) 0 (opNorm e.Lt) (fun i k => PolyRP_const e _ _
          (PolyX_entry_le _ i k)) (fun h => by simp [loopWordMat]))

/-- The normalized trace of a matrix of resolvent polynomials, for `DN ≥ 1`, has the same degree
and mass as an entry. -/
private lemma PolyX_ntr {D N : ℕ} (e : LoopEnv D N) (hκ : 1 ≤ D * N)
    {W : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ} {n : ℕ} {μ : ℝ}
    (hW : ∀ i j, PolyRP e n μ (fun h => W h i j)) :
    PolyRP e n μ (fun h => ntr (W h)) := by
  have h1 := PolyRP_sum e (Finset.univ : Finset (Idx D N)) (F := fun i h => W h i i)
    (fun i _ => hW i i)
  have hc : ((Finset.univ : Finset (Idx D N)).card : ℝ) = (D : ℝ) * N := by
    simp [Finset.card_univ, Fintype.card_prod]
  rw [hc] at h1
  have hκ' : (0 : ℝ) < (D : ℝ) * N := by exact_mod_cast hκ
  have h2 := PolyRP_mul (PolyRP_const e ((Fintype.card (Idx D N) : ℂ)⁻¹) (((D : ℝ) * N)⁻¹)
    (by simp [Fintype.card_prod])) h1
  refine PolyRP_congr (fun h => ?_) (PolyRP_mono (by simp) (le_of_eq ?_) h2)
  · simp [ntr, Matrix.trace]
  · rw [← mul_assoc, inv_mul_cancel₀ hκ'.ne', one_mul]

/-! ### Weights, loops and the focused loop -/

/-- A weight `⟨(𝒢_a - 𝔐_a) E_x⟩` of (5.33) [definition_class_of_expression_loop] is a resolvent
polynomial of degree `1` and mass `(DN)² (1 + β)`, for `DN ≥ 1` and `β ≥ ‖𝔐_a‖`. -/
private lemma PolyX_weight {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (hκ : 1 ≤ D * N)
    (β : ℝ) (hβ : ∀ a, opNorm (e.M a) ≤ β) (a : Fin 2) (y : ℕ) :
    PolyRP e 1 (((D : ℝ) * N) ^ 2 * (1 + β))
      (fun h => ntr ((e.G h a - e.M a) * e.E ι y)) := by
  have h1 := PolyRP_mono (n' := 1) (by simp [List.countP_cons, PolyIsRes]) le_rfl
    (PolyX_ntr e hκ (fun i j => PolyX_word e ι β hβ [.res a, .proj y] i j))
  have h2 := PolyRP_mono (n' := 1) (by simp [PolyIsRes]) le_rfl
    (PolyX_ntr e hκ (fun i j => PolyX_word e ι β hβ [.det a, .proj y] i j))
  have h3 := PolyRP_add h1 (PolyRP_mono (n' := 1) (by omega) le_rfl
    (PolyRP_mul (PolyRP_const e (-1) 1 (by simp)) h2))
  refine PolyRP_congr (fun h => ?_) (PolyRP_mono le_rfl (le_of_eq ?_) h3)
  · simp [ntr, loopWordMat, Matrix.sub_mul, Matrix.trace_sub]
    ring
  · simp [List.countP_cons, PolyIsDet, PolyIsLam]
    ring

/-- A product of powers over a list is the power of the sums of the exponents. -/
private lemma PolyX_prod_pow {α : Type*} (a b c : ℝ) (f g k : α → ℕ) (l : List α) :
    (l.map fun x => a ^ f x * b ^ g x * c ^ k x).prod =
      a ^ (l.map f).sum * b ^ (l.map g).sum * c ^ (l.map k).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, ih]
    ring

/-- The letters `Λ̃` of a word are counted by the two letters `Λ̃₁`, `Λ̃₂`. -/
private lemma PolyX_countP_lam (w : List LoopLetter) :
    w.countP PolyIsLam = w.count (.lamt 0) + w.count (.lamt 1) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    cases x with
    | lamt o => fin_cases o <;> simp [List.countP_cons, PolyIsLam, ih] <;> omega
    | res a => simp [PolyIsLam, ih]
    | det a => simp [PolyIsLam, ih]
    | proj y => simp [PolyIsLam, ih]

/-- An expression of the class has exactly two letters `Λ̃` over all its loops. -/
private lemma PolyX_lam_sum {T : LoopExpr} (hT : T.wf = true) :
    (T.loops.map fun w => w.countP PolyIsLam).sum = 2 := by
  simp only [LoopExpr.wf, Bool.and_eq_true, beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := hT
  simp only [PolyX_countP_lam, List.sum_map_add, h0, h1]

/-- Erasing the entry `w` at position `i` of a list removes its factor from a product. -/
@[to_additive]
private theorem PolyX_prod_eraseIdx {α β : Type*} [CommMonoid β] (f : α → β) :
    ∀ (l : List α) (i : ℕ) (w : α), l[i]? = some w →
      ((l.eraseIdx i).map f).prod * f w = (l.map f).prod
  | [], i, w, h => by simp at h
  | y :: l, 0, w, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [mul_comm]
  | y :: l, i + 1, w, h => by
      have := PolyX_prod_eraseIdx f l i w (by simpa using h)
      simp only [List.eraseIdx_cons_succ, List.map_cons, List.prod_cons]
      rw [mul_assoc, this]

/-- The data returned by `focus`: the focused loop is a permutation of `𝒢_a · tl`. -/
private theorem PolyX_focus {T : LoopExpr} {ℓ : ℕ} {a : Fin 2} {tl : List LoopLetter}
    (h : T.focus = some (ℓ, a, tl)) :
    ∃ w : List LoopLetter, T.loops[ℓ]? = some w ∧ w.Perm (.res a :: tl) := by
  unfold LoopExpr.focus at h
  dsimp only at h
  generalize (if 1 ≤ T.kk 0 then (0 : Fin 2) else 1) = o at h
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i a' tl' hrot
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨w, hw, by rw [← hrot]; exact (List.rotate_perm w r).symm⟩
        · cases h
      · cases h

/-! ### The values of the expressions of the class -/

/-- The characters `m` (resolvents in the loops) and `u` (weights): the degree of an expression. -/
private lemma PolyX_degree (T : LoopExpr) :
    (T.charsZ.1 + T.charsZ.2.2.1).toNat =
      (T.loops.map fun w => w.countP PolyIsRes).sum + T.weights.length := by
  have hc : T.charsZ = ((((T.loops.map fun w => w.countP PolyIsRes).sum : ℕ) : ℤ),
      (T.loops.length : ℤ), (T.weights.length : ℤ), (T.S : ℤ)) := rfl
  rw [hc]
  dsimp only
  rw [← Nat.cast_add, Int.toNat_natCast]

/-- The norm of the limits `𝔐_a` is bounded by `‖𝔐₀‖ + ‖𝔐₁‖`. -/
private lemma PolyX_beta0 {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) :
    opNorm (e.M a) ≤ opNorm (e.M 0) + opNorm (e.M 1) := by
  have h0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
  have h1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
  fin_cases a <;> simp <;> linarith

/-- The product of the light weights of (5.33) [definition_class_of_expression_loop] is a
resolvent polynomial of degree `u` and mass `((DN)² (1 + ‖𝔐₀‖ + ‖𝔐₁‖))^u`, for `DN ≥ 1`. -/
private lemma PolyX_weights {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (hκ : 1 ≤ D * N)
    (ws : List (Fin 2 × ℕ)) :
    PolyRP e ws.length
      ((((D : ℝ) * N) ^ 2 * (1 + opNorm (e.M 0) + opNorm (e.M 1))) ^ ws.length)
      (fun h => (ws.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod) := by
  have := PolyRP_prod e ws (fun p h => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)) (fun _ => 1)
    (fun _ => ((D : ℝ) * N) ^ 2 * (1 + (opNorm (e.M 0) + opNorm (e.M 1))))
    (fun p _ => PolyX_weight e ι hκ _ (PolyX_beta0 e) p.1 p.2)
  simpa [add_assoc] using this

/-- The product of the loop traces of a list of loops is a resolvent polynomial whose degree is the
number of resolvents and whose mass is `(DN)^{Σ|w|} (1 + ‖𝔐₀‖ + ‖𝔐₁‖)^{#𝔐} ‖Λ̃‖^{#Λ̃}`, for
`DN ≥ 1`. -/
private lemma PolyX_loops {D N nb : ℕ} (e : LoopEnv D N) (ι : Fin nb → Fin D) (hκ : 1 ≤ D * N)
    (ls : List (List LoopLetter)) :
    PolyRP e (ls.map fun w => w.countP PolyIsRes).sum
      (((D : ℝ) * N) ^ (ls.map List.length).sum *
        (1 + opNorm (e.M 0) + opNorm (e.M 1)) ^ (ls.map fun w => w.countP PolyIsDet).sum *
        opNorm e.Lt ^ (ls.map fun w => w.countP PolyIsLam).sum)
      (fun h => (ls.map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod) := by
  have hβ : ∀ a, opNorm (e.M a) ≤ 1 + opNorm (e.M 0) + opNorm (e.M 1) := fun a => by
    have h0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
    have h1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
    linarith [PolyX_beta0 e a]
  have := PolyRP_prod e ls (fun w h => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w))
    (fun w => w.countP PolyIsRes)
    (fun w => ((D : ℝ) * N) ^ w.length * (1 + opNorm (e.M 0) + opNorm (e.M 1)) ^
      (w.countP PolyIsDet) * opNorm e.Lt ^ (w.countP PolyIsLam))
    (fun w _ => PolyX_ntr e hκ (fun i j => PolyX_word e ι _ hβ w i j))
  rwa [PolyX_prod_pow] at this

/-- The function `(F 𝒢)_{ij} W ⋯ f ⋯` of (5.41) [reminder_terms_expansion] is a resolvent
polynomial of degree `m + u` and mass `(DN)^K (1 + ‖𝔐₀‖ + ‖𝔐₁‖)^J ‖Λ̃‖²`. -/
private lemma PolyX_pkgVal {D N : ℕ} (T : LoopExpr) (hT : T.wf = true) (e : LoopEnv D N)
    (ι : Fin T.nb → Fin D) (i j : Idx D N) :
    PolyRP e ((T.loops.map fun w => w.countP PolyIsRes).sum + T.weights.length)
      (((D : ℝ) * N) ^ (1 + 2 * T.weights.length + (T.loops.map List.length).sum) *
        (1 + opNorm (e.M 0) + opNorm (e.M 1)) ^ (1 + T.weights.length +
          (T.loops.map fun w => w.countP PolyIsDet).sum) * opNorm e.Lt ^ 2)
      (fun h => T.pkgVal e ι i j h) := by
  have hκ : 1 ≤ D * N := Nat.mul_pos (Fin.pos i.1) (Fin.pos i.2)
  have hM0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
  have hM1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
  have hBd : 0 ≤ 1 + opNorm (e.M 0) + opNorm (e.M 1) := by linarith
  have hκ0 : (0 : ℝ) ≤ (D : ℝ) * N := by positivity
  have hβ : ∀ a, opNorm (e.M a) ≤ 1 + opNorm (e.M 0) + opNorm (e.M 1) := fun a => by
    linarith [PolyX_beta0 e a]
  rcases hfoc : T.focus with _ | ⟨ℓ, a, tl⟩
  · have hnn : (0 : ℝ) ≤ ((D : ℝ) * N) ^ (1 + 2 * T.weights.length +
        (T.loops.map List.length).sum) * (1 + opNorm (e.M 0) + opNorm (e.M 1)) ^
        (1 + T.weights.length + (T.loops.map fun w => w.countP PolyIsDet).sum) *
        opNorm e.Lt ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hκ0 _) (pow_nonneg hBd _)) (sq_nonneg _)
    refine PolyRP_mono (Nat.zero_le _) le_rfl
      (PolyRP_congr (fun h => ?_) (PolyRP_const e 0 _ (by rw [norm_zero]; exact hnn)))
    simp [LoopExpr.pkgVal, hfoc]
  · obtain ⟨w, hw, hperm⟩ := PolyX_focus hfoc
    have hpk : ∀ h, T.pkgVal e ι i j h =
        loopWordMat (e.G h) e.M (e.E ι) e.Lt (LoopLetter.det a :: tl ++ [LoopLetter.res a]) i j *
          (T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
          ((T.loops.eraseIdx ℓ).map fun w =>
            ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod := by
      intro h
      simp only [LoopExpr.pkgVal, hfoc]
    have h4 := PolyRP_mul (PolyRP_mul
      (PolyX_word e ι _ hβ (LoopLetter.det a :: tl ++ [LoopLetter.res a]) i j)
      (PolyX_weights e ι hκ T.weights)) (PolyX_loops e ι hκ (T.loops.eraseIdx ℓ))
    have hcnt1 : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).countP PolyIsRes =
        tl.countP PolyIsRes + 1 := by
      simp [List.countP_append, List.countP_cons, PolyIsRes]
    have hcnt2 : w.countP PolyIsRes = tl.countP PolyIsRes + 1 := by
      rw [hperm.countP_eq]
      simp [List.countP_cons, PolyIsRes]
    have hs0 := PolyX_sum_eraseIdx (fun w : List LoopLetter => w.countP PolyIsRes) T.loops ℓ w hw
    have hs1 := PolyX_sum_eraseIdx (List.length : List LoopLetter → ℕ) T.loops ℓ w hw
    have hs2 := PolyX_sum_eraseIdx (fun w : List LoopLetter => w.countP PolyIsDet) T.loops ℓ w hw
    have hs3 := PolyX_sum_eraseIdx (fun w : List LoopLetter => w.countP PolyIsLam) T.loops ℓ w hw
    have hlam := PolyX_lam_sum hT
    have hwl : w.length = tl.length + 1 := by simpa using hperm.length_eq
    have hwd : w.countP PolyIsDet = tl.countP PolyIsDet := by
      rw [hperm.countP_eq]
      simp [PolyIsDet]
    have hwlam : w.countP PolyIsLam = tl.countP PolyIsLam := by
      rw [hperm.countP_eq]
      simp [PolyIsLam]
    have hlen1 : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).length = tl.length + 2 := by simp
    have hdet1 : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).countP PolyIsDet =
        tl.countP PolyIsDet + 1 := by
      simp [List.countP_append, List.countP_cons, PolyIsDet]
    have hlam1 : (LoopLetter.det a :: tl ++ [LoopLetter.res a]).countP PolyIsLam =
        tl.countP PolyIsLam := by
      simp [List.countP_append, PolyIsLam]
    refine PolyRP_congr (fun h => (hpk h).symm) (PolyRP_mono (le_of_eq ?_) (le_of_eq ?_) h4)
    · simp only [hcnt1]
      omega
    · rw [hlen1, hdet1, hlam1]
      have eA : (T.loops.map List.length).sum =
          ((T.loops.eraseIdx ℓ).map List.length).sum + (tl.length + 1) := by omega
      have eD : (T.loops.map fun w => w.countP PolyIsDet).sum =
          ((T.loops.eraseIdx ℓ).map fun w => w.countP PolyIsDet).sum + tl.countP PolyIsDet := by
        omega
      have eL : opNorm e.Lt ^ 2 = opNorm e.Lt ^ (tl.countP PolyIsLam) *
          opNorm e.Lt ^ ((T.loops.eraseIdx ℓ).map fun w => w.countP PolyIsLam).sum := by
        rw [← pow_add]
        congr 1
        omega
      rw [eA, eD, eL]
      generalize 1 + opNorm (e.M 0) + opNorm (e.M 1) = Bd
      ring

/-- `pkgVal` of an expression of the class `𝒯` is a resolvent polynomial over the standard
basis. -/
theorem loop_pkgVal_poly (T : LoopExpr) (hT : T.wf = true) :
    ∃ c : ℕ, ∀ (D N : ℕ) (e : LoopEnv D N) (ι : Fin T.nb → Fin D) (i j : Idx D N),
      ∃ P : ResPoly D N,
      (∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        T.pkgVal e ι i j h = resPolyEval P h) ∧
      (∀ t ∈ P, t.2.length ≤ (T.charsZ.1 + T.charsZ.2.2.1).toNat ∧ ∀ f ∈ t.2,
        (∃ i, f.1 = Pi.single i 1) ∧ (∃ j, f.2.1 = Pi.single j 1) ∧
        ∃ a : Fin 2, f.2.2 = ((e.c a : ℂ) • lam D N e.A, if e.s a then star (e.z a) else e.z a)) ∧
      (P.map fun t => ‖t.1‖).sum ≤
        ((D : ℝ) * N) ^ c * (1 + opNorm (e.M 0) + opNorm (e.M 1)) ^ c * opNorm e.Lt ^ 2 := by
  refine ⟨(1 + 2 * T.weights.length + (T.loops.map List.length).sum) +
    (1 + T.weights.length + (T.loops.map fun w => w.countP PolyIsDet).sum),
    fun D N e ι i j => ?_⟩
  have hM0 : 0 ≤ opNorm (e.M 0) := norm_nonneg _
  have hM1 : 0 ≤ opNorm (e.M 1) := norm_nonneg _
  have hb : (1 : ℝ) ≤ 1 + opNorm (e.M 0) + opNorm (e.M 1) := by linarith
  have hpos : 0 < D * N := Nat.mul_pos (Fin.pos i.1) (Fin.pos i.2)
  have hk : (1 : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hpos
  obtain ⟨P, h1, h2, h3⟩ := PolyX_pkgVal T hT e ι i j
  refine ⟨P, fun h _ => h1 h, fun t ht => ⟨?_, fun f hf => (h2 t ht).2 f hf⟩, ?_⟩
  · rw [PolyX_degree]
    exact (h2 t ht).1
  · refine h3.trans (mul_le_mul_of_nonneg_right (mul_le_mul
      (pow_le_pow_right₀ hk (Nat.le_add_right _ _)) (pow_le_pow_right₀ hb (Nat.le_add_left _ _))
      (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) (sq_nonneg _))

end RBMTransitionEdge

end
