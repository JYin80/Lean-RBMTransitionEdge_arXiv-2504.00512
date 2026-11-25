module

public import RBMTransitionEdge.Localized.Expansion.PkgWords
public import RBMTransitionEdge.Localized.Expansion.Reach

@[expose] public section

/-!
# The deterministic loops with one `Λ̃` of the further expansion

A loop with one `Λ̃` and no resolvent at the slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law], by (A.7)
[add_one_more_Lambda], with the gain `Im m` of (5.5) [regular_estimate_localized_eigenvector] and
(5.22) [regular_estimate_localized_eigenvalue] for `⟨𝔐_a Λ̃ 𝔐_b E_x⟩`, `a ≠ b`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The loop is `⟨𝔐_a Λ̃ 𝔐_b E_x⟩` up to rotation, with `a ≠ b`. -/
def pkgGainLoop (w : List PkgLetter) : Bool :=
  (List.range w.length).any fun r => match w.rotate r with
    | [.lw (.det a), .lw (.lamt _), .lw (.det b), .lw (.proj _)] => a != b
    | _ => false


/-! ## Norm and trace tools -/

section Tools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma DL_opNorm_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

private lemma DL_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [DL_opNorm_eq] using norm_mul_le A B

private lemma DL_op_smul (c : ℂ) (A : Matrix ι ι ℂ) : opNorm (c • A) = ‖c‖ * opNorm A := by
  simpa only [DL_opNorm_eq] using norm_smul c A

private lemma DL_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

private lemma DL_op_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

private lemma DL_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [DL_opNorm_eq] using Matrix.l2_opNorm_conjTranspose A

private lemma DL_op_diag (d : ι → ℂ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ j, ‖d j‖ ≤ B) :
    opNorm (diagonal d) ≤ B := by
  rw [DL_opNorm_eq, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hB).2 h

private lemma DL_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  have h3 : ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := by
    simp
  rw [h3] at h2
  exact h2.trans h

/-- `|⟨A⟩| ≤ ‖A‖`. -/
private lemma DL_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => DL_entry_le A i i
    _ = _ := by simp

omit [DecidableEq ι] in
/-- Cyclicity of the normalized trace. -/
private lemma DL_ntr_comm (P Q : Matrix ι ι ℂ) : ntr (P * Q) = ntr (Q * P) := by
  unfold ntr
  rw [Matrix.trace_mul_comm]

omit [DecidableEq ι] in
private lemma DL_ntr_smul (c : ℂ) (A : Matrix ι ι ℂ) : ntr (c • A) = c * ntr A := by
  simp [ntr, Matrix.trace_smul]
  ring

omit [DecidableEq ι] in
private lemma DL_ntr_add (A B : Matrix ι ι ℂ) : ntr (A + B) = ntr A + ntr B := by
  simp [ntr, Matrix.trace_add, mul_add]

omit [DecidableEq ι] in
private lemma DL_ntr_sub (A B : Matrix ι ι ℂ) : ntr (A - B) = ntr A - ntr B := by
  simp [ntr, Matrix.trace_sub, mul_sub]

omit [DecidableEq ι] in
private lemma DL_ntr_sum {κ : Type*} (s : Finset κ) (f : κ → Matrix ι ι ℂ) :
    ntr (∑ x ∈ s, f x) = ∑ x ∈ s, ntr (f x) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

omit [DecidableEq ι] in
/-- `⟨Λ²⟩ ≥ 0` for Hermitian `Λ`. -/
private lemma DL_avgSq_nonneg [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    0 ≤ avgSq Λ := by
  have e : (Λ * Λ).trace = (((∑ i, ∑ j, ‖Λ i j‖ ^ 2 : ℝ)) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Λ j i = star (Λ i j) := by rw [← hΛ.apply i j, star_star]
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  unfold avgSq ntr
  rw [e, show ((Fintype.card ι : ℂ)⁻¹ : ℂ) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end Tools

/-! ## Block projections -/

section Blocks

variable {D N : ℕ}

private lemma DL_Ea_mul (a b : Fin D) :
    Ea D N a * Ea D N b = if a = b then Ea D N a else 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    congr 1
    funext p
    by_cases hp : p.1 = a <;> simp [hp]
  · simp only [h, ↓reduceIte]
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p.1 = a
      · have : ¬ p.1 = b := fun e => h (hp.symm.trans e)
        simp [hp, h]
      · simp [hp]
    · simp [hpq]

private lemma DL_op_Ea (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  unfold Ea
  refine DL_op_diag _ 1 (by norm_num) fun p => ?_
  by_cases hp : p.1 = a <;> simp [hp]

/-- `Σ_a E_a = 1`. -/
private lemma DL_sum_Ea : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  rw [Matrix.sum_apply]
  unfold Ea
  by_cases hpq : p = q
  · subst hpq
    simp [Matrix.diagonal_apply_eq]
  · simp [hpq]

/-- The diagonal entries of `lam D N A` vanish. -/
private lemma DL_lam_diag (A : Matrix (Fin N) (Fin N) ℂ) (p : Idx D N) :
    lam D N A p p = 0 := by
  have h2 : ¬ (3 ≤ D ∧ (p.1 : ℕ) + 1 = D ∧ (p.1 : ℕ) = 0) := by
    have := p.1.isLt
    omega
  simp [lam, fwd, h2]

/-- Every diagonal block of `lam D N A` is traceless: `⟨E_a Λ⟩ = 0`. -/
private lemma DL_lam_block (A : Matrix (Fin N) (Fin N) ℂ) (a : Fin D) :
    ntr (Ea D N a * lam D N A) = 0 := by
  unfold ntr Ea
  rw [Matrix.trace]
  simp [Matrix.diag, Matrix.diagonal_mul, DL_lam_diag]

end Blocks

/-! ## The normal form of (A.7) [add_one_more_Lambda]

A product of scalars `c · 1` with `|c| ≤ 1`, block projections `E_a` and factors `M`, `M^*` is a
sum of at most `D^n` terms `c L Π_i M^{s_i} E_{a_i}` with `|c| ≤ 1` and `L ∈ {1, E_a}`: insert
`1 = Σ_a E_a` after each `M^s` and use `E_a E_b = δ_{ab} E_a`. -/

section Normal

variable {D N : ℕ}

/-- The product `Π_i M^{s_i} E_{a_i}` of (A.7) [add_one_more_Lambda] for the list `(s_i, a_i)`,
`s_i = true` for `M^*`. -/
private def DL_np (M : Matrix (Idx D N) (Idx D N) ℂ) (l : List (Bool × Fin D)) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  (l.map fun p => (if p.1 then Mᴴ else M) * Ea D N p.2).prod

/-- A leading factor: `1` or a block projection `E_a`. -/
private def DL_lead (L : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  L = 1 ∨ ∃ a : Fin D, L = Ea D N a

/-- A term `(c, L, l)` with `|c| ≤ 1`, a leading factor `L` and at most `n` factors in `l`. -/
private def DL_tm (n : ℕ) (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) : Prop :=
  ‖τ.1‖ ≤ 1 ∧ DL_lead τ.2.1 ∧ τ.2.2.length ≤ n

/-- The matrix `c L Π_i M^{s_i} E_{a_i}` of a term. -/
private def DL_val (M : Matrix (Idx D N) (Idx D N) ℂ)
    (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) : Matrix (Idx D N) (Idx D N) ℂ :=
  τ.1 • (τ.2.1 * DL_np M τ.2.2)

/-- `Y` is a sum of at most `K` terms with at most `n` factors each. -/
private def DL_nf (M : Matrix (Idx D N) (Idx D N) ℂ) (n K : ℕ) (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    Prop :=
  ∃ T : List (ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)), T.length ≤ K ∧
    (∀ τ ∈ T, DL_tm n τ) ∧ Y = (T.map (DL_val M)).sum

/-- A letter: a scalar `c · 1` with `|c| ≤ 1`, a block projection `E_a`, or `M`, `M^*`. -/
private def DL_good (M L : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  (∃ c : ℂ, ‖c‖ ≤ 1 ∧ L = c • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ∨ (∃ a : Fin D, L = Ea D N a) ∨
    ∃ s : Bool, L = if s then Mᴴ else M

private lemma DL_np_nil (M : Matrix (Idx D N) (Idx D N) ℂ) : DL_np M [] = 1 := rfl

private lemma DL_np_concat (M : Matrix (Idx D N) (Idx D N) ℂ) (l : List (Bool × Fin D))
    (p : Bool × Fin D) :
    DL_np M (l ++ [p]) = DL_np M l * ((if p.1 then Mᴴ else M) * Ea D N p.2) := by
  simp [DL_np, List.map_append, List.prod_append]

/-- The product of (A.7) [add_one_more_Lambda] in the form `List.ofFn`. -/
private lemma DL_np_ofFn (M : Matrix (Idx D N) (Idx D N) ℂ) (l : List (Bool × Fin D)) :
    DL_np M l = (List.ofFn fun i : Fin l.length =>
      (if (l.get i).1 then Mᴴ else M) * Ea D N (l.get i).2).prod := by
  unfold DL_np
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn]
  rfl

private lemma DL_nf_mono {M Y : Matrix (Idx D N) (Idx D N) ℂ} {n n' K K' : ℕ} (hn : n ≤ n')
    (hK : K ≤ K') (h : DL_nf M n K Y) : DL_nf M n' K' Y := by
  obtain ⟨T, hl, hT, rfl⟩ := h
  exact ⟨T, hl.trans hK, fun τ hτ => ⟨(hT τ hτ).1, (hT τ hτ).2.1, (hT τ hτ).2.2.trans hn⟩, rfl⟩

private lemma DL_nf_one (M : Matrix (Idx D N) (Idx D N) ℂ) : DL_nf M 0 1 1 :=
  ⟨[(1, 1, [])], le_rfl, fun τ hτ => by
    simp only [List.mem_singleton] at hτ
    subst hτ
    exact ⟨by simp, Or.inl rfl, le_rfl⟩, by simp [DL_val, DL_np_nil]⟩

/-- Multiplying on the right, term by term. -/
private lemma DL_nf_mul {M B Y : Matrix (Idx D N) (Idx D N) ℂ} {n n' K m : ℕ}
    (hstep : ∀ τ, DL_tm n τ → DL_nf M n' m (DL_val M τ * B)) (h : DL_nf M n K Y) :
    DL_nf M n' (K * m) (Y * B) := by
  obtain ⟨T, hl, hT, rfl⟩ := h
  have key : ∀ T : List (ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)),
      (∀ τ ∈ T, DL_tm n τ) → DL_nf M n' (T.length * m) ((T.map (DL_val M)).sum * B) := by
    intro T
    induction T with
    | nil => exact fun _ => ⟨[], by simp, by simp, by simp⟩
    | cons τ T ih =>
      intro hT
      obtain ⟨T₁, h₁, hT₁, e₁⟩ := hstep τ (hT τ List.mem_cons_self)
      obtain ⟨T₂, h₂, hT₂, e₂⟩ := ih fun τ' hτ' => hT τ' (List.mem_cons_of_mem _ hτ')
      refine ⟨T₁ ++ T₂, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_cons]
        nlinarith
      · intro τ' hτ'
        rcases List.mem_append.1 hτ' with h | h
        · exact hT₁ τ' h
        · exact hT₂ τ' h
      · rw [List.map_cons, List.sum_cons, Matrix.add_mul, e₁, e₂, List.map_append, List.sum_append]
  exact DL_nf_mono le_rfl (Nat.mul_le_mul_right m hl) (key T hT)

/-- A scalar letter: one term. -/
private lemma DL_step_scalar (M : Matrix (Idx D N) (Idx D N) ℂ) {n : ℕ} (c : ℂ) (hc : ‖c‖ ≤ 1)
    (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) (hτ : DL_tm n τ) :
    DL_nf M n 1 (DL_val M τ * (c • (1 : Matrix (Idx D N) (Idx D N) ℂ))) := by
  refine ⟨[(τ.1 * c, τ.2)], le_rfl, fun τ' hτ' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hτ'
    subst hτ'
    refine ⟨?_, hτ.2.1, hτ.2.2⟩
    rw [norm_mul]
    exact (mul_le_mul hτ.1 hc (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp only [DL_val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    rw [mul_comm]

/-- `L Π E_b = c L' Π` with `|c| ≤ 1` and a leading factor `L'`. -/
private lemma DL_lead_Ea (M : Matrix (Idx D N) (Idx D N) ℂ) {L : Matrix (Idx D N) (Idx D N) ℂ}
    (hL : DL_lead L) (l : List (Bool × Fin D)) (b : Fin D) :
    ∃ (c : ℂ) (L' : Matrix (Idx D N) (Idx D N) ℂ), ‖c‖ ≤ 1 ∧ DL_lead L' ∧
      L * DL_np M l * Ea D N b = c • (L' * DL_np M l) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', p, rfl⟩
  · simp only [DL_np_nil, Matrix.mul_one]
    rcases hL with rfl | ⟨a, rfl⟩
    · exact ⟨1, Ea D N b, by simp, Or.inr ⟨b, rfl⟩, by simp⟩
    · rw [DL_Ea_mul]
      by_cases h : a = b
      · exact ⟨1, Ea D N a, by simp, Or.inr ⟨a, rfl⟩, by simp [h]⟩
      · exact ⟨0, Ea D N a, by simp, Or.inr ⟨a, rfl⟩, by simp [h]⟩
  · rw [List.concat_eq_append]
    refine ⟨if p.2 = b then 1 else 0, L, by split_ifs <;> simp, hL, ?_⟩
    rw [DL_np_concat]
    have e : L * (DL_np M l' * ((if p.1 then Mᴴ else M) * Ea D N p.2)) * Ea D N b =
        L * (DL_np M l' * ((if p.1 then Mᴴ else M) * (Ea D N p.2 * Ea D N b))) := by
      simp only [Matrix.mul_assoc]
    rw [e, DL_Ea_mul]
    by_cases h : p.2 = b
    · simp only [h, ↓reduceIte, one_smul]
    · simp [h]

/-- A block projection letter: one term. -/
private lemma DL_step_Ea (M : Matrix (Idx D N) (Idx D N) ℂ) {n : ℕ} (b : Fin D)
    (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) (hτ : DL_tm n τ) :
    DL_nf M n 1 (DL_val M τ * Ea D N b) := by
  obtain ⟨c, L', hc, hL', e⟩ := DL_lead_Ea M hτ.2.1 τ.2.2 b
  refine ⟨[(τ.1 * c, L', τ.2.2)], le_rfl, fun τ' hτ' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hτ'
    subst hτ'
    refine ⟨?_, hL', hτ.2.2⟩
    rw [norm_mul]
    exact (mul_le_mul hτ.1 hc (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp only [DL_val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Matrix.smul_mul]
    rw [e, smul_smul]

/-- A letter `M^s`: insert `1 = Σ_a E_a`, `D` terms. -/
private lemma DL_step_M (M : Matrix (Idx D N) (Idx D N) ℂ) {n : ℕ} (s : Bool)
    (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) (hτ : DL_tm n τ) :
    DL_nf M (n + 1) D (DL_val M τ * (if s then Mᴴ else M)) := by
  refine ⟨(List.finRange D).map fun a => (τ.1, τ.2.1, τ.2.2 ++ [(s, a)]), by simp,
    fun τ' hτ' => ?_, ?_⟩
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hτ'
    refine ⟨hτ.1, hτ.2.1, ?_⟩
    simp only [List.length_append, List.length_singleton]
    have := hτ.2.2
    omega
  · rw [List.map_map, ← Fin.sum_univ_def]
    have e : ∀ a : Fin D, (DL_val M ∘ fun a => (τ.1, τ.2.1, τ.2.2 ++ [(s, a)])) a =
        τ.1 • (τ.2.1 * DL_np M τ.2.2 * (if s then Mᴴ else M) * Ea D N a) := by
      intro a
      simp only [Function.comp, DL_val, DL_np_concat, Matrix.mul_assoc]
    simp only [e]
    rw [← Finset.smul_sum, ← Finset.mul_sum, DL_sum_Ea, Matrix.mul_one, DL_val, Matrix.smul_mul]

/-- One letter: at most `D` terms, one more factor. -/
private lemma DL_step (hD : 1 ≤ D) {M B : Matrix (Idx D N) (Idx D N) ℂ} (hB : DL_good M B) {n : ℕ}
    (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) (hτ : DL_tm n τ) :
    DL_nf M (n + 1) D (DL_val M τ * B) := by
  rcases hB with ⟨c, hc, rfl⟩ | ⟨a, rfl⟩ | ⟨s, rfl⟩
  · exact DL_nf_mono (Nat.le_succ n) hD (DL_step_scalar M c hc τ hτ)
  · exact DL_nf_mono (Nat.le_succ n) hD (DL_step_Ea M a τ hτ)
  · exact DL_step_M M s τ hτ

/-- A product of `n` letters is a sum of at most `D^n` terms with at most `n` factors. -/
private lemma DL_nf_word (hD : 1 ≤ D) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    ∀ Ls : List (Matrix (Idx D N) (Idx D N) ℂ), (∀ X ∈ Ls, DL_good M X) →
      ∀ (n K : ℕ) (Y : Matrix (Idx D N) (Idx D N) ℂ), DL_nf M n K Y →
        DL_nf M (n + Ls.length) (K * D ^ Ls.length) (Y * Ls.prod) := by
  intro Ls
  induction Ls with
  | nil => intro _ n K Y h; simpa using h
  | cons X Ls ih =>
    intro hg n K Y h
    have h1 := DL_nf_mul (fun τ hτ => DL_step hD (hg X List.mem_cons_self) τ hτ) h
    have h2 := ih (fun X' hX' => hg X' (List.mem_cons_of_mem _ hX')) _ _ _ h1
    rw [List.prod_cons, ← Matrix.mul_assoc, List.length_cons]
    refine DL_nf_mono (by omega) (le_of_eq ?_) h2
    ring

/-- The trace of one term against `Λ`: at most `D B`. -/
private lemma DL_term_bound (hD : 1 ≤ D) {M Λ : Matrix (Idx D N) (Idx D N) ℂ} {n : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (H : ∀ l : List (Bool × Fin D), l.length ≤ n → ∀ b, ‖ntr (DL_np M l * Λ * Ea D N b)‖ ≤ B)
    (τ : ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)) (hτ : DL_tm n τ) :
    ‖ntr (DL_val M τ * Λ)‖ ≤ D * B := by
  obtain ⟨hc, hL, hl⟩ := hτ
  rw [DL_val, Matrix.smul_mul, DL_ntr_smul, norm_mul]
  have hDB : B ≤ D * B := le_mul_of_one_le_left hB (by exact_mod_cast hD)
  have hin : ‖ntr (τ.2.1 * DL_np M τ.2.2 * Λ)‖ ≤ D * B := by
    rcases hL with h | ⟨a, h⟩
    · rw [h, Matrix.one_mul, ← Matrix.mul_one (DL_np M τ.2.2 * Λ), ← DL_sum_Ea, Finset.mul_sum,
        DL_ntr_sum]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b : Fin D, ‖ntr (DL_np M τ.2.2 * Λ * Ea D N b)‖ ≤ ∑ _b : Fin D, B :=
            Finset.sum_le_sum fun b _ => H _ hl b
        _ = D * B := by simp
    · rw [h, Matrix.mul_assoc, DL_ntr_comm]
      exact (H _ hl a).trans hDB
  calc ‖τ.1‖ * ‖ntr (τ.2.1 * DL_np M τ.2.2 * Λ)‖ ≤ 1 * (D * B) :=
        mul_le_mul hc hin (norm_nonneg _) zero_le_one
    _ = D * B := one_mul _

/-- The normal form against `Λ`: `|⟨(Π letters) Λ⟩| ≤ D^n · D B` when every term of (A.7)
[add_one_more_Lambda] with at most `n` factors is at most `B`. -/
private lemma DL_core (hD : 1 ≤ D) (M Λ : Matrix (Idx D N) (Idx D N) ℂ) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (H : ∀ l : List (Bool × Fin D), l.length ≤ n → ∀ b, ‖ntr (DL_np M l * Λ * Ea D N b)‖ ≤ B)
    (Ls : List (Matrix (Idx D N) (Idx D N) ℂ)) (hg : ∀ X ∈ Ls, DL_good M X)
    (hn : Ls.length ≤ n) :
    ‖ntr (Ls.prod * Λ)‖ ≤ D ^ n * (D * B) := by
  have h0 := DL_nf_word hD M Ls hg 0 1 1 (DL_nf_one M)
  rw [Matrix.one_mul, zero_add, one_mul] at h0
  obtain ⟨T, hl, hT, e⟩ := DL_nf_mono hn (Nat.pow_le_pow_right hD hn) h0
  rw [e]
  have key : ∀ T : List (ℂ × Matrix (Idx D N) (Idx D N) ℂ × List (Bool × Fin D)),
      (∀ τ ∈ T, DL_tm n τ) → ‖ntr ((T.map (DL_val M)).sum * Λ)‖ ≤ T.length * (D * B) := by
    intro T
    induction T with
    | nil => intro _; simp [ntr]
    | cons τ T ih =>
      intro hT
      rw [List.map_cons, List.sum_cons, Matrix.add_mul, DL_ntr_add, List.length_cons]
      refine (norm_add_le _ _).trans ?_
      have h1 := DL_term_bound hD hB H τ (hT τ List.mem_cons_self)
      have h2 := ih fun τ' hτ' => hT τ' (List.mem_cons_of_mem _ hτ')
      push_cast
      linarith
  have hDB : 0 ≤ (D : ℝ) * B := by positivity
  refine (key T hT).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hDB

/-- `‖Π letters‖ ≤ R^n` when every letter has norm at most `R ≥ 1`. -/
private lemma DL_prod_op (Ls : List (Matrix (Idx D N) (Idx D N) ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (h : ∀ X ∈ Ls, opNorm X ≤ R) : opNorm Ls.prod ≤ R ^ Ls.length := by
  induction Ls with
  | nil =>
    rw [List.prod_nil, List.length_nil, pow_zero]
    exact DL_op_one
  | cons X Ls ih =>
    rw [List.prod_cons, List.length_cons, pow_succ']
    refine (DL_op_mul _ _).trans ?_
    exact mul_le_mul (h X List.mem_cons_self)
      (ih fun X' hX' => h X' (List.mem_cons_of_mem _ hX')) (DL_op_nonneg _) (by linarith)

/-- A letter has norm at most `5/4` when `‖M‖ ≤ 5/4`. -/
private lemma DL_good_op {M X : Matrix (Idx D N) (Idx D N) ℂ} (hM : opNorm M ≤ 5 / 4)
    (h : DL_good M X) : opNorm X ≤ 5 / 4 := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨a, rfl⟩ | ⟨s, rfl⟩
  · rw [DL_op_smul]
    calc ‖c‖ * opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 * 1 :=
          mul_le_mul hc DL_op_one (DL_op_nonneg _) zero_le_one
      _ ≤ 5 / 4 := by norm_num
  · exact (DL_op_Ea a).trans (by norm_num)
  · cases s
    · exact hM
    · simpa [DL_op_conj] using hM

end Normal

/-! ## Words and slots -/

section Words

variable {D N : ℕ}

private lemma DL_lwm_append (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : List LoopLetter) :
    loopWordMat G M E L (u ++ v) = loopWordMat G M E L u * loopWordMat G M E L v := by
  simp [loopWordMat, List.map_append, List.prod_append]

/-- With `Λ̃` cycled to the end: `⟨u Λ̃ v⟩ = ⟨v u Λ̃⟩`. -/
private lemma DL_lwm_split (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : List LoopLetter) (o : Fin 2) :
    ntr (loopWordMat G M E L (u ++ .lamt o :: v)) = ntr (loopWordMat G M E L (v ++ u) * L) := by
  have e : loopWordMat G M E L (u ++ .lamt o :: v) =
      loopWordMat G M E L u * (L * loopWordMat G M E L v) := by
    rw [DL_lwm_append]
    congr 1
  rw [e, DL_lwm_append, DL_ntr_comm, Matrix.mul_assoc, DL_ntr_comm, Matrix.mul_assoc]

/-- The loop is invariant under rotation of its word. -/
private lemma DL_lwm_rotate (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (w : List LoopLetter) (r : ℕ) :
    ntr (loopWordMat G M E L (w.rotate r)) = ntr (loopWordMat G M E L w) := by
  rw [List.rotate_eq_drop_append_take_mod]
  conv_rhs => rw [← List.take_append_drop (r % w.length) w]
  rw [DL_lwm_append, DL_lwm_append, DL_ntr_comm]

/-- A word without resolvent and without `Λ̃` is a product of letters `𝔐_a` and `E_x`. -/
private lemma DL_word_good (G Mm : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L M₀ : Matrix (Idx D N) (Idx D N) ℂ)
    (hM : ∀ a, DL_good M₀ (Mm a)) (hE : ∀ y, DL_good M₀ (E y)) :
    ∀ w : List LoopLetter, (∀ x ∈ w, (∀ a, x ≠ .res a) ∧ ∀ o, x ≠ .lamt o) →
      ∃ Ls : List (Matrix (Idx D N) (Idx D N) ℂ), loopWordMat G Mm E L w = Ls.prod ∧
        Ls.length = w.length ∧ ∀ X ∈ Ls, DL_good M₀ X := by
  intro w
  induction w with
  | nil => exact fun _ => ⟨[], rfl, rfl, by simp⟩
  | cons x w ih =>
    intro hw
    obtain ⟨Ls, e, hl, hg⟩ := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx := hw x List.mem_cons_self
    have e' : loopWordMat G Mm E L (x :: w) =
        loopWordMat G Mm E L [x] * loopWordMat G Mm E L w := by
      rw [← DL_lwm_append]
      simp
    have hx' : DL_good M₀ (loopWordMat G Mm E L [x]) := by
      cases x with
      | res a => exact absurd rfl (hx.1 a)
      | det a => simpa [loopWordMat] using hM a
      | proj y => simpa [loopWordMat] using hE y
      | lamt o => exact absurd rfl (hx.2 o)
    refine ⟨loopWordMat G Mm E L [x] :: Ls, by rw [e', e, List.prod_cons], by simp [hl], ?_⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | h
    · exact hx'
    · exact hg X h

/-- The shape of a gain loop: some rotation of the word is `𝔐_a Λ̃ 𝔐_b E_x` with `a ≠ b`. -/
private lemma DL_gain_shape (w : List LoopLetter) (h : pkgGainLoop (w.map PkgLetter.lw) = true) :
    ∃ (r : ℕ) (a : Fin 2) (o : Fin 2) (b : Fin 2) (x : ℕ),
      w.rotate r = [.det a, .lamt o, .det b, .proj x] ∧ a ≠ b := by
  unfold pkgGainLoop at h
  rw [List.any_eq_true] at h
  obtain ⟨r, -, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.map_rotate] at hr
  generalize w.rotate r = w' at hr ⊢
  split at hr
  · rename_i a o b x heq
    have h' : w'.map PkgLetter.lw =
        [LoopLetter.det a, .lamt o, .det b, .proj x].map PkgLetter.lw := heq
    have hinj : Function.Injective PkgLetter.lw := fun _ _ h => PkgLetter.lw.inj h
    exact ⟨a, o, b, x, List.map_injective_iff.2 hinj h', by simpa using hr⟩
  · exact absurd hr (by simp)

/-- `|m_sc(z)| ≤ 1` for `Im z > 0`. -/
private lemma DL_msc_le (z : ℂ) (hz : 0 < z.im) : ‖msc z‖ ≤ 1 := by
  have h1 : msc z = mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z := by simp [msc, mExt, hz]
  have h0 : opNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 1 / 10 := by simp [opNorm]
  rw [h1]
  exact (mSol_apriori _ Matrix.isHermitian_zero h0 z hz).2.1.le

/-- `M(0, z) = m_sc(z) · 1` for `Im z > 0` ((A.5) [eq:msc] with `Λ = 0`). -/
private lemma DL_MExt_zero (hD : 0 < D) (hN : 0 < N) (z : ℂ) (hz : 0 < z.im) :
    MExt (0 : Matrix (Idx D N) (Idx D N) ℂ) z = msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨C, hC, hCs⟩ := eq_msc_traceless (‖z‖ + 1)⁻¹ (by positivity)
  have h := hCs (Idx D N) 0 Matrix.isHermitian_zero (by simp [opNorm]) (by simp [ntr]) z
    (by rw [inv_inv]; linarith) hz
  have h0 : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by simp [opNorm]
  rw [h0, mul_zero] at h
  have h1 : 0 ≤ ‖mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z - msc z‖ := norm_nonneg _
  have h3 : MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z =
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    ext i j
    have := DL_entry_le (MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z -
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) i j
    have h4 : ‖(MSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z -
      msc z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) i j‖ = 0 :=
      le_antisymm (this.trans (by linarith)) (norm_nonneg _)
    rw [norm_eq_zero] at h4
    exact sub_eq_zero.1 h4
  have h5 : mExt (0 : Matrix (Idx D N) (Idx D N) ℂ) z =
      mSol (0 : Matrix (Idx D N) (Idx D N) ℂ) z := by simp [mExt, hz]
  rw [← h3]
  simp [MExt, MSol, h5]

/-- A slot with `c_a = 0` is the scalar letter `m_sc(z) · 1`, or its conjugate under the flag. -/
private lemma DL_slot_zero (hD : 0 < D) (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (M₀ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (hz : 0 < z.im) (s : Bool) :
    DL_good M₀ (MExt ((((0 : ℝ) : ℂ)) • lam D N A) (if s then star z else z)) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have h1 := DL_MExt_zero hD hN z hz
  left
  cases s
  · exact ⟨msc z, DL_msc_le z hz, by simpa using h1⟩
  · refine ⟨star (msc z), by rw [norm_star]; exact DL_msc_le z hz, ?_⟩
    have h2 := (mExt_conj (0 : Matrix (Idx D N) (Idx D N) ℂ) Matrix.isHermitian_zero z hz.ne').2
    simp only [Complex.ofReal_zero, zero_smul, ite_true]
    rw [h2, h1, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- A slot with Hermitian deformation `Λ'` and `Im z > 0` is the letter `M` or `M^*`, with
`M = M(Λ', z)`. -/
private lemma DL_slot_flag [Nonempty (Idx D N)] (Λ' : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ'.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : Bool) :
    DL_good (MSol Λ' z) (MExt Λ' (if s then star z else z)) := by
  have e : MExt Λ' z = MSol Λ' z := by
    have : mExt Λ' z = mSol Λ' z := by simp [mExt, hz]
    simp [MExt, MSol, this]
  right; right
  refine ⟨s, ?_⟩
  cases s
  · simpa using e
  · simp only [ite_true]
    rw [(mExt_conj Λ' hΛ z hz.ne').2, e]

/-- The letter `E_x`: a block projection, or `1` for an unbound index. -/
private lemma DL_E_good (e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D)
    (M₀ : Matrix (Idx D N) (Idx D N) ℂ) (y : ℕ) : DL_good M₀ (e.E ι y) := by
  unfold LoopEnv.E
  split
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inl ⟨1, by simp, by simp⟩

/-- (A.7) [add_one_more_Lambda] in the form of `DL_np`. -/
private lemma DL_A7 {τ : ℝ} {n : ℕ} {C : ℝ}
    (hC : ∀ (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ), 1 ≤ N →
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → (∀ a : Fin D, ntr (Ea D N a * Λ) = 0) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      ∀ (s : Fin n → Bool) (a : Fin n → Fin D) (b : Fin D),
        ‖ntr ((List.ofFn fun i : Fin n =>
            (if s i then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i)).prod * Λ * Ea D N b)‖ ≤
          C * avgSq Λ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hN : 1 ≤ N) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (htr : ∀ a : Fin D, ntr (Ea D N a * Λ) = 0) (z : ℂ)
    (hzn : ‖z‖ ≤ τ⁻¹) (hz : 0 < z.im) (l : List (Bool × Fin D)) (hl : l.length = n)
    (b : Fin D) : ‖ntr (DL_np (MSol Λ z) l * Λ * Ea D N b)‖ ≤ C * avgSq Λ := by
  subst hl
  rw [DL_np_ofFn]
  exact hC D N Λ hN hΛ hℓ htr z hzn hz (fun i => (l.get i).1) (fun i => (l.get i).2) b

end Words

/-- (A.7) [add_one_more_Lambda] with (5.5) [regular_estimate_localized_eigenvector] and (5.22)
[regular_estimate_localized_eigenvalue] at the slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law]: a loop
with one `Λ̃` and no resolvent is `O(⟨Λ²⟩)`, and `O(Im m ⟨Λ²⟩)` when it is `⟨𝔐_a Λ̃ 𝔐_b E_x⟩`
with `a ≠ b`, every flag, `Im m` of slot `1`. -/
theorem pkg_lam0_bound (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (w : List LoopLetter)
    (hw1 : w.countP (fun x => match x with | .lamt _ => true | _ => false) = 1)
    (hw0 : w.countP (fun x => match x with | .res _ => true | _ => false) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
      ∀ (nb : ℕ) (ι : Fin nb → Fin D) (h : Idx D N → Idx D N → ℂ),
        ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤
          K * ((if pkgGainLoop (w.map PkgLetter.lw) then
            (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im else 1) * avgSq (lam D N e.A)) := by
  obtain ⟨c₀, K₁, -, hK₁, N₁, hadm⟩ := loop_env_admissible D hD δA εA ε hδA hεA hε hε' hε''
  obtain ⟨K₂, hK₂, N₂, hgain⟩ := loop_env_gain D hD δA εA ε hδA hεA hε hε'
  have hτ : 0 < ε / 2 := by positivity
  choose C hC0 hC using fun n : ℕ => add_one_more_Lambda (ε / 2) hτ n
  set n := w.length with hn
  set Cm := ∑ j ∈ Finset.range (n + 1), C j with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun j _ => (hC0 j).le
  have hCj : ∀ j ≤ n, C j ≤ Cm := fun j hj => Finset.single_le_sum (f := C)
    (fun j _ => (hC0 j).le) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  set K₃ := (D : ℝ) ^ n * (D * Cm) + K₁ * (5 / 4) ^ n with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  refine ⟨D * K₂ + K₃ + 1, by positivity, max (max N₁ N₂) 1, ?_⟩
  intro N hN A hA k hk hkN hhs e he nb ι h
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN₁ : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN₂ : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hD0 : 0 < D := by omega
  have hD1 : 1 ≤ D := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, hD0⟩, ⟨0, hN1⟩)⟩
  obtain ⟨hA2, -, hz, hδ⟩ := hadm N hN₁ A hA k hk hkN hhs e he
  have hP : 0 ≤ avgSq (lam D N e.A) := DL_avgSq_nonneg (lam_isHermitian _ _ _)
  have hΛ1 : opNorm (lam D N e.A) ≤ 1 / 10 := (opNorm_lam_le D N e.A).trans hA2
  -- the letters of the slots and the terms of (A.7)
  have hcase : ∃ (M₀ : Matrix (Idx D N) (Idx D N) ℂ) (B : ℝ), 0 ≤ B ∧ B ≤ Cm * avgSq (lam D N e.A) ∧
      opNorm M₀ ≤ 5 / 4 ∧ (∀ a, DL_good M₀ (e.M a)) ∧
      ∀ l : List (Bool × Fin D), l.length ≤ n → ∀ b,
        ‖ntr (DL_np M₀ l * lam D N e.A * Ea D N b)‖ ≤ B := by
    rcases he with ⟨s, rfl⟩ | ⟨t, ht, s, rfl⟩
    · -- the slots of Lemma 5.2: `𝔐₀ = m_sc(z₀) · 1`, `𝔐₁ = M(z₁)`
      set Λ := lam D N A with hΛ
      set z₁ := zOne Λ k ε with hz₁
      have hz1 : (evecEnv D N A k ε s).z 1 = z₁ := rfl
      have hz1pos : 0 < z₁.im := hz1 ▸ (hz 1).2.1
      have hz1n : ‖z₁‖ ≤ (ε / 2)⁻¹ := hz1 ▸ (hz 1).1.1
      have hΛh : Λ.IsHermitian := lam_isHermitian D N A
      have hΛ1' : opNorm Λ ≤ 1 / 10 := hΛ1
      have hMop : opNorm (MSol Λ z₁) ≤ 5 / 4 := by
        have h1 := (mSol_apriori Λ hΛh hΛ1' z₁ hz1pos).2.2
        have h2 : (1 - 2 * opNorm Λ)⁻¹ ≤ 5 / 4 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        linarith
      refine ⟨MSol Λ z₁, Cm * avgSq Λ, mul_nonneg hCm0 hP, le_rfl, hMop, ?_, ?_⟩
      · intro a
        fin_cases a
        · have h0 : 0 < ((evecEnv D N A k ε s).z 0).im := (hz 0).2.1
          exact DL_slot_zero hD0 hN1 A _ _ h0 (s 0)
        · have e1 : (evecEnv D N A k ε s).M 1 = MExt Λ (if s 1 then star z₁ else z₁) := by
            change MExt (((1 : ℝ) : ℂ) • lam D N A) _ = _
            rw [Complex.ofReal_one, one_smul]
            rfl
          simp only [Fin.mk_one, Fin.isValue]
          rw [e1]
          exact DL_slot_flag Λ hΛh z₁ hz1pos (s 1)
      · intro l hl b
        refine (DL_A7 (hC l.length) Λ hN1 hΛh hΛ1' (DL_lam_block A) z₁ hz1n hz1pos l rfl b).trans ?_
        exact mul_le_mul_of_nonneg_right (hCj _ hl) hP
    · -- the slots of Lemma 5.4: `𝔐₀ = 𝔐₁ = M_t(z_t)` at `tΛ`
      set Λ := lam D N A with hΛ
      set zt := zOne ((t : ℂ) • Λ) k ε with hzt
      have hz0 : (evalEnv D N A k ε t s).z 0 = zt := rfl
      have hztpos : 0 < zt.im := hz0 ▸ (hz 0).2.1
      have hztn : ‖zt‖ ≤ (ε / 2)⁻¹ := hz0 ▸ (hz 0).1.1
      have hΛh : Λ.IsHermitian := lam_isHermitian D N A
      have hΛ1' : opNorm Λ ≤ 1 / 10 := hΛ1
      have hM : ∀ a, (evalEnv D N A k ε t s).M a =
          MExt (((t : ℝ) : ℂ) • Λ) (if s a then star zt else zt) := by
        intro a
        fin_cases a <;> rfl
      rcases eq_or_lt_of_le ht.1 with h0 | htpos
      · -- `t = 0`: both slots are scalar letters
        refine ⟨0, 0, le_rfl, mul_nonneg hCm0 hP, by norm_num [opNorm], ?_, ?_⟩
        · intro a
          rw [hM a, ← h0]
          exact DL_slot_zero hD0 hN1 A 0 _ hztpos (s a)
        · intro l _ b
          rcases l with _ | ⟨p, l⟩
          · rw [DL_np_nil, Matrix.one_mul, DL_ntr_comm, DL_lam_block]
            simp
          · have : DL_np (0 : Matrix (Idx D N) (Idx D N) ℂ) (p :: l) = 0 := by
              simp [DL_np]
            rw [this]
            simp [ntr]
      · -- `t > 0`: (A.7) at `tΛ`
        set Λ' := ((t : ℝ) : ℂ) • Λ with hΛ'
        have hΛ'h : Λ'.IsHermitian := by
          rw [hΛ', Matrix.IsHermitian, Matrix.conjTranspose_smul, hΛh.eq]
          simp
        have hΛ'n : opNorm Λ' = t * opNorm Λ := by
          rw [hΛ', DL_op_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
        have hΛ'1 : opNorm Λ' ≤ 1 / 10 := by
          rw [hΛ'n]
          nlinarith [DL_op_nonneg Λ, ht.2]
        have hΛ'tr : ∀ a : Fin D, ntr (Ea D N a * Λ') = 0 := by
          intro a
          rw [hΛ', Matrix.mul_smul, DL_ntr_smul, DL_lam_block, mul_zero]
        have hav : avgSq Λ' = t ^ 2 * avgSq Λ := by
          unfold avgSq
          rw [hΛ', Matrix.smul_mul, Matrix.mul_smul, smul_smul, DL_ntr_smul,
            show ((t : ℂ) * (t : ℂ)) = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
        have hMop : opNorm (MSol Λ' zt) ≤ 5 / 4 := by
          have h1 := (mSol_apriori Λ' hΛ'h hΛ'1 zt hztpos).2.2
          have h2 : (1 - 2 * opNorm Λ')⁻¹ ≤ 5 / 4 := by
            rw [inv_le_comm₀ (by linarith) (by norm_num)]
            linarith
          linarith
        refine ⟨MSol Λ' zt, Cm * avgSq Λ, mul_nonneg hCm0 hP, le_rfl, hMop, ?_, ?_⟩
        · intro a
          rw [hM a]
          exact DL_slot_flag Λ' hΛ'h zt hztpos (s a)
        · intro l hl b
          have h1 := DL_A7 (hC l.length) Λ' hN1 hΛ'h hΛ'1 hΛ'tr zt hztn hztpos l rfl b
          have e1 : ntr (DL_np (MSol Λ' zt) l * Λ' * Ea D N b) =
              (t : ℂ) * ntr (DL_np (MSol Λ' zt) l * Λ * Ea D N b) := by
            rw [hΛ', Matrix.mul_smul, Matrix.smul_mul, DL_ntr_smul]
          rw [e1, hav, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos] at h1
          have h2 : ‖ntr (DL_np (MSol Λ' zt) l * Λ * Ea D N b)‖ ≤ C l.length * t * avgSq Λ := by
            have h3 : t * ‖ntr (DL_np (MSol Λ' zt) l * Λ * Ea D N b)‖ ≤
                t * (C l.length * t * avgSq Λ) := by
              linarith
            exact le_of_mul_le_mul_left h3 htpos
          refine h2.trans ?_
          have h4 : C l.length * t * avgSq Λ ≤ C l.length * avgSq Λ := by
            have hPΛ : 0 ≤ avgSq Λ := hP
            have := mul_nonneg (mul_nonneg (hC0 l.length).le hPΛ) (sub_nonneg.2 ht.2)
            nlinarith
          exact h4.trans (mul_le_mul_of_nonneg_right (hCj _ hl) hP)
  obtain ⟨M₀, B, hB0, hBle, hMop, hMg, hH⟩ := hcase
  -- the bound without the gain
  have hgen : ‖ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)‖ ≤ K₃ * avgSq (lam D N e.A) := by
    obtain ⟨x, hx, hxl⟩ := List.countP_pos_iff.1 (Nat.lt_of_lt_of_eq Nat.one_pos hw1.symm)
    obtain ⟨o, rfl⟩ : ∃ o, x = .lamt o := by
      cases x with
      | lamt o => exact ⟨o, rfl⟩
      | _ => simp at hxl
    obtain ⟨u, v, rfl⟩ := List.append_of_mem hx
    have hc1 : (u ++ LoopLetter.lamt o :: v).countP
        (fun x => match x with | .lamt _ => true | _ => false) = 1 := hw1
    rw [List.countP_append, List.countP_cons] at hc1
    simp only [ite_true] at hc1
    have hu0 : u.countP (fun x => match x with | .lamt _ => true | _ => false) = 0 := by omega
    have hv0 : v.countP (fun x => match x with | .lamt _ => true | _ => false) = 0 := by omega
    have hr : (u ++ LoopLetter.lamt o :: v).countP
        (fun x => match x with | .res _ => true | _ => false) = 0 := hw0
    rw [List.countP_append, List.countP_cons] at hr
    have hur : u.countP (fun x => match x with | .res _ => true | _ => false) = 0 := by omega
    have hvr : v.countP (fun x => match x with | .res _ => true | _ => false) = 0 := by omega
    have hfree : ∀ y ∈ v ++ u, (∀ a, y ≠ .res a) ∧ ∀ o, y ≠ .lamt o := by
      intro y hy
      have hy' : y ∈ u ∨ y ∈ v := by
        rcases List.mem_append.1 hy with h | h
        · exact Or.inr h
        · exact Or.inl h
      constructor
      · rintro a rfl
        rcases hy' with h | h
        · exact absurd rfl (List.countP_eq_zero.1 hur _ h)
        · exact absurd rfl (List.countP_eq_zero.1 hvr _ h)
      · rintro o' rfl
        rcases hy' with h | h
        · exact absurd rfl (List.countP_eq_zero.1 hu0 _ h)
        · exact absurd rfl (List.countP_eq_zero.1 hv0 _ h)
    obtain ⟨Ls, eL, hlen, hLg⟩ := DL_word_good (e.G h) e.M (e.E ι) e.Lt M₀ hMg
      (DL_E_good e ι M₀) (v ++ u) hfree
    have hLn : Ls.length ≤ n := by
      rw [hlen, hn]
      simp only [List.length_append, List.length_cons]
      omega
    rw [DL_lwm_split, eL]
    have eLt : e.Lt = lam D N e.A - (e.δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) := rfl
    rw [eLt, Matrix.mul_sub, DL_ntr_sub, Matrix.mul_smul, Matrix.mul_one, DL_ntr_smul]
    refine (norm_sub_le _ _).trans ?_
    have h1 := DL_core hD1 M₀ (lam D N e.A) n B hB0 hH Ls hLg hLn
    have h2 : ‖(e.δ : ℂ) * ntr Ls.prod‖ ≤ K₁ * avgSq (lam D N e.A) * (5 / 4) ^ n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul hδ ?_ (norm_nonneg _) (by positivity)
      refine (DL_ntr_le _).trans ((DL_prod_op Ls (5 / 4) (by norm_num)
        fun X hX => DL_good_op hMop (hLg X hX)).trans ?_)
      exact pow_le_pow_right₀ (by norm_num) hLn
    have h3 : (D : ℝ) ^ n * (D * B) ≤ (D : ℝ) ^ n * (D * (Cm * avgSq (lam D N e.A))) := by
      gcongr
    calc _ ≤ (D : ℝ) ^ n * (D * B) + K₁ * avgSq (lam D N e.A) * (5 / 4) ^ n := add_le_add h1 h2
      _ ≤ (D : ℝ) ^ n * (D * (Cm * avgSq (lam D N e.A))) +
          K₁ * avgSq (lam D N e.A) * (5 / 4) ^ n := by linarith
      _ = K₃ * avgSq (lam D N e.A) := by rw [hK₃]; ring
  split_ifs with hg
  · -- the gain: `⟨𝔐_a Λ̃ 𝔐_b E_x⟩` with `a ≠ b`
    obtain ⟨r, a, o, b, x, hr, hab⟩ := DL_gain_shape w hg
    rw [← DL_lwm_rotate _ _ _ _ w r, hr]
    have e1 : loopWordMat (e.G h) e.M (e.E ι) e.Lt [.det a, .lamt o, .det b, .proj x] =
        e.M a * e.Lt * e.M b * e.E ι x := by
      simp [loopWordMat, Matrix.mul_assoc]
    rw [e1]
    have hg' := fun c => hgain N hN₂ A hA k hk hkN hhs e he a b c hab
    set Q := (mSol ((e.c 1 : ℂ) • lam D N e.A) (e.z 1)).im * avgSq (lam D N e.A) with hQ
    have hQ0 : 0 ≤ Q := by
      have := (norm_nonneg _).trans (hg' ⟨0, hD0⟩)
      exact (mul_nonneg_iff_of_pos_left hK₂).1 this
    have hK : (D : ℝ) * K₂ ≤ D * K₂ + K₃ + 1 := by linarith
    have hDK : K₂ ≤ (D : ℝ) * K₂ := le_mul_of_one_le_left hK₂.le (by exact_mod_cast hD1)
    unfold LoopEnv.E
    split
    · exact (hg' _).trans (mul_le_mul_of_nonneg_right (hDK.trans hK) hQ0)
    · rw [Matrix.mul_one, ← Matrix.mul_one (e.M a * e.Lt * e.M b), ← DL_sum_Ea, Finset.mul_sum,
        DL_ntr_sum]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c : Fin D, ‖ntr (e.M a * e.Lt * e.M b * Ea D N c)‖ ≤ ∑ _c : Fin D, K₂ * Q :=
            Finset.sum_le_sum fun c _ => hg' c
        _ = D * K₂ * Q := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hK hQ0
  · rw [one_mul]
    have : 0 ≤ (D : ℝ) * K₂ := by positivity
    exact hgen.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  
end RBMTransitionEdge

end
