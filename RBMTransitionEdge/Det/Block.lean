module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core

@[expose] public section

/-!
# Block structure: (2.13), (2.15), translation invariance and the Fourier eigenvectors of M̂

For `Λ = lam D N A`: `S(M) = mI` and the matrix Dyson equation (2.13) [def_M]; the blocks of `M`
for `D = 2` (2.15) [eq:MD=2]; the matrices `M̂` and `K` of (3.1) [def_ML] and (3.2) [def_K]; the
translation invariance of `M̂` (Lemma A.1 [lemma_usual_properties_of_m_and_mu] (vi)) and its
Fourier eigenvectors (A.25) [eq_lambdak].
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The block projection `E_a`, `(E_a)_{ij} = 1(i = j ∈ I_a)`, of Theorem 2.1 [mix]. -/
def Ea (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Idx D N) ℂ :=
  Matrix.diagonal fun p => if p.1 = a then 1 else 0

/-- The `D × D` matrix `M̂(z₁, z₂)` of (3.1) [def_ML]: `M̂_{ab} = D ⟨M(z₁) E_a M(z₂) E_b⟩`. -/
def Mhat {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b => (D : ℂ) * ntr (MExt Λ z₁ * Ea D N a * MExt Λ z₂ * Ea D N b)

/-- `K(z₁, z₂) = [1 - M̂(z₁, z₂)]⁻¹ M̂(z₁, z₂)` of (3.2) [def_K]. -/
def Kmat {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 - Mhat Λ z₁ z₂)⁻¹ * Mhat Λ z₁ z₂

/-- The Fourier vector `u_l(a) = D^{-1/2} e^{2πi l a / D}` of the proof of (A.11) [flat_M],
indexed from `0`. -/
def fourierVec (D : ℕ) (l : Fin D) : Fin D → ℂ :=
  fun a => ((Real.sqrt D)⁻¹ : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (((l : ℕ) * (a : ℕ) : ℕ) : ℂ) / D)

/-- `λ̂_l = u_l^* B u_l`; for a translation invariant `B` this is the eigenvalue
`Σ_b B_{1b} e^{2πi(l-1)(b-1)/D}` of (A.25) [eq_lambdak], indexed from `0`. -/
def circEig {D : ℕ} (B : Matrix (Fin D) (Fin D) ℂ) (l : Fin D) : ℂ :=
  ∑ a : Fin D, ∑ b : Fin D, star (fourierVec D l a) * B a b * fourierVec D l b

/-- The normalized trace of the conjugate transpose is the conjugate of the normalized trace. -/
private lemma Block_ntr_conjTranspose {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) :
    ntr Bᴴ = star (ntr B) := by
  simp [ntr, Matrix.trace_conjTranspose]

/-- For Hermitian `Λ` and `Im z ≠ 0`: `Im (z + m) ≠ 0`, `m = ⟨M⟩`, and `M` is the inverse of `Λ - z - m` ((2.16) [self_m], (2.17) [def_G0]). -/
private lemma Block_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (z + mExt Λ z).im ≠ 0 ∧ mExt Λ z = ntr (MExt Λ z) ∧
      (Λ - (z + mExt Λ z) • (1 : Matrix ι ι ℂ)) * MExt Λ z = 1 := by
  rcases lt_or_gt_of_ne hz with h | h
  · have h' : 0 < (star z).im := by simpa using h
    obtain ⟨h1, h2, h3⟩ := mSol_spec Λ hΛ (star z) h'
    obtain ⟨e1, e2⟩ := mExt_conj Λ hΛ (star z) h'.ne'
    rw [star_star] at e1 e2
    have hm : mExt Λ (star z) = mSol Λ (star z) := by simp only [mExt, h', ↓reduceIte]
    have hM : MExt Λ (star z) = MSol Λ (star z) := by rw [MExt, MSol, hm]
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, hm]
      have : (z + star (mSol Λ (star z))).im = z.im - (mSol Λ (star z)).im := by simp; ring
      rw [this]; linarith
    · rw [e1, hm, e2, hM, Block_ntr_conjTranspose, ← h2]
    · have hw : z + mExt Λ z = star (star z + mSol Λ (star z)) := by
        rw [e1, hm]; simp
      rw [hw, e2, hM]
      have h4 := congrArg Matrix.conjTranspose h3
      rw [conjTranspose_mul, conjTranspose_one, conjTranspose_sub, conjTranspose_smul,
        conjTranspose_one, hΛ.eq] at h4
      exact mul_eq_one_comm.mp h4
  · have hm : mExt Λ z = mSol Λ z := by simp only [mExt, h, ↓reduceIte]
    have hM : MExt Λ z = MSol Λ z := by rw [MExt, MSol, hm]
    obtain ⟨h1, h2, h3⟩ := mSol_spec Λ hΛ z h
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]; simp; linarith
    · rw [hm, hM]; exact h2
    · rw [hm, hM]; exact h3


/-- `M̂_{ab}` of (3.1) [def_ML] as `N⁻¹ Σ_{i,j} M(z₁)_{(b,j),(a,i)} M(z₂)_{(a,i),(b,j)}`. -/
private lemma Block_Mhat_apply (D N : ℕ) (hD : D ≠ 0) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z₁ z₂ : ℂ) (a b : Fin D) :
    Mhat Λ z₁ z₂ a b = (N : ℂ)⁻¹ *
      ∑ i : Fin N, ∑ j : Fin N, MExt Λ z₁ (b, j) (a, i) * MExt Λ z₂ (a, i) (b, j) := by
  have h1 : (D : ℂ) * ((Fintype.card (Idx D N) : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
    field_simp
  have h2 : (MExt Λ z₁ * Ea D N a * MExt Λ z₂ * Ea D N b).trace =
      ∑ i : Fin N, ∑ j : Fin N, MExt Λ z₁ (b, j) (a, i) * MExt Λ z₂ (a, i) (b, j) := by
    simp only [Matrix.trace, Matrix.diag, Ea, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal_apply]
    simp [ite_and]
    exact Finset.sum_comm
  unfold Mhat ntr
  rw [← mul_assoc, h1, h2]


/-- `D ⟨M E_a⟩ = N⁻¹ Σ_i M_{(a,i),(a,i)}`. -/
private lemma Block_diag_apply (D N : ℕ) (hD : D ≠ 0) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (a : Fin D) :
    (D : ℂ) * ntr (MExt Λ z * Ea D N a) = (N : ℂ)⁻¹ * ∑ i : Fin N, MExt Λ z (a, i) (a, i) := by
  have h1 : (D : ℂ) * ((Fintype.card (Idx D N) : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
    field_simp
  have h2 : (MExt Λ z * Ea D N a).trace = ∑ i : Fin N, MExt Λ z (a, i) (a, i) := by
    simp only [Matrix.trace, Matrix.diag, Ea, Matrix.mul_diagonal, Fintype.sum_prod_type]
    simp
  unfold ntr
  rw [← mul_assoc, h1, h2]

/-- The normalized trace over `Idx D N` as a double sum over the diagonal entries. -/
private lemma Block_ntr_apply (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr Λ = ((D : ℂ) * N)⁻¹ * ∑ a : Fin D, ∑ i : Fin N, Λ (a, i) (a, i) := by
  simp [ntr, Matrix.trace, Fintype.sum_prod_type]

open Fin.NatCast Fin.CommRing in
/-- A function on `Fin D` invariant under `a ↦ a + 1` is constant. -/
private lemma Block_iter1 {D : ℕ} [NeZero D] {α : Type*} (f : Fin D → α)
    (h : ∀ a, f (a + 1) = f a) (a b : Fin D) : f a = f b := by
  have key : ∀ n : ℕ, f (b + (n : Fin D)) = f b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, h, ih]
  have := key (a - b).val
  rwa [Fin.cast_val_eq_self, add_sub_cancel] at this

open Fin.NatCast Fin.CommRing in
/-- A function on `Fin D × Fin D` invariant under `(a, b) ↦ (a + 1, b + 1)` is constant on the classes of `b - a`. -/
private lemma Block_iter2 {D : ℕ} [NeZero D] {α : Type*} (f : Fin D → Fin D → α)
    (h : ∀ a b, f (a + 1) (b + 1) = f a b) (a b a' b' : Fin D) (hab : b - a = b' - a') :
    f a b = f a' b' := by
  have key : ∀ n : ℕ, f (a + (n : Fin D)) (b + (n : Fin D)) = f a b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, ← add_assoc, h, ih]
  have h1 := key (a' - a).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h1
  have h2 : b + (a' - a) = b' := by linear_combination hab
  rw [h2] at h1
  exact h1.symm

/-- For `D ≥ 3` the neighbour relation `fwd D a b` is `b = a + 1` in `Fin D`. -/
private lemma Block_fwd_iff (D : ℕ) [NeZero D] (hD : 3 ≤ D) (a b : Fin D) :
    fwd D a b ↔ b = a + 1 := by
  rw [Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < D)]
  unfold fwd
  have ha := a.isLt
  constructor
  · rintro (h | ⟨-, h1, h2⟩)
    · rw [h, Nat.mod_eq_of_lt (by omega)]
    · rw [h2, h1, Nat.mod_self]
  · intro h
    by_cases hc : (a : ℕ) + 1 < D
    · left; rw [h, Nat.mod_eq_of_lt hc]
    · right
      have : (a : ℕ) + 1 = D := by omega
      refine ⟨hD, this, ?_⟩
      rw [h, this, Nat.mod_self]


/-- The interaction `lam D N A` is Hermitian, for every `A`. -/
private lemma Block_lam_herm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (lam D N A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [lam, star_add]
  split_ifs <;> simp [add_comm]

/-- For `D ≥ 3` the block shift `(a, i) ↦ (a + 1, i)` commutes with `lam D N A`, hence with the inverse of `lam D N A - w`. -/
private lemma Block_shift (D N : ℕ) [NeZero D] (hD : 3 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ)
    (w : ℂ) (p q : Idx D N) :
    ((lam D N A - w • (1 : Matrix (Idx D N) (Idx D N) ℂ))⁻¹) (p.1 + 1, p.2) (q.1 + 1, q.2) =
      ((lam D N A - w • (1 : Matrix (Idx D N) (Idx D N) ℂ))⁻¹) p q := by
  let σ : Idx D N ≃ Idx D N := Equiv.prodCongr (Equiv.addRight (1 : Fin D)) (Equiv.refl (Fin N))
  have hσ : (lam D N A - w • (1 : Matrix (Idx D N) (Idx D N) ℂ)).submatrix σ σ =
      lam D N A - w • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [σ, Matrix.one_apply, lam, Block_fwd_iff D hD, Prod.ext_iff]
  have h := Matrix.inv_submatrix_equiv
    (lam D N A - w • (1 : Matrix (Idx D N) (Idx D N) ℂ)) σ σ
  rw [hσ] at h
  exact (congrFun₂ h p q).symm


/-- The four blocks of `lam 2 N A`: `[[0, A], [A^*, 0]]`. -/
private lemma Block_lam2 (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (i k : Fin N) :
    lam 2 N A (0, i) (0, k) = 0 ∧ lam 2 N A (0, i) (1, k) = A i k ∧
      lam 2 N A (1, i) (0, k) = star (A k i) ∧ lam 2 N A (1, i) (1, k) = 0 := by
  simp [lam, fwd]

/-- The four block equations of `(lam 2 N A - w) M = 1`. -/
private lemma Block_eqs (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : ℂ)
    (M : Matrix (Idx 2 N) (Idx 2 N) ℂ)
    (h : (lam 2 N A - w • (1 : Matrix (Idx 2 N) (Idx 2 N) ℂ)) * M = 1)
    (P Q R S : Matrix (Fin N) (Fin N) ℂ) (hP : ∀ i j, P i j = M (0, i) (0, j))
    (hQ : ∀ i j, Q i j = M (0, i) (1, j)) (hR : ∀ i j, R i j = M (1, i) (0, j))
    (hS : ∀ i j, S i j = M (1, i) (1, j)) :
    A * R - w • P = 1 ∧ A * S - w • Q = 0 ∧ Aᴴ * P - w • R = 0 ∧ Aᴴ * Q - w • S = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun₂ h (0, i) (0, j)
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Block_lam2, hP, hR, Prod.ext_iff] at this ⊢
    linear_combination this
  · ext i j
    have := congrFun₂ h (0, i) (1, j)
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Block_lam2, hQ, hS, Prod.ext_iff] at this ⊢
    linear_combination this
  · ext i j
    have := congrFun₂ h (1, i) (0, j)
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Block_lam2, hP, hR, Prod.ext_iff] at this ⊢
    linear_combination this
  · ext i j
    have := congrFun₂ h (1, i) (1, j)
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Block_lam2, hQ, hS, Prod.ext_iff] at this ⊢
    linear_combination this

section Alg
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Push-through identity `A (A^*A - c)⁻¹ = (AA^* - c)⁻¹ A`. -/
private lemma Block_f1 (A X Y : Matrix n n ℂ) (c : ℂ) (hxe : X = A * Aᴴ - c • 1)
    (hye : Y = Aᴴ * A - c • 1) (hX : IsUnit X.det) (hY : IsUnit Y.det) :
    A * Y⁻¹ = X⁻¹ * A := by
  have h : X * A = A * Y := by
    rw [hxe, hye]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  calc A * Y⁻¹ = (X⁻¹ * X) * A * Y⁻¹ := by rw [Matrix.nonsing_inv_mul _ hX, one_mul]
    _ = X⁻¹ * (X * A) * Y⁻¹ := by simp only [mul_assoc]
    _ = X⁻¹ * (A * Y) * Y⁻¹ := by rw [h]
    _ = X⁻¹ * A := by rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hY, mul_one]

/-- Push-through identity `A^* (AA^* - c)⁻¹ = (A^*A - c)⁻¹ A^*`. -/
private lemma Block_f2 (A X Y : Matrix n n ℂ) (c : ℂ) (hxe : X = A * Aᴴ - c • 1)
    (hye : Y = Aᴴ * A - c • 1) (hX : IsUnit X.det) (hY : IsUnit Y.det) :
    Aᴴ * X⁻¹ = Y⁻¹ * Aᴴ := by
  have h : Y * Aᴴ = Aᴴ * X := by
    rw [hxe, hye]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  calc Aᴴ * X⁻¹ = (Y⁻¹ * Y) * Aᴴ * X⁻¹ := by rw [Matrix.nonsing_inv_mul _ hY, one_mul]
    _ = Y⁻¹ * (Y * Aᴴ) * X⁻¹ := by simp only [mul_assoc]
    _ = Y⁻¹ * (Aᴴ * X) * X⁻¹ := by rw [h]
    _ = Y⁻¹ * Aᴴ := by rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hX, mul_one]

/-- `(AA^* - c)⁻¹ (AA^*) = 1 + c (AA^* - c)⁻¹`. -/
private lemma Block_f3 (A X : Matrix n n ℂ) (c : ℂ) (hxe : X = A * Aᴴ - c • 1)
    (hX : IsUnit X.det) : X⁻¹ * (A * Aᴴ) = 1 + c • X⁻¹ := by
  have h : A * Aᴴ = X + c • 1 := by rw [hxe]; abel
  rw [h, mul_add, Matrix.nonsing_inv_mul _ hX, mul_smul_comm, mul_one]

/-- `(A^*A - c)⁻¹ (A^*A) = 1 + c (A^*A - c)⁻¹`. -/
private lemma Block_f3' (A Y : Matrix n n ℂ) (c : ℂ) (hye : Y = Aᴴ * A - c • 1)
    (hY : IsUnit Y.det) : Y⁻¹ * (Aᴴ * A) = 1 + c • Y⁻¹ := by
  have h : Aᴴ * A = Y + c • 1 := by rw [hye]; abel
  rw [h, mul_add, Matrix.nonsing_inv_mul _ hY, mul_smul_comm, mul_one]

/-- For `c ≠ 0`, `tr (AA^* - c)⁻¹ = tr (A^*A - c)⁻¹`. -/
private lemma Block_f4 (A X Y : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0) (hxe : X = A * Aᴴ - c • 1)
    (hye : Y = Aᴴ * A - c • 1) (hX : IsUnit X.det) (hY : IsUnit Y.det) :
    X⁻¹.trace = Y⁻¹.trace := by
  have h1 := Block_f3 A X c hxe hX
  have h2 := Block_f3' A Y c hye hY
  have h3 : A * Y⁻¹ * Aᴴ = 1 + c • X⁻¹ := by
    rw [Block_f1 A X Y c hxe hye hX hY, mul_assoc, h1]
  have h4 := congrArg Matrix.trace h3
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm, h2] at h4
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, add_right_inj] at h4
  exact (mul_left_cancel₀ hc h4).symm

/-- `A (A^*A - c)⁻¹ A^* = 1 + c (AA^* - c)⁻¹`. -/
private lemma Block_f5a (A X Y : Matrix n n ℂ) (c : ℂ) (hxe : X = A * Aᴴ - c • 1)
    (hye : Y = Aᴴ * A - c • 1) (hX : IsUnit X.det) (hY : IsUnit Y.det) :
    A * Y⁻¹ * Aᴴ = 1 + c • X⁻¹ := by
  rw [Block_f1 A X Y c hxe hye hX hY, mul_assoc, Block_f3 A X c hxe hX]

/-- For `c₁, c₂ ≠ 0`: `tr [(AA^* - c₁)⁻¹ (AA^* - c₂)⁻¹] = tr [(A^*A - c₁)⁻¹ (A^*A - c₂)⁻¹]`. -/
private lemma Block_f5 (A X₁ Y₁ X₂ Y₂ : Matrix n n ℂ) (c₁ c₂ : ℂ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hx₁ : X₁ = A * Aᴴ - c₁ • 1) (hy₁ : Y₁ = Aᴴ * A - c₁ • 1) (hx₂ : X₂ = A * Aᴴ - c₂ • 1)
    (hy₂ : Y₂ = Aᴴ * A - c₂ • 1) (hX₁ : IsUnit X₁.det) (hY₁ : IsUnit Y₁.det)
    (hX₂ : IsUnit X₂.det) (hY₂ : IsUnit Y₂.det) :
    (X₁⁻¹ * X₂⁻¹).trace = (Y₁⁻¹ * Y₂⁻¹).trace := by
  have h1 : X₁⁻¹ * (c₂ • X₂⁻¹) = A * (Y₁⁻¹ * Y₂⁻¹ * Aᴴ) - X₁⁻¹ := by
    have h := Block_f5a A X₂ Y₂ c₂ hx₂ hy₂ hX₂ hY₂
    have h' : c₂ • X₂⁻¹ = A * Y₂⁻¹ * Aᴴ - 1 := by rw [h]; abel
    have h'' : X₁⁻¹ * (A * Y₂⁻¹ * Aᴴ) = A * (Y₁⁻¹ * Y₂⁻¹ * Aᴴ) := by
      calc X₁⁻¹ * (A * Y₂⁻¹ * Aᴴ) = (X₁⁻¹ * A) * Y₂⁻¹ * Aᴴ := by simp only [mul_assoc]
        _ = (A * Y₁⁻¹) * Y₂⁻¹ * Aᴴ := by rw [← Block_f1 A X₁ Y₁ c₁ hx₁ hy₁ hX₁ hY₁]
        _ = A * (Y₁⁻¹ * Y₂⁻¹ * Aᴴ) := by simp only [mul_assoc]
    rw [h', mul_sub, mul_one, h'']
  have h2 := congrArg Matrix.trace h1
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A, mul_smul_comm, Matrix.trace_smul] at h2
  have h3 : Y₁⁻¹ * Y₂⁻¹ * Aᴴ * A = Y₁⁻¹ * (1 + c₂ • Y₂⁻¹) := by
    rw [← Block_f3' A Y₂ c₂ hy₂ hY₂]; simp only [mul_assoc]
  rw [h3, mul_add, mul_one, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
    Block_f4 A X₁ Y₁ c₁ hc₁ hx₁ hy₁ hX₁ hY₁] at h2
  simp only [smul_eq_mul] at h2
  have h4 : c₂ * (X₁⁻¹ * X₂⁻¹).trace = c₂ * (Y₁⁻¹ * Y₂⁻¹).trace := by
    rw [h2]; ring
  exact mul_left_cancel₀ hc₂ h4


/-- Solving the four block equations of the `D = 2` Dyson equation (2.15) [eq:MD=2] with `w ≠ 0`. -/
private lemma Block_D2_core (A : Matrix n n ℂ) (w : ℂ) (hw : w ≠ 0) (P Q R S : Matrix n n ℂ)
    (e1 : A * R - w • P = 1) (e2 : A * S - w • Q = 0) (e3 : Aᴴ * P - w • R = 0)
    (e4 : Aᴴ * Q - w • S = 1) :
    IsUnit (A * Aᴴ - (w ^ 2) • (1 : Matrix n n ℂ)).det ∧
      IsUnit (Aᴴ * A - (w ^ 2) • (1 : Matrix n n ℂ)).det ∧
      P = w • (A * Aᴴ - (w ^ 2) • (1 : Matrix n n ℂ))⁻¹ ∧
      S = w • (Aᴴ * A - (w ^ 2) • (1 : Matrix n n ℂ))⁻¹ ∧
      Q = (A * Aᴴ - (w ^ 2) • (1 : Matrix n n ℂ))⁻¹ * A ∧
      R = (Aᴴ * A - (w ^ 2) • (1 : Matrix n n ℂ))⁻¹ * Aᴴ := by
  have hw2 : w ^ 2 * w⁻¹ = w := by field_simp
  have e2' : A * S = w • Q := sub_eq_zero.mp e2
  have e3' : Aᴴ * P = w • R := sub_eq_zero.mp e3
  have hP1 : (A * Aᴴ - (w ^ 2) • (1 : Matrix n n ℂ)) * (w⁻¹ • P) = 1 := by
    calc (A * Aᴴ - (w ^ 2) • (1 : Matrix n n ℂ)) * (w⁻¹ • P)
        = (A * Aᴴ) * (w⁻¹ • P) - (w ^ 2) • (w⁻¹ • P) := by
          rw [sub_mul, smul_mul_assoc, one_mul]
      _ = w⁻¹ • (A * (Aᴴ * P)) - (w ^ 2 * w⁻¹) • P := by
          rw [mul_smul_comm, mul_assoc, smul_smul]
      _ = A * R - w • P := by
          rw [e3', mul_smul_comm, smul_smul, inv_mul_cancel₀ hw, one_smul, hw2]
      _ = 1 := e1
  have hS1 : (Aᴴ * A - (w ^ 2) • (1 : Matrix n n ℂ)) * (w⁻¹ • S) = 1 := by
    calc (Aᴴ * A - (w ^ 2) • (1 : Matrix n n ℂ)) * (w⁻¹ • S)
        = (Aᴴ * A) * (w⁻¹ • S) - (w ^ 2) • (w⁻¹ • S) := by
          rw [sub_mul, smul_mul_assoc, one_mul]
      _ = w⁻¹ • (Aᴴ * (A * S)) - (w ^ 2 * w⁻¹) • S := by
          rw [mul_smul_comm, mul_assoc, smul_smul]
      _ = Aᴴ * Q - w • S := by
          rw [e2', mul_smul_comm, smul_smul, inv_mul_cancel₀ hw, one_smul, hw2]
      _ = 1 := e4
  have hX := Matrix.isUnit_det_of_right_inverse hP1
  have hY := Matrix.isUnit_det_of_right_inverse hS1
  have hXi := Matrix.inv_eq_right_inv hP1
  have hYi := Matrix.inv_eq_right_inv hS1
  have hP : P = w • (A * Aᴴ - (w ^ 2) • (1 : Matrix n n ℂ))⁻¹ := by
    rw [hXi, smul_smul, mul_inv_cancel₀ hw, one_smul]
  have hS : S = w • (Aᴴ * A - (w ^ 2) • (1 : Matrix n n ℂ))⁻¹ := by
    rw [hYi, smul_smul, mul_inv_cancel₀ hw, one_smul]
  refine ⟨hX, hY, hP, hS, ?_, ?_⟩
  · have : Q = w⁻¹ • (A * S) := by rw [e2', smul_smul, inv_mul_cancel₀ hw, one_smul]
    rw [this, hS, mul_smul_comm, smul_smul, inv_mul_cancel₀ hw, one_smul]
    exact Block_f1 A _ _ (w ^ 2) rfl rfl hX hY
  · have : R = w⁻¹ • (Aᴴ * P) := by rw [e3', smul_smul, inv_mul_cancel₀ hw, one_smul]
    rw [this, hP, mul_smul_comm, smul_smul, inv_mul_cancel₀ hw, one_smul]
    exact Block_f2 A _ _ (w ^ 2) rfl rfl hX hY

/-- The two diagonal products of blocks of `M̂` (3.1) [def_ML] for `D = 2` have the same trace. -/
private lemma Block_tr_diag (A X₁ Y₁ X₂ Y₂ : Matrix n n ℂ) (c₁ c₂ w₁ w₂ : ℂ) (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hx₁ : X₁ = A * Aᴴ - c₁ • 1) (hy₁ : Y₁ = Aᴴ * A - c₁ • 1)
    (hx₂ : X₂ = A * Aᴴ - c₂ • 1) (hy₂ : Y₂ = Aᴴ * A - c₂ • 1) (hX₁ : IsUnit X₁.det)
    (hY₁ : IsUnit Y₁.det) (hX₂ : IsUnit X₂.det) (hY₂ : IsUnit Y₂.det) :
    ((w₁ • X₁⁻¹) * (w₂ • X₂⁻¹)).trace = ((w₁ • Y₁⁻¹) * (w₂ • Y₂⁻¹)).trace := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]
  rw [Block_f5 A X₁ Y₁ X₂ Y₂ c₁ c₂ hc₁ hc₂ hx₁ hy₁ hx₂ hy₂ hX₁ hY₁ hX₂ hY₂]

/-- The two off-diagonal products of blocks of `M̂` (3.1) [def_ML] for `D = 2` have the same trace. -/
private lemma Block_tr_off (A X₁ Y₁ X₂ Y₂ : Matrix n n ℂ) (c₁ c₂ : ℂ) (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hx₁ : X₁ = A * Aᴴ - c₁ • 1) (hy₁ : Y₁ = Aᴴ * A - c₁ • 1)
    (hx₂ : X₂ = A * Aᴴ - c₂ • 1) (hy₂ : Y₂ = Aᴴ * A - c₂ • 1) (hX₁ : IsUnit X₁.det)
    (hY₁ : IsUnit Y₁.det) (hX₂ : IsUnit X₂.det) (hY₂ : IsUnit Y₂.det) :
    ((Y₁⁻¹ * Aᴴ) * (X₂⁻¹ * A)).trace = ((X₁⁻¹ * A) * (Y₂⁻¹ * Aᴴ)).trace := by
  have e1 : (Y₁⁻¹ * Aᴴ) * (X₂⁻¹ * A) = Y₁⁻¹ * (1 + c₂ • Y₂⁻¹) := by
    rw [← Block_f3' A Y₂ c₂ hy₂ hY₂]
    calc Y₁⁻¹ * Aᴴ * (X₂⁻¹ * A) = Y₁⁻¹ * (Aᴴ * X₂⁻¹) * A := by simp only [mul_assoc]
      _ = Y₁⁻¹ * (Y₂⁻¹ * Aᴴ) * A := by rw [Block_f2 A X₂ Y₂ c₂ hx₂ hy₂ hX₂ hY₂]
      _ = Y₁⁻¹ * (Y₂⁻¹ * (Aᴴ * A)) := by simp only [mul_assoc]
  have e2 : (X₁⁻¹ * A) * (Y₂⁻¹ * Aᴴ) = X₁⁻¹ * (1 + c₂ • X₂⁻¹) := by
    rw [← Block_f5a A X₂ Y₂ c₂ hx₂ hy₂ hX₂ hY₂]
    simp only [mul_assoc]
  rw [e1, e2]
  simp only [mul_add, mul_one, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [Block_f4 A X₁ Y₁ c₁ hc₁ hx₁ hy₁ hX₁ hY₁,
    Block_f5 A X₁ Y₁ X₂ Y₂ c₁ c₂ hc₁ hc₂ hx₁ hy₁ hx₂ hy₂ hX₁ hY₁ hX₂ hY₂]


end Alg

/-- The blocks of `M` for `D = 2` in terms of `w` ((2.15) [eq:MD=2]), from `(lam 2 N A - w) M = 1` and `w ≠ 0`. -/
private lemma Block_D2_alg (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) (hw : w ≠ 0)
    (M : Matrix (Idx 2 N) (Idx 2 N) ℂ)
    (h : (lam 2 N A - w • (1 : Matrix (Idx 2 N) (Idx 2 N) ℂ)) * M = 1) :
    IsUnit (A * Aᴴ - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ∧
      IsUnit (Aᴴ * A - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ∧
      (fun i j => M (0, i) (0, j)) =
        w • (A * Aᴴ - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ ∧
      (fun i j => M (1, i) (1, j)) =
        w • (Aᴴ * A - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ ∧
      (fun i j => M (0, i) (1, j)) =
        (A * Aᴴ - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * A ∧
      (fun i j => M (1, i) (0, j)) =
        (Aᴴ * A - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * Aᴴ := by
  obtain ⟨e1, e2, e3, e4⟩ := Block_eqs N A w M h (Matrix.of fun i j => M (0, i) (0, j))
    (Matrix.of fun i j => M (0, i) (1, j)) (Matrix.of fun i j => M (1, i) (0, j))
    (Matrix.of fun i j => M (1, i) (1, j)) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)
  exact Block_D2_core A w hw _ _ _ _ e1 e2 e3 e4

/-- For `D = 2`, `tr M_{(11)} = tr M_{(22)}` ((2.13) [def_M]). -/
private lemma Block_D2_tr (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) (hw : w ≠ 0)
    (M : Matrix (Idx 2 N) (Idx 2 N) ℂ)
    (h : (lam 2 N A - w • (1 : Matrix (Idx 2 N) (Idx 2 N) ℂ)) * M = 1) :
    ∑ i : Fin N, M (0, i) (0, i) = ∑ i : Fin N, M (1, i) (1, i) := by
  obtain ⟨hX, hY, hP, hS, -, -⟩ := Block_D2_alg N A w hw M h
  have h4 := Block_f4 A _ _ (w ^ 2) (pow_ne_zero 2 hw) rfl rfl hX hY
  have t1 : ∑ i : Fin N, M (0, i) (0, i) =
      (w • (A * Aᴴ - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace := by
    rw [← hP]; rfl
  have t2 : ∑ i : Fin N, M (1, i) (1, i) =
      (w • (Aᴴ * A - (w ^ 2) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace := by
    rw [← hS]; rfl
  rw [t1, t2, Matrix.trace_smul, Matrix.trace_smul, h4]


/-- `Σ_{i,j} X_{ji} Y_{ij} = tr (X Y)`. -/
private lemma Block_trsum {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    ∑ i, ∑ j, X j i * Y i j = (X * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_comm

/-- For `D = 2`, `M̂_{00} = M̂_{11}` and `M̂_{01} = M̂_{10}` (Lemma A.1 [lemma_usual_properties_of_m_and_mu] (vi)). -/
private lemma Block_Mhat_D2 (N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) :
    Mhat (lam 2 N A) z₁ z₂ 0 0 = Mhat (lam 2 N A) z₁ z₂ 1 1 ∧
      Mhat (lam 2 N A) z₁ z₂ 0 1 = Mhat (lam 2 N A) z₁ z₂ 1 0 := by
  have : Nonempty (Idx 2 N) := ⟨(0, ⟨0, hN⟩)⟩
  obtain ⟨hw₁, hm₁, hM₁⟩ := Block_spec (Block_lam_herm 2 N A) h₁
  obtain ⟨hw₂, hm₂, hM₂⟩ := Block_spec (Block_lam_herm 2 N A) h₂
  have hw₁0 : z₁ + mExt (lam 2 N A) z₁ ≠ 0 := fun h => hw₁ (by rw [h]; simp)
  have hw₂0 : z₂ + mExt (lam 2 N A) z₂ ≠ 0 := fun h => hw₂ (by rw [h]; simp)
  obtain ⟨hX₁, hY₁, hP₁, hS₁, hQ₁, hR₁⟩ := Block_D2_alg N A _ hw₁0 _ hM₁
  obtain ⟨hX₂, hY₂, hP₂, hS₂, hQ₂, hR₂⟩ := Block_D2_alg N A _ hw₂0 _ hM₂
  have hc₁ := pow_ne_zero 2 hw₁0
  have hc₂ := pow_ne_zero 2 hw₂0
  have key := Block_tr_diag A _ _ _ _ _ _ (z₁ + mExt (lam 2 N A) z₁) (z₂ + mExt (lam 2 N A) z₂) hc₁ hc₂ rfl rfl rfl rfl hX₁ hY₁ hX₂ hY₂
  have key' := Block_tr_off A _ _ _ _ _ _ hc₁ hc₂ rfl rfl rfl rfl hX₁ hY₁ hX₂ hY₂
  refine ⟨?_, ?_⟩
  · rw [Block_Mhat_apply 2 N (by norm_num), Block_Mhat_apply 2 N (by norm_num)]
    have e1 := Block_trsum (fun i j => MExt (lam 2 N A) z₁ (0, i) (0, j))
      (fun i j => MExt (lam 2 N A) z₂ (0, i) (0, j))
    have e2 := Block_trsum (fun i j => MExt (lam 2 N A) z₁ (1, i) (1, j))
      (fun i j => MExt (lam 2 N A) z₂ (1, i) (1, j))
    rw [hP₁, hP₂] at e1
    rw [hS₁, hS₂] at e2
    exact congrArg (fun x => (N : ℂ)⁻¹ * x) (e1.trans (key.trans e2.symm))
  · rw [Block_Mhat_apply 2 N (by norm_num), Block_Mhat_apply 2 N (by norm_num)]
    have e1 := Block_trsum (fun i j => MExt (lam 2 N A) z₁ (1, i) (0, j))
      (fun i j => MExt (lam 2 N A) z₂ (0, i) (1, j))
    have e2 := Block_trsum (fun i j => MExt (lam 2 N A) z₁ (0, i) (1, j))
      (fun i j => MExt (lam 2 N A) z₂ (1, i) (0, j))
    rw [hR₁, hQ₂] at e1
    rw [hQ₁, hR₂] at e2
    exact congrArg (fun x => (N : ℂ)⁻¹ * x) (e1.trans (key'.trans e2.symm))

/-- `u_l(a) = D^{-1/2} ζ^{l a}` with `ζ = e^{2πi/D}`. -/
private lemma Block_fv (D : ℕ) (l a : Fin D) :
    fourierVec D l a = ((Real.sqrt D)⁻¹ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / D) ^ ((l : ℕ) * (a : ℕ)) := by
  unfold fourierVec
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `ζ^n = ζ^{n mod D}` for `ζ = e^{2πi/D}`. -/
private lemma Block_zeta_pow (D : ℕ) (hD : D ≠ 0) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I / D) ^ n =
      Complex.exp (2 * Real.pi * Complex.I / D) ^ (n % D) := by
  have h1 : Complex.exp (2 * Real.pi * Complex.I / D) ^ D = 1 :=
    (Complex.isPrimitiveRoot_exp D hD).pow_eq_one
  conv_lhs => rw [← Nat.div_add_mod n D, pow_add, pow_mul, h1, one_pow, one_mul]

/-- `u_l(a)^* u_l(a) = 1/D`. -/
private lemma Block_norm (D : ℕ) (hD : D ≠ 0) (l a : Fin D) :
    star (fourierVec D l a) * fourierVec D l a = (D : ℂ)⁻¹ := by
  have hζ : ‖Complex.exp (2 * Real.pi * Complex.I / D)‖ = 1 :=
    (Complex.isPrimitiveRoot_exp D hD).norm'_eq_one hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  rw [Block_fv, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [norm_mul, norm_pow, hζ, one_pow, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hDpos.le]
  push_cast
  rfl

open Fin.NatCast Fin.CommRing in
/-- A translation invariant matrix has `u_l` as an eigenvector with eigenvalue `u_l^* B u_l` ((A.25) [eq_lambdak]). -/
private lemma Block_circ (D : ℕ) [NeZero D] (B : Matrix (Fin D) (Fin D) ℂ)
    (hB : ∀ a b a' b' : Fin D, b - a = b' - a' → B a b = B a' b') (l : Fin D) :
    B *ᵥ fourierVec D l = circEig B l • fourierVec D l := by
  have hD : D ≠ 0 := NeZero.ne D
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / D) with hζ
  set lam' : ℂ := ∑ c : Fin D, B 0 c * ζ ^ ((l : ℕ) * (c : ℕ)) with hlam
  have hmul : ∀ a c : Fin D, ζ ^ ((l : ℕ) * ((a + c : Fin D) : ℕ)) =
      ζ ^ ((l : ℕ) * (a : ℕ)) * ζ ^ ((l : ℕ) * (c : ℕ)) := by
    intro a c
    rw [← pow_add, Block_zeta_pow D hD, Block_zeta_pow D hD ((l : ℕ) * (a : ℕ) + (l : ℕ) * (c : ℕ)),
      Fin.val_add, ← mul_add, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have hBu : ∀ a, (B *ᵥ fourierVec D l) a = lam' * fourierVec D l a := by
    intro a
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp (Equiv.addLeft a)]
    rw [hlam, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Equiv.coe_addLeft]
    rw [hB a (a + c) 0 c (by ring), Block_fv, Block_fv, hmul]
    ring
  have hcirc : circEig B l = lam' := by
    unfold circEig
    have : ∀ a : Fin D, ∑ b : Fin D, star (fourierVec D l a) * B a b * fourierVec D l b =
        lam' * (D : ℂ)⁻¹ := by
      intro a
      have h1 : ∑ b : Fin D, star (fourierVec D l a) * B a b * fourierVec D l b =
          star (fourierVec D l a) * (B *ᵥ fourierVec D l) a := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [h1, hBu, ← mul_assoc, mul_comm (star _), mul_assoc, Block_norm D hD]
    rw [Finset.sum_congr rfl fun a _ => this a]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
    field_simp
  funext a
  rw [hBu a, hcirc]
  rfl

/-- (2.13) [def_M]: for `Λ = lam D N A`, `S(M) = mI`, i.e. `D ⟨M E_a⟩ = m` for every block `a`,
and `M` solves the matrix Dyson equation `(mI + z - Λ) M + I = 0`; `z ∉ ℝ`. -/
theorem def_M_scalar (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    (∀ a : Fin D, (D : ℂ) * ntr (MExt (lam D N A) z * Ea D N a) = mExt (lam D N A) z) ∧
      ((mExt (lam D N A) z + z) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - lam D N A) *
          MExt (lam D N A) z + 1 = 0 := by
  have : NeZero D := ⟨by omega⟩
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN⟩)⟩
  have hD0 : D ≠ 0 := by omega
  obtain ⟨hw, hm, hM⟩ := Block_spec (Block_lam_herm D N A) hz
  have hw0 : z + mExt (lam D N A) z ≠ 0 := fun h => hw (by rw [h]; simp)
  refine ⟨?_, ?_⟩
  · have hT : ∀ a b : Fin D, ∑ i : Fin N, MExt (lam D N A) z (a, i) (a, i) =
        ∑ i : Fin N, MExt (lam D N A) z (b, i) (b, i) := by
      by_cases h3 : 3 ≤ D
      · refine Block_iter1 (fun a => ∑ i : Fin N, MExt (lam D N A) z (a, i) (a, i)) ?_
        intro a
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Block_shift D N h3 A (z + mExt (lam D N A) z) (a, i) (a, i)
      · obtain rfl : D = 2 := by omega
        intro a b
        have key := Block_D2_tr N A _ hw0 _ hM
        fin_cases a <;> fin_cases b
        · rfl
        · exact key
        · exact key.symm
        · rfl
    intro a
    rw [Block_diag_apply D N hD0 _ _ a, hm, Block_ntr_apply]
    rw [Finset.sum_congr rfl fun b _ => hT b a]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hD0
    by_cases hN0 : (N : ℂ) = 0
    · simp [hN0]
    · field_simp
  · have : (mExt (lam D N A) z + z) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - lam D N A =
        -(lam D N A - (z + mExt (lam D N A) z) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
      rw [add_comm]; abel
    rw [this, neg_mul, hM]
    simp


/-- (2.15) [eq:MD=2]: for `D = 2` and `w = z + m(z)`, the blocks of `M` are
`w (AA^* - w²)⁻¹`, `w (A^*A - w²)⁻¹`, `(AA^* - w²)⁻¹ A`, `(A^*A - w²)⁻¹ A^*`, and
`m = N⁻¹ tr M_{(11)}`; `z ∉ ℝ`. -/
theorem eq_MD2 (N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    (fun i j => MExt (lam 2 N A) z (0, i) (0, j)) =
        (z + mExt (lam 2 N A) z) •
          (A * Aᴴ - (z + mExt (lam 2 N A) z) ^ 2 • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ ∧
      (fun i j => MExt (lam 2 N A) z (1, i) (1, j)) =
        (z + mExt (lam 2 N A) z) •
          (Aᴴ * A - (z + mExt (lam 2 N A) z) ^ 2 • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ ∧
      (fun i j => MExt (lam 2 N A) z (0, i) (1, j)) =
        (A * Aᴴ - (z + mExt (lam 2 N A) z) ^ 2 • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * A ∧
      (fun i j => MExt (lam 2 N A) z (1, i) (0, j)) =
        (Aᴴ * A - (z + mExt (lam 2 N A) z) ^ 2 • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * Aᴴ ∧
      mExt (lam 2 N A) z = (N : ℂ)⁻¹ * Matrix.trace (fun i j => MExt (lam 2 N A) z (0, i) (0, j)) := by
  have : Nonempty (Idx 2 N) := ⟨(0, ⟨0, hN⟩)⟩
  obtain ⟨hw, hm, hM⟩ := Block_spec (Block_lam_herm 2 N A) hz
  have hw0 : z + mExt (lam 2 N A) z ≠ 0 := fun h => hw (by rw [h]; simp)
  obtain ⟨-, -, hP, hS, hQ, hR⟩ := Block_D2_alg N A _ hw0 _ hM
  refine ⟨hP, hS, hQ, hR, ?_⟩
  have key := Block_D2_tr N A _ hw0 _ hM
  change mExt (lam 2 N A) z = (N : ℂ)⁻¹ * ∑ i : Fin N, MExt (lam 2 N A) z (0, i) (0, i)
  rw [hm, Block_ntr_apply, Fin.sum_univ_two, ← key]
  by_cases hN0 : (N : ℂ) = 0
  · simp [hN0]
  · field_simp
    ring

/-- Lemma A.1 [lemma_usual_properties_of_m_and_mu] (vi): `M̂(z₁, z₂)` is translation
invariant, `M̂_{ab} = M̂_{a'b'}` whenever `b - a = b' - a' mod D`; `z₁, z₂ ∉ ℝ`. -/
theorem Mhat_translation (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (a b a' b' : Fin D) (hab : b - a = b' - a') :
    Mhat (lam D N A) z₁ z₂ a b = Mhat (lam D N A) z₁ z₂ a' b' := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : D ≠ 0 := by omega
  by_cases hN : N = 0
  · subst hN
    simp [Block_Mhat_apply D 0 hD0]
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  refine Block_iter2 (fun a b => Mhat (lam D N A) z₁ z₂ a b) ?_ a b a' b' hab
  intro a b
  by_cases h3 : 3 ≤ D
  · rw [Block_Mhat_apply D N hD0, Block_Mhat_apply D N hD0]
    refine congrArg (fun x => (N : ℂ)⁻¹ * x) ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have s1 := Block_shift D N h3 A (z₁ + mExt (lam D N A) z₁) (b, j) (a, i)
    have s2 := Block_shift D N h3 A (z₂ + mExt (lam D N A) z₂) (a, i) (b, j)
    exact congrArg₂ (· * ·) s1 s2
  · obtain rfl : D = 2 := by omega
    have key := Block_Mhat_D2 N hN1 A z₁ z₂ h₁ h₂
    fin_cases a <;> fin_cases b
    · exact key.1.symm
    · exact key.2.symm
    · exact key.2
    · exact key.1

/-- (A.25) [eq_lambdak]: the Fourier vectors `u_l` are eigenvectors of `M̂(z₁, z₂)` with
eigenvalues `λ̂_l`; `z₁, z₂ ∉ ℝ`. -/
theorem Mhat_eigvec (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (l : Fin D) :
    Mhat (lam D N A) z₁ z₂ *ᵥ fourierVec D l =
      circEig (Mhat (lam D N A) z₁ z₂) l • fourierVec D l := by
  have : NeZero D := ⟨by omega⟩
  exact Block_circ D _ (fun a b a' b' hab => Mhat_translation D hD N A z₁ z₂ h₁ h₂ a b a' b' hab) l

/-- The interaction `Λ = lam D N A` of (1.3) [matrix_H] (for `D = 2` in the form
`[[0, A], [A^*, 0]]` of (2.15) [eq:MD=2]) is Hermitian, for every `A`. -/
theorem lam_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : (lam D N A).IsHermitian := by
  exact Block_lam_herm D N A

end RBMTransitionEdge

end
