module

public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Localized.Expansion.Words
public import RBMTransitionEdge.Localized.Pathwise

@[expose] public section

/-!
# Values of the expressions of the expansion of §5.3

The data of the two slots of (5.32) [eq;expT0], the matrix of a word, the value of an expression
of the class (5.33) [definition_class_of_expression_loop] at an array, and the polarization
identity (5.29) [expansion_of_im] for the four flagged starting loops.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The data of the two slots of (5.32) [eq;expT0]: the coupling `A`, the slot deformations
`c_a Λ`, the spectral parameters `z_a` (`Im z_a > 0`), the flags (`true`: `𝒢_a = G_a^*`) and the
shift `δ` of `Λ̃ = Λ - δ`. -/
structure LoopEnv (D N : ℕ) where
  /-- The coupling `A` of (1.3) [matrix_H]. -/
  A : Matrix (Fin N) (Fin N) ℂ
  /-- The slot deformations `c_a Λ`. -/
  c : Fin 2 → ℝ
  /-- The spectral parameters. -/
  z : Fin 2 → ℂ
  /-- The flags: `true` for `G_a^*`. -/
  s : Fin 2 → Bool
  /-- The shift `δ` of `Λ̃ = Λ - δ`. -/
  δ : ℝ

/-- `𝒢_a = (h + c_a Λ - z_a)⁻¹`, or `(h + c_a Λ - z̄_a)⁻¹ = G_a^*` when the flag is set. -/
def LoopEnv.G {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) (a : Fin 2) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of h + ((e.c a : ℂ) • lam D N e.A)) (if e.s a then star (e.z a) else e.z a)

/-- `𝔐_a = M(z_a)` of (2.17) [def_G0] for `c_a Λ`, or `M(z̄_a)` when the flag is set. -/
def LoopEnv.M {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) : Matrix (Idx D N) (Idx D N) ℂ :=
  MExt ((e.c a : ℂ) • lam D N e.A) (if e.s a then star (e.z a) else e.z a)

/-- The block projection `E_x` at the value `ι x` of the bound index `x`. -/
def LoopEnv.E {D N : ℕ} (_e : LoopEnv D N) {nb : ℕ} (ι : Fin nb → Fin D) (x : ℕ) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  if hx : x < nb then Ea D N (ι ⟨x, hx⟩) else 1

/-- `Λ̃ = Λ - δ`. -/
def LoopEnv.Lt {D N : ℕ} (e : LoopEnv D N) : Matrix (Idx D N) (Idx D N) ℂ :=
  lam D N e.A - (e.δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)

/-- The matrix of a word, for resolvents `G a`, limits `M a`, projections `E x` and `Λ̃ = L`. -/
def loopWordMat {ι : Type*} [Fintype ι] [DecidableEq ι] (G M : Fin 2 → Matrix ι ι ℂ)
    (E : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (w : List LoopLetter) : Matrix ι ι ℂ :=
  (w.map fun x => match x with
    | .res a => G a
    | .det a => M a
    | .proj y => E y
    | .lamt _ => L).prod

/-- The value of an expression (5.33) [definition_class_of_expression_loop] at the array `h`:
`D^{dexp} N^{-S} Σ_ι Π ⟨(𝒢_a - 𝔐_a) E_x⟩ Π ⟨word⟩`, the sum over the bound block indices. -/
def LoopExpr.evalH {D N : ℕ} (T : LoopExpr) (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (D : ℂ) ^ T.dexp * ((N : ℂ) ^ T.S)⁻¹ * ∑ ι : Fin T.nb → Fin D,
    (T.weights.map fun p => ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)).prod *
    (T.loops.map fun w => ntr (loopWordMat (e.G h) e.M (e.E ι) e.Lt w)).prod

/-- The value of the starting loop (5.32) [eq;expT0]: `⟨𝒢₀ Λ̃ 𝒢₁ Λ̃⟩`, with no bound index, no
weight and coefficient `1` in the sense of (5.33) [definition_class_of_expression_loop]. -/
private theorem loopStart_evalH {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) :
    loopStart.evalH e h = ntr (e.G h 0 * e.Lt * e.G h 1 * e.Lt) := by
  have : Unique (Fin loopStart.nb → Fin D) := inferInstanceAs (Unique (Fin 0 → Fin D))
  unfold LoopExpr.evalH
  rw [Fintype.sum_unique]
  simp [loopStart, loopWordMat, Matrix.mul_assoc]

/-- For Hermitian `X`, the resolvent at `z̄` is the adjoint of the resolvent at `z`, the identity
`G(z̄) = G(z)^*` behind the flags of (5.32) [eq;expT0]. -/
private theorem res_star_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) : res X (star z) = (res X z)ᴴ := by
  unfold res
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hX.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/-- The polarization identity (5.29) [expansion_of_im]: the signed sum of the four flagged
starting loops (5.32) [eq;expT0] is `-4 ⟨Im G₀ Λ̃ Im G₁ Λ̃⟩`. -/
theorem loop_polar {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * loopStart.evalH { e with s := s } h =
      -4 * ntr (imRes (Matrix.of h + ((e.c 0 : ℂ) • lam D N e.A)) (e.z 0) * e.Lt *
        imRes (Matrix.of h + ((e.c 1 : ℂ) • lam D N e.A)) (e.z 1) * e.Lt) := by
  have hX : ∀ a : Fin 2, (Matrix.of h + ((e.c a : ℂ) • lam D N e.A)).IsHermitian := by
    intro a
    refine hh.add ?_
    have := (lam_isHermitian D N e.A)
    unfold Matrix.IsHermitian at this ⊢
    rw [Matrix.conjTranspose_smul, this]
    simp
  set X : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ := fun a => Matrix.of h + ((e.c a : ℂ) • lam D N e.A)
    with hXdef
  have hG : ∀ (s : Fin 2 → Bool) (a : Fin 2), ({ e with s := s } : LoopEnv D N).G h a =
      if s a then (res (X a) (e.z a))ᴴ else res (X a) (e.z a) := by
    intro s a
    by_cases hs : s a
    · have := res_star_of_isHermitian (X a) (hX a) (e.z a)
      simp only [LoopEnv.G, hs, ite_true, Complex.star_def] at this ⊢
      exact this
    · simp [LoopEnv.G, hs, hXdef]
  set G : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ := fun a => res (X a) (e.z a) with hGdef
  have hLt : ({ e with s := fun _ => false } : LoopEnv D N).Lt = e.Lt := rfl
  have hterm : ∀ s : Fin 2 → Bool, loopStart.evalH { e with s := s } h =
      ntr ((if s 0 then (G 0)ᴴ else G 0) * e.Lt * (if s 1 then (G 1)ᴴ else G 1) * e.Lt) := by
    intro s
    rw [loopStart_evalH, hG s 0, hG s 1]
    rfl
  simp only [hterm]
  refine Eq.trans (Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Bool) _
    (fun p : Bool × Bool => (if p.1 = p.2 then (1 : ℂ) else -1) *
      ntr ((if p.1 then (G 0)ᴴ else G 0) * e.Lt * (if p.2 then (G 1)ᴴ else G 1) * e.Lt))
    (fun s => rfl)) ?_
  have hIm : ∀ a : Fin 2, imRes (X a) (e.z a) = (2 * Complex.I)⁻¹ • (G a - (G a)ᴴ) := fun a => rfl
  rw [show imRes (Matrix.of h + ((e.c 0 : ℂ) • lam D N e.A)) (e.z 0) =
    (2 * Complex.I)⁻¹ • (G 0 - (G 0)ᴴ) from hIm 0,
    show imRes (Matrix.of h + ((e.c 1 : ℂ) • lam D N e.A)) (e.z 1) =
    (2 * Complex.I)⁻¹ • (G 1 - (G 1)ᴴ) from hIm 1]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  unfold ntr
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  have hI : (2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
    rw [← mul_inv, show (2 * Complex.I) * (2 * Complex.I) = -4 by
      rw [mul_mul_mul_comm, Complex.I_mul_I]; norm_num]
    norm_num
  have hF : (if False then (1 : ℂ) else -1) = -1 := by simp
  simp only [Bool.true_eq_false, hF]
  linear_combination (4 * ((Fintype.card (Idx D N) : ℂ))⁻¹ *
    ((G 0 * e.Lt * G 1 * e.Lt).trace - ((G 0)ᴴ * e.Lt * G 1 * e.Lt).trace -
      (G 0 * e.Lt * (G 1)ᴴ * e.Lt).trace + ((G 0)ᴴ * e.Lt * (G 1)ᴴ * e.Lt).trace)) * hI

end RBMTransitionEdge

end
