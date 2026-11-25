module

public import RBMTransitionEdge.Main.Statements
public import RBMTransitionEdge.Det.Density
public import RBMTransitionEdge.Tools.MinMax

@[expose] public section

/-!
# The reflection `k ↦ DN + 1 - k`

Theorem 2.4 [theorem_localized_eigenvector_localization] and Theorem 2.5
[theorem_localized_eigenvalue] for `2k ≤ DN + 1`, and the reflection `h ↦ -h`, `A ↦ -A` that
gives every `k ≤ DN` (§5: the other case can be treated analogously).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- Theorem 2.4 [theorem_localized_eigenvector_localization] for `k` with `2k ≤ DN + 1`
(so `𝔯(k) = k`): the statement `LocalizedEvecStatement` with `k ≤ DN` replaced by
`2k ≤ DN + 1`. -/
def LocalizedEvecHalf : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    (∀ ε : ℝ, 0 < ε → ε < 2 * εA → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
          ∀ a : Fin D, blockMass u a <
            1 - (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ε₀))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧
          ∀ a : Fin D, blockMass u a ≤ 1 - (N : ℝ) ^ (-c)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-c)))

/-- Theorem 2.5 [theorem_localized_eigenvalue] for `k` with `2k ≤ DN + 1` (so `𝔯(k) = k`): the
statement `LocalizedEvalStatement` with `k ≤ DN` replaced by `2k ≤ DN + 1`. -/
def LocalizedEvalHalf : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    (∀ ε ε₀ : ℝ, 0 < ε → 0 < ε₀ → ε₀ < 2 * ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-1 + ε) * hsNorm A < |shiftX D N A k w|} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ε₀))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N k ^ (-(1 / 3 : ℝ)) ≤
          |shiftX D N A k w|} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c))) ∧
    (∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      |(∫ w, corrPairing (D * N) n (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ))
            (quant (rho (lam D N A)) (D * N) k) O (eigK (HLam D N A w)) ∂(blockLaw D N L)) -
        (∫ w, corrPairing (D * N) n (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ))
            (quant rhoSc (D * N) k) O (eigK (blockH D N w)) ∂(blockLaw D N L))| ≤
        (N : ℝ) ^ (-c))

/-- The integral against the image of `μ` under `x ↦ -x`. -/
private lemma Reflect_integral_neg {α E : Type*} [MeasurableSpace α] [InvolutiveNeg α]
    [MeasurableNeg α] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) :
    ∫ x, f x ∂(μ.map (fun x : α => -x)) = ∫ x, f (-x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.neg α) f

/-- Integrability against the image of `μ` under `x ↦ -x`. -/
private lemma Reflect_integrable_neg {α E : Type*} [MeasurableSpace α] [InvolutiveNeg α]
    [MeasurableNeg α] [NormedAddCommGroup E] (μ : Measure α) (f : α → E) :
    Integrable f (μ.map (fun x : α => -x)) ↔ Integrable (fun x => f (-x)) μ :=
  (MeasurableEquiv.neg α).measurableEmbedding.integrable_map_iff

/-- The entry laws of `-h`: the images of `νd`, `νo` under `x ↦ -x`. All of (2.1)
[eq:meanvar], (2.2) [eq:meanvar2] and (2.3) [eq:highmoment] are invariant under it. -/
def Reflect_negLaws {C : ℕ → ℝ} (L : EntryLaws C) : EntryLaws C where
  νd := L.νd.map (fun x : ℝ => -x)
  νo := L.νo.map (fun z : ℂ => -z)
  intd := fun p => by
    change Integrable (fun x : ℝ => |x| ^ p) ((L.νd : Measure ℝ).map (fun x : ℝ => -x))
    rw [Reflect_integrable_neg]
    simpa only [abs_neg] using L.intd p
  into := fun p => by
    change Integrable (fun z : ℂ => ‖z‖ ^ p) ((L.νo : Measure ℂ).map (fun z : ℂ => -z))
    rw [Reflect_integrable_neg]
    simpa only [norm_neg] using L.into p
  meand := by
    change ∫ x, x ∂((L.νd : Measure ℝ).map (fun x : ℝ => -x)) = 0
    rw [Reflect_integral_neg, integral_neg, L.meand, neg_zero]
  vard := by
    change ∫ x, x ^ 2 ∂((L.νd : Measure ℝ).map (fun x : ℝ => -x)) = 1
    rw [Reflect_integral_neg]
    simpa only [neg_sq] using L.vard
  meano := by
    change ∫ z, z ∂((L.νo : Measure ℂ).map (fun z : ℂ => -z)) = 0
    rw [Reflect_integral_neg, integral_neg, L.meano, neg_zero]
  varo := by
    change ∫ z, ‖z‖ ^ 2 ∂((L.νo : Measure ℂ).map (fun z : ℂ => -z)) = 1
    rw [Reflect_integral_neg]
    simpa only [norm_neg] using L.varo
  pseudo := by
    change ∫ z, z ^ 2 ∂((L.νo : Measure ℂ).map (fun z : ℂ => -z)) = 0
    rw [Reflect_integral_neg]
    simpa only [neg_sq] using L.pseudo
  moments := fun p => by
    change (∫ x, |x| ^ p ∂((L.νd : Measure ℝ).map (fun x : ℝ => -x))) +
      (∫ z, ‖z‖ ^ p ∂((L.νo : Measure ℂ).map (fun z : ℂ => -z))) ≤ C p
    rw [Reflect_integral_neg, Reflect_integral_neg]
    simpa only [abs_neg, norm_neg] using L.moments p

/-- `blockLaw D N (Reflect_negLaws L)` is the image of `blockLaw D N L` under `w ↦ -w`. -/
lemma Reflect_blockLaw_neg (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    (blockLaw D N L).map (fun w : Fin D → Coords N => -w) = blockLaw D N (Reflect_negLaws L) := by
  have h1 : (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)).map (fun x : Fin N → ℝ => -x) =
      Measure.pi fun _ : Fin N => (Reflect_negLaws L).νd := by
    have := Measure.pi_map_pi (μ := fun _ : Fin N => (L.νd : Measure ℝ))
      (f := fun _ => fun x : ℝ => -x) (fun _ => measurable_neg.aemeasurable)
    exact this
  have h2 : (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)).map (fun x : Fin N → ℂ => -x) =
      Measure.pi fun _ : Fin N => (Reflect_negLaws L).νo := by
    have := Measure.pi_map_pi (μ := fun _ : Fin N => (L.νo : Measure ℂ))
      (f := fun _ => fun x : ℂ => -x) (fun _ => measurable_neg.aemeasurable)
    exact this
  have h3 : (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)).map
      (fun x : Fin N → Fin N → ℂ => -x) =
      Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (Reflect_negLaws L).νo := by
    have := Measure.pi_map_pi (μ := fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
      (f := fun _ => fun x : Fin N → ℂ => -x) (fun _ => measurable_neg.aemeasurable)
    rw [← h2]
    exact this
  have h4 : (coordLaw N L).map (fun w : Coords N => -w) = coordLaw N (Reflect_negLaws L) := by
    unfold coordLaw
    rw [← h1, ← h3]
    exact (Measure.map_prod_map _ _ measurable_neg measurable_neg).symm
  have hsf : SigmaFinite ((coordLaw N L).map (fun w : Coords N => -w)) := by
    rw [h4]
    unfold coordLaw
    infer_instance
  unfold blockLaw
  rw [← h4]
  exact Measure.pi_map_pi (μ := fun _ : Fin D => coordLaw N L)
      (f := fun _ => fun x : Coords N => -x) (hμ := fun _ => hsf)
      (fun _ => measurable_neg.aemeasurable)

/-- The law of `-w` under `blockLaw D N L`, on arbitrary sets: `blockLaw D N L (-w ∈ T)` is
`blockLaw D N (Reflect_negLaws L) T`. -/
private lemma Reflect_blockLaw_preimage (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (T : Set (Fin D → Coords N)) :
    blockLaw D N L ((fun w : Fin D → Coords N => -w) ⁻¹' T) =
      blockLaw D N (Reflect_negLaws L) T := by
  rw [← Reflect_blockLaw_neg]
  exact ((MeasurableEquiv.neg (Fin D → Coords N)).map_apply T).symm

/-- The integral against `blockLaw D N (Reflect_negLaws L)` is the integral of `f (-w)` against
`blockLaw D N L`. -/
private lemma Reflect_blockLaw_integral (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (f : (Fin D → Coords N) → ℝ) :
    ∫ w, f w ∂(blockLaw D N (Reflect_negLaws L)) = ∫ w, f (-w) ∂(blockLaw D N L) := by
  rw [← Reflect_blockLaw_neg]
  exact Reflect_integral_neg _ f

/-- `wig n (-w) = -wig n w`. -/
private lemma Reflect_wig_neg (n : ℕ) (w : Coords n) : wig n (-w) = -wig n w := by
  ext i j
  simp only [wig, Matrix.neg_apply]
  by_cases h : i = j
  · simp [h]
  · by_cases h' : i < j <;> simp [h, h']

/-- `H(-w) = -H(w)`. -/
private lemma Reflect_blockH_neg (D N : ℕ) (w : Fin D → Coords N) :
    blockH D N (-w) = -blockH D N w := by
  ext p q
  simp only [blockH, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp [Reflect_wig_neg]

/-- `Λ(-A) = -Λ(A)`. -/
private lemma Reflect_lam_neg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N (-A) = -lam D N A := by
  ext p q
  simp only [lam, Matrix.neg_apply, star_neg]
  split_ifs <;> simp [add_comm]

/-- `H_Λ(-A, -w) = -H_Λ(A, w)`. -/
private lemma Reflect_HLam_neg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin D → Coords N) :
    HLam D N (-A) (-w) = -HLam D N A w := by
  unfold HLam
  rw [Reflect_blockH_neg, Reflect_lam_neg, neg_add]

/-- `‖-A‖ = ‖A‖`. -/
private lemma Reflect_opNorm_neg {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    opNorm (-A) = opNorm A := by
  rw [opNorm, opNorm, map_neg, norm_neg]

/-- `‖-A‖_HS = ‖A‖_HS`. -/
private lemma Reflect_hsNorm_neg {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsNorm (-A) = hsNorm A := by
  simp [hsNorm]

/-- `𝔯(DN + 1 - k) = 𝔯(k)` for `k ≤ DN + 1`. -/
private lemma Reflect_rk (D N k : ℕ) (hk : k ≤ D * N + 1) : rk D N (D * N + 1 - k) = rk D N k := by
  unfold rk
  have : D * N + 1 - (D * N + 1 - k) = k := by omega
  rw [this, min_comm]

/-- The card of the index set is `DN`. -/
private lemma Reflect_card (D N : ℕ) : Fintype.card (Idx D N) = D * N := by
  simp [Idx]

/-- `λ_{DN+1-k}(-X) = -λ_k(X)` for a Hermitian `X` on `Idx D N`. -/
private lemma Reflect_eigK_neg (D N : ℕ) (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N) :
    eigK (-X) (D * N + 1 - k) = -eigK X k := by
  have := eigK_neg X hX (D * N + 1 - k) (by omega) (by rw [Reflect_card]; omega)
  rw [this, Reflect_card]
  congr 2
  omega

/-- A vector is a unit eigenvector of `-H` for `-μ` iff it is one of `H` for `μ`. -/
private lemma Reflect_isUnitEigvec_neg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (μ : ℝ)
    (u : ι → ℂ) : IsUnitEigvec (-M) (-μ) u ↔ IsUnitEigvec M μ u := by
  unfold IsUnitEigvec
  rw [Matrix.neg_mulVec, Complex.ofReal_neg, neg_smul, neg_inj]

/-- The event of Theorem 2.4 for `(A, k)` is the preimage under `w ↦ -w` of the event for
`(-A, DN + 1 - k)`. -/
private lemma Reflect_evec_set (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ D * N) (P : (Idx D N → ℂ) → Prop) :
    {w : Fin D → Coords N | ∃ u, IsUnitEigvec (HLam D N A w) (eigK (HLam D N A w) k) u ∧ P u} =
      (fun w : Fin D → Coords N => -w) ⁻¹'
        {w : Fin D → Coords N | ∃ u, IsUnitEigvec (HLam D N (-A) w)
          (eigK (HLam D N (-A) w) (D * N + 1 - k)) u ∧ P u} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Reflect_HLam_neg]
  rw [Reflect_eigK_neg D N _ (HLam_isHermitian D N A w) k hk1 hk]
  simp only [Reflect_isUnitEigvec_neg]

section Reflect_lam
open scoped Matrix.Norms.L2Operator

/-- The interaction `Λ` of (1.3) [matrix_H] is Hermitian. -/
private lemma Reflect_lam_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (lam D N A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [lam, star_add]
  split_ifs <;> simp [add_comm]

/-- The embedding of the `N`-dimensional space as the `a`-th block. -/
private def Reflect_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

/-- The block embedding `J_a` is an isometry: `J_a^* J_a = 1`. -/
private lemma Reflect_J_conj_mul (D N : ℕ) (a : Fin D) :
    (Reflect_J D N a)ᴴ * Reflect_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Reflect_J, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `‖J_a‖ ≤ 1`. -/
private lemma Reflect_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖Reflect_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (Reflect_J D N a)
  rw [Reflect_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖Reflect_J D N a‖ := norm_nonneg _
  nlinarith

/-- `‖J_a M J_b^*‖ ≤ ‖M‖`. -/
private lemma Reflect_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖Reflect_J D N a * M * (Reflect_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := Reflect_J_norm D N hN a
  have hb := Reflect_J_norm D N hN b
  calc ‖Reflect_J D N a * M * (Reflect_J D N b)ᴴ‖ ≤ ‖Reflect_J D N a * M‖ * ‖(Reflect_J D N b)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Reflect_J D N a‖ * ‖M‖) * ‖(Reflect_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

/-- The entries of the block `J_a M J_b^*`. -/
private lemma Reflect_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (Reflect_J D N a * M * (Reflect_J D N b)ᴴ) p q =
      if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Reflect_J, Prod.ext_iff, h1, h2]

/-- `Λ` as a sum of blocks `J_a A J_b^*` and `J_a A^* J_b^*`. -/
private lemma Reflect_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then Reflect_J D N a * A * (Reflect_J D N b)ᴴ else 0) +
        (if fwd D b a then Reflect_J D N a * Aᴴ * (Reflect_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D, (if fwd D a b then Reflect_J D N a * A * (Reflect_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, Reflect_block_apply]
  have e2 : ∀ a b : Fin D,
      (if fwd D b a then Reflect_J D N a * Aᴴ * (Reflect_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, Reflect_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]


/-- `‖Λ‖ ≤ 2 D² ‖A‖`. -/
private lemma Reflect_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [Reflect_lam_eq]
  have hb : ∀ a b : Fin D, ‖(if fwd D a b then Reflect_J D N a * A * (Reflect_J D N b)ᴴ else 0) +
      (if fwd D b a then Reflect_J D N a * Aᴴ * (Reflect_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then Reflect_J D N a * A * (Reflect_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact Reflect_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then Reflect_J D N a * Aᴴ * (Reflect_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (Reflect_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


/-- For `D ≥ 1` and `δA > 0`, `‖A‖ ≤ N^{-δA}` gives `‖Λ‖ ≤ 1/10` for `N` large. -/
private lemma Reflect_lam_small (D : ℕ) (hD : 1 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N : ℕ, N₁ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-δA) → opNorm (lam D N A) ≤ 1 / 10 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨max 1 ⌈(20 * (D : ℝ) ^ 2) ^ (1 / δA)⌉₊, le_max_left _ _, ?_⟩
  intro N hN A hA
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNceil : (20 * (D : ℝ) ^ 2) ^ (1 / δA) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have h20 : 20 * (D : ℝ) ^ 2 ≤ (N : ℝ) ^ δA := by
    calc 20 * (D : ℝ) ^ 2 = ((20 * (D : ℝ) ^ 2) ^ (1 / δA)) ^ δA := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ (N : ℝ) ^ δA := Real.rpow_le_rpow (by positivity) hNceil hδA.le
  have hNpow : (N : ℝ) ^ (-δA) = ((N : ℝ) ^ δA)⁻¹ := Real.rpow_neg hN0.le _
  have hℓA : 2 * (D : ℝ) ^ 2 * opNorm A ≤ 1 / 10 := by
    have h1 : opNorm A ≤ (20 * (D : ℝ) ^ 2)⁻¹ := by
      refine hA.trans ?_
      rw [hNpow]
      exact inv_anti₀ (by positivity) h20
    calc 2 * (D : ℝ) ^ 2 * opNorm A ≤ 2 * (D : ℝ) ^ 2 * (20 * (D : ℝ) ^ 2)⁻¹ := by gcongr
      _ = 1 / 10 := by field_simp; norm_num
  exact (Reflect_opNorm_lam D N hN1 A).trans hℓA

end Reflect_lam

section Reflect_quant

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- `⟨B^*⟩ = conj ⟨B⟩`. -/
private lemma Reflect_ntr_conjTranspose (B : Matrix ι ι ℂ) : ntr Bᴴ = star (ntr B) := by
  unfold ntr
  rw [Matrix.trace_conjTranspose, star_mul', star_inv₀, star_natCast, mul_comm]

omit [DecidableEq ι] [Nonempty ι] in
/-- `⟨-B⟩ = -⟨B⟩`. -/
private lemma Reflect_ntr_neg (B : Matrix ι ι ℂ) : ntr (-B) = -ntr B := by
  unfold ntr
  rw [Matrix.trace_neg, mul_neg]

/-- The solution of (2.16) [self_m] for `-Λ`: `m_{-Λ}(z) = -conj m_Λ(-conj z)`. -/
private lemma Reflect_mSol_neg {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    mSol (-Λ) z = -star (mSol Λ (-star z)) := by
  have hz1 : 0 < (-star z).im := by simpa using hz
  obtain ⟨him, hntr, hmul⟩ := mSol_spec Λ hΛ (-star z) hz1
  set w := mSol Λ (-star z) with hw
  set Xi := MSol Λ (-star z) with hXi
  have hY : (Λ - (-star z + w) • (1 : Matrix ι ι ℂ))ᴴ = Λ - (-z + star w) • (1 : Matrix ι ι ℂ) := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hΛ.eq, star_add, star_neg,
      star_star]
  have hmul' : Xiᴴ * (Λ - (-z + star w) • (1 : Matrix ι ι ℂ)) = 1 := by
    rw [← hY, ← conjTranspose_mul, hmul, conjTranspose_one]
  have hinv : (-Λ - (z + -star w) • (1 : Matrix ι ι ℂ))⁻¹ = -Xiᴴ := by
    apply Matrix.inv_eq_left_inv
    rw [show -Λ - (z + -star w) • (1 : Matrix ι ι ℂ) =
      -(Λ - (-z + star w) • (1 : Matrix ι ι ℂ)) by module, neg_mul_neg, hmul']
  have hsol : 0 < (-star w).im ∧
      -star w = ntr (-Λ - (z + -star w) • (1 : Matrix ι ι ℂ))⁻¹ := by
    refine ⟨by simpa using him, ?_⟩
    rw [hinv, Reflect_ntr_neg, Reflect_ntr_conjTranspose, ← hntr]
  obtain ⟨him', hntr', -⟩ := mSol_spec (-Λ) hΛ.neg z hz
  exact (mSol_existsUnique (-Λ) hΛ.neg z hz).unique ⟨him', hntr'⟩ hsol


/-- `ρ_{-Λ}(x) = ρ_Λ(-x)` (2.19) [eq:density_rhoN]. -/
lemma Reflect_rho_neg {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (x : ℝ) :
    rho (-Λ) x = rho Λ (-x) := by
  have key : (fun η : ℝ => (mSol (-Λ) ((x : ℂ) + (η : ℂ) * Complex.I)).im) =ᶠ[𝓝[>] (0 : ℝ)]
      fun η : ℝ => (mSol Λ (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : 0 < η := hη
    have him : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη'
    change (mSol (-Λ) ((x : ℂ) + (η : ℂ) * Complex.I)).im = _
    rw [Reflect_mSol_neg hΛ him]
    have : -star ((x : ℂ) + (η : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [this]
    simp
  have hl : limUnder (𝓝[>] (0 : ℝ)) (fun η : ℝ => (mSol (-Λ) ((x : ℂ) + (η : ℂ) * Complex.I)).im) =
      limUnder (𝓝[>] (0 : ℝ))
        (fun η : ℝ => (mSol Λ (((-x : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im) := by
    unfold limUnder
    rw [Filter.map_congr key]
  unfold rho
  exact congrArg (· / Real.pi) hl

/-- `T(x) = ∫_{(x, ∞)} ρ_Λ`. -/
private def Reflect_T (Λ : Matrix ι ι ℂ) (x : ℝ) : ℝ := ∫ E in Set.Ioi x, rho Λ E

/-- `ρ_Λ` vanishes outside `(E⁻, E⁺)` (§2.2, after (2.19) [eq:density_rhoN]). -/
private lemma Reflect_rho_eq_zero {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {x : ℝ} (hx : x ∉ Set.Ioo (Eminus Λ) (Eplus Λ)) : rho Λ x = 0 := by
  obtain ⟨-, hsupp⟩ := rho_support Λ hΛ hℓ
  by_contra h
  have : x ∈ Function.support (rho Λ) := h
  rw [hsupp] at this
  exact hx this

/-- `ρ_Λ > 0` on `(E⁻, E⁺)`. -/
private lemma Reflect_rho_pos {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    {x : ℝ} (hx : x ∈ Set.Ioo (Eminus Λ) (Eplus Λ)) : 0 < rho Λ x := by
  obtain ⟨-, hsupp⟩ := rho_support Λ hΛ hℓ
  have : x ∈ Function.support (rho Λ) := by rw [hsupp]; exact hx
  exact lt_of_le_of_ne ((rho_stieltjes Λ hΛ hℓ).1 x) (Ne.symm this)

/-- `T = 0` to the right of `E⁺`. -/
private lemma Reflect_T_of_ge {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    {x : ℝ} (hx : Eplus Λ ≤ x) : Reflect_T Λ x = 0 := by
  unfold Reflect_T
  refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
  refine Reflect_rho_eq_zero hΛ hℓ fun h => ?_
  have := h.2
  have : x < u := hu
  linarith [h.2]

/-- `T = 1` to the left of `E⁻`. -/
private lemma Reflect_T_of_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    {x : ℝ} (hx : x ≤ Eminus Λ) : Reflect_T Λ x = 1 := by
  unfold Reflect_T
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, (rho_stieltjes Λ hΛ hℓ).2.2.2.1]
  intro u hu
  refine Reflect_rho_eq_zero hΛ hℓ fun h => ?_
  have : ¬ x < u := hu
  push Not at this
  linarith [h.1]

/-- `T(x) - T(y) = ∫_x^y ρ_Λ` for `x ≤ y`. -/
private lemma Reflect_T_sub {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    {x y : ℝ} (hxy : x ≤ y) : Reflect_T Λ x - Reflect_T Λ y = ∫ u in x..y, rho Λ u := by
  unfold Reflect_T
  exact intervalIntegral.integral_Ioi_sub_Ioi (rho_stieltjes Λ hΛ hℓ).2.2.1.integrableOn hxy

/-- `T` is nonincreasing. -/
private lemma Reflect_T_antitone {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) : Antitone (Reflect_T Λ) := by
  intro x y hxy
  have := Reflect_T_sub hΛ hℓ hxy
  have h0 : 0 ≤ ∫ u in x..y, rho Λ u :=
    intervalIntegral.integral_nonneg hxy fun u _ => (rho_stieltjes Λ hΛ hℓ).1 u
  linarith

/-- `T` is continuous. -/
private lemma Reflect_T_continuous {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) : Continuous (Reflect_T Λ) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (rho Λ) volume a b := fun a b =>
    (rho_stieltjes Λ hΛ hℓ).2.1.intervalIntegrable a b
  have hprim := intervalIntegral.continuous_primitive hint 0
  have : Reflect_T Λ = fun x => Reflect_T Λ 0 - ∫ u in (0 : ℝ)..x, rho Λ u := by
    funext x
    rcases le_total 0 x with h | h
    · rw [← Reflect_T_sub hΛ hℓ h]; ring
    · have := Reflect_T_sub hΛ hℓ h
      rw [intervalIntegral.integral_symm]
      linarith
  rw [this]
  exact continuous_const.sub hprim

/-- `T` is strictly decreasing on `[E⁻, E⁺]`. -/
private lemma Reflect_T_strictAnti {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {x y : ℝ} (hx : Eminus Λ ≤ x) (hxy : x < y) (hy : y ≤ Eplus Λ) :
    Reflect_T Λ y < Reflect_T Λ x := by
  have h1 := Reflect_T_sub hΛ hℓ hxy.le
  have hpos : 0 < ∫ u in x..y, rho Λ u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((rho_stieltjes Λ hΛ hℓ).2.1.intervalIntegrable x y) (fun u hu => ?_) hxy
    exact Reflect_rho_pos hΛ hℓ ⟨lt_of_le_of_lt hx hu.1, lt_of_lt_of_le hu.2 hy⟩
  linarith

/-- The level `p ∈ (0,1)` of `T` is taken at a single point `γ`: `{p ≤ T} = (-∞, γ]` and
`{T ≤ p} = [γ, ∞)`. -/
private lemma Reflect_T_level {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ γ : ℝ, (∀ x, p ≤ Reflect_T Λ x ↔ x ≤ γ) ∧ ∀ x, Reflect_T Λ x ≤ p ↔ γ ≤ x := by
  obtain ⟨hlt, -⟩ := rho_support Λ hΛ hℓ
  have hc := Reflect_T_continuous hΛ hℓ
  have h0 := Reflect_T_of_ge hΛ hℓ (le_refl (Eplus Λ))
  have h1 := Reflect_T_of_le hΛ hℓ (le_refl (Eminus Λ))
  obtain ⟨γ, hγ, hTγ⟩ := intermediate_value_Icc' hlt.le hc.continuousOn
    (show p ∈ Set.Icc (Reflect_T Λ (Eplus Λ)) (Reflect_T Λ (Eminus Λ)) by
      rw [h0, h1]; exact ⟨hp0.le, hp1.le⟩)
  have hne1 : γ ≠ Eminus Λ := fun h => by rw [h, h1] at hTγ; linarith
  have hne2 : γ ≠ Eplus Λ := fun h => by rw [h, h0] at hTγ; linarith
  have hγ1 : Eminus Λ < γ := lt_of_le_of_ne hγ.1 (Ne.symm hne1)
  have hγ2 : γ < Eplus Λ := lt_of_le_of_ne hγ.2 hne2
  refine ⟨γ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · by_contra hcon
    push Not at hcon
    rcases le_or_gt (Eplus Λ) x with h | h
    · rw [Reflect_T_of_ge hΛ hℓ h] at hx; linarith
    · have := Reflect_T_strictAnti hΛ hℓ hγ1.le hcon h.le
      linarith
  · have := Reflect_T_antitone hΛ hℓ hx
    linarith
  · by_contra hcon
    push Not at hcon
    rcases lt_or_ge x (Eminus Λ) with h | h
    · rw [Reflect_T_of_le hΛ hℓ h.le] at hx; linarith
    · have := Reflect_T_strictAnti hΛ hℓ h hcon hγ2.le
      linarith
  · have := Reflect_T_antitone hΛ hℓ hx
    linarith

/-- The reflection of quantiles: for Hermitian `Λ` with `‖Λ‖ ≤ 1/10`, `1 ≤ k ≤ Mc` and the
`γ_k` of (2.20) [eq:gammak], `γ_{Mc+1-k}(ρ_{-Λ}) = -γ_k(ρ_Λ)`. -/
lemma Reflect_quant_neg {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (Mc k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Mc) :
    quant (rho (-Λ)) Mc (Mc + 1 - k) = -quant (rho Λ) Mc k := by
  have hMc : (0 : ℝ) < Mc := by exact_mod_cast (show 0 < Mc by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkM : (k : ℝ) ≤ Mc := by exact_mod_cast hk
  set p : ℝ := ((k : ℝ) - 1 / 2) / Mc with hp
  have hp0 : 0 < p := by rw [hp]; apply div_pos <;> linarith
  have hp1 : p < 1 := by rw [hp, div_lt_one hMc]; linarith
  have hkc : ((Mc + 1 - k : ℕ) : ℝ) = (Mc : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hp' : (((Mc + 1 - k : ℕ) : ℝ) - 1 / 2) / Mc = 1 - p := by
    rw [hp, hkc]; field_simp; ring
  obtain ⟨γ, hγ1, hγ2⟩ := Reflect_T_level hΛ hℓ hp0 hp1
  have hint := (rho_stieltjes Λ hΛ hℓ).2.2.1
  have hmass := (rho_stieltjes Λ hΛ hℓ).2.2.2.1
  have hq1 : quant (rho Λ) Mc k = γ := by
    unfold quant
    have : {x : ℝ | ((k : ℝ) - 1 / 2) / Mc ≤ ∫ E in Set.Ioi x, rho Λ E} = Set.Iic γ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      rw [← hp]
      exact hγ1 x
    rw [this]
    exact csSup_Iic
  have hrho : rho (-Λ) = fun t => rho Λ (-t) := funext (Reflect_rho_neg hΛ)
  have hflip : ∀ x : ℝ, ∫ E in Set.Ioi x, rho (-Λ) E = 1 - Reflect_T Λ (-x) := by
    intro x
    rw [hrho]
    change ∫ E in Set.Ioi x, rho Λ (-E) = _
    rw [integral_comp_neg_Ioi]
    have := integral_add_compl (μ := volume) (measurableSet_Iic (a := -x)) hint
    rw [Set.compl_Iic, hmass] at this
    unfold Reflect_T
    linarith
  have hq2 : quant (rho (-Λ)) Mc (Mc + 1 - k) = -γ := by
    unfold quant
    have : {x : ℝ | (((Mc + 1 - k : ℕ) : ℝ) - 1 / 2) / Mc ≤ ∫ E in Set.Ioi x, rho (-Λ) E} =
        Set.Iic (-γ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      rw [hp', hflip x]
      constructor
      · intro h
        have := (hγ2 (-x)).1 (by linarith)
        linarith
      · intro h
        have := (hγ2 (-x)).2 (by linarith)
        linarith
    rw [this]
    exact csSup_Iic
  rw [hq1, hq2]

end Reflect_quant

/-- The semicircle quantiles reflect: `γ_{Mc+1-k}^{sc} = -γ_k^{sc}` for `1 ≤ k ≤ Mc`, from the case
`Λ = 0` of `Reflect_quant_neg` (`ρ_0 = ρ_sc`, Definition 2.7 [defn_Mm]). -/
lemma Reflect_quant_sc (Mc k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Mc) :
    quant rhoSc Mc (Mc + 1 - k) = -quant rhoSc Mc k := by
  have h0 : opNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 1 / 10 := by
    unfold opNorm; simp
  have := Reflect_quant_neg (Λ := (0 : Matrix (Fin 1) (Fin 1) ℂ)) isHermitian_zero h0 Mc k hk1 hk
  rwa [neg_zero, (rho_zero (ι := Fin 1)).2.1] at this

/-- The block-diagonal matrix `H` is Hermitian. -/
private lemma Reflect_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  have : blockH D N w = HLam D N 0 w := by
    unfold HLam
    have : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
      ext p q
      simp [lam]
    rw [this, add_zero]
  rw [this]
  exact HLam_isHermitian D N 0 w

/-- The shift `X` of Theorem 2.5 [theorem_localized_eigenvalue] changes sign under the
reflection. -/
private lemma Reflect_shiftX_neg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ D * N) (hΛ : opNorm (lam D N A) ≤ 1 / 10) (w : Fin D → Coords N) :
    shiftX D N (-A) (D * N + 1 - k) (-w) = -shiftX D N A k w := by
  have hDN : 0 < D * N := by omega
  have : Nonempty (Idx D N) := by
    have hD : D ≠ 0 := fun h => by simp [h] at hDN
    have hN : N ≠ 0 := fun h => by simp [h] at hDN
    exact ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, Nat.pos_of_ne_zero hN⟩)⟩
  unfold shiftX
  rw [Reflect_HLam_neg, Reflect_blockH_neg, Reflect_lam_neg,
    Reflect_eigK_neg D N _ (HLam_isHermitian D N A w) k hk1 hk,
    Reflect_eigK_neg D N _ (Reflect_blockH_isHermitian D N w) k hk1 hk,
    Reflect_quant_neg (Reflect_lam_isHermitian D N A) hΛ (D * N) k hk1 hk,
    Reflect_quant_sc (D * N) k hk1 hk]
  ring

/-- Reflection of the Theorem 2.5 bound for events in `|X|`. -/
private lemma Reflect_eval_bound (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N)
    (hΛ : opNorm (lam D N A) ≤ 1 / 10) (Q : ℝ → Prop) (b : ENNReal)
    (h : blockLaw D N (Reflect_negLaws L) {w : Fin D → Coords N |
      Q |shiftX D N (-A) (D * N + 1 - k) w|} ≤ b) :
    blockLaw D N L {w : Fin D → Coords N | Q |shiftX D N A k w|} ≤ b := by
  have : {w : Fin D → Coords N | Q |shiftX D N A k w|} = (fun w : Fin D → Coords N => -w) ⁻¹'
      {w : Fin D → Coords N | Q |shiftX D N (-A) (D * N + 1 - k) w|} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Reflect_shiftX_neg D N A k hk1 hk hΛ, abs_neg]
  rw [this, Reflect_blockLaw_preimage]
  exact h

/-- The pairing of Theorem 2.5 reflects: for `ev' i = -ev (Mc + 1 - i)` (`1 ≤ i ≤ Mc`) the
sum over distinct indices of `O(-·)` at `ev'` and `-γ` is the sum of `O` at `ev` and `γ`. -/
private lemma Reflect_corrPairing (Mc n : ℕ) (s γ : ℝ) (O : (Fin n → ℝ) → ℝ) (ev ev' : ℕ → ℝ)
    (hev : ∀ i, 1 ≤ i → i ≤ Mc → ev' i = -ev (Mc + 1 - i)) :
    corrPairing Mc n s (-γ) (fun x => O (-x)) ev' = corrPairing Mc n s γ O ev := by
  unfold corrPairing
  rw [← Equiv.sum_comp (Equiv.embeddingCongr (Equiv.refl (Fin n)) (Fin.revPerm (n := Mc)))]
  refine Finset.sum_congr rfl fun f _ => ?_
  change O (-fun j => s * (ev' (((Equiv.refl (Fin n)).embeddingCongr Fin.revPerm f) j + 1) -
    -γ)) = _
  congr 1
  funext j
  have hj := (f j).isLt
  have e : (((Equiv.refl (Fin n)).embeddingCongr Fin.revPerm f) j : ℕ) =
      Mc - ((f j : ℕ) + 1) := by
    simp [Fin.val_rev]
  have h1 := hev (Mc - ((f j : ℕ) + 1) + 1) (by omega) (by omega)
  have h2 : Mc + 1 - (Mc - ((f j : ℕ) + 1) + 1) = (f j : ℕ) + 1 := by omega
  rw [Pi.neg_apply, e, h1, h2]
  ring

/-- `λ_i(-X) = -λ_{DN+1-i}(X)` for a Hermitian `X` on `Idx D N`, `1 ≤ i ≤ DN`. -/
private lemma Reflect_eigK_neg' (D N : ℕ) (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ D * N) : eigK (-X) i = -eigK X (D * N + 1 - i) := by
  have := Reflect_eigK_neg D N X hX (D * N + 1 - i) (by omega) (by omega)
  rwa [show D * N + 1 - (D * N + 1 - i) = i by omega] at this

/-- The pairing of `H_Λ` at `γ_k` for `(A, w)` is the pairing of `O(-·)` at `γ_{DN+1-k}` for
`(-A, -w)`. -/
private lemma Reflect_corr_one (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ D * N) (hΛ : opNorm (lam D N A) ≤ 1 / 10) (n : ℕ) (O : (Fin n → ℝ) → ℝ) (s : ℝ)
    (w : Fin D → Coords N) :
    corrPairing (D * N) n s (quant (rho (lam D N (-A))) (D * N) (D * N + 1 - k))
        (fun x => O (-x)) (eigK (HLam D N (-A) (-w))) =
      corrPairing (D * N) n s (quant (rho (lam D N A)) (D * N) k) O (eigK (HLam D N A w)) := by
  have hDN : 0 < D * N := by omega
  have : Nonempty (Idx D N) := by
    have hD : D ≠ 0 := fun h => by simp [h] at hDN
    have hN : N ≠ 0 := fun h => by simp [h] at hDN
    exact ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, Nat.pos_of_ne_zero hN⟩)⟩
  rw [Reflect_lam_neg, Reflect_quant_neg (Reflect_lam_isHermitian D N A) hΛ (D * N) k hk1 hk]
  refine Reflect_corrPairing (D * N) n s _ O _ _ fun i hi1 hi => ?_
  rw [Reflect_HLam_neg]
  exact Reflect_eigK_neg' D N _ (HLam_isHermitian D N A w) i hi1 hi

/-- The pairing of `H` at `γ_k^{sc}` for `w` is the pairing of `O(-·)` at `γ_{DN+1-k}^{sc}` for
`-w`. -/
private lemma Reflect_corr_two (D N : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N) (n : ℕ)
    (O : (Fin n → ℝ) → ℝ) (s : ℝ) (w : Fin D → Coords N) :
    corrPairing (D * N) n s (quant rhoSc (D * N) (D * N + 1 - k))
        (fun x => O (-x)) (eigK (blockH D N (-w))) =
      corrPairing (D * N) n s (quant rhoSc (D * N) k) O (eigK (blockH D N w)) := by
  rw [Reflect_quant_sc (D * N) k hk1 hk]
  refine Reflect_corrPairing (D * N) n s _ O _ _ fun i hi1 hi => ?_
  rw [Reflect_blockH_neg]
  exact Reflect_eigK_neg' D N _ (Reflect_blockH_isHermitian D N w) i hi1 hi

/-- Reflection of the Theorem 2.5 comparison of correlation functions. -/
private lemma Reflect_corr_bound (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N)
    (hΛ : opNorm (lam D N A) ≤ 1 / 10) (n : ℕ) (O : (Fin n → ℝ) → ℝ) (s b : ℝ)
    (h : |(∫ w, corrPairing (D * N) n s (quant (rho (lam D N (-A))) (D * N) (D * N + 1 - k))
            (fun x => O (-x)) (eigK (HLam D N (-A) w)) ∂(blockLaw D N (Reflect_negLaws L))) -
        (∫ w, corrPairing (D * N) n s (quant rhoSc (D * N) (D * N + 1 - k))
            (fun x => O (-x)) (eigK (blockH D N w)) ∂(blockLaw D N (Reflect_negLaws L)))| ≤ b) :
    |(∫ w, corrPairing (D * N) n s (quant (rho (lam D N A)) (D * N) k) O
          (eigK (HLam D N A w)) ∂(blockLaw D N L)) -
      (∫ w, corrPairing (D * N) n s (quant rhoSc (D * N) k) O
          (eigK (blockH D N w)) ∂(blockLaw D N L))| ≤ b := by
  rw [Reflect_blockLaw_integral, Reflect_blockLaw_integral] at h
  simp only [Reflect_corr_one D N A k hk1 hk hΛ n O s, Reflect_corr_two D N k hk1 hk n O s] at h
  exact h

/-- Reflection of the Theorem 2.4 bound: a bound for the event of `(-A, DN + 1 - k)` under the
reflected laws is a bound for the event of `(A, k)`. -/
private lemma Reflect_evec_bound (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N)
    (P : (Idx D N → ℂ) → Prop) (b : ENNReal)
    (h : blockLaw D N (Reflect_negLaws L) {w : Fin D → Coords N | ∃ u,
      IsUnitEigvec (HLam D N (-A) w) (eigK (HLam D N (-A) w) (D * N + 1 - k)) u ∧ P u} ≤ b) :
    blockLaw D N L {w : Fin D → Coords N | ∃ u, IsUnitEigvec (HLam D N A w)
      (eigK (HLam D N A w) k) u ∧ P u} ≤ b := by
  rw [Reflect_evec_set D N A k hk1 hk P, Reflect_blockLaw_preimage]
  exact h

/-- The reflection `h ↦ -h`, `A ↦ -A`, `k ↦ DN + 1 - k` for Theorem 2.4
[theorem_localized_eigenvector_localization]: the case `2k ≤ DN + 1` gives every `k ≤ DN`. -/
theorem localized_evec_reflect (h : LocalizedEvecHalf) : LocalizedEvecStatement := by
  intro D hD δA εA hδA hεA C
  obtain ⟨h1, h2⟩ := h D hD δA εA hδA hεA C
  refine ⟨fun ε hε hε2 => ?_, ?_⟩
  · obtain ⟨ε₀, hε₀, N₀, hN₀⟩ := h1 ε hε hε2
    refine ⟨ε₀, hε₀, N₀, fun N hN L A hA k hk1 hk hHS => ?_⟩
    by_cases hk2 : 2 * k ≤ D * N + 1
    · exact hN₀ N hN L A hA k hk1 hk2 hHS
    · have := hN₀ N hN (Reflect_negLaws L) (-A) (by rwa [Reflect_opNorm_neg]) (D * N + 1 - k)
        (by omega) (by omega)
        (by rwa [Reflect_hsNorm_neg, Reflect_rk D N k (by omega)])
      rw [Reflect_hsNorm_neg, Reflect_rk D N k (by omega)] at this
      exact Reflect_evec_bound D N L A k hk1 hk _ _ this
  · obtain ⟨c, hc, N₀, hN₀⟩ := h2
    refine ⟨c, hc, N₀, fun N hN L A hA k hk1 hk hHS => ?_⟩
    by_cases hk2 : 2 * k ≤ D * N + 1
    · exact hN₀ N hN L A hA k hk1 hk2 hHS
    · have := hN₀ N hN (Reflect_negLaws L) (-A) (by rwa [Reflect_opNorm_neg]) (D * N + 1 - k)
        (by omega) (by omega)
        (by rwa [Reflect_hsNorm_neg, Reflect_rk D N k (by omega)])
      exact Reflect_evec_bound D N L A k hk1 hk _ _ this

/-- The reflection `h ↦ -h`, `A ↦ -A`, `k ↦ DN + 1 - k` for Theorem 2.5
[theorem_localized_eigenvalue]: the case `2k ≤ DN + 1` gives every `k ≤ DN`, the test function
`O` being replaced by `x ↦ O(-x)`. -/
theorem localized_eval_reflect (h : LocalizedEvalHalf) : LocalizedEvalStatement := by
  intro D hD δA εA hδA hεA C
  obtain ⟨h1, h2, h3⟩ := h D hD δA εA hδA hεA C
  obtain ⟨N₁, hN₁, hsmall⟩ := Reflect_lam_small D (by omega) δA hδA
  refine ⟨fun ε ε₀ hε hε₀ hεε => ?_, ?_, fun n O hO hOc => ?_⟩
  · obtain ⟨N₀, hN₀⟩ := h1 ε ε₀ hε hε₀ hεε
    refine ⟨max N₀ N₁, fun N hN L A hA k hk1 hk hHS => ?_⟩
    have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hΛ := hsmall N (le_trans (le_max_right _ _) hN) A hA
    by_cases hk2 : 2 * k ≤ D * N + 1
    · exact hN₀ N hNN₀ L A hA k hk1 hk2 hHS
    · have := hN₀ N hNN₀ (Reflect_negLaws L) (-A) (by rwa [Reflect_opNorm_neg]) (D * N + 1 - k)
        (by omega) (by omega)
        (by rwa [Reflect_hsNorm_neg, Reflect_rk D N k (by omega)])
      rw [Reflect_hsNorm_neg] at this
      exact Reflect_eval_bound D N L A k hk1 hk hΛ
        (fun t => (N : ℝ) ^ (-1 + ε) * hsNorm A < t) _ this
  · obtain ⟨c, hc, N₀, hN₀⟩ := h2
    refine ⟨c, hc, max N₀ N₁, fun N hN L A hA k hk1 hk hHS => ?_⟩
    have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hΛ := hsmall N (le_trans (le_max_right _ _) hN) A hA
    by_cases hk2 : 2 * k ≤ D * N + 1
    · exact hN₀ N hNN₀ L A hA k hk1 hk2 hHS
    · have := hN₀ N hNN₀ (Reflect_negLaws L) (-A) (by rwa [Reflect_opNorm_neg]) (D * N + 1 - k)
        (by omega) (by omega)
        (by rwa [Reflect_hsNorm_neg, Reflect_rk D N k (by omega)])
      rw [Reflect_rk D N k (by omega)] at this
      exact Reflect_eval_bound D N L A k hk1 hk hΛ
        (fun t => (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N k ^ (-(1 / 3 : ℝ)) ≤ t) _ this
  · obtain ⟨c₁, hc₁, N₁', hN₁'⟩ := h3 n O hO hOc
    obtain ⟨c₂, hc₂, N₂', hN₂'⟩ := h3 n (fun x => O (-x)) (hO.comp contDiff_neg)
      (hOc.comp_homeomorph (Homeomorph.neg (Fin n → ℝ)))
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max (max N₁' N₂') N₁, fun N hN L A hA k hk1 hk hHS => ?_⟩
    have hNa : N₁' ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNb : N₂' ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hΛ := hsmall N (le_trans (le_max_right _ _) hN) A hA
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast le_trans hN₁ (le_trans (le_max_right _ _) hN)
    by_cases hk2 : 2 * k ≤ D * N + 1
    · refine (hN₁' N hNa L A hA k hk1 hk2 hHS).trans ?_
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left c₁ c₂])
    · have := hN₂' N hNb (Reflect_negLaws L) (-A) (by rwa [Reflect_opNorm_neg]) (D * N + 1 - k)
        (by omega) (by omega)
        (by rwa [Reflect_hsNorm_neg, Reflect_rk D N k (by omega)])
      rw [Reflect_rk D N k (by omega)] at this
      refine (Reflect_corr_bound D N L A k hk1 hk hΛ n O _ _ this).trans ?_
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_right c₁ c₂])

end RBMTransitionEdge

end
