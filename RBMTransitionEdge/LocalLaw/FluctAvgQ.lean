module

public import RBMTransitionEdge.LocalLaw.ResPolyDer
public import RBMTransitionEdge.LocalLaw.FluctPrelim

@[expose] public section

/-!
# The matrix `Q` of fluctuation averaging

The vectors of the averaged expansion, the matrix `Q` through which the derivative of
`⟨B H̲G⟩` of (2.30) [eq:HGline] in one entry is written, the good event of the averaged moment
inequalities, `Q` as a resolvent polynomial entrywise, and the bound on the derivatives of `Q`
on the good event.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The vectors of the averaged expansion: the standard basis `e_k` and `B e_k`, `B^* e_k`,
`Λ e_k`. -/
def avgVecs (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) : Finset (Idx D N → ℂ) :=
  Finset.univ.image (fun k => Pi.single k 1) ∪ Finset.univ.image (fun k => B *ᵥ Pi.single k 1) ∪
    Finset.univ.image (fun k => Bᴴ *ᵥ Pi.single k 1) ∪
      Finset.univ.image (fun k => Λ *ᵥ Pi.single k 1)

/-- The matrix `Q = (DN)⁻¹ (G B H̲G + Σ_a c_a G E_a G)`, `c_a = θ N⁻¹ tr(E_a G B)
+ (1 - θ)(DN)⁻¹ tr(G B)`, so that the derivative of `⟨B H̲G⟩` ((2.30) [eq:HGline]) in the
direction `E_{ij}` is `(DN)⁻¹ (G B)_{ji} - Q_{ji}`. -/
def qMat (D N : ℕ) (θ : ℝ) (H Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  ((D : ℂ) * N)⁻¹ • (res (H + Λ) z * B * hgUnder D N θ H Λ z +
    ∑ a, ((θ : ℂ) * (N : ℂ)⁻¹ * (Ea D N a * res (H + Λ) z * B).trace +
      ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ * (res (H + Λ) z * B).trace) •
        (res (H + Λ) z * Ea D N a * res (H + Λ) z))

/-- The good event of the averaged moment inequalities: the good event on `avgVecs`, and
`|Q_{kl}| ≤ λ_Q` for all entries. -/
def avgGood (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (Γ Υ bQ : ℝ) :
    Set (Idx D N → Idx D N → ℂ) :=
  goodSet Λ z (avgVecs D N Λ B) Γ Υ ∩
    {h | ∀ k l, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ≤ bQ}


/-! ### Helpers: the identity `H G = I - (Λ - z) G`, the entries of `S_θ`, the entries of `Q` -/

/-- `H̲G = I - (Λ - z) G + S_θ(G) G` for Hermitian `H`, `Λ` and `Im z > 0`, because
`(H + Λ - z) G = I` ((2.30) [eq:HGline] with the profile `S_θ`). -/
private lemma FAQ_hgUnder_eq (D N : ℕ) (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ)
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

/-- The coefficient `θ N⁻¹ 1(r, m in the same block) + (1 - θ)(DN)⁻¹` of the entries of `S_θ`. -/
private def FAQ_kap (D N : ℕ) (θ : ℝ) (r m : Idx D N) : ℂ :=
  (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = m.1 then 1 else 0) + ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹

/-- The coefficient `κ` is symmetric. -/
private lemma FAQ_kap_comm (D N : ℕ) (θ : ℝ) (r m : Idx D N) :
    FAQ_kap D N θ r m = FAQ_kap D N θ m r := by
  unfold FAQ_kap
  simp only [eq_comm (a := r.1)]

/-- The normalized trace as a sum over the diagonal. -/
private lemma FAQ_ntr_eq (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr M = ((D : ℂ) * N)⁻¹ * ∑ r, M r r := by
  simp [ntr, Matrix.trace, Fintype.card_prod]

/-- `S_θ(R)` is the diagonal matrix with entries `Σ_r κ(r, p) R_{rr}`. -/
private lemma FAQ_sTheta_apply (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ)
    (p q : Idx D N) :
    sTheta D N θ R p q = if p = q then ∑ r, FAQ_kap D N θ r p * R r r else 0 := by
  have hD : (D : ℂ) ≠ 0 := by
    have : 0 < D := p.1.pos
    exact_mod_cast this.ne'
  have hDn : (D : ℂ) * ((D : ℂ) * N)⁻¹ = (N : ℂ)⁻¹ := by
    field_simp
  have hblk : ∀ a : Fin D, (D : ℂ) * ntr (R * Ea D N a) =
      (N : ℂ)⁻¹ * ∑ r, (if r.1 = a then R r r else 0) := by
    intro a
    rw [FAQ_ntr_eq]
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
    rw [e1, hblk, FAQ_ntr_eq]
    simp only [FAQ_kap, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∀ r : Idx D N, (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = p.1 then (1 : ℂ) else 0) * R r r =
        (θ : ℂ) * ((N : ℂ)⁻¹ * if r.1 = p.1 then R r r else 0) := by
      intro r
      split_ifs <;> ring
    simp only [e2]
    push_cast
    simp only [mul_assoc]
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

/-- The entries of `G E_a`. -/
private lemma FAQ_GEa_apply (D N : ℕ) (G : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D)
    (k m : Idx D N) : (G * Ea D N a) k m = if m.1 = a then G k m else 0 := by
  simp only [Ea, Matrix.mul_diagonal]
  split_ifs <;> simp

/-- The entries of `(G E_a G)`. -/
private lemma FAQ_GEaG_apply (D N : ℕ) (G : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D)
    (k l : Idx D N) :
    (G * Ea D N a * G) k l = ∑ m, if m.1 = a then G k m * G m l else 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [FAQ_GEa_apply]
  split_ifs <;> simp

/-- The block trace `tr(E_a M)`. -/
private lemma FAQ_trEa (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) :
    (Ea D N a * M).trace = ∑ r, if r.1 = a then M r r else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Ea, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

/-- The entries of `Q` in terms of the entries of `G`, `G B` and `Λ G`: the expansion of
`G B H̲G + Σ_a c_a G E_a G` through `H̲G = I - (Λ - z) G + S_θ(G) G`. -/
private lemma FAQ_qMat_apply (D N : ℕ) (θ : ℝ) (H Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (k l : Idx D N) :
    qMat D N θ H Λ B z k l = ((D : ℂ) * N)⁻¹ *
      ((res (H + Λ) z * B) k l - (∑ m, (res (H + Λ) z * B) k m * (Λ * res (H + Λ) z) m l) +
        z * (∑ m, (res (H + Λ) z * B) k m * res (H + Λ) z m l) +
        (∑ m, ∑ r, FAQ_kap D N θ r m * res (H + Λ) z r r *
          ((res (H + Λ) z * B) k m * res (H + Λ) z m l)) +
        (∑ m, ∑ r, FAQ_kap D N θ r m * (res (H + Λ) z * B) r r *
          (res (H + Λ) z k m * res (H + Λ) z m l))) := by
  set G := res (H + Λ) z with hG
  have hD : (D : ℂ) ≠ 0 := by
    have : 0 < D := k.1.pos
    exact_mod_cast this.ne'
  have hYm : (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G + sTheta D N θ G * G) =
      1 - Λ * G + z • G + sTheta D N θ G * G := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hS : ∀ m, (sTheta D N θ G * G) m l = (∑ r, FAQ_kap D N θ r m * G r r) * G m l := by
    intro m
    simp only [Matrix.mul_apply, FAQ_sTheta_apply, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have h1 : (G * B * hgUnder D N θ H Λ z) k l = (G * B) k l -
      (∑ m, (G * B) k m * (Λ * G) m l) + z * (∑ m, (G * B) k m * G m l) +
      (∑ m, ∑ r, FAQ_kap D N θ r m * G r r * ((G * B) k m * G m l)) := by
    rw [FAQ_hgUnder_eq D N θ H Λ hH hΛ z hz, ← hG, hYm]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Matrix.mul_apply (M := G * B) (N := Λ * G), Matrix.mul_apply (M := G * B) (N := G),
      Matrix.mul_apply (M := G * B) (N := sTheta D N θ G * G)]
    simp only [hS]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hc : ∀ a : Fin D, ((θ : ℂ) * (N : ℂ)⁻¹ * (Ea D N a * G * B).trace +
      ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ * (G * B).trace) =
        ∑ r, ((θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = a then 1 else 0) +
          ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹) * (G * B) r r := by
    intro a
    rw [Matrix.mul_assoc, FAQ_trEa]
    simp only [add_mul, Finset.sum_add_distrib, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  have h2 : ∑ a, ((θ : ℂ) * (N : ℂ)⁻¹ * (Ea D N a * G * B).trace +
      ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ * (G * B).trace) * (G * Ea D N a * G) k l =
      ∑ m, ∑ r, FAQ_kap D N θ r m * (G * B) r r * (G k m * G m l) := by
    have e : ∀ a : Fin D, ((θ : ℂ) * (N : ℂ)⁻¹ * (Ea D N a * G * B).trace +
        ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ * (G * B).trace) * (G * Ea D N a * G) k l =
        ∑ m, if m.1 = a then (∑ r, ((θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = a then 1 else 0) +
          ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹) * (G * B) r r) * (G k m * G m l) else 0 := by
      intro a
      rw [hc a, FAQ_GEaG_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, Finset.sum_mul, FAQ_kap]
  unfold qMat
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, smul_eq_mul]
  rw [h1, h2]

/-! ### Helpers: sums of resolvent polynomials, the values of the forms -/

/-- The polynomial `Σ_x g(x)` over the index set, as a concatenation. -/
private def FAQ_sum {D N : ℕ} (g : Idx D N → ResPoly D N) : ResPoly D N :=
  (Finset.univ : Finset (Idx D N)).toList.flatMap g

/-- The value of a concatenation over a list. -/
private lemma FAQ_eval_flatMap {D N : ℕ} {ι : Type*} (L : List ι) (g : ι → ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (L.flatMap g) h = (L.map fun x => resPolyEval (g x) h).sum := by
  induction L with
  | nil => simp [resPolyEval]
  | cons x L ih => simp only [List.flatMap_cons, resPolyEval_append, ih, List.map_cons,
      List.sum_cons]

/-- The value of a sum of polynomials over the index set. -/
private lemma FAQ_eval_sum {D N : ℕ} (g : Idx D N → ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FAQ_sum g) h = ∑ x, resPolyEval (g x) h := by
  unfold FAQ_sum
  rw [FAQ_eval_flatMap, Finset.sum_map_toList]

/-- `A resolvent polynomial's term lists are concatenated by the derivative. -/
private lemma FAQ_resPolyD_flatMap {D N : ℕ} {ι : Type*} (a b : Idx D N) (c : ℂ) (L : List ι)
    (g : ι → ResPoly D N) :
    resPolyD a b c (L.flatMap g) = L.flatMap (fun x => resPolyD a b c (g x)) := by
  unfold resPolyD
  rw [List.flatMap_assoc]

/-- The derivative of a concatenation. -/
private lemma FAQ_resPolyD_append {D N : ℕ} (a b : Idx D N) (c : ℂ) (P Q : ResPoly D N) :
    resPolyD a b c (P ++ Q) = resPolyD a b c P ++ resPolyD a b c Q := by
  unfold resPolyD
  rw [List.flatMap_append]

/-- The derivative of a sum over the index set. -/
private lemma FAQ_resPolyD_sum {D N : ℕ} (a b : Idx D N) (c : ℂ) (g : Idx D N → ResPoly D N) :
    resPolyD a b c (FAQ_sum g) = FAQ_sum (fun x => resPolyD a b c (g x)) :=
  FAQ_resPolyD_flatMap a b c _ g

/-- The star of a standard basis vector. -/
private lemma FAQ_star_single {D N : ℕ} (p : Idx D N) :
    star (Pi.single p (1 : ℂ) : Idx D N → ℂ) = Pi.single p 1 := by
  funext s
  by_cases h : s = p <;> simp [h]

/-- The `p`-th entry of the `q`-th column. -/
private lemma FAQ_mulVec_single {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ) (q p : Idx D N) :
    (M *ᵥ Pi.single q (1 : ℂ)) p = M p q := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The form `e_p^* G e_q` is the entry `G_{pq}`. -/
private lemma FAQ_f_ee {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Pi.single p 1, Pi.single q 1, Λ, z) h = res (Matrix.of h + Λ) z p q := by
  unfold resFactorEval
  simp only
  rw [FAQ_star_single, single_dotProduct, one_mul, FAQ_mulVec_single]

/-- The form `e_p^* G (M e_q)` is the entry `(G M)_{pq}`. -/
private lemma FAQ_f_eM {D N : ℕ} (Λ M : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Pi.single p 1, M *ᵥ Pi.single q 1, Λ, z) h =
      (res (Matrix.of h + Λ) z * M) p q := by
  unfold resFactorEval
  simp only
  rw [FAQ_star_single, single_dotProduct, one_mul, Matrix.mulVec_mulVec, FAQ_mulVec_single]

/-- The form `(Λ e_p)^* G e_q` is the entry `(Λ G)_{pq}` for Hermitian `Λ`. -/
private lemma FAQ_f_Le {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Λ *ᵥ Pi.single p 1, Pi.single q 1, Λ, z) h =
      (Λ * res (Matrix.of h + Λ) z) p q := by
  unfold resFactorEval
  simp only
  rw [Matrix.star_mulVec, hΛ.eq, ← Matrix.dotProduct_mulVec, FAQ_star_single, single_dotProduct,
    one_mul, Matrix.mulVec_mulVec, FAQ_mulVec_single]

/-- The one-entry slice of a Hermitian array is Hermitian. -/
private lemma FAQ_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

/-! ### The resolvent polynomial of `Q_{kl}` -/

/-- The first group of the polynomial of `Q_{kl}`: `(DN)⁻¹ (G B)_{kl}`. -/
private def FAQ_P1 (D N : ℕ) (B : Matrix (Idx D N) (Idx D N) ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (k l : Idx D N) : ResPoly D N :=
  [(((D : ℂ) * N)⁻¹, [(Pi.single k 1, B *ᵥ Pi.single l 1, Λ, z)])]

/-- The second group: `-(DN)⁻¹ (G B Λ G)_{kl}`. -/
private def FAQ_P2 (D N : ℕ) (B : Matrix (Idx D N) (Idx D N) ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (k l : Idx D N) : ResPoly D N :=
  FAQ_sum (fun m => [(-((D : ℂ) * N)⁻¹,
    [(Pi.single k 1, B *ᵥ Pi.single m 1, Λ, z), (Λ *ᵥ Pi.single m 1, Pi.single l 1, Λ, z)])])

/-- The third group: `z (DN)⁻¹ (G B G)_{kl}`. -/
private def FAQ_P3 (D N : ℕ) (B : Matrix (Idx D N) (Idx D N) ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (k l : Idx D N) : ResPoly D N :=
  FAQ_sum (fun m => [(z * ((D : ℂ) * N)⁻¹,
    [(Pi.single k 1, B *ᵥ Pi.single m 1, Λ, z), (Pi.single m 1, Pi.single l 1, Λ, z)])])

/-- The fourth group for one `r`: the terms of `(DN)⁻¹ (G B S_θ(G) G)_{kl}` with the diagonal
entry `G_{rr}`. -/
private def FAQ_P4r (D N : ℕ) (θ : ℝ) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l r : Idx D N) : ResPoly D N :=
  FAQ_sum (fun m => [(((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r m,
    [(Pi.single k 1, B *ᵥ Pi.single m 1, Λ, z), (Pi.single m 1, Pi.single l 1, Λ, z),
      (Pi.single r 1, Pi.single r 1, Λ, z)])])

/-- The fifth group for one `r`: the terms of `(DN)⁻¹ Σ_a c_a (G E_a G)_{kl}` with the form
`e_r^* G B e_r`. -/
private def FAQ_P5r (D N : ℕ) (θ : ℝ) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l r : Idx D N) : ResPoly D N :=
  FAQ_sum (fun m => [(((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r m,
    [(Pi.single k 1, Pi.single m 1, Λ, z), (Pi.single m 1, Pi.single l 1, Λ, z),
      (Pi.single r 1, B *ᵥ Pi.single r 1, Λ, z)])])

/-- The resolvent polynomial of `Q_{kl}`: the five groups of the expansion
`(DN)⁻¹ (G B - G B Λ G + z G B G + G B S_θ(G) G + Σ_a c_a G E_a G)_{kl}` in forms
`x^* G y` with `x, y ∈ {e_p, B e_p, Λ e_p}`. -/
private def FAQ_PQ (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (k l : Idx D N) : ResPoly D N :=
  FAQ_P1 D N B Λ z k l ++ FAQ_P2 D N B Λ z k l ++ FAQ_P3 D N B Λ z k l ++
    FAQ_sum (FAQ_P4r D N θ B Λ z k l) ++ FAQ_sum (FAQ_P5r D N θ B Λ z k l)

/-- On Hermitian arrays the polynomial `FAQ_PQ` takes the value `Q_{kl}`. -/
private lemma FAQ_eval_PQ (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (k l : Idx D N)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    resPolyEval (FAQ_PQ D N θ Λ B z k l) h = qMat D N θ (Matrix.of h) Λ B z k l := by
  rw [FAQ_qMat_apply D N θ (Matrix.of h) Λ B hh hΛ z hz k l]
  simp only [FAQ_PQ, FAQ_P1, FAQ_P2, FAQ_P3, FAQ_P4r, FAQ_P5r, resPolyEval_append, FAQ_eval_sum]
  simp only [resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, add_zero, mul_one, FAQ_f_ee, FAQ_f_eM, FAQ_f_Le Λ hΛ]
  set G := res (Matrix.of h + Λ) z with hG
  have e2 : ∑ x, -((D : ℂ) * N)⁻¹ * ((G * B) k x * (Λ * G) x l) =
      -(((D : ℂ) * N)⁻¹ * ∑ m, (G * B) k m * (Λ * G) m l) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e3 : ∑ x, z * ((D : ℂ) * N)⁻¹ * ((G * B) k x * G x l) =
      ((D : ℂ) * N)⁻¹ * (z * ∑ m, (G * B) k m * G m l) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e4 : ∑ x, ∑ x_1, ((D : ℂ) * N)⁻¹ * FAQ_kap D N θ x x_1 *
      ((G * B) k x_1 * (G x_1 l * G x x)) = ((D : ℂ) * N)⁻¹ *
        ∑ m, ∑ r, FAQ_kap D N θ r m * G r r * ((G * B) k m * G m l) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have e5 : ∑ x, ∑ x_1, ((D : ℂ) * N)⁻¹ * FAQ_kap D N θ x x_1 *
      (G k x_1 * (G x_1 l * (G * B) x x)) = ((D : ℂ) * N)⁻¹ *
        ∑ m, ∑ r, FAQ_kap D N θ r m * (G * B) r r * (G k m * G m l) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [e2, e3, e4, e5]
  ring

/-- Membership in a sum of polynomials. -/
private lemma FAQ_mem_sum {D N : ℕ} (g : Idx D N → ResPoly D N) (t : ℂ × ResMono D N) :
    t ∈ FAQ_sum g ↔ ∃ x, t ∈ g x := by
  simp [FAQ_sum, List.mem_flatMap]

/-- The standard basis vectors lie in `avgVecs`. -/
private lemma FAQ_e_mem (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := by
  simp only [avgVecs, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl ⟨p, rfl⟩))

/-- The vectors `B e_p` lie in `avgVecs`. -/
private lemma FAQ_Be_mem (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (B *ᵥ Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := by
  simp only [avgVecs, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inr ⟨p, rfl⟩))

/-- The vectors `Λ e_p` lie in `avgVecs`. -/
private lemma FAQ_Le_mem (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (Λ *ᵥ Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := by
  simp only [avgVecs, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨p, rfl⟩

/-- Every term of `FAQ_PQ` has at most three factors, with vectors in `avgVecs` and the pair
`(Λ, z)`. -/
private lemma FAQ_PQ_good (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (k l : Idx D N) :
    ∀ t ∈ FAQ_PQ D N θ Λ B z k l, t.2.length ≤ 3 ∧ ∀ f ∈ t.2,
      f.1 ∈ avgVecs D N Λ B ∧ f.2.1 ∈ avgVecs D N Λ B ∧ f.2.2 = (Λ, z) := by
  intro t ht
  simp only [FAQ_PQ, FAQ_P1, FAQ_P2, FAQ_P3, FAQ_P4r, FAQ_P5r, List.mem_append, FAQ_mem_sum,
    List.mem_singleton] at ht
  have e := FAQ_e_mem D N Λ B
  have eB := FAQ_Be_mem D N Λ B
  have eL := FAQ_Le_mem D N Λ B
  rcases ht with (((((rfl | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨r, m, rfl⟩) | ⟨r, m, rfl⟩))
  all_goals refine ⟨by simp, fun f hf => ?_⟩
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  all_goals rcases hf with rfl | rfl | rfl
  all_goals refine ⟨?_, ?_, rfl⟩ <;> first | exact e _ | exact eB _ | exact eL _

/-- The weight `Σ_t |c_t|` of a resolvent polynomial. -/
private def FAQ_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

/-- The weight of a concatenation. -/
private lemma FAQ_wt_append {D N : ℕ} (P Q : ResPoly D N) :
    FAQ_wt (P ++ Q) = FAQ_wt P + FAQ_wt Q := by
  simp [FAQ_wt, List.map_append, List.sum_append]

/-- The weight of a single term. -/
private lemma FAQ_wt_single {D N : ℕ} (c : ℂ) (m : ResMono D N) : FAQ_wt [(c, m)] = ‖c‖ := by
  simp [FAQ_wt]

/-- The weight of a sum over the index set. -/
private lemma FAQ_wt_sum {D N : ℕ} (g : Idx D N → ResPoly D N) :
    FAQ_wt (FAQ_sum g) = ∑ x, FAQ_wt (g x) := by
  have key : ∀ L : List (Idx D N), FAQ_wt (L.flatMap g) = (L.map fun x => FAQ_wt (g x)).sum := by
    intro L
    induction L with
    | nil => simp [FAQ_wt]
    | cons x L ih =>
      rw [List.flatMap_cons, FAQ_wt_append, ih, List.map_cons, List.sum_cons]
  unfold FAQ_sum
  rw [key, Finset.sum_map_toList]

/-- Each block of `Idx D N` has `N` elements. -/
private lemma FAQ_card_block (D N : ℕ) (r : Idx D N) :
    ∑ m : Idx D N, (if r.1 = m.1 then (1 : ℝ) else 0) = N := by
  rw [Fintype.sum_prod_type]
  have : ∀ m1 : Fin D, ∑ m2 : Fin N, (if r.1 = (m1, m2).1 then (1 : ℝ) else 0) =
      if r.1 = m1 then (N : ℝ) else 0 := by
    intro m1
    by_cases h : r.1 = m1 <;> simp [h]
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The real coefficient `θ N⁻¹ 1(same block) + (1 - θ)(DN)⁻¹`. -/
private def FAQ_kapR (D N : ℕ) (θ : ℝ) (r m : Idx D N) : ℝ :=
  θ * (N : ℝ)⁻¹ * (if r.1 = m.1 then 1 else 0) + (1 - θ) * ((D : ℝ) * N)⁻¹

/-- The coefficient `κ` is the real number `FAQ_kapR`. -/
private lemma FAQ_kap_eq (D N : ℕ) (θ : ℝ) (r m : Idx D N) :
    FAQ_kap D N θ r m = (FAQ_kapR D N θ r m : ℂ) := by
  unfold FAQ_kap FAQ_kapR
  push_cast
  split_ifs <;> simp

/-- For `θ ∈ [0, 1]` the coefficient `κ` is nonnegative. -/
private lemma FAQ_kapR_nonneg (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (r m : Idx D N) :
    0 ≤ FAQ_kapR D N θ r m := by
  unfold FAQ_kapR
  have h1 : 0 ≤ 1 - θ := by linarith
  split_ifs <;> positivity

/-- The sum of `κ` over all pairs is `D N`. -/
private lemma FAQ_kapR_sum (D N : ℕ) (θ : ℝ) (hD : 0 < D) (hN : 0 < N) :
    ∑ r : Idx D N, ∑ m : Idx D N, FAQ_kapR D N θ r m = (D * N : ℝ) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold FAQ_kapR
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, FAQ_card_block]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- The norm of `(DN)⁻¹` as a complex number. -/
private lemma FAQ_norm_inv (D N : ℕ) : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by
  rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]

/-- The weight of `FAQ_PQ` is at most `4 (1 + |z|)`: `(DN)⁻¹ + 3 + |z|`, where the three
`1`'s are the weights of the groups with `(DN)⁻¹` and `κ` (this is where `θ ∈ [0, 1]` enters). -/
private lemma FAQ_wt_PQ_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N) :
    FAQ_wt (FAQ_PQ D N θ Λ B z k l) ≤ 4 * (1 + ‖z‖) := by
  have hD : 0 < D := k.1.pos
  have hN : 0 < N := k.2.pos
  have hDN : (0 : ℝ) < (D : ℝ) * N := by positivity
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by
    simp [Fintype.card_prod]
  have hone : ((D : ℝ) * N)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by
      have h1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith)
  have hκ : ∀ r m : Idx D N, ‖((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r m‖ =
      ((D : ℝ) * N)⁻¹ * FAQ_kapR D N θ r m := by
    intro r m
    rw [norm_mul, FAQ_norm_inv, FAQ_kap_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (FAQ_kapR_nonneg D N θ hθ0 hθ1 r m)]
  have hs1 : ∑ _m : Idx D N, ((D : ℝ) * N)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hs2 : ∑ r : Idx D N, ∑ m : Idx D N, ((D : ℝ) * N)⁻¹ * FAQ_kapR D N θ r m = 1 := by
    simp only [← Finset.mul_sum]
    rw [FAQ_kapR_sum D N θ hD hN]
    field_simp
  unfold FAQ_PQ FAQ_P1 FAQ_P2 FAQ_P3 FAQ_P4r FAQ_P5r
  simp only [FAQ_wt_append, FAQ_wt_sum, FAQ_wt_single, norm_neg, FAQ_norm_inv, norm_mul, hκ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.mul_sum] at *
  rw [hs2]
  have e1 : (D : ℝ) * N * (‖z‖ * ((D : ℝ) * N)⁻¹) = ‖z‖ := by field_simp
  have e2 : (D : ℝ) * N * ((D : ℝ) * N)⁻¹ = 1 := by field_simp
  rw [e1, e2]
  have := norm_nonneg z
  nlinarith

/-! ### The resolvent polynomial of `⟨B H̲G⟩` -/

/-- The resolvent polynomial of `⟨B H̲G⟩ = (DN)⁻¹ tr(B (I - (Λ - z) G + S_θ(G) G))` in forms
`e_q^* G (M e_q)`, `M ∈ {B, B Λ}`, and the diagonal entries of `G`. -/
private def FAQ_PF (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) : ResPoly D N :=
  [(((D : ℂ) * N)⁻¹ * B.trace, [])] ++
  FAQ_sum (fun q => [(-((D : ℂ) * N)⁻¹, [(Pi.single q 1, (B * Λ) *ᵥ Pi.single q 1, Λ, z)])]) ++
  FAQ_sum (fun q => [(((D : ℂ) * N)⁻¹ * z, [(Pi.single q 1, B *ᵥ Pi.single q 1, Λ, z)])]) ++
  FAQ_sum (fun r => FAQ_sum (fun q => [(((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r q,
    [(Pi.single r 1, Pi.single r 1, Λ, z), (Pi.single q 1, B *ᵥ Pi.single q 1, Λ, z)])]))

/-- The value of `FAQ_PF` is `⟨B (I - (Λ - z) G + S_θ(G) G)⟩`. -/
private lemma FAQ_eval_PF (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FAQ_PF D N θ Λ B z) h =
      ntr (B * (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z +
        sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z)) := by
  set G := res (Matrix.of h + Λ) z with hG
  have hmat : B * (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G +
      sTheta D N θ G * G) = B - (B * Λ) * G + z • (B * G) + B * (sTheta D N θ G * G) := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Matrix.one_mul]
    abel
  have t1 : (B * Λ * G).trace = ∑ q, (G * (B * Λ)) q q := by
    rw [Matrix.trace_mul_comm]; rfl
  have t2 : (B * G).trace = ∑ q, (G * B) q q := by
    rw [Matrix.trace_mul_comm]; rfl
  have t3 : (B * (sTheta D N θ G * G)).trace =
      ∑ q, ∑ r, FAQ_kap D N θ r q * G r r * (G * B) q q := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, FAQ_sTheta_apply, ite_mul,
      zero_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.sum_mul]
  rw [FAQ_ntr_eq, hmat]
  simp only [FAQ_PF, resPolyEval_append, FAQ_eval_sum]
  simp only [resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, add_zero, mul_one, FAQ_f_ee, FAQ_f_eM]
  have hsum : ∑ r, (B - B * Λ * G + z • (B * G) + B * (sTheta D N θ G * G)) r r =
      B.trace - (B * Λ * G).trace + z * (B * G).trace + (B * (sTheta D N θ G * G)).trace := by
    simp [Matrix.trace, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum, t1, t2, t3]
  have e2 : ∑ x, -((D : ℂ) * N)⁻¹ * (G * (B * Λ)) x x =
      -(((D : ℂ) * N)⁻¹ * ∑ q, (G * (B * Λ)) q q) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e3 : ∑ x, ((D : ℂ) * N)⁻¹ * z * (G * B) x x =
      ((D : ℂ) * N)⁻¹ * (z * ∑ q, (G * B) q q) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e4 : ∑ x, ∑ x_1, ((D : ℂ) * N)⁻¹ * FAQ_kap D N θ x x_1 * (G x x * (G * B) x_1 x_1) =
      ((D : ℂ) * N)⁻¹ * ∑ q, ∑ r, FAQ_kap D N θ r q * G r r * (G * B) q q := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [e2, e3, e4]
  ring

/-- The derivative of a constant term vanishes. -/
private lemma FAQ_resPolyD_nil {D N : ℕ} (a b : Idx D N) (c κ : ℂ) :
    resPolyD a b c [(κ, ([] : ResMono D N))] = [] := by
  simp [resPolyD, resMonoD]

/-- The derivative of a one-factor term. -/
private lemma FAQ_resPolyD_one {D N : ℕ} (a b : Idx D N) (c κ : ℂ) (x y : Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    resPolyD a b c [(κ, [(x, y, Λ, z)])] =
      [(κ * -c, [(x, Pi.single a 1, Λ, z), (Pi.single b 1, y, Λ, z)])] := by
  simp [resPolyD, resMonoD]

/-- The derivative of a two-factor term. -/
private lemma FAQ_resPolyD_two {D N : ℕ} (a b : Idx D N) (c κ : ℂ) (x y u v : Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    resPolyD a b c [(κ, [(x, y, Λ, z), (u, v, Λ, z)])] =
      [(κ * -c, [(x, Pi.single a 1, Λ, z), (Pi.single b 1, y, Λ, z), (u, v, Λ, z)]),
       (κ * -c, [(x, y, Λ, z), (u, Pi.single a 1, Λ, z), (Pi.single b 1, v, Λ, z)])] := by
  simp [resPolyD, resMonoD]

/-- The derivative of the polynomial `FAQ_PF` evaluates to `c ((DN)⁻¹ (G B)_{ba} - Q_{ba})`. -/
private lemma FAQ_eval_dPF (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (a b : Idx D N) (c : ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    resPolyEval (resPolyD a b c (FAQ_PF D N θ Λ B z)) h =
      c * (((D : ℂ) * N)⁻¹ * (res (Matrix.of h + Λ) z * B) b a -
        qMat D N θ (Matrix.of h) Λ B z b a) := by
  rw [FAQ_qMat_apply D N θ (Matrix.of h) Λ B hh hΛ z hz b a]
  simp only [FAQ_PF, FAQ_resPolyD_append, FAQ_resPolyD_sum, FAQ_resPolyD_nil,
    FAQ_resPolyD_one, FAQ_resPolyD_two, resPolyEval_append, FAQ_eval_sum]
  simp only [resPolyEval, resMonoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, add_zero, mul_one, FAQ_f_ee, FAQ_f_eM]
  set G := res (Matrix.of h + Λ) z with hG
  have u1 : ∑ x, G x a * (G * (B * Λ)) b x = ∑ m, (G * B) b m * (Λ * G) m a := by
    have e : (G * (B * Λ)) * G = (G * B) * (Λ * G) := by simp [Matrix.mul_assoc]
    have := congrFun (congrFun e b) a
    rw [Matrix.mul_apply (M := G * (B * Λ)) (N := G),
      Matrix.mul_apply (M := G * B) (N := Λ * G)] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have u2 : ∑ x, G x a * (G * B) b x = ∑ m, (G * B) b m * G m a :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  have u3 : ∑ x, ∑ x_1, FAQ_kap D N θ x x_1 * (G x a * (G b x * (G * B) x_1 x_1)) =
      ∑ m, ∑ r, FAQ_kap D N θ r m * (G * B) r r * (G b m * G m a) := by
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
    rw [FAQ_kap_comm D N θ m r]
    ring
  have u4 : ∑ x, ∑ x_1, FAQ_kap D N θ x x_1 * (G x x * (G x_1 a * (G * B) b x_1)) =
      ∑ m, ∑ r, FAQ_kap D N θ r m * G r r * ((G * B) b m * G m a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have l1 : ∑ x, -((D : ℂ) * N)⁻¹ * -c * (G x a * (G * (B * Λ)) b x) =
      c * ((D : ℂ) * N)⁻¹ * ∑ x, G x a * (G * (B * Λ)) b x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have l2 : ∑ x, ((D : ℂ) * N)⁻¹ * z * -c * (G x a * (G * B) b x) =
      -(c * ((D : ℂ) * N)⁻¹ * (z * ∑ x, G x a * (G * B) b x)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have l3 : ∑ x, ∑ x_1, (((D : ℂ) * N)⁻¹ * FAQ_kap D N θ x x_1 * -c *
        (G x a * (G b x * (G * B) x_1 x_1)) + ((D : ℂ) * N)⁻¹ * FAQ_kap D N θ x x_1 * -c *
        (G x x * (G x_1 a * (G * B) b x_1))) =
      -(c * ((D : ℂ) * N)⁻¹ * ((∑ x, ∑ x_1, FAQ_kap D N θ x x_1 *
          (G x a * (G b x * (G * B) x_1 x_1))) +
        (∑ x, ∑ x_1, FAQ_kap D N θ x x_1 * (G x x * (G x_1 a * (G * B) b x_1))))) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_1 _ => ?_
    ring
  rw [l1, l2, l3, u1, u2, u3, u4]
  ring

/-- Every factor of `FAQ_PF` has the pair `(Λ, z)`. -/
private lemma FAQ_PF_pair (D N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    ∀ t ∈ FAQ_PF D N θ Λ B z, ∀ f ∈ t.2, f.2.2 = (Λ, z) := by
  intro t ht f hf
  simp only [FAQ_PF, List.mem_append, FAQ_mem_sum, List.mem_singleton] at ht
  rcases ht with ((((rfl | ⟨q, rfl⟩) | ⟨q, rfl⟩) | ⟨r, q, rfl⟩))
  · simp at hf
  · simp only [List.mem_singleton] at hf
    subst hf
    rfl
  · simp only [List.mem_singleton] at hf
    subst hf
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> rfl

/-! ### The derivatives of a family of two `m`-dependent factors -/

/-- The value of a polynomial with a first term. -/
private lemma FAQ_eval_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (t :: P) h = t.1 * resMonoEval t.2 h + resPolyEval P h := by
  simp [resPolyEval]

/-- The value of a polynomial whose terms get one more factor in front. -/
private lemma FAQ_eval_map1 {D N : ℕ} (c : ℂ) (f : ResFactor D N) (S : ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (S.map fun t => (c * t.1, f :: t.2)) h =
      c * resFactorEval f h * resPolyEval S h := by
  induction S with
  | nil => simp [resPolyEval]
  | cons t S ih =>
    simp only [List.map_cons, resPolyEval, List.sum_cons, resMonoEval, List.prod_cons] at ih ⊢
    rw [ih]
    ring

/-- The value of a polynomial whose terms get two more factors in front. -/
private lemma FAQ_eval_map2 {D N : ℕ} (f₁ f₂ : ResFactor D N) (S : ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (S.map fun t => (t.1, f₁ :: f₂ :: t.2)) h =
      resFactorEval f₁ h * resFactorEval f₂ h * resPolyEval S h := by
  induction S with
  | nil => simp [resPolyEval]
  | cons t S ih =>
    simp only [List.map_cons, resPolyEval, List.sum_cons, resMonoEval, List.prod_cons] at ih ⊢
    rw [ih]
    ring

/-- The derivative of a polynomial is the concatenation of the derivatives of its terms. -/
private lemma FAQ_resPolyD_cons {D N : ℕ} (a b : Idx D N) (c : ℂ) (t : ℂ × ResMono D N)
    (S : ResPoly D N) :
    resPolyD a b c (t :: S) = resPolyD a b c [t] ++ resPolyD a b c S := by
  simp [resPolyD, List.flatMap_cons]

/-- The derivative of a term with two leading factors. -/
private lemma FAQ_resPolyD_lead2 {D N : ℕ} (a b : Idx D N) (c κ : ℂ) (x y u v : Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (rest : ResMono D N) :
    resPolyD a b c [(κ, (x, y, Λ, z) :: (u, v, Λ, z) :: rest)] =
      [(κ * -c, (x, Pi.single a 1, Λ, z) :: (Pi.single b 1, y, Λ, z) :: (u, v, Λ, z) :: rest),
       (κ * -c, (x, y, Λ, z) :: (u, Pi.single a 1, Λ, z) :: (Pi.single b 1, v, Λ, z) :: rest)] ++
      (resPolyD a b c [(κ, rest)]).map fun t => (t.1, (x, y, Λ, z) :: (u, v, Λ, z) :: t.2) := by
  simp [resPolyD, resMonoD, List.map_map, Function.comp_def]

/-- The value of the derivative of a polynomial with two leading factors. -/
private lemma FAQ_eval_dmap2 {D N : ℕ} (a b : Idx D N) (c : ℂ) (x y u v : Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (S : ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (resPolyD a b c (S.map fun t => (t.1, (x, y, Λ, z) :: (u, v, Λ, z) :: t.2))) h =
      -c * (resFactorEval (x, Pi.single a 1, Λ, z) h * resFactorEval (Pi.single b 1, y, Λ, z) h *
          resFactorEval (u, v, Λ, z) h +
        resFactorEval (x, y, Λ, z) h * resFactorEval (u, Pi.single a 1, Λ, z) h *
          resFactorEval (Pi.single b 1, v, Λ, z) h) * resPolyEval S h +
      resFactorEval (x, y, Λ, z) h * resFactorEval (u, v, Λ, z) h *
        resPolyEval (resPolyD a b c S) h := by
  induction S with
  | nil => simp [resPolyD, resPolyEval]
  | cons t S ih =>
    rw [List.map_cons, FAQ_resPolyD_cons, resPolyEval_append, ih]
    obtain ⟨κ, rest⟩ := t
    simp only
    rw [FAQ_resPolyD_lead2, resPolyEval_append, FAQ_eval_map2, FAQ_resPolyD_cons,
      resPolyEval_append, FAQ_eval_cons, FAQ_eval_cons]
    rw [FAQ_eval_cons (κ, rest) S h, FAQ_resPolyD_cons a b c (κ, rest) S, resPolyEval_append]
    have h0 : resPolyD a b c ([] : ResPoly D N) = [] := rfl
    simp only [h0, resPolyEval, List.map_nil, List.sum_nil, add_zero, resMonoEval, List.map_cons,
      List.prod_cons] at *
    ring

/-- The family of polynomials with terms `t.1 (e_p^* G y)(u^* G e_q) Π t.2`, `t ∈ R p q`: the two
`m`-dependent factors carry the vectors `y` and `u`, and `R p q` is the rest. -/
private def FAQ_big {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (R : Idx D N → Idx D N → ResPoly D N) (y u : Idx D N → ℂ) : ResPoly D N :=
  FAQ_sum fun p => FAQ_sum fun q =>
    (R p q).map fun t => (t.1, (Pi.single p 1, y, Λ, z) :: (u, Pi.single q 1, Λ, z) :: t.2)

/-- The value of `FAQ_big`. -/
private lemma FAQ_eval_big {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (R : Idx D N → Idx D N → ResPoly D N) (y u : Idx D N → ℂ) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FAQ_big Λ z R y u) h = ∑ p, ∑ q, resFactorEval (Pi.single p 1, y, Λ, z) h *
      resFactorEval (u, Pi.single q 1, Λ, z) h * resPolyEval (R p q) h := by
  unfold FAQ_big
  simp only [FAQ_eval_sum, FAQ_eval_map2]

/-- The polynomials of the derivative of `FAQ_big`: the derivative of the rest, and the
derivative of the two `m`-dependent factors, which moves a vector into the rest. -/
private def FAQ_step {D N : ℕ} (a b : Idx D N) (c : ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (R : Idx D N → Idx D N → ResPoly D N) : Idx D N → Idx D N → ResPoly D N :=
  fun p q => resPolyD a b c (R p q) ++
    (if p = b then FAQ_sum (fun p₀ => (R p₀ q).map fun t =>
      (-c * t.1, (Pi.single p₀ 1, Pi.single a 1, Λ, z) :: t.2)) else []) ++
    (if q = a then FAQ_sum (fun q₀ => (R p q₀).map fun t =>
      (-c * t.1, (Pi.single b 1, Pi.single q₀ 1, Λ, z) :: t.2)) else [])

/-- The derivative of `FAQ_big` is `FAQ_big` of the polynomials `FAQ_step`. -/
private lemma FAQ_eval_dbig {D N : ℕ} (a b : Idx D N) (c : ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (R : Idx D N → Idx D N → ResPoly D N) (y u : Idx D N → ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (resPolyD a b c (FAQ_big Λ z R y u)) h =
      resPolyEval (FAQ_big Λ z (FAQ_step a b c Λ z R) y u) h := by
  unfold FAQ_big
  simp only [FAQ_resPolyD_sum, FAQ_eval_sum, FAQ_eval_dmap2, FAQ_step, resPolyEval_append,
    apply_ite (fun P => resPolyEval P h), FAQ_eval_map2, FAQ_eval_sum, FAQ_eval_map1]
  have hzero : resPolyEval ([] : ResPoly D N) h = 0 := by simp [resPolyEval]
  simp only [hzero, mul_add, Finset.sum_add_distrib]
  have T2 : ∑ p : Idx D N, ∑ q : Idx D N, resFactorEval (Pi.single p 1, y, Λ, z) h *
      resFactorEval (u, Pi.single q 1, Λ, z) h *
        (if p = b then ∑ x, -c * resFactorEval (Pi.single x 1, Pi.single a 1, Λ, z) h *
          resPolyEval (R x q) h else 0) =
      ∑ q : Idx D N, resFactorEval (Pi.single b 1, y, Λ, z) h *
        resFactorEval (u, Pi.single q 1, Λ, z) h *
          ∑ x, -c * resFactorEval (Pi.single x 1, Pi.single a 1, Λ, z) h *
            resPolyEval (R x q) h := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have T3 : ∑ p : Idx D N, ∑ q : Idx D N, resFactorEval (Pi.single p 1, y, Λ, z) h *
      resFactorEval (u, Pi.single q 1, Λ, z) h *
        (if q = a then ∑ x, -c * resFactorEval (Pi.single b 1, Pi.single x 1, Λ, z) h *
          resPolyEval (R p x) h else 0) =
      ∑ p : Idx D N, resFactorEval (Pi.single p 1, y, Λ, z) h *
        resFactorEval (u, Pi.single a 1, Λ, z) h *
          ∑ x, -c * resFactorEval (Pi.single b 1, Pi.single x 1, Λ, z) h *
            resPolyEval (R p x) h := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  simp only [mul_ite, mul_zero] at T2 T3 ⊢
  have c1 : ∑ x : Idx D N, ∑ x_1 : Idx D N, -c *
      (resFactorEval (Pi.single x 1, Pi.single a 1, Λ, z) h *
        resFactorEval (Pi.single b 1, y, Λ, z) h *
        resFactorEval (u, Pi.single x_1 1, Λ, z) h) * resPolyEval (R x x_1) h =
      ∑ q : Idx D N, resFactorEval (Pi.single b 1, y, Λ, z) h *
        resFactorEval (u, Pi.single q 1, Λ, z) h *
          ∑ x, -c * resFactorEval (Pi.single x 1, Pi.single a 1, Λ, z) h *
            resPolyEval (R x q) h := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have c2 : ∑ x : Idx D N, ∑ x_1 : Idx D N, -c *
      (resFactorEval (Pi.single x 1, y, Λ, z) h * resFactorEval (u, Pi.single a 1, Λ, z) h *
        resFactorEval (Pi.single b 1, Pi.single x_1 1, Λ, z) h) * resPolyEval (R x x_1) h =
      ∑ p : Idx D N, resFactorEval (Pi.single p 1, y, Λ, z) h *
        resFactorEval (u, Pi.single a 1, Λ, z) h *
          ∑ x, -c * resFactorEval (Pi.single b 1, Pi.single x 1, Λ, z) h *
            resPolyEval (R p x) h := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [add_mul, Finset.sum_add_distrib]
  rw [T2, T3, c1, c2]
  ring

/-! ### Degree, vectors and weight of the polynomials of the expansion -/

/-- At most `ℓ` factors per term, with vectors in `V` and the pair `(Λ, z)`. -/
private def FAQ_good {D N : ℕ} (V : Set (Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (ℓ : ℕ) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, t.2.length ≤ ℓ ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2 = (Λ, z)

/-- The factors of the terms of `resMonoD a b c m`: each is a factor of `m`, or one of the two
factors that replace it; the length goes up by one and every coefficient is `-c`. -/
private lemma FAQ_resMonoD_mem {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    ∀ s ∈ resMonoD a b c m, s.2.length = m.length + 1 ∧ s.1 = -c ∧ ∀ g ∈ s.2, ∃ f ∈ m,
      g = f ∨ g = (f.1, Pi.single a 1, f.2.2.1, f.2.2.2) ∨
        g = (Pi.single b 1, f.2.1, f.2.2.1, f.2.2.2) := by
  induction m with
  | nil => intro s hs; simp [resMonoD] at hs
  | cons f m ih =>
    intro s hs
    simp only [resMonoD, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨t, ht, rfl⟩
    · refine ⟨by simp, rfl, fun g hg => ?_⟩
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨f, List.mem_cons_self, Or.inr (Or.inl rfl)⟩
      · exact ⟨f, List.mem_cons_self, Or.inr (Or.inr rfl)⟩
      · exact ⟨g, List.mem_cons_of_mem _ hg, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ih t ht
      refine ⟨by simp [h1], h2, fun g hg => ?_⟩
      simp only [List.mem_cons] at hg
      rcases hg with hg | hg
      · exact ⟨f, List.mem_cons_self, Or.inl hg⟩
      · obtain ⟨f', hf', hg'⟩ := h3 g hg
        exact ⟨f', List.mem_cons_of_mem _ hf', hg'⟩

/-- One derivative with `e_a, e_b ∈ V`: one more factor per term, vectors still in `V`, pairs
unchanged. -/
private lemma FAQ_good_resPolyD {D N : ℕ} (V : Set (Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (a b : Idx D N) (c : ℂ)
    (ha : (Pi.single a 1 : Idx D N → ℂ) ∈ V) (hb : (Pi.single b 1 : Idx D N → ℂ) ∈ V) (ℓ : ℕ)
    (P : ResPoly D N) (hP : FAQ_good V Λ z ℓ P) : FAQ_good V Λ z (ℓ + 1) (resPolyD a b c P) := by
  intro u hu
  unfold resPolyD at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨t, ht, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨hlen, -, hg⟩ := FAQ_resMonoD_mem a b c t.2 s hs
  obtain ⟨hl, hf⟩ := hP t ht
  refine ⟨by simp only; omega, fun g hg' => ?_⟩
  obtain ⟨f, hfm, hgf⟩ := hg g hg'
  obtain ⟨hf1, hf2, hf3⟩ := hf f hfm
  rcases hgf with h | h | h <;> rw [h]
  · exact ⟨hf1, hf2, hf3⟩
  · exact ⟨hf1, ha, hf3⟩
  · exact ⟨hb, hf2, hf3⟩

/-- The derivative of `a` polynomial in cons form. -/
private lemma FAQ_resPolyD_cons' {D N : ℕ} (a b : Idx D N) (c : ℂ) (t : ℂ × ResMono D N)
    (S : ResPoly D N) :
    resPolyD a b c (t :: S) = ((resMonoD a b c t.2).map fun s => (t.1 * s.1, s.2)) ++
      resPolyD a b c S := by
  simp [resPolyD, List.flatMap_cons]

/-- The weight of a polynomial with a first term. -/
private lemma FAQ_wt_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N) :
    FAQ_wt (t :: P) = ‖t.1‖ + FAQ_wt P := by
  simp [FAQ_wt]

/-- The weight is nonnegative. -/
private lemma FAQ_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ FAQ_wt P :=
  List.sum_nonneg fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

/-- Every derivative of a monomial of degree `d` is `d` terms with coefficient `-c`. -/
private lemma FAQ_wt_resMonoD {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    FAQ_wt (resMonoD a b c m) = m.length * ‖c‖ := by
  induction m with
  | nil => simp [resMonoD, FAQ_wt]
  | cons f m ih =>
    have e : FAQ_wt ((resMonoD a b c m).map fun t => (t.1, f :: t.2)) =
        FAQ_wt (resMonoD a b c m) := by
      simp [FAQ_wt, Function.comp_def]
    simp only [resMonoD]
    rw [FAQ_wt_cons, e, ih]
    simp only [norm_neg, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The weight of a polynomial whose coefficients are all multiplied by `c₀`. -/
private lemma FAQ_wt_map_mul {D N : ℕ} (c₀ : ℂ) (Q : ResPoly D N) :
    FAQ_wt (Q.map fun s => (c₀ * s.1, s.2)) = ‖c₀‖ * FAQ_wt Q := by
  induction Q with
  | nil => simp [FAQ_wt]
  | cons t Q ih =>
    rw [List.map_cons, FAQ_wt_cons, ih, FAQ_wt_cons]
    simp only [norm_mul]
    ring

/-- The weight of a polynomial with one factor added in front of every term. -/
private lemma FAQ_wt_map1 {D N : ℕ} (c₀ : ℂ) (f : ResFactor D N) (Q : ResPoly D N) :
    FAQ_wt (Q.map fun s => (c₀ * s.1, f :: s.2)) = ‖c₀‖ * FAQ_wt Q := by
  rw [← FAQ_wt_map_mul]
  simp [FAQ_wt, Function.comp_def]

/-- The weight of one derivative of a polynomial. -/
private lemma FAQ_wt_resPolyD {D N : ℕ} (a b : Idx D N) (c : ℂ) (P : ResPoly D N) :
    FAQ_wt (resPolyD a b c P) = ‖c‖ * (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum := by
  induction P with
  | nil => simp [resPolyD, FAQ_wt]
  | cons t P ih =>
    rw [FAQ_resPolyD_cons', FAQ_wt_append, FAQ_wt_map_mul, FAQ_wt_resMonoD, ih, List.map_cons,
      List.sum_cons]
    ring

/-- One derivative multiplies the weight by at most the degree bound `ℓ`, when `|c| ≤ 1`. -/
private lemma FAQ_wt_resPolyD_le {D N : ℕ} (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1) (ℓ : ℕ)
    (P : ResPoly D N) (hP : ∀ t ∈ P, t.2.length ≤ ℓ) :
    FAQ_wt (resPolyD a b c P) ≤ ℓ * FAQ_wt P := by
  have key : ∀ Q : ResPoly D N, (∀ t ∈ Q, t.2.length ≤ ℓ) →
      (Q.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum ≤ ℓ * FAQ_wt Q := by
    intro Q
    induction Q with
    | nil => intro _; simp [FAQ_wt]
    | cons t Q ih =>
      intro hQ
      have h1 := ih fun u hu => hQ u (List.mem_cons_of_mem _ hu)
      have h2 : (t.2.length : ℝ) ≤ ℓ := by exact_mod_cast hQ t List.mem_cons_self
      rw [List.map_cons, List.sum_cons, FAQ_wt_cons]
      nlinarith [norm_nonneg t.1, mul_le_mul_of_nonneg_left h2 (norm_nonneg t.1)]
  rw [FAQ_wt_resPolyD]
  have h1 := key P hP
  have h3 : 0 ≤ (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  calc ‖c‖ * (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum
      ≤ 1 * (P.map fun t => ‖t.1‖ * (t.2.length : ℝ)).sum := mul_le_mul_of_nonneg_right hc h3
    _ ≤ ℓ * FAQ_wt P := by rw [one_mul]; exact h1

/-- The two leading factors and the rest of every term of `FAQ_big`. -/
private lemma FAQ_mem_big {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (R : Idx D N → Idx D N → ResPoly D N) (y u : Idx D N → ℂ) (t : ℂ × ResMono D N) :
    t ∈ FAQ_big Λ z R y u ↔ ∃ p q, ∃ s ∈ R p q,
      t = (s.1, (Pi.single p 1, y, Λ, z) :: (u, Pi.single q 1, Λ, z) :: s.2) := by
  unfold FAQ_big
  simp only [FAQ_mem_sum, List.mem_map]
  constructor
  · rintro ⟨p, q, s, hs, rfl⟩
    exact ⟨p, q, s, hs, rfl⟩
  · rintro ⟨p, q, s, hs, rfl⟩
    exact ⟨p, q, s, hs, rfl⟩

/-- All factors of `FAQ_big` carry the pair `(Λ, z)` when the rest does. -/
private lemma FAQ_big_pair {D N : ℕ} (V : Set (Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (ℓ : ℕ) (R : Idx D N → Idx D N → ResPoly D N)
    (hR : ∀ p q, FAQ_good V Λ z ℓ (R p q)) (y u : Idx D N → ℂ) :
    ∀ t ∈ FAQ_big Λ z R y u, ∀ f ∈ t.2, f.2.2 = (Λ, z) := by
  intro t ht f hf
  obtain ⟨p, q, s, hs, rfl⟩ := (FAQ_mem_big Λ z R y u t).mp ht
  simp only [List.mem_cons] at hf
  rcases hf with rfl | rfl | hf
  · rfl
  · rfl
  · exact ((hR p q s hs).2 f hf).2.2

/-- The representation of a family `F` of functions of `w` by the polynomials `R`: along the
slice through `h`, `F_m(w)` is the value of `FAQ_big` for the vectors `Y m`, `U m`; the rest has
at most `ℓ` factors per term over `V` with the pair `(Λ, z)` and total weight at most `W`. -/
private def FAQ_Rep {D N : ℕ} (V : Set (Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (Y U : Idx D N → Idx D N → ℂ)
    (F : Idx D N → ℂ → ℂ) (ℓ : ℕ) (W : ℝ) : Prop :=
  ∃ R : Idx D N → Idx D N → ResPoly D N, (∀ p q, FAQ_good V Λ z ℓ (R p q)) ∧
    ∑ p, ∑ q, FAQ_wt (R p q) ≤ W ∧
    ∀ m w, F m w = resPolyEval (FAQ_big Λ z R (Y m) (U m)) (setEntry h i j w)

/-- One derivative keeps a representation: the degree of the rest goes up by one and the weight
is multiplied by at most `ℓ + 2`. -/
private lemma FAQ_Rep_step {D N : ℕ} (V : Set (Idx D N → ℂ))
    (hV : ∀ p : Idx D N, (Pi.single p 1 : Idx D N → ℂ) ∈ V)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (Y U : Idx D N → Idx D N → ℂ) (F : Idx D N → ℂ → ℂ) (ℓ : ℕ) (W : ℝ) (a b : Idx D N) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (Dr : (ℂ → ℂ) → ℂ → ℂ)
    (hD : ∀ P : ResPoly D N, (∀ t ∈ P, ∀ f ∈ t.2, f.2.2 = (Λ, z)) →
      Dr (fun w => resPolyEval P (setEntry h i j w)) =
        fun w => resPolyEval (resPolyD a b c P) (setEntry h i j w))
    (hR : FAQ_Rep V Λ z h i j Y U F ℓ W) :
    FAQ_Rep V Λ z h i j Y U (fun m => Dr (F m)) (ℓ + 1) ((ℓ + 2) * W) := by
  obtain ⟨R, hgood, hwt, hF⟩ := hR
  refine ⟨FAQ_step a b c Λ z R, ?_, ?_, ?_⟩
  · intro p q t ht
    unfold FAQ_step at ht
    simp only [List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · exact FAQ_good_resPolyD V Λ z a b c (hV a) (hV b) ℓ (R p q) (hgood p q) t ht
    · split_ifs at ht
      · rw [FAQ_mem_sum] at ht
        obtain ⟨p₀, ht⟩ := ht
        rw [List.mem_map] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        obtain ⟨hl, hf⟩ := hgood p₀ q s hs
        refine ⟨by simp only [List.length_cons]; omega, fun f hf' => ?_⟩
        simp only [List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact ⟨hV p₀, hV a, rfl⟩
        · exact hf f hf'
      · simp at ht
    · split_ifs at ht
      · rw [FAQ_mem_sum] at ht
        obtain ⟨q₀, ht⟩ := ht
        rw [List.mem_map] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        obtain ⟨hl, hf⟩ := hgood p q₀ s hs
        refine ⟨by simp only [List.length_cons]; omega, fun f hf' => ?_⟩
        simp only [List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact ⟨hV b, hV q₀, rfl⟩
        · exact hf f hf'
      · simp at ht
  · set E := ∑ p, ∑ q, FAQ_wt (R p q) with hE
    have hE0 : 0 ≤ E :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => FAQ_wt_nonneg _
    have hstep : ∀ p q, FAQ_wt (FAQ_step a b c Λ z R p q) ≤ ℓ * FAQ_wt (R p q) +
        (if p = b then ∑ p₀, FAQ_wt (R p₀ q) else 0) +
        (if q = a then ∑ q₀, FAQ_wt (R p q₀) else 0) := by
      intro p q
      unfold FAQ_step
      rw [FAQ_wt_append, FAQ_wt_append]
      have h1 := FAQ_wt_resPolyD_le a b c hc ℓ (R p q) fun t ht => (hgood p q t ht).1
      have h2 : FAQ_wt (if p = b then FAQ_sum (fun p₀ => (R p₀ q).map fun t =>
          (-c * t.1, (Pi.single p₀ 1, Pi.single a 1, Λ, z) :: t.2)) else []) ≤
          if p = b then ∑ p₀, FAQ_wt (R p₀ q) else 0 := by
        split_ifs
        · rw [FAQ_wt_sum]
          refine Finset.sum_le_sum fun p₀ _ => ?_
          rw [FAQ_wt_map1, norm_neg]
          exact mul_le_of_le_one_left (FAQ_wt_nonneg _) hc
        · simp [FAQ_wt]
      have h3 : FAQ_wt (if q = a then FAQ_sum (fun q₀ => (R p q₀).map fun t =>
          (-c * t.1, (Pi.single b 1, Pi.single q₀ 1, Λ, z) :: t.2)) else []) ≤
          if q = a then ∑ q₀, FAQ_wt (R p q₀) else 0 := by
        split_ifs
        · rw [FAQ_wt_sum]
          refine Finset.sum_le_sum fun q₀ _ => ?_
          rw [FAQ_wt_map1, norm_neg]
          exact mul_le_of_le_one_left (FAQ_wt_nonneg _) hc
        · simp [FAQ_wt]
      linarith
    have hsum1 : ∑ p : Idx D N, ∑ q : Idx D N,
        (if p = b then ∑ p₀, FAQ_wt (R p₀ q) else 0) = E := by
      rw [Finset.sum_comm]
      refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) (Finset.sum_comm)
      rw [Finset.sum_ite_eq']
      simp
    have hsum2 : ∑ p : Idx D N, ∑ q : Idx D N,
        (if q = a then ∑ q₀, FAQ_wt (R p q₀) else 0) = E := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_ite_eq']
      simp
    calc ∑ p, ∑ q, FAQ_wt (FAQ_step a b c Λ z R p q)
        ≤ ∑ p : Idx D N, ∑ q : Idx D N, (ℓ * FAQ_wt (R p q) +
          (if p = b then ∑ p₀, FAQ_wt (R p₀ q) else 0) +
          (if q = a then ∑ q₀, FAQ_wt (R p q₀) else 0)) :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hstep p q
      _ = ℓ * E + E + E := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hsum1, hsum2]
      _ ≤ ((ℓ : ℝ) + 2) * W := by
          have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
          nlinarith
  · intro m w
    have e1 : (fun w => F m w) = fun w =>
        resPolyEval (FAQ_big Λ z R (Y m) (U m)) (setEntry h i j w) := funext (hF m)
    have e2 := hD (FAQ_big Λ z R (Y m) (U m)) (FAQ_big_pair V Λ z ℓ R hgood (Y m) (U m))
    change Dr (F m) w = _
    rw [show F m = fun w => resPolyEval (FAQ_big Λ z R (Y m) (U m)) (setEntry h i j w) from e1, e2]
    exact FAQ_eval_dbig a b c Λ z R (Y m) (U m) _

/-- A representation with weight `W` has `0 ≤ W`. -/
private lemma FAQ_Rep_nonneg {D N : ℕ} {V : Set (Idx D N → ℂ)} {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    {z : ℂ} {h : Idx D N → Idx D N → ℂ} {i j : Idx D N} {Y U : Idx D N → Idx D N → ℂ}
    {F : Idx D N → ℂ → ℂ} {ℓ : ℕ} {W : ℝ} (hR : FAQ_Rep V Λ z h i j Y U F ℓ W) : 0 ≤ W := by
  obtain ⟨R, -, hwt, -⟩ := hR
  exact le_trans (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => FAQ_wt_nonneg _) hwt

/-- A representation stays valid for a larger weight. -/
private lemma FAQ_Rep_mono {D N : ℕ} {V : Set (Idx D N → ℂ)} {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    {z : ℂ} {h : Idx D N → Idx D N → ℂ} {i j : Idx D N} {Y U : Idx D N → Idx D N → ℂ}
    {F : Idx D N → ℂ → ℂ} {ℓ : ℕ} {W W' : ℝ} (hR : FAQ_Rep V Λ z h i j Y U F ℓ W)
    (hW : W ≤ W') : FAQ_Rep V Λ z h i j Y U F ℓ W' := by
  obtain ⟨R, hg, hwt, hF⟩ := hR
  exact ⟨R, hg, hwt.trans hW, hF⟩

/-- `n` derivatives keep a representation: degree `ℓ + n`, weight `W (ℓ + n + 1)^n`. -/
private lemma FAQ_Rep_iter {D N : ℕ} (V : Set (Idx D N → ℂ))
    (hV : ∀ p : Idx D N, (Pi.single p 1 : Idx D N → ℂ) ∈ V)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (Y U : Idx D N → Idx D N → ℂ) (F : Idx D N → ℂ → ℂ) (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (Dr : (ℂ → ℂ) → ℂ → ℂ)
    (hD : ∀ P : ResPoly D N, (∀ t ∈ P, ∀ f ∈ t.2, f.2.2 = (Λ, z)) →
      Dr (fun w => resPolyEval P (setEntry h i j w)) =
        fun w => resPolyEval (resPolyD a b c P) (setEntry h i j w))
    (ℓ : ℕ) (W : ℝ) (hR : FAQ_Rep V Λ z h i j Y U F ℓ W) (n : ℕ) :
    FAQ_Rep V Λ z h i j Y U (fun m => Dr^[n] (F m)) (ℓ + n) (W * ((ℓ + n + 1 : ℕ) : ℝ) ^ n) := by
  have hW := FAQ_Rep_nonneg hR
  induction n with
  | zero =>
    refine FAQ_Rep_mono hR ?_
    simp
  | succ n ih =>
    have hs := FAQ_Rep_step V hV Λ z h i j Y U _ (ℓ + n) _ a b c hc Dr hD ih
    change FAQ_Rep V Λ z h i j Y U (fun m => Dr^[n + 1] (F m)) (ℓ + n + 1)
      (W * ((ℓ + (n + 1) + 1 : ℕ) : ℝ) ^ (n + 1))
    refine FAQ_Rep_mono (F := fun m => Dr^[n + 1] (F m)) (by
      simpa only [Function.iterate_succ_apply'] using hs) ?_
    have h1 : (((ℓ + n + 1 : ℕ) : ℝ)) ^ n ≤ (((ℓ + (n + 1) + 1 : ℕ) : ℝ)) ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast (by omega : ℓ + n + 1 ≤ ℓ + (n + 1) + 1)) n
    have h2 : (((ℓ + n : ℕ) : ℝ) + 2) = (((ℓ + (n + 1) + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [h2, pow_succ]
    have := mul_le_mul_of_nonneg_left h1 hW
    nlinarith [Nat.cast_nonneg (α := ℝ) (ℓ + (n + 1) + 1)]

/-- The representation of the single term `(e_k^* G y)(u^* G e_l) Π pre`: the rest is `pre`, at
the index `(k, l)`. -/
private lemma FAQ_Rep_init {D N : ℕ} (V : Set (Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (Y U : Idx D N → Idx D N → ℂ)
    (k l : Idx D N) (pre : ResMono D N) (ℓ : ℕ) (hpre : FAQ_good V Λ z ℓ [(1, pre)]) :
    FAQ_Rep V Λ z h i j Y U (fun m w => resPolyEval [(1, (Pi.single k 1, Y m, Λ, z) ::
      (U m, Pi.single l 1, Λ, z) :: pre)] (setEntry h i j w)) ℓ 1 := by
  refine ⟨fun p q => if p = k ∧ q = l then [(1, pre)] else [], ?_, ?_, ?_⟩
  · intro p q
    by_cases hpq : p = k ∧ q = l
    · simpa [hpq] using hpre
    · simp [hpq, FAQ_good]
  · have : ∀ p q : Idx D N, FAQ_wt (if p = k ∧ q = l then [((1 : ℂ), pre)] else []) =
        if p = k ∧ q = l then 1 else 0 := by
      intro p q
      split_ifs <;> simp [FAQ_wt]
    simp only [this]
    have hone : ∑ p : Idx D N, ∑ q : Idx D N, (if p = k ∧ q = l then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single k]
      · rw [Finset.sum_eq_single l]
        · simp
        · intro q _ hq
          simp [hq]
        · simp
      · intro p _ hp
        simp [hp]
      · simp
    rw [hone]
  · intro m w
    rw [FAQ_eval_big]
    have hR0 : ∀ p q : Idx D N, resPolyEval (if p = k ∧ q = l then [((1 : ℂ), pre)] else [])
        (setEntry h i j w) = if p = k ∧ q = l then resMonoEval pre (setEntry h i j w) else 0 := by
      intro p q
      split_ifs <;> simp [resPolyEval]
    simp only [hR0]
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single l]
      · simp only [and_self, ite_true, resPolyEval, resMonoEval, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.prod_cons, add_zero, one_mul]
        ring
      · intro q _ hq
        simp [hq]
      · simp
    · intro p _ hp
      simp [hp]
    · simp

/-- The bound on a representation: `Σ_m |F_m(w)| ≤ W Γ^ℓ A` when the forms are at most `Γ` and the
two families of `m`-dependent vectors satisfy a Ward bound `A`. -/
private lemma FAQ_Rep_bound {D N : ℕ} (V : Set (Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (hi : (Pi.single i 1 : Idx D N → ℂ) ∈ V) (hj : (Pi.single j 1 : Idx D N → ℂ) ∈ V)
    (Y U : Idx D N → Idx D N → ℂ) (F : Idx D N → ℂ → ℂ) (ℓ : ℕ) (W : ℝ)
    (hR : FAQ_Rep V Λ z h i j Y U F ℓ W) (Γ A : ℝ) (hΓ : 1 ≤ Γ) (w : ℂ)
    (hG : ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h i j w)‖ ≤ Γ)
    (hY : ∀ p, ∑ m, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ ^ 2 ≤ A)
    (hU : ∀ q, ∑ m, ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ ^ 2 ≤ A) :
    ∑ m, ‖F m w‖ ≤ W * Γ ^ ℓ * A := by
  obtain ⟨R, hgood, hwt, hF⟩ := hR
  have hA : 0 ≤ A := le_trans (Finset.sum_nonneg fun m _ => by positivity) (hY i)
  have hΓ0 : 0 ≤ Γ ^ ℓ := pow_nonneg (by linarith) _
  have hE : ∀ p q, ‖resPolyEval (R p q) (setEntry h i j w)‖ ≤ FAQ_wt (R p q) * Γ ^ ℓ := by
    intro p q
    have := resPoly_wirt_le h hh i j V {(Λ, z)} hi hj
      (by intro p hp; rw [Set.mem_singleton_iff.mp hp]; exact ⟨hΛ, hz.ne'⟩) (R p q) ℓ
      (fun t ht => ⟨(hgood p q t ht).1, fun f hf => by
        obtain ⟨h1, h2, h3⟩ := (hgood p q t ht).2 f hf
        exact ⟨h1, h2, Set.mem_singleton_iff.mpr h3⟩⟩) Γ hΓ w
      (by intro p hp x hx y hy; rw [Set.mem_singleton_iff.mp hp]; exact hG x hx y hy) 0 0
    simpa [wirt, FAQ_wt] using this
  have hm : ∀ m, ‖F m w‖ ≤ ∑ p, ∑ q, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ *
      ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ *
        ‖resPolyEval (R p q) (setEntry h i j w)‖ := by
    intro m
    rw [hF, FAQ_eval_big]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, norm_mul]
  have hcs : ∀ p q : Idx D N, ∑ m, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ *
      ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ ≤ A := by
    intro p q
    have h1 : ∀ m, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ *
        ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ ≤
        (‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ ^ 2 +
          ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ ^ 2) / 2 := by
      intro m
      nlinarith [sq_nonneg (‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ -
        ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖)]
    refine (Finset.sum_le_sum fun m _ => h1 m).trans ?_
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [hY p, hU q]
  calc ∑ m, ‖F m w‖
      ≤ ∑ m, ∑ p, ∑ q, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ *
        ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ *
          ‖resPolyEval (R p q) (setEntry h i j w)‖ := Finset.sum_le_sum fun m _ => hm m
    _ = ∑ p, ∑ q, ‖resPolyEval (R p q) (setEntry h i j w)‖ *
        ∑ m, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ *
          ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ ∑ p, ∑ q, FAQ_wt (R p q) * Γ ^ ℓ * A := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        exact mul_le_mul (hE p q) (hcs p q) (Finset.sum_nonneg fun m _ => by positivity)
          (mul_nonneg (FAQ_wt_nonneg _) hΓ0)
    _ = (∑ p, ∑ q, FAQ_wt (R p q)) * Γ ^ ℓ * A := by
        simp only [← Finset.sum_mul]
    _ ≤ W * Γ ^ ℓ * A := by
        have := mul_nonneg hΓ0 hA
        nlinarith

/-- The derivative bound for a family of two `m`-dependent factors with Ward bounds: for the term
`(e_k^* G y_m)(u_m^* G e_l) Π pre` and `a` derivatives `∂_w` after `b` derivatives `∂_{w̄}`,
`Σ_m |∂_w^a ∂_{w̄}^b (·)| ≤ (ℓ₀ + b + 1)^b (ℓ₀ + a + b + 1)^a Γ^{ℓ₀ + a + b} A`. -/
private lemma FAQ_core {D N : ℕ} (V : Set (Idx D N → ℂ))
    (hV : ∀ p : Idx D N, (Pi.single p 1 : Idx D N → ℂ) ∈ V)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (Y U : Idx D N → Idx D N → ℂ) (k l : Idx D N) (pre : ResMono D N) (ℓ₀ : ℕ)
    (hpre : FAQ_good V Λ z ℓ₀ [(1, pre)]) (Γ A : ℝ) (hΓ : 1 ≤ Γ) (w : ℂ)
    (hG : ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h i j w)‖ ≤ Γ)
    (hY : ∀ p, ∑ m, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ ^ 2 ≤ A)
    (hU : ∀ q, ∑ m, ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ ^ 2 ≤ A)
    (a b : ℕ) :
    ∑ m, ‖wirt a b (fun w' => resPolyEval [(1, (Pi.single k 1, Y m, Λ, z) ::
        (U m, Pi.single l 1, Λ, z) :: pre)] (setEntry h i j w')) w‖ ≤
      ((ℓ₀ + b + 1 : ℕ) : ℝ) ^ b * ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ^ a * Γ ^ (ℓ₀ + b + a) * A := by
  have hc : ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs
    · norm_num
    · simp
  have hR0 := FAQ_Rep_init V Λ z h i j Y U k l pre ℓ₀ hpre
  have hpair : ∀ P : ResPoly D N, (∀ t ∈ P, ∀ f ∈ t.2, f.2.2 = (Λ, z)) →
      ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro P hP t ht f hf
    rw [hP t ht f hf]
    exact ⟨hΛ, hz.ne'⟩
  have hR1 := FAQ_Rep_iter V hV Λ z h i j Y U _ j i (if i = j then 1 / 2 else 1) hc dWbar
    (fun P hP => (resPoly_dW h hh i j P (hpair P hP)).2) ℓ₀ 1 hR0 b
  have hR2 := FAQ_Rep_iter V hV Λ z h i j Y U _ i j (if i = j then 1 / 2 else 1) hc dW
    (fun P hP => (resPoly_dW h hh i j P (hpair P hP)).1) (ℓ₀ + b) _ hR1 a
  have hb := FAQ_Rep_bound V Λ hΛ z hz h hh i j (hV i) (hV j) Y U _ _ _ hR2 Γ A hΓ w hG hY hU
  simpa [wirt, mul_assoc] using hb

/-! ### The Ward bounds for the `m`-dependent vectors -/

open scoped Matrix.Norms.L2Operator in
/-- `Σ_k |(T u)_k|² ≤ ‖T‖² Σ_k |u_k|²`. -/
private lemma FAQ_mulVec_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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
private lemma FAQ_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) : opNorm Tᴴ = opNorm T := by
  change ‖Tᴴ‖ = ‖T‖
  exact Matrix.l2_opNorm_conjTranspose T

/-- Ward's identity (2.32) [eq_Ward] for the forms of the standard basis and the vectors `B e_m`,
`Λ e_m`: for `‖B‖, ‖Λ‖ ≤ 1` each of the four sums `Σ_m |form|²` is at most `Υ / η` when
`Im G_{pp} ≤ Υ`. -/
private lemma FAQ_ward {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (hB : opNorm B ≤ 1) (hΛn : opNorm Λ ≤ 1) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (Υ : ℝ)
    (hIm : ∀ p : Idx D N, (res (Matrix.of h + Λ) z p p).im ≤ Υ) :
    (∀ p, ∑ m, ‖resFactorEval (Pi.single p 1, Pi.single m 1, Λ, z) h‖ ^ 2 ≤ Υ / z.im) ∧
    (∀ p, ∑ m, ‖resFactorEval (Pi.single p 1, B *ᵥ Pi.single m 1, Λ, z) h‖ ^ 2 ≤ Υ / z.im) ∧
    (∀ q, ∑ m, ‖resFactorEval (Pi.single m 1, Pi.single q 1, Λ, z) h‖ ^ 2 ≤ Υ / z.im) ∧
    (∀ q, ∑ m, ‖resFactorEval (Λ *ᵥ Pi.single m 1, Pi.single q 1, Λ, z) h‖ ^ 2 ≤ Υ / z.im) := by
  set G := res (Matrix.of h + Λ) z with hG
  have hX : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  have hw := fun p => ward_diag (Matrix.of h + Λ) hX z hz p
  have hrow : ∀ p, ∑ m, ‖G p m‖ ^ 2 ≤ Υ / z.im := fun p => by
    rw [(hw p).2]
    exact div_le_div_of_nonneg_right (hIm p) hz.le
  have hcol : ∀ q, ∑ m, ‖G m q‖ ^ 2 ≤ Υ / z.im := fun q => by
    rw [(hw q).1]
    exact div_le_div_of_nonneg_right (hIm q) hz.le
  refine ⟨fun p => ?_, fun p => ?_, fun q => ?_, fun q => ?_⟩
  · simpa only [FAQ_f_ee] using hrow p
  · simp only [FAQ_f_eM]
    have key := FAQ_mulVec_sq Bᴴ (fun s => starRingEnd ℂ (G p s))
    have e : ∀ m, ‖(Bᴴ *ᵥ fun s => starRingEnd ℂ (G p s)) m‖ = ‖(G * B) p m‖ := by
      intro m
      rw [← Complex.norm_conj, Matrix.mulVec, dotProduct, map_sum, Matrix.mul_apply]
      refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
      simp [Matrix.conjTranspose_apply, mul_comm]
    simp only [e, Complex.norm_conj, FAQ_opNorm_conjTranspose] at key
    refine key.trans ?_
    have h0 : 0 ≤ ∑ k, ‖G p k‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hB0 : 0 ≤ opNorm B := norm_nonneg _
    calc opNorm B ^ 2 * ∑ k, ‖G p k‖ ^ 2 ≤ 1 * (Υ / z.im) :=
          mul_le_mul (by nlinarith) (hrow p) h0 zero_le_one
      _ = Υ / z.im := one_mul _
  · simpa only [FAQ_f_ee] using hcol q
  · simp only [FAQ_f_Le Λ hΛ]
    have key := FAQ_mulVec_sq Λ (fun s => G s q)
    have e : ∀ m, (Λ *ᵥ fun s => G s q) m = (Λ * G) m q := by
      intro m
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    simp only [e] at key
    refine key.trans ?_
    have h0 : 0 ≤ ∑ k, ‖G k q‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hΛ0 : 0 ≤ opNorm Λ := norm_nonneg _
    calc opNorm Λ ^ 2 * ∑ k, ‖G k q‖ ^ 2 ≤ 1 * (Υ / z.im) :=
          mul_le_mul (by nlinarith) (hcol q) h0 zero_le_one
      _ = Υ / z.im := one_mul _

/-! ### Iterated derivatives of the polynomial of `Q_{kl}` -/

/-- `a` derivatives `∂_w` after `b` derivatives `∂_{w̄}`, at the level of polynomials. -/
private def FAQ_Tit {D N : ℕ} (i j : Idx D N) (c : ℂ) (a b : ℕ) (P : ResPoly D N) :
    ResPoly D N :=
  (resPolyD i j c)^[a] ((resPolyD j i c)^[b] P)

/-- Iterated derivatives of a concatenation. -/
private lemma FAQ_iter_append {D N : ℕ} (a b : Idx D N) (c : ℂ) (n : ℕ) (P Q : ResPoly D N) :
    (resPolyD a b c)^[n] (P ++ Q) = (resPolyD a b c)^[n] P ++ (resPolyD a b c)^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, FAQ_resPolyD_append,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- Iterated derivatives of a sum over the index set. -/
private lemma FAQ_iter_sum {D N : ℕ} (a b : Idx D N) (c : ℂ) (n : ℕ) (g : Idx D N → ResPoly D N) :
    (resPolyD a b c)^[n] (FAQ_sum g) = FAQ_sum (fun x => (resPolyD a b c)^[n] (g x)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, FAQ_resPolyD_sum]

/-- The iterated derivatives of a concatenation. -/
private lemma FAQ_Tit_append {D N : ℕ} (i j : Idx D N) (c : ℂ) (a b : ℕ) (P Q : ResPoly D N) :
    FAQ_Tit i j c a b (P ++ Q) = FAQ_Tit i j c a b P ++ FAQ_Tit i j c a b Q := by
  unfold FAQ_Tit
  rw [FAQ_iter_append, FAQ_iter_append]

/-- The iterated derivatives of a sum over the index set. -/
private lemma FAQ_Tit_sum {D N : ℕ} (i j : Idx D N) (c : ℂ) (a b : ℕ) (g : Idx D N → ResPoly D N) :
    FAQ_Tit i j c a b (FAQ_sum g) = FAQ_sum (fun x => FAQ_Tit i j c a b (g x)) := by
  unfold FAQ_Tit
  rw [FAQ_iter_sum, FAQ_iter_sum]

/-- The value of a polynomial whose coefficients are multiplied by `κ`. -/
private lemma FAQ_eval_smul {D N : ℕ} (κ : ℂ) (P : ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (P.map fun t => (κ * t.1, t.2)) h = κ * resPolyEval P h := by
  induction P with
  | nil => simp [resPolyEval]
  | cons t P ih =>
    rw [List.map_cons, FAQ_eval_cons, FAQ_eval_cons, ih]
    ring

/-- The derivative commutes with multiplying the coefficients by `κ`. -/
private lemma FAQ_resPolyD_smul {D N : ℕ} (a b : Idx D N) (c κ : ℂ) (P : ResPoly D N) :
    resPolyD a b c (P.map fun t => (κ * t.1, t.2)) =
      (resPolyD a b c P).map fun t => (κ * t.1, t.2) := by
  induction P with
  | nil => simp [resPolyD]
  | cons t P ih =>
    rw [List.map_cons, FAQ_resPolyD_cons', ih, FAQ_resPolyD_cons', List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    simp [mul_assoc]

/-- Iterated derivatives commute with multiplying the coefficients by `κ`. -/
private lemma FAQ_iter_smul {D N : ℕ} (a b : Idx D N) (c κ : ℂ) (n : ℕ) (P : ResPoly D N) :
    (resPolyD a b c)^[n] (P.map fun t => (κ * t.1, t.2)) =
      ((resPolyD a b c)^[n] P).map fun t => (κ * t.1, t.2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, FAQ_resPolyD_smul,
      Function.iterate_succ_apply']

/-- The iterated derivatives of a single term are linear in its coefficient. -/
private lemma FAQ_eval_Tit_single {D N : ℕ} (i j : Idx D N) (c : ℂ) (a b : ℕ) (κ : ℂ)
    (M : ResMono D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FAQ_Tit i j c a b [(κ, M)]) h =
      κ * resPolyEval (FAQ_Tit i j c a b [(1, M)]) h := by
  have e : ([(κ, M)] : ResPoly D N) = [((1 : ℂ), M)].map fun t => (κ * t.1, t.2) := by simp
  unfold FAQ_Tit
  rw [e, FAQ_iter_smul, FAQ_iter_smul, FAQ_eval_smul]

/-- The bound for one family `Σ_m cf_m (e_k^* G y_m)(u_m^* G e_l) Π pre` after `a` derivatives
`∂_w` and `b` derivatives `∂_{w̄}`, for `|cf_m| ≤ κ`. -/
private lemma FAQ_item_bound {D N : ℕ} (V : Set (Idx D N → ℂ))
    (hV : ∀ p : Idx D N, (Pi.single p 1 : Idx D N → ℂ) ∈ V)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (Y U : Idx D N → Idx D N → ℂ) (k l : Idx D N) (pre : ResMono D N) (ℓ₀ : ℕ)
    (hpre : FAQ_good V Λ z ℓ₀ [(1, pre)]) (Γ A : ℝ) (hΓ : 1 ≤ Γ) (w : ℂ)
    (hG : ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h i j w)‖ ≤ Γ)
    (hY : ∀ p, ∑ m, ‖resFactorEval (Pi.single p 1, Y m, Λ, z) (setEntry h i j w)‖ ^ 2 ≤ A)
    (hU : ∀ q, ∑ m, ‖resFactorEval (U m, Pi.single q 1, Λ, z) (setEntry h i j w)‖ ^ 2 ≤ A)
    (a b : ℕ) (cf : Idx D N → ℂ) (κ : ℝ) (hκ : ∀ m, ‖cf m‖ ≤ κ) :
    ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
        (FAQ_sum fun m => [(cf m, (Pi.single k 1, Y m, Λ, z) ::
          (U m, Pi.single l 1, Λ, z) :: pre)])) (setEntry h i j w)‖ ≤
      κ * (((ℓ₀ + b + 1 : ℕ) : ℝ) ^ b * ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ^ a * Γ ^ (ℓ₀ + b + a) * A) := by
  have hcore := FAQ_core V hV Λ hΛ z hz h hh i j Y U k l pre ℓ₀ hpre Γ A hΓ w hG hY hU a b
  rw [FAQ_Tit_sum, FAQ_eval_sum]
  refine (norm_sum_le _ _).trans ?_
  have hm : ∀ m, ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
      [(cf m, (Pi.single k 1, Y m, Λ, z) :: (U m, Pi.single l 1, Λ, z) :: pre)])
        (setEntry h i j w)‖ ≤ κ * ‖wirt a b (fun w' => resPolyEval
          [(1, (Pi.single k 1, Y m, Λ, z) :: (U m, Pi.single l 1, Λ, z) :: pre)]
          (setEntry h i j w')) w‖ := by
    intro m
    have hP : ∀ t ∈ ([(1, (Pi.single k 1, Y m, Λ, z) :: (U m, Pi.single l 1, Λ, z) :: pre)] :
        ResPoly D N), ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
      intro t ht f hf
      rw [List.mem_singleton] at ht
      subst ht
      simp only [List.mem_cons] at hf
      rcases hf with rfl | rfl | hf
      · exact ⟨hΛ, hz.ne'⟩
      · exact ⟨hΛ, hz.ne'⟩
      · rw [((hpre (1, pre) List.mem_cons_self).2 f hf).2.2]
        exact ⟨hΛ, hz.ne'⟩
    have hw := congrFun (resPoly_wirt h hh i j _ hP a b) w
    rw [FAQ_eval_Tit_single, norm_mul]
    have e : resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
        [(1, (Pi.single k 1, Y m, Λ, z) :: (U m, Pi.single l 1, Λ, z) :: pre)]) (setEntry h i j w) =
        wirt a b (fun w' => resPolyEval [(1, (Pi.single k 1, Y m, Λ, z) ::
          (U m, Pi.single l 1, Λ, z) :: pre)] (setEntry h i j w')) w := hw.symm
    rw [e]
    exact mul_le_mul_of_nonneg_right (hκ m) (norm_nonneg _)
  calc ∑ m, ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
        [(cf m, (Pi.single k 1, Y m, Λ, z) :: (U m, Pi.single l 1, Λ, z) :: pre)])
          (setEntry h i j w)‖
      ≤ ∑ m, κ * ‖wirt a b (fun w' => resPolyEval [(1, (Pi.single k 1, Y m, Λ, z) ::
          (U m, Pi.single l 1, Λ, z) :: pre)] (setEntry h i j w')) w‖ :=
        Finset.sum_le_sum fun m _ => hm m
    _ = κ * ∑ m, ‖wirt a b (fun w' => resPolyEval [(1, (Pi.single k 1, Y m, Λ, z) ::
          (U m, Pi.single l 1, Λ, z) :: pre)] (setEntry h i j w')) w‖ := by
        rw [Finset.mul_sum]
    _ ≤ κ * (((ℓ₀ + b + 1 : ℕ) : ℝ) ^ b * ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ^ a * Γ ^ (ℓ₀ + b + a) *
        A) := by
        refine mul_le_mul_of_nonneg_left hcore ?_
        exact (norm_nonneg _).trans (hκ k)

/-- The value of the iterated derivatives of a sum over the index set. -/
private lemma FAQ_eval_Tit_sum {D N : ℕ} (i j : Idx D N) (c : ℂ) (a b : ℕ)
    (g : Idx D N → ResPoly D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FAQ_Tit i j c a b (FAQ_sum g)) h =
      ∑ x, resPolyEval (FAQ_Tit i j c a b (g x)) h := by
  rw [FAQ_Tit_sum, FAQ_eval_sum]

/-- The coefficient `(DN)⁻¹ κ(r, m)` is at most `(DN)⁻¹ N⁻¹` in modulus for `θ ∈ [0, 1]`. -/
private lemma FAQ_norm_coef_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 0 < D)
    (hN : 0 < N) (r m : Idx D N) :
    ‖((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r m‖ ≤ ((D : ℝ) * N)⁻¹ * (N : ℝ)⁻¹ := by
  rw [norm_mul, FAQ_norm_inv, FAQ_kap_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (FAQ_kapR_nonneg D N θ hθ0 hθ1 r m)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
    nlinarith [inv_pos.mpr hN0]
  unfold FAQ_kapR
  have h2 : 0 ≤ 1 - θ := by linarith
  split_ifs
  · nlinarith [inv_pos.mpr hN0]
  · nlinarith [inv_pos.mpr hN0]

/-- The counting constants of the derivative bound are at most `(a + b + 2)^{a+b} Γ^{a+b+1}` when
the rest has at most one factor. -/
private lemma FAQ_core_le (a b ℓ₀ : ℕ) (hℓ : ℓ₀ ≤ 1) (Γ : ℝ) (hΓ : 1 ≤ Γ) :
    ((ℓ₀ + b + 1 : ℕ) : ℝ) ^ b * ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ^ a * Γ ^ (ℓ₀ + b + a) ≤
      ((a + b + 2 : ℕ) : ℝ) ^ (a + b) * Γ ^ (a + b + 1) := by
  have hx : ((ℓ₀ + b + 1 : ℕ) : ℝ) ≤ ((a + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : ℓ₀ + b + 1 ≤ a + b + 2)
  have hy : ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ≤ ((a + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : ℓ₀ + b + a + 1 ≤ a + b + 2)
  have h1 : ((ℓ₀ + b + 1 : ℕ) : ℝ) ^ b ≤ ((a + b + 2 : ℕ) : ℝ) ^ b :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hx b
  have h2 : ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ^ a ≤ ((a + b + 2 : ℕ) : ℝ) ^ a :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hy a
  have h3 : Γ ^ (ℓ₀ + b + a) ≤ Γ ^ (a + b + 1) := pow_le_pow_right₀ hΓ (by omega)
  have e : ((a + b + 2 : ℕ) : ℝ) ^ (a + b) =
      ((a + b + 2 : ℕ) : ℝ) ^ b * ((a + b + 2 : ℕ) : ℝ) ^ a := by
    rw [← pow_add, Nat.add_comm b a]
  rw [e]
  have hΓ0 : (0 : ℝ) ≤ Γ := by linarith
  exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity)
    (by positivity)

/-- The first Wirtinger derivatives of `⟨B H̲G⟩` of (2.30) [eq:HGline] along a Hermitian slice:
`∂_w = c ((DN)⁻¹ (G B)_{ji} - Q_{ji})` and `∂_{w̄} = c ((DN)⁻¹ (G B)_{ij} - Q_{ij})`, with `c = 1`
for `i ≠ j` and `c = 1/2` for `i = j`. -/
theorem ntr_hgUnder_dW (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    dW (fun w' => ntr (B * hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z)) w =
        (if i = j then 1 / 2 else 1) *
          (((D : ℂ) * N)⁻¹ * (res (Matrix.of (setEntry h i j w) + Λ) z * B) j i -
            qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z j i) ∧
      dWbar (fun w' => ntr (B * hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z)) w =
        (if i = j then 1 / 2 else 1) *
          (((D : ℂ) * N)⁻¹ * (res (Matrix.of (setEntry h i j w) + Λ) z * B) i j -
            qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z i j) := by
  have hPF : ∀ t ∈ FAQ_PF D N θ Λ B z, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t ht f hf
    rw [FAQ_PF_pair D N θ Λ B z t ht f hf]
    exact ⟨hΛ, hz.ne'⟩
  have hfun : (fun w' => ntr (B * hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z)) =
      fun w' => resPolyEval (FAQ_PF D N θ Λ B z) (setEntry h i j w') := by
    funext w'
    rw [FAQ_eval_PF, FAQ_hgUnder_eq D N θ _ Λ (FAQ_slice_herm h hh i j w') hΛ z hz]
  rw [hfun]
  obtain ⟨h1, h2⟩ := resPoly_dW h hh i j (FAQ_PF D N θ Λ B z) hPF
  rw [h1, h2]
  exact ⟨FAQ_eval_dPF D N θ Λ B hΛ z hz i j _ _ (FAQ_slice_herm h hh i j w),
    FAQ_eval_dPF D N θ Λ B hΛ z hz j i _ _ (FAQ_slice_herm h hh i j w)⟩

/-- Each entry `Q_{kl}` is, on Hermitian arrays, a resolvent polynomial in `G(z)` of degree `≤ 3`
over `avgVecs`, with weight `≤ 4(1 + |z|)`. -/
theorem qMat_resPoly (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (k l : Idx D N) :
    ∃ P : ResPoly D N, (∀ t ∈ P, t.2.length ≤ 3 ∧ ∀ f ∈ t.2,
        f.1 ∈ avgVecs D N Λ B ∧ f.2.1 ∈ avgVecs D N Λ B ∧ f.2.2 = (Λ, z)) ∧
      (P.map fun t => ‖t.1‖).sum ≤ 4 * (1 + ‖z‖) ∧
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        resPolyEval P h = qMat D N θ (Matrix.of h) Λ B z k l := by
  refine ⟨FAQ_PQ D N θ Λ B z k l, FAQ_PQ_good D N θ Λ B z k l,
    FAQ_wt_PQ_le D N θ hθ0 hθ1 Λ B z k l, ?_⟩
  intro h hh
  exact FAQ_eval_PQ D N θ Λ B hΛ z hz k l h hh

/-- The derivatives of `Q` on the good event: for fixed `D, a, b` there is `c` such that, for
`‖B‖ ≤ 1`, `1 ≤ Γ`, `η ≤ Υ` and `setEntry h i j w` in the good event on `avgVecs`,
`|∂_w^a ∂_{w̄}^b Q_{kl}(w)| ≤ c (1 + |z|) Γ^{a+b+1} Υ/(Nη)`. -/
theorem qMat_wirt_le (D a b : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (N : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, 0 < z.im → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (w : ℂ) (k l : Idx D N) (Γ Υ : ℝ), 1 ≤ Γ → z.im ≤ Υ →
      setEntry h i j w ∈ goodSet Λ z (avgVecs D N Λ B) Γ Υ →
      ‖wirt a b (fun w' => qMat D N θ (Matrix.of (setEntry h i j w')) Λ B z k l) w‖ ≤
        c * (1 + ‖z‖) * Γ ^ (a + b + 1) * (Υ / ((N : ℝ) * z.im)) := by
  refine ⟨4 * ((a + b + 2 : ℕ) : ℝ) ^ (a + b), by positivity, ?_⟩
  intro N θ hθ0 hθ1 Λ hΛ hΛn B hB z hz h hh i j w k l Γ Υ hΓ hΥ hgood
  have hD : 0 < D := k.1.pos
  have hN : 0 < N := k.2.pos
  have hV : ∀ p : Idx D N, (Pi.single p 1 : Idx D N → ℂ) ∈
      (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) := fun p => FAQ_e_mem D N Λ B p
  have hhH : (Matrix.of (setEntry h i j w)).IsHermitian := FAQ_slice_herm h hh i j w
  have hG : ∀ x ∈ (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)),
      ∀ y ∈ (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)),
      ‖resFactorEval (x, y, Λ, z) (setEntry h i j w)‖ ≤ Γ := fun x hx y hy => (hgood x hx y hy).1
  have hIm : ∀ p : Idx D N, (res (Matrix.of (setEntry h i j w) + Λ) z p p).im ≤ Υ := by
    intro p
    have h1 := (hgood _ (hV p) _ (hV p)).2
    have h2 : star (Pi.single p 1 : Idx D N → ℂ) ⬝ᵥ
        (res (Matrix.of (setEntry h i j w) + Λ) z *ᵥ Pi.single p 1) =
        res (Matrix.of (setEntry h i j w) + Λ) z p p := FAQ_f_ee Λ z (setEntry h i j w) p p
    rwa [h2] at h1
  obtain ⟨hw1, hw2, hw3, hw4⟩ :=
    FAQ_ward Λ B hΛ hB (hΛn.trans (by norm_num)) z hz _ hhH Υ hIm
  have hA1 : 1 ≤ Υ / z.im := by rw [le_div_iff₀ hz]; linarith
  have hPpair : ∀ t ∈ FAQ_PQ D N θ Λ B z k l, ∀ f ∈ t.2,
      f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t ht f hf
    rw [((FAQ_PQ_good D N θ Λ B z k l t ht).2 f hf).2.2]
    exact ⟨hΛ, hz.ne'⟩
  have hfun : (fun w' => qMat D N θ (Matrix.of (setEntry h i j w')) Λ B z k l) =
      fun w' => resPolyEval (FAQ_PQ D N θ Λ B z k l) (setEntry h i j w') :=
    funext fun w' => (FAQ_eval_PQ D N θ Λ B hΛ z hz k l _ (FAQ_slice_herm h hh i j w')).symm
  rw [hfun]
  have hw := congrFun (resPoly_wirt h hh i j (FAQ_PQ D N θ Λ B z k l) hPpair a b) w
  rw [hw]
  change ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b (FAQ_PQ D N θ Λ B z k l))
    (setEntry h i j w)‖ ≤ _
  unfold FAQ_PQ
  rw [FAQ_Tit_append, FAQ_Tit_append, FAQ_Tit_append, FAQ_Tit_append]
  simp only [resPolyEval_append]
  rw [FAQ_eval_Tit_sum (g := FAQ_P4r D N θ B Λ z k l),
    FAQ_eval_Tit_sum (g := FAQ_P5r D N θ B Λ z k l)]
  set A : ℝ := Υ / z.im with hAdef
  set M : ℝ := ((a + b + 2 : ℕ) : ℝ) ^ (a + b) with hMdef
  set ν : ℝ := ((D : ℝ) * N)⁻¹ with hν
  have hM0 : 0 ≤ M := by positivity
  have hΓ0 : 0 ≤ Γ := by linarith
  have hGm : 0 ≤ Γ ^ (a + b + 1) := by positivity
  have hA0 : 0 ≤ A := by linarith
  have hν0 : 0 ≤ ν := by positivity
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hνN : ν ≤ (N : ℝ)⁻¹ := by
    rw [hν, mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
    nlinarith [inv_pos.mpr hN0]
  have hcore : ∀ ℓ₀ : ℕ, ℓ₀ ≤ 1 → ((ℓ₀ + b + 1 : ℕ) : ℝ) ^ b * ((ℓ₀ + b + a + 1 : ℕ) : ℝ) ^ a *
      Γ ^ (ℓ₀ + b + a) * A ≤ M * Γ ^ (a + b + 1) * A := fun ℓ₀ hℓ =>
    mul_le_mul_of_nonneg_right (FAQ_core_le a b ℓ₀ hℓ Γ hΓ) hA0
  have hpre0 : FAQ_good (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) Λ z 0
      [(1, ([] : ResMono D N))] := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨le_refl _, fun f hf => by simp at hf⟩
  have hnorm : ‖((D : ℂ) * N)⁻¹‖ = ν := FAQ_norm_inv D N
  -- the first group: one form
  have b1 : ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b (FAQ_P1 D N B Λ z k l))
      (setEntry h i j w)‖ ≤ ν * (M * Γ ^ (a + b + 1)) := by
    have hP1 : ∀ t ∈ FAQ_P1 D N B Λ z k l, ∀ f ∈ t.2,
        f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
      intro t ht f hf
      simp only [FAQ_P1, List.mem_singleton] at ht
      subst ht
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨hΛ, hz.ne'⟩
    have hw1' := congrFun (resPoly_wirt h hh i j (FAQ_P1 D N B Λ z k l) hP1 a b) w
    have e : resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b (FAQ_P1 D N B Λ z k l))
        (setEntry h i j w) = wirt a b (fun w' => resPolyEval (FAQ_P1 D N B Λ z k l)
          (setEntry h i j w')) w := hw1'.symm
    rw [e]
    have hle := resPoly_wirt_le h hh i j (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) {(Λ, z)}
      (hV i) (hV j) (by intro p hp; rw [Set.mem_singleton_iff.mp hp]; exact ⟨hΛ, hz.ne'⟩)
      (FAQ_P1 D N B Λ z k l) 1
      (by
        intro t ht
        simp only [FAQ_P1, List.mem_singleton] at ht
        subst ht
        refine ⟨le_refl _, fun f hf => ?_⟩
        simp only [List.mem_singleton] at hf
        subst hf
        exact ⟨hV k, FAQ_Be_mem D N Λ B l, Set.mem_singleton _⟩)
      Γ hΓ w
      (by intro p hp x hx y hy; rw [Set.mem_singleton_iff.mp hp]; exact hG x hx y hy) a b
    have hwt : ((FAQ_P1 D N B Λ z k l).map fun t => ‖t.1‖).sum = ν := by
      have := FAQ_wt_single ((D : ℂ) * N)⁻¹ ([(Pi.single k 1, B *ᵥ Pi.single l 1, Λ, z)] :
        ResMono D N)
      rw [hnorm] at this
      exact this
    rw [hwt] at hle
    refine hle.trans ?_
    have h1 : ((1 + a + b : ℕ) : ℝ) ^ (a + b) ≤ M := by
      rw [hMdef]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast (by omega : 1 + a + b ≤ a + b + 2)) _
    have h2 : Γ ^ (1 + a + b) = Γ ^ (a + b + 1) := by rw [show 1 + a + b = a + b + 1 by omega]
    rw [h2]
    calc ((1 + a + b : ℕ) : ℝ) ^ (a + b) * ν * Γ ^ (a + b + 1)
        = ν * (((1 + a + b : ℕ) : ℝ) ^ (a + b) * Γ ^ (a + b + 1)) := by ring
      _ ≤ ν * (M * Γ ^ (a + b + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hGm) hν0
  -- the second group
  have b2 : ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b (FAQ_P2 D N B Λ z k l))
      (setEntry h i j w)‖ ≤ ν * (M * Γ ^ (a + b + 1) * A) := by
    have := FAQ_item_bound (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) hV Λ hΛ z hz h hh i j
      (fun m => B *ᵥ Pi.single m 1) (fun m => Λ *ᵥ Pi.single m 1) k l [] 0 hpre0 Γ A hΓ w hG hw2
      hw4 a b (fun _ => -((D : ℂ) * N)⁻¹) ν (fun m => by
        show ‖-((D : ℂ) * N)⁻¹‖ ≤ ν
        rw [norm_neg, hnorm])
    exact this.trans (mul_le_mul_of_nonneg_left (hcore 0 (by norm_num)) hν0)
  -- the third group
  have b3 : ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b (FAQ_P3 D N B Λ z k l))
      (setEntry h i j w)‖ ≤ (ν * ‖z‖) * (M * Γ ^ (a + b + 1) * A) := by
    have := FAQ_item_bound (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) hV Λ hΛ z hz h hh i j
      (fun m => B *ᵥ Pi.single m 1) (fun m => Pi.single m 1) k l [] 0 hpre0 Γ A hΓ w hG hw2
      hw3 a b (fun _ => z * ((D : ℂ) * N)⁻¹) (ν * ‖z‖) (fun m => by
        show ‖z * ((D : ℂ) * N)⁻¹‖ ≤ ν * ‖z‖
        rw [norm_mul, hnorm, mul_comm])
    exact this.trans (mul_le_mul_of_nonneg_left (hcore 0 (by norm_num)) (by positivity))
  -- the fourth group
  have b4 : ∀ r : Idx D N, ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
      (FAQ_P4r D N θ B Λ z k l r)) (setEntry h i j w)‖ ≤ (ν * (N : ℝ)⁻¹) *
        (M * Γ ^ (a + b + 1) * A) := by
    intro r
    have hpre1 : FAQ_good (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) Λ z 1
        [(1, ([(Pi.single r 1, Pi.single r 1, Λ, z)] : ResMono D N))] := by
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      refine ⟨le_refl _, fun f hf => ?_⟩
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨hV r, hV r, rfl⟩
    have := FAQ_item_bound (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) hV Λ hΛ z hz h hh i j
      (fun m => B *ᵥ Pi.single m 1) (fun m => Pi.single m 1) k l _ 1 hpre1 Γ A hΓ w hG hw2
      hw3 a b (fun m => ((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r m) (ν * (N : ℝ)⁻¹)
      (fun m => by
        have := FAQ_norm_coef_le D N θ hθ0 hθ1 hD hN r m
        rwa [hν])
    exact this.trans (mul_le_mul_of_nonneg_left (hcore 1 le_rfl) (by positivity))
  -- the fifth group
  have b5 : ∀ r : Idx D N, ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
      (FAQ_P5r D N θ B Λ z k l r)) (setEntry h i j w)‖ ≤ (ν * (N : ℝ)⁻¹) *
        (M * Γ ^ (a + b + 1) * A) := by
    intro r
    have hpre1 : FAQ_good (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) Λ z 1
        [(1, ([(Pi.single r 1, B *ᵥ Pi.single r 1, Λ, z)] : ResMono D N))] := by
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      refine ⟨le_refl _, fun f hf => ?_⟩
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨hV r, FAQ_Be_mem D N Λ B r, rfl⟩
    have := FAQ_item_bound (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)) hV Λ hΛ z hz h hh i j
      (fun m => Pi.single m 1) (fun m => Pi.single m 1) k l _ 1 hpre1 Γ A hΓ w hG hw1
      hw3 a b (fun m => ((D : ℂ) * N)⁻¹ * FAQ_kap D N θ r m) (ν * (N : ℝ)⁻¹)
      (fun m => by
        have := FAQ_norm_coef_le D N θ hθ0 hθ1 hD hN r m
        rwa [hν])
    exact this.trans (mul_le_mul_of_nonneg_left (hcore 1 le_rfl) (by positivity))
  have hrhs : Υ / ((N : ℝ) * z.im) = (N : ℝ)⁻¹ * A := by
    rw [hAdef]
    field_simp
  rw [hrhs]
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp [Fintype.card_prod]
  have hνn : (D : ℝ) * N * (ν * (N : ℝ)⁻¹) = (N : ℝ)⁻¹ := by
    rw [hν]
    have : (D : ℝ) ≠ 0 := by positivity
    have : (N : ℝ) ≠ 0 := hN0.ne'
    field_simp
  have s4 : ‖∑ r : Idx D N, resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
      (FAQ_P4r D N θ B Λ z k l r)) (setEntry h i j w)‖ ≤
      (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r : Idx D N, ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
          (FAQ_P4r D N θ B Λ z k l r)) (setEntry h i j w)‖
        ≤ ∑ _r : Idx D N, (ν * (N : ℝ)⁻¹) * (M * Γ ^ (a + b + 1) * A) :=
          Finset.sum_le_sum fun r _ => b4 r
      _ = (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc, hνn]
  have s5 : ‖∑ r : Idx D N, resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
      (FAQ_P5r D N θ B Λ z k l r)) (setEntry h i j w)‖ ≤
      (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r : Idx D N, ‖resPolyEval (FAQ_Tit i j (if i = j then 1 / 2 else 1) a b
          (FAQ_P5r D N θ B Λ z k l r)) (setEntry h i j w)‖
        ≤ ∑ _r : Idx D N, (ν * (N : ℝ)⁻¹) * (M * Γ ^ (a + b + 1) * A) :=
          Finset.sum_le_sum fun r _ => b5 r
      _ = (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc, hνn]
  have hX0 : 0 ≤ M * Γ ^ (a + b + 1) := mul_nonneg hM0 hGm
  have hNi : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN0.le
  have h1 : ν * (M * Γ ^ (a + b + 1)) ≤ (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := by
    calc ν * (M * Γ ^ (a + b + 1)) ≤ (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1)) :=
          mul_le_mul_of_nonneg_right hνN hX0
      _ ≤ (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := by
          refine mul_le_mul_of_nonneg_left ?_ hNi
          nlinarith
  have h2 : ν * (M * Γ ^ (a + b + 1) * A) ≤ (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) :=
    mul_le_mul_of_nonneg_right hνN (mul_nonneg hX0 hA0)
  have h3 : (ν * ‖z‖) * (M * Γ ^ (a + b + 1) * A) ≤
      ((N : ℝ)⁻¹ * ‖z‖) * (M * Γ ^ (a + b + 1) * A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hνN (norm_nonneg z))
      (mul_nonneg hX0 hA0)
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl) |>.trans ?_
  have hz0 := norm_nonneg z
  have hpos : 0 ≤ (N : ℝ)⁻¹ * (M * Γ ^ (a + b + 1) * A) := mul_nonneg hNi (mul_nonneg hX0 hA0)
  nlinarith [b1, b2, b3, s4, s5, h1, h2, h3, mul_nonneg hz0 hpos]

end RBMTransitionEdge

end
