module

public import RBMTransitionEdge.Det.Shift

@[expose] public section

/-!
# The exponent rows of Lemma 5.5

Monomials in `N`, `Im m`, `η`, `‖A‖_HS` and `‖A‖`, and the row lemma: a monomial is at most
`C N^{λ} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` when its exponent is at most `λ` at three points of the
spectral window, for the exponent arithmetic in the proof of Lemma 5.5
[claim_estimate_remainder_terms] under (2.8) [eq:condA2].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A monomial `N^{a/2} (Im m)^{i/2} η^{-l/2} ‖A‖_HS^d ‖A‖^o`. -/
structure FMono where
  a : ℤ
  i : ℤ
  l : ℤ
  d : ℕ
  o : ℕ
  deriving DecidableEq, Repr, Hashable

/-- The product of two monomials. -/
def FMono.mul (p q : FMono) : FMono := ⟨p.a + q.a, p.i + q.i, p.l + q.l, p.d + q.d, p.o + q.o⟩

/-- `(Im m)^{1(r ≥ 2)} η^{1-r}`, the size (A.53) [entprodG] of an entry with `r` resolvents
(`1` for `r ≤ 1`). -/
def FMono.psi (r : ℕ) : FMono := if 2 ≤ r then ⟨0, 2, 2 * ((r : ℤ) - 1), 0, 0⟩ else ⟨0, 0, 0, 0, 0⟩

/-- `(Im m)^{1/2} η^{1/2-r}`, the Ward size of a row or a column of a word with `r ≥ 1`
resolvents (`1` for `r = 0`). -/
def FMono.omega (r : ℕ) : FMono := if 1 ≤ r then ⟨0, 1, 2 * (r : ℤ) - 1, 0, 0⟩ else ⟨0, 0, 0, 0, 0⟩

/-- The value of a monomial at `N`, the bound `M` on `Im m`, `η`, `‖A‖_HS`, `‖A‖`. -/
def FMono.evalR (m : FMono) (N : ℕ) (M η hs op : ℝ) : ℝ :=
  (N : ℝ) ^ ((m.a : ℝ) / 2) * M ^ ((m.i : ℝ) / 2) * η ^ (-(m.l : ℝ) / 2) * hs ^ m.d * op ^ m.o

/-- The exponent of `N` in `m / 𝔗`, `𝔗 = N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, at `x = (𝔯(k)/N)^{1/3}
= N^ξ`, for `Im m ≤ N^{ε/2} x`, `η⁻¹ = N^{1-ε} x`, `‖A‖_HS ≤ N^{-ε_A} x⁻¹`, `‖A‖ ≤ 1`. -/
def FMono.lamR (m : FMono) (ε εA ξ : ℝ) : ℝ :=
  m.a / 2 + m.i / 2 * (ε / 2 + ξ) + m.l / 2 * (1 - ε + ξ) + (1 - 2 * ξ) +
    (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - ξ) + m.o * min 0 (-εA - ξ)
     else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - ξ))

/-! ### The identity for `lamR` and auxiliary real-variable lemmas -/

/-- The exponent `lamR` of the row lemma as `W + V ξ + T(ξ)`, with the part `T(ξ)` coming from
`‖A‖_HS^{d-2} ‖A‖^{o}` (or `‖A‖_HS^{d} ‖A‖^{o}` taken out of `‖A‖_HS²`) in the proof of
Lemma 5.5 [claim_estimate_remainder_terms]. -/
private lemma fr_lam_eq (m : FMono) (ε εA ξ : ℝ) :
    m.lamR ε εA ξ = ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε) + 1) +
      ξ * (((m.i : ℝ) + m.l) / 2 - 2) +
      (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - ξ) + m.o * min 0 (-εA - ξ)
       else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - ξ)) := by
  unfold FMono.lamR
  ring

/-- `lamR` as a function of `ξ` with the single kink `min 0 (c - ξ)`. -/
private lemma fr_lam_g (m : FMono) (ε εA : ℝ) :
    ∃ W V B S : ℝ, ∀ ξ : ℝ, m.lamR ε εA ξ =
      W + V * ξ + B * (-εA - ξ) + S * min 0 (-εA - ξ) := by
  refine ⟨(m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε) + 1,
    ((m.i : ℝ) + m.l) / 2 - 2, if 2 ≤ m.d then (m.d : ℝ) - 2 else 0,
    if 2 ≤ m.d then (m.o : ℝ) else (m.d : ℝ) + m.o - 2, fun ξ => ?_⟩
  rw [fr_lam_eq]
  by_cases h : 2 ≤ m.d
  · simp only [h, ↓reduceIte]; ring
  · simp only [h, ↓reduceIte]; ring

/-- An affine function on an interval is at most `L` if it is at both endpoints. -/
private lemma fr_aff (u v p q L t : ℝ) (hp : p ≤ t) (hq : t ≤ q) (h1 : u + v * p ≤ L)
    (h2 : u + v * q ≤ L) : u + v * t ≤ L := by
  rcases le_total 0 v with hv | hv
  · have := mul_le_mul_of_nonneg_left hq hv
    linarith
  · have := mul_le_mul_of_nonpos_left hp hv
    linarith

/-- A function with one kink at `c` that is at most `L` at `-1/3`, `c` and `0` is at most `L`
on `[-1/3, 0]`. -/
private lemma fr_window (W V B S c L : ℝ)
    (h1 : W + V * (-(1 / 3)) + B * (c - -(1 / 3)) + S * min 0 (c - -(1 / 3)) ≤ L)
    (h2 : W + V * c + B * (c - c) + S * min 0 (c - c) ≤ L)
    (h3 : W + V * 0 + B * (c - 0) + S * min 0 (c - 0) ≤ L)
    (t : ℝ) (ht1 : -(1 / 3) ≤ t) (ht0 : t ≤ 0) :
    W + V * t + B * (c - t) + S * min 0 (c - t) ≤ L := by
  rcases le_or_gt t c with htc | htc
  · rw [min_eq_left (by linarith : (0 : ℝ) ≤ c - t)]
    rw [min_eq_left (by linarith : (0 : ℝ) ≤ c - -(1 / 3))] at h1
    rw [sub_self, min_self] at h2
    have := fr_aff (W + B * c) (V - B) (-(1 / 3)) c L t ht1 htc (by linarith) (by linarith)
    linarith
  · rw [min_eq_right (by linarith : c - t ≤ 0)]
    rw [min_eq_right (by linarith : c - 0 ≤ 0)] at h3
    rw [sub_self, min_self] at h2
    rcases le_or_gt (-(1 / 3)) c with hc | hc
    · have := fr_aff (W + (B + S) * c) (V - B - S) c 0 L t htc.le ht0 (by linarith)
        (by linarith)
      linarith
    · rw [min_eq_right (by linarith : c - -(1 / 3) ≤ 0)] at h1
      have := fr_aff (W + (B + S) * c) (V - B - S) (-(1 / 3)) 0 L t ht1 ht0 (by linarith)
        (by linarith)
      linarith

/-- `(N^s)^n = N^{s n}` for a natural exponent `n`. -/
private lemma fr_rpow_pow (N s : ℝ) (hN : 0 ≤ N) (n : ℕ) : (N ^ s) ^ n = N ^ (s * n) := by
  rw [Real.rpow_mul hN, Real.rpow_natCast]

/-- `‖X‖ ≤ ‖X‖_HS`. -/
private lemma fr_op_le_hs {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    opNorm X ≤ hsNorm X := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ι → ℂ, v = WithLp.toLp 2 x := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp]
  have hsq : ‖(WithLp.toLp 2 (X *ᵥ x) : EuclideanSpace ℂ ι)‖ ^ 2 ≤
      (hsNorm X * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hsNorm,
      Real.sq_sqrt (by positivity), Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : ‖(X *ᵥ x) p‖ ≤ ∑ q, ‖X p q‖ * ‖x q‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖X p q‖) (fun q => ‖x q‖)
    calc ‖(X *ᵥ x) p‖ ^ 2 ≤ (Real.sqrt (∑ q, ‖X p q‖ ^ 2) * Real.sqrt (∑ q, ‖x q‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = (∑ q, ‖X p q‖ ^ 2) * ∑ q, ‖x q‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    two_ne_zero).1 hsq

/-- `‖A‖_HS^d ‖A‖^o ≤ N^{T} ‖A‖_HS²` when `d + o ≥ 2`, `‖A‖ ≤ 1`, `‖A‖ ≤ ‖A‖_HS ≤ N^t`. -/
private lemma fr_hsop (N hs op t : ℝ) (d o : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d + o)
    (hs0 : 0 ≤ hs) (op0 : 0 ≤ op) (hop1 : op ≤ 1) (hophs : op ≤ hs) (hhs : hs ≤ N ^ t) :
    hs ^ d * op ^ o ≤ N ^ (if 2 ≤ d then ((d : ℝ) - 2) * t + o * min 0 t
        else ((d : ℝ) + o - 2) * min 0 t) * hs ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hopN : op ≤ N ^ (min 0 t) := by
    rcases le_total 0 t with h | h
    · rw [min_eq_left h, Real.rpow_zero]; exact hop1
    · rw [min_eq_right h]; exact hophs.trans hhs
  by_cases hd2 : 2 ≤ d
  · simp only [hd2, ↓reduceIte]
    have e1 : hs ^ (d - 2) ≤ (N ^ t) ^ (d - 2) := pow_le_pow_left₀ hs0 hhs _
    have e2 : op ^ o ≤ (N ^ min 0 t) ^ o := pow_le_pow_left₀ op0 hopN _
    rw [fr_rpow_pow _ _ hN0.le] at e1 e2
    have hd' : hs ^ d = hs ^ (d - 2) * hs ^ 2 := by
      rw [← pow_add]; congr 1; omega
    calc hs ^ d * op ^ o = (hs ^ (d - 2) * op ^ o) * hs ^ 2 := by rw [hd']; ring
      _ ≤ (N ^ (t * ((d - 2 : ℕ) : ℝ)) * N ^ (min 0 t * (o : ℝ))) * hs ^ 2 := by gcongr
      _ = _ := by
          rw [← Real.rpow_add hN0]
          congr 2
          push_cast [Nat.cast_sub hd2]
          ring
  · simp only [hd2, ↓reduceIte]
    have e1 : op ^ (2 - d) ≤ hs ^ (2 - d) := pow_le_pow_left₀ op0 hophs _
    have e2 : op ^ (d + o - 2) ≤ (N ^ min 0 t) ^ (d + o - 2) := pow_le_pow_left₀ op0 hopN _
    rw [fr_rpow_pow _ _ hN0.le] at e2
    have h2 : hs ^ d * hs ^ (2 - d) = hs ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have ho : op ^ o = op ^ (2 - d) * op ^ (d + o - 2) := by
      rw [← pow_add]; congr 1; omega
    have hq : min 0 t * ((d + o - 2 : ℕ) : ℝ) = ((d : ℝ) + o - 2) * min 0 t := by
      push_cast [Nat.cast_sub hd]
      ring
    calc hs ^ d * op ^ o = hs ^ d * (op ^ (2 - d) * op ^ (d + o - 2)) := by rw [ho]
      _ ≤ hs ^ d * (hs ^ (2 - d) * N ^ (min 0 t * ((d + o - 2 : ℕ) : ℝ))) := by gcongr
      _ = N ^ (((d : ℝ) + o - 2) * min 0 t) * hs ^ 2 := by
          rw [hq, ← h2]; ring

/-- The value of a monomial at `M = N^{ε/2} x`, `η = N^{-(1-ε)} x⁻¹`. -/
private lemma fr_eval (m : FMono) (N : ℕ) (ε x hs op : ℝ) (hN : 0 < (N : ℝ)) (hx : 0 < x) :
    m.evalR N ((N : ℝ) ^ (ε / 2) * x) ((N : ℝ) ^ (-(1 - ε)) * x⁻¹) hs op =
      (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
        x ^ (((m.i : ℝ) + m.l) / 2) * hs ^ m.d * op ^ m.o := by
  unfold FMono.evalR
  rw [Real.mul_rpow (by positivity) hx.le, Real.mul_rpow (by positivity) (by positivity),
    Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le]
  have e1 : (-(1 - ε)) * (-(m.l : ℝ) / 2) = (m.l : ℝ) / 2 * (1 - ε) := by ring
  have e2 : (-(-(m.l : ℝ) / 2)) = (m.l : ℝ) / 2 := by ring
  have e3 : ε / 2 * ((m.i : ℝ) / 2) = (m.i : ℝ) / 2 * (ε / 2) := by ring
  have e4 : ((m.i : ℝ) + m.l) / 2 = (m.i : ℝ) / 2 + (m.l : ℝ) / 2 := by ring
  rw [e1, e2, e3, e4, Real.rpow_add hx, Real.rpow_add hN, Real.rpow_add hN]
  ring

/-- The row lemma for the exponents of Lemma 5.5 [claim_estimate_remainder_terms]: a monomial
with `Im m` to a nonnegative power and total degree at least `2` in `‖A‖` is at most
`C N^{λ} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` if its exponent is at most `λ` at the edge `x = N^{-1/3}`,
at `x = N^{-ε_A}` and in the bulk `x = 1`, from the bound on `Im m`, `η = etaK`, (2.8)
[eq:condA2] and `‖A‖ ≤ 1`. -/
theorem fmono_row (D : ℕ) (hD : 2 ≤ D) (εA ε : ℝ) (hεA : 0 < εA) (hε : 0 < ε)
    (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (m : FMono) (hi : 0 ≤ m.i) (hd : 2 ≤ m.d + m.o)
    (lam0 : ℝ) (h1 : m.lamR ε εA (-(1 / 3)) ≤ lam0) (h2 : m.lamR ε εA (-εA) ≤ lam0)
    (h3 : m.lamR ε εA 0 ≤ lam0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ 1 →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        m.evalR N ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A) ≤
          C * (N : ℝ) ^ lam0 * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  have _hεA := hεA
  have _hi := hi
  have _hε := hε
  have _hε' := hε'
  have _hε'' := hε''
  obtain ⟨W, V, B, S, hg⟩ := fr_lam_g m ε εA
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  refine ⟨(D : ℝ) ^ (|((m.i : ℝ) + m.l) / 2 - 2| / 3), Real.rpow_pos_of_pos hDpos _, ?_⟩
  intro N hN A hop k hk hk2 hhs
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < k := by linarith
  have hDN : 1 ≤ D * N := Nat.mul_pos (by omega) hN
  have hrk : rk D N k = (k : ℝ) := by
    have : min k (D * N + 1 - k) = k := min_eq_left (by omega)
    simp [rk, this]
  have hη' : etaK D N k ε = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [etaK, hrk]
  have hKle : (k : ℝ) ≤ D * N := by exact_mod_cast (by omega : k ≤ D * N)
  rw [hrk] at hhs ⊢
  rw [hη']
  -- the spectral parameter `x = (k / N)^{1/3}`
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxinv : x⁻¹ = (k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have e1 : ((k : ℝ) ^ (1 / 3 : ℝ))⁻¹ = (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
      (Real.rpow_neg hK0.le _).symm
    have e2 : ((N : ℝ) ^ (-(1 / 3 : ℝ)))⁻¹ = (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_neg hN0.le]; norm_num
    rw [hxdef, mul_inv, e1, e2]
  have hM : (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * (k : ℝ) ^ (1 / 3 : ℝ) = (N : ℝ) ^ (ε / 2) * x := by
    rw [hxdef, Real.rpow_add hN0]; ring
  have hη : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (k : ℝ) ^ (-(1 / 3 : ℝ)) =
      (N : ℝ) ^ (-(1 - ε)) * x⁻¹ := by
    rw [hxinv, show -(2 / 3 : ℝ) + ε = -(1 - ε) + 1 / 3 by ring, Real.rpow_add hN0]; ring
  have hhs' : hsNorm A ≤ (N : ℝ) ^ (-εA) * x⁻¹ := by
    have : (N : ℝ) ^ (-εA) * x⁻¹ = (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [hxinv, show (1 / 3 : ℝ) - εA = -εA + 1 / 3 by ring, Real.rpow_add hN0]; ring
    linarith
  have hT : (N : ℝ) ^ (-(5 / 3 : ℝ)) * (k : ℝ) ^ (2 / 3 : ℝ) * hsNorm A ^ 2 =
      (N : ℝ) ^ (-1 : ℝ) * x ^ 2 * hsNorm A ^ 2 := by
    have e1 : (N : ℝ) ^ (-(5 / 3 : ℝ)) =
        (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ) * ((2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hN0]; congr 1; push_cast; ring
    have e2 : (k : ℝ) ^ (2 / 3 : ℝ) = (k : ℝ) ^ ((1 / 3 : ℝ) * ((2 : ℕ) : ℝ)) := by
      congr 1; push_cast; ring
    rw [hxdef, mul_pow, fr_rpow_pow _ _ hK0.le, fr_rpow_pow _ _ hN0.le, e1, e2]
    ring
  rw [hM, hη, fr_eval m N ε x _ _ hN0 hx0, hT]
  have hs0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  have hop0 : 0 ≤ opNorm A := norm_nonneg _
  have hophs : opNorm A ≤ hsNorm A := fr_op_le_hs A
  have hd : 2 ≤ m.d + m.o := hd
  -- the exponent identity
  have hlam : ∀ ξ : ℝ, m.lamR ε εA ξ =
      ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) + 1 +
        ξ * (((m.i : ℝ) + m.l) / 2 - 2) +
        (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - ξ) + m.o * min 0 (-εA - ξ)
         else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - ξ)) := fun ξ => fr_lam_eq m ε εA ξ
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = ((m.i : ℝ) + m.l) / 2 - 2 := ⟨_, rfl⟩
  rw [← hγ]
  have hC1 : (1 : ℝ) ≤ (D : ℝ) ^ (|γ| / 3) := Real.one_le_rpow hD1 (by positivity)
  by_cases hx1 : 1 ≤ x
  · -- the region `x ≥ 1`
    have hxD : x ≤ (D : ℝ) ^ (1 / 3 : ℝ) := by
      have hk3 : (k : ℝ) ^ (1 / 3 : ℝ) ≤ ((D : ℝ) * N) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hK0.le hKle (by norm_num)
      rw [Real.mul_rpow hDpos.le hN0.le] at hk3
      calc x = (k : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := hxdef
        _ ≤ ((D : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
          gcongr
        _ = (D : ℝ) ^ (1 / 3 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hN0]; simp
    have hxγ : x ^ γ ≤ (D : ℝ) ^ (|γ| / 3) := by
      calc x ^ γ ≤ x ^ |γ| := Real.rpow_le_rpow_of_exponent_le hx1 (le_abs_self γ)
        _ ≤ ((D : ℝ) ^ (1 / 3 : ℝ)) ^ |γ| := Real.rpow_le_rpow hx0.le hxD (abs_nonneg _)
        _ = (D : ℝ) ^ (|γ| / 3) := by
          rw [← Real.rpow_mul hDpos.le]; congr 1; ring
    have hhs0 : hsNorm A ≤ (N : ℝ) ^ (-εA - 0) := by
      rw [sub_zero]
      calc hsNorm A ≤ (N : ℝ) ^ (-εA) * x⁻¹ := hhs'
        _ ≤ (N : ℝ) ^ (-εA) * 1 := by
          exact mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hx1) (by positivity)
        _ = _ := mul_one _
    have hB := fr_hsop (N : ℝ) (hsNorm A) (opNorm A) (-εA - 0) m.d m.o hN1 hd hs0 hop0 hop hophs
      hhs0
    have h3' := hlam 0
    have hexp : ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) +
        (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - 0) + m.o * min 0 (-εA - 0)
         else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - 0)) ≤ lam0 + -1 := by linarith
    have e1 : (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
        (N : ℝ) ^ (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - 0) + m.o * min 0 (-εA - 0)
         else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - 0)) ≤ (N : ℝ) ^ lam0 * (N : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
    have e2 : x ^ (((m.i : ℝ) + m.l) / 2) = x ^ γ * x ^ 2 := by
      rw [hγ, ← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; push_cast; ring
    calc _ = (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
          x ^ (((m.i : ℝ) + m.l) / 2) * (hsNorm A ^ m.d * opNorm A ^ m.o) := by ring
      _ ≤ (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
          x ^ (((m.i : ℝ) + m.l) / 2) * ((N : ℝ) ^ (if 2 ≤ m.d then ((m.d : ℝ) - 2) *
            (-εA - 0) + m.o * min 0 (-εA - 0)
            else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - 0)) * hsNorm A ^ 2) := by
          gcongr
      _ = ((N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
            (N : ℝ) ^ (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - 0) + m.o * min 0 (-εA - 0)
             else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - 0))) * x ^ γ * x ^ 2 * hsNorm A ^ 2 := by
          rw [e2]; ring
      _ ≤ ((N : ℝ) ^ lam0 * (N : ℝ) ^ (-1 : ℝ)) * (D : ℝ) ^ (|γ| / 3) * x ^ 2 *
            hsNorm A ^ 2 := by gcongr
      _ = _ := by ring
  · -- the region `x < 1`
    rw [not_le] at hx1
    have hNgt : (1 : ℝ) < N := by
      by_contra hcon
      have hN1' : (N : ℝ) = 1 := le_antisymm (not_lt.1 hcon) hN1
      have : 1 ≤ x := by
        rw [hxdef, hN1', Real.one_rpow, mul_one]
        exact Real.one_le_rpow hK1 (by norm_num)
      linarith
    have hxlow : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ x := by
      rw [hxdef]
      calc (N : ℝ) ^ (-(1 / 3 : ℝ)) = 1 * (N : ℝ) ^ (-(1 / 3 : ℝ)) := (one_mul _).symm
        _ ≤ _ := by
          gcongr; exact Real.one_le_rpow hK1 (by norm_num)
    obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℝ, ξ = Real.logb N x := ⟨_, rfl⟩
    have hξ : (N : ℝ) ^ ξ = x := by
      rw [hξdef]; exact Real.rpow_logb hN0 hNgt.ne' hx0
    have hξ0 : ξ ≤ 0 := by rw [hξdef]; exact Real.logb_nonpos hNgt hx0.le hx1.le
    have hξ1 : -(1 / 3 : ℝ) ≤ ξ := by
      rw [hξdef]; exact (Real.le_logb_iff_rpow_le hNgt hx0).2 hxlow
    have hlamξ : m.lamR ε εA ξ ≤ lam0 := by
      rw [hg] at h1 h2 h3 ⊢
      exact fr_window W V B S (-εA) lam0 h1 h2 h3 ξ hξ1 hξ0
    have hhsξ : hsNorm A ≤ (N : ℝ) ^ (-εA - ξ) := by
      have : (N : ℝ) ^ (-εA) * x⁻¹ = (N : ℝ) ^ (-εA - ξ) := by
        rw [← hξ, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1
      linarith
    have hB := fr_hsop (N : ℝ) (hsNorm A) (opNorm A) (-εA - ξ) m.d m.o hN1 hd hs0 hop0 hop hophs
      hhsξ
    have hl := hlam ξ
    have hexp : ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) +
        ξ * (((m.i : ℝ) + m.l) / 2) +
        (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - ξ) + m.o * min 0 (-εA - ξ)
         else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - ξ)) ≤ lam0 + -1 + ξ * 2 := by linarith
    have e1 : (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
        (N : ℝ) ^ (ξ * (((m.i : ℝ) + m.l) / 2)) *
        (N : ℝ) ^ (if 2 ≤ m.d then ((m.d : ℝ) - 2) * (-εA - ξ) + m.o * min 0 (-εA - ξ)
         else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - ξ)) ≤
          (N : ℝ) ^ lam0 * (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (ξ * ((2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      push_cast
      linarith
    have e2 : x ^ (((m.i : ℝ) + m.l) / 2) = (N : ℝ) ^ (ξ * (((m.i : ℝ) + m.l) / 2)) := by
      rw [← hξ, ← Real.rpow_mul hN0.le]
    have e3 : x ^ 2 = (N : ℝ) ^ (ξ * ((2 : ℕ) : ℝ)) := by
      rw [← hξ, fr_rpow_pow _ _ hN0.le]
    rw [e2]
    calc _ = (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
          (N : ℝ) ^ (ξ * (((m.i : ℝ) + m.l) / 2)) * (hsNorm A ^ m.d * opNorm A ^ m.o) := by ring
      _ ≤ (N : ℝ) ^ ((m.a : ℝ) / 2 + (m.i : ℝ) / 2 * (ε / 2) + (m.l : ℝ) / 2 * (1 - ε)) *
          (N : ℝ) ^ (ξ * (((m.i : ℝ) + m.l) / 2)) * ((N : ℝ) ^ (if 2 ≤ m.d then
            ((m.d : ℝ) - 2) * (-εA - ξ) + m.o * min 0 (-εA - ξ)
            else ((m.d : ℝ) + m.o - 2) * min 0 (-εA - ξ)) * hsNorm A ^ 2) := by
          gcongr
      _ ≤ ((N : ℝ) ^ lam0 * (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (ξ * ((2 : ℕ) : ℝ))) *
            hsNorm A ^ 2 := by
          rw [← mul_assoc]; gcongr
      _ = (N : ℝ) ^ lam0 * ((N : ℝ) ^ (-1 : ℝ) * x ^ 2 * hsNorm A ^ 2) := by rw [e3]; ring
      _ = 1 * ((N : ℝ) ^ lam0 * ((N : ℝ) ^ (-1 : ℝ) * x ^ 2 * hsNorm A ^ 2)) := (one_mul _).symm
      _ ≤ (D : ℝ) ^ (|γ| / 3) * ((N : ℝ) ^ lam0 * ((N : ℝ) ^ (-1 : ℝ) * x ^ 2 * hsNorm A ^ 2)) :=
          mul_le_mul_of_nonneg_right hC1 (by positivity)
      _ = _ := by ring

end RBMTransitionEdge

end
