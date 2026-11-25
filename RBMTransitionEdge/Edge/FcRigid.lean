module

public import RBMTransitionEdge.Edge.Defs
public import RBMTransitionEdge.LocalLaw.FarDet

@[expose] public section

/-!
# The free-convolution root and rigidity at real points in Lemma 4.1

The root `ξ_fc` of `t⟨(ξ − X)^{-2}⟩ = 1`, the scaling of the moments `⟨(ξ − X)^{-j}⟩`, and their
comparison with the moments of `ρ_N` for a rigid spectrum at real points outside the spectrum
(proof of Lemma 4.1 [CVtG]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- sum-integral comparison for `k^(-s)`. -/
private lemma FcRigid_sum_rpow_le (s : ℝ) (hs0 : 0 < s) (hs1 : s ≠ 1) (a m : ℕ) (ha : 1 ≤ a)
    (hm : a ≤ m) :
    ∑ k ∈ Finset.Ioc a m, (k : ℝ) ^ (-s) ≤ ((m : ℝ) ^ (1 - s) - (a : ℝ) ^ (1 - s)) / (1 - s) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s))
      (Set.Icc (a : ℝ) ((a : ℝ) + ((m - a : ℕ) : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  have e1 : (a : ℝ) + ((m - a : ℕ) : ℝ) = m := by
    rw [Nat.cast_sub hm]; ring
  rw [e1] at h1
  have e2 : ∑ k ∈ Finset.Ioc a m, (k : ℝ) ^ (-s) =
      ∑ i ∈ Finset.range (m - a), ((a : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    have hI : Finset.Ioc a m = Finset.Ico (a + 1) (m + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun i _ => ?_
    push_cast
    ring_nf
  rw [e2]
  refine h1.trans (le_of_eq ?_)
  rw [integral_rpow]
  · ring_nf
  · right
    refine ⟨by intro h; apply hs1; linarith, ?_⟩
    rw [Set.uIcc_of_le (by exact_mod_cast hm)]
    intro h
    linarith [h.1]

/-- `∑_{k ≤ m} k^{-1/3} ≤ (3/2) m^{2/3}`. -/
private lemma FcRigid_sum_third (m : ℕ) :
    ∑ k ∈ Finset.Ioc (0 : ℕ) m, (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (3 / 2) * (m : ℝ) ^ (2 / 3 : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := FcRigid_sum_rpow_le (1 / 3) (by norm_num) (by norm_num) 1 m le_rfl hm
  have e := Finset.sum_Ioc_consecutive (fun k : ℕ => (k : ℝ) ^ (-(1 / 3 : ℝ))) (Nat.zero_le 1) hm
  have h1 : ∑ k ∈ Finset.Ioc (0 : ℕ) 1, (k : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
    have : Finset.Ioc (0 : ℕ) 1 = {1} := by decide
    rw [this]; simp
  have e2 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  rw [e2] at h
  rw [← e, h1]
  have h3 : ((m : ℝ) ^ (2 / 3 : ℝ) - ((1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) / (2 / 3) =
      (3 / 2) * (m : ℝ) ^ (2 / 3 : ℝ) - 3 / 2 := by
    simp; ring
  rw [h3] at h
  linarith

/-- `∑_{a < k ≤ m} k^{-s} ≤ a^{1-s}/(s-1)` for `s > 1`, `a ≥ 1`. -/
private lemma FcRigid_sum_tail (s : ℝ) (hs : 1 < s) (a m : ℕ) (ha : 1 ≤ a) :
    ∑ k ∈ Finset.Ioc a m, (k : ℝ) ^ (-s) ≤ (a : ℝ) ^ (1 - s) / (s - 1) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hpos : 0 < (a : ℝ) ^ (1 - s) / (s - 1) := div_pos (Real.rpow_pos_of_pos ha' _) (by linarith)
  rcases le_or_gt a m with hm | hm
  · have h := FcRigid_sum_rpow_le s (by linarith) (by linarith) a m ha hm
    refine h.trans ?_
    have : (m : ℝ) ^ (1 - s) ≥ 0 := Real.rpow_nonneg (by positivity) _
    rw [show (a : ℝ) ^ (1 - s) / (s - 1) = (0 - (a : ℝ) ^ (1 - s)) / (1 - s) by
      rw [← neg_sub 1 s, div_neg, zero_sub, neg_div]]
    exact div_le_div_of_nonpos_of_le (by linarith) (by linarith)
  · rw [Finset.Ioc_eq_empty (by omega)]
    simpa using hpos.le
/-- `|x^{m+1} - y^{m+1}| ≤ (m+1) B^m |x - y|` for `0 ≤ x, y ≤ B`. -/
private lemma FcRigid_pow_sub (x y B : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxB : x ≤ B) (hyB : y ≤ B)
    (m : ℕ) : |x ^ (m + 1) - y ^ (m + 1)| ≤ (m + 1) * B ^ m * |x - y| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hB : 0 ≤ B := hx.trans hxB
    have e : x ^ (m + 1 + 1) - y ^ (m + 1 + 1) =
        x * (x ^ (m + 1) - y ^ (m + 1)) + y ^ (m + 1) * (x - y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg (pow_nonneg hy _)]
    have h1 : x * |x ^ (m + 1) - y ^ (m + 1)| ≤ B * ((m + 1) * B ^ m * |x - y|) :=
      mul_le_mul hxB ih (abs_nonneg _) hB
    have h2 : y ^ (m + 1) * |x - y| ≤ B ^ (m + 1) * |x - y| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy hyB _) (abs_nonneg _)
    push_cast
    calc _ ≤ B * ((m + 1) * B ^ m * |x - y|) + B ^ (m + 1) * |x - y| := add_le_add h1 h2
      _ = ((m : ℝ) + 1 + 1) * B ^ (m + 1) * |x - y| := by ring

/-- The mean-value bound for `1/a^{m+1}` against `1/b^{m+1}`, `|a - b| ≤ b/2`. -/
private lemma FcRigid_pw (m : ℕ) {a b : ℝ} (hb : 0 < b) (h : |a - b| ≤ b / 2) :
    |1 / a ^ (m + 1) - 1 / b ^ (m + 1)| ≤ (m + 1) * 3 ^ (m + 1) * (|a - b| / b ^ (m + 2)) := by
  have h1 := abs_le.mp h
  have ha : b / 2 ≤ a := by linarith
  have ha2 : a ≤ 3 * b / 2 := by linarith
  have hapos : 0 < a := by linarith
  have hnum := FcRigid_pow_sub a b (3 * b / 2) hapos.le hb.le ha2 (by linarith) m
  have e : 1 / a ^ (m + 1) - 1 / b ^ (m + 1) =
      (b ^ (m + 1) - a ^ (m + 1)) / (a ^ (m + 1) * b ^ (m + 1)) := by
    field_simp
  rw [e, abs_div, abs_mul, abs_of_pos (pow_pos hapos _), abs_of_pos (pow_pos hb _), abs_sub_comm]
  have hden : (b / 2) ^ (m + 1) * b ^ (m + 1) ≤ a ^ (m + 1) * b ^ (m + 1) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ha _) (by positivity)
  have hdpos : 0 < (b / 2) ^ (m + 1) * b ^ (m + 1) := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc |a ^ (m + 1) - b ^ (m + 1)| ≤ (m + 1) * (3 * b / 2) ^ m * |a - b| := hnum
    _ = ((m + 1) * 3 ^ m * 2 * (|a - b| / b ^ (m + 2))) * ((b / 2) ^ (m + 1) * b ^ (m + 1)) := by
      rw [div_pow, mul_pow, div_pow]
      field_simp
      ring
    _ ≤ ((m + 1) * 3 ^ (m + 1) * (|a - b| / b ^ (m + 2))) * (a ^ (m + 1) * b ^ (m + 1)) := by
      have hq : 0 ≤ |a - b| / b ^ (m + 2) := by positivity
      have h3 : (3 : ℝ) ^ m * 2 ≤ 3 ^ (m + 1) := by
        rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < 3 by norm_num) m]
      have h4 : ((m : ℝ) + 1) * 3 ^ m * 2 * (|a - b| / b ^ (m + 2)) ≤
          ((m : ℝ) + 1) * 3 ^ (m + 1) * (|a - b| / b ^ (m + 2)) := by
        have : ((m : ℝ) + 1) * (3 ^ m * 2) ≤ ((m : ℝ) + 1) * 3 ^ (m + 1) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        nlinarith
      exact mul_le_mul h4 hden hdpos.le (by positivity)

/-- `𝔯(k) = k` of (1.4) [eq:rk] for the left half `2k ≤ DN + 1`. -/
private lemma FcRigid_rk_left (D N k : ℕ) (h : 2 * k ≤ D * N + 1) : rk D N k = (k : ℝ) := by
  unfold rk
  rw [Nat.min_eq_left (by omega)]

/-- `𝔯(k) = DN + 1 - k` of (1.4) [eq:rk] for the right half `DN + 1 ≤ 2k`. -/
private lemma FcRigid_rk_right (D N k : ℕ) (hk : k ≤ D * N) (h : D * N + 1 ≤ 2 * k) :
    rk D N k = ((D * N + 1 - k : ℕ) : ℝ) := by
  unfold rk
  rw [Nat.min_eq_right (by omega)]


/-- The exponent bookkeeping `N^{-2/3} k^{-1/3} / (k^{2/3} N^{-2/3})^{j+1} =
N^{2j/3} k^{-(2j+3)/3}` of the part `i₀ < k` of the rigidity sum. -/
private lemma FcRigid_alg (k N : ℝ) (hk : 0 < k) (hN : 0 < N) (j : ℕ) :
    N ^ (-(2 / 3 : ℝ)) * k ^ (-(1 / 3 : ℝ)) / (k ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ))) ^ (j + 1) =
      N ^ (2 * (j : ℝ) / 3) * k ^ (-((2 * (j : ℝ) + 3) / 3)) := by
  have e1 : (k ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ))) ^ (j + 1) =
      k ^ (2 / 3 * ((j : ℝ) + 1)) * N ^ (-(2 / 3) * ((j : ℝ) + 1)) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (N ^ _), ← Real.rpow_mul hk.le,
      ← Real.rpow_mul hN.le]
    push_cast
    ring_nf
  rw [e1, div_eq_iff (by positivity)]
  have e2 : N ^ (2 * (j : ℝ) / 3) * k ^ (-((2 * (j : ℝ) + 3) / 3)) *
      (k ^ (2 / 3 * ((j : ℝ) + 1)) * N ^ (-(2 / 3) * ((j : ℝ) + 1))) =
      (N ^ (2 * (j : ℝ) / 3) * N ^ (-(2 / 3) * ((j : ℝ) + 1))) *
        (k ^ (-((2 * (j : ℝ) + 3) / 3)) * k ^ (2 / 3 * ((j : ℝ) + 1))) := by ring
  rw [e2, ← Real.rpow_add hN, ← Real.rpow_add hk]
  congr 2 <;> ring

/-- The part `k ≤ i₀` of the rigidity sum (proof of Lemma 4.1 [CVtG]): there `b_k ≥ κ` and
`𝔯(k) = k`, and `∑_{k ≤ i₀} k^{-1/3} ≤ (3/2) i₀^{2/3}`. -/
private lemma FcRigid_regI (D N : ℕ) (τ' κ T : ℝ) (j : ℕ) (hN : 1 ≤ N) (hκ : 0 < κ)
    (b : ℕ → ℝ) (i₀ : ℕ) (hi₀ : 2 * i₀ ≤ D * N) (hT : (i₀ : ℝ) ≤ T)
    (hb : ∀ k ∈ Finset.Ioc 0 i₀, κ ≤ b k) :
    ∑ k ∈ Finset.Ioc 0 i₀, (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) /
        b k ^ (j + 1) ≤
      (3 / 2) * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * T ^ (2 / 3 : ℝ))) / κ ^ (j + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ k ∈ Finset.Ioc 0 i₀, (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
      rk D N k ^ (-(1 / 3 : ℝ))) / b k ^ (j + 1) ≤
      ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) / κ ^ (j + 1)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [FcRigid_rk_left D N k (by omega)]
    have hbk : κ ^ (j + 1) ≤ b k ^ (j + 1) := pow_le_pow_left₀ hκ.le (hb k (Finset.mem_Ioc.2 hk)) _
    have hA : 0 ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by
      positivity
    calc _ ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ))) / κ ^ (j + 1) :=
          div_le_div_of_nonneg_left hA (by positivity) hbk
      _ = _ := by ring
  refine (Finset.sum_le_sum key).trans ?_
  rw [← Finset.mul_sum]
  have h1 := FcRigid_sum_third i₀
  have h2 : (i₀ : ℝ) ^ (2 / 3 : ℝ) ≤ T ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hT (by norm_num)
  have hC : 0 ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) / κ ^ (j + 1) := by positivity
  calc _ ≤ ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) / κ ^ (j + 1)) * ((3 / 2) * T ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hC
    _ = _ := by ring

/-- The part `i₀ < k ≤ M` of the rigidity sum (proof of Lemma 4.1 [CVtG]), with the lower bound
`b_k ≥ c k^{2/3} N^{-2/3}` of (2.21) [eq:kappa_gamma_k], `𝔯(k) = k`, and the tail of
`∑ k^{-(2j+3)/3}` from `i₀ ≥ T/2`, `T = N κ^{3/2}`. -/
private lemma FcRigid_regII (D N : ℕ) (τ' κ T c : ℝ) (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3)
    (hN : 1 ≤ N) (hκ : 0 < κ) (hc : 0 < c) (hTdef : T = (N : ℝ) * κ ^ (3 / 2 : ℝ))
    (b : ℕ → ℝ) (i₀ M : ℕ) (hi₀ : 1 ≤ i₀) (hT2 : T / 2 ≤ (i₀ : ℝ)) (hM : 2 * M ≤ D * N)
    (hb : ∀ k ∈ Finset.Ioc i₀ M, c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ b k) :
    ∑ k ∈ Finset.Ioc i₀ M, (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) /
        b k ^ (j + 1) ≤
      6 * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * (κ ^ j)⁻¹) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hi0 : (0 : ℝ) < i₀ := by exact_mod_cast hi₀
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjr3 : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
  set q : ℝ := 2 * (j : ℝ) / 3 with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have key : ∀ k ∈ Finset.Ioc i₀ M, (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
      rk D N k ^ (-(1 / 3 : ℝ))) / b k ^ (j + 1) ≤
      ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * (N : ℝ) ^ q) * (k : ℝ) ^ (-(q + 1)) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    rw [FcRigid_rk_left D N k (by omega)]
    have hβ : 0 < (k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    have hbk : (c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)))) ^ (j + 1) ≤
        b k ^ (j + 1) := pow_le_pow_left₀ (by positivity) (hb k (Finset.mem_Ioc.2 hk)) _
    have hA : 0 ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by
      positivity
    have hal := FcRigid_alg (k : ℝ) (N : ℝ) hk0 hN0 j
    have e : -(q + 1) = -((2 * (j : ℝ) + 3) / 3) := by rw [hq]; ring
    calc _ ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ))) /
          (c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)))) ^ (j + 1) :=
          div_le_div_of_nonneg_left hA (by positivity) hbk
      _ = (N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) /
          ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ^ (j + 1)) := by
        rw [mul_pow]; field_simp
      _ = _ := by rw [hal, e]; ring
  refine (Finset.sum_le_sum key).trans ?_
  rw [← Finset.mul_sum]
  have hs : (1 : ℝ) < q + 1 := by linarith
  have h1 := FcRigid_sum_tail (q + 1) hs i₀ M hi₀
  have e1 : (1 : ℝ) - (q + 1) = -q := by ring
  have e2 : q + 1 - 1 = q := by ring
  rw [e1, e2] at h1
  -- `i₀^{-q} ≤ (T/2)^{-q} = 2^q N^{-q} κ^{-j}`
  have hT0 : 0 < T := by rw [hTdef]; positivity
  have h2 : (i₀ : ℝ) ^ (-q) ≤ (T / 2) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hT2 (by linarith)
  have h3 : (T / 2) ^ (-q) = 2 ^ q * ((N : ℝ) ^ (-q) * κ ^ (-(j : ℝ))) := by
    rw [Real.div_rpow hT0.le (by norm_num), hTdef, Real.mul_rpow hN0.le (by positivity),
      ← Real.rpow_mul hκ.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have : 3 / 2 * -q = -(j : ℝ) := by rw [hq]; ring
    rw [this]
    field_simp
  have h4 : (2 : ℝ) ^ q ≤ 4 := by
    have : (2 : ℝ) ^ q ≤ 2 ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hq]; linarith)
    simpa using this.trans_eq (by norm_num)
  have hq1 : 1 / q ≤ 3 / 2 := by
    rw [div_le_iff₀ hq0, hq]; linarith
  have h5 : ((N : ℝ) ^ q) * ((i₀ : ℝ) ^ (-q) / q) ≤ 6 * (κ ^ (-(j : ℝ))) := by
    have hNN : (N : ℝ) ^ q * (N : ℝ) ^ (-q) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have hκj : 0 ≤ κ ^ (-(j : ℝ)) := by positivity
    calc (N : ℝ) ^ q * ((i₀ : ℝ) ^ (-q) / q) ≤ (N : ℝ) ^ q * ((2 ^ q * ((N : ℝ) ^ (-q) *
          κ ^ (-(j : ℝ)))) / q) := by
          gcongr
          exact h2.trans h3.le
      _ = ((2 ^ q * (1 / q)) * κ ^ (-(j : ℝ))) * ((N : ℝ) ^ q * (N : ℝ) ^ (-q)) := by ring
      _ ≤ ((4 * (3 / 2)) * κ ^ (-(j : ℝ))) * 1 := by
          rw [hNN, mul_one, mul_one]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul h4 hq1 (by positivity) (by norm_num)) hκj
      _ = 6 * κ ^ (-(j : ℝ)) := by ring
  have hA0 : 0 ≤ (N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ := by positivity
  have hkj : κ ^ (-(j : ℝ)) = (κ ^ j)⁻¹ := by
    rw [Real.rpow_neg hκ.le, Real.rpow_natCast]
  calc _ ≤ ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * (N : ℝ) ^ q) * ((i₀ : ℝ) ^ (-q) / q) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹) * ((N : ℝ) ^ q * ((i₀ : ℝ) ^ (-q) / q)) := by ring
    _ ≤ ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹) * (6 * κ ^ (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_left h5 hA0
    _ = _ := by rw [hkj]; ring

/-- The part `M < k ≤ DN` of the rigidity sum (proof of Lemma 4.1 [CVtG]), `M = ⌊DN/2⌋ ≥ N`:
there `b_k ≥ c k^{2/3} N^{-2/3} ≥ c` and `𝔯(k) = DN + 1 - k`, and
`∑_{r ≤ m} r^{-1/3} ≤ (3/2) m^{2/3}`. -/
private lemma FcRigid_regIII (D N : ℕ) (hD : 2 ≤ D) (τ' c : ℝ) (j : ℕ) (hN : 1 ≤ N)
    (hc : 0 < c) (b : ℕ → ℝ) (M : ℕ) (hM : D * N < 2 * M + 2) (hMn : M ≤ D * N)
    (hNM : N ≤ M)
    (hb : ∀ k ∈ Finset.Ioc M (D * N),
      c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ b k) :
    ∑ k ∈ Finset.Ioc M (D * N), (N : ℝ) ^ τ' *
        ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) / b k ^ (j + 1) ≤
      (3 / 2) * (D : ℝ) * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have key : ∀ k ∈ Finset.Ioc M (D * N), (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
      rk D N k ^ (-(1 / 3 : ℝ))) / b k ^ (j + 1) ≤
      ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) * (c ^ (j + 1))⁻¹) *
        (((D * N + 1 - k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [FcRigid_rk_right D N k hk.2 (by omega)]
    have hkN : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
    have hcb : c ≤ b k := by
      refine le_trans ?_ (hb k (Finset.mem_Ioc.2 hk))
      have h1 : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (k : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hN0.le hkN (by norm_num)
      have h2 : (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hN0]; simp
      have h3 : 1 ≤ (k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
        calc (1 : ℝ) = (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := h2.symm
          _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith
    have hbk : c ^ (j + 1) ≤ b k ^ (j + 1) := pow_le_pow_left₀ hc.le hcb _
    have hA : 0 ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
        ((D * N + 1 - k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by positivity
    calc _ ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
          ((D * N + 1 - k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) / c ^ (j + 1) :=
          div_le_div_of_nonneg_left hA (by positivity) hbk
      _ = _ := by ring
  refine (Finset.sum_le_sum key).trans ?_
  rw [← Finset.mul_sum]
  have hrefl : ∑ k ∈ Finset.Ioc M (D * N), (((D * N + 1 - k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) =
      ∑ r ∈ Finset.Ioc 0 (D * N - M), ((r : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have hI : Finset.Ioc M (D * N) = Finset.Ico (M + 1) (D * N + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    have hI2 : Finset.Ioc 0 (D * N - M) = Finset.Ico (D * N + 1 + 1 - (D * N + 1))
        (D * N + 1 + 1 - (M + 1)) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hI, hI2, ← Finset.sum_Ico_reflect (fun r : ℕ => ((r : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) (M + 1)
      (show D * N + 1 ≤ D * N + 1 + 1 by omega)]
  rw [hrefl]
  have h1 := FcRigid_sum_third (D * N - M)
  have h2 : ((D * N - M : ℕ) : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * D := by
    have h3 : ((D * N - M : ℕ) : ℝ) ≤ (D : ℝ) * N := by
      calc ((D * N - M : ℕ) : ℝ) ≤ ((D * N : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
        _ = _ := by push_cast; ring
    calc ((D * N - M : ℕ) : ℝ) ^ (2 / 3 : ℝ) ≤ ((D : ℝ) * N) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h3 (by norm_num)
      _ = (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := Real.mul_rpow (by positivity) hN0.le
      _ ≤ (D : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
          gcongr
          calc (D : ℝ) ^ (2 / 3 : ℝ) ≤ (D : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
            _ = D := Real.rpow_one _
      _ = _ := by ring
  have hNN : (N : ℝ) ^ (-(2 / 3 : ℝ)) * (N : ℝ) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  have hC : 0 ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) * (c ^ (j + 1))⁻¹ := by positivity
  calc _ ≤ ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) * (c ^ (j + 1))⁻¹) *
        ((3 / 2) * ((N : ℝ) ^ (2 / 3 : ℝ) * D)) :=
        mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hC
    _ = (3 / 2) * (D : ℝ) * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹) *
        ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (N : ℝ) ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [hNN, mul_one]

/-- The rigidity sum of the proof of Lemma 4.1 [CVtG]: for `N^{-2/3+2τ'} ≤ κ ≤ 1`, `N^{τ'} ≥ 2`,
`b_k ≥ κ` and `b_k ≥ c k^{2/3} N^{-2/3}` for all `k ∈ ⟦1, DN⟧`,
`∑_k N^{τ'} N^{-2/3} 𝔯(k)^{-1/3} b_k^{-(j+1)} ≤ C N^{τ'} κ^{-j}`, `C` depending on `D`, `c`, `j`
only; the sum is split at `i₀ = ⌊N κ^{3/2}⌋` and at `⌊DN/2⌋`. -/
private lemma FcRigid_sum_bound (D N : ℕ) (hD : 2 ≤ D) (τ' c κ : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hj3 : j ≤ 3) (hN : 1 ≤ N) (hc : 0 < c) (hNτ : 2 ≤ (N : ℝ) ^ τ')
    (hκ0 : (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * τ') ≤ κ) (hκ1 : κ ≤ 1) (b : ℕ → ℝ)
    (hbκ : ∀ k ∈ Finset.Ioc 0 (D * N), κ ≤ b k)
    (hbc : ∀ k ∈ Finset.Ioc 0 (D * N),
      c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ b k) :
    ∑ k ∈ Finset.Ioc 0 (D * N), (N : ℝ) ^ τ' *
        ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) / b k ^ (j + 1) ≤
      (3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) * ((N : ℝ) ^ τ' * (κ ^ j)⁻¹) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : 0 < κ := lt_of_lt_of_le (by positivity) hκ0
  set T : ℝ := (N : ℝ) * κ ^ (3 / 2 : ℝ) with hTdef
  -- `T ≥ N^{3τ'} ≥ 8` and `T ≤ N`
  have hT8 : 8 ≤ T := by
    have h1 : (N : ℝ) ^ (-(1 : ℝ) + 3 * τ') ≤ κ ^ (3 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hκ0 (by norm_num : (0 : ℝ) ≤ 3 / 2)
      rw [← Real.rpow_mul hN0.le] at this
      convert this using 2
      ring
    have h2 : (N : ℝ) ^ (3 * τ') = (N : ℝ) ^ τ' * (N : ℝ) ^ τ' * (N : ℝ) ^ τ' := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
    have h3 : (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) + 3 * τ') = (N : ℝ) ^ (3 * τ') := by
      have : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      calc (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) + 3 * τ') =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) + 3 * τ') := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ (3 * τ') := by rw [← Real.rpow_add hN0]; ring_nf
    have h4 : 8 ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ τ' * (N : ℝ) ^ τ' := by
      have : (2 : ℝ) * 2 * 2 ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ τ' * (N : ℝ) ^ τ' :=
        mul_le_mul (mul_le_mul hNτ hNτ (by norm_num) (by positivity)) hNτ (by norm_num)
          (by positivity)
      linarith
    calc (8 : ℝ) ≤ (N : ℝ) ^ (3 * τ') := by rw [h2]; exact h4
      _ = (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) + 3 * τ') := h3.symm
      _ ≤ T := mul_le_mul_of_nonneg_left h1 hN0.le
  have hTN : T ≤ N := by
    have : κ ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hκ.le hκ1 (by norm_num)
    calc T ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left this hN0.le
      _ = N := mul_one _
  have hT0 : 0 < T := by linarith
  set i₀ : ℕ := ⌊T⌋₊ with hi₀def
  have hi₀T : (i₀ : ℝ) ≤ T := Nat.floor_le hT0.le
  have hi₀T2 : T / 2 ≤ (i₀ : ℝ) := by
    have := Nat.lt_floor_add_one T
    linarith
  have hi₀1 : 1 ≤ i₀ := by
    have : (0 : ℝ) < i₀ := by linarith
    exact_mod_cast this
  have hi₀N : i₀ ≤ N := Nat.floor_le_of_le hTN
  -- the split points
  have hn2 : 2 * N ≤ D * N := Nat.mul_le_mul_right N hD
  set M : ℕ := D * N / 2 with hMdef
  have hM2 : 2 * M ≤ D * N := by omega
  have hM2' : D * N < 2 * M + 2 := by omega
  have hNM : N ≤ M := by omega
  have hMn : M ≤ D * N := by omega
  have hi₀M : i₀ ≤ M := hi₀N.trans hNM
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le i₀) (hi₀M.trans hMn),
    ← Finset.sum_Ioc_consecutive _ hi₀M hMn]
  -- the three parts
  have r1 := FcRigid_regI D N τ' κ T j hN hκ b i₀ (by omega) hi₀T
    (fun k hk => hbκ k (Finset.mem_Ioc.2 ⟨(Finset.mem_Ioc.1 hk).1,
      (Finset.mem_Ioc.1 hk).2.trans (hi₀M.trans hMn)⟩))
  have r2 := FcRigid_regII D N τ' κ T c j hj hj3 hN hκ hc hTdef b i₀ M hi₀1 hi₀T2 hM2
    (fun k hk => hbc k (Finset.mem_Ioc.2 ⟨by have := (Finset.mem_Ioc.1 hk).1; omega,
      (Finset.mem_Ioc.1 hk).2.trans hMn⟩))
  have r3 := FcRigid_regIII D N hD τ' c j hN hc b M hM2' hMn hNM
    (fun k hk => hbc k (Finset.mem_Ioc.2 ⟨by have := (Finset.mem_Ioc.1 hk).1; omega,
      (Finset.mem_Ioc.1 hk).2⟩))
  -- simplify the first part: `T^{2/3} = N^{2/3} κ`
  have hT23 : T ^ (2 / 3 : ℝ) = (N : ℝ) ^ (2 / 3 : ℝ) * κ := by
    rw [hTdef, Real.mul_rpow hN0.le (by positivity), ← Real.rpow_mul hκ.le]
    norm_num
  have hNN : (N : ℝ) ^ (-(2 / 3 : ℝ)) * (N : ℝ) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  have hκj : 1 ≤ (κ ^ j)⁻¹ := by
    rw [one_le_inv₀ (pow_pos hκ _)]
    exact pow_le_one₀ hκ.le hκ1
  have r1' : (3 / 2) * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * T ^ (2 / 3 : ℝ))) /
      κ ^ (j + 1) = (3 / 2) * ((N : ℝ) ^ τ' * (κ ^ j)⁻¹) := by
    rw [hT23]
    have : (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * ((N : ℝ) ^ (2 / 3 : ℝ) * κ)) =
        (N : ℝ) ^ τ' * κ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (N : ℝ) ^ (2 / 3 : ℝ)) := by ring
    rw [this, hNN, mul_one, pow_succ]
    field_simp
  have hA0 : 0 ≤ (N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ := by positivity
  have r3' : (3 / 2) * (D : ℝ) * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹) ≤
      (3 / 2) * (D : ℝ) * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * (κ ^ j)⁻¹) := by
    have hD0 : (0 : ℝ) ≤ (3 / 2) * (D : ℝ) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hD0
    nlinarith
  calc _ ≤ (3 / 2) * ((N : ℝ) ^ τ' * (κ ^ j)⁻¹) +
        6 * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * (κ ^ j)⁻¹) +
        (3 / 2) * (D : ℝ) * ((N : ℝ) ^ τ' * (c ^ (j + 1))⁻¹ * (κ ^ j)⁻¹) := by
        rw [← r1'] ; linarith
    _ = _ := by ring

/-- A probability density `ρ` on `ℝ` that is continuous and positive exactly on `(a, b)`: the
properties of `ρ_N` used for the quantiles (2.20) [eq:gammak] (Definition 2.7 [defn_Mm]). -/
private structure FcRigid_Dens (ρ : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : Continuous ρ
  integ : Integrable ρ
  nonneg : ∀ t, 0 ≤ ρ t
  total : ∫ t, ρ t = 1
  lt : a < b
  zero : ∀ t, t ∉ Set.Ioo a b → ρ t = 0
  pos : ∀ t ∈ Set.Ioo a b, 0 < ρ t

/-- `ρ` vanishes to the right of `b`. -/
private lemma FcRigid_Dens.zero_right {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) {t : ℝ}
    (ht : b < t) : ρ t = 0 :=
  h.zero t fun hm => absurd hm.2 (not_lt.2 ht.le)

/-- The tail `∫_{(x,∞)} ρ` is the interval integral `∫_x^b ρ`. -/
private lemma FcRigid_tail_eq {ρ : ℝ → ℝ} (hρi : Integrable ρ) {b : ℝ}
    (hz : ∀ t, b < t → ρ t = 0) (x : ℝ) : ∫ t in Set.Ioi x, ρ t = ∫ t in x..b, ρ t := by
  rcases le_total x b with hxb | hxb
  · have h0 : ∫ t in Set.Ioi b, ρ t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t ht
    rw [← Set.Ioc_union_Ioi_eq_Ioi hxb, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hρi.integrableOn hρi.integrableOn, h0, add_zero,
      intervalIntegral.integral_of_le hxb]
  · have h0 : ∫ t in Set.Ioi x, ρ t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t (lt_of_le_of_lt hxb ht)
    have h1 : ∫ t in Set.Ioc b x, ρ t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t ht.1
    rw [h0, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxb, h1, neg_zero]

/-- The tail function `F(x) = ∫_x^b ρ` has derivative `-ρ(x)`. -/
private lemma FcRigid_F_hasDerivAt {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) (x : ℝ) :
    HasDerivAt (fun y => ∫ t in y..b, ρ t) (-ρ x) x := by
  have e : (fun y => ∫ t in y..b, ρ t) = fun y => -∫ t in b..y, ρ t := by
    funext y
    rw [intervalIntegral.integral_symm]
  rw [e]
  exact (h.cont.integral_hasStrictDerivAt b x).hasDerivAt.neg

/-- `F(a) = ∫_a^b ρ = 1`. -/
private lemma FcRigid_F_left {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) :
    ∫ t in a..b, ρ t = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset, h.total]
  intro t ht
  by_contra hn
  exact ht (h.zero t fun h' => hn ⟨h'.1, h'.2.le⟩)

/-- `F` is antitone. -/
private lemma FcRigid_F_anti {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) :
    Antitone (fun y => ∫ t in y..b, ρ t) :=
  antitone_of_deriv_nonpos (fun x => (FcRigid_F_hasDerivAt h x).differentiableAt) fun x => by
    rw [(FcRigid_F_hasDerivAt h x).deriv]
    linarith [h.nonneg x]

/-- The supremum defining the quantile is the point `x₀ ∈ (a, b)` with `F(x₀) = p`. -/
private lemma FcRigid_sSup {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) {x₀ p : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo a b) (hp : ∫ t in x₀..b, ρ t = p) :
    sSup {x : ℝ | p ≤ ∫ t in Set.Ioi x, ρ t} = x₀ := by
  have hd := FcRigid_F_hasDerivAt h
  have hanti := FcRigid_F_anti h
  have hz : ∀ t, b < t → ρ t = 0 := fun t ht => h.zero_right ht
  have hsanti : StrictAntiOn (fun y => ∫ t in y..b, ρ t) (Set.Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    linarith [h.pos x hx]
  refine IsGreatest.csSup_eq ⟨?_, fun x hx => ?_⟩
  · change p ≤ ∫ t in Set.Ioi x₀, ρ t
    rw [FcRigid_tail_eq h.integ hz, hp]
  · by_contra hlt
    have hlt := lt_of_not_ge hlt
    have hx' : p ≤ ∫ t in x..b, ρ t := by
      have : p ≤ ∫ t in Set.Ioi x, ρ t := hx
      rwa [FcRigid_tail_eq h.integ hz] at this
    have hx₀I : x₀ ∈ Set.Icc a b := ⟨hx₀.1.le, hx₀.2.le⟩
    rcases le_total x b with hxb | hxb
    · have := hsanti hx₀I ⟨by linarith [hx₀.1], hxb⟩ hlt
      simp only at this
      linarith
    · have h1 := hanti hxb
      have h2 := hsanti hx₀I ⟨hx₀.1.le.trans hx₀.2.le, le_rfl⟩ hx₀.2
      simp only at h1 h2
      linarith

/-- The quantile of index `j ∈ ⟦1, n⟧` lies in `(a, b)` and carries the tail mass `(j - 1/2)/n`
(2.20) [eq:gammak]. -/
private lemma FcRigid_quant_spec {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) {n j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    quant ρ n j ∈ Set.Ioo a b ∧
      ∫ t in quant ρ n j..b, ρ t = ((j : ℝ) - 1 / 2) / n := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hn : (0 : ℝ) < n := by linarith
  have hp0 : 0 < ((j : ℝ) - 1 / 2) / n := div_pos (by linarith) hn
  have hp1 : ((j : ℝ) - 1 / 2) / n < 1 := by
    rw [div_lt_one hn]; linarith
  have hcont : Continuous (fun y => ∫ t in y..b, ρ t) :=
    continuous_iff_continuousAt.2 fun x => (FcRigid_F_hasDerivAt h x).continuousAt
  have hFa := FcRigid_F_left h
  have hFb : ∫ t in b..b, ρ t = 0 := intervalIntegral.integral_same
  obtain ⟨x₀, hx₀, hFx₀⟩ := intermediate_value_Icc' h.lt.le hcont.continuousOn
    (show ((j : ℝ) - 1 / 2) / n ∈ Set.Icc (∫ t in b..b, ρ t) (∫ t in a..b, ρ t) from
      ⟨by rw [hFb]; exact hp0.le, by rw [hFa]; exact hp1.le⟩)
  have hxa : x₀ ≠ a := by
    rintro rfl
    simp only at hFx₀
    rw [hFa] at hFx₀
    linarith
  have hxb : x₀ ≠ b := by
    rintro rfl
    simp only at hFx₀
    rw [hFb] at hFx₀
    linarith
  have hmem : x₀ ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hx₀.1 (Ne.symm hxa), lt_of_le_of_ne hx₀.2 hxb⟩
  have hq : quant ρ n j = x₀ := FcRigid_sSup h hmem hFx₀
  rw [hq]
  exact ⟨hmem, hFx₀⟩

/-- The mass of `[u, v]` is the difference of the tails: `∫_u^v ρ = ∫_u^b ρ - ∫_v^b ρ`. -/
private lemma FcRigid_mass {ρ : ℝ → ℝ} (hc : Continuous ρ) (u v b : ℝ) :
    ∫ t in u..v, ρ t = (∫ t in u..b, ρ t) - ∫ t in v..b, ρ t := by
  have := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) u v)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) v b)
  linarith

/-- The consecutive quantiles `γ_{k+1} ≤ γ_k` enclose the mass `1/n` for `1 ≤ k < n`. -/
private lemma FcRigid_cell_mass {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    quant ρ n (k + 1) ≤ quant ρ n k ∧ ∫ t in quant ρ n (k + 1)..quant ρ n k, ρ t = 1 / n := by
  obtain ⟨-, h1⟩ := FcRigid_quant_spec (n := n) h hk (by omega)
  obtain ⟨-, h2⟩ := FcRigid_quant_spec (n := n) h (by omega : 1 ≤ k + 1) hkn
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : quant ρ n (k + 1) ≤ quant ρ n k := by
    by_contra hcon
    have h3 := FcRigid_F_anti h (le_of_lt (lt_of_not_ge hcon))
    simp only at h3
    rw [h1, h2] at h3
    have h4 := (div_le_div_iff_of_pos_right hn).1 h3
    push_cast at h4
    linarith
  refine ⟨hle, ?_⟩
  rw [FcRigid_mass h.cont _ _ b, h1, h2]
  push_cast
  field_simp
  ring

/-- On a cell `[u, v]` with `v ≤ b`, a monotone continuous `f` satisfies
`f(u) ∫_u^v ρ ≤ ∫_u^v ρ f ≤ f(v) ∫_u^v ρ`. -/
private lemma FcRigid_cell {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Iic b)) (hfm : MonotoneOn f (Set.Iic b)) {u v : ℝ} (huv : u ≤ v)
    (hv : v ≤ b) :
    f u * ∫ t in u..v, ρ t ≤ ∫ t in u..v, ρ t * f t ∧
      ∫ t in u..v, ρ t * f t ≤ f v * ∫ t in u..v, ρ t := by
  have hsub : Set.Icc u v ⊆ Set.Iic b := fun x hx => hx.2.trans hv
  have hgc : ContinuousOn (fun t => ρ t * f t) (Set.Icc u v) :=
    h.cont.continuousOn.mul (hfc.mono hsub)
  have hII : IntervalIntegrable (fun t => ρ t * f t) MeasureTheory.volume u v := by
    refine (hgc.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le huv]
  have hρI : ∀ c : ℝ, IntervalIntegrable (fun t => ρ t * c) MeasureTheory.volume u v := fun c =>
    (h.cont.mul continuous_const).intervalIntegrable _ _
  constructor
  · have := intervalIntegral.integral_mono_on huv (hρI (f u)) hII fun x hx => by
      have := hfm (hsub ⟨le_rfl, huv⟩) (hsub hx) hx.1
      exact mul_le_mul_of_nonneg_left this (h.nonneg x)
    rwa [intervalIntegral.integral_mul_const, mul_comm] at this
  · have := intervalIntegral.integral_mono_on huv hII (hρI (f v)) fun x hx => by
      have := hfm (hsub hx) (hsub ⟨huv, le_rfl⟩) hx.2
      exact mul_le_mul_of_nonneg_left this (h.nonneg x)
    rwa [intervalIntegral.integral_mul_const, mul_comm] at this

/-- The induction on the number of cells behind the discretization: for `p + 1 ≤ n`, with
`S_p = ∑_{k ≤ p} f(γ_k)`, `S_p/n - (f(γ_1) - f(γ_{p+1}))/n ≤ ∫_{γ_{p+1}}^{γ_1} ρ f ≤ S_p/n`. -/
private lemma FcRigid_disc_ind {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Iic b)) (hfm : MonotoneOn f (Set.Iic b)) {n : ℕ} (hn : 1 ≤ n) :
    ∀ p : ℕ, p + 1 ≤ n →
      ((∑ k ∈ Finset.Ioc 0 p, f (quant ρ n k)) -
          (f (quant ρ n 1) - f (quant ρ n (p + 1)))) / n ≤
          ∫ t in quant ρ n (p + 1)..quant ρ n 1, ρ t * f t ∧
        ∫ t in quant ρ n (p + 1)..quant ρ n 1, ρ t * f t ≤
          (∑ k ∈ Finset.Ioc 0 p, f (quant ρ n k)) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hgc : ContinuousOn (fun t => ρ t * f t) (Set.Iic b) := h.cont.continuousOn.mul hfc
  have hII : ∀ u v : ℝ, u ≤ b → v ≤ b →
      IntervalIntegrable (fun t => ρ t * f t) MeasureTheory.volume u v := by
    intro u v hu hv
    refine (hgc.mono ?_).intervalIntegrable
    intro x hx
    exact hx.2.trans (max_le hu hv)
  have hγb : ∀ k, 1 ≤ k → k ≤ n → quant ρ n k ≤ b := fun k hk hkn =>
    (FcRigid_quant_spec h hk hkn).1.2.le
  intro p
  induction p with
  | zero =>
    intro _
    simp
  | succ p ih =>
    intro hp
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hle, hmass⟩ := FcRigid_cell_mass h (by omega : 1 ≤ p + 1) hp
    have hcell := FcRigid_cell h f hfc hfm hle (hγb (p + 1) (by omega) (by omega))
    rw [hmass] at hcell
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hII (quant ρ n (p + 1 + 1)) (quant ρ n (p + 1)) (hγb _ (by omega) hp)
        (hγb _ (by omega) (by omega)))
      (hII (quant ρ n (p + 1)) (quant ρ n 1) (hγb _ (by omega) (by omega))
        (hγb _ (by omega) (by omega)))
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le p)]
    constructor
    · have e : f (quant ρ n (p + 1 + 1)) * (1 / n) = f (quant ρ n (p + 1 + 1)) / n := by ring
      rw [e] at hcell
      have e2 : ((∑ k ∈ Finset.Ioc 0 p, f (quant ρ n k)) + f (quant ρ n (p + 1)) -
          (f (quant ρ n 1) - f (quant ρ n (p + 1 + 1)))) / n =
          ((∑ k ∈ Finset.Ioc 0 p, f (quant ρ n k)) -
            (f (quant ρ n 1) - f (quant ρ n (p + 1)))) / n + f (quant ρ n (p + 1 + 1)) / n := by
        ring
      rw [e2, ← hsplit]
      linarith [hcell.1]
    · have e : f (quant ρ n (p + 1)) * (1 / n) = f (quant ρ n (p + 1)) / n := by ring
      rw [e] at hcell
      rw [← hsplit, add_div]
      linarith [hcell.2]

/-- The discretization at the quantiles (2.20) [eq:gammak]: for `f` monotone and continuous on
`(-∞, b]` with `0 ≤ f ≤ M` there, `|n⁻¹ ∑_k f(γ_k) - ∫ ρ f| ≤ M/n`. -/
private lemma FcRigid_disc {ρ : ℝ → ℝ} {a b : ℝ} (h : FcRigid_Dens ρ a b) (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Iic b)) (hfm : MonotoneOn f (Set.Iic b)) (M : ℝ)
    (hf0 : ∀ x, x ≤ b → 0 ≤ f x) (hfM : ∀ x, x ≤ b → f x ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    |(∑ k ∈ Finset.Ioc 0 n, f (quant ρ n k)) / n - ∫ t, ρ t * f t| ≤ M / n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hγb : ∀ k, 1 ≤ k → k ≤ n → quant ρ n k ≤ b := fun k hk hkn =>
    (FcRigid_quant_spec h hk hkn).1.2.le
  have hγa : ∀ k, 1 ≤ k → k ≤ n → a ≤ quant ρ n k := fun k hk hkn =>
    (FcRigid_quant_spec h hk hkn).1.1.le
  have hgc : ContinuousOn (fun t => ρ t * f t) (Set.Iic b) := h.cont.continuousOn.mul hfc
  have hII : ∀ u v : ℝ, u ≤ b → v ≤ b →
      IntervalIntegrable (fun t => ρ t * f t) MeasureTheory.volume u v := by
    intro u v hu hv
    refine (hgc.mono ?_).intervalIntegrable
    intro x hx
    exact hx.2.trans (max_le hu hv)
  have hab : a ≤ b := h.lt.le
  -- the whole integral is the integral over `[a, b]`
  have hsupp : ∫ t, ρ t * f t = ∫ t in a..b, ρ t * f t := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset]
    intro t ht
    by_contra hn'
    exact ht (show ρ t * f t = 0 by rw [h.zero t fun h' => hn' ⟨h'.1, h'.2.le⟩, zero_mul])
  have hγ1 := hγb 1 le_rfl hn
  have hγn := hγb n hn le_rfl
  have hγn' := hγa n hn le_rfl
  obtain ⟨-, hF1⟩ := FcRigid_quant_spec h (le_refl 1) hn
  obtain ⟨-, hFn⟩ := FcRigid_quant_spec h hn (le_refl n)
  have hFb : ∫ t in b..b, ρ t = 0 := intervalIntegral.integral_same
  have hFa := FcRigid_F_left h
  have hle : quant ρ n n ≤ quant ρ n 1 := by
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    have h3 := FcRigid_F_anti h (le_of_lt hcon)
    simp only at h3
    rw [hFn, hF1] at h3
    have h4 := (div_le_div_iff_of_pos_right hn0).1 h3
    have h5 : (n : ℝ) ≤ 1 := by push_cast at h4; linarith
    have h6 : n = 1 := by
      have : n ≤ 1 := by exact_mod_cast h5
      omega
    rw [h6] at hcon
    exact lt_irrefl _ hcon
  -- the end masses
  have m1 : ∫ t in quant ρ n 1..b, ρ t = 1 / (2 * n) := by
    rw [hF1]; push_cast; field_simp; ring
  have m2 : ∫ t in a..quant ρ n n, ρ t = 1 / (2 * n) := by
    rw [FcRigid_mass h.cont a _ b, hFa, hFn]
    field_simp
    ring
  have hm0 : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
  have hE1 := FcRigid_cell h f hfc hfm hγ1 le_rfl
  have hE2 := FcRigid_cell h f hfc hfm (hγn'.trans' le_rfl) hγn
  rw [m1] at hE1
  rw [m2] at hE2
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hI := FcRigid_disc_ind h f hfc hfm hn m (by omega)
  rw [← hm] at hI
  -- the decomposition of `∫_a^b`
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (hII (quant ρ n n) (quant ρ n 1) hγn hγ1) (hII (quant ρ n 1) b hγ1 le_rfl)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hII a (quant ρ n n) hab hγn) (hII (quant ρ n n) b hγn le_rfl)
  have hsum := Finset.sum_Ioc_succ_top (Nat.zero_le m) (fun k => f (quant ρ n k))
  rw [← hm] at hsum
  have hfb := hfM b le_rfl
  have hfM1 := hfM _ hγ1
  have hf1 := hf0 _ hγ1
  have hfn := hf0 _ hγn
  have hfa := hf0 a hab
  have hfMn := hfM _ hγn
  have hE1lo : 0 ≤ ∫ t in quant ρ n 1..b, ρ t * f t := le_trans (mul_nonneg hf1 hm0) hE1.1
  have hE2lo : 0 ≤ ∫ t in a..quant ρ n n, ρ t * f t := le_trans (mul_nonneg hfa hm0) hE2.1
  have hE1hi : ∫ t in quant ρ n 1..b, ρ t * f t ≤ M / (2 * n) := by
    refine hE1.2.trans ?_
    have := mul_le_mul_of_nonneg_right hfb hm0
    exact this.trans_eq (mul_one_div _ _)
  have hE2hi : ∫ t in a..quant ρ n n, ρ t * f t ≤ M / (2 * n) := by
    refine hE2.2.trans ?_
    have := mul_le_mul_of_nonneg_right hfMn hm0
    exact this.trans_eq (mul_one_div _ _)
  rw [hsupp, abs_le]
  have hMn : M / n = M / (2 * n) + M / (2 * n) := by field_simp; ring
  have hdiv1 : f (quant ρ n 1) / n ≤ M / n := div_le_div_of_nonneg_right hfM1 hn0.le
  have hdiv2 : 0 ≤ f (quant ρ n n) / n := div_nonneg hfn hn0.le
  have e1 : (∑ k ∈ Finset.Ioc 0 n, f (quant ρ n k)) / n =
      (∑ k ∈ Finset.Ioc 0 m, f (quant ρ n k)) / n + f (quant ρ n n) / n := by
    rw [hsum]; ring
  have e2 : ((∑ k ∈ Finset.Ioc 0 m, f (quant ρ n k)) -
      (f (quant ρ n 1) - f (quant ρ n n))) / n =
      (∑ k ∈ Finset.Ioc 0 m, f (quant ρ n k)) / n - f (quant ρ n 1) / n +
        f (quant ρ n n) / n := by ring
  rw [e2] at hI
  rw [e1]
  constructor <;> linarith [hI.1, hI.2]

/-- The mean-value bound for `1/a^j` against `1/b^j` for `j ≥ 1`, `|a - b| ≤ b/2`. -/
private lemma FcRigid_pw' (j : ℕ) (hj : 1 ≤ j) {a b : ℝ} (hb : 0 < b) (h : |a - b| ≤ b / 2) :
    |1 / a ^ j - 1 / b ^ j| ≤ j * 3 ^ j * (|a - b| / b ^ (j + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have := FcRigid_pw m hb h
  push_cast at this ⊢
  exact this

/-- The constant of `fcMom_rigid` for the exponent `j`. -/
private def FcRigid_K (D : ℕ) (c : ℝ) (j : ℕ) : ℝ :=
  j * 3 ^ j * (3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) + 1

/-- `FcRigid_K` is positive. -/
private lemma FcRigid_K_pos (D : ℕ) {c : ℝ} (hc : 0 < c) (j : ℕ) : 0 < FcRigid_K D c j := by
  unfold FcRigid_K
  positivity

/-- The comparison of the moments of a rigid spectrum with those of `ρ` (proof of Lemma 4.1
[CVtG]), for abstract eigenvalues `l`, the quantiles of a density `ρ` and the lower bound (2.21)
[eq:kappa_gamma_k]: the eigenvalue sum is compared with the quantile sum by the mean value
theorem and `FcRigid_sum_bound`, the quantile sum with the integral by `FcRigid_disc`. -/
private lemma FcRigid_core (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (τ' : ℝ)
    (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (hNτ : 2 ≤ (N : ℝ) ^ τ') {ρ : ℝ → ℝ} {a b : ℝ}
    (hd : FcRigid_Dens ρ a b) (l : ℕ → ℝ)
    (hkg : ∀ k, 1 ≤ k → k ≤ D * N →
      c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ b - quant ρ (D * N) k)
    (hrig : ∀ k, 1 ≤ k → k ≤ D * N → |l k - quant ρ (D * N) k| ≤
      (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))))
    (ξ : ℝ) (hξ1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * τ') ≤ ξ - b) (hξ2 : ξ - b ≤ 1) :
    |(∑ k ∈ Finset.Ioc 0 (D * N), 1 / (ξ - l k) ^ j) / ((D * N : ℕ) : ℝ) -
        ∫ t, ρ t * (1 / (ξ - t) ^ j)| ≤
      FcRigid_K D c j * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(1 : ℝ)) * (ξ - b) ^ (-(j : ℝ)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : 1 ≤ D * N := by nlinarith
  have hn0 : (0 : ℝ) < ((D * N : ℕ) : ℝ) := by exact_mod_cast hn1
  set κ : ℝ := ξ - b with hκdef
  have hκ : 0 < κ := lt_of_lt_of_le (by positivity) hξ1
  have hNt1 : (1 : ℝ) ≤ (N : ℝ) ^ τ' := by linarith
  -- the quantiles lie in `(a, b)`
  have hγb : ∀ k, 1 ≤ k → k ≤ D * N → quant ρ (D * N) k < b := fun k hk hkn =>
    (FcRigid_quant_spec hd hk hkn).1.2
  set γ : ℕ → ℝ := fun k => quant ρ (D * N) k with hγdef
  set bk : ℕ → ℝ := fun k => ξ - γ k with hbkdef
  have hbκ : ∀ k ∈ Finset.Ioc 0 (D * N), κ ≤ bk k := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have := hγb k (by omega) hk.2
    simp only [hbkdef, hγdef, hκdef]
    linarith
  have hbc : ∀ k ∈ Finset.Ioc 0 (D * N),
      c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ bk k := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have := hkg k (by omega) hk.2
    simp only [hbkdef, hγdef]
    linarith
  have hW := FcRigid_sum_bound D N hD τ' c κ j hj hj3 hN hc hNτ hξ1 hξ2 bk hbκ hbc
  -- `ε_k ≤ b_k / 2`
  have hε : ∀ k ∈ Finset.Ioc 0 (D * N), (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
      rk D N k ^ (-(1 / 3 : ℝ))) ≤ bk k / 2 := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hrk1 : (1 : ℝ) ≤ rk D N k := by
      unfold rk
      have : 1 ≤ min k (D * N + 1 - k) := by
        rw [Nat.le_min]; omega
      exact_mod_cast this
    have h1 : rk D N k ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hrk1 (by norm_num)
    have h2 : (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) ≤
        (N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
      calc _ = ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ))) * rk D N k ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ))) * 1 := mul_le_mul_of_nonneg_left h1 this
        _ = _ := mul_one _
    have h3 : (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * τ') =
        (N : ℝ) ^ (-(2 / 3 : ℝ)) * ((N : ℝ) ^ τ' * (N : ℝ) ^ τ') := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
    have h4 : 2 * ((N : ℝ) ^ τ' * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ κ := by
      refine le_trans ?_ hξ1
      rw [h3]
      have h5 : 0 ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) * (N : ℝ) ^ τ' := by positivity
      nlinarith
    have h6 := hbκ k (Finset.mem_Ioc.2 hk)
    linarith
  -- the eigenvalue sum against the quantile sum
  have hpt : ∀ k ∈ Finset.Ioc 0 (D * N), |1 / (ξ - l k) ^ j - 1 / (ξ - γ k) ^ j| ≤
      (j : ℝ) * 3 ^ j * ((N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) *
        rk D N k ^ (-(1 / 3 : ℝ))) / bk k ^ (j + 1)) := by
    intro k hk
    have hk' := Finset.mem_Ioc.1 hk
    have hbpos : 0 < bk k := lt_of_lt_of_le hκ (hbκ k hk)
    have hab : |(ξ - l k) - (ξ - γ k)| ≤
        (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) := by
      have := hrig k (by omega) hk'.2
      rw [show (ξ - l k) - (ξ - γ k) = -(l k - γ k) by ring, abs_neg]
      exact this
    have hpw := FcRigid_pw' j hj hbpos (hab.trans (hε k hk))
    refine hpw.trans ?_
    have hj0 : (0 : ℝ) ≤ (j : ℝ) * 3 ^ j := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hj0
    exact div_le_div_of_nonneg_right hab (by positivity)
  have hS1 : |(∑ k ∈ Finset.Ioc 0 (D * N), 1 / (ξ - l k) ^ j) / ((D * N : ℕ) : ℝ) -
      (∑ k ∈ Finset.Ioc 0 (D * N), 1 / (ξ - γ k) ^ j) / ((D * N : ℕ) : ℝ)| ≤
      ((j : ℝ) * 3 ^ j * ((3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) *
        ((N : ℝ) ^ τ' * (κ ^ j)⁻¹))) / ((D * N : ℕ) : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hn0, ← Finset.sum_sub_distrib]
    refine div_le_div_of_nonneg_right ?_ hn0.le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  -- the quantile sum against the integral
  have hfpos : ∀ x : ℝ, x ≤ b → 0 < ξ - x := fun x hx => by linarith
  have hS2 : |(∑ k ∈ Finset.Ioc 0 (D * N), 1 / (ξ - γ k) ^ j) / ((D * N : ℕ) : ℝ) -
      ∫ t, ρ t * (1 / (ξ - t) ^ j)| ≤ (κ ^ j)⁻¹ / ((D * N : ℕ) : ℝ) := by
    have := FcRigid_disc hd (fun x => 1 / (ξ - x) ^ j)
      (by
        refine ContinuousOn.div continuousOn_const
          ((continuousOn_const.sub continuousOn_id).pow j) fun x hx => ?_
        exact pow_ne_zero _ (hfpos x hx).ne')
      (by
        intro x hx y hy hxy
        have hx' := hfpos x hx
        have hy' := hfpos y hy
        exact one_div_le_one_div_of_le (pow_pos hy' j) (pow_le_pow_left₀ hy'.le (by linarith) j))
      ((κ ^ j)⁻¹)
      (fun x hx => by have := hfpos x hx; positivity)
      (fun x hx => by
        have := hfpos x hx
        rw [one_div]
        exact inv_anti₀ (pow_pos hκ j) (pow_le_pow_left₀ hκ.le (by simp only [hκdef]; linarith) j))
      hn1
    exact this
  -- assemble
  have hfin : |(∑ k ∈ Finset.Ioc 0 (D * N), 1 / (ξ - l k) ^ j) / ((D * N : ℕ) : ℝ) -
      ∫ t, ρ t * (1 / (ξ - t) ^ j)| ≤
      (((j : ℝ) * 3 ^ j * ((3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) *
        ((N : ℝ) ^ τ' * (κ ^ j)⁻¹))) + (κ ^ j)⁻¹) / ((D * N : ℕ) : ℝ) := by
    rw [add_div]
    refine le_trans ?_ (add_le_add hS1 hS2)
    exact abs_sub_le _ _ _
  refine hfin.trans ?_
  have hκj : 0 < (κ ^ j)⁻¹ := by positivity
  have hnN : (N : ℝ) ≤ ((D * N : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left N (by omega)
  have hrpow1 : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := Real.rpow_neg_one _
  have hrpowj : κ ^ (-(j : ℝ)) = (κ ^ j)⁻¹ := by rw [Real.rpow_neg hκ.le, Real.rpow_natCast]
  rw [hrpow1, hrpowj]
  unfold FcRigid_K
  have hnum : 0 ≤ ((j : ℝ) * 3 ^ j * ((3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) *
        ((N : ℝ) ^ τ' * (κ ^ j)⁻¹))) + (κ ^ j)⁻¹ := by positivity
  calc _ ≤ (((j : ℝ) * 3 ^ j * ((3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) *
        ((N : ℝ) ^ τ' * (κ ^ j)⁻¹))) + (κ ^ j)⁻¹) / (N : ℝ) :=
        div_le_div_of_nonneg_left hnum hN0 hnN
    _ ≤ (((j : ℝ) * 3 ^ j * ((3 / 2 + (6 + 3 / 2 * (D : ℝ)) * (c ^ (j + 1))⁻¹) *
        ((N : ℝ) ^ τ' * (κ ^ j)⁻¹))) + (N : ℝ) ^ τ' * (κ ^ j)⁻¹) / (N : ℝ) := by
        gcongr
        calc (κ ^ j)⁻¹ = 1 * (κ ^ j)⁻¹ := (one_mul _).symm
          _ ≤ (N : ℝ) ^ τ' * (κ ^ j)⁻¹ := mul_le_mul_of_nonneg_right hNt1 hκj.le
    _ = _ := by field_simp

/-- The density `ρ_N` of (2.19) [eq:density_rhoN] for a Hermitian `Λ` with `‖Λ‖ ≤ 1/10` is a
continuous probability density, positive exactly on `(E⁻, E⁺)` (Definition 2.7 [defn_Mm], §2.2). -/
private lemma FcRigid_dens {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    FcRigid_Dens (rho Λ) (Eminus Λ) (Eplus Λ) := by
  obtain ⟨hnn, hcont, hint, htot, -⟩ := rho_stieltjes Λ hΛ hℓ
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  refine ⟨hcont, hint, hnn, htot, hlt, fun t ht => ?_, fun t ht => ?_⟩
  · by_contra hne
    exact ht (hsupp ▸ Function.mem_support.2 hne)
  · have := hsupp ▸ ht
    exact lt_of_le_of_ne (hnn t) (Ne.symm (Function.mem_support.1 this))

/-- A sum over `(0, m]` is the sum over `range m` shifted by one. -/
private lemma FcRigid_sum_Ioc (g : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Ioc 0 m, g k = ∑ i ∈ Finset.range m, g (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le m), Finset.sum_range_succ, ih]

/-- `λ_{i+1} = eigs i`. -/
private lemma FcRigid_eigK_eigs {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (i : Fin (Fintype.card ι)) : eigK X ((i : ℕ) + 1) = eigs X i := by
  unfold eigK
  simp [i.isLt]

/-- `⟨(ξ - X)^{-j}⟩ = (card ι)⁻¹ ∑_{k=1}^{card ι} (ξ - λ_k)^{-j}`. -/
private lemma FcRigid_fcMom_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (j : ℕ) (ξ : ℝ) :
    fcMom X j ξ = (∑ k ∈ Finset.Ioc 0 (Fintype.card ι), 1 / (ξ - eigK X k) ^ j) /
      Fintype.card ι := by
  unfold fcMom
  congr 1
  rw [FcRigid_sum_Ioc (fun k => 1 / (ξ - eigK X k) ^ j),
    ← Fin.sum_univ_eq_sum_range (fun i => 1 / (ξ - eigK X (i + 1)) ^ j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FcRigid_eigK_eigs]

/-- The moments rescale with the matrix: `⟨(ξ - c⁻¹X)^{-j}⟩ = c^j ⟨(cξ - X)^{-j}⟩` for Hermitian
`X` and `c > 0` (proof of Lemma 4.1 [CVtG], `V = c⁻¹(H + cΛ)`). -/
theorem fcMom_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (c : ℝ) (hc : 0 < c) (j : ℕ) (ξ : ℝ) :
    fcMom (((c : ℂ))⁻¹ • X) j ξ = c ^ j * fcMom X j (c * ξ) := by
  have hcc : ((c : ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hcc]
  have hk := eigK_smul X hX c⁻¹ (inv_pos.2 hc)
  have hi : ∀ i : Fin (Fintype.card ι),
      eigs (((c⁻¹ : ℝ) : ℂ) • X) i = c⁻¹ * eigs X i := by
    intro i
    have := hk ((i : ℕ) + 1)
    rwa [FcRigid_eigK_eigs, FcRigid_eigK_eigs] at this
  have hterm : ∀ i : Fin (Fintype.card ι), 1 / (ξ - eigs (((c⁻¹ : ℝ) : ℂ) • X) i) ^ j =
      c ^ j * (1 / (c * ξ - eigs X i) ^ j) := by
    intro i
    rw [hi i, show ξ - c⁻¹ * eigs X i = c⁻¹ * (c * ξ - eigs X i) by field_simp, mul_pow, inv_pow,
      one_div, one_div, mul_inv, inv_inv]
  unfold fcMom
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, mul_div_assoc]

/-- The eigenvalues are at most `λ_1` (zero-based `eigs` against `eigK X 1`). -/
private lemma FcRigid_eigs_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (i : Fin (Fintype.card ι)) : eigs X i ≤ eigK X 1 := by
  have h0 : 0 < Fintype.card ι := Fintype.card_pos
  have e : eigK X 1 = eigs X ⟨0, h0⟩ := by
    unfold eigK; simp [h0]
  have e2 : eigs X = hX.eigenvalues₀ := by simp [eigs, hX]
  rw [e, e2]
  exact hX.eigenvalues₀_antitone (Fin.zero_le _)

/-- Strict decrease of `ξ ↦ ⟨(ξ - X)^{-2}⟩` to the right of the top eigenvalue `λ_1`. -/
private lemma FcRigid_mom_strictAnti {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {ξ₁ ξ₂ : ℝ} (h1 : eigK X 1 < ξ₁) (h12 : ξ₁ < ξ₂) :
    fcMom X 2 ξ₂ < fcMom X 2 ξ₁ := by
  have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold fcMom
  refine div_lt_div_of_pos_right (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_)
    hpos
  have hu : 0 < ξ₁ - eigs X i := by linarith [FcRigid_eigs_le X hX i]
  exact one_div_lt_one_div_of_lt (pow_pos hu 2)
    (pow_lt_pow_left₀ (by linarith) hu.le (by norm_num))

/-- `ξ ↦ ⟨(ξ - X)^{-2}⟩` is continuous to the right of the top eigenvalue `λ_1`. -/
private lemma FcRigid_mom_continuousOn {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    ContinuousOn (fun ξ => fcMom X 2 ξ) (Set.Ioi (eigK X 1)) := by
  unfold fcMom
  refine ContinuousOn.div_const (continuousOn_finsetSum _ fun i _ => ?_) _
  have hne : ∀ x ∈ Set.Ioi (eigK X 1), (x - eigs X i) ^ 2 ≠ 0 := by
    intro x hx
    have : eigs X i < x := lt_of_le_of_lt (FcRigid_eigs_le X hX i) hx
    exact pow_ne_zero _ (sub_ne_zero.2 this.ne')
  exact ContinuousOn.div continuousOn_const
    ((continuous_id.sub continuous_const).pow 2).continuousOn hne

/-- Bounds on `⟨(ξ - X)^{-2}⟩` to the right of `λ_1`: at least `n⁻¹ (ξ - λ_1)^{-2}` and at most
`(ξ - λ_1)^{-2}`. -/
private lemma FcRigid_mom_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {ξ : ℝ} (h1 : eigK X 1 < ξ) :
    1 / (ξ - eigK X 1) ^ 2 / Fintype.card ι ≤ fcMom X 2 ξ ∧
      fcMom X 2 ξ ≤ 1 / (ξ - eigK X 1) ^ 2 := by
  have h0 : 0 < Fintype.card ι := Fintype.card_pos
  have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h0
  have e : eigK X 1 = eigs X ⟨0, h0⟩ := by
    unfold eigK; simp [h0]
  have hu : 0 < ξ - eigK X 1 := by linarith
  constructor
  · unfold fcMom
    refine div_le_div_of_nonneg_right ?_ hpos.le
    calc 1 / (ξ - eigK X 1) ^ 2 = 1 / (ξ - eigs X ⟨0, h0⟩) ^ 2 := by rw [e]
      _ ≤ ∑ i, 1 / (ξ - eigs X i) ^ 2 :=
        Finset.single_le_sum (f := fun i => 1 / (ξ - eigs X i) ^ 2)
          (fun i _ => by
            have : 0 < ξ - eigs X i := by linarith [FcRigid_eigs_le X hX i]
            positivity) (Finset.mem_univ _)
  · unfold fcMom
    rw [div_le_iff₀ hpos]
    calc ∑ i, 1 / (ξ - eigs X i) ^ 2 ≤ ∑ _i : Fin (Fintype.card ι), 1 / (ξ - eigK X 1) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact one_div_le_one_div_of_le (pow_pos hu 2)
            (pow_le_pow_left₀ hu.le (by linarith [FcRigid_eigs_le X hX i]) 2)
      _ = _ := by simp [mul_comm]

/-- `ξ_fc` is the only root on `(λ_1, ∞)` of `t ⟨(ξ - X)^{-2}⟩ = 1`, for Hermitian `X` and
`t > 0` (proof of Lemma 4.1 [CVtG]). -/
theorem fcXi_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (t : ℝ) (ht : 0 < t) :
    eigK X 1 < fcXi X t ∧ t * fcMom X 2 (fcXi X t) = 1 ∧
      ∀ ξ : ℝ, eigK X 1 < ξ → t * fcMom X 2 ξ = 1 → ξ = fcXi X t := by
  have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- a root to the right of `λ_1`, by the intermediate value theorem
  obtain ⟨ξ₀, hξ₀, hroot⟩ : ∃ ξ₀, eigK X 1 < ξ₀ ∧ t * fcMom X 2 ξ₀ = 1 := by
    set l := eigK X 1 with hl
    set s : ℝ := Real.sqrt (t / Fintype.card ι) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
    have hs2 : s ^ 2 = t / Fintype.card ι := Real.sq_sqrt (by positivity)
    have ht0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    set R : ℝ := s + Real.sqrt t + 1 with hR
    have hRs : s < R := by rw [hR]; linarith
    have hlo : 1 ≤ t * fcMom X 2 (l + s) := by
      have := (FcRigid_mom_bounds X hX (show l < l + s by linarith)).1
      have e : t * (1 / (l + s - l) ^ 2 / Fintype.card ι) = 1 := by
        rw [add_sub_cancel_left, hs2]; field_simp
      calc 1 = t * (1 / (l + s - l) ^ 2 / Fintype.card ι) := e.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left this ht.le
    have hhi : t * fcMom X 2 (l + R) ≤ 1 := by
      have := (FcRigid_mom_bounds X hX (show l < l + R by linarith)).2
      rw [add_sub_cancel_left] at this
      have hR2 : t ≤ R ^ 2 := by
        have h1 : Real.sqrt t ≤ R := by rw [hR]; linarith
        calc t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
          _ ≤ R ^ 2 := pow_le_pow_left₀ ht0.le h1 2
      calc t * fcMom X 2 (l + R) ≤ t * (1 / R ^ 2) := mul_le_mul_of_nonneg_left this ht.le
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; exact hR2
    have hcont : ContinuousOn (fun ξ => t * fcMom X 2 ξ) (Set.Icc (l + s) (l + R)) :=
      (continuousOn_const.mul (FcRigid_mom_continuousOn X hX)).mono fun x hx =>
        (show l < x by linarith [hx.1])
    obtain ⟨ξ₀, hmem, hξ₀eq⟩ := intermediate_value_Icc' (show l + s ≤ l + R by linarith) hcont
      (show (1 : ℝ) ∈ Set.Icc (t * fcMom X 2 (l + R)) (t * fcMom X 2 (l + s)) from ⟨hhi, hlo⟩)
    exact ⟨ξ₀, by linarith [hmem.1], hξ₀eq⟩
  have hS : {ξ : ℝ | eigK X 1 < ξ ∧ t * fcMom X 2 ξ ≤ 1} = Set.Ici ξ₀ := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hlt
      have := mul_lt_mul_of_pos_left (FcRigid_mom_strictAnti X hX h1 (not_le.mp hlt)) ht
      linarith
    · intro h
      refine ⟨lt_of_lt_of_le hξ₀ h, ?_⟩
      rcases h.eq_or_lt with rfl | hlt
      · exact hroot.le
      · have := mul_lt_mul_of_pos_left (FcRigid_mom_strictAnti X hX hξ₀ hlt) ht
        linarith
  have hfc : fcXi X t = ξ₀ := by
    unfold fcXi
    rw [hS, csInf_Ici]
  rw [hfc]
  refine ⟨hξ₀, hroot, fun ξ h1 h2 => ?_⟩
  rcases lt_trichotomy ξ ξ₀ with hlt | heq | hgt
  · have := mul_lt_mul_of_pos_left (FcRigid_mom_strictAnti X hX h1 hlt) ht
    linarith
  · exact heq
  · have := mul_lt_mul_of_pos_left (FcRigid_mom_strictAnti X hX hξ₀ hgt) ht
    linarith

/-- `FcRigid_K` for `j ∈ {1, 2, 3}` is at most the maximum of the three. -/
private lemma FcRigid_K_le_max (D : ℕ) (c : ℝ) (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    FcRigid_K D c j ≤ max (max (FcRigid_K D c 1) (FcRigid_K D c 2)) (FcRigid_K D c 3) := by
  interval_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- Rigidity at real points outside the spectrum (proof of Lemma 4.1 [CVtG]): if the eigenvalues
of `X` satisfy (2.24) [eq:rigidity] with loss `N^{τ'}`, then for `j = 1, 2, 3` and real `ξ` with
`N^{-2/3+2τ'} ≤ ξ - E⁺ ≤ 1`,
`|⟨(ξ - X)^{-j}⟩ - ∫ ρ_N(x)(ξ - x)^{-j} dx| ≤ K N^{τ'} N^{-1} (ξ - E⁺)^{-j}`. -/
theorem fcMom_rigid (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ K : ℝ, 0 < K ∧ ∀ τ' : ℝ, 0 < τ' → τ' ≤ 1 / 10 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian → IsRigid D N A τ' X →
      ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ ξ : ℝ,
        (N : ℝ) ^ (-(2 / 3 : ℝ) + 2 * τ') ≤ ξ - Eplus (lam D N A) →
        ξ - Eplus (lam D N A) ≤ 1 →
        |fcMom X j ξ - rhoMom (lam D N A) 1 j ξ| ≤
          K * (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(1 : ℝ)) * (ξ - Eplus (lam D N A)) ^ (-(j : ℝ))) := by
  obtain ⟨c, C, hc, hC, N₁, hN₁⟩ := kappa_gamma_k D hD δA hδA
  refine ⟨max (max (FcRigid_K D c 1) (FcRigid_K D c 2)) (FcRigid_K D c 3),
    lt_max_of_lt_left (lt_max_of_lt_left (FcRigid_K_pos D hc 1)), fun τ' hτ0 hτ1 => ?_⟩
  have hev : ∀ᶠ N : ℕ in atTop, N₁ ≤ N ∧ 1 ≤ N ∧ (N : ℝ) ^ (-δA) ≤ 1 / 20 ∧
      2 ≤ (N : ℝ) ^ τ' :=
    (eventually_ge_atTop N₁).and ((eventually_ge_atTop 1).and
      ((((tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop).eventually
        (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))).and
      (((tendsto_rpow_atTop hτ0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN A hA X hX hrig j hj hj3 ξ hξ1 hξ2 => ?_⟩
  obtain ⟨hN1, hN2, hAN, hNτ⟩ := hN₀ N hN
  have hn1 : 1 ≤ D * N := by nlinarith
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  have hd := FcRigid_dens (lam D N A) hΛ hℓ
  have hcore := FcRigid_core D N hD hN2 c hc τ' j hj hj3 hNτ hd (eigK X)
    (fun k hk1 hk2 => (hN₁ N hN1 A hA k hk1 hk2).1) hrig ξ hξ1 hξ2
  have hcard : Fintype.card (Idx D N) = D * N := by simp
  have e1 : fcMom X j ξ = (∑ k ∈ Finset.Ioc 0 (D * N), 1 / (ξ - eigK X k) ^ j) /
      ((D * N : ℕ) : ℝ) := by
    rw [FcRigid_fcMom_eq, hcard]
  have e2 : rhoMom (lam D N A) 1 j ξ = ∫ t, rho (lam D N A) t * (1 / (ξ - t) ^ j) := by
    unfold rhoMom
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [one_mul]
    rw [mul_one_div]
  rw [e1, e2]
  refine hcore.trans ?_
  have hpos : 0 ≤ (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(1 : ℝ)) * (ξ - Eplus (lam D N A)) ^ (-(j : ℝ))) := by
    have hκ : 0 < ξ - Eplus (lam D N A) := lt_of_lt_of_le (by positivity) hξ1
    positivity
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (FcRigid_K_le_max D c j hj hj3) (by positivity)) (by
      have hκ : 0 < ξ - Eplus (lam D N A) := lt_of_lt_of_le (by positivity) hξ1
      positivity)

end RBMTransitionEdge

end
