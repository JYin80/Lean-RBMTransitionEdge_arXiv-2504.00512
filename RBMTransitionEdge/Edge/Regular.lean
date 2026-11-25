module

public import RBMTransitionEdge.Edge.Defs
public import RBMTransitionEdge.LocalLaw.Outside
public import RBMTransitionEdge.Localized.Pathwise
public import RBMTransitionEdge.Prob.BlockOU

@[expose] public section

/-!
# `η_*`-regularity of `V` in the proof of Lemma 4.1

The event on which `V = e^{-𝔱/2}H + Λ` is `N^{-2/3+𝔠}`-regular at its right edge, in the sense
of the external input EI-1, has probability at least `1 − N^{-D'}` (proof of Lemma 4.1 [CVtG]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- For `e < 0`, `N^e ≤ ε` once `N` is large. -/
private lemma Regular_pow_le (e ε : ℝ) (he : e < 0) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ e ≤ ε := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h.eventually (eventually_le_nhds hε))
  exact ⟨N₀, fun N hN => by simpa using hN₀ N hN⟩

/-- `N^{𝔠/8} ≤ N^{-11𝔠/8} N η^{3/2}` for `η ≥ η_* = N^{-2/3+𝔠}`: the error `N^{τ'}/(N η)` of
(2.23) [eq:aver_local] with `τ' = 𝔠/8` is at most `N^{-11𝔠/8} √η`. -/
private lemma Regular_core (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (η : ℝ)
    (hη : (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η) :
    (N : ℝ) ^ (a / 8) ≤ (N : ℝ) ^ (-(11 * a / 8)) * N * Real.sqrt η ^ 3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ ((-(2 / 3 : ℝ) + a) / 2) ≤ Real.sqrt η := by
    calc (N : ℝ) ^ ((-(2 / 3 : ℝ) + a) / 2) = Real.sqrt ((N : ℝ) ^ (-(2 / 3 : ℝ) + a)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
          ring_nf
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt hη
  have h2 : (N : ℝ) ^ (-1 + 3 * a / 2) ≤ Real.sqrt η ^ 3 := by
    calc (N : ℝ) ^ (-1 + 3 * a / 2) = ((N : ℝ) ^ ((-(2 / 3 : ℝ) + a) / 2)) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          ring_nf
      _ ≤ Real.sqrt η ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  calc (N : ℝ) ^ (a / 8)
      = (N : ℝ) ^ (-(11 * a / 8)) * (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 + 3 * a / 2) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
        congr 1
        ring
    _ ≤ (N : ℝ) ^ (-(11 * a / 8)) * N * Real.sqrt η ^ 3 := by
        rw [Real.rpow_one]
        gcongr

/-- First error term: `t / (N η) ≤ q √η` when `t ≤ q N η^{3/2}`. -/
private lemma Regular_err1 {t q Nn η : ℝ} (hNn : 0 < Nn) (hη : 0 < η)
    (hcore : t ≤ q * Nn * Real.sqrt η ^ 3) : t * (1 / (Nn * η)) ≤ q * Real.sqrt η := by
  have hsq : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  calc t ≤ q * Nn * Real.sqrt η ^ 3 := hcore
    _ = q * Real.sqrt η * (Nn * Real.sqrt η ^ 2) := by ring
    _ = q * Real.sqrt η * (Nn * η) := by rw [hsq]

/-- Second error term, outside the spectrum: with `S ≥ η` and `1 ≤ t`,
`t (1/(N S) + 1/((N η)² √S)) ≤ 2 q η/√S` when `t ≤ q N η^{3/2}`, `q ≤ 1`. -/
private lemma Regular_err2 {t q Nn η S : ℝ} (ht : 1 ≤ t) (hNn : 1 ≤ Nn) (hη : 0 < η)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hS : η ≤ S) (hcore : t ≤ q * Nn * Real.sqrt η ^ 3) :
    t * (1 / (Nn * S) + 1 / ((Nn * η) ^ 2 * Real.sqrt S)) ≤ 2 * q * (η / Real.sqrt S) := by
  have hNn0 : 0 < Nn := by linarith
  have hS0 : 0 < S := by linarith
  have hu : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS0
  have hsq : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  have hsS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  have hus : Real.sqrt η ≤ Real.sqrt S := Real.sqrt_le_sqrt hS
  have h1 : t * (1 / (Nn * S)) ≤ q * (η / Real.sqrt S) := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have e : q * (η / Real.sqrt S) * (Nn * S) = q * Nn * η * Real.sqrt S := by
      have e' : q * (η / Real.sqrt S) * (Nn * Real.sqrt S ^ 2) = q * Nn * η * Real.sqrt S := by
        field_simp
      rwa [hsS] at e'
    rw [e]
    calc t ≤ q * Nn * Real.sqrt η ^ 3 := hcore
      _ = q * Nn * Real.sqrt η ^ 2 * Real.sqrt η := by ring
      _ = q * Nn * η * Real.sqrt η := by rw [hsq]
      _ ≤ q * Nn * η * Real.sqrt S := by gcongr
  have h2 : t * (1 / ((Nn * η) ^ 2 * Real.sqrt S)) ≤ q * (η / Real.sqrt S) := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have e : q * (η / Real.sqrt S) * ((Nn * η) ^ 2 * Real.sqrt S) = q * Nn ^ 2 * η ^ 3 := by
      field_simp
    rw [e]
    have hb : 1 ≤ Nn * Real.sqrt η ^ 3 := by
      have : q * (Nn * Real.sqrt η ^ 3) ≤ Nn * Real.sqrt η ^ 3 := by
        have := mul_le_mul_of_nonneg_right hq1 (by positivity : 0 ≤ Nn * Real.sqrt η ^ 3)
        linarith
      nlinarith
    have hη3 : Real.sqrt η ^ 6 = η ^ 3 := by
      have : Real.sqrt η ^ 6 = (Real.sqrt η ^ 2) ^ 3 := by ring
      rw [this, hsq]
    calc t ≤ q * Nn * Real.sqrt η ^ 3 := hcore
      _ ≤ q * Nn * Real.sqrt η ^ 3 * (Nn * Real.sqrt η ^ 3) :=
          le_mul_of_one_le_right (by positivity) hb
      _ = q * Nn ^ 2 * Real.sqrt η ^ 6 := by ring
      _ = q * Nn ^ 2 * η ^ 3 := by rw [hη3]
  calc t * (1 / (Nn * S) + 1 / ((Nn * η) ^ 2 * Real.sqrt S))
      = t * (1 / (Nn * S)) + t * (1 / ((Nn * η) ^ 2 * Real.sqrt S)) := by ring
    _ ≤ 2 * q * (η / Real.sqrt S) := by nlinarith

/-- The rescaling of the constants: if `|y - m| ≤ q P`, `K⁻¹ P ≤ m ≤ K P`, `P = r P₀` with
`r ∈ [1, 51/50]`, `q ≤ 1/(4K)` and `c ∈ [1, 51/50]`, then `(4K)⁻¹ P₀ ≤ c y ≤ 4K P₀`. -/
private lemma Regular_scale {K c r P P0 m y q : ℝ} (hK : 1 ≤ K) (hc1 : 1 ≤ c)
    (hc2 : c ≤ 51 / 50) (hr1 : 1 ≤ r) (hr2 : r ≤ 51 / 50) (hP0 : 0 ≤ P0) (hP : P = r * P0)
    (hq : q ≤ 1 / (4 * K)) (hm1 : K⁻¹ * P ≤ m) (hm2 : m ≤ K * P)
    (hy : |y - m| ≤ q * P) : (4 * K)⁻¹ * P0 ≤ c * y ∧ c * y ≤ 4 * K * P0 := by
  have hK0 : 0 < K := by linarith
  have hP1 : 0 ≤ P := by rw [hP]; positivity
  have hP2 : P0 ≤ P := by rw [hP]; nlinarith
  have hP3 : P ≤ 51 / 50 * P0 := by rw [hP]; nlinarith
  have hKi : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hKi0 : 0 < K⁻¹ := inv_pos.mpr hK0
  have e4 : (4 * K)⁻¹ = K⁻¹ / 4 := by rw [mul_inv]; ring
  have hq' : q ≤ K⁻¹ / 4 := by rw [← e4]; simpa [one_div] using hq
  have hqP : q * P ≤ K⁻¹ / 4 * P := mul_le_mul_of_nonneg_right hq' hP1
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hy0 : 0 ≤ y := by nlinarith
  constructor
  · calc (4 * K)⁻¹ * P0 = K⁻¹ / 4 * P0 := by rw [e4]
      _ ≤ K⁻¹ / 4 * P := by gcongr
      _ ≤ y := by nlinarith
      _ ≤ c * y := le_mul_of_one_le_left hy0 hc1
  · have hyu : y ≤ (K + 1 / 4) * P := by nlinarith
    have hy0' : 0 ≤ (K + 1 / 4) * P := by positivity
    calc c * y ≤ 51 / 50 * ((K + 1 / 4) * P) := by
          apply mul_le_mul hc2 hyu hy0 (by norm_num)
      _ ≤ 51 / 50 * ((K + 1 / 4) * (51 / 50 * P0)) := by gcongr
      _ ≤ 4 * K * P0 := by nlinarith

/-- The bounds of (A.1) [square_root_density] for `K₀` hold for every larger constant. -/
private lemma Regular_Kmono {K₀ K s m : ℝ} (h0 : 0 < K₀) (hK : K₀ ≤ K) (hs : 0 ≤ s)
    (h : K₀⁻¹ * s ≤ m ∧ m ≤ K₀ * s) : K⁻¹ * s ≤ m ∧ m ≤ K * s :=
  ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ h0 hK) hs) h.1,
    le_trans h.2 (mul_le_mul_of_nonneg_right hK hs)⟩

/-- `|Im ⟨G(z)⟩ - Im m(z)| ≤ |⟨(G - M)⟩|` for `Im z > 0` and Hermitian `Λ`. -/
private lemma Regular_im_diff {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    |(ntr (res X z)).im - (mSol Λ z).im| ≤ ‖ntr ((res X z - MExt Λ z) * 1)‖ := by
  obtain ⟨h1, -, -⟩ := MExt_spec Λ hΛ z hz.ne'
  have h2 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  rw [Matrix.mul_one]
  have h3 : ntr (res X z - MExt Λ z) = ntr (res X z) - mExt Λ z := by
    rw [h1]
    simp [ntr, Matrix.trace_sub, mul_sub]
  rw [h3, h2]
  have := Complex.abs_im_le_norm (ntr (res X z) - mSol Λ z)
  simpa [Complex.sub_im] using this

/-- `Im ⟨G_V(z)⟩ = c Im ⟨G_X(cz)⟩` for `V = c⁻¹ X` (the rescaling of the proof of Lemma 4.1
[CVtG]). -/
private lemma Regular_im_res {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (c : ℝ)
    (hc : c ≠ 0) (z : ℂ) :
    (ntr (res (((c : ℂ))⁻¹ • X) z)).im = c * (ntr (res X ((c : ℂ) * z))).im := by
  rw [res_smul X c hc z]
  simp [ntr, Matrix.trace_smul]
  ring

set_option maxHeartbeats 1000000 in
/-- The deterministic core of the regularity step of Lemma 4.1 [CVtG]: for `X = H + Λ` with
`Λ = Λ(cA)`, the averaged bound (2.23) [eq:aver_local] (`hAver`), the improved averaged bound
outside the spectrum (`hOut`), the spectral inclusion of (2.24) [eq:rigidity] (`hSpec`), a norm
bound (`hNorm`) and (A.1) [square_root_density] for `Λ` (`hKd`) give the `η_*`-regularity of
`V = c⁻¹ X` at `c⁻¹ E⁺(Λ)` with `η_* = N^{-2/3+a}`, `c_V = 1/2`, `C_V = 4K`, for
`c ∈ [1, 51/50]`. -/
private lemma Regular_det {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (N : ℕ)
    (hN : 1 ≤ N) (a K c q : ℝ) (ha : 0 < a) (hK : 1 ≤ K) (hc1 : 1 ≤ c) (hc2 : c ≤ 51 / 50)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / (8 * K))
    (hcore : ∀ η : ℝ, (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η →
      (N : ℝ) ^ (a / 8) ≤ q * N * Real.sqrt η ^ 3)
    (X Λ : Matrix ι ι ℂ) (hX : X.IsHermitian) (hΛ : Λ.IsHermitian)
    (hE₁ : 17 / 10 ≤ Eplus Λ) (hE₂ : Eplus Λ ≤ 23 / 10) (hE₃ : Eminus Λ ≤ -(17 / 10))
    (hKd : ∀ z : ℂ, ‖z‖ ≤ (1 / 20 : ℝ)⁻¹ → 0 < z.im →
      (z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ) →
        K⁻¹ * Real.sqrt (kappa Λ z.re + z.im) ≤ (mSol Λ z).im ∧
          (mSol Λ z).im ≤ K * Real.sqrt (kappa Λ z.re + z.im)) ∧
      (z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ) →
        K⁻¹ * (z.im / Real.sqrt (kappa Λ z.re + z.im)) ≤ (mSol Λ z).im ∧
          (mSol Λ z).im ≤ K * (z.im / Real.sqrt (kappa Λ z.re + z.im))))
    (hAver : ∀ z ∈ specDom (1 / 20) N, ‖ntr ((res X z - MExt Λ z) * 1)‖ ≤
      (N : ℝ) ^ (a / 8) * (1 / ((N : ℝ) * |z.im|)))
    (hOut : ∀ z ∈ specDom (1 / 20) N, z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ) →
      ‖ntr ((res X z - MExt Λ z) * 1)‖ ≤ (N : ℝ) ^ (a / 8) *
        (1 / ((N : ℝ) * (kappa Λ z.re + |z.im|)) +
          1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa Λ z.re + |z.im|))))
    (hSpec : eigK X 1 ≤ Eplus Λ + (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8))
    (hNorm : opNorm X ≤ (N : ℝ) ^ (4 * K)) :
    etaRegular N a (1 / 2) (4 * K) (((c : ℂ))⁻¹ • X) (c⁻¹ * Eplus Λ) := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 < K := by linarith
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = c⁻¹ * Eplus Λ := ⟨_, rfl⟩
  have hEp : Eplus Λ = c * E₀ := by rw [hE₀]; field_simp
  rw [← hE₀]
  have hηs : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) + a) := Real.rpow_pos_of_pos hN0 _
  have ht1 : 1 ≤ (N : ℝ) ^ (a / 8) := Real.one_le_rpow hN1 (by linarith)
  have hsc1 : 1 ≤ Real.sqrt c := by
    rw [Real.one_le_sqrt]; exact hc1
  have hsc2 : Real.sqrt c ≤ 51 / 50 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hq4 : q ≤ 1 / (4 * K) :=
    hq.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  -- the rescaled point lies in the spectral domain
  have hdom : ∀ E' η' : ℝ, 0 ≤ E' → E' ≤ 3 → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η' → η' ≤ 51 / 5 →
      ((E' : ℂ) + (η' : ℂ) * Complex.I) ∈ specDom (1 / 20) N := by
    intro E' η' h0 h3 h1 h2
    have hη0 : 0 < η' := lt_of_lt_of_le hηs h1
    have hre : ((E' : ℂ) + (η' : ℂ) * Complex.I).re = E' := by simp
    have him : ((E' : ℂ) + (η' : ℂ) * Complex.I).im = η' := by simp
    refine ⟨?_, ?_⟩
    · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [hre, him, abs_of_nonneg h0, abs_of_pos hη0]
      norm_num
      linarith
    · rw [him, abs_of_pos hη0]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) h1
  -- inside the spectrum: the error of (2.23) is a small multiple of `Im m`
  have hin : ∀ E' η' : ℝ, E' ∈ Set.Icc (Eminus Λ) (Eplus Λ) → 0 ≤ E' → E' ≤ 3 →
      (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η' → η' ≤ 51 / 5 →
      |(ntr (res X ((E' : ℂ) + (η' : ℂ) * Complex.I))).im -
          (mSol Λ ((E' : ℂ) + (η' : ℂ) * Complex.I)).im| ≤
        q * Real.sqrt (kappa Λ E' + η') ∧
      K⁻¹ * Real.sqrt (kappa Λ E' + η') ≤ (mSol Λ ((E' : ℂ) + (η' : ℂ) * Complex.I)).im ∧
      (mSol Λ ((E' : ℂ) + (η' : ℂ) * Complex.I)).im ≤ K * Real.sqrt (kappa Λ E' + η') := by
    intro E' η' hI h0 h3 h1 h2
    have hη0 : 0 < η' := lt_of_lt_of_le hηs h1
    have hz := hdom E' η' h0 h3 h1 h2
    have hre : ((E' : ℂ) + (η' : ℂ) * Complex.I).re = E' := by simp
    have him : ((E' : ℂ) + (η' : ℂ) * Complex.I).im = η' := by simp
    have hκ0 : 0 ≤ kappa Λ E' := le_min (abs_nonneg _) (abs_nonneg _)
    have hd := Regular_im_diff X Λ hΛ _ (by rw [him]; exact hη0)
    have hg := hAver _ hz
    rw [him, abs_of_pos hη0] at hg
    have hsq : Real.sqrt η' ≤ Real.sqrt (kappa Λ E' + η') := Real.sqrt_le_sqrt (by linarith)
    refine ⟨?_, ?_⟩
    · calc _ ≤ _ := hd
        _ ≤ _ := hg
        _ ≤ q * Real.sqrt η' := Regular_err1 hN0 hη0 (hcore η' h1)
        _ ≤ _ := by gcongr
    · have := (hKd _ hz.1 (by rw [him]; exact hη0)).1 (by rw [hre]; exact hI)
      rw [hre, him] at this
      exact this
  -- outside the spectrum: the improved bound of `aver_local_outside`
  have hout : ∀ E' η' : ℝ, E' ∉ Set.Icc (Eminus Λ) (Eplus Λ) → 0 ≤ E' → E' ≤ 3 →
      (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η' → η' ≤ 51 / 5 →
      |(ntr (res X ((E' : ℂ) + (η' : ℂ) * Complex.I))).im -
          (mSol Λ ((E' : ℂ) + (η' : ℂ) * Complex.I)).im| ≤
        2 * q * (η' / Real.sqrt (kappa Λ E' + η')) ∧
      K⁻¹ * (η' / Real.sqrt (kappa Λ E' + η')) ≤
        (mSol Λ ((E' : ℂ) + (η' : ℂ) * Complex.I)).im ∧
      (mSol Λ ((E' : ℂ) + (η' : ℂ) * Complex.I)).im ≤
        K * (η' / Real.sqrt (kappa Λ E' + η')) := by
    intro E' η' hI h0 h3 h1 h2
    have hη0 : 0 < η' := lt_of_lt_of_le hηs h1
    have hz := hdom E' η' h0 h3 h1 h2
    have hre : ((E' : ℂ) + (η' : ℂ) * Complex.I).re = E' := by simp
    have him : ((E' : ℂ) + (η' : ℂ) * Complex.I).im = η' := by simp
    have hκ0 : 0 ≤ kappa Λ E' := le_min (abs_nonneg _) (abs_nonneg _)
    have hd := Regular_im_diff X Λ hΛ _ (by rw [him]; exact hη0)
    have hg := hOut _ hz (by rw [hre]; exact hI)
    rw [him, abs_of_pos hη0, hre] at hg
    refine ⟨?_, ?_⟩
    · calc _ ≤ _ := hd
        _ ≤ _ := hg
        _ ≤ 2 * q * (η' / Real.sqrt (kappa Λ E' + η')) :=
          Regular_err2 ht1 hN1 hη0 hq0 (by
            have : 1 / (8 * K) ≤ 1 := by
              rw [div_le_one (by positivity)]; linarith
            linarith) (by linarith) (hcore η' h1)
    · have := (hKd _ hz.1 (by rw [him]; exact hη0)).2 (by rw [hre]; exact hI)
      rw [hre, him] at this
      exact this
  -- clause (R1): `E ∈ [E₀ - 1/2, E₀]`
  have hR1 : ∀ E η : ℝ, E₀ - 1 / 2 ≤ E → E ≤ E₀ → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η → η ≤ 10 →
      (4 * K)⁻¹ * Real.sqrt (|E - E₀| + η) ≤
          (ntr (res (((c : ℂ))⁻¹ • X) ((E : ℂ) + (η : ℂ) * Complex.I))).im ∧
        (ntr (res (((c : ℂ))⁻¹ • X) ((E : ℂ) + (η : ℂ) * Complex.I))).im ≤
          4 * K * Real.sqrt (|E - E₀| + η) := by
    intro E η hE1 hE2 hη1 hη2
    have hη0 : 0 < η := lt_of_lt_of_le hηs hη1
    have hz : (c : ℂ) * ((E : ℂ) + (η : ℂ) * Complex.I) =
        ((c * E : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [Regular_im_res X c hc0.ne', hz]
    have hE'1 : Eplus Λ - c / 2 ≤ c * E := by rw [hEp]; nlinarith
    have hE'2 : c * E ≤ Eplus Λ := by rw [hEp]; nlinarith
    have hI : c * E ∈ Set.Icc (Eminus Λ) (Eplus Λ) := ⟨by linarith, hE'2⟩
    have hle : |Eplus Λ - c * E| ≤ |c * E - Eminus Λ| := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    have hκ : kappa Λ (c * E) = c * |E - E₀| := by
      unfold kappa
      rw [min_eq_left hle, abs_of_nonneg (by linarith : 0 ≤ Eplus Λ - c * E),
        abs_of_nonpos (by linarith : E - E₀ ≤ 0), hEp]
      ring
    obtain ⟨hd, hm1, hm2⟩ := hin (c * E) (c * η) hI (by linarith) (by linarith)
      (by nlinarith) (by nlinarith)
    have hs : Real.sqrt (kappa Λ (c * E) + c * η) = Real.sqrt c * Real.sqrt (|E - E₀| + η) := by
      rw [hκ, ← mul_add, Real.sqrt_mul hc0.le]
    exact Regular_scale hK hc1 hc2 hsc1 hsc2 (Real.sqrt_nonneg _) hs hq4 hm1 hm2 hd
  -- clause (R2), `E > E₀`: outside the spectrum
  have hR2 : ∀ E η : ℝ, E₀ < E → E ≤ E₀ + 1 / 2 → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η → η ≤ 10 →
      (4 * K)⁻¹ * (η / Real.sqrt (|E - E₀| + η)) ≤
          (ntr (res (((c : ℂ))⁻¹ • X) ((E : ℂ) + (η : ℂ) * Complex.I))).im ∧
        (ntr (res (((c : ℂ))⁻¹ • X) ((E : ℂ) + (η : ℂ) * Complex.I))).im ≤
          4 * K * (η / Real.sqrt (|E - E₀| + η)) := by
    intro E η hE1 hE2 hη1 hη2
    have hη0 : 0 < η := lt_of_lt_of_le hηs hη1
    have hz : (c : ℂ) * ((E : ℂ) + (η : ℂ) * Complex.I) =
        ((c * E : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [Regular_im_res X c hc0.ne', hz]
    have hE'1 : Eplus Λ < c * E := by rw [hEp]; nlinarith
    have hE'2 : c * E ≤ Eplus Λ + c / 2 := by rw [hEp]; nlinarith
    have hI : c * E ∉ Set.Icc (Eminus Λ) (Eplus Λ) := fun h => absurd h.2 (not_le.mpr hE'1)
    have hle : |Eplus Λ - c * E| ≤ |c * E - Eminus Λ| := by
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    have hκ : kappa Λ (c * E) = c * |E - E₀| := by
      unfold kappa
      rw [min_eq_left hle, abs_of_nonpos (by linarith : Eplus Λ - c * E ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ E - E₀), hEp]
      ring
    obtain ⟨hd, hm1, hm2⟩ := hout (c * E) (c * η) hI (by linarith) (by linarith)
      (by nlinarith) (by nlinarith)
    have hs : Real.sqrt (kappa Λ (c * E) + c * η) = Real.sqrt c * Real.sqrt (|E - E₀| + η) := by
      rw [hκ, ← mul_add, Real.sqrt_mul hc0.le]
    have hP : c * η / Real.sqrt (kappa Λ (c * E) + c * η) =
        Real.sqrt c * (η / Real.sqrt (|E - E₀| + η)) := by
      have hpos : 0 < Real.sqrt (|E - E₀| + η) :=
        Real.sqrt_pos.mpr (by positivity)
      have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
      have hsc : 0 < Real.sqrt c := by linarith
      rw [hs]
      calc c * η / (Real.sqrt c * Real.sqrt (|E - E₀| + η))
          = (Real.sqrt c * Real.sqrt c) * η / (Real.sqrt c * Real.sqrt (|E - E₀| + η)) := by
            rw [hcc]
        _ = Real.sqrt c * (η / Real.sqrt (|E - E₀| + η)) := by field_simp
    exact Regular_scale hK hc1 hc2 hsc1 hsc2 (by positivity) hP (by
      have : 2 * q ≤ 2 * (1 / (8 * K)) := by linarith
      calc 2 * q ≤ 2 * (1 / (8 * K)) := this
        _ = 1 / (4 * K) := by field_simp; ring) hm1 hm2 hd
  have hcinv : ((c : ℂ))⁻¹ = (((c⁻¹ : ℝ)) : ℂ) := by push_cast; rfl
  refine ⟨hR1, ?_, ?_, ?_⟩
  · intro E η hE1 hE2 hη1 hη2
    rcases eq_or_lt_of_le hE1 with h | h
    · rw [← h]
      have := hR1 E₀ η (by linarith) le_rfl hη1 hη2
      rw [sub_self, abs_zero, zero_add] at this ⊢
      rw [Real.div_sqrt]
      exact this
    · exact hR2 E η h hE2 hη1 hη2
  · rw [hcinv, eigK_smul X hX c⁻¹ (inv_pos.mpr hc0) 1]
    have h1 : c⁻¹ * eigK X 1 ≤ c⁻¹ * (Eplus Λ + (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8)) :=
      mul_le_mul_of_nonneg_left hSpec (inv_nonneg.mpr hc0.le)
    have h2 : c⁻¹ * (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + a) :=
      calc c⁻¹ * (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8) ≤ 1 * (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8) :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc1) (by positivity)
        _ ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + a) := by
            rw [one_mul]
            exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc c⁻¹ * eigK X 1 ≤ c⁻¹ * (Eplus Λ + (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8)) := h1
      _ = E₀ + c⁻¹ * (N : ℝ) ^ (-(2 / 3 : ℝ) + a / 8) := by rw [hE₀]; ring
      _ ≤ E₀ + (N : ℝ) ^ (-(2 / 3 : ℝ) + a) := by linarith
  · rw [opNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    calc c⁻¹ * opNorm X ≤ 1 * opNorm X :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc1) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hNorm

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma Regular_measurable_wig (n : ℕ) (i j : Fin n) :
    Measurable fun c : Coords n => wig n c i j := by
  unfold wig
  by_cases h1 : i = j
  · simp only [h1, ite_true]
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp measurable_fst))
  · by_cases h2 : i < j
    · simp only [h1, h2, ite_true, ite_false]
      exact measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
    · simp only [h1, h2, ite_false]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)))

/-- The array of `H(w)` is a measurable function of the coordinates `w`. -/
private lemma Regular_measurable_map (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => by
    by_cases h : p.1 = q.1
    · simp only [Matrix.of_symm_apply, blockH, h, ↓reduceIte]
      exact (Regular_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
    · simp only [Matrix.of_symm_apply, blockH, h, ↓reduceIte]
      exact measurable_const

/-- `Σ_a E_a = 1`. -/
private lemma Regular_sum_Ea (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

/-- `‖1‖ ≤ 1`. -/
private lemma Regular_opNorm_one (D N : ℕ) : opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- Union bound for four events. -/
private lemma Regular_union {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S₁ S₂ S₃ S₄ : Set α) (x : ℝ) (hx : 0 ≤ x) (h₁ : μ S₁ ≤ ENNReal.ofReal x)
    (h₂ : μ S₂ ≤ ENNReal.ofReal x) (h₃ : μ S₃ ≤ ENNReal.ofReal x)
    (h₄ : μ S₄ ≤ ENNReal.ofReal x) : μ (S₁ ∪ S₂ ∪ S₃ ∪ S₄) ≤ ENNReal.ofReal (4 * x) := by
  calc μ (S₁ ∪ S₂ ∪ S₃ ∪ S₄) ≤ μ (S₁ ∪ S₂ ∪ S₃) + μ S₄ := measure_union_le _ _
    _ ≤ (μ (S₁ ∪ S₂) + μ S₃) + μ S₄ := by gcongr; exact measure_union_le _ _
    _ ≤ ((μ S₁ + μ S₂) + μ S₃) + μ S₄ := by gcongr; exact measure_union_le _ _
    _ ≤ ((ENNReal.ofReal x + ENNReal.ofReal x) + ENNReal.ofReal x) + ENNReal.ofReal x := by
        gcongr
    _ = ENNReal.ofReal (4 * x) := by
        rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) hx,
          ← ENNReal.ofReal_add (by positivity) hx]
        ring_nf

/-- The regularity step of the proof of Lemma 4.1 [CVtG]: for `𝔠 ∈ (0, 1/10)` and
`𝔱 = N^{-1/3+𝔠}` there are `c_V, C_V > 0` such that, outside an event of probability
`≤ N^{-D'}`, `V = e^{-𝔱/2} H + Λ` is `N^{-2/3+𝔠}`-regular at `E_V⁺ = e^{-𝔱/2} E⁺(e^{𝔱/2} Λ)`. -/
theorem CVtG_regular (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) (ct : ℝ)
    (hct : 0 < ct) (hct' : ct < 1 / 10) :
    ∃ cV CV : ℝ, 0 < cV ∧ 0 < CV ∧ ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      blockLaw D N L {w | ¬ etaRegular N ct cV CV (edgeV D N A ct w)
          (Real.exp (-edgeTime N ct / 2) *
            Eplus (lam D N (((Real.exp (edgeTime N ct / 2) : ℝ) : ℂ) • A)))} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨K₀, hK₀, hKsq⟩ := square_root_density (1 / 20) (by norm_num)
  obtain ⟨Ce, hCe0, hCe⟩ := edge_close_to_edge_sc
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0K : K₀ ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  refine ⟨1 / 2, 4 * K, by norm_num, by positivity, fun D' hD' => ?_⟩
  have hD1 : 1 ≤ D := by omega
  obtain ⟨N₁, hN₁⟩ := aver_local D hD1 (δA / 2) (1 / 20) (by positivity) (by norm_num) C
    (ct / 8) (by positivity) (D' + 1) (by linarith)
  obtain ⟨N₂, hN₂⟩ := aver_local_outside D hD1 (δA / 2) (1 / 20) (by positivity) (by norm_num) C
    (ct / 8) (by positivity) (D' + 1) (by linarith)
  obtain ⟨N₃, hN₃⟩ := spec_inclusion D hD1 (δA / 2) (by positivity) C (ct / 8)
    (by positivity) (D' + 1) (by linarith)
  obtain ⟨N₄, hN₄⟩ := opNorm_noise_le D C 1 one_pos (D' + 1) (by linarith)
  obtain ⟨N₅, hN₅⟩ := Regular_pow_le (-(1 / 3 : ℝ) + ct) (1 / 100) (by linarith) (by norm_num)
  obtain ⟨N₆, hN₆⟩ := Regular_pow_le (-(δA / 2)) (min (1 / 20) (3 / (20 * Ce)))
    (by linarith) (by positivity)
  obtain ⟨N₇, hN₇⟩ := Regular_pow_le (-(11 * ct / 8)) (1 / (8 * K)) (by linarith) (by positivity)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ 4)), fun N hN L A hA => ?_⟩
  have hN₁' : N₁ ≤ N := by omega
  have hN₂' : N₂ ≤ N := by omega
  have hN₃' : N₃ ≤ N := by omega
  have hN₄' : N₄ ≤ N := by omega
  have hN₅' : N₅ ≤ N := by omega
  have hN₆' : N₆ ≤ N := by omega
  have hN₇' : N₇ ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  -- the rescaling constant `c = e^{𝔱/2}`
  set c : ℝ := Real.exp (edgeTime N ct / 2) with hc
  have ht0 : 0 < edgeTime N ct := Real.rpow_pos_of_pos hN0 _
  have ht1 : edgeTime N ct ≤ 1 / 100 := hN₅ N hN₅'
  have hc1 : 1 ≤ c := Real.one_le_exp (by positivity)
  have hc2 : c ≤ 51 / 50 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := edgeTime N ct / 2) (by positivity)
      (by linarith)
    refine this.le.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hc0 : 0 < c := by linarith
  have hexp : Real.exp (-edgeTime N ct / 2) = c⁻¹ := by
    rw [hc, neg_div, Real.exp_neg]
  -- the coupling of `X = H + Λ(cA)`
  set A' : Matrix (Fin N) (Fin N) ℂ := ((c : ℝ) : ℂ) • A with hA'
  have hs1 : (N : ℝ) ^ (-(δA / 2)) ≤ 1 / 20 :=
    (hN₆ N hN₆').trans (min_le_left _ _)
  have hs2 : (N : ℝ) ^ (-(δA / 2)) ≤ 3 / (20 * Ce) :=
    (hN₆ N hN₆').trans (min_le_right _ _)
  have hs0 : 0 < (N : ℝ) ^ (-(δA / 2)) := Real.rpow_pos_of_pos hN0 _
  have hAn : opNorm A' ≤ (N : ℝ) ^ (-(δA / 2)) := by
    rw [hA', opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have h1 : (N : ℝ) ^ (-δA) = (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(δA / 2)) := by
      rw [← Real.rpow_add hN0]
      ring_nf
    calc c * opNorm A ≤ c * (N : ℝ) ^ (-δA) := by gcongr
      _ = c * (N : ℝ) ^ (-(δA / 2)) * (N : ℝ) ^ (-(δA / 2)) := by rw [h1]; ring
      _ ≤ 1 * (N : ℝ) ^ (-(δA / 2)) := by
          gcongr
          nlinarith
      _ = _ := one_mul _
  have hΛn : opNorm (lam D N A') ≤ 2 * (N : ℝ) ^ (-(δA / 2)) :=
    (opNorm_lam_le D N A').trans (by linarith)
  have hΛ1 : opNorm (lam D N A') ≤ 1 / 10 := hΛn.trans (by linarith)
  have hne : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛh := lam_isHermitian D N A'
  have hedge := hCe (Idx D N) (lam D N A') hΛh hΛ1
  have hCe' : Ce * opNorm (lam D N A') ≤ 3 / 10 := by
    calc Ce * opNorm (lam D N A') ≤ Ce * (2 * (3 / (20 * Ce))) := by gcongr; linarith
      _ = 3 / 10 := by field_simp; ring
  have hE₁ : 17 / 10 ≤ Eplus (lam D N A') := by
    have := (abs_le.mp ((le_add_of_nonneg_right (abs_nonneg _)).trans (hedge.trans hCe') :
      |2 - Eplus (lam D N A')| ≤ 3 / 10)).2
    linarith
  have hE₂ : Eplus (lam D N A') ≤ 23 / 10 := by
    have := (abs_le.mp ((le_add_of_nonneg_right (abs_nonneg _)).trans (hedge.trans hCe') :
      |2 - Eplus (lam D N A')| ≤ 3 / 10)).1
    linarith
  have hE₃ : Eminus (lam D N A') ≤ -(17 / 10) := by
    have := (abs_le.mp ((le_add_of_nonneg_left (abs_nonneg _)).trans (hedge.trans hCe') :
      |2 + Eminus (lam D N A')| ≤ 3 / 10)).2
    linarith
  have hKd : ∀ z : ℂ, ‖z‖ ≤ (1 / 20 : ℝ)⁻¹ → 0 < z.im →
      (z.re ∈ Set.Icc (Eminus (lam D N A')) (Eplus (lam D N A')) →
        K⁻¹ * Real.sqrt (kappa (lam D N A') z.re + z.im) ≤ (mSol (lam D N A') z).im ∧
          (mSol (lam D N A') z).im ≤ K * Real.sqrt (kappa (lam D N A') z.re + z.im)) ∧
      (z.re ∉ Set.Icc (Eminus (lam D N A')) (Eplus (lam D N A')) →
        K⁻¹ * (z.im / Real.sqrt (kappa (lam D N A') z.re + z.im)) ≤
            (mSol (lam D N A') z).im ∧
          (mSol (lam D N A') z).im ≤
            K * (z.im / Real.sqrt (kappa (lam D N A') z.re + z.im))) := by
    intro z hz hz0
    obtain ⟨-, h⟩ := hKsq (Idx D N) (lam D N A') hΛh hΛ1
    obtain ⟨hi, ho⟩ := h z hz hz0
    exact ⟨fun hre => Regular_Kmono hK₀ hK0K (Real.sqrt_nonneg _) (hi hre),
      fun hre => Regular_Kmono hK₀ hK0K (div_nonneg hz0.le (Real.sqrt_nonneg _)) (ho hre)⟩
  -- the four local-law events for the law of `H`
  set μ : Measure (Idx D N → Idx D N → ℂ) :=
    (blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w) with hμdef
  have hμ : LLClass D N C 1 μ := llClass_blockH D N C L
  set S₁ : Set (Idx D N → Idx D N → ℂ) :=
    {h | ∃ z ∈ specDom (1 / 20) N, (N : ℝ) ^ (ct / 8) * (1 / ((N : ℝ) * |z.im|)) <
      ‖ntr ((res (Matrix.of h + lam D N A') z - MExt (lam D N A') z) * 1)‖} with hS₁
  set S₂ : Set (Idx D N → Idx D N → ℂ) :=
    {h | ∃ z ∈ specDom (1 / 20) N,
      z.re ∉ Set.Icc (Eminus (lam D N A')) (Eplus (lam D N A')) ∧
      (N : ℝ) ^ (ct / 8) * (1 / ((N : ℝ) * (kappa (lam D N A') z.re + |z.im|)) +
        1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa (lam D N A') z.re + |z.im|))) <
      ‖ntr ((res (Matrix.of h + lam D N A') z - MExt (lam D N A') z) *
        ∑ a, (fun _ : Fin D => (1 : ℂ)) a • Ea D N a)‖} with hS₂
  set S₃ : Set (Idx D N → Idx D N → ℂ) :=
    {h | Eplus (lam D N A') + (N : ℝ) ^ (-(2 / 3 : ℝ) + ct / 8) <
          eigK (Matrix.of h + lam D N A') 1 ∨
        eigK (Matrix.of h + lam D N A') (D * N) <
          Eminus (lam D N A') - (N : ℝ) ^ (-(2 / 3 : ℝ) + ct / 8)} with hS₃
  set S₄ : Set (Idx D N → Idx D N → ℂ) := {h | (N : ℝ) ^ (1 : ℝ) < opNorm (Matrix.of h)}
    with hS₄
  have e₁ : μ S₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    hN₁ N hN₁' 1 zero_le_one le_rfl μ hμ A' hAn 1 (Regular_opNorm_one D N)
  have e₂ : μ S₂ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    hN₂ N hN₂' 1 zero_le_one le_rfl μ hμ A' hAn (fun _ => 1) (fun _ => by simp)
  have e₃ : μ S₃ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) :=
    hN₃ N hN₃' 1 zero_le_one le_rfl μ hμ A' hAn
  have e₄ : μ S₄ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) := hN₄ N hN₄' 1 μ hμ
  -- off the four events, `V` is regular
  have hsub : {w | ¬ etaRegular N ct (1 / 2) (4 * K) (edgeV D N A ct w)
      (Real.exp (-edgeTime N ct / 2) * Eplus (lam D N A'))} ⊆
      (fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w)) ⁻¹' (S₁ ∪ S₂ ∪ S₃ ∪ S₄) := by
    intro w hw
    by_contra hnot
    apply hw
    simp only [Set.mem_preimage, Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hnot
    have hAver : ∀ z ∈ specDom (1 / 20) N,
        ‖ntr ((res (blockH D N w + lam D N A') z - MExt (lam D N A') z) * 1)‖ ≤
          (N : ℝ) ^ (ct / 8) * (1 / ((N : ℝ) * |z.im|)) :=
      fun z hz => not_lt.mp fun h => h₁ ⟨z, hz, h⟩
    have hsum : ∑ a : Fin D, (fun _ : Fin D => (1 : ℂ)) a • Ea D N a = 1 := by
      simp [Regular_sum_Ea]
    have hOut : ∀ z ∈ specDom (1 / 20) N,
        z.re ∉ Set.Icc (Eminus (lam D N A')) (Eplus (lam D N A')) →
        ‖ntr ((res (blockH D N w + lam D N A') z - MExt (lam D N A') z) * 1)‖ ≤
          (N : ℝ) ^ (ct / 8) * (1 / ((N : ℝ) * (kappa (lam D N A') z.re + |z.im|)) +
            1 / (((N : ℝ) * |z.im|) ^ 2 * Real.sqrt (kappa (lam D N A') z.re + |z.im|))) := by
      intro z hz hre
      refine not_lt.mp fun h => h₂ ⟨z, hz, hre, ?_⟩
      rw [hsum]
      exact h
    have hSpec : eigK (blockH D N w + lam D N A') 1 ≤
        Eplus (lam D N A') + (N : ℝ) ^ (-(2 / 3 : ℝ) + ct / 8) :=
      not_lt.mp fun h => h₃ (Or.inl h)
    have hNorm : opNorm (blockH D N w + lam D N A') ≤ (N : ℝ) ^ (4 * K) := by
      have h4 : opNorm (blockH D N w) ≤ (N : ℝ) ^ (1 : ℝ) := not_lt.mp h₄
      rw [Real.rpow_one] at h4
      calc opNorm (blockH D N w + lam D N A')
          ≤ opNorm (blockH D N w) + opNorm (lam D N A') := opNorm_add_le _ _
        _ ≤ (N : ℝ) + 1 := by linarith
        _ ≤ (N : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
        _ ≤ (N : ℝ) ^ (4 * K) := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have hdet := Regular_det (ι := Idx D N) N hN1 ct K c ((N : ℝ) ^ (-(11 * ct / 8))) hct hK1 hc1
      hc2 (Real.rpow_nonneg hN0.le _) (hN₇ N hN₇') (fun η hη => Regular_core N hN1 ct η hη)
      (blockH D N w + lam D N A') (lam D N A') (HLam_isHermitian D N A' w) hΛh hE₁ hE₂ hE₃ hKd
      hAver hOut hSpec hNorm
    have hV : edgeV D N A ct w = ((c : ℂ))⁻¹ • (blockH D N w + lam D N A') := by
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      unfold edgeV
      rw [hexp, smul_add, hA', ← lam_smul D N A c, smul_smul, inv_mul_cancel₀ hc', one_smul]
      rw [Complex.ofReal_inv]
    rw [hV, hexp]
    exact hdet
  have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    Regular_measurable_map D N
  have hxN : 4 * (N : ℝ) ^ (-(D' + 1)) ≤ (N : ℝ) ^ (-D') := by
    have h1 : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
      rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
    rw [h1]
    have h2 : 4 * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]
      exact hN4r
    have h3 : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
    nlinarith
  calc blockLaw D N L {w | ¬ etaRegular N ct (1 / 2) (4 * K) (edgeV D N A ct w)
        (Real.exp (-edgeTime N ct / 2) * Eplus (lam D N A'))}
      ≤ blockLaw D N L ((fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w)) ⁻¹'
          (S₁ ∪ S₂ ∪ S₃ ∪ S₄)) := measure_mono hsub
    _ ≤ μ (S₁ ∪ S₂ ∪ S₃ ∪ S₄) := Measure.le_map_apply hf.aemeasurable _
    _ ≤ ENNReal.ofReal (4 * (N : ℝ) ^ (-(D' + 1))) :=
        Regular_union μ S₁ S₂ S₃ S₄ _ (Real.rpow_nonneg hN0.le _) e₁ e₂ e₃ e₄
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal hxN

end RBMTransitionEdge

end
