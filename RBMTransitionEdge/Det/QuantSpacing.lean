module

public import RBMTransitionEdge.Det.Density
public import RBMTransitionEdge.LocalLaw.FarDet

@[expose] public section

/-!
# The spacing of the quantiles

Upper and lower bounds on the distance of two quantiles (2.20) [eq:gammak] whose indices differ
by at most `N^τ`, for `ρ_N` and for the semicircle density, from the square-root behaviour (A.1)
[square_root_density] and (2.21) [eq:kappa_gamma_k].
-/

open MeasureTheory

noncomputable section
open Classical

namespace RBMTransitionEdge

section QSTail

open Set

/-- A probability density `ρ` on `ℝ`, continuous, positive exactly on `(a, b)`. -/
private structure QS_Dens (ρ : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : Continuous ρ
  integ : Integrable ρ
  nonneg : ∀ t, 0 ≤ ρ t
  total : ∫ t, ρ t = 1
  lt : a < b
  zero : ∀ t, t ∉ Ioo a b → ρ t = 0
  pos : ∀ t ∈ Ioo a b, 0 < ρ t

private lemma QS_Dens.zero_right {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) {t : ℝ} (ht : b < t) :
    ρ t = 0 :=
  h.zero t fun hm => absurd hm.2 (not_lt.2 ht.le)

/-- The tail `F(x) = ∫_x^∞ ρ`. -/
private def QS_F (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Ioi x, ρ t

private lemma QS_F_eq {ρ : ℝ → ℝ} (hρi : Integrable ρ) {b : ℝ} (hz : ∀ t, b < t → ρ t = 0)
    (x : ℝ) : QS_F ρ x = ∫ t in x..b, ρ t := by
  unfold QS_F
  rcases le_total x b with hxb | hxb
  · have h0 : ∫ t in Ioi b, ρ t = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t ht
    rw [← Ioc_union_Ioi_eq_Ioi hxb, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hρi.integrableOn hρi.integrableOn, h0, add_zero,
      intervalIntegral.integral_of_le hxb]
  · have h0 : ∫ t in Ioi x, ρ t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t (lt_of_le_of_lt hxb ht)
    have h1 : ∫ t in Ioc b x, ρ t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => hz t ht.1
    rw [h0, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxb, h1, neg_zero]

private lemma QS_F_hasDerivAt {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) (x : ℝ) :
    HasDerivAt (QS_F ρ) (-ρ x) x := by
  have e : QS_F ρ = fun y => -∫ t in b..y, ρ t := by
    funext y
    rw [QS_F_eq h.integ (fun t ht => h.zero_right ht) y, intervalIntegral.integral_symm]
  rw [e]
  exact (h.cont.integral_hasStrictDerivAt b x).hasDerivAt.neg

private lemma QS_F_left {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) : QS_F ρ a = 1 := by
  rw [QS_F_eq h.integ (b := b) (fun t ht => h.zero_right ht) a,
    intervalIntegral.integral_eq_integral_of_support_subset, h.total]
  intro t ht
  by_contra hn
  exact ht (h.zero t fun h' => hn ⟨h'.1, h'.2.le⟩)

private lemma QS_F_right {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) : QS_F ρ b = 0 := by
  rw [QS_F_eq h.integ (fun t ht => h.zero_right ht) b, intervalIntegral.integral_same]

private lemma QS_F_anti {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) : Antitone (QS_F ρ) :=
  antitone_of_deriv_nonpos (fun x => (QS_F_hasDerivAt h x).differentiableAt) fun x => by
    rw [(QS_F_hasDerivAt h x).deriv]
    linarith [h.nonneg x]

/-- The supremum defining the quantile is the point `x₀ ∈ (a, b)` with `F(x₀) = p`. -/
private lemma QS_sSup {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) {x₀ p : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (hp : QS_F ρ x₀ = p) :
    sSup {x : ℝ | p ≤ ∫ t in Ioi x, ρ t} = x₀ := by
  have hd := QS_F_hasDerivAt h
  have hanti := QS_F_anti h
  have hsanti : StrictAntiOn (QS_F ρ) (Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    linarith [h.pos x hx]
  refine IsGreatest.csSup_eq ⟨?_, fun x hx => ?_⟩
  · change p ≤ QS_F ρ x₀
    rw [hp]
  · by_contra hlt
    have hlt := lt_of_not_ge hlt
    have hx' : p ≤ QS_F ρ x := hx
    have hx₀I : x₀ ∈ Icc a b := ⟨hx₀.1.le, hx₀.2.le⟩
    rcases le_total x b with hxb | hxb
    · have := hsanti hx₀I ⟨by linarith [hx₀.1], hxb⟩ hlt
      linarith
    · have h1 := hanti hxb
      have h2 := hsanti hx₀I ⟨hx₀.1.le.trans hx₀.2.le, le_rfl⟩ hx₀.2
      linarith

/-- The quantile of index `j ∈ ⟦1, n⟧` lies in `(a, b)` and carries the tail mass `(j - 1/2)/n`
(2.20) [eq:gammak]. -/
private lemma QS_quant_spec {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) {n j : ℕ} (hj : 1 ≤ j)
    (hjn : j ≤ n) :
    quant ρ n j ∈ Ioo a b ∧ QS_F ρ (quant ρ n j) = ((j : ℝ) - 1 / 2) / n := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hn : (0 : ℝ) < n := by linarith
  have hp0 : 0 < ((j : ℝ) - 1 / 2) / n := div_pos (by linarith) hn
  have hp1 : ((j : ℝ) - 1 / 2) / n < 1 := by
    rw [div_lt_one hn]; linarith
  have hcont : Continuous (QS_F ρ) :=
    continuous_iff_continuousAt.2 fun x => (QS_F_hasDerivAt h x).continuousAt
  have hFa := QS_F_left h
  have hFb := QS_F_right h
  obtain ⟨x₀, hx₀, hFx₀⟩ := intermediate_value_Icc' h.lt.le hcont.continuousOn
    (show ((j : ℝ) - 1 / 2) / n ∈ Icc (QS_F ρ b) (QS_F ρ a) from
      ⟨by rw [hFb]; exact hp0.le, by rw [hFa]; exact hp1.le⟩)
  have hxa : x₀ ≠ a := by
    rintro rfl
    rw [hFa] at hFx₀
    linarith
  have hxb : x₀ ≠ b := by
    rintro rfl
    rw [hFb] at hFx₀
    linarith
  have hmem : x₀ ∈ Ioo a b := ⟨lt_of_le_of_ne hx₀.1 (Ne.symm hxa), lt_of_le_of_ne hx₀.2 hxb⟩
  have hq : quant ρ n j = x₀ := QS_sSup h hmem hFx₀
  rw [hq]
  exact ⟨hmem, hFx₀⟩

/-- The quantiles `γ_q ≤ γ_p` for `p ≤ q` enclose the mass `(q - p)/n`. -/
private lemma QS_gap {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) {n p q : ℕ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hq : q ≤ n) :
    quant ρ n q ≤ quant ρ n p ∧
      ∫ t in quant ρ n q..quant ρ n p, ρ t = ((q : ℝ) - p) / n := by
  rcases hpq.eq_or_lt with rfl | hlt
  · simp
  obtain ⟨-, hFp⟩ := QS_quant_spec h hp (hpq.trans hq)
  obtain ⟨-, hFq⟩ := QS_quant_spec h (hp.trans hpq) hq
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) < q := by exact_mod_cast hlt
  have hq' : (q : ℝ) ≤ n := by exact_mod_cast hq
  have hn : (0 : ℝ) < n := by linarith
  have hle : quant ρ n q ≤ quant ρ n p := by
    by_contra hcon
    have h1 := QS_F_anti h (le_of_lt (lt_of_not_ge hcon))
    rw [hFp, hFq] at h1
    have h2 := (div_le_div_iff_of_pos_right hn).1 h1
    linarith
  refine ⟨hle, ?_⟩
  have hz : ∀ t, b < t → ρ t = 0 := fun t ht => h.zero_right ht
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (h.cont.intervalIntegrable (μ := MeasureTheory.volume) (quant ρ n q) (quant ρ n p))
    (h.cont.intervalIntegrable (μ := MeasureTheory.volume) (quant ρ n p) b)
  have e2 := QS_F_eq h.integ hz (quant ρ n q)
  have e3 := QS_F_eq h.integ hz (quant ρ n p)
  rw [hFq] at e2
  rw [hFp] at e3
  have : ∫ t in quant ρ n q..quant ρ n p, ρ t = ((q : ℝ) - 1 / 2) / n - ((p : ℝ) - 1 / 2) / n := by
    linarith
  rw [this]
  ring

/-- A lower bound of `ρ` on `[γ_q, γ_p]` bounds the gap `γ_p - γ_q` from above. -/
private lemma QS_bound_lo {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) {n p q : ℕ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hq : q ≤ n) {L : ℝ}
    (hL : ∀ t ∈ Icc (quant ρ n q) (quant ρ n p), L ≤ ρ t) :
    L * (quant ρ n p - quant ρ n q) ≤ ((q : ℝ) - p) / n := by
  obtain ⟨hle, hint⟩ := QS_gap h hp hpq hq
  have hi : IntervalIntegrable ρ MeasureTheory.volume (quant ρ n q) (quant ρ n p) :=
    h.cont.intervalIntegrable _ _
  have c1 : IntervalIntegrable (fun _ : ℝ => L) MeasureTheory.volume (quant ρ n q)
      (quant ρ n p) := intervalIntegrable_const
  have h1 := intervalIntegral.integral_mono_on hle c1 hi hL
  rw [intervalIntegral.integral_const, smul_eq_mul, hint] at h1
  linarith

/-- An upper bound of `ρ` on `[γ_q, γ_p]` bounds the gap `γ_p - γ_q` from below. -/
private lemma QS_bound_hi {ρ : ℝ → ℝ} {a b : ℝ} (h : QS_Dens ρ a b) {n p q : ℕ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hq : q ≤ n) {U : ℝ}
    (hU : ∀ t ∈ Icc (quant ρ n q) (quant ρ n p), ρ t ≤ U) :
    ((q : ℝ) - p) / n ≤ U * (quant ρ n p - quant ρ n q) := by
  obtain ⟨hle, hint⟩ := QS_gap h hp hpq hq
  have hi : IntervalIntegrable ρ MeasureTheory.volume (quant ρ n q) (quant ρ n p) :=
    h.cont.intervalIntegrable _ _
  have c2 : IntervalIntegrable (fun _ : ℝ => U) MeasureTheory.volume (quant ρ n q)
      (quant ρ n p) := intervalIntegrable_const
  have h2 := intervalIntegral.integral_mono_on hle hi c2 hU
  rw [intervalIntegral.integral_const, smul_eq_mul, hint] at h2
  linarith

end QSTail

section QSCube

/-- The cube root `x^{1/3}`. -/
private def QS_g (x : ℝ) : ℝ := x ^ (1 / 3 : ℝ)

private lemma QS_g_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ QS_g x := Real.rpow_nonneg hx _

private lemma QS_g_pos {x : ℝ} (hx : 0 < x) : 0 < QS_g x := Real.rpow_pos_of_pos hx _

private lemma QS_g_cube {x : ℝ} (hx : 0 ≤ x) : QS_g x ^ 3 = x := by
  unfold QS_g
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma QS_g_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    QS_g (x * y) = QS_g x * QS_g y :=
  Real.mul_rpow hx hy

private lemma QS_g_le_of_cube {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ 3) :
    QS_g x ≤ y :=
  (pow_le_pow_iff_left₀ (QS_g_nonneg hx) hy (n := 3) (by norm_num)).1
    (by rw [QS_g_cube hx]; exact h)

private lemma QS_g_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : QS_g x ≤ QS_g y :=
  Real.rpow_le_rpow hx hxy (by norm_num)

private lemma QS_rpow23 {x : ℝ} (hx : 0 ≤ x) : x ^ (2 / 3 : ℝ) = QS_g x ^ 2 := by
  unfold QS_g
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma QS_neg23 {N : ℝ} (hN : 0 ≤ N) : N ^ (-(2 / 3 : ℝ)) = (QS_g N ^ 2)⁻¹ := by
  rw [Real.rpow_neg hN, QS_rpow23 hN]

private lemma QS_neg13 {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 3 : ℝ)) = (QS_g x)⁻¹ :=
  Real.rpow_neg hx _

private lemma QS_kap_form {x N : ℝ} (hx : 0 ≤ x) (hN : 0 ≤ N) :
    x ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ)) = (QS_g x / QS_g N) ^ 2 := by
  rw [QS_rpow23 hx, QS_neg23 hN, div_pow, div_eq_mul_inv]

private lemma QS_sqrt_le {u v K X Y : ℝ} (hv0 : 0 ≤ v) (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hu : u ≤ K * X ^ 2) (hv : v ≤ K * Y ^ 2) :
    Real.sqrt (u * v) ≤ K * (X * Y) := by
  rw [Real.sqrt_le_left (by positivity)]
  calc u * v ≤ (K * X ^ 2) * (K * Y ^ 2) := mul_le_mul hu hv hv0 (by positivity)
    _ = (K * (X * Y)) ^ 2 := by ring

private lemma QS_le_sqrt {u v k X Y : ℝ} (hk : 0 ≤ k) (hu : k * X ^ 2 ≤ u)
    (hv : k * Y ^ 2 ≤ v) : k * (X * Y) ≤ Real.sqrt (u * v) := by
  apply Real.le_sqrt_of_sq_le
  calc (k * (X * Y)) ^ 2 = (k * X ^ 2) * (k * Y ^ 2) := by ring
    _ ≤ u * v := mul_le_mul hu hv (by positivity) (le_trans (by positivity) hu)

end QSCube

section QSData

open Set

/-- The inputs on `ρ_N` for `Λ = lam D N A`: the density `ρ`, its square-root behaviour (A.1)
[square_root_density] on `[a, b] = [E⁻, E⁺]`, and the quantile positions (2.21)
[eq:kappa_gamma_k]. -/
private structure QS_Data (D N : ℕ) (c₂ C₂ C₁ : ℝ) (ρ : ℝ → ℝ) (a b : ℝ) : Prop where
  dens : QS_Dens ρ a b
  sqlo : ∀ x ∈ Icc a b, C₁⁻¹ * Real.sqrt ((b - x) * (x - a)) ≤ ρ x
  sqhi : ∀ x ∈ Icc a b, ρ x ≤ C₁ * Real.sqrt ((b - x) * (x - a))
  ul : ∀ j : ℕ, 1 ≤ j → j ≤ D * N →
    c₂ * ((j : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ b - quant ρ (D * N) j
  uu : ∀ j : ℕ, 1 ≤ j → j ≤ D * N →
    b - quant ρ (D * N) j ≤ C₂ * ((j : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)))
  vl : ∀ j : ℕ, 1 ≤ j → j ≤ D * N →
    c₂ * ((j : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      quant ρ (D * N) (D * N + 1 - j) - a
  vu : ∀ j : ℕ, 1 ≤ j → j ≤ D * N →
    quant ρ (D * N) (D * N + 1 - j) - a ≤
      C₂ * ((j : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)))

private lemma QS_kap_forms {D N : ℕ} {c₂ C₂ C₁ : ℝ} {ρ : ℝ → ℝ} {a b : ℝ}
    (hd : QS_Data D N c₂ C₂ C₁ ρ a b) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ D * N) :
    c₂ * (QS_g j / QS_g N) ^ 2 ≤ b - quant ρ (D * N) j ∧
      b - quant ρ (D * N) j ≤ C₂ * (QS_g j / QS_g N) ^ 2 ∧
      c₂ * (QS_g j / QS_g N) ^ 2 ≤ quant ρ (D * N) (D * N + 1 - j) - a ∧
      quant ρ (D * N) (D * N + 1 - j) - a ≤ C₂ * (QS_g j / QS_g N) ^ 2 := by
  have e := QS_kap_form (Nat.cast_nonneg j) (Nat.cast_nonneg N)
  have h1 := hd.ul j hj hjn
  have h2 := hd.uu j hj hjn
  have h3 := hd.vl j hj hjn
  have h4 := hd.vu j hj hjn
  rw [e] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The bounds of `ρ_N` on `[γ_q, γ_p]`, `1 ≤ p ≤ q ≤ DN`, from the square-root behaviour and the
positions of the two quantiles. -/
private lemma QS_rho_bounds {D N : ℕ} {c₂ C₂ C₁ : ℝ} {ρ : ℝ → ℝ} {a b : ℝ}
    (hd : QS_Data D N c₂ C₂ C₁ ρ a b) (hC₂ : 0 < C₂) (hC₁ : 0 < C₁) (hc₂ : 0 < c₂)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ D * N)
    {t : ℝ} (ht : t ∈ Icc (quant ρ (D * N) q) (quant ρ (D * N) p)) :
    ρ t ≤ C₁ * (C₂ * ((QS_g q / QS_g N) * (QS_g ((D * N + 1 - p : ℕ) : ℝ) / QS_g N))) ∧
      C₁⁻¹ * (c₂ * ((QS_g p / QS_g N) * (QS_g ((D * N + 1 - q : ℕ) : ℝ) / QS_g N))) ≤ ρ t := by
  obtain ⟨hmp, -⟩ := QS_quant_spec hd.dens hp (hpq.trans hq)
  obtain ⟨hmq, -⟩ := QS_quant_spec hd.dens (hp.trans hpq) hq
  have hq1 : 1 ≤ q := hp.trans hpq
  have hmem : t ∈ Icc a b := ⟨by linarith [hmq.1, ht.1], by linarith [hmp.2, ht.2]⟩
  have hnp : 1 ≤ D * N + 1 - p := by
    have : p ≤ D * N := hpq.trans hq
    omega
  have hnpn : D * N + 1 - p ≤ D * N := by omega
  have hnq : 1 ≤ D * N + 1 - q := by omega
  have hnqn : D * N + 1 - q ≤ D * N := by omega
  obtain ⟨-, huq, -, -⟩ := QS_kap_forms hd hq1 hq
  obtain ⟨hup, -, -, -⟩ := QS_kap_forms hd hp (hpq.trans hq)
  obtain ⟨-, -, -, hvp⟩ := QS_kap_forms hd hnp hnpn
  obtain ⟨-, -, hvq, -⟩ := QS_kap_forms hd hnq hnqn
  rw [show D * N + 1 - (D * N + 1 - p) = p by omega] at hvp
  rw [show D * N + 1 - (D * N + 1 - q) = q by omega] at hvq
  have hgN : 0 ≤ QS_g N := QS_g_nonneg (Nat.cast_nonneg N)
  constructor
  · have h1 := QS_sqrt_le (u := b - t) (v := t - a) (K := C₂)
      (X := QS_g q / QS_g N) (Y := QS_g ((D * N + 1 - p : ℕ) : ℝ) / QS_g N)
      (by linarith [hmq.1, ht.1]) hC₂.le
      (div_nonneg (QS_g_nonneg (Nat.cast_nonneg q)) hgN)
      (div_nonneg (QS_g_nonneg (Nat.cast_nonneg _)) hgN)
      (by linarith [ht.1]) (by linarith [ht.2])
    exact (hd.sqhi t hmem).trans (mul_le_mul_of_nonneg_left h1 hC₁.le)
  · have h1 := QS_le_sqrt (u := b - t) (v := t - a) (k := c₂)
      (X := QS_g p / QS_g N) (Y := QS_g ((D * N + 1 - q : ℕ) : ℝ) / QS_g N) hc₂.le
      (by linarith [ht.2]) (by linarith [ht.1])
    exact (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hC₁.le)).trans (hd.sqlo t hmem)

end QSData

section QSArith

/-- The two cases of `𝔯(k)` (1.4) [eq:rk]: the right or the left half of the index range. -/
private lemma QS_rk_cases (D N k : ℕ) (hk : k ≤ D * N) :
    (rk D N k = k ∧ 2 * (k : ℝ) ≤ (D : ℝ) * N + 1) ∨
      (rk D N k = (D : ℝ) * N + 1 - k ∧ (D : ℝ) * N + 1 < 2 * k) := by
  unfold rk
  by_cases h : k ≤ D * N + 1 - k
  · left
    rw [min_eq_left h]
    refine ⟨rfl, ?_⟩
    have : 2 * k ≤ D * N + 1 := by omega
    exact_mod_cast this
  · right
    have h' : D * N + 1 - k < k := lt_of_not_ge h
    rw [min_eq_right h'.le]
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_sub (by omega : k ≤ D * N + 1)]
      push_cast
      ring
    · have : D * N + 1 < 2 * k := by omega
      exact_mod_cast this

private lemma QS_rk_ge_one (D N k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N) : 1 ≤ rk D N k := by
  unfold rk
  have : 1 ≤ min k (D * N + 1 - k) := by omega
  exact_mod_cast this

private lemma QS_cast_sub (n p : ℕ) (h : p ≤ n + 1) :
    ((n + 1 - p : ℕ) : ℝ) = (n : ℝ) + 1 - p := by
  rw [Nat.cast_sub h]
  push_cast
  ring

private lemma QS_arith_hi {n k p q m r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqn : q ≤ n)
    (hkp : k - m ≤ p) (hkq : q ≤ k + m) (hr : r = k ∨ r = n + 1 - k) :
    q * (n + 1 - p) ≤ n * (r + m) := by
  rcases hr with rfl | rfl
  · calc q * (n + 1 - p) ≤ (r + m) * n :=
          mul_le_mul hkq (by linarith) (by linarith) (by linarith)
      _ = n * (r + m) := by ring
  · exact mul_le_mul hqn (by linarith) (by linarith) (by linarith)

private lemma QS_arith_lo {n k p q m r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqn : q ≤ n)
    (hkp : k - m ≤ p) (hkq : q ≤ k + m) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hr : (r = k ∧ 2 * k ≤ n + 1) ∨ (r = n + 1 - k ∧ n + 1 < 2 * k)) (h2m : 2 * m ≤ r) :
    r * n ≤ 8 * (p * (n + 1 - q)) := by
  rcases hr with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · have e1 : r / 2 ≤ p := by linarith
    have e2 : (n + 1) / 4 ≤ n + 1 - q := by linarith
    have e3 := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · have e1 : (n + 1) / 4 ≤ p := by linarith
    have e2 : (n + 1 - k) / 2 ≤ n + 1 - q := by linarith
    have e3 := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith

end QSArith

section QSCore

open Set

private lemma QS_alg_lower {D' N' gD gN s C₁ C₂ d Δ : ℝ} (hgN : 0 < gN) (hgD : 0 < gD)
    (hs : 0 < s) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hN3 : N' = gN ^ 3) (hD3 : D' = gD ^ 3)
    (hb : d / (D' * N') ≤ C₁ * (C₂ * (gD * s / gN)) * Δ) :
    1 / (D' * gD * C₁ * C₂) * d * ((gN ^ 2)⁻¹ * s⁻¹) ≤ Δ := by
  subst hN3 hD3
  have hpos : 0 < gD ^ 3 * gN ^ 3 := by positivity
  rw [div_le_iff₀ hpos] at hb
  have e : 1 / (gD ^ 3 * gD * C₁ * C₂) * d * ((gN ^ 2)⁻¹ * s⁻¹) =
      d / ((gD ^ 3 * gD * C₁ * C₂) * (gN ^ 2 * s)) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have : C₁ * (C₂ * (gD * s / gN)) * Δ * (gD ^ 3 * gN ^ 3) =
      (gD ^ 3 * gD * C₁ * C₂) * (gN ^ 2 * s) * Δ := by
    field_simp
  linarith

private lemma QS_alg_upper_A {D' N' gD gN g' C₁ c₂ d m Δ : ℝ} (hgN : 0 < gN) (hgD : 0 < gD)
    (hg' : 0 < g') (hC₁ : 0 < C₁) (hc₂ : 0 < c₂) (hN3 : N' = gN ^ 3) (hD3 : D' = gD ^ 3)
    (hb : C₁⁻¹ * (c₂ * (gD * g' / (2 * gN))) * Δ ≤ d / (D' * N')) (hdm : d ≤ m) :
    Δ ≤ 2 * C₁ / (c₂ * D' * gD) * m * ((gN ^ 2)⁻¹ * g'⁻¹) := by
  subst hN3 hD3
  have hpos : 0 < gD ^ 3 * gN ^ 3 := by positivity
  rw [le_div_iff₀ hpos] at hb
  have e1 : C₁⁻¹ * (c₂ * (gD * g' / (2 * gN))) * Δ * (gD ^ 3 * gN ^ 3) =
      (c₂ * gD ^ 3 * gD * gN ^ 2 * g' * Δ) / (2 * C₁) := by
    field_simp
  rw [e1, div_le_iff₀ (by positivity)] at hb
  have e2 : 2 * C₁ / (c₂ * gD ^ 3 * gD) * m * ((gN ^ 2)⁻¹ * g'⁻¹) =
      (2 * C₁ * m) / (c₂ * gD ^ 3 * gD * gN ^ 2 * g') := by
    field_simp
  rw [e2, le_div_iff₀ (by positivity)]
  nlinarith

private lemma QS_alg_upper_B {gN gr μ m C₂ Δ g3 : ℝ} (hgN : 0 < gN) (hgr : 0 < gr)
    (hμ : 0 < μ) (hC₂ : 0 < C₂) (hm3 : m = μ ^ 3) (hgr2 : gr ≤ 2 * μ) (hg3 : g3 ≤ 2 * μ)
    (hg30 : 0 ≤ g3) (hΔ : Δ ≤ C₂ * (g3 / gN) ^ 2) :
    Δ ≤ 8 * C₂ * m * ((gN ^ 2)⁻¹ * gr⁻¹) := by
  have h1 : (g3 / gN) ^ 2 ≤ 4 * μ ^ 2 / gN ^ 2 := by
    rw [div_pow]
    gcongr
    nlinarith
  have h2 : μ ^ 2 / 2 ≤ m * gr⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hgr, hm3]
    nlinarith [sq_nonneg μ, mul_pos hμ hμ]
  calc Δ ≤ C₂ * (g3 / gN) ^ 2 := hΔ
    _ ≤ C₂ * (4 * μ ^ 2 / gN ^ 2) := by gcongr
    _ = 8 * C₂ * ((gN ^ 2)⁻¹ * (μ ^ 2 / 2)) := by field_simp; ring
    _ ≤ 8 * C₂ * ((gN ^ 2)⁻¹ * (m * gr⁻¹)) := by gcongr
    _ = 8 * C₂ * m * ((gN ^ 2)⁻¹ * gr⁻¹) := by ring

/-- The lower bound of the spacing `γ_p - γ_q ≥ c (q - p) N^{-2/3} (𝔯(k) + m)^{-1/3}` for
`1 ≤ p ≤ q ≤ DN`, `k ∈ {p, q}`, `q - p ≤ m`. -/
private lemma QS_core_lower {D N : ℕ} {c₂ C₂ C₁ : ℝ} {ρ : ℝ → ℝ} {a b : ℝ}
    (hd : QS_Data D N c₂ C₂ C₁ ρ a b) (hc₂ : 0 < c₂) (hC₂ : 0 < C₂) (hC₁ : 0 < C₁)
    (hD : 1 ≤ D) (hN : 1 ≤ N) {m : ℝ} (hm : 1 ≤ m) {p q k : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ D * N) (hk1 : 1 ≤ k) (hk2 : k ≤ D * N)
    (hk : k = p ∨ k = q) (hqp : (q : ℝ) - p ≤ m) :
    (1 / ((D : ℝ) * QS_g D * C₁ * C₂)) * ((q : ℝ) - p) *
        ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (rk D N k + m) ^ (-(1 / 3 : ℝ))) ≤
      quant ρ (D * N) p - quant ρ (D * N) q := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.2 (by omega)
  have hgN : 0 < QS_g (N : ℝ) := QS_g_pos hNpos
  have hgD : 0 < QS_g (D : ℝ) := QS_g_pos hDpos
  have hN3 : (N : ℝ) = QS_g (N : ℝ) ^ 3 := (QS_g_cube hNpos.le).symm
  have hD3 : (D : ℝ) = QS_g (D : ℝ) ^ 3 := (QS_g_cube hDpos.le).symm
  have hr1 := QS_rk_ge_one D N k hk1 hk2
  have hrm : 0 < rk D N k + m := by linarith
  have hs : 0 < QS_g (rk D N k + m) := QS_g_pos hrm
  have hs3 : QS_g (rk D N k + m) ^ 3 = rk D N k + m := QS_g_cube hrm.le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hqR : (q : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hq
  have hkR : (k : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hk2
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpq : ((k : ℝ) - m ≤ p) ∧ ((q : ℝ) ≤ k + m) := by
    rcases hk with rfl | rfl
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hrc : rk D N k = k ∨ rk D N k = (D : ℝ) * N + 1 - k := by
    rcases QS_rk_cases D N k hk2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hprod := QS_arith_hi hpR hpqR hqR hkpq.1 hkpq.2 hrc
  have hn1p : ((D * N + 1 - p : ℕ) : ℝ) = (D : ℝ) * N + 1 - p := by
    have := QS_cast_sub (D * N) p (by omega)
    push_cast at this
    exact this
  -- the upper bound of `ρ_N` on `[γ_q, γ_p]`
  have hU : ∀ t ∈ Icc (quant ρ (D * N) q) (quant ρ (D * N) p),
      ρ t ≤ C₁ * (C₂ * (QS_g (D : ℝ) * QS_g (rk D N k + m) / QS_g (N : ℝ))) := by
    intro t ht
    have h1 := (QS_rho_bounds hd hC₂ hC₁ hc₂ hp hpq hq ht).1
    refine h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC₂.le) hC₁.le)
    have hy0 : (0 : ℝ) ≤ ((D * N + 1 - p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hg : QS_g (q : ℝ) * QS_g ((D * N + 1 - p : ℕ) : ℝ) ≤
        QS_g (D : ℝ) * QS_g (N : ℝ) * QS_g (rk D N k + m) := by
      rw [← QS_g_mul hq0 hy0]
      apply QS_g_le_of_cube (mul_nonneg hq0 hy0) (by positivity)
      calc (q : ℝ) * ((D * N + 1 - p : ℕ) : ℝ) ≤ (D : ℝ) * N * (rk D N k + m) := by
            rw [hn1p]; exact hprod
        _ = (QS_g (D : ℝ) * QS_g (N : ℝ) * QS_g (rk D N k + m)) ^ 3 := by
            rw [mul_pow, mul_pow, hs3, ← hN3, ← hD3]
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hgN]
    nlinarith
  have hb := QS_bound_hi hd.dens hp hpq hq hU
  rw [QS_neg23 hNpos.le, QS_neg13 hrm.le]
  have hb' : ((q : ℝ) - p) / ((D : ℝ) * N) ≤
      C₁ * (C₂ * (QS_g (D : ℝ) * QS_g (rk D N k + m) / QS_g (N : ℝ))) *
        (quant ρ (D * N) p - quant ρ (D * N) q) := by
    have := hb
    push_cast at this
    exact this
  exact QS_alg_lower hgN hgD hs hC₁ hC₂ hN3 hD3 hb'

/-- The upper bound of the spacing `γ_p - γ_q ≤ C m N^{-2/3} 𝔯(k)^{-1/3}` for `1 ≤ p ≤ q ≤ DN`,
`k ∈ {p, q}`, `q - p ≤ m`. -/
private lemma QS_core_upper {D N : ℕ} {c₂ C₂ C₁ : ℝ} {ρ : ℝ → ℝ} {a b : ℝ}
    (hd : QS_Data D N c₂ C₂ C₁ ρ a b) (hc₂ : 0 < c₂) (hC₂ : 0 < C₂) (hC₁ : 0 < C₁)
    (hD : 1 ≤ D) (hN : 1 ≤ N) {m : ℝ} (hm : 1 ≤ m) {p q k : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ D * N) (hk1 : 1 ≤ k) (hk2 : k ≤ D * N)
    (hk : k = p ∨ k = q) (hqp : (q : ℝ) - p ≤ m) :
    quant ρ (D * N) p - quant ρ (D * N) q ≤
      max (2 * C₁ / (c₂ * D * QS_g D)) (8 * C₂) * m *
        ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.2 (by omega)
  have hgN : 0 < QS_g (N : ℝ) := QS_g_pos hNpos
  have hgD : 0 < QS_g (D : ℝ) := QS_g_pos hDpos
  have hN3 : (N : ℝ) = QS_g (N : ℝ) ^ 3 := (QS_g_cube hNpos.le).symm
  have hD3 : (D : ℝ) = QS_g (D : ℝ) ^ 3 := (QS_g_cube hDpos.le).symm
  have hr1 := QS_rk_ge_one D N k hk1 hk2
  have hr0 : 0 < rk D N k := by linarith
  have hgr : 0 < QS_g (rk D N k) := QS_g_pos hr0
  have hgr3 : QS_g (rk D N k) ^ 3 = rk D N k := QS_g_cube hr0.le
  have hm0 : 0 < m := by linarith
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hqR : (q : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hq
  have hkR : (k : ℝ) ≤ (D : ℝ) * N := by exact_mod_cast hk2
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpq : ((k : ℝ) - m ≤ p) ∧ ((q : ℝ) ≤ k + m) := by
    rcases hk with rfl | rfl
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hn1p : ((D * N + 1 - p : ℕ) : ℝ) = (D : ℝ) * N + 1 - p := by
    have := QS_cast_sub (D * N) p (by omega)
    push_cast at this
    exact this
  have hn1q : ((D * N + 1 - q : ℕ) : ℝ) = (D : ℝ) * N + 1 - q := by
    have := QS_cast_sub (D * N) q (by omega)
    push_cast at this
    exact this
  rw [QS_neg23 hNpos.le, QS_neg13 hr0.le]
  have hX : 0 ≤ (QS_g (N : ℝ) ^ 2)⁻¹ * (QS_g (rk D N k))⁻¹ := by positivity
  by_cases h2m : 2 * m ≤ rk D N k
  · -- `𝔯(k) ≥ 2m`: `ρ_N ≳ (𝔯(k)/N)^{1/3}` on the interval
    have hlo := QS_arith_lo hpR hpqR hqR hkpq.1 hkpq.2 hk1R hkR (QS_rk_cases D N k hk2) h2m
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hy0 : (0 : ℝ) ≤ ((D * N + 1 - q : ℕ) : ℝ) := Nat.cast_nonneg _
    have hy : QS_g (D : ℝ) * QS_g (rk D N k) * QS_g (N : ℝ) ≤
        2 * (QS_g (p : ℝ) * QS_g ((D * N + 1 - q : ℕ) : ℝ)) := by
      have h3 : (QS_g (D : ℝ) * QS_g (rk D N k) * QS_g (N : ℝ)) ^ 3 ≤
          (2 * (QS_g (p : ℝ) * QS_g ((D * N + 1 - q : ℕ) : ℝ))) ^ 3 := by
        have e1 : (QS_g (D : ℝ) * QS_g (rk D N k) * QS_g (N : ℝ)) ^ 3 =
            rk D N k * ((D : ℝ) * N) := by
          rw [mul_pow, mul_pow, hgr3, ← hN3, ← hD3]; ring
        have e2 : (2 * (QS_g (p : ℝ) * QS_g ((D * N + 1 - q : ℕ) : ℝ))) ^ 3 =
            8 * ((p : ℝ) * ((D : ℝ) * N + 1 - q)) := by
          rw [mul_pow, mul_pow, QS_g_cube hp0, QS_g_cube hy0, hn1q]; ring
        rw [e1, e2]
        exact hlo
      exact (pow_le_pow_iff_left₀ (by positivity)
        (mul_nonneg (by norm_num) (mul_nonneg (QS_g_nonneg hp0) (QS_g_nonneg hy0)))
        (n := 3) (by norm_num)).1 h3
    have hL : ∀ t ∈ Icc (quant ρ (D * N) q) (quant ρ (D * N) p),
        C₁⁻¹ * (c₂ * (QS_g (D : ℝ) * QS_g (rk D N k) / (2 * QS_g (N : ℝ)))) ≤ ρ t := by
      intro t ht
      refine le_trans ?_ (QS_rho_bounds hd hC₂ hC₁ hc₂ hp hpq hq ht).2
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hc₂.le)
        (inv_nonneg.2 hC₁.le)
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hgN]
    have hb := QS_bound_lo hd.dens hp hpq hq hL
    have hb' : C₁⁻¹ * (c₂ * (QS_g (D : ℝ) * QS_g (rk D N k) / (2 * QS_g (N : ℝ)))) *
        (quant ρ (D * N) p - quant ρ (D * N) q) ≤ ((q : ℝ) - p) / ((D : ℝ) * N) := by
      have := hb
      push_cast at this
      exact this
    have hA := QS_alg_upper_A hgN hgD hgr hC₁ hc₂ hN3 hD3 hb' hqp
    exact hA.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0.le) hX)
  · -- `𝔯(k) < 2m`: both quantiles are within `C (3m/N)^{2/3}` of the same edge
    have h2m := not_le.1 h2m
    have hmp := (QS_quant_spec hd.dens hp (hpq.trans hq)).1
    have hmq := (QS_quant_spec hd.dens (hp.trans hpq) hq).1
    have hq1 : 1 ≤ q := hp.trans hpq
    have hΔ : quant ρ (D * N) p - quant ρ (D * N) q ≤ C₂ * (QS_g (3 * m) / QS_g (N : ℝ)) ^ 2 := by
      rcases QS_rk_cases D N k hk2 with ⟨hr, h1⟩ | ⟨hr, h1⟩
      · have hq3 : (q : ℝ) ≤ 3 * m := by linarith [hkpq.2]
        have huq := (QS_kap_forms hd hq1 hq).2.1
        have hg : QS_g (q : ℝ) ≤ QS_g (3 * m) := QS_g_mono (Nat.cast_nonneg q) hq3
        have hg2 : C₂ * (QS_g (q : ℝ) / QS_g (N : ℝ)) ^ 2 ≤
            C₂ * (QS_g (3 * m) / QS_g (N : ℝ)) ^ 2 := by
          have := QS_g_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
          gcongr
        linarith [hmp.2]
      · have hnp : 1 ≤ D * N + 1 - p := by
          have : p ≤ D * N := hpq.trans hq
          omega
        have hnpn : D * N + 1 - p ≤ D * N := by omega
        have hvp := (QS_kap_forms hd hnp hnpn).2.2.2
        rw [show D * N + 1 - (D * N + 1 - p) = p by omega] at hvp
        have hq3 : ((D * N + 1 - p : ℕ) : ℝ) ≤ 3 * m := by
          rw [hn1p]; linarith [hkpq.1]
        have hg : QS_g ((D * N + 1 - p : ℕ) : ℝ) ≤ QS_g (3 * m) :=
          QS_g_mono (Nat.cast_nonneg _) hq3
        have hg2 : C₂ * (QS_g ((D * N + 1 - p : ℕ) : ℝ) / QS_g (N : ℝ)) ^ 2 ≤
            C₂ * (QS_g (3 * m) / QS_g (N : ℝ)) ^ 2 := by
          have := QS_g_nonneg
            (Nat.cast_nonneg (D * N + 1 - p) : (0 : ℝ) ≤ ((D * N + 1 - p : ℕ) : ℝ))
          gcongr
        linarith [hmq.1]
    have hμ : 0 < QS_g m := QS_g_pos hm0
    have hμ3 : QS_g m ^ 3 = m := QS_g_cube hm0.le
    have hg3 : QS_g (3 * m) ≤ 2 * QS_g m :=
      QS_g_le_of_cube (by positivity) (by positivity) (by rw [mul_pow, hμ3]; nlinarith)
    have hgr2 : QS_g (rk D N k) ≤ 2 * QS_g m :=
      QS_g_le_of_cube hr0.le (by positivity) (by rw [mul_pow, hμ3]; nlinarith)
    have hB := QS_alg_upper_B hgN hgr hμ hC₂ hμ3.symm hgr2 hg3
      (QS_g_nonneg (by positivity)) hΔ
    exact hB.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hm0.le) hX)

end QSCore

section QSAssemble

open Set

/-- Both spacing bounds for the pair `(i, k)`, `|i - k| ≤ N^τ`, from the two cores. -/
private lemma QS_assemble {D N : ℕ} {c₂ C₂ C₁ : ℝ} {ρ : ℝ → ℝ} {a b : ℝ}
    (hd : QS_Data D N c₂ C₂ C₁ ρ a b) (hc₂ : 0 < c₂) (hC₂ : 0 < C₂) (hC₁ : 0 < C₁)
    (hD : 1 ≤ D) (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) {i k : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ D * N) (hk1 : 1 ≤ k) (hk2 : k ≤ D * N) (hik : |(i : ℝ) - k| ≤ (N : ℝ) ^ τ) :
    |quant ρ (D * N) i - quant ρ (D * N) k| ≤
        max (2 * C₁ / (c₂ * D * QS_g D)) (8 * C₂) * (N : ℝ) ^ τ *
          ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) ∧
      (1 / ((D : ℝ) * QS_g D * C₁ * C₂)) * |(i : ℝ) - k| *
        ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (rk D N k + (N : ℝ) ^ τ) ^ (-(1 / 3 : ℝ))) ≤
      |quant ρ (D * N) i - quant ρ (D * N) k| := by
  have hm : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hN) hτ
  rcases le_total i k with h | h
  · obtain ⟨hle, -⟩ := QS_gap hd.dens hi1 h hk2
    have hqp : (k : ℝ) - i ≤ (N : ℝ) ^ τ := by
      have : (i : ℝ) ≤ k := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hik
      exact hik
    have hik' : |(i : ℝ) - k| = (k : ℝ) - i := by
      have : (i : ℝ) ≤ k := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hik', abs_of_nonneg (by linarith)]
    exact ⟨QS_core_upper hd hc₂ hC₂ hC₁ hD hN hm hi1 h hk2 hk1 hk2 (Or.inr rfl) hqp,
      QS_core_lower hd hc₂ hC₂ hC₁ hD hN hm hi1 h hk2 hk1 hk2 (Or.inr rfl) hqp⟩
  · obtain ⟨hle, -⟩ := QS_gap hd.dens hk1 h hi2
    have hqp : (i : ℝ) - k ≤ (N : ℝ) ^ τ := by
      have : (k : ℝ) ≤ i := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)] at hik
      exact hik
    have hik' : |(i : ℝ) - k| = (i : ℝ) - k := by
      have : (k : ℝ) ≤ i := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
    rw [hik', abs_sub_comm, abs_of_nonneg (by linarith)]
    exact ⟨QS_core_upper hd hc₂ hC₂ hC₁ hD hN hm hk1 h hi2 hk1 hk2 (Or.inl rfl) hqp,
      QS_core_lower hd hc₂ hC₂ hC₁ hD hN hm hk1 h hi2 hk1 hk2 (Or.inl rfl) hqp⟩

end QSAssemble


/-- The spacing of the quantiles (2.20) [eq:gammak] of `ρ_N` near the index `k`, from the
square-root density (A.1) [square_root_density] and (2.21) [eq:kappa_gamma_k]: for `Λ = lam D N A`
with `‖A‖ ≤ N^{-δ_A}` and `|i - k| ≤ N^τ`, `|γ_i - γ_k| ≤ C N^τ N^{-2/3} 𝔯(k)^{-1/3}` and
`|γ_i - γ_k| ≥ c |i - k| N^{-2/3} (𝔯(k) + N^τ)^{-1/3}`; the constants depend on `D`, `δ_A` and
`τ` only. -/
theorem quant_spacing (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hτ1 : τ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ i k : ℕ, 1 ≤ i → i ≤ D * N → 1 ≤ k → k ≤ D * N → |(i : ℝ) - k| ≤ (N : ℝ) ^ τ →
        |quant (rho (lam D N A)) (D * N) i - quant (rho (lam D N A)) (D * N) k| ≤
            C * (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) ∧
          c * |(i : ℝ) - k| *
              ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (rk D N k + (N : ℝ) ^ τ) ^ (-(1 / 3 : ℝ))) ≤
            |quant (rho (lam D N A)) (D * N) i - quant (rho (lam D N A)) (D * N) k| := by
  have _ := hτ1
  obtain ⟨c₂, C₂, hc₂, hC₂, N₁, hk⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨C₁, hC₁, hsq⟩ := square_root_density 1 one_pos
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ (-δA) ≤ 1 / 20 :=
    ((tendsto_rpow_neg_atTop hδA).comp tendsto_natCast_atTop_atTop).eventually
      (ge_mem_nhds (by norm_num))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hev
  refine ⟨1 / ((D : ℝ) * QS_g D * C₁ * C₂),
    max (2 * C₁ / (c₂ * D * QS_g D)) (8 * C₂), ?_, ?_, max (max N₁ N₂) 1, ?_⟩
  · have hDpos : (0 : ℝ) < D := Nat.cast_pos.2 (by omega)
    have := QS_g_pos hDpos
    positivity
  · exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  intro N hN A hA i k hi1 hi2 hk1 hk2 hik
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛH := lam_isHermitian D N A
  have hΛn : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    have := hN₂ N hN₂'
    linarith
  obtain ⟨hnn, hcont, hint, htot, -⟩ := rho_stieltjes _ hΛH hΛn
  obtain ⟨hlt, hsupp⟩ := rho_support _ hΛH hΛn
  obtain ⟨hsq1, -⟩ := hsq (Idx D N) (lam D N A) hΛH hΛn
  have hd : QS_Data D N c₂ C₂ C₁ (rho (lam D N A)) (Eminus (lam D N A)) (Eplus (lam D N A)) :=
    { dens := ⟨hcont, hint, hnn, htot, hlt,
        fun t ht => by
          by_contra hne
          exact ht (hsupp ▸ Function.mem_support.2 hne),
        fun t ht => by
          have := hsupp ▸ ht
          exact lt_of_le_of_ne (hnn t) (Ne.symm (Function.mem_support.1 this))⟩
      sqlo := fun x hx => (hsq1 x hx).1
      sqhi := fun x hx => (hsq1 x hx).2
      ul := fun j hj1 hj2 => (hk N hN₁ A hA j hj1 hj2).1
      uu := fun j hj1 hj2 => (hk N hN₁ A hA j hj1 hj2).2.1
      vl := fun j hj1 hj2 => (hk N hN₁ A hA j hj1 hj2).2.2.1
      vu := fun j hj1 hj2 => (hk N hN₁ A hA j hj1 hj2).2.2.2 }
  exact QS_assemble hd hc₂ hC₂ hC₁ (by omega) hN1 hτ.le hi1 hi2 hk1 hk2 hik

/-- The spacing of the semicircle quantiles `γ^{sc}_i` with `DN` particles near the index `k`
(the case `A = 0` of `quant_spacing`, `ρ_N = ρ_sc` by Definition 2.7 [defn_Mm] at `Λ = 0`): for
`|i - k| ≤ N^τ`, `|γ^{sc}_i - γ^{sc}_k| ≤ C N^τ N^{-2/3} 𝔯(k)^{-1/3}` and
`|γ^{sc}_i - γ^{sc}_k| ≥ c |i - k| N^{-2/3} (𝔯(k) + N^τ)^{-1/3}`. -/
theorem quant_spacing_sc (D : ℕ) (hD : 2 ≤ D) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ i k : ℕ, 1 ≤ i → i ≤ D * N → 1 ≤ k → k ≤ D * N → |(i : ℝ) - k| ≤ (N : ℝ) ^ τ →
        |quant rhoSc (D * N) i - quant rhoSc (D * N) k| ≤
            C * (N : ℝ) ^ τ * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) ∧
          c * |(i : ℝ) - k| *
              ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (rk D N k + (N : ℝ) ^ τ) ^ (-(1 / 3 : ℝ))) ≤
            |quant rhoSc (D * N) i - quant rhoSc (D * N) k| := by
  obtain ⟨c, C, hc, hC, N₀, h⟩ := quant_spacing D hD 1 τ one_pos hτ hτ1
  refine ⟨c, C, hc, hC, max N₀ 1, ?_⟩
  intro N hN i k hi1 hi2 hk1 hk2 hik
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hA : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := by
    have : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by unfold opNorm; simp
    rw [this]
    positivity
  have hlam : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    ext p q
    simp [lam]
  have hrho : rho (0 : Matrix (Idx D N) (Idx D N) ℂ) = rhoSc := rho_zero.2.1
  have := h N hN0 0 hA i k hi1 hi2 hk1 hk2 hik
  rw [hlam, hrho] at this
  exact this

end RBMTransitionEdge

end
