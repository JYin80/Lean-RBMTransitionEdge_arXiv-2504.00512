module

public import RBMTransitionEdge.Localized.Expansion.IndexCS

@[expose] public section

/-!
# The label Cauchy–Schwarz of Lemma 5.5

The sum over all labels of a product of nonnegative factors of two labels, bounded by the mixed
norms of the factors with the order of `ℓ²` and sup fixed, as in (5.68) [bound_factors]–(5.71)
[Cauchy_example_2], Example 5.7 [example_estimate_reminder_reminder_terms] and the companion
cases of Lemma 5.5 [claim_estimate_remainder_terms].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The mixed norm of a nonnegative function of two labels summed in the order `first`, then
the other, with `ℓ²` or sup at each label: `ℓ²/ℓ²` is the Hilbert–Schmidt norm, `ℓ²` at the first
and sup at the second is `sup_y (Σ_x f²)^{1/2}` (a Ward norm), sup at the first and `ℓ²` at the
second is `(Σ_y (sup_x f)²)^{1/2}`. -/
def fcsNorm {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (m₁ m₂ : Bool) : ℝ :=
  match m₁, m₂ with
  | true, true => Real.sqrt (∑ x, ∑ y, f x y ^ 2)
  | true, false => ⨆ y, Real.sqrt (∑ x, f x y ^ 2)
  | false, true => Real.sqrt (∑ y, (⨆ x, f x y) ^ 2)
  | false, false => ⨆ x, ⨆ y, f x y

/-- A factor of the label sum: its labels `a, b` (`a = b`: a function of one label), its modes
at `a` and at `b` (`true`: `ℓ²`), and the function. -/
structure FCSFac (ι : Type*) (L : ℕ) where
  /-- The first label of the factor. -/
  a : Fin L
  /-- The second label of the factor (`b = a`: a function of one label). -/
  b : Fin L
  /-- The mode at the label `a`: `true` for `ℓ²`, `false` for sup. -/
  ma : Bool
  /-- The mode at the label `b`: `true` for `ℓ²`, `false` for sup. -/
  mb : Bool
  /-- The function of the two labels: `f x y` with `x` at `a` and `y` at `b`. -/
  f : ι → ι → ℝ

/-- The number of `ℓ²` uses of label `l` by a factor. -/
def FCSFac.use {ι : Type*} {L : ℕ} (g : FCSFac ι L) (l : Fin L) : ℕ :=
  if g.a = l ∧ g.b = l then (if g.ma then 1 else 0)
  else (if g.a = l ∧ g.ma then 1 else 0) + (if g.b = l ∧ g.mb then 1 else 0)

/-- The norm of a factor in the order of the labels (`Fin L`, the smaller label summed first). -/
def FCSFac.norm {ι : Type*} [Fintype ι] {L : ℕ} (g : FCSFac ι L) : ℝ :=
  if g.a = g.b then (if g.ma then Real.sqrt (∑ x, g.f x x ^ 2) else ⨆ x, g.f x x)
  else if g.a < g.b then fcsNorm g.f g.ma g.mb
  else fcsNorm (fun y x => g.f x y) g.mb g.ma

/-- The Cauchy–Schwarz of (5.70) [Cauchy_example_1] and (5.71) [Cauchy_example_2] over one label:
the sum of a product of `n ≤ 2` functions `W` of the label is at most `|ι|^{(2 - n)/2}` times the
product of their `ℓ²` norms. -/
private lemma labelcs_sum_weights {ι : Type*} [Fintype ι] (W : List (ι → ℝ))
    (n : ℕ) (hn : W.length = n) (h2 : n ≤ 2) :
    ∑ v, (W.map fun w => w v).prod ≤
      (Fintype.card ι : ℝ) ^ ((2 - (n : ℝ)) / 2) *
        (W.map fun w => Real.sqrt (∑ v, w v ^ 2)).prod := by
  subst hn
  match W, h2 with
  | [], _ =>
    simp
  | [w], _ =>
    have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) w
    have hcard : (Fintype.card ι : ℝ) ^ ((2 - ((List.length [w] : ℕ) : ℝ)) / 2) =
        Real.sqrt (Fintype.card ι) := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [hcard]
    simpa using this
  | [w₁, w₂], _ =>
    have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) w₁ w₂
    simpa using this
  | _ :: _ :: _ :: _, h2 => simp at h2

/-- The one-label step of (5.70) [Cauchy_example_1] and (5.71) [Cauchy_example_2]: the sum over
one label of a product of nonnegative functions of it, together with the weights `W` already in
`ℓ²`. Each factor `g` has `c g ≤ 1` uses of `ℓ²`, and `n` counts the uses and the weights, at most
two. A factor without a use is bounded by its supremum and one with a use is taken in `ℓ²`, which
gives `|ι|^{(2 - n)/2}` times the product of these values. -/
private lemma labelcs_claim {ι : Type*} [Fintype ι] {γ : Type*} (h : γ → ι → ℝ) (c : γ → ℕ) :
    ∀ (G : List γ) (W : List (ι → ℝ)) (n : ℕ), (∀ g ∈ G, ∀ v, 0 ≤ h g v) →
      (∀ g ∈ G, c g ≤ 1) → (∀ w ∈ W, ∀ v, 0 ≤ w v) → W.length + (G.map c).sum = n → n ≤ 2 →
      ∑ v, (W.map fun w => w v).prod * (G.map fun g => h g v).prod ≤
        (Fintype.card ι : ℝ) ^ ((2 - (n : ℝ)) / 2) *
          (W.map fun w => Real.sqrt (∑ v, w v ^ 2)).prod *
          (G.map fun g => if c g = 0 then ⨆ v, h g v else Real.sqrt (∑ v, h g v ^ 2)).prod := by
  intro G
  induction G with
  | nil =>
    intro W n _ _ _ hn h2
    simp only [List.map_nil, List.prod_nil, mul_one, List.sum_nil, add_zero] at hn ⊢
    exact labelcs_sum_weights W n hn h2
  | cons g G ih =>
    intro W n hnn hc1 hW hn h2
    have hnnG : ∀ g' ∈ G, ∀ v, 0 ≤ h g' v := fun g' hg' => hnn g' (List.mem_cons_of_mem _ hg')
    have hc1G : ∀ g' ∈ G, c g' ≤ 1 := fun g' hg' => hc1 g' (List.mem_cons_of_mem _ hg')
    have hgn : ∀ v, 0 ≤ h g v := hnn g List.mem_cons_self
    have hgc : c g ≤ 1 := hc1 g List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hn ⊢
    by_cases hc : c g = 0
    · simp only [hc, ↓reduceIte]
      rw [hc, zero_add] at hn
      have hS : 0 ≤ ⨆ v, h g v := Real.iSup_nonneg hgn
      have hGn : ∀ v, 0 ≤ (G.map fun g' => h g' v).prod := fun v =>
        List.prod_nonneg fun a ha => by
          obtain ⟨g', hg', rfl⟩ := List.mem_map.1 ha
          exact hnnG g' hg' v
      have hWn : ∀ v, 0 ≤ (W.map fun w => w v).prod := fun v =>
        List.prod_nonneg fun a ha => by
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
          exact hW w hw v
      have hih := ih W n hnnG hc1G hW hn h2
      calc ∑ v, (W.map fun w => w v).prod * (h g v * (G.map fun g' => h g' v).prod)
          ≤ ∑ v, (W.map fun w => w v).prod * ((⨆ v, h g v) * (G.map fun g' => h g' v).prod) :=
            Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (Finite.le_ciSup (fun v => h g v) v) (hGn v)) (hWn v)
        _ = (⨆ v, h g v) * ∑ v, (W.map fun w => w v).prod * (G.map fun g' => h g' v).prod := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun v _ => by ring
        _ ≤ (⨆ v, h g v) * ((Fintype.card ι : ℝ) ^ ((2 - (n : ℝ)) / 2) *
            (W.map fun w => Real.sqrt (∑ v, w v ^ 2)).prod *
            (G.map fun g' => if c g' = 0 then ⨆ v, h g' v else
              Real.sqrt (∑ v, h g' v ^ 2)).prod) :=
            mul_le_mul_of_nonneg_left hih hS
        _ = _ := by ring
    · simp only [hc, ↓reduceIte]
      have hc' : c g = 1 := by omega
      rw [hc'] at hn
      have hn' : (h g :: W).length + (G.map c).sum = n := by
        simp only [List.length_cons]; omega
      have hW' : ∀ w ∈ h g :: W, ∀ v, 0 ≤ w v := by
        intro w hw v
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hgn v
        · exact hW w hw v
      have hih := ih (h g :: W) n hnnG hc1G hW' hn' h2
      simp only [List.map_cons, List.prod_cons] at hih
      calc ∑ v, (W.map fun w => w v).prod * (h g v * (G.map fun g' => h g' v).prod)
          = ∑ v, (h g v * (W.map fun w => w v).prod) * (G.map fun g' => h g' v).prod :=
            Finset.sum_congr rfl fun v _ => by ring
        _ ≤ _ := hih
        _ = _ := by ring

/-- The mixed norms of a nonnegative function are nonnegative. -/
private lemma labelcs_fcsNorm_nonneg {ι : Type*} [Fintype ι] (f : ι → ι → ℝ)
    (hf : ∀ x y, 0 ≤ f x y) (m₁ m₂ : Bool) : 0 ≤ fcsNorm f m₁ m₂ := by
  cases m₁ <;> cases m₂ <;> simp only [fcsNorm]
  all_goals first
    | exact Real.sqrt_nonneg _
    | exact Real.iSup_nonneg fun y => Real.sqrt_nonneg _
    | exact Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => hf x y

/-- The norm of a nonnegative factor is nonnegative. -/
private lemma labelcs_norm_nonneg {ι : Type*} [Fintype ι] {L : ℕ} (g : FCSFac ι L)
    (hg : ∀ x y, 0 ≤ g.f x y) : 0 ≤ g.norm := by
  unfold FCSFac.norm
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact Real.iSup_nonneg fun x => hg x x
  · exact labelcs_fcsNorm_nonneg _ hg _ _
  · exact labelcs_fcsNorm_nonneg _ (fun x y => hg y x) _ _

/-- A label carries at most one `ℓ²` use per factor. -/
private lemma labelcs_use_le {ι : Type*} {L : ℕ} (g : FCSFac ι L) (l : Fin L) : g.use l ≤ 1 := by
  unfold FCSFac.use
  split_ifs <;> simp_all

/-- The reduction of a function of two labels over its first label: the `ℓ²` norm over it if `m`,
the supremum over it otherwise, as a function of the second label. -/
private def labelcs_redFn {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (m : Bool) (u : ι) : ℝ :=
  if m then Real.sqrt (∑ x, f x u ^ 2) else ⨆ x, f x u

/-- The norm of the reduced function in the mode of the second label is the mixed norm
`fcsNorm`: the order of sup and `ℓ²` of (5.68) [bound_factors]. -/
private lemma labelcs_norm_red {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ι → ℝ)
    (m₀ m₁ : Bool) :
    (if m₁ then Real.sqrt (∑ x, labelcs_redFn f m₀ x ^ 2) else ⨆ x, labelcs_redFn f m₀ x) =
      fcsNorm f m₀ m₁ := by
  cases m₀ <;> cases m₁ <;> simp only [labelcs_redFn, fcsNorm, ↓reduceIte, Bool.false_eq_true]
  · refine le_antisymm (ciSup_le fun x => ciSup_le fun x' => ?_)
      (ciSup_le fun x => ciSup_le fun y => ?_)
    · exact le_trans (Finite.le_ciSup (fun b => f x' b) x)
        (Finite.le_ciSup (fun a => ⨆ b, f a b) x')
    · exact le_trans (Finite.le_ciSup (fun x' => f x' y) x)
        (Finite.le_ciSup (fun u => ⨆ x', f x' u) y)
  · have h : ∀ x : ι, (Real.sqrt (∑ x', f x' x ^ 2)) ^ 2 = ∑ x', f x' x ^ 2 := fun x =>
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    simp only [h]
    rw [Finset.sum_comm]

/-- The factor `g` of the labels `Fin (L + 1)` after the label `0` is summed: a factor of the
labels `Fin L` (the label `l + 1` becomes `l`), or `none` if both labels of `g` are `0`. A factor
with one label `0` becomes a function of the other label, reduced over `0` in the mode of `0`. -/
private def labelcs_red {ι : Type*} [Fintype ι] {L : ℕ} (g : FCSFac ι (L + 1)) :
    Option (FCSFac ι L) :=
  Fin.cases (motive := fun _ => Option (FCSFac ι L))
    (Fin.cases (motive := fun _ => Option (FCSFac ι L)) none
      (fun b' => some ⟨b', b', g.mb, g.mb, fun u _ => labelcs_redFn g.f g.ma u⟩) g.b)
    (fun a' => Fin.cases (motive := fun _ => Option (FCSFac ι L))
      (some ⟨a', a', g.ma, g.ma, fun u _ => labelcs_redFn (fun v w => g.f w v) g.mb u⟩)
      (fun b' => some ⟨a', b', g.ma, g.mb, g.f⟩) g.b) g.a

/-- The value of the factor `g` when the label `0` carries `v` and the labels `l + 1` carry
`x' l`. -/
private def labelcs_val {ι : Type*} {L : ℕ} (g : FCSFac ι (L + 1)) (x' : Fin L → ι) (v : ι) : ℝ :=
  g.f ((Fin.cons v x' : Fin (L + 1) → ι) g.a) ((Fin.cons v x' : Fin (L + 1) → ι) g.b)

/-- The value of the factor `g` at `x'` after the label `0` is summed: the supremum over `v` if
`g` has no `ℓ²` use of `0`, the `ℓ²` norm over `v` if it has one. -/
private def labelcs_rv {ι : Type*} [Fintype ι] {L : ℕ} (g : FCSFac ι (L + 1)) (x' : Fin L → ι) :
    ℝ :=
  if g.use 0 = 0 then ⨆ v, labelcs_val g x' v else Real.sqrt (∑ v, labelcs_val g x' v ^ 2)

/-- The constant factor left by `g` after the label `0` is summed: its norm if both its labels
are `0`, and `1` otherwise. -/
private def labelcs_const {ι : Type*} [Fintype ι] {L : ℕ} (g : FCSFac ι (L + 1)) : ℝ :=
  match labelcs_red g with
  | none => g.norm
  | some _ => 1

/-- The reduction of one factor of `fcs_contract` after the label `0` is summed: if `labelcs_red g`
is a factor `g'`, it is nonnegative, has the norm of `g` (the order of sup and `ℓ²` of (5.68)
[bound_factors]), the `ℓ²` uses of `g` at the labels `l + 1`, and the value `labelcs_rv g x'`;
if there is none, `g` is a constant equal to its norm, with no use of a label `l + 1`. -/
private lemma labelcs_red_spec {ι : Type*} [Fintype ι] [Nonempty ι] {L : ℕ}
    (g : FCSFac ι (L + 1)) (hg : ∀ x y, 0 ≤ g.f x y) (x' : Fin L → ι) :
    match labelcs_red g with
    | none => g.norm = labelcs_rv g x' ∧ ∀ l : Fin L, g.use l.succ = 0
    | some g' => (∀ x y, 0 ≤ g'.f x y) ∧ g'.norm = g.norm ∧
        (∀ l : Fin L, g'.use l = g.use l.succ) ∧
        labelcs_rv g x' = g'.f (x' g'.a) (x' g'.b) := by
  obtain ⟨a, b, ma, mb, f⟩ := g
  simp only at hg
  have h0 : ∀ l : Fin L, (0 : Fin (L + 1)) ≠ l.succ := fun l => (Fin.succ_ne_zero l).symm
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero =>
      cases ma <;>
        simp [labelcs_red, labelcs_rv, labelcs_val, FCSFac.norm, FCSFac.use, h0]
    | succ b' =>
      simp only [labelcs_red, Fin.cases_zero, Fin.cases_succ]
      refine ⟨fun x y => ?_, ?_, fun l => ?_, ?_⟩
      · cases ma <;> simp only [labelcs_redFn]
        · exact Real.iSup_nonneg fun x => hg x _
        · exact Real.sqrt_nonneg _
      · simp only [FCSFac.norm, Fin.succ_pos, ↓reduceIte, h0]
        exact labelcs_norm_red f ma mb
      · by_cases h : b' = l <;> cases mb <;> simp [FCSFac.use, h0, h]
      · cases ma <;> simp [labelcs_rv, labelcs_val, FCSFac.use, labelcs_redFn]
  | succ a' =>
    induction b using Fin.cases with
    | zero =>
      simp only [labelcs_red, Fin.cases_zero, Fin.cases_succ]
      refine ⟨fun x y => ?_, ?_, fun l => ?_, ?_⟩
      · cases mb <;> simp only [labelcs_redFn]
        · exact Real.iSup_nonneg fun x => hg _ x
        · exact Real.sqrt_nonneg _
      · simp only [FCSFac.norm, Fin.succ_ne_zero, ↓reduceIte, Fin.not_lt_zero]
        exact labelcs_norm_red (fun v w => f w v) mb ma
      · by_cases h : a' = l <;> cases ma <;> simp [FCSFac.use, h0, h]
      · cases mb <;> simp [labelcs_rv, labelcs_val, FCSFac.use, labelcs_redFn]
    | succ b' =>
      simp only [labelcs_red, Fin.cases_succ]
      refine ⟨fun x y => hg x y, ?_, fun l => ?_, ?_⟩
      · simp [FCSFac.norm]
      · simp [FCSFac.use]
      · simp [labelcs_rv, labelcs_val, FCSFac.use]

/-- The reduction of a list of factors of `fcs_contract` after the label `0` is summed: the
product of the values `labelcs_rv`, the product of the norms and the sums of the `ℓ²` uses of the
labels `l + 1` split into the constants `labelcs_const` and the reduced factors `labelcs_red`. -/
private lemma labelcs_list {ι : Type*} [Fintype ι] [Nonempty ι] {L : ℕ} (x' : Fin L → ι) :
    ∀ G : List (FCSFac ι (L + 1)), (∀ g ∈ G, ∀ x y, 0 ≤ g.f x y) →
      (G.map fun g => labelcs_rv g x').prod = (G.map labelcs_const).prod *
        ((G.filterMap labelcs_red).map fun g' => g'.f (x' g'.a) (x' g'.b)).prod ∧
      (G.map FCSFac.norm).prod =
        (G.map labelcs_const).prod * ((G.filterMap labelcs_red).map FCSFac.norm).prod ∧
      ∀ l : Fin L, (G.map fun g => g.use l.succ).sum =
        ((G.filterMap labelcs_red).map fun g' => g'.use l).sum := by
  intro G
  induction G with
  | nil => intro _; simp
  | cons g G ih =>
    intro hG
    obtain ⟨ih1, ih2, ih3⟩ := ih fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')
    have hspec := labelcs_red_spec g (hG g List.mem_cons_self) x'
    cases hr : labelcs_red g with
    | none =>
      rw [hr] at hspec
      obtain ⟨h1, h2⟩ := hspec
      refine ⟨?_, ?_, fun l => ?_⟩
      · simp only [List.map_cons, List.prod_cons, List.filterMap_cons, hr, labelcs_const, ih1,
          ← h1]
        ring
      · simp only [List.map_cons, List.prod_cons, List.filterMap_cons, hr, labelcs_const, ih2]
        ring
      · simp only [List.map_cons, List.sum_cons, List.filterMap_cons, hr, h2, ih3, zero_add]
    | some g' =>
      rw [hr] at hspec
      obtain ⟨h0, h1, h2, h3⟩ := hspec
      refine ⟨?_, ?_, fun l => ?_⟩
      · simp only [List.map_cons, List.prod_cons, List.filterMap_cons, hr, labelcs_const, ih1, h3]
        ring
      · simp only [List.map_cons, List.prod_cons, List.filterMap_cons, hr, labelcs_const, ih2, h1]
        ring
      · simp only [List.map_cons, List.sum_cons, List.filterMap_cons, hr, h2 l, ih3]

/-- The sum of the casts of natural numbers is the cast of their sum. -/
private lemma labelcs_cast_sum {γ : Type*} (G : List γ) (c : γ → ℕ) :
    (G.map fun g => (c g : ℝ)).sum = (((G.map c).sum : ℕ) : ℝ) := by
  induction G with
  | nil => simp
  | cons g G ih => simp [ih]

/-- The statement of `fcs_contract` for the labels `Fin L`. -/
private def labelcs_stmt (ι : Type*) [Fintype ι] (L : ℕ) : Prop :=
  ∀ G : List (FCSFac ι L), (∀ g ∈ G, ∀ x y, 0 ≤ g.f x y) →
    (∀ l, (G.map fun g => g.use l).sum ≤ 2) →
    ∑ x : Fin L → ι, (G.map fun g => g.f (x g.a) (x g.b)).prod ≤
      (∏ l : Fin L, (Fintype.card ι : ℝ) ^ ((2 - ((G.map fun g => g.use l).sum : ℝ)) / 2)) *
        (G.map FCSFac.norm).prod

/-- One step of the induction of `fcs_contract`: the statement for the labels `Fin L` gives the
one for `Fin (L + 1)`, by summing the label `0` first. -/
private lemma labelcs_step {ι : Type*} [Fintype ι] (L : ℕ) (ih : labelcs_stmt ι L) :
    labelcs_stmt ι (L + 1) := by
  intro G hG hcap
  rcases isEmpty_or_nonempty ι with hι | hne
  · rw [Finset.sum_eq_zero fun x _ => (hι.false (x 0)).elim]
    refine mul_nonneg (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
    exact List.prod_nonneg fun a ha => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
      exact labelcs_norm_nonneg g (hG g hg)
  · obtain ⟨_, hN, hU⟩ := labelcs_list (fun _ => Classical.arbitrary ι) G hG
    have hG' : ∀ g' ∈ G.filterMap labelcs_red, ∀ x y, 0 ≤ g'.f x y := by
      intro g' hg'
      obtain ⟨g, hg, hr⟩ := List.mem_filterMap.1 hg'
      have := labelcs_red_spec g (hG g hg) (fun _ => Classical.arbitrary ι)
      rw [hr] at this
      exact this.1
    have hcap' : ∀ l : Fin L, ((G.filterMap labelcs_red).map fun g' => g'.use l).sum ≤ 2 :=
      fun l => (hU l) ▸ hcap l.succ
    have hK : 0 ≤ (G.map labelcs_const).prod := by
      refine List.prod_nonneg fun a ha => ?_
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
      unfold labelcs_const
      split
      · exact labelcs_norm_nonneg g (hG g hg)
      · exact zero_le_one
    have hUR : ∀ l : Fin L, (2 : ℝ) - (G.map fun g => ((g.use l.succ : ℕ) : ℝ)).sum =
        2 - ((G.filterMap labelcs_red).map fun g' => ((g'.use l : ℕ) : ℝ)).sum := by
      intro l
      rw [labelcs_cast_sum, labelcs_cast_sum, hU l]
    have hAnn : 0 ≤ (Fintype.card ι : ℝ) ^
        ((2 - (G.map fun g => ((g.use 0 : ℕ) : ℝ)).sum) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsplit : ∑ x : Fin (L + 1) → ι, (G.map fun g => g.f (x g.a) (x g.b)).prod =
        ∑ x' : Fin L → ι, ∑ v : ι, (G.map fun g => labelcs_val g x' v).prod := by
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ι)
        (fun p => (G.map fun g => g.f ((Fin.cons p.1 p.2 : Fin (L + 1) → ι) g.a)
          ((Fin.cons p.1 p.2 : Fin (L + 1) → ι) g.b)).prod) _ (fun p => rfl)]
      rw [Fintype.sum_prod_type_right]
      rfl
    have hx' : ∀ x' : Fin L → ι, ∑ v, (G.map fun g => labelcs_val g x' v).prod ≤
        (Fintype.card ι : ℝ) ^ ((2 - (G.map fun g => ((g.use 0 : ℕ) : ℝ)).sum) / 2) *
          (G.map fun g => labelcs_rv g x').prod := by
      intro x'
      have := labelcs_claim (fun g v => labelcs_val g x' v) (fun g => g.use 0) G [] _
        (fun g hg v => hG g hg _ _) (fun g _ => labelcs_use_le g 0) (by simp) (by simp) (hcap 0)
      rw [← labelcs_cast_sum] at this
      simpa [labelcs_rv] using this
    rw [hsplit]
    calc ∑ x' : Fin L → ι, ∑ v : ι, (G.map fun g => labelcs_val g x' v).prod
        ≤ ∑ x' : Fin L → ι, ((Fintype.card ι : ℝ) ^
            ((2 - (G.map fun g => ((g.use 0 : ℕ) : ℝ)).sum) / 2) * (G.map labelcs_const).prod) *
          ((G.filterMap labelcs_red).map fun g' => g'.f (x' g'.a) (x' g'.b)).prod :=
          Finset.sum_le_sum fun x' _ => by
            refine (hx' x').trans ?_
            rw [(labelcs_list x' G hG).1]
            exact le_of_eq (by ring)
      _ = ((Fintype.card ι : ℝ) ^ ((2 - (G.map fun g => ((g.use 0 : ℕ) : ℝ)).sum) / 2) *
            (G.map labelcs_const).prod) *
          ∑ x' : Fin L → ι,
            ((G.filterMap labelcs_red).map fun g' => g'.f (x' g'.a) (x' g'.b)).prod :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ((Fintype.card ι : ℝ) ^ ((2 - (G.map fun g => ((g.use 0 : ℕ) : ℝ)).sum) / 2) *
            (G.map labelcs_const).prod) *
          ((∏ l : Fin L, (Fintype.card ι : ℝ) ^
            ((2 - ((G.filterMap labelcs_red).map fun g' => ((g'.use l : ℕ) : ℝ)).sum) / 2)) *
            ((G.filterMap labelcs_red).map FCSFac.norm).prod) :=
          mul_le_mul_of_nonneg_left (ih _ hG' hcap') (mul_nonneg hAnn hK)
      _ = _ := by
          rw [Fin.prod_univ_succ, hN]
          simp only [hUR]
          ring

/-- The statement of `fcs_contract` for every number of labels. -/
private lemma labelcs_all {ι : Type*} [Fintype ι] : ∀ L : ℕ, labelcs_stmt ι L := by
  intro L
  induction L with
  | zero =>
    intro G _ _
    have hG : G = [] := by
      cases G with
      | nil => rfl
      | cons g _ => exact g.a.elim0
    subst hG
    simp
  | succ L ih => exact labelcs_step L ih

/-- The label Cauchy–Schwarz of (5.68) [bound_factors]–(5.71) [Cauchy_example_2], Example 5.7
[example_estimate_reminder_reminder_terms] and the companion cases of Lemma 5.5
[claim_estimate_remainder_terms], in one step: if each label carries at most two `ℓ²` uses, the
sum over all labels of a product of nonnegative factors is at most `|ι|^{(2 - c_l)/2}` per label
`l` (`c_l` its uses) times the product of the mixed norms, the labels summed in the order of
`Fin L`. -/
theorem fcs_contract {ι : Type*} [Fintype ι] (L : ℕ) (G : List (FCSFac ι L))
    (hG : ∀ g ∈ G, ∀ x y, 0 ≤ g.f x y) (hcap : ∀ l, (G.map fun g => g.use l).sum ≤ 2) :
    ∑ x : Fin L → ι, (G.map fun g => g.f (x g.a) (x g.b)).prod ≤
      (∏ l : Fin L, (Fintype.card ι : ℝ) ^ ((2 - ((G.map fun g => g.use l).sum : ℝ)) / 2)) *
        (G.map FCSFac.norm).prod :=
  labelcs_all L G hG hcap

end RBMTransitionEdge

end
