module

public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# Complex cumulants (Lemma 2.11, (2.27))

The joint cumulants and the complex `(p, q)`-cumulants `𝒞^{(p,q)}` of a law on `ℂ`, defined by the set-partition
formula, the Wirtinger derivatives used in Lemma 2.11 [lem:complex_cumu], the moment–cumulant recursion, the scaling
`𝒞^{(p,q)}(ch) = c^{p+q} 𝒞^{(p,q)}(h)`, the low cumulants under Assumption 1 [main_assm] and the bounds (2.27)
[eq:bdd_cumu] in scaled form.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The joint cumulant of `X₁, …, Xₙ` under `μ` by the moment–cumulant formula over set
partitions: `Σ_π (-1)^{|π|-1} (|π| - 1)! Π_{B ∈ π} E Π_{i ∈ B} X_i`. -/
def jointCum {n : ℕ} (μ : Measure ℂ) (X : Fin n → ℂ → ℂ) : ℂ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
    (-1 : ℂ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℂ) *
      ∏ B ∈ π.parts, ∫ z, (∏ i ∈ B, X i z) ∂μ

/-- The `(p, q)`-cumulant `𝒞^{(p,q)}(h)` of Lemma 2.11 [lem:complex_cumu]: the joint cumulant of
`p` copies of `h` and `q` copies of `h̄`. -/
def ccum (μ : Measure ℂ) (p q : ℕ) : ℂ :=
  jointCum μ fun i : Fin (p + q) => if (i : ℕ) < p then (fun z => z) else (fun z => starRingEnd ℂ z)

/-- The Wirtinger derivative `∂_z F = (∂_x F - i ∂_y F) / 2`. -/
def dW (F : ℂ → ℂ) : ℂ → ℂ := fun z => (fderiv ℝ F z 1 - Complex.I * fderiv ℝ F z Complex.I) / 2

/-- The Wirtinger derivative `∂_{z̄} F = (∂_x F + i ∂_y F) / 2`. -/
def dWbar (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I) / 2

/-- `F^{(p,q)} = ∂_z^p ∂_{z̄}^q F`, the derivatives `f^{(p,q)}(h, h̄)` of Lemma 2.11
[lem:complex_cumu]. -/
def wirt (p q : ℕ) (F : ℂ → ℂ) : ℂ → ℂ := dW^[p] (dWbar^[q] F)

/-! ### Sums over set partitions -/

section Partition

variable {α : Type*} [DecidableEq α]

/-- The coefficient `(-1)^{k-1} (k-1)!` of a partition with `k` blocks in `jointCum`. -/
private def Cumulant_coef (k : ℕ) : ℂ := (-1 : ℂ) ^ (k - 1) * ((k - 1).factorial : ℂ)

/-- `c_k + (k-1) c_{k-1}` is `1` for `k = 1` and `0` for `k ≥ 2`. -/
private lemma Cumulant_coef_add (k : ℕ) (hk : 1 ≤ k) :
    Cumulant_coef k + ((k - 1 : ℕ) : ℂ) * Cumulant_coef (k - 1) = if k = 1 then 1 else 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · simp [Cumulant_coef]
  · simp only [Cumulant_coef, Nat.add_sub_cancel, Nat.factorial_succ]
    rw [ite_eq_right (by omega)]
    push_cast
    ring

/-- The block sets of the set partitions of `T`. -/
private def Cumulant_PS (T : Finset α) : Finset (Finset (Finset α)) :=
  (Finset.univ : Finset (Finpartition T)).image Finpartition.parts

/-- `P` is the block set of a partition of `T`: nonempty, pairwise disjoint blocks covering
`T`. -/
private lemma Cumulant_mem_PS {T : Finset α} {P : Finset (Finset α)} :
    P ∈ Cumulant_PS T ↔ (∀ B ∈ P, B.Nonempty) ∧ (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧
      ∀ x, x ∈ T ↔ ∃ B ∈ P, x ∈ B := by
  simp only [Cumulant_PS, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨π, rfl⟩
    refine ⟨fun B hB => π.nonempty_of_mem_parts hB, fun B hB C hC h => π.disjoint hB hC h,
      fun x => ⟨fun hx => π.exists_mem hx, fun ⟨B, hB, hx⟩ => π.subset hB hx⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨P, ?_, ?_, ?_⟩, rfl⟩
    · rw [Finset.supIndep_iff_pairwiseDisjoint]
      intro B hB C hC h
      exact h2 B hB C hC h
    · ext x
      rw [Finset.mem_sup, h3]
      rfl
    · intro h
      exact Finset.not_nonempty_empty (h1 ⊥ h)

/-- `Σ_π (-1)^{|π|-1} (|π|-1)! Π_{B ∈ π} m(B)`, the sum over the set partitions `π` of `T`. -/
private def Cumulant_K (m : Finset α → ℂ) (T : Finset α) : ℂ :=
  ∑ π : Finpartition T, Cumulant_coef π.parts.card * ∏ B ∈ π.parts, m B

/-- `Cumulant_K` as a sum over block sets. -/
private lemma Cumulant_K_eq (m : Finset α → ℂ) (T : Finset α) :
    Cumulant_K m T = ∑ P ∈ Cumulant_PS T, Cumulant_coef P.card * ∏ B ∈ P, m B := by
  rw [Cumulant_PS, Finset.sum_image (fun π _ π' _ h => Finpartition.ext h)]
  rfl

/-- The moment–cumulant recursion for a set function with `m(∅) = 1`: splitting off the block
that contains `l`, `m(T) = Σ_{S ⊆ T ∖ {l}} K(S ∪ {l}) m(T ∖ (S ∪ {l}))`. -/
private lemma Cumulant_rec (m : Finset α → ℂ) (hm : m ∅ = 1) {T : Finset α} {l : α}
    (hl : l ∈ T) :
    m T = ∑ S ∈ (T.erase l).powerset, Cumulant_K m (insert l S) * m (T.erase l \ S) := by
  have hT : {T} ∈ Cumulant_PS T := by
    rw [Cumulant_mem_PS]
    exact ⟨by simpa using ⟨l, hl⟩, by simp, by simp⟩
  have hterm : ∀ P ∈ Cumulant_PS T,
      (Cumulant_coef P.card + ((P.card - 1 : ℕ) : ℂ) * Cumulant_coef (P.card - 1)) *
        ∏ B ∈ P, m B = if P = {T} then m T else 0 := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
    have hpos : 1 ≤ P.card := by
      obtain ⟨B, hB, -⟩ := (h3 l).1 hl
      exact Finset.card_pos.2 ⟨B, hB⟩
    rw [Cumulant_coef_add _ hpos]
    by_cases hc : P.card = 1
    · obtain ⟨B, rfl⟩ := Finset.card_eq_one.1 hc
      have hB : B = T := by
        ext x
        rw [h3 x]
        simp
      subst hB
      simp
    · rw [ite_eq_right hc, zero_mul, ite_eq_right]
      rintro rfl
      exact hc (Finset.card_singleton T)
  have hfilt : ∀ P ∈ Cumulant_PS T, (P.filter fun D => l ∉ D).card = P.card - 1 := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
    have h := Finset.card_filter_add_card_filter_not (s := P) (fun D => l ∈ D)
    have hone : (P.filter fun D => l ∈ D).card = 1 := by
      obtain ⟨B, hB, hlB⟩ := (h3 l).1 hl
      refine Finset.card_eq_one.2 ⟨B, ?_⟩
      ext C
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hC, hlC⟩
        by_contra hCB
        exact Finset.disjoint_left.1 (h2 C hC B hB hCB) hlC hlB
      · rintro rfl
        exact ⟨hB, hlB⟩
    omega
  have hstep1 : m T = ∑ P ∈ Cumulant_PS T,
      (Cumulant_coef P.card + ((P.card - 1 : ℕ) : ℂ) * Cumulant_coef (P.card - 1)) *
        ∏ B ∈ P, m B := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ _, ite_eq_left hT]
  have hstep2 : ∑ P ∈ Cumulant_PS T,
      (Cumulant_coef P.card + ((P.card - 1 : ℕ) : ℂ) * Cumulant_coef (P.card - 1)) *
        ∏ B ∈ P, m B = Cumulant_K m T + ∑ P ∈ Cumulant_PS T, ∑ D ∈ P.filter (fun D => l ∉ D),
          Cumulant_coef (P.card - 1) * ∏ B ∈ P, m B := by
    rw [Cumulant_K_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [Finset.sum_const, hfilt P hP, nsmul_eq_mul]
    ring
  have hstep4 : ∑ P ∈ Cumulant_PS T, ∑ D ∈ P.filter (fun D => l ∉ D),
        Cumulant_coef (P.card - 1) * ∏ B ∈ P, m B =
      ∑ S ∈ (T.erase l).powerset.erase (T.erase l), ∑ Q ∈ Cumulant_PS (insert l S),
        (Cumulant_coef Q.card * ∏ B ∈ Q, m B) * m (T.erase l \ S) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨T.erase l \ x.2, x.1.erase x.2⟩)
      (fun y => ⟨insert (T.erase l \ y.1) y.2, T.erase l \ y.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨P, D⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_filter] at hx ⊢
      obtain ⟨hP, hD, hlD⟩ := hx
      obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
      have hDU : D ⊆ T.erase l := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hlD (h ▸ hx), (h3 x).2 ⟨D, hD, hx⟩⟩
      refine ⟨Finset.mem_erase.2 ⟨?_, Finset.mem_powerset.2 Finset.sdiff_subset⟩,
        Cumulant_mem_PS.2 ⟨fun B hB => h1 B (Finset.mem_of_mem_erase hB),
          fun B hB C hC h => h2 B (Finset.mem_of_mem_erase hB) C (Finset.mem_of_mem_erase hC) h,
          fun x => ?_⟩⟩
      · obtain ⟨d, hd⟩ := h1 D hD
        intro h
        have : d ∈ T.erase l \ D := by rw [h]; exact hDU hd
        exact (Finset.mem_sdiff.1 this).2 hd
      · simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨⟨hxl, hxT⟩, hxD⟩)
          · obtain ⟨B, hB, hlB⟩ := (h3 x).1 hl
            exact ⟨B, ⟨fun h => hlD (h ▸ hlB), hB⟩, hlB⟩
          · obtain ⟨B, hB, hxB⟩ := (h3 x).1 hxT
            exact ⟨B, ⟨fun h => hxD (h ▸ hxB), hB⟩, hxB⟩
        · rintro ⟨B, ⟨hBD, hB⟩, hxB⟩
          by_cases hxl : x = l
          · exact Or.inl hxl
          refine Or.inr ⟨⟨hxl, (h3 x).2 ⟨B, hB, hxB⟩⟩, fun hxD => ?_⟩
          exact Finset.disjoint_left.1 (h2 B hB D hD hBD) hxB hxD
    · rintro ⟨S, Q⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_powerset] at hy ⊢
      obtain ⟨⟨hSU, hS⟩, hQ⟩ := hy
      obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hQ
      have hne : (T.erase l \ S).Nonempty :=
        Finset.sdiff_nonempty.2 fun h => hSU (Finset.Subset.antisymm hS h)
      have hdisj : ∀ B ∈ Q, Disjoint (T.erase l \ S) B := by
        intro B hB
        rw [Finset.disjoint_left]
        intro x hx hxB
        have hx' := (h3 x).2 ⟨B, hB, hxB⟩
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert] at hx hx'
        rcases hx' with h | h
        · exact hx.1.1 h
        · exact hx.2 h
      refine ⟨Cumulant_mem_PS.2 ⟨?_, ?_, ?_⟩, Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, ?_⟩⟩
      · intro B hB
        rcases Finset.mem_insert.1 hB with rfl | hB
        · exact hne
        · exact h1 B hB
      · intro B hB C hC hBC
        rcases Finset.mem_insert.1 hB with rfl | hB <;> rcases Finset.mem_insert.1 hC with rfl | hC
        · exact absurd rfl hBC
        · exact hdisj C hC
        · exact (hdisj B hB).symm
        · exact h2 B hB C hC hBC
      · intro x
        rw [Finset.exists_mem_insert, ← h3 x]
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        constructor
        · intro hx
          by_cases hxl : x = l
          · exact Or.inr (Or.inl hxl)
          by_cases hxS : x ∈ S
          · exact Or.inr (Or.inr hxS)
          · exact Or.inl ⟨⟨hxl, hx⟩, hxS⟩
        · rintro (⟨⟨-, hx⟩, -⟩ | rfl | hxS)
          · exact hx
          · exact hl
          · exact (Finset.mem_erase.1 (hS hxS)).2
      · simp
    · rintro ⟨P, D⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_filter] at hx
      obtain ⟨hP, hD, hlD⟩ := hx
      obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
      have hDU : D ⊆ T.erase l := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hlD (h ▸ hx), (h3 x).2 ⟨D, hD, hx⟩⟩
      simp only
      rw [Finset.sdiff_sdiff_eq_self hDU, Finset.insert_erase hD]
    · rintro ⟨S, Q⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_powerset] at hy
      obtain ⟨⟨hSU, hS⟩, hQ⟩ := hy
      obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hQ
      have hne : (T.erase l \ S).Nonempty :=
        Finset.sdiff_nonempty.2 fun h => hSU (Finset.Subset.antisymm hS h)
      have hnot : T.erase l \ S ∉ Q := by
        intro h
        obtain ⟨x, hx⟩ := hne
        have hx' := (h3 x).2 ⟨_, h, hx⟩
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert] at hx hx'
        rcases hx' with h | h
        · exact hx.1.1 h
        · exact hx.2 h
      simp only
      rw [Finset.erase_insert hnot, Finset.sdiff_sdiff_eq_self hS]
    · rintro ⟨P, D⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_filter] at hx
      obtain ⟨hP, hD, hlD⟩ := hx
      obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
      have hDU : D ⊆ T.erase l := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hlD (h ▸ hx), (h3 x).2 ⟨D, hD, hx⟩⟩
      simp only
      rw [Finset.sdiff_sdiff_eq_self hDU, Finset.card_erase_of_mem hD,
        ← Finset.mul_prod_erase P m hD]
      ring
  rw [hstep1, hstep2, hstep4, ← Finset.add_sum_erase _ _
    (Finset.mem_powerset.2 (Finset.Subset.refl (T.erase l))), Finset.insert_erase hl,
    Finset.sdiff_self, hm, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Cumulant_K_eq, Finset.sum_mul]


/-- The partition sum is invariant under an injective relabelling of the indices. -/
private lemma Cumulant_K_image {β : Type*} [DecidableEq β] (m : Finset α → ℂ) {g : β → α}
    (hg : Function.Injective g) (T : Finset β) :
    Cumulant_K m (T.image g) = Cumulant_K (fun B => m (B.image g)) T := by
  rw [Cumulant_K_eq, Cumulant_K_eq]
  symm
  refine Finset.sum_nbij' (fun P => P.image (Finset.image g))
    (fun Q => Q.image fun B => T.filter fun x => g x ∈ B) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
    refine Cumulant_mem_PS.2 ⟨?_, ?_, ?_⟩
    · intro B' hB'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      exact (h1 B hB).image g
    · intro B' hB' C' hC' h
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hC'
      have hBC : B ≠ C := fun e => h (e ▸ rfl)
      exact (Finset.disjoint_image hg).2 (h2 B hB C hC hBC)
    · intro y
      simp only [Finset.mem_image, exists_exists_and_eq_and]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨B, hB, hxB⟩ := (h3 x).1 hx
        exact ⟨B, hB, x, hxB, rfl⟩
      · rintro ⟨B, hB, x, hxB, rfl⟩
        exact ⟨x, (h3 x).2 ⟨B, hB, hxB⟩, rfl⟩
  · intro Q hQ
    obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hQ
    refine Cumulant_mem_PS.2 ⟨?_, ?_, ?_⟩
    · intro B' hB'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      obtain ⟨y, hy⟩ := h1 B hB
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ((h3 y).2 ⟨B, hB, hy⟩)
      exact ⟨x, Finset.mem_filter.2 ⟨hx, hy⟩⟩
    · intro B' hB' C' hC' h
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB'
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hC'
      have hBC : B ≠ C := fun e => h (e ▸ rfl)
      rw [Finset.disjoint_left]
      intro x hxB hxC
      exact Finset.disjoint_left.1 (h2 B hB C hC hBC) (Finset.mem_filter.1 hxB).2
        (Finset.mem_filter.1 hxC).2
    · intro x
      simp only [Finset.mem_image, exists_exists_and_eq_and, Finset.mem_filter]
      constructor
      · intro hx
        obtain ⟨B, hB, hxB⟩ := (h3 (g x)).1 (Finset.mem_image_of_mem g hx)
        exact ⟨B, hB, hx, hxB⟩
      · rintro ⟨B, -, hx, -⟩
        exact hx
  · intro P hP
    obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hP
    simp only [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := P)]
    refine Finset.image_congr fun B hB => ?_
    ext x
    simp only [Function.comp_apply, Finset.mem_filter, hg.mem_finset_image, id]
    exact ⟨fun h => h.2, fun h => ⟨(h3 x).2 ⟨B, hB, h⟩, h⟩⟩
  · intro Q hQ
    obtain ⟨h1, h2, h3⟩ := Cumulant_mem_PS.1 hQ
    simp only [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := Q)]
    refine Finset.image_congr fun B hB => ?_
    ext y
    simp only [Function.comp_apply, Finset.mem_image, Finset.mem_filter, id]
    constructor
    · rintro ⟨x, ⟨-, hxB⟩, rfl⟩
      exact hxB
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ((h3 y).2 ⟨B, hB, hy⟩)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  · intro P hP
    rw [Finset.card_image_of_injective _ (Finset.image_injective hg),
      Finset.prod_image fun B _ C _ h => Finset.image_injective hg h]

end Partition

/-- The moment `E Π_{i ∈ B} X_i` of a block. -/
private def Cumulant_mom (μ : Measure ℂ) {ι : Type*} (X : ι → ℂ → ℂ) (B : Finset ι) : ℂ :=
  ∫ z, (∏ i ∈ B, X i z) ∂μ

/-- The variable `h` at the indices with `τ i` and `h̄` elsewhere. -/
private def Cumulant_typ {ι : Type*} (τ : ι → Prop) [DecidablePred τ] : ι → ℂ → ℂ :=
  fun i => if τ i then (fun z => z) else (fun z => starRingEnd ℂ z)

/-- `ccum` as a partition sum. -/
private lemma Cumulant_ccum_eq (μ : Measure ℂ) (p q : ℕ) :
    ccum μ p q = Cumulant_K (Cumulant_mom μ (Cumulant_typ fun i : Fin (p + q) => (i : ℕ) < p))
      Finset.univ := rfl

/-- The moment of a block of `h`'s and `h̄`'s is `E h^a h̄^b`. -/
private lemma Cumulant_mom_typ (μ : Measure ℂ) {ι : Type*} (τ : ι → Prop) [DecidablePred τ]
    (B : Finset ι) :
    Cumulant_mom μ (Cumulant_typ τ) B =
      ∫ z, z ^ (B.filter τ).card * starRingEnd ℂ z ^ (B.filter fun i => ¬ τ i).card ∂μ := by
  unfold Cumulant_mom Cumulant_typ
  congr 1
  funext z
  simp only [ite_apply]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]

/-- The joint cumulant of `a` copies of `h` and `b` copies of `h̄`, in any arrangement, is
`𝒞^{(a,b)}`. -/
private lemma Cumulant_K_typ (μ : Measure ℂ) {ι : Type*} [DecidableEq ι] (τ : ι → Prop)
    [DecidablePred τ] (T : Finset ι) :
    Cumulant_K (Cumulant_mom μ (Cumulant_typ τ)) T =
      ccum μ (T.filter τ).card (T.filter fun i => ¬ τ i).card := by
  set A := T.filter τ
  set B := T.filter fun i => ¬ τ i
  let eA := Finset.equivFinOfCardEq (s := A) rfl
  let eB := Finset.equivFinOfCardEq (s := B) rfl
  let g : Fin (A.card + B.card) → ι :=
    Fin.addCases (fun i => (eA.symm i : ι)) (fun j => (eB.symm j : ι))
  have hgA : ∀ i : Fin A.card, g (Fin.castAdd B.card i) ∈ A := by
    intro i; simp [g]
  have hgB : ∀ j : Fin B.card, g (Fin.natAdd A.card j) ∈ B := by
    intro j; simp [g]
  have hτ : ∀ i, τ (g i) ↔ (i : ℕ) < A.card := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact ⟨fun _ => by simp, fun _ => (Finset.mem_filter.1 (hgA i)).2⟩
    · exact ⟨fun h => absurd h (Finset.mem_filter.1 (hgB j)).2, fun h => by simp at h⟩
  have hinj : Function.Injective g := by
    intro i i'
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;>
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i' <;> intro h
    · simp only [g, Fin.addCases_left] at h
      rw [eA.symm.injective (Subtype.ext h)]
    · exact absurd (Finset.mem_filter.1 (hgA i)).2
        (by rw [h]; exact (Finset.mem_filter.1 (hgB j')).2)
    · exact absurd (Finset.mem_filter.1 (hgA i')).2
        (by rw [← h]; exact (Finset.mem_filter.1 (hgB j)).2)
    · simp only [g, Fin.addCases_right] at h
      rw [eB.symm.injective (Subtype.ext h)]
  have himg : Finset.univ.image g = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact (Finset.mem_filter.1 (hgA i)).1
      · exact (Finset.mem_filter.1 (hgB j)).1
    · intro hx
      by_cases hxτ : τ x
      · have hxA : x ∈ A := Finset.mem_filter.2 ⟨hx, hxτ⟩
        exact Finset.mem_image.2 ⟨Fin.castAdd B.card (eA ⟨x, hxA⟩), Finset.mem_univ _, by simp [g]⟩
      · have hxB : x ∈ B := Finset.mem_filter.2 ⟨hx, hxτ⟩
        exact Finset.mem_image.2 ⟨Fin.natAdd A.card (eB ⟨x, hxB⟩), Finset.mem_univ _, by simp [g]⟩
  rw [← himg, Cumulant_K_image _ hinj, Cumulant_ccum_eq]
  congr 1
  funext C
  unfold Cumulant_mom
  congr 1
  funext z
  rw [Finset.prod_image hinj.injOn]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Cumulant_typ]
  rw [if_congr (hτ i) rfl rfl]

/-- Counting the subsets of `U` by the numbers of indices of each type. -/
private lemma Cumulant_sum_powerset {ι : Type*} (τ : ι → Prop) [DecidablePred τ]
    (U : Finset ι) (F : ℕ → ℕ → ℂ) :
    ∑ S ∈ U.powerset, F (S.filter τ).card (S.filter fun i => ¬ τ i).card =
      ∑ p ∈ Finset.range ((U.filter τ).card + 1),
        ∑ q ∈ Finset.range ((U.filter fun i => ¬ τ i).card + 1),
          (((U.filter τ).card.choose p : ℂ) * ((U.filter fun i => ¬ τ i).card.choose q : ℂ)) *
            F p q := by
  set A := U.filter τ
  set B := U.filter fun i => ¬ τ i
  have h1 : ∑ S ∈ U.powerset, F (S.filter τ).card (S.filter fun i => ¬ τ i).card =
      ∑ x ∈ A.powerset ×ˢ B.powerset, F x.1.card x.2.card := by
    refine Finset.sum_nbij' (fun S => (S.filter τ, S.filter fun i => ¬ τ i))
      (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_product, Finset.mem_powerset] at hS ⊢
      exact ⟨Finset.filter_subset_filter _ hS, Finset.filter_subset_filter _ hS⟩
    · intro x hx
      simp only [Finset.mem_product, Finset.mem_powerset] at hx ⊢
      exact Finset.union_subset (hx.1.trans (Finset.filter_subset _ _))
        (hx.2.trans (Finset.filter_subset _ _))
    · intro S _
      exact Finset.filter_union_filter_not_eq _ _
    · rintro ⟨X, Y⟩ hx
      simp only [Finset.mem_product, Finset.mem_powerset] at hx
      obtain ⟨hX, hY⟩ := hx
      refine Prod.ext ?_ ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hi | hi, hτ⟩
          · exact hi
          · exact absurd hτ (Finset.mem_filter.1 (hY hi)).2
        · intro hi
          exact ⟨Or.inl hi, (Finset.mem_filter.1 (hX hi)).2⟩
      · ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hi | hi, hτ⟩
          · exact absurd (Finset.mem_filter.1 (hX hi)).2 hτ
          · exact hi
        · intro hi
          exact ⟨Or.inr hi, (Finset.mem_filter.1 (hY hi)).2⟩
    · intro S _
      rfl
  rw [h1, Finset.sum_product]
  have h2 : ∀ X : Finset ι, ∑ Y ∈ B.powerset, F X.card Y.card =
      ∑ q ∈ Finset.range (B.card + 1), (B.card.choose q : ℂ) * F X.card q := fun X => by
    rw [Finset.sum_powerset_apply_card (fun k => F X.card k)]
    simp [nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun X _ => h2 X, Finset.sum_comm]
  have h3 : ∀ q, ∑ X ∈ A.powerset, (B.card.choose q : ℂ) * F X.card q =
      ∑ p ∈ Finset.range (A.card + 1), (A.card.choose p : ℂ) * ((B.card.choose q : ℂ) * F p q) :=
    fun q => by
      rw [Finset.sum_powerset_apply_card (fun k => (B.card.choose q : ℂ) * F k q)]
      simp [nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun q _ => h3 q, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The recursion of `Cumulant_rec` for the variables `Cumulant_typ τ`, grouped by type counts. -/
private lemma Cumulant_rec_count (μ : Measure ℂ) [IsProbabilityMeasure μ] {ι : Type*}
    [DecidableEq ι] (τ : ι → Prop) [DecidablePred τ] {T : Finset ι} {l : ι} (hl : l ∈ T)
    (a b : ℕ) (ha : ((T.erase l).filter τ).card = a)
    (hb : ((T.erase l).filter fun i => ¬ τ i).card = b) :
    Cumulant_mom μ (Cumulant_typ τ) T =
      ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
        (a.choose p * b.choose q : ℂ) *
          ccum μ (p + if τ l then 1 else 0) (q + if τ l then 0 else 1) *
            ∫ z, z ^ (a - p) * starRingEnd ℂ z ^ (b - q) ∂μ := by
  have hm : Cumulant_mom μ (Cumulant_typ τ) ∅ = 1 := by
    simp [Cumulant_mom]
  rw [Cumulant_rec _ hm hl]
  have hS : ∀ S ∈ (T.erase l).powerset,
      Cumulant_K (Cumulant_mom μ (Cumulant_typ τ)) (insert l S) *
          Cumulant_mom μ (Cumulant_typ τ) (T.erase l \ S) =
        (fun p q => ccum μ (p + if τ l then 1 else 0) (q + if τ l then 0 else 1) *
            ∫ z, z ^ (a - p) * starRingEnd ℂ z ^ (b - q) ∂μ)
          (S.filter τ).card (S.filter fun i => ¬ τ i).card := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hlS : l ∉ S := fun h => by simpa using hS h
    have hsd : ∀ (σ : ι → Prop) [DecidablePred σ],
        ((T.erase l \ S).filter σ).card = ((T.erase l).filter σ).card - (S.filter σ).card := by
      intro σ _
      rw [← Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hS)]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    rw [Cumulant_K_typ, Cumulant_mom_typ, hsd, hsd, ha, hb]
    simp only [Finset.filter_insert]
    by_cases hτ : τ l
    · simp [hτ, Finset.card_insert_of_notMem (fun h => hlS (Finset.mem_filter.1 h).1)]
    · simp [hτ, Finset.card_insert_of_notMem (fun h => hlS (Finset.mem_filter.1 h).1)]
  rw [Finset.sum_congr rfl hS, Cumulant_sum_powerset τ (T.erase l)
    (fun p q => ccum μ (p + if τ l then 1 else 0) (q + if τ l then 0 else 1) *
      ∫ z, z ^ (a - p) * starRingEnd ℂ z ^ (b - q) ∂μ), ha, hb]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `E h^a h̄^{b+1}` by the recursion, with the last index of type `h̄`. -/
private lemma Cumulant_rec_hbar (μ : Measure ℂ) [IsProbabilityMeasure μ] (a b : ℕ) :
    ∫ z, z ^ a * starRingEnd ℂ z ^ (b + 1) ∂μ =
      ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
        (a.choose p * b.choose q : ℂ) * ccum μ p (q + 1) *
          ∫ z, z ^ (a - p) * starRingEnd ℂ z ^ (b - q) ∂μ := by
  have hA : (Finset.univ.filter fun i : Fin (a + b + 1) => (i : ℕ) < a).card = a := by
    rw [Fin.card_filter_val_lt]
    omega
  have hB : (Finset.univ.filter fun i : Fin (a + b + 1) => ¬ (i : ℕ) < a).card = b + 1 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (a + b + 1) => (i : ℕ) < a)
    rw [hA, Finset.card_univ, Fintype.card_fin] at this
    omega
  have key := Cumulant_rec_count μ (fun i : Fin (a + b + 1) => (i : ℕ) < a)
    (Finset.mem_univ (Fin.last (a + b))) a b
    (by rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp), hA])
    (by rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp), hB]; rfl)
  have hl : ¬ ((Fin.last (a + b) : ℕ) < a) := by simp
  simp only [hl, ite_false, add_zero] at key
  rw [← key, Cumulant_mom_typ, hA, hB]

/-- `E h^{a+1} h̄^b` by the recursion, with the last index of type `h`. -/
private lemma Cumulant_rec_h (μ : Measure ℂ) [IsProbabilityMeasure μ] (a b : ℕ) :
    ∫ z, z ^ (a + 1) * starRingEnd ℂ z ^ b ∂μ =
      ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
        (a.choose p * b.choose q : ℂ) * ccum μ (p + 1) q *
          ∫ z, z ^ (a - p) * starRingEnd ℂ z ^ (b - q) ∂μ := by
  have hA : (Finset.univ.filter fun i : Fin (a + b + 1) => ¬ b ≤ (i : ℕ)).card = b := by
    simp only [not_le]
    rw [Fin.card_filter_val_lt]
    omega
  have hB : (Finset.univ.filter fun i : Fin (a + b + 1) => b ≤ (i : ℕ)).card = a + 1 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (a + b + 1) => b ≤ (i : ℕ))
    rw [hA, Finset.card_univ, Fintype.card_fin] at this
    omega
  have key := Cumulant_rec_count μ (fun i : Fin (a + b + 1) => b ≤ (i : ℕ))
    (Finset.mem_univ (Fin.last (a + b))) a b
    (by rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp), hB]; rfl)
    (by rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp), hA])
  have hl : b ≤ ((Fin.last (a + b) : ℕ)) := by simp
  simp only [hl, ite_true, add_zero] at key
  rw [← key, Cumulant_mom_typ, hA, hB]

/-- The partition sum is homogeneous: `Σ_π c_π Π_B (c^{|B|} m(B)) = c^{|T|} Σ_π c_π Π_B m(B)`. -/
private lemma Cumulant_K_smul {α : Type*} [DecidableEq α] (m : Finset α → ℂ) (c : ℂ)
    (T : Finset α) :
    Cumulant_K (fun B => c ^ B.card * m B) T = c ^ T.card * Cumulant_K m T := by
  unfold Cumulant_K
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, π.sum_card_parts]
  ring

/-- A bound on the partition sum from bounds on the block values. -/
private lemma Cumulant_norm_K_le {α : Type*} [DecidableEq α] (m : Finset α → ℂ) (D : ℕ → ℝ)
    (T : Finset α) (h : ∀ B, ‖m B‖ ≤ D B.card) :
    ‖Cumulant_K m T‖ ≤
      ∑ π : Finpartition T, ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, D B.card := by
  unfold Cumulant_K
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [norm_mul, norm_prod]
  have hc : ‖Cumulant_coef π.parts.card‖ = ((π.parts.card - 1).factorial : ℝ) := by
    simp [Cumulant_coef]
  rw [hc]
  gcongr with B hB
  exact h B

/-- `‖Π_{i ∈ B} X_i(z)‖ = ‖z‖^{|B|}` for the variables `h`, `h̄`. -/
private lemma Cumulant_norm_prod_typ {ι : Type*} (τ : ι → Prop) [DecidablePred τ] (B : Finset ι)
    (z : ℂ) : ‖∏ i ∈ B, Cumulant_typ τ i z‖ = ‖z‖ ^ B.card := by
  rw [norm_prod, Finset.prod_congr rfl fun i _ => (show ‖Cumulant_typ τ i z‖ = ‖z‖ by
    simp only [Cumulant_typ]; split_ifs <;> simp), Finset.prod_const]

/-- The cumulants up to order two of a probability measure on `ℂ`. -/
private lemma Cumulant_low (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ccum μ 1 0 = ∫ z, z ∂μ ∧ ccum μ 0 1 = ∫ z, starRingEnd ℂ z ∂μ ∧
      ccum μ 1 1 = ∫ z, z * starRingEnd ℂ z ∂μ - (∫ z, starRingEnd ℂ z ∂μ) * ∫ z, z ∂μ ∧
      ccum μ 2 0 = ∫ z, z ^ 2 ∂μ - (∫ z, z ∂μ) ^ 2 ∧
      ccum μ 0 2 = ∫ z, starRingEnd ℂ z ^ 2 ∂μ - (∫ z, starRingEnd ℂ z ∂μ) ^ 2 := by
  have h10 := Cumulant_rec_h μ 0 0
  have h01 := Cumulant_rec_hbar μ 0 0
  have h11 := Cumulant_rec_hbar μ 1 0
  have h20 := Cumulant_rec_h μ 1 0
  have h02 := Cumulant_rec_hbar μ 0 1
  simp only [zero_add, pow_one, pow_zero, mul_one, Finset.range_one, zero_tsub, integral_const,
    probReal_univ, one_smul, Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.reduceAdd, Finset.sum_range_succ, Nat.choose_succ_self_right, tsub_zero,
    tsub_self] at h10 h01 h11 h20 h02
  refine ⟨h10.symm, h01.symm, ?_, ?_, ?_⟩
  · rw [h11, h01]
    ring
  · rw [h20, h10]
    ring
  · rw [h02, h01]
    ring


/-- The moment–cumulant recursion `E h^a h̄^{b+1} = Σ_{p ≤ a, q ≤ b} C(a,p) C(b,q) 𝒞^{(p,q+1)}
E h^{a-p} h̄^{b-q}`: (2.26) [5.16] for polynomial `F`. -/
theorem moment_ccum_recursion (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : ∀ p : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ p) μ) (a b : ℕ) :
    ∫ z, z ^ a * starRingEnd ℂ z ^ (b + 1) ∂μ =
      ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
        (a.choose p * b.choose q : ℂ) * ccum μ p (q + 1) *
          ∫ z, z ^ (a - p) * starRingEnd ℂ z ^ (b - q) ∂μ :=
  Cumulant_rec_hbar μ a b

/-- Scaling: `𝒞^{(p,q)}(c h) = c^{p+q} 𝒞^{(p,q)}(h)` for real `c`. -/
theorem ccum_map_smul (μ : Measure ℂ) [IsProbabilityMeasure μ] (c : ℝ) (p q : ℕ) :
    ccum (μ.map fun z => (c : ℂ) * z) p q = (c : ℂ) ^ (p + q) * ccum μ p q := by
  set X := Cumulant_typ fun i : Fin (p + q) => (i : ℕ) < p
  have hX : ∀ i z, X i ((c : ℂ) * z) = (c : ℂ) * X i z := by
    intro i z
    simp only [X, Cumulant_typ]
    split_ifs
    · rfl
    · simp [Complex.conj_ofReal]
  have hXc : ∀ i, Continuous (X i) := by
    intro i
    simp only [X, Cumulant_typ]
    split_ifs
    · exact continuous_id
    · exact Complex.continuous_conj
  have hmom : Cumulant_mom (μ.map fun z => (c : ℂ) * z) X =
      fun B => (c : ℂ) ^ B.card * Cumulant_mom μ X B := by
    funext B
    unfold Cumulant_mom
    rw [integral_map (φ := fun z : ℂ => (c : ℂ) * z)
      (continuous_const.mul continuous_id).aemeasurable
      (continuous_finsetProd _ fun i _ => hXc i).aestronglyMeasurable]
    simp only [hX, Finset.prod_mul_distrib, Finset.prod_const]
    rw [integral_const_mul]
  rw [Cumulant_ccum_eq, Cumulant_ccum_eq, hmom, Cumulant_K_smul, Finset.card_univ,
    Fintype.card_fin]

/-- The second-order cumulants of (2.27) [eq:bdd_cumu] in scaled form: `𝒞^{(1,0)} = 𝒞^{(0,1)} = 0`,
`𝒞^{(1,1)} = 1`, `𝒞^{(2,0)} = 𝒞^{(0,2)} = 0` off the diagonal and `= 1` on the diagonal. -/
theorem ccum_entry_low {C : ℕ → ℝ} (L : EntryLaws C) :
    ccum L.νo 1 0 = 0 ∧ ccum L.νo 0 1 = 0 ∧ ccum L.νo 1 1 = 1 ∧ ccum L.νo 2 0 = 0 ∧
      ccum L.νo 0 2 = 0 ∧ ccum ((L.νd : Measure ℝ).map fun x : ℝ => (x : ℂ)) 1 1 = 1 ∧
      ccum ((L.νd : Measure ℝ).map fun x : ℝ => (x : ℂ)) 2 0 = 1 ∧
      ccum ((L.νd : Measure ℝ).map fun x : ℝ => (x : ℂ)) 0 2 = 1 := by
  set μd := (L.νd : Measure ℝ).map fun x : ℝ => (x : ℂ)
  obtain ⟨o10, o01, o11, o20, o02⟩ := Cumulant_low (L.νo : Measure ℂ)
  obtain ⟨-, -, d11, d20, d02⟩ := Cumulant_low μd
  have hmo : ∫ z, z ∂(L.νo : Measure ℂ) = 0 := L.meano
  have hmoc : ∫ z, starRingEnd ℂ z ∂(L.νo : Measure ℂ) = 0 := by
    rw [integral_conj, L.meano, map_zero]
  have hvo : ∫ z, z * starRingEnd ℂ z ∂(L.νo : Measure ℂ) = 1 := by
    have : (fun z : ℂ => z * starRingEnd ℂ z) = fun z => ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      funext z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, integral_complex_ofReal, L.varo]
    simp
  have hpoc : ∫ z, starRingEnd ℂ z ^ 2 ∂(L.νo : Measure ℂ) = 0 := by
    simp_rw [← map_pow]
    rw [integral_conj, L.pseudo, map_zero]
  have hmap : ∀ f : ℂ → ℂ, Continuous f →
      ∫ z, f z ∂μd = ∫ x, f (x : ℂ) ∂(L.νd : Measure ℝ) := fun f hf =>
    integral_map Complex.continuous_ofReal.aemeasurable hf.aestronglyMeasurable
  have hd1 : ∫ z, z ∂μd = 0 := by
    rw [hmap (fun z => z) continuous_id, integral_complex_ofReal, L.meand]
    simp
  have hd1c : ∫ z, starRingEnd ℂ z ∂μd = 0 := by
    rw [hmap _ Complex.continuous_conj]
    simp only [Complex.conj_ofReal]
    rw [integral_complex_ofReal, L.meand]
    simp
  have hd2 : ∀ f : ℂ → ℂ, Continuous f → (∀ x : ℝ, f x = ((x ^ 2 : ℝ) : ℂ)) →
      ∫ z, f z ∂μd = 1 := by
    intro f hf hfx
    rw [hmap f hf]
    simp only [hfx]
    rw [integral_complex_ofReal, L.vard]
    simp
  have hd11 := hd2 (fun z => z * starRingEnd ℂ z) (continuous_id.mul Complex.continuous_conj)
    (fun x => by simp [Complex.conj_ofReal, sq])
  have hd20 := hd2 (fun z => z ^ 2) (continuous_pow 2) (fun x => by simp)
  have hd02 := hd2 (fun z => starRingEnd ℂ z ^ 2) (Complex.continuous_conj.pow 2)
    (fun x => by simp [Complex.conj_ofReal])
  refine ⟨by rw [o10, hmo], by rw [o01, hmoc], by rw [o11, hvo, hmoc, hmo]; ring,
    by rw [o20, L.pseudo, hmo]; ring, by rw [o02, hpoc, hmoc]; ring,
    by rw [d11, hd11, hd1c, hd1]; ring, by rw [d20, hd20, hd1]; ring,
    by rw [d02, hd02, hd1c]; ring⟩

/-- (2.27) [eq:bdd_cumu] in scaled form: every `(p, q)`-cumulant of a scaled entry is bounded by a
constant depending only on `p`, `q` and the moment constants `C`. -/
theorem ccum_entry_le (C : ℕ → ℝ) (p q : ℕ) :
    ∃ K : ℝ, ∀ L : EntryLaws C, ‖ccum L.νo p q‖ ≤ K ∧
      ‖ccum ((L.νd : Measure ℝ).map fun x : ℝ => (x : ℂ)) p q‖ ≤ K := by
  refine ⟨∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
    ((π.parts.card - 1).factorial : ℝ) * ∏ B ∈ π.parts, C B.card, fun L => ⟨?_, ?_⟩⟩
  · rw [Cumulant_ccum_eq]
    refine Cumulant_norm_K_le _ _ _ fun B => ?_
    unfold Cumulant_mom
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Cumulant_norm_prod_typ]
    have h1 := L.moments B.card
    have h0 : 0 ≤ ∫ x, |x| ^ B.card ∂(L.νd : Measure ℝ) :=
      integral_nonneg fun x => by positivity
    linarith
  · rw [Cumulant_ccum_eq]
    refine Cumulant_norm_K_le _ _ _ fun B => ?_
    unfold Cumulant_mom
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Cumulant_norm_prod_typ]
    rw [integral_map (φ := fun x : ℝ => (x : ℂ)) (f := fun z : ℂ => ‖z‖ ^ B.card)
      Complex.continuous_ofReal.aemeasurable (continuous_norm.pow _).aestronglyMeasurable]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have h1 := L.moments B.card
    have h0 : 0 ≤ ∫ z, ‖z‖ ^ B.card ∂(L.νo : Measure ℂ) :=
      integral_nonneg fun z => by positivity
    linarith

end RBMTransitionEdge

end
