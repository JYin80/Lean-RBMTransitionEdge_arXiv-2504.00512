module

public import RBMTransitionEdge.Localized.Expansion.FSharp
public import RBMTransitionEdge.Localized.Expansion.FRule
public import RBMTransitionEdge.Localized.Expansion.Rem2Expand
public import RBMTransitionEdge.LocalLaw.CumulantClass

@[expose] public section

/-!
# The bridges from the rules to the remainders and the leaves

In the proof of Lemma 5.5 [claim_estimate_remainder_terms]: if every derivative structure of
`𝓔^{(2)}_𝓡(p, q)` has an assignment that passes the rows (`FRuleOK`, the conclusion of the rule
lemmas), the signed sum over the four starting loops of (5.29) [expansion_of_im] of
`𝓔^{(2)}(p, q)` inside the cumulant sum is at most `N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` at
the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law]; and the same for the further terminal cases (i)–(iii)
from an assignment with the prefactor of a leaf.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### The factor list of the rules at the four flags -/

/-- The factor list of the rules (`PkgExpr.rfacs`) with the resolvent flags `s`: `ffacs` with the
pairing `fpm` through `𝔐`, and every resolvent of a slot paired through `𝒢` doubled
(`𝒢 𝒢ᴴ`, (5.29) [expansion_of_im]). -/
private def RB_F (R : PkgExpr) (s : Fin 2 → Bool) : List FFac :=
  (R.ffacs s R.fpm).map fun f => if R.fpg 0 then f.dupRes 0 else if R.fpg 1 then f.dupRes 1 else f

/-- At the flags `false` it is `rfacs`. -/
private lemma RB_F_false (R : PkgExpr) : RB_F R (fun _ => false) = R.rfacs := rfl

/-- Doubling the resolvents of a slot commutes with dropping the flags. -/
private lemma RB_uf_dup (a' : Fin 2) (f : FFac) :
    (f.dupRes a').unflag = (f.unflag.dupRes a').unflag := by
  have hl : ∀ w : List FLet, (w.flatMap (FLet.dupRes a')).map
      (fun z => match z with | .res a _ => FLet.res a false | z => z) =
      ((w.map fun z => match z with | .res a _ => FLet.res a false | z => z).flatMap
        (FLet.dupRes a')).map (fun z => match z with | .res a _ => FLet.res a false | z => z) := by
    intro w
    induction w with
    | nil => rfl
    | cons z w ih =>
      simp only [List.flatMap_cons, List.map_cons, List.map_append, ih]
      congr 1
      cases z with
      | res a f => by_cases ha : a = a' <;> simp [FLet.dupRes, ha]
      | _ => rfl
  cases f with
  | ent x y w => exact congrArg (FFac.ent x y) (hl w)
  | loop w => exact congrArg FFac.loop (hl w)
  | wt a x => rfl

/-- Dropping the flags twice is dropping them once. -/
private lemma RB_uf_uf (f : FFac) : f.unflag.unflag = f.unflag := by
  cases f with
  | ent x y w =>
    simp only [FFac.unflag, List.map_map]
    congr 1
    refine List.map_congr_left fun z _ => ?_
    cases z <;> rfl
  | loop w =>
    simp only [FFac.unflag, List.map_map]
    congr 1
    refine List.map_congr_left fun z _ => ?_
    cases z <;> rfl
  | wt a x => rfl

/-- The factor lists at the four flags agree with `rfacs` up to the flags. -/
private lemma RB_F_unflag (R : PkgExpr) (s : Fin 2 → Bool) :
    (RB_F R s).map FFac.unflag = R.rfacs.map FFac.unflag := by
  rw [← RB_F_false]
  unfold RB_F
  have key : ∀ L L' : List FFac, L.map FFac.unflag = L'.map FFac.unflag →
      ∀ φ : FFac → FFac, (∀ f, (φ f).unflag = (φ f.unflag).unflag) →
      (L.map φ).map FFac.unflag = (L'.map φ).map FFac.unflag := by
    intro L L' h φ hφ
    have e : ∀ M : List FFac, (M.map φ).map FFac.unflag =
        (M.map FFac.unflag).map (fun f => (φ f).unflag) := by
      intro M
      simp only [List.map_map]
      exact List.map_congr_left fun f _ => hφ f
    rw [e, e, h]
  refine key _ _ (ffacs_unflag R s _ R.fpm) _ fun f => ?_
  split_ifs
  · exact RB_uf_dup 0 f
  · exact RB_uf_dup 1 f
  · exact (RB_uf_uf f).symm

/-- An assignment valid for `rfacs` is valid at every flag, with the same bound (`fvalid` and
`fboundM` do not see the flags). -/
private lemma RB_valid (R : PkgExpr) (g : FAsg) (hg : fvalid R.nb R.rfacs g = true)
    (s : Fin 2 → Bool) :
    fvalid R.nb (RB_F R s) g = true ∧ fboundM (RB_F R s) g = fboundM R.rfacs g := by
  obtain ⟨h1, h2⟩ := fvalid_unflag R.nb (RB_F R s) R.rfacs (RB_F_unflag R s) g
  exact ⟨h1 ▸ hg, h2⟩

/-- Under a valid assignment the entry labels are below `4`, so a factor takes the same value at
labels that agree below `4`. -/
private lemma RB_val_lab {D N : ℕ} (nb : ℕ) (F : List FFac) (g : FAsg) (hg : fvalid nb F g = true)
    (e : LoopEnv D N) {nb' : ℕ} (ι : Fin nb' → Fin D) (κ κ' : ℕ → Idx D N)
    (hκ : ∀ l : ℕ, l < 4 → κ l = κ' l) (h : Idx D N → Idx D N → ℂ) :
    F.map (FFac.val e ι κ h) = F.map (FFac.val e ι κ' h) := by
  unfold fvalid at hg
  simp only [Bool.and_eq_true, List.all_eq_true] at hg
  have hF := hg.1.1.2
  refine List.map_congr_left fun f hf => ?_
  have := hF f hf
  cases f with
  | ent x y w =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [FFac.val, hκ x this.1.1, hκ y this.1.2]
  | loop w => rfl
  | wt a x => rfl

/-- The value of an expression depends on the entry labels only through the labels of its
letters `Δ`. -/
private lemma RB_evalH_lab {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ κ' : ℕ → Idx D N)
    (hκ : ∀ w ∈ R.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → κ u = κ' u ∧ κ v = κ' v)
    (h : Idx D N → Idx D N → ℂ) : R.evalH e κ h = R.evalH e κ' h := by
  have hw : ∀ ι : Fin R.nb → Fin D, ∀ w ∈ R.loops,
      pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w = pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ' w := by
    intro ι w hwl
    unfold pkgWordMat
    congr 1
    refine List.map_congr_left fun x hx => ?_
    cases x with
    | lw y => rfl
    | ent u v => simp only [(hκ w hwl u v hx).1, (hκ w hwl u v hx).2]
  unfold PkgExpr.evalH
  congr 1
  refine Finset.sum_congr rfl fun ι _ => ?_
  congr 1
  congr 1
  exact List.map_congr_left fun w hwl => by rw [hw ι w hwl]


/-! ### The flags -/

/-- The sign of a flag. -/
private abbrev RB_σ (b : Bool) : ℂ := if b then -1 else 1

/-- The signed sum over the four flags as a sum over the flag `b` of slot `a'` and the flag `c` of
the other slot. -/
private lemma RB_sum_flags (a' : Fin 2) (f : (Fin 2 → Bool) → ℂ) :
    ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * f s =
      ∑ c : Bool, RB_σ c * ∑ b : Bool, RB_σ b * f (Function.update (fun _ => c) a' b) := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  have h0 : ∀ b c : Bool, Function.update (fun _ => c) (0 : Fin 2) b = ![b, c] := by
    intro b c; funext x; fin_cases x <;> simp
  have h1 : ∀ b c : Bool, Function.update (fun _ => c) (1 : Fin 2) b = ![c, b] := by
    intro b c; funext x; fin_cases x <;> simp
  fin_cases a' <;> simp [h0, h1, finTwoArrowEquiv_symm_apply] <;> ring

/-- A slot paired through `𝔐` enters only through one letter `𝔐`. -/
private lemma RB_onlyDet {R : PkgExpr} {a : Fin 2} (h : R.fpm a = true) : R.onlyDet a = true := by
  unfold PkgExpr.fpm at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- A slot paired through `𝒢` enters only through one resolvent. -/
private lemma RB_onlyRes {R : PkgExpr} {a : Fin 2} (h : R.fpg a = true) : R.onlyRes a = true := by
  unfold PkgExpr.fpg at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- At most one slot is paired through `𝔐`. -/
private lemma RB_fpm_eq {R : PkgExpr} {a' : Fin 2} (h : R.fpm a' = true) :
    R.fpm = fun a => decide (a = a') := by
  have h01 : R.fpm 0 = true → R.fpm 1 = false := by
    intro h0
    unfold PkgExpr.fpm at h0
    simp only [Bool.and_eq_true] at h0
    unfold PkgExpr.fpm
    rw [h0.1.1, h0.1.2]
    simp
  funext a
  fin_cases a' <;> fin_cases a
  · simpa using h
  · simpa using h01 h
  · have : R.fpm 0 = false := by
      cases h1 : R.fpm 0
      · rfl
      · simp [h01 h1] at h
    simpa using this
  · simpa using h

/-- At most one slot is paired through `𝒢`. -/
private lemma RB_fpg_eq {R : PkgExpr} {a' : Fin 2} (h : R.fpg a' = true) :
    R.fpg = fun a => decide (a = a') := by
  have h01 : R.fpg 0 = true → R.fpg 1 = false := by
    intro h0
    unfold PkgExpr.fpg at h0
    simp only [Bool.and_eq_true] at h0
    unfold PkgExpr.fpg
    rw [h0.1]
    simp
  funext a
  fin_cases a' <;> fin_cases a
  · simpa using h
  · simpa using h01 h
  · have : R.fpg 0 = false := by
      cases h1 : R.fpg 0
      · rfl
      · simp [h01 h1] at h
    simpa using this
  · simpa using h

/-- A slot is not paired both through `𝔐` and through `𝒢`. -/
private lemma RB_fpm_fpg {R : PkgExpr} {a : Fin 2} (hm : R.fpm a = true) (hg : R.fpg a = true) :
    False := by
  have h1 := RB_onlyDet hm
  have h2 := RB_onlyRes hg
  unfold PkgExpr.onlyDet at h1
  unfold PkgExpr.onlyRes at h2
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at h1 h2
  have : (R.loops.map fun w => w.count (.lw (.res a))).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact List.count_eq_zero.2 (h1.1.2 w hw)
  omega

/-- The value of an expression at the flags `s` through the factor list of the rules. -/
private def RB_V {D N : ℕ} (R : PkgExpr) (e₀ : LoopEnv D N) (κ : ℕ → Idx D N) (s : Fin 2 → Bool)
    (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) * ∑ ι : Fin R.nb → Fin D,
    ((RB_F R s).map (FFac.val { e₀ with s := s } ι κ h)).prod

/-- The signed sum of (5.29) [expansion_of_im] at a Hermitian array: with the pairings through `𝔐`
((5.58) [eq:polar2]) and through `𝒢` (`𝒢 - 𝒢ᴴ = 2 i η 𝒢 𝒢ᴴ`, (5.29)), the signed sum over the
four flags of the value of `R` is a combination of at most four values through the factor list of
the rules, with coefficients of size at most `2 η` for a pairing through `𝒢` and `1` otherwise. -/
private lemma RB_flags {D N : ℕ} (R : PkgExpr) (e₀ : LoopEnv D N) (η : ℝ)
    (hη : ∀ a, (e₀.z a).im = η) (hη0 : 0 < η) (κ : ℕ → Idx D N) :
    ∃ w : Fin 4 → ℂ, ∃ σ : Fin 4 → Fin 2 → Bool,
      (∀ j, ‖w j‖ ≤ 2 * (if R.fpg 0 || R.fpg 1 then η else 1)) ∧
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.evalH { e₀ with s := s } κ h =
          ∑ j, w j * RB_V R e₀ κ (σ j) h := by
  have hz : ∀ s : Fin 2 → Bool, ∀ a, 0 < (({ e₀ with s := s } : LoopEnv D N).z a).im :=
    fun s a => (hη a) ▸ hη0
  have hz' : ∀ s : Fin 2 → Bool, ∀ a, (({ e₀ with s := s } : LoopEnv D N).z a).im ≠ 0 :=
    fun s a => (hz s a).ne'
  have hσn : ∀ b, ‖RB_σ b‖ = 1 := fun b => by cases b <;> simp [RB_σ]
  by_cases hm : ∃ a', R.fpm a' = true
  · obtain ⟨a', ha'⟩ := hm
    have hpm := RB_fpm_eq ha'
    by_cases hg : ∃ b', R.fpg b' = true
    · -- both pairings, at different slots
      obtain ⟨b', hb'⟩ := hg
      have hpg := RB_fpg_eq hb'
      have hab : a' ≠ b' := by
        rintro rfl
        exact RB_fpm_fpg ha' hb'
      have hF : ∀ s, RB_F R s = (R.ffacs s R.fpm).map (FFac.dupRes b') := by
        intro s
        unfold RB_F
        rw [hpg]
        fin_cases b' <;> simp
      have hupd : ∀ c : Bool, Function.update (fun _ => c) a' false =
          Function.update (fun _ => false) b' c := by
        intro c
        funext x
        fin_cases a' <;> fin_cases b' <;> fin_cases x <;> simp_all
      refine ⟨![2 * Complex.I * (η : ℂ), 0, 0, 0], fun _ => fun _ => false, ?_, ?_⟩
      · have : (R.fpg 0 || R.fpg 1) = true := by
          rw [hpg]; fin_cases b' <;> simp
        intro j
        fin_cases j <;> simp [this, abs_of_pos hη0, hη0.le]
      · intro h hh
        rw [RB_sum_flags a']
        have e1 : ∀ c : Bool, ∑ b : Bool, RB_σ b *
            R.evalH { e₀ with s := Function.update (fun _ => c) a' b } κ h =
            R.evalP { e₀ with s := Function.update (fun _ => false) b' c }
              (fun a => decide (a = a')) κ h := by
          intro c
          rw [← hupd c]
          exact pkg_pair_ident R a' (RB_onlyDet ha') { e₀ with s := fun _ => c }
            (hz' _ a') κ h
        simp only [e1]
        have e2 : ∑ c : Bool, RB_σ c *
            R.evalP { e₀ with s := Function.update (fun _ => false) b' c }
              (fun a => decide (a = a')) κ h =
            2 * Complex.I * ((e₀.z b').im : ℂ) * ((R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) *
              ∑ ι : Fin R.nb → Fin D, (((R.ffacs (fun _ => false) (fun a => decide (a = a'))).map
                (FFac.dupRes b')).map (FFac.val { e₀ with s := fun _ => false } ι κ h)).prod) :=
          pkg_pairG_ident R b' (RB_onlyRes hb') { e₀ with s := fun _ => false }
            (hz _) (fun a => decide (a = a')) κ h hh
        simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, zero_mul, add_zero]
        refine e2.trans ?_
        rw [hη b', RB_V, hF, hpm]
        simp [Matrix.vecHead, Matrix.vecTail]
    · simp only [not_exists, Bool.not_eq_true] at hg
      have hpg : R.fpg = fun _ => false := funext hg
      have hF : ∀ s, RB_F R s = R.ffacs s R.fpm := by
        intro s
        unfold RB_F
        rw [hpg]
        simp
      refine ⟨![RB_σ false, RB_σ true, 0, 0],
        ![Function.update (fun _ => false) a' false, Function.update (fun _ => true) a' false,
          fun _ => false, fun _ => false], ?_, ?_⟩
      · intro j
        fin_cases j <;> simp [hpg, hσn]
      · intro h hh
        rw [RB_sum_flags a']
        have e1 : ∀ c : Bool, ∑ b : Bool, RB_σ b *
            R.evalH { e₀ with s := Function.update (fun _ => c) a' b } κ h =
            RB_V R e₀ κ (Function.update (fun _ => c) a' false) h := by
          intro c
          refine (pkg_pair_ident R a' (RB_onlyDet ha') { e₀ with s := fun _ => c }
            (hz' _ a') κ h).trans ?_
          rw [pkg_evalP_ffacs _ _ _ (hz _) κ h hh, RB_V, hF, hpm]
        simp only [e1, Fin.sum_univ_four, Fintype.sum_bool]
        simp
        ring
  · simp only [not_exists, Bool.not_eq_true] at hm
    have hpm : R.fpm = fun _ => false := funext hm
    by_cases hg : ∃ b', R.fpg b' = true
    · obtain ⟨b', hb'⟩ := hg
      have hpg := RB_fpg_eq hb'
      have hF : ∀ s, RB_F R s = (R.ffacs s R.fpm).map (FFac.dupRes b') := by
        intro s
        unfold RB_F
        rw [hpg]
        fin_cases b' <;> simp
      refine ⟨![RB_σ false * (2 * Complex.I * (η : ℂ)), RB_σ true * (2 * Complex.I * (η : ℂ)),
        0, 0], ![fun _ => false, fun _ => true, fun _ => false, fun _ => false], ?_, ?_⟩
      · have : (R.fpg 0 || R.fpg 1) = true := by
          rw [hpg]; fin_cases b' <;> simp
        intro j
        fin_cases j <;> simp [this, abs_of_pos hη0, hη0.le]
      · intro h hh
        rw [RB_sum_flags b']
        have e1 : ∀ c : Bool, ∑ b : Bool, RB_σ b *
            R.evalH { e₀ with s := Function.update (fun _ => c) b' b } κ h =
            2 * Complex.I * (η : ℂ) * RB_V R e₀ κ (fun _ => c) h := by
          intro c
          simp only [← pkg_evalP_false]
          refine (pkg_pairG_ident R b' (RB_onlyRes hb') { e₀ with s := fun _ => c }
            (hz _) (fun _ => false) κ h hh).trans ?_
          rw [hη b', RB_V, hF, hpm]
        simp only [e1, Fin.sum_univ_four, Fintype.sum_bool]
        simp
        ring
    · simp only [not_exists, Bool.not_eq_true] at hg
      have hpg : R.fpg = fun _ => false := funext hg
      have hF : ∀ s, RB_F R s = R.ffacs s R.fpm := by
        intro s
        unfold RB_F
        rw [hpg]
        simp
      refine ⟨![1, -1, -1, 1], ![![false, false], ![false, true], ![true, false], ![true, true]],
        ?_, ?_⟩
      · intro j
        fin_cases j <;> simp [hpg]
      · intro h hh
        have e1 : ∀ s : Fin 2 → Bool, R.evalH { e₀ with s := s } κ h = RB_V R e₀ κ s h := by
          intro s
          rw [← pkg_evalP_false, pkg_evalP_ffacs _ _ _ (hz _) κ h hh, RB_V, hF, hpm]
        simp only [e1]
        rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
        simp [Fin.sum_univ_four, finTwoArrowEquiv_symm_apply]
        ring

/-- The signed sum over the four flags of (5.29) [expansion_of_im] of the expectation of the value
of `R` is at most `8`, times `η` for a pairing through `𝒢`, times the coefficient, times the sum
over the flags and the block indices of `|E Π factors|` of the factor list of the rules. -/
private lemma RB_core {D N : ℕ} (R : PkgExpr) (e₀ : LoopEnv D N) (η : ℝ)
    (hη : ∀ a, (e₀.z a).im = η) (hη0 : 0 < η) (C : ℕ → ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (hμ : LLClass D N C 1 μ) (κ : ℕ → Idx D N) :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, R.evalH { e₀ with s := s } κ h ∂μ‖ ≤
      8 * (if R.fpg 0 || R.fpg 1 then η else 1) *
        ‖(R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)‖ *
        ∑ s : Fin 2 → Bool, ∑ ι : Fin R.nb → Fin D,
          ‖∫ h, ((RB_F R s).map (FFac.val { e₀ with s := s } ι κ h)).prod ∂μ‖ := by
  have := hμ.prob
  have hz : ∀ s : Fin 2 → Bool, ∀ a, 0 < (({ e₀ with s := s } : LoopEnv D N).z a).im :=
    fun s a => (hη a) ▸ hη0
  have hz' : ∀ s : Fin 2 → Bool, ∀ a, (({ e₀ with s := s } : LoopEnv D N).z a).im ≠ 0 :=
    fun s a => (hz s a).ne'
  obtain ⟨w, σ, hw, hrep⟩ := RB_flags R e₀ η hη hη0 κ
  set c : ℂ := (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S) with hc
  have hintP : ∀ (s : Fin 2 → Bool) (F : List FFac) (ι : Fin R.nb → Fin D),
      Integrable (fun h => (F.map (FFac.val { e₀ with s := s } ι κ h)).prod) μ :=
    fun s F ι => fb_integrable C μ hμ _ (hz' s) ι κ F
  have hintH : ∀ s : Fin 2 → Bool, Integrable (fun h => R.evalH { e₀ with s := s } κ h) μ := by
    intro s
    refine ((integrable_finsetSum Finset.univ fun ι _ =>
      hintP s (R.ffacs s fun _ => false) ι).const_mul c).congr ?_
    filter_upwards [hμ.herm] with h hh
    rw [← pkg_evalP_false, pkg_evalP_ffacs _ _ _ (hz s) κ h hh]
  have e1 : ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
      ∫ h, R.evalH { e₀ with s := s } κ h ∂μ =
      ∑ j, w j * (c * ∑ ι : Fin R.nb → Fin D,
        ∫ h, ((RB_F R (σ j)).map (FFac.val { e₀ with s := σ j } ι κ h)).prod ∂μ) := by
    calc _ = ∫ h, ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
          R.evalH { e₀ with s := s } κ h ∂μ := by
          rw [integral_finsetSum _ fun s _ => (hintH s).const_mul _]
          simp only [integral_const_mul]
      _ = ∫ h, ∑ j, w j * RB_V R e₀ κ (σ j) h ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hμ.herm] with h hh
          exact hrep h hh
      _ = _ := by
          rw [integral_finsetSum _ fun j _ => ?_]
          · simp only [integral_const_mul, RB_V]
            congr 1
            funext j
            rw [integral_finsetSum _ fun ι _ => hintP _ _ ι]
          · exact ((integrable_finsetSum Finset.univ fun ι _ => hintP _ _ ι).const_mul _).const_mul
              _
  rw [e1]
  set G : (Fin 2 → Bool) → ℝ := fun s => ∑ ι : Fin R.nb → Fin D,
    ‖∫ h, ((RB_F R s).map (FFac.val { e₀ with s := s } ι κ h)).prod ∂μ‖ with hG
  have hG0 : ∀ s, 0 ≤ G s := fun s => Finset.sum_nonneg fun ι _ => norm_nonneg _
  have hηf : 0 ≤ 2 * (if R.fpg 0 || R.fpg 1 then η else 1) := by
    split_ifs <;> positivity
  calc _ ≤ ∑ j, ‖w j‖ * (‖c‖ * G (σ j)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, norm_mul]
        gcongr
        exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 4, 2 * (if R.fpg 0 || R.fpg 1 then η else 1) * (‖c‖ * ∑ s, G s) := by
        refine Finset.sum_le_sum fun j _ => ?_
        gcongr
        · exact hw j
        · exact Finset.single_le_sum (fun s _ => hG0 s) (Finset.mem_univ _)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The engine with the rule -/

/-- The label sum `Σ_κ Σ_ι |E Π factors|` of the factor list of the rules at the four flags, at
the labels of the engine, times `8`, the factor `η` of a pairing through `𝒢` and the
coefficient. -/
private def RB_X {D N : ℕ} (R : PkgExpr) (e₀ : LoopEnv D N)
    (μ : Measure (Idx D N → Idx D N → ℂ)) (η : ℝ) : ℝ :=
  8 * (if R.fpg 0 || R.fpg 1 then η else 1) *
    ‖(R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)‖ *
    ∑ s : Fin 2 → Bool, ∑ κ : Fin 4 → Idx D N,
      if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
        ∑ ι : Fin R.nb → Fin D, ‖∫ h, ((RB_F R s).map (FFac.val { e₀ with s := s } ι
          (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖
      else 0

/-- `η = etaK` is positive and at most `1`, and `Im m ≤ M = N^{-1/3+ε/2} 𝔯(k)^{1/3}` is positive. -/
private lemma RB_eta {D N k : ℕ} (ε : ℝ) (hε'' : ε ≤ 1 / 3) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hkN : 2 * k ≤ D * N + 1) :
    0 < etaK D N k ε ∧ etaK D N k ε ≤ 1 ∧
      0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) ∧ 1 ≤ rk D N k := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrk : (1 : ℝ) ≤ rk D N k := by
    unfold rk
    exact_mod_cast (le_min hk (by omega))
  refine ⟨?_, ?_, by positivity, hrk⟩
  · unfold etaK; positivity
  · unfold etaK
    exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
      (Real.rpow_le_one_of_one_le_of_nonpos hrk (by norm_num)) (by positivity) zero_le_one).trans
      (by norm_num)

/-- One structure `R` with an assignment that passes the rows (`FRuleOK`) with the prefactor
`N^{pre/2}`, in the proof of Lemma 5.5 [claim_estimate_remainder_terms]: by `pkg_fsharp_bound` at
the four flags and `fmono_ok_row` on every monomial of the bound times the prefactor and `rext`,
the label sum `RB_X` times `N^{(pre + 2S)/2}` is at most `Q (N^{τ'} + 1) N^{2ε} N^{-5/3}
𝔯(k)^{2/3} ‖A‖²_HS`, uniformly in the member of the class, `A`, `k` and the slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law]. -/
private lemma RB_engine (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (R : PkgExpr) (pre : ℤ)
    (g : FAsg) (hok : FRuleOK R pre g) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ τ' : ℝ, 0 < τ' → ∀ᶠ N : ℕ in atTop,
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e₀ : LoopEnv D N, (∀ s : Fin 2 → Bool,
          (∃ s', ({ e₀ with s := s } : LoopEnv D N) = evecEnv D N A k ε s') ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s', ({ e₀ with s := s } : LoopEnv D N) =
            evalEnv D N A k ε t s') →
        (N : ℝ) ^ (((pre + 2 * R.S : ℤ) : ℝ) / 2) * RB_X R e₀ μ (etaK D N k ε) ≤
          Q * ((N : ℝ) ^ τ' + 1) * ((N : ℝ) ^ (2 * ε) *
            ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) := by
  obtain ⟨hv, hm⟩ := hok
  set L := fboundM R.rfacs g with hL
  choose! Cm hCm hrow using fun m (hm' : m ∈ L) =>
    fmono_ok_row D hD εA ε hεA hε hε' hε'' _ (hm m hm')
  have hCs : 0 ≤ (L.map Cm).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hx
      exact (hCm m hm').le
  set D' : ℝ := |(pre : ℝ)| / 2 + 2 with hD'
  refine ⟨32 * |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * ((L.map Cm).sum + 1), by positivity,
    fun τ' hτ' => ?_⟩
  have hE : ∀ s : Fin 2 → Bool, ∀ᶠ N : ℕ in atTop,
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e : LoopEnv D N, ((∃ s, e = evecEnv D N A k ε s) ∨
          ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s, e = evalEnv D N A k ε t s) →
        ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
          ∑ ι : Fin R.nb → Fin D, ‖∫ h, ((RB_F R s).map (FFac.val e ι
            (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0) ≤
        (N : ℝ) ^ τ' * (L.map fun m => m.evalR N
            ((N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ)) (etaK D N k ε)
            (hsNorm A) (opNorm A)).sum + (N : ℝ) ^ (-D') * hsNorm A ^ 2 := by
    intro s
    rw [hL, ← (RB_valid R g hv s).2]
    exact Filter.eventually_atTop.2 (pkg_fsharp_bound D hD δA εA ε hδA hεA hε hε' hε'' C R.nb
      (RB_F R s) g (RB_valid R g hv s).1 D' (by positivity) τ' hτ')
  filter_upwards [Filter.eventually_all.2 hE, Filter.eventually_ge_atTop 1] with N hN hN1
  intro μ hμ A hA k hk hkN hhs e₀ hadm
  obtain ⟨hη0, hη1, hM0, hrk⟩ := RB_eta (D := D) ε hε'' hN1 hk hkN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hA1 : opNorm A ≤ 1 :=
    hA.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  set M := (N : ℝ) ^ (-(1 / 3 : ℝ) + ε / 2) * rk D N k ^ (1 / 3 : ℝ) with hM
  set η := etaK D N k ε with hη
  set T := (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2)
    with hT
  set ηf : ℝ := if R.fpg 0 || R.fpg 1 then η else 1 with hηf
  have hηf0 : 0 ≤ ηf := by rw [hηf]; split_ifs <;> positivity
  have hηf1 : ηf ≤ 1 := by rw [hηf]; split_ifs <;> linarith
  have hhs0 : 0 ≤ hsNorm A := by unfold hsNorm; positivity
  have hT0 : 0 ≤ T := by positivity
  -- the prefactor and `rext` as monomials
  have hpre : (⟨pre, 0, 0, 0, 0⟩ : FMono).evalR N M η (hsNorm A) (opNorm A) =
      (N : ℝ) ^ ((pre : ℝ) / 2) := by
    simp [FMono.evalR]
  have hext : R.rext.evalR N M η (hsNorm A) (opNorm A) = ηf := by
    rw [hηf]
    unfold PkgExpr.rext
    split_ifs <;> simp [FMono.evalR]
  -- (k1): every monomial times the prefactor and `rext`
  have k1 : ∀ m ∈ L, (N : ℝ) ^ ((pre : ℝ) / 2) * ηf *
      m.evalR N M η (hsNorm A) (opNorm A) ≤ Cm m * T := by
    intro m hm'
    have := hrow m hm' N hN1 A hA1 k hk hkN hhs
    rw [fmono_evalR_mul _ _ N hN1 M η _ _ hM0 hη0, fmono_evalR_mul _ _ N hN1 M η _ _ hM0 hη0,
      hpre, hext] at this
    rw [hT]
    calc _ = m.evalR N M η (hsNorm A) (opNorm A) * (N : ℝ) ^ ((pre : ℝ) / 2) * ηf := by ring
      _ ≤ _ := this
      _ = _ := by ring
  -- (k2): the additive term of the engine
  have k2 : (N : ℝ) ^ ((pre : ℝ) / 2) * ηf * ((N : ℝ) ^ (-D') * hsNorm A ^ 2) ≤ T := by
    have e1 : (N : ℝ) ^ ((pre : ℝ) / 2) * (N : ℝ) ^ (-D') ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) := by
      rw [← Real.rpow_add hN0]
      refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
      rw [hD']
      have := le_abs_self (pre : ℝ)
      linarith
    have e2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * ε) * rk D N k ^ (2 / 3 : ℝ) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1' (by linarith))
        (Real.one_le_rpow hrk (by norm_num))
    calc _ ≤ (N : ℝ) ^ ((pre : ℝ) / 2) * 1 * ((N : ℝ) ^ (-D') * hsNorm A ^ 2) := by
          gcongr
      _ ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) * hsNorm A ^ 2 := by
          rw [mul_one, ← mul_assoc]
          gcongr
      _ ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) * hsNorm A ^ 2 *
          ((N : ℝ) ^ (2 * ε) * rk D N k ^ (2 / 3 : ℝ)) :=
          le_mul_of_one_le_right (by positivity) e2
      _ = T := by rw [hT]; ring
  -- the four flags
  have hsum : ∑ s : Fin 2 → Bool, ∑ κ : Fin 4 → Idx D N,
      (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
        ∑ ι : Fin R.nb → Fin D, ‖∫ h, ((RB_F R s).map (FFac.val { e₀ with s := s } ι
          (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0) ≤
      4 * ((N : ℝ) ^ τ' * (L.map fun m => m.evalR N M η (hsNorm A) (opNorm A)).sum +
        (N : ℝ) ^ (-D') * hsNorm A ^ 2) := by
    calc _ ≤ ∑ _s : Fin 2 → Bool, ((N : ℝ) ^ τ' *
          (L.map fun m => m.evalR N M η (hsNorm A) (opNorm A)).sum +
          (N : ℝ) ^ (-D') * hsNorm A ^ 2) :=
          Finset.sum_le_sum fun s _ => hN s μ hμ A hA k hk hkN hhs _ (hadm s)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
          Fintype.card_fin, Fintype.card_pi, Finset.prod_const, nsmul_eq_mul]; norm_num
  -- the coefficient
  have hc : (N : ℝ) ^ (((pre + 2 * R.S : ℤ) : ℝ) / 2) *
      ‖(R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)‖ =
      |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * (N : ℝ) ^ ((pre : ℝ) / 2) := by
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_intCast, ← Real.rpow_intCast (N : ℝ) (-R.S)]
    have : (N : ℝ) ^ (((pre + 2 * R.S : ℤ) : ℝ) / 2) * (N : ℝ) ^ (((-R.S : ℤ) : ℝ)) =
        (N : ℝ) ^ ((pre : ℝ) / 2) := by
      rw [← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    rw [← this]
    ring
  have hBs : (N : ℝ) ^ ((pre : ℝ) / 2) * ηf *
      (L.map fun m => m.evalR N M η (hsNorm A) (opNorm A)).sum ≤ (L.map Cm).sum * T := by
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
    exact List.sum_le_sum fun m hm' => k1 m hm'
  have hτ0 : 0 ≤ (N : ℝ) ^ τ' := by positivity
  calc (N : ℝ) ^ (((pre + 2 * R.S : ℤ) : ℝ) / 2) * RB_X R e₀ μ η
      = 8 * (|(R.cf : ℝ)| * (D : ℝ) ^ R.dexp) * ((N : ℝ) ^ ((pre : ℝ) / 2) * ηf *
          ∑ s : Fin 2 → Bool, ∑ κ : Fin 4 → Idx D N,
            (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
              ∑ ι : Fin R.nb → Fin D, ‖∫ h, ((RB_F R s).map (FFac.val { e₀ with s := s } ι
                (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0)) := by
        rw [RB_X, ← hηf]
        rw [show ∀ x y z w : ℝ, x * (8 * y * z * w) = 8 * (x * z) * y * w by intros; ring, hc]
        ring
    _ ≤ 8 * (|(R.cf : ℝ)| * (D : ℝ) ^ R.dexp) * ((N : ℝ) ^ ((pre : ℝ) / 2) * ηf *
          (4 * ((N : ℝ) ^ τ' * (L.map fun m => m.evalR N M η (hsNorm A) (opNorm A)).sum +
            (N : ℝ) ^ (-D') * hsNorm A ^ 2))) := by
        gcongr
    _ = 32 * (|(R.cf : ℝ)| * (D : ℝ) ^ R.dexp) * ((N : ℝ) ^ τ' * ((N : ℝ) ^ ((pre : ℝ) / 2) * ηf *
          (L.map fun m => m.evalR N M η (hsNorm A) (opNorm A)).sum) +
          (N : ℝ) ^ ((pre : ℝ) / 2) * ηf * ((N : ℝ) ^ (-D') * hsNorm A ^ 2)) := by ring
    _ ≤ 32 * (|(R.cf : ℝ)| * (D : ℝ) ^ R.dexp) * ((N : ℝ) ^ τ' * ((L.map Cm).sum * T) + T) := by
        gcongr
    _ ≤ 32 * |(R.cf : ℝ)| * (D : ℝ) ^ R.dexp * ((L.map Cm).sum + 1) * ((N : ℝ) ^ τ' + 1) * T := by
        have : (N : ℝ) ^ τ' * ((L.map Cm).sum * T) + T ≤
            ((L.map Cm).sum + 1) * ((N : ℝ) ^ τ' + 1) * T := by
          nlinarith [mul_nonneg hτ0 hT0, mul_nonneg hCs hT0]
        calc _ ≤ 32 * (|(R.cf : ℝ)| * (D : ℝ) ^ R.dexp) *
              (((L.map Cm).sum + 1) * ((N : ℝ) ^ τ' + 1) * T) := by gcongr
          _ = _ := by ring

/-! ### Sums over the labels -/

/-- The signed sum over the flags passes inside a sum. -/
private lemma RB_L1 {ι : Type*} [Fintype ι] (w : (Fin 2 → Bool) → ℂ)
    (f : (Fin 2 → Bool) → ι → ℂ) :
    ∑ s : Fin 2 → Bool, w s * ∑ x, f s x = ∑ x, ∑ s : Fin 2 → Bool, w s * f s x := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- The signed sum over the flags passes inside an `if`. -/
private lemma RB_L2 (w : (Fin 2 → Bool) → ℂ) (P : Prop) [Decidable P]
    (f : (Fin 2 → Bool) → ℂ) :
    ∑ s : Fin 2 → Bool, w s * (if P then f s else 0) =
      if P then ∑ s : Fin 2 → Bool, w s * f s else 0 := by
  split_ifs <;> simp

/-- The signed sum over the flags passes a constant factor. -/
private lemma RB_L3 (w : (Fin 2 → Bool) → ℂ) (k : ℂ) (f : (Fin 2 → Bool) → ℂ) :
    ∑ s : Fin 2 → Bool, w s * (k * f s) = k * ∑ s : Fin 2 → Bool, w s * f s := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The signed sum over the flags passes inside a sum over a list. -/
private lemma RB_L4 {α : Type*} (w : (Fin 2 → Bool) → ℂ) (L : List α)
    (f : (Fin 2 → Bool) → α → ℂ) :
    ∑ s : Fin 2 → Bool, w s * (L.map (f s)).sum =
      (L.map fun x => ∑ s : Fin 2 → Bool, w s * f s x).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

/-- A sum over four labels as a sum over the maps `Fin 4 → Idx D N`. -/
private lemma RB_sum_pi4 {β : Type*} [Fintype β] (g : β → β → β → β → ℝ) :
    ∑ κ : Fin 4 → β, g (κ 0) (κ 1) (κ 2) (κ 3) = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  simp only [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  rfl

/-- The number of pairs of indices in one block is `D N²`. -/
private lemma RB_count (D N : ℕ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = D * N ^ 2 := by
  have h : ∀ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = N := by
    intro i
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- The cumulant factor of `outer` and `rem2PQ` is at most `|K| N^{-(p+q+1)/2}`, with `K` of
(2.27) [eq:bdd_cumu] (`llClass_ccum_le`). -/
private lemma RB_cum {D N : ℕ} (C : ℕ → ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C 1 μ) (p q : ℕ) (K : ℝ)
    (hK : ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)), LLClass D N C θ μ →
      ∀ i j : Idx D N,
        ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤ K * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)))
    (i j : Idx D N) :
    ‖ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q)‖ ≤
      |K| * (N : ℝ) ^ (-(((p + q + 1 : ℕ) : ℝ) / 2)) := by
  have h1 : ‖(if i = j then (1 / 2 : ℂ) else 1) ^ (p + q)‖ ≤ 1 := by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    split_ifs <;> norm_num
  have h2 : (1 : ℝ) ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _))
  have h3 := hK D N 1 μ hμ i j
  rw [show p + (q + 1) = p + q + 1 by omega] at h3
  rw [norm_mul, norm_div]
  calc _ ≤ ‖ccum (μ.map fun h => h i j) p (q + 1)‖ / 1 * 1 := by
        gcongr
    _ ≤ _ := by
        rw [div_one, mul_one]
        exact h3.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))

/-- A sum over the labels of an `if` of a sum over a list, as a sum over the list. -/
private lemma RB_L5 {ι α : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] (L : List α)
    (f : ι → α → ℝ) :
    ∑ κ, (if P κ then (L.map (f κ)).sum else 0) =
      (L.map fun x => ∑ κ, (if P κ then f κ x else 0)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun κ _ => ?_
    split_ifs <;> simp

/-- The triangle inequality for a sum over a list. -/
private lemma RB_norm_list (l : List PkgExpr) (f : PkgExpr → ℂ) :
    ‖(l.map f).sum‖ ≤ (l.map fun x => ‖f x‖).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The norm of the cumulant sums of `outer2` around the signed sums, with the cumulant factors
bounded by `B₀` and `B₁`, as one sum over the four labels. -/
private lemma RB_norm_nest {D N : ℕ} (a : ℂ) (c₀ c : Idx D N → Idx D N → ℂ) (B₀ B₁ : ℝ)
    (hB₀' : 0 ≤ B₀) (hB₀ : ∀ α β, ‖c₀ α β‖ ≤ B₀) (hB₁ : ∀ i j, ‖c i j‖ ≤ B₁)
    (L : List PkgExpr) (Z : Idx D N → Idx D N → Idx D N → Idx D N → PkgExpr → ℂ) :
    ‖a * ∑ α : Idx D N, ∑ β : Idx D N, (if α.1 = β.1 then c₀ α β * ∑ i : Idx D N,
        ∑ j : Idx D N, (if i.1 = j.1 then c i j * (L.map (Z α β i j)).sum else 0) else 0)‖ ≤
      ‖a‖ * (B₀ * B₁) * ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
        (L.map fun R' => ‖Z (κ 0) (κ 1) (κ 2) (κ 3) R'‖).sum else 0) := by
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [RB_sum_pi4 (fun a b c d => if a.1 = b.1 ∧ c.1 = d.1 then
    (L.map fun R' => ‖Z a b c d R'‖).sum else 0)]
  have hX : ∀ α β i j, 0 ≤ (L.map fun R' => ‖Z α β i j R'‖).sum := fun α β i j =>
    List.sum_nonneg fun x hx => by
      obtain ⟨R', -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  calc _ ≤ ∑ α : Idx D N, ∑ β : Idx D N, (B₀ * B₁) * ∑ i : Idx D N, ∑ j : Idx D N,
        (if α.1 = β.1 ∧ i.1 = j.1 then (L.map fun R' => ‖Z α β i j R'‖).sum else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_))
        by_cases hαβ : α.1 = β.1
        · simp only [hαβ, ite_true, true_and, norm_mul]
          calc _ ≤ B₀ * ∑ i : Idx D N, ∑ j : Idx D N,
                ‖(if i.1 = j.1 then c i j * (L.map (Z α β i j)).sum else 0)‖ := by
                gcongr
                · exact hB₀ α β
                · exact (norm_sum_le _ _).trans
                    (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
            _ ≤ _ := by
                rw [mul_assoc]
                gcongr
                rw [Finset.mul_sum]
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_le_sum fun j _ => ?_
                split_ifs
                · rw [norm_mul]
                  exact mul_le_mul (hB₁ i j) (RB_norm_list _ _) (norm_nonneg _)
                    ((norm_nonneg _).trans (hB₁ i j))
                · simp
        · simp [hαβ]
    _ = _ := by simp only [Finset.mul_sum]

/-- The admissible slots: every flag of `e₀` gives the slots of Lemma 5.2 or of Lemma 5.4. -/
private def RB_adm {D N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ) (e₀ : LoopEnv D N) :
    Prop :=
  ∀ s : Fin 2 → Bool, (∃ s', ({ e₀ with s := s } : LoopEnv D N) = evecEnv D N A k ε s') ∨
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s', ({ e₀ with s := s } : LoopEnv D N) = evalEnv D N A k ε t s'

/-- `N^{τ/2}` absorbs a constant: `K (N^{τ/2} + 1) ≤ N^τ` once `N^{τ/2} ≥ 2K + 1`. -/
private lemma RB_absorb {N : ℕ} (hN : 1 ≤ N) {τ K : ℝ} (hK : 0 ≤ K)
    (hNK : 2 * K + 1 ≤ (N : ℝ) ^ (τ / 2)) : K * ((N : ℝ) ^ (τ / 2) + 1) ≤ (N : ℝ) ^ τ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  rw [hsq]
  nlinarith

/-- (5.29) [expansion_of_im], (5.83) [concrete_expansion_tl_2_heavy_package_right] and (5.84)
[concrete_expansion_tl_2_loop] in the proof of Lemma 5.5 [claim_estimate_remainder_terms]: the
bridge from the rules to the remainders at slots `{e₀ with s := s}` that are admissible for every
flag. -/
private lemma RB_rem2 (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (R : PkgExpr) (p₀ q₀ : ℕ)
    (hpq : p₀ + q₀ = 2) (p q : ℕ)
    (hrule : ∀ R' ∈ R.fpkg.dwirt 2 3 p q, ∃ g : FAsg,
      FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) g) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ N : ℕ in atTop,
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e₀ : LoopEnv D N, RB_adm A k ε e₀ →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer2 { e₀ with s := s } μ p₀ q₀ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  intro τ hτ
  set L := R.fpkg.dwirt 2 3 p q with hL
  have : Nonempty FAsg := ⟨⟨[], []⟩⟩
  choose! G hG using hrule
  choose! Q hQ0 hQ using fun R' (hR' : R' ∈ L) =>
    RB_engine D hD δA εA ε hδA hεA hε hε' hε'' C R' _ (G R') (hG R' hR')
  obtain ⟨K₀, hK₀⟩ := llClass_ccum_le C p₀ (q₀ + 1)
  obtain ⟨K₁, hK₁⟩ := llClass_ccum_le C p (q + 1)
  obtain ⟨CU, -, Nη, hNη⟩ := pkg_slot_im D hD δA εA ε hδA hεA hε hε' hε''
  have hQs : 0 ≤ (L.map Q).sum := List.sum_nonneg fun x hx => by
    obtain ⟨R', hR', rfl⟩ := List.mem_map.1 hx
    exact hQ0 R' hR'
  set Kt : ℝ := (D : ℝ)⁻¹ * (|K₀| * |K₁|) * (L.map Q).sum with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  have hpow : ∀ᶠ N : ℕ in atTop, 2 * Kt + 1 ≤ (N : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hEall := (Filter.eventually_all_finite (List.finite_toSet L)).2
    fun R' (hR' : R' ∈ L) => hQ R' hR' (τ / 2) (by linarith)
  filter_upwards [hEall, hpow, Filter.eventually_ge_atTop (max Nη 1)] with N hNE hNp hN
  intro μ hμ A hA k hk hkN hhs e₀ hadm
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hη0, -, -, -⟩ := RB_eta (D := D) ε hε'' hN1 hk hkN
  set η := etaK D N k ε with hη
  have hzη : ∀ a, (e₀.z a).im = η := fun a =>
    (hNη N (le_trans (le_max_left _ _) hN) A hA k hk hkN hhs _ (hadm fun _ => false) a).1
  have hz' : ∀ (s : Fin 2 → Bool) a, (({ e₀ with s := s } : LoopEnv D N).z a).im ≠ 0 :=
    fun s a => by rw [show (({ e₀ with s := s } : LoopEnv D N).z a) = e₀.z a from rfl, hzη a]
                  exact hη0.ne'
  -- `pkg_rem2_expand`, with the signed sum passed inside the cumulant sums
  set c₀ : Idx D N → Idx D N → ℂ := fun α β => ccum (μ.map fun h => h α β) p₀ (q₀ + 1) /
    ((p₀.factorial * q₀.factorial : ℕ) : ℂ) * (if α = β then (1 / 2 : ℂ) else 1) ^ (p₀ + q₀)
    with hc₀
  set c : Idx D N → Idx D N → ℂ := fun i j => ccum (μ.map fun h => h i j) p (q + 1) /
    ((p.factorial * q.factorial : ℕ) : ℂ) * (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) with hc
  set Z : Idx D N → Idx D N → Idx D N → Idx D N → PkgExpr → ℂ := fun α β i j R' =>
    ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
      ∫ h, R'.evalH { e₀ with s := s }
        (fun l => if l = 2 then i else if l = 3 then j else if l = 0 then α else β) h ∂μ with hZ
  have eq1 : ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
      R.outer2 { e₀ with s := s } μ p₀ q₀ p q =
      -((D : ℂ) * N)⁻¹ * ∑ α : Idx D N, ∑ β : Idx D N, (if α.1 = β.1 then c₀ α β *
        ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then c i j * (L.map (Z α β i j)).sum
          else 0) else 0) := by
    have hexp := fun (s : Fin 2 → Bool) (κ : ℕ → Idx D N) =>
      pkg_rem2_expand D N C R { e₀ with s := s } (hz' s) μ hμ κ p q
    simp only [PkgExpr.outer2, hexp, RB_L1, RB_L2, RB_L3, RB_L4, hZ, hc, hc₀, ← hL]
  -- the cumulant factors, `llClass_ccum_le`
  have hB₀ : ∀ α β, ‖c₀ α β‖ ≤ |K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2)) :=
    fun α β => RB_cum C μ hμ p₀ q₀ K₀ hK₀ α β
  have hB₁ : ∀ i j, ‖c i j‖ ≤ |K₁| * (N : ℝ) ^ (-(((p + q + 1 : ℕ) : ℝ) / 2)) :=
    fun i j => RB_cum C μ hμ p q K₁ hK₁ i j
  -- per structure and labels: the flags (`RB_core`), then the labels of the engine
  have hZb : ∀ R' ∈ L, ∀ κ : Fin 4 → Idx D N, ‖Z (κ 0) (κ 1) (κ 2) (κ 3) R'‖ ≤
      8 * (if R'.fpg 0 || R'.fpg 1 then η else 1) *
        ‖(R'.cf : ℂ) * (D : ℂ) ^ R'.dexp * (N : ℂ) ^ (-R'.S)‖ *
        ∑ s : Fin 2 → Bool, ∑ ι : Fin R'.nb → Fin D, ‖∫ h, ((RB_F R' s).map
          (FFac.val { e₀ with s := s } ι (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod
            ∂μ‖ := by
    intro R' hR' κ
    refine (RB_core R' e₀ η hzη hη0 C μ hμ _).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun ι _ => ?_
    congr 2
    funext h
    rw [RB_val_lab R'.nb (RB_F R' s) (G R') (RB_valid R' (G R') (hG R' hR').1 s).1 _ ι _ _ ?_ h]
    intro l hl
    interval_cases l <;> rfl
  have hRX : ∀ R' ∈ L, ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
      ‖Z (κ 0) (κ 1) (κ 2) (κ 3) R'‖ else 0) ≤ RB_X R' e₀ μ η := by
    intro R' hR'
    calc _ ≤ ∑ κ : Fin 4 → Idx D N, 8 * (if R'.fpg 0 || R'.fpg 1 then η else 1) *
          ‖(R'.cf : ℂ) * (D : ℂ) ^ R'.dexp * (N : ℂ) ^ (-R'.S)‖ *
          ∑ s : Fin 2 → Bool, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
            ∑ ι : Fin R'.nb → Fin D, ‖∫ h, ((RB_F R' s).map (FFac.val { e₀ with s := s } ι
              (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0) := by
          refine Finset.sum_le_sum fun κ _ => ?_
          by_cases hb : (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1
          · simp only [hb, and_self, ite_true]
            exact hZb R' hR' κ
          · simp only [hb, ite_false, Finset.sum_const_zero, mul_zero, le_refl]
      _ = RB_X R' e₀ μ η := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          rfl
  -- the engine, the prefactor and `N^{τ/2}`
  have hrk : (1 : ℝ) ≤ rk D N k := (RB_eta (D := D) ε hε'' hN1 hk hkN).2.2.2
  have hhs0 : 0 ≤ hsNorm A := by unfold hsNorm; positivity
  set T := (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
    hsNorm A ^ 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have he : ∀ R' : PkgExpr, (N : ℝ) ^ ((((-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) + 2 * R'.S : ℤ) :
      ℝ) / 2) = (N : ℝ) ^ (-((p + q : ℕ) : ℝ) / 2 - 3) := by
    intro R'
    congr 1
    push_cast
    ring
  have hpre : ‖-((D : ℂ) * N)⁻¹‖ * ((|K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2))) *
      (|K₁| * (N : ℝ) ^ (-(((p + q + 1 : ℕ) : ℝ) / 2)))) =
      (D : ℝ)⁻¹ * (|K₀| * |K₁|) * (N : ℝ) ^ (-((p + q : ℕ) : ℝ) / 2 - 3) := by
    have h3 : ((p₀ + q₀ + 1 : ℕ) : ℝ) = 3 := by rw [hpq]; norm_num
    rw [h3, norm_neg, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast, mul_inv]
    have : (N : ℝ)⁻¹ * (N : ℝ) ^ (-((3 : ℝ) / 2)) * (N : ℝ) ^ (-(((p + q + 1 : ℕ) : ℝ) / 2)) =
        (N : ℝ) ^ (-((p + q : ℕ) : ℝ) / 2 - 3) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    rw [← this]
    ring
  rw [eq1]
  calc _ ≤ ‖-((D : ℂ) * N)⁻¹‖ * ((|K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2))) *
        (|K₁| * (N : ℝ) ^ (-(((p + q + 1 : ℕ) : ℝ) / 2)))) *
        ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
          (L.map fun R' => ‖Z (κ 0) (κ 1) (κ 2) (κ 3) R'‖).sum else 0) :=
        RB_norm_nest _ c₀ c _ _ (by positivity) hB₀ hB₁ L Z
    _ = (D : ℝ)⁻¹ * (|K₀| * |K₁|) * (L.map fun R' => (N : ℝ) ^ ((((-((p + q : ℕ) : ℤ) - 6 -
          2 * R'.S) + 2 * R'.S : ℤ) : ℝ) / 2) * ∑ κ : Fin 4 → Idx D N,
          (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then ‖Z (κ 0) (κ 1) (κ 2) (κ 3) R'‖
            else 0)).sum := by
        rw [hpre, RB_L5]
        simp only [he, List.sum_map_mul_left]
        ring
    _ ≤ (D : ℝ)⁻¹ * (|K₀| * |K₁|) * (L.map fun R' => Q R' * ((N : ℝ) ^ (τ / 2) + 1) * T).sum := by
        gcongr
        refine List.sum_le_sum fun R' hR' => ?_
        refine le_trans ?_ (hNE R' hR' μ hμ A hA k hk hkN hhs e₀ hadm)
        gcongr
        exact hRX R' hR'
    _ = Kt * ((N : ℝ) ^ (τ / 2) + 1) * T := by
        rw [List.sum_map_mul_right, List.sum_map_mul_right, hKt]
        ring
    _ ≤ (N : ℝ) ^ τ * T := mul_le_mul_of_nonneg_right (RB_absorb hN1 hKt0 hNp) hT0
    _ = _ := by rw [hT, Real.rpow_add hN0]; ring

/-- The further terminal cases (i)–(iii) in the proof of Lemma 5.5
[claim_estimate_remainder_terms], with (5.29) [expansion_of_im]: the bridge from the rules to the
leaves at slots `{e₀ with s := s}` that are admissible for every flag. -/
private lemma RB_leaf (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (R : PkgExpr) (p₀ q₀ : ℕ)
    (hpq : p₀ + q₀ = 2) (hlab : ∀ w ∈ R.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2)
    (hrule : ∃ g : FAsg, FRuleOK R (-9 - 2 * R.S) g) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ N : ℕ in atTop,
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ e₀ : LoopEnv D N, RB_adm A k ε e₀ →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer { e₀ with s := s } μ p₀ q₀‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) := by
  intro τ hτ
  obtain ⟨g, hg⟩ := hrule
  obtain ⟨Q, hQ0, hQ⟩ := RB_engine D hD δA εA ε hδA hεA hε hε' hε'' C R _ g hg
  obtain ⟨K₀, hK₀⟩ := llClass_ccum_le C p₀ (q₀ + 1)
  obtain ⟨CU, -, Nη, hNη⟩ := pkg_slot_im D hD δA εA ε hδA hεA hε hε' hε''
  set Kt : ℝ := ((D : ℝ) ^ 2)⁻¹ * |K₀| * Q with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  have hpow : ∀ᶠ N : ℕ in atTop, 2 * Kt + 1 ≤ (N : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hQ (τ / 2) (by linarith), hpow, Filter.eventually_ge_atTop (max Nη 1)]
    with N hNE hNp hN
  intro μ hμ A hA k hk hkN hhs e₀ hadm
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  obtain ⟨hη0, -, -, hrk⟩ := RB_eta (D := D) ε hε'' hN1 hk hkN
  set η := etaK D N k ε with hη
  have hzη : ∀ a, (e₀.z a).im = η := fun a =>
    (hNη N (le_trans (le_max_left _ _) hN) A hA k hk hkN hhs _ (hadm fun _ => false) a).1
  -- the signed sum passed inside the cumulant sum
  set c₀ : Idx D N → Idx D N → ℂ := fun α β => ccum (μ.map fun h => h α β) p₀ (q₀ + 1) /
    ((p₀.factorial * q₀.factorial : ℕ) : ℂ) * (if α = β then (1 / 2 : ℂ) else 1) ^ (p₀ + q₀)
    with hc₀
  set Z : Idx D N → Idx D N → ℂ := fun α β =>
    ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
      ∫ h, R.evalH { e₀ with s := s } (fun l => if l = 0 then α else β) h ∂μ with hZ
  have eq1 : ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
      R.outer { e₀ with s := s } μ p₀ q₀ =
      -((D : ℂ) * N)⁻¹ * ∑ α : Idx D N, ∑ β : Idx D N,
        (if α.1 = β.1 then c₀ α β * Z α β else 0) := by
    simp only [PkgExpr.outer, RB_L1, RB_L2, RB_L3, hZ, hc₀]
  -- the labels of `R` are `0, 1`: the labels `2, 3` of the engine are free
  have hZκ : ∀ κ : Fin 4 → Idx D N, Z (κ 0) (κ 1) =
      ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, R.evalH { e₀ with s := s } (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h ∂μ := by
    intro κ
    simp only [hZ]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun h => ?_))
    refine RB_evalH_lab R _ _ _ (fun w hw u v huv => ?_) h
    obtain ⟨hu, hv⟩ := hlab w hw u v huv
    constructor
    · interval_cases u <;> rfl
    · interval_cases v <;> rfl
  have hcore : ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
      ‖Z (κ 0) (κ 1)‖ else 0) ≤ RB_X R e₀ μ η := by
    calc _ ≤ ∑ κ : Fin 4 → Idx D N, 8 * (if R.fpg 0 || R.fpg 1 then η else 1) *
          ‖(R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)‖ *
          ∑ s : Fin 2 → Bool, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
            ∑ ι : Fin R.nb → Fin D, ‖∫ h, ((RB_F R s).map (FFac.val { e₀ with s := s } ι
              (fun l => if hl : l < 4 then κ ⟨l, hl⟩ else κ 0) h)).prod ∂μ‖ else 0) := by
          refine Finset.sum_le_sum fun κ _ => ?_
          by_cases hb : (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1
          · simp only [hb, and_self, ite_true]
            rw [hZκ κ]
            exact RB_core R e₀ η hzη hη0 C μ hμ _
          · simp only [hb, ite_false, Finset.sum_const_zero, mul_zero, le_refl]
      _ = RB_X R e₀ μ η := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          rfl
  -- the count `D N²` of the free labels `2, 3`
  have hcnt : ∑ κ : Fin 4 → Idx D N, (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then
      ‖Z (κ 0) (κ 1)‖ else 0) = ((D : ℝ) * N ^ 2) *
        ∑ α : Idx D N, ∑ β : Idx D N, (if α.1 = β.1 then ‖Z α β‖ else 0) := by
    rw [RB_sum_pi4 (fun a b c d => if a.1 = b.1 ∧ c.1 = d.1 then ‖Z a b‖ else 0), ← RB_count D N,
      mul_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases hαβ : α.1 = β.1
    · simp only [hαβ, true_and, ite_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · simp [hαβ]
  have hB₀ : ∀ α β, ‖c₀ α β‖ ≤ |K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2)) :=
    fun α β => RB_cum C μ hμ p₀ q₀ K₀ hK₀ α β
  have hhs0 : 0 ≤ hsNorm A := by unfold hsNorm; positivity
  set T := (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
    hsNorm A ^ 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have hpre : (D * N : ℝ)⁻¹ * (|K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2))) *
      ((D : ℝ) * N ^ 2)⁻¹ =
      ((D : ℝ) ^ 2)⁻¹ * |K₀| * (N : ℝ) ^ ((((-9 - 2 * R.S) + 2 * R.S : ℤ) : ℝ) / 2) := by
    have h3 : ((p₀ + q₀ + 1 : ℕ) : ℝ) = 3 := by rw [hpq]; norm_num
    have : (N : ℝ)⁻¹ * (N : ℝ) ^ (-((3 : ℝ) / 2)) * ((N : ℝ) ^ 2)⁻¹ =
        (N : ℝ) ^ ((((-9 - 2 * R.S) + 2 * R.S : ℤ) : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    rw [h3, ← this]
    field_simp
  have hZ0 : 0 ≤ ∑ α : Idx D N, ∑ β : Idx D N, (if α.1 = β.1 then ‖Z α β‖ else 0) :=
    Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun β _ => by split_ifs <;> simp
  rw [eq1]
  calc _ ≤ (D * N : ℝ)⁻¹ * ((|K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2))) *
        ∑ α : Idx D N, ∑ β : Idx D N, (if α.1 = β.1 then ‖Z α β‖ else 0)) := by
        rw [norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        gcongr
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
        split_ifs
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hB₀ α β) (norm_nonneg _)
        · simp
    _ = (D * N : ℝ)⁻¹ * (|K₀| * (N : ℝ) ^ (-(((p₀ + q₀ + 1 : ℕ) : ℝ) / 2))) *
        ((D : ℝ) * N ^ 2)⁻¹ * ∑ κ : Fin 4 → Idx D N,
          (if (κ 0).1 = (κ 1).1 ∧ (κ 2).1 = (κ 3).1 then ‖Z (κ 0) (κ 1)‖ else 0) := by
        rw [hcnt]
        field_simp
    _ ≤ ((D : ℝ) ^ 2)⁻¹ * |K₀| * ((N : ℝ) ^ ((((-9 - 2 * R.S) + 2 * R.S : ℤ) : ℝ) / 2) *
        RB_X R e₀ μ η) := by
        rw [hpre]
        exact le_of_le_of_eq (mul_le_mul_of_nonneg_left hcore (by positivity)) (by ring)
    _ ≤ ((D : ℝ) ^ 2)⁻¹ * |K₀| * (Q * ((N : ℝ) ^ (τ / 2) + 1) * T) := by
        exact mul_le_mul_of_nonneg_left (hNE μ hμ A hA k hk hkN hhs e₀ hadm) (by positivity)
    _ = Kt * ((N : ℝ) ^ (τ / 2) + 1) * T := by rw [hKt]; ring
    _ ≤ (N : ℝ) ^ τ * T := mul_le_mul_of_nonneg_right (RB_absorb hN1 hKt0 hNp) hT0
    _ = _ := by rw [hT, Real.rpow_add hN0]; ring

/-! ### The bridges -/

/-- The bridge from the rules to the remainders in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: if every derivative structure `R'` of `𝓔^{(2)}_𝓡(p, q)` has an
assignment that passes the rows (`FRuleOK`, the conclusion of the rule lemmas), the signed sum over
the four starting loops of (5.29) [expansion_of_im] of `𝓔^{(2)}(p, q)` inside the cumulant sum is
at most `N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, at the slots of Lemmas 5.2
[lemma_localized_eigenvector_local_law] and 5.4 [lemma_localized_eigenvalue_local_law]. -/
theorem pkg_rem2_bridge (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (R : PkgExpr) (p₀ q₀ : ℕ)
    (hpq : p₀ + q₀ = 2) (p q : ℕ)
    (hrule : ∀ R' ∈ R.fpkg.dwirt 2 3 p q, ∃ g : FAsg,
      FRuleOK R' (-((p + q : ℕ) : ℤ) - 6 - 2 * R'.S) g) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer2 (evecEnv D N A k ε s) μ p₀ q₀ p q‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              R.outer2 (evalEnv D N A k ε t s) μ p₀ q₀ p q‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  intro τ hτ
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (RB_rem2 D hD δA εA ε hδA hεA hε hε' hε'' C R p₀ q₀ hpq p q hrule τ hτ)
  refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs => ⟨?_, fun t ht => ?_⟩⟩
  · exact hN₀ N hN μ hμ A hA k hk hkN hhs (evecEnv D N A k ε fun _ => false)
      fun s => Or.inl ⟨s, rfl⟩
  · exact hN₀ N hN μ hμ A hA k hk hkN hhs (evalEnv D N A k ε t fun _ => false)
      fun s => Or.inr ⟨t, ht, s, rfl⟩

/-- The bridge from the rules to the further terminal cases (i)–(iii) in the proof of Lemma 5.5
[claim_estimate_remainder_terms]: if the labels of `R` are `0, 1` and it has an assignment that
passes the rows with the prefactor of a leaf, the signed sum over the four starting loops of (5.29)
[expansion_of_im] of the cumulant sum `outer` is at most `N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`,
at the slots of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law]. -/
theorem pkg_leaf_bridge (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (hε : 0 < ε) (hε' : ε < 2 * εA) (hε'' : ε ≤ 1 / 3) (C : ℕ → ℝ) (R : PkgExpr) (p₀ q₀ : ℕ)
    (hpq : p₀ + q₀ = 2) (hlab : ∀ w ∈ R.loops, ∀ u v : ℕ, PkgLetter.ent u v ∈ w → u < 2 ∧ v < 2)
    (hrule : ∃ g : FAsg, FRuleOK R (-9 - 2 * R.S) g) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            R.outer (evecEnv D N A k ε s) μ p₀ q₀‖ ≤
          (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
            hsNorm A ^ 2) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
              R.outer (evalEnv D N A k ε t s) μ p₀ q₀‖ ≤
            (N : ℝ) ^ (τ + 2 * ε) * ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) *
              hsNorm A ^ 2) := by
  intro τ hτ
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (RB_leaf D hD δA εA ε hδA hεA hε hε' hε'' C R p₀ q₀ hpq hlab hrule τ hτ)
  refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs => ⟨?_, fun t ht => ?_⟩⟩
  · exact hN₀ N hN μ hμ A hA k hk hkN hhs (evecEnv D N A k ε fun _ => false)
      fun s => Or.inl ⟨s, rfl⟩
  · exact hN₀ N hN μ hμ A hA k hk hkN hhs (evalEnv D N A k ε t fun _ => false)
      fun s => Or.inr ⟨t, ht, s, rfl⟩

end RBMTransitionEdge

end
