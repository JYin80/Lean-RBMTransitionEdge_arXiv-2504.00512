module

public import RBMTransitionEdge.Localized.Expansion.PkgInv2
public import RBMTransitionEdge.Localized.Expansion.Pairing
public import RBMTransitionEdge.Localized.Expansion.DetLoop
public import RBMTransitionEdge.Localized.Expansion.PkgInv
public import RBMTransitionEdge.Localized.Expansion.PkgCounts
import all RBMTransitionEdge.Localized.Expansion.PkgInv
import all RBMTransitionEdge.Localized.Expansion.PkgCounts
import all Init.Data.List.SplitOn.Basic

@[expose] public section

/-!
# The exceptional classes of the further expansion of Lemma 5.5

The package properties `freeTwo` and `gainLam2`, and the finite check of the exceptional classes
of the further expansion in the proof of Lemma 5.5 [claim_estimate_remainder_terms], on which the
generic count does not suffice: the leaves of case (ii) with `fR = 2` after (5.92)
[eq:weak_further_expansion2], the leaf (5.94) [expansion_result_type_3_fr_2_m_plus_u_2], and the
exceptional subcases of the companion cases (5), (6), (8), each decided with the property its bound
uses on the finite tree below the starting expressions.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- A package of a word with `Δ` without `Λ̃` with at least two resolvents. -/
def PkgExpr.freeTwo (R : PkgExpr) : Bool :=
  R.loops.any fun w => w.any PkgLetter.isEnt &&
    (pkgSegs w).any fun σ => !(σ.any PkgLetter.isLam) && 2 ≤ σ.countP PkgLetter.isRes

/-- The loop of `Λ̃₂` (Type II) is `⟨𝔐_a Λ̃₂ 𝔐_b E_x⟩`, `a ≠ b`. -/
def PkgExpr.gainLam2 (R : PkgExpr) : Bool :=
  R.loops.any fun w => w.contains (.lw (.lamt 1)) && !(w.any PkgLetter.isEnt) && pkgGainLoop w

open private fR_step inv_fTree from RBMTransitionEdge.Localized.Expansion.PkgInv
open private mem_fTree fTree_succ_single from RBMTransitionEdge.Localized.Expansion.PkgCounts

/-! ### The finite check

The statements of the five lists are decided on the finite tree below `𝒯₀`: by `pkg_inv_counts`,
`T` lies in `loopTree k` with `k = Σ(𝓡₀) ≤ 2`, and `𝓡` lies in the further tree of `𝓡₀` at the
depth `d = fR + Σ - k ≤ 4 - k`, whenever `fR ≤ 2` and `Σ ≤ 2`, as every list requires. -/

/-- The first list: the leaves of Type II with `fR = 2` (after (5.92) [eq:weak_further_expansion2]),
the antecedents of the Boolean tests first, as the tests are run on every node of the tree. -/
private def plB1 (R : PkgExpr) : Bool :=
  decide (R.fR = 2 → R.ptype = 2 → R.ffocus = none →
    (R.fsig = 1 → R.gainLam2 = true ∧ R.freeTwo = true) ∧
    (R.fsig = 2 → R.gainLam2 = true ∨ R.freeTwo = true))

/-- The second list: the leaf (5.94) [expansion_result_type_3_fr_2_m_plus_u_2]. -/
private def plB2 (R : PkgExpr) : Bool :=
  decide (R.fR = 2 → R.fsig = 0 → R.ptype = 3 → R.ffocus = none → R.onlyDet 1 = true)

/-- The third list: the exceptional subcase of case (5), `fR = 0`, `Σ = 1`. -/
private def plB3 (R : PkgExpr) : Bool :=
  decide (R.fR = 0 → R.fsig = 1 → R.ptype = 2 → R.ffocus.isSome = true →
    R.freeTwo = true ∨ 2 ≤ R.lamSide 0 true ∨ 2 ≤ R.lamSide 1 false)

/-- The fourth list: the exceptional subcase of case (6), `fR = 1`, `Σ = 1`, `a₄ = 0`. -/
private def plB4 (R : PkgExpr) : Bool :=
  decide (R.fR = 1 → R.fsig = 1 → R.ptype = 2 → R.lamSide 1 false = 0 →
    R.ffocus.isSome = true → R.gainLam2 = true)

/-- The fifth list: the exceptional subcase of case (8), `fR = 0`, `Σ = 0`. -/
private def plB5 (T : LoopExpr) (R₀ R : PkgExpr) : Bool :=
  decide (R.fR = 0 → R.fsig = 0 → R.ptype = 3 → R.ffocus.isSome = true →
    T = loopStart ∧ R = R₀ ∧ R.fpkg.onlyRes 1 = true)

/-- The five tests on one expression. -/
private def plNode (T : LoopExpr) (R₀ R : PkgExpr) : Bool :=
  plB1 R && plB2 R && plB3 R && plB4 R && plB5 T R₀ R

/-- The five tests on every expression of the further tree of `R` of depth at most `f` that has
`fR ≤ 2` and `Σ ≤ 2`; both counts do not decrease along the tree, so no other expression is
tested. -/
private def plWalk (T : LoopExpr) (R₀ : PkgExpr) : ℕ → PkgExpr → Bool
  | 0, R => plNode T R₀ R
  | f + 1, R => plNode T R₀ R &&
      (!decide (R.fR ≤ 2 ∧ R.fsig ≤ 2) || R.fstep.all (plWalk T R₀ f))

/-- The derivatives `(p, q)` of `𝓡_𝒯(p₀, q₀)` with `p + q = 2`. -/
private def plPQ : List (ℕ × ℕ) := [(0, 2), (1, 1), (2, 0)]

/-- The tests from every `𝓡₀` of `𝒯 ∈ loopTree k` with `rcount = 0` and `Σ(𝓡₀) = k`. -/
private def plStart (k : ℕ) : Bool :=
  (loopTree k).all fun T => !decide (T.rcount = 0) ||
    plPQ.all fun pq => (T.pkgStart.dwirt 0 1 pq.1 pq.2).all fun R₀ =>
      !decide (R₀.fsig.toNat = k) || plWalk T R₀ (4 - k) R₀

private theorem plStart_zero : plStart 0 = true := by decide +kernel
private theorem plStart_one : plStart 1 = true := by decide +kernel
private theorem plStart_two : plStart 2 = true := by decide +kernel

/-! ### From the finite check to the further tree -/

/-- `fR` and `Σ` do not decrease along the further tree: Table 2 [table_effect_of_operations_2]. -/
private theorem fTree_mono (R : PkgExpr) (d : ℕ) (R' : PkgExpr) (h : R' ∈ fTree d [R]) :
    R.fR ≤ R'.fR ∧ R.fsig ≤ R'.fsig :=
  inv_fTree (fun S => R.fR ≤ S.fR ∧ R.fsig ≤ S.fsig)
    (fun S hS R'' hR'' => ⟨hS.1.trans (fR_step S R'' hR'').1, hS.2.trans (fR_step S R'' hR'').2⟩)
    d [R] (fun S hS => by rw [List.mem_singleton.1 hS]; exact ⟨le_refl _, le_refl _⟩) R' h

/-- Every expression of the further tree of `R` of depth at most `f` with `fR ≤ 2` and `Σ ≤ 2`
passes the five tests, if the walk from `R` does. -/
private theorem plWalk_sound (T : LoopExpr) (R₀ : PkgExpr) :
    ∀ (f : ℕ) (R : PkgExpr), plWalk T R₀ f R = true →
      ∀ d ≤ f, ∀ R' ∈ fTree d [R], R'.fR ≤ 2 → R'.fsig ≤ 2 → plNode T R₀ R' = true
  | 0, R, h, d, hd, R', hR', _, _ => by
      have hd0 : d = 0 := by omega
      subst hd0
      rw [fTree, List.mem_singleton] at hR'
      subst hR'
      simpa only [plWalk] using h
  | f + 1, R, h, d, hd, R', hR', h1, h2 => by
      cases d with
      | zero =>
          rw [fTree, List.mem_singleton] at hR'
          subst hR'
          simp only [plWalk, Bool.and_eq_true] at h
          exact h.1
      | succ d =>
          have hm := fTree_mono R _ R' hR'
          rw [fTree_succ_single, mem_fTree] at hR'
          obtain ⟨S, hS, hR'⟩ := hR'
          simp only [plWalk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not] at h
          rcases h.2 with hg | hall
          · exact absurd ⟨by omega, by omega⟩ hg
          · exact plWalk_sound T R₀ f S (List.all_eq_true.1 hall S hS) d (by omega) R' hR' h1 h2

/-- The five tests hold from every `𝓡₀` of `𝒯 ∈ loopTree k` with `Σ(𝓡₀) = k ≤ 2`. -/
private theorem plStart_sound (k : ℕ) (hk : k ≤ 2) (T : LoopExpr) (hT : T ∈ loopTree k)
    (hR0 : T.rcount = 0) (p₀ q₀ : ℕ) (hpq : p₀ + q₀ = 2) (R₀ : PkgExpr)
    (hR₀ : R₀ ∈ T.pkgStart.dwirt 0 1 p₀ q₀) (hs : R₀.fsig.toNat = k) :
    plWalk T R₀ (4 - k) R₀ = true := by
  have hall : plStart k = true := by
    interval_cases k
    · exact plStart_zero
    · exact plStart_one
    · exact plStart_two
  have h1 := List.all_eq_true.1 hall T hT
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
  rcases h1 with h1 | h1
  · exact absurd hR0 h1
  · have hpq' : (p₀, q₀) ∈ plPQ := by
      simp only [plPQ, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq]
      omega
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 _ hpq') R₀ hR₀
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
    rcases h2 with h2 | h2
    · exact absurd hs h2
    · exact h2

end RBMTransitionEdge

end
