module

public import RBMTransitionEdge

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `RBMTransitionEdge` named in its proof. The
definitions that occur in the statements are those of `RBMTransitionEdge/MainDefs.lean`.
-/

section
noncomputable section
namespace RBMTransitionEdge
open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff

/-- Theorem 2.1 [mix], (2.5); the statement is `RBMTransitionEdge.MixStatement`. -/
theorem theorem_2_1 : MixStatement :=
  mix

/-- Theorem 2.5 [theorem_localized_eigenvalue]: `LocalizedEvalStatement`. -/
theorem theorem_2_5 : LocalizedEvalStatement :=
  localized_eval

end RBMTransitionEdge
end
