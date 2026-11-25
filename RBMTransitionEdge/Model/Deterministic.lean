module

public import RBMTransitionEdge.MainDefs
public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# The deterministic objects of §2.2

The solution `m` of (2.16) [self_m] and the matrix `M` of (2.17) [def_G0] (Definition 2.7
[defn_Mm]) for a general Hermitian `Λ`, the density `ρ_N` of (2.19) [eq:density_rhoN], its edges
`E^±` and the curvature parameters `γ_±` of (2.6) [eq:def_gamma], the semicircle density (2.18)
[eq:semidensity] and the quantiles (2.20) [eq:gammak]. Existence, uniqueness and the properties
of these objects are separate statements.
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `M(z) = (Λ - z - m(z))⁻¹` of (2.17) [def_G0]. -/
def MSol {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (Λ - (z + mSol Λ z) • (1 : Matrix ι ι ℂ))⁻¹

/-- The right edge `E⁺`: the supremum of the support of `ρ_N`. -/
def Eplus {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) : ℝ :=
  sSup (Function.support (rho Λ))

/-- The left edge `E⁻`: the infimum of the support of `ρ_N`. -/
def Eminus {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) : ℝ :=
  sInf (Function.support (rho Λ))

/-- `γ₊` of (2.6) [eq:def_gamma]: `lim_{E↑E⁺} ρ_N(E)/√(E⁺ - E) = γ₊^{3/2}/π`. -/
def gammaPlus {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) : ℝ :=
  (Real.pi * limUnder (𝓝[<] (Eplus Λ)) fun E => rho Λ E / Real.sqrt (Eplus Λ - E)) ^ (2 / 3 : ℝ)

/-- `γ₋` of (2.6) [eq:def_gamma]: `lim_{E↓E⁻} ρ_N(E)/√(E - E⁻) = γ₋^{3/2}/π`. -/
def gammaMinus {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) : ℝ :=
  (Real.pi * limUnder (𝓝[>] (Eminus Λ)) fun E => rho Λ E / Real.sqrt (E - Eminus Λ)) ^ (2 / 3 : ℝ)

end RBMTransitionEdge

end
