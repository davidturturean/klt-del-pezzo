import KltDP.Geometry.GluedAdjunctionIntrinsicTargetInputAliases

/-!
# The measured module projection round trips inside the target transition

Retain the original bundled modules. Normalize only projections of a literal
ModuleCat.of, the named Prefunctor object projection, and the local monoidal
alias exposed by componentRestriction. No proof argument is unfolded.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetModuleProjections

private theorem module_carrier (B : Type u) [Ring B] (M : Type u)
    [AddCommGroup M] [Module B M] : (ModuleCat.of B M).carrier = M := rfl

private theorem module_add (B : Type u) [Ring B] (M : Type u)
    [g : AddCommGroup M] [Module B M] : (ModuleCat.of B M).isAddCommGroup = g := rfl

private theorem module_scalar (B : Type u) [Ring B] (M : Type u)
    [AddCommGroup M] [m : Module B M] : (ModuleCat.of B M).isModule = m := rfl

/-- The same original target square with the measured projection round trips reduced. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    have h := GluedAdjunctionIntrinsicTargetInputAliases.target_square
      f I hI U r d hU hd hAmbient
    try dsimp only [module_carrier, module_add, module_scalar, Prefunctor.obj] at h
    exact h

/-- Remove only the local monoidal alias from the original target-transition word. -/
def local_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    have h := GluedAdjunctionIntrinsicTargetInputAliases.local_square
      f I U r d hU hd hAmbient hCurve
    dsimp only [AffineModuleTildeTensorPullbackRestriction.moduleTensor] at h
    exact h

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetModuleProjections
