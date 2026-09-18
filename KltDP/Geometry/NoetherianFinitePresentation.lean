import KltDP.Geometry.CoherentQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FinitePresentation

/-! Ordinary finite-presentation inputs for the actual family Euler theorem.
No cohomology or constancy assertion is assumed. Noetherianity is used only
in the ordinary input adapters, not in any published-source telescope. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.NoetherianFinitePresentation

/-- The original affine ring maps are finitely presented because their
actual source section rings are Noetherian and they are finite type. -/
theorem of_locallyOfFiniteType {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  constructor
  intro U V e
  letI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp
    (LocallyOfFiniteType.finiteType_of_affine_subset U V e)

/-- Properness supplies finite type for the same original morphism. -/
theorem of_isProper {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] : LocallyOfFinitePresentation f :=
  of_locallyOfFiniteType f

local instance noetherianPresentationOverLocallyBijective (X : Scheme.{u}) :
    ∀ U : X.Opens,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
        AddCommGrp.{u} :=
  CoherentQuasicoherent.schemeOverWEqualsLocallyBijective X

/-- The original structure module satisfies the pinned native finite
presentation predicate, via its already proved literal coherence. -/
theorem structureSheaf (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  CoherentQuasicoherent.isFinitePresentation_of_isCoherentModule
    (SheafOfModules.unit X.ringCatSheaf)

end KltDP.Geometry.NoetherianFinitePresentation

#check @KltDP.Geometry.NoetherianFinitePresentation.of_isProper
#check @KltDP.Geometry.NoetherianFinitePresentation.structureSheaf
#print axioms KltDP.Geometry.NoetherianFinitePresentation.of_isProper
#print axioms KltDP.Geometry.NoetherianFinitePresentation.structureSheaf
