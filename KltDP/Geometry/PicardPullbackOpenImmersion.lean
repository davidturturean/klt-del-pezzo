import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.PicardOpenRestriction
import KltDP.Geometry.SchemePicardPullback

/-!
# Picard pullback agrees with open restriction

The existing natural isomorphism between image-open restriction and
scheme-module pullback identifies their actions on actual sheaf
isomorphism classes. Taking units gives equality of the two existing
Picard homomorphisms. This comparison applies to every open immersion;
it requires no integrality or Cartier-divisor hypothesis.

The proof uses the pinned Mathlib quotient and units extensionality APIs
and the already constructed `restrictionIsoPullback`. It introduces no
new pullback, quotient, or monoidal comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual pullback and open-restriction functors induce the same
map on actual sheaf isomorphism classes. -/
theorem schemeModulePullbackClassMap_eq_restrictionClassMap
    (a : Skeleton X.Modules) :
    schemeModulePullbackClassMap f a =
      SchemeModuleRestriction.restrictionClassMap f a := by
  refine Quotient.inductionOn a (fun M => ?_)
  exact Quotient.sound ⟨((SchemeModuleRestriction.restrictionIsoPullback f).app M).symm⟩

/-- Actual scheme Picard pullback agrees with the existing open
restriction homomorphism. -/
theorem schemePicardPullbackHom_eq_picardRestrictionHom :
    schemePicardPullbackHom f = SchemeModuleRestriction.picardRestrictionHom f := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  apply MonoidHom.ext
  intro p
  apply Units.ext
  change schemeModulePullbackClassMap f (show (Skeleton X.Modules)ˣ from p).val =
    SchemeModuleRestriction.restrictionClassMap f
      (show (Skeleton X.Modules)ˣ from p).val
  exact schemeModulePullbackClassMap_eq_restrictionClassMap f _

end KltDP.Geometry
