import KltDP.Geometry.ModuleOpenRestrictionTensor
import KltDP.Geometry.TensorInvertibleSheaf

/-!
# Actual Picard restriction along an open immersion

The existing open-restriction functor preserves the actual module-sheaf
tensor and its unit. It therefore induces a homomorphism on actual
isomorphism classes, and `Units.map` restricts the project's Picard group.
The actual restricted sheaf is again locally free of rank one, by the
proved equivalence between this property and tensor-invertibility.

The quotient and tensor identities used here are the pinned Mathlib
`CategoryTheory.Skeletal` and `CategoryTheory.Monoidal.Skeleton` APIs.
The later official `Skeleton.monoidHom` requires a full monoidal-functor
structure; this bounded adapter proves exactly the needed quotient laws
from the already constructed tensor and unit isomorphisms. It introduces
no new sheaf tensor, quotient, or notion of invertibility.

This file constructs restriction for actual open immersions. It does not
assert that a rational Cartier equation pulls back along an arbitrary
scheme morphism, or supply a Cartier compatibility theorem as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- Apply the actual open-restriction functor to an actual sheaf
isomorphism class. Well-definedness uses its action on isomorphisms. -/
def restrictionClassMap : Skeleton X.Modules → Skeleton Y.Modules :=
  Quotient.map (restriction f).obj (fun _ _ h =>
    h.map (fun e => (restriction f).mapIso e))

@[simp]
theorem restrictionClassMap_toSkeleton (M : X.Modules) :
    restrictionClassMap f (toSkeleton M) = toSkeleton ((restriction f).obj M) := rfl

/-- The induced map on actual isomorphism classes preserves the actual
tensor product and actual unit. -/
def restrictionClassHom :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    Skeleton X.Modules →* Skeleton Y.Modules := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact {
    toFun := restrictionClassMap f
    map_one' := by
      rw [Skeleton.one_eq, restrictionClassMap_toSkeleton, Skeleton.one_eq]
      exact Quotient.sound ⟨restrictionTensorUnitIso f⟩
    map_mul' := by
      intro a b
      refine Quotient.inductionOn₂ a b (fun M N => ?_)
      change restrictionClassMap f (toSkeleton M * toSkeleton N) =
        restrictionClassMap f (toSkeleton M) * restrictionClassMap f (toSkeleton N)
      rw [← Skeleton.toSkeleton_tensorObj, restrictionClassMap_toSkeleton,
        restrictionClassMap_toSkeleton, restrictionClassMap_toSkeleton,
        ← Skeleton.toSkeleton_tensorObj]
      exact Quotient.sound ⟨restrictionTensorIso f M N⟩ }

@[simp]
theorem restrictionClassHom_toSkeleton (M : X.Modules) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    restrictionClassHom f (toSkeleton M) = toSkeleton ((restriction f).obj M) := rfl

/-- Restriction on the existing actual Picard groups is the map on
units of the proved tensor-monoid homomorphism. -/
def picardRestrictionHom : X.Pic →* Y.Pic := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact Units.map (restrictionClassHom f)

/-- The restricted Picard class has exactly the restricted sheaf class. -/
theorem picardRestrictionHom_val (p : X.Pic) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    (picardRestrictionHom f p : Skeleton Y.Modules) =
      restrictionClassHom f (p : Skeleton X.Modules) := rfl

/-- The actual restriction of a locally free rank-one sheaf is locally
free of rank one. Its tensor inverse comes from restricting the actual
inverse class, and the existing converse gives local trivializations. -/
theorem restriction_isInvertible (L : InvertibleSheaf X) :
    KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) ((restriction f).obj L.obj) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  apply SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton
  change IsUnit (restrictionClassHom f (toSkeleton L.obj))
  exact (InvertibleSheaf.isUnit_toSkeleton L).map (restrictionClassHom f)

/-- The actual restricted module sheaf, carrying its proved local
rank-one property. -/
def restrictInvertibleSheaf (L : InvertibleSheaf X) : InvertibleSheaf Y :=
  ⟨(restriction f).obj L.obj, restriction_isInvertible f L⟩

/-- Restriction of an invertible sheaf and restriction of its actual
Picard class agree. -/
theorem picardRestrictionHom_toPic (L : InvertibleSheaf X) :
    picardRestrictionHom f L.toPic = (restrictInvertibleSheaf f L).toPic := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  apply Units.ext
  change (picardRestrictionHom f L.toPic : Skeleton Y.Modules) =
    ((restrictInvertibleSheaf f L).toPic : Skeleton Y.Modules)
  rw [picardRestrictionHom_val, InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  rfl

end KltDP.Geometry.SchemeModuleRestriction
