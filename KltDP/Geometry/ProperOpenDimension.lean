import KltDP.Geometry.CodimensionOneOpen
import KltDP.Geometry.ClosedPointDimension
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Dimension comparison through an actual proper isomorphism open

A proper morphism between integral schemes of finite type over the field
preserves global dimension if it is an isomorphism over a nonempty open.
The proof chooses an actual closed point in that open on the source.
Properness makes its image closed. The actual stalks have equal dimension,
and the previously proved finite-type closed-point theorem compares each
of them with its global scheme dimension.

No birationality, dimension comparison, or stalk isomorphism is supplied
as an additional assumption. Reuse is the pinned finite-type Jacobson
theorem, actual proper-map closedness, and the existing dimension theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The local-ring dimensions agree at every actual point of an
isomorphism open, via the three actual open-immersion stalk maps. -/
theorem ringKrullDim_stalk_eq_over_isomorphism_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : X) (hx : f.base x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f.base x)) := by
  let x' : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  calc
    ringKrullDim (X.presheaf.stalk x) =
        ringKrullDim ((f ⁻¹ᵁ U).toScheme.presheaf.stalk x') :=
      ringKrullDim_stalk_openImmersion (f ⁻¹ᵁ U).ι x'
    _ = ringKrullDim (U.toScheme.presheaf.stalk ((f ∣_ U).base x')) :=
      (ringKrullDim_stalk_openImmersion (f ∣_ U) x').symm
    _ = ringKrullDim (Y.presheaf.stalk (U.ι.base ((f ∣_ U).base x'))) :=
      (ringKrullDim_stalk_openImmersion U.ι ((f ∣_ U).base x')).symm
    _ = ringKrullDim (Y.presheaf.stalk (f.base x)) := by
      change ringKrullDim (Y.presheaf.stalk (((f ∣_ U).base x').val)) = _
      exact congrArg (fun y : Y => ringKrullDim (Y.presheaf.stalk y))
        (morphismRestrict_base_coe f U x')

/-- The actual proper morphism has source and target of equal global
dimension whenever its actual isomorphism open is nonempty. -/
theorem topologicalKrullDim_eq_of_proper_isomorphism_open
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (U : Y.Opens) [Nonempty U] [IsIso (f ∣_ U)] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  letI : LocallyOfFiniteType (f ≫ g) := inferInstance
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ g)
  let y : U.toScheme := Classical.choice (inferInstance : Nonempty U)
  let x' : (f ⁻¹ᵁ U).toScheme := (asIso (f ∣_ U)).inv.base y
  have hnonempty : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := ⟨x'.val, x'.property⟩
  obtain ⟨x, hx, hxclosed⟩ :=
    nonempty_inter_closedPoints hnonempty (f ⁻¹ᵁ U).isOpen.isLocallyClosed
  have hyclosed : IsClosed ({f.base x} : Set Y) := by
    simpa only [Set.image_singleton] using f.isClosedMap {x} hxclosed
  calc
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk x) :=
      (closed_stalk_dimension_eq_global X (f ≫ g) x hxclosed).symm
    _ = ringKrullDim (Y.presheaf.stalk (f.base x)) :=
      ringKrullDim_stalk_eq_over_isomorphism_open f U x hx
    _ = topologicalKrullDim Y := closed_stalk_dimension_eq_global Y g (f.base x) hyclosed

end KltDP.Geometry
