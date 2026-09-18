import KltDP.Compatibility.BirationalRationality
import KltDP.Geometry.BirationalIsomorphismOpen

/-!
# Rationality transport along the original birational morphism

The original generic-point/stalk definition of birationality gives an
isomorphism over an actual nonempty target open by the compiled
`exists_isomorphism_open_of_isBirationalScheme`. Those opens and that
restricted original map supply the partial isomorphism over the original
base. The source and target structure maps remain explicit.

This is ordinary transport of an existing rationality proof. It does not
assert rationality of klt del Pezzo surfaces or cohomology vanishing.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f]
    (sX : X ⟶ S) (sY : Y ⟶ S) (hcomp : f ≫ sY = sX)
    (hbir : IsBirationalScheme f)

include hcomp hbir

/-- The actual birational morphism induces a partial isomorphism over the
original base, using its original restriction to a nonempty open. -/
theorem birationalOver_of_isBirationalScheme : Scheme.BirationalOver sX sY := by
  obtain ⟨U, hU, hfU⟩ := exists_isomorphism_open_of_isBirationalScheme f hbir
  letI : Nonempty U.toScheme := ⟨Classical.choice hU⟩
  letI : IsIso (f ∣_ U) := hfU
  have hUset : (U : Set Y).Nonempty :=
    ⟨(Classical.choice hU).val, (Classical.choice hU).property⟩
  refine ⟨{
    source := f ⁻¹ᵁ U
    dense_source := (f ⁻¹ᵁ U).isOpen.dense (preimage_nonempty_of_isIso_restrict f U)
    target := U
    dense_target := U.isOpen.dense hUset
    iso := asIso (f ∣_ U) }, ?_⟩
  change (f ∣_ U) ≫ U.ι ≫ sY = (f ⁻¹ᵁ U).ι ≫ sX
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hcomp]

/-- Rationality over the original base transfers through the original
birational map. The target's rationality remains an explicit hypothesis. -/
theorem isRationalOver_of_isBirationalScheme [Scheme.IsRationalOver sY] :
    Scheme.IsRationalOver sX :=
  Scheme.BirationalOver.isRationalOver sX sY
    (birationalOver_of_isBirationalScheme f sX sY hcomp hbir)

end KltDP.Geometry
