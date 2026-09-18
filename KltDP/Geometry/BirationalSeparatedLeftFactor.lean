import KltDP.Geometry.BirationalComposition
import KltDP.Geometry.BirationalIsomorphismOpen
import KltDP.Geometry.RationalFunctionSheaf

/-!
# Birationality of the original first factor

A separated finite-type birational second map is an isomorphism over an
actual nonempty open. Injectivity there forces the first map to preserve
generic points whenever its composite is birational. The existing original
function-field composition theorem then proves the first map birational.
No generic-point condition on that first map is an additional hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Cancel an original separated, locally finite-type birational map on
the right, deriving generic-point preservation of the original first map. -/
theorem isBirationalScheme_left_of_comp_of_isSeparated
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType g] [IsSeparated g]
    (hg : IsBirationalScheme g) (hfg : IsBirationalScheme (f ≫ g)) :
    IsBirationalScheme f := by
  obtain ⟨U, hU, hgU⟩ := exists_isomorphism_open_of_isBirationalScheme g hg
  letI : Nonempty U := hU
  letI : IsIso (g ∣_ U) := hgU
  have hη : genericPoint Z ∈ U := genericPoint_mem_nonempty_open Z U
  have hfgη : g.base (f.base (genericPoint X)) = genericPoint Z := hfg.map_genericPoint
  have ha : f.base (genericPoint X) ∈ g ⁻¹ᵁ U := by
    change g.base (f.base (genericPoint X)) ∈ U
    rw [hfgη]
    exact hη
  have hb : genericPoint Y ∈ g ⁻¹ᵁ U := by
    change g.base (genericPoint Y) ∈ U
    rw [hg.map_genericPoint]
    exact hη
  have he : (g ∣_ U).base ⟨f.base (genericPoint X), ha⟩ =
      (g ∣_ U).base ⟨genericPoint Y, hb⟩ := by
    rw [morphismRestrict_base]
    exact Subtype.ext (hfgη.trans hg.map_genericPoint.symm)
  have hgeneric : f.base (genericPoint X) = genericPoint Y :=
    congrArg Subtype.val ((g ∣_ U).homeomorph.injective he)
  letI : GenericPointPreserving f := ⟨hgeneric⟩
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  exact BirationalComposition.isBirationalScheme_left_of_comp f g hfg

end KltDP.Geometry
