import KltDP.Geometry.SchemeConormalOpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# An original closed curve on an isomorphism open

An actual closed immersion whose whole image lies over an isomorphism
open remains a closed immersion after a proper map. Its original
conormal sheaf is unchanged. The construction uses the original open
immersion lift and original restricted map, with both triangles proved.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.CurveOnIsomorphismOpen

variable {C S T : Scheme.{u}} (i : C ⟶ S) (b : S ⟶ T) (U : T.Opens)
    (hU : Set.range i.base ⊆ ((b ⁻¹ᵁ U : S.Opens) : Set S))

/-- Factor the original curve inclusion through the actual inverse-image open. -/
def lift : C ⟶ (b ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (b ⁻¹ᵁ U).ι i (by rwa [Scheme.Opens.range_ι])

@[reassoc]
theorem lift_ι : lift i b U hU ≫ (b ⁻¹ᵁ U).ι = i :=
  IsOpenImmersion.lift_fac _ _ _

instance lift_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (lift i b U hU) := by
  letI : IsClosedImmersion (lift i b U hU ≫ (b ⁻¹ᵁ U).ι) := by
    rw [lift_ι]
    infer_instance
  exact IsClosedImmersion.of_comp _ (b ⁻¹ᵁ U).ι

/-- The same composite factors through the original restricted map. -/
theorem comp_factor :
    (lift i b U hU ≫ (b ∣_ U)) ≫ U.ι = i ≫ b := by
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, lift_ι]

include hU in
/-- Properness closes the locally closed image through the actual isomorphism open. -/
theorem comp_isClosedImmersion [IsClosedImmersion i] [IsProper b] [IsIso (b ∣_ U)] :
    IsClosedImmersion (i ≫ b) := by
  letI : IsImmersion (i ≫ b) := by
    rw [← comp_factor i b U hU]
    infer_instance
  apply IsClosedImmersion.of_isPreimmersion
  simpa only [Set.image_univ] using (i ≫ b).isClosedMap Set.univ isClosed_univ

include hU in
/-- The actual conormal on the unchanged original curve is preserved;
no normal-bundle comparison is assumed. -/
def conormalIso [IsIso (b ∣_ U)] :
    schemeConormalSheaf (i ≫ b) ≅ schemeConormalSheaf i :=
  eqToIso (congrArg schemeConormalSheaf (comp_factor i b U hU).symm) ≪≫
    schemeConormalPostcompOpenIso (lift i b U hU ≫ (b ∣_ U)) U.ι ≪≫
    schemeConormalPostcompOpenIso (lift i b U hU) (b ∣_ U) ≪≫
    (schemeConormalPostcompOpenIso (lift i b U hU) (b ⁻¹ᵁ U).ι).symm ≪≫
    eqToIso (congrArg schemeConormalSheaf (lift_ι i b U hU))

end KltDP.Geometry.CurveOnIsomorphismOpen

#print axioms KltDP.Geometry.CurveOnIsomorphismOpen.comp_isClosedImmersion
#print axioms KltDP.Geometry.CurveOnIsomorphismOpen.conormalIso
