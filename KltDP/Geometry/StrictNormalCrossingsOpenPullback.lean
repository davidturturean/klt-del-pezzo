import KltDP.Geometry.DominantCartierRegularPullback
import KltDP.Geometry.StrictNormalCrossingsCartierLocality
import KltDP.Geometry.StrictNormalCrossingsEquiv

/-!
# Strict normal crossings under the original open-immersion pullback

At each original source point, pull back an existing regular chart of the
divisor. Its germ is the image of the original germ under the actual stalk
isomorphism. Transport of the original parameter family gives SNC there,
and the accepted Cartier locality criterion handles all equation charts.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.DominantCartierPullback
attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance openImmersion_genericPointPreserving
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] : GenericPointPreserving j :=
  ⟨genericPoint_eq_of_isOpenImmersion j⟩

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- An original open immersion preserves SNC of the actual signed Cartier
pullback, using its actual isomorphisms on structure-sheaf stalks. -/
theorem isStrictNormalCrossingsCartier_of_isOpenImmersion
    (j : Y ⟶ X) [IsOpenImmersion j] (D : CartierDivisor X)
    (hD : IsStrictNormalCrossingsCartier X D) :
    IsStrictNormalCrossingsCartier Y (pullbackHom j D) := by
  apply isStrictNormalCrossingsCartier_of_local_equations Y (pullbackHom j D)
  intro y
  obtain ⟨c, hc⟩ := hD.1 (j.base y)
  refine ⟨pulledRegularChart j D c, hc, ?_⟩
  let e : X.presheaf.stalk (j.base y) ≃+* Y.presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  have hs := (hD.2 c (j.base y) hc).map_equiv e
  have heq : e (X.presheaf.germ c.chart.openSet (j.base y) hc c.coefficient) =
      Y.presheaf.germ (j ⁻¹ᵁ c.chart.openSet) y hc
        (j.app c.chart.openSet c.coefficient) :=
    Scheme.stalkMap_germ_apply j c.chart.openSet y hc c.coefficient
  exact (congrArg (IsStrictNormalCrossingsEquation (Y.presheaf.stalk y)) heq).mp hs

/-- In particular, an actual scheme isomorphism transports the original
SNC divisor to its actual signed Cartier pullback. -/
theorem isStrictNormalCrossingsCartier_of_iso (e : Y ≅ X)
    (D : CartierDivisor X) (hD : IsStrictNormalCrossingsCartier X D) :
    IsStrictNormalCrossingsCartier Y (pullbackHom e.hom D) :=
  isStrictNormalCrossingsCartier_of_isOpenImmersion e.hom D hD

end KltDP.Geometry.DominantCartierPullback

#print axioms KltDP.Geometry.DominantCartierPullback.isStrictNormalCrossingsCartier_of_isOpenImmersion
#print axioms KltDP.Geometry.DominantCartierPullback.isStrictNormalCrossingsCartier_of_iso
