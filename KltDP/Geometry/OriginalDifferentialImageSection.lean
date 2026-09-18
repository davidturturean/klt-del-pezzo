import KltDP.Geometry.CartierFrames
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

/-!
# The original differential image section

This definition is extracted unchanged from the canonical coefficient-order
module. It uses the original module-pullback adjunction unit and the original
differential map, with the same namespace and public name.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.NormalizedDifferentialCoefficientOrder

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The literal original differential applied to a literal original section. -/
def imageSection {k : Type u} [CommRing k] {A B : Scheme.{u}}
    (sA : A ⟶ Spec (CommRingCat.of k)) (sB : B ⟶ Spec (CommRingCat.of k))
    (p : B ⟶ A) (hp : p ≫ sA = sB) (T : A.Opens)
    (s : (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2).val.obj (op T)) :
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2).val.obj
      (op (p ⁻¹ᵁ T)) :=
  (SchemeKaehlerExteriorPullbackTransport.map sA p sB hp 2).val.app (op (p ⁻¹ᵁ T))
    (pullbackSection p (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) T s)

end KltDP.Geometry.NormalizedDifferentialCoefficientOrder

#check @KltDP.Geometry.NormalizedDifferentialCoefficientOrder.imageSection
