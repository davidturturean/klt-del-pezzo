import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.DominantCartierPullbackOpenRestriction
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# Canonical Cartier representatives under an original open immersion

The original signed Cartier pullback module comparison, the given
canonical module isomorphism, and the original exterior differential
give the comparison. The field-structure equality is transported by
the existing differential map. Isomorphisms are covered automatically.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalCartierOpenPullback

local instance openGenericPointPreserving {S T : Scheme.{u}}
    [IsIntegral S] [IsIntegral T] (e : S ⟶ T) [IsOpenImmersion e] :
    GenericPointPreserving e := ⟨genericPoint_eq_of_isOpenImmersion e⟩

/-- The original signed pullback of a genuine canonical Cartier
representative represents the original source differential exterior. -/
def canonicalModuleIso
    {k : Type u} [CommRing k] {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]
    (e : S ⟶ T) [IsOpenImmersion e]
    (fT : T ⟶ Spec (CommRingCat.of k)) (fS : S ⟶ Spec (CommRingCat.of k))
    (he : e ≫ fT = fS) (KT : CartierDivisor T)
    (eKT : cartierDivisorModule T KT ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fT 2) :
    cartierDivisorModule S (DominantCartierPullback.pullbackHom e KT) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fS 2 := by
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso fT e fS he 2
  exact (DominantCartierPullback.modulePullbackIso e KT).symm ≪≫
    (schemeModulePullback e).mapIso eKT ≪≫
      asIso (SchemeKaehlerExteriorPullbackTransport.map fT e fS he 2)

/-- Cancelling the original Cartier module comparison recovers the
original exterior differential, composed with the original canonical frame. -/
theorem canonicalModuleIso_comp
    {k : Type u} [CommRing k] {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]
    (e : S ⟶ T) [IsOpenImmersion e]
    (fT : T ⟶ Spec (CommRingCat.of k)) (fS : S ⟶ Spec (CommRingCat.of k))
    (he : e ≫ fT = fS) (KT : CartierDivisor T)
    (eKT : cartierDivisorModule T KT ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fT 2) :
    (DominantCartierPullback.modulePullbackIso e KT).hom ≫
        (canonicalModuleIso e fT fS he KT eKT).hom =
      (schemeModulePullback e).map eKT.hom ≫
        SchemeKaehlerExteriorPullbackTransport.map fT e fS he 2 := by
  simp only [canonicalModuleIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Category.assoc, Iso.hom_inv_id_assoc]

end KltDP.Geometry.CanonicalCartierOpenPullback

#check @KltDP.Geometry.CanonicalCartierOpenPullback.canonicalModuleIso
#check @KltDP.Geometry.CanonicalCartierOpenPullback.canonicalModuleIso_comp
#print axioms KltDP.Geometry.CanonicalCartierOpenPullback.canonicalModuleIso
#print axioms KltDP.Geometry.CanonicalCartierOpenPullback.canonicalModuleIso_comp
