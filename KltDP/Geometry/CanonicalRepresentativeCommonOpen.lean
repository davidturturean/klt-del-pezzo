import KltDP.Geometry.CanonicalExteriorCommonOpen
import KltDP.Geometry.CartierSchemePullbackOpenImmersion
import KltDP.Geometry.CartierPicardKernel

/-!
# Actual Cartier representatives on an original common open

Each original Cartier divisor is identified with its own original exterior
sheaf. The original open differential maps construct the comparison on the
common open; no cross-model comparison is supplied. The actual restricted
Cartier divisors consequently differ by a principal divisor. Equality of
chosen coefficients requires further normalization and is not asserted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CanonicalRepresentativeCommonOpen

open SchemeKaehlerSheaf SchemeKaehlerExteriorPullbackTransport
open CanonicalExteriorCommonOpen OpenImmersionRational

variable {k : Type u} [CommRing k] {S V W : Scheme.{u}}
    [IsIntegral S] [IsIntegral V] [IsIntegral W]
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (iS : W ⟶ S) (iV : W ⟶ V) [IsOpenImmersion iS] [IsOpenImmersion iV]
    (h : iS ≫ fS = iV ≫ fV) (n : ℕ)
    (D : CartierDivisor S) (E : CartierDivisor V)
    (eD : cartierDivisorModule S D ≅ SchemeExteriorPower.sheaf (baseRingSheaf fS) n)
    (eE : cartierDivisorModule V E ≅ SchemeExteriorPower.sheaf (baseRingSheaf fV) n)

/-- The two original representative modules are compared using the actual
open exterior differential maps. -/
def moduleIso :
    (schemeModulePullback iS).obj (cartierDivisorModule S D) ≅
      (schemeModulePullback iV).obj (cartierDivisorModule V E) :=
  CanonicalExteriorIsoCancellation.comparison
    ((schemeModulePullback iS).mapIso eD ≪≫ exteriorIso fS fV iS iV h n)
    ((schemeModulePullback iV).mapIso eE)

private theorem moduleIso_normalization :
    (moduleIso fS fV iS iV h n D E eD eE).hom ≫ (schemeModulePullback iV).map eE.hom =
      (schemeModulePullback iS).map eD.hom ≫ (exteriorIso fS fV iS iV h n).hom :=
  CanonicalExteriorIsoCancellation.comparison_hom_comp
    ((schemeModulePullback iS).mapIso eD ≪≫ exteriorIso fS fV iS iV h n)
    ((schemeModulePullback iV).mapIso eE)

/-- Following the comparison by the second representative identification
and its original open differential gives exactly the first original map. -/
theorem moduleIso_hom_comp :
    (moduleIso fS fV iS iV h n D E eD eE).hom ≫
        ((schemeModulePullback iV).map eE.hom ≫ map fV iV (iV ≫ fV) rfl n) =
      (schemeModulePullback iS).map eD.hom ≫ map fS iS (iV ≫ fV) h n := by
  rw [← Category.assoc, moduleIso_normalization, Category.assoc, exteriorIso_hom_comp]

/-- The same comparison between the modules of the actual Cartier restrictions. -/
def restrictionModuleIso :
    cartierDivisorModule W (cartierRestrictionHom iS D) ≅
      cartierDivisorModule W (cartierRestrictionHom iV E) :=
  (cartierModulePullbackIso iS D).symm ≪≫ moduleIso fS fV iS iV h n D E eD eE ≪≫
    cartierModulePullbackIso iV E

include h eD eE in
/-- The actual restricted Cartier representatives differ by an actual
principal Cartier divisor on this same common open. -/
theorem exists_principal_difference :
    ∃ a : W.functionFieldˣ,
      cartierRestrictionHom iS D - cartierRestrictionHom iV E =
        principalCartierDivisorHom W (Additive.ofMul a) := by
  have hPic := cartierPicardClass_eq_of_iso W
    (cartierRestrictionHom iS D) (cartierRestrictionHom iV E)
    (restrictionModuleIso fS fV iS iV h n D E eD eE)
  apply (cartierPicardClass_eq_one_iff W
    (cartierRestrictionHom iS D - cartierRestrictionHom iV E)).mp
  rw [cartierPicardClass_sub, hPic]
  exact div_self' (cartierPicardClass W (cartierRestrictionHom iV E))

end KltDP.Geometry.CanonicalRepresentativeCommonOpen
