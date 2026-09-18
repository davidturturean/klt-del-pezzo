import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.CanonicalExteriorIsoCancellation

/-!
# Comparisons for the original exterior maps on a common open

The two original open differentials identify the pulled exterior sheaves.
These comparisons retain the original maps for the subsequent naturality square.
No comparison map, differential compatibility, or canonical divisor equality
is assumed. The result applies to every exterior degree.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CanonicalExteriorCommonOpen

open SchemeKaehlerSheaf SchemeKaehlerExteriorPullbackTransport

variable {k : Type u} [CommRing k] {S V W X : Scheme.{u}}

/-- The original triangles over the base determine the structure equality
on the same common open. -/
theorem structure_eq
    (σ : X ⟶ Spec (CommRingCat.of k)) (π : S ⟶ X) (v : V ⟶ X)
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (hS : π ≫ σ = fS) (hV : v ≫ σ = fV)
    (iS : W ⟶ S) (iV : W ⟶ V) (hcomm : iS ≫ π = iV ≫ v) :
    iS ≫ fS = iV ≫ fV := by
  rw [← hS, ← hV, ← Category.assoc, hcomm, Category.assoc]

/-- The comparison is the first original open differential followed by
the inverse of the second original open differential. -/
def exteriorIso
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (iS : W ⟶ S) (iV : W ⟶ V) [IsOpenImmersion iS] [IsOpenImmersion iV]
    (h : iS ≫ fS = iV ≫ fV) (n : ℕ) :
    (schemeModulePullback iS).obj (SchemeExteriorPower.sheaf (baseRingSheaf fS) n) ≅
      (schemeModulePullback iV).obj (SchemeExteriorPower.sheaf (baseRingSheaf fV) n) := by
  letI := map_isIso fS iS (iV ≫ fV) h n
  letI := map_isIso fV iV (iV ≫ fV) rfl n
  exact CanonicalExteriorIsoCancellation.comparison
    (asIso (map fS iS (iV ≫ fV) h n)) (asIso (map fV iV (iV ≫ fV) rfl n))

/-- The same comparison is normalized by the original open differential maps. -/
theorem exteriorIso_hom_comp
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (iS : W ⟶ S) (iV : W ⟶ V) [IsOpenImmersion iS] [IsOpenImmersion iV]
    (h : iS ≫ fS = iV ≫ fV) (n : ℕ) :
    (exteriorIso fS fV iS iV h n).hom ≫ map fV iV (iV ≫ fV) rfl n =
      map fS iS (iV ≫ fV) h n := by
  letI := map_isIso fS iS (iV ≫ fV) h n
  letI := map_isIso fV iV (iV ≫ fV) rfl n
  exact CanonicalExteriorIsoCancellation.comparison_hom_comp
    (asIso (map fS iS (iV ≫ fV) h n)) (asIso (map fV iV (iV ≫ fV) rfl n))

/-- The source comparison uses only original pullback composition and the
given equality of original scheme morphisms. -/
def commonSourceIso
    (σ : X ⟶ Spec (CommRingCat.of k)) (π : S ⟶ X) (v : V ⟶ X)
    (iS : W ⟶ S) (iV : W ⟶ V) (hcomm : iS ≫ π = iV ≫ v) (n : ℕ) :
    (schemeModulePullback iS).obj
        ((schemeModulePullback π).obj (SchemeExteriorPower.sheaf (baseRingSheaf σ) n)) ≅
      (schemeModulePullback iV).obj
        ((schemeModulePullback v).obj (SchemeExteriorPower.sheaf (baseRingSheaf σ) n)) :=
  CanonicalExteriorIsoCancellation.comparison
    (sourceIso σ π iS (iV ≫ v) hcomm n) (sourceIso σ v iV (iV ≫ v) rfl n)

theorem commonSourceIso_hom_comp
    (σ : X ⟶ Spec (CommRingCat.of k)) (π : S ⟶ X) (v : V ⟶ X)
    (iS : W ⟶ S) (iV : W ⟶ V) (hcomm : iS ≫ π = iV ≫ v) (n : ℕ) :
    (commonSourceIso σ π v iS iV hcomm n).hom ≫
        (sourceIso σ v iV (iV ≫ v) rfl n).hom =
      (sourceIso σ π iS (iV ≫ v) hcomm n).hom :=
  CanonicalExteriorIsoCancellation.comparison_hom_comp
    (sourceIso σ π iS (iV ≫ v) hcomm n) (sourceIso σ v iV (iV ≫ v) rfl n)

end KltDP.Geometry.CanonicalExteriorCommonOpen
