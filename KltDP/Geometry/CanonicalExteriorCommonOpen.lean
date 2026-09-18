import KltDP.Geometry.CanonicalExteriorCommonOpenComparison

/-!
# The original exterior-map square on a common open

Prove cancellation in an arbitrary category before substituting the actual
sheaf maps. The specialization retains the original maps, their original
pullback-composition isomorphisms, and the original structure triangles.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CanonicalExteriorCommonOpen

open SchemeKaehlerSheaf SchemeKaehlerExteriorPullbackTransport

private theorem square_of_normalizations
    {𝒞 : Type*} [Category 𝒞] {A B C D E F : 𝒞}
    (a : A ⟶ B) (b : C ⟶ D) (c : A ⟶ C) (d : B ⟶ D)
    (u : A ⟶ E) (v : C ⟶ E) (r : B ⟶ F) (s : D ⟶ F) (t : E ⟶ F)
    [Mono s] (hc : c ≫ v = u) (hd : d ≫ s = r)
    (ha : a ≫ r = u ≫ t) (hb : b ≫ s = v ≫ t) :
    a ≫ d = c ≫ b := by
  apply (cancel_mono s).mp
  calc
    (a ≫ d) ≫ s = a ≫ r := by rw [Category.assoc, hd]
    _ = u ≫ t := ha
    _ = c ≫ (v ≫ t) := by rw [← Category.assoc, hc]
    _ = (c ≫ b) ≫ s := by rw [Category.assoc, hb]

variable {k : Type u} [CommRing k] {S V W X : Scheme.{u}}

private theorem composite_structure
    (σ : X ⟶ Spec (CommRingCat.of k)) (v : V ⟶ X)
    (fV : V ⟶ Spec (CommRingCat.of k)) (hV : v ≫ σ = fV) (iV : W ⟶ V) :
    (iV ≫ v) ≫ σ = iV ≫ fV := by
  rw [Category.assoc, hV]

private theorem left_composition
    (σ : X ⟶ Spec (CommRingCat.of k)) (π : S ⟶ X) (v : V ⟶ X)
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (hS : π ≫ σ = fS) (hV : v ≫ σ = fV)
    (iS : W ⟶ S) (iV : W ⟶ V) (hcomm : iS ≫ π = iV ≫ v) (n : ℕ) :
    (schemeModulePullback iS).map (map σ π fS hS n) ≫
        map fS iS (iV ≫ fV) (structure_eq σ π v fS fV hS hV iS iV hcomm) n =
      (sourceIso σ π iS (iV ≫ v) hcomm n).hom ≫
        map σ (iV ≫ v) (iV ≫ fV) (composite_structure σ v fV hV iV) n :=
  map_comp_sourceIso σ π iS fS hS (iV ≫ v) hcomm (iV ≫ fV)
    (structure_eq σ π v fS fV hS hV iS iV hcomm) (composite_structure σ v fV hV iV) n

private theorem right_composition
    (σ : X ⟶ Spec (CommRingCat.of k)) (v : V ⟶ X)
    (fV : V ⟶ Spec (CommRingCat.of k)) (hV : v ≫ σ = fV) (iV : W ⟶ V) (n : ℕ) :
    (schemeModulePullback iV).map (map σ v fV hV n) ≫ map fV iV (iV ≫ fV) rfl n =
      (sourceIso σ v iV (iV ≫ v) rfl n).hom ≫
        map σ (iV ≫ v) (iV ≫ fV) (composite_structure σ v fV hV iV) n :=
  map_comp_sourceIso σ v iV fV hV (iV ≫ v) rfl (iV ≫ fV) rfl
    (composite_structure σ v fV hV iV) n

private theorem right_map_mono
    (fV : V ⟶ Spec (CommRingCat.of k)) (iV : W ⟶ V) [IsOpenImmersion iV] (n : ℕ) :
    Mono (map fV iV (iV ≫ fV) rfl n) := by
  letI := map_isIso fV iV (iV ≫ fV) rfl n
  infer_instance

/-- The actual common-open comparison commutes with both original exterior
maps from the base. The structure equality is derived from the original diagram. -/
theorem exteriorIso_natural
    (σ : X ⟶ Spec (CommRingCat.of k)) (π : S ⟶ X) (v : V ⟶ X)
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (hS : π ≫ σ = fS) (hV : v ≫ σ = fV)
    (iS : W ⟶ S) (iV : W ⟶ V) [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v) (n : ℕ) :
    (schemeModulePullback iS).map (map σ π fS hS n) ≫
        (exteriorIso fS fV iS iV (structure_eq σ π v fS fV hS hV iS iV hcomm) n).hom =
      (commonSourceIso σ π v iS iV hcomm n).hom ≫
        (schemeModulePullback iV).map (map σ v fV hV n) := by
  letI := right_map_mono fV iV n
  exact square_of_normalizations
    ((schemeModulePullback iS).map (map σ π fS hS n))
    ((schemeModulePullback iV).map (map σ v fV hV n))
    (commonSourceIso σ π v iS iV hcomm n).hom
    (exteriorIso fS fV iS iV (structure_eq σ π v fS fV hS hV iS iV hcomm) n).hom
    (sourceIso σ π iS (iV ≫ v) hcomm n).hom
    (sourceIso σ v iV (iV ≫ v) rfl n).hom
    (map fS iS (iV ≫ fV) (structure_eq σ π v fS fV hS hV iS iV hcomm) n)
    (map fV iV (iV ≫ fV) rfl n)
    (map σ (iV ≫ v) (iV ≫ fV) (composite_structure σ v fV hV iV) n)
    (commonSourceIso_hom_comp σ π v iS iV hcomm n)
    (exteriorIso_hom_comp fS fV iS iV (structure_eq σ π v fS fV hS hV iS iV hcomm) n)
    (left_composition σ π v fS fV hS hV iS iV hcomm n)
    (right_composition σ v fV hV iV n)

end KltDP.Geometry.CanonicalExteriorCommonOpen
