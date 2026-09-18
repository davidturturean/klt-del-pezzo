import KltDP.Geometry.AffineDifferentialExteriorOriginalStalk
import KltDP.Geometry.OriginalDifferentialImageWedge

/-!
# The original affine differential image on actual Cartier neighborhoods

Keep the original source and target affine schemes and every original
open restriction. The pinned Spec section map fixes the actual numerator
map, so the original intrinsic/native stalk comparison evaluates the same
differential image section on any neighborhood of the source point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineSpecDifferentialImageStalk

open SchemeKaehlerSheaf AffineDifferentialExteriorOriginalStalk
open NormalizedDifferentialCoefficientOrder
open AffineDifferentialExteriorStalkEvaluation
  (originalStalkRing stalkAffineAlgebra stalkGroundAlgebra stalkExteriorModule)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem appLE_toOpen {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (U : (Spec (CommRingCat.of A)).Opens)
    (V : (Spec (CommRingCat.of B)).Opens)
    (hVU : V ≤ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U) :
    StructureSheaf.toOpen A U ≫ (Spec.map (CommRingCat.ofHom φ)).appLE U V hVU =
      CommRingCat.ofHom φ ≫ StructureSheaf.toOpen B V := by
  have h : StructureSheaf.toOpen A U ≫ (Spec.map (CommRingCat.ofHom φ)).app U =
      CommRingCat.ofHom φ ≫ StructureSheaf.toOpen B
        ((Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U) :=
    StructureSheaf.toOpen_comp_comap φ U
  have hres : StructureSheaf.toOpen B ((Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U) ≫
      (Spec (CommRingCat.of B)).presheaf.map (homOfLE hVU).op =
        StructureSheaf.toOpen B V :=
    StructureSheaf.toOpen_res B _ V (homOfLE hVU)
  unfold Scheme.Hom.appLE
  rw [← Category.assoc, h, Category.assoc, hres]

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →+* B)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (U : (Spec (CommRingCat.of A)).Opens) (V : (Spec (CommRingCat.of B)).Opens)
    (hVU : V ≤ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U) (v : Fin 2 → A)

include hφ

/-- The literal original image section is the wedge of the literal
original mapped numerators on every actual smaller source open. -/
theorem imageSection_wedge_d_restrict :
    (SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k B)))) 2).val.map
        (homOfLE hVU).op
      (imageSection (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k B))) (Spec.map (CommRingCat.ofHom φ)) hφ U
        (SchemeExteriorPower.wedge
          (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 U
          (fun i => (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
            (StructureSheaf.toOpen A U (v i))))) =
      SchemeExteriorPower.wedge
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k B)))) 2 V
        (fun i => (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k B)))).d
          (StructureSheaf.toOpen B V (φ (v i)))) := by
  have hscalar (i : Fin 2) :
      (Spec.map (CommRingCat.ofHom φ)).appLE U V hVU
          (StructureSheaf.toOpen A U (v i)) =
        StructureSheaf.toOpen B V (φ (v i)) :=
    ConcreteCategory.congr_hom (appLE_toOpen (A := A) (B := B) φ U V hVU) (v i)
  exact OriginalDifferentialImageWedge.imageSection_wedge_d_restrict_of_appLE
    (k := k) (X := Spec (CommRingCat.of A)) (Y := Spec (CommRingCat.of B))
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (Spec.map (CommRingCat.ofHom (algebraMap k B))) (Spec.map (CommRingCat.ofHom φ))
    hφ U V hVU (fun i => StructureSheaf.toOpen A U (v i))
    (fun i => StructureSheaf.toOpen B V (φ (v i))) hscalar

/-- The original intrinsic stalk comparison evaluates the exact image
section used by the original Cartier coefficient producer. -/
theorem comparison_imageSection_wedge_d (p : PrimeSpectrum B) (hp : p ∈ V)
    (b : Basis (Fin 2) B (KaehlerDifferential k B)) :
    letI := stalkAffineAlgebra (A := B) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
    letI := stalkExteriorModule k B p 2
    comparisonOfBasis k B p b ((presheaf k B 2).germ V p hp
      ((SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k B)))) 2).val.map
          (homOfLE hVU).op
        (imageSection (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k B))) (Spec.map (CommRingCat.ofHom φ)) hφ U
          (SchemeExteriorPower.wedge
            (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 U
            (fun i => (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
              (StructureSheaf.toOpen A U (v i))))))) =
      exteriorPower.ιMulti (originalStalkRing B p) 2
        (fun i => KaehlerDifferential.D k (originalStalkRing B p)
          (StructureSheaf.toStalk B p (φ (v i)))) := by
  letI := stalkAffineAlgebra (A := B) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
  letI := stalkExteriorModule k B p 2
  have hsection := imageSection_wedge_d_restrict (k := k) (A := A) (B := B)
    (φ := φ) (hφ := hφ) (U := U) (V := V) (hVU := hVU) (v := v)
  have hstalk := congrArg (fun s : (presheaf k B 2).obj (op V) =>
    comparisonOfBasis k B p b ((presheaf k B 2).germ V p hp s)) hsection
  exact hstalk.trans (comparisonOfBasis_germ_wedge_D k B p b V hp (fun i => φ (v i)))

end KltDP.Geometry.AffineSpecDifferentialImageStalk

#check @KltDP.Geometry.AffineSpecDifferentialImageStalk.imageSection_wedge_d_restrict
#check @KltDP.Geometry.AffineSpecDifferentialImageStalk.comparison_imageSection_wedge_d
#print axioms KltDP.Geometry.AffineSpecDifferentialImageStalk.comparison_imageSection_wedge_d
