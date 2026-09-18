import KltDP.Geometry.AffineDifferentialExteriorOriginalStalk
import KltDP.Geometry.AffineDifferentialExteriorPullbackComparison

/-!
# The original affine exterior pullback on actual stalk germs

Take the stalk of the existing intrinsic exterior pullback map, then the
normalized comparison with the original structure-stalk differentials.
The existing pullback-unit formula and pinned Spec stalk naturality identify
its value with the wedge of the images under the original scheme stalk map.
No new map compatibility or canonical coefficient equality is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorPullbackStalk

open SchemeKaehlerSheaf AffineDifferentialExteriorOriginalStalk
open AffineDifferentialExteriorStalkEvaluation (stalkAffineAlgebra stalkGroundAlgebra stalkExteriorModule)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (p : PrimeSpectrum B)

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "j" => Spec.map (CommRingCat.ofHom (algebraMap A B))
local notation "Bₚ" => AffineDifferentialExteriorStalkEvaluation.originalStalkRing B p
local notation "Ωₚ" => (KaehlerDifferential k Bₚ)

/-- The original pulled intrinsic exterior sheaf over the original affine ring B. -/
abbrev pullbackPresheaf (n : ℕ) :
    TopCat.Presheaf (ModuleCat.{u} B) (PrimeSpectrum.Top B) :=
  (AffineKaehlerStalkLocalization.modulePresheafFunctor B).obj
    ((schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf fA) n))

/-- The actual adjunction unit applied to the original affine differential wedge. -/
def originalUnitWedge (n : ℕ) (v : Fin n → A) :
    (pullbackPresheaf k A B n).obj (op ⊤) :=
  (((schemeModulePullbackPushforwardAdjunction j).unit.app
    (SchemeExteriorPower.sheaf (baseRingSheaf fA) n)).val.app (op ⊤))
      (SchemeExteriorPower.wedge (baseRingSheaf fA) n ⊤
        (fun i => (baseRingDerivation fA).d (StructureSheaf.toOpen A ⊤ (v i))))

private theorem originalMap_unit_wedge (n : ℕ) (v : Fin n → A) :
    (AffineDifferentialExteriorPullbackComparison.intrinsicMap k A B n).val.app (op ⊤)
        (originalUnitWedge k A B n v) =
      SchemeExteriorPower.wedge (baseRingSheaf fB) n ⊤
        (fun i => (baseRingDerivation fB).d
          (StructureSheaf.toOpen B ⊤ (algebraMap A B (v i)))) :=
  SchemeKaehlerExteriorPullbackTransport.map_unit_wedge_toOpen
    fA (algebraMap A B) fB (AffineKaehlerPullbackComparison.baseMap_comp k A B) n v

variable {n : ℕ} (b : Basis (Fin n) B (KaehlerDifferential k B))

/-- The original pullback morphism on the original stalk, followed by the
previously normalized native comparison. -/
def pullbackStalkMap :
    letI := stalkAffineAlgebra (A := B) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
    letI := stalkExteriorModule k B p n
    (pullbackPresheaf k A B n).stalk p ⟶ ModuleCat.of B (⋀[Bₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := B) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
  letI := stalkExteriorModule k B p n
  exact (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} B)
    (X := PrimeSpectrum.Top B) p).map
      ((AffineKaehlerStalkLocalization.modulePresheafFunctor B).map
        (AffineDifferentialExteriorPullbackComparison.intrinsicMap k A B n)) ≫
    comparisonOfBasis k B p b

/-- The original map on the unit wedge is evaluated through the original B germs. -/
theorem pullbackStalkMap_germ_unit_toStalk (v : Fin n → A) :
    letI := stalkAffineAlgebra (A := B) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
    letI := stalkExteriorModule k B p n
    pullbackStalkMap k A B p b
        ((pullbackPresheaf k A B n).germ ⊤ p trivial (originalUnitWedge k A B n v)) =
      exteriorPower.ιMulti Bₚ n
        (fun i => KaehlerDifferential.D k Bₚ
          (StructureSheaf.toStalk B p (algebraMap A B (v i)))) := by
  letI := stalkAffineAlgebra (A := B) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
  letI := stalkExteriorModule k B p n
  change comparisonOfBasis k B p b
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} B)
      (X := PrimeSpectrum.Top B) p).map
        ((AffineKaehlerStalkLocalization.modulePresheafFunctor B).map
          (AffineDifferentialExteriorPullbackComparison.intrinsicMap k A B n)) _) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change comparisonOfBasis k B p b ((presheaf k B n).germ ⊤ p trivial
    ((AffineDifferentialExteriorPullbackComparison.intrinsicMap k A B n).val.app
      (op ⊤) (originalUnitWedge k A B n v))) = _
  rw [originalMap_unit_wedge]
  exact comparisonOfBasis_germ_wedge_D k B p b ⊤ trivial
    (fun i => algebraMap A B (v i))

private theorem original_stalkMap_toStalk (a : A) :
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap p).hom
        (StructureSheaf.toStalk A
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))).base p) a) =
      StructureSheaf.toStalk B p (algebraMap A B a) :=
  AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom (algebraMap A B)) p a

/-- The output is the native wedge of the images under the literal original
scheme stalk map, with all affine scalar and point comparisons discharged. -/
theorem pullbackStalkMap_germ_unit_stalkMap (v : Fin n → A) :
    letI := stalkAffineAlgebra (A := B) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
    letI := stalkExteriorModule k B p n
    pullbackStalkMap k A B p b
        ((pullbackPresheaf k A B n).germ ⊤ p trivial (originalUnitWedge k A B n v)) =
      exteriorPower.ιMulti Bₚ n
        (fun i => KaehlerDifferential.D k Bₚ
          (((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap p).hom
            (StructureSheaf.toStalk A
              ((Spec.map (CommRingCat.ofHom (algebraMap A B))).base p) (v i)))) := by
  letI := stalkAffineAlgebra (A := B) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
  letI := stalkExteriorModule k B p n
  refine (pullbackStalkMap_germ_unit_toStalk k A B p b v).trans ?_
  apply congrArg (exteriorPower.ιMulti Bₚ n)
  funext i
  exact congrArg (KaehlerDifferential.D k Bₚ)
    (original_stalkMap_toStalk (A := A) (B := B) (p := p) (v i)).symm

end KltDP.Geometry.AffineDifferentialExteriorPullbackStalk

#check @KltDP.Geometry.AffineDifferentialExteriorPullbackStalk.pullbackStalkMap_germ_unit_stalkMap
#print axioms KltDP.Geometry.AffineDifferentialExteriorPullbackStalk.pullbackStalkMap_germ_unit_stalkMap
