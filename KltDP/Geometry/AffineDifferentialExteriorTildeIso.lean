import KltDP.Geometry.AffineModuleTildeExteriorIso
import KltDP.Geometry.AffineDifferentialExteriorTildeMap

/-!
# The original native-to-intrinsic affine differential exterior isomorphism

For a finite free native differential module, the proved original tilde map
and the original affine Kähler exterior comparison give an isomorphism with
the intrinsic differential exterior sheaf. Its forward map is exactly the
already normalized native-to-intrinsic map. The inverse retains the original
coordinate wedges, and both compositions are proved on the actual sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorTildeMap

open AffineKaehlerTildeDerivation AffineDifferentialExteriorNormalization
open SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
variable {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

/-- The actual native top differential tilde is identified with the original
intrinsic exterior sheaf by the already constructed map. -/
def isoOfBasis :
    ((differentialModule k A).exteriorPower n).tilde ≅
      SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n :=
  AffineModuleTildeExteriorMap.isoOfBasis (differentialModule k A) b ≪≫
    (exteriorIso k A n).symm

theorem isoOfBasis_hom : (isoOfBasis k A b).hom = map k A n := rfl

include b in
/-- The original forward map itself is invertible; it is not replaced. -/
theorem map_isIso : IsIso (map k A n) := by
  change IsIso (isoOfBasis k A b).hom
  infer_instance

def inverseOfBasis :
    SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n ⟶
        ((differentialModule k A).exteriorPower n).tilde :=
  (isoOfBasis k A b).inv

theorem inverseOfBasis_eq :
    inverseOfBasis k A b = (exteriorIso k A n).hom ≫
      AffineModuleTildeExteriorMap.inverseOfBasis (differentialModule k A) b := rfl

theorem map_inverseOfBasis : map k A n ≫ inverseOfBasis k A b = 𝟙 _ :=
  (isoOfBasis k A b).hom_inv_id

theorem inverseOfBasis_map : inverseOfBasis k A b ≫ map k A n = 𝟙 _ :=
  (isoOfBasis k A b).inv_hom_id

/-- The actual inverse takes each intrinsic coordinate wedge back to its
original native differential wedge on every original open. -/
theorem inverseOfBasis_wedge_D (U : Opens (PrimeSpectrum A)) (v : Fin n → A) :
    (inverseOfBasis k A b).val.app (op U)
        (SchemeExteriorPower.wedge
          (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n U
          (fun i => (baseRingDerivation
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
              (StructureSheaf.toOpen A U (v i)))) =
      ModuleCat.Tilde.toOpen ((differentialModule k A).exteriorPower n) U
        (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i))) := by
  refine (congrArg ((inverseOfBasis k A b).val.app (op U))
    (map_toOpen_D k A n U v).symm).trans ?_
  exact ((_root_.SheafOfModules.evaluation
    (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
      (isoOfBasis k A b)).toLinearEquiv.symm_apply_apply _

/-- Original standard smoothness of relative dimension two supplies the
actual finite differential basis, with no frame or isomorphism premise. -/
def standardSmoothIso [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    ((differentialModule k A).exteriorPower 2).tilde ≅
      SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 :=
  isoOfBasis k A (AffineTopDifferentialFrame.standardSmoothDifferentialBasis k A)

theorem standardSmoothIso_hom [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    (standardSmoothIso k A).hom = map k A 2 := rfl

end KltDP.Geometry.AffineDifferentialExteriorTildeMap
