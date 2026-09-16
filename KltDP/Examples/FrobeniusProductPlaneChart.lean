import KltDP.Examples.FrobeniusBlowupSmooth
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Geometry.ProjectiveLineComparison
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The polynomial plane chart in the actual projective product

The polynomial--tensor equivalence and the affine fiber-product theorem
identify `Spec k[u][v]` with the product of two affine lines over `k`.
The two existing first charts of the projective line induce an open
immersion into the actual scheme fiber product. Its projections are the
original polynomial coordinates, and its structure map preserves the
original coefficient field.

Reuse: Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
`RingTheory/PolynomialAlgebra.lean` (`_root_.polyEquivTensor`) and
`AlgebraicGeometry/Pullbacks.lean` (`pullbackSpecIso` and
`Scheme.pullback_map_isOpenImmersion`), together with the existing actual
projective-line chart maps. No product-chart identification is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Examples.FrobeniusProductPlaneChart

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusProjectivePoints
open ProjectiveLineComparison

variable {k : Type u} [Field k]

/-- The first polynomial coordinate is the coefficient variable `u`. -/
def firstCoordinateMap : Polynomial k →+* planeRing k := Polynomial.C

/-- The second polynomial coordinate is the outer variable `v`. -/
def secondCoordinateMap : Polynomial k →+* planeRing k :=
  Polynomial.mapRingHom Polynomial.C

@[simp] theorem firstCoordinateMap_X :
    firstCoordinateMap (Polynomial.X : Polynomial k) = uCoord := rfl

@[simp] theorem secondCoordinateMap_X :
    secondCoordinateMap (Polynomial.X : Polynomial k) = vCoord :=
  Polynomial.map_X _

@[simp] theorem firstCoordinateMap_C (r : k) :
    firstCoordinateMap (Polynomial.C r) = planeConstants r := rfl

@[simp] theorem secondCoordinateMap_C (r : k) :
    secondCoordinateMap (Polynomial.C r) = planeConstants r :=
  Polynomial.map_C _

/-- The actual structure morphism of each polynomial affine line. -/
def lineStructure : Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

/-- The actual polynomial plane is the fiber product of the two affine lines. -/
def planeProductIso : Spec (CommRingCat.of (planeRing k)) ≅
    pullback (lineStructure (k := k)) lineStructure :=
  Scheme.Spec.mapIso
    (_root_.polyEquivTensor k (Polynomial k)).symm.toRingEquiv.toCommRingCatIso.op ≪≫
      (pullbackSpecIso k (Polynomial k) (Polynomial k)).symm

@[reassoc] theorem planeProductIso_hom_fst :
    (planeProductIso (k := k)).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) := by
  change (Spec.map (CommRingCat.ofHom
      (_root_.polyEquivTensor k (Polynomial k)).symm.toRingHom) ≫
        (pullbackSpecIso k (Polynomial k) (Polynomial k)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg (fun f : Polynomial k →+* planeRing k => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro p
  change (_root_.polyEquivTensor k (Polynomial k)).symm
    (p ⊗ₜ[k] (1 : Polynomial k)) = Polynomial.C p
  simpa only [Polynomial.map_one, Polynomial.smul_eq_C_mul, mul_one] using
    _root_.polyEquivTensor_symm_apply_tmul_eq_smul k (Polynomial k) p 1

@[reassoc] theorem planeProductIso_hom_snd :
    (planeProductIso (k := k)).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) := by
  change (Spec.map (CommRingCat.ofHom
      (_root_.polyEquivTensor k (Polynomial k)).symm.toRingHom) ≫
        (pullbackSpecIso k (Polynomial k) (Polynomial k)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  apply congrArg (fun f : Polynomial k →+* planeRing k => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro p
  change (_root_.polyEquivTensor k (Polynomial k)).symm
    ((1 : Polynomial k) ⊗ₜ[k] p) = p.map (algebraMap k (Polynomial k))
  simpa only [one_smul] using
    _root_.polyEquivTensor_symm_apply_tmul_eq_smul k (Polynomial k) 1 p

/-- The actual product of the two first projective-line open charts. -/
def affineProductChart : pullback (lineStructure (k := k)) lineStructure ⟶ projectiveProduct k :=
  pullback.map lineStructure lineStructure
    (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)
    (polynomialChartMap k 0) (polynomialChartMap k 0) (𝟙 _)
    (by rw [Category.comp_id, polynomialChartMap_structureMap]; rfl)
    (by rw [Category.comp_id, polynomialChartMap_structureMap]; rfl)

instance affineProductChart_isOpenImmersion : IsOpenImmersion (affineProductChart (k := k)) := by
  unfold affineProductChart
  infer_instance

@[reassoc] theorem affineProductChart_fst :
    affineProductChart (k := k) ≫ pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      pullback.fst lineStructure lineStructure ≫ polynomialChartMap k 0 :=
  pullback.lift_fst _ _ _

@[reassoc] theorem affineProductChart_snd :
    affineProductChart (k := k) ≫ pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      pullback.snd lineStructure lineStructure ≫ polynomialChartMap k 0 :=
  pullback.lift_snd _ _ _

/-- The actual affine-plane open chart in the original projective product. -/
def planeChart : Spec (CommRingCat.of (planeRing k)) ⟶ projectiveProduct k :=
  planeProductIso.hom ≫ affineProductChart

instance planeChart_isOpenImmersion : IsOpenImmersion (planeChart (k := k)) := by
  unfold planeChart
  infer_instance

/-- The first product projection has polynomial coordinate `u`. -/
@[reassoc] theorem planeChart_fst :
    planeChart (k := k) ≫ pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) ≫ polynomialChartMap k 0 := by
  rw [planeChart, Category.assoc, affineProductChart_fst,
    ← Category.assoc, planeProductIso_hom_fst]

/-- The second product projection has polynomial coordinate `v`. -/
@[reassoc] theorem planeChart_snd :
    planeChart (k := k) ≫ pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) ≫ polynomialChartMap k 0 := by
  rw [planeChart, Category.assoc, affineProductChart_snd,
    ← Category.assoc, planeProductIso_hom_snd]

/-- The chart preserves the original coefficient-field structure morphism. -/
@[reassoc] theorem planeChart_structure :
    planeChart (k := k) ≫ projectiveProductToSpec = planeStructure := by
  rw [projectiveProductToSpec, ← Category.assoc, planeChart_fst,
    Category.assoc, polynomialChartMap_structureMap, ← Spec.map_comp]; rfl

end KltDP.Examples.FrobeniusProductPlaneChart
