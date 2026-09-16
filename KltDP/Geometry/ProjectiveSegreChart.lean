import KltDP.Geometry.ProjectiveChartNormal
import KltDP.Examples.FrobeniusBlowupSmooth

/-!
# The Segre map on the chart `D(x₀ y₀)` of `P¹ ×_k P¹`

On the product chart with coordinates `u = x₁/x₀`, `v = y₁/y₀` the Segre map
`[x₀:x₁] × [y₀:y₁] ↦ [x₀y₀ : x₁y₀ : x₀y₁ : x₁y₁]` lands in the chart `D(z₀)` of `P³` and is the
morphism of affine schemes `Spec k[u][v] ⟶ Spec k[a,b,c]` given by `a ↦ u`, `b ↦ v`, `c ↦ uv`:

* `segreChartHom : affineRing k 3 →+* planeRing k` with the explicit right inverse `planeToAffine`
  (`u ↦ a`, `v ↦ b`), hence surjective (`segreChartHom_surjective`);
* `segreChartSpec = Spec.map segreChartHom` is a closed immersion (pinned
  `IsClosedImmersion.spec_of_surjective`);
* `segreChart : Spec (planeRing k) ⟶ projectiveSpace k 3` is `segreChartSpec`, followed by the
  accepted chart identification `Spec (affineRing k 3) ≅ Spec (chartRing k 3)` (`coordinateRingEquiv`)
  and the accepted open immersion `chartMorphism k 3` of `D(z₀)`; it is a closed immersion into the
  chart (`segreChartPiece`, `segreChart_eq`) and is over `k` (`segreChart_structure`).

The three other product charts, the charts `D(z_m)` (`m ≠ 0`) of `P³`, the pairwise overlaps and the
gluing of the four chart maps to `P¹ ×_k P¹ ⟶ P³` are not treated here (see the lane record).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveSegre

open ProjectiveChart KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The Segre chart ring map `a ↦ u`, `b ↦ v`, `c ↦ uv` (coefficients fixed). -/
def segreChartHom : affineRing k 3 →+* planeRing k :=
  MvPolynomial.eval₂Hom planeConstants ![uCoord, vCoord, uCoord * vCoord]

@[simp] theorem segreChartHom_C (r : k) :
    segreChartHom k (MvPolynomial.C r) = planeConstants r :=
  MvPolynomial.eval₂Hom_C _ _ r

@[simp] theorem segreChartHom_X_zero : segreChartHom k (MvPolynomial.X 0) = uCoord :=
  MvPolynomial.eval₂Hom_X' _ _ 0

@[simp] theorem segreChartHom_X_one : segreChartHom k (MvPolynomial.X 1) = vCoord :=
  MvPolynomial.eval₂Hom_X' _ _ 1

@[simp] theorem segreChartHom_X_two : segreChartHom k (MvPolynomial.X 2) = uCoord * vCoord :=
  MvPolynomial.eval₂Hom_X' _ _ 2

/-- The right inverse `u ↦ a`, `v ↦ b` of the Segre chart ring map. -/
def planeToAffine : planeRing k →+* affineRing k 3 :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)

theorem segreChartHom_comp_planeToAffine :
    (segreChartHom k).comp (planeToAffine k) = RingHom.id (planeRing k) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro r
      simp [planeToAffine, planeConstants]
    · simp [planeToAffine, uCoord]
  · simp [planeToAffine, vCoord]

theorem planeToAffine_rightInverse : Function.RightInverse (planeToAffine k) (segreChartHom k) :=
  fun x => RingHom.congr_fun (segreChartHom_comp_planeToAffine k) x

/-- The Segre chart ring map is surjective. -/
theorem segreChartHom_surjective : Function.Surjective (segreChartHom k) :=
  (planeToAffine_rightInverse k).surjective

/-- The Segre map on the chart, as a morphism of affine schemes `Spec k[u][v] ⟶ Spec k[a,b,c]`. -/
def segreChartSpec :
    Spec (CommRingCat.of (planeRing k)) ⟶ Spec (CommRingCat.of (affineRing k 3)) :=
  Spec.map (CommRingCat.ofHom (segreChartHom k))

instance segreChartSpec_isClosedImmersion : IsClosedImmersion (segreChartSpec k) :=
  IsClosedImmersion.spec_of_surjective _ (segreChartHom_surjective k)

/-- The affine coordinate ring `k[a,b,c]` of the chart `D(z₀)` of `P³`, as a scheme
isomorphism onto the spectrum of the accepted chart ring. -/
def affineChartIso :
    Spec (CommRingCat.of (affineRing k 3)) ≅ Spec (CommRingCat.of (chartRing k 3)) :=
  Scheme.Spec.mapIso (coordinateRingEquiv k 3).toCommRingCatIso.op

theorem affineChartIso_hom :
    (affineChartIso k).hom =
      Spec.map (CommRingCat.ofHom (coordinateRingEquiv k 3).toRingHom) := rfl

/-- The closed immersion of the Segre chart into the accepted chart `D(z₀)` of `P³`. -/
def segreChartPiece : Spec (CommRingCat.of (planeRing k)) ⟶ Spec (CommRingCat.of (chartRing k 3)) :=
  segreChartSpec k ≫ (affineChartIso k).hom

instance segreChartPiece_isClosedImmersion : IsClosedImmersion (segreChartPiece k) := by
  unfold segreChartPiece
  infer_instance

/-- The Segre map on the chart `D(x₀ y₀)`, into `P³`. -/
def segreChart : Spec (CommRingCat.of (planeRing k)) ⟶ projectiveSpace k 3 :=
  segreChartPiece k ≫ chartMorphism k 3

theorem segreChart_eq : segreChart k = segreChartPiece k ≫ chartMorphism k 3 := rfl

/-- The chart `D(z₀)` of `P³` is over `k` (the `n = 3` instance of the accepted `P¹` argument). -/
theorem chartMorphism_over_base :
    chartMorphism k 3 ≫ projectiveSpaceToSpec k 3 =
      Spec.map (CommRingCat.ofHom (constants k 3)) := by
  unfold chartMorphism projectiveSpaceToSpec
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The Segre chart map is over `k`. -/
theorem segreChart_structure : segreChart k ≫ projectiveSpaceToSpec k 3 = planeStructure := by
  rw [segreChart, segreChartPiece, Category.assoc, Category.assoc, chartMorphism_over_base,
    affineChartIso_hom, segreChartSpec, planeStructure, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp [planeConstants]

end KltDP.Geometry.ProjectiveSegre
