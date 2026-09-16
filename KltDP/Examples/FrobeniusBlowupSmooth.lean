import KltDP.Examples.FrobeniusBlowupContact
import KltDP.Geometry.AffineBlowupChartEquiv
import KltDP.Geometry.AffineBlowupCover
import KltDP.Compatibility.PolynomialStandardSmooth
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Smoothness of the actual affine-plane point blowup

Both actual Rees charts of `(u,v)` are polynomial planes. The first
presentation is already proved in `FrobeniusBlowupContact`; the second
is derived from it by the actual coordinate-swap algebra isomorphism and
the proved chart universal property. Generation by `u,v` proves that
these charts cover the actual Rees Proj. Their actual structure maps
are smooth over the original coefficient field, hence so is the blowup.

This establishes smoothness for the explicit plane-center construction.
It does not assume or prove a coordinate presentation at an arbitrary
smooth surface point, or the surface intersection formulas.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace KltDP.Examples.FrobeniusBlowupSmooth

open KltDP.Geometry.AffineBlowup FrobeniusBlowupContact
open KltDP.Compatibility.PolynomialStandardSmooth

variable {k : Type u} [Field k]

/-- The actual coefficient map into the two-variable polynomial plane. -/
def planeConstants : k →+* planeRing k :=
  (Polynomial.C : Polynomial k →+* planeRing k).comp Polynomial.C

/-- Swapping the polynomial variables uses the existing tensor commutativity isomorphism. -/
def coordinateSwap : planeRing k ≃ₐ[k] planeRing k :=
  (_root_.polyEquivTensor k (Polynomial k)).trans
    ((Algebra.TensorProduct.comm k (Polynomial k) (Polynomial k)).trans
      (_root_.polyEquivTensor k (Polynomial k)).symm)

@[simp] theorem coordinateSwap_u : coordinateSwap (uCoord (k := k)) = vCoord := by
  simp [coordinateSwap, uCoord, vCoord, Polynomial.smul_eq_C_mul]

@[simp] theorem coordinateSwap_v : coordinateSwap (vCoord (k := k)) = uCoord := by
  simp [coordinateSwap, uCoord, vCoord, Polynomial.smul_eq_C_mul]

@[simp] theorem coordinateSwap_constants (r : k) :
    coordinateSwap (planeConstants r) = planeConstants r :=
  (coordinateSwap (k := k)).commutes r

/-- The coordinate swap carries the actual center ideal to itself. -/
theorem coordinateSwap_center :
    Ideal.map (coordinateSwap (k := k)).toRingHom centerIdeal = centerIdeal := by
  rw [centerIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {coordinateSwap (uCoord (k := k)), coordinateSwap vCoord} =
    Ideal.span {uCoord, vCoord}
  rw [coordinateSwap_u, coordinateSwap_v, Ideal.span_pair_comm]

/-- The second chart is the actual localization at the generator `vT`. -/
abbrev reesVChartRing (k : Type u) [Field k] :=
  chartRing (centerIdeal (k := k)) centerV

/-- The actual second chart is a polynomial plane, by coordinate transport of the first. -/
def vChartPolynomialEquiv : reesVChartRing k ≃+* planeRing k :=
  (chartCoordinateEquiv centerIdeal centerIdeal centerV centerU
    (coordinateSwap (k := k)).toRingEquiv coordinateSwap_center coordinateSwap_v).trans
      chartPolynomialEquiv

/-- The actual field-to-chart ring map used by the scheme structure morphism. -/
def chartConstants (a : centerIdeal (k := k)) : k →+* chartRing centerIdeal a :=
  (chartBaseMap centerIdeal a).comp planeConstants

@[simp] theorem uChartPolynomialEquiv_constants (r : k) :
    chartPolynomialEquiv (chartConstants (centerU (k := k)) r) = planeConstants r := by
  change chartToPolynomial (baseMap (Polynomial.C (Polynomial.C r))) =
    Polynomial.C (Polynomial.C r)
  rw [chartToPolynomial_baseMap, chartSubstitution_C]

@[simp] theorem vChartPolynomialEquiv_constants (r : k) :
    vChartPolynomialEquiv (chartConstants (centerV (k := k)) r) = planeConstants r := by
  change chartPolynomialEquiv
    (chartCoordinateEquiv centerIdeal centerIdeal centerV centerU
      (coordinateSwap (k := k)).toRingEquiv coordinateSwap_center coordinateSwap_v
        (chartBaseMap centerIdeal centerV (planeConstants r))) = planeConstants r
  rw [chartCoordinateEquiv_baseMap]
  change (chartPolynomialEquiv (k := k))
    (chartBaseMap centerIdeal centerU ((coordinateSwap (k := k)) (planeConstants r))) =
      planeConstants r
  rw [coordinateSwap_constants]
  exact uChartPolynomialEquiv_constants r

/-- The original polynomial plane's structure morphism over its coefficient field. -/
def planeStructure : Spec (CommRingCat.of (planeRing k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom planeConstants)

/-- Two polynomial coordinates give smooth relative dimension two over the actual field. -/
instance planeStructure_smoothTwo : IsSmoothOfRelativeDimension 2 (planeStructure (k := k)) := by
  unfold planeStructure planeConstants
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  exact inferInstanceAs (IsSmoothOfRelativeDimension (1 + 1)
    (Spec.map (CommRingCat.ofHom (Polynomial.C : Polynomial k →+* planeRing k)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))

instance planeStructure_smooth : IsSmooth (planeStructure (k := k)) :=
  IsSmoothOfRelativeDimension.isSmooth 2 _

/-- The actual map from an individual Rees chart to the coefficient field. -/
def chartStructure (a : centerIdeal (k := k)) :
    Spec (CommRingCat.of (chartRing centerIdeal a)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (chartConstants a))

/-- On the first actual chart the structure morphism is identified with the polynomial one. -/
theorem uChartStructure_eq :
    chartStructure (centerU (k := k)) =
      Spec.map (CommRingCat.ofHom (chartPolynomialEquiv (k := k)).symm.toRingHom) ≫
        planeStructure := by
  rw [chartStructure, planeStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f : k →+* reesChartRing k => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro r
  apply (chartPolynomialEquiv (k := k)).injective
  change (chartPolynomialEquiv (k := k)) (chartConstants centerU r) =
    (chartPolynomialEquiv (k := k)) ((chartPolynomialEquiv (k := k)).symm (planeConstants r))
  rw [RingEquiv.apply_symm_apply, uChartPolynomialEquiv_constants]

/-- On the second actual chart the structure morphism has the same polynomial description. -/
theorem vChartStructure_eq :
    chartStructure (centerV (k := k)) =
      Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).symm.toRingHom) ≫
        planeStructure := by
  rw [chartStructure, planeStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f : k →+* reesVChartRing k => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro r
  exact ((vChartPolynomialEquiv (k := k)).toEquiv.eq_symm_apply).mpr
    (vChartPolynomialEquiv_constants r)

instance uChartStructure_smoothTwo :
    IsSmoothOfRelativeDimension 2 (chartStructure (centerU (k := k))) := by
  rw [uChartStructure_eq]
  letI : IsIso (CommRingCat.ofHom (chartPolynomialEquiv (k := k)).symm.toRingHom) := by
    change IsIso (chartPolynomialEquiv (k := k)).symm.toCommRingCatIso.hom
    infer_instance
  exact inferInstanceAs (IsSmoothOfRelativeDimension (0 + 2)
    (Spec.map (CommRingCat.ofHom (chartPolynomialEquiv (k := k)).symm.toRingHom) ≫
      planeStructure))

instance vChartStructure_smoothTwo :
    IsSmoothOfRelativeDimension 2 (chartStructure (centerV (k := k))) := by
  rw [vChartStructure_eq]
  letI : IsIso (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).symm.toRingHom) := by
    change IsIso (vChartPolynomialEquiv (k := k)).symm.toCommRingCatIso.hom
    infer_instance
  exact inferInstanceAs (IsSmoothOfRelativeDimension (0 + 2)
    (Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).symm.toRingHom) ≫
      planeStructure))

/-- The two selected elements are actual generators of the center ideal. -/
def centerGenerator : Bool → centerIdeal (k := k)
  | false => centerU
  | true => centerV

theorem span_centerGenerator :
    Ideal.span (Set.range (fun i => (centerGenerator (k := k) i : planeRing k))) =
      centerIdeal := by
  have h : Set.range (fun i => (centerGenerator (k := k) i : planeRing k)) =
      {uCoord, vCoord} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      cases i <;> simp [centerGenerator, centerU, centerV]
    · intro hr
      change r = uCoord (k := k) ∨ r = vCoord (k := k) at hr
      rcases hr with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  rw [h]
  rfl

/-- The actual morphism from the Rees point blowup to the original field. -/
def blowupStructure : scheme (centerIdeal (k := k)) ⟶ Spec (CommRingCat.of k) :=
  toSpec centerIdeal ≫ planeStructure

/-- Each actual Rees chart restricts the original field structure by its actual ring map. -/
theorem chartι_blowupStructure (a : centerIdeal (k := k)) :
    chartι centerIdeal a ≫ blowupStructure = chartStructure a := by
  rw [blowupStructure, ← Category.assoc, chartι_toSpec, planeStructure,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The full actual Rees blowup of the plane at `(u,v)` is smooth of
relative dimension two over the field. -/
instance blowupStructure_smoothTwo :
    IsSmoothOfRelativeDimension 2 (blowupStructure (k := k)) := by
  apply IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension 2)
    (generatingAffineCover centerIdeal centerGenerator span_centerGenerator).openCover
  intro i
  change IsSmoothOfRelativeDimension 2
    (chartι centerIdeal (centerGenerator i) ≫ blowupStructure)
  rw [chartι_blowupStructure]
  cases i
  · exact uChartStructure_smoothTwo
  · exact vChartStructure_smoothTwo

instance blowupStructure_smooth : IsSmooth (blowupStructure (k := k)) :=
  IsSmoothOfRelativeDimension.isSmooth 2 _

end KltDP.Examples.FrobeniusBlowupSmooth
