import KltDP.Geometry.CurvePreservedOnIsomorphismOpen
import KltDP.Geometry.PrimeCurveClosedImage
import KltDP.Geometry.PrimeCurveConormalDegree
import KltDP.Geometry.Resolution

/-!
# The original image curve and its unchanged self-intersection

A curve entirely contained in the isomorphism open of a proper map has
an actual closed image curve. The original curve-source isomorphism is
over k, and the actual conormal comparison preserves its self-intersection.
In particular, an original minus-one curve remains a minus-one curve.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.CurveOnIsomorphismOpen

variable {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    (C : S.PrimeCurve) (b : S.toScheme ⟶ T.toScheme) [IsProper b]
    (U : T.toScheme.Opens) [IsIso (b ∣_ U)]
    (hU : Set.range C.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme))

/-- The actual closed image of the unchanged original curve inclusion. -/
def imageCurve : T.PrimeCurve := by
  letI := comp_isClosedImmersion C.inclusion b U hU
  exact C.closedImage (C.inclusion ≫ b)

@[simp]
theorem coe_imageCurve :
    (imageCurve C b U hU : Set T.toScheme) = b.base '' (C : Set S.toScheme) := by
  change Set.range (C.inclusion ≫ b).base = _
  change Set.range (b.base ∘ C.inclusion.base) = _
  rw [Set.range_comp, C.range_inclusion]

/-- The target image curve is isomorphic to the original curve scheme. -/
def imageCurveSourceIso : (imageCurve C b U hU).toScheme ≅ C.toScheme := by
  letI := comp_isClosedImmersion C.inclusion b U hU
  exact C.closedImageSourceIso (C.inclusion ≫ b)

@[reassoc]
theorem imageCurveSourceIso_hom_map :
    (imageCurveSourceIso C b U hU).hom ≫ (C.inclusion ≫ b) =
      (imageCurve C b U hU).inclusion := by
  letI := comp_isClosedImmersion C.inclusion b U hU
  exact C.closedImageSourceIso_hom_map (C.inclusion ≫ b)

/-- The original field structure is retained by the image-curve isomorphism. -/
theorem imageCurveSourceIso_over_base
    (hover : b ≫ T.structureMorphism = S.structureMorphism) :
    (imageCurveSourceIso C b U hU).hom ≫ C.toSpec = (imageCurve C b U hU).toSpec := by
  change (imageCurveSourceIso C b U hU).hom ≫
    (C.inclusion ≫ S.structureMorphism) =
      (imageCurve C b U hU).inclusion ≫ T.structureMorphism
  rw [← hover, ← Category.assoc C.inclusion b T.structureMorphism,
    ← Category.assoc, imageCurveSourceIso_hom_map]

/-- The actual self-intersection is unchanged on the original isomorphism open. -/
theorem imageCurve_selfIntersection [IsAlgClosed k]
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (hover : b ≫ T.structureMorphism = S.structureMorphism) :
    (imageCurve C b U hU).selfIntersectionNumber hT = C.selfIntersectionNumber hS := by
  letI := comp_isClosedImmersion C.inclusion b U hU
  let D := imageCurve C b U hU
  have hD : (D : Set T.toScheme) = Set.range (C.inclusion ≫ b).base := rfl
  let LS := InvertibleSheaf.ofIso
    (cartierDivisorInvertibleSheaf S.toScheme (-S.primeCurveCartier hS C))
    (PrimeCurveConormalDegree.negativeCartierKernelIso hS C C.inclusion
      C.range_inclusion.symm)
  let LT := InvertibleSheaf.ofIso
    (cartierDivisorInvertibleSheaf T.toScheme (-T.primeCurveCartier hT D))
    (PrimeCurveConormalDegree.negativeCartierKernelIso hT D (C.inclusion ≫ b) hD)
  have hsource := PrimeCurveConormalDegree.selfIntersectionNumber_eq_neg_lineDegree
    hS C C.inclusion C.range_inclusion.symm LS.property
  have htarget := PrimeCurveConormalDegree.selfIntersectionNumber_eq_neg_lineDegree
    hT D (C.inclusion ≫ b) hD LT.property
  rw [PrimeCurveConormalDegree.lineDegree_curveConormalLine_eq_euler_difference,
    PrimeCurveConormalDegree.conormalLine_obj] at hsource htarget
  have hbase : (C.inclusion ≫ b) ≫ T.structureMorphism =
      C.inclusion ≫ S.structureMorphism := by rw [Category.assoc, hover]
  have hconormal := ModuleCohomology.eulerCharacteristic_eq_of_iso
    (C.inclusion ≫ S.structureMorphism) (conormalIso C.inclusion b U hU)
  rw [hbase, hconormal] at htarget
  exact htarget.trans hsource.symm

/-- A disjoint original minus-one curve is available for the next actual contraction. -/
theorem imageCurve_isMinusOne [IsAlgClosed k]
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (hover : b ≫ T.structureMorphism = S.structureMorphism)
    (hC : IsMinusOneCurve hS C) :
    IsMinusOneCurve hT (imageCurve C b U hU) := by
  obtain ⟨eP, heP⟩ := hC.isoProjectiveLine
  refine ⟨⟨imageCurveSourceIso C b U hU ≪≫ eP, ?_⟩, ?_⟩
  · change ((imageCurveSourceIso C b U hU).hom ≫ eP.hom) ≫
      projectiveSpaceToSpec k 1 = _
    rw [Category.assoc, heP, imageCurveSourceIso_over_base C b U hU hover]
  · rw [imageCurve_selfIntersection C b U hU hS hT hover]
    exact hC.selfIntersection

end KltDP.Geometry.CurveOnIsomorphismOpen

#print axioms KltDP.Geometry.CurveOnIsomorphismOpen.imageCurve_selfIntersection
#print axioms KltDP.Geometry.CurveOnIsomorphismOpen.imageCurve_isMinusOne
