import KltDP.Geometry.CurvePairKernelOpen
import KltDP.Geometry.PrimeCurvePairKernelDegree
import KltDP.Geometry.PrimeCurveImageOnIsomorphismOpen

/-!
# All original curve intersection numbers survive the isomorphism open

The original two curves may intersect each other. Their actual closed
images have the same intersection number because the negative Cartier
ideals have the same restricted kernel module on the unchanged first
curve. The self-intersection case is included without a separate case.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.CurveOnIsomorphismOpen

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
    (C D : S.PrimeCurve) (b : S.toScheme ⟶ T.toScheme) [IsProper b]
    (U : T.toScheme.Opens) [IsIso (b ∣_ U)]
    (hC : Set.range C.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme))
    (hD : Set.range D.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme))

/-- Actual closed images preserve the original full two-curve intersection pairing. -/
theorem imageCurve_intersectionNumber
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (hover : b ≫ T.structureMorphism = S.structureMorphism) :
    (imageCurve C b U hC).intersectionNumber
      (T.primeCurveCartier hT (imageCurve D b U hD)) =
      C.intersectionNumber (S.primeCurveCartier hS D) := by
  letI := comp_isClosedImmersion C.inclusion b U hC
  letI := comp_isClosedImmersion D.inclusion b U hD
  have hs := PrimeCurvePairKernelDegree.intersectionNumber_neg_eq_euler_kernel
    hS C D C.inclusion D.inclusion C.range_inclusion.symm D.range_inclusion.symm
  have ht := PrimeCurvePairKernelDegree.intersectionNumber_neg_eq_euler_kernel
    hT (imageCurve C b U hC) (imageCurve D b U hD)
    (C.inclusion ≫ b) (D.inclusion ≫ b) rfl rfl
  have hbase : (C.inclusion ≫ b) ≫ T.structureMorphism =
      C.inclusion ≫ S.structureMorphism := by rw [Category.assoc, hover]
  have hkernel := ModuleCohomology.eulerCharacteristic_eq_of_iso
    (C.inclusion ≫ S.structureMorphism) (pairKernelIso C.inclusion D.inclusion b U hC hD)
  rw [hbase, hkernel] at ht
  exact neg_injective (ht.trans hs.symm)

end KltDP.Geometry.CurveOnIsomorphismOpen

#print axioms KltDP.Geometry.CurveOnIsomorphismOpen.imageCurve_intersectionNumber
