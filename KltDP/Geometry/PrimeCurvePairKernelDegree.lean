import KltDP.Geometry.PrimeCurveConormalDegree

/-!
# Pairwise intersection degree on the unchanged original curve carriers

For arbitrary original prime curves E and F, the negative intersection
number E.F is the Euler degree of F's actual ideal restricted to E.
Both closed curve carriers and their maps stay explicit; they need not
be disjoint or distinct. The ideal is proved invertible from regularity.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurvePairKernelDegree

open NormalProjectiveSurface PrimeCurveConormalDegree ModuleCohomology

/-- The original two-curve intersection is computed by the actual restricted kernel sheaf. -/
theorem intersectionNumber_neg_eq_euler_kernel
    {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
    (hreg : ∀ x : X.Point, RegularPoint X.toScheme x) (E F : X.PrimeCurve)
    {A B : Scheme.{u}} (i : A ⟶ X.toScheme) (j : B ⟶ X.toScheme)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsReduced A] [IsReduced B]
    (hE : (E : Set X.toScheme) = Set.range i.base)
    (hF : (F : Set X.toScheme) = Set.range j.base) :
    -(E.intersectionNumber (X.primeCurveCartier hreg F)) =
      eulerCharacteristic (i ≫ X.structureMorphism)
          ((schemeModulePullback i).obj (schemeKernelIdeal j)) -
        eulerCharacteristic (i ≫ X.structureMorphism)
          (_root_.SheafOfModules.unit A.ringCatSheaf) := by
  let K := InvertibleSheaf.ofIso
    (cartierDivisorInvertibleSheaf X.toScheme (-X.primeCurveCartier hreg F))
    (negativeCartierKernelIso hreg F j hF)
  rw [← E.intersectionNumber_neg]
  change E.lineDegree (pullbackInvertibleSheaf E.inclusion
    (cartierDivisorInvertibleSheaf X.toScheme (-X.primeCurveCartier hreg F))) = _
  refine lineDegree_eq_euler_difference E (inv (PrimeCurveInclusionLift.lift E i hE))
    (i ≫ X.structureMorphism) ?_ _ (pullbackInvertibleSheaf i K) ?_
  · rw [← Category.assoc, ← PrimeCurveInclusionLift.inclusion_eq_inv_lift E i hE]
    rfl
  · refine (schemeModulePullback E.inclusion).mapIso (negativeCartierKernelIso hreg F j hF) ≪≫ ?_
    rw [PrimeCurveInclusionLift.inclusion_eq_inv_lift E i hE]
    exact (schemeModulePullbackCompIso (inv (PrimeCurveInclusionLift.lift E i hE)) i).symm.app
      (schemeKernelIdeal j)

end KltDP.Geometry.PrimeCurvePairKernelDegree

#print axioms KltDP.Geometry.PrimeCurvePairKernelDegree.intersectionNumber_neg_eq_euler_kernel
