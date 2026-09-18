import KltDP.Geometry.SmoothSurfaceDivisorPicard
import KltDP.Geometry.RationalPicardIntersection
import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.Geometry.IsolatedExceptionalSelectionGeometry

/-!
# The original Picard pairings of isolated minus-two curves

The smooth Weil-to-Picard map sends the original single-prime divisor to
the original prime Cartier class. Its integral Picard pairing is therefore
the existing geometric Cartier pairing. Isolation makes distinct selected
curves disjoint; the diagonal is their actual minus-two self-intersection.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s) [IsSmooth S.structureMorphism]

/-- The single-prime Weil class has the actual prime Cartier Picard class. -/
theorem smoothWeilClassPicardEquiv_single_toMul (C : S.PrimeCurve) :
    (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C 1))).toMul =
      cartierPicardClass S.toScheme (S.primeCurveCartier hS C) := by
  rw [← S.cartierToWeilHom_primeCurveCartier hS C]
  exact S.regularWeilClassPicardEquiv_of_cartier S.regularPoints_of_isSmooth
    (S.primeCurveCartier hS C)

/-- The original integral node-class pairing is the original Cartier pairing. -/
theorem integralPicardIntersectionBilinForm_smoothPrimeClasses (C D : S.PrimeCurve) :
    S.integralPicardIntersectionBilinForm hS
        (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C 1)))
        (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single D 1))) =
      S.intersectionPairing hS (S.primeCurveCartier hS C) (S.primeCurveCartier hS D) := by
  rw [S.integralPicardIntersectionBilinForm_apply,
    S.smoothWeilClassPicardEquiv_single_toMul hS C,
    S.smoothWeilClassPicardEquiv_single_toMul hS D, S.picardPairing_class hS]

/-- Each pairing between original isolated minus-two node classes is even. -/
theorem isolatedSelection_nodePicard_pairing_even
    {X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)
    (N : Finset S.PrimeCurve)
    (hiso : UnbranchedExceptionalBlocks.IsolatedSelection π N)
    (hN : ∀ C ∈ N, IsExceptionalCurve π C)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hS = -2)
    (C D : {C : S.PrimeCurve // C ∈ N}) :
    Even (S.integralPicardIntersectionBilinForm hS
      (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1)))
      (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single D.val 1)))) := by
  classical
  rw [S.integralPicardIntersectionBilinForm_smoothPrimeClasses hS C.val D.val]
  by_cases hCD : C.val = D.val
  · rw [hCD, S.intersectionPairing_primeCurve hS]
    change Even (D.val.selfIntersectionNumber hS)
    rw [hself D.val D.property]
    exact ⟨-1, by norm_num⟩
  · have hdisj := UnbranchedExceptionalBlocks.isolatedSelection_pairwise π N hiso hN
    rw [(PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      S hS C.val D.val hCD).mpr (hdisj C.property D.property hCD)]
    exact even_zero

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.smoothWeilClassPicardEquiv_single_toMul
#print axioms KltDP.Geometry.NormalProjectiveSurface.smoothWeilClassPicardEquiv_single_toMul
#check @KltDP.Geometry.NormalProjectiveSurface.isolatedSelection_nodePicard_pairing_even
#print axioms KltDP.Geometry.NormalProjectiveSurface.isolatedSelection_nodePicard_pairing_even
