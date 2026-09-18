import KltDP.Geometry.NormalModelKlt
import KltDP.Geometry.NormalModelFrameNormalization
import KltDP.Geometry.CommonOpenLocalFrameDiscrepancy

/-!
# The original compatible discrepancy coefficients satisfy the klt bound

The actual all-normal-model klt predicate is evaluated on the original
smooth source and its actual prime generic point. The original compatible
canonical frame and Cartier numerator identify that test with the original
rational Weil difference. No discrepancy bound or normalization is supplied.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.KltOriginalDiscrepancyBound

open NormalProjectiveSurface NormalModelCanonical

attribute [local instance] integralSchemeStalk_isDomain

/-- Every coefficient of the original compatible canonical difference is
greater than minus one, directly from the actual all-model klt predicate. -/
theorem coefficient_gt_neg_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hklt : IsKltWithCanonicalDivisor X KX)
    (hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) = KX)
    (C : S.PrimeCurve) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (-1 : ℚ) < (S.rationalCartierToWeilHom KS -
      QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hklt.2.1) C := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsSmooth S.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  letI : LocallyOfFiniteType (π ≫ X.structureMorphism) := by
    rw [hπ]
    infer_instance
  let x : CodimensionOnePoint S.toScheme :=
    ⟨C.genericPoint, C.ringKrullDim_stalk_genericPoint⟩
  letI : IsDiscreteValuationRing (S.toScheme.presheaf.stalk x.val) :=
    normalFiniteTypePoint_isDiscreteValuationRing (π ≫ X.structureMorphism) S.normal x
  obtain ⟨U, hne, hcanonicalU⟩ := hklt.1
  letI : Nonempty U.toScheme := hne
  letI : Nonempty U := ⟨Classical.choice hne⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨hsmooth, hU, KU, ⟨eKU⟩, hKU⟩ := hcanonicalU
  obtain ⟨F, hF, hForder⟩ := NormalModelFrameNormalization.exists_normalized_frame
    S X π hbir π (𝟙 S.toScheme) (𝟙 S.toScheme) (by simp) hπ
    C.genericPoint C.genericPoint rfl C rfl KS eKS U hU KU eKU
    (hpush.trans hKU.symm)
  obtain ⟨n, hn, A, hA⟩ :=
    (X.qCartier_iff_exists_positive_multiple (rationalizeWeilDivisor X KX)).mp hklt.2.1
  have hbound := (hklt.2.2 U hne hsmooth hU KU eKU hKU
    S.toScheme S.normal π hbir x).2 F hF n hn A hA
  have hraw := CommonOpenCanonicalLocalFrame.localFrame_order
    S X π π (𝟙 S.toScheme) (𝟙 S.toScheme) (by simp) hπ
    C.genericPoint x.val rfl KS eKS C rfl
  have horder : F.order =
      (CommonOpenCanonicalLocalFrame.localFrame S X π π
        (𝟙 S.toScheme) (𝟙 S.toScheme) (by simp) hπ
        C.genericPoint x.val rfl KS eKS).order := hForder.trans hraw.symm
  have hformula := CommonOpenCanonicalLocalFrame.localFrame_discrepancy_eq
    S X π π (𝟙 S.toScheme) (𝟙 S.toScheme) (by simp) hπ
    C.genericPoint C x rfl rfl S.normal KS eKS
    (rationalizeWeilDivisor X KX) hklt.2.1 n hn A hA
  have hformulaF : discrepancyForCartierMultiple X π x.val F n A =
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hklt.2.1) C := by
    simpa only [discrepancyForCartierMultiple, horder] using hformula
  rwa [hformulaF] at hbound

end KltDP.Geometry.KltOriginalDiscrepancyBound

#check @KltDP.Geometry.KltOriginalDiscrepancyBound.coefficient_gt_neg_one
#print axioms KltDP.Geometry.KltOriginalDiscrepancyBound.coefficient_gt_neg_one
