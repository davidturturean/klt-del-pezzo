import KltDP.Geometry.RuledFiberConstancyOrthogonality
import KltDP.Geometry.RationalTreePicardProjectiveLine
import KltDP.Geometry.PointBlowupPicardDecomposition
import KltDP.Geometry.ContractionPicardUnimodular
import KltDP.LinearAlgebra.SectionFiberIntegralDual

/-!
# The original Picard pairing of a ruling over the projective line is unimodular

The full ruled Picard theorem gives the original section plus base Picard
decomposition. The actual base isomorphism makes its Picard group cyclic.
The actual fibre comes from that base and pairs once with the section,
so those original two classes generate. Their actual pairing gives a
bijection with the integral dual, without using surface rationality.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RuledProjectiveLineBase

variable {k : Type u} [Field k] [IsAlgClosed k]
  (V : NormalProjectiveSurface k)
  (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1) (hCreg : ∀ y : C, RegularPoint C y)
  (q : V.toScheme ⟶ C) (hbase : q ≫ c = V.structureMorphism)
  (hsurj : Function.Surjective q.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : q.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism)
  (σ : C ⟶ V.toScheme) (hσ : σ ≫ q = 𝟙 C)
  (eC : C ≅ projectiveSpace k 1)

include hV hCdim hCreg hbase hsurj hfib hσ eC

/-- Unimodularity concerns the actual full Picard group and its original
integral intersection pairing. Section/fibre representations are constructed. -/
theorem picardUnimodular : V.PicardUnimodular hV := by
  obtain ⟨A, eA, heA, _heAbase, _hA⟩ :=
    RuledSurfaceSourceGeometry.exists_sectionPrimeCurve V c q hbase hCdim σ hσ
  letI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set C).Nonempty from ⟨genericPoint C, Set.mem_univ _⟩)
    isOpen_univ.isLocallyClosed
  obtain ⟨e, he⟩ := hfib y hy
  obtain ⟨F, eF, heF, _heFbase, _hF⟩ :=
    RuledSurfaceSourceGeometry.exists_fiberPrimeCurve V q y hy e he
  obtain ⟨ePic, _eNum, hePic, _heNum, hAF, hFF⟩ :=
    Literature.Hartshorne.ruled_surface_picard_literal
      k V hV C c hCdim hCreg q hbase hsurj hfib σ hσ A eA heA y hy F eF heF
  obtain ⟨l, hl⟩ := RuledFiberOriginalPullback.fiberPicard_from_base
    hV C c hCdim hCreg q hbase hsurj hfib σ hσ y hy F eF heF
  let PA := cartierPicardHom V.toScheme (V.primeCurveCartier hV A)
  let PF := cartierPicardHom V.toScheme (V.primeCurveCartier hV F)
  let B := V.integralPicardIntersectionBilinForm hV
  let eG : Additive C.Pic ≃+ ℤ :=
    (((PointBlowupPicard.pullbackEquivOfIso eC).symm.trans
      (RationalTreePicard.projectiveLinePicardExponentEquiv k)).toAdditive).trans
        (AddEquiv.additiveMultiplicative ℤ)
  have hfbase : PF = (schemePicardPullbackHom q).toAdditive (Additive.ofMul l) :=
    congrArg Additive.ofMul hl
  have hpair (D E : CartierDivisor V.toScheme) :
      B (cartierPicardHom V.toScheme D) (cartierPicardHom V.toScheme E) =
        V.intersectionPairing hV D E := by
    rw [V.integralPicardIntersectionBilinForm_apply]
    exact V.picardPairing_class hV D E
  have hAF' : B PA PF = 1 := (hpair _ _).trans hAF
  have hFF' : B PF PF = 0 := (hpair _ _).trans hFF
  have hFA' : B PF PA = 1 :=
    (V.integralPicardIntersectionBilinForm_isSymm hV PF PA).trans hAF'
  have hgen := LinearAlgebra.SectionFiberIntegralDual.generate_of_cyclic_base
    B PA PF (schemePicardPullbackHom q).toAdditive ePic hePic eG (Additive.ofMul l) hfbase hAF'
  exact (V.picardUnimodular_iff_bilinForm hV).mpr
    (LinearAlgebra.SectionFiberIntegralDual.dual_bijective_of_section_fiber
      B PA PF hgen hAF' hFA' hFF')

end KltDP.Geometry.RuledProjectiveLineBase

#print axioms KltDP.Geometry.RuledProjectiveLineBase.picardUnimodular
