import KltDP.Geometry.RuledSurfaceSourceGeometry
import KltDP.Literature.Hartshorne.RuledSurfacePicard
import KltDP.Geometry.BirationalPicardIntersectionPullback
import KltDP.Geometry.NumericalIntersectionPairing
import KltDP.Geometry.SurfacePointBlowupSequenceBirational
import KltDP.Geometry.SurfacePointBlowupSequenceGeometry

/-!
# An original ruled fibre gives an isotropic class on the original surface

The full ruled geometry constructs the actual section and a closed scheme
fibre. The reviewed Picard theorem computes their intersections. Pullback
along the given original point-blowup sequence preserves these values in
the original numerical quotient. Pairing with the pulled section is one,
so the pulled fibre class is nonzero.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RuledFiberOriginalPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S V : NormalProjectiveSurface k}

/-- The numerical class of the original line bundle pulled from an actual
prime Cartier divisor on the original target. -/
def pullbackCurveClass (b : S.toScheme ⟶ V.toScheme)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v) (F : V.PrimeCurve) :
    S.NumericalClassGroup :=
  S.picardNumericalClass
    (schemePicardPullbackHom b
      (cartierPicardClass V.toScheme (V.primeCurveCartier hV F)))

/-- The original point-blowup sequence preserves both actual prime-divisor
pairings after passage to the original numerical quotient. -/
theorem pairing_pullbackCurveClass
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v) (A F : V.PrimeCurve) :
    S.numericalIntersectionBilinForm hS
        (pullbackCurveClass b hV A) (pullbackCurveClass b hV F) =
      (V.intersectionPairing hV
        (V.primeCurveCartier hV A) (V.primeCurveCartier hV F) : ℚ) := by
  letI : IsProper b := hb.isProper
  calc
    _ = (S.picardPairing hS
        (schemePicardPullbackHom b
          (cartierPicardClass V.toScheme (V.primeCurveCartier hV A)))
        (schemePicardPullbackHom b
          (cartierPicardClass V.toScheme (V.primeCurveCartier hV F))) : ℚ) :=
      S.numericalIntersectionBilinForm_picard hS _ _
    _ = (V.picardPairing hV
        (cartierPicardClass V.toScheme (V.primeCurveCartier hV A))
        (cartierPicardClass V.toScheme (V.primeCurveCartier hV F)) : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ))
        (BirationalPicardIntersectionPullback.picardPairing_pullback
          b hb.over_base hb.isBirationalScheme hS hV _ _)
    _ = _ := congrArg (fun z : ℤ => (z : ℚ)) (V.picardPairing_class hV _ _)

/-- Every original ruling supplies an actual closed fibre whose original
pullback is nonzero and isotropic. Neither prime-curve representations nor
numerical identities are input hypotheses. -/
theorem exists_original_isotropic_fiber
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1) (hCreg : ∀ y : C, RegularPoint C y)
    (q : V.toScheme ⟶ C) (hbase : q ≫ c = V.structureMorphism)
    (hsurj : Function.Surjective q.base)
    (hfib : ∀ y : C, IsClosed ({y} : Set C) →
      ∃ e : q.fiber y ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism)
    (σ : C ⟶ V.toScheme) (hσ : σ ≫ q = 𝟙 C) :
    ∃ (y : C) (_hy : IsClosed ({y} : Set C)) (A F : V.PrimeCurve)
      (eA : A.toScheme ≅ C) (eF : F.toScheme ≅ q.fiber y),
      eA.inv ≫ A.inclusion = σ ∧
      eF.hom ≫ q.fiberι y = F.inclusion ∧
      V.intersectionPairing hV
        (V.primeCurveCartier hV A) (V.primeCurveCartier hV F) = 1 ∧
      V.intersectionPairing hV
        (V.primeCurveCartier hV F) (V.primeCurveCartier hV F) = 0 ∧
      S.numericalIntersectionBilinForm hS
        (pullbackCurveClass b hV A) (pullbackCurveClass b hV F) = 1 ∧
      pullbackCurveClass b hV F ≠ 0 ∧
      S.numericalIntersectionBilinForm hS
        (pullbackCurveClass b hV F) (pullbackCurveClass b hV F) = 0 := by
  obtain ⟨A, eA, heA, _heAbase, _hA⟩ :=
    RuledSurfaceSourceGeometry.exists_sectionPrimeCurve V c q hbase hCdim σ hσ
  letI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set C).Nonempty from ⟨genericPoint C, Set.mem_univ _⟩)
    isOpen_univ.isLocallyClosed
  obtain ⟨e, he⟩ := hfib y hy
  obtain ⟨F, eF, heF, _heFbase, _hF⟩ :=
    RuledSurfaceSourceGeometry.exists_fiberPrimeCurve V q y hy e he
  obtain ⟨_ePic, _eNum, _hePic, _heNum, hAF, hFF⟩ :=
    Literature.Hartshorne.ruled_surface_picard_literal
      k V hV C c hCdim hCreg q hbase hsurj hfib σ hσ A eA heA y hy F eF heF
  have hAFpull : S.numericalIntersectionBilinForm hS
      (pullbackCurveClass b hV A) (pullbackCurveClass b hV F) = 1 := by
    rw [pairing_pullbackCurveClass b hb hS hV A F, hAF, Int.cast_one]
  have hFFpull : S.numericalIntersectionBilinForm hS
      (pullbackCurveClass b hV F) (pullbackCurveClass b hV F) = 0 := by
    rw [pairing_pullbackCurveClass b hb hS hV F F, hFF, Int.cast_zero]
  refine ⟨y, hy, A, F, eA, eF, heA, heF, hAF, hFF, hAFpull, ?_, hFFpull⟩
  intro hz
  have hzero : (0 : ℚ) = 1 := by simpa only [hz, map_zero] using hAFpull
  exact zero_ne_one hzero

end KltDP.Geometry.RuledFiberOriginalPullback

#check @KltDP.Geometry.RuledFiberOriginalPullback.exists_original_isotropic_fiber
#print axioms KltDP.Geometry.RuledFiberOriginalPullback.pullbackCurveClass
#print axioms KltDP.Geometry.RuledFiberOriginalPullback.pairing_pullbackCurveClass
#print axioms KltDP.Geometry.RuledFiberOriginalPullback.exists_original_isotropic_fiber
