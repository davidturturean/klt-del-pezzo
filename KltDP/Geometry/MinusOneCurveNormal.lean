import KltDP.Geometry.MinusOneCurveConormal
import KltDP.Geometry.SchemeInvertibleDualPullback

/-!
# Original normal and conormal sheaves of a minus-one curve

The original conormal's actual dual is invertible by its actual evaluation.
Pulling that evaluation to the given projective line makes the exponents
add to zero. Thus conormal degree one forces the original normal to be
O(-1), without supplying a normal bundle or its isomorphism class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open KltDP.Geometry.RationalTreePicard

universe u

namespace KltDP.Geometry.MinusOneCurveNormal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance normalModulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

local instance normalModulesSymmetric (Y : Scheme.{u}) : SymmetricCategory Y.Modules :=
  Scheme.Modules.symmetricCategory Y

local instance structureSectionsComm (Y : Scheme.{u}) :
    ∀ U, IsMulCommutative (Y.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (Y.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The actual sheaf dual, with local invertibility derived from its
evaluation with the original invertible sheaf. -/
def actualDualLine {Y : Scheme.{u}} (L : InvertibleSheaf Y) :
    InvertibleSheaf Y :=
  ⟨KltDP.SheafOfModules.dual Y.ringCatSheaf L.obj, by
    apply SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton
    refine isUnit_of_dvd_one ⟨toSkeleton L.obj, ?_⟩
    rw [mul_comm, ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact Quotient.sound ⟨(KltDP.SheafOfModules.tensorDualIsoUnit
      Y.sheaf.val Y.ringCatSheaf.cond L.obj).symm⟩⟩

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : X.PrimeCurve)

/-- The actual dual of the original inclusion's conormal sheaf. -/
def normalLine : InvertibleSheaf C.toScheme :=
  actualDualLine (conormalLine X hregular C)

theorem normalLine_obj :
    (normalLine X hregular C).obj =
      KltDP.SheafOfModules.dual C.toScheme.ringCatSheaf
        (schemeConormalSheaf C.inclusion) := rfl

/-- The original normal pulls back to O(-1) along the given isomorphism
over the original field, as an actual module sheaf. -/
theorem normal_iso_of_square_neg_one
    (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hsquare : C.selfIntersectionNumber hregular = -1) :
    Nonempty ((schemeModulePullback e.inv).obj
      (KltDP.SheafOfModules.dual C.toScheme.ringCatSheaf
        (schemeConormalSheaf C.inclusion)) ≅
      (monomialLineBundle k (-1)).obj) := by
  let L := pullbackInvertibleSheaf e.inv (conormalLine X hregular C)
  let N := pullbackInvertibleSheaf e.inv (normalLine X hregular C)
  have hL : ProjectiveLineSheafExponent.exponent k L = 1 := by
    rw [← ProjectiveLineDegree.degree_eq_exponent k L,
      pulled_conormal_degree X hregular C e he, hsquare]
    norm_num
  have hsum := ProjectiveLineSheafExponent.exponent_eq_add_of_tensorIso k L N
    (InvertibleSheaf.trivial (projectiveSpace k 1))
    (schemeModulePullbackDualEvaluationIso e.inv (conormalLine X hregular C)).symm
  rw [ProjectiveLineDegree.exponent_trivial, hL] at hsum
  apply nonempty_iso_monomial_of_degree N (-1)
  rw [ProjectiveLineDegree.degree_eq_exponent]
  omega

end KltDP.Geometry.MinusOneCurveNormal

namespace KltDP.Geometry

open MinusOneCurveNormal

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MinusOneCurveNormal.structureSectionsComm

/-- An actual minus-one curve supplies the original invertible defining
ideal and the two actual first-kind bundle identifications. The original
curve, inclusion, and isomorphism over the base field are retained. -/
theorem IsMinusOneCurve.original_conormal_and_normal
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : NormalProjectiveSurface k}
    {hregular : ∀ x : X.Point, RegularPoint X.toScheme x}
    {C : X.PrimeCurve} (hC : IsMinusOneCurve hregular C) :
    KltDP.SheafOfModules.IsInvertible (R := X.toScheme.ringCatSheaf)
      (schemeKernelIdeal C.inclusion) ∧
    ∃ e : C.toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec ∧
      Nonempty ((schemeModulePullback e.inv).obj (schemeConormalSheaf C.inclusion) ≅
        (monomialLineBundle k 1).obj) ∧
      Nonempty ((schemeModulePullback e.inv).obj
        (KltDP.SheafOfModules.dual C.toScheme.ringCatSheaf
          (schemeConormalSheaf C.inclusion)) ≅
        (monomialLineBundle k (-1)).obj) := by
  obtain ⟨e, he⟩ := hC.isoProjectiveLine
  exact ⟨(kernelLine X hregular C).property, e, he,
    conormal_iso_of_square_neg_one X hregular C e he hC.selfIntersection,
    normal_iso_of_square_neg_one X hregular C e he hC.selfIntersection⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsMinusOneCurve.original_conormal_and_normal
