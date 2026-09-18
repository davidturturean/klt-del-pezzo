import KltDP.Geometry.Resolution
import KltDP.Geometry.PrimeCurveConormalDegree
import KltDP.Geometry.ProjectiveLineDegreeExponent
import KltDP.Geometry.SchemeIsoEulerTransport

/-!
# The original conormal of a rational minus-one curve

The original inclusion kernel is the negative prime Cartier module. Its
pullback is therefore an actual invertible conormal sheaf of degree one
when the original self-intersection is minus one. Transport along the
given projective-line isomorphism and the proved degree classification
produce an actual sheaf isomorphism with O(1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.RationalTreePicard

universe u

namespace KltDP.Geometry.MinusOneCurveNormal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance modulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Degree classification gives an actual isomorphism of the original
line sheaf, by equality in the actual skeleton of module sheaves. -/
theorem nonempty_iso_monomial_of_degree
    {k : Type u} [Field k] (L : InvertibleSheaf (projectiveSpace k 1))
    (n : ℤ) (hn : ProjectiveLineDegree.degree k L = n) :
    Nonempty (L.obj ≅ (monomialLineBundle k n).obj) := by
  have hp : L.toPic = (monomialLineBundle k n).toPic :=
    ProjectiveLineDegree.toPic_eq_of_exponent_eq k (by
      rw [← ProjectiveLineDegree.degree_eq_exponent k L, hn,
        monomialLineBundle_exponent])
  have hs : (L.toPic : Skeleton (projectiveSpace k 1).Modules) =
      ((monomialLineBundle k n).toPic : Skeleton (projectiveSpace k 1).Modules) :=
    congrArg (fun p : (projectiveSpace k 1).Pic =>
      (p : Skeleton (projectiveSpace k 1).Modules)) hp
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val] at hs
  exact Quotient.exact hs

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : X.PrimeCurve)

/-- The actual original inclusion kernel, with invertibility derived from
its isomorphism with the negative prime Cartier module. -/
def kernelLine : InvertibleSheaf X.toScheme :=
  InvertibleSheaf.ofIso
    (cartierDivisorInvertibleSheaf X.toScheme (-X.primeCurveCartier hregular C))
    (PrimeCurveConormalDegree.negativeCartierKernelIso hregular C C.inclusion
      C.range_inclusion.symm)

/-- The actual conormal sheaf of the original curve inclusion. -/
def conormalLine : InvertibleSheaf C.toScheme :=
  pullbackInvertibleSheaf C.inclusion (kernelLine X hregular C)

theorem conormalLine_obj :
    (conormalLine X hregular C).obj = schemeConormalSheaf C.inclusion := rfl

/-- The original conormal degree is minus the original self-intersection. -/
theorem conormal_degree :
    C.lineDegree (conormalLine X hregular C) =
      -C.selfIntersectionNumber hregular := by
  have h : C.intersectionNumber (-X.primeCurveCartier hregular C) =
      C.lineDegree (conormalLine X hregular C) :=
    C.lineDegree_eq_of_iso
      ((schemeModulePullback C.inclusion).mapIso
        (PrimeCurveConormalDegree.negativeCartierKernelIso hregular C C.inclusion
          C.range_inclusion.symm))
  rw [C.intersectionNumber_neg] at h
  exact h.symm

variable (e : C.toScheme ≅ projectiveSpace k 1)
  (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)

include he

/-- The degree of the original conormal, transported along the given
isomorphism over the original field. -/
theorem pulled_conormal_degree :
    ProjectiveLineDegree.degree k
      (pullbackInvertibleSheaf e.inv (conormalLine X hregular C)) =
      -C.selfIntersectionNumber hregular := by
  change eulerCharacteristic (projectiveSpaceToSpec k 1)
      ((schemeModulePullback e.inv).obj (conormalLine X hregular C).obj) -
    eulerCharacteristic (projectiveSpaceToSpec k 1)
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = _
  rw [← eulerCharacteristic_eq_pullback_inv e C.toSpec
      (projectiveSpaceToSpec k 1) he,
    ← eulerCharacteristic_unit_eq e C.toSpec (projectiveSpaceToSpec k 1) he]
  exact conormal_degree X hregular C

/-- Original square minus one gives O(1) for the actual conormal pulled
back to the given projective line; no conormal-class input is supplied. -/
theorem conormal_iso_of_square_neg_one
    (hsquare : C.selfIntersectionNumber hregular = -1) :
    Nonempty ((schemeModulePullback e.inv).obj (schemeConormalSheaf C.inclusion) ≅
      (monomialLineBundle k 1).obj) := by
  apply nonempty_iso_monomial_of_degree
    (pullbackInvertibleSheaf e.inv (conormalLine X hregular C)) 1
  rw [pulled_conormal_degree X hregular C e he, hsquare]
  norm_num

end KltDP.Geometry.MinusOneCurveNormal

#print axioms KltDP.Geometry.MinusOneCurveNormal.conormal_iso_of_square_neg_one
