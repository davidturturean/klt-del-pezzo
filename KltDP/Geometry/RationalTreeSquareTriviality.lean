import KltDP.Manuscript.S02.RationalTreePicard
import KltDP.Geometry.UnbranchedRationalHalfLine

/-!
# Trivializing the actual half-line on an entire rational tree

The proved Picard isomorphism has a torsion-free integral target. An actual
tensor-square isomorphism therefore trivializes the original line bundle
on the whole tree, retaining compatibility at every node automatically.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.RationalTreeSquareTriviality

open RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

variable {k : Type u} [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    (sC : C ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C),
      componentUnionScheme C {D} ≅ projectiveSpace k 1)

include sC hdim hTree htrans eC in
/-- Two-torsion vanishes in the original integral Picard group of the whole tree. -/
theorem eq_one_of_sq_eq_one (p : C.Pic) (hp : p ^ 2 = 1) : p = 1 := by
  let d := KltDP.Manuscript.S02.rationalTreePicardEquiv C sC hdim hTree htrans eC
  have hs : d p * d p = 1 := by
    simpa only [map_pow, pow_two, map_mul, map_one] using congrArg d hp
  apply d.injective
  rw [map_one]
  funext D
  apply Multiplicative.toAdd.injective
  have h := congrArg (fun v => Multiplicative.toAdd (v D)) hs
  change Multiplicative.toAdd (d p D) + Multiplicative.toAdd (d p D) = 0 at h
  change Multiplicative.toAdd (d p D) = 0
  omega

/-- The original square isomorphism supplies an actual global frame on the tree. -/
def unitIsoOfSquareIso (L : InvertibleSheaf C)
    (e : L.obj ⊗ L.obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf) :
    L.obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf := by
  have hs : L.toPic ^ 2 = 1 := by
    apply Units.ext
    change (L.toPic : Skeleton C.Modules) ^ 2 = 1
    rw [pow_two, InvertibleSheaf.toPic_val,
      ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact Quotient.sound ⟨e ≪≫
      (PresheafOfModules.sheafTensorUnitIso C.sheaf.val C.ringCatSheaf.cond).symm⟩
  exact Classical.choice ((toPic_eq_one_iff_iso_unit L).mp
    (eq_one_of_sq_eq_one C sC hdim hTree htrans eC L.toPic hs))

/-- Branch disjointness derives the whole-tree half-line frame from the
original Cartier square; no component frames are supplied. -/
def unbranchedHalfLineIso {X : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf :=
  unitIsoOfSquareIso C sC hdim hTree htrans eC (pullbackInvertibleSheaf f L)
    (UnbranchedRationalHalfLine.squareUnitIso E hE L e f hdisj)

end KltDP.Geometry.RationalTreeSquareTriviality

#print axioms KltDP.Geometry.RationalTreeSquareTriviality.eq_one_of_sq_eq_one
#print axioms KltDP.Geometry.RationalTreeSquareTriviality.unbranchedHalfLineIso
