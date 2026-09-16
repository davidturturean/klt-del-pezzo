import KltDP.Geometry.ProjectiveLineSquareTriviality
import KltDP.Geometry.TensorInvertibleSheaf

/-!
# No nontrivial two-torsion in the actual projective-line Picard group

An actual Picard unit has an original module-sheaf representative. The
proved tensor-invertibility criterion makes that representative an
actual invertible sheaf. Equality of its squared class with one produces
an actual tensor-square isomorphism, so the proved projective-line
trivialization makes the original Picard class one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveLinePicardTwoTorsion

variable (k : Type u) [Field k]

/-- The original tensor Picard group of the actual projective line has no nontrivial two-torsion. -/
theorem eq_one_of_sq_eq_one (p : (projectiveSpace k 1).Pic) (hp : p ^ 2 = 1) : p = 1 := by
  letI := Types.instFunLike.{u}
  letI := Types.instConcreteCategory.{u}
  let X := projectiveSpace k 1
  letI := Scheme.Modules.monoidalCategory X
  let a : (Skeleton X.Modules)ˣ := p
  let M : X.Modules := (fromSkeleton X.Modules).obj a.val
  have hM : toSkeleton M = a.val := Quotient.out_eq a.val
  have hunit : IsUnit (toSkeleton M) := hM.symm ▸ a.isUnit
  let L : InvertibleSheaf X :=
    ⟨M, SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton M hunit⟩
  have ha : a ^ 2 = 1 := hp
  have hsquare : toSkeleton (M ⊗ M) = toSkeleton (𝟙_ X.Modules) := by
    have h := congrArg Units.val ha
    change a.val ^ 2 = 1 at h
    simpa only [pow_two, ← hM, ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq] using h
  obtain ⟨e⟩ := (show Nonempty (M ⊗ M ≅ 𝟙_ X.Modules) from Quotient.exact hsquare)
  let e' : L.obj ⊗ L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    e ≪≫ PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  let t : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    ProjectiveLineSquareTriviality.invertibleUnitIsoOfSquareIso k L e'
  change a = 1
  apply Units.ext
  change a.val = (1 : Skeleton X.Modules)
  rw [← hM, Skeleton.one_eq]
  exact Quotient.sound ⟨t ≪≫
    (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm⟩

end KltDP.Geometry.ProjectiveLinePicardTwoTorsion
