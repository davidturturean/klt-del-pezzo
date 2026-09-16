import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Geometry.InvertibleSheafPicard

/-!
# The actual cohomology Euler value on Picard classes

An isomorphism of coefficient sheaves induces the existing base-field
linear equivalences on cohomology. Their equal finranks make the original
Euler value invariant under isomorphism, so it descends through the actual
sheaf skeleton and restricts to the existing scheme Picard group.

These are equalities of the previously defined finrank expression. Its
cohomological interpretation still requires the finite-dimensionality and
vanishing hypotheses recorded in `ModuleCohomologyEuler`. No additivity
under tensor product or intersection pairing is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

namespace ModuleCohomology

/-- Equal dimensions follow from the actual induced linear isomorphism. -/
theorem cohomologyDimension_eq_of_iso {M N : X.Modules}
    (e : M ≅ N) (n : ℕ) :
    cohomologyDimension f M n = cohomologyDimension f N n :=
  ((baseFunctor f n).mapIso e).toLinearEquiv.finrank_eq

/-- The same actual Euler expression is independent of a representative. -/
theorem eulerCharacteristic_eq_of_iso {M N : X.Modules} (e : M ≅ N) :
    eulerCharacteristic f M = eulerCharacteristic f N := by
  unfold eulerCharacteristic
  have h : (fun n : ℕ => (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)) =
      (fun n : ℕ => (-1 : ℤ) ^ n * (cohomologyDimension f N n : ℤ)) := by
    funext n
    rw [cohomologyDimension_eq_of_iso f e n]
  rw [h]

end ModuleCohomology

/-- Descent uses precisely the existing quotient by actual sheaf isomorphisms. -/
def skeletonEulerValue : Skeleton X.Modules → ℤ :=
  Quotient.lift (ModuleCohomology.eulerCharacteristic f) (by
    intro M N h
    obtain ⟨e⟩ := h
    exact ModuleCohomology.eulerCharacteristic_eq_of_iso f e)

theorem skeletonEulerValue_toSkeleton (M : X.Modules) :
    skeletonEulerValue f (toSkeleton M) = ModuleCohomology.eulerCharacteristic f M := rfl

/-- Restriction to the original Picard group; this is a function, with no
claim that cohomological Euler characteristic is a group homomorphism. -/
def picardEulerValue (p : X.Pic) : ℤ :=
  skeletonEulerValue f (p : Skeleton X.Modules)

/-- The Picard class of a line bundle has the Euler value of that very sheaf. -/
theorem picardEulerValue_toPic (L : InvertibleSheaf X) :
    picardEulerValue f L.toPic = ModuleCohomology.eulerCharacteristic f L.obj := by
  letI := Scheme.Modules.monoidalCategory X
  unfold picardEulerValue
  rw [InvertibleSheaf.toPic_val, skeletonEulerValue_toSkeleton]

/-- The Picard identity evaluates on the actual structure-sheaf module. -/
theorem picardEulerValue_one :
    picardEulerValue f (1 : X.Pic) =
      ModuleCohomology.eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  letI := Scheme.Modules.monoidalCategory X
  change skeletonEulerValue f (1 : Skeleton X.Modules) = _
  rw [Skeleton.one_eq, skeletonEulerValue_toSkeleton]
  exact ModuleCohomology.eulerCharacteristic_eq_of_iso f
    (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond)

end KltDP.Geometry
