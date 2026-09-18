import KltDP.Geometry.AmpleSerre

/-!
# Global generation and semiampleness from an actual unit isomorphism

The existing free-singleton comparison generates the structure module.
Transport along the given isomorphism generates the original line, whose
first power then witnesses the existing semiampleness predicate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.Positivity

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- An actual frame globally generates the original invertible sheaf. -/
theorem isGloballyGenerated_of_unitIso
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :
    IsGloballyGenerated L.obj := by
  apply AmpleSerre.isGloballyGenerated_of_iso e.symm
  exact ⟨PUnit, (_root_.SheafOfModules.freeUniqueIsoUnit (R := X.ringCatSheaf) PUnit).hom,
    inferInstance⟩

/-- Its first tensor power witnesses semiampleness of the original line. -/
theorem isSemiample_of_unitIso
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) : IsSemiample L :=
  ⟨1, Nat.zero_lt_one, L, (pow_one L.toPic).symm, isGloballyGenerated_of_unitIso L e⟩

end KltDP.Geometry.Positivity
