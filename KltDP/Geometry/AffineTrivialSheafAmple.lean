import KltDP.Geometry.AmpleOfAffineNonvanishingCover

/-!
# The original trivial sheaf is Serre ample on an affine scheme

The unit section has the entire original scheme as its intrinsic
nonvanishing open. The affine-cover criterion therefore gives an actual
instance of the existing Serre ampleness definition, without assuming
an ample sheaf or a twisted global-generation conclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineTrivialSheafAmple

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen InvertibleSheafSectionPowers

/-- The original unit section as a compatible family on the original scheme. -/
def unitSection (X : Scheme.{u}) : (InvertibleSheaf.trivial X).obj.sections :=
  (_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _)

/-- The original unit section vanishes nowhere. -/
theorem nonvanishingOpen_unitSection (X : Scheme.{u}) :
    nonvanishingOpen X (InvertibleSheaf.trivial X) (unitSection X) = ⊤ := by
  rw [InvertibleSectionNonvanishingFrame.nonvanishingOpen_eq_basicOpen
    (InvertibleSheaf.trivial X) (Iso.refl _) (unitSection X)]
  have h : frameCoefficient (InvertibleSheaf.trivial X) (Iso.refl _) (unitSection X) =
      (1 : Γ(X, ⊤)) := rfl
  rw [h, Scheme.basicOpen_one]

/-- On every original affine scheme, the original structure line sheaf
is ample in the already defined Serre sense. -/
theorem trivial_isAmple (X : Scheme.{u}) [IsAffine X] :
    AmpleSerre.IsAmple (InvertibleSheaf.trivial X) := by
  apply AmpleOfAffineNonvanishingCover.isAmple_of_finite_cover (InvertibleSheaf.trivial X)
    isCompact_univ isQuasiSeparated_univ (fun _ : PUnit.{u + 1} => unitSection X)
  · intro i
    rw [nonvanishingOpen_unitSection]
    exact isAffineOpen_top X
  · intro x hx
    apply Opens.mem_iSup.mpr
    exact ⟨PUnit.unit, by rw [nonvanishingOpen_unitSection]; trivial⟩

end KltDP.Geometry.AffineTrivialSheafAmple
