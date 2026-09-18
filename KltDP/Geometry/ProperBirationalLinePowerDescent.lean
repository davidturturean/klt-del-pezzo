import KltDP.Geometry.ProperBirationalTargetIso
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# Actual line-power descent to the original birational target

The target isomorphism is constructed from the original contracted curves.
Pulling back the actual ample-factor line along that isomorphism gives a line
on the original target; pullback composition retains the original power class.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.ProperBirationalLinePowerDescent

/-- Actual sheaf pullback composition, expressed in the original Picard groups. -/
theorem pullback_toPic_of_factor {S X Y : Scheme.{u}}
    (π : S ⟶ X) (g : X ⟶ Y) (f : S ⟶ Y)
    (h : π ≫ g = f) (A : InvertibleSheaf Y) :
    (pullbackInvertibleSheaf π (pullbackInvertibleSheaf g A)).toPic =
      (pullbackInvertibleSheaf f A).toPic := by
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic,
    ← schemePicardPullbackHom_toPic]
  exact (congrArg (fun q => q A.toPic) (schemePicardPullbackHom_comp g π)).symm.trans
    (congrArg (fun q => schemePicardPullbackHom q A.toPic) h)

/-- The actual positive power pulled back from a contraction target descends
to any original normal projective target contracting the same prime curves. -/
theorem exists_line_of_same_exceptional_curves
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X Y : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (f : S.toScheme ⟶ Y.toScheme)
    [IsProper π] [IsProper f]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hf : f ≫ Y.structureMorphism = S.structureMorphism)
    (hbirπ : IsBirationalScheme π) (hbirf : IsBirationalScheme f)
    (hsame : ∀ C : S.PrimeCurve, IsExceptionalCurve π C ↔ IsExceptionalCurve f C)
    (L : InvertibleSheaf S.toScheme) (A : InvertibleSheaf Y.toScheme) (m : ℕ)
    (hpower : Nonempty ((pullbackInvertibleSheaf f A).obj ≅
      (InvertibleSheafSectionPowers.power L m).obj)) :
    ∃ B : InvertibleSheaf X.toScheme,
      (pullbackInvertibleSheaf π B).toPic = L.toPic ^ m := by
  obtain ⟨e, he, _, _⟩ := ProperBirationalTargetIso.exists_iso_of_same_exceptional_curves
    π f hπ hf hbirπ hbirf hsame
  refine ⟨pullbackInvertibleSheaf e.hom A, ?_⟩
  calc
    (pullbackInvertibleSheaf π (pullbackInvertibleSheaf e.hom A)).toPic =
        (pullbackInvertibleSheaf f A).toPic := pullback_toPic_of_factor π e.hom f he A
    _ = (InvertibleSheafSectionPowers.power L m).toPic :=
      SchemeKernelIdealIsoTransport.toPic_eq_of_iso _ _ hpower.some
    _ = L.toPic ^ m := InvertibleSheafSectionPowers.power_toPic L m

end KltDP.Geometry.ProperBirationalLinePowerDescent
#check @KltDP.Geometry.ProperBirationalLinePowerDescent.exists_line_of_same_exceptional_curves
#print axioms KltDP.Geometry.ProperBirationalLinePowerDescent.exists_line_of_same_exceptional_curves
