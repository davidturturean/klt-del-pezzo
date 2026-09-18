import KltDP.Literature.ZariskiNormalCompletion
import KltDP.Geometry.SingularStalkCompletionNormal
import KltDP.Geometry.ActualContractionMorphismDescent

/-! Direct original-stalk use and the reduced set of resolution existence inputs. -/
noncomputable section
open AlgebraicGeometry CategoryTheory KltDP.Literature.Stacks
universe u
namespace KltDP.Geometry

/-- Normality of the original completed local ring at every original singular point. -/
theorem localCompletion_singularStalk_normal
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : x ∈ singularLocus X.toScheme) :
    IsLocalRing (localCompletion (X.toScheme.presheaf.stalk x)) ∧
      IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) ∧
      IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x)) :=
  localCompletion_singularStalk_normal_of_zariski
    Literature.Zariski.closedPoint_normal_completion_literal X x hx

/-- Completion normality, source packaging, and the contraction universal property
are derived. The two geometric existence inputs remain explicit. -/
theorem exists_minimalResolution_of_modification_and_contraction_inputs
    {k : Type u} [Field k] [IsAlgClosed k]
    (hL : LipmanModificationLiteral k) (hCa : CastelnuovoContractionLiteral k)
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsMinimalResolution S X π :=
  exists_minimalResolution_of_zariski_and_remaining_inputs
    Literature.Zariski.closedPoint_normal_completion_literal hL hCa
    (contractionUniversal k) X

end KltDP.Geometry
#check @KltDP.Geometry.localCompletion_singularStalk_normal
#print axioms KltDP.Geometry.localCompletion_singularStalk_normal
#check @KltDP.Geometry.exists_minimalResolution_of_modification_and_contraction_inputs
#print axioms KltDP.Geometry.exists_minimalResolution_of_modification_and_contraction_inputs
