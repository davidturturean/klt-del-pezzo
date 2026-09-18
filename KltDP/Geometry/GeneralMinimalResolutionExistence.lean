import KltDP.Literature.LipmanResolutionLiteral
import KltDP.Literature.HartshorneCastelnuovoLiteral
import KltDP.Geometry.LipmanRawSourceConsumer
import KltDP.Geometry.HartshorneCastelnuovoContraction
import KltDP.Geometry.SingularStalkCompletionZariski

/-!
# General resolution and minimal resolution existence

The source and map are constructed for the original normal projective
surface. Completion normality, projectivity of the resolution source,
contraction factorization, and termination are supplied by the separately
proved adapters. No resolution or contraction existence input remains.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory KltDP.Literature.Stacks
universe u
namespace KltDP.Geometry.GeneralResolution

/-- Original proper birational regular modifications from the full Lipman source. -/
theorem modification (k : Type u) [Field k] [IsAlgClosed k] :
    LipmanModificationLiteral k :=
  LipmanIdentityNormalization.lipmanModificationLiteral_of_raw_source
    Literature.Stacks.lipman_resolution_of_normal_completions_literal

/-- Original minus-one contractions from the complete Castelnuovo source. -/
theorem contraction (k : Type u) [Field k] [IsAlgClosed k] :
    CastelnuovoContractionLiteral k :=
  castelnuovoContractionLiteral_of_hartshorne
    Literature.Hartshorne.castelnuovo_contraction_literal

/-- Every original normal projective surface has a projective regular resolution. -/
theorem exists_resolution {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsResolution S X π :=
  (lipmanResolutionLiteral_of_zariski
    Literature.Zariski.closedPoint_normal_completion_literal (modification k)).exists_resolution
    X (normalSurface_singularLocus_finite X)

/-- Every original normal projective surface has a minimal resolution. -/
theorem exists_minimalResolution {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsMinimalResolution S X π :=
  exists_minimalResolution_of_modification_and_contraction_inputs
    (modification k) (contraction k) X

end KltDP.Geometry.GeneralResolution
#check @KltDP.Geometry.GeneralResolution.exists_resolution
#check @KltDP.Geometry.GeneralResolution.exists_minimalResolution
#print axioms KltDP.Geometry.GeneralResolution.modification
#print axioms KltDP.Geometry.GeneralResolution.contraction
#print axioms KltDP.Geometry.GeneralResolution.exists_resolution
#print axioms KltDP.Geometry.GeneralResolution.exists_minimalResolution
