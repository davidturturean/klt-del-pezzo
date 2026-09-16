import KltDP.Geometry.AffineCohomologyVanishing
import KltDP.Geometry.ProjectiveLineCanonicalFormula

/-!
# Projective-line consumers of proved affine vanishing

The all-degree affine quasicoherent vanishing proof supplies the only
remaining premise of the existing projective-line genus and canonical-degree
adapters. These two conclusions have no vanishing hypothesis.

Source draft: VM elaboration and compiled dependency audit remain pending.
-/

noncomputable section

universe u

namespace KltDP.Geometry.AffineCohomologyPort

variable (k : Type u) [Field k]

/-- The original projective line has genus zero, from proved affine vanishing. -/
theorem genus_projectiveLine_eq_zero :
    CurveCanonical.genus (projectiveSpaceToSpec k 1) = 0 :=
  OpenRestrictionExtOne.genus_projectiveLine_eq_zero_of_affineVanishing k
    affineVanishingLiteral_proved

/-- The original projective line satisfies the canonical degree formula. -/
theorem canonicalDegreeFormula_projectiveLine :
    CurveCanonical.CanonicalDegreeFormula (projectiveSpaceToSpec k 1) :=
  ProjectiveLineCanonicalFormula.canonicalDegreeFormula_projectiveLine k
    affineVanishingLiteral_proved

end KltDP.Geometry.AffineCohomologyPort
