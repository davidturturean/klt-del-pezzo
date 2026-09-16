import KltDP.Geometry.SingularPoints
import KltDP.Geometry.PrimeCurveCodimension

/-!
# Actual normal stalks of dimension one are DVRs

This module reuses the proved regularity of a Noetherian integrally closed
local domain of dimension at most one. In dimension exactly one its actual
cotangent space has dimension one. The pinned Mathlib DVR characterization
then proves that the original local ring is a discrete valuation ring.

The scheme wrappers use actual structure-sheaf stalks and the existing
normality predicate. The prime-curve specialization consumes the separately
proved generic-point dimension theorem. No DVR, local-dimension comparison,
or prime-curve consequence is stored as a new structure field.

Reused source: Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b,
`RingTheory/DiscreteValuationRing/TFAE.lean`,
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` (Apache-2.0).
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

/-- A regular local domain of dimension exactly one is a DVR, by the
actual one-dimensional cotangent-space characterization. -/
theorem isDiscreteValuationRing_of_regularLocal_of_ringKrullDim_eq_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R]
    (hR : RegularLocal R) (hdim : ringKrullDim R = 1) :
    IsDiscreteValuationRing R := by
  letI : IsNoetherianRing R := hR.1
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hcot :
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :
        WithBot ℕ∞) = 1 := hR.2.symm.trans hdim
  exact_mod_cast hcot

/-- A Noetherian integrally closed local domain of dimension one is an
actual DVR. Both regularity and the DVR conclusion are proved. -/
theorem isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] (hdim : ringKrullDim R = 1) :
    IsDiscreteValuationRing R :=
  isDiscreteValuationRing_of_regularLocal_of_ringKrullDim_eq_one R
    (regularLocal_of_isIntegrallyClosed_of_ringKrullDim_le_one R hdim.le) hdim

/-- At an actual normal scheme point, Noetherianity and local dimension
one imply the DVR property. The domain input of Mathlib's DVR class is
explicitly the domain proof already contained in normality. -/
theorem normalStalk_isDiscreteValuationRing (X : Scheme.{u})
    (hnormal : IsNormalScheme X) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    @IsDiscreteValuationRing (X.presheaf.stalk x) _ (hnormal x).1 := by
  letI : IsDomain (X.presheaf.stalk x) := (hnormal x).1
  letI : IsIntegrallyClosed (X.presheaf.stalk x) := (hnormal x).2
  exact isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (X.presheaf.stalk x) hdim

/-- The same actual-stalk conclusion with Noetherianity derived from a
locally Noetherian scheme through its affine stalk localization. -/
theorem normalStalk_isDiscreteValuationRing_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hnormal : IsNormalScheme X) (x : X)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    @IsDiscreteValuationRing (X.presheaf.stalk x) _ (hnormal x).1 := by
  letI : IsNoetherianRing (X.presheaf.stalk x) :=
    isNoetherianRing_stalk_of_isLocallyNoetherian X x
  exact normalStalk_isDiscreteValuationRing X hnormal x hdim

namespace NormalProjectiveSurface

variable {k : Type u} [Field k]

/-- A dimension-one stalk of the actual normal projective surface is a
DVR. The surface's Noetherian stalk, domain, and normality instances are
already derived from its stated geometric hypotheses. -/
theorem stalk_isDiscreteValuationRing_of_ringKrullDim_eq_one
    (X : NormalProjectiveSurface k) (x : X.Point)
    (hdim : ringKrullDim (X.stalk x) = 1) :
    IsDiscreteValuationRing (X.stalk x) :=
  normalStalk_isDiscreteValuationRing X.toScheme X.normal x hdim

/-- The actual generic-point stalk of every actual prime curve on the
normal projective surface is a DVR. Its local dimension is proved in
`PrimeCurveCodimension`, rather than assumed here. -/
theorem PrimeCurve.genericPoint_isDiscreteValuationRing
    {X : NormalProjectiveSurface k} (C : X.PrimeCurve) :
    IsDiscreteValuationRing (X.stalk C.genericPoint) :=
  X.stalk_isDiscreteValuationRing_of_ringKrullDim_eq_one C.genericPoint
    C.ringKrullDim_stalk_genericPoint

end NormalProjectiveSurface

end KltDP.Geometry
