import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.ProjectiveChartNormal
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normality of actual affine section rings

An actual nonempty affine open of an integral normal scheme has an
integrally closed section ring. The proof uses the pinned descent theorem
from maximal-ideal localizations, identifies each such localization with
the corresponding actual structure-sheaf stalk, and transports the given
stalk normality through that canonical equivalence. No Noetherian or
dimension assumption is needed for this normality descent.

The surface wrappers separately supply Noetherianity from the actual
finite-type structure morphism. Together these are the ring hypotheses
used by `AffinePrincipalSupport` and `DivisorOrderTransport`.

Reused source: Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b,
`IsIntegrallyClosed.of_localization_maximal` in
`RingTheory/LocalProperties/IntegrallyClosed.lean` and
`IsAffineOpen.isLocalization_stalk'` in `AlgebraicGeometry/AffineScheme.lean`
(Apache-2.0). Integral closedness under a ring equivalence reuses the
already proved project helper `isIntegrallyClosed_of_ringEquiv`.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

/-- The actual section ring of a nonempty affine open in an integral
normal scheme is integrally closed, by descent from its actual stalks. -/
theorem isIntegrallyClosed_affineSections_of_isNormal
    (X : Scheme.{u}) [IsIntegral X] (hnormal : IsNormalScheme X)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _hp hpmax
  letI : p.IsMaximal := hpmax
  let q : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hqU : hU.fromSpec.base q ∈ U := (hU.isoSpec.inv.base q).2
  letI : IsDomain (X.presheaf.stalk (hU.fromSpec.base q)) :=
    (hnormal (hU.fromSpec.base q)).1
  letI : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec.base q)) :=
    (hnormal (hU.fromSpec.base q)).2
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base q)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec.base q, hqU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec.base q)) p :=
    hU.isLocalization_stalk' q hqU
  let e : Localization.AtPrime p ≃ₐ[Γ(X, U)]
      X.presheaf.stalk (hU.fromSpec.base q) :=
    IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk (hU.fromSpec.base q))
  exact isIntegrallyClosed_of_ringEquiv e.symm.toRingEquiv

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Every actual nonempty affine section ring of the normal projective
surface is integrally closed; this is derived from the stated normality. -/
theorem affineSections_isIntegrallyClosed
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X.toScheme, U) :=
  isIntegrallyClosed_affineSections_of_isNormal X.toScheme X.normal hU

/-- Every actual affine section ring is Noetherian, using projectivity's
finite-type map over the field and the resulting local Noetherianity. -/
theorem affineSections_isNoetherianRing
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(X.toScheme, U) := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  exact IsLocallyNoetherian.component_noetherian ⟨U, hU⟩

end NormalProjectiveSurface

end KltDP.Geometry
