import KltDP.Geometry.PointBlowupLocalUniqueness
import KltDP.Compatibility.SchemeTwoOpenCoverIso
import KltDP.Geometry.AffineBlowupExceptionalFiber
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The actual center fiber of the whole point blowup

The reduced closed center is the actual quotient prime in the chosen
affine chart. Its fiber under the whole glued projection is identified
with the already constructed affine center fiber, preserving both maps.
The original affine square is proved to be a pullback from its exact
open range; pasting that square with the affine center fiber constructs
the isomorphism and both of its projection identities.

The quotient-glued exceptional scheme therefore maps by a closed immersion
to the whole point blowup, with image exactly the original projection's
fiber over the selected point. No properness, integrality, fiber model,
or isomorphism is supplied as a new hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- The actual quotient-center morphism into the original whole scheme. -/
def closedCenterInclusion : Spec (CommRingCat.of (R ⧸ q.asIdeal)) ⟶ X :=
  AffineBlowup.centerInclusion q.asIdeal ≫ j

/-- The affine quotient center has exactly the selected maximal point
as its image. This follows from the actual quotient spectrum map. -/
theorem range_affineCenterInclusion :
    Set.range (AffineBlowup.centerInclusion q.asIdeal).base = {q} := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)) = {q}
  rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  apply Set.ext
  intro p
  change (q.asIdeal : Set R) ⊆ p.asIdeal ↔ p = q
  constructor
  · intro hp
    exact PrimeSpectrum.ext
      (Ideal.IsMaximal.eq_of_le (inferInstance : q.asIdeal.IsMaximal)
        p.isPrime.ne_top hp).symm
  · rintro rfl
    exact Set.Subset.rfl

/-- The whole center inclusion has the actual selected singleton image. -/
theorem range_closedCenterInclusion :
    Set.range (closedCenterInclusion j q).base = {j.base q} := by
  change Set.range (j.base ∘ (AffineBlowup.centerInclusion q.asIdeal).base) = _
  rw [Set.range_comp, range_affineCenterInclusion, Set.image_singleton]

include hclosed in
/-- The affine quotient inclusion followed by the open chart is closed
in the whole scheme because its actual singleton image is closed. -/
theorem closedCenterInclusion_isClosedImmersion :
    IsClosedImmersion (closedCenterInclusion j q) := by
  letI : IsClosedImmersion (AffineBlowup.centerInclusion q.asIdeal) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsImmersion (closedCenterInclusion j q) := by
    unfold closedCenterInclusion
    infer_instance
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_closedCenterInclusion]
  exact hclosed

/-- The literal categorical fiber over the actual reduced closed center. -/
abbrev globalCenterFiber :=
  pullback (projection j q hclosed) (closedCenterInclusion j q)

/-- Its actual morphism into the whole constructed source. -/
abbrev globalCenterFiberι : globalCenterFiber j q hclosed ⟶ scheme j q hclosed :=
  pullback.fst _ _

/-- Its actual morphism to the original quotient center. -/
abbrev globalCenterFiberToCenter :
    globalCenterFiber j q hclosed ⟶ Spec (CommRingCat.of (R ⧸ q.asIdeal)) :=
  pullback.snd _ _

instance globalCenterFiberι_isClosedImmersion :
    IsClosedImmersion (globalCenterFiberι j q hclosed) := by
  exact MorphismProperty.pullback_fst (P := @IsClosedImmersion)
    (projection j q hclosed) (closedCenterInclusion j q)
    (closedCenterInclusion_isClosedImmersion j q hclosed)

/-- The actual categorical fiber inclusion has the full point-fiber image. -/
theorem range_globalCenterFiberι :
    Set.range (globalCenterFiberι j q hclosed).base =
      (projection j q hclosed).base ⁻¹' {j.base q} := by
  rw [globalCenterFiberι, Scheme.Pullback.range_fst, range_closedCenterInclusion]

/-- The original affine Rees square is an actual pullback: its open
source piece has exactly the proved inverse-image range. -/
theorem affineBlowup_isPullback :
    IsPullback (affineBlowupι j q hclosed) (AffineBlowup.toSpec q.asIdeal)
      (projection j q hclosed) j :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _
    (affineBlowupι_projection j q hclosed) (range_affineBlowupι j q hclosed)

/-- Paste the actual affine center square with the derived global affine
square. The resulting square is the whole projection over the same center. -/
theorem affineCenterFiber_isPullback :
    IsPullback (AffineBlowup.centerFiberι q.asIdeal ≫ affineBlowupι j q hclosed)
      (AffineBlowup.centerFiberToCenter q.asIdeal)
      (projection j q hclosed) (closedCenterInclusion j q) :=
  (IsPullback.of_hasPullback (AffineBlowup.toSpec q.asIdeal)
    (AffineBlowup.centerInclusion q.asIdeal)).paste_horiz
      (affineBlowup_isPullback j q hclosed)

/-- The affine and whole-scheme center fibers are canonically isomorphic
by the actual pasted pullback square. -/
def affineCenterFiberIso :
    AffineBlowup.centerFiber q.asIdeal ≅ globalCenterFiber j q hclosed :=
  (affineCenterFiber_isPullback j q hclosed).isoPullback

@[reassoc] theorem affineCenterFiberIso_hom_ι :
    (affineCenterFiberIso j q hclosed).hom ≫ globalCenterFiberι j q hclosed =
      AffineBlowup.centerFiberι q.asIdeal ≫ affineBlowupι j q hclosed :=
  (affineCenterFiber_isPullback j q hclosed).isoPullback_hom_fst

@[reassoc] theorem affineCenterFiberIso_hom_toCenter :
    (affineCenterFiberIso j q hclosed).hom ≫ globalCenterFiberToCenter j q hclosed =
      AffineBlowup.centerFiberToCenter q.asIdeal :=
  (affineCenterFiber_isPullback j q hclosed).isoPullback_hom_snd

/-- The original quotient-glued exceptional scheme is the center fiber
of the whole constructed blowup, with its original inclusion preserved. -/
def exceptionalGlobalFiberIso :
    AffineBlowup.exceptionalScheme q.asIdeal ≅ globalCenterFiber j q hclosed :=
  AffineBlowup.exceptionalFiberIso q.asIdeal ≪≫ affineCenterFiberIso j q hclosed

@[reassoc] theorem exceptionalGlobalFiberIso_hom_ι :
    (exceptionalGlobalFiberIso j q hclosed).hom ≫ globalCenterFiberι j q hclosed =
      AffineBlowup.exceptionalι q.asIdeal ≫ affineBlowupι j q hclosed := by
  rw [exceptionalGlobalFiberIso, Iso.trans_hom, Category.assoc,
    affineCenterFiberIso_hom_ι, ← Category.assoc,
    AffineBlowup.exceptionalFiberIso_hom_ι]

/-- Its original inclusion into the whole blowup is a closed immersion,
proved through the actual categorical fiber rather than assumed. -/
theorem exceptionalGlobalInclusion_isClosedImmersion :
    IsClosedImmersion (AffineBlowup.exceptionalι q.asIdeal ≫
      affineBlowupι j q hclosed) := by
  rw [← exceptionalGlobalFiberIso_hom_ι]
  infer_instance

/-- The whole exceptional inclusion has exactly the original point fiber
as its image. No proper subset of that fiber is substituted. -/
theorem range_exceptionalGlobalInclusion :
    Set.range (AffineBlowup.exceptionalι q.asIdeal ≫
      affineBlowupι j q hclosed).base =
        (projection j q hclosed).base ⁻¹' {j.base q} := by
  rw [← exceptionalGlobalFiberIso_hom_ι]
  change Set.range ((globalCenterFiberι j q hclosed).base ∘
    (exceptionalGlobalFiberIso j q hclosed).hom.base) = _
  rw [Set.range_comp, (exceptionalGlobalFiberIso j q hclosed).hom.surjective.range_eq,
    Set.image_univ, range_globalCenterFiberι]

end KltDP.Geometry.PointBlowupGluing
