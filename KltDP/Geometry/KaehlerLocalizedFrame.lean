import KltDP.Geometry.FrameRestrictionDeterminant
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Module

/-!
# Kähler frames under a localization, and their frame-change unit

BRIEF33 takes the *overlap* route to the surface canonical class: a cocycle needs frames only on the
overlaps of a cover, and on a common basic open of two charts the section ring is a **localization** of
each chart ring.  This module supplies the ring-level half of that route — the chart frame promoted
along a localization, and the comparison of two such frames.

* **`kaehlerLocalizationMap`**: `KaehlerDifferential.map k k A B` repackaged as a map semilinear over
  `algebraMap A B` (it is `A`-linear into a `B`-module; the pin has no such repackaging).
* **`localizedFrame`**: a chart basis of `Ω[A⁄k]` promoted to a basis of `Ω[B⁄k]`, through the pinned
  `Basis.ofIsLocalizedModule` and the pinned instance `KaehlerDifferential.isLocalizedModule_map`
  (which is exactly `Algebra.FormallyEtale.of_isLocalization` in disguise).  `localizedFrame_apply`
  records that its vectors are the images of the chart frame's vectors.
* **`frameChangeUnit_localizedFrame`**: the frame-change unit of two promoted frames is the image of
  the chart's own frame-change unit — proved by feeding `kaehlerLocalizationMap` to
  `FrameRestrictionDeterminant.frameChangeUnit_restrict`, because
  `Basis.ofIsLocalizedModule_apply` supplies precisely that lemma's hypothesis.
* **`presentationJacobian_localized`**: hence, for two submersive presentations of the chart, the unit
  on the localization is the image of `presentationJacobian` — the overlap unit of route (b), with no
  free-sheaf sections anywhere.
* **`localizedFrame_self`, `localizedFrame_mul`**: the two `IsCocycle` shapes for promoted frames.

Nothing is admitted here.  Everything is either pinned (`Basis.ofIsLocalizedModule`,
`KaehlerDifferential.map`, `isLocalizedModule_map`) or this lane's already-compiled
`FrameRestrictionDeterminant` / `TopDifferentialFrameChange`.
-/

noncomputable section

open KltDP.Geometry.AffineTopDifferentialFrame KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.FrameRestrictionDeterminant

universe u

namespace KltDP.Geometry.KaehlerLocalizedFrame

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (S : Submonoid A) [IsLocalization S B]
variable {n : ℕ}

/-- The Kähler map of a localization, as a map semilinear over `algebraMap A B`. -/
def kaehlerLocalizationMap :
    KaehlerDifferential k A →ₛₗ[algebraMap A B] KaehlerDifferential k B where
  toFun := KaehlerDifferential.map k k A B
  map_add' := map_add _
  map_smul' a x := by
    have h : KaehlerDifferential.map k k A B (a • x) =
        a • KaehlerDifferential.map k k A B x := map_smul _ a x
    rw [h]
    exact (algebraMap_smul B a (KaehlerDifferential.map k k A B x)).symm

@[simp]
theorem kaehlerLocalizationMap_apply (x : KaehlerDifferential k A) :
    kaehlerLocalizationMap k A B x = KaehlerDifferential.map k k A B x := rfl

/-- **The chart frame promoted along the localization.** -/
def localizedFrame (b : Basis (Fin n) A (KaehlerDifferential k A)) :
    Basis (Fin n) B (KaehlerDifferential k B) :=
  b.ofIsLocalizedModule B S (KaehlerDifferential.map k k A B)

@[simp]
theorem localizedFrame_apply (b : Basis (Fin n) A (KaehlerDifferential k A)) (i : Fin n) :
    localizedFrame k A B S b i = KaehlerDifferential.map k k A B (b i) :=
  Basis.ofIsLocalizedModule_apply B S (KaehlerDifferential.map k k A B) b i

/-- **The frame-change unit of two promoted frames is the image of the chart's unit.** -/
theorem frameChangeUnit_localizedFrame (b b' : Basis (Fin n) A (KaehlerDifferential k A)) :
    frameChangeUnit (localizedFrame k A B S b) (localizedFrame k A B S b') =
      Units.map (algebraMap A B).toMonoidHom (frameChangeUnit b b') :=
  frameChangeUnit_restrict b b' (localizedFrame k A B S b) (localizedFrame k A B S b')
    (kaehlerLocalizationMap k A B)
    (fun t => (localizedFrame_apply k A B S b t).symm)
    (fun t => (localizedFrame_apply k A B S b' t).symm)

/-- **The overlap unit is the image of the presentation Jacobian**, with no free-sheaf sections. -/
theorem presentationJacobian_localized (P P' : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) (hP' : P'.dimension = 2) :
    frameChangeUnit (localizedFrame k A B S (presentationDifferentialBasis k A P hP))
        (localizedFrame k A B S (presentationDifferentialBasis k A P' hP')) =
      Units.map (algebraMap A B).toMonoidHom (presentationJacobian k A P P' hP hP') :=
  frameChangeUnit_localizedFrame k A B S _ _

/-- Normalisation for promoted frames: the first `IsCocycle` field. -/
theorem localizedFrame_self (b : Basis (Fin n) A (KaehlerDifferential k A)) :
    frameChangeUnit (localizedFrame k A B S b) (localizedFrame k A B S b) = 1 :=
  frameChangeUnit_self _

/-- The triple-overlap identity for promoted frames: the second `IsCocycle` field. -/
theorem localizedFrame_mul (b b' b'' : Basis (Fin n) A (KaehlerDifferential k A)) :
    frameChangeUnit (localizedFrame k A B S b) (localizedFrame k A B S b') *
        frameChangeUnit (localizedFrame k A B S b') (localizedFrame k A B S b'') =
      frameChangeUnit (localizedFrame k A B S b) (localizedFrame k A B S b'') :=
  frameChangeUnit_mul _ _ _

end KltDP.Geometry.KaehlerLocalizedFrame
