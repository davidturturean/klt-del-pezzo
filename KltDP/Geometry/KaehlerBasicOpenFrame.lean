import KltDP.Geometry.AffineDifferentialSectionsFrame
import KltDP.Geometry.KaehlerLocalizedFrame

/-!
# Chart frames on a basic open, and the instances that make them available

`KaehlerLocalizedFrame.localizedFrame` promotes a chart frame of `Ω[A⁄k]` to a frame of `Ω[B⁄k]`
whenever `B` is a localization of `A`. Applying it to a **basic open** of an affine chart of a scheme
needs three things in scope, and this module settles exactly which of them the pin already provides:

* `Algebra Γ(X, W) Γ(X, X.basicOpen r)` — **already a global instance** in pinned Mathlib,
  `AlgebraicGeometry.Scheme.algebra_section_section_basicOpen`, whose `algebraMap` is the sheaf
  restriction `X.presheaf.map (homOfLE (X.basicOpen_le r)).op`. Nothing to do.
* `IsLocalization (Submonoid.powers r) Γ(X, X.basicOpen r)` — **not** an instance for a general
  affine open. `IsAffineOpen.isLocalization_basicOpen` is a *theorem*; the only instance,
  `isLocalization_away_of_isAffine`, needs `[IsAffine X]` and `r : Γ(X, ⊤)`. So it must be supplied
  at the use site, exactly as pinned Mathlib does everywhere (`letI := hU.isLocalization_basicOpen r`).
  `IsLocalization.Away` is an `abbrev` for `IsLocalization (Submonoid.powers r)`, so it matches
  `localizedFrame`'s `[IsLocalization S B]` with `S := Submonoid.powers r` without massaging.
  Recorded here as **`basicOpen_isLocalization`**.
* `IsScalarTower k Γ(X, W) Γ(X, X.basicOpen r)` — **not** available, and it is the one that needs a
  proof. Both `k`-algebra structures are the ones induced by the structure morphism
  (`baseToAffineSectionsMap`), and the accepted `baseToAffineSectionsMap_restrict` says precisely that
  restriction commutes with them, which is `IsScalarTower.of_algebraMap_eq`'s hypothesis.
  Recorded here as **`basicOpen_isScalarTower`**.

These are stated as named theorems rather than instances on purpose: `IsLocalization` and
`IsScalarTower` are `Prop` classes whose statements mention the `letI`-supplied `k`-algebra
structures, so registering them globally would fix a choice of algebra structure that the rest of the
tree deliberately keeps explicit (`affineSectionsAlgebra` is "a named structure, not a global
instance that could select a different map").

With those settled:

* **`basicOpenFrame`**: a chart frame of `Ω[Γ(X, W)⁄k]` promoted to a frame of
  `Ω[Γ(X, X.basicOpen r)⁄k]`.
* **`frameChangeUnit_basicOpenFrame`**: its transition unit is the image of the chart's transition
  unit under the restriction map — the overlap unit of the atlas route.
* **`basicOpenSectionsFrame`** and **`frameChangeUnit_basicOpenSectionsFrame`**: the same frame
  carried onto the sections of `Ω_{X/k}` over the basic open, via
  `AffineDifferentialSectionsFrame.sectionsFrame`, with the transition unit *unchanged* by that
  second step. So the sheaf-level unit on a basic open is the image of the ring-level chart unit,
  with no further comparison.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.KaehlerLocalizedFrame
open KltDP.Geometry.AffineDifferentialSectionsFrame

universe u

namespace KltDP.Geometry.KaehlerBasicOpenFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {n : ℕ}

/-- **The basic open of an affine chart is a localization of it.** Pinned Mathlib proves this as a
theorem, not an instance, for a general affine open. -/
theorem basicOpen_isLocalization {W : X.Opens} (hW : IsAffineOpen W) (r : Γ(X, W)) :
    IsLocalization (Submonoid.powers r) Γ(X, X.basicOpen r) :=
  hW.isLocalization_basicOpen r

/-- **The two structure-induced `k`-algebra structures form a scalar tower with the restriction.**
This is the accepted `baseToAffineSectionsMap_restrict` read through
`IsScalarTower.of_algebraMap_eq`. -/
theorem basicOpen_isScalarTower {W : X.Opens} (hW : IsAffineOpen W) (r : Γ(X, W)) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    letI : Algebra k Γ(X, X.basicOpen r) :=
      (baseToAffineSectionsMap f (hW.basicOpen r)).hom.toAlgebra
    IsScalarTower k Γ(X, W) Γ(X, X.basicOpen r) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  letI : Algebra k Γ(X, X.basicOpen r) :=
    (baseToAffineSectionsMap f (hW.basicOpen r)).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  exact (congrArg (fun φ : CommRingCat.of k ⟶ Γ(X, X.basicOpen r) => φ.hom a)
    (baseToAffineSectionsMap_restrict f hW (hW.basicOpen r) (X.basicOpen_le r))).symm

/-- **A chart frame promoted to the basic open.** -/
def basicOpenFrame {W : X.Opens} (hW : IsAffineOpen W) (r : Γ(X, W)) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    letI : Algebra k Γ(X, X.basicOpen r) :=
      (baseToAffineSectionsMap f (hW.basicOpen r)).hom.toAlgebra
    Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)) →
      Basis (Fin n) Γ(X, X.basicOpen r) (KaehlerDifferential k Γ(X, X.basicOpen r)) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  letI : Algebra k Γ(X, X.basicOpen r) :=
    (baseToAffineSectionsMap f (hW.basicOpen r)).hom.toAlgebra
  letI := basicOpen_isLocalization hW r
  letI := basicOpen_isScalarTower f hW r
  exact fun b => localizedFrame k Γ(X, W) Γ(X, X.basicOpen r) (Submonoid.powers r) b

/-- **The transition unit on the basic open is the image of the chart's transition unit.** -/
theorem frameChangeUnit_basicOpenFrame {W : X.Opens} (hW : IsAffineOpen W) (r : Γ(X, W)) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    letI : Algebra k Γ(X, X.basicOpen r) :=
      (baseToAffineSectionsMap f (hW.basicOpen r)).hom.toAlgebra
    ∀ b b' : Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)),
      frameChangeUnit (basicOpenFrame f hW r b) (basicOpenFrame f hW r b') =
        Units.map (algebraMap Γ(X, W) Γ(X, X.basicOpen r)).toMonoidHom
          (frameChangeUnit b b') := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  letI : Algebra k Γ(X, X.basicOpen r) :=
    (baseToAffineSectionsMap f (hW.basicOpen r)).hom.toAlgebra
  letI := basicOpen_isLocalization hW r
  letI := basicOpen_isScalarTower f hW r
  intro b b'
  exact frameChangeUnit_localizedFrame k Γ(X, W) Γ(X, X.basicOpen r) (Submonoid.powers r) b b'

/-- **The promoted frame, carried onto the sections of the differential sheaf over the basic open.**
-/
def basicOpenSectionsFrame {W : X.Opens} (hW : IsAffineOpen W) (r : Γ(X, W)) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)) →
      Basis (Fin n) Γ(X, X.basicOpen r)
        ((baseRingSheaf f).val.obj (op (X.basicOpen r))) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  exact fun b => sectionsFrame f (hW.basicOpen r) (basicOpenFrame f hW r b)

/-- **The sheaf-level transition unit on a basic open is the image of the chart's ring-level unit.**
The transport to sections contributes nothing, because it is linear over the section ring itself. -/
theorem frameChangeUnit_basicOpenSectionsFrame {W : X.Opens} (hW : IsAffineOpen W)
    (r : Γ(X, W)) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    ∀ b b' : Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)),
      frameChangeUnit (basicOpenSectionsFrame f hW r b) (basicOpenSectionsFrame f hW r b') =
        Units.map (algebraMap Γ(X, W) Γ(X, X.basicOpen r)).toMonoidHom
          (frameChangeUnit b b') := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  intro b b'
  exact (frameChangeUnit_sectionsFrame f (hW.basicOpen r) (basicOpenFrame f hW r b)
    (basicOpenFrame f hW r b')).trans (frameChangeUnit_basicOpenFrame f hW r b b')

end KltDP.Geometry.KaehlerBasicOpenFrame
