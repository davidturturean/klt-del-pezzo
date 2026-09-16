import KltDP.Geometry.AffineDifferentialGammaEquiv
import KltDP.Geometry.FrameRestrictionDeterminant

/-!
# Chart frames of the Kähler module, as frames of the differential sheaf's sections

`AffineDifferentialGammaEquiv.affineDifferentialGammaEquiv` identifies the sections of `Ω_{X/k}` over
an affine open `W` with `Ω[Γ(X, W)⁄k]`, `Γ(X, W)`-linearly.  This module carries frames across that
identification, which is what the atlas route needs: the frames it has are frames of the *ring*
Kähler module (`AffineTopDifferentialFrame.presentationDifferentialBasis`, and on a common basic open
`KaehlerLocalizedFrame.localizedFrame`), while the gluing consumes frames of the *sheaf's sections*.

* **`sectionsFrame`**: a frame of `Ω[Γ(X, W)⁄k]` transported to a frame of
  `(baseRingSheaf f).val.obj (op W)` by `Basis.map`.
* **`sectionsFrame_apply`**: its vectors are the images of the original frame's vectors.
* **`frameChangeUnit_sectionsFrame`**: **the transition unit is unchanged by the transport.** The
  frame-change unit of two transported frames is the frame-change unit of the two original frames —
  not merely its image under some comparison, because the transport is linear over `Γ(X, W)` itself.
* **`frameChangeUnit_sectionsFrame_presentation`**: hence, for two submersive presentations of the
  chart ring, the transition unit of the transported frames *is* the presentation Jacobian.

**Why this is stated for an arbitrary frame `b`.**  The atlas route supplies its frames in two
different ways — from a submersive presentation on a chart, and from `localizedFrame` on a common
basic open — and both are just particular bases of `Ω[Γ(X, W)⁄k]`.  Stating the transport and the
transition-unit identity for an arbitrary basis means neither construction needs its own version, and
the cocycle identities already proved for frame-change units (`frameChangeUnit_self`,
`frameChangeUnit_mul`, and `KaehlerLocalizedFrame`'s localized forms) transfer verbatim.

The transport costs nothing at the level of determinants: `FrameRestrictionDeterminant.det_restrict`
is stated for a map semilinear over an arbitrary ring map, and here that ring map is the identity of
`Γ(X, W)`, so the determinant is carried across unchanged.  No ring bridge appears anywhere, because
`affineDifferentialGammaEquiv` carries none.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.AffineTopDifferentialFrame KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.FrameRestrictionDeterminant
open KltDP.Geometry.AffineDifferentialGammaEquiv

universe u

namespace KltDP.Geometry.AffineDifferentialSectionsFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {n : ℕ}

/-- **A frame of the Kähler module of an affine chart ring, as a frame of the differential sheaf's
sections over that chart.** -/
def sectionsFrame {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)) →
      Basis (Fin n) Γ(X, W) ((baseRingSheaf f).val.obj (op W)) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  exact fun b => b.map (affineDifferentialGammaEquiv f hW).symm

/-- The transported frame's vectors are the images of the original frame's vectors. -/
theorem sectionsFrame_apply {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    ∀ (b : Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W))) (t : Fin n),
      sectionsFrame f hW b t = (affineDifferentialGammaEquiv f hW).symm (b t) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  intro b t
  rfl

/-- **The transition unit is unchanged by the transport to sheaf sections.** -/
theorem frameChangeUnit_sectionsFrame {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    ∀ b b' : Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)),
      frameChangeUnit (sectionsFrame f hW b) (sectionsFrame f hW b') = frameChangeUnit b b' := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  intro b b'
  apply Units.ext
  rw [frameChangeUnit_val, frameChangeUnit_val]
  exact det_restrict b b' (sectionsFrame f hW b) (sectionsFrame f hW b')
    (affineDifferentialGammaEquiv f hW).symm.toLinearMap (fun t => rfl) (fun t => rfl)

/-- **The transition unit of the transported presentation frames is the presentation Jacobian.** -/
theorem frameChangeUnit_sectionsFrame_presentation {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    ∀ (P P' : Algebra.SubmersivePresentation k Γ(X, W))
      (hP : P.dimension = 2) (hP' : P'.dimension = 2),
      frameChangeUnit (sectionsFrame f hW (presentationDifferentialBasis k Γ(X, W) P hP))
          (sectionsFrame f hW (presentationDifferentialBasis k Γ(X, W) P' hP')) =
        presentationJacobian k Γ(X, W) P P' hP hP' := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  intro P P' hP hP'
  exact frameChangeUnit_sectionsFrame f hW _ _

end KltDP.Geometry.AffineDifferentialSectionsFrame
