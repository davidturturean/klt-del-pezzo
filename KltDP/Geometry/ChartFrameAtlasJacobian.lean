import KltDP.Geometry.ChartFrameAtlasSheaf
import KltDP.Geometry.KaehlerFrameLocalization

/-!
# The transition unit of a Kähler atlas is the Jacobian of the coordinate change

`ChartFrameAtlasSheaf` glues an atlas of chart frames into an actual invertible sheaf, with the
transition units defined as frame-change determinants.  This module identifies those units in the
case the assembly is built for: the module family is the Kähler module of the section rings, the
frames are the Kähler bases of submersive presentations of relative dimension two carried to the
overlap, and the transition unit is then the image of the presentation Jacobian.

* **`transitionUnit_eq_presentationJacobian`**: if the two chart frames on the overlap `U i ⊓ U j`
  are the transports (`KaehlerFrameLocalization.transportedFrame`) of two submersive presentations
  along an identification `e` of the overlap's Kähler module, then the atlas transition unit is
  `Units.map (algebraMap _ _) (presentationJacobian k A P P' hP hP')`.

The identification `e` is a hypothesis, as in `KaehlerFrameLocalization`: for an overlap that is a
basic open of a chart the pinned Mathlib supplies it (`KaehlerDifferential.map` is an
`IsLocalizedModule` for `Submonoid.powers f`, and the accepted
`AffineKaehlerTildeLocalization.presheafComparison_basicOpen_bijective` uses the same fact), so
supplying it is a citation rather than a gap.

Nothing is admitted here.  What remains for the Kähler instantiation of the atlas is the frame family
on *every* open of a chart together with its restriction coherence, which is the `hframe` hypothesis
of `ChartFrameAtlasSheaf`; this module only fixes what the resulting units are.
-/

noncomputable section

open scoped TensorProduct

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.KaehlerFrameLocalization
open KltDP.Geometry.ChartFrameAtlasSheaf

universe u

namespace KltDP.Geometry.ChartFrameAtlasJacobian

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable (k : Type u) [CommRing k] [∀ W : X.Opens, Algebra k Γ(X, W)]
variable (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i →
  Basis (Fin 2) Γ(X, W) (KaehlerDifferential k Γ(X, W)))
variable (A : Type u) [CommRing A] [Algebra k A]

/-- **The transition unit of a Kähler chart atlas is the image of the presentation Jacobian.** -/
theorem transitionUnit_eq_presentationJacobian (i j : ι) [Algebra A Γ(X, U i ⊓ U j)]
    (e : Γ(X, U i ⊓ U j) ⊗[A] KaehlerDifferential k A ≃ₗ[Γ(X, U i ⊓ U j)]
      KaehlerDifferential k Γ(X, U i ⊓ U j))
    (P P' : Algebra.SubmersivePresentation k A) (hP : P.dimension = 2) (hP' : P'.dimension = 2)
    (hi : frame i (U i ⊓ U j) inf_le_left =
      transportedFrame k A Γ(X, U i ⊓ U j) e P hP)
    (hj : frame j (U i ⊓ U j) inf_le_right =
      transportedFrame k A Γ(X, U i ⊓ U j) e P' hP') :
    transitionUnit U (fun W => KaehlerDifferential k Γ(X, W)) frame i j =
      Units.map (algebraMap A Γ(X, U i ⊓ U j)).toMonoidHom
        (presentationJacobian k A P P' hP hP') := by
  show frameChangeUnit (frame i (U i ⊓ U j) inf_le_left)
      (frame j (U i ⊓ U j) inf_le_right) = _
  rw [hi, hj]
  exact presentationJacobian_transport k A Γ(X, U i ⊓ U j) e P P' hP hP'

end KltDP.Geometry.ChartFrameAtlasJacobian
