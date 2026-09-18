import KltDP.Geometry.SquareZeroMemberConnected
import KltDP.Geometry.ProjectiveLineClosedPointCartier
import KltDP.Geometry.CartierPullbackClosedFiber
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.DominantCartierRegularPullback
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Every original closed-point fiber of the square-zero pencil is
geometrically connected. The original Cartier point, its signed and
regular pullbacks, and the actual scheme fiber are compared explicitly;
no reduced-fiber or connectedness premise is inserted. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)
  (hrational : Scheme.BirationalOver X.structureMorphism
    (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

local instance pencilClosedFiberIntegral : IsIntegral X.toScheme := X.integral
local instance pencilClosedFiberTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include eK hrational in
/-- Connectedness holds after every original field extension of each
original closed-point fiber, including the complete fiber scheme. -/
theorem squareZero_pencil_closedFiber_geometrically_connected
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1)
    [IsProper π] [GenericPointPreserving π] [Surjective π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (eF : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F)
    (x : projectiveSpace k 1) (hclosed : IsClosed ({x} : Set (projectiveSpace k 1))) :
    ∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k)),
      ConnectedSpace (pullback
        (pullback.snd π (closedPointSection (projectiveSpaceToSpec k 1) x hclosed)) q :
          Scheme.{u}) := by
  obtain ⟨D, hD, hci, hi, hI, ⟨eD⟩⟩ :=
    ProjectiveLineClosedPointCartier.exists_cartierDivisor k x hclosed
  let i := closedPointSection (projectiveSpaceToSpec k 1) x hclosed
  letI : IsClosedImmersion i := hci
  let E := pullbackDivisor π D hD
  let hE : HasRegularCartierEquations X.toScheme E :=
    pullbackDivisor_hasRegularEquations π D hD
  have hp : DominantCartierPullback.pullbackHom π D = E :=
    DominantCartierPullback.pullbackHom_eq_pullbackDivisor π D hD
  let e : cartierDivisorModule X.toScheme E ≅ cartierDivisorModule X.toScheme F :=
    eqToIso (congrArg (cartierDivisorModule X.toScheme) hp.symm) ≪≫
      (DominantCartierPullback.modulePullbackIso π D).symm ≪≫
      (schemeModulePullback π).mapIso eD ≪≫ eF
  let θ : effectiveCartierScheme X.toScheme E hE ≅ pullback π i :=
    CartierPullbackClosedFiber.iso π D hD i hI.symm
  have hθfst : θ.hom ≫ pullback.fst π i = effectiveCartierInclusion X.toScheme E hE :=
    CartierPullbackClosedFiber.iso_hom_fst π D hD i hI.symm
  have hf : pullback.fst π i ≫ X.structureMorphism = pullback.snd π i := by
    rw [← hπ, pullback.condition_assoc, hi, Category.comp_id]
  have hθ : θ.hom ≫ pullback.snd π i =
      effectiveCartierInclusion X.toScheme E hE ≫ X.structureMorphism := by
    rw [← hf, ← Category.assoc, hθfst]
  letI : Surjective (pullback.snd π i) := MorphismProperty.pullback_snd _ _ inferInstance
  let y : (pullback π i : Scheme.{u}) :=
    Classical.choose ((pullback.snd π i).surjective (IsLocalRing.closedPoint k))
  letI : Nonempty (effectiveCartierScheme X.toScheme E hE) := ⟨θ.inv.base y⟩
  intro l inst q
  letI : ConnectedSpace (pullback
      (effectiveCartierInclusion X.toScheme E hE ≫ X.structureMorphism) q : Scheme.{u}) :=
    X.squareZero_member_geometrically_connected hX K eK hrational F hF hFF hKF E hE e l q
  let η := pullback.map
    (effectiveCartierInclusion X.toScheme E hE ≫ X.structureMorphism) q
    (pullback.snd π i) q θ.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact hθ.symm) (by simp only [Category.comp_id, Category.id_comp])
  letI : IsIso η := by dsimp [η]; infer_instance
  exact η.surjective.connectedSpace η.base.hom.continuous

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_pencil_closedFiber_geometrically_connected
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_pencil_closedFiber_geometrically_connected
