import KltDP.Geometry.SquareZeroCartierMemberEuler
import KltDP.Geometry.ProjectiveLineClosedPointCartier
import KltDP.Geometry.CartierPullbackClosedFiber
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.DominantCartierRegularPullback

/-! The Euler characteristic of the complete ORIGINAL closed-point fiber
of a square-zero pencil is one. The Cartier pullback ideal equals the actual
fiber kernel, including nilpotents. Neither a replaced reduced curve nor a
fiber Euler value is assumed. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance pencilEulerSourceIntegral : IsIntegral X.toScheme := X.integral
local instance pencilEulerTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include eK in
/-- Every actual closed-point fiber has Euler characteristic one over the
original field. No rationality, surface Euler value or connectedness is supplied. -/
theorem squareZero_pencil_closedFiber_eulerCharacteristic_eq_one
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1) [GenericPointPreserving π] [QuasiCompact π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (eF : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F)
    (x : projectiveSpace k 1) (hclosed : IsClosed ({x} : Set (projectiveSpace k 1))) :
    eulerCharacteristic
      (pullback.snd π (closedPointSection (projectiveSpaceToSpec k 1) x hclosed))
      (_root_.SheafOfModules.unit
        (pullback π (closedPointSection (projectiveSpaceToSpec k 1) x hclosed)).ringCatSheaf) = 1 := by
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
  have hker : (pullback.fst π i).ker =
      effectiveCartierIdealDataOfRegularEquations X.toScheme E hE :=
    (CartierPullbackClosedFiber.ideal_eq_fiber_ker π D hD i hI.symm).symm
  have hf : pullback.fst π i ≫ X.structureMorphism = pullback.snd π i := by
    rw [← hπ, pullback.condition_assoc, hi, Category.comp_id]
  letI : IsClosedImmersion (pullback.fst π i) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have h := X.squareZero_member_eulerCharacteristic_eq_one hX K eK F hFF hKF
    E hE e (pullback.fst π i) hker
  rw [hf] at h
  exact h

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_pencil_closedFiber_eulerCharacteristic_eq_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_pencil_closedFiber_eulerCharacteristic_eq_one
