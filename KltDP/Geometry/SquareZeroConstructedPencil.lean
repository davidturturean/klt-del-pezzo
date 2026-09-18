import KltDP.Geometry.SquareZeroPencilSurjective
import KltDP.Geometry.SquareZeroPencilClosedFibers

/-! The actual complete square-zero pencil and geometric connectedness
of every closed fiber, with all original map data constructed internally. -/

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

local instance constructedPencilIntegral : IsIntegral X.toScheme := X.integral
local instance constructedPencilTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include eK in
/-- The original nef divisor yields a complete surjective pencil whose
entire original closed fibers remain connected after every field extension. -/
theorem exists_completePencil_connected_closedFibers_of_nef_squareZero
    (hrational : Scheme.BirationalOver X.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    ∃ π : X.toScheme ⟶ projectiveSpace k 1,
      π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism ∧ IsProper π ∧
      GenericPointPreserving π ∧ IsDominant π ∧ Surjective π ∧
      Nonempty ((pullbackInvertibleSheaf π
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule X.toScheme F) ∧
      ∀ (x : projectiveSpace k 1) (hc : IsClosed ({x} : Set (projectiveSpace k 1))),
        ∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k)),
          ConnectedSpace (pullback
            (pullback.snd π (closedPointSection (projectiveSpaceToSpec k 1) x hc)) q :
              Scheme.{u}) := by
  obtain ⟨π, hπ, hp, hg, hd, hs, ⟨e⟩⟩ :=
    X.exists_surjective_completePencilMorphism_of_nef_squareZero hX K eK hrational F hF hFF hKF
  letI := hp
  letI := hg
  letI := hs
  refine ⟨π, hπ, hp, hg, hd, hs, ⟨e⟩, ?_⟩
  exact X.squareZero_pencil_closedFiber_geometrically_connected
    hX K eK hrational F hF hFF hKF π hπ e

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_completePencil_connected_closedFibers_of_nef_squareZero
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_completePencil_connected_closedFibers_of_nef_squareZero
