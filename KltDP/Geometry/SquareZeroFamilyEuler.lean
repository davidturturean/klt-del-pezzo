import KltDP.Geometry.SquareZeroResidueFiberEuler
import KltDP.Geometry.NoetherianFinitePresentation
import KltDP.Geometry.DominantRegularCurveFlat
import KltDP.Geometry.DominantGenericPoint
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.AffineModuleFlatOver
import KltDP.Geometry.FiberEulerFunction
import KltDP.Literature.Stacks.ProperFlatFiberEuler
import Mathlib.Topology.LocallyConstant.Basic

/-! Euler characteristic one for every actual residue-field fiber of the
original square-zero pencil. The complete reviewed proper-flat-family
Euler theorem supplies local constancy; the original closed-fiber value,
flatness and both native finite-presentation inputs are proved. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

local instance familyEulerOverLocallyBijective (Y : Scheme.{u}) :
    ∀ U : Y.Opens,
      ((Opens.grothendieckTopology Y).over U).WEqualsLocallyBijective AddCommGrp.{u} :=
  CoherentQuasicoherent.schemeOverWEqualsLocallyBijective Y

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
local instance familyEulerSourceIntegral : IsIntegral X.toScheme := X.integral
local instance familyEulerTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- Every original residue-field fiber has Euler characteristic one. -/
theorem squareZero_fiberEuler_eq_one
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1) [IsProper π] [IsDominant π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (eF : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F)
    (y : projectiveSpace k 1) :
    fiberEuler π (SheafOfModules.unit X.toScheme.ringCatSheaf) y = 1 := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  letI : IsLocallyNoetherian (projectiveSpace k 1) :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec (projectiveSpaceToSpec k 1)
  letI : LocallyOfFinitePresentation π := NoetherianFinitePresentation.of_isProper π
  letI : (SheafOfModules.unit X.toScheme.ringCatSheaf).IsFinitePresentation :=
    NoetherianFinitePresentation.structureSheaf X.toScheme
  letI : GenericPointPreserving π := genericPointPreserving_of_isDominant π
  letI : Flat π := DominantRegularCurveFlat.flat_projectiveLine π
  have hloc := (Literature.Stacks.properFlat_fiberEuler_literal π
    (SheafOfModules.unit X.toScheme.ringCatSheaf)
    ((isFlatModuleOver_unit_iff π).mpr inferInstance)).1
  letI : JacobsonSpace (projectiveSpace k 1) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceToSpec k 1)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set (projectiveSpace k 1)).Nonempty)
    isOpen_univ.isLocallyClosed
  rw [hloc.apply_eq_of_preconnectedSpace y x, fiberEuler_unit]
  exact X.squareZero_closedResidueFiber_eulerCharacteristic_eq_one
    hX K eK F hFF hKF π hπ eF x hx

/-- In particular, the ORIGINAL generic fiber has Euler characteristic one. -/
theorem squareZero_genericFiber_eulerCharacteristic_eq_one
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1) [IsProper π] [IsDominant π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (eF : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F) :
    eulerCharacteristic (π.fiberToSpecResidueField (genericPoint (projectiveSpace k 1)))
      (SheafOfModules.unit (π.fiber (genericPoint (projectiveSpace k 1))).ringCatSheaf) = 1 := by
  rw [← fiberEuler_unit]
  exact X.squareZero_fiberEuler_eq_one hX K eK F hFF hKF π hπ eF _

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_genericFiber_eulerCharacteristic_eq_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_fiberEuler_eq_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_genericFiber_eulerCharacteristic_eq_one
