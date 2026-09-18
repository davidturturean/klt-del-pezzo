import KltDP.Geometry.SquareZeroFamilyEuler

/-! The arbitrary-base-change clause of the full proper-flat-family Euler
theorem applies to the original square-zero pencil, with its actual
pulled-back structure module and every actual residue-field fiber. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

local instance baseChangeEulerOverLocallyBijective (Y : Scheme.{u}) :
    ∀ U : Y.Opens,
      ((Opens.grothendieckTopology Y).over U).WEqualsLocallyBijective AddCommGrp.{u} :=
  CoherentQuasicoherent.schemeOverWEqualsLocallyBijective Y

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
local instance baseChangeEulerSourceIntegral : IsIntegral X.toScheme := X.integral
local instance baseChangeEulerTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- Every residue-field fiber after arbitrary original base change still
has Euler characteristic one, with its actual structure module. -/
theorem squareZero_baseChange_fiberEuler_eq_one
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
    (T : Scheme.{u}) (g : T ⟶ projectiveSpace k 1) (t : T) :
    fiberEuler (pullback.snd π g)
      (SheafOfModules.unit (pullback π g : Scheme.{u}).ringCatSheaf) t = 1 := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  letI : IsLocallyNoetherian (projectiveSpace k 1) :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec (projectiveSpaceToSpec k 1)
  letI : LocallyOfFinitePresentation π := NoetherianFinitePresentation.of_isProper π
  letI : (SheafOfModules.unit X.toScheme.ringCatSheaf).IsFinitePresentation :=
    NoetherianFinitePresentation.structureSheaf X.toScheme
  letI : Flat π := DominantRegularCurveFlat.flat_projectiveLine π
  have hbc := (Literature.Stacks.properFlat_fiberEuler_literal π
    (SheafOfModules.unit X.toScheme.ringCatSheaf)
    ((isFlatModuleOver_unit_iff π).mpr inferInstance)).2 T g t
  have hcoeff :
      fiberEuler (pullback.snd π g)
        ((schemeModulePullback (pullback.fst π g)).obj
          (SheafOfModules.unit X.toScheme.ringCatSheaf)) t =
      fiberEuler (pullback.snd π g)
        (SheafOfModules.unit (pullback π g : Scheme.{u}).ringCatSheaf) t :=
    eulerCharacteristic_eq_of_iso ((pullback.snd π g).fiberToSpecResidueField t)
      ((schemeModulePullback ((pullback.snd π g).fiberι t)).mapIso
        (schemeModulePullbackUnitIso (pullback.fst π g)))
  rw [← hcoeff, hbc]
  exact X.squareZero_fiberEuler_eq_one hX K eK F hFF hKF π hπ eF _

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_baseChange_fiberEuler_eq_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_baseChange_fiberEuler_eq_one
