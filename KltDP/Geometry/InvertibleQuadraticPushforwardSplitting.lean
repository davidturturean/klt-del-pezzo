import KltDP.Geometry.QuadraticPushforwardSplitting
import KltDP.Geometry.AffineOpenNonemptyBasis
import KltDP.Geometry.InvertibleQuadraticAtlas
import KltDP.Geometry.TransitionUnitRefinement

/-!
# The actual cover of a square-root line has pushforward O plus the original dual

All charts, transitions, scalar actions, and the inverse-image sheaf
come from the original square section. The basis and positive coordinate
identification are constructed here, so the final isomorphism has no
supplied splitting or local atlas compatibility hypotheses.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleQuadraticAtlas

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

local instance pushforwardLineScalarComm :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance pushforwardLineModulesMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance pushforwardLineModulesBinaryBiproducts : HasBinaryBiproducts X.Modules :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Original recovery followed by actual affine refinement preserves the original line. -/
def squareSectionLineCoordinatesIso [X.IsSeparated] (L : InvertibleSheaf X)
    (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens))) :
    L.obj ≅ moduleSheaf X (fromSquareSection X L b).opens
      (fromSquareSection X L b).units :=
  invertibleSheafRecoveryIso X L ≪≫
    refinementIso X L.localTrivializations.X (invertibleSheafUnits X L)
      (AffineOpenRefinement.opens X L.localTrivializations.X)
      (AffineOpenRefinement.original X L.localTrivializations.X)
      (AffineOpenRefinement.subordinate X L.localTrivializations.X)
      (invertibleSheafUnits_isCocycle X L)
      (AffineOpenRefinement.covers X L.localTrivializations.X (invertibleSheafUnits_cover X L))

/-- The pushforward from the same constructed square-section cover splits
as the original structure sheaf and the original line's actual dual. -/
def squareSectionPushforwardDualIso [X.IsSeparated] (L : InvertibleSheaf X)
    (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens))) :
    (fromSquareSection X L b).pushforwardUnit ≅
      _root_.SheafOfModules.unit X.ringCatSheaf ⊞
        KltDP.SheafOfModules.dual X.ringCatSheaf L.obj := by
  let D := fromSquareSection X L b
  let a : AffineOpenRefinement.NonemptyIndex X L.localTrivializations.X →
      AffineOpenRefinement.Index X L.localTrivializations.X := Subtype.val
  have hB : TopologicalSpace.Opens.IsBasis (Set.range (fun i => D.opens (a i))) :=
    AffineOpenRefinement.nonempty_isBasis X L.localTrivializations.X
      (invertibleSheafUnits_cover X L)
  letI : ∀ i, Nontrivial Γ(X, D.opens (a i)) := fun i =>
    AffineOpenRefinement.nonemptyIndex_sectionRing_nontrivial X L.localTrivializations.X i
  exact D.coefficientSplittingIso a hB ≪≫ biprod.mapIso (Iso.refl _)
    (inverseCoordinatesDualIso X D.opens D.units D.cocycle D.covers L
      (squareSectionLineCoordinatesIso X L b))

/-- An arbitrary original square-root isomorphism gives the same exact splitting. -/
def squareRootPushforwardDualIso [X.IsSeparated] (L : InvertibleSheaf X) (N : X.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : X.Opens))) :
    (fromSquareRoot X L N e b).pushforwardUnit ≅
      _root_.SheafOfModules.unit X.ringCatSheaf ⊞
        KltDP.SheafOfModules.dual X.ringCatSheaf L.obj :=
  squareSectionPushforwardDualIso X L (e.inv.val.app (op ⊤) b)

end KltDP.Geometry.InvertibleQuadraticAtlas

#check @KltDP.Geometry.InvertibleQuadraticAtlas.squareRootPushforwardDualIso
#print axioms KltDP.Geometry.InvertibleQuadraticAtlas.squareRootPushforwardDualIso
