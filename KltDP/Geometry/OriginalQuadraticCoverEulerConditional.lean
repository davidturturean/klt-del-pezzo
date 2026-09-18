import KltDP.Geometry.InvertibleQuadraticPushforwardSplitting
import KltDP.Geometry.OriginalLineDualEulerCorrection
import KltDP.Geometry.AffineSurfaceEulerSplitConditional

/-!
# Euler characteristic of the same original square-root cover

The actual splitting is constructed from the original line, square-root
isomorphism, and section. The complete published affine-cohomology input
remains explicit until its separate source admission. No Euler identity,
pushforward splitting, chart compatibility, or RR correction is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance originalEulerSurfaceSeparated : S.toScheme.IsSeparated := surfaceSeparated S

local instance originalEulerModulesMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

local instance originalEulerSectionsComm :
    ∀ U, IsMulCommutative (S.toScheme.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.toScheme.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

include hAffine

/-- The original square-root cover has exactly the original unit-plus-dual Euler value. -/
theorem original_squareRoot_euler_split (L : InvertibleSheaf S.toScheme)
    (N : S.toScheme.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (b : N.val.obj (op (⊤ : S.toScheme.Opens))) :
    let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L N e b
    eulerCharacteristic (A.morphism ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit A.scheme.ringCatSheaf) =
      eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) +
      eulerCharacteristic S.structureMorphism (schemeDualSheaf L.obj) := by
  let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L N e b
  letI : IsFinite A.morphism := A.morphism_isFinite
  exact eulerCharacteristic_structureSheaf_of_pushforward_unit_dual hAffine S A.morphism L
    (InvertibleQuadraticAtlas.squareRootPushforwardDualIso S.toScheme L N e b)

variable [IsAlgClosed k]
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  (K : CartierDivisor S.toScheme)
  (eK : cartierDivisorModule S.toScheme K ≅
    relativeDifferentialExterior S.structureMorphism 2)

include eK

/-- The same original cover has the exact manuscript RR correction, with
the Cartier representative constructed from its original half-line. -/
theorem original_squareRoot_euler_riemannRoch (L : InvertibleSheaf S.toScheme)
    (N : S.toScheme.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (b : N.val.obj (op (⊤ : S.toScheme.Opens))) :
    let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L N e b
    (eulerCharacteristic (A.morphism ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit A.scheme.ringCatSheaf) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) +
        (S.intersectionPairing hregular (S.picardRepresentative L.toPic)
          (S.picardRepresentative L.toPic + K) : ℚ) / 2 := by
  dsimp only
  rw [original_squareRoot_euler_split hAffine S L N e b, Int.cast_add]
  exact S.unit_add_dual_euler hregular K eK L

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.original_squareRoot_euler_riemannRoch
#print axioms KltDP.Geometry.NormalProjectiveSurface.original_squareRoot_euler_riemannRoch
