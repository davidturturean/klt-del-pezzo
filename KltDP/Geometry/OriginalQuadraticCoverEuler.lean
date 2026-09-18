import KltDP.Geometry.SelectedOriginalCoverEulerConditional
import KltDP.Literature.Stacks.AffineMorphismCohomology

/-!
# Euler characteristic of the actual original quadratic cover

These direct consumers discharge the complete affine-cohomology input
using the reviewed full published Stacks theorem. The cover, original
line, original square-root isomorphism, and original branch are unchanged.
The selected-curve formula derives its Picard and canonical-degree
equations and has no cohomological or numerical hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance nativeQuadraticEulerSeparated : S.toScheme.IsSeparated := surfaceSeparated S

local instance nativeQuadraticEulerMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The same original square-root cover has the actual unit-plus-dual Euler value. -/
theorem originalQuadraticCover_eulerCharacteristic
    (L : InvertibleSheaf S.toScheme) (N : S.toScheme.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : S.toScheme.Opens))) :
    let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L N e b
    eulerCharacteristic (A.morphism ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit A.scheme.ringCatSheaf) =
      eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) +
      eulerCharacteristic S.structureMorphism (schemeDualSheaf L.obj) :=
  original_squareRoot_euler_split KltDP.Literature.Stacks.affine_morphism_cohomology_literal
    S L N e b

variable [IsAlgClosed k]

/-- RR computes the actual original cover's Euler value from the original half-line. -/
theorem originalQuadraticCover_eulerCharacteristic_riemannRoch
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (L : InvertibleSheaf S.toScheme) (N : S.toScheme.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : S.toScheme.Opens))) :
    let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L N e b
    (eulerCharacteristic (A.morphism ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit A.scheme.ringCatSheaf) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) +
        (S.intersectionPairing hregular (S.picardRepresentative L.toPic)
          (S.picardRepresentative L.toPic + K) : ℚ) / 2 :=
  original_squareRoot_euler_riemannRoch
    KltDP.Literature.Stacks.affine_morphism_cohomology_literal S hregular K eK L N e b

variable [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance nativeSelectedEulerSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

/-- The actual cover of the original disjoint rational minus-two selection
has Euler characteristic twice that of the base minus one quarter the original count. -/
theorem selectedOriginalCover_eulerCharacteristic
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hP1 : ∀ C ∈ N, ∃ η : C.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
    (eulerCharacteristic (A.morphism ≫ S.structureMorphism)
        (_root_.SheafOfModules.unit A.scheme.ringCatSheaf) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) - (N.card : ℚ) / 4 :=
  selected_original_cover_euler KltDP.Literature.Stacks.affine_morphism_cohomology_literal
    S N E hE L e hweil hdisj hP1 hself

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.selectedOriginalCover_eulerCharacteristic
#print axioms KltDP.Geometry.NormalProjectiveSurface.originalQuadraticCover_eulerCharacteristic
#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedOriginalCover_eulerCharacteristic
