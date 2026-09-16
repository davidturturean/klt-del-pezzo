import KltDP.Geometry.AffineOpenRefinement
import KltDP.Geometry.TransitionUnitRecovery
import KltDP.Geometry.TransitionUnitTensor
import KltDP.Geometry.TransitionUnitRefinementCocycle
import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# A quadratic scheme cover from an actual square line bundle and section

The original invertible sheaf is recovered from its actual transition units.
Tensoring that recovery and applying the existing tensor multiplication
isomorphism transports an arbitrary section of its tensor square to actual
matching coordinates for the squared units. Restriction to all affine
subopens derives the branch equations and the affine atlas. Separatedness
of the original scheme supplies intersection affineness. The existing
scheme gluing then constructs a finite flat morphism over that scheme.

The square-root version starts with an actual isomorphism L ⊗ L ≅ N and
an actual section of N, and uses its inverse to obtain the square section.
No affine triviality of the original charts, branch matching equation,
transition cocycle, glued cover, preimage identification, finiteness or
flatness is an input. Branch smoothness, integrality, identification with
a specified divisor, and the manuscript's numerical surface claims are
separate obligations.

Reuse: the original sectionwise multiplication and actual sheaf tensor
comparison are in TransitionUnitTensor, and actual arbitrary-sheaf
recovery is in TransitionUnitRecovery. Pinned and newer official Mathlib
`CategoryTheory/Monoidal/Category.lean` provide the same `tensorIso`
construction; no new tensor or quasi-coherent-sheaf foundation is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleQuadraticAtlas

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

local instance schemeModulesMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

section MatchingCoordinates

variable {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

/-- Original global matching coordinates, restricted to a subordinate affine open. -/
def refinedCoefficient (q : sections X U (productUnits X U g g) ⊤)
    (i : AffineOpenRefinement.Index X U) : Γ(X, AffineOpenRefinement.opens X U i) :=
  res X (le_inf le_top (AffineOpenRefinement.subordinate X U i))
    (q.val (AffineOpenRefinement.original X U i))

/-- The square branch equation follows from the original matching section. -/
theorem refinedCoefficient_branch
    (q : sections X U (productUnits X U g g) ⊤)
    (i j : AffineOpenRefinement.Index X U) :
    res X (inf_le_left : AffineOpenRefinement.opens X U i ⊓
        AffineOpenRefinement.opens X U j ≤ AffineOpenRefinement.opens X U i)
        (refinedCoefficient X U g q i) =
      (refinedUnits X U g (AffineOpenRefinement.opens X U)
          (AffineOpenRefinement.original X U) (AffineOpenRefinement.subordinate X U)
          i j : Γ(X, AffineOpenRefinement.opens X U i ⊓
            AffineOpenRefinement.opens X U j)) ^ 2 *
        res X (inf_le_right : AffineOpenRefinement.opens X U i ⊓
          AffineOpenRefinement.opens X U j ≤ AffineOpenRefinement.opens X U j)
          (refinedCoefficient X U g q j) := by
  have hW : AffineOpenRefinement.opens X U i ⊓ AffineOpenRefinement.opens X U j ≤
      ((⊤ : X.Opens) ⊓ U (AffineOpenRefinement.original X U i)) ⊓
        U (AffineOpenRefinement.original X U j) :=
    le_inf
      (le_inf le_top (inf_le_left.trans (AffineOpenRefinement.subordinate X U i)))
      (inf_le_right.trans (AffineOpenRefinement.subordinate X U j))
  have h := congrArg (res X hW)
    (q.property (AffineOpenRefinement.original X U i)
      (AffineOpenRefinement.original X U j))
  simpa only [refinedCoefficient, refinedUnits_val, productUnits_val, pow_two,
    map_mul, res_res] using h

/-- The actual affine quadratic atlas extracted from one squared matching section. -/
def fromMatchingSquare [X.IsSeparated] (hg : IsCocycle X U g)
    (hU : (⨆ i, U i) = ⊤) (q : sections X U (productUnits X U g g) ⊤) :
    QuadraticCoverAtlas.Data X (AffineOpenRefinement.Index X U) where
  opens := AffineOpenRefinement.opens X U
  affine := AffineOpenRefinement.affine X U
  pair_affine := AffineOpenRefinement.pair_affine X U
  triple_affine := AffineOpenRefinement.triple_affine X U
  covers := AffineOpenRefinement.covers X U hU
  units := refinedUnits X U g (AffineOpenRefinement.opens X U)
    (AffineOpenRefinement.original X U) (AffineOpenRefinement.subordinate X U)
  cocycle := refinedUnits_isCocycle X U g (AffineOpenRefinement.opens X U)
    (AffineOpenRefinement.original X U) (AffineOpenRefinement.subordinate X U) hg
  sections := refinedCoefficient X U g q
  branch := refinedCoefficient_branch X U g q

end MatchingCoordinates

/-- The actual tensor square has the squared extracted transition units. -/
def squareCoordinatesIso (L : InvertibleSheaf X) :
    L.obj ⊗ L.obj ≅ moduleSheaf X L.localTrivializations.X
      (productUnits X L.localTrivializations.X
        (invertibleSheafUnits X L) (invertibleSheafUnits X L)) :=
  CategoryTheory.MonoidalCategory.tensorIso
      (invertibleSheafRecoveryIso X L) (invertibleSheafRecoveryIso X L) ≪≫
    TransitionUnitGluing.tensorIso X L.localTrivializations.X
      (invertibleSheafUnits X L) (invertibleSheafUnits X L)
      (invertibleSheafUnits_isCocycle X L) (invertibleSheafUnits_isCocycle X L)
      (invertibleSheafUnits_cover X L)

/-- Coordinates of the original tensor-square section in the actual squared cocycle sheaf. -/
def squareCoordinates (L : InvertibleSheaf X)
    (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens))) :
    sections X L.localTrivializations.X
      (productUnits X L.localTrivializations.X
        (invertibleSheafUnits X L) (invertibleSheafUnits X L)) ⊤ :=
  (squareCoordinatesIso X L).hom.val.app (op ⊤) b

/-- An arbitrary tensor-square section determines its actual affine quadratic atlas. -/
def fromSquareSection [X.IsSeparated] (L : InvertibleSheaf X)
    (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens))) :
    QuadraticCoverAtlas.Data X (AffineOpenRefinement.Index X L.localTrivializations.X) :=
  fromMatchingSquare X L.localTrivializations.X (invertibleSheafUnits X L)
    (invertibleSheafUnits_isCocycle X L) (invertibleSheafUnits_cover X L)
    (squareCoordinates X L b)

/-- The local coefficients are restrictions of the original section's actual tensor coordinates. -/
@[simp]
theorem fromSquareSection_sections [X.IsSeparated] (L : InvertibleSheaf X)
    (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens)))
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    (fromSquareSection X L b).sections i =
      res X (le_inf le_top (AffineOpenRefinement.subordinate X L.localTrivializations.X i))
        (((squareCoordinatesIso X L).hom.val.app (op ⊤) b).val
          (AffineOpenRefinement.original X L.localTrivializations.X i)) := rfl

/-- Scheme gluing constructs the finite flat morphism from the original square section. -/
theorem fromSquareSection_finite_flat [X.IsSeparated] (L : InvertibleSheaf X)
    (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens))) :
    IsFinite (fromSquareSection X L b).morphism ∧
      AlgebraicGeometry.Flat (fromSquareSection X L b).morphism :=
  ⟨(fromSquareSection X L b).morphism_isFinite, (fromSquareSection X L b).morphism_flat⟩

/-- An original square-root isomorphism and original section produce the atlas, without local data. -/
def fromSquareRoot [X.IsSeparated] (L : InvertibleSheaf X) (N : X.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : X.Opens))) :
    QuadraticCoverAtlas.Data X (AffineOpenRefinement.Index X L.localTrivializations.X) :=
  fromSquareSection X L (e.inv.val.app (op ⊤) b)

/-- The cover constructed from an actual square-root line bundle and section is finite and flat. -/
theorem fromSquareRoot_finite_flat [X.IsSeparated] (L : InvertibleSheaf X) (N : X.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : X.Opens))) :
    IsFinite (fromSquareRoot X L N e b).morphism ∧
      AlgebraicGeometry.Flat (fromSquareRoot X L N e b).morphism :=
  fromSquareSection_finite_flat X L (e.inv.val.app (op ⊤) b)

end KltDP.Geometry.InvertibleQuadraticAtlas
