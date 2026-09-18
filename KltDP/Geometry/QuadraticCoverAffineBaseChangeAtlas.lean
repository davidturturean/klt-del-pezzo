import KltDP.Geometry.QuadraticCoverAtlasBaseChangeChart
import KltDP.Geometry.QuadraticCoverAppLE
import KltDP.Geometry.AffineOpenRefinement
import KltDP.Geometry.TransitionUnitRefinementCocycle
import KltDP.Geometry.RationalTreePicardCoordinateCocycle

/-!
# The literal affine branch atlas after an arbitrary scheme base change

Every affine subopen of an original inverse-image chart is used. Branch
coefficients are mapped by the original `f.appLE`; transition units are the
existing pulled and refined units. Their equations are proved by applying
the original structure-sheaf map to the original branch equations.
Only separatedness of the actual new base is needed for affine intersections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing

variable {X Y : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι) (f : Y ⟶ X)

/-- All affine subopens of the original inverse-image cover. -/
abbrev BaseChangeIndex := AffineOpenRefinement.Index Y (fun i => f ⁻¹ᵁ D.opens i)

abbrev baseChangeOpens : D.BaseChangeIndex f → Y.Opens :=
  AffineOpenRefinement.opens Y (fun i => f ⁻¹ᵁ D.opens i)

abbrev baseChangeOriginal : D.BaseChangeIndex f → ι :=
  AffineOpenRefinement.original Y (fun i => f ⁻¹ᵁ D.opens i)

theorem baseChangeSubordinate (i : D.BaseChangeIndex f) :
    D.baseChangeOpens f i ≤ f ⁻¹ᵁ D.opens (D.baseChangeOriginal f i) :=
  AffineOpenRefinement.subordinate Y (fun i => f ⁻¹ᵁ D.opens i) i

/-- Existing actual pulled transition units, restricted to the affine refinement. -/
def baseChangeUnits (i j : D.BaseChangeIndex f) :
    Γ(Y, D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)ˣ :=
  refinedUnits Y (fun i => f ⁻¹ᵁ D.opens i)
    (RationalTreePicard.pullbackUnits f D.opens D.units)
    (D.baseChangeOpens f) (D.baseChangeOriginal f) (D.baseChangeSubordinate f) i j

theorem baseChangePairSubordinate (i j : D.BaseChangeIndex f) :
    D.baseChangeOpens f i ⊓ D.baseChangeOpens f j ≤
      f ⁻¹ᵁ (D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j)) :=
  fun _ hx => ⟨D.baseChangeSubordinate f i hx.1, D.baseChangeSubordinate f j hx.2⟩

/-- The refined unit is exactly the original unit under the original section map. -/
theorem baseChangeUnits_val (i j : D.BaseChangeIndex f) :
    (D.baseChangeUnits f i j : Γ(Y, D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)) =
      f.appLE (D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j))
        (D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)
        (D.baseChangePairSubordinate f i j)
        (D.units (D.baseChangeOriginal f i) (D.baseChangeOriginal f j)) := by
  change res Y _ (res Y _ (f.app _
    (D.units (D.baseChangeOriginal f i) (D.baseChangeOriginal f j) :
      Γ(X, D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j))))) = _
  rw [res_res]
  rfl

theorem baseChangeUnits_isCocycle :
    IsCocycle Y (D.baseChangeOpens f) (D.baseChangeUnits f) :=
  refinedUnits_isCocycle Y (fun i => f ⁻¹ᵁ D.opens i)
    (RationalTreePicard.pullbackUnits f D.opens D.units)
    (D.baseChangeOpens f) (D.baseChangeOriginal f) (D.baseChangeSubordinate f)
    (RationalTreePicard.pullbackUnits_isCocycle f D.opens D.units D.cocycle)

/-- Literal original branch coefficients on the actual new affine charts. -/
def baseChangeSections (i : D.BaseChangeIndex f) : Γ(Y, D.baseChangeOpens f i) :=
  f.appLE (D.opens (D.baseChangeOriginal f i)) (D.baseChangeOpens f i)
    (D.baseChangeSubordinate f i) (D.sections (D.baseChangeOriginal f i))

/-- The new branch equations follow from the original branch equations. -/
theorem baseChangeSections_branch (i j : D.BaseChangeIndex f) :
    res Y inf_le_left (D.baseChangeSections f i) =
      (D.baseChangeUnits f i j : Γ(Y, D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)) ^ 2 *
        res Y inf_le_right (D.baseChangeSections f j) := by
  have h := congrArg
    (f.appLE (D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j))
      (D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)
      (D.baseChangePairSubordinate f i j)).hom
    (D.branch (D.baseChangeOriginal f i) (D.baseChangeOriginal f j))
  rw [map_mul, map_pow] at h
  simpa only [baseChangeSections, baseChangeUnits_val,
    QuadraticCoverAppLE.res_appLE, QuadraticCoverAppLE.appLE_res] using h

/-- The base-changed quadratic atlas is constructed from the original atlas and morphism. -/
def baseChangeAtlas [Y.IsSeparated] : QuadraticCoverAtlas.Data Y (D.BaseChangeIndex f) where
  opens := D.baseChangeOpens f
  affine := AffineOpenRefinement.affine Y (fun i => f ⁻¹ᵁ D.opens i)
  pair_affine := AffineOpenRefinement.pair_affine Y (fun i => f ⁻¹ᵁ D.opens i)
  triple_affine := AffineOpenRefinement.triple_affine Y (fun i => f ⁻¹ᵁ D.opens i)
  covers := AffineOpenRefinement.covers Y (fun i => f ⁻¹ᵁ D.opens i)
    (f.preimage_iSup_eq_top D.covers)
  units := D.baseChangeUnits f
  cocycle := D.baseChangeUnits_isCocycle f
  sections := D.baseChangeSections f
  branch := D.baseChangeSections_branch f

#print axioms baseChangeSections_branch
#print axioms baseChangeAtlas

end KltDP.Geometry.QuadraticCoverAtlas.Data
