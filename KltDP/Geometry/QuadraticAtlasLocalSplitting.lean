import KltDP.Geometry.QuadraticRootChartSplitting
import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# Actual split maps throughout the original quadratic atlas

Roots with the proved original coefficient and overlap equations give
splittings on every original subchart. The forward maps commute with
the literal localMap, including both coefficient restriction and the
original unit rescaling. These are the actual local maps used in descent.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.QuadraticAtlasLocalSplitting

open TransitionUnitGluing QuadraticCover QuadraticCoverAtlas QuadraticTransitionCocycle

variable {X : Scheme.{u}} {ι : Type u} (D : Data X ι)
    (a : ∀ i, Γ(X, D.opens i)ˣ)
    (ha : ∀ i, (a i : Γ(X, D.opens i)) ^ 2 = D.sections i)
    (hr : ∀ i j, res X (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      (a i : Γ(X, D.opens i)) = (D.units i j : Γ(X, D.opens i ⊓ D.opens j)) *
        res X inf_le_right (a j : Γ(X, D.opens j)))

/-- The original unit root restricted by the original structure-sheaf map. -/
def rootOn {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) : Γ(X, W)ˣ :=
  Units.map (res X hi).toMonoidHom (a i)

include ha in
theorem rootOn_sq {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) :
    (rootOn D a hi : Γ(X, W)) ^ 2 = res X hi (D.sections i) := by
  change (res X hi (a i : Γ(X, D.opens i))) ^ 2 = _
  rw [← map_pow, ha i]

include hr in
/-- The actual roots obey the original restricted transition on every subchart. -/
theorem rootOn_relation {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V) :
    res X hWV (rootOn D a hi : Γ(X, V)) =
      (restrictedUnit X D.opens D.units (hWV.trans hi) hj : Γ(X, W)) *
        (rootOn D a hj : Γ(X, W)) := by
  have h := congrArg (res X (le_inf (hWV.trans hi) hj)) (hr i j)
  change res X hWV (res X hi (a i : Γ(X, D.opens i))) =
    res X (le_inf (hWV.trans hi) hj) (D.units i j : Γ(X, D.opens i ⊓ D.opens j)) *
      res X hj (a j : Γ(X, D.opens j))
  simpa only [map_mul, res_res] using h

/-- The splitting is an isomorphism of the original actual subchart. -/
def splitOn {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) (h2 : IsUnit (2 : Γ(X, W))) :
    D.frameChart hi ≅ Spec Γ(X, W) ⨿ Spec Γ(X, W) :=
  QuadraticRootChartSplitting.splitIso (res X hi (D.sections i))
    (rootOn D a hi) (rootOn_sq D a ha hi) h2

include hr in
/-- The actual forward splitting commutes with the original restriction and rescaling. -/
@[reassoc]
theorem map_splitOn_hom {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsUnit (2 : Γ(X, V))) (hW : IsUnit (2 : Γ(X, W))) :
    D.map hi hj hWV ≫ (splitOn D a ha hi hV).hom =
      (splitOn D a ha hj hW).hom ≫
        coprod.map (Spec.map (CommRingCat.ofHom (res X hWV)))
          (Spec.map (CommRingCat.ofHom (res X hWV))) :=
  QuadraticRootChartSplitting.hom_mappedRescale (res X hWV)
    (res X hi (D.sections i)) (res X hj (D.sections j))
    (rootOn D a hi) (rootOn D a hj)
    (restrictedUnit X D.opens D.units (hWV.trans hi) hj)
    (rootOn_sq D a ha hi) (rootOn_sq D a ha hj)
    (by simpa only [res_res] using
      branchCondition_of_le X D.opens D.units D.sections D.branch (hWV.trans hi) hj)
    (rootOn_relation D a hr hi hj hWV) hV hW

include hr in
/-- The actual inverse splitting commutes with those same original maps. -/
@[reassoc]
theorem splitOn_inv_map {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsUnit (2 : Γ(X, V))) (hW : IsUnit (2 : Γ(X, W))) :
    (splitOn D a ha hj hW).inv ≫ D.map hi hj hWV =
      coprod.map (Spec.map (CommRingCat.ofHom (res X hWV)))
        (Spec.map (CommRingCat.ofHom (res X hWV))) ≫ (splitOn D a ha hi hV).inv :=
  QuadraticRootChartSplitting.inv_mappedRescale (res X hWV)
    (res X hi (D.sections i)) (res X hj (D.sections j))
    (rootOn D a hi) (rootOn D a hj)
    (restrictedUnit X D.opens D.units (hWV.trans hi) hj)
    (rootOn_sq D a ha hi) (rootOn_sq D a ha hj)
    (by simpa only [res_res] using
      branchCondition_of_le X D.opens D.units D.sections D.branch (hWV.trans hi) hj)
    (rootOn_relation D a hr hi hj hWV) hV hW

/-- The forward map to two copies of the original base uses the original affine inclusion. -/
def forwardOn {i : ι} {W : X.Opens} (hi : W ≤ D.opens i)
    (hW : IsAffineOpen W) (h2 : IsUnit (2 : Γ(X, W))) : D.frameChart hi ⟶ X ⨿ X :=
  (splitOn D a ha hi h2).hom ≫ coprod.map hW.fromSpec hW.fromSpec

include hr in
/-- The actual local forward maps already agree before gluing. -/
@[reassoc]
theorem map_forwardOn {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h2V : IsUnit (2 : Γ(X, V))) (h2W : IsUnit (2 : Γ(X, W))) :
    D.map hi hj hWV ≫ forwardOn D a ha hi hV h2V =
      forwardOn D a ha hj hW h2W := by
  rw [forwardOn, ← Category.assoc, map_splitOn_hom D a ha hr]
  rw [Category.assoc, coprod.map_map]
  have he : Spec.map (CommRingCat.ofHom (res X hWV)) ≫ hV.fromSpec = hW.fromSpec :=
    hV.map_fromSpec hW (homOfLE hWV).op
  rw [he]
  rfl

end KltDP.Geometry.QuadraticAtlasLocalSplitting

#print axioms KltDP.Geometry.QuadraticAtlasLocalSplitting.map_forwardOn
