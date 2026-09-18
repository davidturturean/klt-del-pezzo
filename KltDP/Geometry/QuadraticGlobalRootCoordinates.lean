import KltDP.Geometry.QuadraticTensorSectionCoordinates

/-!
# Coherent unit roots in the original quadratic atlas

A global frame and an actual global unit determine a section of the
original line bundle. Its affine coordinates are units, their squares
are the literal coefficients of the original quadratic atlas, and their
overlap equations use exactly that atlas's original transition units.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.QuadraticGlobalRootCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open TransitionUnitGluing TransitionUnitExtraction InvertibleQuadraticAtlas
open SchemeModuleTensorSections QuadraticTensorSectionCoordinates

variable (X : Scheme.{u}) (L : InvertibleSheaf X)
    (t : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (b : Γ(X, ⊤)ˣ)

/-- The original global section with coefficient the original unit. -/
def rootSection : L.obj.val.obj (op (⊤ : X.Opens)) :=
  t.inv.val.app (op ⊤) (b : Γ(X, ⊤))

/-- The original global frame evaluated on any actual open. -/
def globalFrameEquiv (W : X.Opens) :
    L.obj.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op W)).mapIso t).toLinearEquiv

/-- A unit in each original affine chart, constructed from the actual two frames. -/
def rootUnit (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i)ˣ :=
  KltDP.Module.transitionUnit
      (globalFrameEquiv X L t (AffineOpenRefinement.opens X L.localTrivializations.X i))
      (chartEquiv X L.obj L.localTrivializations
        (AffineOpenRefinement.original X L.localTrivializations.X i)
        (AffineOpenRefinement.subordinate X L.localTrivializations.X i)) *
    Units.map (res X (show AffineOpenRefinement.opens X L.localTrivializations.X i ≤ ⊤
      from le_top)).toMonoidHom b

private theorem moduleMap_comp (M : X.Modules) {V W Z : X.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) (r : M.val.obj (op Z)) :
    M.val.map (homOfLE hVW).op (M.val.map (homOfLE hWZ).op r) =
      M.val.map (homOfLE (hVW.trans hWZ)).op r :=
  (CategoryTheory.congr_fun
    (M.val.presheaf.map_comp (homOfLE hWZ).op (homOfLE hVW).op) r).symm

/-- The unit is the literal local coordinate of the original global section. -/
theorem rootUnit_val (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    (rootUnit X L t b i : Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i)) =
      chartEquiv X L.obj L.localTrivializations
        (AffineOpenRefinement.original X L.localTrivializations.X i)
        (AffineOpenRefinement.subordinate X L.localTrivializations.X i)
        (L.obj.val.map (homOfLE (show
          AffineOpenRefinement.opens X L.localTrivializations.X i ≤ ⊤ from le_top)).op
          (rootSection X L t b)) := by
  let V := AffineOpenRefinement.opens X L.localTrivializations.X i
  let c := chartEquiv X L.obj L.localTrivializations
    (AffineOpenRefinement.original X L.localTrivializations.X i)
    (AffineOpenRefinement.subordinate X L.localTrivializations.X i)
  let z : Γ(X, V) := res X (show V ≤ ⊤ from le_top) (b : Γ(X, ⊤))
  have h := KltDP.Module.transitionUnit_mul_apply (globalFrameEquiv X L t V) c
    ((globalFrameEquiv X L t V).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  have hn := _root_.PresheafOfModules.naturality_apply t.inv.val
    (homOfLE (show V ≤ ⊤ from le_top)).op (b : Γ(X, ⊤))
  exact h.trans (congrArg c hn)

/-- Eliminate recovery and restriction while the module and atlas are abstract. -/
theorem recovery_restrict_coordinate (M : X.Modules)
    (T : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (r : M.val.obj (op (⊤ : X.Opens))) (i : T.I) (V : X.Opens) (hV : V ≤ T.X i) :
    res X (le_inf le_top hV) (((recoveryIso X M T).hom.val.app (op ⊤) r).val i) =
      chartEquiv X M T i hV (M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op r) := by
  change res X (le_inf le_top hV)
    (chartEquiv X M T i inf_le_right (M.val.map (homOfLE inf_le_left).op r)) = _
  exact (chartEquiv_restrict X M T i (le_inf le_top hV) inf_le_right
    (M.val.map (homOfLE inf_le_left).op r)).symm.trans
      (congrArg (chartEquiv X M T i hV)
        (moduleMap_comp X M (le_inf le_top hV) inf_le_left r))

/-- Refined recovery coordinates are the actual original chart coordinates. -/
theorem refinedCoordinate_eq_chart (r : L.obj.val.obj (op (⊤ : X.Opens)))
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    res X (le_inf le_top (AffineOpenRefinement.subordinate X L.localTrivializations.X i))
      (((invertibleSheafRecoveryIso X L).hom.val.app (op ⊤) r).val
        (AffineOpenRefinement.original X L.localTrivializations.X i)) =
      chartEquiv X L.obj L.localTrivializations
        (AffineOpenRefinement.original X L.localTrivializations.X i)
        (AffineOpenRefinement.subordinate X L.localTrivializations.X i)
        (L.obj.val.map (homOfLE (show
          AffineOpenRefinement.opens X L.localTrivializations.X i ≤ ⊤ from le_top)).op r) := by
  exact recovery_restrict_coordinate X L.obj L.localTrivializations r
    (AffineOpenRefinement.original X L.localTrivializations.X i)
    (AffineOpenRefinement.opens X L.localTrivializations.X i)
    (AffineOpenRefinement.subordinate X L.localTrivializations.X i)

/-- The actual unit is also the original restricted matching coordinate. -/
theorem rootUnit_val_coordinate
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    (rootUnit X L t b i : Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i)) =
      res X (le_inf le_top (AffineOpenRefinement.subordinate X L.localTrivializations.X i))
        (((invertibleSheafRecoveryIso X L).hom.val.app (op ⊤)
          (rootSection X L t b)).val
            (AffineOpenRefinement.original X L.localTrivializations.X i)) :=
  (rootUnit_val X L t b i).trans
    (refinedCoordinate_eq_chart X L (rootSection X L t b) i).symm

/-- Squaring those actual units gives the literal quadratic branch coefficients. -/
theorem rootUnit_sq [X.IsSeparated]
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    (rootUnit X L t b i : Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i)) ^ 2 =
      (fromSquareSection X L
        (tensorSection L.obj L.obj ⊤ (rootSection X L t b) (rootSection X L t b))).sections i := by
  change _ = refinedCoefficient X L.localTrivializations.X (invertibleSheafUnits X L)
    (squareCoordinates X L (tensorSection L.obj L.obj ⊤
      (rootSection X L t b) (rootSection X L t b))) i
  rw [squareCoordinates_tensorSection]
  simp only [refinedCoefficient, sectionMul_val, map_mul, ← pow_two, map_pow]
  exact congrArg (fun z => z ^ 2) (rootUnit_val_coordinate X L t b i)

/-- Actual refined matching coordinates satisfy the original refined-unit equation. -/
theorem refined_roots_overlap {I J : Type u} (U : J → X.Opens)
    (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (q : sections X U g ⊤)
    (V : I → X.Opens) (σ : I → J) (hσ : ∀ i, V i ≤ U (σ i))
    (a : ∀ i, Γ(X, V i)ˣ)
    (ha : ∀ i, (a i : Γ(X, V i)) = res X (le_inf le_top (hσ i)) (q.val (σ i)))
    (i j : I) :
    res X (inf_le_left : V i ⊓ V j ≤ V i) (a i : Γ(X, V i)) =
      (refinedUnits X U g V σ hσ i j : Γ(X, V i ⊓ V j)) *
        res X inf_le_right (a j : Γ(X, V j)) := by
  have hW : V i ⊓ V j ≤ ((⊤ : X.Opens) ⊓ U (σ i)) ⊓ U (σ j) :=
    le_inf (le_inf le_top (inf_le_left.trans (hσ i))) (inf_le_right.trans (hσ j))
  have h := congrArg (res X hW) (q.property (σ i) (σ j))
  have hq : res X (inf_le_left : V i ⊓ V j ≤ V i)
      (res X (le_inf le_top (hσ i)) (q.val (σ i))) =
    (refinedUnits X U g V σ hσ i j : Γ(X, V i ⊓ V j)) *
      res X inf_le_right (res X (le_inf le_top (hσ j)) (q.val (σ j))) := by
    simpa only [refinedUnits_val, map_mul, res_res] using h
  exact (congrArg (res X (inf_le_left : V i ⊓ V j ≤ V i)) (ha i)).trans
    (hq.trans (congrArg (fun z : Γ(X, V j) =>
      (refinedUnits X U g V σ hσ i j : Γ(X, V i ⊓ V j)) *
        res X inf_le_right z) (ha j).symm))

/-- The roots obey the actual atlas overlap rescaling, with its original units. -/
theorem rootUnit_overlap (i j : AffineOpenRefinement.Index X L.localTrivializations.X) :
    res X (inf_le_left : AffineOpenRefinement.opens X L.localTrivializations.X i ⊓
      AffineOpenRefinement.opens X L.localTrivializations.X j ≤
      AffineOpenRefinement.opens X L.localTrivializations.X i)
        (rootUnit X L t b i : Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i)) =
      (refinedUnits X L.localTrivializations.X (invertibleSheafUnits X L)
        (AffineOpenRefinement.opens X L.localTrivializations.X)
        (AffineOpenRefinement.original X L.localTrivializations.X)
        (AffineOpenRefinement.subordinate X L.localTrivializations.X) i j :
          Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X i ⊓
            AffineOpenRefinement.opens X L.localTrivializations.X j)) *
        res X inf_le_right
          (rootUnit X L t b j : Γ(X, AffineOpenRefinement.opens X L.localTrivializations.X j)) := by
  exact refined_roots_overlap X L.localTrivializations.X (invertibleSheafUnits X L)
    ((invertibleSheafRecoveryIso X L).hom.val.app (op ⊤) (rootSection X L t b))
    (AffineOpenRefinement.opens X L.localTrivializations.X)
    (AffineOpenRefinement.original X L.localTrivializations.X)
    (AffineOpenRefinement.subordinate X L.localTrivializations.X)
    (rootUnit X L t b) (rootUnit_val_coordinate X L t b) i j

end KltDP.Geometry.QuadraticGlobalRootCoordinates

#print axioms KltDP.Geometry.QuadraticGlobalRootCoordinates.rootUnit_sq
#print axioms KltDP.Geometry.QuadraticGlobalRootCoordinates.rootUnit_overlap
