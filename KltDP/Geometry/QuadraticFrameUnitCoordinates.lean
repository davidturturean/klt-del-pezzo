import KltDP.Geometry.QuadraticGlobalRootCoordinates

/-!
# Unit coordinates in the original chosen module atlas

The accepted transition-unit and recovery lemmas apply to a chosen actual
atlas, including the pulled ambient atlas. This gives units on arbitrary
subopens and their literal refined transition equations. No replacement
of the original atlas by chosen invertible-sheaf charts is needed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.QuadraticFrameUnitCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open TransitionUnitGluing TransitionUnitExtraction QuadraticGlobalRootCoordinates

variable (X : Scheme.{u}) (M : X.Modules)
    (T : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (t : M ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (b : Γ(X, ⊤)ˣ)

def frameSection : M.val.obj (op (⊤ : X.Opens)) := t.inv.val.app (op ⊤) (b : Γ(X, ⊤))

def frameEquiv (W : X.Opens) : M.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op W)).mapIso t).toLinearEquiv

/-- The literal unit comparing the global frame with an original local frame. -/
def unitOn (i : T.I) {W : X.Opens} (hW : W ≤ T.X i) : Γ(X, W)ˣ :=
  KltDP.Module.transitionUnit (frameEquiv X M t W) (chartEquiv X M T i hW) *
    Units.map (res X (show W ≤ ⊤ from le_top)).toMonoidHom b

theorem unitOn_val (i : T.I) {W : X.Opens} (hW : W ≤ T.X i) :
    (unitOn X M T t b i hW : Γ(X, W)) =
      chartEquiv X M T i hW
        (M.val.map (homOfLE (show W ≤ ⊤ from le_top)).op (frameSection X M t b)) := by
  let c := chartEquiv X M T i hW
  let z : Γ(X, W) := res X (show W ≤ ⊤ from le_top) (b : Γ(X, ⊤))
  have h := KltDP.Module.transitionUnit_mul_apply (frameEquiv X M t W) c
    ((frameEquiv X M t W).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.trans (congrArg c (_root_.PresheafOfModules.naturality_apply t.inv.val
    (homOfLE (show W ≤ ⊤ from le_top)).op (b : Γ(X, ⊤))))

/-- The same unit is the original restricted recovery coordinate. -/
theorem unitOn_recoveryCoordinate (i : T.I) {W : X.Opens} (hW : W ≤ T.X i) :
    (unitOn X M T t b i hW : Γ(X, W)) =
      res X (le_inf le_top hW)
        (((recoveryIso X M T).hom.val.app (op ⊤) (frameSection X M t b)).val i) :=
  (unitOn_val X M T t b i hW).trans
    (recovery_restrict_coordinate X M T (frameSection X M t b) i W hW).symm

/-- Restricting these actual units gives the exact original refined cocycle. -/
theorem refined_overlap {I : Type u} (V : I → X.Opens) (σ : I → T.I)
    (hσ : ∀ i, V i ≤ T.X (σ i)) (i j : I) :
    res X (inf_le_left : V i ⊓ V j ≤ V i)
      (unitOn X M T t b (σ i) (hσ i) : Γ(X, V i)) =
      (refinedUnits X T.X (transitionUnits X M T) V σ hσ i j : Γ(X, V i ⊓ V j)) *
        res X inf_le_right (unitOn X M T t b (σ j) (hσ j) : Γ(X, V j)) := by
  exact refined_roots_overlap X T.X (transitionUnits X M T)
    ((recoveryIso X M T).hom.val.app (op ⊤) (frameSection X M t b))
    V σ hσ (fun i => unitOn X M T t b (σ i) (hσ i))
    (fun i => unitOn_recoveryCoordinate X M T t b (σ i) (hσ i)) i j

end KltDP.Geometry.QuadraticFrameUnitCoordinates

#print axioms KltDP.Geometry.QuadraticFrameUnitCoordinates.refined_overlap
