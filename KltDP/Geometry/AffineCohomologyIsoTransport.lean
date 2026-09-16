/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

The quasicoherence and cohomology transport have the mathematical role of
Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleCohomologyAffineCover.lean:61-94 and
SchemeModuleCohomologyAffineHTwo.lean:147-218.
The proofs below reuse the existing project functors and cohomology
isomorphism; no modern Ext.MapBijective port is required.
-/
import KltDP.Geometry.QuasicoherentOpenRestriction
import KltDP.Geometry.SchemeIsoCohomology

/-!
# Transport for the affine-vanishing port

Pushforward along a scheme isomorphism is identified with restriction along
its inverse by uniqueness of left adjoints. The existing restriction theorem
therefore supplies quasicoherence. The existing natural cohomology comparison
transfers subsingletonness in every degree. Source draft; VM checks pending.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineCohomologyPort

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

/-- The inverse is pushforward along the actual inverse scheme map. -/
def pushforwardInverseEquivalence (e : X ≅ Y) : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (schemeModulePushforward e.hom)
    (schemeModulePushforward e.inv)
    (schemeModulePushforwardCompIso e.hom e.inv ≪≫
      eqToIso (congrArg schemeModulePushforward e.hom_inv_id) ≪≫
      schemeModulePushforwardIdIso X).symm
    (schemeModulePushforwardCompIso e.inv e.hom ≪≫
      eqToIso (congrArg schemeModulePushforward e.inv_hom_id) ≪≫
      schemeModulePushforwardIdIso Y)

/-- Along an isomorphism, actual pushforward is restriction along the inverse. -/
def pushforwardIsoRestriction (e : X ≅ Y) :
    schemeModulePushforward e.hom ≅ SchemeModuleRestriction.restriction e.inv :=
  Adjunction.leftAdjointUniq (pushforwardInverseEquivalence e).toAdjunction
    (SchemeModuleRestriction.restrictionAdjunction e.inv)

/-- Pushforward along a scheme isomorphism preserves original quasicoherence. -/
theorem pushforward_isQuasicoherent_of_iso (e : X ≅ Y)
    (M : X.Modules) [M.IsQuasicoherent] :
    ((schemeModulePushforward e.hom).obj M).IsQuasicoherent :=
  _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := Y.ringCatSheaf)
    (M := (SchemeModuleRestriction.restriction e.inv).obj M)
    (N := (schemeModulePushforward e.hom).obj M)
    ((pushforwardIsoRestriction e).app M).inv

/-- The existing cohomology comparison reflects vanishing in any degree. -/
theorem h_subsingleton_of_pushforward_iso (e : X ≅ Y) (M : X.Modules) (n : ℕ)
    [Subsingleton (ModuleCohomology.H ((schemeModulePushforward e.hom).obj M) n)] :
    Subsingleton (ModuleCohomology.H M n) := by
  let h := ModuleCohomology.pushforwardIsoHAddEquiv e M n
  exact ⟨fun a b => h.symm.injective (Subsingleton.elim _ _)⟩

end KltDP.Geometry.AffineCohomologyPort
