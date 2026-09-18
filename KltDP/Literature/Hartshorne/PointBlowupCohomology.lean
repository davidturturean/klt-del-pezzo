import KltDP.Geometry.Resolution
import KltDP.Geometry.SchemeIsoCohomology
import KltDP.Geometry.SchemeModuleIso
import KltDP.Geometry.ModuleCohomologyEuler

/-!
# Hartshorne V.3.4: full original point-blowup structure cohomology

Published GTM52, pp387-388, with the surface and closed-point conventions
on pp357/386. All three clauses and all original base-field actions are
retained. Higher direct image zero is represented on the actual underlying
abelian sheaf, using the full Stacks01F1 dictionary. No exactness on all
sheaves, selected canonical-map normalization, or characteristic restriction
is asserted. Root source/native review and ordinary consumers are recorded
in point_blowup_cohomology_reuse_20260915; production registry is unchanged.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KltDP.Geometry KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Literature.Hartshorne

axiom point_blowup_structure_cohomology_literal :
∀ (k : Type u) [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (_hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (P : X.Point) (c : PointBlowupChart X.toScheme P),
  IsIso c.projection.c ∧
    (∀ i : ℕ, 0 < i →
      IsZero
        (((schemeAbelianSheafPushforward c.projection).rightDerived i).obj
          ((_root_.SheafOfModules.toSheaf c.scheme.ringCatSheaf).obj
            (_root_.SheafOfModules.unit c.scheme.ringCatSheaf)))) ∧
    (∀ i : ℕ,
      Nonempty
        (((baseFunctor X.structureMorphism i).obj
            (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)) ≅
          ((baseFunctor (c.projection ≫ X.structureMorphism) i).obj
            (_root_.SheafOfModules.unit c.scheme.ringCatSheaf))))

end KltDP.Literature.Hartshorne

#check @KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal
