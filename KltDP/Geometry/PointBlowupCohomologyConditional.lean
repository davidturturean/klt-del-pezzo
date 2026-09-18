import KltDP.Geometry.Resolution
import KltDP.Geometry.SchemeIsoCohomology
import KltDP.Geometry.SchemeModuleIso
import KltDP.Geometry.ModuleCohomologyEuler

/-!
# Original point-blowup structure-sheaf cohomology

The complete three-clause Hartshorne V.3.4 statement remains an explicit
hypothesis. Its all-degree module-valued comparison is transported through
the original blowup presentation and the original field triangle. The
resulting dimensions and Euler value concern the original surface sheaves.
No higher-direct-image vanishing or comparison is inferred from pushforward
of the structure sheaf alone.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original unit-sheaf comparison and scheme-isomorphism cohomology
comparison preserve the original base-field actions. -/
def schemeIsoStructureHLinearEquiv
    {k : Type u} [Field k] {X Y : Scheme.{u}} (e : X ≅ Y)
    (g : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    (baseFunctor g n).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ≃ₗ[k]
      (baseFunctor (e.hom ≫ g) n).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  ((baseFunctor g n).mapIso (schemeIsoUnitIso e)).toLinearEquiv.trans
    (pushforwardIsoHBaseRingLinearEquiv e g
      (_root_.SheafOfModules.unit X.ringCatSheaf) n)

end KltDP.Geometry.ModuleCohomology

namespace KltDP.Geometry

open ModuleCohomology

variable (hHartshorne : ∀ (k : Type u) [Field k] [IsAlgClosed k]
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
            (_root_.SheafOfModules.unit c.scheme.ringCatSheaf)))))

include hHartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {p : T.Point}

/-- An original point blowup preserves all structure-sheaf cohomology
over the original field, through its actual presentation isomorphism. -/
theorem IsPointBlowupAt.structureSheafHLinearEquiv_nonempty
    (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (n : ℕ) :
    Nonempty
      (((baseFunctor S.structureMorphism n).obj
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf)) ≃ₗ[k]
        ((baseFunctor T.structureMorphism n).obj
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf))) := by
  obtain ⟨c, e, he⟩ := hb.blowup
  have hbase : e.hom ≫ (c.projection ≫ T.structureMorphism) =
      S.structureMorphism := by
    rw [← Category.assoc, he, hb.over_base]
  have eH := schemeIsoStructureHLinearEquiv e
    (c.projection ≫ T.structureMorphism) n
  rw [hbase] at eH
  exact ⟨eH.symm.trans ((hHartshorne k T hT p c).2.2 n).some.toLinearEquiv.symm⟩

/-- Every original cohomology dimension is unchanged by a point blowup. -/
theorem IsPointBlowupAt.structureSheaf_cohomologyDimension_eq
    (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n :=
  (IsPointBlowupAt.structureSheafHLinearEquiv_nonempty hHartshorne hb hT n).some.finrank_eq

/-- Equality of the original alternating cohomology sums. -/
theorem IsPointBlowupAt.structureSheaf_eulerCharacteristic_eq
    (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) := by
  unfold eulerCharacteristic
  simp only [IsPointBlowupAt.structureSheaf_cohomologyDimension_eq hHartshorne hb hT]

/-- Irregularity is the original degree-one cohomology dimension. -/
theorem IsPointBlowupAt.irregularity_eq
    (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 :=
  IsPointBlowupAt.structureSheaf_cohomologyDimension_eq hHartshorne hb hT 1

end KltDP.Geometry

#check @KltDP.Geometry.IsPointBlowupAt.structureSheafHLinearEquiv_nonempty
#print axioms KltDP.Geometry.ModuleCohomology.schemeIsoStructureHLinearEquiv
#print axioms KltDP.Geometry.IsPointBlowupAt.structureSheaf_eulerCharacteristic_eq
#print axioms KltDP.Geometry.IsPointBlowupAt.irregularity_eq
