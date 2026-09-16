import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# The intrinsic nonvanishing open in an actual frame

Transport the accepted structure-module atlas through the original frame.
Its coordinates are the original frame maps, so atlas independence identifies
the intrinsic nonvanishing open with the original global coefficient's basic
open. This comparison supplies no section-extension or ampleness hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSectionNonvanishingFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen InvertibleSheafSectionPowers
open TransitionUnitExtraction

variable {X : Scheme.{u}} (L : InvertibleSheaf X)
  (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- The original structure-module atlas transported through an actual frame. -/
def atlasOfFrame : KltDP.SheafOfModules.LocalTrivializations
    (R := X.ringCatSheaf) L.obj :=
  (KltDP.SheafOfModules.unitLocalTrivializations (R := X.ringCatSheaf)).ofIso e.symm

/-- On every original open, the transported atlas map is the original
restriction of the original frame morphism. -/
theorem atlasOfFrame_unitIso_hom (U : X.Opens) :
    ((atlasOfFrame L e).unitIso U).hom =
      (_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map e.hom := by
  let F := _root_.SheafOfModules.overFunctor X.ringCatSheaf U
  let a := _root_.SheafOfModules.freeUniqueIsoUnit (R := X.ringCatSheaf.over U) PUnit
  change (F.map e.hom ≫ (_root_.SheafOfModules.unitOverIso (R := X.ringCatSheaf) U).hom ≫
      a.inv) ≫ a.hom = F.map e.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    _root_.SheafOfModules.unitOverIso, Iso.refl_hom]
  exact Category.comp_id (F.map e.hom)

private theorem atlasOfFrame_open (U : X.Opens) :
    (atlasOfFrame L e).X U = U := rfl

private theorem atlasOfFrame_chartCoefficient (s : L.obj.sections) (U : X.Opens) :
    chartCoefficient X L.obj (atlasOfFrame L e) s U =
      e.hom.val.app (op U) (s.val (op U)) := by
  have h := congrArg
    (fun g : L.obj.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U) =>
      g.val.app (op (Over.mk (homOfLE (show U ≤ U from le_rfl)))) (s.val (op U)))
    (atlasOfFrame_unitIso_hom L e U)
  exact (chartEquiv_apply X L.obj (atlasOfFrame L e) U le_rfl (s.val (op U))).trans h

/-- An actual frame identifies the intrinsic nonvanishing open with the
literal original coefficient's basic open. -/
theorem nonvanishingOpen_eq_basicOpen (s : L.obj.sections) :
    nonvanishingOpen X L s = X.basicOpen (frameCoefficient L e s) := by
  have h := chart_inf_nonvanishingOpen X L s (atlasOfFrame L e) (⊤ : X.Opens)
  have hc := congrArg (fun a : Γ(X, ⊤) => X.basicOpen a)
    (atlasOfFrame_chartCoefficient L e s (⊤ : X.Opens))
  exact (inf_eq_right.mpr le_top :
    (⊤ : X.Opens) ⊓ nonvanishingOpen X L s = nonvanishingOpen X L s).symm.trans (h.trans hc)

end KltDP.Geometry.InvertibleSectionNonvanishingFrame
