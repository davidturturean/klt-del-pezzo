import KltDP.Geometry.InvertibleSectionNonvanishingOpen

/-! Actual sheaf isomorphisms preserve intrinsic nonvanishing opens
of the same original compatible sections. The transported atlas supplies
the exact inverse-coordinate comparison. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.InvertibleSectionNonvanishingOpen

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open TransitionUnitExtraction

variable {X : Scheme.{u}}

/-- Transported frame coordinates use the original inverse sheaf map. -/
theorem unitIso_ofIso_hom {M N : X.Modules}
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (e : M ≅ N) (i : t.I) :
    ((t.ofIso e).unitIso i).hom =
      (_root_.SheafOfModules.overFunctor X.ringCatSheaf (t.X i)).map e.inv ≫
        (t.unitIso i).hom := by
  simp only [KltDP.SheafOfModules.LocalTrivializations.unitIso,
    KltDP.SheafOfModules.LocalTrivializations.ofIso, Iso.symm_hom,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Category.assoc]

/-- On the same chart, transport followed by inverse coordinates
returns the original coefficient. -/
theorem chartCoefficient_ofIso {M N : X.Modules}
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (e : M ≅ N) (s : M.sections) (i : t.I) :
    chartCoefficient X N (t.ofIso e) (_root_.SheafOfModules.sectionsMap e.hom s) i =
      chartCoefficient X M t s i := by
  let U : X.Opens := t.X i
  let V : (Over U)ᵒᵖ := op (Over.mk (homOfLE (le_refl U)))
  let r : M.val.obj (op U) := s.val (op U)
  let a := (t.unitIso i).hom.val.app V
  have heval : ((t.ofIso e).unitIso i).hom.val.app V (e.hom.val.app (op U) r) =
      a (e.inv.val.app (op U) (e.hom.val.app (op U) r)) :=
    congrArg (fun q : N.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U) =>
      q.val.app V (e.hom.val.app (op U) r)) (unitIso_ofIso_hom t e i)
  have hc : e.inv.val.app (op U) (e.hom.val.app (op U) r) = r :=
    congrArg (fun q : M ⟶ M => q.val.app (op U) r) e.hom_inv_id
  calc
    chartCoefficient X N (t.ofIso e) (_root_.SheafOfModules.sectionsMap e.hom s) i =
        ((t.ofIso e).unitIso i).hom.val.app V (e.hom.val.app (op U) r) := rfl
    _ = a (e.inv.val.app (op U) (e.hom.val.app (op U) r)) := heval
    _ = a r := congrArg a hc
    _ = chartCoefficient X M t s i := rfl

/-- The same original section has exactly the same intrinsic
nonvanishing open after an actual sheaf isomorphism. -/
theorem nonvanishingOpen_sectionsMap_iso (L N : InvertibleSheaf X)
    (e : L.obj ≅ N.obj) (s : L.obj.sections) :
    nonvanishingOpen X N (_root_.SheafOfModules.sectionsMap e.hom s) =
      nonvanishingOpen X L s := by
  let t := L.localTrivializations
  let d := t.ofIso e
  change nonvanishingOpenOfAtlas X N.obj N.localTrivializations
    (_root_.SheafOfModules.sectionsMap e.hom s) = nonvanishingOpenOfAtlas X L.obj t s
  rw [nonvanishingOpenOfAtlas_eq X N.obj N.localTrivializations d]
  change (⨆ i : t.I, X.basicOpen
    (chartCoefficient X N.obj (t.ofIso e)
      (_root_.SheafOfModules.sectionsMap e.hom s) i)) =
    (⨆ i : t.I, X.basicOpen (chartCoefficient X L.obj t s i))
  apply iSup_congr
  intro i
  exact congrArg X.basicOpen (chartCoefficient_ofIso t e s i)

end KltDP.Geometry.InvertibleSectionNonvanishingOpen

#check @KltDP.Geometry.InvertibleSectionNonvanishingOpen.nonvanishingOpen_sectionsMap_iso
#print axioms KltDP.Geometry.InvertibleSectionNonvanishingOpen.nonvanishingOpen_sectionsMap_iso
