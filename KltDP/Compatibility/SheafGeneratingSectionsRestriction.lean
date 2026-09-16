import KltDP.Compatibility.SheafGeneratingSectionsMap

/-!
# Restricted generating sections retain their original values

The accepted restriction construction maps the actual free coproduct through
the colimit-preserving Over functor.  The coproduct comparison commutes with
each original summand inclusion.  Consequently each transported generating
section is exactly the original section evaluated on the underlying open.
This identifies the concrete sections selected by a local generator argument.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace KltDP.SheafGeneratingSectionsRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type w} [Category.{w} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, HasSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- The accepted free-sheaf restriction comparison respects each original
unit summand. -/
theorem overFreeIso_ι (U : C) (I : Type u) (i : I) :
    Sigma.ι (fun _ : I => _root_.SheafOfModules.unit (R.over U)) i ≫
        (_root_.SheafOfModules.mapFreeIso (_root_.SheafOfModules.overFunctor R U) I
          (_root_.SheafOfModules.unitOverIso (R := R) U).symm).hom =
      (_root_.SheafOfModules.unitOverIso (R := R) U).inv ≫
        (_root_.SheafOfModules.overFunctor R U).map
          (Sigma.ι (fun _ : I => _root_.SheafOfModules.unit R) i) := by
  simp [_root_.SheafOfModules.mapFreeIso, PreservesCoproduct.inv_hom,
    Sigma.mapIso, Sigma.map, Category.assoc]
  exact ι_comp_sigmaComparison (_root_.SheafOfModules.overFunctor R U)
    (fun _ : I => _root_.SheafOfModules.unit R) i

/-- Expose the original coproduct-inclusion formula for section values
without reducing a particular colimit comparison. -/
theorem freeHomEquiv_val {D : Type w} [Category.{v} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrp.{u}] [K.WEqualsLocallyBijective AddCommGrp.{u}]
    [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
    {N : _root_.SheafOfModules.{u} S} {I : Type u}
    (f : _root_.SheafOfModules.free I ⟶ N) (i : I) (V : Dᵒᵖ) :
    (N.freeHomEquiv f i).val V =
      (Sigma.ι (fun _ : I => _root_.SheafOfModules.unit S) i ≫ f).val.app V
        (1 : S.val.obj V) := rfl

/-- Each section of the restricted generating family is the original
section, evaluated on the underlying object of the Over-site. -/
theorem generatorsOver_section_val {M : _root_.SheafOfModules.{u} R}
    (G : M.GeneratingSections) (U : C) (i : G.I) (V : (Over U)ᵒᵖ) :
    (((G.map (_root_.SheafOfModules.overFunctor R U)
      (_root_.SheafOfModules.unitOverIso (R := R) U).symm).s i).val V) =
      (G.s i).val (op V.unop.left) := by
  have hι : Sigma.ι (fun _ : G.I => _root_.SheafOfModules.unit R) i ≫ G.π =
      M.unitHomEquiv.symm (G.s i) := by
    change Sigma.ι _ i ≫ Sigma.desc (fun j => M.unitHomEquiv.symm (G.s j)) = _
    exact Sigma.ι_desc _ i
  simp only [_root_.SheafOfModules.GeneratingSections.map, freeHomEquiv_val,
    _root_.SheafOfModules.GeneratingSections.mapFreeHom]
  rw [← Category.assoc, overFreeIso_ι]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hι]
  change (M.unitHomEquiv (M.unitHomEquiv.symm (G.s i))).val (op V.unop.left) = _
  rw [Equiv.apply_symm_apply]

end KltDP.SheafGeneratingSectionsRestriction
