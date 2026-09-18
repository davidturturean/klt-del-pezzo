import KltDP.Geometry.CompleteLinearSystemGlobalGeneration

/-! The complete original linear-system morphism extends to the whole
source when its actual section-generatedness has been proved. The same
morphism and the same degree-one pullback comparison are retained. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.CompleteLinearSystemGlobalMorphism
open CompleteLinearSystemSections

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] (hpos : 0 < dimension f L)
  (hL : Positivity.IsGloballyGenerated L.obj)

/-- The original non-base inclusion is an isomorphism onto the whole source. -/
def domainIso : (CompleteLinearSystemMap.nonBaseOpen f L hpos).toScheme ≅ X := by
  let U := CompleteLinearSystemMap.nonBaseOpen f L hpos
  have hU : U = ⊤ := CompleteLinearSystemGlobalGeneration.nonBaseOpen_eq_top f L hpos hL
  letI : IsIso U.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι
    (by simpa only [Scheme.Opens.opensRange_ι] using hU)
  exact asIso U.ι

/-- The original complete-system map, on the whole original scheme. -/
def morphism : X ⟶ projectiveSpace k (dimension f L - 1) :=
  (domainIso f L hpos hL).inv ≫ CompleteLinearSystemMap.morphism f L hpos

/-- Restricting the global morphism recovers the original complete-system morphism. -/
theorem domainIso_hom_morphism :
    (domainIso f L hpos hL).hom ≫ morphism f L hpos hL =
      CompleteLinearSystemMap.morphism f L hpos := by
  rw [morphism, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The global morphism preserves the original field structure. -/
@[reassoc] theorem morphism_structure :
    morphism f L hpos hL ≫ projectiveSpaceToSpec k (dimension f L - 1) = f := by
  rw [morphism, Category.assoc, CompleteLinearSystemMap.morphism_structure,
    ← Category.assoc]
  change ((domainIso f L hpos hL).inv ≫ (domainIso f L hpos hL).hom) ≫ f = f
  rw [Iso.inv_hom_id, Category.id_comp]

/-- The original O(1) pulls back to the original line on the whole source. -/
def pullbackDegreeOneIso :
    (pullbackInvertibleSheaf (morphism f L hpos hL)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1))).obj ≅ L.obj := by
  let a := domainIso f L hpos hL
  let m := CompleteLinearSystemMap.morphism f L hpos
  let H := ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1)
  exact ((schemeModulePullbackCompIso a.inv m).app H.obj).symm ≪≫
    (schemeModulePullback a.inv).mapIso (CompleteLinearSystemMap.pullbackDegreeOneIso f L hpos) ≪≫
    (schemeModulePullbackCompIso a.inv a.hom).app L.obj ≪≫
    eqToIso (congrArg (fun q : X ⟶ X => (schemeModulePullback q).obj L.obj) a.inv_hom_id) ≪≫
    (schemeModulePullbackIdIso X).app L.obj

end KltDP.Geometry.CompleteLinearSystemGlobalMorphism

#check @KltDP.Geometry.CompleteLinearSystemGlobalMorphism.pullbackDegreeOneIso
#print axioms KltDP.Geometry.CompleteLinearSystemGlobalMorphism.pullbackDegreeOneIso
