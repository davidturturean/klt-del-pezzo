import KltDP.Geometry.GlobalGenerationOfLocalExtensions

/-!
# Original global generators from unit coefficients in actual local frames

A global family containing a section with coefficient one in each frame
of an original open cover generates the actual module sheaf. The original
family itself, and thus its finite index when present, is retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.FramedGlobalGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Abstract

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}]
  [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  (M : _root_.SheafOfModules.{u} R) (e : M ≅ _root_.SheafOfModules.unit R)

/-- The unit of an actual global frame is a singleton generating family. -/
def generatorsOfUnitIso : M.GeneratingSections where
  I := PUnit.{u + 1}
  s _ := M.unitHomEquiv e.inv
  epi := by
    constructor
    intro N a b hab
    have h := congrArg (fun f => N.freeHomEquiv f PUnit.unit) hab
    have he : N.unitHomEquiv (e.inv ≫ a) = N.unitHomEquiv (e.inv ≫ b) := by
      simpa only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
        Equiv.apply_symm_apply, _root_.SheafOfModules.unitHomEquiv_comp_apply] using h
    exact (cancel_epi e.inv).mp (N.unitHomEquiv.injective he)

end Abstract

local instance framedOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance framedOverLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}


variable {X : Scheme.{u}}

/-- An original global family containing a unit coefficient on each actual
frame chart gives an epimorphism from the original free sheaf on that family. -/
theorem epi_of_unit_coefficients (M : X.Modules)
    {I K : Type u} (U : I → X.Opens) (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (e : ∀ i, M.over (U i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (T : K → M.sections)
    (hT : ∀ i, ∃ j, (e i).hom.val.app (op (Over.mk (𝟙 (U i))))
      ((T j).val (op (U i))) = (1 : Γ(X, U i))) :
    Epi (M.freeHomEquiv.symm T) := by
  apply GlobalGenerationOfLocalExtensions.epi_of_generator_extensions M U hcover
    (fun i => generatorsOfUnitIso (M.over (U i)) (e i)) T
  intro i k
  obtain ⟨j, hj⟩ := hT i
  refine ⟨j, ?_⟩
  have hid : (e i).inv.val.app (op (Over.mk (𝟙 (U i))))
      ((e i).hom.val.app (op (Over.mk (𝟙 (U i)))) ((T j).val (op (U i)))) =
      (T j).val (op (U i)) :=
    congrArg (fun f : M.over (U i) ⟶ M.over (U i) =>
      f.val.app (op (Over.mk (𝟙 (U i)))) ((T j).val (op (U i)))) (e i).hom_inv_id
  exact hid.symm.trans
    (congrArg ((e i).inv.val.app (op (Over.mk (𝟙 (U i))))) hj)

/-- The original generating family with its original index, without
replacing it by all global sections or an enlarged choice family. -/
def generatingSectionsOfUnitCoefficients (M : X.Modules)
    {I K : Type u} (U : I → X.Opens) (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (e : ∀ i, M.over (U i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (T : K → M.sections)
    (hT : ∀ i, ∃ j, (e i).hom.val.app (op (Over.mk (𝟙 (U i))))
      ((T j).val (op (U i))) = (1 : Γ(X, U i))) : M.GeneratingSections where
  I := K
  s := T
  epi := epi_of_unit_coefficients M U hcover e T hT

end KltDP.Geometry.FramedGlobalGeneration
