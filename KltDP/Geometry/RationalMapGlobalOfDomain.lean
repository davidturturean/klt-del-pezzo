import Mathlib.AlgebraicGeometry.RationalMap

/-! A rational map whose proved domain is the whole original scheme
gives an actual morphism with its original function-field restriction. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RationalMapGlobalOfDomain

variable {X Y : Scheme.{u}} [IsIntegral X] [Y.IsSeparated]
    (f : X.RationalMap Y) (hf : f.domain = ⊤)

def hom : X ⟶ Y :=
  X.topIso.inv ≫ (X.isoOfEq hf).inv ≫ f.toPartialMap.hom

theorem inclusion_hom : f.domain.ι ≫ hom f hf = f.toPartialMap.hom := by
  have hi : f.domain.ι ≫ X.topIso.inv ≫ (X.isoOfEq hf).inv = 𝟙 _ := by
    apply (cancel_mono f.domain.ι).mp
    simp only [Category.assoc, Scheme.isoOfEq_inv_ι,
      Scheme.toIso_inv_ι, Category.comp_id, Category.id_comp]
  simpa only [hom, ← Category.assoc, Category.id_comp] using
    congrArg (fun q => q ≫ f.toPartialMap.hom) hi

theorem fromFunctionField :
    X.fromSpecStalk (genericPoint X) ≫ hom f hf = f.fromFunctionField := by
  let p := f.toPartialMap
  have hx : genericPoint X ∈ p.domain :=
    (genericPoint_specializes _).mem_open p.domain.isOpen
      p.dense_domain.nonempty.choose_spec
  have hp : X.fromSpecStalk (genericPoint X) ≫ hom f hf = p.fromFunctionField := by
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι p.domain (genericPoint X) hx,
      Category.assoc]
    change f.domain.fromSpecStalkOfMem (genericPoint X) hx ≫
      (f.domain.ι ≫ hom f hf) = p.fromFunctionField
    rw [inclusion_hom]
    rfl
  exact hp.trans (congrArg Scheme.RationalMap.fromFunctionField
    (Scheme.RationalMap.toRationalMap_toPartialMap f))

end KltDP.Geometry.RationalMapGlobalOfDomain
