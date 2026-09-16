/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

Adapted from official Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:69–194.
The pinned Presentation, free sheaves and actual generating morphisms are retained.
-/
import KltDP.Compatibility.SheafGeneratingSectionsMap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Transporting original module-sheaf presentations

A colimit-preserving functor with an actual unit isomorphism carries a
presentation to a presentation. Its relation map is constructed from the
mapped original relation and kernel inclusion. Cokernel preservation proves
that these relations generate the new kernel; kernel preservation is not
required. This supplies the presentation transport used in affine
quasicoherent reconstruction, without assuming that reconstruction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u u₁ v₁ u₂ v₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {ι σ : Type u}

/-- The actual cokernel projection supplies the original generating family. -/
def generatorsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : M.GeneratingSections where
  I := σ
  s := M.freeHomEquiv g
  epi := by
    simp only [Equiv.symm_apply_apply]
    exact epi_of_isColimit_cofork H'

@[simp]
theorem generatorsOfIsCokernelFree_π {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (generatorsOfIsCokernelFree f g H H').π = g :=
  M.freeHomEquiv.symm_apply_apply g

/-- The original relations surject onto the actual kernel of the projection. -/
def relationsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (kernel (generatorsOfIsCokernelFree f g H H').π).GeneratingSections where
  I := ι
  s := (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv
    (kernel.lift (generatorsOfIsCokernelFree f g H H').π f (by simp [H]))
  epi := by
    let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    let h' : Abelian.image f ≅ kernel (generatorsOfIsCokernelFree f g H H').π :=
      kernel.mapIso (cokernel.π f) (generatorsOfIsCokernelFree f g H H').π
        (Iso.refl _) h (by simp [h])
    have hcomp : Abelian.factorThruImage f ≫ h'.hom =
        kernel.lift (generatorsOfIsCokernelFree f g H H').π f (by simp [H]) := by
      apply equalizer.hom_ext
      simp [h']
    simp only [Equiv.symm_apply_apply]
    rw [← hcomp]
    infer_instance

/-- Build a presentation from the original free cokernel diagram. -/
def presentationOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : M.Presentation where
  generators := generatorsOfIsCokernelFree f g H H'
  relations := relationsOfIsCokernelFree f g H H'

/-- The actual presentation is the cokernel of its relation map. -/
def Presentation.isColimit {M : SheafOfModules.{u} R} (P : M.Presentation) :
    IsColimit (CokernelCofork.ofπ
      (f := P.relations.π ≫ kernel.ι P.generators.π) P.generators.π (by simp)) := by
  letI : Epi P.generators.π := P.generators.epi
  letI : Epi P.relations.π := P.relations.epi
  exact isCokernelEpiComp
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι P.generators.π) (kernel.condition _))
      (kernelIsKernel P.generators.π)) P.relations.π rfl

/-- An actual isomorphism transports both original generating families. -/
def Presentation.ofIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (P : M.Presentation) : N.Presentation where
  generators := P.generators.ofEpi f
  relations := P.relations.ofEpi
    ((kernelCompMono P.generators.π f).symm ≪≫
      eqToIso (by rw [P.generators.ofEpi_π f])).hom

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [HasSheafify K AddCommGrp.{u}] [K.WEqualsLocallyBijective AddCommGrp.{u}]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {M : SheafOfModules.{u} R} (P : M.Presentation)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R))

local instance : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F

/-- Original relations, mapped by F and expressed in its actual free coordinates. -/
def Presentation.mapRelations : free (R := S) P.relations.I ⟶ free P.generators.I :=
  (mapFreeIso F P.relations.I η).hom ≫ F.map P.relations.π ≫
    F.map (kernel.ι P.generators.π) ≫ (mapFreeIso F P.generators.I η).inv

/-- Original generators, with the same index and the canonical free comparison. -/
abbrev Presentation.mapGenerators : free P.generators.I ⟶ F.obj M :=
  P.generators.mapFreeHom F η

theorem Presentation.mapRelations_mapGenerators :
    P.mapRelations F η ≫ P.mapGenerators F η = 0 := by
  simp only [Presentation.mapRelations, Presentation.mapGenerators,
    GeneratingSections.mapFreeHom, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]

/-- Colimit preservation transports an actual presentation. -/
def Presentation.map : (F.obj M).Presentation :=
  presentationOfIsCokernelFree (P.mapRelations F η) (P.mapGenerators F η)
    (P.mapRelations_mapGenerators F η) (by
      refine IsColimit.equivOfNatIsoOfIso
        (parallelPair.ext (mapFreeIso F P.relations.I η).symm
          (mapFreeIso F P.generators.I η).symm
          (by simp [Presentation.mapRelations]) (by simp)) _ _ ?_
        (isColimitOfPreserves F P.isColimit)
      exact Cocones.ext (Iso.refl _) (by
        rintro (_ | _)
        <;> simp [Presentation.mapRelations, Presentation.mapGenerators,
          GeneratingSections.mapFreeHom, ← Functor.map_comp]))

/-- The resulting projection remains the mapped original generator morphism. -/
theorem Presentation.map_π_eq :
    (P.map F η).generators.π = (mapFreeIso F P.generators.I η).hom ≫ F.map P.generators.π :=
  (F.obj M).freeHomEquiv.symm_apply_apply _

@[simp]
theorem Presentation.map_generators_I : (P.map F η).generators.I = P.generators.I := rfl

@[simp]
theorem Presentation.map_relations_I : (P.map F η).relations.I = P.relations.I := rfl

end SheafOfModules
