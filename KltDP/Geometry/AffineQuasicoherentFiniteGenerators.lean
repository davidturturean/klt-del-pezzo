/-
Original pinned-API adapter for the finite-generators argument in
Vilin97/MazurTheorem, commit 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleQuasicoherent.lean:661-676,1648-1688. Released under Apache 2.0.
The original tilde counit, actual free coproducts and section modules are retained.
-/
import KltDP.Geometry.AffineQuasicoherentCounit
import KltDP.Geometry.AffineModuleTildeFiniteType

/-!
# Original finite global generators on Spec R

The proved original tilde/global-sections counit reflects epimorphisms
between quasicoherent sheaves to surjections of their actual section
modules. A finite global generating family therefore gives a finite
section module. Conversely, a finite original section module supplies an
actual finite global generating family through its actual tilde counit.

The passage from local finite type to finite global generators remains
a separate compact affine-cover argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]

private theorem epi_of_iso_square {C : Type*} [Category C] {A B M N : C}
    (q : A ⟶ B) (g : M ⟶ N) (a : A ⟶ M) (b : B ⟶ N)
    [Epi g] [Epi a] [IsIso b] (h : q ≫ b = a ≫ g) : Epi q := by
  have heq : q = (a ≫ g) ≫ inv b := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

private theorem map_epi_of_natural_iso_components
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) [F.ReflectsEpimorphisms]
    (ε : G ⋙ F ⟶ 𝟭 D) {M N : D} (g : M ⟶ N)
    [Epi g] [Epi (ε.app M)] [IsIso (ε.app N)] : Epi (G.map g) :=
  F.epi_of_epi_map (epi_of_iso_square (F.map (G.map g)) g
    (ε.app M) (ε.app N) (ε.naturality g))

private theorem globalSections_epi_of_counit_iso {M N : (Spec (.of R)).Modules}
    (g : M ⟶ N) [Epi g] [IsIso (counit M)] [IsIso (counit N)] :
    Epi ((globalSectionsFunctor R).map g) := by
  letI : Epi ((counitNatTrans R).app M) := inferInstanceAs (Epi (counit M))
  letI : IsIso ((counitNatTrans R).app N) := inferInstanceAs (IsIso (counit N))
  exact map_epi_of_natural_iso_components (functor R) (globalSectionsFunctor R)
    (counitNatTrans R) g

/-- Actual affine global sections take an epimorphism between original
quasicoherent sheaves to a surjective original module map. -/
theorem globalSections_map_surjective_of_epi {M N : (Spec (.of R)).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (g : M ⟶ N) [Epi g] :
    Function.Surjective ((globalSectionsFunctor R).map g) := by
  letI : IsIso (counit M) := counit_isIso_of_isQuasicoherent M
  letI : IsIso (counit N) := counit_isIso_of_isQuasicoherent N
  letI : Epi ((globalSectionsFunctor R).map g) := globalSections_epi_of_counit_iso g
  exact (ModuleCat.epi_iff_surjective ((globalSectionsFunctor R).map g)).mp inferInstance

/-- A finite actual global generating family gives finite original affine
global sections; finite freeness is retained through the original coproduct. -/
theorem globalSections_finite_of_generatingSections (M : (Spec (.of R)).Modules)
    [M.IsQuasicoherent] (G : M.GeneratingSections) [Finite G.I] :
    Module.Finite R (sectionModule M ⊤) := by
  let P : ModuleCat.{u} R := ∐ (fun _ : G.I => ModuleCat.of R R)
  let eP := finiteCoproductIsoPi R G.I
  letI : Module.Finite R P := Module.Finite.equiv eP.symm.toLinearEquiv
  let e : P ≅ (globalSectionsFunctor R).obj
      (_root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) G.I) :=
    (unitNatIso R).app P ≪≫ (globalSectionsFunctor R).mapIso (freeCoproductIso R G.I)
  letI : IsIso (counit (_root_.SheafOfModules.free
      (R := (Spec (.of R)).ringCatSheaf) G.I)) := counit_isIso_of_free R G.I
  letI : IsIso (counit M) := counit_isIso_of_isQuasicoherent M
  letI : Epi ((globalSectionsFunctor R).map G.π) := globalSections_epi_of_counit_iso G.π
  let q := e.hom ≫ (globalSectionsFunctor R).map G.π
  letI : Epi q := inferInstanceAs (Epi (e.hom ≫ (globalSectionsFunctor R).map G.π))
  exact Module.Finite.of_surjective q.hom ((ModuleCat.epi_iff_surjective q).mp inferInstance)

/-- Finite actual affine global sections give an actual finite global
free epimorphism onto the same original quasicoherent sheaf. -/
theorem exists_finite_generatingSections_of_globalSections_finite
    (M : (Spec (.of R)).Modules) [M.IsQuasicoherent]
    [Module.Finite R (sectionModule M ⊤)] :
    ∃ G : M.GeneratingSections, Finite G.I := by
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi R (sectionModule M ⊤)
  letI : Epi p := hp
  letI : IsIso (counit M) := counit_isIso_of_isQuasicoherent M
  let q := p ≫ counit M
  letI : Epi q := inferInstanceAs (Epi (p ≫ counit M))
  let G := (_root_.SheafOfModules.free.generatingSections
    (R := (Spec (.of R)).ringCatSheaf) (ULift.{u} (Fin n))).ofEpi q
  refine ⟨G, ?_⟩
  exact inferInstanceAs (Finite (ULift.{u} (Fin n)))

end KltDP.Geometry.AffineModuleTilde
