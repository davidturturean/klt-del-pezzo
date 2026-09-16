import KltDP.Geometry.AffineModuleTildeKernel
import KltDP.Geometry.AffineModuleTildeFiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite-type kernels of actual finite-free maps on an affine scheme

An arbitrary map from a finite free sheaf to an original tilde sheaf lifts
through the proved full faithfulness to a map of actual modules. Its
categorical module kernel embeds in the actual finite product of copies
of the Noetherian base ring. The resulting finite generation passes through
the proved tilde kernel comparison and the original Over-site generators.

The structure-sheaf case is obtained through the existing unit isomorphism.
Neither the given map nor its chosen section family is assumed surjective.
This is an affine kernel lemma, not the assertion of local coherence on
arbitrary opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (R : Type u) [CommRing R] (I : Type u) (N : ModuleCat.{u} R)

/-- Recover the actual module map of an arbitrary free-to-tilde morphism. -/
def finiteFreeModuleMap
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    (∐ (fun _ : I => ModuleCat.of R R)) ⟶ N :=
  (functor R).preimage ((freeCoproductIso R I).hom ≫ φ)

/-- The recovered map has exactly the original sheaf morphism. -/
@[simp]
theorem finiteFreeModuleMap_map
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    (functor R).map (finiteFreeModuleMap R I N φ) = (freeCoproductIso R I).hom ≫ φ :=
  (functor R).map_preimage _

/-- The actual kernel is identified through the original free comparison. -/
def freeToTildeKernelIso
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    (kernel (finiteFreeModuleMap R I N φ)).tilde ≅ kernel φ :=
  kernelIso (finiteFreeModuleMap R I N φ) ≪≫
    kernel.mapIso ((functor R).map (finiteFreeModuleMap R I N φ)) φ
      (freeCoproductIso R I) (Iso.refl N.tilde) (by
        simpa only [Iso.refl_hom, finiteFreeModuleMap_map] using
          (Category.comp_id ((freeCoproductIso R I).hom ≫ φ)))

/-- The actual sheaf kernel inclusion corresponds to the actual module inclusion. -/
theorem freeToTildeKernelIso_hom_ι
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    (freeToTildeKernelIso R I N φ).hom ≫ kernel.ι φ =
      (functor R).map (kernel.ι (finiteFreeModuleMap R I N φ)) ≫
        (freeCoproductIso R I).hom := by
  simp only [freeToTildeKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.lift_ι]
  rw [← Category.assoc, kernelIso_hom_ι]

variable [Finite I] [IsNoetherianRing R]

/-- The original categorical module kernel embeds in the finite Noetherian product. -/
theorem finiteFreeModuleMap_kernel_finite
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    Module.Finite R (kernel (finiteFreeModuleMap R I N φ) : ModuleCat.{u} R) := by
  let j := kernel.ι (finiteFreeModuleMap R I N φ) ≫ (finiteCoproductIsoPi R I).hom
  exact Module.Finite.of_injective j.hom
    ((ModuleCat.mono_iff_injective j).mp
      (inferInstanceAs (Mono
        (kernel.ι (finiteFreeModuleMap R I N φ) ≫ (finiteCoproductIsoPi R I).hom))))

/-- Every original finite-free-to-tilde map has finite-type actual kernel. -/
theorem isFiniteType_kernel_free_to_tilde
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    _root_.SheafOfModules.IsFiniteType (kernel φ) := by
  letI := finiteFreeModuleMap_kernel_finite R I N φ
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi R (kernel (finiteFreeModuleMap R I N φ))
  letI : Epi p := hp
  exact _root_.SheafOfModules.isFiniteType_of_free_epi
    (R := (Spec (.of R)).ringCatSheaf) (M := kernel φ)
    (I := ULift.{u} (Fin n)) (p := p ≫ (freeToTildeKernelIso R I N φ).hom)

omit [Finite I] [IsNoetherianRing R] in
/-- The structure-sheaf case uses the original unit isomorphism. -/
def freeToUnitKernelIso
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf) :
    (kernel (finiteFreeModuleMap R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv))).tilde ≅
      kernel φ :=
  freeToTildeKernelIso R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv) ≪≫
    kernel.mapIso (φ ≫ (unitIso R).inv) φ (Iso.refl _) (unitIso R) (by simp)

omit [Finite I] [IsNoetherianRing R] in
/-- The unit-target comparison retains the same original kernel inclusion. -/
theorem freeToUnitKernelIso_hom_ι
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf) :
    (freeToUnitKernelIso R I φ).hom ≫ kernel.ι φ =
      (functor R).map
        (kernel.ι (finiteFreeModuleMap R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv))) ≫
          (freeCoproductIso R I).hom := by
  simp only [freeToUnitKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.lift_ι, Iso.refl_hom, Category.comp_id]
  exact freeToTildeKernelIso_hom_ι R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv)

/-- The affine structure-sheaf kernel condition holds for every original finite family. -/
theorem isFiniteType_kernel_free_to_unit
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf) :
    _root_.SheafOfModules.IsFiniteType (kernel φ) := by
  letI := finiteFreeModuleMap_kernel_finite R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv)
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi R
    (kernel (finiteFreeModuleMap R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv)))
  letI : Epi p := hp
  exact _root_.SheafOfModules.isFiniteType_of_free_epi
    (R := (Spec (.of R)).ringCatSheaf) (M := kernel φ)
    (I := ULift.{u} (Fin n)) (p := p ≫ (freeToUnitKernelIso R I φ).hom)

end KltDP.Geometry.AffineModuleTilde
