import KltDP.Geometry.SchemeModuleOpenLocality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The original global factor determined by normalized local maps

The pinned abelian-category monoLift constructs a factor through an original
monomorphism once its cokernel obstruction vanishes. Normalized local maps on
an actual open cover prove that vanishing. Monicity identifies the restriction
of the resulting global factor with every given local map, and the existing
local isomorphism criterion proves that the global factor is an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace KltDP.Geometry

variable {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    {M N Q : X.Modules} (b : N ⟶ Q) [Mono b] (a : M ⟶ Q)
    (e : ∀ i, (schemeModulePullback (U i).ι).obj M ≅
      (schemeModulePullback (U i).ι).obj N)
    (he : ∀ i, (e i).hom ≫ (schemeModulePullback (U i).ι).map b =
      (schemeModulePullback (U i).ι).map a)

include hU he in
/-- The local original factorizations kill the original global cokernel obstruction. -/
theorem schemeModule_monic_cokernel_zero : a ≫ cokernel.π b = 0 := by
  apply schemeModule_hom_ext_of_openCover U hU
  intro i
  let F := schemeModulePullback (U i).ι
  letI : F.PreservesZeroMorphisms :=
    schemeModulePullback_open_preservesZeroMorphisms (U i).ι
  change F.map (a ≫ cokernel.π b) = F.map 0
  rw [Functor.map_comp, ← he i, Category.assoc,
    ← F.map_comp b (cokernel.π b), cokernel.condition]
  simp only [Functor.map_zero, comp_zero]

/-- The pinned monoLift of the original global map, with its obstruction proved on the cover. -/
def schemeModuleMonicFactorOnOpenCover : M ⟶ N :=
  Abelian.monoLift b a (schemeModule_monic_cokernel_zero U hU b a e he)

/-- The global factor preserves the original global target map. -/
@[reassoc] theorem schemeModuleMonicFactorOnOpenCover_comp :
    schemeModuleMonicFactorOnOpenCover U hU b a e he ≫ b = a :=
  Abelian.monoLift_comp b a (schemeModule_monic_cokernel_zero U hU b a e he)

/-- Its actual pullback on every covering open is the prescribed normalized local map. -/
theorem schemeModuleMonicFactorOnOpenCover_map (i : ι) :
    (schemeModulePullback (U i).ι).map (schemeModuleMonicFactorOnOpenCover U hU b a e he) =
      (e i).hom := by
  letI := schemeModulePullback_open_preservesMonomorphisms (U i).ι
  apply (cancel_mono ((schemeModulePullback (U i).ι).map b)).mp
  rw [← Functor.map_comp, schemeModuleMonicFactorOnOpenCover_comp]
  exact (he i).symm

/-- The original global factor is an isomorphism because all its actual open pullbacks are. -/
theorem schemeModuleMonicFactorOnOpenCover_isIso :
    IsIso (schemeModuleMonicFactorOnOpenCover U hU b a e he) := by
  apply schemeModule_isIso_of_openCover U hU
  intro i
  rw [schemeModuleMonicFactorOnOpenCover_map]
  infer_instance

/-- The resulting original global isomorphism, constructed from monoLift rather than gluing data. -/
def schemeModuleMonicFactorIsoOnOpenCover : M ≅ N := by
  letI := schemeModuleMonicFactorOnOpenCover_isIso U hU b a e he
  exact asIso (schemeModuleMonicFactorOnOpenCover U hU b a e he)

@[reassoc] theorem schemeModuleMonicFactorIsoOnOpenCover_comp :
    (schemeModuleMonicFactorIsoOnOpenCover U hU b a e he).hom ≫ b = a :=
  schemeModuleMonicFactorOnOpenCover_comp U hU b a e he

/-- Compatibility is a theorem about the original restricted global map, not an input cocycle. -/
theorem schemeModuleMonicFactorIsoOnOpenCover_map (i : ι) :
    (schemeModulePullback (U i).ι).map
        (schemeModuleMonicFactorIsoOnOpenCover U hU b a e he).hom = (e i).hom :=
  schemeModuleMonicFactorOnOpenCover_map U hU b a e he i

end KltDP.Geometry
