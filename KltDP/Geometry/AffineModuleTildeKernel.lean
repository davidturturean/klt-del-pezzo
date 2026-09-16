import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels of the original affine tilde functor

The canonical kernel comparison is bijective on each basic open. The
original module kernel sequence remains exact after localization, and
localization preserves its injective first map. Evaluation preserves the
monomorphism from the actual sheaf kernel. Its inclusion equation then
gives both injectivity and surjectivity of the canonical comparison.

The proof uses the pinned localization-exactness theorem and the existing
tilde section maps. It requires neither Noetherianity nor a supplied
kernel comparison isomorphism, quasicoherent reconstruction, or vanishing.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] {M N P : ModuleCat.{u} R}

-- The existing forgetful functor retains the original section carrier
-- and its original R-action, without choosing a section-ring scalar tower.
private abbrev basicOpenMap (g : M ⟶ N) (r : R) :
    M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen r)) ⟶
      N.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen r)) :=
  ((modulesSpecToSheaf R).map (map g)).val.app (op (PrimeSpectrum.basicOpen r))

private theorem basicOpenMap_eq (g : M ⟶ N) (r : R) :
    (basicOpenMap g r).hom =
      IsLocalizedModule.map (Submonoid.powers r)
        (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
        (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom g.hom := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
  apply LinearMap.ext
  intro m
  change (map g).val.app (op (PrimeSpectrum.basicOpen r))
      (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r) m) = _
  rw [map_app_toOpen]
  change (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom (g.hom m) =
    IsLocalizedModule.map (Submonoid.powers r)
      (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
      (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom g.hom
      ((ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom m)
  exact (IsLocalizedModule.map_apply (Submonoid.powers r)
    (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom g.hom m).symm

private theorem basicOpenMap_injective (g : M ⟶ N)
    (hg : Function.Injective g) (r : R) : Function.Injective (basicOpenMap g r) := by
  change Function.Injective (basicOpenMap g r).hom
  rw [basicOpenMap_eq]
  exact IsLocalizedModule.map_injective (Submonoid.powers r)
    (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom g.hom hg

private theorem basicOpenMap_exact (f : M ⟶ N) (g : N ⟶ P)
    (h : Function.Exact f g) (r : R) :
    Function.Exact (basicOpenMap f r) (basicOpenMap g r) := by
  change Function.Exact (basicOpenMap f r).hom (basicOpenMap g r).hom
  rw [basicOpenMap_eq, basicOpenMap_eq]
  exact IsLocalizedModule.map_exact (Submonoid.powers r)
    (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
    (ModuleCat.Tilde.toOpen P (PrimeSpectrum.basicOpen r)).hom f.hom g.hom h

private theorem moduleKernel_exact (g : M ⟶ N) :
    Function.Exact (kernel.ι g) g := by
  intro y
  constructor
  · intro hy
    refine ⟨(ModuleCat.kernelIsoKer g).inv ⟨y, hy⟩, ?_⟩
    exact ConcreteCategory.congr_hom (ModuleCat.kernelIsoKer_inv_kernel_ι g)
      (⟨y, hy⟩ : LinearMap.ker g.hom)
  · rintro ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom (kernel.condition g) x

/-- The original kernel comparison is bijective on each actual basic open. -/
theorem kernelComparison_basicOpen_bijective (g : M ⟶ N) (r : R) :
    Function.Bijective
      ((kernelComparison g (functor R)).val.app (op (PrimeSpectrum.basicOpen r))) := by
  let U := PrimeSpectrum.basicOpen r
  let c := kernelComparison g (functor R)
  let q := kernel.ι ((functor R).map g)
  change Function.Bijective (c.val.app (op U))
  have hq : Function.Injective (q.val.app (op U)) := by
    let E := _root_.SheafOfModules.evaluation (Spec (.of R)).ringCatSheaf (op U)
    change Function.Injective (E.map q)
    exact (ModuleCat.mono_iff_injective (E.map q)).mp inferInstance
  have hc (x : (kernel g).tilde.val.obj (op U)) :
      q.val.app (op U) (c.val.app (op U) x) = basicOpenMap (kernel.ι g) r x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.val.app (op U)) (kernelComparison_comp_ι g (functor R))) x
  refine ⟨?_, ?_⟩
  · intro x y h
    apply basicOpenMap_injective (kernel.ι g)
      ((ModuleCat.mono_iff_injective (kernel.ι g)).mp inferInstance) r
    rw [← hc x, ← hc y, h]
  · intro y
    have hy : basicOpenMap g r (q.val.app (op U) y) = 0 := by
      exact ConcreteCategory.congr_hom
        (congrArg (fun φ => φ.val.app (op U))
          (kernel.condition ((functor R).map g))) y
    obtain ⟨x, hx⟩ :=
      (basicOpenMap_exact (kernel.ι g) g (moduleKernel_exact g) r
        (q.val.app (op U) y)).mp hy
    exact ⟨x, hq ((hc x).trans hx)⟩

/-- The actual tilde functor preserves the original kernel comparison. -/
theorem kernelComparison_isIso (g : M ⟶ N) :
    IsIso (kernelComparison g (functor R)) :=
  KltDP.SheafOfModules.isIso_of_bijective_on_basis (kernelComparison g (functor R))
    PrimeSpectrum.isBasis_basic_opens (kernelComparison_basicOpen_bijective g)

instance functor_preservesKernel (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0) (functor R) := by
  letI := kernelComparison_isIso g
  exact PreservesKernel.of_iso_comparison (functor R) g

/-- Package the proved canonical comparison on the original sheaf objects. -/
def kernelIso (g : M ⟶ N) : (kernel g).tilde ≅ kernel ((functor R).map g) := by
  letI := kernelComparison_isIso g
  exact asIso (kernelComparison g (functor R))

@[simp]
theorem kernelIso_hom (g : M ⟶ N) :
    (kernelIso g).hom = kernelComparison g (functor R) := rfl

/-- The comparison retains the original inclusion into the source sheaf. -/
@[simp]
theorem kernelIso_hom_ι (g : M ⟶ N) :
    (kernelIso g).hom ≫ kernel.ι ((functor R).map g) = (functor R).map (kernel.ι g) :=
  kernelComparison_comp_ι g (functor R)

end KltDP.Geometry.AffineModuleTilde
