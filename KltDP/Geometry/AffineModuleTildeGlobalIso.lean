import KltDP.Geometry.AffineModuleTildeLocalization

/-!
# Original global sections of an affine tilde sheaf

The pinned canonical map M → Γ(Spec R, M̃) is an isomorphism. Both
injectivity and surjectivity follow from the proved basic-open localization
statements at f = 1. The isomorphism keeps the original canonical section
of every module element.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- The original canonical map to all global sections is injective. -/
theorem toOpen_top_injective : Function.Injective (ModuleCat.Tilde.toOpen M ⊤) := by
  have h : Function.Injective
      (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen (1 : R))) := by
    intro m n hmn
    obtain ⟨k, hk⟩ := toOpen_eq_imp_exists_pow_smul_eq M (1 : R) m n hmn
    simpa only [one_pow, one_smul] using hk
  exact (congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) =>
    Function.Injective (ModuleCat.Tilde.toOpen M U))
      (PrimeSpectrum.basicOpen_one (R := R))).mp h

/-- Every original global section of M̃ is the canonical section of a module element. -/
theorem toOpen_top_surjective : Function.Surjective (ModuleCat.Tilde.toOpen M ⊤) := by
  have h : Function.Surjective
      (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen (1 : R))) := by
    intro s
    obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_toOpen M (1 : R) s
    exact ⟨m, by simpa only [one_pow, one_smul] using hm.symm⟩
  exact (congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) =>
    Function.Surjective (ModuleCat.Tilde.toOpen M U))
      (PrimeSpectrum.basicOpen_one (R := R))).mp h

instance toOpen_top_isIso : IsIso (ModuleCat.Tilde.toOpen M ⊤) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨toOpen_top_injective M, toOpen_top_surjective M⟩

/-- The original global-section comparison, with its original R-module structure. -/
def isoTop : M ≅ M.tildeInModuleCat.obj (op ⊤) :=
  asIso (ModuleCat.Tilde.toOpen M ⊤)

@[simp]
theorem isoTop_hom : (isoTop M).hom = ModuleCat.Tilde.toOpen M ⊤ := rfl

@[simp]
theorem isoTop_hom_apply (m : M) :
    (isoTop M).hom m = ModuleCat.Tilde.toOpen M ⊤ m := rfl

end KltDP.Geometry.AffineModuleTilde
