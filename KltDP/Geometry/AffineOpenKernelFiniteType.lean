/-
Original project adapter composing actual finite-module generators and
original scheme/Over-site equivalences. Released under Apache 2.0; see
docs/reuse_sources/affine_open_kernel/sources/LICENSE.
-/
import KltDP.Geometry.SchemeModuleIso
import KltDP.Geometry.ModuleOpenOverEquivalence
import KltDP.Geometry.AffineFreeKernelFiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Actual finite-type kernels on affine opens of locally Noetherian schemes

For an arbitrary original finite-free-to-unit map on the Over site of an
actual affine open, recover its map on the open subscheme and then on
`Spec Γ(X, U)` through the original scheme isomorphism. The actual affine
module kernel has finite generators. Transporting their original finite-free
epimorphism back gives an epimorphism onto the original Over-site kernel.

The given section family is not required to generate the unit sheaf. Only
the section ring of the actual affine open is asserted Noetherian. This
is the affine-open kernel leaf; the all-open cover assembly and literal
coherence condition remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace AffineModuleTilde

/-- The actual affine kernel has a global finite-free epimorphism. This
retains the generator map, so it can be transported through equivalences. -/
theorem exists_finite_free_epi_kernel_free_to_unit
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf) :
    ∃ (n : ℕ)
      (p : _root_.SheafOfModules.free
        (R := (Spec (.of R)).ringCatSheaf) (ULift.{u} (Fin n)) ⟶ kernel φ),
      Epi p := by
  letI := finiteFreeModuleMap_kernel_finite R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv)
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi R
    (kernel (finiteFreeModuleMap R I (ModuleCat.of R R) (φ ≫ (unitIso R).inv)))
  letI : Epi p := hp
  exact ⟨n, p ≫ (freeToUnitKernelIso R I φ).hom, inferInstance⟩

end AffineModuleTilde

/-- Every actual finite-free-to-unit map on an affine open has an actual
finite-free epimorphism onto its original Over-site kernel. The map is
recovered through the canonical `IsAffineOpen.isoSpec`, not assumed to
come from a module map. -/
theorem exists_finite_free_epi_kernel_on_affineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U)
    (I : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ (n : ℕ)
      (p : _root_.SheafOfModules.free
        (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶ kernel φ),
      Epi p := by
  let R := Γ(X, U)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let e : Spec (.of R) ≅ U.toScheme := hU.isoSpec.symm
  let φ₁ := openToOverFreeToUnitPreimage U I φ
  let φ₂ := schemeIsoFreeToUnitPreimage e I φ₁
  obtain ⟨n, p, hp⟩ :=
    AffineModuleTilde.exists_finite_free_epi_kernel_free_to_unit R I φ₂
  letI : Epi p := hp
  let p₁ := (schemeIsoFreeIso e (ULift.{u} (Fin n))).hom ≫
    (schemeModulePushforward e.hom).map p ≫ (schemeIsoFreeToUnitKernelIso e I φ₁).hom
  letI : Epi p₁ := inferInstanceAs (Epi
    ((schemeIsoFreeIso e (ULift.{u} (Fin n))).hom ≫
      (schemeModulePushforward e.hom).map p ≫ (schemeIsoFreeToUnitKernelIso e I φ₁).hom))
  let p₂ := (openToOverFreeIso U (ULift.{u} (Fin n))).hom ≫
    (openToOverFunctor U).map p₁ ≫ (openToOverFreeToUnitKernelIso U I φ).hom
  exact ⟨n, p₂, inferInstanceAs (Epi
    ((openToOverFreeIso U (ULift.{u} (Fin n))).hom ≫
      (openToOverFunctor U).map p₁ ≫ (openToOverFreeToUnitKernelIso U I φ).hom))⟩

/-- The original kernel on an actual affine open is finite type, in the
pinned sense of finite local generator families on the original Over site. -/
theorem isFiniteType_kernel_free_to_unit_on_affineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U)
    (I : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    _root_.SheafOfModules.IsFiniteType (kernel φ) := by
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi_kernel_on_affineOpen U hU I φ
  letI : Epi p := hp
  letI : HasBinaryProducts (Over U) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
      (C := X.Opens) (B := U)
  exact _root_.SheafOfModules.isFiniteType_of_free_epi
    (R := X.ringCatSheaf.over U) (M := kernel φ)
    (I := ULift.{u} (Fin n)) (p := p)

end KltDP.Geometry
