/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from MazurTorsion/Upstream/DivisorLineBundle.lean, revision
9327963d4ec14fba49c7b14b004fd00707ffc2e9, lines 481–623.
The existing KltDP sheaf tensor and reflective sheafification comparisons
replace the upstream AINTLIB wrappers. The local-injectivity argument also
uses the pinned basic-open pattern in AffineKaehlerTildeLocalization.
-/
import KltDP.Geometry.AffineModuleTildeTensorMap
import KltDP.Geometry.SheafPicard

/-!
# Tilde of the original module tensor is the actual sheaf tensor

The canonical fractional-section tensor map is locally bijective, by its
proved principal-open equivalences. Sheafification therefore identifies
tilde of the original module tensor with the tensor of the original tilde
sheaves. No tensor comparison, affine reconstruction, or local freeness is
assumed. Naturality under base change and its common-chart applications to
global adjunction remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTildeTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)

local instance sheafMonoidal : MonoidalCategory (Spec (CommRingCat.of R)).Modules :=
  Scheme.Modules.monoidalCategory (Spec (CommRingCat.of R))

private abbrev underlyingMap :=
  (_root_.PresheafOfModules.toPresheaf (Spec (CommRingCat.of R)).ringCatSheaf.val).map
    (presheafMap M N)

private theorem locallyInjective_of_basicOpen
    {P Q : (Opens (PrimeSpectrum R))ᵒᵖ ⥤ AddCommGrp.{u}} (α : P ⟶ Q)
    (hα : ∀ r : R, Function.Injective (α.app (op (PrimeSpectrum.basicOpen r)))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (PrimeSpectrum R)) α := by
  constructor
  intro U s t h x hx
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.unop.isOpen
  refine ⟨PrimeSpectrum.basicOpen r, homOfLE hrU, ?_, hxr⟩
  change P.map (homOfLE hrU).op s = P.map (homOfLE hrU).op t
  apply hα r
  have hs := ConcreteCategory.congr_hom (α.naturality (homOfLE hrU).op) s
  have ht := ConcreteCategory.congr_hom (α.naturality (homOfLE hrU).op) t
  exact hs.trans ((congrArg (Q.map (homOfLE hrU).op) h).trans ht.symm)

/-- Local injectivity is detected on the original principal-open basis. -/
theorem presheafMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
      (underlyingMap M N) :=
  locallyInjective_of_basicOpen _
    (fun f => (sectionsMap_basicOpen_bijective M N f).injective)

/-- Every original target section lifts locally through the actual tensor map. -/
theorem presheafMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec (CommRingCat.of R)))
      (underlyingMap M N) := by
  constructor
  intro U s x hx
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨PrimeSpectrum.basicOpen f, homOfLE hfU, ?_, hxf⟩
  exact (sectionsMap_basicOpen_bijective M N f).surjective
    ((tensorModule M N).tilde.val.map (homOfLE hfU).op s)

/-- The actual tensor presheaf map is inverted by the original module sheafification. -/
theorem presheafMap_mem_sheafificationW :
    PresheafOfModules.sheafificationW
      (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.val) (presheafMap M N) :=
  (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mpr
    ⟨presheafMap_isLocallyInjective M N, presheafMap_isLocallySurjective M N⟩

/-- The canonical map after sheafification, before the original tensor/counit comparisons. -/
def sheafifiedMap :=
  (PresheafOfModules.sheafification (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.val)).map
    (presheafMap M N)

theorem sheafifiedMap_isIso : IsIso (sheafifiedMap M N) :=
  (PresheafOfModules.sheafificationW_iff _ _).mp (presheafMap_mem_sheafificationW M N)

/-- The canonical affine tilde tensor comparison on the original module sheaves. -/
def iso : (tensorModule M N).tilde ≅ M.tilde ⊗ N.tilde := by
  letI := sheafifiedMap_isIso M N
  exact (PresheafOfModules.sheafTensorIsoSheafification
      (Spec (CommRingCat.of R)).sheaf.val (Spec (CommRingCat.of R)).ringCatSheaf.cond
      M.tilde N.tilde ≪≫
    asIso (sheafifiedMap M N) ≪≫
    PresheafOfModules.sheafificationForgetIso
      (Spec (CommRingCat.of R)).ringCatSheaf (tensorModule M N).tilde).symm

end KltDP.Geometry.AffineModuleTildeTensor
