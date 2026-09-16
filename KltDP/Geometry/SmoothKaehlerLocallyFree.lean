/-
Original project adapter developed for KltDelPezzoLean.
Released under Apache 2.0; see the source and license bindings in
docs/reuse_sources/smooth_kaehler_locally_free/source_bindings.json.
-/
import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineModuleTildeFiniteType
import KltDP.Geometry.SchemeKaehlerOpenRestriction
import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.ModuleOpenOverEquivalence
import KltDP.Geometry.SmoothFieldCharts
import KltDP.Geometry.FiniteLocallyFreeCoherent
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Finite local bases of the original smooth differential sheaf

A standard-smooth algebra supplies a basis of its actual Kähler module.
The original tilde comparison carries this basis to the actual global
differential sheaf on its spectrum. On a standard-smooth affine open of
an original scheme, restriction along the original affine-chart
isomorphism transports this free sheaf back to the actual open.

The scalar map is exactly `baseToAffineSectionsMap`, and its composition
with the original chart is proved equal to the original structure map.
The existing differential restriction isomorphism and the existing
open-to-Over comparison then give literal finite local bases.

For a smooth scheme over a field the required charts follow from pinned
scheme smoothness. Local ranks may vary. No regularity, numerical rank,
canonical divisor, or dualizing object is supplied or asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.SmoothKaehlerLocallyFree

open SchemeKaehlerSheaf SchemeKaehlerOpenRestriction SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- Reuse the accepted concrete sheafification instances on each original open
-- site, so the Over-site adjunction is not rediscovered by typeclass search.
-- They are local to their accepted module, so they are re-declared here as
-- local instances with the accepted declarations as bodies.
local instance laneOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  schemeOverHasWeakSheafify X U

local instance laneOverWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} :=
  schemeOverWEqualsLocallyBijective X U

section Affine

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- An actual finite Kähler basis gives an isomorphism from the original
coproduct free sheaf to the original differential sheaf on the spectrum. -/
def affineFreeIsoOfBasis {I : Type u} [Finite I]
    (b : Basis I A (KaehlerDifferential k A)) :
    _root_.SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅
      baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  (AffineModuleTilde.freeCoproductIso A I).symm ≪≫
    (AffineModuleTilde.functor A).mapIso (AffineModuleTilde.finiteCoproductIsoPi A I) ≪≫
    AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of A (I → A))
      (N := AffineKaehlerTildeDerivation.differentialModule k A) b.equivFun.symm ≪≫
    (AffineKaehlerTildeLocalization.iso k A).symm

/-- Standard smoothness supplies both the actual differential basis and
the finiteness of its index type. This also retains the zero-ring case. -/
def standardSmoothAffineFreeIso [Algebra.IsStandardSmooth k A] :
    _root_.SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf)
      (Module.Free.ChooseBasisIndex A (KaehlerDifferential k A)) ≅
        baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  affineFreeIsoOfBasis k A (Module.Free.chooseBasis A (KaehlerDifferential k A))

end Affine

section Charts

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual standard-smooth chart gives a finite free basis on the
original open subscheme. The basis size is supplied by its Kähler module. -/
theorem exists_standardSmooth_open_freeIso {U : X.Opens} (hU : IsAffineOpen U)
    (hs : RingHom.IsStandardSmooth (baseToAffineSectionsMap f hU).hom) :
    ∃ I : Type u, Finite I ∧ Nonempty
      (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (restriction U.ι).obj (baseRingSheaf f)) := by
  let A := Γ(X, U)
  letI : Algebra k A := (baseToAffineSectionsMap f hU).hom.toAlgebra
  letI : Algebra.IsStandardSmooth k A := hs.toAlgebra
  let I := Module.Free.ChooseBasisIndex A (KaehlerDifferential k A)
  let j := hU.isoSpec.hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hj : j ≫ g = U.ι ≫ f := by
    change hU.isoSpec.hom ≫ Spec.map (baseToAffineSectionsMap f hU) = U.ι ≫ f
    rw [Spec_map_baseToAffineSectionsMap f hU, ← Category.assoc,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
  letI : PreservesColimitsOfSize.{u, u} (restriction j) :=
    (restrictionAdjunction j).leftAdjoint_preservesColimits
  let e₀ : _root_.SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅
      baseRingSheaf g := standardSmoothAffineFreeIso k A
  let e₁ : _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (restriction j).obj (baseRingSheaf g) :=
    _root_.SheafOfModules.mapFreeIso (restriction j) I (restrictionUnitIso j).symm ≪≫
      (restriction j).mapIso e₀
  let e₂ : baseRingSheaf (j ≫ g) ≅ baseRingSheaf (U.ι ≫ f) :=
    eqToIso (congrArg baseRingSheaf hj)
  exact ⟨I, inferInstance, ⟨e₁ ≪≫ restrictionIso g j ≪≫ e₂ ≪≫
    (restrictionIso f U.ι).symm⟩⟩

end Charts

section SmoothField

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) [IsSmooth f]

/-- Every point has an actual finite free differential basis on an
original affine open, obtained from scheme smoothness over the field. -/
theorem exists_affine_open_freeIso (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ I : Type u, Finite I ∧ Nonempty
        (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
          (restriction U.ι).obj (baseRingSheaf f)) := by
  obtain ⟨U, hU, hx, hs⟩ := isSmooth_field_exists_affine_standardSmooth f x
  exact ⟨U, hU, hx, exists_standardSmooth_open_freeIso f hU hs⟩

/-- The original global differential sheaf has actual finite local
bases in the original Over-site language. No basis data is assumed. -/
theorem exists_finite_localBases :
    ∃ q : (baseRingSheaf f).LocalGeneratorsData,
      q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I := by
  classical
  choose U hU hx I hI e using exists_affine_open_freeIso f
  let eO (x : X) :
      _root_.SheafOfModules.free (R := X.ringCatSheaf.over (U x)) (I x) ≅
        (baseRingSheaf f).over (U x) :=
    openToOverFreeIso (U x) (I x) ≪≫
      (openToOverFunctor (U x)).mapIso (Classical.choice (e x)) ≪≫
      openToOverRestrictionIso (U x) (baseRingSheaf f)
  let q : (baseRingSheaf f).LocalGeneratorsData := {
    I := X
    X := U
    coversTop := by
      intro W x hxW
      exact ⟨W ⊓ U x, homOfLE inf_le_left,
        ⟨x, ⟨homOfLE inf_le_right⟩⟩, ⟨hxW, hx x⟩⟩
    generators x :=
      (_root_.SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (U x)) (I x)).ofEpi (eO x).hom }
  refine ⟨q, ⟨?_⟩, ?_⟩
  · intro x
    change IsIso ((_root_.SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) (I x)).ofEpi (eO x).hom).π
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_π]
    infer_instance
  · intro x
    exact hI x

/-- Smoothness over a field makes the original differential sheaf
locally free. The conclusion permits the genuine local ranks to vary. -/
theorem isLocallyFree :
    _root_.SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) (baseRingSheaf f) := by
  obtain ⟨q, hq, _⟩ := exists_finite_localBases f
  exact ⟨q, hq⟩

/-- The same actual local bases prove finite type of the original sheaf. -/
theorem isFiniteType : (baseRingSheaf f).IsFiniteType := by
  obtain ⟨q, _, hq⟩ := exists_finite_localBases f
  exact ⟨q, hq⟩

end SmoothField

end KltDP.Geometry.SmoothKaehlerLocallyFree
