/-
Original pinned-API adapter for the affine finite-section argument in
Vilin97/MazurTheorem at 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleQuasicoherent.lean:1380-1443. Released under Apache 2.0.
The original section rings and modules are retained, using the accepted
denominator-extension and power-zero theorems for their localization.
-/
import KltDP.Geometry.AffineOpenFiniteGenerators
import KltDP.Geometry.QuasicoherentSectionPowerZero
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite original sections of finite-type quasicoherent sheaves

Local finite generating families yield finite sections on every original
affine open. The basic opens lying inside those actual generating charts
cover the affine open. Their defining functions span the unit ideal, so
the pinned localization finiteness theorem applies to the original
restriction maps. No global finite generators are assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineFiniteTypeSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- Use the explicit pinned dictionaries already compiled for these same
-- original Over sites in CoherentQuasicoherent and FiniteLocallyFreeCoherent.
local instance schemeOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance schemeOverWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

variable {X : Scheme.{u}} (M : X.Modules)

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

local instance basicSectionModule {U : X.Opens} (f : Γ(X, U)) :
    Module Γ(X, U) (M.val.obj (op (X.basicOpen f))) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

/-- The actual original restriction, linear over the original ambient ring. -/
def basicRestrictionLinear {U : X.Opens} (f : Γ(X, U)) :
    M.val.obj (op U) →ₗ[Γ(X, U)] M.val.obj (op (X.basicOpen f)) where
  toFun := M.val.map (homOfLE (X.basicOpen_le f)).op
  map_add' := (M.val.map (homOfLE (X.basicOpen_le f)).op).hom.map_add
  map_smul' r t := M.val.map_smul (homOfLE (X.basicOpen_le f)).op r t

/-- The original restriction to an intrinsic basic open is the actual
localized module map. Its two denominator laws were proved separately. -/
theorem basicRestriction_isLocalized [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule (Submonoid.powers f) (basicRestrictionLinear M f) where
  map_units s := by
    obtain ⟨n, hn⟩ := s.property
    rw [← hn, map_pow]
    apply IsUnit.pow
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun t : M.val.obj (op (X.basicOpen f)) =>
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op f • t)
    exact (RingedSpace.isUnit_res_basicOpen X.toRingedSpace f).smul_bijective
  surj' s := by
    obtain ⟨n, t, ht⟩ := AffineOpenModule.exists_restrict_eq_pow_smul hU M f s
    exact ⟨(t, ⟨f ^ n, n, rfl⟩), ht.symm⟩
  exists_of_eq {s t} hst := by
    obtain ⟨n, hn⟩ := QuasicoherentSectionPowerZero.exists_pow_smul_eq_of_isCompact
      M hU.isCompact f s t hst
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩

-- Keep localization finiteness independent of the chosen generator
-- cover, so its kernel check sees abstract finite-section witnesses.
private theorem sections_finite_of_basic_cover [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (t : Set Γ(X, U))
    (ht : Ideal.span t = ⊤)
    (hfinite : ∀ g : t,
      Module.Finite Γ(X, X.basicOpen g.1) (M.val.obj (op (X.basicOpen g.1)))) :
    Module.Finite Γ(X, U) (M.val.obj (op U)) := by
  letI (g : t) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) :=
    hU.isLocalization_basicOpen g.1
  letI (g : t) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g.1)
      (M.val.obj (op (X.basicOpen g.1))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI (g : t) : IsLocalizedModule (Submonoid.powers g.1)
      (basicRestrictionLinear M g.1) := basicRestriction_isLocalized M hU g.1
  exact Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t => M.val.obj (op (X.basicOpen g.1)))
    (Rₚ := fun g : t => Γ(X, X.basicOpen g.1))
    t ht (fun g => basicRestrictionLinear M g.1) hfinite

private theorem sections_finite_of_localGenerators [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    (q : M.LocalGeneratorsData) (hq : ∀ i : q.I, Finite (q.generators i).I) :
    Module.Finite Γ(X, U) (M.val.obj (op U)) := by
  let t : Set Γ(X, U) := {f | ∃ i, X.basicOpen f ≤ q.X i}
  have hopen : ⨆ f : t, X.basicOpen f.1 = U := by
    apply le_antisymm
    · exact iSup_le fun f => X.basicOpen_le f.1
    · intro x hx
      obtain ⟨W, j, ⟨i, ⟨g⟩⟩, hxW⟩ := q.coversTop (⊤ : X.Opens) x trivial
      have hxi : x ∈ q.X i := g.le hxW
      obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxi⟩ hx
      exact (le_iSup (fun f : t => X.basicOpen f.1) ⟨f, i, hf⟩) hxf
  apply sections_finite_of_basic_cover M hU t
    ((hU.basicOpen_union_eq_self_iff t).mp hopen)
  intro g
  obtain ⟨i, hi⟩ := g.2
  letI : Finite (q.generators i).I := hq i
  exact AffineOpenFiniteGenerators.sections_finite_of_over_generators_of_le M hi
    (hU.basicOpen g.1) (q.generators i)

/-- Every original affine open has a finite original module of sections
for a quasicoherent sheaf of finite type. -/
theorem sections_finite [M.IsQuasicoherent] [M.IsFiniteType]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) (M.val.obj (op U)) := by
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  exact sections_finite_of_localGenerators M hU q hq

end KltDP.Geometry.AffineFiniteTypeSections
