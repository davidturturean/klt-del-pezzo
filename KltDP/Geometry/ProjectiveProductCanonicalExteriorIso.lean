import KltDP.Geometry.ProjectiveProductCanonicalExteriorFrames
import KltDP.Geometry.TransitionUnitExtraction

/-!
# The original exterior square of the sum of two invertible sheaves

Original local trivializations provide actual rank-one section frames on
common subopens. The already defined ordered tensor-to-exterior map is
therefore locally bijective before sheafification. The existing module
sheafification theorem proves that its actual sheaf map is an isomorphism.
No local or global tensor-to-exterior identity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalExteriorIso

open ProjectiveProductCanonicalExteriorMap ProjectiveProductCanonicalExteriorFrames
open TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (L M : InvertibleSheaf X)

local instance exteriorMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem exists_bijective_subopen (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧
      Function.Bijective (sectionsMap L.obj M.obj V) := by
  have hL : x ∈ ⨆ i, L.localTrivializations.X i := by
    rw [invertibleSheafUnits_cover X L]
    trivial
  have hM : x ∈ ⨆ i, M.localTrivializations.X i := by
    rw [invertibleSheafUnits_cover X M]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hL
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hM
  let V := U ⊓ L.localTrivializations.X i ⊓ M.localTrivializations.X j
  refine ⟨V, inf_le_left.trans inf_le_left, ⟨⟨hx, hi⟩, hj⟩, ?_⟩
  exact sectionsMap_bijective L.obj M.obj V
    (chartEquiv X L.obj L.localTrivializations i (inf_le_left.trans inf_le_right))
    (chartEquiv X M.obj M.localTrivializations j inf_le_right)

private abbrev underlyingMap :=
  (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.val).map
    (presheafMap L.obj M.obj)

/-- The original ordered wedge map is locally injective from the actual rank-one atlases. -/
theorem presheafMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (underlyingMap L M) := by
  constructor
  intro U s t h x hx
  obtain ⟨V, hVU, hxV, hb⟩ := exists_bijective_subopen L M U.unop x hx
  refine ⟨V, homOfLE hVU, ?_, hxV⟩
  apply hb.injective
  have hs := ConcreteCategory.congr_hom
    ((underlyingMap L M).naturality (homOfLE hVU).op) s
  have ht := ConcreteCategory.congr_hom
    ((underlyingMap L M).naturality (homOfLE hVU).op) t
  exact hs.trans ((congrArg
    ((SchemeExteriorPower.presheaf (L.obj ⊞ M.obj) 2).presheaf.map
      (homOfLE hVU).op) h).trans ht.symm)

/-- Every original exterior section lifts locally through the original tensor presheaf map. -/
theorem presheafMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (underlyingMap L M) := by
  constructor
  intro U s x hx
  obtain ⟨V, hVU, hxV, hb⟩ := exists_bijective_subopen L M U x hx
  refine ⟨V, homOfLE hVU, ?_, hxV⟩
  exact hb.surjective
    ((SchemeExteriorPower.presheaf (L.obj ⊞ M.obj) 2).map (homOfLE hVU).op s)

/-- The original sheaf tensor-to-exterior map of two invertible sheaves is an isomorphism. -/
theorem map_isIso : IsIso (ProjectiveProductCanonicalExteriorMap.map L.obj M.obj) := by
  have hw : _root_.PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.val) (presheafMap L.obj M.obj) :=
    (_root_.PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mpr
      ⟨presheafMap_isLocallyInjective L M, presheafMap_isLocallySurjective L M⟩
  letI : IsIso ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (presheafMap L.obj M.obj)) :=
    (_root_.PresheafOfModules.sheafificationW_iff _ _).mp hw
  unfold ProjectiveProductCanonicalExteriorMap.map
  infer_instance

/-- The actual exterior-square comparison, with forward map the original ordered wedge. -/
def iso : L.obj ⊗ M.obj ≅ SchemeExteriorPower.sheaf (L.obj ⊞ M.obj) 2 := by
  letI := map_isIso L M
  exact asIso (ProjectiveProductCanonicalExteriorMap.map L.obj M.obj)

@[simp]
theorem iso_hom : (iso L M).hom = ProjectiveProductCanonicalExteriorMap.map L.obj M.obj := rfl

end KltDP.Geometry.ProjectiveProductCanonicalExteriorIso
