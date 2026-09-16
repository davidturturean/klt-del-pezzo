import KltDP.Geometry.RationalTreePicardRestrictionPullbackSections
import KltDP.Geometry.RationalTreePicardLeafNodeCover
import KltDP.Geometry.RationalTreePicardMultidegree
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Picard classes on a clopen decomposition: the restriction homomorphism is injective

BRIEF23, task 1 (injectivity half). Let `X = U ⊔ V` with `U`, `V` disjoint opens covering `X`.
A module sheaf `M` on `X` whose pullbacks to `U` and to `V` are trivial has an atlas of pullback
charts on the two-element cover `{U, V}` (the accepted `localTrivializationsOfOpenCharts` with
`openChartOfPullback`); its transition unit on the overlap `U ⊓ V = ⊥` lives in the subsingleton
ring `Γ(X, ⊥)` and the diagonal units are `1` (`IsCocycle.unit_self`), so the extracted cocycle is
gauge-equivalent to the constant cocycle by the trivial gauge and the accepted `unitIsoOfGauge`
gives `M ≅ O_X` (`unitIsoOfClopen`). Hence a Picard class of `X` restricting trivially to `U` and
to `V` is trivial (`toPic_eq_one_of_clopen`), i.e. the restriction homomorphism
`restrictionHom U V : X.Pic →* U.Pic × V.Pic` is injective (`restrictionHom_injective`).
Surjectivity is the separate module `PicardClopenSurjective`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.PicardClopen

open KltDP.Geometry KltDP.Geometry.RationalTreePicard SchemeModuleRestriction
  TransitionUnitExtraction TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (U V : X.Opens)

/-- The two-element cover `{U, V}`, indexed in universe `u`. -/
def cover : ULift.{u} Bool → X.Opens
  | ⟨true⟩ => U
  | ⟨false⟩ => V

theorem cover_true : cover U V ⟨true⟩ = U := rfl

theorem cover_false : cover U V ⟨false⟩ = V := rfl

theorem cover_exists (hcov : ∀ x : X, x ∈ U ∨ x ∈ V) (x : X) : ∃ i, x ∈ cover U V i := by
  rcases hcov x with h | h
  · exact ⟨⟨true⟩, h⟩
  · exact ⟨⟨false⟩, h⟩

theorem cover_inf_eq_bot_of_ne (hdisj : U ⊓ V = ⊥) :
    ∀ (i j : ULift.{u} Bool), i ≠ j → cover U V i ⊓ cover U V j = ⊥
  | ⟨true⟩, ⟨true⟩, h => absurd rfl h
  | ⟨true⟩, ⟨false⟩, _ => hdisj
  | ⟨false⟩, ⟨true⟩, _ => (inf_comm V U).trans hdisj
  | ⟨false⟩, ⟨false⟩, h => absurd rfl h

variable (M : X.Modules)
  (tU : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf)
  (tV : (schemeModulePullback V.ι).obj M ≅ _root_.SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- The two pullback trivializations, indexed by the cover. -/
def trivializations : ∀ i : ULift.{u} Bool,
    (schemeModulePullback (cover U V i).ι).obj M ≅
      _root_.SheafOfModules.unit (cover U V i).toScheme.ringCatSheaf
  | ⟨true⟩ => tU
  | ⟨false⟩ => tV

/-- The atlas of `M` on the cover `{U, V}` given by the two pullback trivializations. -/
def atlas (hcov : ∀ x : X, x ∈ U ∨ x ∈ V) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M :=
  localTrivializationsOfOpenCharts M (cover U V) (cover_exists U V hcov)
    (fun i => openChartOfPullback M (cover U V i) (trivializations U V M tU tV i))

/-- The transition units of the atlas are gauge-equivalent to the constant cocycle by the trivial
gauge: the diagonal units are `1`, the off-diagonal ones live in `Γ(X, U ⊓ V) = Γ(X, ⊥)`. -/
theorem atlas_isGauge (hdisj : U ⊓ V = ⊥) (hcov : ∀ x : X, x ∈ U ∨ x ∈ V) :
    IsGauge X (cover U V) (transitionUnits X M (atlas U V M tU tV hcov))
      (oneUnits X (cover U V)) (fun _ => 1) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    have h := (transitionUnits_isCocycle X M (atlas U V M tU tV hcov)).unit_self i
    simp only [Units.val_one, map_one, one_mul, mul_one, oneUnits]
    exact h
  · haveI : Subsingleton Γ(X, cover U V i ⊓ cover U V j) :=
      subsingleton_sections_of_eq_bot (cover_inf_eq_bot_of_ne U V hdisj i j hij)
    exact Subsingleton.elim _ _

/-- **A module sheaf trivial on both pieces of a clopen decomposition is trivial.** -/
def unitIsoOfClopen (hdisj : U ⊓ V = ⊥) (hcov : ∀ x : X, x ∈ U ∨ x ∈ V) :
    M ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  unitIsoOfGauge (X := X) (M := M) (t := atlas U V M tU tV hcov) (fun _ => 1)
    (atlas_isGauge U V M tU tV hdisj hcov)

/-- A Picard class restricting trivially to both pieces of a clopen decomposition is trivial. -/
theorem toPic_eq_one_of_clopen (hdisj : U ⊓ V = ⊥) (hcov : ∀ x : X, x ∈ U ∨ x ∈ V)
    (L : InvertibleSheaf X) (hU : schemePicardPullbackHom U.ι L.toPic = 1)
    (hV : schemePicardPullbackHom V.ι L.toPic = 1) : L.toPic = 1 := by
  rw [schemePicardPullbackHom_toPic, toPic_eq_one_iff_iso_unit] at hU hV
  obtain ⟨eU⟩ := hU
  obtain ⟨eV⟩ := hV
  exact (toPic_eq_one_iff_iso_unit L).mpr ⟨unitIsoOfClopen U V L.obj eU eV hdisj hcov⟩

/-- The restriction homomorphism of a clopen decomposition. -/
def restrictionHom : X.Pic →* U.toScheme.Pic × V.toScheme.Pic :=
  (schemePicardPullbackHom U.ι).prod (schemePicardPullbackHom V.ι)

theorem restrictionHom_apply (c : X.Pic) :
    restrictionHom U V c = (schemePicardPullbackHom U.ι c, schemePicardPullbackHom V.ι c) := rfl

/-- **Injectivity of the restriction homomorphism of a clopen decomposition.** -/
theorem restrictionHom_injective (hdisj : U ⊓ V = ⊥) (hcov : ∀ x : X, x ∈ U ∨ x ∈ V) :
    Function.Injective (restrictionHom U V) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨L, rfl⟩ := toPic_surjective c
  have h1 : schemePicardPullbackHom U.ι L.toPic = 1 := congrArg Prod.fst hc
  have h2 : schemePicardPullbackHom V.ι L.toPic = 1 := congrArg Prod.snd hc
  exact toPic_eq_one_of_clopen U V hdisj hcov L h1 h2

/-- Universe check at universe `0`. -/
example {X₀ : Scheme.{0}} (U₀ V₀ : X₀.Opens) (hdisj : U₀ ⊓ V₀ = ⊥)
    (hcov : ∀ x : X₀, x ∈ U₀ ∨ x ∈ V₀) : Function.Injective (restrictionHom U₀ V₀) :=
  restrictionHom_injective U₀ V₀ hdisj hcov

end KltDP.Geometry.PicardClopen
