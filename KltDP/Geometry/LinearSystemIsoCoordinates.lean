import KltDP.Geometry.LinearSystemNormalizedCoordinates

/-!
# Original section coordinates under an actual invertible-sheaf isomorphism

Evaluating the original sheaf isomorphism and composing with the original
frames gives two linear trivializations of the same module. The existing
transition unit compares all original section coefficients. It therefore
preserves their intrinsic nonvanishing opens and the normalized projective
scaling relation. No coordinate or open compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemNaturality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction TransitionUnitGluing
  InvertibleSectionNonvanishingOpen LinearSystemMorphism

variable {X : Scheme.{u}}

local instance sectionModule (A : X.Modules) (W : X.Opens) :
    Module Γ(X, W) (A.val.obj (op W)) := (A.val.obj (op W)).isModule

private def sectionIso {A B : X.Modules} (e : A ≅ B) (W : X.Opens) :
    A.val.obj (op W) ≃ₗ[Γ(X, W)] B.val.obj (op W) :=
  ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op W)).mapIso e).toLinearEquiv

variable (L M : InvertibleSheaf X) (e : L.obj ≅ M.obj)

/-- The unit comparing the original frames through the original sheaf isomorphism. -/
def isoFrameTransition (i : L.localTrivializations.I) (i' : M.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i)
    (hWi' : W ≤ M.localTrivializations.X i') : Γ(X, W)ˣ :=
  KltDP.Module.transitionUnit
    ((sectionIso e W).trans (chartEquiv X M.obj M.localTrivializations i' hWi'))
    (chartEquiv X L.obj L.localTrivializations i hWi)

/-- Every original section coefficient changes by that same actual unit. -/
theorem coefficient_sectionsMap_iso (s : L.obj.sections)
    (i : L.localTrivializations.I) (i' : M.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i)
    (hWi' : W ≤ M.localTrivializations.X i') :
    coefficient L s i hWi = (isoFrameTransition L M e i i' hWi hWi' : Γ(X, W)) *
      coefficient M (_root_.SheafOfModules.sectionsMap e.hom s) i' hWi' :=
  (KltDP.Module.transitionUnit_mul_apply
    ((sectionIso e W).trans (chartEquiv X M.obj M.localTrivializations i' hWi'))
    (chartEquiv X L.obj L.localTrivializations i hWi) (s.val (op W))).symm

/-- On an original subopen of a frame, the coefficient has precisely the intrinsic open. -/
theorem basicOpen_coefficient (s : L.obj.sections) (i : L.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i) :
    X.basicOpen (coefficient L s i hWi) = W ⊓ nonvanishingOpen X L s := by
  calc
    _ = X.basicOpen (res X hWi (chartCoefficient X L.obj L.localTrivializations s i)) :=
      congrArg (fun a : Γ(X, W) => X.basicOpen a)
        (chartCoefficient_restrict X L.obj L.localTrivializations s i hWi).symm
    _ = W ⊓ X.basicOpen (chartCoefficient X L.obj L.localTrivializations s i) :=
      X.basicOpen_res _ (homOfLE hWi).op
    _ = W ⊓ (L.localTrivializations.X i ⊓ nonvanishingOpen X L s) :=
      congrArg (fun V : X.Opens => W ⊓ V)
        (chart_inf_nonvanishingOpen X L s L.localTrivializations i).symm
    _ = _ := by rw [← inf_assoc, inf_eq_left.mpr hWi]

/-- An actual sheaf isomorphism preserves the original section's intrinsic nonvanishing open. -/
theorem nonvanishingOpen_sectionsMap_iso (s : L.obj.sections) :
    nonvanishingOpen X M (_root_.SheafOfModules.sectionsMap e.hom s) =
      nonvanishingOpen X L s := by
  apply SetLike.ext
  intro x
  have hxL : x ∈ ⨆ i, L.localTrivializations.X i := by
    rw [TransitionUnitExtraction.chartOpens_cover]
    trivial
  have hxM : x ∈ ⨆ i, M.localTrivializations.X i := by
    rw [TransitionUnitExtraction.chartOpens_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxL
  obtain ⟨i', hi'⟩ := Opens.mem_iSup.mp hxM
  let W : X.Opens := L.localTrivializations.X i ⊓ M.localTrivializations.X i'
  have hWi : W ≤ L.localTrivializations.X i := inf_le_left
  have hWi' : W ≤ M.localTrivializations.X i' := inf_le_right
  let a := isoFrameTransition L M e i i' hWi hWi'
  have hc : X.basicOpen (coefficient L s i hWi) =
      X.basicOpen (coefficient M (_root_.SheafOfModules.sectionsMap e.hom s) i' hWi') := by
    rw [coefficient_sectionsMap_iso L M e s i i' hWi hWi', Scheme.basicOpen_mul,
      Scheme.basicOpen_of_isUnit X a.isUnit]
    exact inf_eq_right.mpr (X.basicOpen_le _)
  have hopen : W ⊓ nonvanishingOpen X L s =
      W ⊓ nonvanishingOpen X M (_root_.SheafOfModules.sectionsMap e.hom s) :=
    (basicOpen_coefficient L s i hWi).symm.trans
      (hc.trans (basicOpen_coefficient M (_root_.SheafOfModules.sectionsMap e.hom s) i' hWi'))
  constructor
  · intro hx
    have hxW : x ∈ W ⊓ nonvanishingOpen X M
        (_root_.SheafOfModules.sectionsMap e.hom s) := ⟨⟨hi, hi'⟩, hx⟩
    exact (hopen.symm ▸ hxW).2
  · intro hx
    have hxW : x ∈ W ⊓ nonvanishingOpen X L s := ⟨⟨hi, hi'⟩, hx⟩
    exact (hopen ▸ hxW).2

variable {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

/-- The literal compatible sections transported by the original isomorphism. -/
abbrev isoSections : Fin (n + 1) → M.obj.sections :=
  fun j => _root_.SheafOfModules.sectionsMap e.hom (s j)

/-- Their actual nonvanishing opens cover whenever the original section opens do. -/
theorem isoSections_cover (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) :
    (⨆ j, nonvanishingOpen X M (isoSections L M e s j)) = ⊤ :=
  (iSup_congr (fun j => nonvanishingOpen_sectionsMap_iso L M e (s j))).trans hcover

/-- The unchanged normalized coordinates obey the original projective scaling identity. -/
theorem coordinates_sectionsMap_iso_scale
    (i : L.localTrivializations.I) (i' : M.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i)
    (hWi' : W ≤ M.localTrivializations.X i') (m m' : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m))
    (hWm' : W ≤ nonvanishingOpen X M (isoSections L M e s m')) (j : Fin (n + 1)) :
    coordinates L s i hWi m hWm j =
      coordinates L s i hWi m hWm m' *
        coordinates M (isoSections L M e s) i' hWi' m' hWm' j := by
  apply (coefficient_isUnit L (s m) i hWi hWm).mul_left_cancel
  rw [denominator_mul_coordinates, ← mul_assoc, denominator_mul_coordinates]
  rw [coefficient_sectionsMap_iso L M e (s j) i i' hWi hWi',
    coefficient_sectionsMap_iso L M e (s m') i i' hWi hWi', mul_assoc]
  change (isoFrameTransition L M e i i' hWi hWi' : Γ(X, W)) *
      coefficient M (isoSections L M e s j) i' hWi' =
    (isoFrameTransition L M e i i' hWi hWi' : Γ(X, W)) *
      (coefficient M (isoSections L M e s m') i' hWi' *
        coordinates M (isoSections L M e s) i' hWi' m' hWm' j)
  exact congrArg (fun a : Γ(X, W) =>
    (isoFrameTransition L M e i i' hWi hWi' : Γ(X, W)) * a)
    (denominator_mul_coordinates M (isoSections L M e s) i' hWi' m' hWm' j).symm

end KltDP.Geometry.LinearSystemNaturality
