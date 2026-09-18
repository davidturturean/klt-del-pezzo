import KltDP.Geometry.BirationalIsomorphismOpen
import KltDP.Geometry.MinimalResolutionCount

/-!
# Exceptional-curve finiteness and descent for actual resolution maps

The original generic stalk map supplies an actual isomorphism open through
the proved spreading-out theorem. Thus neither finiteness of the exceptional
curves nor strict decrease under an actual contraction requires an external
dense-open statement or a separately supplied termination measure.

This advances the finite exceptional configuration and minimalization steps
of Proposition 2.4. It does not construct a resolution or a contraction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

/-- An actual proper birational map between normal projective surfaces has
only finitely many contracted prime curves. Source regularity is unnecessary. -/
theorem exceptionalCurves_finite_of_proper_birational
    {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)
    [IsProper π] (hbir : IsBirationalScheme π) :
    {C : S.PrimeCurve | IsExceptionalCurve π C}.Finite := by
  obtain ⟨V, hV, hViso⟩ := exists_isomorphism_open_of_isBirationalScheme π hbir
  letI : Nonempty V.toScheme := hV
  letI : IsIso (π ∣_ V) := hViso
  obtain ⟨s, hs⟩ := preimage_nonempty_of_isIso_restrict π V
  refine (NormalProjectiveSurface.PrimeCurve.finite_setOf_subset
    (Z := ((π ⁻¹ᵁ V : S.toScheme.Opens) : Set S.toScheme)ᶜ)
    (π ⁻¹ᵁ V).isOpen.isClosed_compl ?_).subset ?_
  · intro h
    have hsZ : s ∈ ((π ⁻¹ᵁ V : S.toScheme.Opens) : Set S.toScheme)ᶜ := by
      rw [h]
      exact Set.mem_univ s
    exact hsZ hs
  · intro C hC t ht htV
    exact IsExceptionalCurve.subset_exceptionalLocus π hC ht ⟨V, htV, hViso⟩

/-- The finite exceptional set is derived from the defining resolution
properties, including its original birational stalk map. -/
theorem IsResolution.exceptionalCurves_finite_of_actualMap
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hπ : IsResolution S X π) :
    {C : S.PrimeCurve | IsExceptionalCurve π C}.Finite := by
  letI : IsProper π := hπ.isProper
  exact exceptionalCurves_finite_of_proper_birational π
    ((isBirational_iff_isBirationalScheme π).mp hπ.birational)

private theorem denseOpenStatement :
    KltDP.Literature.Stacks.BirationalIsoOverDenseOpenLiteral k := by
  constructor
  intro S X π hπ hbir
  letI : IsProper π := isProper_of_comp_structureMorphism π hπ
  obtain ⟨V, hV, hViso⟩ := exists_isomorphism_open_of_isBirationalScheme π
    ((isBirational_iff_isBirationalScheme π).mp hbir)
  exact ⟨V, V.isOpen.dense (Set.nonempty_coe_sort.mp hV), hViso⟩

/-- An actual exceptional-curve contraction strictly lowers the finite
number of exceptional curves over the original target. All dense-open and
finiteness inputs of the existing geometric injection proof are discharged. -/
theorem IsContraction.ncard_exceptionalCurves_lt_of_actualMaps
    {S S' X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    {π' : S'.toScheme ⟶ X.toScheme} (hπ : IsResolution S X π)
    (hπ' : IsResolution S' X π') {b : S.toScheme ⟶ S'.toScheme}
    {E : S.PrimeCurve} (hb : IsContraction S S' b E)
    (hfac : b ≫ π' = π) (hE : IsExceptionalCurve π E) :
    {C' : S'.PrimeCurve | IsExceptionalCurve π' C'}.ncard <
      {C : S.PrimeCurve | IsExceptionalCurve π C}.ncard :=
  hb.ncard_exceptionalCurves_lt denseOpenStatement hπ hπ' hfac hE

end KltDP.Geometry
