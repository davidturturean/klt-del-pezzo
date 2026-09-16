import KltDP.Geometry.RationalTreePicardStalkTransport
import KltDP.Geometry.RationalTreePicardProjectiveLine

/-!
# Chart exponents under isomorphisms, and their realization

BRIEF14, steps 1 and 2. The chart exponent of an invertible sheaf on a scheme identified with the
projective line depends only on the isomorphism class of the sheaf (`chartExponent_congr_iso`) and
is invariant under pulling back along an isomorphism of the base with the composed identification
(`chartExponent_pullback_iso`). Consequently the component exponents of the restriction of a line
bundle to a closed union of components are the original exponents of the corresponding original
components (`componentExponent_componentUnionRestriction`, generalizing the `= 0` transfer of the
leaf induction), and every integer is a chart exponent on a scheme identified with `P^1`
(`exists_chartExponent_eq`, from the lane's `monomialLineBundle`) and a component exponent on a
curve with a single component (`exists_componentExponent_eq_of_subsingleton`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

section ChartExponent

variable (k : Type u) [Field k]

/-- The chart exponent depends only on the isomorphism class of the sheaf. -/
theorem chartExponent_congr_iso {Y : Scheme.{u}} (e : Y ≅ projectiveSpace k 1)
    (M N : InvertibleSheaf Y) (i : M.obj ≅ N.obj) : chartExponent k e M = chartExponent k e N :=
  ProjectiveLineSheafExponent.exponent_eq_of_iso k _ _ ((schemeModulePullback e.inv).mapIso i)

/-- The chart exponent is invariant under pulling back along an isomorphism of the base, with the
composed identification. -/
theorem chartExponent_pullback_iso {Y Y' : Scheme.{u}} (φ : Y' ≅ Y) (e : Y ≅ projectiveSpace k 1)
    (M : InvertibleSheaf Y) :
    chartExponent k (φ ≪≫ e) (pullbackInvertibleSheaf φ.hom M) = chartExponent k e M := by
  apply ProjectiveLineSheafExponent.exponent_eq_of_iso
  have h : (φ ≪≫ e).inv ≫ φ.hom = e.inv := by
    rw [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (schemeModulePullbackCompIso (φ ≪≫ e).inv φ.hom).app M.obj ≪≫
    eqToIso (congrArg (fun m => (schemeModulePullback m).obj M.obj) h)

/-- Every integer is a chart exponent on a scheme identified with the projective line. -/
theorem exists_chartExponent_eq {Y : Scheme.{u}} (e : Y ≅ projectiveSpace k 1) (d : ℤ) :
    ∃ M : InvertibleSheaf Y, chartExponent k e M = d :=
  ⟨pullbackInvertibleSheaf e.hom (monomialLineBundle k d),
    (ProjectiveLineSheafExponent.exponent_eq_of_iso k _ _
      (pullbackInvPullbackIso e.symm (monomialLineBundle k d).obj)).trans
      (monomialLineBundle_exponent k d)⟩

end ChartExponent

section ComponentExponent

variable (k : Type u) [Field k] {X : Scheme.{u}} [NoetherianSpace X]

/-- The component exponent depends only on the isomorphism class of the sheaf. -/
theorem componentExponent_congr_iso (S : Set ↥(irreducibleComponents X))
    (e : componentUnionScheme X S ≅ projectiveSpace k 1) (M N : InvertibleSheaf X)
    (i : M.obj ≅ N.obj) : componentExponent k X S e M = componentExponent k X S e N :=
  chartExponent_congr_iso k e _ _ ((schemeModulePullback (componentUnionInclusion X S)).mapIso i)

/-- The component exponents of the restriction of a line bundle to a closed union of components
are the original component exponents of the corresponding original components. -/
theorem componentExponent_componentUnionRestriction (S : Set ↥(irreducibleComponents X))
    (ident : ComponentUnionIdentification X S)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (L : InvertibleSheaf X) (D' : ↥(irreducibleComponents (componentUnionScheme X S))) :
    componentExponent k (componentUnionScheme X S) {D'} (ident.projectiveLineIso e D')
        (componentUnionRestriction X S L) =
      componentExponent k X {componentImage X S D'} (e (componentImage X S D')) L := by
  unfold componentExponent ComponentUnionIdentification.projectiveLineIso
  rw [← chartExponent_pullback_iso k (ident.iso D') (e (componentImage X S D'))
    (componentUnionRestriction X {componentImage X S D'} L)]
  apply chartExponent_congr_iso
  exact (schemeModulePullbackCompIso (componentUnionInclusion (componentUnionScheme X S) {D'})
      (componentUnionInclusion X S)).app L.obj ≪≫
    eqToIso (congrArg (fun m => (schemeModulePullback m).obj L.obj) (ident.iso_hom_over D').symm) ≪≫
    ((schemeModulePullbackCompIso (ident.iso D').hom
      (componentUnionInclusion X {componentImage X S D'})).app L.obj).symm

/-- On a reduced curve with a single component identified with the projective line, every integer
is a component exponent. -/
theorem exists_componentExponent_eq_of_subsingleton [AlgebraicGeometry.IsReduced X]
    [Subsingleton ↥(irreducibleComponents X)] (C : ↥(irreducibleComponents X))
    (e : componentUnionScheme X {C} ≅ projectiveSpace k 1) (d : ℤ) :
    ∃ L : InvertibleSheaf X, componentExponent k X {C} e L = d := by
  haveI := surjective_componentUnionInclusion_of_subsingleton X C
  haveI : IsIso (componentUnionInclusion X {C}) :=
    isIso_of_isClosedImmersion_of_surjective (componentUnionInclusion X {C})
  obtain ⟨M, hM⟩ := exists_chartExponent_eq k e d
  refine ⟨pullbackInvertibleSheaf (inv (componentUnionInclusion X {C})) M, ?_⟩
  unfold componentExponent
  rw [← hM]
  apply chartExponent_congr_iso
  exact pullbackInvPullbackIso (asIso (componentUnionInclusion X {C})) M.obj

end ComponentExponent

end KltDP.Geometry.RationalTreePicard
