import KltDP.Geometry.AffineModuleChartDenominators
import KltDP.Geometry.AffineModuleDenominatorDescent
import KltDP.Geometry.AffineModuleCounitIsomorphism

/-!
# Affine reconstruction of an original invertible sheaf

Refine the actual trivializing cover by basic opens and use compactness
of Spec R to choose a finite subcover. The original chart isomorphisms
prove denominator extension on each member, and the finite-cover gluing
theorem proves it globally. Thus the original counit is an isomorphism.
No global trivialization or affine reconstruction is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]

/-- Actual local rank-one trivializations imply global denominator extension on Spec R. -/
theorem denominatorExtension_top_of_localTrivializations
    (M : (Spec (.of R)).Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := (Spec (.of R)).ringCatSheaf) M) :
    DenominatorExtension M ⊤ := by
  classical
  have hpoint (x : PrimeSpectrum R) :
      ∃ (i : t.I) (g : R), x ∈ PrimeSpectrum.basicOpen g ∧
        PrimeSpectrum.basicOpen g ≤ t.X i := by
    have hx : x ∈ ⨆ i, t.X i := by
      rw [TransitionUnitExtraction.chartOpens_cover (Spec (.of R)) M t]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨_, ⟨g, rfl⟩, hxg, hgi⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (t.X i).isOpen
    exact ⟨i, g, hxg, hgi⟩
  choose i g hx hgi using hpoint
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isCompact_basicOpen (1 : R)).elim_finite_subcover
    (fun x : PrimeSpectrum R => (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have hcover : (⊤ : (Spec (.of R)).Opens) =
      ⨆ x : s, PrimeSpectrum.basicOpen (g x) := by
    apply le_antisymm
    · intro x _
      have hxone : x ∈ PrimeSpectrum.basicOpen (1 : R) := by simp
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hs hxone)
      obtain ⟨hys, hxy⟩ := Set.mem_iUnion.mp hy
      exact Opens.mem_iSup.mpr ⟨⟨y, hys⟩, hxy⟩
    · exact le_top
  apply DenominatorExtension.of_finite_basicOpen_cover M ⊤ (fun x : s => g x) hcover
  intro x
  exact denominatorExtension_basicOpen_of_chart M t (i x) (g x) (hgi x)

/-- The original affine counit is an isomorphism for an actual locally trivial rank-one sheaf. -/
theorem counit_isIso_of_localTrivializations
    (M : (Spec (.of R)).Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := (Spec (.of R)).ringCatSheaf) M) :
    IsIso (counit M) :=
  counit_isIso_of_denominatorExtension M (denominatorExtension_top_of_localTrivializations M t)

/-- An original invertible sheaf is the tilde sheaf of its original global-section module. -/
def invertibleCounitIso (L : InvertibleSheaf (Spec (.of R))) :
    (sectionModule L.obj ⊤).tilde ≅ L.obj := by
  letI := counit_isIso_of_localTrivializations L.obj L.localTrivializations
  exact asIso (counit L.obj)

@[simp]
theorem invertibleCounitIso_hom (L : InvertibleSheaf (Spec (.of R))) :
    (invertibleCounitIso L).hom = counit L.obj := rfl

/-- Affine reconstruction retains the original restriction of every global section. -/
theorem invertibleCounitIso_hom_toOpen (L : InvertibleSheaf (Spec (.of R)))
    (U : (Spec (.of R)).Opens) (s : sectionModule L.obj ⊤) :
    (invertibleCounitIso L).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (sectionModule L.obj ⊤) U s) =
      L.obj.val.map (homOfLE le_top).op s :=
  counit_toOpen L.obj U s

end KltDP.Geometry.AffineModuleTilde
