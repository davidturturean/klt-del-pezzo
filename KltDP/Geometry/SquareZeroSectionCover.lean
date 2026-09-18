import KltDP.Geometry.SquareZeroMembersDisjoint
import KltDP.Geometry.IndependentSectionWeilMembers
import KltDP.Geometry.EffectiveCartierNonvanishing
import KltDP.Geometry.InvertibleSectionNonvanishingIso
import KltDP.Geometry.RegularCartierIdealSupport

/-! The two independent original sections of O(F) have nonvanishing
opens covering the whole original surface. All divisors, section-preserving
isomorphisms, and support disjointness are produced from those sections. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
open InvertibleSectionNonvanishingOpen

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance sectionCoverIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The original independent pair itself has no base point; there is
no supplied nonvanishing cover or generatedness assumption. -/
theorem independent_sections_cover_of_nef_squareZero (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (s : Fin 2 → sections (cartierDivisorModule X.toScheme F))
    (hs : letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme F)
      LinearIndependent k s) :
    (⨆ i : Fin 2, nonvanishingOpen X.toScheme (cartierDivisorInvertibleSheaf X.toScheme F)
      (schemeModuleSectionOfTop (cartierDivisorModule X.toScheme F) (s i))) = ⊤ := by
  obtain ⟨E, hE, e, he, hlinear, hne⟩ :=
    X.exists_distinct_effectiveCartier_members_of_independent hX F s hs
  have hEff (i : Fin 2) : EffectiveDivisor (X.cartierToWeilHom (E i)) :=
    X.effective_cartierToWeilHom_of_regularEquations (E i) (hE i)
  have hdisj := X.effectiveMembers_disjoint_of_nef_squareZero hX K eK F hF hFF hKF
    (X.cartierToWeilHom (E 0)) (X.cartierToWeilHom (E 1))
    (hEff 0) (hEff 1) (hlinear 0) (hlinear 1) hne
  have hsupport (i : Fin 2) :
      ((effectiveCartierIdealDataOfRegularEquations X.toScheme (E i) (hE i)).support :
        Set X.toScheme) = divisorSupport (X.cartierToWeilHom (E i)) := by
    letI := X.stalks_uniqueFactorizationMonoid_of_regular hX
    exact X.regularCartierIdealData_support (E i) (hEff i)
  let c (i : Fin 2) := schemeModuleSectionOfTop (cartierDivisorModule X.toScheme (E i))
    (effectiveCartierSection X.toScheme (E i) (hE i))
  have htop (M : X.toScheme.Modules) (t : M.val.obj (op (⊤ : X.toScheme.Opens))) :
      (schemeModuleSectionOfTop M t).val (op (⊤ : X.toScheme.Opens)) = t :=
    (schemeModuleSectionsEquivTop M).apply_symm_apply t
  have hc (i : Fin 2) : _root_.SheafOfModules.sectionsMap (e i).hom (c i) =
      schemeModuleSectionOfTop (cartierDivisorModule X.toScheme F) (s i) := by
    apply (schemeModuleSectionsEquivTop (cartierDivisorModule X.toScheme F)).injective
    change (e i).hom.val.app (op (⊤ : X.toScheme.Opens))
      ((schemeModuleSectionOfTop (cartierDivisorModule X.toScheme (E i))
        (effectiveCartierSection X.toScheme (E i) (hE i))).val (op (⊤ : X.toScheme.Opens))) =
      (schemeModuleSectionOfTop (cartierDivisorModule X.toScheme F) (s i)).val
        (op (⊤ : X.toScheme.Opens))
    rw [htop, htop, he i]
  have hopen (i : Fin 2) := nonvanishingOpen_sectionsMap_iso
    (cartierDivisorInvertibleSheaf X.toScheme (E i))
    (cartierDivisorInvertibleSheaf X.toScheme F) (e i) (c i)
  apply top_unique
  intro x _
  have hoff : ∃ i : Fin 2,
      x ∉ (effectiveCartierIdealDataOfRegularEquations X.toScheme (E i) (hE i)).support := by
    by_cases hx : x ∈ divisorSupport (X.cartierToWeilHom (E 0))
    · refine ⟨1, ?_⟩
      change x ∉ ((effectiveCartierIdealDataOfRegularEquations X.toScheme (E 1)
        (hE 1)).support : Set X.toScheme)
      rw [hsupport 1]
      exact fun hx' => Set.disjoint_left.mp hdisj hx hx'
    · refine ⟨0, ?_⟩
      change x ∉ ((effectiveCartierIdealDataOfRegularEquations X.toScheme (E 0)
        (hE 0)).support : Set X.toScheme)
      rwa [hsupport 0]
  obtain ⟨i, hi⟩ := hoff
  refine Opens.mem_iSup.mpr ⟨i, ?_⟩
  have hni := hopen i
  rw [hc i] at hni
  rw [hni]
  exact (effectiveCartierSection_mem_nonvanishing_iff X.toScheme (E i) (hE i) x).mpr hi

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.independent_sections_cover_of_nef_squareZero
#print axioms KltDP.Geometry.NormalProjectiveSurface.independent_sections_cover_of_nef_squareZero
