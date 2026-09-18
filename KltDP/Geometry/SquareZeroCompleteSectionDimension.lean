import KltDP.Geometry.LineSectionPointEvaluation
import KltDP.Geometry.SquareZeroSectionCover
import KltDP.Geometry.SquareZeroNefSections
import KltDP.Geometry.ProperInvertibleSectionBasis
import KltDP.Geometry.ClosedPoints
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The complete original square-zero system has exactly two sections.
Evaluation at an actual closed rational point has one-dimensional target.
Two independent kernel sections would contradict their proved original
nonvanishing cover, so rank-nullity gives h0 at most two. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
open InvertibleSectionNonvanishingOpen LineSectionPointEvaluation

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance completeDimensionIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The entire original section space has dimension at most two. -/
theorem squareZero_hZero_le_two (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 0 ≤ 2 := by
  let L := cartierDivisorInvertibleSheaf X.toScheme F
  letI := baseSectionsModule X.structureMorphism L.obj
  letI := CompleteLinearSystemSections.topSections_finiteDimensional X.structureMorphism L
  letI : JacobsonSpace X.toScheme := LocallyOfFiniteType.jacobsonSpace X.structureMorphism
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X.toScheme).Nonempty) isOpen_univ.isLocallyClosed
  let i := closedPointSection X.structureMorphism x hx
  have hi : i ≫ X.structureMorphism = 𝟙 _ :=
    closedPointSection_over_base X.structureMorphism x hx
  let φ : sections L.obj →ₗ[k] k := evaluation X.structureMorphism i hi L
  have hk : Module.finrank k (LinearMap.ker φ) ≤ 1 := by
    by_contra hn
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
      (show 2 ≤ Module.finrank k (LinearMap.ker φ) by omega)
    let s : Fin 2 → sections L.obj := fun j => (v j).val
    have hs : LinearIndependent k s := by
      exact hv.map' (LinearMap.ker φ).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hcover := X.independent_sections_cover_of_nef_squareZero hX K eK F hF hFF hKF s hs
    have hmem : fieldMorphismPoint i ∈ (⨆ j : Fin 2,
        nonvanishingOpen X.toScheme L (schemeModuleSectionOfTop L.obj (s j))) := by
      change (⨆ j : Fin 2, nonvanishingOpen X.toScheme L
        (schemeModuleSectionOfTop L.obj (s j))) = ⊤ at hcover
      exact hcover.symm ▸ (show fieldMorphismPoint i ∈ (⊤ : X.toScheme.Opens) from trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hmem
    exact not_mem_nonvanishing_of_evaluation_eq_zero X.structureMorphism i hi L (s j)
      (show φ (s j) = 0 from (v j).property) hj
  have hr : Module.finrank k (LinearMap.range φ) ≤ 1 := by
    simpa only [Module.finrank_self] using (LinearMap.range φ).finrank_le
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [cohomologyDimension_zero_eq_finrank_sections]
  change Module.finrank k (sections L.obj) ≤ 2
  omega

include eK in
/-- Rational-surface RR and actual point evaluation give the exact
complete-system dimension and the vanishing of its first cohomology. -/
theorem squareZero_hZero_eq_two_and_hOne_eq_zero
    (hrational : Scheme.BirationalOver X.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 0 = 2 ∧
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 1 = 0 := by
  have hle := X.squareZero_hZero_le_two hX K eK F hF hFF hKF
  have heq := X.squareZero_hZero_eq_hOne_add_two hX K eK hrational F hF hFF hKF
  omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_hZero_eq_two_and_hOne_eq_zero
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_hZero_eq_two_and_hOne_eq_zero
