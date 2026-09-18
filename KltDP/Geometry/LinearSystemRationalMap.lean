import KltDP.Geometry.LinearSystemDegreeOnePullback
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import Mathlib.AlgebraicGeometry.RationalMap

/-!
# The actual partial and rational maps of a finite tuple of original sections

The specified sections generate on their original non-base open. Pulling the
original line and sections to that open gives the actual projective morphism
and the original degree-one pullback isomorphism. On an integral source, a
nonempty non-base open is dense, so the existing Mathlib partial-map and
rational-map constructions apply. No generation on the whole source and no
complete-system or birationality assertion is imposed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemRationalMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

/-- The original non-base open of exactly the specified finite tuple. -/
def nonBaseOpen : X.Opens := ⨆ i, nonvanishingOpen X L (s i)

/-- The original line pulled back to its actual non-base open. -/
abbrev restrictedLine : InvertibleSheaf (nonBaseOpen L s).toScheme :=
  pullbackInvertibleSheaf (nonBaseOpen L s).ι L

/-- The literal original pullback of each specified compatible section. -/
abbrev restrictedSections : Fin (n + 1) → (restrictedLine L s).obj.sections :=
  fun i => InvertibleSheafSectionPowersPullback.pullbackSection
    (nonBaseOpen L s).ι L.obj (s i)

/-- These original pulled section opens cover precisely the non-base scheme. -/
theorem restrictedSections_cover :
    (⨆ i, nonvanishingOpen (nonBaseOpen L s).toScheme (restrictedLine L s)
      (restrictedSections L s i)) = ⊤ := by
  calc
    _ = ⨆ i, (nonBaseOpen L s).ι ⁻¹ᵁ nonvanishingOpen X L (s i) :=
      iSup_congr (fun i => InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
        (nonBaseOpen L s).ι L (s i))
    _ = (nonBaseOpen L s).ι ⁻¹ᵁ nonBaseOpen L s :=
      ((nonBaseOpen L s).ι.preimage_iSup (fun i => nonvanishingOpen X L (s i))).symm
    _ = ⊤ := (nonBaseOpen L s).ι_preimage_self

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual morphism of the original tuple on its actual non-base open. -/
def morphism : (nonBaseOpen L s).toScheme ⟶ projectiveSpace k n :=
  LinearSystemMorphism.morphism (restrictedLine L s) (restrictedSections L s)
    ((nonBaseOpen L s).ι ≫ f) (restrictedSections_cover L s)

/-- The map preserves the original field structure restricted to the non-base open. -/
theorem morphism_structure :
    morphism L s f ≫ projectiveSpaceToSpec k n = (nonBaseOpen L s).ι ≫ f :=
  LinearSystemMorphism.morphism_structure (restrictedLine L s) (restrictedSections L s)
    ((nonBaseOpen L s).ι ≫ f) (restrictedSections_cover L s)

/-- The actual projective degree-one sheaf pulls back to the original restricted line. -/
def pullbackDegreeOneIso :
    (pullbackInvertibleSheaf (morphism L s f) (ProjectiveSpaceDegreeOneSheaf.degreeOne k n)).obj ≅
      (pullbackInvertibleSheaf (nonBaseOpen L s).ι L).obj :=
  LinearSystemPullback.pullbackDegreeOneIso (restrictedLine L s) (restrictedSections L s)
    ((nonBaseOpen L s).ι ≫ f) (restrictedSections_cover L s)

/-- Each standard chart pulls back to the corresponding original section open. -/
theorem morphism_preimage_coordinateChart (i : Fin (n + 1)) :
    morphism L s f ⁻¹ᵁ (ProjectiveChart.coordinateChartMorphism k n i).opensRange =
      (nonBaseOpen L s).ι ⁻¹ᵁ nonvanishingOpen X L (s i) :=
  (LinearSystemMorphism.morphism_preimage_coordinateChart
    (restrictedLine L s) (restrictedSections L s) ((nonBaseOpen L s).ι ≫ f)
    (restrictedSections_cover L s) i).trans
      (InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
        (nonBaseOpen L s).ι L (s i))

variable [IsIntegral X]

/-- A nonempty original non-base open is dense in the integral source. -/
theorem nonBaseOpen_dense (hU : (nonBaseOpen L s : Set X).Nonempty) :
    Dense (nonBaseOpen L s : Set X) := (nonBaseOpen L s).2.dense hU

/-- The original finite tuple as Mathlib's existing partial map. -/
def partialMap (hU : (nonBaseOpen L s : Set X).Nonempty) :
    X.PartialMap (projectiveSpace k n) where
  domain := nonBaseOpen L s
  dense_domain := nonBaseOpen_dense L s hU
  hom := morphism L s f

/-- Its domain is exactly the original union of nonvanishing section opens. -/
theorem partialMap_domain (hU : (nonBaseOpen L s : Set X).Nonempty) :
    (partialMap L s f hU).domain = nonBaseOpen L s := rfl

/-- The original finite tuple as Mathlib's existing rational-map class. -/
def rationalMap (hU : (nonBaseOpen L s : Set X).Nonempty) : X ⤏ projectiveSpace k n :=
  (partialMap L s f hU).toRationalMap

/-- The original rational map is over the original field, as an equality
of the existing rational-map classes. -/
theorem rationalMap_structure (hU : (nonBaseOpen L s : Set X).Nonempty) :
    (rationalMap L s f hU).compHom (projectiveSpaceToSpec k n) = f.toRationalMap := by
  change ((partialMap L s f hU).compHom (projectiveSpaceToSpec k n)).toRationalMap =
    f.toPartialMap.toRationalMap
  apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
  refine ⟨nonBaseOpen L s, nonBaseOpen_dense L s hU, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_refl (nonBaseOpen L s)) ≫
      (morphism L s f ≫ projectiveSpaceToSpec k n) =
    X.homOfLE (show nonBaseOpen L s ≤ ⊤ from le_top) ≫ (X.topIso.hom ≫ f)
  rw [Scheme.homOfLE_rfl, Category.id_comp, Scheme.topIso_hom,
    ← Category.assoc, Scheme.homOfLE_ι]
  exact morphism_structure L s f

end KltDP.Geometry.LinearSystemRationalMap
