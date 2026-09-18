import KltDP.Geometry.LinearSystemImageAmple
import KltDP.Geometry.AmplePositivity
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite pullback of the actual projective image line

The constructed projective coordinate sections already give a finite
affine nonvanishing cover. Pulling them along the composite of an actual
finite map and an actual closed projective embedding proves ampleness
of the original composite pullback. The original pullback composition
isomorphism identifies it with the requested iterated pullback.

The actual schematic-image line is literally this closed-embedding
pullback of degree one. Its finite pullback is therefore ample without
an added cover, frame, or ampleness-comparison premise. The general
finite-pullback theorem from an abstract Serre-ample input is not claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace KltDP.Geometry.FinitePullbackImageLineAmple

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

local instance (T : Scheme.{u}) : MonoidalCategory T.Modules :=
  Scheme.Modules.monoidalCategory T

open ProjectiveSpaceDegreeOneSheaf InvertibleSectionNonvanishingOpen

/-- Finite pullback preserves ampleness of the actual line supplied by a closed embedding. -/
theorem finite_pullback_degreeOne_isAmple (k : Type u) [Field k] (n : ℕ)
    {Y Z : Scheme.{u}} (π : Z ⟶ Y) [IsFinite π]
    (i : Y ⟶ projectiveSpace k n) [IsClosedImmersion i] :
    AmpleSerre.IsAmple
      (pullbackInvertibleSheaf π (pullbackInvertibleSheaf i (degreeOne k n))) := by
  letI : NoetherianSpace (projectiveSpace k n) := projectiveSpace_noetherianSpace k n
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ i)
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ i)
  have ha : AmpleSerre.IsAmple (pullbackInvertibleSheaf (π ≫ i) (degreeOne k n)) := by
    apply AffinePullbackOfNonvanishingCoverAmple.isAmple_pullback_of_finite_cover
      (π ≫ i) (degreeOne k n) isCompact_univ isQuasiSeparated_univ
      (fun j : ULift.{u} (Fin (n + 1)) => homogeneousSection k n j.down)
    · intro j
      rw [nonvanishingOpen_homogeneousSection]
      exact Proj.isAffineOpen_basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X j.down)
        (ProjectiveChart.coordinate_mem k n j.down) Nat.one_pos
    · intro x hx
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((chart_cover k n).ge hx)
      exact Opens.mem_iSup.mpr ⟨j, by rwa [nonvanishingOpen_homogeneousSection]⟩
  apply AmplePositivity.isAmple_of_toPic_eq ?_ ha
  apply Units.ext
  change toSkeleton ((schemeModulePullback (π ≫ i)).obj (degreeOne k n).obj) =
    toSkeleton ((schemeModulePullback π).obj ((schemeModulePullback i).obj (degreeOne k n).obj))
  exact Quotient.sound ⟨((schemeModulePullbackCompIso π i).app (degreeOne k n).obj).symm⟩

/-- The original line on the actual schematic image remains ample after an actual finite map. -/
theorem finite_pullback_imageLine_isAmple {k : Type u} [Field k] {X Z : Scheme.{u}}
    (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
    (f : X ⟶ Spec (CommRingCat.of k))
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    (π : Z ⟶ SchematicImageGlued.image (LinearSystemMorphism.morphism L s f hcover))
    [IsFinite π] :
    AmpleSerre.IsAmple
      (pullbackInvertibleSheaf π (LinearSystemMorphism.imageLine L s f hcover)) :=
  finite_pullback_degreeOne_isAmple k n π
    (SchematicImageGlued.inclusion (LinearSystemMorphism.morphism L s f hcover))

end KltDP.Geometry.FinitePullbackImageLineAmple
