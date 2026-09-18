import KltDP.Geometry.ProjectiveHomogeneousSectionCoordinates
import KltDP.Geometry.ProjectiveCoordinateTupleMorphism
import KltDP.Geometry.LinearSystemMorphism

/-!
# The original homogeneous-coordinate linear system is the identity

The original chosen-atlas coordinates equal the actual standard coordinate
fractions. Each original affine chart map is therefore its original map
to projective space. The existing gluing uniqueness proves equality of the
unchanged linear-system morphism with the identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveCoordinateLinearSystem

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing LinearSystemMorphism ProjectiveSpaceDegreeOneSheaf
  ProjectiveCoordinateSectionBasicOpen

variable (k : Type u) [Field k] (n : ℕ)

/-- The original morphism of the original homogeneous sections of O(1) is the identity. -/
theorem morphism_homogeneousSection :
    LinearSystemMorphism.morphism (degreeOne k n) (homogeneousSection k n)
      (projectiveSpaceToSpec k n) (homogeneousSection_cover k n) =
        𝟙 (projectiveSpace k n) := by
  apply (LinearSystemMorphism.chartCover (degreeOne k n) (homogeneousSection k n)
    (homogeneousSection_cover k n)).hom_ext
  intro c
  change c.affineOpen.2.fromSpec ≫
      LinearSystemMorphism.morphism (degreeOne k n) (homogeneousSection k n)
        (projectiveSpaceToSpec k n) (homogeneousSection_cover k n) =
    c.affineOpen.2.fromSpec ≫ 𝟙 (projectiveSpace k n)
  rw [chart_morphism, Category.comp_id]
  let hstd := le_standardOpen_of_homogeneousSection k n c.index c.nonvanishing
  let r : Fin (n + 1) → Γ(projectiveSpace k n, c.affineOpen.1) :=
    coordinates (degreeOne k n) (homogeneousSection k n)
      c.frame c.inFrame c.index c.nonvanishing
  let r' : Fin (n + 1) → Γ(projectiveSpace k n, c.affineOpen.1) :=
    fun j => res (projectiveSpace k n) hstd (coordinateSection k n c.index j)
  have hr : r = r' := funext fun j =>
    coordinates_homogeneousSection k n c.frame c.inFrame c.index c.nonvanishing j
  let a := (baseToAffineSectionsMap (projectiveSpaceToSpec k n) c.affineOpen.2).hom
  have hm : r c.index = 1 :=
    coordinates_self (degreeOne k n) (homogeneousSection k n)
      c.frame c.inFrame c.index c.nonvanishing
  have hm' : r' c.index = 1 :=
    ProjectiveCoordinateTupleMorphism.coordinateTuple_self k n c.index hstd
  have hr' : (⟨r, hm⟩ : {q : Fin (n + 1) → Γ(projectiveSpace k n, c.affineOpen.1) //
      q c.index = 1}) = ⟨r', hm'⟩ := Subtype.ext hr
  have ht := congrArg
    (fun q : {q : Fin (n + 1) → Γ(projectiveSpace k n, c.affineOpen.1) // q c.index = 1} =>
      ProjectiveChart.tupleMorphism n a q.val c.index q.property) hr'
  change ProjectiveChart.tupleMorphism n a r c.index hm = c.affineOpen.2.fromSpec
  exact ht.trans (ProjectiveCoordinateTupleMorphism.tupleMorphism_eq_fromSpec
    k n c.affineOpen.2 c.index hstd)

end KltDP.Geometry.ProjectiveCoordinateLinearSystem
