import KltDP.Geometry.KltResolutionExceptionalGenusZero
import KltDP.Geometry.GenusZeroCurveProjectiveLineMap
import KltDP.Geometry.ProperNonconstantCurveFieldFinite

/-!
# Finite degree-one projective-line maps for actual exceptional curves

The original resolution and target klt property produce arithmetic genus
zero for each original contracted prime. The original-curve construction
then supplies a regular Cartier point, its complete linear system, and a
proper nonconstant map to the actual projective line. The proved curve
finiteness theorem applies to this same map. Its pullback of the original
degree-one sheaf has actual Euler degree one.

No point, Cartier divisor, genus, curve smoothness, map, degree, finiteness,
or projective-line isomorphism is an input. The final degree-one isomorphism
step is separate. The existing isolated Hodge, Riemann--Roch and Stein
dependencies remain visible.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open ModuleCohomology

/-- An original exceptional curve has an actual finite degree-one map to
P1, with all point and linear-system choices produced internally. -/
theorem IsResolution.exceptional_exists_finite_projectiveLine_map_of_klt
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hres : IsResolution S X π)
    (hklt : IsKlt X) (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) :
    ∃ g : C.toScheme ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = C.toSpec ∧ IsFinite g ∧
      eulerCharacteristic C.toSpec (pullbackInvertibleSheaf g
          (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj -
        eulerCharacteristic C.toSpec
          (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) = 1 := by
  letI := C.toSpec_isProper
  have hgenus := hres.exceptional_arithmetic_genus_zero_of_klt hklt C hC
  obtain ⟨g, hg, hproper, hdegree, hnonconstant⟩ :=
    GenusZeroCurveProjectiveLineMap.exists_proper_morphism_with_degree_one
      C.toSpec C.dimension_one_toScheme hgenus
  letI : IsProper g := hproper
  have hfinite : IsFinite g :=
    ProperNonconstantCurve.isFinite_of_not_factors_through_structure
      C.toSpec (projectiveSpaceToSpec k 1) g hg C.dimension_one_toScheme.le hnonconstant
  exact ⟨g, hg, hfinite, hdegree⟩

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.exceptional_exists_finite_projectiveLine_map_of_klt
#print axioms KltDP.Geometry.IsResolution.exceptional_exists_finite_projectiveLine_map_of_klt
