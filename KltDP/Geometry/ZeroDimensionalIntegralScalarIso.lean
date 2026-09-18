import KltDP.Geometry.ZeroDimensionalBigness
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! A zero-dimensional integral scheme is affine. If its original global
scalar map is an isomorphism, its original structure map is an isomorphism. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ZeroDimensionalIntegralScalarIso

variable {X : Scheme.{u}} [IsIntegral X]

theorem isAffine (hdim : topologicalKrullDim X = 0) : IsAffine X := by
  letI : Subsingleton X := ZeroDimensionalBigness.subsingleton_of_dimension_zero hdim
  let x : X := genericPoint X
  have htop : (X.affineCover.map x).opensRange = ⊤ := by
    apply le_antisymm le_top
    intro y _
    simpa only [Subsingleton.elim y x] using X.affineCover.covers x
  letI : IsIso (X.affineCover.map x) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  exact IsAffine.of_isIso (asIso (X.affineCover.map x)).inv

theorem structureMap_isIso {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (hdim : topologicalKrullDim X = 0)
    [IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop)] : IsIso f := by
  letI : IsAffine X := isAffine hdim
  letI : IsIso f.appTop := IsIso.of_isIso_comp_left
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv f.appTop
  exact (HasAffineProperty.iff_of_isAffine
    (P := MorphismProperty.isomorphisms Scheme) (f := f)).mpr
      ⟨inferInstance, inferInstance⟩

#print axioms isAffine
#print axioms structureMap_isIso

end KltDP.Geometry.ZeroDimensionalIntegralScalarIso
