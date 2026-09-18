import KltDP.Geometry.RuledSurfaceNumericsConditional
import KltDP.Literature.Hartshorne.RuledSurfacePicard
import KltDP.Literature.Hartshorne.RuledSurfaceGenus

/-!
# Numerical invariants of the original ruled surface

The complete root-reviewed V.2.3 and V.2.5 literals instantiate the preserved
full-hypothesis ordinary consumer. The original surface, base curve, ruled
morphism, all closed scheme fibres, and section are unchanged.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.RuledSurfaceNumerics

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1)
  (hCreg : ∀ y : C, RegularPoint C y)
  (π : X.toScheme ⟶ C)
  (hbase : π ≫ c = X.structureMorphism)
  (hsurj : Function.Surjective π.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : π.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 =
        π.fiberι y ≫ X.structureMorphism)
  (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C)

include hCdim hCreg hbase hsurj hfib hσ in
/-- The original ruled surface has its rank, canonical square and Noether
sum expressed using the original scalar first cohomology of its unit sheaf. -/
theorem invariants
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2) :
    X.picardRank = 2 ∧
      X.intersectionPairing hX K K =
        8 * (1 - (cohomologyDimension X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 : ℤ)) ∧
      X.intersectionPairing hX K K + (X.picardRank : ℤ) =
        10 - 8 * (cohomologyDimension X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 : ℤ) :=
  RuledSurfaceNumericsConditional.invariants
    KltDP.Literature.Hartshorne.ruled_surface_picard_literal
    KltDP.Literature.Hartshorne.ruled_surface_genus_literal
    X hX C c hCdim hCreg π hbase hsurj hfib σ hσ K eK

include hX hCdim hCreg hbase hsurj hfib hσ in
/-- The original structure-sheaf Euler characteristic is one minus its
original scalar first cohomology dimension. -/
theorem eulerCharacteristic_eq_one_sub_h1 :
    eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) =
      1 - (cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 : ℤ) := by
  have hg := KltDP.Literature.Hartshorne.ruled_surface_genus_literal
    k X hX C c hCdim hCreg π hbase hsurj hfib σ hσ
  have hpa := hg.1
  rw [← hg.2.2] at hpa
  omega

end KltDP.Geometry.RuledSurfaceNumerics

#check @KltDP.Geometry.RuledSurfaceNumerics.invariants
#print axioms KltDP.Geometry.RuledSurfaceNumerics.invariants
#check @KltDP.Geometry.RuledSurfaceNumerics.eulerCharacteristic_eq_one_sub_h1
#print axioms KltDP.Geometry.RuledSurfaceNumerics.eulerCharacteristic_eq_one_sub_h1
