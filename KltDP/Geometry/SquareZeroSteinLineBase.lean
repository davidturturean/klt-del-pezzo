import KltDP.Geometry.SquareZeroProjectiveLineFactor
import KltDP.Geometry.ProperSteinConnected
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian

/-! For the original complete square-zero map, an actual P1 comparison
of its Stein base forces the SAME finite factor to be an isomorphism.
Thus the original map itself has the original structure-sheaf isomorphism
and all geometrically connected fibers. The base comparison is explicit
until its independent actual geometric producer is applied. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

private theorem genericPointPreserving_of_surjective
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [Surjective f] : GenericPointPreserving f := by
  constructor
  apply IsGenericPoint.eq _ (genericPoint_spec Z)
  simpa only [Set.image_univ, f.surjective.range_eq, closure_univ] using
    (genericPoint_spec Y).image f.continuous

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance steinLineBaseIntegral : IsIntegral X.toScheme := X.integral
local instance steinLineBaseTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include eK in
/-- The actual P1 Stein base and original pullback line force the finite
factor to be an isomorphism; connectedness holds on the original map. -/
theorem squareZero_stein_factor_isIso_of_base_iso
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1) [IsProper π] [Surjective π]
    (e : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F)
    {B : Scheme.{u}} (f : X.toScheme ⟶ B) (g : B ⟶ projectiveSpace k 1)
    [IsIso f.c] [IsFinite g] (hfg : f ≫ g = π)
    (eB : B ≅ projectiveSpace k 1)
    (heB : eB.hom ≫ projectiveSpaceToSpec k 1 = g ≫ projectiveSpaceToSpec k 1) :
    IsIso g ∧ IsIso π.c ∧
      ∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ projectiveSpace k 1),
        ConnectedSpace (pullback π q : Scheme.{u}) := by
  let f' := f ≫ eB.hom
  let g' := eB.inv ≫ g
  have hfg' : f' ≫ g' = π := by
    dsimp [f', g']
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hfg
  have hg' : g' ≫ projectiveSpaceToSpec k 1 = projectiveSpaceToSpec k 1 := by
    dsimp [g']
    rw [Category.assoc, ← heB, Iso.inv_hom_id_assoc]
  let e' : (pullbackInvertibleSheaf (f' ≫ g')
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F :=
    eqToIso (congrArg (fun t : X.toScheme ⟶ projectiveSpace k 1 =>
      (schemeModulePullback t).obj (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1).obj) hfg') ≪≫ e
  letI : Surjective (f ≫ g) := by rw [hfg]; infer_instance
  letI : Surjective g := Surjective.of_comp f g
  letI : Surjective g' := by dsimp [g']; infer_instance
  letI : IsFinite g' := by dsimp [g']; infer_instance
  letI : GenericPointPreserving g' := genericPointPreserving_of_surjective g'
  letI : IsIso g' :=
    X.squareZero_projectiveLine_factor_isIso hX K eK F hFF hKF f' g' hg' e'
  have hgg' : g = eB.hom ≫ g' := by
    dsimp [g']
    rw [Iso.hom_inv_id_assoc]
  letI : IsIso g := by rw [hgg']; infer_instance
  letI : IsIso g.c := PresheafedSpace.c_isIso_of_iso g.toPshHom
  have hc : IsIso π.c := by
    rw [← hfg]
    change IsIso (g.c ≫ (TopCat.Presheaf.pushforward CommRingCat g.base).map f.c)
    infer_instance
  letI := hc
  letI : IsLocallyNoetherian (projectiveSpace k 1) :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec (projectiveSpaceToSpec k 1)
  exact ⟨inferInstance, hc, ProperSteinConnected.geometrically_connected π⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_stein_factor_isIso_of_base_iso
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_stein_factor_isIso_of_base_iso
