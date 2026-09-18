import KltDP.Geometry.SquareZeroSteinLineBase
import KltDP.Geometry.KltIsotropicMapBase
import KltDP.Geometry.FiniteProjectiveLineCurveGeometry
import KltDP.Geometry.SteinTargetIntegral
import KltDP.Geometry.GeometricConnectedFiberTopology
import KltDP.Geometry.NefNullCurveNegativeSquare
import KltDP.Literature.SteinFactorizationNoetherian

/-! The original square-zero pencil on a rank-one klt del Pezzo resolution
has geometrically connected fibers. The complete Stein factorization is
constructed from the reviewed full theorem. Its original intermediate
curve is integral, normal, regular, proper and one-dimensional by ordinary
producers. The actual klt exceptional curves identify that base with P1;
primitivity then makes the SAME finite factor an isomorphism.

No rationality, Euler value, supplied Stein data, curve-base isomorphism,
or connected-fiber condition is a hypothesis of this endpoint. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.KltSquareZeroPencilStein
open NefNullCurveNegativeSquare

variable {k : Type u} [Field k] [IsAlgClosed k]
local instance kltPencilSteinTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The original pencil's canonical pushforward-O map is an isomorphism,
and every original field-valued scheme fiber is connected. -/
theorem structureSheaf_iso_and_geometrically_connected
    {S X : NormalProjectiveSurface k}
    (ρ : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X ρ)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (F : CartierDivisor S.toScheme)
    (hFF : S.intersectionPairing hmin.regular F F = 0)
    (hKF : S.intersectionPairing hmin.regular K F = -2)
    (π : S.toScheme ⟶ projectiveSpace k 1) [IsProper π] [Surjective π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = S.structureMorphism)
    (e : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule S.toScheme F) :
    IsIso π.c ∧
      ∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ projectiveSpace k 1),
        ConnectedSpace (pullback π q : Scheme.{u}) := by
  letI : IsLocallyNoetherian (projectiveSpace k 1) :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec (projectiveSpaceToSpec k 1)
  obtain ⟨B, f, g, hfg, hfproper, hfconnected, hgfinite, hfc, _hrelative, _hnormalization⟩ :=
    KltDP.Literature.Stacks.steinFactorization_noetherian_literal
      (projectiveSpace k 1) S.toScheme π
  letI : IsProper f := hfproper
  letI : IsFinite g := hgfinite
  letI : IsIso f.c := hfc
  have hfsurj : Function.Surjective f.base := by
    intro b
    obtain ⟨s, hs⟩ :=
      (GeometricConnectedFiberTopology.isConnected_preimage_singleton f hfconnected b).nonempty
    exact ⟨s, hs⟩
  obtain ⟨hB, hBnormal⟩ := SteinTargetIntegral.integral_and_normal f S.normal hfsurj
  letI : IsIntegral B := hB
  letI : Surjective (f ≫ g) := by rw [hfg]; infer_instance
  letI : Surjective g := Surjective.of_comp f g
  let c := g ≫ projectiveSpaceToSpec k 1
  letI : IsProper c := FiniteProjectiveLineCurveGeometry.structure_isProper g
  have hbase : f ≫ c = S.structureMorphism := by
    dsimp [c]
    rw [← Category.assoc, hfg, hπ]
  let H := ProjectiveSpaceDegreeOneSheaf.degreeOne k 1
  let L := pullbackInvertibleSheaf g H
  let ecomp : (pullbackInvertibleSheaf (f ≫ g) H).obj ≅
      cartierDivisorModule S.toScheme F :=
    eqToIso (congrArg (fun t : S.toScheme ⟶ projectiveSpace k 1 =>
      (schemeModulePullback t).obj H.obj) hfg) ≪≫ e
  let ef : (pullbackInvertibleSheaf f L).obj ≅ cartierDivisorModule S.toScheme F :=
    (schemeModulePullbackCompIso f g).app H.obj ≪≫ ecomp
  have hpic : schemePicardPullbackHom f L.toPic = cartierPicardClass S.toScheme F :=
    (schemePicardPullbackHom_toPic f L).trans
      (SchemeKernelIdealIsoTransport.toPic_eq_of_iso
        (pullbackInvertibleSheaf f L) (cartierDivisorInvertibleSheaf S.toScheme F) ef)
  have hnum : S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom f L.toPic)) =
      cartierClass S F :=
    congrArg (fun a : S.toScheme.Pic => S.picardNumericalMap (Additive.ofMul a)) hpic
  have hne : S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom f L.toPic)) ≠ 0 := by
    rw [hnum]
    intro hz
    have hpair := cartierClass_pairing S hmin.regular K F
    rw [hz, map_zero, hKF] at hpair
    norm_num at hpair
  have hsq : S.numericalIntersectionBilinForm hmin.regular
      (S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom f L.toPic)))
      (S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom f L.toPic))) = 0 := by
    rw [hnum, cartierClass_pairing, hFF, Int.cast_zero]
  obtain ⟨eB, heB⟩ := KltIsotropicMapBase.exists_projectiveLine_iso ρ hmin hDP hrank p hp B c
    (FiniteProjectiveLineCurveGeometry.dimension_eq_one g g.surjective)
    (FiniteProjectiveLineCurveGeometry.regularPoint g g.surjective hBnormal)
    f hbase L.toPic hne hsq
  exact (S.squareZero_stein_factor_isIso_of_base_iso hmin.regular K eK F hFF hKF
    π e f g hfg eB heB).2

end KltDP.Geometry.KltSquareZeroPencilStein

#check @KltDP.Geometry.KltSquareZeroPencilStein.structureSheaf_iso_and_geometrically_connected
#print axioms KltDP.Geometry.KltSquareZeroPencilStein.structureSheaf_iso_and_geometrically_connected
