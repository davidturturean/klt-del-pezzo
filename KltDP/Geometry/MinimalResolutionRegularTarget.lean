import KltDP.Geometry.SmoothSurfaceKlt
import KltDP.Geometry.KltMinimalResolutionAutomaticGeometry
import KltDP.Geometry.ActualExceptionalLocus
import KltDP.Geometry.ProperBirationalConnectedFibers
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse

/-!
# A minimal resolution of a regular target is an isomorphism

The original all-normal-model klt theorem for the regular target and the
proved exact singular count rule out every actual contracted prime. The
original proper birational inverse on the complement then covers the whole
target. No factorization or exceptional-fiber isomorphism is assumed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- Absence of original contracted primes makes the original resolution an
isomorphism; connected fibers and the structure-sheaf inverse are derived. -/
theorem IsResolution.isIso_of_no_exceptionalCurve
    (hres : IsResolution S X π)
    (hnone : ∀ C : S.PrimeCurve, ¬ IsExceptionalCurve π C) : IsIso π := by
  letI : IsProper π := hres.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  letI : IsIso π.c := ProperBirationalStructureSheaf.resolution_c_isIso π hres
  have hempty : ActualExceptionalLocus.primeSupport π = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨C, hC, _⟩ := (ActualExceptionalLocus.mem_primeSupport π x).mp hx
    exact hnone C hC
  have hopen : ActualExceptionalLocus.complementOpen π hbir = ⊤ := by
    apply Opens.ext
    change (π.base '' ActualExceptionalLocus.primeSupport π)ᶜ = Set.univ
    rw [hempty, Set.image_empty, Set.compl_empty]
  apply IsLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit => ActualExceptionalLocus.complementOpen π hbir)
    (by simpa only [iSup_const] using hopen)
  intro i
  exact ActualExceptionalLocus.isIso_complementOpen π hbir hres.over_base
    (ProperBirationalConnectedFibers.resolution_pointFibers_connected π hres)

/-- The actual minimal resolution over an everywhere regular target has no
contracted prime, by the original exact singular-point count. -/
theorem IsMinimalResolution.not_isExceptionalCurve_of_target_regular
    (hmin : IsMinimalResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) (C : S.PrimeCurve) :
    ¬ IsExceptionalCurve π C := by
  letI : IsSmoothOfRelativeDimension 2 X.structureMorphism :=
    X.isSmoothOfRelativeDimension_two_of_regularPoints hX
  have hgeom := hmin.exceptional_forest_and_singular_count_from_klt X.isKlt_of_isSmooth
  have hsing : X.singularPoints = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact ((X.mem_singularPoints x).mp hx) (hX x)
  have hcard : Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent = 0 := by
    rw [← hgeom.2.1, hsing, Finset.card_empty]
  intro hC
  letI : Finite (ActualExceptionalIncidence.graph π).ConnectedComponent := hgeom.1
  letI : Nonempty (ActualExceptionalIncidence.graph π).ConnectedComponent :=
    ⟨(ActualExceptionalIncidence.graph π).connectedComponentMk ⟨C, hC⟩⟩
  exact (Nat.ne_of_gt (Nat.card_pos (α :=
    (ActualExceptionalIncidence.graph π).ConnectedComponent))) hcard

/-- Minimality and regularity of the original target force the original
resolution morphism itself to be an isomorphism. -/
theorem IsMinimalResolution.isIso_of_target_regular
    (hmin : IsMinimalResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) : IsIso π :=
  hmin.toIsResolution.isIso_of_no_exceptionalCurve
    (hmin.not_isExceptionalCurve_of_target_regular hX)

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.isIso_of_target_regular
#print axioms KltDP.Geometry.IsMinimalResolution.isIso_of_target_regular
