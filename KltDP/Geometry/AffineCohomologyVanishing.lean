/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Ported from Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleCohomologyAffineHOne.lean:53-74 and
SchemeModuleCohomologyAffineHThree.lean:190-364,416-505.
The project's already-proved IsFlasqueSheaf and cohomology-under-isomorphism
APIs replace duplicate modern foundations. No positive-degree conclusion
is retained as an assumption in the final theorem.
-/
import KltDP.Geometry.AffineCohomologyLocalKilling
import KltDP.Geometry.AffineCohomologyDimensionShift

/-!
# Positive-degree affine quasicoherent vanishing

The finite-cover map kills each class locally. Its actual quasicoherent
cokernel and the long exact sequence make that map injective. Strong
induction in the degree supplies all section-surjectivity conditions
needed by the local-killing recursion. Actual affine isomorphisms then
transport the result from spectra to every affine scheme.

Source port draft: VM elaboration, transitive axiom audit, and integration
remain pending. The final construction targets the existing exact
AffineVanishingLiteral interface, without using a literature axiom.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open KltDP.Geometry.ModuleCohomology

namespace KltDP.Geometry.AffineCohomologyPort

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private abbrev AbSheaf (X : Scheme.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}

/-- The degree-one base of affine vanishing, for every quasicoherent spectrum module. -/
theorem moduleSpecHOne_subsingleton {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] : Subsingleton (H M 1) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨I, U, hfinite, hcover, haffine, _, hkilled⟩ :=
    LocalKilling.schemeHOne_finiteAffineKillingCover M c
  letI : Finite I := hfinite
  letI (i : I) : IsAffine (U i) := haffine i
  apply toAffineCoverModule_HOne_injective M U hcover
  rw [hkilled, map_zero]

private abbrev openSheafPullback {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf U := OpenRestrictionExtOne.res U.ι

private instance openSheafPullback_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openSheafPullback U) :=
  OpenRestrictionExtOne.res_preservesFiniteLimits U.ι

private instance openSheafPullback_preservesFiniteColimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (openSheafPullback U) :=
  OpenRestrictionExtOne.res_preservesFiniteColimits U.ι

private instance openSheafPullback_preservesZeroMorphisms {X : Scheme.{u}} (U : X.Opens) :
    (openSheafPullback U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private theorem openSheafPullback_isFlasque {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) (hF : IsFlasqueSheaf F) :
    IsFlasqueSheaf ((openSheafPullback U).obj F) := by
  intro V W i
  exact hF (U.ι.opensFunctor.map i)

private abbrev injectiveCokernelSequence {X : Scheme.{u}} (F : AbSheaf X) :
    ShortComplex (AbSheaf X) := OpenRestrictionExtOne.injectiveSES F

private theorem injectiveCokernelSequence_shortExact {X : Scheme.{u}} (F : AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := OpenRestrictionExtOne.injectiveSES_shortExact F

private theorem subsingleton_H_X₃_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ)
    (hmiddle : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n))
    (hleft : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₃ n) := by
  letI := hmiddle
  letI := hleft
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨y, hy⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃
    hS n (n + 1) rfl c (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

private theorem openSheafPullback_injectiveCokernel_H_succ_subsingleton
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X) (n : ℕ)
    (hF : Subsingleton
      (CategoryTheory.Sheaf.H ((openSheafPullback U).obj F) (n + 2))) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((openSheafPullback U).obj (cokernel (Injective.ι F))) (n + 1)) := by
  let L := openSheafPullback U
  let S := injectiveCokernelSequence F
  letI : L.PreservesZeroMorphisms := openSheafPullback_preservesZeroMorphisms U
  have hSL : (S.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact (injectiveCokernelSequence_shortExact F) L
  have hI : IsFlasqueSheaf (Injective.under F) :=
    isFlasque_of_injective (Injective.under F)
  have hIL : IsFlasqueSheaf (L.obj (Injective.under F)) :=
    openSheafPullback_isFlasque U (Injective.under F) hI
  have hmiddle : Subsingleton
      (CategoryTheory.Sheaf.H (L.obj (Injective.under F)) (n + 1)) :=
    sheafH_subsingleton_of_flasque (U : Scheme.{u}) _ hIL n
  exact subsingleton_H_X₃_of_shortExact hSL (n + 1) hmiddle hF

private theorem injectiveCokernel_app_surjective_of_pullback_HOne_subsingleton
    {R : CommRingCat.{u}} (F : AbSheaf (Spec R)) (U : (Spec R).Opens)
    (hF : Subsingleton (CategoryTheory.Sheaf.H ((openSheafPullback U).obj F) 1)) :
    Function.Surjective ((cokernel.π (Injective.ι F)).val.app (op U)) := by
  let L := openSheafPullback U
  let S := injectiveCokernelSequence F
  letI : L.PreservesZeroMorphisms := openSheafPullback_preservesZeroMorphisms U
  have hSL : (S.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact (injectiveCokernelSequence_shortExact F) L
  letI : Subsingleton ((S.map L).X₁.H 1) := hF
  have hsurjective := CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
    hSL (isTerminalTop : IsTerminal (⊤ : Opens (U : Scheme)))
  change Function.Surjective ((L.map (cokernel.π (Injective.ι F))).val.app
    (op (⊤ : Opens (U : Scheme)))) at hsurjective
  change Function.Surjective ((cokernel.π (Injective.ι F)).val.app
    (op (U.ι.opensFunctor.obj (⊤ : Opens (U : Scheme))))) at hsurjective
  have htop : U.ι.opensFunctor.obj (⊤ : Opens (U : Scheme)) = U := by
    ext x
    simp
  rw [htop] at hsurjective
  exact hsurjective

private theorem affineSyzygyAppSurjective_of_pullback_H_succ_subsingleton
    {R : CommRingCat.{u}} (F : AbSheaf (Spec R)) (n : ℕ)
    (hF : ∀ (U : (Spec R).Opens), IsAffineOpen U → ∀ k, k < n →
      Subsingleton (CategoryTheory.Sheaf.H ((openSheafPullback U).obj F) (k + 1))) :
    LocalKilling.AffineSyzygyAppSurjective F n := by
  induction n generalizing F with
  | zero => exact .zero F
  | succ n ih =>
      apply LocalKilling.AffineSyzygyAppSurjective.succ
      · intro U hU
        exact injectiveCokernel_app_surjective_of_pullback_HOne_subsingleton F U
          (hF U hU 0 (Nat.zero_lt_succ n))
      · apply ih
        intro U hU k hk
        apply openSheafPullback_injectiveCokernel_H_succ_subsingleton
        exact hF U hU (k + 1) (Nat.succ_lt_succ hk)

/-- Every positive cohomology group of an original quasicoherent spectrum module vanishes. -/
theorem moduleSpecHSucc_subsingleton {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) : Subsingleton (H M (n + 1)) := by
  induction n using Nat.strong_induction_on generalizing R M with
  | h n ih =>
      cases n with
      | zero => exact moduleSpecHOne_subsingleton M
      | succ n =>
          refine subsingleton_of_forall_eq 0 fun c => ?_
          let F := (_root_.SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
          have hsyzygy : LocalKilling.AffineSyzygyAppSurjective F (n + 1) := by
            apply affineSyzygyAppSurjective_of_pullback_H_succ_subsingleton
            intro U hU k hk
            letI : IsAffine (U : Scheme) := hU
            let N := (SchemeModuleRestriction.restriction U.ι).obj M
            letI : N.IsQuasicoherent := by dsimp [N]; infer_instance
            let e := (U : Scheme).isoSpec
            let P := (schemeModulePushforward e.hom).obj N
            letI : P.IsQuasicoherent := pushforward_isQuasicoherent_of_iso e N
            letI : Subsingleton (H P (k + 1)) := ih k hk P
            have hN : Subsingleton (H N (k + 1)) :=
              h_subsingleton_of_pushforward_iso e N (k + 1)
            change Subsingleton (H N (k + 1))
            exact hN
          obtain ⟨I, U, hfinite, hcover, haffine, _, hkilled⟩ :=
            LocalKilling.schemeHSucc_finiteAffineKillingCover_of_affine_syzygy_app_surjective
              M (n + 1) c hsyzygy
          letI : Finite I := hfinite
          letI (i : I) : IsAffine (U i) := haffine i
          letI : (cokernel (toAffineCoverModule M U)).IsQuasicoherent :=
            affineCoverCokernel_isQuasicoherent M U
          letI : Subsingleton (H (cokernel (toAffineCoverModule M U)) (n + 1)) :=
            ih n (Nat.lt_succ_self n) _
          apply toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton M U hcover (n + 1)
          rw [hkilled, map_zero]

/-- Every positive cohomology group vanishes on any actual affine scheme. -/
theorem moduleAffineHSucc_subsingleton {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) : Subsingleton (H M (n + 1)) := by
  let e := X.isoSpec
  let N := (schemeModulePushforward e.hom).obj M
  letI : N.IsQuasicoherent := pushforward_isQuasicoherent_of_iso e M
  letI : Subsingleton (H N (n + 1)) := moduleSpecHSucc_subsingleton N n
  exact h_subsingleton_of_pushforward_iso e M (n + 1)

/-- The existing affine-vanishing interface is filled by the ported proof. -/
theorem affineVanishingLiteral_proved : KltDP.Literature.Stacks.AffineVanishingLiteral.{u} where
  subsingleton_H X _ F _ p hp := by
    cases p with
    | zero => exact (Nat.lt_irrefl 0 hp).elim
    | succ n => exact moduleAffineHSucc_subsingleton F n

end KltDP.Geometry.AffineCohomologyPort
