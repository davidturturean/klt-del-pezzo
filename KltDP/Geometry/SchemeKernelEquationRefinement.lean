import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.CartierPullbackFrameSquare

/-!
# Original kernel equations agree on nested ambient opens

The existing original kernel inclusion is monic after ambient open pullback.
Its proved normalization therefore identifies the two actual equation maps
on a smaller open. The section-ring normalization is the accepted
`topIso_inv_homOfLE_appTop`, applied to the original local equation.

No comparison map or agreement of frames is an input. This is the ambient
kernel square, before pulling it to the closed scheme's conormal sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeKernelEquationRefinement

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (h : V ≤ U)

/-- The original restricted scheme morphisms commute with the original open inclusions. -/
theorem restriction_square :
    (f ∣_ V) ≫ Y.homOfLE h =
      X.homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx) ≫ (f ∣_ U) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, morphismRestrict_ι]

variable (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0)

include hd in
/-- The same actual equation is killed by the smaller restricted morphism. -/
theorem equation_eq_zero : (f ∣_ V).appTop ((Y.homOfLE h).appTop d) = 0 := by
  have hs := congrArg (fun g => g.appTop) (restriction_square f U V h)
  simp only [Scheme.comp_appTop] at hs
  have he := ConcreteCategory.congr_hom hs d
  change (f ∣_ V).appTop ((Y.homOfLE h).appTop d) =
    (X.homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).appTop
      ((f ∣_ U).appTop d) at he
  rw [hd, map_zero] at he
  exact he

/-- Both routes land in the pullback of the same original global kernel and coincide. -/
theorem localEquation_refinement :
    kernelFrameRefinement f U.ι (Y.homOfLE h) (localKernelGlobalEquation f U d hd) ≫
        (eqToIso (congrArg schemeModulePullback (Y.homOfLE_ι h))).hom.app
          (schemeKernelIdeal f) =
      localKernelGlobalEquation f V ((Y.homOfLE h).appTop d)
        (equation_eq_zero f U V h d hd) := by
  apply (pulledKernelInclusion_cancel f V.ι _ _).mp
  rw [Category.assoc, pulledKernelInclusion_congr f (Y.homOfLE_ι h),
    localKernelGlobalEquation_refinement_inclusion, localKernelGlobalEquation_inclusion]

private theorem localEquation_refinement_eq (e : Γ(V.toScheme, ⊤))
    (he : e = (Y.homOfLE h).appTop d) (hde : (f ∣_ V).appTop e = 0) :
    kernelFrameRefinement f U.ι (Y.homOfLE h) (localKernelGlobalEquation f U d hd) ≫
        (eqToIso (congrArg schemeModulePullback (Y.homOfLE_ι h))).hom.app
          (schemeKernelIdeal f) = localKernelGlobalEquation f V e hde := by
  subst e
  exact localEquation_refinement f U V h d hd

section Affine

variable {Z : Scheme.{u}} (I : Z.IdealSheafData) (A B : Z.affineOpens) (hle : B ≤ A)
  (a : Γ(Z, A.1))

/-- The actual open-subscheme section map agrees with the original ambient restriction. -/
theorem affineEquation_restrict :
    (Z.homOfLE hle).appTop (gluedAffineEquation A a) =
      gluedAffineEquation B (Z.presheaf.map (homOfLE hle).op a) := by
  have htop := CartierPullbackFrameSquare.topIso_inv_homOfLE_appTop hle
  have happ := congrArg (fun m : Γ(Z, A.1) ⟶ Γ(B.1.toScheme, ⊤) => m a) htop
  simpa only [gluedAffineEquation, CommRingCat.comp_apply] using happ

variable (hI : I.ideal A = Ideal.span {a})

include hI in
/-- The actual ambient restriction of the original equation is killed on the smaller chart. -/
theorem affineEquation_eq_zero :
    (I.gluedTo ∣_ B.1).appTop
      (gluedAffineEquation B (Z.presheaf.map (homOfLE hle).op a)) = 0 := by
  have hz := equation_eq_zero I.gluedTo A.1 B.1 hle
    (gluedAffineEquation A a) (gluedAffineEquation_eq_zero I A a hI)
  simpa only [affineEquation_restrict] using hz

end Affine

/-- Retain the exact proposition inferred from a supplied proof term. -/
private abbrev statementOf {P : Prop} (_h : P) : Prop := P

set_option maxHeartbeats 800000 in
private def affineEquation_refinement_proof {Z : Scheme.{u}} (I : Z.IdealSheafData)
    (A B : Z.affineOpens) (hle : B ≤ A) (a : Γ(Z, A.1))
    (hI : I.ideal A = Ideal.span {a}) :=
  localEquation_refinement_eq (X := I.glueData.glued) (Y := Z) I.gluedTo A.1 B.1 hle
    (gluedAffineEquation (X := Z) A a) (gluedAffineEquation_eq_zero (X := Z) I A a hI)
    (gluedAffineEquation (X := Z) B (Z.presheaf.map (homOfLE hle).op a))
    (affineEquation_restrict (Z := Z) A B hle a).symm (affineEquation_eq_zero (Z := Z) I A B hle a hI)

/-- The original affine equation frames agree in the same pulled global kernel on refinement.
Its proposition is exactly the inferred equality of the two original maps;
`statementOf` is a transparent identity on that proposition. -/
theorem affineEquation_refinement {Z : Scheme.{u}} (I : Z.IdealSheafData)
    (A B : Z.affineOpens) (hle : B ≤ A) (a : Γ(Z, A.1))
    (hI : I.ideal A = Ideal.span {a}) :
    statementOf (affineEquation_refinement_proof I A B hle a hI) :=
  affineEquation_refinement_proof I A B hle a hI

end KltDP.Geometry.SchemeKernelEquationRefinement
