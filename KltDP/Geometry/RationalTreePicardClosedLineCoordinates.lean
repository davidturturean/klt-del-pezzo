import KltDP.Geometry.RationalTreePicardClosedFrameGeometry
import KltDP.Geometry.SchemeConormalEquationChange

/-!
# Geometric component maps of the original scalar-kernel trivialization

The original scalar matching unit has the actual structure map on the
right component and the original scalar multiple of the structure map
on the left. These formulas are proved by the original kernel inclusion,
the original quotient maps, and evaluation of a unit-module morphism at
the original global section 1. No component-coordinate equation is input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The inverse actual tilde-unit map keeps the original section of 1. -/
theorem affineUnitIso_inv_one (A : Type u) [CommRing A] :
    (AffineModuleTilde.unitIso A).inv.val.app (op ⊤)
        (1 : Γ(Spec (CommRingCat.of A), ⊤)) =
      ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A) := by
  have h : (AffineModuleTilde.unitIso A).hom.val.app (op ⊤)
      (ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A)) =
      (1 : Γ(Spec (CommRingCat.of A), ⊤)) := by
    rw [affineUnitIso_hom_toOpen]
    exact (StructureSheaf.toOpen A ⊤).hom.map_one
  have h2 : (AffineModuleTilde.unitIso A).inv.val.app (op ⊤)
      ((AffineModuleTilde.unitIso A).hom.val.app (op ⊤)
        (ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A))) =
      ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A) :=
    ConcreteCategory.congr_hom
      (congrArg (fun g : (ModuleCat.of A A).tilde ⟶ (ModuleCat.of A A).tilde =>
        g.val.app (op ⊤)) (AffineModuleTilde.unitIso A).hom_inv_id)
      (ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A))
  rw [h] at h2
  exact h2

variable {k : Type u} [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (I J : Ideal A) (g : kˣ)

/-- The original matching generator has exactly the original gauged
quotient pair as its image in the source of the actual sheaf kernel. -/
theorem closedLineUnitIso_one_pair (hcover : I ⊓ J = ⊥) :
    ((closedLineUnitIso A I J g hcover).hom ≫
        kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g))).val.app
          (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)) =
      ModuleCat.Tilde.toOpen (ModuleCat.of A ((A ⧸ I) × (A ⧸ J))) ⊤
        (closedLinePairLinear A I J g (1 : A ⧸ I ⊓ J)) := by
  let e : (A ⧸ I ⊓ J) ≃ₐ[A] A :=
    (Ideal.quotientEquivAlgOfEq A hcover).trans (AlgEquiv.quotientBot A A)
  have hι : (closedLineUnitIso A I J g hcover).hom ≫
        kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g)) =
      (AffineModuleTilde.unitIso A).inv ≫
        AffineModuleTilde.map (ModuleCat.ofHom e.symm.toLinearMap) ≫
        AffineModuleTilde.map (ModuleCat.ofHom (closedLinePairLinear A I J g)) := by
    change ((AffineModuleTilde.unitIso A).inv ≫
        AffineModuleTilde.map (ModuleCat.ofHom e.symm.toLinearMap) ≫
        (closedLineQuotientSheafIso A I J g).hom) ≫
          kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g)) = _
    rw [Category.assoc, Category.assoc, closedLineQuotientSheafIso_hom_ι]
  rw [hι]
  change (AffineModuleTilde.map (ModuleCat.ofHom (closedLinePairLinear A I J g))).val.app
      (op ⊤) ((AffineModuleTilde.map (ModuleCat.ofHom e.symm.toLinearMap)).val.app
        (op ⊤) ((AffineModuleTilde.unitIso A).inv.val.app (op ⊤)
          (1 : Γ(Spec (CommRingCat.of A), ⊤)))) = _
  rw [affineUnitIso_inv_one, AffineModuleTilde.map_app_toOpen,
    AffineModuleTilde.map_app_toOpen]
  change ModuleCat.Tilde.toOpen (ModuleCat.of A ((A ⧸ I) × (A ⧸ J))) ⊤
      (closedLinePairLinear A I J g (e.symm 1)) = _
  rw [map_one]

/-- The right original quotient coordinate of the matching generator is 1. -/
theorem closedLinePairLinear_one_snd :
    (closedLinePairLinear A I J g (1 : A ⧸ I ⊓ J)).2 = 1 := by
  change Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right) 1 = 1
  exact map_one _

/-- The left original quotient coordinate is the original lifted node scalar. -/
theorem closedLinePairLinear_one_fst :
    (closedLinePairLinear A I J g (1 : A ⧸ I ⊓ J)).1 =
      Ideal.Quotient.mk I (closedLineGaugeUnit A g : A) := by
  change ((closedLineGaugeUnit A g)⁻¹)⁻¹ •
      Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left) 1 = _
  rw [inv_inv, map_one, Units.smul_def, Algebra.smul_def, mul_one]
  rfl

/-- The actual section of the original lifted scalar on the left component. -/
def closedLineLeftScalarSection : Γ(Spec (CommRingCat.of (A ⧸ I)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv
    (Ideal.Quotient.mk I (closedLineGaugeUnit A g : A))

/-- The original scalar-kernel trivialization has the canonical geometric
structure map as its right component, including its normalization. -/
theorem closedLineUnitIso_rightComponent (hcover : I ⊓ J = ⊥) :
    (closedLineUnitIso A I J g hcover).hom ≫ closedLineRightComponentMap A I J g =
      structureToPushforwardUnit (closedComponentInclusion A J) := by
  apply ((componentUnitPushforward A (A ⧸ J)).unitHomEquiv).injective
  apply (schemeModuleSectionsEquivTop _).injective
  change (quotientTildePushforwardUnitIso A J).hom.val.app (op ⊤)
      ((AffineModuleTilde.map (ModuleCat.ofHom
        (LinearMap.snd A (A ⧸ I) (A ⧸ J)))).val.app (op ⊤)
        (((closedLineUnitIso A I J g hcover).hom ≫
          kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g))).val.app
            (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)))) =
    (closedComponentInclusion A J).appTop (1 : Γ(Spec (CommRingCat.of A), ⊤))
  rw [closedLineUnitIso_one_pair, AffineModuleTilde.map_app_toOpen]
  change (componentUnitTildePushforwardIso A (A ⧸ J)).hom.val.app (op ⊤)
      (ModuleCat.Tilde.toOpen (ModuleCat.of A (A ⧸ J)) ⊤
        (closedLinePairLinear A I J g (1 : A ⧸ I ⊓ J)).2) = _
  rw [componentUnitTildePushforwardIso_toOpen, closedLinePairLinear_one_snd]
  change (Spec (CommRingCat.of (A ⧸ J))).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv 1) = _
  simp only [map_one]

/-- The left component is the canonical geometric structure map followed
by multiplication by the SAME original lifted node scalar. -/
theorem closedLineUnitIso_leftComponent (hcover : I ⊓ J = ⊥) :
    (closedLineUnitIso A I J g hcover).hom ≫ closedLineLeftComponentMap A I J g =
      structureToPushforwardUnit (closedComponentInclusion A I) ≫
        (schemeModulePushforward (closedComponentInclusion A I)).map
          (schemeScalarEnd (closedLineLeftScalarSection A I g)) := by
  apply ((componentUnitPushforward A (A ⧸ I)).unitHomEquiv).injective
  apply (schemeModuleSectionsEquivTop _).injective
  change (quotientTildePushforwardUnitIso A I).hom.val.app (op ⊤)
      ((AffineModuleTilde.map (ModuleCat.ofHom
        (LinearMap.fst A (A ⧸ I) (A ⧸ J)))).val.app (op ⊤)
        (((closedLineUnitIso A I J g hcover).hom ≫
          kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g))).val.app
            (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)))) =
    (schemeScalarEnd (closedLineLeftScalarSection A I g)).val.app (op ⊤)
      ((closedComponentInclusion A I).appTop (1 : Γ(Spec (CommRingCat.of A), ⊤)))
  rw [closedLineUnitIso_one_pair, AffineModuleTilde.map_app_toOpen]
  change (componentUnitTildePushforwardIso A (A ⧸ I)).hom.val.app (op ⊤)
      (ModuleCat.Tilde.toOpen (ModuleCat.of A (A ⧸ I)) ⊤
        (closedLinePairLinear A I J g (1 : A ⧸ I ⊓ J)).1) = _
  rw [componentUnitTildePushforwardIso_toOpen, closedLinePairLinear_one_fst,
    schemeScalarEnd_appTop, map_one, one_mul]
  change (Spec (CommRingCat.of (A ⧸ I))).presheaf.map (𝟙 (op ⊤))
      (closedLineLeftScalarSection A I g) = closedLineLeftScalarSection A I g
  exact ConcreteCategory.congr_hom
    ((Spec (CommRingCat.of (A ⧸ I))).presheaf.map_id (op ⊤)) _

end KltDP.Geometry.RationalTreePicard
