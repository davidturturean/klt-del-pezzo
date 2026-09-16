import KltDP.Geometry.NormalTwistedAdjunctionTensorChart
import KltDP.Geometry.PrincipalConormalTildeDual

/-!
# Affine adjunction with the actual sheaf dual of the conormal line

The original quotient Kähler sheaf is identified with the actual pulled-back
ambient top-differential tilde sheaf tensored with the existing sheaf dual of
the original conormal tilde. The right-factor comparison is the produced
evaluation-normalized principal conormal dual comparison.

Contracting the result with the original conormal agrees with the actual
module evaluation transported through the earlier tilde tensor comparison.
The whole chart is independent of the chosen regular principal equation.
The contraction calculation is proved first at abstract monoidal objects.

Identification with a global conormal sheaf, compatibility on common affine
refinements, and gluing to global adjunction remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u v w

namespace KltDP.Geometry.NormalTwistedAdjunctionSheafDualChart

section MonoidalPairing

variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private def pairedEvaluation (P F : C) {N U : C} (ev : P ⊗ N ⟶ U) :
    P ⊗ (F ⊗ N) ⟶ F ⊗ U :=
  (α_ P F N).inv ≫ (β_ P F).hom ▷ N ≫ (α_ F P N).hom ≫ F ◁ ev

private theorem pairedEvaluation_comp (P F : C) {N D U : C}
    (m : N ⟶ D) (evD : P ⊗ D ⟶ U) (evN : P ⊗ N ⟶ U)
    (hm : P ◁ m ≫ evD = evN) :
    P ◁ (F ◁ m) ≫ pairedEvaluation P F evD = pairedEvaluation P F evN := by
  unfold pairedEvaluation
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp, hm]

private theorem pairedEvaluation_trans (P F : C) {H N D U : C}
    (a : H ≅ F ⊗ N) (n : N ≅ D)
    (evD : P ⊗ D ⟶ U) (evN : P ⊗ N ⟶ U)
    (hn : P ◁ n.hom ≫ evD = evN) :
    P ◁ (a ≪≫ whiskerLeftIso F n).hom ≫ pairedEvaluation P F evD =
      P ◁ a.hom ≫ pairedEvaluation P F evN := by
  change P ◁ (a.hom ≫ F ◁ n.hom) ≫ pairedEvaluation P F evD =
    P ◁ a.hom ≫ pairedEvaluation P F evN
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, pairedEvaluation_comp P F n.hom evD evN hn]

end MonoidalPairing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (S : Scheme.{u}) :
    ∀ U, IsMulCommutative (S.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance modulesMonoidal (S : Scheme.{u}) : MonoidalCategory S.Modules :=
  Scheme.Modules.monoidalCategory S

local instance modulesSymmetric (S : Scheme.{u}) : SymmetricCategory S.Modules :=
  Scheme.Modules.symmetricCategory S

section Principal

variable {A : Type u} [CommRing A] (J : Ideal A)

/-- Contract the actual sheaf dual with the original conormal, retaining the unit factor. -/
def conormalContraction (F : (Spec (CommRingCat.of (A ⧸ J))).Modules) :
    (PrincipalConormalTildeDual.conormalModule J).tilde ⊗
        (F ⊗ KltDP.SheafOfModules.dual (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf
          (PrincipalConormalTildeDual.conormalModule J).tilde) ⟶
      F ⊗ _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf :=
  pairedEvaluation (PrincipalConormalTildeDual.conormalModule J).tilde F
    (KltDP.SheafOfModules.evaluation (Spec (CommRingCat.of (A ⧸ J))).sheaf.val
      (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf.cond
      (PrincipalConormalTildeDual.conormalModule J).tilde)

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- Tensor the actual evaluation-normalized conormal dual comparison with any original sheaf. -/
def normalTensorIso (F : (Spec (CommRingCat.of (A ⧸ J))).Modules) :
    F ⊗ (PrincipalConormalTildeDual.normalModule J).tilde ≅
      F ⊗ KltDP.SheafOfModules.dual (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf
        (PrincipalConormalTildeDual.conormalModule J).tilde :=
  whiskerLeftIso F (PrincipalConormalTildeDual.iso J d hJ hregular)

/-- The comparison's forward map is the original left tensor functor on the produced dual map. -/
theorem normalTensorIso_hom (F : (Spec (CommRingCat.of (A ⧸ J))).Modules) :
    (normalTensorIso J d hJ hregular F).hom =
      F ◁ (PrincipalConormalTildeDual.iso J d hJ hregular).hom := rfl

/-- Contract using the original module evaluation transported through the tilde tensor map. -/
def moduleContraction (F : (Spec (CommRingCat.of (A ⧸ J))).Modules) :
    (PrincipalConormalTildeDual.conormalModule J).tilde ⊗
        (F ⊗ (PrincipalConormalTildeDual.normalModule J).tilde) ⟶
      F ⊗ _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf :=
  pairedEvaluation (PrincipalConormalTildeDual.conormalModule J).tilde F
    (PrincipalConormalTildeDual.transportedEvaluationIso J d hJ hregular).hom

/-- Tensoring the produced normal comparison preserves the original evaluation exactly. -/
theorem normalTensorIso_evaluation (F : (Spec (CommRingCat.of (A ⧸ J))).Modules) :
    (PrincipalConormalTildeDual.conormalModule J).tilde ◁
        (normalTensorIso J d hJ hregular F).hom ≫ conormalContraction J F =
      moduleContraction J d hJ hregular F :=
  pairedEvaluation_comp (PrincipalConormalTildeDual.conormalModule J).tilde F
    (PrincipalConormalTildeDual.iso J d hJ hregular).hom _ _
    (PrincipalConormalTildeDual.iso_evaluation J d hJ hregular)

/-- The right-factor tensor comparison is independent of the regular equation. -/
theorem normalTensorIso_eq (F : (Spec (CommRingCat.of (A ⧸ J))).Modules)
    (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    normalTensorIso J e hE heregular F = normalTensorIso J d hJ hregular F := by
  unfold normalTensorIso
  rw [PrincipalConormalTildeDual.iso_eq J d hJ hregular e hE heregular]

end Principal

section SmoothChart

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]

/-- The actual pullback of the original ambient top-differential tilde sheaf. -/
abbrev ambientSheaf : (Spec (CommRingCat.of (A ⧸ J))).Modules :=
  (schemeModulePullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
    (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- The actual affine Kähler sheaf is the pulled ambient top-form sheaf tensored with the
existing sheaf dual of the original conormal tilde. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J)))) ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
          (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde ⊗
        KltDP.SheafOfModules.dual (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf
          (PrincipalConormalTildeDual.conormalModule J).tilde :=
  NormalTwistedAdjunctionTensorChart.iso R A J d hJ hregular ≪≫
    normalTensorIso J d hJ hregular (ambientSheaf R A J)

/-- The forward map retains the original tensor chart and the produced conormal dual map. -/
theorem iso_hom :
    (iso R A J d hJ hregular).hom =
      (NormalTwistedAdjunctionTensorChart.iso R A J d hJ hregular).hom ≫
        ambientSheaf R A J ◁ (PrincipalConormalTildeDual.iso J d hJ hregular).hom := rfl

set_option maxHeartbeats 800000 in
/-- Contraction after the actual chart agrees with the original transported module pairing. -/
theorem iso_evaluation :
    (PrincipalConormalTildeDual.conormalModule J).tilde ◁
        (iso R A J d hJ hregular).hom ≫ conormalContraction J (ambientSheaf R A J) =
      (PrincipalConormalTildeDual.conormalModule J).tilde ◁
          (NormalTwistedAdjunctionTensorChart.iso R A J d hJ hregular).hom ≫
        moduleContraction J d hJ hregular (ambientSheaf R A J) :=
  pairedEvaluation_trans (PrincipalConormalTildeDual.conormalModule J).tilde
    (ambientSheaf R A J) (NormalTwistedAdjunctionTensorChart.iso R A J d hJ hregular)
    (PrincipalConormalTildeDual.iso J d hJ hregular) _ _
    (PrincipalConormalTildeDual.iso_evaluation J d hJ hregular)

/-- The full actual-object affine chart is independent of the chosen regular equation. -/
theorem iso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    iso R A J e hE heregular = iso R A J d hJ hregular := by
  unfold iso
  rw [NormalTwistedAdjunctionTensorChart.iso_eq R A J d hJ hregular e hE heregular,
    normalTensorIso_eq J d hJ hregular (ambientSheaf R A J) e hE heregular]

end SmoothChart

end KltDP.Geometry.NormalTwistedAdjunctionSheafDualChart
