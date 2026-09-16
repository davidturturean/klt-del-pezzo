import KltDP.Geometry.PrincipalConormalLocalizationEvaluation
import KltDP.Geometry.SchemeDualTensorNaturality
import KltDP.Geometry.SchemeModuleSheafificationInstances

/-!
# Actual principal conormal dual comparison under localization

The original tilde-dual comparison commutes with principal localization.
One route localizes the original normal module and then takes its proved
tilde-dual comparison. The other pulls back the original comparison, uses
the existing sheaf-dual pullback map, and precomposes local functionals by
the original conormal pullback isomorphism. Evaluation proves the two
actual routes equal, independently of the regular equation.

Global chart comparison and gluing remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.PrincipalConormalLocalizationDual

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem pullbackTensor_inv_natural_right {X Y : Scheme.{u}}
    (f : Y ⟶ X) (P : X.Modules) {N D : X.Modules} (a : N ⟶ D) :
    ((schemeModulePullback f).obj P ◁ (schemeModulePullback f).map a) ≫
        (schemeModulePullbackTensorIso f P D).inv =
      (schemeModulePullbackTensorIso f P N).inv ≫
        (schemeModulePullback f).map (P ◁ a) := by
  have h : (schemeModulePullback f).map (P ◁ a) ≫
      (schemeModulePullbackTensorIso f P D).hom =
    (schemeModulePullbackTensorIso f P N).hom ≫
      ((schemeModulePullback f).obj P ◁ (schemeModulePullback f).map a) := by
    have hn := schemeModulePullbackTensorIso_natural f (𝟙 P) a
    rw [(schemeModulePullback f).map_id P] at hn
    simpa only [id_tensorHom] using hn
  apply (cancel_epi (schemeModulePullbackTensorIso f P N).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem comparisonEvaluation {Dcat : Type*} [Category Dcat] [MonoidalCategory Dcat]
    {P C N B DC DP O : Dcat} (c : P ≅ C) (a : N ⟶ B) (b : B ≅ DP) (s : DC ≅ DP)
    (evalC : C ⊗ DC ⟶ O) (evalP : P ⊗ DP ⟶ O) (EB : P ⊗ B ⟶ O)
    (hc : (c.hom ⊗ s.inv) ≫ evalC = evalP)
    (hb : (P ◁ b.hom) ≫ evalP = EB) :
    (c.hom ⊗ (a ≫ b.hom ≫ s.inv)) ≫ evalC = (P ◁ a) ≫ EB := by
  calc
    _ = (𝟙 P ⊗ a) ≫ (𝟙 P ⊗ b.hom) ≫ (c.hom ⊗ s.inv) ≫ evalC := by
      simp only [← tensor_comp_assoc, Category.id_comp, Category.assoc]
    _ = (P ◁ a) ≫ (P ◁ b.hom) ≫ evalP := by
      rw [hc]
      simp only [id_tensorHom]
    _ = (P ◁ a) ≫ EB := by rw [hb]

private theorem evaluationCancel {Dcat : Type*} [Category Dcat] [MonoidalCategory Dcat]
    {P C N N' D O : Dcat} (c : P ≅ C) (n : N ≅ N') (p : N ≅ D)
    (evalC : C ⊗ D ⟶ O) (E : C ⊗ N' ⟶ O) (T : P ⊗ N ⟶ O)
    (hp : (c.hom ⊗ p.hom) ≫ evalC = T)
    (hn : (tensorIso c n).hom ≫ E = T) :
    (C ◁ (n.inv ≫ p.hom)) ≫ evalC = E := by
  apply (cancel_epi (tensorIso c n).hom).mp
  rw [← id_tensorHom]
  simp only [tensorIso_hom, ← tensor_comp_assoc, Category.comp_id, Iso.hom_inv_id_assoc]
  exact hp.trans hn.symm

private theorem schemeComparisonEvaluation {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) (N : X.Modules)
    (e : N ≅ KltDP.SheafOfModules.dual X.ringCatSheaf L.obj)
    {C : Y.Modules} (c : (schemeModulePullback f).obj L.obj ≅ C) :
    (c.hom ⊗ (((schemeModulePullback f).mapIso e) ≪≫
      schemeModulePullbackDualIso f L ≪≫ (sectionDualIso Y c).symm).hom) ≫
        KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond C =
      ((schemeModulePullback f).obj L.obj ◁ (schemeModulePullback f).map e.hom) ≫
        (schemeModulePullbackDualEvaluationIso f L).hom :=
  comparisonEvaluation c ((schemeModulePullback f).map e.hom)
    (schemeModulePullbackDualIso f L) (sectionDualIso Y c)
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond C)
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond
      ((schemeModulePullback f).obj L.obj))
    (schemeModulePullbackDualEvaluationIso f L).hom
    (SchemeDualTensorNaturality.sectionDualIso_evaluation Y c)
    (schemeModulePullbackDualIso_evaluation f L)

private theorem iso_eq_of_inv_comp {Ccat : Type*} [Category Ccat]
    {N N' D : Ccat} (n : N ≅ N') (e : N' ≅ D) (p : N ≅ D)
    (h : n.inv ≫ p.hom = e.hom) : n ≪≫ e = p := by
  apply Iso.ext
  exact (congrArg (fun a => n.hom ≫ a) h).symm.trans (by
    change n.hom ≫ n.inv ≫ p.hom = p.hom
    rw [Iso.hom_inv_id_assoc])

private theorem localComparison_unique {R : Type u} [CommRing R]
    (I : Ideal R) (e : I) (hI : Ideal.span {(e : R)} = I)
    (he : (e : R) ∈ nonZeroDivisors R)
    (P N : (Spec (CommRingCat.of (R ⧸ I))).Modules)
    (c : P ≅ (PrincipalConormalTildeDual.conormalModule I).tilde)
    (n : N ≅ (PrincipalConormalTildeDual.normalModule I).tilde)
    (p : N ≅ KltDP.SheafOfModules.dual
      (Spec (CommRingCat.of (R ⧸ I))).ringCatSheaf
      (PrincipalConormalTildeDual.conormalModule I).tilde)
    (hp : (c.hom ⊗ p.hom) ≫ KltDP.SheafOfModules.evaluation
      (Spec (CommRingCat.of (R ⧸ I))).sheaf.val
      (Spec (CommRingCat.of (R ⧸ I))).ringCatSheaf.cond
      (PrincipalConormalTildeDual.conormalModule I).tilde =
      (tensorIso c n).hom ≫ (PrincipalConormalTildeDual.transportedEvaluationIso I e hI he).hom) :
    n ≪≫ PrincipalConormalTildeDual.iso I e hI he = p := by
  exact iso_eq_of_inv_comp n (PrincipalConormalTildeDual.iso I e hI he) p
    (PrincipalConormalTildeDual.iso_unique I e hI he (n.inv ≫ p.hom)
      (evaluationCancel c n p
        (KltDP.SheafOfModules.evaluation
          (Spec (CommRingCat.of (R ⧸ I))).sheaf.val
          (Spec (CommRingCat.of (R ⧸ I))).ringCatSheaf.cond
          (PrincipalConormalTildeDual.conormalModule I).tilde)
        (PrincipalConormalTildeDual.transportedEvaluationIso I e hI he).hom
        ((tensorIso c n).hom ≫ (PrincipalConormalTildeDual.transportedEvaluationIso I e hI he).hom)
        hp rfl))

open PrincipalConormalLocalization

variable {A : Type u} [CommRing A] (J : Ideal A) (r : A) (d : J)
  (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)

/-- Localize the actual normal module, then use the original localized tilde-dual map. -/
def localizedComparisonIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
        (PrincipalConormalTildeDual.normalModule J).tilde ≅
      KltDP.SheafOfModules.dual (Spec (CommRingCat.of (quotientRing J r))).ringCatSheaf
        (PrincipalConormalTildeDual.conormalModule (localizedIdeal J r)).tilde :=
  normalTildePullbackIso J r d hJ hd ≪≫
    PrincipalConormalTildeDual.iso (localizedIdeal J r) (localizedEquation J r d)
      (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd)

/-- Pull back the original tilde-dual map and use the original sheaf dual
pullback and contravariant conormal comparison. -/
def pulledComparisonIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
        (PrincipalConormalTildeDual.normalModule J).tilde ≅
      KltDP.SheafOfModules.dual (Spec (CommRingCat.of (quotientRing J r))).ringCatSheaf
        (PrincipalConormalTildeDual.conormalModule (localizedIdeal J r)).tilde :=
  (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).mapIso
      (PrincipalConormalTildeDual.iso J d hJ hd) ≪≫
    schemeModulePullbackDualIso (Spec.map (CommRingCat.ofHom (quotientMap J r)))
      (PrincipalConormalTildeDual.conormalLine J d hJ hd) ≪≫
    (sectionDualIso (Spec (CommRingCat.of (quotientRing J r)))
      (conormalTildePullbackIso J r d hJ hd)).symm

private theorem pulledEvaluation :
    ((schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
      (PrincipalConormalTildeDual.conormalModule J).tilde ◁
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).map
        (PrincipalConormalTildeDual.iso J d hJ hd).hom) ≫
        (schemeModulePullbackDualEvaluationIso
          (Spec.map (CommRingCat.ofHom (quotientMap J r)))
          (PrincipalConormalTildeDual.conormalLine J d hJ hd)).hom =
      (schemeModulePullbackTensorIso
        (Spec.map (CommRingCat.ofHom (quotientMap J r)))
        (PrincipalConormalTildeDual.conormalModule J).tilde
        (PrincipalConormalTildeDual.normalModule J).tilde).inv ≫
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).map
        (PrincipalConormalTildeDual.transportedEvaluationIso J d hJ hd).hom ≫
      (schemeModulePullbackUnitIso
        (Spec.map (CommRingCat.ofHom (quotientMap J r)))).hom := by
  rw [schemeModulePullbackDualEvaluationIso_hom]
  rw [← Category.assoc]
  erw [pullbackTensor_inv_natural_right
    (Spec.map (CommRingCat.ofHom (quotientMap J r)))
    (PrincipalConormalTildeDual.conormalModule J).tilde
    (PrincipalConormalTildeDual.iso J d hJ hd).hom]
  have h := congrArg (fun k =>
    (schemeModulePullbackTensorIso
      (Spec.map (CommRingCat.ofHom (quotientMap J r)))
      (PrincipalConormalTildeDual.conormalModule J).tilde
      (PrincipalConormalTildeDual.normalModule J).tilde).inv ≫
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).map k ≫
    (schemeModulePullbackUnitIso (Spec.map (CommRingCat.ofHom (quotientMap J r)))).hom)
    (PrincipalConormalTildeDual.iso_evaluation J d hJ hd)
  simpa only [Functor.map_comp, Category.assoc] using h

set_option maxHeartbeats 800000 in
private theorem comparison_evaluation :
    ((conormalTildePullbackIso J r d hJ hd).hom ⊗
      (pulledComparisonIso J r d hJ hd).hom) ≫
      KltDP.SheafOfModules.evaluation
        (Spec (CommRingCat.of (quotientRing J r))).sheaf.val
        (Spec (CommRingCat.of (quotientRing J r))).ringCatSheaf.cond
        (PrincipalConormalTildeDual.conormalModule (localizedIdeal J r)).tilde =
    (tensorIso (conormalTildePullbackIso J r d hJ hd)
      (normalTildePullbackIso J r d hJ hd)).hom ≫
      (PrincipalConormalTildeDual.transportedEvaluationIso (localizedIdeal J r)
        (localizedEquation J r d) (localizedEquation_span J r d hJ)
        (localizedEquation_regular J r d hd)).hom := by
  exact (schemeComparisonEvaluation
    (Spec.map (CommRingCat.ofHom (quotientMap J r)))
    (PrincipalConormalTildeDual.conormalLine J d hJ hd)
    (PrincipalConormalTildeDual.normalModule J).tilde
    (PrincipalConormalTildeDual.iso J d hJ hd)
    (conormalTildePullbackIso J r d hJ hd)).trans
    ((pulledEvaluation J r d hJ hd).trans
    (PrincipalConormalLocalizationEvaluation.tensor_evaluation J r d hJ hd).symm)

set_option maxHeartbeats 800000 in
/-- The two produced actual sheaf-dual routes commute with principal localization. -/
theorem comparisonIso_eq :
    localizedComparisonIso J r d hJ hd = pulledComparisonIso J r d hJ hd := by
  exact localComparison_unique (localizedIdeal J r) (localizedEquation J r d)
    (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd)
    ((schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
      (PrincipalConormalTildeDual.conormalModule J).tilde)
    ((schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
      (PrincipalConormalTildeDual.normalModule J).tilde)
    (conormalTildePullbackIso J r d hJ hd) (normalTildePullbackIso J r d hJ hd)
    (pulledComparisonIso J r d hJ hd) (comparison_evaluation J r d hJ hd)

/-- The same actual pullback route is independent of the regular principal equation. -/
theorem pulledComparisonIso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A) :
    pulledComparisonIso J r e hE he = pulledComparisonIso J r d hJ hd := by
  rw [← comparisonIso_eq J r e hE he, ← comparisonIso_eq J r d hJ hd]
  unfold localizedComparisonIso
  rw [normalTildePullbackIso_eq J r d hJ hd e hE he]
  rw [PrincipalConormalTildeDual.iso_eq (localizedIdeal J r)
    (localizedEquation J r d) (localizedEquation_span J r d hJ)
    (localizedEquation_regular J r d hd) (localizedEquation J r e)
    (localizedEquation_span J r e hE) (localizedEquation_regular J r e he)]

end KltDP.Geometry.PrincipalConormalLocalizationDual
