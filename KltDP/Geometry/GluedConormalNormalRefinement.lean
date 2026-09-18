import KltDP.Geometry.GluedConormalBasicOpenDual
import KltDP.Geometry.GluedConormalTildeRefinement
import KltDP.Geometry.GluedConormalTildeDualChart
import KltDP.Geometry.SchemeModulePullbackDualNaturality
import KltDP.Geometry.SchemeModulePullbackDualComp

/-!
# Refinement of the original global normal comparison

The original basic-open normal-module comparison preserves the original
dual evaluation. Naturality and composition of the original dual pullback
map transport that local square through the proved original global
conormal square. The resulting equality uses the original global normal
chart isomorphisms, quotient-chart inclusion, and equality transport.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GluedConormalNormalRefinement

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (S : Scheme.{u}) :
    ∀ U, IsMulCommutative (S.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

private theorem sectionDualIso_trans (X : Scheme.{u}) {M N P : X.Modules}
    (c : M ≅ N) (d : N ≅ P) :
    sectionDualIso X (c ≪≫ d) = sectionDualIso X d ≪≫ sectionDualIso X c := by
  apply Iso.ext
  exact sectionDualMap_comp X c.hom d.hom

private theorem refl_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (M : C) : (Iso.refl F).app M = Iso.refl (F.obj M) := rfl

private theorem dual_comp_refinement {X U V : Scheme.{u}}
    (b : V ⟶ U) (i : U ⟶ X) (j : V ⟶ X) (h : b ≫ i = j)
    (L : InvertibleSheaf X) :
    (schemeModulePullback b).mapIso (schemeModulePullbackDualIso i L) ≪≫
      schemeModulePullbackDualIso b (pullbackInvertibleSheaf i L) =
    ((schemeModulePullbackCompIso b i).app
        (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) ≪≫
      (eqToIso (congrArg schemeModulePullback h)).app
        (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj)) ≪≫
      schemeModulePullbackDualIso j L ≪≫
      sectionDualIso V ((schemeModulePullbackCompIso b i).app L.obj ≪≫
        (eqToIso (congrArg schemeModulePullback h)).app L.obj) := by
  subst j
  simpa only [eqToIso_refl, refl_app, Iso.trans_refl] using
    schemeModulePullbackDualIso_comp b i L

private theorem normal_comparison_refinement {X U V : Scheme.{u}}
    (b : V ⟶ U) (i : U ⟶ X) (j : V ⟶ X) (h : b ≫ i = j)
    (L : InvertibleSheaf X) (L₀ : InvertibleSheaf U)
    {C₁ N₁ : V.Modules} {N₀ : U.Modules}
    (c₀ : L₀.obj ≅ (schemeModulePullback i).obj L.obj)
    (c₁ : C₁ ≅ (schemeModulePullback j).obj L.obj)
    (e₀ : N₀ ≅ KltDP.SheafOfModules.dual U.ringCatSheaf L₀.obj)
    (e₁ : N₁ ≅ KltDP.SheafOfModules.dual V.ringCatSheaf C₁)
    (c : (schemeModulePullback b).obj L₀.obj ≅ C₁)
    (n : (schemeModulePullback b).obj N₀ ≅ N₁)
    (hc : (schemeModulePullback b).mapIso c₀ ≪≫
        (schemeModulePullbackCompIso b i).app L.obj ≪≫
        (eqToIso (congrArg schemeModulePullback h)).app L.obj = c ≪≫ c₁)
    (hn : n ≪≫ e₁ = (schemeModulePullback b).mapIso e₀ ≪≫
      schemeModulePullbackDualIso b L₀ ≪≫ (sectionDualIso V c).symm) :
    (schemeModulePullback b).mapIso (e₀ ≪≫ (sectionDualIso U c₀).symm ≪≫
        (schemeModulePullbackDualIso i L).symm) ≪≫
      (schemeModulePullbackCompIso b i).app
        (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) ≪≫
      (eqToIso (congrArg schemeModulePullback h)).app
        (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) =
    n ≪≫ e₁ ≪≫ (sectionDualIso V c₁).symm ≪≫
      (schemeModulePullbackDualIso j L).symm := by
  let F := schemeModulePullback b
  let KL := (schemeModulePullbackCompIso b i).app L.obj ≪≫
    (eqToIso (congrArg schemeModulePullback h)).app L.obj
  let KD := (schemeModulePullbackCompIso b i).app
      (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) ≪≫
    (eqToIso (congrArg schemeModulePullback h)).app
      (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj)
  let G := (F.mapIso (sectionDualIso U c₀)).symm
  let H := (F.mapIso (schemeModulePullbackDualIso i L)).symm
  let P := schemeModulePullbackDualIso b (pullbackInvertibleSheaf i L)
  let Q := (sectionDualIso V (F.mapIso c₀)).symm
  let R := (sectionDualIso V KL).symm
  let J := (schemeModulePullbackDualIso j L).symm
  have hnat : G ≪≫ P = schemeModulePullbackDualIso b L₀ ≪≫ Q := by
    have hh := congrArg (fun z => G ≪≫ z ≪≫ Q)
      (schemeModulePullbackDualIso_natural b L₀ (pullbackInvertibleSheaf i L) c₀)
    simpa only [G, Q, F, P, Iso.trans_assoc, Iso.symm_self_id_assoc,
      Iso.self_symm_id, Iso.trans_refl] using hh.symm
  have hcomp : H ≪≫ KD = P ≪≫ R ≪≫ J := by
    have hh := congrArg (fun z => H ≪≫ z ≪≫ R ≪≫ J)
      (dual_comp_refinement b i j h L)
    simpa only [H, KD, R, J, F, P, KL, Iso.trans_assoc,
      Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
      Iso.self_symm_id, Iso.trans_refl] using hh.symm
  have hconormal : Q ≪≫ R = (sectionDualIso V c).symm ≪≫
      (sectionDualIso V c₁).symm := by
    have hh := congrArg (fun z => (sectionDualIso V z).symm) hc
    simpa only [Q, R, KL, F, sectionDualIso_trans, Iso.trans_symm, Iso.trans_assoc] using hh
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc]
  change F.mapIso e₀ ≪≫ G ≪≫ H ≪≫ KD =
    n ≪≫ e₁ ≪≫ (sectionDualIso V c₁).symm ≪≫ J
  rw [hcomp]
  rw [← Iso.trans_assoc G P, hnat, Iso.trans_assoc]
  rw [← Iso.trans_assoc Q R, hconormal, Iso.trans_assoc]
  simpa only [Iso.trans_assoc] using
    congrArg (fun z => z ≪≫ (sectionDualIso V c₁).symm ≪≫ J) hn.symm

open GluedConormalBasicOpenLocalization GluedConormalBasicOpenNormal
open GluedConormalTildeDualChart

variable {X : Scheme.{u}} (I : X.IdealSheafData) (hI : IdealLocallyPrincipalRegular I)
  (U : X.affineOpens) (r d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original global normal chart comparison commutes with the actual basic-open
quotient-chart refinement, with no compatibility witness as an input. -/
theorem chartIso_refinement :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).mapIso
        (chartIso I hI U d hU hd) ≪≫
      (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
        (I.glueData.ι U)).app (globalNormalSheaf I) ≪≫
      (eqToIso (congrArg schemeModulePullback
        (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r)))).app
        (globalNormalSheaf I) =
    normalTildeRefinementIso I U r d hU hd ≪≫
      chartIso I hI (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hU) (equation_regular U r d hd) := by
  exact normal_comparison_refinement
    (I.glueDataObjMap (X.affineBasicOpen_le r)) (I.glueData.ι U)
    (I.glueData.ι (X.affineBasicOpen r))
    (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r))
    (gluedConormalLine I hI)
    (PrincipalConormalTildeDual.conormalLine (I.ideal U)
      (gluedAffineIdealEquation I U d hU) hU.symm hd)
    (gluedAffineConormalTildePullbackIso I U d hU hd)
    (gluedAffineConormalTildePullbackIso I (X.affineBasicOpen r) (sectionMap U r d)
      (equation_span I U r d hU) (equation_regular U r d hd))
    (PrincipalConormalTildeDual.iso (I.ideal U)
      (gluedAffineIdealEquation I U d hU) hU.symm hd)
    (PrincipalConormalTildeDual.iso (I.ideal (X.affineBasicOpen r))
      (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hU))
      (equation_span I U r d hU).symm (equation_regular U r d hd))
    (tildeRefinementIso I U r d hU hd) (normalTildeRefinementIso I U r d hU hd)
    (GluedConormalTildeRefinement.tildePullbackIso_refinement I U r d hU hd)
    (GluedConormalBasicOpenDual.comparisonIso_eq I U r d hU hd)

end KltDP.Geometry.GluedConormalNormalRefinement
