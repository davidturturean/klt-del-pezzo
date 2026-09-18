import KltDP.Geometry.GluedAdjunctionAmbientChart
import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra
import KltDP.Geometry.AffineDifferentialExteriorPullbackComparison
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportComp

/-!
# The actual ambient affine exterior chart commutes with basic-open restriction

The original native exterior square and original intrinsic composition law
identify the same restriction map. Cancelling the original native exterior
isomorphisms proves compatibility of the actual ambient affine chart maps.
The smaller chart's standard smoothness is derived from localization.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement

open SchemeKaehlerSheaf GluedConormalBasicOpenLocalization

private theorem reframe_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A M P : C} {B N Q : D}
    (e : A ⟶ P) (e' : B ⟶ Q) (a : M ≅ P) (a' : N ≅ Q)
    (n : F.obj M ⟶ N) (i : F.obj P ⟶ Q) (c : F.obj A ⟶ B)
    (hn : F.map a.hom ≫ i = n ≫ a'.hom)
    (hc : F.map e ≫ i = c ≫ e') :
    F.map (e ≫ a.inv) ≫ n = c ≫ e' ≫ a'.inv := by
  apply (cancel_mono a'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [F.map_comp, Category.assoc, ← hn, ← Category.assoc (F.map a.inv),
    ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]
  exact hc

/-- Normalize the original frame solely in its abstract category. -/
private theorem frame_hom_word {C : Type*} [Category C] {P Q T W : C}
    (e : P ≅ Q) (t : Q ≅ T) (a : W ≅ T) (m : P ⟶ Q) (he : e.hom = m) :
    (e ≪≫ t ≪≫ a.symm).hom = (m ≫ t.hom) ≫ a.inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, he, Category.assoc]

/-- Specialize the checked categorical word at the original exterior map, with inferred type. -/
private def openFrame_hom {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g) (n : ℕ)
    {M : Y.Modules} (a : M ≅ SchemeExteriorPower.sheaf (baseRingSheaf g) n) :=
  frame_hom_word (SchemeKaehlerExteriorOpenRestriction.pullbackIso f j n)
    (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n) hg)) a
    (SchemeKaehlerExteriorPullbackMap.map f j n)
    (SchemeKaehlerExteriorOpenRestriction.pullbackIso_hom f j n)

/-- Name the exact original frame map so later proof types do not expand its isomorphisms. -/
private def originalFrameHom {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g) (n : ℕ)
    {M : Y.Modules} (a : M ≅ SchemeExteriorPower.sheaf (baseRingSheaf g) n) :
    (schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ⟶ M :=
  (SchemeKaehlerExteriorOpenRestriction.pullbackIso f j n ≪≫
    eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n) hg) ≪≫
    a.symm).hom

private theorem originalFrameHom_eq {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g) (n : ℕ)
    {M : Y.Modules} (a : M ≅ SchemeExteriorPower.sheaf (baseRingSheaf g) n) :
    originalFrameHom f j g hg n a =
      SchemeKaehlerExteriorPullbackTransport.map f j g hg n ≫ a.inv := by
  subst g
  simp only [originalFrameHom, SchemeKaehlerExteriorPullbackTransport.map,
    eqToIso_refl, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    Category.comp_id, Category.id_comp]
  exact congrArg (fun m => m ≫ a.inv)
    (SchemeKaehlerExteriorOpenRestriction.pullbackIso_hom f j n)

/-- Use the proved forward maps before a concrete smooth affine basis is substituted. -/
private theorem replace_frame_homs {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A P : C} {B Q : D} (a : A ≅ P) (a' : B ≅ Q)
    (m : A ⟶ P) (m' : B ⟶ Q) (ν : F.obj A ⟶ B) (i : F.obj P ⟶ Q)
    (ha : a.hom = m) (ha' : a'.hom = m') (h : F.map m ≫ i = ν ≫ m') :
    F.map a.hom ≫ i = ν ≫ a'.hom := by
  rw [ha, ha']
  exact h

private def native_frame_square (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R B] :=
  replace_frame_homs (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (AffineDifferentialExteriorTildeMap.standardSmoothIso R A)
    (AffineDifferentialExteriorTildeMap.standardSmoothIso R B)
    (AffineDifferentialExteriorTildeMap.map R A 2)
    (AffineDifferentialExteriorTildeMap.map R B 2)
    (AffineDifferentialExteriorPullbackComparison.nativeSheafMap R A B 2)
    (AffineDifferentialExteriorPullbackComparison.intrinsicMap R A B 2)
    (AffineDifferentialExteriorTildeMap.standardSmoothIso_hom R A)
    (AffineDifferentialExteriorTildeMap.standardSmoothIso_hom R B)
    (AffineDifferentialExteriorPullbackComparison.native_intrinsic_square R A B 2)

/-- Replace the normalized frames in the abstract category, including association. -/
private theorem reframe_original {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A M P : C} {B N Q T : D}
    (e : A ⟶ P) (e' : B ⟶ Q) (a : M ≅ P) (a' : N ≅ Q)
    (n : F.obj M ⟶ N) (i : F.obj P ⟶ Q) (c₁ : F.obj A ⟶ T) (c₂ : T ⟶ B)
    {x : A ⟶ M} {y : B ⟶ N}
    (hx : x = e ≫ a.inv) (hy : y = e' ≫ a'.inv)
    (hn : F.map a.hom ≫ i = n ≫ a'.hom)
    (hc : F.map e ≫ i = c₁ ≫ c₂ ≫ e') :
    F.map x ≫ n = c₁ ≫ c₂ ≫ y := by
  rw [hx, hy]
  exact (reframe_square F e e' a a' n i (c₁ ≫ c₂) hn
    (hc.trans (Category.assoc c₁ c₂ e').symm)).trans (Category.assoc c₁ c₂ _)

/-- Infer the original frame equality from the checked abstract replacement.
This avoids elaborating its same concrete scheme-module conclusion twice. -/
private def openFrame_refinement {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X) [IsOpenImmersion j]
    (l : Z ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g)
    (t : Z ⟶ X) [IsOpenImmersion t] (ht : l ≫ j = t)
    (q : Z ⟶ Spec (CommRingCat.of R)) (hq : l ≫ g = q) (hqt : t ≫ f = q)
    (n : ℕ) {M : Y.Modules} {N : Z.Modules}
    (a : M ≅ SchemeExteriorPower.sheaf (baseRingSheaf g) n)
    (a' : N ≅ SchemeExteriorPower.sheaf (baseRingSheaf q) n)
    (ν : (schemeModulePullback l).obj M ⟶ N)
    (hn : (schemeModulePullback l).map a.hom ≫
        SchemeKaehlerExteriorPullbackTransport.map g l q hq n = ν ≫ a'.hom) :=
  reframe_original (schemeModulePullback l)
    (SchemeKaehlerExteriorPullbackTransport.map f j g hg n)
    (SchemeKaehlerExteriorPullbackTransport.map f t q hqt n) a a' ν
    (SchemeKaehlerExteriorPullbackTransport.map g l q hq n)
    ((schemeModulePullbackCompIso l j).hom.app
      (SchemeExteriorPower.sheaf (baseRingSheaf f) n))
    (eqToIso (congrArg
      (fun s => (schemeModulePullback s).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n))
      ht)).hom
    (x := originalFrameHom f j g hg n a) (y := originalFrameHom f t q hqt n a')
    (originalFrameHom_eq f j g hg n a) (originalFrameHom_eq f t q hqt n a') hn
    (SchemeKaehlerExteriorPullbackTransport.map_comp f j l g hg t ht q hq hqt n)

/-- Check the original native-frame application while the two affine rings are independent. -/
private def affineFrame_refinement (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (t : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion t]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (ht : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j = t)
    (hqt : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  openFrame_refinement f j (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) hj t ht
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (AffineKaehlerPullbackComparison.baseMap_comp R A B) hqt 2
    (AffineDifferentialExteriorTildeMap.standardSmoothIso R A)
    (AffineDifferentialExteriorTildeMap.standardSmoothIso R B)
    (AffineDifferentialExteriorPullbackComparison.nativeSheafMap R A B 2)
    (by
      simpa only [AffineDifferentialExteriorPullbackComparison.intrinsicMap] using
        native_frame_square R A B)

/-- Specialize the checked composition at the actual basic open, with an inferred conclusion. -/
private def affineIso_refinement_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) (r : Γ(X, U.1)) :=
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  letI := GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
  letI := GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, (X.affineBasicOpen r).1) :=
      GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r
    affineFrame_refinement R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1)
      f U.2.fromSpec (X.affineBasicOpen r).2.fromSpec
      (GluedAdjunctionAmbientChart.affineBaseMap_comp f U)
      (U.2.map_fromSpec (X.affineBasicOpen r).2
        (homOfLE (X.affineBasicOpen_le r)).op)
      (GluedAdjunctionAmbientChart.affineBaseMap_comp f (X.affineBasicOpen r))

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) (r : Γ(X, U.1))

/-- The original native exterior restriction agrees with restriction of the actual global chart.
The transparent inferred proposition unfolds the two original `affineIso` definitions and
retains the same pullback composition and equality transport; no compatibility is assumed. -/
theorem affineIso_refinement :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    letI := GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
    letI := GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
    ∀ [hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      statementOf (affineIso_refinement_proof f U r hSmooth) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  letI := GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
  letI := GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
  intro hSmooth
  exact affineIso_refinement_proof f U r hSmooth

end KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement

namespace KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement

/-- The exact original frame map retained by the compiled refinement proof. -/
abbrev storedFrameHom := @originalFrameHom

/-- The already checked original affine refinement before section rings are substituted. -/
def storedAffineFrameRefinement := @affineFrame_refinement

end KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement

namespace KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement

/-- Reuse the checked equation for the original frame and the original transported map. -/
def storedFrameHom_transport := @originalFrameHom_eq

end KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement
