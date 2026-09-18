import KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement
import KltDP.Geometry.AffineAdjunctionAmbientPullbackSquare
import KltDP.Geometry.GluedAdjunctionAmbientSquarePasting
import KltDP.Geometry.GluedAdjunctionOriginalAffineNormalization

/-!
# The original global ambient adjunction factor on a basic-open refinement

The original native exterior square, quotient scalar square, and pullback
square pasting identify the actual ambient chart comparison on refinement.
The smaller chart's smoothness is derived from its original localization.
No compatibility of the original chart maps is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAmbientRefinement

open SchemeModulePullbackSquareCoherence GluedConormalBasicOpenLocalization
open SchemeKaehlerSheaf

private theorem inverse_frame_word {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A N : C} {A' N' : D} (e : A ≅ N) (e' : A' ≅ N')
    (ν : F.obj N ⟶ N') (r : F.obj A ⟶ A')
    (h : F.map e.hom ≫ ν = r ≫ e'.hom) :
    F.map e.inv ≫ r = ν ≫ e'.inv := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.map_inv_hom_id_assoc]

private def square_natural {X V Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
    (h : k ≫ g = j ≫ f) {M N : Y.Modules} (a : M ⟶ N) :=
  ((schemeModulePullbackCompIso k g ≪≫ eqToIso (congrArg schemeModulePullback h) ≪≫
    (schemeModulePullbackCompIso j f).symm).hom.naturality a)

/-- Retain the original composition component with the nested object telescope
used by the compiled affine equation, before any affine rings are substituted. -/
private def composition_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) :
    (schemeModulePullback f).obj ((schemeModulePullback g).obj M) ⟶
      (schemeModulePullback (f ≫ g)).obj M :=
  (schemeModulePullbackCompIso f g).hom.app M

/-- Check only the original affine equation with its explicit nested-object carriers. -/
private theorem normalize_frame_equation {X U V : Scheme.{u}}
    (g : U ⟶ X) (g' : V ⟶ X) (c : V ⟶ U) (hc : c ≫ g = g') (M : X.Modules)
    {N : U.Modules} {N' : V.Modules}
    {x : (schemeModulePullback g).obj M ⟶ N}
    {y : (schemeModulePullback g').obj M ⟶ N'}
    {ν : (schemeModulePullback c).obj N ⟶ N'}
    (hν : (schemeModulePullback c).map x ≫ ν = composition_hom c g M ≫
      (eqToIso (congrArg (fun q => (schemeModulePullback q).obj M) hc)).hom ≫ y) :
    (schemeModulePullback c).map x ≫ ν = composition_hom c g M ≫
      (eqToIso (congrArg (fun q => (schemeModulePullback q).obj M) hc)).hom ≫ y := hν

private theorem frame_square_pasting {X Y U V Q P : Scheme.{u}}
    (f : X ⟶ Y) (g : U ⟶ Y) (g' : V ⟶ Y)
    (j : Q ⟶ X) (j' : P ⟶ X) (k : Q ⟶ U) (k' : P ⟶ V)
    (b : P ⟶ Q) (c : V ⟶ U)
    (hU : k ≫ g = j ≫ f) (hV : k' ≫ g' = j' ≫ f)
    (hb : b ≫ j = j') (hc : c ≫ g = g') (hr : b ≫ k = k' ≫ c) (M : Y.Modules)
    {N : U.Modules} {N' : V.Modules}
    {x : (schemeModulePullback g).obj M ⟶ N}
    {y : (schemeModulePullback g').obj M ⟶ N'}
    {ν : (schemeModulePullback c).obj N ⟶ N'}
    (hν : (schemeModulePullback c).map x ≫ ν =
      composition_hom c g M ≫
        (eqToIso (congrArg (fun q => (schemeModulePullback q).obj M) hc)).hom ≫ y)
    (e : (schemeModulePullback g).obj M ≅ N)
    (e' : (schemeModulePullback g').obj M ≅ N')
    (he : e.hom = x) (he' : e'.hom = y)
    {δ : (schemeModulePullback b).obj ((schemeModulePullback k).obj N) ⟶
      (schemeModulePullback k').obj N'}
    (hδ : δ = (squareIso c k k' b hr N).hom ≫ (schemeModulePullback k').map ν) :
    (schemeModulePullback b).map
        ((schemeModulePullback k).map e.inv ≫ (squareIso f g j k hU M).hom) ≫
        (schemeModulePullbackCompIso b j).hom.app ((schemeModulePullback f).obj M) ≫
        (eqToIso (congrArg schemeModulePullback hb)).hom.app ((schemeModulePullback f).obj M) =
      δ ≫ (schemeModulePullback k').map e'.inv ≫ (squareIso f g' j' k' hV M).hom := by
  let r := (schemeModulePullbackCompIso c g).hom.app M ≫
    (eqToIso (congrArg schemeModulePullback hc)).hom.app M
  have hFrame : (schemeModulePullback c).map e.hom ≫ ν = r ≫ e'.hom := by
    simpa only [r, composition_hom, he, he', eqToIso.hom, eqToHom_app,
      Category.assoc] using hν
  have hInverse := inverse_frame_word (schemeModulePullback c) e e' ν r hFrame
  have hMappedInverse := congrArg (fun z => (schemeModulePullback k').map z) hInverse
  simp only [CategoryTheory.Functor.map_comp] at hMappedInverse
  have hNat := square_natural c k k' b hr e.inv
  change (schemeModulePullback b).map ((schemeModulePullback k).map e.inv) ≫
      (squareIso c k k' b hr ((schemeModulePullback g).obj M)).hom =
    (squareIso c k k' b hr N).hom ≫
      (schemeModulePullback k').map ((schemeModulePullback c).map e.inv) at hNat
  have hGrid := GluedAdjunctionAmbientSquarePasting.square_pasting
    f g g' j j' k k' b c hU hV hb hc hr M
  rw [hδ, (schemeModulePullback b).map_comp, Category.assoc, hGrid]
  change (schemeModulePullback b).map ((schemeModulePullback k).map e.inv) ≫
      (squareIso c k k' b hr ((schemeModulePullback g).obj M)).hom ≫
      (schemeModulePullback k').map r ≫ (squareIso f g' j' k' hV M).hom = _
  rw [← Category.assoc
    ((schemeModulePullback b).map ((schemeModulePullback k).map e.inv))
    (squareIso c k k' b hr ((schemeModulePullback g).obj M)).hom, hNat]
  calc
    _ = (squareIso c k k' b hr N).hom ≫
        ((schemeModulePullback k').map ((schemeModulePullback c).map e.inv) ≫
          (schemeModulePullback k').map r) ≫ (squareIso f g' j' k' hV M).hom := by
      simp only [Category.assoc]
    _ = _ := by
      rw [hMappedInverse]
      simp only [Category.assoc]

/-- Specialize the compiled quotient square independently of the ambient frame pasting. -/
private def original_quotient_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  let _ : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
  let _ : IsScalarTower R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
  AffineAdjunctionAmbientPullbackSquare.ambientRestriction_eq_square R
    Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U) (I.ideal (X.affineBasicOpen r))
    (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))

/-- Apply the exact stored affine equation while its rings remain independent.
The two actual frame isomorphisms are arguments, so the conclusion retains them. -/
private def affine_frame_square (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R B]
    {X Y Q P : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (d : Y ⟶ X)
    (g : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion g]
    (g' : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion g']
    (j : Q ⟶ Y) (j' : P ⟶ Y)
    (k : Q ⟶ Spec (CommRingCat.of A)) (k' : P ⟶ Spec (CommRingCat.of B))
    (b : P ⟶ Q)
    (hU : k ≫ g = j ≫ d) (hV : k' ≫ g' = j' ≫ d) (hb : b ≫ j = j')
    (hc : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ g = g')
    (hr : b ≫ k = k' ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hg' : g' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (e : (schemeModulePullback g).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) 2) ≅
      (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde)
    (e' : (schemeModulePullback g').obj (SchemeExteriorPower.sheaf (baseRingSheaf f) 2) ≅
      (ModuleCat.of B (⋀[B]^2 (KaehlerDifferential R B))).tilde)
    (he : e.hom = GluedAdjunctionAffineExteriorRefinement.storedFrameHom
      f g (Spec.map (CommRingCat.ofHom (algebraMap R A))) hg 2
      (AffineDifferentialExteriorTildeMap.standardSmoothIso R A))
    (he' : e'.hom = GluedAdjunctionAffineExteriorRefinement.storedFrameHom
      f g' (Spec.map (CommRingCat.ofHom (algebraMap R B))) hg' 2
      (AffineDifferentialExteriorTildeMap.standardSmoothIso R B)) :=
  frame_square_pasting d g g' j j' k k' b
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) hU hV hb hc hr
    (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)
    (GluedAdjunctionAffineExteriorRefinement.storedAffineFrameRefinement
      R A B f g g' hg hc hg')
    e e' he he' rfl


/-- Retain the original whole chart arrows before substituting concrete section rings. -/
private theorem retain_original_chart_maps {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S T : C} {S' T' W : D}
    {x : S ⟶ T} {x' : S' ⟶ T'} {c : F.obj T ⟶ W} {d : W ⟶ T'}
    {δ : F.obj S ⟶ S'} (h : F.map x ≫ c ≫ d = δ ≫ x')
    (a : S ⟶ T) (a' : S' ⟶ T') (ha : a = x) (ha' : a' = x') :
    F.map a ≫ c ≫ d = δ ≫ a' := by
  rw [ha, ha']
  exact h

/-- The already checked ring-level square with the actual whole chart maps as arguments. -/
private def affine_original_frame_square (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R B]
    {X Y Q P : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (d : Y ⟶ X)
    (g : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion g]
    (g' : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion g']
    (j : Q ⟶ Y) (j' : P ⟶ Y)
    (k : Q ⟶ Spec (CommRingCat.of A)) (k' : P ⟶ Spec (CommRingCat.of B))
    (b : P ⟶ Q)
    (hU : k ≫ g = j ≫ d) (hV : k' ≫ g' = j' ≫ d) (hb : b ≫ j = j')
    (hc : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ g = g')
    (hr : b ≫ k = k' ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hg' : g' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (e : (schemeModulePullback g).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) 2) ≅
      (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde)
    (e' : (schemeModulePullback g').obj (SchemeExteriorPower.sheaf (baseRingSheaf f) 2) ≅
      (ModuleCat.of B (⋀[B]^2 (KaehlerDifferential R B))).tilde)
    (he : e.hom = GluedAdjunctionAffineExteriorRefinement.storedFrameHom
      f g (Spec.map (CommRingCat.ofHom (algebraMap R A))) hg 2
      (AffineDifferentialExteriorTildeMap.standardSmoothIso R A))
    (he' : e'.hom = GluedAdjunctionAffineExteriorRefinement.storedFrameHom
      f g' (Spec.map (CommRingCat.ofHom (algebraMap R B))) hg' 2
      (AffineDifferentialExteriorTildeMap.standardSmoothIso R B))
    (α : (schemeModulePullback k).obj
        (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde ⟶
      (schemeModulePullback j).obj ((schemeModulePullback d).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)))
    (α' : (schemeModulePullback k').obj
        (ModuleCat.of B (⋀[B]^2 (KaehlerDifferential R B))).tilde ⟶
      (schemeModulePullback j').obj ((schemeModulePullback d).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)))
    (hα : α = (schemeModulePullback k).map e.inv ≫
      (squareIso d g j k hU (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)).hom)
    (hα' : α' = (schemeModulePullback k').map e'.inv ≫
      (squareIso d g' j' k' hV (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)).hom) :=
  retain_original_chart_maps (schemeModulePullback b)
    (affine_frame_square R A B f d g g' j j' k k' b hU hV hb hc hr hg hg' e e' he he')
    α α' hα hα'

/-- Check the exact original quotient-chart arrow on one arbitrary chart. -/
private theorem original_chart_hom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData) (U : X.affineOpens) :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      (GluedAdjunctionAmbientChart.iso f I U).hom =
        (schemeModulePullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))).map
          (GluedAdjunctionAmbientChart.affineIso f U).inv ≫
        (squareIso I.gluedTo U.2.fromSpec (I.glueData.ι U)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
          (GluedAdjunctionAmbientChart.chartMap_square I U)
          (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)).hom := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro hSmooth
  rfl

private def original_frame_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  let _ : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
  let _ : IsScalarTower R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, (X.affineBasicOpen r).1) :=
      GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r
    let φ := Ideal.Quotient.mk (I.ideal U)
    let φ' := Ideal.Quotient.mk (I.ideal (X.affineBasicOpen r))
    let ψ := quotientMap I U r
    let σ := algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1)
    let hRing := AffineAdjunctionAmbientScalarSquare.quotientMap_comp_mk
      Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U) (I.ideal (X.affineBasicOpen r))
      (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
    let hSpec := (AffineModuleTilde.specMap_comp_eq φ ψ).trans
      ((congrArg (fun ρ => Spec.map (CommRingCat.ofHom ρ)) hRing).trans
        (AffineModuleTilde.specMap_comp_eq σ φ').symm)
    affine_original_frame_square R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1)
      f I.gluedTo U.2.fromSpec (X.affineBasicOpen r).2.fromSpec
      (I.glueData.ι U) (I.glueData.ι (X.affineBasicOpen r))
      (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom φ'))
      (Spec.map (CommRingCat.ofHom ψ))
      (GluedAdjunctionAmbientChart.chartMap_square I U)
      (GluedAdjunctionAmbientChart.chartMap_square I (X.affineBasicOpen r))
      (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r))
      (U.2.map_fromSpec (X.affineBasicOpen r).2 (homOfLE (X.affineBasicOpen_le r)).op)
      hSpec (GluedAdjunctionAmbientChart.affineBaseMap_comp f U)
      (GluedAdjunctionAmbientChart.affineBaseMap_comp f (X.affineBasicOpen r))
      (GluedAdjunctionAmbientChart.affineIso f U)
      (GluedAdjunctionAmbientChart.affineIso f (X.affineBasicOpen r))
      (GluedAdjunctionOriginalAffineNormalization.nativeOriginalAffineHom f U hSmooth)
      (GluedAdjunctionOriginalAffineNormalization.nativeOriginalAffineHom f (X.affineBasicOpen r)
        (GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r))
      (GluedAdjunctionAmbientChart.iso f I U).hom
      (GluedAdjunctionAmbientChart.iso f I (X.affineBasicOpen r)).hom
      (original_chart_hom f I U)
      (original_chart_hom f I (X.affineBasicOpen r))

/-- Substitute an already checked original factor only after the frame square is instantiated. -/
private theorem substitute_right_factor {C : Type*} [Category C] {S T V : C}
    {a : S ⟶ V} {b c : S ⟶ T} {d : T ⟶ V}
    (h : a = b ≫ d) (hc : c = b) : a = c ≫ d :=
  h.trans (congrArg (fun q => q ≫ d) hc.symm)

/-- The original scalar square is pasted after the original frame square has been checked. -/
private def iso_refinement_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    substitute_right_factor (original_frame_square f I U r hSmooth)
      (original_quotient_square f I U r)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
  (U : X.affineOpens) (r : Γ(X, U.1))

/-- The original global ambient chart comparison respects the actual basic-open restriction.
The transparent proposition retains the original `GluedAdjunctionAmbientChart.iso` maps,
the original quotient-chart inclusion, and the original ambient module restriction. -/
theorem iso_refinement :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      statementOf (iso_refinement_proof f I U r hSmooth) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro hSmooth
  exact iso_refinement_proof f I U r hSmooth

end KltDP.Geometry.GluedAdjunctionAmbientRefinement
