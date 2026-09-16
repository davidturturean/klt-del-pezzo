import KltDP.Examples.FrobeniusExceptionalChartFrames
import KltDP.Geometry.AffineBlowupAmbientFrameComparison
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# Original conormal frames and the common ambient kernel

The comparisons below use the original restriction, pullback-unit and
pullback-composition maps. A local conormal equation frame is identified
with the pullback of its original local kernel equation. Quotient-chart
frames retain these maps under the actual glued chart isomorphism.

Reuse: the existing original-equation frame modules and the pinned
adjunction uniqueness API supply the comparisons. The newer official
pullback associativity theorem uses an API absent from the project pin;
SchemeModulePullbackCoherence supplies the bounded adapter for exactly
the original comparisons. No transition equality or line-bundle degree
is a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

open SchemeModuleRestriction

variable {X Y Z : Scheme.{u}}

/-- The conormal of the actual restriction is compared with the
pullback of the original global conormal along the original open. -/
def localConormalToGlobalPullbackIso (f : X ⟶ Y) (U : Y.Opens) :
    schemeConormalSheaf (f ∣_ U) ≅
      (schemeModulePullback (f ⁻¹ᵁ U).ι).obj (schemeConormalSheaf f) :=
  (schemeConormalRestrictionIso f U).symm ≪≫
    (restrictionIsoPullback (f ⁻¹ᵁ U).ι).app (schemeConormalSheaf f)

-- Cancel the original six factors before instantiating their scheme-module objects.
private theorem conormalIso_cancel_first_two
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {M₀ M₁ M₂ M₃ : D} {N₀ N₁ N₂ : C}
    (a : M₀ ≅ M₁) (b : M₁ ≅ M₂) (c : M₂ ≅ M₃)
    (d : M₃ ≅ P.obj N₀) (e : N₁ ≅ N₀) (q : N₁ ≅ N₂) :
    ((a ≪≫ b ≪≫ c ≪≫ d ≪≫ P.mapIso e.symm ≪≫ P.mapIso q).inv ≫ a.hom) ≫
        b.hom = P.map (q.inv ≫ e.hom) ≫ d.inv ≫ c.inv := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 800000 in
/-- This is the original kernel comparison after the actual square of
open restrictions is flattened by the original composition maps. -/
theorem localConormalToGlobalPullbackIso_kernel (f : X ⟶ Y) (U : Y.Opens) :
    (localConormalToGlobalPullbackIso f U).hom ≫
        (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).hom.app (schemeKernelIdeal f) =
      (schemeModulePullback (f ∣_ U)).map (localKernelToGlobalPullbackIso f U).hom ≫
        (schemeModulePullbackCompIso (f ∣_ U) U.ι).hom.app (schemeKernelIdeal f) ≫
          (eqToIso (congrArg schemeModulePullback (morphismRestrict_ι f U))).hom.app
            (schemeKernelIdeal f) := by
  let P := schemeModulePullback (f ∣_ U)
  let a := (restrictionIsoPullback (f ⁻¹ᵁ U).ι).app
    ((schemeModulePullback f).obj (schemeKernelIdeal f))
  let b := (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).app (schemeKernelIdeal f)
  let c := (eqToIso (congrArg schemeModulePullback
    (morphismRestrict_ι f U).symm)).app (schemeKernelIdeal f)
  let d := ((schemeModulePullbackCompIso (f ∣_ U) U.ι).app
    (schemeKernelIdeal f)).symm
  let e := (restrictionIsoPullback U.ι).app (schemeKernelIdeal f)
  let q := schemeKernelRestrictionIso f U
  change ((a ≪≫ b ≪≫ c ≪≫ d ≪≫ P.mapIso e.symm ≪≫ P.mapIso q).inv ≫ a.hom) ≫
    b.hom = P.map (q.inv ≫ e.hom) ≫ d.inv ≫ c.inv
  exact conormalIso_cancel_first_two P a b c d e q

/-- The original local conormal equation map, with target the actual
open pullback of the global conormal. -/
def localConormalGlobalFrame (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    _root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf ⟶
      (schemeModulePullback (f ⁻¹ᵁ U).ι).obj (schemeConormalSheaf f) :=
  schemeConormalGenerator (f ∣_ U) d hd ≫ (localConormalToGlobalPullbackIso f U).hom

/-- The original conormal equation becomes the actual pullback of the
same kernel equation under this canonical comparison. -/
theorem localConormalGlobalFrame_kernel (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    localConormalGlobalFrame f U d hd ≫
        (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).hom.app (schemeKernelIdeal f) =
      schemeModulePullbackFrame (f ∣_ U) (localKernelGlobalEquation f U d hd) ≫
        (schemeModulePullbackCompIso (f ∣_ U) U.ι).hom.app (schemeKernelIdeal f) ≫
          (eqToIso (congrArg schemeModulePullback (morphismRestrict_ι f U))).hom.app
            (schemeKernelIdeal f) := by
  rw [localConormalGlobalFrame, Category.assoc, localConormalToGlobalPullbackIso_kernel]
  simp only [schemeConormalGenerator, schemeModulePullbackFrame,
    localKernelGlobalEquation, Functor.map_comp, Category.assoc]

-- Share the original transported composite before substituting an overlap scheme.
private def normalizedCompositeFrame
    (h : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z) (hj : h ≫ i = j)
    {M : Z.Modules}
    (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ (schemeModulePullback i).obj M) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⟶ (schemeModulePullback j).obj M :=
  schemeModulePullbackFrame h s ≫ (schemeModulePullbackCompIso h i).hom.app M ≫
    (eqToIso (congrArg schemeModulePullback hj)).hom.app M

private theorem normalizedCompositeFrame_components
    (h : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z) (hj : h ≫ i = j)
    {M : Z.Modules}
    (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ (schemeModulePullback i).obj M) :
    normalizedCompositeFrame h i j hj s =
      schemeModulePullbackFrame h s ≫ (schemeModulePullbackCompIso h i).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hj)).hom.app M := rfl

-- Derive the same ambient endpoint from its existing inclusion equation.
-- Cancellation occurs on the open ambient chart before any closed pullback.
private theorem localKernel_refinement_eq_of_inclusion
    (f : X ⟶ Y) (U : Y.Opens) (d : Γ(U.toScheme, ⊤))
    (hd : (f ∣_ U).appTop d = 0) (g : Z ⟶ U.toScheme) (j : Z ⟶ Y)
    [IsOpenImmersion j] (h : g ≫ U.ι = j)
    (s : _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback j).obj (schemeKernelIdeal f))
    (hs : s ≫ pulledKernelInclusion f j = schemeScalarEnd (g.appTop d)) :
    s = kernelFrameRefinement f U.ι g (localKernelGlobalEquation f U d hd) ≫
      (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f) := by
  apply (pulledKernelInclusion_cancel f j _ _).mp
  rw [hs, Category.assoc, pulledKernelInclusion_congr f h,
    localKernelGlobalEquation_refinement_inclusion]

/-- Equality transport preserves the original normalized pullback of a map. -/
theorem schemeModulePullbackFrame_eqToIso {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    schemeModulePullbackFrame f s ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app M =
      schemeModulePullbackFrame g s := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- Reassociation of normalized frames uses the original comparison
isomorphisms. The two final morphism equalities only name the same actual
composites; the resulting reassociation is proved, rather than supplied. -/
theorem schemeModulePullbackFrame_flatten {W : Scheme.{u}}
    (e : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (j : X ⟶ Z) (l : W ⟶ Z)
    (hj : g ≫ h = j) (hl : e ≫ j = l) {M : Z.Modules}
    (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ (schemeModulePullback h).obj M) :
    schemeModulePullbackFrame e
        (schemeModulePullbackFrame g s ≫
          (schemeModulePullbackCompIso g h).hom.app M ≫
            (eqToIso (congrArg schemeModulePullback hj)).hom.app M) ≫
      (schemeModulePullbackCompIso e j).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hl)).hom.app M =
    schemeModulePullbackFrame (e ≫ g) s ≫
      (schemeModulePullbackCompIso (e ≫ g) h).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback
          ((Category.assoc e g h).trans
            ((congrArg (fun q : X ⟶ Z => e ≫ q) hj).trans hl)))).hom.app M := by
  subst j
  subst l
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    schemeModulePullbackFrame_postcomp, Category.assoc, eqToHom_app]
  rw [schemeModulePullbackCompIso_assoc]
  rw [← Category.assoc (schemeModulePullbackFrame e (schemeModulePullbackFrame g s)),
    schemeModulePullbackFrame_comp]
  simp only [eqToIso.hom, eqToHom_refl, Category.comp_id]

-- Compose the original equalities in an abstract category, without dependent rewrites.
private theorem frame_transport_chain
    {D : Type*} [Category D] {A B C E F G : D} {T : Type*}
    (Φ : T → (A ⟶ E)) (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ F)
    (t₀ t : F ⟶ G) (q : B ⟶ E) (p : E ⟶ G)
    {x y : T} {z : A ⟶ G}
    (hcomp : q ≫ p = b ≫ c ≫ t₀) (ht : t₀ = t)
    (hpost : Φ x = a ≫ q) (hxy : x = y)
    (hflat : Φ y ≫ p ≫ 𝟙 G = z) : a ≫ b ≫ c ≫ t = z := by
  have hcomp' : q ≫ p = b ≫ c ≫ t :=
    hcomp.trans (congrArg (fun v => b ≫ c ≫ v) ht)
  calc
    _ = (a ≫ q) ≫ p :=
      ((Category.assoc a q p).trans (congrArg (fun v => a ≫ v) hcomp')).symm
    _ = Φ x ≫ p := congrArg (fun v => v ≫ p) hpost.symm
    _ = Φ y ≫ p := congrArg (fun v => Φ v ≫ p) hxy
    _ = z := (congrArg (fun v => Φ y ≫ v) (Category.comp_id p).symm).trans hflat

-- Reuse the same flattening proof with the module and both original frames abstract.
private theorem pullbackFrame_kernel_transport
    {X₀ X₁ X₂ X₃ X₄ : Scheme.{u}}
    (g : X₀ ⟶ X₁) (i : X₁ ⟶ X₂) (f : X₂ ⟶ X₃)
    (r : X₁ ⟶ X₄) (j : X₄ ⟶ X₃) (h : r ≫ j = i ≫ f) (M : X₃.Modules)
    (s : _root_.SheafOfModules.unit X₁.ringCatSheaf ⟶
      (schemeModulePullback i).obj ((schemeModulePullback f).obj M))
    (t : _root_.SheafOfModules.unit X₄.ringCatSheaf ⟶
      (schemeModulePullback j).obj M)
    (hs : s ≫ (schemeModulePullbackCompIso i f).hom.app M =
      schemeModulePullbackFrame r t ≫ (schemeModulePullbackCompIso r j).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app M) :
    schemeModulePullbackFrame g s ≫
        (schemeModulePullbackCompIso g i).hom.app ((schemeModulePullback f).obj M) ≫
          (schemeModulePullbackCompIso (g ≫ i) f).hom.app M ≫
            (eqToIso (congrArg schemeModulePullback (Category.assoc g i f))).hom.app M =
      schemeModulePullbackFrame (g ≫ r) t ≫
        (schemeModulePullbackCompIso (g ≫ r) j).hom.app M ≫
          (eqToIso (congrArg schemeModulePullback
            ((Category.assoc g r j).trans (congrArg (fun q => g ≫ q) h)))).hom.app M := by
  exact frame_transport_chain
    (fun v : _root_.SheafOfModules.unit X₁.ringCatSheaf ⟶
        (schemeModulePullback (i ≫ f)).obj M => schemeModulePullbackFrame g v)
    (schemeModulePullbackFrame g s)
    ((schemeModulePullbackCompIso g i).hom.app ((schemeModulePullback f).obj M))
    ((schemeModulePullbackCompIso (g ≫ i) f).hom.app M)
    ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj M)
      (Category.assoc g i f))).hom)
    ((eqToIso (congrArg schemeModulePullback (Category.assoc g i f))).hom.app M)
    ((schemeModulePullback g).map ((schemeModulePullbackCompIso i f).hom.app M))
    ((schemeModulePullbackCompIso g (i ≫ f)).hom.app M)
    (schemeModulePullbackCompIso_assoc g i f M)
    (eqToHom_app (congrArg schemeModulePullback (Category.assoc g i f)) M).symm
    (schemeModulePullbackFrame_postcomp g s ((schemeModulePullbackCompIso i f).hom.app M))
    hs
    (schemeModulePullbackFrame_flatten (M := M) g r j (i ≫ f) (g ≫ (i ≫ f)) h rfl t)

/-- Pulling the original local conormal frame farther back and then
flattening to the global kernel gives the original local kernel frame.
The two routes have the same actual composite scheme morphism. -/
theorem localConormalGlobalFrame_pullback_kernel (f : X ⟶ Y) (U : Y.Opens)
    (g : Z ⟶ (f ⁻¹ᵁ U).toScheme)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    schemeModulePullbackFrame g (localConormalGlobalFrame f U d hd) ≫
        (schemeModulePullbackCompIso g (f ⁻¹ᵁ U).ι).hom.app (schemeConormalSheaf f) ≫
          (schemeModulePullbackCompIso (g ≫ (f ⁻¹ᵁ U).ι) f).hom.app
            (schemeKernelIdeal f) ≫
            (eqToIso (congrArg schemeModulePullback
              (Category.assoc g (f ⁻¹ᵁ U).ι f))).hom.app (schemeKernelIdeal f) =
      schemeModulePullbackFrame (g ≫ (f ∣_ U)) (localKernelGlobalEquation f U d hd) ≫
        (schemeModulePullbackCompIso (g ≫ (f ∣_ U)) U.ι).hom.app (schemeKernelIdeal f) ≫
          (eqToIso (congrArg schemeModulePullback
            ((Category.assoc g (f ∣_ U) U.ι).trans
              (congrArg (fun q => g ≫ q) (morphismRestrict_ι f U))))).hom.app
                (schemeKernelIdeal f) := by
  exact pullbackFrame_kernel_transport g (f ⁻¹ᵁ U).ι f (f ∣_ U) U.ι
    (morphismRestrict_ι f U) (schemeKernelIdeal f)
    (localConormalGlobalFrame f U d hd) (localKernelGlobalEquation f U d hd)
    (localConormalGlobalFrame_kernel f U d hd)

private theorem frameComposite_congr {g g' : Z ⟶ X} (hg : g = g')
    (h : X ⟶ Y) (l : Z ⟶ Y) (hl : g ≫ h = l) (hl' : g' ≫ h = l)
    {M : Y.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ (schemeModulePullback h).obj M) :
    schemeModulePullbackFrame g s ≫ (schemeModulePullbackCompIso g h).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hl)).hom.app M =
      schemeModulePullbackFrame g' s ≫ (schemeModulePullbackCompIso g' h).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hl')).hom.app M := by
  subst g'
  rfl

/-- The actual local quotient square supplies the common ambient
composite, using the original restricted-morphism identity. -/
theorem localQuotientSquare_base {W : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (g : Z ⟶ (f ⁻¹ᵁ U).toScheme) (q : Z ⟶ W) (v : W ⟶ U.toScheme)
    (hsquare : g ≫ (f ∣_ U) = q ≫ v) :
    (g ≫ (f ⁻¹ᵁ U).ι) ≫ f = q ≫ (v ≫ U.ι) := by
  rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hsquare, Category.assoc]

set_option maxHeartbeats 800000 in
/-- The original local conormal frame, through the actual quotient
square, becomes the pullback of its original common-ambient kernel frame.
Only an equality of the actual scheme maps is required; no frame
agreement, coefficient, or preservation of monomorphisms is assumed. -/
theorem localConormalGlobalFrame_common_ambient {W : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (g : Z ⟶ (f ⁻¹ᵁ U).toScheme)
    (q : Z ⟶ W) (v : W ⟶ U.toScheme)
    (hsquare : g ≫ (f ∣_ U) = q ≫ v)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    schemeModulePullbackFrame g (localConormalGlobalFrame f U d hd) ≫
        (schemeModulePullbackCompIso g (f ⁻¹ᵁ U).ι).hom.app (schemeConormalSheaf f) ≫
          (schemeModulePullbackCompIso (g ≫ (f ⁻¹ᵁ U).ι) f).hom.app
            (schemeKernelIdeal f) ≫
            (eqToIso (congrArg schemeModulePullback
              (localQuotientSquare_base f U g q v hsquare))).hom.app (schemeKernelIdeal f) ≫
              (schemeModulePullbackCompIso q (v ≫ U.ι)).inv.app (schemeKernelIdeal f) =
      schemeModulePullbackFrame q
        (kernelFrameRefinement f U.ι v (localKernelGlobalEquation f U d hd)) := by
  apply (cancel_mono ((schemeModulePullbackCompIso q (v ≫ U.ι)).hom.app
    (schemeKernelIdeal f))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have htail : g ≫ ((f ⁻¹ᵁ U).ι ≫ f) = q ≫ (v ≫ U.ι) := by
    rw [← morphismRestrict_ι, ← Category.assoc, hsquare, Category.assoc]
  have hlocal : (g ≫ (f ∣_ U)) ≫ U.ι = q ≫ (v ≫ U.ι) := by
    rw [hsquare, Category.assoc]
  have H := congrArg (fun z => z ≫
      (eqToIso (congrArg schemeModulePullback htail)).hom.app (schemeKernelIdeal f))
    (localConormalGlobalFrame_pullback_kernel f U g d hd)
  calc
    _ = schemeModulePullbackFrame (g ≫ (f ∣_ U)) (localKernelGlobalEquation f U d hd) ≫
        (schemeModulePullbackCompIso (g ≫ (f ∣_ U)) U.ι).hom.app (schemeKernelIdeal f) ≫
          (eqToIso (congrArg schemeModulePullback hlocal)).hom.app
            (schemeKernelIdeal f) := by
      simpa only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans] using H
    _ = schemeModulePullbackFrame (q ≫ v) (localKernelGlobalEquation f U d hd) ≫
        (schemeModulePullbackCompIso (q ≫ v) U.ι).hom.app (schemeKernelIdeal f) ≫
          (eqToIso (congrArg schemeModulePullback (Category.assoc q v U.ι))).hom.app
            (schemeKernelIdeal f) :=
      frameComposite_congr hsquare U.ι (q ≫ (v ≫ U.ι)) hlocal (Category.assoc q v U.ι)
        (localKernelGlobalEquation f U d hd)
    _ = _ := by
      symm
      simpa only [kernelFrameRefinement, eqToIso_refl, Iso.refl_hom,
        NatTrans.id_app, Category.comp_id] using
        schemeModulePullbackFrame_flatten (M := schemeKernelIdeal f)
          q v U.ι (v ≫ U.ι) (q ≫ (v ≫ U.ι)) rfl rfl
          (localKernelGlobalEquation f U d hd)

/-- Named actual global and ambient maps retain the same derived square. -/
theorem localQuotientSquare_named_base {W : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (g : Z ⟶ (f ⁻¹ᵁ U).toScheme) (q : Z ⟶ W) (v : W ⟶ U.toScheme)
    (j : Z ⟶ X) (w : W ⟶ Y)
    (hj : g ≫ (f ⁻¹ᵁ U).ι = j) (hw : v ≫ U.ι = w)
    (hsquare : g ≫ (f ∣_ U) = q ≫ v) : j ≫ f = q ≫ w := by
  rw [← hj, ← hw]
  exact localQuotientSquare_base f U g q v hsquare

/-- The same canonical comparison with the original global and ambient
map names retained. These names do not change the original equation frame. -/
theorem localConormalGlobalFrame_named_common_ambient {W : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (g : Z ⟶ (f ⁻¹ᵁ U).toScheme)
    (q : Z ⟶ W) (v : W ⟶ U.toScheme) (j : Z ⟶ X) (w : W ⟶ Y)
    (hj : g ≫ (f ⁻¹ᵁ U).ι = j) (hw : v ≫ U.ι = w)
    (hsquare : g ≫ (f ∣_ U) = q ≫ v)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    (schemeModulePullbackFrame g (localConormalGlobalFrame f U d hd) ≫
        (schemeModulePullbackCompIso g (f ⁻¹ᵁ U).ι).hom.app (schemeConormalSheaf f) ≫
          (eqToIso (congrArg schemeModulePullback hj)).hom.app (schemeConormalSheaf f)) ≫
      (schemeModulePullbackCompIso j f).hom.app (schemeKernelIdeal f) ≫
        (eqToIso (congrArg schemeModulePullback
          (localQuotientSquare_named_base f U g q v j w hj hw hsquare))).hom.app
            (schemeKernelIdeal f) ≫
          (schemeModulePullbackCompIso q w).inv.app (schemeKernelIdeal f) =
      schemeModulePullbackFrame q
        (kernelFrameRefinement f U.ι v (localKernelGlobalEquation f U d hd) ≫
          (eqToIso (congrArg schemeModulePullback hw)).hom.app (schemeKernelIdeal f)) := by
  subst j
  subst w
  simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Category.assoc] using localConormalGlobalFrame_common_ambient f U g q v hsquare d hd

-- Normalize the same comparison and substitute the already-proved frame equality
-- while the schemes and local equation are still abstract.
private theorem localConormalGlobalFrame_named_comparison {W : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (g : Z ⟶ (f ⁻¹ᵁ U).toScheme)
    (q : Z ⟶ W) (v : W ⟶ U.toScheme) (j : Z ⟶ X) (w : W ⟶ Y)
    (hj : g ≫ (f ⁻¹ᵁ U).ι = j) (hw : v ≫ U.ι = w)
    (hsquare : g ≫ (f ∣_ U) = q ≫ v)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0)
    (s : _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback j).obj (schemeConormalSheaf f))
    (hs : s = schemeModulePullbackFrame g (localConormalGlobalFrame f U d hd) ≫
      (schemeModulePullbackCompIso g (f ⁻¹ᵁ U).ι).hom.app (schemeConormalSheaf f) ≫
        (eqToIso (congrArg schemeModulePullback hj)).hom.app (schemeConormalSheaf f))
    (hbase : j ≫ f = q ≫ w)
    (comparison : (schemeModulePullback j).obj (schemeConormalSheaf f) ≅
      (schemeModulePullback q).obj ((schemeModulePullback w).obj (schemeKernelIdeal f)))
    (hcomparison : comparison.hom =
      ((schemeModulePullbackCompIso j f).app (schemeKernelIdeal f) ≪≫
        (eqToIso (congrArg schemeModulePullback hbase)).app (schemeKernelIdeal f) ≪≫
          ((schemeModulePullbackCompIso q w).app (schemeKernelIdeal f)).symm).hom)
    (ambientFrame : _root_.SheafOfModules.unit W.ringCatSheaf ⟶
      (schemeModulePullback w).obj (schemeKernelIdeal f))
    (hambientFrame : ambientFrame =
      kernelFrameRefinement f U.ι v (localKernelGlobalEquation f U d hd) ≫
        (eqToIso (congrArg schemeModulePullback hw)).hom.app (schemeKernelIdeal f)) :
    s ≫ comparison.hom = schemeModulePullbackFrame q ambientFrame := by
  rw [hcomparison]
  subst ambientFrame
  rw [hs]
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc] using
    localConormalGlobalFrame_named_common_ambient f U g q v j w hj hw hsquare d hd

private theorem restrictionFrame_comparison (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    (restrictionUnitIso f).inv ≫ (restriction f).map s ≫
        (restrictionIsoPullback f).hom.app M = schemeModulePullbackFrame f s := by
  rw [(restrictionIsoPullback f).hom.naturality s]
  have hu : (restrictionUnitIso f).inv ≫
      (restrictionIsoPullback f).hom.app (_root_.SheafOfModules.unit Y.ringCatSheaf) =
        (schemeModulePullbackUnitIso f).inv := by
    apply (cancel_mono (schemeModulePullbackUnitIso f).hom).mp
    rw [Category.assoc, restrictionIsoPullback_unit, Iso.inv_hom_id, Iso.inv_hom_id]
  rw [← Category.assoc, hu]
  rfl

/-- The original quotient-chart frame, before any change of ambient
chart, is exactly the normalized pullback of the original local frame.
Its actual map to the glued closed scheme is retained. -/
theorem gluedAffineConormalChartFrameIso_global
    (I : Y.IdealSheafData) (U : Y.affineOpens) (d : Γ(Y, U.1))
    (hI : I.ideal U = Ideal.span {d}) (hregular : d ∈ nonZeroDivisors Γ(Y, U.1)) :
    (gluedAffineConormalChartFrameIso I U d hI hregular).hom =
      schemeModulePullbackFrame (I.glueDataObjIso U).hom
          (localConormalGlobalFrame I.gluedTo U.1 (gluedAffineEquation U d)
            (gluedAffineEquation_eq_zero I U d hI)) ≫
        (schemeModulePullbackCompIso (I.glueDataObjIso U).hom
          (I.gluedTo ⁻¹ᵁ U.1).ι).hom.app (schemeConormalSheaf I.gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback (I.glueDataObjIso_hom_ι U))).hom.app
            (schemeConormalSheaf I.gluedTo) := by
  simp only [gluedAffineConormalChartFrameIso, gluedAffineGlobalConormalUnitIso,
    gluedAffineGlobalConormalPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← Category.assoc ((restriction (I.glueDataObjIso U).hom).map _),
    ← Category.assoc (restrictionUnitIso (I.glueDataObjIso U).hom).inv,
    restrictionFrame_comparison (I.glueDataObjIso U).hom
      ((gluedAffineConormalIso I U d hI hregular).hom ≫
        (schemeConormalRestrictionIso I.gluedTo U.1).inv)]
  simp only [schemeModulePullbackFrame, localConormalGlobalFrame,
    localConormalToGlobalPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rfl

-- Keep the named composite in the theorem type before specializing the schemes.
private theorem pullbackFrame_flatten_named {W : Scheme.{u}}
    (e : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (j : X ⟶ Z) (t : W ⟶ Y) (l : W ⟶ Z)
    (hj : g ≫ h = j) (ht : e ≫ g = t) (hl : e ≫ j = l) (htl : t ≫ h = l)
    {M : Z.Modules}
    (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ (schemeModulePullback h).obj M) :
    schemeModulePullbackFrame e
        (schemeModulePullbackFrame g s ≫
          (schemeModulePullbackCompIso g h).hom.app M ≫
            (eqToIso (congrArg schemeModulePullback hj)).hom.app M) ≫
      (schemeModulePullbackCompIso e j).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hl)).hom.app M =
    schemeModulePullbackFrame t s ≫
      (schemeModulePullbackCompIso t h).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback htl)).hom.app M := by
  subst t
  exact schemeModulePullbackFrame_flatten e g h j l hj hl s

namespace AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The original local quotient-chart map reaches the original global
exceptional chart through the actual restricted-open inclusion. -/
@[reassoc] theorem originalExceptionalChartLocalMap_ι :
    originalExceptionalChartLocalMap I a ≫
        ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι =
      originalExceptionalChartMap I a := by
  rw [originalExceptionalChartLocalMap, Category.assoc,
    (exceptionalIdeal I).glueDataObjIso_hom_ι]
  exact exceptionalGluedChartIso_hom_toExceptional I a

set_option maxHeartbeats 800000 in
/-- The original global conormal frame is normalized through its actual
restricted quotient chart. This retains all original composition maps. -/
theorem originalExceptionalChartFrameIso_global :
    (originalExceptionalChartFrameIso I a).hom =
      schemeModulePullbackFrame (originalExceptionalChartLocalMap I a)
          (localConormalGlobalFrame (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
            (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
            (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
              (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))) ≫
        (schemeModulePullbackCompIso (originalExceptionalChartLocalMap I a)
          ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι).hom.app
            (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback
            (originalExceptionalChartLocalMap_ι I a))).hom.app
              (schemeConormalSheaf (exceptionalIdeal I).gluedTo) := by
  simp only [originalExceptionalChartFrameIso, originalExceptionalChartPullbackIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change schemeModulePullbackFrame (exceptionalGluedChartIso I a).hom
      (gluedAffineConormalChartFrameIso (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)
        (chartEquationSection_regular I a)).hom ≫
      (schemeModulePullbackCompIso (exceptionalGluedChartIso I a).hom
        ((exceptionalIdeal I).glueData.ι (chartAffineOpen I a))).hom.app _ ≫
        (eqToIso (congrArg schemeModulePullback
          (exceptionalGluedChartIso_hom_toExceptional I a))).hom.app _ = _
  rw [gluedAffineConormalChartFrameIso_global]
  exact pullbackFrame_flatten_named
    (M := schemeConormalSheaf (exceptionalIdeal I).gluedTo)
    (exceptionalGluedChartIso I a).hom
    ((exceptionalIdeal I).glueDataObjIso (chartAffineOpen I a)).hom
    ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι
    ((exceptionalIdeal I).glueData.ι (chartAffineOpen I a))
    (originalExceptionalChartLocalMap I a) (originalExceptionalChartMap I a)
    ((exceptionalIdeal I).glueDataObjIso_hom_ι (chartAffineOpen I a)) rfl
    (exceptionalGluedChartIso_hom_toExceptional I a)
    (originalExceptionalChartLocalMap_ι I a)
    (localConormalGlobalFrame (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
      (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
      (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)))

/-- This is the original quotient square, including the original ambient
coordinate isomorphism used to transport the equation section. -/
@[reassoc] theorem originalExceptionalChartLocalMap_restrict :
    originalExceptionalChartLocalMap I a ≫
        ((exceptionalIdeal I).gluedTo ∣_ (chartAffineOpen I a).1) =
      exceptionalChartInclusion I a ≫ (chartAmbientIso I a).hom := by
  apply (cancel_mono (chartAffineOpen I a).1.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    originalExceptionalChartLocalMap_ι, Category.assoc, chartAmbientIso_hom_ι]
  change (exceptionalChartToFiber I a ≫ (exceptionalFiberIso I).inv) ≫
      exceptionalι I = exceptionalChartInclusion I a ≫ chartι I a
  simp only [Category.assoc, exceptionalFiberIso_inv_ι, exceptionalChartToFiber_ι,
    exceptionalChartToBlowup]

/-- The actual exceptional overlap is the quotient of the actual common
ambient Rees chart. Its closed map is kept separate from open immersions. -/
def exceptionalOverlapAmbientInclusion : exceptionalOverlapScheme I a b ⟶
    Spec (CommRingCat.of (conormalOverlapRing I a b)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (conormalOverlapIdeal I a b)))

/-- The original left quotient-chart route is exactly the left route
from the actual ambient quotient square. -/
theorem exceptionalOverlap_left_local_square :
    (exceptionalOverlapLeftMorphism I a b ≫ originalExceptionalChartLocalMap I a) ≫
        ((exceptionalIdeal I).gluedTo ∣_ (chartAffineOpen I a).1) =
      exceptionalOverlapAmbientInclusion I a b ≫ overlapToLeftAmbient I a b := by
  rw [Category.assoc, originalExceptionalChartLocalMap_restrict,
    ← Category.assoc, exceptionalOverlapLeftMorphism_inclusion]
  exact Category.assoc _ _ _

/-- The original right quotient-chart route obeys the same actual square,
using the original second ambient equation rather than a chosen frame. -/
theorem exceptionalOverlap_right_local_square :
    (exceptionalOverlapRightMorphism I a b ≫ originalExceptionalChartLocalMap I b) ≫
        ((exceptionalIdeal I).gluedTo ∣_ (chartAffineOpen I b).1) =
      exceptionalOverlapAmbientInclusion I a b ≫ overlapToRightAmbient I a b := by
  rw [Category.assoc, originalExceptionalChartLocalMap_restrict,
    ← Category.assoc, exceptionalOverlapRightMorphism_inclusion]
  exact Category.assoc _ _ _

/-- The original exceptional overlap map into the glued exceptional scheme. -/
def originalExceptionalOverlapMap : exceptionalOverlapScheme I a b ⟶ exceptionalScheme I :=
  exceptionalOverlapLeftMorphism I a b ≫ originalExceptionalChartMap I a

theorem originalExceptionalOverlapMap_right :
    exceptionalOverlapRightMorphism I a b ≫ originalExceptionalChartMap I b =
      originalExceptionalOverlapMap I a b := by
  simpa only [originalExceptionalOverlapMap, originalExceptionalChartMap, Category.assoc] using
    congrArg (fun z => z ≫ (exceptionalFiberIso I).inv)
      (exceptionalOverlap_morphism_condition I a b).symm

theorem originalExceptionalOverlapMap_local_left :
    (exceptionalOverlapLeftMorphism I a b ≫ originalExceptionalChartLocalMap I a) ≫
        ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι =
      originalExceptionalOverlapMap I a b := by
  rw [Category.assoc, originalExceptionalChartLocalMap_ι]
  rfl

theorem originalExceptionalOverlapMap_local_right :
    (exceptionalOverlapRightMorphism I a b ≫ originalExceptionalChartLocalMap I b) ≫
        ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I b).1).ι =
      originalExceptionalOverlapMap I a b := by
  rw [Category.assoc, originalExceptionalChartLocalMap_ι,
    originalExceptionalOverlapMap_right]

/-- Both actual overlap routes retain the original global frame
normalization after their original map names have been identified. -/
theorem originalExceptionalChartFrameIso_refinement_global {T : Scheme.{u}}
    (h : T ⟶ exceptionalChart I a) (j : T ⟶ exceptionalScheme I)
    (hj : h ≫ originalExceptionalChartMap I a = j) :
    schemeModulePullbackFrame h (originalExceptionalChartFrameIso I a).hom ≫
        (schemeModulePullbackCompIso h (originalExceptionalChartMap I a)).hom.app
          (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback hj)).hom.app
            (schemeConormalSheaf (exceptionalIdeal I).gluedTo) =
      schemeModulePullbackFrame (h ≫ originalExceptionalChartLocalMap I a)
          (localConormalGlobalFrame (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
            (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
            (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
              (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))) ≫
        (schemeModulePullbackCompIso (h ≫ originalExceptionalChartLocalMap I a)
          ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι).hom.app
            (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback
            ((Category.assoc h (originalExceptionalChartLocalMap I a)
              ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι).trans
                ((congrArg (fun z => h ≫ z) (originalExceptionalChartLocalMap_ι I a)).trans
                  hj)))).hom.app (schemeConormalSheaf (exceptionalIdeal I).gluedTo) := by
  rw [originalExceptionalChartFrameIso_global]
  exact schemeModulePullbackFrame_flatten h (originalExceptionalChartLocalMap I a)
    ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι
    (originalExceptionalChartMap I a) j (originalExceptionalChartLocalMap_ι I a) hj _

-- Keep the overlap map and its local-route equality abstract during conversion.
private theorem originalExceptionalChartFrameIso_refinement_named {T : Scheme.{u}}
    (h : T ⟶ exceptionalChart I a) (j : T ⟶ exceptionalScheme I)
    (hj : h ≫ originalExceptionalChartMap I a = j)
    (hlocal : (h ≫ originalExceptionalChartLocalMap I a) ≫
      ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι = j) :
    normalizedCompositeFrame h (originalExceptionalChartMap I a) j hj
        (originalExceptionalChartFrameIso I a).hom =
      schemeModulePullbackFrame (h ≫ originalExceptionalChartLocalMap I a)
          (localConormalGlobalFrame (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
            (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
            (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
              (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))) ≫
        (schemeModulePullbackCompIso (h ≫ originalExceptionalChartLocalMap I a)
          ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).ι).hom.app
            (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback hlocal)).hom.app
            (schemeConormalSheaf (exceptionalIdeal I).gluedTo) :=
  originalExceptionalChartFrameIso_refinement_global I a h j hj

/-- Pullback of the actual left global conormal frame to its original overlap. -/
def originalOverlapFrameLeft :
    _root_.SheafOfModules.unit (exceptionalOverlapScheme I a b).ringCatSheaf ⟶
      (schemeModulePullback (originalExceptionalOverlapMap I a b)).obj
        (schemeConormalSheaf (exceptionalIdeal I).gluedTo) :=
  schemeModulePullbackFrame (exceptionalOverlapLeftMorphism I a b)
      (originalExceptionalChartFrameIso I a).hom ≫
    (schemeModulePullbackCompIso (exceptionalOverlapLeftMorphism I a b)
      (originalExceptionalChartMap I a)).hom.app _

/-- Pullback of the actual right frame to that same original global module. -/
def originalOverlapFrameRight :
    _root_.SheafOfModules.unit (exceptionalOverlapScheme I a b).ringCatSheaf ⟶
      (schemeModulePullback (originalExceptionalOverlapMap I a b)).obj
        (schemeConormalSheaf (exceptionalIdeal I).gluedTo) :=
  normalizedCompositeFrame
    (M := schemeConormalSheaf (exceptionalIdeal I).gluedTo)
    (exceptionalOverlapRightMorphism I a b) (originalExceptionalChartMap I b)
    (originalExceptionalOverlapMap I a b) (originalExceptionalOverlapMap_right I a b)
    (originalExceptionalChartFrameIso I b).hom

/-- The global exceptional map and actual ambient quotient give one
common composite into the original blowup. -/
theorem originalExceptionalOverlapMap_base :
    originalExceptionalOverlapMap I a b ≫ (exceptionalIdeal I).gluedTo =
      exceptionalOverlapAmbientInclusion I a b ≫ ambientOverlapMap I a b :=
  localQuotientSquare_named_base (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
    (exceptionalOverlapLeftMorphism I a b ≫ originalExceptionalChartLocalMap I a)
    (exceptionalOverlapAmbientInclusion I a b) (overlapToLeftAmbient I a b)
    (originalExceptionalOverlapMap I a b) (ambientOverlapMap I a b)
    (originalExceptionalOverlapMap_local_left I a b) rfl
    (exceptionalOverlap_left_local_square I a b)

/-- The same canonical comparison is used for both actual frames. It
depends only on the actual global overlap and ambient quotient maps. -/
def originalOverlapKernelComparisonIso :
    (schemeModulePullback (originalExceptionalOverlapMap I a b)).obj
        (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≅
      (schemeModulePullback (exceptionalOverlapAmbientInclusion I a b)).obj
        ((schemeModulePullback (ambientOverlapMap I a b)).obj
          (schemeKernelIdeal (exceptionalIdeal I).gluedTo)) :=
  (schemeModulePullbackCompIso (originalExceptionalOverlapMap I a b)
    (exceptionalIdeal I).gluedTo).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback (originalExceptionalOverlapMap_base I a b))).app _ ≪≫
    ((schemeModulePullbackCompIso (exceptionalOverlapAmbientInclusion I a b)
      (ambientOverlapMap I a b)).app _).symm

/-- The actual left global frame agrees with the left ambient kernel
frame under the one canonical comparison, including the closed pullback. -/
theorem originalOverlapFrameLeft_comparison :
    originalOverlapFrameLeft I a b ≫ (originalOverlapKernelComparisonIso I a b).hom =
      schemeModulePullbackFrame (exceptionalOverlapAmbientInclusion I a b)
        (leftAmbientKernelFrame I a b) := by
  have hf := originalExceptionalChartFrameIso_refinement_global I a
    (exceptionalOverlapLeftMorphism I a b) (originalExceptionalOverlapMap I a b) rfl
  have H := localConormalGlobalFrame_named_common_ambient
    (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
    (exceptionalOverlapLeftMorphism I a b ≫ originalExceptionalChartLocalMap I a)
    (exceptionalOverlapAmbientInclusion I a b) (overlapToLeftAmbient I a b)
    (originalExceptionalOverlapMap I a b) (ambientOverlapMap I a b)
    (originalExceptionalOverlapMap_local_left I a b) rfl
    (exceptionalOverlap_left_local_square I a b)
    (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
    (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
      (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))
  rw [← hf] at H
  simpa only [originalOverlapFrameLeft, originalOverlapKernelComparisonIso,
    leftAmbientKernelFrame, Iso.trans_hom, Iso.symm_hom, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.assoc] using H

-- Check the original concrete endpoint conversions separately from normalization.
private theorem originalOverlapFrameRight_local_refinement :
    originalOverlapFrameRight I a b =
      schemeModulePullbackFrame
          (exceptionalOverlapRightMorphism I a b ≫ originalExceptionalChartLocalMap I b)
          (localConormalGlobalFrame (exceptionalIdeal I).gluedTo (chartAffineOpen I b).1
            (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))
            (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I b)
              (chartEquationSection I b) (exceptionalIdeal_chartEquationSection I b))) ≫
        (schemeModulePullbackCompIso
          (exceptionalOverlapRightMorphism I a b ≫ originalExceptionalChartLocalMap I b)
          ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I b).1).ι).hom.app
            (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback
            (originalExceptionalOverlapMap_local_right I a b))).hom.app
              (schemeConormalSheaf (exceptionalIdeal I).gluedTo) :=
  originalExceptionalChartFrameIso_refinement_named I b
    (exceptionalOverlapRightMorphism I a b) (originalExceptionalOverlapMap I a b)
    (originalExceptionalOverlapMap_right I a b)
    (originalExceptionalOverlapMap_local_right I a b)

private theorem originalOverlapKernelComparisonIso_hom_components :
    (originalOverlapKernelComparisonIso I a b).hom =
      ((schemeModulePullbackCompIso (originalExceptionalOverlapMap I a b)
        (exceptionalIdeal I).gluedTo).app (schemeKernelIdeal (exceptionalIdeal I).gluedTo) ≪≫
        (eqToIso (congrArg schemeModulePullback
          (originalExceptionalOverlapMap_base I a b))).app
            (schemeKernelIdeal (exceptionalIdeal I).gluedTo) ≪≫
          ((schemeModulePullbackCompIso (exceptionalOverlapAmbientInclusion I a b)
            (ambientOverlapMap I a b)).app (schemeKernelIdeal (exceptionalIdeal I).gluedTo)).symm).hom :=
  Eq.refl (originalOverlapKernelComparisonIso I a b).hom

private theorem rightAmbientKernelFrame_components :
    rightAmbientKernelFrame I a b =
      kernelFrameRefinement (exceptionalIdeal I).gluedTo (chartAffineOpen I b).1.ι
          (overlapToRightAmbient I a b)
          (localKernelGlobalEquation (exceptionalIdeal I).gluedTo (chartAffineOpen I b).1
            (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))
            (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I b)
              (chartEquationSection I b) (exceptionalIdeal_chartEquationSection I b))) ≫
        (eqToIso (congrArg schemeModulePullback (ambientOverlapMap_right I a b))).hom.app
          (schemeKernelIdeal (exceptionalIdeal I).gluedTo) :=
  localKernel_refinement_eq_of_inclusion (exceptionalIdeal I).gluedTo
    (chartAffineOpen I b).1
    (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))
    (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I b)
      (chartEquationSection I b) (exceptionalIdeal_chartEquationSection I b))
    (overlapToRightAmbient I a b) (ambientOverlapMap I a b)
    (ambientOverlapMap_right I a b) (rightAmbientKernelFrame I a b)
    (rightAmbientKernelFrame_inclusion I a b)

set_option maxHeartbeats 800000 in
/-- The right original equation gives its actual right ambient frame
through exactly the same global-to-ambient comparison. -/
theorem originalOverlapFrameRight_comparison :
    originalOverlapFrameRight I a b ≫ (originalOverlapKernelComparisonIso I a b).hom =
      schemeModulePullbackFrame (exceptionalOverlapAmbientInclusion I a b)
        (rightAmbientKernelFrame I a b) := by
  exact localConormalGlobalFrame_named_comparison
    (exceptionalIdeal I).gluedTo (chartAffineOpen I b).1
    (exceptionalOverlapRightMorphism I a b ≫ originalExceptionalChartLocalMap I b)
    (exceptionalOverlapAmbientInclusion I a b) (overlapToRightAmbient I a b)
    (originalExceptionalOverlapMap I a b) (ambientOverlapMap I a b)
    (originalExceptionalOverlapMap_local_right I a b) (ambientOverlapMap_right I a b)
    (exceptionalOverlap_right_local_square I a b)
    (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))
    (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I b)
      (chartEquationSection I b) (exceptionalIdeal_chartEquationSection I b))
    (originalOverlapFrameRight I a b)
    (originalOverlapFrameRight_local_refinement I a b)
    (originalExceptionalOverlapMap_base I a b)
    (originalOverlapKernelComparisonIso I a b)
    (originalOverlapKernelComparisonIso_hom_components I a b)
    (rightAmbientKernelFrame I a b) (rightAmbientKernelFrame_components I a b)

/-- The transition of the actual global conormal equation frames is
the original ambient equation ratio restricted to the actual quotient. -/
theorem originalOverlapFrame_transition :
    originalOverlapFrameRight I a b =
      schemeScalarEnd ((exceptionalOverlapAmbientInclusion I a b).appTop
        (ambientOverlapRatioSection I a b)) ≫ originalOverlapFrameLeft I a b := by
  apply (cancel_mono (originalOverlapKernelComparisonIso I a b).hom).mp
  rw [originalOverlapFrameRight_comparison, Category.assoc,
    originalOverlapFrameLeft_comparison]
  exact ambientKernelFrame_transition_pullback I a b (exceptionalOverlapAmbientInclusion I a b)

end AffineBlowup

/-- Canonical frame transport through named composites, for a frame
already taking values in an iterated pullback. This compares the original
maps without requiring the frame to come from a global trivialization. -/
theorem schemeModulePullbackFrame_flatten_map {W : Scheme.{u}}
    (e : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (j : X ⟶ Z) (t : W ⟶ Y) (l : W ⟶ Z)
    (hj : g ≫ h = j) (ht : e ≫ g = t) (hl : t ≫ h = l) {M : Z.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (schemeModulePullback g).obj ((schemeModulePullback h).obj M)) :
    schemeModulePullbackFrame e
        (s ≫ (schemeModulePullbackCompIso g h).hom.app M ≫
          (eqToIso (congrArg schemeModulePullback hj)).hom.app M) ≫
      (schemeModulePullbackCompIso e j).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback
          ((congrArg (fun z => e ≫ z) hj).symm.trans
            ((Category.assoc e g h).symm.trans
              ((congrArg (fun z => z ≫ h) ht).trans hl))))).hom.app M =
      (schemeModulePullbackFrame e s ≫
        (schemeModulePullbackCompIso e g).hom.app ((schemeModulePullback h).obj M) ≫
          (eqToIso (congrArg schemeModulePullback ht)).hom.app
            ((schemeModulePullback h).obj M)) ≫
        (schemeModulePullbackCompIso t h).hom.app M ≫
          (eqToIso (congrArg schemeModulePullback hl)).hom.app M := by
  subst j
  subst t
  subst l
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    schemeModulePullbackFrame_postcomp, Category.assoc, eqToHom_app]
  rw [schemeModulePullbackCompIso_assoc]
  simp only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl, Category.comp_id]

-- Perform the iso/frame normalization while every scheme, module and frame is abstract.
private theorem pullbackFrameIso_flatten_map {W : Scheme.{u}}
    (e : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (j : X ⟶ Z) (t : W ⟶ Y) (l : W ⟶ Z)
    (hj : g ≫ h = j) (ht : e ≫ g = t) (hl : t ≫ h = l) (he : e ≫ j = l)
    {M : Z.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ≅
      (schemeModulePullback g).obj ((schemeModulePullback h).obj M))
    (s' : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ (schemeModulePullback j).obj M)
    (hs : s.hom ≫ (schemeModulePullbackCompIso g h).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback hj)).hom.app M = s') :
    ((schemeModulePullbackUnitIso e).symm ≪≫ (schemeModulePullback e).mapIso s ≪≫
      (schemeModulePullbackCompIso e g).app ((schemeModulePullback h).obj M) ≪≫
        (eqToIso (congrArg schemeModulePullback ht)).app ((schemeModulePullback h).obj M)).hom ≫
      ((schemeModulePullbackCompIso t h).app M ≪≫
        (eqToIso (congrArg schemeModulePullback hl)).app M).hom =
    schemeModulePullbackFrame e s' ≫ (schemeModulePullbackCompIso e j).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback he)).hom.app M := by
  have H := schemeModulePullbackFrame_flatten_map e g h j t l hj ht hl s.hom
  rw [hs] at H
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    schemeModulePullbackFrame, Category.assoc] using H.symm

-- Cancel the original frame/comparison pair before specializing its module objects.
private theorem pullbackFrameIso_flatten_cancel {W : Scheme.{u}}
    (e : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (j : X ⟶ Z) (t : W ⟶ Y) (l : W ⟶ Z)
    (hj : g ≫ h = j) (ht : e ≫ g = t) (hl : t ≫ h = l) (he : e ≫ j = l)
    {M : Z.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ≅ (schemeModulePullback j).obj M)
    (overlapFrame : _root_.SheafOfModules.unit W.ringCatSheaf ≅
      (schemeModulePullback t).obj ((schemeModulePullback h).obj M))
    (hoverlapFrame : overlapFrame.hom =
      ((schemeModulePullbackUnitIso e).symm ≪≫
        (schemeModulePullback e).mapIso (s ≪≫
          ((schemeModulePullbackCompIso g h).app M ≪≫
            (eqToIso (congrArg schemeModulePullback hj)).app M).symm) ≪≫
        (schemeModulePullbackCompIso e g).app ((schemeModulePullback h).obj M) ≪≫
          (eqToIso (congrArg schemeModulePullback ht)).app ((schemeModulePullback h).obj M)).hom)
    (comparison : (schemeModulePullback t).obj ((schemeModulePullback h).obj M) ≅
      (schemeModulePullback l).obj M)
    (hcomparison : comparison.hom = ((schemeModulePullbackCompIso t h).app M ≪≫
      (eqToIso (congrArg schemeModulePullback hl)).app M).hom)
    (targetFrame : _root_.SheafOfModules.unit W.ringCatSheaf ⟶
      (schemeModulePullback l).obj M)
    (htargetFrame : targetFrame =
      schemeModulePullbackFrame e s.hom ≫ (schemeModulePullbackCompIso e j).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback he)).hom.app M) :
    overlapFrame.hom ≫ comparison.hom = targetFrame := by
  rw [hoverlapFrame, hcomparison]
  subst targetFrame
  let c := (schemeModulePullbackCompIso g h).app M ≪≫
    (eqToIso (congrArg schemeModulePullback hj)).app M
  have hc : (s ≪≫ c.symm).hom ≫ (schemeModulePullbackCompIso g h).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback hj)).hom.app M = s.hom := by
    change (s ≪≫ c.symm).hom ≫ c.hom = s.hom
    exact (Iso.eq_comp_inv c).mp rfl
  exact pullbackFrameIso_flatten_map e g h j t l hj ht hl he
    (s ≪≫ c.symm) s.hom hc

private theorem pullbackFrameIso_flatten_left {W : Scheme.{u}}
    (e : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (j : X ⟶ Z) (l : W ⟶ Z)
    (hj : g ≫ h = j) (hl : (e ≫ g) ≫ h = l) (he : e ≫ j = l)
    {M : Z.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ≅
      (schemeModulePullback g).obj ((schemeModulePullback h).obj M))
    (s' : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ (schemeModulePullback j).obj M)
    (hs : s.hom ≫ (schemeModulePullbackCompIso g h).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback hj)).hom.app M = s') :
    ((schemeModulePullbackUnitIso e).symm ≪≫ (schemeModulePullback e).mapIso s ≪≫
      (schemeModulePullbackCompIso e g).app ((schemeModulePullback h).obj M)).hom ≫
      ((schemeModulePullbackCompIso (e ≫ g) h).app M ≪≫
        (eqToIso (congrArg schemeModulePullback hl)).app M).hom =
    schemeModulePullbackFrame e s' ≫ (schemeModulePullbackCompIso e j).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback he)).hom.app M := by
  simpa only [eqToIso_refl, Iso.trans_refl] using
    pullbackFrameIso_flatten_map e g h j (e ≫ g) l hj rfl hl he s s' hs

end KltDP.Geometry

namespace KltDP.Examples.FrobeniusExceptionalFrameTransition

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalOverlap
open FrobeniusExceptionalProjectiveLine FrobeniusExceptionalLine

variable {k : Type u} [Field k]

/-- The existing P1 overlap map followed by the existing inverse
exceptional-fiber isomorphism is the original exceptional overlap map. -/
theorem projectiveOverlap_toExceptional :
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k) ≫
        exceptionalProjectiveLineIso.inv =
      originalExceptionalOverlapMap (centerIdeal (k := k)) centerU centerV := by
  rw [FrobeniusExceptionalChartFrames.overlapToProjectiveLine, Category.assoc,
    leftToProjectiveLine_inv]
  rfl

/-- One original comparison from the existing P1 conormal pullback to
the actual global exceptional conormal pullback on the same overlap. -/
def projectiveOverlapConormalComparisonIso :
    (schemeModulePullback
      (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k))).obj
        conormalLine.obj ≅
      (schemeModulePullback (originalExceptionalOverlapMap (centerIdeal (k := k)) centerU centerV)).obj
        (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) :=
  (schemeModulePullbackCompIso FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    exceptionalProjectiveLineIso.inv).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback (projectiveOverlap_toExceptional (k := k)))).app _

set_option maxHeartbeats 800000 in
/-- The existing first P1 frame retains the original left global
equation frame under the canonical comparison. -/
theorem projective_leftFrame_comparison :
    (FrobeniusExceptionalChartFrames.leftOverlapFrameIso (k := k)).hom ≫
        projectiveOverlapConormalComparisonIso.hom =
      originalOverlapFrameLeft (centerIdeal (k := k)) centerU centerV := by
  have hc : (FrobeniusExceptionalChartFrames.leftFrameIso (k := k)).hom ≫
      (schemeModulePullbackCompIso leftToProjectiveLine exceptionalProjectiveLineIso.inv).hom.app
        (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) ≫
      (eqToIso (congrArg schemeModulePullback
        (leftToProjectiveLine_inv (k := k)))).hom.app
          (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) =
      (originalExceptionalChartFrameIso (centerIdeal (k := k)) centerU).hom := by
    change FrobeniusExceptionalChartFrames.leftFrameIso.hom ≫
      leftConormalPullbackIso.hom = _
    simp only [FrobeniusExceptionalChartFrames.leftFrameIso, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have H := pullbackFrameIso_flatten_left
    (M := schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo)
    (exceptionalOverlapLeftMorphism (centerIdeal (k := k)) (centerU (k := k)) centerV)
    leftToProjectiveLine exceptionalProjectiveLineIso.inv
    (originalExceptionalChartMap (centerIdeal (k := k)) centerU)
    (originalExceptionalOverlapMap (centerIdeal (k := k)) centerU centerV)
    leftToProjectiveLine_inv projectiveOverlap_toExceptional rfl
    FrobeniusExceptionalChartFrames.leftFrameIso
    (originalExceptionalChartFrameIso (centerIdeal (k := k)) centerU).hom hc
  simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using H

-- Keep the three original right-frame conversions as separately checked proof constants.
private theorem projective_rightOverlapFrame_hom_components :
    (FrobeniusExceptionalChartFrames.rightOverlapFrameIso (k := k)).hom =
      ((schemeModulePullbackUnitIso
        (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)).symm ≪≫
        (schemeModulePullback
          (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)).mapIso
          ((originalExceptionalChartFrameIso (centerIdeal (k := k)) centerV) ≪≫
            ((schemeModulePullbackCompIso rightToProjectiveLine exceptionalProjectiveLineIso.inv).app
              (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) ≪≫
              (eqToIso (congrArg schemeModulePullback (rightToProjectiveLine_inv (k := k)))).app
                (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo)).symm) ≪≫
        (schemeModulePullbackCompIso
          (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
          rightToProjectiveLine).app
            ((schemeModulePullback exceptionalProjectiveLineIso.inv).obj
              (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo)) ≪≫
          (eqToIso (congrArg schemeModulePullback
            (FrobeniusExceptionalChartFrames.overlapToProjectiveLine_right (k := k)).symm)).app
              ((schemeModulePullback exceptionalProjectiveLineIso.inv).obj
                (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo))).hom :=
  Eq.refl (FrobeniusExceptionalChartFrames.rightOverlapFrameIso (k := k)).hom

private theorem projectiveOverlapConormalComparisonIso_hom_components :
    (projectiveOverlapConormalComparisonIso (k := k)).hom =
      ((schemeModulePullbackCompIso FrobeniusExceptionalChartFrames.overlapToProjectiveLine
        exceptionalProjectiveLineIso.inv).app
          (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) ≪≫
        (eqToIso (congrArg schemeModulePullback (projectiveOverlap_toExceptional (k := k)))).app
          (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo)).hom :=
  Eq.refl (projectiveOverlapConormalComparisonIso (k := k)).hom

private theorem projective_rightOriginalOverlapFrame_components :
    originalOverlapFrameRight (centerIdeal (k := k)) centerU centerV =
      schemeModulePullbackFrame
          (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
          (originalExceptionalChartFrameIso (centerIdeal (k := k)) centerV).hom ≫
        (schemeModulePullbackCompIso
          (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
          (originalExceptionalChartMap (centerIdeal (k := k)) centerV)).hom.app
            (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) ≫
          (eqToIso (congrArg schemeModulePullback
            (originalExceptionalOverlapMap_right (centerIdeal (k := k)) centerU centerV))).hom.app
              (schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo) :=
  normalizedCompositeFrame_components
    (M := schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo)
    (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
    (originalExceptionalChartMap (centerIdeal (k := k)) centerV)
    (originalExceptionalOverlapMap (centerIdeal (k := k)) centerU centerV)
    (originalExceptionalOverlapMap_right (centerIdeal (k := k)) centerU centerV)
    (originalExceptionalChartFrameIso (centerIdeal (k := k)) centerV).hom

set_option maxHeartbeats 800000 in
/-- The existing second P1 frame is compared by the same canonical map. -/
theorem projective_rightFrame_comparison :
    (FrobeniusExceptionalChartFrames.rightOverlapFrameIso (k := k)).hom ≫
        projectiveOverlapConormalComparisonIso.hom =
      originalOverlapFrameRight (centerIdeal (k := k)) centerU centerV := by
  exact pullbackFrameIso_flatten_cancel
    (M := schemeConormalSheaf (exceptionalIdeal (centerIdeal (k := k))).gluedTo)
    (exceptionalOverlapRightMorphism (centerIdeal (k := k)) (centerU (k := k)) centerV)
    rightToProjectiveLine exceptionalProjectiveLineIso.inv
    (originalExceptionalChartMap (centerIdeal (k := k)) centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    (originalExceptionalOverlapMap (centerIdeal (k := k)) centerU centerV)
    rightToProjectiveLine_inv FrobeniusExceptionalChartFrames.overlapToProjectiveLine_right.symm
    projectiveOverlap_toExceptional
    (originalExceptionalOverlapMap_right (centerIdeal (k := k)) centerU centerV)
    (originalExceptionalChartFrameIso (centerIdeal (k := k)) centerV)
    (FrobeniusExceptionalChartFrames.rightOverlapFrameIso (k := k))
    (projective_rightOverlapFrame_hom_components (k := k))
    (projectiveOverlapConormalComparisonIso (k := k))
    (projectiveOverlapConormalComparisonIso_hom_components (k := k))
    (originalOverlapFrameRight (centerIdeal (k := k)) centerU centerV)
    (projective_rightOriginalOverlapFrame_components (k := k))

/-- The transition of the existing original P1 conormal frames is the
original equation ratio restricted through the actual ambient quotient. -/
theorem projectiveFrame_transition :
    (FrobeniusExceptionalChartFrames.rightOverlapFrameIso (k := k)).hom =
      schemeScalarEnd ((exceptionalOverlapAmbientInclusion (centerIdeal (k := k)) centerU centerV).appTop
        (ambientOverlapRatioSection (centerIdeal (k := k)) centerU centerV)) ≫
          FrobeniusExceptionalChartFrames.leftOverlapFrameIso.hom := by
  apply (cancel_mono (projectiveOverlapConormalComparisonIso (k := k)).hom).mp
  rw [projective_rightFrame_comparison, Category.assoc, projective_leftFrame_comparison]
  exact originalOverlapFrame_transition (centerIdeal (k := k)) centerU centerV

/-- The automorphism extracted from the already constructed P1 frames
has the actual quotient-section coefficient, rather than a prescribed one. -/
theorem actualOverlapFrameChange_eq_scalar :
    (FrobeniusExceptionalChartFrames.actualOverlapFrameChange (k := k)).hom =
      schemeScalarEnd ((exceptionalOverlapAmbientInclusion (centerIdeal (k := k)) centerU centerV).appTop
        (ambientOverlapRatioSection (centerIdeal (k := k)) centerU centerV)) := by
  apply (cancel_mono (FrobeniusExceptionalChartFrames.leftOverlapFrameIso (k := k)).hom).mp
  rw [FrobeniusExceptionalChartFrames.actualOverlapFrameChange_hom_leftFrame]
  exact projectiveFrame_transition

/-- The actual quotient pullback of the ambient ratio section is the
section whose coordinate under the proved Laurent equivalence is T. -/
theorem quotientRatioSection_laurent :
    (exceptionalOverlapAmbientInclusion (centerIdeal (k := k)) centerU centerV).appTop
        (ambientOverlapRatioSection (centerIdeal (k := k)) centerU centerV) =
      (Scheme.ΓSpecIso (CommRingCat.of
        (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv
          ((exceptionalOverlapLaurentEquiv (k := k)).symm (LaurentPolynomial.T 1)) := by
  have hquot : Ideal.Quotient.mk
      (conormalOverlapIdeal (centerIdeal (k := k)) centerU centerV)
      (conormalOverlapRatio (centerIdeal (k := k)) centerU centerV) =
      (exceptionalOverlapLaurentEquiv (k := k)).symm (LaurentPolynomial.T 1) := by
    apply (exceptionalOverlapLaurentEquiv (k := k)).injective
    rw [RingEquiv.apply_symm_apply]
    exact exceptionalOverlapLaurentEquiv_ratio
  rw [← hquot]
  exact (RingHom.congr_fun
    (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Ideal.Quotient.mk
          (conormalOverlapIdeal (centerIdeal (k := k)) centerU centerV)))))
    (conormalOverlapRatio (centerIdeal (k := k)) centerU centerV)).symm

/-- The automorphism of the actual structure module extracted from the
existing P1 conormal frames is multiplication by the original Laurent
coordinate T, transported through the actual quotient and Gamma-Spec
isomorphisms. No Laurent transition or line-bundle degree is assumed. -/
theorem actualOverlapFrameChange_laurent :
    (FrobeniusExceptionalChartFrames.actualOverlapFrameChange (k := k)).hom =
      schemeScalarEnd
        ((Scheme.ΓSpecIso (CommRingCat.of
          (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv
            ((exceptionalOverlapLaurentEquiv (k := k)).symm (LaurentPolynomial.T 1))) := by
  rw [actualOverlapFrameChange_eq_scalar, quotientRatioSection_laurent]

end KltDP.Examples.FrobeniusExceptionalFrameTransition
