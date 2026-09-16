import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# The original chart-to-image comparison on global sections

The existing top-open and image isomorphisms identify an original open chart
with its actual image open. Its map on sections is exactly the original appIso,
with the canonical top-section comparison retained. Coordinate maps between two
original charts therefore give maps between their image opens over the ambient
square, with their original section maps unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original chart viewed as an isomorphism onto its literal image of top. -/
def schemeOpenChartIso {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] :
    A ≅ (j ''ᵁ ⊤).toScheme :=
  A.topIso.symm ≪≫ j.isoImage ⊤

@[reassoc] theorem schemeOpenChartIso_hom_ι
    {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] :
    (schemeOpenChartIso j).hom ≫ (j ''ᵁ ⊤).ι = j := by
  simp only [schemeOpenChartIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Scheme.Hom.isoImage_hom_ι, Scheme.toIso_inv_ι_assoc, Category.id_comp]

@[reassoc] theorem schemeOpenChartIso_inv_ι
    {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] :
    (schemeOpenChartIso j).inv ≫ j = (j ''ᵁ ⊤).ι :=
  (Iso.inv_comp_eq (schemeOpenChartIso j)).mpr (schemeOpenChartIso_hom_ι j).symm

private theorem chart_appLE_congr {A X : Scheme.{u}} {f g : A ⟶ X}
    (h : f = g) (U : X.Opens) (V : A.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- The original appIso is the section map of the actual chart-to-open isomorphism. -/
theorem schemeOpenChartIso_appTop {A X : Scheme.{u}}
    (j : A ⟶ X) [IsOpenImmersion j] :
    (j ''ᵁ ⊤).topIso.inv ≫ (schemeOpenChartIso j).hom.appTop = (j.appIso ⊤).hom := by
  let U := j ''ᵁ ⊤
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  have ht : (schemeOpenChartIso j).hom.appLE ⊤ ⊤ le_rfl =
      (schemeOpenChartIso j).hom.appTop :=
    Scheme.Hom.appLE_eq_app _ (U := ⊤)
  have h := Scheme.appLE_comp_appLE (schemeOpenChartIso j).hom U.ι
    U ⊤ ⊤ U.ι_preimage_self.ge le_rfl
  rw [hι, ht] at h
  exact h.trans ((chart_appLE_congr (schemeOpenChartIso_hom_ι j) U ⊤ _ _).trans
    (Scheme.Hom.appIso_hom' j ⊤).symm)

theorem schemeOpenChartIso_section {A X : Scheme.{u}}
    (j : A ⟶ X) [IsOpenImmersion j] (s : Γ(A, ⊤)) :
    (schemeOpenChartIso j).hom.appTop ((j ''ᵁ ⊤).topIso.inv ((j.appIso ⊤).inv s)) = s := by
  calc
    _ = (j.appIso ⊤).hom ((j.appIso ⊤).inv s) := by
      change ((j ''ᵁ ⊤).topIso.inv ≫ (schemeOpenChartIso j).hom.appTop)
        ((j.appIso ⊤).inv s) = _
      exact ConcreteCategory.congr_hom (schemeOpenChartIso_appTop j) _
    _ = s := by
      change ((j.appIso ⊤).inv ≫ (j.appIso ⊤).hom) s = s
      rw [Iso.inv_hom_id]
      rfl

theorem schemeOpenChartIso_inv_section {A X : Scheme.{u}}
    (j : A ⟶ X) [IsOpenImmersion j] (s : Γ(A, ⊤)) :
    (schemeOpenChartIso j).inv.appTop s = (j ''ᵁ ⊤).topIso.inv ((j.appIso ⊤).inv s) := by
  calc
    _ = (schemeOpenChartIso j).inv.appTop
        ((schemeOpenChartIso j).hom.appTop ((j ''ᵁ ⊤).topIso.inv ((j.appIso ⊤).inv s))) := by
      rw [schemeOpenChartIso_section]
    _ = _ := Iso.hom_inv_id_apply (Scheme.Γ.mapIso (schemeOpenChartIso j).op) _

/-- The coordinate map between the original charts induces this map of their actual image opens. -/
def schemeOpenChartMap {A B X Y : Scheme.{u}}
    (a : A ⟶ X) [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b] (c : A ⟶ B) :
    (a ''ᵁ ⊤).toScheme ⟶ (b ''ᵁ ⊤).toScheme :=
  (schemeOpenChartIso a).inv ≫ c ≫ (schemeOpenChartIso b).hom

@[reassoc] theorem schemeOpenChartMap_ι {A B X Y : Scheme.{u}}
    (a : A ⟶ X) [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b]
    (c : A ⟶ B) (p : X ⟶ Y) (h : a ≫ p = c ≫ b) :
    schemeOpenChartMap a b c ≫ (b ''ᵁ ⊤).ι = (a ''ᵁ ⊤).ι ≫ p := by
  simp only [schemeOpenChartMap, Category.assoc, schemeOpenChartIso_hom_ι]
  rw [← h, schemeOpenChartIso_inv_ι_assoc]

theorem schemeOpenChartMap_section {A B X Y : Scheme.{u}}
    (a : A ⟶ X) [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b]
    (c : A ⟶ B) (s : Γ(B, ⊤)) :
    (schemeOpenChartMap a b c).appTop ((b ''ᵁ ⊤).topIso.inv ((b.appIso ⊤).inv s)) =
      (a ''ᵁ ⊤).topIso.inv ((a.appIso ⊤).inv (c.appTop s)) := by
  simp only [schemeOpenChartMap, Scheme.comp_appTop, ConcreteCategory.comp_apply,
    schemeOpenChartIso_section, schemeOpenChartIso_inv_section]

end KltDP.Geometry
