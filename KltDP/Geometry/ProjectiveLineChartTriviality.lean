import KltDP.Geometry.AffinePIDInvertibleTrivial
import KltDP.Geometry.ProjectiveLineComparison
import KltDP.Geometry.PicardOpenRestriction
import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.ModuleOpenOver

/-!
# Actual unit trivializations on the two standard projective-line charts

Restrict an original invertible sheaf along each polynomial chart map.
The proved affine-line theorem trivializes that original restricted sheaf.
Transport along the chart's actual isomorphism with its open subscheme
then gives a unit trivialization on the original standard open.

Restriction composition is obtained from the existing comparisons with
actual module pullback. The resulting local atlas retains the two standard
opens; its index type is lifted only to the universe required by the
existing local-trivialization structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveLineChartTriviality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction ProjectiveLineComparison

private def restrictionCompIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] :
    restriction f ⋙ restriction g ≅ restriction (g ≫ f) :=
  isoWhiskerRight (restrictionIsoPullback f) (restriction g) ≪≫
    isoWhiskerLeft (schemeModulePullback f) (restrictionIsoPullback g) ≪≫
      schemeModulePullbackCompIso g f ≪≫ (restrictionIsoPullback (g ≫ f)).symm

private def restrictionObjectIsoOfEq {X Y : Scheme.{u}}
    {f g : Y ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) (M : X.Modules) : (restriction f).obj M ≅ (restriction g).obj M := by
  cases h
  exact Iso.refl _

variable (k : Type u) [Field k]

/-- The polynomial chart is isomorphic to the actual standard open subscheme. -/
def polynomialChartOpenIso (i : Fin 2) :
    Spec (.of (Polynomial k)) ≅ (chartOpen k i).toScheme :=
  (polynomialChartMap k i).isoOpensRange ≪≫
    (projectiveSpace k 1).isoOfEq (polynomialChartMap_opensRange k i)

@[simp]
theorem polynomialChartOpenIso_hom_ι (i : Fin 2) :
    (polynomialChartOpenIso k i).hom ≫ (chartOpen k i).ι = polynomialChartMap k i := by
  simp only [polynomialChartOpenIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]

@[simp]
theorem polynomialChartOpenIso_hom_ι_assoc (i : Fin 2) {Z : Scheme.{u}}
    (h : projectiveSpace k 1 ⟶ Z) :
    (polynomialChartOpenIso k i).hom ≫ (chartOpen k i).ι ≫ h =
      polynomialChartMap k i ≫ h := by
  simpa only [Category.assoc] using
    CategoryTheory.eq_whisker' (polynomialChartOpenIso_hom_ι k i) h

@[simp]
theorem polynomialChartOpenIso_inv_chartMap (i : Fin 2) :
    (polynomialChartOpenIso k i).inv ≫ polynomialChartMap k i = (chartOpen k i).ι := by
  simp only [polynomialChartOpenIso, Iso.trans_inv, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, Scheme.isoOfEq_inv_ι]

@[simp]
theorem polynomialChartOpenIso_inv_chartMap_assoc (i : Fin 2) {Z : Scheme.{u}}
    (h : projectiveSpace k 1 ⟶ Z) :
    (polynomialChartOpenIso k i).inv ≫ polynomialChartMap k i ≫ h =
      (chartOpen k i).ι ≫ h := by
  simpa only [Category.assoc] using
    CategoryTheory.eq_whisker' (polynomialChartOpenIso_inv_chartMap k i) h

/-- The actual restriction along a polynomial chart is a trivial affine-line sheaf. -/
def polynomialRestrictionUnitIso (L : InvertibleSheaf (projectiveSpace k 1)) (i : Fin 2) :
    (restriction (polynomialChartMap k i)).obj L.obj ≅
      _root_.SheafOfModules.unit (Spec (.of (Polynomial k))).ringCatSheaf :=
  AffineModuleTilde.affineLineInvertibleUnitIso k
    (restrictInvertibleSheaf (polynomialChartMap k i) L)

/-- The original restriction to each actual standard open subscheme is a unit sheaf. -/
def chartRestrictionUnitIso (L : InvertibleSheaf (projectiveSpace k 1)) (i : Fin 2) :
    (restriction (chartOpen k i).ι).obj L.obj ≅
      _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf := by
  let f := polynomialChartMap k i
  let q := (polynomialChartOpenIso k i).inv
  have hq : q ≫ f = (chartOpen k i).ι := polynomialChartOpenIso_inv_chartMap k i
  exact ((restrictionCompIso f q).app L.obj ≪≫
      restrictionObjectIsoOfEq hq L.obj).symm ≪≫
    (restriction q).mapIso (polynomialRestrictionUnitIso k L i) ≪≫ restrictionUnitIso q

/-- The original unit trivialization, expressed on the existing over site. -/
def chartOverUnitIso (L : InvertibleSheaf (projectiveSpace k 1)) (i : Fin 2) :
    L.obj.over (chartOpen k i) ≅
      _root_.SheafOfModules.unit ((projectiveSpace k 1).ringCatSheaf.over (chartOpen k i)) :=
  (openChartToOverUnitIso (chartOpen k i) L.obj (chartRestrictionUnitIso k L i).symm).symm

/-- Every original projective-line invertible sheaf has an atlas on its two standard opens. -/
def standardChartLocalTrivializations (L : InvertibleSheaf (projectiveSpace k 1)) :
    KltDP.SheafOfModules.LocalTrivializations
      (R := (projectiveSpace k 1).ringCatSheaf) L.obj :=
  localTrivializationsOfOpenCharts L.obj
    (fun i : ULift.{u} (Fin 2) => chartOpen k i.down)
    (fun x => by
      have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
        rw [chartOpen_sup]
        trivial
      change x ∈ chartOpen k 0 ∨ x ∈ chartOpen k 1 at hx
      rcases hx with hx | hx
      · exact ⟨⟨0⟩, hx⟩
      · exact ⟨⟨1⟩, hx⟩)
    (fun i => (chartRestrictionUnitIso k L i.down).symm)

@[simp]
theorem standardChartLocalTrivializations_X (L : InvertibleSheaf (projectiveSpace k 1))
    (i : ULift.{u} (Fin 2)) :
    (standardChartLocalTrivializations k L).X i = chartOpen k i.down := rfl

end KltDP.Geometry.ProjectiveLineChartTriviality
