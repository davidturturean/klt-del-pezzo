import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSquare
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.SchemeModulePullbackTensorInclusion

/-!
# Transport of a normalized original top-differential factor across an open square

The actual exterior-differential square and the original tensor pullback
comparison transport a proved factor on a source chart. The scheme maps,
ideal inclusions and their normalization remain literal. This is an ordinary
comparison lemma; the geometric point-blowup application supplies its local
factor and ideal comparison from the actual constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SchemeTopDifferentialFactorSquare

open SchemeKaehlerSheaf

local instance factorSquareModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

abbrev top {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : X.Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf f) n

/-- The isomorphism is the original differential along the original open map. -/
def openIso {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (c : Y ⟶ X) [IsOpenImmersion c]
    (p : Y ⟶ Spec (CommRingCat.of k)) (hp : c ≫ f = p) (n : ℕ) :
    (schemeModulePullback c).obj (top f n) ≅ top p n := by
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso f c p hp n
  exact asIso (SchemeKaehlerExteriorPullbackTransport.map f c p hp n)

theorem openIso_hom {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (c : Y ⟶ X) [IsOpenImmersion c]
    (p : Y ⟶ Spec (CommRingCat.of k)) (hp : c ≫ f = p) (n : ℕ) :
    (openIso f c p hp n).hom =
      SchemeKaehlerExteriorPullbackTransport.map f c p hp n := rfl

variable {k : Type u} [CommRing k] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (π : Y ⟶ X) (l : Z ⟶ Y) (c : W ⟶ X) (b : Z ⟶ W)
    (hsq : l ≫ π = b ≫ c)
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : π ≫ f = g)
    (p : W ⟶ Spec (CommRingCat.of k)) (hp : c ≫ f = p)
    (q : Z ⟶ Spec (CommRingCat.of k)) (hl : l ≫ g = q) (hb : b ≫ p = q)
    (n : ℕ) [IsOpenImmersion l] [IsOpenImmersion c]

/-- The two original source comparisons around the actual scheme square. -/
def sourceIso :
    (schemeModulePullback l).obj ((schemeModulePullback π).obj (top f n)) ≅
      (schemeModulePullback b).obj (top p n) :=
  SchemeKaehlerExteriorPullbackTransport.squareSourceIso f π l c b hsq n ≪≫
    (schemeModulePullback b).mapIso (openIso f c p hp n)

variable {I : Y.Modules} {J : Z.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit Z.ringCatSheaf)
    (eJ : J ≅ (schemeModulePullback l).obj I)
    (hJ : eJ.hom ≫ ((schemeModulePullback l).map i ≫
      (schemeModulePullbackUnitIso l).hom) = j)

/-- The original ideal and differential comparisons determine the tensor comparison. -/
def targetIso :
    (schemeModulePullback l).obj (I ⊗ top g n) ≅ J ⊗ top q n :=
  schemeModulePullbackTensorIso l I (top g n) ≪≫
    tensorIso eJ.symm (openIso g l q hl n)

include hJ in
theorem targetIso_inclusion :
    (targetIso l g q hl n eJ).hom ≫ schemeStructureTensorInclusion j (top q n) =
      (schemeModulePullback l).map (schemeStructureTensorInclusion i (top g n)) ≫
        (openIso g l q hl n).hom :=
  schemeModulePullbackTensorIso_comparison_inclusion l i (top g n) eJ
    (openIso g l q hl n) j hJ

variable (e : (schemeModulePullback b).obj (top p n) ≅ J ⊗ top q n)
    (he : e.hom ≫ schemeStructureTensorInclusion j (top q n) =
      SchemeKaehlerExteriorPullbackTransport.map p b q hb n)

/-- The transported factor uses the original source, local factor and target comparison. -/
def factorIso :
    (schemeModulePullback l).obj ((schemeModulePullback π).obj (top f n)) ≅
      (schemeModulePullback l).obj (I ⊗ top g n) :=
  sourceIso f π l c b hsq p hp n ≪≫ e ≪≫ (targetIso l g q hl n eJ).symm

include hJ he in
/-- The full original global differential is preserved under this transport. -/
theorem factorIso_comp :
    (factorIso f π l c b hsq g p hp q hl n eJ e).hom ≫
        (schemeModulePullback l).map (schemeStructureTensorInclusion i (top g n)) =
      (schemeModulePullback l).map
        (SchemeKaehlerExteriorPullbackTransport.map f π g hg n) := by
  apply (cancel_mono (openIso g l q hl n).hom).mp
  rw [Category.assoc, ← targetIso_inclusion l g q hl n i j eJ hJ]
  simp only [factorIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [he]
  simpa only [sourceIso, Iso.trans_hom, Functor.mapIso_hom, openIso_hom,
    Category.assoc] using
    (SchemeKaehlerExteriorPullbackTransport.map_square f π l c b hsq n
      g hg p hp q hl hb).symm

end KltDP.Geometry.SchemeTopDifferentialFactorSquare
