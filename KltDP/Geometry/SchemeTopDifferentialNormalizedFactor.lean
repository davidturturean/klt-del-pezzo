import KltDP.Geometry.SchemeTopDifferentialFactorSquare

/-!
# An original top-differential factor together with its normalization

The already proved square transport supplies the actual factor and its
actual differential equation in one dependent pair. Keeping this pair
named prevents downstream chart wrappers from reconstructing the large
factor expression while checking its normalization.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.SchemeTopDifferentialFactorSquare

local instance normalizedFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [CommRing k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (π : Y ⟶ X) (l : Z ⟶ Y) (c : W ⟶ X) (b : Z ⟶ W)
  (hsq : l ≫ π = b ≫ c)
  (g : Y ⟶ Spec (CommRingCat.of k)) (hg : π ≫ f = g)
  (p : W ⟶ Spec (CommRingCat.of k)) (hp : c ≫ f = p)
  (q : Z ⟶ Spec (CommRingCat.of k)) (hl : l ≫ g = q) (hb : b ≫ p = q)
  (n : ℕ) [IsOpenImmersion l] [IsOpenImmersion c]
  {I : Y.Modules} {J : Z.Modules}
  (i : I ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)
  (j : J ⟶ _root_.SheafOfModules.unit Z.ringCatSheaf)
  (eJ : J ≅ (schemeModulePullback l).obj I)
  (hJ : eJ.hom ≫ ((schemeModulePullback l).map i ≫ (schemeModulePullbackUnitIso l).hom) = j)
  (e : (schemeModulePullback b).obj (top p n) ≅ J ⊗ top q n)
  (he : e.hom ≫ schemeStructureTensorInclusion j (top q n) =
    SchemeKaehlerExteriorPullbackTransport.map p b q hb n)

/-- The same original transported isomorphism, paired with its proved normalization. -/
def normalizedFactor :
    {F : (schemeModulePullback l).obj ((schemeModulePullback π).obj (top f n)) ≅
        (schemeModulePullback l).obj (I ⊗ top g n) //
      F.hom ≫ (schemeModulePullback l).map (schemeStructureTensorInclusion i (top g n)) =
        (schemeModulePullback l).map (SchemeKaehlerExteriorPullbackTransport.map f π g hg n)} :=
  ⟨factorIso f π l c b hsq g p hp q hl n eJ e,
    factorIso_comp f π l c b hsq g hg p hp q hl hb n i j eJ hJ e he⟩

end KltDP.Geometry.SchemeTopDifferentialFactorSquare

#print axioms KltDP.Geometry.SchemeTopDifferentialFactorSquare.normalizedFactor
