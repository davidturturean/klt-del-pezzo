import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# Comparing canonical lines from different actual Kähler atlases

Each atlas maps to the same independently defined exterior sheaf of the
original global Kähler sheaf. These comparisons therefore identify the
original canonical lines without an overlap-compatibility premise. Their
identity and composition laws are proved for the actual sheaf isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

namespace KltDP.Geometry.CanonicalAtlasComparison

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))
  {ι κ τ : Type u} {n : ℕ}
  (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (b : ∀ i, letI := KaehlerChartAtlas.chartAlgebra f U hU i;
    Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i)))
  (hcovU : (⨆ i, U i) = ⊤)
  (V : κ → X.Opens) (hV : ∀ j, IsAffineOpen (V j))
  (c : ∀ j, letI := KaehlerChartAtlas.chartAlgebra f V hV j;
    Basis (Fin n) Γ(X, V j) (KaehlerDifferential k Γ(X, V j)))
  (hcovV : (⨆ j, V j) = ⊤)

/-- Two original Kähler atlases give canonically isomorphic frame lines. -/
def atlasIso :
    (KaehlerChartAtlas.canonicalSheaf f U hU b hcovU).obj ≅
      (KaehlerChartAtlas.canonicalSheaf f V hV c hcovV).obj :=
  kaehlerChartAtlasIso f U hU b hcovU ≪≫
    (kaehlerChartAtlasIso f V hV c hcovV).symm

/-- The comparison commutes with the original maps to the global exterior sheaf. -/
@[reassoc]
theorem atlasIso_hom_toExterior :
    (atlasIso f U hU b hcovU V hV c hcovV).hom ≫
        (kaehlerChartAtlasIso f V hV c hcovV).hom =
      (kaehlerChartAtlasIso f U hU b hcovU).hom := by
  simp only [atlasIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- An atlas compared with itself gives the identity on its original canonical line. -/
@[simp]
theorem atlasIso_refl :
    atlasIso f U hU b hcovU U hU b hcovU = Iso.refl _ := by
  apply Iso.ext
  simp only [atlasIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id, Iso.refl_hom]

/-- Changing actual atlases twice agrees with the direct comparison. -/
theorem atlasIso_trans (W : τ → X.Opens) (hW : ∀ l, IsAffineOpen (W l))
    (d : ∀ l, letI := KaehlerChartAtlas.chartAlgebra f W hW l;
      Basis (Fin n) Γ(X, W l) (KaehlerDifferential k Γ(X, W l)))
    (hcovW : (⨆ l, W l) = ⊤) :
    atlasIso f U hU b hcovU V hV c hcovV ≪≫
        atlasIso f V hV c hcovV W hW d hcovW =
      atlasIso f U hU b hcovU W hW d hcovW := by
  apply Iso.ext
  simp only [atlasIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

end KltDP.Geometry.CanonicalAtlasComparison
