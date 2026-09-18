import KltDP.Geometry.AffineChartStalkGerms

/-! The original parameter numerators under the actual principal-chart stalk map. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffinePrincipalNeighborhoodStalkGerms

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (p : PrimeSpectrum (Localization.Away r))

/-- The actual composite stalk map takes a parameter germ to the literal
toStalk of its principal-localization numerator. -/
theorem germ_comp_stalkMap (hp : ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) ≫ hU.fromSpec).base p ∈ U) :
    X.presheaf.germ U (((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) ≫ hU.fromSpec).base p) hp ≫ ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) ≫ hU.fromSpec).stalkMap p =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)) ≫
        StructureSheaf.toStalk (Localization.Away r) p := by
  let l : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec Γ(X, U) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))
  have hchart := AffineChartStalkGerms.germ_comp_stalkMap hU (l.base p) hp
  have hspec : StructureSheaf.toStalk Γ(X, U) (l.base p) ≫ l.stalkMap p =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)) ≫
        StructureSheaf.toStalk (Localization.Away r) p :=
    stalkMap_toStalk
      (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) p
  rw [Scheme.stalkMap_comp, ← Category.assoc]
  exact (congrArg (fun a : Γ(X, U) ⟶ (Spec Γ(X, U)).presheaf.stalk (l.base p) =>
    a ≫ l.stalkMap p) hchart).trans hspec

/-- Value form with exactly the original scheme germ and affine numerator. -/
theorem germ_stalkMap (hp : ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) ≫ hU.fromSpec).base p ∈ U) (a : Γ(X, U)) :
    ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) ≫ hU.fromSpec).stalkMap p (X.presheaf.germ U (((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) ≫ hU.fromSpec).base p) hp a) =
      StructureSheaf.toStalk (Localization.Away r) p
        (algebraMap Γ(X, U) (Localization.Away r) a) :=
  ConcreteCategory.congr_hom (germ_comp_stalkMap hU r p hp) a

end KltDP.Geometry.AffinePrincipalNeighborhoodStalkGerms
