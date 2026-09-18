import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Original affine-chart stalk maps on original section germs

The pinned affine-chart section formula and stalk naturality identify
the composite with the literal affine `toStalk` map. Vanishing therefore
passes to the original affine chart through its original local ring map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineChartStalkGerms

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) (hp : hU.fromSpec.base p ∈ U)

/-- The actual open-chart stalk map takes an actual section germ to its
literal original affine numerator germ. -/
theorem germ_comp_stalkMap :
    X.presheaf.germ U (hU.fromSpec.base p) hp ≫ hU.fromSpec.stalkMap p =
      StructureSheaf.toStalk Γ(X, U) p := by
  rw [Scheme.stalkMap_germ, IsAffineOpen.fromSpec_app_self, Category.assoc,
    TopCat.Presheaf.germ_res]
  rfl

theorem toStalk_mem_maximalIdeal (a : Γ(X, U))
    (ha : X.presheaf.germ U (hU.fromSpec.base p) hp a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec.base p))) :
    StructureSheaf.toStalk Γ(X, U) p a ∈
      IsLocalRing.maximalIdeal ((Spec Γ(X, U)).presheaf.stalk p) := by
  have heq := congrArg
    (fun g : Γ(X, U) ⟶ (Spec Γ(X, U)).presheaf.stalk p => g.hom a)
    (germ_comp_stalkMap hU p hp)
  change (hU.fromSpec.stalkMap p).hom
    (X.presheaf.germ U (hU.fromSpec.base p) hp a) =
      StructureSheaf.toStalk Γ(X, U) p a at heq
  rw [← heq]
  exact map_nonunit (hU.fromSpec.stalkMap p).hom _ ha

end KltDP.Geometry.AffineChartStalkGerms

#check @KltDP.Geometry.AffineChartStalkGerms.toStalk_mem_maximalIdeal
#print axioms KltDP.Geometry.AffineChartStalkGerms.toStalk_mem_maximalIdeal
