import KltDP.Geometry.AffineChartStalkGerms

/-!
# Actual pulled section germs through the original affine source chart

Compose the original scheme stalk map with the original open-chart stalk
map. The result on a target section is exactly the original `appLE`
numerator followed by the original affine `toStalk` map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineChartStalkGerms

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (U : X.Opens)
    {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(Y, V)) (hp : hV.fromSpec.base p ∈ V)

/-- The original morphism of stalk rings on a pulled section is the
literal `appLE` map followed by the literal affine `toStalk`. -/
theorem pulled_germ_comp_stalkMap :
    X.presheaf.germ U (π.base (hV.fromSpec.base p)) (hVU hp) ≫
        π.stalkMap (hV.fromSpec.base p) ≫ hV.fromSpec.stalkMap p =
      π.appLE U V hVU ≫ StructureSheaf.toStalk Γ(Y, V) p := by
  calc
    _ = π.app U ≫ Y.presheaf.germ (π ⁻¹ᵁ U) (hV.fromSpec.base p) (hVU hp) ≫
        hV.fromSpec.stalkMap p := by rw [Scheme.stalkMap_germ_assoc]
    _ = π.app U ≫ Y.presheaf.map (homOfLE hVU).op ≫
        (Y.presheaf.germ V (hV.fromSpec.base p) hp ≫ hV.fromSpec.stalkMap p) := by
      rw [TopCat.Presheaf.germ_res_assoc]
    _ = _ := by
      rw [germ_comp_stalkMap hV p hp]
      rfl

/-- The value formula retains the literal original scheme stalk map
and the literal original affine numerator. -/
theorem pulled_germ_toStalk (s : Γ(X, U)) :
    hV.fromSpec.stalkMap p
      (π.stalkMap (hV.fromSpec.base p)
        (X.presheaf.germ U (π.base (hV.fromSpec.base p)) (hVU hp) s)) =
      StructureSheaf.toStalk Γ(Y, V) p (π.appLE U V hVU s) := by
  exact ConcreteCategory.congr_hom (pulled_germ_comp_stalkMap π U hV hVU p hp) s

end KltDP.Geometry.AffineChartStalkGerms

#check @KltDP.Geometry.AffineChartStalkGerms.pulled_germ_toStalk
#print axioms KltDP.Geometry.AffineChartStalkGerms.pulled_germ_toStalk
