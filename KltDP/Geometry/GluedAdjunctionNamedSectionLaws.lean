import KltDP.Geometry.GluedAdjunctionSectionNaturality

/-!
# Section laws for the original named additive map

The existing chart-section laws are applied before substituting the
concrete global modules. Each conclusion retains its given additive map;
the defining equality identifies it with the original chart section map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionNamedSectionLaws

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (M N : X.Modules)

/-- Scalar linearity retains the given original additive map. -/
theorem hom_smul (W : X.Opens) (hW : j ''ᵁ (j ⁻¹ᵁ W) = W)
    (a : (schemeModulePullback j).obj M ⟶ (schemeModulePullback j).obj N)
    (g : M.val.obj (op W) →+ N.val.obj (op W))
    (hg : g = GluedAdjunctionChartSectionMap.hom j M N W hW a)
    (r : Γ(X, W)) (m : M.val.obj (op W)) :
    g (r • m) = r • g m := by
  subst g
  exact GluedAdjunctionChartSectionMap.hom_smul j M N W hW a r m

/-- Restriction compatibility retains both given original additive maps. -/
theorem hom_res (W V : X.Opens) (h : V ≤ W)
    (hW : j ''ᵁ (j ⁻¹ᵁ W) = W) (hV : j ''ᵁ (j ⁻¹ᵁ V) = V)
    (a : (schemeModulePullback j).obj M ⟶ (schemeModulePullback j).obj N)
    (gW : M.val.obj (op W) →+ N.val.obj (op W))
    (gV : M.val.obj (op V) →+ N.val.obj (op V))
    (hgW : gW = GluedAdjunctionChartSectionMap.hom j M N W hW a)
    (hgV : gV = GluedAdjunctionChartSectionMap.hom j M N V hV a)
    (m : M.val.obj (op W)) :
    gV (M.val.map (homOfLE h).op m) = N.val.map (homOfLE h).op (gW m) := by
  subst gW
  subst gV
  exact GluedAdjunctionSectionNaturality.hom_res j M N W V h hW hV a m

/-- Bijectivity retains the given original additive map. -/
theorem hom_bijective (W : X.Opens) (hW : j ''ᵁ (j ⁻¹ᵁ W) = W)
    (e : (schemeModulePullback j).obj M ≅ (schemeModulePullback j).obj N)
    (g : M.val.obj (op W) →+ N.val.obj (op W))
    (hg : g = GluedAdjunctionChartSectionMap.hom j M N W hW e.hom) :
    Function.Bijective g := by
  subst g
  exact GluedAdjunctionChartSectionMap.hom_bijective j M N W hW e

end KltDP.Geometry.GluedAdjunctionNamedSectionLaws
