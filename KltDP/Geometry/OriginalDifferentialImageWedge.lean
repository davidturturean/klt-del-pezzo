import KltDP.Geometry.OriginalDifferentialImageSection

/-!
# The original differential image on section wedges

Normalize the original adjunction-unit definition and its original open
restriction while the source and target schemes remain abstract. The
scalar comparison can then be specialized to the actual affine maps
without unfolding the concrete differential sheaf construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OriginalDifferentialImageWedge

open SchemeKaehlerSheaf NormalizedDifferentialCoefficientOrder

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (π : Y ⟶ X) (hπ : π ≫ f = g)

/-- The alias uses exactly the original adjunction-unit wedge formula. -/
theorem imageSection_wedge_d (U : X.Opens) (s : Fin 2 → Γ(X, U)) :
    imageSection f g π hπ U (SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
      (fun i => (baseRingDerivation f).d (s i))) =
      SchemeExteriorPower.wedge (baseRingSheaf g) 2 (π ⁻¹ᵁ U)
        (fun i => (baseRingDerivation g).d (π.app U (s i))) :=
  SchemeKaehlerExteriorPullbackTransport.map_unit_wedge_d f π g hπ 2 U s

/-- The original section restriction retains the original `appLE` map. -/
theorem imageSection_wedge_d_restrict (U : X.Opens) (V : Y.Opens)
    (hVU : V ≤ π ⁻¹ᵁ U) (s : Fin 2 → Γ(X, U)) :
    (SchemeExteriorPower.sheaf (baseRingSheaf g) 2).val.map (homOfLE hVU).op
      (imageSection f g π hπ U (SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
        (fun i => (baseRingDerivation f).d (s i)))) =
      SchemeExteriorPower.wedge (baseRingSheaf g) 2 V
        (fun i => (baseRingDerivation g).d (π.appLE U V hVU (s i))) := by
  rw [imageSection_wedge_d f g π hπ U s, SchemeExteriorPower.wedge_restrict]
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf g) 2 V)
  funext i
  exact ((baseRingDerivation g).d_map (homOfLE hVU).op (π.app U (s i))).symm

/-- Only the actual scalar section equation is used in specialization. -/
theorem imageSection_wedge_d_restrict_of_appLE (U : X.Opens) (V : Y.Opens)
    (hVU : V ≤ π ⁻¹ᵁ U) (s : Fin 2 → Γ(X, U)) (t : Fin 2 → Γ(Y, V))
    (hst : ∀ i, π.appLE U V hVU (s i) = t i) :
    (SchemeExteriorPower.sheaf (baseRingSheaf g) 2).val.map (homOfLE hVU).op
      (imageSection f g π hπ U (SchemeExteriorPower.wedge (baseRingSheaf f) 2 U
        (fun i => (baseRingDerivation f).d (s i)))) =
      SchemeExteriorPower.wedge (baseRingSheaf g) 2 V
        (fun i => (baseRingDerivation g).d (t i)) := by
  refine (imageSection_wedge_d_restrict f g π hπ U V hVU s).trans ?_
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf g) 2 V)
  exact funext (fun i => congrArg (baseRingDerivation g).d (hst i))

end KltDP.Geometry.OriginalDifferentialImageWedge

#check @KltDP.Geometry.OriginalDifferentialImageWedge.imageSection_wedge_d_restrict_of_appLE
#print axioms KltDP.Geometry.OriginalDifferentialImageWedge.imageSection_wedge_d_restrict_of_appLE
