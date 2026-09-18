import KltDP.Geometry.OriginalDifferentialImageSection
import KltDP.Geometry.CartierFrameSectionCoefficient

/-!
# Original Cartier coefficients of actual differential image sections

The original adjunction-unit pullback is semilinear and the original
differential map is linear. Therefore the actual image coefficient of
any target section is its pulled original target coefficient times the
image coefficient of the original target Cartier frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.NormalizedDifferentialCoefficientOrder

open SmoothCanonicalExteriorComparison CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (π : Y ⟶ X) (hπ : π ≫ f = g)

/-- Semilinearity is inherited from the literal original pullback unit. -/
theorem imageSection_smul (U : X.Opens) (a : Γ(X, U))
    (s : (relativeDifferentialExterior f 2).val.obj (op U)) :
    imageSection f g π hπ U (a • s) = π.app U a • imageSection f g π hπ U s := by
  unfold imageSection
  rw [pullbackSection_smul, map_smul]

/-- Original restriction gives precisely the original `appLE` scalar. -/
theorem imageSection_restrict_smul (U : X.Opens) (V : Y.Opens)
    (hVU : V ≤ π ⁻¹ᵁ U) (a : Γ(X, U))
    (s : (relativeDifferentialExterior f 2).val.obj (op U)) :
    (relativeDifferentialExterior g 2).val.map (homOfLE hVU).op
        (imageSection f g π hπ U (a • s)) =
      π.appLE U V hVU a • (relativeDifferentialExterior g 2).val.map (homOfLE hVU).op
        (imageSection f g π hπ U s) := by
  rw [imageSection_smul, map_smul]
  rfl

private theorem sectionCoefficient_smul
    (Z : Scheme.{u}) [IsIntegral Z] (D : CartierDivisor Z)
    (M : Z.Modules) (e : cartierDivisorModule Z D ≅ M)
    (c : CartierEquationChart Z D) (a : Γ(Z, c.openSet))
    (s : M.val.obj (op c.openSet)) :
    sectionCoefficient Z D M e c (a • s) = a * sectionCoefficient Z D M e c s := by
  unfold sectionCoefficient
  rw [(e.inv.val.app (op c.openSet)).hom.map_smul, LinearEquiv.map_smul, smul_eq_mul]

/-- This is the coefficient of the actual image of the original target
Cartier frame, multiplied by the actual pulled coefficient of the section. -/
theorem sectionCoefficient_image
    [IsIntegral X] [IsIntegral Y]
    (DT : CartierDivisor X) (DS : CartierDivisor Y)
    (eT : cartierDivisorModule X DT ≅ relativeDifferentialExterior f 2)
    (eS : cartierDivisorModule Y DS ≅ relativeDifferentialExterior g 2)
    (cT : CartierEquationChart X DT) (cS : CartierEquationChart Y DS)
    (hST : cS.openSet ≤ π ⁻¹ᵁ cT.openSet)
    (s : (relativeDifferentialExterior f 2).val.obj (op cT.openSet)) :
    sectionCoefficient Y DS (relativeDifferentialExterior g 2) eS cS
        ((relativeDifferentialExterior g 2).val.map (homOfLE hST).op
          (imageSection f g π hπ cT.openSet s)) =
      π.appLE cT.openSet cS.openSet hST
          (sectionCoefficient X DT (relativeDifferentialExterior f 2) eT cT s) *
        sectionCoefficient Y DS (relativeDifferentialExterior g 2) eS cS
          ((relativeDifferentialExterior g 2).val.map (homOfLE hST).op
            (imageSection f g π hπ cT.openSet
              (frame X DT (relativeDifferentialExterior f 2) eT cT))) := by
  have h := congrArg (fun t =>
    sectionCoefficient Y DS (relativeDifferentialExterior g 2) eS cS
      ((relativeDifferentialExterior g 2).val.map (homOfLE hST).op
        (imageSection f g π hπ cT.openSet t)))
    (sectionCoefficient_smul_frame X DT (relativeDifferentialExterior f 2) eT cT s)
  dsimp only at h
  rw [imageSection_restrict_smul, sectionCoefficient_smul] at h
  exact h.symm

end KltDP.Geometry.NormalizedDifferentialCoefficientOrder

#check @KltDP.Geometry.NormalizedDifferentialCoefficientOrder.sectionCoefficient_image
#print axioms KltDP.Geometry.NormalizedDifferentialCoefficientOrder.sectionCoefficient_image
