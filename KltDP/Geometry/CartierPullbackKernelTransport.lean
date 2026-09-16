import KltDP.Geometry.CartierDivisorPullbackIdeal
import KltDP.Geometry.CartierDivisorPullbackAdd
import KltDP.Geometry.KernelIdealIsoTransport

/-!
# Actual kernel ideals of Cartier pullbacks along open immersions

The ideal data of a regular effective Cartier divisor pulls back along an
open immersion to the kernel of the actual base-changed closed subscheme.
The proof compares regular generators with the original section-ring
isomorphism on each affine image. It uses the pinned kernel base-change
theorem and proves equality of ideal data, retaining the inclusions into
the structure sheaf.

The isomorphism-square specialization supplies generic-point preservation
and the pullback square from the two actual isomorphisms. The source ideal
identification is explicit data, not a proposed identity on the target.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierPullbackKernelTransport

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackAdd

variable {X Y Z Z' : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Cartier pullback along an open immersion has the kernel ideal of the
actual base change of the original zero scheme. -/
theorem pullbackIdealData_eq_kernel (π : X ⟶ Y) [IsOpenImmersion π]
    [GenericPointPreserving π] (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D) (ι : Z ⟶ Y) [QuasiCompact ι]
    (ι' : Z' ⟶ X) (j : Z' ⟶ Z) (H : IsPullback ι' j π ι)
    (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = ι.ker) :
    pullbackIdealData π D hD = ι'.ker := by
  apply IdealSheafData.ext_of_affine_cover _ _
    (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet)
    (fun x => hD (π.base x))
  intro c W hW
  apply IdealSheafData.ideal_eq_of_nonempty
  intro hne
  letI : Nonempty W.1 := hne
  let V : Y.affineOpens := ⟨π ''ᵁ W.1, W.2.image_of_isOpenImmersion π⟩
  have hV : V.1 ≤ c.chart.openSet := by
    rintro _ ⟨x, hx, rfl⟩
    exact hW hx
  letI : Nonempty V.1 := by
    obtain ⟨x⟩ := hne
    exact ⟨⟨π.base x.1, ⟨x.1, x.2, rfl⟩⟩⟩
  have hspan : (effectiveCartierIdealDataOfRegularEquations Y D hD).ideal V =
      Ideal.span {Y.presheaf.map (homOfLE hV).op c.coefficient} :=
    effectiveCartierIdealDataOfRegularEquations_ideal_chart Y D hD
      (RegularCartierEquationChart.restrict Y D c V.1 hV) V.2
  have hcoef : π.appLE c.chart.openSet W.1 hW c.coefficient =
      (π.appIso W.1).hom (Y.presheaf.map (homOfLE hV).op c.coefficient) := by
    change _ = (Y.presheaf.map (homOfLE hV).op ≫ (π.appIso W.1).hom) c.coefficient
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  calc
    (pullbackIdealData π D hD).ideal W =
        Ideal.span {π.appLE c.chart.openSet W.1 hW c.coefficient} :=
      pullbackIdealData_ideal π D hD c W hW
    _ = Ideal.span {(π.appIso W.1).hom
        (Y.presheaf.map (homOfLE hV).op c.coefficient)} :=
      congrArg (fun s => Ideal.span {s}) hcoef
    _ = ((effectiveCartierIdealDataOfRegularEquations Y D hD).ideal V).comap
        (π.appIso W.1).inv.hom := by
      rw [hspan, Ideal.comap_inv_eq_map_hom, Ideal.map_span, Set.image_singleton]
    _ = ι'.ker.ideal W := by
      rw [hI]
      exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion ι ι' j π H W).symm

/-- An actual commuting square with isomorphisms on its vertical sides
transports the divisor's ideal to the actual target kernel. -/
theorem pullbackIdealData_eq_kernel_of_iso (e : X ≅ Y)
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
    (ι : Z ⟶ Y) [QuasiCompact ι] (ι' : Z' ⟶ X) (j : Z' ≅ Z)
    (sq : ι' ≫ e.hom = j.hom ≫ ι)
    (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = ι.ker) :
    pullbackIdealData e.hom D hD = ι'.ker :=
  pullbackIdealData_eq_kernel e.hom D hD ι ι' j.hom
    (IsPullback.of_vert_isIso ⟨sq⟩) hI

end KltDP.Geometry.CartierPullbackKernelTransport
