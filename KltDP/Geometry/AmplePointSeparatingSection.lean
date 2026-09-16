import KltDP.Geometry.SchemeKernelTensorVanishing
import KltDP.Geometry.InvertibleSheafFrameWithin
import KltDP.Geometry.SchemeKernelCoherent
import KltDP.Geometry.GloballyGeneratedImageSection
import KltDP.Geometry.AmpleSerre

/-!
# Actual ample sections separating a closed point from a distinct point

The original closed-point ideal is coherent on a locally Noetherian
scheme. Serre ampleness makes its twist by a positive tensor power
globally generated. On an actual frame neighborhood of a distinct point,
the original tensor ideal inclusion is an epimorphism. The generating
section argument gives an original preimage section whose image has a
unit coefficient germ there. The proved actual pullback equation makes
that same image vanish on the residue-field scheme of the chosen closed
point.

The ambient scheme is integral for the accepted Cartier construction of
a frame within a prescribed neighborhood. No point-ideal coherence,
local epi, frame, or section-existence witness is assumed in the ample
consumer. This produces actual sections; conversion to a nonempty
effective-Cartier intersection and strict curve degree is subsequent work.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AmplePointSeparatingSection

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X]

local instance (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

/-- Global generation of the actual point-ideal twist supplies an actual
image section vanishing at that point and with unit germ in an actual
frame at any distinct point. Its original preimage section is retained. -/
theorem exists_point_separating_image_section (L : InvertibleSheaf X)
    (x y : X) (hclosed : IsClosed ({x} : Set X)) (hne : y ≠ x)
    (hL : Positivity.IsGloballyGenerated
      (L.obj ⊗ schemeKernelIdeal (X.fromSpecResidueField x))) :
    ∃ (U : X.Opens) (hyU : y ∈ U)
      (e : L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
      (s : (L.obj ⊗ schemeKernelIdeal (X.fromSpecResidueField x)).val.obj (op ⊤)),
      x ∉ U ∧
      (SchemeKernelTensor.inclusion (X.fromSpecResidueField x) L.obj).val.app (op ⊤) s ≠ 0 ∧
      RationalTreePicard.pulledSection (X.fromSpecResidueField x) L.obj ⊤
        ((SchemeKernelTensor.inclusion (X.fromSpecResidueField x) L.obj).val.app
          (op ⊤) s) = 0 ∧
      IsUnit (X.presheaf.germ U y hyU
        (e.hom.val.app (op (Over.mk (𝟙 U)))
          (L.obj.val.map (homOfLE (le_top : U ≤ ⊤)).op
            ((SchemeKernelTensor.inclusion (X.fromSpecResidueField x) L.obj).val.app
              (op ⊤) s)))) := by
  let V : X.Opens := ⟨({x} : Set X)ᶜ, hclosed.isOpen_compl⟩
  have hyV : y ∈ V := fun hy => hne (Set.mem_singleton_iff.mp hy)
  obtain ⟨U, hUV, hyU, ⟨e⟩⟩ :=
    InvertibleSheafFrameWithin.exists_unit_frame_within L V y hyV
  have hxU : x ∉ U := fun hxU => hUV hxU (Set.mem_singleton x)
  letI := SchemeKernelTensor.point_over_inclusion_epi X x L.obj U hxU
  obtain ⟨s, hs, hu⟩ := GloballyGeneratedImageSection.exists_nonzero_image_section
    hL (SchemeKernelTensor.inclusion (X.fromSpecResidueField x) L.obj) U y hyU e
  exact ⟨U, hyU, e, s, hxU, hs,
    SchemeKernelTensor.pulledSection_inclusion_eq_zero (X.fromSpecResidueField x) L ⊤ s, hu⟩

/-- Serre ampleness produces a positive power with an actual section
vanishing at a chosen closed point and having unit germ at a distinct
point. All ideal, frame, epi, and generating-section data are proved. -/
theorem exists_positive_power_point_separating_section [IsLocallyNoetherian X]
    (L : InvertibleSheaf X) (hL : AmpleSerre.IsAmple L)
    (x y : X) (hclosed : IsClosed ({x} : Set X)) (hne : y ≠ x) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (M : InvertibleSheaf X), M.toPic = L.toPic ^ n ∧
      ∃ (U : X.Opens) (hyU : y ∈ U)
        (e : M.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
        (s : (M.obj ⊗ schemeKernelIdeal (X.fromSpecResidueField x)).val.obj (op ⊤)),
        x ∉ U ∧
        (SchemeKernelTensor.inclusion (X.fromSpecResidueField x) M.obj).val.app (op ⊤) s ≠ 0 ∧
        RationalTreePicard.pulledSection (X.fromSpecResidueField x) M.obj ⊤
          ((SchemeKernelTensor.inclusion (X.fromSpecResidueField x) M.obj).val.app
            (op ⊤) s) = 0 ∧
        IsUnit (X.presheaf.germ U y hyU
          (e.hom.val.app (op (Over.mk (𝟙 U)))
            (M.obj.val.map (homOfLE (le_top : U ≤ ⊤)).op
              ((SchemeKernelTensor.inclusion (X.fromSpecResidueField x) M.obj).val.app
                (op ⊤) s)))) := by
  obtain ⟨N, hN⟩ := hL (schemeKernelIdeal (X.fromSpecResidueField x))
    (closedPointKernel_isCoherentModule X x hclosed)
  obtain ⟨M, hM, hGG⟩ := hN (N + 1) (Nat.le_succ N)
  exact ⟨N + 1, Nat.succ_pos N, M, hM,
    exists_point_separating_image_section M x y hclosed hne hGG⟩

end KltDP.Geometry.AmplePointSeparatingSection
