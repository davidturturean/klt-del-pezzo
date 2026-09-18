import KltDP.Geometry.RegularSurfacePointNativeNeighborhood
import KltDP.Geometry.NativeDifferentialCanonicalFrame

/-!
# An actual canonical module frame near the original regular point

Choose an original affine chart and apply native basis spreading. Its actual
principal open contains x, and the native determinant gives O(0) ≅ Ω² there.
This is the local frame stage; normalization to a specified target canonical
Weil divisor is a separate principal-coordinate comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open IntrinsicNodal SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) {S : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]
    (π : S ⟶ X.toScheme) (hπ : π ≫ X.structureMorphism = f)
    (hbir : IsBirationalScheme π)

include hSmooth hπ hbir in
/-- The original regular point has a genuine affine canonical module frame.
No frame, local canonical representative, or target smoothness is assumed. -/
theorem exists_regular_closed_native_canonical_frame
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x) :
    ∃ (V : X.toScheme.Opens) (hxV : x ∈ V), IsAffineOpen V ∧
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
      Nonempty (cartierDivisorModule V.toScheme 0 ≅
        relativeDifferentialExterior (V.ι ≫ X.structureMorphism) 2) := by
  let U : X.toScheme.Opens := (X.toScheme.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.toScheme.affineCover.map x)
  have hxU : x ∈ U := X.toScheme.affineCover.covers x
  letI := affineSectionsAlgebra X.structureMorphism hU
  letI := stalkAlgebra X.structureMorphism x
  letI := X.toScheme.presheaf.algebra_section_stalk ⟨x, hxU⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower X.structureMorphism hU x hxU
  letI := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨r, hr, v, b, hv, hb, hprimitive, hopen, y, hy⟩ :=
    X.exists_regular_closed_principal_native_basis f π hπ hbir x hclosed hregular hU hxU
  let j : Spec (CommRingCat.of (Localization.Away r)) ⟶ X.toScheme :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X.toScheme, U) (Localization.Away r))) ≫
      hU.fromSpec
  letI : IsOpenImmersion j := hopen
  letI : Nonempty (Spec (CommRingCat.of (Localization.Away r))) := ⟨y⟩
  have hxj : x ∈ j.opensRange := ⟨y, hy⟩
  letI : Nonempty j.opensRange := ⟨⟨x, hxj⟩⟩
  have hscalar : baseToAffineSectionsMap X.structureMorphism hU ≫
      CommRingCat.ofHom (algebraMap Γ(X.toScheme, U) (Localization.Away r)) =
      CommRingCat.ofHom (algebraMap k (Localization.Away r)) := by
    change CommRingCat.ofHom ((algebraMap Γ(X.toScheme, U) (Localization.Away r)).comp
      (algebraMap k Γ(X.toScheme, U))) = _
    exact congrArg CommRingCat.ofHom
      (IsScalarTower.algebraMap_eq k Γ(X.toScheme, U) (Localization.Away r)).symm
  have hstructure : j ≫ X.structureMorphism =
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X.toScheme, U) (Localization.Away r))) ≫ hU.fromSpec) ≫ _ = _
    rw [Category.assoc, ← Spec_map_baseToAffineSectionsMap X.structureMorphism hU,
      ← Spec.map_comp, hscalar]
  exact ⟨j.opensRange, hxj, isAffineOpen_opensRange j,
    ⟨NativeDifferentialCanonicalFrame.zeroIsoOnRange k (Localization.Away r)
      j X.structureMorphism hstructure b⟩⟩

end KltDP.Geometry.NormalProjectiveSurface
