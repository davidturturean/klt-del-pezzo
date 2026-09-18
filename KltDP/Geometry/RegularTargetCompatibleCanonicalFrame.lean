import KltDP.Geometry.NormalModelFrameNormalization
import KltDP.Geometry.NormalModelCanonicalReferenceTransfer
import KltDP.Geometry.NormalModelFrameOverCanonicalReference
import KltDP.Geometry.RegularSurfacePointCanonicalFrame
import KltDP.Geometry.CanonicalOpenNeighborhoodExtension
import KltDP.Geometry.CanonicalWeilDivisor

/-!
# The compatible original canonical frame over a regular target neighborhood

The original target canonical divisor chooses its dense canonical reference.
A genuine native frame near the regular image extends that exact reference.
The compiled compatible-source-frame construction, actual reference transfer,
and literal preimage restriction then supply the same source canonical order
on a neighborhood mapping into the new target reference. Every original
Cartier numerator is identified there by the ordinary local extension theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RegularTargetCompatibleCanonicalFrame

open NormalModelCanonical OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain

local instance compatibleFramePrimeDVR {k : Type u} [Field k]
    (S : NormalProjectiveSurface k) (C : S.PrimeCurve) :
    IsDiscreteValuationRing (S.toScheme.presheaf.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- Derive the actual local target reference, normalized source frame,
whole-neighborhood map, original KS coefficient and every Cartier numerator
identity from the original canonical data and regular closed image. -/
theorem exists_compatible_frame
    {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) = KX)
    (C : S.PrimeCurve)
    (hclosed : IsClosed ({π.base C.genericPoint} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme (π.base C.genericPoint)) :
    ∃ (W : X.toScheme.Opens) (hxW : π.base C.genericPoint ∈ W),
      IsAffineOpen W ∧
      letI : Nonempty W.toScheme := ⟨⟨π.base C.genericPoint, hxW⟩⟩
      letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
      ∃ (KW : CartierDivisor W.toScheme)
        (eKW : cartierDivisorModule W.toScheme KW ≅
          SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            (W.ι ≫ X.structureMorphism) 2)
        (G : LocalFrame (π ≫ X.structureMorphism) C.genericPoint)
        (p : G.neighborhood ⟶ W.toScheme),
        p ≫ W.ι = G.toModel ≫ π ∧
        IsNormalized X W KW eKW π C.genericPoint G ∧
        G.order = S.cartierToWeilHom KS C ∧
        ∀ (n : ℕ) (A : CartierDivisor X.toScheme), X.cartierToWeilHom A = n • KX →
          n • KW = cartierRestrictionHom W.ι A := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI := C.genericPoint_isDiscreteValuationRing
  obtain ⟨U, hne, hcanonicalU⟩ := hcanonical
  letI : Nonempty U.toScheme := hne
  letI : Nonempty U := ⟨Classical.choice hne⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨hsmooth, hU, KU, ⟨eKU⟩, hKU⟩ := hcanonicalU
  obtain ⟨F, hF, hForder⟩ := NormalModelFrameNormalization.exists_normalized_frame
    S X π hbir π (𝟙 S.toScheme) (𝟙 S.toScheme) (by simp) hπ
    C.genericPoint C.genericPoint rfl C rfl KS eKS U hU KU eKU
    (hpush.trans hKU.symm)
  obtain ⟨W, hxW, hW, heW⟩ := X.exists_regular_closed_native_canonical_frame
    S.structureMorphism π hπ hbir (π.base C.genericPoint) hclosed hregular
  letI : Nonempty W.toScheme := ⟨⟨π.base C.genericPoint, hxW⟩⟩
  letI : Nonempty W := ⟨⟨π.base C.genericPoint, hxW⟩⟩
  letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let eW := Classical.choice heW
  obtain ⟨KW, eKW, hcoordinate, _, hmultiple⟩ :=
    CanonicalOpenNeighborhoodExtension.exists_canonical_representative
      X U W hU KU eKU KX hKU eW
  letI : Nonempty (U ⊓ W).toScheme :=
    CanonicalNeighborhoodCartierMultiple.intersection_nonempty U W
  have hFW : IsNormalized X W KW eKW π C.genericPoint F :=
    isNormalized_of_reference_overlap X U W (U ⊓ W) inf_le_left inf_le_right
      KU KW eKU eKW hcoordinate π C.genericPoint F hF
  obtain ⟨G, p, hp, hG, hGorder⟩ := exists_frame_over_reference
    X W KW eKW π C.genericPoint F hFW hxW
  exact ⟨W, hxW, hW, KW, eKW, G, p, hp, hG, hGorder.trans hForder, hmultiple⟩

end KltDP.Geometry.RegularTargetCompatibleCanonicalFrame

#check @KltDP.Geometry.RegularTargetCompatibleCanonicalFrame.exists_compatible_frame
#print axioms KltDP.Geometry.RegularTargetCompatibleCanonicalFrame.exists_compatible_frame
