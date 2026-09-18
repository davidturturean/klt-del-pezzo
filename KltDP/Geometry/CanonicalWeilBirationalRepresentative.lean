import KltDP.Geometry.CanonicalWeilDivisor
import KltDP.Geometry.OpenCartierWeilNestedRestriction
import KltDP.Geometry.CanonicalCartierOpenPullback
import KltDP.Geometry.CanonicalCartierRepresentativePushforward
import KltDP.Geometry.SmoothOpenCanonicalWeilChoice
import KltDP.Geometry.ProperBirationalCanonicalOpen

/-!
# A compatible canonical divisor above any actual canonical Weil divisor

Shrink the original canonical open to the isomorphism open of the original
proper birational morphism. Exact Cartier-order restriction preserves its
Weil extension. The existing canonical class comparison and principal
correction then produce the exact target representative, with the original
top differential sheaf on the smooth source.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

private theorem isIso_morphismRestrict_of_le
    {S X : Scheme.{u}} (π : S ⟶ X) (U V : X.Opens)
    [IsIso (π ∣_ U)] (hVU : V ≤ U) : IsIso (π ∣_ V) := by
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    ext x
    change (∃ y : U, y.val ∈ V ∧ y.val = x) ↔ x ∈ V
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hVU hx⟩, hx, rfl⟩
  let e := morphismRestrictRestrict π U (U.ι ⁻¹ᵁ V) ≪≫
    morphismRestrictEq π himage
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp
    (inferInstanceAs (IsIso ((π ∣_ U) ∣_ (U.ι ⁻¹ᵁ V))))

namespace IsCanonicalWeilDivisor

variable {k : Type u} [Field k] (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π)

include hπ in
/-- Every genuine canonical Weil divisor on the target has an exactly
compatible Cartier representative of the original top differentials on
the smooth source of the original proper birational morphism. -/
theorem exists_compatible_canonical_cartier
    (KX : X.WeilDivisor) (hKX : IsCanonicalWeilDivisor X KX) :
    ∃ KS : CartierDivisor S.toScheme,
      Nonempty (cartierDivisorModule S.toScheme KS ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          S.structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) = KX := by
  obtain ⟨U, hne, hsmooth, hU, KU, ⟨eKU⟩, hKU⟩ := hKX
  letI : Nonempty U.toScheme := hne
  letI : Nonempty U := ⟨Classical.choice hne⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let V : X.toScheme.Opens := U ⊓ targetIsomorphismOpen π
  have hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V := by
    intro C
    exact ⟨hU C,
      ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve X π hbir C⟩
  letI : Nonempty V.toScheme :=
    OpenCartierWeil.nonempty_of_primeGenericPoint_mem V hV
  letI : Nonempty V := ⟨Classical.choice inferInstance⟩
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  letI : IsIso (π ∣_ targetIsomorphismOpen π) := isIso_targetIsomorphismOpen π
  letI : IsIso (π ∣_ V) :=
    isIso_morphismRestrict_of_le π (targetIsomorphismOpen π) V inf_le_right
  letI : IsSmoothOfRelativeDimension 2 (V.ι ≫ X.structureMorphism) :=
    SmoothStructureOnIsomorphismOpen.isSmoothOfRelativeDimension
      2 S.structureMorphism X.structureMorphism π hπ V
  let j : V.toScheme ⟶ U.toScheme := X.toScheme.homOfLE (show V ≤ U from inf_le_left)
  letI : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (X.toScheme.homOfLE _))
  letI : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩
  let KV := OpenImmersionRational.cartierRestrictionHom j KU
  have hj : j ≫ (U.ι ≫ X.structureMorphism) = V.ι ≫ X.structureMorphism := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have eKV : cartierDivisorModule V.toScheme KV ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (V.ι ≫ X.structureMorphism) 2 := by
    have e := CanonicalCartierOpenPullback.canonicalModuleIso j
      (U.ι ≫ X.structureMorphism) (V.ι ≫ X.structureMorphism) hj KU eKU
    rw [DominantCartierPullback.pullbackHom_eq_cartierRestrictionHom] at e
    exact e
  have hKV : OpenCartierWeil.restrictedWeilHom V KV = KX :=
    (OpenCartierWeil.restrictedWeilHom_nestedRestriction U V inf_le_left hV KU).trans hKU
  obtain ⟨D, ⟨eD⟩, hD⟩ :=
    CanonicalWeilBirational.exists_compatible_canonical_cartier S X π hπ V hbir hV
  have hclass : X.weilClassMap
      (BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D)) =
      X.weilClassMap KX := by
    rw [hD, ← hKV]
    exact SmoothOpenCanonicalWeil.weilRepresentative_class_eq X V hV KV eKV
  obtain ⟨KS, hpush, ⟨eKS⟩⟩ :=
    BirationalWeilPushforward.exists_cartier_representative_with_pushforward
      π hbir D KX hclass
  exact ⟨KS, ⟨eKS ≪≫ eD⟩, hpush⟩

end IsCanonicalWeilDivisor
end KltDP.Geometry

#check @KltDP.Geometry.IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
#print axioms KltDP.Geometry.IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
