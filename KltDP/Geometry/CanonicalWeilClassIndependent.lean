import KltDP.Geometry.CanonicalWeilDivisor
import KltDP.Geometry.CanonicalRepresentativeCommonOpen
import KltDP.Geometry.OpenCartierWeilNestedRestriction
import KltDP.Geometry.OpenCartierWeilPrincipal

/-!
# The Weil class of genuine canonical representatives

Intersect the two original canonical opens. Their actual Cartier
restrictions differ by a principal divisor, by the original exterior
differential comparison. Exact nested restriction and principal extension
then compare the original Weil divisors on the whole surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.IsCanonicalWeilDivisor

open OpenImmersionRational

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    {D E : X.WeilDivisor}

/-- Two genuine canonical Weil divisors on the same original surface
differ by an actual principal Weil divisor. -/
theorem linearlyEquivalent (hD : IsCanonicalWeilDivisor X D)
    (hE : IsCanonicalWeilDivisor X E) : X.LinearlyEquivalent D E := by
  obtain ⟨U, hneU, hsmoothU, hU, KU, ⟨eKU⟩, hKU⟩ := hD
  letI : Nonempty U.toScheme := hneU
  letI : Nonempty U := ⟨Classical.choice hneU⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨V, hneV, hsmoothV, hV, KV, ⟨eKV⟩, hKV⟩ := hE
  letI : Nonempty V.toScheme := hneV
  letI : Nonempty V := ⟨Classical.choice hneV⟩
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let W : X.toScheme.Opens := U ⊓ V
  have hW : ∀ C : X.PrimeCurve, C.genericPoint ∈ W := fun C => ⟨hU C, hV C⟩
  letI : Nonempty W.toScheme := OpenCartierWeil.nonempty_of_primeGenericPoint_mem W hW
  letI : Nonempty W := ⟨Classical.choice inferInstance⟩
  letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let jU : W.toScheme ⟶ U.toScheme :=
    X.toScheme.homOfLE (show W ≤ U from inf_le_left)
  let jV : W.toScheme ⟶ V.toScheme :=
    X.toScheme.homOfLE (show W ≤ V from inf_le_right)
  letI : IsOpenImmersion jU := inferInstanceAs (IsOpenImmersion (X.toScheme.homOfLE _))
  letI : IsOpenImmersion jV := inferInstanceAs (IsOpenImmersion (X.toScheme.homOfLE _))
  have hbase : jU ≫ (U.ι ≫ X.structureMorphism) =
      jV ≫ (V.ι ≫ X.structureMorphism) := by
    dsimp only [jU, jV]
    rw [← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc, Scheme.homOfLE_ι]
  obtain ⟨f, hf⟩ := CanonicalRepresentativeCommonOpen.exists_principal_difference
    (U.ι ≫ X.structureMorphism) (V.ι ≫ X.structureMorphism)
    jU jV hbase 2 KU KV eKU eKV
  have hDU : OpenCartierWeil.restrictedWeilHom W (cartierRestrictionHom jU KU) = D :=
    (OpenCartierWeil.restrictedWeilHom_nestedRestriction U W inf_le_left hW KU).trans hKU
  have hEV : OpenCartierWeil.restrictedWeilHom W (cartierRestrictionHom jV KV) = E :=
    (OpenCartierWeil.restrictedWeilHom_nestedRestriction V W inf_le_right hW KV).trans hKV
  have hlin := OpenCartierWeil.restrictedWeilHom_linearlyEquivalent_of_principal
    W hW (cartierRestrictionHom jU KU) (cartierRestrictionHom jV KV) f hf
  simpa only [hDU, hEV] using hlin

/-- The actual Weil class is independent of the canonical open and its
Cartier representative of the original top differentials. -/
theorem weilClassMap_eq (hD : IsCanonicalWeilDivisor X D)
    (hE : IsCanonicalWeilDivisor X E) : X.weilClassMap D = X.weilClassMap E :=
  (X.linearlyEquivalent_iff_weilClassMap_eq D E).mp (linearlyEquivalent hD hE)

end KltDP.Geometry.IsCanonicalWeilDivisor
