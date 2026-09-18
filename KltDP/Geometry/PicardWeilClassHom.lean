import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.CartierWeilClassMap
import KltDP.Geometry.InvertibleSheafPicard

/-!
# The actual Picard group maps to the actual Weil class group

Compose the inverse of the existing Cartier-class/Picard equivalence with
the existing Cartier-to-Weil class homomorphism. The map is defined for the
original normal projective surface over any field. No factoriality,
algebraic-closure, regularity, or inverse Weil-to-Picard comparison is used.
Its representative formula uses the original Cartier divisor sheaf O(D).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

/-- The one-way map from original Picard classes to original Weil classes. -/
def picardToWeilClassHom : Additive S.toScheme.Pic →+ S.WeilClassGroup :=
  S.cartierClassToWeilClassHom.comp
    (cartierClassPicardEquiv S.toScheme).symm.toAddMonoidHom

/-- On an actual Cartier divisor, the map is its original Weil-divisor class. -/
theorem picardToWeilClassHom_cartierPicardHom (D : CartierDivisor S.toScheme) :
    S.picardToWeilClassHom (cartierPicardHom S.toScheme D) =
      S.weilClassMap (S.cartierToWeilHom D) := by
  have hD : cartierClassPicardEquiv S.toScheme (cartierClassMap S.toScheme D) =
      cartierPicardHom S.toScheme D := rfl
  change S.cartierClassToWeilClassHom
    ((cartierClassPicardEquiv S.toScheme).symm (cartierPicardHom S.toScheme D)) = _
  rw [← hD, AddEquiv.symm_apply_apply]
  exact S.cartierClassToWeilClassHom_class D

/-- An actual isomorphism to O(D) gives the same Weil class. The sheaf-class
comparison is proved from the isomorphism, not supplied as a premise. -/
theorem picardToWeilClassHom_of_module_iso
    (L : InvertibleSheaf S.toScheme) (D : CartierDivisor S.toScheme)
    (e : L.obj ≅ cartierDivisorModule S.toScheme D) :
    S.picardToWeilClassHom (Additive.ofMul L.toPic) =
      S.weilClassMap (S.cartierToWeilHom D) := by
  have hL : L.toPic = cartierPicardClass S.toScheme D := by
    letI := Scheme.Modules.monoidalCategory S.toScheme
    apply Units.ext
    change (L.toPic : Skeleton S.toScheme.Modules) =
      (cartierPicardClass S.toScheme D : Skeleton S.toScheme.Modules)
    rw [InvertibleSheaf.toPic_val, cartierPicardClass_val]
    exact Quotient.sound ⟨e⟩
  rw [hL]
  exact S.picardToWeilClassHom_cartierPicardHom D

end KltDP.Geometry.NormalProjectiveSurface
