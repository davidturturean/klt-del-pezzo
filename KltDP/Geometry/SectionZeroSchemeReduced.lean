import KltDP.Geometry.SectionZeroScheme
import KltDP.Geometry.SectionEffectiveWeil
import KltDP.Geometry.CartierIdealReduced

/-!
# Reducedness of the original section's actual zero scheme

For an original section-preserving Cartier representative, actual regular
equations imply effectivity of its original finite Weil divisor. Coefficients
at most one and factoriality of the original surface stalks therefore make
its original Cartier ideal radical. The already proved all-open image-ideal
equality transfers this to the original section-image subsheaf.

The resulting radical ideal data and reduced scheme are the existing
nonzeroSectionIdealData and its actual gluing. The original closed immersion
and its normalized dual-evaluation kernel are retained literally. No square
root, replacement zero scheme, or reducedness premise is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

/-- The original section-image ideal is radical on every original open.
Effectivity is derived from the original regular equations. -/
theorem nonzeroSectionImage_isRadical_of_cartier
    (L : InvertibleSheaf X.toScheme)
    (s : L.obj.val.obj (op (⊤ : X.toScheme.Opens)))
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    (e : cartierDivisorModule X.toScheme E ≅ L.obj)
    (he : e.hom.val.app (op (⊤ : X.toScheme.Opens))
      (effectiveCartierSection X.toScheme E hE) = s)
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) (W : X.toScheme.Opens) :
    (sectionImageIdeal X.toScheme L.obj s W).IsRadical := by
  rw [← sectionImageIdeal_eq_of_iso X.toScheme e
    (effectiveCartierSection X.toScheme E hE) s he W,
    ← cartierSectionIdeal_eq_imageIdeal_of_regularEquations X.toScheme E hE W]
  exact X.cartierSectionIdeal_isRadical E
    (X.effective_cartierToWeilHom_of_regularEquations E hE) hE_one W

/-- The exact original zero ideal data is radical, without an auxiliary square-root line. -/
theorem nonzeroSectionIdealData_radical_of_cartier
    (L : InvertibleSheaf X.toScheme)
    (s : L.obj.val.obj (op (⊤ : X.toScheme.Opens))) (hs : s ≠ 0)
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    (e : cartierDivisorModule X.toScheme E ≅ L.obj)
    (he : e.hom.val.app (op (⊤ : X.toScheme.Opens))
      (effectiveCartierSection X.toScheme E hE) = s)
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) :
    (nonzeroSectionIdealData X.toScheme L s hs).radical =
      nonzeroSectionIdealData X.toScheme L s hs := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.radical_ideal, nonzeroSectionIdealData_ideal]
  exact (X.nonzeroSectionImage_isRadical_of_cartier L s E hE e he hE_one U.1).radical

/-- The original closed zero scheme is reduced. Its original inclusion and
the original dual-evaluation kernel are unchanged. -/
theorem nonzeroSectionZero_isReduced_of_cartier
    (L : InvertibleSheaf X.toScheme)
    (s : L.obj.val.obj (op (⊤ : X.toScheme.Opens))) (hs : s ≠ 0)
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    (e : cartierDivisorModule X.toScheme E ≅ L.obj)
    (he : e.hom.val.app (op (⊤ : X.toScheme.Opens))
      (effectiveCartierSection X.toScheme E hE) = s)
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1) :
    AlgebraicGeometry.IsReduced (nonzeroSectionIdealData X.toScheme L s hs).glueData.glued :=
  Scheme.IdealSheafData.glued_isReduced
    (nonzeroSectionIdealData X.toScheme L s hs)
    (X.nonzeroSectionIdealData_radical_of_cartier L s hs E hE e he hE_one)

end KltDP.Geometry.NormalProjectiveSurface
