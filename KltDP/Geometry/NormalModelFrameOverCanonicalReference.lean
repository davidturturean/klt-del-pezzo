import KltDP.Geometry.NormalModelLocalFrameRestrictionNormalized

/-!
# A normalized frame whose whole neighborhood lies over the local reference

If the original model point maps into the actual target reference, restrict
the original frame to its literal preimage. The original restricted morphism
then provides the whole-neighborhood factorization needed by the differential
square. The same original model order and normalization are preserved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical

attribute [local instance] integralSchemeStalk_isDomain

local instance overReferenceIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (W : X.toScheme.Opens) [Nonempty W.toScheme] :
    IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι

/-- The actual point-containment hypothesis derives the original factor
through the reference; it is not supplied as a separate map premise. -/
theorem exists_frame_over_reference
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (W : X.toScheme.Opens) [Nonempty W.toScheme]
    (KW : CartierDivisor W.toScheme)
    (eKW : cartierDivisorModule W.toScheme KW ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (W.ι ≫ X.structureMorphism) 2)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X W KW eKW v x F) (hx : v.base x ∈ W) :
    ∃ (G : LocalFrame (v ≫ X.structureMorphism) x)
      (p : G.neighborhood ⟶ W.toScheme),
      p ≫ W.ι = G.toModel ≫ v ∧
      IsNormalized X W KW eKW v x G ∧ G.order = F.order := by
  let Z := (F.toModel ≫ v) ⁻¹ᵁ W
  have hZ : F.point ∈ Z := by
    change (F.toModel ≫ v).base F.point ∈ W
    rw [Scheme.comp_base_apply, F.point_eq]
    exact hx
  refine ⟨F.restrict Z hZ, (F.toModel ≫ v) ∣_ W, ?_,
    LocalFrame.restrict_isNormalized X W KW eKW v x F Z hZ hF, F.restrict_order Z hZ⟩
  change ((F.toModel ≫ v) ∣_ W) ≫ W.ι = (Z.ι ≫ F.toModel) ≫ v
  exact (morphismRestrict_ι (F.toModel ≫ v) W).trans
    (Category.assoc Z.ι F.toModel v).symm

end KltDP.Geometry.NormalModelCanonical

#check @KltDP.Geometry.NormalModelCanonical.exists_frame_over_reference
#print axioms KltDP.Geometry.NormalModelCanonical.exists_frame_over_reference
