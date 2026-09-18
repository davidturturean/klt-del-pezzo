import KltDP.Geometry.NormalModelLocalFrameRestrictionNormalized

/-!
# Factoring an original normalized frame through a target chart

Pull back the actual chart range and restrict the existing source frame.
The original open-immersion lift gives the chart map and its point equation.
Normalization and the source order are preserved by the already proved
original frame restriction, without assuming a neighborhood factorization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical

attribute [local instance] integralSchemeStalk_isDomain

local instance chartReferenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- An actual target-chart point above the image supplies an actual whole
source neighborhood mapping into that chart, with its original frame order. -/
theorem exists_frame_over_reference_chart
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V A : Scheme.{u}} [IsIntegral V] [IsIntegral A]
    (v : V ⟶ X.toScheme) (x : V) [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (p : F.neighborhood ⟶ U.toScheme) (hp : p ≫ U.ι = F.toModel ≫ v)
    (i : A ⟶ U.toScheme) [IsOpenImmersion i]
    (a : A) (ha : i.base a = p.base F.point) :
    ∃ (G : LocalFrame (v ≫ X.structureMorphism) x) (q : G.neighborhood ⟶ A),
      (q ≫ i) ≫ U.ι = G.toModel ≫ v ∧
      IsNormalized X U KU eKU v x G ∧ G.order = F.order ∧ q.base G.point = a := by
  let Z := p ⁻¹ᵁ i.opensRange
  have hZ : F.point ∈ Z := by
    change p.base F.point ∈ Set.range i.base
    exact ⟨a, ha⟩
  let G := F.restrict Z hZ
  have hrange : Set.range (Z.ι ≫ p).base ⊆ Set.range i.base := by
    rintro y ⟨z, rfl⟩
    change p.base (Z.ι.base z) ∈ Set.range i.base
    exact z.property
  let q : G.neighborhood ⟶ A := IsOpenImmersion.lift i (Z.ι ≫ p) hrange
  have hqi : q ≫ i = Z.ι ≫ p := IsOpenImmersion.lift_fac i (Z.ι ≫ p) hrange
  have htriangle : (q ≫ i) ≫ U.ι = G.toModel ≫ v := by
    rw [hqi, Category.assoc, hp]
    exact (Category.assoc Z.ι F.toModel v).symm
  have hpoint : q.base G.point = a := by
    apply i.isOpenEmbedding.injective
    calc
      i.base (q.base G.point) = (q ≫ i).base G.point :=
        (Scheme.comp_base_apply q i G.point).symm
      _ = (Z.ι ≫ p).base G.point := congrArg (fun f => f.base G.point) hqi
      _ = p.base F.point := rfl
      _ = i.base a := ha.symm
  exact ⟨G, q, htriangle, LocalFrame.restrict_isNormalized X U KU eKU v x F Z hZ hF,
    F.restrict_order Z hZ, hpoint⟩

end KltDP.Geometry.NormalModelCanonical

#check @KltDP.Geometry.NormalModelCanonical.exists_frame_over_reference_chart
#print axioms KltDP.Geometry.NormalModelCanonical.exists_frame_over_reference_chart
