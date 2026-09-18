import KltDP.Geometry.CanonicalDivisorTargetOpenNamedSquare
import KltDP.Geometry.AffineCanonicalDifferenceFromNamedSquare
import KltDP.Geometry.NormalModelLocalFrameConstructor

/-!
# Positive original canonical difference on genuine affine parameter charts

The source frame is the existing Cartier-frame constructor. Its proved
normalization fixes the original rational value of the actual differential
image. Genuine target parameters and original affine Kähler bases force the
same section coefficient into the source maximal ideal. Its nonzeroness and
positive DVR order follow from that fixed rational value, without a supplied
coefficient identity, determinant comparison, or discrepancy formula.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.NormalizedAffineCanonicalDifference

open NormalModelCanonical CartierRationalCoordinate NormalizedDifferentialCoefficientOrder
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkGroundAlgebra)

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

local instance referenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance chartGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The actual integer Cartier difference is positive on these original
parameter charts. Every scalar/coefficient comparison is derived internally. -/
theorem order_difference_pos
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (A B : Type u) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra k A] [Algebra k B]
    (i : Spec (CommRingCat.of A) ⟶ U.toScheme) [IsOpenImmersion i]
    (sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (hi : i ≫ (U.ι ≫ X.structureMorphism) = sA)
    (hA : sA = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (jB : Spec (CommRingCat.of B) ⟶ V) [IsOpenImmersion jB]
    (p : PrimeSpectrum B) (hp : jB.base p = x)
    [IsSmoothOfRelativeDimension 2 (jB ≫ (v ≫ X.structureMorphism))]
    (hB : jB ≫ (v ≫ X.structureMorphism) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (DS : CartierDivisor (Spec (CommRingCat.of B)))
    (eS : cartierDivisorModule (Spec (CommRingCat.of B)) DS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (jB ≫ (v ≫ X.structureMorphism)) 2)
    (hF : IsNormalized X U KU eKU v x
      (LocalFrame.ofCanonicalDivisor (v ≫ X.structureMorphism) jB p x hp DS eS))
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) [GenericPointPreserving q]
    (hq : (q ≫ i) ≫ U.ι = jB ≫ v)
    (cS : CartierEquationChart (Spec (CommRingCat.of B)) DS)
    (cT : CartierEquationChart (Spec (CommRingCat.of A))
      (DominantCartierPullback.pullbackHom i KU))
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet) (hpS : p ∈ cS.openSet)
    (bA : Basis (Fin 2) A (KaehlerDifferential k A))
    (bB : Basis (Fin 2) B (KaehlerDifferential k B))
    (vA : Fin 2 → A)
    (hvA : ∀ t, StructureSheaf.toStalk A (q.base p) (vA t) ∈
      IsLocalRing.maximalIdeal (originalStalkRing A (q.base p))) :
    letI : IsDiscreteValuationRing ((Spec (CommRingCat.of B)).presheaf.stalk p) :=
      OpenImmersionRational.stalk_isDiscreteValuationRing_of_isOpenImmersion jB p x hp
    letI := stalkGroundAlgebra (k := k) (A := A) (p := q.base p)
    ∀ bₚ : Basis (Fin 2) (originalStalkRing A (q.base p))
        (KaehlerDifferential k (originalStalkRing A (q.base p))),
      (∀ t, bₚ t = KaehlerDifferential.D k (originalStalkRing A (q.base p))
        (StructureSheaf.toStalk A (q.base p) (vA t))) →
      0 < cartierOrderAt (Spec (CommRingCat.of B)) DS p -
        cartierOrderAt (Spec (CommRingCat.of B))
          (DominantCartierPullback.pullbackHom q
            (DominantCartierPullback.pullbackHom i KU)) p := by
  letI : IsDiscreteValuationRing ((Spec (CommRingCat.of B)).presheaf.stalk p) :=
    OpenImmersionRational.stalk_isDiscreteValuationRing_of_isOpenImmersion jB p x hp
  let sB := jB ≫ (v ≫ X.structureMorphism)
  have hqbase : q ≫ sA = sB := by
    rw [← hi]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ X.structureMorphism) hq
  exact AffineCanonicalDifferenceFromSquare.order_difference_pos_of_named_square
    k A B sA sB q hqbase hA hB p bA bB
    (DominantCartierPullback.pullbackHom i KU) DS eS
    (CanonicalDivisorTargetOpenSquare.normalized_square
      X U KU eKU i sA hi v x jB p hp DS eS hF q hq)
    cT cS hST hpS vA hvA

end KltDP.Geometry.NormalizedAffineCanonicalDifference

#check @KltDP.Geometry.NormalizedAffineCanonicalDifference.order_difference_pos
#print axioms KltDP.Geometry.NormalizedAffineCanonicalDifference.order_difference_pos
