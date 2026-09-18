import KltDP.Geometry.CanonicalLocalReferenceDiscrepancy

/-!
# The original rational discrepancy on an actual reference chart

The signed pullback composition identity identifies the actual chart divisor
with the reference pullback in the original local numerator theorem. This
retains the same rational Weil divisor and original source prime.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalLocalReferenceDiscrepancy

open NormalModelCanonical NormalProjectiveSurface DominantCartierPullback OpenImmersionRational

local instance chartDiscrepancyReferenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (W : X.toScheme.Opens) [Nonempty W.toScheme] :
    IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι

local instance chartDiscrepancyOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

local instance chartDiscrepancyPrimeDVR {k : Type u} [Field k]
    (S : NormalProjectiveSurface k) (C : S.PrimeCurve) :
    IsDiscreteValuationRing (S.toScheme.presheaf.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- The original rational discrepancy equals the signed Cartier difference
computed on the actual affine chart of the same canonical reference. -/
theorem coefficient_eq_chart_difference
    {k : Type u} [Field k] [IsAlgClosed k] (S X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (C : S.PrimeCurve) (F : LocalFrame (π ≫ X.structureMorphism) C.genericPoint)
    (W : X.toScheme.Opens) [Nonempty W.toScheme]
    {T : Scheme.{u}} [IsIntegral T] (i : T ⟶ W.toScheme) [IsOpenImmersion i]
    (q : F.neighborhood ⟶ T) [GenericPointPreserving q]
    (hq : (q ≫ i) ≫ W.ι = F.toModel ≫ π)
    (KW : CartierDivisor W.toScheme) (KS : CartierDivisor S.toScheme)
    (hF : F.order = S.cartierToWeilHom KS C)
    (KX : X.WeilDivisor) (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.cartierToWeilHom A = n • KX)
    (hmultiple : n • KW = cartierRestrictionHom W.ι A) :
    (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C =
      ((F.order - cartierOrderAt F.neighborhood
        (pullbackHom q (pullbackHom i KW)) F.point : ℤ) : ℚ) := by
  have h := coefficient_eq_local_difference S X π C F W (q ≫ i) hq KW KS hF
    KX hK n hn A hA hmultiple
  have hdiv : pullbackHom (q ≫ i) KW = pullbackHom q (pullbackHom i KW) :=
    congrArg (fun f => f KW) (pullbackHom_comp q i)
  simpa only [hdiv] using h

end KltDP.Geometry.CanonicalLocalReferenceDiscrepancy

#check @KltDP.Geometry.CanonicalLocalReferenceDiscrepancy.coefficient_eq_chart_difference
#print axioms KltDP.Geometry.CanonicalLocalReferenceDiscrepancy.coefficient_eq_chart_difference
