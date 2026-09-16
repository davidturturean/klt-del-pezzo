import KltDP.Geometry.PrimeCurveIntersectionDegreeSum

/-!
# `intersectionDegree C D = effectiveCartierDegree (D|_C)`

The F03 intersection number of a prime curve `C ⊄ Supp D` with an effective Cartier
divisor `D` is, by construction, the accepted effective Cartier degree of the restricted
divisor `D|_C` on the curve scheme, for the structure morphism `C.toSpec`: the restricted
divisor has regular local equations on `C` (`restrictCartier_hasRegularEquations`, no
regularity hypothesis on `C`), its zero scheme is the intersection subscheme `C ∩ D` with the
same closed immersion, and the degree is `dim_k H⁰(C ∩ D, O)`, i.e. `dim_k Γ(D|_C, O)` by the
accepted `H⁰` comparison. This module records these identities explicitly, together with the
general statement `effectiveCartierDegree = dim_k Γ(D, O_D)`: the exact right-hand side of
Stacks 0AYY. A future admission of 0AYY on the curve therefore yields
`deg O_C(D|_C) = intersectionDegree C D` with no further geometry.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (Y : Scheme.{u}) [IsIntegral Y] (E : CartierDivisor Y)
  (hE : HasRegularCartierEquations Y E) (f : Y ⟶ Spec (CommRingCat.of k))

/-- `effectiveCartierDegree Y E hE f = dim_k Γ(D, O_D)`, the right-hand side of Stacks 0AYY, for
the `k`-action through the structure morphism `D → Y → Spec k`. -/
theorem effectiveCartierDegree_eq_finrank_sections :
    letI := Module.compHom Γ(effectiveCartierScheme Y E hE, ⊤)
      (baseFieldToGlobalSections (effectiveCartierToSpec Y E hE f))
    effectiveCartierDegree Y E hE f = Module.finrank k Γ(effectiveCartierScheme Y E hE, ⊤) :=
  cohomologyDimension_zero_unit_eq_finrank (effectiveCartierToSpec Y E hE f)

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- (1) The restricted divisor `D|_C` has regular local equations on the curve: the restricted
charts `i⁻¹U_c` with equations `i.app d_c` cover `C`. No regularity hypothesis on `C` is used. -/
theorem restrictCartier_hasRegularCartierEquations :
    HasRegularCartierEquations C.toScheme (C.restrictCartier D hD hC) :=
  C.restrictCartier_hasRegularEquations D hD hC

/-- (2) The zero scheme of `D|_C` is the intersection subscheme `C ∩ D`. -/
def intersectionSchemeIsoEffectiveCartierScheme :
    C.intersectionScheme D hD hC ≅
      effectiveCartierScheme C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC) :=
  Iso.refl _

/-- (2') The closed immersion `C ∩ D → C` is the zero-scheme inclusion of `D|_C`. -/
theorem intersectionInclusion_eq_effectiveCartierInclusion :
    C.intersectionInclusion D hD hC =
      effectiveCartierInclusion C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC) := rfl

/-- (2'') The structure morphism of `C ∩ D` over `k` is that of the zero scheme of `D|_C`. -/
theorem intersectionToSpec_eq_effectiveCartierToSpec :
    C.intersectionToSpec D hD hC =
      effectiveCartierToSpec C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec := rfl

/-- (3) **`intersectionDegree C D = effectiveCartierDegree (D|_C)`** on the curve, for the
structure morphism `C.toSpec`: the exact right-hand side of Stacks 0AYY applied to `D|_C`. -/
theorem intersectionDegree_eq_effectiveCartierDegree :
    C.intersectionDegree D hD hC =
      effectiveCartierDegree C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec := rfl

/-- The identity holds for any witness of the regular local equations of `D|_C`. -/
theorem intersectionDegree_eq_effectiveCartierDegree_of_witness
    (hreg : HasRegularCartierEquations C.toScheme (C.restrictCartier D hD hC)) :
    C.intersectionDegree D hD hC =
      effectiveCartierDegree C.toScheme (C.restrictCartier D hD hC) hreg C.toSpec := rfl

/-- `intersectionDegree = dim_k Γ(D|_C, O)` in the form of the 0AYY right-hand side. -/
theorem intersectionDegree_eq_finrank_effectiveCartierScheme :
    letI := Module.compHom
      Γ(effectiveCartierScheme C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC), ⊤)
      (baseFieldToGlobalSections (effectiveCartierToSpec C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec))
    C.intersectionDegree D hD hC =
      Module.finrank k Γ(effectiveCartierScheme C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC), ⊤) :=
  effectiveCartierDegree_eq_finrank_sections C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
