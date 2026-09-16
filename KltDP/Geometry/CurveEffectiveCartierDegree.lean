import KltDP.Geometry.CurveEffectiveCartierHOneVanishing
import KltDP.Geometry.ClosedImmersionStructureEpi
import KltDP.Geometry.PrimeCurveIntersectionEffectiveDegree
import KltDP.Geometry.PrimeCurveIntersectionFinite
import KltDP.Geometry.PrimeCurvePullbackFrameCore
import KltDP.Geometry.CartierTensorProduct
import KltDP.Geometry.CartierPrincipalPicard
import KltDP.AdmissionProbe.CurveTensorDegreeConsumers

/-!
# Stacks 0AYY on a prime curve, and the F03 intersection-degree bridge

With the two inputs now proved — `O_C → i_*O_E` is an epimorphism for the closed immersion of the
zero scheme `E` of an effective Cartier divisor (`ClosedImmersionStructureEpi`), and
`H¹(C, i_*O_E) = 0` when `E` is finite with closed points (`CurveEffectiveCartierHOneVanishing`) —
the ideal short exact sequence gives `deg O_C(−E) = −deg E`; the admitted 0AYX additivity
(`lineDegree_eq_add_of_tensorIso`) together with `O_C(E) ⊗ O_C(−E) ≅ O_C(0) ≅ O_C` turns this into

    deg O_C(E) = effectiveCartierDegree E = dim_k Γ(E, O_E)          (Stacks 0AYY).

For `E = D|_C` the zero scheme is the intersection scheme `C ∩ D` (finite with closed points by
the accepted 3b(i) finiteness), so `deg O_C(D|_C) = intersectionDegree C D`; and through the
unconditional Picard-class bridge `[O_C(D|_C)] = [i^*O_X(D)]` also `deg (i^*O_X(D)) = intersectionDegree C D`
(`f03_intersection_degree_bridge`). Additivity of `intersectionDegree` in `D` is not derived here:
the restriction `restrictCartier` has no additivity lemma yet (see `F03_DEGREE_0AYY_PLAN.md`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open scoped CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- The module of the zero divisor is trivial (through the principal divisor of `1`). -/
def cartierDivisorModule_zero_iso_unit :
    cartierDivisorModule C.toScheme 0 ≅ _root_.SheafOfModules.unit C.toScheme.ringCatSheaf := by
  have h : principalCartierDivisorHom C.toScheme
      (Additive.ofMul (1 : C.toScheme.functionFieldˣ)) = 0 := by simp
  exact h ▸ principalCartierModuleIsoUnit C.toScheme 1

/-- `deg O_C(0) = 0`. -/
theorem lineDegree_cartier_zero :
    C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme 0) = 0 :=
  C.lineDegree_eq_zero_of_iso_unit _ (cartierDivisorModule_zero_iso_unit C)

section Divisor

variable (E : CartierDivisor C.toScheme)

/-- `deg O_C(E) + deg O_C(−E) = 0` (admitted 0AYX additivity through `O(E) ⊗ O(−E) ≅ O(E + −E)`). -/
theorem lineDegree_cartier_add_neg :
    C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme E) +
      C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (-E)) = 0 := by
  have h := KltDP.AdmissionProbe.CurveTensorDegreeConsumers.lineDegree_eq_add_of_tensorIso C
    (cartierDivisorInvertibleSheaf C.toScheme E) (cartierDivisorInvertibleSheaf C.toScheme (-E))
    (cartierDivisorInvertibleSheaf C.toScheme (E + -E)) (cartierTensorIso C.toScheme E (-E)).symm
  have h0 : C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (E + -E)) = 0 := by
    rw [add_neg_cancel]
    exact C.lineDegree_cartier_zero
  linarith

variable (hE : HasRegularCartierEquations C.toScheme E)

/-- **Stacks 0AYY on the prime curve**: for an effective Cartier divisor `E` whose zero scheme is
finite with closed points, `deg O_C(E) = effectiveCartierDegree E = dim_k Γ(E, O_E)`. -/
theorem lineDegree_cartier_eq_effectiveCartierDegree
    [Finite (effectiveCartierScheme C.toScheme E hE)]
    (hT1 : ∀ x : effectiveCartierScheme C.toScheme E hE, IsClosed ({x} : Set _)) :
    C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme E) =
      (effectiveCartierDegree C.toScheme E hE C.toSpec : ℤ) := by
  have hneg := C.lineDegree_neg_cartier_of_sequence E hE
    (effectiveCartier_structureToPushforwardUnit_epi C.toScheme E hE)
    (C.divisorStructurePushforward_hOne_subsingleton E hE hT1)
  have hsum := C.lineDegree_cartier_add_neg E
  linarith

end Divisor

section Intersection

variable (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- `deg O_C(D|_C) = intersectionDegree C D`. -/
theorem lineDegree_restrictCartier_eq_intersectionDegree :
    C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)) =
      (C.intersectionDegree D hD hC : ℤ) := by
  haveI : Finite (effectiveCartierScheme C.toScheme (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC)) :=
    C.intersectionScheme_finite' D hD hC
  exact C.lineDegree_cartier_eq_effectiveCartierDegree (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC)
    (C.intersectionScheme_isClosed_singleton' D hD hC)

/-- `deg (i^*O_X(D)) = intersectionDegree C D`, through the Picard-class bridge. -/
theorem lineDegree_pullback_eq_intersectionDegree :
    C.lineDegree (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)) =
      (C.intersectionDegree D hD hC : ℤ) :=
  (C.lineDegree_eq_of_toPic_eq (C.picardClass_restrict_eq_pullback D hD hC).symm).trans
    (C.lineDegree_restrictCartier_eq_intersectionDegree D hD hC)

end Intersection

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

namespace KltDP.Geometry

/-- **The F03 intersection-degree bridge.** For a prime curve `C` on a normal projective surface
`X` over a field `k`, a Cartier divisor `D` on `X` with regular local equations (`hD`) not
containing `C` in its support (`hC`): the F03 intersection number `intersectionDegree C D`
(the length `dim_k Γ(C ∩ D, O)`) is the degree of the restricted line bundle `O_C(D|_C)` and of
the pulled-back line bundle `i^*O_X(D)` on `C`. All universes coincide (`u`). -/
theorem f03_intersection_degree_bridge {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (C : X.PrimeCurve) (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD) :
    C.lineDegree (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)) =
        (C.intersectionDegree D hD hC : ℤ) ∧
      C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)) =
        (C.intersectionDegree D hD hC : ℤ) :=
  ⟨C.lineDegree_pullback_eq_intersectionDegree D hD hC,
    C.lineDegree_restrictCartier_eq_intersectionDegree D hD hC⟩

/-- Universe check: the bridge instantiates at a single universe `u` with no further constraints. -/
example {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
    (hC : C.NotInSupport D hD) :
    C.lineDegree (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)) =
      (C.intersectionDegree D hD hC : ℤ) :=
  (f03_intersection_degree_bridge C D hD hC).1

end KltDP.Geometry
