import KltDP.RingTheory.NormalHeightOneUnits
import KltDP.Geometry.StalkUnitNeighborhood

/-!
# Original stalk units from vanishing curve orders on a normal surface

The accepted curve-to-stalk-prime correspondence identifies the original
height-one valuations. Normal Hartogs then recovers an actual stalk unit;
pinned germ representability realizes it on a smaller prescribed open.
No factoriality of any stalk or affine neighborhood is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Zero original curve orders through a point give an actual unit of
the original normal stalk. -/
theorem exists_stalk_unit_of_curve_orders_eq_zero (x : X.toScheme)
    (f : X.toScheme.functionFieldˣ)
    (hzero : ∀ C : X.PrimeCurve, x ∈ C → C.order f = 0) :
    ∃ a : (X.stalk x)ˣ,
      Units.map (algebraMap (X.stalk x) X.toScheme.functionField) a = f := by
  let U : X.toScheme.Opens := (X.toScheme.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.toScheme.affineCover.map x)
  let xu : U := ⟨x, X.toScheme.affineCover.covers x⟩
  apply RingTheory.NormalHartogs.exists_unit_of_affinePrincipalOrder_eq_zero
    (X.stalk x) X.toScheme.functionField f
  intro q
  obtain ⟨C, hC⟩ := X.stalkHeightOnePrime_surjective hU xu q
  rw [← hC, ← C.1.order_eq_stalkHeightOnePrime_order hU xu C.2 f]
  exact hzero C.1 C.2

/-- The actual unit can be represented inside the original equation
neighborhood with the prescribed original rational image. -/
theorem exists_regular_unit_near_of_curve_orders_eq_zero (x : X.toScheme)
    (U : X.toScheme.Opens) (hxU : x ∈ U) (f : X.toScheme.functionFieldˣ)
    (hzero : ∀ C : X.PrimeCurve, x ∈ C → C.order f = 0) :
    ∃ (V : X.toScheme.Opens) (_ : V ≤ U) (hxV : x ∈ V) (b : Γ(X.toScheme, V)ˣ),
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      Units.map (X.toScheme.germToFunctionField V).hom.toMonoidHom b = f := by
  obtain ⟨a, ha⟩ := X.exists_stalk_unit_of_curve_orders_eq_zero x f hzero
  obtain ⟨V, hVU, hxV, b, hb⟩ :=
    exists_section_unit_of_stalk_unit_within X.toScheme x a U hxU
  refine ⟨V, hVU, hxV, b, ?_⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  calc
    Units.map (X.toScheme.germToFunctionField V).hom.toMonoidHom b =
        Units.map (algebraMap (X.stalk x) X.toScheme.functionField)
          (Units.map (X.toScheme.presheaf.germ V x hxV).hom.toMonoidHom b) :=
      (section_unit_toFunctionField_eq_stalk X.toScheme x V hxV b).symm
    _ = f := by rw [hb]; exact ha

end KltDP.Geometry.NormalProjectiveSurface
