import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Affine charts into the actual global pullback

An already proved composite pullback square induces a chart of the original
global pullback. The induced map is a pullback of the actual base chart map,
so an open base chart yields an open chart of the actual pullback.
This is a categorical pasting adapter, not an assumed comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.PullbackChartLift

variable {A B S T Z : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ S}
  {g : B ⟶ Z} {v : S ⟶ T} {f : T ⟶ Z}
  (H : IsPullback a b g (v ≫ f))

/-- The universal map into the actual original global pullback. -/
def lift : A ⟶ pullback g f :=
  pullback.lift a (b ≫ v) (by rw [H.w, Category.assoc])

@[simp, reassoc]
theorem lift_fst : lift H ≫ pullback.fst g f = a := pullback.lift_fst _ _ _

@[simp, reassoc]
theorem lift_snd : lift H ≫ pullback.snd g f = b ≫ v := pullback.lift_snd _ _ _

/-- Cancellation of the right pullback square proves the chart square. -/
theorem isPullback : IsPullback (lift H) b (pullback.snd g f) v := by
  have h : IsPullback (lift H ≫ pullback.fst g f) b g (v ≫ f) := by
    rw [lift_fst]
    exact H
  exact h.of_right (lift_snd H) (IsPullback.of_hasPullback g f)

/-- Actual open base charts give actual open charts of the original pullback. -/
theorem isOpenImmersion [IsOpenImmersion v] : IsOpenImmersion (lift H) := by
  rw [← (isPullback H).isoPullback_hom_fst]
  infer_instance

#print axioms isPullback
#print axioms isOpenImmersion

end KltDP.Geometry.PullbackChartLift
