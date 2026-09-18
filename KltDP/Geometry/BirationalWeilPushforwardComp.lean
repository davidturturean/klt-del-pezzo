import KltDP.Geometry.BirationalWeilPushforward
import KltDP.Geometry.BirationalComposition

/-!
# Composition of the original proper birational Weil pushforwards

The unique prime above an original target prime is the prime obtained by
lifting through both original morphisms. Evaluation of the actual finite
Weil sums then gives composition, including arbitrary signed coefficients.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S T X : NormalProjectiveSurface k}
  (b : S.toScheme ⟶ T.toScheme) [IsProper b] (hb : IsBirationalScheme b)
  (g : T.toScheme ⟶ X.toScheme) [IsProper g] (hg : IsBirationalScheme g)

include hb hg in
theorem comp_isBirational : IsBirationalScheme (b ≫ g) := by
  letI : GenericPointPreserving b := ⟨hb.map_genericPoint⟩
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  exact (BirationalComposition.isBirationalScheme_comp_iff b g).mpr ⟨hb, hg⟩

theorem abovePrimeCurve_comp (C : X.PrimeCurve) :
    abovePrimeCurve (b ≫ g) (comp_isBirational b hb g hg) C =
      abovePrimeCurve b hb (abovePrimeCurve g hg C) := by
  symm
  apply abovePrimeCurve_unique (b ≫ g) (comp_isBirational b hb g hg)
  rw [Scheme.comp_base_apply, abovePrimeCurve_map_genericPoint,
    abovePrimeCurve_map_genericPoint]

theorem pushforward_comp (D : S.WeilDivisor) :
    pushforward (b ≫ g) (comp_isBirational b hb g hg) D =
      pushforward g hg (pushforward b hb D) := by
  ext C
  exact congrArg D (abovePrimeCurve_comp b hb g hg C)

theorem pushforward_comp_hom :
    pushforward (b ≫ g) (comp_isBirational b hb g hg) =
      (pushforward g hg).comp (pushforward b hb) := by
  apply AddMonoidHom.ext
  intro D
  exact pushforward_comp b hb g hg D

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.pushforward_comp
#print axioms KltDP.Geometry.BirationalWeilPushforward.pushforward_comp
