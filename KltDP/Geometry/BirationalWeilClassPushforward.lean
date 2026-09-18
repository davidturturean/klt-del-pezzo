import KltDP.Geometry.BirationalPrincipalPushforwardSource
import KltDP.Geometry.WeilClassGroup

/-!
# The original birational pushforward on Weil divisor classes

Principal preservation puts the original principal subgroup in the
kernel of the original divisor pushforward followed by the target class
map. The existing quotient universal property then constructs the class
pushforward, with its literal formula on every original representative.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalWeilClassPushforward

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The actual principal-preservation theorem supplies the kernel
inclusion needed by the existing quotient universal property. -/
theorem principalDivisors_le_ker :
    S.principalDivisors ≤
      (X.weilClassMap.comp (BirationalWeilPushforward.pushforward π hbir)).ker := by
  intro D hD
  obtain ⟨f, rfl⟩ := (S.mem_principalDivisors_iff D).mp hD
  exact (X.weilClassMap_eq_zero_iff _).mpr
    (BirationalWeilPushforward.pushforward_principalDivisor_exists π hbir f)

/-- Pushforward on the original Weil class groups, induced by the
original finite-sum pushforward and its proved principal preservation. -/
def pushforward : S.WeilClassGroup →+ X.WeilClassGroup :=
  QuotientAddGroup.lift S.principalDivisors
    (X.weilClassMap.comp (BirationalWeilPushforward.pushforward π hbir))
    (principalDivisors_le_ker π hbir)

/-- On every actual divisor representative, the induced map is the
class of its original finite-sum pushforward. -/
@[simp]
theorem pushforward_weilClassMap (D : S.WeilDivisor) :
    pushforward π hbir (S.weilClassMap D) =
      X.weilClassMap (BirationalWeilPushforward.pushforward π hbir D) := rfl

/-- The original quotient square commutes as a homomorphism equality. -/
theorem pushforward_comp_weilClassMap :
    (pushforward π hbir).comp S.weilClassMap =
      X.weilClassMap.comp (BirationalWeilPushforward.pushforward π hbir) := rfl

/-- The induced map is uniquely determined by its values on original
finite Weil-divisor representatives. -/
theorem pushforward_unique (φ : S.WeilClassGroup →+ X.WeilClassGroup)
    (hφ : φ.comp S.weilClassMap =
      X.weilClassMap.comp (BirationalWeilPushforward.pushforward π hbir)) :
    φ = pushforward π hbir := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨D, rfl⟩ := S.weilClassMap_surjective c
  exact DFunLike.congr_fun hφ D

/-- The original pushforward preserves the existing linear-equivalence
relation, with its original nonzero rational-function witnesses. -/
theorem pushforward_linearlyEquivalent {D E : S.WeilDivisor}
    (h : S.LinearlyEquivalent D E) :
    X.LinearlyEquivalent (BirationalWeilPushforward.pushforward π hbir D)
      (BirationalWeilPushforward.pushforward π hbir E) := by
  apply (X.linearlyEquivalent_iff_weilClassMap_eq _ _).mpr
  exact congrArg (pushforward π hbir)
    ((S.linearlyEquivalent_iff_weilClassMap_eq D E).mp h)

/-- The class of each actually contracted prime, with any original
integer coefficient, has zero pushforward. -/
theorem pushforward_weilClassMap_single_contracted (B : S.PrimeCurve) (z : ℤ)
    (p : Spec (CommRingCat.of k) ⟶ X.toScheme)
    (hB : B.inclusion ≫ π = B.toSpec ≫ p) (hp : p ≫ X.structureMorphism = 𝟙 _) :
    pushforward π hbir (S.weilClassMap (Finsupp.single B z)) = 0 := by
  rw [pushforward_weilClassMap,
    BirationalWeilPushforward.pushforward_single_contracted π hbir B z p hB hp, map_zero]

/-- The unique original prime above a target prime pushes to that
target prime's class with its unchanged integer coefficient. -/
theorem pushforward_weilClassMap_single_above (C : X.PrimeCurve) (z : ℤ) :
    pushforward π hbir
        (S.weilClassMap (Finsupp.single (BirationalPrimeCorrespondence.abovePrimeCurve π hbir C) z)) =
      X.weilClassMap (Finsupp.single C z) := by
  rw [pushforward_weilClassMap, BirationalWeilPushforward.pushforward_single_above]

end KltDP.Geometry.BirationalWeilClassPushforward
