import KltDP.Geometry.SchemeIsoCohomology
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.PicardEulerValue

/-!
# Euler-characteristic transport along a scheme isomorphism over a field

For an isomorphism of schemes `e : X ≅ Y` the accepted `SchemeIsoCohomology` identifies the
cohomology of `e.hom_* M` (base action through `g : Y ⟶ Spec k`) with that of `M` (base action
through `e.hom ≫ g`), linearly over any base ring. This module draws the numerical consequences:

* `schemeIsoPushforwardPullbackIso`: `e.hom_* ≅ e.inv^*` as functors `X.Modules ⥤ Y.Modules`
  (pullback along `e.hom` is an equivalence with quasi-inverse pullback along `e.inv`, by the
  accepted composition/identity comparisons of pullback, so it is left adjoint to both `e.hom_*` and
  `e.inv^*`; uniqueness of right adjoints);
* `cohomologyDimension_pushforward_iso`, `eulerCharacteristic_pushforward_iso`:
  `h^n_g(e.hom_* M) = h^n_{e.hom ≫ g}(M)` and `χ_g(e.hom_* M) = χ_{e.hom ≫ g}(M)`;
* `eulerCharacteristic_eq_pullback_inv`: for `f : X ⟶ Spec k`, `g : Y ⟶ Spec k` with
  `e.hom ≫ g = f`, `χ_f(M) = χ_g(e.inv^* M)`; `eulerCharacteristic_unit_eq`: `χ_f(O_X) = χ_g(O_Y)`.

The base field is arbitrary; no finiteness or vanishing hypothesis is used (the Euler
characteristic is the accepted finite-support alternating sum of finranks).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- Pullback along `e.hom` followed by pullback along `e.inv` is the identity functor. -/
def schemeIsoPullbackHomInvIso :
    schemeModulePullback e.hom ⋙ schemeModulePullback e.inv ≅ 𝟭 Y.Modules :=
  schemeModulePullbackCompIso e.inv e.hom ≪≫
    eqToIso (congrArg schemeModulePullback e.inv_hom_id) ≪≫ schemeModulePullbackIdIso Y

/-- Pullback along `e.inv` followed by pullback along `e.hom` is the identity functor. -/
def schemeIsoPullbackInvHomIso :
    schemeModulePullback e.inv ⋙ schemeModulePullback e.hom ≅ 𝟭 X.Modules :=
  schemeModulePullbackCompIso e.hom e.inv ≪≫
    eqToIso (congrArg schemeModulePullback e.hom_inv_id) ≪≫ schemeModulePullbackIdIso X

/-- Pullback along the isomorphism `e.hom` is an equivalence, with quasi-inverse pullback along
`e.inv`. -/
def schemeIsoPullbackEquivalence : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (schemeModulePullback e.hom) (schemeModulePullback e.inv)
    (schemeIsoPullbackHomInvIso e).symm (schemeIsoPullbackInvHomIso e)

/-- Pushforward along `e.hom` is pullback along `e.inv`: both are right adjoint to pullback
along `e.hom`. -/
def schemeIsoPushforwardPullbackIso :
    schemeModulePushforward e.hom ≅ schemeModulePullback e.inv :=
  Adjunction.rightAdjointUniq (schemeModulePullbackPushforwardAdjunction e.hom)
    (schemeIsoPullbackEquivalence e).toAdjunction

namespace ModuleCohomology

variable {k : Type u} [Field k]

/-- Cohomological dimensions are preserved by pushforward along an isomorphism, the base action
on the source being through the composite structure morphism. -/
theorem cohomologyDimension_pushforward_iso (g : Y ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ) :
    cohomologyDimension g ((schemeModulePushforward e.hom).obj M) n =
      cohomologyDimension (e.hom ≫ g) M n := by
  letI := baseModule g ((schemeModulePushforward e.hom).obj M) n
  letI := baseModule (e.hom ≫ g) M n
  exact (pushforwardIsoHBaseRingLinearEquiv e g M n).finrank_eq

/-- The Euler characteristic is preserved by pushforward along an isomorphism. -/
theorem eulerCharacteristic_pushforward_iso (g : Y ⟶ Spec (CommRingCat.of k)) (M : X.Modules) :
    eulerCharacteristic g ((schemeModulePushforward e.hom).obj M) =
      eulerCharacteristic (e.hom ≫ g) M := by
  unfold eulerCharacteristic
  have h : (fun n : ℕ => (-1 : ℤ) ^ n *
        (cohomologyDimension g ((schemeModulePushforward e.hom).obj M) n : ℤ)) =
      fun n : ℕ => (-1 : ℤ) ^ n * (cohomologyDimension (e.hom ≫ g) M n : ℤ) := by
    funext n
    rw [cohomologyDimension_pushforward_iso e g M n]
  rw [h]

/-- The Euler characteristic is preserved by pullback along the inverse isomorphism. -/
theorem eulerCharacteristic_pullback_inv (g : Y ⟶ Spec (CommRingCat.of k)) (M : X.Modules) :
    eulerCharacteristic g ((schemeModulePullback e.inv).obj M) =
      eulerCharacteristic (e.hom ≫ g) M := by
  rw [← eulerCharacteristic_pushforward_iso e g M]
  exact eulerCharacteristic_eq_of_iso g ((schemeIsoPushforwardPullbackIso e).symm.app M)

/-- **Euler transport**: for an isomorphism `e` over `k` (`e.hom ≫ g = f`), the Euler
characteristic of `M` on `X` is that of `e.inv^* M` on `Y`. -/
theorem eulerCharacteristic_eq_pullback_inv (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (hfg : e.hom ≫ g = f) (M : X.Modules) :
    eulerCharacteristic f M = eulerCharacteristic g ((schemeModulePullback e.inv).obj M) := by
  rw [eulerCharacteristic_pullback_inv e g M, hfg]

/-- The structure sheaves of isomorphic schemes over `k` have the same Euler characteristic. -/
theorem eulerCharacteristic_unit_eq (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (hfg : e.hom ≫ g = f) :
    eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) =
      eulerCharacteristic g (_root_.SheafOfModules.unit Y.ringCatSheaf) := by
  rw [eulerCharacteristic_eq_pullback_inv e f g hfg]
  exact eulerCharacteristic_eq_of_iso g (schemeModulePullbackUnitIso e.inv)

end ModuleCohomology

end KltDP.Geometry
