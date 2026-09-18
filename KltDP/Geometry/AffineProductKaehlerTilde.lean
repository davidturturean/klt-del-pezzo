import KltDP.RingTheory.KaehlerTensorProductSplit
import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineModuleTildeFunctor

/-!
# The normalized absolute differential splitting on an affine product

The scheme is the original Spec of S tensor_R T, and its structure morphism
is Spec of the original R-algebra map. The actual differential sheaf is
identified with the tilde of the two original base-changed Kähler modules.
The forward map retains differentiation of s tensor 1 and 1 tensor t on
every open. Comparison of these summands with the actual Spec projection
pullbacks is a separate companion step; no global product or exterior
identity is assumed here.

Reuse: the existing actual affine differential/tilde isomorphism and
functorial tilde maps are composed directly with the compiled ring split.
No new sheafification or direct-sum framework is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineProductKaehler

open AffineKaehlerTildeDerivation

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The first original base-changed differential module. -/
abbrev leftModule : ModuleCat (S ⊗[R] T) :=
  ModuleCat.of (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] KaehlerDifferential R S)

/-- The second original base-changed differential module. -/
abbrev rightModule : ModuleCat (S ⊗[R] T) :=
  ModuleCat.of (S ⊗[R] T) ((S ⊗[R] T) ⊗[T] KaehlerDifferential R T)

/-- The actual binary direct-sum module, represented as a binary product. -/
abbrev splitModule : ModuleCat (S ⊗[R] T) :=
  ModuleCat.of (S ⊗[R] T) (leftModule R S T × rightModule R S T)

/-- Sheafification of the original absolute differential splitting. -/
def tildeIso :
    (differentialModule R (S ⊗[R] T)).tilde ≅ (splitModule R S T).tilde :=
  AffineModuleTilde.linearEquivIso
    (M := differentialModule R (S ⊗[R] T)) (N := splitModule R S T)
    (KltDP.KaehlerTensorProductSplit.tensorProductEquiv R S T)

/-- The actual differential sheaf on the original affine tensor-product
scheme, with the original structure morphism to Spec R. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T)))) ≅
      (splitModule R S T).tilde :=
  AffineKaehlerTildeLocalization.iso R (S ⊗[R] T) ≪≫ tildeIso R S T

/-- On every original open, a canonical function section differentiates
to the canonical section of its original ring differential splitting. -/
theorem iso_d_toOpen (U : Opens (PrimeSpectrum (S ⊗[R] T))) (b : S ⊗[R] T) :
    (iso R S T).hom.val.app (op U)
        ((SchemeKaehlerSheaf.baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))))).d
            (StructureSheaf.toOpen (S ⊗[R] T) U b)) =
      ModuleCat.Tilde.toOpen (splitModule R S T) U
        (KltDP.KaehlerTensorProductSplit.tensorProductEquiv R S T
          (KaehlerDifferential.D R (S ⊗[R] T) b)) := by
  change (tildeIso R S T).hom.val.app (op U)
    ((AffineKaehlerTildeLocalization.iso R (S ⊗[R] T)).hom.val.app (op U) _) = _
  rw [AffineKaehlerTildeLocalization.iso_d, sectionD_toOpen]
  exact AffineModuleTilde.map_app_toOpen
    (KltDP.KaehlerTensorProductSplit.tensorProductEquiv R S T).toModuleIso.hom U _

/-- The first original tensor inclusion has the required normalization. -/
theorem iso_d_tmul_one (U : Opens (PrimeSpectrum (S ⊗[R] T))) (s : S) :
    (iso R S T).hom.val.app (op U)
        ((SchemeKaehlerSheaf.baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))))).d
            (StructureSheaf.toOpen (S ⊗[R] T) U (s ⊗ₜ 1))) =
      ModuleCat.Tilde.toOpen (splitModule R S T) U
        (1 ⊗ₜ KaehlerDifferential.D R S s, 0) := by
  simpa only [KltDP.KaehlerTensorProductSplit.tensorProductEquiv_D_tmul_one] using
    iso_d_toOpen R S T U (s ⊗ₜ 1)

/-- The second original tensor inclusion has the required normalization. -/
theorem iso_d_one_tmul (U : Opens (PrimeSpectrum (S ⊗[R] T))) (t : T) :
    (iso R S T).hom.val.app (op U)
        ((SchemeKaehlerSheaf.baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))))).d
            (StructureSheaf.toOpen (S ⊗[R] T) U (1 ⊗ₜ t))) =
      ModuleCat.Tilde.toOpen (splitModule R S T) U
        (0, 1 ⊗ₜ KaehlerDifferential.D R T t) := by
  simpa only [KltDP.KaehlerTensorProductSplit.tensorProductEquiv_D_one_tmul] using
    iso_d_toOpen R S T U (1 ⊗ₜ t)

end KltDP.Geometry.AffineProductKaehler
