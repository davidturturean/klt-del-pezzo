import KltDP.Geometry.SchemeAbelianSheafPushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Full affine-morphism cohomology comparison: Stacks 089W

Lemma 30.2.4 at Stacks revision 540451b3e79a131df8eca4c4187448e49dcb262d.
All schemes, affine morphisms, quasicoherent coefficients, and degrees are
retained. The natural family is witnessed by the published canonical Leray
comparison. This existence statement does not identify a chosen native map
as canonical, nor assert exactness on all abelian sheaves.

The full source, native dictionary, independent review, and root decision
are in affine_morphism_cohomology_source_20260915. This isolated declaration
does not modify the production literature registry.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Literature.Stacks

attribute [local instance] Types.instFunLike Types.instConcreteCategory

axiom affine_morphism_cohomology_literal :
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x)

end KltDP.Literature.Stacks

#check @KltDP.Literature.Stacks.affine_morphism_cohomology_literal
