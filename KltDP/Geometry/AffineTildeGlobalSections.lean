import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Geometry.AffineKaehlerTildeDerivation

/-!
# Global sections of the tilde of the Kähler module

The last hop of BRIEF33 item 1 needs `Ω[B⁄k]` to be recovered from the global sections of its tilde,
as `B`-modules.  That statement is accepted already: `AffineModuleTilde.unitNatIso` is the natural
isomorphism `𝟭 ≅ functor R ⋙ globalSectionsFunctor R`, and both object spellings are `rfl`
(`(functor R).obj M = M.tilde`, `globalSectionsFunctor_obj M = sectionModule M ⊤`).  This module only
specialises it, so that the composition step has a named `≃ₗ` to work with rather than a natural
isomorphism between functors.

* **`tildeGlobalSectionsEquiv`**: `M ≃ₗ[R] sectionModule M.tilde ⊤` for any `R`-module `M`.
* **`kaehlerTildeGlobalSectionsEquiv`**: the same at `M := differentialModule k B`, i.e.
  `Ω[B⁄k] ≃ₗ[B] sectionModule ((differentialModule k B).tilde) ⊤`.

Note the scalars: `sectionModule` is the *base-ring* packaging of the sections
(`sectionModule_coe … := rfl`), which is what makes this a `B`-linear statement.  The sections of
`M.tilde.val.obj (op ⊤)` carry the *local section ring* `Γ(Spec B, ⊤)` instead — the same carrier,
a different bundling, and the distinction that has to be respected when composing.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.AffineModuleTilde KltDP.Geometry.AffineKaehlerTildeDerivation

universe u

namespace KltDP.Geometry.AffineTildeGlobalSections

/-- **A module is the global sections of its tilde**, as modules over the base ring. -/
def tildeGlobalSectionsEquiv (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    M ≃ₗ[R] sectionModule M.tilde ⊤ :=
  ((unitNatIso R).app M).toLinearEquiv

/-- The Kähler module is the global sections of its tilde. -/
def kaehlerTildeGlobalSectionsEquiv (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] :
    KaehlerDifferential k B ≃ₗ[B] sectionModule ((differentialModule k B).tilde) ⊤ :=
  tildeGlobalSectionsEquiv B (differentialModule k B)

end KltDP.Geometry.AffineTildeGlobalSections
