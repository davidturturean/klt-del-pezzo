import KltDP.Geometry.AffineDifferentialSectionsGamma
import KltDP.Geometry.AffineTildeGlobalSections

/-!
# The sections of `Ω_{X/k}` on an affine open, through to the Kähler module

This composes the pieces of BRIEF33 item 1 that are already compiled:

* `AffineDifferentialSections.affineDifferentialSectionsEquiv` — the sections of `Ω_{X/k}` restricted
  to an affine open `W`, compared with the sections of the tilde of `Ω[Γ(X, W)⁄k]`, over
  `Γ(W.toScheme, ⊤)`;
* `AffineTildeGlobalSections.kaehlerTildeGlobalSectionsEquiv` — `Ω[B⁄k]` as the global sections of its
  tilde, over `B`;
* `AffineDifferentialSectionsGamma.sectionsRingIso` — the ring bridge `Γ(W.toScheme, ⊤) ≅ Γ(X, W)`.

**`restrictionTildeSections`** is the hop between the middle two: the sections of the tilde pulled
back along the affine identification `hW.isoSpec.hom`, read at the image of `⊤`.  It is stated at
`.val.presheaf.obj`, the level at which the accepted `SchemeModuleRestriction.restrictionSectionsIso`
lives, and is proved by citing it — not by `rfl`, which is what failed when the two sides were
`ModuleCat` objects over different rings.

The image opens are kept **unrewritten** (`j ''ᵁ ⊤`, `W.ι ''ᵁ ⊤`) rather than transported across
`Scheme.Opens.ι_image_top` / `opensRange_of_isIso`: those equalities move a ring and a module
together, which is the heterogeneous transport the lane rules warn against.  A consumer holding a
concrete affine `W` rewrites them once, at the point of use.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.AffineKaehlerTildeDerivation KltDP.Geometry.AffineTildeGlobalSections
open KltDP.Geometry.AffineDifferentialSections KltDP.Geometry.AffineDifferentialSectionsGamma

universe u

namespace KltDP.Geometry.AffineDifferentialGamma

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The sections of the tilde, pulled back along the affine identification and read at the image of
`⊤`: the accepted restriction comparison, at the presheaf level where it lives. -/
def restrictionTildeSections {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    ((restriction hW.isoSpec.hom).obj
        ((differentialModule k Γ(X, W)).tilde)).val.presheaf.obj (op (⊤ : W.toScheme.Opens)) ≅
      ((differentialModule k Γ(X, W)).tilde).val.presheaf.obj
        (op (hW.isoSpec.hom ''ᵁ (⊤ : W.toScheme.Opens))) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  exact restrictionSectionsIso hW.isoSpec.hom ((differentialModule k Γ(X, W)).tilde) ⊤

/-- The sections of `Ω_{X/k}` on the image of `⊤`, which is the affine open itself once rewritten. -/
def restrictedDifferentialSections {W : X.Opens} :
    ((restriction W.ι).obj (baseRingSheaf f)).val.presheaf.obj (op (⊤ : W.toScheme.Opens)) ≅
      (baseRingSheaf f).val.presheaf.obj (op (W.ι ''ᵁ (⊤ : W.toScheme.Opens))) :=
  restrictionSectionsIso W.ι (baseRingSheaf f) ⊤

end KltDP.Geometry.AffineDifferentialGamma
