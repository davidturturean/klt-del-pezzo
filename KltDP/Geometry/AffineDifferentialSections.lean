import KltDP.Geometry.AffineDifferentialSheafIso

/-!
# Sections of the differential sheaf on an affine open

`AffineDifferentialSheafIso.affineDifferentialIso` identifies `Ω_{X/k}` restricted to an affine open
`W` with the tilde of `Ω[Γ(X, W)⁄k]`.  Evaluating that isomorphism at the top open of the subscheme
gives the sections-level statement the overlap route consumes.

* **`affineDifferentialSectionsEquiv`**: a `Γ(W.toScheme, ⊤)`-linear equivalence between the sections
  of the restricted differential sheaf and the sections of the tilde, obtained with the accepted
  evaluation idiom `((SheafOfModules.evaluation _ (op ⊤)).mapIso e).toLinearEquiv`.
* **`restrictedSectionsIso`**: the left-hand side is the differential sheaf's sections over the image
  of `⊤`, by the accepted `SchemeModuleRestriction.restrictionSectionsIso` (which is `Iso.refl`).
  Note this holds at `.val.presheaf.obj` (the additive sections), **not** at `.val.obj`: the latter are
  `ModuleCat` objects over two different rings, `Γ(W.toScheme, ⊤)` and `Γ(X, W)`.

What is deliberately *not* done here: transporting the scalars along `Scheme.Opens.topIso :
Γ(W, ⊤) ≅ Γ(X, W)` to restate the equivalence over `Γ(X, W)`, and composing with
`AffineModuleTilde.isoTop` to reach `Ω[Γ(X, W)⁄k]` itself.  Both are named remainders rather than
risked here; they are pure bookkeeping over this equivalence.

Nothing is admitted here.

**Build state (2026-09-12): this module compiles and is accepted.**  It was accepted in
candidate1197 (commit `247e025`), is imported by the root module and by
`AffineDifferentialSectionsGamma`, and builds clean.  `restrictedSectionsIso` below is the
corrected, citation-based form, stated at `.val.presheaf.obj`; the `.val.obj` form that failed in
record `20260912T034206Z-677749` was a type mismatch — the two sides are `ModuleCat` objects over
the different rings `Γ(W.toScheme, ⊤)` and `Γ(X, W)` — and is deliberately not what is stated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeKaehlerOpenRestriction
open KltDP.Geometry.SchemeModuleRestriction KltDP.Geometry.AffineKaehlerTildeDerivation
open KltDP.Geometry.AffineDifferentialSheafIso

universe u

namespace KltDP.Geometry.AffineDifferentialSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The sections of `Ω_{X/k}` on an affine open, as sections of the tilde of its Kähler module.** -/
def affineDifferentialSectionsEquiv {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    ((restriction W.ι).obj (baseRingSheaf f)).val.obj (op (⊤ : W.toScheme.Opens)) ≃ₗ[Γ(W.toScheme, ⊤)]
      ((restriction hW.isoSpec.hom).obj
        ((differentialModule k Γ(X, W)).tilde)).val.obj (op (⊤ : W.toScheme.Opens)) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  exact ((_root_.SheafOfModules.evaluation W.toScheme.ringCatSheaf
    (op (⊤ : W.toScheme.Opens))).mapIso (affineDifferentialIso f hW)).toLinearEquiv

/-- The additive sections of the restricted differential sheaf on `⊤` are its sections over the image
of `⊤`, by the accepted restriction comparison. -/
def restrictedSectionsIso {W : X.Opens} :
    ((restriction W.ι).obj (baseRingSheaf f)).val.presheaf.obj (op (⊤ : W.toScheme.Opens)) ≅
      (baseRingSheaf f).val.presheaf.obj (op (W.ι ''ᵁ (⊤ : W.toScheme.Opens))) :=
  restrictionSectionsIso W.ι (baseRingSheaf f) ⊤

end KltDP.Geometry.AffineDifferentialSections
