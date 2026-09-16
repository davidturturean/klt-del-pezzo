import KltDP.Geometry.AffineDifferentialSections

/-!
# The scalar bridge for the affine sections of the differential sheaf

`AffineDifferentialSections.affineDifferentialSectionsEquiv` compares the sections of `Ω_{X/k}` on an
affine open `W` with the sections of the tilde of `Ω[Γ(X, W)⁄k]`, over the ring `Γ(W.toScheme, ⊤)`.
This module records the ring bridge from that ring to `Γ(X, W)`, which is the form the chart frames of
`KaehlerLocalizedFrame` are stated in.

The bridge is **not** definitional and is deliberately exposed rather than hidden:

* `Scheme.Opens.toScheme_presheaf_obj` gives `Γ(W.toScheme, V) = Γ(X, W.ι ''ᵁ V)` by `rfl`, so the
  sections ring of the open subscheme at `⊤` *is* `Γ(X, W.ι ''ᵁ ⊤)`;
* but `W.ι ''ᵁ ⊤ = W` (`Scheme.Opens.ι_image_top`) is only propositional, which is exactly why pinned
  Mathlib supplies `Scheme.Opens.topIso : Γ(W, ⊤) ≅ Γ(X, W)` as an `eqToIso`-based ring isomorphism
  rather than an identity.  Pinned Mathlib flags the two as merely "non-reducibly defeq".

* **`sectionsRingIso`**: that ring isomorphism, named at the scheme level.
* **`sectionsRing_eq`**: the `rfl`-level identification `Γ(W.toScheme, ⊤) = Γ(X, W.ι ''ᵁ ⊤)`, recorded
  so consumers can see which hop is free and which one costs an `eqToIso`.

Nothing is admitted here.  What remains for the bridge is to carry
`affineDifferentialSectionsEquiv` across `sectionsRingIso` and compose with the tilde's global-section
comparison (`AffineModuleTilde.isoTop`, whose carrier is `tildeInModuleCat.obj (op ⊤)`, the same
carrier as `.tilde.val.obj (op ⊤)` but differently bundled — the accepted `AffineModuleTildeUnit`
states its own equivalence at the `.tilde.val.obj` spelling, which is the one to mirror).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialSectionsGamma

variable {X : Scheme.{u}}

/-- **The ring bridge**: the sections of an open subscheme at `⊤` versus the sections on the open. -/
def sectionsRingIso (W : X.Opens) : Γ(W.toScheme, ⊤) ≅ Γ(X, W) :=
  W.topIso

/-- The free half of the bridge: the sections ring of the open subscheme at `⊤` **is** the sections
ring of `X` on the image of `⊤`, definitionally. -/
theorem sectionsRing_eq (W : X.Opens) :
    Γ(W.toScheme, (⊤ : W.toScheme.Opens)) = Γ(X, W.ι ''ᵁ (⊤ : W.toScheme.Opens)) := rfl

end KltDP.Geometry.AffineDifferentialSectionsGamma
