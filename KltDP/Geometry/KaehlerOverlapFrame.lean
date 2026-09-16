import KltDP.Geometry.KaehlerBasicOpenFrame

/-!
# Two chart frames on one overlap, without transporting anything

This is the piece the cross-chart atlas needs, and it is where the naive route is **blocked**.

`KaehlerOverlapRefinement.exists_common_basicOpen` gives, around a point of `U₁ ⊓ U₂`, elements
`a : Γ(X, U₁)` and `c : Γ(X, U₂)` with `X.basicOpen a = X.basicOpen c`. Promoting each chart's frame
with `KaehlerBasicOpenFrame.basicOpenFrame` lands them in `Ω[Γ(X, X.basicOpen a)⁄k]` and
`Ω[Γ(X, X.basicOpen c)⁄k]` — two *different* modules over two *different* rings, identified only
propositionally. Comparing them by rewriting that equality would carry **a ring and a module
together**, which is exactly the heterogeneous transport the lane rules forbid and which cost this
lane five sessions.

**The fix is to re-index, not to transport.** Both promotions are made into the sections of one open
`V`, with the open equalities taken as *hypotheses* and `subst`-ed — the accepted
`SchemeModuleRestriction.sectionsOfImageEq` pattern. Two facts make that legitimate:

* the `Γ(X, W)`-algebra structure on `Γ(X, V)` is **defined from `V ≤ W`** (`restrictAlgebra`), not
  transported; after `subst` it is definitionally Mathlib's
  `Scheme.algebra_section_section_basicOpen`, because the two differ only in a proof of `V ≤ W` and
  proofs are irrelevant;
* `IsLocalization` is a **`Prop`**, so moving it along the open equality carries no data at all.

So `restrict_isLocalization` and `restrict_isScalarTower` put both charts' localization data on the
same open, and `overlapFrame` promotes either chart's frame into `Ω[Γ(X, V)⁄k]` — **one** module.
`overlapTransitionUnit` is then an honest `Γ(X, V)ˣ` comparing two frames of the same module, with no
cast anywhere in its statement or its proof.

* **`restrictAlgebra`**: `Algebra Γ(X, W) Γ(X, V)` from `V ≤ W`, the sheaf restriction. Named, not a
  global instance, matching the tree's policy for `affineSectionsAlgebra`.
* **`restrict_isLocalization`**: `IsLocalization (Submonoid.powers r) Γ(X, V)` when
  `X.basicOpen r = V`.
* **`restrict_isScalarTower`**: the `k`-tower for any affine `V ≤ W`, from accepted
  `baseToAffineSectionsMap_restrict`.
* **`overlapFrame`**, **`frameChangeUnit_overlapFrame`**: a chart frame promoted to `V`, and its
  transition unit as the image of the chart's.
* **`overlapTransitionUnit`**: the cross-chart unit on a common overlap.

Nothing is admitted here. This module does **not** assemble an atlas; it removes the obstruction that
prevented one. See the lane notes for what the assembly still requires.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.KaehlerLocalizedFrame

universe u

namespace KltDP.Geometry.KaehlerOverlapFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {n : ℕ}

/-- **The sections algebra of a smaller open**, defined from the inclusion rather than transported.
On a basic open this is definitionally the pinned `Scheme.algebra_section_section_basicOpen`. -/
def restrictAlgebra {V W : X.Opens} (hVW : V ≤ W) : Algebra Γ(X, W) Γ(X, V) :=
  (X.presheaf.map (homOfLE hVW).op).hom.toAlgebra

/-- **An open presented as a basic open is a localization**, stated on the open itself. The open
equality is a hypothesis and is `subst`-ed; `IsLocalization` is a `Prop`, so nothing is carried. -/
theorem restrict_isLocalization {V W : X.Opens} (hW : IsAffineOpen W) (r : Γ(X, W))
    (hVW : V ≤ W) (h : X.basicOpen r = V) :
    letI := restrictAlgebra hVW
    IsLocalization (Submonoid.powers r) Γ(X, V) := by
  subst h
  exact hW.isLocalization_basicOpen r

/-- **The `k`-scalar tower for any affine open inside an affine chart.** This is the accepted
`baseToAffineSectionsMap_restrict` read through `IsScalarTower.of_algebraMap_eq`. -/
theorem restrict_isScalarTower {V W : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hVW : V ≤ W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
    letI := restrictAlgebra hVW
    IsScalarTower k Γ(X, W) Γ(X, V) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
  letI := restrictAlgebra hVW
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  exact (congrArg (fun φ : CommRingCat.of k ⟶ Γ(X, V) => φ.hom a)
    (baseToAffineSectionsMap_restrict f hW hV hVW)).symm

/-- **A chart frame promoted to a common overlap**, presented as a basic open of the chart. -/
def overlapFrame {V W : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (r : Γ(X, W))
    (hVW : V ≤ W) (h : X.basicOpen r = V) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
    Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)) →
      Basis (Fin n) Γ(X, V) (KaehlerDifferential k Γ(X, V)) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
  letI := restrictAlgebra hVW
  letI := restrict_isLocalization hW r hVW h
  letI := restrict_isScalarTower f hW hV hVW
  exact fun b => localizedFrame k Γ(X, W) Γ(X, V) (Submonoid.powers r) b

/-- **The promoted frames' transition unit is the image of the chart's transition unit.** -/
theorem frameChangeUnit_overlapFrame {V W : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (r : Γ(X, W)) (hVW : V ≤ W) (h : X.basicOpen r = V) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
    letI := restrictAlgebra hVW
    ∀ b b' : Basis (Fin n) Γ(X, W) (KaehlerDifferential k Γ(X, W)),
      frameChangeUnit (overlapFrame f hW hV r hVW h b) (overlapFrame f hW hV r hVW h b') =
        Units.map (algebraMap Γ(X, W) Γ(X, V)).toMonoidHom (frameChangeUnit b b') := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
  letI := restrictAlgebra hVW
  letI := restrict_isLocalization hW r hVW h
  letI := restrict_isScalarTower f hW hV hVW
  intro b b'
  exact frameChangeUnit_localizedFrame k Γ(X, W) Γ(X, V) (Submonoid.powers r) b b'

/-- **The cross-chart transition unit on a common overlap.** Both frames are bases of the *same*
module `Ω[Γ(X, V)⁄k]`, so this is an ordinary frame-change unit: no transport, no cast. -/
def overlapTransitionUnit {U₁ U₂ V : X.Opens} (h₁ : IsAffineOpen U₁) (h₂ : IsAffineOpen U₂)
    (hV : IsAffineOpen V) (a : Γ(X, U₁)) (c : Γ(X, U₂))
    (hV₁ : V ≤ U₁) (hV₂ : V ≤ U₂)
    (ha : X.basicOpen a = V) (hc : X.basicOpen c = V) :
    letI : Algebra k Γ(X, U₁) := (baseToAffineSectionsMap f h₁).hom.toAlgebra
    letI : Algebra k Γ(X, U₂) := (baseToAffineSectionsMap f h₂).hom.toAlgebra
    Basis (Fin n) Γ(X, U₁) (KaehlerDifferential k Γ(X, U₁)) →
      Basis (Fin n) Γ(X, U₂) (KaehlerDifferential k Γ(X, U₂)) → Γ(X, V)ˣ := by
  letI : Algebra k Γ(X, U₁) := (baseToAffineSectionsMap f h₁).hom.toAlgebra
  letI : Algebra k Γ(X, U₂) := (baseToAffineSectionsMap f h₂).hom.toAlgebra
  exact fun b₁ b₂ =>
    frameChangeUnit (overlapFrame f h₁ hV a hV₁ ha b₁) (overlapFrame f h₂ hV c hV₂ hc b₂)

end KltDP.Geometry.KaehlerOverlapFrame
