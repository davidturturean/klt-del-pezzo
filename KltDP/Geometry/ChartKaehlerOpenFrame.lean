import KltDP.Geometry.ChartKaehlerOverFree
import KltDP.Compatibility.FreeSheafSections
import KltDP.Compatibility.FreeSheafTransportedBasis
import KltDP.Geometry.TransitionUnitSections

/-!
# A chart frame of `Ω` gives a frame of its sections on **every** open below the chart

This is route 1's payload. `ChartFrameAtlasSheaf` demands a frame on every open `W ≤ U i`, and that
demand is structural: `IsCocycle.mul_res` states its units on the full pairwise intersections, which
are not basic opens of either chart. A *sheaf-level* free presentation supplies exactly that, because
the sections of a finite free sheaf over **any** object of the site are free
(`KltDP.Compatibility.FreeSheafSections.freeSectionsBasis`).

* **`differentialSections`**, **`differentialRestr`**: the module family `W ↦ Ω_{X/k}(W)` and its
  restriction maps, semilinear over the structure-sheaf restriction — the `L` and `restr` fields of
  the atlas.
* **`chartOpenFrame`**: a chart frame `Basis (Fin n) Γ(X, U) (Ω[Γ(X, U)⁄k])` gives
  `Basis (Fin n) Γ(X, W) (Ω_{X/k}(W))` for every `W ≤ U` — the atlas's `frame` field.
* **`chartOpenFrame_restrict`**: those frames restrict to one another — the atlas's `hframe` field.

**Why `hframe` is cheap here.** The frame vectors are the values of *one* family of tautological
sections of the free sheaf, carried across a *sheaf* isomorphism. So their compatibility is
`freeSectionsBasis_map` (the `sections` property) plus `PresheafOfModules.naturality_apply` — the
same pattern the accepted `overTrivializationSectionEquiv_naturality` uses. No naturality of a
comparison isomorphism in the open has to be proved.

The over-site index `Over.mk (homOfLE hW)` and the identification of `((baseRingSheaf f).over U)`'s
sections at it with `Ω_{X/k}(W)` follow the accepted `overTrivializationSectionEquiv`, which is
stated with source `M.val.obj (op V)` and scalars `Γ(X, V)` for exactly this reason.

The index of a free sheaf must lie in `Type u`, so the free presentation is indexed by
`ULift (Fin n)` and the frame is reindexed along `Equiv.ulift`. That reindexing is of the *basis*;
no sheaf is transported.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.ChartKaehlerOverFree
open KltDP.Geometry.TransitionUnitGluing
open KltDP.Compatibility.FreeSheafSections
open KltDP.Compatibility.FreeSheafTransportedBasis

universe u

namespace KltDP.Geometry.ChartKaehlerOpenFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Re-declaration of the accepted sheafification instance on an over site: the accepted one is
`local` and does not reach importing modules. -/
local instance laneOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  schemeOverHasWeakSheafify X U

/-- Re-declaration of the accepted local-bijectivity instance on an over site, for the same reason. -/
local instance laneOverWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} :=
  schemeOverWEqualsLocallyBijective X U

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The module family the atlas consumes**: the sections of `Ω_{X/k}` on each open. -/
abbrev differentialSections (W : X.Opens) : Type u := (baseRingSheaf f).val.obj (op W)

/-- **Restriction of differential sections**, semilinear over the structure-sheaf restriction. -/
def differentialRestr {V W : X.Opens} (h : V ≤ W) :
    differentialSections f W →ₛₗ[res X h] differentialSections f V where
  toFun := (baseRingSheaf f).val.map (homOfLE h).op
  map_add' x y := map_add _ x y
  map_smul' r x := (baseRingSheaf f).val.map_smul (homOfLE h).op r x

/-- **A chart frame gives a frame of the differential sections on every open below the chart**,
at the index the free sheaf carries. -/
def chartOpenFrameULift {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)) →
      ∀ (W : X.Opens), W ≤ U →
        Basis (ULift.{u} (Fin n)) Γ(X, W) (differentialSections f W) := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  intro b W hW
  exact transportedBasis (X.ringCatSheaf.over U) (ULift.{u} (Fin n))
    ((baseRingSheaf f).over U) (chartOverFreeIsoFin f hU b)
    (op (Over.mk (homOfLE hW)))

/-- **Those frames restrict to one another.** With `transportedBasis` opaque this is one
application of `transportedBasis_map`; nothing of the chart construction is unfolded. -/
theorem chartOpenFrameULift_restrict {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    ∀ (b : Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)))
      {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U) (s : ULift.{u} (Fin n)),
      differentialRestr f hVW (chartOpenFrameULift f hU b W hW s) =
        chartOpenFrameULift f hU b V (hVW.trans hW) s := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  intro b V W hVW hW s
  exact transportedBasis_map (X.ringCatSheaf.over U) (ULift.{u} (Fin n))
    ((baseRingSheaf f).over U) (chartOverFreeIsoFin f hU b)
    (Over.homMk (homOfLE hVW) (Subsingleton.elim _ _) :
      Over.mk (homOfLE (hVW.trans hW)) ⟶ Over.mk (homOfLE hW)).op s

/-- **The chart frame the atlas consumes**, indexed by `Fin n`. -/
def chartOpenFrame {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)) →
      ∀ (W : X.Opens), W ≤ U → Basis (Fin n) Γ(X, W) (differentialSections f W) := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  intro b W hW
  exact (chartOpenFrameULift f hU b W hW).reindex (Equiv.ulift.{u, 0} (α := Fin n))

/-- **Those frames restrict to one another.** This is the atlas's `hframe` hypothesis. -/
theorem chartOpenFrame_restrict {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    ∀ (b : Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)))
      {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U) (t : Fin n),
      differentialRestr f hVW (chartOpenFrame f hU b W hW t) =
        chartOpenFrame f hU b V (hVW.trans hW) t := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  intro b V W hVW hW t
  show differentialRestr f hVW
      ((chartOpenFrameULift f hU b W hW).reindex (Equiv.ulift.{u, 0} (α := Fin n)) t) =
    (chartOpenFrameULift f hU b V (hVW.trans hW)).reindex
      (Equiv.ulift.{u, 0} (α := Fin n)) t
  rw [Basis.reindex_apply, Basis.reindex_apply]
  exact chartOpenFrameULift_restrict f hU b hVW hW _

end KltDP.Geometry.ChartKaehlerOpenFrame
