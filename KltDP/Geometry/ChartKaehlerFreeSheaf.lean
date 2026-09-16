import KltDP.Geometry.SmoothKaehlerLocallyFree

/-!
# A chart frame gives a free-sheaf presentation of `Ω` on the chart

Route 1 of the atlas assembly needs a frame of `Ω_{X/k}` on **every** open below a chart — which
`ChartFrameAtlasSheaf` structurally demands, because `IsCocycle.mul_res` states its units on the full
pairwise intersections. A *sheaf-level* free iso supplies exactly that, and the accepted
`SmoothKaehlerLocallyFree.exists_standardSmooth_open_freeIso` proves one exists. This module records
the **named, frame-parameterised** version of it.

Two of the three costs of route 1 are discharged here, and both turn out to be cheaper than expected:

* **Rank normalisation.** There is no `∃ I` to normalise. The accepted
  `SmoothKaehlerLocallyFree.affineFreeIsoOfBasis` already takes an *arbitrary* index with `[Finite I]`
  and a basis of `Ω[A⁄k]`; the existential in `exists_standardSmooth_open_freeIso` appears only
  because that theorem chooses `Module.Free.ChooseBasisIndex` for itself. Instantiating
  `affineFreeIsoOfBasis` at a given index with a chart frame avoids the existential entirely.
* **`RingHom.IsStandardSmooth`.** Not required. Standard smoothness is used only to *produce* a basis
  (`Module.Free.chooseBasis`). `ChartFrameAtlasSheaf` takes its frames as **data**, so the assembly
  needs no smoothness hypothesis at all; smoothness re-enters only when one wants to *exhibit* the
  frames, via the accepted `isSmooth_field_exists_affine_standardSmooth`.

**The index lives in `Type u`, not in `Type`.** `SheafOfModules.free` takes `I : Type u` where `u` is
the universe of the ring sheaf, so `Fin n : Type` does not typecheck there; `chartFreeIsoFin`
supplies the `Fin n`-parameterised frame by reindexing along `Equiv.ulift` and landing on
`ULift (Fin n)`. This is the whole of the rank normalisation cost, and it is a reindexing of the
*basis*, never a transport of the sheaf.

* **`chartFreeIso`**: a frame `Basis I Γ(X, U) (Ω[Γ(X, U)⁄k])` with `I : Type u` finite gives
  `free (R := U.toScheme.ringCatSheaf) I ≅ (restriction U.ι).obj (baseRingSheaf f)`.
* **`chartFreeIsoFin`**: the same for a frame indexed by `Fin n`, at index `ULift (Fin n)`.

The construction mirrors the accepted `exists_standardSmooth_open_freeIso` step for step — the square
`hj : hU.isoSpec.hom ≫ g = U.ι ≫ f`, the coproduct-preservation instance from
`restrictionAdjunction`, `mapFreeIso`, and the two `restrictionIso` hops — with
`affineFreeIsoOfBasis` in place of `standardSmoothAffineFreeIso`.

Note this is deliberately the **`U.ι`** presentation, not the `fromSpec` one used by
`AffineDifferentialGammaEquiv`: the accepted over-site bridge (`openToOverRestrictionIso`) is stated
for `restriction U.ι`, so that is the presentation route 1 must land in.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeKaehlerOpenRestriction
open KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.SmoothKaehlerLocallyFree

universe u

namespace KltDP.Geometry.ChartKaehlerFreeSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **A chart frame presents `Ω_{X/k}` on the chart as a free sheaf.** -/
def chartFreeIso {U : X.Opens} (hU : IsAffineOpen U) {I : Type u} [Finite I] :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    Basis I Γ(X, U) (KaehlerDifferential k Γ(X, U)) →
      (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (restriction U.ι).obj (baseRingSheaf f)) := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  intro b
  let j := hU.isoSpec.hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
  have hj : j ≫ g = U.ι ≫ f := by
    change hU.isoSpec.hom ≫ Spec.map (baseToAffineSectionsMap f hU) = U.ι ≫ f
    rw [Spec_map_baseToAffineSectionsMap f hU, ← Category.assoc,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
  letI : PreservesColimitsOfSize.{u, u} (restriction j) :=
    (restrictionAdjunction j).leftAdjoint_preservesColimits
  let e₀ : _root_.SheafOfModules.free
      (R := (Spec (CommRingCat.of Γ(X, U))).ringCatSheaf) I ≅ baseRingSheaf g :=
    affineFreeIsoOfBasis k Γ(X, U) b
  let e₁ : _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (restriction j).obj (baseRingSheaf g) :=
    _root_.SheafOfModules.mapFreeIso (restriction j) I (restrictionUnitIso j).symm ≪≫
      (restriction j).mapIso e₀
  let e₂ : baseRingSheaf (j ≫ g) ≅ baseRingSheaf (U.ι ≫ f) :=
    eqToIso (congrArg baseRingSheaf hj)
  exact e₁ ≪≫ restrictionIso g j ≪≫ e₂ ≪≫ (restrictionIso f U.ι).symm

/-- **The same, for a frame indexed by `Fin n`.** The index of the free sheaf must live in `Type u`,
so it is `ULift (Fin n)` and the frame is reindexed along `Equiv.ulift`. -/
def chartFreeIsoFin {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)) →
      (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ≅
        (restriction U.ι).obj (baseRingSheaf f)) := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  exact fun b => chartFreeIso f hU (b.reindex (Equiv.ulift.{u, 0} (α := Fin n)).symm)

end KltDP.Geometry.ChartKaehlerFreeSheaf
