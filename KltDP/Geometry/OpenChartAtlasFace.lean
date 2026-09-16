import KltDP.Geometry.RationalTreePicardRestrictionPullbackSections

/-!
# The `Opens`-site face of an open-chart atlas, at a supplied index (F03/F04 infrastructure)

The tracked blocker `docs/BLOCKER_OVERSITE_INSTANTIATION_20260912.md` asks for an `Opens`-site face of
`TransitionUnitExtraction.chartEquiv` stated **at a supplied index**, so that a consumer at a concrete
atlas never has to instantiate `chartEquiv`'s definition — which fixes the over-site category
`X.ringCatSheaf.over (t.X i)` inside itself, and so cannot be folded by rewriting any equation.

**The interface asked for is already accepted.** `KltDP.Geometry.RationalTreePicard.chartEquiv_ofOpenCharts`
states, for an atlas `localTrivializationsOfOpenCharts M V hV e`,
`chartEquiv X M _ i hWi s = openChartCoordinate M (V i) (e i) hWi s`, with the index supplied in the
statement as `hWi : W ≤ V i`; and `openChartCoordinate` is over-site-free, read on the `Opens` site by
the accepted `openChartCoordinate_app`. Its proof is `rw [chartEquiv_apply]` followed by `congrArg` —
never `rw` — against `unitIso_ofOpenCharts_hom`, which is exactly why it elaborates where a rewrite of
the over-site term cannot: `congrArg` builds the equation at the morphism, so the category index is
never matched syntactically.

This module adds only the two consumer-facing corollaries that were missing, both stated at a supplied
index and both discharging their over-site content through accepted lemmas:

* `chartEquiv_ofOpenCharts_eq`: the chart coordinate equals a given section value `r`, given the
  scheme-level chart equation over `(V i).ι ⁻¹ᵁ W`;
* `chartEquiv_ofOpenCharts_eq_one`: the frame case `r = 1`, which is the shape every atlas frame
  condition actually has.

Nothing here is admitted, and nothing is assumed: every hypothesis is an `Opens`-site equation about
the chart trivialisation `e i` alone.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenChartAtlasFace

open SchemeModuleRestriction TransitionUnitExtraction
open KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules)

/-- **The over-site coordinate read on the `Opens` site**, with the preimage open written directly as
`U.ι ⁻¹ᵁ W` rather than through `U.overEquivalence.functor`. The two indices are definitionally equal
(the accepted `overEquivalence_functor_obj_top` is the same `rfl`), so this is the accepted
`openChartCoordinate_app` in the shape a chart-level frame condition is actually stated in. -/
theorem openChartCoordinate_app_preimage (U : X.Opens)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    {W : X.Opens} (hW : W ≤ U) (s : M.val.obj (op W)) :
    U.ι.app W (openChartCoordinate M U e hW s) =
      e.inv.val.app (op (U.ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset U.ι.base (W : Set X))).op s) :=
  openChartCoordinate_app M U e hW s

variable {ι : Type u} (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
  (e : ∀ i, _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅
    (restriction (V i).ι).obj M)

/-- **The chart coordinate of an open-chart atlas, at a supplied index.** The hypothesis mentions no
over-site object: it is an equation about the chart trivialisation `e i` on `(V i).ι ⁻¹ᵁ W`, read
against the image `(V i).ι.app W r` of the intended value. A consumer at a concrete atlas supplies its
own chart-level frame identity and never instantiates `chartEquiv`. -/
theorem chartEquiv_ofOpenCharts_eq (i : ι) {W : X.Opens} (hWi : W ≤ V i)
    (s : M.val.obj (op W)) (r : Γ(X, W))
    (h : (e i).inv.val.app (op ((V i).ι ⁻¹ᵁ W))
        ((M.val.map (homOfLE (x := (V i).ι ''ᵁ (V i).ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset (V i).ι.base (W : Set X))).op s)) =
      (V i).ι.app W r) :
    chartEquiv X M (localTrivializationsOfOpenCharts M V hV e) i hWi s = r := by
  have h1 : (V i).ι.app W (openChartCoordinate M (V i) (e i) hWi s) = (V i).ι.app W r :=
    (openChartCoordinate_app_preimage M (V i) (e i) hWi s).trans h
  have h2 := congrArg (openSectionsInv (V i) hWi) h1
  rw [openSectionsInv_app, openSectionsInv_app] at h2
  exact (chartEquiv_ofOpenCharts M V hV e i hWi s).trans h2

/-- **The frame case at a supplied index**: if the chart trivialisation sends the restricted section to
`1`, the atlas chart coordinate of that section is `1`. This is the shape every atlas frame condition
has, and it is the statement a concrete consumer applies with `exact`.  (`map_one` is used as a
rewrite against the `RingHom` `openSectionsInv`, never as a term against a categorical `CommRingCat`
hom, which carries no `MonoidHomClass`.) -/
theorem chartEquiv_ofOpenCharts_eq_one (i : ι) {W : X.Opens} (hWi : W ≤ V i)
    (s : M.val.obj (op W))
    (h : (e i).inv.val.app (op ((V i).ι ⁻¹ᵁ W))
        ((M.val.map (homOfLE (x := (V i).ι ''ᵁ (V i).ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset (V i).ι.base (W : Set X))).op s)) =
      (1 : Γ((V i).toScheme, (V i).ι ⁻¹ᵁ W))) :
    chartEquiv X M (localTrivializationsOfOpenCharts M V hV e) i hWi s = (1 : Γ(X, W)) := by
  have h1 : (V i).ι.app W (openChartCoordinate M (V i) (e i) hWi s) = 1 :=
    (openChartCoordinate_app_preimage M (V i) (e i) hWi s).trans h
  have h2 := congrArg (openSectionsInv (V i) hWi) h1
  rw [openSectionsInv_app, map_one] at h2
  exact (chartEquiv_ofOpenCharts M V hV e i hWi s).trans h2

end KltDP.Geometry.OpenChartAtlasFace
