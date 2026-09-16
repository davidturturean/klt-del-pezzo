import KltDP.Geometry.ExteriorPowerFrameComparison
import KltDP.Geometry.SmoothSurfaceKaehlerAtlas

/-!
# The smooth canonical frame line is the actual top-differential sheaf

The source line is the existing determinant-glued canonical sheaf. The
target is independently defined by the global relative Kähler sheaf and
the actual exterior-presheaf/sheafification construction. The comparison
uses the existing restriction-compatible Kähler frames; smoothness supplies
the atlas on a surface.

This identifies the canonical frame line with `∧² Ω_{X/k}`. It supplies no
dualizing complex, Serre-duality pairing, Euler reflection, or Riemann--Roch.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.ChartKaehlerOpenFrame

universe u

namespace KltDP.Geometry.SmoothCanonicalExteriorComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section ChartAtlas

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The exterior sheaf of the original global relative Kähler sheaf.
Its definition has no smoothness, frame, atlas, or canonical-line input. -/
abbrev relativeDifferentialExterior (n : ℕ) : X.Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf f) n

/-- An existing Kähler-frame atlas identifies its canonical line with the
independent exterior sheaf of the original global Kähler sheaf. -/
def kaehlerChartAtlasIso {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) {n : ℕ}
    (b : ∀ i, letI := KaehlerChartAtlas.chartAlgebra f U hU i;
      Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i)))
    (hcov : (⨆ i, U i) = ⊤) :
    (KaehlerChartAtlas.canonicalSheaf f U hU b hcov).obj ≅
      relativeDifferentialExterior f n :=
  (ExteriorPowerFrameComparison.sheafIso (baseRingSheaf f) U
    (fun i W hW => chartOpenFrame f (hU i) (b i) W hW)
    (fun i _ _ hVW hW t => chartOpenFrame_restrict f (hU i) (b i) hVW hW t)
    hcov).symm

end ChartAtlas

section SmoothSurface

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]

/-- For an actual smooth surface, the already constructed canonical frame
line is the actual second exterior sheaf of relative differentials. No
additional atlas hypothesis is needed. -/
def canonicalSheafOfSmoothSurfaceIsoExterior :
    (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface f).obj ≅
      relativeDifferentialExterior f 2 :=
  kaehlerChartAtlasIso f (SmoothSurfaceKaehlerAtlas.atlasOpen f)
    (SmoothSurfaceKaehlerAtlas.atlasOpen_isAffineOpen f)
    (SmoothSurfaceKaehlerAtlas.atlasFrame f) (SmoothSurfaceKaehlerAtlas.atlasOpen_iSup f)

/-- The independent top-differential sheaf is locally free of rank one. -/
theorem relativeDifferentialExterior_isInvertible :
    isInvertibleSheaf X (relativeDifferentialExterior f 2) :=
  KltDP.SheafOfModules.IsInvertible.of_iso
    (R := X.ringCatSheaf)
    (M := (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface f).obj)
    (N := relativeDifferentialExterior f 2)
    (canonicalSheafOfSmoothSurfaceIsoExterior f)

end SmoothSurface

end KltDP.Geometry.SmoothCanonicalExteriorComparison
