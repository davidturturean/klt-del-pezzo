import KltDP.Geometry.QuadraticCoverAtlasIntegral
import KltDP.Geometry.QuadraticCoverOddValuation
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Group.Even

/-!
# One original branch coefficient controls the actual quadratic atlas

All branch coefficients are compared in the same original scheme function
field, using the canonical generic-point germ maps. The original overlap
unit and the original branch equation give a unit-square relation between
these images. Pinned `IsSquare.sq` and `IsSquare.mul` then transfer
nonsquareness from one nonempty chart to every nonempty chart.

For an atlas of nonempty charts, canonical germ injectivity supplies the
injections required by the existing global-integrality theorem. One original
finite odd valuation therefore suffices for the constructed cover's
integrality. No chartwise nonsquare family or global integrality conclusion
is supplied. No characteristic restriction, separability or smoothness claim
is made. Geometric production of the actual odd valuation remains separate.

The nonempty-chart hypothesis in the global adapters is literal: an arbitrary
atlas may contain empty opens, where a germ to a field is not defined.
Removing such charts is a separate atlas comparison if needed.

Reuse: pinned FunctionField.germToFunctionField, germ_res_apply, the original
germ-injectivity theorem and IsSquare multiplication; the same APIs were
checked in newer official Mathlib (Apache 2.0). No general square-arithmetic
lemma, new function field or new scalar map is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} [IsIntegral X] {ι : Type u}
    (D : QuadraticCoverAtlas.Data X ι)

private theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (res X h a) = X.germToFunctionField U a :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (inferInstance : Nonempty V))) a

private theorem branch_germs_related (i j : ι)
    [Nonempty (D.opens i)] [Nonempty (D.opens j)] :
    ∃ q : X.functionFieldˣ,
      X.germToFunctionField (D.opens i) (D.sections i) =
        (q : X.functionField) ^ 2 *
          X.germToFunctionField (D.opens j) (D.sections j) := by
  letI : Nonempty (D.opens i ⊓ D.opens j : X.Opens) := by
    obtain ⟨xi⟩ := (inferInstance : Nonempty (D.opens i))
    obtain ⟨xj⟩ := (inferInstance : Nonempty (D.opens j))
    obtain ⟨x, hxi, hxj⟩ := nonempty_preirreducible_inter
      (D.opens i).isOpen (D.opens j).isOpen ⟨xi.val, xi.property⟩ ⟨xj.val, xj.property⟩
    exact ⟨⟨x, hxi, hxj⟩⟩
  let q : X.functionFieldˣ :=
    Units.map (X.germToFunctionField (D.opens i ⊓ D.opens j)).hom.toMonoidHom
      (D.units i j)
  refine ⟨q, ?_⟩
  change X.germToFunctionField (D.opens i) (D.sections i) =
    (X.germToFunctionField (D.opens i ⊓ D.opens j)
      (D.units i j : Γ(X, D.opens i ⊓ D.opens j))) ^ 2 *
        X.germToFunctionField (D.opens j) (D.sections j)
  simpa only [map_mul, map_pow, germ_restrict] using
    congrArg (X.germToFunctionField (D.opens i ⊓ D.opens j)).hom (D.branch i j)

/-- Nonsquareness of one original coefficient transfers to any other nonempty
chart through the original transition unit, in the same original function field. -/
theorem functionField_nonsquare_of_chart (i j : ι)
    [Nonempty (D.opens i)] [Nonempty (D.opens j)]
    (hs : ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens i) (D.sections i)) :
    ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens j) (D.sections j) := by
  intro x hx
  obtain ⟨q, hq⟩ := branch_germs_related D i j
  have hj : IsSquare (X.germToFunctionField (D.opens j) (D.sections j)) :=
    (isSquare_iff_exists_sq _).mpr ⟨x, hx.symm⟩
  have hi : IsSquare (X.germToFunctionField (D.opens i) (D.sections i)) :=
    hq.symm ▸ (IsSquare.sq (q : X.functionField)).mul hj
  obtain ⟨y, hy⟩ := hi.exists_sq
  exact hs y hy.symm

/-- One original function-field nonsquare gives an integral constructed cover.
All chart injections and all other nonsquare coefficients are derived. -/
theorem scheme_isIntegral_of_functionField_nonsquare
    [∀ i, Nonempty (D.opens i)] (i : ι)
    (hs : ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens i) (D.sections i)) :
    IsIntegral D.scheme := by
  apply D.scheme_isIntegral_of_chart_nonsquare (fun _ : ι => ↥X.functionField)
  · intro j
    change Function.Injective (X.germToFunctionField (D.opens j))
    exact X.germToFunctionField_injective (D.opens j)
  · intro j
    change ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens j) (D.sections j)
    exact functionField_nonsquare_of_chart D i j hs

/-- A finite odd valuation of one original chart coefficient suffices for
global integrality. The actual valuation and its value are inputs; neither
chartwise nonsquareness nor any cover-domain assertion is an input. -/
theorem scheme_isIntegral_of_functionField_oddValuation
    [∀ i, Nonempty (D.opens i)] (i : ι)
    (valuation : AddValuation X.functionField (WithTop ℤ)) (z : ℤ)
    (hv : valuation (X.germToFunctionField (D.opens i) (D.sections i)) =
      (z : WithTop ℤ)) (hz : Odd z) : IsIntegral D.scheme :=
  scheme_isIntegral_of_functionField_nonsquare D i
    (nonsquare_of_odd_addValuation valuation
      (X.germToFunctionField (D.opens i) (D.sections i)) z hv hz)

end KltDP.Geometry.QuadraticCoverAtlas.Data
