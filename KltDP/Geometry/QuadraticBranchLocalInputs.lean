import KltDP.Geometry.QuadraticCoverReducedBranch
import KltDP.Geometry.QuadraticRamificationCharts
import KltDP.Geometry.NormalAffineSections

/-!
# Local inputs from the actual branch quotient scheme

A point of the original branch chart `Spec(R/(s))` lies over a prime
containing the original coefficient `s`. Consequently `s` is a nonunit.
Under the original affine chart map, its actual structure-sheaf germ is
also a nonunit: the point is outside the basic open of `s`.

Reducedness of that same affine branch scheme implies reducedness of the
literal quotient ring, using the pinned affine-Spec equivalence. For an
original quadratic atlas on an integral normal base, one nonempty reduced
branch chart with nonzero coefficient therefore proves integrality of the
unchanged glued cover. Empty unselected charts are allowed.

The branch point, branch reducedness, original base normality and nonzero
coefficient are geometric inputs. This file derives the ring and stalk
nonunit conditions; it does not identify a separately supplied geometric
Cartier divisor with the branch quotient, derive its reducedness from
smoothness, or prove the nonzero coefficient from a Cartier equation.
There is no characteristic restriction or cover-smoothness conclusion.

Reuse: pinned `affine_isReduced_iff`, `fromSpec_preimage_basicOpen`,
`RingedSpace.mem_basicOpen`, and the actual affine section-ring normality
adapter. Newer official Mathlib a4d9f2fdd2f64b55969042eef459606961dc63a2
retains these affine reducedness/basic-open APIs (Apache-2.0). No source
port or dependency change is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R]

/-- The actual branch point lies over a prime containing its original
defining coefficient. -/
theorem branch_point_mem_ideal (s : R) (y : branchScheme s) :
    s ∈ ((branchι s).base y).asIdeal := by
  change Ideal.Quotient.mk (branchIdeal s) s ∈ y.asIdeal
  rw [branchQuotient_mk_self]
  exact y.asIdeal.zero_mem

/-- Nonemptiness of the actual branch supplies the nonunit condition. -/
theorem branch_point_not_isUnit (s : R) (y : branchScheme s) : ¬IsUnit s := by
  intro hs
  exact ((branchι s).base y).isPrime.ne_top
    (((branchι s).base y).asIdeal.eq_top_of_isUnit_mem
      (branch_point_mem_ideal s y) hs)

/-- Reducedness belongs to the original quotient ring, by the actual
affine-Spec equivalence, rather than to a substituted branch ring. -/
theorem branch_quotient_isReduced (s : R) (hred : IsReduced (branchScheme s)) :
    _root_.IsReduced (R ⧸ Ideal.span ({s} : Set R)) :=
  (affine_isReduced_iff (.of (R ⧸ branchIdeal s))).mp hred

/-- The actual map from the branch chart lands in its original base open. -/
theorem branch_point_mem_open {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Γ(X, U)) (y : branchScheme s) :
    ((branchι s) ≫ hU.fromSpec).base y ∈ U :=
  (hU.isoSpec.inv.base ((branchι s).base y)).2

/-- The original branch equation has nonunit germ at the actual image of
every branch point under the original affine chart map. -/
theorem branch_point_germ_not_isUnit {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Γ(X, U)) (y : branchScheme s) :
    ¬IsUnit (X.presheaf.germ U (((branchι s) ≫ hU.fromSpec).base y)
      (branch_point_mem_open hU s y) s) := by
  intro hs
  have hbasic := (X.toRingedSpace.mem_basicOpen s
    (((branchι s) ≫ hU.fromSpec).base y) (branch_point_mem_open hU s y)).mpr hs
  have hpre : (branchι s).base y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s := hbasic
  rw [hU.fromSpec_preimage_basicOpen] at hpre
  exact (PrimeSpectrum.mem_basicOpen s ((branchι s).base y)).mp hpre
    (branch_point_mem_ideal s y)

end KltDP.Geometry.QuadraticCover

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover

/-- One actual reduced nonempty branch chart supplies the nonunit and
reduced-quotient inputs to the original cover's integrality proof. Only
the original coefficient's nonvanishing and base normality remain inputs
in addition to that geometric branch data. -/
theorem scheme_isIntegral_of_reduced_nonempty_branchChart
    {X : Scheme.{u}} [IsIntegral X] {ι : Type u}
    (D : QuadraticCoverAtlas.Data X ι) (hnormal : IsNormalScheme X)
    (i : ι) (y : branchScheme (D.sections i)) (hs : D.sections i ≠ 0)
    (hred : IsReduced (branchScheme (D.sections i))) : IsIntegral D.scheme := by
  letI : Nonempty (D.opens i) :=
    ⟨⟨((branchι (D.sections i)) ≫ (D.affine i).fromSpec).base y,
      branch_point_mem_open (D.affine i) (D.sections i) y⟩⟩
  letI : IsIntegrallyClosed Γ(X, D.opens i) :=
    isIntegrallyClosed_affineSections_of_isNormal X hnormal (D.affine i)
  letI : IsFractionRing Γ(X, D.opens i) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (D.opens i) (D.affine i)
  apply D.scheme_isIntegral_of_selected_chart_nonsquare i
  change ∀ x : X.functionField,
    x ^ 2 ≠ algebraMap Γ(X, D.opens i) X.functionField (D.sections i)
  exact nonsquare_of_reduced_branch_quotient (↥X.functionField) (D.sections i) hs
    (branch_point_not_isUnit (D.sections i) y)
    (branch_quotient_isReduced (D.sections i) hred)

end KltDP.Geometry.QuadraticCoverAtlas.Data
