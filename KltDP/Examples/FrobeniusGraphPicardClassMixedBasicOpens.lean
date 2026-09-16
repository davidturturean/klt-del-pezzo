import KltDP.Examples.FrobeniusGraphPicardClassMixedOverlap

/-!
# Two actual basic opens covering each mixed plane

The sections are the original polynomial coordinates and 1-u^p*v.
The identity 1=(1-u^p*v)+u^p*v proves that D(v) and D(1-u^p*v)
cover the entire plane, including the mixed point missing from the
diagonal charts. On the second basic open the displayed equation is an
actual regular unit by the existing structure-sheaf restriction theorem.

The comparison of its vanishing with the original graph still requires
transporting the original diagonal equation on D(v). It is not assumed
in this cover or unit construction. The cover works also for p=0.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassMixedBasicOpens

open FrobeniusBlowupContact
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassPowerCharts
open FrobeniusGraphPicardClassMixedOverlap

variable {k : Type u} [Field k]

def innerSection : Γ(Spec (CommRingCat.of (planeRing k)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord

def outerSection : Γ(Spec (CommRingCat.of (planeRing k)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord

/-- The mixed-chart polynomial, interpreted as an actual original plane section. -/
def mixedEquation (p : ℕ) : Γ(Spec (CommRingCat.of (planeRing k)), ⊤) :=
  1 - innerSection ^ p * outerSection

theorem mixedEquation_polynomial (p : ℕ) :
    mixedEquation (k := k) p =
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (1 - uCoord ^ p * vCoord) := by
  simp only [mixedEquation, innerSection, outerSection, map_sub, map_one, map_mul, map_pow]

/-- This elementary identity gives the full mixed-plane cover without p>0. -/
theorem mixedBasicOpens_cover (p : ℕ) :
    (Spec (CommRingCat.of (planeRing k))).basicOpen (mixedEquation p) ⊔
      (Spec (CommRingCat.of (planeRing k))).basicOpen outerSection = ⊤ := by
  let X := Spec (CommRingCat.of (planeRing k))
  have hs : mixedEquation p + innerSection ^ p * outerSection = (1 : Γ(X, ⊤)) :=
    sub_add_cancel _ _
  have h := X.basicOpen_add_le (mixedEquation p) (innerSection ^ p * outerSection)
  rw [hs, X.basicOpen_one, X.basicOpen_mul] at h
  exact top_unique (h.trans (sup_le_sup_left inf_le_right _))

/-- The first open is exactly the previously identified original diagonal overlap. -/
theorem mixedChart_preimage_diagonal_section (i : Fin 2) :
    productChart (k := k) i (otherIndex i) ⁻¹ᵁ (productChart i i).opensRange =
      (Spec (CommRingCat.of (planeRing k))).basicOpen outerSection := by
  rw [mixedChart_preimage_diagonal, outerSection, basicOpen_eq_of_affine]

/-- The displayed mixed equation is a regular unit on its own actual basic open. -/
theorem mixedEquation_restrict_isUnit (p : ℕ) :
    IsUnit ((Spec (CommRingCat.of (planeRing k))).presheaf.map
      (homOfLE ((Spec (CommRingCat.of (planeRing k))).basicOpen_le (mixedEquation p))).op
        (mixedEquation p)) :=
  (Spec (CommRingCat.of (planeRing k))).toRingedSpace.isUnit_res_basicOpen (mixedEquation p)

/-- This is an actual unit of the original open's section ring. -/
def mixedEquationOpenUnit (p : ℕ) :
    Γ(Spec (CommRingCat.of (planeRing k)),
      (Spec (CommRingCat.of (planeRing k))).basicOpen (mixedEquation p))ˣ :=
  (mixedEquation_restrict_isUnit (k := k) p).unit

theorem mixedEquationOpenUnit_val (p : ℕ) :
    (mixedEquationOpenUnit (k := k) p : Γ(Spec (CommRingCat.of (planeRing k)),
      (Spec (CommRingCat.of (planeRing k))).basicOpen (mixedEquation p))) =
        (Spec (CommRingCat.of (planeRing k))).presheaf.map
          (homOfLE ((Spec (CommRingCat.of (planeRing k))).basicOpen_le (mixedEquation p))).op
            (mixedEquation p) :=
  (mixedEquation_restrict_isUnit (k := k) p).unit_spec

end KltDP.Examples.FrobeniusGraphPicardClassMixedBasicOpens
