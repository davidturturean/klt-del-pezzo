import KltDP.Manuscript.S07.BisectionRamification
import KltDP.Literature.Hartshorne.HurwitzDegreeTwoInstance

/-!
# Discharging the Riemann–Hurwitz input of Lemma 7.2

`RiemannHurwitzDegreeTwo p F g B` (the explicit hypothesis of `bisectionRamification_count`) follows
from the admitted instance `hurwitz_degreeTwo_projectiveLine_instance` together with
`bisection_pullback_degree` (`deg(g|_B) = B · F`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript.S07

variable {k : Type u} [Field k] [IsAlgClosed k] {R : ResolutionDatum k}

/-- The Riemann–Hurwitz count for a bisection, from the admitted Hurwitz instance. -/
theorem riemannHurwitzDegreeTwo_of_instance (p : ℕ) [CharP k p] (hp : 2 < p)
    (F : CartierDivisor R.S.toScheme) (g : R.S.toScheme ⟶ projectiveSpace k 1)
    (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
    (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
      cartierDivisorModule R.S.toScheme F)
    (B : R.S.PrimeCurve) : RiemannHurwitzDegreeTwo p F g B := by
  intro hiso hFB _hp2 T hT
  obtain ⟨eB, heB⟩ := hiso
  have hdeg : B.lineDegree (pullbackInvertibleSheaf (B.inclusion ≫ g)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)) = 2 := by
    rw [bisection_pullback_degree F g e B]; exact hFB
  exact KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance p hp R.S B eB heB g hg
    hdeg T hT

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.riemannHurwitzDegreeTwo_of_instance
