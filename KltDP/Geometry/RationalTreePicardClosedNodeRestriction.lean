import KltDP.Geometry.RationalTreePicardClosedNodeField

/-!
# Original node-field coordinates respect component restriction

An original algebra restriction that carries both original component
ideals into their target ideals induces the original intersection-quotient
map. The ground-field equivalences derived from reduced one-point support
commute with this map: every source intersection class is an original
base scalar, and all the maps are homomorphisms over that same base field.

Consequently the original node characters and the base-field scalars of
restricted intersection units agree. The last theorem gives precisely
the branch-evaluation compatibility used by the earlier matching-module
restriction theorem. Naturality of the actual geometric component frames
under restriction is still a separate sheaf comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (k A B : Type u) [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
  (I J : Ideal A) (I' J' : Ideal B)
  (q : PrimeSpectrum A) (q' : PrimeSpectrum B)
  (hsupport : PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) = {q})
  (hsupport' : PrimeSpectrum.zeroLocus (I' ⊔ J' : Ideal B) = {q'})
  [IsReduced (A ⧸ I ⊔ J)] [IsReduced (B ⧸ I' ⊔ J')]
  (φ : A →ₐ[k] B) (hI : I ≤ I'.comap φ) (hJ : J ≤ J'.comap φ)

/-- Original component restrictions induce the original map on the
scheme-theoretic intersection quotients. -/
def closedNodeQuotientRestriction : (A ⧸ I ⊔ J) →ₐ[k] B ⧸ I' ⊔ J' :=
  Ideal.quotientMapₐ (I' ⊔ J') φ (sup_le
    (hI.trans (Ideal.comap_mono le_sup_left))
    (hJ.trans (Ideal.comap_mono le_sup_right)))

/-- Derived ground-field coordinates commute with the original restriction
map on the actual intersection quotients. -/
theorem reducedNodeFieldEquiv_restrict (x : A ⧸ I ⊔ J) :
    reducedNodeFieldEquiv B I' J' q' hsupport' k
        (closedNodeQuotientRestriction k A B I J I' J' φ hI hJ x) =
      reducedNodeFieldEquiv A I J q hsupport k x := by
  let e := reducedNodeFieldEquiv A I J q hsupport k
  let e' := reducedNodeFieldEquiv B I' J' q' hsupport' k
  let f := closedNodeQuotientRestriction k A B I J I' J' φ hI hJ
  change e' (f x) = e x
  obtain ⟨c, rfl⟩ := e.symm.surjective x
  have hc := e.symm.commutes c
  change e.symm c = algebraMap k (A ⧸ I ⊔ J) c at hc
  rw [hc, f.commutes, e'.commutes, e.commutes]

include hI hJ in
/-- The actual original node character evaluates an original restricted
function to the same base-field value. -/
theorem reducedNodeCharacter_restrict (a : A) :
    reducedNodeCharacter B I' J' q' hsupport' k (φ a) =
      reducedNodeCharacter A I J q hsupport k a :=
  reducedNodeFieldEquiv_restrict k A B I J I' J' q q' hsupport hsupport' φ hI hJ
    (Ideal.Quotient.mk (I ⊔ J) a)

/-- Restricting an actual intersection unit preserves its derived
ground-field scalar. This is the same scalar used in the component gauge. -/
theorem reducedNodeScalarUnit_restrict (g : (A ⧸ I ⊔ J)ˣ) :
    reducedNodeScalarUnit B I' J' q' hsupport' k
        (Units.map (closedNodeQuotientRestriction k A B I J I' J' φ hI hJ).toMonoidHom g) =
      reducedNodeScalarUnit A I J q hsupport k g := by
  apply Units.ext
  exact reducedNodeFieldEquiv_restrict k A B I J I' J' q q' hsupport hsupport' φ hI hJ g

section BranchEvaluation

/-- The original first-component evaluation factors through its original
quotient restriction to the node, then through the derived field map. -/
def reducedNodeBranchEvaluation : (A ⧸ I) →ₐ[k] k :=
  (reducedNodeFieldEquiv A I J q hsupport k).toAlgHom.comp
    { __ := Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)
      commutes' := fun _ => rfl }

include hJ in
/-- The evaluation compatibility required by branch matching is derived
from the original quotient restriction and the actual reduced node field. -/
theorem reducedNodeBranchEvaluation_restrict (x : A ⧸ I) :
    reducedNodeBranchEvaluation k B I' J' q' hsupport'
        (Ideal.quotientMapₐ I' φ hI x) =
      reducedNodeBranchEvaluation k A I J q hsupport x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact reducedNodeCharacter_restrict k A B I J I' J' q q' hsupport hsupport' φ hI hJ a

end BranchEvaluation

end KltDP.Geometry.RationalTreePicard
