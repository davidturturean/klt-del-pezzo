import KltDP.Geometry.RationalTreePicardClosedNodeFrames
import KltDP.Compatibility.ClosedAlgebraResidue
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The ground field of an actual reduced one-point intersection

For the original closed intersection A/(I+J), reducedness and singleton
support imply I+J is the actual maximal ideal of that point. This ideal
equality is proved from the pinned vanishing-ideal/radical correspondence.
The existing closed-residue-field theorem then constructs the original
quotient's base-field equivalence over an algebraically closed field.

The resulting intersection unit has an actual base-field scalar and hence
an explicit lift through the original base algebra map. No residue-field
isomorphism or maximal-ideal equality is supplied as a hypothesis. The
nodal-curve application must still establish the stated reducedness and
singleton-support conditions on its original closed-component charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (A : Type u) [CommRing A] (I J : Ideal A) (q : PrimeSpectrum A)
  (hsupport : PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) = {q})

include hsupport in
/-- The point supporting the original closed intersection is closed,
so its original prime ideal is maximal. -/
theorem reducedNodePoint_isMaximal : q.asIdeal.IsMaximal := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
  rw [← hsupport]
  exact PrimeSpectrum.isClosed_zeroLocus ((I ⊔ J : Ideal A) : Set A)

include hsupport in
/-- Reducedness and the original one-point support identify the actual
intersection ideal with the original point ideal. -/
theorem reducedNodeIdeal_eq [IsReduced (A ⧸ I ⊔ J)] : I ⊔ J = q.asIdeal := by
  have hrad : (I ⊔ J).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced (I ⊔ J)).mpr inferInstance
  calc
    I ⊔ J = (I ⊔ J).radical := hrad.radical.symm
    _ = PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A)) :=
      (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical (I ⊔ J)).symm
    _ = q.asIdeal := by rw [hsupport, PrimeSpectrum.vanishingIdeal_singleton]

section BaseField

variable (k : Type u) [Field k] [IsAlgClosed k] [Algebra k A] [Algebra.FiniteType k A]

/-- The original quotient at a closed point is the ground field. Its
inverse is the original base algebra map followed by the quotient map. -/
def closedPointQuotientFieldEquiv (p : Ideal A) [p.IsMaximal] : (A ⧸ p) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k
    (KltDP.Compatibility.closedPointCharacter_ker k p).symm).trans
      (Ideal.quotientKerAlgEquivOfRightInverse
        (f := KltDP.Compatibility.closedPointCharacter k p)
        (g := algebraMap k A) (fun c =>
          (KltDP.Compatibility.closedPointCharacter k p).commutes c))

/-- The quotient equivalence evaluates by the existing actual residue
character, on the original quotient representative. -/
theorem closedPointQuotientFieldEquiv_mk (p : Ideal A) [p.IsMaximal] (a : A) :
    closedPointQuotientFieldEquiv A k p (Ideal.Quotient.mk p a) =
      KltDP.Compatibility.closedPointCharacter k p a := rfl

/-- The original reduced intersection quotient is the actual ground field,
derived from its support and finite-type residue field. -/
def reducedNodeFieldEquiv [IsReduced (A ⧸ I ⊔ J)] : (A ⧸ I ⊔ J) ≃ₐ[k] k := by
  letI := reducedNodePoint_isMaximal A I J q hsupport
  exact (Ideal.quotientEquivAlgOfEq k (reducedNodeIdeal_eq A I J q hsupport)).trans
    (closedPointQuotientFieldEquiv A k q.asIdeal)

/-- The original node evaluation, retaining the original quotient map. -/
def reducedNodeCharacter [IsReduced (A ⧸ I ⊔ J)] : A →ₐ[k] k :=
  (reducedNodeFieldEquiv A I J q hsupport k).toAlgHom.comp
    (Ideal.Quotient.mkₐ k (I ⊔ J))

/-- An original intersection unit determines its actual base-field scalar. -/
def reducedNodeScalarUnit [IsReduced (A ⧸ I ⊔ J)] (g : (A ⧸ I ⊔ J)ˣ) : kˣ :=
  Units.map (reducedNodeFieldEquiv A I J q hsupport k).toAlgHom.toMonoidHom g

/-- The scalar lifts back to the SAME original intersection unit through
the original base algebra map; liftability is proved, not assumed. -/
theorem reducedNodeScalarUnit_algebraMap [IsReduced (A ⧸ I ⊔ J)]
    (g : (A ⧸ I ⊔ J)ˣ) :
    algebraMap k (A ⧸ I ⊔ J) (reducedNodeScalarUnit A I J q hsupport k g : k) = g := by
  let e := reducedNodeFieldEquiv A I J q hsupport k
  change algebraMap k (A ⧸ I ⊔ J) (e (g : A ⧸ I ⊔ J)) = g
  exact (e.symm.commutes (e (g : A ⧸ I ⊔ J))).symm.trans
    (e.symm_apply_apply (g : A ⧸ I ⊔ J))

end BaseField

end KltDP.Geometry.RationalTreePicard
