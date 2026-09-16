import KltDP.Geometry.PrimeCurveIntersectionKernel
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.PrimeCurveIntersectionNumber

/-!
# Symmetry of the intersection number of two prime curves on a regular surface

On a regular projective surface over an algebraically closed field, a prime curve `C` has a Cartier
divisor `D_C` with `I(D_C) = vanishingIdeal C` (`PrimeCurveCartierVanishingIdeal`), and for a prime
curve `C'` with `C ⊄ Supp D_{C'}`, the
intersection number `C·D_{C'}` is the degree of `Z(vanishingIdeal C ⊔ I(D_{C'}))`
(`PrimeCurveIntersectionKernel`) `= Z(I(D_C) ⊔ I(D_{C'}))`, a symmetric expression:
`intersectionDegree_symm`, `intersectionNumber_symm`, exported as `f03_intersection_symmetric`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- `C·D_{C'}` is the degree of `Z(I(D_C) ⊔ I(D_{C'}))`. -/
theorem intersectionDegree_primeCurveCartier_eq (C C' : X.PrimeCurve)
    (hC : C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C')) :
    C.intersectionDegree (X.primeCurveCartier hregular C')
        (X.primeCurveCartier_hasRegularEquations hregular C') hC =
      idealSheafDataDegree X.toScheme
        (effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular C)
            (X.primeCurveCartier_hasRegularEquations hregular C) ⊔
          effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular C')
            (X.primeCurveCartier_hasRegularEquations hregular C'))
        X.structureMorphism := by
  rw [C.intersectionDegree_eq_idealSheafDataDegree, X.primeCurveCartier_idealData_eq_vanishingIdeal hregular C]

/-- **Symmetry** `C·D_{C'} = C'·D_C` of the scheme-theoretic intersection numbers of two prime curves
on a regular surface (each not contained in the support of the other's divisor). -/
theorem intersectionDegree_symm (C C' : X.PrimeCurve)
    (hC : C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C'))
    (hC' : C'.NotInSupport (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)) :
    C.intersectionDegree (X.primeCurveCartier hregular C')
        (X.primeCurveCartier_hasRegularEquations hregular C') hC =
      C'.intersectionDegree (X.primeCurveCartier hregular C)
        (X.primeCurveCartier_hasRegularEquations hregular C) hC' := by
  rw [X.intersectionDegree_primeCurveCartier_eq hregular C C' hC,
    X.intersectionDegree_primeCurveCartier_eq hregular C' C hC', sup_comm]

/-- **Symmetry** of the general intersection numbers `C·D_{C'} = C'·D_C`. -/
theorem intersectionNumber_symm (C C' : X.PrimeCurve)
    (hC : C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C'))
    (hC' : C'.NotInSupport (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)) :
    C.intersectionNumber (X.primeCurveCartier hregular C') =
      C'.intersectionNumber (X.primeCurveCartier hregular C) := by
  rw [C.intersectionNumber_eq_intersectionDegree _ _ hC,
    C'.intersectionNumber_eq_intersectionDegree _ _ hC',
    X.intersectionDegree_symm hregular C C' hC hC']

end KltDP.Geometry.NormalProjectiveSurface

namespace KltDP.Geometry

open KltDP.Geometry.NormalProjectiveSurface

/-- **F03, symmetry.** On a regular projective surface over an algebraically closed field, for prime
curves `C`, `C'` with `C ⊄ Supp D_{C'}` and `C' ⊄ Supp D_C`: (1) the kernel of `C ∩ D → X` is
`vanishingIdeal C ⊔ I(D)` for every effective `D` with `C ⊄ Supp D`; (2) `C·D_{C'} = C'·D_C` for the
scheme-theoretic numbers; (3) the same for the general `intersectionNumber`. Single universe `u`. -/
theorem f03_intersection_symmetric {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C C' : X.PrimeCurve)
    (hC : C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C'))
    (hC' : C'.NotInSupport (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)) :
    (∀ (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
        (hCD : C.NotInSupport D hD),
        (C.intersectionToSurface D hD hCD).ker =
          C.vanishingIdeal ⊔ effectiveCartierIdealDataOfRegularEquations X.toScheme D hD) ∧
    C.intersectionDegree (X.primeCurveCartier hregular C')
        (X.primeCurveCartier_hasRegularEquations hregular C') hC =
      C'.intersectionDegree (X.primeCurveCartier hregular C)
        (X.primeCurveCartier_hasRegularEquations hregular C) hC' ∧
    C.intersectionNumber (X.primeCurveCartier hregular C') =
      C'.intersectionNumber (X.primeCurveCartier hregular C) :=
  ⟨fun D hD hCD => C.intersectionToSurface_ker D hD hCD,
    X.intersectionDegree_symm hregular C C' hC hC',
    X.intersectionNumber_symm hregular C C' hC hC'⟩

/-- Universe check: the symmetry instantiates at a single universe `u`. -/
example {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C C' : X.PrimeCurve)
    (hC : C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C'))
    (hC' : C'.NotInSupport (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)) :
    C.intersectionNumber (X.primeCurveCartier hregular C') =
      C'.intersectionNumber (X.primeCurveCartier hregular C) :=
  (f03_intersection_symmetric X hregular C C' hC hC').2.2

end KltDP.Geometry
