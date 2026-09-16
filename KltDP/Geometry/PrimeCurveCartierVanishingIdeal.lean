import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.RegularStalkUFD
import KltDP.Geometry.EffectiveWeilCartierEquations
import KltDP.Geometry.CartierIdealReduced
import KltDP.Geometry.CartierIdealSupport
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# The Cartier divisor of a prime curve on a regular surface cuts out the curve

For a prime curve `C` on a regular projective surface over an algebraically closed field, the
Cartier divisor `D_C` corresponding to the Weil divisor `1·C` (`primeCurveCartier`) has regular
local equations, and its divisor ideal sheaf `I(D_C)` (`effectiveCartierIdealDataOfRegularEquations`)
is the vanishing ideal sheaf of `C`: its support is `C` (accepted germ-unit criterion
`regularCartierEquation_germ_isUnit_iff` with the support criterion `mem_support_iff_not_isUnit_germ`)
and its sections are radical ideals (accepted `cartierSectionIdeal_isRadical`, coefficients `≤ 1`),
so `I(D_C) = I(D_C).radical = vanishingIdeal I(D_C).support = vanishingIdeal C`
(`primeCurveCartier_idealData_eq_vanishingIdeal`). This identifies the zero scheme `Z(D_C)` with the
reduced curve `C` as ideal-sheaf data — the first ingredient of the symmetric identification
`Z(D_C) ∩ Z(D) ≅ C ∩ D`. No square-root datum `(L, e)` is needed (unlike the accepted
`effectiveCartierIdealData_eq_vanishingIdeal`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section SingleCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-- The Weil divisor `1·C` is effective. -/
theorem single_one_effective (C : X.PrimeCurve) :
    EffectiveDivisor (Finsupp.single C (1 : ℤ)) := by
  intro C'
  by_cases h : C = C'
  · subst h
    exact le_of_le_of_eq zero_le_one Finsupp.single_eq_same.symm
  · exact le_of_eq (Finsupp.single_eq_of_ne h).symm

/-- The Weil divisor `1·C` has all coefficients `≤ 1`. -/
theorem single_one_le_one (C C' : X.PrimeCurve) :
    (Finsupp.single C (1 : ℤ)) C' ≤ 1 := by
  by_cases h : C = C'
  · subst h
    exact le_of_eq Finsupp.single_eq_same
  · exact le_of_eq_of_le (Finsupp.single_eq_of_ne h) zero_le_one

end SingleCurve

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The Cartier divisor of a prime curve on a regular surface: the Cartier divisor whose Weil
divisor is `1·C`. -/
def primeCurveCartier (C : X.PrimeCurve) : CartierDivisor X.toScheme :=
  (X.regularCartierWeilEquiv hregular).symm (Finsupp.single C 1)

/-- The Weil divisor of `D_C` is `1·C`. -/
theorem cartierToWeilHom_primeCurveCartier (C : X.PrimeCurve) :
    X.cartierToWeilHom (X.primeCurveCartier hregular C) = Finsupp.single C 1 :=
  (X.regularCartierWeilEquiv_apply hregular _).symm.trans
    ((X.regularCartierWeilEquiv hregular).apply_symm_apply _)

/-- `D_C` has regular local equations (it is effective). -/
theorem primeCurveCartier_hasRegularEquations (C : X.PrimeCurve) :
    HasRegularCartierEquations X.toScheme (X.primeCurveCartier hregular C) := by
  letI := X.stalks_uniqueFactorizationMonoid_of_regular hregular
  refine X.hasRegularCartierEquations_of_effective_weil _ ?_
  rw [cartierToWeilHom_primeCurveCartier]
  exact single_one_effective C

/-- **The divisor ideal sheaf of `D_C` has support `C`.** -/
theorem primeCurveCartier_support (C : X.PrimeCurve) :
    ((effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)).support : Set X.toScheme) = C := by
  letI := X.stalks_uniqueFactorizationMonoid_of_regular hregular
  ext x
  obtain ⟨c, hxc⟩ := X.primeCurveCartier_hasRegularEquations hregular C x
  simp only [SetLike.mem_coe]
  rw [PrimeCurve.mem_support_iff_not_isUnit_germ (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C) c x hxc,
    X.regularCartierEquation_germ_isUnit_iff _ c ⟨x, hxc⟩, cartierToWeilHom_primeCurveCartier]
  constructor
  · intro h
    by_contra hx
    exact h fun C' hxC' => Finsupp.single_eq_of_ne fun hCC' => hx (by rw [hCC']; exact hxC')
  · intro hx h
    have h1 := h C hx
    rw [Finsupp.single_eq_same] at h1
    exact one_ne_zero h1

/-- **The divisor ideal sheaf of `D_C` is radical on every affine open.** -/
theorem primeCurveCartier_ideal_isRadical (C : X.PrimeCurve) (U : X.toScheme.affineOpens) :
    ((effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)).ideal U).IsRadical := by
  letI := X.stalks_uniqueFactorizationMonoid_of_regular hregular
  rw [effectiveCartierIdealDataOfRegularEquations_ideal]
  refine X.cartierSectionIdeal_isRadical _ ?_ ?_ U.1
  · rw [cartierToWeilHom_primeCurveCartier]
    exact single_one_effective C
  · rw [cartierToWeilHom_primeCurveCartier]
    exact single_one_le_one C

/-- **`I(D_C) = vanishingIdeal C`**: the divisor ideal sheaf of the Cartier divisor of a prime curve
on a regular surface is the vanishing ideal sheaf of the curve. -/
theorem primeCurveCartier_idealData_eq_vanishingIdeal (C : X.PrimeCurve) :
    effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C) = C.vanishingIdeal := by
  set I := effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular C)
    (X.primeCurveCartier_hasRegularEquations hregular C)
  have hrad : I.radical = I := by
    ext U : 2
    show (I.ideal U).radical = I.ideal U
    exact Ideal.radical_eq_iff.mpr (X.primeCurveCartier_ideal_isRadical hregular C U)
  have hsupp : I.support = C.closedSubset :=
    Closeds.ext (X.primeCurveCartier_support hregular C)
  calc I = I.radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal I.support :=
        (Scheme.IdealSheafData.vanishingIdeal_support (I := I)).symm
    _ = Scheme.IdealSheafData.vanishingIdeal C.closedSubset := by rw [hsupp]
    _ = C.vanishingIdeal := rfl

end KltDP.Geometry.NormalProjectiveSurface
