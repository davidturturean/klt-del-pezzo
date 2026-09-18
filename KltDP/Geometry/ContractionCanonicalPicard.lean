import KltDP.Geometry.ContractionCanonicalSquare
import KltDP.Geometry.ContractionPicardSplitting

/-! The actual normalized Picard decomposition of any actual canonical
Cartier representative. The compatible divisor is constructed internally;
its exact signed formula supplies the positive exceptional coordinate. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve} (hb : IsContraction S T b E)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hminus : IsMinusOneCurve hS E)

include hb hminus

/-- The original canonical class is the original target pullback times
the class of the original exceptional prime. No compatibility is assumed. -/
theorem canonical_picard_eq_pullback_mul_exceptional
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2) :
    cartierPicardClass S.toScheme KS =
      schemePicardPullbackHom b (cartierPicardClass T.toScheme KT) *
        cartierPicardClass S.toScheme (S.primeCurveCartier hS E) := by
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hb.regular
  let hbir := (isBirational_iff_isBirationalScheme b).mp hb.birational
  obtain ⟨K, ⟨eK⟩, hpush⟩ := IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
    S T b hb.over_base hbir (T.cartierToWeilHom KT) (IsCanonicalWeilDivisor.of_cartier T KT eKT)
  have hclass : cartierPicardClass S.toScheme KS = cartierPicardClass S.toScheme K :=
    SchemeKernelIdealIsoTransport.toPic_eq_of_iso
      (cartierDivisorInvertibleSheaf S.toScheme KS)
      (cartierDivisorInvertibleSheaf S.toScheme K) (eKS ≪≫ eK.symm)
  rw [hclass, hb.compatible_canonical_difference hS hminus KT K eK hpush,
    cartierPicardClass_add, ← DominantCartierPullback.cartierPicardClass_pullback b KT]

/-- In the original normalized splitting the canonical class has actual
target canonical component and exceptional coordinate one. -/
theorem canonical_picardDecomposition
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2) :
    hb.picardDecomposition hS hminus (cartierPicardClass S.toScheme KS) =
      (cartierPicardClass T.toScheme KT, Multiplicative.ofAdd (1 : ℤ)) := by
  rw [hb.canonical_picard_eq_pullback_mul_exceptional hS hminus KS KT eKS eKT,
    map_mul, hb.picardDecomposition_pullback hS hminus,
    hb.picardDecomposition_exceptional hS hminus]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.canonical_picardDecomposition
#print axioms KltDP.Geometry.IsContraction.canonical_picardDecomposition
