/-
The finite-cover assembly follows the AlgebraicJacobian contributors'
WeilDivisor.lean (copyright 2026), released under Apache 2.0 and frozen at
frenzymath/Algebraic-Geometry commit 9223d85c786394721963a9d642b08d066b72a594.
The local proof reuses this project's actual height-one-prime valuation
support and transport theorems, rather than the external Ring.ordFrac.
-/
import KltDP.Geometry.DivisorOrderTransport
import KltDP.Geometry.NormalAffineSections
import KltDP.Geometry.PrimeCurveOrder
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.Data.Set.Finite.Lattice

/-!
# Actual global principal divisors on normal projective surfaces

A curve whose generic point lies in an affine open determines an actual
height-one prime of its section ring. This assignment is injective on
these curves, and the global rational-function order equals the existing
affine prime-localization order. Consequently each affine open meets only
finitely many generic points with nonzero order.

The actual surface is quasi-compact by its already proved Noetherian
topology. The pinned finite affine subcover therefore turns the local
bounds into finite support on the original prime-curve carrier. The
principal divisor is then the existing `Finsupp` with those actual orders
as coefficients. Multiplication and inversion of rational functions give
addition and negation of these actual divisors.

No finiteness conclusion or order comparison is assumed. The only input
rational functions are units of the original function field. This module
does not construct Cartier divisors, divisor classes, or intersections.

See `docs/PRINCIPAL_DIVISOR_FOUNDATION.md` for the source correspondence
and the precise remaining geometry obligations.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k]

namespace PrimeCurve

variable {X : NormalProjectiveSurface k}

/-- The actual affine height-one prime corresponding to the generic
point of a curve in an affine neighborhood. Its height is proved. -/
def affineHeightOnePrime (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (hmem : C.genericPoint ∈ U) :
    RingTheory.AffineHeightOnePrime Γ(X.toScheme, U) :=
  ⟨hU.primeIdealOf ⟨C.genericPoint, hmem⟩, C.primeIdealOf_height_eq_one hU hmem⟩

/-- Distinct actual curves with generic points in one affine chart give
distinct actual height-one primes of its section ring. -/
theorem affineHeightOnePrime_injective {U : X.toScheme.Opens} (hU : IsAffineOpen U) :
    Function.Injective (fun C : {C : X.PrimeCurve // C.genericPoint ∈ U} =>
      C.1.affineHeightOnePrime hU C.2) := by
  intro C D h
  apply Subtype.ext
  apply genericPoint_injective
  have hprime : hU.primeIdealOf ⟨C.1.genericPoint, C.2⟩ =
      hU.primeIdealOf ⟨D.1.genericPoint, D.2⟩ :=
    congrArg (fun p : RingTheory.AffineHeightOnePrime Γ(X.toScheme, U) => p.1) h
  have hpoints := congrArg (fun p => hU.fromSpec.base p) hprime
  simpa only [hU.fromSpec_primeIdealOf] using hpoints

/-- The global order along an actual curve agrees exactly with the
affine prime-localization order in every affine neighborhood of its
generic point. All affine-ring hypotheses are derived from the surface. -/
theorem order_eq_affinePrincipalOrder (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (hmem : C.genericPoint ∈ U)
    (f : X.toScheme.functionFieldˣ) :
    letI : Nonempty U := ⟨⟨C.genericPoint, hmem⟩⟩
    letI : IsNoetherianRing Γ(X.toScheme, U) := X.affineSections_isNoetherianRing hU
    letI : IsIntegrallyClosed Γ(X.toScheme, U) := X.affineSections_isIntegrallyClosed hU
    letI : IsFractionRing Γ(X.toScheme, U) X.toScheme.functionField :=
      functionField_isFractionRing_of_isAffineOpen X.toScheme U hU
    C.order f = RingTheory.affinePrincipalOrder Γ(X.toScheme, U) X.toScheme.functionField
      (C.affineHeightOnePrime hU hmem) f := by
  letI : Nonempty U := ⟨⟨C.genericPoint, hmem⟩⟩
  letI : IsNoetherianRing Γ(X.toScheme, U) := X.affineSections_isNoetherianRing hU
  letI : IsIntegrallyClosed Γ(X.toScheme, U) := X.affineSections_isIntegrallyClosed hU
  letI : IsFractionRing Γ(X.toScheme, U) X.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.toScheme U hU
  exact (affinePrincipalOrder_eq_stalkDivisorOrder X.toScheme U hU
    ⟨C.genericPoint, hmem⟩ (C.primeIdealOf_height_eq_one hU hmem) f).symm

end PrimeCurve

variable (X : NormalProjectiveSurface k)

/-- On each actual affine open, only finitely many curves with generic
point in that open have a nonzero order of the given rational function.
The empty affine open is included without a nonemptiness assumption. -/
theorem finite_order_support_on_affine {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (f : X.toScheme.functionFieldˣ) :
    {C : X.PrimeCurve | C.genericPoint ∈ U ∧ C.order f ≠ 0}.Finite := by
  classical
  by_cases hUe : Nonempty U
  · letI : Nonempty U := hUe
    letI : IsNoetherianRing Γ(X.toScheme, U) := X.affineSections_isNoetherianRing hU
    letI : IsIntegrallyClosed Γ(X.toScheme, U) := X.affineSections_isIntegrallyClosed hU
    letI : IsFractionRing Γ(X.toScheme, U) X.toScheme.functionField :=
      functionField_isFractionRing_of_isAffineOpen X.toScheme U hU
    let φ : {C : X.PrimeCurve // C.genericPoint ∈ U} →
        RingTheory.AffineHeightOnePrime Γ(X.toScheme, U) :=
      fun C => C.1.affineHeightOnePrime hU C.2
    have hφ : Function.Injective φ := PrimeCurve.affineHeightOnePrime_injective hU
    have hpre :
        (φ ⁻¹' Function.support (fun p =>
          RingTheory.affinePrincipalOrder Γ(X.toScheme, U) X.toScheme.functionField p f)).Finite :=
      (RingTheory.affinePrincipalOrder_finite_support Γ(X.toScheme, U)
        X.toScheme.functionField f).preimage (Set.injOn_of_injective hφ)
    have himage := hpre.image
      (fun C : {C : X.PrimeCurve // C.genericPoint ∈ U} => C.1)
    refine himage.subset ?_
    intro C hC
    refine ⟨⟨C, hC.1⟩, ?_, rfl⟩
    change RingTheory.affinePrincipalOrder Γ(X.toScheme, U) X.toScheme.functionField
      (C.affineHeightOnePrime hU hC.1) f ≠ 0
    rw [← C.order_eq_affinePrincipalOrder hU hC.1 f]
    exact hC.2
  · refine Set.finite_empty.subset ?_
    intro C hC
    exact (hUe ⟨⟨C.genericPoint, hC.1⟩⟩).elim

/-- The actual global order function on the original prime curves has
finite support. The finite affine cover is derived from the surface's
Noetherian topology, and every affine support bound is already proved. -/
theorem order_finite_support (f : X.toScheme.functionFieldˣ) :
    (Function.support (fun C : X.PrimeCurve => C.order f)).Finite := by
  let 𝒰 := X.toScheme.affineCover.finiteSubcover
  haveI (i : 𝒰.J) : IsAffine (𝒰.obj i) :=
    Scheme.isAffine_affineCover X.toScheme _
  refine (Set.finite_iUnion (fun i : 𝒰.J =>
    X.finite_order_support_on_affine (isAffineOpen_opensRange (𝒰.map i)) f)).subset ?_
  intro C hC
  exact Set.mem_iUnion.mpr ⟨𝒰.f C.genericPoint, 𝒰.covers C.genericPoint, hC⟩

/-- The actual principal Weil divisor of a nonzero rational function.
Its coefficients are the proved DVR orders at the original curve stalks;
the finite-support witness is derived, rather than supplied by the caller. -/
def principalDivisor (f : X.toScheme.functionFieldˣ) : X.WeilDivisor :=
  Finsupp.ofSupportFinite (fun C => C.order f) (X.order_finite_support f)

@[simp]
theorem principalDivisor_apply (f : X.toScheme.functionFieldˣ) (C : X.PrimeCurve) :
    X.principalDivisor f C = C.order f := rfl

/-- The principal-divisor map is an additive homomorphism from the
multiplicative group of actual nonzero rational functions. -/
def principalDivisorHom : Additive X.toScheme.functionFieldˣ →+ X.WeilDivisor where
  toFun f := X.principalDivisor f.toMul
  map_zero' := by
    apply Finsupp.ext
    intro C
    exact C.order_one
  map_add' f g := by
    apply Finsupp.ext
    intro C
    exact C.order_mul f.toMul g.toMul

@[simp]
theorem principalDivisorHom_apply (f : X.toScheme.functionFieldˣ) :
    X.principalDivisorHom (Additive.ofMul f) = X.principalDivisor f := rfl

@[simp]
theorem principalDivisor_one : X.principalDivisor 1 = 0 :=
  X.principalDivisorHom.map_zero

theorem principalDivisor_mul (f g : X.toScheme.functionFieldˣ) :
    X.principalDivisor (f * g) = X.principalDivisor f + X.principalDivisor g :=
  X.principalDivisorHom.map_add (Additive.ofMul f) (Additive.ofMul g)

@[simp]
theorem principalDivisor_inv (f : X.toScheme.functionFieldˣ) :
    X.principalDivisor f⁻¹ = -X.principalDivisor f :=
  X.principalDivisorHom.map_neg (Additive.ofMul f)

/-- The finite component support is exactly the set of curves with
nonzero actual rational-function order. -/
@[simp]
theorem mem_principalDivisor_support (f : X.toScheme.functionFieldˣ) (C : X.PrimeCurve) :
    C ∈ (X.principalDivisor f).support ↔ C.order f ≠ 0 :=
  Finsupp.mem_support_iff

/-- The geometric support is a closed subset of the original surface.
This is a finite union of curves, not a claim of finitely many points. -/
theorem principalDivisor_geometricSupport_isClosed (f : X.toScheme.functionFieldˣ) :
    IsClosed (divisorSupport (X.principalDivisor f)) :=
  divisorSupport_isClosed (X.principalDivisor f)

end KltDP.Geometry.NormalProjectiveSurface
