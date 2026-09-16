import KltDP.Geometry.CartierExtensionAcrossPoint
import KltDP.Geometry.WeilClassPicard
import KltDP.Geometry.PrimeCurveStalkCoordinates

/-!
# Picard classes trivial off a prime curve: `ker (Pic X → Pic (X ∖ E)) = ℤ · [O_X(E)]`

BRIEF32, task 1 (F09 step (iii)). `X` is a normal projective surface over an algebraically closed
field with factorial stalks, `E` a prime curve of `X` and `V` the complement of `E`. A Picard class
that restricts trivially to `V` is the class of a Cartier divisor whose Weil divisor is supported on
`E` — hence of `n · E` — and conversely `[O_X(E)]` restricts trivially to `V`.

* `eq_of_genericPoint_mem`: a prime curve whose generic point lies on `E` **is** `E` (two distinct
  prime curves would give a strict chain of height-one primes in one affine chart, by the accepted
  `affineHeightOnePrime_le` and `primeIdealOf_height_eq_one`); hence
  `genericPoint_mem_complementOpen_iff : C.genericPoint ∈ X ∖ E ↔ C ≠ E`, which is the hypothesis
  `hV` of the main theorems, and `complementOpen` is nonempty (it contains the generic point of `X`).
* `restrictedCoefficient_cartierRestriction`: the coefficient along `C` built in
  `Geometry/OpenCartierWeil` from the restriction of a Cartier divisor of `X` is the accepted
  `cartierToWeilHom` coefficient, whenever `C.genericPoint ∈ V`; with
  `eq_zero_of_restrictedWeilHom_eq_zero` (from BRIEF31's `cartierRestrictionHom_extension`) this
  identifies the Weil divisors that restrict to zero.
* `primeCurveClass E := weilPicardClass (single E 1)` (`= [O_X(E)]`; `[O_X(−E)]` is its inverse),
  `primeCurveClass_mem_ker`, and **`mem_ker_iff : c ∈ ker (Pic X → Pic V) ↔ ∃ n : ℤ, c = [O_X(E)]^n`**.
* `InfiniteOrder c : Prop := ∀ n : ℤ, c ^ n = 1 → n = 0` (a named hypothesis, never an axiom) and
  **`kernelEquivInt : ker (Pic X → Pic V) ≃* Multiplicative ℤ`** under it.

The infinite-order hypothesis is discharged from `E · E = −1` in
`Geometry/ExceptionalKernelInfiniteOrder`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.PrimeCurveComplementKernel

open KltDP.Geometry.OpenImmersionRational KltDP.Geometry.OpenCartierWeil
open KltDP.Geometry.CartierExtension

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}

/-! ## A prime curve through the generic point of a prime curve is that curve -/

/-- **Two prime curves with `C.genericPoint ∈ E` coincide.** Otherwise their affine primes in a
common chart form a strict chain, so the lower one has height at most `0`, contradicting the
accepted `primeIdealOf_height_eq_one`. -/
theorem eq_of_genericPoint_mem (C E : X.PrimeCurve)
    (h : C.genericPoint ∈ (E : Set X.toScheme)) : C = E := by
  by_contra hne
  let U : X.toScheme.Opens := (X.toScheme.affineCover.map C.genericPoint).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.toScheme.affineCover.map C.genericPoint)
  have hxU : C.genericPoint ∈ U := X.toScheme.affineCover.covers C.genericPoint
  letI : Nonempty U := ⟨⟨C.genericPoint, hxU⟩⟩
  have hle : (E.affineHeightOnePrime hU
        (E.genericPoint_mem_of_mem (⟨C.genericPoint, hxU⟩ : U) h)).1.asIdeal ≤
      (hU.primeIdealOf (⟨C.genericPoint, hxU⟩ : U)).asIdeal :=
    E.affineHeightOnePrime_le hU (⟨C.genericPoint, hxU⟩ : U) h
  have hne' : (E.affineHeightOnePrime hU
      (E.genericPoint_mem_of_mem (⟨C.genericPoint, hxU⟩ : U) h)).1 ≠
      hU.primeIdealOf (⟨C.genericPoint, hxU⟩ : U) := by
    intro heq
    apply hne
    apply NormalProjectiveSurface.PrimeCurve.genericPoint_injective
    have heq' : hU.primeIdealOf
          (⟨E.genericPoint, E.genericPoint_mem_of_mem (⟨C.genericPoint, hxU⟩ : U) h⟩ : U) =
        hU.primeIdealOf (⟨C.genericPoint, hxU⟩ : U) := heq
    have hpoints := congrArg (fun p => hU.fromSpec.base p) heq'
    simpa only [hU.fromSpec_primeIdealOf] using hpoints.symm
  have hlt : (E.affineHeightOnePrime hU
      (E.genericPoint_mem_of_mem (⟨C.genericPoint, hxU⟩ : U) h)).1 <
      hU.primeIdealOf (⟨C.genericPoint, hxU⟩ : U) := lt_of_le_of_ne hle hne'
  have hE1 : Order.height (E.affineHeightOnePrime hU
      (E.genericPoint_mem_of_mem (⟨C.genericPoint, hxU⟩ : U) h)).1 = 1 := by
    have hh := E.primeIdealOf_height_eq_one hU
      (E.genericPoint_mem_of_mem (⟨C.genericPoint, hxU⟩ : U) h)
    rwa [Ideal.height_eq_primeHeight] at hh
  have hC1 : Order.height (hU.primeIdealOf (⟨C.genericPoint, hxU⟩ : U)) = 1 := by
    have hh := C.primeIdealOf_height_eq_one hU hxU
    rwa [Ideal.height_eq_primeHeight] at hh
  have hchain := Order.height_add_one_le hlt
  rw [hE1, hC1] at hchain
  exact absurd hchain (by decide)

variable (E : X.PrimeCurve)

/-- The complement of a prime curve, as an open subscheme. -/
def complementOpen : X.toScheme.Opens :=
  ⟨((E : Set X.toScheme))ᶜ, E.isClosed.isOpen_compl⟩

theorem mem_complementOpen_iff (x : X.toScheme) :
    x ∈ complementOpen E ↔ x ∉ (E : Set X.toScheme) := Iff.rfl

/-- The generic point of the surface is not on a prime curve. -/
theorem genericPoint_not_mem : _root_.genericPoint X.toScheme ∉ (E : Set X.toScheme) := by
  intro hmem
  apply E.ne_univ
  have h1 : closure ({_root_.genericPoint X.toScheme} : Set X.toScheme) ⊆
      (E : Set X.toScheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) E.isClosed
  rw [genericPoint_closure] at h1
  exact Set.eq_univ_of_univ_subset h1

instance complementOpen_nonempty : Nonempty (complementOpen E) :=
  ⟨⟨_root_.genericPoint X.toScheme, genericPoint_not_mem E⟩⟩

instance complementOpen_nonempty' : Nonempty (complementOpen E).toScheme :=
  ⟨Classical.choice (complementOpen_nonempty E)⟩

/-- **The curves meeting the complement of `E` are exactly the curves other than `E`.** -/
theorem genericPoint_mem_complementOpen_iff (C : X.PrimeCurve) :
    C.genericPoint ∈ complementOpen E ↔ C ≠ E := by
  constructor
  · intro hmem hCE
    exact hmem (hCE ▸ C.genericPoint_mem)
  · intro hCE hmem
    exact hCE (eq_of_genericPoint_mem C E hmem)

/-! ## Coefficients of a restricted Cartier divisor -/

variable [∀ y : X.toScheme, UniqueFactorizationMonoid (X.stalk y)]
  (V : X.toScheme.Opens) [Nonempty V.toScheme]

local instance kernelOpenNonempty : Nonempty V := ⟨Classical.choice inferInstance⟩

local instance kernelOpenIntegral : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

/-- Transport back and forth along the function-field isomorphism is the identity. -/
theorem transportUnit_of_hom (f : X.toScheme.functionFieldˣ) :
    transportUnit V (Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom f) = f := by
  apply Units.ext
  exact Iso.hom_inv_id_apply (functionFieldIso V.ι) (f : X.toScheme.functionField)

/-- **The coefficients of the restriction are the accepted Cartier–Weil coefficients** at every
prime curve meeting the open. -/
theorem restrictedCoefficient_cartierRestriction (D : CartierDivisor X.toScheme)
    (C : X.PrimeCurve) (hC : C.genericPoint ∈ V) :
    restrictedCoefficient V (cartierRestrictionHom V.ι D) C = X.cartierToWeilHom D C := by
  obtain ⟨e, U₀, hmem, hU₀⟩ := exists_cartierOrderEquation X.toScheme D C.genericPoint
  letI : Nonempty U₀ := ⟨⟨C.genericPoint, hmem⟩⟩
  letI : Nonempty (V.ι ⁻¹ᵁ U₀) := ⟨⟨(⟨C.genericPoint, hC⟩ : V.toScheme), hmem⟩⟩
  have hpre := cartierRestriction_globalEquation_preimage V.ι D U₀ e hU₀
  have hCW : C.genericPoint ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ U₀) :=
    (Scheme.Hom.map_mem_image_iff V.ι (U := V.ι ⁻¹ᵁ U₀)
      (x := (⟨C.genericPoint, hC⟩ : V.toScheme))).mpr hmem
  rw [restrictedCoefficient_eq_of_equation V (cartierRestrictionHom V.ι D) C (V.ι ⁻¹ᵁ U₀) hCW
      (Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom e) hpre,
    transportUnit_of_hom V e]
  exact (X.cartierToWeilHom_apply_of_equation D C U₀ hmem e hU₀).symm

/-- A Cartier divisor of the open subscheme with vanishing Weil divisor is zero (from BRIEF31's
`cartierRestrictionHom_extension`). -/
theorem eq_zero_of_restrictedWeilHom_eq_zero (D : CartierDivisor V.toScheme)
    (hD : restrictedWeilHom V D = 0) : D = 0 := by
  have hext : extension V D = 0 := by
    rw [extension, hD, map_zero]
  have h := cartierRestrictionHom_extension V D
  rw [hext, map_zero] at h
  exact h.symm

/-! ## The kernel of restriction to the complement of `E` -/

/-- The Picard class `[O_X(E)]` of a prime curve. The class of `O_X(−E)` is its inverse. -/
def primeCurveClass : X.toScheme.Pic := X.weilPicardClass (Finsupp.single E 1)

/-- The Weil-to-Picard map as an additive homomorphism. -/
def weilPicardHom (X : NormalProjectiveSurface k)
    [∀ y : X.toScheme, UniqueFactorizationMonoid (X.stalk y)] :
    X.WeilDivisor →+ Additive X.toScheme.Pic :=
  X.weilClassPicardEquiv.toAddMonoidHom.comp X.weilClassMap

theorem weilPicardHom_apply (D : X.WeilDivisor) :
    weilPicardHom X D = Additive.ofMul (X.weilPicardClass D) := rfl

/-- Multiples of a prime divisor give powers of its class. -/
theorem weilPicardClass_single (n : ℤ) :
    X.weilPicardClass (Finsupp.single E n) = primeCurveClass E ^ n := by
  have h := AddMonoidHom.apply_int (Additive X.toScheme.Pic)
    ((weilPicardHom X).comp (Finsupp.singleAddHom E)) n
  have h1 : ((weilPicardHom X).comp (Finsupp.singleAddHom E)) n =
      Additive.ofMul (X.weilPicardClass (Finsupp.single E n)) := rfl
  have h2 : ((weilPicardHom X).comp (Finsupp.singleAddHom E)) 1 =
      Additive.ofMul (primeCurveClass E) := rfl
  rw [h1, h2] at h
  have h3 := congrArg Additive.toMul h
  rw [toMul_zsmul] at h3
  exact h3

variable {V}

/-- **`[O_X(E)]` restricts trivially to the complement of `E`.** -/
theorem primeCurveClass_mem_ker
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E) :
    primeCurveClass E ∈ (schemePicardPullbackHom V.ι).ker := by
  have hrep : primeCurveClass E =
      cartierPicardClass X.toScheme (X.cartierWeilEquiv.symm (Finsupp.single E 1)) :=
    X.weilClassPicardEquiv_representative (Finsupp.single E 1)
  have hw : X.cartierToWeilHom (X.cartierWeilEquiv.symm (Finsupp.single E 1)) =
      Finsupp.single E 1 := by
    have hh := X.cartierWeilEquiv.apply_symm_apply (Finsupp.single E 1)
    rwa [X.cartierWeilEquiv_apply] at hh
  have hzero : cartierRestrictionHom V.ι (X.cartierWeilEquiv.symm (Finsupp.single E 1)) = 0 := by
    apply eq_zero_of_restrictedWeilHom_eq_zero V
    apply Finsupp.ext
    intro C
    by_cases hC : C.genericPoint ∈ V
    · have hcoeff := restrictedCoefficient_cartierRestriction V
        (X.cartierWeilEquiv.symm (Finsupp.single E 1)) C hC
      have hCE : C ≠ E := (hV C).mp hC
      change restrictedCoefficient V _ C = (0 : X.WeilDivisor) C
      rw [hcoeff, hw, Finsupp.single_eq_of_ne (Ne.symm hCE)]
      rfl
    · change restrictedCoefficient V _ C = (0 : X.WeilDivisor) C
      rw [restrictedCoefficient_of_not_mem V _ C hC]
      rfl
  have hone : cartierPicardClass V.toScheme 0 = 1 := by
    have hp := cartierPicardClass_principal V.toScheme (1 : V.toScheme.functionFieldˣ)
    rwa [show Additive.ofMul (1 : V.toScheme.functionFieldˣ) = 0 from rfl, map_zero] at hp
  rw [MonoidHom.mem_ker, hrep, schemePicardPullbackHom_cartierPicardClass, hzero, hone]

/-- **Step (iii): the kernel of restriction to `X ∖ E` is the group of powers of `[O_X(E)]`.** -/
theorem mem_ker_iff (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E)
    (c : X.toScheme.Pic) :
    c ∈ (schemePicardPullbackHom V.ι).ker ↔ ∃ n : ℤ, c = primeCurveClass E ^ n := by
  constructor
  · intro hc
    obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme c
    rw [MonoidHom.mem_ker, schemePicardPullbackHom_cartierPicardClass] at hc
    obtain ⟨g', hg'⟩ := (cartierPicardClass_eq_one_iff V.toScheme _).mp hc
    set g : X.toScheme.functionFieldˣ := transportUnit V g' with hgdef
    set D₀ : CartierDivisor X.toScheme :=
      D - principalCartierDivisorHom X.toScheme (Additive.ofMul g) with hD₀def
    have hrestr : cartierRestrictionHom V.ι D₀ = 0 := by
      rw [hD₀def, map_sub, cartierRestrictionHom_principal, hgdef, transportUnit_hom, hg',
        sub_self]
    have hsingle : X.cartierToWeilHom D₀ = Finsupp.single E (X.cartierToWeilHom D₀ E) := by
      apply Finsupp.ext
      intro C
      by_cases hCE : C = E
      · rw [hCE, Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hCE)]
        have hC : C.genericPoint ∈ V := (hV C).mpr hCE
        have hcoeff := restrictedCoefficient_cartierRestriction V D₀ C hC
        rw [hrestr, restrictedCoefficient_zero] at hcoeff
        exact hcoeff.symm
    have hclass : cartierPicardClass X.toScheme D₀ = cartierPicardClass X.toScheme D := by
      have hhom : cartierPicardHom X.toScheme D₀ = cartierPicardHom X.toScheme D := by
        rw [hD₀def, map_sub, cartierPicardHom_principal, sub_zero]
      exact congrArg Additive.toMul hhom
    refine ⟨X.cartierToWeilHom D₀ E, ?_⟩
    rw [← weilPicardClass_single E, ← hsingle, X.weilPicardClass_of_cartier, hclass]
  · rintro ⟨n, rfl⟩
    exact Subgroup.zpow_mem _ (primeCurveClass_mem_ker E hV) n

/-! ## The kernel as `ℤ` -/

/-- A named hypothesis: the class `c` has infinite order. -/
def InfiniteOrder (c : X.toScheme.Pic) : Prop := ∀ n : ℤ, c ^ n = 1 → n = 0

/-- The powers of `[O_X(E)]`, as a homomorphism into the kernel. -/
def kernelHom (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E) :
    Multiplicative ℤ →* ↥(schemePicardPullbackHom V.ι).ker where
  toFun n := ⟨primeCurveClass E ^ n.toAdd, (mem_ker_iff E hV _).mpr ⟨n.toAdd, rfl⟩⟩
  map_one' := Subtype.ext (zpow_zero (primeCurveClass E))
  map_mul' a b := Subtype.ext (zpow_add (primeCurveClass E) a.toAdd b.toAdd)

theorem kernelHom_bijective (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E)
    (hinf : InfiniteOrder (primeCurveClass E)) :
    Function.Bijective (kernelHom E hV) := by
  constructor
  · intro a b hab
    have h : primeCurveClass E ^ a.toAdd = primeCurveClass E ^ b.toAdd :=
      congrArg (fun z : ↥(schemePicardPullbackHom V.ι).ker => (z : X.toScheme.Pic)) hab
    have hsub : primeCurveClass E ^ (a.toAdd - b.toAdd) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    exact Multiplicative.toAdd.injective (sub_eq_zero.mp (hinf _ hsub))
  · rintro ⟨c, hc⟩
    obtain ⟨n, rfl⟩ := (mem_ker_iff E hV c).mp hc
    exact ⟨Multiplicative.ofAdd n, Subtype.ext rfl⟩

/-- **`ker (Pic X → Pic (X ∖ E)) ≃* ℤ`**, given that `[O_X(E)]` has infinite order. -/
def kernelEquivInt (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E)
    (hinf : InfiniteOrder (primeCurveClass E)) :
    ↥(schemePicardPullbackHom V.ι).ker ≃* Multiplicative ℤ :=
  (MulEquiv.ofBijective (kernelHom E hV) (kernelHom_bijective E hV hinf)).symm

end KltDP.Geometry.PrimeCurveComplementKernel
