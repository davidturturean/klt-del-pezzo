import KltDP.LinearAlgebra.SplitConormalDeterminant
import KltDP.RingTheory.RegularPrincipalConormal
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Actual local determinant adjunction for a smooth principal quotient

For an actual regular equation `d` generating `J`, the original quotient
`B = A/J` has a split conormal sequence when `A` and `B` are formally
smooth over the original base ring. A standard-smooth presentation of
relative dimension one for `B` supplies its Kähler frame. These proved
inputs give an actual equivalence `Ω[B/R] ≃ ∧²(B ⊗[A] Ω[A/R])`.

The equivalence sends the image of an ambient form `η` to `d(d) ∧ η`.
It is independent of the quotient frame and scales by the original
quotient scalar when the actual equation is multiplied. No adjunction,
conormal exactness, determinant relation, or differential frame is
postulated in the final standard-smooth endpoint.

The original conormal and Kähler sheaf chart comparisons, overlap
compatibility, and gluing to the accepted surface canonical sheaf remain
the global producer obligation. No statement about singular curves or
duality is asserted.
-/

noncomputable section

open scoped TensorProduct
open KltDP.LinearAlgebra.SplitConormalDeterminant

universe u

namespace KltDP.RingTheory.SmoothPrincipalConormalDeterminant

section KernelTransport

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

private def cotangentMapOfKerEq (I : Ideal A) (hI : I = RingHom.ker (algebraMap A B)) :
    I.Cotangent →ₗ[A] B ⊗[A] KaehlerDifferential R A := by
  subst I
  exact KaehlerDifferential.kerCotangentToTensor R A B

private theorem cotangentMapOfKerEq_toCotangent
    (I : Ideal A) (hI : I = RingHom.ker (algebraMap A B)) (x : I) :
    cotangentMapOfKerEq R A B I hI (I.toCotangent x) =
      1 ⊗ₜ[A] KaehlerDifferential.D R A (x : A) := by
  subst I
  exact KaehlerDifferential.kerCotangentToTensor_toCotangent R A B x

private theorem cotangentMapOfKerEq_exact
    (I : Ideal A) (hI : I = RingHom.ker (algebraMap A B))
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact (cotangentMapOfKerEq R A B I hI)
      (KaehlerDifferential.mapBaseChange R A B) := by
  subst I
  exact KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

private theorem cotangentMapOfKerEq_injective
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
    (I : Ideal A) (hI : I = RingHom.ker (algebraMap A B))
    (h : Function.Surjective (algebraMap A B)) :
    Function.Injective (cotangentMapOfKerEq R A B I hI) := by
  subst I
  exact ((Algebra.FormallySmooth.iff_injective_and_split
    (R := R) (P := A) (S := B) h).mp inferInstance).1

end KernelTransport

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)

private theorem quotientKernelEq : J = RingHom.ker (algebraMap A (A ⧸ J)) := by
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- The original differential on the actual ideal conormal module. -/
def quotientCotangentMap :
    J.Cotangent →ₗ[A] (A ⧸ J) ⊗[A] KaehlerDifferential R A :=
  cotangentMapOfKerEq R A (A ⧸ J) J (quotientKernelEq A J)

theorem quotientCotangentMap_toCotangent (x : J) :
    quotientCotangentMap R A J (J.toCotangent x) =
      1 ⊗ₜ[A] KaehlerDifferential.D R A (x : A) :=
  cotangentMapOfKerEq_toCotangent R A (A ⧸ J) J (quotientKernelEq A J) x

/-- The actual defining-equation differential, linear over the original quotient ring. -/
def equationDifferential (d : J) :
    (A ⧸ J) →ₗ[A ⧸ J] (A ⧸ J) ⊗[A] KaehlerDifferential R A :=
  LinearMap.toSpanSingleton (A ⧸ J) ((A ⧸ J) ⊗[A] KaehlerDifferential R A)
    (1 ⊗ₜ[A] KaehlerDifferential.D R A (d : A))

theorem equationDifferential_one (d : J) :
    equationDifferential R A J d 1 = 1 ⊗ₜ[A] KaehlerDifferential.D R A (d : A) :=
  LinearMap.toSpanSingleton_one _ _ _

/-- Its source is the original regular-principal conormal parametrization. -/
theorem quotientCotangentMap_principal (d : J) (q : A ⧸ J) :
    quotientCotangentMap R A J (principalConormalMap J d q) =
      equationDifferential R A J d q := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [principalConormalMap_mk, map_smul, map_smul, quotientCotangentMap_toCotangent]
  change r • ((1 : A ⧸ J) ⊗ₜ[A] KaehlerDifferential.D R A (d : A)) =
    Ideal.Quotient.mk J r • ((1 : A ⧸ J) ⊗ₜ[A] KaehlerDifferential.D R A (d : A))
  exact (algebraMap_smul (A ⧸ J) r _).symm

/-- Exactness uses the pinned conormal theorem and the proved principal parametrization. -/
theorem equationDifferential_exact (d : J) (hJ : Ideal.span {(d : A)} = J) :
    Function.Exact (equationDifferential R A J d)
      (KaehlerDifferential.mapBaseChange R A (A ⧸ J)) := by
  have hex := cotangentMapOfKerEq_exact R A (A ⧸ J) J (quotientKernelEq A J)
    (show Function.Surjective (algebraMap A (A ⧸ J)) from Ideal.Quotient.mk_surjective)
  change Function.Exact (quotientCotangentMap R A J)
    (KaehlerDifferential.mapBaseChange R A (A ⧸ J)) at hex
  intro m
  constructor
  · intro hm
    obtain ⟨x, hx⟩ := (hex m).mp hm
    obtain ⟨q, hq⟩ := principalConormalMap_surjective J d hJ x
    refine ⟨q, ?_⟩
    rw [← quotientCotangentMap_principal, hq, hx]
  · rintro ⟨q, rfl⟩
    exact (hex _).mpr ⟨principalConormalMap J d q, quotientCotangentMap_principal R A J d q⟩

/-- The equation-change formula follows from linearity of the original conormal differential. -/
theorem equationDifferential_change (d e : J) (r : A) (he : (e : A) = r * (d : A)) :
    equationDifferential R A J e 1 =
      Ideal.Quotient.mk J r • equationDifferential R A J d 1 := by
  have he' : e = r • d := Subtype.ext he
  calc
    equationDifferential R A J e 1 = quotientCotangentMap R A J (J.toCotangent e) := by
      rw [equationDifferential_one, quotientCotangentMap_toCotangent]
    _ = r • quotientCotangentMap R A J (J.toCotangent d) := by
      rw [he', map_smul, map_smul]
    _ = Ideal.Quotient.mk J r • equationDifferential R A J d 1 := by
      rw [quotientCotangentMap_toCotangent, equationDifferential_one]
      exact (algebraMap_smul (A ⧸ J) r _).symm

section Smooth

variable [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R (A ⧸ J)]

/-- A smooth regular principal quotient has an injective original equation differential. -/
theorem equationDifferential_injective (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hregular : (d : A) ∈ nonZeroDivisors A) :
    Function.Injective (equationDifferential R A J d) := by
  intro q q' hq
  apply principalConormalMap_injective J d hJ hregular
  apply cotangentMapOfKerEq_injective R A (A ⧸ J) J (quotientKernelEq A J)
    (show Function.Surjective (algebraMap A (A ⧸ J)) from Ideal.Quotient.mk_surjective)
  change quotientCotangentMap R A J (principalConormalMap J d q) =
    quotientCotangentMap R A J (principalConormalMap J d q')
  rwa [quotientCotangentMap_principal, quotientCotangentMap_principal]

/-- Formal smoothness supplies a section of the actual quotient differential map. -/
theorem exists_quotientSection :
    ∃ s : KaehlerDifferential R (A ⧸ J) →ₗ[A ⧸ J]
        (A ⧸ J) ⊗[A] KaehlerDifferential R A,
      KaehlerDifferential.mapBaseChange R A (A ⧸ J) ∘ₗ s = LinearMap.id :=
  ((Algebra.FormallySmooth.iff_injective_and_split (R := R) (P := A) (S := A ⧸ J)
    (show Function.Surjective (algebraMap A (A ⧸ J)) from
      Ideal.Quotient.mk_surjective)).mp inferInstance).2

def quotientSection : KaehlerDifferential R (A ⧸ J) →ₗ[A ⧸ J]
    (A ⧸ J) ⊗[A] KaehlerDifferential R A :=
  Classical.choose (exists_quotientSection R A J)

theorem quotientSection_property :
    KaehlerDifferential.mapBaseChange R A (A ⧸ J) ∘ₗ quotientSection R A J = LinearMap.id :=
  Classical.choose_spec (exists_quotientSection R A J)

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- The equation-normalized actual determinant equivalence, from a quotient differential frame. -/
def determinantEquivOfFrame (a : KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J] (A ⧸ J)) :
    KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J]
      (⋀[A ⧸ J]^2 ((A ⧸ J) ⊗[A] KaehlerDifferential R A)) :=
  equiv (equationDifferential R A J d) (KaehlerDifferential.mapBaseChange R A (A ⧸ J))
    (equationDifferential_exact R A J d hJ)
    (equationDifferential_injective R A J d hJ hregular)
    (quotientSection R A J) (quotientSection_property R A J) a

theorem determinantEquivOfFrame_mapBaseChange
    (a : KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J] (A ⧸ J))
    (m : (A ⧸ J) ⊗[A] KaehlerDifferential R A) :
    determinantEquivOfFrame R A J d hJ hregular a
        (KaehlerDifferential.mapBaseChange R A (A ⧸ J) m) =
      exteriorPower.ιMulti (A ⧸ J) 2 ![1 ⊗ₜ[A] KaehlerDifferential.D R A (d : A), m] := by
  rw [determinantEquivOfFrame, equiv_projection_apply, equationDifferential_one, leftWedge_apply]

theorem determinantEquivOfFrame_eq
    (a a' : KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J] (A ⧸ J)) :
    determinantEquivOfFrame R A J d hJ hregular a =
      determinantEquivOfFrame R A J d hJ hregular a' :=
  equiv_eq _ _ _ _ _ _ _ _ _ _

theorem determinantEquivOfFrame_changeEquation
    (a a' : KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J] (A ⧸ J))
    (e : J) (hE : Ideal.span {(e : A)} = J) (heregular : (e : A) ∈ nonZeroDivisors A)
    (r : A) (he : (e : A) = r * (d : A)) (n : KaehlerDifferential R (A ⧸ J)) :
    determinantEquivOfFrame R A J e hE heregular a' n =
      Ideal.Quotient.mk J r • determinantEquivOfFrame R A J d hJ hregular a n :=
  equiv_apply_of_generator_smul _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (equationDifferential_change R A J d e r he) n

end Smooth

/-- The actual Kähler frame of a standard-smooth quotient of relative dimension one. -/
def standardSmoothQuotientFrame [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)] :
    KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J] (A ⧸ J) := by
  classical
  let P := Classical.choose
    (Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := A ⧸ J) (n := 1))
  have hP : P.dimension = 1 := Classical.choose_spec
    (Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := A ⧸ J) (n := 1))
  letI := Fintype.ofFinite P.vars
  letI := Fintype.ofFinite P.rels
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set P.vars) = 1 := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
  let b := P.basisKaehler.reindex (Fintype.equivFinOfCardEq hc)
  exact b.equivFun.trans (LinearEquiv.funUnique (Fin 1) (A ⧸ J) (A ⧸ J))

section StandardSmooth

variable [Algebra.FormallySmooth R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]

local instance quotientStandardSmooth : Algebra.IsStandardSmooth R (A ⧸ J) :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R) (S := A ⧸ J) 1

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- Local determinant adjunction produced from smoothness and the actual regular equation. -/
def determinantEquiv :
    KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J]
      (⋀[A ⧸ J]^2 ((A ⧸ J) ⊗[A] KaehlerDifferential R A)) :=
  determinantEquivOfFrame R A J d hJ hregular (standardSmoothQuotientFrame R A J)

/-- The produced isomorphism retains the original differential of the actual equation. -/
theorem determinantEquiv_mapBaseChange (m : (A ⧸ J) ⊗[A] KaehlerDifferential R A) :
    determinantEquiv R A J d hJ hregular
        (KaehlerDifferential.mapBaseChange R A (A ⧸ J) m) =
      exteriorPower.ιMulti (A ⧸ J) 2 ![1 ⊗ₜ[A] KaehlerDifferential.D R A (d : A), m] :=
  determinantEquivOfFrame_mapBaseChange R A J d hJ hregular
    (standardSmoothQuotientFrame R A J) m

/-- Replacing the actual equation by an actual multiple gives the required local transition. -/
theorem determinantEquiv_changeEquation
    (e : J) (hE : Ideal.span {(e : A)} = J) (heregular : (e : A) ∈ nonZeroDivisors A)
    (r : A) (he : (e : A) = r * (d : A)) (n : KaehlerDifferential R (A ⧸ J)) :
    determinantEquiv R A J e hE heregular n =
      Ideal.Quotient.mk J r • determinantEquiv R A J d hJ hregular n :=
  determinantEquivOfFrame_changeEquation R A J d hJ hregular
    (standardSmoothQuotientFrame R A J) (standardSmoothQuotientFrame R A J)
    e hE heregular r he n

end StandardSmooth

end KltDP.RingTheory.SmoothPrincipalConormalDeterminant
