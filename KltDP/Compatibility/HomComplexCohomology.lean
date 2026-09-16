/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import KltDP.Compatibility.HomComplexSingleCocycle
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The cocycle quotient computes the homology of the Hom complex

Port of the quotient and actual homology-data blocks of Mathlib
`HomComplexCohomology` at 79d0395a1825a6264ad5d269e35e60537518955e.
The cocycle inclusion reuses the pinned concrete additive kernel theorem.
The existing coboundary subgroup is unchanged. Newer syntax and category
names are adapted to the pin; no Ext or homotopy-category equivalence is
assumed.
-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex.HomComplex

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

/-- The actual subgroup inclusion from cocycles to cochains. -/
def Cocycle.toCochainAddMonoidHom : Cocycle K L n →+ Cochain K L n :=
  (cocycle K L n).subtype

@[simp]
lemma Cocycle.toCochainAddMonoidHom_apply (x : Cocycle K L n) :
    Cocycle.toCochainAddMonoidHom K L n x = (x : Cochain K L n) := rfl

/-- The original cocycle subgroup is a categorical kernel of the differential. -/
def Cocycle.isKernel (hm : n + 1 = m) :
    IsLimit (KernelFork.ofι (f := (HomComplex K L).d n m)
      (AddCommGrp.ofHom (Cocycle.toCochainAddMonoidHom K L n)) (by
        apply AddCommGrp.ext
        intro x
        exact Cocycle.δ_eq_zero x m)) := by
  subst m
  change IsLimit (AddCommGrp.kernelCone ((HomComplex K L).d n (n + 1)))
  exact AddCommGrp.kernelIsLimit ((HomComplex K L).d n (n + 1))

/-- The type of cohomology classes of degree `n` in the complex of morphisms
from `K` to `L`. -/
def CohomologyClass : Type v := Cocycle K L n ⧸ coboundaries K L n

instance : AddCommGroup (CohomologyClass K L n) :=
  inferInstanceAs (AddCommGroup (Cocycle K L n ⧸ coboundaries K L n))

namespace CohomologyClass

variable {K L n}

/-- The cohomology class of a cocycle. -/
def mk (x : Cocycle K L n) : CohomologyClass K L n :=
  Quotient.mk _ x

lemma mk_surjective : Function.Surjective (mk : Cocycle K L n → _) :=
  Quotient.mk_surjective

variable (K L n) in
@[simp]
lemma mk_zero :
    mk (0 : Cocycle K L n) = 0 := rfl

@[simp]
lemma mk_add (x y : Cocycle K L n) :
    mk (x + y) = mk x + mk y := rfl

@[simp]
lemma mk_sub (x y : Cocycle K L n) :
    mk (x - y) = mk x - mk y := rfl

@[simp]
lemma mk_neg (x : Cocycle K L n) :
    mk (-x) = -mk x := rfl

lemma mk_eq_zero_iff (x : Cocycle K L n) :
    mk x = 0 ↔ x ∈ coboundaries K L n :=
  QuotientAddGroup.eq_zero_iff x

variable (K L n) in
/-- The projection map `Cocycle K L n →+ CohomologyClass K L n`. -/
def mkAddMonoidHom : Cocycle K L n →+ CohomologyClass K L n where
  toFun := mk
  map_zero' := by simp
  map_add' := by simp

@[simp]
lemma mkAddMonoidHom_apply (x : Cocycle K L n) :
    mkAddMonoidHom K L n x = mk x := rfl

section

variable {G : Type*} [AddCommGroup G]
  (f : Cocycle K L n →+ G) (hf : coboundaries K L n ≤ f.ker)

/-- Constructor for additive morphisms from `CohomologyClass K L n`. -/
def descAddMonoidHom :
    CohomologyClass K L n →+ G :=
  QuotientAddGroup.lift _ f hf

@[simp]
lemma descAddMonoidHom_cohomologyClass (x : Cocycle K L n) :
    descAddMonoidHom f hf (mk x) = f x := rfl

end

end CohomologyClass

private lemma cocycle_kernel_lift_coe (hp : m + 1 = p)
    {A : AddCommGrp.{v}} (f : A ⟶ AddCommGrp.of (Cochain K L m))
    (hf : f ≫ (HomComplex K L).d m p = 0) (x : A) :
    Cocycle.toCochainAddMonoidHom K L m
      (((Cocycle.isKernel K L m p hp).lift (KernelFork.ofι f hf)).hom x) = f.hom x := by
  exact ConcreteCategory.congr_hom
    ((Cocycle.isKernel K L m p hp).fac (KernelFork.ofι f hf) WalkingParallelPair.zero) x

/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
def leftHomologyData' (hm : n + 1 = m) (hp : m + 1 = p) :
    ((HomComplex K L).sc' n m p).LeftHomologyData where
  K := .of (Cocycle K L m)
  H := .of (CohomologyClass K L m)
  i := AddCommGrp.ofHom (Cocycle.toCochainAddMonoidHom K L m)
  π := AddCommGrp.ofHom (CohomologyClass.mkAddMonoidHom K L m)
  wi := by
    apply AddCommGrp.ext
    intro x
    exact Cocycle.δ_eq_zero x p
  hi := Cocycle.isKernel K L _ _ hp
  wπ := by
    ext x
    dsimp
    rw [CohomologyClass.mk_eq_zero_iff]
    refine ⟨n, hm, x, ?_⟩
    exact (cocycle_kernel_lift_coe K L m p hp
      ((HomComplex K L).sc' n m p).f
      ((HomComplex K L).sc' n m p).zero x).symm
  hπ :=
    Cofork.IsColimit.mk _
      (fun s ↦ AddCommGrp.ofHom (CohomologyClass.descAddMonoidHom s.π.hom
        (by
          rintro z ⟨q, hq, y, hy⟩
          obtain rfl : n = q := by omega
          change s.π.hom z = 0
          let d := ((HomComplex K L).sc' n m p).f
          let hd := ((HomComplex K L).sc' n m p).zero
          have hz : ((Cocycle.isKernel K L m p hp).lift
              (KernelFork.ofι d hd)).hom y = z := by
            apply Subtype.ext
            exact (cocycle_kernel_lift_coe K L m p hp d hd y).trans hy
          have hs := ConcreteCategory.congr_hom s.condition y
          simp only [zero_comp] at hs
          change s.π.hom (((Cocycle.isKernel K L m p hp).lift
            (KernelFork.ofι d hd)).hom y) = 0 at hs
          exact (congrArg s.π.hom hz).symm.trans hs)))
      (fun s ↦ rfl)
      (fun s l hl ↦ by
        ext x
        obtain ⟨y, rfl⟩ := x.mk_surjective
        simpa using ConcreteCategory.congr_hom hl y)

/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
noncomputable def leftHomologyData :
    ((HomComplex K L).sc n).LeftHomologyData :=
  leftHomologyData' K L _ n _ (by simp) (by simp)

/-- The homology of `HomComplex K L` in degree `n` identifies to `CohomologyClass K L n`. -/
noncomputable def homologyAddEquiv :
    (HomComplex K L).homology n ≃+ CohomologyClass K L n :=
  (leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv

end CochainComplex.HomComplex
