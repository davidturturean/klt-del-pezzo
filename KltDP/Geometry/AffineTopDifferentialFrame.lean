/-
The determinant/permutation argument below is adapted from the pinned
Mathlib/LinearAlgebra/Determinant.lean at commit
c44e0c8ee63ca166450922a373c7409c5d26b00b, preserving its notice:

Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit

/-!
# Actual top differential frames on standard-smooth affine surfaces

A finite basis gives a frame of its actual top exterior power. Applying
this to the actual Kähler basis of a submersive presentation of relative
dimension two gives a frame of `⋀[A]^2 (KaehlerDifferential k A)` and an
isomorphism from its actual tilde module sheaf to the structure-sheaf unit.

The frame depends on the presentation and the ordering of its free
coordinates. No global canonical divisor or numerical pairing is defined
here. The proof uses alternation in every characteristic and requires no
nontriviality assumption on the coefficient ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry.AffineTopDifferentialFrame

section ExteriorFrame

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
variable {n : ℕ}

/-- The determinant relative to an actual finite basis identifies its
actual top exterior power with the coefficient ring. The inverse sends
a scalar to that scalar times the wedge of the basis. -/
def determinantEquiv (b : Basis (Fin n) A M) : (⋀[A]^n M) ≃ₗ[A] A := by
  let φ : (⋀[A]^n M) →ₗ[A] A := exteriorPower.alternatingMapLinearEquiv b.det
  let ψ : A →ₗ[A] (⋀[A]^n M) :=
    LinearMap.toSpanSingleton A (⋀[A]^n M) (exteriorPower.ιMulti A n b)
  refine LinearEquiv.ofLinear φ ψ ?_ ?_
  · apply LinearMap.ext
    intro r
    change exteriorPower.alternatingMapLinearEquiv b.det
      (r • exteriorPower.ιMulti A n b) = r
    simp only [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Basis.det_self, smul_eq_mul, mul_one]
  · apply exteriorPower.linearMap_ext
    let F := (ψ.comp φ).compAlternatingMap (exteriorPower.ιMulti A n)
    let G := (LinearMap.id : (⋀[A]^n M) →ₗ[A] (⋀[A]^n M)).compAlternatingMap
      (exteriorPower.ιMulti A n)
    have hb : F b = G b := by
      change (exteriorPower.alternatingMapLinearEquiv b.det
        (exteriorPower.ιMulti A n b)) • exteriorPower.ιMulti A n b =
        exteriorPower.ιMulti A n b
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        Basis.det_self, one_smul]
    change F = G
    refine Basis.ext_alternating b fun i hi => ?_
    let σ : Equiv.Perm (Fin n) :=
      Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change F (b ∘ σ) = G (b ∘ σ)
    rw [F.map_perm, G.map_perm, hb]

/-- The frame coordinate of any actual pure wedge is its determinant. -/
theorem determinantEquiv_apply_wedge (b : Basis (Fin n) A M) (v : Fin n → M) :
    determinantEquiv b (exteriorPower.ιMulti A n v) = b.det v := by
  change exteriorPower.alternatingMapLinearEquiv b.det
    (exteriorPower.ιMulti A n v) = b.det v
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

/-- The wedge of the chosen basis has frame coordinate one. -/
theorem determinantEquiv_basis_wedge (b : Basis (Fin n) A M) :
    determinantEquiv b (exteriorPower.ιMulti A n b) = 1 :=
  (determinantEquiv_apply_wedge b b).trans b.det_self

/-- The inverse frame map uses the actual canonical wedge, not a chosen
unrelated generator of an isomorphic module. -/
theorem determinantEquiv_symm_apply (b : Basis (Fin n) A M) (a : A) :
    (determinantEquiv b).symm a = a • exteriorPower.ιMulti A n b := rfl

end ExteriorFrame

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- Reindex the actual differential basis supplied by a submersive
presentation whose relative dimension is two. Its size follows from
the presentation's generator/relation count. -/
def presentationDifferentialBasis (P : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) : Basis (Fin 2) A (KaehlerDifferential k A) := by
  classical
  letI := Fintype.ofFinite P.vars
  letI := Fintype.ofFinite P.rels
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set P.vars) = 2 := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
  exact P.basisKaehler.reindex (Fintype.equivFinOfCardEq hc)

/-- The original top differential module has an actual frame provided by
the chosen standard-smooth presentation. -/
def presentationTopDifferentialEquiv (P : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) : (⋀[A]^2 (KaehlerDifferential k A)) ≃ₗ[A] A :=
  determinantEquiv (presentationDifferentialBasis k A P hP)

/-- The actual affine tilde of the top differential module is isomorphic
to the original structure-sheaf unit. -/
def presentationTopDifferentialSheafIso (P : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) :
    (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential k A))).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of A (⋀[A]^2 (KaehlerDifferential k A))) (N := ModuleCat.of A A)
    (presentationTopDifferentialEquiv k A P hP) ≪≫
    AffineModuleTilde.unitIso A

/-- Standard smoothness supplies the presentation used for the actual
rank-two Kähler basis. -/
def standardSmoothDifferentialBasis
    [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    Basis (Fin 2) A (KaehlerDifferential k A) :=
  presentationDifferentialBasis k A
    (Classical.choose
      (Algebra.IsStandardSmoothOfRelativeDimension.out (R := k) (S := A) (n := 2)))
    (Classical.choose_spec
      (Algebra.IsStandardSmoothOfRelativeDimension.out (R := k) (S := A) (n := 2)))

/-- A standard-smooth algebra of relative dimension two has the actual
top differential frame, without an additional rank or regularity premise. -/
def standardSmoothTopDifferentialEquiv
    [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    (⋀[A]^2 (KaehlerDifferential k A)) ≃ₗ[A] A :=
  determinantEquiv (standardSmoothDifferentialBasis k A)

/-- The actual top differential tilde is trivial on this standard-smooth
affine chart. This is a local frame theorem for the original differential
module; it does not assert that frames agree on distinct charts. -/
def standardSmoothTopDifferentialSheafIso
    [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential k A))).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of A (⋀[A]^2 (KaehlerDifferential k A))) (N := ModuleCat.of A A)
    (standardSmoothTopDifferentialEquiv k A) ≪≫
    AffineModuleTilde.unitIso A

end KltDP.Geometry.AffineTopDifferentialFrame
