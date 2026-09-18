import KltDP.Geometry.FiniteFactorConstant
import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.RationalPoints

/-!
A topologically constant map from the original proper reduced connected
scheme factors through its actual field structure map. The lift is made
into an original affine neighborhood; the compiled affine constant-map
producer supplies the scheme factorization, including its field triangle.
This converts containment of an original prime in a point fiber into
precisely the scheme factorization used by the contraction criterion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurvePointFiberFactorization

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- An actual field-point factorization is constant on underlying points. -/
theorem base_eq_of_factor {C Y : Scheme.{u}}
    (τ : C ⟶ Spec (CommRingCat.of k)) (g : C ⟶ Y)
    (p : Spec (CommRingCat.of k) ⟶ Y) (h : g = τ ≫ p) (c : C) :
    g.base c = fieldMorphismPoint p := by
  rw [h, Scheme.comp_base_apply]
  exact congrArg p.base (Subsingleton.elim (τ.base c) (IsLocalRing.closedPoint k))

/-- The original constant morphism factors through an actual section of
its target's structure map. No affine-target hypothesis is imposed. -/
theorem exists_fieldPoint_of_constant_base [IsAlgClosed k] {C Y : Scheme.{u}}
    (τ : C ⟶ Spec (CommRingCat.of k)) [IsProper τ] [IsReduced C] [ConnectedSpace C]
    (σ : Y ⟶ Spec (CommRingCat.of k)) (g : C ⟶ Y) (hg : g ≫ σ = τ)
    (y : Y) (hbase : ∀ c : C, g.base c = y) :
    ∃ p : Spec (CommRingCat.of k) ⟶ Y,
      g = τ ≫ p ∧ p ≫ σ = 𝟙 _ ∧ fieldMorphismPoint p = y := by
  let U : Y.Opens := (Y.affineCover.map y).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.map y)
  have hyU : y ∈ U := Y.affineCover.covers y
  letI : IsAffine U.toScheme := hU
  have hlift : Set.range g.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    rw [hbase c]
    exact hyU
  let l : C ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hlift
  let p : Spec (CommRingCat.of k) ⟶ Y :=
    FiniteFactorConstant.affinePoint τ l ≫ U.ι
  have hfac : τ ≫ p = g := by
    change τ ≫ (FiniteFactorConstant.affinePoint τ l ≫ U.ι) = g
    rw [← Category.assoc, FiniteFactorConstant.structure_affinePoint]
    exact IsOpenImmersion.lift_fac U.ι g hlift
  have hpσ : p ≫ σ = 𝟙 _ := by
    apply FiniteFactorConstant.structure_comp_injective τ
    change τ ≫ (p ≫ σ) = τ ≫ 𝟙 _
    rw [← Category.assoc, hfac, hg, Category.comp_id]
  refine ⟨p, hfac.symm, hpσ, ?_⟩
  let c : C := Classical.arbitrary C
  exact (base_eq_of_factor τ g p hfac.symm c).symm.trans (hbase c)

/-- An original prime contained in a point fiber is contracted in the
actual field-point sense of the normal-factor prime criterion. -/
theorem exists_factor_of_constant [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (C : X.PrimeCurve) {Y : Scheme.{u}}
    (σ : Y ⟶ Spec (CommRingCat.of k)) (π : X.toScheme ⟶ Y)
    (hπ : π ≫ σ = X.structureMorphism) (y : Y)
    (hC : ∀ x ∈ (C : Set X.toScheme), π.base x = y) :
    ∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _ ∧ fieldMorphismPoint p = y := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  apply exists_fieldPoint_of_constant_base C.toSpec σ (C.inclusion ≫ π)
  · rw [Category.assoc, hπ]
    rfl
  · intro c
    change π.base (C.inclusion.base c) = y
    apply hC
    rw [← C.range_inclusion]
    exact Set.mem_range_self c

/-- The original prime's scheme factorization gives constancy on its
original carrier in the surface. -/
theorem base_eq_on_prime_of_factor
    (X : NormalProjectiveSurface k) (C : X.PrimeCurve) {Y : Scheme.{u}}
    (π : X.toScheme ⟶ Y) (p : Spec (CommRingCat.of k) ⟶ Y)
    (h : C.inclusion ≫ π = C.toSpec ≫ p) :
    ∀ x ∈ (C : Set X.toScheme), π.base x = fieldMorphismPoint p := by
  intro x hx
  rw [← C.range_inclusion] at hx
  obtain ⟨c, rfl⟩ := hx
  exact base_eq_of_factor C.toSpec (C.inclusion ≫ π) p h c

end KltDP.Geometry.PrimeCurvePointFiberFactorization
