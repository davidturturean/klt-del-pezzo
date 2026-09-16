import KltDP.Geometry.EffectiveCartierSection
import KltDP.Geometry.CartierEquationUnits
import KltDP.Geometry.CartierPicardHom
import Mathlib.Algebra.BigOperators.Fin

/-!
# A Cartier divisor from local equations on a cover

On an integral scheme, nonempty opens covering `X` together with a nonzero rational equation on
each, whose classes agree on overlaps, glue (by the sheaf property of the accepted Cartier divisor
sheaf, as in `exists_cartierDivisor_of_weilDivisor`) to a global Cartier divisor
`cartierDivisorOfEquations`. Its restriction to each cover open is the class of the given equation,
it is unique with that property, each cover open is an equation chart, and regular coefficients for
the equations make it an effective divisor with regular equations (`HasRegularCartierEquations`),
so that the accepted `effectiveCartierIdealDataOfRegularEquations` supplies its zero scheme.

The compatibility hypothesis is stated as equality of equation classes on the pairwise
intersections; on an integral scheme these are nonempty (they contain the generic point), which is
recorded as the named instance `inf_nonempty`. The criterion `cartierEquationClassHom_eq_iff`
(ratio is a regular unit) converts it into a statement about unit ratios.

Also recorded: the Picard relation is a formal consequence of a Cartier divisor identity
`D = F + Σ_j (j+1)•C_j + p•P` through the accepted additive `cartierPicardHom`
(`cartierPicardHom_fiber_relation`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- Two nonempty opens of an integral scheme meet (in the generic point). -/
instance inf_nonempty (U V : X.Opens) [Nonempty U] [Nonempty V] : Nonempty (U ⊓ V : X.Opens) :=
  ⟨⟨genericPoint X, genericPoint_mem_nonempty_open X U, genericPoint_mem_nonempty_open X V⟩⟩

section Glue

variable {ι : Type u} (U : ι → X.Opens) [hU : ∀ i, Nonempty (U i)]
  (hcover : (⊤ : X.Opens) ≤ iSup U) (f : ι → X.functionFieldˣ)
  (hcompat : ∀ i j, cartierEquationClassHom X (U i ⊓ U j) (Additive.ofMul (f i)) =
    cartierEquationClassHom X (U i ⊓ U j) (Additive.ofMul (f j)))
include hcover hcompat

omit hcover in
/-- The local equation classes form a compatible family. -/
theorem cartierEquationClasses_isCompatible :
    TopCat.Presheaf.IsCompatible (cartierDivisorSheaf X).val U
      (fun i => cartierEquationClassHom X (U i) (Additive.ofMul (f i))) := by
  intro i j
  change (cartierDivisorSheaf X).val.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
      (cartierEquationClassHom X (U i) (Additive.ofMul (f i))) =
    (cartierDivisorSheaf X).val.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
      (cartierEquationClassHom X (U j) (Additive.ofMul (f j)))
  rw [cartierEquationClassHom_restrict, cartierEquationClassHom_restrict]
  exact hcompat i j

/-- The glued global Cartier divisor with the prescribed local equations. -/
def cartierDivisorOfEquations : CartierDivisor X :=
  ((cartierDivisorSheaf X).existsUnique_gluing' U ⊤ (fun i => homOfLE (show U i ≤ ⊤ from le_top))
    hcover _ (cartierEquationClasses_isCompatible X U f hcompat)).choose

/-- On each cover open the glued divisor has the prescribed equation. -/
theorem cartierDivisorOfEquations_restrict (i : ι) :
    (cartierDivisorSheaf X).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op
        (cartierDivisorOfEquations X U hcover f hcompat) =
      cartierEquationClassHom X (U i) (Additive.ofMul (f i)) :=
  ((cartierDivisorSheaf X).existsUnique_gluing' U ⊤ (fun i => homOfLE (show U i ≤ ⊤ from le_top))
    hcover _ (cartierEquationClasses_isCompatible X U f hcompat)).choose_spec.1 i

/-- A Cartier divisor with the prescribed equations on the cover is the glued one. -/
theorem cartierDivisor_eq_of_local_equations (D : CartierDivisor X)
    (hD : ∀ i, (cartierDivisorSheaf X).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op D =
      cartierEquationClassHom X (U i) (Additive.ofMul (f i))) :
    D = cartierDivisorOfEquations X U hcover f hcompat :=
  ((cartierDivisorSheaf X).existsUnique_gluing' U ⊤ (fun i => homOfLE (show U i ≤ ⊤ from le_top))
    hcover _ (cartierEquationClasses_isCompatible X U f hcompat)).choose_spec.2 D hD

/-- Each cover open is an equation chart of the glued divisor. -/
def cartierDivisorOfEquations_chart (i : ι) :
    CartierEquationChart X (cartierDivisorOfEquations X U hcover f hcompat) where
  openSet := U i
  nonempty := hU i
  equation := f i
  represents := (cartierDivisorOfEquations_restrict X U hcover f hcompat i).symm

variable (c : ∀ i, Γ(X, U i))
  (hc : ∀ i, X.germToFunctionField (U i) (c i) = (f i : X.functionField))
include c hc

/-- Regular coefficients for the equations give regular equation charts. -/
def cartierDivisorOfEquations_regularChart (i : ι) :
    RegularCartierEquationChart X (cartierDivisorOfEquations X U hcover f hcompat) where
  chart := cartierDivisorOfEquations_chart X U hcover f hcompat i
  coefficient := c i
  germ_eq := hc i

/-- With regular coefficients on every cover open, the glued divisor is effective with regular
equations (so the accepted ideal-sheaf data of its zero scheme is available). -/
theorem cartierDivisorOfEquations_hasRegularEquations :
    HasRegularCartierEquations X (cartierDivisorOfEquations X U hcover f hcompat) := by
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
  exact ⟨cartierDivisorOfEquations_regularChart X U hcover f hcompat c hc i, hi⟩

end Glue

/-- Equality of Cartier divisors is local: it suffices to check the restrictions to an open cover. -/
theorem cartierDivisor_eq_of_restrict_eq {ι : Type u} (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U) (D E : CartierDivisor X)
    (h : ∀ i, (cartierDivisorSheaf X).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op D =
      (cartierDivisorSheaf X).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op E) : D = E :=
  (cartierDivisorSheaf X).eq_of_locally_eq' U ⊤ (fun i => homOfLE (show U i ≤ ⊤ from le_top))
    hcover D E h

/-- The Picard relation is a formal consequence of the Cartier divisor identity, through the accepted
additive Cartier→Picard homomorphism. -/
theorem cartierPicardHom_fiber_relation {q : ℕ} (D F P : CartierDivisor X)
    (C : Fin q → CartierDivisor X) (p : ℕ)
    (h : D = F + ∑ j : Fin q, (j.val + 1) • C j + p • P) :
    cartierPicardHom X D =
      cartierPicardHom X F + ∑ j : Fin q, (j.val + 1) • cartierPicardHom X (C j) +
        p • cartierPicardHom X P := by
  rw [h, map_add, map_add, map_sum, map_nsmul]
  simp only [map_nsmul]

end KltDP.Geometry
