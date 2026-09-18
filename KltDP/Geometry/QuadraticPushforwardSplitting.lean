import KltDP.Geometry.QuadraticPushforwardProjections
import KltDP.Geometry.SchemeModuleBiprodEvaluation

/-!
# The original quadratic pushforward splits into its two actual coefficient modules

The two global projections are an isomorphism because their evaluated
map on a basis is the original quadratic coefficient equivalence. No
global splitting, trace map, or supplied pushforward identification is
an input. A nonempty basis is extracted from the original line atlas in
the following specialization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing SchemeModuleBiprodEvaluation

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

local instance splittingModulesBinaryBiproducts : HasBinaryBiproducts X.Modules :=
  HasBinaryBiproducts.of_hasBinaryProducts

variable {κ : Type u} (a : κ → ι)
  (hB : Opens.IsBasis (Set.range (fun i => D.opens (a i))))
  [∀ i, Nontrivial Γ(X, D.opens (a i))]

/-- The original constant and root maps together give the coefficient morphism. -/
def coefficientSplittingMap : D.pushforwardUnit ⟶
    _root_.SheafOfModules.unit X.ringCatSheaf ⊞ D.inverseTransitionModule :=
  biprod.lift (D.constantProjection a hB) (D.inverseProjection a hB)

/-- The coefficient morphism is an isomorphism on the actual global modules. -/
theorem coefficientSplittingMap_isIso : IsIso (D.coefficientSplittingMap a hB) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis _ hB
  intro i
  let U := D.opens (a i)
  let T := trivialization X D.opens (inverseUnits X D.opens D.units)
    (inverseUnits_isCocycle X D.opens D.units D.cocycle) (a i) (le_refl U)
  let e := (D.coefficientPairEquiv (a i)).trans
    ((LinearEquiv.refl Γ(X, U) Γ(X, U)).prodCongr T.symm)
  let q := sectionPairEquiv (_root_.SheafOfModules.unit X.ringCatSheaf)
    D.inverseTransitionModule U
  have heq : (q : _ → _) ∘
      ((D.coefficientSplittingMap a hB).val.app (op U) : _ → _) = (e : _ → _) := by
    funext s
    change sectionPairEquiv (_root_.SheafOfModules.unit X.ringCatSheaf)
      D.inverseTransitionModule U
        ((biprod.lift (D.constantProjection a hB) (D.inverseProjection a hB)).val.app
          (op U) s) = e s
    rw [sectionPairEquiv_lift, D.constantProjection_app, D.inverseProjection_app]
    rfl
  apply (Function.Bijective.of_comp_iff' q.bijective _).mp
  rw [heq]
  exact e.bijective

/-- The constructed splitting of the original pushforward structure sheaf. -/
def coefficientSplittingIso : D.pushforwardUnit ≅
    _root_.SheafOfModules.unit X.ringCatSheaf ⊞ D.inverseTransitionModule := by
  letI := D.coefficientSplittingMap_isIso a hB
  exact asIso (D.coefficientSplittingMap a hB)

end KltDP.Geometry.QuadraticCoverAtlas.Data

#check @KltDP.Geometry.QuadraticCoverAtlas.Data.coefficientSplittingIso
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.coefficientSplittingIso
