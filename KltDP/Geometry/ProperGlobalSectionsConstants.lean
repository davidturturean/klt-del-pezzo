import KltDP.Geometry.ProperGlobalSectionsFinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Constant global functions over an algebraically closed base

The scalar map is induced by the original scheme morphism. Its finiteness,
already proved using Mathlib's proper global-sections theorem, makes it
integral. Mathlib's algebraically closed field theorem then proves that
this particular map is bijective. The resulting algebra equivalence and
dimension statement use this same scalar action throughout.

No choice of a field structure on global sections or abstract identification
of the section ring is part of the input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
  [UniversallyClosed f] [LocallyOfFiniteType f]

/-- Every global function is a unique scalar from the original base field. -/
theorem baseFieldToGlobalSections_bijective :
    Function.Bijective (baseFieldToGlobalSections f) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral (baseFieldToGlobalSections f)
    (baseFieldToGlobalSections_finite f).to_isIntegral

/-- The actual scalar map identifies the section algebra with the base. -/
def baseFieldGlobalSectionsAlgEquiv :
    letI := (baseFieldToGlobalSections f).toAlgebra
    k ≃ₐ[k] Γ(X, ⊤) := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  exact AlgEquiv.ofBijective (Algebra.ofId k Γ(X, ⊤))
    (baseFieldToGlobalSections_bijective f)

/-- The equivalence sends a scalar to its global constant section. -/
theorem baseFieldGlobalSectionsAlgEquiv_apply (a : k) :
    baseFieldGlobalSectionsAlgEquiv f a = baseFieldToGlobalSections f a := rfl

/-- Global functions have dimension one for the original scalar action. -/
theorem globalSections_finrank_one :
    letI := (baseFieldToGlobalSections f).toAlgebra
    Module.finrank k Γ(X, ⊤) = 1 := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  calc
    Module.finrank k Γ(X, ⊤) = Module.finrank k k :=
      (baseFieldGlobalSectionsAlgEquiv f).symm.toLinearEquiv.finrank_eq
    _ = 1 := Module.finrank_self k

end KltDP.Geometry
