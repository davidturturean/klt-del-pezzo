import KltDP.Geometry.CoherentQuasicoherent
import KltDP.Geometry.QuasicoherentSectionExtension

/-!
# Original coherent sections extend after powers of a function

The original literal coherence predicate supplies quasicoherence through
the constructed finite presentations. The actual QCQS extension theorem
then applies to the same module, function, intrinsic basic open and section.
No additional quasicoherence or extension witness is assumed.

This is the global-function case; powers of a nontrivial invertible sheaf
and the construction of a Serre-ample sheaf remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CoherentSectionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules) [IsCoherentModule M]

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.presheaf.obj (op V)) :=
  (M.val.obj (op V)).isModule

/-- An actual coherent section over D(f) extends to the original QCQS
domain after multiplication by a power of the original function. -/
theorem exists_restrict_eq_pow_smul {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hUqs : IsQuasiSeparated (U : Set X))
    (f : Γ(X, U)) (s : M.val.obj (op (X.basicOpen f))) :
    ∃ (n : ℕ) (t : M.val.obj (op U)),
      M.val.map (homOfLE (X.basicOpen_le f)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
  letI : M.IsQuasicoherent :=
    CoherentQuasicoherent.isQuasicoherent_of_isCoherentModule M
  exact QuasicoherentSectionExtension.exists_restrict_eq_pow_smul_of_qcqs M hU hUqs f s

end KltDP.Geometry.CoherentSectionExtension
