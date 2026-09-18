import KltDP.Geometry.NonclosedPointBirationalIso
import KltDP.Geometry.ClosedPointFiberSubsingleton
import KltDP.Geometry.ProperBirationalPointFiber
import KltDP.Geometry.ProperIsoComponents

/-!
The actual proper birational map with connected fibers and an isomorphic
structure-sheaf pushforward is an isomorphism off its contracted support.
Closed fibers are controlled by actual contracted prime curves; nonclosed
fibers are controlled by the proved codimension-one isomorphism theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperBirationalOffContractedSupport

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X Y : NormalProjectiveSurface k) (π : X.toScheme ⟶ Y.toScheme)
  [IsProper π] [Surjective π]
  (hπ : π ≫ Y.structureMorphism = X.structureMorphism)
  (hbir : IsBirationalScheme π) (S : Set X.toScheme)
  (hS : ∀ C : X.PrimeCurve,
    (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) →
    (C : Set X.toScheme) ⊆ S)

include hπ hbir hS

theorem pointFiber_subsingleton (y : Y.toScheme)
    (hconnected : IsConnected (π.base ⁻¹' {y})) (hout : y ∉ π.base '' S) :
    (π.base ⁻¹' {y}).Subsingleton := by
  letI : Nontrivial Y.toScheme :=
    ProperBirationalPointFiber.target_nontrivial X Y.structureMorphism π hbir
  by_cases hy : IsClosed ({y} : Set Y.toScheme)
  · exact ClosedPointFiberSubsingleton.subsingleton_off_contracted_support
      X π Y.structureMorphism hπ S hS y hy hconnected hout
  · obtain ⟨U, hyU, hU⟩ :=
      NonclosedPointBirationalIso.exists_isomorphism_open Y π hbir y hy
    letI : IsIso (π ∣_ U) := hU
    exact NonclosedPointBirationalIso.pointFiber_subsingleton_of_isIso_restrict π U y hyU

/-- The original map restricted away from all contracted prime images
is an isomorphism; no quasi-finiteness or inverse map is assumed. -/
theorem isIso_restrict [IsIso π.c]
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (U : Y.toScheme.Opens) (hU : ∀ y ∈ U, y ∉ π.base '' S) :
    IsIso (π ∣_ U) := by
  letI : IsProper (π ∣_ U) := IsLocalAtTarget.restrict (P := @IsProper) inferInstance U
  letI : Surjective (π ∣_ U) := IsLocalAtTarget.restrict (P := @Surjective) inferInstance U
  letI : IsIso (π ∣_ U).c := ProperIsoComponents.restrict_c_isIso π U
  have hinj : Function.Injective (π ∣_ U).base := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : π.base x.val = π.base y.val := by
      calc
        π.base x.val = ((π ∣_ U).base x).val := (morphismRestrict_base_coe π U x).symm
        _ = ((π ∣_ U).base y).val := congrArg Subtype.val hxy
        _ = π.base y.val := morphismRestrict_base_coe π U y
    have hfiber := pointFiber_subsingleton X Y π hπ hbir S hS (π.base x.val)
      (hconnected _) (hU _ x.property)
    exact hfiber rfl hxy'.symm
  exact ProperIsoComponents.isIso_of_bijective (π ∣_ U)
    ⟨hinj, (inferInstance : Surjective (π ∣_ U)).surj⟩

end KltDP.Geometry.ProperBirationalOffContractedSupport
