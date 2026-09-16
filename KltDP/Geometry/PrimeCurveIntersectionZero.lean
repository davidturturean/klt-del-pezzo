import KltDP.Geometry.PrimeCurveIntersectionDegreeSum

/-!
# The zero criterion for the prime-curve intersection number

`C·D = 0` exactly when the intersection scheme `C ∩ D` is empty: the number is the `k`-dimension of
`Γ(C ∩ D, O)`, which is finite (02O6); it vanishes iff the ring of global functions is trivial, and a
nonempty scheme has a nontrivial ring of global functions (its stalks are local rings).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- A scheme whose ring of global functions is trivial is empty. -/
theorem scheme_isEmpty_of_subsingleton_sections (Z : Scheme.{u}) (h : Subsingleton Γ(Z, ⊤)) :
    IsEmpty Z := by
  refine ⟨fun x => ?_⟩
  have h10 : (1 : Γ(Z, ⊤)) = 0 := Subsingleton.elim _ _
  have := congrArg (Z.presheaf.germ ⊤ x trivial) h10
  rw [map_one, map_zero] at this
  exact one_ne_zero this

/-- **The zero criterion**: `C·D = 0` iff `C ∩ D = ∅`. -/
theorem intersectionDegree_eq_zero_iff :
    C.intersectionDegree D hD hC = 0 ↔ IsEmpty (C.intersectionScheme D hD hC) := by
  constructor
  · intro h
    letI := Module.compHom Γ(C.intersectionScheme D hD hC, ⊤)
      (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
    haveI : Module.Finite k Γ(C.intersectionScheme D hD hC, ⊤) :=
      finite_sections_of_hZero (C.intersectionToSpec D hD hC)
        (C.intersectionDegree_finiteDimensional D hD hC)
    have hfin : Module.finrank k Γ(C.intersectionScheme D hD hC, ⊤) = 0 :=
      (C.intersectionDegree_eq_finrank_sections D hD hC).symm.trans h
    exact scheme_isEmpty_of_subsingleton_sections _ (Module.finrank_zero_iff.mp hfin)
  · intro h
    haveI : IsEmpty (effectiveCartierScheme C.toScheme (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC)) := h
    exact effectiveCartierDegree_eq_zero_of_isEmpty C.toScheme (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
