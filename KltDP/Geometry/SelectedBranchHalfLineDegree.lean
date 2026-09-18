import KltDP.Geometry.SelectedPrimeCartierIntersection
import KltDP.Geometry.SchemeModulePullbackTensor

/-!
# The original half-line has degree minus one on a selected minus-two curve

The actual square isomorphism restricts to the original curve, and the
existing proper-curve tensor-degree theorem computes its degree. For an
original disjoint selected curve, the selected Cartier sum has degree
equal to its actual self-intersection. Thus a selected minus-two curve
has original half-line degree minus one. Identifying the ramification
normal line with this restriction remains a separate geometric step.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance selectedBranchHalfLineDegreeMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The original square isomorphism computes twice the original restricted half-line degree. -/
theorem two_mul_restrictionDegree_of_square
    (E : CartierDivisor S.toScheme) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (C : S.PrimeCurve) :
    2 * C.restrictionDegree L = C.intersectionNumber E := by
  letI : MonoidalCategory C.toScheme.Modules := Scheme.Modules.monoidalCategory C.toScheme
  let M := pullbackInvertibleSheaf C.inclusion L
  let N := pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf S.toScheme E)
  let ε : N.obj ≅ M.obj ⊗ M.obj :=
    (schemeModulePullback C.inclusion).mapIso e.symm ≪≫
      schemeModulePullbackTensorIso C.inclusion L.obj L.obj
  have h := KltDP.AdmissionProbe.CurveTensorDegreeConsumers.lineDegree_eq_add_of_tensorIso
    C M M N ε
  change C.intersectionNumber E = C.restrictionDegree L + C.restrictionDegree L at h
  simpa only [two_mul] using h.symm

/-- The actual half-line restricts with degree minus one on an original disjoint selected minus-two curve. -/
theorem restrictionDegree_halfLine_eq_neg_one_on_selected_curve
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (C : S.PrimeCurve) (hC : C ∈ N)
    (hself : C.selfIntersectionNumber hregular = -2) :
    C.restrictionDegree L = -1 := by
  have hbranch := S.intersectionNumber_selected_disjoint_sum hregular N E hE hdisj C hC
  have htwice := S.two_mul_restrictionDegree_of_square E L e C
  rw [hbranch, hself] at htwice
  omega

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.restrictionDegree_halfLine_eq_neg_one_on_selected_curve
