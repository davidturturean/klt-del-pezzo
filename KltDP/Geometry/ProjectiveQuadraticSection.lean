import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.TransitionUnitTensor
import KltDP.Geometry.ProperGlobalSectionsFinite

/-!
# The actual section defined by a homogeneous quadratic polynomial

On the original standard projective charts the coefficient is q(z/z_i).
Homogeneity gives exactly the square of the original degree-one cocycle.
This constructs the section of O(2) without any reducedness or smoothness
assumption on its zero scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveQuadraticSection

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing ProjectiveSpaceDegreeOneSheaf
  ProjectiveCoordinateSectionBasicOpen ProjectiveCoordinateSectionRelations

variable (k : Type u) [Field k] (n : ℕ)

/-- The original base-field scalars on an arbitrary projective open. -/
def scalars (W : (projectiveSpace k n).Opens) : k →+* Γ(projectiveSpace k n, W) :=
  (res (projectiveSpace k n) (le_top : W ≤ ⊤)).comp
    (baseFieldToGlobalSections (projectiveSpaceToSpec k n))

theorem scalars_restrict {V W : (projectiveSpace k n).Opens} (h : V ≤ W) :
    (res (projectiveSpace k n) h).comp (scalars k n W) = scalars k n V := by
  ext a
  exact res_res (projectiveSpace k n) h le_top _

/-- The literal polynomial q evaluated in the original chart ratios. -/
def coefficient (q : MvPolynomial (Fin (n + 1)) k) (i : Fin (n + 1)) :
    Γ(projectiveSpace k n, standardOpen k n i) :=
  MvPolynomial.eval₂Hom (scalars k n (standardOpen k n i))
    (coordinateSection k n i) q

theorem coefficient_transition (q : MvPolynomial (Fin (n + 1)) k)
    (hq : q.IsHomogeneous 2) (i j : Fin (n + 1)) :
    res (projectiveSpace k n) inf_le_left (coefficient k n q i) =
      (overlapUnit k n (ULift.up i) (ULift.up j) :
        Γ(projectiveSpace k n, standardOpen k n i ⊓ standardOpen k n j)) ^ 2 *
          res (projectiveSpace k n) inf_le_right (coefficient k n q j) := by
  unfold coefficient
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom,
    scalars_restrict, scalars_restrict]
  change MvPolynomial.eval₂ _ _ q = _
  have heq : (fun a => res (projectiveSpace k n)
      (inf_le_left : standardOpen k n i ⊓ standardOpen k n j ≤ standardOpen k n i)
      (coordinateSection k n i a)) =
      (fun a => (overlapUnit k n (ULift.up i) (ULift.up j) :
        Γ(projectiveSpace k n, standardOpen k n i ⊓ standardOpen k n j)) *
          res (projectiveSpace k n) inf_le_right (coordinateSection k n j a)) := by
    funext a
    exact coordinateSection_relation_mul k n i j a
  rw [heq]
  exact homogeneous_eval₂_scale hq _ _ _

/-- The original degree-one transition cocycle squared. -/
abbrev quadraticUnits := productUnits (projectiveSpace k n) (chart k n)
  (overlapUnit k n) (overlapUnit k n)

theorem quadraticUnits_isCocycle :
    IsCocycle (projectiveSpace k n) (chart k n) (quadraticUnits k n) :=
  productUnits_isCocycle _ _ _ _ (overlapUnit_isCocycle k n) (overlapUnit_isCocycle k n)

/-- The actual degree-two invertible sheaf on the original projective space. -/
def degreeTwo : InvertibleSheaf (projectiveSpace k n) :=
  invertibleSheaf _ (chart k n) (quadraticUnits k n)
    (quadraticUnits_isCocycle k n) (chart_cover k n)

/-- This is the actual tensor square of the original O(1). -/
def degreeTwoTensorIso :
    letI := Scheme.Modules.monoidalCategory (projectiveSpace k n)
    (degreeOne k n).obj ⊗ (degreeOne k n).obj ≅ (degreeTwo k n).obj :=
  tensorIso _ (chart k n) (overlapUnit k n) (overlapUnit k n)
    (overlapUnit_isCocycle k n) (overlapUnit_isCocycle k n) (chart_cover k n)

/-- The original quadratic polynomial as a genuine global section. -/
def quadraticSection (q : MvPolynomial (Fin (n + 1)) k) (hq : q.IsHomogeneous 2) :
    (degreeTwo k n).obj.sections :=
  globalSectionOfCoordinates _ (chart k n) (quadraticUnits k n)
    (fun i => coefficient k n q i.down) (fun i j => by
      simpa only [quadraticUnits, productUnits_val, pow_two] using
        coefficient_transition k n q hq i.down j.down)

/-- Its original standard frame reads exactly q(z/z_i). -/
theorem section_frame (q : MvPolynomial (Fin (n + 1)) k) (hq : q.IsHomogeneous 2)
    (i : ULift.{u} (Fin (n + 1))) {W : (projectiveSpace k n).Opens}
    (hW : W ≤ chart k n i) :
    trivialization _ (chart k n) (quadraticUnits k n) (quadraticUnits_isCocycle k n) i hW
      ((quadraticSection k n q hq).val (op W)) =
        res (projectiveSpace k n) hW (coefficient k n q i.down) :=
  trivialization_globalSectionOfCoordinates _ _ _ _ _ _ i hW

end KltDP.Geometry.ProjectiveQuadraticSection

#print axioms KltDP.Geometry.ProjectiveQuadraticSection.coefficient_transition
#print axioms KltDP.Geometry.ProjectiveQuadraticSection.degreeTwoTensorIso
#print axioms KltDP.Geometry.ProjectiveQuadraticSection.section_frame
