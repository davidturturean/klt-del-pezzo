import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import KltDP.Geometry.ProjectiveSpaceTupleMorphism

/-!
# Normalized coordinates of original invertible-sheaf sections

On an original atlas chart where a selected section does not vanish, its
coefficient is a unit. Dividing the original section coefficients by that
unit gives a tuple normalized at the selected index. The actual transition
unit between two frames proves the exact projective scaling identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing TransitionUnitExtraction InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- The coefficient of the original section on an original subopen of an atlas chart. -/
def coefficient (s : L.obj.sections) (i : L.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i) : Γ(X, W) :=
  chartEquiv X L.obj L.localTrivializations i hWi (s.val (op W))

theorem coefficient_restrict (s : L.obj.sections) (i : L.localTrivializations.I)
    {V W : X.Opens} (hVW : V ≤ W) (hWi : W ≤ L.localTrivializations.X i) :
    res X hVW (coefficient L s i hWi) = coefficient L s i (hVW.trans hWi) := by
  exact (chartEquiv_restrict X L.obj L.localTrivializations i hVW hWi
    (s.val (op W))).symm.trans
      (congrArg (chartEquiv X L.obj L.localTrivializations i (hVW.trans hWi))
        (s.property (homOfLE hVW).op))

/-- The actual coefficient is a unit wherever the original section is nonvanishing. -/
theorem coefficient_isUnit (s : L.obj.sections) (i : L.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i)
    (hWs : W ≤ nonvanishingOpen X L s) : IsUnit (coefficient L s i hWi) := by
  let a := chartCoefficient X L.obj L.localTrivializations s i
  have hWa : W ≤ X.basicOpen a := by
    rw [← chart_inf_nonvanishingOpen X L s L.localTrivializations i]
    exact le_inf hWi hWs
  have hu := (RingedSpace.isUnit_res_basicOpen X.toRingedSpace a).map (res X hWa)
  change IsUnit (res X hWa (res X (X.basicOpen_le a) a)) at hu
  rw [res_res] at hu
  have hc : res X hWi a = coefficient L s i hWi :=
    chartCoefficient_restrict X L.obj L.localTrivializations s i hWi
  exact (congrArg IsUnit hc).mp hu

variable {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

/-- The original normalized tuple on a subopen where its selected denominator is a unit. -/
def coordinates (i : L.localTrivializations.I) {W : X.Opens}
    (hWi : W ≤ L.localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m)) (j : Fin (n + 1)) : Γ(X, W) :=
  (((coefficient_isUnit L (s m) i hWi hWm).unit)⁻¹ : Γ(X, W)ˣ) *
    coefficient L (s j) i hWi

theorem coordinates_self (i : L.localTrivializations.I) {W : X.Opens}
    (hWi : W ≤ L.localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m)) : coordinates L s i hWi m hWm m = 1 := by
  let d : Γ(X, W)ˣ := (coefficient_isUnit L (s m) i hWi hWm).unit
  exact (congrArg (fun a : Γ(X, W) => (d⁻¹ : Γ(X, W)ˣ) * a)
    (coefficient_isUnit L (s m) i hWi hWm).unit_spec.symm).trans (Units.inv_mul d)

theorem denominator_mul_coordinates (i : L.localTrivializations.I) {W : X.Opens}
    (hWi : W ≤ L.localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m)) (j : Fin (n + 1)) :
    coefficient L (s m) i hWi * coordinates L s i hWi m hWm j =
      coefficient L (s j) i hWi := by
  let d : Γ(X, W)ˣ := (coefficient_isUnit L (s m) i hWi hWm).unit
  exact (congrArg (fun a : Γ(X, W) => a * ((d⁻¹ : Γ(X, W)ˣ) *
    coefficient L (s j) i hWi))
    (coefficient_isUnit L (s m) i hWi hWm).unit_spec.symm).trans
      (Units.mul_inv_cancel_left d (coefficient L (s j) i hWi))

/-- Restricting the normalized original coordinates preserves their values. -/
theorem coordinates_restrict (i : L.localTrivializations.I) {V W : X.Opens}
    (hVW : V ≤ W) (hWi : W ≤ L.localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m)) (j : Fin (n + 1)) :
    res X hVW (coordinates L s i hWi m hWm j) =
      coordinates L s i (hVW.trans hWi) m (hVW.trans hWm) j := by
  apply (coefficient_isUnit L (s m) i (hVW.trans hWi) (hVW.trans hWm)).mul_left_cancel
  rw [denominator_mul_coordinates,
    ← coefficient_restrict L (s m) i hVW hWi, ← map_mul,
    denominator_mul_coordinates, coefficient_restrict]

private theorem normalized_scale {R : Type u} [CommRing R] {I : Type*}
    (a b : I → R) (m' : I) (u v : Rˣ) (hv : (v : R) = b m')
    (t : R) (ht : ∀ j, a j = t * b j) (j : I) :
    (u⁻¹ : Rˣ) * a j = ((u⁻¹ : Rˣ) * a m') * ((v⁻¹ : Rˣ) * b j) := by
  rw [ht j, ht m', ← hv]
  symm
  calc
    _ = ((u⁻¹ : Rˣ) : R) * t * ((v : R) * (v⁻¹ : Rˣ)) * b j := by ring
    _ = _ := by rw [Units.mul_inv, mul_one, mul_assoc]

/-- The exact projective scaling identity comes from the original frame transition. -/
theorem coordinates_scale (i i' : L.localTrivializations.I) {W : X.Opens}
    (hWi : W ≤ L.localTrivializations.X i) (hWi' : W ≤ L.localTrivializations.X i')
    (m m' : Fin (n + 1)) (hWm : W ≤ nonvanishingOpen X L (s m))
    (hWm' : W ≤ nonvanishingOpen X L (s m')) (j : Fin (n + 1)) :
    coordinates L s i hWi m hWm j =
      coordinates L s i hWi m hWm m' * coordinates L s i' hWi' m' hWm' j := by
  let t := transitionUnitOn X L.obj L.localTrivializations i i' hWi hWi'
  apply normalized_scale
    (fun r => coefficient L (s r) i hWi) (fun r => coefficient L (s r) i' hWi') m'
    (coefficient_isUnit L (s m) i hWi hWm).unit
    (coefficient_isUnit L (s m') i' hWi' hWm').unit
    (coefficient_isUnit L (s m') i' hWi' hWm').unit_spec (t : Γ(X, W))
  intro r
  exact (KltDP.Module.transitionUnit_mul_apply
    (chartEquiv X L.obj L.localTrivializations i' hWi')
    (chartEquiv X L.obj L.localTrivializations i hWi) ((s r).val (op W))).symm

end KltDP.Geometry.LinearSystemMorphism
