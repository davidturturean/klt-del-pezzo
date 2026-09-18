import KltDP.Geometry.PrimeCurveClosedImage
import KltDP.Geometry.SelectedPrimeCurveCartierUnion
import KltDP.Geometry.SplitCartierPullbackReducedUnion

/-!
# The two actual prime curves in a split original curve inverse image

Both labeled maps are the original coproduct injections followed by the
inverse splitting and original ambient projection. Their actual closed
images are distinct disjoint prime curves. The resulting finite set has
cardinality two and exactly the original full inverse-image union.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.SplitPrimeCurveImages

open NormalProjectiveSurface SplitAmbientPullbackCopies

variable {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    (π : T.toScheme ⟶ S.toScheme) (C : S.PrimeCurve)
    (q : pullback π C.inclusion ≅ C.toScheme ⨿ C.toScheme)

/-- The actual prime-curve image of each labeled ambient map. -/
def copyCurve (ε : Bool) : T.PrimeCurve :=
  C.closedImage (T := T) (ambientCopy π C.inclusion q ε)

@[simp] theorem coe_copyCurve (ε : Bool) :
    (copyCurve π C q ε : Set T.toScheme) = Set.range (ambientCopy π C.inclusion q ε).base := rfl

/-- The actual image curve scheme retains its original source scheme. -/
def copyCurveSourceIso (ε : Bool) : (copyCurve π C q ε).toScheme ≅ C.toScheme :=
  C.closedImageSourceIso (T := T) (ambientCopy π C.inclusion q ε)

@[reassoc] theorem copyCurveSourceIso_hom_map (ε : Bool) :
    (copyCurveSourceIso π C q ε).hom ≫ ambientCopy π C.inclusion q ε =
      (copyCurve π C q ε).inclusion :=
  C.closedImageSourceIso_hom_map (T := T) (ambientCopy π C.inclusion q ε)

/-- The two actual prime-curve images are disjoint. -/
theorem copyCurve_disjoint :
    Disjoint (copyCurve π C q false : Set T.toScheme) (copyCurve π C q true : Set T.toScheme) :=
  ambientCopy_disjoint π C.inclusion q

theorem copyCurve_false_ne_true : copyCurve π C q false ≠ copyCurve π C q true := by
  intro h
  have hd := copyCurve_disjoint π C q
  rw [h] at hd
  obtain ⟨x, hx⟩ := (copyCurve π C q true).nonempty
  exact Set.disjoint_left.mp hd hx hx

/-- The actual pair of lifted prime curves. -/
def copyCurves : Finset T.PrimeCurve := by
  classical
  exact {copyCurve π C q false, copyCurve π C q true}

theorem copyCurve_mem (ε : Bool) : copyCurve π C q ε ∈ copyCurves π C q := by
  classical
  cases ε <;> simp [copyCurves]

theorem copyCurves_card : (copyCurves π C q).card = 2 := by
  classical
  exact Finset.card_pair (copyCurve_false_ne_true π C q)

theorem copyCurves_pairwise :
    ((copyCurves π C q : Finset T.PrimeCurve) : Set T.PrimeCurve).Pairwise
      (fun P Q => Disjoint (P : Set T.toScheme) (Q : Set T.toScheme)) := by
  classical
  rw [copyCurves, Finset.coe_pair, Set.pairwise_pair]
  intro _
  exact ⟨copyCurve_disjoint π C q, (copyCurve_disjoint π C q).symm⟩

/-- The actual selected pair has exactly the same closed union as the two original ambient copies. -/
theorem copyCurves_union :
    T.selectedPrimeClosedUnion (copyCurves π C q) =
      SplitCartierPullbackReducedUnion.copyUnion π C.inclusion q := by
  classical
  apply Closeds.ext
  change (⋃ P ∈ ({copyCurve π C q false, copyCurve π C q true} : Finset T.PrimeCurve),
      (P : Set T.toScheme)) =
    (copyCurve π C q false : Set T.toScheme) ∪ (copyCurve π C q true : Set T.toScheme)
  ext x
  simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton, Set.mem_union]
  constructor
  · rintro ⟨P, (rfl | rfl), hx⟩
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨_, Or.inl rfl, hx⟩
    · exact ⟨_, Or.inr rfl, hx⟩

end KltDP.Geometry.SplitPrimeCurveImages

#print axioms KltDP.Geometry.SplitPrimeCurveImages.copyCurves_card
#print axioms KltDP.Geometry.SplitPrimeCurveImages.copyCurves_union

