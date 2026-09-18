import KltDP.Compatibility.BirationalRationality
import KltDP.Geometry.RationalMapGraphBirational

/-!
# Both projections of the original partial-isomorphism graph

The inverse of the given open isomorphism followed by the original graph
lift is a dominant section over the original target open. Hence the actual
second graph projection, as well as the first, is proper and birational.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- The graph of an actual dense-open isomorphism over the base gives two
original proper birational morphisms, retaining their base equation. -/
theorem exists_proper_birational_graph_of_partialIso
    {S T B : Scheme.{u}} [IsIntegral S] [IsIntegral T] [IsNoetherian S]
    (s : S ⟶ B) (t : T ⟶ B) [IsProper s] [IsProper t]
    (φ : S.PartialIso T) (hφ : φ.IsOver s t) :
    ∃ (G : Scheme.{u}) (p : G ⟶ S) (q : G ⟶ T) (hG : IsIntegral G),
      letI := hG
      IsProper p ∧ IsProper q ∧ IsBirationalScheme p ∧
        IsBirationalScheme q ∧ q ≫ t = p ≫ s := by
  let f := φ.toPartialMap
  have hf : f.hom ≫ t = f.domain.ι ≫ s := by
    simpa only [f, Scheme.PartialIso.toPartialMap_hom, Category.assoc] using hφ
  let G := RationalMapGraphClosure.model s t f hf
  let p : G ⟶ S := RationalMapGraphClosure.projection s t f hf
  let q : G ⟶ T := RationalMapGraphClosure.extension s t f hf
  letI : IsIntegral G := RationalMapGraphClosure.model_isIntegral s t f hf
  letI : IsProper p := RationalMapGraphClosure.projection_isProper s t f hf
  have hqt : q ≫ t = p ≫ s := RationalMapGraphClosure.extension_comp s t f hf
  letI : IsProper (q ≫ t) := by rw [hqt]; infer_instance
  letI : IsProper q := IsProper.of_comp_of_isSeparated q t
  let j : φ.target.toScheme ⟶ G :=
    φ.iso.inv ≫ RationalMapGraphClosure.domainLift s t f hf
  letI : IsDominant j := inferInstance
  have hj : j ≫ q = φ.target.ι := by
    dsimp only [j, q]
    rw [Category.assoc, RationalMapGraphClosure.domainLift_extension]
    change φ.iso.inv ≫ (φ.iso.hom ≫ φ.target.ι) = φ.target.ι
    exact φ.iso.inv_hom_id_assoc _
  letI : Nonempty φ.target.toScheme := by
    obtain ⟨x, hx⟩ := φ.dense_target.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI : IsIso (q ∣_ φ.target) :=
    DominantOpenSection.isIso_restrict_of_dominant_section q φ.target j hj
  exact ⟨G, p, q, inferInstance, inferInstance, inferInstance,
    RationalMapGraphClosure.projection_isBirationalScheme s t f hf,
    isBirationalScheme_of_isIso_restrict q φ.target, hqt⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_proper_birational_graph_of_partialIso
#print axioms KltDP.Geometry.exists_proper_birational_graph_of_partialIso
