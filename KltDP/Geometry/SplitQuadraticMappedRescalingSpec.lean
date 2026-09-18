import KltDP.Geometry.SplitQuadraticMappedRescaling

/-!
# Actual affine split-cover squares under the original transition map

Apply the spectrum functor to the proved original algebra equations. Both
components, the inverse CRT map, and the forward CRT map are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

open QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original coefficient-and-rescaling transition intertwines the actual affine splittings. -/
theorem splitQuadraticSpecIso_mappedRescale (f : R →+* S) (a : Rˣ) (b v : Sˣ)
    (h : f ((a : R) ^ 2) = (v : S) ^ 2 * (b : S) ^ 2)
    (ha : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticSpecIso b hS).inv ≫
        mappedRescaleMap f ((a : R) ^ 2) ((b : S) ^ 2) v h =
      coprod.map (Spec.map (CommRingCat.ofHom f))
        (Spec.map (CommRingCat.ofHom f)) ≫ (splitQuadraticSpecIso a hR).inv := by
  apply coprod.hom_ext
  · simp only [splitQuadraticSpecIso_inl_assoc,
      coprod.inl_map_assoc, splitQuadraticSpecIso_inl]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h : SplitQuadraticAlgebra a →+* S =>
      Spec.map (CommRingCat.ofHom h))
      (splitQuadraticEvalPositive_mappedRescale f a b v h ha hR hS)
  · simp only [splitQuadraticSpecIso_inr_assoc,
      coprod.inr_map_assoc, splitQuadraticSpecIso_inr]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h : SplitQuadraticAlgebra a →+* S =>
      Spec.map (CommRingCat.ofHom h))
      (splitQuadraticEvalNegative_mappedRescale f a b v h ha hR hS)

/-- The forward square uses that same original transition, without choosing a new chart map. -/
theorem splitQuadraticSpecIso_hom_mappedRescale (f : R →+* S) (a : Rˣ) (b v : Sˣ)
    (h : f ((a : R) ^ 2) = (v : S) ^ 2 * (b : S) ^ 2)
    (ha : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    mappedRescaleMap f ((a : R) ^ 2) ((b : S) ^ 2) v h ≫
        (splitQuadraticSpecIso a hR).hom =
      (splitQuadraticSpecIso b hS).hom ≫
        coprod.map (Spec.map (CommRingCat.ofHom f))
          (Spec.map (CommRingCat.ofHom f)) := by
  have hs := congrArg
    (fun t => (splitQuadraticSpecIso b hS).hom ≫ t ≫
      (splitQuadraticSpecIso a hR).hom)
    (splitQuadraticSpecIso_mappedRescale f a b v h ha hR hS)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hs

/-- Both actual root-evaluation components lie over the original base identity. -/
theorem splitQuadraticSpecIso_inv_toBase (a : Rˣ) (hR : IsUnit (2 : R)) :
    (splitQuadraticSpecIso a hR).inv ≫ toBase ((a : R) ^ 2) =
      coprod.desc (𝟙 (Spec (.of R))) (𝟙 (Spec (.of R))) := by
  apply coprod.hom_ext
  · simp only [splitQuadraticSpecIso_inl_assoc, coprod.inl_desc]
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact (splitQuadraticEvalPositive a hR).commutes r
  · simp only [splitQuadraticSpecIso_inr_assoc, coprod.inr_desc]
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact (splitQuadraticEvalNegative a hR).commutes r

end KltDP.Geometry
