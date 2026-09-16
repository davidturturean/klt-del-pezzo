import KltDP.Geometry.RegularLocalEquiv

/-!
# Openness of the regular locus on actual open covers

Open immersions identify the actual stalks at corresponding points. Hence
the regular locus is the union of the images of the regular loci of the
members of any scheme open cover. Its openness can therefore be checked on
that cover, and in particular on an affine open cover.

These results are local-to-global adapters. Openness on the affine schemes
is an explicit hypothesis; no general regularity-openness theorem is assumed.
Closedness of the singular locus then follows by taking the complement.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u v

namespace KltDP.Geometry

/-- The regular locus is recovered from the actual regular loci and actual
open-immersion maps of a scheme open cover. -/
theorem regularLocus_eq_iUnion_image_of_openCover {X : Scheme.{u}}
    (𝒰 : Scheme.OpenCover.{v, u} X) :
    regularLocus X = ⋃ i, (𝒰.map i).base '' regularLocus (𝒰.obj i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine Set.mem_iUnion.mpr ⟨𝒰.f x, y, ?_, hy⟩
    rw [regularLocus_preimage_of_isOpenImmersion (𝒰.map (𝒰.f x))]
    change (𝒰.map (𝒰.f x)).base y ∈ regularLocus X
    rwa [hy]
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    rw [regularLocus_preimage_of_isOpenImmersion (𝒰.map i)] at hy
    exact hy

/-- Openness of the actual regular locus is local on any scheme open cover. -/
theorem isOpen_regularLocus_iff_of_openCover {X : Scheme.{u}}
    (𝒰 : Scheme.OpenCover.{v, u} X) :
    IsOpen (regularLocus X) ↔ ∀ i, IsOpen (regularLocus (𝒰.obj i)) := by
  constructor
  · intro h i
    rw [regularLocus_preimage_of_isOpenImmersion (𝒰.map i)]
    exact h.preimage (𝒰.map i).continuous
  · intro h
    rw [regularLocus_eq_iUnion_image_of_openCover 𝒰]
    exact isOpen_iUnion fun i ↦
      (𝒰.map i).isOpenEmbedding.isOpenMap _ (h i)

/-- Openness proved on every member of an actual open cover gives openness
on the scheme. The local openness proofs remain required inputs. -/
theorem isOpen_regularLocus_of_openCover {X : Scheme.{u}}
    (𝒰 : Scheme.OpenCover.{v, u} X)
    (h : ∀ i, IsOpen (regularLocus (𝒰.obj i))) :
    IsOpen (regularLocus X) :=
  (isOpen_regularLocus_iff_of_openCover 𝒰).mpr h

/-- An affine open cover reduces regular-locus openness to its actual affine
schemes, with their original structure-sheaf stalks. -/
theorem isOpen_regularLocus_iff_of_affineOpenCover {X : Scheme.{u}}
    (𝒰 : Scheme.AffineOpenCover.{v, u} X) :
    IsOpen (regularLocus X) ↔
      ∀ i, IsOpen (regularLocus (Spec (𝒰.obj i))) :=
  isOpen_regularLocus_iff_of_openCover 𝒰.openCover

/-- The two loci are complements, so singular-locus closedness is precisely
regular-locus openness. -/
theorem isClosed_singularLocus_iff_isOpen_regularLocus (X : Scheme.{u}) :
    IsClosed (singularLocus X) ↔ IsOpen (regularLocus X) := by
  rw [singularLocus_eq_compl_regularLocus, isClosed_compl_iff]

/-- Closedness of the singular locus follows once regular-locus openness has
been proved on every member of an actual open cover. -/
theorem isClosed_singularLocus_of_openCover {X : Scheme.{u}}
    (𝒰 : Scheme.OpenCover.{v, u} X)
    (h : ∀ i, IsOpen (regularLocus (𝒰.obj i))) :
    IsClosed (singularLocus X) :=
  (isClosed_singularLocus_iff_isOpen_regularLocus X).mpr
    (isOpen_regularLocus_of_openCover 𝒰 h)

/-- Affine regularity-openness results imply closedness of the scheme's
singular locus after transport along its actual affine open cover. -/
theorem isClosed_singularLocus_of_affineOpenCover {X : Scheme.{u}}
    (𝒰 : Scheme.AffineOpenCover.{v, u} X)
    (h : ∀ i, IsOpen (regularLocus (Spec (𝒰.obj i)))) :
    IsClosed (singularLocus X) :=
  isClosed_singularLocus_of_openCover 𝒰.openCover h

end KltDP.Geometry
