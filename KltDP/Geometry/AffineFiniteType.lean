import KltDP.Geometry.ProjectiveFiniteType

/-!
# The actual base algebra on an affine open

For an affine open `U` of a scheme over `Spec R`, the base-to-sections map
is the homomorphism corresponding under `Spec` to the actual composite
`Spec Γ(X,U) → X → Spec R`. The algebra structure on `Γ(X,U)` is defined
by this homomorphism and its structural map is recorded explicitly.

When the given scheme structure morphism is locally of finite type, this
algebra is of finite type. Restriction to a smaller affine open commutes
with the same base map and is an algebra homomorphism for these structures.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry

/-- The homomorphism from the actual base ring to the sections of an affine
open, obtained from its canonical open immersion into the given scheme. -/
def baseToAffineSectionsMap {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} (hU : IsAffineOpen U) :
    CommRingCat.of R ⟶ Γ(X, U) :=
  Spec.preimage (hU.fromSpec ≫ f)

@[simp]
theorem Spec_map_baseToAffineSectionsMap {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} (hU : IsAffineOpen U) :
    Spec.map (baseToAffineSectionsMap f hU) = hU.fromSpec ≫ f :=
  Spec.map_preimage _

/-- Affine sections are of finite type for their actual base homomorphism.
The open immersion supplies local finite type of the composite to the base. -/
theorem baseToAffineSectionsMap_finiteType {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) :
    (baseToAffineSectionsMap f hU).hom.FiniteType := by
  have hcomp : LocallyOfFiniteType (hU.fromSpec ≫ f) := inferInstance
  rw [← Spec_map_baseToAffineSectionsMap f hU] at hcomp
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hcomp

/-- The algebra structure induced by the actual map to the base. This is
a named structure, not a global instance that could select a different map. -/
abbrev affineSectionsAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra R Γ(X, U) :=
  (baseToAffineSectionsMap f hU).hom.toAlgebra

/-- Its algebra map is precisely the homomorphism corresponding to the
canonical affine-open immersion followed by the given structure morphism. -/
@[simp]
theorem affineSectionsAlgebra_algebraMap {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} (hU : IsAffineOpen U) :
    letI := affineSectionsAlgebra f hU
    algebraMap R Γ(X, U) = (baseToAffineSectionsMap f hU).hom := rfl

/-- Finite type for that exact algebra structure. -/
theorem affineSectionsAlgebra_finiteType {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := affineSectionsAlgebra f hU
    Algebra.FiniteType R Γ(X, U) :=
  baseToAffineSectionsMap_finiteType f hU

/-- Restriction to a smaller affine open commutes with the actual base map. -/
@[reassoc]
theorem baseToAffineSectionsMap_restrict {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    baseToAffineSectionsMap f hU ≫ X.presheaf.map (homOfLE h).op =
      baseToAffineSectionsMap f hV := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec_map_baseToAffineSectionsMap,
    Spec_map_baseToAffineSectionsMap, ← Category.assoc,
    hU.map_fromSpec hV (homOfLE h).op]

/-- The actual restriction on sections, viewed as an algebra homomorphism
for the two compatible structures induced by the given base map. -/
def affineSectionsRestrictAlgHom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    letI := affineSectionsAlgebra f hU
    letI := affineSectionsAlgebra f hV
    Γ(X, U) →ₐ[R] Γ(X, V) := by
  letI := affineSectionsAlgebra f hU
  letI := affineSectionsAlgebra f hV
  refine { (X.presheaf.map (homOfLE h).op).hom with commutes' := ?_ }
  intro r
  exact congrArg (fun φ : CommRingCat.of R ⟶ Γ(X, V) ↦ φ.hom r)
    (baseToAffineSectionsMap_restrict f hU hV h)

/-- The bundled algebra homomorphism has the original sheaf restriction
as its underlying ring homomorphism. -/
@[simp]
theorem affineSectionsRestrictAlgHom_toRingHom {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    letI := affineSectionsAlgebra f hU
    letI := affineSectionsAlgebra f hV
    (affineSectionsRestrictAlgHom f hU hV h).toRingHom =
      (X.presheaf.map (homOfLE h).op).hom := rfl

end KltDP.Geometry
