import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.RationalTreePicardIntrinsicNode

/-!
# The original ground field and the actual closed-stalk residue field

The scalar action is induced by the original structure morphism through
IntrinsicNodal.stalkAlgebra. Its residue scalar map is identified with the
original geometric base-to-residue-field map by full faithfulness of Spec.
Closed-point bijectivity therefore applies to this exact scalar map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ClosedPointStalkResidue

open IntrinsicNodal

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X)

/-- The actual stalk scalar map followed by the actual residue quotient. -/
theorem baseToStalkMap_residue :
    baseToStalkMap f x ≫ X.residue x = baseToResidueFieldMap f x := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec_map_baseToStalkMap, Spec_map_baseToResidueFieldMap,
    Scheme.fromSpecResidueField, Category.assoc]

/-- The canonical residue algebra uses exactly the original geometric scalar map. -/
theorem algebraMap_eq :
    letI := stalkAlgebra f x
    algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      (baseToResidueFieldMap f x).hom := by
  letI := stalkAlgebra f x
  change (IsLocalRing.residue (X.presheaf.stalk x)).comp (baseToStalkMap f x).hom =
    (baseToResidueFieldMap f x).hom
  exact congrArg (fun g : CommRingCat.of k ⟶ X.residueField x => g.hom)
    (baseToStalkMap_residue f x)

/-- At an actual closed point over an algebraically closed field, this same scalar map is bijective. -/
theorem algebraMap_bijective [IsAlgClosed k] [LocallyOfFiniteType f]
    (hclosed : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra f x
    Function.Bijective (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  letI := stalkAlgebra f x
  rw [algebraMap_eq f x]
  exact baseToResidueFieldMap_bijective f x hclosed

/-- The compatible k-algebra equivalence comes from the actual residue scalar map itself. -/
def algEquiv [IsAlgClosed k] [LocallyOfFiniteType f]
    (hclosed : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra f x
    k ≃ₐ[k] IsLocalRing.ResidueField (X.presheaf.stalk x) := by
  letI := stalkAlgebra f x
  exact AlgEquiv.ofBijective
    (Algebra.ofId k (IsLocalRing.ResidueField (X.presheaf.stalk x)))
    (algebraMap_bijective f x hclosed)

/-- The equivalence preserves the literal residue scalar map. -/
theorem algEquiv_toRingHom [IsAlgClosed k] [LocallyOfFiniteType f]
    (hclosed : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra f x
    (algEquiv f x hclosed).toRingHom =
      algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := rfl

end KltDP.Geometry.ClosedPointStalkResidue
