import KltDP.Geometry.AffineSmoothLocalizationTransport
import KltDP.Geometry.RegularLocalDimensionTwo

/-! Stacks 0B8X, full Lemma 33.25.8, frozen revision
 a04446e57ec1fbc252a871afcec7752fb2807b14.
 Isolated literal admitted by admission_review/ROOT_CANDIDATE_ADMISSION_DECISION.json.
 Native smoothness uses the original affine ring maps. The regular locus is
 the literal maximal-ideal-generator definition; openness and density are retained. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Literature.Stacks

axiom regular_smooth_loci_perfect_literal
    (k : Type u) [Field k] [PerfectField k]
    (X : Scheme.{u}) [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    let L : Set X := {x |
      KltDP.Geometry.AffineSmoothLocalizationTransport.algebraSmoothAt f x}
    let G : Set X := {x |
      KltDP.Geometry.RegularLocalByGenerators (X.presheaf.stalk x)}
    L = G ∧ IsOpen L ∧ Dense L

end KltDP.Literature.Stacks
#check @KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal
#print axioms KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal
