import KltDP.Examples.FrobeniusNullBlocksOpen
import KltDP.Examples.FrobeniusOldChainTransversalConfiguration

/-!
# The actual reduced null-locus equation at an old-chain crossing

The original old-chain block is an open chart of the actual null locus.
Its proved crossing equation therefore gives the kernel of the original
null-locus stalk map itself. The parameters are in the original surface
stalk; no replacement divisor or assumed SNC witness is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusNullOldNodeEquation

open KltDP.Geometry KltDP.Geometry.RationalTreePicard

private theorem node_equation_of_stalkIso_factor
    {Z Y S : Scheme.{u}} [NoetherianSpace Z]
    (j : Z ⟶ Y) (ι : Y ⟶ S) (g : Z ⟶ S) (hfac : j ≫ ι = g)
    (D E : ↥(irreducibleComponents Z)) (z : Z) [IsIso (j.stalkMap z)]
    (h : TransversalCrossing g D E z) :
    RegularLocal (S.presheaf.stalk (ι.base (j.base z))) ∧
      ringKrullDim (S.presheaf.stalk (ι.base (j.base z))) = 2 ∧
      ∃ f g : S.presheaf.stalk (ι.base (j.base z)),
        Ideal.span {f, g} = maximalIdeal (S.presheaf.stalk (ι.base (j.base z))) ∧
        RingHom.ker (ι.stalkMap (j.base z)).hom = Ideal.span {f * g} := by
  subst g
  obtain ⟨hregular, hdim, f, g, hspan, hker, -, -⟩ := h
  refine ⟨hregular, hdim, f, g, hspan, ?_⟩
  have hinj : Function.Injective (j.stalkMap z).hom :=
    (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv.injective
  rwa [Scheme.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hinj] at hker

open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
  FrobeniusMultiCentreOldChain FrobeniusContractingLocusPieces
  FrobeniusNullBlocksOpen

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (hn : 2 < n)

/-- At each actual crossing of two old components, the original reduced
null locus is cut out by the product of two regular parameters. -/
theorem nullLocus_old_node_equation (i : Fin n)
    (D E : ↥(irreducibleComponents (oldChain q n a ha i))) (hDE : D ≠ E)
    (z : oldChain q n a ha i) (hzD : z ∈ D.1) (hzE : z ∈ E.1) :
    let j := oldChainToNullLocus q n a ha hproj hn i
    let ι := Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)
    RegularLocal ((multiSurface (q + 1) n a).presheaf.stalk (ι.base (j.base z))) ∧
      ringKrullDim ((multiSurface (q + 1) n a).presheaf.stalk (ι.base (j.base z))) = 2 ∧
      ∃ f g : (multiSurface (q + 1) n a).presheaf.stalk (ι.base (j.base z)),
        Ideal.span {f, g} = maximalIdeal
          ((multiSurface (q + 1) n a).presheaf.stalk (ι.base (j.base z))) ∧
        RingHom.ker (ι.stalkMap (j.base z)).hom = Ideal.span {f * g} := by
  letI : IsIso ((oldChainToNullLocus q n a ha hproj hn i).stalkMap z) :=
    blockToNullLocus_stalkMap_isIso q n a ha hproj hn (some (Sum.inr i)) z
  exact node_equation_of_stalkIso_factor _ _ _
    (oldChainToNullLocus_comp q n a ha hproj hn i) D E z
    ((oldChain_transversalConfiguration q n a ha i).crossing D E hDE z hzD hzE)

end KltDP.Examples.FrobeniusNullOldNodeEquation
