import KltDP.Geometry.CoherentQuasicoherent
import KltDP.Geometry.InvertibleSheafSectionExtension

/-!
# Literal coherent sections extend into original line-sheaf powers

The constructed coherent-to-quasicoherent comparison applies the global
extension theorem to the original literal coherent module. The original
symmetric tensor comparison also gives the left-twist order used by the
existing Serre ampleness predicate. No quasicoherence or section-extension
witness is added as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafCoherentSectionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance coherentExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance coherentExtensionSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X) (M : X.Modules) (s : L.obj.sections)

/-- The actual original multiplication map in the left-twist order. -/
def leftTwistMap (n : ℕ) : M ⟶ (power L n).obj ⊗ M :=
  rightTwistMap M L s n ≫ (β_ M (power L n).obj).hom

/-- Literal coherence supplies the required QC structure on the same original
module, so every sufficiently high original right twist admits an extension. -/
theorem eventually_exists_twisted_extension [IsCoherentModule M]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (t : M.val.obj (op (nonvanishingOpen X L s))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ v : (M ⊗ (power L n).obj).val.obj (op ⊤),
        (M ⊗ (power L n).obj).val.map
            (homOfLE (show nonvanishingOpen X L s ≤ ⊤ from le_top)).op v =
          (rightTwistMap M L s n).val.app (op (nonvanishingOpen X L s)) t := by
  letI : M.IsQuasicoherent :=
    CoherentQuasicoherent.isQuasicoherent_of_isCoherentModule M
  exact InvertibleSheafSectionExtension.eventually_exists_twisted_extension L M s hX hXqs t

/-- The same actual extensions in the tensor order used by Serre ampleness. -/
theorem eventually_exists_left_twisted_extension [IsCoherentModule M]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (t : M.val.obj (op (nonvanishingOpen X L s))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ v : ((power L n).obj ⊗ M).val.obj (op ⊤),
        ((power L n).obj ⊗ M).val.map
            (homOfLE (show nonvanishingOpen X L s ≤ ⊤ from le_top)).op v =
          (leftTwistMap L M s n).val.app (op (nonvanishingOpen X L s)) t := by
  obtain ⟨N, hN⟩ := eventually_exists_twisted_extension L M s hX hXqs t
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨v, hv⟩ := hN n hn
  let e : M ⊗ (power L n).obj ≅ (power L n).obj ⊗ M := β_ M (power L n).obj
  refine ⟨e.hom.val.app (op ⊤) v, ?_⟩
  exact (PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (show nonvanishingOpen X L s ≤ ⊤ from le_top)).op v).symm.trans
      (congrArg (e.hom.val.app (op (nonvanishingOpen X L s))) hv)

end KltDP.Geometry.InvertibleSheafCoherentSectionExtension
