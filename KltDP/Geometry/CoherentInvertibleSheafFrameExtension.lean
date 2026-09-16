import KltDP.Geometry.InvertibleSheafFrameSectionExtension
import KltDP.Geometry.CoherentQuasicoherent

/-!
# Actual coherent twisted section extension on a frame

The literal coherent predicate supplies quasicoherence through the proved
adapter, then the actual framed extension theorem supplies every sufficiently
high tensor twist. The frame remains explicit. No Serre ampleness witness or
global gluing for a nontrivial invertible sheaf is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafFrameSectionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance coherentFrameExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame

variable {X : Scheme.{u}} (M : X.Modules) (L : InvertibleSheaf X)

/-- The same actual chart extension for the project's literal coherent
module predicate, with quasicoherence derived rather than assumed. -/
theorem eventually_exists_twisted_extension_of_coherent [IsCoherentModule M]
    (hX : IsCompact (Set.univ : Set X)) (hXqs : IsQuasiSeparated (Set.univ : Set X))
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (s : L.obj.sections)
    (t : M.val.obj (op (X.basicOpen (frameCoefficient L e s)))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ v : (M ⊗ (power L n).obj).val.obj (op ⊤),
        (M ⊗ (power L n).obj).val.map
            (homOfLE (X.basicOpen_le (frameCoefficient L e s))).op v =
          (rightTwistMap M L s n).val.app (op (X.basicOpen (frameCoefficient L e s))) t := by
  letI : M.IsQuasicoherent := CoherentQuasicoherent.isQuasicoherent_of_isCoherentModule M
  exact eventually_exists_twisted_extension M L hX hXqs e s t


end KltDP.Geometry.InvertibleSheafFrameSectionExtension
