import KltDP.Geometry.RationalTreePicardMatching
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.Geometry.InvertibleSheaf

/-!
# The affine sheaf of a tree branch-matching module

The base scheme is literally Spec of the component-ring equalizer, and the
module sheaf is literally the tilde of the twisted matching module. The
constructed linear equivalence and existing tilde functor prove an actual
isomorphism to its structure-sheaf unit. This does not identify an arbitrary
nodal curve with this affine scheme or descend an arbitrary invertible sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {k V : Type u} [CommRing k] (G : SimpleGraph V)
  (R : V → Type u) [∀ v, CommRing (R v)] [∀ v, Algebra k (R v)]
  (ev : ∀ d : G.Dart, R d.fst →ₐ[k] k) (g : G.Dart → kˣ)

/-- The original affine sheaf associated to the twisted matching module. -/
def matchingSheaf : (Spec (CommRingCat.of (matchingRing G R ev))).Modules :=
  (ModuleCat.of (matchingRing G R ev) (matchingSections G R ev g)).tilde

/-- The actual matching sheaf is trivial when its branch graph is a tree. -/
def treeMatchingSheafUnitIso (hG : G.IsTree)
    (hreverse : ∀ d : G.Dart, g d.symm = (g d)⁻¹) (root : V) :
    matchingSheaf G R ev g ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (matchingRing G R ev))).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of (matchingRing G R ev) (matchingSections G R ev g))
    (N := ModuleCat.of (matchingRing G R ev) (matchingRing G R ev))
    (treeMatchingLinearEquiv G R ev g hG hreverse root) ≪≫
      AffineModuleTilde.unitIso (matchingRing G R ev)

/-- Invertibility follows from the proved original module-sheaf isomorphism. -/
def treeMatchingInvertibleSheaf (hG : G.IsTree)
    (hreverse : ∀ d : G.Dart, g d.symm = (g d)⁻¹) (root : V) :
    InvertibleSheaf (Spec (CommRingCat.of (matchingRing G R ev))) :=
  InvertibleSheaf.ofIso
    (InvertibleSheaf.trivial (Spec (CommRingCat.of (matchingRing G R ev))))
    (treeMatchingSheafUnitIso G R ev g hG hreverse root).symm

end KltDP.Geometry.RationalTreePicard
