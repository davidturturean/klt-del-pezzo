import KltDP.Geometry.BirationalCartierCommonSectionRatios
import KltDP.Geometry.SchemeFunctionFieldIndependentGenerators
import KltDP.Geometry.SectionRatioBigness
import KltDP.Geometry.BignessPositivePowerReflection

/-!
# An original birational Cartier linear system gives original bigness

Original affine charts provide sufficiently many independent rational
functions. The birational system realizes them as ratios of actual global
sections of one positive Cartier multiple. The compiled monomial boxes
then prove the unchanged section-growth criterion for that multiple,
and positive-power reflection returns to the original Cartier line.

The system need only generate on the original chosen nonempty open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalSectionGrowth

open OpenPullbackLinearSystemCartierRatios LinearSystemMorphism
  InvertibleSectionNonvanishingOpen ModuleCohomology SectionMonomialGrowth

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ X) [IsOpenImmersion f]
    {k : Type u} [Field k] (b : X ⟶ Spec (CommRingCat.of k)) [IsProper b]
    (D : CartierDivisor X) {n : ℕ}
    (s : Fin (n + 1) → (cartierDivisorInvertibleSheaf X D).obj.sections)

/-- Birationality of the actual system onto its actual closed image
implies the original section-growth bigness of its original Cartier line. -/
theorem isBig_of_birational_system
    (hcover : (⨆ j, nonvanishingOpen Y (pulledLine f D) (pulledTuple f D s j)) = ⊤)
    (e : Z ⟶ projectiveSpace k n) [IsClosedImmersion e] (g : Y ⟶ Z)
    (hg : IsBirationalScheme g)
    (hcomp : g ≫ e = morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover)
    (hdim : 0 < Positivity.natDim X) :
    Positivity.IsBig b (cartierDivisorInvertibleSheaf X D) := by
  letI := functionFieldAlgebra b
  obtain ⟨d, z, hd, hdz, hz⟩ := exists_independent_functions_of_natDim_pos b hdim
  obtain ⟨m, t₀, t, hm, ht₀, ht⟩ :=
    exists_common_section_ratios f b D s hcover e g hg hcomp z
  have hind : AlgebraicIndependent k
      (fun i => cartierGlobalSectionRationalValue X (m • D) (t i) /
        cartierGlobalSectionRationalValue X (m • D) t₀) := by
    have he : (fun i => cartierGlobalSectionRationalValue X (m • D) (t i) /
        cartierGlobalSectionRationalValue X (m • D) t₀) = z := funext ht
    rw [he]
    exact hz
  have hbig : Positivity.IsBig b (cartierDivisorInvertibleSheaf X (m • D)) :=
    SectionRatioBigness.isBig_of_algebraicallyIndependent_ratios b (m • D)
      t₀ ht₀ t hind hd hdz
  have hclass : (cartierDivisorInvertibleSheaf X (m • D)).toPic =
      (cartierDivisorInvertibleSheaf X D).toPic ^ m :=
    congrArg Additive.toMul ((cartierPicardHom X).map_nsmul D m)
  exact isBig_of_toPic_eq_pow b (cartierDivisorInvertibleSheaf X D)
    (cartierDivisorInvertibleSheaf X (m • D)) m hm hclass hbig

end KltDP.Geometry.BirationalSectionGrowth
