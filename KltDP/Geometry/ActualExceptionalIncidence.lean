import KltDP.Topology.IncidenceGraphComponents
import KltDP.Geometry.ActualResolutionSingularComponentBound

/-!
# The actual exceptional incidence graph and its component count

Vertices are all original prime curves contracted by the original morphism.
Edges mean nonempty intersection of their actual carriers. Proper birationality
proves finiteness of the vertex set. The graph's connected components correspond
to connected components of the original exceptional support. For a resolution
with connected original fibers, their count bounds actual singular points.

This constructs the counting interface; acyclicity, rationality, minimality,
resolution existence, and the numerical seven-component bound remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ActualExceptionalIncidence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)

/-- All actual contracted prime curves, with no independently supplied list. -/
abbrev Vertices := {C : S.PrimeCurve // IsExceptionalCurve π C}

/-- The graph uses intersections of the original curve carriers. -/
def graph : SimpleGraph (Vertices π) :=
  NormalProjectiveSurface.curveIncidenceGraph (fun C : Vertices π => C.val)

theorem union_eq_primeSupport :
    (⋃ C : Vertices π, (C.val : Set S.toScheme)) = ActualExceptionalLocus.primeSupport π := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    exact (ActualExceptionalLocus.mem_primeSupport π x).mpr ⟨C.val, C.property, hxC⟩
  · intro hx
    obtain ⟨C, hC, hxC⟩ := (ActualExceptionalLocus.mem_primeSupport π x).mp hx
    exact Set.mem_iUnion.mpr ⟨⟨C, hC⟩, hxC⟩

theorem finite_vertices [IsProper π] (hbir : IsBirationalScheme π) : Finite (Vertices π) :=
  (exceptionalCurves_finite_of_proper_birational π hbir).to_subtype

/-- Actual topological components correspond to components of the original
intersection graph, before any forest property is needed. -/
def supportComponentEquiv [IsProper π] (hbir : IsBirationalScheme π) :
    ConnectedComponents (ActualExceptionalLocus.primeSupport π) ≃ (graph π).ConnectedComponent := by
  letI : Finite (Vertices π) := finite_vertices π hbir
  have e := KltDP.Topology.IncidenceGraphComponents.equiv
    (fun C : Vertices π => (C.val : Set S.toScheme))
    (fun C => C.val.isClosed) (fun C => C.val.isIrreducible.isConnected)
  rw [union_eq_primeSupport π] at e
  exact e

/-- For an actual resolution, the same bijection concerns its entire original
non-isomorphism locus, including all fiber points. -/
def resolutionComponentEquiv [IsAlgClosed k] (hπ : IsResolution S X π)
    (hconnected : ∀ y : X.toScheme, IsConnected (π.base ⁻¹' {y})) :
    ConnectedComponents (exceptionalLocus π) ≃ (graph π).ConnectedComponent := by
  letI : IsProper π := hπ.isProper
  letI : IsIso π.c := ProperBirationalStructureSheaf.resolution_c_isIso π hπ
  have hbir := (isBirational_iff_isBirationalScheme π).mp hπ.birational
  rw [ActualExceptionalLocus.exceptionalLocus_eq_primeSupport
    π hbir hπ.over_base hconnected]
  exact supportComponentEquiv π hbir

/-- The finite number of actual graph blocks bounds the number of distinct
singular points. No bound on the number of prime curves is substituted for it. -/
theorem singularPoints_card_le_graph_components [IsAlgClosed k]
    (hπ : IsResolution S X π)
    (hconnected : ∀ y : X.toScheme, IsConnected (π.base ⁻¹' {y})) :
    Finite (graph π).ConnectedComponent ∧
      X.singularPoints.card ≤ Nat.card (graph π).ConnectedComponent := by
  have h := hπ.singularPoints_card_le_exceptional_components hconnected
  letI : Finite (ConnectedComponents (exceptionalLocus π)) := h.1
  let e := resolutionComponentEquiv π hπ hconnected
  exact ⟨Finite.of_equiv _ e, h.2.trans_eq (Nat.card_congr e)⟩

end KltDP.Geometry.ActualExceptionalIncidence

#print axioms KltDP.Geometry.ActualExceptionalIncidence.singularPoints_card_le_graph_components
