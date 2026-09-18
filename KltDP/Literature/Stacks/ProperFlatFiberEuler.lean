import KltDP.Geometry.CoherentQuasicoherent
import KltDP.Geometry.AffineModuleFlatOver
import KltDP.Geometry.FiberEulerFunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.LocallyConstant.Basic

/-! Stacks Project Lemma 36.32.2, Tag 0B9T, full statement.
Revision 540451b3e79a131df8eca4c4187448e49dcb262d,
perfect.tex lines 7960-7983. Both local constancy and unrestricted numerical
base-change compatibility are retained. Independently reviewed native
definitions and the exact full telescope are recorded in the adjacent
ROOT_CANDIDATE_ADMISSION_DECISION.json dossier. Isolated admission only;
this file does not alter the production source registry. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Literature.Stacks

local instance sourceEulerOverLocallyBijective (X : Scheme.{u}) :
    ∀ U : X.Opens,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} :=
  KltDP.Geometry.CoherentQuasicoherent.schemeOverWEqualsLocallyBijective X

axiom properFlat_fiberEuler_literal
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hflat : KltDP.Geometry.IsFlatModuleOver f M) :
    IsLocallyConstant (KltDP.Geometry.fiberEuler f M) ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
        KltDP.Geometry.fiberEuler (pullback.snd f g)
          ((KltDP.Geometry.schemeModulePullback (pullback.fst f g)).obj M) t =
        KltDP.Geometry.fiberEuler f M (g.base t)

end KltDP.Literature.Stacks

#check @KltDP.Literature.Stacks.properFlat_fiberEuler_literal
#print axioms KltDP.Literature.Stacks.properFlat_fiberEuler_literal
