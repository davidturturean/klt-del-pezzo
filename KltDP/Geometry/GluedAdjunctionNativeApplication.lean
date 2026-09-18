import Lean

/-! Apply two already inferred original terms without reconstructing their
expected types in the elaborator. The ordinary kernel checks the application. -/
open Lean Meta Elab Tactic
namespace KltDP.Geometry.GluedAdjunctionNativeApplication

elab "exact_native_adjunction_application " f:ident a:ident : tactic => withMainContext do
  let fn ← instantiateMVars (← Term.elabTerm f none)
  let arg ← instantiateMVars (← Term.elabTerm a none)
  (← getMainGoal).assign (.app fn arg)
  replaceMainGoal []

end KltDP.Geometry.GluedAdjunctionNativeApplication
