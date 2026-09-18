import KltDP.Geometry.GluedAdjunctionNativeApplication

/-! The term form of the compiled native application, for retaining the
inferred type between successive original arguments. Kernel checking is unchanged. -/
open Lean Meta Elab Term
namespace KltDP.Geometry.GluedAdjunctionNativeApplicationTerm

elab "native_adjunction_application% " f:ident a:ident : term => do
  let fn ← instantiateMVars (← elabTerm f none)
  let arg ← instantiateMVars (← elabTerm a none)
  return .app fn arg

end KltDP.Geometry.GluedAdjunctionNativeApplicationTerm
