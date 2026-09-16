import Lean

/-!
# Compiled-environment trust inventory

This module is audit tooling, not a mathematical premise. Its commands inspect
Lean's checked-environment map, including unsafe implementation entries which
are not logical premises. Acceptance also requires the separately source-bound
policy gate. The combined `#klt_trust_report` command captures one
environment and shares complete direct-dependency arrays across root scans;
`#klt_trust_inventory` and `#klt_trust_audit` remain available separately.
See `docs/TRUST_AUDIT.md` for the policy and remaining semantic obligations.
-/

/-- Opt-in plain tagged output; default message reporting preserves existing JSON fixtures. -/
register_option KltDP.Audit.Trust.streamOutput : Bool := {
  defValue := false
  descr := "stream tagged trust records to uncaptured stderr instead of retaining informational messages"
}

/-- Opt-in lossless references to the already source-bound imported `.olean` objects.
Legacy raw strings remain for admitted axioms and stage-one cache/owner comparisons. -/
register_option KltDP.Audit.Trust.nativeTypeReferences : Bool := {
  defValue := false
  descr := "reference complete imported native types except exact legacy-text consumers"
}

namespace KltDP.Audit.Trust

open Lean Elab Command

/-- These are foundational Lean axioms, not results attributed to the literature. -/
def foundationalAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- Exactly four literal Stacks entries. This candidate remains inactive until root promotion. -/
def literatureAxioms : Array Name := #[`KltDP.Literature.Stacks.field_isJ2,
  `KltDP.Literature.Stacks.regularLocal_isUFD,
  `KltDP.Literature.Stacks.properCohomology_finite,
  `KltDP.Literature.Stacks.proper_curve_tensor_degree_literal]

def compilerCachePolicy : String := "lean419_logical_boundary_four_stacks_v6"

def allowedAxiom (n : Name) : Bool :=
  foundationalAxioms.contains n || literatureAxioms.contains n

def declarationModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- Exact type data from the independent axiom-free VM probe 20260906T055518Z-30169.
No J2/axiom module is imported into this tooling module. -/
def fieldJ2ExpectedType : Expr :=
  Lean.Expr.forallE
    `k
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
    (Lean.Expr.forallE
      `instField
      (Lean.Expr.app (Lean.Expr.const `Field [Lean.Level.param `u]) (Lean.Expr.bvar 0))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `KltDP.Literature.J2Ring [Lean.Level.param `u, Lean.Level.param `v])
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `EuclideanDomain.toCommRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Field.toEuclideanDomain [Lean.Level.param `u]) (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0))))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default)

/-- Exact checked proposition from the axiom-free VM probe 20260906T174212Z-57212.
The returned domain supplies cancellation for the original ring operations.
No regularity, factoriality or axiom module is imported by this tooling. -/
def regularLocalUFDExpectedType : Expr :=
  Lean.Expr.forallE
    `R
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
    (Lean.Expr.forallE
      `instCommRing
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        `instLocalRing
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `IsLocalRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))))
        (Lean.Expr.forallE
          `hregular
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `KltDP.Geometry.RegularLocalByGenerators [Lean.Level.param `u])
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Exists [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `IsDomain [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 2)))))
            (Lean.Expr.lam
              `hDomain
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `IsDomain [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 2))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `UniqueFactorizationMonoid [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `IsDomain.toCancelCommMonoidWithZero [Lean.Level.param `u])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3)))
                  (Lean.Expr.bvar 0)))
              (Lean.BinderInfo.default)))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.default)

/-- Exact Expr from actual candidate capture 20260909T010922Z-70712,
reviewed against the full literal telescope; this is expression data, not a mathematical axiom. -/
def properCohomologyExpectedType : Expr :=
  Lean.Expr.forallE
    `A
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
    (Lean.Expr.forallE
      `instCommRing
      (Lean.Expr.app (Lean.Expr.const `CommRing [Lean.Level.param `u]) (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        `instNoetherianRing
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `IsNoetherianRing [Lean.Level.param `u]) (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u]) (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))))
        (Lean.Expr.forallE
          `X
          (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
          (Lean.Expr.forallE
            `f
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `Quiver.Hom
                      [Lean.Level.succ (Lean.Level.param `u), Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.CategoryStruct.toQuiver
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `CategoryTheory.Category.toCategoryStruct
                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                      (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
                (Lean.Expr.bvar 0))
              (Lean.Expr.app
                (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))))
            (Lean.Expr.forallE
              `instProper
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsProper [Lean.Level.param `u]) (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))))
                (Lean.Expr.bvar 0))
              (Lean.Expr.forallE
                `M
                (Lean.Expr.app
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                  (Lean.Expr.bvar 2))
                (Lean.Expr.forallE
                  `instCoherent
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `KltDP.Geometry.IsCoherentModule [Lean.Level.param `u])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 0))
                  (Lean.Expr.forallE
                    `n
                    (Lean.Expr.const `Nat [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Module.Finite [Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.bvar 8))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `KltDP.Geometry.ModuleCohomology.rightDerivedH [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 2))
                              (Lean.Expr.bvar 0)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.param `u])
                              (Lean.Expr.bvar 8))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toCommSemiring [Lean.Level.param `u])
                                (Lean.Expr.bvar 8))
                              (Lean.Expr.bvar 7))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `AddCommGroup.toAddCommMonoid [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `KltDP.Geometry.ModuleCohomology.rightDerivedH [Lean.Level.param `u])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.bvar 2))
                              (Lean.Expr.bvar 0)))
                          (Lean.Expr.app
                            (Lean.Expr.const `AddCommGrp.str [Lean.Level.param `u])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `Prefunctor.obj
                                          [Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.succ (Lean.Level.param `u),
                                           Lean.Level.succ (Lean.Level.param `u)])
                                        (Lean.Expr.app
                                          (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                                          (Lean.Expr.bvar 5)))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `CategoryTheory.CategoryStruct.toQuiver
                                            [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                          (Lean.Expr.app
                                            (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                                            (Lean.Expr.bvar 5)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `CategoryTheory.Category.toCategoryStruct
                                              [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                            (Lean.Expr.app
                                              (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                                              (Lean.Expr.bvar 5)))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `SheafOfModules.instCategory
                                                    [Lean.Level.param `u,
                                                     Lean.Level.param `u,
                                                     Lean.Level.param `u,
                                                     Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 5)))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.bvar 5))))))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `Preorder.smallCategory [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 5)))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 5))))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `PartialOrder.toPreorder [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 5)))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 5))))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CompleteSemilatticeInf.toPartialOrder
                                                          [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `TopologicalSpace.Opens
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 5)))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 5))))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CompleteLattice.toCompleteSemilatticeInf
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `TopologicalSpace.Opens
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 5)))))))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 5))))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `TopologicalSpace.Opens.instCompleteLattice
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 5)))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 5))))))))))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `Opens.grothendieckTopology [Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                             Lean.Level.param `u,
                                                             Lean.Level.param `u])
                                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.bvar 5)))))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                           Lean.Level.param `u,
                                                           Lean.Level.param `u])
                                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                             Lean.Level.param `u,
                                                             Lean.Level.param `u])
                                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                          [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.bvar 5))))))))
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.Scheme.ringCatSheaf
                                                [Lean.Level.param `u])
                                              (Lean.Expr.bvar 5))))))
                                    (Lean.Expr.const `AddCommGrp [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `CategoryTheory.CategoryStruct.toQuiver
                                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                      (Lean.Expr.const `AddCommGrp [Lean.Level.param `u]))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `CategoryTheory.Category.toCategoryStruct
                                          [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                        (Lean.Expr.const `AddCommGrp [Lean.Level.param `u]))
                                      (Lean.Expr.const `AddCommGrp.instCategory [Lean.Level.param `u]))))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `CategoryTheory.Functor.toPrefunctor
                                            [Lean.Level.param `u,
                                             Lean.Level.param `u,
                                             Lean.Level.succ (Lean.Level.param `u),
                                             Lean.Level.succ (Lean.Level.param `u)])
                                          (Lean.Expr.app
                                            (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                                            (Lean.Expr.bvar 5)))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `SheafOfModules.instCategory
                                                  [Lean.Level.param `u,
                                                   Lean.Level.param `u,
                                                   Lean.Level.param `u,
                                                   Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.bvar 5)))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                             Lean.Level.param `u,
                                                             Lean.Level.param `u])
                                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.bvar 5))))))))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `Preorder.smallCategory [Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 5)))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.bvar 5))))))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `PartialOrder.toPreorder [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 5)))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 5))))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `CompleteSemilatticeInf.toPartialOrder
                                                        [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 5)))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 5))))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `CompleteLattice.toCompleteSemilatticeInf
                                                          [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `TopologicalSpace.Opens
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 5)))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 5))))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `TopologicalSpace.Opens.instCompleteLattice
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 5)))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 5))))))))))))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `Opens.grothendieckTopology [Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                           Lean.Level.param `u,
                                                           Lean.Level.param `u])
                                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                             Lean.Level.param `u,
                                                             Lean.Level.param `u])
                                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                          [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.bvar 5)))))))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                         Lean.Level.param `u,
                                                         Lean.Level.param `u])
                                                      (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                    (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                           Lean.Level.param `u,
                                                           Lean.Level.param `u])
                                                        (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                      (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                        [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const
                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                          [Lean.Level.param `u])
                                                        (Lean.Expr.bvar 5))))))))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `AlgebraicGeometry.Scheme.ringCatSheaf [Lean.Level.param `u])
                                            (Lean.Expr.bvar 5))))
                                      (Lean.Expr.const `AddCommGrp [Lean.Level.param `u]))
                                    (Lean.Expr.const `AddCommGrp.instCategory [Lean.Level.param `u]))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `KltDP.Geometry.ModuleCohomology.rightDerivedFunctor
                                        [Lean.Level.param `u])
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 0))))
                              (Lean.Expr.bvar 2)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `KltDP.Geometry.ModuleCohomology.baseRingRightDerivedModule
                                    [Lean.Level.param `u])
                                  (Lean.Expr.bvar 8))
                                (Lean.Expr.bvar 7))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 2))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.instImplicit))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.implicit))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit)

/-- Exact Expr from the independent expected-type probe build 20260910T041513Z-104870 on the
dedicated dev runner (module `KltDP.AdmissionProbe.CurveTensorDegreeExpectedType`, which does
not import the literal); this is expression data, not a mathematical axiom. -/
def curveTensorDegreeExpectedType : Expr :=
  Lean.Expr.forallE
    `k
    (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
    (Lean.Expr.forallE
      `instField
      (Lean.Expr.app (Lean.Expr.const `Field [Lean.Level.param `u]) (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        `Y
        (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u])
        (Lean.Expr.forallE
          `f
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `Quiver.Hom
                    [Lean.Level.succ (Lean.Level.param `u), Lean.Level.succ (Lean.Level.param `u)])
                  (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `CategoryTheory.CategoryStruct.toQuiver
                      [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                    (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `CategoryTheory.Category.toCategoryStruct
                        [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                      (Lean.Expr.const `AlgebraicGeometry.Scheme [Lean.Level.param `u]))
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.instCategory [Lean.Level.param `u]))))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app
              (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `EuclideanDomain.toCommRing [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Field.toEuclideanDomain [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1))))))
          (Lean.Expr.forallE
            `instProper
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `AlgebraicGeometry.IsProper [Lean.Level.param `u]) (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.const `AlgebraicGeometry.Spec [Lean.Level.param `u])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `CommRingCat.of [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `EuclideanDomain.toCommRing [Lean.Level.param `u])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Field.toEuclideanDomain [Lean.Level.param `u])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 2))))))
              (Lean.Expr.bvar 0))
            (Lean.Expr.forallE
              `hdim
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `LE.le [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `WithBot [Lean.Level.zero]) (Lean.Expr.const `ENat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Preorder.toLE [Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `WithBot [Lean.Level.zero]) (Lean.Expr.const `ENat [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `WithBot.preorder [Lean.Level.zero]) (Lean.Expr.const `ENat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `PartialOrder.toPreorder [Lean.Level.zero])
                            (Lean.Expr.const `ENat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `OmegaCompletePartialOrder.toPartialOrder [Lean.Level.zero])
                              (Lean.Expr.const `ENat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CompleteLattice.instOmegaCompletePartialOrder [Lean.Level.zero])
                                (Lean.Expr.const `ENat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CompletelyDistribLattice.toCompleteLattice [Lean.Level.zero])
                                  (Lean.Expr.const `ENat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `CompleteLinearOrder.toCompletelyDistribLattice [Lean.Level.zero])
                                    (Lean.Expr.const `ENat []))
                                  (Lean.Expr.const `instCompleteLinearOrderENat [])))))))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `topologicalKrullDim [Lean.Level.param `u])
                      (Lean.Expr.app
                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `AlgebraicGeometry.PresheafedSpace.carrier
                                [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                            (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                  [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                              (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                            (Lean.Expr.app
                              (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                              (Lean.Expr.app
                                (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                                (Lean.Expr.bvar 2)))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier
                            [Lean.Level.succ (Lean.Level.param `u), Lean.Level.param `u, Lean.Level.param `u])
                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                      (Lean.Expr.app
                        (Lean.Expr.const `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace [Lean.Level.param `u])
                        (Lean.Expr.app
                          (Lean.Expr.const `AlgebraicGeometry.Scheme.toLocallyRingedSpace [Lean.Level.param `u])
                          (Lean.Expr.bvar 2))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `WithBot [Lean.Level.zero]) (Lean.Expr.const `ENat [])))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `One.toOfNat1 [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `WithBot [Lean.Level.zero]) (Lean.Expr.const `ENat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `WithBot.one [Lean.Level.zero]) (Lean.Expr.const `ENat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `AddMonoidWithOne.toOne [Lean.Level.zero])
                          (Lean.Expr.const `ENat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `AddCommMonoidWithOne.toAddMonoidWithOne [Lean.Level.zero])
                            (Lean.Expr.const `ENat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `NonAssocSemiring.toAddCommMonoidWithOne [Lean.Level.zero])
                              (Lean.Expr.const `ENat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.const `ENat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `CommSemiring.toSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `ENat []))
                                (Lean.Expr.const `instENatCommSemiring []))))))))))
              (Lean.Expr.forallE
                `E
                (Lean.Expr.app
                  (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.forallE
                  `V
                  (Lean.Expr.app
                    (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.forallE
                    `n
                    (Lean.Expr.const `Nat [])
                    (Lean.Expr.forallE
                      `m
                      (Lean.Expr.const `Nat [])
                      (Lean.Expr.forallE
                        `hE
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `KltDP.Geometry.ModuleCohomology.IsLocallyFreeOfRankOn
                                [Lean.Level.param `u])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 3))
                          (Lean.Expr.bvar 1))
                        (Lean.Expr.forallE
                          `hV
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `KltDP.Geometry.ModuleCohomology.IsLocallyFreeOfRankOn
                                  [Lean.Level.param `u])
                                (Lean.Expr.bvar 8))
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.bvar 1))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                                (Lean.Expr.const `Int []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `KltDP.Geometry.ModuleCohomology.finiteRankDegree
                                                  [Lean.Level.param `u])
                                                (Lean.Expr.bvar 11))
                                              (Lean.Expr.bvar 10))
                                            (Lean.Expr.bvar 9))
                                          (Lean.Expr.bvar 8))
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `CategoryTheory.MonoidalCategoryStruct.tensorObj
                                                [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                              (Lean.Expr.app
                                                (Lean.Expr.const `AlgebraicGeometry.Scheme.Modules [Lean.Level.param `u])
                                                (Lean.Expr.bvar 9)))
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `SheafOfModules.instCategory
                                                      [Lean.Level.param `u,
                                                       Lean.Level.param `u,
                                                       Lean.Level.param `u,
                                                       Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 9)))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 9))))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `Preorder.smallCategory [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 9)))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 9))))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `PartialOrder.toPreorder [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `TopologicalSpace.Opens
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 9)))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 9))))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `CompleteSemilatticeInf.toPartialOrder
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `TopologicalSpace.Opens
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 9)))))))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 9))))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CompleteLattice.toCompleteSemilatticeInf
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `TopologicalSpace.Opens
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                                             Lean.Level.param `u,
                                                                             Lean.Level.param `u])
                                                                          (Lean.Expr.const
                                                                            `CommRingCat
                                                                            [Lean.Level.param `u]))
                                                                        (Lean.Expr.const
                                                                          `CommRingCat.instCategory
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                            [Lean.Level.param `u])
                                                                          (Lean.Expr.bvar 9)))))))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 9))))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `TopologicalSpace.Opens.instCompleteLattice
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 9)))))))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 9))))))))))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `Opens.grothendieckTopology [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.bvar 9)))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                             Lean.Level.param `u,
                                                             Lean.Level.param `u])
                                                          (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                        (Lean.Expr.const `CommRingCat.instCategory [Lean.Level.param `u]))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const
                                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                            [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.bvar 9))))))))
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `AlgebraicGeometry.Scheme.ringCatSheaf
                                                  [Lean.Level.param `u])
                                                (Lean.Expr.bvar 9))))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const
                                                  `CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct
                                                  [Lean.Level.param `u, Lean.Level.succ (Lean.Level.param `u)])
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `AlgebraicGeometry.Scheme.Modules
                                                    [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 9)))
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const
                                                        `SheafOfModules.instCategory
                                                        [Lean.Level.param `u,
                                                         Lean.Level.param `u,
                                                         Lean.Level.param `u,
                                                         Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopologicalSpace.Opens [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 9)))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.PresheafedSpace.carrier
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.bvar 9))))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `Preorder.smallCategory [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `TopologicalSpace.Opens
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 9)))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.PresheafedSpace.carrier
                                                                    [Lean.Level.succ (Lean.Level.param `u),
                                                                     Lean.Level.param `u,
                                                                     Lean.Level.param `u])
                                                                  (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                (Lean.Expr.const
                                                                  `CommRingCat.instCategory
                                                                  [Lean.Level.param `u]))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.bvar 9))))))))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.const `PartialOrder.toPreorder [Lean.Level.param `u])
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `TopologicalSpace.Opens
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 9)))))))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.PresheafedSpace.carrier
                                                                      [Lean.Level.succ (Lean.Level.param `u),
                                                                       Lean.Level.param `u,
                                                                       Lean.Level.param `u])
                                                                    (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                                  (Lean.Expr.const
                                                                    `CommRingCat.instCategory
                                                                    [Lean.Level.param `u]))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.bvar 9))))))))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `CompleteSemilatticeInf.toPartialOrder
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `TopologicalSpace.Opens
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                                             Lean.Level.param `u,
                                                                             Lean.Level.param `u])
                                                                          (Lean.Expr.const
                                                                            `CommRingCat
                                                                            [Lean.Level.param `u]))
                                                                        (Lean.Expr.const
                                                                          `CommRingCat.instCategory
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                            [Lean.Level.param `u])
                                                                          (Lean.Expr.bvar 9)))))))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 9))))))))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `CompleteLattice.toCompleteSemilatticeInf
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const
                                                                    `TopologicalSpace.Opens
                                                                    [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.const
                                                                      `TopCat.carrier
                                                                      [Lean.Level.param `u])
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.PresheafedSpace.carrier
                                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                                             Lean.Level.param `u,
                                                                             Lean.Level.param `u])
                                                                          (Lean.Expr.const
                                                                            `CommRingCat
                                                                            [Lean.Level.param `u]))
                                                                        (Lean.Expr.const
                                                                          `CommRingCat.instCategory
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.app
                                                                            (Lean.Expr.const
                                                                              `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                                               Lean.Level.param `u,
                                                                               Lean.Level.param `u])
                                                                            (Lean.Expr.const
                                                                              `CommRingCat
                                                                              [Lean.Level.param `u]))
                                                                          (Lean.Expr.const
                                                                            `CommRingCat.instCategory
                                                                            [Lean.Level.param `u]))
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                            [Lean.Level.param `u])
                                                                          (Lean.Expr.app
                                                                            (Lean.Expr.const
                                                                              `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                              [Lean.Level.param `u])
                                                                            (Lean.Expr.bvar 9)))))))
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                                             Lean.Level.param `u,
                                                                             Lean.Level.param `u])
                                                                          (Lean.Expr.const
                                                                            `CommRingCat
                                                                            [Lean.Level.param `u]))
                                                                        (Lean.Expr.const
                                                                          `CommRingCat.instCategory
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                            [Lean.Level.param `u])
                                                                          (Lean.Expr.bvar 9))))))))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `TopologicalSpace.Opens.instCompleteLattice
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.PresheafedSpace.carrier
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                            [Lean.Level.succ (Lean.Level.param `u),
                                                                             Lean.Level.param `u,
                                                                             Lean.Level.param `u])
                                                                          (Lean.Expr.const
                                                                            `CommRingCat
                                                                            [Lean.Level.param `u]))
                                                                        (Lean.Expr.const
                                                                          `CommRingCat.instCategory
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.app
                                                                          (Lean.Expr.const
                                                                            `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                            [Lean.Level.param `u])
                                                                          (Lean.Expr.bvar 9)))))))
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                                (Lean.Expr.app
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.PresheafedSpace.carrier
                                                                        [Lean.Level.succ (Lean.Level.param `u),
                                                                         Lean.Level.param `u,
                                                                         Lean.Level.param `u])
                                                                      (Lean.Expr.const
                                                                        `CommRingCat
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.const
                                                                      `CommRingCat.instCategory
                                                                      [Lean.Level.param `u]))
                                                                  (Lean.Expr.app
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                          [Lean.Level.succ (Lean.Level.param `u),
                                                                           Lean.Level.param `u,
                                                                           Lean.Level.param `u])
                                                                        (Lean.Expr.const
                                                                          `CommRingCat
                                                                          [Lean.Level.param `u]))
                                                                      (Lean.Expr.const
                                                                        `CommRingCat.instCategory
                                                                        [Lean.Level.param `u]))
                                                                    (Lean.Expr.app
                                                                      (Lean.Expr.const
                                                                        `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                        [Lean.Level.param `u])
                                                                      (Lean.Expr.app
                                                                        (Lean.Expr.const
                                                                          `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                          [Lean.Level.param `u])
                                                                        (Lean.Expr.bvar 9))))))))))))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `Opens.grothendieckTopology [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TopCat.carrier [Lean.Level.param `u])
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.PresheafedSpace.carrier
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                  [Lean.Level.succ (Lean.Level.param `u),
                                                                   Lean.Level.param `u,
                                                                   Lean.Level.param `u])
                                                                (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                              (Lean.Expr.const
                                                                `CommRingCat.instCategory
                                                                [Lean.Level.param `u]))
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.app
                                                                (Lean.Expr.const
                                                                  `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                  [Lean.Level.param `u])
                                                                (Lean.Expr.bvar 9)))))))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TopCat.str [Lean.Level.param `u])
                                                      (Lean.Expr.app
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.PresheafedSpace.carrier
                                                              [Lean.Level.succ (Lean.Level.param `u),
                                                               Lean.Level.param `u,
                                                               Lean.Level.param `u])
                                                            (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                          (Lean.Expr.const
                                                            `CommRingCat.instCategory
                                                            [Lean.Level.param `u]))
                                                        (Lean.Expr.app
                                                          (Lean.Expr.app
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                                                                [Lean.Level.succ (Lean.Level.param `u),
                                                                 Lean.Level.param `u,
                                                                 Lean.Level.param `u])
                                                              (Lean.Expr.const `CommRingCat [Lean.Level.param `u]))
                                                            (Lean.Expr.const
                                                              `CommRingCat.instCategory
                                                              [Lean.Level.param `u]))
                                                          (Lean.Expr.app
                                                            (Lean.Expr.const
                                                              `AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                                                              [Lean.Level.param `u])
                                                            (Lean.Expr.app
                                                              (Lean.Expr.const
                                                                `AlgebraicGeometry.Scheme.toLocallyRingedSpace
                                                                [Lean.Level.param `u])
                                                              (Lean.Expr.bvar 9))))))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `AlgebraicGeometry.Scheme.ringCatSheaf
                                                    [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 9))))
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `AlgebraicGeometry.Scheme.Modules.monoidalCategory
                                                [Lean.Level.param `u])
                                              (Lean.Expr.bvar 9))))
                                        (Lean.Expr.bvar 5))
                                      (Lean.Expr.bvar 4)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `HMul.hMul
                                                [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `Nat []))
                                            (Lean.Expr.const `Nat []))
                                          (Lean.Expr.const `Nat []))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `instHMul [Lean.Level.zero])
                                            (Lean.Expr.const `Nat []))
                                          (Lean.Expr.const `instMulNat [])))
                                      (Lean.Expr.bvar 3))
                                    (Lean.Expr.bvar 2)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `KltDP.SheafOfModules.IsLocallyFreeOfRank.tensor
                                                [Lean.Level.param `u])
                                              (Lean.Expr.bvar 9))
                                            (Lean.Expr.bvar 5))
                                          (Lean.Expr.bvar 4))
                                        (Lean.Expr.bvar 3))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.bvar 1))
                                  (Lean.Expr.bvar 0))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Int []))
                                      (Lean.Expr.const `Int []))
                                    (Lean.Expr.const `Int []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `instHAdd [Lean.Level.zero])
                                      (Lean.Expr.const `Int []))
                                    (Lean.Expr.const `Int.instAdd [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `HMul.hMul
                                              [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `Int []))
                                          (Lean.Expr.const `Int []))
                                        (Lean.Expr.const `Int []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `instHMul [Lean.Level.zero])
                                          (Lean.Expr.const `Int []))
                                        (Lean.Expr.const `Int.instMul [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Nat.cast [Lean.Level.zero])
                                          (Lean.Expr.const `Int []))
                                        (Lean.Expr.const `instNatCastInt []))
                                      (Lean.Expr.bvar 3)))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.const
                                                      `KltDP.Geometry.ModuleCohomology.finiteRankDegree
                                                      [Lean.Level.param `u])
                                                    (Lean.Expr.bvar 11))
                                                  (Lean.Expr.bvar 10))
                                                (Lean.Expr.bvar 9))
                                              (Lean.Expr.bvar 8))
                                            (Lean.Expr.bvar 7))
                                          (Lean.Expr.bvar 6))
                                        (Lean.Expr.bvar 4))
                                      (Lean.Expr.bvar 2))
                                    (Lean.Expr.bvar 0))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Int []))
                                        (Lean.Expr.const `Int []))
                                      (Lean.Expr.const `Int []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `instHMul [Lean.Level.zero])
                                        (Lean.Expr.const `Int []))
                                      (Lean.Expr.const `Int.instMul [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Nat.cast [Lean.Level.zero])
                                        (Lean.Expr.const `Int []))
                                      (Lean.Expr.const `instNatCastInt []))
                                    (Lean.Expr.bvar 2)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const
                                                    `KltDP.Geometry.ModuleCohomology.finiteRankDegree
                                                    [Lean.Level.param `u])
                                                  (Lean.Expr.bvar 11))
                                                (Lean.Expr.bvar 10))
                                              (Lean.Expr.bvar 9))
                                            (Lean.Expr.bvar 8))
                                          (Lean.Expr.bvar 7))
                                        (Lean.Expr.bvar 6))
                                      (Lean.Expr.bvar 5))
                                    (Lean.Expr.bvar 3))
                                  (Lean.Expr.bvar 1)))))
                          (Lean.BinderInfo.default))
                        (Lean.BinderInfo.default))
                      (Lean.BinderInfo.default))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.implicit))
      (Lean.BinderInfo.instImplicit))
    (Lean.BinderInfo.implicit)

/-- Validate the literal declaration when present. Isolated tooling fixtures may
omit entries; the production parser requires all four exact approved entries. -/
def validateLiteratureShape (env : Environment) : CommandElabM Unit := do
  let name := `KltDP.Literature.Stacks.field_isJ2
  if let some ci := env.checked.get.find? name then
    let .axiomInfo actual := ci
      | throwError "Field-J2 admission requires an axiom declaration of the reviewed literal type"
    unless !actual.isUnsafe && actual.levelParams == [`u, `v] &&
        declarationModule env name == `KltDP.Literature.Stacks.FieldJ2 &&
        (declRangeExt.find? env name).isSome &&
        Expr.equal actual.type fieldJ2ExpectedType do
      throwError "Field-J2 declaration differs from the independently reviewed module/type/telescope"
  let ufdName := `KltDP.Literature.Stacks.regularLocal_isUFD
  if let some ci := env.checked.get.find? ufdName then
    let .axiomInfo actual := ci
      | throwError "Regular-local UFD admission requires the reviewed literal axiom declaration"
    unless !actual.isUnsafe && actual.levelParams == [`u] &&
        declarationModule env ufdName == `KltDP.Literature.Stacks.RegularLocalUFD &&
        (declRangeExt.find? env ufdName).isSome &&
        Expr.equal actual.type regularLocalUFDExpectedType do
      throwError "Regular-local UFD declaration differs from the independently reviewed module/type/telescope"

  let properName := `KltDP.Literature.Stacks.properCohomology_finite
  if let some ci := env.checked.get.find? properName then
    let .axiomInfo actual := ci
      | throwError "Proper-cohomology admission requires the reviewed literal axiom declaration"
    unless !actual.isUnsafe && actual.levelParams == [`u] &&
        declarationModule env properName == `KltDP.Literature.Stacks.ProperCohomologyFinite &&
        (declRangeExt.find? env properName).isSome &&
        Expr.equal actual.type properCohomologyExpectedType do
      throwError "Proper-cohomology declaration differs from the reviewed module/type/telescope"

  let curveName := `KltDP.Literature.Stacks.proper_curve_tensor_degree_literal
  if let some ci := env.checked.get.find? curveName then
    let .axiomInfo actual := ci
      | throwError "Curve-tensor-degree admission requires the reviewed literal axiom declaration"
    unless !actual.isUnsafe && actual.levelParams == [`u] &&
        declarationModule env curveName == `KltDP.Literature.Stacks.CurveTensorDegreeLiteral &&
        (declRangeExt.find? env curveName).isSome &&
        Expr.equal actual.type curveTensorDegreeExpectedType do
      throwError "Curve-tensor-degree declaration differs from the independently probed module/type/telescope"

/-- Module ownership also catches project declarations outside its usual namespace. -/
def isProjectDeclaration (env : Environment) (n : Name) : Bool :=
  (`KltDP).isPrefixOf (privateToUserName n.eraseMacroScopes) ||
    (`KltDP).isPrefixOf (declarationModule env n)

/-- Only this specific implementation module is exempt as audit tooling. -/
def isAuditTooling (env : Environment) (n : Name) : Bool :=
  declarationModule env n == `KltDP.Audit.Trust

/-- Lean creates partial executable companions even for ordinary safe recursion.
Only the compiler's naming convention, a same-module safe definition, and an
identical universe-parameter list/type together qualify for this classification.
An opaque wrapper produced by a user-written `partial def` does not qualify. -/
def isSafeRuntimeCompanion (env : Environment) (n : Name) : Bool := Id.run do
  let some owner := Compiler.isUnsafeRecName? n | return false
  let some (.defnInfo runtime) := env.checked.get.find? n | return false
  let some (.defnInfo logical) := env.checked.get.find? owner | return false
  return runtime.safety == .partial && logical.safety == .safe &&
    runtime.type == logical.type && runtime.levelParams == logical.levelParams &&
    declarationModule env n == declarationModule env owner

/-- The old compiler's exact suffixes; this alone does not establish provenance. -/
def compilerStageName? : Name → Option (Name × Nat)
  | .str owner "_cstage1" => some (owner, 1)
  | .str owner "_cstage2" => some (owner, 2)
  | _ => none

/-- Common old-compiler cache invariants. Source declarations have direct ranges
and ordinary unsafe definitions have regular, rather than opaque, hints.
These are compiler conventions, not unforgeable registration metadata. -/
def hasCompilerStageShape (env : Environment) (n owner : Name) : Bool := Id.run do
  let some (.defnInfo cache) := env.checked.get.find? n | return false
  let some (.defnInfo logical) := env.checked.get.find? owner | return false
  return cache.safety == .unsafe && cache.hints == .opaque &&
    logical.safety == .safe && !isNoncomputable env owner &&
    (declRangeExt.find? env n).isNone &&
    declarationModule env n == declarationModule env owner

/-- Lean 4.19 `register_stage1_decl` preserves its owner's type and universes. -/
def isCompilerStageOne (env : Environment) (n owner : Name) : Bool := Id.run do
  unless n == .str owner "_cstage1" && hasCompilerStageShape env n owner do
    return false
  let some (.defnInfo cache) := env.checked.get.find? n | return false
  let some (.defnInfo logical) := env.checked.get.find? owner | return false
  return cache.type == logical.type && cache.levelParams == logical.levelParams

/-- Identify only the reviewed old-compiler cache convention. Stage two has an
erased runtime type, so it needs a validated stage-one pair instead of type
equality. Its full closure remains visible, but it is not a logical audit root.
Any logical root depending on either unsafe cache still fails without exception. -/
def isCompilerStageCache (env : Environment) (n : Name) : Bool := Id.run do
  let some (owner, stage) := compilerStageName? n | return false
  if stage == 1 then return isCompilerStageOne env n owner
  unless hasCompilerStageShape env n owner &&
      isCompilerStageOne env (.str owner "_cstage1") owner do return false
  let some (.defnInfo cache) := env.checked.get.find? n | return false
  return cache.levelParams.isEmpty

/-- An unsafe entry without a direct source range is inventoried as nonlogical
implementation data. This does NOT authenticate compiler origin: metaprograms
can construct the same metadata. Exact-source policy is a separate required
gate. No such entry is ever allowed in a logical root's dependency closure. -/
def isUnsafeImplementation (env : Environment) (n : Name) : Bool := Id.run do
  let some ci := env.checked.get.find? n | return false
  return ci.isUnsafe && (declRangeExt.find? env n).isNone

/-- Nonlogical rows retain their complete, ordinarily failing closures. -/
def isNonlogicalImplementation (env : Environment) (n : Name) : Bool :=
  isCompilerStageCache env n || isUnsafeImplementation env n

def sortedNames (ns : NameSet) : Array Name :=
  ns.toList.toArray.qsort (fun a b => a.toString < b.toString)

def namesJson (ns : Array Name) : Json := toJson (ns.map Name.toString)

/-- A fresh expression cache per call; collect projections as well as constants. -/
def expressionNamesDag (e : Expr) (initial : NameSet) : NameSet :=
  runST (α := NameSet) fun σ => do
    let names : ST.Ref σ NameSet ← ST.mkRef (σ := σ) (m := ST σ) initial
    let gather : Expr → ST σ Unit := fun node => do
      match node with
      | .const n _ => ST.Ref.modify (m := ST σ) names (·.insert n)
      | .proj n _ _ => ST.Ref.modify (m := ST σ) names (·.insert n)
      | _ => pure ()
    e.forEach (ω := σ) (m := ST σ) gather
    ST.Ref.get (m := ST σ) names

/-- Same cases and final ordering as the baseline direct-dependency collector. -/
def directDependenciesDag (ci : ConstantInfo) : Array Name := Id.run do
  let mut ns := expressionNamesDag ci.type {}
  if let some value := ci.value? (allowOpaque := true) then
    ns := expressionNamesDag value ns
  match ci with
  | .inductInfo v =>
    for n in v.all ++ v.ctors do ns := ns.insert n
  | .ctorInfo v => ns := ns.insert v.induct
  | .recInfo v =>
    for n in v.all do ns := ns.insert n
    for r in v.rules do
      ns := expressionNamesDag r.rhs (ns.insert r.ctor)
  | _ => pure ()
  return sortedNames ns

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def reducibilityHintsName (ci : ConstantInfo) : Option String :=
  match ci with
  | .defnInfo v => some <| match v.hints with
    | .opaque => "opaque"
    | .abbrev => "abbrev"
    | .regular _ => "regular"
  | _ => none

structure Closure where
  visited : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  unsafeDeclarations : NameSet := {}
  partialDeclarations : NameSet := {}
  toolingDeclarations : NameSet := {}
  opaqueDeclarations : NameSet := {}
  runtimeOverrides : NameSet := {}

def forbiddenAxioms (s : Closure) : Array Name :=
  (sortedNames s.axioms).filter (fun n => !allowedAxiom n)

def Closure.passes (s : Closure) : Bool :=
  (forbiddenAxioms s).isEmpty && s.missing.isEmpty &&
    s.unsafeDeclarations.isEmpty && s.partialDeclarations.isEmpty &&
    s.toolingDeclarations.isEmpty

/-- Inventory the checked environment. In Lean 4.19 `env.constants` denotes this
same map; it does not supply an independent list of pending declarations. -/
def projectDeclarations (env : Environment) : Array Name := Id.run do
  let mut ns : NameSet := {}
  for (n, _) in env.checked.get.constants do
    if isProjectDeclaration env n then ns := ns.insert n
  return sortedNames ns

def closureJson (s : Closure) : Json := Json.mkObj [
  ("passes", toJson s.passes),
  ("transitive_dependency_count_including_root", toJson s.visited.toList.length),
  ("transitive_axioms", namesJson (sortedNames s.axioms)),
  ("forbidden_axioms", namesJson (forbiddenAxioms s)),
  ("missing_checked_declarations", namesJson (sortedNames s.missing)),
  ("unsafe_dependencies", namesJson (sortedNames s.unsafeDeclarations)),
  ("partial_dependencies", namesJson (sortedNames s.partialDeclarations)),
  ("audit_tooling_dependencies", namesJson (sortedNames s.toolingDeclarations)),
  ("opaque_dependencies", namesJson (sortedNames s.opaqueDeclarations)),
  ("runtime_override_dependencies", namesJson (sortedNames s.runtimeOverrides))]

/-- A compiler companion is not a logical premise. Its executable closure is
still checked for axioms, missing constants, unsafe definitions, and tooling.
Only validated safe-definition companions may have partial safety in that scope. -/
def rootPasses (env : Environment) (n : Name) (s : Closure) : Bool :=
  if isSafeRuntimeCompanion env n then
    (forbiddenAxioms s).isEmpty && s.missing.isEmpty &&
      s.unsafeDeclarations.isEmpty && s.toolingDeclarations.isEmpty &&
      (sortedNames s.partialDeclarations).all (isSafeRuntimeCompanion env)
  else s.passes

def emit (tag : String) (payload : Json) : CommandElabM Unit := do
  if streamOutput.get (← getOptions) then
    liftIO do
      let out ← IO.getStderr
      out.putStr s!"{tag} {payload.compress}\n"
      out.flush
  else
    logInfo m!"{tag} {payload.compress}"

abbrev ScanM := StateRefT (NameMap (Array Name)) CommandElabM

/-- Cache only complete direct-edge arrays; no partial transitive closures. -/
def cachedDependencies (ci : ConstantInfo) : ScanM (Array Name) := do
  if let some names := (← get).find? ci.name then return names
  let names := directDependenciesDag ci
  modify (·.insert ci.name names)
  return names

/-- Each root gets its own name-visited set. The edge cache belongs to the
enclosing command's single immutable environment snapshot. -/
def closureCached (env : Environment) (root : Name) : ScanM Closure := do
  let mut result : Closure := {}
  let mut pending : Array Name := #[root]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if result.visited.contains n then continue
    result := { result with visited := result.visited.insert n }
    let some ci := env.checked.get.find? n
      | result := { result with missing := result.missing.insert n }
        continue
    if ci.isAxiom then result := { result with axioms := result.axioms.insert n }
    if ci.isUnsafe then
      result := { result with unsafeDeclarations := result.unsafeDeclarations.insert n }
    if ci.isPartial then
      result := { result with partialDeclarations := result.partialDeclarations.insert n }
    if isAuditTooling env n then
      result := { result with toolingDeclarations := result.toolingDeclarations.insert n }
    if ci matches .opaqueInfo _ then
      result := { result with opaqueDeclarations := result.opaqueDeclarations.insert n }
    if isExtern env n || (Compiler.getImplementedBy? env n).isSome then
      result := { result with runtimeOverrides := result.runtimeOverrides.insert n }
    pending := pending ++ (← cachedDependencies ci)
  return result

/-- Exact name components, without private-name or macro-scope erasure. Numeric
components are decimal strings so that JSON consumers cannot round large naturals. -/
def nativeTypeNameParts : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nativeTypeNameParts p).push (Json.arr #[toJson "str", toJson s])
  | .num p i => (nativeTypeNameParts p).push (Json.arr #[toJson "num", toJson (toString i)])

/-- Preserve the exact old raw-text consumers on both sides of each stage-one
comparison. This does not change compiler-cache classification or trust policy. -/
def needsLegacyTypeExpression (env : Environment) (n : Name) : Bool :=
  literatureAxioms.contains n || (!isAuditTooling env n &&
    ((match compilerStageName? n with
      | some (owner, 1) => isCompilerStageOne env n owner
      | _ => false) ||
    isCompilerStageOne env (.str n "_cstage1") n))

/-- A reference is valid only for an imported checked declaration. The parser
must bind the canonical artifact path to the unchanged source/object manifests;
the artifact retains the complete ConstantInfo and its unmodified `type` field. -/
def nativeTypeReference (env : Environment) (n : Name) : CommandElabM Json := do
  let some i := env.getModuleIdxFor? n
    | throwError "Native type reference requires an imported declaration: {n}"
  let owner := env.header.moduleNames[i.toNat]!
  return Json.mkObj [
    ("encoding", toJson "lean419-olean-constant-type-v1"),
    ("module", toJson owner.toString),
    ("declaration", toJson n.toString),
    ("name_parts", Json.arr (nativeTypeNameParts n)),
    ("artifact", toJson (".lake/build/lib/lean/" ++ owner.toString.replace "." "/" ++ ".olean"))]

def inventorySchema (nativeTypes : Bool) : String :=
  if nativeTypes then "klt-compiled-trust-native-types-v2" else "klt-compiled-trust-v1"

/-- All original policy fields are unchanged. Only the opt-in raw-type transport
uses a bound native artifact for rows without an exact raw-string consumer. -/
def declarationJsonCached (env : Environment) (n : Name) (checkedClosure : Closure) : ScanM Json := do
  let tooling := isAuditTooling env n
  let companion := isSafeRuntimeCompanion env n
  let cache := !tooling && isCompilerStageCache env n
  let implementation := !tooling && !cache && isUnsafeImplementation env n
  let base := [
    ("name", toJson n.toString),
    ("user_name", toJson (privateToUserName n.eraseMacroScopes).toString),
    ("module", toJson (declarationModule env n).toString),
    ("scope", toJson (if tooling then "audit_tooling" else if cache then
      "compiler_stage_cache" else if companion then
      "safe_definition_runtime_companion" else if implementation then
      "unsafe_implementation" else "mathematical_declaration"))]
  let some ci := env.checked.get.find? n
    | return Json.mkObj (base ++ [("checked", toJson false)])
  let typeText ← liftM <| liftTermElabM do
    withOptions (fun o => o.setBool `pp.all true) do
      return (← Meta.ppExpr ci.type).pretty
  let nativeTypes := KltDP.Audit.Trust.nativeTypeReferences.get (← getOptions)
  let typeExpression ← if nativeTypes && !needsLegacyTypeExpression env n then
      liftM <| nativeTypeReference env n
    else pure (toJson (reprStr ci.type))
  return Json.mkObj (base ++ [
    ("checked", toJson true),
    ("kind", toJson (declarationKind ci)),
    ("universe_parameters", namesJson ci.levelParams.toArray),
    ("type", toJson typeText),
    ("type_expression", typeExpression),
    ("direct_dependencies", namesJson (← cachedDependencies ci)),
    ("unsafe", toJson ci.isUnsafe),
    ("partial", toJson ci.isPartial),
    ("reducibility_hints", toJson (reducibilityHintsName ci)),
    ("noncomputable", toJson (isNoncomputable env n)),
    ("extern", toJson (isExtern env n)),
    ("implemented_by", toJson ((Compiler.getImplementedBy? env n).map Name.toString)),
    ("source_range_present", toJson (declRangeExt.find? env n).isSome),
    ("compiler_cache_owner", toJson (if cache then (compilerStageName? n).map (·.1.toString) else none)),
    ("compiler_cache_stage", toJson (if cache then (compilerStageName? n).map (·.2) else none)),
    ("root_policy_passes", if tooling || cache || implementation then Json.null else toJson (rootPasses env n checkedClosure)),
    ("closure", if tooling then Json.null else closureJson checkedClosure)])

/-- One captured environment; one edge cache; each completed root closure is
used for its inventory record and aggregate audit before it is discarded. -/
def process (env : Environment) (inventory audit : Bool) : ScanM Unit := do
  liftM <| validateLiteratureShape env
  let nativeTypes := KltDP.Audit.Trust.nativeTypeReferences.get (← getOptions)
  let ns := projectDeclarations env
  let caches := ns.filter (fun n => !isAuditTooling env n && isCompilerStageCache env n)
  let implementations := ns.filter (fun n => !isAuditTooling env n &&
    !isCompilerStageCache env n && isUnsafeImplementation env n)
  let roots := ns.filter (fun n => !isAuditTooling env n && !isNonlogicalImplementation env n)
  let mathematicalRoots := roots.filter (fun n => !isSafeRuntimeCompanion env n)
  if audit && !inventory && mathematicalRoots.isEmpty then
    throwError "KLT trust audit has no mathematical declarations to audit"
  if inventory then
    liftM <| emit "KLT_TRUST_INVENTORY_BEGIN" (Json.mkObj [
      ("schema", toJson (inventorySchema nativeTypes)),
      ("compiler_cache_policy", toJson compilerCachePolicy),
      ("foundational_axioms", namesJson foundationalAxioms),
      ("literature_axioms", namesJson literatureAxioms),
      ("declaration_count", toJson ns.size),
      ("scope", toJson "checked declarations owned by KltDP modules or KltDP user names")])
  let mut failures : Array Json := #[]
  let mut allAxioms : NameSet := {}
  for n in ns do
    let tooling := isAuditTooling env n
    let closure ← if tooling then pure {} else closureCached env n
    if inventory then
      liftM <| emit "KLT_TRUST_DECL" (← declarationJsonCached env n closure)
    if audit && !tooling && !isNonlogicalImplementation env n then
      for a in sortedNames closure.axioms do allAxioms := allAxioms.insert a
      unless rootPasses env n closure do
        failures := failures.push (Json.mkObj [
          ("name", toJson n.toString), ("closure", closureJson closure)])
  if inventory then
    liftM <| emit "KLT_TRUST_INVENTORY_END" (Json.mkObj [("declaration_count", toJson ns.size)])
  if audit then
    if mathematicalRoots.isEmpty then
      throwError "KLT trust audit has no mathematical declarations to audit"
    for failure in failures do liftM <| emit "KLT_TRUST_FAILURE" failure
    liftM <| emit "KLT_TRUST_AUDIT" (Json.mkObj [
      ("schema", toJson (inventorySchema nativeTypes)),
      ("compiler_cache_policy", toJson compilerCachePolicy),
      ("mathematical_declaration_count", toJson mathematicalRoots.size),
      ("runtime_companion_count", toJson (roots.size - mathematicalRoots.size)),
      ("compiler_stage_cache_count", toJson caches.size),
      ("unsafe_implementation_count", toJson implementations.size),
      ("failed_declaration_count", toJson failures.size),
      ("transitive_axioms", namesJson (sortedNames allAxioms)),
      ("literature_axioms", namesJson literatureAxioms),
      ("status", toJson (if failures.isEmpty then "dependency_policy_passed" else "dependency_policy_failed")),
      ("manuscript_completeness", toJson "not_assessed_by_dependency_audit")])
    unless failures.isEmpty do
      throwError "KLT trust audit rejected {failures.size} mathematical declarations; inspect KLT_TRUST_FAILURE records"

/-- Compatibility helper for one declaration. Production reports use `process`
so that all roots in the command share one direct-edge cache. This helper uses
the same fast collector and is not an independent historical reference. -/
def declarationJson (env : Environment) (n : Name) : CommandElabM Json := do
  validateLiteratureShape env
  let action : ScanM Json := do
    let closure ← if isAuditTooling env n then pure {} else closureCached env n
    declarationJsonCached env n closure
  action.run' {}

/-- Inventory only, with one direct-edge cache for the captured environment. -/
elab "#klt_trust_inventory" : command => do
  let env ← getEnv
  (process env true false).run' {}

/-- Audit only. This does not certify manuscript coverage or external provenance. -/
elab "#klt_trust_audit" : command => do
  let env ← getEnv
  (process env false true).run' {}

/-- Emit the complete inventory followed by the audit, reusing each completed
root closure and the command-local direct-edge cache. -/
elab "#klt_trust_report" : command => do
  let env ← getEnv
  (process env true true).run' {}

end KltDP.Audit.Trust
