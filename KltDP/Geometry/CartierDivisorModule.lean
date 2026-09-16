import KltDP.Geometry.CartierPrincipalModuleLocal
import KltDP.Compatibility.SheafSubmodule

/-!
# The actual module sheaf O(D)

For an actual global Cartier section `D`, we define a submodule of the
actual rational-function module sheaf. A section belongs when, on every
nonempty smaller open with an actual equation `f` for `D`, its rational
value lies in `f⁻¹ O`. Restriction stability and locality of this condition
are proved. The reviewed submodule-sheaf constructor therefore supplies
an actual module sheaf, with its actual inclusion into rational functions.

On an open with equation `f`, membership is exactly membership in the
principal fractional module `f⁻¹ O(U)`. Local rank-one trivializations of
the resulting sheaf are a separate next construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- Being a local equation for an actual global Cartier divisor is
preserved by restriction to a nonempty smaller open. -/
theorem cartierGlobalEquation_restrict (D : CartierDivisor X)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    cartierEquationClassHom X V (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D := by
  have hcomp : (homOfLE (show U ≤ ⊤ from le_top)).op ≫ i.op =
      (homOfLE (show V ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
  calc
    cartierEquationClassHom X V (Additive.ofMul f) =
        (cartierDivisorSheaf X).val.map i.op
          (cartierEquationClassHom X U (Additive.ofMul f)) :=
      (cartierEquationClassHom_restrict X i.le f).symm
    _ = (cartierDivisorSheaf X).val.map i.op
        ((cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :=
      congrArg _ hf
    _ = (cartierDivisorSheaf X).val.map
        ((homOfLE (show U ≤ ⊤ from le_top)).op ≫ i.op) D :=
      (ConcreteCategory.congr_hom ((cartierDivisorSheaf X).val.map_comp _ _) D).symm
    _ = _ := congrArg (fun j => (cartierDivisorSheaf X).val.map j D) hcomp

/-- The section condition, kept separate from its bundled submodule. -/
private def cartierSectionCondition (D : CartierDivisor X) (U : X.Opens)
    (s : (rationalFunctionModule X).val.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (i : V ⟶ U) (hV : Nonempty V),
    letI := hV
    ∀ f : X.functionFieldˣ,
      cartierEquationClassHom X V (Additive.ofMul f) =
          (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D →
        rationalFunctionModuleSectionsEquiv X V
          ((rationalFunctionModule X).val.map i.op s) ∈ principalEquationSubmodule X V f

/-- Sections which lie in `f⁻¹ O` for every actual smaller equation chart. -/
def cartierSectionSubmodule (D : CartierDivisor X) (U : X.Opens) :
    Submodule Γ(X, U) ((rationalFunctionModule X).val.obj (op U)) where
  carrier := cartierSectionCondition X D U
  zero_mem' := by
    intro V i hV
    letI := hV
    intro f hf
    simpa only [map_zero] using (principalEquationSubmodule X V f).zero_mem
  add_mem' := by
    intro s t hs ht V i hV
    letI := hV
    intro f hf
    simpa only [map_add] using
      (principalEquationSubmodule X V f).add_mem (hs V i hV f hf) (ht V i hV f hf)
  smul_mem' := by
    intro a s hs V i hV
    letI := hV
    intro f hf
    have hrestrict :
        (rationalFunctionModule X).val.map i.op (a • s) =
          X.presheaf.map i.op a •
            (rationalFunctionModule X).val.map i.op s :=
      (rationalFunctionModule X).val.map_smul i.op a s
    have hlinear :
        rationalFunctionModuleSectionsEquiv X V
            (X.presheaf.map i.op a •
              (rationalFunctionModule X).val.map i.op s) =
          X.presheaf.map i.op a •
            rationalFunctionModuleSectionsEquiv X V
              ((rationalFunctionModule X).val.map i.op s) :=
      LinearEquiv.map_smul
        (rationalFunctionModuleSectionsEquiv X V)
        (X.presheaf.map i.op a)
        ((rationalFunctionModule X).val.map i.op s)
    have hsmul :=
      (congrArg
        (fun t : (rationalFunctionModule X).val.obj (op V) =>
          rationalFunctionModuleSectionsEquiv X V t)
        hrestrict).trans hlinear
    exact Eq.mpr
      (congrArg
        (fun z : X.functionField => z ∈ principalEquationSubmodule X V f)
        hsmul)
      ((principalEquationSubmodule X V f).smul_mem
        (X.presheaf.map i.op a) (hs V i hV f hf))

private theorem rationalModule_restrict_comp {U V W : X.Opens}
    (i : W ⟶ V) (j : V ⟶ U) (s : (rationalFunctionModule X).val.obj (op U)) :
    (rationalFunctionModule X).val.map (i ≫ j).op s =
      (rationalFunctionModule X).val.map i.op
        ((rationalFunctionModule X).val.map j.op s) :=
  ConcreteCategory.congr_hom ((rationalFunctionModule X).val.presheaf.map_comp j.op i.op) s

/-- The actual section submodules are stable under restriction. -/
def cartierDivisorPresheafSubmodule (D : CartierDivisor X) :
    (rationalFunctionModule X).val.Submodule where
  obj U := cartierSectionSubmodule X D U.unop
  map {U V} j := by
    intro s hs
    change (rationalFunctionModule X).val.map j s ∈ cartierSectionSubmodule X D V.unop
    intro W i hW
    letI := hW
    intro f hf
    have hm := hs W (i ≫ j.unop) hW f hf
    exact Eq.mp
      (congrArg
        (fun t : (rationalFunctionModule X).val.obj (op W) =>
          rationalFunctionModuleSectionsEquiv X W t ∈ principalEquationSubmodule X W f)
        (rationalModule_restrict_comp X i j.unop s)) hm

/-- Membership in the actual divisor submodule is local for the
open-set Grothendieck topology. -/
theorem cartierDivisorPresheafSubmodule_isSheaf (D : CartierDivisor X)
    {U : (X.Opens)ᵒᵖ} (s : (rationalFunctionModule X).val.obj U)
    (hlocal : (cartierDivisorPresheafSubmodule X D).toSubfunctor.sieveOfSection s ∈
      Opens.grothendieckTopology X U.unop) :
    s ∈ (cartierDivisorPresheafSubmodule X D).obj U := by
  intro V i hV
  letI := hV
  intro f hf
  apply mem_principalEquationSubmodule_of_locally_mem X V f
  intro x hx
  obtain ⟨W, j, hW, hxW⟩ := hlocal x (i.le hx)
  let T : X.Opens := V ⊓ W
  have hxT : x ∈ T := ⟨hx, hxW⟩
  letI : Nonempty T := ⟨⟨x, hxT⟩⟩
  let iV : T ⟶ V := homOfLE inf_le_left
  let iW : T ⟶ W := homOfLE inf_le_right
  have hfT := cartierGlobalEquation_restrict X D iV f hf
  change (rationalFunctionModule X).val.map j.op s ∈ cartierSectionSubmodule X D W at hW
  have hm := hW T iW inferInstance f hfT
  have hpaths : iW ≫ j = iV ≫ i := Subsingleton.elim _ _
  have heq : rationalFunctionModuleSectionsEquiv X T
      ((rationalFunctionModule X).val.map iW.op
        ((rationalFunctionModule X).val.map j.op s)) =
      rationalFunctionModuleSectionsEquiv X V
        ((rationalFunctionModule X).val.map i.op s) := by
    rw [← rationalModule_restrict_comp, hpaths, rationalModule_restrict_comp]
    exact rationalFunctionModuleSectionsEquiv_naturality X iV _
  exact ⟨T, iV, hxT, heq ▸ hm⟩

/-- The actual O(D) subsheaf, using the proved locality condition. -/
def cartierDivisorSubmodule (D : CartierDivisor X) :
    (rationalFunctionModule X).Submodule where
  toSubmodule := cartierDivisorPresheafSubmodule X D
  isSheaf := fun {U} s hs => cartierDivisorPresheafSubmodule_isSheaf X D (U := U) s hs

/-- The actual structure-sheaf module O(D), contained in rational functions. -/
def cartierDivisorModule (D : CartierDivisor X) : X.Modules :=
  (cartierDivisorSubmodule X D).toSheafOfModules

/-- The actual inclusion O(D) → K_X. -/
def cartierDivisorModuleInclusion (D : CartierDivisor X) :
    cartierDivisorModule X D ⟶ rationalFunctionModule X :=
  (cartierDivisorSubmodule X D).ι

/-- Expose the original carrier predicate without specializing its quantifiers. -/
private theorem condition_of_cartier_mem (D : CartierDivisor X) (U : X.Opens)
    (s : (rationalFunctionModule X).val.obj (op U))
    (hs : s ∈ cartierSectionSubmodule X D U) :
    cartierSectionCondition X D U s := hs

/-- Eliminate the defining condition at a separately quantified equation chart.
Keeping the chart separate from the ambient open isolates the dependent
carrier projection from later identity-chart specialization. -/
private theorem cartier_condition_equation_chart (D : CartierDivisor X)
    (U V : X.Opens) [Nonempty V] (i : V ⟶ U)
    (s : (rationalFunctionModule X).val.obj (op U))
    (hs : cartierSectionCondition X D U s)
    (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X V (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D) :
    rationalFunctionModuleSectionsEquiv X V
        ((rationalFunctionModule X).val.map i.op s) ∈ principalEquationSubmodule X V f :=
  hs V i inferInstance f hf

/-- Express chart membership in the ambient open's field coordinates before
specializing the chart to the ambient open. The conclusion does not contain
a restriction map, so its later identity-chart specialization needs no
comparison of concrete identity restriction terms. -/
private theorem cartier_condition_ambient_field (D : CartierDivisor X)
    (U V : X.Opens) [Nonempty U] [Nonempty V] (i : V ⟶ U)
    (s : (rationalFunctionModule X).val.obj (op U))
    (hs : cartierSectionCondition X D U s)
    (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X V (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D) :
    rationalFunctionModuleSectionsEquiv X U s ∈ principalEquationSubmodule X V f := by
  have hm := cartier_condition_equation_chart X D U V i s hs f hf
  exact Eq.mp
    (congrArg
      (fun z : X.functionField => z ∈ principalEquationSubmodule X V f)
      (rationalFunctionModuleSectionsEquiv_naturality X i s)) hm

private theorem principal_mem_of_cartier_mem (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (s : (rationalFunctionModule X).val.obj (op U))
    (hs : s ∈ cartierSectionSubmodule X D U) :
    rationalFunctionModuleSectionsEquiv X U s ∈ principalEquationSubmodule X U f :=
  cartier_condition_ambient_field X D U U (𝟙 U) s
    (condition_of_cartier_mem X D U s hs) f hf

private theorem cartier_mem_of_principal_mem (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (s : (rationalFunctionModule X).val.obj (op U))
    (hs : rationalFunctionModuleSectionsEquiv X U s ∈ principalEquationSubmodule X U f) :
    s ∈ cartierSectionSubmodule X D U := by
  intro V i hV
  letI := hV
  intro g hg
  have hfV := cartierGlobalEquation_restrict X D i f hf
  have hsV : rationalFunctionModuleSectionsEquiv X U s ∈
      principalEquationSubmodule X V f :=
    mem_principalEquationSubmodule_restrict X i.le f hs
  have hmem : rationalFunctionModuleSectionsEquiv X U s ∈
      principalEquationSubmodule X V g :=
    Eq.mp
      (congrArg
        (fun P : Submodule Γ(X, V) X.functionField =>
          rationalFunctionModuleSectionsEquiv X U s ∈ P)
        (principalEquationSubmodule_eq_of_class_eq X V f g (hfV.trans hg.symm))) hsV
  exact Eq.mpr
    (congrArg
      (fun z : X.functionField => z ∈ principalEquationSubmodule X V g)
      (rationalFunctionModuleSectionsEquiv_naturality X i s)) hmem

/-- On an actual equation chart, the defining condition is precisely
membership in `f⁻¹ O(U)` with the same function-field comparison. -/
theorem mem_cartierSectionSubmodule_iff (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (s : (rationalFunctionModule X).val.obj (op U)) :
    s ∈ cartierSectionSubmodule X D U ↔
      rationalFunctionModuleSectionsEquiv X U s ∈ principalEquationSubmodule X U f :=
  ⟨principal_mem_of_cartier_mem X D U f hf s,
    cartier_mem_of_principal_mem X D U f hf s⟩

end KltDP.Geometry
