import KltDP.Geometry.RationalTreePicardMatching

/-!
# Restriction compatibility of branch-matching trivializations

Component algebra maps commuting with the original branch evaluations induce
a ring homomorphism on equalizers and a semilinear map on twisted matching
modules. The explicit vertex-unit trivialization commutes with these maps.
These are algebraic restriction maps; no normalization sheaf comparison is
postulated.
-/

noncomputable section

namespace KltDP.Geometry.RationalTreePicard

open SimpleGraph

variable {k V : Type*} [CommRing k] (G : SimpleGraph V)
  (R S : V → Type*) [∀ v, CommRing (R v)] [∀ v, Algebra k (R v)]
  [∀ v, CommRing (S v)] [∀ v, Algebra k (S v)]
  (evR : ∀ d : G.Dart, R d.fst →ₐ[k] k)
  (evS : ∀ d : G.Dart, S d.fst →ₐ[k] k)
  (φ : ∀ v, R v →ₐ[k] S v)
  (hφ : ∀ (d : G.Dart) (x : R d.fst), evS d (φ d.fst x) = evR d x)

/-- Component restriction induces a homomorphism of the actual equalizer
rings. Its underlying map is the original family of algebra maps. -/
def matchingRingMap
    (hφ : ∀ (d : G.Dart) (x : R d.fst), evS d (φ d.fst x) = evR d x) :
    matchingRing G R evR →+* matchingRing G S evS where
  toFun r := ⟨fun v => φ v (r.val v), by
    funext d
    change evS d (φ d.fst (r.val d.fst)) = evS d.symm (φ d.snd (r.val d.snd))
    have hreverse (x : R d.snd) : evS d.symm (φ d.snd x) = evR d.symm x := by
      exact hφ d.symm x
    rw [hφ d (r.val d.fst), hreverse (r.val d.snd)]
    exact matchingRing_condition G R evR r d⟩
  map_zero' := by
    apply Subtype.ext
    funext v
    exact map_zero (φ v)
  map_one' := by
    apply Subtype.ext
    funext v
    exact map_one (φ v)
  map_add' r s := by
    apply Subtype.ext
    funext v
    exact map_add (φ v) (r.val v) (s.val v)
  map_mul' r s := by
    apply Subtype.ext
    funext v
    exact map_mul (φ v) (r.val v) (s.val v)

@[simp]
theorem matchingRingMap_val (r : matchingRing G R evR) (v : V) :
    (matchingRingMap G R S evR evS φ hφ r).val v = φ v (r.val v) := rfl

variable (g : G.Dart → kˣ)

/-- The actual component restrictions preserve all original twisted branch
equations and are semilinear over the induced equalizer-ring map. -/
def matchingSectionsMap :
    matchingSections G R evR g →ₛₗ[matchingRingMap G R S evR evS φ hφ]
      matchingSections G S evS g where
  toFun s := ⟨fun v => φ v (s.val v), by
    intro d
    change evS d (φ d.fst (s.val d.fst)) =
      (g d : k) * evS d.symm (φ d.snd (s.val d.snd))
    have hreverse (x : R d.snd) : evS d.symm (φ d.snd x) = evR d.symm x := by
      exact hφ d.symm x
    rw [hφ d (s.val d.fst), hreverse (s.val d.snd)]
    exact s.property d⟩
  map_add' s t := by
    apply Subtype.ext
    funext v
    exact map_add (φ v) (s.val v) (t.val v)
  map_smul' r s := by
    apply Subtype.ext
    funext v
    change φ v (r.val v * s.val v) = φ v (r.val v) * φ v (s.val v)
    exact map_mul (φ v) _ _

@[simp]
theorem matchingSectionsMap_val (s : matchingSections G R evR g) (v : V) :
    (matchingSectionsMap G R S evR evS φ hφ g s).val v = φ v (s.val v) := rfl

/-- The explicit matching trivialization is natural under the original
component restrictions. The same vertex units are used on both sides. -/
theorem matchingLinearEquiv_natural (b : V → kˣ)
    (hb : ∀ d : G.Dart, b d.fst * g d = b d.snd)
    (s : matchingSections G R evR g) :
    matchingLinearEquiv G S evS g b hb
        (matchingSectionsMap G R S evR evS φ hφ g s) =
      matchingRingMap G R S evR evS φ hφ (matchingLinearEquiv G R evR g b hb s) := by
  apply Subtype.ext
  funext v
  change algebraMap k (S v) (b v : k) * φ v (s.val v) =
    φ v (algebraMap k (R v) (b v : k) * s.val v)
  rw [map_mul, (φ v).commutes]

/-- The tree trivializations therefore form a compatible family under
component restrictions, before any geometric sheaf comparison is made. -/
theorem treeMatchingLinearEquiv_natural (hG : G.IsTree)
    (hreverse : ∀ d : G.Dart, g d.symm = (g d)⁻¹) (root : V)
    (s : matchingSections G R evR g) :
    treeMatchingLinearEquiv G S evS g hG hreverse root
        (matchingSectionsMap G R S evR evS φ hφ g s) =
      matchingRingMap G R S evR evS φ hφ
        (treeMatchingLinearEquiv G R evR g hG hreverse root s) :=
  matchingLinearEquiv_natural G R S evR evS φ hφ g
    (KltDP.Combinatorics.treePotential hG g root)
    (fun d => (KltDP.Combinatorics.treePotential_edge hG g hreverse root d.adj).symm) s

end KltDP.Geometry.RationalTreePicard
