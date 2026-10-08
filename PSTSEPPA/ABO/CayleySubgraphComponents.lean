import PSTSEPPA.ABO.CayleySubgraph

/-!
# Intrinsic connected components of Cayley skeletons

An arbitrary ABO skeleton is not a complete E-graph.  Its components must
therefore be determined by realised paths, not by simply intersecting the
skeleton's vertex set with ambient subalphabet cosets.

We first prove word concatenation and inversion for the explicit path
relation in arbitrary deterministic E-graphs.  Intrinsic C-reachability in
a skeleton is then reflexive, symmetric and transitive, and the C-component
of a vertex is an equivalence class of this relation.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V E ι : Type*} (G : EGraph V E ι)

/-- Concatenating two actually realised paths in a possibly incomplete
E-graph gives an actually realised concatenated word. -/
theorem follows_append
    {u v z : V} {p q : LabelWord ι}
    (hp : G.Follows u p v) (hq : G.Follows v q z) :
    G.Follows u (p ++ q) z := by
  induction hp with
  | nil u =>
      simpa using hq
  | @cons u v s w e hs hl hrest ih =>
      exact EGraph.Follows.cons e hs hl (ih hq)

/-- Reverse every directed edge and invert the word, to follow a realised
path in the opposite direction. The proof uses formal inverse edge tokens,
so geometric loops pose no exceptional case. -/
theorem follows_inverse
    {u v : V} {w : LabelWord ι}
    (hp : G.Follows u w v) :
    G.Follows v (PSTS.SignedWord.inv w) u := by
  induction hp with
  | nil u =>
      simpa using (EGraph.Follows.nil u)
  | @cons u v s w e hs hl hrest ih =>
      rw [PSTS.SignedWord.inv_cons]
      have hback :
          G.Follows (G.target e) [PSTS.SignedLetter.inv s] u := by
        refine EGraph.Follows.cons (G.inv e) ?_ ?_ ?_
        · rfl
        · calc
            G.label (G.inv e) =
                PSTS.SignedLetter.inv (G.label e) :=
              G.toLabelledGraph.label_inv_eq e
            _ = PSTS.SignedLetter.inv s :=
              congrArg PSTS.SignedLetter.inv hl
        · have ht : G.target (G.inv e) = u := by
            change G.source (G.inv (G.inv e)) = u
            rw [G.inv_inv]
            exact hs
          rw [ht]
          exact EGraph.Follows.nil u
      exact G.follows_append ih hback

end EGraph

namespace CayleySubgraphSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}
variable (K : CayleySubgraphSpec gen A)

/-- Intrinsic C-reachability is transitive, including in incomplete skeletons. -/
theorem subalphabetReachable_trans
    (C : Finset ι) {x y z : K.Vertex}
    (hxy : K.SubalphabetReachable C x y)
    (hyz : K.SubalphabetReachable C y z) :
    K.SubalphabetReachable C x z := by
  rcases hxy with ⟨p, hpC, hp⟩
  rcases hyz with ⟨q, hqC, hq⟩
  exact
    ⟨p ++ q,
      (LabelWord.uses_append C p q).2 ⟨hpC, hqC⟩,
      (K.toEGraph).follows_append hp hq⟩

/-- Intrinsic C-reachability is symmetric, using the formal inverse edges
present in every Cayley skeleton. -/
theorem subalphabetReachable_symm
    (C : Finset ι) {x y : K.Vertex}
    (hxy : K.SubalphabetReachable C x y) :
    K.SubalphabetReachable C y x := by
  rcases hxy with ⟨w, hwC, hw⟩
  exact
    ⟨PSTS.SignedWord.inv w,
      hwC.inv,
      (K.toEGraph).follows_inverse hw⟩

/-- The vertex C-component is an actual path-reachability class, rather
than merely the intersection of a set with an ambient C-coset. -/
def SubalphabetComponent
    (C : Finset ι) (x : K.Vertex) : Set K.Vertex :=
  {y | K.SubalphabetReachable C x y}

theorem mem_subalphabetComponent_iff
    (C : Finset ι) (x y : K.Vertex) :
    y ∈ K.SubalphabetComponent C x ↔
      K.SubalphabetReachable C x y :=
  Iff.rfl

theorem self_mem_subalphabetComponent
    (C : Finset ι) (x : K.Vertex) :
    x ∈ K.SubalphabetComponent C x :=
  K.subalphabetReachable_refl C x

/-- Members of one intrinsic component determine exactly the same component. -/
theorem subalphabetComponent_eq_of_reachable
    (C : Finset ι) {x y : K.Vertex}
    (hxy : K.SubalphabetReachable C x y) :
    K.SubalphabetComponent C x = K.SubalphabetComponent C y := by
  ext z
  constructor
  · intro hxz
    exact
      K.subalphabetReachable_trans C
        (K.subalphabetReachable_symm C hxy) hxz
  · intro hyz
    exact K.subalphabetReachable_trans C hxy hyz

/-- Every intrinsic C-component is contained in the corresponding
ambient C-coset, even if the skeleton omits some C-edges. -/
theorem component_subset_ambientCoset
    (C : Finset ι) (x : K.Vertex)
    {y : K.Vertex}
    (hy : y ∈ K.SubalphabetComponent C x) :
    y.1 ∈ generatedLeftCoset gen C x.1 :=
  K.subalphabetReachable_implies_coset C x y hy

end CayleySubgraphSpec

end ABO
end PSTSEPPA
