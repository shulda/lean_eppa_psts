import PSTSEPPA.ABO.ComponentSubgraphPaths

/-!
# Exact restriction of an ambient Cayley skeleton to any subalphabet

To apply a corrected ABO rank-two stage to a single ambient skeleton
K over a larger alphabet S, we must produce honest Cayley skeletons
K|B over all two-letter subalphabets B. This module constructs the
literal edge-filtered restriction, retaining ALL old vertices and
exactly the genuine directed edges labelled in B.

We prove that the inclusion preserves formal inverse edge tokens,
is injective on vertices and edges, and reflects EVERY realised
signed path whose word is supported on B. Thus its intrinsic
C-component relation, for every C⊆B, is EXACTLY the ambient one.

There is no group retractability, amalgamation, or completion
assumption. Missing edges remain missing. In particular this is
stronger than a purely ambient group-coset restriction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen S)

/-- The SAME vertex set, and precisely the REAL signed edges
of the original skeleton whose underlying label lies in B.
No assumption B⊆S is needed: non-S labels had no old edges. -/
def restrictAlphabet (B : Finset ι) :
    CayleySubgraphSpec gen B where
  vertices := K.vertices
  edges := {e | e ∈ K.edges ∧ signedBase e.2 ∈ B}
  source_mem := by
    intro e he
    exact K.source_mem e he.1
  inv_mem := by
    intro e he
    refine ⟨K.inv_mem e he.1, ?_⟩
    change signedBase (PSTS.SignedLetter.inv e.2) ∈ B
    simpa only [signedBase_inv] using he.2
  label_mem := by
    intro e he
    change signedBase e.2 ∈ B
    exact he.2

/-- The exact inclusion, with identity vertex function and
underlying signed edge token unchanged. -/
noncomputable def restrictAlphabetHom (B : Finset ι) :
    LabelledGraphHom
      ((K.restrictAlphabet B).toEGraph).toLabelledGraph
      (K.toEGraph).toLabelledGraph where
  onVertex := fun x => x
  onEdge := fun e => ⟨e.1, e.2.1⟩
  map_source := by
    intro e
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    rfl
  map_label := by
    intro e
    rfl

/-- This literal alphabet restriction loses no old vertices. -/
theorem restrictAlphabetHom_vertex_injective (B : Finset ι) :
    Function.Injective (K.restrictAlphabetHom B).onVertex := by
  intro x y h
  exact h

/-- Nor does it identify distinct signed oriented edge tokens. -/
theorem restrictAlphabetHom_edge_injective (B : Finset ι) :
    Function.Injective (K.restrictAlphabetHom B).onEdge := by
  intro e f h
  apply Subtype.ext
  exact congrArg (fun t : K.Edge => t.1) h

/-- Lift a realised ambient path whose ACTUAL signed word uses
only B into the edge-filtered B-skeleton. Every step is the
very same old directed edge, including inverses and loops. -/
theorem follows_lift_restrictAlphabet
    (B : Finset ι)
    {u v : K.Vertex} {w : LabelWord ι}
    (hp : (K.toEGraph).Follows u w v)
    (hw : LabelWord.Uses B w) :
    ((K.restrictAlphabet B).toEGraph).Follows u w v := by
  induction hp with
  | nil u =>
      exact EGraph.Follows.nil _
  | @cons u v s w e hs hl hrest ih =>
      have heB : signedBase e.1.2 ∈ B := by
        change signedBase ((K.toEGraph).label e) ∈ B
        rw [hl]
        exact hw.1
      let f : (K.restrictAlphabet B).Edge :=
        ⟨e.1, ⟨e.2, heB⟩⟩
      refine EGraph.Follows.cons f ?_ ?_ ?_
      · exact hs
      · exact hl
      · exact ih hw.2

/-- EXACT correspondence of realised signed paths for B-words,
with no substitution of a path in the ambient Cayley graph. -/
theorem restrictAlphabet_follows_iff
    (B : Finset ι) (u v : K.Vertex)
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    ((K.restrictAlphabet B).toEGraph).Follows u w v ↔
      (K.toEGraph).Follows u w v := by
  constructor
  · intro hp
    exact hp.map (K.restrictAlphabetHom B)
  · intro hp
    exact K.follows_lift_restrictAlphabet B hp hw

/-- Therefore actual intrinsic C-components (C⊆B) coincide
between the original skeleton and its B-edge restriction.
This works for arbitrary incomplete input skeletons. -/
theorem restrictAlphabet_subalphabetReachable_iff
    (B C : Finset ι) (hCB : C ⊆ B)
    (x y : K.Vertex) :
    (K.restrictAlphabet B).SubalphabetReachable C x y ↔
      K.SubalphabetReachable C x y := by
  constructor
  · rintro ⟨w, hw, hp⟩
    have hwB : LabelWord.Uses B w := hw.mono hCB
    exact ⟨w, hw, (K.restrictAlphabet_follows_iff B x y w hwB).mp hp⟩
  · rintro ⟨w, hw, hp⟩
    have hwB : LabelWord.Uses B w := hw.mono hCB
    exact ⟨w, hw, (K.restrictAlphabet_follows_iff B x y w hwB).mpr hp⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
