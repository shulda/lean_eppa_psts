import PSTSEPPA.ABO.SourceLiteralY1RootComponentVertexEquiv
import PSTSEPPA.ABO.LabelledGroupSingleCosetGraphIso
import PSTSEPPA.ABO.BijectiveGraphPathReflection

/-!
# True original rooted A-component signed graph equivalence

The finite-indexed first-rank literal paper T(Y₁) old-edge cover is
already known to be isomorphic over the ORIGINAL incomplete input
to the independent source H₁ old-edge cover. The exact root-A-component
vertex equivalence is also established, using realised signed paths.

Here we identify ALL actual oriented signed edges IN EACH CHOSEN
A-component, not only its vertices or ambient group coordinates.
A component edge is characterized by:
1. actual OLD edge membership in the incomplete parent skeleton;
2. signed label belonging to A;
3. its source lying in the actual rooted A-component.
All three conditions are transported and reflected. As a result the
rooted components are isomorphic as signed EGraphs, bijective on
vertices and formal directed edge tokens, and all realised signed
paths are preserved AND reflected, including inverse edges and loops.

This does not identify the selected *completed* coset quotient or
the augmented Z₁ stages. It is the precise old-edge geometric input
for transporting those corrected Definition-5.3 stages.
-/

namespace PSTSEPPA
namespace ABO

namespace CayleySubgraphSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}
variable (K : CayleySubgraphSpec gen S)

/-- Actual signed edges of an intrinsic B-component are precisely
its parent OLD B-edges whose SOURCE lies in that component.
No arbitrary ambient Cayley edge is admitted. -/
theorem componentSubgraph_edge_mem_iff
    (B : Finset ι) (root : K.Vertex) (e : ActionEdge Γ ι) :
    e ∈ (K.subalphabetComponentSubgraph B root).edges ↔
      e ∈ K.edges ∧ signedBase e.2 ∈ B ∧
        e.1 ∈ (K.subalphabetComponentSubgraph B root).vertices := by
  constructor
  · rintro ⟨f, rfl, hB, hreach⟩
    exact ⟨f.2, hB, ⟨(K.toEGraph).source f, rfl, hreach⟩⟩
  · rintro ⟨he, hB, ⟨u, hu, hreach⟩⟩
    let f : K.Edge := ⟨e, he⟩
    have hsource : (K.toEGraph).source f = u :=
      Subtype.ext hu.symm
    refine ⟨f, rfl, hB, ?_⟩
    rw [hsource]
    exact hreach

end CayleySubgraphSpec

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- An ACTUAL original oriented signed edge lies in a chosen
paper T(Y₁) root-A-component iff its group-isomorphic edge lies
in the corresponding source-H₁ root-A-component.
The test is based on realised original edges and A-paths. -/
theorem sourceLiteralY1Direct_rootA_component_edge_iff
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (e : ActionEdge (sourceLiteralY1 src dst).transitionGroup ι) :
    e ∈ (sourceLiteralY1DirectRootComponent src dst base A root).edges ↔
    ((sourceH1EquivLiteralY1Transition src dst).symm e.1, e.2) ∈
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).edges := by
  let L := sourceLiteralY1DirectOriginalSkeleton src dst base
  let K := sourceH1OriginalSkeleton src dst base
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  let rL : (L.restrictAlphabet A).Vertex := ⟨root, by trivial⟩
  let rK : (K.restrictAlphabet A).Vertex := ⟨E root, by trivial⟩
  have horig : e ∈ L.edges ↔ (E e.1, e.2) ∈ K.edges := by
    have h := sourceLiteralY1DirectOriginal_edge_iff_sourceH1
      src dst base (E e.1) e.2
    simpa [E] using h
  have hrestrict :
      e ∈ (L.restrictAlphabet A).edges ↔
      (E e.1, e.2) ∈ (K.restrictAlphabet A).edges := by
    change (e ∈ L.edges ∧ signedBase e.2 ∈ A) ↔
      ((E e.1, e.2) ∈ K.edges ∧ signedBase e.2 ∈ A)
    exact and_congr horig Iff.rfl
  have hcomponent :
      e.1 ∈ (sourceLiteralY1DirectRootComponent src dst base A root).vertices ↔
        E e.1 ∈
          (sourceH1OriginalRootComponent src dst base A (E root)).vertices :=
    sourceLiteralY1Direct_rootA_component_vertex_iff src dst base A root e.1
  have hsource :=
    (L.restrictAlphabet A).componentSubgraph_edge_mem_iff A rL e
  have htarget :=
    (K.restrictAlphabet A).componentSubgraph_edge_mem_iff A rK (E e.1, e.2)
  change
    e ∈ ((L.restrictAlphabet A).subalphabetComponentSubgraph A rL).edges ↔
      (E e.1, e.2) ∈
        ((K.restrictAlphabet A).subalphabetComponentSubgraph A rK).edges
  exact hsource.trans
    ((and_congr hrestrict (and_congr Iff.rfl hcomponent)).trans
      htarget.symm)

/-- An actual signed oriented-edge equivalence for each selected
root-A-component, with no ambient-coset identification.
All formal inverse edge tokens remain separate. -/
noncomputable def sourceLiteralY1Direct_rootA_component_edgeEquiv
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1DirectRootComponent src dst base A root).Edge ≃
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).Edge where
  toFun e :=
    ⟨((sourceH1EquivLiteralY1Transition src dst).symm e.1.1, e.1.2),
      (sourceLiteralY1Direct_rootA_component_edge_iff
        src dst base A root e.1).mp e.2⟩
  invFun e :=
    ⟨((sourceH1EquivLiteralY1Transition src dst) e.1.1, e.1.2), by
      apply (sourceLiteralY1Direct_rootA_component_edge_iff
        src dst base A root
          ((sourceH1EquivLiteralY1Transition src dst) e.1.1, e.1.2)).mpr
      simpa using e.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · simp
    · rfl
  right_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · simp
    · rfl

/-- The TRUE rooted old signed A-components form isomorphic labelled
graphs, with their already-certified vertex and new edge equivalences.
No completion edge of the initial X₁ is introduced. -/
noncomputable def sourceLiteralY1Direct_rootA_component_graphHom
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      ((sourceLiteralY1DirectRootComponent src dst base A root).toEGraph).toLabelledGraph
      ((sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).toEGraph).toLabelledGraph := by
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  let genL := (sourceLiteralY1 src dst).transitionSubgroupGenerator
  let genK := sourceH1Generator src dst
  refine
    { onVertex := sourceLiteralY1Direct_rootA_component_vertexEquiv src dst base A root
      onEdge := sourceLiteralY1Direct_rootA_component_edgeEquiv src dst base A root
      map_source := ?_
      map_inv := ?_
      map_label := ?_ }
  · intro e
    apply Subtype.ext
    rfl
  · intro e
    apply Subtype.ext
    apply Prod.ext
    · have hstep :
          E (e.1.1 * PSTS.SignedWord.evalGroupLetter genL e.1.2) =
            E e.1.1 * PSTS.SignedWord.evalGroupLetter genK e.1.2 := by
        rw [map_mul,
          labelledMulEquiv_evalGroupLetter genL genK E
            (sourceLiteralY1Generator_to_sourceH1 src dst) e.1.2]
      simp only [sourceLiteralY1Direct_rootA_component_edgeEquiv,
        CayleySubgraphSpec.toEGraph, CayleySubgraphSpec.toLabelledGraph]
      change E ((cayleyGraph genL).target e.1) =
        (cayleyGraph genK).target (E e.1.1, e.1.2)
      rw [cayleyGraph.target_eq_mul_evalGroupLetter,
        cayleyGraph.target_eq_mul_evalGroupLetter]
      exact hstep
    · rfl
  · intro e
    rfl

/-- The old signed rooted A-component isomorphism is bijective
on BOTH actual vertices and all formal directed edge tokens. -/
theorem sourceLiteralY1Direct_rootA_component_graphHom_bijective
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Bijective
      (sourceLiteralY1Direct_rootA_component_graphHom
        src dst base A root).onVertex ∧
    Function.Bijective
      (sourceLiteralY1Direct_rootA_component_graphHom
        src dst base A root).onEdge :=
  ⟨(sourceLiteralY1Direct_rootA_component_vertexEquiv
      src dst base A root).bijective,
    (sourceLiteralY1Direct_rootA_component_edgeEquiv
      src dst base A root).bijective⟩

/-- ALL genuinely realised signed paths in the paper root-A-component
are preserved AND reflected in the corresponding source H₁ component.
No ambient subgroup word calculation substitutes for missing old edges. -/
theorem sourceLiteralY1Direct_rootA_component_graphHom_follows_iff
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u v : (sourceLiteralY1DirectRootComponent
      src dst base A root).Vertex)
    (w : LabelWord ι) :
    ((sourceLiteralY1DirectRootComponent
      src dst base A root).toEGraph).Follows u w v ↔
    ((sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).toEGraph).Follows
      ((sourceLiteralY1Direct_rootA_component_graphHom
        src dst base A root).onVertex u) w
      ((sourceLiteralY1Direct_rootA_component_graphHom
        src dst base A root).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1Direct_rootA_component_graphHom src dst base A root)
    (sourceLiteralY1Direct_rootA_component_graphHom_bijective
      src dst base A root).1
    (sourceLiteralY1Direct_rootA_component_graphHom_bijective
      src dst base A root).2 u v w

end ABO
end PSTSEPPA
