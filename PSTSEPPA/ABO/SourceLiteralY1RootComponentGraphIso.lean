import PSTSEPPA.ABO.SourceLiteralY1RootComponentVertexEquiv
import PSTSEPPA.ABO.LabelledGroupSingleCosetGraphIso

/-!
# Signed graph isomorphism of genuinely rooted old A-components in paper T(Y₁)

The exact paper T(Y₁) and SourceH₁ original incomplete covering
signed EGraphs are already known to be isomorphic, and #503 compares
vertices of each ACTUAL old A-connected component. Here we complete
the missing signed ORIENTED EDGE comparison for each such component.

The key proof uses a general elementary characterization of the edges
of a genuine B-rooted, B-restricted Cayley subgraph: precisely OLD
signed B-edges whose source belongs to the actual reached root
component. Thus no X₁-only artificial complete edge is ever added.
Our group map carries old edge membership and root-component
membership in both directions, so it induces a bijection of all
formal oriented signed edges, preserves their sources, labels and
inversion, and reflects each chronological signed path.

This is the genuine *old input rooted skeleton* graph isomorphism
needed before applying exact coset-gluing naturality and identifying
the selected completed Definition-5.3 stages. No full completed
coset-extension or augmentation is asserted here.
-/

namespace PSTSEPPA
namespace ABO

namespace CayleySubgraphSpec
variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {S : Finset ι}
variable (K : CayleySubgraphSpec gen S)

/-- An oriented edge is in the actual rooted B-component of the
literal B-edge restriction iff it is a REAL original B-edge and its
source belongs to the original *intrinsic* rooted B-component.
No ambient group B-coset replacement. -/
theorem restrictedRootComponent_edge_iff
    (B : Finset ι)
    (root : (K.restrictAlphabet B).Vertex)
    (e : ActionEdge Γ ι) :
    e ∈ ((K.restrictAlphabet B).subalphabetComponentSubgraph B root).edges ↔
      e ∈ K.edges ∧ signedBase e.2 ∈ B ∧
      e.1 ∈ ((K.restrictAlphabet B).subalphabetComponentSubgraph B root).vertices := by
  constructor
  · rintro ⟨f, hf, _hb, hr⟩
    have hOld : e ∈ K.edges := by
      simpa only [hf] using f.2.1
    have hB : signedBase e.2 ∈ B := by
      simpa only [hf] using f.2.2
    refine ⟨hOld, hB, ?_⟩
    exact ⟨((K.restrictAlphabet B).toEGraph).source f,
      congrArg Prod.fst hf, hr⟩
  · rintro ⟨hOld, hB, ⟨u, hu, hr⟩⟩
    let f : (K.restrictAlphabet B).Edge := ⟨e, ⟨hOld, hB⟩⟩
    have hsrc : ((K.restrictAlphabet B).toEGraph).source f = u := by
      apply Subtype.ext
      exact hu.symm
    refine ⟨f, rfl, hB, ?_⟩
    rw [hsrc]
    exact hr

end CayleySubgraphSpec

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Actual old original signed edge membership in the literal paper
cover is equivalent to membership after transporting its group source
coordinate by the genuine labelled T(Y₁)≃*SourceH₁ isomorphism. -/
theorem sourceLiteralY1Direct_original_edge_iff_source
    (src dst : ι → V) (base : V)
    (e : ActionEdge (sourceLiteralY1 src dst).transitionGroup ι) :
    e ∈ (sourceLiteralY1DirectOriginalSkeleton src dst base).edges ↔
      ((sourceH1EquivLiteralY1Transition src dst).symm e.1, e.2) ∈
        (sourceH1OriginalSkeleton src dst base).edges := by
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  have h := sourceLiteralY1DirectOriginal_edge_iff_sourceH1
    src dst base (E e.1) e.2
  have hgroup :
      (sourceH1EquivLiteralY1Transition src dst) (E e.1) = e.1 := by
    simp [E]
  simpa only [hgroup] using h

/-- An ACTUAL old A-component oriented signed edge belongs to the
literal paper rooted component iff its corresponding SourceH₁ edge
belongs to the actual corresponding rooted component. In particular
matching ambient group cosets is not the membership test. -/
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
  change e ∈ ((L.restrictAlphabet A).subalphabetComponentSubgraph A rL).edges ↔
      (E e.1, e.2) ∈ ((K.restrictAlphabet A).subalphabetComponentSubgraph A rK).edges
  rw [L.restrictedRootComponent_edge_iff A rL e,
      K.restrictedRootComponent_edge_iff A rK (E e.1,e.2)]
  constructor
  · rintro ⟨hOld, hB, hroot⟩
    exact ⟨(sourceLiteralY1Direct_original_edge_iff_source src dst base e).mp hOld,
      hB, (sourceLiteralY1Direct_rootA_component_vertex_iff
        src dst base A root e.1).mp hroot⟩
  · rintro ⟨hOld, hB, hroot⟩
    exact ⟨(sourceLiteralY1Direct_original_edge_iff_source src dst base e).mpr hOld,
      hB, (sourceLiteralY1Direct_rootA_component_vertex_iff
        src dst base A root e.1).mpr hroot⟩

/-- All TRUE original signed oriented edge tokens of each printed T(Y₁)
rooted A-component correspond bijectively to those of the source H₁
rooted A-component, preserving their genuine edge support. -/
noncomputable def sourceLiteralY1Direct_rootA_component_edgeEquiv
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1DirectRootComponent src dst base A root).Edge ≃
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).Edge where
  toFun p :=
    ⟨((sourceH1EquivLiteralY1Transition src dst).symm p.1.1, p.1.2),
      (sourceLiteralY1Direct_rootA_component_edge_iff
        src dst base A root p.1).mp p.2⟩
  invFun q :=
    ⟨(sourceH1EquivLiteralY1Transition src dst q.1.1, q.1.2), by
      apply (sourceLiteralY1Direct_rootA_component_edge_iff
        src dst base A root
        (sourceH1EquivLiteralY1Transition src dst q.1.1, q.1.2)).mpr
      simpa using q.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · simp
    · rfl
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · simp
    · rfl

/-- The true signed rooted original A-component isomorphism. Distinct
positive/negative oriented input tokens remain distinct; no fake
completion edge is allowed. -/
noncomputable def sourceLiteralY1DirectRootComponentGraphHom
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      ((sourceLiteralY1DirectRootComponent src dst base A root).toEGraph).toLabelledGraph
      ((sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).toEGraph).toLabelledGraph where
  onVertex := sourceLiteralY1Direct_rootA_component_vertexEquiv src dst base A root
  onEdge := sourceLiteralY1Direct_rootA_component_edgeEquiv src dst base A root
  map_source := by
    intro e
    apply Subtype.ext
    rfl
  map_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · dsimp [sourceLiteralY1Direct_rootA_component_edgeEquiv]
      change
        (sourceH1EquivLiteralY1Transition src dst).symm
          (e.1.1 *
            PSTS.SignedWord.evalGroupLetter
              (sourceLiteralY1 src dst).transitionSubgroupGenerator e.1.2) =
        (sourceH1EquivLiteralY1Transition src dst).symm e.1.1 *
          PSTS.SignedWord.evalGroupLetter (sourceH1Generator src dst) e.1.2
      rw [map_mul]
      exact congrArg _ (labelledMulEquiv_evalGroupLetter
        (sourceLiteralY1 src dst).transitionSubgroupGenerator
        (sourceH1Generator src dst)
        (sourceH1EquivLiteralY1Transition src dst).symm
        (sourceLiteralY1Generator_to_sourceH1 src dst) e.1.2)
    · rfl
  map_label := by
    intro e
    rfl

/-- The graph comparison is bijective on rooted ACTUAL old
component vertices AND oriented edge tokens. -/
theorem sourceLiteralY1DirectRootComponentGraphHom_bijective
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Bijective
      (sourceLiteralY1DirectRootComponentGraphHom src dst base A root).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectRootComponentGraphHom src dst base A root).onEdge :=
  ⟨(sourceLiteralY1Direct_rootA_component_vertexEquiv src dst base A root).bijective,
    (sourceLiteralY1Direct_rootA_component_edgeEquiv src dst base A root).bijective⟩

/-- Literal original A-root components have identical languages of
REAL chronological signed paths after group/edge transport. -/
theorem sourceLiteralY1DirectRootComponentGraphHom_follows_iff
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u v : (sourceLiteralY1DirectRootComponent src dst base A root).Vertex)
    (w : LabelWord ι) :
    ((sourceLiteralY1DirectRootComponent src dst base A root).toEGraph).Follows
      u w v ↔
    ((sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).toEGraph).Follows
      ((sourceLiteralY1DirectRootComponentGraphHom src dst base A root).onVertex u) w
      ((sourceLiteralY1DirectRootComponentGraphHom src dst base A root).onVertex v) := by
  exact EGraph.follows_iff_bijective
    (sourceLiteralY1DirectRootComponentGraphHom src dst base A root)
    (sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root).1
    (sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root).2 u v w

end ABO
end PSTSEPPA
