import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso
import PSTSEPPA.ABO.BijectiveLabelledEGraphPaths
import PSTSEPPA.ABO.ForwardInductionArbitraryRankRootedCompletedEGraphIso

/-!
# True signed B-component EGraph isomorphisms under bijective transport

The source cluster property refers to entire ACTUAL signed B-component
graphs, including both oriented edge tokens, not only ambient group
vertex sets. A bijective labelled EGraph morphism of incomplete
signed graphs must restrict to an actual B-component graph
isomorphism, for EVERY selected subalphabet B, including
signed inverse letters, loops and genuinely missing old edges.

We prove a reusable GENERIC restriction construction and
bijectivity. It uses real signed path preservation/reflection,
not reachability in a completed ambient Cayley graph.
Then apply it to the independently certified arbitrary-rank
rooted local H[C] / original Γ multiCE signed EGraph isomorphism.

This supplies a literal labelled graph isomorphism of the
whole corresponding TRUE B-components on original/new
vertices AND directed signed edge classes, even if Γ is
only k-retractable instead of globally retractable.
It will be used to transfer the proper B-cluster SHAPE clause
of source Definition 3.22, alongside component-tag support
minima and off-skeleton equivalence.

No quotient by equal ambient Γ values, artificial signed
old edge, new axiom, or sorry.
-/

namespace PSTSEPPA
namespace ABO
namespace EGraph

variable {V E W F ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable (G : EGraph V E ι) (H : EGraph W F ι)
variable (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
/-- The actual B-component membership of a vertex is reflected
by the bijective labelled signed graph morphism. -/
theorem BComponentVertex_mem_iff_bijective
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (anchor v : V) :
    v ∈ G.BComponentVertexSet B anchor ↔
      f.onVertex v ∈ H.BComponentVertexSet B (f.onVertex anchor) :=
  G.subalphabet_paths_iff_of_bijective_labelledHom
    H f hv he B anchor v

/-- Membership of the complete ORIGINAL oriented signed B-edge
token set is reflected, not merely source or label equality. -/
theorem BComponentEdge_mem_iff_bijective
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (anchor : V) (e : E) :
    e ∈ G.BComponentEdgeSet B anchor ↔
      f.onEdge e ∈ H.BComponentEdgeSet B (f.onVertex anchor) := by
  constructor
  · rintro ⟨hl, hs⟩
    constructor
    · rw [f.map_label e]
      exact hl
    · rw [f.map_source e]
      exact (G.BComponentVertex_mem_iff_bijective
        H f hv he B anchor (G.source e)).mp hs
  · rintro ⟨hl, hs⟩
    constructor
    · rw [f.map_label e] at hl
      exact hl
    · rw [f.map_source e] at hs
      exact (G.BComponentVertex_mem_iff_bijective
        H f hv he B anchor (G.source e)).mpr hs

/-- Restriction of a genuine globally bijective signed EGraph
morphism to the TRUE B-component is a genuine labelled graph
morphism of exactly the ORIGINAL B-component EGraphs. -/
noncomputable def BComponentHomOfBijective
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (anchor : V) :
    LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      (H.BComponentEGraph B (f.onVertex anchor)).toLabelledGraph where
  onVertex v :=
    ⟨f.onVertex v.1,
      (G.BComponentVertex_mem_iff_bijective
        H f hv he B anchor v.1).mp v.2⟩
  onEdge e :=
    ⟨f.onEdge e.1,
      (G.BComponentEdge_mem_iff_bijective
        H f hv he B anchor e.1).mp e.2⟩
  map_source e := by
    apply Subtype.ext
    exact f.map_source e.1
  map_inv e := by
    apply Subtype.ext
    exact f.map_inv e.1
  map_label e := f.map_label e.1

/-- The true restricted morphism is BIJECTIVE on the entire
B-component vertex set AND on every actual oriented signed
B-edge token. No global completeness or Cayley coset shortcut. -/
theorem BComponentHomOfBijective_bijective
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (anchor : V) :
    Function.Bijective
      (G.BComponentHomOfBijective H f hv he B anchor).onVertex ∧
    Function.Bijective
      (G.BComponentHomOfBijective H f hv he B anchor).onEdge := by
  constructor
  · constructor
    · intro u v huv
      apply Subtype.ext
      exact hv.1 (congrArg Subtype.val huv)
    · intro y
      obtain ⟨x, hx⟩ := hv.2 y.1
      refine ⟨⟨x, ?_⟩, ?_⟩
      · apply (G.BComponentVertex_mem_iff_bijective
          H f hv he B anchor x).mpr
        rw [hx]
        exact y.2
      · apply Subtype.ext
        exact hx
  · constructor
    · intro u v huv
      apply Subtype.ext
      exact he.1 (congrArg Subtype.val huv)
    · intro y
      obtain ⟨x, hx⟩ := he.2 y.1
      refine ⟨⟨x, ?_⟩, ?_⟩
      · apply (G.BComponentEdge_mem_iff_bijective
          H f hv he B anchor x).mpr
        rw [hx]
        exact y.2
      · apply Subtype.ext
        exact hx

end EGraph

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The actual rooted local H[C] and original Γ source
multiCE entire REAL signed B-component EGraphs are
isomorphic: explicit labelled morphism bijective on
whole component vertices and BOTH oriented signed edge
classes. Original Γ need not be globally retractable. -/
theorem arbitraryRankRootedSignedBComponentIso_bijective
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (B : Finset ι)
    (u : (K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret) :
    Function.Bijective
      ((K.arbitraryRankRootedLocalCompletedEGraph C root P hadm hgen hret)
        .BComponentHomOfBijective
        (K.arbitraryRankRootedOriginalCompletedEGraph C root P hadm hgen hret)
        (K.arbitraryRankRootedCompletedEGraphHom C root P hadm hgen hret)
        (K.arbitraryRankRootedCompletedEGraphHom_bijective
          C root P hadm hgen hret).1
        (K.arbitraryRankRootedCompletedEGraphHom_bijective
          C root P hadm hgen hret).2
        B u).onVertex ∧
    Function.Bijective
      ((K.arbitraryRankRootedLocalCompletedEGraph C root P hadm hgen hret)
        .BComponentHomOfBijective
        (K.arbitraryRankRootedOriginalCompletedEGraph C root P hadm hgen hret)
        (K.arbitraryRankRootedCompletedEGraphHom C root P hadm hgen hret)
        (K.arbitraryRankRootedCompletedEGraphHom_bijective
          C root P hadm hgen hret).1
        (K.arbitraryRankRootedCompletedEGraphHom_bijective
          C root P hadm hgen hret).2
        B u).onEdge :=
  (K.arbitraryRankRootedLocalCompletedEGraph C root P hadm hgen hret)
    .BComponentHomOfBijective_bijective
      (K.arbitraryRankRootedOriginalCompletedEGraph C root P hadm hgen hret)
      (K.arbitraryRankRootedCompletedEGraphHom C root P hadm hgen hret)
      (K.arbitraryRankRootedCompletedEGraphHom_bijective
        C root P hadm hgen hret).1
      (K.arbitraryRankRootedCompletedEGraphHom_bijective
        C root P hadm hgen hret).2 B u

end CayleySubgraphSpec
end ABO
end PSTSEPPA
