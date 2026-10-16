import PSTSEPPA.ABO.KStablePullbackIntrinsicBComponents
import PSTSEPPA.ABO.KStablePullbackAdmissibility

/-!
# Genuine intrinsic B-component graph isomorphisms across stable pullback covers

For Q : G ↠ H stable on B, let K be any actual INCOMPLETE
H-Cayley skeleton, L := Q⁻¹(K) its literal old-edge G-pullback,
and x an actual L-vertex.

The restriction of the labelled pullback graph covering
    F : L → K
to the entire genuine intrinsic B-path component of x is a
BIJECTION onto the intrinsic B-path component of F(x), not
merely a surjection of group coordinates or a bijection of
ambient B-cosets.

We prove both:
  * equivalence of the actual OLD B-component VERTEX subtypes;
  * equivalence of all old formally ORIENTED B-edge tokens whose
    sources are in these components.

The vertex proof lifts a true downstairs B-path from x,
and uses stability injectivity within the UNIQUE gG[B] coset
to rule out two upstairs endpoints with the same image.
The oriented edge proof uses the already certified unique
signed edge lift at each prescribed source and the preceding
component vertex bijection. Loop and inverse tokens are
never identified, and missing old edges are never completed.

This is precisely the component-tag fidelity necessary before
trying the corrected ABO Theorem 4.7 mixed-support full
multi-coset embedding argument. It does NOT assert that the
canonical ambient map on the whole glued multiCE is injective;
separate components with equal H ambient coordinates may exist.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- The genuine signed OLD intrinsic B-component of the
G-pullback is exactly isomorphic as a vertex type to the
genuine intrinsic B-component of its chosen H-root.
This is stronger than the previously established
relative reachability iff, but still faithfully retains
the original chosen component root and its coset tag. -/
noncomputable def pullbackQuotient_intrinsicBComponentEquiv
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (x : (K.pullbackQuotient Q).Vertex) :
    {y : (K.pullbackQuotient Q).Vertex //
      (K.pullbackQuotient Q).SubalphabetReachable B x y} ≃
    {z : K.Vertex //
      K.SubalphabetReachable B
        ((K.pullbackQuotientHom Q).onVertex x) z} := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  let φ :
      {y : L.Vertex // L.SubalphabetReachable B x y} →
        {z : K.Vertex // K.SubalphabetReachable B (F.onVertex x) z} :=
    fun y =>
      ⟨F.onVertex y.1, by
        obtain ⟨w, hw, hp⟩ := y.2
        exact ⟨w, hw, hp.map F⟩⟩
  apply Equiv.ofBijective φ
  constructor
  · intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    have hQ :
        Q.hom y.1.1 = Q.hom z.1.1 :=
      congrArg
        (fun t : {v : K.Vertex // K.SubalphabetReachable B (F.onVertex x) v} =>
          t.1.1) hyz
    exact Q.injective_on_generatedLeftCoset_of_stableAt
      B hB x.1
      (L.subalphabetReachable_implies_coset B x y.1 y.2)
      (L.subalphabetReachable_implies_coset B x z.1 z.2)
      hQ
  · intro z
    obtain ⟨w, hw, hp⟩ := z.2
    obtain ⟨y, hyPath, hyMap⟩ :=
      K.pullbackQuotientHom_follows_lift Q hp x rfl
    refine ⟨⟨y, ⟨w, hw, hyPath⟩⟩, ?_⟩
    apply Subtype.ext
    exact hyMap

/-- The exact actual vertex coordinate of the
component isomorphism is the OLD quotient graph map. -/
@[simp] theorem pullbackQuotient_intrinsicBComponentEquiv_val
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (x : (K.pullbackQuotient Q).Vertex)
    (y : {y : (K.pullbackQuotient Q).Vertex //
      (K.pullbackQuotient Q).SubalphabetReachable B x y}) :
    (K.pullbackQuotient_intrinsicBComponentEquiv Q B hB x y).1 =
      (K.pullbackQuotientHom Q).onVertex y.1 :=
  rfl

/-- The true directed OLD signed B-edge tokens of one
intrinsic B-component. This retains exactly the
actual source-reachable edges with B-labels, NOT
the (possibly larger) ambient B-Cayley coset edges. -/
def IntrinsicBEdgeAt
    (K : CayleySubgraphSpec genΔ A)
    (B : Finset ι) (root : K.Vertex) :=
  {e : K.Edge //
    K.SubalphabetReachable B root (K.toEGraph.source e) ∧
      signedBase (K.toEGraph.label e) ∈ B}

/-- The OLD B-labelled edge image of the actual
G-pullback B-component, retaining all directed signed
edge tokens of loops and nontrivial transitions. -/
noncomputable def pullbackQuotient_intrinsicBComponentEdgeMap
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (x : (K.pullbackQuotient Q).Vertex) :
    (K.pullbackQuotient Q).IntrinsicBEdgeAt B x →
      K.IntrinsicBEdgeAt B ((K.pullbackQuotientHom Q).onVertex x) :=
  fun e =>
    ⟨(K.pullbackQuotientHom Q).onEdge e.1, by
      constructor
      · have hMapped :
          K.SubalphabetReachable B
            ((K.pullbackQuotientHom Q).onVertex x)
            ((K.pullbackQuotientHom Q).onVertex
              ((K.pullbackQuotient Q).toEGraph.source e.1)) := by
            obtain ⟨w, hw, hp⟩ := e.2.1
            exact ⟨w, hw, hp.map (K.pullbackQuotientHom Q)⟩
        rw [(K.pullbackQuotientHom Q).map_source e.1]
        exact hMapped
      · rw [(K.pullbackQuotientHom Q).map_label e.1]
        exact e.2.2⟩

/-- Equality of OLD signed B-edges in H reflects to
equality of the ORIGINAL edge tokens in the specified
G-component, by genuine source injectivity in ONE
translated B-coset and deterministic signed edges. -/
theorem pullbackQuotient_intrinsicBComponentEdgeMap_injective
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (x : (K.pullbackQuotient Q).Vertex) :
    Function.Injective
      (K.pullbackQuotient_intrinsicBComponentEdgeMap Q B x) := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  intro e f hef
  have hDownEdge : F.onEdge e.1 = F.onEdge f.1 :=
    congrArg Subtype.val hef
  have hDownSource :
      F.onVertex (L.toEGraph.source e.1) =
        F.onVertex (L.toEGraph.source f.1) := by
    calc
      F.onVertex (L.toEGraph.source e.1) =
          K.toEGraph.source (F.onEdge e.1) :=
        (F.map_source e.1).symm
      _ = K.toEGraph.source (F.onEdge f.1) :=
        congrArg K.toEGraph.source hDownEdge
      _ = F.onVertex (L.toEGraph.source f.1) :=
        F.map_source f.1
  have hSrcCoord : (L.toEGraph.source e.1).1 =
      (L.toEGraph.source f.1).1 :=
    Q.injective_on_generatedLeftCoset_of_stableAt
      B hB x.1
      (L.subalphabetReachable_implies_coset
        B x (L.toEGraph.source e.1) e.2.1)
      (L.subalphabetReachable_implies_coset
        B x (L.toEGraph.source f.1) f.2.1)
      (congrArg (fun z : K.Vertex => z.1) hDownSource)
  have hSrc :
      L.toEGraph.source e.1 = L.toEGraph.source f.1 :=
    Subtype.ext hSrcCoord
  have hLabel : L.toEGraph.label e.1 = L.toEGraph.label f.1 := by
    calc
      L.toEGraph.label e.1 = K.toEGraph.label (F.onEdge e.1) :=
        (F.map_label e.1).symm
      _ = K.toEGraph.label (F.onEdge f.1) :=
        congrArg K.toEGraph.label hDownEdge
      _ = L.toEGraph.label f.1 := F.map_label f.1
  apply Subtype.ext
  exact L.toEGraph.deterministic hSrc hLabel

/-- The vertex component equivalence supplies a UNIQUE
upstairs source for every genuine OLD B-edge of the
target B-component. The already certified old edge
lift supplies precisely the original signed edge. -/
theorem pullbackQuotient_intrinsicBComponentEdgeMap_surjective
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (x : (K.pullbackQuotient Q).Vertex) :
    Function.Surjective
      (K.pullbackQuotient_intrinsicBComponentEdgeMap Q B x) := by
  let L := K.pullbackQuotient Q
  let F := K.pullbackQuotientHom Q
  intro e
  let yH : K.Vertex := K.toEGraph.source e.1
  obtain ⟨y, hyMap⟩ :=
    (K.pullbackQuotient_intrinsicBComponentEquiv Q B hB x).surjective
      (⟨yH, e.2.1⟩ :
        {z : K.Vertex // K.SubalphabetReachable B (F.onVertex x) z})
  have hySource :
      F.onVertex y.1 = K.toEGraph.source e.1 :=
    congrArg Subtype.val hyMap
  obtain ⟨f, hfSource, hfMap⟩ :=
    K.pullbackQuotientHom_edge_lift Q e.1 y.1 hySource
  have hfReach : L.SubalphabetReachable B x (L.toEGraph.source f) := by
    rw [hfSource]
    exact y.2
  have hfBase : signedBase (L.toEGraph.label f) ∈ B := by
    rw [← F.map_label f, hfMap]
    exact e.2.2
  refine ⟨⟨f, ⟨hfReach, hfBase⟩⟩, ?_⟩
  apply Subtype.ext
  exact hfMap

/-- Actual bijection between all genuinely EXISTING
oriented signed B-edge tokens of the chosen intrinsic
G and H components. It does not assume either
component is an entire ambient B-coset. -/
noncomputable def pullbackQuotient_intrinsicBComponentEdgeEquiv
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (x : (K.pullbackQuotient Q).Vertex) :
    (K.pullbackQuotient Q).IntrinsicBEdgeAt B x ≃
      K.IntrinsicBEdgeAt B ((K.pullbackQuotientHom Q).onVertex x) :=
  Equiv.ofBijective
    (K.pullbackQuotient_intrinsicBComponentEdgeMap Q B x)
    ⟨K.pullbackQuotient_intrinsicBComponentEdgeMap_injective Q B hB x,
     K.pullbackQuotient_intrinsicBComponentEdgeMap_surjective Q B hB x⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
