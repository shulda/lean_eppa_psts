import PSTSEPPA.ABO.SourceLiteralY1SelectedRootCompletedEGraphIso

/-!
# Exact missing signed B-edge eligibility under genuine labelled graph isomorphisms

Corrected ABO Definition 5.3 type-(2) augments an OLD INCOMPLETE
coset-extension EGraph at an eligible root where no outgoing
OLD B-labelled signed edge exists. Checking the actual edge
predicate matters: the artificial X₁ complete action can contain
edges absent from the original input, and the underlying ambient
group coordinates do not determine which differently tagged
coset-extension vertices should be glued.

A genuine bijective signed labelled EGraph morphism preserves AND
REFLECTS this missing-edge predicate, because it is bijective on
formal oriented EDGE TOKENS, bijective on VERTICES, and preserves
the full signed labels and old edge sources. We certify this generic
fact and apply it to the TRUE printed T(Y₁) selected root A-component
ordinary P_A multi-coset EGraph and the independent SourceH₁ version.

This does not assert that an arbitrary old root satisfies the
predicate. Later the rank-two source/local H₁[A] off-B theorem
supplies eligibility for the ACTUALLY selected type-(2) indices.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V W Edge FEdge ι : Type*}

/-- No ACTUAL signed edge with base label in B leaves the
specified old vertex. This is exactly the old-edge exclusion
required by the deterministic isolated full-B-coset augmentation. -/
def NoSignedBEdgesAt
    (G : EGraph V Edge ι) (B : Finset ι) (u : V) : Prop :=
  ∀ e : Edge, G.source e = u → signedBase (G.label e) ∉ B

/-- A genuine old oriented signed EGraph ISOMORPHISM preserves
AND REFLECTS the absence of outgoing old B-edges at any point.

Crucially surjectivity of the edge-token map is needed to reflect
absence in the target, and vertex injectivity is used to recover
the correct source point of each lifted target edge. -/
theorem noSignedBEdgesAt_iff_of_bijective
    (G : EGraph V Edge ι) (H : EGraph W FEdge ι)
    (f : LabelledGraphHom G.toLabelledGraph H.toLabelledGraph)
    (hv : Function.Bijective f.onVertex)
    (he : Function.Bijective f.onEdge)
    (B : Finset ι) (u : V) :
    G.NoSignedBEdgesAt B u ↔
      H.NoSignedBEdgesAt B (f.onVertex u) := by
  constructor
  · intro hG e heSource
    obtain ⟨d, rfl⟩ := he.2 e
    have hdSource : G.source d = u := by
      apply hv.1
      calc
        f.onVertex (G.source d) = H.source (f.onEdge d) :=
          (f.map_source d).symm
        _ = f.onVertex u := heSource
    have hd := hG d hdSource
    simpa only [f.map_label d] using hd
  · intro hH d hdSource
    have hsource :
        H.source (f.onEdge d) = f.onVertex u := by
      calc
        H.source (f.onEdge d) = f.onVertex (G.source d) :=
          f.map_source d
        _ = f.onVertex u := congrArg f.onVertex hdSource
    have h := hH (f.onEdge d) hsource
    simpa only [f.map_label d] using h

end EGraph

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- ACTUAL selected rank-two plain PRECOMPLETION missing-B-edge
eligibility for the literal paper T(Y₁) original-root coset
extension agrees exactly with the original SourceH₁ A-root
geometry. The result uses the actual completed-Coset EGraph
isomorphism but NO stationary loops, so absent old edges
remain genuinely absent on BOTH sides. -/
theorem sourceLiteralY1SelectedRoot_noSignedBEdgesAt_iff
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) (B : Finset ι)
    (z : Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root P)) :
    (sourceLiteralY1SelectedRootCompletedEGraph
      src dst base A hcard root P).NoSignedBEdgesAt B z ↔
    (sourceH1OriginalRankTwoRootCompletedEGraph
      src dst base A hcard
      ((sourceH1EquivLiteralY1Transition src dst).symm root) P).NoSignedBEdgesAt B
      ((sourceLiteralY1SelectedRootCompletedEGraphHom
        src dst base A hcard root P).onVertex z) := by
  let G := sourceLiteralY1SelectedRootCompletedEGraph src dst base A hcard root P
  let H := sourceH1OriginalRankTwoRootCompletedEGraph
    src dst base A hcard
    ((sourceH1EquivLiteralY1Transition src dst).symm root) P
  let f := sourceLiteralY1SelectedRootCompletedEGraphHom
    src dst base A hcard root P
  have hb := sourceLiteralY1SelectedRootCompletedEGraphHom_bijective
    src dst base A hcard root P
  exact G.noSignedBEdgesAt_iff_of_bijective H f hb.1 hb.2 B z

end ABO
end PSTSEPPA
