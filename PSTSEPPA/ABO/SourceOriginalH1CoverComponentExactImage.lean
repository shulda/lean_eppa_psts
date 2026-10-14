import PSTSEPPA.ABO.SourceOriginalH1LocalCoverIndex
import PSTSEPPA.ABO.AmbientSkeletonAlphabetRestriction
import PSTSEPPA.ABO.ComponentSubgraphPaths

/-!
# Exact original-input images of genuine H₁ preimage components

The original edge-labelled input graph is an INCOMPLETE signed
EGraph. The first-rank H₁ preimage skeleton has only the inverse
images of those OLD signed edges; it is NOT the complete X₁ graph.

For every actual source cover index j=(base,A,root), its connected
A-component maps onto exactly the original A-component of the
projection of root, on vertices. More strongly, EVERY original
signed A-edge whose source lies in that projected component
has an actual preimage edge in the selected H₁ cover component.

These are literal vertex/edge covering properties: not mere
ambient group-coset coordinate identities, and with no invented
X₁ completion edges, quotient-tag collapses, or representative
choices. They are needed to identify the actual covers selected
in corrected ABO Definition 5.3 with our source-indexed stages.

This does not assert equality of the eventual completed Z₁
catalogues or prove Condition 5.2, Theorem 4.7 or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- EXACT projected vertex image of any original H₁ A-cover
component, including a disconnected original graph and a root
above any input vertex. On the right only REAL input signed
A-paths are used. No ambient X₁-completion path is admitted. -/
theorem sourceCoverIndexComponent_vertex_image_exact
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst)
    (v : V) :
    (∃ x : (sourceCoverIndexComponent src dst j).Vertex,
      sourceH1Orbit src dst j.1 x.1 = v) ↔
    ∃ w : LabelWord ι,
      LabelWord.Uses j.2.1.1 w ∧
      (sourceInputEGraph src dst).Follows
        (sourceH1Orbit src dst j.1 j.2.2) w v := by
  let K := sourceCoverIndexSkeleton src dst j
  let A := j.2.1.1
  let root := sourceCoverIndexRoot src dst j
  let L := K.restrictAlphabet A
  have hcover :=
    sourceH1OriginalSkeleton_subalphabetReachable_iff
      src dst j.1 A root v
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hreachL⟩ := x.2
    have hreachK : K.SubalphabetReachable A root y :=
      (K.restrictAlphabet_subalphabetReachable_iff
        A A (Finset.Subset.rfl) root y).mp hreachL
    have hprojected :
        (sourceH1OriginalSkeletonHom src dst j.1).onVertex y = v := by
      change sourceH1Orbit src dst j.1 y.1 = v
      calc
        sourceH1Orbit src dst j.1 y.1 =
          sourceH1Orbit src dst j.1 x.1 :=
          congrArg (sourceH1Orbit src dst j.1) hy
        _ = v := hx
    exact hcover.mpr ⟨y, hreachK, hprojected⟩
  · intro hpath
    obtain ⟨y, hreachK, hprojected⟩ := hcover.mp hpath
    have hreachL : L.SubalphabetReachable A root y :=
      (K.restrictAlphabet_subalphabetReachable_iff
        A A (Finset.Subset.rfl) root y).mpr hreachK
    refine ⟨L.componentLiftVertex A root y hreachL, ?_⟩
    exact hprojected

/-- Every actual oriented signed A-edge of the ORIGINAL
input graph with source in the projected original A-component
lifts to a genuine directed edge of the selected H₁ cover
component. In particular formal negative edge tokens and
geometric loops are preserved; no added X₁ edges count. -/
theorem sourceCoverIndexComponent_edge_lift_over_original_component
    (src dst : ι → V)
    (j : SourceOriginalH1CoverIndex src dst)
    (s : SignedLabel ι)
    (hA : signedBase s ∈ j.2.1.1)
    (hsource :
      ∃ w : LabelWord ι,
        LabelWord.Uses j.2.1.1 w ∧
        (sourceInputEGraph src dst).Follows
          (sourceH1Orbit src dst j.1 j.2.2) w
          (sourceInputSignedSource src dst s)) :
    ∃ e : (sourceCoverIndexComponent src dst j).Edge,
      e.1.2 = s := by
  let K := sourceCoverIndexSkeleton src dst j
  let A := j.2.1.1
  let root := sourceCoverIndexRoot src dst j
  let L := K.restrictAlphabet A
  obtain ⟨x, hx⟩ :=
    (sourceCoverIndexComponent_vertex_image_exact
      src dst j (sourceInputSignedSource src dst s)).mpr hsource
  obtain ⟨y, hy, hreach⟩ := x.2
  have heK : (x.1, s) ∈ K.edges := by
    change sourceH1Orbit src dst j.1 x.1 =
      sourceInputSignedSource src dst s
    exact hx
  have heL : (x.1, s) ∈ L.edges :=
    ⟨heK, hA⟩
  let e : L.Edge := ⟨(x.1, s), heL⟩
  have hsourceEq : (L.toEGraph).source e = y := by
    apply Subtype.ext
    exact hy.symm
  have hReachSource :
      L.SubalphabetReachable A root ((L.toEGraph).source e) := by
    rw [hsourceEq]
    exact hreach
  refine ⟨L.componentLiftEdge A root e hA hReachSource, ?_⟩
  rfl

end ABO
end PSTSEPPA
