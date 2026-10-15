import PSTSEPPA.ABO.SourceLiteralY1MultiCosetRawGluingTransport
import PSTSEPPA.ABO.AmbientSkeletonAlphabetRestriction
import PSTSEPPA.ABO.ComponentSubgraph

/-!
# Rooted original A-component vertex equivalence for printed T(Y₁)

The original incomplete signed covers of the literal paper transition
group T(Y₁) and the source model H₁ are already signed-graph isomorphic,
with an exact generator-preserving group coordinate isomorphism.
We now restrict their ACTUAL old oriented edges to an arbitrary alphabet A,
then take the intrinsic REAL A-connected component of a specified
group root.

The resulting rooted component vertex types are equivalent, with
the map on coordinates exactly the actual T(Y₁)→SourceH₁ group isomorphism.
Membership is checked by genuinely realised old A-paths, not by
membership in a potentially larger ambient group A-coset.

This is the first stage in comparing selected Definition-5.3 root
A-components as complete coset extensions. A signed edge isomorphism,
glued completed quotient transport, augmentations and PSTS EPPA
remain separate gates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- An arbitrary group vertex lies in the literal original A-component
of a chosen old-cover root iff its actual image under the labelled
group isomorphism lies in the corresponding SourceH₁ A-component.
Uses only true ORIGINAL signed A-paths, including formal inverses. -/
theorem sourceLiteralY1Direct_rootA_component_vertex_iff
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root x : (sourceLiteralY1 src dst).transitionGroup) :
    x ∈
      (((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A)
        .subalphabetComponentSubgraph A
          (⟨root, by trivial⟩ :
            ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)).vertices
      ↔
    (sourceH1EquivLiteralY1Transition src dst).symm x ∈
      (((sourceH1OriginalSkeleton src dst base).restrictAlphabet A)
        .subalphabetComponentSubgraph A
          (⟨(sourceH1EquivLiteralY1Transition src dst).symm root, by trivial⟩ :
            ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)).vertices := by
  let L := sourceLiteralY1DirectOriginalSkeleton src dst base
  let K := sourceH1OriginalSkeleton src dst base
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  let f := sourceLiteralY1DirectToSourceH1OriginalHom src dst base
  let rL : L.Vertex := ⟨root, by trivial⟩
  let xL : L.Vertex := ⟨x, by trivial⟩
  let rK : K.Vertex := ⟨E root, by trivial⟩
  let xK : K.Vertex := ⟨E x, by trivial⟩
  have hroot : f.onVertex rL = rK := by
    apply Subtype.ext
    exact (sourceLiteralY1DirectToSourceH1_coordinate src dst base rL).symm
  have hxmap : f.onVertex xL = xK := by
    apply Subtype.ext
    exact (sourceLiteralY1DirectToSourceH1_coordinate src dst base xL).symm
  have hreach :
      L.SubalphabetReachable A rL xL ↔
      K.SubalphabetReachable A rK xK := by
    have h := sourceLiteralY1DirectToSourceH1_A_reachable_iff
      src dst base A rL xL
    rw [hroot, hxmap] at h
    exact h
  have hL :
      x ∈ (L.restrictAlphabet A).subalphabetComponentSubgraph A
            (rL : (L.restrictAlphabet A).Vertex) |>.vertices ↔
      (L.restrictAlphabet A).SubalphabetReachable A rL xL := by
    constructor
    · rintro ⟨u, hu, hr⟩
      have hueq : u = (xL : (L.restrictAlphabet A).Vertex) :=
        Subtype.ext hu
      simpa only [hueq] using hr
    · intro hr
      exact ⟨xL, rfl, hr⟩
  have hK :
      E x ∈ (K.restrictAlphabet A).subalphabetComponentSubgraph A
            (rK : (K.restrictAlphabet A).Vertex) |>.vertices ↔
      (K.restrictAlphabet A).SubalphabetReachable A rK xK := by
    constructor
    · rintro ⟨u, hu, hr⟩
      have hueq : u = (xK : (K.restrictAlphabet A).Vertex) :=
        Subtype.ext hu
      simpa only [hueq] using hr
    · intro hr
      exact ⟨xK, rfl, hr⟩
  change
    x ∈ (L.restrictAlphabet A).subalphabetComponentSubgraph A rL |>.vertices ↔
      E x ∈ (K.restrictAlphabet A).subalphabetComponentSubgraph A rK |>.vertices
  exact hL.trans
    ((L.restrictAlphabet_subalphabetReachable_iff A A (subset_rfl) rL xL).trans
      (hreach.trans
        ((K.restrictAlphabet_subalphabetReachable_iff A A (subset_rfl) rK xK).symm.trans hK.symm)))

/-- The full chosen-root ACTUAL original A-component VERTEX CARRIERS
are bijective. The result is uniform in the original input, alphabet,
base vertex and actual group root, with no choice of coset reps. -/
noncomputable def sourceLiteralY1Direct_rootA_component_vertexEquiv
    (src dst : ι → V) (base : V) (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A)
      .subalphabetComponentSubgraph A
        (⟨root, by trivial⟩ :
          ((sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A).Vertex)).Vertex
      ≃
    (((sourceH1OriginalSkeleton src dst base).restrictAlphabet A)
      .subalphabetComponentSubgraph A
        (⟨(sourceH1EquivLiteralY1Transition src dst).symm root, by trivial⟩ :
          ((sourceH1OriginalSkeleton src dst base).restrictAlphabet A).Vertex)).Vertex where
  toFun p :=
    ⟨(sourceH1EquivLiteralY1Transition src dst).symm p.1,
      (sourceLiteralY1Direct_rootA_component_vertex_iff src dst base A root p.1).mp p.2⟩
  invFun p :=
    ⟨(sourceH1EquivLiteralY1Transition src dst) p.1, by
      apply (sourceLiteralY1Direct_rootA_component_vertex_iff src dst base A root
        ((sourceH1EquivLiteralY1Transition src dst) p.1)).mpr
      simpa only [MulEquiv.symm_apply_apply] using p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact (sourceH1EquivLiteralY1Transition src dst).apply_symm_apply p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact (sourceH1EquivLiteralY1Transition src dst).symm_apply_apply p.1

end ABO
end PSTSEPPA
