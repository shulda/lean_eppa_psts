import PSTSEPPA.ABO.SourceG2AugmentedStageWordKernel
import PSTSEPPA.ABO.AugmentedClusterLocalCompletedActionIso
import PSTSEPPA.ABO.DependentDisjointWordCongruence
import PSTSEPPA.ABO.Type1OriginalLocalStageIndexEquiv
import PSTSEPPA.ABO.CompleteStageWordKernelTransport

/-!
# Actual source H₁ type-(1) augmented clusters inherit the genuine finite G₂ word action

The actual input-dependent finite G₂ already covers every local
rank-two type-(1) completed augmented cluster over the generated
subgroup H₁[A]. The entire ORIGINAL ambient H₁ augmented cluster
lives in H₁[A], and its true completed signed action is isomorphic
to the local one. The real G₂ word-action congruence consequently
holds on ALL original old and newly attached ambient H₁ vertices.

The statement is for a genuine anchored proper cluster P with
proper D⊂A. No ambient-coordinate quotient, arbitrary representative,
artificial edge completion or dependence on a hypothetical finite
group is used. It is exactly the type-(1) action half of the
source-specific corrected Definition-5.3 Z₁-to-G₂ bridge.

The full Z₁ catalogue also includes type-(2) stages and plain
stages, and corrected Condition 5.2 and higher rank remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- If two chronological signed words represent the same element
of the CONCRETE finite G₂ built from the original source edge
input, then they have equal actions at EVERY ORIGINAL ambient
H₁ type-(1) augmented-cluster vertex. The original cluster
may have any finite family P of proper A-subalphabets; every
proper D⊂A is supported, with both signs and legal fixed loops. -/
theorem sourceG2OriginalType1_wordValue_congr
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (P : ClusterSpec A)
    (D : {D : Finset ι // D ⊂ A})
    (v : generatedSubgroup (sourceH1Generator src dst) A)
    (hv : v ∈ P.VertexSet
      (trivialCompletionGenerator (sourceH1Generator src dst) A))
    (p q : LabelWord ι)
    (hpq : PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) p =
      PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) q) :
    ∀ y : (P.augmentedCayleySubgraph
      (sourceH1Generator src dst)
      D.1 D.2.subset (v : SourceH1 src dst)).Vertex,
      (P.augmentedTrivialStage
        (gen := sourceH1Generator src dst)
        D.1 D.2.subset (v : SourceH1 src dst)).followWord y p =
      (P.augmentedTrivialStage
        (gen := sourceH1Generator src dst)
        D.1 D.2.subset (v : SourceH1 src dst)).followWord y q := by
  let gen := sourceH1Generator src dst
  let genLocal := trivialCompletionGenerator gen A
  let j : ClusterSpec.augmentedType1Index genLocal A :=
    ⟨P, D, ⟨v, hv⟩⟩
  let G := P.augmentedTrivialStage
    (gen := genLocal) D.1 D.2.subset v
  let H := P.augmentedTrivialStage
    (gen := gen) D.1 D.2.subset (v : SourceH1 src dst)
  let f := P.localAugmentedCompletedStageHom
    gen D.1 D.2.subset v
  have hLocal (x : (P.augmentedCayleySubgraph
      genLocal D.1 D.2.subset v).Vertex) :
      G.followWord x p = G.followWord x q := by
    have hTagged :
        (ClusterSpec.augmentedType1FamilyStage genLocal A).followWord
          (⟨j, x⟩ : Σ k : ClusterSpec.augmentedType1Index genLocal A,
            ClusterSpec.augmentedType1Vertex k) p =
        (ClusterSpec.augmentedType1FamilyStage genLocal A).followWord
          (⟨j, x⟩ : Σ k : ClusterSpec.augmentedType1Index genLocal A,
            ClusterSpec.augmentedType1Vertex k) q :=
      sourceG2Type1Catalogue_wordValue_congr
        src dst A hcard ⟨j, x⟩ p q hpq
    exact (dependentDisjointStage_wordEquality_at_tag_iff
      (fun k : ClusterSpec.augmentedType1Index genLocal A =>
        ClusterSpec.augmentedType1Stage k) j x p q).mp hTagged
  have hf : Function.Surjective f.onVertex :=
    (P.localAugmentedCompletedStageHom_bijective
      gen D.1 D.2.subset v).1.2
  exact G.wordActionCongr_of_surjectiveHom
    H f hf p q hLocal

end ABO
end PSTSEPPA
