import PSTSEPPA.ABO.AugmentedClusterTrivialStage
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths

/-!
# The singleton-word kernel is preserved by actual augmented cluster stages

Corrected ABO Proposition 5.4 needs a k=1 stability base for the
finite stage family Z₁. The family includes AUGMENTED clusters
(type (1)), not just completed full coset extensions.

For ANY augmented cluster (at arbitrary ambient rank), any
positive generator i and any vertex x, one of two things happens:

* x belongs to a full coset constituent on an alphabet containing
  i, and ALL signed i-edges of that coset lie in the augmented
  skeleton; hence a {i}-supported word is followed by genuine old
  edges and has its literal ambient group-value endpoint;
* x has NO outgoing old edge of either sign labelled i.
  The trivial loop completion fixes x for all i-steps.

Therefore EVERY {i}-supported word w with ambient group value
[ w ]_Γ = 1 acts as the IDENTITY PERMUTATION on the actual
complete augmented-cluster stage.

This goes beyond a mere component classification: it proves the
exact word-kernel test needed by the independently audited k=1
repair R2, for Definition 5.3's type-(1) augmented clusters.
It does NOT yet construct the finite union X₂, analyze type-(2)
augmented full coset extensions, or prove the final
1-stable quotient G₂ -> H₁.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace ClusterSpec

variable {A : Finset ι}
variable (P : ClusterSpec A)

/-- Every vertex of an augmented cluster is either inside a
literal FULL i-containing coset constituent or has NO original
i-labelled outgoing edge. This uses genuine old edge data
and covers both the original cluster and its attached B-coset. -/
theorem augmented_singleton_fullCoset_or_missing
    (D : Finset ι) (hDA : D ⊆ A) (v : Γ)
    (x : (P.augmentedCayleySubgraph gen D hDA v).Vertex)
    (i : ι) :
    (∃ (C : Finset ι) (g : Γ),
      x.1 ∈ generatedLeftCoset gen C g ∧
      i ∈ C ∧
      (∀ f : ActionEdge Γ ι,
        f ∈ FullCosetEdgeSet gen C g →
        f ∈ (P.augmentedCayleySubgraph gen D hDA v).edges)) ∨
    (¬ ∃ e : (P.augmentedCayleySubgraph gen D hDA v).Edge,
      ((P.augmentedCayleySubgraph gen D hDA v).toEGraph).source e = x ∧
      signedBase
        (((P.augmentedCayleySubgraph gen D hDA v).toEGraph).label e) = i) := by
  let K := P.augmentedCayleySubgraph gen D hDA v
  by_cases he :
      ∃ e : K.Edge,
        (K.toEGraph).source e = x ∧
        signedBase ((K.toEGraph).label e) = i
  · obtain ⟨e, hSource, hLabel⟩ := he
    have hSrc : e.1.1 = x.1 :=
      congrArg Subtype.val hSource
    have hBase : signedBase e.1.2 = i := hLabel
    rcases e.2 with hCluster | hAdded
    · obtain ⟨C, hCP, hOldSrc, hOldLabel⟩ := hCluster
      have hxC : x.1 ∈ generatedSubgroup gen C := hSrc ▸ hOldSrc
      have hiC : i ∈ C := by
        change signedBase e.1.2 ∈ C at hOldLabel
        rw [hBase] at hOldLabel
        exact hOldLabel
      left
      refine ⟨C, 1, ?_, hiC, ?_⟩
      · simpa [generatedLeftCoset_one] using hxC
      · intro f hf
        have hfC :
            f.1 ∈ generatedSubgroup gen C := by
          change (cayleyGraph gen).source f ∈ generatedSubgroup gen C
          simpa only [generatedLeftCoset_one] using hf.1
        exact Or.inl ⟨C, hCP, hfC, hf.2⟩
    · have hxD : x.1 ∈ generatedLeftCoset gen D v :=
        hSrc ▸ hAdded.1
      have hiD : i ∈ D := by
        have hAddedLabel : signedBase e.1.2 ∈ D := hAdded.2
        rw [hBase] at hAddedLabel
        exact hAddedLabel
      left
      refine ⟨D, v, hxD, hiD, ?_⟩
      intro f hf
      exact Or.inr hf
  · exact Or.inr he

/-- The k=1 **word-kernel** condition for every genuine
trivially completed augmented cluster: an identity-valued
singleton-supported word fixes every completed vertex.
No global Cayley-map injection or higher-rank cluster
property is needed. -/
theorem augmentedTrivialStage_singleton_identity_word_fixes
    (D : Finset ι) (hDA : D ⊆ A) (v : Γ)
    (i : ι) (w : LabelWord ι)
    (hw : LabelWord.Uses ({i} : Finset ι) w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (x : (P.augmentedCayleySubgraph gen D hDA v).Vertex) :
    (P.augmentedTrivialStage D hDA v).followWord x w = x := by
  let K := P.augmentedCayleySubgraph gen D hDA v
  let paired : K.toEGraph.LocallyPairedLabels :=
    P.augmentedCayleySubgraph_locallyPairedLabels D hDA v
  let T := P.augmentedTrivialStage (gen := gen) D hDA v
  rcases P.augmented_singleton_fullCoset_or_missing D hDA v x i with
    ⟨C, g, hxC, hiC, hfull⟩ | hMissing
  · have hsub : ({i} : Finset ι) ⊆ C :=
      Finset.singleton_subset_iff.mpr hiC
    have hwC : LabelWord.Uses C w := hw.mono hsub
    obtain ⟨y, hOldPath, hvalue⟩ :=
      K.follows_word_in_fullCoset C g hfull x hxC w hwC
    have hxy : y = x := by
      apply Subtype.ext
      simpa [hval] using hvalue
    have hCompleted := hOldPath.map
      (K.toEGraph.trivialLoopCompletionHom paired)
    have hT : T.toEGraph.Follows x w x := by
      change T.toEGraph.Follows x w y at hCompleted
      rw [hxy] at hCompleted
      exact hCompleted
    exact T.toEGraph.follows_right_unique
      (T.follows_followWord x w) hT
  · have hNo (s : SignedLabel ι)
        (hs : signedBase s = i) :
        ¬ ∃ e : K.Edge,
          K.toEGraph.source e = x ∧
          K.toEGraph.label e = s := by
      rintro ⟨e, hsource, hlabel⟩
      apply hMissing
      refine ⟨e, hsource, ?_⟩
      rw [hlabel]
      exact hs
    have hfix :
        ∀ t : LabelWord ι,
          LabelWord.Uses ({i} : Finset ι) t →
          T.followWord x t = x := by
      intro t
      induction t with
      | nil =>
          intro _
          rfl
      | cons s t ih =>
          intro ht
          have hs : signedBase s = i :=
            Finset.mem_singleton.mp ht.1
          have hedge : T.edgeAt x s = (x, s) := by
            change (actionGraph
              (K.toEGraph.loopCompletedPermutation paired)).edgeAt x s = (x, s)
            exact actionGraph.edgeAt _ x s
          have hloop : T.target (x, s) = x :=
            K.toEGraph.trivialLoopCompletion_loop_of_missing
              paired x s (hNo s hs)
          rw [T.followWord_cons, hedge, hloop]
          exact ih ht.2
    exact hfix w hw

end ClusterSpec
end ABO
end PSTSEPPA
