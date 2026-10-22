import PSTSEPPA.ABO.UpwardInductionAugmentedFullBCosetWordEquality
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# Actual Cayley(G) cover forces H word equality in an ISOLATED-root attachment

This theorem is a precise cover/path calculation for the legally completed
`IsolatedCosetGluing` stage constructed at an old H-root with NO outgoing
old B-labelled edges (hypothesis `hMissing`). It is valid for the
rank-one/type-(2) isolated full B-coset attachment, including signed inverse
edge tokens and stationary loops on labels outside B.

The source's corrected ABO Theorem 4.7(iii) off-skeleton proper B-cluster
with multiple constituents normally already has genuine old B-edges. Its
augmentation identifies the WHOLE B-component with a full H[B] coset.
This lemma DOES NOT supply that non-isolated cluster augmentation or its
Cayley(G) cover. The parallel genuine canonical Cayley cluster construction
is being developed separately in `UpwardInductionAugmentedClusterBWordEquality`.

Within this isolated-root scope, a genuine labelled Cayley(G)→stage
morphism takes the original G B-word path p into the completed stage.
If a genuine second stage path labelled w₁ ++ inv(w₂) has the same
true endpoint, deterministic signed stage following and the exact
attached B-coset word endpoint lemma yield [p]_H=[w₁ inv(w₂)]_H.

No unsupported Cayley(H) embedding of the WHOLE loop-completed stage,
no fake old signed edges, no collapse of original component tags.
-/
namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

/-- A real G→legally completed ISOLATED-root H B-augmentation
cover and one ACTUAL completed-stage constituent-piece B-path from
its correct glued full-B source to the image of the genuine
G ambient p endpoint yield EXACTLY the group-word equality
used as an ingredient in the proper n≥2 source upward bridge argument,
conditional on obtaining the corresponding genuine general augmentation.

Every signed path is witnessed using genuine positive and
inverse edge tokens; the proof does NOT presuppose
ambient H-embedding of the loop-completed stage. -/
theorem augmentedStage_HWordEquality_of_realGCayleyCover
    (H : EGraph V OldEdge ι)
    (genH : ι → Δ) (B : Finset ι) (gH : Δ) (root : V)
    (hMissing : ∀ e : OldEdge,
      H.source e = root → signedBase (H.label e) ∉ B)
    (hpaired : H.LocallyPairedLabels)
    (p₀ : CosetPoint genH B gH)
    (genG : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      (completedStage H genH B gH root hMissing hpaired).toEGraph.toLabelledGraph)
    (u : Γ)
    (C₁ C₂ : Finset ι)
    (p w₁ w₂ : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hw₁ : LabelWord.Uses (B ∩ C₁) w₁)
    (hw₂ : LabelWord.Uses (B ∩ C₂) w₂)
    (hBase :
      F.onVertex u = gluePoint genH B gH root p₀)
    (hAugmentedPiecePath :
      (completedStage H genH B gH root hMissing hpaired).toEGraph.Follows
        (gluePoint genH B gH root p₀)
        (w₁ ++ PSTS.SignedWord.inv w₂)
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p))) :
    PSTS.SignedWord.evalGroup genH p =
      PSTS.SignedWord.evalGroup genH
        (w₁ ++ PSTS.SignedWord.inv w₂) := by
  let T := completedStage H genH B gH root hMissing hpaired
  have hCayley :
      (cayleyGraph genG).toEGraph.Follows
        u p (u * PSTS.SignedWord.evalGroup genG p) := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using
      (cayleyGraph genG).follows_followWord u p
  have hMapped :
      T.toEGraph.Follows
        (gluePoint genH B gH root p₀) p
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p)) := by
    have h := hCayley.map F
    rw [hBase] at h
    exact h
  have hPEnd :
      T.followWord (gluePoint genH B gH root p₀) p =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord (gluePoint genH B gH root p₀) p)
      hMapped
  have hQEnd :
      T.followWord (gluePoint genH B gH root p₀)
          (w₁ ++ PSTS.SignedWord.inv w₂) =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord
        (gluePoint genH B gH root p₀)
        (w₁ ++ PSTS.SignedWord.inv w₂))
      hAugmentedPiecePath
  have hSameEndpoint :
      T.followWord (gluePoint genH B gH root p₀) p =
      T.followWord (gluePoint genH B gH root p₀)
          (w₁ ++ PSTS.SignedWord.inv w₂) :=
    hPEnd.trans hQEnd.symm
  exact completedStage_properTwoPiece_BWordEquality
    H genH B gH root hMissing hpaired p₀
    C₁ C₂ p w₁ w₂ hp hw₁ hw₂ hSameEndpoint

end IsolatedCosetGluing
end ABO
end PSTSEPPA
