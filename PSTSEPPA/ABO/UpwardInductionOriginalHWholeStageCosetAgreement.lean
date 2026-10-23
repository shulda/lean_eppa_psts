import PSTSEPPA.ABO.UpwardInductionWholeBOldSignedEmbedding
import PSTSEPPA.ABO.UpwardInductionActualGCoverHQuotientEndpoint

/-!
# Corrected ABO upward 4.7(iii): REAL original H inclusion meets its full H[B] coset

The accepted construction of the true NONISOLATED completed B-augmentation
contains TWO separately certified signed labelled maps:
  i : H_old → T, preserving ALL original component-tagged
      old vertices and BOTH oriented signed old edges;
  J : (one ACTUAL full H[B] coset) → T, preserving
      all actual signed full-coset edges and vertices.

Crucially these maps are NOT unrelated: for EVERY old vertex x
of the ONE selected ORIGINAL signed H B-component, i(x)
and J(cHom(x)) are the SAME actual newly completed stage
vertex, because the correct entire-component replacement
carrier identifies that chosen component with its INJECTIVE
canonical full H[B] coset image. On unrelated original old
component tags i retains original tagged left summand.

Here we prove the exact agreement of i and J on the chosen
component. Combining it with the accepted group quotient
G→H source B-word equality and a genuine signed Cayley(G)→T
cover gives the EXACT H-stage image of the true original
second selected B-component anchor automatically.

Thus the old source-facing hypothesis
  i(s₂) = F(g₁*[p]_G)
is no longer an independent arbitrary equality of two
possibly different original quotient tags: it follows
from the TRUE original signed B-component→full coset
morphism, REAL G→H group quotient, precise ORIGINAL
anchor coordinates and an ACTUAL based Cayley(G) cover.

Remaining source task is building the appropriate
history-selected real Cayley(G)→this T group-transition
quotient and source coatom/root matches. No global
embedding of T into Cayley(H), no fake old edge,
no unrelated original tag collapse or new axioms.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V OldEdge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace EGraph

/-- The TRUE signed old-H inclusion i into the actual
nonisolated completed B-stage agrees on every vertex of
the ONE selected ORIGINAL old B-component with its
certified signed component→full H[B] coset inclusion
followed by the real full coset→stage map J.

This is an equality of ACTUAL stage vertices, not
just group coordinates or abstract B-reachability. -/
theorem wholeOriginalBComponentOldSignedHom_agrees_fullCoset
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (genH : ι → Γ) (B : Finset ι) (anchor : V) (gH : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex)
    (x : {v : V // v ∈ G.BComponentVertexSet B anchor}) :
    (G.wholeOriginalBComponentOldSignedHom
      hpaired genH B anchor gH cHom hcInjective).onVertex x.1 =
    (G.fullBCosetToWholeOriginalBComponentStageHom
      hpaired genH B anchor gH cHom.onVertex hcInjective).onVertex
        (cHom.onVertex x) := by
  change
    G.originalVertexToFullBReplacement
      genH B anchor gH cHom.onVertex x.1 =
      Sum.inr (cHom.onVertex x)
  exact G.originalVertexToFullBReplacement_inside
    genH B anchor gH cHom.onVertex x.1 x.2

/-- The exact SECOND ORIGINAL tagged H-component stage
anchor image follows automatically from:
(1) a real signed G Cayley→nonisolated augmented H-stage
cover F based at the first ACTUAL embedded old H point;
(2) the actual labelled group quotient Q:G→H;
(3) the true G signed B-word endpoint equation
g₂=g₁*[p]_G;
(4) the true H full-coset coordinate equations for the
TWO already named genuine ORIGINAL old H-component points.

In particular no extra target equality hCoverEnd, globally
injective original H coset-extension ambient projection,
or isolated-root no-old-B-edge assumption occurs. -/
theorem wholeOriginalBComponent_oldTarget_of_realGCover_and_HQuotient
    (genG : ι → Δ) (genH : ι → Γ)
    (Q : LabelledGroupQuotient genG genH)
    (G : EGraph V OldEdge ι)
    (hpaired : G.LocallyPairedLabels)
    (B : Finset ι) (anchor : V) (gH : Γ)
    (cHom : LabelledGraphHom
      (G.BComponentEGraph B anchor).toLabelledGraph
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph)
    (hcInjective : Function.Injective cHom.onVertex)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      (G.wholeOriginalBComponentAugmentedStage
        hpaired genH B anchor gH cHom.onVertex hcInjective).toEGraph.toLabelledGraph)
    (g₁ g₂ : Δ)
    (s₁ s₂ : {v : V // v ∈ G.BComponentVertexSet B anchor})
    (p : LabelWord ι) (hp : LabelWord.Uses B p)
    (hG : g₂ = g₁ * PSTS.SignedWord.evalGroup genG p)
    (hH₁ : (cHom.onVertex s₁).1 = Q.hom g₁)
    (hH₂ : (cHom.onVertex s₂).1 = Q.hom g₂)
    (hBase :
      F.onVertex g₁ =
        (G.wholeOriginalBComponentOldSignedHom
          hpaired genH B anchor gH cHom hcInjective).onVertex s₁.1) :
    F.onVertex g₂ =
      (G.wholeOriginalBComponentOldSignedHom
        hpaired genH B anchor gH cHom hcInjective).onVertex s₂.1 := by
  let T := G.wholeOriginalBComponentAugmentedStage
    hpaired genH B anchor gH cHom.onVertex hcInjective
  let J := G.fullBCosetToWholeOriginalBComponentStageHom
    hpaired genH B anchor gH cHom.onVertex hcInjective
  let i := G.wholeOriginalBComponentOldSignedHom
    hpaired genH B anchor gH cHom hcInjective
  have hMeet₁ : i.onVertex s₁.1 = J.onVertex (cHom.onVertex s₁) :=
    G.wholeOriginalBComponentOldSignedHom_agrees_fullCoset
      hpaired genH B anchor gH cHom hcInjective s₁
  have hMeet₂ : i.onVertex s₂.1 = J.onVertex (cHom.onVertex s₂) :=
    G.wholeOriginalBComponentOldSignedHom_agrees_fullCoset
      hpaired genH B anchor gH cHom hcInjective s₂
  have hBased : F.onVertex g₁ = J.onVertex (cHom.onVertex s₁) :=
    hBase.trans hMeet₁
  have hExact : F.onVertex g₂ = J.onVertex (cHom.onVertex s₂) :=
    T.cayleyGCover_original_H_quotient_forces_B_stage_endpoint
      genG genH Q F B gH J g₁ g₂
      (cHom.onVertex s₁) (cHom.onVertex s₂)
      p hp hG hH₁ hH₂ hBased
  exact hExact.trans hMeet₂.symm

end EGraph
end ABO
end PSTSEPPA
