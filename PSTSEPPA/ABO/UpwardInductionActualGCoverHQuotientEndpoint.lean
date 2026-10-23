import PSTSEPPA.ABO.UpwardInductionRealCoverFullCosetActualEndpoint
import PSTSEPPA.ABO.Stability

/-!
# Corrected ABO 4.7(iii): G→H quotient FORCES the actual H[B]-augmented stage endpoint

The source's off-skeleton proper B-cluster n>=2 bridge argument
compares two REAL B-paths in a FULL H[B]-coset attached along
the true original component-tagged B-cluster.

The previous exact endpoint theorem shows that an ACTUAL
signed Cayley(G)→completed H-stage morphism F based at the
TRUE embedded coset vertex J(c₁) sends any original
G B-word endpoint g₁*[p]_G to the TRUE stage vertex
J(c₂), as soon as the H-coset coordinates satisfy
c₂.coord=c₁.coord*[p]_H.

Here we discharge that H-coordinate equality itself from
the genuine label-preserving group quotient Q:G→H:
  * g₂ = g₁ * [p]_G is an ACTUAL G group-coordinate equation;
  * c₁.coord = Q(g₁) and c₂.coord = Q(g₂) are the TRUE
    original H ambient values of the TWO specified
    component-tagged old H vertices, not an asserted
    identification of arbitrary old quotient vertices;
  * group-homomorphism naturality of signed chronological
    word evaluation gives Q([p]_G)=[p]_H.

Thus F(g₂)=J(c₂) is a theorem, NOT an extra source
stage-endpoint hypothesis. Every actual source signed
edge orientation and missing-label stationary H-stage loop
is respected by the existing Cayley-graph morphisms.
This holds for NONISOLATED proper clusters as soon as the
correct original H-component is embedded into full H[B]
by the certified source forward Theorem4.5 construction.

The remaining substantive source task is to instantiate
the actual history-selected H augmentation and its
generator-preserving G-stage transition quotient, and
select the correctly matched original H/G rooted anchors.
No global stage→Cayley(H), tag collapse, fake old edge,
new axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ V StageEdge : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]

namespace CompleteEGraph

variable (T : CompleteEGraph V StageEdge ι)

/-- A REAL based Cayley(G)→T signed stage cover,
a genuinely labelled quotient Q:G→H, and the EXACT
original source-coset coordinate equations force the
TRUE mapped original H endpoint in the augmented full
H[B] coset. No free assumption on the target stage
vertex, no quotient tag identification. -/
theorem cayleyGCover_original_H_quotient_forces_B_stage_endpoint
    (genG : ι → Γ) (genH : ι → Δ)
    (Q : LabelledGroupQuotient genG genH)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (B : Finset ι) (gH : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B gH).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (g₁ g₂ : Γ)
    (c₁ c₂ : IsolatedCosetGluing.CosetPoint genH B gH)
    (p : LabelWord ι) (hp : LabelWord.Uses B p)
    (hG : g₂ = g₁ * PSTS.SignedWord.evalGroup genG p)
    (hc₁ : c₁.1 = Q.hom g₁)
    (hc₂ : c₂.1 = Q.hom g₂)
    (hBase : F.onVertex g₁ = J.onVertex c₁) :
    F.onVertex g₂ = J.onVertex c₂ := by
  have hHCoord :
      c₂.1 = c₁.1 * PSTS.SignedWord.evalGroup genH p := by
    calc
      c₂.1 = Q.hom g₂ := hc₂
      _ = Q.hom (g₁ * PSTS.SignedWord.evalGroup genG p) :=
        congrArg Q.hom hG
      _ = Q.hom g₁ *
            Q.hom (PSTS.SignedWord.evalGroup genG p) :=
        Q.hom.map_mul _ _
      _ = c₁.1 * PSTS.SignedWord.evalGroup genH p := by
        rw [Q.map_evalGroup, ←hc₁]
  have hEndpoint :
      F.onVertex (g₁ * PSTS.SignedWord.evalGroup genG p) =
        J.onVertex c₂ :=
    T.cayleyGCover_original_B_word_exactHStageEndpoint
      genG F genH B gH J g₁ c₁ c₂ p hp hBase hHCoord
  exact (congrArg F.onVertex hG).trans hEndpoint

end CompleteEGraph
end ABO
end PSTSEPPA
