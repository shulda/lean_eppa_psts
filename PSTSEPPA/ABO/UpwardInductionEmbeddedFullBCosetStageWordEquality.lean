import PSTSEPPA.ABO.IsolatedCosetGluing
import PSTSEPPA.ABO.CayleySubgraphFullCosetPaths
import PSTSEPPA.ABO.CayleyStageProjection

/-!
# Exact signed B-word arithmetic from a REAL EMBEDDED full H[B] coset in ANY stage

The general corrected ABO Theorem 4.7(iii) proper B-cluster
augmentation is NOT an isolated-root gluing: old B-edges
already exist, and the entire old intrinsic component is
identified with part of a newly full H[B] coset.

Fortunately, the group-word comparison does not need
the whole LEGALLY completed H-stage to embed in Cayley(H).
That would in general be false due to stationary outside-B
loops. Instead it needs ONLY one actual labelled graph
embedding of the literal full H[B] coset into the completed
stage, injective on coset vertices.

For any real full-B coset embedding J into any complete
signed deterministic EGraph T:
* every B-supported chronological signed word w from
  J(p) ends EXACTLY at J(q), with q.1=p.1*[w]_H;
* if two such B-words have the SAME ACTUAL T endpoint,
  their evaluations [w]_H are equal;
* if a real Cayley(G)->T morphism maps an ambient
  G word p into that same endpoint as an independently
  real B-piece path q from J(p0), then [p]_H=[q]_H.

These statements retain genuine positive/inverse oriented
edge tokens, require NO no-old-B-edge condition, NO stage
to-Cayley(H) morphism, and NEVER identify distinct
old-component tags by ambient H coordinates. Construction
of the original history-selected full-component B-gluing,
including this injective J and the Cayley(G) cover, remains
the precise separate source-geometric obligation.
-/

namespace PSTSEPPA
namespace ABO

variable {V Edge ι Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Δ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- A genuine full H[B] coset embedded in an arbitrary complete
signed stage has exactly the same B-word endpoints as the
actual full Cayley(H) coset. The stage may have unrelated
old vertices, old B-edges, and stationary outside-B loops. -/
theorem embeddedFullBCoset_B_followWord_exact
    (genH : ι → Δ) (B : Finset ι) (g : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B g).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (p : IsolatedCosetGluing.CosetPoint genH B g)
    (w : LabelWord ι) (hw : LabelWord.Uses B w) :
    ∃ q : IsolatedCosetGluing.CosetPoint genH B g,
      T.followWord (J.onVertex p) w = J.onVertex q ∧
      q.1 = p.1 * PSTS.SignedWord.evalGroup genH w := by
  let K := IsolatedCosetGluing.fullCosetSubgraph genH B g
  obtain ⟨q, hRealPath, hValue⟩ :=
    K.follows_word_in_fullCoset B g
      (by intro e he; exact he)
      p p.2 w hw
  have hStagePath :
      T.toEGraph.Follows (J.onVertex p) w (J.onVertex q) :=
    hRealPath.map J
  have hEnd :
      T.followWord (J.onVertex p) w = J.onVertex q :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord (J.onVertex p) w) hStagePath
  exact ⟨q, hEnd, hValue⟩

/-- The B-word equality detector in an ARBITRARY completed
stage with a real injectively embedded full H[B] coset.
No requirements on old B-edges of the stage or on
outside-B stationary loops. -/
theorem embeddedFullBCoset_B_sameEndpoint_evalGroup_eq
    (genH : ι → Δ) (B : Finset ι) (g : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B g).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hInjective : Function.Injective J.onVertex)
    (p : IsolatedCosetGluing.CosetPoint genH B g)
    (w₁ w₂ : LabelWord ι)
    (hw₁ : LabelWord.Uses B w₁)
    (hw₂ : LabelWord.Uses B w₂)
    (hSameEndpoint :
      T.followWord (J.onVertex p) w₁ =
      T.followWord (J.onVertex p) w₂) :
    PSTS.SignedWord.evalGroup genH w₁ =
      PSTS.SignedWord.evalGroup genH w₂ := by
  obtain ⟨q₁, hEnd₁, hVal₁⟩ :=
    T.embeddedFullBCoset_B_followWord_exact genH B g
      J p w₁ hw₁
  obtain ⟨q₂, hEnd₂, hVal₂⟩ :=
    T.embeddedFullBCoset_B_followWord_exact genH B g
      J p w₂ hw₂
  have hImage : J.onVertex q₁ = J.onVertex q₂ :=
    hEnd₁.symm.trans (hSameEndpoint.trans hEnd₂)
  have hPoint : q₁ = q₂ := hInjective hImage
  have hMul :
      p.1 * PSTS.SignedWord.evalGroup genH w₁ =
        p.1 * PSTS.SignedWord.evalGroup genH w₂ := by
    calc
      p.1 * PSTS.SignedWord.evalGroup genH w₁ = q₁.1 := hVal₁.symm
      _ = q₂.1 := congrArg Subtype.val hPoint
      _ = p.1 * PSTS.SignedWord.evalGroup genH w₂ := hVal₂
  exact mul_left_cancel hMul

/-- The SOURCE-FAITHFUL abstract augmented-stage bridge:
from a REAL Cayley(G) cover of an arbitrary legally completed
H-stage, and a vertex-INJECTIVE genuine full H[B]-coset
embedding into that stage, the original G B-word p and a
real second stage B-word q with identical endpoints have
EQUAL H evaluations. There need be old B-edges at the core. -/
theorem embeddedFullBCoset_HWordEquality_of_realGCayleyCover
    {Γ : Type*} [Group Γ]
    (genH : ι → Δ) (B : Finset ι) (g : Δ)
    (J : LabelledGraphHom
      ((IsolatedCosetGluing.fullCosetSubgraph genH B g).toEGraph).toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (hInjective : Function.Injective J.onVertex)
    (genG : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph genG).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (u : Γ)
    (p₀ : IsolatedCosetGluing.CosetPoint genH B g)
    (p q : LabelWord ι)
    (hp : LabelWord.Uses B p)
    (hq : LabelWord.Uses B q)
    (hBase : F.onVertex u = J.onVertex p₀)
    (hSecondPath :
      T.toEGraph.Follows (J.onVertex p₀) q
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p))) :
    PSTS.SignedWord.evalGroup genH p =
      PSTS.SignedWord.evalGroup genH q := by
  have hGCayley :
      (cayleyGraph genG).toEGraph.Follows u p
        (u * PSTS.SignedWord.evalGroup genG p) := by
    simpa only [cayleyGraph.followWord_eq_mul_evalGroup] using
      (cayleyGraph genG).follows_followWord u p
  have hMapped :
      T.toEGraph.Follows (J.onVertex p₀) p
        (F.onVertex (u * PSTS.SignedWord.evalGroup genG p)) := by
    have h := hGCayley.map F
    rw [hBase] at h
    exact h
  have hPEnd :
      T.followWord (J.onVertex p₀) p =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord (J.onVertex p₀) p) hMapped
  have hQEnd :
      T.followWord (J.onVertex p₀) q =
        F.onVertex (u * PSTS.SignedWord.evalGroup genG p) :=
    T.toEGraph.follows_right_unique
      (T.follows_followWord (J.onVertex p₀) q) hSecondPath
  exact T.embeddedFullBCoset_B_sameEndpoint_evalGroup_eq
    genH B g J hInjective p₀ p q hp hq
    (hPEnd.trans hQEnd.symm)

end CompleteEGraph
end ABO
end PSTSEPPA
