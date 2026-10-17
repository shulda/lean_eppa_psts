import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedAmbientEmbedding
import PSTSEPPA.ABO.RankTwoComponentBase
import PSTSEPPA.ABO.MultiCosetSelectedSubalphabetComponents
import PSTSEPPA.ABO.BridgeFreenessInterface
import PSTSEPPA.ABO.CayleySubgraphAdmissibility

/-!
# The remaining genuine rank-two B-bridges after ROOTED ambient embeddedness

The source first-rank signed G[A] P_A construction is now proven
embedded on the FULL old+fresh attached region of ONE genuine original
old A-component. This says nothing by itself about *ambient B-bridges*.

Here we isolate the exact additional rank-two obligation, without
silently claiming the entire disconnected G[A]-pullback is embedded
or replacing component tags by ambient coordinates.

1. Any labelled map out of a DETERMINISTIC E-graph that is injective
   on a SELECTED vertex region is also injective on every actual
   formally oriented signed edge whose source is in that region.
   Apply this to the TRUE first-rank rooted G[A] attached region.

2. Under rooted ambient vertex injectivity, no EXTERNAL bridge
   can exist for the empty alphabet: its ambient cosets are
   singletons, hence the two selected tagged quotient vertices
   themselves are equal.

3. A positive-length proper-B path inside one FULL B-constituent
   is always available between points with the same INTRINSIC
   B-component tag. This holds even without rooted embeddedness.

4. At rank |A| <= 2, the exact remaining proper-B bridge-reflection
   problem ON A SELECTED ROOTED REGION is EQUIVALENT to the purely
   tagged geometric ALIGNMENT condition: if two selected vertices
   lie in the same ambient B-coset, then they are equal, OR they
   have representations in the SAME completed B-tagged constituent
   with the SAME intrinsic B-component index. This equivalence
   uses the verified rank-two full-coset-or-isolated-singleton
   classification, and DOES NOT assume the alignment condition.

Consequently the first-rank EXTERNAL B-bridge-reflection problem
is reduced to TAG ALIGNMENT for each nonempty singleton B among
the chosen old-root attached points. This is distinct from
the paper's separate repair R8 for the full-B-coset alternative
inside the cluster analysis of corrected 4.7(iii).
Neither ambient embeddedness nor rank-two admissibility
automatically supplies external B-tag alignment.

No statement of unconditional full bridge freeness, corrected
4.7(iii), Condition 5.2 or PSTS EPPA is asserted.
-/

namespace PSTSEPPA
namespace ABO

namespace LabelledGraphHom

variable {V E W F ι : Type*}
variable {G : EGraph V E ι} {H : LabelledGraph W F ι}

/-- Vertex injectivity ONLY on S forces signed oriented EDGE
injectivity on those genuine old/fresh edges whose source lies in S.
The source graph is deterministic; no hypothesis on vertices
outside S, or on edge targets, is needed. -/
theorem edge_injOn_of_vertex_injOn
    (f : LabelledGraphHom G.toLabelledGraph H)
    (S : Set V)
    (hv : Set.InjOn f.onVertex S) :
    Set.InjOn f.onEdge {e : E | G.source e ∈ S} := by
  intro e he e' he' hed
  apply G.deterministic
  · apply hv he he'
    calc
      f.onVertex (G.source e) = H.source (f.onEdge e) :=
        (f.map_source e).symm
      _ = H.source (f.onEdge e') := by rw [hed]
      _ = f.onVertex (G.source e') := f.map_source e'
  · calc
      G.label e = H.label (f.onEdge e) :=
        (f.map_label e).symm
      _ = H.label (f.onEdge e') := by rw [hed]
      _ = G.label e' := f.map_label e'

end LabelledGraphHom

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- EXACT selected oriented signed edges of one old A-component's
FULL attached region: the old/fresh source is selected.
No arbitrary unseen G-pullback components are included. -/
def rootedMultiCosetEdgeRegion
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex) :
    Set (K.MultiCosetEdgeVertexIncidenceQuotient
      P hadm hgen hret) :=
  {e | (K.multiCosetEGraph P hadm hgen hret).source e ∈
    K.rootedMultiCosetImage P hadm hgen hret root}

/-- The source's true selected OLD A-component ambient embedding
automatically embeds ALL ACTUAL ORIENTED signed edges in the
selected full old/fresh attached coset region as well. -/
theorem rootedMultiCosetAmbient_edge_injOn_of_vertex_injOn
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (hv : Set.InjOn
      (K.multiCosetAmbientValue P hadm hgen hret)
      (K.rootedMultiCosetImage P hadm hgen hret root)) :
    Set.InjOn
      (K.multiCosetAmbientHom P hadm hgen hret).onEdge
      (K.rootedMultiCosetEdgeRegion P hadm hgen hret root) :=
  (K.multiCosetAmbientHom P hadm hgen hret).edge_injOn_of_vertex_injOn
      (K.rootedMultiCosetImage P hadm hgen hret root) hv

/-- With rooted ambient injectivity, the empty alphabet creates
NO external bridge between any two points of that selected
component-tagged old/fresh region. An empty path suffices.
This does not address either singleton in a rank-two A. -/
theorem rootedMultiCoset_no_empty_bridges_of_vertex_injOn
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex)
    (hInj : Set.InjOn
      (K.multiCosetAmbientValue P hadm hgen hret)
      (K.rootedMultiCosetImage P hadm hgen hret root))
    (u v : K.MultiCosetVertex P hadm hgen hret)
    (hu : u ∈ K.rootedMultiCosetImage P hadm hgen hret root)
    (hv : v ∈ K.rootedMultiCosetImage P hadm hgen hret root)
    (hCoset :
      K.multiCosetAmbientValue P hadm hgen hret v ∈
        generatedLeftCoset gen (∅ : Finset ι)
          (K.multiCosetAmbientValue P hadm hgen hret u)) :
    ∃ w : LabelWord ι,
      LabelWord.Uses (∅ : Finset ι) w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows u w v := by
  have hValues :
      K.multiCosetAmbientValue P hadm hgen hret v =
        K.multiCosetAmbientValue P hadm hgen hret u := by
    simpa only [generatedLeftCoset_empty_eq_singleton, Set.mem_singleton_iff]
      using hCoset
  have huv : u = v := hInj hu hv hValues.symm
  subst v
  exact ⟨[], by simp, EGraph.Follows.nil _⟩

/-- The true rank-two rooted region reflects all proper-B
ambient connections precisely if they are actual B-paths in
the original signed multi-coset extension. This is a RELATIVE
bridge condition, not the full source Definition 4.1. -/
def RootedProperBridgeReflection
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex) : Prop :=
  ∀ (B : Finset ι), B ⊂ A →
    ∀ (u v : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret),
      u ∈ K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root →
      v ∈ K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root →
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret v ∈
        generatedLeftCoset gen B
          (K.multiCosetAmbientValue (allProperCosetFamily A)
            hadm hgen hret u) →
      ∃ w : LabelWord ι, LabelWord.Uses B w ∧
        (K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).Follows u w v

/-- The exact EXTERNAL-B-TAG alignment condition on the selected
old-root attached region. When ambient B-cosets of u and v
intersect, they must be equal vertices OR the two vertices
must lie in the very SAME intrinsically indexed attached
FULL B-coset copy. The same ambient group coordinate
alone never establishes this. -/
def RootedProperBridgeTagAlignment
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (root : K.Vertex) : Prop :=
  ∀ (B : Finset ι) (hBA : B ⊂ A),
    ∀ (u v : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret),
      u ∈ K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root →
      v ∈ K.rootedMultiCosetImage (allProperCosetFamily A)
        hadm hgen hret root →
      K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret v ∈
        generatedLeftCoset gen B
          (K.multiCosetAmbientValue (allProperCosetFamily A)
            hadm hgen hret u) →
      u = v ∨
        ∃ (p q : K.AttachedCosetVertex B),
          p.1 = q.1 ∧
          u = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret B
            ((mem_allProperCosetFamily A B).mpr hBA) p ∧
          v = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret B
            ((mem_allProperCosetFamily A B).mpr hBA) q

/-- Sharp rank-two reduction: relative bridge reflection is
EQUIVALENT to true component-tag alignment of external B-coset
pairs. The implication from paths uses the independently
certified full-B-coset-or-isolated-singleton dichotomy.
The reverse implication follows REAL signed B-paths inside
one tagged complete B-copy. No hypothesis asserts that
the needed alignment has already been proved. -/
theorem rootedProperBridgeReflection_iff_tagAlignment
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card ≤ 2)
    (root : K.Vertex) :
    K.RootedProperBridgeReflection hadm hgen hret root ↔
      K.RootedProperBridgeTagAlignment hadm hgen hret root := by
  constructor
  · intro hreflect B hBA u v hu hv hCoset
    let P := allProperCosetFamily A
    have hBP : B ∈ P.alphabets :=
      (mem_allProperCosetFamily A B).mpr hBA
    obtain ⟨w, hw, hpath⟩ :=
      hreflect B hBA u v hu hv hCoset
    rcases K.rank_two_B_component_full_or_singleton
        hadm hgen hret hcard B hBP u with hfull | hisolated
    · rcases hfull with ⟨p, hpu, hexact⟩
      obtain ⟨q, hqp, hvq⟩ :=
        (hexact v).mp ⟨w, hw, hpath⟩
      exact Or.inr ⟨p, q, hqp.symm, hpu, hvq⟩
    · have hEq : v = u := hisolated v ⟨w, hw, hpath⟩
      exact Or.inl hEq.symm
  · intro halign B hBA u v hu hv hCoset
    let P := allProperCosetFamily A
    have hBP : B ∈ P.alphabets :=
      (mem_allProperCosetFamily A B).mpr hBA
    rcases halign B hBA u v hu hv hCoset with heq | ⟨p, q, hpq, hpu, hvq⟩
    · subst v
      exact ⟨[], by simp, EGraph.Follows.nil _⟩
    · have hpath :
          ∃ w : LabelWord ι, LabelWord.Uses B w ∧
            (K.multiCosetEGraph P hadm hgen hret).Follows
              (K.multiCosetInclude P hadm hgen hret B hBP p)
              w
              (K.multiCosetInclude P hadm hgen hret B hBP q) :=
        (K.multiCoset_selected_B_component_exact
          P hadm hgen hret B hBP p
          (K.multiCosetInclude P hadm hgen hret B hBP q)).mpr
          ⟨q, hpq.symm, rfl⟩
      simpa only [hpu, hvq] using hpath

end CayleySubgraphSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The FIRST genuine printed-source rank-two old-component
embeddedness already proved on main also embeds every formal
SIGNED edge whose source is in this whole attached root region.
No claim is made about unrelated original A-components. -/
theorem sourceLiteralY1SelectedLocal_rootedMultiCoset_edge_injOn
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Set.InjOn
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientHom
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)).onEdge
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetEdgeRegion
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root)) := by
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  exact K.rootedMultiCosetAmbient_edge_injOn_of_vertex_injOn
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    (sourceLiteralY1SelectedLocalGOld_identity
      src dst base A root)
    (sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn
      src dst base A hcard root)

/-- The selected ORIGINAL first-rank local G[A] component's
full old+fresh attached region has NO empty-alphabet ambient
bridges. It is a concrete source theorem deduced from
its actually certified unconditional rooted embedding. -/
theorem sourceLiteralY1SelectedLocal_rootedMultiCoset_no_empty_bridges
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (u v : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le))
    (hu : u ∈
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetImage
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root))
    (hv : v ∈
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetImage
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root))
    (hCoset :
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) v ∈
      generatedLeftCoset
        (trivialCompletionGenerator
          (sourceLiteralY1X2AllGenerator src dst) A)
        ∅
        ((sourceLiteralY1SelectedLocalGOldPullback
          src dst base A root).multiCosetAmbientValue
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le) u)) :
    ∃ w : LabelWord ι, LabelWord.Uses (∅ : Finset ι) w ∧
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetEGraph
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)).Follows u w v := by
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  exact K.rootedMultiCoset_no_empty_bridges_of_vertex_injOn
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    (sourceLiteralY1SelectedLocalGOld_identity
      src dst base A root)
    (sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn
      src dst base A hcard root)
    u v hu hv hCoset

/-- SOURCE-EXACT REFORMULATION OF THE REMAINING first-rank G-external
B-bridge reflection obligation: reflection of the selected
genuine old G[A]-component region is equivalent to true
same-component-index B-tagged coset alignment on every external
proper-B ambient pair. In this concrete case, the only still
unsettled nonempty B have |B|=1. It does NOT prove alignment. -/
theorem sourceLiteralY1SelectedLocal_rootedProperBridgeReflection_iff_tagAlignment
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperBridgeReflection
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) ↔
    (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).RootedProperBridgeTagAlignment
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
        (sourceLiteralY1SelectedLocalGOld_identity
          src dst base A root) := by
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  exact K.rootedProperBridgeReflection_iff_tagAlignment
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    hcard.le
    (sourceLiteralY1SelectedLocalGOld_identity
      src dst base A root)

end ABO
end PSTSEPPA
