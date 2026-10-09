import PSTSEPPA.ABO.GraphHomInjectivity
import PSTSEPPA.ABO.MultiCosetMorphisms
import PSTSEPPA.ABO.CosetConnectivity

/-!
# The actual bridge-freeness condition for tagged coset extensions

ABO Definition 4.1 has two distinct requirements for the *full*
coset extension: its canonical map to the ambient Cayley graph is an
embedding, and any two of its vertices connected by a B-word in the
ambient Cayley graph (B⊊A) are connected by a genuine B-word in
the coset extension itself.

We state the same property for any selected coset family P. This
makes it possible to transfer bridge freeness across the checked
coatom-only/full-proper graph isomorphism, and supplies an explicit
*inductive hypothesis* for the forward step. Crucially, this property
is NOT automatic from admissibility and is not assumed as an axiom.

In our EGraph model, injectivity on vertices of the ambient map
already implies injectivity on directed signed edge tokens: the source
EGraph is deterministic. Thus it suffices to include vertex injection
as the embedding clause.

The ambient Cayley graph here is the Cayley graph of Γ; applications
where K⊆G[A] are obtained by restricting this interface to that
subgroup. The historical forward-induction theorem additionally
requires bridge freeness and cluster property of every lower-rank
component extension; neither is hidden in the definition below.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Explicit bridge-freeness interface modelled on ABO Definition 4.1:
the canonical tagged-CE morphism is vertex-injective, and every
proper-B ambient coset connection between CE points is realised
by a B-labelled path INSIDE that CE. No global injectivity claim
is being made unless this property is separately established. -/
def MultiCosetBridgeFree
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  Function.Injective
    (K.multiCosetAmbientHom P hadm hgen hret).onVertex ∧
  ∀ (B : Finset ι), B ⊂ A →
    ∀ (u v : K.MultiCosetVertex P hadm hgen hret),
      K.multiCosetAmbientValue P hadm hgen hret v ∈
        generatedLeftCoset gen B
          (K.multiCosetAmbientValue P hadm hgen hret u) →
      ∃ w : LabelWord ι,
        LabelWord.Uses B w ∧
        (K.multiCosetEGraph P hadm hgen hret).Follows u w v

/-- The actual canonical CE→Cayley graph morphism is injective on
both vertices AND signed directed edges under the first clause
of bridge freeness, by deterministic source-labelled edges. -/
theorem multiCosetBridgeFree_ambient_graph_embedding
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hBridge : K.MultiCosetBridgeFree P hadm hgen hret) :
    Function.Injective
      (K.multiCosetAmbientHom P hadm hgen hret).onVertex ∧
    Function.Injective
      (K.multiCosetAmbientHom P hadm hgen hret).onEdge := by
  exact
    (K.multiCosetAmbientHom P hadm hgen hret).bijective_on_image_of_vertex_injective
      hBridge.1

/-- Under bridge freeness, *intrinsic* B-connectivity in the
extension is equivalent to ambient B-coset connectivity, for
every B⊊A. In the forward direction the actual CE-path
maps to the ambient Cayley graph; the converse is precisely
the independent bridge-freeness assumption. -/
theorem multiCosetBridgeFree_reachable_iff_ambient_coset
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hBridge : K.MultiCosetBridgeFree P hadm hgen hret)
    (B : Finset ι) (hBA : B ⊂ A)
    (u v : K.MultiCosetVertex P hadm hgen hret) :
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph P hadm hgen hret).Follows u w v) ↔
    K.multiCosetAmbientValue P hadm hgen hret v ∈
      generatedLeftCoset gen B
        (K.multiCosetAmbientValue P hadm hgen hret u) := by
  let H := K.multiCosetAmbientHom P hadm hgen hret
  constructor
  · rintro ⟨w, hw, hpath⟩
    have hmapped :
        (cayleyGraph gen).toEGraph.Follows
          (H.onVertex u) w (H.onVertex v) :=
      hpath.map H
    have hcanonical :
        (cayleyGraph gen).toEGraph.Follows
          (H.onVertex u) w
          ((cayleyGraph gen).followWord (H.onVertex u) w) :=
      (cayleyGraph gen).follows_followWord (H.onVertex u) w
    have hvalue :
        (cayleyGraph gen).followWord (H.onVertex u) w =
          H.onVertex v :=
      (cayleyGraph gen).toEGraph.follows_right_unique
        hcanonical hmapped
    exact
      (mem_generatedLeftCoset_iff_subalphabetReachable
        gen B (H.onVertex u) (H.onVertex v)).mpr
        ⟨w, hw, hvalue⟩
  · intro hAmbient
    exact hBridge.2 B hBA u v hAmbient

end CayleySubgraphSpec
end ABO
end PSTSEPPA
