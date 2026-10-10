import PSTSEPPA.ABO.RankTwoCompletedComponentShape
import PSTSEPPA.ABO.SingleCosetConnectivity
import PSTSEPPA.ABO.TrivialLoopCompletion

/-!
# Corrected ABO Proposition 5.4: no unwanted singleton-word action at rank two

The independently audited k=1 repair R2 observes that a singleton
generator word cannot acquire a new nontrivial action in the rank-two
completed full coset extensions. We certify a stronger version:

For the genuine canonical COMPLETED full coset extension of a rank-two
Cayley skeleton (|A|=2), for ANY selected proper subalphabet B⊂A
and any signed B-word w, if its value in the ambient generating group
is identity, following w fixes EVERY VERTEX of the complete extension.

Proof:
* The rank-two exact component classification and loop-completion
  invariance classify each B-component as a full tagged B-coset or
  an isolated singleton.
* In a full B-coset, the actual word-path lemma gives an endpoint
  with identical component index and coordinate
      p.value * evalGroup(gen,w) = p.value.
  The selected tagged coset coordinate is injective at fixed index,
  so the endpoint is LITERALLY the original tagged vertex.
  Map this genuine path through the multi-CE and trivial-completion
  inclusions. Determinism forces the complete-stage endpoint to agree.
* For a singleton component, every actual completed B-path is
  stationary, including the path followed by w.

This is a substantial concrete word-kernel result at the k=1 R2
base for unaugmented rank-two full extensions. It is NOT yet a
proof that the full assembled G₂→H₁ is 1-stable, since the augmented
cluster objects in Z₁ and the finite disjoint-stage quotient maps
still need their analogous witness analysis and construction.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- An identity-valued B-word fixes EVERY vertex of the actual
rank-two trivially completed full proper-alphabet coset extension.
This is a statement about the COMPLETE action, not just old
skeleton points or group-valued abstract words. -/
theorem rankTwo_completedStage_identity_B_word_fixes
    (hcard : A.card = 2)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (w : LabelWord ι)
    (hw : LabelWord.Uses B w)
    (hval : PSTS.SignedWord.evalGroup gen w = 1)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      (K.admissible_of_card_le_two hcard.le) hgen hret) :
    (K.allProperCompletedStage
        (K.admissible_of_card_le_two hcard.le)
        hgen hret hcard.ge).followWord z w = z := by
  let hadm : K.AdmissibleForCosetExtension :=
    K.admissible_of_card_le_two hcard.le
  let P := allProperCosetFamily A
  let hweak : K.MultiCosetWeaklyComplete P hadm hgen hret :=
    allProperCosetFamily_weaklyComplete K hadm hgen hret hcard.ge
  let CE := K.multiCosetEGraph P hadm hgen hret
  let paired : CE.LocallyPairedLabels :=
    K.multiCoset_locallyPairedLabels_of_weakComplete
      P hadm hgen hret hweak
  let T := K.allProperCompletedStage hadm hgen hret hcard.ge
  rcases K.rankTwo_completedStage_B_component_full_or_singleton
      hcard hgen hret B hBP z with
    ⟨p, hz, _⟩ | hSingleton
  · obtain ⟨q, hPathB, hidx, hvalue⟩ :=
      K.singleCosetEGraph_follows_word B p hw
    have hvalueEq : q.2.1 = p.2.1 := by
      simpa [hval] using hvalue
    have hpq : q = p :=
      K.attachedValue_injective_of_same_index B hidx hvalueEq
    let f := K.singleCosetToMultiHom P hadm hgen hret B hBP
    have hCE : CE.Follows
        (K.multiCosetInclude P hadm hgen hret B hBP p) w
        (K.multiCosetInclude P hadm hgen hret B hBP p) := by
      have h := hPathB.map f
      change CE.Follows
        (K.multiCosetInclude P hadm hgen hret B hBP p) w
        (K.multiCosetInclude P hadm hgen hret B hBP q) at h
      rw [hpq] at h
      exact h
    have hT : T.toEGraph.Follows
        (K.multiCosetInclude P hadm hgen hret B hBP p) w
        (K.multiCosetInclude P hadm hgen hret B hBP p) := by
      have h := hCE.map (CE.trivialLoopCompletionHom paired)
      exact h
    rw [hz]
    exact T.toEGraph.follows_right_unique
      (T.follows_followWord
        (K.multiCosetInclude P hadm hgen hret B hBP p) w) hT
  · have hPath : T.toEGraph.Follows z w (T.followWord z w) :=
      T.follows_followWord z w
    exact hSingleton (T.followWord z w) ⟨w, hw, hPath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
