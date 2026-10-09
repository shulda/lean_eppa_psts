import PSTSEPPA.ABO.RetractableGroupContent
import PSTSEPPA.ABO.CayleyEdgeRetraction
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Corrected ABO Corollary 5.7: endpoint-preserving path-content descent

This module isolates the FINITE DESCENT from the actual corrected ABO
Lemma 5.6. The deep input (the endpoint-preserving geometric path
replacement following one redundant generator deletion) is a named
predicate; it is NOT proved by retractability alone.

For any E-graph K, finite edge-generator alphabet E, and E-generated
retractable group G, if K has the actual one-generator path
replacement property, every realised path u -> v can be replaced
by a path with the same endpoints, the SAME final G-value, and
positive edge-generator support EXACTLY equal to the canonical
group content of its G-value.

A short proof chooses a minimum-support path among all paths with
those two endpoints and that G-value. If it uses an edge outside
canonical content, retractability says deleting that edge from its
word preserves group value. The geometric replacement hypothesis
then gives an actual path with strictly smaller support, a
contradiction. Conversely group-content minimality gives the
other inclusion.

In particular empty group content forces the two endpoints to be
equal. No assertion of the finite reflection group or the missing
corrected ABO Section 4/5 construction is made here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The *geometric* part of the corrected ABO Lemma 5.6, phrased
without silently identifying raw signed edge words with real paths.

Whenever a path word can have all occurrences of one signed edge
generator deleted without changing its G-value, there is a REAL
replacement path between the SAME endpoints, with the same G-value
and support included in the original support minus that generator.

This is an explicit hard proof obligation and is NOT inferred
from Retractable gen or a bare word deletion. -/
def EndpointPreservingSingleEdgeDeletion
    (K : EGraph V Edge ι) (gen : ι → Γ) : Prop :=
  ∀ (u v : V) (w : LabelWord ι),
    K.Follows u w v →
    ∀ (a : ι), a ∈ LabelWord.positiveSupport w →
      PSTS.SignedWord.evalGroup gen (LabelWord.eraseGenerator a w) =
        PSTS.SignedWord.evalGroup gen w →
      ∃ q : LabelWord ι,
        K.Follows u q v ∧
        PSTS.SignedWord.evalGroup gen q =
          PSTS.SignedWord.evalGroup gen w ∧
        LabelWord.positiveSupport q ⊆
          (LabelWord.positiveSupport w).erase a

namespace RetractableGroupContent

/-- If a generator is outside the canonical content of g,
erasing its positive AND inverse letters from any word of
G-value g preserves the exact G-value.

The proof uses source retractability against the genuinely
minimal-content representative; no path interpretation is used. -/
theorem eraseGenerator_value_of_not_mem_content
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen)
    (g : Γ) (w : LabelWord ι)
    (hw : PSTS.SignedWord.evalGroup gen w = g)
    (a : ι) (ha : a ∉ content gen hgen g) :
    PSTS.SignedWord.evalGroup gen
        (LabelWord.eraseGenerator a w) = g := by
  let t := leastWord gen hgen g
  have ht : PSTS.SignedWord.evalGroup gen t = g :=
    (leastWord_spec gen hgen g).1
  have htAvoid : ∀ s ∈ t, signedBase s ≠ a := by
    intro s hs hsa
    apply ha
    have hMem : signedBase s ∈ LabelWord.positiveSupport t := by
      simp only [LabelWord.positiveSupport, List.mem_toFinset]
      exact List.mem_map.mpr ⟨s, hs, rfl⟩
    change a ∈ LabelWord.positiveSupport t
    simpa [hsa] using hMem
  have hErase :
      LabelWord.eraseGenerator a t = t :=
    LabelWord.eraseGenerator_eq_self_of_all_base_ne a t htAvoid
  have hEq :
      PSTS.SignedWord.evalGroup gen w =
        PSTS.SignedWord.evalGroup gen t :=
    hw.trans ht.symm
  have hRet := hret a w t hEq
  rw [hErase] at hRet
  exact hRet.trans ht

end RetractableGroupContent

/-- Corrected ABO Corollary 5.7 from a *separately established*
endpoint-preserving single-edge path replacement theorem.

The returned word is an actual K-path from u to v; its group
value is unchanged in the FINAL group Γ, and its positive edge
support is EXACTLY the canonical content of this group value.
This handles the empty-content case without an implicit
connectedness assumption on the empty spanning graph. -/
theorem endpointPath_with_exact_groupContent
    (K : EGraph V Edge ι)
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen)
    (hDelete : EndpointPreservingSingleEdgeDeletion K gen)
    (u v : V) (w : LabelWord ι)
    (hPath : K.Follows u w v) :
    ∃ q : LabelWord ι,
      K.Follows u q v ∧
      PSTS.SignedWord.evalGroup gen q =
        PSTS.SignedWord.evalGroup gen w ∧
      LabelWord.positiveSupport q =
        RetractableGroupContent.content gen hgen
          (PSTS.SignedWord.evalGroup gen w) := by
  classical
  let valW : Γ := PSTS.SignedWord.evalGroup gen w
  let P : ℕ → Prop := fun n =>
    ∃ q : LabelWord ι,
      K.Follows u q v ∧
      PSTS.SignedWord.evalGroup gen q = valW ∧
      (LabelWord.positiveSupport q).card = n
  have hExists : ∃ n : ℕ, P n :=
    ⟨(LabelWord.positiveSupport w).card, w, hPath, rfl, rfl⟩
  obtain ⟨q, hqPath, hqVal, hqCard⟩ := Nat.find_spec hExists
  have hContentSub :
      RetractableGroupContent.content gen hgen valW ⊆
        LabelWord.positiveSupport q :=
    RetractableGroupContent.content_subset_of_representation
      gen hgen hret valW q hqVal
  have hSupportSub :
      LabelWord.positiveSupport q ⊆
        RetractableGroupContent.content gen hgen valW := by
    intro a ha
    by_contra haNotContent
    have hErasedValue :
        PSTS.SignedWord.evalGroup gen
            (LabelWord.eraseGenerator a q) =
          PSTS.SignedWord.evalGroup gen q := by
      calc
        PSTS.SignedWord.evalGroup gen
            (LabelWord.eraseGenerator a q) = valW :=
          RetractableGroupContent.eraseGenerator_value_of_not_mem_content
            gen hgen hret valW q hqVal a haNotContent
        _ = PSTS.SignedWord.evalGroup gen q := hqVal.symm
    obtain ⟨q', hq'Path, hq'Val, hq'Sub⟩ :=
      hDelete u v q hqPath a ha hErasedValue
    have hStrict : LabelWord.positiveSupport q' ⊂
        LabelWord.positiveSupport q := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro x hx
        exact (Finset.mem_erase.mp (hq'Sub hx)).2
      · intro hEq
        have ha' : a ∈ LabelWord.positiveSupport q' := by
          rw [hEq]
          exact ha
        exact (Finset.mem_erase.mp (hq'Sub ha')).1 rfl
    have hCardStrict :
        (LabelWord.positiveSupport q').card <
          (LabelWord.positiveSupport q).card :=
      Finset.card_lt_card hStrict
    have hMinimal :
        Nat.find hExists ≤ (LabelWord.positiveSupport q').card :=
      Nat.find_min' hExists
        ⟨q', hq'Path, hq'Val.trans hqVal, rfl⟩
    have hContradiction :
        (LabelWord.positiveSupport q').card < Nat.find hExists :=
      lt_of_lt_of_eq hCardStrict hqCard
    exact (not_lt_of_ge hMinimal) hContradiction
  refine ⟨q, hqPath, hqVal, ?_⟩
  exact Finset.Subset.antisymm hSupportSub hContentSub

/-- The empty-content case of corrected Corollary 5.7:
under geometric path replacement, a path with empty
canonical group content can only connect a vertex to itself. -/
theorem endpoint_eq_of_empty_groupContent
    (K : EGraph V Edge ι)
    (gen : ι → Γ) (hgen : IsGenerated gen)
    (hret : Retractable gen)
    (hDelete : EndpointPreservingSingleEdgeDeletion K gen)
    (u v : V) (w : LabelWord ι)
    (hPath : K.Follows u w v)
    (hEmpty :
      RetractableGroupContent.content gen hgen
        (PSTS.SignedWord.evalGroup gen w) = ∅) :
    u = v := by
  obtain ⟨q, hqPath, _, hqContent⟩ :=
    endpointPath_with_exact_groupContent K gen hgen hret
      hDelete u v w hPath
  have hqEmpty : LabelWord.positiveSupport q = ∅ := by
    rw [hqContent]
    exact hEmpty
  have hqNil : q = [] := by
    cases q with
    | nil => rfl
    | cons s tail =>
        have hSome :
            signedBase s ∈
              LabelWord.positiveSupport (s :: tail) := by
          simp [LabelWord.positiveSupport]
        rw [hqEmpty] at hSome
        exact False.elim (Finset.not_mem_empty _ hSome)
  subst q
  exact K.follows_nil_iff.mp hqPath

end ABO
end PSTSEPPA
