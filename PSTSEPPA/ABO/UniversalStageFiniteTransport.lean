import PSTSEPPA.ABO.UniversalKernelAllSizesCatalogue

/-!
# Exact transport of ANY finite completed ABO stage into the universal catalogue

The finite all-sizes catalogue is indexed by actions on Fin n, whereas
the true ABO coset extensions have rich tagged/quotient vertex types.
No replacement of those true vertices by ambient Cayley coordinates
is valid, as the explicit geometry counterexamples demonstrate.

This module transports the ACTUAL positive and inverse transition
permutations of an arbitrary complete E-graph T along an honest
equivalence e : V ≃ Fin n. It proves exact signed-path naturality,
preserves the rank-k kernel requirement, and provides a LITERAL
index in the universal bounded-size catalogue whenever |V| <= M.

The only additional hypotheses for an arbitrary true completed
stage are its finite size bound and its *real* transition word-kernel
condition. Those are exactly the remaining source Definition-5.3
geometric gates. This transport itself does not assert them.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*} [Fintype ι] [DecidableEq ι]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- Transport the actual positive transition permutation of a genuine
completed E-graph along an arbitrary bijection of vertex carriers.
No injectivity of the map of generator labels is imposed. -/
noncomputable def transportedAction {n : ℕ} (e : V ≃ Fin n) :
    ι → Equiv.Perm (Fin n) :=
  fun i => (e.symm.trans (T.letterPerm (.pos i))).trans e

/-- Transporting a positive or inverse signed step retains its exact
target; the inverse case uses the TRUE inverse transition of T. -/
theorem transportedAction_signed_step
    {n : ℕ} (e : V ≃ Fin n) (v : V)
    (s : SignedLabel ι) :
    signedPerm (T.transportedAction e) s (e v) =
      e (T.letterPerm s v) := by
  cases s with
  | pos i =>
      simp [signedPerm, transportedAction]
  | neg i =>
      rw [T.letterPerm_inv (.pos i)]
      simp [signedPerm, transportedAction]

/-- The transported action follows exactly the same full signed word
as T, conjugated by the vertex bijection. No missing edge is
completed anew, and both formal inverse labels are preserved. -/
theorem transportedAction_followWord
    {n : ℕ} (e : V ≃ Fin n) (v : V) (w : LabelWord ι) :
    (actionGraph (T.transportedAction e)).followWord (e v) w =
      e (T.followWord v w) := by
  induction w generalizing v with
  | nil =>
      rfl
  | cons s w ih =>
      rw [CompleteEGraph.followWord_cons]
      rw [CompleteEGraph.followWord_cons]
      rw [← CompleteEGraph.letterPerm_apply]
      rw [← CompleteEGraph.letterPerm_apply]
      rw [actionGraph.letterPerm]
      rw [T.transportedAction_signed_step]
      exact ih _

/-- Conjugating the actual finite stage preserves its true identity
word kernel for all signed words. It does not rely on a Cayley
embedding of the original tagged coset-extension quotient. -/
theorem transportedAction_wordValue_eq_one
    {n : ℕ} (e : V ≃ Fin n) (w : LabelWord ι)
    (hval : T.wordValue w = 1) :
    (actionGraph (T.transportedAction e)).wordValue w = 1 := by
  apply ((actionGraph (T.transportedAction e)).
    wordValue_eq_one_iff_all_vertices_fixed w).mpr
  intro y
  calc
    (actionGraph (T.transportedAction e)).followWord y w =
        (actionGraph (T.transportedAction e)).
          followWord (e (e.symm y)) w := by
            exact congrArg
              (fun z => (actionGraph (T.transportedAction e)).followWord z w)
              (e.apply_symm_apply y).symm
    _ = e (T.followWord (e.symm y) w) :=
        T.transportedAction_followWord e (e.symm y) w
    _ = e (e.symm y) := by
        rw [(T.wordValue_eq_one_iff_all_vertices_fixed w).mp hval]
    _ = y := e.apply_symm_apply y

end CompleteEGraph

variable [Group Γ]

/-- Every real finite completed stage which satisfies the ambient
rank-k word-kernel test gives a literal finite-catalogue entry
after any chosen equivalence of its vertex set with Fin n.
This is an exact action, not padded by stationary vertices. -/
noncomputable def exactStageCatalogueEntry
    (gen : ι → Γ) (k M n : ℕ)
    (T : CompleteEGraph V Edge ι)
    (e : V ≃ Fin n) (hn : n ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1) :
    boundedKernelAllSizesIndex gen k M :=
  boundedKernelAllSizesEntry gen k M n hn
    (T.transportedAction e)
    (by
      intro C hC w hw hval
      exact T.transportedAction_wordValue_eq_one e w
        (hkernel C hC w hw hval))

/-- Every actual signed word path in the original completed stage
is transported to the corresponding TRUE tagged component of
the all-sizes universal complete EGraph. This statement gives
the precise source-to-universal action interface. -/
theorem exactStageCatalogueEntry_followWord
    (gen : ι → Γ) (k M n : ℕ)
    (T : CompleteEGraph V Edge ι)
    (e : V ≃ Fin n) (hn : n ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1)
    (v : V) (w : LabelWord ι) :
    (boundedKernelAllSizesStage gen k M).followWord
      (⟨exactStageCatalogueEntry gen k M n T e hn hkernel, e v⟩ :
        boundedKernelAllSizesVertex gen k M) w =
      ⟨exactStageCatalogueEntry gen k M n T e hn hkernel,
        e (T.followWord v w)⟩ := by
  calc
    (boundedKernelAllSizesStage gen k M).followWord
        (⟨exactStageCatalogueEntry gen k M n T e hn hkernel, e v⟩ :
          boundedKernelAllSizesVertex gen k M) w =
        ⟨exactStageCatalogueEntry gen k M n T e hn hkernel,
          (actionGraph (T.transportedAction e)).followWord (e v) w⟩ := by
          exact boundedKernelAllSizesEntry_followWord gen k M n hn
            (T.transportedAction e)
            (by
              intro C hC w hw hval
              exact T.transportedAction_wordValue_eq_one e w
                (hkernel C hC w hw hval)) (e v) w
    _ = ⟨exactStageCatalogueEntry gen k M n T e hn hkernel,
          e (T.followWord v w)⟩ := by
          rw [T.transportedAction_followWord]

/-- Canonical finite type specialization: the true arbitrary
finite carrier is renamed by a bijection to Fin(card V).
The original graph need not be a Cayley subgraph. -/
noncomputable def finiteExactStageCatalogueEntry
    [Fintype V]
    (gen : ι → Γ) (k M : ℕ)
    (T : CompleteEGraph V Edge ι)
    (hcard : Fintype.card V ≤ M)
    (hkernel :
      ∀ (C : Finset ι), C.card ≤ k →
        ∀ (w : LabelWord ι), LabelWord.Uses C w →
          PSTS.SignedWord.evalGroup gen w = 1 →
            T.wordValue w = 1) :
    boundedKernelAllSizesIndex gen k M := by
  classical
  exact exactStageCatalogueEntry gen k M (Fintype.card V)
    T (Fintype.equivFin V) hcard hkernel

end ABO
end PSTSEPPA
