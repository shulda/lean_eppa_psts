import PSTSEPPA.ABO.Retractability

/-!
# Retractability and Cayley covers

This file formalizes ABO Proposition 3.3 for finite labelled groups.

The target attached to a subalphabet `A` is the Cayley graph of
`generatedSubgroup gen A` with every generator outside `A` acting as the
identity.  This is exactly the source paper's trivial completion
`overline(G[A])`.
-/

namespace PSTSEPPA
namespace ABO

open PSTS

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]

/-- A based surjective canonical Cayley morphism onto the trivial completion
of the `A`-subgroup Cayley graph.

For complete deterministic labelled graphs, surjectivity on vertices already
forces surjectivity on directed edges; vertex-surjectivity is the only part
stored explicitly. -/
structure TrivialCompletionCover (gen : ι → Γ) (A : Finset ι) where
  hom :
    LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      (cayleyGraph (trivialCompletionGenerator gen A)).toEGraph.toLabelledGraph
  map_one : hom.onVertex 1 = 1
  vertex_surjective : Function.Surjective hom.onVertex

/-- The source-paper single-generator deletion is restriction to the
complementary subalphabet. -/
@[simp]
theorem LabelWord.restrictTo_univ_erase (a : ι) (w : LabelWord ι) :
    LabelWord.restrictTo (Finset.univ.erase a) w =
      LabelWord.eraseGenerator a w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      by_cases h : signedBase s = a
      · simp [LabelWord.restrictTo, LabelWord.eraseGenerator,
          LabelWord.deleteGenerators, h, ih]
      · simp [LabelWord.restrictTo, LabelWord.eraseGenerator,
          LabelWord.deleteGenerators, h, ih]

/-- The easy direction of ABO Proposition 3.3:
if every trivial completion is covered by the ambient Cayley graph, then the
labelled group is retractable. -/
theorem retractable_of_trivialCompletionCovers
    (gen : ι → Γ)
    (hcovers : ∀ A : Finset ι, TrivialCompletionCover gen A) :
    Retractable gen := by
  intro a p q hpq
  let A : Finset ι := Finset.univ.erase a
  let C := hcovers A
  let S := cayleyGraph gen
  let T := cayleyGraph (trivialCompletionGenerator gen A)

  have hsrc :
      S.followWord (1 : Γ) p = S.followWord (1 : Γ) q := by
    change
      (cayleyGraph gen).followWord (1 : Γ) p =
        (cayleyGraph gen).followWord (1 : Γ) q
    rw [cayleyGraph.followWord_eq_mul_evalGroup,
      cayleyGraph.followWord_eq_mul_evalGroup]
    simpa using hpq

  have htarget :
      T.followWord (1 : generatedSubgroup gen A) p =
        T.followWord (1 : generatedSubgroup gen A) q := by
    calc
      T.followWord (1 : generatedSubgroup gen A) p =
          T.followWord (C.hom.onVertex (1 : Γ)) p := by
            rw [C.map_one]
      _ = C.hom.onVertex (S.followWord (1 : Γ) p) := by
            exact CompleteEGraph.hom_followWord S T C.hom (1 : Γ) p
      _ = C.hom.onVertex (S.followWord (1 : Γ) q) := by
            exact congrArg C.hom.onVertex hsrc
      _ = T.followWord (C.hom.onVertex (1 : Γ)) q := by
            exact (CompleteEGraph.hom_followWord S T C.hom (1 : Γ) q).symm
      _ = T.followWord (1 : generatedSubgroup gen A) q := by
            rw [C.map_one]

  have htargetEval :
      PSTS.SignedWord.evalGroup (trivialCompletionGenerator gen A) p =
        PSTS.SignedWord.evalGroup (trivialCompletionGenerator gen A) q := by
    change
      (cayleyGraph (trivialCompletionGenerator gen A)).followWord
          (1 : generatedSubgroup gen A) p =
        (cayleyGraph (trivialCompletionGenerator gen A)).followWord
          (1 : generatedSubgroup gen A) q at htarget
    rw [cayleyGraph.followWord_eq_mul_evalGroup,
      cayleyGraph.followWord_eq_mul_evalGroup] at htarget
    simpa using htarget

  have hcoe := congrArg
    (fun x : generatedSubgroup gen A => (x : Γ)) htargetEval
  rw [coe_evalGroup_trivialCompletionGenerator,
    coe_evalGroup_trivialCompletionGenerator] at hcoe
  change
    PSTS.SignedWord.evalGroup gen
        (LabelWord.restrictTo (Finset.univ.erase a) p) =
      PSTS.SignedWord.evalGroup gen
        (LabelWord.restrictTo (Finset.univ.erase a) q) at hcoe
  simpa using hcoe

end ABO
end PSTSEPPA
