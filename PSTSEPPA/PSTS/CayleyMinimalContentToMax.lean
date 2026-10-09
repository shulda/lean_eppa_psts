import PSTSEPPA.PSTS.CayleyPathInclusion
import PSTSEPPA.PSTS.MaxTransporter

/-!
# Exact Cayley minimal-content certificate gives finite PSTS fibre-MAX

Once the genuine Cayley positive-edge path-inclusion lemma is proved,
the sole nontrivial group input left is a finite reflecting group H
that has a group projection to the selected finite Q and, for every
h∈H, a SAME-VALUE signed path whose underlying positive Cayley edge
set is included in that of EVERY other signed path of H-value h.

We formalize this as an explicit conditional certificate. Its
minimal_support clause is the central OPEN content-reflection
theorem from corrected ABO Section 4/5, not an axiom and not
a consequence of the total permutation lifts.

The construction below proves that any such finite certificate
gives the precise MaxTransporterExtension interface previously
verified to imply finite PSTS EPPA with closed embeddings.

This sharpens the mathematical stopping criterion: no full
F-inverse cover theory, arbitrary graph symmetries, or general
partial algebra EPPA need be separately formalized.
-/

namespace PSTSEPPA
namespace PSTS

variable {V ι : Type*} {A : PSTS V}
variable {gen : ι → PartialAut A}
variable (L : TotalPermutationLifts A gen)

/-- A finite Cayley group with a positive-edge CONTENT-MINIMAL
word in each H-value fibre. This is an honest independent
mathematical hypothesis to be discharged by the corrected
Cayley-specialized group reflection theorem. -/
structure CayleyMinimalContentCertificate where
  H : Type*
  [groupH : Group H]
  [fintypeH : Fintype H]
  lift : ι → H
  toQ : H →* L.generatedQ
  toQ_lift : ∀ i : ι, toQ (lift i) = L.cayleyGenerator i
  minimalWord : H → SignedWord ι
  minimalWord_value :
    ∀ h : H, SignedWord.evalGroup lift (minimalWord h) = h
  minimal_support :
    ∀ (h : H) (w : SignedWord ι),
      SignedWord.evalGroup lift w = h →
      ∀ e : L.generatedQ × ι,
        e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator 1
          (minimalWord h) →
        e ∈ ABO.cayleyWordPositiveTrace L.cayleyGenerator 1 w

namespace CayleyMinimalContentCertificate

variable {L : TotalPermutationLifts A gen}
variable (C : CayleyMinimalContentCertificate L)

instance : Group C.H := C.groupH
instance : Fintype C.H := C.fintypeH

/-- Every signed H-word projects to the actual Cayley Q-word value,
including inverse signed generators in chronological order. -/
theorem project_word (w : SignedWord ι) :
    C.toQ (SignedWord.evalGroup C.lift w) = L.valueQ w := by
  have hLetter : ∀ s : SignedLetter ι,
      C.toQ (SignedWord.evalGroupLetter C.lift s) =
      SignedWord.evalGroupLetter L.cayleyGenerator s := by
    intro s
    cases s with
    | pos i =>
        exact C.toQ_lift i
    | neg i =>
        simpa only [SignedWord.evalGroupLetter_neg, map_inv]
          using congrArg Inv.inv (C.toQ_lift i)
  have hWord : ∀ w : SignedWord ι,
      C.toQ (SignedWord.evalGroup C.lift w) =
      SignedWord.evalGroup L.cayleyGenerator w := by
    intro w
    induction w with
    | nil =>
        exact map_one C.toQ
    | cons s w ih =>
        calc
          C.toQ (SignedWord.evalGroup C.lift (s :: w)) =
            C.toQ (SignedWord.evalGroupLetter C.lift s) *
              C.toQ (SignedWord.evalGroup C.lift w) := by
                rw [SignedWord.evalGroup_cons, map_mul]
          _ = SignedWord.evalGroupLetter L.cayleyGenerator s *
                SignedWord.evalGroup L.cayleyGenerator w := by
                  rw [hLetter, ih]
          _ = SignedWord.evalGroup L.cayleyGenerator (s :: w) := rfl
  rw [hWord, L.selectedCayley_wordValue_eq_valueQ]

/-- The chosen reduced word and any competing word in the
same H fibre have identical Q endpoints. This follows from
the actual projection homomorphism, not an extra hypothesis. -/
theorem minimalWord_valueQ_eq
    (h : C.H) (w : SignedWord ι)
    (hw : SignedWord.evalGroup C.lift w = h) :
    L.valueQ (C.minimalWord h) = L.valueQ w := by
  have hmin := C.project_word (C.minimalWord h)
  have hwQ := C.project_word w
  rw [C.minimalWord_value h] at hmin
  rw [hw] at hwQ
  exact hmin.symm.trans hwQ

/-- Main CONDITIONAL bridge: Cayley-minimal positive-edge
supports imply genuine restriction MAX for the concrete
PSTS partial automorphisms, in the EXACT fibre orientation
used by the already-certified closed-PSTS-EPPA transfer. -/
noncomputable def toMaxTransporterExtension :
    MaxTransporterExtension A gen where
  H := C.H
  groupH := C.groupH
  fintypeH := C.fintypeH
  liftGen := C.lift
  maxWord := C.minimalWord
  maxWord_value := C.minimalWord_value
  dominates := by
    intro h w hw
    exact L.partial_le_of_positiveCayleyTrace_subset
      (C.minimalWord h) w
      (C.minimalWord_valueQ_eq h w hw)
      (C.minimal_support h w hw)

end CayleyMinimalContentCertificate
end PSTS
end PSTSEPPA
