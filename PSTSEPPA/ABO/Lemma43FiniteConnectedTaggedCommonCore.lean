import PSTSEPPA.ABO.Lemma43MinimumWitnessPropagation

/-!
# ABO Lemma 4.3: one original tagged common core for a finite connected family

This is the FINITE-CONSTITUENT part of the existing proof of
Auinger--Bitterlich--Otto, Lemma 4.3 (PDF pp.37–38),
not an alternative mathematical conjecture.

Fix one TRUE signed intrinsic B-path component Q of the
original uncompleted full component-tagged coset extension.
We have a finite family I of selected constituent slices
S_i = Q ∩ v_i H[C_i] with their ORIGINAL old skeleton
component tags c_i. The "intersection graph" on I has
an edge i--j exactly when S_i ∩ S_j has an ACTUAL
original quotient vertex. Assume the family is connected
in that literal graph, based at an included index root.

The LOWER-RANK cluster-property induction supplies each
S_i with an attained minimum component-tagged support.
The previously certified pairwise witness-propagation
lemma (source Figures 7 -> 8) says:

  if two slices overlap, EVERY chosen vertex attaining
  the first slice's minimum lies also in the second,
  and the SAME original tagged minimum is valid there.

We now formally iterate that statement ALONG EVERY FINITE
PATH in the actual overlap graph. Consequently:
  (1) there is ONE tagged support (M,m), with original
      old-component index m, minimum for every slice;
  (2) ONE ACTUAL vertex z attaining (M,m) belongs
      simultaneously to ALL selected slices;
  (3) the WHOLE UNION of the finite family has
      that same attained minimum.

This is the finite connected-cover/common-core
induction from ABO Lemma 4.3, with no fake old
edges or group-coordinate identifications.

The theorem explicitly ASSUMES a finite connected
family of true constituent slices and lower-rank
minimum supports. That finite family and its
connectivity are obtained from the source's minimal
maximal-constituent cover of Q; formalizing the
construction of that cover, proving its connectivity,
handling the already-full-B-coset alternative,
localizing retractability from H to H[A], and
identifying the final B-cluster via Corollary 3.12
remain separate obligations.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable [DecidableEq κ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- FINITE CONNECTED constituent-family minimum-core theorem
matching the final many-piece induction in source Lemma 4.3.

Every slice is a TRUE old-component-tagged constituent
intersection with the SAME actual B-path component.
Connectivity is given by the reflexive-transitive
closure of the literal intersection relation of these
slices (not by equality of their ambient group cosets).

The lower-rank induction is precisely the explicit
premise that EACH slice already has some attained
original-tagged minimum support.

The result produces ONE ACTUAL minimum witness z
IN THE INTERSECTION OF ALL SLICES, and the same
attained minimum support for the full UNION. -/
theorem allProperCoset_connected_tagged_family_common_minimum
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (C : κ → Finset ι)
    (hCP : ∀ i : κ,
      C i ∈ (allProperCosetFamily A).alphabets)
    (c : ∀ i : κ, K.ComponentIndex (C i))
    (indices : Finset κ)
    (root : κ) (hroot : root ∈ indices)
    (hConnected :
      ∀ i ∈ indices,
        Relation.ReflTransGen
          (fun j k : κ =>
            j ∈ indices ∧ k ∈ indices ∧
            ((K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C j) (hCP j) (c j)) ∩
             (K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C k) (hCP k) (c k))).Nonempty)
          root i)
    (hEachMinimum :
      ∀ i ∈ indices,
        ∃ (M : Finset ι) (m : K.ComponentIndex M),
          K.IsMinimalTaggedSupportFor
            (allProperCosetFamily A) hadm hgen hret
            (K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i))
            M m) :
    ∃ (M : Finset ι) (m : K.ComponentIndex M)
      (z : K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret),
      K.HasTaggedSupportAt (allProperCosetFamily A)
        hadm hgen hret M m z ∧
      (∀ i ∈ indices,
        z ∈ K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i) ∧
        K.IsMinimalTaggedSupportFor
          (allProperCosetFamily A) hadm hgen hret
          (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor (C i) (hCP i) (c i))
          M m) ∧
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        { y | ∃ i ∈ indices,
          y ∈ K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i) }
        M m := by
  let P := allProperCosetFamily A
  let S : κ → Set (K.MultiCosetVertex P hadm hgen hret) :=
    fun i => K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor (C i) (hCP i) (c i)
  let R : κ → κ → Prop :=
    fun i j => i ∈ indices ∧ j ∈ indices ∧ (S i ∩ S j).Nonempty
  obtain ⟨M, m, hRootMin⟩ := hEachMinimum root hroot
  obtain ⟨z, hzRoot, hzSupport⟩ := hRootMin.1
  have hConn : ∀ i ∈ indices, Relation.ReflTransGen R root i :=
    hConnected
  have hPropagate :
      ∀ i j : κ, i ∈ indices → j ∈ indices →
        (S i ∩ S j).Nonempty →
        (z ∈ S i ∧
          K.IsMinimalTaggedSupportFor
            P hadm hgen hret (S i) M m) →
        z ∈ S j ∧
          K.IsMinimalTaggedSupportFor
            P hadm hgen hret (S j) M m := by
    intro i j _hi hj hOverlap hCurrent
    obtain ⟨N, n, hMinJ⟩ := hEachMinimum j hj
    obtain ⟨t, htI, htJ⟩ := hOverlap
    exact K.allProperCoset_minimum_witness_propagates_to_adjacent_slice
      hadm hgen hret
      B (C i) (C j) (hCP i) (hCP j)
      anchor (c i) (c j) M m hCurrent.2
      ⟨N, n, hMinJ⟩
      z hCurrent.1 hzSupport t htI htJ
  have hAlong :
      ∀ i : κ, Relation.ReflTransGen R root i →
        z ∈ S i ∧
          K.IsMinimalTaggedSupportFor
            P hadm hgen hret (S i) M m := by
    intro i hWalk
    induction hWalk with
    | refl =>
        exact ⟨hzRoot, hRootMin⟩
    | tail _hPrev hStep ih =>
        exact hPropagate _ _
          hStep.1 hStep.2.1 hStep.2.2 ih
  have hAll :
      ∀ i ∈ indices,
        z ∈ S i ∧
          K.IsMinimalTaggedSupportFor
            P hadm hgen hret (S i) M m := by
    intro i hi
    exact hAlong i (hConn i hi)
  refine ⟨M, m, z, hzSupport, hAll, ?_⟩
  constructor
  · exact ⟨z, ⟨root, hroot, hzRoot⟩, hzSupport⟩
  · intro D hDP p y hy hPy
    obtain ⟨i, hi, hySlice⟩ := hy
    exact (hAll i hi).2.2 D hDP p y hySlice hPy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
