import PSTSEPPA.ABO.StandardCosetFamily
import PSTSEPPA.ABO.WeakCompletePairedEdges

/-!
# Rank-two full coset extension: every singleton edge lies in its full coset

The corrected ABO Proposition 5.4 has a genuine k=1 base gap.
One key geometric fact in that base is that the `c`-components of
rank-two FULL coset extensions have only two forms:

  * an actual full {c}-coset, if the vertex belongs to such a summand;
  * an isolated singleton with NO outgoing c-labelled edge, otherwise.

This module certifies the structural edge-source half of that
dichotomy from the ACTUAL weakly complete tagged multi-coset graph.

At rank |A|=2, if a proper constituent D contains c, then D={c}.
Weak completeness says every signed edge of the multi-extension is
represented in some completed constituent. Hence every c-labelled
edge originates within the FULL selected {c}-coset summand.
Consequently a point not belonging to any of those tagged cosets
has no outgoing +c OR -c edges. Under trivial loop completion,
such a point is fixed by both c actions.

This avoids the invalid argument that the multi-CE projection into
the ambient Cayley group is globally injective: only the already
certified inclusion of a selected tagged coset is used.

The remaining R2 step must still analyze actual augmented Z₁
components and deduce 1-stability of the constructed G₂→H₁;
neither conclusion is claimed in this module.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- At rank two the ONLY proper constituent containing i is {i}.
Empty constituents and the other singleton may still be present. -/
theorem allProper_rankTwo_label_unique
    (hcard : A.card = 2) (i : ι)
    (D : Finset ι)
    (hD : D ∈ (allProperCosetFamily A).alphabets)
    (hi : i ∈ D) :
    D = {i} := by
  have hProper : D ⊂ A :=
    (mem_allProperCosetFamily A D).mp hD
  have hLess : D.card < 2 := by
    simpa [hcard] using (Finset.card_lt_card hProper)
  have hAtMostOne : D.card ≤ 1 := Nat.le_of_lt_succ hLess
  ext x
  constructor
  · intro hx
    have hxi : x = i :=
      (Finset.card_le_one.mp hAtMostOne) x hx i hi
    simpa [hxi]
  · intro hx
    have hxi : x = i := Finset.mem_singleton.mp hx
    simpa [hxi] using hi

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- When selected constituents containing i must all equal B,
every i-labelled global multi-coset edge has a source INSIDE
the full selected component-tagged B-coset.

This is proved with actual edge representatives and their
source morphisms, not with any ambient-group injectivity. -/
theorem multiCoset_edge_source_in_unique_label_coset
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hweak : K.MultiCosetWeaklyComplete P hadm hgen hret)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (i : ι)
    (hUnique : ∀ D ∈ P.alphabets, i ∈ D → D = B)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret)
    (hi : signedBase
      ((K.multiCosetEGraph P hadm hgen hret).label e) = i) :
    ∃ p : K.AttachedCosetVertex B,
      (K.multiCosetEGraph P hadm hgen hret).source e =
        K.multiCosetInclude P hadm hgen hret B hBP p := by
  obtain ⟨D, hDP, p, s, he⟩ := hweak e
  have hiD : i ∈ D := by
    have hlabel :
        (K.multiCosetEGraph P hadm hgen hret).label e = s.1 := by
      rw [← he]
      rfl
    have hb : signedBase s.1 = i := by
      rw [← hlabel]
      exact hi
    rw [← hb]
    exact s.2
  have hDB : D = B := hUnique D hDP hiD
  subst D
  let F := K.singleCosetToMultiHom P hadm hgen hret B hBP
  let eB : K.SingleCosetEdge B := Sum.inr (p, s)
  refine ⟨p, ?_⟩
  have heq : F.onEdge eB = e := by
    exact he
  calc
    (K.multiCosetEGraph P hadm hgen hret).source e =
        (K.multiCosetEGraph P hadm hgen hret).source (F.onEdge eB) := by
          rw [heq]
    _ = F.onVertex ((K.singleCosetEGraph B).source eB) :=
      F.map_source eB
    _ = F.onVertex p := rfl
    _ = K.multiCosetInclude P hadm hgen hret B hBP p := rfl

/-- Specialize the edge-source dichotomy to full proper coset
extensions of RANK TWO. Every edge with base label i must
originate inside the full {i}-coset constituent. -/
theorem allProper_rankTwo_signedEdge_source_in_singleton_coset
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card = 2)
    (i : ι) (hiA : i ∈ A)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hlabel :
      signedBase ((K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).label e) = i) :
    ∃ p : K.AttachedCosetVertex ({i} : Finset ι),
      (K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).source e =
      K.multiCosetInclude (allProperCosetFamily A)
        hadm hgen hret {i}
        ((mem_allProperCosetFamily A {i}).mpr
          (singleton_ssubset_of_card_ge_two A (by simp [hcard]) i hiA))
        p := by
  let P := allProperCosetFamily A
  have hBP : ({i} : Finset ι) ∈ P.alphabets :=
    (mem_allProperCosetFamily A {i}).mpr
      (singleton_ssubset_of_card_ge_two A
        (by simp [hcard]) i hiA)
  have hWeak : K.MultiCosetWeaklyComplete P hadm hgen hret :=
    allProperCosetFamily_weaklyComplete K hadm hgen hret
      (by simp [hcard])
  have hUnique : ∀ D ∈ P.alphabets, i ∈ D → D = ({i} : Finset ι) := by
    intro D hD hiD
    exact allProper_rankTwo_label_unique hcard i D hD hiD
  exact K.multiCoset_edge_source_in_unique_label_coset
    P hadm hgen hret hWeak {i} hBP i hUnique e hlabel

/-- A rank-two full coset-extension vertex OUTSIDE the selected
full {i}-coset constituents has no originally available signed
i-labelled edge in either direction. It is therefore isolated
in the i-subgraph before adding trivial loops. -/
theorem allProper_rankTwo_outside_singleton_has_no_label
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : A.card = 2)
    (i : ι) (hiA : i ∈ A)
    (u : K.MultiCosetVertex (allProperCosetFamily A) hadm hgen hret)
    (houtside :
      ∀ p : K.AttachedCosetVertex ({i} : Finset ι),
        u ≠ K.multiCosetInclude (allProperCosetFamily A)
          hadm hgen hret {i}
          ((mem_allProperCosetFamily A {i}).mpr
            (singleton_ssubset_of_card_ge_two A
              (by simp [hcard]) i hiA)) p)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient
      (allProperCosetFamily A) hadm hgen hret)
    (hsource :
      (K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).source e = u) :
    signedBase ((K.multiCosetEGraph
      (allProperCosetFamily A) hadm hgen hret).label e) ≠ i := by
  intro hlabel
  obtain ⟨p, hp⟩ :=
    K.allProper_rankTwo_signedEdge_source_in_singleton_coset
      hadm hgen hret hcard i hiA e hlabel
  exact houtside p (hsource.symm.trans hp)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
