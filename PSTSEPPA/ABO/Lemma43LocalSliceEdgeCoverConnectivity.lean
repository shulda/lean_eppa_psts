import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion

/-!
# ABO Lemma 4.3: the edge cover needs to cover only the CHOSEN B-component

The previous exact edge-cover connectivity lemma accepted an edge
cover of *every* B-edge in the whole multiCE. That is a correct
abstract implication but far stronger than the ACTUAL source
construction, where one fixes one intrinsic B-component Q and
selects only constituent cosets meeting Q.

The source only guarantees the following genuinely LOCAL statement:

  whenever an actual B-edge has a source B-reachable from the
  selected anchor root of Q, that edge belongs to some selected
  constituent slice indexed in I, including both oriented endpoints.

This file proves that EXACT weaker hypothesis suffices to
connect the intersection graph of the selected slices. The
proof works entirely in the original incomplete signed
EGraph and explicitly tracks the growing realised B-word
prefix from the fixed anchor. At each edge, that prefix
supplies the required source-in-Q witness, allowing
the locally indexed coatom edge-cover to be applied.

The final specialization uses the genuine Definition-3.22
component-tagged constituent slices B_i=Q∩v_iH[A_i].
Their original old C-component tags are retained.

This is the source-faithful connectivity interface for the
finite-family common-core theorem. It does NOT assume
all other B-components of the entire extension are covered
by the same selected family. The precise FINITE index
construction using CoatomEdgeCover and the finiteness
of H[A] remains separate.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V Edge ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- A signed path from u∈Q to v∈Q induces a walk
through the actual intersection graph of selected
edge-cover slices if every TRUE B-edge whose SOURCE
is reachable from Q's chosen anchor is contained in
some such slice.

The chosen family need NOT cover any edges outside Q;
the proof carries a realised signed B-prefix throughout
the induction and does not appeal to any imaginary
Cayley completion edges. -/
theorem local_B_component_path_slices_overlap_connected
    (G : EGraph V Edge ι)
    (B : Finset ι) (anchor : V)
    (slices : κ → Set V) (I : Finset κ)
    (hLocalEdgeCover :
      ∀ e : Edge,
        (∃ w : LabelWord ι,
          LabelWord.Uses B w ∧
            G.Follows anchor w (G.source e)) →
        signedBase (G.label e) ∈ B →
        ∃ k ∈ I,
          G.source e ∈ slices k ∧ G.target e ∈ slices k)
    {u v : V} {w : LabelWord ι}
    (hAnchorU :
      ∃ p : LabelWord ι,
        LabelWord.Uses B p ∧ G.Follows anchor p u)
    (hp : G.Follows u w v)
    (hw : LabelWord.Uses B w)
    (i j : κ) (hi : i ∈ I) (hj : j ∈ I)
    (hu : u ∈ slices i) (hv : v ∈ slices j) :
    Relation.ReflTransGen
      (fun a b : κ =>
        a ∈ I ∧ b ∈ I ∧ (slices a ∩ slices b).Nonempty)
      i j := by
  let R : κ → κ → Prop :=
    fun a b => a ∈ I ∧ b ∈ I ∧ (slices a ∩ slices b).Nonempty
  have hPath :
      ∀ {x y : V} {p : LabelWord ι},
        G.Follows x p y → LabelWord.Uses B p →
          (∃ q : LabelWord ι,
            LabelWord.Uses B q ∧ G.Follows anchor q x) →
          ∀ (a b : κ),
            a ∈ I → b ∈ I →
            x ∈ slices a → y ∈ slices b →
            Relation.ReflTransGen R a b := by
    intro x y p hReal
    induction hReal with
    | nil x =>
        intro _hpB _hAnchorX a b ha hb hxa hxb
        have hab : R a b := ⟨ha, hb, ⟨x, hxa, hxb⟩⟩
        exact Relation.ReflTransGen.tail
          Relation.ReflTransGen.refl hab
    | @cons x y s p e hsource hlabel hrest ih =>
        intro hpB hAnchorX a b ha hb hxa hyb
        have hLetterB : signedBase (G.label e) ∈ B := by
          rw [hlabel]
          exact hpB.1
        have hSourceReach :
            ∃ q : LabelWord ι,
              LabelWord.Uses B q ∧
                G.Follows anchor q (G.source e) := by
          obtain ⟨q, hqB, hqPath⟩ := hAnchorX
          refine ⟨q, hqB, ?_⟩
          rw [hsource]
          exact hqPath
        obtain ⟨k, hk, hSourceK, hTargetK⟩ :=
          hLocalEdgeCover e hSourceReach hLetterB
        have hXK : x ∈ slices k := by
          simpa only [hsource] using hSourceK
        have hE : G.Follows x [s] (G.target e) :=
          EGraph.Follows.cons e hsource hlabel
            (EGraph.Follows.nil (G.target e))
        have hNextReach :
            ∃ q : LabelWord ι,
              LabelWord.Uses B q ∧
                G.Follows anchor q (G.target e) := by
          obtain ⟨q, hqB, hqPath⟩ := hAnchorX
          refine ⟨q ++ [s], ?_, ?_⟩
          · exact (LabelWord.uses_append B q [s]).mpr
              ⟨hqB, ⟨hpB.1, trivial⟩⟩
          · exact G.follows_append hqPath hE
        have hak : R a k := ⟨ha, hk, ⟨x, hxa, hXK⟩⟩
        have hStep : Relation.ReflTransGen R a k :=
          Relation.ReflTransGen.tail
            Relation.ReflTransGen.refl hak
        have hRest : Relation.ReflTransGen R k b :=
          ih hpB.2 hNextReach k b hk hb hTargetK hyb
        exact hStep.trans hRest
  exact hPath hp hw hAnchorU i j hi hj hu hv

/-- Source-exact connectivity of a finite selected indexed
family of B-component slices with only a LOCAL edge-cover
hypothesis, i.e. edges from the CHOSEN B-component Q.

This is the correct hypothesis to combine with the
genuine coatom edge-cover theorem and finite list
of coatom attachments in the published Lemma 4.3. -/
theorem local_selected_B_component_slices_overlap_connected
    (G : EGraph V Edge ι)
    (B : Finset ι) (anchor : V)
    (slices : κ → Set V) (I : Finset κ)
    (root : κ) (hroot : root ∈ I)
    (hNonempty : ∀ i ∈ I, (slices i).Nonempty)
    (hBComponent :
      ∀ i ∈ I, ∀ z ∈ slices i,
        ∃ w : LabelWord ι,
          LabelWord.Uses B w ∧ G.Follows anchor w z)
    (hLocalEdgeCover :
      ∀ e : Edge,
        (∃ w : LabelWord ι,
          LabelWord.Uses B w ∧
            G.Follows anchor w (G.source e)) →
        signedBase (G.label e) ∈ B →
        ∃ k ∈ I,
          G.source e ∈ slices k ∧ G.target e ∈ slices k) :
    ∀ i ∈ I, Relation.ReflTransGen
      (fun j k : κ =>
        j ∈ I ∧ k ∈ I ∧ (slices j ∩ slices k).Nonempty)
      root i := by
  obtain ⟨u, huRoot⟩ := hNonempty root hroot
  obtain ⟨wu, hwU, hAnchorU⟩ :=
    hBComponent root hroot u huRoot
  intro i hi
  obtain ⟨v, hvI⟩ := hNonempty i hi
  obtain ⟨wv, hwV, hAnchorV⟩ :=
    hBComponent i hi v hvI
  have hUV :
      G.Follows u (PSTS.SignedWord.inv wu ++ wv) v :=
    G.follows_append (G.follows_inverse hAnchorU) hAnchorV
  have hwUV :
      LabelWord.Uses B (PSTS.SignedWord.inv wu ++ wv) :=
    (LabelWord.uses_append B _ _).mpr ⟨hwU.inv, hwV⟩
  exact G.local_B_component_path_slices_overlap_connected
    B anchor slices I hLocalEdgeCover
    ⟨wu, hwU, hAnchorU⟩ hUV hwUV
    root i hroot hi huRoot hvI

end EGraph

variable {ι Γ κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable [DecidableEq κ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The ACTUAL source Lemma-4.3 finite-family overlap
connectivity for original component-tagged slices of
ONE intrinsic B-component Q, under EDGE coverage
of Q alone (not of the whole multiCE).

Every selected slice is B-reachable by its very definition;
only the existence of a source-local coatom-edge-index
inside the finite chosen family remains an explicit input. -/
theorem allProperCoset_local_tagged_slice_overlap_connected
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (C : κ → Finset ι)
    (hCP : ∀ i : κ,
      C i ∈ (allProperCosetFamily A).alphabets)
    (c : ∀ i : κ, K.ComponentIndex (C i))
    (I : Finset κ)
    (root : κ) (hroot : root ∈ I)
    (hNonempty : ∀ i ∈ I,
      (K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor (C i) (hCP i) (c i)).Nonempty)
    (hLocalEdgeCover :
      ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret,
        (∃ w : LabelWord ι,
          LabelWord.Uses B w ∧
            (K.multiCosetEGraph (allProperCosetFamily A)
              hadm hgen hret).Follows anchor w
              ((K.multiCosetEGraph (allProperCosetFamily A)
                hadm hgen hret).source e)) →
        signedBase
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).label e) ∈ B →
        ∃ i ∈ I,
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).source e ∈
            K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i) ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).target e ∈
            K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i)) :
    ∀ i ∈ I, Relation.ReflTransGen
      (fun j k : κ =>
        j ∈ I ∧ k ∈ I ∧
          ((K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor (C j) (hCP j) (c j)) ∩
           (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor (C k) (hCP k) (c k))).Nonempty)
      root i := by
  let G := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  let slices : κ → Set
      (K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret) :=
    fun i => K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor (C i) (hCP i) (c i)
  have hInside :
      ∀ i ∈ I, ∀ z ∈ slices i,
        ∃ w : LabelWord ι,
          LabelWord.Uses B w ∧ G.Follows anchor w z := by
    intro i _hi z hz
    exact hz.1
  exact G.local_selected_B_component_slices_overlap_connected
    B anchor slices I root hroot
    hNonempty hInside hLocalEdgeCover

end CayleySubgraphSpec
end ABO
end PSTSEPPA
