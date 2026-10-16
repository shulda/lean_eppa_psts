import PSTSEPPA.ABO.KStablePullbackComponentGraphEquiv
import PSTSEPPA.ABO.ComponentIndexMonotonicity
import PSTSEPPA.ABO.MultiCosetOverlap

/-!
# Genuine component-tagged coset support transport across G ↠ H pullbacks

Let Q:G↠H be a labelled group quotient, K a genuinely INCOMPLETE
H-Cayley A-skeleton, and L := Q⁻¹(K) the old-edge G-pullback.

The full ABO coset extension is NOT a quotient by ambient group
coordinates. For every B it first forms an independent tagged
coset over EACH intrinsic old B-component, and it later glues
the B/C copies ONLY when they share a common actual (B∩C)
component support.

This module transports exactly that raw gluing geometry:
* map each actual G intrinsic B-component INDEX to its H image;
* this index map is onto but NOT in general one-to-one;
* the map commutes with B⊆C refinement of component indices;
* on each selected indexed full G[B] coset, the group quotient
  maps into the corresponding indexed full H[B] coset;
* if Q is stable on B, the map between these two full coset
  fibre carriers is an actual BIJECTION;
* transporting an attached vertex keeps the component tag;
* the attached map commutes with increasing the alphabet;
* therefore true component-tagged (B∩C)-intersection
  supports map to true (B∩C)-supports downstairs.

IMPORTANT: THE CONVERSE INTERSECTION-SUPPORT REFLECTION AND
INJECTIVITY ACROSS DIFFERENT G COMPONENT TAGS ARE NOT CLAIMED.
They are the difficult mixed-support G-level multiCE embedding
step in corrected ABO Theorem 4.7(ii). This file is intended
to expose that exact remaining obligation without an invalid
ambient-value identification or fake completion of old edges.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- The ACTUAL B-component index of an old G-pullback
vertex determines an unambiguous H B-component index.
Different G-component tags may map to the SAME H tag. -/
noncomputable def pullbackQuotient_componentIndexToBase
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) :
    (K.pullbackQuotient Q).ComponentIndex B → K.ComponentIndex B :=
  fun c => Quotient.liftOn c
    (fun x => K.componentClass B ((K.pullbackQuotientHom Q).onVertex x))
    (by
      intro x y hxy
      apply (K.componentClass_eq_iff B
        ((K.pullbackQuotientHom Q).onVertex x)
        ((K.pullbackQuotientHom Q).onVertex y)).mpr
      obtain ⟨w, hw, hp⟩ := hxy
      exact ⟨w, hw, hp.map (K.pullbackQuotientHom Q)⟩)

/-- Actual old-root component tags project precisely to
the H component of the same original signed-cover point. -/
@[simp] theorem pullbackQuotient_componentIndexToBase_class
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (x : (K.pullbackQuotient Q).Vertex) :
    K.pullbackQuotient_componentIndexToBase Q B
      ((K.pullbackQuotient Q).componentClass B x) =
    K.componentClass B ((K.pullbackQuotientHom Q).onVertex x) :=
  rfl

/-- Every actual H B-component has an old G-cover component
above it because the genuine old quotient skeleton map is
surjective on vertices. Global tag injectivity is NOT claimed. -/
theorem pullbackQuotient_componentIndexToBase_surjective
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) :
    Function.Surjective (K.pullbackQuotient_componentIndexToBase Q B) := by
  intro c
  induction c using Quotient.inductionOn with
  | h y =>
      obtain ⟨x, hx⟩ :=
        K.pullbackQuotientHom_vertex_surjective Q y
      refine ⟨(K.pullbackQuotient Q).componentClass B x, ?_⟩
      change K.componentClass B ((K.pullbackQuotientHom Q).onVertex x) =
        K.componentClass B y
      rw [hx]

/-- Actual component-index transport is compatible with
the inclusion B⊆C of signed supported alphabets.
This is precisely the tag naturality required for
the ABO full multi-coset gluing relation. -/
theorem pullbackQuotient_componentIndexToBase_natural
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B C : Finset ι) (hBC : B ⊆ C)
    (c : (K.pullbackQuotient Q).ComponentIndex B) :
    K.pullbackQuotient_componentIndexToBase Q C
      ((K.pullbackQuotient Q).componentIndexMap B C hBC c) =
    K.componentIndexMap B C hBC
      (K.pullbackQuotient_componentIndexToBase Q B c) := by
  induction c using Quotient.inductionOn with
  | h x => rfl

/-- A point in the actual full G[B] coset indexed by an
intrinsic old G B-component maps into the corresponding
full H[B] coset tagged by its H component index. -/
theorem pullbackQuotient_componentAmbientCoset_map
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (c : (K.pullbackQuotient Q).ComponentIndex B)
    (g : Γ)
    (hg : g ∈ (K.pullbackQuotient Q).componentAmbientCoset B c) :
    Q.hom g ∈
      K.componentAmbientCoset B
        (K.pullbackQuotient_componentIndexToBase Q B c) := by
  induction c using Quotient.inductionOn with
  | h x =>
      change g ∈ generatedLeftCoset genΓ B x.1 at hg
      change Q.hom g ∈ generatedLeftCoset genΔ B (Q.hom x.1)
      exact Q.map_mem_generatedLeftCoset B x.1 g hg

/-- On every chosen indexed H full B-coset, every target
point has an upstairs preimage in the PARTICULAR
component-tagged source full G[B] coset. The source
component index is held fixed throughout. -/
theorem pullbackQuotient_componentAmbientCoset_surjective
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (c : (K.pullbackQuotient Q).ComponentIndex B)
    (h : Δ)
    (hh : h ∈ K.componentAmbientCoset B
      (K.pullbackQuotient_componentIndexToBase Q B c)) :
    ∃ g : Γ,
      g ∈ (K.pullbackQuotient Q).componentAmbientCoset B c ∧
      Q.hom g = h := by
  induction c using Quotient.inductionOn with
  | h x =>
      change h ∈ generatedLeftCoset genΔ B (Q.hom x.1) at hh
      exact Q.exists_generatedLeftCoset_preimage B x.1 h hh

/-- B-stability forces the whole group quotient to be
injective WITHIN ONE selected component-tagged G[B]
coset. Nothing here compares two different source tags. -/
theorem pullbackQuotient_componentAmbientCoset_injective
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (c : (K.pullbackQuotient Q).ComponentIndex B)
    {g h : Γ}
    (hg : g ∈ (K.pullbackQuotient Q).componentAmbientCoset B c)
    (hh : h ∈ (K.pullbackQuotient Q).componentAmbientCoset B c)
    (hEq : Q.hom g = Q.hom h) :
    g = h := by
  induction c using Quotient.inductionOn with
  | h x =>
      exact Q.injective_on_generatedLeftCoset_of_stableAt
        B hB x.1 hg hh hEq

/-- The FULL coset vertex fibre over one chosen original G
component tag is bijective with the full coset fibre over
its mapped H component tag. This is NOT the same thing as
claiming the full tagged disjoint unions are injective. -/
noncomputable def pullbackQuotient_componentAmbientCosetEquiv
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    (c : (K.pullbackQuotient Q).ComponentIndex B) :
    {g : Γ //
      g ∈ (K.pullbackQuotient Q).componentAmbientCoset B c} ≃
    {h : Δ //
      h ∈ K.componentAmbientCoset B
        (K.pullbackQuotient_componentIndexToBase Q B c)} := by
  apply Equiv.ofBijective
    (fun g : {g : Γ //
        g ∈ (K.pullbackQuotient Q).componentAmbientCoset B c} =>
      (⟨Q.hom g.1,
        K.pullbackQuotient_componentAmbientCoset_map Q B c g.1 g.2⟩ :
       {h : Δ //
         h ∈ K.componentAmbientCoset B
           (K.pullbackQuotient_componentIndexToBase Q B c)}))
  constructor
  · intro g h heq
    apply Subtype.ext
    exact K.pullbackQuotient_componentAmbientCoset_injective
      Q B hB c g.2 h.2 (congrArg Subtype.val heq)
  · intro h
    obtain ⟨g, hg, hmap⟩ :=
      K.pullbackQuotient_componentAmbientCoset_surjective
        Q B c h.1 h.2
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact hmap

/-- Concrete map of ACTUAL component-tagged attached
B-coset points, with BOTH the component index and group
value transported by the proper maps. No tag erasure. -/
noncomputable def pullbackQuotient_attachedCosetToBase
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) :
    (K.pullbackQuotient Q).AttachedCosetVertex B →
      K.AttachedCosetVertex B :=
  fun p =>
    ⟨K.pullbackQuotient_componentIndexToBase Q B p.1,
      ⟨Q.hom p.2.1,
        K.pullbackQuotient_componentAmbientCoset_map
          Q B p.1 p.2.1 p.2.2⟩⟩

/-- The actual ambient group coordinate transported by the
tagged B-coset map is precisely Q, not an arbitrary
representative or a new quotient identification. -/
@[simp] theorem pullbackQuotient_attachedCosetToBase_value
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B) :
    K.attachedValue B
      (K.pullbackQuotient_attachedCosetToBase Q B p) =
    Q.hom ((K.pullbackQuotient Q).attachedValue B p) :=
  rfl

/-- Transporting a genuine OLD skeleton point through its
tagged B-coset copy commutes exactly with the old-graph
quotient covering. Its real component tag is preserved. -/
theorem pullbackQuotient_attachedCosetToBase_skeleton
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι)
    (x : (K.pullbackQuotient Q).Vertex) :
    K.pullbackQuotient_attachedCosetToBase Q B
      ((K.pullbackQuotient Q).attachedOfSkeletonVertex B x) =
    K.attachedOfSkeletonVertex B
      ((K.pullbackQuotientHom Q).onVertex x) :=
  rfl

/-- A labelled group quotient cannot collapse two
points with the SAME genuine source B-component tag
when its restriction to G[B] is stable. This does NOT
compare points in different source components. -/
theorem pullbackQuotient_attachedCosetToBase_injective_same_index
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B : Finset ι) (hB : Q.StableAt B)
    {p q : (K.pullbackQuotient Q).AttachedCosetVertex B}
    (hIndex : p.1 = q.1)
    (hMap : K.pullbackQuotient_attachedCosetToBase Q B p =
      K.pullbackQuotient_attachedCosetToBase Q B q) :
    p = q := by
  have hqCoset :
      q.2.1 ∈ (K.pullbackQuotient Q).componentAmbientCoset B p.1 := by
    rw [hIndex]
    exact q.2.2
  have hGroup :
      p.2.1 = q.2.1 :=
    K.pullbackQuotient_componentAmbientCoset_injective
      Q B hB p.1 p.2.2 hqCoset
      (congrArg (K.attachedValue B) hMap)
  exact (K.pullbackQuotient Q).attachedValue_injective_of_same_index
    B hIndex hGroup

/-- A whole tagged B-coset copy is stable under alphabet
enlargement B⊆C: the component-index maps commute and
the physical group coordinate remains Q(g). -/
theorem pullbackQuotient_attachedCosetToBase_natural
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B C : Finset ι) (hBC : B ⊆ C)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B) :
    K.pullbackQuotient_attachedCosetToBase Q C
      ((K.pullbackQuotient Q).attachedSubalphabetMap B C hBC p) =
    K.attachedSubalphabetMap B C hBC
      (K.pullbackQuotient_attachedCosetToBase Q B p) := by
  apply K.attachedValue_injective_of_same_index C
  · exact K.pullbackQuotient_componentIndexToBase_natural
      Q B C hBC p.1
  · rfl

/-- A TRUE common original (B∩C)-component support
upstairs is always sent to a TRUE common (B∩C)-support
downstairs; the witness retains its intrinsic tag.
The converse is precisely NOT asserted here. -/
theorem pullbackQuotient_shareIntersectionSupport_forward
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (B C : Finset ι)
    (p : (K.pullbackQuotient Q).AttachedCosetVertex B)
    (q : (K.pullbackQuotient Q).AttachedCosetVertex C)
    (hShare : (K.pullbackQuotient Q).ShareIntersectionSupport
      B C p q) :
    K.ShareIntersectionSupport B C
      (K.pullbackQuotient_attachedCosetToBase Q B p)
      (K.pullbackQuotient_attachedCosetToBase Q C q) := by
  obtain ⟨r, hrp, hrq⟩ := hShare
  refine ⟨K.pullbackQuotient_attachedCosetToBase Q (B ∩ C) r, ?_, ?_⟩
  · calc
      K.attachedSubalphabetMap (B ∩ C) B
          Finset.inter_subset_left
          (K.pullbackQuotient_attachedCosetToBase Q (B ∩ C) r) =
        K.pullbackQuotient_attachedCosetToBase Q B
          ((K.pullbackQuotient Q).attachedSubalphabetMap (B ∩ C) B
            Finset.inter_subset_left r) :=
        (K.pullbackQuotient_attachedCosetToBase_natural
          Q (B ∩ C) B Finset.inter_subset_left r).symm
      _ = K.pullbackQuotient_attachedCosetToBase Q B p :=
        congrArg (K.pullbackQuotient_attachedCosetToBase Q B) hrp
  · calc
      K.attachedSubalphabetMap (B ∩ C) C
          Finset.inter_subset_right
          (K.pullbackQuotient_attachedCosetToBase Q (B ∩ C) r) =
        K.pullbackQuotient_attachedCosetToBase Q C
          ((K.pullbackQuotient Q).attachedSubalphabetMap (B ∩ C) C
            Finset.inter_subset_right r) :=
        (K.pullbackQuotient_attachedCosetToBase_natural
          Q (B ∩ C) C Finset.inter_subset_right r).symm
      _ = K.pullbackQuotient_attachedCosetToBase Q C q :=
        congrArg (K.pullbackQuotient_attachedCosetToBase Q C) hrq

end CayleySubgraphSpec
end ABO
end PSTSEPPA
