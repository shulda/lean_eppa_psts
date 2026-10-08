import PSTSEPPA.ABO.ClusterTransport
import PSTSEPPA.ABO.AugmentedClusterReflection

/-!
# Stability transport of augmented ABO clusters

The standard augmented cluster consists of the original cluster together with
one attached B-coset.  The labelled quotient respects both pieces.

The essential cross-piece injection argument is delegated to
`hom_reflects_generatedLeftCoset_on_cluster`: an image overlap between the
original cluster and the newly attached coset must already be an overlap in the
source.  Thus piecewise stability (including stability on B) implies a
labelled graph isomorphism, on vertices and on directed edge tokens.

This is the concrete graph form of ABO Lemma 3.14.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}

namespace LabelledGroupQuotient

variable (Q : LabelledGroupQuotient genΓ genΔ)

/-- The natural quotient map on an augmented cluster, with literally
corresponding edge tokens and unchanged signed labels. -/
noncomputable def augmentedClusterHom
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ) :
    LabelledGraphHom
      (P.augmentedToLabelledGraph genΓ B v)
      (P.augmentedToLabelledGraph genΔ B (Q.hom v)) where
  onVertex x :=
    ⟨Q.hom x.1, by
      rcases x.2 with hx | hx
      · rcases hx with ⟨C, hCP, hxC⟩
        exact Or.inl ⟨C, hCP, Q.hom_mem_generatedSubgroup C hxC⟩
      · exact Or.inr (Q.hom_mem_generatedLeftCoset B hx)⟩
  onEdge e :=
    ⟨(Q.hom e.1.1, e.1.2), by
      rcases e.2 with he | he
      · rcases he with ⟨C, hCP, hs, hl⟩
        exact Or.inl ⟨C, hCP, Q.hom_mem_generatedSubgroup C hs, hl⟩
      · exact Or.inr ⟨Q.hom_mem_generatedLeftCoset B he.1, he.2⟩⟩
  map_source e := by
    apply Subtype.ext
    rfl
  map_inv e := by
    apply Subtype.ext
    rcases e with ⟨⟨x, s⟩, he⟩
    cases s with
    | pos i =>
        change
          (Q.hom (x * genΓ i), PSTS.SignedLetter.neg i) =
            (Q.hom x * genΔ i, PSTS.SignedLetter.neg i)
        rw [map_mul, Q.map_gen]
    | neg i =>
        change
          (Q.hom (x * (genΓ i)⁻¹), PSTS.SignedLetter.pos i) =
            (Q.hom x * (genΔ i)⁻¹, PSTS.SignedLetter.pos i)
        rw [map_mul, map_inv, Q.map_gen]
  map_label e := rfl

@[simp]
theorem augmentedClusterHom_onVertex_val
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (x : P.AugmentedVertex genΓ B v) :
    ((Q.augmentedClusterHom P B v).onVertex x).1 = Q.hom x.1 :=
  rfl

@[simp]
theorem augmentedClusterHom_onEdge_val
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (e : P.AugmentedEdge genΓ B v) :
    ((Q.augmentedClusterHom P B v).onEdge e).1 =
      (Q.hom e.1.1, e.1.2) :=
  rfl

/-- The quotient is injective on the union of the original cluster and the
attached B-coset. The mixed cases use coset-reflection on cluster vertices. -/
theorem hom_injective_on_augmentedVertexSet
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hv : v ∈ P.VertexSet genΓ)
    (hgenΔ : IsGenerated genΔ) (hretΔ : Retractable genΔ)
    (hpieces : ∀ C ∈ P.pieces, Q.StableAt C)
    (hB : Q.StableAt B)
    {x y : Γ}
    (hx : x ∈ P.AugmentedVertexSet genΓ B v)
    (hy : y ∈ P.AugmentedVertexSet genΓ B v)
    (hxy : Q.hom x = Q.hom y) :
    x = y := by
  rcases hx with hxCluster | hxCoset
  · rcases hy with hyCluster | hyCoset
    · exact
        Q.hom_injective_on_clusterVertexSet
          P hgenΔ hretΔ hpieces hxCluster hyCluster hxy
    · have hxImage :
          Q.hom x ∈ generatedLeftCoset genΔ B (Q.hom v) := by
        rw [hxy]
        exact Q.hom_mem_generatedLeftCoset B hyCoset
      have hxCoset :=
        Q.hom_reflects_generatedLeftCoset_on_cluster
          P hgenΔ hretΔ hpieces hv hxCluster hxImage
      exact Q.hom_injective_on_generatedLeftCoset
        B hB hxCoset hyCoset hxy
  · rcases hy with hyCluster | hyCoset
    · have hyImage :
          Q.hom y ∈ generatedLeftCoset genΔ B (Q.hom v) := by
        rw [← hxy]
        exact Q.hom_mem_generatedLeftCoset B hxCoset
      have hyCoset :=
        Q.hom_reflects_generatedLeftCoset_on_cluster
          P hgenΔ hretΔ hpieces hv hyCluster hyImage
      exact Q.hom_injective_on_generatedLeftCoset
        B hB hxCoset hyCoset hxy
    · exact Q.hom_injective_on_generatedLeftCoset
        B hB hxCoset hyCoset hxy

/-- Full vertex bijectivity of the canonical augmented cluster morphism. -/
theorem augmentedClusterHom_vertex_bijective
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hv : v ∈ P.VertexSet genΓ)
    (hgenΔ : IsGenerated genΔ) (hretΔ : Retractable genΔ)
    (hpieces : ∀ C ∈ P.pieces, Q.StableAt C)
    (hB : Q.StableAt B) :
    Function.Bijective (Q.augmentedClusterHom P B v).onVertex := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact
      Q.hom_injective_on_augmentedVertexSet
        P B v hv hgenΔ hretΔ hpieces hB
        x.2 y.2 (congrArg Subtype.val hxy)
  · rintro ⟨y, hy⟩
    rcases hy with hyCluster | hyCoset
    · rcases hyCluster with ⟨C, hCP, hyC⟩
      rcases Q.exists_subgroup_preimage C hyC with ⟨x, hxC, hxy⟩
      refine ⟨⟨x, Or.inl ⟨C, hCP, hxC⟩⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    · have hyStep :
          (Q.hom v)⁻¹ * y ∈ generatedSubgroup genΔ B :=
        hyCoset
      rcases Q.exists_subgroup_preimage B hyStep with
        ⟨b, hbB, hbEq⟩
      have hvb :
          v * b ∈ generatedLeftCoset genΓ B v := by
        change v⁻¹ * (v * b) ∈ generatedSubgroup genΓ B
        simpa [mul_assoc] using hbB
      refine ⟨⟨v * b, Or.inr hvb⟩, ?_⟩
      apply Subtype.ext
      change Q.hom (v * b) = y
      calc
        Q.hom (v * b) = Q.hom v * Q.hom b := map_mul Q.hom v b
        _ = Q.hom v * ((Q.hom v)⁻¹ * y) := by rw [hbEq]
        _ = y := by simp [mul_assoc]

/-- Full directed-edge bijectivity. This handles overlapping edge sets and
formally inverse directed edges, including the trivial-generator cases. -/
theorem augmentedClusterHom_edge_bijective
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hv : v ∈ P.VertexSet genΓ)
    (hgenΔ : IsGenerated genΔ) (hretΔ : Retractable genΔ)
    (hpieces : ∀ C ∈ P.pieces, Q.StableAt C)
    (hB : Q.StableAt B) :
    Function.Bijective (Q.augmentedClusterHom P B v).onEdge := by
  constructor
  · intro e f hef
    apply Subtype.ext
    have hpair :
        (Q.hom e.1.1, e.1.2) =
          (Q.hom f.1.1, f.1.2) :=
      congrArg Subtype.val hef
    have hfirst : e.1.1 = f.1.1 :=
      Q.hom_injective_on_augmentedVertexSet
        P B v hv hgenΔ hretΔ hpieces hB
        (P.augmented_edge_source_mem genΓ B v e.2)
        (P.augmented_edge_source_mem genΓ B v f.2)
        (congrArg (fun p : Δ × SignedLabel ι => p.1) hpair)
    have hsecond : e.1.2 = f.1.2 :=
      congrArg (fun p : Δ × SignedLabel ι => p.2) hpair
    exact Prod.ext hfirst hsecond
  · rintro ⟨⟨y, s⟩, he⟩
    rcases he with heCluster | heCoset
    · rcases heCluster with ⟨C, hCP, hyC, hsC⟩
      rcases Q.exists_subgroup_preimage C hyC with
        ⟨x, hxC, hxy⟩
      refine ⟨⟨(x, s), Or.inl ⟨C, hCP, hxC, hsC⟩⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hxy
      · rfl
    · have hyStep :
          (Q.hom v)⁻¹ * y ∈ generatedSubgroup genΔ B :=
        heCoset.1
      rcases Q.exists_subgroup_preimage B hyStep with
        ⟨b, hbB, hbEq⟩
      have hvb :
          v * b ∈ generatedLeftCoset genΓ B v := by
        change v⁻¹ * (v * b) ∈ generatedSubgroup genΓ B
        simpa [mul_assoc] using hbB
      refine ⟨⟨(v * b, s), Or.inr ⟨hvb, heCoset.2⟩⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · change Q.hom (v * b) = y
        calc
          Q.hom (v * b) = Q.hom v * Q.hom b := map_mul Q.hom v b
          _ = Q.hom v * ((Q.hom v)⁻¹ * y) := by rw [hbEq]
          _ = y := by simp [mul_assoc]
      · rfl

/-- Labelled-graph form of ABO Lemma 3.14, with the exact stability hypotheses
on the constituent alphabets and on the attached coset alphabet. -/
theorem augmentedClusterHom_bijective_of_stablePieces
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hv : v ∈ P.VertexSet genΓ)
    (hgenΔ : IsGenerated genΔ) (hretΔ : Retractable genΔ)
    (hpieces : ∀ C ∈ P.pieces, Q.StableAt C)
    (hB : Q.StableAt B) :
    Function.Bijective (Q.augmentedClusterHom P B v).onVertex ∧
      Function.Bijective (Q.augmentedClusterHom P B v).onEdge :=
  ⟨Q.augmentedClusterHom_vertex_bijective
      P B v hv hgenΔ hretΔ hpieces hB,
    Q.augmentedClusterHom_edge_bijective
      P B v hv hgenΔ hretΔ hpieces hB⟩

/-- Source-facing rank formulation: if |A| = k, B is proper in A, and
the quotient is (k-1)-stable, then corresponding B-augmented A-clusters
are labelled-graph isomorphic. -/
theorem augmentedClusterHom_bijective_of_kStable
    {A : Finset ι} (P : ClusterSpec A)
    (B : Finset ι) (v : Γ)
    (hv : v ∈ P.VertexSet genΓ)
    (hgenΔ : IsGenerated genΔ) (hretΔ : Retractable genΔ)
    {k : Nat} (hcard : A.card = k) (hBproper : B ⊂ A)
    (hk : Q.KStable (k - 1)) :
    Function.Bijective (Q.augmentedClusterHom P B v).onVertex ∧
      Function.Bijective (Q.augmentedClusterHom P B v).onEdge := by
  apply Q.augmentedClusterHom_bijective_of_stablePieces
    P B v hv hgenΔ hretΔ
  · intro C hCP
    apply hk C
    have hlt : C.card < A.card :=
      Finset.card_lt_card (P.proper C hCP)
    rw [hcard] at hlt
    exact Nat.le_sub_one_of_lt hlt
  · apply hk B
    have hlt : B.card < A.card :=
      Finset.card_lt_card hBproper
    rw [hcard] at hlt
    exact Nat.le_sub_one_of_lt hlt

end LabelledGroupQuotient

end ABO
end PSTSEPPA
