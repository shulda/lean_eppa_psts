import PSTSEPPA.ABO.CayleySubgraphComponents
import PSTSEPPA.ABO.AugmentedCluster

/-!
# Realising full-coset paths inside arbitrary Cayley subgraphs

ABO's cluster/component calculations often identify a *literal* full
subalphabet coset together with all its signed Cayley edges. An equality of
ambient group cosets is not itself a proof of graph connectivity: this
file supplies the missing path-lifting theorem.

If a Cayley skeleton K includes every D-labelled directed edge whose
source lies in gG[D], then every D-supported group word can actually be
followed inside K from any vertex of that coset. Consequently any
two skeleton vertices inside that full coset are genuinely D-connected.

The proof does not require retractability, group generation, injectivity
of any ambient projection, or a choice of coset representative.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

open ClusterSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every D-supported word can be realised by actual edges of K
inside an ambient D-coset all of whose D-edges lie in K.
The endpoint is the exact group word evaluation, not merely a
point with the same ambient D-component. -/
theorem follows_word_in_fullCoset
    (D : Finset ι) (g : Γ)
    (hfull : ∀ e : ActionEdge Γ ι,
      e ∈ FullCosetEdgeSet gen D g → e ∈ K.edges)
    (x : K.Vertex) (hx : x.1 ∈ generatedLeftCoset gen D g)
    (w : LabelWord ι) (hw : LabelWord.Uses D w) :
    ∃ y : K.Vertex,
      (K.toEGraph).Follows x w y ∧
      y.1 = x.1 * PSTS.SignedWord.evalGroup gen w := by
  induction w generalizing x with
  | nil =>
      exact ⟨x, EGraph.Follows.nil x, by simp⟩
  | cons s w ih =>
      let edge : ActionEdge Γ ι := (x.1, s)
      have hedge : edge ∈ K.edges :=
        hfull edge ⟨hx, hw.1⟩
      let next : K.Vertex :=
        ⟨(cayleyGraph gen).target edge, K.target_mem hedge⟩
      have hnext : next.1 ∈ generatedLeftCoset gen D g :=
        fullCosetEdge_target_mem gen D g ⟨hx, hw.1⟩
      obtain ⟨y, hpath, hvalue⟩ := ih next hnext hw.2
      refine ⟨y, ?_, ?_⟩
      · exact EGraph.Follows.cons ⟨edge, hedge⟩
          (by apply Subtype.ext; rfl) rfl hpath
      · calc
          y.1 = next.1 * PSTS.SignedWord.evalGroup gen w := hvalue
          _ = (x.1 * PSTS.SignedWord.evalGroupLetter gen s) *
                PSTS.SignedWord.evalGroup gen w := by
                  change (cayleyGraph gen).target (x.1, s) *
                    PSTS.SignedWord.evalGroup gen w =
                      (x.1 * PSTS.SignedWord.evalGroupLetter gen s) *
                        PSTS.SignedWord.evalGroup gen w
                  rw [cayleyGraph.target_eq_mul_evalGroupLetter]
          _ = x.1 * PSTS.SignedWord.evalGroup gen (s :: w) := by
                  simp [PSTS.SignedWord.evalGroup, mul_assoc]

/-- A full D-coset contained in a Cayley skeleton is genuinely
D-path-connected. Both endpoints must be literal skeleton vertices;
no ambient-coset injectivity or graph completeness elsewhere is used. -/
theorem reachable_in_fullCoset
    (D : Finset ι) (g : Γ)
    (hfull : ∀ e : ActionEdge Γ ι,
      e ∈ FullCosetEdgeSet gen D g → e ∈ K.edges)
    (x y : K.Vertex)
    (hx : x.1 ∈ generatedLeftCoset gen D g)
    (hy : y.1 ∈ generatedLeftCoset gen D g) :
    K.SubalphabetReachable D x y := by
  have hcoset :
      generatedLeftCoset gen D g =
        generatedLeftCoset gen D x.1 :=
    generatedLeftCoset_eq_of_mem gen D hx
  have hyx : y.1 ∈ generatedLeftCoset gen D x.1 := by
    rw [← hcoset]
    exact hy
  have hdiff : x.1⁻¹ * y.1 ∈ generatedSubgroup gen D := hyx
  obtain ⟨w, hw, heval⟩ :=
    exists_word_uses_eq_of_mem_generatedSubgroup gen D hdiff
  obtain ⟨z, hpath, hvalue⟩ :=
    K.follows_word_in_fullCoset D g hfull x hx w hw
  have hzy : z = y := by
    apply Subtype.ext
    calc
      z.1 = x.1 * PSTS.SignedWord.evalGroup gen w := hvalue
      _ = x.1 * (x.1⁻¹ * y.1) := by rw [heval]
      _ = y.1 := by simp [mul_assoc]
  exact ⟨w, hw, hzy ▸ hpath⟩

end CayleySubgraphSpec
end ABO
end PSTSEPPA
