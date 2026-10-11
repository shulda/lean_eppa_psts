# Human falsification audit: algebraic detector lifts do **not** replace geometric ABO stages
2026-10-11; authoritative mathematical warning; no new formal theorem.

## Exact counterexample (rank two, globally retractable ambient group)

Take the alphabet \(A=\{a,b\}\), the group
\[
\Gamma=C_2\times C_2=\langle a,b\mid a^2=b^2=1,\;ab=ba\rangle,
\]
and the **genuine incomplete** \(A\)-labelled Cayley skeleton
\[
K:\qquad 1 \xrightarrow{a} a \xrightarrow{b} ab
\]
together with the formal inverse edge tokens. Its vertex set is
\(\{1,a,ab\}\), and its two geometric edges are exactly those displayed.

1. **Retractability:** \(\Gamma\) is globally retractable, since erasing
   \(a\) or \(b\) is simply projection to the other \(C_2\) factor.
2. **Admissibility:** \(K\) is admissible under source Definition 3.16:
   \(|A|=2\), so this is a case of the Lean-certified theorem
   \`CayleySubgraphSpec.admissible_of_card_le_two\`.
3. **Full proper-alphabet coset extension:**
   - The \(b\)-component of original vertex \(1\) is a singleton,
     so attaching its full \(b\)-coset adds one vertex \(b_{\mathrm{left}}\)
     adjacent to \(1\) by a \(b\)-edge.
   - The \(a\)-component of original vertex \(ab\) is a singleton,
     so attaching its full \(a\)-coset adds one **distinct**
     vertex \(b_{\mathrm{right}}\) adjacent to \(ab\) by an \(a\)-edge.
   - Both have *ambient Cayley coordinate* \(b\), but they are not
     identified in ABO's gluing quotient (3.10): distinct tagged
     \(a\)- and \(b\)-coset points are identified only via an actual
     common \(\varnothing\)-component representative in the original
     skeleton, and \(b\notin K\). See Lean
     \`MultiCosetVertexQuotient.MultiCosetRawRelated\` and
     \`MultiCosetOverlap.ShareIntersectionSupport\`.
   - In total the extension has **five** vertices, not four.
4. **Distinct endpoints of equal group words:** starting at old \(1\),
   the true \(b\)-path ends at \(b_{\mathrm{left}}\) whereas the true
   \(aba\)-path ends at \(b_{\mathrm{right}}\). But
   \([aba]_\Gamma=[b]_\Gamma\).
   Hence the Cayley graph of \(\Gamma\) **cannot** cover the completed
   extension by a source-based labelled cover (it has only four
   vertices; more decisively, its equal group words would be forced
   to have equal endpoints, unlike the actual completed extension).
5. **The detector rank lift is powerless here:** for this already
   globally retractable generated \(\Gamma\), every coordinate
   \(\Gamma[B]\), with outside labels trivial, is a homomorphic image
   of \(\Gamma\). Thus the synchronized subgroup
   \(H_{k+1}\le \Gamma\times\prod_{|B|\le k}\Gamma[B]\)
   is the *graph of a homomorphism* and projects isomorphically onto
   \(\Gamma\) for every \(k\). In particular, its generator relations
   still include \(aba=b\), so it cannot cover this completed extension.

**Verified outside Lean as a tiny finite combinatorial check:** the
four singleton-alphabet intrinsic components of \(K\) are
\(\{1,a\}\) and \(\{ab\}\) for label \(a\), and \(\{1\}\) and
\(\{a,ab\}\) for label \(b\). Exactly two new tagged points are
added, each with ambient value \(b\), and they remain distinct.

## What this actually rules out

- It disproves the general shortcut **"the all-rank algebraic detector
  group plus ordinary Cayley pullbacks covers all required completed
  coset-extension stages"**. It does **not** disprove the corrected
  Auinger--Bitterlich--Otto theorem, ordinary PSTS EPPA, or our formal
  all-rank algebraic lemma #334.
- PR #331's factorization theorem requires **both** graphs already
  embedded as literal Cayley subgraphs. The problematic full coset
  extension need **not** be embedded, as the example demonstrates.
  Applying #331 to it prior to an embedding theorem would be circular.
- The literal pullback of \(K\) preserves ONLY existing signed edges;
  it cannot add the two genuinely different coset-extension vertices
  or their new \(a/b\)-edges. A pullback of the extension as an
  \`CayleySubgraphSpec\` is not even defined before embedding.
- No generic **surjectivity of connected factorization** can hold
  for arbitrary graph morphisms: the inclusion of one proper connected
  subgraph into a larger connected Cayley skeleton already fails.
  To establish component surjectivity, the input must satisfy
  actual local **edge-lifting/surjectivity** assumptions.

## What remains viable

- Corrected ABO's actual completed-stage transition groups can
  distinguish \(b\) from \(aba\). The rank-two three-family completed
  stages already formalized in the repository may detect this
  particular example. The counterexample does **not** show that
  their combined rank-two construction fails.
- The exact source Definition-5.3 family \(Z_k\) includes **plain**
  full coset extensions (\(B=\varnothing\)), as well as all prescribed
  augmentations. The theorem-4.7 argument needs labelled Cayley
  covers of their **trivial completions**, not just cover/pullback
  morphisms of the old input skeleton.
- The useful invariant to check HUMANLY, before deeper Lean, is:
  for every source-required completed stage \(T\), if the chosen new
  group is \(G\) then
  \[
    \ker(\mathrm{ev}_G)\subseteq\ker(\mathrm{wordValue}_T).
  \]
  Equality-of-value in \(G\) must imply equality of **actual**
  completed-stage word actions, including the words \(b\) and \(aba\)
  in this example. Merely \((k+1)\)-retractable and \(k\)-stable does
  not imply this arbitrary-stage kernel inclusion.
- Next risky test: compare the precise source Definition-5.3 index
  set \((A,\mathcal C_H,v,B)\), including \(B=\varnothing\), with
  the actual stage indices of our candidate construction; then
  check that EACH augmented stage's transition kernel is covered.
  At higher ranks, specifically test true bridge freeness and
  cluster-property propagation, NOT just algebraic word deletion.
  Fall back to the exact source \(Y_k/Z_k\) stage family if needed.

**Status:** decisive counterexample to a purported shortcut,
not to the source theorem. Avoid starting a Lean proof of the
invalid implication; do not mark source \(Y_k/Z_k\) completeness
or bridge freeness as proved by the existing algebra and
embedded-graph factorization modules.
