# Primary sources and provenance

Repository citations are pinned to the reviewed source or dependency revision. Direct declaration links in the chapter text identify the supporting statement. The [library bibliography](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/references.bib) is linked at the survey revision; inclusion there is not a claim that this review checked every cited paper. Mathematical attributions reported only from source annotations are identified as such in the chapters.

The private-transcript sources are described in [the extraction methods](development-history/methods.md); selected excerpts are included in the manual, while their bulk exports remain untracked. Public GitHub issues, PRs and CI runs are linked from [development history](development-history/index.md). Refetching mutable records is not an archive of their historical contents. Inaccessible sources and unavailable archives are identified below or in the relevant chapter.

<a id="alonmatiasszegedy99"></a>
## alonmatiasszegedy99

Noga Alon, Yossi Matias, Mario Szegedy. “The Space Complexity of Approximating the Frequency Moments.” *Journal of Computer and System Sciences* 58(1), 137–147, 1999; preliminary version in STOC 1996. https://doi.org/10.1006/jcss.1997.1545 . Author-hosted copy of the journal version: https://www.tau.ac.il/~nogaa/PDFS/amsz4.pdf . An independent agent review checked the theorem locators and statements (Theorem 2.2 for the `F₂` sketch, Proposition 3.1 for the `F∞` lower bound) against that copy on 2026-11-07 UTC. The JCSS page numbers were taken from secondary search summaries and were not checked against the typeset journal PDF.

<a id="alonyusterzwick1995"></a>
## alonyusterzwick1995

Noga Alon, Raphael Yuster, Uri Zwick. "Color-Coding." *Journal of the ACM* 42(4), 844–856, 1995. https://doi.org/10.1145/210332.210337 . Bibliographic data from the DOI record. The locator Lemma 3.1 (colorful paths by dynamic programming over color sets) was taken from secondary descriptions; the full text was not inspected in this pass.

<a id="barrett26"></a>
## barrett26

Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker and Sorrachai Yingchareonthawornchai. *CSLib: The Lean Computer Science Library*. arXiv:2602.04846v1, 2026. https://doi.org/10.48550/arXiv.2602.04846 . Author/title/version metadata checked against https://arxiv.org/abs/2602.04846 on 2026-11-02 UTC.

<a id="bcs16"></a>
## bcs16

Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner. *Interactive Oracle Proofs*. TCC 2016-B II, 31–60. https://doi.org/10.1007/978-3-662-53644-5_2 .

<a id="blum67"></a>
## blum67

Manuel Blum. *A Machine-Independent Theory of the Complexity of Recursive Functions*. Journal of the ACM 14(2), 322–336, 1967. https://doi.org/10.1145/321386.321395 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the two axioms, recursive relatedness and the speed-up theorem to this paper.

<a id="borodin72"></a>
## borodin72

Allan Borodin. *Computational Complexity and the Existence of Complexity Gaps*. Journal of the ACM 19(1), 158–174, 1972. https://doi.org/10.1145/321679.321691 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the gap theorem and the almost-everywhere class convention to this paper.

<a id="bs23"></a>
## bs23

Dan Boneh and Victor Shoup. *A Graduate Course in Applied Cryptography*, version 0.6, January 2023. https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf . Title, authors and edition verified from the primary PDF during independent source review on 2026-11-02. Detailed textbook locator claims remain attributed to the Lean source docstrings; no complete textbook correspondence audit was performed.

<a id="bt06"></a>
## bt06

Andrej Bogdanov and Luca Trevisan. *Average-Case Complexity*. Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006. https://doi.org/10.1561/0400000004 ; arXiv:cs/0606037. Definition, lemma and theorem numbers (Definitions 1, 2, 6, 8–11 and 17, Proposition 7, Lemma 18, Theorem 19, Claim 20) were checked against the arXiv text on 2026-11-07.

<a id="canetti20"></a>
## canetti20

Ran Canetti. *Universally Composable Security*. Journal of the ACM 67(5), Article 28, 2020; full version Cryptology ePrint Archive 2000/067. https://doi.org/10.1145/3402457 .

<a id="cks20"></a>
## cks20

Clément L. Canonne, Gautam Kamath and Thomas Steinke. *The Discrete Gaussian for Differential Privacy*. NeurIPS 2020; cited from arXiv:2004.00010v5, 2021. https://arxiv.org/abs/2004.00010 . Definition 28 and Lemmas 29–30 were checked against the arXiv v5 PDF on 2026-11-07.

<a id="clrs09"></a>
## clrs09

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest and Clifford Stein. *Introduction to Algorithms*, third edition. MIT Press, 2009. ISBN 978-0-262-03384-8. Section 35.1, procedure `APPROX-VERTEX-COVER` and Theorem 35.1 (it is a polynomial-time 2-approximation algorithm). The locator was checked against secondary course material, not the printed book.

<a id="complexitylib"></a>
## complexitylib

Complexitylib contributors. *Complexitylib*, source snapshot `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. [Pinned repository](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8). Individual declarations are linked in the text. The repository bibliography records mathematical sources; attribution here reports those source annotations unless independent verification is explicitly stated.

<a id="cookmertz24"></a>
## cookmertz24

James Cook and Ian Mertz. *Tree Evaluation is in Space O(log n · log log n)*. STOC 2024; full report ECCC TR23-174 (15 November 2023). https://eccc.weizmann.ac.il/report/2023/174/ .

<a id="cookreckhow73"></a>
## cookreckhow73

Stephen A. Cook, Robert A. Reckhow. “Time Bounded Random Access Machines.” *Journal of Computer and System Sciences* 7(4), 354–375, 1973. https://doi.org/10.1016/S0022-0000(73)80029-7 . Local source explicitly labels its adaptation; publisher fetch unavailable in this pass.

<a id="cormode05"></a>
## cormode05

Graham Cormode, S. Muthukrishnan. “An Improved Data Stream Summary: The Count-Min Sketch and its Applications.” *Journal of Algorithms* 55(1), 58–75, 2005. https://doi.org/10.1016/j.jalgor.2003.12.001 ; author PDF https://www.cs.ox.ac.uk/people/graham.cormode/pubs/papers/cm-full.pdf . Sections 3–4.1 and fixed point-query guarantee consulted.

<a id="cslib"></a>
## cslib

CSLib contributors. *CSLib*, pinned dependency snapshot `254e30e6d4299c51323aaeaf5f51a4763b375d4a`. [Pinned repository](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a).

<a id="cygan2015"></a>
## cygan2015

Marek Cygan, Fedor V. Fomin, Łukasz Kowalik, Daniel Lokshtanov, Dániel Marx, Marcin Pilipczuk, Michał Pilipczuk, and Saket Saurabh. *Parameterized Algorithms*. Springer, 2015. [DOI](https://doi.org/10.1007/978-3-319-21275-3). Inspected the authors' companion PDF dated 2016-05-30: Definitions 1.2–1.3 (p. 13), Definition 2.1 (pp. 18–19), Lemma 2.2 (p. 20), and Section 2.2.1 (pp. 21–22); accessed 2026-11-02. The color-coding locators Section 5.2 and Lemma 5.5, and the fpt-reduction locator Section 13.1, used in [parameterized complexity](machines-and-classes/parameterized-complexity.md), were not re-inspected.

<a id="dinur2007"></a>
## dinur2007

Irit Dinur. “The PCP Theorem by Gap Amplification.” *Journal of the ACM* 54(3), Article 12 (2007). DOI: https://doi.org/10.1145/1236457.1236459. Author copy dated 2007-02-13 inspected: https://www.wisdom.weizmann.ac.il/~dinuri/mypapers/combpcp.pdf (opening definition and Theorem 1.1).

<a id="dworkroth14"></a>
## dworkroth14

Cynthia Dwork and Aaron Roth. *The Algorithmic Foundations of Differential Privacy*. Foundations and Trends in Theoretical Computer Science 9(3–4), 211–407, 2014. https://doi.org/10.1561/0400000042 . Definition 2.4, Proposition 2.1, Theorem 2.2 and its footnote, §2.3, Claim 3.5, Theorem 3.16, Theorem B.1 and Corollary B.2 were checked against the published PDF on 2026-11-07.

<a id="erickson24"></a>
## erickson24

Jeff Erickson, Ivor van der Hoog, Tillmann Miltzow. “Smoothing the Gap Between NP and ∃R.” *SIAM Journal on Computing* 53(6), FOCS20-102–FOCS20-138, 2024. https://doi.org/10.1137/20M1385287 . Author preprint consulted: https://arxiv.org/abs/1912.02278v3 , §6.1. Published metadata comes from the pinned bibliography; the consulted preprint is dated 2021.

<a id="fly22"></a>
## fly22

Zhiyuan Fan, Jiatu Li, and Tianqi Yang. *The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity*. Electronic Colloquium on Computational Complexity (ECCC), Report TR21-125, Revision 1 (12 June 2022), https://eccc.weizmann.ac.il/report/2021/125/ ; conference version in *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 962–975, https://doi.org/10.1145/3519935.3520010 . Inspected ECCC TR21-125 Revision 1 PDF directly: Section 4.1 (pp. 24–26), Section 4.2, Definitions 4.3–4.5 (pp. 26–27), Section 4.4, Definition 4.9 (p. 28), Section 7.1, Definition 7.1, Lemmas 7.2–7.4, and Theorem 7.5 (pp. 39–41), and Section 7.2 (pp. 41–42).

<a id="gentry09"></a>
## gentry09

Craig Gentry. “Fully Homomorphic Encryption Using Ideal Lattices.” *STOC 2009*, 169–178. https://doi.org/10.1145/1536414.1536440 . Bibliographic data and theorem locator taken from the pinned repository; full text not independently re-audited here.

<a id="ggm86"></a>
## ggm86

Oded Goldreich, Shafi Goldwasser, Silvio Micali. “How to Construct Random Functions.” *Journal of the ACM* 33(4), 792–807, 1986. Author-hosted version of record: https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf . Adaptive function-test definition consulted.

<a id="gkr15"></a>
## gkr15

Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum. *Delegating Computation: Interactive Proofs for Muggles*. JACM 62(4), article 27, 2015. https://doi.org/10.1145/2699436 .

<a id="goldreich-tree24"></a>
## goldreich-tree24

Oded Goldreich. *On the Cook–Mertz Tree Evaluation procedure*. ECCC TR24-109, revision 2 (27 December 2024). https://eccc.weizmann.ac.il/report/2024/109/ .

<a id="goldreich04"></a>
## goldreich04

Oded Goldreich. *Foundations of Cryptography, Volume 2: Basic Applications*. Cambridge University Press, 2004. https://doi.org/10.1017/CBO9780511721656 . Author's chapter listing and draft availability: https://www.wisdom.weizmann.ac.il/~oded/foc-vol2.html . Author page checked; the full published chapter was not independently audited here.

<a id="grs12"></a>
## grs12

Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan. *Universally Utility-Maximizing Privacy Mechanisms*. SIAM Journal on Computing 41(6), 1673–1693, 2012; conference version STOC 2009. https://doi.org/10.1137/09076828X . §2.1 and Example 2.1 were checked against arXiv:0811.2841v3 on 2026-11-07.

<a id="gsw13"></a>
## gsw13

Craig Gentry, Amit Sahai, Brent Waters. “Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based.” *CRYPTO 2013*, LNCS 8042, 75–92. https://doi.org/10.1007/978-3-642-40041-4_5 ; authors' full-version record https://eprint.iacr.org/2013/340 . Metadata/abstract checked; PDF fetch was blocked in this source pass.

<a id="hennie1965"></a>
## hennie1965

F. C. Hennie. “One-tape, off-line Turing machine computations.” *Information and Control* 8(6), 553–578, 1965. https://doi.org/10.1016/S0019-9958(65)90399-2 . Bibliographic metadata checked; the article body was not inspected in this pass, so the manual cites it for the crossing-sequence method and not for a numbered statement.

<a id="henson26"></a>
## henson26

Christopher Henson and Fabrizio Montesi. *Computer Science as Infrastructure: the Spine of the Lean Computer Science Library (CSLib)*. EPTCS 449 (LSFA 2026), pp. 141–148, 2026. https://doi.org/10.4204/EPTCS.449.9 . Version-of-record metadata verified through https://arxiv.org/abs/2602.15078v2 on 2026-11-02 UTC; DOI resolver was unavailable in this research environment.

<a id="hhrvw20"></a>
## hhrvw20

Iftach Haitner, Thomas Holenstein, Omer Reingold, Salil Vadhan, Hoeteck Wee. “Inaccessible Entropy II: IE Functions and Universal One-Way Hashing.” *Theory of Computing* 16(8), 1–55, 2020. https://doi.org/10.4086/toc.2020.v016a008 . Open-access article PDF inspected (Section 3, Definitions 3.1, 3.3, 3.9, pp. 11–15; Section 4.2, Theorem 4.5 and Claims 4.6–4.8, pp. 21–25, adapted to a constant light-image threshold with inverse-linear gap `1 / (64 * (n + 1))`; and Section 5.1, Theorem 5.1, Lemmas 5.3–5.7, and Section 5.1.5 STEPS 1–5, pp. 25–32).

<a id="hill99"></a>
## hill99

Johan Håstad, Russell Impagliazzo, Leonid A. Levin, Michael Luby. “A Pseudorandom Generator from Any One-Way Function.” *SIAM Journal on Computing* 28(4), 1364–1396, 1999. https://doi.org/10.1137/S0097539793244708 . Publisher abstract checked; full article not independently audited.

<a id="holenstein06"></a>
## holenstein06

Thomas Holenstein. “Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness.” *TCC 2006*. Author PDF: https://crypto.ethz.ch/publications/files/Holens06.pdf . Definitions and construction overview consulted.

<a id="holenstein09"></a>
## holenstein09

Thomas Holenstein. “Parallel Repetition: Simplifications and the No-Signaling Case.” *Theory of Computing* 5(8), 141–172, 2009. https://doi.org/10.4086/toc.2009.v005a008 . Journal PDF inspected (Definition 2.4 and Theorem 2.5, p. 146; Definition 5.1, p. 151; Lemma 5.4 and (5.5), p. 153; Claims 6.2 and 6.3, p. 154; Lemma 6.4 and (6.3)–(6.7) of its proof, p. 155; (6.8)–(6.16), p. 156; the first stage of the embedding, from (6.15) and (6.16) by Corollary 5.3, (6.17)–(6.19) and the second stage, and Lemma 6.5, (6.20) and its proof, p. 157; Lemma 7.1, p. 158; the proof of Theorem 2.5, (7.6) and (7.7), p. 159).

<a id="immerman1988"></a>
## immerman1988

Neil Immerman. “Nondeterministic Space Is Closed under Complementation.” *SIAM Journal on Computing* 17(5), 935–938 (1988). DOI: https://doi.org/10.1137/0217058. Author copy inspected: https://people.cs.umass.edu/~immerman/pub/space.pdf (Theorem 1; inspected 2026-11-01).

<a id="impagliazzo01"></a>
## impagliazzo01

Russell Impagliazzo and Ramamohan Paturi. *On the Complexity of k-SAT*. Journal of Computer and System Sciences 62(2), 367–375, 2001. DOI: [10.1006/jcss.2000.1727](https://doi.org/10.1006/jcss.2000.1727). [Author-hosted copy](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturi_2001_jcss.pdf). Publisher metadata and abstract checked 2026-11-02; cited for the historical exponent-based hypothesis, not for the 2026 result.

<a id="impagliazzowigderson97"></a>
## impagliazzowigderson97

Russell Impagliazzo and Avi Wigderson. *P = BPP if E Requires Exponential Circuits: Derandomizing the XOR Lemma*. Proceedings of the 29th Annual ACM Symposium on Theory of Computing, 220–229, 1997. DOI: [10.1145/258533.258590](https://doi.org/10.1145/258533.258590). ACM metadata checked by the coordinated source pass on 2026-11-02; no complete literature proof audit is asserted.

<a id="katzlindell20"></a>
## katzlindell20

Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd edition. CRC Press, 2020. Bibliographic metadata and section titles checked against the authors' 3rd-edition table of contents and preface: https://www.cs.umd.edu/~jkatz/imc/toc-preface-3rd.pdf (Sections 9.2.3–9.2.4 on the factoring and RSA assumptions; Section 15.1.1 on trapdoor permutations; Section 15.2 on Paillier encryption; Sections 15.4.1–15.4.3 on quadratic residues and the quadratic residuosity assumption; and Sections 15.5.1–15.5.2 on modular square roots and the Rabin trapdoor permutation). Detailed numbered locators (Definitions, Claims, Propositions, Lemmas, Constructions, Examples, Exercises, and Theorems) remain attributed to the Lean source docstrings, as the textbook body was not independently audited; the Lean modules adapt the parameter generators, RSA challenge domain, Rabin sampling distribution, and the Paillier encryption-randomness sampler (dyadic sampling with `unitOrOne` in place of uniform `ℤ_N^*`) as documented in their module docstrings and implementation notes.

<a id="lean-validation"></a>
## lean-validation

Lean development team. *Validating a Lean Proof*, The Lean Language Reference, accessed 2026-11-02 UTC. https://lean-lang.org/doc/reference/latest/ValidatingProofs/ . The page was inspected live; the requested version-specific URL was unavailable, and no verified archival snapshot was obtained. Version-specific library assertions in this dossier instead rely on pinned repository sources.

<a id="lfkn92"></a>
## lfkn92

Carsten Lund, Lance Fortnow, Howard Karloff and Noam Nisan. *Algebraic Methods for Interactive Proof Systems*. JACM 39(4), 859–868, 1992. https://doi.org/10.1145/146585.146605 .

<a id="liupass20"></a>
## liupass20

Yanyi Liu and Rafael Pass. *On One-way Functions and Kolmogorov Complexity*. FOCS 2020, 1243–1254. https://doi.org/10.1109/FOCS46700.2020.00118 . Definition/theorem locators refer to the full version https://arxiv.org/abs/2009.11514v1 , §§2.3 and 3, pp. 8–9.

<a id="mathlib"></a>
## mathlib

Mathlib contributors. *Mathlib*, pinned source `69552756cd8a2d2d48763cf7279fd814d6a1224d`, inspected 2026-11-01. https://github.com/leanprover-community/mathlib4/tree/69552756cd8a2d2d48763cf7279fd814d6a1224d

<a id="monderershapley96"></a>
## monderershapley96

Dov Monderer and Lloyd S. Shapley. *Potential Games*. Games and Economic Behavior 14(1), 124–143, 1996. https://doi.org/10.1006/game.1996.0044 . The published text was consulted on 2026-11-07 for the definitions (2.1)–(2.3), Lemmas 2.1, 2.3, 2.5 and 2.7, Corollary 2.2, Theorem 3.1 and footnote 12.

<a id="naoryung89"></a>
## naoryung89

Moni Naor and Moti Yung. “Universal One-Way Hash Functions and their Cryptographic Applications.” *Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989)*, 33–43, 1989. https://doi.org/10.1145/73007.73011 . Authors' revised manuscript (March 13, 1995): https://www.wisdom.weizmann.ac.il/~naor/PAPERS/uowhf.ps (§2, §2.3, §3 and §4).

<a id="nisanwigderson94"></a>
## nisanwigderson94

Noam Nisan and Avi Wigderson. *Hardness vs Randomness*. Journal of Computer and System Sciences 49(2), 149–167, 1994. DOI: [10.1016/S0022-0000(05)80043-1](https://doi.org/10.1016/S0022-0000(05)80043-1). Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; this section's source-to-proof description follows the pinned Lean documentation.

<a id="openai-logspace26"></a>
## openai-logspace26

OpenAI. *Exact Derandomization of Logarithmic Space: L = RL = BPL*. Preprint, 23 September 2026, not peer reviewed; cited here only for construction provenance. Accompanying Lean file at revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/CatalyticComparison.lean .

<a id="openaieth26"></a>
## openaieth26

OpenAI. *The Exponential Time Hypothesis is False*. Manuscript dated 17 October 2026, revised 25 October 2026. Source revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. [PDF](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf); [primary TeX](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex). The interpolation-route statement, metadata and label were checked in freshly retrieved TeX on 2026-11-02; full proof and PDF pagination were not independently audited.

<a id="reingold2008"></a>
## reingold2008

Omer Reingold. “Undirected Connectivity in Log-Space.” *Journal of the ACM* 55(4), Article 17 (2008). DOI: https://doi.org/10.1145/1391289.1391291. Author copy dated 2008-05-03 inspected: https://omereingold.wordpress.com/wp-content/uploads/2014/10/sl.pdf.

<a id="reynolds02"></a>
## reynolds02

John C. Reynolds. “Separation Logic: A Logic for Shared Mutable Data Structures.” *LICS 2002*, 55–74. https://doi.org/10.1109/LICS.2002.1029817 ; author PDF https://www.cs.cmu.edu/~jcr/seplogic.pdf . The standard locality/separating-conjunction principle was consulted; the local finite-support model is an adaptation.

<a id="rompel90"></a>
## rompel90

John Rompel. “One-Way Functions are Necessary and Sufficient for Secure Signatures.” *Proceedings of the Twenty-Second Annual ACM Symposium on Theory of Computing (STOC 1990)*, 387–394, 1990. https://doi.org/10.1145/100216.100269 . Bibliographic metadata checked against the repository bibliography; the formalization establishes universal one-way hashing via the inaccessible-entropy construction of [hhrvw20](#hhrvw20) rather than Rompel's original construction, and the ACM full text was not directly inspected in this pass.

<a id="rosenthal73"></a>
## rosenthal73

Robert W. Rosenthal. *A Class of Games Possessing Pure-Strategy Nash Equilibria*. International Journal of Game Theory 2(1), 65–67, 1973. https://doi.org/10.1007/BF01737559 . Bibliographic metadata checked on 2026-11-07; the potential-function theorem is attributed as cited in Monderer–Shapley, Theorem 3.1.

<a id="roughgarden13cs364a"></a>
## roughgarden13cs364a

Tim Roughgarden. *CS364A: Algorithmic Game Theory*, lecture notes, Stanford University, Fall 2013. https://theory.stanford.edu/~tim/f13/f13.html . Lecture #17, "No-Regret Dynamics" (18 November 2013), was consulted on 2026-11-07 for Definition 1.2, §3, Proposition 3.1, Remark 3.2 and Corollary 3.3.

<a id="roughgarden15"></a>
## roughgarden15

Tim Roughgarden. *Intrinsic Robustness of the Price of Anarchy*. Journal of the ACM 62(5), Article 32, 2015. https://doi.org/10.1145/2806883 . The author's version of 14 July 2015 was consulted on 2026-11-07 for Definition 2.1, derivation (3)–(5), Example 2.5, (15) and Theorems 3.2–3.3; locators follow that version.

<a id="roughgardentardos02"></a>
## roughgardentardos02

Tim Roughgarden and Éva Tardos. *How Bad Is Selfish Routing?* Journal of the ACM 49(2), 236–259, 2002. https://doi.org/10.1145/506147.506153 . The author's version of 5 December 2001 was consulted on 2026-11-07 for Section 2.1, Definition 2.1, Lemma 2.2, Theorem 4.5 and Figure 3; locators follow that version.

<a id="shamir1992"></a>
## shamir1992

Adi Shamir. “IP = PSPACE.” *Journal of the ACM* 39(4), 869–877 (1992). DOI: https://doi.org/10.1145/146585.146609. Original-paper scan inspected: https://crypto.cs.mcgill.ca/~crepeau/COMP647/2007/TOPIC01/Shamir-IP=PSPACE.pdf.

<a id="sleatortarjan85"></a>
## sleatortarjan85

Daniel D. Sleator, Robert E. Tarjan. “Amortized Efficiency of List Update and Paging Rules.” *Communications of the ACM* 28(2), 202–208, 1985. https://doi.org/10.1145/2786.2793 ; author PDF https://www.cs.cmu.edu/~sleator/papers/amortized-efficiency.pdf . Paging scope and equal-capacity specialization checked against source and local mapping.

<a id="sudantrevisanvadhan01"></a>
## sudantrevisanvadhan01

Madhu Sudan, Luca Trevisan and Salil Vadhan. *Pseudorandom Generators without the XOR Lemma*. Journal of Computer and System Sciences 62(2), 236–266, 2001. DOI: [10.1006/jcss.2000.1730](https://doi.org/10.1006/jcss.2000.1730). Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; the proof-route attribution comes from the pinned Lean module.

<a id="thaler22"></a>
## thaler22

Justin Thaler. *Proofs, Arguments, and Zero-Knowledge*. Foundations and Trends in Privacy and Security 4(2–4), 117–660, 2022. https://doi.org/10.1561/3300000030 . Later author manuscript consulted: https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf , dated 18 July 2023, §§4.1, 4.6.

<a id="thorup13"></a>
## thorup13

Mikkel Thorup. “Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence.” *FOCS 2013*, 90–99. https://doi.org/10.1109/FOCS.2013.18 ; author preprint https://arxiv.org/abs/1311.3121v2 . Bibliographic record checked; the formalization's quantitative adaptation is grounded in the pinned abstract and library source.

<a id="toda1991"></a>
## toda1991

Seinosuke Toda. “PP Is as Hard as the Polynomial-Time Hierarchy.” *SIAM Journal on Computing* 20(5), 865–877 (1991). Publisher abstract inspected 2026-11-01: https://doi.org/10.1137/0220053.

<a id="williams25"></a>
## williams25

R. Ryan Williams. *Simulating Time With Square-Root Space*. arXiv:2502.17779v1 (25 February 2025), Appendix A, equation (6); version states to appear in STOC 2025. https://arxiv.org/abs/2502.17779v1 .

<a id="williamsonshmoys11"></a>
## williamsonshmoys11

David P. Williamson and David B. Shmoys. *The Design of Approximation Algorithms*. Cambridge University Press, 2011. https://doi.org/10.1017/CBO9780511921735 . Section 1.6 (Algorithm 1.2, Theorems 1.11 and 1.12) and the Chapter 1 Chapter Notes attribution of the greedy set-cover analysis to Chvátal (Mathematics of Operations Research 4(3), 233–235, 1979, https://doi.org/10.1287/moor.4.3.233) were checked against the authors' electronic edition at https://www.designofapproxalgs.com on 2026-11-07, as were Section 2.4 (Lemma 2.10, Theorems 2.11 and 2.12) and the Chapter 2 Chapter Notes, which attribute nearest addition and its analysis to Rosenkrantz, Stearns and Lewis (1977) and call the double-tree algorithm folklore.
