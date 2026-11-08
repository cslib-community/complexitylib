# Primary sources and provenance

Repository citations are pinned to the reviewed source or dependency revision. Direct declaration links in the chapter text identify the supporting statement. The [library bibliography](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/references.bib) is linked at the survey revision; inclusion there is not a claim that this review checked every cited paper. Mathematical attributions reported only from source annotations are identified as such in the chapters.

The private-transcript sources are described in [the extraction methods](development-history/methods.md); selected excerpts are included in the manual, while their bulk exports remain untracked. Public GitHub issues, PRs and CI runs are linked from [development history](development-history/index.md). Refetching mutable records is not an archive of their historical contents. Inaccessible sources and unavailable archives are identified below or in the relevant chapter.

<a id="aaronson20"></a>
## aaronson20

Scott Aaronson. *The Busy Beaver Frontier*. ACM SIGACT News 51(3), 32–54, 2020. https://doi.org/10.1145/3427361.3427369 ; author's version https://www.scottaaronson.com/papers/bb.pdf . Read in the author's version on 2026-11-08: Proposition 1 (oracle access to any upper bound on the shift function solves the halting problem, hence no such bound is computable; the library proves the unrelativized corollary) and Proposition 2 (the shift function eventually exceeds every computable function). Both are stated for Turing machines; Section 2 notes that they hold in any universal model of computation. Section 1 defines `BB_L` for a programming language `L` with bit-string programs (and a variant through Kolmogorov complexity), the closest analogue of the library's code-size version. Journal pagination was taken from the bibliographic record.

<a id="alonmatiasszegedy99"></a>
## alonmatiasszegedy99

Noga Alon, Yossi Matias, Mario Szegedy. “The Space Complexity of Approximating the Frequency Moments.” *Journal of Computer and System Sciences* 58(1), 137–147, 1999; preliminary version in STOC 1996. https://doi.org/10.1006/jcss.1997.1545 . Author-hosted copy of the journal version: https://www.tau.ac.il/~nogaa/PDFS/amsz4.pdf . An independent agent review checked the theorem locators and statements (Theorem 2.2 for the `F₂` sketch, Proposition 3.1 for the `F∞` lower bound) against that copy on 2026-11-07 UTC. The JCSS page numbers were taken from secondary search summaries and were not checked against the typeset journal PDF.

<a id="alonyusterzwick1995"></a>
## alonyusterzwick1995

Noga Alon, Raphael Yuster, Uri Zwick. "Color-Coding." *Journal of the ACM* 42(4), 844–856, 1995. https://doi.org/10.1145/210332.210337 . Bibliographic data from the DOI record. The locator Lemma 3.1 (colorful paths by dynamic programming over color sets) was taken from secondary descriptions; the full text was not inspected in this pass.

<a id="barrett26"></a>
## barrett26

Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker and Sorrachai Yingchareonthawornchai. *CSLib: The Lean Computer Science Library*. arXiv:2602.04846v1, 2026. https://doi.org/10.48550/arXiv.2602.04846 . Author/title/version metadata checked against https://arxiv.org/abs/2602.04846 on 2026-11-02 UTC.

<a id="bcgl92"></a>
## bcgl92

Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby. *On the Theory of Average Case Complexity*. Journal of Computer and System Sciences 44(2), 193–219, 1992; preliminary version in STOC 1989. https://doi.org/10.1016/0022-0000(92)90019-F . Bibliographic metadata checked against the Crossref record on 2026-11-08. The primary text was not inspected, and no theorem number is claimed. The manual attributes to this paper only the implication `DistNP ⊆ AvgP ⇒ NE = E`, as reported by [bm15](#bm15), §5.

<a id="bcs16"></a>
## bcs16

Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner. *Interactive Oracle Proofs*. TCC 2016-B II, 31–60. https://doi.org/10.1007/978-3-662-53644-5_2 .

<a id="bellman58"></a>
## bellman58

Richard Bellman. "On a Routing Problem." *Quarterly of Applied Mathematics* 16(1), 87–90, 1958. https://doi.org/10.1090/qam/102435 . Bibliographic data from the DOI record and secondary summaries; the paper was not inspected in this pass.

<a id="bennett89"></a>
## bennett89

Charles H. Bennett. *Time/Space Trade-Offs for Reversible Computation*. SIAM Journal on Computing 18(4), 766–776, 1989. https://doi.org/10.1137/0218053 . Bibliographic metadata only; the paper was not inspected in this pass. The manual credits it with the recursive checkpointing strategy as described in [ltv98](#ltv98), Sections 6 and 7.

<a id="bermanhartmanis75"></a>
## bermanhartmanis75

Leonard Berman and Juris Hartmanis. *On Isomorphisms and Density of NP and Other Complete Sets*. Technical Report TR75-260, Department of Computer Science, Cornell University, October 1975. https://hdl.handle.net/1813/7101 . The open eCommons PDF is an image scan without a text layer. An independent agent review checked these locators against it on 2026-11-08 UTC: §I, printed p. 2 (the isomorphism conjecture and its `P ≠ NP` consequence); §III, Theorem 1, printed pp. 7–10 (PDF pp. 10–13; isomorphism from invertible, length-increasing one-one reductions); Lemmas 3 and 5, printed pp. 10–12 (length growth and the two-argument padding and read-back condition); and Theorem 7 with its CNF construction, printed pp. 13–14. The journal version (*SIAM Journal on Computing* 6(2), 305–322, 1977, https://doi.org/10.1137/0206023) was not checked, and its numbering is not claimed to match.

<a id="blum67"></a>
## blum67

Manuel Blum. *A Machine-Independent Theory of the Complexity of Recursive Functions*. Journal of the ACM 14(2), 322–336, 1967. https://doi.org/10.1145/321386.321395 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the two axioms, recursive relatedness and the speed-up theorem to this paper. The manual also mentions the customary attribution of the measure-independent theorem on arbitrarily complex functions to this paper (and to Rabin, 1960); that attribution and any theorem locator are unverified.

<a id="bm15"></a>
## bm15

Markus Bläser and Bodo Manthey. *Smoothed Complexity Theory*. ACM Transactions on Computation Theory 7(2), Article 6, 2015; preliminary version in MFCS 2012. https://doi.org/10.1145/2656210 ; arXiv:1202.1936. Read in arXiv v2 (29 June 2012) on 2026-11-08. §5, in the paragraph before Theorem 5.2, attributes `DistNP ⊆ Avg-P ⇒ NE = E` to Ben-David, Chor, Goldreich and Luby. Journal metadata checked against the Crossref record.

<a id="borodin72"></a>
## borodin72

Allan Borodin. *Computational Complexity and the Existence of Complexity Gaps*. Journal of the ACM 19(1), 158–174, 1972. https://doi.org/10.1145/321679.321691 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the gap theorem and the almost-everywhere class convention to this paper.

<a id="borodinelyaniv98"></a>
## borodinelyaniv98

Allan Borodin, Ran El-Yaniv. *Online Computation and Competitive Analysis*. Cambridge University Press, 1998. The chapter outline, in particular Chapter 1 on list accessing, comes from the publisher's table of contents; the book text was not inspected in this pass. The manual cites it only as a textbook pointer for ski rental and for the deterministic list-accessing lower bound, with no theorem numbers.

<a id="bs23"></a>
## bs23

Dan Boneh and Victor Shoup. *A Graduate Course in Applied Cryptography*, version 0.6, January 2023. https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf . Title, authors and edition verified from the primary PDF during independent source review on 2026-11-02. Detailed textbook locator claims remain attributed to the Lean source docstrings; no complete textbook correspondence audit was performed.

<a id="bt06"></a>
## bt06

Andrej Bogdanov and Luca Trevisan. *Average-Case Complexity*. Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006. https://doi.org/10.1561/0400000004 ; arXiv:cs/0606037. Definition, lemma and theorem numbers (Definitions 1, 2, 6, 8–11 and 17, Proposition 7, Lemma 18, Theorem 19, Claim 20) were checked against the arXiv text on 2026-11-07.

<a id="canetti20"></a>
## canetti20

Ran Canetti. *Universally Composable Security*. Journal of the ACM 67(5), Article 28, 2020; full version Cryptology ePrint Archive 2000/067. https://doi.org/10.1145/3402457 .

<a id="chaitin74"></a>
## chaitin74

Gregory J. Chaitin. *Information-Theoretic Limitations of Formal Systems*. Journal of the ACM 21(3), 403–424, 1974. https://doi.org/10.1145/321832.321839 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected. The manual attributes the incompleteness theorem for program-size complexity to it, following the customary attribution; its theorem numbers and the exact form of its bound are unverified. The Lean docstrings also cite the textbook treatment in Li and Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th edition (Springer, 2019), Chapter 2; the section and theorem locator within that chapter was not checked.

<a id="chattopadhyayliao20"></a>
## chattopadhyayliao20

Eshan Chattopadhyay and Jyun-Jie Liao. *Optimal Error Pseudodistributions for Read-Once Branching Programs*. 35th Computational Complexity Conference (CCC 2020), LIPIcs 169, 25:1–25:27, 2020. https://doi.org/10.4230/LIPIcs.CCC.2020.25 ; cited from arXiv:2002.07208v4. Appendix A.1 (Definition A.2, Lemmas A.3 and A.4) was checked against the arXiv v4 text on 2026-11-08. Hoza (2021) cites the CCC version's Lemma 43 for the same material.

<a id="christofides76"></a>
## christofides76

Nicos Christofides. *Worst-Case Analysis of a New Heuristic for the Travelling Salesman Problem*. Report 388, Graduate School of Industrial Administration, Carnegie-Mellon University, 1976; reprinted in *Operations Research Forum* 3, article 20, 2022, https://doi.org/10.1007/s43069-021-00101-z . The report details are those of reference [73] in [Williamson and Shmoys](#williamsonshmoys11), whose Chapter 2 Notes attribute the algorithm to Christofides; the reprint details come from search summaries. Neither the report nor the reprint was checked; the formalization follows the proof of Theorem 2.13 of Williamson and Shmoys.

<a id="chrobakkarloffpaynevishwanathan91"></a>
## chrobakkarloffpaynevishwanathan91

Marek Chrobak, Howard J. Karloff, Thomas H. Payne, Sundar Vishwanathan. "New Results on Server Problems." *SIAM Journal on Discrete Mathematics* 4(2), 172–181, 1991. https://doi.org/10.1137/0404017 . Bibliographic metadata only; the full text was not inspected in this pass, so no theorem number is cited. The manual credits this paper with the `k`-competitiveness of Double Coverage on the line, which secondary sources attribute to it; the local proof uses the standard potential `k·M_min + Σ_{i<j}|s_i - s_j|`.

<a id="cks20"></a>
## cks20

Clément L. Canonne, Gautam Kamath and Thomas Steinke. *The Discrete Gaussian for Differential Privacy*. NeurIPS 2020; cited from arXiv:2004.00010v5, 2021. https://arxiv.org/abs/2004.00010 . Definition 28 and Lemmas 29–30 were checked against the arXiv v5 PDF on 2026-11-07.

<a id="clrs09"></a>
## clrs09

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest and Clifford Stein. *Introduction to Algorithms*, third edition. MIT Press, 2009. ISBN 978-0-262-03384-8. Section 35.1, procedure `APPROX-VERTEX-COVER` and Theorem 35.1 (it is a polynomial-time 2-approximation algorithm). The locator 35.1 was checked against secondary course material, not the printed book. Sections 22.3–22.4 (depth-first search; Lemma 22.11, acyclic if and only if no back edges; Theorem 22.12, correctness of `TOPOLOGICAL-SORT`) and Section 24.1 (Bellman–Ford; Lemma 24.2, estimates equal shortest-path weights after `|V| - 1` passes when no negative cycle is reachable; Theorem 24.4, correctness of `BELLMAN-FORD`) were likewise checked against secondary course material. Sections 25.1 ("Shortest paths and matrix multiplication": repeated (min,+) squaring) and 25.2 ("The Floyd–Warshall algorithm") are the all-pairs shortest-path locators. They were checked against the edition's published table of contents only.

<a id="complexitylib"></a>
## complexitylib

Complexitylib contributors. *Complexitylib*, source snapshot `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. [Pinned repository](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8). Individual declarations are linked in the text. The repository bibliography records mathematical sources; attribution here reports those source annotations unless independent verification is explicitly stated.

<a id="cook74"></a>
## cook74

Stephen A. Cook. *An Observation on Time-Storage Trade Off*. Journal of Computer and System Sciences 9(3):308-316, 1974. The pyramid lower bound was checked through its statement as Theorem 4.8 of [nordstrom15](#nordstrom15).

<a id="cookmertz24"></a>
## cookmertz24

James Cook and Ian Mertz. *Tree Evaluation is in Space O(log n · log log n)*. STOC 2024; full report ECCC TR23-174 (15 November 2023). https://eccc.weizmann.ac.il/report/2023/174/ .

<a id="cookreckhow73"></a>
## cookreckhow73

Stephen A. Cook, Robert A. Reckhow. “Time Bounded Random Access Machines.” *Journal of Computer and System Sciences* 7(4), 354–375, 1973. https://doi.org/10.1016/S0022-0000(73)80029-7 . Local source explicitly labels its adaptation; publisher fetch unavailable in this pass.

<a id="cookreckhow79"></a>
## cookreckhow79

Stephen A. Cook, Robert A. Reckhow. “The Relative Efficiency of Propositional Proof Systems.” *The Journal of Symbolic Logic* 44(1), 36–50, 1979. https://doi.org/10.2307/2273702 . The manual cites this paper for the notion of a Frege system. The simulation of resolution by the Frege system in the [proof-systems chapter](circuits-logic-and-other-models/proof-systems.md) is presented as a standard fact in this framework, with no theorem locator; the paper itself was not re-inspected in this pass.

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

Cynthia Dwork and Aaron Roth. *The Algorithmic Foundations of Differential Privacy*. Foundations and Trends in Theoretical Computer Science 9(3–4), 211–407, 2014. https://doi.org/10.1561/0400000042 . Definition 2.4, Proposition 2.1, Theorem 2.2 and its footnote, §2.3, Claim 3.5, Theorem 3.16, Definition 3.7, Theorem 3.20, Corollary 3.21, Theorem B.1 and Corollary B.2 were checked against the published PDF on 2026-11-07.

<a id="edmonds65"></a>
## edmonds65

Jack Edmonds. "Maximum Matching and a Polyhedron with 0,1-Vertices." *Journal of Research of the National Bureau of Standards, Section B* 69B(1–2), 125–130, 1965. https://doi.org/10.6028/jres.069B.013 . Cited only as the origin of polynomial-time minimum-weight perfect matching, which the library does not formalize; the bibliographic details come from search summaries and the paper was not checked.

<a id="erdos1947"></a>
## erdos1947

Paul Erdős. “Some Remarks on the Theory of Graphs.” *Bulletin of the American Mathematical Society* 53(4), 292–294, 1947. https://doi.org/10.1090/S0002-9904-1947-08785-1 . Bibliographic metadata checked on 2026-11-07; the full text was not inspected in this pass. The manual attributes only the counting lower bound `2 ^ (k / 2) < R(k, k)` to this paper; the formal statement follows Alon–Spencer, *The Probabilistic Method*, Proposition 1.1.1, as cited in the Lean documentation.

<a id="erdosszekeres1935"></a>
## erdosszekeres1935

Paul Erdős and George Szekeres. “A Combinatorial Problem in Geometry.” *Compositio Mathematica* 2, 463–470, 1935. http://www.numdam.org/item/CM_1935__2__463_0/ . The graph-theoretic Ramsey theorem and its induction, pp. 465–467, give the upper bound `R(k, l) ≤ C(k + l − 2, k − 1)`; the agent review of the introducing PR checked pp. 466–467 against the Numdam PDF.

<a id="erickson24"></a>
## erickson24

Jeff Erickson, Ivor van der Hoog, Tillmann Miltzow. “Smoothing the Gap Between NP and ∃R.” *SIAM Journal on Computing* 53(6), FOCS20-102–FOCS20-138, 2024. https://doi.org/10.1137/20M1385287 . Author preprint consulted: https://arxiv.org/abs/1912.02278v3 , §6.1. Published metadata comes from the pinned bibliography; the consulted preprint is dated 2021.

<a id="fks84"></a>
## fks84

Michael L. Fredman, János Komlós, Endre Szemerédi. "Storing a Sparse Table with O(1) Worst Case Access Time." *Journal of the ACM* 31(3), 538–544, 1984. https://doi.org/10.1145/828.1884 . Bibliographic metadata was checked against the DOI record on 2026-11-08. The full text was not inspected. The formalization follows the textbook account in [clrs09](#clrs09), Section 11.5 ("Perfect hashing"), and that locator was checked against the edition's published table of contents only. No theorem numbers are attributed to either source.

<a id="floyd62"></a>
## floyd62

Robert W. Floyd. "Algorithm 97: Shortest Path." *Communications of the ACM* 5(6), 345, 1962. https://doi.org/10.1145/367766.368168 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the Floyd–Warshall recurrence to this note.

<a id="fly22"></a>
## fly22

Zhiyuan Fan, Jiatu Li, and Tianqi Yang. *The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity*. Electronic Colloquium on Computational Complexity (ECCC), Report TR21-125, Revision 1 (12 June 2022), https://eccc.weizmann.ac.il/report/2021/125/ ; conference version in *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 962–975, https://doi.org/10.1145/3519935.3520010 . Inspected ECCC TR21-125 Revision 1 PDF directly: Section 4.1 (pp. 24–26), Section 4.2, Definitions 4.3–4.5 (pp. 26–27), Section 4.4, Definition 4.9 (p. 28), Section 7.1, Definition 7.1, Lemmas 7.2–7.4, and Theorem 7.5 (pp. 39–41), and Section 7.2 (pp. 41–42).

<a id="freivalds79"></a>
## freivalds79

Rūsiņš Freivalds. "Fast Probabilistic Algorithms." *Mathematical Foundations of Computer Science 1979*, Lecture Notes in Computer Science 74, 57–69. https://doi.org/10.1007/3-540-09526-8_5 . Bibliographic data from the DOI record, checked 2026-11-07; the full text was not inspected. The manual attributes only the random-vector matrix-product check to this paper.

<a id="gentry09"></a>
## gentry09

Craig Gentry. “Fully Homomorphic Encryption Using Ideal Lattices.” *STOC 2009*, 169–178. https://doi.org/10.1145/1536414.1536440 . Bibliographic data and theorem locator taken from the pinned repository; full text not independently re-audited here.

<a id="ggm86"></a>
## ggm86

Oded Goldreich, Shafi Goldwasser, Silvio Micali. “How to Construct Random Functions.” *Journal of the ACM* 33(4), 792–807, 1986. Author-hosted version of record: https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf . Adaptive function-test definition consulted.

<a id="gkr15"></a>
## gkr15

Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum. *Delegating Computation: Interactive Proofs for Muggles*. JACM 62(4), article 27, 2015. https://doi.org/10.1145/2699436 .

<a id="goemanswilliamson95"></a>
## goemanswilliamson95

Michel X. Goemans and David P. Williamson. "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming." *Journal of the ACM* 42(6), 1115–1145, 1995. https://doi.org/10.1145/227683.227684 . Section 2 (the relaxation (P) and random-hyperplane rounding) and Section 3 (Theorem 3.1, Lemma 3.2, Theorem 3.3, Lemma 3.4, and Lemma 3.5 with its tangent-line proof at `θ = 2.331122`) were checked against the author-hosted copy at https://math.mit.edu/~goemans/PAPERS/maxcut-jacm.pdf on 2026-11-08.

<a id="goldreich-tree24"></a>
## goldreich-tree24

Oded Goldreich. *On the Cook–Mertz Tree Evaluation procedure*. ECCC TR24-109, revision 2 (27 December 2024). https://eccc.weizmann.ac.il/report/2024/109/ .

<a id="goldreich04"></a>
## goldreich04

Oded Goldreich. *Foundations of Cryptography, Volume 2: Basic Applications*. Cambridge University Press, 2004. https://doi.org/10.1017/CBO9780511721656 . Author's chapter listing and draft availability: https://www.wisdom.weizmann.ac.il/~oded/foc-vol2.html . Author page checked; the full published chapter was not independently audited here.

<a id="gomoryhu61"></a>
## gomoryhu61

Ralph E. Gomory and T. C. Hu. “Multi-Terminal Network Flows.” *Journal of the Society for Industrial and Applied Mathematics* 9(4), 551–570, 1961. https://doi.org/10.1137/0109047 . Bibliographic metadata checked through the publisher record; the article body was not inspected in this pass. The manual cites it for cut-equivalent (Gomory–Hu) trees and the triangle inequality for minimum cut values, as described in [Schrijver 2003](#schrijver03), Section 15.4.

<a id="grs12"></a>
## grs12

Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan. *Universally Utility-Maximizing Privacy Mechanisms*. SIAM Journal on Computing 41(6), 1673–1693, 2012; conference version STOC 2009. https://doi.org/10.1137/09076828X . §2.1 and Example 2.1 were checked against arXiv:0811.2841v3 on 2026-11-07.

<a id="gsw13"></a>
## gsw13

Craig Gentry, Amit Sahai, Brent Waters. “Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based.” *CRYPTO 2013*, LNCS 8042, 75–92. https://doi.org/10.1007/978-3-642-40041-4_5 ; authors' full-version record https://eprint.iacr.org/2013/340 . Metadata/abstract checked; PDF fetch was blocked in this source pass.

<a id="gusfield90"></a>
## gusfield90

Dan Gusfield. “Very Simple Methods for All Pairs Network Flow Analysis.” *SIAM Journal on Computing* 19(1), 143–155, 1990. https://doi.org/10.1137/0219009 . Bibliographic metadata checked through the publisher record; the article body was not inspected in this pass. Cited only for the variant of the Gomory–Hu construction without contraction, which is not formalized.

<a id="hartline21"></a>
## hartline21

Jason D. Hartline. *Mechanism Design and Approximation*, book manuscript; chapters 1–7 revised 20 September 2021. http://jasonhartline.com/MDnA/ . The author-hosted Chapter 2, "Equilibrium", was consulted on 2026-11-08 for Definitions 2.3.2 and 2.4.1, §2.3, §2.4, Proposition 2.4.1, Theorem 2.5.1, §2.7 (Corollaries 2.7.1 and 2.7.2, Example 2.7.1), §2.8 (Example 2.8.1) and §2.9; locators follow that version.

<a id="hartmanis1968"></a>
## hartmanis1968

Juris Hartmanis. "Computational Complexity of One-Tape Turing Machine Computations." *Journal of the ACM* 15(2), 325–339, 1968. https://doi.org/10.1145/321450.321464 . Bibliographic metadata checked through Crossref; the article body was not inspected in this pass. The manual cites it for the `n log n` lower bound on one-tape recognition of nonregular languages, as attributed in [Pighizzini 2009](#pighizzini2009), §1 and §4.

<a id="hennie1965"></a>
## hennie1965

F. C. Hennie. “One-tape, off-line Turing machine computations.” *Information and Control* 8(6), 553–578, 1965. https://doi.org/10.1016/S0019-9958(65)90399-2 . Bibliographic metadata checked; the article body was not inspected in this pass, so the manual cites it for the crossing-sequence method and not for a numbered statement.

<a id="henson26"></a>
## henson26

Christopher Henson and Fabrizio Montesi. *Computer Science as Infrastructure: the Spine of the Lean Computer Science Library (CSLib)*. EPTCS 449 (LSFA 2026), pp. 141–148, 2026. https://doi.org/10.4204/EPTCS.449.9 . Version-of-record metadata verified through https://arxiv.org/abs/2602.15078v2 on 2026-11-02 UTC; DOI resolver was unavailable in this research environment.

<a id="hhk17"></a>
## hhk17

Dennis Hofheinz, Kathrin Hövelmanns, Eike Kiltz. “A Modular Analysis of the Fujisaki–Okamoto Transformation.” *Theory of Cryptography (TCC 2017)*, LNCS 10677, 341–371, 2017. https://doi.org/10.1007/978-3-319-70500-2_12 ; full version https://eprint.iacr.org/2017/604 (dated 2 November 2021). Checked against the 2 November 2021 ePrint PDF (§2.1 correctness/spreadness and Def. 2.2 / Fig. 4 IND-CPA; §3.1 Fig. 5 transform `T`; §3.2.1 Fig. 9 `FO^⊥`; §3.2.2 Fig. 12 `FO-notbot`), with model adaptations (`ExplicitCoinPKE`/`Scheme` fixed types and arbitrary `sampleCoins`/`sampleMsg`/`sampleKey` samplers, single-stage fixed-message probability-difference `indCpaGame`/`indCpaAdvantage`, and domain-separated `H : Bool × M × CT → K`) documented in the Lean module and chapter text.

<a id="hhrvw20"></a>
## hhrvw20

Iftach Haitner, Thomas Holenstein, Omer Reingold, Salil Vadhan, Hoeteck Wee. “Inaccessible Entropy II: IE Functions and Universal One-Way Hashing.” *Theory of Computing* 16(8), 1–55, 2020. https://doi.org/10.4086/toc.2020.v016a008 . Open-access article PDF inspected (Section 3, Definitions 3.1, 3.3, 3.9, pp. 11–15; Section 4.2, Theorem 4.5 and Claims 4.6–4.8, pp. 21–25, adapted to a constant light-image threshold with inverse-linear gap `1 / (64 * (n + 1))`; and Section 5.1, Theorem 5.1, Lemmas 5.3–5.7, and Section 5.1.5 STEPS 1–5, pp. 25–32).

<a id="hierholzer73"></a>
## hierholzer73

Carl Hierholzer. “Ueber die Möglichkeit, einen Linienzug ohne Wiederholung und ohne Unterbrechung zu umfahren.” *Mathematische Annalen* 6, 30–32, 1873. https://doi.org/10.1007/BF01442866 . Cited for the sufficiency of even degrees and the splicing construction; the attribution follows secondary sources, and the German original was not checked.

<a id="hill99"></a>
## hill99

Johan Håstad, Russell Impagliazzo, Leonid A. Levin, Michael Luby. “A Pseudorandom Generator from Any One-Way Function.” *SIAM Journal on Computing* 28(4), 1364–1396, 1999. https://doi.org/10.1137/S0097539793244708 . Publisher abstract checked; full article not independently audited.

<a id="hmu06"></a>
## hmu06

John E. Hopcroft, Rajeev Motwani and Jeffrey D. Ullman. *Introduction to Automata Theory, Languages, and Computation*, third edition. Addison-Wesley, 2006. ISBN 0-321-45536-3. Cited for Section 7.4.4 ("Testing Membership in a CFL"), the CYK algorithm for grammars in Chomsky normal form. The section number and title were checked against secondary course material, not the printed book.

<a id="holenstein06"></a>
## holenstein06

Thomas Holenstein. “Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness.” *TCC 2006*. Author PDF: https://crypto.ethz.ch/publications/files/Holens06.pdf . Definitions and construction overview consulted.

<a id="holenstein09"></a>
## holenstein09

Thomas Holenstein. “Parallel Repetition: Simplifications and the No-Signaling Case.” *Theory of Computing* 5(8), 141–172, 2009. https://doi.org/10.4086/toc.2009.v005a008 . Journal PDF inspected (Definition 2.4 and Theorem 2.5, p. 146; Definition 5.1, p. 151; Lemma 5.4 and (5.5), p. 153; Claims 6.2 and 6.3, p. 154; Lemma 6.4 and (6.3)–(6.7) of its proof, p. 155; (6.8)–(6.16), p. 156; the first stage of the embedding, from (6.15) and (6.16) by Corollary 5.3, (6.17)–(6.19) and the second stage, and Lemma 6.5, (6.20) and its proof, p. 157; Lemma 7.1, p. 158; the proof of Theorem 2.5, (7.6) and (7.7), p. 159).

<a id="hoza21"></a>
## hoza21

William M. Hoza. *Better Pseudodistributions and Derandomization for Space-Bounded Computation*. APPROX/RANDOM 2021, LIPIcs 207, 28:1–28:23, 2021. https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2021.28 . Appendix A (Lemma A.2 and the proof of Theorem A.3) was checked against the LIPIcs text on 2026-11-08.

<a id="immerman1988"></a>
## immerman1988

Neil Immerman. “Nondeterministic Space Is Closed under Complementation.” *SIAM Journal on Computing* 17(5), 935–938 (1988). DOI: https://doi.org/10.1137/0217058. Author copy inspected: https://people.cs.umass.edu/~immerman/pub/space.pdf (Theorem 1; inspected 2026-11-01).

<a id="impagliazzo01"></a>
## impagliazzo01

Russell Impagliazzo and Ramamohan Paturi. *On the Complexity of k-SAT*. Journal of Computer and System Sciences 62(2), 367–375, 2001. DOI: [10.1006/jcss.2000.1727](https://doi.org/10.1006/jcss.2000.1727). [Author-hosted copy](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturi_2001_jcss.pdf). Publisher metadata and abstract checked 2026-11-02; cited for the historical exponent-based hypothesis, not for the 2026 result.

<a id="impagliazzowigderson97"></a>
## impagliazzowigderson97

Russell Impagliazzo and Avi Wigderson. *P = BPP if E Requires Exponential Circuits: Derandomizing the XOR Lemma*. Proceedings of the 29th Annual ACM Symposium on Theory of Computing, 220–229, 1997. DOI: [10.1145/258533.258590](https://doi.org/10.1145/258533.258590). ACM metadata checked by the coordinated source pass on 2026-11-02; no complete literature proof audit is asserted.

<a id="irani91"></a>
## irani91

Sandy Irani. "Two Results on the List Update Problem." *Information Processing Letters* 38(6), 301–306, 1991. https://doi.org/10.1016/0020-0190(91)90086-W . Crossref metadata checked on 2026-11-07; the full text was not inspected in this pass. The manual uses it only as the place where secondary sources say the deterministic `2n/(n+1)` list-update lower bound of Karp and Raghavan is reported.

<a id="karlin88"></a>
## karlin88

Anna R. Karlin, Mark S. Manasse, Larry Rudolph, Daniel D. Sleator. "Competitive Snoopy Caching." *Algorithmica* 3, 79–119, 1988. https://doi.org/10.1007/BF01762111 . Bibliographic data from secondary indexes and the DOI record; the full text was not inspected in this pass. The manual credits this paper only with the rent-or-buy framing behind ski rental, which secondary sources attribute to it.

<a id="kasami65"></a>
## kasami65

Tadao Kasami. *An Efficient Recognition and Syntax-Analysis Algorithm for Context-Free Languages*. Scientific Report AFCRL-65-758, Air Force Cambridge Research Laboratory, Bedford, MA, 1965. Bibliographic metadata was checked against secondary sources on 2026-11-08; the report was not inspected. It is cited, with [Younger 1967](#younger67), as an original source of the CYK algorithm.

<a id="katzlindell20"></a>
## katzlindell20

Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd edition. CRC Press, 2020. Bibliographic metadata and section titles checked against the authors' 3rd-edition table of contents and preface: https://www.cs.umd.edu/~jkatz/imc/toc-preface-3rd.pdf (Sections 9.2.3–9.2.4 on the factoring and RSA assumptions; Section 15.1.1 on trapdoor permutations; Section 15.2 on Paillier encryption; Sections 15.4.1–15.4.3 on quadratic residues and the quadratic residuosity assumption; and Sections 15.5.1–15.5.2 on modular square roots and the Rabin trapdoor permutation). Detailed numbered locators (Definitions, Claims, Propositions, Lemmas, Constructions, Examples, Exercises, and Theorems) remain attributed to the Lean source docstrings, as the textbook body was not independently audited; the Lean modules adapt the parameter generators, RSA challenge domain, Rabin sampling distribution, and the Paillier encryption-randomness sampler (dyadic sampling with `unitOrOne` in place of uniform `ℤ_N^*`) as documented in their module docstrings and implementation notes.

<a id="kobayashi1985"></a>
## kobayashi1985

Kojiro Kobayashi. "On proving time constructibility of functions." *Theoretical Computer Science* 35, 215–225, 1985. https://doi.org/10.1016/0304-3975(85)90015-5 . Bibliographic metadata checked through Crossref; the article body was not inspected in this pass. The manual cites it, as [Pighizzini 2009](#pighizzini2009) §4 does, as an independent proof of the `n log n` bound.

<a id="kortevygen18"></a>
## kortevygen18

Bernhard Korte and Jens Vygen. *Combinatorial Optimization: Theory and Algorithms*, sixth edition. Springer, Algorithms and Combinatorics 21, 2018. https://doi.org/10.1007/978-3-662-56039-6 . Cited for Section 2.4 (Eulerian and bipartite graphs), which characterizes connected graphs with a closed Eulerian walk by even degrees (Euler, Hierholzer). The section was located from secondary sources and not checked against the printed book; its theorem number is not cited.

<a id="kov17"></a>
## kov17

Peter Kairouz, Sewoong Oh and Pramod Viswanath. *The Composition Theorem for Differential Privacy*. IEEE Transactions on Information Theory 63(6), 4037–4049, 2017. https://doi.org/10.1109/TIT.2017.2685505 ; theorem numbering cited from arXiv:1311.0776v4, 2015. Theorem 3.4 (equation (7)) was checked against the arXiv v4 PDF on 2026-11-07; the journal metadata was checked against Crossref.

<a id="lean-validation"></a>
## lean-validation

Lean development team. *Validating a Lean Proof*, The Lean Language Reference, accessed 2026-11-02 UTC. https://lean-lang.org/doc/reference/latest/ValidatingProofs/ . The page was inspected live; the requested version-specific URL was unavailable, and no verified archival snapshot was obtained. Version-specific library assertions in this dossier instead rely on pinned repository sources.

<a id="lev86"></a>
## lev86

Leonid A. Levin. *Average Case Complete Problems*. SIAM Journal on Computing 15(1), 285–286, 1986. https://doi.org/10.1137/0215020 . Bibliographic metadata checked on 2026-11-07. The manual attributes only the existence of a complete distributional problem for `(NP, PComp)` to this paper, and follows the proof of [bt06](#bt06), Theorem 19.

<a id="lfkn92"></a>
## lfkn92

Carsten Lund, Lance Fortnow, Howard Karloff and Noam Nisan. *Algebraic Methods for Interactive Proof Systems*. JACM 39(4), 859–868, 1992. https://doi.org/10.1145/146585.146605 .

<a id="liupass20"></a>
## liupass20

Yanyi Liu and Rafael Pass. *On One-way Functions and Kolmogorov Complexity*. FOCS 2020, 1243–1254. https://doi.org/10.1109/FOCS46700.2020.00118 . Definition/theorem locators refer to the full version https://arxiv.org/abs/2009.11514v1 , §§2.3 and 3, pp. 8–9.

<a id="lll82"></a>
## lll82

Arjen K. Lenstra, Hendrik W. Lenstra Jr. and László Lovász. "Factoring Polynomials with Rational Coefficients." *Mathematische Annalen* 261, 515–534, 1982. https://doi.org/10.1007/BF01457454 . Inspected the author-hosted scan https://www.math.leidenuniv.nl/~hwl/PUBLICATIONS/1982f/art.pdf on 2026-11-08: §1, conditions (1.4)–(1.5), Proposition (1.6) and the remark after it, Proposition (1.11), the algorithm (1.15)–(1.21), the swap formulas (1.22) and the termination argument (1.23)–(1.26).

<a id="ltv98"></a>
## ltv98

Ming Li, John Tromp and Paul Vitányi. *Reversible Simulation of Irreversible Computation by Pebble Games*. Physica D 120, 168–176, 1998. https://doi.org/10.1016/S0167-2789(98)00052-9 . Locators refer to arXiv:quant-ph/9703009v3 (11 April 1997), https://arxiv.org/abs/quant-ph/9703009v3 . The reversible pebble rule (Section 6), the procedures `pebble(s, n)` and `unpebble(s, n)` (Section 7), Theorem 1, Corollaries 1 and 2, Lemma 1 and Theorem 2 were checked.

<a id="manassemcgeochsleator90"></a>
## manassemcgeochsleator90

Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator. "Competitive Algorithms for Server Problems." *Journal of Algorithms* 11(2), 208–230, 1990. https://doi.org/10.1016/0196-6774(90)90003-W ; author PDF https://www.cs.cmu.edu/~sleator/papers/server-problems.pdf . Theorem 6 (lower bound `k/(k-h+1)` against `h`-server offline algorithms on a graph with at least `k + 1` nodes, proved with a lazy online algorithm, its nemesis sequence and an ensemble of offline algorithms) and Corollary 7 (no `c`-competitive algorithm for `c < k`) were checked against the author PDF on 2026-11-08. The local lower bound is the case `h = k`.

<a id="mathlib"></a>
## mathlib

Mathlib contributors. *Mathlib*, pinned source `69552756cd8a2d2d48763cf7279fd814d6a1224d`, inspected 2026-11-01. https://github.com/leanprover-community/mathlib4/tree/69552756cd8a2d2d48763cf7279fd814d6a1224d

<a id="mccreightmeyer69"></a>
## mccreightmeyer69

Edward M. McCreight and Albert R. Meyer. *Classes of Computable Functions Defined by Bounds on Computation: Preliminary Report*. Proceedings of the First Annual ACM Symposium on Theory of Computing (STOC '69), 79–88, 1969. https://doi.org/10.1145/800169.805423 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected. The manual attributes the union, naming and honesty theorems to it, following the customary attribution; Odifreddi's textbook [odifreddi99](#odifreddi99) attributes the Naming Theorem VII.3.6 and the Union Theorem VII.3.7 to it. The paper's own theorem numbers and exact hypotheses are unverified. Odifreddi states the union theorem for a uniformly recursive sequence `t_n` with `t_n(x) ≤ t_{n+1}(x)` for all `n` and `x`, which is the hypothesis of `union_theorem`. Secondary accounts state the union theorem for a recursively enumerable "self-bounded" set of bounds, in which every finite subset is dominated almost everywhere by a member; this would match `union_theorem_of_directed`, but it has not been checked against the paper, so the library derives the directed and almost-everywhere variants from the pointwise `union_theorem`. The open survey by Hartmanis and Hopcroft (Cornell TR70-59, https://hdl.handle.net/1813/5918) is an image scan that was not read in this pass.

<a id="mitzenmacherupfal17"></a>
## mitzenmacherupfal17

Michael Mitzenmacher and Eli Upfal. *Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis*, 2nd edition. Cambridge University Press, 2017. The locator Section 1.3, Theorem 1.4 (an incorrect product survives a uniform `0`/`1` vector with probability at most `1/2`) was checked against secondary descriptions on 2026-11-07; the full text was not inspected in this pass.

<a id="monderershapley96"></a>
## monderershapley96

Dov Monderer and Lloyd S. Shapley. *Potential Games*. Games and Economic Behavior 14(1), 124–143, 1996. https://doi.org/10.1006/game.1996.0044 . The published text was consulted on 2026-11-07 for the definitions (2.1)–(2.3), Lemmas 2.1, 2.3, 2.5 and 2.7, Corollary 2.2, Theorem 3.1 and footnote 12.

<a id="mosertardos10"></a>
## mosertardos10

Robin A. Moser and Gábor Tardos. “A Constructive Proof of the General Lovász Local Lemma.” *Journal of the ACM* 57(2), Article 11, 2010. https://doi.org/10.1145/1667053.1667060 . Open version: arXiv:0903.0544v3, https://arxiv.org/abs/0903.0544 . Theorems 1.1–1.4, the Section 2 definitions of the log and witness trees, Lemma 2.1 and the Section 3 counting argument (Lemma 3.1) were checked against the arXiv v3 PDF (dated 20 May 2009) on 2026-11-08. The JACM article numbering was not checked against the typeset journal version.

<a id="nagamochiibaraki92"></a>
## nagamochiibaraki92

Hiroshi Nagamochi and Toshihide Ibaraki. "Computing Edge-Connectivity in Multigraphs and Capacitated Graphs." *SIAM Journal on Discrete Mathematics* 5(1), 54–66, 1992. https://doi.org/10.1137/0405004 . Bibliographic metadata checked against the Crossref record on 2026-11-08; the paper was not inspected. The manual credits it with the basic property of maximum adjacency orderings (the cut of the last vertex is a minimum cut between the last two), as attributed by [stoerwagner97](#stoerwagner97) in secondary descriptions. No locator is claimed.

<a id="nagy1972"></a>
## nagy1972

Zsigmond Nagy. “A Constructive Estimation of the Ramsey Numbers” (in Hungarian). *Matematikai Lapok* 23, 301–302, 1972 (the volume is dated 1972 but reportedly appeared in 1975). The original was not inspected; the construction and its bound follow Jukna, *Extremal Combinatorics*, 2nd ed., §13.7 and the Chapter 13 exercises, as cited in the Lean documentation.

<a id="naoryung89"></a>
## naoryung89

Moni Naor and Moti Yung. “Universal One-Way Hash Functions and their Cryptographic Applications.” *Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989)*, 33–43, 1989. https://doi.org/10.1145/73007.73011 . Authors' revised manuscript (March 13, 1995): https://www.wisdom.weizmann.ac.il/~naor/PAPERS/uowhf.ps (§2, §2.3, §3 and §4).

<a id="nisan92"></a>
## nisan92

Noam Nisan. *Pseudorandom Generators for Space-Bounded Computation*. Combinatorica 12(4), 449–461, 1992. DOI: [10.1007/BF01305237](https://doi.org/10.1007/BF01305237). The publisher copy is paywalled and was not consulted, so its theorem numbering is unverified. The statement was checked against S. Vadhan, *Pseudorandomness* (2012), §8.2.1, and P. Hatami and W. Hoza, *Paradigms for Unconditional Pseudorandom Generators* (2024), Definition 1.5 and §3.2. The Lean proof is the library's own derivation of the hashing argument in expectation form.

<a id="nisanwigderson94"></a>
## nisanwigderson94

Noam Nisan and Avi Wigderson. *Hardness vs Randomness*. Journal of Computer and System Sciences 49(2), 149–167, 1994. DOI: [10.1016/S0022-0000(05)80043-1](https://doi.org/10.1016/S0022-0000(05)80043-1). Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; this section's source-to-proof description follows the pinned Lean documentation.

<a id="nordstrom15"></a>
## nordstrom15

Jakob Nordström. *New Wine into Old Wineskins: A Survey of Some Pebbling Classics with Supplemental Results*, manuscript version of 25 March 2015. https://www.jakobnordstrom.se/docs/publications/PebblingSurveyTMP.pdf . Definition 1.1 (black pebble game), Proposition 2.5 (sliding), Theorem 4.1 (complete binary trees), Definition 4.5 and Theorem 4.8 (pyramids) were checked.

<a id="odifreddi99"></a>
## odifreddi99

Piergiorgio Odifreddi. *Classical Recursion Theory, Volume II*. Studies in Logic and the Foundations of Mathematics 143, North-Holland, 1999. ISBN 978-0-444-50205-6. Read in the author's open PDF, https://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT2.pdf , on 2026-11-08. Locators checked there, with the book's printed page numbers: Definition VII.2.9 (measured sets, pp. 33–34); Definition VII.2.13 (`g`-honest functions, p. 35); Exercise VII.2.14a (members of a measured set are honest for one recursive `g`, attributed to Blum 1967, p. 36); Definition VII.3.1 (the almost-everywhere class `C_t`, p. 47); Theorem VII.3.6 (Naming Theorem, attributed to Meyer and McCreight 1969, statement and proof pp. 51–54); and Theorem VII.3.7 (Union Theorem, attributed to Meyer and McCreight 1969, p. 55). The manual uses this book for the statements of these results, not for their proofs: the library's union proof was written independently, and its naming proof follows the book's priority construction with the differences recorded in the Lean module docstring.

<a id="openai-logspace26"></a>
## openai-logspace26

OpenAI. *Exact Derandomization of Logarithmic Space: L = RL = BPL*. Preprint, 23 September 2026, not peer reviewed; cited here only for construction provenance. Accompanying Lean file at revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/CatalyticComparison.lean .

<a id="openaieth26"></a>
## openaieth26

OpenAI. *The Exponential Time Hypothesis is False*. Manuscript dated 17 October 2026, revised 25 October 2026. Source revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. [PDF](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf); [primary TeX](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex). The interpolation-route statement, metadata and label were checked in freshly retrieved TeX on 2026-11-02; full proof and PDF pagination were not independently audited.

<a id="pighizzini2009"></a>
## pighizzini2009

Giovanni Pighizzini. "Nondeterministic One-Tape Off-Line Turing Machines and Their Time Complexity." arXiv:0905.1271v1 [cs.FL], 2009. https://arxiv.org/abs/0905.1271v1 . The v1 text was read for §1, Theorem 1 (§3: crossing sequences of bounded length imply regularity, stated for nondeterministic machines under the weak measure), and the opening of §4 with Theorem 3 (attribution of the deterministic `n log n` bound to Trakhtenbrot, Hartmanis and Kobayashi). The arXiv record says the paper was to appear in the *Journal of Automata, Languages and Combinatorics*; secondary indexes place it in volume 14 (2009), pp. 107–124. The journal version was not inspected.

<a id="rado62"></a>
## rado62

Tibor Radó. *On Non-Computable Functions*. The Bell System Technical Journal 41(3), 877–884, 1962. https://doi.org/10.1002/j.1538-7305.1962.tb00480.x ; scan at https://archive.org/details/bstj41-3-877 . Read in the archive.org text on 2026-11-08: Section V, Theorem (`Σ(n)` eventually exceeds every computable `f`, so `Σ` is not computable), proved with an auxiliary computable majorant of `f`; Section VI defines the shift function `S(n)` and derives the same domination from `S(n) ≥ Σ(n)`.

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

<a id="roth82"></a>
## roth82

Alvin E. Roth. *Incentive Compatibility in a Market with Indivisible Goods*. Economics Letters 9(2), 127–132, 1982. https://doi.org/10.1016/0165-1765(82)90003-9 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected. It is cited as the standard primary reference for the strategy-proofness of top trading cycles; no locator in it was verified, and neither [schummervohra07](#schummervohra07) nor [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, cites it.

<a id="rothpostlewaite77"></a>
## rothpostlewaite77

Alvin E. Roth and Andrew Postlewaite. *Weak versus Strong Domination in a Market with Indivisible Goods*. Journal of Mathematical Economics 4(2), 131–137, 1977. https://doi.org/10.1016/0304-4068(77)90004-0 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected, so no theorem number is cited. The housing-market modules attribute to it, as the standard primary reference and without a verified locator, the uniqueness of the strict-core (weak-domination) allocation and its agreement with the competitive allocation; neither [schummervohra07](#schummervohra07) nor [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, cites it.

<a id="roughgarden13cs364a"></a>
## roughgarden13cs364a

Tim Roughgarden. *CS364A: Algorithmic Game Theory*, lecture notes, Stanford University, Fall 2013. https://theory.stanford.edu/~tim/f13/f13.html . Lecture #17, "No-Regret Dynamics" (18 November 2013), was consulted on 2026-11-07 for Definition 1.2, §3, Proposition 3.1, Remark 3.2, Corollary 3.3 and footnote 1. Lecture #9, "Beyond Quasi-Linearity" (21 October 2013), was consulted on 2026-11-08 for §3 (the top trading cycle algorithm, Theorems 3.1 and 3.2). Its core is defined by strict blocking, for which only the existence half of Theorem 3.2 holds; a checked three-agent market in `ComplexityTests/HousingMarket.lean` has a second core allocation.

<a id="roughgarden15"></a>
## roughgarden15

Tim Roughgarden. *Intrinsic Robustness of the Price of Anarchy*. Journal of the ACM 62(5), Article 32, 2015. https://doi.org/10.1145/2806883 . The author's version of 14 July 2015 was consulted on 2026-11-07 for Definition 2.1, derivation (3)–(5), Example 2.5, (15) and Theorems 3.2–3.3; locators follow that version.

<a id="roughgardentardos02"></a>
## roughgardentardos02

Tim Roughgarden and Éva Tardos. *How Bad Is Selfish Routing?* Journal of the ACM 49(2), 236–259, 2002. https://doi.org/10.1145/506147.506153 . The author's version of 5 December 2001 was consulted on 2026-11-07 for Section 2.1, Definition 2.1, Lemma 2.2, Theorem 4.5 and Figure 3; locators follow that version.

<a id="sakszhou99"></a>
## sakszhou99

Michael Saks and Shiyu Zhou. *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*. Journal of Computer and System Sciences 58(2), 376–403, 1999. https://doi.org/10.1006/jcss.1998.1616 . The publisher copy is paywalled and was not consulted, so its internal numbering (including the Lemma 5.4 cited by Chattopadhyay–Liao) is unverified. The iteration is formalized from the presentation of Chattopadhyay and Liao (2020), Appendix A.1.

<a id="schrijver03"></a>
## schrijver03

Alexander Schrijver. *Combinatorial Optimization: Polyhedra and Efficiency*. Algorithms and Combinatorics 24, Springer, 2003. Cited for Gomory–Hu trees. The locator (Chapter 15, “Connectivity and Gomory–Hu trees”, Section 15.4) is taken from secondary descriptions of the table of contents only: the book itself was not inspected, and no theorem or page locator is claimed.

<a id="schrijver17"></a>
## schrijver17

Alexander Schrijver. *A Course in Combinatorial Optimization*. Lecture notes, version of March 23, 2017. https://homepages.cwi.nl/~lex/files/dict.pdf . The author-hosted PDF was consulted on 2026-11-08 UTC for Section 10.4 (Lemma 10.2), Section 10.5 (Example 10.5a, displays (23)–(25) and (27), Theorems 10.6, 10.7 and 10.9) and Exercise 10.22; the matroid intersection modules cite these locators. The corresponding chapter of Schrijver's 2003 monograph (Chapter 41) is cited in the library from secondary descriptions only; its theorem and page locators are unverified.

<a id="schummervohra07"></a>
## schummervohra07

James Schummer and Rakesh V. Vohra. "Mechanism Design without Money." Chapter 10 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 243–265. A university-hosted PDF of the book was consulted on 2026-11-08 for §10.3 (the definition of blocking coalitions and the core, Definition 10.5, Theorems 10.6 and 10.7, pp. 253–255). Its core uses weak blocking, the strict core of the housing-market modules. Its claim on p. 255 that the core and the strict core coincide under strict preferences is refuted by a checked three-agent market in `ComplexityTests/HousingMarket.lean`.

<a id="shamir1992"></a>
## shamir1992

Adi Shamir. “IP = PSPACE.” *Journal of the ACM* 39(4), 869–877 (1992). DOI: https://doi.org/10.1145/146585.146609. Original-paper scan inspected: https://crypto.cs.mcgill.ca/~crepeau/COMP647/2007/TOPIC01/Shamir-IP=PSPACE.pdf.

<a id="shapleyscarf74"></a>
## shapleyscarf74

Lloyd Shapley and Herbert Scarf. *On Cores and Indivisibility*. Journal of Mathematical Economics 1(1), 23–37, 1974. https://doi.org/10.1016/0304-4068(74)90033-0 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected. The housing market model and the top trading cycles algorithm (credited there to David Gale) are attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, §3, and [schummervohra07](#schummervohra07), §10.6 (which lists the pages as 23–28; the Crossref record was not rechecked). The housing-market modules also attribute to it the competitive allocation at round-size prices (`isCompetitive_ttc`), from memory of the literature; this attribution is unverified.

<a id="sipser13"></a>
## sipser13

Michael Sipser. *Introduction to the Theory of Computation*, third edition. Cengage Learning, 2013. Cited for Definition 2.8 (Chomsky normal form: rules `A → BC` and `A → a`, with `S → ε` permitted for the start variable `S`, and `S` forbidden on every right-hand side; the library's `ChomskyNormalFormGrammar` imposes the latter restriction only when `S → ε` is present) and Theorem 7.16 ("Every context-free language is a member of P", proved by the CYK dynamic program). Both locators were checked against secondary course material, not the printed book.

<a id="sleatortarjan85"></a>
## sleatortarjan85

Daniel D. Sleator, Robert E. Tarjan. “Amortized Efficiency of List Update and Paging Rules.” *Communications of the ACM* 28(2), 202–208, 1985. https://doi.org/10.1145/2786.2793 ; author PDF https://www.cs.cmu.edu/~sleator/papers/amortized-efficiency.pdf . Paging scope and equal-capacity specialization checked against source and local mapping. The list-update cost model of Section 2, Theorem 1 (`C_MF(s) ≤ 2C_A(s) + X_A(s) − F_A(s) − m`) and the remark after its proof (different initial lists, plus the initial inversion count) were checked against the author PDF on 2026-11-07 UTC.

<a id="stoerwagner97"></a>
## stoerwagner97

Mechthild Stoer and Frank Wagner. "A Simple Min-Cut Algorithm." *Journal of the ACM* 44(4), 585–591, 1997. https://doi.org/10.1145/263867.263872 . Bibliographic metadata checked against the Crossref record on 2026-11-08. The publisher's PDF returned HTTP 403 and was not retried, so the paper was not inspected. Its numbering (the phase recursion as Theorem 2.1, the cut-of-the-phase lemma as Lemma 3.1) comes from secondary descriptions and is unverified, which is why the Lean docstrings name the results rather than the numbers. The 8-vertex example graph in `ComplexityTests/StoerWagner.lean` and the trace of the worked example's first phase come from the English Wikipedia article "Stoer–Wagner algorithm", consulted on 2026-11-08, not from the paper's figure. A. Frank's note on MA orderings was unreachable (connection failure), and the corresponding section of Schrijver's 2003 monograph was not consulted; neither is cited.

<a id="sudantrevisanvadhan01"></a>
## sudantrevisanvadhan01

Madhu Sudan, Luca Trevisan and Salil Vadhan. *Pseudorandom Generators without the XOR Lemma*. Journal of Computer and System Sciences 62(2), 236–266, 2001. DOI: [10.1006/jcss.2000.1730](https://doi.org/10.1006/jcss.2000.1730). Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; the proof-route attribution comes from the pinned Lean module.

<a id="tarjan72"></a>
## tarjan72

Robert Endre Tarjan. "Depth-First Search and Linear Graph Algorithms." *SIAM Journal on Computing* 1(2), 146–160, 1972. https://doi.org/10.1137/0201010 . Bibliographic data from the DOI record; the paper was not inspected in this pass.

<a id="thaler22"></a>
## thaler22

Justin Thaler. *Proofs, Arguments, and Zero-Knowledge*. Foundations and Trends in Privacy and Security 4(2–4), 117–660, 2022. https://doi.org/10.1561/3300000030 . Later author manuscript consulted: https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf , dated 18 July 2023, §§4.1, 4.6.

<a id="thorup13"></a>
## thorup13

Mikkel Thorup. “Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence.” *FOCS 2013*, 90–99. https://doi.org/10.1109/FOCS.2013.18 ; author preprint https://arxiv.org/abs/1311.3121v2 . Bibliographic record checked; the formalization's quantitative adaptation is grounded in the pinned abstract and library source.

<a id="toda1991"></a>
## toda1991

Seinosuke Toda. “PP Is as Hard as the Polynomial-Time Hierarchy.” *SIAM Journal on Computing* 20(5), 865–877 (1991). Publisher abstract inspected 2026-11-01: https://doi.org/10.1137/0220053.

<a id="vww18"></a>
## vww18

Virginia Vassilevska Williams and R. Ryan Williams. "Subcubic Equivalences Between Path, Matrix, and Triangle Problems." *Journal of the ACM* 65(5), 27:1–27:38, 2018; preliminary version in FOCS 2010. https://doi.org/10.1145/3186893 . Bibliographic metadata checked on 2026-11-07; the manual cites it only as the standard reference for the APSP class and the negative-triangle equivalence, without a theorem locator.

<a id="wattenhofer16"></a>
## wattenhofer16

Roger Wattenhofer. *Principles of Distributed Computing*, lecture notes, ETH Zürich, Chapter 7 "Maximal Independent Set". https://disco.ethz.ch/courses/podc_allstars/lecture/chapter7.pdf (PDF dated 2016-08-23). Inspected 2026-11-08: Algorithm 7.12 ("Fast MIS 2"), Lemma 7.14 (edge removal), Theorem 7.15, Corollary 7.18 and the chapter notes, which attribute the algorithm to Métivier, Robson, Saheb-Djahromi and Zemmari (Distributed Computing 23(5–6), 2011) as a simplification of Luby (SIAM J. Comput. 15(4), 1986). Those two papers were not inspected.

<a id="williams25"></a>
## williams25

R. Ryan Williams. *Simulating Time With Square-Root Space*. arXiv:2502.17779v1 (25 February 2025), Appendix A, equation (6); version states to appear in STOC 2025. https://arxiv.org/abs/2502.17779v1 .

<a id="williamsonshmoys11"></a>
## williamsonshmoys11

David P. Williamson and David B. Shmoys. *The Design of Approximation Algorithms*. Cambridge University Press, 2011. https://doi.org/10.1017/CBO9780511921735 . Section 1.6 (Algorithm 1.2, Theorems 1.11 and 1.12) and the Chapter 1 Chapter Notes attribution of the greedy set-cover analysis to Chvátal (Mathematics of Operations Research 4(3), 233–235, 1979, https://doi.org/10.1287/moor.4.3.233) were checked against the authors' electronic edition at https://www.designofapproxalgs.com on 2026-11-07, as were Section 2.4 (Lemma 2.10, Theorems 2.11 and 2.12) and the Chapter 2 Chapter Notes, which attribute nearest addition and its analysis to Rosenkrantz, Stearns and Lewis (1977) and call the double-tree algorithm folklore. The handshake argument, Theorem 2.13 (Christofides' algorithm is a 3/2-approximation) and its proof, and the Chapter 2 Notes attribution to Christofides (reference [73]) were checked against the same edition on 2026-11-08.

<a id="younger67"></a>
## younger67

Daniel H. Younger. "Recognition and Parsing of Context-Free Languages in Time n³." *Information and Control* 10(2), 189–208, 1967. https://doi.org/10.1016/S0019-9958(67)80007-X . Bibliographic metadata was checked on 2026-11-08; the article body was not inspected. It is cited, with [Kasami 1965](#kasami65), as an original source of the CYK algorithm.
