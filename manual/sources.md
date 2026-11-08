# Primary sources and provenance

Repository citations are pinned to the reviewed source or dependency revision. Direct declaration links in the chapter text identify the supporting statement. The [library bibliography](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/references.bib) is linked at the survey revision; inclusion there is not a claim that this review checked every cited paper. Mathematical attributions reported only from source annotations are identified as such in the chapters.

The private-transcript sources are described in [the extraction methods](development-history/methods.md); selected excerpts are included in the manual, while their bulk exports remain untracked. Public GitHub issues, PRs and CI runs are linked from [development history](development-history/index.md). Refetching mutable records is not an archive of their historical contents. Inaccessible sources and unavailable archives are identified below or in the relevant chapter.

<a id="aaronson20"></a>
## aaronson20

Scott Aaronson. *The Busy Beaver Frontier*. ACM SIGACT News 51(3), 32–54, 2020. https://doi.org/10.1145/3427361.3427369 ; author's version https://www.scottaaronson.com/papers/bb.pdf . Read in the author's version on 2026-11-08: Proposition 1 (oracle access to any upper bound on the shift function solves the halting problem, hence no such bound is computable; the library proves the unrelativized corollary) and Proposition 2 (the shift function eventually exceeds every computable function). Both are stated for Turing machines; Section 2 notes that they hold in any universal model of computation. Section 1 defines `BB_L` for a programming language `L` with bit-string programs (and a variant through Kolmogorov complexity), the closest analogue of the library's code-size version. Journal pagination was taken from the bibliographic record.

<a id="abukhzam2007"></a>
## abukhzam2007

Faisal N. Abu-Khzam, Michael R. Fellows, Michael A. Langston and W. Henry Suters. "Crown Structures for Vertex Cover Kernelization." *Theory of Computing Systems* 41(3), 411–430, 2007. https://doi.org/10.1007/s00224-007-1328-0 . Bibliographic data and the abstract (crown structures; a crown-based kernelization compared with the LP-based one) were checked against secondary search summaries on 2026-11-08 UTC. The full text was not inspected, and the crown definition used in [Crown](../Complexity/Foundations/Combinatorics/SimpleGraph/Crown.lean) is not attributed to a numbered statement there. Chor, Fellows and Juedes, "Linear Kernels in Linear Time, or How to Save k Colors in O(n²) Steps", WG 2004, LNCS 3353, 257–269, https://doi.org/10.1007/978-3-540-30559-0_22, is cited in the module docstring on the same basis.

<a id="achlioptas03"></a>
## achlioptas03

Dimitris Achlioptas. “Database-Friendly Random Projections: Johnson–Lindenstrauss with Binary Coins.” *Journal of Computer and System Sciences* 66(4), 671–687, 2003. https://doi.org/10.1016/S0022-0000(03)00025-4 . Author-hosted copy of the typeset journal version: https://cgi.di.uoa.gr/~optas/papers/jl.pdf . Checked against that copy on 2026-11-07 UTC: Theorem 1.1 on p. 673 (squared distances within `1 ± ε` with probability at least `1 - n^(-β)` for `k ≥ k₀ = (4 + 2β) log n / (ε²/2 - ε³/3)`, stated for all `ε, β > 0`; the `±1` distribution is (1)). Also checked: Lemma 4.1 on p. 679 (Gaussian entries), Lemma 5.1 on p. 679 (the per-vector tails), and Lemma 5.2 on p. 680, eqs. (6)–(7) (the bounds on `𝔼 exp (h Q²)` and `𝔼 Q⁴`).

<a id="ahocorasick75"></a>
## ahocorasick75

Alfred V. Aho, Margaret J. Corasick. "Efficient String Matching: An Aid to Bibliographic Search." *Communications of the ACM* 18(6), 333–340, 1975. https://doi.org/10.1145/360825.360855 . Scanned copy in D. J. Bernstein's bibliography archive, https://cr.yp.to/bib/1975/aho.pdf , checked 2026-11-08 for Algorithms 1 and 3, Lemmas 1–3, Theorems 1, 2 and 4, and Figures 1 and 2.

<a id="alonbabaisuzuki1991"></a>
## alonbabaisuzuki1991

Noga Alon, László Babai and Hiroshi Suzuki. “Multilinear Polynomials and Frankl–Ray-Chaudhuri–Wilson Type Intersection Theorems.” *Journal of Combinatorial Theory, Series A* 58(2), 165–180, 1991. https://doi.org/10.1016/0097-3165(91)90058-O . Bibliographic metadata from search summaries on 2026-11-08; the full text was not inspected in this pass. The manual attributes only the multilinear polynomial method for uniform and nonuniform restricted-intersection bounds to this paper; theorem numbers are not cited.

<a id="alonmatiasszegedy99"></a>
## alonmatiasszegedy99

Noga Alon, Yossi Matias, Mario Szegedy. “The Space Complexity of Approximating the Frequency Moments.” *Journal of Computer and System Sciences* 58(1), 137–147, 1999; preliminary version in STOC 1996. https://doi.org/10.1006/jcss.1997.1545 . Author-hosted copy of the journal version: https://www.tau.ac.il/~nogaa/PDFS/amsz4.pdf . An independent agent review checked the theorem locators and statements (Theorem 2.2 for the `F₂` sketch, Proposition 3.1 for the `F∞` lower bound) against that copy on 2026-11-07 UTC. The JCSS page numbers were taken from secondary search summaries and were not checked against the typeset journal PDF.

<a id="alonyusterzwick1995"></a>
## alonyusterzwick1995

Noga Alon, Raphael Yuster, Uri Zwick. "Color-Coding." *Journal of the ACM* 42(4), 844–856, 1995. https://doi.org/10.1145/210332.210337 . Bibliographic data from the DOI record. The locator Lemma 3.1 (colorful paths by dynamic programming over color sets) was taken from secondary descriptions; the full text was not inspected in this pass.

<a id="anshelevichdktwr08"></a>
## anshelevichdktwr08

Elliot Anshelevich, Anirban Dasgupta, Jon Kleinberg, Éva Tardos, Tom Wexler and Tim Roughgarden. *The Price of Stability for Network Design with Fair Cost Allocation*. SIAM Journal on Computing 38(4), 1602–1623, 2008; preliminary version in FOCS 2004. https://doi.org/10.1137/070680096 . Bibliographic metadata only, as given in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, reference [1]; the DOI was taken from a search summary. The paper's text was not inspected (the author-hosted copies tried returned 404), so no locator in it is cited. The `H_k` price-of-stability theorem is attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Theorem 2.1, and proved following [tardoswexler07](#tardoswexler07), §19.3.

<a id="apostolicobreslauergalil95"></a>
## apostolicobreslauergalil95

Alberto Apostolico, Dany Breslauer and Zvi Galil. "Parallel Detection of All Palindromes in a String." *Theoretical Computer Science* 141(1–2), 163–173, 1995. https://doi.org/10.1016/0304-3975(94)00083-U . Locators refer to the preliminary version, INRIA Research Report RR-2136, 1993, open copy https://inria.hal.science/inria-00074536 , checked on 2026-11-08 UTC. Section 1 defines even and odd palindromes of radius `R` centered at a position and the maximal radii at all positions; the manual's center convention is translated from these definitions. Section 1 also states that Manacher's algorithm computes the maximal radii at all positions in linear time. The journal text was not inspected.

<a id="baloghbekesidosaepsteinlevin18"></a>
## baloghbekesidosaepsteinlevin18

János Balogh, József Békési, György Dósa, Leah Epstein and Asaf Levin. *A new lower bound for classic online bin packing*. arXiv:1807.05554v1, 2018. https://arxiv.org/abs/1807.05554 ; published in *Algorithmica* 83(7), 2047–2062, 2021, https://doi.org/10.1007/s00453-021-00818-7 (bibliographic data from the Crossref record; the locators follow arXiv v1). Worker w156-ff read the arXiv version on 2026-11-08 UTC. Section 1 reports that Yao's first lower bound on the asymptotic competitive ratio uses at most three types of items, `1/7 + ε`, `1/3 + ε` and `1/2 + ε`; it does not state the value of that bound. It also reports the later bounds of Brown and Liang (`1.53635`), van Vliet (`1.5401474`) and Balogh, Békési and Galambos (`248/161`). The library's [OnlineLowerBound](../Complexity/Algorithms/Lean/BinPacking/OnlineLowerBound.lean) module takes its item types from this report.

<a id="barak-steurer16"></a>
## barak-steurer16

Boaz Barak and David Steurer. *Proofs, beliefs, and algorithms through the lens of sum-of-squares*. Lecture notes, 2016, https://www.sumofsquares.org/ . On 2026-11-08 UTC worker w96-sos consulted these author-hosted lectures: "Mathematical definitions" (https://www.sumofsquares.org/public/lec01-2_definitions.pdf), for Theorem 19, the duality of sum-of-squares certificates and pseudo-distributions; "The sos algorithm over general domains" (https://www.sumofsquares.org/public/lec-definitions-general.pdf), for Definition 1 (sos proofs), the remark after Theorem 2 (degree-`d` sos refutations), Definitions 5 and 7 (pseudo-distributions and the constraints they satisfy) and Theorem 8; and "Higher-degree integrality gaps" (https://www.sumofsquares.org/public/lec03-2_lowerbounds_csp.pdf), for Theorem 2, Lemmas 7 and 9, and Lemma 24 (Grigoriev's bound for Tseitin tautologies on vertex expanders). The sum-of-squares modules cite these locators. The notes are a living document, and the numbering may change.

<a id="barrett26"></a>
## barrett26

Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker and Sorrachai Yingchareonthawornchai. *CSLib: The Lean Computer Science Library*. arXiv:2602.04846v1, 2026. https://doi.org/10.48550/arXiv.2602.04846 . Author/title/version metadata checked against https://arxiv.org/abs/2602.04846 on 2026-11-02 UTC.

<a id="bcgl92"></a>
## bcgl92

Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby. *On the Theory of Average Case Complexity*. Journal of Computer and System Sciences 44(2), 193–219, 1992; preliminary version in STOC 1989. https://doi.org/10.1016/0022-0000(92)90019-F . Bibliographic metadata checked against the Crossref record on 2026-11-08. The primary text was not inspected, and no theorem number is claimed. The manual attributes to this paper only the implication `DistNP ⊆ AvgP ⇒ NE = E`, as reported by [bm15](#bm15), §5.

<a id="bcs16"></a>
## bcs16

Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner. *Interactive Oracle Proofs*. TCC 2016-B II, 31–60. https://doi.org/10.1007/978-3-662-53644-5_2 .

<a id="beigelgill92"></a>
## beigelgill92

Richard Beigel and John Gill. "Counting Classes: Thresholds, Parity, Mods, and Fewness." *Theoretical Computer Science* 103(1), 3–23, 1992. https://doi.org/10.1016/0304-3975(92)90084-S ; the author's full version (dated June 10, 1996) is linked from https://cis.temple.edu/~beigel/papers/bg-mods-tcs.html . Checked against that author's version on 2026-11-08 UTC by worker w167-modpe: Property 8(ii) (binomial coefficients `C(f, g)` of #P functions with polynomially bounded UPF `g` are in #P), Corollary 20 (`C(n, p^k) ≢ 0 mod p` iff the base-`p` digit of `n` at `p^k` is nonzero), Proposition 29 (`j ∣ k` gives `MOD_jP ⊆ MOD_kP`) and Theorem 30 (`MOD_{k^i}P = MOD_kP` for prime `k` and `i ≥ 1`). Numbering follows the author's version; the journal pagination is from the DOI record and the typeset journal numbering was not checked.

<a id="bellman58"></a>
## bellman58

Richard Bellman. "On a Routing Problem." *Quarterly of Applied Mathematics* 16(1), 87–90, 1958. https://doi.org/10.1090/qam/102435 . Bibliographic data from the DOI record and secondary summaries; the paper was not inspected in this pass.

<a id="bennett89"></a>
## bennett89

Charles H. Bennett. *Time/Space Trade-Offs for Reversible Computation*. SIAM Journal on Computing 18(4), 766–776, 1989. https://doi.org/10.1137/0218053 . Bibliographic metadata only; the paper was not inspected in this pass. The manual credits it with the recursive checkpointing strategy as described in [ltv98](#ltv98), Sections 6 and 7.

<a id="berge57"></a>
## berge57

Claude Berge. *Two Theorems in Graph Theory*. Proceedings of the National Academy of Sciences of the United States of America 43(9), 842–844, 1957. https://doi.org/10.1073/pnas.43.9.842 . Bibliographic metadata only; the primary text was not inspected. The manual attributes to this paper the augmenting-path characterization of maximum matchings; the "Theorem 1" locator comes from secondary descriptions and is unverified. Schrijver's lecture notes ([schrijver17](#schrijver17), Theorem 3.2) state the result without attribution.

<a id="berge58"></a>
## berge58

Claude Berge. *Sur le couplage maximum d'un graphe*. Comptes Rendus Hebdomadaires des Séances de l'Académie des Sciences 247, 258–259, 1958. Bibliographic data from secondary bibliographies; the note was not inspected, and no theorem number is claimed. The manual attributes to it the Tutte–Berge formula, following [schrijver17](#schrijver17), Section 5.1.

<a id="bermanhartmanis75"></a>
## bermanhartmanis75

Leonard Berman and Juris Hartmanis. *On Isomorphisms and Density of NP and Other Complete Sets*. Technical Report TR75-260, Department of Computer Science, Cornell University, October 1975. https://hdl.handle.net/1813/7101 . The open eCommons PDF is an image scan without a text layer. An independent agent review checked these locators against it on 2026-11-08 UTC: §I, printed p. 2 (the isomorphism conjecture and its `P ≠ NP` consequence); §III, Theorem 1, printed pp. 7–10 (PDF pp. 10–13; isomorphism from invertible, length-increasing one-one reductions); Lemmas 3 and 5, printed pp. 10–12 (length growth and the two-argument padding and read-back condition); and Theorem 7 with its CNF construction, printed pp. 13–14. The journal version (*SIAM Journal on Computing* 6(2), 305–322, 1977, https://doi.org/10.1137/0206023) was not checked, and its numbering is not claimed to match.

<a id="bertsekas88"></a>
## bertsekas88

Dimitri P. Bertsekas. "The auction algorithm: A distributed relaxation method for the assignment problem." *Annals of Operations Research* 14, 105–123, 1988. https://doi.org/10.1007/BF02186476 . Author-hosted scan: https://web.mit.edu/dimitrib/www/TheAuctionAP.pdf . The original algorithm is the MIT LIDS working paper "A Distributed Algorithm for the Assignment Problem" (March 1979), retyped at https://web.mit.edu/dimitrib/www/Bertsekas_Auction_Distributed_1979.pdf . The manual uses the 1988 paper for the `O(N A C / ε)` complexity of the pure (unscaled) auction (§1) and for scaling integer costs by `N + 1` and running down to `ε = 1` (§3). Both locators were checked against the author-hosted scan on 2026-11-08 UTC.

<a id="bertsekas98"></a>
## bertsekas98

Dimitri P. Bertsekas. *Network Optimization: Continuous and Discrete Models*. Athena Scientific, Belmont, MA, 1998. ISBN 1-886529-02-7. Author-hosted copy: https://web.mit.edu/dimitrib/www/netbook_Full_Book_NEW.pdf . Checked against that copy on 2026-11-08 UTC: §1.3.3 and Prop. 1.4 (an assignment satisfying `ε`-complementary slackness is within `n ε` of optimal); §7.1.1, ε-CS (7.1), the bidding rule (7.2)–(7.5) with the Gauss–Seidel version, Prop. 7.1 (ε-CS is preserved) and Prop. 7.2 (termination, `n ε`-optimality, optimality for integer data and `ε < 1/n`); Figs. 1.12–1.14 (the price-war example); §7.1.4 and Prop. 7.3 (`ε`-scaling, not formalized).

<a id="bfprt73"></a>
## bfprt73

Manuel Blum, Robert W. Floyd, Vaughan Pratt, Ronald L. Rivest and Robert E. Tarjan. *Time Bounds for Selection*. Journal of Computer and System Sciences 7(4), 448–461, 1973. https://doi.org/10.1016/S0022-0000(73)80033-9 . Bibliographic metadata and the abstract's `5.4305 n` comparison bound for `PICK` were checked through secondary search results on 2026-11-08; the paper's text was not read. The manual attributes to this paper only the median-of-medians selection algorithm and that constant. The groups-of-five accounting in the Lean files follows the presentation in [clrs09](#clrs09), Section 9.3, which was not checked against the printed book.

<a id="bhr12"></a>
## bhr12

Mihir Bellare, Viet Tung Hoang, Phillip Rogaway. "Foundations of Garbled Circuits." *Proceedings of the 2012 ACM Conference on Computer and Communications Security (CCS '12)*, 784–796, 2012. https://doi.org/10.1145/2382196.2382279 . Full version: Cryptology ePrint Archive, Report 2012/265. Bibliographic data from the DOI record and secondary listings. The ePrint copy returned HTTP 403 and the ACM page sat behind a bot challenge in this pass, so no theorem or definition numbers are claimed. The garbling-scheme syntax and simulation-based privacy with topology side information are cited at paper level only.

<a id="bjkst02"></a>
## bjkst02

Ziv Bar-Yossef, T. S. Jayram, Ravi Kumar, D. Sivakumar, Luca Trevisan. “Counting Distinct Elements in a Data Stream.” *Randomization and Approximation Techniques in Computer Science (RANDOM 2002)*, LNCS 2483, 1–10, Springer, 2002. https://doi.org/10.1007/3-540-45726-7_1 . Author-hosted copy: https://webee.technion.ac.il/people/zivby/papers/f0/f0.ps . Locators checked against that copy on 2026-11-08 UTC: Section 2 (the first algorithm) and Theorem 1. The algorithm picks a pairwise independent hash `h : [m] → [M]` with `M = m³` and keeps the `t = ⌈96/ε²⌉` smallest distinct hash values. It outputs `tM/v`, where `v` is the `t`-th smallest value. Each tail is bounded by `1/6` via Chebyshev, plus `1/m` for collisions, and the median of `O(log(1/δ))` copies gives `O(1/ε² · log m · log(1/δ))` bits. The LNCS page numbers come from the DOI record and were not checked against the typeset volume.

<a id="bland77"></a>
## bland77

Robert G. Bland. "New Finite Pivoting Rules for the Simplex Method." *Mathematics of Operations Research* 2(2), 103–107, 1977. https://doi.org/10.1287/moor.2.2.103 . Bibliographic data from the DOI record and search summaries; the paper was not inspected in this pass, and no theorem number is claimed. The manual credits it with the smallest-subscript pivoting rule and its finiteness; the formalized no-cycling proof is the standard largest-fickle-variable argument as presented in textbooks such as [chvatal83](#chvatal83), Chapter 3.

<a id="blum67"></a>
## blum67

Manuel Blum. *A Machine-Independent Theory of the Complexity of Recursive Functions*. Journal of the ACM 14(2), 322–336, 1967. https://doi.org/10.1145/321386.321395 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the two axioms, recursive relatedness and the speed-up theorem to this paper. The manual also mentions the customary attribution of the measure-independent theorem on arbitrarily complex functions to this paper (and to Rabin, 1960); that attribution and any theorem locator are unverified.

<a id="bm15"></a>
## bm15

Markus Bläser and Bodo Manthey. *Smoothed Complexity Theory*. ACM Transactions on Computation Theory 7(2), Article 6, 2015; preliminary version in MFCS 2012. https://doi.org/10.1145/2656210 ; arXiv:1202.1936. Read in arXiv v2 (29 June 2012) on 2026-11-08. §5, in the paragraph before Theorem 5.2, attributes `DistNP ⊆ Avg-P ⇒ NE = E` to Ben-David, Chor, Goldreich and Luby. Journal metadata checked against the Crossref record.

<a id="bmr90"></a>
## bmr90

Donald Beaver, Silvio Micali, Phillip Rogaway. "The Round Complexity of Secure Protocols." *Proceedings of the 22nd Annual ACM Symposium on Theory of Computing (STOC '90)*, 503–513, 1990. https://doi.org/10.1145/100216.100287 . Bibliographic data from the DOI record and secondary listings, cited as the usual source of the point-and-permute technique. The full text was not inspected in this pass.

<a id="bodlaenderjansenkratsch2014"></a>
## bodlaenderjansenkratsch2014

Hans L. Bodlaender, Bart M. P. Jansen and Stefan Kratsch. "Kernelization Lower Bounds by Cross-Composition." *SIAM Journal on Discrete Mathematics* 28(1), 277–305, 2014. https://doi.org/10.1137/120880240 . Inspected the arXiv version [1206.5941v1](https://arxiv.org/abs/1206.5941v1) on 2026-11-08: Definition 1 (kernelization, generalized kernelization, p. 4), Definition 2 (compression, p. 5), Proposition 1 (p. 5), Definition 4 (weak OR-distillation, p. 5), Theorem 2 (Fortnow–Santhanam, p. 6), Lemma 1 (complementary witness lemma, attributed to Dell and van Melkebeek, p. 7), Definition 8 (polynomial equivalence relation, p. 8), Definition 9 (and/or-cross-composition, p. 8), Theorem 5 and Corollary 2 (p. 9) and Theorem 6 with its proof (pp. 10–11). Locators follow that arXiv numbering; the journal numbering was not checked.

<a id="borodin72"></a>
## borodin72

Allan Borodin. *Computational Complexity and the Existence of Complexity Gaps*. Journal of the ACM 19(1), 158–174, 1972. https://doi.org/10.1145/321679.321691 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the gap theorem and the almost-everywhere class convention to this paper.

<a id="borodinelyaniv98"></a>
## borodinelyaniv98

Allan Borodin, Ran El-Yaniv. *Online Computation and Competitive Analysis*. Cambridge University Press, 1998. The chapter outline, in particular Chapter 1 on list accessing, comes from the publisher's table of contents; the book text was not inspected in this pass. The manual cites it only as a textbook pointer for ski rental and for the deterministic list-accessing lower bound, with no theorem numbers.

<a id="bregman73"></a>
## bregman73

L. M. Brégman. "Some properties of nonnegative matrices and their permanents." *Soviet Mathematics Doklady* 14, 945–949, 1973; translated from *Doklady Akademii Nauk SSSR* 211, 27–30, 1973. Bibliographic data from secondary sources; the paper was not inspected. The manual credits it only with the statement of the bound `per A ≤ ∏ i, (r i)! ^ (1 / r i)` for 0/1 matrices.

<a id="broder97"></a>
## broder97

Andrei Z. Broder. “On the Resemblance and Containment of Documents.” *Proceedings of Compression and Complexity of Sequences 1997* (SEQUENCES 1997), IEEE, 21–29. https://doi.org/10.1109/SEQUEN.1997.666900 . DOI and metadata as reported by search indexes; neither the DOI nor the full text was resolved in this pass (no connection to the publisher). The manual credits it with the MinHash identity `Pr[min σ(A) = min σ(B)] = |A ∩ B|/|A ∪ B|` for a uniform permutation, which secondary sources attribute to it.

<a id="bs23"></a>
## bs23

Dan Boneh and Victor Shoup. *A Graduate Course in Applied Cryptography*, version 0.6, January 2023. https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf . Title, authors and edition verified from the primary PDF during independent source review on 2026-11-02. Detailed textbook locator claims remain attributed to the Lean source docstrings; no complete textbook correspondence audit was performed.

<a id="bt06"></a>
## bt06

Andrej Bogdanov and Luca Trevisan. *Average-Case Complexity*. Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006. https://doi.org/10.1561/0400000004 ; arXiv:cs/0606037. Definition, lemma and theorem numbers (Definitions 1, 2, 6, 8–11 and 17, Proposition 7, Lemma 18, Theorem 19, Claim 20) were checked against the arXiv text on 2026-11-07.

<a id="canetti20"></a>
## canetti20

Ran Canetti. *Universally Composable Security*. Journal of the ACM 67(5), Article 28, 2020; full version Cryptology ePrint Archive 2000/067. https://doi.org/10.1145/3402457 .

<a id="ccpv11"></a>
## ccpv11

Gruia Călinescu, Chandra Chekuri, Martin Pál, Jan Vondrák. “Maximizing a Monotone Submodular Function subject to a Matroid Constraint.” *SIAM Journal on Computing* 40(6), 1740–1766, 2011. https://doi.org/10.1137/080733991 . The `p`-system definition and the greedy ratios `1/p` (modular) and `1/(p+1)` (monotone submodular) in Section 1, and the proof of the `1/(p+1)` bound in Appendix B (“Analysis of Greedy for p-systems”), were checked on 2026-11-08 against the authors' manuscript dated September 21, 2009, at https://theory.stanford.edu/~jvondrak/data/submod-matroid.pdf ; the journal pagination was not checked. The manual reports the original Fisher–Nemhauser–Wolsey and Jenkyns attributions as stated in this paper.

<a id="cgks98"></a>
## cgks98

Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan. *Private Information Retrieval*. Journal of the ACM 45(6), 965–981, 1998; preliminary version FOCS 1995. https://doi.org/10.1145/293347.293350 . Definition 1 (§2.1), the schemes of §§3.1, 3.2 and 3.4 (Proposition 4, Corollary 3), the covering-code schemes of §3.3 (Theorem 1, its footnote on exact covers, Corollary 2; pp. 8–10), the single-server bound of §5.1 in its one-round and interactive forms, and §5.2 (the Claim, its two observations and the closing note on the even-set scheme) were checked on 2026-11-08 against the authors' journal version of April 21, 1998, at http://people.csail.mit.edu/madhu/papers/1995/pir-journ.pdf (§5 is on pp. 13–15). In the interactive form, the user's output may depend on its coins, so the source's step that the same communication forces the same output is replaced by the rectangle property of protocols. The typeset JACM PDF was not consulted; locators follow the authors' version.

<a id="chaitin74"></a>
## chaitin74

Gregory J. Chaitin. *Information-Theoretic Limitations of Formal Systems*. Journal of the ACM 21(3), 403–424, 1974. https://doi.org/10.1145/321832.321839 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected. The manual attributes the incompleteness theorem for program-size complexity to it, following the customary attribution; its theorem numbers and the exact form of its bound are unverified. The Lean docstrings also cite the textbook treatment in Li and Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th edition (Springer, 2019), Chapter 2; the section and theorem locator within that chapter was not checked.

<a id="chakrabarti25"></a>
## chakrabarti25

Amit Chakrabarti. *Data Stream Algorithms: Lecture Notes*. Dartmouth College, latest update July 1, 2025. https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf . Locators checked against that PDF on 2026-11-07 UTC: Unit 1 (Section 1.1 for the MAJORITY and FREQUENT problems, Algorithm 1 and Theorem 1.3.1 for Misra–Gries, Exercise 1-1 for the `(m − m̂)/k` sharpening), Section 2.4 (the median trick) and Section 5.3 (Algorithms 7–8 and equations (5.1)–(5.7) for the Count-Sketch).

<a id="charikar02"></a>
## charikar02

Moses S. Charikar. “Similarity Estimation Techniques from Rounding Algorithms.” *Proceedings of the 34th Annual ACM Symposium on Theory of Computing* (STOC 2002), 380–388. https://doi.org/10.1145/509907.509965 . DOI and metadata as reported by search indexes; the DOI was not resolved in this pass. The locator Lemma 1 (for a similarity admitting a locality-sensitive hashing scheme, `1 − sim` satisfies the triangle inequality) was not checked against the full text in this pass.

<a id="charikar04"></a>
## charikar04

Moses Charikar, Kevin Chen, Martin Farach-Colton. “Finding Frequent Items in Data Streams.” *Theoretical Computer Science* 312(1), 3–15, 2004; preliminary version in ICALP 2002. https://doi.org/10.1016/S0304-3975(03)00400-6 . Bibliographic data from search summaries of the DOI record; the Count-Sketch statements formalized here follow the presentation of [chakrabarti25](#chakrabarti25), Section 5.3. The journal text was not inspected in this pass.

<a id="chattopadhyayliao20"></a>
## chattopadhyayliao20

Eshan Chattopadhyay and Jyun-Jie Liao. *Optimal Error Pseudodistributions for Read-Once Branching Programs*. 35th Computational Complexity Conference (CCC 2020), LIPIcs 169, 25:1–25:27, 2020. https://doi.org/10.4230/LIPIcs.CCC.2020.25 ; cited from arXiv:2002.07208v4. Appendix A.1 (Definition A.2, Lemmas A.3 and A.4) was checked against the arXiv v4 text on 2026-11-08. Hoza (2021) cites the CCC version's Lemma 43 for the same material.

<a id="christofides76"></a>
## christofides76

Nicos Christofides. *Worst-Case Analysis of a New Heuristic for the Travelling Salesman Problem*. Report 388, Graduate School of Industrial Administration, Carnegie-Mellon University, 1976; reprinted in *Operations Research Forum* 3, article 20, 2022, https://doi.org/10.1007/s43069-021-00101-z . The report details are those of reference [73] in [Williamson and Shmoys](#williamsonshmoys11), whose Chapter 2 Notes attribute the algorithm to Christofides; the reprint details come from search summaries. Neither the report nor the reprint was checked; the formalization follows the proof of Theorem 2.13 of Williamson and Shmoys.

<a id="chrobakkarloffpaynevishwanathan91"></a>
## chrobakkarloffpaynevishwanathan91

Marek Chrobak, Howard J. Karloff, Thomas H. Payne, Sundar Vishwanathan. "New Results on Server Problems." *SIAM Journal on Discrete Mathematics* 4(2), 172–181, 1991. https://doi.org/10.1137/0404017 . Bibliographic metadata only; the full text was not inspected in this pass, so no theorem number is cited. The manual credits this paper with the `k`-competitiveness of Double Coverage on the line, which secondary sources attribute to it; the local proof uses the standard potential `k·M_min + Σ_{i<j}|s_i - s_j|`.

<a id="chvatal83"></a>
## chvatal83

Vašek Chvátal. *Linear Programming*. W. H. Freeman, New York, 1983. Bibliographic data from library and search summaries; the book was not inspected in this pass. The chapter locators used in the manual and docstrings (Chapter 2 for dictionaries, pivoting and the optimality test; Chapters 2–3 for the unboundedness test, which search summaries of the table of contents place in Chapter 3; Chapter 3 for cycling, the cycling example and the smallest-subscript rule; Chapter 5 for duality and the dual solution read off the final dictionary) come from secondary summaries and memory of the book, not from a copy, and are unverified. The coefficients of the cycling example in `ComplexityTests/Algorithms/Lean/Simplex.lean` were taken from those summaries and checked by running Dantzig's rule on them, which returns to the initial basis after six degenerate pivots.

<a id="cks20"></a>
## cks20

Clément L. Canonne, Gautam Kamath and Thomas Steinke. *The Discrete Gaussian for Differential Privacy*. NeurIPS 2020; cited from arXiv:2004.00010v5, 2021. https://arxiv.org/abs/2004.00010 . Definition 28 and Lemmas 29–30 were checked against the arXiv v5 PDF on 2026-11-07.

<a id="clrs09"></a>
## clrs09

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest and Clifford Stein. *Introduction to Algorithms*, third edition. MIT Press, 2009. ISBN 978-0-262-03384-8. Section 35.1, procedure `APPROX-VERTEX-COVER` and Theorem 35.1 (it is a polynomial-time 2-approximation algorithm). The locator 35.1 was checked against secondary course material, not the printed book. Sections 22.3–22.4 (depth-first search; Lemma 22.11, acyclic if and only if no back edges; Theorem 22.12, correctness of `TOPOLOGICAL-SORT`) and Section 24.1 (Bellman–Ford; Lemma 24.2, estimates equal shortest-path weights after `|V| - 1` passes when no negative cycle is reachable; Theorem 24.4, correctness of `BELLMAN-FORD`) were likewise checked against secondary course material. Sections 25.1 ("Shortest paths and matrix multiplication": repeated (min,+) squaring) and 25.2 ("The Floyd–Warshall algorithm") are the all-pairs shortest-path locators. They were checked against the edition's published table of contents only. Section 26.4 ("Push-relabel algorithms") is the push–relabel locator. Its statement numbers were checked against secondary course material, not the printed book: Lemma 26.14 (an overflowing vertex admits a push or a relabel), Lemma 26.15 (heights never decrease, and a relabel raises them), Lemma 26.16 (push and relabel keep a height function), Lemma 26.17 (no residual `s`–`t` path), Theorem 26.18 (correctness at termination), Lemma 26.19 (an overflowing vertex reaches `s` in the residual network), Lemma 26.20 (heights stay below `2|V|`), Corollary 26.21 (fewer than `2|V|²` relabels), Lemmas 26.22 and 26.23 (fewer than `2|V||E|` saturating and fewer than `4|V|²(|V| + |E|)` nonsaturating pushes) and Theorem 26.24 (`O(|V|² |E|)` basic operations). Section 9.3 ("Selection in worst-case linear time") is the locator for the groups-of-five median-of-medians algorithm and its counting step; it was not checked against the printed book. Section 15.4 ("Longest common subsequence": Theorem 15.1, optimal substructure of an LCS, and the running example `ABCBDAB`, `BDCABA` with an LCS of length `4`) and Problem 15-5 ("Edit distance") are the edit-distance and LCS locators. They were checked against secondary course material, not the printed book.

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

<a id="correaschulzstiermoses04"></a>
## correaschulzstiermoses04

José R. Correa, Andreas S. Schulz and Nicolás E. Stier-Moses. *Selfish Routing in Capacitated Networks*. Mathematics of Operations Research 29(4), 961–976, 2004. https://doi.org/10.1287/moor.1040.0098 . Bibliographic metadata only; the publisher's text is paywalled and no open author's version was found, so it was not inspected and no locator in it is cited. Following [roughgarden13cs364a](#roughgarden13cs364a), Lecture #11, Theorem 3.3, which credits it, `Complexity/GameTheory/Congestion/PigouBound.lean` cites it for the Pigou-bound theorem in the generality formalized there.

<a id="coverthomas06"></a>
## coverthomas06

Thomas M. Cover and Joy A. Thomas. *Elements of Information Theory*, second edition. Wiley-Interscience, 2006. https://doi.org/10.1002/047174882X . Section 5.11, "Generation of discrete distributions from fair coins": Theorem 5.11.1 (`H(X) ≤ E[T]` for every generating tree), Theorem 5.11.2 (equality for dyadic distributions) and Theorem 5.11.3 (`H(X) ≤ E[T] < H(X) + 2` for the optimal tree). The theorem numbers and statements were taken from secondary summaries and course notes on 2026-11-08; the printed book was not inspected. Also cited for Section 2.10 (Fano's inequality: Theorem 2.10.1, the corollary after it with the sharper `log(|𝒳| − 1)` form for estimators valued in `𝒳`, and the remark on guessing without side information), Section 7.1 (capacity of the binary symmetric channel), Lemma 7.9.2 and Theorem 7.9.1 (the converse to the channel coding theorem); these locators were likewise checked against secondary course material, not the printed book.

Chapter 13 (universal source coding): the Lempel–Ziv tree-structured (incremental) parsing, its example `ABBABBABBBAABABAA`, and the distinct-parsing lemma `c(n) ≤ n / ((1 - ε_n) log n)` with `ε_n = min(1, (log log n + 4) / log n)` in §13.5. The library cites only the section; secondary sources disagree on the lemma's number. The section, the lemma's statement and the example were taken from secondary course material and search summaries and were not checked against the printed book.

<a id="cslib"></a>
## cslib

CSLib contributors. *CSLib*, pinned dependency snapshot `254e30e6d4299c51323aaeaf5f51a4763b375d4a`. [Pinned repository](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a).

<a id="cygan2015"></a>
## cygan2015

Marek Cygan, Fedor V. Fomin, Łukasz Kowalik, Daniel Lokshtanov, Dániel Marx, Marcin Pilipczuk, Michał Pilipczuk, and Saket Saurabh. *Parameterized Algorithms*. Springer, 2015. [DOI](https://doi.org/10.1007/978-3-319-21275-3). Inspected the authors' companion PDF dated 2016-05-30: Definitions 1.2–1.3 (p. 13), Definition 2.1 (pp. 18–19), Lemma 2.2 (p. 20), and Section 2.2.1 (pp. 21–22); accessed 2026-11-02. On 2026-11-08 the same PDF returned HTTP 403, so the crown material of Section 2.3 cited by [Crown](../Complexity/Foundations/Combinatorics/SimpleGraph/Crown.lean) was not inspected. Secondary sources number the crown lemma Lemma 2.14 and the `3k` kernel Theorem 2.16; these numbers are unverified and are not used in the Lean docstrings. The color-coding locators Section 5.2 and Lemma 5.5, the fpt-reduction locator Section 13.1, and the tree-decomposition locator Section 7.3.1 (weighted independent set, stated for `n`-vertex graphs), used in [parameterized complexity](machines-and-classes/parameterized-complexity.md), were not re-inspected.

<a id="dasguptagupta03"></a>
## dasguptagupta03

Sanjoy Dasgupta, Anupam Gupta. “An Elementary Proof of a Theorem of Johnson and Lindenstrauss.” *Random Structures & Algorithms* 22(1), 60–65, 2003. https://doi.org/10.1002/rsa.10073 . Author-hosted copy: https://cseweb.ucsd.edu/~dasgupta/papers/jl.pdf . Checked against that copy on 2026-11-07 UTC: Theorem 2.1 on p. 61 (`0 < ε < 1` and `k ≥ 4 (ε²/2 - ε³/3)⁻¹ ln n`), and Lemma 2.2 on p. 62 (tails for the projection of a random unit vector onto `k` coordinates, proved with `𝔼 exp (sX²) = (1 - 2s)^(-1/2)` for a standard Gaussian `X`).

<a id="diestel25"></a>
## diestel25

Reinhard Diestel. *Graph Theory*, sixth edition. Graduate Texts in Mathematics 173, Springer, 2025. The author's free preview chapters (https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch3.pdf and Ch1.pdf) were consulted on 2026-11-08 UTC for Section 1.4 (separating sets), Section 3.3, Corollary 3.3.5 (i) (vertex form, `ab ∉ E`) and (ii) (edge form), and the statements of Theorems 3.3.1 and 3.3.6, which are cited only as remaining work.

<a id="dinic70"></a>
## dinic70

E. A. Dinic. “Algorithm for Solution of a Problem of Maximum Flow in Networks with Power Estimation.” *Soviet Mathematics Doklady* 11, 1277–1280 (1970). This original paper was not consulted. The bibliographic data come from secondary citations, and the manual attributes to it only the level-network and blocking-flow method and its phase bound, as these are standardly described. Yefim Dinitz's historical account, “Dinitz' Algorithm: The Original Version and Even's Version” (in *Theoretical Computer Science: Essays in Memory of Shimon Even*, LNCS 3895, 218–240, Springer, 2006, https://doi.org/10.1007/11685654_10 ; bibliographic data checked against the Crossref record on 2026-11-08), is cited in the module docstrings for the history. Its text was not inspected: the author-hosted PDF's text layer could not be extracted.

<a id="dinur2007"></a>
## dinur2007

Irit Dinur. “The PCP Theorem by Gap Amplification.” *Journal of the ACM* 54(3), Article 12 (2007). DOI: https://doi.org/10.1145/1236457.1236459. Author copy dated 2007-02-13 inspected: https://www.wisdom.weizmann.ac.il/~dinuri/mypapers/combpcp.pdf (opening definition and Theorem 1.1).

<a id="dosasgall2013"></a>
## dosasgall2013

György Dósa and Jiří Sgall. "First Fit bin packing: A tight analysis." *30th International Symposium on Theoretical Aspects of Computer Science (STACS 2013)*, LIPIcs 20, 538–549, 2013. https://doi.org/10.4230/LIPIcs.STACS.2013.538 . Worker w156-ff read the open-access LIPIcs PDF on 2026-11-08 UTC and checked these parts: the weight function of Section 1.2 (scaled size `6/5 · a` plus a bonus); the observation there that every bin weighs at most `1.7`; Lemma 1.1, the amortization step; and the Section 1.1 history of the additive constants. [FirstFitWeight](../Complexity/Algorithms/Lean/BinPacking/FirstFitWeight.lean) cites these locators. The constant `+0.9` is credited there to Garey, Graham, Johnson and Yao (ref. [4]), and `+0.7` to Xia and Tan (ref. [15]); both attributions are reported only via this paper. The absolute bound `FF ≤ 1.7 · Opt` (Theorem 3.13) and the lower bounds of Section 4 (Lemma 4.1, Theorem 4.2) were read but are not formalized. The small instances for `Opt ≤ 9` at the end of the proof of Theorem 4.2 (`i` items each of sizes `1/6 - 2δ`, `1/3 + δ` and `1/2 + δ`) are checked for `i = 3` and `i = 9` in [BinPackingFirstFitWeight](../ComplexityTests/BinPackingFirstFitWeight.lean).

<a id="dworkroth14"></a>
## dworkroth14

Cynthia Dwork and Aaron Roth. *The Algorithmic Foundations of Differential Privacy*. Foundations and Trends in Theoretical Computer Science 9(3–4), 211–407, 2014. https://doi.org/10.1561/0400000042 . Definition 2.4, Proposition 2.1, Theorem 2.2 and its footnote, §2.3, Claim 3.5, Theorem 3.16, Definition 3.7, Theorem 3.20, Corollary 3.21, Theorem B.1 and Corollary B.2 were checked against the published PDF on 2026-11-07. Lemma 8.4 and Corollary 8.5 (p. 165), Theorem 8.7 (p. 166), Theorem 8.8 with its proof and Claim 8.9 (pp. 167–169), and the bibliographic notes of §8.3, which credit Theorem 8.8 to De (p. 171), were checked on 2026-11-08 against the authors' open version (https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf), whose page numbers these are.

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

<a id="fnw78"></a>
## fnw78

Marshall L. Fisher, George L. Nemhauser, Laurence A. Wolsey. “An Analysis of Approximations for Maximizing Submodular Set Functions—II.” *Mathematical Programming Study* 8, 73–87, 1978. https://doi.org/10.1007/BFb0121195 . Bibliographic data from the DOI record; the paper is paywalled and its full text was not inspected. The manual attributes to it only the greedy `1/2` (matroid) and `1/(p+1)` (intersection of `p` matroids) bounds, following [Călinescu et al.](#ccpv11), Section 1 and Appendix B.

<a id="fortnowsanthanam2011"></a>
## fortnowsanthanam2011

Lance Fortnow and Rahul Santhanam. "Infeasibility of Instance Compression and Succinct PCPs for NP." *Journal of Computer and System Sciences* 77(1), 91–106, 2011. https://doi.org/10.1016/j.jcss.2010.06.007 . Bibliographic data from the DOI record. The paper was not inspected in this pass; the manual cites the statement of its distillation theorem through [Bodlaender, Jansen and Kratsch](#bodlaenderjansenkratsch2014), Theorem 2.

<a id="franklwilson1981"></a>
## franklwilson1981

Peter Frankl and Richard M. Wilson. “Intersection Theorems with Geometric Consequences.” *Combinatorica* 1(4), 357–368, 1981. https://doi.org/10.1007/BF02579457 . Bibliographic metadata as already recorded in the library bibliography; it was not re-checked against the publisher record, and the full text was not inspected in this pass. The manual attributes to this paper the modular intersection theorem and the explicit Ramsey graph on the `(p² - 1)`-subsets of a `p³`-set. The formal modular statement is the restricted form given by the triangular polynomial argument (`|L| ≤ d mod p`); the paper's own hypotheses (reportedly `|L| ≤ d` in the uniform case) were not checked.

<a id="freivalds79"></a>
## freivalds79

Rūsiņš Freivalds. "Fast Probabilistic Algorithms." *Mathematical Foundations of Computer Science 1979*, Lecture Notes in Computer Science 74, 57–69. https://doi.org/10.1007/3-540-09526-8_5 . Bibliographic data from the DOI record, checked 2026-11-07; the full text was not inspected. The manual attributes only the random-vector matrix-product check to this paper.

<a id="friezekaronski2016"></a>
## friezekaronski2016

Alan Frieze and Michał Karoński. *Introduction to Random Graphs*. Cambridge University Press, 2016. https://doi.org/10.1017/CBO9781316339831 . Inspected the author-hosted version dated August 7, 2026 (https://www.math.cmu.edu/~af1p/BOOK.pdf), §4.1, Theorem 4.1 and its proof. The theorem is stated for `G_m` with `m = n (log n + c_n) / 2`; the proof works in `G(n, p)` with `p = (log n + c) / n`, and the text later cites it for "`G(n, p)` is connected w.h.p. for `np − log n → ∞`". The book attributes the theorem to Erdős and Rényi, "On random graphs I", *Publ. Math. Debrecen* 6 (1959), 290–297; that paper was not inspected. The publisher's ISBN and DOI are from catalogue records.

<a id="gentry09"></a>
## gentry09

Craig Gentry. “Fully Homomorphic Encryption Using Ideal Lattices.” *STOC 2009*, 169–178. https://doi.org/10.1145/1536414.1536440 . Bibliographic data and theorem locator taken from the pinned repository; full text not independently re-audited here.

<a id="ggm86"></a>
## ggm86

Oded Goldreich, Shafi Goldwasser, Silvio Micali. “How to Construct Random Functions.” *Journal of the ACM* 33(4), 792–807, 1986. Author-hosted version of record: https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf . Adaptive function-test definition consulted.

<a id="gglrs00"></a>
## gglrs00

Oded Goldreich, Shafi Goldwasser, Eric Lehman, Dana Ron and Alex Samorodnitsky. *Testing Monotonicity*. Combinatorica 20(3), 301–337, 2000. https://doi.org/10.1007/s004930070011 . Bibliographic metadata checked against the Crossref record on 2026-11-08. The journal version is paywalled, and the author-hosted pages could not be reached (connection reset), so the text was not inspected and no theorem locator is claimed. The manual attributes the edge tester for Boolean functions on the hypercube to this paper, as [roughgarden15cc](#roughgarden15cc) does.

<a id="gibbard73"></a>
## gibbard73

Allan Gibbard. "Manipulation of Voting Schemes: A General Result." *Econometrica* 41(4), 587–601, 1973. https://doi.org/10.2307/1914083 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected. [Nisan, *Introduction to Mechanism Design*](#nisan07), p. 239, credits the theorem to Gibbard (1973) and Satterthwaite (1975); Nisan's own statement (Theorem 9.8) is the form for rules onto at least three alternatives. The range form (at least three possible outcomes), formalized as the main theorem, is the standard statement in secondary accounts and was not checked against the original; no theorem number is claimed.

<a id="gilbertpollak68"></a>
## gilbertpollak68

E. N. Gilbert and H. O. Pollak. *Steiner Minimal Trees*. SIAM Journal on Applied Mathematics 16(1), 1–29, 1968. https://doi.org/10.1137/0116001 . Cited only because the Chapter 12 Notes of [Williamson and Shmoys](#williamsonshmoys11) attribute the MST factor-2 heuristic for Steiner tree to Moore, as described in this paper. The paper itself was not checked.

<a id="gkr15"></a>
## gkr15

Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum. *Delegating Computation: Interactive Proofs for Muggles*. JACM 62(4), article 27, 2015. https://doi.org/10.1145/2699436 .

<a id="goemanswilliamson95"></a>
## goemanswilliamson95

Michel X. Goemans and David P. Williamson. "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming." *Journal of the ACM* 42(6), 1115–1145, 1995. https://doi.org/10.1145/227683.227684 . Section 2 (the relaxation (P) and random-hyperplane rounding) and Section 3 (Theorem 3.1, Lemma 3.2, Theorem 3.3, Lemma 3.4, and Lemma 3.5 with its tangent-line proof at `θ = 2.331122`) were checked against the author-hosted copy at https://math.mit.edu/~goemans/PAPERS/maxcut-jacm.pdf on 2026-11-08.

<a id="goldbergtarjan88"></a>
## goldbergtarjan88

Andrew V. Goldberg and Robert E. Tarjan. "A New Approach to the Maximum-Flow Problem." *Journal of the ACM* 35(4), 921–940, 1988. https://doi.org/10.1145/48014.61051 . The bibliographic data come from search summaries of the publisher record (2026-11-08). The paper was not inspected, so no theorem number is cited. The manual credits it with the preflow push–relabel method and its `O(|V|² |E|)` generic bound, as these are standardly described. The formalization follows [clrs09](#clrs09), Section 26.4.

<a id="goldreich-tree24"></a>
## goldreich-tree24

Oded Goldreich. *On the Cook–Mertz Tree Evaluation procedure*. ECCC TR24-109, revision 2 (27 December 2024). https://eccc.weizmann.ac.il/report/2024/109/ .

<a id="goldreich04"></a>
## goldreich04

Oded Goldreich. *Foundations of Cryptography, Volume 2: Basic Applications*. Cambridge University Press, 2004. https://doi.org/10.1017/CBO9780511721656 . Author's chapter listing and draft availability: https://www.wisdom.weizmann.ac.il/~oded/foc-vol2.html . Author page checked; the full published chapter was not independently audited here.

<a id="gomoryhu61"></a>
## gomoryhu61

Ralph E. Gomory and T. C. Hu. “Multi-Terminal Network Flows.” *Journal of the Society for Industrial and Applied Mathematics* 9(4), 551–570, 1961. https://doi.org/10.1137/0109047 . Bibliographic metadata checked through the publisher record; the article body was not inspected in this pass. The manual cites it for cut-equivalent (Gomory–Hu) trees and the triangle inequality for minimum cut values, as described in [Schrijver 2003](#schrijver03), Section 15.4.

<a id="grenet11"></a>
## grenet11

Bruno Grenet. *An upper bound for the permanent versus determinant problem*. Manuscript, 2011 (the PDF is dated May 25, 2012). https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf . Checked against the author's PDF on 2026-11-08. Its unnumbered Lemma (an algebraic branching program of size `2ⁿ` on the subsets of `{1, …, n}` computes the permanent) and unnumbered Theorem (a `(2ⁿ - 1) × (2ⁿ - 1)` matrix with entries in `{x_ij} ∪ {-1, 0, 1}` has the permanent as determinant) are `Matrix.permanent_eq_det_grenetMatrix` and `Cslib.Circuits.Arithmetic.isProjection_permanent_det_two_pow_sub_one`. Grenet works over fields of characteristic other than two; the library proves the identity over every commutative ring. The library uses Grenet's construction with a different sign normalization: `-1` on the diagonal at every vertex other than the merged source and sink, rather than loops of weight `1` with weight `-1` on the first layer for even `n`. It proves the determinant identity through the adjugate rather than through cycle covers.

<a id="grigoriev01"></a>
## grigoriev01

Dima Grigoriev. *Linear lower bound on degrees of Positivstellensatz calculus proofs for the parity*. Theoretical Computer Science 259(1–2), 613–622, 2001. https://doi.org/10.1016/S0304-3975(00)00157-2 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC. The article is behind a publisher paywall, so its text was not consulted, and no theorem or page locator in it is claimed. The library attributes the linear degree lower bound for Tseitin parity systems on expanders to this paper. The precise statement used is that of [barak-steurer16](#barak-steurer16), lecture "Higher-degree integrality gaps", Lemma 24.

<a id="grigorievhirschpasechnik02"></a>
## grigorievhirschpasechnik02

Dima Grigoriev, Edward A. Hirsch and Dmitrii V. Pasechnik. *Complexity of Semialgebraic Proofs*. Moscow Mathematical Journal 2(4), 647–679, 2002; extended abstracts in STACS 2002 and ICALP 2002. https://doi.org/10.17323/1609-4514-2002-2-4-647-679 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC. On the same date worker w96-sos consulted the author-hosted copy https://edwardahirsch.github.io/edwardahirsch/papers/02mmj.pdf for Section 2.3 (the translation of a CNF into the inequalities (2.4)–(2.6)), Section 2.5 (static `LS₊`) and Example 2.1 (p. 10 of that copy: the degree-`2` static `LS₊` refutation of `PHP^m_{m-1}`). The ECCC version (TR01-103) could not be retrieved, and the typeset journal pagination of Example 2.1 was not checked.

<a id="grs12"></a>
## grs12

Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan. *Universally Utility-Maximizing Privacy Mechanisms*. SIAM Journal on Computing 41(6), 1673–1693, 2012; conference version STOC 2009. https://doi.org/10.1137/09076828X . §2.1 and Example 2.1 were checked against arXiv:0811.2841v3 on 2026-11-07.

<a id="gsw13"></a>
## gsw13

Craig Gentry, Amit Sahai, Brent Waters. “Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based.” *CRYPTO 2013*, LNCS 8042, 75–92. https://doi.org/10.1007/978-3-642-40041-4_5 ; authors' full-version record https://eprint.iacr.org/2013/340 . Metadata/abstract checked; PDF fetch was blocked in this source pass.

<a id="gupta23"></a>
## gupta23

Anupam Gupta. “Dimension Reduction and the JL Lemma.” Chapter 11 of the lecture notes for CMU 15-850 *Advanced Algorithms*; PDF dated 2023-02-17. https://www.cs.cmu.edu/~15850/notes/lec12.pdf . Checked on 2026-11-07 UTC: §11.6.2, Lemma 11.9 bounds `𝔼 exp (tV²)` for a symmetric σ-sub-Gaussian `V` by the corresponding Gaussian moment generating function. The proof linearizes the square with an independent Gaussian, exchanges the averages and applies the sub-Gaussian bound. The notes apply the lemma to Rademacher projection matrices.

<a id="guruswamirudrasudan25"></a>
## guruswamirudrasudan25

Venkatesan Guruswami, Atri Rudra and Madhu Sudan. *Essential Coding Theory*. Draft book, version of 26 August 2025. https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/ ; open PDF https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf . The library's key is `GuruswamiRudraSudan2019`. Read in the open PDF on 2026-11-08 for Chapter 6:
- §6.2 (the binary symmetric channel) and §6.2.2 (capacity: reliable communication is possible below it and impossible above it);
- Theorem 6.3.1 (p. 119): part (1), achievability with error `2^(−δn)`, and part (2), for `0 ≤ p < 1/2` and `k ≥ ⌈(1 − H(p) + ε) n⌉` with `0 ≤ ε ≤ 1/2 − p`, some message misdecoded with probability more than `1/2`;
- §6.3.1, the packing proof of part (2) (pp. 120–122), and Remark 6.3.2, the error bound `1 − 2^(−βn)`;
- §6.3.2 and Claim 6.3.3, the random-coding proof of part (1).

The draft does not name Wolfowitz. The manual's attribution of the strong converse for discrete memoryless channels to him is standard background and was not checked against his paper.

<a id="gusfield90"></a>
## gusfield90

Dan Gusfield. “Very Simple Methods for All Pairs Network Flow Analysis.” *SIAM Journal on Computing* 19(1), 143–155, 1990. https://doi.org/10.1137/0219009 . Bibliographic metadata checked through the publisher record; the article body (paywalled) was not inspected, so no theorem or page locator is given. Cited for the variant of the Gomory–Hu construction without contraction: a parent array, one minimum cut computation per non-root vertex in the original graph, the re-hanging of vertices on the source side, and the swap of `s` and `t` when the parent of `t` is on the source side. That description was taken from secondary accounts of the algorithm. The Lean proof of correctness (`isGomoryHuTree_gusfieldParent`) is self-contained and does not follow the article's argument.

<a id="harpeledindykmotwani12"></a>
## harpeledindykmotwani12

Sariel Har-Peled, Piotr Indyk, Rajeev Motwani. “Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality.” *Theory of Computing* 8(14), 321–350, 2012. https://doi.org/10.4086/toc.2012.v008a014 . DOI and metadata as reported by search indexes; the open-access PDF could not be fetched in this pass (no connection). Cited for the `(r, cr, p₁, p₂)` form of locality-sensitive families.

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

<a id="indykmotwani98"></a>
## indykmotwani98

Piotr Indyk, Rajeev Motwani. “Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality.” *Proceedings of the 30th Annual ACM Symposium on Theory of Computing* (STOC 1998), 604–613. https://doi.org/10.1145/276698.276876 . DOI and metadata as reported by search indexes; neither the DOI nor the full text was resolved in this pass. Cited for the definition of locality-sensitive families and for bit sampling under the Hamming distance.

<a id="irani91"></a>
## irani91

Sandy Irani. "Two Results on the List Update Problem." *Information Processing Letters* 38(6), 301–306, 1991. https://doi.org/10.1016/0020-0190(91)90086-W . Crossref metadata checked on 2026-11-07; the full text was not inspected in this pass. The manual uses it only as the place where secondary sources say the deterministic `2n/(n+1)` list-update lower bound of Karp and Raghavan is reported.

<a id="johnsonlindenstrauss84"></a>
## johnsonlindenstrauss84

William B. Johnson, Joram Lindenstrauss. “Extensions of Lipschitz Mappings into a Hilbert Space.” In *Conference in Modern Analysis and Probability (New Haven, Conn., 1982)*, Contemporary Mathematics 26, 189–206. American Mathematical Society, 1984. https://doi.org/10.1090/conm/026/737400 . Bibliographic data from the DOI record; the manual attributes only the existence of low-distortion linear embeddings of `n` points into `O(log n / ε²)` dimensions to this paper.

<a id="kargerstein96"></a>
## kargerstein96

David R. Karger and Clifford Stein. "A New Approach to the Minimum Cut Problem." *Journal of the ACM* 43(4), 601–640, 1996. https://doi.org/10.1145/234533.234534 . Bibliography key `KargerStein1996`. Inspected on 2026-11-08 in the author-hosted copy (people.csail.mit.edu/karger/Papers/contract.pdf, dated 6 August 1996); locators refer to that copy. Section 2 defines the blocks `s(a)` and the output cut. Lemma 2.1 says a cut is output iff no crossing edge is contracted. Theorem 2.2 is the per-cut bound `C(n, 2)⁻¹`, and the text after its proof notes that the `n`-cycle makes the bound tight. The proof of Theorem 4.4 attributes the bound of `C(n, 2)` minimum cuts to Dinitz, Karzanov and Lomonosov (1976). The proof of Theorem 8.4, stated for `α`-minimal cuts, bounds their number by the disjointness of the output events; applied to Theorem 2.2, this argument gives the count. That 1976 paper was not consulted and is cited only through this attribution.

<a id="karlin88"></a>
## karlin88

Anna R. Karlin, Mark S. Manasse, Larry Rudolph, Daniel D. Sleator. "Competitive Snoopy Caching." *Algorithmica* 3, 79–119, 1988. https://doi.org/10.1007/BF01762111 . Bibliographic data from secondary indexes and the DOI record; the full text was not inspected in this pass. The manual credits this paper only with the rent-or-buy framing behind ski rental, which secondary sources attribute to it.

<a id="kasai01"></a>
## kasai01

Toru Kasai, Gunho Lee, Hiroki Arimura, Setsuo Arikawa and Kunsoo Park. "Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its Applications." *Combinatorial Pattern Matching (CPM 2001)*, Lecture Notes in Computer Science 2089, 181–192, Springer, 2001. https://doi.org/10.1007/3-540-48194-X_17 . Bibliographic data from secondary indexes and the DOI record; the publisher's full text was not accessible in this pass. The manual credits it with the text-order LCP algorithm and the height lemma `lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1`, following the customary attribution; its internal lemma and theorem numbers are not cited.

<a id="kasami65"></a>
## kasami65

Tadao Kasami. *An Efficient Recognition and Syntax-Analysis Algorithm for Context-Free Languages*. Scientific Report AFCRL-65-758, Air Force Cambridge Research Laboratory, Bedford, MA, 1965. Bibliographic metadata was checked against secondary sources on 2026-11-08; the report was not inspected. It is cited, with [Younger 1967](#younger67), as an original source of the CYK algorithm.

<a id="katzlindell20"></a>
## katzlindell20

Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd edition. CRC Press, 2020. Bibliographic metadata and section titles checked against the authors' 3rd-edition table of contents and preface: https://www.cs.umd.edu/~jkatz/imc/toc-preface-3rd.pdf (Sections 9.2.3–9.2.4 on the factoring and RSA assumptions; Section 15.1.1 on trapdoor permutations; Section 15.2 on Paillier encryption; Sections 15.4.1–15.4.3 on quadratic residues and the quadratic residuosity assumption; and Sections 15.5.1–15.5.2 on modular square roots and the Rabin trapdoor permutation). Detailed numbered locators (Definitions, Claims, Propositions, Lemmas, Constructions, Examples, Exercises, and Theorems) remain attributed to the Lean source docstrings, as the textbook body was not independently audited; the Lean modules adapt the parameter generators, RSA challenge domain, Rabin sampling distribution, and the Paillier encryption-randomness sampler (dyadic sampling with `unitOrOne` in place of uniform `ℤ_N^*`) as documented in their module docstrings and implementation notes.

<a id="khot10"></a>
## khot10

Subhash Khot. "On the Unique Games Conjecture (Invited Survey)." *2010 IEEE 25th Annual Conference on Computational Complexity (CCC)*, 99–121, 2010. https://doi.org/10.1109/CCC.2010.19 . Author-hosted copy inspected: https://cs.nyu.edu/~khot/papers/UGCSurvey.pdf (Section 2.4, p. 6 of the author copy: the second paragraph after Definition 2.4, beginning "Let us return", on finding a satisfying labelling of a value-1 instance by trying every label for one vertex and propagating along each connected component, and the remark after Conjecture 2.5 that the conjecture would be false with `ε = 0`). The page range and DOI are from the bibliographic record and were not checked against the typeset proceedings.

<a id="kleenepost54"></a>
## kleenepost54

Stephen C. Kleene and Emil L. Post. *The Upper Semi-Lattice of Degrees of Recursive Unsolvability*. Annals of Mathematics (2) 59(3), 379–407, 1954. https://doi.org/10.2307/1969708 . Bibliographic metadata checked on 2026-11-08; the article is paywalled and was not inspected. The manual attributes to it, following the customary attribution, the existence of two Turing-incomparable sets below `0′` by the finite extension method. No section or theorem locator is claimed.

<a id="kleinbergtardos06"></a>
## kleinbergtardos06

Jon Kleinberg and Éva Tardos. *Algorithm Design*. Addison-Wesley, 2006. Cited for Section 6.6 ("Sequence Alignment"), the alignment dynamic program with gap and mismatch costs. Section 6.7 ("Sequence Alignment in Linear Space via Divide and Conquer") is the locator for the Hirschberg follow-up. The section titles were checked against search summaries of the published table of contents on 2026-11-08, not the printed book.

<a id="kmb81"></a>
## kmb81

L. Kou, G. Markowsky and L. Berman. *A Fast Algorithm for Steiner Trees*. Acta Informatica 15(2), 141–145, 1981. https://doi.org/10.1007/BF00288961 . The heuristic's steps (shortest-path distance graph on the terminals, its minimum spanning tree, replacement by shortest paths, a spanning tree of the result, then pruning non-terminal leaves) and the `2 (1 - 1/ℓ)` bound, with `ℓ` the number of leaves of an optimal tree, are taken from the abstract and secondary sources. The body of the paper was not consulted.

<a id="knuth1994"></a>
## knuth1994

Donald E. Knuth. *The Sandwich Theorem*. Electronic Journal of Combinatorics 1, A1, 1994. https://doi.org/10.37236/1193 ; arXiv text https://arxiv.org/abs/math/9312214 . The arXiv text was consulted on 2026-11-07 for §1 (orthogonal labelings and the lemma `α ≤ ϑ`), §4 (4.9), §5 (5.2), the product lemma of §20 and the pentagon umbrella of §22. The formal umbrella matches §22 up to the vertex relabelling `i ↦ 3i`.

<a id="knuthyao76"></a>
## knuthyao76

Donald E. Knuth and Andrew C. Yao. "The Complexity of Nonuniform Random Number Generation." In J. F. Traub (ed.), *Algorithms and Complexity: New Directions and Recent Results*, Academic Press, 1976, pp. 357–428. Cited for DDG trees, the optimal tree built from binary expansions, and the entropy bounds `H ≤ E[T] < H + 2`. These attributions follow Cover–Thomas §5.11 and secondary literature (Saad, Freer, Rinard and Mansinghka, POPL 2020). The 1976 text was not inspected, so no theorem number is cited.

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

<a id="lemkehowson64"></a>
## lemkehowson64

Carlton E. Lemke and Joseph T. Howson, Jr. "Equilibrium Points of Bimatrix Games." *Journal of the Society for Industrial and Applied Mathematics* 12(2), 413–423, 1964. https://doi.org/10.1137/0112033 . Bibliographic data from the DOI record and secondary summaries; the paper's text was not consulted. It is cited only as the origin of the algorithm. Locators for the formalized statements follow [vonstengel07](#vonstengel07).

<a id="leskovecrajaramanullman20"></a>
## leskovecrajaramanullman20

Jure Leskovec, Anand Rajaraman, Jeffrey D. Ullman. *Mining of Massive Datasets*, 3rd edition. Cambridge University Press, 2020. https://doi.org/10.1017/9781108684163 . DOI and metadata as reported by search indexes. The section locators used here (3.3.3 minhashing and Jaccard similarity, 3.4.2 analysis of the banding technique, 3.6.1 locality-sensitive functions, 3.6.2 families for the Jaccard distance, 3.6.3 amplification, 3.7.1 families for the Hamming distance) were matched against section titles reported by secondary sources; the book text was not inspected in this pass (no connection to the authors' site).

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

Arjen K. Lenstra, Hendrik W. Lenstra Jr. and László Lovász. "Factoring Polynomials with Rational Coefficients." *Mathematische Annalen* 261, 515–534, 1982. https://doi.org/10.1007/BF01457454 . Inspected the author-hosted scan https://www.math.leidenuniv.nl/~hwl/PUBLICATIONS/1982f/art.pdf on 2026-11-08: §1, conditions (1.4)–(1.5) and the remark after (1.5), Proposition (1.6) and the remark after it, Proposition (1.11), the algorithm (1.15)–(1.21), the swap formulas (1.22) and the termination argument (1.23)–(1.26).

<a id="lovasz1979"></a>
## lovasz1979

László Lovász. *On the Shannon Capacity of a Graph*. IEEE Transactions on Information Theory 25(1), 1–7, 1979. https://doi.org/10.1109/TIT.1979.1055985 . Bibliographic data from the DOI record. The full text was not inspected in this pass, so no theorem numbers are quoted. The attributed content (orthonormal representations with orthogonality on nonadjacent pairs, `ϑ`, `Θ ≤ ϑ`, submultiplicativity under strong products and `Θ(C₅) = √5`) follows [knuth1994](#knuth1994) and standard accounts.

<a id="lp09"></a>
## lp09

Yehuda Lindell, Benny Pinkas. "A Proof of Security of Yao's Protocol for Two-Party Computation." *Journal of Cryptology* 22(2), 161–188, 2009. https://doi.org/10.1007/s00145-008-9036-8 . Metadata checked at the publisher. The full text is paywalled and ePrint 2004/175 returned HTTP 403 in this pass, so theorem and section locators are not claimed.

<a id="ltv98"></a>
## ltv98

Ming Li, John Tromp and Paul Vitányi. *Reversible Simulation of Irreversible Computation by Pebble Games*. Physica D 120, 168–176, 1998. https://doi.org/10.1016/S0167-2789(98)00052-9 . Locators refer to arXiv:quant-ph/9703009v3 (11 April 1997), https://arxiv.org/abs/quant-ph/9703009v3 . The reversible pebble rule (Section 6), the procedures `pebble(s, n)` and `unpebble(s, n)` (Section 7), Theorem 1, Corollaries 1 and 2, Lemma 1 and Theorem 2 were checked. The definitions of available pebbles and of weak and strong solvability, the statement and proof of Theorem 1 (including the distance estimate `2^j + 2^f + 2^(f+1) + ⋯ + 2^(j−1) ≤ 2^(j+1)`), and Corollary 1 were rechecked against the same arXiv version on 2026-11-08 for `ReversiblePathReachable.lean`.

<a id="manacher75"></a>
## manacher75

Glenn Manacher. “A New Linear-Time ‘On-Line’ Algorithm for Finding the Smallest Initial Palindrome of a String.” *Journal of the ACM* 22(3), 346–351, 1975. https://doi.org/10.1145/321892.321896 . Bibliographic data from the DOI record; the paper is behind the ACM paywall and was not inspected. The manual credits it with the linear-time algorithm for all maximal palindromic radii as described in [apostolicobreslauergalil95](#apostolicobreslauergalil95), Section 1; its formulation is on-line, as its title and that description say, and its internal locators are not cited.

<a id="manassemcgeochsleator90"></a>
## manassemcgeochsleator90

Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator. "Competitive Algorithms for Server Problems." *Journal of Algorithms* 11(2), 208–230, 1990. https://doi.org/10.1016/0196-6774(90)90003-W ; author PDF https://www.cs.cmu.edu/~sleator/papers/server-problems.pdf . Theorem 6 (lower bound `k/(k-h+1)` against `h`-server offline algorithms on a graph with at least `k + 1` nodes, proved with a lazy online algorithm, its nemesis sequence and an ensemble of offline algorithms) and Corollary 7 (no `c`-competitive algorithm for `c < k`) were checked against the author PDF on 2026-11-08. The local lower bound is the case `h = k`.

<a id="manbermyers93"></a>
## manbermyers93

Udi Manber and Gene Myers. "Suffix Arrays: A New Method for On-Line String Searches." *SIAM Journal on Computing* 22(5), 935–948, 1993; preliminary version in SODA 1990. https://doi.org/10.1137/0222058 . Bibliographic data from secondary indexes and the DOI record; the journal text is behind the SIAM paywall and was not inspected. The manual credits it with the suffix array and with the contrast between the plain `O(P log N)` binary search and the `O(P + log N)` search that reuses longest-common-prefix information, following the customary attribution; section and theorem numbers are not cited.

<a id="mathlib"></a>
## mathlib

Mathlib contributors. *Mathlib*, pinned source `69552756cd8a2d2d48763cf7279fd814d6a1224d`, inspected 2026-11-01. https://github.com/leanprover-community/mathlib4/tree/69552756cd8a2d2d48763cf7279fd814d6a1224d

<a id="mccreightmeyer69"></a>
## mccreightmeyer69

Edward M. McCreight and Albert R. Meyer. *Classes of Computable Functions Defined by Bounds on Computation: Preliminary Report*. Proceedings of the First Annual ACM Symposium on Theory of Computing (STOC '69), 79–88, 1969. https://doi.org/10.1145/800169.805423 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected. The manual attributes the union, naming and honesty theorems to it, following the customary attribution; Odifreddi's textbook [odifreddi99](#odifreddi99) attributes the Naming Theorem VII.3.6 and the Union Theorem VII.3.7 to it. The paper's own theorem numbers and exact hypotheses are unverified. Odifreddi states the union theorem for a uniformly recursive sequence `t_n` with `t_n(x) ≤ t_{n+1}(x)` for all `n` and `x`, which is the hypothesis of `union_theorem`. Secondary accounts state the union theorem for a recursively enumerable "self-bounded" set of bounds, in which every finite subset is dominated almost everywhere by a member; this would match `union_theorem_of_directed`, but it has not been checked against the paper, so the library derives the directed and almost-everywhere variants from the pointwise `union_theorem`. The open survey by Hartmanis and Hopcroft (Cornell TR70-59, https://hdl.handle.net/1813/5918) is an image scan that was not read in this pass.

<a id="menger27"></a>
## menger27

Karl Menger. "Zur allgemeinen Kurventheorie." *Fundamenta Mathematicae* 10, 96–115, 1927. Cited for attribution only: the paper was not consulted, and the formal statements follow [schrijver17](#schrijver17) and [diestel25](#diestel25).

<a id="mignonressayre04"></a>
## mignonressayre04

Thierry Mignon and Nicolas Ressayre. *A quadratic bound for the determinant and permanent problem*. International Mathematics Research Notices 2004(79), 4241–4253, 2004. https://doi.org/10.1155/S1073792804142566 . Bibliographic metadata checked on 2026-11-08; the publisher copy was not inspected, so no theorem number is claimed. The statement (`dc(perm_n) ≥ n²/2` in characteristic zero), the point `X₀` (all ones with `1 - n` in one corner), and the two Hessian lemmas were checked against R. Saptharishi, *A survey of lower bounds in arithmetic circuit complexity*, chapter "Determinantal Complexity Lower Bounds" (Theorem `thm:Mignon-Ressayre-mainthm`, Lemmas `lem:MR-det-ub` and `lem:MR-perm-lb`), at GitHub revision `af95c539`. The full rank of the Hessian at `X₀` is proved in the library by its own sandwich-identity argument, not by the survey's eigenvalue or block-matrix computation.

<a id="misragries82"></a>
## misragries82

Jayadev Misra, David Gries. “Finding Repeated Elements.” *Science of Computer Programming* 2(2), 143–152, 1982. https://doi.org/10.1016/0167-6423(82)90012-0 . Bibliographic data from search summaries of the DOI record; the Misra–Gries statements formalized here follow the presentation of [chakrabarti25](#chakrabarti25), Unit 1. The journal text was not inspected in this pass.

<a id="mitzenmacherupfal17"></a>
## mitzenmacherupfal17

Michael Mitzenmacher and Eli Upfal. *Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis*, 2nd edition. Cambridge University Press, 2017. The locator Section 1.3, Theorem 1.4 (an incorrect product survives a uniform `0`/`1` vector with probability at most `1/2`) was checked against secondary descriptions on 2026-11-07; the full text was not inspected in this pass.

<a id="monderershapley96"></a>
## monderershapley96

Dov Monderer and Lloyd S. Shapley. *Potential Games*. Games and Economic Behavior 14(1), 124–143, 1996. https://doi.org/10.1006/game.1996.0044 . The published text was consulted on 2026-11-07 for the definitions (2.1)–(2.3), Lemmas 2.1, 2.3, 2.5 and 2.7, Corollary 2.2, Theorem 3.1 and footnote 12.

<a id="mosertardos10"></a>
## mosertardos10

Robin A. Moser and Gábor Tardos. “A Constructive Proof of the General Lovász Local Lemma.” *Journal of the ACM* 57(2), Article 11, 2010. https://doi.org/10.1145/1667053.1667060 . Open version: arXiv:0903.0544v3, https://arxiv.org/abs/0903.0544 . Theorems 1.1–1.4, the Section 2 definitions of the log and witness trees, Lemma 2.1 and the Section 3 counting argument (Lemma 3.1) were checked against the arXiv v3 PDF (dated 20 May 2009) on 2026-11-08. The JACM article numbering was not checked against the typeset journal version.

<a id="mullersatterthwaite77"></a>
## mullersatterthwaite77

Eitan Muller and Mark A. Satterthwaite. "The Equivalence of Strong Positive Association and Strategy-Proofness." *Journal of Economic Theory* 14(2), 412–418, 1977. https://doi.org/10.1016/0022-0531(77)90140-5 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected. It is cited, from secondary accounts, for the equivalence of strategy-proofness and Maskin monotonicity (strong positive association) and for the theorem that a Maskin monotone rule with at least three outcomes is dictatorial. The library proves both through [Nisan](#nisan07)'s argument; no theorem number is claimed.

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

<a id="nisan07"></a>
## nisan07

Noam Nisan. "Introduction to Mechanism Design (for Computer Scientists)." Chapter 9 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 209–242. https://doi.org/10.1017/CBO9780511800481.011 . A university-hosted PDF of the book was consulted on 2026-11-08 for §9.2 (pp. 211–215): Definition 9.1 (social welfare and social choice functions), Definition 9.4 (manipulation and incentive compatibility), Definition 9.5 and Proposition 9.6 (one-voter monotonicity is equivalent to incentive compatibility), Definition 9.7 (dictator), Theorem 9.8 (Gibbard–Satterthwaite, for rules onto at least three alternatives), Definition 9.9 (moving a set `S` to the top, and the induced social welfare function), and the proof of Lemmas 9.10 and 9.11 (the claim that the outcome lies in `S`, transitivity, unanimity and IIA). The library's proof follows this reduction; its main theorem assumes three alternatives in the range rather than onto, which needs an extension of rankings of the range to all alternatives.

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

<a id="post46"></a>
## post46

Emil L. Post. "A Variant of a Recursively Unsolvable Problem." *Bulletin of the American Mathematical Society* 52(4), 264–268, 1946. https://doi.org/10.1090/S0002-9904-1946-08555-9 . Bibliographic metadata only. The publisher's PDF returned an access error and was not inspected. It is cited as the origin of the correspondence problem and its unsolvability, as in [sipser13](#sipser13), §5.2.

<a id="radhakrishnan97"></a>
## radhakrishnan97

Jaikumar Radhakrishnan. "An Entropy Proof of Bregman's Theorem." *Journal of Combinatorial Theory, Series A* 77(1), 161–164, 1997. https://doi.org/10.1006/jcta.1996.2727 . Bibliographic data from the DOI record. Cited only as an alternative proof; the library does not formalize it.

<a id="rado62"></a>
## rado62

Tibor Radó. *On Non-Computable Functions*. The Bell System Technical Journal 41(3), 877–884, 1962. https://doi.org/10.1002/j.1538-7305.1962.tb00480.x ; scan at https://archive.org/details/bstj41-3-877 . Read in the archive.org text on 2026-11-08: Section V, Theorem (`Σ(n)` eventually exceeds every computable `f`, so `Σ` is not computable), proved with an auxiliary computable majorant of `f`; Section VI defines the shift function `S(n)` and derives the same domination from `S(n) ≥ Σ(n)`.

<a id="raychaudhuriwilson1975"></a>
## raychaudhuriwilson1975

Dijen K. Ray-Chaudhuri and Richard M. Wilson. “On `t`-Designs.” *Osaka Journal of Mathematics* 12(3), 737–744, 1975. Bibliographic metadata from search summaries on 2026-11-08; the full text was not inspected in this pass. The manual attributes only the uniform bound `C(n, s)` for `s` allowed intersection sizes to this paper.

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

<a id="rothsotomayor90"></a>
## rothsotomayor90

Alvin E. Roth and Marilda A. Oliveira Sotomayor. *Two-Sided Matching: A Study in Game-Theoretic Modeling and Analysis*. Econometric Society Monographs, Cambridge University Press, 1990. https://doi.org/10.1017/CCOL052139015X . Bibliographic metadata checked against Crossref on 2026-11-08. The book itself was not inspected. Its Chapter 2 theorem numbers and statements were checked against Muriel Niederle's lecture notes *Matching: The Theory* (Stanford, 26 September 2011, https://web.stanford.edu/~niederle/MarketDesignClassIntro2.pdf), which follow the book's numbering. They are Theorem 2.8 (a stable matching exists for every marriage market), Theorem 2.12 (with strict preferences there are M-optimal and W-optimal stable matchings), Theorem 2.13 (opposing interests, credited to Knuth) and Theorem 2.22 (with strict preferences, the set of people who are single is the same for all stable matchings). The incomplete-list stable-matching modules cite these theorems.

<a id="roughgarden03"></a>
## roughgarden03

Tim Roughgarden. *The Price of Anarchy is Independent of the Network Topology*. Journal of Computer and System Sciences 67(2), 341–364, 2003. https://doi.org/10.1016/S0022-0000(03)00044-8 . The author's version of 23 December 2002 (https://theory.stanford.edu/~tim/papers/indep.pdf) was consulted on 2026-11-08 for Section 2.4, Definitions 2.5 and 3.1–3.3, Theorem 3.8, Lemma 4.1, Theorem 4.2, Proposition 5.1 and Remark 5.2; locators follow that version. Its anarchy value is defined through marginal costs for latencies with `x c(x)` convex, and Proposition 5.1 takes the degree `p ≥ 1`. The library uses the Pigou-ratio definition of [roughgarden13cs364a](#roughgarden13cs364a), Lecture #11, (2), which agrees with it on standard classes (Definition 3.1; up to the degenerate convention when `c(r) = 0`), needs no convexity, and includes `d = 0`.

<a id="roughgarden13cs364a"></a>
## roughgarden13cs364a

Tim Roughgarden. *CS364A: Algorithmic Game Theory*, lecture notes, Stanford University, Fall 2013. https://theory.stanford.edu/~tim/f13/f13.html . Lecture #17, "No-Regret Dynamics" (18 November 2013), was consulted on 2026-11-07 for Definition 1.2, §3, Proposition 3.1, Remark 3.2, Corollary 3.3 and footnote 1. Lecture #9, "Beyond Quasi-Linearity" (21 October 2013), was consulted on 2026-11-08 for §3 (the top trading cycle algorithm, Theorems 3.1 and 3.2). Its core is defined by strict blocking, for which only the existence half of Theorem 3.2 holds; a checked three-agent market in `ComplexityTests/HousingMarket.lean` has a second core allocation. Lecture #11, "Selfish Routing and the Price of Anarchy" (28 October 2013), was consulted on 2026-11-08 for Definition 3.2, the Pigou bound (2), Theorem 3.3, Table 1 and the proof in §5. Lecture #15, "Best-Case and Strong Nash Equilibria" (11 November 2013), was consulted on 2026-11-08 for §1.2 (network cost-sharing games, displays (1) and (2)), §1.3 (VHS or Betamax, Figure 1), §1.4 (the opt-out example, Figure 2), Theorem 2.1, the remark after it that the opt-out example rules out a smaller factor, and displays (3) and (4). Exercise Set #7, Exercise 55 (`C(f)/2 ≤ Φ(f) ≤ C(f)` for affine atomic selfish routing), was consulted on the same day.

<a id="roughgarden15"></a>
## roughgarden15

Tim Roughgarden. *Intrinsic Robustness of the Price of Anarchy*. Journal of the ACM 62(5), Article 32, 2015. https://doi.org/10.1145/2806883 . The author's version of 14 July 2015 was consulted on 2026-11-07 for Definition 2.1, derivation (3)–(5), Example 2.5, (15) and Theorems 3.2–3.3; locators follow that version.

<a id="roughgarden15cc"></a>
## roughgarden15cc

Tim Roughgarden. *Communication Complexity (for Algorithm Designers)*. Lecture notes, arXiv:1509.06257v1, 2015; published in Foundations and Trends in Theoretical Computer Science 11(3–4), 217–404, 2016. https://arxiv.org/abs/1509.06257v1 . arXiv version 1 was consulted on 2026-11-08 for §8.3.1 (pp. 125–129): the edge tester, display (8.2), the Key Claim and Theorem 8.2, which the notes attribute to [gglrs00](#gglrs00). The monotonicity-testing modules follow this proof, and their locators follow version 1. Theorem 8.2 takes `t = Θ(n / ε)` trials. The library proves the upper bound with explicit constants and claims nothing about fewer trials.

<a id="roughgardentardos02"></a>
## roughgardentardos02

Tim Roughgarden and Éva Tardos. *How Bad Is Selfish Routing?* Journal of the ACM 49(2), 236–259, 2002. https://doi.org/10.1145/506147.506153 . The author's version of 5 December 2001 was consulted on 2026-11-07 for Section 2.1, Definition 2.1, Lemma 2.2, Theorem 4.5 and Figure 3; locators follow that version.

<a id="roughgardentardos07"></a>
## roughgardentardos07

Tim Roughgarden and Éva Tardos. "Introduction to the Inefficiency of Equilibria." Chapter 17 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 443–459. A university-hosted PDF of the book was consulted on 2026-11-08 for §17.1.3 (the definitions of the price of anarchy and the price of stability) and Example 17.3 with Figure 17.3 (the `H_k` lower bound for Shapley network design games).

<a id="sakszhou99"></a>
## sakszhou99

Michael Saks and Shiyu Zhou. *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*. Journal of Computer and System Sciences 58(2), 376–403, 1999. https://doi.org/10.1006/jcss.1998.1616 . The publisher copy is paywalled and was not consulted, so its internal numbering (including the Lemma 5.4 cited by Chattopadhyay–Liao) is unverified. The iteration is formalized from the presentation of Chattopadhyay and Liao (2020), Appendix A.1.

<a id="satterthwaite75"></a>
## satterthwaite75

Mark A. Satterthwaite. "Strategy-Proofness and Arrow's Conditions: Existence and Correspondence Theorems for Voting Procedures and Social Welfare Functions." *Journal of Economic Theory* 10(2), 187–217, 1975. https://doi.org/10.1016/0022-0531(75)90050-2 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected. Cited, with [Gibbard](#gibbard73), for the Gibbard–Satterthwaite theorem; no theorem number is claimed.

<a id="schoenebeck08"></a>
## schoenebeck08

Grant Schoenebeck. *Linear Level Lasserre Lower Bounds for Certain k-CSPs*. 49th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2008), 593–602. https://doi.org/10.1109/FOCS.2008.74 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC. On the same date worker w96-sos consulted the author-hosted copy https://schoeneb.people.si.umich.edu/papers/LasserreNew.pdf (19 pages, TeX output dated 6 December 2008) for Definition 5 (rounds of Lasserre), Definition 10 (width-`w` resolution on XOR formulas), Lemma 13 (the main lemma, p. 8) and Claim 14. In that copy Lemma 13 grants a feasible solution at the `w/2`-th round of Lasserre. An independent review reported `w/4` from a different version, so the constant is version-dependent. The library proves the sum-of-squares form of the lemma and does not construct Lasserre vectors. The typeset FOCS version was not consulted.

<a id="schrijver03"></a>
## schrijver03

Alexander Schrijver. *Combinatorial Optimization: Polyhedra and Efficiency*. Algorithms and Combinatorics 24, Springer, 2003. Cited for Gomory–Hu trees. The locator (Chapter 15, “Connectivity and Gomory–Hu trees”, Section 15.4) is taken from secondary descriptions of the table of contents only: the book itself was not inspected, and no theorem or page locator is claimed. It is also cited for Dinitz's algorithm: the locator Section 10.6 (on Dinitz's `O(n²m)` maximum-flow algorithm) was likewise taken from secondary descriptions of the table of contents.

<a id="schrijver17"></a>
## schrijver17

Alexander Schrijver. *A Course in Combinatorial Optimization*. Lecture notes, version of March 23, 2017. https://homepages.cwi.nl/~lex/files/dict.pdf . The author-hosted PDF was consulted on 2026-11-08 UTC for Section 10.4 (Lemma 10.2), Section 10.5 (Example 10.5a, displays (23)–(25) and (27), Theorems 10.6, 10.7 and 10.9) and Exercise 10.22; the matroid intersection modules cite these locators. It was also consulted on 2026-11-08 UTC for Section 3.2 (display (6) and Theorem 3.2), Section 5.1 (Theorem 5.1 and Corollary 5.1a) and Theorem 5.2; the general-matching modules `Berge` and `TutteBerge` cite these locators. Section 4.1 (Theorem 4.1, Corollaries 4.1a and 4.1b, and the vertex-splitting and undirected remarks after them) was consulted on the same date for the Menger modules. The corresponding chapter of Schrijver's 2003 monograph (Chapter 41) is cited in the library from secondary descriptions only; its theorem and page locators are unverified.

<a id="schrijver78"></a>
## schrijver78

Alexander Schrijver. "A Short Proof of Minc's Conjecture." *Journal of Combinatorial Theory, Series A* 25(1), 80–83, 1978. https://doi.org/10.1016/0097-3165(78)90036-5 . Bibliographic data from the DOI record; the paper was not inspected. The induction in the library's Brégman module follows the published descriptions of this proof (induction on `n`, a convexity inequality at one row, then averaging over the rows).

<a id="schummervohra07"></a>
## schummervohra07

James Schummer and Rakesh V. Vohra. "Mechanism Design without Money." Chapter 10 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 243–265. A university-hosted PDF of the book was consulted on 2026-11-08 for §10.3 (the definition of blocking coalitions and the core, Definition 10.5, Theorems 10.6 and 10.7, pp. 253–255). Its core uses weak blocking, the strict core of the housing-market modules. Its claim on p. 255 that the core and the strict core coincide under strict preferences is refuted by a checked three-agent market in `ComplexityTests/HousingMarket.lean`.

<a id="shamir1992"></a>
## shamir1992

Adi Shamir. “IP = PSPACE.” *Journal of the ACM* 39(4), 869–877 (1992). DOI: https://doi.org/10.1145/146585.146609. Original-paper scan inspected: https://crypto.cs.mcgill.ca/~crepeau/COMP647/2007/TOPIC01/Shamir-IP=PSPACE.pdf.

<a id="shannon1956"></a>
## shannon1956

Claude E. Shannon. *The Zero Error Capacity of a Noisy Channel*. IRE Transactions on Information Theory 2(3), 8–19, 1956. https://doi.org/10.1109/TIT.1956.1056798 . Bibliographic data from the DOI record. The zero-error capacity as a limit over strong powers, and the five-word code in the square of the pentagon, are attributed from secondary accounts; the full text was not inspected in this pass.

<a id="shapleyscarf74"></a>
## shapleyscarf74

Lloyd Shapley and Herbert Scarf. *On Cores and Indivisibility*. Journal of Mathematical Economics 1(1), 23–37, 1974. https://doi.org/10.1016/0304-4068(74)90033-0 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected. The housing market model and the top trading cycles algorithm (credited there to David Gale) are attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, §3, and [schummervohra07](#schummervohra07), §10.6 (which lists the pages as 23–28; the Crossref record was not rechecked). The housing-market modules also attribute to it the competitive allocation at round-size prices (`isCompetitive_ttc`), from memory of the literature; this attribution is unverified.

<a id="sipser13"></a>
## sipser13

Michael Sipser. *Introduction to the Theory of Computation*, third edition. Cengage Learning, 2013. Cited for Definition 2.8 (Chomsky normal form: rules `A → BC` and `A → a`, with `S → ε` permitted for the start variable `S`, and `S` forbidden on every right-hand side; the library's `ChomskyNormalFormGrammar` imposes the latter restriction only when `S → ε` is present) and Theorem 7.16 ("Every context-free language is a member of P", proved by the CYK dynamic program). Both locators were checked against secondary course material, not the printed book. Also cited for §5.2 and Theorem 5.15 (Post's correspondence problem is undecidable, proved through the modified problem MPCP by a reduction from `A_TM`). That locator was checked against secondary summaries, not the printed book.

<a id="sleatortarjan85"></a>
## sleatortarjan85

Daniel D. Sleator, Robert E. Tarjan. “Amortized Efficiency of List Update and Paging Rules.” *Communications of the ACM* 28(2), 202–208, 1985. https://doi.org/10.1145/2786.2793 ; author PDF https://www.cs.cmu.edu/~sleator/papers/amortized-efficiency.pdf . Paging scope and equal-capacity specialization checked against source and local mapping. The list-update cost model of Section 2, Theorem 1 (`C_MF(s) ≤ 2C_A(s) + X_A(s) − F_A(s) − m`) and the remark after its proof (different initial lists, plus the initial inversion count) were checked against the author PDF on 2026-11-07 UTC.

<a id="soare87"></a>
## soare87

Robert I. Soare. *Recursively Enumerable Sets and Degrees*. Perspectives in Mathematical Logic, Springer, 1987. https://doi.org/10.1007/978-3-662-02460-7 . Bibliographic metadata checked on 2026-11-08; the book was not inspected, and no open copy was used. It is cited as a standard reference for oracle computations, the use principle and finite extension constructions. No chapter or theorem locator is claimed.

<a id="stoerwagner97"></a>
## stoerwagner97

Mechthild Stoer and Frank Wagner. "A Simple Min-Cut Algorithm." *Journal of the ACM* 44(4), 585–591, 1997. https://doi.org/10.1145/263867.263872 . Bibliographic metadata checked against the Crossref record on 2026-11-08. The publisher's PDF returned HTTP 403 and was not retried, so the paper was not inspected. Its numbering (the phase recursion as Theorem 2.1, the cut-of-the-phase lemma as Lemma 3.1) comes from secondary descriptions and is unverified, which is why the Lean docstrings name the results rather than the numbers. The 8-vertex example graph in `ComplexityTests/StoerWagner.lean` and the trace of the worked example's first phase come from the English Wikipedia article "Stoer–Wagner algorithm", consulted on 2026-11-08, not from the paper's figure. A. Frank's note on MA orderings was unreachable (connection failure), and the corresponding section of Schrijver's 2003 monograph was not consulted; neither is cited.

<a id="sudantrevisanvadhan01"></a>
## sudantrevisanvadhan01

Madhu Sudan, Luca Trevisan and Salil Vadhan. *Pseudorandom Generators without the XOR Lemma*. Journal of Computer and System Sciences 62(2), 236–266, 2001. DOI: [10.1006/jcss.2000.1730](https://doi.org/10.1006/jcss.2000.1730). Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; the proof-route attribution comes from the pinned Lean module.

<a id="tardoswexler07"></a>
## tardoswexler07

Éva Tardos and Tom Wexler. "Network Formation Games and the Potential Function Method." Chapter 19 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 487–516. A university-hosted PDF of the book was consulted on 2026-11-08 for §19.3.1 (the global connection game, the potential `Σ c_e H_{k_e}`, Lemmas 19.7 and 19.8, Theorem 19.10), §19.3.2 (fair cost sharing as a congestion game with `c_e(x) = c_e / x`) and §19.3.3 (Theorem 19.13: `cost(S) / A ≤ Φ(S) ≤ B · cost(S)` with `A, B > 0` gives price of stability at most `AB`).

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

<a id="toran04"></a>
## toran04

Jacobo Torán. “Space and Width in Propositional Resolution.” The Computational Complexity Column, *Bulletin of the EATCS* 83, 86–104, 2004 (bibliography key `Toran2004`). Author-hosted copy: https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/toran/beatcs/column83.pdf . Checked against that copy on 2026-11-08 UTC: Definition 2 (resolution space, as sequences of clause sets obtained by deleting clauses, adding a resolvent or adding an initial clause, the model of `CNF.configLTS`), Definition 7 (the pebble game in which an inference may shift a pebble from a parent to the resolvent) and Lemma 8 (space equals that game's pebble number), Theorem 9 (`tree-size(F) ≥ 2 ^ space(F) - 1`, after Esteban and Torán), and the Section 4 statement that the pigeonhole formulas with `m > n` have resolution space exactly `n + 1` independently of the number of pigeons (the text says "holes", evidently a slip). The survey's numerical values are those of the shifting game, one less than clause space in the library's convention. The survey credits the pigeonhole result to its reference [29], J. Torán, “Lower bounds for the space used in resolution”, CSL 1999, LNCS 1683, 362–373; that paper was not inspected. Journal pagination was taken from the bibliographic record.

<a id="vonstengel07"></a>
## vonstengel07

Bernhard von Stengel. "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form." Chapter 3 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, pp. 53–78. https://doi.org/10.1017/CBO9780511800481.005 . The author's preprint https://www.maths.lse.ac.uk/Personal/stengel/TEXTE/agt-stengel.pdf was consulted on 2026-11-08 for Proposition 3.1, the example (3.3), Definition 3.2, Proposition 3.3, (3.5)–(3.6), the polytope form of nondegeneracy in §3.3, §3.4 and Corollary 3.7. Statement and equation numbers follow that preprint; its page numbers differ from the book's.

<a id="vww18"></a>
## vww18

Virginia Vassilevska Williams and R. Ryan Williams. "Subcubic Equivalences Between Path, Matrix, and Triangle Problems." *Journal of the ACM* 65(5), 27:1–27:38, 2018; preliminary version in FOCS 2010. https://doi.org/10.1145/3186893 . Bibliographic metadata checked on 2026-11-07. The authors' journal manuscript https://people.csail.mit.edu/virgi/tria-mmult-jv.pdf was consulted on 2026-11-08 for the negative triangle problem over a structure (Section 2), Theorem 4.1, Theorem 4.2, Lemma 4.1 and Lemma 4.2 (and its proof with parts of size `n^{1−a}`). Theorem and lemma numbers follow that manuscript.

<a id="wagnerfischer74"></a>
## wagnerfischer74

Robert A. Wagner and Michael J. Fischer. "The String-to-String Correction Problem." *Journal of the ACM* 21(1), 168–173, 1974. https://doi.org/10.1145/321796.321811 . The bibliographic data come from search summaries of the publisher record (2026-11-08). The full text is paywalled and was not inspected, so the paper's internal theorem and algorithm numbering is unverified and is not cited. The manual credits it with the edit-distance dynamic program under general letter costs, with traces (alignments) as the objects of minimum cost and with the `O(|x| |y|)` table, as these are standardly described.

<a id="wattenhofer16"></a>
## wattenhofer16

Roger Wattenhofer. *Principles of Distributed Computing*, lecture notes, ETH Zürich, Chapter 7 "Maximal Independent Set". https://disco.ethz.ch/courses/podc_allstars/lecture/chapter7.pdf (PDF dated 2016-08-23). Inspected 2026-11-08: Algorithm 7.12 ("Fast MIS 2"), Lemma 7.14 (edge removal), Theorem 7.15, Corollary 7.18 and the chapter notes, which attribute the algorithm to Métivier, Robson, Saheb-Djahromi and Zemmari (Distributed Computing 23(5–6), 2011) as a simplification of Luby (SIAM J. Comput. 15(4), 1986). Those two papers were not inspected.

<a id="williams25"></a>
## williams25

R. Ryan Williams. *Simulating Time With Square-Root Space*. arXiv:2502.17779v1 (25 February 2025), Appendix A, equation (6); version states to appear in STOC 2025. https://arxiv.org/abs/2502.17779v1 .

<a id="williamsonshmoys11"></a>
## williamsonshmoys11

David P. Williamson and David B. Shmoys. *The Design of Approximation Algorithms*. Cambridge University Press, 2011. https://doi.org/10.1017/CBO9780511921735 . Section 1.6 (Algorithm 1.2, Theorems 1.11 and 1.12) and the Chapter 1 Chapter Notes attribution of the greedy set-cover analysis to Chvátal (Mathematics of Operations Research 4(3), 233–235, 1979, https://doi.org/10.1287/moor.4.3.233) were checked against the authors' electronic edition at https://www.designofapproxalgs.com on 2026-11-07, as were Section 2.4 (Lemma 2.10, Theorems 2.11 and 2.12) and the Chapter 2 Chapter Notes, which attribute nearest addition and its analysis to Rosenkrantz, Stearns and Lewis (1977) and call the double-tree algorithm folklore. The handshake argument, Theorem 2.13 (Christofides' algorithm is a 3/2-approximation) and its proof, and the Chapter 2 Notes attribution to Christofides (reference [73]) were checked against the same edition on 2026-11-08, as were Exercise 2.5 (the MST 2-approximation for Steiner tree, metric part (a) and metric completion part (b)), Section 12.3 and the Chapter 12 Notes attribution of the factor-2 Steiner heuristic to Moore via Gilbert and Pollak (reference [130]). Section 2.2 (Algorithm 2.1, Theorems 2.3 and 2.4) and the Chapter 2 Chapter Notes, which attribute the k-center algorithm and analysis to Gonzalez (Theoretical Computer Science 38, 293–306, 1985, https://doi.org/10.1016/0304-3975(85)90224-5), an alternative 2-approximation to Hochbaum and Shmoys (Mathematics of Operations Research 10(2), 180–184, 1985, https://doi.org/10.1287/moor.10.2.180) and Theorem 2.4 to Hsu and Nemhauser (Discrete Applied Mathematics 1(3), 209–215, 1979, https://doi.org/10.1016/0166-218X(79)90044-1), were checked against the same electronic edition on 2026-11-08; the three original papers were not checked.

<a id="yao80"></a>
## yao80

Andrew Chi-Chih Yao. "New Algorithms for Bin Packing." *Journal of the ACM* 27(2), 207–227, 1980. https://doi.org/10.1145/322186.322187 . Bibliographic data and the abstract are from the Crossref record of the DOI, checked on 2026-11-08 UTC. The abstract defines `r(S)` as the maximum ratio `S(L)/L*` for large `L*`, where `S(L)` is the number of bins used by algorithm `S` and `L*` the minimum number needed. It states that every on-line algorithm `S` has `r(S) ≥ 3/2`. The item types `1/7 + ε`, `1/3 + ε` and `1/2 + ε` of the construction are as reported in [baloghbekesidosaepsteinlevin18](#baloghbekesidosaepsteinlevin18), Section 1. The full text was not inspected, since no open copy was found, so the theorem number and Yao's own proof are not recorded. [OnlineLowerBound](../Complexity/Algorithms/Lean/BinPacking/OnlineLowerBound.lean) cites the paper on that basis.

<a id="yekhanin12"></a>
## yekhanin12

Sergey Yekhanin. *Locally Decodable Codes*. Foundations and Trends in Theoretical Computer Science 6(3), 139–255, 2012. https://doi.org/10.1561/0400000030 . Definition 6.1 and Lemma 6.2 (§6.1.1, private information retrieval from perfectly smooth codes) were checked on 2026-11-08 against the author's draft at https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/LDC_now.pdf ; the numbering of the published monograph was not checked.

<a id="yao86"></a>
## yao86

Andrew Chi-Chih Yao. "How to Generate and Exchange Secrets (Extended Abstract)." *27th Annual Symposium on Foundations of Computer Science (FOCS 1986)*, 162–167, 1986. https://doi.org/10.1109/SFCS.1986.25 . Bibliographic data from the DOI record and secondary listings, cited as the customary origin of garbled circuits. The full text was not inspected in this pass.

<a id="younger67"></a>
## younger67

Daniel H. Younger. "Recognition and Parsing of Context-Free Languages in Time n³." *Information and Control* 10(2), 189–208, 1967. https://doi.org/10.1016/S0019-9958(67)80007-X . Bibliographic metadata was checked on 2026-11-08; the article body was not inspected. It is cited, with [Kasami 1965](#kasami65), as an original source of the CYK algorithm.

<a id="zivlempel78"></a>
## zivlempel78

Jacob Ziv and Abraham Lempel. "Compression of Individual Sequences via Variable-Rate Coding." *IEEE Transactions on Information Theory* 24(5), 530–536, 1978. https://doi.org/10.1109/TIT.1978.1055934 . Bibliographic data from the DOI record and secondary summaries. The incremental parsing rule (each phrase is the shortest new prefix) is attributed through [Cover and Thomas](#coverthomas06); the paper's text was not inspected in this pass.
