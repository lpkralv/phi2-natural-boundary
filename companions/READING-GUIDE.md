---
title: "Reading guide for the Goldbach generating series"
subtitle: "The Egami–Matsumoto conjecture: a natural boundary of the Goldbach generating series"
author: "For the author"
date: "23 November 2026, for the paper as posted on Hexagon (hexagon:2611.00834, version 2) and Zenodo"
toc: true
toc-depth: 2
mainfontoptions:
  - "Renderer=HarfBuzz"
  - "BoldFont=STIX Two Text"
  - '`BoldFeatures={Weight=700}`{=latex}'
  - "BoldItalicFont=STIX Two Text Italic"
  - '`BoldItalicFeatures={Weight=700}`{=latex}'
monofont: "Latin Modern Mono"
monofontoptions:
  - "Scale=0.85"
  - "BoldFont=Latin Modern Mono"
monofontfallback:
  - "STIX Two Math:mode=harf"
  - "STIX Two Text:mode=harf"
  - "Arial:mode=harf"
---

# How to use this guide

Keep the paper beside this guide. Read a numbered statement or a lettered input in the paper, then its matching subsection here. References to the primer lead to background by topic. Each item starts with a paraphrase of the paper, followed by intermediate steps. The worked examples and check questions are part of the guide.

The paper reuses letters, and the argument or context attached to each is what fixes its meaning. $F(x)=\sum\Lambda(n)e^{-nx}$ is a function of a positive real $x$; $\psi=-\zeta'/\zeta$; $H=\Phi_2-M$ is the holomorphic part under RH (Corollary B(iii)), while $\mathbb H$ is the half-plane $\operatorname{Re}s>1$ and $h(x)=F(x)-1/x$ is a function of real $x$. The pair series is $\mathcal C(s)$. In the proof of Theorem 5.4, $\mathcal T$ is the set of tail indices. In equation (25), $\widetilde E_r$ combines the entire tail integrals $E_j$. $B$ is the supremum of the real parts of the zeros, and $2B$ is the real point of Theorem C. $\mathcal Z$ is the set of non-trivial zeros, $\mathcal Z_{\mathrm{off}}$ the ones off the line, $\mathcal Z_{\mathrm c}$ the ones on it. The threshold of Sections 5 and 6 is $X$. The abstract weight estimates in Section 5 use $U$.

The main Lean names are given in Section 10 and Appendix A of the paper. This guide repeats them there and does not attach a formal counterpart to each statement in Chapters 1 to 8. The paper names only the main formal statements; for the intermediate results it says that the repository documentation lists the formal counterparts by section.

## Contents

1. Abstract and Section 1: introduction, Theorem A, Corollary B, Theorem C and Corollary D
2. Section 2: notation and classical inputs
3. Section 3: the decomposition
4. Section 4: continuation under $\mathrm H_\infty$
5. Section 5: non-cancellation, the phase cone
6. Section 6: the natural boundary
7. Section 7: sums of more than two prime powers
8. Section 8: proofs of Corollary B and Theorem C, and remarks
9. Section 9. Earlier work
10. Section 10. Formal verification and the statement on the use of AI
11. Appendix A. The Lean statements
12. A one-page map of the whole proof
13. Glossary, with first-definition locations

# 1. Abstract and Section 1: introduction, Theorem A, Corollary B, Theorem C and Corollary D

## Abstract

Egami and Matsumoto proved the continuation under RH and conjectured that it stops at $\operatorname{Re}s=1$. This paper proves the boundary from RH alone and from the weaker $\mathrm H_\infty$. The corresponding boundary for $\Phi_r$ is at $\operatorname{Re}s=r-1$. The phase estimate controls products of Gamma values associated with zeros of opposite-sign ordinates. A point whose every representation uses sufficiently high zeros has a nonzero coefficient. The proof finds such points accumulating at every point of the boundary, and under RH they are dense on the boundary itself.

The abstract also announces the positive-residue pole at $2B$ in the event that RH fails under $\mathrm H_\infty$. The conditional implications are checked in Lean. Corollary D obtains the boundaries unconditionally in writing using Alpöge's certified proof of RH.

## Section 1.1: equation (1), the series and the conjecture

The paper writes $\Phi_2$ two ways in equation (1): as the double series over prime-power pairs, and as a single Dirichlet series $\sum_{N\ge2}G_2(N)N^{-s}$ with $G_2(N)=\sum_{m+n=N}\Lambda(m)\Lambda(n)$ the weighted count of representations of $N$ as a sum of two prime powers. It bounds $G_2(N)\le N\log^2N$, so the series converges absolutely for $\operatorname{Re}s>2$. The series appears in Egami's 1999 paper. Under RH, Egami and Matsumoto identify the simple poles at $2$ and $1+\rho$ in the continuation half-plane and state the conjecture.

In equation (1), $N\ge2$ is an integer. There are $N-1$ ordered pairs $(m,n)$ with $m+n=N$, each weight $\Lambda(m)\Lambda(n)$ at most $\log^2N$, so $G_2(N)\le(N-1)\log^2N\le N\log^2N$. Absolute convergence for $\sigma>2$ is then the comparison
$$\sum_{N\ge2}G_2(N)N^{-\sigma}\le\sum_{N\ge2}N^{1-\sigma}\log^2N<\infty\qquad(\sigma>2),$$
which at $\sigma=3$ reads $\sum N^{-2}\log^2N$, convergent.

The normal approach starts from the right at a fixed height $\tau$. The point $1+i\tau+\eta$ moves horizontally to $1+i\tau$ as $\eta\downarrow0$. See the primer on atomic measures for how multiplying by $\eta$ isolates the weight at that height.

The definition of a natural boundary quantifies over every point of the line and every disc centred there. Agreement is required at every point of the right half-disc where the continuation is analytic. A denominator $s-\rho-\rho'$ gives a candidate singularity. The coefficients from all pairs with that denominator must be added before deciding whether there is a singularity. See the primer on meromorphic functions and natural boundaries.

### The hypothesis $\mathrm H_\infty$

Write $\mathcal Z$ for the set of non-trivial zeros and $\rho=\beta+i\gamma$ for one such zero, with real part $\beta$, ordinate $\gamma$ and multiplicity $m(\rho)$. For each $\delta>0$, $\mathrm H_\infty$ allows only finitely many zeros with $\beta>\tfrac12+\delta$. RH implies it, as does finiteness of all zeros off the critical line. With $B=\sup_\rho\beta$, Lemma 2.1 gives $B<1$ and shows that high zeros approach the line. Section 1.1 explains why the paper keeps this weaker premise in Theorem A after using Alpöge's certified RH in Corollary D.

Only finitely many zeros lie below any fixed height in modulus. $\mathrm H_\infty$ allows infinitely many off-line zeros, with real parts approaching $\tfrac12$ as their ordinates grow in modulus. A fixed strip $1-B\le\beta\le B$ with $B<1$ gives the margin for the phase estimate in Section 5 and the cutoff in Section 7. The approach of high zeros to the line in Lemma 2.1(b) is what keeps high pair sums from accumulating inside $\operatorname{Re}s>1$ (Lemma 4.1) and puts the interior poles of Proposition 6.3 near the line. Proposition 3.7 gives the holomorphic remainder $\mathcal A$ on $\operatorname{Re}s>\tfrac12$ without either consequence.

## Section 1.2. The results

### Theorem A

The paper assumes $\mathrm H_\infty$ and states three parts. (i) $\Phi_2$ has a meromorphic continuation to $\operatorname{Re}s>1$. (ii) $\operatorname{Re}s=1$ is a natural boundary, in the classical form: for no point $s_1$ on the line, no radius $r>0$ and no $g$ meromorphic on the disc $|s-s_1|<r$ does $g$ agree with $\Phi_2$ at every point of the half-disc $\{|s-s_1|<r,\ \operatorname{Re}s>1\}$ where $\Phi_2$ is analytic. (iii) For every integer $r\ge2$, $\Phi_r$ continues to $\operatorname{Re}s>r-1$ with $\operatorname{Re}s=r-1$ a natural boundary in the same sense.

Read (ii) with Primer, Natural boundaries. The restriction "where $\Phi_2$ is analytic" is there because $\Phi_2$ itself has poles in the half-disc; you cannot ask $g$ to equal a function at its own poles. The paragraph after the theorem explains why (i) says "meromorphic" and no more: under $\mathrm H_\infty$ the continuation may carry poles RH forbids. A zero with $\beta>\tfrac12$ and its conjugate give a pair sum with real part $2\beta\in(1,2)$; two zeros right of the line give a sum with real part above $1$. Which candidates are actual poles depends on cancellation, so Theorem A(i) refuses to list them. Theorem C settles one of them: the real point $2B$ is a pole whenever some zero lies off the line. Only under RH (Corollary B) does the pole list become clean.

### Corollary B

The paper defines, for a zero $\rho$, $a_\rho=m(\rho)\Gamma(\rho)$, and for real $\tau$ the atom
$$\mu\{\tau\}=\sum_{\substack{(\rho,\rho')\in\mathcal Z\times\mathcal Z\\ \gamma+\gamma'=\tau}}a_\rho a_{\rho'}\qquad\text{(equation (2))},$$
a sum over ordered pairs of zeros whose ordinates add to $\tau$ (a diagonal pair $(\rho,\rho)$ counted once), convergent by Lemma 3.4. For the ordered sum, for $\rho\ne\rho'$ the pairs $(\rho,\rho')$ and $(\rho',\rho)$ give two terms; where $\tau=2\gamma$ has the single representation $(\rho,\rho)$, $\mu\{\tau\}=a_\rho^2$, and counting the diagonal twice would give the factor $2$ printed in Egami and Matsumoto's (4.11) (Remark 8.3.1); at $\tau=0$ the pairs $(\rho,\bar\rho)$ and $(\bar\rho,\rho)$ are distinct, and both count (Remark 8.3.1). It is the complex mass of the measure at the single height $\tau$. Then, assuming RH: (i) the continuation is analytic on $\operatorname{Re}s>1$ except for simple poles at $s=2$ (residue $1$) and at $s=1+\rho$ (residue $-2m(\rho)/\rho$); (ii) $\operatorname{Re}s=1$ is a natural boundary; (iii) with $M(s)=2\psi(s-1)/(s-1)-1/(\Gamma(s)(s-2))$ and $H=\Phi_2-M$, the part $H$ is holomorphic on $\operatorname{Re}s>1$ and $\eta H(1+i\tau+\eta)\to\mu\{\tau\}/\Gamma(1+i\tau)$ as $\eta\downarrow0$, for every real $\tau$; (iv) for every $r\ge2$, the only poles in $\operatorname{Re}s>r-1$ are simple, at $r$ with residue $1/(r-1)!$ and at $r-1+\rho$ with residue $-r\,m(\rho)\Gamma(\rho)/\Gamma(r-1+\rho)$. The radial limit of $\eta\Phi_r(r-1+i\tau+\eta)$ is $\binom r2\mu\{\tau\}/\Gamma(r-1+i\tau)$ at $\tau\ne0$.

Here $\psi=-\zeta'/\zeta$ (Primer, The von Mangoldt function), and $M$ is the "main term" that carries all the poles; subtracting it leaves the holomorphic part $H$ whose radial behaviour reads off the atoms. The residue $-2m(\rho)/\rho$ is nonzero since $m(\rho)\ge1$ and $\rho\ne0$. The factor $2$ comes from the cross term $2x^{-1}h$ in $F^2=x^{-2}+2x^{-1}h+h^2$, whose transform gives the term $2\psi(s-1)/(s-1)$ of $M$: $\psi(s-1)$ has residue $-m(\rho)$ at $s=1+\rho$, and $1/(s-1)=1/\rho$ there. It is not a count of ordered pairs of zeros. Ordered-pair counting is a separate matter that lives in $\mu$: the paper's Remark 8.3.1 compares $\mu$ against Egami and Matsumoto's single-representation formula, where the diagonal differs by a factor $2$ because a diagonal pair $(\rho',\rho')$ is one ordered pair, not two. The paper credits the termwise radial-limit argument to Bhowmik, Ramaré and Schlage-Puchta and keeps as its own the subtraction of $M$ and the corrected value at $\tau=0$ (Remark 8.3.1). Corollary B is proved in Section 8.1 from the machinery of Theorem A, and the novelty sentence states plainly: no earlier complete proof of the $\Phi_2$ boundary without RH, and none complete under RH alone.

### Theorem C

The paper returns to $\mathrm H_\infty$ alone and recalls $B=\sup_\rho\beta$. Its lead-in sentence carries the whole idea: if some zero lies off the line, then among the candidate poles that Theorem A leaves undecided there is one at which nothing can cancel. The pairs of zeros with sum $2B$ are exactly the pairs $(\rho,\bar\rho)$ with $\beta=B$, and each carries the positive coefficient $a_\rho a_{\bar\rho}=m(\rho)^2|\Gamma(\rho)|^2$.

Then the statement. Assume $\mathrm H_\infty$. (i) If some zero has $\beta\ne\tfrac12$, then $\tfrac12<B<1$, the set of zeros with $\beta=B$ is finite and not empty, and the real point $2B\in(1,2)$ is a simple pole of $\Phi_2$ with residue
$$\frac1{\Gamma(2B)}\sum_{\rho\in\mathcal Z,\ \beta=B}m(\rho)^2|\Gamma(\rho)|^2>0 .$$
The sum runs over both $\rho$ and $\bar\rho$, so each conjugate pair $\rho\ne\bar\rho$ contributes $2m(\rho)^2|\Gamma(\rho)|^2$. (ii) RH holds if and only if $\Phi_2$ has no pole in the real interval $(1,2)$.

Unpack part (i) one clause at a time. A zero off the line, or its mirror image $1-\bar\rho$, lies to the right of the line, so $B>\tfrac12$; $B<1$ is Lemma 2.1(a); hence $1<2B<2$. "Finite and not empty" says the supremum $B$ is attained, a real part that at least one zero has; that needs $\mathrm H_\infty$ and is the first step of the proof in Section 8.2. The sum in the residue is the coefficient $\nu(2B)$ of Section 4 (equation (14)), so the residue is $\nu(2B)/\Gamma(2B)$. Why each term is positive: conjugation preserves zeros and multiplicities, and $\Gamma(\bar z)=\overline{\Gamma(z)}$ by (G1), so $a_{\bar\rho}=m(\rho)\overline{\Gamma(\rho)}$ and $a_\rho a_{\bar\rho}=m(\rho)^2\Gamma(\rho)\overline{\Gamma(\rho)}=m(\rho)^2|\Gamma(\rho)|^2$, which is positive because $\Gamma$ has no zeros. And $\Gamma(2B)>0$ because $2B$ is a positive real number. Compare this with Section 5: there the weights are complex numbers that might cancel, and a phase cone is needed to show they do not. Here every weight is a positive real number, and positive numbers cannot add to zero.

The paper's paragraph after the theorem sets the limits of the statement. The interval in (ii) is open: it excludes $s=2$, which is a pole under RH (Corollary B(i)). Only $2B$ is shown to be a pole. Other real points of $(1,2)$ can be pair sums, for instance $2\beta$ for a zero with $\tfrac12<\beta<B$, and Theorem C says nothing about them.

Section 9 discusses two precedents. Under RH, Bhowmik and Schlage-Puchta show that $2\rho_1$ is singular. The chosen pair outweighs the much higher pairs, and a finite check rules out other representations of comparable height. Their point lies on $\operatorname{Re}s=1$. Theorem C finds a pole inside the continuation half-plane through the positivity of every weight. Matsumoto's survey already includes $2B$ among the candidate pair sums.

The earlier RH criterion is due to Bhowmik, Halupczok, Matsumoto and Suzuki in the case $q=1$, written out for $\Phi_2$ by Bhowmik and Halupczok. If $B<1$, the infimum of the $\sigma\ge\tfrac32$ for which $\Phi_2(s)-1/(s-2)$ extends analytically to $\operatorname{Re}s>\sigma$ is $1+B$. In particular, RH is equivalent to analyticity on $\operatorname{Re}s>\tfrac32$. This test uses the poles at $1+\rho$ and needs only $B<1$, which follows from $\mathrm H_\infty$. Theorem C(ii) gives a new form of the criterion, and part (i) proves that the candidate $2B$ is a simple pole with positive residue.

### Corollary D

The paper states that Theorem A and Corollary B hold unconditionally. Alpöge's Lean result, certified as Mathlib's `RiemannHypothesis`, supplies the premise for B. Under RH every non-trivial zero has $\beta=\tfrac12$, so the exceptional set in $\mathrm H_\infty$ is empty for each $\delta>0$. That supplies the premise for A. The other inputs in Section 2 are unconditional classical results. Section 10 sets out how the paper assembles the proof and what the author checked. With RH established, Theorem C describes what an off-line zero would force. [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Joint certification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Sutherland's independent checks](https://math.mit.edu/~drew/grh/)

## Section 1.3. The idea

The paper sketches the argument before proving the individual pieces.

### The decomposition, and why it fails off the line

The paper writes $F(x)=\sum\Lambda(n)e^{-nx}$ and displays the identity everything starts from: integration term by term gives $\Gamma(s)\Phi_2(s)=\int_0^\infty F(x)^2x^{s-1}\,dx$ for $\operatorname{Re}s>2$. Since $F$ decays exponentially as $x\to\infty$, the continuation of $\Phi_2$ is decided by the behaviour of $F$ as $x\downarrow0$, and there $1/x$ is the main term of $F$, coming from the pole of $-\zeta'/\zeta$ at $1$ (Lemma 3.5). So the paper puts $h(x)=F(x)-1/x$, the oscillating part. Then $F^2=x^{-2}+2x^{-1}h+h^2$, and the first two terms give a function meromorphic on the whole plane. The explicit formula writes $h=-Z+c_0+V$ with $Z(x)=\sum_\rho a_\rho x^{-\rho}$, a constant $c_0$ and $V(x)=O(x^{1/2})$, and the Mellin transform of $Z^2$ over $(0,1]$ is the pair sum
$$\mathcal C(s)=\sum_{(\rho,\rho')\in\mathcal Z\times\mathcal Z}\frac{a_\rho a_{\rho'}}{s-\rho-\rho'},$$
a sum of simple fractions whose candidate poles are the pair sums $\rho+\rho'$ (candidate, because the fractions that share a point can cancel there). Under RH every pair sum lies on $\operatorname{Re}s=1$, and $\eta\,\mathcal C(1+i\tau+\eta)\to\mu\{\tau\}$ because each term $\eta/(\eta+i(\tau-\gamma-\gamma'))$ has modulus at most $1$; a natural boundary follows once $\mu\{\tau\}\ne0$ on a dense set of $\tau$.

$Z$ is the zero-sum of the explicit formula; $a_\rho=m(\rho)\Gamma(\rho)$ again. The modulus-at-most-$1$ bound is the computation $\lvert\eta/(\eta+i(\tau-\gamma-\gamma'))\rvert=\eta/\sqrt{\eta^2+(\tau-\gamma-\gamma')^2}\le1$, and it $\to0$ for any pair sum $\gamma+\gamma'\ne\tau$, however close, as $\eta\downarrow0$. That vanishing is what replaces hypothesis (B): no lower bound on the spacing of pair sums is needed, because the factor $\eta$ kills every off-$\tau$ term in the limit (Primer, Atomic measures and the radial limit).

The paper then says both steps fail off the line. A zero with $\beta>\tfrac12$ pairs with its conjugate to give the real point $2\beta\in(1,2)$, inside $\operatorname{Re}s>1$; off-line zeros can give pair sums with real part $\beta+\beta'\ne1$. And the radial bound fails: the term becomes $\eta/(\eta+1-\beta-\beta'+i(\tau-\gamma-\gamma'))$, whose denominator vanishes when both $\eta=\beta+\beta'-1$, which is positive when $\beta+\beta'>1$, and $\tau=\gamma+\gamma'$, so on the normal at that height the term blows up at a positive $\eta$ rather than dying. This is why the $\mathrm H_\infty$ proof splits into cases and does not use the radial limit when infinitely many zeros are off the line.

### The five moves

The paper lists five steps; this is the spine of Chapters 3 to 7.

1. **An exact decomposition with no hypothesis** (Section 3). Writing $h^2=Z^2-2c_0Z+((c_0+V)^2-2ZV)$ and moving the cross term $-2c_0Z$, whose Mellin transform is $-2c_0L(s)$ with $L(s)=\sum_\rho a_\rho/(s-\rho)$ meromorphic on $\mathbb C$, into the meromorphic part, gives $\Phi_2=M_0+(\mathcal C+\mathcal A)/\Gamma$ with $M_0$ meromorphic on $\mathbb C$ and $\mathcal A$ holomorphic on $\operatorname{Re}s>\tfrac12$. $M_0$ and $\mathcal A$ involve the zeros too (through $\psi$, $L$, $Z$ and $V$), but both already extend across the line, so, as the paper says, whatever obstructs continuation of $\Phi_2$ across the line is in $\mathcal C$.
2. **Continuation** (Section 4). Under $\mathrm H_\infty$, high zeros have real parts near $\tfrac12$, so high pairs have sums near the line, never deep inside $\operatorname{Re}s>1$. On a compact subset of $\operatorname{Re}s>1$ only finitely many pairs are polar; the rest converge, so $\mathcal C$, hence $\Phi_2$, is meromorphic there. The residue of $\mathcal C$ at $s_0$ is $\nu(s_0)$, the sum of $a_\rho a_{\rho'}$ over all representations $s_0=\rho+\rho'$.
3. **Non-cancellation** (Section 5). A candidate $s_0$ is a pole when $\nu(s_0)\ne0$ (this is Proposition 4.2(c), which needs $s_0$ in $\operatorname{Re}s>1$ and different from $2$ and from the points $1+\rho$), and $\nu(s_0)$ can have many terms. If $s_0$ has bounded imaginary part and at least one representation, and every representation uses two zeros above the corresponding threshold, each is a pair of opposite signs $\rho=b+i(u+\tau)$, $\rho'=c-iu$ with $u$ large; Stirling gives the modulus a factor $e^{-\pi u}$, so the lowest representation at height $u_0$ dominates everything more than $\sqrt{u_0}$ above it, and the ones within $\sqrt{u_0}$ have phases that spread, in the limit, by at most $\pi(B-\tfrac12)$ about a common direction (at finite height there are also the drift and the Stirling error). The proof uses a wider cone of half-angle $\pi B/2<\pi/2$ about the direction $\tau\log u_0$ (Lemma 5.2), so all head terms push the sum the same way and nothing cancels the lowest. On the line $b=c=\tfrac12$ the spread shrinks to the slow drift $\tau\log(u/u_0)$, the case RH uses.
4. **Two cases** (Section 6). If infinitely many zeros lie off the line, pair sums $\bar\rho_n+\rho'_n$ with real part $>1$ tend to $1+iy$ from inside $\operatorname{Re}s>1$ (Littlewood's gap theorem supplies the partner, $\mathrm H_\infty$ pushes both real parts to $\tfrac12$); their representations are all high, so step (3) makes them genuine poles, and interior poles accumulating at $1+iy$ forbid continuation. If only finitely many lie off the line, those pairs give a function meromorphic across the line, and the RH argument (radial limits, dense nonzero atoms, blow-up along the normal) runs on the rest.
5. **Sums of $r$ prime powers** (Section 7). Expanding $F^r=(1/x+h)^r$, keeping exact the finitely many zeros with $\beta$ above a cutoff and bounding the rest, writes $\Phi_r$ as $c_r(s)\Phi_2(s-r+2)$ plus pieces meromorphic or holomorphic past the line, with $c_r$ zero-free; so an extension of $\Phi_r$ across $\operatorname{Re}s=r-1$ would extend $\Phi_2$ across $\operatorname{Re}s=1$.

The paper then notes that under RH, $\mathcal C$ has no poles in $\operatorname{Re}s>1$, the infinite-off-line case does not occur, and the poles and radial limits come out explicitly (Section 8.1). It adds one sentence on Theorem C(i): it is steps (1) and (2) at the single point $s_0=2B$. Every term of $\nu(2B)$ is positive, so no phase estimate is needed, and $M_0$ is analytic there because $2B\ne2$, as $B<1$, and $\zeta$ has no real zero in $(0,1)$ (Section 8.2). Step (3), the hard one, is not used for Theorem C at all.

Section 1.3 closes with a roadmap. Section 2 collects the classical inputs; Sections 3 to 6 prove Theorem A(i) and (ii); Section 7 proves Theorem A(iii); Section 8 proves Corollary B and Theorem C and adds remarks not used in the proofs; Section 9 compares earlier work, and Section 10 describes the formal verification.

## Section 1.4. What is earlier and what is new

The paper credits the continuation and residues under RH to Egami and Matsumoto, and the unconditional continuation on $\operatorname{Re}s>2B$ to Bhowmik, Halupczok, Matsumoto and Suzuki. It cites earlier decompositions, including Cantarini, Gambini and Zaccagnini's formula, which with the argument of Section 4 also gives Theorem A(i). Billington, Cheng, Schettler and Suriajaya use the smoothing $F$, its square and the explicit formula with the constant $-\log(2\pi)$. They evaluate the smoothing at $x=1/N$.

The paper credits Bhowmik, Ramaré and Schlage-Puchta for the termwise radial limit and Egami and Matsumoto for its single-representation coefficient. Bhowmik and Schlage-Puchta and Bhowmik, Ramaré and Schlage-Puchta compare the lowest pair with the much higher pairs. Earlier work uses Littlewood's theorem to obtain density, and Egami and Matsumoto and Bhowmik and Schlage-Puchta use radial blow-up to exclude extension. The split into finitely and infinitely many off-line zeros, and the use of off-line zeros to accumulate singularities, follow earlier work of Bhowmik and Schlage-Puchta.

The paper lists as new the unconditional boundaries in Corollary D, the complete continuation under $\mathrm H_\infty$, the phase cone and the choice of points with only high representations, and the direct normalized decomposition in equation (13). It also lists the subtraction of $M$ in the radial limit, which gives the value at the real boundary point, the reduction for $\Phi_r$ under $\mathrm H_\infty$, and the proof of the positive-residue pole at $2B$. The Mellin reduction gives an independent argument for the higher series, as Remark 8.3.2 explains. Matsumoto's survey already listed $2B$ among the candidates. Section 9 discusses the earlier pole criterion through $1+\rho$.

## Check your understanding

1. **Question.** Why does $\mathrm H_\infty$, not RH, suffice for Theorem A? **Answer.** The continuation and the non-cancellation use only that high zeros have real parts near $\tfrac12$ (so high pairs stay near the line) and that $B=\sup\beta<1$. Both follow from $\mathrm H_\infty$ (Lemma 2.1). RH is the special case $B=\tfrac12$.
2. **Question.** Why is Theorem A(i) only "meromorphic", with no pole list? **Answer.** Off the line, pair sums can land inside $\operatorname{Re}s>1$ (e.g. the real point $2\beta$), and whether a candidate is a real pole depends on cancellation the theorem does not resolve. The clean list is Corollary B(i), under RH.
3. **Question.** Where does the factor $\eta$ do its work? **Answer.** In the radial limit it kills every pair sum but $\tau$, since $\eta/(\eta+i(\tau-\gamma-\gamma'))\to0$ for $\gamma+\gamma'\ne\tau$. That removes any need for a spacing hypothesis like (B). The bound that justifies the limit, each term of modulus at most $1$, has no analogue for a pair with $\beta+\beta'>1$, and the paper proves no formula for the radial limit of the full pair sum under $\mathrm H_\infty$. That is why the infinite-off-line case avoids the radial limit; the finite-off-line case still takes it, on the on-line pair sum $\mathcal C_{\mathrm c}$.
4. **Question.** What is a "candidate pole" versus an "actual pole"? **Answer.** A candidate is a pair sum $\rho+\rho'$, a denominator in $\mathcal C$. At a point $s_0$ of $\operatorname{Re}s>1$ other than $2$ and the points $1+\rho$, where $M_0$ is analytic, a candidate $s_0$ is an actual pole of $\Phi_2$ exactly when the coefficient $\nu(s_0)=\sum_{\rho+\rho'=s_0}a_\rho a_{\rho'}$, there the residue of $\mathcal C$, is nonzero (Proposition 4.2(c)); every point of the strip $1<\operatorname{Re}s<2-B$ qualifies. Non-cancellation (Section 5) is the proof that $\nu(s_0)\ne0$ for the points the boundary argument keeps; at $2B$ positivity does the same job (Theorem C).
5. **Question.** Is the RH criterion of Theorem C(ii) new? **Answer.** Only in form, as the paper says. A criterion through the poles at $1+\rho$ is the case $q=1$ of Proposition 3 of Bhowmik, Halupczok, Matsumoto and Suzuki, and it needs only $B<1$, which $\mathrm H_\infty$ implies. What Theorem C adds is the proof that the real point $2B$ is a pole.
6. **Question.** Why can nothing cancel at $2B$? **Answer.** A pair with sum $2B$ has real parts adding to $2B$, each at most $B$, so both equal $B$, and ordinates adding to $0$; so it is $(\rho,\bar\rho)$ with $\beta=B$, and its weight $m(\rho)^2|\Gamma(\rho)|^2$ is a positive real number.

# 2. Section 2: notation and classical inputs

Section 2 is bookkeeping: the conventions, the three theorems on the zeros the proof borrows, and four facts about $\Gamma$. Nothing is proved about $\Phi_2$ here. Read it once, then return as each item is used.

## The opening: conventions, equations (3)–(4), and the symmetries

The paper fixes that $C$ is a positive constant that may change from line to line, while a constant it will reuse carries a subscript; it fixes $s=\sigma+it$, $w$, $z$ as complex variables, $\mathbb H=\{\operatorname{Re}s>1\}$ (the paper now adds "a right half-plane", since $\mathbb H$ often means the upper half-plane elsewhere), $D(z_0,r)$ the open disc; and in equation (3) it defines $\psi=-\zeta'/\zeta$ and the counting function $N(t)=\sum_{\rho\in\mathcal Z,\ 0<\gamma\le t}m(\rho)$. It records three facts about $\psi$ (its Dirichlet series and the bound $|\psi(z)|\le\psi(\operatorname{Re}z)$ for $\operatorname{Re}z>1$; meromorphy with simple poles at $z=1$, residue $1$, and at each zero, residue $-m(\rho)$); equation (4) folds the factor $1/(2\pi i)$ into the symbol $\int_{(c)}$; and it states the zero-free regions and the two symmetries of the zeros.

$N(t)$ counts zeros by height, with multiplicity, from the real axis up to $t$; $N(t)=0$ for $t\le0$. The bound $|\psi(z)|\le\psi(\operatorname{Re}z)$ for $\operatorname{Re}z>1$ is the triangle inequality on the Dirichlet series: each term $\Lambda(n)n^{-z}$ has modulus $\Lambda(n)n^{-\operatorname{Re}z}$ because $|n^{-z}|=n^{-\operatorname{Re}z}$, and $\Lambda\ge0$, so summing moduli gives the real-point value. The residue signs come from Primer, Meromorphic functions: the logarithmic derivative of $(z-a)^m g(z)$ with $g(a)\ne0$ has residue $m$ at $a$; negating gives $\psi$ residue $-m(\rho)$ at a zero, and $+1$ at the pole $z=1$ (where $\zeta$ has a simple pole, $m=-1$). These signs are what the contour shift of Lemma 3.5 picks up, at $w=1$ and at the zeros.

Equation (4) is the convention $\int_{(c)}f(w)\,dw=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}f(w)\,dw=\frac1{2\pi}\int_{\mathbb R}f(c+iy)\,dy$, the line read upward with $f$ integrable on it (Primer, Cauchy's theorem). The variable $c$ is the real abscissa of the vertical line, $y$ the real integration variable; every use below keeps that $1/2\pi$.

Two symmetries of the zeros are stated here and used throughout. Conjugation $\rho\mapsto\bar\rho$ preserves $\mathcal Z$ and multiplicities, from $\zeta(\bar z)=\overline{\zeta(z)}$. The functional equation $\zeta(s)=2^s\pi^{s-1}\sin(\tfrac12\pi s)\Gamma(1-s)\zeta(1-s)$ gives $\rho\mapsto1-\rho$, and combining, $\rho\mapsto1-\bar\rho$, which keeps the ordinate and sends $\beta$ to $1-\beta$. The paper calls these the symmetries of the zeros; they are why $B\ge\tfrac12$ (Lemma 2.1), why negative ordinates can be counted by positive ones (Lemma 3.2), and why a partner zero can always be reflected onto $\beta\ge\tfrac12$ (Chapter 6). The zero-free-region facts ($\zeta\ne0$ on $\operatorname{Re}s\ge1$, none with $\operatorname{Re}s\le0$ except the trivial zeros) give $0<\beta<1$ for every non-trivial zero.

## Section 2.1. The classical inputs on the zeros, (Z1)–(Z5)

The paper cites Titchmarsh for the first three facts and proves the last two. (Z1): a constant $C_1$ with $N(t+1)-N(t)\le C_1\log(t+3)$ for all $t\ge0$ (the count of zeros in a unit interval $(t,t+1]$ is $O(\log(t+3))$; this is an upper bound, with no matching lower bound claimed). (Z2): Littlewood's gap theorem, a constant $A$ with some ordinate within $A/\log\log\log t$ of any large $t$ (zeros are never too sparse). (Z3): the local expansion of $\psi$, that $\psi(z)+\sum_{|\gamma-\operatorname{Im}z|\le1}m(\rho)/(z-\rho)$ is $O(\log|\operatorname{Im}z|)$ for $-1\le\operatorname{Re}z\le2$, $|\operatorname{Im}z|\ge2$ and $\zeta(z)\ne0$, the last condition because $\psi$ and the sum both have poles at the zeros (near a zero, $\psi$ is its nearby simple poles plus a mild remainder). (Z4): ordinates are unbounded above, from (Z2).

These three are Primer, The three classical inputs (Z1) to (Z3). Hold the plain reading: (Z1) counts, (Z2) spaces, (Z3) locally resolves $\psi$ into its poles. For (Z3) the paper now quotes Titchmarsh's own form, which is stated for $\zeta'/\zeta$: $\zeta'(s)/\zeta(s)=\sum_{|t-\gamma|\le1}1/(s-\rho)+O(\log t)$, uniformly for $-1\le\sigma\le2$ and large $t$. Since $\psi=-\zeta'/\zeta$, the sign of the sum changes, which is why (Z3) has $\psi(z)+\sum$. The paper notes it writes (Z3) with the multiplicities $m(\rho)$, since $\zeta'/\zeta$ has residue $m(\rho)$ at $\rho$, and uses it down to $|\operatorname{Im}z|\ge2$, the extension from large $t$ being elementary (bounded on a compact strip away from the zeros, bounded near each zero because $\psi(z)+m(\rho_0)/(z-\rho_0)$ is analytic there, and negative $t$ by conjugation). (Z4) is the one-line deduction: by (Z2) at a $t$ with $\log\log\log t>1$ and $t>T+A$, some ordinate exceeds $t-A>T$.

A sentence added after the list says where the hand-checking sits: the passages from Titchmarsh's statements to (Z1) and (Z3), and from the DLMF to (G4) below, are argued in this section and are not formalized; the formal developments take these forms as hypotheses (Section 10).

### (Z5). No real zero in $(0,1)$

The paper uses the alternating zeta series. The series $\sum_{n\ge1}(-1)^{n-1}n^{-s}$ converges for $\operatorname{Re}s>0$, by Abel summation, to an analytic function. On $\operatorname{Re}s>1$ its sum is $(1-2^{1-s})\zeta(s)$, and by the identity theorem this identity extends to all $s\ne1$ with $\operatorname{Re}s>0$. For real $0<\sigma<1$ the series is an alternating series with decreasing terms, so its sum is at least $1-2^{-\sigma}>0$, while $1-2^{1-\sigma}<0$; hence $\zeta(\sigma)\ne0$. The paper notes that the formal development proves this fact by another argument.

The steps the paper skips. Where the factor comes from: for $\operatorname{Re}s>1$ everything converges absolutely, and the alternating series is the full series minus twice its even terms, $\sum n^{-s}-2\sum(2n)^{-s}=\zeta(s)-2\cdot2^{-s}\zeta(s)=(1-2^{1-s})\zeta(s)$. Why the sum is at least $1-2^{-\sigma}$: for an alternating series whose terms decrease to $0$, the sum lies between any two consecutive partial sums, here between $1-2^{-\sigma}$ and $1$. Why the factor is negative: $1-\sigma>0$, so $2^{1-\sigma}>1$. A positive number equal to a negative number times $\zeta(\sigma)$ forces $\zeta(\sigma)<0$, in particular $\zeta(\sigma)\ne0$. At $\sigma=\tfrac12$: the series is at least $1-2^{-1/2}\approx0.293$ and the factor is $1-2^{1/2}\approx-0.414$. Primer, The zeta function, has this as a worked topic, with the meaning of Abel summation.

## Section 2.2. The hypothesis

### Lemma 2.1. The two consequences of $\mathrm H_\infty$

The paper writes $B=\sup_{\rho}\beta$ and, assuming $\mathrm H_\infty$, proves: (a) $\tfrac12\le B<1$, and $1-B\le\beta\le B$ for every zero; (b) for every $\delta>0$ there is a height $T$ past which $|\beta-\tfrac12|\le\delta$.

These are the two consequences of $\mathrm H_\infty$ that the proof of Theorem A(i) and (ii) uses. The paper invokes $\mathrm H_\infty$ directly twice more, each time for a finiteness statement: in Section 7.1, to make the extracted set $\mathcal E_*$ finite, and in Section 8.2, to show that $B$ is attained by finitely many zeros. Part (a) puts every non-trivial zero in the strip $1-B\le\beta\le B$, strictly inside the critical strip; the half-plane $\operatorname{Re}s>B$ contains no zeros. The proof: $\mathrm H_\infty$ with $\delta=\tfrac14$ leaves only finitely many zeros with $\beta>\tfrac34$, each below $1$, so $B$ is at most the largest of $\tfrac34$ and those finitely many values (not equal to it: under RH, $B=\tfrac12$), hence $B<1$; $\mathcal Z$ is nonempty by (Z4), and of $\rho,1-\bar\rho$ one has real part $\ge\tfrac12$, so $B\ge\tfrac12$; and $1-\beta$ is the real part of $1-\bar\rho$, so $1-\beta\le B$, giving the lower bound $\beta\ge1-B$. Part (b): the zeros with $\beta>\tfrac12+\delta$ are finitely many, so take $T$ above all their ordinates in modulus. For $|\gamma|>T$, $\beta\le\tfrac12+\delta$, and the same for $1-\bar\rho$ gives $1-\beta\le\tfrac12+\delta$, that is $\beta\ge\tfrac12-\delta$. So high zeros are squeezed to the line. Keep (b) in mind: it is the exact statement "high zeros are near the line" that Chapters 4 and 6 lean on.

## Section 2.3: the Gamma facts, (G1)–(G4)

The paper lists four standard facts about $\Gamma$, from the NIST library. (G1): $\Gamma$ has no zeros, $1/\Gamma$ is entire, $\Gamma(z+1)=z\Gamma(z)$, $\Gamma(1)=\Gamma(2)=1$, $\Gamma(\bar z)=\overline{\Gamma(z)}$. (G2): $|\Gamma(\tfrac12+ix)|^2=\pi/\cosh\pi x$ for real $x$. (G3): on a vertical strip $a\le\operatorname{Re}z\le a'$ with $0<a$, $|\Gamma(z)|(1+|\operatorname{Im}z|)^n$ is bounded for every $n\ge0$, so $\Gamma$ decays there faster than any power of $|\operatorname{Im}z|$. The strip must lie in positive real part: a strip that contains $0$ or a negative integer contains a pole of $\Gamma$, and no bound holds on all of it. Lemma 3.3 carries the decay to $-\tfrac12\le\operatorname{Re}w\le2$, but only for $|\operatorname{Im}w|\ge1$. (G4): Stirling on vertical strips: for real $x_1\le x_2$ there are $C$ and $T_0$ with $|\Gamma(z)-e^{\mathrm{St}(z)}|\le(C/|\operatorname{Im}z|)|e^{\mathrm{St}(z)}|$ for $x_1\le\operatorname{Re}z\le x_2$ and $|\operatorname{Im}z|\ge T_0$, where $\mathrm{St}(z)=(z-\tfrac12)\operatorname{Log}z-z+\tfrac12\log2\pi$. The inequality is claimed only above the height $T_0$.

These are Primer, Gamma. The one to study is (G4), because Section 5 needs the argument of $\Gamma$ as well as its size, and $\mathrm{St}(z)$ carries the phase. $\operatorname{Log}$ is the principal logarithm. The paper derives (G4) from the multiplicative Stirling form $\Gamma(z)=e^{-z}z^z(2\pi/z)^{1/2}\Gamma^*(z)$ with $\Gamma^*(z)=1+O(1/z)$: with principal powers the prefactor $e^{-z}z^z(2\pi/z)^{1/2}$ is exactly $e^{\mathrm{St}(z)}$ (the only logarithm being $\operatorname{Log}z$ inside $\mathrm{St}$), and on the part of the strip with $|\operatorname{Im}z|\ge T_0$ one has $|z|\ge|\operatorname{Im}z|$, so the $O(1/z)$ error is at most $C/|\operatorname{Im}z|$. (G2) is the reflection formula at $z=\tfrac12+ix$, where $1-z=\bar z$ and $\sin\pi z=\cosh\pi x$; it gives the modulus of $\Gamma$ on the critical line exactly, and Section 5 uses it for its on-line checks (the example after Lemma 5.2 and the same-sign pairs in the opening of Section 5). The $e^{-\pi u}$ decay of the weights for general real parts comes from (G4), through Lemmas 5.1 and 5.3. (G3) with a high power is what makes $\Gamma$ integrable on vertical lines, used repeatedly for the contour integrals in Section 3.

# 3. Section 3: the decomposition

This is the technical core of the hypothesis-free part. The goal (Proposition 3.7) is one identity, true with no assumption on where the zeros are, that puts into a single function, the pair sum $\mathcal C$, the part of $\Phi_2$ that decides whether it continues to the line and across it; the other terms extend across the line. The build-up is: the Mellin transform of $F^2$ and its split (Lemma 3.1); a count of zeros making $\sum|a_\rho|$ converge (Lemmas 3.2–3.4); the explicit formula for $h$ (Lemma 3.5); and a general lemma on sums of simple fractions (Lemma 3.6) used to assemble the identity. Nothing here uses $\mathrm H_\infty$ or RH.

## Section 3.1. The Mellin transform

### Lemma 3.1

The paper defines (equation (5)) $F(x)=\sum_{n\ge1}\Lambda(n)e^{-nx}$, $h(x)=F(x)-1/x$, and the kernel $k_x(w)=x^{-w}\Gamma(w)\psi(w)$; it records the two Mellin transforms (equation (6)) $\int_0^\infty F x^{z-1}=\Gamma(z)\psi(z)$ for $\operatorname{Re}z>1$ and $\int_0^\infty F^2 x^{s-1}=\Gamma(s)\Phi_2(s)$ for $\operatorname{Re}s>2$, the Mellin inversion $F(x)=\int_{(c)}k_x$ for $c>1$ (equation (7)), the pieces $e_1,E_2,R$ (equation (8)) got by splitting the integrals at $x=1$, the main term $M(s)=2\psi(s-1)/(s-1)-1/(\Gamma(s)(s-2))$ (equation (9)), and then Lemma 3.1: for $\operatorname{Re}s>2$, $R(s)$ converges absolutely and $\Gamma(s)\Phi_2(s)=\Gamma(s)M(s)+E_2(s)-2e_1(s-1)+R(s)$.

The objects are Primer, The Mellin transform. $F$ is non-negative, continuous on $(0,\infty)$, with $F(x)\le Ce^{-x}$ for $x\ge1$ (since $\Lambda(n)\le n$ and $\sum ne^{-nx}$ sums the geometric-type tail); its $1/x$ singularity at $0$ is the pole of $\zeta$ showing up, and $h=F-1/x$ is $F$ with that singularity removed. The first transform in (6) is the termwise integral $\int_0^\infty e^{-nx}x^{z-1}\,dx=\Gamma(z)n^{-z}$ summed against $\Lambda(n)$ (Tonelli to justify the swap, then Fubini); the second is the same for $F^2=\sum_{m,n}\Lambda(m)\Lambda(n)e^{-(m+n)x}$, convergent for $\operatorname{Re}s>2$ by the $N\log^2N$ bound of Section 1.1. Mellin inversion (7) is Primer, Mellin inversion: apply Fourier inversion to $\varphi(v)=F(e^{-v})e^{-cv}$, whose Fourier transform is the first integral in (6); $k_x$ is integrable on the line $\operatorname{Re}w=c$ by (G3) and $|\psi(c+iy)|\le\psi(c)$.

The split is the move that matters. On $(0,1]$, $F^2=x^{-2}+2x^{-1}h+h^2$; integrating each term against $x^{s-1}$ and sending the tails over $[1,\infty)$ into the entire functions $e_1,E_2$ (entire because $F\le Ce^{-x}$ there), the behaviour at the line is decided by $R(s)=\int_0^1h^2x^{s-1}\,dx$. The proof of Lemma 3.1 runs this bookkeeping: equation (10) is $\Gamma(z)\psi(z)=1/(z-1)+\int_0^1 h x^{z-1}+e_1(z)$ (the $1/(z-1)$ is $\int_0^1 x^{-1}x^{z-1}=1/(z-1)$, the contribution of the removed singularity); then for $\operatorname{Re}s>2$ the square gives $\Gamma(s)\Phi_2(s)=1/(s-2)+2\int_0^1 h x^{s-2}+R(s)+E_2(s)$, and replacing the middle integral by (10) at $z=s-1$, together with $\Gamma(s-1)/\Gamma(s)=1/(s-1)$, turns the first terms into $\Gamma(s)M(s)$. The expansion of $F^2$, and in particular keeping the cross term $2x^{-1}h$ exact rather than bounding it, is what Section 3.4 needs so that a merely bounded remainder in the explicit formula suffices.

## Section 3.2: Lemmas 3.2–3.4, counting the zeros

### Lemma 3.2 (Counting)

The paper states three bounds: (a) a constant $C_2$ with every window of radius one $\mathcal W_t=\{\rho:|\gamma-t|\le1\}$ (so of width two) finite and of total multiplicity at most $C_2\log(|t|+3)$; (b) $m(\rho)\le C_2\log(|\gamma|+3)$; (c) $\sum_\rho(1+|\gamma|)^{-2}<\infty$.

All three are consequences of (Z1) and conjugate symmetry. (a): a window has finitely many zeros (Section 2), and counting the positive-ordinate ones by at most three integer unit intervals and applying (Z1) bounds it, the zeros at $\gamma=0$ being a fixed finite count. (b) is "one term is at most the sum", with $\rho\in\mathcal W_\gamma$. (c): the zeros with $\lfloor\gamma\rfloor=n$ number at most $C_2\log(|n|+4)$ by (a) and have $1+|\gamma|\ge(1+|n|)/2$, so $\sum_\rho(1+|\gamma|)^{-2}\le\sum_n 4C_2\log(|n|+4)(1+|n|)^{-2}<\infty$. The point of (c) is the next lemma: it is what makes $\sum|a_\rho|$ finite.

### Lemma 3.3 (Gamma on the strip)

The paper states that for every $n\ge0$ there is $C$ with $|\Gamma(w)|\le C(1+|\operatorname{Im}w|)^{-n}$ on $-\tfrac12\le\operatorname{Re}w\le2$, $|\operatorname{Im}w|\ge1$. This is (G3) pushed one unit left using $\Gamma(w)=\Gamma(w+1)/w$: then $\tfrac12\le\operatorname{Re}(w+1)\le3$ and $|1/w|\le1/|\operatorname{Im}w|\le1$. It is the decay that makes $k_x$ integrable on the line $\operatorname{Re}w=-\tfrac12$ in Lemma 3.5.

### Lemma 3.4

The paper states (a) $S:=\sum_\rho|a_\rho|<\infty$ and the double series $\sum|a_\rho a_{\rho'}|$ converges to $S^2$; (b) $Z(x)=\sum_\rho a_\rho x^{-\rho}$ converges absolutely for every $x>0$, with $|Z(x)|\le Sx^{-1}$ for $0<x\le1$.

This is where the pieces meet: $a_\rho=m(\rho)\Gamma(\rho)$, so $|a_\rho|\le m(\rho)|\Gamma(\rho)|$, and for $|\gamma|\ge1$, Lemma 3.3 (with $n=3$) and Lemma 3.2(b) give $|a_\rho|\le C_2\log(|\gamma|+3)\cdot C(1+|\gamma|)^{-3}\le 2C_2C(1+|\gamma|)^{-2}$, summable by Lemma 3.2(c); the finitely many $|\gamma|<1$ add a constant. So $S<\infty$, and the double series is the product $S\cdot S$ (Primer, Absolutely convergent series). In (b), $|x^{-\rho}|=x^{-\beta}$ with $0<\beta<1$ lies between $\min(1,x^{-1})$ and $\max(1,x^{-1})$, so at most $x^{-1}$ on $(0,1]$. The finiteness of $S$ is used everywhere downstream: it is the majorant for the dominated-convergence radial limits and the convergence of $\mathcal C$.

## Section 3.3. The explicit formula

### Lemma 3.5

The paper proves: for every $x>0$, $k_x$ is integrable on the line $\operatorname{Re}w=-\tfrac12$, and $h(x)=-Z(x)+c_0+V(x)$ (equation (11)) with $c_0=\psi(0)$ and $V(x)=\int_{(-1/2)}k_x$, and $|V(x)|\le K_0x^{1/2}$.

This is Primer, The explicit formula, done with the contour stopped at $\operatorname{Re}w=-\tfrac12$. The idea: $F(x)=\int_{(2)}k_x$ by inversion (7); push the line from $\operatorname{Re}w=2$ left to $\operatorname{Re}w=-\tfrac12$ and pick up residues. The proof has four marked parts, and the guide reads each as the mechanical step it is.

- *The line $\operatorname{Re}w=-\tfrac12$.* Neither $\Gamma$ nor $\psi$ has a pole there. For $|t|\ge2$, the distance $|-\tfrac12+it-\rho|$ is at least $\beta+\tfrac12>\tfrac12$. The nearby terms in (Z3) therefore have total modulus at most twice their total multiplicity, which is $O(\log(|t|+3))$ by Lemma 3.2. Lemma 3.3 bounds $\Gamma$ by $C(1+|t|)^{-2}$. On the remaining compact segment both functions are bounded by continuity. Multiplying by $|x^{-w}|=x^{1/2}$ gives an integrable bound and $|V(x)|\le K_0x^{1/2}$.
- *Good heights.* To close the contour one needs horizontal sides where $\psi$ is not too large. For integer $n\ge2$, the ordinates in $[n-1,n+2]$ have total multiplicity $M_n\le C\log n$; choosing $T_n\in[n,n+1]$ at distance at least $\delta_n=1/(4M_n+4)$ from all of them (a measure count shows such $T_n$ exists) makes $|\psi(\sigma\pm iT_n)|\le C\log^2 n$ on $-1\le\sigma\le2$. This is the one place the local count (Z1), via Lemma 3.2, is used to find a clean height.
- *The rectangle.* On the rectangle $Q_n$ with corners $2\pm iT_n$, $-\tfrac12\pm iT_n$, the residue theorem gives a signed identity: the integral up the right side ($\operatorname{Re}w=2$) minus the integral up the left side ($\operatorname{Re}w=-\tfrac12$), plus the contribution $\mathcal H_n$ of the two horizontal sides, all with the factor $1/2\pi i$, equals the sum of the residues inside: $1/x$ at $w=1$ (where $\psi$ has residue $1$ and $x^{-1}\Gamma(1)=1/x$), $\psi(0)$ at $w=0$ (pole of $\Gamma$, residue $1$, $\psi$ analytic there since $\zeta(0)=-\tfrac12\ne0$), and $-a_\rho x^{-\rho}$ at each zero with $|\gamma|<T_n$. The horizontal contribution $\mathcal H_n\to0$ by the decay bounds.
- *The limit.* As $n\to\infty$ the right vertical integral (at $\operatorname{Re}w=2$) tends to $F(x)$ by (7), the left one (at $\operatorname{Re}w=-\tfrac12$) to $V(x)$, and the finite zero sums to $Z(x)$ by absolute convergence (Lemma 3.4(b)). This gives (11).

The paper's closing remark is the crux of the whole hypothesis-free design: *the proof crosses every zero, wherever it lies, so no hypothesis enters.* The value $c_0=\psi(0)=-\log2\pi$ is not needed for the proof and is used only in Remark 8.3.1.

## Section 3.4: Lemma 3.6 and Proposition 3.7, the regularized identity

### Lemma 3.6 (Cauchy sums)

The paper states a general fact: for countably many points $p_i$ and summable coefficients $a_i$, if a disc $D(z_0,r)$ stays at distance $\ge d$ from all but finitely many $p_i$, then $f(w)=\sum_i a_i/(w-p_i)$ is meromorphic on the disc and $(w-z_0)f(w)\to\sum_{p_i=z_0}a_i$ as $w\to z_0$.

This is the lemma that turns any of the paper's sums of simple fractions ($L$, $\mathcal C$, $\mathcal C_{\mathrm c}$) into a meromorphic function with a readable residue. The proof splits $f$ into the finite part over the near points $\mathcal E$ (a rational function with simple poles) and the tail, which converges uniformly to a holomorphic function by the Weierstrass M-test (each term bounded by $|a_i|/d$); the residue at $z_0$ collects exactly the $a_i$ with $p_i=z_0$, since any such $i$ lies in $\mathcal E$. Primer, Meromorphic functions, has the residue-limit idea.

### Proposition 3.7 (the regularized identity)

The paper defines (equation (12)) $L(s)=\sum_\rho a_\rho/(s-\rho)$, the pair sum $\mathcal C(s)=\sum_{(\rho,\rho')}a_\rho a_{\rho'}/(s-\rho-\rho')$, $M_0(s)=M(s)-2c_0L(s)/\Gamma(s)$, and $\mathcal A(s)=E_2(s)-2e_1(s-1)+\int_0^1((c_0+V)^2-2ZV)x^{s-1}\,dx$; then states (a) $L$ and $M_0$ meromorphic on $\mathbb C$, (b) $\mathcal A$ holomorphic on $\operatorname{Re}s>\tfrac12$, (c) $\Phi_2=M_0+(\mathcal C+\mathcal A)/\Gamma$ for $\operatorname{Re}s>2$ (equation (13)).

This is step (1) of the idea, made exact. The sums are over ordered pairs, a diagonal pair once. (a): $L$ is meromorphic by Lemma 3.6 with $d=1$ (on any disc, all but finitely many zeros are a unit away in imaginary part); $M$ is meromorphic since $\psi$ is and $1/\Gamma$ entire, so $M_0$ is. (b): $E_2,e_1$ are entire, and the integrand of the extra integral is bounded by $K_1x^{\operatorname{Re}s-3/2}$ on $(0,1]$ (from $|c_0+V|\le|c_0|+K_0$ and $|2ZV|\le2SK_0x^{-1/2}$, Lemmas 3.4(b) and 3.5), integrable and holomorphic for $\operatorname{Re}s>\tfrac12$ (Primer, Holomorphy of integrals). (c): on $(0,1]$, $h^2=Z^2-2c_0Z+((c_0+V)^2-2ZV)$; Fubini (justified by $\sum|a_\rho a_{\rho'}|\int_0^1x^{\sigma-3}=S^2/(\sigma-2)$) gives $\int_0^1 Z^2x^{s-1}=\mathcal C(s)$ and $\int_0^1 Zx^{s-1}=L(s)$, so $R(s)=\mathcal C-2c_0L+\mathcal A-E_2+2e_1$, and Lemma 3.1 becomes $\Gamma(s)\Phi_2=\Gamma(s)M-2c_0L+\mathcal C+\mathcal A$; divide by $\Gamma(s)\ne0$.

Read the paper's two remarks after the proof slowly, because they say what the identity adds. First, *why subtract $2c_0L$*: left in the remainder, the term $-2c_0Z(x)x^{s-1}$ is bounded near $0$ by $2|c_0|S\,x^{\operatorname{Re}s-1-B}$, since $|Z(x)|\le Sx^{-B}$ on $(0,1]$ when every zero has real part at most $B$; integrated absolutely, this bound guarantees convergence only for $\operatorname{Re}s>B$, a half-plane that contains the line only if $B<1$. That is what the bound guarantees, not where the term stops: its transform is $-2c_0L$, meromorphic on the whole plane. Pulled out as $-2c_0L$ it costs nothing, and the remainder $\mathcal A$ that is left is holomorphic on $\operatorname{Re}s>\tfrac12$ with no hypothesis. The coefficient of $\mathcal C$ is exactly $+1$. Section 9 credits the shape of the identity (a pair sum plus a holomorphic remainder) to Egami and Matsumoto, Bhowmik and Schlage-Puchta, and Cantarini, Gambini and Zaccagnini, and is explicit that what (13) adds is not a remainder reaching further left (theirs already does) but this particular normalization proved directly and used for both the continuation and the non-cancellation.

# 4. Section 4: continuation under $\mathrm H_\infty$

By (13), $\Phi_2$ continues as far as $\mathcal C$ does. This short section proves that under $\mathrm H_\infty$ the pair sum $\mathcal C$, and so $\Phi_2$, is meromorphic on $\operatorname{Re}s>1$, and computes the residue. That is Theorem A(i).

## The opening and equation (14)

The paper defines, for $s_0\in\mathbb C$, the representations $\mathcal R(s_0)=\{(\rho,\rho')\in\mathcal Z\times\mathcal Z:\rho+\rho'=s_0\}$ and the coefficient $\nu(s_0)=\sum_{(\rho,\rho')\in\mathcal R(s_0)}a_\rho a_{\rho'}$ (equation (14)), an absolutely convergent sum by Lemma 3.4(a), and notes that under RH $\nu(1+i\tau)=\mu\{\tau\}$. Section 1.4 records that without any hypothesis $\Phi_2$ continues to $\operatorname{Re}s>2B$ by a result of Bhowmik, Halupczok, Matsumoto and Suzuki, which reaches the line only when $B=\tfrac12$ and controls none of the pair sums on the line.

$\mathcal R(s_0)$ is the set of ways to write $s_0$ as an ordered sum of two zeros, and $\nu(s_0)$ is the total weight of those ways, a collision coefficient. It is defined for every $s_0$. On $\mathbb H$, Proposition 4.2(a) proves that $\mathcal C$ is meromorphic with residue $\nu(s_0)$ at each point $s_0$. The opening of Section 4 explains that $\mathcal C$ is meromorphic wherever the pair sums do not accumulate, including to the left of the line under $\mathrm H_\infty$. $\nu(s_0)$ decides whether $s_0$ is a pole of $\Phi_2$ at every point of $\mathbb H$ other than $2$ and the points $1+\rho$, where $M_0$ is analytic (Proposition 4.2(c)); the strip $1<\operatorname{Re}s<2-B$ consists of such points. On the line $\operatorname{Re}s=1$ itself, there $\nu(s_0)$ is not a Laurent residue. Under RH, $\nu(1+i\tau)=\mu\{\tau\}$, the atom that the radial limit extracts (Corollary B(iii)). Without RH the two need not match: $\nu(1+i\tau)$ sums every representation of the point $1+i\tau$, including any pairs of off-line zeros whose real parts add to $1$ (such as $\rho$ with $1-\bar\rho$), while the radial limit of the finite-off-line case extracts only the on-line part $\mu_{\mathrm c}\{\tau\}$, from $\mathcal C_{\mathrm c}$ (Lemma 6.6). Lemma 6.6 gives the radial limit for $\mathcal C_{\mathrm c}$. For a pair with $\beta+\beta'>1$, the denominator vanishes at $\eta=\beta+\beta'-1$ on the normal with $\tau=\gamma+\gamma'$. This prevents using the same termwise bound for the full pair sum, which is why Section 6.1 uses interior poles.

## Lemma 4.1 (Local finiteness)

The paper states: assume $\mathrm H_\infty$; for a compact $K\subset\mathbb H$ there are a finite set $\mathcal E$ of ordered pairs and $d>0$ with $|s-\rho-\rho'|\ge d$ for all $s\in K$ and $(\rho,\rho')\notin\mathcal E$; in particular only finitely many pairs have $\rho+\rho'\in K$.

This is the single place $\mathrm H_\infty$ enters the continuation, and the proof splits three ways. Let $e=\min_{s\in K}\operatorname{Re}s-1>0$ and $Y=\max_{s\in K}|\operatorname{Im}s|$; Lemma 2.1(b) with $\delta=e/4$ gives a height $T$ past which $\beta\le\tfrac12+e/4$. Then: if both ordinates exceed $T$, both real parts are near $\tfrac12$, so $\operatorname{Re}(s-\rho-\rho')\ge1+e-1-e/2=e/2$ (the pair sum is too far left to reach $K$); if one ordinate is low ($|\gamma|\le T$) and the other very high ($|\gamma'|>T+Y+1$), the imaginary parts separate, $|\operatorname{Im}(s-\rho-\rho')|>1$; every remaining pair has both ordinates bounded by $T+Y+1$, a finite set $\mathcal E$. Take $d=\min(e/2,1)$. So high pairs cannot crowd a compact subset of $\mathbb H$. The paper's remark after the lemma names the failure mode $\mathrm H_\infty$ rules out: if infinitely many zeros had $\beta\ge\tfrac12+\delta$, their conjugate pair sums (the real points $2\beta\ge1+2\delta$) could accumulate inside $\operatorname{Re}s>1$.

## Proposition 4.2 (Continuation and residues)

The paper states, under $\mathrm H_\infty$: (a) $\mathcal C$ is meromorphic on $\mathbb H$, with $\mathcal R(s_0)$ finite and $(s-s_0)\mathcal C(s)\to\nu(s_0)$ at every $s_0\in\mathbb H$; (b) the right side of (13) is meromorphic on $\mathbb H$ and equals $\Phi_2$ on $\operatorname{Re}s>2$, so it is the continuation of Theorem A(i); (c) if $s_0\in\mathbb H$ is neither $2$ nor one of the points $1+\rho$, then $M_0$ is analytic at $s_0$ and $(s-s_0)\Phi_2(s)\to\nu(s_0)/\Gamma(s_0)$, so $s_0$ is a simple pole whenever $\nu(s_0)\ne0$; and all of this holds at every point of the strip $1<\operatorname{Re}s<2-B$, which contains neither $2$ nor any of the points $1+\rho$.

Part (a) is Lemma 4.1 feeding Lemma 3.6 (with the ordered pairs as index set, the points $\rho+\rho'$, coefficients $a_\rho a_{\rho'}$ of total modulus $S^2$): meromorphy on every disc inside $\mathbb H$, residue $\nu(s_0)$. Part (b) just assembles: $M_0$ meromorphic on $\mathbb C$, $\mathcal A$ holomorphic on $\operatorname{Re}s>\tfrac12$, $1/\Gamma$ entire, plus (a), plus (13). Part (c) is the one to read closely, because it is the bridge from "$\nu(s_0)\ne0$" to "pole". Where can $M_0$ have poles in $\mathbb H$? The poles of $\psi(s-1)$ lie at $s=2$, at the points $s=1+\rho$, and at $s-1\in\{-2,-4,\dots\}$, which is outside $\mathbb H$; the other terms of $M$ have poles only at $s=1$ and $s=2$; and the poles of $L$ are among the zeros, with real part less than $1$. So $M_0$ is analytic at every point of $\mathbb H$ other than $2$ and the points $1+\rho$. At such a point $(s-s_0)M_0\to0$ and $(s-s_0)\mathcal A/\Gamma\to0$, leaving $(s-s_0)\mathcal C/\Gamma\to\nu(s_0)/\Gamma(s_0)$: a nonzero limit of $(s-s_0)f(s)$ means a pole of order exactly one (Primer, Meromorphic functions). Why the strip $1<\operatorname{Re}s<2-B$ is singled out: it is nonempty since $B<1$ (Lemma 2.1(a)); it lies in $\operatorname{Re}s<\tfrac32$, so it does not contain $2$; and $\operatorname{Re}(1+\rho)=1+\beta\ge2-B$, so it contains none of the points $1+\rho$. On the strip no exclusion needs checking, and that is the form Section 6 uses. The point $2B$ of Theorem C lies in the strip only when $B<\tfrac23$ (that is when $2B<2-B$), so for it the exclusions are checked by hand in Section 8.2.

The paper's closing paragraph answers "which candidates lie in $\mathbb H$?": a pair sum has real part $\beta+\beta'>1$ only if one zero has $\beta>\tfrac12$. Under RH there is none, so $\mathcal C$ is holomorphic on $\mathbb H$ and the only poles are those of $M_0$ (the points $2$ and $1+\rho$ of Corollary B(i)). Under $\mathrm H_\infty$ there may be off-line zeros, and by part (c) their pair sums $s_0$, other than $2$ and the points $1+\rho$, are poles when $\nu(s_0)\ne0$. For the points near the line that the boundary proof needs, the decision $\nu(s_0)\ne0$ is Section 5. For the real point $2B$ it is positivity, and the paper says here that the proof of Theorem C applies part (c) at $2B$ (Section 8.2).

# 5. Section 5: non-cancellation, the phase cone

This is the technical centre of the new idea. The question is whether $\nu(s_0)=\sum a_\rho a_{\rho'}$ can be zero when the sum has many terms. The answer (Theorem 5.6): no, provided $|\operatorname{Im}s_0|\le Y$, $s_0$ has at least one representation, and every representation uses two zeros whose ordinates have modulus above a threshold $X$ that depends on $B$ and $Y$. The non-emptiness matters: a point with no representation satisfies "every representation is high" vacuously and has $\nu(s_0)=0$. The strategy is to strip the zeros out first and prove a general statement about a family of "weights" (Theorem 5.4), then feed the zeros in with a $\log^2$ count. Nothing here uses $\mathrm H_\infty$ directly; it uses only a bound $B<1$ on the real parts, and the results hold for any $B\in[\tfrac12,1)$. Read Primer, Phases, and The head–tail principle, first.

## Section 5.1: the weights (equations (15)–(16), Lemmas 5.1–5.3)

The paper observes that two high zeros whose sum has bounded imaginary part have ordinates of opposite signs, so a representation of $s_0=\alpha+i\tau$ is $\rho=b+i(u+\tau)$, $\rho'=c-iu$ with $u$ large, and its weight is $m(\rho)m(\rho')$ times $w_{b,c}(\tau,u)=\Gamma(b+i(u+\tau))\Gamma(c-iu)$ (equation (15)); it defines the leading term $\Omega_{b,c}(\tau,u)=2\pi e^{-\pi u-\pi\tau/2}u^{b+c-1}\exp(i(\tau\log u+\tfrac\pi2(b-c)))$ (equation (16)).

Here $b,c$ are the real parts of the two zeros (both in $[1-B,B]$), $u$ is the modulus of the negative ordinate, and $\tau=\operatorname{Im}s_0$. The two Gamma arguments have ordinates $u+\tau$ and $-u$. Their magnitudes differ by the bounded quantity $|\tau|$. $\Omega_{b,c}$ is its Stirling approximation. Read $\Omega$: the modulus is $2\pi e^{-\pi u-\pi\tau/2}u^{b+c-1}$, decaying like $e^{-\pi u}$; the phase is $\tau\log u+\tfrac\pi2(b-c)$, a slow drift $\tau\log u$ in $u$ plus a fixed offset $\tfrac\pi2(b-c)$ that is zero when $b=c$ (in particular on the line, and also for two off-line zeros with equal real parts) and nonzero when $b\ne c$.

### Lemma 5.1 (Stirling for the weights)

The paper states that for $b,c\in[1-B,B]$, $|\tau|\le Y$, $u\ge U$, $|w_{b,c}-\Omega_{b,c}|\le(K/u)|\Omega_{b,c}|$. This is (G4) applied twice. The proof first records, for $b\in[0,1]$ and $t\ge2$, the one-variable Stirling form (equation (17)) $\Gamma(b+it)=\sqrt{2\pi}\,t^{b-1/2}e^{-\pi t/2}\exp(i(t\log t-t+\tfrac\pi2(b-\tfrac12)))(1+O(t^{-1}))$, got by substituting $\operatorname{Log}(b+it)=\log t+i\pi/2+\operatorname{Log}(1-ib/t)$ into $\mathrm{St}(z)$ of (G4) and controlling the error (the paper writes the explicit bound $|\varepsilon|\le4/t$). Then it applies (17) at $t=u+\tau$ (for $\Gamma(b+i(u+\tau))$) and at $t=u$ (for $\Gamma(c-iu)=\overline{\Gamma(c+iu)}$ by (G1)), multiplies, and collects: the modulus is $2\pi(u+\tau)^{b-1/2}u^{c-1/2}e^{-\pi u-\pi\tau/2}(1+O(1/u))$ with $(u+\tau)^{b-1/2}=u^{b-1/2}(1+O_Y(1/u))$, and the combined phase is $\tau\log u+\tfrac\pi2(b-c)+O_Y(1/u)$ (the leftover bracket $(u+\tau)\log(1+\tau/u)-\tau$ is $O_Y(1/u)$ by Taylor). That is $\Omega_{b,c}(1+O_Y(1/u))$.

The phase offset $\tfrac\pi2(b-c)$ is independent of height for fixed $b$ and $c$. Its maximum modulus over the strip is $\tfrac\pi2(2B-1)$. It vanishes for equal real parts. For zeta zeros under $\mathrm H_\infty$, both real parts tend to $\tfrac12$ as their heights grow, so the offset tends to zero, but Lemma 2.1(b) gives no rate that would put it inside the $O(1/u)$ error. Lemma 5.2 allows the full range of offsets.

### Lemma 5.2 (the phase cone)

The paper states, with $\lambda_B=\sin(\tfrac\pi2(1-B))>0$: there is $U$ such that for $b,c\in[1-B,B]$, $|\tau|\le Y$ and $U\le u_0\le u\le u_0+\sqrt{u_0}$,
$$\operatorname{Re}\bigl(e^{-i\tau\log u_0}w_{b,c}(\tau,u)\bigr)\ge\lambda_B\,|w_{b,c}(\tau,u)|.$$
In words: after rotating by the single direction $\tau\log u_0$, every weight in the window $[u_0,u_0+\sqrt{u_0}]$ has real part a fixed positive fraction of its modulus, so all of them point into one half-plane and cannot cancel.

The proof: with $\theta=\pi(1-B)\in(0,\tfrac\pi2]$, the rotated main term $e^{-i\tau\log u_0}\Omega_{b,c}$ has argument $\varphi=\tau\log(u/u_0)+\tfrac\pi2(b-c)$. The drift $|\tau\log(u/u_0)|\le Y\log(1+u_0^{-1/2})\le Yu_0^{-1/2}\le\theta/4$ once $u_0\ge(4Y/\theta)^2$, and the offset $|\tfrac\pi2(b-c)|\le\tfrac\pi2-\theta$ (since $|b-c|\le2B-1$). So $|\varphi|\le\tfrac\pi2-\tfrac34\theta$ and $\operatorname{Re}(e^{-i\tau\log u_0}\Omega)\ge\sin(\tfrac34\theta)|\Omega|$; absorbing the Stirling error $\epsilon=K/u_0$ (Lemma 5.1) brings this to $\ge\sin(\tfrac12\theta)|w|=\lambda_B|w|$ once $u_0$ is large. The two things to hold on to: the rotation is by $\tau\log u_0$, a direction fixed by $\tau$ and the lowest height, *not* by the argument of any one weight; and the cone has half-angle $\tfrac\pi2 B<\tfrac\pi2$, wide enough that two weights at opposite edges can differ in argument by nearly $\pi-2\theta$ (more than a right angle when $B>\tfrac34$) yet both still have positive real part after the common rotation.

The paper gives a worked example on the line. With the first three positive ordinates $\gamma_1<\gamma_2<\gamma_3$ and $b=c=\tfrac12$, the pair sum $\tau=\gamma_3-\gamma_2=3.9888\ldots$ is represented by $(\gamma_3,-\gamma_2)$, so $u=\gamma_2=21.022\ldots$ and the weight has modulus $2.48\ldots\cdot10^{-31}$; across the window of width $\sqrt u=4.58\ldots$ the modulus falls by $e^{-\pi\sqrt u}=5.55\ldots\cdot10^{-7}$ while the argument turns by only $0.726\ldots$ radians, against about $0.787$ predicted by the leading term (16). The paper is explicit that this illustrates the drift, not the lemma (whose threshold $U$ is not made numerical). The paper computes these values and $\mu\{0\}$ in Remark 8.3.1 in floating point with the mpmath library at 40 significant digits, using its values of the ordinates; they are numerical illustrations, not certified enclosures.

### Lemma 5.3 (Decay)

The paper states: for $b,c,b_0,c_0\in[1-B,B]$ with $b+c=b_0+c_0$, and $U\le u_0\le u$, $|w_{b,c}(\tau,u)|\le K_1(1+u-u_0)e^{-\pi(u-u_0)}|w_{b_0,c_0}(\tau,u_0)|$. This is the head–tail bound: a weight at height $u$ is smaller than the lowest by a factor that decays exponentially in $u-u_0$. The proof compares the $\Omega$-moduli (which, with $\alpha=b+c$, is $(u/u_0)^{\alpha-1}e^{-\pi(u-u_0)}$) and bounds the power $(u/u_0)^{\alpha-1}$ by $1$ (if $\alpha\le1$) or by $1+u-u_0$ (if $1<\alpha<2$), giving $K_1=3$. The condition $b+c=b_0+c_0$ is what makes the powers $u^{b+c-1}$ cancel in the ratio; the paper's remark notes all representations of one point share it, since $b+c=\operatorname{Re}s_0$.

## Section 5.2. Non-cancellation for an abstract family

### Theorem 5.4

The paper states the self-contained result: for $B\in[\tfrac12,1)$, $Y>0$, $\kappa\ge0$ there is $U$ with the property that, given $|\tau|\le Y$ and data $b,c:\iota\to[1-B,B]$, $u:\iota\to\mathbb R$, $q:\iota\to\mathbb N$, $i_0\in\iota$ satisfying (1) $b_i+c_i$ constant; (2) $U\le u_{i_0}\le u_i$ and $q_{i_0}\ge1$; (3) for every real $v$ only finitely many indices $i$ have $u_i\in[v,v+1)$ (a condition on the indices, weight zero included), and for $v\ge0$ their total weight $\sum q_i$ is at most $\kappa\log^2(v+Y+4)$; the series $\sum_i q_i w_{b_i,c_i}(\tau,u_i)$ converges absolutely and is nonzero.

This is the head–tail principle (Primer) made into a theorem, with the zeros abstracted away into an index set $\iota$ with a weight $q_i$ and a height $u_i$. The proof is the clean version of step (3) of the idea. Set $d_n=4\kappa K_1(Y+4)(n+2)^3 e^{-\pi n}$; choose $n_0$ with $\sum_{n\ge n_0}d_n\le\lambda_B/2$; take $U$ large. Partition $\iota$ into bins $I_n$ by $u_i\in[u_0+n,u_0+n+1)$. Then:

- *Convergence.* Lemma 5.3 and condition (3) bound $\sum_i q_i|w_i|$ by a convergent series in $|w_0|$.
- *Head* (within $\sqrt{u_0}$ of $u_0$). Lemma 5.2 gives $\operatorname{Re}(e^{-i\tau\log u_0}q_i w_i)\ge\lambda_B q_i|w_i|\ge0$, and the lowest term $i_0$ alone contributes $\ge\lambda_B|w_0|$ (since $q_{i_0}\ge1$).
- *Tail* (beyond $\sqrt{u_0}$). For those bins $n\ge n_0$ and $u_0<(n+1)^2$, so $\sum_{i\in I_n}q_i|w_i|\le d_n|w_0|$, and the whole tail is $\le\tfrac12\lambda_B|w_0|$.
- *Conclusion.* $\operatorname{Re}(e^{-i\tau\log u_0}\sum_i q_i w_i)\ge\lambda_B|w_0|-\tfrac12\lambda_B|w_0|>0$, so the sum is nonzero.

The real part after rotation is positive; a positive real part forces the number itself nonzero. That is the entire payoff, and it rests on two inequalities with different jobs. The lowest weight, counted at least once, supplies the positive lower bound $\lambda_B|w_0|$ on the rotated real part; every other head term adds a non-negative amount, however many there are and however large (the lowest need not be the largest term of the head). The tail alone is bounded in modulus, by half that lower bound (decay against a $\log^2$ count).

## Section 5.3: the zero side (Lemma 5.5, Theorem 5.6)

The opening of Section 5 explains why the argument selects points with only high representations. A same-sign pair $\gamma,\gamma'>0$ with $\gamma+\gamma'=\tau$ has both ordinates in $(0,\tau)$, so it is low; on the line all such pairs have nearly the same modulus $2\pi e^{-\pi\tau/2}$, and no lowest one dominates. That is why the threshold is at least $Y$, and why earlier work at the fixed points $2\rho_1$ (Bhowmik and Schlage-Puchta) and $2\gamma_1$ (Bhowmik, Ramaré and Schlage-Puchta), where the only same-sign representation is the diagonal, needed a finite check of the other pairs.

### Lemma 5.5

The paper states: for $|\operatorname{Im}s_0|\le Y$ and $v\ge0$, the pairs in $\mathcal R(s_0)$ with $\gamma'\in(-v-1,-v]$ are finitely many, with total weight $\le\kappa_0\log^2(v+Y+4)$. This supplies condition (3) of Theorem 5.4 from the zero counts: $\rho'$ lies in the window $\mathcal W_{-v-1/2}$ of multiplicity $\le C_2\log(v+\tfrac72)$ (Lemma 3.2(a)), and $\rho=s_0-\rho'$ is then determined with $|\gamma|\le Y+v+1$, so $m(\rho)\le C_2\log(v+Y+4)$ (Lemma 3.2(b)); the product gives $\kappa_0=C_2^2$.

### Theorem 5.6 (Non-cancellation)

The paper states: for $B\in[\tfrac12,1)$, $Y>0$ there is $X\ge Y$ such that for any $s_0$ with $|\operatorname{Im}s_0|\le Y$ and any non-empty $\mathcal J\subseteq\mathcal R(s_0)$ whose pairs all have $1-B\le\beta,\beta'\le B$ and $|\gamma|,|\gamma'|>X$, the sum $\sum_{\mathcal J}a_\rho a_{\rho'}\ne0$; and, under $\mathrm H_\infty$ with $B=\sup\beta$, $\nu(s_0)\ne0$ whenever $\mathcal R(s_0)$ is non-empty with all ordinates of modulus $>X$.

This is Theorem 5.4 dressed in zeros. The proof's *orientation* step is the one to follow: each pair in $\mathcal J$ has opposite-sign ordinates (two positive ones above $X\ge Y$ would sum above $2X>Y\ge|\tau|$; two negative, below $-2X$), so writing the negative one as $-u$ gives $(b,c,u)$ with $u>X$, $b+c=\operatorname{Re}s_0$, $b,c\in[1-B,B]$, and $a_\rho a_{\rho'}=q\,w_{b,c}(\tau,u)$ with $q=m(\rho)m(\rho')\ge1$. Then *the family* step applies Theorem 5.4 with $\iota=\mathcal J$: condition (1) is $b+c=\operatorname{Re}s_0$; condition (3) is Lemma 5.5 applied to the pairs and to the reversed pairs (both in $\mathcal R(s_0)$), total weight $\le2\kappa_0\log^2(v+Y+4)$, so $\kappa=2\kappa_0$; condition (2) holds because a least $u_{i_0}>X\ge U$ exists. Under $\mathrm H_\infty$, Lemma 2.1(a) gives $1-B\le\beta\le B$ for every zero, so $\mathcal J=\mathcal R(s_0)$ works and $\nu(s_0)\ne0$. The existence of $X$ depends on $B$, $Y$ and the zero-count constant. Remark 8.3.3 explains why no finite table of zeros can make it explicit.

# 6. Section 6: the natural boundary

This section proves Theorem A(ii). It splits the zeros into those off the line, $\mathcal Z_{\mathrm{off}}=\{\rho:\beta\ne\tfrac12\}$, and those on it, $\mathcal Z_{\mathrm c}=\mathcal Z\setminus\mathcal Z_{\mathrm{off}}$. By the symmetry $\rho\mapsto1-\bar\rho$, $\mathcal Z_{\mathrm{off}}$ is infinite exactly when infinitely many zeros have $\beta>\tfrac12$. The two cases need different arguments, so the section has two subsections plus two shared lemmas. The division by infinite-versus-finite off-line zeros, and the use of off-line zeros to make singularities accumulate, follow Bhowmik and Schlage-Puchta (2007).

## Lemma 6.1 (Low representations)

The paper states: for all real $X,Y$ the set $\mathcal E(X,Y)=\{s:|\operatorname{Im}s|\le Y,\ \exists(\rho,\rho')\in\mathcal R(s)\text{ with }|\gamma|\le X\text{ or }|\gamma'|\le X\}$ is finite. The proof: if a representation has one ordinate of modulus $\le X$, the other has modulus $\le|X|+|Y|$, so $s$ is a sum of two zeros from a finite set. This is the "discard the finitely many low points" lemma: in any bounded window of $\tau$, only finitely many $\tau$ have a representation using a low zero, and those are thrown away so that Theorem 5.6 applies at the rest.

## Lemma 6.2 (Line blow-up)

The paper states the criterion that turns a nonzero radial limit into a barrier: if $G$ is holomorphic on $\mathbb H$ and for every $\varepsilon>0$ there are $\tau_0\ne y$ with $|\tau_0-y|<\varepsilon$ and $c\ne0$ with $\eta G(1+i\tau_0+\eta)\to c$, then no $g$ meromorphic on any disc $D(1+iy,r)$ agrees with $G$ on the part of the disc in $\mathbb H$ outside a set with no accumulation point there.

The proof is Primer, Sets without accumulation points, plus the identity theorem. Suppose such a $g$ exists; its poles are isolated, so on a small punctured disc about $s_1=1+iy$, $g$ is analytic. Pick $\tau_0,c$ for $\varepsilon$ the radius; at $s_0=1+i\tau_0$, $g$ is analytic on a neighbourhood $N$, and $g=G$ on $N\cap\mathbb H$ off an accumulation-free set, hence everywhere there by continuity. Then $\eta G(s_0+\eta)=\eta g(s_0+\eta)\to0\cdot g(s_0)=0$, contradicting $c\ne0$. In words: a function meromorphic across the line would have to be finite (hence give limit $0$ after multiplying by $\eta$) at almost every nearby point, but the nonzero atom forces a genuine blow-up at a dense set of points. This is the finite-off-line case's engine; the infinite-off-line case blocks continuation a different way (interior poles).

## Section 6.1: infinitely many zeros off the line (Proposition 6.3, Corollary 6.4)

### Proposition 6.3 (Interior poles)

The paper states: under $\mathrm H_\infty$, if $\mathcal Z_{\mathrm{off}}$ is infinite, then for every real $y$ there are distinct $s_n\in\mathbb H$, $s_n\to1+iy$, each a simple pole of $\Phi_2$.

The construction is step (4), infinite case. Infinitely many zeros have $\beta>\tfrac12$ with $|\gamma_n|\to\infty$; take $\gamma_n\to+\infty$. Littlewood's gap theorem (Z2) at $t=\gamma_n+y$ gives a partner $\rho'_n$ with $\gamma'_n-\gamma_n\to y$; reflect by $1-\bar\rho'_n$ so $\beta'_n\ge\tfrac12$. Both ordinates go to $+\infty$, so $\mathrm H_\infty$ (Lemma 2.1(b)) sends $\beta_n,\beta'_n\to\tfrac12$, and
$$s_n=\bar\rho_n+\rho'_n=(\beta_n+\beta'_n)+i(\gamma'_n-\gamma_n)\to1+iy,\qquad\operatorname{Re}s_n>1.$$
The real parts exceed and tend to $1$, so infinitely many $s_n$ are distinct. *Every representation is high*: with $X$ from Theorem 5.6 and $\mathcal E(X,Y)$ finite (Lemma 6.1), for large $n$ the point $s_n$ avoids $\mathcal E(X,Y)$, so every pair in $\mathcal R(s_n)$ has both ordinates of modulus $>X$, and Theorem 5.6 gives $\nu(s_n)\ne0$. *Poles*: for large $n$, $1<\operatorname{Re}s_n<2-B$, so Proposition 4.2(c) makes $s_n$ a simple pole. Note the division of labour. The off-line zeros that give $s_n$ real part $>1$ come from the case assumption that $\mathcal Z_{\mathrm{off}}$ is infinite, not from $\mathrm H_\infty$, which supplies none (RH implies $\mathrm H_\infty$ and has no off-line zeros). $\mathrm H_\infty$ controls their limiting real parts: through Lemma 2.1(b) it drives $\beta_n$ and $\beta'_n$ to $\tfrac12$, so the pair sum lands near $1+iy$.

### Corollary 6.4

The paper concludes: under $\mathrm H_\infty$ with $\mathcal Z_{\mathrm{off}}$ infinite, no $g$ meromorphic on $D(1+iy,r)$ agrees with $\Phi_2$ on the part in $\mathbb H$ off an accumulation-free set. The proof: such a $g$ would, near each $s_n$, agree with $\Phi_2$ on a punctured neighbourhood (the exceptional set has no accumulation point), hence have a pole at $s_n$; then the poles of $g$ accumulate at the interior point $1+iy$ of its disc of meromorphy, impossible. This is why the infinite case does not use the radial limit: the obstruction is poles *on* the line's neighbourhood, which could sit on the normal itself.

## Section 6.2: finitely many zeros off the line (Lemmas 6.5–6.7, Theorems 6.8–6.9)

The paper splits the pair sum (equation (18)) into $\mathcal C_{\mathrm c}$ (both zeros on the line), $\mathcal C_{\mathrm{ex}}=\mathcal C-\mathcal C_{\mathrm c}$ (at least one off), and $W=M_0+(\mathcal C_{\mathrm{ex}}+\mathcal A)/\Gamma$; and defines the on-line atom $\mu_{\mathrm c}\{\tau\}=\sum_{\gamma+\gamma'=\tau,\ \rho,\rho'\in\mathcal Z_{\mathrm c}}a_\rho a_{\rho'}$.

### Lemma 6.5 (The split)

The paper states: under $\mathrm H_\infty$ with $\mathcal Z_{\mathrm{off}}$ finite, $\mathcal C_{\mathrm c}$ is holomorphic on $\mathbb H$, $\mathcal C_{\mathrm{ex}}$ meromorphic on $\mathbb C$, $W$ meromorphic on $\operatorname{Re}s>\tfrac12$, and $\Phi_2=W+\mathcal C_{\mathrm c}/\Gamma$ on $\mathbb H$. The point is that the finitely many off-line zeros can be peeled off into a function meromorphic across the line, leaving the on-line part, which behaves as under RH. $\mathcal C_{\mathrm c}$ is holomorphic on $\mathbb H$ because for $\rho,\rho'\in\mathcal Z_{\mathrm c}$ the pair sum has real part $1$, so $|s-\rho-\rho'|\ge\operatorname{Re}s-1$ gives uniform convergence on $\operatorname{Re}s\ge1+\varepsilon$. And $\mathcal C_{\mathrm{ex}}$ is a finite inclusion–exclusion over $\mathcal Z_{\mathrm{off}}$: $\mathcal C_{\mathrm{ex}}(s)=2\sum_{\rho_0\in\mathcal Z_{\mathrm{off}}}a_{\rho_0}L(s-\rho_0)-\sum_{(\rho_0,\rho_1)\in\mathcal Z_{\mathrm{off}}^2}a_{\rho_0}a_{\rho_1}/(s-\rho_0-\rho_1)$, meromorphic on $\mathbb C$ because $L$ is (Proposition 3.7).

### Lemma 6.6 (Radial limit)

The paper states $\eta\,\mathcal C_{\mathrm c}(1+i\tau+\eta)\to\mu_{\mathrm c}\{\tau\}$ for every real $\tau$. This is the radial limit that step (4) of the idea uses in the finite-off-line case, now proved: each term $a_\rho a_{\rho'}\eta/(\eta+i(\tau-\gamma-\gamma'))$ has modulus $\le|a_\rho a_{\rho'}|$ and tends to $a_\rho a_{\rho'}$ if $\gamma+\gamma'=\tau$ and to $0$ otherwise, so dominated convergence (majorant $S^2$, Lemma 3.4(a)) gives $\mu_{\mathrm c}\{\tau\}$. The paper repeats that the factor $\eta$, not a spacing hypothesis, removes every off-$\tau$ pair sum, crediting the observation to Bhowmik, Ramaré and Schlage-Puchta.

### Lemma 6.7 (High pairs in every interval)

The paper states: with $\mathcal Z_{\mathrm{off}}$ finite, for every $X$ and every interval $(a,b)$ there are $\tau\in(a,b)$ and on-line zeros $\rho,\rho'$ with $\gamma+\gamma'=\tau$ and both ordinates of modulus $>X$. This is the density input, Littlewood's gap theorem again. The window for the second ordinate is $(\gamma_1+a,\gamma_1+b)$, and $a$ may be negative, so it is not enough to put $\gamma_1$ itself high: the bottom of the window, $\gamma_1+a$, has to be high as well. With $T_{\mathrm{off}}$ above the modulus of every off-line ordinate and $T_0$ the height past which (Z2) applies as below, the proof picks $\rho_1$ with $\gamma_1>\max(T_0-a,\ X,\ X-a,\ T_{\mathrm{off}},\ T_{\mathrm{off}}-a)$. So $\gamma_1>X$, $\gamma_1>T_{\mathrm{off}}$, $\gamma_1+a\ge T_0$, $\gamma_1+a>X$ and $\gamma_1+a>T_{\mathrm{off}}$. Then (Z2) supplies $\rho_2$ with $\gamma_2\in(\gamma_1+a,\gamma_1+b)$ (the proof applies the theorem to the midpoint: with $\ell=b-a$, apply (Z2) at $t+\ell/2$, for $t$ beyond a height $T_0$ chosen so that $A/\log\log\log(t+\ell/2)<\ell/2$; then some ordinate lies strictly between $t$ and $t+\ell$); both exceed the off-line heights, so $\rho_1,\rho_2\in\mathcal Z_{\mathrm c}$, and $\tau=\gamma_2-\gamma_1=\gamma_2+(-\gamma_1)$ is a pair sum of $\rho_2$ and $\bar\rho_1$ (conjugate symmetry), with ordinates $\gamma_2>X$ and $-\gamma_1$, $\gamma_1>X$.

### Theorem 6.8 (Density of nonzero atoms)

The paper states: with $\mathcal Z_{\mathrm{off}}$ finite, every neighbourhood of every real $y$ contains a $\tau_0\ne y$ with $\mu_{\mathrm c}\{\tau_0\}\ne0$. The proof combines the pieces, in this order. Take $X$ from Theorem 5.6 with its parameter set to $\tfrac12$. First discard from the neighbourhood the finite set $E=\{\tau:1+i\tau\in\mathcal E(X,Y)\}$ (Lemma 6.1) and the points $0,y$, and pass to a subinterval $(a,b)$ that avoids them. Then Lemma 6.7 finds, inside $(a,b)$, a $\tau$ and a high on-line pair with sum $1+i\tau$. Let $\mathcal J$ be the set of representations of $1+i\tau$ by two on-line zeros. It is not empty; its zeros have real part $\tfrac12$; and since $\tau\notin E$ all its ordinates have modulus above $X$. The first statement of Theorem 5.6, the one for a non-empty subset $\mathcal J$ of the representations, then gives $\mu_{\mathrm c}\{\tau\}=\sum_{\mathcal J}a_\rho a_{\rho'}\ne0$. Two cautions. The $\tfrac12$ here is the strip parameter of Theorem 5.6, chosen because the zeros of $\mathcal J$ lie on the line; it is not $\sup\beta$, which exceeds $\tfrac12$ if any off-line zero exists. And the order cannot be reversed: finding a high pair first and then discarding the point if it lies in $E$ would prove nothing about density. This is non-cancellation and density married: a nonzero on-line atom in every neighbourhood.

### Theorem 6.9

The paper states: under $\mathrm H_\infty$ with $\mathcal Z_{\mathrm{off}}$ finite, no $g$ meromorphic on $D(1+iy,r)$ agrees with $\Phi_2$ on the part in $\mathbb H$ off an accumulation-free set. The proof reduces to Lemma 6.2: shrink to $r\le\tfrac12$ so the disc lies in $\operatorname{Re}s>\tfrac12$, where $W$ is meromorphic and $\Gamma$ analytic and zero-free; then $g_1=\Gamma(g-W)$ is meromorphic and equals $\mathcal C_{\mathrm c}$ off an accumulation-free set (Lemma 6.5), and $\mathcal C_{\mathrm c}$ meets the blow-up hypothesis at $y$ with $c=\mu_{\mathrm c}\{\tau_0\}\ne0$ (Lemma 6.6 and Theorem 6.8). Lemma 6.2 rules out $g_1$, hence $g$.

## Proof of Theorem A(i) and (ii)

The paper assembles the two cases. Part (i) is Proposition 4.2(b). For (ii), a $g$ coinciding with $\Phi_2$ where $\Phi_2$ is analytic agrees with it off a set with no accumulation point in $\mathbb H$ (the poles of $\Phi_2$ in $\mathbb H$ have none), so under $\mathrm H_\infty$ either $\mathcal Z_{\mathrm{off}}$ is infinite (Corollary 6.4) or finite (Theorem 6.9); either way no such $g$ exists. The two cases exhaust $\mathrm H_\infty$, which is the whole content of "assuming only $\mathrm H_\infty$".

# 7. Section 7: sums of more than two prime powers

This section proves Theorem A(iii) by reducing $\Phi_r$ to $\Phi_2$. The series $\Phi_r(s)=\sum_{k_1,\dots,k_r}\Lambda(k_1)\cdots\Lambda(k_r)(k_1+\cdots+k_r)^{-s}$ converges for $\operatorname{Re}s>r$. Expanding $F^r=(1/x+h)^r$, the terms with at most two factors $h$ are rewritten through $F^2$ and $F$, and give $\Phi_2$ shifted by $r-2$ times a factor with no zeros; the terms with three or more factors $h$ are the difficulty. Under RH, $h=O(x^{-b})$ for every $b>\tfrac12$, and these terms are too small to reach the line. $\mathrm H_\infty$ alone does not guarantee that bound (RH is one case of $\mathrm H_\infty$, and there it holds). The paper's reason is that a zero with $\beta>b$ contributes a term of size $x^{-\beta}$ to $h$. A single term gives no lower bound for an oscillating sum, so the step, in full, is this: if $h=O(x^{-b})$ on $(0,1]$, then $\int_0^1h(x)x^{z-1}\,dx$ is holomorphic on $\operatorname{Re}z>b$, and equation (10) then makes $\Gamma(z)\psi(z)$ analytic on $\operatorname{Re}z>b$ apart from $z=1$; but $\Gamma\psi$ has a pole at every zero, so no zero has $\beta>b$. The remedy is a cutoff: keep the finitely many large-real-part zeros exact, bound the rest. The paper also credits and comments on earlier treatments (Egami and Matsumoto's $\S6$; Bhowmik and Schlage-Puchta's circle-method reduction; Tanigawa and Zhai's $\Phi_r$ coverage, read as incomplete).

## Section 7.1: the cutoff (equations (19)–(21), Lemmas 7.1–7.2)

The paper sets (equation (19)) $\delta_*=(1-B)/2\in(0,\tfrac14]$, $\sigma_*=\tfrac12+\delta_*/3$, $\mathcal E_*=\{\rho:\beta>\sigma_*\}$ (finite by $\mathrm H_\infty$), and splits $h=h_{\mathrm{ex}}+g$ (equation (20)) with $h_{\mathrm{ex}}(x)=-\sum_{\rho\in\mathcal E_*}a_\rho x^{-\rho}$ the zeros to the right of the cutoff and $g$ the rest (a zero with $\beta$ exactly $\sigma_*$ stays in $g$).

$\sigma_*$ is a cutoff above $\tfrac12$; $\mathcal E_*$ is the finite set of zeros with real part above it. The cutoff need not lie below $B$: $\sigma_*>B$ exactly when $B<\tfrac47$ (under RH, $B=\tfrac12$ and $\sigma_*=\tfrac7{12}$), and then $\mathcal E_*$ is empty. $h_{\mathrm{ex}}$ holds those zeros as an explicit finite sum of powers (whose Mellin transforms are elementary), and $g$ is everything else, small enough to bound. The margins $\sigma_*$ and $\delta_*$ are chosen so the leftover terms land left of the line; the next lemma checks that.

### Lemma 7.1

The paper states $|h_{\mathrm{ex}}(x)|\le L_*x^{-B}$ and $|g(x)|\le K_*x^{-\sigma_*}$ on $(0,1]$. Direct: $|x^{-\rho}|=x^{-\beta}\le x^{-B}$ for the extracted zeros, and $\le x^{-\sigma_*}$ for those left in $g$ (all with $\beta\le\sigma_*$), with $|V(x)|\le K_0x^{1/2}\le K_0x^{-\sigma_*}$ and the constant $c_0$ absorbed. So $h_{\mathrm{ex}}$ carries the dangerous large powers and $g$ is controlled at $x^{-\sigma_*}$, only a little worse than $x^{-1/2}$.

### Lemma 7.2

The paper defines $E_j(z)=\int_1^\infty F^j x^{z-1}\,dx$ (entire) and (equation (21)) $G_*(z)=\Gamma(z)\psi(z)-E_1(z)-1/(z-1)+\sum_{\rho\in\mathcal E_*}a_\rho/(z-\rho)$, and states $G_*$ is meromorphic on $\mathbb C$ with $G_*(z)=\int_0^1 g\,x^{z-1}\,dx$ for $\operatorname{Re}z>1$. Since $g=F-x^{-1}-h_{\mathrm{ex}}=F-x^{-1}+\sum_{\mathcal E_*}a_\rho x^{-\rho}$, the proof starts from $\int_0^1 F x^{z-1}=\Gamma(z)\psi(z)-E_1(z)$, subtracts the main-term transform $\int_0^1 x^{-1}x^{z-1}=1/(z-1)$, and adds the weighted extracted-zero transforms $a_\rho\int_0^1 x^{-\rho}x^{z-1}=a_\rho/(z-\rho)$. The sign in (21) cancels the residue $-a_\rho$ of $\Gamma\psi$ at an extracted zero: $G_*$ is $g$'s Mellin transform made meromorphic on the whole plane.

## Section 7.2: the reduction (equations (22)–(26), Lemma 7.3, Proposition 7.4)

The paper applies the binomial theorem to $F=1/x+h$ (equation (22)): $F^r=C_r x^{2-r}F^2-r(r-2)x^{1-r}F+A_r x^{-r}+Q_r$ with $C_r=\binom r2$, $A_r=\tfrac12(r-1)(r-2)$, and $Q_r=\sum_{k=3}^r\binom rk x^{k-r}h^k$ the terms with three or more factors $h$. It checks the low-power coefficients match ($C_r-r(r-2)+A_r=1$, $2C_r-r(r-2)=r$, $C_r$), then splits $Q_r=P_r+R_r$ by the number of factors $g$ (equation (23)): $P_r$ keeps the terms with at most one $g$, $R_r$ the terms with two or more. With $h_{\mathrm{ex}}^p=\sum_{\boldsymbol\rho\in\mathcal E_*^p}a(\boldsymbol\rho)x^{-\xi(\boldsymbol\rho)}$ (ordered tuples with $\xi(\boldsymbol\rho)=\rho_1+\cdots+\rho_p$ and $a(\boldsymbol\rho)=(-a_{\rho_1})\cdots(-a_{\rho_p})$), it defines (equation (24)) $\mathcal P_r(s)$, the explicit meromorphic transform of $P_r$, and $\mathcal H_r(s)=\int_0^1 R_r x^{s-1}\,dx$.

The structure: $P_r$ is built from $h_{\mathrm{ex}}$ (finitely many explicit powers) with at most one $g$, so its transform $\mathcal P_r$ is a finite combination of elementary poles and shifted copies of $G_*$, meromorphic on $\mathbb C$; $R_r$ has at least two factors $g$, each small, so its transform is holomorphic across the line. $\xi(\boldsymbol\rho)=\rho_1+\cdots+\rho_p$ and $a(\boldsymbol\rho)=(-a_{\rho_1})\cdots(-a_{\rho_p})$ are just the bookkeeping of expanding $h_{\mathrm{ex}}^p$.

### Lemma 7.3

The paper states $\mathcal P_r$ meromorphic on $\mathbb C$ with $\mathcal P_r(s)=\int_0^1 P_r x^{s-1}$ for $\operatorname{Re}s>r$, and $\mathcal H_r$ absolutely convergent and holomorphic on $\operatorname{Re}s>r-1-\delta_*$. The $\mathcal P_r$ part is term-by-term Mellin transforms, using Lemma 7.2 for the terms carrying one $g$. The $\mathcal H_r$ part is the margin check: a term of $R_r$ with $p$ factors $h_{\mathrm{ex}}$ and $j\ge2$ factors $g$ decays on $(0,1]$ like $x^{-r+2p\delta_*+j(1-\sigma_*)}$, and the exponent $2p\delta_*+j(1-\sigma_*)$ is at least $1+\delta_*$ in both cases ($p\ge1$, or $p=0$ hence $j\ge3$), so $R_r=O(x^{-(r-1-\delta_*)})$ and its transform is holomorphic on $\operatorname{Re}s>r-1-\delta_*$. The paper's remark shows why the cutoff is needed: bounding all of $h$ by $x^{-B}$ guarantees the integrability of $x^{3-r}h^3x^{s-1}$ only for $\operatorname{Re}s>r-3+3B$, and $r-3+3B$ lies left of $r-1$ only when $B<\tfrac23$; the cutoff routes the big powers into the explicit $\mathcal P_r$ instead. The half-planes in that remark, including those for $3h_{\mathrm{ex}}g^2$ and $g^3$, are what the upper bounds guarantee, not exact abscissae of convergence: under RH, for instance, $h_{\mathrm{ex}}=0$.

### Proposition 7.4 (The reduction)

The paper states, for $r\ge3$, with $c_r(s)=C_r\Gamma(s-r+2)/\Gamma(s)=C_r\prod_{j=1}^{r-2}(s-j)^{-1}$ and $M_r$ as in equation (25), where $\widetilde E_r(s)=E_r(s)-C_rE_2(s-r+2)+r(r-2)E_1(s-r+1)$, $M_r$ is meromorphic on $\mathbb C$, and for $\operatorname{Re}s>r$ (equation (26)) $\Phi_r(s)=c_r(s)\Phi_2(s-r+2)+M_r(s)+\mathcal H_r(s)/\Gamma(s)$.

This is step (5) made exact. The proof Mellin-transforms the expansion (22): the $C_r x^{2-r}F^2$ term gives $C_r(\Gamma(w)\Phi_2(w)-E_2(w))$ with $w=s-r+2$; the $-r(r-2)x^{1-r}F$ term gives $-r(r-2)(\Gamma(z)\psi(z)-E_1(z))$ with $z=s-r+1$; the $A_r x^{-r}$ term gives $A_r/(s-r)$; and $Q_r=P_r+R_r$ gives $\mathcal P_r+\mathcal H_r$ (Lemma 7.3). Dividing by $\Gamma(s)$ and using $\Gamma(s-r+2)/\Gamma(s)=\prod_{j=1}^{r-2}(s-j)^{-1}$ (G1) gives (26). The key feature of $c_r$: it is a rational function with no zeros, and its only poles are at $1,\dots,r-2$, at distance at least $1$ from every point of the line $\operatorname{Re}s=r-1$. So near each point of that line both $c_r$ and $1/c_r$ are holomorphic, and multiplying or dividing by $c_r$ does not change whether a function extends meromorphically across the line there. The paper notes $C_r=\binom r2$ counts the ways to pick the two slots of the $r$-tuple that carry the oscillating part of $F$.

## Proof of Theorem A(iii)

The paper closes: $r=2$ is Theorem A(i) and (ii). For $r\ge3$, on $\operatorname{Re}s>r-1$ the right side of (26) is meromorphic ($\Phi_2(s-r+2)$ by Theorem A(i), $c_r$ rational, $M_r$ meromorphic on $\mathbb C$, $\mathcal H_r/\Gamma$ holomorphic past the line), and equals $\Phi_r$ on $\operatorname{Re}s>r$, so it is the continuation. For the boundary, suppose $g$ is meromorphic near $s_1=r-1+i\tau$ and agrees with $\Phi_r$ where it is analytic on the right. Subtract $M_r+\mathcal H_r/\Gamma$, divide by $c_r$, and translate the variable by $r-2$. The resulting function is meromorphic near $1+i\tau$ and agrees with $\Phi_2$ off the locally finite set of poles of $\Phi_r$ in the translated half-disc. Corollary 6.4 or Theorem 6.9 excludes this. This covers $\tau=0$, and poles of $M_r$ near $s_1$ are allowed. The paper writes: “All of the difficulty of the boundary in Theorem A(iii) lies in the case $r=2$: the proof above uses Theorem A(i) for the continuation, and the non-cancellation of Section 5 and the two cases of Section 6 only through Corollary 6.4 and Theorem 6.9.” In the setting of RH, Bhowmik and Schlage-Puchta describe this relationship by saying that the analytic behaviour of $\Phi_r$ is determined by that of $\Phi_2$.

# 8. Section 8: proofs of Corollary B and Theorem C, and remarks

Sections 8.1 and 8.2 derive Corollary B and Theorem C from the preceding machinery. Section 8.3 contains three numbered remarks.

## Section 8.1: proof of Corollary B

The paper assumes RH, notes that then every $\beta=\tfrac12$ so $\mathrm H_\infty$ holds with $B=\tfrac12$, $\mathcal Z_{\mathrm{off}}=\varnothing$, $\mathcal Z_{\mathrm c}=\mathcal Z$, $\mathcal C=\mathcal C_{\mathrm c}$ and $\mu=\mu_{\mathrm c}$. It then proves the four parts.

- *Continuation and (ii).* RH implies $\mathrm H_\infty$, so Theorem A gives both directly; what remains is the poles, residues, and the limits (iii)–(iv). Under RH every pair sum has real part $1$, so $\mathcal C$ converges uniformly on $\operatorname{Re}s\ge1+\varepsilon$ and is holomorphic on $\mathbb H$.
- *(i).* The poles of $L$ are the zeros, on $\operatorname{Re}s=\tfrac12$, so $L/\Gamma$ and $\mathcal A/\Gamma$ are holomorphic on $\operatorname{Re}s>\tfrac12$; hence on $\mathbb H$, $\Phi_2=M+H$ with $H=(\mathcal C+\mathcal A-2c_0L)/\Gamma$ holomorphic. The poles of $M$ in $\mathbb H$ are those of $\psi(s-1)$ (at $s=2$ and $s=1+\rho$) and of $1/(s-2)$. At $s=2$ the residue is $1$ (the terms $2$ and $-1$ of $(s-2)M$); at $s=1+\rho$ it is $-2m(\rho)/\rho\ne0$. Simple poles, by the order-one residue-limit criterion.
- *(iii).* For real $\tau$, along the normal $\eta\mathcal A(s)\to0$ and $\eta L(s)\to0$ ($\mathcal A,L$ analytic at $1+i\tau$), $\eta\mathcal C(s)\to\mu\{\tau\}$ (Lemma 6.6), and $1/\Gamma(s)\to1/\Gamma(1+i\tau)$; so $\eta H(s)\to\mu\{\tau\}/\Gamma(1+i\tau)$.
- *(iv).* For $r\ge3$, under RH the cutoff set $\mathcal E_*$ is empty, so $h_{\mathrm{ex}}=0$ and $\mathcal P_r=0$, and $M_r$ loses its $\mathcal P_r$ term. The residues at $s=r$ ($=1/(r-1)!$, from the coefficient identity) and $s=r-1+\rho$ ($=-r\,m(\rho)\Gamma(\rho)/\Gamma(r-1+\rho)\ne0$, using $\Gamma(1+\rho)=\rho\Gamma(\rho)$) come out by direct computation; the radial limit at $\tau\ne0$ is $c_r(r-1+i\tau)=C_r\Gamma(1+i\tau)/\Gamma(r-1+i\tau)$ times (iii)'s limit, giving $\binom r2\mu\{\tau\}/\Gamma(r-1+i\tau)$.

The residue $-2m(\rho)/\rho$ and the factor $\binom r2$ are the two numbers to carry into Corollary B. The proof is entirely a specialization of Theorem A's machinery to $B=\tfrac12$; the paper notes the Lean checks Corollary B by a separate route (a contour shift under RH), not by this specialization (Section 10).

## Section 8.2: proof of Theorem C

The paper assumes $\mathrm H_\infty$ and announces the plan. Part (i) takes three steps: $B$ is attained; every representation of $2B$ is a zero paired with its conjugate, so that $\nu(2B)>0$; and $2B$ is none of the points excluded in Proposition 4.2(c), which then gives the pole. Part (ii) follows from (i) and Corollary B(i). Besides the results already proved, the third step and part (ii) use one classical fact: $\zeta(\sigma)\ne0$ for real $0<\sigma<1$.

### Part (i), step 1: $B$ is attained

The paper takes a zero $\rho_0$ with $\beta_0\ne\tfrac12$. Of $\rho_0$ and $1-\bar\rho_0$ one has real part greater than $\tfrac12$, so $B>\tfrac12$, and $B<1$ by Lemma 2.1(a). Put $\delta=\tfrac12(B-\tfrac12)$, so that $\tfrac12+\delta<B$. By $\mathrm H_\infty$ only finitely many zeros have $\beta>\tfrac12+\delta$, and there is at least one, since $B$ is the supremum of the real parts; every other zero has $\beta\le\tfrac12+\delta<B$. So $B$ is the largest real part among finitely many zeros: it is attained, and only finitely many zeros have $\beta=B$.

This is the one place Theorem C uses $\mathrm H_\infty$ directly, and the reason something is needed follows. A supremum need not be a maximum: without a hypothesis the real parts could creep up towards $B$ without any zero reaching it, and then no pair of zeros would have sum $2B$. $\mathrm H_\infty$ cuts the candidates down to a finite set, and a finite set has a largest element. With numbers: if $B=0.7$ then $\delta=0.1$, only finitely many zeros have $\beta>0.6$, and the largest of their real parts is $0.7$.

### Part (i), step 2: the coefficient $\nu(2B)$

The paper shows that the representations of $2B$ are exactly the pairs $(\rho,\bar\rho)$ with $\beta=B$. If $\rho+\rho'=2B$ then $\beta+\beta'=2B$ and $\gamma+\gamma'=0$; since both real parts are at most $B$, the first equation forces $\beta=\beta'=B$, and then the second gives $\rho'=\bar\rho$. Conversely every zero with $\beta=B$ gives the representation $(\rho,\bar\rho)$, since $\bar\rho$ is a zero with $m(\bar\rho)=m(\rho)$. By (G1), $a_\rho a_{\bar\rho}=m(\rho)^2\Gamma(\rho)\overline{\Gamma(\rho)}=m(\rho)^2|\Gamma(\rho)|^2$, so
$$\nu(2B)=\sum_{\rho\in\mathcal Z,\ \beta=B}m(\rho)^2|\Gamma(\rho)|^2,$$
a finite sum, not empty, of positive terms. The sum runs over both $\rho$ and $\bar\rho$, so each conjugate pair $\rho\ne\bar\rho$ contributes $2m(\rho)^2|\Gamma(\rho)|^2$: the ordered pairs $(\rho,\bar\rho)$ and $(\bar\rho,\rho)$ are two representations with the same weight.

The real part fixes both real parts at $B$. The zero imaginary part forces the ordinates to be opposites. These conditions make every weight positive.

### Part (i), step 3: the pole

The paper checks the exclusions of Proposition 4.2(c). The point $2B$ lies in $\mathbb H$, since $B>\tfrac12$. It is not $2$, since $B<1$. And it is not $1+\rho$ for any zero $\rho$: that would make $\rho=2B-1$ a real zero in $(0,1)$, which (Z5) rules out. Proposition 4.2(c) then gives $(s-2B)\Phi_2(s)\to\nu(2B)/\Gamma(2B)$, which is positive because $\Gamma(2B)>0$. So $2B$ is a simple pole with this residue.

### Part (ii)

If RH fails, some zero has $\beta\ne\tfrac12$, and by (i) the point $2B\in(1,2)$ is a pole. If RH holds, Corollary B(i) leaves as possible poles in $\mathbb H$ only $2$ and the points $1+\rho$. The point $2$ is not in $(1,2)$, and a point $1+\rho$ in $(1,2)$ would make $\rho$ a real zero in $(0,1)$. So $\Phi_2$ has no pole in $(1,2)$.

Note which hypothesis each direction uses. "RH fails, so there is a pole" is part (i), which needs $\mathrm H_\infty$. "RH holds, so there is no pole" uses RH itself, through Corollary B(i). The statement is an equivalence under the standing assumption $\mathrm H_\infty$; it is not a proof of RH, and it does not say that a pole in $(1,2)$ would have to be at $2B$ only (other real pair sums are left open, as Section 1.2 says).

## Section 8.3. Remarks

### Remark 8.3.1. The radial coefficient and the real limit

Under RH, for real $\tau\ne0$, $M$ is analytic at $1+i\tau$. The factor $\eta$ removes its contribution to the limit and leaves $\mu\{\tau\}/\Gamma(1+i\tau)$. With one unordered representation by distinct ordinates, $\mu\{\tau\}$ counts both orders and agrees with Egami and Matsumoto's radial coefficient. A diagonal representation contributes one term. The earlier formula as printed also gives a factor of two in this case, which does not affect the use of its nonvanishing. At $\tau=2\gamma_1$ the diagonal term agrees with the one used by Bhowmik, Ramaré and Schlage-Puchta.

At $\tau=0$, $M$ has residue $2\psi(0)=-2\log(2\pi)$ at $s=1$. The limit for the full function is $\mu\{0\}-2\log(2\pi)$. Each zero supplies one ordered pair $(\rho,\bar\rho)$, so $\mu\{0\}=\sum_\rho m(\rho)^2|\Gamma(\rho)|^2$. The paper's floating-point sum over the first ten positive ordinates and their conjugates gives approximately $6.518\cdot10^{-19}$ and a limit about $-3.6758$.

The paper proves negativity independently of that computation. The first three terms of the series for $\cosh(\pi t)$ dominate the terms of $(\tfrac14+t^2)^2$. By (G2), $\mu\{0\}$ is at most $\pi$ times the sum of squares of $m(\rho)/(\tfrac14+\gamma^2)$. These numbers are nonnegative, so the sum of squares is at most the square of their sum $D$. Under RH, $1/\rho+1/\bar\rho=1/(\tfrac14+\gamma^2)$. Davenport's paired sum therefore gives $D=2+\gamma_{\mathrm E}-\log(4\pi)<0.05$, where $\gamma_{\mathrm E}$ is Euler's constant. Hence $\mu\{0\}<0.008$ and the full limit is less than $-3.66$.

The earlier numerical value at zero, $3.259\ldots\cdot10^{-19}$, agrees to the printed digits with one term per conjugate pair, half the value of $\mu\{0\}$. The contribution of $M$ is $-2\log(2\pi)$, which supplies all the displayed digits of $-3.6758$. The current paper relates this to $\Delta_2(x)=\sum_{n\le x}G_2(n)-x^2/2-H_2(x)$, where $H_2(x)=-2\sum_\rho x^{1+\rho}/(\rho(1+\rho))$. Partial summation gives $\Phi_2(s)/s$ as the transform of the cumulative count against $x^{-s-1}$. The main-term transform is $1/(2(s-2))$, and the transform of $H_2$ has poles only at $1+\rho$. Both are analytic at $s=1$, so only $\Phi_2(s)/s$ contributes to the real limit. The identity first holds for $\operatorname{Re}s>2$ and extends to $\operatorname{Re}s>1$, where $\Delta_2(x)=O(x\log^3x)$ gives convergence of its transform. With $\sigma=s+1$, this gives the earlier paper's constant $c_2^{\mathrm{BRS}}=\mu\{0\}-2\log(2\pi)$.

The earlier oscillation argument gives deviations from $c_2^{\mathrm{BRS}}x$. Even a deviation above that baseline by $0.4713x$ gives a negative lower bound for $\Delta_2(x)/x$. The remark also notes that partial summation contributes the factor $1/s$ at the nonzero ordinate, making the diagonal contribution about $0.0167$ in modulus. The real limit forces $\liminf \Delta_2(x)/x\le c_2^{\mathrm{BRS}}<0$, the property denoted by $\Omega_-(x)$. The cited argument leaves $\Omega_+(x)$, meaning $\limsup \Delta_2(x)/x>0$, unsettled.

### Remark 8.3.2. The circle-method kernel bound

For $T_3(\alpha)=\sum_{|n|\le x}(x-|n|)^2e^{2\pi in\alpha}$ with $x$ a large positive integer, setting $\alpha=\tfrac12$ makes the exponential $(-1)^n$. Then $T_3(\tfrac12)=x^2+2\sum_{n=1}^{x-1}(x-n)^2(-1)^n=x$. At $x=3$ this is $9+2(-4+1)=3$. The printed bound is a constant times $\min(x^3,8)$ here, and a constant cannot bound the growing value $x$. Bhowmik and Schlage-Puchta's expansion under RH gives an error holomorphic on $\operatorname{Re}s>r-\tfrac{11}{10}$. The paper leaves open whether a corrected estimate would prove that theorem. Proposition 7.4 gives an independent reduction under $\mathrm H_\infty$ using Mellin transforms. Under RH its own error $\mathcal H_r/\Gamma$ is holomorphic on $\operatorname{Re}s>r-\tfrac54$ (Section 8.1).

### Remark 8.3.3. Thresholds

The proof uses only the existence of $X$. The threshold is chosen for a given $B$ and an ordinate bound $Y$. The projection margin $\lambda_B=\cos(\tfrac\pi2B)$ decreases to zero as $B$ approaches $1$. The application of Theorem 5.4 uses the bin estimate of Lemma 5.5, whose constant comes from (Z1). The paper gives no uniform threshold as $B$ approaches $1$. The estimate applies at all heights, so a finite list of zeros cannot supply that constant.

# 9. Section 9. Earlier work

The paper compares the earlier boundary arguments with Theorem 5.6, which handles coincidences at the selected points, and Lemma 6.6, which recovers the atom regardless of how close distinct sums are.

- Egami and Matsumoto's Theorem 2.1: under RH, $\Phi_2$ continues to $\operatorname{Re}s>1$ with simple poles at $s=2$ and at $s=1+\rho$ for each non-trivial zero $\rho$. Their Conjecture 2.1 is quoted in full: $\operatorname{Re}s=1$ is the natural boundary. They proved the conjecture under RH and a hypothesis (B). Hypothesis (A) says that a nonzero sum $\gamma_1+\gamma_2$ of two ordinates has a unique unordered representation: if $\gamma_1+\gamma_2=\gamma_3+\gamma_4\ne0$ then $(\gamma_3,\gamma_4)$ is $(\gamma_1,\gamma_2)$ or $(\gamma_2,\gamma_1)$. Hypothesis (B) is quantitative: there is a constant $\alpha$ with $0<\alpha<\pi/2$ such that, whenever $\gamma_1+\gamma_2\ne0$ and $(\gamma_3,\gamma_4)$ is neither $(\gamma_1,\gamma_2)$ nor $(\gamma_2,\gamma_1)$, $|(\gamma_1+\gamma_2)-(\gamma_3+\gamma_4)|\ge\exp(-\alpha(|\gamma_1|+|\gamma_2|+|\gamma_3|+|\gamma_4|))$. The lower bound depends on the four ordinates and shrinks as they grow, so it is no fixed gap. It is positive, though, so a different pair cannot have the same nonzero sum; that is how (B) implies (A). In their proof (A) makes the residue at a candidate point a single nonzero product of Gamma values, and (B) bounds the near-coincident terms of the remaining sum.
- Bhowmik and Schlage-Puchta removed (B), proving the boundary under RH and (A) (their Conjecture 1). Their Theorem 2 (of Bhowmik and Schlage-Puchta) has four parts; the paper quotes all four. Part (1) gives, under RH, that the $\Phi_r$ boundaries are equivalent to the $\Phi_2$ boundary. Part (2) gives that under RH and (A), $\Phi_2$ has the boundary. Part (3) gives that under RH, $\Phi_2$ has a singularity at $2\rho_1$ (first zero $\rho_1=\tfrac12+14.1347\ldots i$). Part (4): under their Conjecture 2 (a form of (B)), and not RH, $\{\operatorname{Re}s>2\sigma_0\}\subseteq\mathcal D_2\subseteq\{\operatorname{Re}s>1\}$, where $\sigma_0$ is the infimum of $\sigma$ past which only finitely many zeros have $\beta>\sigma$. The paper notes that $\sigma_0=\tfrac12$ exactly under $\mathrm H_\infty$, so part (4) under $\mathrm H_\infty$ reads $\mathcal D_2=\{\operatorname{Re}s>1\}$: the same continuation and boundary as Theorem A, but still under the extra hypothesis Conjecture 2.
- Tanigawa and Zhai state a half-plane form for a class containing $\Phi_2$ and $\Phi_r$ under RH. Egami and Matsumoto called the proof incomplete, and this paper agrees. The proofs for $\Phi_2$ and $\Phi_r$ establish meromorphy on a half-plane. The corollary then uses the density of sums of poles of the factors. It leaves out the step showing that their contributions to the same sum survive cancellation. That is a gap in the cited proof. Theorem A establishes the boundary by its own argument, and the assessment bears on the claim about earlier complete proofs under RH alone.
- Peter's continuation theorem for Dirichlet series attached to polynomials (Theorem 1.3, 1998) requires each auxiliary series to have only finitely many poles in each vertical strip of finite width. For $\Phi_2$ the auxiliary series is $-\zeta'/\zeta$, which has infinitely many poles (the zeros of $\zeta$) in the strip $0<\operatorname{Re}w<1$, so the theorem does not apply; the same holds for $\Phi_r$.
- Zaharescu and Zaki prove, under RH, a natural boundary at $\operatorname{Re}s=\tfrac32$ for a related series; there the singularities come from single zeros, and a hypothesis again limits coincidences to finitely many.
- Egami and Matsumoto (2024) restate the conjecture as open. For a function-field analogue of $\Phi_2$ they prove, with no hypothesis, continuation to the whole plane when the characteristics of the two function fields are equal and a natural boundary $\operatorname{Re}s=2$ when they differ. Matsumoto's survey states the boundary of $\Phi_2$ as a consequence of RH and the linear independence conjecture. Rüppel carries both results, the continuation and the natural boundary under an analogue of (B), over to the series with $m\equiv a$, $n\equiv b\pmod q$, assuming the generalized Riemann hypothesis up to a possible exceptional zero. Cantarini, Gambini and Zaccagnini state the boundary for the Liouville analogue under RH, simple zeros and linear independence.
- The historical precedents include the prime zeta function $P(s)=\sum_p p^{-s}$. The line $\operatorname{Re}s=0$ is a natural boundary of $e^{P(s)}$ under RH (Kluyver and Landau) and of $P(s)$ without RH (Landau and Walfisz). The paper also cites the Euler products $\prod_p h(p^{-s})$ of Estermann and Dahlquist.
- Table 1 lists the hypotheses under which the boundary of $\Phi_2$ has been stated: RH and (B) (Egami and Matsumoto, Theorem 2.2); RH and (A) (Bhowmik and Schlage-Puchta, Theorem 2(2)); RH and linear independence of the ordinates (Matsumoto's survey, Theorem 5.4); $\mathrm H_\infty$ and a form of (B) for all zeros (Bhowmik and Schlage-Puchta, Theorem 2(4), proof partly by reference); RH (Tanigawa and Zhai, Corollary 1.4, half-plane form, proof read as incomplete); and $\mathrm H_\infty$ alone (Theorem A).

The paper reads Bhowmik and Schlage-Puchta's separation hypothesis for all zeros as restricted to nonzero sums, since every pair of conjugate ordinates sums to zero. On that reading it gives no pole at the real candidate $2B$. Their proof of the boundary in that setting, apart from the density argument, refers to results established under RH. For higher series, Egami and Matsumoto assumed RH, (B) and further hypotheses $(\mathrm C)_k$ for $k\le r$. At a nonzero ordinate sum with a unique unordered representation by two distinct zeros, their radial formula agrees with Corollary B(iv). In the random-sign version studied by Bhowmik and Matsumoto, the convergence line is almost surely a natural boundary and lies at or to the left of $\operatorname{Re}s=r/2$.

The paper discusses decompositions with a pair sum and a remainder, including Cantarini, Gambini and Zaccagnini's unconditional formula. Equation (13) contributes the normalization and direct proof, with the isolated pair series and a holomorphic remainder on $\operatorname{Re}s>\tfrac12$.

Section 9 places $\mathrm H_\infty$ between RH and the Lindelöf hypothesis via Backlund's criterion. A zero-density bound that grows with height cannot give a finite total count. A footnote cites unrefereed preprints asserting $B\le7/8$ (OpenAI) and a sharper bound (Liu). Such a bound leaves open whether high zeros approach the line, the property used in Lemma 4.1.

For the mean values, the paper traces estimates of $\sum_{N\le X}G_2(N)$ from Fujii's $O(X^{3/2})$ error and his explicit contribution from the poles at $1+\rho$ to Bhowmik and Schlage-Puchta and to Languasco and Zaccagnini. Under RH the last formula is
$$\sum_{N\le X}G_2(N)=\frac{X^2}{2}-2\sum_\rho\frac{X^{1+\rho}}{\rho(1+\rho)}+O(X\log^3X).$$
Bhowmik and Ruzsa show that an error $O(X^{2-\delta})$ for some $\delta>0$, relative to $X^2/2$, implies $B<1$. Granville's RH criterion uses prime-only weights and the Hardy–Littlewood main term. The earlier pole criterion from Bhowmik, Halupczok, Matsumoto and Suzuki assumes $B<1$ and detects off-line zeros through $1+\rho$. Li and Liu's preprint concerns representations of individual large even integers under the generalized Riemann hypothesis for Dirichlet $L$-functions and either of their further spectral hypotheses S and R.

# 10. Formal verification and the unnumbered AI acknowledgement

## Section 10. What is checked

The two developments prove Theorems A and C from $\mathrm H_\infty$ with their classical inputs and prove Corollary B from RH with its classical inputs. Each input in a formal signature is a proposition. The kernel checks the implication from those propositions. The developments and their libraries supply the other steps, including (Z4), (Z5), (G1)–(G3), Mellin inversion, the contour arguments and the residue theorem. The paper's two developments use Lean and Mathlib 4.34.0 and the same pinned version of PrimeNumberTheoremAnd.

Corollary D combines four ingredients in writing. The Lean and Mathlib communities' certification identifies Alpöge's theorem as Mathlib's `RiemannHypothesis`. The second ingredient is RH implying $\mathrm H_\infty$. The local build checks `Paper2.hinf_of_RH` and also `Phi2Proof.Z1_of_RH`, which gives the symmetry hypothesis from RH. The third ingredient is the unconditional classical inputs, checked by hand in the forms used here. The fourth is the two conditional Lean developments. Alpöge uses Lean and Mathlib 4.33.1, while this paper uses 4.34.0. The definition of `RiemannHypothesis` has the same source text in both versions. The version comparison was made at the source level, and the builds are separate. [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Joint certification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Sutherland's independent checks](https://math.mit.edu/~drew/grh/)

### Table 2. The formal hypotheses

The paper labels the classical inputs independently of the names in Lean.

- `Hinf` is $\mathrm H_\infty$.
- `Z1` is the symmetries of the zeros with multiplicities (the paper derives these from the functional equation; the formal development assumes them).
- `Z2` is (Z1) together with the Riemann–von Mangoldt formula $N(T)=\tfrac T{2\pi}\log\tfrac T{2\pi}-\tfrac T{2\pi}+O(\log T)$ (the asymptotic is not used by the proofs).
- `Z3` is (Z3), `ZLittlewood` is (Z2), and `StirlingStrip` is (G4).
- `ZetaNoZeroIoo` is (Z5). The development proves this premise for Theorem C.
- In the RH development, `RiemannVonMangoldt` gives the local count (Z1), `LittlewoodGap` gives (Z2), and `LogDerivZetaLocal` gives (Z3). Mathlib’s `RiemannHypothesis` is the RH premise for Corollary B and is the proposition in Theorem C(ii).

The formal `Z1` assumes zero symmetries, and `Z2` includes the full Riemann–von Mangoldt asymptotic. The written proof derives the symmetries and uses the local count alone. `Phi2HInf.phi2_hinf_natural_boundary` covers Theorem A(i)–(ii), and `Phi2HInf.phiR_hinf_natural_boundary` covers Theorem A(iii) for every $r\ge2$. The separate `_classical` forms use pointwise agreement at analytic points. This follows from the codiscrete statements because the poles in the right half-plane have no accumulation point there. The release documentation lists the intermediate results by section.

For Corollary B, the RH development's statements are `phi2_natural_boundary` (first clause B(i) with residues, second codiscrete clause B(ii)), `Phi2Proof.tendsto_eta_Hphi2` (B(iii)), and `phiR_natural_boundary`, `phiR_radial_limit` (B(iv)); hypotheses are RH (Mathlib's `RiemannHypothesis`) and (Z1)–(Z3) as `RiemannVonMangoldt`, `LittlewoodGap`, `LogDerivZetaLocal`; the radial limits need only RH, (Z1), (Z3). The RH development uses its own route (a contour shift under RH giving $h=O(x^{-b})$ for every $b>\tfrac12$), and that Section 8.1's derivation from Theorem A's machinery is *not* formalized in that form; the formal statements use the continuation from the RH contour argument. The development gets the modulus of the weights from the Gamma reflection formula and proves its own phase cone using Euler's limit formula. Appendix A lists the RH pointwise form, `phi2_natural_boundary_classical`, which is available in the release.

Theorem C has three Lean statements.

*The three statements.* All are in the $\mathrm H_\infty$ development. `Phi2HInf.phi2_hinf_pole_twoBsup` is Theorem C(i) for the continuation given by the right side of (13). It asserts $\tfrac12<B<1$, that the set of zeros with $\beta=B$ is finite and not empty, the formula $\nu(2B)=\sum_{\beta=B}m(\rho)^2|\Gamma(\rho)|^2$ and its positivity, the residue $\nu(2B)/\Gamma(2B)$ and its positivity, and the order $-1$ of the pole. `Phi2HInf.phi2_hinf_pole_twoBsup_of_continuation` gives the residue and the order for every function meromorphic on $\operatorname{Re}s>1$ that agrees with the series on $\operatorname{Re}s>2$ outside a set without accumulation point there; so the pole does not depend on which continuation one writes down. `Phi2HInf.phi2_hinf_rh_iff_no_real_pole_of_continuation` is Theorem C(ii) for every such function, with RH in Mathlib's formulation `RiemannHypothesis` and "no pole at $x$" written as a non-negative order at $x$.

*Hypotheses, and one premise.* The hypotheses of the three are `Hinf`, `Z1`, `Z2`, `Z3` and `StirlingStrip`, in the dictionary above; the first two statements, which are Theorem C(i), also assume a zero with $\beta\ne\tfrac12$. `ZLittlewood` is not among them. Each of the three also takes the premise `ZetaNoZeroIoo`, which says that $\zeta(\sigma)\ne0$ for $0<\sigma<1$. The paper calls it a premise and not a hypothesis because the development proves it, as `Phi2HInf.zetaNoZeroIoo`; the hypotheses are assumed and not proved. The signatures carry `StirlingStrip` through the continuation lemmas, and the proof of Theorem C passes it to lemmas that do not use it.

In Section 8.2 the implication of Theorem C(ii) from RH to the absence of poles in $(1,2)$ comes from Corollary B(i). The Lean development proves the implication directly.

Section 10 lists what lies outside the formal verification. It includes the proof outline and credits in Section 1, the comments after the results, and the section openers and unnumbered remarks in Sections 3 to 7. Examples include the phase illustration in Section 5 and the explanation of the cubic term in Section 7. The remarks in Section 8.3, including the bound for $\mu\{0\}$ and the comparison with the earlier oscillation argument, are outside the formal verification, as are Section 9 and the assembly of Corollary D. It records hand checks for the zero symmetries and the cited forms of (Z1), (Z3) and (G4). The formal proof of Theorem C(ii) uses the development and Mathlib to relate the zeros in the open strip to the zeros in Mathlib's statement of RH. The development proves (Z5) by a route different from the printed proof.

The paper gives about 15,700 lines in 170 files for release v1.2, with about 5,700 lines in 69 files beyond the RH-only v1.1 release. The latter contains about 10,000 lines in 101 files. It reports that neither development contains `sorry` and that the main theorems depend on `propext`, `Classical.choice` and `Quot.sound`, the three standard axioms. [Lean developments](https://github.com/lpkralv/phi2-natural-boundary)

## Acknowledgement and statement on the use of AI (unnumbered section)

The author is a computer scientist, not a mathematician; he directed an AI research agent through a sequence of questions on natural boundaries of Goldbach series over primes and prime powers, chose the direction at each step, and decided to attack the Egami–Matsumoto conjecture under RH alone. He designed the verification methodology (independent adversarial reviews, re-derivation and small-case checks of every result before it was recorded as proved, and a Lean formalization). The mathematics is largely the work of AI models (Anthropic Claude, OpenAI GPT) under his direction: the idea of Section 5, the phase alignment of opposite-sign pairs, and the reduction of Section 7. Multiple models reviewed the argument. An Anthropic Claude model drafted the manuscript, which the author edited; AI agents wrote the Lean development. The author did not write or check the Lean line by line and relies on the Lean kernel and the checks of Section 10. No human mathematician has checked the proof line by line. There is no co-reader; queries will be answered by the author with the same AI assistance. No AI system is an author, and the author takes full responsibility. The section ends by thanking Anna DeConti, formerly of Osbourn Park High School, who taught him calculus.

Read this as the paper's own account of how it was made and of what has and has not been checked by a human. It is consistent with Section 10: the Lean-checked part is the implication from hypotheses to theorem; the arguments outside the formal verification, among them the passage from Titchmarsh's statements to the forms (Z1) and (Z3), are supplied in the prose; no line-by-line human check of the whole proof is claimed.

# 11. Appendix A. The Lean statements

Appendix A prints, verbatim, the Lean definitions of the hypotheses, of the natural-boundary predicate and of the series, then the formal theorem statements (docstrings and proofs omitted). This chapter helps you read them; Primer, Enough Lean, covers the syntax. The appendix opens with a paragraph of translations, which is the dictionary to keep beside the code.

The naming conventions from that opening paragraph: all live in the namespace `GoldbachBoundaries`, with the $\mathrm H_\infty$ hypotheses in `Paper2` (except `StirlingStrip`, which with the premise `ZetaNoZeroIoo` and the $\mathrm H_\infty$ theorems is in `Phi2HInf`), the RH hypotheses in `Paper2`, and `tendsto_eta_Hphi2` in `Phi2Proof`. `I` is the imaginary unit; `Phi2` is $\Phi_2$ as a function on $\mathbb C$ and `PhiR r` is $\Phi_r$ (where the series does not converge, the Lean sum defaults to $0$, which is harmless since the statements use the series only where it converges); `HH` is $\mathbb H$, `halfPlane a` is $\{\operatorname{Re}s>a\}$, `lineOne` is $\{\operatorname{Re}s=1\}$, `lineAt a` is $\{\operatorname{Re}s=a\}$; `NontrivialZeros`, `zetaMult`, `Nzero` are $\mathcal Z$, $m(\rho)$, $N(t)$; `conj` is conjugation and `Complex.log` the principal logarithm. For the Theorem C statements the paragraph adds: `HasResidue F α c` means $(s-\alpha)F(s)\to c$; `meromorphicOrderAt F α = -1` means a simple pole at $\alpha$, and `((-1 : ℤ) : WithTop ℤ)` is that order $-1$; `Bsup` is $B$; `collisionAtom s` is $\nu(s)$ of equation (14); `Phi2cHInf` is the continuation given by the right side of (13); and the sum `∑'` over the zeros `ρ` with `(ρ : ℂ).re = Bsup` runs over the zeros with $\beta=B$.

The appendix has three blocks, in this order: the $\mathrm H_\infty$ development for Theorem A, the $\mathrm H_\infty$ development for Theorem C, and the RH development for Corollary B.

### The definitions to read

- `halfPlane`, `HH`, `lineOne` and `lineAt` name the domains and lines. `NontrivialZeros` selects zeros in the open critical strip. `zetaMult` reads the order at a zero as a natural number. `HasResidue F α c` says $(s-\alpha)F(s)\to c$ as $s$ approaches $\alpha$ through points other than $\alpha$.
- `Bsup` takes the supremum of the real parts of the zeros. `zeroCoef` is the complex weight $a_\rho$. `collisionIdx s` restricts ordered pairs to those with sum $s$ and `collisionAtom s` sums their products. Appendix A describes `Phi2cHInf` as the continuation from equation (13), and `PhiRc` as the continuation constructed in the RH development.

- `Hinf`: for every $\delta>0$ the set of zeros with $\tfrac12+\delta<\operatorname{Re}\rho$ is finite. This is $\mathrm H_\infty$ exactly.
- `Z1`: for every zero $\rho$, both $\bar\rho$ and $1-\bar\rho$ are zeros of the same multiplicity. The two symmetries, as a hypothesis.
- `Nzero`, then `Z2`: the Riemann–von Mangoldt asymptotic for $N(t)$ (the `∀ᶠ t in atTop` clause, "for all sufficiently large $t$") *and* the unit-window bound $N(t+1)-N(t)\le C_1\log(t+3)$. The second clause is the paper's (Z1); the first is the extra asymptotic the proofs do not use.
- `Z3`: the local expansion of $\zeta'/\zeta$, that the logarithmic derivative minus its nearby simple poles is $O(\log|\operatorname{Im}z|)$ on the strip. The paper's (Z3).
- `ZLittlewood` / `LittlewoodGap`: for all large $t$ some ordinate is within $a/\log\log\log t$ of $t$. The paper's (Z2).
- `StirlingStrip`: the (G4) inequality, $\|\Gamma(z)-e^{\mathrm{St}(z)}\|\le(C/|\operatorname{Im}z|)\|e^{\mathrm{St}(z)}\|$ on a strip above a height $T_0$, with $\mathrm{St}(z)$ written out as `(z-1/2)*Complex.log z - z + (1/2)*Complex.log(2π)`.
- `NoMeromorphicExtensionAt` and `IsNaturalBoundary`: the boundary predicate. `IsNaturalBoundary F U L` says that at every point of the line $L$, no function meromorphic on a disc centred there agrees with $F$ on the part of the disc in $U$ off a set with no accumulation point (`codiscreteWithin`). This is the codiscrete form of the natural boundary (Primer, Sets without accumulation points). It implies the classical form of Theorem A(ii), agreement at every point where the continuation is analytic, and the `_classical` statements of the $\mathrm H_\infty$ development record that. Appendix A lists the RH development’s pointwise form, `phi2_natural_boundary_classical`, which is available in the release.
- `Phi2`, `PhiR`: the two series, as `tsum` over pairs and over `Fin r → ℕ` tuples.
- `ZetaNoZeroIoo`: for every real $\sigma$ with $0<\sigma<1$, `riemannZeta σ ≠ 0`. This is the premise of the Theorem C statements, and Section 10 names `zetaNoZeroIoo` as the development's proof of it (`Ioo` is Mathlib's name for an open interval).

### The theorem statements to read

The appendix prints two theorem statements for Theorem A, three for Theorem C and four for Corollary B. Section 10 describes the two pointwise forms for Theorem A. Appendix A lists those and the pointwise form in the RH development. The Lean release contains all three.

- `phi2_hinf_natural_boundary`: takes `hH, hZ1, hZ2, hZ3, hL, hStir` (the six $\mathrm H_\infty$ hypotheses) and concludes a conjunction: there *exists* a meromorphic $F$ on `HH` equal to `Phi2` on `halfPlane 2` (Theorem A(i)), *and* every such $F$ (meromorphic, codiscretely equal to the series) `IsNaturalBoundary ... lineOne` (Theorem A(ii)).
- `phiR_hinf_natural_boundary`: the same for `PhiR r` on `halfPlane (r-1)` with `lineAt (r-1)`, for every `r ≥ 2` (Theorem A(iii)).
- the two RH radial limits `tendsto_eta_Hphi2` and `phiR_radial_limit`: `Tendsto (fun η => η * ...) (𝓝[>] 0) (𝓝 L)` reads "$\eta\cdot(\ldots)\to L$ as $\eta\downarrow0$", with $L=$ `pairAtom τ / Gamma (1 + τ*I)` for `Hphi2`, the subtracted function $H=\Phi_2-M$ (not $\Phi_2$ itself), for every real $\tau$ (Corollary B(iii)), and $\binom r2\mu\{\tau\}/\Gamma(r-1+i\tau)$ for the continuation `PhiRc r` of $\Phi_r$ itself, under the hypothesis `hτ : τ ≠ 0` (B(iv)); `pairAtom τ` is $\mu\{\tau\}$.
- `phi2_natural_boundary` (RH): its first clause carries the residues (`HasResidue`, `HasPhi2Residues`, `meromorphicOrderAt F α = -1` for a simple pole, residues nonzero), Corollary B(i); its second, codiscrete clause is B(ii). `phiR_natural_boundary` is the $\Phi_r$ analogue.
- `phi2_hinf_pole_twoBsup` (Theorem C(i)): takes `hH, hZ1, hZ2, hZ3, hStir`, the premise `hζ : ZetaNoZeroIoo`, and `hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2` (a zero off the line). Its conclusion is a chain of conjunctions; read them in order against the theorem. `1 / 2 < Bsup ∧ Bsup < 1` is $\tfrac12<B<1$. The two set clauses, `.Finite` and `.Nonempty`, say the zeros with $\beta=B$ are finitely many and at least one. The `collisionAtom` equation is $\nu(2B)=\sum_{\beta=B}m(\rho)^2|\Gamma(\rho)|^2$ (the right side is a real number cast to $\mathbb C$), followed by "real part positive, imaginary part zero", which is how "$\nu(2B)>0$" is said of a complex number. `HasResidue Phi2cHInf (2 * Bsup) (collisionAtom (2 * Bsup) / Gamma (2 * Bsup))` is the residue $\nu(2B)/\Gamma(2B)$, again followed by its positivity. The last two clauses are the order $-1$ and "not analytic at $2B$".
- `phi2_hinf_pole_twoBsup_of_continuation`: the same residue and order for any `F` meromorphic on `HH` with `F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2`, that is, for every meromorphic continuation of the series.
- `phi2_hinf_rh_iff_no_real_pole_of_continuation` (Theorem C(ii)): for any such `F`, `RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → 0 ≤ meromorphicOrderAt F x`. The right side reads "at every real $x$ with $1<x<2$ the order of $F$ is at least $0$", which is "no pole at $x$". There is no `hoff` here: the statement is an equivalence, not a claim about a given off-line zero.

The appendix notes which names are Mathlib's (`RiemannHypothesis`, `riemannZeta`, `AnalyticAt`, `Tendsto`, `MeromorphicOn`, `AnalyticOnNhd`, `meromorphicOrderAt`, `codiscreteWithin`, `EqOn`, `ball`, `atTop`, `Real.log`, `ArithmeticFunction.vonMangoldt`), and that `∀ᶠ t in atTop` means "for all sufficiently large $t$", `∑ᶠ` a finite sum, and `=ᶠ[codiscreteWithin S]` agreement off an accumulation-free subset of $S$.

Applying the boundary clause to the continuation of Theorem A gives the boundary for $\Phi_2$ and for $\Phi_r$. To apply the Theorem C statements, supply `zetaNoZeroIoo` for `hζ`. The two pole statements still require `hoff`, a zero off the line. Table 2 and the signatures show which classical inputs each implication uses.

# 12. A one-page map of the whole proof

The result, in one breath: assuming only that high zeros cluster near the critical line ($\mathrm H_\infty$), $\Phi_2$ continues to $\operatorname{Re}s>1$ and that line is a wall; under RH you additionally get the exact poles, residues and radial limit (Corollary B).

The five moves, and where each lives:

1. **Decompose, with no hypothesis** (Section 3). Expand $\Gamma\Phi_2$ as the Mellin transform of $F^2$, use the explicit formula $h=-Z+c_0+V$, and regularize by pulling the cross term into a meromorphic $M_0$. Result: $\Phi_2=M_0+(\mathcal C+\mathcal A)/\Gamma$, with $M_0$ meromorphic on $\mathbb C$, $\mathcal A$ holomorphic past the line, and the pair sum $\mathcal C(s)=\sum a_\rho a_{\rho'}/(s-\rho-\rho')$ carrying the obstruction to continuing across the line (the other two terms involve the zeros but extend across it). Proposition 3.7.
2. **Continue** (Section 4). Under $\mathrm H_\infty$, high zeros have real parts near $\tfrac12$, so high pairs cannot crowd a compact subset of $\operatorname{Re}s>1$ (Lemma 4.1); $\mathcal C$ is meromorphic there, residue $\nu(s_0)$ (Proposition 4.2). At a point $s_0$ of $\operatorname{Re}s>1$ other than $2$ and the points $1+\rho$, where $M_0$ is analytic, a candidate $s_0$ is a pole of $\Phi_2$ iff $\nu(s_0)\ne0$ (Proposition 4.2(c)); the strip $1<\operatorname{Re}s<2-B$ consists of such points.
3. **Don't let it cancel** (Section 5). Let $|\operatorname{Im}s_0|\le Y$, let $s_0$ have at least one representation, and let every representation use two zeros whose ordinates have modulus above the threshold $X$ of Theorem 5.6. Then they are opposite-sign pairs; Stirling gives each weight the modulus $2\pi e^{-\pi u-\pi\tau/2}u^{b+c-1}$ to leading order, with exponential factor $e^{-\pi u}$, and a phase $\tau\log u+\tfrac\pi2(b-c)$. The head, within $\sqrt{u_0}$ of the lowest height, stays in a cone of half-angle $\tfrac\pi2 B<\tfrac\pi2$ about $\tau\log u_0$ (Lemma 5.2): each head term has non-negative rotated real part, and the lowest supplies at least $\lambda_B|w_0|$. In the tail, more than $\sqrt{u_0}$ above the lowest height, Theorem 5.4 combines the individual decay from Lemma 5.3 with the count in each unit bin. The total tail modulus is at most half the lower bound from the head. So $\nu(s_0)\ne0$ (Theorems 5.4, 5.6).
4. **Two cases** (Section 6). Infinitely many off-line zeros: build interior poles accumulating at $1+iy$ (Proposition 6.3, Corollary 6.4). Finitely many: peel them off, run the radial limit and dense nonzero atoms on the on-line part, blow up along the normal (Lemmas 6.5–6.7, Theorems 6.8–6.9). Either way, no continuation across the line (Theorem A(i),(ii)).
5. **Climb to $\Phi_r$** (Section 7). Expand $F^r$, keep the finitely many large-real-part zeros exact, bound the rest: $\Phi_r=c_r\Phi_2(\cdot-r+2)+\text{(meromorphic)}+\text{(holomorphic past the line)}$, $c_r$ zero-free, so the $\Phi_r$ boundary reduces to the $\Phi_2$ boundary (Theorem A(iii)).

Under RH (Section 8.1): $B=\tfrac12$, no off-line zeros, $\mathcal C$ holomorphic on $\mathbb H$, and the poles ($2$, $1+\rho$), residues ($1$, $-2m(\rho)/\rho$) and limits come out explicitly (Corollary B).

Theorem C (Section 8.2) is moves 1 and 2 at one point. If a zero lies off the line, $\mathrm H_\infty$ makes the largest real part $B$ attained; the only pairs with sum $2B$ are $(\rho,\bar\rho)$ with $\beta=B$, with positive weights, so $\nu(2B)>0$; and $2B$ is neither $2$ nor a point $1+\rho$, because $\zeta$ has no real zero in $(0,1)$. So $2B$ is a simple pole with residue $\nu(2B)/\Gamma(2B)>0$, and under $\mathrm H_\infty$, RH holds if and only if $\Phi_2$ has no pole in $(1,2)$. Move 3 is not needed. The criterion is new only in form; the proof that $2B$ is a pole is what is new (Section 1.2).

Corollary D supplies the hypotheses of Theorem A and Corollary B in writing, starting with Alpöge's certified RH theorem. The appendix and Section 10 identify the formal implications used in that assembly.

# 13. Glossary, with first-definition locations

Locations are the paper's unless marked "guide". "Eq (n)" is the paper's displayed equation.

| Symbol | Meaning | First defined |
|---|---|---|
| $\Phi_2(s)$ | Goldbach generating Dirichlet series $\sum\Lambda(m)\Lambda(n)(m+n)^{-s}$ | Eq (1), §1.1 |
| $\Phi_r(s)$ | the $r$-fold analogue | Theorem A, §1.2; §7 |
| $G_2(N)$ | weighted count of $N=m+n$ in prime powers | Eq (1), §1.1 |
| $\Lambda$ | von Mangoldt function | §1.1 (Primer, von Mangoldt) |
| $\zeta$, $\psi=-\zeta'/\zeta$ | zeta and its negative log-derivative | §1.1; eq (3), §2 |
| RH, $\mathrm H_\infty$ | Riemann Hypothesis; for every $\delta>0$, only finitely many zeros have real part greater than $\tfrac12+\delta$ | §1.1 |
| $\mathcal Z$, $\mathcal Z_{\mathrm{off}}$, $\mathcal Z_{\mathrm c}$ | non-trivial zeros; those off the line; those on it | §1.1 and the opening of §6 |
| $\rho=\beta+i\gamma$, $m(\rho)$ | a zero, its real part, ordinate, multiplicity | §1.1 |
| $B=\sup_\rho\beta$ | supremum of real parts of zeros | §1.1; Lemma 2.1 |
| $a_\rho=m(\rho)\Gamma(\rho)$ | weight of a zero | §1.2 |
| $\mu\{\tau\}$ | atom, $\sum_{\gamma+\gamma'=\tau}a_\rho a_{\rho'}$ (ordered pairs) | Eq (2), §1.2 |
| $M(s)$, $H=\Phi_2-M$ | main term; holomorphic part (under RH) | Corollary B; eq (9), §3.1 |
| $F(x)$, $h(x)=F-1/x$, $k_x(w)$ | exponential sum; its regular part; kernel $x^{-w}\Gamma\psi$ | $F,h$ in §1.3, all three in Eq (5), §3.1 |
| $e_1$, $E_2$, $R$ | tail and remainder integrals | Eq (8), §3.1 |
| $N(t)$ | zeros with $0<\gamma\le t$, with multiplicity | Eq (3), §2 |
| $\int_{(c)}$ | $\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}$ | Eq (4), §2 |
| (Z1)–(Z5) | local count, Littlewood gap, local expansion, unbounded ordinates, no real zeros in $(0,1)$ | §2.1 |
| (G1)–(G4) | Gamma facts; reflection; strip decay; Stirling exponent $\mathrm{St}(z)$ | §2.3 |
| $\mathcal W_t$, $C_1$, $C_2$ | window of radius one, the zeros with $\lvert\gamma-t\rvert\le1$; constants of (Z1), Lemma 3.2 | (Z1) and Lemma 3.2, §3.2 |
| $Z(x)=\sum a_\rho x^{-\rho}$, $c_0=\psi(0)$, $V(x)$ | zero-sum; constant; bounded remainder | $Z$ in §1.3, all three in Eq (11), §3.3 |
| $S=\sum_\rho|a_\rho|$ | the summability constant | Lemma 3.4 |
| $L(s)$, $\mathcal C(s)$, $M_0(s)$, $\mathcal A(s)$ | single-zero sum; pair sum; meromorphic part; holomorphic remainder | first introduced in §1.3, defined together in Eq (12), §3.4 |
| $\mathcal R(s_0)$, $\nu(s_0)$ | representations of $s_0$ as a pair sum; their coefficient | Eq (14), §4 |
| $w_{b,c}(\tau,u)$, $\Omega_{b,c}(\tau,u)$ | weight of an opposite-sign pair; its Stirling leading term | Eqs (15)–(16), §5.1 |
| $\lambda_B=\sin(\tfrac\pi2(1-B))$ | cone margin | Lemma 5.2 |
| $X$, $U$ | threshold of Sections 5–6 and the abstract non-cancellation threshold used to define it | Theorem 5.6 and Theorem 5.4, respectively |
| $\mathcal E(X,Y)$ | the finite low-representation set | Lemma 6.1 |
| $\mathcal C_{\mathrm c}$, $\mathcal C_{\mathrm{ex}}$, $W$, $\mu_{\mathrm c}\{\tau\}$ | on-line pair sum; off-line part; $M_0+(\mathcal C_{\mathrm{ex}}+\mathcal A)/\Gamma$; on-line atom | Eq (18) and following text, §6.2 |
| $\sigma_*$, $\delta_*$, $\mathcal E_*$ | cutoff parameters and the extracted zero set | Eq (19), §7.1 |
| $h_{\mathrm{ex}}$, $g$, $G_*$ | extracted part of $h$; the rest; $g$'s meromorphic transform | Eqs (20)–(21), §7.1 |
| $C_r=\binom r2$, $A_r$, $Q_r$, $P_r$, $R_r$ | binomial coefficients and the $h$-heavy remainders | Eqs (22)–(23), §7.2 |
| $\mathcal P_r$, $\mathcal H_r$, $c_r(s)$, $\widetilde E_r(s)$, $M_r(s)$ | explicit transform, holomorphic remainder, reduction factor, combination of entire tails, meromorphic part | Eqs (24)–(25), §7.2 |
| $\{2\}\cup\{1+\rho\}$ | the RH pole set for $\Phi_2$ | Corollary B(i), §1.2 |
| $2B$, $\nu(2B)$ | the real point of Theorem C; its coefficient $\sum_{\beta=B}m(\rho)^2\lvert\Gamma(\rho)\rvert^2$ | Theorem C, §1.2; §8.2 |
| Table 1 | hypotheses under which the boundary of $\Phi_2$ has been stated | §9 |
| Table 2 | correspondence between classical inputs and formal hypotheses | §10 |
