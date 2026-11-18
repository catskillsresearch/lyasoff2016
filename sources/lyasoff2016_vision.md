---
source_pdf: lyasoff2016.pdf
ocr_method: cursor-vision-triple-merge
verification_status: draft
---

# Transcription (LLM vision OCR)


<!-- page 1 -->

Finance Stoch (2016) 20:1061–1096  
DOI 10.1007/s00780-016-0307-1

# Another look at the integral of exponential Brownian motion and the pricing of Asian options

**Andrew Lyasoff**$^1$

Received: 19 February 2015 / Accepted: 8 April 2016 / Published online: 15 July 2016  
© Springer-Verlag Berlin Heidelberg 2016

**Abstract** It is shown that Marc Yor’s formula (Adv. Appl. Probab. 24:509–531, 1992) for the density of the integral of exponential Brownian motion taken over a finite time interval is an extremal member of a family of previously unknown integral formulae for the same density. The derivation is independent from the one by Yor and obtained from a simple time-reversibility feature, in conjunction with a Fokker–Planck type argument. Similar arguments lead to an independent derivation of Dufresne’s result (Scand. Actuar. J. 90:39–79, 1990) for the law of the integral taken over an infinite time interval. The numerical aspects of the new formulae are developed, with concrete applications to Asian options.

**Keywords** Exponential Brownian motion · Random environment · Asian options

**Mathematics Subject Classification (2010)** 60J65 · 60J60

**JEL Classification** C63 · C65 · G13

## 1 Introduction

The present paper is a follow-up to Marc Yor’s discovery [33] of an integral formula for the density of the distribution of the integral of exponential Brownian motion taken over a finite time interval: with $\sigma = 2$, one has

$$
\begin{aligned}
\phi_{t,\sigma}(x,y) &:= \frac{1}{\mathrm{d}x\,\mathrm{d}y}\,\mathbb{P}\!\left[\int_0^t e^{\sigma W_s}\,\mathrm{d}s \in \mathrm{d}x,\, W_t \in \mathrm{d}y\right] \\
&= \frac{1}{x}\,e^{-\frac{1}{2x}(1+e^{2y})}\,\theta\!\left(\frac{e^y}{x},\,t\right),
\end{aligned}
\tag{1.1}
$$

---

✉ A. Lyasoff · alyasoff@bu.edu

$^1$ Questrom School of Business, Boston University, Boston, MA, United States

<!-- page 2 -->

where
$$
\theta(r,t)=\frac{r}{\sqrt{2\pi^3 t}}\,e^{\frac{\pi^2}{2t}}\int_0^\infty e^{-\frac{u^2}{2t}}\,e^{-r\cosh u}\,\sinh u\,\sin\frac{\pi u}{t}\,\mathrm{d}u.
$$

One immediate application of such a formula is the computation of expected values of the form
$$
\mathbb{E}\left[f\left(\int_0^t e^{\sigma W_s+\nu s}\,\mathrm{d}s\right)\right],
$$
for some choice of the parameters $\sigma,\nu\in\mathbb{R}$, $0<t\le\infty$, and the Borel function $f:\mathbb{R}_+\to\mathbb{R}$. With $f(x)=(x-K)^+$ for some fixed $K>0$, such expected values can be linked to the price of so-called average or Asian call options. Another reason for studying the distribution of the integral of exponential Brownian motion is the seemingly unrelated domain of disordered systems and diffusions in random environment (see [7] for a detailed discussion and references).

To gain some insight into the nature of Yor’s formula (1.1), notice that with $\sigma=2$ and $\nu=0$, the price of the Asian call can be linked to the multiple integral
$$
\frac{e^{\frac{\pi^2}{2t}}}{\sqrt{2\pi^3 t}}
$$
$$
\times\int_0^\infty \mathrm{d}x\,\frac{(x-K)^+}{x^2}\int_{-\infty}^\infty \mathrm{d}y\,e^{y-\frac{1}{2x}(1+e^{2y})}\int_0^\infty e^{-\frac{u^2}{2t}-\frac{e^y\cosh u}{x}}\sinh u\,\sin\frac{\pi u}{t}\,\mathrm{d}u.
$$

Unfortunately, some computational issues related to the oscillatory nature of the integrand aside, the above expression exists as an iterated integral (in that order of integration), but *not* as a triple integral over the domain $\mathbb{R}_{++}\times\mathbb{R}\times\mathbb{R}_{++}$. The reason is that for $K\ge 0$,
$$
\int_K^\infty \frac{1}{x}\,e^{-\frac{e^y\cosh u+(1+e^{2y})/2}{x}}\,\mathrm{d}x=-\operatorname{Ei}(0)+\operatorname{Ei}\left(-\frac{1}{K}\left(e^y\cosh u+(1+e^{2y})/2\right)\right)
$$
$$
=\infty,
$$
which shows that the order of integration is crucial (Fubini’s theorem does not hold). This limits significantly the applicability of (1.1). It is important to understand the intrinsic reason why the above triple integral fails to exist: the point is that (1.1) is essentially an integral (convolution) of probability densities of the form
$$
\mathbb{R}_{++}\ni x\mapsto \frac{a^{p-1}}{\Gamma(p-1)}\,\frac{1}{x^p}\,e^{-\frac{a}{x}},\qquad a>0,\tag{1.2}
$$
with $p=2$, and with that particular choice for $p$, these densities do not have finite first moments.

The main objective of the present paper is to derive integral representations that are analogous to (1.1), but can be expressed as convolutions of densities of the form (1.2) with $p\ge 3$; in fact, one would need at least $p=4$ in order to ensure that the triple integral representing the unconditional first moment exists, and not just as an

<!-- page 3 -->

iterated integral. We emphasize that this task cannot revolve around exploring various integral re-interpretations of Yor’s formula. This is because Yor’s formula (see [33, (6.c)]) is obtained from some rather special features of Bessel processes and confluent hypergeometric functions, the generalization of which, if possible at all, is difficult to establish. In what follows, we develop a new method for deriving integral representations for the density in (1.1) (including the representation on the right side of (1.1)) which is independent from Yor’s method and rests on the following elementary time-reversibility-in-law property of generic integral functionals of Brownian motion: For measurable functions $V_i : \mathbb{R}_+ \times \mathbb{R} \to \mathbb{R}$, $1 \le i \le n$, chosen so that the integrals below exist a.s., one has the identity in law

$$
\left( \int_0^t V_1(s, W_s)\,\mathrm{d}s, \ldots, \int_0^t V_n(s, W_s)\,\mathrm{d}s, W_t \right)
$$
$$
\stackrel{\mathrm{law}}{=} \left( \int_0^t V_1(t-s, W_t - W_s)\,\mathrm{d}s, \ldots, \int_0^t V_n(t-s, W_t - W_s)\,\mathrm{d}s, W_t \right). \tag{1.3}
$$

The above identity—usually stated with $n = 1$ and $V_1(s, W_s) = \exp(\sigma W_s)$—has been used in a number of contexts (see Alili et al. [1], Bertoin and Yor [3], Carmona et al. [4], Linetsky [19]), and its proof is completely elementary. Indeed, setting $B_s^t := W_t - W_{t-s}$, $s \in [0,t]$, and changing the integration variable in the last $n$ integrals from $s$ to $t-s$, the right side of (1.3) can be written as

$$
\left( \int_0^t V_1(s, B_s^t)\,\mathrm{d}s, \ldots, \int_0^t V_n(s, B_s^t)\,\mathrm{d}s, B_t^t \right)
$$
$$
\stackrel{\mathrm{law}}{=} \left( \int_0^t V_1(s, W_s)\,\mathrm{d}s, \ldots, \int_0^t V_n(s, W_s)\,\mathrm{d}s, W_t \right).
$$

Nevertheless, as we are about to see, (1.3) encodes all the features needed to develop integral representations for the density, including the one due to Yor.

The outline of the method is then the following. Starting from (1.3) and using a Fokker–Planck type argument, we derive a second order PDE for the joint density $\phi_{t,\sigma}(x,y)$ in the variables $x$ and $y$, for fixed $t$. The idea behind this derivation is simple: each side of (1.3) has its own infinitesimal generator, and as the density of both sides is the same, the actions of the adjoint infinitesimal generators on this density must yield the same result (for fixed $t$).$^1$ The derivation of this PDE is the objective of Sect. 3 below (see (3.6b)). As an aside, and completely unintentionally, this derivation yields yet another proof of the striking identity of Donati-Martin et al. [8, (1.1)] (see (4.4) below). Somewhat surprisingly, the second order PDE reduces to a first order PDE, the integral lines of which foliate the domain $\mathbb{R}_{++}\times\mathbb{R}$ into 1-manifolds and can be computed in closed form. The information encrypted in those integral lines plays in our analysis the same role as the connection between Bessel processes

$^1$The most common use of (1.3) has been to identify the integral component(s) on the right side as diffusion(s) (in $t$) and rely on diffusion theory for the study of the distribution of the associated component(s) on the left side. In contrast, the time dynamics play no role in the present study, except for the fact that an infinitesimal generator for either side exists.

<!-- page 4 -->

of index $\nu$ and the exponential Brownian motion of index $\nu$ (due to Lamperti’s representation) plays in Yor’s derivation of (1.1). Using the properties of the first order PDE, we derive in Sect. 4 a closed-form expression for the Laplace transform of the conditional law of $\bigl(\int_0^t e^{\sigma W_s}\,\mathrm{d}s\bigr)^{-1}$ given $W_t$. In Sect. 5, we use this Laplace transform to develop a family of integral representations for $\phi_{t,\sigma}(x,y)$. The essence of this step is to seek expressions for $\phi_{t,\sigma}(x,y)$ in the form of contour integrals, i.e., expressions written as

$$
\phi_{t,\sigma}(x,y) = \frac{1}{x^p}\oint_\gamma e^{-z/x}\,f_{t,p}(y,z)\,\mathrm{d}z, \quad x \in \mathbb{R},
$$

for various choices of the integer $p \ge 2$, of the contour $\gamma$ and of the function $(y,z) \mapsto f_{t,p}(y,z)$ that comply with the Laplace transform. To be precise, writing the Laplace transform in terms of the above expression leads to an equation for $\gamma$ and $f_{t,p}(y,z)$. This is simply our special way of inverting the Laplace transform. We are going to see that the choices for such representations are many, and one of those choices is precisely (1.1). One interesting (and useful) aspect of our method is the possibility to obtain integral representations with $p = 3$ and $p = 4$, as discussed above. Moreover, by choosing the contour $\gamma$ accordingly, we obtain integral representations with less problematic oscillations and substantially easier to evaluate numerically, even in the case $p = 2$. Finally, we discuss in Sect. 6 concrete applications to Asian options, which are illustrated with concrete numerical examples. The accuracy with which the exact formulae that we obtain can be evaluated depends mostly on how far one can push the working precision in the computing system—especially for smaller volatilities and shorter time intervals. In addition, most of the formulae that we obtain rely on computer algebra. Fortunately, a computing system with which one can accomplish such tasks is available and in the public domain. All the computing that the present paper refers to is done on a Surface tablet running ‘Linux’ OS (as a virtual machine), with the Sage computing system and the mpmath (mp) library (within Sage) for higher precision arithmetic.

For a detailed review of the topic “integral functionals of Brownian motion” and for a comprehensive bibliography, we refer the reader to the survey papers of Matsumoto and Yor [22, 23] and also to the collection of papers by Yor [35]. The present paper is self-contained and does not rely on previously known results, except for the time-reversibility property (1.3) and the auxiliary results included in the next section. Aside from the short proof of Dufresne’s result [11] about the integral taken over an infinite time period, which is included at the beginning of Sect. 3, it is not in the paper’s objectives to develop alternative derivations of previously known results. Not counting Yor’s original result [33], which we are going to obtain as a special case of more general integral formulae, the only other known result that crops up in our study—accidentally, and seemingly out of nowhere—is the striking identity in (4.4).

## 2 Some auxiliary results

A truly pedantic approach to the study of the distributions of the integrals

$$
\int_0^t e^{\sigma W_s}\,\mathrm{d}s,\quad t > 0,\quad \text{and}\quad \int_0^\infty e^{\sigma W_s - \nu s}\,\mathrm{d}s,\quad \sigma,\nu > 0, \tag{2.1}
$$

<!-- page 5 -->

Another look at the integral of exponential Brownian motion

would require a formal proof that infinitely smooth densities exist, before the task of calculating those densities can be undertaken. There are various ways in which such issues can be addressed. Perhaps the most elementary approach, which does not involve advanced tools from diffusion theory or Malliavin calculus, is to replace $(W_s, 0 \le s \le t)$ with $\bigl(\alpha_s + \frac{s}{t}\xi,\, 0 \le s \le t\bigr)$, where $(\alpha_s, 0 \le s \le t)$ is a pinned Brownian motion, pinned at $\alpha_0 = \alpha_t = 0$, and $\xi \sim \mathcal{N}(0,t)$ is a Gaussian random variable with $\mathbb{E}[\xi]=0$ and $\mathbb{E}[\xi^2]=t$ which is independent from $(\alpha_s)$. If we fix the sample path $[0,t] \ni s \mapsto \alpha_s$, then the first integral in (2.1) becomes a strictly monotone function of $\xi$ and the existence of an infinitely smooth density can be established with the standard tools from analysis. The existence of a smooth density for the second integral can be obtained in a similar fashion. Given our main objectives, we prefer not to be sidetracked into formal proofs of such features and only state (without proof, except for the elementary lemma below) the properties that we are going to need later on.

**Lemma 2.1.** *We have for any $p \in \mathbb{N}_0 := \{0, 1, 2, \dots\}$ that*
$$
\mathbb{E}\left[\left(\int_0^t e^{\sigma W_s}\,ds\right)^{\pm p}\right] < \infty.
$$

*Proof.* There are well-known exact formulae for the above moments (see [9] and [10], for example), but establishing just the finiteness of the moments, as stated here, is completely elementary; one only has to notice that
$$
\int_0^t e^{\sigma W_s}\,ds \le t\,e^{\sigma \sup_{0 \le s \le t}|W_s|} \stackrel{\text{law}}{=} t\,e^{\sigma|W_t|}
$$
and that
$$
\left(\int_0^t e^{\sigma W_s}\,ds\right)^{-1} \stackrel{\text{law}}{=} \left(\int_0^t e^{-\sigma W_s}\,ds\right)^{-1} \le \frac{1}{t}\,e^{\sigma \sup_{0 \le s \le t}|W_s|} \stackrel{\text{law}}{=} \frac{1}{t}\,e^{\sigma|W_t|}.
$$
$\square$

**Proposition 2.2.** *Given any $t>0$, $\sigma>0$ and $\nu<0$, the densities*
$$
\phi_{t,\sigma}(x \mid y) := \frac{1}{dx}\,\mathbb{P}\left[\int_0^t e^{\sigma W_s}\,ds \in dx \,\middle|\, W_t = y\right], \qquad x>0,\; -\infty < y < \infty,
$$
$$
\phi_{t,\sigma}(x,y) := \frac{1}{dx\,dy}\,\mathbb{P}\left[\int_0^t e^{\sigma W_s}\,ds \in dx,\; W_t \in dy\right]
$$
$$
= \frac{1}{\sqrt{2\pi t}}\,e^{-\frac{1}{2t}y^2}\,\phi_{t,\sigma}(x \mid y), \qquad x>0,\; -\infty < y < \infty,
$$
$$
\psi_{\sigma,\nu}(x) := \frac{1}{dx}\,\mathbb{P}\left[\int_0^\infty e^{\sigma W_s + \nu s}\,ds \in dx\right], \qquad x>0,
$$
*have the following properties:*

<!-- page 6 -->

**(a)** All functions $(x,y) \mapsto \phi_{t,\sigma}(x,y)$, $(x,y) \mapsto \phi_{t,\sigma}(x \mid y)$, and $x \mapsto \psi_{\sigma,\nu}(x)$ are infinitely smooth in all variables.

**(b)** $\lim_{x \searrow 0} \psi_{\sigma,\nu}(x) = 0$, $\lim_{x \nearrow \infty} \frac{\partial^n}{\partial x^n}\psi_{\sigma,\nu}(x) = 0$, and $\lim_{x \searrow 0} \frac{\partial^n}{\partial x^n}\psi_{\sigma,\nu}(x)$ exists for every $n \geq 0$.

**(c)** $\lim_{x \searrow 0} \phi_{t,\sigma}(x \mid y) = 0$, $\lim_{x \nearrow \infty} \frac{\partial^{m+n}}{\partial x^m \partial y^n}\phi_{t,\sigma}(x \mid y) = 0$, and
$$
\lim_{x \searrow 0} \frac{\partial^{m+n}}{\partial x^m \partial y^n}\phi_{t,\sigma}(x \mid y)
$$
exists for every $m,n \geq 0$.

**(d)** For any $m,n,p \in \mathbb{N}$, we have
$$
\int_{-\infty}^{\infty} \mathrm{d}y\, e^{-\frac{y^2}{2t}} \int_0^{\infty} x^{\pm p} \left| \frac{\partial^{m+n}}{\partial x^m \partial y^n}\phi_{t,\sigma}(x \mid y) \right| \mathrm{d}x < \infty.
$$

In particular, the function
$$
\mathbb{R} \ni y \mapsto \mathbb{E}\left[\left(\int_0^t e^{\sigma W_s}\,\mathrm{d}s\right)^{\pm p} \,\Big|\, W_t = y\right] = \int_0^{\infty} x^{\pm p} \phi_{t,\sigma}(x \mid y)\,\mathrm{d}x
$$
is infinitely smooth and one has
$$
\frac{\partial^n}{\partial y^n}\mathbb{E}\left[\left(\int_0^t e^{\sigma W_s}\,\mathrm{d}s\right)^{\pm p} \,\Big|\, W_t = y\right] = \int_0^{\infty} x^{\pm p} \frac{\partial^n}{\partial y^n}\phi_{t,\sigma}(x \mid y)\,\mathrm{d}x.
$$

With the scaling property of Brownian motion in mind, the following relations are easy to verify:
$$
\phi_{t,1}(x,y) = \frac{1}{\sigma^3}\,\phi_{\frac{t}{\sigma^2},\sigma}\!\left(\frac{x}{\sigma^2}, \frac{y}{\sigma}\right), \qquad \phi_{t,1}(x \mid y) = \frac{1}{\sigma^2}\,\phi_{\frac{t}{\sigma^2},\sigma}\!\left(\frac{x}{\sigma^2} \,\Big|\, \frac{y}{\sigma}\right),
$$
$$
\psi_{1,\nu}(x) = \frac{1}{\sigma^2}\,\psi_{\sigma,\nu\sigma^2}\!\left(\frac{x}{\sigma^2}\right).
$$

At the same time, a straightforward application of the Cameron–Martin–Girsanov theorem implies that the joint density of
$$
\left(\int_0^t e^{\sigma W_s + \mu s}\,\mathrm{d}s,\, W_t\right), \qquad \sigma > 0,\; -\infty < \mu < \infty,
$$
which we denote by $\phi_{t,\sigma,\mu}(x,y)$, $x > 0$, $-\infty < y < \infty$, can be connected with the density $\phi_{t,\sigma}(x,y) = \phi_{t,\sigma,0}(x,y)$ through the formula
$$
\phi_{t,\sigma,\mu}(x,y) = e^{\frac{\mu}{\sigma}y + \frac{1}{2}\frac{\mu^2}{\sigma^2}t}\,\phi_{t,\sigma,0}\!\left(x,\, y + \frac{\mu}{\sigma}t\right). \tag{2.2}
$$

<!-- page 7 -->

## 3 Fokker–Planck type characterization of the law of the integral taken over finite and infinite time intervals

As noted in the introduction, the tools developed in the present paper rest in a crucial way on the time-reversibility relation (1.3), which leads to a Fokker–Planck type equation for the integral taken at a finite time. Applying the Fokker–Planck argument to the law of the integral taken over an infinite time period is somewhat simpler, and obtains from a particular application of what is known as the “random affine equation” (see Bertoin and Yor [3, (17)]): If $W$ and $B$ are two independent Brownian motions, then for every choice of $\sigma > 0$ and $\nu < 0$, we have $\int_0^\infty e^{\sigma(W_s+\nu s)}\,ds < \infty$ a.s.,$^2$ and as a result, the following process is well defined:
$$
Z_t := e^{\sigma(\nu t - B_t)} \left( \int_0^\infty e^{\sigma(\nu s + W_s)}\,ds + \int_0^t e^{\sigma(-\nu s + B_s)}\,ds \right), \quad t \ge 0. \tag{3.1}
$$

This process is a stationary Markov process for the filtration $(\mathcal{F}_t)_{t \ge 0}$ defined by $\mathcal{F}_t := \sigma(W_u, B_v : u \in \mathbb{R}_+, v \in [0,t])$, with $Z_t \stackrel{\text{law}}{=} \int_0^\infty e^{\sigma(W_s+\nu s)}\,ds$ for any $t \ge 0$, and its infinitesimal generator is given by
$$
\mathcal{L} := \frac{1}{2}\sigma^2 x^2 \frac{\partial^2}{\partial x^2} + \left( 1 + \left( \nu\sigma + \frac{\sigma^2}{2} \right) x \right) \frac{\partial}{\partial x}. \tag{3.2}
$$

Consequently, the density $\psi_{\sigma,\nu}(x)$, which is also the density of the random variable $Z_t$ for any fixed $t \in \mathbb{R}_+$, must solve the Fokker–Planck equation
$$
\frac{\partial}{\partial x} \left( \frac{\sigma^2}{2} \frac{\partial}{\partial x}\bigl(x^2 \psi_{\sigma,\nu}(x)\bigr) - \left( 1 + \left( \nu\sigma + \frac{\sigma^2}{2} \right) x \right) \psi_{\sigma,\nu}(x) \right) = 0.
$$

A straightforward integration of this equation gives
$$
\psi_{\sigma,\nu}(x) = e^{-\frac{2}{x\sigma^2}} x^{\frac{2\nu}{\sigma}-1} \left( \frac{2c_1}{\sigma^2} \int_{x_0}^{x} e^{\frac{2}{u\sigma^2}} u^{-\frac{2\nu}{\sigma}-1}\,du + c_2 \right), \quad x > 0,
$$
for some $x_0 > 0$ and free constants $c_1$ and $c_2$. Since $e^{\frac{2}{u\sigma^2} - \frac{2}{x\sigma^2}} \ge 1$ for $u \le x$ and the function
$$
x \mapsto x^{\frac{2\nu}{\sigma}-1} \int_{x_0}^{x} u^{-\frac{2\nu}{\sigma}-1}\,du = \frac{\sigma}{2\nu} x^{\frac{2\nu}{\sigma}-1} \left( x_0^{-\frac{2\nu}{\sigma}} - x^{-\frac{2\nu}{\sigma}} \right)
$$
is not integrable at $\infty$, while the function $x \mapsto e^{-\frac{2}{x\sigma^2}} x^{\frac{2\nu}{\sigma}-1}$ obviously is ($\nu < 0$), we must have $c_1 = 0$. The constant $c_2$ is then determined from the normalization and we

---

$^2$ In Dufresne [11, Proposition 4.4.4], this property is established as a consequence from the arcsine law. Alternatively, it can be seen as a direct application of the law of the iterated logarithm, since $\int_0^\infty e^{\sigma((1+\varepsilon)\sqrt{2s\log(\log s)}+\nu s)}\,ds < \infty$ for every choice of $\sigma$, $\varepsilon > 0$ and $\nu < 0$.

<!-- page 8 -->

arrive at the formula

$$
\psi_{\sigma,\nu}(x) = \frac{\sigma^{\frac{4\nu}{\sigma}}}{4^{\nu/\sigma}\,\Gamma\!\left(-\frac{2\nu}{\sigma}\right)}\,e^{-\frac{2}{x\sigma^2}}\,x^{\frac{2\nu}{\sigma}-1}, \qquad x \in \mathbb{R}_{++},\; \nu < 0,\; \sigma > 0. \tag{3.3}
$$

Several comments are now in order.

*Remark 3.1* The above formula can be traced back to Pollak and Siegmund [25, Proposition 3], where it is established in the special case $\nu = -\frac{1}{2}\sigma$. In its present form, it was first derived by Dufresne [11] by using an entirely different method. Since then, a number of other derivations have emerged: Yor [34], Bertoin and Yor [3, (16)], Matsumoto and Yor [22, p. 334], Baudoin and O'Connell [2, (6)], etc. Except for [2], which relies on the features of the Laplace transform of the integral, the consensus strategy appears to be to derive the law of the integral over infinite time as the limit of the law of the integral over finite time,[^3] which in turn can be identified in law with a diffusion process that has the same dynamics as the process $Z$ (one can write the same SDE for both) and shares the same generator as the one in (3.2). The shortcut in the foregoing is in the explicit construction of a process ($Z$ from equation (3.1)) that already *is* stationary (immediately after it starts at $t = 0$), has the same law (for any fixed $t$, including $t = 0$) as the integral taken at infinite time period, and is subject to a Markovian dynamics described in terms of a concrete generator ($\mathcal{L}$ from equation (3.2)). This allows us to circumvent the passing-to-the-limit step in the argument, and to immediately conclude that the “running” (as opposed to the “limiting”) density of the already stationary process must solve the associated Fokker–Planck equation, without the need to invoke any tools from diffusion theory in order to justify the ergodicity feature and connect the infinitesimal generator with the limiting law.[^4]

For a twice continuously differentiable function $V \colon \mathbb{R} \to \mathbb{R}$, let

$$
X_t = \int_0^t V(W_s)\,ds \quad \text{and} \quad Y_t = \int_0^t V(W_t - W_s)\,ds, \qquad t \geq 0.
$$

Let $(X_t^{(1)},\, t \geq 0)$ and $(Y_t^{(1)},\, t \geq 0)$ denote the above processes with $V$ replaced by $V'$ and $(X_t^{(2)},\, t \geq 0)$ and $(Y_t^{(2)},\, t \geq 0)$ with $V$ replaced by $V''$. In addition, suppose that

[^3]: Dufresne [11] also discretizes the finite time integral and relies on the discrete time result from Vervaat [31] (effectively, on the result of Chamayou and Letac [5]), before passing to the limit. Yor [34] connects (3.3) with Getoor's result [16] on escape times of Brownian motion.

[^4]: Strictly speaking, although identical in terms of dynamics, the SDE that one can write for the process $Z$ from (3.1) is different for the SDE that one can write for the integral taken over finite time (see [3, 19, 20, 21, 22, 25]) in the sense that the filtration of $Z$ is larger, and this is what allows us to “fit” the limiting distribution into the initial state $Z_0$, which then makes passing to the limit redundant. In fact, the coincidence between the two SDEs is an accident of a sort, because the process $Z$ originates from perturbing in a particular way the integral over infinite time, and the result $Z$ cannot depend on the history of the Brownian motion until time $t$ alone.

<!-- page 9 -->

the function $V$ is chosen so that the following integrals are finite a.s. for any $t > 0$:

$$
\int_0^t \mathbb{E}\big[|V(W_s)|\big]\,\mathrm{d}s < \infty, \quad \int_0^t \mathbb{E}\big[|Y_s^{(2)}|\big]\,\mathrm{d}s < \infty \quad \text{and} \quad \int_0^t \mathbb{E}\big[|Y_s^{(1)}|^2\big]\,\mathrm{d}s < \infty.
$$

As a direct application of Itô’s formula, given any test function (infinitely smooth with compact support) $\varphi \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, we can write

$$
\begin{aligned}
\mathbb{E}[\varphi(X_t, W_t)] - \varphi(0, 0) &= \int_0^t \mathbb{E}\Big[V(W_s)\varphi^{(1,0)}(X_s, W_s) \\
&\quad + \frac{1}{2}\varphi^{(0,2)}(X_s, W_s)\Big]\,\mathrm{d}s,
\end{aligned}
\tag{3.4a}
$$

$$
\begin{aligned}
\mathbb{E}[\varphi(Y_t, W_t)] - \varphi(0, 0) &= \int_0^t \mathbb{E}\Big[V(0)\varphi^{(1,0)}(Y_s, W_s) + \frac{1}{2}Y_s^{(2)}\varphi^{(1,0)}(Y_s, W_s) \\
&\quad + \frac{1}{2}(Y_s^{(1)})^2 \varphi^{(2,0)}(Y_s, W_s) + Y_s^{(1)}\varphi^{(1,1)}(Y_s, W_s) \\
&\quad + \frac{1}{2}\varphi^{(0,2)}(Y_s, W_s)\Big]\,\mathrm{d}s.
\end{aligned}
\tag{3.4b}
$$

Due to the time-reversibility feature (1.3), nothing will change in (3.4b) if throughout this equation, the symbol “$Y$” is replaced with the symbol “$X$”. In our next step, we define the differentiation operator

$$
\mathscr{A}_t(x, y; u, v) := \frac{1}{2}u^2 \frac{\partial^2}{\partial x^2} + u \frac{\partial^2}{\partial x\,\partial y} + \left(\frac{1}{2}v + V(0) - V(y)\right) \frac{\partial}{\partial x},
$$

subtract (3.4a) from (3.4b) (after replacing “$Y$” by “$X$”), and differentiate in $t$. This yields the relation

$$
\mathbb{E}\Big[\big(\mathscr{A}_t(X_t, W_t; X_t^{(1)}, X_t^{(2)})\varphi\big)(X_t, W_t)\Big] = 0.
\tag{3.5}
$$

Let

$$
\phi_t(x \mid y) := \frac{1}{\mathrm{d}x}\,\mathbb{P}[X_t \in \mathrm{d}x \mid W_t = y], \qquad x > 0,\; -\infty < y < \infty,
$$

denote the conditional density of $X_t$ given $W_t$, and let

$$
M_{x,y}(\mathrm{d}u, \mathrm{d}v) := \mathbb{P}\big[X_t^{(1)} \in \mathrm{d}u,\; X_t^{(2)} \in \mathrm{d}v \mid X_t = x,\; W_t = y\big], \qquad (u, v) \in \mathbb{R}^2,
$$

be the conditional distribution of $(X_t^{(1)}, X_t^{(2)})$ given $(X_t, W_t)$. By way of an example, with $V(\cdot) = \exp^{\sigma\cdot}$, we have $X_t^{(1)} = \sigma X_t$ and $X_t^{(2)} = \sigma^2 X_t$, in which case $M_{x,y}(\mathrm{d}u, \mathrm{d}v)$ is nothing but a point mass at $(\sigma x, \sigma^2 x)$. In any case, we can now rewrite (3.5) in the equivalent form

$$
\frac{1}{\sqrt{2\pi t}} \int_{-\infty}^{\infty} \mathrm{d}y \int_0^{\infty} \mathrm{d}x\, e^{-\frac{y^2}{2t}} \phi_t(x \mid y) \left(\int_{\mathbb{R}^2} M_{x,y}(\mathrm{d}u, \mathrm{d}v)\,\mathscr{A}_t(x, y; u, v)\right) \varphi(x, y) = 0.
$$

<!-- page 10 -->

As this relation must hold for any test function $\varphi$, we arrive at the equation
$$
\left(\int_{\mathbb{R}^2} M_{x,y}(du,dv)\,\mathcal{A}_t(x,y;u,v)\right)^{*}\!\left(e^{-\frac{y^2}{2t}}\phi_t(x|y)\right)=0,
$$
where $(\cdot)^{*}$ denotes the usual adjoint operator. As noted earlier, with $V(\cdot)=\exp^{\sigma\cdot}$, the above adjoint is simply $\mathcal{A}_t(x,y;\sigma x,\sigma^2 x)^{*}$ and the last equation specializes to
$$
\frac{\partial}{\partial x}\left(\frac{\sigma^2 x^2}{2}\frac{\partial}{\partial x}\phi_{t,\sigma}(x|y)+\sigma x\frac{\partial}{\partial y}\phi_{t,\sigma}(x|y)-\left(\frac{\sigma xy}{t}-\frac{\sigma^2 x}{2}+1-e^{\sigma y}\right)\phi_{t,\sigma}(x|y)\right)=0.
\tag{3.6a}
$$

Since the unconditional joint density $\phi_{t,\sigma}(x,y)$ is linked to $\phi_{t,\sigma}(x|y)$ through the relation
$$
\phi_{t,\sigma}(x,y)=\frac{1}{\sqrt{2\pi t}}e^{-\frac{y^2}{2t}}\phi_{t,\sigma}(x|y),
$$
the above PDE can be restated as
$$
\frac{\partial}{\partial x}\left(\frac{\sigma^2 x^2}{2}\frac{\partial}{\partial x}\phi_{t,\sigma}(x,y)+\sigma x\frac{\partial}{\partial y}\phi_{t,\sigma}(x,y)+\left(e^{\sigma y}+\frac{\sigma^2 x}{2}-1\right)\phi_{t,\sigma}(x,y)\right)=0.
\tag{3.6b}
$$

*Remark 3.2* In much the same way, the invariance relation (1.3) can be used to obtain PDEs for the joint density of other integral functionals of Brownian motion. In particular, given any $p>0$, one can write
$$
\left(\int_0^t e^{W_s}\,ds,\,\frac{1}{p}\log\int_0^t e^{pW_s}\,ds,\,W_t\right)\stackrel{\text{law}}{=}\left(e^{W_t}\int_0^t e^{-W_s}\,ds,\,W_t+\frac{1}{p}\log\int_0^t e^{-pW_s}\,ds,\,W_t\right).
$$

Setting
$$
X_t:=\int_0^t e^{W_s}\,ds\quad\text{and}\quad M_t:=\max_{s\in[0,t]}W_s=\lim_{p\nearrow\infty}\frac{1}{p}\log\int_0^t e^{pW_s}\,ds,
$$
the last identity implies $(X_t,M_t,W_t)\stackrel{\text{law}}{=}(e^{-W_t}X_t,M_t-W_t,-W_t)$, which is equivalent to
$$
(X_t,M_t-W_t,M_t)\stackrel{\text{law}}{=}(e^{-W_t}X_t,M_t,M_t-W_t).
$$

As a special case, we have $(M_t-W_t,M_t)\stackrel{\text{law}}{=}(M_t,M_t-W_t)$ which follows trivially from the reflection principle (to be precise, from the well-known formula for the

<!-- page 11 -->

joint density of $(M_t,W_t)$).$^5$ With this observation in mind, it is not very difficult to establish for the joint density of $(X_t,M_t-W_t,M_t)$ the invariance property

$$
e^{z-y}\Phi_t(e^{z-y}x,y,z)=\Phi_t(x,y,z)=e^{y-z}\Phi_t(e^{y-z}x,z,y),\qquad x,y,z\in\mathbb{R}_+,
$$

and then derive a PDE for that density, which is analogous to (3.6b) above. Unfortunately, it does not appear to be possible to reduce this PDE to a first order PDE. In much the same way, one can develop a PDE for the joint density of

$$
\left(\int_0^t W_s\,\mathrm{d}s,\,\int_0^t W_s^2\,\mathrm{d}s,\,W_t\right).
$$

**4 Foliation of the joint law of** $(\int_0^t e^{\sigma W_s}\,\mathrm{d}s,\,W_t)$

In order to solve (3.6a) in the domain $\{x>0,\,-\infty<y<\infty\}$, we first note that this equation implies that for some yet to be determined function $y\mapsto\alpha(y)$, one must have

$$
\begin{aligned}
&\frac{\sigma^2 x}{2}\frac{\partial}{\partial x}\phi_{t,\sigma}(x \mid y)+\sigma\frac{\partial}{\partial y}\phi_{t,\sigma}(x \mid y) \\
&\quad=\left(\frac{\sigma y}{t}-\frac{\sigma^2}{2}+\frac{1-e^{\sigma y}}{x}\right)\phi_{t,\sigma}(x \mid y)+\frac{\alpha(y)}{x}.
\end{aligned}
\tag{4.1}
$$

This is a first order PDE, the nature of which is encrypted into the integral lines of the vector field

$$
(x,y)\mapsto\mathcal{V}(x,y):=\frac{\sigma^2 x}{2}\frac{\partial}{\partial x}+\sigma\frac{\partial}{\partial y}.
$$

These integral lines can be expressed as

$$
\mathbb{R}\ni u\mapsto(\gamma_x(u),\eta_y(u)):=(xe^{\frac{1}{2}\sigma^2 u},\,(y+u)\sigma),
$$

for various choices of $x\in\mathbb{R}_{++}$ and $y\in\mathbb{R}$, and will play a crucial role in our study. We can now restate (4.1) as

$$
\begin{aligned}
&\frac{d}{du}\phi_{t,\sigma}\!\left(xe^{\frac{1}{2}\sigma^2 u} \mid (y+u)\sigma\right) \\
&\quad=\left(\frac{\sigma^2(y+u)}{t}-\frac{\sigma^2}{2}+\frac{1-e^{\sigma^2(y+u)}}{xe^{\frac{1}{2}\sigma^2 u}}\right)\phi_{t,\sigma}\!\left(xe^{\frac{1}{2}\sigma^2 u} \mid (y+u)\sigma\right) \\
&\qquad+\frac{\alpha((y+u)\sigma)}{xe^{\frac{1}{2}\sigma^2 u}},
\end{aligned}
\tag{4.2}
$$

$^5$The connections between the distributions of $X_t$, $M_t$ and $L_t$, the local time of $W$ in $0$, have been studied extensively by several authors—see the survey papers by Matsumoto and Yor [20, 21].

<!-- page 12 -->

and observe that

$$
\begin{aligned}
\int_0^{\infty} \frac{\mathrm{d}}{\mathrm{d}u} \phi_{t,\sigma}\!\left(x e^{\frac{1}{2}\sigma^2 u} \,\middle|\, (y+u)\sigma\right) \mathrm{d}x
&= \frac{\mathrm{d}}{\mathrm{d}u}\left(e^{-\frac{1}{2}\sigma^2 u} \int_0^{\infty} \phi_{t,\sigma}(x \mid (y+u)\sigma)\,\mathrm{d}x\right) \\
&= \frac{\mathrm{d}}{\mathrm{d}u}\left(e^{-\frac{1}{2}\sigma^2 u}\right) = -\frac{\sigma^2}{2}\,e^{-\frac{\sigma^2}{2}u}.
\end{aligned}
$$

Since the left side of (4.2) integrates (in $x$) to a finite value, the unknown function $\alpha(\cdot)$ must be chosen in such a way that the right side of (4.2) integrates to a finite value as well. However, a formal integration of the right side of (4.2) yields

$$
\begin{aligned}
&\int_0^{\infty} \left(\frac{\sigma^2 (y+u)}{t} - \frac{\sigma^2}{2} + \frac{1 - e^{\sigma^2 (y+u)}}{x e^{\frac{1}{2}\sigma^2 u}}\right) \phi_{t,\sigma}\!\left(x e^{\frac{1}{2}\sigma^2 u} \,\middle|\, (y+u)\sigma\right) \mathrm{d}x \\
&\qquad + \frac{\alpha((y+u)\sigma)}{e^{\frac{1}{2}\sigma^2 u}} \int_0^{\infty} \frac{1}{x}\,\mathrm{d}x, \qquad u \in \mathbb{R},
\end{aligned}
$$

and with $u = 0$ this expression becomes

$$
\int_0^{\infty} \left(\frac{\sigma^2 y}{t} - \frac{\sigma^2}{2} + \frac{1 - e^{\sigma^2 y}}{x}\right) \phi_{t,\sigma}(x \mid \sigma y)\,\mathrm{d}x + \alpha(\sigma y) \int_0^{\infty} \frac{1}{x}\,\mathrm{d}x. \tag{4.3}
$$

Since the integral

$$
\int_0^{t} \frac{\phi_{t,\sigma}(x \mid \sigma y)}{x}\,\mathrm{d}x = \mathbb{E}\left[\left(\int_0^{t} e^{\sigma W_s}\,\mathrm{d}s\right)^{-1} \,\middle|\, W_t = y\right]
$$

is finite (see Lemma 2.1) while $\int_0^{\infty} \frac{1}{x}\,\mathrm{d}x = \infty$, we see that (4.3) can be finite only if we set the function $\alpha(\cdot)$ to $0$. Essentially, we are using the finiteness of the above integral as a “boundary condition” from which we can fix the solution to (3.6a). In any case, integrating both sides of (4.2) with $\alpha(\cdot) = 0$ and $u = 0$, we arrive at the special form

$$
\frac{\sigma^2 y}{t} + (1 - e^{\sigma^2 y}) \int_0^{t} \frac{\phi_{t,\sigma}(x \mid \sigma y)}{x}\,\mathrm{d}x = 0
$$

or, equivalently,

$$
(e^{\sigma^2 y} - 1) \int_0^{t} \frac{\phi_{t,\sigma}(x \mid \sigma y)}{x}\,\mathrm{d}x = \frac{\sigma^2 y}{t}.
$$

With $y \neq 0$, the last relation yields

$$
\int_0^{t} \frac{\phi_{t,\sigma}(x \mid y/\sigma)}{x}\,\mathrm{d}x = \frac{y}{t(e^y - 1)},
$$

and as both sides are continuous functions of $y$, letting $y \to 0$ gives

<!-- page 13 -->

$$
\int_0^{t} \frac{\phi_{t,\sigma}(x \mid 0)}{x}\,\mathrm{d}x = \frac{1}{t}.
$$

These findings can be summarized as follows.

**Theorem 4.1** *In the domain $\{(x,y): x>0,\,-\infty<y<\infty\}$, the conditional density $\phi_{t,\sigma}(x \mid y)$ satisfies the first order PDE*
$$
\frac{\sigma^2 x}{2}\frac{\partial}{\partial x}\phi_{t,\sigma}(x \mid y)+\sigma\frac{\partial}{\partial y}\phi_{t,\sigma}(x \mid y)=\left(\frac{\sigma y}{t}+\frac{1-e^{\sigma y}}{x}-\frac{\sigma^2}{2}\right)\phi_{t,\sigma}(x \mid y),
$$
*which is equivalent to the PDE, for the unconditional density,*
$$
\frac{\sigma^2 x}{2}\frac{\partial}{\partial x}\phi_{t,\sigma}(x,y)+\sigma\frac{\partial}{\partial y}\phi_{t,\sigma}(x,y)=\left(\frac{1-e^{\sigma y}}{x}-\frac{\sigma^2}{2}\right)\phi_{t,\sigma}(x,y).
$$

*In addition, we have the identity*
$$
\mathbb{E}\left[\left(\int_0^{t} e^{\sigma W_s}\,\mathrm{d}s\right)^{-1} \,\middle|\, W_t = y/\sigma\right]=\frac{y}{t(e^y-1)} \quad \text{for any } y \in \mathbb{R}, \tag{4.4}
$$
*where the right side is understood to be $\frac{1}{t}$ when $y=0$.*

**Remark 4.2** The last identity was first discovered by Donati-Martin et al. [8] (see also [9]). The reason why (4.4) was referred to as “striking” by those who first discovered it is that the expectation on the left appears to be invariant under the choice of $\sigma$. We note that the method used above is completely different from the one employed in [8] and [9]. It is also very different from the derivation of Hobson [17], who showed that (4.4) follows from Vervaat’s relationship between Brownian bridges and excursions, and from Chaumont et al. [6], where (4.4) is derived from the cyclic exchangeability property of exponential functionals of Lévy processes. While it is not uncommon to arrive at one and the same relation with different methods and from different points of view, it is remarkable that in this case, the methods and the points of view appear to be entirely unrelated. $\square$

Coming back now to the integral lines $\mathbb{R}\ni u\mapsto(\gamma_x(u),\eta_y(u))$ of the vector field $\mathcal{V}(x,y)$, we observe that there is precisely one such line that passes through any $(x,y)\in\mathbb{R}_{++}\times\mathbb{R}$, and any such line is completely determined by the intercept $\eta_y(u)=0$. Thus, the entire family of integral lines can be described as
$$
\left\{\mathbb{R}\ni u\mapsto\left(\gamma_x(u),\eta_0(u)\right)=\left(xe^{\frac{1}{2}\sigma^2 u},\,\sigma u\right)\in\mathbb{R}_{++}\times\mathbb{R}: x\in\mathbb{R}_{++}\right\},
$$
or equivalently as
$$
\left\{\mathbb{R}\ni u\mapsto\left(\frac{x}{\sigma^2}e^{\frac{u}{2}},\,\frac{u}{\sigma}\right)\in\mathbb{R}_{++}\times\mathbb{R}: x\in\mathbb{R}_{++}\right\},
$$

<!-- page 14 -->

which gives a *foliation* of the space $\mathbb{R}_{++} \times \mathbb{R}$ into 1-manifolds. The key feature of this foliation is that an explicit expression for the logarithmic derivative of the (conditional or unconditional) density along each of its 1-manifolds is readily available, as we are about to establish. To this end, we first note that, setting$^6$
$$
Z_t = \sigma^2 e^{-\frac{\sigma^2}{2} W_t} \int_0^t e^{\sigma W_s}\,\mathrm{d}s,
$$
we can write
$$
\frac{1}{\mathrm{d}x\,\mathrm{d}u}\,\mathbb{P}[Z_t \in \mathrm{d}x,\,\sigma W_t \in \mathrm{d}u] = \phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}},\,\frac{u}{\sigma}\right).
$$

Next, notice that the first order equations for $\phi_{t,\sigma}(x \mid y)$ and $\phi_{t,\sigma}(x,y)$ from Theorem 4.1 can be foliated into the two (equivalent) collections of ODEs
$$
\frac{\mathrm{d}}{\mathrm{d}u}\phi_{t,\sigma}\!\left(x e^{\frac{1}{2}\sigma^2 u},\,\sigma u\right) = \left(\frac{1 - e^{\sigma^2 u}}{x e^{\frac{1}{2}\sigma^2 u}} - \frac{\sigma^2}{2}\right)\phi_{t,\sigma}\!\left(x e^{\frac{1}{2}\sigma^2 u},\,\sigma u\right), \quad x \in \mathbb{R}_{++},
$$
$$
\frac{\mathrm{d}}{\mathrm{d}u}\phi_{t,\sigma}\!\left(x e^{\frac{1}{2}\sigma^2 u} \,\middle|\, \sigma u\right) = \left(\frac{\sigma^2 u}{t} - \frac{\sigma^2}{2} + \frac{1 - e^{\sigma^2 u}}{x e^{\frac{1}{2}\sigma^2 u}}\right)\phi_{t,\sigma}\!\left(x e^{\frac{1}{2}\sigma^2 u} \,\middle|\, \sigma u\right), \quad x \in \mathbb{R}_{++}.
$$

After a simple change of variables, namely $u \mapsto \frac{u}{\sigma^2}$ and $x \mapsto \frac{x}{\sigma^2}$, these (equivalent) equations take the form
$$
\frac{\mathrm{d}}{\mathrm{d}u}\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}},\,\frac{u}{\sigma}\right) = -\left(\frac{1}{2} + \frac{2}{x}\sinh\frac{u}{2}\right)\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}},\,\frac{u}{\sigma}\right), \quad x \in \mathbb{R}_{++},
$$
$$
\frac{\mathrm{d}}{\mathrm{d}u}\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}} \,\middle|\, \frac{u}{\sigma}\right) = \left(\frac{u}{\sigma^2 t} - \frac{1}{2} - \frac{2}{x}\sinh\frac{u}{2}\right)\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}} \,\middle|\, \frac{u}{\sigma}\right), \quad x \in \mathbb{R}_{++}.
$$

The integration of the first equation gives
$$
\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}},\,\frac{u}{\sigma}\right) = C_t(x)\,e^{-\frac{u}{2} - \frac{4}{x}\cosh\frac{u}{2}}.
$$

To determine the function $C_t(x)$, i.e., the free constant from the integration, observe that
$$
\mathbb{P}[\sigma W_t \in \mathrm{d}u \mid Z_t \in \mathrm{d}x] = \frac{\mathbb{P}[\sigma W_t \in \mathrm{d}u,\,Z_t \in \mathrm{d}x]}{\mathbb{P}[Z_t \in \mathrm{d}x]}\,\mathrm{d}u = \frac{\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}},\,\frac{u}{\sigma}\right)}{h_t(x)}\,\mathrm{d}u,
$$
where $h_t(x) = \frac{1}{\mathrm{d}x}\,\mathbb{P}[Z_t \in \mathrm{d}x]$ is the (smooth) density of $Z_t$. Consequently,$^7$

$^6$ Processes of this form have played an important role in other studies—see the survey papers by Matsumoto and Yor [20, 21].

$^7$ See http://dlmf.nist.gov/10.32.E9 regarding the identity involving $K_1$.

<!-- page 15 -->

$$
\frac{h_t(x)}{C_t(x)} = \int_{-\infty}^{\infty} e^{-\frac{u}{2} - \frac{4}{x}\cosh\frac{u}{2}}\,\mathrm{d}u = 2\int_{-\infty}^{\infty} e^{-u - \frac{4}{x}\cosh u}\,\mathrm{d}u
$$
$$
= 4\int_0^{\infty} e^{-\frac{4}{x}\cosh u}\cosh u\,\mathrm{d}u = 4K_1\!\left(\frac{4}{x}\right),
$$
where $K_1$ stands for the modified Bessel function of the second kind.

Similarly, the integration of the equation for the conditional density gives
$$
\phi_{t,\sigma}\!\left(\frac{x}{\sigma^2}e^{\frac{u}{2}} \,\middle|\, \frac{u}{\sigma}\right) = \Lambda_t\!\left(\frac{x}{\sigma^2}\right) e^{-\frac{u}{2} - \frac{4}{x}\cosh\frac{u}{2} + \frac{u^2}{2\sigma^2 t}}, \quad x \in \mathbb{R}_{++},\, u \in \mathbb{R}. \tag{4.5}
$$

Setting $u = 0$ in the last relation, we see that the function $\Lambda_t(\cdot)$ can be expressed as
$$
\Lambda_t(x) = \phi_{t,\sigma}(x \mid 0)\,e^{4/(\sigma^2 x)} \quad \text{or} \quad \Lambda_t\!\left(\frac{x}{\sigma^2}\right) = \phi_{t,\sigma}\!\left(\frac{x}{\sigma^2} \,\middle|\, 0\right) e^{\frac{4}{x}}, \quad x \in \mathbb{R}_{++},
$$
and therefore (4.5) can be rearranged as
$$
\phi_{t,\sigma}(x \mid y) = \phi_{t,\sigma}\!\left(x e^{-\frac{\sigma y}{2}} \,\middle|\, 0\right) e^{-\frac{\sigma y}{2} - \frac{2}{\sigma^2 x}\left(e^{\frac{\sigma y}{2}} - 1\right)^2 + \frac{y^2}{2t}}. \tag{4.6}
$$

As we are about to see, this last relation would allow us to obtain a closed-form expression for the *Laplace transform* of the conditional law of $\left(\int_0^t e^{\sigma W_s}\,\mathrm{d}s\right)^{-1}$ given the position of the Brownian motion at time $t$, i.e.,
$$
\mathscr{L}_{t,y}(u) = \int_0^{\infty} e^{-\frac{u}{x}} \phi_{t,\sigma}(x \mid y)\,\mathrm{d}x, \quad u > 0.
$$

*Remark 4.3* We stress that here we work with Laplace transforms with respect to the probability measure, not with respect to the time variable. $\square$

To facilitate the calculation of $\mathscr{L}_{t,y}(u)$, we now define the family of operators $\mathscr{T}_{t,y}$, $y \in \mathbb{R}$, to act on continuous functions $\varphi : \mathbb{R}_{++} \to \mathbb{R}$ according to the rule
$$
(\mathscr{T}_{t,y}\varphi)(x) := \varphi\!\left(x e^{-\frac{\sigma y}{2}}\right) e^{-\frac{\sigma y}{2} - \frac{2}{\sigma^2 x}\left(e^{\frac{\sigma y}{2}} - 1\right)^2 + \frac{y^2}{2t}}, \quad x > 0.
$$

With this operation in mind, (4.6) can be interpreted as $\phi_{t,\sigma}(\cdot \mid y) = \mathscr{T}_{t,y}\phi_{t,\sigma}(\cdot \mid 0)$. Since conditional densities integrate to 1, this observation has the effect that when applied to the function $\phi_{t,\sigma}(\cdot \mid 0)$, the transformations $\mathscr{T}_{t,y}$, $y \in \mathbb{R}$, preserve the probability mass, i.e.,
$$
1 = \int_0^{\infty} \phi_{t,\sigma}(x \mid y)\,\mathrm{d}x = \int_0^{\infty} \mathscr{T}_{t,y}\phi_{t,\sigma}(x \mid 0)\,\mathrm{d}x.
$$

However, for a generic function $\varphi \ge 0$, the property $\int_0^{\infty} \mathscr{T}_{t,y}\varphi(x)\,\mathrm{d}x = 1$ for any $y \in \mathbb{R}$ results into the chain of identities

<!-- page 16 -->

$$
1 = \int_{0}^{\infty} \mathscr{T}_{t,y}\varphi(x)\,\mathrm{d}x = e^{\frac{y^2}{2t}} \int_{0}^{\infty} \varphi\!\left(xe^{-\frac{\sigma y}{2}}\right) e^{-\frac{2}{\sigma^2 x}\left(e^{\frac{\sigma y}{2}} - 1\right)^2} \,\mathrm{d}\!\left(xe^{-\frac{\sigma y}{2}}\right)
$$
$$
= e^{\frac{y^2}{2t}} \int_{0}^{\infty} \varphi(x)\, e^{-\frac{4}{\sigma^2 x}\left(\cosh\frac{\sigma y}{2} - 1\right)} \,\mathrm{d}x. \tag{4.7}
$$

Since the function $\mathbb{R}_+ \ni y \mapsto \frac{4}{\sigma^2}\left(\cosh\frac{\sigma y}{2} - 1\right) \in \mathbb{R}_+$ is one-to-one and invertible, we see from the last relation that $y \mapsto \int_{0}^{\infty} \mathscr{T}_{t,y}$ acts as some sort of a “transformed Laplace transform”, and we can claim the following.

**Proposition 4.4** The density $x \mapsto \phi_{t,\sigma}(x \mid 0)$ can be identified as the unique function $x \mapsto \varphi(x)$ that has the property $\int_{0}^{\infty} \mathscr{T}_{t,y}\varphi(x)\,\mathrm{d}x = 1$ for all $y \in \mathbb{R}$.

This brings us to the following result.

**Theorem 4.5** For fixed $t > 0$ and $\sigma > 0$, the Laplace transform of the conditional law
$$
\frac{1}{\mathrm{d}x}\,\mathbb{P}\!\left[\left(\int_0^t e^{\sigma W_s}\,\mathrm{d}s\right)^{-1} \in \mathrm{d}x \,\middle|\, W_t = y\right], \quad x > 0,\, y \in \mathbb{R},
$$
is given by
$$
\mathscr{L}_{t,y}(u) = \int_{0}^{\infty} e^{-\frac{u}{x}} \phi_{t,\sigma}(x \mid y)\,\mathrm{d}x = e^{\frac{y^2}{2t} - \frac{2}{\sigma^2 t}\operatorname{arcosh}^2\!\left(\cosh\frac{\sigma y}{2} + \frac{u\sigma^2}{4}\, e^{-\frac{\sigma y}{2}}\right)}.
$$

*Proof* Establishing this result is merely a matter of computation, which comes down to integrating (4.6), changing the integration variable accordingly, and taking into account (4.7). This yields
$$
\mathscr{L}_{t,y}(u) = \int_{0}^{\infty} e^{-\frac{u}{x}} \phi_{t,\sigma}(x \mid y)\,\mathrm{d}x
$$
$$
= \int_{0}^{\infty} e^{-\frac{u}{x}} \phi_{t,\sigma}\!\left(xe^{-\frac{\sigma y}{2}} \,\middle|\, 0\right) e^{-\frac{\sigma y}{2} - \frac{2}{\sigma^2 x}\left(e^{\frac{\sigma y}{2}} - 1\right)^2 + \frac{y^2}{2t}} \,\mathrm{d}x
$$
$$
= e^{\frac{y^2}{2t}} \int_{0}^{\infty} \phi_{t,\sigma}(x \mid 0)\, e^{-\frac{1}{x} e^{-\frac{\sigma y}{2}}\left(u + \frac{2}{\sigma^2}\left(e^{\frac{\sigma y}{2}} - 1\right)^2\right)} \,\mathrm{d}x
$$
$$
= e^{\frac{y^2}{2t}} \int_{0}^{\infty} \phi_{t,\sigma}(x \mid 0)\, e^{-\frac{4}{\sigma^2 x}\left(u e^{-\frac{\sigma y}{2}}\frac{\sigma^2}{4} + \cosh\frac{\sigma y}{2} - 1\right)} \,\mathrm{d}x
$$
$$
= e^{\frac{y^2}{2t}} \int_{0}^{\infty} \phi_{t,\sigma}(x \mid 0)\, e^{-\frac{4}{\sigma^2 x}\left(\cosh\frac{\sigma z}{2} - 1\right)} \,\mathrm{d}x,
$$

where
$$
\cosh\frac{\sigma z}{2} = u e^{-\frac{\sigma y}{2}}\frac{\sigma^2}{4} + \cosh\frac{\sigma y}{2} \quad \text{or} \quad z = \frac{2}{\sigma}\operatorname{arcosh}\!\left(\cosh\frac{\sigma y}{2} + u e^{-\frac{\sigma y}{2}}\frac{\sigma^2}{4}\right).
$$

<!-- page 17 -->

**Another look at the integral of exponential Brownian motion** · **1077**

The Laplace transform can now be written as

$$
\mathscr{L}_{t,y}(u) = e^{\frac{y^2}{2t}} e^{-\frac{z^2}{2t}} e^{\frac{z^2}{2t}} \int_{0}^{\infty} \phi_{t,\sigma}(x \mid 0)\, e^{-\frac{4}{\sigma^2 x}\left(\cosh\frac{\sigma z}{2} - 1\right)} \,\mathrm{d}x = e^{\frac{y^2}{2t}} e^{-\frac{z^2}{2t}}. \square
$$

Now we can obtain again the “striking” identity in (4.4), this time by differentiating the Laplace transform $\mathscr{L}_{t,y}(u)$; a straightforward—albeit somewhat tedious—calculation gives

$$
\begin{aligned}
\mathbb{E}\left[\left(\int_{0}^{t} e^{\sigma W_s}\,\mathrm{d}s\right)^{-1} \,\Big|\, W_t = y\right] &= -\lim_{u \to 0} \frac{\partial}{\partial u} \mathscr{L}_{t,y}(u) \\
&= \frac{\sigma y}{t\left(e^{\sigma y} - 1\right)}, \quad -\infty < y < \infty.
\end{aligned}
$$

The calculation of moments of higher order is possible—especially if delegated to computer algebra. By way of an example, the Sage program gives the expansion

$$
\begin{aligned}
\mathscr{L}_{t,0}(u) \\
= {}& \frac{1}{810967336058880000}\left(\frac{171460800\,\sigma^{18}}{t} + \frac{3168117684\,\sigma^{16}}{t^2}\right. \\
&\quad + \frac{26520488325\,\sigma^{14}}{t^3} + \frac{132024741590\,\sigma^{12}}{t^4} + \frac{430791891075\,\sigma^{10}}{t^5} \\
&\quad + \frac{955555260660\,\sigma^{8}}{t^6} + \frac{1440985946400\,\sigma^{6}}{t^7} + \frac{1424690467200\,\sigma^{4}}{t^8} \\
&\quad \left.+ \frac{838053216000\,\sigma^{2}}{t^9} + \frac{223480857600}{t^{10}}\right) u^{10} \\
&- \frac{1}{1067062284288000}\left(\frac{2116800\,\sigma^{16}}{t} + \frac{38798964\,\sigma^{14}}{t^2} + \frac{317833445\,\sigma^{12}}{t^3}\right. \\
&\quad + \frac{1520066730\,\sigma^{10}}{t^4} + \frac{4642833195\,\sigma^{8}}{t^5} + \frac{9274945680\,\sigma^{6}}{t^6} \\
&\quad \left.+ \frac{11835663840\,\sigma^{4}}{t^7} + \frac{8821612800\,\sigma^{2}}{t^8} + \frac{2940537600}{t^9}\right) u^{9} \\
&+ \frac{1}{6974263296000}\left(\frac{132300\,\sigma^{14}}{t} + \frac{2400129\,\sigma^{12}}{t^2} + \frac{19114550\,\sigma^{10}}{t^3}\right. \\
&\quad + \frac{86641555\,\sigma^{8}}{t^4} + \frac{241441200\,\sigma^{6}}{t^5} + \frac{413693280\,\sigma^{4}}{t^6} + \frac{403603200\,\sigma^{2}}{t^7} \\
&\quad \left.+ \frac{172972800}{t^{8}}\right) u^{8}
\end{aligned}
$$

<!-- page 18 -->

**1078** · A. Lyasoff

$$
\begin{aligned}
&- \frac{1}{14529715200}\left(\frac{2700\sigma^{12}}{t} + \frac{48321\sigma^{10}}{t^2} + \frac{370370\sigma^{8}}{t^3} + \frac{1556555\sigma^{6}}{t^4} + \frac{3783780\sigma^{4}}{t^5} + \frac{5045040\sigma^{2}}{t^6} + \frac{2882880}{t^7}\right) u^7 \\
&+ \frac{1}{159667200}\left(\frac{300\sigma^{10}}{t} + \frac{5269\sigma^{8}}{t^2} + \frac{38225\sigma^{6}}{t^3} + \frac{143220\sigma^{4}}{t^4} + \frac{277200\sigma^{2}}{t^5} + \frac{221760}{t^6}\right) u^6 \\
&- \frac{1}{604800}\left(\frac{12\sigma^{8}}{t} + \frac{205\sigma^{6}}{t^2} + \frac{1365\sigma^{4}}{t^3} + \frac{4200\sigma^{2}}{t^4} + \frac{5040}{t^5}\right) u^5 \\
&+ \frac{1}{13440}\left(\frac{3\sigma^{6}}{t} + \frac{49\sigma^{4}}{t^2} + \frac{280\sigma^{2}}{t^3} + \frac{560}{t^4}\right) u^4 - \frac{1}{360}\left(\frac{\sigma^{4}}{t} + \frac{15\sigma^{2}}{t^2} + \frac{60}{t^3}\right) u^3 \\
&+ \frac{1}{24}\left(\frac{\sigma^{2}}{t} + \frac{12}{t^2}\right) u^2 - \frac{u}{t} + 1 + \mathcal{O}(u^{11}).
\end{aligned}
$$

From the last expansion, one can easily obtain the values for

$$
\mathbb{E}\left[\left(\int_{0}^{t} e^{\sigma W_s}\,\mathrm{d}s\right)^{-p} \,\middle|\, W_t = 0\right]
$$

with $p = 0, 1, \ldots, 10$ (we use Sage again) as

$$
\begin{aligned}
&1,\quad \frac{1}{t},\quad \frac{\sigma^2}{12t} + \frac{1}{t^2},\quad \frac{\sigma^4}{60t} + \frac{\sigma^2}{4t^2} + \frac{1}{t^3},\quad \frac{3\sigma^6}{560t} + \frac{7\sigma^4}{80t^2} + \frac{\sigma^2}{2t^3} + \frac{1}{t^4}, \\
&\frac{\sigma^8}{420t} + \frac{41\sigma^6}{1008t^2} + \frac{13\sigma^4}{48t^3} + \frac{5\sigma^2}{6t^4} + \frac{1}{t^5},\quad \frac{5\sigma^{10}}{3696t} + \frac{479\sigma^8}{20160t^2} + \frac{695\sigma^6}{4032t^3} + \frac{31\sigma^4}{48t^4} + \frac{5\sigma^2}{4t^5} + \frac{1}{t^6}, \\
&\frac{15\sigma^{12}}{16016t} + \frac{59\sigma^{10}}{3520t^2} + \frac{37\sigma^8}{288t^3} + \frac{311\sigma^6}{576t^4} + \frac{21\sigma^4}{16t^5} + \frac{7\sigma^2}{4t^6} + \frac{1}{t^7}, \\
&\frac{7\sigma^{14}}{9152t} + \frac{266681\sigma^{12}}{19219200t^2} + \frac{4201\sigma^{10}}{38016t^3} + \frac{17311\sigma^8}{34560t^4} + \frac{67\sigma^6}{48t^5} + \frac{287\sigma^4}{120t^6} + \frac{7\sigma^2}{3t^7} + \frac{1}{t^8}, \\
&\frac{7\sigma^{16}}{9724t} + \frac{63397\sigma^{14}}{4804800t^2} + \frac{3739217\sigma^{12}}{34594560t^3} + \frac{32753\sigma^{10}}{63360t^4} + \frac{2021\sigma^8}{1280t^5} + \frac{757\sigma^6}{240t^6} + \frac{161\sigma^4}{40t^7} + \frac{3\sigma^2}{t^8} + \frac{1}{t^9},
\end{aligned}
$$

<!-- page 19 -->

**Another look at the integral of exponential Brownian motion** · **1079**

$$
\frac{567\sigma^{18}}{739024\,t} + \frac{1543917\sigma^{16}}{108908800\,t^2} + \frac{364919\sigma^{14}}{3075072\,t^3} + \frac{5839219\sigma^{12}}{9884160\,t^4} + \frac{21713\sigma^{10}}{11264\,t^5}
$$

$$
+ \frac{5473\sigma^{8}}{1280\,t^6} + \frac{619\sigma^{6}}{96\,t^7} + \frac{51\sigma^{4}}{8\,t^8} + \frac{15\sigma^{2}}{4\,t^9} + \frac{1}{t^{10}}.
$$

**Remark 4.6** It is now clear that the striking identity discovered by Donati-Martin et al. [8] is a special case of a perhaps even more striking feature: The conditional moments of $\mathbb{E}\bigl[(\int_0^t e^{\sigma W_s}\,\mathrm{d}s)^{-p} \mid W_t = 0\bigr]$ can be written as homogeneous polynomials of degree $p$ from the variables $\sigma^2$ and $\frac{1}{t}$ with leading term $\frac{1}{t^p}$ and final term equal to const. $\frac{\sigma^{2(p-1)}}{t}$, for $p \geq 2$.

## 5 Integral representations for the density of the integral taken over finite time

Since the densities of the integrals $\int_0^t e^{\sigma W_s}\,\mathrm{d}s$, for various choices of $\sigma$, are simple transformations of one another, it would be enough for us to compute the density with $\sigma = 1$. Furthermore, because of the connection established in (4.6), it would suffice to compute just the conditional density $\phi_{t,1}(\cdot \mid 0)$. In conjunction with Proposition 4.4 and the relation (4.7), this calculation comes down to solving for the function $\mathbb{R}_{++} \ni x \mapsto \varphi_t(x)$ from the integral equation (this is simply (4.7) with the substitutions $\sigma = 1$ and $y = 2y$)

$$
\int_0^\infty \varphi_t(x)\, e^{-\frac{4\cosh y - 4}{x}}\,\mathrm{d}x = e^{-\frac{2y^2}{t}}. \tag{5.1}
$$

Essentially, the problem comes down to inverting a concrete Laplace transform, and the idea is to do this by developing various integral expressions for the density that are consistent with the Laplace transform. Inspired by Yor’s discovery [32] that the density of the Hartman–Watson distribution may be interpreted as a contour integral,$^8$ we attempt to resolve the above equation for $\varphi_t(\cdot)$ by seeking solutions in the form of contour integrals written as

$$
\varphi_t(x) = \frac{1}{x^p}\oint_\gamma e^{-\frac{z}{x}}\, f_{t,p}(z)\,\mathrm{d}z, \qquad x \in \mathbb{R},
$$

for various choices of the contour $\gamma \subset \{z \in \mathbb{C} : \mathfrak{R}(z) > 0\}$, the integer $p \geq 2$ and the function $f_{t,p}(\cdot)$. As we are about to see, there is simply too much to choose from, and Yor’s formula (1.1) can be seen as one such choice. Assuming that the operations $\int_0^\infty \mathrm{d}x$ and $\oint_\gamma \mathrm{d}z$ can be interchanged, we must choose the contour $\gamma$ and the function $z \mapsto f_{t,p}(z)$ so that the following identity holds for any $y \in \mathbb{R}$:

$$
\oint_\gamma f_{t,p}(z) \left( \int_0^\infty \frac{1}{x^p}\, e^{-\frac{z + 4\cosh y - 4}{x}}\,\mathrm{d}x \right) \mathrm{d}z = \oint_\gamma \frac{f_{t,p}(z)\,(p-2)!}{(z + 4\cosh y - 4)^{p-1}}\,\mathrm{d}z
$$

$$
= e^{-\frac{2y^2}{t}}. \tag{5.2}
$$

$^8$Yor’s formula (1.1) is essentially a consequence from the contour integral representation of the density of the Hartman–Watson law.

<!-- page 20 -->

It is clear from the last relation that in order to justify the interchange of the two integration operations, it would be enough to check that

$$
\oint_{\gamma} \frac{|f_{t,p}(z)|}{|z + 4\cosh y - 4|^{p-1}} \, |\mathrm{d}z| < \infty \quad \text{for any } y \in \mathbb{R}.
$$

Our first step in this program is to rewrite the above contour integral in a more tractable form that makes the calculus of residues easier to implement. In particular, we should like to express the contour $\gamma$ as a function of the form

$$
\theta \mapsto \gamma(\theta) = -4(\cosh \zeta(\theta) - 1) \in \mathbb{C},
$$

where $\theta \mapsto \zeta(\theta)$ represents another contour inside $\mathbb{C}$. As $\gamma \subset \{z \in \mathbb{C} : \mathfrak{R}(z) > 0\}$, we must have $\zeta \subset \{z \in \mathbb{C} : \mathfrak{R}(\cosh z) < 1\}$. Changing the variables in (5.2) accordingly, we arrive at the following equation for the contour $\zeta$ and the function $g_{t,p}(z) := f_{t,p}(4 - 4\cosh z)$ (i.e., we seek the unknown function $f_{t,p}(\cdot)$ in the form $f_{t,p}(z) = g_{t,p}(\mathrm{arcosh}(1 - z/4))$, $z \in \mathbb{C}$, for some yet to be determined function $g_{t,p}(\cdot)$):

$$
\oint_{\zeta} \frac{g_{t,p}(z)}{(\cosh z - \cosh y)^{p-1}} \sinh z \,\mathrm{d}z = \frac{(-4)^{p-2}}{(p-2)!} e^{-\frac{2y^2}{t}} \quad \text{for all } y \in \mathbb{R}. \tag{5.3}
$$

As long as the contour $\zeta$ and the function $z \mapsto g_{t,p}(z)$ satisfy the above relation, we can express the conditional density as a contour integral of the form

$$
\begin{aligned}
\phi_{t,1}(x \mid 0) &= \frac{1}{x^p} \oint_{\gamma} e^{-\frac{z}{x}} f_{t,p}(z) \,\mathrm{d}z \\
&= -\frac{4}{x^p} \oint_{\zeta} e^{\frac{4}{x}(\cosh z - 1)} g_{t,p}(z) \sinh z \,\mathrm{d}z, \quad x \in \mathbb{R}.
\end{aligned} \tag{5.4}
$$

The only remaining task is to establish precisely how the contour $\zeta$ and the function $z \mapsto g_{t,p}(z)$ can be engineered to solve (5.3). To start with this program, notice first that if $\zeta$ is a closed contour that bounds a region $\Omega$ which contains the entire real line $\mathbb{R}$, and if the function $\zeta \ni z \mapsto g_{t,p}(z)$ has an analytic extension to the entire domain $\Omega$, the calculus of residues would reduce (5.3) to

$$
R_{t,p}(y) + R_{t,p}(-y) = \frac{1}{2\pi i} \frac{(-4)^{p-2}}{(p-2)!} e^{-\frac{2y^2}{t}}, \quad y \in \mathbb{R},\, p \geq 2, \tag{5.5}
$$

where

$$
R_{t,p}(y) := \frac{1}{(p-2)!} \lim_{z \to y} \frac{\mathrm{d}^{p-2}}{\mathrm{d}z^{p-2}} \left( \frac{(z-y)^{p-1} g_{t,p}(z)}{(\cosh z - \cosh y)^{p-1}} \sinh z \right). \tag{5.6}
$$

The calculation of $R_{t,p}(y)$ is completely straightforward for $p = 2, 3$, but for larger values of $p$, the use of computer algebra becomes handy. By way of an example, Sage returns

<!-- page 21 -->

$$
R_{t,2}(y) = g_{t,2}(y), \quad y \in \mathbb{R},
$$

$$
R_{t,3}(y) = \frac{g'_{t,3}(y)}{\sinh y}, \quad y \in \mathbb{R},
$$

$$
R_{t,4}(y) = -\frac{\cosh y\, g'_{t,4}(y)}{2\sinh^3 y} + \frac{g''_{t,4}(y)}{2\sinh^2 y}, \quad y \in \mathbb{R},
$$

$$
R_{t,5}(y) = \frac{g'_{t,5}(y)}{3\sinh^3 y} - \frac{\cosh y\, g''_{t,5}(y)}{2\sinh^4 y} + \frac{g^{(3)}_{t,5}(y)}{6\sinh^3 y} + \frac{g'_{t,5}(y)}{2\sinh^5 y}, \quad y \in \mathbb{R},
$$

$$
\begin{aligned}
R_{t,6}(y) =\;& -\frac{\cosh y\, g'_{t,6}(y)}{4\sinh^5 y} + \frac{11 g''_{t,6}(y)}{24\sinh^4 y} - \frac{\cosh y\, g^{(3)}_{t,6}(y)}{4\sinh^5 y} + \frac{g^{(4)}_{t,6}(y)}{24\sinh^4 y} \\
&\quad - \frac{5 \cosh y\, g'_{t,6}(y)}{8\sinh^7 y} + \frac{5 g''_{t,6}(y)}{8\sinh^6 y}, \quad y \in \mathbb{R}.
\end{aligned}
$$

These relations reveal the general rule for producing the function $R_{t,p}(\cdot)$ from any concrete choice for the function $g_{t,p}(\cdot)$. To put it in another way, one can think of $R_{t,p}$ as a function of the symbol $g_{t,p}$. If we now use the symbol $g(\cdot)$ as a generic placeholder for the input $g_{t,p}(\cdot)$, and interpret the above relations as recipes for producing the symbol $R_{t,p}(\cdot)$ from the generic symbol $g(\cdot)$, we see that for $p \geq 3$, the recipe for producing $R_{t,p}(\cdot)$ is connected to the recipe for producing $R_{t,p-1}(\cdot)$, through the following relation, which is easy to verify directly from (5.6):

$$
R_{t,p}(y) = \frac{1}{(p-2)\sinh y}\frac{d}{dy} R_{t,p-1}(y), \quad R_{t,2}(y) = g(y), \quad y \in \mathbb{R}. \tag{5.7}
$$

In particular, we see that if $g(\cdot)$ is chosen to be an even function, the output $R_{t,p}(\cdot)$ will be even as well, which in conjunction with (5.5) will give us the formula

$$
R_{t,p}(y) = \frac{1}{4\pi i}\frac{(-4)^{p-2}}{\Gamma(p-1)} e^{-\frac{2y^2}{t}}, \quad y \in \mathbb{R}.
$$

Since $R_{t,p}(\cdot)$ is now known, we can recover $g(\cdot)$, which is simply a placeholder for $g_{t,p}(\cdot)$, with $p-2$ anti-differentiations from (5.7). Clearly, the result is going to depend on $p-2$ free constants, but this is to be expected, since the function

$$
z \mapsto g_{t,p}(z) := f_{t,p}(4 - 4\cosh z)
$$

we are looking for cannot be determined uniquely from (5.3). Because all we need is just one concrete choice for $g_{t,p}(\cdot)$, we can suppose that all free constants are null, and with this choice all functions $g_{t,p}(\cdot)$, $p \geq 2$, are automatically even, as intended.$^9$

$^9$ Equation (5.3) is the only condition that we want the function $g_{t,p}(\cdot)$ to satisfy. Because of the magic of the Cauchy formula and the calculus of residues, the left side of (5.3) is nothing but a differentiation operation of order $p-2$ applied to $g_{t,p}(\cdot)$, while the right side is given. It should be clear that (5.3) can be satisfied with infinitely many choices for $g_{t,p}(\cdot)$.

<!-- page 22 -->

With the help of the Sage system again, we arrive for $p = 2, 3, 4$ at the expressions

$$
\begin{aligned}
g_{t,2}(y) &= \frac{1}{4\pi i} e^{-2\frac{y^2}{t}}, \quad y \in \mathbb{R}, \\
g_{t,3}(y) &= e^{t/8} \frac{\sqrt{t}}{4i\sqrt{2\pi}} \left( \mathrm{erf}\left( \frac{t+4y}{2\sqrt{2t}} \right) + \mathrm{erf}\left( \frac{t-4y}{2\sqrt{2t}} \right) \right), \quad y \in \mathbb{R}, \\
g_{t,4}(y) &= e^{t/2} \frac{\sqrt{t}}{2i\sqrt{2\pi}} \left( \mathrm{erf}\left( \frac{t+2y}{\sqrt{2t}} \right) + \mathrm{erf}\left( \frac{t-2y}{\sqrt{2t}} \right) \right) \\
&\quad - e^{t/8} \cosh y \frac{\sqrt{t}}{i\sqrt{2\pi}} \left( \mathrm{erf}\left( \frac{t+4y}{2\sqrt{2t}} \right) + \mathrm{erf}\left( \frac{t-4y}{2\sqrt{2t}} \right) \right), \quad y \in \mathbb{R}. \tag{5.8}
\end{aligned}
$$

In addition to being even, these functions are analytic in the entire complex plane $\mathbb{C}$, and since we have $\overline{\mathrm{erf}(z)} = \mathrm{erf}(\bar{z})$ and $\mathrm{erf}(-z) = -\mathrm{erf}(z)$, $z \in \mathbb{C}$, it is straightforward to check that $\overline{g_{t,p}(z)} = -g_{t,p}(\bar{z})$, $z \in \mathbb{C}$. This last relation has the effect that

$$
\mathfrak{R}(g_{t,p}(z)) = -\mathfrak{R}(g_{t,p}(\bar{z})) \quad \text{and} \quad \mathfrak{I}(g_{t,p}(z)) = \mathfrak{I}(g_{t,p}(\bar{z})).
$$

Now we turn to the equation (5.3) and the choice of the contour

$$
\zeta \subset \{ z \in \mathbb{C} : \mathfrak{R}(\cosh z) < 1 \}.
$$

Since $\mathfrak{R}(\cosh z) = \cos \mathfrak{I}(z) \cosh \mathfrak{R}(z)$, $z \in \mathbb{C}$, the above relation is the same as

$$
\zeta \subset \{ z \in \mathbb{C} : \cos \mathfrak{I}(z) < 1/\cosh \mathfrak{R}(z) \}.
$$

In particular, it would be enough for us to take

$$
\begin{aligned}
\zeta &\subset \{ z \in \mathbb{C} : \cos \mathfrak{I}(z) \leq 0 \} \\
&= \left\{ z \in \mathbb{C} : (2k - 1)\frac{\pi}{2} \leq \mathfrak{I}(z) \leq (2k + 1)\frac{\pi}{2} \text{ for some integer } k \in \mathbb{Z} \setminus \{0\} \right\}.
\end{aligned}
$$

Of course, we must choose $\zeta$ so that it bounds a region $\Omega$ that contains the entire real line $\mathbb{R}$. There is indeed too much to choose from. Perhaps the simplest such choice is

$$
\zeta = \zeta_a := \bigl( (-\infty, +\infty) \ni u \mapsto u - ia \bigr) \cup \bigl( (+\infty, -\infty) \ni u \mapsto u + ia \bigr)
$$

for some fixed $a \in \bigl[\frac{\pi}{2}, \frac{3\pi}{2}\bigr]$. The choice that appears to be “most obvious” is “the middle” $a = \pi$, and as we are about to see, this choice (i.e., $\zeta = \zeta_\pi$) leads to a family of integral representations of which the well-known Yor formula is a special (and extreme, in that it involves the lowest possible power of $p$) case. However, we shall also establish that choosing the borderline $a = \frac{\pi}{2}$ (i.e., $\zeta = \zeta_{\pi/2}$) leads to computationally more tractable representations.$^{10}$ Of course, in order to interpret (see (5.3))

$$
\oint_{\zeta_a} \frac{g_{t,p}(z)}{(\cosh z - \cosh y)^{p-1}} \sinh z \,\mathrm{d}z
$$

$^{10}$ Apparently, there are infinitely many choices for the contour $\zeta$ that can be used for constructing integral representations that are of interest to us. The study of which choices would lead to the most computationally efficient representations is beyond the scope of the present paper. Our choices here appear to be “natural”, but we are also trying to mimic the contour integral representations from [32] simply because we insist on developing integral representation of which (1.1) is a special case.

<!-- page 23 -->

as a closed-contour integral and apply calculus of residues as planned, one must show that

$$
\lim_{n \to \infty} \left( \int_{-1}^{1} \frac{g_{t,p}(n + iau)}{(\cosh(n + iau) - \cosh y)^{p-1}} \sinh(n + iau)\,\mathrm{d}u + \int_{-1}^{1} \frac{g_{t,p}(-n - iau)}{(\cosh(-n - iau) - \cosh y)^{p-1}} \sinh(-n - iau)\,\mathrm{d}u \right) = 0.
$$

However, as long as the function $z \mapsto g_{t,p}(z)$ is chosen to be even, the last two integrals annihilate each other and the above condition is satisfied in a trivial way.

Now we turn to computing the various concrete forms of the general contour-integral representation in (5.4) with $\zeta = \zeta_a$, $\frac{\pi}{2} \le a \le \frac{3\pi}{2}$. Since for any $u \in \mathbb{R}$, we have

$$
-g_{t,p}(u + ia) = \overline{g_{t,p}(u - ia)}, \qquad \cosh(u + ia) = \overline{\cosh(u - ia)}, \qquad \sinh(u + ia) = \overline{\sinh(u - ia)},
$$

we can then write, for $x > 0$,

$$
\begin{aligned}
\phi_{t,1}(x \mid 0) &= -\frac{4}{x^p} \int_{-\infty}^{\infty} \Bigl( e^{\frac{4}{x}(\cosh(u-ia)-1)} g_{t,p}(u - ia) \sinh(u - ia) - e^{\frac{4}{x}(\cosh(u+ia)-1)} g_{t,p}(u + ia) \sinh(u + ia) \Bigr)\,\mathrm{d}u \\
&= -\frac{16}{x^p} e^{-\frac{4}{x}} \int_{0}^{\infty} \mathfrak{R}\left( e^{\frac{4}{x} \cosh(u-ia)}\, g_{t,p}(u - ia)\, \sinh(u - ia) \right)\mathrm{d}u.
\end{aligned}
$$

With a completely analogous calculation, (5.3) can be cast as

$$
2 \int_{-\infty}^{\infty} \mathfrak{R}\left( \frac{g_{t,p}(u - ia)}{(\cosh(u - ia) - \cosh y)^{p-1}}\, \sinh(u - ia) \right)\mathrm{d}u = \frac{(-4)^{p-2}}{(p-2)!}\, e^{-\frac{2y^2}{t}}
$$

for any $y \in \mathbb{R}$. By using the relations

$$
\begin{aligned}
\cosh(u \pm ia) &= \cos(a \mp iu), & \sinh(u \pm ia) &= \pm i \sin(a \mp iu), \\
\cos(\pi \mp iu) &= -\cosh u, & \pm i \sin(\pi \mp iu) &= -\sinh u, \\
\cos(\pi/2 \mp iu) &= \pm i \sinh u, & \pm i \sin(\pi/2 \mp iu) &= \pm i \cosh u,
\end{aligned}
$$

we can restate the last two integral equation as follows: with $a = \pi/2$, for any $y \in \mathbb{C}$ with $-\pi/2 < \mathfrak{I}(y) < \pi/2$,

$$
\phi_{t,1}(x \mid 0) = \frac{16}{x^p}\, e^{-\frac{4}{x}} \int_{0}^{\infty} \mathfrak{R}\left( i\, e^{-i\frac{4}{x} \sinh u}\, \cosh u\, g_{t,p}(u - i\pi/2) \right)\mathrm{d}u, \qquad x > 0.
$$

<!-- page 24 -->

and

$$
2 \int_{-\infty}^{\infty} \mathfrak{R}\left( -i \cosh u \frac{g_{t,p}(u - i\pi/2)}{(-i \sinh u - \cosh y)^{p-1}} \right) du = \frac{(-4)^{p-2}}{(p-2)!} e^{-\frac{2y^2}{t}},
$$

and with $a = \pi$, for any $y \in \mathbb{C}$ with $-\pi < \mathfrak{I}(y) < \pi$,

$$
\phi_{t,1}(x \mid 0) = \frac{16}{x^p} e^{-\frac{4}{x}} \int_{0}^{\infty} \mathfrak{R}\left( e^{-\frac{4}{x} \cosh u} \sinh u \, g_{t,p}(u - i\pi) \right) du, \qquad x > 0,
$$

and

$$
2 \int_{-\infty}^{\infty} \mathfrak{R}\left( -\sinh u \frac{g_{t,p}(u - i\pi)}{(-\cosh u - \cosh y)^{p-1}} \right) du = \frac{(-4)^{p-2}}{(p-2)!} e^{-\frac{2y^2}{t}}.
$$

In order to justify the interchange of the integrations over the variables $x$ and $z$, on which the above calculations are based, it would be enough to check that the following conditions are in force:

$$
\int_{-\infty}^{\infty} \left| g_{t,p}(u - i\pi/2) \frac{\cosh u}{(-i \sinh u - \cosh y)^{p-1}} \right| du < \infty, \qquad -\pi/2 < \mathfrak{I}(y) < \pi/2
$$

and

$$
\int_{-\infty}^{\infty} \left| g_{t,p}(u - i\pi) \frac{\sinh u}{(-\cosh u - \cosh y)^{p-1}} \right| du < \infty, \qquad -\pi < \mathfrak{I}(y) < \pi.
$$

A straightforward calculation shows that

$$
\mathfrak{R}(i \sinh u + \cosh y) = \cos \mathfrak{I}(y) \cosh \mathfrak{R}(y) - \cosh \mathfrak{R}(u) \sin \mathfrak{I}(u).
$$

In particular, with $-\pi/2 < \mathfrak{I}(y) < \pi/2$, we have

$$
|-i \sinh u - \cosh y| \geq \cos \mathfrak{I}(y) \cosh \mathfrak{R}(y) > 0, \qquad \text{for any } u \in \mathbb{R}.
$$

Similarly,

$$
\mathfrak{R}(\cosh u + \cosh y) = \cos \mathfrak{I}(y) \cosh \mathfrak{R}(y) + \cos \mathfrak{I}(u) \cosh \mathfrak{R}(u),
$$

$$
\mathfrak{I}(\cosh u + \cosh y) = \sin \mathfrak{I}(y) \sinh \mathfrak{R}(y) + \sin \mathfrak{I}(u) \sinh \mathfrak{R}(u),
$$

so that one has for any $u \in \mathbb{R}$

$$
|\cosh u + \cosh y| = \sqrt{\sin^2 \mathfrak{I}(y) \sinh^2 \mathfrak{R}(y) + \bigl(\cos \mathfrak{I}(y) \cosh \mathfrak{R}(y) + \cosh u\bigr)^2}.
$$

If $\mathfrak{R}(y) \neq 0 \neq \mathfrak{I}(y)$, the above norm is bounded from below by

$$
|\sin \mathfrak{I}(y) \sinh \mathfrak{R}(y)| > 0.
$$

If $\mathfrak{I}(y) = 0$, the same norm is bounded from below by

$$
\sqrt{\bigl(\cosh \mathfrak{R}(y) + \cosh u\bigr)^2} \geq \cosh \mathfrak{R}(y) \geq 1,
$$

<!-- page 25 -->

and if $\mathfrak{R}(y) = 0$, with $-\pi < \mathfrak{I}(y) < \pi$ and $u \in \mathbb{R}$, we have

$$
|\cosh u + \cosh y| \geq \cosh u + \cos \mathfrak{I}(y) \geq 1 + \cos \mathfrak{I}(y) > 0.
$$

In any case, we can claim that with $-\pi < \mathfrak{I}(y) < \pi$, one has

$$
\inf_{u \in \mathbb{R}} |\cosh u + \cosh y| > 0.
$$

Therefore, it is enough to establish that

$$
\int_{-\infty}^{\infty} \left| g_{t,p}(u - i\pi/2) \cosh u \right| du < \infty
$$

and

$$
\int_{-\infty}^{\infty} \left| g_{t,p}(u - i\pi) \sinh u \right| du < \infty.
$$

To see why these estimates are indeed satisfied, first notice that the expressions $g_{t,p}(u - i\pi/2)$ and $g_{t,p}(u - i\pi)$ are both linear combinations of expressions of the form $\mathrm{erf}(c_1 u + i c_2)$ for various constants $c_1, c_2 \in \mathbb{R}$. Then notice that for every choice of $a, b \in \mathbb{R}$, one has

$$
\mathfrak{I}(\mathrm{erf}(a + ib)) = \frac{1}{2i}\bigl(\mathrm{erf}(a + ib) - \mathrm{erf}(a - ib)\bigr) = \frac{b e^{-a^2}}{\sqrt{\pi}} \int_{-1}^{1} e^{b^2 v} \cos(2abv) \, dv
$$

and

$$
\mathfrak{R}(\mathrm{erf}(a + ib)) = \frac{1}{2}\bigl(\mathrm{erf}(a + ib) - \mathrm{erf}(-a + ib)\bigr) = \frac{a e^{b^2}}{\sqrt{\pi}} \int_{-1}^{1} e^{-a^2 v} \cos(2abv) \, dv.
$$

These relations follow trivially from differentiating the functions $v \mapsto \mathrm{erf}(a + ibv)$ and $v \mapsto \mathrm{erf}(av + ib)$. Since the integrals

$$
\int_{-\infty}^{\infty} e^{-c_1^2 u^2} \cosh u \, du \quad \text{and} \quad \int_{-\infty}^{\infty} e^{-c_1^2 u^2} |\sinh u| \, du
$$

are finite, the exchange of the two integration operations is finally justified.

By using the conversion rule $\phi_{t,\sigma}(x \mid 0) = \sigma^2 \phi_{\sigma^2 t,1}(\sigma^2 x \mid 0)$ and the relation (4.6), we obtain the general formulae ($x \in \mathbb{R}$)

$$
\phi_{t,\sigma}(x \mid y) = \frac{16}{\sigma^{2p-2} x^p}\, e^{\frac{1}{2}\sigma y(p-1) + \frac{y^2}{2t} - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} \cosh u \, \mathfrak{R}\!\left(i\, e^{-i \frac{4}{\sigma^2 x} e^{\sigma y/2} \sinh u}\, g_{\sigma^2 t,p}(u - i\pi/2)\right) du, \tag{5.9a}
$$

$$
\phi_{t,\sigma}(x \mid y) = \frac{16}{\sigma^{2p-2} x^p}\, e^{\frac{1}{2}\sigma y(p-1) + \frac{y^2}{2t} - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} \sinh u \, \mathfrak{R}\!\left(e^{-\frac{4}{\sigma^2 x} e^{\sigma y/2} \cosh u}\, g_{\sigma^2 t,p}(u - i\pi)\right) du. \tag{5.9b}
$$

<!-- page 26 -->

which are equivalent to the formulae, for the unconditional joint density,

$$
\phi_{t,\sigma}(x, y) = \frac{16}{\sigma^{2p-2} x^p \sqrt{2\pi t}}\, e^{\frac{1}{2}\sigma y(p-1) - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} \cosh u \, \mathfrak{R}\!\left(i\, e^{-i \frac{4}{\sigma^2 x} e^{\sigma y/2} \sinh u}\, g_{\sigma^2 t,p}(u - i\pi/2)\right) du, \tag{5.10a}
$$

$$
\phi_{t,\sigma}(x, y) = \frac{16}{\sigma^{2p-2} x^p \sqrt{2\pi t}}\, e^{\frac{1}{2}\sigma y(p-1) - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} \sinh u \, \mathfrak{R}\!\left(e^{-\frac{4}{\sigma^2 x} e^{\sigma y/2} \cosh u}\, g_{\sigma^2 t,p}(u - i\pi)\right) du. \tag{5.10b}
$$

We shall refer to (5.10a) as “the $\frac{\pi}{2}$-formula of order $p$” and to (5.10b) as “the $\pi$-formula of order $p$.” With $p = 2$, we have

$$
g_{\sigma^2 t,2}\!\left(u - i\frac{\pi}{2}\right) = \frac{1}{4\pi i}\, e^{-2\frac{(u - i\pi/2)^2}{\sigma^2 t}} = \frac{1}{4\pi}\, e^{\frac{\pi^2}{2\sigma^2 t} - \frac{2u^2}{\sigma^2 t}}\left(\sin\frac{2\pi u}{\sigma^2 t} - i\cos\frac{2\pi u}{\sigma^2 t}\right),
$$

and

$$
g_{\sigma^2 t,2}(u - i\pi) = \frac{1}{4\pi i}\, e^{-2\frac{(u - i\pi)^2}{\sigma^2 t}} = \frac{1}{4\pi}\, e^{\frac{2\pi^2 - 2u^2}{\sigma^2 t}}\left(\sin\frac{4\pi u}{\sigma^2 t} - i\cos\frac{4\pi u}{\sigma^2 t}\right).
$$

As a result, (5.9a) and (5.9b) specialize to

$$
\phi_{t,\sigma}(x \mid y) = \frac{4\, e^{\frac{\pi^2}{2\sigma^2 t}}}{\sigma^2 x^2 \pi}\, e^{\frac{\sigma y}{2} + \frac{y^2}{2t} - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} e^{-\frac{2u^2}{\sigma^2 t}} \cosh u \cos\!\left(\frac{4\sinh u\, e^{\sigma y/2}}{\sigma^2 x} - \frac{2\pi u}{\sigma^2 t}\right) du
$$

and

$$
\phi_{t,\sigma}(x \mid y) = \frac{4\, e^{\frac{2\pi^2}{\sigma^2 t}}}{\sigma^2 x^2 \pi}\, e^{\frac{\sigma y}{2} + \frac{y^2}{2t} - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} e^{-\frac{2u^2}{\sigma^2 t} - \frac{4\cosh u}{\sigma^2 x} e^{\sigma y/2}}\, \sinh u \sin\frac{4\pi u}{\sigma^2 t}\, du,
$$

while (5.10a) and (5.10b) specialize to

$$
\phi_{t,\sigma}(x, y) = \frac{4\, e^{\frac{\pi^2}{2\sigma^2 t}}}{\sigma^2 x^2 \pi \sqrt{2\pi t}}\, e^{\frac{\sigma y}{2} - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} e^{-\frac{2u^2}{\sigma^2 t}} \cosh u \cos\!\left(\frac{4\sinh u\, e^{\sigma y/2}}{\sigma^2 x} - \frac{2\pi u}{\sigma^2 t}\right) du
$$

<!-- page 27 -->

and

$$
\phi_{t,\sigma}(x, y) = \frac{4\, e^{\frac{2\pi^2}{\sigma^2 t}}}{\sigma^2 x^2 \pi \sqrt{2\pi t}}\, e^{\frac{\sigma y}{2} - \frac{2}{\sigma^2 x}(e^{\sigma y} + 1)} \times \int_0^{\infty} e^{-\frac{2u^2}{\sigma^2 t}}\, e^{-\frac{4\cosh u}{\sigma^2 x} e^{\sigma y/2}}\, \sinh u \sin\frac{4\pi u}{\sigma^2 t}\, du.
$$

**Remark 5.1** With $\sigma = 2$, the last formula, i.e., the $\pi$-formula of order 2, reads

$$
\phi_{t,2}(x, y) = \frac{e^{\frac{\pi^2}{2t}}}{x^2 \pi \sqrt{2\pi t}}\, e^{y - \frac{1}{2x}(e^{2y} + 1)} \int_0^{\infty} e^{-\frac{u^2}{2t}}\, e^{-\frac{\cosh u}{x} e^y}\, \sinh u \sin\frac{\pi u}{t}\, du,
$$

and this is precisely Yor's formula [33, (6.c)]—see (1.1) above.

**Remark 5.2** It is easy to see why from a computational point of view, the $\frac{\pi}{2}$-formula may be preferable to the $\pi$-formula: The expression $e^{-\frac{4}{\sigma^2 x} e^{\sigma y/2} \cosh u}$ in the $\pi$-formula involves double exponentials, whereas in the $\frac{\pi}{2}$-formula, this expression is replaced with the bounded term $\cos(\cdots)$. These differences are manifested in the numerical evaluation of $\int_0^{\infty} \phi_{t,2}(x \mid 0)\, dx$, which comes down to the computation of a double integral of the form $\int_0^{\infty} du \int_0^{\infty} dx\,(\cdots)$. In either case, the double integral converges and Sage/Maxima can compute the inner integral in closed form as an explicit function of $u$. This function, which is considerably simpler in the case of the $\pi$-formula, can only be integrated numerically and only on a finite interval. In the case of the $\pi$-formula, the widely used QUADPACK package from Maxima (via Sage), with the default working precision, fails to compute $\int_0^a du$ with $a \ge 720$, and for smaller values of $a$, say $a = 710$, returns a number close to $1.0$ with error of order $10^{-8}$ (and with the report of an ‘excessive roundoff error’ throughout the integration). In the case of the $\pi/2$-formula, however, QUADPACK can compute $\int_0^a du$ with $a$ as large as $a = 5000$ and returns $1.0$ with error of order $10^{-13}$. When using numerical integration based on the fast GSL C-library (via Sage), in some sense the opposite is observed: In the case of the $\pi$-formula, $\int_0^a du$ evaluates to $1.0$ with error of order $10^{-7}$ for $a \approx 700$, while in the case of the $\frac{\pi}{2}$-formula, $\int_0^a du$ evaluates to $1.0$ with error of order $10^{-12}$ but only for $a \le 10$.$^{11}$ Overall, at least in the context of the computation described here, the $\frac{\pi}{2}$-formula appears to provide 5 additional digits of precision essentially for free.

**Remark 5.3** Above, we computed $\int_0^{\infty} \phi_{t,2}(x \mid 0)\, dx$ for the purpose of benchmarking, but nothing would have changed if we were to compute $\int_a^{\infty} \phi_{t,\sigma}(x \mid y)\, dx$ for some fixed $a > 0$; we again end up with a double integral $\int_0^{\infty} du \int_a^{\infty} dx\,(\cdots)$, and the inner integral is again computable in closed form in terms of special functions. In fact, from the point of view of machine precision arithmetic, the computation of

$^{11}$ Generally, the GSL C-library is much faster, but in all experiments described here, both methods return the results practically in an instant.

<!-- page 28 -->

$\int_a^{\infty} \phi_{t,\sigma}(x \mid y)\,dx$ would be easier, because the numerical procedure must deal only with the thinness of the distribution at $\infty$, as opposed to thinness at both $\infty$ and $0$. We stress that—and the numerical examples discussed in the previous remark are a perfect illustration—there would be no need in principle to develop integral formulae of order higher that $p=2$ if one is only interested in computing probabilities (say, the probability for an Asian option to be in the money). The problem occurs when computing expected values that involve $\int_a^{\infty} x\,\phi_{t,\sigma}(x \mid y)\,dx$, because the integral in $x$ would not converge for fixed $u$ unless $p \ge 3$, and the double integral can be computed only by carrying out the integration in the variable $u$ first.

**Remark 5.4** Another—and perhaps even more important—advantage of the $\frac{\pi}{2}$-formula is that it still allows the real part $\mathfrak{R}(\cdots)$ in (5.10a) to be expressed in closed form, i.e., without the use of the function $\mathfrak{R}(\cdot)$, not just for $p=2$, but also for $p>2$. This is important because many of the commonly used quadrature packages are only meant to work with functions that evaluate to real floats. For this reason, and also for the reasons noted in the previous remark, in what follows we are going to be concerned only with applications of the $\frac{\pi}{2}$-formula, but note that applications of the $\pi$-formula may be developed in a completely analogous fashion.

**Remark 5.5** As an aside, the $\pi$-formula for the conditional density $\phi_{t,\sigma}(x \mid y)$ leads to the following curious identity, which sheds some light on the nature of the integral representations obtained above: for all $z \in \mathbb{C} \setminus (-\infty,1)$, one has

$$
\frac{1}{\pi}\,e^{\frac{2\pi^2}{t}}\int_1^\infty \frac{e^{-\frac{2}{t}\operatorname{arcosh}^2 u}}{u+z}\,\sin\!\left(\frac{4\pi}{t}\operatorname{arcosh} u\right)\,du = e^{-\frac{2}{t}\operatorname{arcosh}^2 z}.
$$

To see where this identity may be coming from, first observe that with a simple change of the integration variable, the $\pi$-formula can be rewritten as

$$
\phi_{t,1}(x \mid 0)=\frac{e^{2\pi^2/t}}{\pi}\int_8^\infty \frac{1}{x^2}\,e^{-\frac{u}{x}}\,e^{-\frac{2}{t}\operatorname{arcosh}^2\frac{u-4}{4}}\,\sin\!\left(\frac{4\pi}{t}\operatorname{arcosh}\frac{u-4}{4}\right)\,du.
$$

Substituting the above expression in the equation (see (5.1))

$$
\int_0^\infty \phi_{t,1}(x \mid 0)\,e^{-\frac{4\cosh y-4}{x}}\,dx = e^{-\frac{2y^2}{t}},\quad y\in\mathbb{C},\ -\pi<\mathfrak{I}(y)<\pi,
$$

carrying out the integration in $x$, which leads to a closed-form expression as a function of $u$, and finally substituting $y=\operatorname{arcosh} z$ gives the result. $\square$

## 6 Computation of expected values and applications to Asian options

Because the initial motivation for the present study was to achieve greater computational tractability, our exposition would not be complete without concrete examples to illustrate the applicability of the new formulae we have developed. As

<!-- page 29 -->

the most widely discussed concrete examples documented throughout the literature (related to the distribution of the integral of exponential Brownian motion) involve the pricing of Asian options, this will be the nature of our illustrations also. However, we emphasize very strongly that the essence of our approach is to carry out calculations by using the density of the distribution directly, and in this respect our method can be seen as universal, in the sense that the concrete representations for the density that we obtain are not related to Asian options in any way.

The numerical evaluation of the prices of Asian options has a long history and can be traced back at least as far as Turnbull and Wakeman [28]. The next step was due to Eydeland and Geman [14], who used a particular algorithm for inverting the Laplace transform (in the time variable) which was computed by Geman and Yor [15]. Another widely used approach to Asian options is to establish lower and upper bounds for the price. This method was pioneered by Rogers and Shi [26], and we refer to the recent work of Kordzakhia and Novikov [18] for a unified and expanded framework as well as an up-to-date overview of this approach and the related literature. Generically, the upper/lower bound technique can give the price of the Asian option with 3 decimal places of accuracy. Other computational methods, specifically designed for Asian options, have been developed by Dufresne [12, 13], Milevsky and Posner [24], Thompson [27], Linetsky [19], Večeř [29, 30] and others. Among these works, Linetsky's provides the most accurate results, achieving 10 decimal places of accuracy. Since his numerical examples are benchmarked against those of his predecessors, we use in this section his parameter values (in all 7 cases from [19, Table 1]) as a benchmark test, but include 24 new cases at the end. We stress, however, that the methodology developed in the present paper is not specific to Asian options.

Now we turn to the computation of expected values of the form

$$
\mathbb{E}\left[f\left(\int_0^t e^{\sigma W_s + \mu s}\,\mathrm{d}s\right)\right],
$$

which was our main motivation for developing integral representations for $\phi_{t,\sigma}(x \mid y)$ or, equivalently, for $\phi_{t,\sigma}(x,y)$. As we are already well aware, an integral formula of order $p=2$ would be inadequate for computing conditional expectations of the form

$$
\mathbb{E}\left[f\left(\int_0^t e^{\sigma W_s}\,\mathrm{d}s\right) \,\Big|\, W_t = y\right] = \int_0^\infty f(x)\,\phi_{t,\sigma}(x \mid y)\,\mathrm{d}x
$$

for functions $\mathbb{R}_+ \ni x \mapsto f(x)$ that are linear at $\infty$ (for example, $f(x)=x$ or $f(x)=(x-K)^+$), as the integral on the right would become a double integral that exists only as an iterated integral, but not as an integral on the domain $\mathbb{R}_+\times\mathbb{R}_+$. Integral formulae of order $p=3$ are still inadequate because the integration of the above expression against the density $\frac{1}{\sqrt{2\pi t}} e^{-\frac{y^2}{2t}}\,\mathrm{d}y$ leads to triple integrals that still exist only as iterated integrals.$^{12}$

$^{12}$ With $p=3$ and $f(x)=x$ or $f(x)=(x-K)^+$, the integration with respect to $x$ can be closed, but the integration with respect to the remaining variables $u$ and $y$ can only be carried out as an iterated double integral (in this order).

<!-- page 30 -->

In what follows, we illustrate with concrete examples the use of the $\frac{\pi}{2}$-formula of order $p=4$ in the calculation of the price of certain Asian options, i.e., in the calculation of integrals of the form

$$
\int_{-\infty}^{\infty} dy \int_{k}^{\infty} (x-k)\,\phi_{t,\sigma,\mu}(x,y)\,dx, \qquad k \geq 0,
$$

where (see (2.2))

$$
\phi_{t,\sigma,\mu}(x,y) = e^{\frac{\mu}{\sigma}y + \frac{1}{2}\frac{\mu^{2}}{\sigma^{2}}t}\,\phi_{t,\sigma,0}\!\left(x,\, y + \frac{\mu}{\sigma}t\right)
$$

and $\phi_{t,\sigma,0}(\cdot,\cdot) =: \phi_{t,\sigma}(\cdot,\cdot)$ is given by (5.10a) with $p=4$. The calculation then boils down to the computation of a triple integral in the variables $x$, $y$ and $u$. Since we are using the $\frac{\pi}{2}$-formula of order $p=4$, the integrand in the triple integral is summable and we can choose the order of integration in any way that we find useful—recall that $p=4$ is the lowest power for which this property holds. In particular, if the variable $x$ is integrated out first, the corresponding integral can be computed in closed form and we are left with a double integral in the variables $y$ and $u$, which can be computed only numerically. Since the exact value of this integral for $k=0$ is known, we can use the case $k=0$ as a benchmark for the accuracy of the double quadrature that will be used.

Our first step in this program is to transform the above integral into

$$
\int_{0}^{\infty} dw \int_{k}^{\infty} (x-k)\,\frac{2}{\sigma w}\,\phi_{t,\sigma,\mu}\!\left(x,\, \frac{2\log w}{\sigma}\right) dx.
$$

Expanding the density $\phi_{t,\sigma,\mu}$ according to the $\frac{\pi}{2}$-formula of order $p=4$, the above integral becomes

$$
\Re\!\left(\int_{0}^{\infty} dw \int_{0}^{\infty} du\, B(w)\, C(u,w)\, g_{\sigma^2 t,\,4}\!\left(u - i\frac{\pi}{2}\right) \int_{k}^{\infty} \frac{x-k}{x^{4}}\, e^{-A(u,w)/x}\, dx\right),
$$

where the function $g_{t,4}(\cdot)$ is given by (5.8) and

$$
A(u,w) := \frac{2w^{2}e^{\mu t} + 4iw\, e^{\frac{1}{2}\mu t}\sinh u + 2}{\sigma^{2}},
$$

$$
B(w) := \frac{2w^{\frac{2\mu}{\sigma^{2}}-1}\, e^{\frac{\mu^{2}t}{2\sigma^{2}}}}{\sigma},
$$

$$
C(u,w) := \frac{8i\sqrt{2}\,\sigma^{-2p+2}\, w^{p-1}\cosh u\, e^{\frac{1}{2}\mu p t - \frac{1}{2}\mu t}}{\sqrt{\pi t}}.
$$

The innermost integral can be computed in closed form: For any integer $p \geq 3$ and quantity $A \in \mathbb{C}$ with $\Re(A) > 0$, which is independent from $x$, one can write

<!-- page 31 -->

$$
S_{k,p}(u, w) := \int_k^\infty e^{-\frac{A}{x}} \frac{x - k}{x^p}\,dx
$$
$$
= \int_k^\infty e^{-\frac{A}{x}} \frac{1}{x^{p-1}}\,dx - k \int_k^\infty e^{-\frac{A}{x}} \frac{1}{x^p}\,dx
$$
$$
= \int_0^{\frac{1}{k}} e^{-Av}\,v^{p-3}\,dv - k \int_0^{\frac{1}{k}} e^{-Av}\,v^{p-2}\,dv
$$
$$
= kA^{-(p-1)}\Gamma\!\left(p - 1, \frac{A}{k}\right) - A^{-(p-2)}\Gamma\!\left(p - 2, \frac{A}{k}\right)
$$
$$
\qquad - kA^{-(p-1)}\Gamma(p - 1) + A^{-(p-2)}\Gamma(p - 2),
$$

with the understanding that for $k = 0$, one has
$$
S_{0,p}(u, w) := \int_0^\infty e^{-\frac{A}{x}} \frac{1}{x^{p-1}}\,dx = A^{-(p-2)}\Gamma(p - 2).
$$

If $k$ depends on a parameter $\alpha$, i.e., $k = k(\alpha)$, then
$$
S'_{k(\alpha),p}(u, w) := \partial_\alpha\bigl(S_{k(\alpha),p}(u, w)\bigr) = -k'(\alpha) \int_{k(\alpha)}^\infty e^{-\frac{A}{x}} \frac{1}{x^p}\,dx
$$
$$
= -k'(\alpha) \int_0^{\frac{1}{k}} e^{-Av}\,v^{p-2}\,dv
$$
$$
= k'(\alpha)A^{-(p-1)}\Gamma\!\left(p - 1, \frac{A}{k}\right) - k'(\alpha)A^{-(p-1)}\Gamma(p - 1).
$$

The complex-valued functions
$$
(u, w) \mapsto F_{t,\sigma,\mu,k}(u, w) := B(w)\,C(u, w)\,g_{\sigma^2 t,\,4}\!\left(u - i\frac{\pi}{2}\right) S_{k,4}(u, w),
$$
$$
(u, w) \mapsto F'_{t,\sigma,\mu,k(\alpha)}(u, w) := B(w)\,C(u, w)\,g_{\sigma^2 t,\,4}\!\left(u - i\frac{\pi}{2}\right) S'_{k(\alpha),4}(u, w)
$$
can be integrated numerically in the domain $\mathbb{R}_+ \times \mathbb{R}_+$, and we are only interested in the real part of the result. Some of the widely used (and highly efficient) numerical integration packages will not accept functions that do not evaluate to real floats—`numerical_integral` and `nintegral` in Sage are in this category.$^{13}$ However, the symbolic platform in Sage is capable of segregating the real and imaginary parts of the above functions in symbolic form (one of the advantages of the $\frac{\pi}{2}$-formula), providing closed-form expressions in terms of special functions for $\Re\bigl(F_{t,\sigma,\mu,k}(u, w)\bigr)$ and $\Im\bigl(F_{t,\sigma,\mu,k}(u, w)\bigr)$. The integrals
$$
\int_0^\infty \int_0^\infty \Re\bigl(F_{t,\sigma,\mu,k}(u, w)\bigr)\,du\,dw, \quad \int_0^\infty \int_0^\infty \Re\bigl(F'_{t,\sigma,\mu,k(\alpha)}(u, w)\bigr)\,du\,dw \tag{6.1}
$$

$^{13}$ The first function uses the GSL C-library, while the second one uses the QUADPACK package.

<!-- page 32 -->

can then be computed rather efficiently by iterating `nintegral` in $u$, followed by `numerical_integral` in $w$. Unfortunately, this technique works only for relatively large values for $\sigma$ and $t$, and not quite with the accuracy that one might desire. By way of an example, with $t = 1$, $\sigma = 1$, $\mu = 0$, and $k = 0$, the first integral above gives the exact value of $\mathbb{E}\bigl[\int_0^1 e^{W_s}\,\mathrm{d}s\bigr]$ only with accuracy of order $\approx 10^{-8}$.

In order to obtain practically meaningful results—or any results at all—for more realistic values for $\sigma$ and $t$, the numerical integration must be executed with higher working precision than the standard machine precision. One package that allows such operations is mpmath (`mp`). Specifically, the function `mp.quad` can perform both single and double quadratures with arbitrary precision. In addition, `mp.quad` can integrate numerically complex-valued functions, and generally, the numerical integration with `mp.quad` of the complex functions $(u, w) \mapsto F_{t,\sigma,\mu,k}(u, w)$ and $(u, w) \mapsto F'_{t,\sigma,\mu,k(\alpha)}(u, w)$ is considerably more efficient than the numerical integration of their real parts, expressed in terms of special functions.$^{14}$

**Remark 6.1** The numerical integration described in this section is not specific to Asian options and can be applied to more general integrals of the form
$$
\int_0^\infty \mathrm{d}w \int_0^\infty \mathrm{d}u\, B(w)\, C(u, w)\, g_{\sigma^2 t,\,4}\!\left(u - i\frac{\pi}{2}\right) \int_0^\infty \frac{f(x)}{x^4}\, e^{-\frac{1}{x}A(u,w)}\,\mathrm{d}x
$$
for reasonably behaved functions $x \mapsto f(x)$—say for smooth $f$ that are at most linear at $0$ and $\infty$. The only simplification that comes from the Asian call structure is due to the fact that the integration in the variable $x$ can be closed, which then reduces the triple integral to a double integral. Because of the similarity between these integrals for various choices of the function $f$, and because the main obstacle in the numerical integration is in the shape of the density for smaller values for $\sigma$ and $t$, we can benchmark our choice of numerical integration strategy (i.e., the choice of method, working precision and domain of integration) by comparing the result for $k = 0$ with the exact value
$$
\mathbb{E}\left[\int_0^t e^{\sigma W_s + \mu s}\,\mathrm{d}s\right] = \frac{2\left(e^{\frac{1}{2}\sigma^2 t + \mu t} - 1\right)}{\sigma^2 + 2\mu}.
$$

In general, using $k = 0$ as a benchmark in the design of an integration strategy for a particular choice for $\sigma$, $t$ and $\mu$ is useful because with $k = 0$, the procedure is forced to deal with the thinness of the density at both $0$ and $\infty$, whereas with $k > 0$, the first challenge goes away. Thus, it is reasonable to assume that the numerical integration with $k > 0$ would be at least as precise as with $k = 0$.

Now we turn to some concrete examples from the realm of Asian call options. Consider the canonical complete market model (as in Linetsky [19] and others) that consists of a risky security $S_t$, $t \geq 0$, and a risk-free security that generates a constant rate of return $r > 0$; specifically, under the pricing (risk-neutral) measure $\mathbb{Q}$,

$^{14}$ One possible explanation for this phenomenon is that the closed-form expression for $\Re\bigl(F_{t,\sigma,\mu,k}(u, w)\bigr)$ is quite long and requires a substantially larger number of evaluations.

<!-- page 33 -->

the dynamics of $(S_t)$ are given by $dS_t = \sigma S_t\,dW_t + r S_t\,dt$, where $W_t$, $t \geq 0$, is a $\mathbb{Q}$-Brownian motion. The price at time $t = 0$ of an Asian (average) call option with strike price $K > 0$ and maturity date $T > 0$ is

$$
\begin{aligned}
&e^{-rT}\mathbb{E}^{\mathbb{Q}}\left[\left(\frac{1}{T}S_0\int_0^T e^{\sigma W_s + (r-\frac{1}{2}\sigma^2)s}\,ds - K\right)^+\right] \\
&= e^{-rT}\frac{S_0}{T}\mathbb{E}^{\mathbb{Q}}\left[\left(\int_0^T e^{\sigma W_s + (r-\frac{1}{2}\sigma^2)s}\,ds - \frac{KT}{S_0}\right)^+\right] \\
&= e^{-rT}\frac{S_0}{T}\int_0^\infty\int_0^\infty \Re\bigl(F_{t,\sigma,\mu,k}(u,w)\bigr)\,du\,dw
\end{aligned}
$$

with $\mu = r - \frac{1}{2}\sigma^2$ and $k = \frac{KT}{S_0}$. If one is interested in computing the sensitivity of the call option to the spot price $S_0$ (the so-called “delta” of the option), then one must compute two such integrals, namely

$$
\begin{aligned}
&\frac{e^{-rT}}{T}\int_0^\infty\int_0^\infty \Re\bigl(F_{t,\sigma,\mu,k}(u,w)\bigr)\,du\,dw \\
&\quad - e^{-rT}\frac{K}{S_0}\int_0^\infty\int_0^\infty \Re\bigl(F'_{t,\sigma,\mu,k}(u,w)\bigr)\,du\,dw. \tag{6.2}
\end{aligned}
$$

First, we compare the results from the numerical integration described above in each of the 7 cases from [19, Table 1]. Cases 4 through 6 involve $T = 1$, $\sigma = 1/2$ and $r = 5/100$, for 3 different choices for $S_0$, which is tantamount to 3 different choices of the strike price $K$. With these values, the integration strategy based on double quadratures using `mp.quad` in the domain $(u,w) \in [0,20] \times [0,20]$, with working precision set to `mp.dps` = 30, produces the exact value for $K = 0$ with error $\leq 10^{-25}$. The same integration strategy produces values for each of the Asian call options in cases 4 through 6 which, after being rounded to the 10th decimal place, exactly match the corresponding values from [19, Table 3]. Similarly, case 7 involves $T = 2$, $\sigma = 1/2$ and $r = 5/100$. Using the same integration strategy gives the exact value for $K = 0$ with error $\leq 10^{-14}$, and produces a value for the Asian call option in case 7 which, after rounding to the 10th decimal place, again coincides with the value reported in [19, Table 3]. The same claim can be made for case 3 ($T = 2$, $\sigma = 1/4$ and $r = 1/80$), except that the exact value for $K = 0$ is produced with error $\leq 10^{-17}$.

Cases 1 and 2 from [19, Table 1] are more involved and require a different integration strategy. In both cases $T = 1$ and the volatility $\sigma$ is set to, respectively, $1/10$ and $3/10$. This combination of volatility values and life-time of the option requires higher working precision than `mp.dps` = 30, which makes the double quadrature using `mp.quad` excessively slow. The following alternative strategy can then be used. For a discrete set of abscissas $w_i \in \mathbb{R}_+$, $0 \leq i \leq n$, and for a sufficiently large $a > 0$, compute numerically the values

$$
b_i = \int_0^a \Re\bigl(F_{T,\sigma,\mu,k}(u,w_i)\bigr)\,du, \quad 0 \leq i \leq n,
$$
<｜tool▁call▁end｜><｜tool▁calls▁end｜>

<!-- page 34 -->

**Table 1** $T = 1/2$, $\sigma = 22/100$; strategy: `mp.dps` $= 120$, $n = 45$, $w_0 = 10^{-65}$, $w_n = 2$, $a = 2$; error for $K = 0$ is $\leq 10^{-15}$; Asian call with strike $K$

| Strike $K$ | Asian call price |
| :--- | :--- |
| $7/10$ | $0.302471713826246$ |
| $8/10$ | $0.203823272652937$ |
| $9/10$ | $0.109134667336200$ |
| $1$ | $0.038694821814008$ |
| $11/10$ | $0.008127776133751$ |
| $12/10$ | $0.001028464610034$ |

**Table 2** $T = 1/2$, $\sigma = 1/3$; strategy: `mp.dps` $= 60$, $n = 65$, $w_0 = 1/4$, $w_n = 15/4$, $a = 20$; error for $K = 0$ is $\leq 10^{-11}$; Asian call with strike $K$

| Strike $K$ | Asian call price |
| :--- | :--- |
| $7/10$ | $0.30256324113$ |
| $8/10$ | $0.20574087443$ |
| $9/10$ | $0.11939786084$ |
| $1$ | $0.05691875027$ |
| $11/10$ | $0.02222765943$ |
| $12/10$ | $0.00727337085$ |

by using single quadrature with `mp.quad` and an appropriate value for the working precision parameter `mp.dps`. Then construct a natural spline from the tabulated values $(w_i, b_i)$, $0 \leq i \leq n$, and finally calculate exactly, i.e., with the designated working precision, the integral of this spline over the interpolation domain $[w_0, w_n]$. One remarkable advantage of this strategy is that it is easily parallelizable. Fortunately, in the present context, the nature of the function

$$
\mathbb{R}_+ \ni w \mapsto \int_0^a \Re\bigl(F_{T,\sigma,\mu,k}(u,w)\bigr)\,du \in \mathbb{R}
$$

is such that this function can be approximated rather efficiently with natural splines over an appropriate finite domain. In case 2 from [19, Table 1], following the spline quadrature strategy with `mp.dps` $= 45$, $a = 20$, $n = 100$, $w_0 = 1/8$ and $w_n = 5$ gives the exact value for $K = 0$ with error $\leq 10^{-13}$ and again produces a value for the Asian option which, after rounding to the 10th decimal place, becomes identical to the value reported in [19, Table 3]. The same exact claim can also be made for case 1 ($T = 1$ and $\sigma = 1/10$), except that one must set the working precision as high as `mp.dps` $= 300$, and use interpolation with $n = 35$, $w_0 = 1/2$ and $w_n = 16/10$ (the exact value for $K = 0$ is again obtained with error $\leq 10^{-13}$).

We now conclude the paper with yet another set of examples, which were chosen to be somewhat more realistic. In all cases, the numerical integration strategy is based on interpolation quadratures, as describe above. The initial price is scaled to $S_0 = 1$, and the interest rate is fixed to $r = 5/200 = 2.5\%$. The values of all Asian call options are computed for time $t = 0$ and are reported in Tables 1–4.

All calculations reported above are done with a single Sage process from a Linux virtual box on a Surface tablet with 2 GB of RAM (dedicated to Linux) and a 64-bit

<!-- page 35 -->

**Table 3** $T = 1$, $\sigma = 22/100$; strategy: `mp.dps` $= 60$, $n = 65$, $w_0 = 1/8$, $w_n = 28/8$, $a = 20$; error for $K = 0$ is $\leq 10^{-12}$; Asian call with strike $K$

| Strike $K$ | Asian call price |
| :--- | :--- |
| $7/10$ | $0.304923087645$ |
| $8/10$ | $0.208572293433$ |
| $9/10$ | $0.120806302805$ |
| $1$ | $0.056156816264$ |
| $11/10$ | $0.020689114929$ |
| $12/10$ | $0.006174095598$ |

**Table 4** $T = 1$, $\sigma = 1/3$; strategy: `mp.dps` $= 45$, $n = 100$, $w_0 = 1/4$, $w_n = 5$, $a = 20$; error for $K = 0$ is $\leq 10^{-11}$; Asian call with strike $K$

| Strike $K$ | Asian call price |
| :--- | :--- |
| $7/10$ | $0.30620859092$ |
| $8/10$ | $0.21565075810$ |
| $9/10$ | $0.13878233268$ |
| $1$ | $0.08160208509$ |
| $11/10$ | $0.04425815874$ |
| $12/10$ | $0.02244768617$ |

2.50 GHz processor. The computing times (for a single call option) are heavily dependent on the working precision, and vary between roughly 30 min (`mp.dps` $= 30$) and 60 min (`mp.dps` $= 120$), but increase to as much as 7 h with `mp.dps` $= 300$. As was already noted, the computing times scale almost exactly to the number of processors used, since the procedure involves the calculation of a finite number of univariate integrals in a single pass (the sub-kernels need to communicate only once, and the integration of the resulting spline is essentially instantaneous). Finally, we note that—see (6.2)—the calculation of the delta of the option involves twice the amount of work needed for the calculation of the option price (unless the option price is already computed). Since up to a factor, the function $F'$ comprises the first and the third terms in the function $F$, the calculation of the second integral in (6.1) can be accomplished by using the same integration strategy with which the first integral is computed; but typically—see Remark 5.3—, the calculation of $F'$ is considerably less demanding and in most cases can be accomplished with the native precision.

**Acknowledgements**

The author is greatly indebted to two exceptionally conscientious and constructive anonymous referees, and also to Catherine Donati-Martin, Helyette Geman, Yannis Karatzas, Alex Novikov, Hiroyuki Matsumoto, and especially to Marc Yor, for their interest in the present work and for many helpful comments.

**References**

1. Alili, L., Dufresne, D., Yor, M.: Sur l'identité de Bougerol pour les fonctionnelles exponentielles du mouvement brownien avec drift. In: Yor, M. (ed.) Exponential Functionals and Principal Values Related to Brownian Motion. A Collection of Research Papers, pp. 3–14. Biblioteca de la Revista Matemática Ibero-Americana, Madrid (1997)

2. Baudoin, F., O'Connell, N.: Exponential functionals of Brownian motion and class-one Whittaker functions. Ann. Inst. Henri Poincaré B, Calc. Probab. Stat. **47**, 1096–1120 (2011)

<!-- page 36 -->

3. Bertoin, J., Yor, M.: Exponential functionals of Lévy processes. Probab. Surv. 2, 191–212 (2005)

4. Carmona, P., Petit, F., Yor, M.: On the distribution and asymptotic results for exponential functionals of Lévy processes. In: Yor, M. (ed.) Exponential Functionals and Principal Values Related to Brownian Motion. A Collection of Research Papers, pp. 73–130. Biblioteca de la Revista Matemática IberoAmericana, Madrid (1997)

5. Chamayou, J., Letac, G.: Explicit stationary distributions for compositions of random functions and products of random matrices. J. Theor. Probab. 4, 3–36 (1991)

6. Chaumont, L., Hobson, D.G., Yor, M.: Some consequences of the cyclic exchangeability property for exponential functionals of Lévy processes. In: Azéma, J., et al. (eds.) Séminaire de Probabilités de Strasbourg 35. Lecture Notes in Mathematics, vol. 1755, pp. 334–347 (2001)

7. Comtet, A., Monthus, C., Yor, M.: Exponential functionals of Brownian motion and disordered systems. J. Appl. Probab. 35, 255–271 (1998)

8. Donati-Martin, C., Matsumoto, H., Yor, M.: On striking identities about the exponential functionals of the Brownian bridge and Brownian motion. Period. Math. Hung. 41, 103–119 (2000)

9. Donati-Martin, C., Matsumoto, H., Yor, M.: On positive and negative moments of the integral of geometric Brownian motions. Stat. Probab. Lett. 49, 45–52 (2000)

10. Dufresne, D.: Weak convergence of random growth processes with applications to insurance. Insur. Math. Econ. 8, 187–201 (1989)

11. Dufresne, D.: The distribution of a perpetuity with application to risk theory and pension funding. Scand. Actuar. J. 90, 39–79 (1990)

12. Dufresne, D.: Laguerre series for Asian and other options. Math. Finance 10, 407–428 (2000)

13. Dufresne, D.: The integral of geometric Brownian motion. Adv. Appl. Probab. 33, 223–241 (2001)

14. Eydeland, A., Geman, H.: Domino effect: Inverting the Laplace transform. Risk 8, 65–67 (1995)

15. Geman, H., Yor, M.: Bessel process, Asian options and perpetuities. Math. Finance 3, 349–375 (1993)

16. Getoor, R.K.: The Brownian escape process. Ann. Probab. 7, 864–867 (1979)

17. Hobson, D.G.: A short proof of an identity for a Brownian bridge due to Donati-Martin, Matsumoto and Yor. Stat. Probab. Lett. 77, 148–150 (2007)

18. Kordzakhia, N., Novikov, A.: On lower and upper bounds for Asian-type options: A unified approach (2013). Preprint, available online at: arXiv:1309.2383

19. Linetsky, V.: Spectral expansions for Asian (average price) options. Oper. Res. 52, 856–867 (2004)

20. Matsumoto, H., Yor, M.: An analogue of Pitman’s $2M - X$ theorem for exponential Wiener functionals, Part I: A time-inversion approach. Nagoya Math. J. 159, 125–166 (2000)

21. Matsumoto, H., Yor, M.: An analogue of Pitman’s $2M - X$ theorem for exponential Wiener functionals, Part II: The role of the generalized inverse Gaussian laws. Nagoya Math. J. 162, 65–86 (2001)

22. Matsumoto, H., Yor, M.: Exponential functionals of Brownian motion, I: Probability laws at fixed time. Probab. Surv. 2, 312–347 (2005)

23. Matsumoto, H., Yor, M.: Exponential functionals of Brownian motion, II: Some related diffusion processes. Probab. Surv. 2, 348–384 (2005)

24. Milevsky, M.A., Posner, S.E.: Asian options, the sum of lognormals, and the reciprocal gamma distribution. J. Financ. Quant. Anal. 33, 409–422 (1998)

25. Pollak, M., Siegmund, D.: A diffusion process and its applications to detecting a change in the drift of a Brownian motion. Biometrika 72, 267–280 (1985)

26. Rogers, L.C.G., Shi, Z.: The value of an Asian option. J. Appl. Probab. 32, 1077–1088 (1995)

27. Thompson, G.W.P.: Fast narrow bounds on the value of Asian options. Working paper (1999). Available online at: http://www.jbs.cam.ac.uk/fileadmin/user_upload/research/workingpapers/wp0209.pdf

28. Turnbull, S.M., Wakeman, L.M.: A quick algorithm for pricing European average options. J. Financ. Quant. Anal. 26, 377–389 (1991)

29. Večeř, J.: A new PDE approach for pricing arithmetic average Asian options. J. Comput. Finance 4, 105–113 (2001)

30. Večeř, J.: Black–Scholes representation for Asian options. Math. Finance 24, 598–626 (2014)

31. Vervaat, W.: On a stochastic difference equation and a representation of non-negative infinitely divisible random variables. Adv. Appl. Probab. 11, 750–783 (1979)

32. Yor, M.: Loi de l’indice du lacet brownien, et distribution de Hartman–Watson. Z. Wahrscheinlichkeitstheor. Verw. Geb. 53, 71–95 (1980)

33. Yor, M.: On some exponential functionals of Brownian motion. Adv. Appl. Probab. 24, 509–531 (1992)

34. Yor, M.: Sur certaines fonctionnelles exponentielles du mouvement brownien réel. J. Appl. Probab. 29, 202–208 (1992)

35. Yor, M.: Exponential Functionals of Brownian Motion and Related Processes. Springer, Berlin (2001)
