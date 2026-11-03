# Lean results: assumptions and conclusions

This page translates the proved Lean statements into mathematical notation.
Each entry links to the declarations being summarized. The **Comparison**
notes state whether the mathematical assumptions and conclusions match the
manuscript. The [correspondence map](../CORRESPONDENCE.md) follows the
manuscript order.

The energy and regret constants match the manuscript, including $K=4$ for
Shannon entropy. Lean proves the Shannon derivative estimate directly and also
formalizes Banach's norm equality used in the manuscript's proof.

Throughout, “smooth” means $C^\infty$, derivative norms are multilinear
operator norms, and $A^{\ast}$ denotes the adjoint (the transpose in Euclidean
coordinates). The relative Bregman divergence is
$D_\psi(c,x)=\psi(c)-\psi(x)-\langle\nabla_{\mathrm{rel}}\psi(x),c-x\rangle$.
Logarithms are natural unless a base is displayed.

<a id="prop-bch"></a>

## BCH theorem

Lean: [AltOMD.BCH.propositionA1](../AltOMD/BCH.lean#L106), [AltOMD.BCH.existsUnique_bch](../AltOMD/BCH.lean#L49). Manuscript: Proposition A.1.

**Assumptions.** Let $A=\mathbb Q\langle U,V\rangle$ be the free associative algebra on two generators, with commutator $[P,Q]=PQ-QP$. Work in $A[[t]]$. The symbols $tU,tV$ have positive degree, so formal exponentials and logarithms are defined coefficient by coefficient. No numerical convergence assumption occurs.

**Statement.** There is a unique zero-constant series
$Z=\log(\exp(tU)\exp(tV))$ satisfying $\exp Z=\exp(tU)\exp(tV)$.
Writing $Z=\sum_{q\ge1}t^q\Phi_q$, each $\Phi_q$ is a rational Lie polynomial homogeneous of word length $q$. For every $q\ge1$,

$$
\Phi_q=\frac1q\sum_{m=1}^q\frac{(-1)^{m-1}}m
\sum_{\substack{r_i,s_i\ge0,\ r_i+s_i>0\\\sum_i(r_i+s_i)=q}}
\frac{[U^{r_1}V^{s_1}\cdots U^{r_m}V^{s_m}]}
{\prod_i r_i!s_i!}.
$$

The bracket expands into individual letters with right nesting, and a one-letter bracket equals that letter.

**Comparison.** Matched. The formal-series variable records word degree.

<a id="lem-formal-modified-energy-preservation"></a>

## Formal preservation of modified energy

Lean: [AltOMD.CanonicalHamiltonian.bilinear_formal_preservation](../AltOMD/Hamiltonian/CanonicalHamiltonian.lean#L278), [AltOMD.CanonicalHamiltonian.formalPullback_coefficient](../AltOMD/Hamiltonian/CanonicalHamiltonian.lean#L183). Manuscript: formal preservation lemma.

**Assumptions.** Let $n,m\ge0$, let $A:\mathbb R^n\to\mathbb R^m$ be linear, and let $F:\mathbb R^n\to\mathbb R$, $G:\mathbb R^m\to\mathbb R$ be smooth. Extend $F,G$ to the product by the coordinate projections. Set $L_Qf=\{f,Q\}$ for the constant skew tensor associated with $A$. Define the canonical BCH corrections $H_r$, with $H_0=F+G$.

**Statement.** For $\widehat H_\eta=\sum_{r\ge0}\eta^rH_r$,

$$
\exp(\eta L_G)\exp(\eta L_F)\widehat H_\eta=\widehat H_\eta.
$$

More explicitly, for every $q\ge0$ and every point $z$,
$\sum_{r+\alpha+\beta=q}(L_G^\alpha L_F^\beta H_r)(z)/(\alpha!\beta!)=H_q(z)$.
The associated update first computes $u'=u-\eta A^\top\nabla G(w)$, then $w'=w+\eta A\nabla F(u')$. The formal pullback therefore has the displayed operator order.

**Comparison.** Matched. Both statements assert formal coefficient identities without assuming convergence.

<a id="lem-correction-coefficients"></a>

## Coefficient bound for correction terms

Lean: [AltOMD.CanonicalHamiltonian.bilinear_correction_representation_and_bound](../AltOMD/Hamiltonian/CanonicalHamiltonian.lean#L286), [AltOMD.CanonicalHamiltonian.correction_representation_and_bound](../AltOMD/Hamiltonian/CanonicalHamiltonian.lean#L120). Manuscript: correction-coefficient lemma.

**Assumptions.** Use the smooth bilinear Hamiltonian system and canonical corrections from the preceding entry. Let $r\ge0$.

**Statement.** A specified finite coefficient list represents $H_r$ as

$$
H_r=\sum_i c_i\{Q_{i,1},\{Q_{i,2},\ldots,
\{Q_{i,r},Q_{i,r+1}\}\ldots\}\},\qquad
\sum_i|c_i|\le4^{r+1},
$$

where every $Q_{i,j}$ is $F$ or $G$. Each word has $r+1$ letters, and repeated words may remain separate summands. For $r=0$, the length-one convention yields $H_0=F+G$.

**Comparison.** Matched, including ordinary right nesting, word length $r+1$,
the coefficient bound $4^{r+1}$, and the $r=0$ convention. Collecting repeated
words can only decrease the sum of absolute coefficients.

<a id="lem-lie-derivative-majorant"></a>

## Coefficient bound for a Lie derivative

Lean: [ScalarMajorant.lie_derivative_majorant_source_ereal](../AltOMD/Hamiltonian/ScalarMajorant.lean#L210). Manuscript: scalar-majorant lemma.

**Assumptions.** Let $J:E^{\ast}\to E$ be continuous and linear, and let $F,G,f:E\to\mathbb R$ be smooth. Suppose $K\ge1$ and $\|D^rF(x)\|+\|D^rG(y)\|\le K^r r!$ for every $r\ge1,x,y$. Choose $Q=F$ or $Q=G$. Let $b(t)=\sum_{r\ge0}b_rt^r$ be a formal scalar series with $b_r\ge0$. Assume $\|D^rf\|_\infty/r!\le b_r$ for $r\ge1$.

**Statement.** Define $L_Qf=Df[J(DQ)]$ and the formal series
$v(t)=\|J\|K(1-Kt)^{-2}$. Then every derivative of $L_Qf$ has a finite global supremum and

$$
\frac{\|D^sL_Qf\|_\infty}{s!}\le[t^s]\bigl(v(t)b'(t)\bigr),\qquad s\ge0.
$$

**Comparison.** Matched. Lean proves the inverse-square coefficient formula and the formal-series bound. Finiteness of the suprema follows internally from the displayed bounds.

<a id="lem-bracket-majorant"></a>

## Derivative bound for nested brackets

Lean: [ManuscriptBounds.nested_bracket_bound_source](../AltOMD/Hamiltonian/ManuscriptBounds.lean#L194). Manuscript: nested-bracket lemma.

**Assumptions.** Let $J:E^{\ast}\to E$ be continuous, linear, and skew, and let $F,G$ be smooth. Suppose $K\ge1$ and
$\|D^aF\|_\infty+\|D^aG\|_\infty\le K^a a!$ for all $a\ge1$. Set $C_0=24\max\{\|J\|,1\}K^2$. Choose any ordinary right-nested Poisson bracket $B$ with $q\ge2$ letters, each equal to $F$ or $G$.

**Statement.** Every derivative supremum below is finite, and

$$
\frac{\|D^sB\|_\infty}{(q+s-1)!}\le C_0^{q+s-1},\qquad s\ge0.
$$

**Comparison.** Matched. The theorem uses the summed derivative assumption, ordinary right nesting, and the manuscript's global bound. The conversion from the internal bracket convention is proved.

<a id="lem-lie-derivative-bound"></a>

## Lie derivative bound for correction terms

Lean: [ManuscriptBounds.canonical_mixed_bound_of_nested](../AltOMD/Hamiltonian/ManuscriptBounds.lean#L148), with [canonical_mixed_bound_source](../AltOMD/Hamiltonian/ManuscriptBounds.lean#L213) supplying the nested-bracket hypothesis from the standing regularity assumption. Manuscript: mixed Lie-derivative lemma.

**Assumptions.** Let $J$ be a continuous skew linear map and let $F,G$ be smooth. Assume the preceding nested-bracket bound holds with a constant $C_0\ge1$. Let $H_r$ be the canonical BCH corrections. Choose $r,\alpha,\beta\ge0$ with $r+\alpha+\beta\ge1$.

**Statement.** The global supremum is finite and satisfies

$$
\|L_G^\alpha L_F^\beta H_r\|_\infty
\le(4C_0)^{r+\alpha+\beta+1}(r+\alpha+\beta)!.
$$

**Comparison.** Matched. The canonical coefficient representation and coefficient bound are supplied inside the proof. No Hamiltonian-representation hypothesis remains.

<a id="lem-real-taylor-composition"></a>

## Taylor remainder for two composed flows

Lean: [BilinearSystem.taylor_remainder_source](../AltOMD/Hamiltonian/TaylorSource.lean#L68). Manuscript: composed-flow Taylor lemma.

**Assumptions.** Let $A:E_X\to E_Y$ be bounded linear between real Hilbert spaces, let $F,G$ be smooth, and let $f:E_X\times E_Y\to\mathbb R$ be smooth. Use the associated Hamiltonian operators $L_F,L_G$. Fix $m\ge0$ and assume
$|\bigl(L_{G}^{\alpha}L_{F}^{\beta}f\bigr)(z)|\le M$ for every $z$ whenever $\alpha+\beta=m+1$.

**Statement.** For every $h\ge0$ and $z=(u,w)$, the actual AltOMD shear is

$$
\mathcal M_{h}(u,w)=
\bigl(u-hA^{\ast}\nabla G(w),\,
 w+hA\nabla F(u-hA^{\ast}\nabla G(w))\bigr).
$$

This map satisfies

$$
\left|f\bigl(\mathcal M_{h}(z)\bigr)-
\sum_{\alpha+\beta\le m}\frac{h^{\alpha+\beta}}{\alpha!\beta!}
\bigl(L_{G}^{\alpha}L_{F}^{\beta}f\bigr)(z)\right|
\le\frac{2^{m+1}M h^{m+1}}{(m+1)!}.
$$

**Comparison.** Matched. The global derivative bound supplies the bounds along the shear trajectories internally.

<a id="lem-regret-decomposition"></a>

## Regret decomposition

Lean: [ExtendedRegret.regret_decomposition_all](../AltOMD/Regret/ExtendedRegret.lean#L309), using [Decomposition.regret_decomposition_all](../AltOMD/Regret/Decomposition.lean#L207). Manuscript: regret-decomposition lemma.

**Assumptions.** Let $\psi_X,\psi_Y$ be proper closed convex extended-real regularizers with the relative Legendre properties. Their effective domains have closures $X,Y$. Let $A:E_X\to E_Y$ be linear between finite-dimensional real inner-product spaces. Fix a real step size $\eta$ (positive in the manuscript), start in the relative interiors of the effective domains, and follow the actual primal AltOMD minimization updates. Fix comparators $c_x\in\mathrm{dom}\,\psi_X,c_y\in\mathrm{dom}\,\psi_Y$.

Initialize $u_0=\nabla_{\mathrm{rel}}\psi_X(x_0)$ and $w_0=\nabla_{\mathrm{rel}}\psi_Y(y_0)$, then set $u_{k+1}=u_k-\eta A^{\ast}y_k$ and $w_{k+1}=w_k+\eta Ax_{k+1}$. Write $F=\psi_X^{\ast}$, $G=\psi_Y^{\ast}$, $H_0=F+G$, and

$$
\Gamma(u,w)=F(u)+G(w)+\psi_X(c_x)+\psi_Y(c_y)
-\langle u,c_x\rangle-\langle w,c_y\rangle.
$$

**Statement.** The conjugate values along the generated dual trajectory are finite. For every $k\ge0$,

$$
0\le\Gamma(u_k,w_k)
=D_{\psi_X}(c_x,x_k)+D_{\psi_Y}(c_y,y_k),
$$

$$
\eta\bigl(\langle Ax_{k+1},c_y\rangle-\langle Ac_x,y_k\rangle\bigr)
=H_0(z_{k+1})-H_0(z_k)+\Gamma(z_k)-\Gamma(z_{k+1}).
$$

**Comparison.** Matched. The proof derives finiteness and interiority from the primal minimization updates. No finite-initial-radius premise is added to this lemma.

<a id="lem-modified-energy-tool"></a>

## Finite modified-energy bounds

Lean: [canonical_bilinear_modified_energy_estimates](../AltOMD/Regret/CanonicalEnergy.lean#L47).

**Assumptions.** Let $E_X,E_Y$ be finite-dimensional real inner-product spaces, $A:E_X\to E_Y$ linear, and $F,G$ smooth real-valued functions on the respective spaces. Assume $K\ge1$ and, for every integer $r\ge1$ and every $u,w$,

$$
\|D^rF(u)\|+\|D^rG(w)\|\le K^r r!.
$$

Set $C_0=24\max\{\|A\|,1\}K^2$. Choose any $N\in\mathbb N$,
$0<\eta\le[16C_0(N+2)]^{-1}$, and $z=(u,w)$. Let $H_r$ be the canonical Hamiltonian coefficients constructed from the proved BCH coefficients, and define
$\widehat H_\eta^{[N]}=\sum_{r=0}^{N}\eta^rH_r$, with $H_0=F+G$.

**Statement.** For

$$
\mathcal M_{\eta}(u,w)=
\bigl(u-\eta A^{\ast}\nabla G(w),\;
w+\eta A\nabla F(u-\eta A^{\ast}\nabla G(w))\bigr),
$$

the two bounds are

$$
|\widehat H_\eta^{[N]}(z)-H_0(z)|\le\frac{64}{3}C_0^2\eta,
\qquad
|\widehat H_\eta^{[N]}(\mathcal M_\eta z)-\widehat H_\eta^{[N]}(z)|
\le16e^2C_0^2\eta\,4^{-(N+1)}.
$$

No convergence of the infinite modified-Hamiltonian series is assumed. The coefficient sequence and algebraic identities are supplied internally. The pointwise derivative assumption is equivalent to the manuscript’s sum-of-suprema bound. Moreover, $\|A\|=\|J_A\|$ for the Euclidean block Hamiltonian matrix, so the definition of $C_0$ agrees.

**Comparison.** Matched, including the correction constant $64/3$ and
defect bound $16e^2C_0^2\eta\,4^{-(N+1)}$.

<a id="thm-main"></a>

## Logarithmic regret

Lean: [ExtendedRegret.logarithmic_regret](../AltOMD/Regret/ExtendedRegret.lean#L183), with the extended-real primal trajectory defined in the same file and [regret definition](../AltOMD/Regret/PrimalRegret.lean#L72).

**Assumptions.** Let $E_X,E_Y$ be finite-dimensional real inner-product spaces and $A:E_X\to E_Y$ linear. The strategy sets $X,Y$ are compact and convex. Each regularizer is a proper closed convex extended-real function whose effective domain has closure equal to the corresponding strategy set. Each regularizer is strictly convex and continuously differentiable in affine-hull coordinates on the relative interior of the effective domain. The relative-gradient norm tends to infinity along every interior sequence approaching the relative boundary.

The actual Fenchel conjugates $F,G$ are smooth and satisfy $\sup_u\|D^rF(u)\|+\sup_w\|D^rG(w)\|\le K^r r!$ for every $r\ge1$, with fixed $K\ge1$. Fix initial points in the relative interiors of the effective domains, independently of the horizon. Assume the actual extended-real initial radius is finite:

$$
\Lambda_0=\sup_{c_x\in X}D_{\psi_X}(c_x,x_0)
+\sup_{c_y\in Y}D_{\psi_Y}(c_y,y_0)<\infty.
$$

For every integer $T\ge1$, set $N=\lfloor\log_2T\rfloor$, $C_0=24\max\{\|A\|,1\}K^2$, and $\eta=[16C_0(N+2)]^{-1}$. Assume sequences start at the fixed initial points and, for every $k<T$, are feasible minimizers satisfying

$$
\begin{aligned}
x_{k+1}&\in\arg\min_{a\in X}\{
\eta\langle Aa,y_k\rangle+D_{\psi_X}(a,x_k)\},\\
y_{k+1}&\in\arg\min_{b\in Y}\{
-\eta\langle Ax_{k+1},b\rangle+D_{\psi_Y}(b,y_k)\}.
\end{aligned}
$$

The Bregman objective uses the extended-real regularizer value. The proof establishes agreement of the derivative pairing with the relative gradient. Later-iterate interiority follows from the minimization updates.

**Statement.** Define

$$
\begin{aligned}
\mathrm{Reg}_T={}&\sup_{c_x\in X}\sum_{k<T}
\bigl(\langle Ax_{k+1},y_k\rangle-\langle Ac_x,y_k\rangle\bigr)\\
&+\sup_{c_y\in Y}\sum_{k<T}
\bigl(\langle Ax_{k+1},c_y\rangle-\langle Ax_{k+1},y_k\rangle\bigr).
\end{aligned}
$$

Then

$$
\mathrm{Reg}_T\le16C_0\Lambda_0(N+2)
 +\left(\frac{128}{3}+4e^2\right)C_0^2
\le16C_0\Lambda_0(\log_2T+2)
 +\left(\frac{128}{3}+4e^2\right)C_0^2.
$$

**Comparison.** Matched, including the additive coefficient $128/3+4e^2$.
The two endpoint corrections contribute $128/3$, and
$T/4^{N+1}\le1/4$ bounds the accumulated defect by $4e^2$.
The theorem is quantified over extended-real regularizers. Finite initial
radius implies that every feasible comparator has a finite regularizer value,
so the reduction to real restrictions is proved internally.

<a id="prop-fenchel-legendre-identities"></a>

## Fenchel–Legendre identities

Lean: [ExtendedDuality.fenchel_legendre_identities](../AltOMD/Entropy/ExtendedDuality.lean#L163). Manuscript: Fenchel–Legendre proposition.

**Assumptions.** Let $\psi:E\to\mathbb R\cup\{+\infty\}$ be proper and convex on a finite-dimensional real inner-product space. Assume $\psi$ is differentiable in affine-hull coordinates throughout $\mathrm{ri}(\mathrm{dom}\,\psi)$. The actual Fenchel conjugate
$f(u)=\sup_{c\in E}(\langle u,c\rangle-\psi(c))$ is finite on a neighborhood of $u$ and differentiable at $u$. Suppose $x=\nabla f(u)\in\mathrm{ri}(\mathrm{dom}\,\psi)$.

**Statement.** Then

$$
\psi(x)+f(u)=\langle u,x\rangle,
\qquad
\langle u-\nabla_{\mathrm{rel}}\psi(x),c-x\rangle=0
\quad\text{for every }c\in\mathrm{dom}\,\psi.
$$

**Comparison.** Matched. Lean uses the extended-real Fenchel supremum and derives the required real conjugate and derivative identities from local finiteness.

<a id="prop-power-series-polarization-input"></a>

## Power-series and polarization bounds

Lean: [WeightedSeries.completeSpace](../AltOMD/Entropy/WeightedSeries.lean#L44), [norm_mul_le](../AltOMD/Entropy/WeightedSeries.lean#L119), [iteratedDeriv_eq](../AltOMD/Entropy/WeightedSeries.lean#L158), [abs_iteratedDeriv_le](../AltOMD/Entropy/WeightedSeries.lean#L165), and [Polarization.euclidean_norm_eq_diagonal_sup](../AltOMD/Entropy/EuclideanPolarization.lean#L10).

**Assumptions.** Fix a real radius $r>0$. A series $P=(P_j)_{j\geq0}$ belongs to $\mathcal A_r$ when $\sum_{j\geq0}|P_j|r^j<\infty$. The multiplication bound concerns arbitrary $P,Q\in\mathcal A_r$. The derivative statement allows every integer $s\geq0$. Separately, let $s\geq1$ and let $M:E^s\to\mathbb R$ be a continuous multilinear map on $E=\mathbb R^d$ with the Euclidean norm, invariant under every permutation of the arguments.

**Statement.** The space $\mathcal A_r$ is complete for the weighted coefficient norm. Multiplication is the Cauchy product, with coefficient $(PQ)_j=\sum_{a+b=j}P_aQ_b$, and

$$
\|PQ\|_r\leq\|P\|_r\|Q\|_r.
$$

The scalar sum $p(t)=\sum_{j\geq0}P_jt^j$ is analytic near zero. The actual ordinary derivatives satisfy

$$
p^{(s)}(0)=s!P_s,
\qquad |p^{(s)}(0)|\leq s!r^{-s}\|P\|_r.
$$

For the symmetric multilinear map, Lean proves

$$
\|M\|_{\mathrm{op}}=\sup_{\|h\|\leq1}|M(h,\ldots,h)|.
$$

The norm is the multilinear operator norm, and the supremum concerns the closed unit ball. The equality includes $d=0$. The separate [general real polarization bound](../AltOMD/Entropy/Polarization.lean#L167), valid without a Hilbert-space assumption, is retained with factor $s^s/s!$ (and hence $e^s$).

**Comparison.** The power-series claims match. In the manuscript's completeness proof, $P^{[n]}$ denotes
a whole series in a Cauchy sequence, $a_{n,j}$ its $j$th coefficient, and $a_j$ the
limiting coefficient. In Lean these correspond to `u n : Series r`,
`coeff r (u n) j`, and `coeff r P_lim j` for the limit series $P_\infty$, represented
by `P_lim : Series r`. The stored coordinate
`(u n) j` is weighted by $r^j$. Lean inherits completeness from $\ell^1$;
`dist_eq_weighted_sum` identifies its distance with the manuscript's weighted
coefficient distance. This notation clarification changes no assumptions or
conclusions. Banach's norm equality also matches exactly. The
[finite-dimensional Hilbert-space proof](../AltOMD/Entropy/Banach.lean#L29)
chooses a norm-attaining unit tuple whose vector sum has maximal norm.
Symmetry and the parallelogram identity show that normalized pair averaging
preserves norm attainment; maximality then forces all entries to coincide.
The zero-dimensional case is handled separately.

<a id="prop-shannon"></a>

## Shannon entropy

Lean: [strictConvexOn_entropy](../AltOMD/Entropy/Shannon.lean#L48), [contDiffOn_entropy_intrinsicInterior](../AltOMD/Entropy/Shannon.lean#L145), [gradientBlowsUpAtBoundary_entropy](../AltOMD/Entropy/Shannon.lean#L184), [extendedEntropy_fenchel_eq_logSumExp](../AltOMD/Entropy/Shannon/Extended.lean#L103), [gradient_logSumExp](../AltOMD/Entropy/Shannon.lean#L319), [norm_iteratedFDeriv_logSumExp_le_sharp](../AltOMD/Entropy/ShannonDerivatives.lean#L206), [norm_iteratedFDeriv_logSumExp_le_manuscript](../AltOMD/Entropy/ShannonDerivatives.lean#L236), [sup_norm_iteratedFDeriv_logSumExp_le_manuscript](../AltOMD/Entropy/ShannonDerivatives.lean#L248), the retained [norm_iteratedFDeriv_logSumExp_le](../AltOMD/Entropy/ShannonDerivatives.lean#L256), [bregman_le_radius](../AltOMD/Entropy/Shannon/Trajectory.lean#L59), and [supremum_bregman_le_radius](../AltOMD/Entropy/Shannon/Trajectory.lean#L67).

The extended-real properties are proved separately by
[effectiveDomain_extendedEntropy](../AltOMD/Entropy/Shannon/Extended.lean#L45),
[extendedEntropy_proper](../AltOMD/Entropy/Shannon/Extended.lean#L71),
[lowerSemicontinuous_extendedEntropy](../AltOMD/Entropy/Shannon/Extended.lean#L56),
and [convex_epigraph_extendedEntropy](../AltOMD/Entropy/Shannon/Extended.lean#L91).
The theorem [isLegendre_extendedEntropy](../AltOMD/Entropy/Shannon/Legendre.lean#L43)
packages these and the relative geometry into `ExtendedRegret.IsLegendre`.

**Assumptions.** Let $I$ be a finite nonempty coordinate set, with Euclidean norm on $\mathbb R^I$, and let $\Delta_I=\{x:x_i\geq0,\ \sum_i x_i=1\}$. Define $\psi(x)=\sum_i x_i\log x_i$ on $\Delta_I$, with $0\log0=0$, and define $\psi(x)=+\infty$ outside $\Delta_I$. The radius conclusion additionally fixes $x\in\Delta_I$ with every coordinate strictly positive.

**Statement.** The entropy is finite and continuous on the closed simplex, strictly convex there, and smooth on the relative interior. The relative interior consists exactly of the strictly positive simplex points. Along every sequence of relative-interior points converging to a relative-boundary point, the norm of the gradient restricted to the affine hull tends to infinity. These are the relative Legendre properties used in the manuscript.

The extended-real entropy is proper and lower semicontinuous, with convex epigraph and effective domain exactly $\Delta_I$. The full Fenchel supremum satisfies

$$
\sup_{x\in\mathbb R^I}\bigl(\langle u,x\rangle-\psi(x)\bigr)
=F(u):=\log\sum_i e^{u_i},
\qquad (\nabla F(u))_i=\frac{e^{u_i}}{\sum_j e^{u_j}}.
$$

The conjugate is smooth everywhere. For every $u\in\mathbb R^I$ and every integer $s\geq1$,

$$
\|D^sF(u)\|_{\mathrm{op}}\leq2^{s-1}s!\leq\frac12 4^s s!.
$$

The manuscript's literal uniform statement is also formalized:

$$
\sup_{u\in\mathbb R^I}\|D^sF(u)\|_{\mathrm{op}}\leq\frac12 4^s s!.
$$

For every comparator $c$ in the closed simplex, including boundary points, the relative Bregman divergence equals $\sum_i c_i\log(c_i/x_i)$. Consequently,

$$
\sup_{c\in\Delta_I}D_\psi(c,x)\leq\log\frac1{\min_i x_i}<\infty.
$$

Finiteness of the derivative and Bregman suprema follows from the uniform
pointwise bounds `norm_iteratedFDeriv_logSumExp_le_sharp` and
`bregman_le_radius`. These give upper bounds for the underlying ranges.
The real-valued supremum inequalities alone do not assert boundedness:
Lean's `sSup` on an unbounded-above set of reals is $0$.

**Comparison.** The geometry, conjugacy, radius, and literal derivative supremum
statements match. The manuscript's $4^s s!/2$ bound is a formal corollary of
Lean's stronger $2^{s-1}s!$ bound; the earlier $16^s s!$ theorem is also retained.
The proof estimates the full multilinear coefficients of
the analytic composition of the logarithm and normalized exponential sum.
It does not use a directional-to-multilinear norm conversion. Banach's
diagonal-norm equality is proved separately as described above.

<a id="prop-entropy-assumptions"></a>

## Validity of the entropy assumptions

Lean: [isLegendre_extendedEntropy](../AltOMD/Entropy/Shannon/Legendre.lean#L43), [sum_sup_derivatives_le](../AltOMD/Entropy/Shannon/LogarithmicRegret.lean#L75), [norm_iteratedFDeriv_logSumExp_le_sharp](../AltOMD/Entropy/ShannonDerivatives.lean#L206), [contDiff_logSumExp](../AltOMD/Entropy/ShannonDerivatives.lean#L109), [bregman_le_radius](../AltOMD/Entropy/Shannon/Trajectory.lean#L59), and [supremum_bregman_le_radius](../AltOMD/Entropy/Shannon/Trajectory.lean#L67).

**Assumptions.** Let $I,J$ be finite nonempty coordinate sets. Both players use the negative Shannon regularizer on the corresponding closed simplex. Fix strictly positive initial strategies $x_0\in\Delta_I$ and $y_0\in\Delta_J$. Define $F(u)=\log\sum_{i\in I}e^{u_i}$ and $G(w)=\log\sum_{j\in J}e^{w_j}$.

**Statement.** Both regularizers have the relative Legendre properties, and both conjugates are smooth on the entire Euclidean space. For every integer $s\geq1$, the actual global derivative suprema satisfy

$$
\sup_u\|D^sF(u)\|_{\mathrm{op}}
+\sup_w\|D^sG(w)\|_{\mathrm{op}}
\leq4^s s!.
$$

$$
\begin{aligned}
\Lambda_0
&:=\sup_{c\in\Delta_I}D_{\psi_I}(c,x_0)
 +\sup_{d\in\Delta_J}D_{\psi_J}(d,y_0)\\
&\leq\log\frac1{\min_i x_{0,i}}
 +\log\frac1{\min_j y_{0,j}}<\infty.
\end{aligned}
$$

**Comparison.** Matched with $K=4$. Lean applies its
stronger full multilinear derivative estimate to both conjugates, while the
manuscript uses Banach's norm equality after bounding directional derivatives.
The pointwise derivative and Bregman bounds establish finiteness of all the
displayed suprema, as explained above.

The theorem `isLegendre_extendedEntropy` supplies all six fields of
[`ExtendedRegret.IsLegendre`](../AltOMD/Regret/ExtendedRegret.lean#L25):
properness, lower semicontinuity, convexity, strict convexity on the relative
interior, relative $C^1$ regularity, and boundary steepness. It transports
the real entropy properties to `ExtendedDuality.value extendedEntropy`
using equality on the simplex and local equality in affine-hull coordinates.
The headline theorem itself uses extended-real
derivative suprema and explicitly assumes a finite extended-real initial
radius, so its assumptions do not have the real-supremum ambiguity.

<a id="cor-entropy"></a>

## Alternating multiplicative weights

Lean: [alternatingSimplex_regret](../AltOMD/Entropy/Shannon/Algorithm.lean#L139) and [alternatingSimplex_regret_uniform](../AltOMD/Entropy/Shannon/Algorithm.lean#L156), for the [alternatingSimplex recursion](../AltOMD/Entropy/Shannon/Algorithm.lean#L50).

**Assumptions.** Let $I,J$ be finite nonempty coordinate sets, let $A:\mathbb R^I\to\mathbb R^J$ be linear, and fix strictly positive simplex points $x_0,y_0$. For every integer $T\geq1$, set

$$
C=384\max\{\|A\|_{\mathrm{op}},1\},\qquad
R_0=\log\frac1{\min_i x_{0,i}}+\log\frac1{\min_j y_{0,j}},\qquad
\eta=\frac1{16C(\lfloor\log_2T\rfloor+2)}.
$$

**Statement.** The recursion starts from $(x_0,y_0)$ and uses the normalized updates

$$
x_{k+1,i}=\frac{x_{k,i}e^{-\eta(A^\top y_k)_i}}
{\sum_\ell x_{k,\ell}e^{-\eta(A^\top y_k)_\ell}},\qquad
 y_{k+1,j}=\frac{y_{k,j}e^{\eta(Ax_{k+1})_j}}
{\sum_\ell y_{k,\ell}e^{\eta(Ax_{k+1})_\ell}}.
$$

Every denominator is positive, and every iterate remains a strictly positive simplex point. Player two uses the newly updated $x_{k+1}$. The [total external regret](../AltOMD/Regret/PrimalRegret.lean#L72), evaluated at $(x_{k+1},y_k)$ for $0\leq k<T$, satisfies

$$
\mathrm{Reg}_T\leq16CR_0(\log_2T+2)
 +\left(\frac{128}{3}+4e^2\right)C^2.
$$

More explicitly, player one takes the supremum over $c\in\Delta_I$ of $\sum_{k<T}\langle A(x_{k+1}-c),y_k\rangle$. Player two takes the supremum over $d\in\Delta_J$ of $\sum_{k<T}\langle Ax_{k+1},d-y_k\rangle$. The total regret is the sum of these two suprema, with each comparator fixed across all rounds.

For uniform initial strategies, the bound becomes

$$
\mathrm{Reg}_T\leq16C\log(|I||J|)(\log_2T+2)
 +\left(\frac{128}{3}+4e^2\right)C^2.
$$

Lean's natural-number logarithm in the step size equals $\lfloor\log_2T\rfloor$ for $T\geq1$.

**Comparison.** Matched, including $K=4$, $C=384\max\{\|A\|,1\}$,
the step size, and the additive coefficient $128/3+4e^2$.
The [Lean proof](../AltOMD/Entropy/Shannon/LogarithmicRegret.lean#L118)
applies [VerifiedRegret.logarithmic_regret](../AltOMD/VerifiedRegret.lean#L62)
to real-valued entropy on the simplex, supplying the pointwise derivative
and comparator-radius bounds directly. The manuscript derives the corollary
from its extended-real main theorem, whose Lean counterpart is
`ExtendedRegret.logarithmic_regret`.
All hypotheses of the theorem used by Lean are discharged internally.
The bundled `isLegendre_extendedEntropy` theorem also establishes the
headline theorem's Legendre condition; the corollary retains its existing
proof through `VerifiedRegret.logarithmic_regret`.
