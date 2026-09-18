# Statement

**Theorem 1.1.** Let $k$ be an algebraically closed field of characteristic $p > 2$ and let $X$ be a projective surface over $k$ with klt singularities, $\rho(X) = 1$ and $-K_X$ ample. Then $X$ has at most seven singular points.

**Theorem 1.2.** The bound is sharp and characteristic-dependent: over every algebraically closed field of characteristic three there is such a surface with exactly seven singular points and $K_X^2 = 1/3$ (Bernasconi), and over every algebraically closed field of characteristic two there are such surfaces $X_{2,n}$, $n \ge 3$, with $2n+1$ singular points and $K_X^2 = 2/(n-2)$ (Keel–McKernan).

Both theorems are proved in the paper (`source/manuscript.pdf`) and formalized in Lean 4:

```lean
KltDP.Manuscript.uniformSevenPointBound
KltDP.Manuscript.S01.sharpnessExampleCharThree
KltDP.Manuscript.S01.characteristicTwoFamily
```
