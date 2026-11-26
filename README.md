# Mordell-Weil Theorem

A Proof of Mordell theorem of Elliptic curves, which states that 

for an elliptic curve $E$ defined over the rational numbers $Q$, the group of rational points of $E$ is a finitely generated abelian group.

## Step 0 [Descent lemma](Mordell/Descent.lean)

Define 

G: Abelian group,

Height:  `h : G → K`,  `K` is an Archimedean order field (e.g. $R$)

and  Suppose

- (a) `h_fin`  : for `C`  `{P | h P ≤ C}` is finite
- (b) `h_add`  : for `Q` const. `c_Q` $\exist$ `h (P + Q) ≤ 2 h P + c_Q`
- (c) `h_dbl`  : $\exist$ c s.t. `4 h P - c ≤ h (2 • P)`
- (d) `G / 2G` is finite

Then `G` is finitelt generated

(d) is given by two patterns
- `descent_lemma` : With an explicit element `S` of finite set
- `descent_lemma'` : quoitent group `G ⧸ 2G` is `Finite`

## Step 1 [Naive height](Mordell/Step1.lean)

`W.Point`:  Rational number group of elliptic curve of Mathlib (which has group structure) and 
`P.naiveHeight = logHeight (x(P) : 1)`: naive height of Mathlib (`x(P) = m/n` => `log max(|m|,|n|)`)

proves 
- (a) `finite_height_le`    : `{P | h P ≤ B}` is finite
- (b) `height_add_le`       : `h (P + Q) ≤ 2 h P + c_Q`
- (c) `height_two_smul_ge`  : `4 h P - c ≤ h (2 • P)`

- Field `F` has height(`AdmissibleAbsValues F`)
- (a) is [Northcott](https://www.math.tugraz.at/~widmer/Publications/Northprop.pdf)(there are only finitely many elements of bounded degree and bounded height)
`F = ℚ` satisfies above assumptions,

The instance is [`Mathlib.NumberTheory.Height.NumberField`](https://lean4.party/docs/Mathlib/NumberTheory/Height/NumberField.html)

(b)(c) are derived from **approx parallelogram relation(近似平行四辺形則)**（M. Stoll, 2026）
  `|h(P+Q) + h(P-Q) - 2(h P + h Q)| ≤ C`
of Mathlib.
The proof states add/sub map `addSubMap : ℙ² → ℙ²` is a morphism (generazation of discussion of [resultant](https://en.wikipedia.org/wiki/Resultant)(終結式) of  denominator and numerator of doubled point formular)

At last, states for the points group of Mathlib that **If one suppose weak Mordell–Weil（`W(F)/2W(F)` is finite, `W(F)` is finited generated** with Step 0 (`descent_lemma'` of `Mordell.Descent`).

## Step 2 [Weak Mordell–Weil theorem(1)](Mordell/Step2.lean)

Consider a curve   `E : y² = x³ + a x² + b x`   (`b ≠ 0`) which has a rational point `T = (0,0)` with order 2. 

`SqClass F` is a group of square class(平方類) `F^× / (F^×)²` 

Define a map

`α(O) = 1`,  `α(T) = b`,  `α(x, y) = x`  （`x ≠ 0`）

(Silverman–Tate, *Rational Points on Elliptic Curves*, §III.5)

1. `alpha_add`      : `α` is homomorphic ($\forall$ `F` group structure is `W.Point`  inMathlib)
2. `alpha_eq_cls_dvd` : `F = ℚ`, `a b ∈ ℤ` then  `α(P)` is square class of `b` ,which is divisor `d`
3. `finite_range_alpha` : especially image of `α` is finite

### Digest of proof 
-  **Vieta**（`vieta`）: a line `y = ℓx + ν` crosses with a curve at `x₁, x₂`, 

`x₁x₂ + x₁x₃ + x₂x₃ = b - 2ℓν`、`x₁x₂x₃ = ν²` where the third crossing point is `x₃ = ℓ² - a - x₁ - x₂`

then `x³+ax²+bx-(ℓx+ν)² - (x-x₁)(x-x₂)(x-x₃)` is first order formuler, vanishes at `x₁, x₂` (if tangent is double root)

- **image**: If `x = m/n` is irreducible, `(mn)·(m² + amn + bn²)`is a square of integer.
  
  Bacause common divisor of two factors divides `b` (`b n⁴ = n²S - mn(mn + an²)`, `m⁴ = m²S - mn(am² + bmn)`), `mn = ± g u²`  (`g ∣ b`)
  
## Step 2.2 [2-Isogeny map](Mordell/Isogeny.lean)

Define a map from `E : y² = x³ + c x² + d x` to `E_u : y² = x³ + A x² + B x`  (`A = -2c/u²`, `B = (c² - 4d)/u⁴`) 

 `φ_u(O) = O`,  `φ_u(T) = O`,  `φ_u(x, y) = (y²/(u²x²), y(d - x²)/(u³x²))`

as a map between points groups of Mathlib `W.Point`, then prove

- `Data.phi_add`  : `φ_u` is **homomorphic**
- `psi_phi`       : `ψ ∘ φ = [2]`（`φ = φ₁ : E → E'`, `ψ = φ₂ : E' → E`）
- `Data.exists_phi_eq_of_alpha_eq_one` : `ker α ⊆ φ_u(E(ℚ))`

`u = 1` is `φ : E → E'`, `u = 2` isが `ψ : E' → E` (`E' : y² = x³ - 2a x² + (a² - 4b) x`)

The core of the proof is the gradient of tangent line of `E'` is given as closed form　`L = N / (-ν u (2ℓx₁x₂ + ν(x₁+x₂)))` (`Mordell.IsogId`)

## [Weak Mordell–Weil and Mordell theorem](Mordell/WeakMW.lean) (for a curve has order 2 rational points)

### Group theory: `finite_reps_two`
If 
- additive　map `ψ : Γ' →+ Γ`, `φ : Γ → Γ'` are `ψ (φ P) = 2 • P`
- Image of homomorphism `α : Γ →+ A`、`α' : Γ' →+ A'` if finite

  `ker α ⊆ ψ(Γ')`、`ker α' ⊆ φ(Γ)`

for abelian group `Γ, Γ'` , there exists finitely representation`Γ / 2Γ`

(representive element version of `[Γ : 2Γ] ≤ [Γ : ψΓ'] [Γ' : φΓ] = |α(Γ)| |α'(Γ')|` in the textbook)

### Final result
-  for `weak_mordell_weil` : `E : y² = x³ + ax² + bx` (`a, b ∈ ℤ`, `b ≠ 0`, `a² - 4b ≠ 0`), there exists finitely representations of `E(ℚ) / 2E(ℚ)`
- `mordell`: `E(ℚ)` is finitely generated (sets Axiom systems of the Height of $Q$ and Northcott as instance arguments)
