# Geometric Interface TODO

## General target

Let `k` be an arbitrary field, `X` a projective `k`-scheme, `L` an ample line bundle, and `φ : X → X` a `k`-morphism. Fix `μ : φ*L ≅ L^⊗d`, where `d ≥ 2`. The target is to construct a closed immersion `j : X ↪ ℙᴹ_k` and an everywhere-defined morphism `Ψ` of the same degree `d`, with `Ψ ∘ j = j ∘ φ`, preserving all original iterates, and with `j*O(1) ≅ L^⊗s` for some `s ≥ 1`.

The library establishes the version with coordinate inputs, together with the cocycle section algebra, the maps in every degree induced by a single polarization, and the section-lifting theorem. The remaining tasks construct these inputs from the given geometric data.

## Remaining implementation

- [ ] **Construct the embedding from an ample power.** Starting from the original `L`, obtain `a ≥ 1`, `B = L^⊗a`, an actual closed immersion `i : X ↪ ℙʳ_k`, and `i*O(1) ≅ B`.
- [ ] **Identify the original tensor powers.** Construct natural identifications of the tensor powers with the existing cocycle powers, compatible with multiplication, restriction, pullback, and higher-degree polarizations induced by the single `μ`.
- [ ] **Prove `hres`.** Use the ideal sheaf of the original embedding to prove surjectivity of restriction in the required degree `td`, retaining the full target section space and allowing `Γ(X,O_X) ≠ k`.
- [ ] **Identify the original scheme and morphism.** Prove that the original `X` is the actual `Proj` of the chosen homogeneous restriction kernel, and identify the original `φ`, the coordinate endomorphism, and the final commutative square on the full structure sheaf over the specified base field, preserving nonreduced structure.
- [ ] **Handle the empty scheme.** The general target includes the empty scheme, whereas the current coordinate theorem assumes geometric nonemptiness; this boundary case requires a separate implementation.

A separate task is to formalize the paper's degree-one boundary proposition (§3, Proposition 3.7). The `d ≥ 2` theorem above is independent of this proposition.

## How standard theorems supply the inputs on paper

The following argument uses standard algebraic geometry. Its end-to-end formalization in Lean remains pending.

### 1. Fix a very ample power

First assume that `X` is nonempty. Ampleness and the finite-type hypothesis give some `B = L^⊗a` and an immersion `i : X → ℙʳ_k` with `i*O(1) ≅ B`. Since `X/k` is proper and the target is separated, this immersion is proper, has closed image, and is a closed immersion. These statements apply to nonreduced schemes. [Stacks 01VS](https://stacks.math.columbia.edu/tag/01VS), [01W6](https://stacks.math.columbia.edu/tag/01W6), [01IQ](https://stacks.math.columbia.edu/tag/01IQ)

### 2. Apply Serre vanishing to this fixed embedding

Let `𝓘` be the coherent ideal sheaf of the original embedding. Tensor the ideal-sheaf exact sequence with `O(n)` and take cohomology. Serre vanishing gives `H¹(ℙʳ,𝓘(n)) = 0` for all sufficiently large `n`, yielding

$$
H^0(\mathbb P^r,\mathcal O(n))\twoheadrightarrow H^0(X,B^{\otimes n}).
$$

For `n ≥ 0`, the left-hand side consists of homogeneous forms of degree `n` in the old variables. Choose `t ≥ 1` so that `td` reaches this threshold, obtaining the required `hres`. The ideal sheaf and its vanishing threshold remain fixed as `t` varies. Surjectivity is required only in degree `td`. [Stacks 0B5T](https://stacks.math.columbia.edu/tag/0B5T), [01XT](https://stacks.math.columbia.edu/tag/01XT)

### 3. Construct the coordinates and homogeneous kernel

Set `s_α = u^α|_X`, where `|α| = t`. These sections define `j₀ = ν_t ∘ i` and generate `M = B^⊗t`; they need not form a basis of the full space of global sections.

The fixed polarization identifies `φ*s_α` with a section of `M^⊗d = B^⊗td`. By `hres`, each such section lifts to a form of degree `td` in the old variables. Factoring each monomial into a product of `d` monomials of degree `t` gives homogeneous forms `F_α` of degree `d` in the new variables, satisfying exact equalities on the original sections.

Set

$$
J=\ker\!\left(k[Y_\alpha]\longrightarrow
\bigoplus_{m\ge0}H^0(X,M^{\otimes m}),\quad Y_\alpha\longmapsto s_\alpha\right).
$$

This is a homogeneous ideal, and `X ≅ Proj(k[Y]/J)` preserves the original closed subscheme structure. The identification uses the exact restriction kernel, including the data of the nonreduced structure. [Stacks 03GL](https://stacks.math.columbia.edu/tag/03GL)

For homogeneous `G ∈ J`, the single polarization and its compatible tensor powers give `G(F(s)) = 0`, so substitution preserves the original `J`. Under the polarization isomorphism, the pullbacks of the generating sections still generate the corresponding line bundle. Hence the `F_α` have no common base point on the original geometric zero locus. Generating sections of a line bundle, together with its isomorphism, determine the projective morphism. Thus the resulting endomorphism of the quotient scheme equals the original `φ` as a scheme morphism, including its action on the structure sheaf. [Stacks 01NE](https://stacks.math.columbia.edu/tag/01NE)

The verified coordinate extension theorem now applies, providing the required further embedding while preserving the original degree `d`. Serre vanishing supplies the section-lifting input; the coordinate theorem supplies the ambient extension over finite fields. The empty scheme can be handled separately using the empty embedding and `[x:y] ↦ [x^d:y^d]` on `ℙ¹`.

## Criteria for completion of the formalization

The remaining steps formalize classical geometric facts and their application to the original objects. The implementation must construct the actual identifications and prove compatibility. Each desired conclusion requires a proof from the original inputs; `hres` remains an explicit hypothesis until its proof is formalized.

The general target may be described as an end-to-end formalization only once it takes the original `X,L,φ,μ` directly as inputs and constructs all the intermediate data above. The independent results in §2, §4, and §5 do not depend on completing this TODO.
