# Realization, Extension, and Orbit Obstructions in Arithmetic Dynamics

Lean 4 formalizations of recurrence zero-set realization via Frobenius, degree-preserving projective extension, and orbit obstructions.

| Result | Formalized scope | Entry point |
|---|---|---|
| Inverse realization of recurrence zero sets in positive characteristic | Realization of every `p`-normal set over the fixed field `𝔽_p(t)` | [Derksen/Prop26.lean](ArithDyn/Derksen/Prop26.lean) |
| Degree-preserving projective extension | Closed immersion, twisting-sheaf pullbacks, and a commuting diagram for all iterates, starting from homogeneous coordinate data | [Extension/Theorem31Projective.lean](ArithDyn/Extension/Theorem31Projective.lean) |
| Oscillation of orbit densities over finite-field extensions | Density liminf, limsup, and nonconvergence for an explicit map | [Density/Main.lean](ArithDyn/Density/Main.lean) |
| Nonexistence of a universal geometrically nilpotent seed | An explicit counterexample, with statements for closed and locally closed subvarieties | [Nilpotence/Irreducible.lean](ArithDyn/Nilpotence/Irreducible.lean) |

The proofs of inverse realization, density oscillation, and geometric nilpotence do not depend on the extension module. See [formalization scope](docs/FORMALIZATION.md) for theorem declarations and precise inputs.

## Build and checks

Install [elan](https://github.com/leanprover/elan) and Python 3. The repository pins Lean `4.29.0` and the Mathlib revision.

```bash
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

The final command audits four lists of declarations and compiles two interface tests. Axiom dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`. The source contains no `sorry`, `native_decide`, or custom axioms. Each theorem is checked under its stated hypotheses.

## Remaining gap in general projective extension

The general theorem starts with a projective scheme `X` over an arbitrary field, an ample line bundle `L`, and a fixed polarization `φ*L ≅ L^⊗d`, where `d ≥ 2`. Its conclusion is an extension to projective space of the same degree. The formalization covers the construction from coordinate data, section algebras, and the maps in every degree induced by a single polarization. **The passage from general geometric data to these coordinate inputs remains to be formalized.**

On paper, choose a very ample power `B = L^⊗a` and a closed immersion `i : X ↪ ℙʳ`, with ideal sheaf `𝓘`. The exact sequence

$$
0\longrightarrow\mathcal I(n)\longrightarrow\mathcal O_{\mathbb P^r}(n)
\longrightarrow i_*B^{\otimes n}\longrightarrow0
$$

and Serre vanishing give surjectivity of restriction for all sufficiently large `n`. Choosing `t ≥ 1` with `td` sufficiently large gives the hypothesis called `hres` in the code:

$$
k[u_0,\ldots,u_r]_{td}\twoheadrightarrow H^0(X,B^{\otimes td}).
$$

The polarized pullbacks of the degree-`t` coordinate sections lift to degree-`td` forms, which become degree-`d` forms in Veronese coordinates. The argument applies over arbitrary fields and to nonreduced schemes, retains the full `H⁰(X,O_X)`, and uses restriction surjectivity only in degree `td`. The standard inputs are [embeddings from ample powers](https://stacks.math.columbia.edu/tag/01VS), [Serre vanishing](https://stacks.math.columbia.edu/tag/0B5T), and [sections on projective space](https://stacks.math.columbia.edu/tag/01XT).

The remaining work is to formalize these classical inputs and identify the original scheme, tensor powers, and polarization with the coordinate construction. See the [geometric TODO](docs/TODO.md) for the tasks and their mathematical justification.
