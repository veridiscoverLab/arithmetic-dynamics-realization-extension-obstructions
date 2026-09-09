# Formalization Scope and Theorem Entry Points

The Lean declarations specify the scope and hypotheses of each result. Section numbers follow *Realization, Extension, and Orbit Obstructions in Arithmetic Dynamics*.

## Independent Main Results

| Section | Main declarations | Source files |
|---|---|---|
| §2: Inverse realization of `p`-normal sets | `ArithDyn.Derksen.theorem22`, `prop26`, `prop27` | [Prop26.lean](../ArithDyn/Derksen/Prop26.lean); the propositions are defined in [Normal.lean](../ArithDyn/Derksen/Normal.lean) |
| §4: Orbit-density oscillation | `ArithDyn.Density.liminf_density_galoisField`, `limsup_density_galoisField`, `density_not_convergent_galoisField` | [Main.lean](../ArithDyn/Density/Main.lean) |
| §4: Zariski density | `ArithDyn.Density.prop_4_10` | [Zariski.lean](../ArithDyn/Density/Zariski.lean) |
| §5: No universal geometrically nilpotent seed | `ArithDyn.Nilpotence.theorem_5_2`, `theorem_5_2_locallyClosed`, `theorem_5_2'` | [Main.lean](../ArithDyn/Nilpotence/Main.lean), [Irreducible.lean](../ArithDyn/Nilpotence/Irreducible.lean) |
| §5: Monomial criterion | `ArithDyn.Nilpotence.prop_5_11` | [Monomial.lean](../ArithDyn/Nilpotence/Monomial.lean) |

None of these three groups of modules transitively imports `ArithDyn.Extension`. The geometric TODOs in §3 do not impose `hres` or polarized-extension assumptions on them.

The final declaration in §2, `theorem22 (p) [Fact p.Prime] : Theorem22 p`, invokes the unconditional proof of `prop26`. The proof uses finite modifications in the definition, closure properties of recurrence zero sets, and descent along finite-field extensions to obtain a realization over the fixed field `RatFunc (ZMod p)`.

## §3: Verified Projective Results

[theorem_3_1_projective](../ArithDyn/Extension/Theorem31Projective.lean) takes the following inputs:

- A homogeneous ideal `I` in the original polynomial ring, with a nonempty geometric projective zero locus;
- A family `f` of homogeneous forms of degree `d ≥ 2`;
- The assumptions that `f` has no base points on the original zero locus and that substitution preserves the original ideal `I`.

It constructs an endomorphism `φ` of `Proj(k[x]/I)` and maps `j, Ψ` in a common finite coordinate system, proving that:

1. `j` is a closed immersion into the standard polynomial `Proj`;
2. `j*O(1) ≅ O_X(s)`, where the right-hand side is the standard twisting sheaf pulled back along the original coordinate inclusion;
3. `Ψ*O(1) ≅ O(d)`, with the original degree `d` unchanged;
4. The scheme morphisms satisfy `φ ≫ j = j ≫ Ψ`, and the square commutes for every iterate.

These identities include the structure-sheaf maps and retain the original quotient by `I`. The radical ideal is used only in the base-point-free criterion.

The homogeneous coordinate presentation and `f` have not yet been constructed from arbitrary original data `X,L,φ`. Nor have this presentation, the concrete twisting sheaves, and the base-field structure been fully identified with the original inputs. The scope of the general version therefore remains subject to the [geometric TODOs](TODO.md).

## Section and Polarization Interfaces

- [ProjTwistReconstruction.lean](../ArithDyn/Extension/ProjTwistReconstruction.lean): Extracts transition functions from a sheaf of modules with specified local bases and proves the reconstruction isomorphism by sheaf gluing.
- [ProjTwistPullbackMate.lean](../ArithDyn/Extension/ProjTwistPullbackMate.lean): Proves that the canonical comparison for pullback of sheaves of modules is invertible.
- [PolarizationSheaf.lean](../ArithDyn/Extension/PolarizationSheaf.lean): Produces compatible isomorphisms of sheaves of modules in every degree from a single polarization isomorphism.
- [PolarizedSectionDynamics.lean](../ArithDyn/Extension/PolarizedSectionDynamics.lean): Assembles these maps into an endomorphism of the same full section ring. When the original morphism is over the base field, this is a base-field algebra endomorphism. Degree zero retains the full `Γ(X,O_X)`.
- [SectionLifting.lean](../ArithDyn/Extension/SectionLifting.lean): Given a surjective restriction map `hres` in the exact required degree, constructs homogeneous polynomial lifts, the original homogeneous kernel, and the full commutative algebra diagram.

The cocycle powers and their multiplication are implemented. The tensor-product constructions and their natural identifications with an independently given `L^{⊗n}` remain TODOs.

## Verification Entry Points

`ArithDyn.lean` imports all library modules. The four axiom inventories are:

| File | Number of `#print axioms` checks |
|---|---:|
| [Axioms.lean](../ArithDyn/Axioms.lean) | 89 |
| [BridgeAxioms.lean](../ArithDyn/Extension/BridgeAxioms.lean) | 74 |
| [ProjTwistAxioms.lean](../ArithDyn/Extension/ProjTwistAxioms.lean) | 66 |
| [EndpointAxioms.lean](../ArithDyn/Extension/EndpointAxioms.lean) | 68 |

There are 297 check commands in total, counting repeated checks of the same theorem. The verification script also compiles [ProjectiveEndpoint.lean](../tests/ProjectiveEndpoint.lean) and [PolarizedInput.lean](../tests/PolarizedInput.lean). The former invokes the full projective theorem with an arbitrary field universe and finite coordinates. The latter connects the actual section ring, grading, and polarization endomorphism to `SectionLifting`, retaining the explicit `hres` assumption. Both tests retain the original field without a `ULift` replacement.

Permitted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The checks verify the declarations under their stated hypotheses. Deriving the geometric hypotheses from the general problem remains a separate formalization task.

See the [verification record](VERIFICATION.md) for the results of this build.
