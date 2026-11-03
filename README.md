# AltOMD-Lean

Lean 4 formalization of *Logarithmic Regret for Alternating Mirror Descent*
by Tianlong Nan and Christian Kroer.

Start with [CORRESPONDENCE.md](CORRESPONDENCE.md) to locate a manuscript result.
The [mathematical statements](AltOMDAudit/README.md) translate the corresponding
Lean declarations into **assumptions and conclusions**, with links to the proofs
and a comparison with the paper.

The manuscript and Lean use $K=4$ and $C=384\max\{\|A\|,1\}$ for the Shannon
specialization, with additive regret coefficient $128/3+4e^2$. Lean proves
the Shannon derivative bound directly for multilinear derivatives and includes
the manuscript's exact supremum bound as a corollary. Banach's diagonal-norm
equality is also formalized for finite-dimensional real Hilbert spaces;
the correspondence notes distinguish these proof routes.

## Verify the proofs

The project pins Lean and Mathlib to `v4.33.1`. From the repository root, run:

```sh
lake exe cache get
lake build AltOMD AltOMD.Audit
lake env lean AltOMD/Audit.lean
```

The build checks the proofs. The last command prints the axioms used by the
selected results. The permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The mathematical statements explain the
assumptions and conclusions checked by Lean.

## Source layout

| Location | Contents |
| --- | --- |
| [AltOMD/BCH.lean](AltOMD/BCH.lean) | Universal BCH theorem |
| [AltOMD/Regret/ExtendedRegret.lean](AltOMD/Regret/ExtendedRegret.lean) | Main theorem and decomposition for extended-real regularizers |
| [AltOMD/Algebra/](AltOMD/Algebra/) | Formal series and Lie algebra |
| [AltOMD/Hamiltonian/](AltOMD/Hamiltonian/) | Hamiltonian corrections and finite-energy analysis |
| [AltOMD/Entropy/](AltOMD/Entropy/) | Convex duality, Shannon entropy, and multiplicative weights |
| [AltOMD/Regret/](AltOMD/Regret/) | Trajectories, comparator identities, and regret bounds |
| [AltOMD/Audit.lean](AltOMD/Audit.lean) | Axiom checks |
