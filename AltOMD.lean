import AltOMD.VerifiedRegret
import AltOMD.Hamiltonian.CanonicalHamiltonian
import AltOMD.Regret.CanonicalEnergy
import AltOMD.Entropy.WeightedSeries
import AltOMD.Entropy.Polarization
import AltOMD.Entropy.Shannon.Extended
import AltOMD.Entropy.Shannon.LogarithmicRegret
import AltOMD.Entropy.Shannon.Algorithm
import AltOMD.Hamiltonian.ScalarMajorant
import AltOMD.Hamiltonian.ManuscriptBounds
import AltOMD.Hamiltonian.TaylorSource
import AltOMD.Entropy.EuclideanPolarization
import AltOMD.Entropy.ExtendedDuality
import AltOMD.Regret.Decomposition
import AltOMD.Regret.ExtendedRegret
import AltOMD.Entropy.Shannon.Legendre

/-! Lean formalization accompanying the AltOMD manuscript.

The primal entry point `AltOMD.ExtendedRegret.logarithmic_regret` states both
manuscript bounds for extended-real regularizers, with the initial comparator
radius explicit. The reduction to finite real restrictions is proved internally.
The original `AltOMD.VerifiedRegret.logarithmic_regret` remains available.
This theorem derives iterate interiority from relative-gradient boundary blowup and
applies the proved BCH results directly to a common canonical sequence.
The generic primal and dual theorems remain available transitively.
`AltOMD.BCH.propositionA1` verifies the manuscript's BCH proposition, including
its explicit Dynkin formula. The Dynkin–Specht–Wever identity is proved
internally as part of that construction.
-/
