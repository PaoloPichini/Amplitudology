# Amplitudology
Code to perform symbolic and numerical computations relevant for scattering amplitude techniques in quantum field theory.

Research package developed over the course of a PhD and postdoc for personal and collaborative use. Recently made public (19/03/2026), documentation improvements in progress.

Key research tool in all papers listed here: https://inspirehep.net/authors/1896597

STRUCTURE:

(1) Symbolic expressions

Symbolic definitions (including kernel-level properties) for: dot products, Weyl spinor products, Dirac spinor products, field strength products, Levi-Civita tensors.

Highlights:
- vec, pol: momentum and polarisation four-vectors, eg vec[i] --> p_i, pol[i] --> \epsilon_i
- spA, spS: angle and square Weyl spinors, eg spA[i] --> |i>, spS[i] --> |i]
- Ubar, V: Dirac spinors, eg Ubar[i] --> \bar{u}_i
- ap, sp: angle and square Weyl products, eg ap[spA[i],spA[j]] --> <ij>, sp[spS[i],spS[j]] --> [ij]
- momp: Weyl momentum product, eg momp[spS[i],vec[j],spA[k]] --> [i|p_j|k>
- dot: Lorentz dot product, eg dot[pol[i],vec[j]] --> p_i . \epsilon_j
- dp: Dirac spinor product, eg dp[Ubar[i],vec[j],V[k]] --> \bar{u}_i \slashed{p}_j v_k

------

(2) Numerics

Explicit parametrisation of momenta and spinors.

Functions to plug in numbers into such parametrisation (rational, floating point, finite fields).

Functions optimized for four-point Compton amplitudes (two-massive-two-massless kinematics).

Generalisation of key functions to arbitrary amplitudes.

Highlights:
- Three number fields supported: rational, floating point, finite fields (prime $P to choose)
- toField, toRational: convert between rationals and finite field arithmetic
- Numgen: generates numerical polarisation vectors for a given set of massive and massless particles
- Numdict: dictionary translating symbolic expressions (dot, dp, ap, sp, momp, epsilon) into numerical evaluations
- NumEvalMatrix / NumEvalMatrixFP: builds a matrix of numerical evaluations over finite fields / floating point
- indepFF: takes an ansatz list and extracts linearly independent structures using finite field row reduction
- solveFF: solves a system of conditions on an ansatz using finite field numerics

------

(3) Ansatz

Functions to create ansatz for: Compton amplitude, five-point amplitudes, generic amplitudes.

Steps:
- find basic building blocks (spinor products or dot products)
- helper functions useful in generating the ansatz
- functions to generate the ansatz and evaluate it numerically

Key sections:
- All-Point Ansatz: versatile functions for any kinematics (Lorentz dot products)
- Spinor Ansatz: functions to build ansatz for Dirac spinor products

Highlights:
- BasisCov / BasisCovRel: produce a basis and basis reduction relation for any given kinematics (NB polarisation and momentum variables)
- AnsatzCov / AnsatzCovFull: use basis to create an ansatz for Lorentz dot products
- dotproducts / dotprod: generates all possible monomials of dot products from a list of building blocks
- dpAnsatz / dpAnsatzSpecialize: constructs all possible ansatz terms with two Dirac spinors and a specified number of gamma matrices, given polarisation vectors of external particles

------

(4) Graph functions

(Under construction)

Functions to generate/manipulate graphs representing Feynman diagrams.

So far:
- plot a graph with appropriate labels
- generalise the built-in CanonicalGraph functions to allow for multigraphs and for graphs with directed edges (retarder/advanced propagators)
