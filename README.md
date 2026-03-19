# Amplitudology
Code to perform symbolic and numerical computations relevant for scattering amplitude techniques in quantum field theory.

Research package developed over the course of a PhD and postdoc for personal and collaborative use. Recently made public (19/03/2026), documentation improvements in progress.

Key research tool in all papers listed here: https://inspirehep.net/authors/1896597

STRUCTURE:

(1) Symbolic expressions

Symbolic definitions (including kernel-level properties) for: dot products, Weyl spinor products, Dirac spinor products, field strength products, Levi-Civita tensors.

Highlights:
-vec, pol: momentum and polarisation four-vectors, eg vec[i] --> p_i, pol[i] --> \epsilon_i
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

------

(3) Ansatz

Functions to create ansatz for: Compton amplitude, five-point amplitudes, generic amplitudes.

Steps:
- find basic building blocks (spinor products or dot products)
- helper functions useful in generating the ansatz
- functions to generate the ansatz and evaluate it numerically

------

(4) Graph functions

(Under construction)

Functions to generate/manipulate graphs representing Feynman diagrams.

So far:
- plot a graph with appropriate labels
- generalise the built-in CanonicalGraph functions to allow for multigraphs and for graphs with directed edges (retarder/advanced propagators)
