# Amplitudology
Code to perform symbolic and numerical computations relevant for scattering amplitude techniques in quantum field theory.

!!! IMPORTANT: this code was developed for private use and it has just been made public (19/03/2026). WORK IN PROGRESS to clean it up and comment it properly to make it user-friendly.

STRUCTURE:

(1) Symbolic expressions

Symbolic definitions (including kernel-level properties) for: dot products, Weyl spinor products, Dirac spinor products, field strength products, Levi-Civita tensors.

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
