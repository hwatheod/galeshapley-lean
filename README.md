## Introduction
This repository is formalization of some results about stable matchings and the [Gale-Shapley algorithm](https://en.wikipedia.org/wiki/Gale%E2%80%93Shapley_algorithm). 

We follow [Dumont's paper](https://www.mat.univie.ac.at/~slc/opapers/s23dumont.pdf) (in French) as it contains more advanced results than other sources.

An introduction to the subject can be found in Gale and Shapley's [original paper](https://www.jstor.org/stable/2312726). Many other sources have introductory material on the topic as well.

We do not handle the case of incomplete preference lists. However, we do allow different cardinalities on the two sides, so matchings are implemented as partial functions `M → Option W`.

In the main library `GaleShapley`, only one proposer, arbitarily chosen using `choose`, proposes on each round. This gives maximal generality of the results, since it shows they do not depend on who proposes each round. For a computable implementation, see the `Computable Implementation` section.

## Summary of main results formalized

#### GaleShapley.Basic

Implements the Gale-Shapley algorithm `galeShapley` which gives a stable matching given an initial set of preferences. The proof of stability is from Gale and Shapley's original paper, also given in Section 1.2 of Dumont, and many other sources.

#### GaleShapley.Optimality

`proposerOptimal`: The Gale-Shapley algorithm gives the optimal stable matching for the proposing side. The proof is from Gale and Shapley's original paper, also available in many other sources.

The dual result `receiverPessimal` follows as a corollary.

#### GaleShapley.Hwang

`hwangTheorem`: Hwang's theorem as stated in Dumont's paper section 1.5 in terms of revendicateurs. We follow the proof in Dumont. This gives three corollaries:
- `proposerOptimal'`: An alternative proof of proposer optimality.
- `paretoOptimality`: There is no matching (whether stable or not) in which all proposers do better than in the proposer-optimal stable matching. 
- `menShouldntLie`: The Dubins-Freedman result that "men shouldn't lie", with the proof given in Theorem 2.3 of Dumont. Using Hwang's theorem, the proof is much simpler than the original proof from Dubins and Freedman's paper.

#### GaleShapley.TwoStableMatchings

A collection of results about the interaction of 2 stable matchings for the same set of preferences, found in sections 1.3 and 1.4 of Dumont.

It culminates with Conway's result that the set of stable matchings for a fixed set of preferences form a complete lattice under the natural `inf` and `sup` operations (`supMatchingClosed`, `supMatchingStable`, `infMatchingClosed`, `infMatchingStable`)

#### GaleShapley.StableLattice

`mPref_stableCompleteLattice`: Construct the complete lattice mentioned above on the set of stable matchings, using the results from `GaleShapley.TwoStableMatchings`.

`gsEqualsTop`: Yet another version of proposer optimality, saying that the stable matching given by the Gale-Shapley algorithm is the top element of the complete lattice. We derive the result in a straightforward way from the main result in `Optimality`.

## Computable Implementation

The subdirectory `GaleShapley/Compute` contains a computable implementation of the algorithm which can be compiled and executed. We assume `DecidableEq M` and `DecidableEq W` to allow computation.

`Basic` contains the same implementation as in the main library, except that instead of choosing a proposer arbitrarily, we assume `LinearOrder M` and choose the lowest eligible proposer each round. This is a minimal version of the library where all proofs have been removed except those necessary to define the algorithm.

`BasicAlt` contains an alternate "parallel" implementation in which all eligible proposers propose each round. However, for reasons I don't really understand, this code runs extremely slowly starting at `n=4`. Ideas for resolving this issue, or at least understanding it, would be appreciated.

`Compute` contains a sample definition of some preferences and computations. The n=4 example is taken from Gale and Shapley's original paper. Some computations are done with `#eval`, and there is also a `Main` function doing the computation for `n=4` which can be compiled with `lake build GaleShapleyCompute`. The compiled binary is at `.lake/build/bin/GaleShapleyCompute`.

You can see the `n=4` slowdown for `BasicAlt` if you change the import in `Compute` from `Basic` to `BasicAlt`, and look at the `#eval` statement towards the bottom of the file.



