# Efficient CHAD: Agda formalisation

CHAD [[1]][chad1] is an automatic differentiation (AD) algorithm in the form of a code transformation.
That is to say, it takes a program (in a functional language) that computes some function from real numbers to real numbers, and produces a different program that not only computes the original result of the input program, but also its derivative.
(The input program is allowed to have other arguments or results than just real numbers or structures/arrays of real numbers, but these will not be active for differentiation.)

CHAD is not the only such code transformation, but its roots in mathematics, which yield an elegant correctness proof (to those who are enlightened with knowledge of category theory), as well as its purity and generality make it particularly attractive.
However, so far its time complexity was not yet up to standards: for reverse AD, the expectation is that the produced program can compute a gradient in at most a constant factor more time than the original program computed its output, and CHAD as presented in [[1]][chad1] did not attain this complexity goal.

In our paper [[2]][arxiv2], we optimise the CHAD code transformation to make it attain this goal and provide a proof that the desired complexity is indeed attained.
This repository contains an Agda formalisation of this complexity proof.


## Building the proof

Compiling the code = checking the proof, because of how Agda works.
We use Agda 2.6.3 with [standard-library](https://github.com/agda/agda-stdlib/releases/tag/v1.7.2) version 1.7.2.

To compile, use `make check`, or equivalently `agda --safe chad-cost.agda`.
(The `--safe` flag disables various features, such as additional axioms (`postulate`) etc., that can make Agda unsound. Of course, the code also compiles without `--safe`.)

If you wish, you can furthermore add `--without-K` and observe that the code still compiles in this mode.


## Structure of the code

The formalisation is split in two parts: the _statement_ of the theorem, and its _proof_.
This is done to facilitate manually reading the specification (that sets up everything needed for the statement and then poses the statement) and verifying that it corresponds to what you expect this proof to prove.
If you are convinced of this, observing that `chad-cost.agda` defines terms of the required types (i.e. proofs of the required theorems) is sufficient to believe the proof, if you trust Agda.
There is then no need to understand all the additional lemmas and arguments that lead to this proof.

The **specification** is given in `spec/linear-types.agda`, `spec/LACM.agda` and `spec.agda`.
The `spec.linear-types` module sets up some definitions about the monoids that we use (our use of "linear" in this repository refers to monoid structures, not resource-linearity as in Rust, Linear Haskell etc.); `spec.LACM` then defines an abstract _local accumulation monad_ with some declared complexity properties (that the implementation in Agda does not satisfy because it lacks mutability, but a proper implementation is easily written in e.g. Haskell); finally, `spec.agda` gives the term language we operate on, its semantics and cost model (`eval`), the CHAD code transformation as we modified it (`chad`), and finally the theorem statements (`TH1-STATEMENT` and `TH2-STATEMENT`).
Theorem 1 is the theorem that is proved by induction; theorem 2 is its corollary that does away with the potential function, which users are likely not interested in.

The specification part of the Agda code is properly commented and also appears in the appendix of the paper [[2]][arxiv2].

The **proof** first gives some definitions and lemmas in `setup.agda`, and then proves two larger lemmas in `eval-sink-commute.agda` (which proves that `eval` and `sink` commute given appropriate permutations of the relevant valuation environments) and `chad-preserves-primal.agda` (which proves that the first half of a CHAD-transformed program actually does still compute the same thing as the original program -- this is used in the complexity proof for scoping constructs such as `let`).
Then, the final inductive proof, as well as that of the corollary, can be found in `chad-cost.agda`.
The proof uses a number of arithmetic lemmas of which the generated proofs (generated using `arith-solver` in this repo) can be found in `lemmas.agda`.
Documentation about the proof part of the proof is still somewhat lacking.


## Arithmetic lemmas

While Agda is great for anything defined in terms of induction on data types, it is not so great at integer arithmetic.
The standard library offers an integer equality solver (`Data.Integer.Solver`) but not an integer _inequality_ solver; `agda-presburger` exists but is, as befits a decision procedure for Presburger arithmetic, doubly exponential and in practice runs out of memory on formulas not half as large as we need to prove here.
Fortunately, the arithmetic proofs to be made are very simple in structure, and because I was not yet aware that Agda macros were sufficiently flexible to provide an interactive proving experience when I wrote this, I instead wrote Haskell code to prove such inequalities with a simple tactic language.
Said code lives in `arith-solver/`.
Documentation about this monstrosity is still somewhat lacking, but none of it is necessary to _read_ or _check_ the proof.
It is just clumsy automation to _write_ parts of the proof.


[chad1]: https://dl.acm.org/doi/10.1145/3527634
[arxiv2]: TODO
