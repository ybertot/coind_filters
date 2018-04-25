Modeling a short but complex Haskell program manipulating lazy sequences

The main objective of this experiment is to show that one can use the simple
co-recursion capabilities of the Coq system to describe complex programs
mixing co-recursion and well-founded recursion.

The culminating example is a program that computes the infinite sequence
of prime numbers.  As such, it is only well-formed because we can prove that
there are an infinity of prime numbers.


Files sieve.v filter.v and sieve_arith_complements.v have been edited from
the initial revision to compile with coq-8.3pl1 and coq-8.4pl3
(as checked in June 2014).

The same version still compiles with coq-8.8 (as checked in April 2018),
but there are warnings concerning deprecated commands.

Just these three files should be enough to see the contents of the paper 

"Filters on coinductive streams, an application to Eratosthenes' sieve"

at work.

To run them, compile them in the following order:

filter.v
sieve_arith_complements.v
sieve.v
