Modeling a short but complex Haskell program manipulating lazy sequences

The main objective of this experiment is to show that one can use the simple
co-recursion capabilities of the Coq system to describe complex programs
mixing co-recursion and well-founded recursion.

The culminating example is a program that computes the infinite sequence
of prime numbers.  As such, it is only well-formed because we can prove that
there are an infinity of prime numbers.


Files sieve.v filter.v and sieve_arith_complements.v have been edited from
the initial revision to compile with coq-8.8.

Just these three files should be enough to see the contents of the paper.

"Filters on coinductive streams, an application to Eratosthenes' sieve"

To run the files, generate a makefile with the following command:

`coq_makefile -f _CoqProject -o Makefile`

then make with:

`make`


