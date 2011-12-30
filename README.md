The package [fingertree](http://hackage.haskell.org/package/fingertree) provides finger trees over any monoid, allowing great flexibility. Unfortunately, this comes at a considerable performance cost: for example, sequences implemented with this package tend to run about an order of magnitude slower than the specialised code in the [containers](http://hackage.haskell.org/package/containers) package. 

The main obstacles to performance in the fingertree package relative to the containers package are:

  * boxed representation of the underlying monoid
  * lack of specialisation of the underlying monoid operations

This package, fingertree-unboxed, addresses both of these problems. We use Template Haskell to generate the boilerplate for the unboxed representation, and we make ample use of INLINABLE pragmas to specialise for the monoid operations.

