# Language of Geometry

Calculates the complexity for "The language of geometry"

### Compiling Code
The code is written in [Haskell](https://www.haskell.org/downloads). No package is necessary to compile.

**Compiling:**
```sh
ghc -o lot database_from_file.hs
```

**Running:**

The first argument is the path of a file which must contain a list of strings (one string per line) to calculate the complexity.

The second argument is the Language of Thought type. Use "octagon" for the LoT for sequences in [0..7]. Use "binary" for the LoT for sequences in [0..1]. Use "chunk" for the Lot-Chunk version.

```sh
./lot experiments/binary/experiment1.txt "binary"
```

### Citing this code
Please cite one of the following papers:

Amalric M, Wang L, Pica P, Figueira S, Sigman M, et al. (2017) [The language of geometry: Fast comprehension of geometrical primitives and rules in human adults and preschoolers.](https://doi.org/10.1371/journal.pcbi.1005273) PLOS Computational Biology 13(1): e1005273.

Romano S, Salles A, Amalric M, Dehaene S, Sigman M, et al. (2018) [Bayesian validation of grammar productions for the language of thought.](https://doi.org/10.1371/journal.pone.0200420) PLOS ONE 13(7): e0200420.

Wang L, Amalric M, Fang W, Jiang X, Pallier C, et al. (2019) [Representation of spatial sequences using nested rules in human prefrontal cortex](https://doi.org/10.1016/j.neuroimage.2018.10.061) NeuroImage, Vol. 186, 2019. Pages 245-255.
