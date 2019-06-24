# generics-mrsop-gdiff

Implements the GDiff algorithm with a more realistic memory consumption,
and adapted to the `generics-mrsop` library. The original implementation of
gdiff carries around a number of unecessary proof objects, which makes it
unusable in real-life-sized diffs.

The gdiff algorithm is described in [this paper](https://www.andres-loeh.de/GDiff.html)