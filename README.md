# generics-mrsop-gdiff

Implements the GDiff algorithm with a more realistic memory consumption,
and adapted to the `generics-mrsop` library. The original implementation of
gdiff carries around a number of unecessary proof objects, which makes it
unusable in real-life-sized diffs. The gdiff algorithm is described in [this paper](https://www.andres-loeh.de/GDiff.html)

We also provide a merge algorithm based on [this repo](https://github.com/VictorCMiraldo/stdiff),
for the `stdiff` approach. Read [this paper](https://victorcmiraldo.github.io/data/tyde2017.pdf)
and/or [this thesis](https://dspace.library.uu.nl/handle/1874/380853) for more information.
