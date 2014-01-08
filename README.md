From the Porter
===============

Homebrew users can install z3 via my tap: ```brew tap paulp/extras && brew install z3``` No, that's not true anymore because mavericks broke everything in the world, but [here is a guy](http://stackoverflow.com/questions/20877528/errors-when-building-z3-unstable-branch) with the same problem, so maybe something will develop on that front.

The lara source was scala 2.7 - this repository takes it to 2.8, 2.9, 2.10, and finally 2.11.0-M7, and also from ant to [sbt](https://github.com/paulp/sbt-extras/). I am unaffiliated with the authors of this code, I'm just an interested observer who prefers a more recently minted scala.

```
sbt test
```

Comfusy: Complete Functional Synthesis
======================================

This repository contains the source code for the implementation of the "Complete Functional Synthesis" approach described in the eponymous PLDI 2010 paper [1].

For more info, please read the [corresponding page hosted at EPFL](http://lara.epfl.ch/w/comfusy).

References
----------

  1. V.Kuncak, M.Mayer, R.Piskac, P.Suter, *Complete Functional Synthesis*, Proceedings of the 2010 ACM SIGPLAN conference on Programming Language
Design and Implementation (PLDI). 2010, pp. 316–329.
  2. V.Kuncak, M.Mayer, R.Piskac, P.Suter, *Software Synthesis Procedures*, Communications of the ACM (Feb. 2012), pp. 103–111.
