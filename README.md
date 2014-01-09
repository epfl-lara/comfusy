Comfusy: Complete Functional Synthesis
======================================

This repository contains the source code for the implementation of the "Complete Functional Synthesis" approach described in the eponymous PLDI 2010 paper [1]. Consider it unmaintained.

For more info, please read the [corresponding page hosted at EPFL](http://lara.epfl.ch/w/comfusy).

Comfusy was originally written against Scala 2.7 (compiler and library), and built using ant. Ports to sbt and Scala > 2.7 by [paulp](https://github.com/paulp/).

A note for Mac users
====================

(By [paulp](https://github.com/paulp/comfusy).) Homebrew users can install z3 via my tap: ```brew tap paulp/extras && brew install z3``` No, that's not true anymore because mavericks broke everything in the world, but [here is a guy](http://stackoverflow.com/questions/20877528/errors-when-building-z3-unstable-branch) with the same problem, so maybe something will develop on that front.

References
----------

  1. V.Kuncak, M.Mayer, R.Piskac, P.Suter, *Complete Functional Synthesis*, Proceedings of the 2010 ACM SIGPLAN conference on Programming Language
Design and Implementation (PLDI). 2010, pp. 316–329.
  2. V.Kuncak, M.Mayer, R.Piskac, P.Suter, *Software Synthesis Procedures*, Communications of the ACM (Feb. 2012), pp. 103–111.
