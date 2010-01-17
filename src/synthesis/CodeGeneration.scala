package synthesis

import scala.collection.immutable.Map

trait CodeGeneration {
  self: ChooseTransformer =>
  import global._
  import PASynthesis._
  import scala.tools.nsc.util.Position

  type SymbolMap = Map[String,Symbol]

  private lazy val scalaPack: Symbol = definitions.ScalaPackage
  private lazy val scalaMath: Symbol = definitions.getModule("scala.Math")
  private lazy val scalaMathMin: Symbol = definitions.getMember(scalaMath, "min")
  private lazy val scalaMathMax: Symbol = definitions.getMember(scalaMath, "max")
  private lazy val scalaMathAbs: Symbol = definitions.getMember(scalaMath, "abs")
  private lazy val scalaCollection: Symbol = definitions.getModule("scala.collection")
  private lazy val scalaCollectionImmutable: Symbol = definitions.getModule("scala.collection.immutable")
  private lazy val scalaCollectionImmutableSetModule: Symbol = definitions.getModule("scala.collection.immutable.Set")
  private lazy val setEmpty: Symbol = definitions.getMember(scalaCollectionImmutableSetModule, "empty")
  private lazy val unsatConstraintsException: Symbol = definitions.getClass("synthesis.Definitions.UnsatisfiableConstraint")
  private val throwTree = Throw(New(Ident(unsatConstraintsException), List(Nil)))
  private lazy val matrixIteratorClass: Symbol = definitions.getClass("synthesis.Common.MatrixIterator")
  private lazy val matrixIteratorClassNext: Symbol = definitions.getMember(matrixIteratorClass, "next")
  private lazy val synthesisPack: Symbol = definitions.getModule("synthesis")
  private lazy val synthesisCommon: Symbol = definitions.getModule("synthesis.Common")
  private lazy val bezoutFunction: Symbol = definitions.getMember(synthesisCommon, "bezoutWithBaseMM")
  private lazy val gcdFunction: Symbol = definitions.getMember(synthesisCommon, "gcdlist")
  private lazy val lcmFunction: Symbol = definitions.getMember(synthesisCommon, "lcmlist")

  class CodeGenerator(val unit: CompilationUnit, val owner: Symbol, val initialMap: SymbolMap, val emitWarnings: Boolean, val pos: Position) {
    import scala.tools.nsc.util.NoPosition

    // defines a new variable and returns a new symbol map with it
    private def assign(map: SymbolMap, varNme: String, expr: PATerm): (SymbolMap,Tree) = {
      val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "s")).setInfo(definitions.IntClass.tpe)
      (map + (varNme -> newSym), ValDef(newSym, termToCode(map, expr)))
    }

    private def apaAssign(map: SymbolMap, varNme: String, expr: APATerm): (SymbolMap,Tree) = {
      val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "s")).setInfo(definitions.IntClass.tpe)
      (map + (varNme -> newSym), ValDef(newSym, apaTermToCode(map, expr)))
    }

    private def apaInputAssign(map: SymbolMap, expr: /*APA*/InputAssignment): (SymbolMap,List[Tree]) = expr match {
      case SingleInputAssignment(inVar, inTerm) => {
        val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "t")).setInfo(definitions.IntClass.tpe)
        (map + (inVar.name -> newSym), List(ValDef(newSym, apaInTermToCode(map, inTerm))))
      }
      case BezoutInputAssignment(vss, ts) => {
        val matrixSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "m")).setInfo(matrixIteratorClass.tpe)
        var newMap: SymbolMap = map
        var trees: List[Tree] = Nil

        // builds a MatrixIterator with the results of the Bezout function.
        trees = trees ::: (ValDef(matrixSym, New(Ident(matrixIteratorClass), List(List( Apply(Select(Select(Ident(synthesisPack), synthesisCommon), bezoutFunction), List(Apply(Ident(definitions.ListModule), ts.map(apaInTermToCode(map, _))))))))) :: Nil)

        (vss.flatten:List[synthesis.InputVar]).foreach((v:synthesis.InputVar) => {
          val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "t")).setInfo(definitions.IntClass.tpe)
          newMap = newMap + (v.name -> newSym)
          trees = trees ::: (ValDef(newSym, Select(Ident(matrixSym), matrixIteratorClassNext.name)) :: Nil)
        })

        (newMap, trees)
      }
    }

    private def variable(map: SymbolMap, varNme: String): Tree = {
      Ident(map(varNme))
    }
  
    def programToCode(prec: PACondition, prog: PAProgram, withPrec: Boolean): Tree = 
      programToCode(initialMap, prec, prog, withPrec)

    def apaProgramToCode(prec: APACondition, prog: APAProgram, withPrec: Boolean): Tree =
      apaProgramToCode(initialMap, prec, prog, withPrec)

    def programToCode(initMap: SymbolMap, prec: PACondition, prog: PAProgram, withPrec: Boolean): Tree = {
      var map: SymbolMap = initMap

      if(prec.global_condition == PAFalse()) {
        if(emitWarnings)
          reporter.error(pos, "Synthesis predicate will never be satisfiable.")

        return throwTree // trick so that the code still typechecks
      }

      val preCheckCode: List[Tree] = if(withPrec && prec.global_condition != PATrue()) {
        List(If(Select(conditionToCode(map,prec), nme.UNARY_!), throwTree, EmptyTree))
      } else {
        Nil
      }

      var inputAss: List[Tree] = Nil
      prog.input_assignment.foreach(ia => {
        val (nmap, ntree) = assign(map, ia._1.name, ia._2)
        map = nmap
        inputAss = ntree :: inputAss
      })
      inputAss = inputAss.reverse

      val caseSplitAss: List[Tree] = if(prog.case_splits.programs.size != 0) {
        // there is some if-then-else mojo in there.
        // we find the names of the output variables of the case splits, and...
        val valNames = prog.case_splits.programs(0)._2.output_variables.map(ov => ov.name)
        val valCount = valNames.size
        // ...prepare a symbol for each of them.
        valNames.foreach(vn => {
          val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "csOut")).setInfo(definitions.IntClass.tpe)
          map = map + (vn -> newSym)
        })

        // generates the big case split (hopefully)
        val bigIteExpr: Tree = prog.case_splits.programs.foldRight[Tree](throwTree)((condProgPair: (PACondition,PAProgram), rest: Tree) => {
          If(conditionToCode(map, condProgPair._1), programToCode(map, PACondition(Nil,PATrue()), condProgPair._2, false), rest) 
        })

        if (valCount == 1) {
          List(ValDef(map(valNames.head), bigIteExpr))
        } else {
          val tempTupleSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "tempTuple$")).setInfo(definitions.tupleType(valNames.map(n => definitions.IntClass.tpe)))
          ValDef(tempTupleSym, bigIteExpr) :: (
            for(val c <- 0 until valCount) yield ValDef(map(valNames(c)), Select(Ident(tempTupleSym), definitions.tupleField(valCount, (c+1))))
          ).toList
        }
      } else {
        Nil
      }

      var outputAss: List[Tree] = Nil
      prog.output_assignment.foreach(oa => {
        val (nmap, ntree) = assign(map, oa._1.name, oa._2)
        map = nmap
        outputAss = ntree :: outputAss
      })
      outputAss = outputAss.reverse

      Block(
        preCheckCode ::: inputAss ::: caseSplitAss ::: outputAss
      ,
      if(prog.output_variables.size == 1) {
        variable(map, prog.output_variables(0).name) 
      } else {
        New(
          TypeTree(definitions.tupleType(prog.output_variables.map(x => definitions.IntClass.tpe))),
          List(prog.output_variables.map(ov => variable(map, ov.name)))
        )
      })
    }

    def apaProgramToCode(initMap: SymbolMap, prec: APACondition, prog: APAProgram, withPrec: Boolean): Tree = {
      var map: SymbolMap = initMap

      if(prec.global_condition == APAFalse()) {
        if(emitWarnings)
          reporter.error(pos, "Synthesis predicate will never be satisfiable.")

        return throwTree // trick so that the code still typechecks
      }

      val preCheckCode: List[Tree] = if(withPrec && !(prec.global_condition == APATrue() && prec.pf == APAEmptySplitCondition())) {
        List(If(Select(apaConditionToCode(map,prec), nme.UNARY_!), throwTree, EmptyTree))
      } else {
        Nil
      }

      var inputAssignments: List[Tree] = Nil
      prog.input_assignment.foreach(ia => {
        val (nmap, nTrees) = apaInputAssign(map, ia)
        map = nmap
        inputAssignments = inputAssignments ::: nTrees
      })

      val caseSplitAssignments: List[Tree] = prog.case_splits match {
        case APAFalseSplit() => List(throwTree)
        case APAEmptySplit() => Nil
        case APACaseSplit(programs) => if(programs.size != 0) {
          // extract the magic.
          val valNames = programs(0)._2.output_variables.map(ov => ov.name)
          val valCount = valNames.size
          valNames.foreach(vn => {
            val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "y")).setInfo(definitions.IntClass.tpe)
            map = map + (vn -> newSym)
          })
 
          val iteExpr: Tree = programs.foldRight[Tree](throwTree)((condProgPair: (APACondition, APAProgram), rest: Tree) => {
            If(apaConditionToCode(map, condProgPair._1), apaProgramToCode(map, APACondition(Nil, APATrue(), APAEmptySplitCondition()), condProgPair._2, false), rest)
          })

          if (valCount == 1) {
            List(ValDef(map(valNames.head), iteExpr))
          } else {
            val tempTupleSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "tempTuple")).setInfo(definitions.tupleType(valNames.map(n => definitions.IntClass.tpe)))
            ValDef(tempTupleSym, iteExpr) :: (
              for(val c <- 0 until valCount) yield ValDef(map(valNames(c)), Select(Ident(tempTupleSym), definitions.tupleField(valCount, (c+1))))
            ).toList
          }
        } else {
          Nil
        } // : List[(APACondition, APAProgram)] 
        case a @ APAForSplit(vs, lb, ub, cond, prog) => {
          //println("AAA : " + a)
          //println("VS : " + vs)
          //println("LB : " + lb)
          //println("UB : " + ub)
          //println("CD : " + cond)
          //println("PR : " + prog)

          val valNames = prog.output_variables.map(ov => ov.name)
          val valCount = valNames.size
          // note that these are mutable.
          val valSyms: List[Symbol] = valNames.map(vn => {
            val newSym = owner.newVariable(NoPosition, unit.fresh.newName(NoPosition, "y")).setInfo(definitions.IntClass.tpe)
            map = map + (vn -> newSym)
            newSym
          })

          val fSym = owner.newVariable(NoPosition, unit.fresh.newName(NoPosition, "f")).setInfo(definitions.BooleanClass.tpe)
          val lbSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "lb")).setInfo(definitions.IntClass.tpe)
          val ubSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "ub")).setInfo(definitions.IntClass.tpe)
          val counterSyms = vs.map(iv => {
          val newSym = owner.newVariable(NoPosition, unit.fresh.newName(NoPosition, "y")).setInfo(definitions.IntClass.tpe)
            map = map + (iv.name -> newSym)
            newSym
          })
          
          val beforeLoopAssignments: List[Tree] = List(
            ValDef(fSym, Literal(Constant(false))),
            ValDef(lbSym, apaInTermToCode(map, lb)),
            ValDef(ubSym, apaInTermToCode(map, ub))) :::
            counterSyms.map(cs => ValDef(cs, Ident(lbSym))) :::
            valSyms.map(vs => ValDef(vs, Literal(Constant(0))))

          val condAssTree: Tree = If(apaConditionToCode(map, cond), Block(List(Assign(Ident(fSym), Literal(Constant(true)))), apaProgramToCode(map, APACondition(Nil, APATrue(), APAEmptySplitCondition()), prog, false)), EmptyTree)
            val nestedLoops = counterSyms.foldRight(condAssTree)((nextSym: Symbol, tr: Tree) => {
              makeForLoop(nextSym, Apply(Select(Select(Ident(fSym), nme.UNARY_!), nme.ZAND), List(Apply(Select(Ident(nextSym), nme.LE), List(Ident(ubSym))))), tr)
            })

          beforeLoopAssignments ::: List(nestedLoops, If(Select(Ident(fSym), nme.UNARY_!), throwTree, EmptyTree))
        }
      }

      var outputAssignments: List[Tree] = Nil
      prog.output_assignment.foreach(oa => {
        val (nmap, ntree) = apaAssign(map, oa._1.name, oa._2)
        map = nmap
        outputAssignments = ntree :: outputAssignments
      })
      outputAssignments = outputAssignments.reverse

      Block(
        preCheckCode ::: inputAssignments ::: caseSplitAssignments ::: outputAssignments,
        if(prog.output_variables.size == 1) {
          variable(map, prog.output_variables(0).name)
        } else {
          New(
            TypeTree(definitions.tupleType(prog.output_variables.map(x => definitions.IntClass.tpe))),
            List(prog.output_variables.map(ov => variable(map, ov.name)))
          )
        }
      )
    }
  
    def termToCode(map: SymbolMap, term: PATerm): Tree = term match {
      case PADivision(num, den) => {
        // num / den actually generates:
        // { val N = ''num''; (N - ((den + N % den) % den)) / den }
        // (floored integer division, where -1 / 2 = -1 (w. rest 1))
        val numTree = termToCode(map, num)
        val denTree = Literal(Constant(den))
        flooredDivision(numTree, denTree)
      }
      case PAMinimum(terms) => {
        def binaryMin(t1:Tree,t2:Tree): Tree = {
          Apply(Select(Select(Ident(scalaPack), scalaMath), scalaMathMin), List(t1, t2))
        }

        terms.map(termToCode(map,_)).reduceLeft((t1,t2) => binaryMin(t1,t2))
      }
      case PAMaximum(terms) => {
        def binaryMax(t1:Tree,t2:Tree): Tree = {
          Apply(Select(Select(Ident(scalaPack), scalaMath), scalaMathMax), List(t1, t2))
        }
        terms.map(termToCode(map,_)).reduceLeft((t1,t2) => binaryMax(t1,t2))
      }
      case PACombination(cst, inAff, outAff) => (inAff,outAff) match {
        case (Nil,Nil) => Literal(Constant(cst))
        case _ => {
          val factorList: List[(Int,String)] = inAff.map(ia => (ia._1,ia._2.name)) ::: outAff.map(oa => (oa._1,oa._2.name))
          val prodList: List[Tree] = factorList.map(isp => {
            if(isp._1 == 0)
              Literal(Constant(0))
            else if(isp._1 == 1)
              variable(map, isp._2)
            else
              Apply(Select(Literal(Constant(isp._1)), nme.MUL), List(variable(map, isp._2)))
          })
          (if (cst == 0) prodList else Literal(Constant(cst)) :: prodList).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ADD), List(t2)))
        }
      }
    }

    def formulaToCode(map: SymbolMap, form: PAFormula): Tree = form match {
      case PAConjunction(fs) => {
        fs.map(formulaToCode(map,_)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ZAND), List(t2)))
      }
      case PADisjunction(fs) => {
        fs.map(formulaToCode(map,_)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ZOR), List(t2)))
      }
      case PADivides(coef,comb) => Apply(Select(Apply(Select(termToCode(map,comb), nme.MOD), List(Literal(Constant(coef)))), nme.EQ), List(Literal(Constant(0))))
      case PAEqualZero(comb) => Apply(Select(termToCode(map,comb), nme.EQ), List(Literal(Constant(0))))
      case PAGreaterZero(comb) => Apply(Select(termToCode(map,comb), nme.GT), List(Literal(Constant(0))))
      case PAGreaterEqZero(comb) => Apply(Select(termToCode(map,comb), nme.GE), List(Literal(Constant(0))))
      case PATrue() => Literal(Constant(true))
      case PAFalse() => Literal(Constant(false))
    }

    def apaFormulaToCode(map: SymbolMap, form: APAFormula): Tree = form match {
      case APAConjunction(fs) => {
        fs.map(apaFormulaToCode(map,_)).reduceLeft((t1:Tree, t2:Tree) => Apply(Select(t1, nme.ZAND), List(t2)))
      }
      case APADisjunction(fs) => {
        fs.map(apaFormulaToCode(map,_)).reduceLeft((t1:Tree, t2:Tree) => Apply(Select(t1, nme.ZOR), List(t2)))
      }
      case APANegation(f) => Select(apaFormulaToCode(map, f), nme.UNARY_!)
      case APADivides(coef, apac) => Apply(Select(Apply(Select(apaTermToCode(map, apac), nme.MOD), List(apaInTermToCode(map, coef))), nme.EQ), List(Literal(Constant(0))))
      case APAEqualZero(apac) => Apply(Select(apaTermToCode(map, apac), nme.EQ), List(Literal(Constant(0))))
      case APAGreaterZero(apac) => Apply(Select(apaTermToCode(map, apac), nme.GT), List(Literal(Constant(0))))
      case APAGreaterEqZero(apac) => Apply(Select(apaTermToCode(map, apac), nme.GE), List(Literal(Constant(0))))
      case APATrue() => Literal(Constant(true))
      case APAFalse() => Literal(Constant(false))
    }

    def flooredDivision(t1: Tree, t2: Tree): Tree = {
        val numSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "n")).setInfo(definitions.IntClass.tpe)
        val denSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "d")).setInfo(definitions.IntClass.tpe)
        val numTree = Ident(numSym) 
        val denTree = Ident(denSym)
        Block(
          List(
            ValDef(numSym, t1),
            ValDef(denSym, t2)),
          Apply(
            Select(
              Apply(
                Select(
                  numTree,
                  nme.SUB),
                List(
                  Apply(
                    Select(
                      Apply(Select(denTree, nme.ADD), List(Apply(Select(numTree,nme.MOD), List(denTree)))),
                      nme.MOD),
                    List(denTree))
                  )),
              nme.DIV),
            List(denTree)
        ))
    }

    def apaTermToCode(map: SymbolMap, term: APATerm): Tree = term match {
      case APADivision(num, den) => {
        // num / den actually generates:
        // { val N = ''num''; val D = ''den''; (N - ((D + N % D) % D)) / D }
        // (floored integer division, where -1 / 2 = -1 (w. rest 1))
        flooredDivision(apaTermToCode(map, num), apaInTermToCode(map, den))
      }
      case APAMinimum(terms) => {
        def binaryMin(t1:Tree,t2:Tree): Tree = {
          Apply(Select(Select(Ident(scalaPack), scalaMath), scalaMathMin), List(t1, t2))
        }

        terms.map(apaTermToCode(map,_)).reduceLeft((t1,t2) => binaryMin(t1,t2))
      }
      case APAMaximum(terms) => {
        def binaryMax(t1:Tree,t2:Tree): Tree = {
          Apply(Select(Select(Ident(scalaPack), scalaMath), scalaMathMax), List(t1, t2))
        }
        terms.map(apaTermToCode(map,_)).reduceLeft((t1,t2) => binaryMax(t1,t2))
      }
      case APACombination(cstInTerm, outAff) => outAff match {
        case Nil => apaInTermToCode(map, cstInTerm)
        case _ => {
          val factorList: List[(Tree,String)] = outAff.map(oa => (apaInTermToCode(map, oa._1) ,oa._2.name))
          val prodList: List[Tree] = factorList.map(isp => {
            Apply(Select(isp._1, nme.MUL), List(variable(map, isp._2)))
          })
          (apaInTermToCode(map, cstInTerm) :: prodList).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ADD), List(t2)))
        }
      }
    }

    def apaInTermToCode(map: SymbolMap, term: APAInputTerm): Tree = term match {
      case APAInputCombination(intCst, inAff) => inAff match {
        case Nil => Literal(Constant(intCst))
        case _ => {
          val factorList: List[(Int,String)] = inAff.map(ia => (ia._1,ia._2.name))
          val prodList: List[Tree] = factorList.map(isp => {
            if(isp._1 == 0)
              Literal(Constant(0))
            else if(isp._1 == 1)
              variable(map, isp._2)
            else
              Apply(Select(Literal(Constant(isp._1)), nme.MUL), List(variable(map, isp._2)))
          })
          (if (intCst == 0) prodList else Literal(Constant(intCst)) :: prodList).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ADD), List(t2)))
        }
      }
      case APAInputDivision(nums, dens) => {
        val num: Tree = nums.map(apaInTermToCode(map, _)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.MUL), List(t2)))
        val den: Tree = dens.map(apaInTermToCode(map, _)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.MUL), List(t2)))
        //Apply(Select(num, nme.DIV), List(den))
        flooredDivision(num, den)
      }
      case APAInputMultiplication(ops) => ops.map(apaInTermToCode(map, _)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.MUL), List(t2)))
      case APAInputAddition(ops) => ops.map(apaInTermToCode(map, _)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ADD), List(t2)))
      case APAInputAbs(term) => Apply(Select(Select(Ident(scalaPack), scalaMath), scalaMathAbs), List(apaInTermToCode(map, term)))
      case APAInputGCD(ops) => Apply(Select(Select(Ident(synthesisPack), synthesisCommon), gcdFunction), List(Apply(Ident(definitions.ListModule), ops.map(apaInTermToCode(map, _)))))
      case APAInputLCM(ops) => Apply(Select(Select(Ident(synthesisPack), synthesisCommon), lcmFunction), List(Apply(Ident(definitions.ListModule), ops.map(apaInTermToCode(map, _)))))
    }

    def conditionToCode(topMap: SymbolMap, cond: PACondition): Tree = {
      var map: SymbolMap = topMap
      var inputAss: List[Tree] = Nil
      cond.input_assignment.foreach(ia => {
        val (nmap, ntree) = assign(map, ia._1.name, ia._2)
        map = nmap
        inputAss = ntree :: inputAss
      })
      inputAss = inputAss.reverse
      Block(inputAss, formulaToCode(map, cond.global_condition)) 
    }

    def apaConditionToCode(topMap: SymbolMap, cond: APACondition): Tree = {
      var map: SymbolMap = topMap
      var inputAss: List[Tree] = Nil
      cond.input_assignment.foreach(ia => {
        val (nmap, ntrees) = apaInputAssign(map, ia)
        map = nmap
        inputAss = inputAss ::: ntrees
      })
      Block(inputAss, Apply(Select(apaFormulaToCode(map, cond.global_condition), nme.ZAND), List(apaSplitConditionToCode(map, cond.pf))))
    }

    def apaSplitConditionToCode(topMap: SymbolMap, splitCond: APASplitCondition): Tree = splitCond match {
      case APAForCondition(vs, lb, ub, cond) => {
        var newMap: SymbolMap = topMap
        val fSym = owner.newVariable(NoPosition, unit.fresh.newName(NoPosition, "f")).setInfo(definitions.BooleanClass.tpe)
        val lbSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "lb")).setInfo(definitions.IntClass.tpe)
        val ubSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "ub")).setInfo(definitions.IntClass.tpe)
        val counterSyms: List[Symbol] = vs.map((v:synthesis.InputVar) => {
          val newSym = owner.newVariable(NoPosition, unit.fresh.newName(NoPosition, "i")).setInfo(definitions.IntClass.tpe)
          newMap = newMap + (v.name -> newSym)
          newSym
        })

        val initialAssignments: List[Tree] = List(
          ValDef(fSym, Literal(Constant(false))),
          ValDef(lbSym, apaInTermToCode(topMap, lb)),
          ValDef(ubSym, apaInTermToCode(topMap, ub))) :::
          counterSyms.map(cs => ValDef(cs, Ident(lbSym)))


        val condAssTree: Tree = If(apaConditionToCode(newMap, cond), Assign(Ident(fSym), Literal(Constant(true))), EmptyTree)
        val nestedLoops = counterSyms.foldRight(condAssTree)((nextSym: Symbol, tr: Tree) => {
          makeForLoop(nextSym, Apply(Select(Select(Ident(fSym), nme.UNARY_!), nme.ZAND), List(Apply(Select(Ident(nextSym), nme.LE), List(Ident(ubSym))))), tr)
        })

        Block(
          initialAssignments ::: List(
            nestedLoops
          ),
          Ident(fSym)
        )
      }
      case APAEmptySplitCondition() => Literal(Constant(true))
      case APACaseSplitCondition(cs) => cs.map(c => c match {
        case apac: APACondition => apaConditionToCode(topMap, apac)
        case apasc: APASplitCondition => apaSplitConditionToCode(topMap, apasc)
      }).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ZOR), List(t2)))

      case _ => scala.Predef.error("Should be unreachable.")
    }

    // builds a for loop which increments the counter while condTree holds
    def makeForLoop(counter: Symbol, condTree: Tree, body: Tree): Tree = {
      val label = owner.newLabel(NoPosition, unit.fresh.newName(NoPosition, "forloop$")).setInfo(MethodType(Nil, definitions.UnitClass.tpe))
      val continu = Apply(Ident(label), Nil)
      val rhs = If(condTree, Block(body :: Assign(Ident(counter), Apply(Select(Ident(counter), nme.ADD), List(Literal(Constant(1))))) :: Nil, continu), EmptyTree)
      LabelDef(label, Nil, rhs)
    }

    def setTermToCode(map: SymbolMap, term: bapa.ASTBAPASyn.BASet, baseTypeTree: TypeTree): Tree = term match {
      case bapa.ASTBAPASyn.SetVar(name) => variable(map, name)
      case bapa.ASTBAPASyn.EmptySet => /*TypeApply(*/Select(Select(Select(Select(Ident(scalaPack), scalaCollection), scalaCollectionImmutable), scalaCollectionImmutableSetModule), setEmpty)//, List(baseTypeTree)) 
      case bapa.ASTBAPASyn.Union(s1,s2) => Apply(Select(setTermToCode(map,s1,baseTypeTree), nme.PLUSPLUS), List(setTermToCode(map,s2,baseTypeTree)))
      case bapa.ASTBAPASyn.Intersec(s1, bapa.ASTBAPASyn.Compl(s2)) => Apply(Select(setTermToCode(map,s1,baseTypeTree), encode("--")), List(setTermToCode(map,s2,baseTypeTree)))
      case bapa.ASTBAPASyn.Intersec(bapa.ASTBAPASyn.Compl(s1), s2) => Apply(Select(setTermToCode(map,s2,baseTypeTree), encode("--")), List(setTermToCode(map,s1,baseTypeTree)))
      case bapa.ASTBAPASyn.Intersec(s1,s2) => Apply(Select(setTermToCode(map,s1,baseTypeTree), encode("**")), List(setTermToCode(map,s2,baseTypeTree)))
      case _ => {
        //setTermToCode(map, bapa.ASTBAPASyn.EmptySet, baseTypeTree) 
        scala.Predef.error("Don't know what to do with : " + term)
      }
    }

    def setIntTermToCode(map: SymbolMap, term: bapa.ASTBAPASyn.PAInt, baseTypeTree: TypeTree): Tree = term match {
      case bapa.ASTBAPASyn.IntVar(name) => variable(map, name)
      case bapa.ASTBAPASyn.IntConst(c) => Literal(Constant(c))
      case bapa.ASTBAPASyn.Plus(t1,t2) => Apply(Select(setIntTermToCode(map,t1,baseTypeTree), nme.ADD), List(setIntTermToCode(map,t2,baseTypeTree)))
      case bapa.ASTBAPASyn.Times(coef,t2) => Apply(Select(setIntTermToCode(map,t2,baseTypeTree), nme.MUL), List(Literal(Constant(coef))) )
      case bapa.ASTBAPASyn.Card(st) => Select(setTermToCode(map,st,baseTypeTree), "size")
    }
  }
}
