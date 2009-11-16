package synthesis

import scala.collection.immutable.Map

trait CodeGeneration {
  self: ChooseTransformer =>
  import global._
  import PASynthesis._

  type SymbolMap = Map[String,Symbol]

  private lazy val unsatConstraintsException: Symbol = definitions.getClass("synthesis.Definitions.UnsatisfiableConstraint")
  private lazy val scalaPack: Symbol = definitions.ScalaPackage
  private lazy val scalaMath: Symbol = definitions.getModule("scala.Math")
  private lazy val scalaMathMin: Symbol = definitions.getMember(scalaMath, "min")
  private lazy val scalaMathMax: Symbol = definitions.getMember(scalaMath, "max")
  
  class CodeGenerator(val unit: CompilationUnit, val owner: Symbol, val initialMap: SymbolMap) {
    import scala.tools.nsc.util.NoPosition

    // defines a new variable and returns a new symbol map with it
    private def assign(map: SymbolMap, varNme: String, expr: PATerm): (SymbolMap,Tree) = {
      val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "synLoc")).setInfo(definitions.IntClass.tpe)
      (map + (varNme -> newSym), ValDef(newSym, termToCode(map, expr)))
    }

    private def variable(map: SymbolMap, varNme: String): Tree = {
      Ident(map(varNme))
    }
  
    def programToCode(prec: PACondition, prog: PAProgram): Tree = 
      programToCode(initialMap, prec, prog)

    def programToCode(initMap: SymbolMap, prec: PACondition, prog: PAProgram): Tree = {
      var map: SymbolMap = initMap

      val throwTree = Throw(New(Ident(unsatConstraintsException), List(Nil)))

      val preCheckCode: List[Tree] = if(prec.global_condition != PATrue()) {
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
          If(conditionToCode(map, condProgPair._1), programToCode(map, PACondition(Nil,PATrue()), condProgPair._2), rest) 
        })

        if (valCount == 1) {
          List(ValDef(map(valNames.head), bigIteExpr))
        } else {
          val tempTupleSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "tempTuple")).setInfo(definitions.tupleType(valNames.map(n => definitions.IntClass.tpe)))
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
  
    def termToCode(map: SymbolMap, term: PATerm): Tree = term match {
      case PADivision(num, den) => {
        // num / den actually generates:
        // { val N = ''num''; (N - ((den + N % den) % den)) / den }
        // (floored integer division, where -1 / 2 = -1 (w. rest 1))
        val numSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "divNum")).setInfo(definitions.IntClass.tpe)
        val numTree = Ident(numSym) 
        val denTree = Literal(Constant(den))
        Block(
          List(ValDef(numSym, termToCode(map,num))),
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
      case eq: PAEquation => equationToCode(map, eq)
      case PAConjunction(fs) => {
        fs.map(formulaToCode(map,_)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ZAND), List(t2)))
      }
      case PADisjunction(fs) => {
        fs.map(formulaToCode(map,_)).reduceLeft((t1:Tree,t2:Tree) => Apply(Select(t1, nme.ZOR), List(t2)))
      }
    }
  
    def equationToCode(map: SymbolMap, eq: PAEquation): Tree = eq match {
      case PADivides(coef,comb) => Apply(Select(Apply(Select(termToCode(map,comb), nme.MOD), List(Literal(Constant(coef)))), nme.EQ), List(Literal(Constant(0))))
      case PAEqualZero(comb) => Apply(Select(termToCode(map,comb), nme.EQ), List(Literal(Constant(0))))
      case PAGreaterZero(comb) => Apply(Select(termToCode(map,comb), nme.GT), List(Literal(Constant(0))))
      case PAGreaterEqZero(comb) => Apply(Select(termToCode(map,comb), nme.GE), List(Literal(Constant(0))))
      case PATrue() => Literal(Constant(true))
      case PAFalse() => Literal(Constant(false))
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
  }
}
