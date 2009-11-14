package synthesis

import scala.collection.immutable.Map

trait CodeGeneration {
  self: ChooseTransformer =>
  import global._
  import PASynthesis._

  type SymbolMap = Map[String,Symbol]

  class CodeGenerator(val unit: CompilationUnit, val owner: Symbol, initMap: SymbolMap) {
    private val initialMap: SymbolMap = initMap
    private lazy val scalaPack: Symbol = definitions.ScalaPackage
    private lazy val scalaMath: Symbol = definitions.getModule("scala.Math")
    private lazy val scalaMathMin: Symbol = definitions.getMember(scalaMath, "min")
    private lazy val scalaMathMax: Symbol = definitions.getMember(scalaMath, "max")

    // defines a new variable and returns a new symbol map with it
    private def assign(map: SymbolMap, varNme: String, expr: PATerm): (SymbolMap,Tree) = {
      import scala.tools.nsc.util.NoPosition
      val newSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "synLoc")).setInfo(definitions.IntClass.tpe)
      (map + (varNme -> newSym), ValDef(newSym, termToCode(map, expr)))
    }

    private def variable(map: SymbolMap, varNme: String): Tree = {
      Ident(map(varNme))
    }
  
    def programToCode(prec: PACondition, prog: PAProgram): Tree = {
      var map: SymbolMap = initialMap
      var inputAss: List[Tree] = Nil
      prog.input_assignment.foreach(ia => {
        val (nmap, ntree) = assign(map, ia._1.name, ia._2)
        map = nmap
        inputAss = ntree :: inputAss
      })
      inputAss = inputAss.reverse

      var outputAss: List[Tree] = Nil
      prog.output_assignment.foreach(oa => {
        val (nmap, ntree) = assign(map, oa._1.name, oa._2)
        map = nmap
        outputAss = ntree :: outputAss
      })
      outputAss = outputAss.reverse

      Block(
        inputAss ::: outputAss
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
      case PADivision(num, den) => Apply(Select(termToCode(map,num), nme.DIV), List(Literal(Constant(den))))
      case PAIfThenElse(cond, then, elze) => scala.Predef.error("X") // equationToCode 
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
        //case ((1,iv)::Nil,Nil) if cst == 0 => variable(map,iv.name)
        //case (Nil,(1,ov)::Nil) if cst == 0 => variable(map,ov.name)
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
  
    def equationToCode(map: SymbolMap, eq: PAEquation): Tree = eq match {
      case PADivides(coef,comb) => scala.Predef.error("YYY")
      case PAEqualZero(comb) => scala.Predef.error("YYY")
      case PAGreaterZero(comb) => scala.Predef.error("YYY")
      case PAGreaterEqZero(comb) => scala.Predef.error("YYY")
      case PATrue() => Literal(Constant(true))
      case PAFalse() => Literal(Constant(false))
    }

    def conditionToCode(map: SymbolMap, cond: PACondition): Tree = {
      scala.Predef.error("NOT IMPLEMENTED YET")
    }
  }
}
