package synthesis

import Arithmetic._

import scala.collection.immutable.Set

import scala.tools.nsc.transform.TypingTransformers

// import scala.tools.nsc.util.NoPosition

trait ChooseTransformer
  extends TypingTransformers
  with ArithmeticExtractors
  with CodeGeneration {
  self: MainComponent =>
  import global._

  def tupleField(n: Int, j: Int): TermSymbol = definitions.getMemberValue(definitions.TupleClass(n), nme.productAccessorName(j))

  private val SHOWDEBUGINFO = false
  private def dprintln(str: Any): Unit = {
    if(SHOWDEBUGINFO)
      println(str.toString)
  }
  private val SHOWAPADEBUGINFO = false
  private def ddprintln(str: Any): Unit = {
    if(SHOWAPADEBUGINFO)
      println(str.toString)
  }

  private lazy val synthesisPackage: Symbol = rootMirror.getRequiredModule("synthesis")
  private lazy val synthesisDefinitionsModule: Symbol = rootMirror.getRequiredModule("synthesis.Definitions")
  private lazy val immutableSetTraitSymbol = rootMirror.getRequiredClass("scala.collection.immutable.Set")

  /** The actual rewriting function is the following. */
  def transformChooseCalls(unit: CompilationUnit, emitWarnings: Boolean): Unit =
    unit.body = new ChooseTransformer(unit, emitWarnings).transform(unit.body)

  class ChooseTransformer(unit: CompilationUnit, val emitWarnings: Boolean) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if(synthesisDefinitionsModule == s.symbol && n.toString == "choose" && predicate.vparams(0).tpt.tpe == definitions.IntClass.tpe) => {
          // SANITY CHECKS
          var foundErrors = false
          // DEBUG reporter.info(a.pos, "here!", true)
          val Function(funValDefs, funBody) = predicate

          // we check that we're only synthesizing integers, and collect the
          // set of input variables
          // for (valDef <- funValDefs) {
          //   if(valDef.tpt.tpe != definitions.IntClass.tpe) {
          //     reporter.error(valDef.pos, "unsupported type in call to synthesizer: " + valDef.tpt.tpe)
          //     foundErrors = true
          //   }
          // }
          // if (foundErrors)
          //   return a

          // for the record
          val outputVariableList = funValDefs.map(_.name.toString)

          // EXTRACTION
          val (extractedFormula,extractedSymbols) =
           extractFormula(funBody) match {
            case Some((f,s)) => (normalized(f), s.filter((sym: Symbol) => !outputVariableList.contains(sym.name.toString)))
            case None => {
              foundErrors = true
              (False(),Set.empty[Symbol])
            }
          }
          if (foundErrors)
            return a

          dprintln("Corresponding formula: " + extractedFormula)
          dprintln("Symbols in there     : " + extractedSymbols)

          // ALTERNATIVE LINEARIZATION
          val apaStyleFormula: APAFormula = formulaToAPAFormula2(extractedFormula, Set.empty[String] ++ outputVariableList) match {
            case Some(f) => f
            case None => {
              reporter.error(funBody.pos, "predicate is not in parametrized linear arithmetic")
              foundErrors = true
              APAFalse()
            }
          }

          ddprintln("IQL : " + isQuasiLinear(extractedFormula, Set.empty[String] ++ outputVariableList))

          if (foundErrors) {
            return a
          }

          // We check for uniqueness of the solution.
          if(emitWarnings) {
            val outVars = Set.empty ++ outputVariableList
            val (fcopy,toMap,fromMap) = renameVarSet(extractedFormula, outVars)
            val diseqs: List[Formula] = toMap.map(p => NotEquals(Variable(p._1), Variable(p._2))).toList
            val completeFormula = And(extractedFormula :: fcopy :: Or(diseqs) :: Nil)
            isSat(completeFormula) match {
              case (Some(true), Some(ass)) => {
                var wm = "Synthesis predicate has multiple solutions for variable assignment: "
                wm = wm + ass.keys.filter(k => !toMap.keys.toList.contains(k) && !fromMap.keys.toList.contains(k)).toList.map(k => k + " = " + ass(k)).mkString(", ")
                wm = wm + "\n"
                wm = wm + "  Solution 1: " + outVars.toList.map(k => k + " = " + ass(k)).mkString(", ") + "\n"
                wm = wm + "  Solution 2: " + outVars.toList.map(k => k + " = " + ass(toMap(k))).mkString(", ") + "\n"
                reporter.info(a.pos, wm, true)
              }
              case (Some(false), _) => ; // desirable: solution is always unique if it exists
              case (_,_) => reporter.info(a.pos, "Synthesis predicate may not always have a unique solution (decision procedure did not respond).", true)
            }
          }

          //val (apaPrec, apaProg) = APASynthesis.solve(mikaelsAST) //apaStyleFormula)
          val (apaPrec, apaProg) = APASynthesis.solve(apaStyleFormula)
          //ddprintln("APA-Style formula : " + mikaelsAST) // apaStyleFormula)
          ddprintln("APA-Style formula : " + apaStyleFormula)
          ddprintln("APA precond       : " + apaPrec)
          ddprintln("APA program       : " + apaProg)

          //val (paPrec,paProg) = PASynthesis.solve(outputVariableList.map(PASynthesis.OutputVar(_)), paStyleFormula)
          //dprintln("Mikael-Style formula : " + paStyleFormula)
          //dprintln("Precondition         : " + paPrec)
          //dprintln("Program              : " + paProg)

          // We try to falsify the pre-condition.
          if(emitWarnings && !(apaPrec.global_condition == APATrue() && apaPrec.pf == APAEmptySplitCondition())) {
            apaConditionToFormula(apaPrec) match {
              case None => reporter.info(a.pos, "Synthesis predicate may not always be satisfiable (decision procedure could not handle the non-linear precondition).", true)
              case Some(myStyle) if(myStyle != False()) => {
                dprintln("My-style: " + myStyle)
                isSat(Not(myStyle)) match {
                  case (Some(true), Some(ass)) => {
                    reporter.info(a.pos, "Synthesis predicate is not satisfiable for variable assignment: " + ass.map(p => p._1 + " = " + p._2).mkString(", "), true)

                  }
                  case (Some(false), _) => ;
                  case (_,_) => reporter.info(a.pos, "Synthesis predicate may not always be satisfiable (decision procedure did not respond).", true)
                }
              }
              case Some(_) => ; // we would already have a warning.
            }
          }

          // CODE GENERATION
          var initialMap: SymbolMap = Map.empty
          extractedSymbols.foreach(sym => {
            initialMap = initialMap + (sym.name.toString -> sym)
          })
          val codeGen = new CodeGenerator(unit, currentOwner, initialMap, emitWarnings, a.pos)
          val generated = codeGen.apaProgramToCode(apaPrec, apaProg, true)

          typer.typed(atOwner(currentOwner) {
            generated
          })
        }
        // END OF CODE GENERATION FOR CHOOSE STATS FOR PARAM. LINEAR ARITH.

        case m @ Match(selector, cases)
          if isSubType(selector.tpe, definitions.IntClass.tpe)
            && cases.forall(cse => cse.guard == EmptyTree) => {
          //reporter.info(m.pos, "I'm inside a synth. PM expression.", true)

          val scrutSym = selector match {
            case i @ Ident(_) if i.symbol.isStable => i.symbol
            case _ => currentOwner.newValue(unit.freshTermName("scrutinee"), selector.pos).setInfo(selector.tpe)
          }
          val scrutName: String = scrutSym.name.toString

          var patternConditionPairs: List[(Tree,Formula)] = Nil
          var encounteredNonArith: Boolean = false
          var allAreNotArith: Boolean = true
          val newCases = cases.map(cse => {
            extractExtractors(cse.pat) match {
              case Some((formula,inVars,outVars,wildcards)) => {
                formula match {
                  case Times(_) | Plus(_) | Minus(_,_) => allAreNotArith = false
                  case _ => ;
                }
                val frm = normalized(Equals(formula, Variable(scrutName)))

                val outVarSyms: List[Symbol] = outVars.toList
                val realOutVarList: List[String] = outVarSyms.map(_.name.toString) ::: wildcards.toList
                val realOutVarSet: Set[String] = Set.empty ++ realOutVarList

                formulaToPAFormula(frm, realOutVarSet) match {
                  case Some(f) => { // means the formula was linear arithmetic
                                    // and could be transformed to Mikael's format
                    val paStyle: PASynthesis.PAFormula = f
                    dprintln(frm)
                    dprintln(paStyle)
                    val (paPrec,paProg) = PASynthesis.solve(realOutVarList.map(PASynthesis.OutputVar(_)), paStyle)

                    patternConditionPairs = (cse.pat, conditionToFormula(paPrec)) :: patternConditionPairs

                    var initialMap: SymbolMap = Map(scrutName -> scrutSym)
                    inVars.foreach(sym => {
                      initialMap = initialMap + (sym.name.toString -> sym)
                    })
                    val codeGen = new CodeGenerator(unit, currentOwner, initialMap, emitWarnings, cse.pat.pos)
                    val generatedCode: Tree = if(outVars.isEmpty) {
                      // note that we ignore the case where we only have to
                      // generate code for the wildcards, since we know their
                      // values won't be used on this side
                      cse.body
                    } else {
                      // we build new symbols
                      val newOutSyms = outVarSyms.map(s =>
                        currentOwner.newValue(unit.freshTermName(s.name.toString), s.pos).setInfo(definitions.IntClass.tpe)
                      )
                      //val wcSyms = wildcards.toList.map(w =>
                      //  currentOwner.newValue(cse.pat.pos, unit.fresh.newName(cse.pat.pos, "wc$")).setInfo(definitions.IntClass.tpe)
                      //)
                      val symSubst = new TreeSymSubstituter(outVarSyms, newOutSyms)
                      // this generates code that returns a tuple.
                      val computedTuple = symSubst(codeGen.programToCode(paPrec, paProg, false))
                      if (realOutVarList.size == 1) {
                        // we know it's not a wildcard, because of the check
                        // above. We only have to assign it, since the symbol
                        // was in the binder, it should be the same in the
                        // expression to the right.
                        Block(
                          ValDef(newOutSyms.head, computedTuple) :: Nil,
                          symSubst(cse.body)
                        )
                      } else {
                        val outVarCount = outVarSyms.size
                        val tupleHolderSym = currentOwner.newValue(unit.freshTermName("t"), cse.pat.pos).setInfo(definitions.tupleType(realOutVarList.map(n => definitions.IntClass.tpe)))

                        Block(
                          ValDef(tupleHolderSym, computedTuple) :: (
                          for(c <- 0 until outVarCount) yield
                            ValDef(newOutSyms(c), Select(Ident(tupleHolderSym), tupleField(realOutVarList.size, (c+1))))
                          ).toList, // :::
//                          for(c <- 0 until wcSyms.size) :: (
//                            ValDef(wcSyms(c), Select(Ident(tupleHolderSym), tupleField(realOutVarList.size, (c+1+outVarCount))))
//                          ).toList,
                          symSubst(cse.body)
                        )
                      }
                    }

                    // build the new casedef
                    CaseDef(
                      Ident(nme.WILDCARD), // always matches on anything...
                      codeGen.conditionToCode(initialMap, paPrec), // ...guard does the job
                      generatedCode
                    )
                  }
                  case None => {
                    encounteredNonArith = true
                    reporter.error(cse.pat.pos, "Pattern is not linear arithmetic.")
                    cse
                  }
                }
              }
              case None => { encounteredNonArith = true; cse }
            }
          })

          if(allAreNotArith) {
            return super.transform(m)
          }

          if(encounteredNonArith) {
            reporter.error(m.pos, "Not all patterns are linear-arithmetic.")
            return super.transform(m)
          }

          if(emitWarnings) {
            // checks for completeness
            patternConditionPairs = patternConditionPairs.reverse
            val compForm = Not(Or(patternConditionPairs.map(_._2)))
            isSat(compForm) match {
              case (Some(true), Some(ass)) => {
                val assStr = variablesOf(compForm).toList.map(vn => vn + " = " + ass(vn)).mkString(", ")
                reporter.info(m.pos, "Match is not exhaustive. It will fail for the values: " + assStr, true)
              }
              case (Some(false), _) => ; // means PM is exhaustive
              case (None,_) => reporter.info(m.pos, "Match may not be exhaustive (decision procedure did not respond).", true)
            }

            // checks for reachability
            var foundUnreachable = false
            for(c <- 0 until patternConditionPairs.size - 1) {
              if(!foundUnreachable) {
                val theOne = patternConditionPairs(c+1)
                val reachForm = And(Not(Or(patternConditionPairs.take(c + 1).map(_._2))), theOne._2)
                isSat(reachForm) match {
                  case (Some(true), _) => ; // desirable, means pattern is reachable.
                  case (Some(false), _) => reporter.info(theOne._1.pos, "Unreachable pattern.", true)
                  case (None, _) => reporter.info(theOne._1.pos, "Pattern may be unreachable (decision procedure did not respond).", true)
                }
              }
            }
          }

          val theCode = selector match {
            case i @ Ident(_) if i.symbol == scrutSym => Match(selector, newCases)
            case _ => Block(
              ValDef(scrutSym, transform(selector))
              :: Nil,
              Match(Ident(scrutSym), newCases)
            )
          }

          typer.typed(atOwner(currentOwner) {
            theCode
          })
        }

        // most likely the ugliest match case you ever encountered.
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if(synthesisDefinitionsModule == s.symbol && n.toString == "choose" && (predicate.vparams(0).tpt.tpe match { case TypeRef(_,sym,_) if (sym == immutableSetTraitSymbol) => true case _ => false })) => {
          // reporter.info(predicate.pos, "in a set choose !!!", true)
          val instantiatedSetType  = predicate.vparams(0).tpt.tpe
          val TypeRef(_, _, List(uletTpe)) = instantiatedSetType
          val underlyingElementType: Type = uletTpe
          val underlyingElementTypeTree: TypeTree = TypeTree(uletTpe)

          // SANITY CHECKS
          var foundErrors = false
          val Function(funValDefs, funBody) = predicate


          val (frml,setVars,intVars) = extractSetFormula(funBody) match {
            case Some((p,s1,s2)) => (p,s1,s2)
            case None => {
              foundErrors = true
              (bapa.ASTBAPASyn.LikeFalse,Set.empty[Symbol],Set.empty[Symbol])
            }
          }
          if(foundErrors)
            return a

          val outSetVarList: List[Symbol] = funValDefs.map(_.symbol)
          val inSetVarList: List[Symbol] = (setVars -- outSetVarList).toList
          val inIntVarList: List[Symbol] = (intVars).toList

          dprintln(frml)
          dprintln("outset vars : " + outSetVarList)
          dprintln("inset  vars : " + inSetVarList)
          dprintln("in int vars : " + inIntVarList)

          val ruzicaStyleTask = bapa.ASTBAPASyn.Task(inSetVarList.map(_.name.toString), outSetVarList.map(_.name.toString), inIntVarList.map(_.name.toString), Nil, frml)

          dprintln(ruzicaStyleTask)

          val (preCardAssigns,frmForSynthesis,linOutVars,asss) = bapa.Algorithm.solve(ruzicaStyleTask, true)
          val myStyleFormula = normalized(bapa.ASTBAPASyn.bapaFormToArithForm(frmForSynthesis))

          dprintln("The cardinality assignments are... " + preCardAssigns)
          dprintln("  ")
          dprintln("And the formula for syntesis is.... " + frmForSynthesis)
          dprintln("  ")
          dprintln("Local out vars : " + linOutVars)
          dprintln("  ")
          dprintln("...and the assignments say: " + asss)
          dprintln("  ")
          dprintln(myStyleFormula)

          // LINEARIZATION
          val mikaelStyleFormula: PASynthesis.PAFormula = formulaToPAFormula(myStyleFormula, Set.empty[String] ++ linOutVars) match {
            case Some(f) => f
            case None => {
              reporter.error(funBody.pos, "predicate contains non-linear arithmetic")
              foundErrors = true
              PASynthesis.PAFalse()
            }
          }
          if (foundErrors)
            return a

          dprintln(mikaelStyleFormula)

          val (paPrec,paProg) = PASynthesis.solve(linOutVars.map(PASynthesis.OutputVar(_)), mikaelStyleFormula)

          // SATisfiability check...
          if(emitWarnings && !(paPrec.global_condition == PASynthesis.PATrue())) {
            val myStyle = conditionToFormula(paPrec)

            if(myStyle != False()) {
              // we need to tell Z3 that sizes of existing sets are not negative.
              val posCardConstraints: Formula = And(preCardAssigns.map(_._1).map((varName: String) => LessEqThan(IntLit(0), Variable(varName))))
              dprintln("card cons: " + posCardConstraints)

              dprintln("My-style: " + myStyle)
              isSat(And(posCardConstraints :: Not(myStyle) :: Nil)) match {
                case (Some(true), Some(ass)) => {
                  val assString = ass.filter(ae => !preCardAssigns.map(_._1).contains(ae._1)).map(p => p._1 + " = " + p._2).mkString(", ")
                  reporter.info(a.pos, "Synthesis predicate is not always satisfiable." + (if (!assString.isEmpty) " (eg. " + assString + ")" else ""), true)
                }
                case (Some(false), _) => ;
                case (_,_) => reporter.info(a.pos, "Synthesis predicate may not always be satisfiable (decision procedure did not respond).", true)
              }
            } else {
              //reporter.info(a.pos, "Synthesis predicate is never satisfiable.", true)
            }
          }
          // end of SAT check.

          // CODE GENERATION
          var symbolMap: SymbolMap = Map.empty
          // we put in the 'c' symbols
          preCardAssigns.map(_._1).foreach(nme => { symbolMap = symbolMap + (nme -> currentOwner.newValue(TermName(unit.fresh.newName(nme))).setInfo(definitions.IntClass.tpe) ) } )
          inIntVarList.foreach(sym => { symbolMap = symbolMap + (sym.name.toString -> sym) } )
          inSetVarList.foreach(sym => { symbolMap = symbolMap + (sym.name.toString -> sym) } )

          val codeGen = new CodeGenerator(unit, currentOwner, symbolMap, emitWarnings, a.pos)

          val preliminaryCardAssigns: List[Tree] = preCardAssigns.map(pca => {
            ValDef(symbolMap(pca._1), codeGen.setIntTermToCode(symbolMap, pca._2, underlyingElementTypeTree))
          })

          val mikiProgram: List[Tree] = {
            //val mikiFun: Tree = Throw(New(Ident(definitions.getClass("synthesis.Definitions.UnsatisfiableConstraint")), List(Nil)))
            dprintln(paPrec)
            dprintln(paProg)
            val mikiFun: Tree = codeGen.programToCode(paPrec, paProg, true)
            linOutVars.foreach(nme => { symbolMap = symbolMap + (nme -> currentOwner.newValue(TermName(unit.fresh.newName(nme))).setInfo(definitions.IntClass.tpe) ) } )

            val lovss = linOutVars.size
            if(lovss == 1) {
              List(ValDef(symbolMap(linOutVars.head), mikiFun))
            } else {
              val tempTupleSym = currentOwner.newValue(TermName(unit.fresh.newName("tempTuple$"))).setInfo(definitions.tupleType(linOutVars.map(n => definitions.IntClass.tpe)))
              ValDef(tempTupleSym, mikiFun) :: (
                for(c <- 0 until lovss) yield ValDef(symbolMap(linOutVars(c)), Select(Ident(tempTupleSym), tupleField(lovss, c+1)))).toList
            }
          }

          outSetVarList.foreach(sym => { symbolMap = symbolMap + (sym.name.toString -> sym) } )
          val concludingAssigns: List[Tree] = (for(ass <- asss) yield {
            if(!symbolMap.isDefinedAt(ass.setName)) {
              symbolMap = symbolMap + (ass.setName -> currentOwner.newValue(TermName(unit.fresh.newName(ass.setName + "$"))).setInfo(instantiatedSetType))
            }
            ass match {
              case bapa.ASTBAPASyn.Simple(nme, setExpr) => ValDef(symbolMap(nme), codeGen.setTermToCode(symbolMap, setExpr, underlyingElementTypeTree))
              case bapa.ASTBAPASyn.Take(nme, cnt, setExpr) => {
                ValDef(symbolMap(nme),
                  Apply(
                    Select(Select(Ident(synthesisPackage), synthesisDefinitionsModule), definitions.termMember(synthesisDefinitionsModule, "takeFromSet")),
                    List(codeGen.setIntTermToCode(symbolMap, cnt, underlyingElementTypeTree), codeGen.setTermToCode(symbolMap, setExpr, underlyingElementTypeTree))
                  )
                )

              }
            }
          }).toList



          typer.typed(atOwner(currentOwner) {
            Block(
              preliminaryCardAssigns :::
              mikiProgram :::
              concludingAssigns :::
              Nil,
              if(outSetVarList.size == 1) {
                Ident(outSetVarList(0))
              } else {
                New(
                  TypeTree(definitions.tupleType(outSetVarList.map(x => instantiatedSetType))),
                  List(outSetVarList.map(sym => Ident(sym)))
                )
              }
            )
          })
        }

        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if(synthesisDefinitionsModule == s.symbol && n.toString == "choose") => {
          /*
          val tpe = predicate.vparams(0).tpt.tpe
          val TypeRef(_,sym,args) = tpe
          println(sym)  // : Symbol
          println(args) // : List[Type]
          println("***")
          val immModule = definitions.getModule("scala.collection.immutable")
          val setTrait  = definitions.getMember(immModule, "Set")
          println(immModule)
          println(immModule.tpe)
          println(setTrait)
          println(setTrait.tpe)
          val setTrait2 = definitions.getClass("scala.collection.immutable.Set")
          println(setTrait2)
          println(setTrait2.tpe)
          println("***")
          println(sym == setTrait2)
          args(0) match {
            case TypeRef(_, ss, Nil) if ss == definitions.getClass("scala.Predef.String") => println("yes yes yes yes")
          }

          */
          reporter.error(predicate.vparams.head.pos, "Unsupported type in call to ``choose''.")
          super.transform(a)
        }

        case _ => super.transform(tree)
      }
    }

    def extractExtractors(tree: Tree): Option[(Term,Set[Symbol],Set[Symbol],Set[String])] = {
      var bindSymbols: Set[Symbol] = Set.empty
      var inSymbols: Set[Symbol] = Set.empty
      var wildcards: Set[String] = Set.empty
      case class EscapeException() extends Exception
      var wcCount = -1

      def et(t: Tree): Term = t match {
        case ExExTimes(t1,t2) => Times(et(t1), et(t2))
        case ExExPlus(t1,t2) => Plus(et(t1), et(t2))
        case ExExMinus(t1,t2) => Minus(et(t1), et(t2))
        case b @ Bind(name, Ident(nme.WILDCARD)) => {
          bindSymbols = bindSymbols + b.symbol
          Variable(name.toString)
        }
        case Ident(nme.WILDCARD) => {
          wcCount = wcCount + 1
          val wcName = "wildcard$" + wcCount
          wildcards = wildcards + wcName
          Variable("wildcard$" + wcCount)
        }
        case i @ Ident(nme) if i.symbol.isStable => {
          inSymbols = inSymbols + i.symbol
          Variable(nme.toString)
        }
        case Literal(Constant(i: Int)) => IntLit(i)
        case _ => {
          reporter.error(t.pos, "invalid expression in arithmetic pattern")
          throw EscapeException()
        }
      }

      try {
        val retTerm = et(tree)
        Some((retTerm,inSymbols,bindSymbols,wildcards))
      } catch {
        case EscapeException() => None
      }
    }

    // tries to extract an arithmetic formula from the code.
    def extractFormula(tree: Tree): Option[(Formula,Set[Symbol])] = {
      var extractedSymbols: Set[Symbol] = Set.empty
      case class EscapeException() extends Exception

      def ef(t: Tree): Formula = t match {
        case ExTrueLiteral() => True()
        case ExFalseLiteral() => False()
        case ExAnd(l,r) => And(ef(l), ef(r))
        case ExOr(l,r) => Or(ef(l), ef(r))
        case ExNot(f) => Not(ef(f))
        case ExEquals(l,r) => Equals(et(l), et(r))
        case ExNotEquals(l,r) => NotEquals(et(l), et(r))
        case ExLessThan(l,r) => LessThan(et(l), et(r))
        case ExLessEqThan(l,r) => LessEqThan(et(l), et(r))
        case ExGreaterThan(l,r) => GreaterThan(et(l), et(r))
        case ExGreaterEqThan(l,r) => GreaterEqThan(et(l), et(r))
        case _ => {
          reporter.error(t.pos, "invalid expression in sythesis predicate")
          throw EscapeException()
        }
      }

      // def bip(t: Tree): Term = t match {
      //   case ExIntIdentifier(id) => id: TermName
      //   case _                   => null
      // }

      def et(t: Tree): Term = t match {
        case ExIntLiteral(value) => IntLit(value)
        case ExIntIdentifier(id) => {
          extractedSymbols = extractedSymbols + t.symbol
          Variable(id.toString)
        }
        case ExPlus(l,r) => Plus(et(l), et(r))
        case ExMinus(l,r) => Minus(et(l), et(r))
        case ExTimes(l,r) => Times(et(l), et(r))
        // case ExDiv(l,r) => Div(et(l), et(r))
        // case ExModulo(l,r) => Modulo(et(l), et(r))
        case ExNeg(t) => Neg(et(t))
        case _ => {
          reporter.error(t.pos, "invalid term in synthesis predicate")
          throw EscapeException()
        }
      }

      try {
        val res = ef(tree)
        Some((res,extractedSymbols))
      } catch {
        case EscapeException() => None
      }
    }

    // tries to convert a formula to Mikael's format. Returns None if one of
    // the predicates contains a non-linear term.
    def formulaToPAFormula(formula: Formula, outVarSet: Set[String]): Option[PASynthesis.PAFormula] = {
      case class EscapeException() extends Exception

      def f2paf(f: Formula): PASynthesis.PAFormula = f match {
        case And(fs) => PASynthesis.PAConjunction(fs.map(f2paf(_)))
        case Or(fs) => PASynthesis.PADisjunction(fs.map(f2paf(_)))
        case True() => PASynthesis.PATrue()
        case False() => PASynthesis.PAFalse()
        case Equals(term, IntLit(0)) => PASynthesis.PAEqualZero(makePACombination(term))
        case GreaterEqThan(term, IntLit(0)) => PASynthesis.PAGreaterEqZero(makePACombination(term))
        case _ => scala.sys.error("Unexpected formula in format conversion: " + f)
      }

      def makePACombination(term: Term): PASynthesis.PACombination = term match {
        case LinearCombination(cstTerm, cstList) => {
          var inVarsAff:  List[(Int,PASynthesis.InputVar)] = Nil
          var outVarsAff: List[(Int,PASynthesis.OutputVar)] = Nil

          for((nme,coef) <- cstList) {
            if(outVarSet.contains(nme)) {
              outVarsAff = (coef,PASynthesis.OutputVar(nme)) :: outVarsAff
            } else {
              inVarsAff = (coef,PASynthesis.InputVar(nme)) :: inVarsAff
            }
          }

          PASynthesis.PACombination(cstTerm, inVarsAff.reverse.distinct, outVarsAff.reverse.distinct)
        }
        case _ => throw EscapeException()
      }

      try {
        Some(f2paf(formula))
      } catch {
        case EscapeException() => None
      }
    }

    def formulaToAPAFormula2(formula: Formula, outVarSet: Set[String]): Option[APAFormula] =
    if(!isQuasiLinear(formula, outVarSet)) {
      None
    } else {
      case class EscapeException() extends Exception

      def f2apaf(form: Formula): APAFormula = ((form match {
        case And(fs) => APAConjunction(fs.map(f2apaf(_)))
        case Or(fs) => APADisjunction(fs.map(f2apaf(_)))
        case Not(f) => APANegation(f2apaf(f))
        case True() => APATrue()
        case False() => APAFalse()
        case Equals(l,r) => t2apat(l).===(t2apat(r))
        case NotEquals(l,r) => APANegation(t2apat(l).===(t2apat(r)))
        case LessThan(l,r) => t2apat(l).<(t2apat(r))
        case LessEqThan(l,r) => t2apat(l).<=(t2apat(r))
        case GreaterThan(l,r) => t2apat(l).>(t2apat(r))
        case GreaterEqThan(l,r) => t2apat(l).>=(t2apat(r))
      }):APAFormula).simplified

      def t2apat(term: Term): APACombination = ((term match {
        case Variable(id) if outVarSet.contains(id) => APASynthesisExamples.O(id).toCombination
        case Variable(id) => APACombination(APASynthesisExamples.I(id).toInputTerm, Nil)
        case IntLit(value) => APACombination(value)
        case Neg(t) => t2apat(t).*(-1)
        case Plus(ts) => ts.map(t2apat(_)).reduceLeft(_.+(_))
        case Minus(t1, t2) => t2apat(t1).-(t2apat(t2))
        case times @ Times(ts) => {
          tryInTerm(times) match {
            case Some(apaic) => APACombination(apaic)
            case None => {
              val mapped = ts.map(tryInTerm(_))
              mapped.count(_.isEmpty) match {
                case 0 => scala.sys.error("Something went wrong.")
                case 1 => {
                  val inTerm: APAInputTerm = mapped.filter(_.isDefined).map(_.get).reduceLeft[APAInputTerm]((x:APAInputTerm,y:APAInputTerm) => APAInputMultiplication(x :: y :: Nil).simplified)
                  // .get should never fail !
                  val outTerm: APACombination = t2apat(ts.find(tryInTerm(_).isEmpty).get)
                  outTerm.*(inTerm)
                }
                case _ => throw EscapeException()
              }
            }
          }
        }
        case Div(t1, t2) => scala.sys.error("Div should not occur.")
        case Modulo(t1, t2) => scala.sys.error("Mod should not occur.")
        case Min(ts) => scala.sys.error("Mod should not occur.")
      }):APACombination).simplified

      def tryInTerm(term: Term): Option[APAInputTerm] = (term match {
        case Variable(id) if outVarSet.contains(id) => None
        case Variable(id) => Some(APASynthesisExamples.I(id).toInputTerm)
        case IntLit(value) => Some(APAInputCombination(value))
        case Neg(t) => tryInTerm(t).map(_.*(APAInputCombination(-1)))
        case Plus(ts) => {
          val mapped = ts.map(tryInTerm(_))
          mapped.find(_.isEmpty) match {
            case Some(_) => None
            case None => {
              val mappedOK: List[APAInputTerm] = mapped.map(_.get)
              Some(mappedOK.reduceLeft(_.+(_)))
            }
          }
        }
        case Minus(t1, t2) => {
          val tt1 = tryInTerm(t1)
          val tt2 = tryInTerm(t2)
          if(tt1.isEmpty || tt2.isEmpty) {
            None
          } else {
            Some(tt1.get.-(tt2.get))
          }
        }
        case Times(ts) => {
          val mapped = ts.map(tryInTerm(_))
          mapped.find(_.isEmpty) match {
            case Some(_) => None
            case None => {
              val mappedOK: List[APAInputTerm] = mapped.map(_.get)
              Some(mappedOK.reduceLeft[APAInputTerm]((x:APAInputTerm,y:APAInputTerm) => APAInputMultiplication(x :: y :: Nil).simplified))
            }
          }
        }
        case Div(t1, t2) => scala.sys.error("Div should not occur.")
        case Modulo(t1, t2) => scala.sys.error("Mod should not occur.")
        case Min(ts) => scala.sys.error("Mod should not occur.")
      }).map(_.simplified)

      try {
        Some(f2apaf(formula))
      } catch {
        case EscapeException() => scala.sys.error("was quasi-linear or not??"); None
      }
    }

/*    def formulaToAPAFormula(formula: Formula, outVarSet: Set[String]): Option[APAFormula] = {
      case class EscapeException() extends Exception

      def f2apaf(f: Formula): APAFormula = f match {
        case And(fs) => APAConjunction(fs.map(f2apaf(_)))
        case Or(fs) => APADisjunction(fs.map(f2apaf(_)))
        case True() => APATrue()
        case False() => APAFalse()
        case Equals(term, IntLit(0)) => APAEqualZero(makeAPACombination(term))
        case GreaterEqThan(term, IntLit(0)) => APAGreaterEqZero(makeAPACombination(term))
        case _ => scala.sys.error("Unexpected formula in APA format conversion: " + f)
      }

      def makeAPACombination(term: Term): APACombination = term match {
        case LinearCombination(cstTerm, cstList) => {
          var inVarsAff:  List[(Int, InputVar)] = Nil
          var outVarsAff: List[(APAInputCombination, OutputVar)] = Nil

          for((nme,coef) <- cstList) {
            if(outVarSet.contains(nme)) {
              outVarsAff = (APAInputCombination(coef, Nil), OutputVar(nme)) :: outVarsAff
            } else {
              inVarsAff = (coef, InputVar(nme)) :: inVarsAff
            }
          }

          APACombination(APAInputCombination(cstTerm, inVarsAff.reverse.distinct), outVarsAff.reverse.distinct)
        }
        case _ => throw EscapeException()
      }

      try {
        Some(f2apaf(formula))
      } catch {
        case EscapeException() => None
      }
    }
*/

    // tries to extract a formula about (immutable) sets, possibly with
    // arithmetic stuff in it as well
    // the first set contains the set variables we encountered, the second the integer variables
    def extractSetFormula(tree: Tree): Option[(bapa.ASTBAPASyn.Formula,Set[Symbol],Set[Symbol])] = {
      var extractedSetSymbols: Set[Symbol] = Set.empty
      var extractedIntSymbols: Set[Symbol] = Set.empty
      case class EscapeException() extends Exception
      import bapa.ASTBAPASyn.{atom2formula}

      def ef(t: Tree): bapa.ASTBAPASyn.Formula = t match {
        case ExAnd(l,r) => bapa.ASTBAPASyn.And(ef(l), ef(r))
        case ExOr(l,r) => bapa.ASTBAPASyn.Or(ef(l), ef(r))
        case ExNot(f) => bapa.ASTBAPASyn.Not(ef(f))
        case ExEquals(l,r) => {
          if(l.tpe == definitions.IntClass.tpe) {
            bapa.ASTBAPASyn.IntEqual(et(l), et(r))
          } else {
            bapa.ASTBAPASyn.SetEqual(es(l), es(r))
          }
        }
        case ExNotEquals(l,r) => {
          bapa.ASTBAPASyn.Not(
            if(l.tpe == definitions.IntClass.tpe) {
              bapa.ASTBAPASyn.IntEqual(et(l), et(r))
            } else {
              bapa.ASTBAPASyn.SetEqual(es(l), es(r))
            })
        }
        case ExLessThan(l,r) => bapa.ASTBAPASyn.IntLessEqual(bapa.ASTBAPASyn.Plus(bapa.ASTBAPASyn.IntConst(1), et(l)), et(r))
        case ExLessEqThan(l,r) => bapa.ASTBAPASyn.IntLessEqual(et(l), et(r))
        case ExGreaterThan(l,r) => bapa.ASTBAPASyn.IntLessEqual(bapa.ASTBAPASyn.Plus(bapa.ASTBAPASyn.IntConst(1), et(r)), et(l))
        case ExGreaterEqThan(l,r) =>  bapa.ASTBAPASyn.IntLessEqual(et(r), et(l))
        case ExSubsetOf(l,r) => bapa.ASTBAPASyn.SetSubset(es(l), es(r))
        case _ => {
          reporter.error(t.pos, "invalid expression in sythesis predicate")
          throw EscapeException()
        }
      }

      def et(t: Tree): bapa.ASTBAPASyn.PAInt = t match {
        case ExIntLiteral(value) => bapa.ASTBAPASyn.IntConst(value)
        case ExIntIdentifier(id) => {
          extractedIntSymbols = extractedIntSymbols + t.symbol
          bapa.ASTBAPASyn.IntVar(id.toString)
        }
        case ExPlus(l,r) => bapa.ASTBAPASyn.Plus(et(l), et(r))
        case ExMinus(l,r) => bapa.ASTBAPASyn.Plus(et(l), bapa.ASTBAPASyn.Times(-1, et(r)))
        case ExTimes(ExIntLiteral(coef),r) => bapa.ASTBAPASyn.Times(coef, et(r))
        case ExTimes(l,ExIntLiteral(coef)) => bapa.ASTBAPASyn.Times(coef, et(l))
        case ExNeg(t) => bapa.ASTBAPASyn.Times(-1, et(t))
        case ExSetCard(s) => bapa.ASTBAPASyn.Card(es(s))
        case _ => {
          reporter.error(t.pos, "invalid integer term in synthesis predicate")
          throw EscapeException()
        }
      }

      def es(t: Tree): bapa.ASTBAPASyn.BASet = t match {
        case ExEmptySet() => bapa.ASTBAPASyn.EmptySet
        case ExSetIdentifier(id) => {
          extractedSetSymbols = extractedSetSymbols + t.symbol
          bapa.ASTBAPASyn.SetVar(id.toString)
        }
        case ExUnion(l,r) => bapa.ASTBAPASyn.Union(es(l),es(r))
        case ExIntersection(l,r) => bapa.ASTBAPASyn.Intersec(es(l),es(r))
        case ExSetMinus(l,r) => bapa.ASTBAPASyn.Intersec(es(l), bapa.ASTBAPASyn.Compl(es(r)))
        case _ => {
          reporter.error(t.pos, "invalid set term in synthesis predicate")
          throw EscapeException()
        }
      }

      try {
        val res = ef(tree)
        Some((res,extractedSetSymbols,extractedIntSymbols))
      } catch {
        case EscapeException() => None
      }
    }
  }

  def conditionToFormula(cond: PASynthesis.PACondition): Formula = {
    import PASynthesis._

    def f2f(f: PAFormula): Formula = f match {
      case PAConjunction(fs) => And(fs.map(f2f(_)))
      case PADisjunction(fs) => Or(fs.map(f2f(_)))
      case PADivides(coef, comb) => Equals(IntLit(0), Modulo(t2t(comb), IntLit(coef)))
      case PAEqualZero(comb) => Equals(IntLit(0), t2t(comb))
      case PAGreaterZero(comb) => LessThan(IntLit(0), t2t(comb))
      case PAGreaterEqZero(comb) => LessEqThan(IntLit(0), t2t(comb))
      case PATrue() => True()
      case PAFalse() => False()
    }

    def t2t(t: PATerm): Term = t match {
      case PACombination(coef, ias, oas) => {
        Plus(IntLit(coef) ::
          ias.map(ia => Times(IntLit(ia._1) :: Variable(ia._2.name) :: Nil)) :::
          oas.map(oa => Times(IntLit(oa._1) :: Variable(oa._2.name) :: Nil)))
      }
      case PADivision(pac, coef) => {
        Div(t2t(pac), IntLit(coef))
        /* val num = t2t(pac)
        val den = IntLit(coef)
        Div(
          Minus(
            num,
            Modulo(
              Plus(den :: Modulo(num, den) :: Nil),
              den)),
          den) */
      }
      case PAMinimum(ts) => Min(ts.map(t2t(_)))
      case PAMaximum(ts) => Neg(Min(ts.map(tr => Neg(t2t(tr)))))
    }

    val inAss = cond.input_assignment.map(ia => {
      Equals(Variable(ia._1.name), t2t(ia._2))
    })
    val out = normalized(Or(Not(And(inAss)) :: f2f(cond.global_condition) :: Nil))
    //println(out)
    out
  }

  // does its "best" to convert to some formula we can send to Z3, but may fail
  def apaConditionToFormula(cond: APACondition): Option[Formula] = {
    case class EscapeException() extends Exception

    def f2f(f: APAFormula): Formula = f match {
      case APAConjunction(fs) => And(fs.map(f2f(_)))
      case APADisjunction(fs) => Or(fs.map(f2f(_)))
      case APANegation(fm) => Not(f2f(fm))
      case APADivides(coef, comb) => Equals(IntLit(0), Modulo(t2t(comb), it2t(coef)))
      case APAEqualZero(comb) => Equals(IntLit(0), t2t(comb))
      case APAGreaterZero(comb) => LessThan(IntLit(0), t2t(comb))
      case APAGreaterEqZero(comb) => LessEqThan(IntLit(0), t2t(comb))
      case APATrue() => True()
      case APAFalse() => False()
    }

    def t2t(t: APATerm): Term = t match {
      case APACombination(cstPart, ol) => {
        Plus(it2t(cstPart) ::
          ol.map(op => Times(it2t(op._1) :: Variable(op._2.name) :: Nil)))
      }
      case APADivision(pac, coef) => {
        Div(t2t(pac), it2t(coef))
      }
      case APAMinimum(ts) => Min(ts.map(t2t(_)))
      case APAMaximum(ts) => Neg(Min(ts.map(tr => Neg(t2t(tr)))))
    }

    def it2t(it: APAInputTerm): Term = it match {
      case APAInputCombination(coef, il) => {
        Plus(IntLit(coef) ::
          il.map(ip => Times(IntLit(ip._1) :: Variable(ip._2.name) :: Nil)))
      }
      case APAInputDivision(nums, dens) => {
        Div(Times(nums.map(it2t(_))), Times(dens.map(it2t(_))))
      }
      case APAInputMultiplication(ops) => Times(ops.map(it2t(_)))
      case APAInputAddition(ops) => Plus(ops.map(it2t(_)))
      case APAInputAbs(arg) => val t = it2t(arg); Neg(Min(t :: Neg(t) :: Nil))
      case APAInputGCD(_) => throw EscapeException()
      case APAInputLCM(_) => throw EscapeException()
    }

    def iass2f(ia: InputAssignment): Formula = ia match {
      case SingleInputAssignment(v, t) => Equals(Variable(v.name), it2t(t))
      case _ => throw EscapeException()
    }

    try {
      if(cond.pf != APAEmptySplitCondition()) throw EscapeException()

      val inAss = cond.input_assignment.map(iass2f(_))
      val out = normalized(Or(Not(And(inAss)) :: f2f(cond.global_condition) :: Nil))
      //println(out)
      Some(out)
    } catch {
      case EscapeException() => None
    }
  }
}
