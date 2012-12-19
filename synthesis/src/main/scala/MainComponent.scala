package synthesis

import scala.tools.nsc._
import scala.tools.nsc.plugins._

class MainComponent(val global: Global, val pluginInstance: SynthesisPlugin)
  extends PluginComponent
  with ChooseTransformer
{
  import global._

  // when we use 2.8.x, swap the comments in the following two lines
  val runsAfter = List("refchecks")
  override val runsRightAfter = Some("refchecks")

  val phaseName = pluginInstance.name

  var fresh: scala.tools.nsc.util.FreshNameCreator = null

  protected def stopIfErrors: Unit = {
    if(reporter.hasErrors) {
      println("There were errors.")
      exit(0)
    }
  }

  def newPhase(prev: Phase) = new MainPhase(prev)

  class MainPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      //global ref to freshName creator
      fresh = unit.fresh

      transformChooseCalls(unit, pluginInstance.emitWarnings)
    }
  }
}
