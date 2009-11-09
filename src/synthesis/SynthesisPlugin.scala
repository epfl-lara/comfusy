package synthesis

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}

/** This class is the entry point for the plugin. */
class SynthesisPlugin(val global: Global) extends Plugin {
  import global._

  val name = "synthesis"
  val description = "Synthesis of functions given in terms of specifications."

  /** The help message displaying the options for that plugin. */
  override val optionsHelp: Option[String] = Some(
    "  -P:synthesis:check-preconditions        Uses a decision procedure to check that the preconditions are satisfiable.")

  /** Processes the command-line options. */
  override def processOptions(options: List[String], error: String => Unit) {
    for(option <- options) {
      option match {
        case "check-preconditions" => ;
        case _ => error("Invalid option: " + option)
      }
    }
  }

  val components = List[PluginComponent](new MainComponent(global, this))
}
