package compiler.runners

import compiler.gennames.FileExtensions.licorne as licorneExt
import compiler.io.{SourceCodeProvider, SourceFile}
import compiler.pipeline.TasksPipelines
import compiler.reasoning.{ArithIntMode, BvInt32Mode, CounterexampleBox, IntHandlingMode}

import java.nio.file.{Files, InvalidPathException, Path, Paths}
import scala.annotation.tailrec
import scala.collection.mutable

object Main {

  private val defaultClassOutDir = "./classes"
  private val cmdLineExitCode = -22

  private type MutArgsMap = mutable.Map[String, Option[String]]

  def main(args: Array[String]): Unit = {
    val cmdLine = args.mkString(" ")
    try {
      val (action, pathStrs) = parseCmdLine(splitAtSpacesExceptBetweenBrackets(cmdLine))
      val paths = extractAllPaths(pathStrs)
      val sourceFiles = paths.map(p => SourceFile(p.toString))
      action.run(sourceFiles)
    } catch {
      case e: InvalidPathException => error(e.getMessage)
    }
  }

  private def extractAllPaths(pathStrs: List[String]): List[Path] = {
    pathStrs.flatMap { ps =>
      val path = Path.of(ps)
      val file = path.toFile
      if (!file.exists()) {
        error(s"file not found: $path")
      }
      if file.isFile then List(path)
      else Files.walk(path).toArray(new Array[Path](_))
    }.filter(_.toString.endsWith("." + licorneExt))
  }

  private def splitAtSpacesExceptBetweenBrackets(cmdLine: String): List[String] = {

    val charsAndDepths = cmdLine.foldLeft(List((0.toChar, 0))) { (reversedCharsAndDepths, currChar) =>
      val currDepth = reversedCharsAndDepths.head._2
      currChar match {
        case '[' if currDepth > 0 => error("nested lists are not supported")
        case '[' => (currChar, currDepth + 1) :: reversedCharsAndDepths
        case ']' if currDepth == 0 => error("unexpected ']'")
        case ']' => (currChar, currDepth - 1) :: reversedCharsAndDepths
        case _ => (currChar, currDepth) :: reversedCharsAndDepths
      }
    }.reverse.tail

    @tailrec def split(wordsReversed: List[String], currWordReversed: List[Char], charsAndDepth: List[(Char, Int)]): List[String] = {
      charsAndDepth match {
        case Nil =>
          (currWordReversed.reverse.mkString :: wordsReversed).reverse
        case (currChar, 0) :: tail if currChar.isWhitespace =>
          split(currWordReversed.reverse.mkString :: wordsReversed, Nil, tail)
        case (currChar, _) :: tail =>
          split(wordsReversed, currChar :: currWordReversed, tail)
      }
    }

    split(Nil, Nil, charsAndDepths)
  }

  private def parseCmdLine(cmdLine: List[String]): (Action, List[String]) = {
    cmdLine match {
      case Nil => error("empty command")
      case cmd :: tail => {
        if (cmd == "help") {
          displayHelp()
          System.exit(0)
          throw new AssertionError() // should never happen because exit occurred before
        }
        val (args, files) = tail.span(_.startsWith("-"))
        if (files.isEmpty) {
          error("no input files")
        }
        val argsMap = parseArgs(Nil, args.map(_.substring(1)))
        cmd match {
          case "run" => (Run(argsMap), files)
          case "compile" => (Compile(argsMap), files)
          case "typecheck" => (TypeCheck(argsMap), files)
          case _ => error(s"unknown command: $cmd")
        }
      }
    }
  }

  /**
   * Parse the arguments of a command
   *
   * @param alrParsed already parsed
   * @param rem       remaining words to parse
   * @return a map arg -> value
   */
  @tailrec private def parseArgs(alrParsed: List[(String, Option[String])], rem: List[String]): MutArgsMap = {
    rem match {
      case Nil => mutable.Map.from(alrParsed)
      case head :: tail =>
        head.split("=", 2).toList match {
          case noValArg :: Nil => parseArgs((noValArg, None) :: alrParsed, tail)
          case arg :: value :: Nil => parseArgs((arg, Some(value)) :: alrParsed, tail)
          case _ => assert(false)
        }
    }
  }

  private def getValuedArg(argName: String, argsMap: MutArgsMap, optDefault: Option[String] = None): String = {
    argsMap.remove(argName).getOrElse(optDefault).getOrElse(error(s"missing required argument: $argName"))
  }

  private def getValuedArgOpt(argName: String, argsMap: MutArgsMap): Option[String] = {
    argsMap.remove(argName).map {
      case Some(value) => value
      case None => error(s"missing value for argument $argName")
    }
  }

  private def getUnvalArg(argName: String, argsMap: MutArgsMap): Boolean = {
    argsMap.remove(argName) match {
      case None => false
      case Some(None) => true
      case Some(_) => error(s"argument $argName takes no value")
    }
  }

  private def getOutputNameArg(sources: List[SourceCodeProvider], argsMap: MutArgsMap, defaultOutputName: String): String = {
    getValuedArg("out-file", argsMap, Some(defaultOutputName))
  }

  private def getOutDirArg(argsMap: MutArgsMap): Path = {
    Paths.get(getValuedArg("out-dir", argsMap, Some(defaultClassOutDir)))
  }
  
  private def getSSADirArg(argsMap: MutArgsMap): Option[Path] = {
    getValuedArgOpt("ir-dir", argsMap).map(Paths.get(_))
  }

  private def getIntHandlingModeArg(argsMap: MutArgsMap): IntHandlingMode[?] = {
    val smtIntArith = "arith"
    val smtIntBitvec = "bitvec"
    getValuedArg("smt-int", argsMap, Some(smtIntArith)) match {
      case `smtIntArith` => ArithIntMode
      case `smtIntBitvec` => BvInt32Mode
      case unknown => error("unknown SMT integer mode: " + unknown)
    }
  }

  private def getIndentGranularityArg(argsMap: MutArgsMap): Int = {
    val argStr = getValuedArg("indent", argsMap, Some("2"))
    val indent = argStr.toIntOption.getOrElse(error(s"could not convert $argStr to an integer"))
    if (indent <= 0) {
      error("indent must be positive")
    }
    indent
  }

  private def getPrintAllParenthesesArg(argsMap: MutArgsMap): Boolean = {
    getUnvalArg("all-parenth", argsMap)
  }

  private def getCounterExBoxArg(argsMap: MutArgsMap): Option[CounterexampleBox] = {
    Option.when(getUnvalArg("counter-ex", argsMap))(new CounterexampleBox)
  }

  private def getProgramArgsArg(argsMap: MutArgsMap): Array[String] = {
    val emptyArrStr = "[]"
    val arrayStr = getValuedArg("args", argsMap, Some(emptyArrStr))
    if (!(arrayStr.startsWith("[") && arrayStr.endsWith("]"))) {
      error("program arguments must be given as a list (surrounded by brackets and separated by whitespaces)")
    }
    if arrayStr == emptyArrStr then Array.empty else arrayStr.tail.init.split(' ')
  }

  // Actions, i.e. description of commands to the cmdline program -----------------------------------------------

  private trait Action {
    def run(sources: List[SourceCodeProvider]): Unit
  }

  /**
   * Run command (compile and run)
   */
  private case class Run(argsMap: MutArgsMap) extends Action {
    override def run(sources: List[SourceCodeProvider]): Unit = {
      val outDirPath = getOutDirArg(argsMap)
      val ssaDir = getSSADirArg(argsMap)
      val ihm = getIntHandlingModeArg(argsMap)
      val counterExBoxOpt = getCounterExBoxArg(argsMap)
      val compiler = TasksPipelines.compiler(outDirPath, ssaDir, ihm, counterExBoxOpt)
      val programArgs = getProgramArgsArg(argsMap)
      reportUnknownArgsIfAny(argsMap)
      val mainClasses = compiler.apply(sources)
      if (mainClasses.isEmpty) {
        error("no main class found")
      } else if (mainClasses.size >= 2) {
        error("found more than one main class")
      }
      val process = new Runner(error, outDirPath).runMain(mainClasses.head, inheritIO = true, programArgs)
      val exitCode = process.waitFor()
      if (exitCode != 0) {
        System.err.println(s"Process terminated with error code $exitCode")
      }
    }
  }

  /**
   * Compile command
   */
  private case class Compile(argsMap: MutArgsMap) extends Action {
    override def run(sources: List[SourceCodeProvider]): Unit = {
      val outDirPath = getOutDirArg(argsMap)
      val ssaDir = getSSADirArg(argsMap)
      val ihm = getIntHandlingModeArg(argsMap)
      val counterExBoxOpt = getCounterExBoxArg(argsMap)
      val compiler = TasksPipelines.compiler(outDirPath, ssaDir, ihm, counterExBoxOpt)
      reportUnknownArgsIfAny(argsMap)
      compiler.apply(sources)
    }
  }

  /**
   * Typecheck command (typecheck a file)
   */
  private case class TypeCheck(argsMap: MutArgsMap) extends Action {
    override def run(sources: List[SourceCodeProvider]): Unit = {
      val ssaDir = getSSADirArg(argsMap)
      val ihm = getIntHandlingModeArg(argsMap)
      val counterExBoxOpt = getCounterExBoxArg(argsMap)
      val typeChecker = TasksPipelines.typeChecker(ssaDir, ihm, counterExBoxOpt)
      reportUnknownArgsIfAny(argsMap)
      typeChecker.apply(sources)
      println("typecheck: done")
    }
  }

  private def error(msg: String): Nothing = {
    System.err.println(msg)
    System.exit(cmdLineExitCode)

    // should never happen
    throw new AssertionError()
  }

  private def reportUnknownArgsIfAny(argsMap: MutArgsMap): Unit = {
    if (argsMap.nonEmpty) {
      error(s"unknown argument(s): ${argsMap.keys.mkString(", ")}")
    }
  }

  private def displayHelp(): Unit = {
    println(
      s"""
         |Command: <cmd> [<arg>*] <file>*
         |   e.g. run -out-dir=output examples/sorting.lic
         |
         |run: compile and run the program
         | args: -out-dir=...: required, directory where to write the output file
         |       -ir-dir=...: optional, directory where to write the IR representation of the program (not written by default)
         |       -smt-int=arith|bitvec: optional, integer handling mode by the SMT solver (default is arith)
         |       -counter-ex: displays the counter-examples found by the SMT solver
         |       -args=[...]: optional, arguments to be passed to the executed program (e.g. -args=[foo bar baz])
         |compile: compile the program
         | args: -out-dir=...: required, directory where to write the output file
         |       -ir-dir=...: optional, directory where to write the IR representation of the program (not written by default)
         |       -smt-int=arith|bitvec: optional, integer handling mode by the SMT solver (default is arith)
         |       -counter-ex: displays the counter-examples found by the SMT solver
         |typecheck: parse and typecheck the program
         |help: displays help (this)
         |""".stripMargin)
  }

  extension (str: String) private def withHeadUppercase: String = {
    if str.isEmpty then str
    else str.head.toUpper +: str.tail
  }

  @tailrec private def yesNoQuestion(prompt: String): Boolean = {
    println(prompt)
    val input = scala.io.StdIn.readLine()
    val lowerCaseInput = input.toLowerCase
    if (Set("y", "yes").contains(lowerCaseInput)) {
      true
    } else if (Set("n", "no").contains(lowerCaseInput)) {
      false
    } else {
      println("expected 'yes' or 'no'")
      yesNoQuestion(prompt)
    }
  }

}
