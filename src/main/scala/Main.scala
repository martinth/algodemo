package object cnf {
	type Config = Map[String, Boolean]
	type ClauseGenerator = (Int, Int) => CNFFormula
	
	def time[R](desc: String, limit: Long, block: => R): R = {
	    val t0 = System.nanoTime()
	    val result = block    // call-by-name
	    val dur = (System.nanoTime() - t0)
	    if(dur > limit) {
	    	println(desc + ": " + dur + "ns")
	    }
	    result
	}
}

import cnf.{Config, ClauseGenerator, time}
import scala.util.Random
import scala.collection.parallel.immutable.ParVector
import scala.collection.immutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.actors.Futures._
import scala.concurrent.duration._
import scala.math.{abs, ceil, floor}
import util.control.Breaks._
import scala.actors.remote.RemoteActor._
import scala.actors.Actor

/** 
 * A boolean variable.
 * 
 * @constructor create a new variable with the given name
 * @param name name of the variable
 * @param negated whether or not this variable should be evaluated as negated 
 */
class Var(val name: String, val negated: Boolean = false) {
  
  /** creates a negated version of this var **/
  def unary_~ = new Var(name, !negated)
  
  /** evaluates this variable from the given configuration **/
  def eval(config: Config) = config get name match {
    case Some(value) => value ^ negated
    case None 		 => throw new RuntimeException("%s not found in config" format name)
  }
  
  override def toString = if (negated) "~"+name else name 
}

/**
 * A boolean OR clause that contains a number of variables
 * 
 * @constructor creates a new clause with the given variables
 */
class Clause(val vars: Var*) {
  
  /** evaluates this clause from the given configuration, returns true if 
   * at least one of the varaibles can be evaulated to true **/
  def eval(config: Config) = vars exists (_.eval(config))
  
  /** the number of variables in this clause **/
  def length = vars.length
    
  override def toString = vars.mkString(" ∨ ")
}

/**
 * A boolean formula the AND some clauses together 
 */
class CNFFormula(clauses: Clause*) {
  
  /** returns all clauses that are not satisfied by the given config **/
  def unsatisfied(config: Config) = clauses filter (_.eval(config) == false)
  
  /** returns all variable names(!) that are used at least ones in this formula **/
  def allVars = (clauses.flatMap(_.vars)).map(_.name)

  /** returns the number of variables (including duplicates) **/
  def length = clauses map (_.length) sum
  
  override def toString = clauses map (c => "(" + c.toString + ")") mkString " ∧ "
}

object CNFSolver {
  
  
  /**
   * Run a probabilistic k-Sat algorithm to find a solution for the
   * given formula. Repeats the algorithm at most repeats time.
   */
  def probKSat(formula: CNFFormula, repeats: Int = 20) = {
    
    var result: Option[Config] = None
    
    for(i <- 1 to repeats if !result.isDefined) {
      result = probKSatAlgo(formula)
    }
  
    result
  }
  
  def probKSatAlgo(formula: CNFFormula) = {
    val rnd = new Random(42)
    
    /** tail recursive algorithm to find a solution **/
    def rec(config: collection.mutable.Map[String, Boolean], limit: Int):Option[Config] = {
      
      val imutableConfig = config.toMap
      
      // get all unsatisfied clauses from formula
      val unsatClauses = formula.unsatisfied(imutableConfig)
      
      // if there are none, we have found a solution and return a result
      if(unsatClauses.length == 0) {
        Some(imutableConfig)
      } 
      // we have to go deeper! (if we haven't reach our limit yet)
      else if (limit > 0) {
        // get all variables from an unsatisfied clause
        val vars = unsatClauses.apply(0).vars
        // choose one variable randomly invert it's configuration and go deeper
        val varToMod = vars.apply(time("rnd", 10000000, rnd.nextInt(vars.length))).name
        config(varToMod) = !config(varToMod)
        rec(config, limit - 1)
      } 
      // so we reached our depth limit and have found no solution - maybe there is none
      else {
        None
      }
    }
    
    // create random configuration (a map from variable names to booleans)
    val randomConfig = (formula.allVars map (v => (v, time("rnd", 10000000, rnd.nextBoolean))))
    
    // pass this configuration to our internal helper function
    val mutableConfig = collection.mutable.Map(randomConfig: _*)
    rec(mutableConfig, 3*formula.length)
    
  }
}

object CNFGenerator {
  def uniformDistribution(k: Int)(m: Int, n: Int) = {
    
    // build a list of all variables n and there negated form 
    val vars = new ListBuffer[Var]()
    for(i <- 1 to n) {
      val v = new Var("x"+i)
      vars += v
      vars += ~v
    }
    
    // create m clauses where each clause selected k random variables
    val rnd = new Random(42)
    val clauses = for(i <- 1 to m) yield new Clause((for(j <- 1 to k) yield vars(rnd.nextInt(vars.length))): _*)
    
    new CNFFormula(clauses:_*)
  }
}

/** helper to signal runtime exceeded **/
case class ToMuchTimeException(avgDuration: Duration) extends Exception


object Main extends App {
  
  /**
   * Calculates the percentage of solvable clauses for a given n,m that are generated
   * by the given clauseGenerator. If the average runtime of the solution finding
   * process exceeds timeLimit a ToMuchTimeException is thrown
   */
  def avgNonvalidClauses(n: Int, m: Int)(implicit clauseGenerator: ClauseGenerator) = {

    val startTime = System.nanoTime
    
    /** how man iteration to build the average **/
	val TRIES = 100
    
    // do TRIES iterations in parallel 
    val tasks = for (i <- 0 until TRIES) yield future[Option[Config]] {
	    val clause = clauseGenerator(m, n)
	    val solution = CNFSolver.probKSat(clause)
	    solution
	}
	  
	/* wait for all threads to finish and collect the results. we will only wait
	 * at most TRIES * 100ms (note: flatten filters out all
	 * None's) */
	val results = awaitAll(500 * TRIES, tasks: _*).asInstanceOf[List[Option[Option[Config]]]].flatten
	
	val millis = Duration(System.nanoTime - startTime, NANOSECONDS).toMillis
    val avg = (results count (_.isDefined)) /  results.length.toFloat
    
    println(s"n=$n, m=$m => $avg ($millis ms)")
	
	avg
  }
  

  implicit val generator = CNFGenerator.uniformDistribution(3)_

  var m = 50
  for (n <- 20 to 25) { // TO INFINITY AND BEYOND
    avgNonvalidClauses(n, n+100)
  }
    
  

 
}
