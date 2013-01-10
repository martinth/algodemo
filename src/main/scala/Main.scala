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
import scala.util.{Random}
import scala.collection.parallel.immutable.ParVector
import scala.collection.immutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.concurrent.duration._
import scala.math.{abs, ceil, floor}
import util.control.Breaks._
import akka.actor._
import akka.pattern._
import akka.util.Timeout
import akka.routing._
import scala.actors.Futures
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, Future}


	final class MersenneTwister (seed: Int = 5489) {
  private val N = 624
  private val M = 397
 
  private val MatrixA = 0x9908b0dfL
 
  private val UpperMask = 0x80000000L
  private val LowerMask = 0x7fffffffL
 
  private val mt = new Array[Long](N)
  private var mti = N + 1
 
  mt(0) = seed
  for (i <- 1 until N) mt(i) = (1812433253L * (mt(i - 1) ^ (mt(i - 1) >>> 30)) + i) & 0xffffffffL
 
  // Generates the next random integer in the sequence
  def nextInt(): Int = {
    var y = 0L
 
    if (mti >= N) {
      val mag01 = Array(0L, MatrixA)
 
      var kk = 0
      while (kk < N - M) {
        y = (mt(kk) & UpperMask) | (mt(kk + 1) & LowerMask)
        mt(kk) = mt(kk + M) ^ (y >>> 1) ^ mag01(y.toInt & 0x1)
        kk += 1
      }
      while (kk < N - 1) {
        y = (mt(kk) & UpperMask) | (mt(kk + 1) & LowerMask)
        mt(kk) = mt(kk + (M - N)) ^ (y >>> 1) ^ mag01(y.toInt & 0x1)
        kk += 1
      }
      y = (mt(N - 1) & UpperMask) | (mt(0) & LowerMask)
      mt(N - 1) = mt(M - 1) ^ (y >>> 1) ^ mag01(y.toInt & 0x1)
 
      mti = 0
    }
 
    y = mt(mti); mti += 1
    y ^= y >>> 11
    y ^= (y << 7) & 0x9d2c5680L
    y ^= (y << 15) & 0xefc60000L
    y ^= (y >>> 18)
 
    y.toInt
  }
 
  // Generates a random integer in the interval [0, limit)
  def nextInt(limit: Int): Int = {
    // Find shift distance
    val lim = limit.toLong & 0xffffffffL
    var n = -1; var bit = 1L << 32
    while (bit > lim) { n += 1; bit >>>= 1 }
 
    // Generate integer, take most significant bits; reject while outside interval
    var r = (nextInt().toLong & 0xffffffffL) >>> n
    while (r >= lim) { r = (nextInt().toLong & 0xffffffffL) >>> n }
    r.toInt
  }
 
  // Generates a random Double in the interval [0, 1)
  def nextDouble(): Double = {
    val a: Long = (nextInt().toLong & 0xffffffffL) >>> 5
    val b: Long = (nextInt().toLong & 0xffffffffL) >>> 6
    (a * 67108864.0 + b) / 9007199254740992.0
  }
  
  def nextBoolean(): Boolean = {
    (nextInt() % 2 == 0)
  }
}

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
    val rnd = new MersenneTwister(42)
    
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

case class RandomRequest(n: Int, m: Int, clauseGenerator: ClauseGenerator)
case class Reply(solutionExists: Boolean, duration: Duration)

class RandomActor extends Actor {
  def receive = {
    case RandomRequest(n, m, clauseGenerator) => {
       val startTime = System.nanoTime
       val clause = clauseGenerator(m, n)
       val solution = CNFSolver.probKSat(clause)
       sender ! Reply(solution.isDefined, Duration(System.nanoTime - startTime, NANOSECONDS))
    }
  }
}


object Main extends App {
  
  val system = ActorSystem("MySystem")
  val router = system.actorOf(Props[RandomActor].withRouter(RoundRobinRouter(nrOfInstances = Runtime.getRuntime().availableProcessors())))
  
  /**
   * Calculates the percentage of solvable clauses for a given n,m that are generated
   * by the given clauseGenerator. If the average runtime of the solution finding
   * process exceeds timeLimit a ToMuchTimeException is thrown
   */
  def avgNonvalidClauses(n: Int, m: Int)(implicit clauseGenerator: ClauseGenerator) = {

    val startTime = System.nanoTime
    
    /** how man iteration to build the average **/
	val TRIES = 100
	
	implicit val timeout = Timeout(3*2*TRIES seconds)
	
	val listOfFutures = List.fill(TRIES)(akka.pattern.ask(router, RandomRequest(n, m, clauseGenerator)).mapTo[Reply])

	val futureOfList = Future.sequence(listOfFutures)
	val res = Await.ready(futureOfList, 100 seconds)
	println(res)

//	val millis = Duration(System.nanoTime - startTime, NANOSECONDS).toMillis
//    val avg = (results count (_.isDefined)) /  results.length.toFloat
//    
//    println(s"n=$n, m=$m => $avg ($millis ms)")
//	
//	avg
  }
  

  implicit val generator = CNFGenerator.uniformDistribution(3)_

  var m = 50
  for (n <- 20 to 25) { // TO INFINITY AND BEYOND
    avgNonvalidClauses(n, n+100)
  }
    
  

 
}
