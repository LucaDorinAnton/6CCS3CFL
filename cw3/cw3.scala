// Coursework 3 - Luca-Dorin Anton - 6CCS3CFL

//  Based on Dr Christian Urban's comb2.scala

// A parser and interpreter for the While language
object ParseTrepeter {

import scala.io.Source

// read a tokens file and return it's contents as a list of pairs
def readTks(file: String) : List[(String, String)] = {
  for(line <- Source.fromFile(file).getLines.toList) yield {
    line.split(' ') match { case Array(x: String, y: String) => (x, y) }
  }
}



import scala.language.implicitConversions
import scala.language.reflectiveCalls

// more convenience for the semantic actions later on
case class ~[+A, +B](_1: A, _2: B)


type IsSeq[A] = A => Seq[_]

abstract class Parser[I : IsSeq, T] {
  def parse(ts: I): Set[(T, I)]

  def parse_all(ts: I) : Set[T] =
    for ((head, tail) <- parse(ts); if tail.isEmpty) yield head
}

class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) =
    for ((head1, tail1) <- p.parse(sb);
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I : IsSeq, T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)
}

class FunParser[I : IsSeq, T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
  def parse(sb: I) =
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

case class Tok1Parser(s: String) extends Parser[List[(String, String)], (String, String)] {
  def parse(toks: List[(String, String)]) = toks match{
    case (s, x)::tail => Set(((s, x), tail))
    case _ => Set()
  }
}

case class Tok2Parser(tok: (String, String)) extends Parser[List[(String, String)], (String, String)] {
  def parse(toks: List[(String, String)]) = toks match{
    case (tok._1, tok._2)::tail => Set((tok, tail))
    case _ => Set()
  }
}

case object NumParser extends Parser[List[(String, String)], Int] {
  def parse(tks: List[(String, String)]) = tks match {
    case ("n", nr)::tail => Set((nr.toInt, tail))
    case _ => Set()
  }
}

case object IdParser extends Parser[List[(String, String)], String] {
  def parse(tks: List[(String, String)]) = tks match {
    case ("id", id)::tail => Set((id, tail))
    case _ => Set()
  }
}

case object StrParser extends Parser[List[(String, String)], String] {
  def parse(tks: List[(String, String)]) = tks match {
    case ("str", str)::tail => Set((str.filter(_ != '\"'), tail))
    case _ => Set()
  }
}


implicit def string2parser(s : String) = Tok1Parser(s)

implicit def tuple2parser(tok: (String, String)) = Tok2Parser(tok)

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S](q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

implicit def StringOps(tok: (String, String)) = new {
  def ||(q : => Parser[List[(String, String)], (String, String)]) = new AltParser[List[(String, String)], (String, String)](tok, q)
  def ||(r: String) = new AltParser[List[(String, String)], (String, String)](tok, r)
  def ==>[S] (f: => ((String, String)) => S) = new FunParser[List[(String, String)], (String, String), S](tok, f)
  def ~[S](q : => Parser[List[(String, String)], S]) =
    new SeqParser[List[(String, String)], (String, String), S](tok, q)
  def ~(r: String) =
    new SeqParser[List[(String, String)], (String, String), (String, String)](tok, r)
}


// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class Read(s: String) extends Stmt


case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp


// arithmetic expressions
lazy val AExp: Parser[List[(String, String)], AExp] =
  (Te ~ ("op", "+") ~ AExp) ==> { case x ~ _ ~ z => Aop("+", x, z): AExp } ||
  (Te ~ ("op", "-") ~ AExp) ==> { case x ~ _ ~ z => Aop("-", x, z): AExp } || Te
lazy val Te: Parser[List[(String, String)], AExp] =
  (Fa ~ ("op", "*") ~ Te) ==> { case x ~ _ ~ z => Aop("*", x, z): AExp } ||
  (Fa ~ ("op", "/") ~ Te) ==> { case x ~ _ ~ z => Aop("/", x, z): AExp } ||
  (Fa ~ ("op", "%") ~ Te) ==> {case x ~ _ ~ z => Aop("%", x, z): AExp} || Fa
lazy val Fa: Parser[List[(String, String)], AExp] =
   (("p", "(") ~ AExp ~ ("p", ")")) ==> { case _ ~ y ~ _ => y } ||
   IdParser ==> Var ||
   NumParser ==> Num

// boolean expressions with some simple nesting
lazy val BExp: Parser[List[(String, String)], BExp] =
   (AExp ~ ("op", "==") ~ AExp) ==> { case x ~ _ ~ z => Bop("==", x, z): BExp } ||
   (AExp ~ ("op", "!=") ~ AExp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } ||
   (AExp ~ ("op", "<") ~ AExp) ==> { case x ~ _ ~ z => Bop("<", x, z): BExp } ||
   (AExp ~ ("op", ">") ~ AExp) ==> { case x ~ _ ~ z => Bop(">", x, z): BExp } ||
   (AExp ~ ("op", "<=") ~ AExp) ==> {case x ~ _ ~ z => Bop("<=", x, z): BExp} ||
   (AExp ~ ("op", ">=") ~ AExp) ==> {case x ~ _ ~ z => Bop(">=", x, z): BExp} ||
   (("p", "(") ~ BExp ~ ("p", ")") ~ ("op", "&&") ~ BExp) ==> { case _ ~ y ~ _ ~ _ ~ v => And(y, v): BExp } ||
   (("p", "(") ~ BExp ~ ("p", ")") ~ ("op", "||") ~ BExp) ==> { case _ ~ y ~ _ ~ _ ~ v => Or(y, v): BExp } ||
   (("k", "true") ==> (_ => True: BExp )) ||
   (("k", "false") ==> (_ => False: BExp )) ||
   (("p", "(") ~ BExp ~ ("p", ")")) ==> { case _ ~ x ~ _ => x }

// statement / statements
lazy val Stmt: Parser[List[(String, String)], Stmt] =
  ((("k", "skip") ==> (_ => Skip: Stmt)) ||
   (IdParser ~ ("op", ":=") ~ AExp) ==> { case x ~ _ ~ z => Assign(x, z): Stmt } ||
   (("k", "write") ~ IdParser) ==> { case _ ~ y => Write(y): Stmt } ||
   (("k", "write") ~ ("p", "(") ~ IdParser ~ ("p", ")")) ==> { case _ ~ _ ~ y ~ _ => Write(y): Stmt } ||
   (("k", "write") ~ StrParser) ==> { case _ ~ y => Write(y): Stmt } ||
   (("k", "read") ~ IdParser) ==> { case _ ~ y => Read(y): Stmt } ||
   (("k", "if") ~ BExp ~ ("k", "then") ~ Block ~ ("k", "else") ~ Block) ==>
    { case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w): Stmt } ||
   (("k", "while") ~ BExp ~ ("k", "do") ~ Block) ==> { case _ ~ y ~ _ ~ w => While(y, w) })

lazy val Stmts: Parser[List[(String, String)], Block] =
  (Stmt ~ ("s", ";") ~ Stmts) ==> { case x ~ _ ~ z => x :: z : Block } ||
  (Stmt ==> ( s => List(s) : Block))

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[(String, String)], Block] =
  ((("p", "{") ~ Stmts ~ ("p", "}")) ==> { case _ ~ y ~ _ => y } ||
   (Stmt ==> (s => List(s) : Block)))


// an interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env)
  case While(b, bl) =>
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case Write(x) => { println(env(x)) ; env }
  case Read(x) => env + (x -> scala.io.StdIn.readLine().toInt)
}

def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())


  def main(args: Array[String]): Unit = {
    val test1_tks = readTks("test1.tks")
    val fib_tks = readTks("fib.tks")
    val loops_tks = readTks("loops.tks")
    val primes_tks = readTks("primes.tks")

    val test1_tree = Stmts.parse_all(test1_tks).head
    val fib_tree = Stmts.parse_all(fib_tks).head
    val loops_tree = Stmts.parse_all(loops_tks).head
    val primes_tree = Stmts.parse_all(primes_tks).head

    val test1_res = eval(test1_tree)
    val fib_res = eval(fib_tree)
    val primes_res = eval(primes_tree)
    val loops_res = eval(loops_tree)


    println("----------------------------------")
    println("--- test1 results ---")
    println(test1_res)
    println("----------------------------------")

    println("----------------------------------")
    println("--- fib results ---")
    println(fib_res)
    println("----------------------------------")

    println("----------------------------------")
    println("--- primes results ---")
    println(primes_res)
    println("----------------------------------")

    println("----------------------------------")
    println("--- loops results ---")
    println(loops_res)
    println("----------------------------------")
  }

}
