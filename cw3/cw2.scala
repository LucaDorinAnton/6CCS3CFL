// Coursework 2 - 6CCS3CFL - Luca-Dorin Anton
// Based on Dr. Christian Urban's lexer.scala - Lecture 4


// A simple lexer inspired by work of Sulzmann & Lu
//==================================================
object Lexer {



import scala.language.implicitConversions
import scala.language.reflectiveCalls

// regular expressions including records
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CFUN(f : Char => Boolean) extends Rexp // cfun instead of char, range and all
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp

// values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

def Character(c: Char) = CFUN(_ == c)
def RANGE(cs: Set[Char]) = CFUN(cs.contains(_))
def ALL = CFUN(_ => true)


// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => Character(c)
  case c::s => SEQ(Character(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp =
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
  def + = PLUS(r)
  def ? = OPTIONAL(r)
  def ^ (n: Int) = NTIMES(r, n)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def + = PLUS(s)
  def ? = OPTIONAL(s)
  def ^ (n: Int) = NTIMES(s, n)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CFUN(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case RECD(_, r1) => nullable(r1)
}

def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CFUN(f) => if (f(c)) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case NTIMES(r, i) =>
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case RECD(_, r1) => der(c, r1)
}


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}


// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) =>
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => if (nullable(r)) Left(mkeps(r)) else Right(Empty)
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
  case RECD(x, r) => Rec(x, mkeps(r))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CFUN(d), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), Left(v1)) => Left(inj(r, c, v1))
  case (OPTIONAL(r), Right(v2)) => Right(inj(r, c, v2))
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else
    { throw new Exception("lexing error") }
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexer(r: Rexp, s: String) =
  env(lex(r, s.toList))

val UPPER = RANGE(('A' to 'Z').toSet)
val LOWER = RANGE(('a' to 'z').toSet)
val ZERO_DIGITS = RANGE(('0' to '9').toSet)
val ONE_DIGITS = RANGE(('1' to '9').toSet)
val SYM = RANGE(('A' to 'Z').toSet ++ ('a' to 'z').toSet ++ ('0' to '9').toSet ++ Set('_'))

val NOT_QUOTES = CFUN(_ != '"')
val NOT_NEWLINES = CFUN(_ != '\n')

val KEYWORD : Rexp =  "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip"
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ":=" | "&&" | "||"
val STR: Rexp = "\"" ~ NOT_QUOTES.% ~ "\""
val PARA: Rexp = "{" | "}" | "(" | ")"
val SEMI: Rexp = ";"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val ID = SYM ~ (SYM | ZERO_DIGITS).%
val NUM = "0" | ONE_DIGITS ~ STAR(ZERO_DIGITS)
val COMM : Rexp = "//" ~ STAR(NOT_NEWLINES) ~ "\n" //in-line comments


val WHILE_REGS = (("k" $ KEYWORD) |
                  ("op" $ OP)     |
                  ("str" $ STR)   |
                  ("p" $ PARA)    |
                  ("s" $ SEMI)    |
                  ("w" $ WHITESPACE) |
                  ("n" $ NUM)     |
                  ("id" $ ID)     |
                  ("c" $ COMM)).%

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) =
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) =
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s))
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else
    { throw new Exception("lexing error") }
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) =
  env(lex_simp(r, s.toList))

// escapes strings and prints them out as "", "\n" and so on
def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

// Remove comments and whitespace from the token List
def sanitize(tks: List[(String, String)]) : List[(String, String)]= tks match {
  case Nil => Nil
  case t::ts => t match {
    case ("w", _) => sanitize(ts)
    case ("c", _) => sanitize(ts)
    case _ => t::sanitize(ts)
  }
}

def lex_while(s: String) : List[(String, String)] =
  sanitize(lexing_simp(WHILE_REGS, s))

def main(args: Array[String]): Unit = {

  val test1 = "if (a < b) then skip else a := a * b + 1"
  val test1_tks = lex_while(test1)

  val fib = """write "Fib";
  read n;
  minus1 := 0;
  minus2 := 1;
  while n > 0 do {
         temp := minus2;
         minus2 := minus1 + minus2;
         minus1 := temp;
         n := n - 1
  };
  write "Result";
  write minus2
  """

  val fib_tks = lex_while(fib)

  val loops = """start := 1000;
  x := start;
  y := start;
  z := start;
  while 0 < x do {
   while 0 < y do {
    while 0 < z do { z := z - 1 };
    z := start;
    y := y - 1
   };
   y := start;
   x := x - 1
  }
  """

  val loops_tks = lex_while(loops)

  val primes = """// prints out prime numbers from
  // 2 to 100 (end)

  end := 100;
  n := 2;
  while (n < end) do {
    f := 2;
    tmp := 0;
    while ((f < n / 2 + 1) && (tmp == 0)) do {
      if ((n / f) * f == n) then { tmp := 1 } else { skip };
      f := f + 1
    };
    if (tmp == 0) then { write(n) } else { skip };
    n := n + 1
  }
  """

  val primes_tks = lex_while(primes)

  import java.io._
  val test1_writer = new PrintWriter(new File("test1.tks"))
  test1_tks.map{ case (str1, str2) => test1_writer.write(s"$str1 $str2\n") }
  test1_writer.close()

  val fib_writer = new PrintWriter(new File("fib.tks"))
  fib_tks.map{ case (str1, str2) => fib_writer.write(s"$str1 $str2\n") }
  fib_writer.close()

  val loops_writer = new PrintWriter(new File("loops.tks"))
  loops_tks.map{ case (str1, str2) => loops_writer.write(s"$str1 $str2\n") }
  loops_writer.close()

  val primes_writer = new PrintWriter(new File("primes.tks"))
  primes_tks.map{ case (str1, str2) => primes_writer.write(s"$str1 $str2\n") }
  primes_writer.close()
 }

}
