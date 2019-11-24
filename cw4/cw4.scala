// Coursework 4 - Luca-Dorin Anton - 6CCS3CFL

//  Based on Dr Christian Urban's comb2.scala,  and my cw3 implementation and

// A parser and compiler for the While language
object ParsePiler {

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
case class For(id: String, a: AExp, b: AExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class WriteStr(s: String) extends Stmt
case class WriteAExp(a: AExp) extends Stmt
case class Read(s: String) extends Stmt


case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp


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
   (("k", "true") ==> (_ => True: BExp )) ||
   (("k", "false") ==> (_ => False: BExp )) ||
   (("p", "(") ~ BExp ~ ("p", ")")) ==> { case _ ~ x ~ _ => x }

// statement / statements
lazy val Stmt: Parser[List[(String, String)], Stmt] =
  ((("k", "skip") ==> (_ => Skip: Stmt)) ||
   (IdParser ~ ("op", ":=") ~ AExp) ==> { case x ~ _ ~ z => Assign(x, z): Stmt } ||
   (("k", "write") ~ AExp) ==> { case _ ~ y => WriteAExp(y): Stmt } ||
   (("k", "write") ~ StrParser) ==> { case _ ~ y => WriteStr(y): Stmt } ||
   (("k", "read") ~ IdParser) ==> { case _ ~ y => Read(y): Stmt } ||
   (("k", "if") ~ BExp ~ ("k", "then") ~ Block ~ ("k", "else") ~ Block) ==>
    { case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w): Stmt } ||
    (("k", "for") ~ IdParser ~ ("op", ":=") ~ AExp ~ ("k", "upto") ~ AExp ~ ("k", "do") ~ Block) ==>
    {case _ ~ id ~ _ ~ init ~ _ ~ end ~  _ ~ bl => For(id, init, end, bl) : Stmt} ||
   (("k", "while") ~ BExp ~ ("k", "do") ~ Block) ==> { case _ ~ y ~ _ ~ w => While(y, w) })

lazy val Stmts: Parser[List[(String, String)], Block] =
  (Stmt ~ ("s", ";") ~ Stmts) ==> { case x ~ _ ~ z => x :: z : Block } ||
  (Stmt ==> ( s => List(s) : Block))

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[(String, String)], Block] =
  ((("p", "{") ~ Stmts ~ ("p", "}")) ==> { case _ ~ y ~ _ => y } ||
   (Stmt ==> (s => List(s) : Block)))



// |------------------- A Compiler for the While language //


// compiler headers needed for the JVM
// (contains methods for read and write)
val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static writeInt(I)V
    .limit locals 1
    .limit stack 2
    getstatic java/lang/System/out Ljava/io/PrintStream;
    iload 0
    invokevirtual java/io/PrintStream/println(I)V
    return
.end method

.method public static writeStr(Ljava/lang/String;)V
  .limit stack 3
  .limit locals 1

  getstatic      java/lang/System/out Ljava/io/PrintStream;
  aload 0
  invokevirtual  java/io/PrintStream/println(Ljava/lang/String;)V

  return

.end method

.method public static read()I
    .limit locals 10
    .limit stack 10

    ldc 0
    istore 1  ; this will hold our final integer
Label1:
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I
    istore 2
    iload 2
    ldc 10   ; the newline delimiter
    isub
    ifeq Label2
    iload 2
    ldc 32   ; the space delimiter
    isub
    ifeq Label2

    iload 2
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48
    isub
    ldc 10
    iload 1
    imul
    iadd
    istore 1
    goto Label1
Label2:
    ;when we come here we have our integer computed in local variable 1
    iload 1
    ireturn
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""



// Compiler functions


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// convenient string interpolations
// for instructions and labels
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def string_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

// this allows you to write things like
// i"add" and l"Label"


// environments
type Env = Map[String, Int]


def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
}

// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}

// boolean expression compilation
//  - the jump-label is for where to jump if the condition is not true
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop("<=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
  case Bop(">", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmplt $jmp"
  case Bop(">=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmple $jmp"
}

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  }
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case For(id, init, end, bl) => {
    val index = env.getOrElse(id, env.keys.size)
    val for_begin = Fresh("For_begin")
    val for_end = Fresh("For_end")
    val env_assign = env + (id -> index)
    val boolean_jmp = compile_bexp(Bop("<=", Var(id), end), env_assign, for_end)
    val (instr, env_end) = compile_block(bl, env_assign)
    (i";for loop start" ++
     compile_aexp(init, env) ++
     i"istore $index \t\t; $id" ++
     l"$for_begin" ++
     boolean_jmp ++
     instr ++
     i"iload ${env_end(id)}" ++
     i"ldc 1" ++
     i"iadd" ++
     i"istore ${env_end(id)}" ++
     i"goto $for_begin" ++
     l"$for_end", env_end)
  }
  case WriteAExp(x) => {
    val instr = compile_aexp(x, env)
    ( instr ++ i"invokestatic XXX/XXX/writeInt(I)V", env)
  }
  case WriteStr(x) =>
    (i"""ldc "$x" \t\t;""" ++
     i"invokestatic XXX/XXX/writeStr(Ljava/lang/String;)V", env)
  case Read(x) => {
    val index = env.getOrElse(x, env.keys.size)
    (i"invokestatic XXX/XXX/read()I" ++
     i"istore $index \t\t; $x", env + (x -> index))
  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}


// compiling and running files
//
// JVM files can be assembled with
//
//    java -jar jvm/jasmin-2.4/jasmin.jar fib.j
//
// and started with
//
//    java fib/fib



import scala.util._
import scala.sys.process._
import scala.io

def compile_tofile(bl: Block, class_name: String) = {
  val output = compile(bl, class_name)
  val fw = new java.io.FileWriter(class_name + ".j")
  fw.write(output)
  fw.close()
}

def compile_all(bl: Block, class_name: String) : Unit = {
  compile_tofile(bl, class_name)
  println("compiled ")
  val test = ("java -jar ~/jvm/jasmin-2.4/jasmin.jar " + class_name + ".j").!!
  println("assembled ")
}

def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0) + "ns, " + ((t1 - t0)/1000000) + "ms, " + (((t1 - t0)/1000000)/1000) + "seconds.")
    result
}

def compile_run(bl: Block, class_name: String) : Unit = {
  println("Start compilation")
  compile_all(bl, class_name)
  println("running")
  time(1, ("java " + class_name + "/" + class_name).!)
}


  def main(args: Array[String]): Unit = {
    // val fib_tks = readTks("fib.tks")
    // val fact_tks = readTks("fact.tks")
    val for_test_tks = readTks("for_test.tks")

    // val fib_tree = Stmts.parse_all(fib_tks).head
    // val fact_tree = Stmts.parse_all(fact_tks).head
    val for_test_tree = Stmts.parse_all(for_test_tks).head

    // compile_tofile(fib_tree, "fib")
    // compile_tofile(fact_tree, "fact")
    compile_tofile(for_test_tree, "fortest")

  }

}
