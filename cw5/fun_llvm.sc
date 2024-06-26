// A Small LLVM Compiler for a Simple Typed Functional Language
// (includes an external lexer and parser)
//
//
// call with 
//
//     amm fun_llvm.sc main fact.fun
//     amm fun_llvm.sc main defs.fun
//
// or
//
//     amm fun_llvm.sc write fact.fun
//     amm fun_llvm.sc write defs.fun
//
//       this will generate an .ll file. 
//
// or 
//
//     amm fun_llvm.sc run fact.fun
//     amm fun_llvm.sc run defs.fun
//
//
// You can interpret an .ll file using lli, for example
//
//      lli fact.ll
//
// The optimiser can be invoked as
//
//      opt -O1 -S in_file.ll > out_file.ll
//      opt -O3 -S in_file.ll > out_file.ll
//
// The code produced for the various architectures can be obtain with
//   
//   llc -march=x86 -filetype=asm in_file.ll -o -
//   llc -march=arm -filetype=asm in_file.ll -o -  
//
// Producing an executable can be achieved by
//
//    llc -filetype=obj in_file.ll
//    gcc in_file.o -o a.out
//    ./a.out


import $file.fun_tokens, fun_tokens._
import $file.fun_parser, fun_parser._ 


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String , ty: String = "UNDEF") extends KVal
case class KInt(i: Int) extends KVal
case class KFloat(f: Float) extends KVal

case class Kop(o: String, v1: KVal, v2: KVal, ty: String = "UNDEF") extends KVal
case class KCall(o: String, vrs: List[KVal], ty: String = "UNDEF") extends KVal
case class KRef(o: String, ty: String = "UNDEF") extends KVal

case class KLet(x: String, e1: KVal, e2: KExp, ty: String = "UNDEF") extends KExp {
  override def toString = s"LET $x : $ty = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal, ty: String = "UNDEF") extends KExp


// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) if s.head.isLower => k(KVar(s)) 
  case Var(s) if s.head.isUpper => {
    val z = Fresh("tmp")
    KLet(z, KRef(s), k(KVar(z)))
  }
  case Num(i) => k(KInt(i))
  case FNum(f) => k(KFloat(f))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
}   

//initial continuation
def CPSi(e: Exp) = CPS(e)({x => KReturn(x)})


type TyEnv = Map[String, String]

def isBool(o: String) = Set("==", "!=", "<", "<=", ">", ">=").contains(o)

def val_type(v: KVal) : String = v match {
  case KVar(_, s) => s
  case KInt(_) => "Int"
  case KFloat(_) => "Double"
  case Kop(_, _, _, s) => s
  case KCall(_, _, s) => s
  case KRef(_, s) => s
}

def typ_val(v: KVal , local_ty: TyEnv, global_ty: TyEnv) : KVal = v match {
  case KVar(s, _) if s.head.isLower => KVar(s, local_ty.get(s).get)
  case KInt(i) => KInt(i)
  case KFloat(f) => KFloat(f)
  case Kop(o, v1, v2, _) => {
    val new_v1 = typ_val(v1, local_ty, global_ty)
    val new_v2 = typ_val(v2, local_ty, global_ty)
    if (isBool(o)) Kop(o, new_v1, new_v2, "Bool")
    else Kop(o, new_v1, new_v2, val_type(new_v1))
  }
  case KCall(n, args, _) => {
    val new_args = args.map({arg => typ_val(arg, local_ty, global_ty)}).toList
    KCall(n, new_args, global_ty.get(n).get)
  }
  case KRef(s, _) => KRef(s, global_ty.get(s).get) 
}


def typ_exp(a: KExp , local_ty: TyEnv, global_ty: TyEnv) : (KExp, TyEnv) = a match {
  case KLet(n, v, e, _) => {
    val new_v = typ_val(v, local_ty, global_ty)
    val let_ty = val_type(new_v)
    val new_e = typ_exp(e, local_ty + (n -> let_ty), global_ty)
    (KLet(n, new_v, new_e._1, let_ty), new_e._2)
  }
  case KIf(x1, e1, e2) => {
    val new_e1 = typ_exp(e1, local_ty, global_ty)
    val new_e2 = typ_exp(e2, new_e1._2, global_ty)
    (KIf(x1, new_e1._1, new_e2._1), new_e2._2)
  }
  case KReturn(v, _) => {
    val new_v = typ_val(v, local_ty, global_ty)
    (KReturn(new_v, val_type(new_v)), local_ty)
  }
}

// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def string_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "==" => "icmp eq i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
}

def compile_dop(op: String) = op match {
case "+" => "fadd double "
case "*" => "fmul double "
case "-" => "fsub double "
case "==" => "fcmp oeq double "
case "<=" => "fcmp ole double "
case "<" => "fcmp olt double "
}

def typ_to_ll(t: String) = t match {
  case "Int" => "i32"
  case "Double" => "double"
  case "Bool" => "i1"
  case "Void" => "void"
}

def compile_and_format(v: KVal) : String = {
  val compiled_v = compile_val(v)
  s"${typ_to_ll(val_type(v))} $compiled_v"
}

// compile K values
def compile_val(v: KVal) : String = v match {
  case KInt(i) => s"$i"
  case KFloat(f) => s"$f"
  case KVar(s, _) => s"%$s"
  case KRef(s, t) => s"load ${typ_to_ll(t)} , ${typ_to_ll(t)}* @$s"
  case Kop(op, x1, x2, t) if(val_type(x1) == "Double") => 
    s"${compile_dop(op)} ${compile_val(x1)}, ${compile_val(x2)}"
  case Kop(op, x1, x2, t) => 
    s"${compile_op(op)} ${compile_val(x1)}, ${compile_val(x2)}"
  case KCall(x1, args, t) => 
    s"call ${typ_to_ll(t)} @$x1(${args.map(compile_and_format).mkString(", ")})"
 
    
}

// compile K expressions
def compile_exp(a: KExp) : String = a match {
  case KReturn(v, "Void") =>
    i"ret void"
  case KReturn(v, ty) =>
    i"ret ${typ_to_ll(ty)} ${compile_val(v)}"
  
  case KLet(_, KCall(o, vrs, "Void"), e, _) =>
    i"${compile_val(KCall(o, vrs, "Void"))}" ++ compile_exp(e)
  case KLet(x: String, v: KVal, e: KExp, _) => 
    i"%$x = ${compile_val(v)}" ++ compile_exp(e)
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1) ++
    l"\n$else_br" ++ 
    compile_exp(e2)
  }
}


val prelude = """

declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @skip() #0 {
  ret void
}

@.str = private constant [4 x i8] c"%d\0A\00"

define void @print_int(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)
"""

val init_global : TyEnv = Map(
  ("new_line" -> "Void"),
  ("print_star" -> "Void"),
  ("print_space" -> "Void"),
  ("skip" -> "Void"),
  ("print_int" -> "Void")
)

def format_arg(arg: (String, String)) : String = s"${typ_to_ll(arg._2)} %${arg._1}"



// compile function for declarations and main
def compile_decl(d: Decl, global_ty: TyEnv) : (String, TyEnv) = d match {
  case Const(n, i) => {
    ( m"@$n = global i32 ${i.toString}", global_ty + (n -> "Int"))
  }

  case FConst(n, f) => {
    ( m"@$n = global double ${f.toString}", global_ty + (n -> "Double"))
  }

  case Def(name, args, ty, body) => {
    val local_ty = args.toMap
    val k_bod = CPSi(body)
    val typed_bod = typ_exp(k_bod, local_ty, global_ty + (name -> ty))
    val compiled_bod = compile_exp(typed_bod._1) 
    ( m"define ${typ_to_ll(ty)} @$name (${args.map(format_arg).mkString(", ")}) {" ++
    compiled_bod ++
    m"}\n", global_ty + (name -> ty))
  }

  case Main(body) => {
    val k_bod = CPS(body)(_ => KReturn(KInt(0)))
    val typed_bod = typ_exp(k_bod, Map(), global_ty)
    val compiled_bod = compile_exp(typed_bod._1)
    ( m"define i32 @main() {" ++
    compiled_bod ++
    m"}\n", global_ty )
  }
}

def compile_helper(prog: List[Decl], global_ty: TyEnv = init_global) : (String, TyEnv) = prog match {
  case Nil => ("", global_ty)
  case d::rest => {
    val compiled_d = compile_decl(d, global_ty)
    val compiled_rest = compile_helper(rest, compiled_d._2)
    (compiled_d._1 ++ compiled_rest._1, compiled_rest._2)
  }
}

// main compiler functions
def compile(prog: List[Decl]) : String = 
  prelude ++ compile_helper(prog)._1.mkString


import ammonite.ops._


@main
def main(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    println(compile(ast))
}

@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    val code = compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}

@main
def run(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    write(fname)  
    os.proc("llc", "-filetype=obj", file ++ ".ll").call()
    os.proc("gcc", file ++ ".o", "-o", file ++ ".bin").call()
    os.proc(os.pwd / (file ++ ".bin")).call(stdout = os.Inherit)
    println(s"done.")
}




// CPS functions
/*

def fact(n: Int) : Int = 
  if (n == 0) 1 else n * fact(n - 1)

fact(6)

def factT(n: Int, acc: Int) : Int =
  if (n == 0) acc else factT(n - 1, acc * n)

factT(6, 1)

def factC(n: Int, ret: Int => Int) : Int = {
  if (n == 0) ret(1) 
  else factC(n - 1, x => ret(x * n))
}

factC(6, x => x)
factC(6, x => {println(s"The final Result is $x") ; 0})
factC(6, _ + 1)

def fibC(n: Int, ret: Int => Int) : Int = {
  if (n == 0 || n == 1) ret(1)
  else fibC(n - 1, x => fibC(n - 2, y => ret(x + y)))
}

fibC(10, x => {println(s"Result: $x") ; 1})


*/



//some testcases:
// numbers and vars   
println(CPSi(Num(1)).toString)
println(CPSi(Var("z")).toString)

//  a * 3
val e1 = Aop("*", Var("a"), Num(3))
println(CPSi(e1).toString)

// (a * 3) + 4
val e2 = Aop("+", Aop("*", Var("a"), Num(3)), Num(4))
println(CPSi(e2).toString)

// 2 + (a * 3)
val e3 = Aop("+", Num(2), Aop("*", Var("a"), Num(3)))
println(CPSi(e3).toString)

//(1 - 2) + (a * 3)
val e4 = Aop("+", Aop("-", Num(1), Num(2)), Aop("*", Var("a"), Num(3)))
println(CPSi(e4).toString)

// 3 + 4 ; 1 * 7
val es = Sequence(Aop("+", Num(3), Num(4)),
                  Aop("*", Num(1), Num(7)))
println(CPSi(es).toString)

// if (1 == 1) then 3 else 4
val e5 = If(Bop("==", Num(1), Num(1)), Num(3), Num(4))
println(CPSi(e5).toString)

// if (1 == 1) then 3 + 7 else 4 * 2
val ei = If(Bop("==", Num(1), Num(1)), 
                Aop("+", Num(3), Num(7)),
                Aop("*", Num(4), Num(2)))
println(CPSi(ei).toString)


// if (10 != 10) then e5 else 40
val e6 = If(Bop("!=", Num(10), Num(10)), e5, Num(40))
println(CPSi(e6).toString)


// foo(3)
val e7 = Call("foo", List(Num(3)))
println(CPSi(e7).toString)

// foo(3 * 1, 4, 5 + 6)
val e8 = Call("foo", List(Aop("*", Num(3), Num(1)), 
                          Num(4), 
                          Aop("+", Num(5), Num(6))))
println(CPSi(e8).toString)

// a * 3 ; b + 6
val e9 = Sequence(Aop("*", Var("a"), Num(3)), 
                  Aop("+", Var("b"), Num(6)))
println(CPSi(e9).toString)


val e10 = Aop("*", Aop("+", Num(1), Call("foo", List(Var("a"), Num(3)))), Num(4))
println(CPSi(e10).toString)
