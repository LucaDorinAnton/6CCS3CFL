// Coursework 1 solution by Luca-Dorin Anton - Student id 1710700
// Based on re3.scala - 6CCS3CFL - Dr. Christian Urban


// A version with simplification of derivatives;
// this keeps the regular expressions small, which
// is good for the run-time


abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CFUN(f : Char => Boolean) extends Rexp // cfun instead of char, range and all
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
// added by me
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class UPTO(r: Rexp, n: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp

// some functions to test CFUN

def matchA(c: Char) : Boolean = c == 'a'
def matchB(c: Char) : Boolean = c == 'b'
def matchC(c: Char) : Boolean = c == 'c'
def matchSetAtoC(c: Char) : Boolean = Set[Char]('a', 'b', 'c').contains(c)
def matchSetAandB(c: Char) : Boolean = Set[Char]('a', 'b', 'c').contains(c)
def matchAll(c: Char): Boolean = true

// the nullable function: tests whether the regular
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  // Added by me
  case CFUN(_) => false //implementation for CFUN
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case UPTO(_, _) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n ,m) => if (n == 0) true else nullable(r)
  case NOT(r) => ! nullable(r)
}

// the derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CFUN(f) => if (f(c)) ONE else ZERO //implementation for CFUN
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case NTIMES(r, i) =>
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  // Added by me

  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case UPTO(r, n) => if (n == 0) ZERO else SEQ(der(c, r), UPTO(r, n - 1))
  case FROM(r, n) => if (n == 0) ONE else SEQ(der(c, r), FROM(r, n - 1))
  case BETWEEN(r, n, m)=> (n, m) match {
    case (0, 0) => ONE
    case (0, m) => SEQ(der(c, r), UPTO(r, m - 1))
    case (n, m) => SEQ(der(c, r), BETWEEN(r, n - 1, m - 1))
  }
  case NOT(r) => NOT(der(c, r))
}


def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}


// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}


// the main matcher function
def matcher(r: Rexp, s: String) : Boolean =
  nullable(ders(s.toList, r))


//set for the CFUN class
val letters_digits_and_chars = ('a' to 'z').toSet ++ ('0' to '9').toSet ++ Set[Char]('_', '.', '-')

def char_class(c: Char) : Boolean = letters_digits_and_chars.contains(c)
def atoZ(c: Char) : Boolean = ('a' to 'z').toSet.contains(c)
def char_at(c: Char) : Boolean = c == '@'
def char_dot(c: Char) : Boolean = c == '.'
def aToZandDot(c: Char) : Boolean = (('a' to 'z').toSet ++ Set[Char]('.')).contains(c)
//regular expression for emails
val email_1 = SEQ(PLUS(CFUN(char_class)), CFUN(char_at)) // matches everythin before @ including @
val email_2 = SEQ(PLUS(CFUN(char_class)), CFUN(char_dot)) // matches from @ (exclusive) to . (inclusive)
val email_3 = BETWEEN(CFUN(aToZandDot), 2, 6) //matches domain
val email_4 = SEQ(email_1, email_2) // matches everything excluding domain
val email_final = SEQ(email_4, email_3) // matches everythin

val my_email = "luca-dorin.anton@kcl.ac.uk"

val der_email = ders(my_email.toList, email_final)

"""
 der_email with fancy formatting...

ALT(
  SEQ(
    SEQ(
      STAR(
        CFUN(<function1>)
      ),
      CFUN(<function1>)
    ),
    BETWEEN(
      CFUN(<function1>)
      ,2,6)
  ),
  BETWEEN(
    CFUN(<function1>)
    ,0,4)
)

"""

def matchSlash(c: Char) : Boolean = c == '/'
def matchStar(c: Char) : Boolean = c == '*'


val weird_part = NOT(SEQ(SEQ(STAR(CFUN(matchAll)), CFUN(matchStar)), SEQ(CFUN(matchSlash), STAR(CFUN(matchAll)))))
val weird = SEQ(SEQ(SEQ(SEQ(CFUN(matchSlash), CFUN(matchStar)), weird_part), CFUN(matchStar)), CFUN(matchSlash))

val test1 = "/**/" /// true
val test2 = "/*foobar*/" // true
val test3 = "/*test*/test*/" //false
val test4 = "/*test/*test*/" // true


















// Test Cases

// evil regular expressions: (a?){n} a{n}  and (a*)* b
def EVIL1(n: Int) = SEQ(NTIMES(OPT(CHAR('a')), n), NTIMES(CHAR('a'), n))
val EVIL2 = SEQ(STAR(STAR(CHAR('a'))), CHAR('b'))


def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


//test: (a?{n}) (a{n})
for (i <- 0 to 8000 by 1000) {
  println(f"$i: ${time_needed(3, matcher(EVIL1(i), "a" * i))}%.5f")
}

//test: (a*)* b
for (i <- 0 to 6000000 by 500000) {
  println(f"$i: ${time_needed(3, matcher(EVIL2, "a" * i))}%.5f")
}


// size of a regular expressions - for testing purposes
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case ALT(r1, r2) => 1 + size(r1) + size(r2)
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case STAR(r) => 1 + size(r)
  case NTIMES(r, _) => 1 + size(r)
}


// now the size of the derivatives grows
// much, much slower

size(ders("".toList, EVIL2))      // 5
size(ders("a".toList, EVIL2))     // 8
size(ders("aa".toList, EVIL2))    // 8
size(ders("aaa".toList, EVIL2))   // 8
size(ders("aaaa".toList, EVIL2))  // 8
size(ders("aaaaa".toList, EVIL2)) // 8
