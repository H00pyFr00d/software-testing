import scala.collection.immutable.ListMap
import Console.{BLACK, GREEN, RED, RESET, UNDERLINED, YELLOW_B}
import org.scalatest.funsuite.AnyFunSuite
import FrogInterpreter.Syntax.*
import FrogInterpreter.{Interpreter, Parser, Typer}

val tyCheck: (Env, Expr, Type) => Unit = Typer.tyCheck
val tyInfer: (Env, Expr) => Type = Typer.tyInfer
val parser: Parser = Interpreter.parser
val emptyEnv: Env = ListMap[Variable, Type]()

def check(e: Expr, t: Type): Unit = tyCheck(emptyEnv, e, t)
def exp(s: String): Expr = parser.parseStr(s)
def typ(s: String): Type = parser.parseTyStr(s)

def typeTest(pack: (() => Expr, () => Type)): (Boolean, String) = {
  val (e, ty) = pack
  var err = false
  var msg = "No error."
  try {
    check(e(), ty())
  } catch {
    case error:Throwable =>
      err = true
      msg = error.getMessage
  }
  (err, msg)
}

// ======================================= Unit Tests =======================================

// Arithmetic expressions
class ArithTypeTests extends AnyFunSuite {
  test("var int") {
    val (err, msg) = typeTest((() => exp("let x = 1 in x"), () => typ("int")))
    assert(!err, msg)
  }

  test("plus") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in x + y"), () => typ("int"))
    assert(!err, msg)
  }

  test("minus") {
    val (err, msg) = typeTest(() => exp("let x = 2 in let y = 1 in x - y"), () => typ("int"))
    assert(!err, msg)
  }

  test("times") {
    val (err, msg) = typeTest(() => exp("let x = 2 in let y = 3 in x * y"), () => typ("int"))
    assert(!err, msg)
  }
}

// Booleans
class BooleanTypeTests extends AnyFunSuite {
  test("var bool") {
    val (err, msg) = typeTest(() => exp("let x = true in x"), () => typ("bool"))
    assert(!err, msg)
  }

  test("are eq") {
    val (err, msg) = typeTest(() => exp("let x = 1 in x == 1"), () => typ("bool"))
    assert(!err, msg)
  }

  test("are not eq") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in x == y"), () => typ("bool"))
    assert(!err, msg)
  }

  test("less") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in x < y"), () => typ("bool"))
    assert(!err, msg)
  }

  test("if then else") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in if x < y then x else y"), () => typ("int"))
    assert(!err, msg)
  }
}

// Strings
class StringTypeTests extends AnyFunSuite {
  test("var str") {
    val (err, msg) = typeTest(() => exp("let x = \"hello\" in x"), () => typ("string"))
    assert(!err, msg)
  }

  test("length") {
    val (err, msg) = typeTest(() => exp("let x = \"hello\" in length(x)"), () => typ("int"))
    assert(!err, msg)
  }

  test("index") {
    val (err, msg) = typeTest(() => exp("let x = \"hello\" in index(x, 0)"), () => typ("string"))
    assert(!err, msg)
  }

  test("concat") {
    val (err, msg) = typeTest(() => exp("concat(\"hello\", \"world\")"), () => typ("string"))
    assert(!err, msg)
  }
}

// Variables and let-binding
class VariableTypeTests extends AnyFunSuite {
  test("var let") {
    val (err, msg) = typeTest(() => exp("let x = 1 in x"), () => typ("int"))
    assert(!err, msg)
  }

  test("anno") {
    val (err, msg) = typeTest(() => exp("let x = 1 in (x : int)"), () => typ("int"))
    assert(!err, msg)
  }
}

// Functions
class FunctionTypeTests extends AnyFunSuite {
  test("lambda") {
    val (err, msg) = typeTest(() => exp("\\x . x + 1"), () => typ("int -> int"))
    assert(!err, msg)
  }
}

// Pairing
class PairTypeTests extends AnyFunSuite {
  test("pair") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in (x, y)"), () => typ("int * int"))
    assert(!err, msg)
  }

  test("first") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in let z = (x, y) in fst(z)"), () => typ("int"))
    assert(!err, msg)
  }

  test("second") {
    val (err, msg) = typeTest(() => exp("let x = 1 in let y = 2 in let z = (x, y) in snd(z)"), () => typ("int"))
    assert(!err, msg)
  }
}

// Records
class RecordTypeTests extends AnyFunSuite {
  test("record") {
    val (err, msg) = typeTest(() => exp("<foo = 1, bar = true>"), () => typ("<foo: int, bar: bool>"))
    assert(!err, msg)
  }

  test("projection") {
    val (err, msg) = typeTest(() => exp("let x = <foo = 1, bar = true> in x.foo"), () => typ("int"))
    assert(!err, msg)
  }
}

// Variants
class VariantTypeTests extends AnyFunSuite {
  test("variant") {
    val (err, msg) = typeTest(() => exp("select foo 1"), () => typ("[foo: int]"))
    assert(!err, msg)
  }
}

// Bags
class BagTypeTests extends AnyFunSuite {
  test("bag") {
    val (err, msg) = typeTest(() => exp("{|1, 2, 3, 4, 5|}"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("flat map (lambda)") {
    val (err, msg) = typeTest(() => exp("flatMap({|1, 2, 3|}, \\x . {| x, x |})"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("flat map (function)") {
    val (err, msg) = typeTest(() => exp("sig f : int -> {|int|} let fun f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("when") {
    val (err, msg) = typeTest(() => exp("when(true, {| 1 , 2 |})"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("count") {
    val (err, msg) = typeTest(() => exp("count({|1, 2, 3, 4, 5|}, 3)"), () => typ("int"))
    assert(!err, msg)
  }

  test("sum") {
    val (err, msg) = typeTest(() => exp("sum({|1, 2, 3, 4, 5|}, {| 6, 7, 8 |})"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("diff") {
    val (err, msg) = typeTest(() => exp("diff({|1, 2, 3, 4, 5|}, {|1, 2, 3|})"), () => typ("{|int|}"))
    assert(!err, msg)
  }
}

// Syntactic sugar
class SyntacticSugarTypeTests extends AnyFunSuite {
  test("let pair") {
    val (err, msg) = typeTest(() => exp("let (x, y) = (1, 2) in x + y"), () => typ("int"))
    assert(!err, msg)
  }

  test("let fun") {
    val (err, msg) = typeTest(() => exp("sig f : int -> int let fun f(x) = x + 1 in f(1)"), () => typ("int"))
    assert(!err, msg)
  }

  test("let rec") {
    val (err, msg) = typeTest(() => exp("sig f : int -> int let rec f(x) = if x == 0 then 0 else f(x - 1) in f(5)"), () => typ("int"))
    assert(!err, msg)
  }

  test("let record") {
    val (err, msg) = typeTest(() => exp("let <foo = x, bar = y> = <foo = 1, bar = 2> in x + y"), () => typ("int"))
    assert(!err, msg)
  }

  test("comprehension w/ bind") {
    val (err, msg) = typeTest(() => exp("{| x | x <- {|1, 2, 3|} |}"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("comprehension w/ guard") {
    val (err, msg) = typeTest(() => exp("{| x | x <- {|1, 2, 3|}, 1 < x |}"), () => typ("{|int|}"))
    assert(!err, msg)
  }

  test("comprehension w/ let") {
    val (err, msg) = typeTest(() => exp("{| x + y | let x = 1, y <- {| 1, 2, 3 |} |}"), () => typ("{|int|}"))
    assert(!err, msg)
  }
}