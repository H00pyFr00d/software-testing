import scala.collection.immutable.ListMap
import Console.{GREEN, RED, BLACK, RESET, YELLOW_B, UNDERLINED}

import Assign3.Syntax.Syntax._
import Assign3.Typer._
import Assign3.Interpreter._

val tyCheck = Typer.tyCheck

val tyInfer = Typer.tyInfer

val parser = Interpreter.parser

val emptyEnv = ListMap[Variable, Type]()

def check(e: Expr, t: Type): Unit = tyCheck(emptyEnv, e, t)

def exp(s: String): Expr = parser.parseStr(s)

def typ(s: String): Type = parser.parseTyStr(s)

// Test begin

val testTy0 = (
  "identity function",
  () => exp("\\x . x"),
  () => typ("int -> int")
)

val testTy1 = (
  "first",
  () => exp("\\x . fst(x)"),
  () => typ("int * bool -> int")
)

val testTy2 = (
  "projection",
  () => exp("sig f : <foo: int> -> int let fun f(x) = x.foo + 42 in f <foo = 0>"),
  () => typ("int")
)

val testTy3 = (
  "advanced projection",
  () => exp("sig f : <foo: int> -> int let fun f(x) = x.foo + 42 in f <foo = 42, bar = true>"),
  () => typ("int")
)

val testTy4 = (
  "case split",
  () => exp("""
  sig g : [foo: int, bar: bool] -> int
  let fun g(x) = case x of {
    foo x -> x,
    bar b -> if b then 42 else 37
  } in g (select bar true)"""),
  () => typ("int")
)

val testTy5 = (
  "annotation and subtyping",
  () => exp("""
  sig g : [foo: int, bar: bool] -> int
  let fun g(x) = case x of {
    foo x -> x,
    bar b -> if b then 42 else 37
  } in g ((select foo 6) : [foo: int])
  """),
  () => typ("int")
)

val testTy6 = (
  "nested subtyping",
  () => exp("sig f : <foo: <bar: int>> -> int let fun f(x) = x.foo.bar in f <foo = <bar = 42, baz = 37>>"),
  () => typ("int")
)

val testTy7 = (
  "power",
  () => exp("""
  rec power (input) .
  let x = fst(input) in
  let n = snd(input) in
  if (n == 0) then 1
  else x * power(x,n-1)
  """),
  () => typ("int * int -> int")
)

val testTy8 = (
  "bags",
  () => exp("""
  let piBag = {|3, 1, 4, 1, 5, 9|} in
  {| x + z | x <- piBag, 4 < x, y <- piBag, let z = y * y |}
  """),
  () => typ("{|int|}")
)

// Semi-official tests
val testTy9 = (
  "factorial",
  () => exp("""
  sig fact : int -> int
  let rec fact(n) = if (n == 0) then 1 else n*fact(n-1) in fact(4)
  """),
  () => typ("int")
)

val testTy10 = (
  "record_subtyping",
  () => exp("""
  sig getName : <name:string> -> string
  let fun getName(x) = x.name in
  let alice = <name = "Alice", age = 9> in
  let bob = <name = "Bob", year = 1984> in
  (getName alice, getName bob)
  """),
  () => typ("string * string")
)

val testTy11 = (
  "advanced variant",
  () => exp("""
  sig f : [some: int, none: unit] -> int
  let fun f(x) = case x of {some y -> y, none z -> 0} in
  f(select some 42)
  """),
  () => typ("int")
)

// Personal tests

// Arithmetic expressions
val var_int = (
  "var int",
  () => exp("let x = 1 in x"),
  () => typ("int")
)

val plus = (
  "plus",
  () => exp("let x = 1 in let y = 2 in x + y"),
  () => typ("int")
)

val minus = (
  "minus",
  () => exp("let x = 2 in let y = 1 in x - y"),
  () => typ("int")
)

val times = (
  "times",
  () => exp("let x = 2 in let y = 3 in x * y"),
  () => typ("int")
)

// Booleans
val var_bool = (
  "bools",
  () => exp("let x = true in x"),
  () => typ("bool")
)

val eq_1 = (
  "are eq",
  () => exp("let x = 1 in x == 1"),
  () => typ("bool")
)

val eq_2 = (
  "are not eq",
  () => exp("let x = 1 in let y = 2 in x == y"),
  () => typ("bool")
)

val less = (
  "less",
  () => exp("let x = 1 in let y = 2 in x < y"),
  () => typ("bool")
)

val if_then_else = (
  "if then else",
  () => exp("let x = 1 in let y = 2 in if x < y then x else y"),
  () => typ("int")
)

// Strings
val var_str = (
  "var str",
  () => exp("let x = \"hello\" in x"),
  () => typ("string")
)

val length = (
  "length",
  () => exp("let x = \"hello\" in length(x)"),
  () => typ("int")
)

val index = (
  "index",
  () => exp("let x = \"hello\" in index(x, 0)"),
  () => typ("string")
)

val concat = (
  "concat",
  () => exp("concat(\"hello\", \"world\")"),
  () => typ("string")
)

// Variables and let-binding
val var_let = (
  "var",
  () => exp("let x = 1 in x"),
  () => typ("int")
)

val anno = (
  "anno",
  () => exp("let x = 1 in (x : int)"),
  () => typ("int")
)

// Functions
val lambda = (
  "lambda",
  () => exp("\\x . x + 1"),
  () => typ("int -> int")
)

// Pairing
val pair = (
  "pair",
  () => exp("let x = 1 in let y = 2 in (x, y)"),
  () => typ("int * int")
)

val first = (
  "first",
  () => exp("let x = 1 in let y = 2 in let z = (x, y) in fst(z)"),
  () => typ("int")
)

val second = (
  "second",
  () => exp("let x = 1 in let y = 2 in let z = (x, y) in snd(z)"),
  () => typ("int")
)

// Records
val record = (
  "record",
  () => exp("<foo = 1, bar = true>"),
  () => typ("<foo: int, bar: bool>")
)

val proj = (
  "projection",
  () => exp("let x = <foo = 1, bar = true> in x.foo"),
  () => typ("int")
)

// Variants
val variant = (
  "variant",
  () => exp("select foo 1"),
  () => typ("[foo: int]")
)


// Bags
val bag = (
  "bag",
  () => exp("{|1, 2, 3, 4, 5|}"),
  () => typ("{|int|}")
)

val flat_map_lambda = (
  "flat map (lambda)",
  () => exp("flatMap({|1, 2, 3|}, \\x . {| x, x |})"),
  () => typ("{|int|}")
)

val flat_map_func = (
  "flat map (function)",
  () => exp("""
  sig f : int -> {|int|} 
  let fun f(x) = {|x + 1|} in 
  flatMap({|1, 2, 3|}, f) 
  """),
  () => typ("{|int|}")
)

val when = (
  "when",
  () => exp("when(true, {| 1 , 2 |})"),
  () => typ("{|int|}")
)

val count = (
  "count",
  () => exp("count({|1, 2, 3, 4, 5|}, 3)"),
  () => typ("int")
)

val sum = (
  "sum",
  () => exp("sum({|1, 2, 3, 4, 5|}, {| 6, 7, 8 |})"),
  () => typ("{|int|}")
)

val diff = (
  "diff",
  () => exp("diff({|1, 2, 3, 4, 5|}, {|1, 2, 3|})"),
  () => typ("{|int|}")
)

// Syntactic sugar
val let_pair = (
  "let pair",
  () => exp("let (x, y) = (1, 2) in x + y"),
  () => typ("int")
)

val let_fun = (
  "let fun",
  () => exp("sig f : int -> int let fun f(x) = x + 1 in f(1)"),
  () => typ("int")
)

val let_rec = (
  "let rec",
  () => exp("sig f : int -> int let rec f(x) = if x == 0 then 0 else f(x - 1) in f(5)"),
  () => typ("int")
)

val let_record = (
  "let record",
  () => exp("let <foo = x, bar = y> = <foo = 1, bar = 2> in x + y"),
  () => typ("int")
)

val comprehension_bind = (
  "comprehension w/ bind",
  () => exp("{| x | x <- {|1, 2, 3|} |}"),
  () => typ("{|int|}")
)

val comprehension_guard = (
  "comprehension w/ guard",
  () => exp("{| x | x <- {|1, 2, 3|}, 1 < x |}"),
  () => typ("{|int|}")
)

val comprehension_let = (
  "comprehension w/ let",
  () => exp("{| x + y | let x = 1, y <- {| 1, 2, 3 |} |}"),
  () => typ("{|int|}")
)

def test(pack: (String, () => Expr, () => Type)) =
  val (s, e, ty) = pack
  Console.print(s"--------------------------------------------------------------- Running <" ++ s ++ ">. ---------------------------------------------------------------\n")
  var noError = true
  try {
    check(e(), ty())
  } catch {
    case msg:Throwable => {
      Console.println(s"\n    [ ${RED} Failed ${RESET} ] - " + msg + "\n")
      noError = false
    }
  }
  if noError then Console.println(s"\n    [ ${GREEN} Passed ${RESET} ] - " + ty() + "\n") else ()

@main def runTests() = {
  println("[ Provided tests ]")
  test(testTy0)
  test(testTy1)
  test(testTy2)
  test(testTy3)
  test(testTy4)
  test(testTy5)
  test(testTy6)
  test(testTy7)
  test(testTy8)
  println("\n\n[ Semi-official tests ]")
  test(testTy9)
  test(testTy10)
  test(testTy11)
  println("\n\n[ Personal tests ]")
  test(var_int)
  test(plus)
  test(minus)
  test(times)
  test(var_bool)
  test(eq_1)
  test(eq_2)
  test(less)
  test(if_then_else)
  test(var_str)
  test(length)
  test(index)
  test(concat)
  test(var_let)
  test(anno)
  test(lambda)
  test(pair)
  test(first)
  test(second)
  test(record)
  test(proj)
  test(variant)
  test(bag)
  test(flat_map_lambda)
  test(flat_map_func)
  test(when)
  test(count)
  test(sum)
  test(diff)
  test(let_pair)
  test(let_fun)
  test(let_rec)
  test(let_record)
  test(comprehension_bind)
  test(comprehension_guard)
  test(comprehension_let)
}