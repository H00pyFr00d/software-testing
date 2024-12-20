import Assign3.Syntax.Syntax._
import Assign3.Interpreter._
import scala.collection.immutable.ListMap
import Console.{GREEN, RED, BLACK, RESET, YELLOW_B, UNDERLINED}

val subst = Interpreter.SubstExpr.subst

val parser = Interpreter.parser

val desugar = Interpreter.desugar

val eval = Interpreter.eval

def aequiv(e1: Expr, e2:Expr): Boolean = {
  def equivVar(l: List[(Variable,Variable)], v1: Variable, v2: Variable): Boolean = l match {
    case Nil => v1 == v2
    case (x1,x2)::xs =>
      if (v1 == x1 || v2 == x2) {
        v1 == x1 && v2 == x2
      } else {
        equivVar(xs,v1,v2)
      }
  };
  def go(l: List[(Variable,Variable)], e1: Expr, e2: Expr): Boolean = (e1,e2) match {
    case (Unit, Unit) => true

    case (Num(n), Num(m)) => n == m
    case (Plus(e11,e12), Plus(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Times(e11,e12), Times(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Minus(e11,e12), Minus(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)

    case (Bool(b1), Bool(b2)) => b1 == b2
    case (Eq(e11,e12), Eq(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (IfThenElse(e10,e11,e12), IfThenElse(e20,e21,e22)) =>
      go(l,e10,e20) && go(l,e11,e21) && go(l,e12,e22)

    case (Str(s1), Str(s2)) => s1 == s2
    case (Length(e1), Length(e2)) =>
      go(l,e1,e2)
    case (Index(e11,e12), Index(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Concat(e11,e12), Concat(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)

    case (Var(v1),Var(v2)) => equivVar(l,v1,v2)
    case (Let(x1,e11,e12),Let(x2,e21,e22)) =>
      go(l,e11,e21) && go((x1,x2)::l,e12,e22)
    case (LetFun(f1,_,x1,e11,e12),LetFun(f2,_,x2,e21,e22)) =>
      go((x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
    case (LetRec(f1,_,x1,e11,e12),LetRec(f2,_,x2,e21,e22)) =>
      go((f1,f2)::(x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
    case (LetPair(x1,y1,e11,e12), LetPair(x2,y2,e21,e22)) =>
      go(l,e11,e21) && go((x1,x2)::(y1,y2)::l, e12,e22)
    case (LetRecord(xs1,e11,e12),LetRecord(xs2,e21,e22)) =>
      // assumes no variables repeated
      if xs1.keys != xs2.keys then false
      else {
        val vars = xs1.keys.map{(k) => (xs1(k),xs2(k))}.toList
        go(l,e11,e12) && go(vars ++ l,e12,e22)
      }

    case (Pair(e11,e12), Pair(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (First(e1), First(e2)) =>
      go(l,e1,e2)
    case (Second(e1), Second(e2)) =>
      go(l,e1,e2)

    case (Lambda(x1,e1),Lambda(x2,e2)) =>
      go((x1,x2)::l,e1,e2)
    case (Apply(e11,e12), Apply(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Rec(f1,x1,e1),Rec(f2,x2,e2)) =>
        go((f1,f2)::(x1,x2)::l,e1,e2)

    case (Record(es1),Record(es2)) =>
      es1.keys == es2.keys &&
        es1.keys.forall{(k) => go(l,es1(k),es2(k))}
    case (Proj(e1,l1),Proj(e2,l2)) =>
      l1 == l2 && go(l,e1,e2)

    case (Variant(l1,e1),Variant(l2,e2)) =>
      l1 == l2 && go(l,e1,e2)
    case (Case(e1,cls1),Case(e2,cls2)) =>
      cls1.keys == cls2.keys &&
        cls1.keys.forall{(k) =>
          val (x1,e1) = cls1(k)
          val (x2,e2) = cls2(k)
          go((x1,x2)::l,e1,e2)
        }

    case (Anno(e1,t1),Anno(e2,t2)) => go(l,e1,e2)

    case (e1,e2) => e1 == e2
    // NOTE: α-equivalence for bag-relevant expressions is not implemented yet.
  };
  go(Nil,e1,e2)
}

// Official tests
lazy val substExp1: Boolean = aequiv(
  subst(
    parser.parseStr("""
        (\y.x + y) x
       """), parser.parseStr("(y+y)"),
    "x"),
  parser.parseStr("""
        (\z.(y + y) + z) (y+y)
       """))

val expr1: String = "((\\y.x + y) x)[x = (y + y)] => (\\z.(y + y) + z) (y+y)"

lazy val substExp2: Boolean = aequiv(
    subst(
      parser.parseStr("""
        let y = x in
        x + y
       """), parser.parseStr("(y+y)"),
      "x"),
      parser.parseStr("""
        let z = (y + y) in (y + y) + z
       """))

val expr2: String = "(let y = x in x + y)[x = (y + y)] => let z = (y + y) in (y + y) + z"

lazy val substExp3: Boolean =
  aequiv(
    subst(
      parser.parseStr("""
        (rec f (y).
          if (y == 0) then
            y else
            x + f(y - 1))
        y
       """),
      parser.parseStr("f y"),
      "x"),
    parser.parseStr("""
        (rec g (z).
          if (z == 0) then
            z else
            (f y) + g(z - 1))
        y
       """))

val expr3: String = "((rec f (y). if (y == 0) then y else x + f(y - 1)) y)[x = f y] => (rec g (z). if (z == 0) then z else (f y) + g(z - 1)) y"

lazy val substExp4: Boolean = aequiv(
  subst(
    desugar(parser.parseStr("""
        let (y,z) = (x,x+1) in
        x + y + z
       """)), parser.parseStr("(y*z)"),
    "x"),
    desugar(parser.parseStr("""
        let (a,b) = ((y*z),(y*z)+1) in
        (y*z) + a + b
       """)))

val expr4: String = "(let (y,z) = (x,x+1) in x + y + z)[x = (y*z)] => let (a,b) = ((y*z),(y*z)+1) in (y*z) + a + b"

lazy val substExp5: Boolean = aequiv(
  subst(
    desugar(parser.parseStr("""
        sig f: int -> int let fun f(y) = x + y in f x
       """)), parser.parseStr("(y+y)"),
    "x"),
     desugar( parser.parseStr("""
        sig f: int -> int let fun f(z) = (y+y) + z in f (y+y)
       """)))

val expr5: String = "(sig f: int -> int let fun f(y) = x + y in f x)[x = (y+y)] => sig f: int -> int let fun f(z) = (y+y) + z in f (y+y)"

lazy val substExp6: Boolean =
  aequiv(
    subst(
      desugar(parser.parseStr("""
        sig f: int -> int let rec f (y) =
          if (y == 0) then
            y else
            x + f(y - 1)
        in f y
       """)),
      parser.parseStr("f y"),
      "x"),
    desugar(parser.parseStr("""
        sig g: int -> int let rec g (z) =
          if (z == 0) then
            z else
            (f y) + g(z - 1)
        in g y
       """)))

val expr6: String = "(sig f: int -> int let rec f (y) = if (y == 0) then y else x + f(y - 1) in f y)[x = f y] => sig g: int -> int let rec g (z) = if (z == 0) then z else (f y) + g(z - 1) in g y"

lazy val substExp7: Boolean =
  eval(
    subst(desugar(parser.parseStr("""sig f: int -> int let rec f(x) = x+1 in f 12""")),Num(14),"x")) == NumV(13)

val expr7: String = "(sig f: int -> int let rec f(x) = x+1 in f 12)[x = 14] == 13"

lazy val substExp8: Boolean =
  eval(
    subst(desugar(parser.parseStr("""sig x: int -> int let rec x (y) = if y == 12 then x (y+1) else (y+1) in x 12""")),Num(26),"x")) == NumV(14)

val expr8: String = "(sig x: int -> int let rec x (y) = if y == 12 then x (y+1) else (y+1) in x 12)[x = 26] == 14"

lazy val substExp9: Boolean =
  aequiv(subst(Rec("f","x",Plus(Num(2),Var("x"))),Num(20),"x"), Rec("f","x",Plus(Num(2),Var("x"))))

val expr9: String = "(Rec(f,x,2+x))[x = 20] ==ₐ Rec(f,x,2+x)"

lazy val substExp10: Boolean =
  eval(
    subst(desugar(parser.parseStr("""let (a,b) = (12,13) in (sig f:int -> int let rec f (x) = x+1 in f a)""")),Num(14),"x")) == NumV(13)

val expr10: String = "(let (a,b) = (12,13) in (sig f:int -> int let rec f (x) = x+1 in f a)[x = 14] == 13"

lazy val substExp11: Boolean =
  eval(
    subst(desugar(parser.parseStr("""let (a,b) = (12,13) in (sig f:int->int let fun f(x) = x+1 in f a)""")),Num(14),"x")) == NumV(13)

val expr11: String = "(let (a,b) = (12,13) in (sig f:int->int let fun f(x) = x+1 in f a))[x = 14] == 13"

lazy val substExp12: Boolean =
  eval(
    subst(desugar(parser.parseStr("""let (a,b) = (12,13) in (sig f:int->int let rec f(x) = x+1 in f a)""")),Num(14),"x")) == NumV(13)

val expr12: String = "(let (a,b) = (12,13) in (sig f:int->int let rec f(x) = x+1 in f a))[x = 14] == 13"

// Broken - see @54 on Piazza
// lazy val substExp13: Boolean =
//   aequiv(
//     subst(
//       parser.parseStr("""
//       {| y | let x = 4, let y = x + 1 |}
//        """),
//       parser.parseStr("2"),
//       "x"),
//     parser.parseStr("""
//       {| y | let x = 4, let y = x + 1 |}
//        """))

// val expr13: String = "{| y | let x = 4, let y = x + 1 |}[x = 2] => {| y | let x = 4, let y = x + 1 |}"

// Personal tests

// Substitutions

// Evaluation
lazy val plus: Boolean = eval(parser.parseStr("1 + 2")) == NumV(3)
lazy val minus: Boolean = eval(parser.parseStr("1 - 2")) == NumV(-1)
lazy val times: Boolean = eval(parser.parseStr("2 * 3")) == NumV(6)

lazy val eq: Boolean = eval(parser.parseStr("1 == 1")) == BoolV(true)
lazy val ifThenElseTrue: Boolean = eval(parser.parseStr("if true then 1 else 2")) == NumV(1)
lazy val ifThenElseFalse: Boolean = eval(parser.parseStr("if false then 1 else 2")) == NumV(2)

lazy val letInt: Boolean = eval(parser.parseStr("let x = 1 in x")) == NumV(1)
lazy val letBool: Boolean = eval(parser.parseStr("let x = true in x")) == BoolV(true)
lazy val letStr: Boolean = eval(parser.parseStr("let x = \"hello\" in x")) == StringV("hello")

lazy val length: Boolean = eval(parser.parseStr("length(\"hello\")")) == NumV(5)
lazy val index: Boolean = eval(parser.parseStr("index(\"hello\", 1)")) == StringV("e")
lazy val concat: Boolean = eval(parser.parseStr("concat(\"hello \", \"world\")")) == StringV("hello world")

lazy val lambda: Boolean = eval(parser.parseStr("\\x. x + 1")) == FunV("x",Plus(Var("x"),Num(1)))

lazy val rec: Boolean = eval(desugar(parser.parseStr("""sig f : int -> int let rec f(x) = if (x == 0) then 1 else f(x - 1) in f(10)"""))) == NumV(1)

lazy val pair: Boolean = eval(parser.parseStr("(1, 2)")) == PairV(NumV(1),NumV(2))
lazy val first: Boolean = eval(parser.parseStr("fst((1, 2))")) == NumV(1)
lazy val second: Boolean = eval(parser.parseStr("snd((1, 2))")) == NumV(2)

lazy val record: Boolean = eval(parser.parseStr("<foo = 1, bar = true>")) == RecordV(ListMap("foo" -> NumV(1), "bar" -> BoolV(true)))
lazy val proj: Boolean = eval(parser.parseStr("let x = <foo = 1, bar = true> in x.foo")) == NumV(1)

lazy val variant: Boolean = eval(parser.parseStr("select x 1")) == VariantV("x",NumV(1))
lazy val caseVariant: Boolean = eval(desugar(parser.parseStr("sig f : [some: int, none: unit] -> int let fun f(x) = case x of {some y -> y, none z -> 0} in f(select some 42)"))) == NumV(42)

lazy val bag: Boolean = eval(parser.parseStr("{| 1, 2, 3 |}")) == BagV(List(NumV(1),NumV(2),NumV(3)))
lazy val flatMapFunc: Boolean = eval(desugar(parser.parseStr("sig f : int -> {| int |} let fun f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)"))) == BagV(List(NumV(2), NumV(3), NumV(4)))
lazy val flatMapRec: Boolean = eval(desugar(parser.parseStr("sig f : int -> {| int |} let rec f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)"))) == BagV(List(NumV(2), NumV(3), NumV(4)))
lazy val whenTrue: Boolean = eval(parser.parseStr("when({| 1, 2, 3 |}, true)")) == BagV(List(NumV(1), NumV(2), NumV(3)))
lazy val whenFalse: Boolean = eval(parser.parseStr("when({| 1, 2, 3 |}, false)")) == BagV(List())
lazy val count: Boolean = eval(parser.parseStr("count({| 1, 2, 2, 3 |}, 2)")) == NumV(2)
lazy val sum: Boolean = eval(parser.parseStr("sum({| 1, 2, 2, 3 |}, {| 1, 2 |})")) == BagV(List(NumV(1), NumV(2), NumV(2), NumV(3), NumV(1), NumV(2)))
lazy val diff: Boolean = eval(parser.parseStr("diff({| 1, 2, 2, 3|}, {| 1, 2 |})")) == BagV(List(NumV(2), NumV(3)))

def test(test: Boolean) = {
  print((if test then s"  [  ${GREEN}Passed${RESET}  ]" else s"  [  ${RED}Failed${RESET}  ]"))
}

@main def runTests() = {
  println("--------------------------------------------------------------- Official tests ---------------------------------------------------------------")
  println("     Result  |  Test Name  |  Test Description")
  test(substExp1) 
  println(" substExp1" + "  : " + expr1)
  test(substExp2)
  println(" substExp2" + "  : " + expr2)
  test(substExp3)
  println(" substExp3" + "  : " + expr3)
  test(substExp4)
  println(" substExp4" + "  : " + expr4)
  test(substExp5)
  println(" substExp5" + "  : " + expr5)
  test(substExp6)
  println(" substExp6" + "  : " + expr6)
  test(substExp7)
  println(" substExp7" + "  : " + expr7)
  test(substExp8)
  println(" substExp8" + "  : " + expr8)
  test(substExp9)
  println(" substExp9" + "  : " + expr9)
  test(substExp10)
  println(" substExp10" + " : " + expr10)
  test(substExp11)
  println(" substExp11" + " : " + expr11)
  test(substExp12)
  println(" substExp12" + " : " + expr12)

  println("\n--------------------------------------------------------------- Personal tests ---------------------------------------------------------------")
  println("     Result  |  Test Name  |  Test Description")
  test(plus)
  println(" plus        : eval(1 + 2) == NumV(3)")
  test(minus)
  println(" minus       : eval(1 - 2) == NumV(-1)")
  test(times)
  println(" times       : eval(2 * 3) == NumV(6)")
  test(eq)
  println(" eq          : eval(1 == 1) == BoolV(true)")
  test(ifThenElseTrue)
  println(" ifThen      : eval(if true then 1 else 2) == NumV(1)")
  test(ifThenElseFalse)
  println(" Else        : eval(if false then 1 else 2) == NumV(2)")
  test(letInt)
  println(" letInt      : eval(let x = 1 in x) == NumV(1)")
  test(letBool)
  println(" letBool     : eval(let x = true in x) == BoolV(true)")
  test(letStr)
  println(" letStr      : eval(let x = \"hello\" in x) == StrV(\"hello\")")
  test(length)
  println(" length      : eval(length(\"hello\")) == NumV(5)")
  test(index)
  println(" index       : eval(index(\"hello\", 1)) == StrV(\"e\")")
  test(concat)
  println(" concat      : eval(concat(\"hello \", \"world\")) == StrV(\"hello world\")")
  test(lambda)
  println(" lambda      : eval(\\x. x + 1) == FunV(\"x\",Plus(Var(\"x\"),Num(1)))")
  test(rec)
  println(" rec         : eval(desugar(sig f : int -> int let rec f(x) = if (x == 0) then 1 else f(x - 1) in f(10)) == 1")
  test(pair)
  println(" pair        : eval((1, 2)) == PairV(NumV(1),NumV(2))")
  test(first)
  println(" first       : eval(fst((1, 2)) == NumV(1)")
  test(second)
  println(" second      : eval(snd((1, 2)) == NumV(2)")
  test(record)
  println(" record      : eval(<foo = 1, bar = true>) == RecordV(Map(\"x\" -> NumV(1), \"y\" -> NumV(2)))")
  test(proj)
  println(" proj        : eval(let x = <foo = 1, bar = true> in x.foo) == NumV(1)")
  test(variant)
  println(" variant     : eval(select x 1) == VariantV(\"x\",NumV(1))")
  test(caseVariant)
  println(" caseVariant : eval(sig f : [some: int, none: unit] -> int let fun f(x) = case x of {some y -> y, none z -> 0} in f(select some 42)) == NumV(42)")
  test(bag) 
  println(" bag         : eval({| 1, 2, 3 |}) == BagV(List(NumV(1), NumV(2), NumV(3)))")
  test(flatMapFunc) // This looks weird but flatMaps can't operate with a function f : int -> int, as this breaks typing
  println(" flatMap     : eval(desugar(sig f : int -> {| int |} let fun f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)) == BagV(List(NumV(2), NumV(3), NumV(4)))")
  test(flatMapRec)
  println(" flatMapRec  : eval(desugar(sig f : int -> {| int |} let rec f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)) == BagV(List(NumV(2), NumV(3), NumV(4)))")
  test(whenTrue)
  println(" whenTrue    : eval(when({| 1, 2, 3 |}, true)) == BagV(List(NumV(1)))")
  test(whenFalse)
  println(" whenFalse   : eval(when({| 1, 2, 3 |}, false)) == BagV(List())")
  test(count)
  println(" count       : eval(count({| 1, 2, 2, 3 |}, 2)) == NumV(2)")
  test(sum) // note that that bags are unordered so if this fails it might be because your implementation puts the bags together in a different way
  println(" sum         : eval(sum({| 1, 2, 2, 3 |}, {| 1, 2 |})) == BagV(List(NumV(1), NumV(2), NumV(2), NumV(3), NumV(1), NumV(2)))")
  test(diff)
  println(" diff        : eval(diff({| 1, 2, 2, 3|}, {| 1, 2 |})) == BagV(List(NumV(2), NumV(3)))")
}
