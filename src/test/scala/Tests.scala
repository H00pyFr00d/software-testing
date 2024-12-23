import scala.collection.immutable.ListMap
import Console.{BLACK, GREEN, RED, RESET, UNDERLINED, YELLOW_B}
import org.scalatest.funsuite.AnyFunSuite
import FrogInterpreter.Syntax.*
import FrogInterpreter.{Interpreter, Parser, Typer, Bags}
import scala.annotation.tailrec

// ====================================== Initialising ======================================
val parser: Parser = Interpreter.parser

// [ Typer ]
val tyCheck: (Env, Expr, Type) => Unit = Typer.tyCheck
val tyInfer: (Env, Expr) => Type = Typer.tyInfer
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

// [ Interpreter ]
val subst = Interpreter.SubstExpr.subst
val desugar = Interpreter.desugar
val eval = Interpreter.eval

def aequiv(e1: Expr, e2:Expr): Boolean = {
  @tailrec
  def equivVar(l: List[(Variable,Variable)], v1: Variable, v2: Variable): Boolean = l match {
    case Nil => v1 == v2
    case (x1,x2)::xs => if (v1 == x1 || v2 == x2) {v1 == x1 && v2 == x2} else {equivVar(xs,v1,v2)}
  }

  def go(l: List[(Variable,Variable)], e1: Expr, e2: Expr): Boolean = (e1,e2) match {
    case (Unit, Unit) => true

    case (Num(n), Num(m)) => n == m
    case (Plus(e11,e12), Plus(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)
    case (Times(e11,e12), Times(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)
    case (Minus(e11,e12), Minus(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)

    case (Bool(b1), Bool(b2)) => b1 == b2
    case (Eq(e11,e12), Eq(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)
    case (IfThenElse(e10,e11,e12), IfThenElse(e20,e21,e22)) => go(l,e10,e20) && go(l,e11,e21) && go(l,e12,e22)

    case (Str(s1), Str(s2)) => s1 == s2
    case (Length(e1), Length(e2)) => go(l,e1,e2)
    case (Index(e11,e12), Index(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)
    case (Concat(e11,e12), Concat(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)

    case (Var(v1),Var(v2)) => equivVar(l,v1,v2)
    case (Let(x1,e11,e12),Let(x2,e21,e22)) => go(l,e11,e21) && go((x1,x2)::l,e12,e22)
    case (LetFun(f1,_,x1,e11,e12),LetFun(f2,_,x2,e21,e22)) => go((x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
    case (LetRec(f1,_,x1,e11,e12),LetRec(f2,_,x2,e21,e22)) => go((f1,f2)::(x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
    case (LetPair(x1,y1,e11,e12), LetPair(x2,y2,e21,e22)) => go(l,e11,e21) && go((x1,x2)::(y1,y2)::l, e12,e22)
    case (LetRecord(xs1,e11,e12),LetRecord(xs2,e21,e22)) =>
      // assumes no variables repeated
      if xs1.keys != xs2.keys then false
      else {
        val vars = xs1.keys.map{k => (xs1(k),xs2(k))}.toList
        go(l,e11,e12) && go(vars ++ l,e12,e22)
      }

    case (Pair(e11,e12), Pair(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)
    case (First(e1), First(e2)) => go(l,e1,e2)
    case (Second(e1), Second(e2)) => go(l,e1,e2)

    case (Lambda(x1,e1),Lambda(x2,e2)) => go((x1,x2)::l,e1,e2)
    case (Apply(e11,e12), Apply(e21,e22)) => go(l,e11,e21) && go(l,e12,e22)
    case (Rec(f1,x1,e1),Rec(f2,x2,e2)) => go((f1,f2)::(x1,x2)::l,e1,e2)

    case (Record(es1),Record(es2)) => es1.keys == es2.keys && es1.keys.forall{k => go(l,es1(k),es2(k))}
    case (Proj(e1,l1),Proj(e2,l2)) => l1 == l2 && go(l,e1,e2)

    case (Variant(l1,e1),Variant(l2,e2)) => l1 == l2 && go(l,e1,e2)
    case (Case(e1,cls1),Case(e2,cls2)) =>
      cls1.keys == cls2.keys &&
        cls1.keys.forall{k =>
          val (x1,e1) = cls1(k)
          val (x2,e2) = cls2(k)
          go((x1,x2)::l,e1,e2)
        }

    case (Anno(e1,t1),Anno(e2,t2)) => go(l,e1,e2)

    case (e1,e2) => e1 == e2
    // NOTE: α-equivalence for bag-relevant expressions is not implemented yet.
  }

  go(Nil,e1,e2)
}

// ======================================= Unit Tests ======================================
// Bags
class BagImplTests extends AnyFunSuite {
  test("toList") {
    assert(Bags.BagImpl.toList(ListMap(1 -> 1, 2 -> 1, 3 -> 1)) == List(1,2,3))
  }

  test("fromList") {
    assert(Bags.BagImpl.fromList(List(1,2,3)) == ListMap(1 -> 1, 2 -> 1, 3 -> 1))
  }

  test("toString") {
    assert(Bags.BagImpl.toString(ListMap(1 -> 1, 2 -> 1, 3 -> 1)) == "Bag(1, 2, 3)")
  }

  test("add") {
    assert(Bags.BagImpl.add(ListMap(1 -> 1, 2 -> 1, 3 -> 1), 4) == ListMap(1 -> 1, 2 -> 1, 3 -> 1, 4 -> 1))
  }

  test("sum") {
    assert(Bags.BagImpl.sum(ListMap(1 -> 1, 2 -> 1, 3 -> 1), ListMap(2 -> 1, 3 -> 1, 4 -> 1)) == ListMap(1 -> 1, 2 -> 2, 3 -> 2, 4 -> 1))
  }

  test("diff") {
    assert(Bags.BagImpl.diff(ListMap(1 -> 1, 2 -> 1, 3 -> 1), ListMap(2 -> 1, 3 -> 1)) == ListMap(1 -> 1))
  }

  test("flatMap") {
    assert(Bags.BagImpl.flatMap(ListMap(1 -> 1, 2 -> 1, 3 -> 1), (x: Int) => ListMap(x + 1 -> 1)) == ListMap(2 -> 1, 3 -> 1, 4 -> 1))
  }

  test("count") {
    assert(Bags.BagImpl.count(ListMap(1 -> 1, 2 -> 1, 3 -> 1), 2) == 1)
  }
}

// Interpreter

// Parser

// Syntax
class ValueTests extends AnyFunSuite {
  test("BagV.toString") {
    assert(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)).toString == "Bag(NumV(1), NumV(2), NumV(3))")
  }
}

class SymGeneratorTests extends AnyFunSuite {
  test("genVar") {
    val symGenerator = new SymGenerator
    assert(symGenerator.genVar("x0") == "x0_0")
    assert(symGenerator.genVar("x0") == "x0_1")
    assert(symGenerator.genVar("x0") == "x0_2")
  }

  test("freshVar") {
    val symGenerator = new SymGenerator
    assert(symGenerator.freshVar() == "$0")
    assert(symGenerator.freshVar() == "$1")
    assert(symGenerator.freshVar() == "$2")
  }  
}

class SwapVarTests extends AnyFunSuite {
  test("swapVar (x == y)") {
    assert(swapVar("a", "a", "b") == "b")
  }

  test("swapVar (x != y and x == z)") {
    assert(swapVar("a", "b", "a") == "b")
  }

  test("swapVar (x != y and x != z)") {
    assert(swapVar("a", "b", "c") == "a")
  }
}

// Typer
class IsEqTypeTests extends AnyFunSuite {
  test("Simple") {
    assert(Typer.isEqType(TyUnit))
    assert(Typer.isEqType(TyInt))
    assert(Typer.isEqType(TyString))
    assert(Typer.isEqType(TyBool))
  }

  test("Variant") {
    assert(Typer.isEqType(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
  }

  test("TyPair") {
    assert(Typer.isEqType(TyPair(TyInt, TyInt)))
  }

  test("Non-EqType") {
    assert(!Typer.isEqType(TyFun(TyInt, TyInt)))
    assert(!Typer.isEqType(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.isEqType(TyBag(TyInt)))
  }
}

class SubtypeTests extends AnyFunSuite {
  test("Unit <: Unit") {
    assert(Typer.subtype(TyUnit, TyUnit))
  }

  test("Unit !<: Non-Unit") {
    assert(!Typer.subtype(TyUnit, TyInt))
    assert(!Typer.subtype(TyUnit, TyBool))
    assert(!Typer.subtype(TyUnit, TyString))
    assert(!Typer.subtype(TyUnit, TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyUnit, TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyUnit, TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyUnit, TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyUnit, TyBag(TyInt)))
  }

  test("Int <: Int") {
    assert(Typer.subtype(TyInt, TyInt))
  }

  test("Int !<: Non-Int") {
    assert(!Typer.subtype(TyInt, TyUnit))
    assert(!Typer.subtype(TyInt, TyBool))
    assert(!Typer.subtype(TyInt, TyString))
    assert(!Typer.subtype(TyInt, TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyInt, TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyInt, TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyInt, TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyInt, TyBag(TyInt)))
  }

  test("Bool <: Bool") {
    assert(Typer.subtype(TyBool, TyBool))
  }

  test("Bool !<: Non-Bool") {
    assert(!Typer.subtype(TyBool, TyUnit))
    assert(!Typer.subtype(TyBool, TyInt))
    assert(!Typer.subtype(TyBool, TyString))
    assert(!Typer.subtype(TyBool, TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyBool, TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyBool, TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyBool, TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyBool, TyBag(TyInt)))
  }

  test("String <: String") {
    assert(Typer.subtype(TyString, TyString))
  }

  test("String !<: Non-String") {
    assert(!Typer.subtype(TyString, TyUnit))
    assert(!Typer.subtype(TyString, TyInt))
    assert(!Typer.subtype(TyString, TyBool))
    assert(!Typer.subtype(TyString, TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyString, TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyString, TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyString, TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyString, TyBag(TyInt)))
  }

  test("Pair <: Pair") {
    assert(Typer.subtype(TyPair(TyInt, TyInt), TyPair(TyInt, TyInt)))
  }

  test("Pair !<: Non-Pair") {
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyUnit))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyInt))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyBool))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyString))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyPair(TyInt, TyInt), TyBag(TyInt)))
  }

  test("Function <: Function") {
    assert(Typer.subtype(TyFun(TyInt, TyInt), TyFun(TyInt, TyInt)))
  }

  test("Function !<: Non-Function") {
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyUnit))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyInt))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyBool))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyString))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyFun(TyInt, TyInt), TyBag(TyInt)))
  }

  test("Record <: Record - Same") {
    assert(Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
  }

  test("Record <: Record - Different Order") {
    assert(Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyRecord(ListMap("bar" -> TyInt, "foo" -> TyInt))))
  }

  test("Record <: Smaller Record") {
    assert(Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyRecord(ListMap("foo" -> TyInt))))
  }

  test("Record !<: Bigger Record") {
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt, "baz" -> TyInt))))
  }

  test("Record !<: Non-Record") {
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyUnit))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyInt))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyBool))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyString))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyBag(TyInt)))
  }

  test("Variant <: Variant - Same") {
    assert(Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
  }

  test("Variant <: Variant - Different Order") {
    assert(Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyVariant(ListMap("bar" -> TyInt, "foo" -> TyInt))))
  }

  test("Variant <: Smaller Variant") {
    assert(Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt, "baz" -> TyInt))))
  }

  test("Variant !<: Bigger Variant") {
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyVariant(ListMap("foo" -> TyInt))))
  }

  test("Variant !<: Non-Variant") {
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyUnit))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyInt))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyBool))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyString))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt)), TyBag(TyInt)))
  }

  test("Bag <: Bag") {
    assert(Typer.subtype(TyBag(TyInt), TyBag(TyInt)))
  }

  test("Bag !<: Non-Bag") {
    assert(!Typer.subtype(TyBag(TyInt), TyUnit))
    assert(!Typer.subtype(TyBag(TyInt), TyInt))
    assert(!Typer.subtype(TyBag(TyInt), TyBool))
    assert(!Typer.subtype(TyBag(TyInt), TyString))
    assert(!Typer.subtype(TyBag(TyInt), TyPair(TyInt, TyInt)))
    assert(!Typer.subtype(TyBag(TyInt), TyFun(TyInt, TyInt)))
    assert(!Typer.subtype(TyBag(TyInt), TyRecord(ListMap("foo" -> TyInt, "bar" -> TyInt))))
    assert(!Typer.subtype(TyBag(TyInt), TyVariant(ListMap("foo" -> TyInt, "bar" -> TyInt))))
  }
}

// =================================== Integration Tests ===================================
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
class ArithInterpreterTests extends AnyFunSuite {
  test("plus") {
    assert(eval(parser.parseStr("1 + 2")) == NumV(3))
  }

  test("minus") {
    assert(eval(parser.parseStr("1 - 2")) == NumV(-1))
  }

  test("times") {
    assert(eval(parser.parseStr("2 * 3")) == NumV(6))
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
class BooleanInterpreterTests extends AnyFunSuite {
  test("eq") {
    assert(eval(parser.parseStr("1 == 1")) == BoolV(true))
  }

  test("ifThenElse (True)") {
    assert(eval(parser.parseStr("if true then 1 else 2")) == NumV(1))
  }

  test("ifThenElse (False)") {
    assert(eval(parser.parseStr("if false then 1 else 2")) == NumV(2))
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
class StringInterpreterTests extends AnyFunSuite {
  test("length") {
    assert(eval(parser.parseStr("length(\"hello\")")) == NumV(5))
  }

  test("index") {
    assert(eval(parser.parseStr("index(\"hello\", 1)")) == StringV("e"))
  }

  test("concat") {
    assert(eval(parser.parseStr("concat(\"hello \", \"world\")")) == StringV("hello world"))
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
class LetBindingInterpreterTests extends AnyFunSuite {
  test("let int") {
    assert(eval(parser.parseStr("let x = 1 in x")) == NumV(1))
  }

  test("let bool") {
    assert(eval(parser.parseStr("let x = true in x")) == BoolV(true))
  }

  test("let str") {
    assert(eval(parser.parseStr("let x = \"hello\" in x")) == StringV("hello"))
  }
}

// Functions
class FunctionTypeTests extends AnyFunSuite {
  test("lambda") {
    val (err, msg) = typeTest(() => exp("\\x . x + 1"), () => typ("int -> int"))
    assert(!err, msg)
  }
}

class FunctionInterpreterTests extends AnyFunSuite {
  test("lambda") {
    assert(eval(parser.parseStr("\\x. x + 1")) == FunV("x",Plus(Var("x"),Num(1))))
  }

  test("rec") {
    assert(eval(desugar(parser.parseStr("""sig f : int -> int let rec f(x) = if (x == 0) then 1 else f(x - 1) in f(10)"""))) == NumV(1))
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
class PairInterpreterTests extends AnyFunSuite {
  test("pair") {
    assert(eval(parser.parseStr("(1, 2)")) == PairV(NumV(1),NumV(2)))
  }

  test("first") {
    assert(eval(parser.parseStr("fst((1, 2))")) == NumV(1))
  }

  test("second") {
    assert(eval(parser.parseStr("snd((1, 2))")) == NumV(2))
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
class RecordInterpreterTests extends AnyFunSuite {
  test("record") {
    assert(eval(parser.parseStr("<foo = 1, bar = true>")) == RecordV(ListMap("foo" -> NumV(1), "bar" -> BoolV(true))))
  }

  test("projection") {
    assert(eval(parser.parseStr("let x = <foo = 1, bar = true> in x.foo")) == NumV(1))
  }
}

// Variants
class VariantTypeTests extends AnyFunSuite {
  test("variant") {
    val (err, msg) = typeTest(() => exp("select foo 1"), () => typ("[foo: int]"))
    assert(!err, msg)
  }
}
class VariantInterpreterTests extends AnyFunSuite {
  test("variant") {
    assert(eval(parser.parseStr("select x 1")) == VariantV("x",NumV(1)))
  }

  test("case statement") {
    assert(eval(desugar(parser.parseStr("sig f : [some: int, none: unit] -> int let fun f(x) = case x of {some y -> y, none z -> 0} in f(select some 42)"))) == NumV(42))
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
class BagInterpreterTests extends AnyFunSuite {
  test("bag") {
    assert(eval(parser.parseStr("{| 1, 2, 3 |}")) == BagV(Bags.BagImpl.fromList(List(NumV(1),NumV(2),NumV(3)))))
  }

  test("flatMap (lambda)") {
    assert(eval(desugar(parser.parseStr("sig f : int -> {| int |} let fun f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)"))) == BagV(Bags.BagImpl.fromList(List(NumV(2), NumV(3), NumV(4)))))
  }

  test("flatMap (rec)") {
    assert(eval(desugar(parser.parseStr("sig f : int -> {| int |} let rec f(x) = {|x + 1|} in flatMap({|1, 2, 3|}, f)"))) == BagV(Bags.BagImpl.fromList(List(NumV(2), NumV(3), NumV(4)))))
  }

  test("when (True)") {
    assert(eval(parser.parseStr("when(true, {| 1, 2, 3 |})")) == BagV(Bags.BagImpl.fromList(List(NumV(1), NumV(2), NumV(3)))))
  }

  test("when (False)") {
    assert(eval(parser.parseStr("when(false, {| 1, 2, 3 |})")) == BagV(Bags.BagImpl.fromList(List())))
  }

  test("count") {
    assert(eval(parser.parseStr("count({| 1, 2, 2, 3 |}, 2)")) == NumV(2))
  }

  test("sum") {
    assert(eval(parser.parseStr("sum({| 1, 2, 2, 3 |}, {| 1, 2 |})")) == BagV(Bags.BagImpl.fromList(List(NumV(1), NumV(2), NumV(2), NumV(3), NumV(1), NumV(2)))))
  }

  test("diff") {
    assert(eval(parser.parseStr("diff({| 1, 2, 2, 3|}, {| 1, 2 |})")) == BagV(Bags.BagImpl.fromList(List(NumV(2), NumV(3)))))
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