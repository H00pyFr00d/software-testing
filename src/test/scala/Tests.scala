import scala.collection.immutable.ListMap
import Console.{BLACK, GREEN, RED, RESET, UNDERLINED, YELLOW_B}
import org.scalatest.funsuite.AnyFunSuite
import FrogInterpreter.Syntax.*
import FrogInterpreter.{Interpreter, Parser, Typer, Bags}
import scala.annotation.tailrec

// ====================================== Initialising ======================================
val parser: Parser = new Parser

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
class SwapTests extends AnyFunSuite {
  var swap = Interpreter.SubstExpr.swap

  test("Value") {
    assert(swap(UnitV, "x", "y") == UnitV)
    assert(swap(NumV(1), "x", "y") == NumV(1))
    assert(swap(BoolV(true), "x", "y") == BoolV(true))
    assert(swap(StringV("hello"), "x", "y") == StringV("hello"))
    assert(swap(PairV(NumV(1), NumV(2)), "x", "y") == PairV(NumV(1), NumV(2)))
    assert(swap(RecordV(ListMap("l" -> NumV(42))), "x", "y") == RecordV(ListMap("l" -> NumV(42))))
    assert(swap(VariantV("foo", NumV(42)), "x", "y") == VariantV("foo", NumV(42)))
    assert(swap(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)), "x", "y") == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
    assert(swap(FunV("x", Var("x")), "x", "y") == FunV("x", Var("x")))
    assert(swap(RecV("f", "x", Var("x")), "x", "y") == RecV("f", "x", Var("x")))
  }

  test("Unit") {
    assert(swap(Unit, "x", "y") == Unit)
  }

  test("Int") {
    assert(swap(Num(1), "x", "y") == Num(1))
  }

  test("Plus") {
    assert(swap(Plus(Num(1), Num(2)), "x", "y") == Plus(Num(1), Num(2)))
    assert(swap(Plus(Var("x"), Num(2)), "x", "y") == Plus(Var("y"), Num(2)))
  }

  test("Minus") {
    assert(swap(Minus(Num(1), Num(2)), "x", "y") == Minus(Num(1), Num(2)))
    assert(swap(Minus(Var("x"), Num(2)), "x", "y") == Minus(Var("y"), Num(2)))
  }

  test("Times") {
    assert(swap(Times(Num(1), Num(2)), "x", "y") == Times(Num(1), Num(2)))
    assert(swap(Times(Var("x"), Num(2)), "x", "y") == Times(Var("y"), Num(2)))
  }

  test("Bool") {
    assert(swap(Bool(true), "x", "y") == Bool(true))
  }

  test("Eq") {
    assert(swap(Eq(Num(1), Num(2)), "x", "y") == Eq(Num(1), Num(2)))
    assert(swap(Eq(Var("x"), Num(2)), "x", "y") == Eq(Var("y"), Num(2)))
  }

  test("Less") {
    assert(swap(Less(Num(1), Num(2)), "x", "y") == Less(Num(1), Num(2)))
    assert(swap(Less(Var("x"), Num(2)), "x", "y") == Less(Var("y"), Num(2)))
  }

  test("IfThenElse") {
    assert(swap(IfThenElse(Bool(true), Num(1), Num(2)), "x", "y") == IfThenElse(Bool(true), Num(1), Num(2)))
    assert(swap(IfThenElse(Var("x"), Num(1), Num(2)), "x", "y") == IfThenElse(Var("y"), Num(1), Num(2)))
  }

  test("Str") {
    assert(swap(Str("hello"), "x", "y") == Str("hello"))
  }

  test("Length") {
    assert(swap(Length(Str("hello")), "x", "y") == Length(Str("hello")))
    assert(swap(Length(Var("x")), "x", "y") == Length(Var("y")))
  }

  test("Index") {
    assert(swap(Index(Str("hello"), Num(0)), "x", "y") == Index(Str("hello"), Num(0)))
    assert(swap(Index(Var("x"), Num(0)), "x", "y") == Index(Var("y"), Num(0)))
  }

  test("Concat") {
    assert(swap(Concat(Str("hello"), Str("world")), "x", "y") == Concat(Str("hello"), Str("world")))
    assert(swap(Concat(Var("x"), Str("world")), "x", "y") == Concat(Var("y"), Str("world")))
  }

  test("Let") {
    assert(swap(Let("z", Num(1), Var("z")), "x", "y") == Let("z", Num(1), Var("z")))
    assert(swap(Let("x", Num(1), Var("x")), "x", "y") == Let("y", Num(1), Var("y")))
  }

  test("Anno") {
    assert(swap(Anno(Num(1), TyInt), "x", "y") == Anno(Num(1), TyInt))
    assert(swap(Anno(Var("x"), TyInt), "x", "y") == Anno(Var("y"), TyInt))
  }

  test("Pair") {
    assert(swap(Pair(Num(1), Num(2)), "x", "y") == Pair(Num(1), Num(2)))
    assert(swap(Pair(Var("x"), Num(2)), "x", "y") == Pair(Var("y"), Num(2)))
  }

  test("First") {
    assert(swap(First(Var("z")), "x", "y") == First(Var("z")))
    assert(swap(First(Var("x")), "x", "y") == First(Var("y")))
  }

  test("Second") {
    assert(swap(Second(Var("z")), "x", "y") == Second(Var("z")))
    assert(swap(Second(Var("x")), "x", "y") == Second(Var("y")))
  }

  test("Lambda") {
    assert(swap(Lambda("z", Var("z")), "x", "y") == Lambda("z", Var("z")))
    assert(swap(Lambda("x", Var("x")), "x", "y") == Lambda("y", Var("y")))
  }

  test("Apply") {
    assert(swap(Apply(Var("f"), Var("z")), "x", "y") == Apply(Var("f"), Var("z")))
    assert(swap(Apply(Var("f"), Var("x")), "x", "y") == Apply(Var("f"), Var("y")))
  }

  test("Rec") {
    assert(swap(Rec("f", "z", Var("z")), "x", "y") == Rec("f", "z", Var("z")))
    assert(swap(Rec("f", "x", Var("x")), "x", "y") == Rec("f", "y", Var("y")))
  }

  test("Record") {
    assert(swap(Record(ListMap("l" -> Num(42))), "x", "y") == Record(ListMap("l" -> Num(42))))
    assert(swap(Record(ListMap("l" -> Var("x"))), "x", "y") == Record(ListMap("l" -> Var("y"))))
  }

  test("Proj") {
    assert(swap(Proj(Var("r"), "foo"), "x", "y") == Proj(Var("r"), "foo"))
  }

  test("Variant") {
    assert(swap(Variant("foo", Num(42)), "x", "y") == Variant("foo", Num(42)))
    assert(swap(Variant("foo", Var("x")), "x", "y") == Variant("foo", Var("y")))
  }

  test("Case") {
    assert(swap(Case(Var("v"), ListMap("z" -> ("z", NumV(1)))), "x", "y") == Case(Var("v"), ListMap("z" -> ("z", NumV(1)))))
    assert(swap(Case(Var("v"), ListMap("x" -> ("x", NumV(1)))), "x", "y") == Case(Var("v"), ListMap("x" -> ("y", NumV(1)))))
  }

  test("Bag") {
    assert(swap(Bag(List(NumV(1), NumV(2), NumV(3))), "x", "y") == Bag(List(NumV(1), NumV(2), NumV(3))))
  }

  test("FlatMap") {
    assert(swap(FlatMap(Var("b"), Lambda("z", Var("z"))), "x", "y") == FlatMap(Var("b"), Lambda("z", Var("z"))))
    assert(swap(FlatMap(Var("b"), Lambda("x", Var("x"))), "x", "y") == FlatMap(Var("b"), Lambda("y", Var("y"))))
    assert(swap(FlatMap(Var("x"), Lambda("z", Var("z"))), "x", "y") == FlatMap(Var("y"), Lambda("z", Var("z"))))
  }

  test("When") {
    assert(swap(When(Var("b"), Lambda("z", Var("z"))), "x", "y") == When(Var("b"), Lambda("z", Var("z"))))
    assert(swap(When(Var("b"), Lambda("x", Var("x"))), "x", "y") == When(Var("b"), Lambda("y", Var("y"))))
    assert(swap(When(Var("x"), Lambda("z", Var("z"))), "x", "y") == When(Var("y"), Lambda("z", Var("z"))))
  }

  test("Sum") {
    assert(swap(Sum(Var("b1"), Var("b2")), "x", "y") == Sum(Var("b1"), Var("b2")))
    assert(swap(Sum(Var("x"), Var("b2")), "x", "y") == Sum(Var("y"), Var("b2")))
  }

  test("Diff") {
    assert(swap(Diff(Var("b1"), Var("b2")), "x", "y") == Diff(Var("b1"), Var("b2")))
    assert(swap(Diff(Var("x"), Var("b2")), "x", "y") == Diff(Var("y"), Var("b2")))
  }

  test("Empty Comprehension") {
    assert(swap(Comprehension(Var("z"), List()), "x", "y") == Comprehension(Var("z"), List()))
    assert(swap(Comprehension(Var("x"), List()), "x", "y") == Comprehension(Var("y"), List()))
  }

  test("Comprehension w/ Bind") {
    assert(swap(Comprehension(Var("b"), List(Bind("z", Var("l")))), "x", "y") == Comprehension(Var("b"), List(Bind("z", Var("l")))))
    assert(swap(Comprehension(Var("b"), List(Bind("x", Var("l")))), "x", "y") == Comprehension(Var("b"), List(Bind("y", Var("l")))))
  }

  test("Comprehension w/ Guard") {
    assert(swap(Comprehension(Var("b"), List(Guard(Var("z")))), "x", "y") == Comprehension(Var("b"), List(Guard(Var("z")))))
    assert(swap(Comprehension(Var("b"), List(Guard(Var("x")))), "x", "y") == Comprehension(Var("b"), List(Guard(Var("y")))))
  }

  test("Comprehension w/ CLet") {
    assert(swap(Comprehension(Var("b"), List(CLet("z", Var("l")))), "x", "y") == Comprehension(Var("b"), List(CLet("z", Var("l")))))
    assert(swap(Comprehension(Var("b"), List(CLet("x", Var("l")))), "x", "y") == Comprehension(Var("b"), List(CLet("y", Var("l")))))
  }

  test("Count") {
    assert(swap(Count(Var("b"), Num(2)), "x", "y") == Count(Var("b"), Num(2)))
    assert(swap(Count(Var("x"), Num(2)), "x", "y") == Count(Var("y"), Num(2)))
  }

  test("LetPair") {
    assert(swap(LetPair("z", "w", Var("p"), Var("p")), "x", "y") == LetPair("z", "w", Var("p"), Var("p")))
    assert(swap(LetPair("x", "w", Var("p"), Var("p")), "x", "y") == LetPair("y", "w", Var("p"), Var("p")))
    assert(swap(LetPair("z", "x", Var("p"), Var("p")), "x", "y") == LetPair("z", "y", Var("p"), Var("p")))
  }

  test("LetFun") {
    assert(swap(LetFun("f", TyInt, "z", Var("f"), Var("f")), "x", "y") == LetFun("f", TyInt, "z", Var("f"), Var("f")))
    assert(swap(LetFun("f", TyInt, "x", Var("f"), Var("f")), "x", "y") == LetFun("f", TyInt, "y", Var("f"), Var("f")))
    assert(swap(LetFun("f", TyInt, "z", Var("x"), Var("f")), "x", "y") == LetFun("f", TyInt, "z", Var("y"), Var("f")))
  }

  test("LetRec") {
    assert(swap(LetRec("f", TyInt, "z", Var("f"), Var("f")), "x", "y") == LetRec("f", TyInt, "z", Var("f"), Var("f")))
    assert(swap(LetRec("f", TyInt, "x", Var("f"), Var("f")), "x", "y") == LetRec("f", TyInt, "y", Var("f"), Var("f")))
    assert(swap(LetRec("f", TyInt, "z", Var("x"), Var("f")), "x", "y") == LetRec("f", TyInt, "z", Var("y"), Var("f")))
  }

  test("LetRecord") {
    assert(swap(LetRecord(ListMap("l" -> "z"), Var("r"), Var("r")), "x", "y") == LetRecord(ListMap("l" -> "z"), Var("r"), Var("r")))
    assert(swap(LetRecord(ListMap("l" -> "x"), Var("r"), Var("r")), "x", "y") == LetRecord(ListMap("l" -> "y"), Var("r"), Var("r")))
    assert(swap(LetRecord(ListMap("l" -> "z"), Var("x"), Var("r")), "x", "y") == LetRecord(ListMap("l" -> "z"), Var("y"), Var("r")))
  }
}

class SubstTests extends AnyFunSuite {
  test("Value") {
    assert(subst(UnitV, Unit, "x") == UnitV)
    assert(subst(NumV(1), Unit, "x") == NumV(1))
    assert(subst(BoolV(true), Unit, "x") == BoolV(true))
    assert(subst(StringV("hello"), Unit, "x") == StringV("hello"))
    assert(subst(PairV(NumV(1), NumV(2)), Unit, "x") == PairV(NumV(1), NumV(2)))
    assert(subst(RecordV(ListMap("l" -> NumV(42))), Unit, "x") == RecordV(ListMap("l" -> NumV(42))))
    assert(subst(VariantV("foo", NumV(42)), Unit, "x") == VariantV("foo", NumV(42)))
    assert(subst(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)), Unit, "x") == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
    assert(subst(FunV("x", Var("x")), Unit, "x") == FunV("x", Var("x")))
    assert(subst(RecV("f", "x", Var("x")), Unit, "x") == RecV("f", "x", Var("x")))
  }

  test("Unit") {
    assert(subst(Unit, Unit, "x") == Unit)
  }

  test("Int") {
    assert(subst(Num(1), Unit, "x") == Num(1))
  }

  test("Plus") {
    assert(subst(Plus(Num(1), Num(2)), Unit, "x") == Plus(Num(1), Num(2)))
    assert(subst(Plus(Var("x"), Num(2)), Num(1), "x") == Plus(Num(1), Num(2)))
  }

  test("Minus") {
    assert(subst(Minus(Num(1), Num(2)), Unit, "x") == Minus(Num(1), Num(2)))
    assert(subst(Minus(Var("x"), Num(2)), Num(1), "x") == Minus(Num(1), Num(2)))
  }

  test("Times") {
    assert(subst(Times(Num(1), Num(2)), Unit, "x") == Times(Num(1), Num(2)))
    assert(subst(Times(Var("x"), Num(2)), Num(1), "x") == Times(Num(1), Num(2)))
  }

  test("Bool") {
    assert(subst(Bool(true), Unit, "x") == Bool(true))
  }

  test("Eq") {
    assert(subst(Eq(Num(1), Num(2)), Unit, "x") == Eq(Num(1), Num(2)))
    assert(subst(Eq(Var("x"), Num(2)), Num(1), "x") == Eq(Num(1), Num(2)))
  }

  test("Less") {
    assert(subst(Less(Num(1), Num(2)), Unit, "x") == Less(Num(1), Num(2)))
    assert(subst(Less(Var("x"), Num(2)), Num(1), "x") == Less(Num(1), Num(2)))
  }

  test("IfThenElse") {
    assert(subst(IfThenElse(Bool(true), Num(1), Num(2)), Unit, "x") == IfThenElse(Bool(true), Num(1), Num(2)))
    assert(subst(IfThenElse(Var("x"), Num(1), Num(2)), Num(1), "x") == IfThenElse(Num(1), Num(1), Num(2)))
  }

  test("Str") {
    assert(subst(Str("hello"), Unit, "x") == Str("hello"))
  }

  test("Length") {
    assert(subst(Length(Str("hello")), Unit, "x") == Length(Str("hello")))
    assert(subst(Length(Var("x")), Num(1), "x") == Length(Num(1)))
  }

  test("Index") {
    assert(subst(Index(Str("hello"), Num(0)), Unit, "x") == Index(Str("hello"), Num(0)))
    assert(subst(Index(Var("x"), Num(0)), Num(1), "x") == Index(Num(1), Num(0)))
  }

  test("Concat") {
    assert(subst(Concat(Str("hello"), Str("world")), Unit, "x") == Concat(Str("hello"), Str("world")))
    assert(subst(Concat(Var("x"), Str("world")), Str("hello"), "x") == Concat(Str("hello"), Str("world")))
  }

  test("Var") {
    assert(subst(Var("x"), Num(1), "x") == Num(1))
    assert(subst(Var("y"), Num(1), "x") == Var("y"))
  }

  test("Let") {
    Interpreter.generator.reset()
    assert(subst(Let("z", Num(1), Var("z")), Unit, "x") == Let("z_0", Num(1), Var("z_0")))
  }

  test("Anno") {
    assert(subst(Anno(Num(1), TyInt), Unit, "x") == Anno(Num(1), TyInt))
    assert(subst(Anno(Var("x"), TyInt), Num(1), "x") == Anno(Num(1), TyInt))
  }

  test("Lambda") {
    Interpreter.generator.reset()
    assert(subst(Lambda("z", Var("z")), Unit, "x") == Lambda("z_0", Var("z_0")))
  }

  test("Apply") {
    assert(subst(Apply(Var("f"), Var("z")), Unit, "x") == Apply(Var("f"), Var("z")))
    assert(subst(Apply(Var("f"), Var("x")), Num(1), "x") == Apply(Var("f"), Num(1)))
    assert(subst(Apply(Var("f"), Var("x")), Var("g"), "f") == Apply(Var("g"), Var("x")))
  }

  test("Rec") {
    Interpreter.generator.reset()
    assert(subst(Rec("f", "z", Var("z")), Unit, "x") == Rec("f_0", "z_1", Var("z_1")))
  }

  test("Pair") {
    assert(subst(Pair(Num(1), Num(2)), Unit, "x") == Pair(Num(1), Num(2)))
    assert(subst(Pair(Var("x"), Num(2)), Num(1), "x") == Pair(Num(1), Num(2)))
  }

  test("First") {
    assert(subst(First(Var("z")), Unit, "x") == First(Var("z")))
    assert(subst(First(Var("x")), Num(1), "x") == First(Num(1)))
  }

  test("Second") {
    assert(subst(Second(Var("z")), Unit, "x") == Second(Var("z")))
    assert(subst(Second(Var("x")), Num(1), "x") == Second(Num(1)))
  }

  test("Record") {
    assert(subst(Record(ListMap("l" -> Num(42))), Unit, "x") == Record(ListMap("l" -> Num(42))))
    assert(subst(Record(ListMap("l" -> Var("x"))), Num(1), "x") == Record(ListMap("l" -> Num(1))))
  }

  test("Proj") {
    assert(subst(Proj(Var("r"), "foo"), Unit, "x") == Proj(Var("r"), "foo"))
  }

  test("Variant") {
    assert(subst(Variant("foo", Num(42)), Unit, "x") == Variant("foo", Num(42)))
    assert(subst(Variant("foo", Var("x")), Num(1), "x") == Variant("foo", Num(1)))
  }

  test("Case") {
    Interpreter.generator.reset()
    assert(subst(Case(Var("v"), ListMap("z" -> ("z", NumV(1)))), Unit, "x") == Case(Var("v"), ListMap("z" -> ("z_0", NumV(1)))))
  }

  test("Bag") {
    assert(subst(Bag(List(Num(1), Num(2), Num(3))), Unit, "x") == Bag(List(Num(1), Num(2), Num(3))))
    assert(subst(Bag(List(Var("x"), Num(2), Num(3))), Num(1), "x") == Bag(List(Num(1), Num(2), Num(3))))
  }

  test("FlatMap") {
    Interpreter.generator.reset()
    assert(subst(FlatMap(Var("b"), Lambda("z", Var("z"))), Unit, "x") == FlatMap(Var("b"), Lambda("z_0", Var("z_0"))))
  }

  test("When") {
    Interpreter.generator.reset()
    assert(subst(When(Var("b"), Lambda("z", Var("z"))), Unit, "x") == When(Var("b"), Lambda("z_0", Var("z_0"))))
  }

  test("Sum") {
    assert(subst(Sum(Var("b1"), Var("b2")), Unit, "x") == Sum(Var("b1"), Var("b2")))
    assert(subst(Sum(Var("x"), Var("b2")), Num(1), "x") == Sum(Num(1), Var("b2")))
  }

  test("Diff") {
    assert(subst(Diff(Var("b1"), Var("b2")), Unit, "x") == Diff(Var("b1"), Var("b2")))
    assert(subst(Diff(Var("x"), Var("b2")), Num(1), "x") == Diff(Num(1), Var("b2")))
  }

  test("Empty Comprehension") {
    assert(subst(Comprehension(Var("z"), List()), Unit, "x") == Comprehension(Var("z"), List()))
    assert(subst(Comprehension(Var("x"), List()), Num(1), "x") == Comprehension(Num(1), List()))
  }

  test("Comprehension w/ Bind") {
    Interpreter.generator.reset()
    assert(subst(Comprehension(Var("b"), List(Bind("z", Var("l")))), Unit, "x") == Comprehension(Var("b"), List(Bind("z_0", Var("l")))))
  }

  test("Comprehension w/ Guard") {
    assert(subst(Comprehension(Var("b"), List(Guard(Var("z")))), Unit, "x") == Comprehension(Var("b"), List(Guard(Var("z")))))
    assert(subst(Comprehension(Var("b"), List(Guard(Var("x")))), Num(1), "x") == Comprehension(Var("b"), List(Guard(Num(1)))))
  }

  test("Comprehension w/ CLet") {
    Interpreter.generator.reset()
    assert(subst(Comprehension(Var("b"), List(CLet("z", Var("l")))), Unit, "x") == Comprehension(Var("b"), List(CLet("z_0", Var("l")))))
  }

  test("Full Comprehension") {
    Interpreter.generator.reset()
    assert(subst(Comprehension(Var("b"), List(Bind("z", Var("l")), CLet("c", Num(1)), Guard(Less(Var("z"), Num(10))))), Unit, "x") == Comprehension(Var("b"), List(Bind("z_0", Var("l")), CLet("c_1", Num(1)), Guard(Less(Var("z_0"), Num(10))))))
  }

  test("Bind w/o Comprehension") {
    assertThrows[Exception] {
      subst(Bind("x", Num(1)), Unit, "x")
    }
  }

  test("Guard w/o Comprehension") {
    assertThrows[Exception] {
      subst(Guard(Num(1)), Unit, "x")
    }
  }

  test("CLet w/o Comprehension") {
    assertThrows[Exception] {
      subst(CLet("x", Num(1)), Unit, "x")
    }
  }

  test("Unexpected Pattern in Comprehension") {
    assertThrows[Exception] {
      subst(Comprehension(Var("b"), List(Num(1))), Unit, "x")
    }
  }

  test("Count") {
    assert(subst(Count(Var("b"), Num(2)), Unit, "x") == Count(Var("b"), Num(2)))
    assert(subst(Count(Var("x"), Num(2)), Num(1), "x") == Count(Num(1), Num(2)))
  }

  test("LetPair") {
    Interpreter.generator.reset()
    assert(subst(LetPair("z", "w", Num(1), Num(2)), Unit, "x") == LetPair("z_0", "w_1", Num(1), Num(2)))
  }

  test("LetFun") {
    Interpreter.generator.reset()
    assert(subst(LetFun("f", TyInt, "z", Var("g"), Num(1)), Unit, "x") == LetFun("f_0", TyInt, "z_1", Var("g"), Num(1)))
  }

  test("LetRec") {
    Interpreter.generator.reset()
    assert(subst(LetRec("f", TyInt, "z", Var("g"), Num(1)), Unit, "x") == LetRec("f_0", TyInt, "z_1", Var("g"), Num(1)))
  }

  test("LetRecord") {
    Interpreter.generator.reset()
    assert(subst(LetRecord(ListMap("l" -> "z"), Var("r"), Unit), Unit, "x") == LetRecord(ListMap("l" -> "z_0"), Var("r"), Unit))
  }
}

class DesugarTests extends AnyFunSuite {
  test("Value") {
    assertThrows[Exception] {desugar(UnitV)}
    assertThrows[Exception] {desugar(NumV(1))}
    assertThrows[Exception] {desugar(BoolV(true))}
    assertThrows[Exception] {desugar(StringV("hello"))}
    assertThrows[Exception] {desugar(PairV(NumV(1), NumV(2)))}
    assertThrows[Exception] {desugar(RecordV(ListMap("l" -> NumV(42))))}
    assertThrows[Exception] {desugar(VariantV("foo", NumV(42)))}
    assertThrows[Exception] {desugar(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))}
    assertThrows[Exception] {desugar(FunV("x", Var("x")))}
    assertThrows[Exception] {desugar(RecV("f", "x", Var("x")))}
  }

  test("Unit") {
    assert(desugar(Unit) == Unit)
  }

  test("Int") {
    assert(desugar(Num(1)) == Num(1))
  }

  test("Plus") {
    assert(desugar(Plus(Num(1), Num(2))) == Plus(Num(1), Num(2)))
  }

  test("Minus") {
    assert(desugar(Minus(Num(1), Num(2))) == Minus(Num(1), Num(2)))
  }

  test("Times") {
    assert(desugar(Times(Num(1), Num(2))) == Times(Num(1), Num(2)))
  }

  test("Bool") {
    assert(desugar(Bool(true)) == Bool(true))
  }

  test("Eq") {
    assert(desugar(Eq(Num(1), Num(2))) == Eq(Num(1), Num(2)))
  }

  test("Less") {
    assert(desugar(Less(Num(1), Num(2))) == Less(Num(1), Num(2)))
  }

  test("IfThenElse") {
    assert(desugar(IfThenElse(Bool(true), Num(1), Num(2))) == IfThenElse(Bool(true), Num(1), Num(2)))
  }

  test("Str") {
    assert(desugar(Str("hello")) == Str("hello"))
  }

  test("Length") {
    assert(desugar(Length(Str("hello"))) == Length(Str("hello")))
  }

  test("Index") {
    assert(desugar(Index(Str("hello"), Num(0))) == Index(Str("hello"), Num(0)))
  }

  test("Concat") {
    assert(desugar(Concat(Str("hello"), Str("world"))) == Concat(Str("hello"), Str("world")))
  }

  test("Var") {
    assert(desugar(Var("x")) == Var("x"))
  }

  test("Let") {
    assert(desugar(Let("x", Num(1), Var("x"))) == Let("x", Num(1), Var("x")))
  }

  test("Anno") {
    assert(desugar(Anno(Num(1), TyInt)) == Num(1))
  }

  test("Lambda") {
    assert(desugar(Lambda("x", Var("x"))) == Lambda("x", Var("x")))
  }

  test("Apply") {
    assert(desugar(Apply(Var("f"), Var("x"))) == Apply(Var("f"), Var("x")))
  }

  test("Rec") {
    assert(desugar(Rec("f", "x", Var("x"))) == Rec("f", "x", Var("x")))
  }

  test("Pair") {
    assert(desugar(Pair(Num(1), Num(2))) == Pair(Num(1), Num(2)))
  }

  test("First") {
    assert(desugar(First(Var("x"))) == First(Var("x")))
  }

  test("Second") {
    assert(desugar(Second(Var("x"))) == Second(Var("x")))
  }

  test("Record") {
    assert(desugar(Record(ListMap("l" -> Num(42)))) == Record(ListMap("l" -> Num(42))))
  }

  test("Proj") {
    assert(desugar(Proj(Var("r"), "foo")) == Proj(Var("r"), "foo"))
  }

  test("Variant") {
    assert(desugar(Variant("foo", Num(42))) == Variant("foo", Num(42)))
  }

  test("Case") {
    assert(desugar(Case(Var("v"), ListMap("z" -> ("z", Var("z_prime"))))) == Case(Var("v"), ListMap("z" -> ("z", Var("z_prime")))))
  }

  test("Bag") {
    assert(desugar(Bag(List(Num(1), Num(2), Num(3)))) == Bag(List(Num(1), Num(2), Num(3))))
  }

  test("FlatMap") {
    assert(desugar(FlatMap(Var("b"), Lambda("z", Var("z")))) == FlatMap(Var("b"), Lambda("z", Var("z"))))
  }

  test("When") {
    assert(desugar(When(Var("b"), Lambda("z", Var("z")))) == When(Var("b"), Lambda("z", Var("z"))))
  }

  test("Sum") {
    assert(desugar(Sum(Var("b1"), Var("b2"))) == Sum(Var("b1"), Var("b2")))
  }

  test("Diff") {
    assert(desugar(Diff(Var("b1"), Var("b2"))) == Diff(Var("b1"), Var("b2")))
  }

  test("Count") {
    assert(desugar(Count(Var("b"), Num(2))) == Count(Var("b"), Num(2)))
  }

  test("Empty Comprehension") {
    assert(desugar(Comprehension(Var("z"), List())) == Bag(List(Var("z"))))
  }

  test("Comprehension w/ Bind") {
    assert(desugar(Comprehension(Var("b"), List(Bind("z", Var("l"))))) == FlatMap(Var("l"), Lambda("z", Bag(List(Var("b"))))))
  }

  test("Comprehension w/ Guard") {
    assert(desugar(Comprehension(Var("b"), List(Guard(Var("z"))))) == When(Var("z"), Bag(List(Var("b")))))
  }

  test("Comprehension w/ CLet") {
    assert(desugar(Comprehension(Var("b"), List(CLet("z", Var("l"))))) == Let("z", Var("l"), Bag(List(Var("b")))))
  }

  test("Unexpected Pattern in Comprehension") {
    assertThrows[Exception] {
      desugar(Comprehension(Var("b"), List(Num(1))))
    }
  }

  test("LetPair") {
    Interpreter.generator.reset()
    assert(desugar(LetPair("z", "w", Pair(Num(1), Num(2)), Var("z"))) == Let("$0", Pair(Num(1), Num(2)), First(Var("$0"))))
  }

  test("LetFun") {
    assert(desugar(LetFun("f", TyInt, "z", Var("f"), Var("f"))) == Let("f", Lambda("z", Var("f")), Var("f")))
  }

  test("LetRec") {
    assert(desugar(LetRec("f", TyInt, "z", Var("f"), Var("f"))) == Let("f", Rec("f", "z", Var("f")), Var("f")))
  }

  test("LetRecord") {
    Interpreter.generator.reset()
    assert(desugar(LetRecord(ListMap("l" -> "z"), Var("r"), Var("r"))) == Let("$0", Var("r"), Var("r")))
  }

  test("Bind w/o Comprehension") {
    assertThrows[Exception] {
      desugar(Bind("x", Num(1)))
    }
  }

  test("Guard w/o Comprehension") {
    assertThrows[Exception] {
      desugar(Guard(Num(1)))
    }
  }

  test("CLet w/o Comprehension") {
    assertThrows[Exception] {
      desugar(CLet("x", Num(1)))
    }
  }
}

class InterpreterValueTests extends AnyFunSuite {
  test("add") {
    assert(Interpreter.Value.add(NumV(1), NumV(2)) == NumV(3))
  }

  test("add with non-NumV") {
    assertThrows[Exception] {
      Interpreter.Value.add(NumV(1), BoolV(true))
    }
  }

  test("sub") {
    assert(Interpreter.Value.subtract(NumV(1), NumV(2)) == NumV(-1))
  }

  test("sub with non-NumV") {
    assertThrows[Exception] {
      Interpreter.Value.subtract(NumV(1), BoolV(true))
    }
  }

  test("mul") {
    assert(Interpreter.Value.multiply(NumV(2), NumV(3)) == NumV(6))
  }

  test("mul with non-NumV") {
    assertThrows[Exception] {
      Interpreter.Value.multiply(NumV(1), BoolV(true))
    }
  }

  test("eq") {
    assert(Interpreter.Value.eq(NumV(1), NumV(1)) == BoolV(true))
    assert(Interpreter.Value.eq(NumV(1), NumV(2)) == BoolV(false))
    assert(Interpreter.Value.eq(BoolV(true), BoolV(true)) == BoolV(true))
    assert(Interpreter.Value.eq(BoolV(true), BoolV(false)) == BoolV(false))
    assert(Interpreter.Value.eq(BoolV(false), BoolV(true)) == BoolV(false))
    assert(Interpreter.Value.eq(BoolV(false), BoolV(false)) == BoolV(true))
    assert(Interpreter.Value.eq(StringV("hello"), StringV("hello")) == BoolV(true))
    assert(Interpreter.Value.eq(StringV("hello"), StringV("world")) == BoolV(false))
    assert(Interpreter.Value.eq(PairV(NumV(1), NumV(2)), PairV(NumV(1), NumV(2))) == BoolV(true))
    assert(Interpreter.Value.eq(PairV(NumV(1), NumV(2)), PairV(NumV(2), NumV(1))) == BoolV(false))
    assert(Interpreter.Value.eq(VariantV("foo", NumV(42)), VariantV("foo", NumV(42))) == BoolV(true))
    assert(Interpreter.Value.eq(VariantV("foo", NumV(42)), VariantV("bar", NumV(42))) == BoolV(false))
  }

  test("eq (incomparable)") {
    assertThrows[Exception] {
      Interpreter.Value.eq(NumV(1), BoolV(true))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(BoolV(true), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(NumV(1), StringV("hello"))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(StringV("hello"), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(NumV(1), PairV(NumV(1), NumV(2)))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(PairV(NumV(1), NumV(2)), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(NumV(1), VariantV("foo", NumV(42)))
    }

    assertThrows[Exception] {
      Interpreter.Value.eq(VariantV("foo", NumV(42)), NumV(1))
    }
  }

  test("less") {
    assert(Interpreter.Value.less(NumV(1), NumV(2)) == BoolV(true))
    assert(Interpreter.Value.less(NumV(2), NumV(1)) == BoolV(false))
  }

  test("less (incomparable)") {
    assertThrows[Exception] {
      Interpreter.Value.less(NumV(1), BoolV(true))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(BoolV(true), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(NumV(1), StringV("hello"))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(StringV("hello"), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(NumV(1), PairV(NumV(1), NumV(2)))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(PairV(NumV(1), NumV(2)), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(NumV(1), VariantV("foo", NumV(42)))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(VariantV("foo", NumV(42)), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(NumV(1), BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)), NumV(1))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(NumV(1), FunV("x", Var("x")))
    }

    assertThrows[Exception] {
      Interpreter.Value.less(FunV("x", Var("x")), NumV(1))
    }
  }

  test("length") {
    assert(Interpreter.Value.length(StringV("hello")) == NumV(5))
  }

  test("length (non-StringV)") {
    assertThrows[Exception] {
      Interpreter.Value.length(NumV(1))
      Interpreter.Value.length(BoolV(true))
      Interpreter.Value.length(PairV(NumV(1), NumV(2)))
      Interpreter.Value.length(RecordV(ListMap("l" -> NumV(42))))
      Interpreter.Value.length(VariantV("foo", NumV(42)))
      Interpreter.Value.length(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
      Interpreter.Value.length(FunV("x", Var("x")))
    }
  }

  test("index") {
    assert(Interpreter.Value.index(StringV("hello"), NumV(0)) == StringV("h"))
    assert(Interpreter.Value.index(StringV("hello"), NumV(1)) == StringV("e"))
    assert(Interpreter.Value.index(StringV("hello"), NumV(2)) == StringV("l"))
    assert(Interpreter.Value.index(StringV("hello"), NumV(3)) == StringV("l"))
    assert(Interpreter.Value.index(StringV("hello"), NumV(4)) == StringV("o"))
  }

  test("index (non-StringV)") {
    assertThrows[Exception] {
      Interpreter.Value.index(NumV(1), NumV(0))
      Interpreter.Value.index(BoolV(true), NumV(0))
      Interpreter.Value.index(PairV(NumV(1), NumV(2)), NumV(0))
      Interpreter.Value.index(RecordV(ListMap("l" -> NumV(42))), NumV(0))
      Interpreter.Value.index(VariantV("foo", NumV(42)), NumV(0))
      Interpreter.Value.index(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)), NumV(0))
      Interpreter.Value.index(FunV("x", Var("x")), NumV(0))
    }
  }

  test("concat") {
    assert(Interpreter.Value.concat(StringV("hello"), StringV("world")) == StringV("helloworld"))
  }

  test("concat (non-StringV)") {
    assertThrows[Exception] {
      Interpreter.Value.concat(StringV("hello"), NumV(1))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(NumV(1), StringV("hello"))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(NumV(1), NumV(1))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(BoolV(true), StringV("hello"))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(StringV("hello"), BoolV(true))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(PairV(NumV(1), NumV(2)), StringV("hello"))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(StringV("hello"), PairV(NumV(1), NumV(2)))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(RecordV(ListMap("l" -> NumV(42))), StringV("hello"))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(StringV("hello"), RecordV(ListMap("l" -> NumV(42))))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(VariantV("foo", NumV(42)), StringV("hello"))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(StringV("hello"), VariantV("foo", NumV(42)))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)), StringV("hello"))
    }
    assertThrows[Exception] {
      Interpreter.Value.concat(StringV("hello"), BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
    }
  }
}

class InterpreterEval extends AnyFunSuite {
  test("Value") {
    assert(Interpreter.eval(UnitV) == UnitV)
    assert(Interpreter.eval(NumV(1)) == NumV(1))
    assert(Interpreter.eval(BoolV(true)) == BoolV(true))
    assert(Interpreter.eval(StringV("hello")) == StringV("hello"))
    assert(Interpreter.eval(PairV(NumV(1), NumV(2))) == PairV(NumV(1), NumV(2)))
    assert(Interpreter.eval(RecordV(ListMap("l" -> NumV(42)))) == RecordV(ListMap("l" -> NumV(42))))
    assert(Interpreter.eval(VariantV("foo", NumV(42))) == VariantV("foo", NumV(42)))
    assert(Interpreter.eval(BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1))) == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
    assert(Interpreter.eval(FunV("x", Var("x"))) == FunV("x", Var("x")))
    assert(Interpreter.eval(RecV("f", "x", Var("x"))) == RecV("f", "x", Var("x")))
  }

  test("Unit") {
    assert(Interpreter.eval(Unit) == UnitV)
  }

  test("Int") {
    assert(Interpreter.eval(Num(1)) == NumV(1))
  }

  test("Plus") {
    assert(Interpreter.eval(Plus(Num(1), Num(2))) == NumV(3))
  }

  test("Minus") {
    assert(Interpreter.eval(Minus(Num(1), Num(2))) == NumV(-1))
  }

  test("Times") {
    assert(Interpreter.eval(Times(Num(2), Num(3))) == NumV(6))
  }

  test("Bool") {
    assert(Interpreter.eval(Bool(true)) == BoolV(true))
  }

  test("Eq") { 
    assert(Interpreter.eval(Eq(Num(1), Num(1))) == BoolV(true))
    assert(Interpreter.eval(Eq(Num(1), Num(2))) == BoolV(false))
    assert(Interpreter.eval(Eq(Bool(true), Bool(true))) == BoolV(true))
    assert(Interpreter.eval(Eq(Bool(true), Bool(false))) == BoolV(false))
    assert(Interpreter.eval(Eq(Bool(false), Bool(true))) == BoolV(false))
    assert(Interpreter.eval(Eq(Bool(false), Bool(false))) == BoolV(true))
    assert(Interpreter.eval(Eq(Str("hello"), Str("hello"))) == BoolV(true))
    assert(Interpreter.eval(Eq(Str("hello"), Str("world"))) == BoolV(false))
    assert(Interpreter.eval(Eq(Pair(Num(1), Num(2)), Pair(Num(1), Num(2)))) == BoolV(true))
    assert(Interpreter.eval(Eq(Pair(Num(1), Num(2)), Pair(Num(2), Num(1)))) == BoolV(false))
    assert(Interpreter.eval(Eq(Variant("foo", Num(42)), Variant("foo", Num(42)))) == BoolV(true))
    assert(Interpreter.eval(Eq(Variant("foo", Num(42)), Variant("bar", Num(42)))) == BoolV(false))
  }

  test("Less") {
    assert(Interpreter.eval(Less(Num(1), Num(2))) == BoolV(true))
    assert(Interpreter.eval(Less(Num(2), Num(1))) == BoolV(false))
  }

  test("IfThenElse") {
    assert(Interpreter.eval(IfThenElse(Bool(true), Num(1), Num(2))) == NumV(1))
    assert(Interpreter.eval(IfThenElse(Bool(false), Num(1), Num(2))) == NumV(2))
  }

  test("Str") {
    assert(Interpreter.eval(Str("hello")) == StringV("hello"))
  }

  test("Length") {
    assert(Interpreter.eval(Length(Str("hello"))) == NumV(5))
  }

  test("Index") {
    assert(Interpreter.eval(Index(Str("hello"), Num(0))) == StringV("h"))
    assert(Interpreter.eval(Index(Str("hello"), Num(1))) == StringV("e"))
    assert(Interpreter.eval(Index(Str("hello"), Num(2))) == StringV("l"))
    assert(Interpreter.eval(Index(Str("hello"), Num(3))) == StringV("l"))
    assert(Interpreter.eval(Index(Str("hello"), Num(4))) == StringV("o"))
  }

  test("Concat") {
    assert(Interpreter.eval(Concat(Str("hello"), Str("world"))) == StringV("helloworld"))
  }

  test("Var") {
    assertThrows[Exception] {
      Interpreter.eval(Var("x"))
    }
  }

  test("Let") {
    assert(Interpreter.eval(Let("x", Num(1), Var("x"))) == NumV(1))
  }

  test("Anno") {
    assertThrows[Exception] {
      Interpreter.eval(Anno(Num(1), TyInt))
    }
  }

  test("Lambda") {
    assert(Interpreter.eval(Lambda("x", Var("x"))) == FunV("x", Var("x")))
  }

  test("Apply") {
    assert(Interpreter.eval(Apply(Lambda("x", Var("x")), Num(1))) == NumV(1))
  }

  test("Rec") {
    assert(Interpreter.eval(Rec("f", "x", Var("x"))) == RecV("f", "x", Var("x")))
  }

  test("Pair") {
    assert(Interpreter.eval(Pair(Num(1), Num(2))) == PairV(NumV(1), NumV(2)))
  }

  test("First") {
    assert(Interpreter.eval(First(Pair(Num(1), Num(2)))) == NumV(1))
  }

  test("Second") {
    assert(Interpreter.eval(Second(Pair(Num(1), Num(2)))) == NumV(2))
  }

  test("Record") {
    assert(Interpreter.eval(Record(ListMap("l" -> Num(42)))) == RecordV(ListMap("l" -> NumV(42))))
  }

  test("Proj") {
    assert(Interpreter.eval(Proj(Record(ListMap("l" -> Num(42))), "l")) == NumV(42))
  }

  test("Proj (label not found)") {
    assertThrows[Exception] {
      Interpreter.eval(Proj(Record(ListMap("l" -> Num(42))), "foo"))
    }
  }

  test("Variant") {
    assert(Interpreter.eval(Variant("foo", Num(42))) == VariantV("foo", NumV(42)))
  }

  test("Case") {
    assert(Interpreter.eval(Case(Variant("foo", Num(42)), ListMap("foo" -> ("x", Var("x"))))) == NumV(42))
  }

  test("Case (label not found)") {
    assertThrows[Exception] {
      Interpreter.eval(Case(Variant("foo", Num(42)), ListMap("bar" -> ("x", Var("x")))))
    }
  }

  test("Bag") {
    assert(Interpreter.eval(Bag(List(Num(1), Num(2), Num(3)))) == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
  }

  test("FlatMap") {
    assert(Interpreter.eval(FlatMap(Bag(List(Num(1), Num(2), Num(3))), Lambda("x", Bag(List(Var("x")))))) == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
  }

  test("FlatMap (expects function with bag-type return)") {
    assertThrows[Exception] {
      Interpreter.eval(FlatMap(Bag(List(Num(1), Num(2), Num(3))), Lambda("x", Var("x"))))
    }
  }

  test("FlatMap (expects bag and function)") {
    assertThrows[Exception] {
      Interpreter.eval(FlatMap(Num(1), Lambda("x", Bag(List(Var("x"))))))
    }
  }

  test("When") {
    assert(Interpreter.eval(When(Bool(true), Bag(List(Num(1), Num(2), Num(3))))) == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
  }

  test("When (expects boolean and bag)") {
    assertThrows[Exception] {
      Interpreter.eval(When(Num(1), Num(1)))
    }
  }

  test("Sum") {
    assert(Interpreter.eval(Sum(Bag(List(Num(1), Num(2), Num(3))), Bag(List(Num(1), Num(2), Num(3))))) == BagV(ListMap(NumV(1) -> 2, NumV(2) -> 2, NumV(3) -> 2)))
  }

  test("Sum (expects bags)") {
    assertThrows[Exception] {
      Interpreter.eval(Sum(Num(1), Num(1)))
    }
  }

  test("Diff") {
    assert(Interpreter.eval(Diff(Bag(List(Num(1), Num(2), Num(3))), Bag(List(Num(4), Num(5), Num(6))))) == BagV(ListMap(NumV(1) -> 1, NumV(2) -> 1, NumV(3) -> 1)))
    assert(Interpreter.eval(Diff(Bag(List(Num(1), Num(2), Num(3))), Bag(List(Num(1), Num(2), Num(3))))) == BagV(ListMap()))
  }

  test("Diff (expects bags)") {
    assertThrows[Exception] {
      Interpreter.eval(Diff(Num(1), Num(1)))
    }
  }

  test("Count") {
    assert(Interpreter.eval(Count(Bag(List(Num(1), Num(2), Num(3))), Num(2))) == NumV(1))
  }

  test("Count (expects bag)") {
    assertThrows[Exception] {
      Interpreter.eval(Count(Num(1), Num(1)))
    }
  }

  test("Pattern Matching Should Be Desugared") {
    assertThrows[Exception] {
      Interpreter.eval(LetPair("z", "w", Pair(Num(1), Num(2)), Var("z")))
    }

    assertThrows[Exception] {
      Interpreter.eval(LetFun("f", TyInt, "z", Var("f"), Var("f")))
    }

    assertThrows[Exception] {
      Interpreter.eval(LetRec("f", TyInt, "z", Var("f"), Var("f")))
    }

    assertThrows[Exception] {
      Interpreter.eval(LetRecord(ListMap("l" -> "z"), Var("r"), Var("r")))
    }

    assertThrows[Exception] {
      Interpreter.eval(Comprehension(Var("z"), List(Num(1))))
    }

    assertThrows[Exception] {
      Interpreter.eval(Bind("x", Num(1)))
    }

    assertThrows[Exception] {
      Interpreter.eval(Guard(Num(1)))
    }

    assertThrows[Exception] {
      Interpreter.eval(CLet("x", Num(1)))
    }
  }
}

// Parser
class ParseStrArithTests extends AnyFunSuite {
  test("Unit") {
    assert(parser.parseStr("()") == Unit)
  }

  test("Num") {
    assert(parser.parseStr("1") == Num(1))
  }

  test("Plus") {
    assert(parser.parseStr("1 + 2") == Plus(Num(1), Num(2)))
  }

  test("Minus") {
    assert(parser.parseStr("1 - 2") == Minus(Num(1), Num(2)))
  }

  test("Times") {
    assert(parser.parseStr("1 * 2") == Times(Num(1), Num(2)))
  }
}

class ParseStrBoolTests extends AnyFunSuite {
  test("Bool") {
    assert(parser.parseStr("true") == Bool(true))
  }

  test("Eq") {
    assert(parser.parseStr("1 == 1") == Eq(Num(1), Num(1)))
  }

  test("Less") {
    assert(parser.parseStr("1 < 2") == Less(Num(1), Num(2)))
  }

  test("IfThenElse") {
    assert(parser.parseStr("if true then 1 else 2") == IfThenElse(Bool(true), Num(1), Num(2)))
  }

  test("Str") {
    assert(parser.parseStr("\"hello\"") == Str("hello"))
  }
}

class ParseStrStringTests extends AnyFunSuite{
  test("String") {
    assert(parser.parseStr("\"hello\"") == Str("hello"))
  }

  test("Length") {
    assert(parser.parseStr("length(\"hello\")") == Length(Str("hello")))
  }

  test("Index") {
    assert(parser.parseStr("index(\"hello\", 0)") == Index(Str("hello"), Num(0)))
  }

  test("Concat") {
    assert(parser.parseStr("concat(\"hello\", \"world\")") == Concat(Str("hello"), Str("world")))
  }
}

class ParseStrVarTests extends AnyFunSuite {
  test("Var") {
    assert(parser.parseStr("x") == Var("x"))
  }

  test("Let") {
    assert(parser.parseStr("let x = 1 in x") == Let("x", Num(1), Var("x")))
  }
}

class ParseStrAnnoTests extends AnyFunSuite {
  test("Anno") {
    assert(parser.parseStr("1 : int") == Anno(Num(1), TyInt))
  }
}

class ParseStrFunctionTests extends AnyFunSuite {
  test("Lambda") {
    assert(parser.parseStr("\\x . x") == Lambda("x", Var("x")))
  }

  test("Apply") {
    assert(parser.parseStr("f(x)") == Apply(Var("f"), Var("x")))
  }
}

class ParseStrPairTests extends AnyFunSuite {
  test("Pair") {
    assert(parser.parseStr("(1, 2)") == Pair(Num(1), Num(2)))
  }

  test("First") {
    assert(parser.parseStr("fst((1, 2))") == First(Pair(Num(1), Num(2))))
  }

  test("Second") {
    assert(parser.parseStr("snd((1, 2))") == Second(Pair(Num(1), Num(2))))
  }
}

class ParseStrRecordTests extends AnyFunSuite {
  test("Record") {
    assert(parser.parseStr("<l=42>") == Record(ListMap("l" -> Num(42))))
  }

  test("Proj") {
    assert(parser.parseStr("r.foo") == Proj(Var("r"), "foo"))
  }
}

class ParseStrVariantTests extends AnyFunSuite {
  test("Case") {
    assert(parser.parseStr("case v of {foo x -> 1, bar y -> 2}") == Case(Var("v"), ListMap("foo" -> ("x", Num(1)), "bar" -> ("y", Num(2)))))
  }
}

class ParseStrErrorTests extends AnyFunSuite {
  test("Malformed Plus") {
    assertThrows[Exception] {
      parser.parseStr("1 +")
    }
  }

  test("Malformed Let") {
    assertThrows[Exception] {
      parser.parseStr("let x = 1")
    }
  }

  test("Malformed Anno") {
    assertThrows[Exception] {
      parser.parseStr("1 :")
    }
  }

  test("Malformed Lambda") {
    assertThrows[Exception] {
      parser.parseStr("\\x")
    }
  }

  test("Malformed Apply") {
    assertThrows[Exception] {
      parser.parseStr("f(x")
    }
  }

  test("Malformed Pair") {
    assertThrows[Exception] {
      parser.parseStr("(1,")
    }
  }

  test("Malformed First") {
    assertThrows[Exception] {
      parser.parseStr("fst((1, 2")
    }
  }

  test("Malformed Second") {
    assertThrows[Exception] {
      parser.parseStr("snd((1, 2")
    }
  }

  test("Malformed Record") {
    assertThrows[Exception] {
      parser.parseStr("<l=42")
    }
  }

  test("Malformed Proj") {
    assertThrows[Exception] {
      parser.parseStr("r.")
    }
  }

  test("Malformed Case") {
    assertThrows[Exception] {
      parser.parseStr("case v of {foo x -> 1, bar y -> 2")
    }
  }

  test("Malformed Bag") {
    assertThrows[Exception] {
      parser.parseStr("Bag(1, 2, 3")
    }
  }

  test("Malformed FlatMap") {
    assertThrows[Exception] {
      parser.parseStr("flatMap(Bag(1, 2, 3), (x) => Bag(x + 1))")
    }
  }

  test("Malformed When") {
    assertThrows[Exception] {
      parser.parseStr("when(Bag(1, 2, 3), (x) => x > 1)")
    }
  }

  test("Malformed Count") {
    assertThrows[Exception] {
      parser.parseStr("count(Bag(1, 2, 3), 2")
    }
  }

  test("Malformed Sum") {
    assertThrows[Exception] {
      parser.parseStr("sum(Bag(1, 2, 3), Bag(2, 3, 4")
    }
  }

  test("Malformed Diff") {
    assertThrows[Exception] {
      parser.parseStr("diff(Bag(1, 2, 3), Bag(2, 3, 4")
    }
  }

  test("Malformed LetPair") {
    assertThrows[Exception] {
      parser.parseStr("let (x, y) = (1, ) in x")
    }
  }

  test("Malformed LetRecord") {
    assertThrows[Exception] {
      parser.parseStr("let <l=1, m=2> in l")
    }
  }

  test("Malformed Comprehension") {
    assertThrows[Exception] {
      parser.parseStr("comprehension(Bag(1, 2, 3), (x) => Bag(x + 1))")
    }
  }

  test("Malformed Bind") {
    assertThrows[Exception] {
      parser.parseStr("bind(x, Bag(1, 2, 3))")
    }
  }

  test("Malformed Guard") {
    assertThrows[Exception] {
      parser.parseStr("guard(Bag(1, 2, 3))")
    }
  }

  test("Malformed CLet") {
    assertThrows[Exception] {
      parser.parseStr("clet(x, Bag(1, 2, 3))")
    }
  }
}

class ParseTyStrTests extends AnyFunSuite{
  test("TyUnit") {
    assert(parser.parseTyStr("unit") == TyUnit)
  }

  test("TyInt") {
    assert(parser.parseTyStr("int") == TyInt)
  }

  test("TyBool") {
    assert(parser.parseTyStr("bool") == TyBool)
  }

  test("TyString") {
    assert(parser.parseTyStr("string") == TyString)
  }

  test("TyPair") {
    assert(parser.parseTyStr("int * bool") == TyPair(TyInt, TyBool))
  }

  test("TyFun") {
    assert(parser.parseTyStr("int -> bool") == TyFun(TyInt, TyBool))
  }

  test("TyRecord") {
    assert(parser.parseTyStr("<foo:int, bar:bool>") == TyRecord(ListMap("foo" -> TyInt, "bar" -> TyBool)))
  }

  test("TyVariant") {
    assert(parser.parseTyStr("[some: int, none: unit]") == TyVariant(ListMap("some" -> TyInt, "none" -> TyUnit)))
  }

  test("TyBag") {
    assert(parser.parseTyStr("{|int|}") == TyBag(TyInt))
  }
}

class ParseTyStrErrorTests extends AnyFunSuite {
  test("Malformed TyPair") {
    assertThrows[Exception] {
      parser.parseTyStr("int *")
    }
  }

  test("Malformed TyFun") {
    assertThrows[Exception] {
      parser.parseTyStr("int ->")
    }
  }

  test("Malformed TyRecord") {
    assertThrows[Exception] {
      parser.parseTyStr("<foo:int, bar:bool")
    }
  }

  test("Malformed TyVariant") {
    assertThrows[Exception] {
      parser.parseTyStr("[some: int, none: unit")
    }
  }

  test("Malformed TyBag") {
    assertThrows[Exception] {
      parser.parseTyStr("{|int|")
    }
  }
}

class ParseTests extends AnyFunSuite {
  test("Parse examples/simple.frog") {
    val file = "examples/simple.frog"
    val parsed = parser.parse(file)
    assert(parsed == Let("x", Num(1), Plus(Var("x"), Num(1))))
  }
}

// class FunctionNameMismatch extends AnyFunSuite {
//
// }



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