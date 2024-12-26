package FrogInterpreter

import scala.language.implicitConversions
import scala.collection.immutable.ListMap
import scala.collection.Seq
import FrogInterpreter.Bags.BagImpl


/*======================================================================
  The rest of this file is support code, which you should not (and do not
  need to) change.
  ====================================================================== */

object Syntax {
  type Variable = String
  type Env = ListMap[Variable, Type]
  type Label = String
  type Field[A] = ListMap[Label, A]

  // ======================================================================
  // Expressions
  // ======================================================================
  sealed abstract class Expr

  // Unit
  case object Unit extends Expr

  // Arithmetic expressions
  case class Num(n: Integer) extends Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
  case class Minus(e1: Expr, e2: Expr) extends Expr
  case class Times(e1: Expr, e2: Expr) extends Expr

  // Booleans
  case class Bool(b: Boolean) extends Expr
  case class Eq(e1: Expr, e2: Expr) extends Expr
  case class Less(e1: Expr, e2: Expr) extends Expr
  case class IfThenElse(e: Expr, e1: Expr, e2: Expr) extends Expr

  // Strings
  case class Str(s: String) extends Expr
  case class Length(e: Expr) extends Expr
  case class Index(e1: Expr, e2: Expr) extends Expr
  case class Concat(e1: Expr, e2: Expr) extends Expr

  // Variables and let-binding
  case class Var(x: Variable) extends Expr
  case class Let(x: Variable, e1: Expr, e2: Expr) extends Expr

  // Annotations
  case class Anno(e: Expr, ty: Type) extends Expr

  // Functions
  case class Lambda(x: Variable, e: Expr) extends Expr
  case class Apply(e1: Expr, e2: Expr) extends Expr
  case class Rec(f: Variable, x: Variable, e: Expr) extends Expr

  // Pairing
  case class Pair(e1: Expr, e2: Expr) extends Expr
  case class First(e: Expr) extends Expr
  case class Second(e: Expr) extends Expr

  // Records
  case class Record(es: Field[Expr]) extends Expr
  case class Proj(e: Expr, l: Label) extends Expr

  // Variants
  case class Variant(l: Label, e: Expr) extends Expr
  case class Case(e: Expr, cls: Field[(Variable, Expr)]) extends Expr

  // Bags
  case class Bag(es: List[Expr]) extends Expr
  case class FlatMap(e1: Expr, e2: Expr) extends Expr
  case class When(e1: Expr, e2: Expr) extends Expr
  case class Count(e1: Expr, e2: Expr) extends Expr
  case class Sum(e1: Expr, e2: Expr) extends Expr
  case class Diff(e1: Expr, e2: Expr) extends Expr

  // Syntactic sugars
  case class LetPair(x: Variable, y: Variable, e1: Expr, e2: Expr) extends Expr
  case class LetFun(f: Variable, ty: Type, arg: Variable, e1: Expr, e2: Expr) extends Expr
  case class LetRec(f: Variable, ty: Type, arg: Variable, e1: Expr, e2: Expr) extends Expr
  case class LetRecord(xs: Field[Variable], e1: Expr, e2: Expr) extends Expr
  case class Comprehension(e: Expr, es: List[Expr]) extends Expr
  case class Bind(x: Variable, e: Expr) extends Expr
  case class Guard(e: Expr) extends Expr
  case class CLet(x: Variable, e: Expr) extends Expr

  // Values
  abstract class Value extends Expr
  case object UnitV extends Value
  case class NumV(n: Integer) extends Value
  case class BoolV(b: Boolean) extends Value
  case class StringV(s: String) extends Value
  case class PairV(v1: Value, v2: Value) extends Value
  case class RecordV(vs: Field[Value]) extends Value
  case class VariantV(l: Label, v:Value) extends Value
  case class BagV(vs: BagImpl.T[Value]) extends Value {
    override def toString: String = BagImpl.toString(vs)
  }
  case class FunV(x: Variable, e: Expr) extends Value
  case class RecV(f:Variable, x: Variable, e: Expr) extends Value

  // ======================================================================
  // Types
  // ======================================================================
  sealed abstract class Type

  // Types
  case object TyUnit extends Type
  case object TyInt extends Type
  case object TyBool extends Type
  case object TyString extends Type
  case class  TyPair(ty1: Type, ty2: Type) extends Type
  case class  TyFun(ty1: Type, ty2: Type) extends Type
  case class  TyRecord(tys: Field[Type]) extends Type
  case class  TyVariant(tys: Field[Type]) extends Type
  case class  TyBag(ty: Type) extends Type


  // ======================================================================
  // Substitutions
  // ======================================================================

  // a class for generating fresh variables
  class SymGenerator {
    private var id = 0
    // generate a fresh variable from an existing variable
    def genVar(s: Variable): Variable = {
      val fresh_s = s + "_" + id
      id = id + 1
      fresh_s
    }
    // generate a fresh variable from nothing
    def freshVar(): Variable = {
      val fresh_s = "$" + id
      id = id + 1
      fresh_s
    }
    // reset the counter
    def reset(): Unit = {id = 0}
  }

  // swap y and z in x
  def swapVar(x: Variable, y: Variable, z: Variable): Variable =
    if x == y then z else if x == z then y else x

  // a trait for substitutable things, e.g., expressions and types
  trait Substitutable[A] {
    // swap y and z in t
    def swap(t: A, y: Variable, z: Variable): A

    // subst x in t1 with t2, i.e., t1[t2/x]
    def subst(t1: A, t2: A, x: Variable): A
  }
}


