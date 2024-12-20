package Assign3.Interpreter

import Assign3.Parser.Parser
import Assign3.Syntax.Syntax._
import Assign3.Typer.Typer
import Assign3.Bags.Bags.BagImpl
import scala.collection.immutable.ListMap

object Interpreter {

  // ======================================================================
  // Capture-avoiding substitution
  // ======================================================================

  val generator = SymGenerator()

  object SubstExpr extends Substitutable[Expr] {
    // swap y and z in e
    def swap(e: Expr, y: Variable, z: Variable): Expr =
      def go(e: Expr): Expr = e match {
        // Value must be closed
        case v: Value => v

        case Unit => Unit

        case Num(n) => Num(n)
        case Plus(e1, e2) => Plus(go(e1), go(e2))
        case Minus(e1, e2) => Minus(go(e1), go(e2))
        case Times(e1, e2) => Times(go(e1), go(e2))

        case Bool(b) => Bool(b)
        case Eq(e1, e2) => Eq(go(e1), go(e2))
        case Less(e1, e2) => Less(go(e1), go(e2))
        case IfThenElse(e, e1, e2) => IfThenElse(go(e), go(e1), go(e2))

        case Str(s) => Str(s)
        case Length(e) => Length(go(e))
        case Index(e1, e2) => Index(go(e1), go(e2))
        case Concat(e1, e2) => Concat(go(e1), go(e2))

        case Var(x) => Var(swapVar(x,y,z))
        case Let(x,e1,e2) => Let(swapVar(x,y,z),go(e1),go(e2))

        case Anno(e, ty) => Anno(go(e), ty)
        // case Inst(e, ty) => Inst(go(e), ty)

        case Pair(e1,e2) => Pair(go(e1),go(e2))
        case First(e) => First(go(e))
        case Second(e) => Second(go(e))

        case Lambda(x,e) => Lambda(swapVar(x,y,z),go(e))
        case Apply(e1,e2) => Apply(go(e1),go(e2))
        case Rec(f,x,e) => Rec(swapVar(f,y,z), swapVar(x,y,z), go(e))

        case Record(es) => Record(es.map((x, e) => (x, go(e))))
        case Proj(e, l) => Proj(go(e), l)

        case Variant(l, e) => Variant(l, go(e))
        case Case(e, cls) => Case(go(e), cls.map((l, entry) =>
          val (x, e) = entry
          (l, (swapVar(x,y,z), go(e)))))

        case Bag(es) => Bag(es.map(e => go(e)))
        case FlatMap(e1, e2) => FlatMap(go(e1), go(e2))
        case When(e1, e2) => When(go(e1), go(e2))
        case Sum(e1, e2) => Sum(go(e1), go(e2))
        case Diff(e1, e2) => Diff(go(e1), go(e2))
        case Comprehension(e, es) => Comprehension(go(e), es.map(e => go(e)))
        case Bind(x, e) => Bind(swapVar(x,y,z), go(e))
        case Guard(e) => Guard(go(e))
        case CLet(x, e) => CLet(swapVar(x,y,z), go(e))
        case Count(e1, e2) => Count(go(e1), go(e2))

        case LetPair(x1,x2,e1,e2) =>
          LetPair(swapVar(x1,y,z),swapVar(x2,y,z),go(e1),go(e2))
        case LetFun(f,ty,x,e1,e2) =>
          LetFun(swapVar(f,y,z),ty,swapVar(x,y,z),go(e1),go(e2))
        case LetRec(f,ty,x,e1,e2) =>
          LetRec(swapVar(f,y,z),ty,swapVar(x,y,z),go(e1),go(e2))
        case LetRecord(xs,e1,e2) =>
          LetRecord(xs.map((l,x) => (l, swapVar(x,y,z))),go(e1),go(e2))
        }
      go(e)

    ////////////////////
    // EXERCISE 4     //
    ////////////////////
    def subst(e1: Expr, e2: Expr, x: Variable): Expr = {
      // BEGIN ANSWER
      def go(e: Expr): Expr = e match {
        // Value must be closed
        case v: Value => v
        case Unit => Unit

        case Num(e) => Num(e)
        case Plus(e1, e2)  => Plus(go(e1), go(e2))
        case Minus(e1, e2) => Minus(go(e1), go(e2))
        case Times(e1, e2) => Times(go(e1), go(e2))

        case Bool(b) => Bool(b)
        case Eq(e1, e2) => Eq(go(e1), go(e2))
        case Less(e1, e2) => Less(go(e1), go(e2))
        case IfThenElse(e, e1, e2) => IfThenElse(go(e), go(e1), go(e2))

        case Str(s) => Str(s)
        case Length(e) => Length(go(e))
        case Index(e1, e2) => Index(go(e1), go(e2))
        case Concat(e1, e2) => Concat(go(e1), go(e2))

        case Var(y) =>
          if x == y then e2 else Var(y)
        case Let(y, e1, e2) =>
          val fresh_y = generator.genVar(y);
          val fresh_e2 = swap(e2, y, fresh_y);
          Let(fresh_y, go(e1), go(fresh_e2))

        case Anno(e, ty) => Anno(go(e), ty)
        // case Inst(e, ty) => Inst(go(e), ty)

        case Lambda(x, e) =>
          val fresh_x = generator.genVar(x)
          val fresh_e = swap(e, x, fresh_x)
          Lambda(fresh_x, go(fresh_e))
        case Apply(e1, e2) => Apply(go(e1), go(e2))
        case Rec(f, x, e) =>
          val fresh_f = generator.genVar(f)
          val fresh_x = generator.genVar(x)
          val fresh_e = swap(swap(e, x, fresh_x), f, fresh_f)
          Rec(fresh_f, fresh_x, go(fresh_e))

        case Pair(e1, e2) => Pair(go(e1), go(e2))
        case First(e) => First(go(e))
        case Second(e) => Second(go(e))

        case Record(es) => Record(es.map((l, e) => (l, go(e))))
        case Proj(e, l) => Proj(go(e), l)

        case Variant(l, e) => Variant(l, go(e))
        case Case(e, cls) => Case(go(e), cls.map((l, entry) =>
          val (x, e) = entry
          val fresh_x = generator.genVar(x)
          val fresh_e = swap(e, x, fresh_x)
          (l, (fresh_x, go(fresh_e)))))

        case Bag(es) => Bag(es.map(e => go(e)))
        case FlatMap(e1, e2) => FlatMap(go(e1), go(e2))
        case When(e1, e2) => When(go(e1), go(e2))
        case Sum(e1, e2) => Sum(go(e1), go(e2))
        case Diff(e1, e2) => Diff(go(e1), go(e2))
        case Comprehension(e, es) =>
          def help(es: List[Expr]): List[Expr] = es match
            case Nil => Nil
            case p :: ps => p match {
              case Bind(x, e) =>
                val fresh_x = generator.genVar(x)
                val fresh_ps = ps.map(p => swap(p, x, fresh_x))
                Bind(fresh_x, go(e)) :: help(fresh_ps)
              case CLet(x, e) =>
                val fresh_x = generator.genVar(x)
                val fresh_ps = ps.map(p => swap(p, x, fresh_x))
                CLet(fresh_x, go(e)) :: help(fresh_ps)
              case Guard(e) => Guard(go(e)) :: help(ps)
              case _ => sys.error("subst: unexpected pattern in comprehension")
            }
          Comprehension(go(e), help(es))
        // case Bind(x, e) =>
        //   val fresh_x = generator.genVar(x)
        //   val fresh_e = swap(e, x, fresh_x)
        //   Bind(fresh_x, go(fresh_e))
        // case CLet(x, e) =>
        //   val fresh_x = generator.genVar(x)
        //   val fresh_e = swap(e, x, fresh_x)
        //   CLet(fresh_x, go(fresh_e))
        // case Guard(e) => Guard(go(e))
        case Bind(_, _) => sys.error("subst: unexpected Bind")
        case CLet(_, _) => sys.error("subst: unexpected CLet")
        case Guard(_) => sys.error("subst: unexpected Guard")
        case Count(e1, e2) => Count(go(e1), go(e2))

        case LetPair(x1,x2,e1,e2) =>
          val fresh_x1 = generator.genVar(x1)
          val fresh_x2 = generator.genVar(x2)
          val fresh_e2 = swap(swap(e2,x1,fresh_x1),x2,fresh_x2)
          LetPair(fresh_x1,fresh_x2,go(e1),go(fresh_e2))
        case LetFun(f,ty,x,e1,e2) =>
          val fresh_f = generator.genVar(f)
          val fresh_x = generator.genVar(x)
          val fresh_e1 = swap(e1,x,fresh_x)
          val fresh_e2 = swap(e2,f,fresh_f)
          LetFun(fresh_f,ty,fresh_x,go(fresh_e1),go(fresh_e2))
        case LetRec(f,ty,x,e1,e2) =>
          val fresh_f = generator.genVar(f)
          val fresh_x = generator.genVar(x)
          val fresh_e1 = swap(swap(e1,x,fresh_x),f,fresh_f)
          val fresh_e2 = swap(e2,f,fresh_f)
          LetRec(fresh_f,ty,fresh_x,go(fresh_e1),go(fresh_e2))
        case LetRecord(xs,e1,e2) =>
          val swaps = xs.map{ case (l,x) => (l,(x,generator.genVar(x)))}
          val fresh_e2 = swaps.foldLeft(e2){case (e,(l,(x,fx))) => swap(e,x,fx)}
          val fresh_xs = swaps.map{ case (l,(x,fresh_x)) => (l,fresh_x)}
          LetRecord(fresh_xs,go(e1),go(fresh_e2))
      }
      go(e1)
    // END ANSWER
    }

  }
  import SubstExpr.{subst}


  
  // ======================================================================
  // Desugaring and Type Erasure
  // ======================================================================
    ////////////////////
    // EXERCISE 4     //
    ////////////////////

  def desugar(e: Expr): Expr = e match {
    // Value
    case v: Value =>
      sys.error("desugar: there shouldn't be any values here")

    // BEGIN ANSWER
    // Unit
    case Unit => Unit

    // Arithmetic
    case Num(n) => Num(n)
    case Plus(e1, e2) => Plus(desugar(e1), desugar(e2))
    case Minus(e1, e2) => Minus(desugar(e1), desugar(e2))
    case Times(e1, e2) => Times(desugar(e1), desugar(e2))

    // Booleans
    case Bool(b) => Bool(b)
    case Eq(e1, e2) => Eq(desugar(e1), desugar(e2))
    case Less(e1, e2) => Less(desugar(e1), desugar(e2))
    case IfThenElse(e, e1, e2) =>
      IfThenElse(desugar(e), desugar(e1), desugar(e2))

    // Strings
    case Str(s) => Str(s)
    case Length(e) => Length(desugar(e))
    case Index(e1, e2) => Index(desugar(e1), desugar(e2))
    case Concat(e1, e2) => Concat(desugar(e1), desugar(e2))

    // Variables and let-binding
    case Var(x) => Var(x)
    case Let(x, e1, e2) => Let(x, desugar(e1), desugar(e2))

    // Annotations and Instantiation
    case Anno(e, _) => desugar(e)
    // case Inst(e, _) => desugar(e)

    // Functions
    case Lambda(x, e) => Lambda(x, desugar(e))
    case Rec(f, x, e) => Rec(f, x, desugar(e))
    case Apply(e1, e2) => Apply(desugar(e1), desugar(e2))

    // Pairing
    case Pair(e1, e2) => Pair(desugar(e1), desugar(e2))
    case First(e) => First(desugar(e))
    case Second(e) => Second(desugar(e))

    // Records
    case Record(es) => Record(es.map((l, e) => (l, desugar(e))))
    case Proj(e, l) => Proj(desugar(e), l)

    // Variants
    case Variant(l, e) => Variant(l, desugar(e))
    case Case(e, cls) => Case(desugar(e), cls.map((l, entry) =>
      val (x, e) = entry
      (l, (x, desugar(e)))))

    // Bags
    case Bag(es) => Bag(es.map(e => desugar(e)))
    case FlatMap(e1, e2) => FlatMap(desugar(e1), desugar(e2))
    case When(e1, e2) => When(desugar(e1), desugar(e2))
    case Sum(e1, e2) => Sum(desugar(e1), desugar(e2))
    case Diff(e1, e2) => Diff(desugar(e1), desugar(e2))
    case Count(e1, e2) => Count(desugar(e1), desugar(e2))
    case Comprehension(e, es) =>
      def desugarBag(e: Expr, ps: List[Expr]): Expr = ps match
        case Nil => Bag(List(desugar(e)))
        case p :: ps =>
          val res = desugarBag(e, ps)
          p match {
            case Bind(x, e) => FlatMap(desugar(e), Lambda(x, res))
            case Guard(e)   => When(desugar(e), res)
            case CLet(x, e) => Let(x, desugar(e), res)
            case _ => sys.error("desugar: unexpected pattern in comprehension")
          }
      desugarBag(e, es)

    // Syntactic sugars
    case LetPair(x, y, e1, e2) =>
      val p = generator.freshVar()
      Let(p, desugar(e1), subst(subst(desugar(e2), First(Var(p)), x), Second(Var(p)), y))
    case LetFun(f, ty, x, e1, e2) =>
      Let(f, Lambda(x, desugar(e1)), desugar(e2))
    case LetRec(f, ty, x, e1, e2) =>
      Let(f, Rec(f, x, desugar(e1)), desugar(e2))
    case LetRecord(xs, e1, e2) =>
      val r = generator.freshVar()
      val e2res = xs.foldLeft(desugar(e2))((expr, lvar) =>
        val (l, x) = lvar
        subst(expr, Proj(Var(r), l), x))
      Let(r, desugar(e1), e2res)
    case Bind(_, _) => sys.error("desugar: unexpected Bind")
    case Guard(_) => sys.error("desugar: unexpected Guard")
    case CLet(_, _) => sys.error("desugar: unexpected CLet")
    // END ANSWER
    }


  // ======================================================================
  // Primitive operations
  // ======================================================================

  object Value {
    // utility methods for operating on values
    def add(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV (v1 + v2)
      case _ => sys.error("arguments to addition are non-numeric")

    def subtract(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV (v1 - v2)
      case _ => sys.error("arguments to subtraction are non-numeric")

    def multiply(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV (v1 * v2)
      case _ => sys.error("arguments to multiplication are non-numeric")

    def eq(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => BoolV (v1 == v2)
      case (BoolV(v1), BoolV(v2)) => BoolV (v1 == v2)
      case (StringV(v1), StringV(v2)) => BoolV (v1 == v2)
      case (PairV(v11, v12), PairV(v21, v22)) => BoolV (v11 == v21 && v12 == v22)
      case (VariantV(l1, v1), VariantV(l2, v2)) => BoolV (l1 == l2 && v1 == v2)
      // no comparision for bags and records currently
      case _ => sys.error("arguments to = are not comparable")

    def less(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => BoolV (v1 < v2)
      case _ => sys.error("arguments to < are not comparable")

    def length(v: Value): Value = v match
      case StringV(v1) => NumV(v1.length)
      case _ => sys.error("argument to length is not a string")

    def index(v1: Value, v2: Value): Value = (v1, v2) match
      case (StringV(v1), NumV(v2)) => StringV(v1.charAt(v2).toString)
      case _ => sys.error("arguments to index are not valid")

    def concat(v1: Value, v2: Value): Value = (v1, v2) match
      case (StringV(v1), StringV(v2)) => StringV(v1 ++ v2)
      case _ => sys.error("arguments to concat are not strings")
  }



  // ======================================================================
  // Evaluation
  // ======================================================================

    ////////////////////
    // EXERCISE 6     //
    ////////////////////
  def eval (e : Expr): Value = e match {
    // Value
    case v: Value => v

    // BEGIN ANSWER
    // Unit
    case Unit => UnitV

    // Arithmetic
    case Num(n) => NumV(n)
    case Plus(e1, e2) =>
      Value.add(eval(e1), eval(e2))
    case Minus(e1, e2) =>
      Value.subtract(eval(e1), eval(e2))
    case Times(e1, e2) =>
      Value.multiply(eval(e1), eval(e2))

    // Booleans
    case Bool(b) => BoolV(b)
    case Eq(e1, e2) =>
      Value.eq(eval(e1), eval(e2))
    case Less(e1, e2) =>
      Value.less(eval(e1), eval(e2))
    case IfThenElse(e, e1, e2) => eval(e) match
      case BoolV(b) => if b then eval(e1) else eval(e2)

    // Strings
    case Str(s) => StringV(s)
    case Length(e) =>
      Value.length(eval(e))
    case Index(e1, e2) =>
      Value.index(eval(e1), eval(e2))
    case Concat(e1, e2) =>
      Value.concat(eval(e1), eval(e2))

    // Variables and let-binding
    case Var(x) =>
      sys.error("eval: free variable " ++ x)
    case Let(x, e1, e2) =>
      val v = eval(e1)
      eval(subst(e2, v, x))

    // Functions
    case Lambda(x, e) => FunV(x, e)
    case Rec(f, x, e) => RecV(f, x, e)
    case Apply(e1, e2) =>
      val v = eval(e2)
      eval(e1) match
        case FunV(x, e) => eval(subst(e, v, x))
        case RecV(f, x, e) => eval(subst(subst(e, v, x), RecV(f, x, e), f))

    // Pairing
    case Pair(e1, e2) => PairV(eval(e1), eval(e2))
    case First(e) => eval(e) match
      case PairV(v1, _) => v1
    case Second(e) => eval(e) match
      case PairV(_, v2) => v2

    // Records
    case Record(es) =>
      RecordV(es.map((l, e) => (l, eval(e))))
    case Proj(e, l) => eval(e) match
      case RecordV(vs) => vs.get(l) match
        case None =>
          sys.error("eval: label " ++ l ++ " does not exist")
        case Some(v) => v

    // Variants
    case Variant(l, e) => VariantV(l, eval(e))
    case Case(e, cls) => eval(e) match
      case VariantV(l, v) => cls.get(l) match
        case None =>
          sys.error("eval: label " ++ l ++ " does not exist")
        case Some((x, e)) => eval(subst(e, v, x))

    // Bags
    case Bag(es) => BagV(BagImpl.fromList(es.map(e => eval(e))))
    case FlatMap(e1, e2) => (eval(e1), eval(e2)) match {
      case (BagV(es), v) => BagV(BagImpl.flatMap(es,{y => eval(Apply(v,y)) match {
        case BagV(es3) => es3
        case _ => sys.error("eval: flatMap expects a bag")
      }}))
      case _ => sys.error("eval: flatMap expects a bag and a function")
    }
    case When(e1, e2) => (eval(e1), eval(e2)) match {
      case (BoolV(b), BagV(es)) => if b then BagV(es) else BagV(BagImpl.fromList(Nil))
      case _ => sys.error("eval: when expects a boolean and a bag")
    }
    case Sum(e1, e2) => (eval(e1), eval(e2)) match {
      case (BagV(es1), BagV(es2)) => BagV(BagImpl.sum(es1,es2))
      case _ => sys.error("eval: sum expects two bags")
    }
    case Diff(e1, e2) => (eval(e1), eval(e2)) match {
      case (BagV(es1), BagV(es2)) => BagV(BagImpl.diff(es1,es2))
      case _ => sys.error("eval: diff expects two bags")
    }
    case Count(e1, e2) => eval(e1) match {
      case BagV(es) =>
        val v2 = eval(e2)
        NumV(BagImpl.count(es,v2))
      case _ => sys.error("eval: count expects a bag")
    }

    // Syntactic sugars or erased terms
    case Anno(_, _) =>
      sys.error("eval: annotation should be desugared")
    case LetPair(_, _, _, _) =>
      sys.error("eval: pattern matching should be desugared")
    case LetFun(_, _, _, _, _) =>
      sys.error("eval: pattern matching should be desugared")
    case LetRec(_, _, _, _, _) =>
      sys.error("eval: pattern matching should be desugared")
    case LetRecord(_, _, _) =>
      sys.error("eval: pattern matching should be desugared")
    case Comprehension(_, _) =>
      sys.error("eval: comprehension should be desugared")
    case Bind(_, _) =>
      sys.error("eval: comprehension should be desugared")
    case Guard(_) =>
      sys.error("eval: comprehension should be desugared")
    case CLet(_, _) =>
      sys.error("eval: comprehension should be desugared")
  // END ANSWER
  }

  /////////////////////////////////////////////////////////
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
  // THE REST OF THIS FILE SHOULD NOT NEED TO BE CHANGED //
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
  /////////////////////////////////////////////////////////
  
  // ======================================================================
  // Some simple programs
  // ======================================================================

  // The following examples illustrate how to embed Frog source code into
  // Scala using multi-line comments, and parse it using parser.parseStr.

  // Example 1: the swap function
  def example1: Expr = parser.parseStr("""
    let swap = \ x . (snd(x), fst(x)) in
    swap(42,17)
    """)

  val parser = new Parser

  // ======================================================================
  // Main
  // ======================================================================

  object Main {
    def typecheck(ast: Expr):Type =
      Typer.tyInfer(ListMap(), ast);

    def evaluate(ast: Expr):Value =
      eval(ast)

    def showResult(ast: Expr) = {
      println("AST:  " + ast.toString + "\n")

      try {
        print("Type Checking...");
        val ty = typecheck(ast);
        println("Done!");
        println("Type of Expression: " + ty.toString + "\n") ;
      } catch {
          case e:Throwable => println("Error: " + e)
      }
      try {
        println("Desugaring...");
        val core_ast = desugar(ast);
        println("Done!");
        println("Desugared AST: " + core_ast.toString + "\n") ;

        println("Evaluating...");
        println("Result: " + evaluate(core_ast))
      } catch {
        case e:Throwable => {
          println("Error: " + e)
          println("Evaluating raw AST...");
          println("Result: " + evaluate(ast))
        }
      }
    }

    def start(): Unit = {
      println("Welcome to Frog! (V1.0, October 22, 2024)");
      println("Enter expressions to evaluate, :load <filename.fish> to load a file, or :quit to quit.");
      println("This REPL can only read one line at a time, use :load to load larger expressions.");
      repl()
    }

    def repl(): Unit = {
      print("Frog> ");
      val input = scala.io.StdIn.readLine();
      if(input == ":quit") {
        println("Goodbye!")
      }
      else if (input.startsWith(":load")) {
        try {
          val ast = parser.parse(input.substring(6));
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      } else {
        try {
          val ast = parser.parseStr(input);
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      }
    }
  }

  def main( args:Array[String] ):Unit = {
    if(args.length == 0) {
      Main.start()
    } else {
      try {
        print("Parsing...");
        val ast = parser.parse(args.head)
        println("Done!");
        Main.showResult(ast)
      } catch {
        case e:Throwable => println("Error: " + e)
      }
    }
  }

}
