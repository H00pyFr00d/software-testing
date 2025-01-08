package FrogInterpreter

import FrogInterpreter.Syntax.*
import FrogInterpreter.Bags.BagImpl

import scala.annotation.tailrec
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
    def subst(t: Expr, e: Expr, x: Variable): Expr = {
      t match {
        // Unit
        case Unit => Unit

        // Arithmetic expressions
        case Num(e) => Num(e)
        case Plus(t1,t2) => Plus(subst(t1,e,x),subst(t2,e,x))
        case Minus(t1,t2) => Minus(subst(t1,e,x),subst(t2,e,x))
        case Times(t1,t2) => Times(subst(t1,e,x),subst(t2,e,x))

        // Booleans
        case Bool(b) => Bool(b)
        case Eq(t1,t2) => Eq(subst(t1,e,x),subst(t2,e,x))
        case Less(t1,t2) => Less(subst(t1,e,x),subst(t2,e,x))
        case IfThenElse(t0,t1,t2) =>
          IfThenElse(subst(t0,e,x),subst(t1,e,x),subst(t2,e,x))

        // Strings
        case Str(s) => Str(s)
        case Length(t0) => Length(subst(t0,e,x))
        case Index(t1,t2) => Index(subst(t1,e,x),subst(t2,e,x))
        case Concat(t1,t2) => Concat(subst(t1,e,x),subst(t2,e,x))

        // Variables and let-binding
        case Var(y) =>
          if (x == y) {
            e
          } else {
            Var(y)
          }
        case Let(y,t1,t2) => {
          val z = generator.genVar(y);
          Let(z,subst(t1,e,x),subst(swap(t2,y,z),e,x))
        }

        // Annotations
        case Anno(t0,ty) => Anno(subst(t0,e,x),ty)

        // Functions
        case Lambda(y,t0) => {
          val z = generator.genVar(y);
          Lambda(z,subst(swap(t0,y,z),e,x))
        }
        case Apply(t1,t2) => Apply(subst(t1,e,x),subst(t2,e,x))
        case Rec(f,y,t0) => {
          val g = generator.genVar(f);
          val z = generator.genVar(y);
          Rec(g,z,subst(swap(swap(t0,f,g),y,z),e,x))
        }

        // Pairing
        case Pair(t1,t2) => Pair(subst(t1,e,x),subst(t2,e,x))
        case First(t0) => First(subst(t0,e,x))
        case Second(t0) => Second(subst(t0,e,x))

        // Records
        case Record(xs) => Record(xs.map((l_n, e_n) => (l_n, subst(e_n, e, x))))
        case Proj(t0,l) => Proj(subst(t0,e,x),l)

        // Variants
        case Variant(l,t0) => Variant(l,subst(t0,e,x))
        case Case(t0,cs) => Case(subst(t0,e,x), cs.map((l_n, entry_n) => { 
          entry_n match {
            case (x_n, t_n) => (l_n, (x_n, subst(t_n, e, x)))
          }
        }))

        // Bags
        case Bag(ts) => Bag(ts.map(t => subst(t,e,x)))
        case FlatMap(t1,t2) => FlatMap(subst(t1,e,x),subst(t2,e,x))
        case When(t1,t2) => When(subst(t1,e,x),subst(t2,e,x))
        case Count(t1,t2) => Count(subst(t1,e,x),subst(t2,e,x))
        case Sum(t1,t2) => Sum(subst(t1,e,x),subst(t2,e,x))
        case Diff(t1,t2) => Diff(subst(t1,e,x),subst(t2,e,x))

        // Syntactic sugars
        case LetPair(y1,y2,t1,t2) => {
          val y1z = generator.genVar(y1);
          val y2z = generator.genVar(y2);
          LetPair(y1z,y2z,subst(t1,e,x),
            subst(swap(swap(t2,y1z,y1), y2z, y2), e,x))
        }
        case LetFun(f,ty,y,t1,t2) => {
          val fz = generator.genVar(f);
          val yz = generator.genVar(y);
          LetFun(fz,ty,yz,subst(swap(t1,yz,y),e,x),
            subst(swap(t2,fz,f), e,x))
        }
        case LetRec(f,ty,y,t1,t2) => {
          val fz = generator.genVar(f);
          val yz = generator.genVar(y);
          LetRec(fz,ty,yz,subst(swap(swap(t1,fz,f),yz,y),e,x),
            subst(swap(t2,fz,f), e,x))
        }
        case LetRecord(xs,t1,t2) => {
          val ys = xs.map((l_n,x_n) =>
            val y_n = generator.freshVar();
            (l_n, y_n)
          )
          LetRecord(ys,subst(t1,e,x),Record(xs.map((l_n,x_n) => (l_n, swap(t2, x_n, ys(l_n))))))
        }
        case Comprehension(t1,ts) => Comprehension(subst(t1,e,x), ts.map(t => subst(t,e,x)))
        case Bind(y,t0) => {
          val z = generator.genVar(y);
          Bind(z,subst(swap(t0,y,z),e,x))
        }
        case Guard(t0) => Guard(subst(t0,e,x))
        case CLet(y,t0) => {
          val z = generator.genVar(y);
          CLet(z,subst(swap(t0,y,z),e,x))
        }

        // Value
        case _ => t
      }
    }
  }
  import SubstExpr.{subst}


  
  // ======================================================================
  // Desugaring and Type Erasure
  // ======================================================================

    ////////////////////
    // EXERCISE 5     //
    ////////////////////
  def desugar(e: Expr): Expr = e match {
    // Value
    case v: Value =>
      sys.error("desugar: there shouldn't be any values here")

    // Arithmetic expressions
    case Plus(e1,e2) => Plus(desugar(e1),desugar(e2))
    case Minus(e1,e2) => Minus(desugar(e1),desugar(e2))
    case Times(e1,e2) => Times(desugar(e1),desugar(e2))

    // Booleans
    case Eq(e1,e2) => Eq(desugar(e1),desugar(e2))
    case Less(e1,e2) => Less(desugar(e1),desugar(e2))
    case IfThenElse(cond,e1,e2) => IfThenElse(desugar(cond),desugar(e1),desugar(e2))

    // Strings
    case Length(e) => Length(desugar(e))
    case Index(e1,e2) => Index(desugar(e1),desugar(e2))
    case Concat(e1,e2) => Concat(desugar(e1),desugar(e2))

    // Variables and let-binding
    case Let(x,e1,e2) => Let(x,desugar(e1),desugar(e2))
    
    // Annotations
    case Anno(e,ty) => desugar(e)

    // Functions
    case Lambda(x,e) => Lambda(x,desugar(e))
    case Apply(e1,e2) => Apply(desugar(e1),desugar(e2))
    case Rec(f,x,e) => Rec(f,x,desugar(e))

    // Pairing
    case Pair(e1,e2) => Pair(desugar(e1),desugar(e2))
    case First(e) => First(desugar(e))
    case Second(e) => Second(desugar(e))

    // Records 
    case Record(es) => Record(es.map((l,e) => (l,desugar(e))))
    case Proj(e,l) => Proj(desugar(e),l)

    // Variants
    case Variant(l,e) => Variant(l,desugar(e))
    case Case(e,cls) => 
      Case(desugar(e),cls.map((l,x_e) => 
        val (x,e) = x_e
        (l,(x,desugar(e)))))

    // Bags
    case Bag(es) => Bag(es.map(e => desugar(e)))
    case FlatMap(e1,e2) => FlatMap(desugar(e1),desugar(e2))
    case When(e1,e2) => When(desugar(e1),desugar(e2))
    case Count(e1,e2) => Count(desugar(e1),desugar(e2))
    case Sum(e1,e2) => Sum(desugar(e1),desugar(e2))
    case Diff(e1,e2) => Diff(desugar(e1),desugar(e2))

    // Syntactic sugars
    case LetPair(x,y,e1,e2) => {
      val p = generator.genVar("p")
      Let(p,desugar(e1),subst(subst(desugar(e2),First(Var(p)),x),Second(Var(p)),y))
    }
    case LetFun(f,ty,arg,e1,e2) =>
      Let(f,Lambda(arg,desugar(e1)),desugar(e2))
    case LetRec(f,ty,arg,e1,e2) => {
      Let(f,Rec(f,arg,desugar(e1)),desugar(e2))
    }
    case LetRecord(xs,e1,e2) => {
      val r = generator.genVar("r")
      Let(r,desugar(e1), Record(xs.map((l_n,x_n) => (l_n,subst(desugar(e2),Proj(Var(r),l_n),x_n)))))
    }
    case Comprehension(e,es) => {
      es match {
        case Nil => Bag(List(desugar(e)))
        case _ => es.head match {
          case Bind(x,e_prime) => FlatMap(desugar(e_prime),Lambda(x,Comprehension(e,es.tail)))
          case Guard(e_prime) => When(desugar(e_prime),Comprehension(e,es.tail))
          case CLet(x,e_prime) => Let(x,desugar(e_prime),Comprehension(e,es.tail))
          case _ => sys.error("desugar: invalid comprehension")
        }
      }
    }
    case e => e
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

    // Unit
    case Unit => UnitV

    // Arithmetic expressions
    case Num(n) => NumV(n)
    case Plus(e1,e2) => Value.add(eval(e1),eval(e2))
    case Minus(e1,e2) => Value.subtract(eval(e1),eval(e2))
    case Times(e1,e2) => Value.multiply(eval(e1),eval(e2))

    // Booleans
    case Bool(b) => BoolV(b)
    case Eq(e1,e2) => Value.eq(eval(e1),eval(e2))
    case Less(e1,e2) => Value.less(eval(e1),eval(e2))
    case IfThenElse(cond,e1,e2) => eval(cond) match
      case BoolV(true) => eval(e1)
      case BoolV(false) => eval(e2)
      case _ => sys.error("eval: condition is not a boolean")

    // Strings
    case Str(s) => StringV(s)
    case Length(e) => Value.length(eval(e))
    case Index(e1,e2) => Value.index(eval(e1),eval(e2))
    case Concat(e1,e2) => Value.concat(eval(e1),eval(e2))

    // Variables and let-binding
    case Var(x) => sys.error("eval: free variable")
    case Let(x,e1,e2) => eval(SubstExpr.subst(e2, e1, x))

    // Annotations
    case Anno(e,ty) => eval(e)

    // Functions
    case Lambda(x,e) => FunV(x,e)
    case Apply(e1,e2) => eval(e1) match
      case FunV(x,e) => eval(SubstExpr.subst(e, eval(e2), x))
      case RecV(f,x,e) => eval(SubstExpr.subst(SubstExpr.subst(e, eval(e1), f), eval(e2), x))
      case _ => sys.error("eval: application of non-function")
    case Rec(f,x,e) => RecV(f,x,e)

    // Pairing
    case Pair(e1,e2) => PairV(eval(e1),eval(e2))
    case First(e) => eval(e) match
      case PairV(v1,v2) => v1
      case _ => sys.error("eval: first of non-pair")
    case Second(e) => eval(e) match
      case PairV(v1,v2) => v2
      case _ => sys.error("eval: second of non-pair")
    
    // Records
    case Record(es) => RecordV(es.map((l,e) => (l,eval(e))))
    case Proj(e,l) => eval(e) match
      case RecordV(es) => es(l)
      case _ => sys.error("eval: projection of non-record")
    
    // Variants
    case Variant(l,e) => VariantV(l,eval(e))
    case Case(e,cls) => eval(e) match
      case VariantV(l,v) => cls(l) match
        case (x,e) => eval(SubstExpr.subst(e, v, x))
      case _ => sys.error("eval: case of non-variant")
    
    // Bags
    case Bag(es) => BagV(BagImpl.fromList(es.map(e => eval(e))))
    case FlatMap(e1,e2) =>  (eval(e1), eval(e2)) match {
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

    case fail => sys.error("eval: todo - " + fail)
  }

  // 

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
        print("Type Checking...\n");
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
