package FrogInterpreter

import FrogInterpreter.Syntax._
import scala.collection.immutable.ListMap

object Typer {
  // ======================================================================
  // Part 1: Typechecking
  // ======================================================================

  val generator = SymGenerator()


  def isEqType(ty: Type): Boolean = ty match {
    case TyUnit | TyInt | TyString | TyBool => true
    case TyVariant(tys) => tys.forall((l, ty0) => isEqType(ty0))
    case TyPair(ty1, ty2) => isEqType(ty1) && isEqType(ty2)
    case _ => false
  }

    ////////////////////
    // EXERCISE 2     //
    ////////////////////
  def subtype(ty1: Type, ty2: Type): Boolean = (ty1, ty2) match {
    case (ty1, ty2) if ty1 == ty2 => true
    case (TyPair(ty1, ty2), TyPair(ty3, ty4)) => subtype(ty1, ty3) && subtype(ty2, ty4)
    case (TyFun(ty1, ty2), TyFun(ty3, ty4)) => subtype(ty3, ty1) && subtype(ty2, ty4)
    case (TyRecord(tys1), TyRecord(tys2)) => 
      tys1.forall((l, ty1) => tys2.get(l) match {
        case None => false
        case Some(ty2) => subtype(ty1, ty2)
      })
    case (TyVariant(tys1), TyVariant(tys2)) => 
      tys2.forall((l, ty2) => tys1.get(l) match {
        case None => false
        case Some(ty1) => subtype(ty1, ty2)
      })
    case (TyBag(ty1), TyBag(ty2)) => subtype(ty1, ty2)
    case _ => false
  }

    ////////////////////
    // EXERCISE 3     //
    ////////////////////
  // checking mode
  def tyCheck(ctx: Env, e: Expr, ty: Type): Unit = (e, ty) match {
    // Conditionals
    case (IfThenElse(e, e1, e2), ty) =>
      println("\n     tyCheck:  IfThenElse(" + e + ", " + e1 + ", " + e2 + "), " + ty)
      tyCheck(ctx, e, TyBool)
      tyCheck(ctx, e1, ty)
      tyCheck(ctx, e2, ty)

    // Variables and let-binding
    case (Let(x, e1, e2), ty2) =>
      println("\n     tyCheck:  Let(" + x + ", " + e1 + ", " + e2 + "), " + ty)
      val ty1 = tyInfer(ctx, e1)
      println("       - tyInfer: inferred " + e1 + " : " + ty1)
      println("       - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ")")
      tyCheck(ctx + (x -> ty1), e2, ty2)

    // Functions
    case (Lambda(x, e), TyFun(ty1, ty2)) =>
      println("\n     tyCheck: Lambda(" + x + ", " + e + "), " + TyFun(ty1, ty2))
      println("        - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ")")
      tyCheck(ctx + (x -> ty1), e, ty2)

    case (Rec(f, x, e), TyFun(ty1, ty2)) =>
      println("\n     tyCheck: Rec(" + f + ", " + x + ", " + e + "), " + TyFun(ty1, ty2))
      println("        - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ") and (" + f + " : " + ty1 + " -> " + ty2 + ")")
      tyCheck(ctx + (f -> TyFun(ty1, ty2)) + (x -> ty1), e, ty2)

    // Pairing
    // pairs have both checking and inference modes
    case (Pair(e1, e2), TyPair(ty1, ty2)) =>
      println("\n     tyCheck: Pair(" + e1 + ", " + e2 + "), " + TyPair(ty1, ty2))
      tyCheck(ctx, e1, ty1)
      tyCheck(ctx, e2, ty2)

    // Records
    case (Record(es), ty) =>
      ty match {
        case TyRecord(tys) => 
          println("\n     tyCheck: Record(" + es + "), " + TyRecord(tys))
          es.foreach((l, e) => tys.get(l) match {
            case None => ()
            case Some(ty) => tyCheck(ctx, e, ty)
          })
        case _ => sys.error("tyCheck: expected record type")
      }

    case (Proj(e, l_j), ty_j) => 
      println("\n     tyCheck: Proj(" + e + ", " + l_j + "), " + ty_j)
      e match {
        case Var(x) => 
          ctx.get(x) match {
            case None => sys.error("tyCheck: unbound variable " ++ x)
            case Some(TyRecord(tys)) => tys.get(l_j) match {
              case None => sys.error("tyCheck: unexpected field " ++ l_j)
              case Some(_) => () // Pass if we find it - no need to check type
            }
            case _ => sys.error("tyCheck: expected record type")
          }
        // This is definitely a hack
        case Proj(e_prime, l) =>
          tyCheck(ctx, e_prime, TyRecord(ListMap(l -> TyRecord(ListMap(l_j -> ty_j)))))
        case _ => sys.error("tyCheck: " + e + " must be a variable or record projection")
      }

    // Variants
    case (Variant(l, e), TyVariant(tys)) =>
      println("\n     tyCheck: Variant(" + l + ", " + e + "), " + TyVariant(tys))
      tys.get(l) match {
        case None => sys.error("tyCheck: unexpected label " ++ l)
        case Some(ty) => tyCheck(ctx, e, ty)
      }

    case (Case(e, cls), ty) => 
      println("\n     tyCheck: Case(" + e + ", " + cls + "), " + ty)
      val var_ty = tyInfer(ctx, e)
      println("       - tyInfer: inferred " + e + " : " + var_ty)
      var_ty match {
        case TyVariant(tys) =>
          cls.foreach((l_n, xe_n) => {
            val (x_n, e_n) = xe_n
            println(l_n + ", " + x_n + ", " + e_n)
            val ty_n = tys.get(l_n) match {
              case None => sys.error("tyCheck: unexpected label " ++ l_n)
              case Some(ty_prime) => ty_prime
            }
            println("       - tyCheck: updating context " + ctx + " with (" + x_n + " : " + ty + ")")
            tyCheck(ctx + (x_n -> ty_n), e_n, ty)
          })
        case _ => sys.error("tyCheck: expected variant type")
      }
      

    // Bags
    case (Bag(es), TyBag(ty)) =>
      println("\n     tyCheck: Bag(" + es + "), " + TyBag(ty))
      es.foreach(e => tyCheck(ctx, e, ty))

    case (FlatMap(e1, e2), TyBag(ty2)) =>
      println("\n     tyCheck: FlatMap(" + e1 + ", " + e2 + "), " + TyBag(ty2))
      val ty1_bag = tyInfer(ctx, e1)
      println("       - tyInfer: inferred " + e1 + " : " + ty1_bag)
      ty1_bag match {
        case TyBag(ty1) => 
          tyCheck(ctx, e2, TyFun(ty1, TyBag(ty2)))
        case _ => sys.error("tyCheck: expected bag type")
      }

    case (When(e1, e2), ty) =>
      println("\n     tyCheck: When(" + e1 + ", " + e2 + "), " + ty)
      tyCheck(ctx, e1, TyBool)
      tyCheck(ctx, e2, ty)

    case (Sum(e1, e2), TyBag(ty)) =>
      println("\n     tyCheck: Sum(" + e1 + ", " + e2 + "), " + TyBag(ty))
      tyCheck(ctx, e1, TyBag(ty))
      tyCheck(ctx, e2, TyBag(ty))

    case (Diff(e1, e2), TyBag(ty)) =>
      println("\n     tyCheck: Diff(" + e1 + ", " + e2 + "), " + TyBag(ty))
      tyCheck(ctx, e1, TyBag(ty))
      tyCheck(ctx, e2, TyBag(ty))
      if (!isEqType(ty)) {
        sys.error("tyCheck: cannot test equality of type " ++ ty.toString)
      }

    // Syntactic sugars
    case (Comprehension(e, es), TyBag(ty)) => 
      println("\n     tyCheck: Comprehension(" + e + ", " + es + "), " + TyBag(ty))
      (e, es) match {
        case (e, Nil) => 
          (tyCheck(ctx, e, ty))
        case (e, es) => 
          es.head match {
            case Guard(e_prime) => 
              tyCheck(ctx, e_prime, TyBool)
              println("       - tyCheck: comprehension guard is a boolean")
              tyCheck(ctx, Comprehension(e, es.tail), TyBag(ty))
            case Bind(x, e_prime) => 
              val ty_bag = tyInfer(ctx, e_prime)
              println("       - tyInfer: inferred " + e_prime + " : " + ty_bag)
              ty_bag match {
                  case TyBag(ty_prime) =>
                    println("       - tyCheck: updating context " + ctx + " with (" + x + " : " + ty_prime + ")")
                    tyCheck(ctx + (x -> ty_prime), Comprehension(e, es.tail), TyBag(ty))
                  case _ => sys.error("tyCheck: expected bag type")
              }
              
            case CLet(x, e_prime) => 
              val ty_prime = tyInfer(ctx, e_prime)
              println("       - tyInfer: inferred " + e_prime + " : " + ty_prime)
              println("       - tyCheck: updating context " + ctx + " with (" + x + " : " + ty_prime + ")")
              tyCheck(ctx + (x -> ty_prime), Comprehension(e, es.tail), TyBag(ty))
            case _ => sys.error("tyCheck: expected bind, guard, or comprehension let")
          }
      }

    case (LetFun(f, TyFun(ty1, ty2), x, e1, e2), ty) => 
      println("\n     tyCheck: LetFun(" + f + ", " + TyFun(ty1, ty2) + ", " + x + ", " + e1 + ", " + e2 + "), " + ty)
      println("        - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ")")
      tyCheck(ctx + (x -> ty1), e1, ty2)
      println("\n      - tyCheck: updating context " + ctx + " with (" + f + " : " + ty1 + " -> " + ty2 + ")")
      tyCheck(ctx + (f -> TyFun(ty1, ty2)), e2, ty)
    

    case (LetRec(f, TyFun(ty1, ty2), x, e1, e2), ty) => 
      println("\n     tyCheck: LetRec(" + f + ", " + TyFun(ty1, ty2) + ", " + x + ", " + e1 + ", " + e2 + "), " + ty)
      println("        - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ") and (" + f + " : " + ty1 + " -> " + ty2 + ")")
      tyCheck(ctx + (f -> TyFun(ty1, ty2)) + (x -> ty1), e1, ty2)
      println("        - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ") and (" + f + " : " + ty1 + " -> " + ty2 + ")")
      tyCheck(ctx + (f -> TyFun(ty1, ty2)), e2, ty)
  

    case (LetPair(x, y, e1, e2), TyPair(ty1, ty2)) =>
      println("       tyCheck: LetPair(" + x + ", " + y + ", " + e1 + ", " + e2 + "), " + TyPair(ty1, ty2))
      tyCheck(ctx, e1, TyPair(ty1, ty2))
      println("        - tyCheck: updating context " + ctx + " with (" + x + " : " + ty1 + ") and (" + y + " : " + ty2 + ")")
      tyCheck(ctx + (x -> ty1) + (y -> ty2), e2, ty)
    
    case (LetRecord(xs, e1, e2), ty) => 
      println("\n     tyCheck: LetRecord(" + xs + ", " + e1 + ", " + e2 + "), " + ty)
      var tys = tyInfer(ctx, e1) 
      println("       - tyInfer: inferred " + e1 + " : " + tys)
      tys match {
        case TyRecord(tys) =>
          xs.foreach((l, x) => tys.get(l) match {
            case None => sys.error("tyCheck: unexpected field " ++ l)
            case Some(ty) => 
              val updated_ctx = xs.foldLeft(ctx)((acc, pair) => pair match {
                case (l, x) => acc + (x -> tys(l))
              })
              println("       - tyCheck: updating context " + ctx + " with " + updated_ctx)
              tyCheck(ctx ++ updated_ctx, e2, ty)
          })
        case _ => sys.error("tyCheck: expected record type")
      }

    case (e, ty_prime) => 
      println("\n     tyCheck: " + e + " : " + ty_prime)
      val ty1 = tyInfer(ctx, e) 
      println("       - tyInfer: inferred " + e + " : " + ty1)
      ty1 match {
        case ty if subtype(ty_prime, ty) => 
          println("       - tyCheck: " + e + " : " + ty_prime + " is subtype of " + ty)
        case ty => sys.error("tyCheck: expected type " ++ ty_prime.toString ++ " but got " ++ ty.toString)
      }
  }

  // inference mode
  def tyInfer(ctx: Env, e: Expr): Type = e match {
    // Value
    case v:Value => sys.error("tyCheck: values should not appear at this stage")

    // Arithmetic
    case Unit => 
      (TyUnit)
    case Num(_) => 
      (TyInt)
    case Plus(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyInt)
    case Minus(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyInt)
    case Times(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyInt)

    // Booleans
    case Bool(_) => 
      (TyBool)
    case Eq(e1, e2) =>
      val ty = tyInfer(ctx,e1)
      println("       - tyInfer: as part of inference, inferred " + e1 + " : " + ty)
      tyCheck(ctx, e2, ty)

      if (!isEqType(ty)) {
        sys.error("tyCheck: cannot test equality of type " ++ ty.toString)
      }
      (TyBool)
    case Less(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyBool)
    case IfThenElse(e, e1, e2) =>
      tyCheck(ctx, e, TyBool)
      val ty = tyInfer(ctx,e1)
      println("       - tyInfer: as part of inference, inferred " + e1 + " : " + ty)
      tyCheck(ctx, e2, ty)
      (ty)

    // Strings
    case Str(_) => 
      (TyString)
    case Length(e) =>
      tyCheck(ctx, e, TyString)
      (TyInt)
    case Index(e1, e2) =>
      tyCheck(ctx, e1, TyString)
      tyCheck(ctx, e2, TyInt)
      (TyString)
    case Concat(e1, e2) =>
      tyCheck(ctx, e1, TyString)
      tyCheck(ctx, e2, TyString)
      (TyString)
    
    // Variables and let-binding
    case Var(x) => 
      ctx.get(x) match {
        case Some(ty) => (ty)
        case None => sys.error("tyInfer: unbound variable " ++ x)
      }
    case Anno(e, ty) =>
      tyCheck(ctx, e, ty)
      (ty)
    case Let(x, e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      println("       - tyInfer: as part of inference, inferred " + e1 + " : " + ty1)
      println("       - tyInfer: updating context " + ctx + " with (" + x + " : " + ty1 + ")")
      val ty2 = tyInfer(ctx + (x -> ty1), e2)
      println("       - tyInfer: as part of inference, inferred " + e2 + " : " + ty2)
      (ty2)
    case Apply(e1, e2) => 
      val f_ty = tyInfer(ctx, e1)
      println("       - tyInfer: as part of inference, inferred " + e1 + " : " + f_ty)
      f_ty match {
        case TyFun(ty1, ty2) => 
          tyCheck(ctx, e2, ty1)
          (ty2)
        case _ => sys.error("tyInfer: expected function type")
      }

    // Pairing
    case Pair(e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      println("       - tyInfer: as part of inference, inferred " + e1 + " : " + ty1)
      val ty2 = tyInfer(ctx, e2)
      println("       - tyInfer: as part of inference, inferred " + e1 + " : " + ty2)
      (TyPair(ty1, ty2))
    case First(e) => 
      val tys = tyInfer(ctx, e) 
      println("       - tyInfer: as part of inference, inferred " + e + " : " + tys)
      tys match {
        case TyPair(ty1, _) => (ty1)
        case _ => sys.error("tyInfer: expected pair type")
      } 
    case Second(e) =>
      val tys = tyInfer(ctx, e)
      println("       - tyInfer: as part of inference, inferred " + e + " : " + tys)
      tys match {
        case TyPair(_, ty2) => (ty2)
        case _ => sys.error("tyInfer: expected pair type")
      }

    // Records
    case Record(es) => 
      (TyRecord(ListMap(es.mapValues(e => tyInfer(ctx, e)).toSeq*)))
    case Proj(e, l) => 
      val record_ty = tyInfer(ctx, e) 
      println("       - tyInfer: as part of inference, inferred " + e + " : " + record_ty)
      record_ty match {
        case TyRecord(tys) => tys.get(l) match {
          case None => sys.error("tyInfer: missing field " ++ l)
          case Some(ty) => (ty)
        }
        case _ => sys.error("tyInfer: expected record type")
      }

    // Variants
    case Variant(l, e) => 
      val ty = tyInfer(ctx, e)
      println("             - tyInfer: as part of inference, inferred " + e + " : " + ty)
      (TyVariant(ListMap(l -> ty)))

    // Bags
    case Bag(es) => 
      val ty = tyInfer(ctx, es.head)
      println("             - tyInfer: as part of inference, inferred " + es.head + " : " + ty)
      if (!es.forall(e => tyInfer(ctx, e) == ty)) {
        sys.error("tyInfer: inconsistent bag types")
      }
      println("             - tyInfer: as part of inference, inferred " + es + " : " + TyBag(ty))
      (TyBag(ty))
    case FlatMap(e1, e2) =>
      val tys = tyInfer(ctx, e1) 
      println("             - tyInfer: as part of inference, inferred " + e1 + " : " + tys)
      tys match {
        case TyBag(ty_1) => 
          val tys = tyInfer(ctx, e2) 
          println("             - tyInfer: as part of inference, inferred " + e2 + " : " + tys)
          tys match {
            case TyFun(ty_1_prime, TyBag(ty_2)) => 
              if (subtype(ty_1_prime, ty_1)) {
                (TyBag(ty_2))
              } else {
                sys.error("tyInfer: expected type " ++ ty_1.toString ++ " but got " ++ ty_2.toString)
              }
            case _ => sys.error("tyInfer: expected function type")
          }
        case _ => sys.error("tyInfer: expected bag type")
      }
      val ty2 = tyInfer(ctx, e2)
      println("             - tyInfer: as part of inference, inferred " + e2 + " : " + ty2)
      (TyBag(ty2))
    case When(e1, e2) =>
      println("     tyInfer: When(" + e1 + ", " + e2 + ")")
      tyCheck(ctx, e1, TyBool)
      val ty2 = tyInfer(ctx, e2)
      println("             - tyInfer: as part of inference, inferred " + e2 + " : " + ty2)
      (TyBag(ty2))
    case Sum(e1, e2) => 
      val tys = tyInfer(ctx, e1) 
      println("             - tyInfer: as part of inference, inferred " + e1 + " : " + tys)
      tys match {
        case TyBag(ty) => 
          tyCheck(ctx, e2, TyBag(ty))
          (TyBag(ty))
        case _ => sys.error("tyInfer: expected bag type")
      }
    case Diff(e1, e2) =>
      val tys = tyInfer(ctx, e1) 
      println("             - tyInfer: as part of inference, inferred " + e1 + " : " + tys)
      tys match {
        case TyBag(ty) => 
          tyCheck(ctx, e2, TyBag(ty))
          if (!isEqType(ty)) {
            sys.error("tyCheck: cannot test equality of type " ++ ty.toString)
          }
          (TyBag(ty))
        case _ => sys.error("tyInfer: expected bag type")
      }
    case Count(e1, e2) => 
      val tys = tyInfer(ctx, e1) 
      println("             - tyInfer: as part of inference, inferred " + e1 + " : " + tys)
      tys match {
        case TyBag(ty) => 
          tyCheck(ctx, e2, ty)
          if (!isEqType(ty)) {
            sys.error("tyCheck: cannot test equality of type " ++ ty.toString)
          }
          (TyInt)
        case _ => sys.error("tyInfer: expected bag type")
      }

    // Syntactic sugars
    case Comprehension(e, es) => 
      es match {
        case Nil => 
          val ty = tyInfer(ctx, e)
          println("             - tyInfer: as part of inference, inferred " + e + " : " + ty)
          (TyBag(ty))
        case _ => 
          es.head match {
            case Guard(e_prime) => 
              tyCheck(ctx, e_prime, TyBool)
              tyInfer(ctx, Comprehension(e, es.tail))
              
            case Bind(x, e_prime) => 
              val ty_prime = tyInfer(ctx, e_prime)
              println("             - tyInfer: as part of inference, inferred " + e_prime + " : " + ty_prime)
              TyBag(tyInfer(ctx + (x -> ty_prime), Comprehension(e, es.tail)))
            case CLet(x, e_prime) => 
              val ty_prime = tyInfer(ctx, e_prime)
              println("             - tyInfer: as part of inference, inferred " + e_prime + " : " + ty_prime)
              TyBag(tyInfer(ctx + (x -> ty_prime), Comprehension(e, es.tail)))
            case _ => sys.error("tyInfer: expected bind, guard, or comprehension let")
          }
      }

    case LetFun(f, TyFun(ty1, ty2), x, e1, e2) =>
      println("       - tyInfer: updating context " + ctx + " with (" + x + " : " + ty1 + ")")
      tyCheck(ctx + (x -> ty1), e1, ty2)
      val ty = tyInfer(ctx + (x -> ty1) + (f -> TyFun(ty1, ty2)), e2)
      println("             - tyInfer: as part of inference, inferred " + e2 + " : " + ty)
      (ty)

    case LetRec(f, TyFun(ty1, ty2), x, e1, e2) =>
      println("       - tyInfer: updating context " + ctx + " with (" + x + " : " + ty1 + ") and (" + f + " : " + ty1 + " -> " + ty2 + ")")
      tyCheck(ctx + (x -> ty1) + (f -> TyFun(ty1, ty2)), e1, ty2)
      val ty = tyInfer(ctx + (x -> ty1) + (f -> TyFun(ty1, ty2)), e2)
      println("             - tyInfer: as part of inference, inferred " + e2 + " : " + ty)
      (ty)  

    case LetPair(x, y, e1, e2) =>
      val ty_pair = tyInfer(ctx, e1)
      println("             - tyInfer: as part of inference, inferred " + e1 + " : " + ty_pair)
      ty_pair match {
        case TyPair(ty1, ty2) => 
          println("       - tyInfer: updating context " + ctx + " with (" + x + " : " + ty1 + ") and (" + y + " : " + ty2 + ")")
          val ty = tyInfer(ctx + (x -> ty1) + (y -> ty2), e2)
          println("             - tyInfer: as part of inference, inferred " + e2 + " : " + ty)
          (ty)
        case _ => sys.error("tyInfer: expected pair type")
      }

    case LetRecord(xs, e1, e2) =>
      val ty_record = tyInfer(ctx, e1)
      println("             - tyInfer: as part of inference, inferred " + e1 + " : " + ty_record)
      ty_record match {
        case TyRecord(tys) => 
          val updated_ctx = xs.foldLeft(ctx)((acc, pair) => pair match {
            case (l, x) => acc + (x -> tys(l))
          })
          println("       - tyInfer: updating context " + ctx + " with " + updated_ctx)
          val ty = tyInfer(ctx ++ updated_ctx, e2)
          println("             - tyInfer: as part of inference, inferred " + e2 + " : " + ty)
          (ty)
        case _ => sys.error("tyInfer: expected record type")
      }
      
    case _ => 
      println("     tyInfer: e = " + e)
      sys.error("todo: tyInfer(" + ctx + ", " + e + ")")
  }
}