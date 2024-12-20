package Assign3.Typer

import Assign3.Syntax.Syntax._
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
    // BEGIN ANSWER
    case (TyUnit, TyUnit) => true
    case (TyInt, TyInt) => true
    case (TyBool, TyBool) => true
    case (TyString, TyString) => true
    case (TyPair(ty11, ty12), TyPair(ty21, ty22)) =>
      subtype(ty11, ty21) && subtype(ty12, ty22)
    case (TyFun(ty11, ty12), TyFun(ty21, ty22)) =>
      subtype(ty21, ty11) && subtype(ty12, ty22)
    case (TyRecord(tys1), TyRecord(tys2)) =>
      // tys2 should be smaller than tys1
      tys2.forall((l, ty2) => tys1.get(l) match {
        case None => false
        case Some(ty1) => subtype(ty1, ty2)
      })
    case (TyVariant(tys1), TyVariant(tys2)) =>
      // tys1 should be smaller than tys2
      tys1.forall((l, ty1) => tys2.get(l) match {
        case None => false
        case Some(ty2) => subtype(ty1, ty2)
      })
    case (TyBag(ty1), TyBag(ty2)) =>
      subtype(ty1, ty2)
    case _ => false
    // END ANSWER
  }


    ////////////////////
    // EXERCISE 3     //
    ////////////////////
  // checking mode
  def tyCheck(ctx: Env, e: Expr, ty: Type): Unit = (e, ty) match {
    // BEGIN ANSWER
    // functions only have checking mode
    case (Lambda(x, e), TyFun(ty1, ty2)) =>
      tyCheck(ctx + (x -> ty1), e, ty2)
    case (Rec(f, x, e), _) => ty match {
      case TyFun(ty1, ty2) =>
        tyCheck(ctx + (f -> ty) + (x -> ty1), e, ty2)
      case _ => sys.error("tyCheck: expected (polymorphic) function type")
    }

    // some bag operations have checking mode
    case (FlatMap(e1, e2), TyBag(ty)) => tyInfer(ctx, e1) match {
      case TyBag(ty1) => tyCheck(ctx, e2, TyFun(ty1, TyBag(ty)))
      case _ => sys.error("tyInfer: flatMap expects bag type")
    }
    case (When(e1, e2), TyBag(ty)) =>
      tyCheck(ctx, e1, TyBool)
      tyCheck(ctx, e2, TyBag(ty))
    case (Sum(e1, e2), TyBag(ty)) =>
      tyCheck(ctx, e1, TyBag(ty))
      tyCheck(ctx, e2, TyBag(ty))
    case (Diff(e1, e2), TyBag(ty)) =>
      if (!isEqType(ty)) {
        sys.error("tyInfer: difference expects bags of elements of equality type, not " ++ ty.toString)
      }
      tyCheck(ctx, e1, TyBag(ty))
      tyCheck(ctx, e2, TyBag(ty))

    case (Bag(es), TyBag(ty)) =>
      es.foreach(e => tyCheck(ctx, e, ty))
    case(Comprehension(e, es), TyBag(ty)) => es match {
      case Nil => tyCheck(ctx, e, ty)
      case p::oth => p match {
        case Bind(x, e1) => tyInfer(ctx, e1) match {
          case TyBag(ty1) =>
            tyCheck(ctx + (x -> ty1), Comprehension(e, oth), TyBag(ty))
          case _ => sys.error("tyCheck: expected bag type")
        }
        case Guard(e1) =>
          tyCheck(ctx, e1, TyBool)
          tyCheck(ctx, Comprehension(e, oth), TyBag(ty))
        case CLet(x, e1) =>
          val ty1 = tyInfer(ctx, e1)
          tyCheck(ctx + (x -> ty1), Comprehension(e, oth), TyBag(ty))
        case _ =>
          sys.error("tyCheck: expected comprehension clause")
      }
    }

 
    // pairs, records, and variants have both checking and inference modes
    case (Pair(e1, e2), TyPair(ty1, ty2)) =>
      tyCheck(ctx, e1, ty1)
      tyCheck(ctx, e2, ty2)
    case (Record(es), TyRecord(tys)) =>
      tys.foreach((l, ty) => es.get(l) match { // subtyping also appears here
        case None => sys.error("tyCheck: label " ++ l ++ " not found in the record type")
        case Some(e) => tyCheck(ctx, e, ty)
      })
      es.foreach((l, e) => tys.get(l) match {
        case None =>
          tyInfer(ctx, e)
          ()
        case Some(ty) => ()
      })
    case (Variant(l, e), TyVariant(tys)) =>
      tys.get(l) match {
        case None => sys.error("tyCheck: label " ++ l ++ " not found in the variant type")
        case Some(ty) => tyCheck(ctx, e, ty)
      }

    // projection has checking mode
    case (Proj(e, l), ty) => tyCheck(ctx, e, TyRecord(ListMap(l -> ty)))

    // constructs with tailing expressions (such as let and case) have both modes
    case (Let(x, e1, e2), ty2) =>
      val ty = tyInfer(ctx, e1)
      tyCheck(ctx + (x -> ty), e2, ty2)
    case (IfThenElse(e, e1, e2), ty) =>
      tyCheck(ctx, e, TyBool)
      tyCheck(ctx, e1, ty)
      tyCheck(ctx, e2, ty)
    case (Case(e, cls), ty) => tyInfer(ctx, e) match {
      case TyVariant(tys) =>
        tys.foreach((l, _) => cls.get(l) match {
          case None => sys.error("tyCheck: label " ++ l ++ " not found in the case clause")
          case Some((_, _)) => ()
        })
        cls.foreach(entry =>
          val (l, (x, e)) = entry
          tys.get(l) match {
            case None => sys.error("tyCheck: label " ++ l ++ " not found in the variant type")
            case Some(argty) => tyCheck(ctx + (x -> argty), e, ty)
          })
      case _ => sys.error("tyInfer: expected variant type")
    }
    // Syntactic sugars
    case (LetPair(x, y, e1, e2), input) => tyInfer(ctx, e1) match {
      case TyPair(ty1, ty2) => tyCheck(ctx + (x -> ty1) + (y -> ty2), e2, input)
      case _ => sys.error("tyInfer: expected pair type")
    }
    case (LetFun(f, ty, x, e1, e2), input) => ty match {
      case TyFun(ty1, ty2) =>
        tyCheck(ctx + (x -> ty1), e1, ty2)
        tyCheck(ctx + (f -> ty), e2, input)
      case _ => sys.error("tyInfer: expected function type")
    }
    case (LetRec(f, ty, x, e1, e2), input) => ty match {
      case TyFun(ty1, ty2) =>
        tyCheck(ctx + (f -> ty) + (x -> ty1), e1, ty2)
        tyCheck(ctx + (f -> ty), e2, input)
      case _ => sys.error("tyInfer: expected (polymorphic) function type")
    }
    case (LetRecord(xs, e1, e2), input) => tyInfer(ctx, e1) match {
      case TyRecord(tys) =>
        val newctx = xs.foldLeft(ctx)((curctx, lx) => 
          val (label, name) = lx
          tys.get(label) match {
            case Some(ty) => curctx + (name -> ty)
            case None => sys.error("tyInfer: label " ++ label ++ " not found in the record type")
          })
        tyCheck(newctx, e2, input)
      case _ => sys.error("tyInfer: expected record type")
    }


    // We only use switch if there is no other more specialised checking rule
    case _ =>
      val ty1 = tyInfer(ctx, e)
      if subtype(ty1, ty) then ()
      else sys.error("tyCheck: fail for " ++ ty1.toString() ++ " and " ++ ty.toString())
    // END ANSWER
  }

  // inference mode
  def tyInfer(ctx: Env, e: Expr): Type = e match {
    // Value
    case v:Value => sys.error("tyCheck: values should not appear at this stage")

    // Arithmetic
    case Unit => (TyUnit)
    case Num(_) => (TyInt)
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
    case Bool(_) => (TyBool)
    case Eq(e1, e2) =>
      val ty = tyInfer(ctx,e1)
      if (!isEqType(ty)) {
        sys.error("tyCheck: cannot test equality of type " ++ ty.toString)
      }
      tyCheck(ctx, e2, ty)
      (TyBool)
    case Less(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyBool)
    case IfThenElse(e, e1, e2) =>
      tyCheck(ctx, e, TyBool)
      val ty = tyInfer(ctx,e1)
      tyCheck(ctx, e2, ty)
      (ty)

    // Strings
    case Str(s) => (TyString)
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

    // BEGIN ANSWER
    // Variables and let-binding
    case Var(x) => ctx(x)
    case Let(x, e1, e2) =>
      val ty = tyInfer(ctx, e1)
      tyInfer(ctx + (x -> ty), e2)

    // Functions
    case Lambda(x, e) =>
      sys.error("tyInfer: cannot infer function types")
    case Apply(e1, e2) => tyInfer(ctx, e1) match {
      case TyFun(ty1, ty2) =>
        tyCheck(ctx, e2, ty1)
        ty2
      case _ => sys.error("tyInfer: expected function type")
    }
    case Rec(f, x, e) =>
      sys.error("tyInfer: cannot infer function types")

    // Annotations
    case Anno(e, ty) =>
      tyCheck(ctx, e, ty)
      ty


    // Pairing
    case Pair(e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      val ty2 = tyInfer(ctx, e2)
      TyPair(ty1, ty2)
    case First(e) => tyInfer(ctx, e) match {
      case TyPair(ty1, _) => ty1
      case _ => sys.error("tyInfer: expected pair type")
    }
    case Second(e) => tyInfer(ctx, e) match {
      case TyPair(_, ty2) => ty2
      case _ => sys.error("tyInfer: expected pair type")
    }

    // Records
    case Record(es) =>
      val tys = es.map((l, e) => (l, tyInfer(ctx, e)))
      TyRecord(tys)
    case Proj(e, l) => tyInfer(ctx, e) match {
      case TyRecord(tys) => tys.get(l) match
        case None => sys.error("tyOf: label" ++ l ++ " not found in the record")
        case Some(ty) => ty
      case _ => sys.error("tyOf: expected record type")
    }

    // Variants
    case Variant(l, e) => TyVariant(ListMap(l -> tyInfer(ctx, e)))
    case Case(e, cls) => tyInfer(ctx, e) match {
      case TyVariant(tys) =>
        tys.foreach((l, _) => cls.get(l) match {
          case None => sys.error("tyCheck: label " ++ l ++ " not found in the case clause")
          case Some((_, _)) => ()
        })
        def help(ty: Option[Type], entry: (Label, (Variable, Expr))): Option[Type] =
          val (label, (x, e)) = entry
          tys.get(label) match {
            case None =>
              sys.error("tyInfer: label " ++ label ++ " not found in the variant type")
            case Some(argty) => ty match {
              case None => Some(tyInfer(ctx + (x -> argty), e))
              case Some(ty) =>
                tyCheck(ctx + (x -> argty), e, ty)
                Some(ty)
            }
          }
        cls.foldLeft(None)(help) match {
          case None => sys.error("tyInfer: empty case clause")
          case Some(ty) => ty
        }
      case _ => sys.error("tyInfer: expected variant type")
    }

    // Bags
    case Bag(ebag) => ebag match {
      case Nil => sys.error("tyInfer: cannot infer empty bag")
      case e::es => 
        val ty = tyInfer(ctx, e)
        es.foreach(e => tyCheck(ctx, e, ty))
        TyBag(ty)
    }
    case FlatMap(e1, e2) => tyInfer(ctx, e1) match {
      case TyBag(ty1) => tyInfer(ctx, e2) match {
        case TyFun(ty11, TyBag(ty2)) =>
          if ty1 == ty11 then TyBag(ty2) else sys.error("tyInfer: flatMap mismatch")
        case _ => sys.error("tyInfer: flatMap expects function type")
      }
      case _ => sys.error("tyInfer: flatMap expects bag type")
    }
    case When(e1, e2) =>
      tyCheck(ctx, e1, TyBool)
      tyInfer(ctx, e2) match {
        case TyBag(ty) => TyBag(ty)
        case ty => sys.error("tyInfer: when expects bag for second argument, instead of " + ty)
    }
    case Sum(e1, e2) => tyInfer(ctx, e1) match {
      case TyBag(ty) =>
        tyCheck(ctx, e2, TyBag(ty))
        TyBag(ty)
      case _ => sys.error("tyInfer: sum expects bag type")
    }
    case Diff(e1, e2) => tyInfer(ctx, e1) match {
      case TyBag(ty) =>
        if (!isEqType(ty)) {
          sys.error("tyInfer: difference expects bags of elements of equality type, not " ++ ty.toString)
        }
        tyCheck(ctx, e2, TyBag(ty))
        TyBag(ty)
      case _ => sys.error("tyInfer: diff expects bag type")
    }

    case Comprehension(e, es) => es match {
      case Nil => TyBag(tyInfer(ctx, e))
      case p::oth => p match {
        case Bind(x, e1) => tyInfer(ctx, e1) match {
          case TyBag(ty1) =>
            tyInfer(ctx + (x -> ty1), Comprehension(e, oth))
          case _ => sys.error("tyInfer: comprehension expects bag type")
        }
        case Guard(e1) =>
          tyCheck(ctx, e1, TyBool)
          tyInfer(ctx, Comprehension(e, oth))
        case CLet(x, e1) =>
          val ty1 = tyInfer(ctx, e1)
          tyInfer(ctx + (x -> ty1), Comprehension(e, oth))
        case _ =>
          sys.error("tyInfer: expected comprehension clause")
      }
    }
    case Count(e1, e2) => tyInfer(ctx, e1) match {
      case TyBag(ty) =>
        if (!isEqType(ty)) {
          sys.error("tyInfer: expected equality type in count, not " ++ ty.toString)
        }
        tyCheck(ctx, e2, ty)
        TyInt
      case _ => sys.error("tyInfer: count expects bag type")
    }

    // Syntactic sugars
    case LetPair(x, y, e1, e2) => tyInfer(ctx, e1) match {
      case TyPair(ty1, ty2) => tyInfer(ctx + (x -> ty1) + (y -> ty2), e2)
      case _ => sys.error("tyInfer: expected pair type")
    }
    case LetFun(f, ty, x, e1, e2) => ty match {
      case TyFun(ty1, ty2) =>
        tyCheck(ctx + (x -> ty1), e1, ty2)
        tyInfer(ctx + (f -> ty), e2)
      case _ => sys.error("tyInfer: expected function type")
    }
    case LetRec(f, ty, x, e1, e2) => ty match {
      case TyFun(ty1, ty2) =>
        tyCheck(ctx + (f -> ty) + (x -> ty1), e1, ty2)
        tyInfer(ctx + (f -> ty), e2)
      case _ => sys.error("tyInfer: expected (polymorphic) function type")
    }
    case LetRecord(xs, e1, e2) => tyInfer(ctx, e1) match {
      case TyRecord(tys) =>
        val newctx = xs.foldLeft(ctx)((curctx, lx) => 
          val (label, name) = lx
          tys.get(label) match {
            case Some(ty) => curctx + (name -> ty)
            case None => sys.error("tyInfer: label " ++ label ++ " not found in the record type")
          })
        tyInfer(newctx, e2)
      case _ => sys.error("tyInfer: expected record type")
    }
    // END ANSWER
    case Bind(_, _) => sys.error("tyInfer: unexpected bind")
    case Guard(_) => sys.error("tyInfer: unexpected guard")
    case CLet(_, _) => sys.error("tyInfer: unexpected CLet")
  }
}
