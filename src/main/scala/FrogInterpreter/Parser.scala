package FrogInterpreter

import FrogInterpreter.Syntax.*

import scala.collection.immutable.ListMap
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

/*======================================================================
  The rest of this file is support code, which you should not (and do not
  need to) change.
  ====================================================================== */

class Parser extends StandardTokenParsers with PackratParsers {

  private type P[+A] = PackratParser[A]

  def parseStr(input: String): Expr = {
    phrase(expression)(new lexical.Scanner(input)) match {
      case Success(ast, _) => ast
      case e: NoSuccess => sys.error(e.msg)
    }
  }

  def parseTyStr(input: String): Type = {
    phrase(typ)(new lexical.Scanner(input)) match {
      case Success(ast, _) => ast
      case e: NoSuccess => sys.error(e.msg)
    }
  }

  def parse(input: String): Expr = {
    val source = scala.io.Source.fromFile(input)
    val lines = try source.mkString finally source.close()
    parseStr(lines)
  }

  lexical.reserved ++= List("let", "in", "rec", "if", "then", "else",
    "int", "string", "bool", "true", "false", "fst", "snd", "concat",
    "index", "length", "fun", "ref", "unit", "case", "of", "select", "forall",
    "flatMap", "count", "when", "sig", "sum", "diff"
  )
  lexical.delimiters ++= List("=","*", "\\", "+", "-", "(", ")", "==", ":", ".",
    "->", ",", "<", ">", "<=", ">=", ":=", "!", ";", "[", "]", "{", "}",
    "{|", "|}", "<-", "|", "()"
  )

  private lazy val expression: P[Expr] =
    simpleExpr

  private lazy val lambda: P[Expr] =
    ("\\" ~> ident) ~ ("." ~> expression) ^^ {
      case arg~body => Lambda(arg, body)
    }

  private lazy val rec: P[Expr] =
    ("rec" ~> ident) ~
      ("(" ~> ident <~ ")") ~
      ("." ~> expression) ^^ {
        case recArg~funArg~body =>
          Rec(recArg, funArg, body)
      }

  private lazy val ifExpr: P[Expr] =
    ("if" ~> expression) ~
      ("then" ~> expression) ~
      ("else" ~> expression) ^^ {
        case cond~e1~e2 => IfThenElse(cond,e1,e2)
      }

  private lazy val letExpr: P[Expr] =
    ("let" ~> ident) ~ ("=" ~> expression) ~ ("in" ~> expression) ^^ {
      case binder~e1~e2 => Let(binder,e1,e2)
    }

  private lazy val letFun: P[Expr] =
    ("sig" ~> ident  ~ (":" ~> typ)) ~ ("let" ~ "fun" ~> ident) ~ ("(" ~> ident <~ ")") ~ ("=" ~> expression) ~
      ("in" ~> expression) ^^ {
        case fun1~ty~fun~binder~e1~e2 =>
          if fun1 != fun then sys.error("Function name mismatch")
          else LetFun(fun,ty,binder,e1,e2)
      }

  private lazy val letRec: P[Expr] =
    ("sig" ~> ident  ~ (":" ~> typ)) ~ ("let" ~ "rec" ~> ident) ~ ("(" ~> ident <~ ")") ~ ("=" ~> expression) ~
      ("in" ~> expression) ^^ {
        case fun1~ty~fun~binder~e1~e2 =>
          if fun1 != fun then sys.error("Function name mismatch")
          else LetRec(fun,ty,binder,e1,e2)
      }

  private lazy val letPair: P[Expr] =
    ("let" ~ "(") ~> ident ~ ("," ~> ident <~ ")") ~
      ("=" ~> expression) ~ ("in" ~> expression) ^^ {
        case x~y~e1~e2 => LetPair(x,y,e1,e2)
      }

  private lazy val letRecord: P[Expr] =
    ("let" ~> recordPattern) ~
      ("=" ~> expression) ~ ("in" ~> expression) ^^ {
        case xs~e1~e2 => LetRecord(xs,e1,e2)
      }

  private lazy val caseVariant: P[Expr] =
    ("case" ~> expression) ~ ("of" ~ "{" ~> caseClauses <~ "}") ^^ {
      case e~cls => Case(e, cls)
    }
  
  private lazy val caseClauses: P[Field[(Variable, Expr)]] =
    caseClause ~ "," ~ caseClauses ^^ {
      case cls~_~clss => cls ++ clss
    } |
    caseClause

  private lazy val caseClause: P[Field[(Variable, Expr)]] =
    ident ~ ident ~ "->" ~ expression ^^ {
      case label~name~_~e => ListMap(label -> (name, e))
    }

  private lazy val recordPattern: P[Field[Variable]] =
    "<" ~> recordPatternFields <~ ">" ^^ (es => es) |
    "<" ~ ">" ^^ {
      case _~_ => ListMap()
    }

  private lazy val recordPatternFields: P[Field[Variable]] =
    recordPatternElem ~ "," ~ recordPatternFields ^^ {
      case (l,e)~_~es => ListMap(l -> e) ++ es
    } |
    recordPatternElem ^^ {
      case (l, e) => ListMap(l -> e)
    }

  private lazy val recordPatternElem: P[(Label, Variable)] =
    ident ~ "=" ~ ident ^^ {
      case l~_~e => (l, e)
    }

  private lazy val typ: P[Type] =
    tyFunp

  private lazy val tyFunp: P[Type] =
    tyPairp ~ "->" ~ tyFunp ^^ {
      case t1~_~t2 => TyFun(t1, t2)
    } | tyPairp

  private lazy val tyPairp: P[Type] =
    simpleType ~ "*" ~ tyPairp ^^ {
      case t1~_~t2 => TyPair(t1,t2)
    } | simpleType

  private lazy val tyBag: P[Type] =
    "{|" ~> typ <~ "|}" ^^ (t => TyBag(t))

  private lazy val tyRecordLit: P[Type] =
    "<" ~> tyRecordFields <~ ">" ^^ (tys => TyRecord(tys)) |
    "<" ~ ">" ^^ {
      case _~_ => TyRecord(ListMap())
    }

  private lazy val tyVariantLit: P[Type] =
    "[" ~> tyRecordFields <~ "]" ^^ (tys => TyVariant(tys)) |
    "[" ~ "]" ^^ {
      case _~_ => TyVariant(ListMap())
    }

  private lazy val tyRecordFields: P[Field[Type]] =
    tyRecordElem ~ "," ~ tyRecordFields ^^ {
      case (l,e)~_~es => ListMap(l -> e) ++ es
    } |
    tyRecordElem ^^ {
      case (l, e) => ListMap(l -> e)
    }

  private lazy val tyRecordElem: P[(Label, Type)] =
    ident ~ ":" ~ typ ^^ {
      case l~_~e => (l, e)
    }

  private lazy val simpleType: P[Type] = tyRecordLit
  | tyVariantLit
  | tyBag
  | primitiveType

  private lazy val primitiveType: P[Type] =
    "unit" ^^^ TyUnit | "bool" ^^^ TyBool | "int" ^^^ TyInt | "string" ^^^ TyString |  "("~>typ<~")"

  private lazy val operations: P[Expr] =
    application |
    annotation |
    projection |
    ("fst" ~ "(") ~> expression <~ ")" ^^ (x => First(x)) |
    ("snd" ~ "(") ~> expression <~ ")" ^^ (x => Second(x)) |
    ("length" ~ "(") ~> expression <~ ")" ^^ (x => Length(x)) |
    ("concat"  ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
      case e1~e2 => Concat(e1,e2)
    } |
    ("index" ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
      case e1~e2 => Index(e1,e2)
    }

  private lazy val arith: P[Expr] =
    comp

  private lazy val prod: P[Expr] =
    prod ~ "*" ~ fact ^^ {
      case e1~_~e2 => Times(e1,e2)
    } | fact

  private lazy val summation: P[Expr] =
    summation ~ "+" ~ prod ^^ {
      case e1~_~e2 => Plus(e1,e2)
    } | summation ~ "-" ~ prod ^^ {
      case e1~_~e2 => Minus(e1,e2)
    } | prod

  private lazy val comp: P[Expr] =
    simpleExpr ~ "==" ~ summation ^^ {
      case e1~_~e2 => Eq(e1,e2)
    } | 
    simpleExpr ~ "<" ~ summation ^^ {
      case e1~_~e2 => Less(e1,e2)
    } | 
    summation

  private lazy val application: P[Expr] =
    fact ~ fact ^^ {
      case e1~e2 => Apply(e1,e2)
    }


  private lazy val annotation: P[Expr] =
    fact ~ (":" ~> typ) ^^ {
      case e1~e2 => Anno(e1,e2)
    }

  private lazy val projection: P[Expr] =
    fact ~ "." ~ ident ^^ {
      case e~_~l => Proj(e, l)
    }


  private lazy val simplerExpr: P[Expr] = lambda |
  rec |
  letExpr |
  letFun |
  letRec |
  letPair |
  letRecord |
  caseVariant |
  ifExpr |
  arith |
  fact

  private lazy val simpleExpr: P[Expr] = simplerExpr

  private lazy val pairLit: P[Expr] =
    "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case t1~_~t2 => Pair(t1,t2)
    }

  private lazy val bagLit: P[Expr] =
    "{|" ~> bagFields <~ "|}" ^^ (e => Bag(e)) |
    bagComprehension

  private lazy val bagFields: P[List[Expr]] =
    expression ~ "," ~ bagFields ^^ {
      case e~_~es => e::es
      // NOTE: We directly use syntactic equivalence here for
      // simplicity. Technically we should consider the equivalence
      // relation of rows.
    } |
    expression ^^ (e => List(e))

  private lazy val bagComprehension: P[Expr] =
    ("{|" ~> expression <~ "|") ~ compclslist <~ "|}" ^^ {
      case e~es => Comprehension(e, es)
    }

  private lazy val compclslist: P[List[Expr]] =
    compcls ~ "," ~ compclslist ^^ {
      case e~_~es => e :: es
    } |
    compcls ^^ (e => List(e))

  private lazy val compcls: P[Expr] =
    (ident <~ "<-") ~ expression ^^ {
      case x~e => Bind(x, e)
    } |
    ("let" ~> ident <~ "=") ~ expression ^^ {
      case x~e => CLet(x, e)
    } |
    expression ^^ (e => Guard(e))

  private lazy val recordLit: P[Expr] =
    "<" ~> recordFields <~ ">" ^^ (es => Record(es)) |
    "<" ~ ">" ^^ {
      case _~_ => Record(ListMap())
    }

  private lazy val recordFields: P[Field[Expr]] =
    recordElem ~ "," ~ recordFields ^^ {
      case (l,e)~_~es => ListMap(l -> e) ++ es
    } |
    recordElem ^^ {
      case (l, e) => ListMap(l -> e)
    }

  private lazy val recordElem: P[(Label, Expr)] =
    ident ~ "=" ~ expression ^^ {
      case l~_~e => (l, e)
    }

  private lazy val variantLit: P[Expr] =
    "select" ~> ident ~ fact ^^ {
      case l~e => Variant(l, e)
    }

  lazy val flatMap: P[Expr] =
    "flatMap" ~ "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case e1~_~e2 => FlatMap(e1, e2)
    }

  private lazy val when: P[Expr] =
    "when" ~ "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case e1~_~e2 => When(e1, e2)
    }

  lazy val sum: P[Expr] =
    "sum" ~ "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case e1~_~e2 => Sum(e1, e2)
    }

  lazy val diff: P[Expr] =
    "diff" ~ "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case e1~_~e2 => Diff(e1, e2)
    }

  lazy val count: P[Expr] =
    "count" ~ "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case e1~_~e2 => Count(e1, e2)
    }

  private lazy val fact: P[Expr] = operations |
    recordLit |
    variantLit |
    bagLit |
    pairLit |
    flatMap |
    count |
    when |
    sum |
    diff |
    (ident ^^ {x => Var(x)}) |
    (numericLit ^^ {x => Num(x.toInt) }) |
    (stringLit ^^ {s => Str(s)}) |
    ("true" ^^^ Bool(true)) |
    ("false" ^^^ Bool(false)) |
    ("()" ^^^ Unit) |
    "("~>expression<~")"

}