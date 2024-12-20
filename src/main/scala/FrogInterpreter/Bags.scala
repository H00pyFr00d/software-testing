package FrogInterpreter

import scala.collection.immutable.ListMap

object Bags {
  trait Bag {
    type T[_]
    def toList[A](b: T[A]): List[A]
    def fromList[A](l: List[A]): T[A]
    def toString[A](b: T[A]) : String = toList(b).mkString("Bag(", ", ", ")")
    def sum[A](b1: T[A], b2: T[A]): T[A]
    def diff[A](b1: T[A], b2: T[A]): T[A]
    def flatMap[A,B](b: T[A], f: A => T[B]): T[B]
    def count[A](b: T[A], x: A): Int
  }

    ////////////////////
    // EXERCISE 1     //
    ////////////////////
  object BagImpl extends Bag {
    // BEGIN ANSWER
    type T[A] = ListMap[A,Int]

    def toList[A](bag: T[A]): List[A] =
      bag.flatMap{ case (k, v) => List.fill(v)(k) }.toList

    def fromList[A](l: List[A]): T[A] = l match {
      case Nil => new ListMap[A,Int]()
      case x::xs => add(fromList(xs),x)
    }
    
    def add[A](bag: T[A], x: A): T[A] =
      bag.updated(x, bag.getOrElse(x, 0) + 1)

    def sum[A](bag: T[A], other: T[A]): T[A] =
      (bag ++ other).map { (k, _) =>
        k -> (bag.getOrElse(k, 0) + other.getOrElse(k, 0))
      }

    def diff[A](bag: T[A], other: T[A]): T[A] = bag.map { case (k, v) =>
          k -> (v - other.getOrElse(k, 0))
        }.filter { case (_, v) => v > 0 }

    def flatMap[A,B](bag: T[A],f: A => T[B]): T[B] =
      bag.foldLeft(new ListMap[B,Int]()) {
        case (acc, (k, v)) => sum(acc, f(k).map((k1, v1) => (k1, v * v1)))
    }

    def count[A](bag: T[A],x: A): Int = bag.getOrElse(x, 0)

    // END ANSWER

  }


}