package Assign3.Bags

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
    type T[A] = List[A]

    def toList[A](bag: T[A]): List[A] = bag

    def fromList[A](l: List[A]): T[A] = l

    def add[A](bag: T[A], x: A): T[A] = bag :+ x

    def sum[A](bag: T[A], other: T[A]): T[A] = bag ++ other

    def diff[A](bag: T[A], other: T[A]): T[A] = bag.filterNot(other.contains)

    def flatMap[A,B](bag: T[A],f: A => T[B]): T[B] = bag.flatMap(f)
    
    def count[A](bag: T[A],x: A): Int = bag.count(_ == x)

  }
}