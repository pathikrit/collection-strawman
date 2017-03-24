package strawman
package collection.test

import strawman.collection.mutable.ArrayDeque

import org.scalatest._

import scala.collection.mutable

class ArrayDequeSpec extends FlatSpec {
  "circular-buffer" should "match the library" in {
    val buffer = ArrayDeque.empty[Int]
    val buffer2 = mutable.ArrayBuffer.empty[Int]

    def apply[U](f: mutable.Buffer[Int] => U) = {
      //println(s"Before: [buffer1=${buffer}; buffer2=${buffer2}]")
      assert(f(buffer) === f(buffer2))
      assert(buffer === buffer2)
    }

    apply(_.append(1, 2, 3, 4, 5))
    apply(_.prepend(6, 7, 8))
    apply(_.trimStart(2))
    apply(_.trimEnd(3))
    apply(_.insertAll(0, Seq(9, 10, 11)))
    apply(_.insertAll(1, Seq(12, 13)))
    apply(_.remove(2))
    apply(_.prependAll(Seq(14, 15, 16, 17)))
    apply(_.remove(1, 5))
    apply(_.prependAll(Seq.tabulate(100)(identity)))
    buffer.trimToSize()
    apply(_.appendAll(Seq.tabulate(100)(identity)))

    (-100 to 100) foreach {i =>
      assert(buffer.splitAt(i) === buffer2.splitAt(i))
    }

    for {
      i <- -100 to 100
      j <- -100 to 100
    } {
      assert(buffer.slice(i, j) === buffer2.slice(i, j))
      if (i >= 1 && j >= 1 && j >= i) assert(buffer.sliding(i, j).toList === buffer2.sliding(i, j).toList)
    }
  }
}