package strawman.collection

import java.util.concurrent.atomic.{AtomicInteger, AtomicReference}

import scala.{Any, Array, Boolean, IllegalArgumentException, Int, NoSuchElementException, None, Nothing, Option, Some, StringContext, Unit, `inline`, math, throws}
import scala.Predef.{intWrapper, require}
import strawman.collection.mutable.ArrayBuffer

import scala.annotation.tailrec
import scala.annotation.unchecked.uncheckedVariance

/** A core Iterator class
  *
  * @define consumesIterator
  * After calling this method, one should discard the iterator it was called
  * on. Using it is undefined and subject to change.
  */
trait Iterator[+A] extends IterableOnce[A] { self =>
  def hasNext: Boolean
  @throws[NoSuchElementException]
  def next(): A
  def iterator() = this

  /** Tests whether this iterator is empty.
    *
    *  @return   `true` if hasNext is false, `false` otherwise.
    *  @note     Reuse: $preservesIterator
    */
  def isEmpty: Boolean = !hasNext

  /** Tests whether a predicate holds for all values produced by this iterator.
    *  $mayNotTerminateInf
    *
    *  @param   p     the predicate used to test elements.
    *  @return        `true` if the given predicate `p` holds for all values
    *                 produced by this iterator, otherwise `false`.
    *  @note          Reuse: $consumesIterator
    */
  def forall(p: A => Boolean): Boolean = {
    var res = true
    while (res && hasNext) res = p(next())
    res
  }

  /** Tests whether a predicate holds for some of the values produced by this iterator.
    *  $mayNotTerminateInf
    *
    *  @param   p     the predicate used to test elements.
    *  @return        `true` if the given predicate `p` holds for some of the values
    *                 produced by this iterator, otherwise `false`.
    *  @note          Reuse: $consumesIterator
    */
  def exists(p: A => Boolean): Boolean = {
    var res = false
    while (!res && hasNext) res = p(next())
    res
  }

  /** Tests whether this iterator contains a given value as an element.
    *  $mayNotTerminateInf
    *
    *  @param elem  the element to test.
    *  @return     `true` if this iterator produces some value that is
    *               is equal (as determined by `==`) to `elem`, `false` otherwise.
    *  @note        Reuse: $consumesIterator
    */
  def contains(elem: Any): Boolean = exists(_ == elem)    // Note--this seems faster than manual inlining!

  /** Counts the number of elements in the $coll which satisfy a predicate.
    *
    *  @param p     the predicate  used to test elements.
    *  @return      the number of elements satisfying the predicate `p`.
    */
  def count(p: A => Boolean): Int = {
    var res = 0
    while (hasNext) if (p(next())) res += 1
    res
  }

  /** Finds the first value produced by the iterator satisfying a
    *  predicate, if any.
    *  $mayNotTerminateInf
    *
    *  @param p the predicate used to test values.
    *  @return  an option value containing the first value produced by the iterator that satisfies
    *           predicate `p`, or `None` if none exists.
    *  @note    Reuse: $consumesIterator
    */
  def find(p: A => Boolean): Option[A] = {
    while (hasNext) {
      val a = next()
      if (p(a)) return Some(a)
    }
    None
  }

  /** A flexible iterator for transforming an `Iterator[A]` into an
   *  Iterator[Seq[A]], with configurable sequence size, step, and
   *  strategy for dealing with elements which don't fit evenly.
   *
   *  Typical uses can be achieved via methods `grouped` and `sliding`.
   */
  class GroupedIterator[B >: A](self: Iterator[B], size: Int, step: Int) extends Iterator[Seq[B]] {

    require(size >= 1 && step >= 1, f"size=$size%d and step=$step%d, but both must be positive")

    private[this] var buffer: ArrayBuffer[B] = ArrayBuffer()  // the buffer
    private[this] var filled = false                          // whether the buffer is "hot"
    private[this] var _partial = true                         // whether we deliver short sequences
    private[this] var pad: Option[() => B] = None             // what to pad short sequences with

    /** Public functions which can be used to configure the iterator before use.
     *
     *  Pads the last segment if necessary so that all segments will
     *  have the same size.
     *
     *  @param x The element that will be appended to the last segment, if necessary.
     *  @return  The same iterator, and ''not'' a new iterator.
     *  @note    This method mutates the iterator it is called on, which can be safely used afterwards.
     *  @note    This method is mutually exclusive with `withPartial(true)`.
     */
    def withPadding(x: => B): this.type = {
      pad = Some(() => x)
      this
    }
    /** Public functions which can be used to configure the iterator before use.
     *
     *  Select whether the last segment may be returned with less than `size`
     *  elements. If not, some elements of the original iterator may not be
     *  returned at all.
     *
     *  @param x `true` if partial segments may be returned, `false` otherwise.
     *  @return  The same iterator, and ''not'' a new iterator.
     *  @note    This method mutates the iterator it is called on, which can be safely used afterwards.
     *  @note    This method is mutually exclusive with `withPadding`.
     */
    def withPartial(x: Boolean): this.type = {
      _partial = x
      if (_partial == true) // reset pad since otherwise it will take precedence
        pad = None

      this
    }

    /** For reasons which remain to be determined, calling
     *  self.take(n).toSeq cause an infinite loop, so we have
     *  a slight variation on take for local usage.
     *  NB: self.take.toSeq is slice.toStream, lazily built on self,
     *  so a subsequent self.hasNext would not test self after the
     *  group was consumed.
     */
    private def takeDestructively(size: Int): Seq[B] = {
      val buf = new ArrayBuffer[B]
      var i = 0
      // The order of terms in the following condition is important
      // here as self.hasNext could be blocking
      while (i < size && self.hasNext) {
        buf += self.next()
        i += 1
      }
      buf
    }

    private def padding(x: Int) = immutable.ImmutableArray.fill(x)(pad.get())
    private def gap = (step - size) max 0

    private def go(count: Int) = {
      val prevSize = buffer.size
      def isFirst = prevSize == 0
      // If there is padding defined we insert it immediately
      // so the rest of the code can be oblivious
      val xs: Seq[B] = {
        val res = takeDestructively(count)
        // was: extra checks so we don't calculate length unless there's reason
        // but since we took the group eagerly, just use the fast length
        val shortBy = count - res.length
        if (shortBy > 0 && pad.isDefined) res ++ padding(shortBy) else res
      }
      lazy val len = xs.length
      lazy val incomplete = len < count

      // if 0 elements are requested, or if the number of newly obtained
      // elements is less than the gap between sequences, we are done.
      def deliver(howMany: Int) = {
        (howMany > 0 && (isFirst || len > gap)) && {
          if (!isFirst)
            buffer dropInPlace (step min prevSize)

          val available =
            if (isFirst) len
            else howMany min (len - gap)

          buffer ++= (xs takeRight available)
          filled = true
          true
        }
      }

      if (xs.isEmpty) false                         // self ran out of elements
      else if (_partial) deliver(len min size)      // if _partial is true, we deliver regardless
      else if (incomplete) false                    // !_partial && incomplete means no more seqs
      else if (isFirst) deliver(len)                // first element
      else deliver(step min size)                   // the typical case
    }

    // fill() returns false if no more sequences can be produced
    private def fill(): Boolean = {
      if (!self.hasNext) false
      // the first time we grab size, but after that we grab step
      else if (buffer.isEmpty) go(size)
      else go(step)
    }

    def hasNext = filled || fill()
    @throws[NoSuchElementException]
    def next() = {
      if (!filled)
        fill()

      if (!filled)
        throw new NoSuchElementException("next on empty iterator")
      filled = false
      immutable.ImmutableArray.fromArrayBuffer(buffer)
    }
  }

  /** Returns an iterator which groups this iterator into fixed size
   *  blocks.  Example usages:
   *  {{{
   *    // Returns List(List(1, 2, 3), List(4, 5, 6), List(7)))
   *    (1 to 7).iterator grouped 3 toList
   *    // Returns List(List(1, 2, 3), List(4, 5, 6))
   *    (1 to 7).iterator grouped 3 withPartial false toList
   *    // Returns List(List(1, 2, 3), List(4, 5, 6), List(7, 20, 25)
   *    // Illustrating that withPadding's argument is by-name.
   *    val it2 = Iterator.iterate(20)(_ + 5)
   *    (1 to 7).iterator grouped 3 withPadding it2.next toList
   *  }}}
   *
   *  @note Reuse: $consumesAndProducesIterator
   */
  def grouped[B >: A](size: Int): GroupedIterator[B] =
    new GroupedIterator[B](self, size, size)

  /** Returns an iterator which presents a "sliding window" view of
   *  this iterator.  The first argument is the window size, and
   *  the second argument `step` is how far to advance the window
   *  on each iteration. The `step` defaults to `1`.
   *
   *  The default `GroupedIterator` can be configured to either
   *  pad a partial result to size `size` or suppress the partial
   *  result entirely.
   *
   *  Example usages:
   *  {{{
   *    // Returns List(List(1, 2, 3), List(2, 3, 4), List(3, 4, 5))
   *    (1 to 5).iterator.sliding(3).toList
   *    // Returns List(List(1, 2, 3, 4), List(4, 5))
   *    (1 to 5).iterator.sliding(4, 3).toList
   *    // Returns List(List(1, 2, 3, 4))
   *    (1 to 5).iterator.sliding(4, 3).withPartial(false).toList
   *    // Returns List(List(1, 2, 3, 4), List(4, 5, 20, 25))
   *    // Illustrating that withPadding's argument is by-name.
   *    val it2 = Iterator.iterate(20)(_ + 5)
   *    (1 to 5).iterator.sliding(4, 3).withPadding(it2.next).toList
   *  }}}
   *
   *  @return An iterator producing `Seq[B]`s of size `size`, except the
   *          last element (which may be the only element) will be truncated
   *          if there are fewer than `size` elements remaining to be grouped.
   *          This behavior can be configured.
   *
   *  @note Reuse: $consumesAndProducesIterator
   */
  def sliding[B >: A](size: Int, step: Int = 1): GroupedIterator[B] =
    new GroupedIterator[B](self, size, step)

  def foldLeft[B](z: B)(op: (B, A) => B): B = {
    var result = z
    while (hasNext) {
      result = op(result, next())
    }
    result
  }

  def foldRight[B](z: B)(op: (A, B) => B): B =
    if (hasNext) op(next(), foldRight(z)(op)) else z

/** Produces a collection containing cumulative results of applying the
   *  operator going left to right.
   *
   *  $willNotTerminateInf
   *  $orderDependent
   *
   *  @tparam B      the type of the elements in the resulting collection
   *  @param z       the initial value
   *  @param op      the binary operator applied to the intermediate result and the element
   *  @return        iterator with intermediate results
   *  @note          Reuse: $consumesAndProducesIterator
   */
  def scanLeft[B](z: B)(op: (B, A) => B): Iterator[B] = new Iterator[B] {
    // We use an intermediate iterator that iterates through the first element `z`
    // and then that will be modified to iterate through the collection
    private var current: Iterator[B] =
      new Iterator[B] {
        def hasNext: Boolean = true
        def next(): B = {
          // Here we change our self-reference to a new iterator that iterates through `self`
          current = new Iterator[B] {
            private var acc = z
            def next(): B = {
              acc = op(acc, self.next())
              acc
            }
            def hasNext: Boolean = self.hasNext
          }
          z
        }
      }
    def next(): B = current.next()
    def hasNext: Boolean = current.hasNext
  }

  def foreach[U](f: A => U): Unit =
    while (hasNext) f(next())

  def indexWhere(p: A => Boolean, from: Int = 0): Int = {
    var i = math.max(from, 0)
    drop(from)
    while (hasNext) {
      if (p(next())) return i
      i += 1
    }
    -1
  }

  /** Returns the index of the first occurrence of the specified
    *  object in this iterable object.
    *  $mayNotTerminateInf
    *
    *  @param  elem  element to search for.
    *  @return the index of the first occurrence of `elem` in the values produced by this iterator,
    *          or -1 if such an element does not exist until the end of the iterator is reached.
    *  @note   Reuse: $consumesIterator
    */
  def indexOf[B >: A](elem: B): Int = indexOf(elem, 0)

  /** Returns the index of the first occurrence of the specified object in this iterable object
    *  after or at some start index.
    *  $mayNotTerminateInf
    *
    *  @param elem element to search for.
    *  @param from the start index
    *  @return the index `>= from` of the first occurrence of `elem` in the values produced by this
    *          iterator, or -1 if such an element does not exist until the end of the iterator is
    *          reached.
    *  @note   Reuse: $consumesIterator
    */
  def indexOf[B >: A](elem: B, from: Int): Int = {
    var i = 0
    while (i < from && hasNext) {
      next()
      i += 1
    }

    while (hasNext) {
      if (next() == elem) return i
      i += 1
    }
    -1
  }

  def length: Int = {
    var len = 0
    while (hasNext) { len += 1; next() }
    len
  }

  final def size: Int = length

  def filter(p: A => Boolean): Iterator[A] = new Iterator[A] {
    private var hd: A = _
    private var hdDefined: Boolean = false

    def hasNext: Boolean = hdDefined || {
      do {
        if (!self.hasNext) return false
        hd = self.next()
      } while (!p(hd))
      hdDefined = true
      true
    }

    def next() =
      if (hasNext) {
        hdDefined = false
        hd
      }
      else Iterator.empty.next()
  }

  def map[B](f: A => B): Iterator[B] = new Iterator[B] {
    def hasNext = self.hasNext
    def next() = f(self.next())
  }

  def flatMap[B](f: A => IterableOnce[B]): Iterator[B] = new Iterator[B] {
    private var myCurrent: Iterator[B] = Iterator.empty
    private def current = {
      while (!myCurrent.hasNext && self.hasNext)
        myCurrent = f(self.next()).iterator()
      myCurrent
    }
    def hasNext = current.hasNext
    def next() = current.next()
  }

  def concat[B >: A](xs: => IterableOnce[B]): Iterator[B] = new Iterator.ConcatIterator[B](self).concat(xs)

  @`inline` def ++ [B >: A](xs: => IterableOnce[B]): Iterator[B] = concat(xs)

  def take(n: Int): Iterator[A] = new Iterator[A] {
    private var i = 0
    def hasNext = self.hasNext && i < n
    def next() =
      if (hasNext) {
        i += 1
        self.next()
      }
      else Iterator.empty.next()
  }

  /** Takes longest prefix of values produced by this iterator that satisfy a predicate.
    *
    *  @param   p  The predicate used to test elements.
    *  @return  An iterator returning the values produced by this iterator, until
    *           this iterator produces a value that does not satisfy
    *           the predicate `p`.
    *  @note    Reuse: $consumesAndProducesIterator
    */
  def takeWhile(p: A => Boolean): Iterator[A] = new Iterator[A] {
    private var hd: A = _
    private var hdDefined: Boolean = false
    private var tail: Iterator[A] = self

    def hasNext = hdDefined || tail.hasNext && {
      hd = tail.next()
      if (p(hd)) hdDefined = true
      else tail = Iterator.empty
      hdDefined
    }
    def next() = if (hasNext) { hdDefined = false; hd } else Iterator.empty.next()
  }

  def drop(n: Int): Iterator[A] = {
    var i = 0
    while (i < n && hasNext) {
      next()
      i += 1
    }
    this
  }

  /** Skips longest sequence of elements of this iterator which satisfy given
    *  predicate `p`, and returns an iterator of the remaining elements.
    *
    *  @param p the predicate used to skip elements.
    *  @return  an iterator consisting of the remaining elements
    *  @note    Reuse: $consumesAndProducesIterator
    */
  def dropWhile(p: A => Boolean): Iterator[A] = new Iterator[A] {
    // Magic value: -1 = hasn't dropped, 0 = found first, 1 = defer to parent iterator
    private[this] var status = -1
    // Local buffering to avoid double-wrap with .buffered
    private[this] var fst: A = _
    def hasNext: Boolean =
      if (status == 1) self.hasNext
      else if (status == 0) true
      else {
        while (self.hasNext) {
          val a = self.next()
          if (!p(a)) {
            fst = a
            status = 0
            return true
          }
        }
        status = 1
        false
      }
    def next() =
      if (hasNext) {
        if (status == 1) self.next()
        else {
          status = 1
          fst
        }
      }
      else Iterator.empty.next()
  }

  def zip[B](that: IterableOnce[B]): Iterator[(A, B)] = new Iterator[(A, B)] {
    val thatIterator = that.iterator()
    def hasNext = self.hasNext && thatIterator.hasNext
    def next() = (self.next(), thatIterator.next())
  }

  /** Creates an iterator that pairs each element produced by this iterator
    *  with its index, counting from 0.
    *
    *  @return        a new iterator containing pairs consisting of
    *                 corresponding elements of this iterator and their indices.
    *  @note          Reuse: $consumesAndProducesIterator
    */
  def zipWithIndex: Iterator[(A, Int)] = new Iterator[(A, Int)] {
    var idx = 0
    def hasNext = self.hasNext
    def next() = {
      val ret = (self.next(), idx)
      idx += 1
      ret
    }
  }

  def sameElements[B >: A](that: IterableOnce[B]): Boolean = {
    val those = that.iterator()
    while (hasNext && those.hasNext)
      if (next() != those.next())
        return false
    // At that point we know that *at least one* iterator has no next element
    // If *both* of them have no elements then the collections are the same
    hasNext == those.hasNext
  }
}

object Iterator {

  val empty: Iterator[Nothing] = new Iterator[Nothing] {
    def hasNext = false
    def next() = throw new NoSuchElementException("next on empty iterator")
  }

  def single[A](a: A): Iterator[A] = new Iterator[A] {
    private var consumed: Boolean = false
    def hasNext = !consumed
    def next() = if (consumed) empty.next() else { consumed = true; a }
  }

  def apply[A](xs: A*): Iterator[A] = new IndexedView[A] {
    val length = xs.length
    def apply(n: Int) = xs(n)
  }.iterator()

  /** Creates an infinite-length iterator which returns successive values from some start value.

    *  @param start the start value of the iterator
    *  @return      the iterator producing the infinite sequence of values `start, start + 1, start + 2, ...`
    */
  def from(start: Int): Iterator[Int] = from(start, 1)

  /** Creates an infinite-length iterator returning values equally spaced apart.
    *
    *  @param start the start value of the iterator
    *  @param step  the increment between successive values
    *  @return      the iterator producing the infinite sequence of values `start, start + 1 * step, start + 2 * step, ...`
    */
  def from(start: Int, step: Int): Iterator[Int] = new Iterator[Int] {
    private var i = start
    def hasNext: Boolean = true
    def next(): Int = { val result = i; i += step; result }
  }

  /** Creates nn iterator returning successive values in some integer interval.
    *
    *  @param start the start value of the iterator
    *  @param end   the end value of the iterator (the first value NOT returned)
    *  @return      the iterator producing values `start, start + 1, ..., end - 1`
    */
  def range(start: Int, end: Int): Iterator[Int] = range(start, end, 1)

  /** An iterator producing equally spaced values in some integer interval.
    *
    *  @param start the start value of the iterator
    *  @param end   the end value of the iterator (the first value NOT returned)
    *  @param step  the increment value of the iterator (must be positive or negative)
    *  @return      the iterator producing values `start, start + step, ...` up to, but excluding `end`
    */
  def range(start: Int, end: Int, step: Int): Iterator[Int] = new Iterator[Int] {
    if (step == 0) throw new IllegalArgumentException("zero step")
    private var i = start
    def hasNext: Boolean = (step <= 0 || i < end) && (step >= 0 || i > end)
    def next(): Int =
      if (hasNext) { val result = i; i += step; result }
      else empty.next()
  }

  /** Creates an infinite iterator that repeatedly applies a given function to the previous result.
    *
    *  @param start the start value of the iterator
    *  @param f     the function that's repeatedly applied
    *  @return      the iterator producing the infinite sequence of values `start, f(start), f(f(start)), ...`
    */
  def iterate[T](start: T)(f: T => T): Iterator[T] = new Iterator[T] {
    private[this] var first = true
    private[this] var acc = start
    def hasNext: Boolean = true
    def next(): T = {
      if (first) first = false
      else acc = f(acc)

      acc
    }
  }

  /** Creates an infinite-length iterator returning the results of evaluating an expression.
    *  The expression is recomputed for every element.
    *
    *  @param elem the element computation.
    *  @return the iterator containing an infinite number of results of evaluating `elem`.
    */
  def continually[A](elem: => A): Iterator[A] = new Iterator[A] {
    def hasNext = true
    def next() = elem
  }

  /** Creates an iterator to which other iterators can be appended efficiently.
    *  Nested ConcatIterators are merged to avoid blowing the stack.
    */
  private final class ConcatIterator[+A](private var current: Iterator[A @uncheckedVariance]) extends Iterator[A] {
    private var tail: ConcatIteratorCell[A @uncheckedVariance] = null
    private var last: ConcatIteratorCell[A @uncheckedVariance] = null
    private var currentHasNextChecked = false

    // Advance current to the next non-empty iterator
    // current is set to null when all iterators are exhausted
    @tailrec
    private[this] def advance(): Boolean = {
      if (tail eq null) {
        current = null
        last = null
        false
      }
      else {
        current = tail.headIterator
        tail = tail.tail
        merge()
        if (currentHasNextChecked) true
        else if (current.hasNext) {
          currentHasNextChecked = true
          true
        } else advance()
      }
    }

    // If the current iterator is a ConcatIterator, merge it into this one
    @tailrec
    private[this] def merge(): Unit =
    if (current.isInstanceOf[ConcatIterator[_]]) {
      val c = current.asInstanceOf[ConcatIterator[A]]
      current = c.current
      currentHasNextChecked = c.currentHasNextChecked
      if (c.tail ne null) {
        c.last.tail = tail
        tail = c.tail
      }
      merge()
    }

    def hasNext =
      if (currentHasNextChecked) true
      else if (current eq null) false
      else if (current.hasNext) {
        currentHasNextChecked = true
        true
      } else advance()

    def next()  =
      if (hasNext) {
        currentHasNextChecked = false
        current.next()
      } else Iterator.empty.next()

    override def concat[B >: A](that: => IterableOnce[B]): Iterator[B] = {
      val c = new ConcatIteratorCell[B](that, null).asInstanceOf[ConcatIteratorCell[A]]
      if(tail eq null) {
        tail = c
        last = c
      } else {
        last.tail = c
        last = c
      }
      if(current eq null) current = Iterator.empty
      this
    }
  }

  private[this] final class ConcatIteratorCell[A](head: => IterableOnce[A], var tail: ConcatIteratorCell[A]) {
    def headIterator: Iterator[A] = head.iterator()
  }
}
