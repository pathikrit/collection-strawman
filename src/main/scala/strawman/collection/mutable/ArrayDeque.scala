package strawman
package collection.mutable

import scala._
import scala.collection.{GenSeq, generic, mutable}
import scala.reflect.ClassTag
import scala.Predef.{assert, require, genericWrapArray}

import java.lang.Math
import java.util.NoSuchElementException

/** An implementation of a double-ended queue that internally uses a resizable circular buffer
  *  Append, prepend, removeFirst, removeLast and random-access (indexed-lookup and indexed-replacement)
  *  take amortized constant time. In general, removals and insertions at i-th index are O(min(i, n-i))
  *  and thus insertions and removals from end/beginning are fast.
  *
  *  @author  Pathikrit Bhowmick
  *  @version 2.13
  *  @since   2.13
  *
  *  @tparam A  the type of this ArrayDeque's elements.
  *
  *  @define Coll `mutable.ArrayDeque`
  *  @define coll array deque
  *  @define thatinfo the class of the returned collection. In the standard library configuration,
  *    `That` is always `ArrayDeque[B]` because an implicit of type `CanBuildFrom[ArrayDeque, B, ArrayDeque[B]]`
  *    is defined in object `ArrayDeque`.
  *  @define bfinfo an implicit value of class `CanBuildFrom` which determines the
  *    result class `That` from the current representation type `Repr`
  *    and the new element type `B`. This is usually the `canBuildFrom` value
  *    defined in object `ArrayDeque`.
  *  @define orderDependent
  *  @define orderDependentFold
  *  @define mayNotTerminateInf
  *  @define willNotTerminateInf
  */
@SerialVersionUID(1L)
class ArrayDeque[A] private[ArrayDeque](
    private[ArrayDeque] var array: Array[AnyRef],
    private[ArrayDeque] var start: Int,
    private[ArrayDeque] var end: Int
) extends mutable.AbstractBuffer[A]
    with mutable.Buffer[A]
    with generic.GenericTraversableTemplate[A, ArrayDeque]
    with mutable.BufferLike[A, ArrayDeque[A]]
    with mutable.IndexedSeq[A]
    with mutable.IndexedSeqOptimized[A, ArrayDeque[A]]
    with mutable.Builder[A, ArrayDeque[A]]
    with Serializable {

  reset(array, start, end)

  private[this] def reset(array: Array[AnyRef], start: Int, end: Int) = {
    assert((array.length & (array.length - 1)) == 0, s"Array.length must be power of 2")
    assert(array.isDefinedAt(start) && array.isDefinedAt(end))
    this.array = array
    this.start = start
    this.end = end
  }

  def this(initialSize: Int = ArrayDeque.DefaultInitialSize) = this(ArrayDeque.alloc(initialSize), 0, 0)

  override def apply(idx: Int) = {
    ArrayDeque.checkIndex(idx, this)
    _get(idx)
  }

  override def update(idx: Int, elem: A) = {
    ArrayDeque.checkIndex(idx, this)
    _set(idx, elem)
  }

  override def +=(elem: A) = {
    sizeHint(size)
    appendAssumingCapacity(elem)
  }

  override def +=:(elem: A) = {
    sizeHint(size)
    prependAssumingCapacity(elem)
  }

  @inline private[ArrayDeque] def appendAssumingCapacity(elem: A): this.type = {
    array(end) = elem.asInstanceOf[AnyRef]
    end = end_-(-1)
    this
  }

  @inline private[ArrayDeque] def prependAssumingCapacity(elem: A): this.type = {
    start = start_+(-1)
    array(start) = elem.asInstanceOf[AnyRef]
    this
  }

  override def ++=:(elems: TraversableOnce[A]) = {
    if (elems.nonEmpty) {
      ArrayDeque.knownSize(elems) match {
        // Size is too expensive to compute - we need to make one more pass to make it an IndexedSeq and retry
        case srcLength if srcLength < 0 =>
          elems.toIndexedSeq ++=: this

        // We know we need to resize in the end, might as well resize and memcopy upfront
        case srcLength if isExpansionNeeded(srcLength + this.length) =>
          val finalLength = srcLength + this.length
          val array2 = ArrayDeque.alloc(finalLength)
          elems.copyToArray(array2.asInstanceOf[Array[A]])
          copySliceToArray(srcStart = 0, dest = array2, destStart = srcLength, maxItems = size)
          reset(array = array2, start = 0, end = finalLength)

        // We know resizing is not necessary so just fill up from (start - srcLength) to (start - 1) and move back start
        case srcLength =>
          elems.toIterator.zipWithIndex foreach {
            case (elem, i) => _set(i - srcLength, elem)
          }
          start = start_+(-srcLength)
      }
    }
    this
  }

  override def insertAll(idx: Int, elems: scala.collection.Traversable[A]): Unit = {
    ArrayDeque.checkIndex(idx, this)
    if (elems.nonEmpty) {
      ArrayDeque.knownSize(elems) match {
        case srcLength if srcLength >= 0 =>
          val finalLength = srcLength + this.length
          // Either we resize right away or move prefix left or suffix right
          if (isExpansionNeeded(finalLength)) {
            val array2 = ArrayDeque.alloc(finalLength)
            copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
            elems.copyToArray(array2.asInstanceOf[Array[A]], idx)
            copySliceToArray(srcStart = idx, dest = array2, destStart = idx + srcLength, maxItems = size)
            reset(array = array2, start = 0, end = finalLength)
          } else if (2*idx >= length) { // Cheaper to shift the suffix right
            val suffix = drop(idx)
            end = start_+(idx)
            elems.foreach(appendAssumingCapacity)
            suffix.foreach(appendAssumingCapacity)
          } else {  // Cheaper to shift prefix left
            val prefix = take(idx)
            start = start_+(idx)
            prefix ++=: elems ++=: this
          }
        case _ => //Expensive to compute size, retry using IndexedSeq
          insertAll(idx, elems.toIndexedSeq)
      }
    }
  }

  override def remove(idx: Int, count: Int) = {
    require(count >= 0, s"removing negative number of elements: $count")
    if (count > 0) {
      ArrayDeque.checkIndex(idx, this)
      val removals = Math.min(size - idx, count)
      // If we are removing more than half the elements, its cheaper to start over
      // Else, choose the shorter: either move the prefix (0 until (idx + removals) right OR the suffix (idx to size) left
      if (2*removals >= size) {
        val array2 = ArrayDeque.alloc(size - removals)
        copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
        copySliceToArray(srcStart = idx + removals - 1, dest = array2, destStart = idx, maxItems = size)
        reset(array = array2, start = 0, end = size - removals)
      } else if (size - idx <= idx + removals) {
        var i = idx
        while(i + removals < size) {
          _set(i, _get(i + removals))
          setNull(i + removals)
          i += 1
        }
        nullify(from = i)
        end = end_-(removals)
      } else {
        var i = idx + removals - 1
        while(i - removals >= 0) {
          _set(i, _get(i - removals))
          setNull(i - removals)
          i -= 1
        }
        nullify(until = i + 1)
        start = start_+(removals)
      }
    }
  }

  override def remove(idx: Int) = {
    val elem = this(idx)
    remove(idx, 1)
    elem
  }

  /**
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @return
    */
  def removeFirst(resizeInternalRepr: Boolean = false): Option[A] =
    if (isEmpty) None else Some(unsafeRemoveFirst(resizeInternalRepr))

  /**
    * Unsafely remove the first element (throws exception when empty)
    * See also removeFirst()
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @throws NoSuchElementException when empty
    * @return
    */
  def unsafeRemoveFirst(resizeInternalRepr: Boolean = false): A = {
    if (isEmpty) throw new NoSuchElementException(s"empty collection")
    val elem = array(start)
    array(start) = null
    start = start_+(1)
    if (resizeInternalRepr) resize(size)
    elem.asInstanceOf[A]
  }

  /**
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @return
    */
  def removeLast(resizeInternalRepr: Boolean = false): Option[A] =
    if (isEmpty) None else Some(unsafeRemoveLast(resizeInternalRepr))

  /**
    * Unsafely remove the last element (throws exception when empty)
    * See also removelast()
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @throws NoSuchElementException when empty
    * @return
    */
  def unsafeRemoveLast(resizeInternalRepr: Boolean = false): A = {
    if (isEmpty) throw new NoSuchElementException(s"empty collection")
    end = end_-(1)
    val elem = array(end)
    array(end) = null
    if (resizeInternalRepr) resize(size)
    elem.asInstanceOf[A]
  }

  /**
    * Remove all elements from this collection and return the elements while emptying this data structure
    * @return
    */
  def removeAll(): scala.collection.Seq[A] = {
    val elems = toSeq
    clear()
    elems
  }

  /**
    * Returns and removes all elements from the left of this queue which satisfy the given predicate
    *
    *  @param f   the predicate used for choosing elements
    *  @return
    */
  def removeHeadWhile(f: A => Boolean): scala.collection.Seq[A] = {
    val elems = Seq.newBuilder[A]
    while(headOption.exists(f)) {
      elems += unsafeRemoveFirst()
    }
    elems.result()
  }

  /**
    * Returns and removes all elements from the right of this queue which satisfy the given predicate
    *
    *  @param f   the predicate used for choosing elements
    *  @return
    */
  def removeLastWhile(f: A => Boolean): scala.collection.Seq[A] = {
    val elems = Seq.newBuilder[A]
    while(lastOption.exists(f)) {
      elems += unsafeRemoveLast()
    }
    elems.result()
  }

  /**
    * Returns the top (front) element of this queue (without removing it) and returns it (None if empty)
    *
    * @return
    */
  def peek: Option[A] =
    headOption

  override def reverse = foldLeft(new ArrayDeque[A](initialSize = size))(_.prependAssumingCapacity(_))

  override def sizeHint(hint: Int) = if (isExpansionNeeded(hint)) resize(hint + 1)

  override def length = end_-(start)

  override def isEmpty = start == end

  override def nonEmpty = start != end

  override def clone() = new ArrayDeque(array.clone(), start = start, end = end)

  /**
    * Note: This does not actually resize the internal representation.
    * See clearAndShrink if you want to also resize internally
    */
  override def clear() = {
    nullify()
    start = 0
    end = 0
  }

  /**
    * clears this buffer and shrinks to @param size
    *
    * @param size
    * @return
    */
  def clearAndShrink(size: Int = ArrayDeque.DefaultInitialSize): this.type = {
    require(size >= 0, s"Non-negative size required")
    reset(array = ArrayDeque.alloc(size), start = 0, end = 0)
    this
  }

  override def slice(from: Int, until: Int) = {
    val left = if (from <= 0) 0 else if (from >= size) size else from
    val right = if (until <= 0) 0 else if (until >= size) size else until
    val len = right - left
    if (len <= 0) {
      ArrayDeque.empty[A]
    } else if (len >= size) {
      clone()
    } else {
      val array2 = copySliceToArray(srcStart = left, dest = ArrayDeque.alloc(len), destStart = 0, maxItems = len)
      new ArrayDeque(array2, 0, len)
    }
  }

  override def sliding(window: Int, step: Int) = {
    require(window > 0 && step > 0, s"window=$window and step=$step, but both must be positive")
    val lag = if (window > step) window - step else 0
    Iterator.range(start = 0, end = length - lag, step = step).map(i => slice(i, i + window))
  }

  override def grouped(n: Int) = sliding(n, n)

  override def copyToArray[B >: A](dest: Array[B], destStart: Int, len: Int) =
    copySliceToArray(srcStart = 0, dest = dest, destStart = destStart, maxItems = len)

  override def companion = ArrayDeque

  override def result() = this

  override def stringPrefix = "ArrayDeque"

  override def toArray[B >: A: ClassTag] =
    copySliceToArray(srcStart = 0, dest = new Array[B](size), destStart = 0, maxItems = size)

  /**
    * This is a more general version of copyToArray - this also accepts a srcStart unlike copyToArray
    * This copies maxItems elements from this collections srcStart to dest's destStart
    * If we reach the end of either collections before we could copy maxItems, we simply stop copying
    *
    * @param dest
    * @param srcStart
    * @param destStart
    * @param maxItems
    */
  def copySliceToArray(srcStart: Int, dest: Array[_], destStart: Int, maxItems: Int): dest.type = {
    ArrayDeque.checkIndex(srcStart, this)
    ArrayDeque.checkIndex(destStart, dest)
    val toCopy = Math.min(maxItems, Math.min(size - srcStart, dest.length - destStart))
    if (toCopy > 0) {
      val startIdx = start_+(srcStart)
      val block1 = Math.min(toCopy, array.length - startIdx)
      Array.copy(src = array, srcPos = startIdx, dest = dest, destPos = destStart, length = block1)
      if (block1 < toCopy) {
        Array.copy(src = array, srcPos = 0, dest = dest, destPos = block1, length = toCopy - block1)
      }
    }
    dest
  }

  /**
    * Trims the capacity of this ArrayDeque's instance to be the current size
    */
  def trimToSize(): Unit = resize(size - 1)

  /**
    * Add idx to start modulo mask
    */
  @inline private[this] def start_+(idx: Int) = (start + idx) & (array.length - 1)

  /**
    * Subtract idx from end modulo mask
    */
  @inline private[this] def end_-(idx: Int) = (end - idx) & (array.length - 1)

  @inline private[this] def _get(idx: Int): A = array(start_+(idx)).asInstanceOf[A]

  @inline private[this] def _set(idx: Int, elem: A) = array(start_+(idx)) = elem.asInstanceOf[AnyRef]

  @inline private[this] def setNull(idx: Int) = _set(idx, null.asInstanceOf[A])

  @inline private[this] def isExpansionNeeded(len: Int) = len >= (array.length - 1)

  private[this] def nullify(from: Int = 0, until: Int = size) = {
    // Optimized version of `from.until(until).foreach(setNull)`
    var i = from
    while(i < until) {
      setNull(i)
      i += 1
    }
  }

  private[this] def resize(len: Int) = {
    if (ArrayDeque.nextPowerOfTwo(len) != array.length) {
      val array2 = copySliceToArray(srcStart = 0, dest = ArrayDeque.alloc(len), destStart = 0, maxItems = size)
      reset(array = array2, start = 0, end = size)
    }
  }
}

object ArrayDeque extends generic.SeqFactory[ArrayDeque] {
  implicit def canBuildFrom[A]: generic.CanBuildFrom[Coll, A, ArrayDeque[A]] =
    ReusableCBF.asInstanceOf[GenericCanBuildFrom[A]]

  override def newBuilder[A]: mutable.Builder[A, ArrayDeque[A]] = new ArrayDeque[A]()

  final val DefaultInitialSize = 8

  private[ArrayDeque] def knownSize[A](coll: TraversableOnce[A]) = {
    //TODO: Remove this temporary util when we switch to strawman .sizeHintIfCheap is now .knownSize
    if (coll.isInstanceOf[List[_]] || coll.isInstanceOf[Stream[_]] || coll.isInstanceOf[Iterator[_]] || !coll.isTraversableAgain) -1 else coll.size
  }

  /**
    * Allocates an array whose size is next power of 2 > $len
    * Largest possible len is 1<<30 - 1
    *
    * @param len
    * @return
    */
  private[ArrayDeque] def alloc(len: Int) = {
    val size = nextPowerOfTwo(len)
    require(size >= 0, s"ArrayDeque too big - cannot allocate ArrayDeque of length $len")
    new Array[AnyRef](size)
  }

  private[ArrayDeque] def nextPowerOfTwo(i: Int): Int =
    ((1 << 31) >>> java.lang.Integer.numberOfLeadingZeros(i)) << 1

  @inline private[ArrayDeque] def checkIndex(idx: Int, seq: GenSeq[_]) =
    if (!seq.isDefinedAt(idx)) throw new IndexOutOfBoundsException(idx.toString)
}
