package strawman
package collection.mutable

import scala._
import scala.collection.{generic, mutable}
import scala.reflect.ClassTag
import scala.Predef.{assert, require}

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
    requireBounds(idx = start, until = array.length)
    requireBounds(idx = end, until = array.length)
    this.array = array
    this.start = start
    this.end = end
  }

  def this(initialSize: Int = ArrayDeque.DefaultInitialSize) = this(ArrayDeque.alloc(initialSize), start = 0, end = 0)

  override def apply(idx: Int) = {
    requireBounds(idx)
    _get(idx)
  }

  override def update(idx: Int, elem: A) = {
    requireBounds(idx)
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
    end = end_+(1)
    this
  }

  @inline private[ArrayDeque] def prependAssumingCapacity(elem: A): this.type = {
    start = start_-(1)
    array(start) = elem.asInstanceOf[AnyRef]
    this
  }

  override def ++=:(elems: scala.collection.TraversableOnce[A]) = {
    if (elems.nonEmpty) {
      // The following code resizes the current collection atmost once and traverses elems atmost twice
      ArrayDeque.knownSize(elems) match {
        // Size is too expensive to compute AND we can traverse it only once - can't do much but retry with an IndexedSeq
        case srcLength if srcLength < 0 && !elems.isTraversableAgain => elems.toIndexedSeq ++=: this

        // We know for sure we need to resize to hold everything, might as well resize and memcopy upfront
        case srcLength if srcLength > 0 && isExpansionNeeded(srcLength + this.length) =>
          val finalLength = srcLength + this.length
          val array2 = ArrayDeque.alloc(finalLength)
          elems.copyToArray(array2.asInstanceOf[Array[A]])
          copySliceToArray(srcStart = 0, dest = array2, destStart = srcLength, maxItems = size)
          reset(array = array2, start = 0, end = finalLength)

        // Just fill up from (start - srcLength) to (start - 1) and move back start
        case _srcLength =>
          val srcLength = if (_srcLength < 0) elems.size else _srcLength
          sizeHint(srcLength + this.length)
          // Optimized version of `elems.zipWithIndex.foreach((elem, i) => _set(i - srcLength, elem))`
          var i = 0
          val it = elems.toIterator
          while(it.hasNext) {
            _set(i - srcLength, it.next())
            i += 1
          }
          start = start_-(srcLength)
      }
    }
    this
  }

  override def ++=(elems: scala.collection.TraversableOnce[A]) = {
    if (elems.nonEmpty) {
      ArrayDeque.knownSize(elems) match {
        case srcLength if srcLength >= 0 =>
          sizeHint(srcLength + this.length)
          elems.foreach(appendAssumingCapacity)
        case _ => elems.foreach(+=)
      }
    }
    this
  }

  override def insertAll(idx: Int, elems: scala.collection.Traversable[A]) = {
    requireBounds(idx)
    if (idx == 0) {
      elems ++=: this
    } else if (idx == length - 1) {
      this ++= elems
    } else if (elems.nonEmpty) {
      val srcLength = elems.size
      val finalLength = srcLength + this.length
      // Either we resize right away or move prefix left or suffix right
      if (isExpansionNeeded(finalLength)) {
        val array2 = ArrayDeque.alloc(finalLength)
        copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
        elems.copyToArray(array2.asInstanceOf[Array[A]], idx)
        copySliceToArray(srcStart = idx, dest = array2, destStart = idx + srcLength, maxItems = size)
        reset(array = array2, start = 0, end = finalLength)
      } else if (2*idx >= length) { // Cheaper to shift the suffix right
        var i = length - 1
        while(i >= idx) {
          _set(i + srcLength, _get(i))
          i -= 1
        }
        end = end_+(srcLength)
        val it = elems.toIterator
        while(it.hasNext) {
          i += 1
          _set(i, it.next())
        }
      } else {  // Cheaper to shift prefix left
        var i = 0
        while(i < idx) {
          _set(i - srcLength, _get(i))
          i += 1
        }
        start = start_-(srcLength)
        val it = elems.toIterator
        while(it.hasNext) {
          _set(i, it.next())
          i += 1
        }
      }
    }
  }

  override def remove(idx: Int, count: Int) = {
    require(count >= 0, s"removing negative number of elements: $count")
    if (count > 0) {
      requireBounds(idx)
      val n = size
      val removals = Math.min(n - idx, count)
      val finalLength = n - removals
      val suffixStart = idx + removals
      // If we know we can resize after removing, do it right away using arrayCopy
      // Else, choose the shorter: either move the prefix (0 until idx) right OR the suffix (idx+removals until n) left
      if (isResizeNecessary(finalLength)) {
        val array2 = ArrayDeque.alloc(finalLength)
        copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
        if (suffixStart < n) copySliceToArray(srcStart = suffixStart, dest = array2, destStart = idx, maxItems = n)
        reset(array = array2, start = 0, end = finalLength)
      } else if (2*idx <= finalLength) { // Cheaper to move the prefix right
        var i = suffixStart
        while(i >= 0) {
          i -= 1
          _set(i, if (i >= removals) _get(i - removals) else null.asInstanceOf[A])
        }
        start = start_+(removals)
      } else {  // Cheaper to move the suffix left
        var i = idx
        while(i < n) {
          _set(i, if (i < finalLength) _get(i + removals) else null.asInstanceOf[A])
          i += 1
        }
        end = end_-(removals)
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
  def removeHeadOption(resizeInternalRepr: Boolean = false): Option[A] =
    if (isEmpty) None else Some(removeHeadAssumingNonEmpty(resizeInternalRepr))

  /**
    * Unsafely remove the first element (throws exception when empty)
    * See also removeHeadOption()
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @throws NoSuchElementException when empty
    * @return
    */
  def removeHead(resizeInternalRepr: Boolean = false): A =
    if (isEmpty) throw new NoSuchElementException(s"empty collection") else removeHeadAssumingNonEmpty(resizeInternalRepr)

  private[this] def removeHeadAssumingNonEmpty(resizeInternalRepr: Boolean = false): A = {
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
  def removeLastOption(resizeInternalRepr: Boolean = false): Option[A] =
    if (isEmpty) None else Some(removeLastAssumingNonEmpty(resizeInternalRepr))

  /**
    * Unsafely remove the last element (throws exception when empty)
    * See also removeLastOption()
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @throws NoSuchElementException when empty
    * @return
    */
  def removeLast(resizeInternalRepr: Boolean = false): A =
    if (isEmpty) throw new NoSuchElementException(s"empty collection") else removeLastAssumingNonEmpty(resizeInternalRepr)

  private[this] def removeLastAssumingNonEmpty(resizeInternalRepr: Boolean = false): A = {
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
    val elems = scala.collection.Seq.newBuilder[A]
    elems.sizeHint(size)
    while(nonEmpty) {
      elems += removeHeadAssumingNonEmpty()
    }
    elems.result()
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
      elems += removeHeadAssumingNonEmpty()
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
      elems += removeLastAssumingNonEmpty()
    }
    elems.result()
  }

  /**
    * Returns the top (front) element of this queue (without removing it) and returns it (None if empty)
    *
    * @return
    */
  def peek: Option[A] = headOption

  override def reverseIterator = Iterator.tabulate(size)(i => this(size - i - 1))

  override def reverseMap[B, That](f: (A) => B)(implicit bf: generic.CanBuildFrom[ArrayDeque[A], B, That]) = reverse.map(f)

  override def reverse = {
    val n = size
    val arr = ArrayDeque.alloc(n)
    var i = 0
    while(i < n) {
      arr(i) = this(n - i - 1).asInstanceOf[AnyRef]
      i += 1
    }
    new ArrayDeque(arr, start = 0, end = n)
  }

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
    while(nonEmpty) {
      removeHeadAssumingNonEmpty()
    }
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
      new ArrayDeque(array2, start = 0, end = len)
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
    requireBounds(srcStart)
    requireBounds(destStart, 0, dest.length)
    val toCopy = Math.min(maxItems, Math.min(size - srcStart, dest.length - destStart))
    if (toCopy > 0) {
      val startIdx = start_+(srcStart)
      val block1 = Math.min(toCopy, array.length - startIdx)
      Array.copy(src = array, srcPos = startIdx, dest = dest, destPos = destStart, length = block1)
      if (block1 < toCopy) {
        Array.copy(src = array, srcPos = 0, dest = dest, destPos = destStart + block1, length = toCopy - block1)
      }
    }
    dest
  }

  /**
    * Trims the capacity of this ArrayDeque's instance to be the current size
    */
  def trimToSize(): Unit = resize(size - 1)

  // Utils for common modular arithmetic:
  @inline private[this] def start_+(idx: Int) = (start + idx) & (array.length - 1)
  @inline private[this] def start_-(idx: Int) = (start - idx) & (array.length - 1)
  @inline private[this] def end_+(idx: Int) = (end + idx) & (array.length - 1)
  @inline private[this] def end_-(idx: Int) = (end - idx) & (array.length - 1)

  @inline private[this] def isResizeNecessary(len: Int) = ArrayDeque.requiredArrayLength(len) != array.length

  @inline private[this] def _get(idx: Int): A = array(start_+(idx)).asInstanceOf[A]

  @inline private[this] def _set(idx: Int, elem: A) = array(start_+(idx)) = elem.asInstanceOf[AnyRef]

  @inline private[this] def isExpansionNeeded(len: Int) = len >= (array.length - 1)

  private[this] def resize(len: Int) = if (isResizeNecessary(len)) {
    val array2 = copySliceToArray(srcStart = 0, dest = ArrayDeque.alloc(len), destStart = 0, maxItems = size)
    reset(array = array2, start = 0, end = size)
  }

  @inline private[this] def requireBounds(idx: Int, from: Int = 0, until: Int = size) =
    if (idx < 0 || until <= idx) throw new IndexOutOfBoundsException(idx.toString)
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
    val size = requiredArrayLength(len)
    require(size >= 0, s"ArrayDeque too big - cannot allocate ArrayDeque of length $len")
    new Array[AnyRef](Math.max(size, DefaultInitialSize))
  }

  /**
    * @param i
    * @return next power of 2 strictly greater than i
    */
  private[ArrayDeque] def requiredArrayLength(i: Int): Int =
    ((1 << 31) >>> java.lang.Integer.numberOfLeadingZeros(i)) << 1
}
