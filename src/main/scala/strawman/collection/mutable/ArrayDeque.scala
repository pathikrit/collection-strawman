package scala             //TODO: Change this to strawman --> we just need sizeHintIfCheap from scala but in strawman it is called knownSize
package collection.mutable

import scala.collection.{GenSeq, generic, mutable}
import scala.reflect.ClassTag

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

  private[this] var mask = 0   // modulus using bitmask since array.length is always power of 2
  resetInternal(array, start, end)

  private[this] def resetInternal(array: Array[AnyRef], start: Int, end: Int) = {
    this.array = array
    this.mask = array.length - 1
    assert((array.length & mask) == 0, s"Array.length must be power of 2")
    assert(0 <= start && start <= mask && 0 <= end && end <= mask)
    this.start = start
    this.end = end
  }

  def this(initialSize: Int = ArrayDeque.DefaultInitialSize) = this(ArrayDeque.alloc(initialSize), 0, 0)

  override def apply(idx: Int) = {
    ArrayDeque.checkIndex(idx, this)
    getInternal(idx).asInstanceOf[A]
  }

  override def update(idx: Int, elem: A) = {
    ArrayDeque.checkIndex(idx, this)
    setInternal(idx, elem.asInstanceOf[AnyRef])
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
    // Note this is faster than super.++=: because this does not need to convert TraversableOnce to a Traversable
    if (elems.nonEmpty) {
      elems.sizeHintIfCheap match {
        case srcLength if srcLength >= 0 && 2*(srcLength + this.length) >= mask =>
          val finalLength = srcLength + this.length
          val array2 = ArrayDeque.alloc(finalLength)
          elems.copyToArray(array2.asInstanceOf[Array[A]])
          copySliceToArray(srcStart = 0, dest = array2, destStart = srcLength, maxItems = size)
          resetInternal(array = array2, start = 0, end = finalLength)
        case _ =>
          val copy = clone()
          end = start
          this ++= elems ++= copy
      }
    }
    this
  }

  override def insertAll(idx: Int, elems: scala.collection.Traversable[A]): Unit = {
    ArrayDeque.checkIndex(idx, this)
    if (elems.nonEmpty) {
      elems.sizeHintIfCheap match {
        case srcLength if srcLength >= 0 =>
          val finalLength = srcLength + this.length
          // Either we resize right away or move prefix right or suffix left
          if (2*finalLength >= mask) {
            val array2 = ArrayDeque.alloc(finalLength)
            copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
            elems.copyToArray(array2.asInstanceOf[Array[A]], idx)
            copySliceToArray(srcStart = idx, dest = array2, destStart = idx + srcLength, maxItems = size)
            resetInternal(array = array2, start = 0, end = finalLength)
          } else {
            val suffix = drop(idx)
            end = start_+(idx)
            elems.foreach(appendAssumingCapacity)
            suffix.foreach(appendAssumingCapacity)
          }
        case _ => //expensive to compute size
          val suffix = drop(idx)
          end = start_+(idx)
          this ++= elems ++= suffix
      }
    }
  }

  override def remove(idx: Int, count: Int): Unit = {
    if (count < 0) throw new IllegalArgumentException(s"removing negative number of elements: $count")
    ArrayDeque.checkIndex(idx, this)
    if (count == 0) return
    val removals = (size - idx) min count
    // If we are removing more than half the elements, its cheaper to start over
    // Else, choose the shorter: either move the prefix (0 until (idx + removals) right OR the suffix (idx to size) left
    if (2*removals >= size) {
      val array2 = ArrayDeque.alloc(size - removals)
      copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
      copySliceToArray(srcStart = idx + removals - 1, dest = array2, destStart = idx, maxItems = size)
      resetInternal(array = array2, start = 0, end = size - removals)
    } else if (size - idx <= idx + removals) {
      var i = idx
      while(i + removals < size) {
        setInternal(i, getInternal(i + removals))
        setInternal(i + removals, null)
        i += 1
      }
      nullify(from = i)
      end = end_-(removals)
    } else {
      var i = idx + removals - 1
      while(i - removals >= 0) {
        setInternal(i, getInternal(i - removals))
        setInternal(i - removals, null)
        i -= 1
      }
      nullify(until = i + 1)
      start = start_+(removals)
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
  def removeFirst(resizeInternalRepr: Boolean = false): Option[A] = {
    if (isEmpty) {
      None
    } else {
      val elem = array(start)
      array(start) = null
      start = start_+(1)
      if (resizeInternalRepr && 2*size < mask) resize(size)
      Some(elem.asInstanceOf[A])
    }
  }

  /**
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @return
    */
  def removeLast(resizeInternalRepr: Boolean = false): Option[A] = {
    if (isEmpty) {
      None
    } else {
      end = end_-(1)
      val elem = array(end)
      array(end) = null
      if (resizeInternalRepr && 2*size < mask) resize(size)
      Some(elem.asInstanceOf[A])
    }
  }

  override def reverse = foldLeft(new ArrayDeque[A](initialSize = size))(_.prependAssumingCapacity(_))

  override def sizeHint(hint: Int) = if (hint >= mask) resize(hint + 1)

  override def length = end_-(start)

  override def isEmpty = start == end

  override def nonEmpty = start != end

  override def clone() = {
    // TODO Scala's array.clone should call java.util.Arrays.copyOf(array, array.length)
    new ArrayDeque(java.util.Arrays.copyOf(array, array.length), start, end)
  }
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
    resetInternal(array = ArrayDeque.alloc(size), start = 0, end = 0)
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
    val lag = (window - step) max 0
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
    val toCopy = maxItems min (size - srcStart) min (dest.length - destStart)
    if (toCopy > 0) {
      val startIdx = start_+(srcStart)
      val block1 = toCopy min (array.length - startIdx)
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
  @inline private[this] def start_+(idx: Int) = (start + idx) & mask

  /**
    * Subtract idx from end modulo mask
    */
  @inline private[this] def end_-(idx: Int) = (end - idx) & mask

  @inline private[this] def getInternal(idx: Int) = array(start_+(idx))

  @inline private[this] def setInternal(idx: Int, elem: AnyRef) = array(start_+(idx)) = elem

  private[this] def nullify(from: Int = 0, until: Int = size) = {
    var i = from
    while(i < until) {
      setInternal(i, null)
      i += 1
    }
  }

  private[this] def resize(len: Int) = {
    val array2 = copySliceToArray(srcStart = 0, dest = ArrayDeque.alloc(len), destStart = 0, maxItems = size)
    resetInternal(array = array2, start = 0, end = size)
  }
}

object ArrayDeque extends generic.SeqFactory[ArrayDeque] {
  implicit def canBuildFrom[A]: generic.CanBuildFrom[Coll, A, ArrayDeque[A]] =
    ReusableCBF.asInstanceOf[GenericCanBuildFrom[A]]

  override def newBuilder[A]: mutable.Builder[A, ArrayDeque[A]] = new ArrayDeque[A]()

  final val DefaultInitialSize = 8

  /**
    * Allocates an array whose size is next power of 2 > $len
    * Largest possible len is 1<<30 - 1
    *
    * @param len
    * @return
    */
  private[ArrayDeque] def alloc(len: Int) = {
    val size = ((1 << 31) >>> Integer.numberOfLeadingZeros(len max DefaultInitialSize)) << 1
    new Array[AnyRef](size.ensuring(_ >= 0, s"ArrayDeque too big - cannot allocate ArrayDeque of length $len"))
  }

  @inline private[ArrayDeque] def checkIndex(idx: Int, seq: GenSeq[_]) =
    if (!seq.isDefinedAt(idx)) throw new IndexOutOfBoundsException(idx.toString)
}
