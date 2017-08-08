package strawman.collection.mutable

import scala._

/** `Queue` objects implement data structures that allow to
  *  insert and retrieve elements in a first-in-first-out (FIFO) manner.
  *
  *  @author  Pathikrit Bhowmick
  *
  *  @version 2.13
  *  @since   2.13
  */
class Queue[A] extends ArrayDeque[A] {

  /**
    * Add elements to the end of this queue
    *
    * @param elem
    * @return this
    */
  def enqueue(elem: A): this.type =
    this += elem

  /** Enqueue two or more elements at the end of the queue. The last element
    *  of the sequence will be on end of the queue.
    *
    *  @param   elems      the element sequence.
    *  @return this
    */
  def enqueue(elem1: A, elem2: A, elems: A*): this.type =
    enqueue(elem1).enqueue(elem2).enqueueAll(elems)

  /** Enqueues all elements in the given traversable object into the queue. The
    *  last element in the traversable object will be on front of the new queue.
    *
    *  @param elems the traversable object.
    *  @return this
    */
  def enqueueAll(elems: TraversableOnce[A]): this.type =
    this ++= elems

  /**
    * Removes the from element from this queue and return it
    *
    * @return
    * @throws java.util.NoSuchElementException when queue is empty
    */
  def dequeue(): A =
    removeFirst().getOrElse(throw new java.util.NoSuchElementException("empty queue"))

  /**
    * Dequeues all elements from this stack and return it
    *
    * @return
    */
  def dequeueAll(): scala.collection.Seq[A] =
    removeAll()

  /**
    * Returns and removes all elements from the end of this queue which satisfy the given predicate
    *
    *  @param f   the predicate used for choosing elements
    *  @return
    */
  def dequeueWhile(f: A => Boolean): scala.collection.Seq[A] = {
    val elems = Seq.newBuilder[A]
    while(peek.exists(f)) {
      elems += dequeue()
    }
    elems.result()
  }

  /**
    * Returns the next element of this queue (without removing it) and returns it (None if empty)
    *
    * @return
    */
  def peek: Option[A] =
    headOption
}
