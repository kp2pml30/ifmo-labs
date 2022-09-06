import kotlinx.atomicfu.*
import java.util.*

class FAAQueue<T> {
    private val head: AtomicRef<Segment> // Head pointer, similarly to the Michael-Scott queue (but the first node is _not_ sentinel)
    private val tail: AtomicRef<Segment> // Tail pointer, similarly to the Michael-Scott queue

    init {
        val firstNode = Segment()
        head = atomic(firstNode)
        tail = atomic(firstNode)
    }

    /**
     * Adds the specified element [x] to the queue.
     */
    fun enqueue(x: T) {
        while (true) {
            val t = tail.value
            val e = t.enqIdx.incrementAndGet()
            if (e < SEGMENT_SIZE) {
                if (t.elements[e].compareAndSet(null, x)) {
                    return
                }
                continue
            }
            // e >= SEGMENT_SIZE
            val tn = t.next.value
            if (tn != null) {
                tail.compareAndSet(t, tn)
                continue
            }
            val tm = Segment(x!!)
            if (t.next.compareAndSet(null, tm)) {
                tail.compareAndSet(t, tm)
                return
            }
        }
    }

    /**
     * Retrieves the first element from the queue
     * and returns it; returns `null` if the queue
     * is empty.
     */
    fun dequeue(): T? {
        while (true) {
            val h = head.value
            val d = h.deqIdx.getAndIncrement()
            if (d >= SEGMENT_SIZE) {
                val hn = h.next.value ?: return null
                head.compareAndSet(h, hn)
                continue
            }
            val cell = h.elements[d]
            while (true) {
                when (val res = cell.value) {
                    null -> {
                        if (cell.compareAndSet(null, DONE)) {
                            break
                        }
                    }
                    DONE -> break
                    else -> {
                        if (cell.compareAndSet(res, DONE)) {
                            return res as T
                        }
                    }
                }
            }
        }
    }

    /**
     * Returns `true` if this queue is empty;
     * `false` otherwise.
     */
    val isEmpty: Boolean get()  {
        while (true) {
            val h = head.value
            val d = h.deqIdx.value
            if (d >= SEGMENT_SIZE) {
                val hn = h.next.value ?: return true
                head.compareAndSet(h, hn)
                continue
            }
            val cell = h.elements[d]
            while (true) {
                when (val res = cell.value) {
                    null -> {
                        if (cell.compareAndSet(null, DONE)) {
                            h.deqIdx.compareAndSet(d, d + 1)
                            break
                        }
                    }
                    DONE -> {
                        h.deqIdx.compareAndSet(d, d + 1)
                        break
                    }
                    else -> return false
                }
            }
        }
    }
}

private class Segment {
    val next = atomic<Segment?>(null)
    val enqIdx = atomic(0) // index for the next enqueue operation
    val deqIdx = atomic(0) // index for the next dequeue operation
    val elements = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)

    constructor() // for the first segment creation

    constructor(x: Any) { // each next new segment should be constructed with an element
        elements[0].value = x
        enqIdx.value = 1
    }
}

private val DONE = Any() // Marker for the "DONE" slot state; to avoid memory leaks
const val SEGMENT_SIZE = 2 // DO NOT CHANGE, IMPORTANT FOR TESTS

