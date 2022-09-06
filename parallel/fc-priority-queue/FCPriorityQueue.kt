import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.atomicArrayOfNulls
import kotlinx.atomicfu.locks.ReentrantLock
import kotlinx.atomicfu.locks.withLock
import java.util.*
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.TimeUnit
import java.util.concurrent.locks.Condition
import java.util.concurrent.locks.Lock
import java.util.function.Supplier

val EMPTY = Any()

inline fun <T> Lock.withTryLock(ifLocked: () -> T, orElse : () -> T) : T {
    return if (tryLock()) {
        try {
            ifLocked()
        } finally {
            unlock()
        }
    } else {
        orElse()
    }
}

private class MyLock : Lock {
    val locked = atomic(false)
    override fun lock() {
        while (locked.value || !locked.compareAndSet(false, true)) {
        }
    }

    override fun lockInterruptibly() {
        TODO("Not yet implemented")
    }

    override fun tryLock(): Boolean {
        return locked.compareAndSet(false, true)
    }

    override fun tryLock(time: Long, unit: TimeUnit): Boolean {
        TODO("Not yet implemented")
    }

    override fun unlock() {
        assert(locked.compareAndSet(true, false))
    }

    override fun newCondition(): Condition {
        TODO("Not yet implemented")
    }

}

class FCPriorityQueue<E : Comparable<E>> {
    private val q = PriorityQueue<E>()
    // do not have an array of locks on which we will wait?..
    private val tasks = atomicArrayOfNulls<Any>(Runtime.getRuntime().availableProcessors())
    private val lock = MyLock() // ReentrantLock()
    // why do we need a counter?
    // if we have an algorithm with a lock, then
    // assuming that someone may just park
    // is strange...

    init {
        for (i in 0 until tasks.size) {
            tasks[i].value = EMPTY
        }
    }

    private fun <R> doTask(block : () -> R) : R {
        val castedBlock : Supplier<Any> = Supplier<Any> { block() }
        var selected = -1
        val put = {
            val rnd = ThreadLocalRandom.current()
            var selected : Int
            while (true) {
                selected = rnd.nextInt(tasks.size)
                if (tasks[selected].compareAndSet(EMPTY, castedBlock)) {
                    break
                }
            }
            selected
        }
        while (true) {
            lock.withTryLock({
                /*
                if (selected != -1 && tasks[selected].value === castedBlock) {
                    tasks[selected].value = null
                    selected = -1
                }
                 */
                for (i in 0 until tasks.size) {
                    val cell = tasks[i]
                    val prevN = cell.value
                    if (prevN is Supplier<*>) {
                        cell.value = prevN.get()
                    }
                }
                if (selected == -1) {
                    return block()
                } else {
                    val cell = tasks[selected]
                    val prev = cell.value
                    cell.value = EMPTY
                    return prev as R
                }
            }, {
                if (selected == -1) {
                    selected = put()
                }
            })
            val mbCalc = tasks[selected].value
            if (mbCalc !== castedBlock) {
                tasks[selected].value = EMPTY
                return mbCalc as R
            }
        }
    }

    /**
     * Retrieves the element with the highest priority
     * and returns it as the result of this function;
     * returns `null` if the queue is empty.
     */
    fun poll(): E? = doTask { q.poll() }

    /**
     * Returns the element with the highest priority
     * or `null` if the queue is empty.
     */
    fun peek(): E? = doTask { q.peek() }

    /**
     * Adds the specified element to the queue.
     */
    fun add(element: E) : Unit = doTask { q.add(element) }
}