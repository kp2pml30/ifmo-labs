package dijkstra

import java.util.*
import java.util.concurrent.Phaser
import java.util.concurrent.locks.ReentrantLock
import java.util.concurrent.PriorityBlockingQueue
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.locks.Lock
import kotlin.Comparator
import kotlin.concurrent.thread
import kotlin.concurrent.withLock

private val NODE_DISTANCE_COMPARATOR = Comparator<Node> { o1, o2 -> Integer.compare(o1!!.distance, o2!!.distance) }

private inline fun Lock.withTryLock(action: () -> Unit) {
    if (!tryLock()) return
    try {
        action()
    } finally {
        unlock()
    }
}

class MultiQueue<T>(val workers: Int, val cmp: Comparator<T>) {
    private class Lockable<Y>(val data: Y) {
        val lock = ReentrantLock()
    }

    private val heaps = Array<Lockable<PriorityQueue<T>>>(workers * 2) { Lockable(PriorityQueue(cmp)) }

    private fun getRnd() = ThreadLocalRandom.current().nextInt(0, heaps.size)

    fun add(o: T): Boolean {
        val q = heaps[getRnd()]
        q.lock.withLock { return q.data.add(o) }
    }

    fun poll(): T? {
        while (true) {
            val r1 = getRnd()
            val r2 = getRnd()
            if (r1 == r2) continue
            val q1 = heaps[minOf(r1, r2)]
            val q2 = heaps[maxOf(r1, r2)]
            q1.lock.withTryLock {
                q2.lock.withTryLock {
                    return when {
                        q1.data.isEmpty() -> q2.data.poll()
                        q2.data.isEmpty() -> q1.data.poll()
                        cmp.compare(q1.data.peek(), q2.data.peek()) <= 0 -> q1.data.poll()
                        else -> q2.data.poll()
                    }
                }
            }
        }
    }
}

// Returns `Integer.MAX_VALUE` if a path has not been found.
fun shortestPathParallel(start: Node) {
    val workers = Runtime.getRuntime().availableProcessors()
    // The distance to the start node is `0`
    start.distance = 0
    // Create a priority (by distance) queue and add the start node into it
    // val q = PriorityBlockingQueue(workers, NODE_DISTANCE_COMPARATOR)
    val q = MultiQueue(workers, NODE_DISTANCE_COMPARATOR)
    q.add(start)
    val tasksLeft = AtomicInteger(1)
    // Run worker threads and wait until the total work is done
    val onFinish = Phaser(workers + 1) // `arrive()` should be invoked at the end by each worker
    repeat(workers) {
        thread {
            while (tasksLeft.get() > 0) {
                val cur: Node = q.poll() ?: continue
                for (e in cur.outgoingEdges) {
                    val new = cur.distance + e.weight
                    while (true) {
                        val old = e.to.distance
                        if (old <= new) break
                        if (e.to.casDistance(old, new)) {
                            if (q.add(e.to)) tasksLeft.incrementAndGet()
                            break
                        }
                    }
                }
                tasksLeft.decrementAndGet()
            }
            onFinish.arrive()
        }
    }
    onFinish.arriveAndAwaitAdvance()
}