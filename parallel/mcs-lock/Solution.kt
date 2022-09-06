import java.lang.IllegalStateException
import java.util.concurrent.atomic.*

class Solution(val env: Environment) : Lock<Solution.Node> {
    // just why is it atomic
    private val NO_LOCK = AtomicReference(Node(null))

    private val tail = AtomicReference(Node(NO_LOCK.value))

    override fun lock() : Node {
        val my = Node()
        while (true) {
            val t = tail.value
            if (t.next.compareAndSet(null, my)) {
                tail.compareAndSet(t, my)
                do {
                    env.park()
                } while (!my.canRun.value)
                return my
            }
            val nxt = t.next.value
            if (nxt != NO_LOCK.value) {
                tail.compareAndSet(t, nxt)
            } else if (t.next.compareAndSet(NO_LOCK.value, my)) {
                tail.compareAndSet(t, my)
                my.canRun.value = true
                return my
            }
        }
    }

    override fun unlock(node : Node) {
        while (true) {
            if (node.next.compareAndSet(null, NO_LOCK.value)) {
                return
            }
            val nxt = node.next.value
            if (nxt === NO_LOCK.value) {
                return
            }
            if (nxt == null) {
                throw IllegalStateException()
            }
            nxt.canRun.value = true
            env.unpark(nxt.thread)
            return
        }
    }

    class Node(nxtInit : Node? = null, canRun : Boolean = false) {
        val thread = Thread.currentThread()!!
        val canRun = AtomicReference(canRun)
        val next = AtomicReference<Node?>(nxtInit)
    }
}