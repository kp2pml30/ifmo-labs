import kotlin.concurrent.getOrSet

/**
 * @author Prokopenko Kirill
 */
class Solution : AtomicCounter {

    private val root = Node(0)
    private val head = ThreadLocal<Node>()

    override fun getAndAdd(x: Int): Int {
        while (true) {
            val cur = head.getOrSet { root }
            val new = Node(cur.value + x)
            val result = cur.next.decide(new)

            head.set(result)
            if (result == new) {
                return cur.value
            }
        }
    }

    // вам наверняка потребуется дополнительный класс
    private class Node(val value: Int) {
        val next = Consensus<Node>()
    }
}
