import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.atomicArrayOfNulls
import java.lang.IllegalStateException

private class Moving (val who : Any, val where : Core)
private class LookAt (val where : Core)

private class Core(
    capacity: Int,
    size0: Int,
) {
    /*
     * <E>
     * null=unassigned
     *   may be only righter than <E>
     * Moving
     * LookAt
     *   compressed path, little [memory] overhead,
     *   created 1 per level
     */
    val array = atomicArrayOfNulls<Any>(capacity)
    val size = atomic(size0)
    val next : AtomicRef<Core?> = atomic(null)
    // memory optimization
    val looker = LookAt(this)
}

// decremented to ~~~slow down~~ harden tests
private const val INITIAL_CAPACITY = 0 // DO NOT CHANGE ME

class DynamicArrayImpl<E> : DynamicArray<E> {
    private val head : AtomicRef<Core>
    private val desired : AtomicRef<Core>

    private fun moveForward(index : Int, mov : Moving, from : Core) : LookAt {
        val nxt = mov.where
        assert(index < from.array.size)
        assert(from.array.size < nxt.array.size)
        nxt.array[index].compareAndSet(null, mov.who)
        from.array[index].compareAndSet(mov, nxt.looker)
        /*
        val hm = from.array[index].value
        if (!(hm is LookAt)) {
            throw IllegalStateException("BAD $hm")
        }
         */
        return nxt.looker
    }

    private inline fun <R> go(index : Int, h0 : Core = head.value, block : (E, Core) -> R) : R {
        var h = h0
        while (index >= h.array.size) {
            h = h.next.value ?: throw IllegalArgumentException("OOB $index")
        }
        assert(index < h.size.value)

        var pathCompression : Pair<LookAt, Core>? = null

        val compress = { cur : LookAt ->
            if (pathCompression !== null) {
                val pc = pathCompression!!
                pc.second.array[index].compareAndSet(pc.first, cur.where)
            }
            pathCompression = Pair(cur, h)
            cur.where
        }

        while (true) {
            val cell = h.array[index]
            h = when (val cValue = cell.value) {
                null -> throw IllegalStateException("wrong state [$index] is null")
                is LookAt -> compress(cValue)
                is Moving -> compress(moveForward(index, cValue, h))
                else -> {
                    val mov = Moving(cValue, h.next.value ?: return block(cValue as E, h))
                    if (!cell.compareAndSet(cValue, mov)) {
                        continue
                    }
                    compress(moveForward(index, mov, h))
                }
            }
        }
    }

    private fun checkSize(index : Int) : Int {
        if (index >= size) {
            throw IllegalArgumentException("OOB $index")
        }
        return index
    }

    override fun get(index: Int) : E = go(checkSize(index)) { e, _ -> e }

    override fun put(index: Int, element: E) {
        checkSize(index)
        var h0 = head.value
        while (true) {
            go(index, h0) { prev, nextCore ->
                h0 = nextCore
                if (nextCore.array[index].compareAndSet(prev, element)) {
                    return
                }
            }
        }
    }

    private fun getDesired() : Core {
        while (true) {
            val des = desired.value
            val nxt = des.next.value ?: return des
            desired.compareAndSet(des, nxt)
        }
    }

    override fun pushBack(element: E) {
        while (true) {
            val des = getDesired()
            val size = des.size.value
            val capa = des.array.size
            if (size < capa) {
                if (des.array[size].compareAndSet(null, element)) {
                    des.size.compareAndSet(size, size + 1)
                    return
                }
                // someone set this element, if he __parked__ right
                // after we will lock
                des.size.compareAndSet(size, size + 1)
                continue
            }
            assert(size == capa)
            // val newCore = Core(capa * 2, capa)
            val newCore = Core(capa + 1, capa) // for debug and test purposes only
            if (!des.next.compareAndSet(null, newCore)) {
                continue
            }
            // forward everyone at least to newCore
            for (i in 0 until capa) {
                go(i) { _, _ -> }
            }
            // now we know for sure that newCore contains all [needed] elements
            while (true) {
                val h = head.value
                //  already further                    || updated
                if (h.array.size >= newCore.array.size || head.compareAndSet(h, newCore)) {
                    break
                }
            }
            // tail recursion
            continue
        }
    }

    override val size: Int get() = getDesired().size.value

    init {
        val atom = Core(INITIAL_CAPACITY, 0)
        head = atomic(atom)
        desired = atomic(atom)
    }
}