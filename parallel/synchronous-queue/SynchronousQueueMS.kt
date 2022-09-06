import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlin.coroutines.Continuation
import kotlin.coroutines.resume
import kotlin.coroutines.suspendCoroutine

private val HEAD = Any()
private val RETRY = Any()

class SynchronousQueueMS<E : Any> : SynchronousQueue<E> {
    private val head : AtomicRef<Core>
    private val tail : AtomicRef<Core>

    init {
        val h = Core(false, null, HEAD)
        head = atomic(h)
        tail = atomic(h)
    }

    private class Core(val isSend : Boolean, val cor : Continuation<Any>?, val data : Any) {
        val next = atomic<Core?>(null)
    }

    override suspend fun receive() : E = doJob(false, Unit)
    override suspend fun send(element : E) : Unit = doJob(true, element)

    private suspend fun <T, CoT : Any> doJob(isSend : Boolean, toPut : CoT) : T {
        while (true) {
            val t = tail.value
            val tn = t.next.value
            if (tn !== null) {
                tail.compareAndSet(t, tn)
                continue
            }
            val h = head.value
            if (h === t || t.isSend == isSend) {
                val res = suspendCoroutine<Any> sc@{ cont ->
                    val me = Core(isSend, cont, toPut)
                    if (!t.next.compareAndSet(null, me)) {
                        cont.resume(RETRY)
                        return@sc
                    } else {
                        tail.compareAndSet(t, me)
                    }
                }
                if (res === RETRY) {
                    continue
                }
                return res as T
            } else {
                val nxt = h.next.value ?: continue
                if (nxt.isSend == isSend || !head.compareAndSet(h, nxt)) {
                    continue
                }
                (nxt.cor as Continuation<CoT>).resume(toPut)
                return nxt.data as T
            }
        }
    }
}
